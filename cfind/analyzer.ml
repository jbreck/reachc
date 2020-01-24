module Log = Srk.Log
include Srk.Log.Make(struct let name = "cfind" end)
open Srk

let cra_refine_flag = ref false
let retry_flag = ref true
let print_summaries_flag = ref false

module CallGraph = Graph.Persistent.Digraph.ConcreteBidirectional(SrkUtil.Int)

module CallSet = BatSet.Make((*IntPair*)SrkUtil.Int)
module VertexSet = SrkUtil.Int.Set


module IntPair = struct
  type t = int * int [@@deriving ord]
  let equal (x,y) (x',y') = (x=x' && y=y')
  let hash = Hashtbl.hash
end
module IntPairMap = BatMap.Make(IntPair)
module IntPairSet = BatSet.Make(IntPair)

module CallGraphSCCs = Graph.Components.Make(CallGraph)

module Sctx = Syntax.MakeSimplifyingContext ()

module Pctx = Syntax.MakeContext ()

let parsingCtx = Pctx.context
let srk = Sctx.context

let name_of_symbol ctx symbol = 
  match Syntax.symbol_name ctx symbol with
  | None -> Syntax.show_symbol ctx symbol
  | Some name -> name

(* Initially based on module Var as defined in   duet/cra.ml  *)
module Var = struct
  let sym_to_var = Hashtbl.create 991
  let var_to_sym = Hashtbl.create 991

  let typ var = `TyInt

  let symbol_of var =
    try Hashtbl.find var_to_sym var
    with Not_found -> failwith "Failed lookup in Var.symbol_of"

  let of_symbol sym =
    if Hashtbl.mem sym_to_var sym then
      Some (Hashtbl.find sym_to_var sym)
    else
      None

  module I = struct
    (*type t = int [@@deriving ord]*)
    type t = Syntax.symbol [@@deriving ord]

    (* Note: hardcoding srk *)
    let pp formatter var =
      let sym = symbol_of var in
      Format.fprintf formatter "%a" (Syntax.pp_symbol srk) sym
    (*let show = SrkUtil.mk_show pp*)
    let show var = 
      let sym = symbol_of var in
      name_of_symbol srk sym

    let equal x y = compare x y = 0
    let hash var = Hashtbl.hash var
  end
  include I

  let register_var sym = 
    begin
      (* sym_to_var and var_to_sym are always identity hash tables
           over the subset of symbol numbers we're currently using *)
      (*let sym = Syntax.mk_symbol srk ~name:(show var) (typ var) in*)
      (*let var = Syntax.int_of_symbol sym in*)
      let var = sym in
      Hashtbl.add var_to_sym var sym;
      Hashtbl.add sym_to_var sym var
    end

  let reset_tables = 
    begin
      Hashtbl.clear var_to_sym;
      Hashtbl.clear sym_to_var
    end
end

module IterDomain = struct
  open Iteration
  open SolvablePolynomial
  module SPOne = SumWedge (SolvablePolynomial) (SolvablePolynomialOne) ()
  module SPPeriodicRational = SumWedge (SPOne) (SolvablePolynomialPeriodicRational) ()
  module SPG = ProductWedge (SPPeriodicRational) (WedgeGuard)
  module SPPRG = Sum (SPG) (PresburgerGuard) ()
  module SPSplit = Sum (SPPRG) (Split(SPPRG)) ()
  module VasSwitch = Sum (Vas)(Vass)()
  module Vas_P = Product(VasSwitch)(Product(WedgeGuard)(LinearRecurrenceInequation))
  module SpPlusSplitVas_P = Sum(SPSplit)(Vas_P)()
  include SpPlusSplitVas_P
end

module MakeTransition (V : Transition.Var) = struct
  include Transition.Make(Sctx)(V)

  module I = Iter(Iteration.MakeDomain(IterDomain))

  let star x = Log.time "cra:star" I.star x

  let add x y =
    if is_zero x then y
    else if is_zero y then x
    else add x y

  let mul x y =
    if is_zero x || is_zero y then zero
    else if is_one x then y
    else if is_one y then x
    else mul x y
end

(* Before refinement code: *)
(*module K = MakeTransition(Var)*)

module K = struct
  module Tr = MakeTransition(Var)
  include Tr

  module CRARefinement = Refinement.DomainRefinement
      (struct
        include Tr
        let star = I.star

        (*let star x = Log.time "refine" I.star x*)

        let equal a b = ((Wedge.is_sat srk (guard a)) == `Unsat)
      end)

  let refine_star x = 
    let nnf_guard = Syntax.rewrite srk ~down:(Syntax.nnf_rewriter srk) (guard x) in
    (*Format.eprintf "  Top-level formula:  %a  \n" (Syntax.Formula.pp srk) nnf_guard;*)
    let to_dnf form = 
      match form with
      | `And top_and_list ->
        let dnf_form_no_labels = (* list list list *)
          List.map
            (fun top_and_child ->
              match Syntax.Formula.destruct srk top_and_child with
              | `Or or_list ->
                List.map
                  (fun or_child ->
                    match Syntax.destruct srk or_child with
                    | `And leaf -> leaf
                    | _ -> [or_child]
                  ) or_list
              | `And and_list -> [and_list]
              | _ -> [[top_and_child]]
            ) top_and_list
          in
        let cartesian_prod =
          let cartesian a b = List.concat (List.map (fun e1 -> List.map (fun e2 -> (e1 @ e2)) b) a) in 
          List.fold_left cartesian ([([])])
          in
        let distributed_list = cartesian_prod dnf_form_no_labels in (* list list *)
        Syntax.mk_or srk (List.map (Syntax.mk_and srk) distributed_list)
      | `Or dnf_list ->
        Syntax.mk_or srk
          (List.concat
            (List.map
              (fun or_of_ands ->
                match Syntax.Formula.destruct srk or_of_ands with
                | `Or list_of_ands -> list_of_ands
                | _ -> [or_of_ands]
              ) dnf_list
            )
          )
      | `Tru -> Syntax.mk_true srk
      | `Fls -> Syntax.mk_false srk
      | `Not x -> Syntax.mk_not srk x
      | `Quantify (`Exists, str, typ, x) -> Syntax.mk_exists srk ~name:str typ x
      | `Quantify (`Forall, str, typ, x) -> Syntax.mk_forall srk ~name:str typ x
      | `Atom (`Eq, left, right) -> Syntax.mk_eq srk left right
      | `Atom (`Leq, left, right) -> Syntax.mk_leq srk left right
      | `Atom (`Lt, left, right) -> Syntax.mk_lt srk left right
      | _ -> failwith "Don't support Prop, Ite"
    in
    let dnf_guard = Syntax.Formula.eval_memo srk to_dnf nnf_guard in
    let (guard_dis, one_dis) = 
      (match Syntax.Formula.destruct srk dnf_guard with
      | `Or disjuncts -> (disjuncts, false)
      | _ -> ([dnf_guard], true)
      )
      in
    (*Format.eprintf " UnsimpGuard dnf size : %d\n Formula:  %a\n%!" (List.length guard_dis) (Syntax.Formula.pp srk) dnf_guard;*)
    if one_dis then I.star x
    else
      let rec build_dnf needed_dis disjuncts =
        match disjuncts with
        | [] -> (needed_dis, false)
        | new_dis :: tl -> 
          let cur_dnf = Syntax.mk_or srk needed_dis in
          (match Smt.entails srk (guard x) cur_dnf with
          | `Yes -> (needed_dis, false)
          | `Unknown -> ([], true)
          | `No ->
            (match Smt.entails srk cur_dnf new_dis with
            | `Yes -> build_dnf [new_dis] tl
            | `Unknown -> ([], true)
            | `No ->
              (match Smt.entails srk new_dis cur_dnf with
              | `Yes -> build_dnf needed_dis tl
              | `Unknown -> ([], true)
              | `No -> build_dnf (new_dis :: needed_dis) tl)
            )
          ) 
        in
      let (needed_dis, bailed) = build_dnf [] guard_dis in
      if bailed then 
        I.star x
      else (
        (*Format.eprintf " SimpGuard dnf size : %d\n Formula:  %a\n%!" (List.length needed_dis) (Syntax.Formula.pp srk) (Syntax.mk_or srk needed_dis);*)
        let x_tr = BatEnum.fold (fun acc a -> a :: acc) [] (transform x) in
        let x_dnf = List.map (fun disjunct -> construct disjunct x_tr) needed_dis in
        if (List.length x_dnf) = 1 then I.star (List.hd x_dnf)
        else
          let result = CRARefinement.refinement x_dnf in
          result)    

  let to_dnf x =
    let open Syntax in
    let guard =
      rewrite srk
        ~down:(nnf_rewriter srk)
        ~up:(Nonlinear.uninterpret_rewriter srk)
        (guard x)
    in
    let x_tr = BatEnum.fold (fun acc a -> a :: acc) [] (transform x) in
    let solver = Smt.mk_solver srk in
    let rhs_symbols =
      BatEnum.fold (fun rhs_symbols (_, t) ->
          Symbol.Set.union rhs_symbols (symbols t))
        Symbol.Set.empty
        (transform x)
    in
    let project x =
      match Var.of_symbol x with
      | Some _ -> true
      | None -> Symbol.Set.mem x rhs_symbols
    in
    Smt.Solver.add solver [guard];
    let rec split disjuncts =
      match Smt.Solver.get_model solver with
      | `Unknown -> [x]
      | `Unsat ->
        BatList.filter_map (fun guard ->
            let interp_guard = Nonlinear.interpret srk guard in
            if Wedge.is_sat srk interp_guard = `Unsat then
              None
            else
              Some (construct interp_guard x_tr))
          disjuncts
      | `Sat m ->
        let disjunct =
          match Interpretation.select_implicant m guard with
          | Some implicant ->
            let cs = CoordinateSystem.mk_empty srk in
            Polyhedron.of_implicant ~admit:true cs implicant
            |> Polyhedron.try_fourier_motzkin cs project
            |> Polyhedron.implicant_of cs
            |> mk_and srk
          | None -> assert false
        in
        Smt.Solver.add solver [mk_not srk disjunct];
        split (disjunct::disjuncts)
    in
    split []

  let refine_star x =
    (* let x_dnf = to_dnf x in *)
    let x_dnf = Log.time "cra:to_dnf" to_dnf x in
    if (List.length x_dnf) = 1 then I.star (List.hd x_dnf)
    else CRARefinement.refinement x_dnf

  let star x = 
    if (!cra_refine_flag) then 
      Log.time "cra:refine_star" refine_star x
    else 
      Log.time "cra:star" I.star x

  (*let project = exists Var.is_global*)
end

(* ********************************************** *)

module IntMap = BatMap.Int
module IntSet = BatSet.Int

module AuxVarModuleCHC = struct
  type val_t = unit
  type val_sym = {
      value: unit; 
      symbol: Srk.Syntax.symbol
  }

  type srk_ctx_magic = Sctx.t
  let srk = srk

  let make_aux_variable name = 
    {value = ();
     symbol = Srk.Syntax.mk_symbol srk ~name `TyInt}

  let post_symbol =
    Memo.memo 
      (* Original code used by chora *)
      (*(fun sym ->
        match Var.of_symbol sym with
        | Some var ->
          Srk.Syntax.mk_symbol srk ~name:(Var.show var ^ "'") (Var.typ var :> Srk.Syntax.typ)
        | None -> assert false)*)
      (* FIXME *)
      (fun sym ->
        begin
        match Var.of_symbol sym with
        | Some var -> ()
        | None -> Var.register_var sym
        end;
        begin
        match Var.of_symbol sym with
        | Some var ->
          Srk.Syntax.mk_symbol srk ~name:(Var.show var ^ "'") (Var.typ var :> Srk.Syntax.typ)
        | None -> assert false
        end)
end

module ProcMap = IntMap

let procedure_names_map = ref ProcMap.empty

module ProcModuleCHC = struct
  module ProcMap = IntMap

  let proc_name_triple_string proc_key = 
    if ProcMap.mem proc_key !procedure_names_map then 
      let name = ProcMap.find proc_key !procedure_names_map in
      Format.sprintf "(%d,\"%s\")" proc_key name
    else
      Format.sprintf "(%d,?)" proc_key

  let proc_name_string proc_key = 
    if ProcMap.mem proc_key !procedure_names_map then 
      let name = ProcMap.find proc_key !procedure_names_map in
      Format.sprintf "%s" name
    else
      Format.sprintf "<unknown procedure(%d)>" proc_key
end

module ChoraCHC = ChoraCore.MakeChoraCore(ProcModuleCHC)(AuxVarModuleCHC)

open AuxVarModuleCHC
open ProcModuleCHC

let make_aux_predicate int_arity name = 
  Srk.Syntax.mk_symbol srk ~name 
    (`TyFun (List.init int_arity (fun n -> `TyInt), `TyBool))

(* ********************************************** *)

let is_syntactic_false srk expr = 
  match Syntax.destruct srk expr with
  | `Fls -> true
  | _ -> false

let is_syntactic_true srk expr = 
  match Syntax.destruct srk expr with
  | `Tru -> true
  | _ -> false

let get_const srk term = 
  match Syntax.Term.destruct srk term with
  | `App (func, args) -> 
    if ((List.length args) = 0) then Some func else None
  | _ -> None

let is_predicate srk expr = 
  match Syntax.destruct srk expr with
  | `App (func, args) -> 
    (match Syntax.expr_typ srk expr with
    | `TyBool -> true
    | _ -> false)
  | _ -> false

let id_of_predicate srk pred = 
  match Syntax.destruct srk pred with
  | `App (func, args) -> 
    (match Syntax.expr_typ srk pred with
    | `TyBool -> Syntax.int_of_symbol func
    | _ -> failwith "id_of_predicate called on non-bool predicate")
  | _ -> failwith "id_of_predicate called on non-application"

let id_of_var srk var =
  match Syntax.destruct srk var with
  | `Var (vnum, typ) -> vnum
  | _ -> failwith "id_of_var called on non-variable"

let typ_of_var srk var =
  match Syntax.destruct srk var with
  | `Var (vnum, typ) -> typ
  | _ -> failwith "typ_of_var called on non-variable"

let find_predicates srk expr = 
  let alg = function
    | `And conjuncts -> List.concat conjuncts
    | `Or disjuncts -> List.concat disjuncts
    | `Quantify (_, name, typ, phi) -> phi
    | `Not (phi) -> phi
    | `Proposition (`Var i) -> failwith "Var-proposition in CHC"
    | `Proposition (`App (p, args)) -> 
      (*if is_predicate srk p then [id_of_predicate srk p] else []*)
      [Syntax.int_of_symbol p]
    | `Atom (_, x, y) -> []
    | `Ite (cond, bthen, belse) -> cond @ bthen @ belse
    | `Tru -> []
    | `Fls -> []
  in
  Syntax.Formula.eval srk alg expr

module VarSet = BatSet.Int

type pred_num_t = int
type var_pos_list = Srk.Syntax.Symbol.t list
type predicate_occurrence = pred_num_t * var_pos_list
type (*'a*) linked_formula = predicate_occurrence *
                         (predicate_occurrence list) *
                         Sctx.t Srk.Syntax.Formula.t
                         (*'a Srk.Syntax.Formula.t*)

let logf_noendl ?(level=`info) =
  let sf = Format.std_formatter in 
  if (Log.level_leq (!Log.verbosity_level) level ||
      Log.level_leq (!my_verbosity_level) level)
  then Format.fprintf sf
  else Format.ifprintf sf

module Chc = struct

  module PredOcc = struct
    (* predicate occurrence *)
    type t = predicate_occurrence
    type pred_occ_tuple = predicate_occurrence
    type pred_occ_record = {
        pred_num:pred_num_t;
        vars:Srk.Syntax.Symbol.t list
    }

    let of_tuple ((pred:pred_num_t), (vars:var_pos_list)) : predicate_occurrence = 
      (pred, vars)

    let mk (pred:pred_num_t) (vars:var_pos_list) : predicate_occurrence = 
      (pred, vars)

    (* Using pred_occ_tuple *)
    let to_rec (pred_occ:pred_occ_tuple) : pred_occ_record =
      let (pred_num,vars) = pred_occ in
      {pred_num=pred_num;vars=vars}

    let to_tuple (pred_occ:pred_occ_tuple) : (pred_num_t * var_pos_list) =
      pred_occ

    (*
    (* Using pred_occ_record *)
    let to_rec (pred_occ:pred_occ_tuple) : pred_occ_record =
      pred_occ

    let to_tuple (pred_occ:pred_occ_record) : (pred_num_t * var_pos_list) =
      (pred_occ.pred_num,pred_occ.vars)
    *)

  end

  type t = linked_formula

  (* YYY *)

  let print_pred_occ ?(level=`info) srk pred_occ = 
    let (pred_num, var_symbols) = PredOcc.to_tuple pred_occ in 
    let n_vars = List.length var_symbols in 
    logf_noendl ~level "%s(" 
      (Syntax.show_symbol srk (Syntax.symbol_of_int pred_num));
    List.iteri 
      (fun i sym ->
        (*Format.printf "%s" (Syntax.show_symbol srk sym);*)
        logf_noendl ~level "%a" (Syntax.pp_symbol srk) sym;
        if i != n_vars - 1 then logf_noendl ~level ",")
      var_symbols;
    logf_noendl ~level ")"
  
  let print_linked_formula ?(level=`info) srk rule = 
    let (conc_pred, hyp_preds, phi) = rule in
    logf_noendl ~level "{ @[";
    List.iter 
      (fun pred -> print_pred_occ srk pred; logf_noendl ~level ";@ ")
      hyp_preds;
    logf_noendl ~level "%a@ -> " (Syntax.Formula.pp srk) phi;
    print_pred_occ ~level srk conc_pred;
    logf_noendl ~level "@] }@."
  
  let print_linked_formula_as_wedge ?(level=`info) srk rule = 
    let (conc_pred, hyp_preds, phi) = rule in
    logf_noendl ~level "{ @[";
    List.iter 
      (fun pred -> print_pred_occ srk pred; logf_noendl ~level ";@ ")
      hyp_preds;
    let all_preds = conc_pred::hyp_preds in 
    let all_pred_vars =
      List.concat
        (List.map 
          (fun occ -> 
            let (pred_num,vars) = PredOcc.to_tuple occ in 
            vars) all_preds) in
    let exists = (fun sym -> List.mem sym all_pred_vars) in 
    let wedge = Wedge.abstract ~exists srk phi in
    logf_noendl ~level "%a@ -> " Wedge.pp wedge;
    print_pred_occ ~level srk conc_pred;
    logf_noendl ~level "@] }@."

  let conc_pred_occ_of_linked_formula rule = 
      let (conc_pred, hyp_preds, phi) = rule in
      conc_pred
  
  let conc_pred_id_of_linked_formula rule = 
      let (conc_pred, hyp_preds, phi) = rule in
      let (pred_num, vars) = PredOcc.to_tuple conc_pred in
      pred_num
  
  let hyp_pred_ids_of_linked_formula rule = 
      let (conc_pred, hyp_preds, phi) = rule in
      List.map 
        (fun pred_occ ->
          let (pred_num, vars) = PredOcc.to_tuple pred_occ in
          pred_num)
        hyp_preds

  let transition_of_linked_formula rule = 
      let (conc_pred, hyp_preds, phi) = rule in
      let (conc_pred_num, conc_vars) = PredOcc.to_tuple conc_pred in
      assert (List.length hyp_preds = 1);
      let (hyp_pred_num, hyp_vars) = PredOcc.to_tuple (List.hd hyp_preds) in
      assert (hyp_pred_num = conc_pred_num);
      Var.reset_tables;
      List.iter (fun sym -> Var.register_var sym) hyp_vars;
      (* conc_vars and hyp_vars are lists of symbols *)
      let transform = 
        List.map2 
          (fun pre post -> 
              ((* pre-state as variable *)
               (match Var.of_symbol pre with
               | Some v -> v
               | _ -> failwith 
                  "Unregistered variable in transition_of_linked_formula"),
              (* post-state as term *)
              Syntax.mk_const srk post))
          hyp_vars
          conc_vars
        in
      K.construct phi transform

  (* Make a rule that corresponds to the identity transition, 
     on the model of the given model_rule.
     The returned rule will have the same predicate occurrences
     as model_rule.  *)
  let identity_linked_formula model_rule =
    let (conc_pred, hyp_preds, _) = model_rule in
    let (conc_pred_num, conc_vars) = PredOcc.to_tuple conc_pred in
    assert (List.length hyp_preds = 1);
    let (hyp_pred_num, hyp_vars) = PredOcc.to_tuple (List.hd hyp_preds) in
    assert (hyp_pred_num = conc_pred_num);
    let eq_atoms = List.fold_left2
      (fun atoms hyp_var conc_var ->
          let atom = Syntax.mk_eq srk 
            (Syntax.mk_const srk hyp_var) 
            (Syntax.mk_const srk conc_var) 
          in atom::atoms)
      [] 
      hyp_vars
      conc_vars
    in
    let phi = Syntax.mk_and srk eq_atoms in
    (conc_pred, hyp_preds, phi)
  
  let linked_formula_of_transition tr model_rule =
    if K.is_one tr then identity_linked_formula model_rule else
    let post_shim = Memo.memo 
        (fun sym -> Syntax.mk_symbol srk 
         ~name:("Post_"^(Syntax.show_symbol srk sym)) `TyInt) in
    let (tr_symbols, post_def) =
      BatEnum.fold (fun (symbols, post_def) (var, term) ->
          let pre_sym = Var.symbol_of var in
          match get_const srk term with
          | Some existing_post_sym ->
            ((pre_sym,existing_post_sym)::symbols,post_def)
          | None -> 
            let new_post_sym = post_shim pre_sym in
            let post_term = Syntax.mk_const srk new_post_sym in
            ((pre_sym,new_post_sym)::symbols,(Syntax.mk_eq srk post_term term)::post_def)
          )
        ([], [])
        (K.transform tr)
    in
    let body =
      SrkSimplify.simplify_terms srk (Syntax.mk_and srk ((K.guard tr)::post_def))
    in
    (* Now, body is a formula over the pre-state and post-state variable pairs
       found in tr_symbols.  I assume that the pre-state variables haven't changed,
       but the post-state variables may have changed.  Because the post-state 
       variables may have changed, I will look up each of the variables in the
       predicate-occurrence in the hypothesis of the model rule and find the
       (new?) post-state variable that it corresponds to, and then I'll put that 
       variable into the predicate-occurrence in the conclusion of the rule that
       I return.  *)
    let (conc_pred, hyp_preds, _) = model_rule in
    let (conc_pred_num, _) = PredOcc.to_tuple conc_pred in
    assert (List.length hyp_preds = 1);
    let (hyp_pred_num, hyp_vars) = PredOcc.to_tuple (List.hd hyp_preds) in
    assert (hyp_pred_num = conc_pred_num);
    let new_args = 
      List.map 
        (fun hyp_var -> 
           let rec go pairs = 
             match pairs with
             | (pre_sym, post_sym)::rest -> 
                     if hyp_var = pre_sym then post_sym else go rest
             | [] -> logf ~level:`fatal "  ERROR: missing symbol %a" (Syntax.pp_symbol srk) hyp_var;
                     failwith "Could not find symbol in linked_formula_of_transition"
           in go tr_symbols)
        hyp_vars in
    let new_conc_pred = PredOcc.of_tuple (conc_pred_num, new_args) in 
    (new_conc_pred, hyp_preds, body)

  (*
  let subst_in_pred pred var_to var_from = 
    let (pred_num, pred_vars) = pred in
    let new_vars = 
      List.map
        (fun old_var -> if old_var = var_from then var_to else old_var)
        pred_vars in
    (pred_num, new_vars)
  
  let subst_in_preds preds var_to var_from = 
    List.map
      (fun pred -> subst_in_pred pred var_to var_from)
      preds
  *)

  let make_vars_unique rule = 
    let (conc_pred, hyp_preds, phi) = rule in 
    let all_preds = conc_pred::hyp_preds in 
    let used_vars = ref Syntax.Symbol.Set.empty in 
    let pairs = ref [] in 
    let make_vars_unique_in_pred pred = 
      let (pred_num, pred_vars) = PredOcc.to_tuple pred in 
      let rec go pred_vars = 
        match pred_vars with 
        | pred_var::rest -> 
          let replaced_vars = go rest in 
          if Syntax.Symbol.Set.mem pred_var !used_vars 
          then 
            let new_var = 
              Syntax.mk_symbol srk 
                ~name:("Dedup_"^(Syntax.show_symbol srk pred_var)) 
                `TyInt in 
            pairs := (pred_var,new_var)::(!pairs); 
            new_var::replaced_vars
          else 
           (used_vars := Syntax.Symbol.Set.add pred_var !used_vars;
            pred_var::replaced_vars)
        | [] ->
          pred_vars
      in
      PredOcc.of_tuple (pred_num, go pred_vars)
    in
    let new_preds = List.map make_vars_unique_in_pred all_preds in
    match new_preds with
    | new_conc_pred :: new_hyp_preds ->
      let equalities = 
        List.map
          (fun (old_var,new_var) ->
             let old_c = Syntax.mk_const srk old_var in
             let new_c = Syntax.mk_const srk new_var in
             Syntax.mk_eq srk old_c new_c) 
          !pairs in
      let new_phi = Syntax.mk_and srk (phi::equalities) in 
      (new_conc_pred, new_hyp_preds, new_phi)
    | _ -> failwith "Should not happen"


  (** Given a formula phi and two predicate occurrences pred_occ1 and pred_occ2,
   *    of the form pred_occ1(v_1,...,v_n)
   *            and pred_occ2(w_1,...,w_n)
   *    substitute each occurrence of w_i with v_i in phi *)
  let substitute_args_pred pred_occ1 pred_occ2 phi = 
    (*Format.printf "  ~~ ~~  To-predicate:";
    print_pred_occ srk pred_occ1;
    Format.printf "@.";
    Format.printf "  ~~ ~~From-predicate:";
    print_pred_occ srk pred_occ2;
    Format.printf "@.";*)
    let (pred_num1, vs) = PredOcc.to_tuple pred_occ1 in
    let (pred_num2, ws) = PredOcc.to_tuple pred_occ2 in
    assert (pred_num1 = pred_num2);
    let sub sym = 
      let rec go list1 list2 =
        match (list1,list2) with
        | (vi::vrest,wi::wrest) ->
          if sym = wi
          then Syntax.mk_const srk vi
          else go vrest wrest
        | ([],[]) -> Syntax.mk_const srk sym
        | _ -> failwith "Unequal-length variable lists in substitute_args"
      in go vs ws 
      in
    let new_phi = Syntax.substitute_const srk sub phi in
    (*Format.printf "  ~~ ~~Formula before: %a@." (Syntax.Formula.pp srk) phi;
    Format.printf "  ~~ ~~Formula  after: %a@." (Syntax.Formula.pp srk) new_phi;*)
    new_phi
  
  (** Replace all skolem constants appearing in rule 
   *    with fresh skolem constants, except for those
   *    appearing in the given list of predicate occurrences *)
  let fresh_skolem_except rule pred_occs =
    let keep = 
      List.fold_left 
        (fun keep pred_occ ->
          let (pred_num, vars) = PredOcc.to_tuple pred_occ in
          List.fold_left
            (fun keep sym ->
               BatSet.Int.add (Syntax.int_of_symbol sym) keep)
            keep
            vars)
        BatSet.Int.empty
        pred_occs in
    let fresh_skolem =
      Memo.memo 
        (fun sym ->
          let name = name_of_symbol srk sym in
          let typ = Syntax.typ_symbol srk sym in
          Syntax.mk_symbol srk ~name typ) in
    let map_symbol sym = 
      if BatSet.Int.mem (Syntax.int_of_symbol sym) keep 
      then sym 
      else fresh_skolem sym in
    let freshen_pred_occ pred_occ = 
      let (pred_num, vars) = PredOcc.to_tuple pred_occ in
      let new_vars = List.map map_symbol vars in 
      PredOcc.of_tuple (pred_num, new_vars) in
    let (conc_pred, hyp_preds, phi) = rule in
    let new_conc_pred = freshen_pred_occ conc_pred in
    let new_hyp_preds = List.map freshen_pred_occ hyp_preds in
    let map_symbol_const sym = 
      Syntax.mk_const srk (map_symbol sym) in
    let new_phi = Syntax.substitute_const srk map_symbol_const phi in
    (new_conc_pred, new_hyp_preds, new_phi)
  
  (* Given two CHCs rule1 and rule2 that have the same conclusion predicate and 
   *   the same list of hypothesis predicates, rewrite rule2 to use the same
   *   variable names used by rule1 *)
  let substitute_args_rule rule1 rule2 = 
    let (conc_pred1, hyp_preds1, phi1) = rule1 in
    let (conc_pred2, hyp_preds2, phi2) = rule2 in
    let (conc_pred_num1, _) = PredOcc.to_tuple conc_pred1 in
    let (conc_pred_num2, _) = PredOcc.to_tuple conc_pred2 in
    assert (conc_pred_num1 = conc_pred_num2);
    let phi2 = substitute_args_pred conc_pred1 conc_pred2 phi2 in
    (* Note: the following asserts that the two hypothesis predicate 
         occurrence lists have the same order, which isn't strictly necessary *)
    let rec go preds1 preds2 phi =
      match (preds1,preds2) with
      | (pred1::more_preds1,pred2::more_preds2) ->
        (* The following call asserts that pred1 = pred2 *)
        let phi = substitute_args_pred pred1 pred2 phi in 
        go more_preds1 more_preds2 phi
      | ([],[]) -> phi
      | _ -> failwith "Unequal-length predicate lists in disjoin_linked_formulas"
      in
    let phi2 = go hyp_preds1 hyp_preds2 phi2 in
    (conc_pred1, hyp_preds1, phi2)
  
  let disjoin_linked_formulas rules =
    match rules with
    | [] -> failwith "Empty rule list in disjoin_linked_formulas"
    | [rule1] -> rule1
    | rule1::old_rules ->
      let (conc_pred1, hyp_preds1, phi1) = rule1 in
      (* FIXME: Should rewrite rule1 first so that it has no duplicate
         occurrences of variables in its predicates *)
      let new_phis = 
        List.map 
          (fun old_rule -> 
             let new_rule = substitute_args_rule rule1 old_rule in
             let new_rule = fresh_skolem_except new_rule (conc_pred1::hyp_preds1) in
             let (_,_, new_phi) = new_rule in
             new_phi)
          old_rules in
      (conc_pred1, hyp_preds1, Syntax.mk_or srk (phi1::new_phis))
  
  let subst_all outer_rule inner_rule =
    (*Format.printf "  ~~Inner rule initially:@.    ";
    print_linked_formula srk inner_rule;
    Format.printf "@.";*)
    let (outer_conc, outer_hyps, outer_phi) = outer_rule in
    let (inner_conc, inner_hyps, inner_phi) = inner_rule in
    let (inner_conc_pred_num, _) = PredOcc.to_tuple inner_conc in
    let (outer_hyps_matching, outer_hyps_non_matching) = 
      List.partition
        (fun pred_occ ->
          let (pred_num, vars) = PredOcc.to_tuple pred_occ in
          (pred_num = inner_conc_pred_num))
        outer_hyps
      in
    (if List.length outer_hyps_matching = 0 
    then failwith "Mismatched subst_all call"
    else ());
    let (new_hyps, new_phis) = 
      List.fold_left
        (fun (hyps,phis) outer_hyp -> 
          (*Format.printf "  ~~Substituting for one outer hypothesis...@.";*)
          let (outer_hyp_pred_num, outer_hyp_args) = PredOcc.to_tuple outer_hyp in
          assert (outer_hyp_pred_num = inner_conc_pred_num);
          let new_phi = substitute_args_pred outer_hyp inner_conc inner_phi in
          let new_rule = (outer_hyp, inner_hyps, new_phi) in
          (*Format.printf "  ~~Rule after substitute_args_pred and before fresh_skolem:@.    ";
          print_linked_formula srk new_rule;
          Format.printf "@.";*)
          let (new_conc, subbed_hyps, new_phi) = 
            fresh_skolem_except new_rule [outer_hyp] in  
          (subbed_hyps @ hyps, new_phi::phis))
        ([],[])
        outer_hyps_matching
      in
    let phi = Syntax.mk_and srk (outer_phi::new_phis) in
    let hyps = outer_hyps_non_matching @ new_hyps in
    (outer_conc, hyps, phi)

end

let linked_formula_has_hyp rule target_hyp_num = 
  let (conc, hyps, phi) = rule in
  List.fold_left 
    (fun running hyp -> 
       let (pred_num, args) = Chc.PredOcc.to_tuple hyp in
       (running || (pred_num = target_hyp_num)))
    false
    hyps;;

let build_linked_formulas srk1 srk2 phi query_pred =
  let rec get_rule vars rules phi = 
    match Syntax.destruct srk1 phi with
    | `Quantify (`Forall, nam, typ, expr) ->
       get_rule ((nam,typ)::vars) rules expr
    | `Or [nothyp; conc] ->
       (match Syntax.destruct srk1 nothyp with 
       | `Not (hyp) -> (hyp,conc,vars)::rules (* reverse? *)
       | _ -> logf ~level:`always "  Bad Rule: %a" (Syntax.Formula.pp srk1) phi;
              failwith "Unrecognized rule format (No negated hypothesis)")
    | _ -> logf ~level:`always "  Bad Rule: %a" (Syntax.Formula.pp srk1) phi;
           failwith "Unrecognized rule format (No top-level quantifier or disjunction)"
    in
  let rules = 
    match Syntax.destruct srk1 phi with
    | `And (parts) -> 
      List.fold_left 
        (fun rules psi -> get_rule [] rules psi)
        []
        parts
    | `Tru -> logf ~level:`always "RESULT: SAT (warning: empty CHC program; EMPTY_PROGRAM)";
      []
    | _ -> 
      (*uncomment to allow*) get_rule [] [] phi
      (*forbid*) (*failwith "Currently forbidden: single-clause CHC program"*)
    in 
  (* Filter out 'dummy rules' having conclusion 'true' *)
  let rules = List.filter 
    (fun (hyp,conc,vars) -> not (is_syntactic_true srk1 conc)) rules in 
  let rename_pred_internal sym = 
    let name = Syntax.show_symbol srk1 sym in
    Syntax.mk_symbol srk2 ~name:name `TyBool
    in
  let rename_pred = Memo.memo rename_pred_internal in
  let linked_formula_of_rule (hyp,conc,vars) = 
    let var_to_skolem_internal var = 
      (let (name, typ) = List.nth vars var in
      match typ with 
      | `TyInt | `TyBool -> Syntax.mk_symbol srk2 ~name:name `TyInt 
      | `TyReal -> failwith "Unrecognized rule format (Real-valued variable)")
      in
    let var_to_skolem = Memo.memo var_to_skolem_internal in
    let convert_formula expr = 
      let mut_equations = ref [] in
      let mut_predicates = ref [] in
      let mut_booleans = ref Syntax.Symbol.Set.empty in
      let rec go_formula expr = 
        begin
          match Syntax.Formula.destruct srk1 expr with
          (* Negation node *)
          | `Not p ->
            begin
              match Syntax.Formula.destruct srk1 p with
              | `Proposition (`Var var) ->
                (* Special case: *)
                (* The boolean quantified variable var appears negatively here. *)
                (* We replace v with an integer variable w and assert w == 0. *)
                let sym = var_to_skolem var in 
                mut_booleans := Syntax.Symbol.Set.add sym !mut_booleans;
                Syntax.mk_eq srk2 (Syntax.mk_const srk2 sym) (Syntax.mk_real srk2 QQ.zero) 
              | _ -> 
              (* General case of negation: *)
              let subexpr = go_formula p in
              Syntax.mk_not srk2 subexpr
            end
          (* Non-recursive nodes *)
          | `Tru -> Syntax.mk_true srk2
          | `Fls -> Syntax.mk_false srk2
          | `Proposition (`Var var) ->
            (* The boolean quantified variable var appears positively here. *)
            (* We replace v with an integer variable w and assert w == 1. *)
            let sym = var_to_skolem var in 
            mut_booleans := Syntax.Symbol.Set.add sym !mut_booleans;
            Syntax.mk_eq srk2 (Syntax.mk_const srk2 sym) (Syntax.mk_real srk2 QQ.one) 
          | `Proposition (`App (f, args)) ->
            (* A horn-clause-predicate occurrence *)
            let fsym = rename_pred f in 
            let fnumber = Syntax.int_of_symbol fsym in
            let rec accum_arg_info (arglist: (('a, 'b) Syntax.expr) list) symbollist = 
              match arglist with
              | [] -> symbollist
              | orig_arg::more_args ->
                (* orig_arg is an argument to a horn-clause predicate *)
                begin
                  match Syntax.Expr.refine srk1 orig_arg with
                  | `Term arg ->
                  begin
                    (* Integer argument to horn-clause predicate *)
                    match Syntax.destruct srk1 arg with
                    | `Var (v, `TyInt) -> 
                      accum_arg_info more_args ((var_to_skolem v)::symbollist)
                    | `Var (v, `TyReal) ->
                      failwith "Unrecognized rule format (Got real predicate argument)"
                    | _ -> 
                      let term = go_term arg in
                      let termsymbol = Syntax.mk_symbol srk2 ~name:"TermSymbol" `TyInt in
                      let termeq = Syntax.mk_eq srk2 (Syntax.mk_const srk2 termsymbol) term in
                      mut_equations := termeq :: !mut_equations;
                      accum_arg_info more_args (termsymbol::symbollist)
                  end
                  | `Formula arg ->
                  begin
                    (* Boolean argument to horn-clause predicate *)
                    match Syntax.Formula.destruct srk1 arg with
                    | `Proposition (`Var var) ->
                      (* Common case: boolean variable *)
                      let sym = var_to_skolem var in 
                      (*mut_booleans := Syntax.Symbol.Set.add sym !mut_booleans;*)
                      accum_arg_info more_args (sym::symbollist)
                    | _ -> 
                      let subformula = go_formula arg in
                      let formulasymbol = Syntax.mk_symbol srk2 ~name:"FormulaSymbol" `TyInt in
                      let formulatrue = 
                        (Syntax.mk_eq srk2 
                          (Syntax.mk_const srk2 formulasymbol) 
                          (Syntax.mk_real srk2 (QQ.one))) in
                      let formulafalse = 
                        (Syntax.mk_eq srk2 
                          (Syntax.mk_const srk2 formulasymbol) 
                          (Syntax.mk_real srk2 (QQ.zero))) in
                      let notf f = Syntax.mk_not srk2 f in
                      let formulaiff = 
                          Syntax.mk_or srk2 
                            [Syntax.mk_and srk2 [ formulatrue;      subformula]; 
                             Syntax.mk_and srk2 [formulafalse; notf subformula]]
                      in
                      mut_equations := formulaiff :: !mut_equations;
                      accum_arg_info more_args (formulasymbol::symbollist)
                  end
                end
              in
            let argsymbols = accum_arg_info args [] in
            let pred_occ = Chc.PredOcc.of_tuple (fnumber, (List.rev argsymbols)) in
            mut_predicates := pred_occ :: !mut_predicates;
            Syntax.mk_true srk2
          (* Recursive nodes: bool from something *)
          | `Ite (cond, bthen, belse) ->
            let cond_f = go_formula cond in
            let bthen_f = go_formula bthen in 
            let belse_f = go_formula belse in 
            Syntax.mk_ite srk2 cond_f bthen_f belse_f
          (* Recursive nodes: bool from bool *)
          | `And exprs -> 
            let subexprs = combine_formulas exprs in  
            Syntax.mk_and srk2 subexprs
          | `Or exprs ->
            let subexprs = combine_formulas exprs in  
            Syntax.mk_or srk2 subexprs
          (* Recursive nodes: bool from int *)
          | `Atom (op, s, t) -> 
            let (s_sub,t_sub) = combine_two_terms s t in
            (match op with
            | `Eq ->  Syntax.mk_eq srk2 s_sub t_sub
            | `Leq -> Syntax.mk_leq srk2 s_sub t_sub 
            | `Lt ->  Syntax.mk_lt srk2 s_sub t_sub)
          (* Format-violating nodes: *)
          | `Quantify (_,_,_,_) -> 
            logf ~level:`fatal "  Bad Rule: %a" (Syntax.Formula.pp srk1) expr;
            failwith "Unrecognized rule format (Got quantifier in rule)"
        end
      and go_term term = 
        begin
          match Syntax.Term.destruct srk1 term with
          (* Non-recursive nodes *)
          | `Real qq -> Syntax.mk_real srk2 qq
          | `Var (var, `TyInt) -> 
            let sym = var_to_skolem var in 
            Syntax.mk_const srk2 sym
          (* Recursive nodes: int from int *)
          | `Add terms ->
            let subexprs = combine_terms terms in  
            Syntax.mk_add srk2 subexprs
          | `Mul terms ->
            let subexprs = combine_terms terms in  
            Syntax.mk_mul srk2 subexprs
          | `Binop (`Div, s, t) ->
            let (s_sub,t_sub) = combine_two_terms s t in
            Syntax.mk_div srk2 s_sub t_sub
          | `Binop (`Mod, s, t) ->
            let (s_sub,t_sub) = combine_two_terms s t in
            Syntax.mk_mod srk2 s_sub t_sub
          | `Unop (`Floor, t) ->
            let subexpr = go_term t in
            Syntax.mk_floor srk2 subexpr
          | `Unop (`Neg, t) ->
            let subexpr = go_term t in
            Syntax.mk_neg srk2 subexpr
          | `Ite (cond, bthen, belse) ->
            let cond_f = go_formula cond in
            let bthen_f = go_term bthen in 
            let belse_f = go_term belse in 
            Syntax.mk_ite srk2 cond_f bthen_f belse_f
          (* Format-violating nodes: *)
          | `Var (v, `TyReal) ->
            logf ~level:`fatal "  Bad Rule: %a" (Syntax.Term.pp srk1) term;
            failwith "Unrecognized rule format (Got real-valued variable)"
          | `App (func, args) -> 
            logf ~level:`fatal "  Bad Rule: %a" (Syntax.Term.pp srk1) term;
            failwith "Unrecognized rule format (Got function application)"
        end
      and combine_formulas exprs = 
        begin
          List.fold_left
            (fun subexprs ex -> 
                let ex_s = go_formula ex in 
                (ex_s::subexprs))
            []
            exprs
        end
      and combine_terms exprs = 
        begin 
          List.fold_left
            (fun subexprs ex -> 
                let ex_s = go_term ex in 
                (ex_s::subexprs))
            []
            exprs
        end
      and combine_two_terms s t = 
        begin
          let s_sub = go_term s in
          let t_sub = go_term t in 
          (s_sub,t_sub)
        end
      in
      let phi = go_formula expr in
      (phi, !mut_predicates, !mut_equations, !mut_booleans)
      (* end of convert_formula *)
    in
    let (hyp_sub,hyp_preds,hyp_eqs,hyp_bools) = convert_formula hyp in
    let (conc_sub,conc_preds,conc_eqs,conc_bools) = convert_formula conc in
    let conc_pred_occ = match conc_preds with
      | [conc_pred_occ] -> conc_pred_occ
      | [] -> 
        if (not (is_syntactic_false srk2 conc_sub))
        then failwith "Unrecognized rule format (Non-false non-predicate conclusion)"
        else (query_pred, [])
      | _ -> failwith "Unrecognized rule format (Multiple conclusion predicate)"
    in 
    let eqs = hyp_eqs @ conc_eqs in
    let bools = Syntax.Symbol.Set.to_list 
      (Syntax.Symbol.Set.union hyp_bools conc_bools) in
    let bool_constraints = 
      List.map 
        (fun boolsym ->
           Syntax.mk_or srk2
             [(Syntax.mk_eq srk2 
               (Syntax.mk_const srk2 boolsym) 
              (Syntax.mk_real srk2 (QQ.zero))); 
             (Syntax.mk_eq srk2 
               (Syntax.mk_const srk2 boolsym) 
             (Syntax.mk_real srk2 (QQ.one)))])
       bools in
    let phi = Syntax.mk_and srk2 (hyp_sub::(eqs @ bool_constraints)) in
    let new_rule = (conc_pred_occ, hyp_preds, phi) in 
    (Chc.make_vars_unique new_rule)
    (* *)
  in
  List.map linked_formula_of_rule rules

let new_empty_matrix () = ref IntPairMap.empty

let assign_matrix_element matrix rowid colid value = 
  matrix := IntPairMap.add (rowid, colid) value !matrix;;

let modify_def_matrix_element matrix rowid colid defaultvalue func = 
  matrix := IntPairMap.modify_def 
    defaultvalue (rowid, colid) func !matrix;;

let get_matrix_element matrix rowid colid =
  IntPairMap.find (rowid, colid) !matrix;;

let has_matrix_element matrix rowid colid =
  IntPairMap.mem (rowid, colid) !matrix

let get_matrix_element_opt matrix rowid colid =
  if has_matrix_element matrix rowid colid 
  then Some (get_matrix_element matrix rowid colid)
  else None;;

let remove_matrix_element matrix rowid colid =
  matrix := (IntPairMap.remove (rowid, colid) !matrix)

let matrix_row_iteri matrix rowid func = 
  IntPairMap.iter 
    (fun (rowid',colid') value ->
      if rowid' != rowid then () else
      func rowid colid' value)
    !matrix;;

let matrix_col_iteri matrix colid func = 
  IntPairMap.iter 
    (fun (rowid',colid') value ->
      if colid' != colid then () else
      func rowid' colid value)
    !matrix;;

let print_scc ?(level=`info) scc = 
  logf_noendl ~level "SCC: [";
  List.iter
    (fun p -> 
      logf_noendl ~level "%a,"
      (Syntax.pp_symbol srk)
      (Syntax.symbol_of_int p))
    scc;
  logf_noendl ~level "]@."

let print_condensed_graph ?(level=`info) callgraph_sccs = 
  logf ~level "SCC list in processing order:";
  List.iter print_scc callgraph_sccs

(* Substitute summaries of lower SCCs into this predicate's rules *)
let subst_summaries rules summaries =
  List.map
    (fun rule ->
     let (conc, hyps, phi) = rule in
     List.fold_left 
       (fun rule_inprog hyp -> 
          let (pred_num, args) = Chc.PredOcc.to_tuple hyp in
          if BatMap.Int.mem pred_num summaries then
            let pred_summary = BatMap.Int.find pred_num summaries in
            (if linked_formula_has_hyp rule_inprog pred_num then
              Chc.subst_all rule_inprog pred_summary
            else rule_inprog)
          else 
            rule_inprog)
       rule
       hyps)
    rules

let build_rule_list_matrix scc rulemap summaries const_id = 
  let rule_list_matrix = new_empty_matrix () in
  logf ~level:`info "  Finding rules";
  List.iter
    (fun p ->
      let p_rules = subst_summaries (BatMap.Int.find p rulemap) !summaries in
      (* let p_rules = 
        List.map
          (fun rule ->
           let (conc, hyps, phi) = rule in
           List.fold_left 
             (fun rule_inprog hyp -> 
                let (pred_num, args) = hyp in
                if BatMap.Int.mem pred_num !summaries then
                  let pred_summary = BatMap.Int.find pred_num !summaries in
                  (if linked_formula_has_hyp rule_inprog pred_num then
                    subst_all rule_inprog pred_summary
                  else rule_inprog)
                else 
                  rule_inprog)
             rule
             hyps)
        p_rules in *)
      List.iter 
        (fun rule ->
           let (conc, hyps, phi) = rule in
           match hyps with
           | [hyp] ->
             let (hyp_pred_num, args) = hyp in
             modify_def_matrix_element 
                rule_list_matrix p hyp_pred_num [] (fun rs -> rule::rs)
           | [] ->
             modify_def_matrix_element 
                rule_list_matrix p const_id [] (fun rs -> rule::rs)
             (*let rs = BatMap.Int.find_default [] p !summary_list_vector in
             summary_list_vector := BatMap.Int.add p (rule::rs) !summary_list_vector*)
           | _ -> failwith "Non-superlinear CHC systems are not yet suppored")
        p_rules) 
    scc;
  rule_list_matrix

let build_rule_matrix scc rulemap summaries const_id = 
  (* First build a matrix whose entries are lists of rules. 
     Then, disjoin the elements of each such list to produce
     a matrix whose entries are single rules. *)
  let rule_list_matrix = 
    build_rule_list_matrix scc rulemap summaries const_id in
  let rule_matrix = new_empty_matrix () in
  logf ~level:`info "  Disjoining CHCs";
  List.iter
    (fun p ->
      matrix_row_iteri
        rule_list_matrix
        p
        (fun _ colid rules ->
          (*Format.printf "    rowid:%d colid:%d@." p colid;
          List.iter
            (fun r ->
            Format.printf "    - A rule to disjoin: ";
            print_linked_formula srk r;
            Format.printf "@.")
          rules;*)
          let combined_rule = Chc.disjoin_linked_formulas rules in
          assign_matrix_element rule_matrix p colid combined_rule)
    ) scc;
  rule_matrix  

let analyze_query_predicate rule_matrix query_int const_id = 
  match get_matrix_element_opt rule_matrix query_int const_id with
  | None -> failwith "Missing final CHC"
  | Some final_rule -> 
    logf_noendl ~level:`info "Final CHC: @.  ";
    Chc.print_linked_formula ~level:`info srk final_rule;
    logf ~level:`info "";
    let (conc, hyps, final_phi) = final_rule in
    begin
      match Wedge.is_sat srk final_phi with
      | `Sat -> logf ~level:`always "RESULT: UNKNOWN (final constraint is sat)"
      | `Unsat -> logf ~level:`always "RESULT: SAT (final constraint is unsat)"
      | `Unknown -> 
        if not !retry_flag then 
          logf ~level:`always "RESULT: UNKNOWN (final constraint unknown)"
        else
        begin
          logf ~level:`info "Preliminary: unknown (final constraint unknown)";
          logf ~level:`info "Retrying...";
          let wedge = Wedge.abstract srk final_phi in
          if Wedge.is_bottom wedge
          then logf ~level:`always "RESULT: SAT (final constraint is unsat)"
          else logf ~level:`always "RESULT: UNKNOWN (final constraint unknown)"
        end
    end

let eliminate_predicate rule_matrix (*query_int*) const_id p =
  (*if p = query_int then () else*)
  logf ~level:`info "   -Eliminating %a" 
    (Syntax.pp_symbol srk) 
    (Syntax.symbol_of_int p);
  (* First, eliminate p's direct recursion if it exists *)
  begin
    if has_matrix_element rule_matrix p p then
      (* Obtain the direct-recursion entry from the matrix *)
      let combined_rec = get_matrix_element rule_matrix p p in
      logf_noendl ~level:`info "    Combined recursive CHC:@.    ";
      Chc.print_linked_formula ~level:`info srk combined_rec;
      (* Star it *)
      let tr = Chc.transition_of_linked_formula combined_rec in
      logf_noendl ~level:`info "    As transition:@.    %a@." K.pp tr;
      let tr_star = K.star tr in 
      logf_noendl ~level:`info "    Starred:@.    %a@." K.pp tr_star;
      let tr_star_rule = 
        Chc.linked_formula_of_transition tr_star combined_rec in
      logf_noendl ~level:`info "    Starred as CHC:@.    ";
      Chc.print_linked_formula ~level:`info srk tr_star_rule;
      (* Use substitution to apply the starred rule onto 
         every other matrix entry corresponding to a rule 
         that has conclusion p *)
      matrix_row_iteri rule_matrix p
        (fun _ hyp nonrec_rule ->
          (* *)
          let sub_rule = Chc.subst_all tr_star_rule nonrec_rule in
          assign_matrix_element rule_matrix p hyp sub_rule);
      remove_matrix_element rule_matrix p p
      (* At this point, p's rules are all non-recursive *)
  end;
  (* Now, remove "uses" of p in other predicates' rules *)
  matrix_col_iteri rule_matrix p 
    (fun q _ qrule ->
      (* qrule has hypothesis p and conclusion q *)
      matrix_row_iteri rule_matrix p
        (fun _ r prule ->
          assert (r != p);
          (* prule has hypothesis r and conclusion p *)
          (* Now, we substitute prule into qrule, 
             creating a new rule with hypothesis r and conclusion q, 
             thus eliminating a use of p. *)
          let sub_rule = Chc.subst_all qrule prule in
          match get_matrix_element_opt rule_matrix q r with
          | None ->
            assign_matrix_element rule_matrix q r sub_rule
          | Some prev_rule ->
            let combined_rule = 
              Chc.disjoin_linked_formulas [prev_rule; sub_rule] in
            assign_matrix_element rule_matrix q r combined_rule));
  (* Now, set all the entries in column p to zero *)
  matrix_col_iteri rule_matrix p 
    (fun q _ _ -> remove_matrix_element rule_matrix q p)
  (* At this point, p has been eliminated from the system *)

let make_chc_projection_and_symbols rule = 
  let (conc, hyps, _) = rule in
  let occs = conc::hyps in
  let arg_list = List.fold_left
    (fun running_args occ ->
       let (_, args) = Chc.PredOcc.to_tuple occ in
       List.append args running_args)
    []
    occs in
  let projection x =
    List.mem x arg_list in
  (projection, arg_list)

(* Create a new CHC representing the hypothetical summary of some procedure,
     given the info_structure that contains the formula (not yet a CHC) for
     the hypothetical summary and the names of the bounding-function 
     symbols (B_in1, B_in2, ...), and the CHC of the fact (i.e., base case) 
     from which that hypothetical sumary was computed. 
   Accomplishing this is simple.
   We are given the constraint formula, info_structure.call_abstraction_fmla,
     and we already have a list of all of the hypothesis and conclusion
     predicate occurrences in fact_pred_occ, and we only need
     to add one more: we need to create a new hypothesis predicate
     occurrence that holds onto all the bounding symbols.  
   In this function, we create that predicate, create an occurrence of it,
     attach it to the list of hypothesis predicate occurrences, and combine
     it with the constraint formula from info_structure to obtain the desired
     CHC. *)
let make_hypothetical_summary_chc info_structure fact_pred_occ : (*'a*) linked_formula =
    let bounding_symbol_list = List.map
      (fun (sym, corresponding_term) -> sym)
      info_structure.ChoraCHC.bound_pairs in 
    let n_bounding_symbols = List.length bounding_symbol_list in
    let new_pred = make_aux_predicate n_bounding_symbols "AuxGlobalPredicate" in
    let new_pred_occ = Chc.PredOcc.of_tuple
      (Srk.Syntax.int_of_symbol new_pred, bounding_symbol_list) in
    (fact_pred_occ, [new_pred_occ], info_structure.call_abstraction_fmla)

let make_final_summary_chc summary_fmla fact_pred_occ : (*'a*) linked_formula =
    (fact_pred_occ, [], summary_fmla)

let summarize_nonlinear_scc scc rulemap summaries = 
  logf ~level:`info "SCC: non-super-linear@.";
  let subbed_chcs_map = 
    List.fold_left
      (fun subbed_chcs_map p ->
        let p_chcs = subst_summaries (BatMap.Int.find p rulemap) !summaries in
        ProcMap.add p p_chcs subbed_chcs_map)
      ProcMap.empty
      scc in 
  let (bounds_map, hyp_sum_map, fact_pred_occ_map) = 
    List.fold_left
      (fun (bounds_map, hyp_sum_map, fact_pred_occ_map) p ->
        let p_chcs = ProcMap.find p subbed_chcs_map in
        let p_facts = 
          List.filter
            (fun chc -> let (conc, hyps, phi) = chc in List.length hyps == 0)
            p_chcs in
        let p_fact = Chc.disjoin_linked_formulas p_facts in
        let (projection, pre_symbols) = make_chc_projection_and_symbols p_fact in
        let tr_symbols = [] in
          (* List.map (fun sym -> (sym, AuxVarModuleCHC.post_symbol sym)) pre_symbols in *)
        let (fact_pred_occ, fact_hyps, fact_phi) = p_fact in
        (assert ((List.length fact_hyps) = 0));
        (* Call into ChoraCore to generalize the fact into a hypothetical summary formula,
             along with a list of bounding symbols, stored together in bounds_structure *)
        let bounds_structure = 
          ChoraCHC.make_hypothetical_summary fact_phi tr_symbols projection in
        (* Concept: make the hypothetical summary formula into a hypothetical summary
             CHC by attaching a new ``auxiliary global variable'' predicate for 
             the predicate's bounding functions. *)
        let hyp_sum_chc = make_hypothetical_summary_chc bounds_structure fact_pred_occ in
        (ProcMap.add p bounds_structure bounds_map, 
         ProcMap.add p hyp_sum_chc hyp_sum_map,
         ProcMap.add p fact_pred_occ fact_pred_occ_map))
      (ProcMap.empty, ProcMap.empty, ProcMap.empty)
      scc in
  let rec_fmla_map = 
    List.fold_left
      (fun rec_fmla_map p ->
        let p_chcs = ProcMap.find p subbed_chcs_map in
        let p_rules = 
          List.filter
            (fun chc -> let (conc, hyps, phi) = chc in List.length hyps != 0)
            p_chcs in
        let p_subbed_rules = subst_summaries p_rules hyp_sum_map in
        let p_rec_rule = Chc.disjoin_linked_formulas p_subbed_rules in
        let (_,_,rec_rule_phi) = p_rec_rule in
        ProcMap.add p rec_rule_phi rec_fmla_map)
      ProcMap.empty
      scc in
  let depth_bound_fmla_map = 
    List.fold_left
      (fun depth_bound_fmla_map p ->
        let depth_bound_fmla = Srk.Syntax.mk_true srk in
        ProcMap.add p depth_bound_fmla depth_bound_fmla_map)
      ProcMap.empty
      scc in
  let height_var = make_aux_variable "H" in 
  (* When changing this to use dual-height, I need to compute "excepting" *)
  let height_model = ChoraCHC.RB height_var in
  let excepting = Srk.Syntax.Symbol.Set.empty in
  let summary_fmla_list = 
    ChoraCHC.make_height_based_summaries
      rec_fmla_map bounds_map depth_bound_fmla_map scc height_model excepting in
  let summary_chc_list = List.map
    (fun (p,fmla) -> 
        let fact_pred_occ = ProcMap.find p fact_pred_occ_map in
        (p, make_final_summary_chc fmla fact_pred_occ))
    summary_fmla_list in 
  List.iter
    (fun (p,chc) -> summaries := (BatMap.Int.add p chc !summaries)) 
    summary_chc_list

(* Okay, given that it is non-linear, what do you do? *)
(* Run over all facts *)
(* Call:
   let hs_projection x = 
     (let symbol_name = Srk.Syntax.show_symbol srk x in 
     let this_name_is_a_param_prime = Str.string_match param_prime symbol_name 0 in
     if this_name_is_a_param_prime then 
       ((*Format.printf "Rejected primed param symbol %s" symbol_name;*) false)
     else
       ((List.fold_left 
           (fun found (vpre,vpost) -> found || vpre == x || vpost == x) 
           false tr_symbols)
         || 
         is_var_global x
       ))
   let bounds = ChoraCHC.make_hypothetical_summary base_case_fmla tr_symbols hs_projection
*)
(* Then, substitute those in *)
(* Then, call the code that makes the height-based summaries
  let summary_fmla_list = 
    ChoraCHC.make_height_based_summaries
      rec_fmla_map bounds_map depth_bound_formula_map proc_key_list height_model excepting in
*)
(* XXX *)

let detect_linear_scc scc rulemap summaries = 
  List.fold_left (* for p in scc *)
    (fun is_linear p -> is_linear &&
      begin
        let p_rules = BatMap.Int.find p rulemap in
        List.fold_left (* for p_rule in p_rules *)
          (fun is_linear_rule rule -> is_linear_rule &&
             begin
               let (conc, hyps, phi) = rule in
               let n_scc_hyps_this_rule = 
               List.fold_left (* for hyp in hyps *)
                 (fun n_scc_hyps hyp ->
                   let (hyp_pred_num, args) = Chc.PredOcc.to_tuple hyp in
                   if BatMap.Int.mem hyp_pred_num !summaries 
                   then n_scc_hyps
                   else (n_scc_hyps + 1))
                 0
                 hyps in
               (n_scc_hyps_this_rule <= 1)
             end)
          true
          p_rules
      end)
    true
    scc

let summarize_linear_scc scc rulemap summaries = 
  logf ~level:`info "SCC: linear@.";
  let const_id = (* (List.hd (List.sort compare scc)) *) -1 in
  assert (not (List.mem const_id scc));
  let rule_matrix = build_rule_matrix scc rulemap summaries const_id in
  (* Now, eliminate predicates from this SCC one at a time*)
  logf ~level:`info "  Eliminating predicates";
  List.iter (eliminate_predicate rule_matrix (*query_int*) const_id) scc;
  (* The remaining matrix entries are summaries; 
     they have no hypothesis predicate occurrences *)
  List.iter
    (fun p ->
      match get_matrix_element_opt rule_matrix p const_id with
      | None -> failwith "Missing const_id entry in rule_matrix"
      | Some rule -> summaries := (BatMap.Int.add p rule !summaries)) 
    scc

let handle_query_predicate scc rulemap summaries query_int = 
  logf ~level:`info "Analysis of query predicate:@.";
  let const_id = -1 in
  let rule_matrix = build_rule_matrix scc rulemap summaries const_id in
  (* The above call boils down to one disjoin_linked_formulas call *)
  analyze_query_predicate rule_matrix query_int const_id

let analyze_scc finished_flag summaries rulemap query_int scc =
  if !finished_flag then () else
  print_scc scc;
  match scc with
  | [p] when p = query_int ->
    handle_query_predicate scc rulemap summaries query_int;
    finished_flag := true
  | _ -> 
    if detect_linear_scc scc rulemap summaries 
    then summarize_linear_scc scc rulemap summaries
    else summarize_nonlinear_scc scc rulemap summaries

let print_summaries summaries = 
  logf ~level:`always "\n** Summaries as formulas **\n";
  BatMap.Int.iter
    (fun pred_num summary_rule ->
        Chc.print_linked_formula ~level:`always srk summary_rule;
        logf ~level:`always "  ")
    !summaries;
  logf ~level:`always "\n** Summaries as wedges **\n";
  BatMap.Int.iter
    (fun pred_num summary_rule ->
        Chc.print_linked_formula_as_wedge ~level:`always srk summary_rule;
        logf ~level:`always "  ")
    !summaries

let analyze_ruleset rules query_int = 
  let callgraph = List.fold_left
    (fun graph rule ->
      let conc_pred_id = Chc.conc_pred_id_of_linked_formula rule in
      let hyp_pred_ids = Chc.hyp_pred_ids_of_linked_formula rule in
      List.fold_left
        (fun g p -> CallGraph.add_edge g conc_pred_id p)
        graph
        hyp_pred_ids)
    CallGraph.empty
    rules
  in
  let rulemap = List.fold_left
    (fun rulemap rule ->
      let conc_pred_id = Chc.conc_pred_id_of_linked_formula rule in
      BatMap.Int.add
        conc_pred_id
        (rule::(BatMap.Int.find_default [] conc_pred_id rulemap))
        rulemap)
    BatMap.Int.empty
    rules
  in
  let callgraph_sccs = CallGraphSCCs.scc_list callgraph in
  (* print_condensed_graph callgraph_sccs; *)
  let summaries = ref BatMap.Int.empty in
  let finished_flag = ref false in
  List.iter
    (analyze_scc finished_flag summaries rulemap query_int)
    callgraph_sccs;
  (if !print_summaries_flag then print_summaries summaries)

let analyze_smt2 filename =  
  (* FIXME let Z3 read the whole file... *)
  let chan = open_in filename in
  let str = really_input_string chan (in_channel_length chan) in
  close_in chan;
  let z3ctx = Z3.mk_context [] in
  let phi = SrkZ3.load_smtlib2 ~context:z3ctx parsingCtx str in
  let query_sym = Syntax.mk_symbol srk ~name:"QUERY" `TyBool in
  let query_int = Syntax.int_of_symbol query_sym in  
  let rules = build_linked_formulas parsingCtx srk phi query_int in 
  List.iter 
    (fun rule -> 
        logf_noendl ~level:`info "Incoming CHC: @.  ";
        Chc.print_linked_formula srk rule) 
    rules;
  analyze_ruleset rules query_int

let _ = 
  CmdLine.register_main_pass analyze_smt2;;

let _ =
  CmdLine.register_config
    ("-split-loops",
     Arg.Clear IterDomain.SPSplit.abstract_left,
     " Turn on loop splitting");
  CmdLine.register_config
    ("-no-matrix",
     Arg.Clear IterDomain.SPOne.abstract_left,
     " Turn off matrix recurrences");
  CmdLine.register_config
    ("-prsd",
     Arg.Clear IterDomain.SPPeriodicRational.abstract_left,
     " Use periodic rational spectral decomposition");
  CmdLine.register_config
    ("-prsd-pg",
     Arg.Clear IterDomain.SPPRG.abstract_left,
     " Use periodic rational spectral decomposition w/ Presburger guard");
  CmdLine.register_config
    ("-vas",
     Arg.Clear IterDomain.SpPlusSplitVas_P.abstract_left,
     " Use VAS abstraction");
  CmdLine.register_config
    ("-vass",
     Arg.Unit (fun () -> IterDomain.VasSwitch.abstract_left := false; IterDomain.SpPlusSplitVas_P.abstract_left := false),
     " Use VASS abstraction");
  CmdLine.register_config
    ("-refine",
     Arg.Set cra_refine_flag,
     " Turn on graph refinement");
  CmdLine.register_config
    ("-no-retry",
     Arg.Clear retry_flag,
     " Turn off automatic retry after unknown Z3 result");
  CmdLine.register_config
    ("-summaries",
     Arg.Set print_summaries_flag,
     " Print summaries");
  ();;

