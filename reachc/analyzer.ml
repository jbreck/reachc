module Log = Srk.Log
include Srk.Log.Make(struct let name = "reachc" end)
open Srk

let cra_refine_flag = ref false
let retry_flag = ref true
let print_summaries_flag = ref false
let substitution_optimization = ref true

(* Non-linear CHC depth-bound squeezing options *)
let chora_debug_squeeze = ref false
let chora_squeeze_sb = ref true (* on by default, now *)
let chora_squeeze_conjoin = ref false

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

  let proc_name_string proc_key = 
    if ProcMap.mem proc_key !procedure_names_map then 
      let name = ProcMap.find proc_key !procedure_names_map in
      Format.sprintf "(%d,\"%s\")" proc_key name
    else
      Format.sprintf "(%d,?)" proc_key
end

module ChoraCHC = ChoraCore.MakeChoraCore(ProcModuleCHC)(AuxVarModuleCHC)

let _ = ChoraCHC.chora_dual := true

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


let logf_noendl ?(level=`info) =
  let sf = Format.std_formatter in 
  if (Log.level_leq (!Log.verbosity_level) level ||
      Log.level_leq (!my_verbosity_level) level)
  then Format.fprintf sf
  else Format.ifprintf sf

module VarSet = BatSet.Int

type atom_arg_t = Sctx.t Srk.Syntax.Term.t
type pred_num_t = int

type atom_t = {
    pred_num:pred_num_t;
    args:atom_arg_t list
}

type chc_t = {
   conc:atom_t;
   hyps:atom_t list;
   fmla:Sctx.t Srk.Syntax.Formula.t (* constraint formula *)
} 

module Chc = struct
  (* constrained horn clause *)

  module Atom = struct

    (* atom, i.e., predicate occurrence *)
    type t = atom_t

    let construct (pred_num:pred_num_t) (args:atom_arg_t list) : atom_t = 
      {pred_num=pred_num;args=args}

    let arg_of_symbol sym : atom_arg_t =
      Srk.Syntax.mk_const srk sym

    let print ?(level=`info) srk atom = 
      let n_args = List.length atom.args in 
      logf_noendl ~level "%s(" 
        (Syntax.show_symbol srk (Syntax.symbol_of_int atom.pred_num));
      List.iteri 
        (fun i arg ->
          (*Format.printf "%s" (Syntax.show_symbol srk sym);*)
          (*logf_noendl ~level "%a" (Syntax.pp_symbol srk) sym;*)
          logf_noendl ~level "%a" (Syntax.Term.pp srk) arg;
          if i != n_args - 1 then logf_noendl ~level ",")
        atom.args;
      logf_noendl ~level ")"

  end

  let construct 
        (conc:atom_t) (hyps:atom_t list) 
        (fmla:Sctx.t Srk.Syntax.Formula.t) : chc_t = 
    {conc=conc;hyps=hyps;fmla=fmla}

  let chc_has_hyp chc target_hyp_num = 
    List.fold_left 
      (fun running hyp -> 
         (running || (hyp.pred_num = target_hyp_num)))
      false
      chc.hyps

  let symbol_of_term_opt term = 
    match Syntax.destruct srk term with
    | `App (func, args) when args = [] -> Some func
    | _ -> None

  let symbol_of_term ?(errormsg="fresh_symbols_for_args did not do its job") term = 
    match Syntax.destruct srk term with
    | `App (func, args) when args = [] -> func
    | _ -> failwith errormsg

  (** Replace all skolem constants appearing in the CHC
   *    with fresh skolem constants *)
  let fresh_skolem_all chc =
    let freshen_symbol_to_symbol =
      Memo.memo 
        (fun sym ->
          let name = name_of_symbol srk sym in
          let typ = Syntax.typ_symbol srk sym in
          Syntax.mk_symbol srk ~name typ) in
    let freshen_symbol_to_const sym =
      Syntax.mk_const srk (freshen_symbol_to_symbol sym) in
    let freshen_expr expr =
      Syntax.substitute_const srk freshen_symbol_to_const expr in
    let freshen_atom atom = 
      (* Term version *)
      let new_args = List.map freshen_expr atom.args in 
      Atom.construct atom.pred_num new_args in
    let new_conc_atom = freshen_atom chc.conc in
    let new_hyp_atoms = List.map freshen_atom chc.hyps in
    let new_phi = freshen_expr chc.fmla in
    construct new_conc_atom new_hyp_atoms new_phi

  (* 
  (* This old version generates equations only, never substitutions *)
  (* This function allows you to specify that some arguments within some
       atom should be replaced with a fresh variable even if other arguments
       within the same atom are not being replaced. *)
  let freshen_and_equate_args_finegrained chc plan_conc_atom plan_hyp_atom_list = 
    let chc = fresh_skolem_all chc in
    let old_atoms = chc.conc::chc.hyps in
    let plan_pseudo_atoms = plan_conc_atom::plan_hyp_atom_list in
    let equations = List.concat (List.map2 
      (fun old_atom plan_pseudo_atom ->
          let (plan_pred_num,plan_args) = plan_pseudo_atom in
          assert (old_atom.pred_num = plan_pred_num);
          List.concat (List.map2 
             (fun old_arg plan_arg_option -> 
                 match plan_arg_option with
                 | None -> []
                 | Some new_arg -> [Syntax.mk_eq srk old_arg new_arg])
             old_atom.args
             plan_args))
      old_atoms
      plan_pseudo_atoms) in
    let new_atoms = List.map2
      (fun old_atom plan_pseudo_atom ->
          let (plan_pred_num,plan_args) = plan_pseudo_atom in
          let new_args = List.map2
            (fun old_arg plan_arg_option ->
                match plan_arg_option with
                | None -> old_arg
                | Some new_arg -> new_arg)
            old_atom.args
            plan_args in
          Atom.construct old_atom.pred_num new_args)
      old_atoms
      plan_pseudo_atoms in
    let new_conc = List.hd new_atoms in
    let new_hyps = List.tl new_atoms in
    let new_phi = Syntax.mk_and srk (chc.fmla::equations) in
    construct new_conc new_hyps new_phi
  *) 

  (* This function allows you to specify that some arguments within some
       atom should be replaced with a fresh variable even if other arguments
       within the same atom are not being replaced. *)
  let freshen_and_equate_args_finegrained chc plan_conc_atom plan_hyp_atom_list = 
    let chc = fresh_skolem_all chc in
    let old_atoms = chc.conc::chc.hyps in
    let plan_pseudo_atoms = plan_conc_atom::plan_hyp_atom_list in
    let sub_targets = ref Syntax.Symbol.Set.empty in
    let seen_symbols = ref Syntax.Symbol.Set.empty in
    (if !substitution_optimization then 
    List.iter
      (fun plan_pseudo_atom ->
          let (plan_pred_num,plan_args) = plan_pseudo_atom in
          List.iter
            (fun plan_arg_opt ->
                match plan_arg_opt with
                | None -> ()
                | Some arg ->
                  match symbol_of_term_opt arg with
                  | None -> 
                    let new_symbols = Syntax.symbols arg in
                    seen_symbols := Syntax.Symbol.Set.union 
                      !seen_symbols new_symbols;
                    sub_targets := Syntax.Symbol.Set.diff
                      !sub_targets new_symbols
                  | Some sym -> 
                    if Syntax.Symbol.Set.mem sym !seen_symbols
                    then 
                      sub_targets := 
                        Syntax.Symbol.Set.remove sym !sub_targets
                    else 
                      (sub_targets := 
                         Syntax.Symbol.Set.add sym !sub_targets;
                       seen_symbols :=
                         Syntax.Symbol.Set.add sym !seen_symbols))
            plan_args)
      plan_pseudo_atoms);
    let sub_sources = ref Syntax.Symbol.Set.empty in
    let seen_symbols = ref Syntax.Symbol.Set.empty in
    (if !substitution_optimization then 
    List.iter
      (fun atom ->
          List.iter
            (fun arg ->
                match symbol_of_term_opt arg with
                | None -> 
                  let new_symbols = Syntax.symbols arg in
                  seen_symbols := Syntax.Symbol.Set.union 
                    !seen_symbols new_symbols;
                  sub_sources := Syntax.Symbol.Set.diff
                    !sub_sources new_symbols
                | Some sym -> 
                  if Syntax.Symbol.Set.mem sym !seen_symbols
                  then 
                    sub_sources := 
                      Syntax.Symbol.Set.remove sym !sub_sources
                  else 
                    (sub_sources := 
                      Syntax.Symbol.Set.add sym !sub_sources;
                    seen_symbols :=
                      Syntax.Symbol.Set.add sym !seen_symbols))
            atom.args)
      old_atoms);
    let check_substitution old_arg new_arg =
      match symbol_of_term_opt old_arg with
      | None -> None
      | Some src_sym ->
        if Syntax.Symbol.Set.mem src_sym !sub_sources
        then (match symbol_of_term_opt new_arg with
              | None -> None
              | Some tgt_sym -> 
                if Syntax.Symbol.Set.mem tgt_sym !sub_targets
                then Some (src_sym,new_arg)
                else None)
        else None in
    let substitutions = ref Syntax.Symbol.Map.empty in
    let equations = List.concat (List.map2 
      (fun old_atom plan_pseudo_atom ->
          let (plan_pred_num,plan_args) = plan_pseudo_atom in
          assert (old_atom.pred_num = plan_pred_num);
          List.concat (List.map2 
             (fun old_arg plan_arg_option -> 
                 match plan_arg_option with
                 | None -> [] (* no new equation *)
                 | Some new_arg -> 
                   if !substitution_optimization
                   then match check_substitution old_arg new_arg with
                        | None -> (* create equation *)
                          [Syntax.mk_eq srk old_arg new_arg]
                        | Some (src_sym,tgt_term) ->
                          substitutions := 
                            Syntax.Symbol.Map.add
                              src_sym
                              tgt_term
                              !substitutions;
                          [] (* substitution instead of equation *)
                   else (* create equation *)
                     [Syntax.mk_eq srk old_arg new_arg])
             old_atom.args
             plan_args))
      old_atoms
      plan_pseudo_atoms) in
    let subbed_fmla = 
      if !substitution_optimization
      then Syntax.substitute_map srk !substitutions chc.fmla
      else chc.fmla in
    let new_atoms = List.map2
      (fun old_atom plan_pseudo_atom ->
          let (plan_pred_num,plan_args) = plan_pseudo_atom in
          let new_args = List.map2
            (fun old_arg plan_arg_option ->
                match plan_arg_option with
                | None -> old_arg
                | Some new_arg -> new_arg)
            old_atom.args
            plan_args in
          Atom.construct old_atom.pred_num new_args)
      old_atoms
      plan_pseudo_atoms in
    let new_conc = List.hd new_atoms in
    let new_hyps = List.tl new_atoms in
    let new_phi = Syntax.mk_and srk (subbed_fmla::equations) in
    construct new_conc new_hyps new_phi


  (* Coarse-grained version *)
  let freshen_and_equate_args chc plan_conc_atom plan_hyp_atom_list =
    let somes x = List.map (fun y -> Some y) x in
    let nones x = List.map (fun y -> None) x in
    let fg_conc_atom =
      match plan_conc_atom with
      | None -> (chc.conc.pred_num, nones chc.conc.args)
      | Some atom -> (chc.conc.pred_num, somes atom.args) in
    let fg_hyp_atom_list = 
      List.map2
        (fun plan_hyp_atom hyp ->
            match plan_hyp_atom with
            | None -> (hyp.pred_num, nones hyp.args)
            | Some atom -> (hyp.pred_num, somes atom.args))
        plan_hyp_atom_list
        chc.hyps in
    freshen_and_equate_args_finegrained chc fg_conc_atom fg_hyp_atom_list

  let freshen_and_equate_args_directly chc plan_conc_atom plan_hyp_atom_list =
    (* Old version that doesn't boil it down to a call to the fine-grained *)
    let chc = fresh_skolem_all chc in
    let old_atoms = chc.conc::chc.hyps in
    let new_atoms = plan_conc_atom::plan_hyp_atom_list in
    let equations = List.concat (List.map2 
      (fun old_atom new_atom_option ->
          match new_atom_option with
          | None -> []
          | Some new_atom ->
             begin
             assert (old_atom.pred_num = new_atom.pred_num);
             List.map2 
                (fun old_arg new_arg -> Syntax.mk_eq srk old_arg new_arg)
                old_atom.args
                new_atom.args
             end)
      old_atoms
      new_atoms) in
    let new_conc = match plan_conc_atom with
                   | None -> chc.conc
                   | Some new_conc_atom -> new_conc_atom in
    let new_hyps = 
        List.map2 (fun old_atom plan_hyp_atom ->
            match plan_hyp_atom with
            | None -> old_atom
            | Some new_hyp_atom -> new_hyp_atom)
        chc.hyps
        plan_hyp_atom_list in 
    let new_phi = Syntax.mk_and srk (chc.fmla::equations) in
    construct new_conc new_hyps new_phi
   
  (* Replace *every* atom-arg with a fresh symbol *)
  let fresh_symbols_for_args chc =
    let new_sym atom arg_num = 
        let name = 
          (name_of_symbol srk (Syntax.symbol_of_int atom.pred_num)) 
          ^ "_arg" ^ (string_of_int arg_num) in
        Syntax.mk_symbol srk ~name `TyInt in
    let atom_with_new_syms atom = 
        let new_args = List.mapi
          (fun arg_num arg ->
              let sym = new_sym atom arg_num in
              Syntax.mk_const srk sym)
          atom.args in
        Atom.construct atom.pred_num new_args in
    let plan_conc = Some (atom_with_new_syms chc.conc) in
    let plan_hyps = List.map
      (fun hyp -> Some (atom_with_new_syms hyp))
      chc.hyps in
    freshen_and_equate_args chc plan_conc plan_hyps

  let fresh_symbols_for_term_args chc =
    let new_sym atom arg_num = 
        let arg = List.nth atom.args arg_num in 
        match Syntax.destruct srk arg with
        | `App (func, f_args) when f_args = [] -> func
        | _ -> (* predicate argument term that isn't a var *)
          let name = 
            (name_of_symbol srk (Syntax.symbol_of_int atom.pred_num)) 
            ^ "_arg" ^ (string_of_int arg_num) in
          Syntax.mk_symbol srk ~name `TyInt in
    let atom_with_new_syms atom = 
        let new_args = List.mapi
          (fun arg_num arg ->
              let sym = new_sym atom arg_num in
              Syntax.mk_const srk sym)
          atom.args in
        Atom.construct atom.pred_num new_args in
    let plan_conc = Some (atom_with_new_syms chc.conc) in
    let plan_hyps = List.map
      (fun hyp -> Some (atom_with_new_syms hyp))
      chc.hyps in
    freshen_and_equate_args chc plan_conc plan_hyps

  (* This function makes all implicit constraints explicit. 
    
     An example of a CHC having implicit constraints is this one:
    
       P(x,y,z+1) :- Q(x,w,0,z*2) /\ phi
       
     which implicitly constrains the first arguments of P and Q to be
     equal, and implicitly constrains the last argument of P, minus one,
     to be half the last argument to Q, and implicitly constrains the
     second-to-last argument to Q to be zero, all without involving any
     explicit constrains in phi. *)
  let fresh_symbols_to_make_constraints_explicit chc =
    let atoms = chc.conc::chc.hyps in
    let seen_symbols = ref Syntax.Symbol.Set.empty in
    let plan_atoms = List.map
      (fun atom ->
          (atom.pred_num,
           List.map
             (fun arg ->
                 let new_symbols = Syntax.symbols arg in
                 let plan_arg = 
                   (* If we set this to None, we'll replace arg with a 
                        fresh constant; if we set it to Some t, we'll
                        replace arg with t.  *)
                   if Syntax.Symbol.Set.disjoint new_symbols !seen_symbols
                   then match symbol_of_term_opt arg with (*arg is unseen *)
                        | None -> None (*arg is a non-const term*)
                        | Some sym -> Some arg (*arg is an unseen const*)
                   else (* arg has been seen already *)
                      None in
                 seen_symbols := 
                     Syntax.Symbol.Set.union !seen_symbols new_symbols;
                 plan_arg)
             atom.args))
      atoms in
    let plan_conc_atom = List.hd plan_atoms in
    let plan_hyp_atoms = List.tl plan_atoms in
    freshen_and_equate_args_finegrained chc plan_conc_atom plan_hyp_atoms

  let subst_all outer_chc inner_chc = 
    let outer_chc = fresh_skolem_all outer_chc in
    let (outer_hyps_matching, outer_hyps_non_matching) = 
      List.partition
        (fun atom -> (atom.pred_num = inner_chc.conc.pred_num))
        outer_chc.hyps
      in
    (if List.length outer_hyps_matching = 0 
    then failwith "Mismatched subst_all call"
    else ());
    let (new_hyps, new_phis) = 
      List.fold_left
        (fun (hyps, phis) outer_hyp -> 
          assert (outer_hyp.pred_num = inner_chc.conc.pred_num);
          let plan_conc_atom = Some outer_hyp in
          let plan_hyp_atom_list = List.map (fun hyp -> None) inner_chc.hyps in
          let new_inner_chc = 
              freshen_and_equate_args 
                inner_chc plan_conc_atom plan_hyp_atom_list in
          (new_inner_chc.hyps @ hyps, new_inner_chc.fmla::phis))
        ([],[])
        outer_hyps_matching
      in
    let phi = Syntax.mk_and srk (outer_chc.fmla::new_phis) in
    let hyps = outer_hyps_non_matching @ new_hyps in
    construct outer_chc.conc hyps phi

  let disjoin chcs =
    match chcs with
    | [] -> failwith "Empty chc list in Chc.disjoin"
    | [chc1] -> chc1
    | chc1::old_chcs ->
      let chc1 = fresh_skolem_all chc1 in
      let chc1 = fresh_symbols_for_args chc1 in
      let new_phis = 
        List.map
          (fun old_chc ->
             let plan_conc_atom = Some chc1.conc in
             let plan_hyp_atom_list = List.map (fun hyp -> Some hyp) chc1.hyps in
             let new_chc = 
               freshen_and_equate_args
                 old_chc plan_conc_atom plan_hyp_atom_list in
             new_chc.fmla) 
          old_chcs in
      let new_phi = Syntax.mk_or srk (chc1.fmla::new_phis) in
      construct chc1.conc chc1.hyps new_phi

  let subst_equating_globally chc subst_map = 
    let sub_policy atom =
        if IntMap.mem atom.pred_num subst_map 
        then Some (IntMap.find atom.pred_num subst_map)
        else None in
    freshen_and_equate_args
      chc
      (sub_policy chc.conc)
      (List.map sub_policy chc.hyps)

  let print ?(level=`info) srk chc = 
    logf_noendl ~level "{ @[";
    List.iter 
      (fun pred -> Atom.print srk pred; logf_noendl ~level ";@ ")
      chc.hyps;    
    logf_noendl ~level "%a@ -> " (Syntax.Formula.pp srk) chc.fmla;
    Atom.print ~level srk chc.conc;
    logf_noendl ~level "@] }@."
 
  let print_as_wedge ?(level=`info) srk chc = 
    let chc = fresh_symbols_for_term_args chc in 
    logf_noendl ~level "{ @[";
    List.iter 
      (fun atom -> Atom.print srk atom; logf_noendl ~level ";@ ")
      chc.hyps;
    let all_preds = chc.conc::chc.hyps in 
    let all_pred_args =
      List.concat
        (List.map 
          (fun atom -> List.map symbol_of_term atom.args) all_preds) in
    let exists = (fun sym -> List.mem sym all_pred_args) in 
    let wedge = Wedge.abstract ~exists srk chc.fmla in
    logf_noendl ~level "%a@ -> " Wedge.pp wedge;
    Atom.print ~level srk chc.conc;
    logf_noendl ~level "@] }@."

  let to_transition chc = 
    let chc = fresh_symbols_for_args chc in
    assert (List.length chc.hyps = 1);
    let hyp_atom = List.hd chc.hyps in
    assert (hyp_atom.pred_num = chc.conc.pred_num);
    Var.reset_tables;
    List.iter (fun arg -> Var.register_var (symbol_of_term arg)) hyp_atom.args;
    (* conc_args and hyp_args are lists of symbols *)
    let transform = 
      List.map2 
        (fun pre post -> 
            (let pre_sym = symbol_of_term pre in 
             (* pre-state as variable *)
             (match Var.of_symbol pre_sym with
             | Some v -> v
             | _ -> failwith "Unregistered variable in to_transition"),
            (* post-state is term *)
            post
            (* if post-state were symbol: *) (*Syntax.mk_const srk post)*)))
        hyp_atom.args
        chc.conc.args
      in
    (chc, K.construct chc.fmla transform)

  (* Make a chc that corresponds to the identity transition, 
     on the model of the given model_chc.
     The returned chc will have the same atoms as model_chc.  *)
  let identity_chc model_chc =
    assert (List.length model_chc.hyps = 1);
    let hyp_pred = List.hd model_chc.hyps in
    assert (hyp_pred.pred_num = model_chc.conc.pred_num);
    let eqs = List.fold_left2
      (fun eqs hyp_arg conc_arg ->
          let eq = Syntax.mk_eq srk hyp_arg conc_arg in eq::eqs)
      [] 
      hyp_pred.args
      model_chc.conc.args
    in
    let phi = Syntax.mk_and srk eqs in
    construct model_chc.conc model_chc.hyps phi
  
  let of_transition tr model_chc : chc_t =
    if K.is_one tr then identity_chc model_chc else
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
    assert (List.length model_chc.hyps = 1);
    let hyp_pred = List.hd model_chc.hyps in
    assert (hyp_pred.pred_num = model_chc.conc.pred_num);
    let new_args = 
      List.map 
        (fun hyp_arg -> 
           let hyp_var = symbol_of_term hyp_arg in
           let rec go pairs = 
             match pairs with
             | (pre_sym, post_sym)::rest -> 
                     if hyp_var = pre_sym 
                     then Syntax.mk_const srk post_sym 
                     else go rest
             | [] -> logf ~level:`fatal "  ERROR: missing symbol %a" (Syntax.pp_symbol srk) hyp_var;
                     failwith "Could not find symbol in of_transition"
           in go tr_symbols)
        hyp_pred.args in
    let new_conc_pred = Atom.construct model_chc.conc.pred_num new_args in 
    (construct new_conc_pred model_chc.hyps body)

end

let build_chc_records srk1 srk2 phi query_pred =
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
  let chc_record_of_rule (hyp,conc,vars) = 
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
            let argterms = List.map (fun sym -> Syntax.mk_const srk2 sym) argsymbols in
            let atom = Chc.Atom.construct fnumber (List.rev argterms) in
            mut_predicates := atom :: !mut_predicates;
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
    let conc_atom = match conc_preds with
      | [conc_atom] -> conc_atom
      | [] -> 
        if (not (is_syntactic_false srk2 conc_sub))
        then failwith "Unrecognized rule format (Non-false non-predicate conclusion)"
        else Chc.Atom.construct query_pred []
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
    (Chc.construct conc_atom hyp_preds phi)
    (* *)
  in
  List.map chc_record_of_rule rules

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

(* ******************** Linear CHC Solving ************************** *)

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

(* Substitute summaries of lower SCCs into this predicate's rules *)
let subst_summaries chcs summaries =
  (* FIXME use declared variable names from somewhere? *)
  List.map
    (fun chc ->
     List.fold_left 
       (fun rule_inprog hyp -> 
          if BatMap.Int.mem hyp.pred_num summaries then
            let pred_summary = BatMap.Int.find hyp.pred_num summaries in
            (if Chc.chc_has_hyp rule_inprog hyp.pred_num then
              Chc.subst_all rule_inprog pred_summary
            else rule_inprog)
          else 
            rule_inprog)
       chc
       chc.hyps)
    chcs

let build_chc_list_matrix scc chc_map summaries const_id = 
  let chc_list_matrix = new_empty_matrix () in
  logf ~level:`info "  Finding rules";
  List.iter
    (fun p ->
      let p_rules = subst_summaries (BatMap.Int.find p chc_map) !summaries in
      List.iter 
        (fun rule ->
           (* fresh_symbols_to_make_constrains_explicit may be required
                for soundness here. *)
           let rule = Chc.fresh_symbols_to_make_constraints_explicit rule in
           match rule.hyps with
           | [hyp] ->
             modify_def_matrix_element 
                chc_list_matrix p hyp.pred_num [] (fun rs -> rule::rs)
           | [] ->
             modify_def_matrix_element 
                chc_list_matrix p const_id [] (fun rs -> rule::rs)
           | _ -> failwith "Non-superlinear SCCs cannot be used by this sub-system")
        p_rules) 
    scc;
  chc_list_matrix

(* First build a matrix whose entries are lists of chcs. 
   Then, disjoin the elements of each such list to produce
     a matrix whose entries are single chcs. *)
let build_chc_matrix scc chc_map summaries const_id = 
  let chc_list_matrix = 
    build_chc_list_matrix scc chc_map summaries const_id in
  let chc_matrix = new_empty_matrix () in
  logf ~level:`info "  Disjoining CHCs";
  List.iter
    (fun p ->
      matrix_row_iteri
        chc_list_matrix
        p
        (fun _ colid rules ->
          (*Format.printf "    rowid:%d colid:%d@." p colid;
          List.iter
            (fun r ->
            Format.printf "    - A rule to disjoin: ";
            Chc.print srk r;
            Format.printf "@.")
          rules;*)
          let combined_rule = Chc.disjoin rules in
          assign_matrix_element chc_matrix p colid combined_rule)
    ) scc;
  chc_matrix  

let eliminate_predicate chc_matrix const_id p =
  logf ~level:`info "   -Eliminating %a" 
    (Syntax.pp_symbol srk) 
    (Syntax.symbol_of_int p);
  (* First, eliminate p's direct recursion if it exists *)
  begin
    if has_matrix_element chc_matrix p p then
      (* Obtain the direct-recursion entry from the matrix *)
      let combined_rec = get_matrix_element chc_matrix p p in
      logf_noendl ~level:`info "    Combined recursive CHC:@.    ";
      Chc.print ~level:`info srk combined_rec;
      (* Star it *)
      let (freshened_chc, tr) = Chc.to_transition combined_rec in
      logf_noendl ~level:`info "    As transition:@.    %a@." K.pp tr;
      let tr_star = K.star tr in 
      logf_noendl ~level:`info "    Starred:@.    %a@." K.pp tr_star;
      (*let tr_star_rule = Chc.of_transition tr_star combined_rec in*)
      let tr_star_rule = Chc.of_transition tr_star freshened_chc in
      logf_noendl ~level:`info "    Starred as CHC:@.    ";
      Chc.print ~level:`info srk tr_star_rule;
      (* Use substitution to apply the starred rule onto 
         every other matrix entry corresponding to a rule 
         that has conclusion p *)
      matrix_row_iteri chc_matrix p
        (fun _ hyp nonrec_rule ->
          (* *)
          let sub_rule = Chc.subst_all tr_star_rule nonrec_rule in
          assign_matrix_element chc_matrix p hyp sub_rule);
      remove_matrix_element chc_matrix p p
      (* At this point, p's rules are all non-recursive *)
  end;
  (* Now, remove "uses" of p in other predicates' rules *)
  matrix_col_iteri chc_matrix p 
    (fun q _ qrule ->
      (* qrule has hypothesis p and conclusion q *)
      matrix_row_iteri chc_matrix p
        (fun _ r prule ->
          assert (r != p);
          (* prule has hypothesis r and conclusion p *)
          (* Now, we substitute prule into qrule, 
             creating a new rule with hypothesis r and conclusion q, 
             thus eliminating a use of p. *)
          let sub_rule = Chc.subst_all qrule prule in
          match get_matrix_element_opt chc_matrix q r with
          | None ->
            assign_matrix_element chc_matrix q r sub_rule
          | Some prev_rule ->
            let combined_rule = 
              Chc.disjoin [prev_rule; sub_rule] in
            assign_matrix_element chc_matrix q r combined_rule));
  (* Now, set all the entries in column p to zero *)
  matrix_col_iteri chc_matrix p 
    (fun q _ _ -> remove_matrix_element chc_matrix q p)
  (* At this point, p has been eliminated from the system *)

let summarize_linear_scc scc chc_map summaries = 
  logf ~level:`info "SCC: linear@.";
  let const_id = (* (List.hd (List.sort compare scc)) *) -1 in
  assert (not (List.mem const_id scc));
  let chc_matrix = build_chc_matrix scc chc_map summaries const_id in
  (* Now, eliminate predicates from this SCC one at a time*)
  logf ~level:`info "  Eliminating predicates";
  List.iter (eliminate_predicate chc_matrix const_id) scc;
  (* The remaining matrix entries are summaries; 
     they have no hypothesis predicate occurrences *)
  List.iter
    (fun p ->
      match get_matrix_element_opt chc_matrix p const_id with
      | None -> failwith "Missing const_id entry in chc_matrix"
      | Some rule -> summaries := (BatMap.Int.add p rule !summaries)) 
    scc

(* ****************** Non-linear CHC Solving ************************ *)

let make_chc_projection_and_symbols chc = 
  let atoms = chc.conc::chc.hyps in
  let sym_list = List.fold_left
    (fun running_syms atom ->
       let syms = List.map (fun arg -> Chc.symbol_of_term arg) atom.args in
       List.append syms running_syms)
    []
    atoms in
  let projection sym = List.mem sym sym_list in
  (projection, sym_list)

(* Create a new CHC representing the hypothetical summary of some procedure,
     given the info_structure that contains the formula (not yet a CHC) for
     the hypothetical summary and the names of the bounding-function 
     symbols (B_in1, B_in2, ...), and the CHC of the fact (i.e., base case) 
     from which that hypothetical sumary was computed. 
   Accomplishing this is simple.
   We are given the constraint formula, info_structure.call_abstraction_fmla,
     and we already have a list of all of the hypothesis and conclusion
     predicate occurrences in fact_atom, and we only need
     to add one more: we need to create a new hypothesis predicate
     occurrence that holds onto all the bounding symbols.  
   In this function, we create that predicate, create an occurrence of it,
     attach it to the list of hypothesis predicate occurrences, and combine
     it with the constraint formula from info_structure to obtain the desired
     CHC. *)
let make_hypothetical_summary_chc info_structure fact_atom : (chc_t * atom_t) =
    let bounding_symbol_list = List.map
      (fun (sym, corresponding_term) -> Srk.Syntax.mk_const srk sym)
      info_structure.ChoraCHC.bound_pairs in 
    let n_bounding_symbols = List.length bounding_symbol_list in
    let new_pred = make_aux_predicate n_bounding_symbols "AuxGlobalPredicate" in
    let new_atom = Chc.Atom.construct
      (Srk.Syntax.int_of_symbol new_pred) bounding_symbol_list in
    (Chc.construct fact_atom [new_atom] info_structure.call_abstraction_fmla,
     new_atom)

let make_final_summary_chc summary_fmla fact_atom : chc_t =
    Chc.construct fact_atom [] summary_fmla

(* This function assumes each atom arg is one symbol, which is an invariant
     that holds at some points in this code but not at others *)
let atom_syms atom = List.map Chc.symbol_of_term atom.args

let depth_bound_formula_to_symbolic_bounds phi sym relevant_symbols = 
  let level = if !chora_debug_squeeze then `always else `info in
  logf ~level " squeezing depth-bound formula to symbolic bounds formula...";
  let exists x =
    x = sym || (List.mem x relevant_symbols)
  in
  let symbol_term = Syntax.mk_const srk sym in
  let debug_list part = 
     logf ~level "      -- inner bound list [";
     List.iter (fun elt -> logf ~level "       %a" (Syntax.Term.pp srk) elt) part;
     logf ~level "      -- inner bound list ]"
  in
  let debug_list_list parts = 
     logf ~level "   -- outer bound list [";
     List.iter (fun part -> debug_list part) parts;
     logf ~level "   -- outer bound list ]"
  in
  let safer_disjoin parts = 
    match parts with 
    | [] -> Syntax.mk_true srk
    | _ -> Syntax.mk_or srk parts
  in
  let to_formula parts = 
    let (lower,upper) = parts in
    logf ~level " lower bounds: ";
    debug_list_list lower;
    logf ~level " upper bounds: ";
    debug_list_list upper;
    let lower_bounds =
      lower
      |> List.map (fun case ->
          case |> List.map (fun lower_bound -> Syntax.mk_leq srk lower_bound symbol_term)
          |> Syntax.mk_and srk)
      |> safer_disjoin
    in
    let upper_bounds =
      upper
      |> List.map (fun case ->
          case |> List.map (fun upper_bound -> Syntax.mk_leq srk symbol_term upper_bound)
          |> Syntax.mk_and srk)
      |> safer_disjoin
    in
    Syntax.mk_and srk [lower_bounds; upper_bounds]
  in
  logf ~level " sbf-squeeze input: %a " (Syntax.Formula.pp srk) phi;
  let formula_parts_wrapped = 
      Wedge.symbolic_bounds_formula_list ~exists srk phi sym in
  match formula_parts_wrapped with
  | `Sat (formula_parts) -> 
      let formula = to_formula formula_parts in 
      logf ~level " sbf-squeeze output: %a " (Syntax.Formula.pp srk) formula;
      formula
  | `Unsat ->
      logf ~level:`always " WARNING: sbf-squeeze got unsatisfiable depth formula!";
      Syntax.mk_true srk

let incorporate_depth_bound_squeezing 
      depth_bound_formula p post_height_sym fact_map =
  let post_height_gt_zero = 
    Syntax.mk_lt srk 
      (Syntax.mk_zero srk)
      (Syntax.mk_const srk post_height_sym) in
  let post_height_eq_zero = 
    Syntax.mk_eq srk 
      (Syntax.mk_zero srk)
      (Syntax.mk_const srk post_height_sym) in
  let p_fact = ProcMap.find p fact_map in
  let to_be_squeezed = 
    (* sophisticated version: assume H' >= 0 inside squeezed version *) 
    Syntax.mk_and srk [post_height_gt_zero; depth_bound_formula] in
  let relevant_symbols = atom_syms p_fact.conc in
  let symbolic_bounds_depth_bound_formula = 
    if !chora_squeeze_sb || !chora_debug_squeeze
    then depth_bound_formula_to_symbolic_bounds 
           to_be_squeezed post_height_sym relevant_symbols
    else Syntax.mk_true srk in
  let incorporate_dbf fmla = 
      begin
        let case_split = 
            Syntax.mk_or srk 
              [(Syntax.mk_and srk [post_height_eq_zero; p_fact.fmla]);
               (Syntax.mk_and srk [post_height_gt_zero; fmla])] in
        if !chora_squeeze_conjoin
        then Syntax.mk_and srk [depth_bound_formula; case_split]
        else case_split
      end
    in
  let final_depth_bound_formula = 
    if !chora_squeeze_sb
    then (incorporate_dbf symbolic_bounds_depth_bound_formula)
    else depth_bound_formula in 
  let level = if !chora_debug_squeeze then `always else `info in
  logf ~level " sbf-squeeze output: %a " (Syntax.Formula.pp srk) final_depth_bound_formula;
  final_depth_bound_formula

let make_depth_bound_summary scc subbed_chcs_map height_sym fact_atom_map fact_map = 
  logf ~level:`info "  Beginning depth-bound analysis"; 
  let (aug_scc, pred_map) = List.fold_left 
    (fun (aug_scc, pred_map) p ->
       let name = "DepthAugmented_" ^ (name_of_symbol srk (Syntax.symbol_of_int p)) in
       let int_arity =
           1 + (List.length (List.hd (ProcMap.find p subbed_chcs_map)).conc.args) in 
       let aug_pred = make_aux_predicate int_arity name in
       ((Syntax.int_of_symbol aug_pred)::aug_scc, IntMap.add p aug_pred pred_map))
    ([],IntMap.empty) 
    scc in
  let augment_atom atom height_term =
    let aug_pred = IntMap.find atom.pred_num pred_map in
    let aug_args = height_term::atom.args in
    Chc.Atom.construct (Syntax.int_of_symbol aug_pred) aug_args in
  let height_plus_zero = Syntax.mk_const srk height_sym in
  let zero = Syntax.mk_real srk QQ.zero in
  let one = Syntax.mk_real srk QQ.one in
  let height_plus_one = Syntax.mk_add srk [height_plus_zero; one] in
  let height_equals_zero = Syntax.mk_eq srk height_plus_zero zero in
  let aug_chc_map = List.fold_left
    (fun aug_chc_map orig_p ->
        let aug_pred = IntMap.find orig_p pred_map in
        let orig_chcs = ProcMap.find orig_p subbed_chcs_map in 
        let (orig_facts,orig_rules) = 
          List.partition
            (fun chc -> (List.length chc.hyps) = 0)
            orig_chcs
          in
        (* For each original fact: 
              Pi(...) = phi
           We get the following augmented fact:
              DebugAugmented_Pi(H,...) = phi /\ H = 0           *)
        let aug_facts = 
          List.map
            (fun orig_fact ->
                let aug_conc = augment_atom orig_fact.conc height_plus_zero in
                let aug_fmla = 
                    Syntax.mk_and srk [orig_fact.fmla; height_equals_zero] in
                Chc.construct aug_conc [] aug_fmla) 
            orig_facts in
        (* For each original rule: 
              Pi(...) = psi /\ Pj1(...) /\ Pj2(...) /\ Pjk(...)
           We get the following rules (plural):
              DebugAugmented_Pi(H+1,...) = DebugAugmented_Pj1(H,...) /\ psi 
              DebugAugmented_Pi(H+1,...) = DebugAugmented_Pj2(H,...) /\ psi 
                                        ...
              DebugAugmented_Pi(H+1,...) = DebugAugmented_Pjk(H,...) /\ psi 
           Note that we are dropping all but one hypothesis atom to obtain
             each of the augmented rules; this causes the variables that were
             the arguments of the dropped atoms to become mere Skolem 
             constants in the augmented Horn-clause SCC.  This is a very
             imprecise abstraction; it's equivalent to Chora's use of the
             "top" element as an abstraction of "skipped over" calls in 
             Chora's depth-bound analysis. *)
        let aug_rules = 
          List.concat 
            (List.map
               (fun orig_rule ->
                  List.map
                    (fun hyp ->
                        let aug_conc = 
                            augment_atom orig_rule.conc height_plus_one in
                        let new_hyp =
                            augment_atom hyp height_plus_zero in
                        Chc.construct aug_conc [new_hyp] orig_rule.fmla) 
                    orig_rule.hyps)
               orig_rules) in
        let aug_chcs = aug_facts @ aug_rules in 
        IntMap.add (Syntax.int_of_symbol aug_pred) aug_chcs aug_chc_map)
    IntMap.empty
    scc in 
  let aug_summaries = ref IntMap.empty in
  (* We re-use our linear-SCC-solving code for depth-bound analysis *)
  summarize_linear_scc aug_scc aug_chc_map aug_summaries;
  let depth_summary_map = List.fold_left
    (fun depth_summary_map orig_p ->
        let fact_atom = ProcMap.find orig_p fact_atom_map in
        let aug_atom = augment_atom fact_atom height_plus_zero in
        let aug_summary = IntMap.find aug_atom.pred_num !aug_summaries in
        let p_subst_pred_num_map = 
            IntMap.singleton aug_atom.pred_num aug_atom in
        let vocab_fixup_chc = 
            Chc.subst_equating_globally aug_summary p_subst_pred_num_map in
        logf ~level:`info "  dbf%s:" (proc_name_string orig_p);
        Chc.print ~level:`info srk vocab_fixup_chc;
        (* At this point, vocab_fixup_chc has a formula that encodes the
             depth-bounding information.  Now we "squeeze" that formula
             to (heuristically) obtain a more "useful" form of it. *)
        let final_depth_bound_fmla = 
            incorporate_depth_bound_squeezing 
              vocab_fixup_chc.fmla orig_p height_sym fact_map in
        (* What we're returning here, for each p, is the formula of the 
           summary of the augmented predicate DebugAugmented_Pp, with the
           vocabularies fixed up such that the height symbol is height_sym
           and the arguments to the conclusion atom of vocab_fixup_chc
           match the conclusion atom of the entry in fact_atom_map for p.
           Basically, that is a formula that bounds the height of the
           recursion tree in terms of the arguments to Pp. *)
        ProcMap.add orig_p final_depth_bound_fmla depth_summary_map)
    ProcMap.empty
    scc in
  logf ~level:`info "  Finished depth-bound analysis"; 
  depth_summary_map

let summarize_nonlinear_scc scc chc_map summaries = 
  logf ~level:`info "SCC: non-super-linear@.";
  let subbed_chcs_map = 
    List.fold_left
      (fun subbed_chcs_map p ->
        let p_chcs = BatMap.Int.find p chc_map in
        (* fresh_symbols_to_make_constrains_explicit may be required
             for soundness here. *)
        let p_chcs = List.map
          (fun chc -> Chc.fresh_symbols_to_make_constraints_explicit chc)
          p_chcs in
        let p_chcs = subst_summaries p_chcs !summaries in
        ProcMap.add p p_chcs subbed_chcs_map)
      ProcMap.empty
      scc in 
  let subst_pred_num_map = ref IntMap.empty in
  let (bounds_map, hyp_sum_map, fact_atom_map, fact_map) = 
    List.fold_left
      (fun (bounds_map, hyp_sum_map, fact_atom_map, fact_map) p ->
        let p_chcs = ProcMap.find p subbed_chcs_map in
        let p_facts = List.filter (fun chc -> List.length chc.hyps == 0) p_chcs in
        let p_fact = Chc.disjoin p_facts in
        let p_fact = Chc.fresh_symbols_for_args p_fact in
        (* now p_fact has a set of fresh symbols in its conclusion atom *)
        let (projection, pre_symbols) = make_chc_projection_and_symbols p_fact in
        (assert ((List.length p_fact.hyps) = 0));
        (* Call into ChoraCore to generalize the fact into a hypothetical summary formula,
             along with a list of bounding symbols, stored together in bounds_structure *)
        let bounds_structure = 
          ChoraCHC.make_hypothetical_summary p_fact.fmla projection in
        (* Concept: make the hypothetical summary formula into a hypothetical summary
             CHC by attaching a new ``auxiliary global variable'' predicate for 
             the predicate's bounding functions. *)
        let (hyp_sum_chc, aux_global_atom) = 
            make_hypothetical_summary_chc bounds_structure p_fact.conc in
        subst_pred_num_map := 
            IntMap.add aux_global_atom.pred_num aux_global_atom !subst_pred_num_map;
        (ProcMap.add p bounds_structure bounds_map, 
         ProcMap.add p hyp_sum_chc hyp_sum_map,
         ProcMap.add p p_fact.conc fact_atom_map,
         ProcMap.add p p_fact fact_map))
      (ProcMap.empty, ProcMap.empty, ProcMap.empty, ProcMap.empty)
      scc in
  let rec_fmla_map = 
    List.fold_left
      (fun rec_fmla_map p ->
        let p_chcs = ProcMap.find p subbed_chcs_map in
        let p_rules = 
          List.filter
            (fun chc -> List.length chc.hyps != 0)
            p_chcs in
        let p_subbed_rules = subst_summaries p_rules hyp_sum_map in
        let p_rec_rule = Chc.disjoin p_subbed_rules in
        let p_fact_atom = ProcMap.find p fact_atom_map in
        let p_subst_pred_num_map = 
            IntMap.add p_fact_atom.pred_num p_fact_atom !subst_pred_num_map in
        let p_vocab_fixup = Chc.subst_equating_globally p_rec_rule p_subst_pred_num_map in
        ProcMap.add p p_vocab_fixup.fmla rec_fmla_map)
      ProcMap.empty
      scc in
  let scc_fact_atom_syms = 
    List.concat
      (List.map atom_syms (BatList.of_enum (ProcMap.values fact_atom_map))) in 
  let simple_height = make_aux_variable (if !ChoraCHC.chora_dual then "RB" else "H") in 
  let (height_model, excepting) = 
    if !ChoraCHC.chora_dual then 
      let rm = make_aux_variable "RM" in 
      let mb = make_aux_variable "MB" in 
      (* When we perform dual-height analysis, we make two copies each (one
         "lower", one "upper") of most of the symbols in our vocabulary, but
         there are some exceptions, i.e., symbols that should not be copied.
         The variable excepting holds the list of such symbols *)
      let excepting = 
        List.fold_left 
          (* Probably want post_symbol applied to the height ones and
               don't need post_symbol applied to the non-height ones *)
          (fun excepting sym -> 
              let excepting = Srk.Syntax.Symbol.Set.add sym excepting in
              Srk.Syntax.Symbol.Set.add (post_symbol sym) excepting)
          Srk.Syntax.Symbol.Set.empty
          (simple_height.symbol::rm.symbol::mb.symbol::scc_fact_atom_syms) in 
      (ChoraCHC.RB_RM_MB (simple_height (* that is, rb *), rm, mb), excepting)
    else 
      (ChoraCHC.RB (simple_height), Srk.Syntax.Symbol.Set.empty) in 
  let depth_bound_fmla_map = (* Non-trivial depth-bound summaries *) 
      make_depth_bound_summary 
        scc 
        subbed_chcs_map 
        (post_symbol simple_height.symbol) 
        fact_atom_map 
        fact_map in
  (* When changing this to use dual-height, I need to compute "excepting" *)
  let summary_fmla_list = 
    ChoraCHC.make_height_based_summaries
      rec_fmla_map bounds_map depth_bound_fmla_map scc height_model excepting in
  let summary_chc_list = List.map
    (fun (p,fmla) -> 
        let p_fact_atom = ProcMap.find p fact_atom_map in
        (p, make_final_summary_chc fmla p_fact_atom))
    summary_fmla_list in 
  List.iter
    (fun (p,chc) -> summaries := (BatMap.Int.add p chc !summaries)) 
    summary_chc_list

(* ********************* Analyzer ************************* *)

let detect_linear_scc scc chc_map summaries = 
  List.fold_left (* for p in scc *)
    (fun is_linear p -> is_linear &&
      begin
        let p_chcs = BatMap.Int.find p chc_map in
        List.fold_left (* for p_chc in p_chcs *)
          (fun is_linear_chc chc -> is_linear_chc &&
             begin
               let n_scc_hyps_this_chc = 
               List.fold_left (* for hyp in hyps *)
                 (fun n_scc_hyps hyp ->
                   if BatMap.Int.mem hyp.pred_num !summaries 
                   then n_scc_hyps
                   else (n_scc_hyps + 1))
                 0
                 chc.hyps in
               (n_scc_hyps_this_chc <= 1)
             end)
          true
          p_chcs
      end)
    true
    scc

let analyze_query_predicate chc_matrix query_int const_id = 
  match get_matrix_element_opt chc_matrix query_int const_id with
  | None -> failwith "Missing final CHC"
  | Some final_chc -> 
    logf_noendl ~level:`info "Final CHC: @.  ";
    Chc.print ~level:`info srk final_chc;
    logf ~level:`info "";
    begin
      match Wedge.is_sat srk final_chc.fmla with
      | `Sat -> logf ~level:`always "RESULT: UNKNOWN (final constraint is sat)"
      | `Unsat -> logf ~level:`always "RESULT: SAT (final constraint is unsat)"
      | `Unknown -> 
        if not !retry_flag then 
          logf ~level:`always "RESULT: UNKNOWN (final constraint unknown)"
        else
        begin
          logf ~level:`info "Preliminary: unknown (final constraint unknown)";
          logf ~level:`info "Retrying...";
          let wedge = Wedge.abstract srk final_chc.fmla in
          if Wedge.is_bottom wedge
          then logf ~level:`always "RESULT: SAT (final constraint is unsat)"
          else logf ~level:`always "RESULT: UNKNOWN (final constraint unknown)"
        end
    end

let handle_query_predicate scc chc_map summaries query_int = 
  logf ~level:`info "Analysis of query predicate:@.";
  let const_id = -1 in
  let chc_matrix = build_chc_matrix scc chc_map summaries const_id in
  (* The above call boils down to one disjoin_chc_ts call *)
  analyze_query_predicate chc_matrix query_int const_id

let analyze_scc finished_flag summaries chc_map query_int scc =
  if !finished_flag then () else
  print_scc scc;
  match scc with
  | [p] when p = query_int ->
    handle_query_predicate scc chc_map summaries query_int;
    finished_flag := true
  | _ -> 
    if detect_linear_scc scc chc_map summaries 
    then summarize_linear_scc scc chc_map summaries
    else summarize_nonlinear_scc scc chc_map summaries

let print_summaries summaries = 
  logf ~level:`always "\n** Summaries as formulas **\n";
  BatMap.Int.iter
    (fun pred_num summary_rule ->
        Chc.print ~level:`always srk summary_rule;
        logf ~level:`always "  ")
    !summaries;
  logf ~level:`always "\n** Summaries as wedges **\n";
  BatMap.Int.iter
    (fun pred_num summary_rule ->
        Chc.print_as_wedge ~level:`always srk summary_rule;
        logf ~level:`always "  ")
    !summaries

let analyze_ruleset chcs query_int = 
  let callgraph = List.fold_left
    (fun graph chc ->
      List.fold_left
        (fun g p -> CallGraph.add_edge g chc.conc.pred_num p)
        graph
        (List.map (fun arg -> arg.pred_num) chc.hyps))
    CallGraph.empty
    chcs
  in
  let chc_map = List.fold_left
    (fun chc_map chc ->
      BatMap.Int.add
        chc.conc.pred_num
        (chc::(BatMap.Int.find_default [] chc.conc.pred_num chc_map))
        chc_map)
    BatMap.Int.empty
    chcs
  in
  let callgraph_sccs = CallGraphSCCs.scc_list callgraph in
  (* print_condensed_graph callgraph_sccs; *)
  let summaries = ref BatMap.Int.empty in
  let finished_flag = ref false in
  List.iter
    (analyze_scc finished_flag summaries chc_map query_int)
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
  let chcs = build_chc_records parsingCtx srk phi query_int in 
  List.iter 
    (fun chc -> 
        logf_noendl ~level:`info "Incoming CHC: @.  ";
        Chc.print srk chc) 
    chcs;
  analyze_ruleset chcs query_int

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
  CmdLine.register_config
    ("-no-sub-opt",
     Arg.Clear substitution_optimization,
     " Use equations, never substitutions, when putting together CHCs");
  (*CmdLine.register_config
    ("-chora-dual",
     Arg.Set ChoraCHC.chora_dual,
     " Compute non-trivial lower bounds in addition to upper bounds"); (* "dual-height" analysis *)*)
  CmdLine.register_config
    ("-no-chora-dual",
     Arg.Clear ChoraCHC.chora_dual,
     " Non-linear CHC 'CHORA' module should compute only upper bounds"); (* "dual-height" analysis *)
  CmdLine.register_config
    ("-chora-debug-squeeze",
     Arg.Set chora_debug_squeeze,
     " Print 'squeezed' depth-bound formula");
  ();;
