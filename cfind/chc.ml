module Log = Srk.Log
open Srk

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


(*module CallGraph = struct
  type t = CallSet.t M.t
  module V = (*IntPair*) SrkUtil.Int
  let iter_vertex f callgraph =
    M.iter (fun k _ -> f k) callgraph
  let iter_succ f callgraph v =
    CallSet.iter f (M.find v callgraph)
  let add_vertex callgraph v =
    if M.mem v callgraph then
      callgraph
    else
      M.add v CallSet.empty callgraph
  let add_edge callgraph u v =
    let callgraph = add_vertex callgraph v in
    if M.mem u callgraph then
      M.add u (CallSet.add v (M.find u callgraph)) callgraph
    else
      M.add u (CallSet.singleton v) callgraph
  let empty = M.empty
end*)

module CallGraphSCCs = Graph.Components.Make(CallGraph)

module Sctx = Syntax.MakeSimplifyingContext ()

module Pctx = Syntax.MakeContext ()

let parsingCtx = Pctx.context
let srk = Sctx.context

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
    let pp formatter var =
      let sym = symbol_of var in
      Format.fprintf formatter "%a" (Syntax.pp_symbol srk) sym
    let show = SrkUtil.mk_show pp
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

module K = MakeTransition(Var)

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



(* Set of variables? *)
(* BatSet.Int *)

(* I'm assuming our formulas are quantifier-free *)
module VarSet = BatSet.Int

(*
let rec find_int_variables_in_term srk (term:'a Syntax.Term.t) = 
  let alg = function
    | `Real qq -> VarSet.empty
    | `App (func, args) -> 
      let arg_vars = 
        List.map 
         (fun arg -> 
            (* WRONG!! *)
            match Syntax.expr_typ srk arg with
            | `TyInt  -> find_int_variables_in_term srk arg
            | `TyReal -> find_int_variables_in_term srk arg
            | `TyBool -> VarSet.empty (*find_int_variables_in_expr srk arg*)) 
          args in
      List.fold_left VarSet.union VarSet.empty arg_vars
    | `Var (v, `TyInt) -> VarSet.singleton v 
    | `Var (v, `TyReal) -> VarSet.empty
    | `Add (args) -> List.fold_left VarSet.union VarSet.empty args  
    | `Mul (args) -> List.fold_left VarSet.union VarSet.empty args  
    | `Binop (`Div, s, t) -> VarSet.union s t  
    | `Binop (`Mod, s, t) -> VarSet.union s t  
    | `Unop (`Floor, s) -> s 
    | `Unop (`Neg, s) -> s
    | `Ite (cond, bthen, belse) -> 
      VarSet.union
        (find_int_variables_in_expr srk cond)
        (VarSet.union bthen belse)
  in
  Syntax.Term.eval srk alg term

and find_int_variables_in_expr srk expr = 
  let alg = function
    | `And conjuncts -> List.fold_left VarSet.union VarSet.empty conjuncts
    | `Or disjuncts -> List.fold_left VarSet.union VarSet.empty disjuncts
    | `Quantify (_, name, typ, phi) -> failwith "find_int_variables_in_expr assumes quantifier-free formula"
    | `Not (phi) -> phi
    | `Proposition (`Var i) -> VarSet.empty
    | `Proposition (`App (p, args)) -> 
      let arg_vars = List.map (find_int_variables_in_term srk) args in
      List.fold_left VarSet.union VarSet.empty arg_vars
    | `Atom (_, x, y) -> 
      VarSet.union
        (find_int_variables_in_term srk x)
        (find_int_variables_in_term srk y)
    | `Ite (cond, bthen, belse) -> 
      VarSet.union
        cond
        (VarSet.union bthen belse)
    | `Tru -> VarSet.empty
    | `Fls -> VarSet.empty
  in
  Syntax.Formula.eval srk alg expr
*)

type pred_num = int
type var_pos_list = Srk.Syntax.Symbol.t list
type predicate_occurrence = pred_num * var_pos_list
type 'a linked_formula = predicate_occurrence *
                         (predicate_occurrence list) *
                         'a Srk.Syntax.Formula.t

let print_pred_occ srk pred_occ = 
    let (pred_num, var_symbols) = pred_occ in 
    let n_vars = List.length var_symbols in 
    Format.printf "%s(" (Syntax.show_symbol srk (Syntax.symbol_of_int pred_num));
    List.iteri 
      (fun i sym ->
        (*Format.printf "%s" (Syntax.show_symbol srk sym);*)
        Format.printf "%a" (Syntax.pp_symbol srk) sym;
        if i != n_vars - 1 then Format.printf ",")
      var_symbols;
    Format.printf ")"

let print_linked_formula srk rule = 
    let (conc_pred, hyp_preds, phi) = rule in
    Format.printf "{ @[";
    List.iter (fun pred -> print_pred_occ srk pred; Format.printf ";@ ")
      hyp_preds;
    Format.printf "%a@ -> " (Syntax.Formula.pp srk) phi;
    print_pred_occ srk conc_pred;
    Format.printf "@] }@."

let conc_pred_occ_of_linked_formula rule = 
    let (conc_pred, hyp_preds, phi) = rule in
    conc_pred

let conc_pred_id_of_linked_formula rule = 
    let (conc_pred, hyp_preds, phi) = rule in
    let (pred_num, vars) = conc_pred in
    pred_num

let hyp_pred_ids_of_linked_formula rule = 
    let (conc_pred, hyp_preds, phi) = rule in
    List.map 
      (fun pred_occ ->
        let (pred_num, vars) = pred_occ in
        pred_num)
      hyp_preds

let transition_of_linked_formula rule = 
    let (conc_pred, hyp_preds, phi) = rule in
    let (conc_pred_num, conc_vars) = conc_pred in
    assert (List.length hyp_preds = 1);
    let (hyp_pred_num, hyp_vars) = List.hd hyp_preds in
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

let linked_formula_of_transition tr model_rule =
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
  let (conc_pred, hyp_preds, _) = model_rule in
  let (conc_pred_num, _) = conc_pred in
  assert (List.length hyp_preds = 1);
  let (hyp_pred_num, hyp_vars) = List.hd hyp_preds in
  assert (hyp_pred_num = conc_pred_num);
  let new_args = 
    List.map 
      (fun hyp_var -> 
         let rec go pairs = 
           match pairs with
           | (pre_sym, post_sym)::rest -> if hyp_var = pre_sym then post_sym else go rest
           | [] -> failwith "Could not find symbol in linked_formula_of_transition"
         in go tr_symbols)
      hyp_vars in
  let new_conc_pred = (conc_pred_num, new_args) in 
  (new_conc_pred, hyp_preds, body)

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
  let (pred_num1, vs) = pred_occ1 in
  let (pred_num2, ws) = pred_occ2 in
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
        let (pred_num, vars) = pred_occ in
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
        let name = Syntax.show_symbol srk sym in
        let typ = Syntax.typ_symbol srk sym in
        Syntax.mk_symbol srk ~name typ) in
  let map_symbol sym = 
    if BatSet.Int.mem (Syntax.int_of_symbol sym) keep 
    then sym 
    else fresh_skolem sym in
  let freshen_pred_occ pred_occ = 
    let (pred_num, vars) = pred_occ in
    let new_vars = List.map map_symbol vars in 
    (pred_num, new_vars) in
  let (conc_pred, hyp_preds, phi) = rule in
  let new_conc_pred = freshen_pred_occ conc_pred in
  let new_hyp_preds = List.map freshen_pred_occ hyp_preds in
  let map_symbol_const sym = 
    Syntax.mk_const srk (map_symbol sym) in
  let new_phi = Syntax.substitute_const srk map_symbol_const phi in
  (new_conc_pred, new_hyp_preds, new_phi)

let substitute_args_rule rule1 rule2 = 
  let (conc_pred1, hyp_preds1, phi1) = rule1 in
  let (conc_pred2, hyp_preds2, phi2) = rule2 in
  let (conc_pred_num1, _) = conc_pred1 in
  let (conc_pred_num2, _) = conc_pred2 in
  assert (conc_pred_num1 = conc_pred_num2);
  let phi2 = substitute_args_pred conc_pred1 conc_pred2 phi2 in
  (* Note: the following assumes that the two hypothesis predicate 
       occurrence lists have the same order, which isn't strictly necessary *)
  let rec go preds1 preds2 phi =
    match (preds1,preds2) with
    | (pred1::more_preds1,pred2::more_preds2) ->
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
  let (inner_conc_pred_num, _) = inner_conc in
  let (outer_hyps_matching, outer_hyps_non_matching) = 
    List.partition
      (fun pred_occ ->
        let (pred_num, vars) = pred_occ in
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
        let (outer_hyp_pred_num, outer_hyp_args) = outer_hyp in
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

let linked_formula_has_hyp rule target_hyp_num = 
  let (conc, hyps, phi) = rule in
  List.fold_left 
    (fun running hyp -> 
       let (pred_num, args) = hyp in
       (running || (pred_num = target_hyp_num)))
    false
    hyps;;

(*

let of_transition_formula tr_symbols fmla = 
    let transform =
      List.fold_left (fun tr (pre, post) ->
          match Var.of_symbol pre with
          | Some v -> (v, Srk.Syntax.mk_const Cra.srk post)::tr
          | None -> assert false)
        []
        tr_symbols
    in
    K.construct fmla transform

 *)

  (*
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
  *)

(*
let load_smtlib2 ?(context=Z3.mk_context []) srk str =
  let z3 = context in
  let ast = Z3.SMT.parse_smtlib2_string z3 str [] [] [] [] in
  let sym_of_decl =
    let cos =
      Memo.memo (fun (name, typ) ->
          mk_symbol srk ~name typ)
    in
    fun decl ->
      let open Z3 in
      let sym = FuncDecl.get_name decl in
      match FuncDecl.get_domain decl with
      | [] ->
        cos (Symbol.to_string sym, typ_of_sort (FuncDecl.get_range decl))
      | dom ->
        let typ =
          `TyFun (List.map typ_of_sort dom,
                  typ_of_sort (FuncDecl.get_range decl))
        in
        cos (Symbol.to_string sym, typ)
  in
  match Expr.refine srk (of_z3 srk sym_of_decl ast) with
  | `Formula phi -> phi
  | `Term _ -> invalid_arg "load_smtlib2"
*)



(** 
 * 1. Replace int variable occurrences with constants
 * 2. 
 *)
let build_linked_formulas srk1 srk2 phi query_pred =
  let rec get_rule vars rules phi = 
    match Syntax.destruct srk1 phi with
    | `Quantify (`Forall, nam, typ, expr) ->
       get_rule ((nam,typ)::vars) rules expr
    | `Or [nothyp; conc] ->
       (match Syntax.destruct srk1 nothyp with 
       | `Not (hyp) -> (hyp,conc,vars)::rules (* reverse? *)
       | _ -> Format.printf "  Bad Rule: %a@." (Syntax.Formula.pp srk1) phi;
              failwith "Unrecognized rule format (No negated hypothesis)")
    | _ -> Format.printf "  Bad Rule: %a@." (Syntax.Formula.pp srk1) phi;
           failwith "Unrecognized rule format (No top-level quantifier or disjunction)"
    in
  let rules = 
    match Syntax.destruct srk1 phi with
    | `And (parts) -> List.fold_left 
      (fun rules psi -> get_rule [] rules psi)
      []
      parts
    | _ -> 
      (*allow*) (*get_rule [] [] phi*)
      (*forbid*) failwith "Currently forbidden: single-clause CHC program"
    in 
  (* Filter out 'dummy rules' whose conclusion is 'true' *)
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
    let rec go_formula expr = 
      begin
        match Syntax.Formula.destruct srk1 expr with
        (* Non-recursive nodes *)
        | `Tru -> (Syntax.mk_true srk2, [], [])
        | `Fls -> (Syntax.mk_false srk2, [], [])
        | `Proposition (`Var var) ->
          (* The boolean quantified variable var is being asserted. *)
          (* We replace v with an integer variable w and assert w == 1. *)
          let sym = var_to_skolem var in 
          (Syntax.mk_eq srk2 
            (Syntax.mk_const srk2 sym) (Syntax.mk_real srk2 QQ.one), 
          [], [])
        | `Proposition (`App (f, args)) ->
          (* A horn-clause-predicate occurrence *)
          let fsym = rename_pred f in 
          let fnumber = Syntax.int_of_symbol fsym in
          let rec accum_arg_info (arglist: (('a, 'b) Syntax.expr) list) symbollist predlist eqlist = 
            match arglist with
            | [] -> (symbollist, predlist, eqlist)
            | orig_arg::more_args ->
              begin
                match Syntax.Expr.refine srk1 orig_arg with
                | `Term arg ->
                begin
                  match Syntax.destruct srk1 arg with
                  | `Var (v, `TyInt) -> 
                    accum_arg_info 
                      more_args ((var_to_skolem v)::symbollist) predlist eqlist 
                  (*| `Var (v, `TyBool) -> 
                    accum_arg_info 
                      more_args ((var_to_skolem v)::symbollist) predlist eqlist*)
                  | `Var (v, `TyReal) ->
                    failwith "Unrecognized rule format (Got real predicate argument)"
                  | _ -> 
                  let (term, tpreds, teqs) = go_term arg in
                  let termsymbol = Syntax.mk_symbol srk2 ~name:"TermSymbol" `TyInt in
                  let termeq = Syntax.mk_eq srk2 (Syntax.mk_const srk2 termsymbol) term in
                  accum_arg_info 
                    more_args (termsymbol::symbollist) (tpreds @ predlist) (termeq::(teqs @ eqlist)) 
                  (*| _ -> failwith "Unrecognized rule format (Got unrecognized predicate argument)")*)
                end
                | `Formula arg ->
                begin
                  let (subformula, fpreds, feqs) = go_formula arg in
                  let formulasymbol = Syntax.mk_symbol srk2 ~name:"FormulaSymbol" `TyInt in
                  let formulatrue = 
                    (Syntax.mk_eq srk2 
                      (Syntax.mk_const srk2 formulasymbol) 
                      (Syntax.mk_real srk2 (QQ.one))) in
                  let notf f = Syntax.mk_not srk2 f in
                  let formulaiff = 
                      Syntax.mk_or srk2 
                        [Syntax.mk_and srk2 [     formulatrue;     subformula]; 
                         Syntax.mk_and srk2 [notf formulatrue;notf subformula]]
                  in
                  accum_arg_info 
                    more_args (formulasymbol::symbollist) (fpreds @ predlist) (formulaiff::(feqs @ eqlist))
                  (*| _ -> failwith "Unrecognized rule format (Got unrecognized predicate argument)")*)
                end
              end
            in
          let (argsymbols, predlist, eqlist) = accum_arg_info args [] [] [] in
          let pred_occ = (fnumber, argsymbols) in
          (Syntax.mk_true srk2, pred_occ::predlist, eqlist)
        (* Recursive nodes: bool from something *)
        | `Ite (cond, bthen, belse) ->
        let (cond_f, cond_p, cond_eq) = go_formula cond in
        let (bthen_f, bthen_p, bthen_eq) = go_formula bthen in 
        let (belse_f, belse_p, belse_eq) = go_formula belse in 
        (Syntax.mk_ite srk2 cond_f bthen_f belse_f,
         cond_p  @ bthen_p  @ belse_p,
         cond_eq @ bthen_eq @ belse_eq)
        (*| `Ite _ ->
          begin
            match Syntax.Expr.refine srk1 expr with
            | `Term ite_term ->
              begin
              match Syntax.Term.destruct srk1 ite_term with
                | `Ite (cond, bthen, belse) ->
                let (cond_f, cond_p, cond_eq) = go_formula cond in
                let (bthen_f, bthen_p, bthen_eq) = go_term bthen in 
                let (belse_f, belse_p, belse_eq) = go_term belse in 
                (Syntax.mk_ite srk2 cond_f bthen_f belse_f,
                 cond_p  @ bthen_p  @ belse_p,
                 cond_eq @ bthen_eq @ belse_eq)
                | _ -> failwith "Unrecognized rule forma (Got unrecognized ITE format 1)"
              end
            | _ -> failwith "Unrecognized rule forma (Got unrecognized ITE format 2)"
          end*)
        (* Recursive nodes: bool from bool *)
        | `And exprs -> 
          let (subexprs, preds, eqs) = combine_formulas exprs in  
          (Syntax.mk_and srk2 subexprs, preds, eqs) 
        | `Or exprs ->
          let (subexprs, preds, eqs) = combine_formulas exprs in  
          (Syntax.mk_or srk2 subexprs, preds, eqs) 
        | `Not p ->
          let (subexpr, preds, eqs) = go_formula p in
          (Syntax.mk_not srk2 subexpr, preds, eqs)
        (* Recursive nodes: bool from int *)
        | `Atom (op, s, t) -> 
          let ((s_sub,t_sub),preds, eqs) = combine_two_terms s t in
          (match op with
          | `Eq ->  (Syntax.mk_eq srk2 s_sub t_sub, preds, eqs) 
          | `Leq -> (Syntax.mk_leq srk2 s_sub t_sub, preds, eqs) 
          | `Lt ->  (Syntax.mk_lt srk2 s_sub t_sub, preds, eqs))
        (* Format-violating nodes: *)
        | `Quantify (_,_,_,_) -> 
          Format.printf "  Bad Rule: %a@." (Syntax.Formula.pp srk1) expr;
          failwith "Unrecognized rule format (Got quantifier in rule)"
        (*| _ -> (* includes ITE at the moment *)
          Format.printf "  Bad Rule: %a@." (Syntax.Formula.pp srk1) expr;
          failwith "Unrecognized rule format (Got unrecognized node in expr)"*)
      end
    and go_term term = 
      begin
        match Syntax.Term.destruct srk1 term with
        (* Non-recursive nodes *)
        | `Real qq -> (Syntax.mk_real srk2 qq, [], [])
        | `Var (var, `TyInt) -> 
          let sym = var_to_skolem var in 
          (Syntax.mk_const srk2 sym, [], [])
        (* Recursive nodes: int from int *)
        | `Add terms ->
          let (subexprs, preds, eqs) = combine_terms terms in  
          (Syntax.mk_add srk2 subexprs, preds, eqs)
        | `Mul terms ->
          let (subexprs, preds, eqs) = combine_terms terms in  
          (Syntax.mk_mul srk2 subexprs, preds, eqs)
        | `Binop (`Div, s, t) ->
          let ((s_sub,t_sub),preds, eqs) = combine_two_terms s t in
          (Syntax.mk_div srk2 s_sub t_sub, preds, eqs)
        | `Binop (`Mod, s, t) ->
          let ((s_sub,t_sub),preds, eqs) = combine_two_terms s t in
          (Syntax.mk_mod srk2 s_sub t_sub, preds, eqs)
        | `Unop (`Floor, t) ->
          let (subexpr, preds, eqs) = go_term t in
          (Syntax.mk_floor srk2 subexpr, preds, eqs)
        | `Unop (`Neg, t) ->
          let (subexpr, preds, eqs) = go_term t in
          (Syntax.mk_neg srk2 subexpr, preds, eqs)
        | `Ite (cond, bthen, belse) ->
        let (cond_f, cond_p, cond_eq) = go_formula cond in
        let (bthen_f, bthen_p, bthen_eq) = go_term bthen in 
        let (belse_f, belse_p, belse_eq) = go_term belse in 
        (Syntax.mk_ite srk2 cond_f bthen_f belse_f,
         cond_p  @ bthen_p  @ belse_p,
         cond_eq @ bthen_eq @ belse_eq)
        (* Format-violating nodes: *)
        | `Var (v, `TyReal) ->
          Format.printf "  Bad Rule: %a@." (Syntax.Term.pp srk1) term;
          failwith "Unrecognized rule format (Got real-valued variable)"
        | `App (func, args) -> 
          Format.printf "  Bad Rule: %a@." (Syntax.Term.pp srk1) term;
          failwith "Unrecognized rule format (Got function application)"
        (*| _ -> 
          Format.printf "  Bad Rule: %a@." (Syntax.Term.pp srk1) term;
          failwith "Unrecognized rule format (Got unrecognized node in term)"*)
      end
    and combine_formulas exprs = 
      begin
        List.fold_left
          (fun (subexprs, preds, eqs) ex -> 
              let ex_s, ex_p, ex_e = go_formula ex in 
              ((ex_s::subexprs), (ex_p @ preds), (ex_e @ eqs)))
          ([],[],[])
          exprs
      end
    and combine_terms exprs = 
      begin 
        List.fold_left
          (fun (subexprs, preds, eqs) ex -> 
              let ex_s, ex_p, ex_e = go_term ex in 
              ((ex_s::subexprs), (ex_p @ preds), (ex_e @ eqs)))
          ([],[],[])
          exprs
      end
    and combine_two_terms s t = 
      begin
        let (s_sub,s_p,s_e) = go_term s in
        let (t_sub,t_p,t_e) = go_term t in 
        ((s_sub,t_sub), (s_p @ t_p), (s_e @ t_e))
      end
      in
    let (hyp_sub,hyp_preds,hyp_eqs) = go_formula hyp in
    let (conc_sub,conc_preds,conc_eqs) = go_formula conc in
    let conc_pred_occ = match conc_preds with
      | [conc_pred_occ] -> conc_pred_occ
      | [] -> 
        if (not (is_syntactic_false srk2 conc_sub))
        then failwith "Unrecognized rule format (Non-false non-predicate conclusion)"
        else (query_pred, [])
      | _ -> failwith "Unrecognized rule format (Multiple conclusion predicate)"
    in 
    let eqs = hyp_eqs @ conc_eqs in
    let phi = 
      if (List.length eqs) > 0
      then Syntax.mk_and srk2 (hyp_sub::eqs)
      else hyp_sub in
    (conc_pred_occ, hyp_preds, phi)
    (* *)
  in
  List.map linked_formula_of_rule rules

(*
let add_entry_to_matrix matrix rowid colid value = 
  (if not (BatMap.Int.mem rowid !matrix) then
    BatMap.Int.add !matrix rowid (BatMap.Int.empty));
  let row = BatMap.Int.find rowid !matrix in
  let row = BatMap.Int.add colid value row in
  matrix := BatMap.
*)

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

let parse_smt2 filename =  
  (* FIXME let Z3 read the whole file... *)
  let chan = open_in filename in
  (*let file = CfgIr.read_file chan in
  let open Core in*)
  let str = really_input_string chan (in_channel_length chan) in
  close_in chan;
  let z3ctx = Z3.mk_context [] in
  let phi = SrkZ3.load_smtlib2 ~context:z3ctx parsingCtx str in
  let query_sym = Syntax.mk_symbol srk ~name:"QUERY" `TyBool in
  (*let query_pred = Syntax.mk_app parsingCtx query_sym [] in*)
  let query_int = Syntax.int_of_symbol query_sym in  
  let rules = build_linked_formulas parsingCtx srk phi query_int in 
  let _ = List.iter 
    (fun rule -> 
        Format.printf "Incoming CHC: @.  ";
        print_linked_formula srk rule) 
    rules in 
  (*let phi = load_smtlib2 ~context:z3ctx srk str in*)
  (*Format.printf "Received formula: @.  %a @.@." (Syntax.Formula.pp srk) phi;*)
  let callgraph = List.fold_left
    (fun graph rule ->
      let conc_pred_id = conc_pred_id_of_linked_formula rule in
      let hyp_pred_ids = hyp_pred_ids_of_linked_formula rule in
      List.fold_left
        (fun g p -> CallGraph.add_edge g conc_pred_id p)
        graph
        hyp_pred_ids)
    CallGraph.empty
    rules
  in
  let rulemap = List.fold_left
    (fun rulemap rule ->
      let conc_pred_id = conc_pred_id_of_linked_formula rule in
      BatMap.Int.add
        conc_pred_id
        (rule::(BatMap.Int.find_default [] conc_pred_id rulemap))
        rulemap)
    BatMap.Int.empty
    rules
  in
  let callgraph_sccs = CallGraphSCCs.scc_list callgraph in
  (*Format.printf "SCC list in processing order:@.";
  List.iter 
    (fun scc ->
      Format.printf "SCC: [";
      List.iter
        (fun p -> 
          Format.printf "%a,"
          (Syntax.pp_symbol srk)
          (Syntax.symbol_of_int p))
        scc;
      Format.printf "]@.")
    callgraph_sccs;*)
  let summaries = ref BatMap.Int.empty in
  let finished = ref false in
  List.iter
    (fun scc -> if !finished then () else 
    begin
      (Format.printf "SCC: [";
      List.iter
        (fun p -> 
          Format.printf "%a,"
          (Syntax.pp_symbol srk)
          (Syntax.symbol_of_int p))
        scc;
      Format.printf "]@.");
      let const_id = (List.hd (List.sort compare scc)) - 1 in
      assert (not (List.mem const_id scc));
      (*let summary_list_vector = ref BatMap.Int.empty in *)
      (*if (List.length scc) > 1 then failwith "Mutual SCC not yet implemented" else*)
      let rule_list_matrix = new_empty_matrix () in
      Format.printf "  Finding rules@.";
      List.iter
        (fun p ->
          let p_rules = BatMap.Int.find p rulemap in
          (* Substitute summaries of lower SCCs into this predicate's rules *)
          let p_rules = 
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
            p_rules in 
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
      (* Disjoin rules in each matrix entry *)
      (*let summary_vector = ref BatMap.Int.empty in
      List.iter
        (fun p ->
          if BatMap.Int.mem p !summary_list_vector then
            let rs = BatMap.Int.find p !summary_list_vector in
            let combined_rule = disjoin_linked_formulas rs in
            summary_vector := BatMap.Int.add p combined_rule !summary_vector
        ) scc;*)
      let rule_matrix = new_empty_matrix () in
      Format.printf "  Disjoining CHCs@.";
      List.iter
        (fun p ->
          matrix_row_iteri
            rule_list_matrix
            p
            (fun _ colid rules ->
              (*Format.printf "    rowid:%d colid:%d@." p colid;
              List.iter
                (fun r ->
                Format.printf "    - One rule to disjoin: ";
                print_linked_formula srk r;
                Format.printf "@.")
              rules;*)
              let combined_rule = disjoin_linked_formulas rules in
              assign_matrix_element rule_matrix p colid combined_rule)
          ) scc;
      (* Use query predicate here? *)
      match scc with
      | [p] when p = query_int ->
        (match get_matrix_element_opt rule_matrix query_int const_id with
          | None -> failwith "Missing final CHC"
          | Some final_rule -> 
            finished := true;
            Format.printf "Final CHC: @.  ";
            print_linked_formula srk final_rule;
            Format.printf "@.";
            let (conc, hyps, final_phi) = final_rule in
            (match Wedge.is_sat srk final_phi with
            | `Sat -> Format.printf "RESULT: UNKNOWN (final constraint is sat)@."
            | `Unsat -> Format.printf "RESULT: SAT (final constraint is unsat)@."
            | `Unknown -> Format.printf "RESULT: UNKNOWN (final constraint unknown)@."))
      | _ -> 
      begin
        (* Now, eliminate predicates from this SCC one at a time*)
        (Format.printf "  Eliminating predicates@.");
        List.iter
          (fun p ->
            if p = query_int then () else
            begin
              (Format.printf "    - Eliminating %a@." 
                (Syntax.pp_symbol srk) 
                (Syntax.symbol_of_int p));
              if has_matrix_element rule_matrix p p then
                let combined_rec = get_matrix_element rule_matrix p p in
                Format.printf "  Combined recursive CHC: ";
                print_linked_formula srk combined_rec;
                Format.printf "@.";
                let tr = transition_of_linked_formula combined_rec in
                Format.printf "    As transition:@.";
                Format.printf "    %a@." K.pp tr;
                let tr_star = K.star tr in 
                Format.printf "    Starred:@.";
                Format.printf "    %a@." K.pp tr_star;
                let tr_star_rule = 
                  linked_formula_of_transition tr_star combined_rec in
                Format.printf "    Starred as CHC:@.  ";
                print_linked_formula srk tr_star_rule;
                (* *)
                matrix_row_iteri rule_matrix p
                  (fun _ hyp nonrec_rule ->
                    (* *)
                    let sub_rule = subst_all tr_star_rule nonrec_rule in
                    assign_matrix_element rule_matrix p hyp sub_rule);
                remove_matrix_element rule_matrix p p
            end;
            matrix_col_iteri rule_matrix p 
              (fun q _ qrule ->
                (* qrule has hypothesis p and conclusion q *)
                matrix_row_iteri rule_matrix p
                  (fun _ r prule ->
                    assert (r != p);
                    (* prule has hypothesis r and conclusion p *)
                    let sub_rule = subst_all qrule prule in
                    match get_matrix_element_opt rule_matrix q r with
                    | None ->
                      assign_matrix_element rule_matrix q r sub_rule
                    | Some prev_rule ->
                      let combined_rule = 
                        disjoin_linked_formulas [prev_rule; sub_rule] in
                      assign_matrix_element rule_matrix q r combined_rule))
          ) scc;
        List.iter
          (fun p ->
            match get_matrix_element_opt rule_matrix p const_id with
            | None -> failwith "Missing const_id entry in rule_matrix"
            | Some rule -> summaries := (BatMap.Int.add p rule !summaries)
          ) scc
      end
    end)
    callgraph_sccs;
  (*
  XList.iter
  X  (fun scc ->
  X    List.iter
  X      (fun p ->
  X        let p_rules = BatMap.Int.find_default [] p rulemap in
  X        List.iter
  X          (fun (hyp,conc,vars) ->
  X            match Syntax.destruct srk conc with
  X            | `App (func, args) ->
  X              Format.printf "-Rule w/conc %a has args {" (Syntax.Formula.pp srk) conc;
  X              List.iter
  X                (fun arg ->
  X                  Format.printf "%a," (Syntax.Expr.pp srk) arg)
  X                args;
  X              Format.printf "}@."
  X            | _ -> failwith "Non-application in conclusion")
  X          p_rules;
  X        ())
  X      scc)
  X  callgraph_sccs;
  *)
  (*let rules = ref [] in 
  Xlet rec get_rule vars phi = 
  X    (*Format.printf "  Rule: %a@." (Syntax.Formula.pp srk) phi;*)
  X    match Syntax.destruct srk phi with
  X    | `Quantify (`Forall, nam, typ, expr) ->
  X       get_rule ((nam,typ)::vars) expr
  X    | `Or [nothyp; conc] ->
  X       (match Syntax.destruct srk nothyp with 
  X       | `Not (hyp) -> rules := (hyp,conc,List.rev vars)::(!rules)
  X       | _ -> Format.printf "  Bad Rule: %a@." (Syntax.Formula.pp srk) phi;
  X              failwith "Unrecognized rule format (No negated hypothesis)")
  X    | _ -> Format.printf "  Bad Rule: %a@." (Syntax.Formula.pp srk) phi;
  X           failwith "Unrecognized rule format (No top-level quantifier or disjunction)"
  X    in
  Xlet rec split_rules phi = 
  X    match Syntax.destruct srk phi with
  X    | `And (parts) -> List.iter (get_rule []) parts
  X    | _ -> get_rule [] phi in
  Xsplit_rules phi;
  XList.iter (fun (hyp,conc,vars) ->
  X    Format.printf "  Rule: @.";
  X    Format.printf "    Vars: ["; 
  X    List.iter (fun (nam,typ) -> Format.printf "%s," nam) vars;
  X    Format.printf "]@.";
  X    Format.printf "     Hyp: %a@." (Syntax.Formula.pp srk) hyp;
  X    Format.printf "    Conc: %a@." (Syntax.Formula.pp srk) conc;
  X    (* *)
  X    let hyp_preds = find_predicates srk hyp in
  X    Format.printf "  HPreds: ["; 
  X    List.iter (fun p -> Format.printf "%a," 
  X      (Syntax.pp_symbol srk) (Syntax.symbol_of_int p)) hyp_preds;
  X    Format.printf "]@.";
  X) !rules;
  *)
  (*let multi = 
    List.fold_left 
      (fun running scc -> (running || ((List.length scc) > 1)))
      false
      callgraph_sccs in
  (if multi then 
      Format.printf "MULTI-PREDICATE SYSTEM@."
  else
      Format.printf "SINGLE-PREDICATE SYSTEM@.");*)
  (*Format.printf "PARSING_COMPLETE@.";*)
  (*
   
  (*let calls =
    fold_edges (fun (_, label, _) callset ->
        match label with
        | Weight _ -> callset
        | Call (en, ex) -> CallSet.add (en, ex) callset)
      rg
      CallSet.empty
  in*) 
  let initial_callgraph =
    (*CallSet.fold (fun call callgraph ->
        CallGraph.add_edge callgraph callgraph_entry call)
      calls*)
      CallGraph.empty
  in 
  let callgraph =
    List.fold_left (fun callgraph (hyp,conc,vars) ->
        CallSet.fold (fun target callgraph ->
            CallGraph.add_edge callgraph target proc)
          (NPathexpr.eval ~table pe_procs pathexpr)
          callgraph)
      call_pathexpr
      (*CallGraph.empty*) initial_callgraph (* Use CallGraph.empty here? *)
  in      
  List.rev (CallGraphSCCs.scc_list callgraph) (* = callgraph_sccs *)
  in 

  (*Format.printf "Finished reading SMTLIB file.@.";*)

  *)

  ()
  (*CfgIr.iter_defs (fun def -> Def.set_max_id def.did) file;
  file*)








(* **************************************************** *)
(*
      List.iter
        (fun p ->
          if p = query_int then () else
          let (rec_rules, nonrec_rules) = 
              List.partition
                (fun rule -> List.mem p (hyp_pred_ids_of_linked_formula rule))
                p_rules in
          Format.printf "  Rec rules: @.";
          Format.printf "    Original rec rules: @.";
          List.iter
            (fun rule ->
              Format.printf "      Rec rule: ";
              print_linked_formula srk rule;
              Format.printf "@.")
            rec_rules;
          let combined_rec = disjoin_linked_formulas rec_rules in
          Format.printf "    Combined rec rule: ";
          print_linked_formula srk combined_rec;
          Format.printf "@.";
          let tr = transition_of_linked_formula combined_rec in
          Format.printf "    As transition:@.";
          Format.printf "    %a@." K.pp tr;
          let tr_star = K.star tr in 
          Format.printf "    Starred:@.";
          Format.printf "    %a@." K.pp tr_star;
          let tr_star_rule = linked_formula_of_transition tr_star combined_rec in
          Format.printf "    Starred as rule:@.  ";
          print_linked_formula srk tr_star_rule;
          Format.printf "  Non-rec rules: @.";
          Format.printf "    Original non-rec rules: @.";
          List.iter
            (fun rule ->
              Format.printf "      Non-rec rule: ";
              print_linked_formula srk rule;
              Format.printf "@.")
            nonrec_rules;
          let combined_nonrec = disjoin_linked_formulas nonrec_rules in
          Format.printf "    Combined non-rec rule: ";
          print_linked_formula srk combined_nonrec;
          Format.printf "@.";
          let summary = subst_all tr_star_rule combined_nonrec in
          Format.printf "  Summary: ";
          print_linked_formula srk summary;
          Format.printf "@.";
*)
