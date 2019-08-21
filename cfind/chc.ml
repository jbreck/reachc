module Log = Srk.Log
open Srk

module CallGraph = Graph.Persistent.Digraph.ConcreteBidirectional(SrkUtil.Int)

module CallSet = BatSet.Make((*IntPair*)SrkUtil.Int)
module VertexSet = SrkUtil.Int.Set

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

(* Disturbs (simple-minded) format invariant of Horn clauses: *)
(*module Ctx = Syntax.MakeSimplifyingContext ()*) 
(* Use this instead, so as to preserve the format invariant: *)
module Ctx = Syntax.MakeContext ()

let srk = Ctx.context

let is_syntactic_false srk expr = 
  match Syntax.destruct srk expr with
  | `Fls -> true
  | _ -> false

let is_syntactic_true srk expr = 
  match Syntax.destruct srk expr with
  | `Tru -> true
  | _ -> false

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

let linked_formula_of_rule hyp conc vars =
  ()
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
let build_linked_formula srk1 srk2 vars phi =
  let rename_internal sym = 
    let name = Syntax.show_symbol srk1 sym in
    let typ = Syntax.typ_symbol srk1 sym in
    Syntax.mk_symbol srk2 ~name:name typ 
    in
  let rename = Memo.memo rename_internal in
  let rec get_rule vars rules phi = 
    match Syntax.destruct srk1 phi with
    | `Quantify (`Forall, nam, typ, expr) ->
       get_rule ((nam,typ)::vars) rules expr
    | `Or [nothyp; conc] ->
       (match Syntax.destruct srk1 nothyp with 
       | `Not (hyp) -> (hyp,conc,List.rev vars)::rules
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
    | _ -> get_rule [] [] phi
    in
  ()
  (*
  let rec go expr = 
  begin
    match destruct srk1 expr with
    | `Real qq -> Syntax.mk_real srk2 qq
    | `App (func, args) -> Syntax.mk_app srk2 
    | `Var (v, `TyReal)
    | `Var (v, `TyInt)
    | `Proposition (`Var v)
    | `Add sum
    | `Mul product
    | `Binop (`Div, s, t)
    | `Binop (`Mod, s, t)
    | `Unop (`Floor, t)
    | `Unop (`Neg, t)
    | `Ite (cond, bthen, belse)
    | `Tru
    | `Fls
    | `And conjuncts
    | `Or disjuncts
    | `Not phi
    | `Quantify (`Exists, name, typ, phi)
    | `Quantify (`Forall, name, typ, phi)
    | `Atom (`Eq, s, t)
    | `Atom (`Leq, s, t)
    | `Atom (`Lt, s, t)
  end
  in go expr
  *)

let parse_smt2 filename =  
  (* FIXME let Z3 read the whole file... *)
  let chan = open_in filename in
  (*let file = CfgIr.read_file chan in
  let open Core in*)
  let str = really_input_string chan (in_channel_length chan) in
  close_in chan;
  let z3ctx = Z3.mk_context [] in
  let phi = SrkZ3.load_smtlib2 ~context:z3ctx srk str in
  (*let phi = load_smtlib2 ~context:z3ctx srk str in*)
  (*Format.printf "Received formula: @.  %a @.@." (Syntax.Formula.pp srk) phi;*)
  let rules = ref [] in 
  let rec get_rule vars phi = 
      (*Format.printf "  Rule: %a@." (Syntax.Formula.pp srk) phi;*)
      match Syntax.destruct srk phi with
      | `Quantify (`Forall, nam, typ, expr) ->
         get_rule ((nam,typ)::vars) expr
      | `Or [nothyp; conc] ->
         (match Syntax.destruct srk nothyp with 
         | `Not (hyp) -> rules := (hyp,conc,List.rev vars)::(!rules)
         | _ -> Format.printf "  Bad Rule: %a@." (Syntax.Formula.pp srk) phi;
                failwith "Unrecognized rule format (No negated hypothesis)")
      | _ -> Format.printf "  Bad Rule: %a@." (Syntax.Formula.pp srk) phi;
             failwith "Unrecognized rule format (No top-level quantifier or disjunction)"
      in
  let rec split_rules phi = 
      match Syntax.destruct srk phi with
      | `And (parts) -> List.iter (get_rule []) parts
      | _ -> get_rule [] phi in
  split_rules phi;
  List.iter (fun (hyp,conc,vars) ->
      Format.printf "  Rule: @.";
      Format.printf "    Vars: ["; 
      List.iter (fun (nam,typ) -> Format.printf "%s," nam) vars;
      Format.printf "]@.";
      Format.printf "     Hyp: %a@." (Syntax.Formula.pp srk) hyp;
      Format.printf "    Conc: %a@." (Syntax.Formula.pp srk) conc;
      (* *)
      let hyp_preds = find_predicates srk hyp in
      Format.printf "  HPreds: ["; 
      List.iter (fun p -> Format.printf "%a," 
        (Syntax.pp_symbol srk) (Syntax.symbol_of_int p)) hyp_preds;
      Format.printf "]@.";
  ) !rules;

  let callgraph = List.fold_left
    (fun graph (hyp,conc,vars) ->
      assert ((is_syntactic_false srk conc) ||
              (is_syntactic_true srk conc) ||
              (is_predicate srk conc));
      if ((is_syntactic_false srk conc) ||
          (is_syntactic_true srk conc)) then graph else
      let conc_pred = id_of_predicate srk conc in
      let hyp_preds = find_predicates srk hyp in
      List.fold_left
        (fun g p -> CallGraph.add_edge g conc_pred p)
        graph
        hyp_preds)
    CallGraph.empty
    !rules
  in
  let rulemap = List.fold_left
    (fun rulemap (hyp,conc,vars) ->
      if ((is_syntactic_false srk conc) ||
          (is_syntactic_true srk conc)) then rulemap else
      let conc_pred = id_of_predicate srk conc in
      BatMap.Int.add
        conc_pred
        ((hyp,conc,vars)::(BatMap.Int.find_default [] conc_pred rulemap))
        rulemap)
    BatMap.Int.empty
    !rules
  in
  Format.printf "SCC list in processing order:@.";
  let callgraph_sccs = CallGraphSCCs.scc_list callgraph in
  List.iter 
    (fun scc ->
      Format.printf "  SCC: [";
      List.iter
        (fun p -> 
          Format.printf "%a,"
          (Syntax.pp_symbol srk)
          (Syntax.symbol_of_int p))
        scc;
      Format.printf "]@.")
    callgraph_sccs;
  List.iter
    (fun scc ->
      List.iter
        (fun p ->
          let p_rules = BatMap.Int.find_default [] p rulemap in
          List.iter
            (fun (hyp,conc,vars) ->
              match Syntax.destruct srk conc with
              | `App (func, args) ->
                Format.printf "-Rule w/conc %a has args {" (Syntax.Formula.pp srk) conc;
                List.iter
                  (fun arg ->
                    Format.printf "%a," (Syntax.Expr.pp srk) arg)
                  args;
                Format.printf "}@."
              | _ -> failwith "Non-application in conclusion")
            p_rules;
          ())
        scc)
    callgraph_sccs;
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





