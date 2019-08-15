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

let parse_smt2 filename =  
  (* FIXME let Z3 read the whole file... *)
  let chan = open_in filename in
  (*let file = CfgIr.read_file chan in
  let open Core in*)
  let str = really_input_string chan (in_channel_length chan) in
  close_in chan;
  let z3ctx = Z3.mk_context [] in
  let phi = SrkZ3.load_smtlib2 ~context:z3ctx srk str in
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
      Format.printf "    Conc: %a@." (Syntax.Formula.pp srk) conc
  ) !rules;

  List.iter (fun (hyp,conc,vars) ->
      assert ((is_syntactic_false srk conc) || (is_predicate srk conc))
  ) !rules;

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





