module Log = Srk.Log
open Srk

(*module Ctx = Syntax.MakeSimplifyingContext ()*) (* Disturbs (simple-minded) format invariant of Horn clauses *)
module Ctx = Syntax.MakeContext ()

let srk = Ctx.context

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
    (*Format.printf "Finished reading SMTLIB file.@.";*)
    ()
    (*CfgIr.iter_defs (fun def -> Def.set_max_id def.did) file;
    file*)
