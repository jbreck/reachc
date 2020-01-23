(*open Core
open CfgIr
open Apak*)
open Srk
(*open Safety*)

(* Frontends *)
(*open TranslateCil
open TranslateCbp
open Conversion*)

(* Analyses *)
(*open Cra
open Proofspace
open Dependence
open ConcDep
open Chora*)

(*open CmdLine*)
open Analyzer

let usage_msg = "Cfind program analyzer\nUsage: cfind [OPTIONS] file.smt2"

let anon_fun s = ignore (CmdLine.main_filename := Some s)

let () =
  (*Sys.set_signal Sys.sigtstp (Sys.Signal_handle (fun _ -> Log.print_stats ()));*)
  let spec_list = CmdLine.spec_list () in
  Arg.parse (Arg.align spec_list) anon_fun usage_msg;
  match !CmdLine.main_filename with
  | None -> 
    begin
      prerr_endline "You must supply a program to be analyzed";
      Arg.usage (Arg.align spec_list) usage_msg
    end
  | Some f -> 
      CmdLine.run f 
  (*;
  match !CfgIr.gfile with
  | None -> begin
      prerr_endline "You must supply a program to be analyzed";
      Arg.usage (Arg.align spec_list) usage_msg
    end
  | Some x -> begin
      CmdLine.run (CfgIr.get_gfile());
      if !CmdLine.show_stats then Log.print_stats ()
    end*)
