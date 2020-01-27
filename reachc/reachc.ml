open Srk

open Analyzer

let usage_msg = "Cfind program analyzer\nUsage: cfind [OPTIONS] file.smt2"

let anon_fun s = ignore (CmdLine.main_filename := Some s)

let () =
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

