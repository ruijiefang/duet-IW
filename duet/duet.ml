open Srk

open! Safety

(* Frontends *)
open! TranslateCil
open! TranslateCbp

(* Analyses *)
open! Cra
open! Proofspace
open! Dependence
open! Categorize

let usage_msg = "Duet program analyzer\nUsage: duet [OPTIONS] file.[c|bp]"

let anon_fun s = ignore (CmdLine.parse s)

let _ =
  Sys.set_signal Sys.sigtstp (Sys.Signal_handle (fun _ -> Log.print_stats ()));
  let spec_list = CmdLine.spec_list () in
  Arg.parse (Arg.align spec_list) anon_fun usage_msg;
  match !CfgIr.gfile with
  | None -> begin
      prerr_endline "You must supply a program to be analyzed";
      Arg.usage (Arg.align spec_list) usage_msg
    end
  | Some _ -> begin
      CmdLine.run (CfgIr.get_gfile());
      if !CmdLine.show_stats then Log.print_stats ()
    end
