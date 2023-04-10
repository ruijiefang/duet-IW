open Core
open Srk
open CfgIr

module RG = Interproc.RG
module Callgraph = RecGraph.Callgraph(Interproc.RG)
module CGLoop = Loop.Make(Callgraph)
let categorize file =
  let show_bool x =
    if x then "True"
    else "False"
  in
  match file.entry_points with
  | [main] -> begin
      let rg = Interproc.make_recgraph file in
      let is_recursive =
        Callgraph.callgraph rg main
        |> CGLoop.loop_nest
        |> CGLoop.cutpoints
        |> CGLoop.VertexSet.is_empty
        |> not
      in
      let _ = 
       (* try 
          file |> CfgIr.iter_defs (fun def ->
            match def.dkind with 
            | Assign (v, e) -> 
              let varname = Core.show_var v in 
              let exprname = Core.show_aexpr e in 
                Printf.printf "(assign %s = %s)\n" varname exprname 
            | Store (a, ae) -> 
              let varname = Core.show_ap a in 
              let aename = Core.show_aexpr ae in 
                Printf.printf "(store %s into %s)\n" varname aename
            | Call (varo, ae, ael) ->
              let varnameo = 
                match varo with | Some v -> Core.show_var v | None -> "" in 
              let aename = Core.show_aexpr ae in 
              let aelnames = List.map (fun x -> Core.show_aexpr x) ael in 
                Printf.printf "(call %s %s" varnameo aename;
                List.iter (fun x -> Printf.printf " %s" x) aelnames;
                Printf.printf ")\n"
            | Assume b -> 
              let bname = Core.show_bexpr b in 
                Printf.printf "(assume %s)\n" bname
            | Initial -> 
              Printf.printf "(initial)\n"
            | Assert (be, s)-> 
              let be_name = Core.show_bexpr be in 
              Printf.printf "(assert %s (%s))\n" be_name s   
            | AssertMemSafe (ae, s) -> 
              let ae_name = Core.show_aexpr ae in 
              Printf.printf "(assert_mem_safe %s (%s))\n" ae_name s 
            | Return (aeo) -> 
              begin match aeo with 
              | Some ae -> 
                Printf.printf "(return %s)\n" @@ Core.show_aexpr ae
              | None -> 
                Printf.printf "(return)\n" end
            | Builtin b -> 
              let bs = 
                begin match b with 
                | Alloc (var, ae, AllocStack)
                | Alloc (var, ae, AllocHeap) -> 
                    let varname = Core.show_var var in 
                    let aename = Core.show_aexpr ae in 
                    Printf.sprintf "(alloc %s %s)" varname aename 
                | Free a-> 
                    Printf.sprintf "(free %s)" @@ Core.show_aexpr a  
                | Fork (_, _, _) -> 
                    "(fork ...)"
                | Acquire _ -> 
                    "(acquire ...)"
                | Release _ -> 
                    "(release ...)"
                | AtomicBegin -> 
                    "(atomic begin)"
                | AtomicEnd -> 
                    "(atomic end)"
                | Exit -> 
                  "(exit)"
                end 
              in             
                Printf.printf "(builtin %s)\n" bs
          ); false
            
      with Not_found ->*) true 
    
      in let uses_memory =
        try
          file |> CfgIr.iter_defs (fun def ->
                      match def.dkind with
                      | Store (_, _) -> raise Not_found
                      | _ -> ());
          false
        with Not_found -> true
      in
      let uses_floats =
        let is_float v =
          match resolve_type (Varinfo.get_type v) with
          | Float _ -> true
          | _ -> false
        in
        List.exists is_float file.vars
        || List.exists
             (fun func ->
               List.exists is_float func.formals
               || List.exists is_float func.locals)
             file.funcs
      in
      Format.printf "Recursive: %s\n" (show_bool is_recursive);
      Format.printf "Memory:    %s\n" (show_bool uses_memory);
      Format.printf "Floats:    %s\n" (show_bool uses_floats)
    end
  | _ -> assert false

let _ =
  CmdLine.register_pass
    ("-categorize", categorize, " List features used in the input program")
