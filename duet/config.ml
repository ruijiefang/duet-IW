(* -*- mode:tuareg -*- *)
let bddbddb_path () =
  match Putil.find_file "bddbddb.jar" with
  | Some file -> Filename.dirname file
  | None -> "/home/rjf/fast/duet-IW/lib"
