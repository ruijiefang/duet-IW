(** reachability tree module *)
open Core
open Srk
open CfgIr
open BatPervasives
open Syntax 
module RG = Interproc.RG
module WG = Srk.WeightedGraph
module G = RG.G
module Int = SrkUtil.Int
module TF = TransitionFormula

include Log.Make(struct let name = "reachTree" end)
type equery = OverApprox | UnderApprox

module ART
  (Ctx: Srk.Syntax.Context)
  (K : sig
    type t
    type var = Var.t
    val pp : Format.formatter -> t -> unit
    val guard : t -> Ctx.t formula
    val transform : t -> (var * Ctx.t arith_term) BatEnum.t
    val mem_transform : var -> t -> bool
    val get_transform : var -> t -> Ctx.t arith_term
    val assume : Ctx.t formula -> t
    val mul : t -> t -> t
    val add : t -> t -> t
    val zero : t
    val one : t
    val star : t -> t
    val exists : (var -> bool) -> t -> t
    val contains_havoc : t -> bool
    val get_post_model : Ctx.t Interpretation.interpretation -> t -> (Ctx.t Interpretation.interpretation) option 
  end)
  (TS : sig
          type vertex
          type transition = K.t
          type t 
          type query
          val empty : t
          val path_weight : query -> vertex -> transition
          val call_weight : query -> vertex * vertex -> transition
          val set_summary : query -> vertex * vertex -> transition -> unit
          val get_summary : query -> vertex * vertex -> transition
          val inter_path_summary : query -> vertex -> vertex -> transition
          val intra_path_summary : query -> vertex -> vertex -> transition
          val omega_path_weight :
            query -> (transition, 'b) Srk.Pathexpr.omega_algebra -> 'b
          val remove_temporaries : t -> t
          val forward_invariants_ivl :
            t -> vertex -> (vertex * Ctx.t Srk.Syntax.formula) list
          val forward_invariants_ivl_pa :
            Ctx.t Srk.Syntax.formula list ->
            t -> vertex -> (vertex * Ctx.t Srk.Syntax.formula) list
          val simplify : (vertex -> bool) -> t -> t
          val iter_succ_e :
            ((vertex * (transition TransitionSystem.label) * vertex) -> unit) -> t -> vertex -> unit
          val edge_weight :
            t -> vertex -> vertex -> K.t Srk.TransitionSystem.label
          val fold_succ_e : (vertex * (K.t Srk.TransitionSystem.label) * vertex -> 'b -> 'b) -> t -> vertex -> 'b -> 'b
          end)
  (PN : sig 
    type t 
    val make : TS.vertex * TS.vertex -> t 
    val string_of : t -> string 
    val of_string : string -> t 
    (* lexicographic comparison using Stdlib.compare *)
    val compare : t -> t -> int 
  end
  )
  (VN : sig 
    val to_vertex : int -> TS.vertex
    val of_vertex : TS.vertex -> int 
  end)
  (Summarizer : sig
    type t
    val init : TS.t -> TS.vertex -> t
    val proc_summary : t -> PN.t -> K.t
    val under_proc_summary : t -> PN.t -> K.t
    val set_proc_summary : t -> PN.t -> K.t -> unit
    val set_under_proc_summary : t -> PN.t -> K.t -> unit
    val refine :
      t -> 
      PN.t ->
      Ctx.t Srk.Syntax.formula ->
      Ctx.t Srk.Syntax.formula -> unit
    val refine_under :
      t -> PN.t -> K.t -> unit
    val path_weight_intra : t -> TS.vertex -> TS.vertex -> K.t
    val path_weight_inter : t -> TS.vertex -> TS.vertex -> K.t
  end)
  = struct  
  (* type for a tree node *)
  type node = int 
  module ProcMap = BatMap.Make(PN)
  module IntMap = BatMap.Make(Int)
  module StringMap = BatMap.Make(String)
  module ISet = BatSet.Make(Int)
  module DQ = BatDeque
  module ARR = Batteries.DynArray 
  type idq_t = int BatDeque.t 
  type state_formula = Ctx.t Syntax.formula 
  exception Mexception of string 
  let mk_true () = Syntax.mk_true Ctx.context
  let mk_false () = Syntax.mk_false Ctx.context 

  let log_formulas prefix formulas = 
    List.iteri (fun i f -> logf ~level:`always "[formula] %s(%i): %a\n" prefix i (Syntax.pp_expr Ctx.context) f) formulas 
  
  let log_weights prefix weights = 
    List.iteri (fun i f -> logf ~level:`always "[weight] %s(%i): %a\n" prefix i K.pp f) weights
  
  let log_model prefix model = 
    logf ~level:`always "[model] %s: %a\n" prefix Interpretation.pp model

  type t = {
    graph : TS.t;
    entry : TS.vertex;
    err_loc: TS.vertex;
    pre_state : state_formula;
    post_state : state_formula;
    mutable vtxcnt : int;
    mutable cfg_vertex : TS.vertex IntMap.t;
    mutable parents : int IntMap.t;
    mutable labels : (Ctx.t Syntax.formula) IntMap.t;
    mutable covers : int IntMap.t;       
    mutable children : int list IntMap.t;
    (* also maintain reverse map for each y, storing (x, y) that are in cover. *)
    (* i.e. reverse_covers[y] returns all x such that (x,y) is in the cover. *)
    mutable reverse_covers : (ISet.t) IntMap.t;
    (* precedent_nodes[v] stores all tree nodes mapping to CFG vertex v. Used in mc_close. *)
    mutable precedent_nodes : (ISet.t) IntMap.t;
    mutable models : (Ctx.t Interpretation.interpretation) IntMap.t;
    interproc : Summarizer.t
  }

  let make (g: TS.t) (entry: TS.vertex) (err_loc: TS.vertex) (pre: state_formula) (post: state_formula) interproc = 
    ref {
      graph = g;
      entry = entry;
      err_loc = err_loc;
      pre_state = pre;
      post_state = post;
      vtxcnt = 0;
      cfg_vertex = IntMap.empty; 
      parents = IntMap.empty;  
      labels = IntMap.empty; 
      children = IntMap.empty;
      covers =  IntMap.empty;
      reverse_covers = IntMap.empty; 
      precedent_nodes = IntMap.empty;
      models = IntMap.empty;
      interproc = interproc
    }

  let get_summarizer (art: t ref) = !art.interproc
  let get_err_loc (art: t ref) = !art.err_loc 
  let get_pre_state (art: t ref) = !art.pre_state 
  let get_post_state (art: t ref) = !art.post_state 
  (** [print_tree t ident v] prints an ART t with indentation `ident` rooted at node v *)
  let print_tree (art: t ref) (indent: string) (v: node) = 
    let rec print_tree_ (art: t ref) indent v = 
      logf ~level:`always "%s|" indent;
      logf ~level:`always "%s+-%d(%d)" indent v (IntMap.find v !art.cfg_vertex |> VN.of_vertex);
      List.iter (fun x -> print_tree_ art (indent^" ") x) (IntMap.find_default [] v !art.children)
    in logf ~level:`always "*"; print_tree_ art indent v

  (*  [parent t i] gets parent of node i in tree t.  *)
  let parent (art : t ref) (i : node) : node = 
    IntMap.find i !art.parents 

  (*  [t %-> i]: get CFG vertex mapped by node i in tree t. *)
  let maps_to (art : t ref) (i : node) : TS.vertex = 
    try 
      IntMap.find i !art.cfg_vertex 
    with _ -> 
      failwith @@ Printf.sprintf "maps_to: not found tree node %d\n" i 

  (* [cfg_edge_weight t mode u v] returns the edge weight of edge (u, v) in ART t.
       If (u, v) maps to a call-edge (x, y) in the CFG, return the over-approximate summary if 
      `mode` is set to `OverApprox`, and return an under-approximate summary otherwise. *)
  let edge_weight (art : t ref) (mode: equery) (u: node) (v: node) = 
    let t = !art in 
    match TS.edge_weight t.graph (maps_to art u) (maps_to art v) with  
      | TransitionSystem.Weight w -> w
      | TransitionSystem.Call (a, b) -> (* (a, b) is a pair of CFG vertices that uniquely identify a call *)
        let (a, b) = VN.to_vertex a, VN.to_vertex b in 
          begin match mode with 
          | OverApprox -> 
            Summarizer.proc_summary (t.interproc) (PN.make (a, b)) 
          | UnderApprox -> 
            Summarizer.under_proc_summary (t.interproc) (PN.make (a, b)) 
          end

  (* [tree_path t u] returns list of tree nodes that form the corrsp. tree path from root of t to tree node u *)
  let tree_path (art: t ref) (u : node) : node list = 
    let rec tree_path_rev art u = 
      match u with 
      | 0 -> [ 0 ]
      | x -> x :: (tree_path_rev art (parent art u)) 
    in List.rev @@ tree_path_rev art u

  (* [children t v] returns children of tree node v in tree t. *)
  let children (art : t ref) (v : node) : node list = 
    IntMap.find v !art.children 

  (* [descendants t v] returns descendants of tree node v in tree t in DFS order. *)
  let rec descendants (art : t ref) (v : node) : node list = 
    let v_children = children art v in 
    v :: (List.fold_left (fun l ch -> (descendants art ch) @ l) [] v_children)

  (* return leaves of subtree rooted at v. *)  
  let rec leaves (art: t ref) (v: node) : node list  = 
    let chs = children art v in 
    if List.length chs == 0 then [ v ]
    else 
      List.fold_left (fun child_leaves ch -> leaves art ch @ child_leaves) [] chs

  (* is a node in tree a leaf? *)
  let is_leaf (art: t ref) (v: node) : bool = 
    let chs = children art v in 
      List.length chs == 0

  (* [label t v] returns the node label of tree node v in tree t. *)
  let label (art : t ref) (v: node) : state_formula =
    IntMap.find v !art.labels

  (* (replaces) sets a label at v *)
  let set_label (art: t ref) (v: node) (lbl: state_formula) = 
    !art.labels <- IntMap.add v lbl !art.labels
  
  (* [get_precedent_nodes t v] retrieves a sequence of precedent nodes of tree node vin preorder in tree t. *)
  (* the list of precedent nodes for a cfg vertex is a list of tree nodes which map to the same cfg location, ordered by < on integers. *)
  let get_precedent_nodes (art: t ref) (v: node) = 
    let cfg_vertex = maps_to art v in 
    let precedents_set = 
      IntMap.find_default ISet.empty (VN.of_vertex cfg_vertex) (!art.precedent_nodes) in 
        ISet.elements precedents_set
  
  (* [path_condition t mode u] returns a list of edge weights that form the path condition from root of t to tree node u.  *)
  (* if `cutoff` is specified to a non-zero value, then [path_condition] will try to stop at intermediate ancestor `cutoff`. *)
  (* Over-approximate summaries are substituted in for call-edge locations if mode = `OverApprox`, and under-approximate *)
  (* summaries are substituted in otherwise. *)
  let path_condition (art: t ref) (mode: equery) ?(cutoff = 0) (u : node) = 
    if u == 0 || cutoff = u then 
      [ ]
    else 
      let rec visit (art: t ref) (u : node) =
        let v = parent art u in 
        begin if (v = 0) then begin 
          [ edge_weight art mode 0 u ]
        end else 
          begin if (v = cutoff) then (* v=0 case is already handled above *)
            [ edge_weight art mode cutoff u]
          else 
            edge_weight art mode v u :: (visit art v) 
          end 
        end 
      in List.rev (visit art u)  

  (** retrieves a new ART node ID, ensuring all ART nodes have distinct IDs in increasing order according to their creation *)
  let get_id (art : t ref) : node = 
    begin 
      let new_id = !art.vtxcnt in 
        !art.vtxcnt <- !art.vtxcnt + 1; 
        new_id
    end

  (* Add new tree leaf mapping to CFG vertex v and with parent tree node p. *)
  let add_tree_vertex (art: t ref) ?model ?(label=mk_true ()) (v: TS.vertex) (p: int) = 
    (* sequentially add v to the lists, indexed by !vtxcnt *)
    let new_vertex = get_id art in (* note that new_vertex refers to a new tree vertex, where as v is a corresp. cfg location. *)
    !art.cfg_vertex <- IntMap.add new_vertex v !art.cfg_vertex;
    !art.parents <- IntMap.add new_vertex p !art.parents;
    !art.labels <- IntMap.add new_vertex label !art.labels;
    !art.children <- IntMap.add new_vertex [] !art.children;
    (* set children of parent to be !vtxcnt :: children. *)
    if p >= 0 then !art.children <- IntMap.add p (new_vertex :: (IntMap.find p !art.children)) !art.children;
    (* Add v to precedent_nodes. *)
    let precedent_nodes = IntMap.find_default ISet.empty (VN.of_vertex v) !art.precedent_nodes |> ISet.add new_vertex in 
    !art.precedent_nodes <- IntMap.add (VN.of_vertex v) precedent_nodes !art.precedent_nodes;
    (* if there is a model, then add it as well. *)
    match model with 
    | Some model -> 
      (* putting vertex v (will be assigned tree node !Ctx.vtxcnt) on execlist with model... *)
      !art.models <- IntMap.add new_vertex model !art.models;
      new_vertex
    | None -> 
      new_vertex

  (** methods for expanding a leaf node v.
      * expand_plain:
      If in plain mode, simply expand v by visiting every out-neighbor on the corresponding cfg location.

      * expand_concolic: 
      If in concolic mode, 
        for every out-neighbor y of v, first try deriving a post-state model of v-> y, if successful, put it
          on the concolic execution worklist. Otherwise, it is a frontier node, and put it on the 
          mcmillan worklist. *)
  
  (* returns a list of new nodes to be added to the worklist *)
  let expand_plain (art : t ref) (v : int) = 
    (* vg is v's correpsonding cfg location in tree `art` *)
    let vg = maps_to art v in 
    let new_tree_nodes = ref [] in 
    TS.iter_succ_e (fun (_, _, y) ->  
        let u =  add_tree_vertex art y v in 
          new_tree_nodes := u :: !new_tree_nodes  
        ) !art.graph vg;
    List.rev !new_tree_nodes

  (* returns (new nodes on concolic worklist, new nodes on frontier worklist) *)
  (* a newly expanded node (leaf) is deemed a _concolic node_ if it can inherit 
     a post-state model from its parent by means of symbol substitution. It is deemed 
     a _frontier node_ if concrete execution cannot reach it from its parent node. A 
     frontier node does not have a model associated with it and is in need of refinement. *)
  let expand_concolic recurse_level (art : t ref) () (v: int) = 
    let oracle = 
      if recurse_level = 0 then Summarizer.path_weight_inter else Summarizer.path_weight_intra in
    let vg = maps_to art v in 
    let new_concolic_nodes, new_frontier_nodes = ref [], ref [] in 
      (* visit out neighbors of v *)
      begin match IntMap.find_opt v !art.models with 
      | Some m ->
        TS.iter_succ_e (fun (_, weight, y) -> 
          let weight =
            match weight with 
            | TransitionSystem.Weight w -> 
              if K.contains_havoc w then begin 
                (* w /\ guard (summary from y -> error location) *)
                K.mul w 
                  (K.assume @@ K.guard (K.mul (oracle !art.interproc y !art.err_loc) 
                  (K.assume !art.post_state)))
              end else 
                w
            | TransitionSystem.Call (u, v) -> 
              let proc = (VN.to_vertex u, VN.to_vertex v) |> PN.make in 
                Summarizer.proc_summary !art.interproc proc  in 
          begin match K.get_post_model m weight with 
          | Some y_model -> 
            let new_vtx = add_tree_vertex art ~model:y_model y v in  
              new_concolic_nodes := new_vtx :: !new_concolic_nodes
          | None -> 
            let new_node = add_tree_vertex art y v in 
              new_frontier_nodes := new_node :: !new_concolic_nodes 
          end
        ) !art.graph vg
      | None -> 
        failwith @@ Printf.sprintf "trying to expand from node %d(%d) without labelled model " v (maps_to art v |> VN.of_vertex)
      end;
      (* make it FIFO *)
      List.rev !new_concolic_nodes, List.rev !new_frontier_nodes
  

    (** "pseudo-expansion" of a leaf node mapping to error loc in a recursion level > 0. 
        Use this when recursively model-checking until the return location of a procedure call
        to expand one-"pseudo-edge" past the return vertex and verify that post-state is reached. *)
    let expand_pseudo (art : t ref) (v: int) = 
      if not (maps_to art v = !art.err_loc) then 
        failwith "err: expand_pseudo: must be called on a leaf node mapping to error location"
      else begin 
        match IntMap.find_opt v !art.models with 
        | Some m -> 
          begin match K.get_post_model m (K.assume !art.post_state) with 
          | Some _ -> `Error
          | None -> `Refine
          end
        | None -> `Refine
      end

  (** maintenance of coverings *)

  (* Adds (v -> w) to covering relation if possible and returns true, false otherwise. *)
  (* note that (v, w) in covering if stateLabel(v) IMPLIES stateLabel(w) *)
    let mc_cover (ctx: intra_context ref) v w =
      let art = !ctx.art in  
      let v_label = ReachTree.label art v in 
      let w_label = ReachTree.label art w in
      if (ReachTree.maps_to art v) <> (ReachTree.maps_to art w) then 
        failwith @@ Printf.sprintf "error: %d->%d but %d->%d\n" v (ReachTree.maps_to art v) w (ReachTree.maps_to art w);
      reset_solver ctx;
      match Smt.entails Ctx.context ~solver:(get_solver ctx) v_label w_label with 
      | `Yes -> 
          logf ~level:`always "   cover success (v=%d, w=%d). \n" v w;
          log_formulas "        v label " [v_label];
          log_formulas "        w label "  [w_label];
        let reverse_covers_w = IntMap.find_default ISet.empty w !art.reverse_covers in 
          !art.covers <- IntMap.add v w (!art.covers);
          !art.reverse_covers <- IntMap.add w (ISet.add v reverse_covers_w) !art.reverse_covers;
          true
      | `No | `Unknown -> false    
  
    let mc_close (ctx: intra_context ref) (v : int) = 
      (* Visits precedents of v in tree and attempts to derive covering relations[]. *)
      let art = !ctx.art in 
      (* A _precedent_ of v in tree is any vertex u<v such that u, v map to the same CFG locations. *)
        let precedents = ReachTree.get_precedent_nodes art v in
      (* Printf.printf "precedents of node %d : " v; List.iter (fun x -> Printf.printf " %d " x) precedents ; Printf.printf "\n";*)
      (* Fold from first node in preorder to the right. If covering succeeds, do not continue covering. *) 
      let result = List.fold_right (fun w status ->
        if status || w == v || w > v (* preorder constraint *) then status
        else begin 
          (* try to "cover v" by deciding if v --> w. If so, no need to further explore v. *)
          let cover_success = mc_cover ctx v w in 
          if cover_success then begin
            (* remove, for each descendant of v, nodes that are sinks of covers. *)
            let v_descendants = ReachTree.descendants art v in 
              List.iter (fun y -> 
                (* Find relations (x,y) in covering relation where y is descendant of v. *)
                if y <> v then 
                begin 
                  (* xs = {x | x -> y} *)
                  let xs = IntMap.find_default ISet.empty y !art.reverse_covers in 
                  (* Iterate through and remove pairs (x, y) from covering relation. *)
                  (* Step 1: Remove (x |-> y) from !ptt.covers. *)
                  ISet.iter (fun x -> !art.covers <- IntMap.remove x !art.covers) xs;
                  (* Step 2: Remove (y |-> xs) from !pthit.reverse_covers. *)
                  !art.reverse_covers <- IntMap.remove y !art.reverse_covers;
                  (* Step 3: add xs to worklist. *)
                  ISet.iter (fun x ->
                    (* add x's subtree leaves back to the worklist. *)
                    let x_leaves = ReachTree.leaves art x in 
                      List.iter (fun x_leaf -> 
                        logf ~level:`always "         close: adding %d back to worklist \n" x_leaf;
                        !ctx.worklist <- worklist_push x_leaf !ctx.worklist) x_leaves;
                    !art.models <- IntMap.remove x !art.models) xs
                end) v_descendants
          end; cover_success
        end) precedents false in result 
  
    (* Checks if tree node v is covered. It is covered if its ancestors or it is in covering relation. *)
    let rec mc_is_covered (ctx: intra_context ref) v = 
      let art = !ctx.art in 
      match IntMap.find_opt v !art.covers with 
      | None -> 
        if v == 0 then false
        else mc_is_covered ctx (ReachTree.parent art v)
      | Some u -> 
        logf ~level:`always "  | covered by %d\n" u;
        true 
    
  

  (* refine the label of each tree node u along path from tree root to v. *)
  let refine (art: t ref) path interpolants : node list = 
    let worklist = ref [] in 
    List.iter2 (fun u interpolant -> 
      let u_label = label art u in 
      let u_label' = Syntax.mk_and Ctx.context [ u_label ; interpolant ] in 
      log_formulas (Printf.sprintf "[relabelling %d CFG vertex %d] to label: " u (maps_to art u |> VN.of_vertex)) [ u_label' ];
      set_label art u u_label';
      (* remove ( * -> u) in covering relation; we just refined label(u) so implications of form label(y)->label(u)
         might not hold anymore. *)
      begin match IntMap.find_opt u !art.reverse_covers with 
      | None -> () 
      | Some l ->  
        (* remove covers (List.iter (fun x -> Printf.printf " (%d->%d)" x u) l *)
        let u_coverers  = 
        ISet.fold (fun x coverers -> 
          (* test if label(x) --> new label(u)*)
          let x_label = label art x in 
          let u_label = label art u in
          begin match Smt.entails Ctx.context (x_label) (u_label) with
          | `No | `Unknown -> 
            (* remove (x, u) from covering. *)
            logf ~level:`always "   refine: removing cover (%d->%d)\n" x u;
            !art.covers <- IntMap.remove x (!art.covers);
            (* add x's subtree leaves back to the worklist. *)
            let x_leaves = leaves art x in 
              List.iter (fun x_leaf -> 
                logf ~level:`always "         refine: adding %d back to worklist \n" x_leaf; 
                worklist := x_leaf :: !worklist) x_leaves;
            !art.models <- IntMap.remove x !art.models;
            l
          | `Yes -> 
            logf ~level:`always "    refine: cover (x %d-> u %d) still holds\n" x u;
            log_formulas " x label: " [x_label];
            log_formulas " u label: " [u_label];
            ISet.add x coverers (* unchanged. *) 
          end
          ) l ISet.empty in 
            !art.reverse_covers <- IntMap.add u u_coverers (!art.reverse_covers)
      end
    ) path interpolants; !worklist  


    (** procedures for lightweight verification of ART invariants *)

    let verify_well_labelled_tree (t: t ref) = 
      let rec aux v =
        let children = children t v in 
        match children with 
        | [] (* leaf node *) -> 
          begin match IntMap.find_opt v (!t.covers) with 
            | None -> 
              logf ~level:`always "!!! found uncovered leaf: %d\n" v;
              (TS.fold_succ_e (fun (x, _, y) _ ->
                logf ~level:`always "  ERROR ERROR ERROR: mapped cfg vertex %d has out-neighbor %d\n" 
                  (VN.of_vertex x) (VN.of_vertex y); 
                false 
              ) !t.graph (maps_to t v) true)
            | Some _ -> true 
          end 
        | _ -> 
          begin match IntMap.find_opt v (!t.covers) with 
          | None -> 
            logf ~level:`always "node %d uncovered\n" v;
            List.fold_left (fun acc u -> (aux u) && acc) true children 
          | Some u -> 
            logf ~level:`always "node %d covered by %d\n" v u;
            true 
          end 
      in 
      logf ~level:`always "verifying well-labelledness of ART...\n";
      let r =  aux 0 in 
      logf ~level:`always "...done verifying well-labelledness of ART\n";
      r

    let check_covering_welformedness (t: t ref) = 
      logf ~level:`always "checking welformedness of covering relations\n";
      IntMap.iter (fun dst covered_from -> 
        ISet.iter (fun src -> 
          logf ~level:`always "checking if (%d, %d) in covering\n" src dst;
          match IntMap.find_opt src (!t.covers) with 
          | Some dst' -> if dst' <> dst then failwith @@ Printf.sprintf "ERROR: (%d, %d) in covering\n" src dst'
          | None -> failwith "ERROR: not in covering"
        ) covered_from
      ) (!t.reverse_covers);
      logf ~level:`always "performing a reverse check\n";
      IntMap.iter (fun src dst -> 
        match IntMap.find_opt dst (!t.reverse_covers) with 
        | Some reverse_covers ->
          begin match ISet.mem src reverse_covers with 
          | false -> failwith @@ Printf.sprintf "ERROR: (%d, %d) in t.covers but %d not in %d's reverse_covers\n" src dst src dst
          | true -> ()
          end
        | None -> failwith @@ Printf.sprintf "ERROR: (%d, %d) in t.covers but no list found in reverse_covers\n" src dst
      ) (!t.covers);
      logf ~level:`always "...done checking welformedness of covering relations\n"

  end
