open BatPervasives
open Srk
open CfgIr
open BatPervasives
open Syntax
open Log 
include Log.Make(struct let name = "reachTree" end)

module RG = Interproc.RG
module WG = Srk.WeightedGraph
module G = RG.G
module Int = SrkUtil.Int
module TF = TransitionFormula

(** Useful definitions for SMT-based analyses: McMillan's assertion-checking algorithm + concolic execution *)

module ProcName = struct 
  type t = int * int 

  let make u v = (u, v)

  let string_of (p: t) = 
    let u, v = p in Printf.sprintf "%d:%d" u v 
  
  let of_string (s: string) = 
    match String.split_on_char ':' s with 
    | [ us ; vs ] -> (make (int_of_string us) (int_of_string vs))
    | _ -> failwith @@ Printf.sprintf "illegal procedure identifier %s" s

  (* lexicographic comparison using Stdlib.compare *)
  let compare p1 p2 = compare p1 p2 
end


module ProcMap = BatMap.Make(ProcName)
module IntMap = BatMap.Make(Int)
module StringMap = BatMap.Make(String)
module ISet = BatSet.Make(Int)
module DQ = BatDeque
module ARR = Batteries.DynArray 
module Int = SrkUtil.Int



(** reachability tree module *)
module Make 
  (C : sig
    type t
    val context : t context
  end)
  (Var : sig
    type t
    val pp : Format.formatter -> t -> unit
    val typ : t -> [ `TyInt | `TyReal ]
    val compare : t -> t -> int
    val symbol_of : t -> symbol
    val of_symbol : symbol -> t option
    val is_global : t -> bool
    val hash : t -> int
    val equal : t -> t -> bool
  end)
  (K : sig
    type t
    type var = Var.t
    val pp : Format.formatter -> t -> unit
    val guard : t -> C.t formula
    val transform : t -> (var * C.t arith_term) BatEnum.t
    val mem_transform : var -> t -> bool
    val get_transform : var -> t -> C.t arith_term
    val assume : C.t formula -> t
    val mul : t -> t -> t
    val add : t -> t -> t
    val zero : t
    val one : t
    val star : t -> t
    val exists : (var -> bool) -> t -> t
  end)
  (TS : sig 
    type vertex 
    type transition = K.t
    type t 
    type query

    module VarSet : BatSet.S with type elt = Var.t

    val empty : t
    val mk_query : ?delay:int ->
                 t ->
                 vertex ->
                 (module WeightedGraph.AbstractWeight
                         with type weight = transition) ->
                 query
    val path_weight : query -> vertex -> transition
    val call_weight : query -> (vertex * vertex) -> transition
    val set_summary : query -> (vertex * vertex) -> transition -> unit 
    val get_summary : query -> (vertex * vertex) -> transition
    val inter_path_summary : query -> vertex -> vertex -> transition 
    val intra_path_summary : query -> vertex -> vertex -> transition 
    val omega_path_weight : query -> (transition,'b) Pathexpr.omega_algebra -> 'b
    val remove_temporaries : t -> t
    val forward_invariants_ivl : t -> vertex -> (vertex * C.t formula) list
    val forward_invariants_ivl_pa : C.t formula list ->
                                  t ->
                                  vertex ->
                                  (vertex * C.t formula) list
    val simplify : (vertex -> bool) -> t -> t
    val loop_headers_live : t -> (int * VarSet.t) list  
  end)
  (CRA: sig     
    val mk_query : TS.t -> TS.vertex -> TS.query
  end)
  (Summarizer: sig 
    type t 
    type state_formula = C.t Syntax.formula 
    val init : TS.t -> int -> t ref 
    val proc_summary : t ref -> int * int -> K.t
    val set_proc_summary : t ref -> int * int -> K.t -> unit
    val refine : t ref -> int * int -> state_formula -> state_formula  -> unit
    val path_weight_intra : t ref -> TS.vertex -> TS.vertex -> K.t    
    val path_weight_inter : t ref -> TS.vertex -> TS.vertex -> K.t
  end)
= struct
  type state_formula = C.t Syntax.formula 


  type idq_t = int BatDeque.t 
  exception Mexception of string 
  let mk_true () = Syntax.mk_true C.context
  let mk_false () = Syntax.mk_false C.context 
  let srk = C.context 

  let log_formulas prefix formulas = 
    List.iteri (fun i f -> logf ~level:`always "[formula] %s(%i): %a\n" prefix i (Syntax.pp_expr_unnumbered srk) f) formulas 

  let log_weights prefix weights = 
    List.iteri (fun i f -> logf ~level:`always "[weight] %s(%i): %a\n" prefix i K.pp f) weights

  let log_model prefix model = 
    logf ~level:`always "[model] %s: %a\n" prefix Interpretation.pp model

  type t = {
    graph : TS.t;
    entry : int;
    err_loc: int;
    pre_state : state_formula;
    post_state : state_formula;
    mutable vtxcnt : int;
    mutable cfg_vertex : int IntMap.t;
    mutable parents : int IntMap.t;
    mutable labels : (Ctx.t Syntax.formula) IntMap.t;
    mutable free_ids : int DQ.t;
    mutable covers : int IntMap.t;       
    mutable children : int list IntMap.t;
    (* also maintain reverse map for each y, storing (x, y) that are in cover. *)
    (* i.e. reverse_covers[y] returns all x such that (x,y) is in the cover. *)
    mutable reverse_covers : (ISet.t) IntMap.t;
    (* precedent_nodes[v] stores all tree nodes mapping to CFG vertex v. Used in mc_close. *)
    mutable precedent_nodes : (ISet.t) IntMap.t;
    mutable models : (Ctx.t Interpretation.interpretation) IntMap.t;
    mutable edge_weight_substitutes : K.t ProcMap.t;
    interproc : Summarizer.t ref
  }

  let make (g: TS.t) (entry: int) (err_loc: int) (pre: state_formula) (post: state_formula) interproc = 
    ref {
      graph = g;
      entry = entry;
      err_loc = err_loc;
      pre_state = pre;
      post_state = post;
      vtxcnt = 0;
      cfg_vertex = IntMap.empty; (** ok *)
      parents = IntMap.empty;  (** ok *)
      labels = IntMap.empty; (** ok *)
      free_ids = DQ.empty; (** ok *)
      children = IntMap.empty; (***)
      covers =  IntMap.empty;
      reverse_covers = IntMap.empty;(** ok *) 
      precedent_nodes = IntMap.empty; (** ok *)
      models = IntMap.empty; (** ok *)
      edge_weight_substitutes = ProcMap.empty;
      interproc = interproc
    }

  let print_tree (art: t ref) indent v = 
    let rec print_tree_ (art: t ref) indent v = 
      logf ~level:`always "%s|" indent;
      logf ~level:`always "%s+-%d(%d)" indent v (IntMap.find v !art.cfg_vertex);
      List.iter (fun x -> print_tree_ art (indent^" ") x) (IntMap.find_default [] v !art.children)
    in logf ~level:`always "*"; print_tree_ art indent v

  (* blow up subtree at v *)
  let rec blowup ?(indent="") (art : t ref) (v : int) =
    let _ = logf ~level:`always "%sblowup: tree node %d \n" indent v in 
    let _ = print_tree art indent v in 
    let t = !art in  
    let v_children = IntMap.find_default [] v t.children in 
    let v_mapsto = IntMap.find v t.cfg_vertex in 
    let v_parent = IntMap.find v t.parents in 
    (* see if we need to delete v from list of children in its parents. *)
    IntMap.find v_parent !art.children 
    |> List.filter (fun x -> not (x = v)) 
    |> fun x -> (!art.children <- IntMap.add v_parent x !art.children);
    (* first put v on the free ids list *)
    t.free_ids <- DQ.cons v t.free_ids;
    (* disassociate v with all data structures *)    
    t.cfg_vertex <- IntMap.remove v t.cfg_vertex;
    t.parents <- IntMap.remove v t.parents;
    t.labels <- IntMap.remove v t.labels;
    t.models <- IntMap.remove v t.models;
    (* delete v from list of precedent nodes of maps_to(v). *)
    let precedents = IntMap.find v_mapsto t.precedent_nodes in 
      t.precedent_nodes <- IntMap.add v_mapsto (ISet.remove v precedents) t.precedent_nodes;
    (* handle deletion coverings. Check if (v, x) in t.covers. If so, remove v from t.reverse_covers[x]. *)
    match IntMap.find_opt v t.covers  with 
    | Some x -> (* v covers x *)
      let x_coverers = IntMap.find x t.reverse_covers in 
        t.reverse_covers <- IntMap.add x (ISet.remove v x_coverers) t.reverse_covers;
        (* remove (v, x) from t.covers as well *)
        t.covers <- IntMap.remove v t.covers   
    | None -> ();
    (* handle deletion of coverings. For each y in t.reverse_covers[v], remove (y, v) in t.covers. *)
    match IntMap.find_opt v t.reverse_covers with 
    | Some v_coverers ->
      (* first we can remove t.reverse_covers[v]. *)
      t.reverse_covers <- IntMap.remove v t.reverse_covers;
      (* next we remove (y,v) from t.covers for every y in v_coverers. *)
      ISet.iter (fun y -> 
        t.covers <- IntMap.remove y t.covers) v_coverers
    | None -> (); (* in this case we're done. *)
    (* finally, do recursive deletion *)
    List.iter (fun child -> blowup ~indent:(indent^" ") art child) v_children


  (*  [t %^ i]: get parent of node i in tree t.  *)
  let parent (art : t ref) (i : int) = 
    IntMap.find i !art.parents 

  (*  [t %-> i]: get CFG vertex mapped by node i in tree t. *)
  let maps_to (art : t ref) (i : int) = 
    try 
      IntMap.find i !art.cfg_vertex 
    with _ -> 
      failwith @@ Printf.sprintf "maps_to: not found tree node %d\n" i 

  (* [cfg_edge_weight t u v] returns the edge weight of edge (u, v) in ART t. *)
  let edge_weight (art : t ref) u v = 
    let t = !art in 
    match ProcMap.find_opt (u, v) t.edge_weight_substitutes with 
    | Some w -> 
      Printf.printf "cfg_edge_weight: edge weight substitute found for (%d,%d)\n" u v;
      w 
    | None -> 
      begin match WG.edge_weight t.graph (maps_to art u) (maps_to art v) with  
      | Weight w -> w
      | Call (a, b) ->
        let w = Summarizer.proc_summary (t.interproc) (a, b) in
        log_weights (Printf.sprintf "******* retrieving summary for %d,%d *****\n" u v) [w];
        w
      end 

  (* [tree_path t u] returns list of tree nodes that form the corrsp. tree path from root of t to tree node u *)
  let tree_path (art: t ref) u = 
    let rec tree_path_rev art u = 
      match u with 
      | 0 -> [ 0 ]
      | x -> x :: (tree_path_rev art (parent art u)) 
    in List.rev @@ tree_path_rev art u

  (* [children t v] returns children of tree node v in tree t. *)
  let children (art : t ref) v = 
    IntMap.find v !art.children 

  (* [descendants t v] returns descendants of tree node v in tree t in DFS order. *)
  let rec descendants (art : t ref) v = 
    let v_children = children art v in 
    v :: (List.fold_left (fun l ch -> (descendants art ch) @ l) [] v_children)

  (* return leaves of subtree rooted at v. *)  
  let rec leaves (art: t ref) v = 
    let chs = children art v in 
    if List.length chs == 0 then [ v ]
    else 
      List.fold_left (fun child_leaves ch -> leaves art ch @ child_leaves) [] chs

  (* is a vertex in tree a leaf? *)
  let is_leaf (art: t ref) v = 
    let chs = children art v in 
      List.length chs == 0

  (* [label t v] returns the node label of tree node v in tree t. *)
  let label (art : t ref) v =
    IntMap.find v !art.labels

  (* (replaces) sets a label at v *)
  let set_label (art: t ref) v lbl = 
    !art.labels <- IntMap.add v lbl !art.labels

  
  (* see if a vertex hasn't been deleted *)
  let find_opt (art: t ref) (v: int) = 
    IntMap.find_opt v !art.parents 

  let substitute_edge_weight (art: t ref) ((u, v) : int * int) w = 
    !art.edge_weight_substitutes <- ProcMap.add (u, v) w !art.edge_weight_substitutes

  let reset_substitute_map (t: t ref) = 
    !t.edge_weight_substitutes <- ProcMap.empty 

  let path_to (art: t ref) u = 
    let rec p (art: t ref) u = 
    match u with
    | 0 -> [ 0 ]
    | _ -> 
      u :: (p art (parent art u)) 
    in p art u |> List.rev 
  
  (* returns a list of call-edges (from shallow to deep) along path from root-to-node v*)
  (* call-edges are represented as 4-tuples: (tree node into call edge) -> callsite start -> callsite end -> (tree node out of call edge) *)
  let calls_in_path (art: t ref) v = 
    let rec f u = 
      let p = parent art u in 
        match p with 
        | -1 -> []
        | 0 -> (*caution: bug TODO*)
          begin match WG.edge_weight !art.graph (maps_to art 0) (maps_to art u) with 
          | Call (a, b) -> [ (0, (a, b), u) ]
          | _ -> []
          end 
        | n ->
          begin match WG.edge_weight !art.graph (maps_to art n) (maps_to art u) with 
          | Call (a, b) -> (n, (a, b), u) :: (f p)
          | _ -> f p 
          end
    in f v |> List.rev

  (* [get_precedent_nodes t v] retrieves a sequence of precedent nodes of tree node vin preorder in tree t. *)
  (* the list of precedent nodes for a cfg vertex is a list of tree nodes which map to the same cfg location, ordered by < on integers. *)
  let get_precedent_nodes (art: t ref) v = 
    let cfg_vertex = maps_to art v in 
    let precedents_set = 
      IntMap.find_default ISet.empty cfg_vertex (!art.precedent_nodes) in 
        ISet.elements precedents_set
  

  (* [t %-*> u] returns a list of edge weights that form the path condition from root of t to tree node u.  *)
  (* if `cutoff` is specified to a non-zero value, then [path_condition] will try to stop at intermediate ancestor `cutoff`. *)
  let path_condition (art: t ref) ?(cutoff = 0) (u : int) = 
    if u == 0 || cutoff = u then 
      [ ]
    else 
      let rec visit (art: t ref) (u : int) =
        let v = parent art u in 
        begin if (v = 0) then begin 
          [ edge_weight art 0 u  ]
        end else 
          begin if (v = cutoff) then (* v=0 case is already handled above *)
            [ edge_weight art cutoff u]
          else 
            edge_weight art v u :: (visit art v) 
          end 
        end 
      in List.rev (visit art u)  

  let get_id (art : t ref) = 
    match DQ.front !art.free_ids with 
    | Some (new_id, free_ids') -> 
      begin (* there are some recycled ids; make use of them. *)
        !art.free_ids <- free_ids';
        new_id
      end
    | None -> (* no more recycled ids; generate a new one. *)
      begin 
        let new_id = !art.vtxcnt in 
          !art.vtxcnt <- !art.vtxcnt + 1; new_id
      end

  (* Add new tree leaf mapping to CFG vertex v and with parent tree node p. *)
  let add_tree_vertex (art: t ref) ?model ?(label=mk_true ()) (v: WG.vertex) (p: int) = 
    (* sequentially add v to the lists, indexed by !vtxcnt *)
    let new_vertex = get_id art in (* note that new_vertex refers to a new tree vertex, where as v is a corresp. cfg location. *)
    !art.cfg_vertex <- IntMap.add new_vertex v !art.cfg_vertex;
    !art.parents <- IntMap.add new_vertex p !art.parents;
    !art.labels <- IntMap.add new_vertex label !art.labels;
    !art.children <- IntMap.add new_vertex [] !art.children;
    (* set children of parent to be !vtxcnt :: children. *)
    if p >= 0 then !art.children <- IntMap.add p (new_vertex :: (IntMap.find p !art.children)) !art.children;
    (* Add v to precedent_nodes. *)
    let precedent_nodes = IntMap.find_default ISet.empty v !art.precedent_nodes |> ISet.add new_vertex in 
    !art.precedent_nodes <- IntMap.add v precedent_nodes !art.precedent_nodes;
    (* if there is a model, then add it as well. *)
    match model with 
    | Some model -> 
      (* putting vertex v (will be assigned tree node !ctx.vtxcnt) on execlist with model... *)
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
    WG.iter_succ_e (fun (_, _, y) ->  
        let u =  add_tree_vertex art y v in 
          new_tree_nodes := u :: !new_tree_nodes  
        ) !art.graph vg;
    List.rev !new_tree_nodes

  (* returns (new nodes on concolic worklist, new nodes on frontier worklist) *)
  (* a newly expanded node (leaf) is deemed a _concolic node_ if it can inherit 
     a post-state model from its parent by means of symbol substitution. It is deemed 
     a _frontier node_ if concrete execution cannot reach it from its parent node. A 
     frontier node does not have a model associated with it and is in need of refinement. *)
  let expand_concolic solver recurse_level (art : t ref) (v: int) = 
    let oracle = 
      if recurse_level = 0 then Summarizer.path_weight_inter else Summarizer.path_weight_intra in
    let vg = maps_to art v in 
    let new_concolic_nodes, new_frontier_nodes = ref [], ref [] in 
      (* visit out neighbors of v *)
      begin match IntMap.find_opt v !art.models with 
      | Some m ->
        WG.iter_succ_e (fun (_, weight, y) -> 
          let weight =
            match weight with 
            | Weight w -> 
              if K.contains_havoc w then begin 
                (* w /\ guard (summary from y -> error location) *)
                K.mul w (K.assume @@ K.guard (K.mul (oracle !art.interproc y !art.err_loc) (K.assume !art.post_state)))
              end else 
                w
            | Call (u, v) -> Summarizer.proc_summary !art.interproc (u, v)  in 
          begin match K.get_post_model ~solver:(solver) m weight with 
          | Some y_model -> 
            let new_vtx = add_tree_vertex art ~model:y_model y v in  
              new_concolic_nodes := new_vtx :: !new_concolic_nodes
          | None -> 
            let new_vtx = add_tree_vertex art y v in 
              new_frontier_nodes := new_vtx :: !new_concolic_nodes 
          end
        ) !art.graph vg
      | None -> 
        failwith @@ Printf.sprintf "trying to expand from node %d(%d) without labelled model " v (maps_to art v)
      end;
      !new_concolic_nodes, !new_frontier_nodes
  

    (** "pseudo-expansion" of a leaf node mapping to error loc in a recursion level > 0. 
        Use this when recursively model-checking until the return location of a procedure call
        to expand one-"pseudo-edge" past the return vertex and verify that post-state is reached. *)
    let expand_pseudo solver (art : t ref) (v: int) = 
      if not (maps_to art v = !art.err_loc) then 
        failwith "err: expand_pseudo: must be called on a leaf node mapping to error location"
      else begin 
        match IntMap.find_opt v !art.models with 
        | Some m -> 
          begin match K.get_post_model ~solver:solver m (K.assume !art.post_state) with 
          | Some _ -> `Error
          | None -> `Refine
          end
        | None -> `Refine
      end
end
