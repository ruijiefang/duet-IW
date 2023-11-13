module TransitionSystem = Srk.TransitionSystem
module Syntax = Srk.Syntax 
type equery = OverApprox | UnderApprox
module ART :
  functor
    (Ctx: Srk.Syntax.Context)
    (K : sig
           type t
           type var 
           val pp : Format.formatter -> t -> unit
           val guard : t -> Ctx.t Srk.Syntax.formula
           val transform : t -> (var * Ctx.t Srk.Syntax.arith_term) BatEnum.t
           val mem_transform : var -> t -> bool
           val get_transform : var -> t -> Ctx.t Srk.Syntax.arith_term
           val assume : Ctx.t Srk.Syntax.formula -> t
           val mul : t -> t -> t
           val add : t -> t -> t
           val zero : t
           val one : t
           val star : t -> t
           val exists : (var -> bool) -> t -> t
           val contains_havoc : t -> bool
           val get_post_model :
             Ctx.t Srk.Interpretation.interpretation ->
             t -> Ctx.t Srk.Interpretation.interpretation option
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
            val compare : t -> t -> int
          end)
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
    ->
    sig
      type node
      type t
      type state_formula = Ctx.t Srk.Syntax.formula
      exception Mexception of string
      val make :
        TS.t ->
        TS.vertex ->
        TS.vertex ->
        state_formula -> state_formula -> Summarizer.t ref -> t ref
      val get_summarizer : t ref -> Summarizer.t
      val get_pre_state : t ref -> Ctx.t Syntax.formula 
      val get_post_state : t ref -> Ctx.t Syntax.formula 
      val get_err_loc : t ref -> TS.vertex
      val print_tree : t ref -> string -> node -> unit
      val parent : t ref -> node -> node
      val maps_to : t ref -> node -> TS.vertex
      val edge_weight : t ref -> equery -> node -> node -> K.t
      val tree_path : t ref -> node -> node list
      val children : t ref -> node -> node list
      val descendants : t ref -> node -> node list
      val leaves : t ref -> node -> node list
      val is_leaf : t ref -> node -> bool
      val label : t ref -> node -> state_formula
      val set_label : t ref -> node -> state_formula -> unit
      val get_precedent_nodes : t ref -> node -> node list
      val path_condition :
        t ref -> equery -> ?cutoff:node -> node -> K.t list
      val get_id : t ref -> node
      val add_tree_vertex :
        t ref ->
        ?model:Ctx.t Srk.Interpretation.interpretation ->
        ?label:Ctx.t Srk.Syntax.formula -> TS.vertex -> int -> node
      val expand_plain : t ref -> int -> node list
      val expand_concolic :
        int -> t ref -> unit -> int -> node list * node list
      val expand_pseudo : t ref -> int -> [> `Error | `Refine ]
      val refine: t ref -> node list -> Ctx.t Syntax.formula list -> node list  
      val verify_well_labelled_tree : t ref -> unit
      val check_covering_welformedness : t ref -> unit 

    end
