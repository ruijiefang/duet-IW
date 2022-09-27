open Core
open Srk
open CfgIr
open BatPervasives

module RG = Interproc.RG
module WG = Srk.WeightedGraph
module TLLRF = TerminationLLRF
module TDTA = TerminationDTA
module G = RG.G
module Ctx = Syntax.MakeSimplifyingContext ()
module Int = SrkUtil.Int
module TF = TransitionFormula

let srk = Ctx.context

include Log.Make(struct let name = "cra" end)

let forward_inv_gen = ref true
let forward_pred_abs = ref false
let dump_goals = ref true
let monotone = ref false
let nb_goals = ref 0
let termination_exp = ref true
let termination_llrf = ref true
let termination_dta = ref true
let termination_phase_analysis = ref true
let precondition = ref false
let termination_attractor = ref true
let termination_prenex = ref true

let dump_goal loc path_condition =
  if !dump_goals then begin
    let filename =
      Format.sprintf "%s%d-line%d.smt2"
        (Filename.chop_extension (Filename.basename loc.Cil.file))
        (!nb_goals)
        loc.Cil.line
    in
    let chan = Stdlib.open_out filename in
    let formatter = Format.formatter_of_out_channel chan in
    logf ~level:`always "Writing goal formula to %s" filename;
    Syntax.pp_smtlib2 srk formatter path_condition;
    Format.pp_print_newline formatter ();
    Stdlib.close_out chan;
    incr nb_goals
  end

let tr_typ typ = match resolve_type typ with
  | Int _   -> `TyInt
  | Float _ -> `TyReal
  | Pointer _ -> `TyInt
  | Enum _ -> `TyInt
  | Array _ -> `TyInt
  | Dynamic ->
    (* TODO : we should conservatively translate Dynamic as a real, but SMT
       solvers struggled with the resulting mixed int/real constraints.  To
       make this sound we should do a type analysis to determine when a
       dynamic type can be narrowed to an int.  The main place this comes up
       is in formal parameters, which are typed dynamic to make indirect calls
       easier to handle. *)
    `TyInt
  | _ -> `TyInt

type value =
  | VVal of Var.t
  | VPos of Var.t
  | VWidth of Var.t
    [@@deriving ord]

module Value = struct
  type t = value [@@deriving ord]
  let hash = function
    | VVal v -> Hashtbl.hash (0, Var.hash v)
    | VPos v -> Hashtbl.hash (1, Var.hash v)
    | VWidth v -> Hashtbl.hash (2, Var.hash v)
  let equal x y = compare_value x y = 0
end
module ValueHT = Hashtbl.Make(Value)

let var_of_value = function
  | VVal v | VPos v | VWidth v -> v
let map_value f = function
  | VVal v -> VVal (f v)
  | VPos v -> VPos (f v)
  | VWidth v -> VWidth (f v)

module V = struct
  module I = struct
    type t = value [@@deriving ord]
    let pp formatter = function
      | VVal v -> Var.pp formatter v
      | VWidth v -> Format.fprintf formatter "%a@@width" Var.pp v
      | VPos v -> Format.fprintf formatter "%a@@pos" Var.pp v
    let show = SrkUtil.mk_show pp
    let equal x y = compare x y = 0
    let hash = function
      | VVal v -> Hashtbl.hash (Var.hash v, 0)
      | VPos v -> Hashtbl.hash (Var.hash v, 1)
      | VWidth v -> Hashtbl.hash (Var.hash v, 2)
  end
  include I



  let sym_to_var = Hashtbl.create 991
  let var_to_sym = ValueHT.create 991

  let typ v = tr_typ (Var.get_type (var_of_value v))

  let symbol_of var =
    if ValueHT.mem var_to_sym var then
      ValueHT.find var_to_sym var
    else begin
      let sym = Ctx.mk_symbol ~name:(show var) (typ var) in
      ValueHT.add var_to_sym var sym;
      Hashtbl.add sym_to_var sym var;
      sym
    end

  let of_symbol sym =
    if Hashtbl.mem sym_to_var sym then
      Some (Hashtbl.find sym_to_var sym)
    else
      None

  let is_global = Var.is_global % var_of_value


end

module K = struct
  include Transition.Make(Ctx)(V)

  let add x y =
    if is_zero x then y
    else if is_zero y then x
    else add x y

  let mul x y =
    if is_zero x || is_zero y then zero
    else if is_one x then y
    else if is_one y then x
    else mul x y
end

type ptr_term =
  { ptr_val : Ctx.arith_term;
    ptr_pos : Ctx.arith_term;
    ptr_width : Ctx.arith_term }

type term =
  | TInt of Ctx.arith_term
  | TPointer of ptr_term

let int_binop op left right =
  match op with
  | Add -> Ctx.mk_add [left; right]
  | Minus -> Ctx.mk_sub left right
  | Mult -> Ctx.mk_mul [left; right]
  | Div -> Ctx.mk_idiv left right
  | Mod -> Ctx.mk_mod left right
  | _ -> Ctx.mk_const (Ctx.mk_symbol ~name:"havoc" `TyInt)

let term_binop op left right = match left, op, right with
  | (TInt left, op, TInt right) ->
    TInt (int_binop op left right)
  | (TPointer ptr, Add, TInt offset)
  | (TInt offset, Add, TPointer ptr) ->
    let p =
      { ptr_val = int_binop Add ptr.ptr_val offset;
        ptr_pos = int_binop Add ptr.ptr_pos offset;
        ptr_width = ptr.ptr_width }
    in
    TPointer p
  | (TPointer ptr, Minus, TInt offset) ->
    let p =
      { ptr_val = int_binop Minus ptr.ptr_val offset;
        ptr_pos = int_binop Minus ptr.ptr_pos offset;
        ptr_width = ptr.ptr_width }
    in
    TPointer p
  | (TInt offset, Minus, TPointer ptr) ->
    let p =
      { ptr_val = int_binop Minus offset ptr.ptr_val;
        ptr_pos = int_binop Minus offset ptr.ptr_pos;
        ptr_width = ptr.ptr_width }
    in
    TPointer p
  | (TPointer left, op, TInt right) ->
    TInt (int_binop op left.ptr_val right)
  | (TInt left, op, TPointer right) ->
    TInt (int_binop op left right.ptr_val)
  | (TPointer left, op, TPointer right) ->
    TInt (int_binop op left.ptr_val right.ptr_val)

let typ_has_offsets typ = match resolve_type typ with
  | Pointer _ | Func _ | Dynamic -> true
  | _ -> false

let is_int_array typ = match resolve_type typ with
  | Array (Concrete (Int _), _) -> true
  | _ -> false

let nondet_const name typ = Ctx.mk_const (Ctx.mk_symbol ~name typ)


let rec tr_expr expr =
  let alg = function
    | OHavoc typ -> TInt (nondet_const "havoc" (tr_typ typ))
    | OConstant (CInt (k, _)) -> TInt (Ctx.mk_real (QQ.of_int k))
    | OConstant (CFloat (k, _)) -> TInt (Ctx.mk_real (QQ.of_float k))
    | OCast (_, expr) -> expr
    | OBinaryOp (a, op, b, _) -> term_binop op a b

    | OUnaryOp (Neg, TInt a, _) -> TInt (Ctx.mk_neg a)
    | OUnaryOp (Neg, TPointer a, _) -> TInt (Ctx.mk_neg a.ptr_val)
    | OAccessPath (Variable v) ->
      if typ_has_offsets (Var.get_type v) then
        TPointer { ptr_val = Ctx.mk_const (V.symbol_of (VVal v));
                   ptr_width = Ctx.mk_const (V.symbol_of (VWidth v));
                   ptr_pos = Ctx.mk_const (V.symbol_of (VPos v)) }
      else TInt (Ctx.mk_const (V.symbol_of (VVal v)))

    | OAddrOf _ ->
      (* Todo: width and pos aren't correct. *)
      TPointer { ptr_val = nondet_const "tr" `TyInt;
                 ptr_width = Ctx.mk_real QQ.one;
                 ptr_pos = Ctx.mk_real QQ.zero }

    (* No real translations for anything else -- just return a free var "tr"
       (which just acts like a havoc). *)
    | OUnaryOp (_, _, typ) -> TInt (nondet_const "tr" (tr_typ typ))
    | OBoolExpr b -> TInt (Ctx.mk_ite (tr_bexpr b) (Ctx.mk_real (QQ.of_int 1)) (Ctx.mk_real (QQ.of_int 0)))
      (*if (Bexpr.equal b Bexpr.ktrue) then TInt (Ctx.mk_real (QQ.of_int 1)) else TInt (Ctx.mk_real (QQ.of_int 0))*)
    | OAccessPath ap -> TInt (nondet_const "tr" (tr_typ (AP.get_type ap)))
    | OConstant _ -> TInt (nondet_const "tr" `TyInt)
  in
  Aexpr.fold alg expr
and  tr_expr_val expr = match tr_expr expr with
  | TInt x -> x
  | TPointer x -> x.ptr_val
and tr_bexpr bexpr =
  let alg = function
    | Core.OAnd (a, b) -> Ctx.mk_and [a; b]
    | Core.OOr (a, b) -> Ctx.mk_or [a; b]
    | Core.OAtom (pred, x, y) ->
      let x = tr_expr_val x in
      let y = tr_expr_val y in
      begin
        match pred with
        | Lt -> Ctx.mk_lt x y
        | Le -> Ctx.mk_leq x y
        | Eq -> Ctx.mk_eq x y
        | Ne -> Ctx.mk_not (Ctx.mk_eq x y)
      end
  in
  Bexpr.fold alg bexpr

(* Populate table mapping variables to the offsets of that variable that
   appear in the program.  Must be called before calling weight *)
let offset_table = Varinfo.HT.create 991
let get_offsets v =
  try Varinfo.HT.find offset_table v
  with Not_found -> Int.Set.empty

let populate_offset_table file =
  let add_offset (v, offset) =
    match offset with
    | OffsetUnknown -> ()
    | OffsetNone -> ()
    | OffsetFixed k ->
      Varinfo.HT.modify_def Int.Set.empty v (Int.Set.add k) offset_table
  in
  let rec aexpr e = match e with
    | Cast (_, e) | UnaryOp (_, e, _) -> aexpr e
    | BinaryOp (e1, _, e2, _) -> aexpr e1; aexpr e2
    | AddrOf a | AccessPath a -> ap a
    | BoolExpr b -> bexpr b
    | Havoc _ | Constant _ -> ()
  and ap a = match a with
    | Variable v -> add_offset v
    | Deref e -> aexpr e
  and bexpr b = match b with
    | And (b1, b2) | Or (b1, b2) -> bexpr b1; bexpr b2
    | Atom (_, e1, e2) -> aexpr e1; aexpr e2
  in
  file |> CfgIr.iter_defs (fun def ->
      match def.dkind with
      | Assign (v, e) -> add_offset v; aexpr e
      | Store (a, e) -> ap a; aexpr e;
      | Call (lhs, a, args) ->
        begin match lhs with
          | Some v -> add_offset v
          | None -> ();
        end;
        aexpr a;
        List.iter aexpr args;
      | Assume b -> bexpr b
      | Initial -> ()
      | Assert (b, _) -> bexpr b
      | AssertMemSafe (a, _) -> aexpr a
      | Return (Some a) -> aexpr a
      | Return None -> ()
      | Builtin (Alloc (v, a, _)) -> add_offset v; aexpr a
      | Builtin (Free a) -> aexpr a
      | Builtin (Fork (lhs, a, args)) ->
        begin match lhs with
          | Some v -> add_offset v
          | None -> ();
        end;
        aexpr a;
        List.iter aexpr args
      | Builtin (Acquire a) | Builtin (Release a) -> aexpr a
      | Builtin AtomicEnd | Builtin AtomicBegin | Builtin Exit -> ())

let rec record_assign (lhs : varinfo) loff rhs roff fields =
  fields |> List.map (fun { fityp; fioffset; _ } ->
      match resolve_type fityp with
      | Record { rfields; _ } ->
        record_assign lhs (loff+fioffset) rhs (roff+fioffset) rfields
      | Pointer _ | Func _ | Dynamic ->
        let lhs = (lhs, OffsetFixed (loff + fioffset)) in
        begin match tr_expr (AccessPath (Variable (rhs, OffsetFixed roff))) with
          | TPointer rhs ->
            BatList.reduce K.mul [
              K.assign (VVal lhs) rhs.ptr_val;
              K.assign (VPos lhs) rhs.ptr_pos;
              K.assign (VWidth lhs) rhs.ptr_width;
            ]
          | TInt tint -> begin
              BatList.reduce K.mul [
                K.assign (VVal lhs) tint;
                K.assign (VPos lhs) (nondet_const "type_err" `TyInt);
                K.assign (VWidth lhs) (nondet_const "type_err" `TyInt)
              ]
            end
        end
      | _ ->
        let lhs = (lhs, OffsetFixed (loff+fioffset)) in
        let rhs = tr_expr_val (AccessPath (Variable (rhs, OffsetFixed (fioffset+roff)))) in
        K.assign (VVal lhs) rhs)
  |> BatList.reduce K.mul

let weight def =
  let open K in
  match def.dkind with
  | Assume phi | Assert (phi, _) -> K.assume (tr_bexpr phi)
  | Assign (lhs, rhs) ->
    let lhs_typ = resolve_type (Var.get_type lhs) in
    let rhs_typ = resolve_type (Aexpr.get_type rhs) in
    begin match lhs_typ, rhs_typ with
      | Record { rfields; _ }, _ | _, Record { rfields; _ } ->
        let lhs, loff = match lhs with
          | (lhs, OffsetFixed k) -> (lhs, k)
          | (lhs, OffsetNone) -> (lhs, 0)
          | _ -> invalid_arg "Unsupported record assignment"
        in
        begin match rhs with
          | AccessPath (Variable (v, OffsetFixed k)) ->
            record_assign lhs loff v k rfields
          | AccessPath (Variable (v, OffsetNone)) ->
            record_assign lhs loff v 0 rfields
          | _ -> invalid_arg "Unsupported record assignment"
        end
      | Pointer _, _ | Func _, _ | Dynamic, _ ->
        begin match tr_expr rhs with
          | TPointer rhs ->
            BatList.reduce K.mul [
              K.assign (VVal lhs) rhs.ptr_val;
              K.assign (VPos lhs) rhs.ptr_pos;
              K.assign (VWidth lhs) rhs.ptr_width;
            ]
          | TInt tint -> begin
              (match Var.get_type lhs, rhs with
               | (_, Havoc _) | (Concrete Dynamic, _) -> ()
               | _ -> Log.errorf "Ill-typed pointer assignment: %a" Def.pp def);
              BatList.reduce K.mul [
                K.assign (VVal lhs) tint;
                K.assign (VPos lhs) (nondet_const "type_err" `TyInt);
                K.assign (VWidth lhs) (nondet_const "type_err" `TyInt)
              ]
            end
        end
      | _, _ -> K.assign (VVal lhs) (tr_expr_val rhs)
    end
  | Store (lhs, rhs) ->
    (* Havoc all the variables lhs could point to *)
    let open PointerAnalysis in
    let rhs_val =
      match tr_expr rhs with
      | TPointer rhs -> rhs.ptr_val
      | TInt tint -> tint
    in
    let add_target memloc tr = match memloc with
      | (MAddr v, offset) when is_int_array (Varinfo.get_type v) ->
        begin
          match offset with
          | OffsetUnknown ->
            Int.Set.fold (fun offset tr ->
                K.add tr (K.assign (VVal (v, OffsetFixed offset)) rhs_val))
              (get_offsets v)
              K.one (* weak update *)
            |> K.mul tr
          | _ ->
            K.mul tr (K.assign (VVal (v,offset)) rhs_val)
        end
      | (MAddr v, offset) ->
        if typ_has_offsets (Var.get_type (v,offset)) then begin
          BatList.reduce K.mul [
            tr;
            K.assign (VVal (v,offset)) (nondet_const "store" `TyInt);
            K.assign (VPos (v,offset)) (nondet_const "store" `TyInt);
            K.assign (VWidth (v,offset)) (nondet_const "store" `TyInt)
          ]
        end else begin
          K.mul tr (K.assign (VVal (v,offset)) (nondet_const "store" `TyInt))
        end
      | _, _ -> tr
    in
    MemLoc.Set.fold add_target (resolve_ap lhs) one
  | Builtin Exit -> zero
  | Builtin (Alloc (v, size, _)) ->
    BatList.reduce K.mul [
      K.assign (VVal v) (nondet_const "alloc" `TyInt);
      K.assign (VWidth v) (tr_expr_val size);
      K.assign (VPos v) (Ctx.mk_real QQ.zero)
    ]
  | Builtin AtomicBegin | Builtin AtomicEnd
  | Builtin (Acquire _) | Builtin (Release _)
  | Builtin (Free _)
  | Initial | AssertMemSafe (_, _) | Return None -> one
  | _ ->
    Log.errorf "No translation for definition: %a" Def.pp def;
    assert false

type 'a label = 'a TransitionSystem.label =
  | Weight of 'a
  | Call of int * int
[@@deriving ord]

type klabel = K.t label [@@deriving ord]

module TS = TransitionSystem.Make(Ctx)(V)(K)

module TransitionDom = struct
  type weight = K.t
  type abstract_weight = K.t
  let concretize x = x
  let abstract x = x
  let equal = K.equal
  let widen = K.widen
end


module MonotoneDom = struct
  open Syntax
  module Sign = Abstract.Sign
  module SymbolSet = Syntax.Symbol.Set
  type weight = K.t
  module VS = Linear.QQVectorSpace
  type abstract_weight = (symbol * symbol) list * Ctx.t Sign.t * VS.t
  let man = Polka.manager_alloc_equalities ()

  (* Map a list of transition symbols to an affine coordinate system
     for those symbols.  *)
  let coordinates_of tr_symbols =
    let enum =
      (List.fold_left (fun syms (x, x') ->
           SymbolSet.add x (SymbolSet.add x' syms))
         SymbolSet.empty
         tr_symbols
       |> SymbolSet.enum)
      /@ mk_const srk
    in
    BatEnum.push enum (mk_one srk);
    BatArray.of_enum enum

  let abstract tr =
    let tf = TF.linearize srk (K.to_transition_formula tr) in
    let coordinates = coordinates_of (TF.symbols tf) in
    let aff =
      Abstract.vanishing_space srk (TF.formula tf) coordinates
    in
    let signs =
      let deltas =
        List.fold_left (fun deltas (x, x') ->
            (mk_sub srk (mk_const srk x') (mk_const srk x))::deltas)
          []
          (TF.symbols tf)
      in
      let vars = BatArray.to_list coordinates in
      Sign.abstract srk (TF.formula tf) (vars@deltas)
    in
    (TF.symbols tf, signs, aff)

  let concretize (tr_symbols, signs, aff) =
    let transform =
      List.fold_left (fun assign (x,x') ->
          match V.of_symbol x with
          | Some v -> (v, mk_const srk x')::assign
          | None -> assert false)
        []
        tr_symbols
    in
    let coordinates = coordinates_of tr_symbols in
    let affine_guard =
      let zero = mk_zero srk in
      List.map
        (fun vec ->
          Linear.term_of_vec srk (fun dim -> coordinates.(dim)) vec
          |> mk_eq srk zero)
        aff
      |> mk_and srk
    in
    let guard =
      mk_and srk [Sign.formula_of srk signs;
                  affine_guard]
    in
    K.construct guard transform

  let equal (tr_symbols1, signs1, aff1) (tr_symbols2, signs2, aff2) =
    let pre_symbols tr_symbols =
      List.fold_left (fun pre (x,_) ->
          SymbolSet.add x pre)
        SymbolSet.empty
        tr_symbols
    in
    SymbolSet.equal (pre_symbols tr_symbols1) (pre_symbols tr_symbols2)
    && Abstract.Sign.equal signs1 signs2
    && VS.equal aff1 aff2

  let widen _ y = y
end

(* Weight-labeled graph module suitable for ocamlgraph *)
module TSG = struct
  type t = TS.t

  module V = struct
    include SrkUtil.Int
    type label = int
    let label x = x
    let create x = x
  end

  module E = struct
    type label = klabel
    type vertex = int
    type t = int * klabel * int [@@deriving ord]
    let src (x, _, _) = x
    let dst (_, _, x) = x
    let label (_, x, _) = x
    let create x y z = (x, y, z)
  end

  let iter_edges_e = WG.iter_edges
  let iter_vertex = WG.iter_vertex
  let iter_succ f tg v =
    WG.U.iter_succ f (WG.forget_weights tg) v
  let fold_pred_e = WG.fold_pred_e
end

module TSDisplay = ExtGraph.Display.MakeLabeled
    (TSG)
    (SrkUtil.Int)
    (struct
      type t = klabel
      let pp formatter w = match w with
        | Weight w -> K.pp formatter w
        | Call (s,t) -> Format.fprintf formatter "call(%d, %d)" s t
    end)

module SA = Abstract.MakeAbstractRSY(Ctx)

(*****************************************************************************
    McMillan's algorithm [McMillan '06] for lazy abstraction with refinement.
*******************************************************************************)

let force_covering = false 
let enable_pruning = false

let enable_symb_exec = false

exception Mexception of string 
module ARR = Batteries.DynArray 

(* Defines an Abstract Reachability Tree context. *)
type art_context = {
  graph : TS.t; (* Underlying control-flow graph. *)
  root: int; (* Root of the underlying CFG. *)
  children : (int ARR.t) ARR.t;  (* Adjacency list representation of ART. *)
  parents : (int ARR.t) ;
  maps_to: (int ARR.t) ; (* F(v): decide which CFG vertex a tree vertex maps to. *)
  vertex_labels : ((Ctx.t Syntax.formula) ARR.t);
  assertion_phi : Ctx.formula ; 
  neg_assertion_phi : Ctx.formula ; 
  is_leaf : (bool ARR.t) ;  (** NEW! *)
  is_covered : (bool ARR.t) ;  (** NEW! *)
  counter : int ref;
  covers: (int * int) list; (* TODO: make this data structure more efficient. :-) *) 
  error_loc : int ; 
  model : Ctx.t Interpretation.interpretation option 
}

type art_path = int list 

type cfg_t = K.t label WG.t


let mk_true () = Syntax.mk_true Ctx.context
let mk_false () = Syntax.mk_false Ctx.context 

(* Creates a new ART node. *)
let mk_query ts entry = TS.mk_query ts entry (if !monotone then (module MonotoneDom) else (module TransitionDom))

let get_path v art =
   let rec aux v art = if v == -1 then [] else v :: (aux (ARR.get art.parents v) art) in 
   List.rev (aux v art)

let mypp_weights s l = List.iteri (fun i f -> logf ~level:`always "%s(%i): \n%a" s i K.pp f) l
let mypp_formula s l = 
  List.iteri (fun i f -> logf ~level:`always "%s(%i): \n%a" s i (Syntax.pp_expr_unnumbered Ctx.context) @@ f) l

let print_path (t:art_context) p = 
  let l = List.length p in 
  Printf.printf "(%d) tree path: " l;
  List.iteri (fun i x -> 
    if i < l - 1 then Printf.printf "%d -> " x else Printf.printf "%d\n" x) p ;
  Printf.printf "    CFG path: ";
  List.iteri (fun i x ->
    if i < l - 1 then Printf.printf "%d -> " @@ ARR.get t.maps_to x else Printf.printf "%d\n" @@ ARR.get t.maps_to x) p  


  (* find loop headers and insert assume for loop invariant . *)
let decorate_transition_system predicates ts entry =
  let module AbsDom =
    TS.ProductIncr
      (TS.ProductIncr(TS.LiftIncr(SA.Sign))(TS.LiftIncr(SA.AffineRelation)))
      (TS.LiftIncr(SA.PredicateAbs(struct let universe = predicates end)))
  in
  let inv = TS.forward_invariants (module AbsDom) ts entry in
  let member varset sym =
    match V.of_symbol sym with
    | Some v -> TS.VarSet.mem v varset
    | None -> false
  in
  TS.loop_headers_live ts
  |> List.fold_left (fun ts (v, live) ->
      let fresh_id = (Def.mk (Assume Bexpr.ktrue)).did in
      let invariant = AbsDom.formula_of (AbsDom.exists (member live) (inv v)) in
      logf "Found invariant at %d:@;%a" v (Syntax.Formula.pp srk) invariant;
      WG.split_vertex ts v (Weight (K.assume invariant)) fresh_id)
    ts

let make_transition_system rg =
  let call_edge block =
    Call ((RG.block_entry rg block).did, (RG.block_exit rg block).did)
  in
  let assertions = ref SrkUtil.Int.Map.empty in
  let add_assert v e =
    assertions := SrkUtil.Int.Map.add v e (!assertions)
  in
  let ts =
    BatEnum.fold (fun ts (block, graph) ->
        let tg =
          RG.G.fold_vertex (fun def tg ->
              let tg = WG.add_vertex tg def.did in
              let label =
                match def.dkind with
                | Call (None, AddrOf (Variable (func, OffsetNone)), []) ->
                  call_edge func
                | Assert (phi, msg) ->
                  let condition = tr_bexpr phi in
                  add_assert def.did (condition, Def.get_location def, msg);
                  Weight (K.assume condition)
                | AssertMemSafe (expr, msg) ->
                  let condition =
                    match tr_expr expr with
                    | TInt _ -> Ctx.mk_false
                    | TPointer p ->
                      Ctx.mk_and [
                        Ctx.mk_leq (Ctx.mk_real QQ.zero) p.ptr_pos;
                        Ctx.mk_lt p.ptr_pos p.ptr_width
                      ]
                  in
                  add_assert def.did (condition, Def.get_location def, msg);
                  Weight (K.assume condition)
                | _ -> Weight (weight def)
              in
              RG.G.fold_succ
                (fun succ tg -> WG.add_edge tg def.did label succ.did)
                graph def
                tg)
            graph
            TS.empty
        in
        let predicates =
          if !forward_pred_abs then
            RG.G.fold_vertex (fun def predicates ->
                match def.dkind  with
                | Assume phi when Bexpr.equal phi Bexpr.ktrue ->
                  predicates
                | Assert (phi, _) | Assume phi ->
                  Syntax.Expr.Set.add (tr_bexpr phi) predicates
                | _ ->
                  predicates)
              graph
              Syntax.Expr.Set.empty
            |> Syntax.Expr.Set.enum
            |> BatList.of_enum
          else
            []
        in

        let entry = (RG.block_entry rg block).did in
        let exit = (RG.block_exit rg block).did in
        let point_of_interest v =
          v = entry || v = exit || SrkUtil.Int.Map.mem v (!assertions)
        in
        let tg = TS.simplify point_of_interest tg in
        let tg = TS.remove_temporaries tg in
        let tg =
          if !forward_inv_gen then let _ = Printf.printf "forward inv gen...\n" in
            Log.phase "Forward invariant generation"
              (decorate_transition_system predicates tg) entry
          else
            tg
        in
        WG.fold_edges (fun (src, label, tgt) ts ->
            match label with
            | Weight w -> WG.add_edge ts src (Weight w) tgt
            | Call (s,t) -> WG.add_edge ts src (Call (s,t)) tgt)
          tg
          (WG.fold_vertex (fun v ts ->
               WG.add_vertex ts v)
              tg
              ts))
      TS.empty
      (RG.bodies rg)
  in
  (ts, !assertions)


let make_ts_assertions_unreachable (ts : cfg_t) assertions = 
  let largest = ref (WG.fold_vertex (fun v max -> if v > max then v else max) ts 0) in 
  let pts = ref ts in 
  let new_vertices = ref [] in 
  assertions |> SrkUtil.Int.Map.iter (
    fun v (phi, _, _) -> 
      (* For each assertion, create new vertex after the assertion state 
       * with edge into the vertex being the negated condition. *)
      let u = !largest + 1 in 
      largest := (!largest) + 1; 
      pts := WG.add_vertex !pts u ;
      pts := WG.add_edge !pts v (Weight (K.assume (Ctx.mk_not phi))) u ;
      let s = Printf.sprintf " Adding assertion node %d -> %d for label " v u in 
      mypp_formula s [ Ctx.mk_not phi ] ; 
      new_vertices := u :: !new_vertices 
  ); !pts, !new_vertices
  

module IntMap = BatMap.Make(Int)

type mtree = {
  graph : cfg_t;
  entry : int;
  cfg_vertex : int ARR.t ;
  parents : int ARR.t ; 
  model : Ctx.t Interpretation.interpretation IntMap.t ;
}

module DQ = BatDeque
type idq_t = int BatDeque.t 


type ltree = {
  graph : cfg_t;
  entry : int;
  cfg_vertex : int ARR.t;
  parents : int ARR.t;
  labels : (Ctx.t Syntax.formula) ARR.t;
  covers : int IntMap.t ref;       
  (* also maintain reverse map for each y, storing (x, y) that are in cover. *)
  reverse_covers : (int list) IntMap.t ref;
  children : int list ARR.t;
  precedent_nodes : (int list) IntMap.t ref;
  models : (Ctx.t Interpretation.interpretation) IntMap.t
}


(* worklist (breadth-first) version of McMillan's algorithm. *)
let mc_exec (mode: int) (ts : cfg_t) (entry : int) (err_loc : int) = 
  (*  [i %>> q]: add i to front of worklist q  *)
  let (%>>)  (i : int) (q : idq_t) = DQ.cons i q in 
  (*  [t %^ i]: get parent of node i in tree t.  *)
  let (%^) (t : ltree) (i : int) = ARR.get t.parents i in
  (*  [t %-> i]: get CFG vertex mapped by node i in tree t. *)
  let (%->) (t : ltree) (i : int) = ARR.get t.cfg_vertex i in
  (* [ew t u v] returns the CFG edge weight of edge (u, v) for vertices u, v in the CFG. *) 
  let ew (t : ltree) u v = match WG.edge_weight t.graph u v with  Weight w -> w  | Call _ -> failwith "call unimplemented" in   
  (* [t %-*> u] returns a list of edge weights that form the path condition from root of t to tree node u.  *)
  let rec (%-*>) (t: ltree) (u : int) = 
    if u == 0 then [ ]
    else let rec (%<*-) (t : ltree) (u : int) =
     match t %^ u with 
      | 0 -> [ ew t (t %-> 0) (t %-> u) ]  
      | v -> ew t (t %-> v) (t %-> u) :: (t %<*- v) in 
      let ews = List.rev (t %<*- u) in
      mypp_weights "edge weights list: " ews; ews in
  (* [tree_path t u] returns list of tree nodes that form the corrsp. tree path from root of t to tree node u *)
  let tree_path t u = 
    let rec tree_path_rev t u = 
      match u with 
      | 0 -> [ 0 ]
      | x -> x :: (tree_path_rev t (t %^ u)) 
    in List.rev @@ tree_path_rev t u
  in 
  (* [children t v] returns children of tree node v in tree t. *)
  let children (t : ltree) v = 
    ARR.get t.children v in 
  (* [descendants t v] returns descendants of tree node v in tree t in DFS order. *)
  let rec descendants (t : ltree) v = 
    let v_children = children t v in 
    Printf.printf " descendants v : %d (" v;
    List.iter (fun x -> Printf.printf " %d " x) v_children;
    Printf.printf "\n";
    v :: (List.fold_left (fun l ch -> (descendants t ch) @ l) [] v_children)
  in
  (* [label t v] returns the node label of tree node v in tree t. *)
  let label (t : ltree) v = ARR.get t.labels v in
  (* [get_precedent_nodes t v] retrieves a sequence of precedent nodes of tree node vin preorder in tree t. *)
  let get_precedent_nodes t v = 
    (* The list is stored in tree structure in reverse, so we reverse it to get preorder. *)
    let cfg_vertex = t %-> v in 
    let postordered_precedents = IntMap.find_default [] cfg_vertex !(t.precedent_nodes) in 
    Printf.printf "    postordered_precedents of %d: " v;List.iter (fun x -> Printf.printf " %d " x) postordered_precedents; Printf.printf "\n";
    List.rev postordered_precedents 
  in
  (* Interpolate the path (entry) -> (t %-> src) -> (sink). If fail, then get model. *)
  let interpolate_or_get_model (t : ltree) (src : int) (sink : int) = 
    let query = mk_query t.graph (t %-> src) in 
    let post_path_summary = TS.path_weight query sink |> K.guard in
    let initial_path_weights = t %-*> src in 
    K.interpolate_or_concrete_model initial_path_weights post_path_summary 
  in
  let get_abstract_model ?(solver=Smt.mk_solver Ctx.context) 
        pre_formula post_pre_symbols 
        (src : int) (sink : int) (graph : cfg_t) = 
    Printf.printf "   get_abstract_model between src = %d and sink = %d\n" src sink ;
    let query = mk_query graph src in 
    let path = TS.path_weight query sink in 
    let pre_formula_symbols = Syntax.symbols pre_formula |> MonotoneDom.SymbolSet.elements in 
    match Smt.get_concrete_model Ctx.context ~solver:(solver) pre_formula_symbols pre_formula with 
      | `Sat itp ->
        logf ~level:`always "Interpretation: %a\n" Interpretation.pp itp ;
        let m = Interpretation.enum itp in 
        let itp' = BatEnum.fold (fun itp' (symb, v) -> 
          let pre_symb = List.assoc symb post_pre_symbols in 
          Interpretation.add pre_symb v itp' ) (Interpretation.empty Ctx.context) m in 
          logf ~level:`always "Interpretation': %a\n" Interpretation.pp itp' ;
          K.get_post_model itp' path               
      | `Unknown -> None 
      | `Unsat -> None
  in 
  (**
   * Set up data structures used by the algorithm: worklist, 
   * vtxcnt (keeps track of largest unused vertex number in tree), 
   * ptt is a pointer to the reachability tree.
   *)
 (* mode: 1 -> concolic McMillan; 0 -> plain McMillan *)
  let get_initial_abstract_model ?(solver=Smt.mk_solver Ctx.context) (src : int) (sink : int) (graph : cfg_t) = 
    Printf.printf "   get_abstract_model between src = %d and sink = %d\n" src sink ;
    let query = mk_query graph src in 
    let path = TS.path_weight query sink in 
    let path_condition = K.guard path in 
    let path_condition_symbols = Syntax.symbols path_condition |> MonotoneDom.SymbolSet.elements in 
      Smt.get_concrete_model Ctx.context ~solver:(solver) path_condition_symbols path_condition 
  in 
  let worklist = (* worklist for McMillan phase *)
    match mode with 
    | 0 -> ref (0 %>> DQ.empty) 
    | 1 -> ref DQ.empty 
    | _ -> failwith "" in 
  let execlist = (* worklist for concolic phase *)
    match mode with 
    | 0 -> ref DQ.empty 
    | 1 -> ref (0 %>> DQ.empty)
    | _ -> failwith "" in 
  let vtxcnt = ref 1 in 
  let ptt = ref { 
    graph = ts; 
    entry = entry; 
    cfg_vertex = ARR.singleton entry ; 
    parents = ARR.singleton (-1) ;
    labels = ARR.singleton (mk_true ());
    covers = ref IntMap.empty;
    reverse_covers = ref IntMap.empty; (* reverse_covers[y] returns all x such that (x,y) is in the cover. *)
    children = ARR.singleton [] ;
    precedent_nodes = ref IntMap.empty; (* precedent_nodes[v] stores all tree nodes mapping to CFG vertex v. Used in mc_close. *)
    models = IntMap.empty
    } in
  let add_tree_vertex ?model v p worklist = (* Add new tree leaf mapping to CFG vertex v and with parent tree node p. *)
    Printf.printf "   add_tree_vertex (CFG vertex = %d, parent = %d, node=%d)\n" v p !vtxcnt;
    ARR.add !ptt.cfg_vertex v;
    ARR.add !ptt.parents p;
    ARR.add !ptt.labels (mk_true ());
    ARR.add !ptt.children [];
    ARR.set !ptt.children p (!vtxcnt :: (children !(ptt) p)); (* set children of parent to be !vtxcnt :: children. *)
    (* Add v to precedent_nodes. *)
    let precedent_nodes = IntMap.find_default [] v !(!ptt.precedent_nodes) in 
    !ptt.precedent_nodes := IntMap.add v (!vtxcnt :: precedent_nodes) !(!ptt.precedent_nodes);
    (* Push it onto the worklist and increment vertex counter. *)
    match model with 
    | Some model -> 
      Printf.printf "     putting %d (will be assigned tree node %d) on execlist with model...\n" v !vtxcnt;
      execlist := !vtxcnt %>> !execlist;
      ptt := {!ptt with models = IntMap.add !vtxcnt model !ptt.models};
      vtxcnt := !vtxcnt + 1
    | None -> worklist := !vtxcnt %>> !worklist; 
    vtxcnt := !vtxcnt + 1
  in let rec leaves v = (* return leaves of subtree rooted at v. *)
    let chs = children !ptt v in 
    if List.length chs == 0 then [ v ]
    else 
      List.fold_left (fun child_leaves ch -> leaves ch @ child_leaves) [] chs
  in let mc_expand v = 
    (* expand leaf node v. If in concolic mode, 
        for every out-neighbor y of v, first try deriving a post-state model of v-> y, if successful, put it
          on the concolic execution worklist. Otherwise, it is a frontier node, and put it on the 
          mcmillan worklist. *)
          Printf.printf "   +---- expanding node %d (%d)\n" v (!ptt %-> v);
    let vg = !(ptt) %-> v in 
    if mode = 0 then 
      WG.iter_succ_e (fun (_, _, y) ->  
        add_tree_vertex y v worklist;
        ) !ptt.graph vg  
    else begin 
      Printf.printf "               visiting its out neighbors...\n";
      begin match IntMap.find_opt v !ptt.models with 
      | Some m ->
        WG.iter_succ_e (fun (_, weight, y) -> 
          let weight = match weight with Weight w -> w | Call _ -> failwith "cannot handle call" in 
          begin match K.get_post_model m weight with 
          | Some y_model ->   
                Printf.printf " ----- post model found for vertex %d\n" y;
                add_tree_vertex ~model:y_model y v execlist 
          | None ->
             Printf.printf "  frontier node: %d\n" y; (* issue: y is a CFG vertex, not an ART node. *)
             add_tree_vertex y v worklist 
          end
        ) !ptt.graph vg
      | None -> failwith @@ Printf.sprintf "trying to expand from node %d(%d) without labelled model " v (!ptt %-> v)
        end
      end
  in let mc_refine_with_interpolants v path interpolants = 
    Printf.printf "  refine: interpolant sequence: ------------------------------\n";
    mypp_formula "" interpolants;
    Printf.printf "--------------------------------------------------------------\n";
    (* refine the label of each tree node u along path from tree root to v. *)
    (*Printf.printf "length of interpolants: %d\n" (List.length interpolants);
    Printf.printf "length of path condition: %d\n" (List.length path_condition);*)
    List.iter2 (fun u interpolant -> 
      let u_label = ARR.get !ptt.labels u in 
      let u_label' = Syntax.mk_and Ctx.context [ u_label ; interpolant ] in 
      ARR.set !ptt.labels u u_label';
      (* remove ( * -> u) in covering relation. *)
      begin match IntMap.find_opt u !(!ptt.reverse_covers) with 
      | None -> () 
      | Some l ->
        (*printf "    refine: removing covers: "; List.iter (fun x -> Printf.printf " (%d->%d)" x u) l; Printf.printf "\n";*)
        let u_coverers  = List.fold_left (fun coverers x -> 
          (* test if label(x) --> new label(u)*)
          let x_label = ARR.get !ptt.labels x in 
          let u_label = ARR.get !ptt.labels u in
          begin match Smt.entails Ctx.context (x_label) (u_label) with
          | `No | `Unknown -> 
            (* remove (x, u) from covering. *)
            Printf.printf "   refine: removing cover (%d->%d)\n" x u;
            !ptt.covers := IntMap.remove x !(!ptt.covers);
            (* add x's subtree leaves back to the worklist. *)
            let x_leaves = leaves x in 
              List.iter (fun x_leaf -> 
                Printf.printf "         refine: adding %d back to worklist \n" x_leaf;
                worklist := x_leaf %>> !worklist) x_leaves;
            l
          | `Yes ->
            Printf.printf "    refine: cover (x %d-> u %d) still holds\n" x u;
            mypp_formula " x label: " [x_label];
            mypp_formula " u label: " [u_label];
           x :: coverers (* unchanged. *) 
          end
          ) [] l in 
            !ptt.reverse_covers := IntMap.add u u_coverers !(!ptt.reverse_covers)
      end
     ) path (interpolants @ [Syntax.mk_false Ctx.context]) in
  let mc_refine v = (* refine path to node v. Returns false if unable to refine. *)
    let path_condition = !ptt %-*> v in 
    let path = tree_path !(ptt) v in 
      Printf.printf "  refine: path condition: ------------------------------\n";
      mypp_weights "" path_condition;
    if mode = 0 then begin 
    match K.interpolate path_condition (Ctx.mk_false) with 
     | `Invalid | `Unknown -> 
      Printf.printf " *********************** REFINEMENT FAILED *************************\n"; false 
     | `Valid interpolants ->
       mc_refine_with_interpolants v path interpolants;
       true  
     end else begin 
      match interpolate_or_get_model !ptt v err_loc with 
      `Invalid v_model -> 
        Printf.printf "Unable to refine but got model\n";
        ptt := {!ptt with models = IntMap.add v v_model !ptt.models }; false 
      | `Unknown -> failwith ""
      | `Valid interpolants -> 
        mc_refine_with_interpolants v path interpolants; true 
     end
  in let mc_cover v w = (* Adds (v -> w) to covering relation if possible and returns true, false otherwise. *)
    let v_label = ARR.get !ptt.labels v in 
    let w_label = ARR.get !ptt.labels w in
    match Smt.entails Ctx.context v_label w_label with 
    | `Yes -> 
      Printf.printf "   cover success (v=%d, w=%d). \n" v w;
      mypp_formula "        v label " [v_label];
      mypp_formula "        w label "  [w_label];
      let reverse_covers_w = IntMap.find_default [] w !(!ptt.reverse_covers) in 
        !ptt.covers := IntMap.add v w !(!ptt.covers);
        !ptt.reverse_covers := IntMap.add w (v :: reverse_covers_w) !(!ptt.reverse_covers);
        true
    | `No | `Unknown -> false    
  in let mc_close (v : int) = (* Visits precedents of v in tree and attempts to derive covering relations[]. *)
    let precedents = get_precedent_nodes !ptt v in
   (* Printf.printf "precedents of node %d : " v; List.iter (fun x -> Printf.printf " %d " x) precedents ; Printf.printf "\n";*)
    (* Fold from first node in preorder to the right. If covering succeeds, do not continue covering. *) 
    let result = List.fold_right (fun w status ->
      if status || w == v || w > v (* preorder constraint *) then status
      else begin 
        let cover_success = mc_cover v w in 
        if cover_success then begin
          (* remove, for each descendant of v, nodes that are sinks of covers. *)
          let v_descendants = descendants !ptt v in 
            List.iter (fun y -> 
              (* Find relations (x,y) in covering relation. *)
              if y <> v then 
              begin 
                let xs = IntMap.find_default [] y !(!ptt.reverse_covers) in 
                (* Iterate through and remove pairs (x, y) from covering relation. *)
                (* Step 1: Remove (x |-> y) from !ptt.covers. *)
                List.iter (fun x -> !ptt.covers := IntMap.remove x !(!ptt.covers)) xs;
                (* Step 2: Remove (y |-> xs) from !pthit.reverse_covers. *)
                !ptt.reverse_covers := IntMap.remove y !(!ptt.reverse_covers)
              end) v_descendants
        end; cover_success
      end) precedents false in result 
  in let rec mc_is_covered v = (* Checks if tree node v is covered. It is covered if its ancestors or it is in covering relation. *)
    match IntMap.find_opt v !(!ptt.covers) with 
    | None -> 
      if v == 0 then false
      else mc_is_covered ((!ptt) %^ v)
    | Some u -> 
      Printf.printf "  | covered by %d\n" u;
      true 
  in let tree_printer_get_name i = 
    match IntMap.find_opt i !(!ptt.covers) with 
    | None ->  Printf.sprintf "%d(%d)" i (!ptt %-> i)
    | Some j -> Printf.sprintf "[%d(%d)]->%d" i (!ptt%->i) j
  in 
  let plain () = 
    let continue = ref true in begin
      while DQ.size !worklist > 0 && !continue do 
        begin match DQ.front !worklist with (* use DQ.rear if want BFS *) 
        | Some (u, w) (* (w, u) if use DQ.front *) ->          Printf.printf " +----------------- ART ----------------+\n";
          let string_of_art = Tree_printer.to_string ~line_prefix:"* " ~get_name:tree_printer_get_name ~get_children:(children !ptt) 0
            in Printf.printf "%s" string_of_art; 
          Printf.printf " +----------------- ART ----------------+\n";
          Printf.printf " visit %d\n" u;
          worklist := w;
          (* Fetched tree node u from work list. First attempt to close it. *)
          if not (mc_is_covered u) then begin
            Printf.printf " uncovered. try close\n";
            begin match mc_close u with 
              | true -> (* Close succeeded. No need to further explore it. *)
                Printf.printf "Close succeeded.\n"; ()
              | false -> (* u is uncovered. *)
                if ((!ptt) %-> u) == err_loc then 
                  begin 
                    continue := mc_refine u;
                    if !continue == false then 
                      failwith " UNSAFE. EXIT\n";
                    Printf.printf " refinement result: %b\n" (!continue);
                  (* for every node along path of refinement try close *)
                  let path = tree_path !ptt u in 
                    List.iter (fun x -> let _ = mc_close x in ()) path 
                  end 
                else begin 
                  Printf.printf " expanding...\n";
                  mc_expand u
                end
            end end
          else Printf.printf "  | covered \n"
          | None -> failwith ""
          end
      done;
      Printf.printf " +++++++++++++++++++++++++++++++++ Final ART +++++++++++++++++++++++++++++ \n";
      let string_of_art = Tree_printer.to_string ~line_prefix:"* " ~get_name:tree_printer_get_name ~get_children:(children !ptt) 0
        in Printf.printf "%s" string_of_art
    end
    in let symb_test () = 
        let pre_formula = [ew !ptt 2 3; ew !ptt 3 4; ew !ptt 4 5; ew !ptt 5 6; ew !ptt 6 7] in
        let _ = mypp_weights "pre_weights: " pre_formula in 
        match K.interpolate_or_concrete_model pre_formula (Ctx.mk_false) with 
        | `Invalid m -> 
          Printf.printf " --- SAT, model is \n";
          Interpretation.pp Format.std_formatter m 
        | `Unknown -> Printf.printf " --- Unknown \n"
        | `Valid itp -> 
          Printf.printf " --- Valid interpolants\n"
       (*
        let pre_formula = List.fold_right (fun weight prod -> K.mul weight prod) pre_formula K.one in 
        let _ = mypp_weights "pre_weight mul: " [pre_formula] in 
        let pre_formula_tf = K.to_transition_formula pre_formula in 

        let pre_formula = pre_formula_tf |> TransitionFormula.formula in 
        let pre_post_symbols = pre_formula_tf |> TransitionFormula.symbols in 
        let post_pre_symbols = List.fold_left (fun post_pre_symbols (x, y) -> 
          Printf.printf "post symb: %s --> pre symb: %s\n" (Syntax.show_symbol Ctx.context y) (Syntax.show_symbol Ctx.context x);
        (y, x) :: post_pre_symbols) [] pre_post_symbols in
        mypp_formula "pre_formula: " [pre_formula];
        match get_abstract_model pre_formula post_pre_symbols 8 err_loc ts with 
        | Some itp ->
          logf ~level:`always "Interpretation: %a\n" Interpretation.pp itp ;
          
        | _ -> failwith "no model found" *)
    in let symb () = 
      let continue = ref true in 
      while !continue && (DQ.size !worklist > 0 || DQ.size !execlist > 0) do
        Printf.printf " continuing...\n";
        if DQ.size !execlist > 0 then begin 
          match DQ.front !execlist with 
          | Some (u, w) -> 
          Printf.printf " +----------------- ART ----------------+\n";
          let string_of_art = Tree_printer.to_string ~line_prefix:"* " ~get_name:tree_printer_get_name ~get_children:(children !ptt) 0
            in Printf.printf "%s" string_of_art; 
          Printf.printf " +----------------- ART ----------------+\n";
          Printf.printf " visit %d (%d)\n" u (!ptt %-> u);
            if (!ptt %-> u) = err_loc then 
              failwith "Concolic execution error loc reached"; 
            execlist := w;
            Printf.printf "model of %d: \n" u;
            Interpretation.pp Format.std_formatter (IntMap.find u !ptt.models) ;
            mc_expand u ;
          | None -> failwith "" (* cannot happen *)
        end else begin 
          match DQ.front !worklist with 
          | Some (u, w) -> 
         Printf.printf " +----------------- ART ----------------+\n";
          let string_of_art = Tree_printer.to_string ~line_prefix:"* " ~get_name:tree_printer_get_name ~get_children:(children !ptt) 0
           in Printf.printf "%s" string_of_art; 
          Printf.printf " +----------------- ART ----------------+\n";
          Printf.printf " visit frontier %d (%d)\n" u (!ptt %-> u);
          worklist := w;
          (* Fetched tree node u from work list. First attempt to close it. *)
          if not (mc_is_covered u) then begin
            Printf.printf " uncovered. try close\n";
            begin match mc_close u with 
              | true -> (* Close succeeded. No need to further explore it. *)
                Printf.printf "Close succeeded.\n"; ()
              | false -> (* u is uncovered. *)
                if true (* ((!ptt) %-> u) == err_loc *) then 
                  begin 
                    continue := mc_refine u;
                    if (!continue) == false then 
                      begin 
                        execlist := u %>> !execlist  (* put u onto execlist since it now has a model. *)
                      end;
                    continue := true;
                  (* for every node along path of refinement try close *)
                  let path = tree_path !ptt u in 
                    List.iter (fun x -> let _ = mc_close x in ()) path 
                  end 
                else begin 
                  Printf.printf " expanding...\n";
                  mc_expand u
                end
            end end
          | None -> failwith "" (* cannot happen *)
        end 
      done
    in 
      match mode with 
      | 0 -> Printf.printf "executing plain mcmillan\n..."; plain ()
      | 1 -> 
        Printf.printf "getting initial abstract model...\n";
        begin match get_initial_abstract_model entry err_loc ts with 
        | `Sat m -> 
          Printf.printf "good. continuing...\n";
          ptt := {!ptt with models = IntMap.add 0 m !ptt.models}; 
          symb ()
        | _ -> 
          Printf.printf "Proven safe by path summary.\n"
        end
      | 2 -> Printf.printf "executing symbolic mcmillan TEST...\n"; symb_test ()
      | _ -> failwith ""



open Smt 
(* concolic execution procedure *)
let sexec (ts : cfg_t) (entry : int) (err_loc : int) = 
  let (%>>) (i : int)  (q : idq_t) = DQ.cons i q in 
  let (%^) (t : mtree) (i : int) = ARR.get t.parents i in
  let (%->) (t : mtree) (i : int) = ARR.get t.cfg_vertex i in 
  let ew (t : mtree) u v = match WG.edge_weight t.graph u v with  Weight w -> w  | Call _ -> failwith "call unimplemented" in   
  (*let (%<<) (q : idq_t) (i : int) = DQ.snoc q i in *)
  let rec (%-*>) (t: mtree) (u : int) = 
    if u == 0 then [ ]
    else let rec (%<*-) (t : mtree) (u : int) =
     match t %^ u with 
      | 0 -> [ ew t (t %-> 0) (t %-> u) ] 
      | v -> ew t (t %-> v) (t %-> u) :: (t %<*- v) in 
      List.rev (t %<*- u) in
  let get_out_neighbors (g : cfg_t) (u : int) = 
    WG.fold_succ_e (fun (x, weight, y) l -> 
      if x <> u then failwith "will not happen" 
      else (weight, y) :: l) g u [] in 
  let get_initial_abstract_model ?(solver=Smt.mk_solver Ctx.context) (src : int) (sink : int) (graph : cfg_t) = 
    Printf.printf "   get_abstract_model between src = %d and sink = %d\n" src sink ;
    let query = mk_query graph src in 
    let path = TS.path_weight query sink in 
    let path_condition = K.guard path in 
    (*Wedge.is_sat_model Ctx.context path_condition *)
    let path_condition_symbols = Syntax.symbols path_condition |> MonotoneDom.SymbolSet.elements in 
      Smt.get_concrete_model Ctx.context ~solver:(solver) path_condition_symbols path_condition 
  in 
  let get_abstract_model ?(solver=Smt.mk_solver Ctx.context) pre_condition (src : int) (sink : int) (graph : cfg_t) = 
    Printf.printf "   get_abstract_model between src = %d and sink = %d\n" src sink ;
    let query = mk_query graph src in 
    let post_condition = TS.path_weight query sink |> K.guard |> K.assume in 
    let condition = K.mul pre_condition post_condition in 
    let condition_tf = K.to_transition_formula condition in 
    let post_pre_symbols = List.fold_right (fun (x, y) l -> (y, x) :: l) (TransitionFormula.symbols condition_tf) [] in 
    let condition_formula = TransitionFormula.formula condition_tf in 
    let condition_symbols = Syntax.symbols condition_formula |> MonotoneDom.SymbolSet.elements in 
    match Smt.get_concrete_model Ctx.context ~solver:(solver) condition_symbols condition_formula with 
      | `Sat itp ->
        logf ~level:`always "Interpretation: %a\n" Interpretation.pp itp ;
        let m = Interpretation.enum itp in 
        let itp' = BatEnum.fold (fun itp' (symb, v) -> 
          let pre_symb = List.assoc symb post_pre_symbols in 
          Interpretation.add pre_symb v itp' ) (Interpretation.empty Ctx.context) m in 
          logf ~level:`always "InterpretationPRIME: %a\n" Interpretation.pp itp'; 
          Some itp'
      | `Unknown -> None 
      | `Unsat -> None
  in
  Printf.printf "sexec: starting symbolic execution entry=%d err_loc=%d\n" entry err_loc;
  let solver = Smt.mk_solver Ctx.context in 
  begin match get_initial_abstract_model ~solver:(solver) entry  err_loc ts with 
  | `Sat initial_model ->
      let worklist = ref (0 %>> DQ.empty) in 
      let vtxcnt = ref 1 in 
      let ptt = ref { 
        graph = ts; 
        entry = entry; 
        cfg_vertex = ARR.singleton entry ; 
        parents = ARR.singleton (-1) ;
        model  = IntMap.singleton 0 initial_model } in
      let unsafe = ref false in 
      Printf.printf "sexec: %d -> %d |- Sat - Assertion might be unsafe, starting symbexec using abstract model. \n" entry err_loc;
      while (DQ.size !worklist > 0) (*&& not !unsafe*) do 
        if !unsafe then begin
          Printf.printf "     *** ASSERTION UNSAFE *** \n"; 
          exit 1 end
        else begin 
          begin match DQ.front !worklist with 
          | Some (tx, w') -> 
            let x = ARR.get !(ptt).cfg_vertex tx in 
            worklist := w'; (* Pop x off front of list. *)
           (* Printf.printf "sexec: exploring tree node %d (cfg node %d) to err_loc %d\n" tx x err_loc;*)
            if x == err_loc then begin 
              unsafe := true;
              Printf.printf " sexec: err loc reached! Assertion unsafe\n" 
            end else 
              let x_model = IntMap.find tx !(ptt).model in 
              let x_out_neighbors = get_out_neighbors !(ptt).graph x in 
                List.iter (fun (weight, y) -> 
                  (*Printf.printf " sexec: -- out edge (%d,%d) \n" x y ; *)
                  let weight = match weight with Weight w -> w | Call _ -> failwith "cannot handle call" in 
                  Smt.Solver.reset solver;
                  begin match K.get_post_model ~solver:(solver) x_model weight with 
                  | Some y_model ->   
                        (*Printf.printf " sexec: -- adding node %d (cfg node %d) to tree\n" !vtxcnt y; *)
                       (* Interpretation.pp Format.str_formatter y_model;
                        Printf.printf "post-state model of dest: %s\n" @@ Format.flush_str_formatter ();*)
                        ARR.add !(ptt).cfg_vertex y;
                        ARR.add !(ptt).parents tx;
                        ptt := {!ptt with model = IntMap.add !vtxcnt y_model !(ptt).model};
                        worklist := !vtxcnt %>> !worklist;
                        vtxcnt := !vtxcnt + 1 
                  | None ->
                 let _ = get_out_neighbors !(ptt).graph y in 
                    try begin 
                      let pre_condition = !(ptt) %-*> y in 
                      let pre_condition = 
                        match pre_condition with 
                        | a :: t -> List.fold_right (fun x y -> K.mul y x) t a
                        | [] -> K.one 
                      in 
                      Smt.Solver.reset solver;
                      match get_abstract_model ~solver:(solver) pre_condition y err_loc (!ptt).graph with 
                        | Some y_model ->
                          ARR.add !(ptt).cfg_vertex y; 
                          ARR.add !(ptt).parents tx;
                          ptt := {!ptt with model = IntMap.add !vtxcnt y_model !(ptt).model};
                          worklist := !vtxcnt %>> !worklist;
                          vtxcnt := !vtxcnt + 1; () ;
                          Printf.printf "   *** Found abstract model for vertex y *** \n"
                        | _ -> () 
                        end with _ -> ()
                  end
                  ) x_out_neighbors;
                  (* Can safely remove current node from the tree. *) 
                  ptt := {!ptt with model = IntMap.remove tx !ptt.model }
          | None -> failwith "cannot happen" 
        end
      end
      done;
        Printf.printf "sexec: %d -> %d |- Greedy exploration ended. No greedy paths to errloc (close to being safe, assertion likely true). \n" entry err_loc
  | `Unsat -> 
    Printf.printf "sexec: %d -> %d |- Unsat - Proven unreachable (safe, assertion is definitely true)\n" entry err_loc 
  | `Unknown -> Printf.printf "sexec: %d -> %d |- State unknown\n" entry err_loc end



module BM = BatMap.Make(Int)

let test_interpolate_path (g : cfg_t) (entry : int) (err_loc : int) = 
  let parents = ref BM.empty in 
  let weights = ref BM.empty in 
  let rec gatherDFS v err_loc p = 
    Printf.printf "gatherDFS: visiting node %d\n" v ; 
    parents := BM.add v p !parents;
    if v == err_loc then ()
    else
      WG.iter_succ_e (fun (_, weight, y) -> 
        (* If y is unvisited, then visit it. *)
        match BM.find_opt y !parents with 
        | None -> 
          let weight = match weight with | Call _ -> failwith "" | Weight w -> w in 
          weights := BM.add y weight !weights;
          gatherDFS y err_loc v
        | Some _ -> ()
        ) g v
  in 
  let rec getPathCond u = 
    Printf.printf "Path node %d, parent %d\n" u (BM.find u !parents);
    if u = entry then begin Printf.printf "returning...\n" ; [] end
    else begin
      let u_weight = BM.find u !weights in 
      u_weight :: (getPathCond @@ BM.find u !parents) end
    in 
      parents := BM.add entry (-1) !parents;
      gatherDFS entry err_loc (-1);
      let path_cond = getPathCond err_loc in 
      let path_cond = List.rev path_cond in 
      Printf.printf "...Got path condition\n";
      mypp_weights "Path condition is: " path_cond;
      let interpolants = K.interpolate [ K.zero ] (mk_false ()) in 
      match interpolants with 
      | `Invalid -> Printf.printf " --- invalid\n"
      | `Unknown -> Printf.printf "  --- unknown\n"
      | `Valid interpolants ->
        mypp_formula " *** Interpolants: " interpolants 


let analyze2 file = 
  populate_offset_table file;
  match file.entry_points with
  | [main] -> begin

      let rg = Interproc.make_recgraph file in
      let entry = (RG.block_entry rg main).did in
      let (ts, assertions) = make_transition_system rg in
      let ts, new_vertices = make_ts_assertions_unreachable ts assertions in 
      TSDisplay.display ts;
      Printf.printf "\nentry: %d\n" entry; 
     (* List.iter (fun err_loc -> 
        Printf.printf "Processing erro %d-----------------------------\n" err_loc;
        test_interpolate_path ts entry err_loc 
        ) new_vertices*)
      List.iter (fun err_loc ->
        Printf.printf "testing overapproximate reachability of location %d\n" err_loc ; 
        Printf.printf "------------------------------\n";
        sexec  ts entry err_loc;
        Printf.printf "------------------------------\n"
        ) new_vertices 
      end
  | _ -> assert false

(* driver for plain mcmillan *)
let analyze3 file = 
  populate_offset_table file;
  match file.entry_points with
  | [main] -> begin

      let rg = Interproc.make_recgraph file in
      let entry = (RG.block_entry rg main).did in
      let (ts, assertions) = make_transition_system rg in
      let ts, new_vertices = make_ts_assertions_unreachable ts assertions in 
      TSDisplay.display ts;
      Printf.printf "\nentry: %d\n" entry; 
     (* List.iter (fun err_loc -> 
        Printf.printf "Processing erro %d-----------------------------\n" err_loc;
        test_interpolate_path ts entry err_loc 
        ) new_vertices*)
      List.iter (fun err_loc ->
        Printf.printf "testing reachability of location %d\n" err_loc ; 
        Printf.printf "------------------------------\n";
        mc_exec 0 ts entry err_loc;
        Printf.printf "------------------------------\n"
        ) new_vertices 
      end
  | _ -> assert false

(* driver for concolic mcmillan *)
let analyze4 file = 
  populate_offset_table file;
  match file.entry_points with
  | [main] -> begin

      let rg = Interproc.make_recgraph file in
      let entry = (RG.block_entry rg main).did in
      let (ts, assertions) = make_transition_system rg in
      let ts, new_vertices = make_ts_assertions_unreachable ts assertions in 
      TSDisplay.display ts;
      Printf.printf "\nentry: %d\n" entry; 
     (* List.iter (fun err_loc -> 
        Printf.printf "Processing erro %d-----------------------------\n" err_loc;
        test_interpolate_path ts entry err_loc 
        ) new_vertices*)
      List.iter (fun err_loc ->
        Printf.printf "testing reachability of location %d\n" err_loc ; 
        Printf.printf "------------------------------\n";
        mc_exec 1 ts entry err_loc;
        Printf.printf "------------------------------\n"
        ) new_vertices 
      end
  | _ -> assert false


let analyze file =
  populate_offset_table file;
  match file.entry_points with
  | [main] -> begin
      let rg = Interproc.make_recgraph file in
      let entry = (RG.block_entry rg main).did in
      let (ts, assertions) = make_transition_system rg in

      (*TSDisplay.display ts;*)
      let query = mk_query ts entry in
      assertions |> SrkUtil.Int.Map.iter (fun v (phi, loc, msg) ->
          (* for each assertion, compute path summary and see if reachable. *)
          let path = TS.path_weight query v in (* ruijie: this is the overapproximation! *)
          let sigma sym =
            match V.of_symbol sym with
            | Some v when K.mem_transform v path ->
              K.get_transform v path
            | _ -> Ctx.mk_const sym
          in
          let phi = Syntax.substitute_const Ctx.context sigma phi in
          let path_condition =
            Ctx.mk_and [K.guard path; Ctx.mk_not phi]
            |> SrkSimplify.simplify_terms srk
          in
          logf "Path condition:@\n%a"
            (Syntax.pp_smtlib2 Ctx.context) path_condition;
          dump_goal loc path_condition;
          (* A path_condition over-approximates the reachability info of the actual path.
             Hence if SAT, then nothing can be concluded.  --- We need to refine about this info.
              But if it is UNSAT or UNKNOWN, we can terminate. *)
          match Wedge.is_sat_model Ctx.context path_condition with
          | `Sat _ -> Report.log_error loc msg
          | `Unsat -> Report.log_safe ()
          | `Unknown ->
            logf ~level:`warn "Z3 inconclusive";
            Report.log_error loc msg);

      Report.print_errors ();
      Report.print_safe ();
    end
  | _ -> assert false

let preimage transition formula =
  let open Syntax in
  let transition = K.linearize transition in
  let fresh_skolem =
    Memo.memo (fun sym ->
        let name = show_symbol srk sym in
        let typ = typ_symbol srk sym in
        mk_const srk (mk_symbol srk ~name typ))
  in
  let subst sym =
    match V.of_symbol sym with
    | Some var ->
       if K.mem_transform var transition then
         K.get_transform var transition
       else
         mk_const srk sym
    | None -> fresh_skolem sym
  in
  mk_and srk [SrkSimplify.eliminate_floor srk (K.guard transition);
              substitute_const srk subst formula]

(* Attractor region analysis *)
let attractor_regions tf =
  let open Syntax in
  let formula = TF.formula tf in
  let attractors =
    BatList.fold_left (fun xs (x, x') ->
        let (x, x') = mk_const srk x, mk_const srk x' in
        let lo =
          let nonincreasing = mk_and srk [formula; mk_leq srk x' x] in
          match SrkZ3.optimize_box srk (mk_and srk [formula; nonincreasing]) [x'] with
          | `Sat [ivl] ->
             (match Interval.lower ivl with
              | Some lo -> [mk_leq srk (mk_real srk lo) x]
              | None -> [])
          | _ -> []
        in
        let hi =
          let nondecreasing = mk_and srk [formula; mk_leq srk x x'] in
          match SrkZ3.optimize_box srk (mk_and srk [formula; nondecreasing]) [x'] with
          | `Sat [ivl] ->
             (match Interval.upper ivl with
              | Some hi -> [mk_leq srk x (mk_real srk hi)]
              | None -> [])
          | _ -> []
        in
        (lo@hi@xs))
      []
      (TF.symbols tf)
  in
  TF.map_formula (fun _ -> mk_and srk (formula::attractors)) tf


let omega_algebra = function
  | `Omega transition ->
     (** over-approximate possibly non-terminating conditions for a transition *)
     begin
       let open Syntax in
       let tf =
         TF.map_formula
           (fun phi -> SrkSimplify.eliminate_floor srk (Nonlinear.linearize srk phi))
           (K.to_transition_formula transition)
       in
       let nonterm tf =
         let pre =
           let fresh_skolem =
             Memo.memo (fun sym -> mk_const srk (dup_symbol srk sym))
           in
           let subst sym =
             match V.of_symbol sym with
             | Some _ -> mk_const srk sym
             | None -> fresh_skolem sym
           in
           substitute_const srk subst (TF.formula tf)
         in
         let llrf, has_llrf =
           if !termination_llrf then
             if TLLRF.has_llrf srk tf then
               [Syntax.mk_false srk], true
             else if !termination_attractor
                     && TLLRF.has_llrf srk (attractor_regions tf) then
               [Syntax.mk_false srk], true
             else
               [pre], false
           else
             (* If LLRF is disabled, default to pre *)
             [pre], false
         in
         let dta =
           (* If LLRF succeeds, then we do not try dta *)
           if (not has_llrf) && !termination_dta then
             [mk_not srk (TDTA.mp srk tf)]
           else []
         in
         let exp =
           if (not has_llrf) && !termination_exp then
             let mp =
               Syntax.mk_not srk
                 (TerminationExp.mp (module Iteration.LinearRecurrenceInequation) srk tf)
             in
             let dta_entails_mp =
               (* if DTA |= mp, DTA /\ MP simplifies to DTA *)
               Syntax.mk_forall_consts
                 srk
                 (fun _ -> false)
                 (Syntax.mk_if srk (mk_and srk dta) mp)
             in
             match Quantifier.simsat srk dta_entails_mp with
             | `Sat -> []
             | _ -> [mp]
           else []
         in
         let result =
           Syntax.mk_and srk (llrf@dta@exp)
         in
         let file = get_gfile () in
         if !dump_goals
            && result <> (Syntax.mk_true srk)
            && result <> (Syntax.mk_false srk) then begin
             let filename =
               Format.sprintf "%s-%d-term.smt2"
                 (Filename.chop_extension (Filename.basename file.filename))
                 (!nb_goals)
          in
          let chan = Stdlib.open_out filename in
          let formatter = Format.formatter_of_out_channel chan in
          logf ~level:`always "Writing goal formula to %s" filename;
          Syntax.pp_smtlib2 srk formatter result;
          Format.pp_print_newline formatter ();
          Stdlib.close_out chan;
          incr nb_goals
           end;
         match Quantifier.simsat srk result with
         | `Unsat -> mk_false srk
         | _ -> result
       in
       if !termination_phase_analysis then begin
           let predicates =
             (* Use variable directions & signs as candidate invariants *)
             List.map (fun (x,x') ->
                 let x = mk_const srk x in
                 let x' = mk_const srk x' in
                 [mk_lt srk x x';
                  mk_lt srk x' x;
                  mk_eq srk x x'])
               (TF.symbols tf)
             |> List.concat
           in
           Iteration.phase_mp srk predicates tf nonterm
         end else
         nonterm tf
     end
  | `Add (cond1, cond2) ->
     (** combining possibly non-terminating conditions for multiple paths *)
     Syntax.mk_or srk [cond1; cond2]
  | `Mul (transition, state) ->
     (** propagate state formula through a transition *)
     preimage transition state

(* Raise universal quantifiers to top-level.  *)
let lift_universals srk phi =
  let open Syntax in
  let phi = rewrite srk ~down:(nnf_rewriter srk) phi in
  let rec quantify_universals (nb, phi) =
    if nb > 0 then
      quantify_universals (nb - 1, mk_forall srk `TyInt phi)
    else
      phi
  in
  let alg = function
    | `Tru -> (0, mk_true srk)
    | `Fls -> (0, mk_false srk)
    | `Atom (`Arith (`Eq, x, y)) -> (0, mk_eq srk x y)
    | `Atom (`Arith (`Lt, x, y)) -> (0, mk_lt srk x y)
    | `Atom (`Arith (`Leq, x, y)) -> (0, mk_leq srk x y)
    | `Atom (`ArrEq (a, b)) -> (0, mk_arr_eq srk a b)
    | `And conjuncts ->
       let max_nb = List.fold_left max 0 (List.map fst conjuncts) in
       let shift_conjuncts =
         conjuncts |> List.map (fun (nb,phi) ->
                     let shift = max_nb - nb in
                     substitute srk (fun (i, typ) -> mk_var srk (i + shift) typ) phi)
       in
       (max_nb, mk_and srk shift_conjuncts)
    | `Or disjuncts ->
       let max_nb = List.fold_left max 0 (List.map fst disjuncts) in
       if max_nb == 0 then
         (0, mk_or srk (List.map snd disjuncts))
       else
         (* Introduce a Skolem constant to distribute universals over disjunction:
            (forall x. F(x)) \/ (forall x. G(x))
            is equisatisfiable with
            exists c. forall x. (F(x) /\ c = 0) \/ (G(x) /\ c = 1) *)
         let sk = mk_const srk (mk_symbol srk ~name:"choice" `TyInt) in
         let shift_disjuncts =
           disjuncts |> BatList.mapi (fun idx (nb,phi) ->
                            let shift = max_nb - nb in
                            mk_and srk
                              [substitute srk (fun (i, typ) -> mk_var srk (i + shift) typ) phi;
                               mk_eq srk sk (mk_int srk idx)])
         in
         (max_nb, mk_or srk shift_disjuncts)

    | `Quantify (`Exists, name, typ, qphi) ->
       (0, mk_exists srk ~name typ (quantify_universals qphi))
    | `Quantify (`Forall, _, `TyInt, (nb_universals, phi)) ->
       (nb_universals + 1, phi)
    | `Quantify (`Forall, name, typ, qphi) ->
       (0, mk_forall srk ~name typ (quantify_universals qphi))
    | `Not (_, _) -> assert false
    | `Proposition (`Var i) -> (0, mk_var srk i `TyBool)
    | `Proposition (`App (p, args)) -> (0, mk_app srk p args)
    | `Ite (cond, bthen, belse) ->
       (0, mk_ite srk
             (quantify_universals cond)
             (quantify_universals bthen)
             (quantify_universals belse))
  in
  quantify_universals (Formula.eval srk alg phi)

let prove_termination_main file =
  populate_offset_table file;
  match file.entry_points with
  | [main] -> begin
      let rg = Interproc.make_recgraph file in
      let entry = (RG.block_entry rg main).did in
      let (ts, _) = make_transition_system rg in
      if !CmdLine.display_graphs then
        TSDisplay.display ts;
      let query = mk_query ts entry in
      let omega_paths_sum =
        TS.omega_path_weight query omega_algebra
        |> (if !termination_prenex
            then lift_universals srk
            else fun x -> x)
        |> SrkSimplify.simplify_terms srk
      in
      if !dump_goals
         && omega_paths_sum <> (Syntax.mk_true srk)
         && omega_paths_sum <> (Syntax.mk_false srk) then begin
          let filename =
            Format.sprintf "%s-%d-term.smt2"
              (Filename.chop_extension (Filename.basename file.filename))
              (!nb_goals)
          in
          let chan = Stdlib.open_out filename in
          let formatter = Format.formatter_of_out_channel chan in
          logf ~level:`always "Writing goal formula to %s" filename;
          Syntax.pp_smtlib2 srk formatter omega_paths_sum;
          Format.pp_print_newline formatter ();
          Stdlib.close_out chan
        end;
      match Quantifier.simsat srk omega_paths_sum with
      | `Sat ->
         Format.printf "Cannot prove that program always terminates\n";
         if !precondition then
           (* TODO: need to eliminate universal quantifiers first quantifiers first! *)
           let simplified =
             omega_paths_sum
             |> Nonlinear.linearize srk
             |> Quantifier.mbp srk (fun sym ->
                    match V.of_symbol sym with
                    | Some x -> V.is_global x
                    | _ -> false)
             |> Syntax.mk_not srk
           in
           Format.printf "Sufficient terminating conditions:\n%a\n"
             (Syntax.Formula.pp srk)
             simplified
      | `Unsat -> Format.printf "Program always terminates\n"
      | `Unknown -> Format.printf "Unknown analysis result\n"
    end
  | _ -> failwith "Cannot find main function within the C source file"

let resource_bound_analysis file =
  populate_offset_table file;
  match file.entry_points with
  | [main] -> begin
      let rg = Interproc.make_recgraph file in
      let (ts, _) = make_transition_system rg in
      let entry = (RG.block_entry rg main).did in
      let query = mk_query ts entry in
      let cost =
        let open CfgIr in
        let file = get_gfile () in
        let is_cost v = (Varinfo.show v) = "__cost" in
        try
          VVal (Var.mk (List.find is_cost file.vars))
        with Not_found ->
          Log.fatalf "Could not find __cost variable"
      in
      let cost_symbol = V.symbol_of cost in
      let exists x =
        match V.of_symbol x with
        | Some v -> Var.is_global (var_of_value v)
        | None -> false
      in
      RG.blocks rg |> BatEnum.iter (fun procedure ->
          let entry = (RG.block_entry rg procedure).did in
          let exit = (RG.block_exit rg procedure).did in
          let summary = WG.RecGraph.call_weight query (entry, exit) in
          if K.mem_transform cost summary then begin
            logf ~level:`always "Procedure: %a" Varinfo.pp procedure;
            (* replace cost with 0, add constraint cost = rhs *)
            let guard =
              let subst x =
                if x = cost_symbol then
                  Ctx.mk_real QQ.zero
                else
                  Ctx.mk_const x
              in
              let rhs =
                Syntax.substitute_const srk subst (K.get_transform cost summary)
              in
              let simplify =
                SrkSimplify.simplify_terms_rewriter srk
                % Nonlinear.simplify_terms_rewriter srk
              in
              Ctx.mk_and [Syntax.substitute_const srk subst (K.guard summary);
                          Ctx.mk_eq (Ctx.mk_const cost_symbol) rhs ]
              |> Syntax.rewrite srk ~up:simplify
            in
            match Wedge.symbolic_bounds_formula ~exists srk guard cost_symbol with
            | `Sat (lower, upper) ->
              begin match lower with
                | Some lower ->
                  logf ~level:`always "%a <= cost" (Syntax.ArithTerm.pp srk) lower;
                  logf ~level:`always "%a is o(%a)"
                    Varinfo.pp procedure
                    BigO.pp (BigO.of_arith_term srk lower)
                | None -> ()
              end;
              begin match upper with
                | Some upper ->
                  logf ~level:`always "cost <= %a" (Syntax.ArithTerm.pp srk) upper;
                  logf ~level:`always "%a is O(%a)"
                  Varinfo.pp procedure
                  BigO.pp (BigO.of_arith_term srk upper)
                | None -> ()
              end
            | `Unsat ->
              logf ~level:`always "%a is infeasible"
                Varinfo.pp procedure
          end else
            logf ~level:`always "Procedure %a has zero cost" Varinfo.pp procedure)
    end
  | _ -> assert false

let _ =
  CmdLine.register_config
    ("-cra-no-forward-inv",
     Arg.Clear forward_inv_gen,
     " Turn off forward invariant generation");
  CmdLine.register_config
    ("-cra-pred-abs",
     Arg.Clear forward_pred_abs,
     " Turn on predicate abstraction in forward invariant generation");
  CmdLine.register_config
    ("-cra-split-loops",
     Arg.Unit (fun () ->
         if !monotone then
           K.domain := (module Iteration.InvariantDirection(val !K.domain))
         else
           K.domain := (module Iteration.Split(val !K.domain))),
     " Turn on loop splitting");
  CmdLine.register_config
    ("-cra-prsd",
     Arg.Unit (fun () ->
         let open Iteration in
         let open SolvablePolynomial in
         K.domain := (module ProductWedge(SolvablePolynomialPeriodicRational)(WedgeGuard))),
     " Use periodic rational spectral decomposition");
  CmdLine.register_config
    ("-cra-vas",
     Arg.Unit (fun () ->
         let open Iteration in
         if !monotone then
           K.domain := (module Product
                                 (Product(Vas.Monotone)(PolyhedronGuard))
                                 (LinearRecurrenceInequation))
         else
           K.domain := (module Product
                                 (Product(Vas)(PolyhedronGuard))
                                 (LinearRecurrenceInequation))),
     " Use VAS abstraction");
  CmdLine.register_config
    ("-cra-vass",
     Arg.Unit (fun () ->
         let open Iteration in
         K.domain := (module Product(Product(LinearRecurrenceInequation)(PolyhedronGuard))(Vass))),
     " Use VASS abstraction");
  CmdLine.register_config
    ("-dump-goals",
     Arg.Set dump_goals,
     " Output goal assertions in SMTLIB2 format");
  CmdLine.register_config
    ("-monotone",
     Arg.Unit (fun () ->
         let open Iteration in
         monotone := true;
         K.domain := (module Product(LinearRecurrenceInequation)(PolyhedronGuard))),
     " Disable non-monotone analysis features");
  CmdLine.register_config
    ("-termination-no-exp",
     Arg.Clear termination_exp,
     " Disable exp-based termination analysis");
  CmdLine.register_config
    ("-termination-no-llrf",
     Arg.Clear termination_llrf,
     " Disable LLRF-based termination analysis");
  CmdLine.register_config
    ("-termination-no-dta",
     Arg.Clear termination_dta,
     " Disable DTA-based termination analysis");
  CmdLine.register_config
    ("-termination-no-phase",
     Arg.Clear termination_phase_analysis,
     " Disable phase-based termination analysis");
  CmdLine.register_config
     ("-termination-no-attractor",
      Arg.Clear termination_attractor,
      " Disable attractor region computation for LLRF");
  CmdLine.register_config
     ("-termination-no-prenex",
      Arg.Clear termination_prenex,
      " Disable prenex conversion");
  CmdLine.register_config
    ("-precondition",
     Arg.Clear precondition,
     " Synthesize mortal preconditions")

let _ =
  CmdLine.register_pass
    ("-cra", analyze, " Compositional recurrence analysis");
  CmdLine.register_pass
    ("-termination", prove_termination_main, " Proof of termination");
  CmdLine.register_pass
    ("-rba", resource_bound_analysis, " Resource bound analysis");
  CmdLine.register_pass 
    ("-concolic", analyze2, " Concolic executor");
  CmdLine.register_pass 
    ("-mcl-plain", analyze3, " Plain McMillan");
  CmdLine.register_pass 
    ("-mcl-concolic", analyze4, " Combined McMillan+Concolic execution algorithm")
