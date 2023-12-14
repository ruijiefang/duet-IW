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

let make_transition_system (simplify:bool) rg =
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
        let tg = if simplify then TS.simplify point_of_interest tg else tg in
        let tg = if simplify then TS.remove_temporaries tg else tg in
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

(** Useful definitions for SMT-based analyses: McMillan's assertion-checking algorithm + concolic execution *)

module ProcName = struct 
  type t = int * int 

  let make ((u, v) : TS.vertex * TS.vertex) : t = (u, v)

  let string_of (p: t) = 
    let u, v = p in Printf.sprintf "%d:%d" u v 
  
  let of_string (s: string) = 
    match String.split_on_char ':' s with 
    | [ us ; vs ] -> (make ((int_of_string us), (int_of_string vs)))
    | _ -> failwith @@ Printf.sprintf "illegal procedure identifier %s" s

  (* lexicographic comparison using Stdlib.compare *)
  let compare (p1: t) (p2: t) = Stdlib.compare p1 p2 
end

module ProcMap = BatMap.Make(ProcName)
module IntMap = BatMap.Make(Int)
module StringMap = BatMap.Make(String)
module ISet = BatSet.Make(Int)
module DQ = BatDeque
module ARR = Batteries.DynArray 
type cfg_t = TSG.t
type idq_t = int BatDeque.t 
type state_formula = Ctx.t Syntax.formula 
exception Mexception of string 
let mk_true () = Syntax.mk_true Ctx.context
let mk_false () = Syntax.mk_false Ctx.context 
let mk_query ts entry = TS.mk_query ts entry (if !monotone then (module MonotoneDom) else (module TransitionDom))

let log_formulas prefix formulas = 
  List.iteri (fun i f -> logf ~level:`always "[formula] %s(%i): %a\n" prefix i (Syntax.pp_expr srk) f) formulas 

let log_weights prefix weights = 
  List.iteri (fun i f -> logf ~level:`always "[weight] %s(%i): %a\n" prefix i K.pp f) weights

let log_model prefix model = 
  logf ~level:`always "[model] %s: %a\n" prefix Interpretation.pp model

(* Convert assertion checking problem to vertex reachability problem. *)
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
      log_formulas s [ Ctx.mk_not phi ] ; 
      new_vertices := u :: !new_vertices 
  ); !pts, !new_vertices

module Summarizer = 
  struct 
      module SMap = BatMap.Make(ProcName)
      type t = {
        graph: cfg_t;
        src: int;
        query: TS.query;
        mutable underapprox: K.t SMap.t
      }

      let init (graph: cfg_t) (src: int) : t =
        let q = mk_query graph src in  
        { graph = graph; src = src; query = q; underapprox = SMap.empty }

      let proc_summary (ctx: t) ((u, v) : ProcName.t) =
          TS.get_summary ctx.query (u, v) 
      
      let set_proc_summary (ctx: t) ((u, v): ProcName.t) (w: K.t) =
          TS.set_summary ctx.query (u, v) w
      
      let under_proc_summary (ctx: t) ((u, v): ProcName.t) : K.t = 
        SMap.find_default K.zero (u, v) ctx.underapprox

      let set_under_proc_summary (ctx: t) ((u, v): ProcName.t) (w: K.t) : unit = 
        ctx.underapprox <- SMap.add (u, v) w ctx.underapprox

      let refine (ctx: t) ((u, v): ProcName.t) (pre: state_formula) (post: state_formula) =
        let summary = proc_summary ctx (u, v) in 
        let s_pre = K.mul (K.assume (Syntax.mk_not srk pre)) summary in 
        let s_post = K.mul summary (K.assume (Syntax.mk_not srk post)) in 
          K.add s_pre s_post |> set_proc_summary ctx (u, v);
          assert (summary <> (proc_summary ctx (u,v)))
      
      let refine_under (ctx: t) ((u, v): ProcName.t) (w:K.t) : unit = 
        let summary = under_proc_summary ctx (u, v) in 
        let summary' = K.add summary w in 
        set_under_proc_summary ctx (u, v) summary'
      
      let path_weight_intra (ctx: t) (src: int) (dst: int) =
          TS.intra_path_summary ctx.query src dst
      
      let path_weight_inter (ctx: t) (src: int) (dst: int) =
          TS.inter_path_summary ctx.query src dst 
  end


  (** Algebraic formulation of McMillan's algorithm. *)
module McMillanChecker = struct
  module VN = struct 
    let to_vertex (v : int) : TS.vertex = v 
    let of_vertex (v : TS.vertex) : int = v
  end
  module TS' = struct 
    include TS
    let iter_succ_e (f: (TS.vertex * (TS.transition label) * TS.vertex) -> unit) (g: TS.t) (v: TS.vertex) = WG.iter_succ_e f g v
    
    let fold_succ_e (f : (TS.vertex * (TS.transition label) * TS.vertex) -> 'b -> 'b) (g: TS.t) (u: TS.vertex) (s: 'b) = 
      WG.fold_succ_e f g u s 

    let edge_weight g u v = WG.edge_weight g u v 
  end
  (* ART module *)
  module ReachTree = ReachTree.ART(Ctx)(K)(TS')(ProcName)(VN)(Summarizer)

  (* to print the reachability tree (+ worklist), or not *) 
  let print_tree = false

  (* contextual information maintained by McMillan-Checker. *)
  (* intraprocedural context *)
  type intra_context = {
    id : ProcName.t;
    ts : cfg_t;
    mutable art : ReachTree.t ref;
    mutable worklist : ReachTree.node DQ.t;
    mutable execlist : ReachTree.node DQ.t;
    global_ctx : global_context ref;
  } 
  (* global context *)
  and global_context = {
      mode: mc_mode;
      interproc: Summarizer.t ref;
  }
  (* mode of McMillan's algorithm: plain, or CRA-fueled concolic mode *)
  and mc_mode = 
      | PlainMcMillan 
      | ConcolicMcMillan
  (* answer *)
  and mc_result = 
      | Safe 
      | Unsafe of K.t list
  (** some helper functions that operate on the context *)

  let mk_intra_context (gctx: global_context ref) (id: ProcName.t) (ts: cfg_t) (pre_state: state_formula) (post_state: state_formula) (entry: int) (err_loc: int)  =
    ref {
      id = id;
      ts = ts;
      worklist = DQ.empty;
      execlist = DQ.empty;
      art = ReachTree.make ts entry err_loc pre_state post_state !gctx.interproc;
      global_ctx = gctx;
    }
  and mk_mc_context (start_mode: mc_mode) (global_cfg: cfg_t) (global_src: int) = 
    ref {
      mode = start_mode; 
      interproc = ref (Summarizer.init global_cfg global_src);
    }

  (** some helper methods *)
  let worklist_push  (i : ReachTree.node) (q : ReachTree.node DQ.t) = DQ.snoc q i 

  (* Interpolate the path (entry) -> (t %-> src) -> (sink). If fail, then get model. *)
  let interpolate_or_get_model (art : ReachTree.t ref) (recurse_level: int) (src : ReachTree.node) (sink: TS.vertex) = 
    let oracle = 
      if recurse_level = 0 then Summarizer.path_weight_inter else Summarizer.path_weight_intra in 
    let is_inter_err_loc = (recurse_level > 0) && ((ReachTree.maps_to art src) = ReachTree.get_err_loc art) in 
    let post_path_summary = oracle (ReachTree.get_summarizer art) (ReachTree.maps_to art src) sink in 
    let err_state =  
      if recurse_level = 0 then K.guard post_path_summary |> Syntax.mk_not srk
      else 
        begin if is_inter_err_loc then 
          Syntax.mk_not srk @@ ReachTree.get_post_state art 
        else (K.guard (K.mul post_path_summary (K.assume (ReachTree.get_post_state art)))) |> Syntax.mk_not srk 
      end
    in
    let initial_path_weights = (K.assume (ReachTree.get_pre_state art)) :: ReachTree.path_condition art OverApprox src in 
      K.interpolate_or_concrete_model initial_path_weights err_state

  let get_global_ctx (ctx: intra_context ref) = (!ctx.global_ctx)

  (** Core procedures of McMillan's algorithm *)


  (* refine path to (tree) node v. 
     Returns `Failure trans with trans being the path-to-error if unable to refine.
     Returns `Success if refine is able to refine. *)
  let mc_refine (ctx: intra_context ref) (recurse_level: int) (v: ReachTree.node) = 
    let handle_failure art v = 
      logf ~level:`always " *********************** REFINEMENT FAILED *************************\n"; 
      let path_condition = ReachTree.path_condition art OverApprox v 
      in `Failure path_condition 
    in let art = !ctx.art in 
    let path_condition = ReachTree.path_condition art OverApprox v in 
    let path = ReachTree.tree_path art v in 
      match !(get_global_ctx ctx).mode with 
      | PlainMcMillan -> 
        begin
        match K.interpolate ((K.assume @@ ReachTree.get_pre_state art) :: path_condition) (Syntax.mk_not srk @@ ReachTree.get_post_state art) with 
        | `Invalid | `Unknown -> 
          handle_failure art v
        | `Valid interpolants ->
          logf ~level:`always "  refine: interpolant sequence for tree vertex %d: -----------\n" v;
          logf ~level:`always " original formula: ";
          log_weights "" path_condition;
          logf ~level:`always "--------------------------------------------------------------\n";
          log_formulas "" interpolants;
          logf ~level:`always "--------------------------------------------------------------\n";
          ReachTree.refine !ctx.art path interpolants
          |> List.iter (fun x -> !ctx.worklist <- worklist_push x !ctx.worklist);
          `Success 
        end 
      | ConcolicMcMillan -> 
        begin 
          match interpolate_or_get_model art recurse_level v @@ ReachTree.get_err_loc art with 
          `Invalid v_model -> 
            logf ~level:`always "Unable to refine but got model\n";
            (* for node v, since v is a frontier node, update art.models to store its corresponding model. *)
            ReachTree.set_model art v v_model;
            handle_failure art v
          | `Unknown -> failwith ""
          | `Valid interpolants -> 
            logf ~level:`always "--- mc_refine: interpolation succeeded. path length %d, interpolant length %d" (List.length path) (List.length interpolants);
            ReachTree.refine art path interpolants
            |> List.iter (fun x -> !ctx.worklist <- worklist_push x !ctx.worklist); 
            `Success 
        end

  let single_plain_mcmillan_round (ctx: intra_context ref) = 
    match DQ.front !ctx.worklist with (* use DQ.rear if want BFS *) 
      | Some (u, w) (* (w, u) if use DQ.front *) ->          
        ReachTree.log_art !ctx.art;
        ReachTree.log_node u;
        log_formulas "label: " [ReachTree.label !ctx.art u]; 
        !ctx.worklist <- w;
        (* Fetched tree node u from work list. First attempt to close it. *)
        if not (ReachTree.is_covered !ctx.art u) then begin
          logf ~level:`always " uncovered. try close\n";
          begin match ReachTree.close !ctx.art u with 
            | (true, wl) -> (* Close succeeded. No need to further explore it. *)
              logf ~level:`always "Close succeeded.\n";

              (* ctx.worklist := u %>> !(ctx.worklist); *)
              `Continue 
            | (false, wl) -> (* u is uncovered. *)
              if (ReachTree.maps_to !ctx.art u) == ReachTree.get_err_loc !ctx.art then 
                begin match mc_refine ctx 0 u with 
                  | `Success -> 
                    logf ~level:`always " refinement result: SUCCESS\n";
                    (* for every node along path of refinement try close *)
                    let path = ReachTree.tree_path !ctx.art u in 
                      List.iter (fun x -> 
                        let _, l = ReachTree.close !ctx.art x in 
                          List.iter (fun frontier -> !ctx.worklist <- worklist_push frontier !ctx.worklist) l) path;
                      (* ctx.worklist := u %>> !(ctx.worklist); *)
                      `Continue
                  | `Failure path_cond -> 
                    logf ~level:`always " refinement result: FAILURE\n";
                    `ErrorReached path_cond
                end 
              else begin 
                logf ~level:`always " expanding...\n";
                let new_nodes = ReachTree.expand_plain !ctx.art u in 
                  logf ~level:`always "new nodes: [";
                  List.iter (fun n -> 
                    logf ~level:`always "%d " (n |> ReachTree.of_node);
                    !ctx.worklist <- worklist_push n !ctx.worklist) new_nodes;
                  logf ~level:`always " ]\n";
                  `Continue
              end
          end end
        else begin (* u is closed *)
          logf ~level:`always "  | covered \n"; 
          `Continue 
        end
      | None -> failwith "err: single_mcmillan_round assumes worklist is non-empty"

  let plain_mcmillan_execute (ctx: intra_context ref) = 
    let continue = ref true in
    let witness_r = ref [ K.zero ] in 
    let state = ref `Continue in 
    let eps = ReachTree.add_tree_vertex !ctx.art ~label:(ReachTree.get_pre_state !ctx.art) (ReachTree.get_entry !ctx.art) (-1) in 
    !ctx.worklist <- worklist_push eps !ctx.worklist;
    begin
      while DQ.size (!ctx.worklist) > 0 && !continue do 
        begin 
          match single_plain_mcmillan_round ctx with 
          | `Continue -> continue := true; state := `Continue
          | `ErrorReached witness -> 
            logf ~level:`always "  not continueing any further --- error reached\n";
            witness_r := witness; 
            continue := false; 
            state := `ErrorReached
        end
      done;
      logf ~level:`always " +++++++++++++++++++++++++++++++++ Final ART +++++++++++++++++++++++++++++ \n";
      ReachTree.log_art !ctx.art;
      match !state with 
      | `ErrorReached -> Unsafe (!witness_r)
      | `Continue -> 
        logf ~level:`always "execution saturated\n"; 
        begin match ReachTree.verify_well_labelled_tree !ctx.art with 
          | false -> failwith "ERROR: well-labelled check failed"
          | true -> ReachTree.check_covering_welformedness !ctx.art 
        end;
        Safe
    end

  (* concolic phase of our model checking algorithm *)
  let concolic_phase (ctx: intra_context ref) (recursion_level: int) = 
    match DQ.front (!ctx.execlist) with 
    | Some (u, w) -> 
      ReachTree.log_art !ctx.art;
      logf ~level:`always " visit %d (%d)\n" u (ReachTree.maps_to !ctx.art u);
      !ctx.execlist <- w;
      if (ReachTree.maps_to !ctx.art u) = (ReachTree.get_err_loc !ctx.art) then 
        begin 
          (** if an error is reached , see if it is a call from the first recursive level or non-first. *)
          (** a non-first recursion level requires an additional step of concolic execution past edge (K.assume !art.post). *)
          if recursion_level = 0 then 
            `ErrorReached u
          else begin 
            logf ~level:`always "inter-procedural return-loc reached. trying expand_pseudo...\n";
            (** if we can successfully expand past the assertion of !art.post_state, then we can report error and exit. *)
            (** otherwise, we shall refine the current, exit node. *)
            match ReachTree.expand_pseudo !ctx.art u with 
            | `Refine -> 
              logf ~level:`always "     ... expand_pseudo failed, adding %d to refinement worklist...\n" u;
              !ctx.worklist <- worklist_push u !ctx.worklist; 
              `Continue 
            | `Error -> 
              logf ~level:`always "       ... expand_pseudo succeeded\n";
              `ErrorReached u 
          end
        end
      else begin
        let u_model = IntMap.find u !(!ctx.art).models in 
          logf ~level:`always "model of %d (%d): \n" u (ReachTree.maps_to !ctx.art u);
          log_model "" u_model;
          let new_concolic_nodes, new_frontier_nodes = ReachTree.expand_concolic (get_solver ctx) recursion_level !ctx.art u in 
            List.iter (fun concolic_node -> !ctx.execlist <- worklist_push concolic_node !ctx.execlist) new_concolic_nodes;
            List.iter (fun frontier_node -> !ctx.worklist <- worklist_push frontier_node !ctx.worklist) new_frontier_nodes;
            `Continue
      end
    | None -> failwith "err: concolic_phase is reading from empty execution worklist" (* cannot happen *)

  (* refinement phase of our model checking algorithm *)
  let refinement_phase (ctx: intra_context ref) (recurse_level: int) = 
    match DQ.front (!ctx.worklist) with 
    | Some (u, w) -> 
      ReachTree.log_art !ctx;
      !ctx.worklist <- w;
      begin match ReachTree.find_opt !ctx.art u with 
      | Some _ -> 
        (* Fetched tree node u from work list. First attempt to close it. *)
        if not (mc_is_covered ctx u) then 
          begin
            logf ~level:`always " uncovered. try close\n";
            if mc_close ctx u then (* Close succeeded. No need to further explore it. *)
              begin 
                logf ~level:`always "Close succeeded.\n"; 
                `Continue
              end   
            else (* u is uncovered. *)
              begin match mc_refine ctx recurse_level u with 
              | `Success -> (* refinement succeeded *)
                logf ~level:`always "refinement_phase: refinement succeeded\n";
                (* for every node along path of refinement try close *)
                let path = ReachTree.tree_path !ctx.art u in 
                  List.iter (fun x -> let _ = mc_close ctx x in ()) path;
                  `Continue 
              | `Failure _ -> 
                !ctx.execlist <- worklist_push u !ctx.execlist; (* put u onto execlist since it now has a model. *)
                (* for every node along path of refinement try close *)
                let path = ReachTree.tree_path !ctx.art u in 
                  List.iter (fun x -> let _ = mc_close ctx x in ()) path 
                ; `Continue
              end
          end
        else begin 
          logf ~level:`always "refinement_phase: %d is covered\n" u;
          `Continue
        end
      | None -> 
        logf ~level:`always "refinement_phase: encountered deleted vertex %d. continuing\n" u;
        `Continue
      end
    | None -> failwith "refinement_phase: encountered an empty worklist for refinement\n" (* cannot happen *)


  (** Create prelude to a procedure, which is a transition formula *)
  let prelude (precondition: Ctx.t Syntax.formula) (transform: Ctx.t Syntax.formula) = 
    failwith ""
 (*   let suffix = "_out__" in 
    let mangle name = name ^ suffix in 
    let replaced = Hashtbl.create 998 in 
    let replace_vocab : Syntax.Symbol.Set.t = Syntax.symbols precondition in 
    let replacer s = 
      match Hashtbl.find_opt replaced s, Syntax.Symbol.Set.mem s replace_vocab with 
      | None, true -> 
          let name = Syntax.show_symbol srk s |> mangle in
          let typ = Syntax.typ_symbol srk s in
            Syntax.mk_const srk (Syntax.mk_symbol srk ~name typ) 
      | Some s', _ -> s'
      | None, false -> Syntax.mk_const srk s in 
    let precondition = Syntax.substitute_const srk replacer precondition in 
    let transform = Syntax.substitute_const srk replacer transform in 
      (Syntax.symbols precondition 
      |> Syntax.Symbol.Set.elements
      |> List.map (fun x -> Ctx.mk_eq (Syntax.mk_const srk x) (nondet_const "havoc" (`TyInt))) 
      |> Syntax.mk_and srk), transform
*)
  (* handle procedure calls by lazily backsolving them along paths-to-error. *)
  let rec handle_path_to_error (ctx: intra_context ref) (recurse_level: int) (err_leaf : int) : [`Concretized of K.t list | `Failure of int ] = 
    let art = !ctx.art in 
    let _ = 
      logf ~level:`always "interpretation at node %d(%d) handle_path_to_error: %a\n" 
        err_leaf (ReachTree.maps_to art err_leaf) (Interpretation.pp) (IntMap.find err_leaf !art.models)

    in let _ = ReachTree.reset_substitute_map art in 
    let seq = List.fold_left K.mul K.one in 
    let project tr = (* existentially quantify over all locals, leaving out only globals *)
      K.exists (fun v -> V.is_global v) tr in
    let call_edges = ReachTree.calls_in_path art err_leaf in 
    let status = List.fold_left 
      (fun result curr_call ->
        match result with 
        | `Unconcretized nnn ->  
          begin
            (* w, z are tree nodes such that (art.maps_to w, art.maps_to z) is a call-edge to (call_entry, call_exit)
               and (call_entry, call_exit) refer to cfg vertex locations delineating the procedure entry/exit in the 
               recursive control flow graph. *)
            let (w, (call_entry, call_exit), z) = curr_call in 
            let prefix = K.assume (!art.pre_state) :: ReachTree.path_condition art w |> seq in
            let suffix = ((ReachTree.path_condition art ~cutoff:z err_leaf) @ [K.assume (!art.post_state)]) |> seq in 
            let summary = 
              logf ~level:`always "get summary (art %d mapsto %d, %d mapsto %d)\n" w (ReachTree.maps_to art w) z (ReachTree.maps_to art z); 
              ReachTree.edge_weight art w z in 
            (* helper subroutine to refine procedure summary of (call_entry, call_exit), when extrapolate failed *)
            let refine_summary_with_extrapolants e1 e2 = 
              Summarizer.refine (!art.interproc) (call_entry, call_exit) e1 e2 
            in let _ = Printf.printf "HERE HEREextrapolate at call site (%d,%d) @ call edge %d\n" call_entry call_exit nnn  
            in begin match K.extrapolate prefix summary suffix recurse_level with 
              | `Sat (e1, e12) -> 
                log_formulas "--- handle_path_to_error : extrapolate success; formulas \n" [e1;e12];
                let pre, transform' = prelude e1 e12 in 
                log_formulas "--- handle_path_to_error : prelude " [ pre ];
                log_formulas "--- handle_path_to_error prelude transform: " [transform'];
                (* instantiate interprocedural reachability query *)
                let ctx' = mk_intra_context (get_global_ctx ctx) (call_entry, call_exit) !art.graph (Syntax.mk_and srk [e1; pre]) transform' call_entry call_exit in 
                begin match concolic_mcmillan_execute ctx' (recurse_level + 1) with 
                  | Safe -> 
                    logf ~level:`always "--- handle_path_to_error: recursive call to concolic_mcmillan_execute failed. refining\n";
                    (* concretization of error trace failed. do refine *)
                      (* declare failure *)
                      refine_summary_with_extrapolants e1 e12;
                      let summary' = ReachTree.edge_weight art w z in 
                        log_weights "  --> new summary: " [summary'];
                      (* return the dst vertex of the call-edge (w,z) as frontier node for refinement. *)
                      (* a frontier node is a node that cannot be reached by means of concrete execution from its parent, 
                         and here our interprocedural definition is the same. *)
                      `Failure z (* z is the dst vertex of call-edge (w, (call_entry, call_exit), z) *)
                  | Unsafe tr -> 
                    logf ~level:`always "--- handle_path_to_error: recursive call to concolic_mcmillan_execute success. substituting in concrete path\n";
                    Printf.printf "concrete path is %d,%d for path from entry to tree node %d(%d) err %d level %d\n" 
                      (ReachTree.maps_to art w) (ReachTree.maps_to art z) err_leaf (ReachTree.maps_to art err_leaf) err_leaf recurse_level;
                       ReachTree.substitute_edge_weight art (w, z) (tr |> seq |> project);
                      `Unconcretized (nnn+1)
                end
              | `Unsat -> 
                failwith "--- handle_path_to_error : extrapolate failed"
            end
         end
         | _ -> result (* some call-edge failed in the middle. go down without trying further. *)
        ) (`Unconcretized 0) call_edges in 
      match status with 
      | `Unconcretized _ -> 
        let path_cond = 
          ReachTree.path_condition art err_leaf in 
        `Concretized path_cond (* by the end, we've concretized ourselves *)
      | `Failure v -> 
        ReachTree.reset_substitute_map art;
        `Failure v  (* otherwise, we've encountered a concretization failure*)

  (* intraprocedural mcmillan's algorithm sped-up with CRA + concolic execution *)
  and concolic_mcmillan_execute (ctx: intra_context ref) (recurse_level: int) : mc_result = 
    logf ~level:`always " *********************************************** recurse_level: %d\n" recurse_level;
    (*if recurse_level > 3 then failwith "failing because recursive level > 1"; *)
    let eps = ReachTree.add_tree_vertex !ctx.art ~label:!(!ctx.art).pre_state !(!ctx.art).entry (-1) in 
    let continue = ref true in 
    let state = ref `Continue in
      !ctx.worklist <- worklist_push eps !ctx.worklist;
      while !continue && (DQ.size (!ctx.worklist) > 0 || DQ.size (!ctx.execlist) > 0) do
        if DQ.size (!ctx.execlist) > 0 then begin 
          (* concolic phase *)
          begin match concolic_phase ctx recurse_level with 
          | `ErrorReached w -> 
            logf ~level:`always "--- concolic_mcmillan_execute: found path-to-error at vertex %d \n" w;
            begin match handle_path_to_error ctx recurse_level w with 
            | `Failure frontier_node -> (* path-to-error concretization failed. frontier_node is the src node of a call-edge. *)
              (* refine and blow away the tree at `frontier_node`. *)
              logf ~level:`always "--- concolic_mcmillan_execute: frontier node is %d\n" frontier_node;
              let children = ReachTree.children !ctx.art frontier_node in 
                (* blow away children of tree node `frontier_node`. *)
                List.iter (fun child -> 
                  logf ~level:`always " --- concolic_mcmillan_execute: blowing away subtree at child node %d \n" child;                  
                  ReachTree.blowup !ctx.art child) children;
                !ctx.worklist <- worklist_push frontier_node !ctx.worklist;
                continue := true
            | `Concretized pathcond ->  
              logf ~level:`always "--- conoclic_mcmilan_execute: managed to concretize an intraprocedural path-to-error. returning... ";
              state := `Concretized (pathcond);
              continue := false
            end
          | `Continue -> 
            state := `Continue
          end
        end else begin 
          (* refinement phase *)
          state := refinement_phase ctx recurse_level
        end
      done; 
      match !state with 
      | `Continue -> Safe
      | `Concretized cond -> Unsafe (cond) 


  let mc_exec (mode: mc_mode) (ts : cfg_t) (entry : int) (err_loc : int) : mc_result = 
    (**
    * Set up data structures used by the algorithm: worklist, 
    * vtxcnt (keeps track of largest unused vertex number in tree), 
    * ptt is a pointer to the reachability tree.
    *)
    let global_context = mk_mc_context mode ts entry in 
    match mode with 
    | PlainMcMillan -> 
      logf ~level:`always "executing plain mcmillan's algorithm\n";
      let main_context = mk_intra_context global_context (entry, err_loc) ts (mk_true ()) (mk_true ()) entry err_loc in 
        plain_mcmillan_execute main_context 
    | ConcolicMcMillan -> 
      logf ~level:`always "executing concolic mcmillan's algorithm\n";
      let main_context = mk_intra_context global_context (entry, err_loc) ts (mk_true ()) (mk_true ()) entry err_loc in 
        concolic_mcmillan_execute main_context 0
  end

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
      log_weights "Path condition is: " path_cond;
      let interpolants = K.interpolate [ K.zero ] (mk_false ()) in 
      match interpolants with 
      | `Invalid -> Printf.printf " --- invalid\n"
      | `Unknown -> Printf.printf "  --- unknown\n"
      | `Valid interpolants ->
        log_formulas " *** Interpolants: " interpolants 


(* driver for plain mcmillan *)
let analyze_plain_mcl file = 
  populate_offset_table file;
  match file.entry_points with
  | [main] -> begin

      let rg = Interproc.make_recgraph file in
      let entry = (RG.block_entry rg main).did in
      let (ts, assertions) = make_transition_system true rg in
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
        match McMillanChecker.mc_exec McMillanChecker.PlainMcMillan ts entry err_loc with 
        | Safe -> Printf.printf "  proven safe\n"
        | Unsafe _ -> Printf.printf "  proven unsafe\n";
        Printf.printf "------------------------------\n"
        ) new_vertices 
      end
  | _ -> assert false

(* driver for concolic mcmillan *)
let analyze_concolic_mcl file = 
  populate_offset_table file;
  match file.entry_points with
  | [main] -> begin

      let rg = Interproc.make_recgraph file in
      let entry = (RG.block_entry rg main).did in
      let (ts, assertions) = make_transition_system true rg in
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
        match McMillanChecker.mc_exec McMillanChecker.ConcolicMcMillan ts entry err_loc with 
        | Safe -> Printf.printf "  proven safe\n";
        | Unsafe _ -> Printf.printf "  proven unsafe\n";
        Printf.printf "------------------------------\n"
        ) new_vertices 
      end
  | _ -> assert false

(** dump simplified CFG before doing model checking / CRA / concolic execution *)
let dump_cfg simplify file = 
  populate_offset_table file;
  match file.entry_points with 
  | [main] ->
    begin 
      let rg = Interproc.make_recgraph file in 
      let _ (* entry *) = (RG.block_entry rg main).did in 
      let (ts, assertions) = make_transition_system simplify rg in 
      let ts, _ = make_ts_assertions_unreachable ts assertions in 
      TSDisplay.display ts
    end
  | _ -> assert false


(** main entry to CRA *)
let analyze file =
  populate_offset_table file;
  match file.entry_points with
  | [main] -> begin
      let rg = Interproc.make_recgraph file in
      let entry = (RG.block_entry rg main).did in
      let (ts, assertions) = make_transition_system true rg in

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
      let (ts, _) = make_transition_system true rg in
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
      let (ts, _) = make_transition_system true rg in
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
    ("-mcl-plain", analyze_plain_mcl, " Plain McMillan");
  CmdLine.register_pass 
    ("-mcl-concolic", analyze_concolic_mcl, " Combined McMillan+Concolic execution algorithm");
  CmdLine.register_pass
    ("-dump-simplified-cfg", dump_cfg true, " Dump simplified control-flow-graph before analysis");
  CmdLine.register_pass
    ("-dump-unsimplified-cfg", dump_cfg false, " Dump unsimplified control-flow-graph of the input program")
