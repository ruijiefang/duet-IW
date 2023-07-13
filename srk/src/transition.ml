open Syntax
open BatPervasives

include Log.Make(struct let name = "srk.transition" end)

module type Var = sig
  type t
  val pp : Format.formatter -> t -> unit
  val show : t -> string
  val typ : t -> [ `TyInt | `TyReal ]
  val compare : t -> t -> int
  val symbol_of : t -> symbol
  val of_symbol : symbol -> t option
  val is_global : t -> bool
end

module Make
    (C : sig
       type t
       val context : t context
     end)
    (Var : Var) =
struct
  module M = BatMap.Make(Var)

  module Term = ArithTerm

  type var = Var.t

  type t =
    { transform : (C.t arith_term) M.t;
      guard : C.t formula }

  let compare x y =
    match Formula.compare x.guard y.guard with
    | 0 -> M.compare Term.compare x.transform y.transform
    | cmp -> cmp

  let srk = C.context

  let pp formatter tr =
    Format.fprintf formatter "{@[<v 0>";
    SrkUtil.pp_print_enum_nobox
       ~pp_sep:(fun formatter () -> Format.pp_print_break formatter 0 0)
       (fun formatter (lhs, rhs) ->
          Format.fprintf formatter "%a := @[%a@]"
            Var.pp lhs
            (Term.pp srk) rhs)
       formatter
       (M.enum tr.transform);
    begin match Formula.destruct srk tr.guard with
      | `Tru -> ()
      | _ ->
        if not (M.is_empty tr.transform) then
          Format.pp_print_break formatter 0 0;
        Format.fprintf formatter "when @[<v 0>%a@]" (Formula.pp srk) tr.guard
    end;
    Format.fprintf formatter "@]}"

  let show = SrkUtil.mk_show pp

  let construct guard assignment =
    { transform =
        List.fold_left (fun m (v, term) -> M.add v term m) M.empty assignment;
      guard = guard }

  let assign v term =
    { transform = M.add v term M.empty;
      guard = mk_true srk }

  let parallel_assign assignment = construct (mk_true srk) assignment

  let assume guard = construct guard []

  let havoc vars =
    let transform =
      List.fold_left (fun transform v ->
          M.add
            v
            (mk_const srk (mk_symbol srk ~name:"havoc" (Var.typ v :> typ)))
            transform)
        M.empty
        vars
    in
    { transform = transform; guard = mk_true srk }

  let mul left right =
    let fresh_skolem =
      Memo.memo (fun sym ->
          let name = show_symbol srk sym in
          let typ = typ_symbol srk sym in
          mk_const srk (mk_symbol srk ~name typ))
    in
    let left_subst sym =
      match Var.of_symbol sym with
      | Some var ->
        if M.mem var left.transform then
          M.find var left.transform
        else
          mk_const srk sym
      | None -> fresh_skolem sym
    in
    let guard =
      mk_and srk [left.guard;
                  substitute_const srk left_subst right.guard]
    in
    let transform =
      M.fold (fun var term transform ->
          if M.mem var transform then
            transform
          else
            M.add var term transform)
        left.transform
        (M.map (substitute_const srk left_subst) right.transform)
    in
    { transform; guard }

  let add left right =
    let left_eq = ref [] in
    let right_eq = ref [] in
    let transform =
      let merge v x y =
        match x, y with
        | Some s, Some t when Term.equal s t -> Some s
        | _, _ ->
          let phi =
            mk_symbol srk ~name:("phi_" ^ (Var.show v)) ((Var.typ v) :> typ)
            |> mk_const srk
          in
          let left_term =
            match x with
            | Some s -> s
            | None -> mk_const srk (Var.symbol_of v)
          in
          let right_term =
            match y with
            | Some t -> t
            | None -> mk_const srk (Var.symbol_of v)
          in
          left_eq := (mk_eq srk left_term phi)::(!left_eq);
          right_eq := (mk_eq srk right_term phi)::(!right_eq);
          Some phi
      in
      M.merge merge left.transform right.transform
    in
    let guard =
      mk_or srk [mk_and srk (left.guard::(!left_eq));
                 mk_and srk (right.guard::(!right_eq))]
    in
    { guard; transform }

  (* Canonical names for post-state symbols.  Having canonical names
     simplifies equality testing and widening. *)
  let post_symbol =
    Memo.memo (fun sym ->
        match Var.of_symbol sym with
        | Some var ->
          mk_symbol srk ~name:(Var.show var ^ "'") (Var.typ var :> typ)
        | None -> assert false)

  let to_transition_formula tr =
    let (tr_symbols, post_def) =
      M.fold (fun var term (symbols, post_def) ->
          let pre_sym = Var.symbol_of var in
          let post_sym = post_symbol pre_sym in
          let post_term = mk_const srk post_sym in
          ((pre_sym,post_sym)::symbols,
           (mk_eq srk post_term term)::post_def))
        tr.transform
        ([], [])
    in
    let body =
      mk_and srk (tr.guard::post_def)
      |> rewrite srk
        ~up:(SrkSimplify.simplify_terms_rewriter srk % Nonlinear.simplify_terms_rewriter srk)
    in
    let exists =
      let post_symbols =
        List.fold_left
          (fun set (_, sym') -> Symbol.Set.add sym' set)
          Symbol.Set.empty
          tr_symbols
      in
      fun x ->
      match Var.of_symbol x with
      | Some _ -> true
      | None -> Symbol.Set.mem x post_symbols
    in
    TransitionFormula.make ~exists body tr_symbols

  let contains_havoc tr = 
    M.fold (fun _ rhs acc -> 
      if acc then acc 
      else begin 
        Symbol.Set.fold 
          (fun s acc -> 
            match Var.of_symbol s with 
            | Some _ -> acc 
            | None -> true || acc) (Syntax.symbols rhs) false
      end
      ) tr.transform false    

  let domain =
    let open Iteration in
    let open SolvablePolynomial in
    ref (module ProductWedge(SolvablePolynomial)(WedgeGuard) : PreDomain)

  let star tr =
    let (module D) = !domain in
    let tf = to_transition_formula tr in
    let iter = D.abstract srk tf in
    let tr_symbols = TransitionFormula.symbols tf in
    let transform =
      List.fold_left (fun tr (pre, post) ->
          match Var.of_symbol pre with
          | Some v -> M.add v (mk_const srk post) tr
          | None -> assert false)
        M.empty
        tr_symbols
    in
    let loop_counter_sym = mk_symbol srk ~name:"K" `TyInt in
    let loop_counter = mk_const srk loop_counter_sym in
    let closure =
      mk_and srk [D.exp srk tr_symbols loop_counter iter;
                  mk_leq srk (mk_real srk QQ.zero) loop_counter]
    in
    { transform = transform;
      guard = closure }

  let zero =
    { transform = M.empty; guard = mk_false srk }

  let one =
    { transform = M.empty; guard = mk_true srk }

  let is_zero tr =
    match Formula.destruct srk tr.guard with
    | `Fls -> true
    | _ -> false

  let is_one tr =
    match Formula.destruct srk tr.guard with
    | `Tru -> M.is_empty tr.transform
    | _ -> false

  let widen x y =
    (* Introduce fresh symbols for variables in the transform of x/y, then
       abstract x and y to a wedge over pre-symbols and these fresh symbols.
       Widen in the wedge domain, then covert back to a formula. *)
    let (transform, post_sym) =
      let add (map, post) var =
        if M.mem var map then
          (map, post)
        else
          let name = Var.show var ^ "'" in
          let sym = mk_symbol srk ~name (Var.typ var :> typ) in
          (M.add var (mk_const srk sym) map, Symbol.Set.add sym post)
      in
      BatEnum.fold
        add
        (BatEnum.fold add (M.empty, Symbol.Set.empty) (M.keys y.transform))
        (M.keys x.transform)
    in
    let exists sym =
      match Var.of_symbol sym with
      | Some _ -> true
      | None -> Symbol.Set.mem sym post_sym
    in
    let to_wedge z =
      let eqs =
        M.fold (fun var term eqs ->
            let term' =
              if M.mem var z.transform then
                M.find var z.transform
              else
                mk_const srk (Var.symbol_of var)
            in
            (mk_eq srk term term')::eqs)
          transform
          []
      in
      mk_and srk (z.guard::eqs)
      |> Wedge.abstract ~exists srk
    in
    let guard =
      Wedge.widen (to_wedge x) (to_wedge y)
      |> Wedge.to_formula
    in
    { transform; guard }

  let widen x y =
    if is_zero x then y
    else if is_zero y then x
    else widen x y

  (* alpha equivalence - only works for normalized transitions! *)
  exception Not_normal
  let equiv x y =
    let sigma =
      let map =
        M.fold (fun v rhs m ->
            match Term.destruct srk rhs,
                  Term.destruct srk (M.find v y.transform) with
            | `App (a, []), `App (b, []) -> Symbol.Map.add a (mk_const srk b) m
            | _ -> raise Not_normal)
          x.transform
          Symbol.Map.empty
      in
      fun sym ->
        try Symbol.Map.find sym map
        with Not_found -> mk_const srk sym
    in
    let x_guard = substitute_const srk sigma x.guard in
    let equiv = SrkSimplify.simplify_terms srk (mk_iff srk x_guard y.guard) in
    match Wedge.is_sat srk (mk_not srk equiv) with
    | `Unsat -> true
    | _ -> false

  let equiv x y =
    try equiv x y
    with | Not_found -> false
         | Not_normal -> false

  let equal x y =
    compare x y = 0
    || is_zero x && (Smt.is_sat srk y.guard) = `Unsat
    || is_zero y && (Smt.is_sat srk x.guard) = `Unsat
    || equiv x y

  let exists p tr =
    let transform = M.filter (fun k _ -> p k) tr.transform in
    let rename =
      Memo.memo (fun sym ->
          mk_symbol srk ~name:(show_symbol srk sym) (typ_symbol srk sym))
    in
    let sigma sym =
      let sym' = match Var.of_symbol sym with
        | Some v -> if p v then sym else rename sym
        | None -> sym
      in
      mk_const srk sym'
    in
    { transform = M.map (substitute_const srk sigma) transform;
      guard = substitute_const srk sigma tr.guard }

  let mem_transform x tr = M.mem x tr.transform
  let get_transform x tr = M.find x tr.transform
  let transform tr = M.enum tr.transform
  let guard tr = tr.guard

  let get_post_model ?(solver=Smt.mk_solver C.context) m f = 
    let _ = Smt.Solver.reset solver in 
    let f_guard = guard f in 
    let replacer (sym : Syntax.symbol) = 
      if Var.of_symbol sym == None then Syntax.mk_const C.context sym 
      else mk_real C.context @@ Interpretation.real m sym 
      in 
    let f_guard' = Syntax.substitute_const C.context replacer f_guard in 
    let f_transform = transform f in 
    let symbols = Syntax.symbols f_guard' |> Symbol.Set.elements in 
    match Smt.get_model ~symbols:(symbols) C.context ~solver:(solver)  f_guard' with 
    | `Sat skolem_model -> 
      let post_model = BatEnum.fold (fun m' (lhs, rhs) ->  
        let sub_expr = Syntax.substitute_const C.context replacer rhs in 
        let lhs_symbol =  Var.symbol_of lhs in
        let sub_val = Interpretation.evaluate_term skolem_model sub_expr in 
        Interpretation.add lhs_symbol (`Real sub_val) m'
      ) m f_transform in Some post_model 
    | _ -> None 

  let rec destruct_and srk phi =
    match Formula.destruct srk phi with
    | `And xs -> List.concat_map (destruct_and srk) xs
    | _ -> [phi]

  (* helper method for interpolate/extrapolate procedures. creates fresh copies of skolem variables in tr *)
  let rename_skolems tr =
    let fresh_skolem =
      Memo.memo (fun sym ->
          match Var.of_symbol sym with
          | Some _ -> mk_const srk sym
          | None ->
              let name = show_symbol srk sym in
              let typ = typ_symbol srk sym in
              mk_const srk (mk_symbol srk ~name typ))
    in
    { transform = M.map (substitute_const srk fresh_skolem) tr.transform;
      guard = substitute_const srk fresh_skolem tr.guard }


  let interpolate_unsat_core solver' trs post guards core = 
    let refresh s = Smt.Solver.reset s; s 
    in let core_symbols =
      List.fold_left (fun core phi ->
          match Formula.destruct srk phi with
          | (`Proposition (`App (s, []))) -> Symbol.Set.add s core
          | _ -> assert false)
        Symbol.Set.empty
        core
    in
    let (itp, _) =
      List.fold_right2 (fun tr guard (itp, post) ->
          let subst sym =
            match Var.of_symbol sym with
            | Some var ->
              if M.mem var tr.transform then
                M.find var tr.transform
              else
                mk_const srk sym
            | None -> mk_const srk sym
          in
          let post' = substitute_const srk subst post in
          let reduced_guard =
            List.filter_map (fun (indicator, guard) ->
                if Symbol.Set.mem indicator core_symbols then
                  Some (mk_not srk guard)
                else
                  None)
              guard
          in
          let wp =
            (mk_not srk (mk_or srk (post'::reduced_guard)))
            |> Quantifier.mbp srk ~solver':(refresh solver') (fun s -> Var.of_symbol s != None)
            |> mk_not srk
          in
          (wp::itp, wp))
        trs
        guards
        ([post], post)
    in `Valid (List.tl itp)  


  let interpolate_query ?(solver=Smt.mk_solver C.context) trs post sat_callback unsat_callback = 
    let _ = Smt.Solver.reset solver in 
    (* Break guards into conjunctions, associate each conjunct with an indicator *)
    let guards =
      List.map (fun tr ->
          List.map
            (fun phi -> (mk_symbol srk `TyBool, phi))
            (destruct_and srk tr.guard))
        trs in 
    let indicators, indicator_symbols =
      List.concat_map (List.map (fun (s, _) -> mk_const srk s)) guards,
      List.concat_map (List.map fst) guards |> Symbol.Set.of_list
    in
    let subscript_tbl = Hashtbl.create 991 in
    let ss_inv = Hashtbl.create 991 in 
    let sst = Hashtbl.create 991 in 
    let subscript sym =
      try
        Hashtbl.find subscript_tbl sym
      with Not_found -> mk_const srk sym
    in
    (* Convert tr into a formula, and simultaneously update the subscript
       table *)
    let to_ss_formula tr guards =
      let ss_guards =
        List.map (fun (indicator, guard) ->
            mk_if srk
              (mk_const srk indicator)
              (substitute_const srk subscript guard))
          guards
      in
      let (ss, phis) =
        M.fold (fun var term (ss, phis) ->
            let var_sym = Var.symbol_of var in
            let var_ss_sym = mk_symbol srk (Var.typ var :> typ) in
            let var_ss_term = mk_const srk var_ss_sym in
            let term_ss = substitute_const srk subscript term in
            ((var_sym, var_ss_sym, var_ss_term)::ss,
             mk_eq srk var_ss_term term_ss::phis))
          tr.transform
          ([], ss_guards)
      in
      List.iter (fun (k, l, v) -> 
        Hashtbl.add subscript_tbl k v;
        Hashtbl.add ss_inv l k;
        Hashtbl.add sst k l) ss;
      mk_and srk phis
    in
    (* gather all symbols into a list, while adding formulas to the solver object *) 
    let symbols = List.fold_left 
      (fun symbols (tr, guard) ->
        let f = to_ss_formula tr guard in 
          Smt.Solver.add solver [f];
          (Syntax.symbols f) :: symbols)
       [] (List.combine trs guards) 
    (* subscript the symbols in the `post` formula, as well *) in 
    let target = substitute_const srk subscript (mk_not srk post) in
    let symbols = (Syntax.symbols target) :: symbols 
      |> List.rev
      |> List.map (fun ss -> Symbol.Set.diff ss indicator_symbols) in 
      Smt.Solver.add solver [target];
      match Smt.Solver.get_unsat_core_or_model solver indicators with 
        | `Sat m ->  
          (sat_callback m symbols sst ss_inv)
        | `Unsat core -> (unsat_callback trs post guards core)
        | `Unknown -> `Unknown 


  let interpolate ?(solver=Smt.mk_solver C.context) ?(qflia_solver=(Smt.mk_solver ~theory:"QF_LIA" srk)) trs post =
    Smt.Solver.reset solver;
    let trs = List.map rename_skolems trs in 
    interpolate_query ~solver:solver trs post (fun _ _ _ _ -> `Invalid) @@ interpolate_unsat_core qflia_solver

  let interpolate_or_concrete_model ?(solver=Smt.mk_solver C.context) ?(qflia_solver=(Smt.mk_solver ~theory:"QF_LIA" srk)) trs post = 
    (* subst_model: rename skolem constants back to their appropriate names using reverse subscript table *)
    Smt.Solver.reset solver;
    let trs = List.map rename_skolems trs in 
    let sat_model model (symbols: Symbol.Set.t list) ss ss_inv = 
        let m = 
          List.fold_left (fun m' symbols -> 
            Symbol.Set.fold (fun s m -> 
              (* the provided model is over both subscripted vocabulary and original vocabulary *)
              begin match Hashtbl.find_opt ss_inv s with 
              | Some s' -> (* subscripted variable *)
                Interpretation.add s' (Interpretation.value model s) m
              |  None -> (* non-subscripted; query directly *)
                Interpretation.add s (Interpretation.value model s)  m 
              end) symbols m'
          ) (Interpretation.wrap srk (fun s -> 
              match Hashtbl.find_opt ss s with 
              | Some sss -> Interpretation.value model sss 
              | None -> `Real (Mpqf.of_int 47))) (*(Interpretation.wrap srk (fun s -> 
                match Hashtbl.find_opt ss s with 
                | Some sss -> Interpretation.value model sss 
                | None -> Interpretation.value model s))*) (*(Interpretation.empty srk)*) symbols in 
          Printf.printf "hashtable length: %d\n" (Hashtbl.length ss_inv);
          Interpretation.pp Format.std_formatter m; 
          Format.print_flush ();
      (* symbols is a list of subscripted symbols arranged in left-to-right order. 
         folding over this in left-to-right order amounts to forward concrete execution. *)
      `Invalid m
   (* let sat_model model ss_inv = 
      let e = Interpretation.enum model in 
      let m' = BatEnum.fold 
        (fun m (s, v) -> 
          match Var.of_symbol s with 
            | Some _ -> (* s is associated with some variable *) 
              Interpretation.add s v m 
            | None -> (* s is e.g. trip count variable or havoc *)
              begin 
                try 
                  let pre_symbol = Hashtbl.find ss_inv s 
                  in Interpretation.add pre_symbol v m
                with Not_found -> m 
              end) (Interpretation.empty C.context) e
      in 
      logf ~level:`always "interpolate: got model, model is: %a\n" (Interpretation.pp) m';
      `Invalid m'
    *) in interpolate_query ~solver:solver trs post sat_model @@ interpolate_unsat_core qflia_solver


  let extrapolate ?(solver=Smt.mk_solver srk) t1 t2 t3 level : [`Sat of (C.t formula * C.t formula) | `Unsat ] =
    let t1 = rename_skolems t1 
    in let t2 = rename_skolems t2 
    in let t3 = rename_skolems t3 
    in let subscript subscript_tbl sym =
      try
        Hashtbl.find subscript_tbl sym
      with Not_found -> 
        mk_const srk sym
    in
    (* Convert tr into a formula, and simultaneously update the subscript
       table *)
    let to_ss_formula tr subscript_tbl reverse_subscript_tbl =
      let ss_guard = substitute_const srk (subscript subscript_tbl) (guard tr)
      in let (ss, phis) =
        M.fold (fun var term (ss, phis) ->
            let var_sym = Var.symbol_of var in
            let var_ss_sym = mk_symbol srk (Var.typ var :> typ) in
            let var_ss_term = mk_const srk var_ss_sym in
            let term_ss = substitute_const srk (subscript subscript_tbl) term in
            ((var_sym, var_ss_term, var_ss_sym)::ss,
             (mk_eq srk var_ss_term term_ss)::phis))
          tr.transform
          ([], [ ss_guard ])
      in
      List.iter (fun (k, v, l) -> 
        Hashtbl.add subscript_tbl k v; Hashtbl.add reverse_subscript_tbl l k) ss;
      mk_and srk phis, Hashtbl.copy reverse_subscript_tbl
    in let subscript_tbl = Hashtbl.create 991 
    in let reverse_subscript_tbl = Hashtbl.create 991 
    in let ss_t1, reverse_subscript_tbl1 = to_ss_formula t1 subscript_tbl reverse_subscript_tbl 
    in let ss_t2, reverse_subscript_tbl2 = to_ss_formula t2 subscript_tbl reverse_subscript_tbl
    in let ss_t3, _ = to_ss_formula t3 subscript_tbl reverse_subscript_tbl
    in let conj = mk_and srk [ss_t1; ss_t2; ss_t3]
    in let is_global t x = 
      try 
        begin match Var.of_symbol (Hashtbl.find t x) with 
        | None -> false 
        | Some v -> 
          if Var.is_global v then begin 
            Printf.printf "symbol %s is global\n" (Syntax.show_symbol srk (Hashtbl.find reverse_subscript_tbl x)); true 
          end else false
        end
      with Not_found -> false  
    in let symbols_t1 = Syntax.symbols ss_t1
    in let symbols_t2 = Syntax.symbols ss_t2
    in let symbols_t3 = Syntax.symbols ss_t3  
    in let symbols_t1_t2 =
      Syntax.symbols ss_t1 (* symbols in t1 that are either globals _and_ in t2 are preserved during projection *)
        |> Symbol.Set.filter 
            (fun x -> (is_global reverse_subscript_tbl1 x))
    in let symbols_t3_t2 = 
        symbols_t3 (* symbols in t3 that are globals _and_ in t2, t1 are preserved during projection *)
        |> Symbol.Set.filter (fun x -> (is_global reverse_subscript_tbl2 x) && (Symbol.Set.mem x symbols_t2))
    (*in let _ = 
      Printf.printf "extrapolate: preserved symbols for t1,t2: ";
      let f x = x 
      |> Symbol.Set.elements 
      |> List.iter (fun s -> 
        try 
          Hashtbl.find reverse_subscript_tbl s 
          |> Syntax.show_symbol srk 
          |> Printf.printf " %s " 
        with Not_found -> ()); Printf.printf "\n" in 
      symbols_t1_t2  |> f; 
      Printf.printf "extrapolate: presreved symbols for t2,t3: ";
      symbols_t3_t2 |> f
    *)in let symbols_conj = Symbol.Set.union symbols_t1 (Symbol.Set.union symbols_t2 symbols_t3)
    (*in let symbols_printer symbs = 
      List.iter (fun x -> 
        Printf.printf " %s (= %s);" 
        (Syntax.show_symbol srk x) (let s = try Hashtbl.find reverse_subscript_tbl x |> Syntax.show_symbol srk with Not_found -> "NONE" in s)) symbs 
    *)
    in
    let extrapolate_project srk (f1: 'a formula) (f3: 'a formula) symbols_f1 symbols_f3 all_symbols model = 
      let open Polyhedron in 
      (* first do NNF conversion on f1, f3 before computing their implicants *)
      let nnf_rewriter = Syntax.nnf_rewriter srk in
      let f1 = Syntax.rewrite srk ~down:(nnf_rewriter) f1 in 
      let f3 = Syntax.rewrite srk ~down:(nnf_rewriter) f3 in 
      let implicant_o1 = Interpretation.select_implicant model f1 in
      let implicant_o2 = Interpretation.select_implicant model f3 in 
        match implicant_o1, implicant_o2 with 
        | Some f1, Some f2 ->
          let cube = of_cube srk (f1@f2) in
          let value_of_coord = (* coord (int) -> x (symbol) -> m[x] (value in R) *)
            fun coord ->
              Syntax.symbol_of_int coord 
              |> Interpretation.real model
          in let xs_f1 = 
            Symbol.Set.diff all_symbols symbols_f1 
            |> Symbol.Set.elements 
            |> List.map Syntax.int_of_symbol  
          in let xs_f3 = 
            Symbol.Set.diff all_symbols symbols_f3 
            |> Symbol.Set.elements 
            |> List.map Syntax.int_of_symbol 
          in let xs_f1f3 = 
            Symbol.Set.diff all_symbols (Symbol.Set.union symbols_f1 symbols_f3)
            |> Symbol.Set.elements 
            |> List.map Syntax.int_of_symbol 
          in let f1_projected = local_project value_of_coord xs_f1 cube
          in let f3_projected = local_project value_of_coord xs_f3 cube
          in let f1f3_projected = local_project value_of_coord xs_f1f3 cube 
          in
            (cube_of srk f1_projected |> Syntax.mk_and srk, cube_of srk f3_projected |> Syntax.mk_and srk, 
            cube_of srk f1f3_projected |> Syntax.mk_and srk)
        | _ -> failwith "error extrapolating: select_implicant returned None"
        in 
    (*Printf.printf "extrapolate: before SMT query \n";
     Printf.printf "extrapolate: ss_t1: ";
     Syntax.pp_expr srk Format.std_formatter ss_t1;
     Format.print_flush ();
     Printf.printf "\n\nextrapolate: ss_t2: ";
     Syntax.pp_expr srk Format.std_formatter ss_t2;
          Format.print_flush ();
     Printf.printf "\n\nextrapolate: ss_t3: ";
     Syntax.pp_expr srk Format.std_formatter ss_t3;
          Format.print_flush ();
     Printf.printf "\n\nextrapolate: ss_conj symbols: ";
     symbols_printer (symbols_conj |> Symbol.Set.elements);
          Format.print_flush();
     Printf.printf "\n\nextrapolate: symbol t1 - t2: ";
     symbols_printer (symbols_t1_t2 |> Symbol.Set.elements);
          Format.print_flush();
     Printf.printf "\n\nextrapolate: symbol t3 - t2: ";
      symbols_printer (symbols_t3_t2 |> Symbol.Set.elements);
          Format.print_flush();
     Printf.printf "\n------------ SMT query in extrapolate ------------\n";*)
     match Smt.get_model ~solver:solver ~symbols:(symbols_conj |> Symbol.Set.elements) srk conj with 
      | `Sat m -> 
        (*Printf.printf "extrapolate: result is SAT, got model\n";*)
        (*Interpretation.pp Format.std_formatter m ;
        Format.print_flush ();*)
        let pre_, post_, prepost = extrapolate_project srk ss_t1 ss_t3 symbols_t1_t2 symbols_t3_t2 symbols_conj m in 
        (*Printf.printf "\npre extrapolant: ";
        Syntax.pp_expr srk Format.std_formatter pre_;
        Format.print_flush();
        Printf.printf "\npost extrapolant: ";
        Syntax.pp_expr srk Format.std_formatter post_;
        Format.print_flush();
        Printf.printf "\n--------------------------\n";*)
          (* reverse-rename *)
          let reverse_substitute symb = 
            try 
              let sym = Hashtbl.find reverse_subscript_tbl symb in 
                mk_const srk sym 
            with Not_found -> mk_const srk symb
          in 
          let ex1 = (substitute_const srk (reverse_substitute) pre_) in 
          let ex2 = (substitute_const srk (reverse_substitute) post_) in 
          let ex13 = (substitute_const srk (reverse_substitute) prepost) in 
          Printf.printf "\npre extrapolant after renaming (level %d): " level;
          Syntax.pp_expr srk Format.std_formatter ex1;
          Format.print_flush();
          Printf.printf "\npost extrapolant after renaming (level %d): " level;
          Syntax.pp_expr srk Format.std_formatter ex2;
          Format.print_flush();
          Printf.printf "\nfootprint extrapolant (level %d): \n" level;  
          Syntax.pp_expr srk Format.std_formatter ex13;
          Format.print_flush();
          Printf.printf "\n--------------------------\n";
          `Sat (ex1, ex2) 
      | `Unknown -> failwith "extrapolate status unknown"
      | `Unsat ->  `Unsat 

  let valid_triple phi path post =
    let path_not_post = List.fold_right mul path (assume (mk_not srk post)) in
    match Smt.is_sat srk (mk_and srk [phi; path_not_post.guard]) with
    | `Sat -> `Invalid
    | `Unknown -> `Unknown
    | `Unsat -> `Valid

  let feasible_triple phi path post = 
    let path_post = List.fold_right mul path (assume (post)) in 
    match Smt.is_sat srk (mk_and srk [phi; path_post.guard]) with
    | `Sat -> `Feasible 
    | `Unknown -> `Unknown 
    | `Unsat -> `Infeasible

  let check_reverse_consecution phi tr (post: C.t formula) = 
    let pre = mul (assume phi) tr in 
    let pre_formula = to_transition_formula pre |> TransitionFormula.formula in 
      Printf.printf "checking implication  P->Q \n";
      Printf.printf "formula P: ";
      Syntax.pp_expr_unnumbered srk Format.std_formatter pre_formula;
      Format.print_flush ();
      Printf.printf "\nformula Q: ";
      Syntax.pp_expr_unnumbered srk Format.std_formatter post;
      Format.print_flush ();
      Printf.printf  "\n";
      Smt.entails C.context post pre_formula 

  let check_consecution phi tr (post: C.t formula) = 
    let pre = mul (assume phi) tr in 
      let pre_formula = to_transition_formula pre |> TransitionFormula.formula in 
      Smt.entails C.context pre_formula post     

  let defines tr =
    M.fold
      (fun var _ defs -> var::defs)
      tr.transform
      []

  let uses tr =
    M.fold
      (fun _ term uses ->
         Symbol.Set.union (symbols term) uses)
      tr.transform
      (symbols tr.guard)
    |> Symbol.Set.enum
    |> BatEnum.filter_map Var.of_symbol
    |> BatList.of_enum

  let abstract_post pre tr =
    let srk = C.context in
    let man = SrkApron.get_manager pre in
    let exists x = Var.of_symbol x != None in
    let fresh =
      Memo.memo (fun sym -> mk_const srk (mk_symbol srk (typ_symbol srk sym)))
    in
    let tr_subst expr =
      substitute_const srk (fun sym ->
          match Var.of_symbol sym with
          | Some v when mem_transform v tr -> fresh sym
          | _ -> mk_const srk sym)
        expr
    in
    let transform_formula =
      transform tr
      /@ (fun (lhs, rhs) ->
          (mk_eq srk (mk_const srk (Var.symbol_of lhs)) (tr_subst rhs)))
      |> BatList.of_enum
    in
    mk_and srk ((tr_subst (SrkApron.formula_of_property pre))
                :: (tr_subst tr.guard)
                :: transform_formula)
    |> Nonlinear.linearize srk
    |> rewrite srk ~down:(nnf_rewriter srk)
    |> Abstract.abstract ~exists srk man

  let linearize tr =
    let (transform, defs) =
      M.fold (fun var t (transform, defs) ->
          let (pure_t, t_defs) =
            SrkSimplify.purify srk (Nonlinear.uninterpret srk t)
          in
          let new_defs =
            Symbol.Map.enum t_defs
            /@ (fun (v,t) ->
              match Expr.refine srk t with
              | `ArithTerm t ->
                 mk_eq srk (mk_const srk v) (Nonlinear.interpret srk t)
              | _ -> assert false)
            |> BatList.of_enum
          in
          (M.add var pure_t transform, new_defs@defs))
        tr.transform
        (M.empty, [])
    in
    let guard =
      Nonlinear.linearize srk (mk_and srk (tr.guard::defs))
    in
    { transform; guard }
end
