open Srk
open OUnit
open Syntax
open Test_pervasives

module V = struct
  type t = string

  let typ_table = Hashtbl.create 991
  let sym_table = Hashtbl.create 991
  let rev_sym_table = Hashtbl.create 991

  let register_var name typ =
    assert (not (Hashtbl.mem typ_table name));
    let sym = Ctx.mk_symbol ~name (typ :> typ) in
    Hashtbl.add typ_table name typ;
    Hashtbl.add sym_table name sym;
    Hashtbl.add rev_sym_table sym name

  let pp = Format.pp_print_string
  let show x = x
  let typ = Hashtbl.find typ_table
  let compare = Stdlib.compare
  let symbol_of = Hashtbl.find sym_table
  let of_symbol sym =
    if Hashtbl.mem rev_sym_table sym then
      Some (Hashtbl.find rev_sym_table sym)
    else
      None
  let is_global _ = false 
  let make_var _ _ = failwith "" 
  let prophesize _ = failwith "" 
  let var_of_prophecy_var = failwith "" 
  let prophecy_var_of_var = failwith "" 
end
module T = Transition.Make(Ctx)(V)

let () =
  T.domain := (module Iteration.Split(val !T.domain))

let () =
  V.register_var "i" `TyInt;
  V.register_var "j" `TyInt;
  V.register_var "k" `TyInt;
  V.register_var "n" `TyInt;
  V.register_var "x" `TyInt;
  V.register_var "y" `TyInt;
  V.register_var "z" `TyInt;
  V.register_var "w" `TyInt

let x = Ctx.mk_const (V.symbol_of "x")
let y = Ctx.mk_const (V.symbol_of "y")
let z = Ctx.mk_const (V.symbol_of "z")
let i = Ctx.mk_const (V.symbol_of "i")
let j = Ctx.mk_const (V.symbol_of "j")
let k = Ctx.mk_const (V.symbol_of "k")
let n = Ctx.mk_const (V.symbol_of "n")
let w = Ctx.mk_const (V.symbol_of "w")

let assert_post tr phi =
  let not_post =
    rewrite srk ~down:(nnf_rewriter srk) (Ctx.mk_not phi)
  in
  let pathcond =
    T.guard (T.mul tr (T.assume not_post))
  in
  if Wedge.is_sat srk pathcond != `Unsat then
    assert_failure (Printf.sprintf "%s\n is not a post-condition of\n%s"
                      (Formula.show srk phi)
                      (T.show tr))

let assert_equal_tr = assert_equal ~cmp:T.equal ~printer:T.show

let mk_block = BatList.reduce T.mul

let mk_if cond bthen belse =
  T.add
    (mk_block ((T.assume cond)::bthen))
    (mk_block ((T.assume (Ctx.mk_not cond))::belse))

let mk_while cond body =
  T.mul
    (T.star (mk_block ((T.assume cond)::body)))
    (T.assume (Ctx.mk_not cond))

let degree1 () =
  let tr =
    let open Infix in
    mk_block [
      T.assign "i" (int 0);
      mk_while (i < n) [
        T.assign "i" (i + (int 1));
      ]
    ]
  in
  let post =
    let open Infix in
    n < (int 0) || i = n
  in
  assert_post tr post

let degree2 () =
  let tr =
    let open Infix in
    mk_block [
      T.assume ((int 0) <= n);
      T.assign "i" (int 0);
      T.assign "x" (int 0);
      mk_while (i < n) [
        T.assume ((int 0) <= n); (* Needed w/o forward inv gen *)
        T.assign "i" (i + (int 1));
        T.assign "j" (int 0);
        mk_while (j < n) [
          T.assign "j" (j + (int 1));
          T.assign "x" (x + (int 1));
        ]
      ]
    ]
  in
  let post =
    let open Infix in
    x = n*n
  in
  assert_post tr post

let degree3 () =
  let tr =
    let open Infix in
    mk_block [
      T.assume ((int 0) <= n);
      T.assign "i" (int 0);
      T.assign "x" (int 0);
      mk_while (i < n) [
        T.assume ((int 0) <= n); (* Needed w/o forward inv gen *)
        T.assign "i" (i + (int 1));
        T.assign "j" (int 0);
        mk_while (j < n) [
        T.assume ((int 0) <= n); (* Needed w/o forward inv gen *)
          T.assign "j" (j + (int 1));
          T.assign "k" (int 0);
          mk_while (k < n) [
            T.assign "k" (k + (int 1));
            T.assign "x" (x + (int 1));
          ]
        ]
      ]
    ]
  in
  let post =
    let open Infix in
    x = n*n*n
  in
  assert_post tr post

let gauss_sum () =
  let tr =
    let open Infix in
    mk_block [
      T.assume ((int 0) <= n);
      T.assign "i" (int 0);
      T.assign "x" (int 0);
      mk_while (i < n) [
        T.assume ((int 0) <= n); (* Needed w/o forward inv gen *)
        T.assume ((int 0) <= i); (* Needed w/o forward inv gen *)
        T.assign "j" i;
        T.assign "i" (i + (int 1));
        mk_while (j < n) [
          T.assign "j" (j + (int 1));
          T.assign "x" (x + (int 1));
        ]
      ]
    ]
  in
  let post =
    let open Infix in
    (int 2) * x <= (n*(n+(int 1)))
  in
  assert_post tr post

let inc_nondet () =
  let tr =
    let open Infix in
    mk_block [
      T.assign "x" (int 0);
      T.assign "y" (int 0);
      T.assign "z" (int 0);
      mk_while (z < n) [
        T.assign "z" (z + (int 1));
        mk_if (z mod (int 2) = (int 0)) [
          T.assign "x" (x + (int 1));
        ] [
          T.assign "y" (y + (int 1));
        ]
      ]
    ]
  in
  let post =
    let open Infix in
    n < (int 0) || x + y = n
  in
  assert_post tr post

let split () =
  let tr =
    let open Infix in
    mk_block [
      T.assume ((int 0) <= n);
      T.assign "x" (int 0);
      T.assign "y" (int 0);
      T.havoc ["z"];
      mk_while (x + y < n) [
        mk_if (z <= (int 0)) [
          T.assign "x" (x + (int 1));
        ] [
          T.assign "y" (y + (int 1));
        ]
      ]
    ]
  in
  let post =
    let open Infix in
    x = n || y = n
  in
  assert_post tr post

let split2 () =
  let tr =
    let open Infix in
    mk_block [
      T.assign "n" (int 100);
      T.assign "x" (int 0);
      T.assign "y" (int 0);
      T.havoc ["z"];
      mk_while (x + y < n) [
        mk_if (x < (int 50)) [
          T.assign "x" (x + (int 1));
        ] [
          T.assign "y" (y + (int 1));
        ]
      ]
    ]
  in
  let post =
    let open Infix in
    x = y
  in
  assert_post tr post
(*
let check_extrapolate test_name tr1 tr2 tr3 = 
  match T.contextualize tr1 tr2 tr3 0 with 
      | `Sat (f1, f2) -> 
        Printf.printf "extrapolate: SAT, formulas: \n";
        Syntax.pp_expr_unnumbered srk Format.std_formatter f1;
        Format.print_flush ();
        Printf.printf " (E1)\n";
        Syntax.pp_expr_unnumbered srk Format.std_formatter f2;
        Format.print_flush ();
        Printf.printf " (E2)\n";
        Printf.printf "checking if {T}tr1{f1} is feasible...\n";
        begin match T.valid_triple (mk_true srk) [tr1] f1 with 
        | `Valid -> 
          Printf.printf " checking consecution property of {f1}tr2{f2}...\n";
          begin match T.feasible_triple f1 [tr2 ] f2 with 
          | `Feasible ->
            Printf.printf "  checking if {f2}tr3{T} is feasible...\n";
            begin match T.valid_triple f2 [tr2]  (mk_true srk) with
            | `Valid -> 
              Printf.printf "%s  ...all checks done. test passed [OK]\n" test_name
            | _ -> assert_failure @@ test_name ^ "   error: check 3 failed\n"
            end
          | _ -> assert_failure @@ test_name ^ "  error: check 2 failed\n"
          end
        | _ -> assert_failure @@ test_name ^ " error: check 1 failed\n" 
        end 
      | `Unsat -> 
        assert_failure @@ test_name ^ "extrapolate: UNSAT\n"

let extrapolate1 () = 
  let open Infix in 
  let tr1 = 
    mk_block [
      T.havoc ["x"];
      T.assume ((int 0) < x);
      T.assign "y" x;
      T.assign "n" (int 100);
      T.assign "i" (int 103);
      T.assign "j" ((int 105));
      T.assign "k" j;
    ]
  in let tr2 = 
    mk_block [
      T.assume ((int 0 ) < z);
      T.assign "z" (x + (int 1));
      T.assign "w" (z + (int 3));
      T.assign "n" (n + (int 1)); 
      T.assign "k" (i + k + (int 1));
    ]
  in let tr3 = 
    mk_block [
      T.assume ((int 0) < x);
      T.assume ((int 0) < k);
      T.assign "k" (w + (int 4));
    ]
  in 
    Printf.printf "extrapolate1--------------------------------------------\n";
    check_extrapolate "extrapolate1" tr1 tr2 tr3

let extrapolate2 () = 
  let open Infix in 
  let tr1 = 
    mk_block [
      T.havoc ["x"];
      T.assume ((int 0) <= x);
      T.assign "y" (int 0)
    ]
  in let tr2 = 
    mk_block [
      T.assign "y" (y + (int 1));
      T.assign "z" (y + (int 3));
      T.assign "x" (x + (int 1))
    ]
  in let tr3 = 
    mk_block [
      T.assume ((int 0) < x);
      T.assume ((int 0) < y);
      T.assume (y < z);
      T.assign "k" (x + (int 10))
    ]
  in 
  Printf.printf "extrapolate2-------------------------------------------\n";
  check_extrapolate "extrapolate2" tr1 tr2 tr3

let extrapolate3 () = 
  let open Infix in 
  let tr1 = 
    mk_block [
      T.havoc ["x"];
      T.assume ((int 0) < x);
      T.assign "y" (int 0)
    ]
  in let tr2 = 
    mk_block [
      T.assign "z" ((int 0) + y);
      T.assume ((int 0) <= y);
      T.assume (((int 0) < x) || (x < (int 0)))
    ]
  in let tr3 = 
    mk_block [
      T.assume ((int 0) < x);
      T.assign "z" ((int 1) + x);
      T.assume ((int 0) < z);
      T.assign "y" ((int 1) + y);
      T.assume ((int 0) < y)
    ]
  in 
  Printf.printf "extrapolate3-----------------------------\n";
  check_extrapolate "extrapolate3" tr1 tr2 tr3
*)
let equal1 () =
  (*let open Infix in *)
  let tr1 =
    mk_block [
      T.havoc ["x"];
      T.assign "y" x;
(*      T.assign "x" (x + (int 12));
      T.assign "z" (int 13) *)
    ]
  in
  let _ = 
    let tr1_formula = T.to_transition_formula tr1 |> TransitionFormula.formula in 
    let tr1_symbols = Syntax.symbols tr1_formula |> Symbol.Set.elements in 
      List.iter (fun symb -> Syntax.show_symbol srk symb |> Printf.printf "equal1: tr1 symbol: %s\n") tr1_symbols 
  in
  let tr2 =
    mk_block [
      T.havoc ["y"];
      T.assign "x" y;
    ]
  in
  assert_equal_tr tr1 tr2

let assert_valid pre tr post =
  if (T.valid_triple pre [tr] post) != `Valid then
    assert_failure (Printf.sprintf "Invalid Hoare triple: {%s} %s {%s}"
                      (Formula.show srk pre)
                      (T.show tr)
                      (Formula.show srk post))

let check_interpolant path itp dst =
  let rec go path itp =
    match path, itp with
    | tr::path, pre::post::itp ->
      Printf.printf "interpolant: ";
      Syntax.pp_expr_unnumbered srk Format.std_formatter pre;
      Format.print_flush ();
      Printf.printf "\ninterpolant: ";
      Syntax.pp_expr_unnumbered srk Format.std_formatter pre;
      Format.print_flush ();
      Printf.printf "\n";
      assert_valid pre tr post;
      go path (post::itp)
    | [], [final_itp] -> 
        assert_valid final_itp (T.assume (dst)) (mk_true srk)
    | _, _ -> 
    Printf.printf "path length %d, interpolant length %d\n" (List.length path) (List.length itp);
    assert false
  in
  go path (Ctx.mk_true::itp)

let interpolate1 () =
  (* 
program:
    x = 0;
    y = 0;
     x = x + 1;
     y = y + 1;
     assert(10<=x); <-------- false assertion
     assert(10<x||x<10);
   * *)
  let path =
    let open Infix in
    [T.assign "x" (int 0);
     T.assign "y" (int 0);
     T.assume (x < (int 10)); 
     T.assign "x" (x + (int 1));
     T.assign "y" (y + (int 1));
     T.assume ((int 10) <= x);
     T.assume ((x < (int 0)) && ((int 0) < (x)));
     T.assume ((int 10) < x || x < (int 10)) ]
  in
  let post = Ctx.mk_false in
  match T.interpolate_or_concrete_model path post with
  | `Valid itp ->
   (* let _ = failwith "valid" in *)check_interpolant path itp post
  | _ ->  (*let _ = failwith "wtf" in *)assert_failure "Invalid post-condition"

let interpolate2 () =
  let _ = Printf.printf " -------------------------- interpolate2 ------------------ \n" in 
(*
program:
   asume (x < 10); ---> good
   x := x + 1; --> x + 1 <= 10
   y := y + 1; ---> y := havoc() + 1
   assert (10 <= x); ---> good
   assert (10 < x || x < 10);
 * *)
  let path =
    let open Infix in
    [T.assume (x < (int 10));
     T.assign "x" (x + (int 1));
     T.assign "y" (y + (int 1));
     T.assume ((int 10) <= x);
     T.assume ((int 10) < x || x < (int 10))]
  in
  let post = Ctx.mk_false in
  match T.interpolate_or_concrete_model path post with
  | `Valid itp ->
    check_interpolant path itp post
  | _ -> 
    assert_failure "Invalid post-condition"

let interpolate3 () =
  let _ = Printf.printf " -------------------------- interpolate3 ------------------ \n" in 
(*
program:
   x := 0;
   y := 0;
   z := havoc();
   assert (z < x);
   assert (z < y);
 * *)
  let path = 
    let open Infix in
    [T.assign "x" (int 0);
     T.assign "y" (int 0);
     T.assume (z < x);
     T.assume (z < y)
    ]
  in
  let post = Ctx.mk_true in 
  match T.interpolate_or_concrete_model path post with 
  | `Valid itp -> 
    check_interpolant path itp post
  | _ -> 
    assert_failure "Invalid post-condition"

let print_model m = 
  Interpretation.pp Format.std_formatter m 

let interpolate_havoc3 () =
  let _ = Printf.printf " -------------------------- interpolate_havoc3 ------------------ \n" in
  let path =
    let open Infix in
    [T.havoc ["x"];T.assume ((int 0) <= x); T.assign "y" (x + (int 1)); T.assume ((int 0) < y)]
  in
  let post = Ctx.mk_true in
  match T.interpolate_or_concrete_model path post with
  | `Valid itp ->
    check_interpolant path itp post
  | _ -> assert_failure "Invalid post-condition"


let interpolate_havoc () =
  let _ = Printf.printf " -------------------------- interpolate_havoc ------------------ \n" in
  let path =
    let open Infix in
    [T.assign "x" (int 0);
     T.assign "y" v; (* havoc *)
     T.assume (x <= y);
     T.assume (y < (int 0))]
  in
  let post = Ctx.mk_false in
  match T.interpolate_or_concrete_model path post with
  | `Valid itp ->
    check_interpolant path itp post
  | _ -> assert_failure "Invalid post-condition"

let interpolate_havoc2 () =
  let _ = Printf.printf " -------------------------- interpolate_havoc2 ------------------ \n" in
  let path =
    let open Infix in
    [T.havoc ["z"];
     T.havoc ["w"];
     T.assign "y" ((int 3)+ z);
     T.assume (Ctx.mk_true)]
  in
  let post = Ctx.mk_true in
  match T.interpolate_or_concrete_model path post with
  | `Invalid _ -> 
    Printf.printf "good; invalid\n"
  | `Valid lis -> 
    Printf.printf "err: got a valid answer in interpolate_havoc2\n";
    List.iteri (fun i itp -> 
      Printf.printf "interpolant %d: " i;
      Syntax.pp_expr_unnumbered srk Format.std_formatter itp;
      Format.print_flush ();
      Printf.printf "\n") lis;
    check_interpolant path lis post;
  | _ -> assert_failure "Error: got unknown answer"


let check_model test_name m expected_cnt expected_valuations = 
  let fail s = 
    assert_failure @@
      Printf.sprintf "check_model error: test %s: %s\n" test_name s in 
  let e = Interpretation.enum m in 
  if BatEnum.count e < expected_cnt then 
    let m_str = Format.asprintf "%a" Interpretation.pp m in 
    fail @@
      Printf.sprintf "expected %d entires in model but got %d\nmodel:%s\n" 
        expected_cnt (BatEnum.count e) m_str 
  else   
    BatEnum.iter  
      (fun (sym, v) ->
        match Hashtbl.find_opt expected_valuations sym with 
        | Some (predicate, expected) -> 
          begin match v with 
          | `Real r -> 
            if not @@ predicate (Mpqf.to_float r) then 
              fail @@
                Printf.sprintf "symbol %s, expected value %s but got %f\n"
                  (Syntax.show_symbol srk sym) expected (Mpqf.to_float r)
          | _ -> 
              fail @@ 
                Printf.sprintf "symbol %s, unknown value\n"
                  (Syntax.show_symbol srk sym) 
          end
        | None -> (** we currently allow havoc symbols in returned models*) ()) e

let form_valuation l = 
  let tbl = Hashtbl.create 991 in 
  List.iter (fun (k,v) -> Hashtbl.add tbl k v) l; 
  tbl 

let interpolate_fail () = 
  let path = 
    let open Infix in
    [T.assign "x" (int 0);
      T.assign "y" (int 0);
      T.assign "z" (int 999);
      T.assign "y" (z + (int 1));
      T.assign "y" (int 0);
      T.assign "y" (y + (int 1));
      T.assign "x" (x + (int 1));
      T.assign "y" (y - (int 1));
      T.assign "x" y;
      T.assume ((int 0) <= x);
      T.assume ((int 0) <= y)
    ]
  in
  let post = let open Infix in mk_not srk ((int 0) <= x) in 
  begin match T.interpolate_or_concrete_model path post with 
  | `Invalid m -> 
    check_model "interpolate_fail" m 3 
      (form_valuation 
        [(V.symbol_of "x", ((fun x -> x = 0.0), "0"));
          (V.symbol_of "y", ((fun y -> y = 0.0), "0"));
          (V.symbol_of "z", ((fun z -> z = 999.0), "999"))])
  | _ ->  
    assert_failure "interpolate_fail: got interpolant when should be sat" 
  end 
  

let interpolate_fail1 () = 
    let path = 
      let open Infix in 
      [T.havoc ["x"]; 
        T.assign "y" ((int 10) + x); 
        T.assign "z" ((int 100));
        T.assign "y" ((int 10) + z);

        T.assume ((int 0) < y)] 
    in let post = let open Infix in Syntax.mk_not srk ((int 100) <= y) in 
    match T.interpolate_or_concrete_model path post with 
    | `Invalid m -> 
      check_model "interpolate_fail1" m 3 
        (form_valuation 
          [(V.symbol_of "x"), ((fun x -> x = 0.0), "0");
           (V.symbol_of "y"), ((fun y -> y = 110.0), "110");
           (V.symbol_of "z"), ((fun z -> z = 100.0), "100")])
    | _ -> 
      assert_failure "interpolate_fail1: got interpolant when should be sat"

let interpolate_fail2 () = 
    let prefix = [T.havoc ["x"] ] 
    in let suffix =
      let open Infix in 
       T.mul (T.assume ((int 10) < x)) (T.assign "x" ((int 10) + x))
    in let post =
      let open Infix in
        T.guard (T.mul suffix (T.assume ((int 1000) < x))) |> Syntax.mk_not srk 
    in match T.interpolate_or_concrete_model prefix post with 
    | `Invalid m -> 
      check_model "interpolate_fail2" m 1 
        (form_valuation [V.symbol_of "x", ((fun x -> x > 990.0), "value greater than 990")])
    | _ -> 
      assert_failure "interpolate_fail1: got interpolant when should be sat"

let negative_eigenvalue () =
  let tr =
    let open Infix in
    mk_block [
      T.assume ((int 0) < x);
      T.assume ((int 0) < y);
      T.assign "n" (x + y);
      T.assign "k" (int 0);
      T.assume ((int 0) < y);
      mk_while ((int 0) < x && (int 0) <= y) [
        T.parallel_assign [("x", y);
                           ("y", x - (int 1));
                           ("k", k + (int 1))]
      ]
    ]
  in
  let post = mk_leq srk k n in
  assert_post tr post

let suite = "Transition" >::: [
    "degree1" >:: degree1;
    "degree2" >:: degree2;
    "degree3" >:: degree3;
    "gauss_sum" >:: gauss_sum;
    "inc_nondet" >:: inc_nondet;
    "split" >:: split;
    "split2" >:: split2;
    "equal1" >:: equal1;
    "interpolate1" >:: interpolate1;
    "interpolate2" >:: interpolate2;
    "interpolate3" >:: interpolate3;
    "interpolate_havoc" >:: interpolate_havoc;
    "interpolate_havoc2" >:: interpolate_havoc2;
    "interpolate_havoc3" >:: interpolate_havoc3;
    "negative_eigenvalue" >:: negative_eigenvalue;
    (*"extrapolate1" >:: extrapolate1;
    "extrapolate2" >:: extrapolate2;
    "extrapolate3" >:: extrapolate3;*)
    "interpolate_fail" >:: interpolate_fail;
    "interpolate_fail1" >:: interpolate_fail1;
    "interpolate_fail2" >:: interpolate_fail2;
  ]
