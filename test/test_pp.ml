open Format

open OUnit2

open Lambda_S_dti
open Syntax
open Pp

let id x = x

let parse str =
  Parser.toplevel Lexer.main @@ Lexing.from_string str

let test_pp_ty =
  let test (expected, u) =
    expected >:: fun ctxt ->
      assert_equal ~ctxt:ctxt ~printer:id expected @@ asprintf "%a" pp_ty u
  in
  List.map test [
    "int -> bool", TyFun (TyInt, TyBool);
    "int -> bool -> ?", TyFun (TyInt, TyFun (TyBool, TyDyn));
    "(int -> bool) -> ?", TyFun (TyFun (TyInt, TyBool), TyDyn);
    "(int -> bool) -> ? -> int", TyFun (TyFun (TyInt, TyBool), TyFun (TyDyn, TyInt));
    (* "'x1 -> 'x2", TyFun (TyVar 1, TyVar 2); *)
  ]

let test_pp_ty2 =
  let test (expected, u) =
    expected >:: fun ctxt ->
      assert_equal ~ctxt:ctxt ~printer:id expected @@ asprintf "%a" pp_ty2 u
  in
  let a, b, c = Typing.fresh_tyvar (), Typing.fresh_tyvar (), Typing.fresh_tyvar () in
  List.map test [
    "int -> bool", TyFun (TyInt, TyBool);
    "int -> bool -> ?", TyFun (TyInt, TyFun (TyBool, TyDyn));
    "(int -> bool) -> ?", TyFun (TyFun (TyInt, TyBool), TyDyn);
    "(int -> bool) -> ? -> int", TyFun (TyFun (TyInt, TyBool), TyFun (TyDyn, TyInt));
    "'a -> 'b", TyFun (a, b);
    "'a -> 'b", TyFun (b, a);
    "('a -> 'b) -> 'a", TyFun (TyFun (c, b), c);
  ]

module ITGL = struct
  open Pp.ITGL

  let test_pp_program =
    let test (e) =
      e >:: fun ctxt ->
        assert_equal ~ctxt:ctxt ~printer:id e @@ asprintf "%a" pp_program @@ parse (e ^ ";;")
    in
    List.map test [
      "fun (x: ?) -> fun (y: ?) -> fun (z: ?) -> z";
      "x (y z)";
      "x y z";
      "1 * 2 + 3 * 4";
      "(1 + 2) * (3 + 4)";
      "(fun (x: ?) -> x) (fun (y: ?) -> y)";
      "1 + (2 : ?)";
    ]

  let suite = [
    "test_pp_program">::: test_pp_program;
  ]
end

module CC = struct
  open Pp.CC
  open Syntax.CC

  let r = Utils.Error.dummy_range

  let test_pp_exp =
    let test (expected, f) =
      expected >:: fun ctxt ->
        assert_equal ~ctxt:ctxt ~printer:id expected @@ asprintf "%a" pp_exp f
    in
    let x, y, z = Var ("x", []), Var ("y", []), Var ("z", []) in
    List.map test [
      "x y z", AppMExp (AppMExp (x, y), z);
      "x (y z)", AppMExp (x, AppMExp (y, z));
      "x * y + z * x", BinOp (Plus, BinOp (Mult, x, y), BinOp (Mult, z, x));
      "(x + y) * (z + x)", BinOp (Mult, BinOp (Plus, x, y), BinOp (Plus, z, x));
      "(fun (x: ?) -> x)<(? -> ?)!>",
      CAppExp (FunBExp ([], ("x", TyDyn), x), CoercionExp (CInj Ar));
      "x<int!>", CAppExp (x, CoercionExp (CInj I));
      "x<int!><bool?p>", CAppExp (CAppExp (x, CoercionExp (CInj I)), CoercionExp (CProj (B, (r, Pos))));
      "(fun (x: ?) -> x) (fun (y: ?) -> y)",
      AppMExp (FunBExp ([], ("x", TyDyn), x), FunBExp ([], ("y", TyDyn), y));
      "x y<int!>", CAppExp (AppMExp (x, y), CoercionExp (CInj I));
      "x (y<int!>)", AppMExp (x, CAppExp (y, CoercionExp (CInj I)));
    ]

  let suite = [
    "test_pp_exp">::: test_pp_exp;
  ]
end

let suite = [
  "test_pp_ty">::: test_pp_ty;
  "test_pp_ty2">::: test_pp_ty2;
  "test_ITGL">::: ITGL.suite;
  "test_CC">::: CC.suite;
]
