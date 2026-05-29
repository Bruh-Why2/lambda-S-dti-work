open Syntax
open Config

exception Stdlib_bug of string
exception Stdlib_exit of int

(* let is_debug = ref false
let is_alt = ref false
let is_B = ref false *)

let is_some_type = tysc_of_ty @@ TyFun (TyDyn, TyBool)

(* module CC = struct 
  open Syntax.CC

  let is_some t = 
    FunBV (fun _ -> function
    | Tagged (t', _) when t = t' -> BoolV true
    | Tagged _ -> BoolV false
    | _ -> raise @@ Stdlib_bug "untagged value"
    )

  let lib_exit = 
    FunV (fun _ -> function
    | IntV i -> raise @@ Stdlib_exit i
    | _ -> raise @@ Stdlib_bug "exit: unexpected value"
    )

  let lib_print_bool = 
    FunV (fun _ -> function
    | BoolV b -> print_string @@ string_of_bool b; UnitV
    | _ -> raise @@ Stdlib_bug "print_bool: unexpected value"
    )

  let lib_print_int = 
    FunV (fun _ -> function
    | IntV i -> print_int i; UnitV
    | _ -> raise @@ Stdlib_bug "print_int: unexpected value"
    )

  let lib_print_newline = 
    FunV (fun _ -> function
    | UnitV -> print_newline (); UnitV
    | _ -> raise @@ Stdlib_bug "print_newline: unexpected value"
    )

  let lib_read_int =
    FunV (fun _ -> function
    | UnitV -> let i = read_int () in IntV i
    | _ -> raise @@ Stdlib_bug "read_int: unexpected value"
    )
end *)

module CC = struct 
  open Syntax.CC

  let is_some t ~config = 
    if config.intoB then
      FunBV (fun _ -> function
      | Tagged (t', _) when t = t' -> BoolV true
      | Tagged _ -> BoolV false
      | _ -> raise @@ Stdlib_bug "untagged value"
      )
    else if config.alt then
      FunDualV (fun _ -> 
        (function
        | CoerceV (_, CSeq (_, CInj t')) when t = t' -> BoolV true
        | CoerceV _ -> BoolV false
        | _ -> raise @@ Stdlib_bug "not dyn value"),
        (function
        | CoerceV (_, CSeq (_, CInj t')), CoercionV c' when t = t' -> Eval.CC.coerce ~debug:config.debug (BoolV true) c'
        | CoerceV _, CoercionV c' -> Eval.CC.coerce ~debug:config.debug (BoolV false) c'
        | _ -> raise @@ Stdlib_bug "not dyn value")
      )
    else
      FunSV (fun _ -> function
      | CoerceV (_, CSeq (_, CInj t')), CoercionV c' when t = t' -> Eval.CC.coerce ~debug:config.debug (BoolV true) c'
      | CoerceV _, CoercionV c' -> Eval.CC.coerce ~debug:config.debug (BoolV false) c'
      | _ -> raise @@ Stdlib_bug "not dyn value"
      )

  let lib_exit ~config = 
    if config.intoB then
      FunBV (fun _ -> function
      | IntV i -> raise @@ Stdlib_exit i
      | _ -> raise @@ Stdlib_bug "exit: unexpected value"
      )
    else if config.alt then
      FunDualV (fun _ -> 
      (function
      | IntV i -> raise @@ Stdlib_exit i
      | _ -> raise @@ Stdlib_bug "exit: unexpected value"),
      (function
      | IntV i, _ -> raise @@ Stdlib_exit i
      | _ -> raise @@ Stdlib_bug "exit: unexpected value")
      )
    else 
      FunSV (fun _ -> function
      | IntV i, _ -> raise @@ Stdlib_exit i
      | _ -> raise @@ Stdlib_bug "exit: unexpected value"
      )

  let lib_print_bool ~config = 
    if config.intoB then
      FunBV (fun _ -> function
      | BoolV b -> print_string @@ string_of_bool b; UnitV
      | _ -> raise @@ Stdlib_bug "print_bool: unexpected value"
      )
    else if config.alt then 
      FunDualV (fun _ -> 
        (function
        | BoolV b -> 
          print_string @@ string_of_bool b;
          UnitV
        | _ -> raise @@ Stdlib_bug "print_bool: unexpected value"),    
        (function
        | BoolV b, CoercionV c -> 
          print_string @@ string_of_bool b;
          Eval.CC.coerce ~debug:config.debug UnitV c
        | _ -> raise @@ Stdlib_bug "print_bool: unexpected value")
      )
    else
      FunSV (fun _ -> function
      | BoolV b, CoercionV c -> 
        print_string @@ string_of_bool b; 
        Eval.CC.coerce ~debug:config.debug UnitV c
      | _ -> raise @@ Stdlib_bug "print_bool: unexpected value"
      )

  let lib_print_int ~config = 
    if config.intoB then
      FunBV (fun _ -> function
      | IntV i -> print_int i; UnitV
      | _ -> raise @@ Stdlib_bug "print_int: unexpected value"
      )
    else if config.alt then
      FunDualV (fun _ -> 
        (function
        | IntV i -> 
          print_int i;
          UnitV
        | _ -> raise @@ Stdlib_bug "print_int: unexpected value"),
        (function
        | IntV i, CoercionV c -> 
          print_int i;
          Eval.CC.coerce ~debug:config.debug UnitV c
        | _ -> raise @@ Stdlib_bug "print_int: unexpected value")
      )
    else
      FunSV (fun _ -> function
      | IntV i, CoercionV c -> 
        print_int i;
        Eval.CC.coerce ~debug:config.debug UnitV c
      | _ -> raise @@ Stdlib_bug "print_int: unexpected value"
      )

  let lib_print_newline ~config = 
    if config.intoB then
      FunBV (fun _ -> function
      | UnitV -> print_newline (); UnitV
      | _ -> raise @@ Stdlib_bug "print_newline: unexpected value"
      )
    else if config.alt then
      FunDualV (fun _ -> 
        (function
        | UnitV -> 
          print_newline (); 
          UnitV
        | _ -> raise @@ Stdlib_bug "print_newline: unexpected value"),
        (function
        | UnitV, CoercionV c -> 
          print_newline (); 
          Eval.CC.coerce ~debug:config.debug UnitV c
        | _ -> raise @@ Stdlib_bug "print_newline: unexpected value")
      )
    else 
      FunSV (fun _ -> function
      | UnitV, CoercionV c -> 
        print_newline (); 
        Eval.CC.coerce ~debug:config.debug UnitV c
      | _ -> raise @@ Stdlib_bug "print_newline: unexpected value"
      )

  let lib_read_int ~config =
    if config.intoB then
      FunBV (fun _ -> function
      | UnitV -> let i = read_int () in IntV i
      | _ -> raise @@ Stdlib_bug "read_int: unexpected value"
      )
    else if config.alt then
      FunDualV (fun _ -> 
        (function
        | UnitV -> 
          let i = read_int () in 
          IntV i
        | _ -> raise @@ Stdlib_bug "print_newline: unexpected value"),
        (function
        | UnitV, CoercionV c -> 
          let i = read_int () in
          Eval.CC.coerce ~debug:config.debug (IntV i) c
        | _ -> raise @@ Stdlib_bug "print_newline: unexpected value")
      )
    else 
      FunSV (fun _ -> function
      | UnitV, CoercionV c -> 
        let i = read_int () in
        Eval.CC.coerce ~debug:config.debug (IntV i) c
      | _ -> raise @@ Stdlib_bug "print_newline: unexpected value"
      )
end

module KNorm = struct 
  open Syntax.KNorm

  let is_some t ~config = 
    if config.intoB then
      FunBV (fun _ -> function
      | Tagged (t', _) when t = t' -> IntV 1
      | Tagged _ -> IntV 0
      | _ -> raise @@ Stdlib_bug "untagged value"
      )
    else if config.alt then
      FunDualV (fun _ -> 
        (function
        | CoerceV (_, CSeq (_, CInj t')) when t = t' -> IntV 1
        | CoerceV _ -> IntV 0
        | _ -> raise @@ Stdlib_bug "not dyn value"),
        (function
        | CoerceV (_, CSeq (_, CInj t')), CoercionV c' when t = t' -> Eval.KNorm.coerce ~debug:config.debug (IntV 1) c'
        | CoerceV _, CoercionV c' -> Eval.KNorm.coerce ~debug:config.debug (IntV 0) c'
        | _ -> raise @@ Stdlib_bug "not dyn value")
      )
    else
      FunSV (fun _ -> function
      | CoerceV (_, CSeq (_, CInj t')), CoercionV c' when t = t' -> Eval.KNorm.coerce ~debug:config.debug (IntV 1) c'
      | CoerceV _, CoercionV c' -> Eval.KNorm.coerce ~debug:config.debug (IntV 0) c'
      | _ -> raise @@ Stdlib_bug "not dyn value"
      )

  let lib_exit ~config = 
    if config.intoB then
      FunBV (fun _ -> function
      | IntV i -> raise @@ Stdlib_exit i
      | _ -> raise @@ Stdlib_bug "exit: unexpected value"
      )
    else if config.alt then
      FunDualV (fun _ -> 
      (function
      | IntV i -> raise @@ Stdlib_exit i
      | _ -> raise @@ Stdlib_bug "exit: unexpected value"),
      (function
      | IntV i, _ -> raise @@ Stdlib_exit i
      | _ -> raise @@ Stdlib_bug "exit: unexpected value")
      )
    else 
      FunSV (fun _ -> function
      | IntV i, _ -> raise @@ Stdlib_exit i
      | _ -> raise @@ Stdlib_bug "exit: unexpected value"
      )

  let lib_print_bool ~config = 
    if config.intoB then
      FunBV (fun _ -> function
      | IntV 1 -> print_string "true"; IntV 0
      | IntV 0 -> print_string "false"; IntV 0
      | _ -> raise @@ Stdlib_bug "print_bool: unexpected value"
      )
    else if config.alt then 
      FunDualV (fun _ -> 
        (function
        | IntV 0 -> 
          print_string "false";
          IntV 0
        | IntV 1 -> 
          print_string "true";
          IntV 0
        | _ -> raise @@ Stdlib_bug "print_bool: unexpected value"),    
        (function
        | IntV 0, CoercionV c -> 
          print_string "false";
          Eval.KNorm.coerce ~debug:config.debug (IntV 0) c
        | IntV 1, CoercionV c -> 
          print_string "true";
          Eval.KNorm.coerce ~debug:config.debug (IntV 0) c
        | _ -> raise @@ Stdlib_bug "print_bool: unexpected value")
      )
    else
      FunSV (fun _ -> function
      | IntV 0, CoercionV c -> 
        print_string "false"; 
        Eval.KNorm.coerce ~debug:config.debug (IntV 0) c
      | IntV 1, CoercionV c -> 
        print_string "true"; 
        Eval.KNorm.coerce ~debug:config.debug (IntV 0) c
      | _ -> raise @@ Stdlib_bug "print_bool: unexpected value"
      )

  let lib_print_int ~config = 
    if config.intoB then
      FunBV (fun _ -> function
      | IntV i -> print_int i; IntV 0
      | _ -> raise @@ Stdlib_bug "print_int: unexpected value"
      )
    else if config.alt then
      FunDualV (fun _ -> 
        (function
        | IntV i -> 
          print_int i;
          IntV 0
        | _ -> raise @@ Stdlib_bug "print_int: unexpected value"),
        (function
        | IntV i, CoercionV c -> 
          print_int i;
          Eval.KNorm.coerce ~debug:config.debug (IntV 0) c
        | _ -> raise @@ Stdlib_bug "print_int: unexpected value")
      )
    else
      FunSV (fun _ -> function
      | IntV i, CoercionV c -> 
        print_int i;
        Eval.KNorm.coerce ~debug:config.debug (IntV 0) c
      | _ -> raise @@ Stdlib_bug "print_int: unexpected value"
      )

  let lib_print_newline ~config = 
    if config.intoB then 
      FunBV (fun _ -> function
      | IntV 0 -> print_newline (); IntV 0
      | _ -> raise @@ Stdlib_bug "print_newline: unexpected value"
      )
    else if config.alt then
      FunDualV (fun _ -> 
        (function
        | IntV 0 -> 
          print_newline (); 
          IntV 0
        | _ -> raise @@ Stdlib_bug "print_newline: unexpected value"),
        (function
        | IntV 0, CoercionV c -> 
          print_newline (); 
          Eval.KNorm.coerce ~debug:config.debug (IntV 0) c
        | _ -> raise @@ Stdlib_bug "print_newline: unexpected value")
      )
    else 
      FunSV (fun _ -> function
      | IntV 0, CoercionV c -> 
        print_newline (); 
        Eval.KNorm.coerce ~debug:config.debug (IntV 0) c
      | _ -> raise @@ Stdlib_bug "print_newline: unexpected value"
      )

  let lib_read_int ~config = 
    if config.intoB then 
      FunBV (fun _ -> function
      | IntV 0 -> let i = read_int () in IntV i
      | _ -> raise @@ Stdlib_bug "print_newline: unexpected value"
      )
    else if config.alt then
      FunDualV (fun _ -> 
        (function
        | IntV 0 -> 
          let i = read_int () in
          IntV i
        | _ -> raise @@ Stdlib_bug "print_newline: unexpected value"),
        (function
        | IntV 0, CoercionV c -> 
          let i = read_int () in
          Eval.KNorm.coerce ~debug:config.debug (IntV i) c
        | _ -> raise @@ Stdlib_bug "print_newline: unexpected value")
      )
    else 
      FunSV (fun _ -> function
      | IntV 0, CoercionV c -> 
        let i = read_int () in 
        Eval.KNorm.coerce ~debug:config.debug (IntV i) c
      | _ -> raise @@ Stdlib_bug "print_newline: unexpected value"
      )
end

let implementations_direct ~config = [
    "exit", [], CC.lib_exit ~config, tysc_of_ty @@ TyFun (TyInt, TyUnit), KNorm.lib_exit ~config;
    "is_bool", [], CC.is_some B ~config, is_some_type, KNorm.is_some B ~config;
    "is_int", [], CC.is_some I ~config, is_some_type, KNorm.is_some I ~config;
    "is_unit", [], CC.is_some U ~config, is_some_type, KNorm.is_some U ~config;
    "is_fun", [], CC.is_some Ar ~config, is_some_type, KNorm.is_some Ar ~config;
    "is_list", [], CC.is_some Li ~config, is_some_type, KNorm.is_some Li ~config;
    "max_int", [], IntV max_int, tysc_of_ty TyInt, IntV max_int;
    "min_int", [], IntV min_int, tysc_of_ty TyInt, IntV min_int;
    "print_bool", [], CC.lib_print_bool ~config, tysc_of_ty @@ TyFun (TyBool, TyUnit), KNorm.lib_print_bool ~config;
    "print_int", [], CC.lib_print_int ~config, tysc_of_ty @@ TyFun (TyInt, TyUnit), KNorm.lib_print_int ~config;
    "print_newline", [], CC.lib_print_newline ~config, tysc_of_ty @@ TyFun (TyUnit, TyUnit), KNorm.lib_print_newline ~config;
    "read_int", [], CC.lib_read_int ~config, tysc_of_ty @@ TyFun (TyUnit, TyInt), KNorm.lib_read_int ~config;
  ]

let implementations_eval = [
    "let not b = if b then false else true;;";
    "let succ x = x + 1;;";
    "let prec x = x - 1;;";
    "let min x y = if x < y then x else y;;";
    "let max x y = if x > y then x else y;;";
    "let abs x = if x < 0 then -x else x;;";
    "let ignore x = ();;";
  ]

let pervasives ~config = 
  let env, tyenv, kfunenvs, kenv = Environment.empty, Environment.empty, (Environment.empty, Environment.empty, Environment.empty), Environment.empty in
  let env, tyenv, kfunenvs, kenv =
    List.fold_left
      (fun (env, tyenv, (tvsenv, alphaenv, betaenv), kenv) (x, xs, v, u, kv) ->
         Environment.add x (xs, v) env, Environment.add x u tyenv, (Environment.add x [] tvsenv, Environment.add x x alphaenv, Environment.add x x betaenv), Environment.add x kv kenv)
      (env, tyenv, kfunenvs, kenv)
      (implementations_direct ~config)
  in
  let env, tyenv, kfunenvs', kenv =
    List.fold_left
      (fun (env, tyenv, kfunenvs, kenv) str ->
        let e = Parser.toplevel Lexer.main @@ Lexing.from_string str in
        let e, u = Typing.ITGL.type_of_program tyenv e in
        let tyenv, e, _ = Typing.ITGL.normalize tyenv e u in
        let new_tyenv, f, _ = Translate.ITGL.translate ~intoB:config.intoB tyenv e in
        let _ = Typing.CC.type_of_program tyenv f in
        let f = 
          if config.intoB then f
          else if config.alt then Translate.CC.translate_alt tyenv f
          else Translate.CC.translate tyenv f
        in let env, _, _ = Eval.CC.eval_program env f in
        let kf, kfunenvs = KNormal.kNorm_funs kfunenvs f in
        let kenv, _, _ = Eval.KNorm.eval_program kenv kf in
        env, new_tyenv, kfunenvs, kenv)
      (env, tyenv, kfunenvs, kenv)
      implementations_eval
  in
  let kfunenvs = 
    if config.compile then
      let kfunenvs = List.fold_left (fun (t, a, b) -> fun x -> Environment.add x [] t, Environment.add x x a, Environment.add x x b) kfunenvs ["not"; "succ"; "prec"; "min"; "max"] in
      (* C言語で既に定義されている関数 *)
      let kfunenvs = List.fold_left (fun (t, a, b) -> fun (x, y) -> Environment.add y [] t, Environment.add x y a, Environment.add y y b) kfunenvs ["abs", "abs_ml"] in
      (* 多相性のある関数 *)
      List.fold_left (fun (t, a, b) -> fun x -> Environment.add x [0, ref None] t, Environment.add x x a, Environment.add x x b) kfunenvs ["ignore"]
    else 
      kfunenvs'
  in
  env, tyenv, kfunenvs, kenv

let venv = List.fold_left (fun vs -> fun x -> V.add x vs) V.empty ["print_int"; "print_bool"; "print_newline"; "read_int"; "not"; "succ"; "prec"; "min"; "max"; "abs"; "ignore"]