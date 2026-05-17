open Format

open Syntax

exception Syntax_error

let with_paren flag ppf_e ppf e =
  fprintf ppf (if flag then "(%a)" else "%a") ppf_e e

let rec gt_ty (u1: ty) u2 = match u1, u2 with
  | TyVar (_, { contents = Some u1 }), u2
  | u1, TyVar (_, { contents = Some u2 }) -> gt_ty u1 u2
  | _, TyFun _ -> true
  | _ -> false

let gte_ty u1 u2 = match u1, u2 with
  | TyTuple _, TyTuple _ -> true
  | _ -> gt_ty u1 u2

(** Pretty-printer for types. Show the raw index of a type variable (e.g., 'x123->'x124). *)
let rec pp_ty ppf = function
  | TyDyn -> pp_print_string ppf "?"
  | TyVar (a, { contents = None }) -> fprintf ppf "'x%d" a
  | TyVar (_, { contents = Some u }) -> pp_ty ppf u
  | TyInt -> pp_print_string ppf "int"
  | TyBool -> pp_print_string ppf "bool"
  | TyUnit -> pp_print_string ppf "unit"
  | TyFun (u1, u2) as u ->
    fprintf ppf "%a -> %a"
      (with_paren (gt_ty u u1) pp_ty) u1
      pp_ty u2
  | TyList u -> 
    fprintf ppf "[%a]" pp_ty u
  | TyTuple us as u ->
    let pp_sep ppf () = fprintf ppf " * " in
    let pp_list ppf types = pp_print_list (fun ppf u' -> (with_paren (gte_ty u u') pp_ty) ppf u') ppf types ~pp_sep:pp_sep in
    fprintf ppf "%a"
      pp_list us

(** Pretty-printer for types. Type variables are renamed (e.g., 'a->'b). *)
let pp_ty2 ppf u =
  let tyvars = ref [] in
  let pp_tyvar ppf (a, _) =
    let rec index_of_tyvar pos = function
      | [] -> tyvars := !tyvars @ [a]; pos
      | a' :: rest -> if a = a' then pos else index_of_tyvar (pos + 1) rest
    in
    let pp_tyvar_of_index ppf i =
      let j = i / 26 in
      let k = i mod 26 in
      let s = String.make 1 @@ char_of_int @@ (int_of_char 'a') + k in
      let t = if j = 0 then "" else string_of_int j in
      fprintf ppf "'%s%s" s t
    in
    pp_tyvar_of_index ppf @@ index_of_tyvar 0 !tyvars
  in
  let rec pp_ty ppf = function
    | TyDyn -> pp_print_string ppf "?"
    | TyVar (_, { contents = Some u }) -> pp_ty ppf u
    | TyVar x -> pp_tyvar ppf x
    | TyInt -> pp_print_string ppf "int"
    | TyBool -> pp_print_string ppf "bool"
    | TyUnit -> pp_print_string ppf "unit"
    | TyFun (u1, u2) as u ->
      fprintf ppf "%a -> %a"
        (with_paren (gt_ty u u1) pp_ty) u1
        pp_ty u2
    | TyList u ->
      fprintf ppf "[%a]" pp_ty u
    | TyTuple us as u ->
      let pp_sep ppf () = fprintf ppf " * " in
      let pp_list ppf types = pp_print_list (fun ppf u' -> (with_paren (gte_ty u u') pp_ty) ppf u') ppf types ~pp_sep:pp_sep in
      fprintf ppf "%a"
        pp_list us
  in pp_ty ppf u

let gt_binop op1 op2 = match op1, op2 with
  | (Plus | Minus | Mult | Div | Mod), (Eq | Neq | Lt | Lte | Gt | Gte)
  | (Mult | Div | Mod), (Plus | Minus) -> true
  | _ -> false

let gte_binop op1 op2 = match op1, op2 with
  | (Eq | Neq | Lt | Lte | Gt | Gte), (Eq | Neq | Lt | Lte | Gt | Gte)
  | (Mult | Div | Mod), (Mult | Div | Mod)
  | (Plus | Minus), (Plus | Minus) -> true
  | _ -> gt_binop op1 op2

let pp_binop ppf op =
  pp_print_string ppf begin
    match op with
    | Plus -> "+"
    | Minus -> "-"
    | Mult -> "*"
    | Div -> "/"
    | Mod -> "mod"
    | Eq -> "="
    | Neq -> "<>"
    | Lt -> "<"
    | Lte -> "<="
    | Gt -> ">"
    | Gte -> ">="
  end

let pp_print_var ppf (x, ys) =
  if List.length ys = 0 then
    fprintf ppf "%s" x
  else
    let pp_sep ppf () = fprintf ppf "," in
    let pp_list ppf types = pp_print_list pp_ty ppf types ~pp_sep:pp_sep in
    fprintf ppf "%s[%a]"
      x
      pp_list ys

let pp_tyarg ppf = function
  | Ty u -> pp_ty ppf u
  | TyNu -> pp_print_string ppf "ν"

let pp_let_tyabses ppf tyvars =
  if List.length tyvars = 0 then
    fprintf ppf ""
  else
    let pp_sep ppf () = fprintf ppf "," in
    let pp_list ppf types = pp_print_list pp_ty ppf types ~pp_sep:pp_sep in
    fprintf ppf "fun %a -> " pp_list @@ List.map (fun x -> TyVar x) tyvars

let pp_print_tas ppf tas =
  let pp_sep ppf () = fprintf ppf "," in
  let pp_list ppf types = pp_print_list pp_tyarg ppf types ~pp_sep:pp_sep in
  fprintf ppf "%a"
    pp_list tas

let pp_tag ppf = function
  | I -> pp_print_string ppf "int"
  | B -> pp_print_string ppf "bool"
  | U -> pp_print_string ppf "unit"
  | Ar -> pp_print_string ppf "(? -> ?)"
  | Li -> pp_print_string ppf "[?]"
  | Tp n ->
    let rec pp_dyn_tuple ppf i =
      if i = 1 then fprintf ppf "?"
      else fprintf ppf "? * %a" pp_dyn_tuple (i - 1)
    in
    fprintf ppf "(%a)"
      pp_dyn_tuple n

let gte_matchform mf1 mf2 = match mf1, mf2 with
  | MatchCons _, MatchCons _ -> true
  | MatchTuple _, MatchTuple _ -> true
  | _ -> false

let rec pp_matchform ppf = function
  | MatchVar (x, u) -> fprintf ppf "(%s: %a)" x pp_ty u
  (* | MatchAsc (mf, u) -> fprintf ppf "(%a : %a)" pp_matchform mf pp_ty u *)
  | MatchILit i -> pp_print_int ppf i
  | MatchBLit b -> pp_print_bool ppf b
  | MatchULit -> pp_print_string ppf "()"
  | MatchNil u -> fprintf ppf "([] : %a)" pp_ty (TyList u)
  | MatchCons (mf1, mf2) as mf -> 
    fprintf ppf "%a :: %a"
      (with_paren (gte_matchform mf mf1) pp_matchform) mf1
      pp_matchform mf2
  | MatchTuple mfs as mf ->
    let pp_sep ppf () = fprintf ppf ", " in
    let pp_list ppf matches = pp_print_list (fun ppf mf' -> (with_paren (gte_matchform mf mf') pp_matchform) ppf mf') ppf matches ~pp_sep:pp_sep in
    fprintf ppf "(%a)"
      pp_list mfs
  | MatchWild _ -> pp_print_string ppf "_"

let gt_coercion c1 c2 = match c1, c2 with
  | (CInj _ | CProj _ | CTvInj _ | CTvProj _ | CTvProjInj _ | CId _ | CFail _ | CFun _ | CList _ | CTuple _), CSeq _ -> true
  | _ -> false

let gte_coercion c1 c2 = match c1, c2 with
  | CFun _, CFun _ -> true
  | CTuple _, CTuple _ -> true
  (* | CList _, CList _ is intentionally ommited *)
  | _ -> gt_coercion c1 c2

let rec pp_coercion ppf = function
  | CInj t -> 
    fprintf ppf "%a!"
      pp_tag t
  | CProj (t, _) ->
    fprintf ppf "%a?p"
      pp_tag t
  | CTvInj ((_, {contents = None} as tv), _) ->
    fprintf ppf "%a!p"
      pp_ty (TyVar tv)
  | CTvProj ((_, {contents = None} as tv), _) ->
    fprintf ppf "%a?p"
      pp_ty (TyVar tv)
  | CTvProjInj ((_, {contents = None} as tv), _, _) ->
    fprintf ppf "?p%a!q"
      pp_ty (TyVar tv)
  | CTvInj (tv, _) ->
    fprintf ppf "|%a|!"
      pp_ty (TyVar tv)
  | CTvProj (tv, _) ->
    fprintf ppf "|%a|?"
      pp_ty (TyVar tv)
  | CTvProjInj (tv, _, _) ->
    fprintf ppf "?|%a|!"
      pp_ty (TyVar tv)
  | CFun (c1, c2) as c ->
    fprintf ppf "%a->%a"
      (with_paren (gte_coercion c c1) pp_coercion) c1
      (with_paren (gte_coercion c c2) pp_coercion) c2
  | CList c ->
    fprintf ppf "[%a]"
      pp_coercion c
  | CTuple cs as c ->
    let pp_sep ppf () = fprintf ppf "*" in
    let pp_list ppf crcs = pp_print_list (fun ppf c' -> (with_paren (gte_coercion c c') pp_coercion) ppf c') ppf crcs ~pp_sep:pp_sep in
    fprintf ppf "%a"
      pp_list cs
  | CId u ->
    fprintf ppf "id{%a}" 
      pp_ty u
  | CSeq (c1, c2) ->
    fprintf ppf "%a;%a"
      pp_coercion c1
      pp_coercion c2
  | CFail (t1, _, t2) ->
    fprintf ppf "⊥{%a,p,%a}"
      pp_tag t1
      pp_tag t2

let pp_coercion2 ppf c = 
  let pp_ty = pp_ty2 in
  let rec pp_coercion ppf = function
  | CInj t -> 
    fprintf ppf "%a!"
      pp_tag t
  | CProj (t, _) ->
    fprintf ppf "%a?p"
      pp_tag t
  | CTvInj ((_, {contents = None} as tv), _) ->
    fprintf ppf "%a!"
      pp_ty (TyVar tv)
  | CTvProj ((_, {contents = None} as tv), _) ->
    fprintf ppf "%a?p"
      pp_ty (TyVar tv)
  | CTvProjInj ((_, {contents = None} as tv), _, _) ->
    fprintf ppf "?p%a!"
      pp_ty (TyVar tv)
  | CTvInj (tv, _) ->
    fprintf ppf "|%a|!"
      pp_ty (TyVar tv)
  | CTvProj (tv, _) ->
    fprintf ppf "|%a|?"
      pp_ty (TyVar tv)
  | CTvProjInj (tv, _, _) ->
    fprintf ppf "?|%a|!"
      pp_ty (TyVar tv)
  | CFun (c1, c2) as c ->
    fprintf ppf "%a->%a"
      (with_paren (gte_coercion c c1) pp_coercion) c1
      (with_paren (gte_coercion c c2) pp_coercion) c2
  | CList c ->
    fprintf ppf "[%a]"
      pp_coercion c
  | CTuple cs as c ->
    let pp_sep ppf () = fprintf ppf "*" in
    let pp_list ppf crcs = pp_print_list (fun ppf c' -> (with_paren (gte_coercion c c') pp_coercion) ppf c') ppf crcs ~pp_sep:pp_sep in
    fprintf ppf "%a"
      pp_list cs
  | CId u ->
    fprintf ppf "id{%a}" 
      pp_ty u
  | CSeq (c1, c2) ->
    fprintf ppf "%a;%a"
      pp_coercion c1
      pp_coercion c2
  | CFail (t1, _, t2) ->
    fprintf ppf "⊥{%a,p,%a}"
      pp_tag t1
      pp_tag t2
  in
  pp_coercion ppf c

module ITGL = struct
  open Syntax.ITGL

  let pp_constr ppf = function
    | CEqual (u1, u2) ->
      fprintf ppf "%a =.= %a" pp_ty u1 pp_ty u2
    | CConsistent (u1, u2) ->
      fprintf ppf "%a ~.~ %a" pp_ty u1 pp_ty u2

  let gt_exp e1 e2 = match e1, e2 with
    | (Var _ | IConst _ | BConst _ | UConst _ | NilExp _ | TupleExp _ | AscExp _ | AppExp _ | BinOp _ | ConsExp _ | IfExp _ | MatchExp _), (LetExp _ | FunEExp _ | FunIExp _ | FixEExp _ | FixIExp _) -> true
    | (Var _ | IConst _ | BConst _ | UConst _ | NilExp _ | TupleExp _ | AscExp _ | AppExp _ | BinOp _ | ConsExp _ | IfExp _), MatchExp _ -> true
    | (Var _ | IConst _ | BConst _ | UConst _ | NilExp _ | TupleExp _ | AscExp _ | AppExp _ | BinOp _ | ConsExp _), IfExp _ -> true
    | BinOp (_, op1, _, _), BinOp (_, op2, _, _) -> gt_binop op1 op2
    | (Var _ | IConst _ | BConst _ | UConst _ | NilExp _ | TupleExp _ | AscExp _ | AppExp _), (BinOp _ | ConsExp _) -> true
    | (Var _ | IConst _ | BConst _ | UConst _ | NilExp _ | TupleExp _ | AscExp _), AppExp _ -> true
    | (Var _ | IConst _ | BConst _ | UConst _ | NilExp _ | TupleExp _), AscExp _ -> true
    | _ -> false

  let gte_exp e1 e2 = match e1, e2 with
    | LetExp _, LetExp _ -> true
    | FunEExp _, FunEExp _ -> true
    | FunIExp _, FunIExp _ -> true
    | FixEExp _, FixEExp _ -> true
    | FixIExp _, FixIExp _ -> true
    | IfExp _, IfExp _ -> true
    | BinOp (_, op1, _, _), BinOp (_, op2, _, _) when op1 = op2 -> true
    | AppExp _, AppExp _ -> true
    | MatchExp _, MatchExp _ -> true
    | ConsExp _, ConsExp _ -> true
    | TupleExp _, TupleExp _ -> true
    | _ -> gt_exp e1 e2

  let rec pp_exp ppf = function
    | Var (_, x, ys) -> pp_print_var ppf (x, !ys)
    | BConst (_, b) -> pp_print_bool ppf b
    | IConst (_, i) -> pp_print_int ppf i
    | UConst _ -> pp_print_string ppf "()"
    | BinOp (_, op, e1, e2) as e ->
      fprintf ppf "%a %a %a"
        (with_paren (gt_exp e e1) pp_exp) e1
        pp_binop op
        (with_paren (gt_exp e e2) pp_exp) e2
    | AscExp (_, e1, u) as e ->
      fprintf ppf "(%a : %a)"
        (with_paren (gt_exp e e1) pp_exp) e1
        pp_ty u
    | IfExp (_, e1, e2, e3) as e ->
      fprintf ppf "if %a then %a else %a"
        (with_paren (gt_exp e e1) pp_exp) e1
        (with_paren (gt_exp e e2) pp_exp) e2
        (with_paren (gt_exp e e3) pp_exp) e3
    | FunEExp (_, x1, u1, e)
    | FunIExp (_, x1, u1, e) ->
      fprintf ppf "fun (%s: %a) -> %a"
        x1
        pp_ty u1
        pp_exp e
    | FixEExp (_, x, y, u1, u2, e)
    | FixIExp (_, x, y, u1, u2, e) ->
      fprintf ppf "fix %s (%s: %a): %a = %a"
        x
        y
        pp_ty u1
        pp_ty u2
        pp_exp e
    | AppExp (_, e1, e2) as e ->
      fprintf ppf "%a %a"
        (with_paren (gt_exp e e1) pp_exp) e1
        (with_paren (gte_exp e e2) pp_exp) e2
    | MatchExp (_, e1, ms) as e ->
      fprintf ppf "match %a with%a"
        (with_paren (gte_exp e e1) pp_exp) e1
        pp_match (ms, e)
    | LetExp (_, x, e1, e2) as e ->
      fprintf ppf "let %s = %a in %a"
        x
        (with_paren (gt_exp e e1) pp_exp) e1
        pp_exp e2
    | NilExp _ -> pp_print_string ppf "[]"
    | ConsExp (_, e1, e2) as e ->
      fprintf ppf "%a :: %a"
        (with_paren (gte_exp e e1) pp_exp) e1
        (with_paren (gt_exp e e2) pp_exp) e2
    | TupleExp (_, es) ->
      let pp_sep ppf () = fprintf ppf ", " in
      let pp_list ppf exps = pp_print_list pp_exp ppf exps ~pp_sep:pp_sep in
      fprintf ppf "(%a)"
        pp_list es
      
  and pp_match ppf = function
    | ((mf, e1) :: m, e) -> 
      fprintf ppf " | %a -> %a%a"
        pp_matchform mf
        (with_paren (gte_exp e e1) pp_exp) e1
        pp_match (m, e)
    | ([], _) -> fprintf ppf ""

  let pp_program ppf = function
    | Exp e -> pp_exp ppf e
    | LetDecl (x, e) ->
      fprintf ppf "let %s = %a"
        x
        pp_exp e
end

module CC = struct
  open Syntax.CC

  let gt_exp f1 f2 = match f1, f2 with
    | (Var _ | IConst _ | BConst _ | UConst | NilExp _ | CoercionExp _ | TupleExp _ | CSeqExp _ | AppMExp _ | AppDExp _ | CAppExp _ | BinOp _ | ConsExp _ | IfExp _ | MatchExp _ | CastExp _), (LetExp _ | FunBExp _ | FixBExp _ | FunSExp _ | FixSExp _ | FunAExp _ | FixAExp _) -> true
    | (Var _ | IConst _ | BConst _ | UConst | NilExp _ | CoercionExp _ | TupleExp _ | CSeqExp _ | AppMExp _ | AppDExp _ | CAppExp _ | BinOp _ | ConsExp _ | IfExp _ | MatchExp _), CastExp _ -> true
    | (Var _ | IConst _ | BConst _ | UConst | NilExp _ | CoercionExp _ | TupleExp _ | CSeqExp _ | AppMExp _ | AppDExp _ | CAppExp _ | BinOp _ | ConsExp _ | IfExp _), MatchExp _ -> true
    | (Var _ | IConst _ | BConst _ | UConst | NilExp _ | CoercionExp _ | TupleExp _ | CSeqExp _ | AppMExp _ | AppDExp _ | CAppExp _ | BinOp _ | ConsExp _), IfExp _ -> true
    | BinOp (op1, _, _), BinOp (op2, _, _) -> gt_binop op1 op2
    | (Var _ | IConst _ | BConst _ | UConst | NilExp _ | CoercionExp _ | TupleExp _ | CSeqExp _ | AppMExp _ | AppDExp _ | CAppExp _ ), (BinOp _ | ConsExp _) -> true
    | (Var _ | IConst _ | BConst _ | UConst | NilExp _ | CoercionExp _ | TupleExp _ | CSeqExp _ | AppMExp _ | AppDExp _), CAppExp _ -> true
    | (Var _ | IConst _ | BConst _ | UConst | NilExp _ | CoercionExp _ | TupleExp _ | CSeqExp _), (AppMExp _ | AppDExp _) -> true
    | (Var _ | IConst _ | BConst _ | UConst | NilExp _ | CoercionExp _ | TupleExp _), CSeqExp _ -> true
    | _ -> false

  let gte_exp f1 f2 = match f1, f2 with
    | (LetExp _ | FunBExp _ | FixBExp _ | FunSExp _ | FixSExp _ | FunAExp _ | FixAExp _), (LetExp _ | FunBExp _ | FixBExp _ | FunSExp _ | FixSExp _ | FunAExp _ | FixAExp _) -> true
    | IfExp _, IfExp _ -> true
    | BinOp (op1, _, _), BinOp (op2, _, _) when op1 = op2 -> true
    | (AppDExp _ | AppMExp _), (AppDExp _ | AppMExp _) -> true
    | CAppExp _, CAppExp _ -> true
    | CSeqExp _, CSeqExp _ -> true
    | MatchExp _, MatchExp _ -> true
    | ConsExp _, ConsExp _ -> true
    | TupleExp _, TupleExp _ -> true
    | _ -> gt_exp f1 f2

  let pp_print_var ppf (x, ys) =
    if List.length ys = 0 then
      fprintf ppf "%s" x
    else
      let pp_sep ppf () = fprintf ppf "," in
      let pp_list ppf types = pp_print_list pp_tyarg ppf types ~pp_sep:pp_sep in
      fprintf ppf "%s[%a]"
        x
        pp_list ys

  let rec pp_exp ppf = function
    | Var (x, ys) -> pp_print_var ppf (x, ys)
    | BConst b -> pp_print_bool ppf b
    | IConst i -> pp_print_int ppf i
    | UConst -> pp_print_string ppf "()"
    | BinOp (op, f1, f2) as f ->
      fprintf ppf "%a %a %a"
        (with_paren (gt_exp f f1) pp_exp) f1
        pp_binop op
        (with_paren (gt_exp f f2) pp_exp) f2
    | IfExp (f1, f2, f3) as f ->
      fprintf ppf "if %a then %a else %a"
        (with_paren (gt_exp f f1) pp_exp) f1
        (with_paren (gt_exp f f2) pp_exp) f2
        (with_paren (gt_exp f f3) pp_exp) f3
    | FunBExp ((x1, u1), f) ->
      fprintf ppf "fun (%s: %a) -> %a"
        x1
        pp_ty u1
        pp_exp f
    | FixBExp ((x, y, u1, u2), f) ->
      fprintf ppf "fix %s (%s: %a): %a = %a"
        x
        y
        pp_ty u1
        pp_ty u2
        pp_exp f
    | FunSExp ((x1, u1), c, f) ->
      fprintf ppf "fun ((%s: %a), %s) -> %a"
        x1
        pp_ty u1
        c
        pp_exp f
    | FixSExp ((x, y, u1, u2), c, f) ->
      fprintf ppf "fix %s ((%s: %a), %s): %a = %a"
        x
        y
        pp_ty u1
        c
        pp_ty u2
        pp_exp f
    | FunAExp ((x1, u1), c, (f1, f2)) ->
      fprintf ppf "fun ((%s: %a), %s) -> (%a | %a)"
        x1
        pp_ty u1
        c
        pp_exp f1
        pp_exp f2
    | FixAExp ((x, y, u1, u2), c, (f1, f2)) ->
      fprintf ppf "fix %s ((%s: %a), %s): %a = (%a | %a)"
        x
        y
        pp_ty u1
        c
        pp_ty u2
        pp_exp f1
        pp_exp f2
    | AppMExp (f1, f2) as f ->
      fprintf ppf "%a %a"
        (with_paren (gt_exp f f1) pp_exp) f1
        (with_paren (gte_exp f f2) pp_exp) f2
    | AppDExp (f1, (f2, f3)) as f ->
      fprintf ppf "%a (%a, %a)"
        (with_paren (gt_exp f f1) pp_exp) f1
        pp_exp f2
        pp_exp f3
    | CAppExp (f1, f2) as f ->
        fprintf ppf "%a<%a>"
          (with_paren (gt_exp f f1) pp_exp) f1
          pp_exp f2
    | CSeqExp (f1, f2) ->
        fprintf ppf "%a;;%a"
          pp_exp f1
          pp_exp f2
    | CastExp (f1, u1, u2, _) as f ->
      begin match f1 with
      | CastExp (_, _, u1', _) when u1 = u1' ->
        fprintf ppf "%a => %a"
          (with_paren (gt_exp f f1) pp_exp) f1
          pp_ty u2
      | CastExp _ ->
        raise Syntax_error
      | _ ->
        fprintf ppf "%a: %a => %a"
          (with_paren (gt_exp f f1) pp_exp) f1
          pp_ty u1
          pp_ty u2
      end
    | MatchExp (e1, ms) as e ->
      fprintf ppf "match %a with%a"
        (with_paren (gte_exp e e1) pp_exp) e1
        pp_match (ms, e)
    | LetExp (x, xs, f1, f2) as f ->
      fprintf ppf "let %s = %a%a in %a"
        x
        pp_let_tyabses xs
        (with_paren (gt_exp f f1) pp_exp) f1
        pp_exp f2
    | CoercionExp c ->
      fprintf ppf "%a"
        pp_coercion c
    | NilExp _ -> pp_print_string ppf "[]"
    | ConsExp (f1, f2) as f ->
      fprintf ppf "%a :: %a"
        (with_paren (gte_exp f f1) pp_exp) f1
        (with_paren (gt_exp f f2) pp_exp) f2
    | TupleExp es ->
      let pp_sep ppf () = fprintf ppf ", " in
      let pp_list ppf exps = pp_print_list pp_exp ppf exps ~pp_sep:pp_sep in
      fprintf ppf "(%a)"
        pp_list es
  and pp_match ppf = function
    | ((mf, e1) :: m, e) -> 
      fprintf ppf " | %a -> %a%a"
        pp_matchform mf
        (with_paren (gte_exp e e1) pp_exp) e1
        pp_match (m, e)
    | ([], _) -> fprintf ppf ""

  let pp_program ppf = function
    | Exp e -> pp_exp ppf e
    | LetDecl (x, xs, f) ->
      fprintf ppf "let %s = %a%a"
        x
        pp_let_tyabses xs
        pp_exp f

  (*let pp_tag ppf t = pp_ty ppf @@ tag_to_ty t*)

  let gt_value v1 v2 = match v1, v2 with
    | (BoolV _ | IntV _ | UnitV | FunBV _ | FunSV _ | FunAV _ | NilV | TupleV _ | CoercionV _ | Tagged _ | CoerceV _), ConsV _ -> true
    | (BoolV _ | IntV _ | UnitV | FunBV _ | FunSV _ | FunAV _ | NilV | TupleV _ | CoercionV _), (Tagged _ | CoerceV _) -> true
    | _ -> false

  let gte_value v1 v2 = match v1, v2 with
    | (FunBV _ | FunSV _ | FunAV _), (FunBV _ | FunSV _ | FunAV _) -> true
    | Tagged _, Tagged _ -> true
    | CoerceV _, CoerceV _ -> true
    | ConsV _, ConsV _ -> true
    | TupleV _, TupleV _ -> true
    | _ -> gt_value v1 v2

  let rec pp_value ppf = function
    | BoolV b -> pp_print_bool ppf b
    | IntV i -> pp_print_int ppf i
    | UnitV -> pp_print_string ppf "()"
    | FunBV _ | FunSV _ | FunAV _ -> pp_print_string ppf "<fun>"
    | CoerceV (v1, c) as v ->
      fprintf ppf "%a<<%a>>"
        (with_paren (gt_value v v1) pp_value) v1
        pp_coercion c
    | CoercionV c -> 
      fprintf ppf "%a"
        pp_coercion c
    | NilV -> pp_print_string ppf "[]"
    | ConsV (v1, v2) as v ->
      fprintf ppf "%a :: %a"
        (with_paren (gte_value v v1) pp_value) v1
        (with_paren (gt_value v v2) pp_value) v2
    | TupleV vs ->
      let pp_sep ppf () = fprintf ppf ", " in
      let pp_list ppf vals = pp_print_list pp_value ppf vals ~pp_sep:pp_sep in
      fprintf ppf "(%a)"
        pp_list vs
    | Tagged (t, v) ->
      fprintf ppf "%a: %a => ?"
        pp_value v
        pp_tag t

  let rec pp_value2 ppf = function
    | BoolV b -> pp_print_bool ppf b
    | IntV i -> pp_print_int ppf i
    | UnitV -> pp_print_string ppf "()"
    | FunBV _ | FunSV _ | FunAV _ -> pp_print_string ppf "<fun>"
    | CoerceV (v1, c) as v ->
      fprintf ppf "%a<<%a>>"
        (with_paren (gt_value v v1) pp_value2) v1
        pp_coercion2 c
    | CoercionV c -> 
      fprintf ppf "%a"
        pp_coercion2 c
    | NilV -> pp_print_string ppf "[]"
    | ConsV (v1, v2) as v ->
      fprintf ppf "%a :: %a"
        (with_paren (gte_value v v1) pp_value2) v1
        (with_paren (gt_value v v2) pp_value2) v2
    | TupleV vs ->
      let pp_sep ppf () = fprintf ppf ", " in
      let pp_list ppf vals = pp_print_list pp_value2 ppf vals ~pp_sep:pp_sep in
      fprintf ppf "(%a)"
        pp_list vs
    | Tagged (t, v) ->
      fprintf ppf "%a: %a => ?"
        pp_value2 v
        pp_tag t
end

module KNorm = struct 
  open Syntax.KNorm

  let gt_exp e e1 = match e, e1 with
    | (Var _ | IConst _ | Nil), _ -> raise @@ Syntax_error(* "gt_exp: value-exp was given as e"*)
    | (Add _ | Sub _ | Mul _ | Div _ | Mod _ | Cons _ | Tuple _ | AppDExp _ | AppTy _ | AppMExp _ | Hd _ | Tl _ | Tget _), _ -> raise @@ Syntax_error(* "gt_exp : expression not contain exp was given as e"*)
    | (IfEqExp _ | IfLteExp _ | MatchExp _), (LetExp _ | LetRecSExp _ | LetRecAExp _ | LetRecBExp _) -> true
    | _ -> false
  
  let gte_exp e e1 = match e, e1 with
    (* | Add _, Add _ | Sub _, Sub _ | Mul _, Mul _ | Div _, Div _ | Mod _, Mod _ | Cons _, Cons _ | Tuple _, Tuple _ -> true *)
    (* | AppTy _, AppTy _ | AppDExp _, AppDExp _ | AppMExp _, AppMExp _ -> true *)
    (* | Hd _, Hd _ | Tl _, Tl _ | Tget _, Tget _ -> true *)
    | (LetExp _ | LetRecSExp _ | LetRecAExp _ | LetRecBExp _) , (LetExp _ | LetRecSExp _ | LetRecAExp _ | LetRecBExp _) -> true
    | (IfEqExp _ | IfLteExp _), (IfEqExp _ | IfLteExp _) -> true
    | MatchExp _, MatchExp _ -> true
    | _ -> gt_exp e e1

  let rec pp_exp ppf = function
    | Var x -> pp_print_string ppf x
    | IConst i -> pp_print_int ppf i
    | Nil -> pp_print_string ppf "[]"
    | Add (x, y) -> fprintf ppf "%s + %s" x y
    | Sub (x, y) -> fprintf ppf "%s - %s" x y
    | Mul (x, y) -> fprintf ppf "%s * %s" x y
    | Div (x, y) -> fprintf ppf "%s / %s" x y
    | Mod (x, y) -> fprintf ppf "%s mod %s" x y
    | Cons (x, y) -> fprintf ppf "%s :: %s" x y
    | Tuple xs -> 
      let pp_sep ppf () = fprintf ppf ", " in
      let pp_list ppf exps = pp_print_list pp_print_string ppf exps ~pp_sep:pp_sep in
      fprintf ppf "(%a)"
        pp_list xs
    | Tget (x, i) -> fprintf ppf "tget(%s, %d)" x i
    | Hd x -> fprintf ppf "hd(%s)" x
    | Tl x -> fprintf ppf "tl(%s)" x
    | IfEqExp (x, y, e1, e2) ->
      fprintf ppf "if %s=%s then %a else %a"
        x
        y
        pp_exp e1
        pp_exp e2
    | IfLteExp (x, y, e1, e2) ->
      fprintf ppf "if %s<=%s then %a else %a"
        x
        y
        pp_exp e1
        pp_exp e2
    | MatchExp (x, ms) as e ->
      fprintf ppf "match %s with%a"
        x        
        pp_match (ms, e)
    | AppMExp (x, y) ->
      fprintf ppf "%s %s" x y
    | AppDExp (x, (y, z)) -> 
      fprintf ppf "%s (%s, %s)" x y z
    | AppTy (x, _, tas) ->
      fprintf ppf "%s[%a]"
        x
        pp_print_tas tas
    | CAppExp (x, y) ->
      fprintf ppf "%s<%s>" x y
    | CastExp (x, u1, u2, _) ->
      fprintf ppf "%s: %a => %a"
        x
        pp_ty u1
        pp_ty u2
    | CSeqExp (x, y) -> 
      fprintf ppf "%s;;%s" x y
    | LetExp (x, e1, e2) as e ->
      fprintf ppf "let %s = %a in %a"
        x
        (with_paren (gt_exp e e1) pp_exp) e1
        pp_exp e2
    | CoercionExp c ->
      pp_coercion ppf c
    | LetRecSExp (x, tvs, (y, k), e1, e2) as e ->
      fprintf ppf "let %s = %afun (%s, %s) -> %a in %a"
        x
        pp_let_tyabses tvs
        y
        k
        (with_paren (gt_exp e e1) pp_exp) e1
        pp_exp e2
    | LetRecAExp (x, tvs, (y, k), (e1, e2), e3) as e ->
      fprintf ppf "let %s = %afun (%s, %s) -> (%a | %a) in %a"
        x
        pp_let_tyabses tvs
        y
        k
        (with_paren (gt_exp e e1) pp_exp) e1
        (with_paren (gt_exp e e2) pp_exp) e2
        pp_exp e3
    | LetRecBExp (x, tvs, y, e1, e2) as e ->
      fprintf ppf "let %s = %afun %s -> %a in %a"
        x
        pp_let_tyabses tvs
        y
        (with_paren (gt_exp e e1) pp_exp) e1
        pp_exp e2
  and pp_match ppf = function
    | ((mf, e1) :: m, e) -> 
      fprintf ppf " | %a -> %a%a"
        pp_matchform mf
        (with_paren (gte_exp e e1) pp_exp) e1
        pp_match (m, e)
    | ([], _) -> fprintf ppf ""
    
  let pp_program ppf = function
    | Exp e -> pp_exp ppf e
    | LetDecl (x, e) ->
      fprintf ppf "let %s = %a"
        x
        pp_exp e
    | LetRecSDecl (x, tvs, (y, k), e) ->
        fprintf ppf "let %s = %afun (%s, %s) -> %a"
          x
          pp_let_tyabses tvs
          y
          k
          pp_exp e
    | LetRecADecl (x, tvs, (y, k), (e1, e2)) ->
        fprintf ppf "let %s = %afun (%s, %s) -> (%a | %a)"
          x
          pp_let_tyabses tvs
          y
          k
          pp_exp e1
          pp_exp e2
    | LetRecBDecl (x, tvs, y, e) ->
        fprintf ppf "let %s = %afun %s -> %a"
          x
          pp_let_tyabses tvs
          y
          pp_exp e

  let gt_value v1 v2 = match v1, v2 with
    | (IntV _ | FunSV _ | FunAV _ | FunBV _ | NilV | TupleV _ | CoercionV _ | CoerceV _), ConsV _ -> true
    | (IntV _ | FunSV _ | FunAV _ | FunBV _ | NilV | TupleV _ | CoercionV _), CoerceV _ -> true
    | _ -> false

  let gte_value v1 v2 = match v1, v2 with
    | (FunSV _ | FunAV _ | FunBV _), (FunSV _ | FunAV _ | FunBV _) -> true
    | CoerceV _, CoerceV _ -> true
    | ConsV _, ConsV _ -> true
    | TupleV _, TupleV _ -> true
    | _ -> gt_value v1 v2

  let rec pp_value ppf = function
    | IntV i -> pp_print_int ppf i
    | NilV -> pp_print_string ppf "[]"
    | ConsV (v1, v2) as v ->
      fprintf ppf "%a :: %a"
        (with_paren (gte_value v v1) pp_value) v1
        (with_paren (gt_value v v2) pp_value) v2
    | TupleV vs ->
      let pp_sep ppf () = fprintf ppf ", " in
      let pp_list ppf vals = pp_print_list pp_value ppf vals ~pp_sep:pp_sep in
      fprintf ppf "(%a)"
        pp_list vs
    | FunSV _ | FunAV _ | FunBV _ -> pp_print_string ppf "<fun>"
    | CoerceV (v1, c) as v -> 
      fprintf ppf "%a<<%a>>"
        (with_paren (gt_value v v1) pp_value) v1
        pp_coercion c
    | Tagged (t, v) ->
      fprintf ppf "%a: %a => ?"
        pp_value v
        pp_tag t
    | CoercionV c -> pp_coercion ppf c

  let rec pp_value2 ppf = function
    | IntV i -> pp_print_int ppf i
    | NilV -> pp_print_string ppf "[]"
    | ConsV (v1, v2) as v ->
      fprintf ppf "%a :: %a"
        (with_paren (gte_value v v1) pp_value2) v1
        (with_paren (gt_value v v2) pp_value2) v2
    | TupleV vs ->
      let pp_sep ppf () = fprintf ppf ", " in
      let pp_list ppf vals = pp_print_list pp_value2 ppf vals ~pp_sep:pp_sep in
      fprintf ppf "(%a)"
        pp_list vs
    | FunSV _ | FunAV _ | FunBV _ -> pp_print_string ppf "<fun>"
    | CoerceV (v1, c) as v -> 
      fprintf ppf "%a<<%a>>"
        (with_paren (gt_value v v1) pp_value2) v1
        pp_coercion2 c
    | Tagged (t, v) ->
      fprintf ppf "%a: %a => ?"
        pp_value2 v
        pp_tag t
    | CoercionV c -> pp_coercion2 ppf c
end

module Cls = struct
  open Syntax.Cls

  let gt_coercion c1 c2 = match c1, c2 with
    | (CTvInj _ | CTvProj _ | CId | CFun _ | CList _ | CTuple _), (CSeqInj _ | CSeqProj _) -> true
    | _ -> false

  let gte_coercion c1 c2 = match c1, c2 with
    | CFun _, CFun _ -> true
    | CTuple _, CTuple _ -> true
    (* | CList _, CList _ is intentionally ommited *)
    | _ -> gt_coercion c1 c2

  let rec pp_coercion ppf = function
    | CId -> fprintf ppf "id"
    (* | Fail _ -> fprintf ppf "⊥" *)
    | CSeqInj (c, t) -> fprintf ppf "%a;%a!" pp_coercion c pp_tag t
    | CSeqProj (t, _, c) -> fprintf ppf "%a?p;%a" pp_tag t pp_coercion c
    (* | SeqProjInj (t1, _, c, t2) -> fprintf ppf "%a?p;%a;%a!" pp_tag t1 pp_coercion c pp_tag t2 *)
    | CTvInj (tv, _) -> fprintf ppf "%a!" pp_ty (TyVar tv)
    | CTvProj (tv, _) -> fprintf ppf "%a?p" pp_ty (TyVar tv)
    (* | TvProjInj (tv, _) -> fprintf ppf "?p%a!" pp_ty (TyVar tv) *)
    | CFun (c1, c2) -> fprintf ppf "%a->%a" pp_coercion c1 pp_coercion c2
    | CList c -> fprintf ppf "[%a]" pp_coercion c
    | CTuple cs as c ->
      let pp_sep ppf () = fprintf ppf "*" in
      let pp_list ppf crcs = pp_print_list (fun ppf c' -> (with_paren (gte_coercion c c') pp_coercion) ppf c') ppf crcs ~pp_sep:pp_sep in
      fprintf ppf "%a"
        pp_list cs

  let pp_let_tyabses ppf tyvars =
    if List.length tyvars = 0 then
      fprintf ppf ""
    else
      let pp_sep ppf () = fprintf ppf "," in
      let pp_list ppf types = pp_print_list pp_ty ppf types ~pp_sep:pp_sep in
      fprintf ppf "[%a] " pp_list @@ List.map (fun x -> TyVar x) tyvars
  
  let pp_print_cls ppf { entry = x; actual_fv = ids } =
    if List.length ids = 0 then 
      fprintf ppf "%s" x
    else let pp_sep ppf () = fprintf ppf "," in
    let pp_list ppf xs = pp_print_list pp_print_string ppf xs ~pp_sep:pp_sep in
    fprintf ppf "%s[%a]"
      x
      pp_list ids

  let rec pp_exp ppf = function
    | Var x -> pp_print_string ppf x
    | Int i -> pp_print_int ppf i
    | Nil -> pp_print_string ppf "[]"
    | Add (x, y) -> fprintf ppf "%s + %s" x y
    | Sub (x, y) -> fprintf ppf "%s - %s" x y
    | Mul (x, y) -> fprintf ppf "%s * %s" x y
    | Div (x, y) -> fprintf ppf "%s / %s" x y
    | Mod (x, y) -> fprintf ppf "%s mod %s" x y
    | Cons (x, y) -> fprintf ppf "%s :: %s" x y
    | Tuple xs ->
      let pp_sep ppf () = fprintf ppf ", " in
      let pp_list ppf vars = pp_print_list pp_print_string ppf vars ~pp_sep:pp_sep in
      fprintf ppf "(%a)"
        pp_list xs
    | Hd x -> fprintf ppf "hd(%s)" x
    | Tl x -> fprintf ppf "tl(%s)" x
    | Tget (x, i) -> fprintf ppf "tget(%s, %i)" x i
    | IfEq (x, y, e1, e2) ->
      fprintf ppf "if %s=%s then %a else %a"
        x
        y
        pp_exp e1
        pp_exp e2
    | IfLte (x, y, e1, e2) ->
      fprintf ppf "if %s<=%s then %a else %a"
        x
        y
        pp_exp e1
        pp_exp e2
    | Match (x, ms) ->
      fprintf ppf "match %s with%a"
        x        
        pp_match ms
    | AppDCls (x, (y, z)) -> fprintf ppf "%s:cls (%s, %s)" x y z
    | AppDDir (l, (y, z)) -> fprintf ppf "%s:label (%s, %s)" l y z
    | AppMCls (x, y) -> fprintf ppf "%s:cls_alt %s" x y
    | AppMDir (l, y) -> fprintf ppf "%s:label_alt %s" l y
    | AppTy (x, _, _, tas) ->
      fprintf ppf "%s[%a]"
        x
        pp_print_tas tas
    | SetTy ((i, { contents = None }), f) -> 
      fprintf ppf "set _ty%d = TYVAR in %a"
        i
        pp_exp f
    | SetTy ((i, { contents = Some (TyFun (u1, u2)) }), f) -> 
      fprintf ppf "set _tyfun%d = TYFUN(%a, %a) in %a"
        i
        pp_ty u1
        pp_ty u2
        pp_exp f
    | SetTy ((i, { contents = Some (TyList u) }), f) -> 
      fprintf ppf "set _tylist%d = TYLIST(%a) in %a"
        i
        pp_ty u
        pp_exp f
    | SetTy ((i, { contents = Some (TyTuple us) }), f) ->
      let pp_sep ppf () = fprintf ppf ", " in
      let pp_list ppf tys = pp_print_list pp_ty ppf tys ~pp_sep:pp_sep in
      fprintf ppf "set _tylist%d = TYTUPLE(%a) in %a"
        i
        pp_list us
        pp_exp f
    | SetTy _ -> raise @@ Syntax_error
    | Cast (x, u1, u2, _) ->
        fprintf ppf "%s: %a => %a"
          x
          pp_ty u1
          pp_ty u2
    | CApp (x, y) ->
      fprintf ppf "%s<%s>" x y
    | CSeq (x, y) ->
      fprintf ppf "%s;;%s" x y
    | Coercion c ->
      fprintf ppf "%a"
        pp_coercion c
    | MakeCls (x, cls, _, f) ->
      fprintf ppf "cls %s = %a in %a"
        x
        pp_print_cls cls
        pp_exp f
    | Let (x, f1, f2) ->
        fprintf ppf "let %s = %a in %a"
          x
          pp_exp f1
          pp_exp f2
    | Insert _ -> raise @@ Syntax_error (*"insert or setty was applied to Cls.pp_exp"*)
  and pp_match ppf = function
    | (mf, e) :: m -> 
      fprintf ppf " | %a -> %a%a"
        pp_matchform mf
        pp_exp e
        pp_match m
    | [] -> fprintf ppf ""

  let pp_fv ppf x =
    fprintf ppf "%s"
      x

  let pp_print_fv ppf fvl =
    let pp_sep ppf () = fprintf ppf "," in
    let pp_list ppf fvs = pp_print_list pp_fv ppf fvs ~pp_sep:pp_sep in
    fprintf ppf "%a"
      pp_list fvl

  let pp_fundef ppf fundef = match fundef with
  | FundefD { name = l; tvs = (tvs, _); arg = (y, z); formal_fv = fvl; body = f} ->
    if List.length fvl = 0 then
      fprintf ppf "let rec %s %a(%s, %s) = %a"
        l
        pp_let_tyabses tvs
        y
        z
        pp_exp f
    else
      fprintf ppf "let rec %s %a(%s, %s) = %a (fv:%a)"
        l
        pp_let_tyabses tvs
        y
        z
        pp_exp f
        pp_print_fv fvl
  | FundefM { name = l; tvs = (tvs, _); arg = y; formal_fv = fvl; body = f} -> 
    if List.length fvl = 0 then
      fprintf ppf "let rec %s %a%s = %a"
        l
        pp_let_tyabses tvs
        y
        pp_exp f
    else
      fprintf ppf "let rec %s %a%s = %a (fv:%a)"
        l
        pp_let_tyabses tvs
        y
        pp_exp f
        pp_print_fv fvl

  let pp_toplevel ppf toplevel =
    let pp_sep ppf () = fprintf ppf "\n" in
    let pp_list ppf defs = pp_print_list pp_fundef ppf defs ~pp_sep:pp_sep in
    fprintf ppf "%a"
      pp_list toplevel

  let pp_program ppf = function
    | Prog (toplevel, cf) ->
      if List.length toplevel = 0 
        then 
          fprintf ppf "exp:\n%a"
            pp_exp cf
        else
          fprintf ppf "%a\nexp:\n%a"
            pp_toplevel toplevel
            pp_exp cf
end
