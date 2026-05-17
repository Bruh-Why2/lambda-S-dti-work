open Format
open Syntax

exception Eval_bug of string

let subst_type = Typing.subst_type

let fresh_tyvar = Typing.fresh_tyvar

let type_of_tag = Typing.type_of_tag

let tag_of_ty = Typing.tag_of_ty

let nu_to_fresh = function
| Ty u -> u
| TyNu -> Typing.fresh_tyvar ()

let rec subst_mf s = function
  | MatchILit _ | MatchBLit _ | MatchULit as mf -> mf
  | MatchWild u -> MatchWild (subst_type s u)
  | MatchVar (x, u) -> MatchVar (x, subst_type s u)
  | MatchNil u -> MatchNil (subst_type s u)
  | MatchCons (mf1, mf2) -> MatchCons (subst_mf s mf1, subst_mf s mf2)
  | MatchTuple mfs -> MatchTuple (List.map (fun mf -> subst_mf s mf) mfs)

let rec normalize_coercion c = match c with
  | CId TyDyn -> c
  | CSeq (CProj _ as c1, c2) -> CSeq (c1, normalize_coercion c2)
  | CTvProj ((_, {contents = Some u}), p) when is_base_type u ->
    normalize_coercion (CSeq (CProj (tag_of_ty u, p), CId u))
  | CTvProj ((_, {contents = Some (TyVar tv)}), p) ->
    normalize_coercion (CTvProj (tv, p))
  | CTvProj ((_, {contents = Some (TyFun (TyVar tv1, TyVar tv2))}), (r, p)) ->
    normalize_coercion (CSeq (CProj (Ar, (r, p)), CFun (CTvInj (tv1, (r, neg p)), CTvProj (tv2, (r, p)))))
  | CTvProj ((_, {contents = Some (TyList (TyVar tv))}), p) ->
    normalize_coercion (CSeq (CProj (Li, p), CList (CTvProj (tv, p))))
  | CTvProj ((_, {contents = None}), _) -> c
  | CTvInj ((_, {contents = Some u }), _) when is_base_type u ->
    normalize_coercion (CSeq (CId u, CInj (tag_of_ty u)))
  | CTvInj ((_, {contents = Some (TyVar tv)}), p) ->
    normalize_coercion (CTvInj (tv, p))
  | CTvInj ((_, {contents = Some (TyFun (TyVar tv1, TyVar tv2))}), (r, p)) ->
    normalize_coercion (CSeq (CFun (CTvProj (tv1, (r, neg p)), CTvInj (tv2, (r, p))), CInj Ar))
  | CTvInj ((_, {contents = Some (TyList (TyVar tv))}), p) ->
    normalize_coercion (CSeq (CList (CTvInj (tv, p)), CInj Li))
  | CTvInj ((_, {contents = None}), _) -> c
  | CTvProjInj ((_, {contents = Some u}), p, _) when is_base_type u ->
    normalize_coercion (CSeq (CProj (tag_of_ty u, p), CSeq (CId u, CInj (tag_of_ty u))))
  | CTvProjInj ((_, {contents = Some (TyVar tv)}), p, q) ->
    normalize_coercion (CTvProjInj (tv, p, q))
  | CTvProjInj ((_, {contents = Some (TyFun (TyVar tv1, TyVar tv2))}), (r1, p), (r2, q)) ->
    normalize_coercion (CSeq (CProj (Ar, (r1, p)), CSeq (CFun (CTvProjInj (tv1, (r2, neg q), (r1, neg p)), CTvProjInj (tv2, (r1, p), (r2, q))), CInj Ar)))
  | CTvProjInj ((_, {contents = Some (TyList (TyVar tv))}), p, q) ->
    normalize_coercion (CSeq (CProj (Li, p), CSeq (CList (CTvProjInj (tv, p, q)), CInj Li)))
  | CTvProjInj ((_, {contents = None}), _, _) -> c
  | CSeq (c1, (CInj _ as c2)) -> CSeq (normalize_coercion c1, c2)
  | CFail _ as c -> c
  | CId (TyVar (_, {contents = Some u})) -> normalize_coercion (CId u)
  | CId _ as c -> c
  | CFun (s, t) -> 
    let s' = normalize_coercion s in
    let t' = normalize_coercion t in
    begin match s', t' with
      | CId u1, CId u2 -> CId (TyFun (u1, u2))
      | _ -> CFun (s', t')
    end
  | CList s -> 
    let s' = normalize_coercion s in
    begin match s' with
      | CId u -> CId (TyList u)
      | _ -> CList s'
    end
  | CTuple ss ->
    let rec check_id l r = match l with
    | CId u :: t -> check_id t (u :: r)
    | _ :: _ -> (false, r) (* r is dummy *)
    | [] -> (true, List.rev r)
    in
    let (is_id, id_u) = check_id ss [] in
    if is_id then CId (TyTuple id_u)
    else CTuple ss
  | CTvProj ((i, {contents = Some (TyFun (u1, u2))}), (r, p)) -> 
    normalize_coercion (CSeq (CProj (Ar, (r, p)), CFun (CTvInj ((i, ref (Some u1)), (r, neg p)), CTvProj ((i, ref (Some u2)), (r, p)))))
  | CTvInj ((i, {contents = Some (TyFun (u1, u2))}), (r, p)) ->
    normalize_coercion (CSeq (CFun (CTvProj ((i, ref (Some u1)), (r, neg p)), CTvInj ((i, ref (Some u2)), (r, p))), CInj Ar))
  | CTvProjInj ((i, {contents = Some (TyFun (u1, u2))}), (r, p), (r', q)) ->
    normalize_coercion (CSeq (CProj (Ar, (r, p)), CSeq (CFun (CTvProjInj ((i, ref (Some u1)), (r', neg q), (r, neg p)), CTvProjInj ((i, ref (Some u2)), (r, p), (r, q))), CInj Ar)))
  | CTvProj ((i, {contents = Some (TyList u)}), p) -> 
    normalize_coercion (CSeq (CProj (Li, p), CList (CTvProj ((i, ref (Some u)), p))))
  | CTvInj ((i, {contents = Some (TyList u)}), p) ->
    normalize_coercion (CSeq (CList (CTvInj ((i, ref (Some u)), p)), CInj Li))
  | CTvProjInj ((i, {contents = Some (TyList u)}), p, q) ->
    normalize_coercion (CSeq (CProj (Li, p), CSeq (CList (CTvProjInj ((i, ref (Some u)), p, q)), CInj Li)))
  | c -> raise @@ Eval_bug (Format.asprintf "cannot normalize coercion: %a" Pp.pp_coercion c)

let rec subst_coercion s = function
| CInj _ | CProj _ as c -> c
| CTvInj ((a, _ as tv), p) -> 
  let u = subst_type s (TyVar tv) in
  normalize_coercion (CTvInj ((a, {contents = Some u}), p))
| CTvProj ((a, _ as tv), p) ->
  let u = subst_type s (TyVar tv) in
  normalize_coercion (CTvProj ((a, {contents = Some u}), p))
| CTvProjInj ((a, _ as tv), p, q) -> 
  let u = subst_type s (TyVar tv) in
  normalize_coercion (CTvProjInj ((a, {contents = Some u}), p, q))
| CFun (c1, c2) -> CFun (subst_coercion s c1, subst_coercion s c2)
| CList c -> CList (subst_coercion s c)
| CTuple cs -> CTuple (List.map (fun c -> subst_coercion s c) cs)
| CId u -> CId (subst_type s u)
| CSeq (c1, c2) -> CSeq (subst_coercion s c1, subst_coercion s c2)
| CFail _ as c -> c

let rec compose ?(debug=false) c1 c2 = (* TODO : blame *)
  if debug then fprintf err_formatter "compose <-- %a；%a@." Pp.pp_coercion c1 Pp.pp_coercion c2;
  let compose = compose ~debug:debug in
  match normalize_coercion c1, normalize_coercion c2 with
  (* id{star} ;;; t *)
  | CId TyDyn, c2 -> c2
  (* G?p;i ;;; t *)
  | CSeq (CProj (t, p), c1), c2 -> CSeq (CProj (t, p), compose c1 c2)
  (* X?p ;;; t *)
  | CTvProj ((a1, _ as tv), p), CId (TyVar (a2, _)) when a1 = a2 -> CTvProj (tv, p)
  | CTvProj ((a1, _ as tv), p), CTvInj ((a2, _), q) when a1 = a2 -> CTvProjInj (tv, p, q)
  (* X! ;;; t *)
  | CTvInj (tv, p), CId TyDyn -> CTvInj (tv, p)
  | CTvInj ((_, uref as tv), (r, p)), CSeq (CProj (Ar, _), c2) ->
    let x1, x2 = fresh_tyvar (), fresh_tyvar () in
    if debug then fprintf err_formatter "DTI: %a is instantiated to %a@." Pp.pp_ty (TyVar tv) Pp.pp_ty (TyFun (x1, x2));
    uref := Some (TyFun (x1, x2));
    begin match x1, x2 with
      | TyVar tv1, TyVar tv2 ->
        compose (CFun (CTvProj (tv1, (r, neg p)), (CTvInj (tv2, (r, p))))) c2
      | _ -> raise @@ Eval_bug "compose: unexpected type of coercion"
    end
  | CTvInj ((_, uref as tv), p), CSeq (CProj (Li, _), c2) ->
    let x1 = fresh_tyvar () in
    if debug then fprintf err_formatter "DTI: %a is instantiated to %a@." Pp.pp_ty (TyVar tv) Pp.pp_ty (TyList x1);
    uref := Some (TyList x1);
    begin match x1 with
      | TyVar tv1 ->
        compose (CList (CTvInj (tv1, p))) c2
      | _ -> raise @@ Eval_bug "compose: unexpected type of coercion"
    end
  | CTvInj ((_, uref as tv), p), CSeq (CProj ((Tp n), _), c2) ->
    let xs = List.map (fun _ -> fresh_tyvar ()) (make_dyn_list n) in
    if debug then fprintf err_formatter "DTI: %a is instantiated to %a@." Pp.pp_ty (TyVar tv) Pp.pp_ty (TyTuple xs);
    uref := Some (TyTuple xs);
    let rec make_c1 l r = match l with
    | TyVar tv :: t -> 
      make_c1 t (CTvInj (tv, p) :: r)
    | _ :: _ -> raise @@ Eval_bug "compose: unexpected type of coercion"
    | [] -> CTuple (List.rev r)
    in
    compose (make_c1 xs []) c2
  | CTvInj ((_, uref as tv), _), CSeq (CProj (t, _), c2) -> 
    let u = type_of_tag t in
    if debug then fprintf err_formatter "DTI: %a is instantiated to %a@." Pp.pp_ty (TyVar tv) Pp.pp_ty u;
    uref := Some u;
    compose (CId u) c2
  | CTvInj ((a1, uref as tv1), _), CTvProj ((a2, _ as tv2), _) -> 
    if a1 = a2 then CId (TyVar tv1)
    else begin 
      if debug then fprintf err_formatter "DTI: %a is instantiated to %a@." Pp.pp_ty (TyVar tv1) Pp.pp_ty (TyVar tv2);
      uref := Some (TyVar tv2); 
      CId (TyVar tv2)
    end
  | CTvInj (tv1, p), CTvProjInj (tv2, q, r) ->
    compose (compose (CTvInj (tv1, p)) (CTvProj (tv2, q))) (CTvInj (tv2, r))
    (* if a1 = a2 then CTvInj tv1
    else (uref := Some (TyVar tv2); CTvInj tv2) *)
  (* ?pX! ;;; t *)
  | CTvProjInj (tv, p, q), c2 ->
    compose (CTvProj (tv, p)) (compose (CTvInj (tv, q)) c2)
  (* | CTvProjInj (tv, p), CId TyDyn -> CTvProjInj (tv, p)
  | CTvProjInj ((_, uref), p), CSeq (CProj (Ar, (r', q)), c2) ->
    let x1, x2 = fresh_tyvar (), fresh_tyvar () in
    uref := Some (TyFun (x1, x2));
    begin match x1, x2 with
    | TyVar tv1, TyVar tv2 ->
      compose (CSeq (CProj (Ar, p), CFun (CTvProjInj (tv1, (r', neg q)), CTvProjInj (tv2, p)))) c2
    | _ -> raise @@ Eval_bug "compose: unexpected type of coercion"
    end
  | CTvProjInj ((_, uref), p), CSeq (CProj (t, _), c2) -> 
    uref := Some (type_of_tag t);
    compose (CSeq (CProj (t, p), CId (type_of_tag t))) c2
  | CTvProjInj ((a1, uref as tv1), p), CTvProj ((a2, _ as tv2), _) -> 
    if a1 = a2 then CTvProj (tv1, p)
    else (uref := Some (TyVar tv2); CTvProj (tv2, p))
  | CTvProjInj ((a1, uref as tv1), p), CTvProjInj ((a2, _ as tv2), _) ->
    if a1 = a2 then CTvProjInj (tv1, p)
    else (uref := Some (TyVar tv2); CTvProjInj (tv2, p)) *)
  (* i ;;; t *)
  | CSeq (_, CInj _) as c1, CId TyDyn -> c1
  | CSeq (c1, CInj t), CSeq (CProj (t', p), c2) ->
    if t = t' then compose c1 c2 
    else CFail (t, p, t')
  | CSeq (c1, CInj Ar), CTvProj ((_, uref as tv), (r, p)) ->
    let x1, x2 = fresh_tyvar (), fresh_tyvar () in
    if debug then fprintf err_formatter "DTI: %a is instantiated to %a@." Pp.pp_ty (TyVar tv) Pp.pp_ty (TyFun (x1, x2));
    uref := Some (TyFun (x1, x2));
    begin match x1, x2 with
      | TyVar tv1, TyVar tv2 ->
        compose c1 (CFun (CTvInj (tv1, (r, neg p)), CTvProj (tv2, (r, p))))
      | _ -> raise @@ Eval_bug "compose: unexpected type of coercion"
    end
  | CSeq (c1, CInj Li), CTvProj ((_, uref as tv), p) ->
    let x1 = fresh_tyvar () in
    if debug then fprintf err_formatter "DTI: %a is instantiated to %a@." Pp.pp_ty (TyVar tv) Pp.pp_ty (TyList x1);
    uref := Some (TyList x1);
    begin match x1 with
      | TyVar tv1 ->
        compose c1 (CList (CTvProj (tv1, p)))
      | _ -> raise @@ Eval_bug "compose: unexpected type of coercion"
    end
  | CSeq (c1, CInj (Tp n)), CTvProj ((_, uref as tv), p) ->
    let xs = List.map (fun _ -> fresh_tyvar ()) (make_dyn_list n) in
    if debug then fprintf err_formatter "DTI: %a is instantiated to %a@." Pp.pp_ty (TyVar tv) Pp.pp_ty (TyTuple xs);
    uref := Some (TyTuple xs);
    let rec make_c2 l r = match l with
    | TyVar tv :: t -> 
      make_c2 t (CTvProj (tv, p) :: r)
    | _ :: _ -> raise @@ Eval_bug "compose: unexpected type of coercion"
    | [] -> CTuple (List.rev r)
    in
    compose c1 (make_c2 xs [])
  | CSeq (c1, CInj t), CTvProj ((_, uref as tv), _) ->
    let u = type_of_tag t in
    if debug then fprintf err_formatter "DTI: %a is instantiated to %a@." Pp.pp_ty (TyVar tv) Pp.pp_ty u;
    uref := Some u;
    compose c1 (CId u)
  | CSeq (_, (CInj _)) as c1, CTvProjInj (tv, p, q) ->
    compose (compose c1 (CTvProj (tv, p))) (CTvInj (tv, q))
  (* | CSeq (c1, CInj Ar), CTvProjInj ((_, uref), (r, p)) ->
    let x1, x2 = fresh_tyvar (), fresh_tyvar () in
    uref := Some (TyFun (x1, x2));
    begin match x1, x2 with
      | TyVar tv1, TyVar tv2 ->
        compose c1 (CSeq (CFun (CTvProjInj (tv1, (r, neg p)), CTvProjInj (tv2, (r, p))), CInj Ar))
      | _ -> raise @@ Eval_bug "compose: unexpected type of coercion"
    end
  | CSeq (c1, CInj t), CTvProjInj ((_, uref), _) ->
    uref := Some (type_of_tag t);
    compose c1 (CSeq (CId (type_of_tag t), CInj t)) *)
  | CFail _ as c1, _ -> c1
  (* g ;;; i *)
  | _, (CFail _ as c2) (*when is_g c1*) -> c2
  | c1, CSeq (c2, CInj t) (*when is_g c1*) -> CSeq (compose c1 c2, CInj t)
  (* g ;;; g *)
  | CId _, c2 -> c2
  | c1, CId _ -> c1
  | CFun (s, t), CFun (s', t') ->
    let c1 = compose s' s in
    let c2 = compose t t' in
    begin match c1, c2 with
      | CId u1, CId u2 -> CId (TyFun (u1, u2))
      | _ -> CFun (c1, c2) 
    end
  | CList s, CList s' ->
    let c = compose s s' in
    begin match c with
      | CId u -> CId (TyList u)
      | _ -> CList c
    end
  | CTuple ss1, CTuple ss2 ->
    let ss = List.map2 (fun s1 s2 -> compose s1 s2) ss1 ss2 in
    let rec check_id l r = match l with
    | CId u :: t -> check_id t (u :: r)
    | _ :: _ -> (false, r) (* r is dummy *)
    | [] -> (true, List.rev r)
    in
    let (is_id, id_u) = check_id ss [] in
    if is_id then CId (TyTuple id_u)
    else CTuple ss
  | _ -> raise @@ Eval_bug "cannot compose coercions"

module CC = struct
  open Syntax.CC

  let rec subst_exp s = function
    | Var (x, ys) ->
      let subst_type = function
        | Ty u -> Ty (subst_type s u)
        | TyNu -> TyNu
      in
      Var (x, List.map subst_type ys)
    | IConst _
    | BConst _
    | UConst as f -> f
    | BinOp (op, f1, f2) -> BinOp (op, subst_exp s f1, subst_exp s f2)
    | IfExp (f1, f2, f3) -> IfExp (subst_exp s f1, subst_exp s f2, subst_exp s f3)
    | FunBExp ((x1, u1), f) -> FunBExp ((x1, subst_type s u1), subst_exp s f)
    | FixBExp ((x, y, u1, u2), f) ->
      FixBExp ((x, y, subst_type s u1, subst_type s u2), subst_exp s f)
    | FunSExp ((x1, u1), k, f) -> FunSExp ((x1, subst_type s u1), k, subst_exp s f)
    | FixSExp ((x, y, u1, u2), k, f) ->
      FixSExp ((x, y, subst_type s u1, subst_type s u2), k, subst_exp s f)
    | FunAExp ((x1, u1), k, (f1, f2)) -> FunAExp ((x1, subst_type s u1), k, (subst_exp s f1, subst_exp s f2))
    | FixAExp ((x, y, u1, u2), k, (f1, f2)) ->
      FixAExp ((x, y, subst_type s u1, subst_type s u2), k, (subst_exp s f1, subst_exp s f2))
    | NilExp u -> NilExp (subst_type s u)
    | ConsExp (f1, f2) -> ConsExp (subst_exp s f1, subst_exp s f2)
    | TupleExp fs -> TupleExp (List.map (fun f -> subst_exp s f) fs)
    | AppMExp (f1, f2) -> AppMExp (subst_exp s f1, subst_exp s f2)
    | AppDExp (f1, (f2, f3)) -> AppDExp (subst_exp s f1, (subst_exp s f2, subst_exp s f3))
    | CastExp (f, u1, u2, r_p) -> CastExp (subst_exp s f, subst_type s u1, subst_type s u2, r_p)
    | CoercionExp c -> CoercionExp (subst_coercion s c)
    | CAppExp (f1, f2) -> CAppExp (subst_exp s f1, subst_exp s f2)
    | CSeqExp (f1, f2) -> CSeqExp (subst_exp s f1, subst_exp s f2)
    | MatchExp (f, ms) -> 
      MatchExp (subst_exp s f, List.map (fun (mf, f) -> subst_mf s mf, subst_exp s f) ms)
    | LetExp (y, ys, f1, f2) ->
      (* Remove substitutions captured by let exp s *)
      let s = List.filter (fun (x, _) -> not @@ List.memq x ys) s in
      LetExp (y, ys, subst_exp s f1, subst_exp s f2)

  let eval_binop op v1 v2 =
    begin match op, v1, v2 with
      | Plus, IntV i1, IntV i2 -> IntV (i1 + i2)
      | Minus, IntV i1, IntV i2 -> IntV (i1 - i2)
      | Mult, IntV i1, IntV i2 -> IntV (i1 * i2)
      | Div, IntV i1, IntV i2 -> IntV (i1 / i2)
      | Mod, IntV i1, IntV i2 -> IntV (i1 mod i2)
      | Eq, IntV i1, IntV i2 -> BoolV (i1 = i2)
      | Neq, IntV i1, IntV i2 -> BoolV (i1 <> i2)
      | Lt, IntV i1, IntV i2 -> BoolV (i1 < i2)
      | Lte, IntV i1, IntV i2 -> BoolV (i1 <= i2)
      | Gt, IntV i1, IntV i2 -> BoolV (i1 > i2)
      | Gte, IntV i1, IntV i2 -> BoolV (i1 >= i2)
      | _ -> raise @@ Eval_bug "binop: unexpected type of argument"
    end

  let rec eval ?(debug=false) (env: (tyvar list * value) Environment.t) f =
    if debug then fprintf err_formatter "eval <-- %a@." Pp.CC.pp_exp f;
    let eval = eval ~debug:debug in
    match f with
    | Var (x, us) ->
      let xs, v = Environment.find x env in
      let us = List.map nu_to_fresh us in
      begin match v with
        | FunBV proc -> FunBV (fun _ -> proc (xs, us))
        | FunSV proc -> FunSV (fun _ -> proc (xs, us))
        | FunAV proc -> FunAV (fun _ -> proc (xs, us))
        | _ -> v
      end
    | IConst i -> IntV i
    | BConst b -> BoolV b
    | UConst -> UnitV
    | BinOp (op, f1, f2) ->
      let v1 = eval env f1 in
      let v2 = eval env f2 in
      eval_binop op v1 v2
    | FunBExp ((x, _), f') ->
      FunBV (
        fun (xs, ys) -> fun v ->
          eval (Environment.add x ([], v) env) @@ subst_exp (Utils.List.zip xs ys) f'
      )
    | FixBExp ((x, y, _, _), f') ->
      let f (xs, ys) v =
        let f' = subst_exp (Utils.List.zip xs ys) f' in
        let rec f _ v =
          let env = Environment.add x (xs, FunBV f) env in
          let env = Environment.add y ([], v) env in
          eval env f'
        in f ([], []) v
      in FunBV f
    | FunSExp ((x, _), k, f') ->
      FunSV (
        fun (xs, ys) -> fun (v, w) ->
          eval (Environment.add x ([], v) (Environment.add k ([], w) env)) @@ subst_exp (Utils.List.zip xs ys) f'
      )
    | FixSExp ((x, y, _, _), k, f') ->
      let f (xs, ys) (v, w) =
        let f' = subst_exp (Utils.List.zip xs ys) f' in
        let rec f _ (v, w) =
          let env = Environment.add x (xs, FunSV f) env in
          let env = Environment.add y ([], v) env in
          let env = Environment.add k ([], w) env in
          eval env f'
        in f ([], []) (v, w)
      in FunSV f
    | FunAExp ((x, _), k, (f', f'')) ->
      FunAV (
        fun (xs, ys) -> 
          (fun v -> eval (Environment.add x ([], v) env) @@ subst_exp (Utils.List.zip xs ys) f'),
          (fun (v, w) -> eval (Environment.add x ([], v) (Environment.add k ([], w) env)) @@ subst_exp (Utils.List.zip xs ys) f'')
      )
    | FixAExp ((x, y, _, _), k, (f', f'')) ->
      let f (xs, ys) =
        let f' = subst_exp (Utils.List.zip xs ys) f' in
        let f'' = subst_exp (Utils.List.zip xs ys) f'' in
        let rec f1' v =
          let env = Environment.add x (xs, FunAV (fun _ -> (f1', f2'))) env in
          let env = Environment.add y ([], v) env in
          eval env f'
        and f2' (v, w) =
          let env = Environment.add x (xs, FunAV (fun _ -> (f1', f2'))) env in
          let env = Environment.add y ([], v) env in
          let env = Environment.add k ([], w) env in
          eval env f''
        in (f1', f2')
      in FunAV f
    | AppMExp (f1, f2) ->
      let v1 = eval env f1 in
      let v2 = eval env f2 in
      eval_app_valM env v1 v2 ~debug:debug
    | AppDExp (f1, (f2, f3)) ->
      let v1 = eval env f1 in
      let v2 = eval env f2 in
      let v3 = eval env f3 in
      eval_app_valD env v1 v2 v3 ~debug:debug
    | IfExp (f1, f2, f3) ->
      let v1 = eval env f1 in
      begin match v1 with
        | BoolV true -> eval env f2
        | BoolV false -> eval env f3
        | _ -> raise @@ Eval_bug "if: non boolean value"
      end
    | LetExp (x, xs, f1, f2) ->
      let v1 = eval env f1 in
      eval (Environment.add x (xs, v1) env) f2
    | MatchExp (f, ms) ->
      let v = eval env f in
      eval_next ~debug:debug env v ms
    | NilExp _ -> NilV
    | ConsExp (f1, f2) ->
      let v2 = eval env f2 in
      let v1 = eval env f1 in
      ConsV (v1, v2)
    | TupleExp fs -> TupleV (List.map (fun f -> eval env f) fs)
    | CastExp (f, u1, u2, r_p) ->
      let v = eval env f in
      cast ~debug:debug v u1 u2 r_p
    | CAppExp (f1, f2) ->
      let v1 = eval env f1 in
      let v2 = eval env f2 in
      begin match v2 with
        | CoercionV c -> coerce ~debug:debug v1 c
        | _ -> raise @@ Eval_bug "capp: application of non coercion value"
      end
    | CSeqExp (f1, f2) ->
      let v1 = eval env f1 in
      let v2 = eval env f2 in
      begin match v1, v2 with
        | CoercionV c1, CoercionV c2 -> CoercionV (compose c1 c2 ~debug:debug)
        | _ -> raise @@ Eval_bug "cseq: sequence of non coercion value"
      end
    | CoercionExp c -> CoercionV c
  and match_mf ?(debug=false) env v mf = match v, mf with
    | _, MatchVar (id, _) ->
      let env = Environment.add id ([], v) env in
      true, env
    | ConsV (v1, v2), MatchCons (mf1, mf2) ->
      let b1, env = match_mf ~debug:debug env v1 mf1 in
      let b2, env = match_mf ~debug:debug env v2 mf2 in
      b1&&b2, env 
    | NilV, MatchNil _ -> true, env
    | IntV i1, MatchILit i2 -> if i1 = i2 then (true, env) else (false, env)
    | BoolV b1, MatchBLit b2 -> if b1 = b2 then (true, env) else (false, env)
    | UnitV, MatchULit -> true, env
    | TupleV vs, MatchTuple mfs ->
      let rec iter env vs mfs b = match vs, mfs with
      | v :: vs, mf :: mfs ->
        let b', env = match_mf ~debug:debug env v mf in
        iter env vs mfs (b && b')
      | _ :: _, [] | [], _ :: _ -> false, env
      | [], [] -> b, env
      in
      iter env vs mfs true
    (* | arg, MatchAsc (mf, _) -> match_mf env arg mf *)
    | _, MatchWild _ -> true, env
    | CoerceV (ConsV (v1, v2), CList s), MatchCons _ -> 
      match_mf ~debug:debug env (ConsV (coerce ~debug:debug v1 s, coerce ~debug:debug v2 (CList s))) mf (* lazy *)
    | _ -> false, env 
  and eval_next ?(debug=false) env v ms = match ms with
    | (mf, f) :: ms ->
      let b, env' = match_mf ~debug:debug env v mf in
      if b then eval ~debug:debug env' f
      else eval_next ~debug:debug env v ms
    | [] -> raise @@ Eval_bug "Didn't match"
  and cast ?(debug=false) v u1 u2 (r, p) =
    let print_debug f = Utils.Format.make_print_debug debug f in
    print_debug "cast <-- %a: %a => %a@." Pp.CC.pp_value v Pp.pp_ty u1 Pp.pp_ty u2;
    let cast = cast ~debug:debug in
    match u1, u2 with
    (* When type variables are instantiated *)
    | TyVar (_, { contents = Some u1 }), u2
    | u1, TyVar (_, { contents = Some u2 }) ->
      cast v u1 u2 (r, p)
    (* IdBase *)
    | TyBool, TyBool
    | TyInt, TyInt
    | TyUnit, TyUnit -> v
    (* IdStar *)
    | TyDyn, TyDyn -> v
    (* Succeed / Fail *)
    | TyDyn, (TyBool | TyInt | TyUnit | TyFun (TyDyn, TyDyn) | TyList TyDyn as u2) -> begin
        match v, u2 with
        | Tagged (B, v), TyBool -> v
        | Tagged (I, v), TyInt -> v
        | Tagged (U, v), TyUnit -> v
        | Tagged (Ar, v), TyFun (TyDyn, TyDyn) -> v
        | Tagged (Li, v), TyList TyDyn -> v
        | Tagged _, _ -> raise @@ Blame (r, p)
        | _ -> raise @@ Eval_bug "untagged value"
      end
    | TyDyn, TyTuple us when us = make_dyn_list (List.length us) ->
      begin match v with
      | Tagged (Tp n, v) when n = List.length us -> v
      | Tagged _ -> raise @@ Blame (r, p)
      | _ -> raise @@ Eval_bug "untagged value"
      end
    (* AppCast *)
    | TyFun (u11, u12), TyFun (u21, u22) -> 
      if u11 = u21 && u12 = u22 then v 
      else begin match v with
      | FunBV proc ->
        FunBV (
          fun (xs, ys) x ->
            let subst = subst_type @@ Utils.List.zip xs ys in
            let arg = cast x (subst u21) (subst u11) (r, neg p) in
            let res = proc (xs, ys) arg in
            cast res (subst u12) (subst u22) (r, p)
        )
      | _ -> raise @@ Eval_bug "non procedural value"
      end
    | TyList u1, TyList u2 -> 
      if u1 = u2 then v 
      else begin match v with
      | NilV -> NilV
      | ConsV (h, t) -> ConsV (cast h u1 u2 (r, p), cast t (TyList u1) (TyList u2) (r, p))
      | _ -> raise @@ Eval_bug "non list value"
      end
    | TyTuple us1, TyTuple us2 ->
      if us1 = us2 then v
      else begin match v with
      | TupleV vs ->
        let rec cast_list vs us1 us2 res = match vs, us1, us2 with
        | v :: vs, u1 :: us1, u2 :: us2 -> cast_list vs us1 us2 ((cast v u1 u2 (r, p)) :: res)
        | [], [], [] -> TupleV (List.rev res)
        | _ -> raise @@ Eval_bug "tuple length is wrong"
        in 
        cast_list vs us1 us2 []
      | _ -> raise @@ Eval_bug "non tuple value"
      end
    (* Tagged *)
    | TyBool, TyDyn -> Tagged (B, v)
    | TyInt, TyDyn -> Tagged (I, v)
    | TyUnit, TyDyn -> Tagged (U, v)
    | TyFun (TyDyn, TyDyn), TyDyn -> Tagged (Ar, v)
    | TyList TyDyn, TyDyn -> Tagged (Li, v)
    | TyTuple us, TyDyn when us = make_dyn_list (List.length us) -> Tagged (Tp (List.length us), v)
    (* Ground *)
    | TyFun _, TyDyn ->
      let dfun = TyFun (TyDyn, TyDyn) in
      let v = cast v u1 dfun (r, p) in
      cast v dfun TyDyn (r, p)
    | TyList _, TyDyn ->
      let dlist = TyList TyDyn in
      let v = cast v u1 dlist (r, p) in
      cast v dlist TyDyn (r, p)
    | TyTuple us, TyDyn ->
      let dtuple = TyTuple (make_dyn_list (List.length us)) in
      let v = cast v u1 dtuple (r, p) in
      cast v dtuple TyDyn (r, p)
    (* Expand *)
    | TyDyn, TyFun _ ->
      let dfun = TyFun (TyDyn, TyDyn) in
      let v = cast v TyDyn dfun (r, p) in
      cast v dfun u2 (r, p)
    | TyDyn, TyList _ ->
      let dlist = TyList TyDyn in
      let v = cast v TyDyn dlist (r, p) in
      cast v dlist u2 (r, p)
    | TyDyn, TyTuple us ->
      let dtuple = TyTuple (make_dyn_list (List.length us)) in
      let v = cast v TyDyn dtuple (r, p) in
      cast v dtuple u2 (r, p)
    (* InstBase / InstArrow *)
    | TyDyn, (TyVar (_, ({ contents = None } as x)) as x') -> begin
        match v with
        | Tagged (B | I | U as t, v) ->
          let u = type_of_tag t in
          print_debug "DTI: %a is instantiated to %a@."
            Pp.pp_ty x'
            Pp.pp_ty u;
          x := Some u;
          v
        | Tagged (Ar, v) ->
          let u = TyFun (Typing.fresh_tyvar (), Typing.fresh_tyvar ()) in
          print_debug "DTI: %a is instantiated to %a@."
            Pp.pp_ty x'
            Pp.pp_ty u;
          x := Some u;
          cast v (TyFun (TyDyn, TyDyn)) u (r, p)
        | Tagged (Li, v) ->
          let u = TyList (Typing.fresh_tyvar ()) in
          print_debug "DTI: %a is instantiated to %a@."
            Pp.pp_ty x'
            Pp.pp_ty u;
          x := Some u;
          cast v (TyList TyDyn) u (r, p)
        | Tagged (Tp n, v) ->
          let dtuple_con = make_dyn_list n in
          let u = TyTuple (List.map (fun _ -> fresh_tyvar ()) dtuple_con) in
          print_debug "DTI: %a is instantiated to %a@."
            Pp.pp_ty x'
            Pp.pp_ty u;
          x := Some u;
          cast v (TyTuple dtuple_con) u (r, p)
        | _ -> raise @@ Eval_bug "cannot instantiate"
      end
    | _ -> raise @@ Eval_bug (asprintf "cannot cast value: %a" Pp.CC.pp_value v)
  and coerce ?(debug=false) v c =
    let print_debug f = Utils.Format.make_print_debug debug f in
    print_debug "coerce <-- %a<%a>@." Pp.CC.pp_value v Pp.pp_coercion c;
    let coerce = coerce ~debug:debug in
    match v with
    | CoerceV (v, c') -> coerce v (compose c' c ~debug:debug)
    | v -> match normalize_coercion c with
      | CId _ -> v
      | CFail (_, (r, p), _) -> raise @@ Blame (r, p)
      | c when is_d c -> CoerceV (v, c)
      | _ -> raise @@ Eval_bug (asprintf "cannot coercion value: %a <%a>" Pp.CC.pp_value v Pp.pp_coercion c)
  and eval_app_valD ?(debug=false) env v1 v2 v3 = match v1 with (*値まで評価しきっているので，論文のようなlet k = t;;c in ~~とはできない*)
    | FunSV proc -> proc ([], []) (v2, v3) 
    | FunAV proc -> 
      begin match v3 with
      | CoercionV (CId _) -> fst (proc ([], [])) v2
      | _ -> snd (proc ([], [])) (v2, v3)
      end
    | CoerceV (v1, CFun (s, t)) -> 
      begin match v3 with
        | CoercionV c -> 
          let k = CoercionV (compose t c ~debug:debug) in
          eval_app_valD env v1 (coerce v2 s ~debug:debug) k ~debug:debug
        | _ -> raise @@ Eval_bug "app: application of non coercion value"
      end
    | _ -> raise @@ Eval_bug (asprintf "app_valD: application of non procedure value: %a" Pp.CC.pp_value v1)
  and eval_app_valM ?(debug=false) env v1 v2 = match v1 with (*値まで評価しきっているので，論文のようなlet k = t;;c in ~~とはできない*)
    | FunBV proc -> proc ([], []) v2
    | FunAV proc -> fst (proc ([], [])) v2
    | CoerceV (v1, CFun (s, t)) -> eval_app_valD env v1 (coerce v2 s ~debug:debug) (CoercionV t) ~debug:debug
    | _ -> raise @@ Eval_bug (asprintf "app_valM: application of non procedure value: %a" Pp.CC.pp_value v1)

  let eval_program ?(debug=false) env p =
    match p with
    | Exp f ->
      let v = eval env f ~debug:debug in
      env, "-", v
    | LetDecl (x, xs, f) ->
      let v = eval env f ~debug:debug in
      let env = Environment.add x (xs, v) env in
      env, x, v
end

module KNorm = struct
  open Syntax.KNorm

  let rec subst_exp s = 
    let subst_type_k s = function
      | Ty u -> Ty (subst_type s u)
      | TyNu -> TyNu
    in function
    | Var _ | IConst _ | Nil as f -> f
    | Add _ | Sub _ | Mul _ | Div _ | Mod _ | Cons _ | Tuple _ | Hd _ | Tl _ | Tget _ as f -> f
    | IfEqExp (x, y, f1, f2) -> IfEqExp (x, y, subst_exp s f1, subst_exp s f2)
    | IfLteExp (x, y, f1, f2) -> IfLteExp (x, y, subst_exp s f1, subst_exp s f2)
    | MatchExp (x, ms) -> MatchExp (x, List.map (fun (mf, f) -> subst_mf s mf, subst_exp s f) ms)
    | AppDExp _ | AppMExp _ | CAppExp _ | CSeqExp _ as f -> f
    | AppTy (x, tvs, tas) -> AppTy (x, tvs, List.map (subst_type_k s) tas)
    | CastExp (x, u1, u2, r_p) -> CastExp (x, subst_type s u1, subst_type s u2, r_p)
    | CoercionExp c -> CoercionExp (subst_coercion s c)
    | LetExp (x, f1, f2) ->
      LetExp (x, subst_exp s f1, subst_exp s f2)
    | LetRecSExp (x, tvs, arg, f1, f2) ->
      LetRecSExp (x, tvs, arg, subst_exp s f1, subst_exp s f2)
    | LetRecAExp (x, tvs, arg, (f1, f1'), f2) ->
      LetRecAExp (x, tvs, arg, (subst_exp s f1, subst_exp s f1'), subst_exp s f2)
    | LetRecBExp (x, tvs, arg, f1, f2) ->
      LetRecBExp (x, tvs, arg, subst_exp s f1, subst_exp s f2)

  let rec eval_exp ?(debug=false) kenv f = 
    if debug then fprintf err_formatter "keval <-- %a@." Pp.KNorm.pp_exp f;
    let eval_exp = eval_exp ~debug:debug in
    match f with
    | Var x -> 
      Environment.find x kenv
    | IConst i -> IntV i
    | Nil -> NilV
    | Add (x1, x2) ->
      let v1 = Environment.find x1 kenv in
      let v2 = Environment.find x2 kenv in
      begin match v1, v2 with
        | IntV i1, IntV i2 -> IntV (i1 + i2)
        | _ -> raise @@ Eval_bug "Add: unexpected type of argument"
      end
    | Sub (x1, x2) ->
      let v1 = Environment.find x1 kenv in
      let v2 = Environment.find x2 kenv in
      begin match v1, v2 with
        | IntV i1, IntV i2 -> IntV (i1 - i2)
        | _ -> raise @@ Eval_bug "Sub: unexpected type of argument"
      end
    | Mul (x1, x2) ->
      let v1 = Environment.find x1 kenv in
      let v2 = Environment.find x2 kenv in
      begin match v1, v2 with
        | IntV i1, IntV i2 -> IntV (i1 * i2)
        | _ -> raise @@ Eval_bug "Mul: unexpected type of argument"
      end
    | Div (x1, x2) ->
      let v1 = Environment.find x1 kenv in
      let v2 = Environment.find x2 kenv in
      begin match v1, v2 with
        | IntV i1, IntV i2 -> IntV (i1 / i2)
        | _ -> raise @@ Eval_bug "Div: unexpected type of argument"
      end
    | Mod (x1, x2) ->
      let v1 = Environment.find x1 kenv in
      let v2 = Environment.find x2 kenv in
      begin match v1, v2 with
        | IntV i1, IntV i2 -> IntV (i1 mod i2)
        | _ -> raise @@ Eval_bug "Mod: unexpected type of argument"
      end
    | Cons (x1, x2) ->
      let v1 = Environment.find x1 kenv in
      let v2 = Environment.find x2 kenv in
      ConsV (v1, v2)
    | Tuple xs ->
      TupleV (List.map (fun x -> Environment.find x kenv) xs)
    | Hd x ->
      let v = Environment.find x kenv in
      begin match v with
      | ConsV (v1, _) -> v1
      | CoerceV (ConsV (v1, _), CList s) -> coerce ~debug:debug v1 s
      | _ -> raise @@ Eval_bug "hd: not list value"
      end
    | Tl x ->
      let v = Environment.find x kenv in
      begin match v with
      | ConsV (_, v2) -> v2
      | CoerceV (ConsV (_, v2), s) -> coerce ~debug:debug v2 s
      | _ -> raise @@ Eval_bug "tl: not list value"
      end
    | Tget (x, i) ->
      let v = Environment.find x kenv in
      begin match v with
      | TupleV vs -> List.nth vs i
      | CoerceV (TupleV vs, CTuple ss) -> coerce ~debug:debug (List.nth vs i) (List.nth ss i)
      | _ -> raise @@ Eval_bug "tget: not tuple value"
      end 
    | IfEqExp (x1, x2, f1, f2) ->
      let v1 = Environment.find x1 kenv in
      let v2 = Environment.find x2 kenv in
      begin match v1, v2 with
        | IntV i1, IntV i2 -> if i1 = i2 then eval_exp kenv f1 else eval_exp kenv f2
        | _ -> raise @@ Eval_bug "IfEqExp: not int value"
      end
    | IfLteExp (x1, x2, f1, f2) ->
      let v1 = Environment.find x1 kenv in
      let v2 = Environment.find x2 kenv in
      begin match v1, v2 with
        | IntV i1, IntV i2 -> if i1 <= i2 then eval_exp kenv f1 else eval_exp kenv f2
        | _ -> raise @@ Eval_bug "IfLteExp: not int value"
      end
    | MatchExp (x, ms) ->
      let v = Environment.find x kenv in
      eval_next ~debug:debug kenv v ms
    | AppMExp (x, y) -> 
      let v1 = Environment.find x kenv in
      let v2 = Environment.find y kenv in
      eval_app_valM kenv v1 v2 ~debug:debug
    | AppDExp (x1, (x2, x3)) -> 
      let v1 = Environment.find x1 kenv in
      let v2 = Environment.find x2 kenv in
      let v3 = Environment.find x3 kenv in
      eval_app_valD kenv v1 v2 v3 ~debug:debug
    | CAppExp (x1, x2) ->
      let v1 = Environment.find x1 kenv in
      let v2 = Environment.find x2 kenv in
      begin match v2 with
      | CoercionV c -> coerce ~debug:debug v1 c
      | _ -> raise @@ Eval_bug "capp: application of non coercion value"
      end
    | CSeqExp (x1, x2) -> 
      let v1 = Environment.find x1 kenv in
      let v2 = Environment.find x2 kenv in
      begin match v1, v2 with
        | CoercionV c1, CoercionV c2 -> CoercionV (compose c1 c2 ~debug:debug)
        | _ -> raise @@ Eval_bug "cseq: sequence of non coercion value"
      end
    | AppTy (x, tvs, tas) ->
      let v1 = Environment.find x kenv in
      let us = List.map nu_to_fresh tas in
      begin match v1 with
        | FunSV proc -> FunSV (fun _ -> proc (tvs, us))
        | FunAV proc -> FunAV (fun _ -> proc (tvs, us))
        | FunBV proc -> FunBV (fun _ -> proc (tvs, us))
        | _ -> raise @@ Eval_bug "AppTy: not fun value"
      end
    | CastExp (x, u1, u2, r_p) ->
      let v = Environment.find x kenv in
      cast ~debug:debug v u1 u2 r_p
    | CoercionExp c -> CoercionV c
    | LetExp (x, f1, f2) -> 
      let v1 = eval_exp kenv f1 in
      eval_exp (Environment.add x v1 kenv) f2
    | LetRecSExp (x, _, (y, k), f1, f2) -> 
      let v1 = 
        FunSV (
          fun (tvs, us) -> fun (v1, v2) ->
          let f1 = subst_exp (Utils.List.zip tvs us) f1 in
          let rec f _ (v1, v2) =
            let kenv = Environment.add x (FunSV f) kenv in
            let kenv = Environment.add y v1 kenv in
            let kenv = Environment.add k v2 kenv in
            eval_exp kenv f1
          in f ([], []) (v1, v2)
        )
      in eval_exp (Environment.add x v1 kenv) f2
    | LetRecAExp (x, _, (y, k), (f1, f1'), f2) -> 
      let v1 = 
        FunAV (
          fun (xs, ys) -> 
          let f1 = subst_exp (Utils.List.zip xs ys) f1 in
          let f1' = subst_exp (Utils.List.zip xs ys) f1' in
          let rec f1_ v =
            let kenv = Environment.add x (FunAV (fun _ -> (f1_, f1'_))) kenv in
            let kenv = Environment.add y v kenv in
            eval_exp kenv f1
          and f1'_ (v, w) =
            let kenv = Environment.add x (FunAV (fun _ -> (f1_, f1'_))) kenv in
            let kenv = Environment.add y v kenv in
            let kenv = Environment.add k w kenv in
            eval_exp kenv f1'
          in (f1_, f1'_)
        )
      in eval_exp (Environment.add x v1 kenv) f2
    | LetRecBExp (x, _, y, f1, f2) ->
      let v1 = 
        FunBV (
          fun (tvs, us) -> fun v ->
          let f1 = subst_exp (Utils.List.zip tvs us) f1 in
          let rec f _ v =
            let kenv = Environment.add x (FunBV f) kenv in
            let kenv = Environment.add y v kenv in
            eval_exp kenv f1
          in f ([], []) v
        )
      in eval_exp (Environment.add x v1 kenv) f2
  and cast ?(debug=false) v u1 u2 (r, p) = 
    let print_debug f = Utils.Format.make_print_debug debug f in
    print_debug "cast <-- %a: %a => %a@." Pp.KNorm.pp_value v Pp.pp_ty u1 Pp.pp_ty u2;
    let cast = cast ~debug:debug in
    match u1, u2 with
    (* When tyvars are instantiated *)
    | TyVar (_, {contents = Some u1}), u2 | u1, TyVar (_, {contents = Some u2}) ->
      cast v u1 u2 (r, p)
    (* IdBase: iota => iota ... ok*)
    | TyBool, TyBool | TyInt, TyInt | TyUnit, TyUnit -> v
    (* IdStar: ? => ? ... ok*)
    | TyDyn, TyDyn -> v
    (* Succeed / Fail: ? => U *)
    | TyDyn, (TyBool | TyInt | TyUnit | TyFun (TyDyn, TyDyn) | TyList TyDyn as u2) -> 
      begin match v, u2 with
        | Tagged (B, v), TyBool -> v (* bool => ? => bool ... ok *)
        | Tagged (I, v), TyInt -> v (* int => ? => int ... ok *)
        | Tagged (U, v), TyUnit -> v (* unit => ? => unit ... ok *)
        | Tagged (Ar, v), TyFun (TyDyn, TyDyn) -> v (* ?->? => ? => ?->? ... ok *)
        | Tagged (Li, v), TyList TyDyn -> v
        | Tagged _, _ -> raise @@ Blame (r, p)
        | _ -> raise @@ Eval_bug "untagged value"
      end
    | TyDyn, TyTuple us when us = make_dyn_list (List.length us) ->
      begin match v with
      | Tagged (Tp n, v) when n = List.length us -> v
      | Tagged _ -> raise @@ Blame (r, p)
      | _ -> raise @@ Eval_bug "untagged value"
      end
    (* AppCast *)
    | TyFun (u11, u12), TyFun (u21, u22) ->
      begin match v with
        | FunBV proc -> 
          FunBV (
            fun (tvs, ts) -> fun x ->
              let subst = subst_type @@ Utils.List.zip tvs ts in
              let arg = cast x (subst u21) (subst u11) (r, (neg p)) in
              let res = proc (tvs, ts) arg in
              cast res (subst u12) (subst u22) (r, p)
          )
        | _ -> raise @@ Eval_bug "non procedual value"
      end
    | TyList u1, TyList u2 -> 
      if u1 = u2 then v 
      else begin match v with
      | NilV -> NilV
      | ConsV (h, t) -> ConsV (cast h u1 u2 (r, p), cast t (TyList u1) (TyList u2) (r, p))
      | _ -> raise @@ Eval_bug "non list value"
      end
    | TyTuple us1, TyTuple us2 ->
      if us1 = us2 then v
      else begin match v with
      | TupleV vs ->
        let rec cast_list vs us1 us2 res = match vs, us1, us2 with
        | v :: vs, u1 :: us1, u2 :: us2 -> cast_list vs us1 us2 ((cast v u1 u2 (r, p)) :: res)
        | [], [], [] -> TupleV (List.rev res)
        | _ -> raise @@ Eval_bug "tuple length is wrong"
        in 
        cast_list vs us1 us2 []
      | _ -> raise @@ Eval_bug "non tuple value"
      end
    (* Tagged *)
    | TyBool, TyDyn -> Tagged (B, v)
    | TyInt, TyDyn -> Tagged (I, v)
    | TyUnit, TyDyn -> Tagged (U, v)
    | TyFun (TyDyn, TyDyn), TyDyn -> Tagged (Ar, v)
    | TyList TyDyn, TyDyn -> Tagged (Li, v)
    | TyTuple us, TyDyn when us = make_dyn_list (List.length us) -> Tagged (Tp (List.length us), v)
    (* Ground *)
    | (TyFun _ as u1), (TyDyn as u2) ->
      let dfun = TyFun (TyDyn, TyDyn) in
      let v = cast v u1 dfun (r, p) in
      cast v dfun u2 (r, p)
    | TyList _, TyDyn ->
      let dlist = TyList TyDyn in
      let v = cast v u1 dlist (r, p) in
      cast v dlist TyDyn (r, p)
    | TyTuple us, TyDyn ->
      let dtuple = TyTuple (make_dyn_list (List.length us)) in
      let v = cast v u1 dtuple (r, p) in
      cast v dtuple TyDyn (r, p)
    (* Expand *)
    | TyDyn, TyFun _ ->
      let dfun = TyFun (TyDyn, TyDyn) in
      let v = cast v u1 dfun (r, p) in 
      cast v dfun u2 (r, p)
    | TyDyn, TyList _ ->
      let dlist = TyList TyDyn in
      let v = cast v TyDyn dlist (r, p) in
      cast v dlist u2 (r, p)
    | TyDyn, TyTuple us ->
      let dtuple = TyTuple (make_dyn_list (List.length us)) in
      let v = cast v TyDyn dtuple (r, p) in
      cast v dtuple u2 (r, p)
    (* InstBase / InstArrow *)
    | TyDyn, (TyVar (_, ({contents = None} as x)) as u') ->
      begin match v with
        | Tagged ((B | I | U as t), v) ->
          let u = type_of_tag t in
          print_debug "DTI: %a is instantiated to %a@."
            Pp.pp_ty u'
            Pp.pp_ty u;
          x := Some u;
          v
        | Tagged (Ar, v) -> 
          let u = TyFun (Typing.fresh_tyvar (), Typing.fresh_tyvar ()) in
          print_debug "DTI: %a is instantiated to %a@."
            Pp.pp_ty u'
            Pp.pp_ty u;
          x := Some u;
          cast v (TyFun (TyDyn, TyDyn)) u (r, p)
        | Tagged (Li, v) ->
          let u = TyList (Typing.fresh_tyvar ()) in
          print_debug "DTI: %a is instantiated to %a@."
            Pp.pp_ty u'
            Pp.pp_ty u;
          x := Some u;
          cast v (TyList TyDyn) u (r, p)
        | Tagged (Tp n, v) ->
          let dtuple_con = make_dyn_list n in
          let u = TyTuple (List.map (fun _ -> fresh_tyvar ()) dtuple_con) in
          print_debug "DTI: %a is instantiated to %a@."
            Pp.pp_ty u'
            Pp.pp_ty u;
          x := Some u;
          cast v (TyTuple dtuple_con) u (r, p)
        | _ -> raise @@ Eval_bug "cannot instamtiate"
      end
    | _ -> raise @@ Eval_bug (asprintf "cannot cast value: %a: %a => %a" Pp.KNorm.pp_value v Pp.pp_ty u1 Pp.pp_ty u2)
  and coerce ?(debug=false) v c =
    let print_debug f = Utils.Format.make_print_debug debug f in
    print_debug "coerce <-- %a<%a>@." Pp.KNorm.pp_value v Pp.pp_coercion c;
    let coerce = coerce ~debug:debug in
    match v with
    | CoerceV (v, c') -> coerce v (compose c' c ~debug:debug)
    | v -> match normalize_coercion c with
      | CId _ -> v
      | CFail (_, (r, p), _) -> raise @@ Blame (r, p)
      | c when is_d c -> CoerceV (v, (*Typing.ITGL.normalize_coercion*) c)
      | _ -> raise @@ Eval_bug (asprintf "cannot coercion value: %a" Pp.KNorm.pp_value v)
  and match_mf ?(debug=false) kenv v mf = match v, mf with
    (* | _, MatchVar (id, _) ->
      let kenv = Environment.add id v kenv in
      true, kenv *)
    | ConsV (v1, v2), MatchCons (mf1, mf2) ->
      let b1, kenv = match_mf ~debug:debug kenv v1 mf1 in
      let b2, kenv = match_mf ~debug:debug kenv v2 mf2 in
      b1&&b2, kenv 
    | NilV, MatchNil _ -> true, kenv
    | IntV i1, MatchILit i2 -> if i1 = i2 then (true, kenv) else (false, kenv)
    | TupleV vs, MatchTuple mfs ->
      let rec iter kenv vs mfs b = match vs, mfs with
      | v :: vs, mf :: mfs ->
        let b', kenv = match_mf ~debug:debug kenv v mf in
        iter kenv vs mfs (b && b')
      | _ :: _, [] | [], _ :: _ -> false, kenv
      | [], [] -> b, kenv
      in
      iter kenv vs mfs true
    (* | IntV i, MatchBLit b -> if i = 1 && b then (true, kenv) else if i = 0 && not b then (false, kenv) else raise @@ Eval_bug "MatchBLit didn't match"
    | IntV 0, MatchULit -> true, kenv *)
    (* | arg, MatchAsc (mf, _) -> match_mf env arg mf *)
    | _, MatchWild _ -> true, kenv
    | CoerceV (ConsV (v1, v2), CList s), MatchCons _ -> 
      match_mf ~debug:debug kenv (ConsV (coerce ~debug:debug v1 s, coerce ~debug:debug v2 (CList s))) mf (* lazy *)
    | _, (MatchVar _ | MatchBLit _ | MatchULit) -> raise @@ Eval_bug "MatchVar, MatchBLit, MatchULit  does not appear in KNormal form"
    | _ -> false, kenv 
  and eval_next ?(debug=false) kenv v ms = match ms with
    | (mf, f) :: ms ->
      let b, kenv' = match_mf ~debug:debug kenv v mf in
      if b then eval_exp ~debug:debug kenv' f
      else eval_next ~debug:debug kenv v ms
    | [] -> raise @@ Eval_bug "Didn't match"
  and eval_app_valD ?(debug=false) kenv v1 v2 v3 = match v1 with
    | FunSV proc -> proc ([], []) (v2, v3)
    | FunAV proc -> 
      begin match v3 with
      | CoercionV (CId _) -> fst (proc ([], [])) v2
      | _ -> snd (proc ([], [])) (v2, v3)
      end
    | CoerceV (v1, CFun (s, t)) -> 
      begin match v3 with
        | CoercionV c -> 
          let k = CoercionV (compose t c ~debug:debug) in
          eval_app_valD kenv v1 (coerce v2 s ~debug:debug) k
        | _ -> raise @@ Eval_bug "app: application of non coercion value"
      end
    | _ -> raise @@ Eval_bug "app_valD: application of non procedure value"
  and eval_app_valM ?(debug=false) env v1 v2 = match v1 with (*値まで評価しきっているので，論文のようなlet k = t;;c in ~~とはできない*)
    | FunAV proc -> fst (proc ([], [])) v2
    | FunBV proc -> proc ([], []) v2
    | CoerceV (v1, CFun (s, t)) -> eval_app_valD env v1 (coerce v2 s ~debug:debug) (CoercionV t) ~debug:debug
    | _ -> raise @@ Eval_bug "app_valM: application of non procedure value"

  let eval_program ?(debug=false) kenv = function
    | Exp f -> let v = eval_exp kenv f ~debug:debug in kenv, "-", v
    | LetDecl (x, f) ->
      let v = eval_exp kenv f ~debug:debug in
      let kenv = Environment.add x v kenv in
      kenv, x, v
    | LetRecSDecl (x, _, (y, k), f') -> 
      let v = 
        FunSV (
          fun (tvs, us) -> fun (v1, v2) ->
          let f' = subst_exp (Utils.List.zip tvs us) f' in
          let rec f _ (v1, v2) =
            let kenv = Environment.add x (FunSV f) kenv in
            let kenv = Environment.add y v1 kenv in
            let kenv = Environment.add k v2 kenv in
            eval_exp kenv f'
          in f ([], []) (v1, v2)
        )
      in let kenv = Environment.add x v kenv in
      kenv, x, v
    | LetRecADecl (x, _, (y, k), (f1, f1')) -> 
      let v = 
        FunAV (
          fun (xs, ys) -> 
          let f1 = subst_exp (Utils.List.zip xs ys) f1 in
          let f1' = subst_exp (Utils.List.zip xs ys) f1' in
          let rec f1_ v =
            let kenv = Environment.add x (FunAV (fun _ -> (f1_, f1'_))) kenv in
            let kenv = Environment.add y v kenv in
            eval_exp kenv f1
          and f1'_ (v, w) =
            let kenv = Environment.add x (FunAV (fun _ -> (f1_, f1'_))) kenv in
            let kenv = Environment.add y v kenv in
            let kenv = Environment.add k w kenv in
            eval_exp kenv f1'
          in (f1_, f1'_)
        )
      in let kenv = Environment.add x v kenv in
      kenv, x, v
    | LetRecBDecl (x, _, y, f') -> 
      let v = 
        FunBV (
          fun (tvs, us) -> fun v ->
          let f' = subst_exp (Utils.List.zip tvs us) f' in
          let rec f _ v =
            let kenv = Environment.add x (FunBV f) kenv in
            let kenv = Environment.add y v kenv in
            eval_exp kenv f'
          in f ([], []) v
        )
      in let kenv = Environment.add x v kenv in
      kenv, x, v
end