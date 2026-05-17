open Pp
open Syntax
open Format

exception Translation_bug of string

(* let type_of_tag = Typing.type_of_tag *)

let tag_of_ty = Typing.tag_of_ty

(* These functions (dom, cod, meet) only can be used for normalized types *)
let dom = function
  | TyVar (_, { contents = Some _ }) ->
    raise @@ Translation_bug "dom: instantiated tyvar is given"
  | TyFun (u1, _) -> u1
  | TyDyn -> TyDyn
  | _ as u ->
    raise @@ Translation_bug (asprintf "failed to match: dom(%a)" pp_ty u)

let cod = function
  | TyVar (_, { contents = Some _ }) ->
    raise @@ Translation_bug "cod: instantiated tyvar is given"
  | TyFun (_, u2) -> u2
  | TyDyn -> TyDyn
  | _ as u ->
    raise @@ Translation_bug (asprintf "failed to match: cod(%a)" pp_ty u)

let rec meet u1 u2 = match u1, u2 with
  | TyVar (_, { contents = Some _ }), _
  | _, TyVar (_, { contents = Some _ }) ->
    raise @@ Translation_bug "meet: instantiated tyvar is given"
  | TyBool, TyBool -> TyBool
  | TyInt, TyInt -> TyInt
  | TyUnit, TyUnit -> TyUnit
  | TyVar (a1, _ as tv), TyVar (a2, _) when a1 = a2 -> TyVar tv
  | TyDyn, u | u, TyDyn -> u
  | TyFun (u11, u12), TyFun (u21, u22) -> TyFun (meet u11 u21, meet u12 u22)
  | TyList u1, TyList u2 -> TyList (meet u1 u2)
  | TyTuple us1, TyTuple us2 -> TyTuple (List.map2 (fun u1 u2 -> meet u1 u2) us1 us2)
  | _ ->
    raise @@ Translation_bug (asprintf "failed to match: meet(%a, %a)" pp_ty u1 pp_ty u2)

let elm = function
  | TyVar (_, { contents = Some _ }) ->
    raise @@ Translation_bug "elm: instantiated tyvar is given"
  | TyList u -> u
  | TyDyn -> TyDyn
  | _ as u -> raise @@ Translation_bug (asprintf "failed to match: elm(%a)" pp_ty u)

module ITGL = struct
  open Syntax.ITGL

  let closure_tyvars_let_decl1 e u1 env =
    TV.elements @@ TV.diff (TV.union (tv_exp e) (ftv_ty u1)) (ftv_tyenv env)

  let closure_tyvars2 w1 env u1 v1 =
    let ftvs = TV.big_union [ftv_tyenv env; ftv_ty u1; ftv_exp v1] in
    TV.elements @@ TV.diff (Syntax.CC.ftv_exp w1) ftvs
  
  let closure_tyvars_let_decl2 w1 env u1 v1 =
    let ftvs = TV.big_union [ftv_tyenv env; ftv_ty u1; tv_exp v1] in
    TV.elements @@ TV.diff (Syntax.CC.ftv_exp w1) ftvs

  (* Cast insertion translation *)
  let rec make_s_coercion (r, p) u1 u2 = match u1, u2 with
    | i1, i2 when is_base_type i1 && is_base_type i2 && i1 = i2 -> CId i1
    | TyVar (i1, {contents = None}) as t, TyVar (i2, {contents = None}) when i1 = i2 -> CId t
    | TyFun (u11, u12), TyFun (u21, u22) -> 
      let s1 = make_s_coercion (r, neg p) u21 u11 in
      let s2 = make_s_coercion (r, p) u12 u22 in
      begin match s1, s2 with
      | CId u1, CId u2 -> CId (TyFun (u1, u2))
      | _ -> CFun (s1, s2)
      end
    | TyList u1, TyList u2 -> 
      let s = make_s_coercion (r, p) u1 u2 in
      begin match s with 
      | CId u -> CId (TyList u)
      | _ -> CList s
      end
    | TyTuple us1, TyTuple us2 ->
      let ss = List.map2 (fun u1 u2 -> make_s_coercion (r, p) u1 u2) us1 us2 in
      let rec check_id l r = match l with
      | CId u :: t -> check_id t (u :: r)
      | _ :: _ -> (false, r) (* r is dummy *)
      | [] -> (true, List.rev r)
      in
      let (is_id, id_u) = check_id ss [] in
      if is_id then CId (TyTuple id_u)
      else CTuple ss
    | TyDyn, TyDyn -> CId TyDyn
    | g, TyDyn when is_ground g -> CSeq (CId g, CInj (tag_of_ty g))
    | TyFun _ as u, TyDyn -> CSeq (make_s_coercion (r, p) u (TyFun (TyDyn, TyDyn)), CInj Ar)
    | TyList _ as u, TyDyn -> CSeq (make_s_coercion (r, p) u (TyList TyDyn), CInj Li)
    | TyTuple us as u, TyDyn ->
      let n = List.length us in
      CSeq (make_s_coercion (r, p) u (TyTuple (make_dyn_list n)), CInj (Tp n))
    | TyVar tv, TyDyn -> CTvInj (tv, (r, p))
    | TyDyn, g when is_ground g -> CSeq (CProj (tag_of_ty g, (r, p)), CId g)
    | TyDyn, (TyFun _ as u) -> CSeq (CProj (Ar, (r, p)), make_s_coercion (r, p) (TyFun (TyDyn, TyDyn)) u)
    | TyDyn, (TyList _ as u) -> CSeq (CProj (Li, (r, p)), make_s_coercion (r, p) (TyList TyDyn) u)
    | TyDyn, (TyTuple us as u) ->
      let n = List.length us in
      CSeq (CProj (Tp n, (r, p)), make_s_coercion (r, p) (TyTuple (make_dyn_list n)) u)
    | TyDyn, TyVar tv -> CTvProj (tv, (r, p))
    | _ -> raise @@ Translation_bug (Format.asprintf "cannot exist such coercion: %a and %a in %a" Pp.pp_ty u1 Pp.pp_ty u2 Utils.Error.pp_range r)

  let cast f r u1 u2 =
    if u1 = u2 then f  (* Omit identity cast for better performance *)
    else CC.CastExp (f, u1, u2, (r, Pos))

  let coerce f r u1 u2 = (* this is not same as ldti about blame label r *)
    if u1 = u2 then f (* Omit identity coercion for better performance *)
    else CC.CAppExp (f, CC.CoercionExp (make_s_coercion (r, Pos) u1 u2))
  
  let rec translate_mf env mf = match mf with 
    | MatchILit _ -> env, mf, TyInt
    | MatchBLit _ -> env, mf, TyBool
    | MatchULit -> env, mf, TyUnit
    | MatchWild u -> env, mf, u
    | MatchNil u -> env, mf, TyList u
    | MatchVar (x, u) as mf -> Environment.add x (tysc_of_ty u) env, mf, u
    | MatchCons (mf1, mf2) -> 
      let env, mf2, u2 = translate_mf env mf2 in
      let env, mf1, u1 = translate_mf env mf1 in
      env, MatchCons (mf1, mf2), meet (TyList u1) u2
    | MatchTuple mfs ->
      let rec iter env l r = match l with
      | h :: t ->
        let env, mf, u = translate_mf env h in
        iter env t ((mf, u) :: r)
      | [] -> 
        let mfs, us = List.split (List.rev r) in
        env, MatchTuple mfs, TyTuple us
      in
      iter env mfs []

  let rec translate_exp ~intoB env f = 
    let translate_exp = translate_exp ~intoB in
    let c = if intoB then cast else coerce in 
    match f with
    | Var (_, x, ys) ->
      begin try
        let TyScheme (xs, u) = Environment.find x env in
        let ftvs = ftv_ty u in
        let s = Utils.List.zip xs !ys in
        let ys = List.map (fun (x, u) -> if TV.mem x ftvs then Ty u else TyNu) s in
        let ys = ys @ Utils.List.repeat TyNu (List.length xs - List.length ys) in
        let u = Typing.subst_type (List.filter (fun (x, _) -> TV.mem x ftvs) s) u in
        CC.Var (x, ys), u
      with Not_found ->
        raise @@ Translation_bug "variable not found during cast-inserting translation"
      end
    | IConst (_, i) -> CC.IConst i, TyInt
    | BConst (_, b) -> CC.BConst b, TyBool
    | UConst _ -> CC.UConst, TyUnit
    | BinOp (_, op, e1, e2) ->
      let ui1, ui2, ui = Typing.type_of_binop op in
      let f1, u1 = translate_exp env e1 in
      let f2, u2 = translate_exp env e2 in
      let r1, r2 = range_of_exp e1, range_of_exp e2 in
      CC.BinOp (op, c f1 r1 u1 ui1, c f2 r2 u2 ui2), ui
    | AscExp (_, e, u1) ->
      let f, u = translate_exp env e in
      let r = range_of_exp e in
      if is_consistent u u1 then
        c f r u u1, u1
      else
        raise @@ Translation_bug "type ascription"
    | IfExp (_, e1, e2, e3) ->
      let f1, u1 = translate_exp env e1 in
      let f2, u2 = translate_exp env e2 in
      let f3, u3 = translate_exp env e3 in
      let r1, r2, r3 = range_of_exp e1, range_of_exp e2, range_of_exp e3 in
      let u = meet u2 u3 in
      CC.IfExp (c f1 r1 u1 TyBool, c f2 r2 u2 u, c f3 r3 u3 u), u
    | FunEExp (_, x, u1, e)
    | FunIExp (_, x, u1, e) ->
      let f, u2 = translate_exp (Environment.add x (tysc_of_ty u1) env) e in
      CC.FunBExp ((x, u1), f), TyFun (u1, u2)
    | FixEExp (_, x, y, u1, u2, e)
    | FixIExp (_, x, y, u1, u2, e) ->
      (* NOTE: Disallow to use x polymorphically in e *)
      let env = Environment.add x (tysc_of_ty (TyFun (u1, u2))) env in
      let env = Environment.add y (tysc_of_ty u1) env in
      let f, u2' = translate_exp env e in
      let r = range_of_exp e in
      CC.FixBExp ((x, y, u1, u2), c f r u2' u2), TyFun (u1, u2)
    | AppExp (_, e1, e2) ->
      let f1, u1 = translate_exp env e1 in
      let f2, u2 = translate_exp env e2 in
      let r1, r2 = range_of_exp e1, range_of_exp e2 in
      (* Format.fprintf std_formatter "u1: %a, u2: %a\n" Pp.pp_ty u1 Pp.pp_ty u2; *)
      CC.AppMExp (c f1 r1 u1 (TyFun (dom u1, cod u1)), c f2 r2 u2 (dom u1)), cod u1
    | MatchExp (r, e, ms) -> 
      let f, u = translate_exp env e in
      let msu, (u_match, u_exp) = translate_ms ~intoB env ms in
      CC.MatchExp (c f r u u_match, List.map (fun (mf, f, u) -> mf, c f r u u_exp) msu), u_exp
    | LetExp (_, x, e1, e2) when Typing.ITGL.is_value env e1 ->
      let f1, u1 = translate_exp env e1 in
      let xs = Typing.ITGL.closure_tyvars1 u1 env e1 in
      let ys = closure_tyvars2 f1 env u1 e1 in
      let xys = xs @ ys in
      let us1 = TyScheme (xys, u1) in
      let f2, u2 = translate_exp (Environment.add x us1 env) e2 in
      CC.LetExp (x, xys, f1, f2), u2
    | LetExp (_, x, e1, e2) ->
      let f1, u1 = translate_exp env e1 in
      let us1 = TyScheme ([], u1) in
      let f2, u2 = translate_exp (Environment.add x us1 env) e2 in
      CC.LetExp (x, [], f1, f2), u2
    | NilExp (_, u) -> CC.NilExp u, TyList u
    | ConsExp (r, e1, e2) ->
      let f1, u1 = translate_exp env e1 in
      let f2, u2 = translate_exp env e2 in
      let u_elm = meet u1 (elm u2) in (* TyDyn であれば TyList TyDyn にする *)
      let u_list = TyList u_elm in
      CC.ConsExp (c f1 r u1 u_elm, c f2 r u2 u_list), u_list
    | TupleExp (_, es) ->
      let fs, us = List.split (List.map (fun e -> translate_exp env e) es) in
      CC.TupleExp fs, TyTuple us
  and translate_ms ~intoB env = function
    | (mf, e) :: t -> 
      if t = [] then
        let env', mf, u_match = translate_mf env mf in
        let f, u_exp = translate_exp ~intoB env' e in
        [mf, f, u_exp], (u_match, u_exp)
      else 
        let env', mf, u_match = translate_mf env mf in
        let f, u_exp = translate_exp ~intoB env' e in
        let t, (u_match', u_exp') = translate_ms ~intoB env t in
        (mf, f, u_exp) :: t, (meet u_match u_match', meet u_exp u_exp')
    | [] -> raise @@ Translation_bug "translate_ms: empty match"

  let translate ~intoB env = function
    | Exp e ->
      let f, u = translate_exp ~intoB env e in
      env, CC.Exp f, u
    | LetDecl (x, e) ->
      let f, u = translate_exp ~intoB env e in
      let tvs = 
        if Typing.ITGL.is_value env e then
          let xs = closure_tyvars_let_decl1 e u env in
          let ys = closure_tyvars_let_decl2 f env u e in
          xs @ ys
        else 
          []
      in let env = Environment.add x (TyScheme (tvs, u)) env in
      env, CC.LetDecl (x, tvs, f), u
end

module CC = struct
  open Syntax.CC

  let fresh_CVar =
    let counter = ref 0 in
    let body () =
      let v = !counter in
      counter := v + 1;
      let id = "k"^string_of_int !counter in
      id, Var (id, [])
    in body

  let rec translate_mf env = function
    | MatchILit _ | MatchBLit _ | MatchULit | MatchWild _ | MatchNil _ as mf -> env, mf 
    | MatchVar (x, u) as mf -> 
      let env = Environment.add x (tysc_of_ty u) env in
      env, mf
    | MatchCons (mf1, mf2) -> 
      let env, mf1 = translate_mf env mf1 in
      let env, mf2 = translate_mf env mf2 in
      env, MatchCons (mf1, mf2)
    | MatchTuple mfs ->
      let rec iter env l r = match l with
      | h :: t ->
        let env, mf = translate_mf env h in
        iter env t (mf :: r)
      | [] -> 
        env, MatchTuple (List.rev r)
      in
      iter env mfs []

  let rec translate_exp env = function
    | Var (x, ys) -> Var (x, ys)
    | IConst i -> IConst i(*, TyInt*)
    | BConst b -> BConst b(*, TyBool*)
    | UConst -> UConst
    | FunBExp ((x, u), f) ->
      let env = Environment.add x (tysc_of_ty u) env in
      let id, k = fresh_CVar () in 
      FunSExp ((x, u), id, translate_exp_k env k f)
    | FixBExp ((x, y, u1, u), f) -> 
      let env = Environment.add y (tysc_of_ty u1) (Environment.add x (tysc_of_ty (TyFun (u1, u))) env) in
      let id, k = fresh_CVar () in 
      FixSExp ((x, y, u1, u), id, translate_exp_k env k f)
    | CAppExp (f1, f2) -> translate_exp_k env f2 f1
    | AppMExp (f1, f2) as f -> (*new*)
      let u = Typing.CC.type_of_program env (Exp f) in
      AppDExp (translate_exp env f1, (translate_exp env f2, (CoercionExp (CId u))))
    | BinOp (op, f1, f2) -> BinOp (op, translate_exp env f1, translate_exp env f2) (*new*)
    | IfExp (f1, f2, f3) -> IfExp (translate_exp env f1, translate_exp env f2, translate_exp env f3) (*new*)
    | MatchExp (f, ms) -> 
      let f = translate_exp env f in
      let ms = List.map (fun (mf, f) -> let env, mf = translate_mf env mf in mf, translate_exp env f) ms in
      MatchExp (f, ms)
    | LetExp (x, ys, f1, f2) -> (*new*)
      let u = Typing.CC.type_of_program env (Exp f1) in
      LetExp (x, ys, translate_exp env f1, translate_exp (Environment.add x (TyScheme (ys, u)) env) f2)
    | NilExp u -> NilExp u
    | ConsExp (f1, f2) -> ConsExp (translate_exp env f1, translate_exp env f2) 
    | TupleExp fs -> TupleExp (List.map (fun f -> translate_exp env f) fs)
    | CastExp _ -> raise @@ Translation_bug "CC.translate cast"
    | FunSExp _ | FixSExp _ | FunAExp _ | FixAExp _ | CoercionExp _ | AppDExp _ | CSeqExp _ -> raise @@ Occur_LS1 "translate"
  and translate_exp_k env k = function
    | Var (x, ys) -> CAppExp (Var (x, ys), k)
    | IConst i -> CAppExp (IConst i, k)
    | BConst b -> CAppExp (BConst b, k)
    | UConst -> CAppExp (UConst, k)
    | FunBExp ((x, u), f) -> 
      let env = Environment.add x (tysc_of_ty u) env in
      let id, k' = fresh_CVar () in 
      CAppExp (FunSExp ((x, u), id, translate_exp_k env k' f), k)
    | FixBExp ((x, y, u1, u), f) -> 
      let env = Environment.add y (tysc_of_ty u1) (Environment.add x (tysc_of_ty (TyFun (u1, u))) env) in
      let id, k' = fresh_CVar () in 
      CAppExp (FixSExp ((x, y, u1, u), id, translate_exp_k env k' f), k)
    | BinOp (op, f1, f2) -> CAppExp (BinOp (op, translate_exp env f1, translate_exp env f2), k)
    | IfExp (f1, f2, f3) -> IfExp (translate_exp env f1, translate_exp_k env k f2, translate_exp_k env k f3)
    | AppMExp (f1, f2) -> AppDExp (translate_exp env f1, (translate_exp env f2, k))
    | CAppExp (f1, f2) -> 
      let id, k' = fresh_CVar () in 
      LetExp (id, [], CSeqExp (f2, k), translate_exp_k env k' f1)
    | MatchExp (f, ms) -> 
      let f = translate_exp env f in
      let ms = List.map (fun (mf, f) -> let env, mf = translate_mf env mf in mf, translate_exp_k env k f) ms in
      MatchExp (f, ms)
    | LetExp (x, ys, f1, f2) -> 
      let u = Typing.CC.type_of_program env (Exp f1) in
      LetExp (x, ys, translate_exp env f1, translate_exp_k (Environment.add x (TyScheme (ys, u)) env) k f2)
    | NilExp u -> CAppExp (NilExp u, k)
    | ConsExp (f1, f2) ->
      CAppExp (ConsExp (translate_exp env f1, translate_exp env f2), k)
    | TupleExp fs -> CAppExp (TupleExp (List.map (fun f -> translate_exp env f) fs), k)
    | CastExp _ -> raise @@ Translation_bug "CC.translate cast"
    | FunSExp _ | FixSExp _ | FunAExp _ | FixAExp _ | CoercionExp _ | AppDExp _ | CSeqExp _ -> raise @@ Occur_LS1 "translate"

  let translate env = function
    | Exp f -> Exp (translate_exp env f)
    | LetDecl (x, ys, f) -> LetDecl (x, ys, translate_exp env f)

  let rec translate_exp_alt env = function
    | Var (x, ys) -> Var (x, ys)
    | IConst i -> IConst i(*, TyInt*)
    | BConst b -> BConst b(*, TyBool*)
    | UConst -> UConst
    | FunBExp ((x, u), f) ->
      let env = Environment.add x (tysc_of_ty u) env in
      let id, k = fresh_CVar () in 
      FunAExp ((x, u), id, (translate_exp_alt env f, translate_exp_k_alt env k f))
    | FixBExp ((x, y, u1, u), f) -> 
      let env = Environment.add y (tysc_of_ty u1) (Environment.add x (tysc_of_ty (TyFun (u1, u))) env) in
      let id, k = fresh_CVar () in 
      FixAExp ((x, y, u1, u), id, (translate_exp_alt env f, translate_exp_k_alt env k f))
    | CAppExp (f1, f2) -> translate_exp_k_alt env f2 f1
    | AppMExp (f1, f2) -> (*new*)
      AppMExp (translate_exp_alt env f1, translate_exp_alt env f2)
    | BinOp (op, f1, f2) -> BinOp (op, translate_exp_alt env f1, translate_exp_alt env f2) (*new*)
    | IfExp (f1, f2, f3) -> IfExp (translate_exp_alt env f1, translate_exp_alt env f2, translate_exp_alt env f3) (*new*)
    | MatchExp (f, ms) -> 
      let f = translate_exp_alt env f in
      let ms = List.map (fun (mf, f) -> let env, mf = translate_mf env mf in mf, translate_exp_alt env f) ms in
      MatchExp (f, ms)
    | LetExp (x, ys, f1, f2) -> (*new*)
      let u = Typing.CC.type_of_program env (Exp f1) in
      LetExp (x, ys, translate_exp_alt env f1, translate_exp_alt (Environment.add x (TyScheme (ys, u)) env) f2)
    | NilExp u -> NilExp u
    | ConsExp (f1, f2) -> ConsExp (translate_exp_alt env f1, translate_exp_alt env f2)  
    | TupleExp fs -> TupleExp (List.map (fun f -> translate_exp_alt env f) fs)
    | CastExp _ -> raise @@ Translation_bug "CC.translate cast"
    | FunSExp _ | FixSExp _ | FunAExp _ | FixAExp _ | CoercionExp _ | AppDExp _ | CSeqExp _ -> raise @@ Occur_LS1 "translate"
  and translate_exp_k_alt env k = function
    | Var (x, ys) -> CAppExp (Var (x, ys), k)
    | IConst i -> CAppExp (IConst i, k)
    | BConst b -> CAppExp (BConst b, k)
    | UConst -> CAppExp (UConst, k)
    | FunBExp ((x, u), f) -> 
      let env = Environment.add x (tysc_of_ty u) env in
      let id, k' = fresh_CVar () in 
      CAppExp (FunAExp ((x, u), id, (translate_exp_alt env f, translate_exp_k_alt env k' f)), k)
    | FixBExp ((x, y, u1, u), f) -> 
      let env = Environment.add y (tysc_of_ty u1) (Environment.add x (tysc_of_ty (TyFun (u1, u))) env) in
      let id, k' = fresh_CVar () in 
      CAppExp (FixAExp ((x, y, u1, u), id, (translate_exp_alt env f, translate_exp_k_alt env k' f)), k)
    | BinOp (op, f1, f2) -> CAppExp (BinOp (op, translate_exp_alt env f1, translate_exp_alt env f2), k)
    | IfExp (f1, f2, f3) -> IfExp (translate_exp_alt env f1, translate_exp_k_alt env k f2, translate_exp_k_alt env k f3)
    | AppMExp (f1, f2) -> AppDExp (translate_exp_alt env f1, (translate_exp_alt env f2, k))
    | CAppExp (f1, f2) -> 
      let id, k' = fresh_CVar () in 
      LetExp (id, [], CSeqExp (f2, k), translate_exp_k_alt env k' f1)
    | MatchExp (f, ms) -> 
      let f = translate_exp_alt env f in
      let ms = List.map (fun (mf, f) -> let env, mf = translate_mf env mf in mf, translate_exp_k_alt env k f) ms in
      MatchExp (f, ms)
    | LetExp (x, ys, f1, f2) -> 
      let u = Typing.CC.type_of_program env (Exp f1) in
      LetExp (x, ys, translate_exp_alt env f1, translate_exp_k_alt (Environment.add x (TyScheme (ys, u)) env) k f2)
    | NilExp u -> CAppExp (NilExp u, k)
    | ConsExp (f1, f2) ->
      CAppExp (ConsExp (translate_exp_alt env f1, translate_exp_alt env f2), k)
    | TupleExp fs -> CAppExp (TupleExp (List.map (fun f -> translate_exp_alt env f) fs), k)
    | CastExp _ -> raise @@ Translation_bug "CC.translate cast"
    | FunSExp _ | FixSExp _ | FunAExp _ | FixAExp _ | CoercionExp _ | AppDExp _ | CSeqExp _ -> raise @@ Occur_LS1 "translate"

  let translate_alt env = function
    | Exp f -> Exp (translate_exp_alt env f)
    | LetDecl (x, ys, f) -> LetDecl (x, ys, translate_exp_alt env f)
end