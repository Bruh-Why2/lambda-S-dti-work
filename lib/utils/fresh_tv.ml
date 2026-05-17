open Syntax

let pick_tv u = match u with
  | TyVar tv -> tv
  | _ -> raise @@ Failure "not_tv"

let rec tv_renew_ty u env = match u with
  | TyVar (i, _) -> 
    begin 
    try TyVar (Environment.find (string_of_int i) env), env with
    Not_found -> let tv = pick_tv (Typing.fresh_tyvar ()) in
    let env = Environment.add (string_of_int i) tv env in
    TyVar tv, env
    end
  | TyDyn | TyInt | TyBool | TyUnit -> u, env
  | TyFun (u1, u2) -> 
    let u1, env = tv_renew_ty u1 env in
    let u2, env = tv_renew_ty u2 env in
    TyFun (u1, u2), env
  | TyList u -> 
    let u, env = tv_renew_ty u env in
    TyList u, env
  | TyTuple us ->
    let rec iter env l r = match l with
    | h :: t ->
      let u, env = tv_renew_ty h env in
      iter env t (u :: r)
    | [] -> 
      TyTuple (List.rev r), env
    in
    iter env us []

let rec tv_renew_coercion c env = match c with
  | CInj _ | CProj _ | CFail _ -> c, env
  | CTvInj ((i, _), p) -> 
    begin
    try CTvInj ((Environment.find (string_of_int i) env), p), env with
    Not_found -> let tv = pick_tv (Typing.fresh_tyvar ())in
    let env = Environment.add (string_of_int i) tv env in
    CTvInj (tv, p), env
    end
  | CTvProj ((i, _), p) -> 
    begin
    try CTvProj ((Environment.find (string_of_int i) env), p), env with
    Not_found -> let tv = pick_tv (Typing.fresh_tyvar ()) in
    let env = Environment.add (string_of_int i) tv env in
    CTvProj (tv, p), env
    end
  | CTvProjInj ((i, _), p, q) -> 
    begin
    try CTvProjInj ((Environment.find (string_of_int i) env), p, q), env with
    Not_found -> let tv = pick_tv (Typing.fresh_tyvar ()) in
    let env = Environment.add (string_of_int i) tv env in
    CTvProjInj (tv, p, q), env
    end
  | CId u ->
    let u, env = tv_renew_ty u env in
    CId u, env
  | CFun (c1, c2) ->
    let c1, env = tv_renew_coercion c1 env in
    let c2, env = tv_renew_coercion c2 env in
    CFun (c1, c2), env 
  | CList c ->
    let c, env = tv_renew_coercion c env in
    CList c, env
  | CTuple cs ->
    let rec iter env l r = match l with
    | h :: t ->
      let c, env = tv_renew_coercion h env in
      iter env t (c :: r)
    | [] -> 
      CTuple (List.rev r), env
    in
    iter env cs []
  | CSeq (c1, c2) ->
    let c1, env = tv_renew_coercion c1 env in
    let c2, env = tv_renew_coercion c2 env in
    CSeq (c1, c2), env 

let rec tv_renew_mf mf env = match mf with
  | MatchILit _ | MatchBLit _ | MatchULit -> mf, env
  | MatchVar (x, u) -> 
    let u, env = tv_renew_ty u env in
    MatchVar (x, u), env
  | MatchNil u -> 
    let u, env = tv_renew_ty u env in
    MatchNil u, env
  | MatchCons (mf1, mf2) ->
    let mf1, env = tv_renew_mf mf1 env in
    let mf2, env = tv_renew_mf mf2 env in
    MatchCons (mf1, mf2), env
  | MatchTuple mfs ->
    let rec iter env l r = match l with
    | h :: t ->
      let mf, env = tv_renew_mf h env in
      iter env t (mf :: r)
    | [] -> 
      MatchTuple (List.rev r), env
    in
    iter env mfs []
  | MatchWild u -> 
    let u, env = tv_renew_ty u env in
    MatchWild u, env

module CC = struct
  open Syntax.CC

  let rec tv_renew_exp e env = match e with
    | Var (x, us) ->
      let env = List.fold_left (fun env -> fun u -> match u with Ty u -> snd (tv_renew_ty u env) | TyNu -> env) env us in
      let us = List.map (fun u -> match u with Ty u -> Syntax.Ty (fst @@ (tv_renew_ty u env)) | TyNu -> TyNu) us in
      Var (x, us), env
    | IConst _ | BConst _ | UConst -> e, env
    | BinOp (op, e1, e2) -> 
      let e1, env = tv_renew_exp e1 env in
      let e2, env = tv_renew_exp e2 env in
      BinOp (op, e1, e2), env
    | IfExp (e1, e2, e3) ->
      let e1, env = tv_renew_exp e1 env in
      let e2, env = tv_renew_exp e2 env in
      let e3, env = tv_renew_exp e3 env in
      IfExp (e1, e2, e3), env
    | FunBExp ((x, u), e) ->
      let u, env = tv_renew_ty u env in
      let e, env = tv_renew_exp e env in
      FunBExp ((x, u), e), env
    | FixBExp ((x, y, u1, u2), e) ->
      let u1, env = tv_renew_ty u1 env in
      let u2, env = tv_renew_ty u2 env in
      let e, env = tv_renew_exp e env in
      FixBExp ((x, y, u1, u2), e), env
    | AppMExp (e1, e2) ->
      let e1, env = tv_renew_exp e1 env in
      let e2, env = tv_renew_exp e2 env in
      AppMExp (e1, e2), env
    | CAppExp (e1, e2) ->
      let e1, env = tv_renew_exp e1 env in
      let e2, env = tv_renew_exp e2 env in
      CAppExp (e1, e2), env
    | CoercionExp c -> 
      let c, env = tv_renew_coercion c env in
      CoercionExp c, env
    | CastExp (e, u1, u2, r_p) -> 
      let e, env = tv_renew_exp e env in
      let u1, env = tv_renew_ty u1 env in
      let u2, env = tv_renew_ty u2 env in
      CastExp (e, u1, u2, r_p), env
    | MatchExp (e, ms) ->
      let e, env = tv_renew_exp e env in
      let ms, env = tv_renew_ms ms env in
      MatchExp (e, ms), env
    | LetExp (x, tvs, e1, e2) ->
      let env = List.fold_left (fun env -> fun (i, _ as tv) -> Syntax.Environment.add (string_of_int i) tv env) env tvs  in
      let e1, env = tv_renew_exp e1 env in
      let e2, env = tv_renew_exp e2 env in
      LetExp (x, tvs, e1, e2), env
    | NilExp u -> 
      let u, env = tv_renew_ty u env in
      NilExp u, env
    | ConsExp (e1, e2) ->
      let e1, env = tv_renew_exp e1 env in
      let e2, env = tv_renew_exp e2 env in
      ConsExp (e1, e2), env
    | TupleExp es ->
      let rec iter env l r = match l with
      | h :: t ->
        let e, env = tv_renew_exp h env in
        iter env t (e :: r)
      | [] -> 
        TupleExp (List.rev r), env
      in
      iter env es []
    | FunSExp _ | FixSExp _ | FunAExp _ | FixAExp _ | AppDExp _ | CSeqExp _ -> raise @@ Occur_LS1 "fresh_tv"
  and tv_renew_ms ms env = match ms with
    | (mf, e) :: ms ->
      let mf, env = tv_renew_mf mf env in
      let e, env = tv_renew_exp e env in
      let ms, env = tv_renew_ms ms env in
      (mf, e) :: ms, env
    | [] -> [], env

  let tv_renew p = match p with
  | Exp e -> 
    let e, _ = tv_renew_exp e Syntax.Environment.empty in 
    Exp e
  | LetDecl (id, tvs, e) -> 
    let env = List.fold_left (fun env -> fun (i, _ as tv) -> Syntax.Environment.add (string_of_int i) tv env) Syntax.Environment.empty tvs  in
    let e, _ = tv_renew_exp e env in
    LetDecl (id, tvs, e)
end