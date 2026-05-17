open Syntax
open Static_manage

exception Closure_bug of string
exception Closure_error of string

let toplevel = ref []

(* let tvset = ref TV.empty *)

(* let ranges = ref [] *)

(* let crcs = ref [] *)

module KNorm = struct
  open Syntax.KNorm

  let rec exist_tv l1 l2 = match l2 with
    | h :: t -> if List.mem h l1 then true else exist_tv l1 t
    | [] -> false
  
  let rec ty_tv tvs u = match u with
    | TyInt | TyBool | TyUnit | TyDyn | TyFun (TyDyn, TyDyn) | TyList TyDyn as u -> (u, fun x -> x)
    | TyTuple us when List.fold_left (fun b u -> b && if u = TyDyn then true else false) true us -> (u, fun x -> x)
    | TyVar tv -> if not (List.mem tv tvs) then (TyManager.register u; (u, fun x -> x)) else (u, fun x -> x)
    | TyFun (u1, u2) ->
      let u1, ufun1 = ty_tv tvs u1 in
      let u2, ufun2 = ty_tv tvs u2 in
      if not (exist_tv (TV.elements (ftv_ty u1)) tvs) && not (exist_tv (TV.elements (ftv_ty u2)) tvs) then begin
        TyManager.register u;
        (u, fun x -> x)
      end else 
        let newu = Typing.fresh_tyvar () in
        let newtv = match newu with
        | TyVar (i, u) -> u := Some (TyFun (u1, u2)); (i, u)
        | _ -> raise @@ Closure_bug "not tyvar was created"
        in
        (newu, fun x -> ufun1 (ufun2 (Cls.SetTy (newtv, x))))
    | TyList u' -> 
      let u', ufun' = ty_tv tvs u' in
      if not (exist_tv (TV.elements (ftv_ty u)) tvs) then begin
        TyManager.register u;
        (u, fun x -> x)
      end else
        let newu = Typing.fresh_tyvar () in
        let newtv = match newu with
          | TyVar (i, u) -> u := Some (TyList u'); (i, u)
          | _ -> raise @@ Closure_bug "not tyvar was created"
        in
        (newu, fun x -> ufun' (Cls.SetTy (newtv, x)))
    | TyTuple us ->
      let us, ufuns = List.split @@ List.map (fun u -> ty_tv tvs u) us in
      if not @@ List.fold_left (fun b u -> b || exist_tv (TV.elements (ftv_ty u)) tvs) false us then begin
        TyManager.register u;
        (u, fun x -> x)
      end else
        let newu = Typing.fresh_tyvar () in
        let newtv = match newu with
          | TyVar (i, u) -> u := Some (TyTuple us); (i, u)
          | _ -> raise @@ Closure_bug "not tyvar was created"
        in
        (newu, fun x -> List.fold_left (fun x ufun -> ufun x) (Cls.SetTy (newtv, x)) (List.rev ufuns))

  let ta_tv tvs = function
    | Ty u -> let (u, f) = ty_tv tvs u in (Ty u, f)
    | TyNu -> (TyNu, fun x -> x)

  let tyvar_to_tyarg tvs = 
    let rec ttt l r = match l with
    | tv :: t -> ttt t ((Ty (TyVar tv)) :: r)
    | [] -> r
  in ttt (List.rev tvs) []

  let rec toCls_crc tvs c = 
    let is_static c = 
      let cached = CrcManager.mem c in
      let constant = match c with
      | Cls.CId
      | Cls.CSeqInj (Cls.CId, I) 
      | Cls.CSeqInj (Cls.CId, B) 
      | Cls.CSeqInj (Cls.CId, U) 
      | Cls.CSeqInj (Cls.CId, Ar) 
      | Cls.CSeqInj (Cls.CId, Li) -> true
      | _ -> false
      in
      cached || constant
    in
    match c with
    | CId _ -> Cls.CId
    | CSeq (CProj (g, (r, p)), c') ->
      let c' = toCls_crc tvs c' in
      let r = RangeManager.range_id r in
      let c = Cls.CSeqProj (g, (r, p), c') in
      if is_static c' then CrcManager.register c;
      c
    | CSeq (CId _, CInj g) -> Cls.CSeqInj (Cls.CId, g)
    | CSeq (c', CInj g) ->
      let c' = toCls_crc tvs c' in
      let c = Cls.CSeqInj (c', g) in
      if is_static c' then CrcManager.register c;
      c
    | CTvInj (tv, (r, p)) ->
      let r = RangeManager.range_id r in
      let c = Cls.CTvInj (tv, (r, p)) in
      if not (List.mem tv tvs) then begin
        TyManager.register (TyVar tv);
        CrcManager.register c
      end;
      c
    | CTvProj (tv, (r, p)) ->
      let r = RangeManager.range_id r in
      let c = Cls.CTvProj (tv, (r, p)) in
      if not (List.mem tv tvs) then begin
        TyManager.register (TyVar tv);
        CrcManager.register c
      end;
      c
    | CFun (c1, c2) ->
      let c1 = toCls_crc tvs c1 in
      let c2 = toCls_crc tvs c2 in
      let c = Cls.CFun (c1, c2) in
      if is_static c1 && is_static c2 then CrcManager.register c;
      c
    | CList c' ->
      let c' = toCls_crc tvs c' in
      let c = Cls.CList c' in
      if is_static c' then CrcManager.register c;
      c
    | CTuple cs ->
      let cs = List.map (fun c -> toCls_crc tvs c) cs in
      let c = Cls.CTuple cs in
      if List.fold_left (fun b c -> b && is_static c) true cs then CrcManager.register c;
      c
    | _ -> raise @@ Closure_bug "bad coercion"

  let rec toCls_exp known tvs args = function
    | Var x -> Cls.Var x
    | IConst i -> Cls.Int i
    | Add (x, y) -> Cls.Add (x, y)
    | Sub (x, y) -> Cls.Sub (x, y)
    | Mul (x, y) -> Cls.Mul (x, y)
    | Div (x, y) -> Cls.Div (x, y)
    | Mod (x, y) -> Cls.Mod (x, y)
    | Nil -> Cls.Nil
    | Cons (x, y) -> Cls.Cons (x, y)
    | Tuple xs -> Cls.Tuple xs
    | Hd x -> Cls.Hd x
    | Tl x -> Cls.Tl x
    | Tget (x, i) -> Tget (x, i)
    | MatchExp (x, ms) -> Cls.Match (x, List.map (fun (mf, f) -> mf, toCls_exp known tvs args f) ms)
    | IfEqExp (x, y, f1, f2) -> Cls.IfEq (x, y, toCls_exp known tvs args f1, toCls_exp known tvs args f2)
    | IfLteExp (x, y, f1, f2) -> Cls.IfLte (x, y, toCls_exp known tvs args f1, toCls_exp known tvs args f2)
    | AppDExp (x, (y, z)) when V.mem x known -> Cls.AppDDir (Cls.to_label x, (y, z))
    | AppDExp (x, (y, z)) -> Cls.AppDCls (x, (y, z))
    | AppMExp (x, y) when V.mem x known -> Cls.AppMDir (Cls.to_label x, y)
    | AppMExp (x, y) -> Cls.AppMCls (x, y)
    | AppTy (x, _, tas) -> 
      let uandf = List.map (ta_tv tvs) tas in
      let rec destruct_uandf l ru rf = match l with
        | (u, f) :: t -> destruct_uandf t (u::ru) (fun x -> rf (f x))
        | [] -> ru, rf 
      in let us, f = destruct_uandf (List.rev uandf) [] (fun x -> x) in
      let (zs, outer_tvs_len) = Environment.find x args in
      (* let (zs, outer_tvs_len) = 
        try Environment.find x args 
        with Not_found -> 
          (* x がトップレベルの関数（id_listなど）であれば環境は空で正常 *)
          if V.mem x known then ([], 0)
          else raise @@ Closure_bug (Format.asprintf "AppTy: environment for %s is not found!" x)
      in *)
      f (Cls.AppTy (x, List.length zs, outer_tvs_len, us))
    | CastExp (x, u1, u2, (r, p)) -> 
      let u1, udeclfun1 = ty_tv tvs u1 in 
      let u2, udeclfun2 = ty_tv tvs u2 in 
      udeclfun1 (udeclfun2 (Cls.Cast (x, u1, u2, (RangeManager.range_id r, p))))
    | CAppExp (x, y) -> Cls.CApp (x, y)
    | CSeqExp (x, y) -> Cls.CSeq (x, y)
    | CoercionExp c -> Cls.Coercion (toCls_crc tvs c)
    | LetExp (x, f1, f2) -> 
      let f1 = toCls_exp known tvs args f1 in
      (* let rec get_env args exp = match exp with
        | Cls.Var y | Cls.Cast (y, _, _, _) | Cls.CApp (y, _) -> 
            (try Some (Environment.find y args) with Not_found -> None)
        | Cls.Let (_, _, body) | Cls.SetTy (_, body) -> 
            get_env args body
        | Cls.AppTy (y, _, _, tas) ->
            (try 
               let (zs, outer_tvs) = Environment.find y args in
               (* AppTyは環境に型変数を追加するため、追加した分だけ k の位置をずらす必要がある。
                  List.length zs が k として使われるため、ダミー変数を入れて長さを水増しする *)
               let dummies = List.init (List.length tas) (fun _ -> "dummy_for_tas") in
               Some (zs @ dummies, outer_tvs)
             with Not_found -> None)
        | _ -> None
      in
      let args' = match get_env args f1 with
        | Some env_data -> Environment.add x env_data args
        | None -> args
      in
      let f2 = toCls_exp known tvs args' f2 in *)
      let f2 = toCls_exp known tvs args f2 in
      begin match f1 with
      | Cls.Coercion (Cls.CSeqInj (Cls.CId, (I | B | U as g))) -> CrcManager.register_inj x g
      | Cls.Coercion (Cls.CSeqProj ((I | B | U as g), (rid, p), Cls.CId)) -> CrcManager.register_proj x (g, rid, p)
      | Cls.Var y when CrcManager.mem_inj y -> CrcManager.register_inj x (CrcManager.find_inj y)
      | Cls.Var y when CrcManager.mem_proj y -> CrcManager.register_proj x (CrcManager.find_proj y)
      | _ -> ()
      end;
      Cls.Let (x, f1, f2)
    | LetRecSExp (x, tvs', (y, z), f1, f2) ->
      let k_fv = V.remove x @@ V.remove y @@ V.remove z @@ fv_exp f1 in
      let new_tvs = tvs' @ tvs in
      let known', f1' =
        if not (V.is_empty k_fv) || List.length new_tvs != 0 then
          let f1' = toCls_exp known new_tvs args f1 in
          known, f1'
        else 
          let toplevel_backup = !toplevel in
          let static_backup = static_save () in
          let known' = V.add x known in
          let f1' = toCls_exp known' new_tvs args f1 in
          let zs = V.diff (Cls.fv_exp f1') (V.of_list [y; z]) in
          if V.is_empty zs (*&& List.length new_tvs = 0*) then 
            known', f1'
          else begin
            toplevel := toplevel_backup; static_restore static_backup;
            (* Format.fprintf Format.err_formatter "backtracking %s\n" x; *)
            let f1' = toCls_exp known new_tvs args f1 in
            known, f1'
          end
      in
      let zs = V.elements (V.diff (Cls.fv_exp f1') (V.of_list [x; y; z])) in
      (* let zts = List.map (fun z -> (z, Environment.find z tyenv')) zs in *)
      let fundef = Cls.FundefD { name = Cls.to_label x; tvs = (new_tvs, List.length tvs'); arg = (y, z); formal_fv = zs; body = f1' } in
      if not @@ List.mem fundef !toplevel then toplevel := fundef :: !toplevel;
      let f2' = toCls_exp known' tvs (Environment.add x (zs, List.length tvs) args) f2 in
      if V.mem x (Cls.fv_exp f2') then
        Cls.MakeCls (x, { Cls.entry = Cls.to_label x; Cls.actual_fv = zs }, { ftvs = tyvar_to_tyarg tvs; offset = List.length tvs' }, f2')
      else f2'
    | LetRecAExp _ -> raise @@ Closure_bug "shouldn't apper alt in closure"
    | LetRecBExp (x, tvs', y, f1, f2) ->
      let k_fv = V.remove x @@ V.remove y @@ fv_exp f1 in
      let new_tvs = tvs' @ tvs in
      let known', f1' =
        if not (V.is_empty k_fv) || List.length new_tvs != 0 then
          let f1' = toCls_exp known new_tvs args f1 in
          known, f1'
        else 
          let toplevel_backup = !toplevel in
          let static_backup = static_save () in
          let known' = V.add x known in
          let f1' = toCls_exp known' new_tvs args f1 in
          let zs = V.diff (Cls.fv_exp f1') (V.singleton y) in
          if V.is_empty zs (*&& List.length new_tvs = 0*) then 
            known', f1'
          else begin
            toplevel := toplevel_backup; static_restore static_backup;
            (* Format.fprintf Format.err_formatter "backtracking %s\n" x; *)
            let f1' = toCls_exp known new_tvs args f1 in
            known, f1'
          end
      in
      let zs = V.elements (V.diff (Cls.fv_exp f1') (V.of_list [x; y])) in
      (* let zts = List.map (fun z -> (z, Environment.find z tyenv')) zs in *)
      let fundef = Cls.FundefM { name = Cls.to_label x; tvs = (new_tvs, List.length tvs'); arg = y; formal_fv = zs; body = f1' } in
      if not @@ List.mem fundef !toplevel then toplevel := fundef :: !toplevel;
      let f2' = toCls_exp known' tvs (Environment.add x (zs, List.length tvs) args) f2 in
      if V.mem x (Cls.fv_exp f2') then
        Cls.MakeCls (x, { Cls.entry = Cls.to_label x; Cls.actual_fv = zs }, { ftvs = tyvar_to_tyarg tvs; offset = List.length tvs' }, f2')
      else f2'

  let toCls kf known = 
    let f = match kf with Exp f -> f | _ -> raise @@ Closure_bug "kf is not exp" in
    toplevel := []; static_clear ();
    toCls_exp known [] Environment.empty f
end

module Cls = struct
  open Syntax.Cls

  let rec replace_var vx vy f = 
    let replace x = if x = vx then vy else x in
    match f with
    | Var x -> Var (replace x)
    | Int i -> Int i
    | Nil -> Nil
    | Add (x, y) -> Add (replace x, replace y)
    | Sub (x, y) -> Sub (replace x, replace y)
    | Mul (x, y) -> Mul (replace x, replace y)
    | Div (x, y) -> Div (replace x, replace y)
    | Mod (x, y) -> Mod (replace x, replace y)
    | Cons (x, y) -> Cons (replace x, replace y)
    | Tuple xs -> Tuple (List.map (fun x -> replace x) xs)
    | Hd x -> Hd (replace x)
    | Tl x -> Tl (replace x)
    | Tget (x, i) -> Tget (replace x, i)
    | IfEq (x, y, f1, f2) -> IfEq (replace x, replace y, replace_var vx vy f1, replace_var vx vy f2)
    | IfLte (x, y, f1, f2) -> IfLte (replace x, replace y, replace_var vx vy f1, replace_var vx vy f2)
    | Match (x, ms) -> Match (replace x, List.map (fun (mf, f) -> mf, replace_var vx vy f) ms)
    | AppTy (x, k, n, tas) -> AppTy (replace x, k, n, tas)
    | AppDCls (x, (y, k)) -> AppDCls (replace x, (replace y, replace k))
    | AppDDir (l, (y, k)) -> AppDDir (to_label (replace (to_id l)), (replace y, replace k))
    | CApp (x, k) -> CApp (replace x, replace k)
    | CSeq (k1, k2) -> CSeq (replace k1, replace k2)
    | Coercion c -> Coercion c
    | Let (x, f1, f2) -> Let (x, replace_var vx vy f1, replace_var vx vy f2)
    | MakeCls (x, {entry = l; actual_fv = fvs}, ftvs, f) -> MakeCls (x, {entry=to_label (replace (to_id l)); actual_fv = List.map replace fvs}, ftvs, replace_var vx vy f)
    | SetTy _ | Insert _ -> raise @@ Closure_bug "SetTy or Insert appear in replace"
    | AppMCls _ | AppMDir _ -> raise @@ Closure_bug "AppM appear in replace"
    | Cast _ -> raise @@ Closure_bug "Cast appear in replace"

  let rec to_alt ids = function
    | Let (x, Coercion CId, f) -> 
      let f = to_alt (V.add x ids) f in
      if V.mem x (fv_exp f) then raise @@ Closure_error "to_alt: id appear"
      else f
    | Let (x, CSeq (k1, k2), f) ->
      begin match V.mem k1 ids, V.mem k2 ids with
      | true, true -> 
        let f = to_alt (V.add x ids) f in
        if V.mem x (fv_exp f) then raise @@ Closure_error "to_alt: id appear"
        else f
      | true, false -> to_alt ids @@ replace_var x k2 f
      | false, true -> to_alt ids @@ replace_var x k1 f
      | false, false -> Let (x, CSeq (k1, k2), to_alt ids f)
      end
    | Let (x, CApp (y, k), f) when V.mem k ids -> to_alt ids (replace_var x y f)
    | Let (x, f1, f2) -> Let (x, to_alt ids f1, to_alt ids f2)
    | IfEq (x, y, f1, f2) -> IfEq (x, y, to_alt ids f1, to_alt ids f2)
    | IfLte (x, y, f1, f2) -> IfLte (x, y, to_alt ids f1, to_alt ids f2)
    | Match (x, ms) -> Match (x, List.map (fun (mf, f) -> mf, to_alt ids f) ms)
    | AppDCls (x, (y, k)) when V.mem k ids -> AppMCls (x, y)
    | AppDDir (l, (y, k)) when V.mem k ids -> AppMDir (l, y)
    | CApp (x, k) when V.mem k ids -> Var x
    | MakeCls (x, cls, ftvs, f) -> MakeCls (x, cls, ftvs, to_alt ids f)
    | AppMCls _ | AppMDir _ -> raise @@ Closure_bug "AppM appear in to_alt"
    | Cast _ -> raise @@ Closure_bug "Cast appear in to_alt"
    | f -> f

  let rec alt_funs = function
    | h :: t -> 
      begin match h with
      | FundefD {name = l; tvs = (tvs, n); arg = (y, k); formal_fv = ids; body = f } -> 
        FundefM {name = l; tvs = (tvs, n); arg = y; formal_fv = ids; body = to_alt (V.singleton k) f } ::
        FundefD {name = l; tvs = (tvs, n); arg = (y, k); formal_fv = ids; body = to_alt V.empty f } ::
        (alt_funs t)
      | _ -> raise @@ Closure_bug "alt form appear in alt_funs"
      end
    | [] -> []

  let altCls p alt =
    if alt then Prog (alt_funs !toplevel, to_alt V.empty p)
    else Prog (List.rev !toplevel, p)
end

let toCls_program kf venv ~alt =
  let p = KNorm.toCls kf venv in
  let p = Cls.altCls p alt in
  p