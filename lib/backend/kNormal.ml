open Syntax

exception KNormal_error of string
exception KNormal_bug of string

let subst_type = Typing.subst_type

(* generate variable string for insert_let *)
let counter = ref 0
let genvar x = 
  let v = !counter in
  counter := v + 1;
  Printf.sprintf "%s_%d" x !counter

let rec alpha_mf idenv = function
  | MatchILit _ | MatchBLit _ | MatchULit | MatchNil _ | MatchWild _  as mf -> mf, idenv
  | MatchVar (x, u) ->
    let newx = genvar x in
    MatchVar (newx, u), Environment.add x newx idenv
  | MatchCons (mf1, mf2) -> 
    let mf1, idenv = alpha_mf idenv mf1 in
    let mf2, idenv = alpha_mf idenv mf2 in
    MatchCons (mf1, mf2), idenv
  | MatchTuple mfs ->
    let rec iter idenv l r = match l with
    | h :: t ->
      let mf, idenv = alpha_mf idenv h in
      iter idenv t (mf :: r)
    | [] -> 
      MatchTuple (List.rev r), idenv
    in
    iter idenv mfs []

let rec k_normalize_mf tvsenv f = function
  | MatchILit _ | MatchNil _ | MatchWild _  as mf -> mf, tvsenv, fun f -> f
  | MatchBLit b -> 
    let i = if b then 1 else 0 in
    MatchILit i, tvsenv, fun f -> f
  | MatchULit ->
    MatchILit 0, tvsenv, fun f -> f
  | MatchVar (x, u) -> MatchWild u, Environment.add x [] tvsenv, fun f' -> KNorm.LetExp (x, f, f')
  | MatchCons (mf1, mf2) -> 
    let x = genvar "_var" in
    let mf1, tvsenv, decl_var1 = k_normalize_mf tvsenv (KNorm.LetExp (x, f, Hd x)) mf1 in
    let y = genvar "_var" in
    let mf2, tvsenv, decl_var2 = k_normalize_mf tvsenv (KNorm.LetExp (y, f, Tl y)) mf2 in
    MatchCons (mf1, mf2), tvsenv, fun f -> decl_var1 (decl_var2 f)
  | MatchTuple mfs -> 
    let rec iter tvsenv l i mfs decl_vars = match l with
    | h :: t ->
      let x = genvar "_var" in
      let mf, tvsenv, decl_var = k_normalize_mf tvsenv (KNorm.LetExp (x, f, KNorm.Tget (x, i))) h in
      iter tvsenv t (i + 1) (mf :: mfs) (decl_var :: decl_vars)
    | [] -> 
      MatchTuple (List.rev mfs), tvsenv, fun f -> List.fold_left (fun f decl_var -> decl_var f) f decl_vars
    in
    iter tvsenv mfs 0 [] []

module CC = struct
  open Syntax.CC

  (* alpha : 変数の名前が被らないように付け替える *)
  let rec alpha_exp idenv = function
    | Var (x, tas) -> Var (Environment.find x idenv, tas)
    | IConst _ | BConst _ | UConst as f -> f
    | BinOp (op, f1, f2) -> BinOp (op, alpha_exp idenv f1, alpha_exp idenv f2)
    | IfExp (f1, f2, f3) ->
      IfExp (alpha_exp idenv f1, alpha_exp idenv f2, alpha_exp idenv f3)
    | FunBExp ((x, u), f) -> 
      let newx = genvar x in
      FunBExp ((newx, u), alpha_exp (Environment.add x newx idenv) f)
    | FixBExp _ -> raise @@ KNormal_error "FixExp should not be alpha_exp's argument"
    | FunSExp ((x, u), k, f) -> 
      let newx = genvar x in
      let newk = genvar k in
      FunSExp ((newx, u), newk, alpha_exp (Environment.add x newx (Environment.add k newk idenv)) f)
    | FixSExp _ -> raise @@ KNormal_error "FixSExp should not be alpha_exp's argument"
    | FunAExp ((x, u), k, (f1, f2)) -> 
      let newx = genvar x in
      let newk = genvar k in
      let idenv = Environment.add x newx (Environment.add k newk idenv) in
      FunAExp ((newx, u), newk, (alpha_exp idenv f1, alpha_exp idenv f2))
    | FixAExp _ -> raise @@ KNormal_bug "FixAExp should not be alpha_exp's argument"
    | AppMExp (f1, f2) -> AppMExp (alpha_exp idenv f1, alpha_exp idenv f2)
    | AppDExp (f1, (f2, f3)) -> AppDExp (alpha_exp idenv f1, (alpha_exp idenv f2, alpha_exp idenv f3))
    | CastExp (f1, u1, u2, p) ->
      CastExp (alpha_exp idenv f1, u1, u2, p)
    | CAppExp (f1, f2) -> CAppExp (alpha_exp idenv f1, alpha_exp idenv f2)
    | CSeqExp (f1, f2) -> CSeqExp (alpha_exp idenv f1, alpha_exp idenv f2)
    | LetExp (x, tvs, FixBExp ((x', y, u1, u2), f1), f2) -> 
      assert (x = x');
      let newx = genvar x in
      let idenv = Environment.add x newx idenv in
      let newy = genvar y in
      LetExp (newx, tvs, FixBExp ((newx, newy, u1, u2), alpha_exp (Environment.add y newy idenv) f1), alpha_exp idenv f2)
    | LetExp (x, tvs, FixSExp ((x', y, u1, u2), k, f1), f2) -> 
      assert (x = x');
      let newx = genvar x in
      let idenv = Environment.add x newx idenv in
      let newy = genvar y in
      let newk = genvar k in
      LetExp (newx, tvs, FixSExp ((newx, newy, u1, u2), newk, alpha_exp (Environment.add y newy (Environment.add k newk idenv)) f1), alpha_exp idenv f2)
    | LetExp (x, tvs, FixAExp ((x', y, u1, u2), k, (f1, f2)), f3) -> 
      assert (x = x');
      let newx = genvar x in
      let idenv = Environment.add x newx idenv in
      let newy = genvar y in
      let newk = genvar k in
      let idenv' = Environment.add y newy (Environment.add k newk idenv) in
      LetExp (newx, tvs, FixAExp ((newx, newy, u1, u2), newk, (alpha_exp idenv' f1, alpha_exp idenv' f2)), alpha_exp idenv f3)
    | LetExp (x, tvs, f1, f2) -> 
      let newx = genvar x in
      LetExp (newx, tvs, alpha_exp idenv f1, alpha_exp (Environment.add x newx idenv) f2)
    | CoercionExp c -> CoercionExp c
    | NilExp u -> NilExp u
    | ConsExp (f1, f2) -> ConsExp (alpha_exp idenv f1, alpha_exp idenv f2)
    | MatchExp (f, ms) -> 
      MatchExp (alpha_exp idenv f, List.map (fun (mf, f) -> let mf, idenv = alpha_mf idenv mf in (mf, alpha_exp idenv f)) ms)
    | TupleExp fs -> 
      TupleExp (List.map (fun f -> alpha_exp idenv f) fs)

  let alpha_program idenv = function
    | Exp f -> Exp (alpha_exp idenv f), idenv
    | LetDecl (x, tvs, FixBExp ((x', y, u1, u2), f)) ->
      assert (x = x');
      let newx = genvar x in
      let idenv = Environment.add x newx idenv in
      let newy = genvar y in
      LetDecl (newx, tvs, FixBExp ((newx, newy, u1, u2), alpha_exp (Environment.add y newy idenv) f)), idenv
    | LetDecl (x, tvs, FixSExp ((x', y, u1, u2), k, f)) ->
      assert (x = x');
      let newx = genvar x in
      let idenv = Environment.add x newx idenv in
      let newy = genvar y in
      let newk = genvar k in
      LetDecl (newx, tvs, FixSExp ((newx, newy, u1, u2), newk, alpha_exp (Environment.add y newy (Environment.add k newk idenv)) f)), idenv
    | LetDecl (x, tvs, FixAExp ((x', y, u1, u2), k, (f1, f2))) ->
      assert (x = x');
      let newx = genvar x in
      let idenv = Environment.add x newx idenv in
      let newy = genvar y in
      let newk = genvar k in
      let idenv' = Environment.add y newy (Environment.add k newk idenv) in
      LetDecl (newx, tvs, FixAExp ((newx, newy, u1, u2), newk, (alpha_exp idenv' f1, alpha_exp idenv' f2))), idenv
    | LetDecl (x, tvs, f) -> 
      let newx = genvar x in
      LetDecl (newx, tvs, alpha_exp idenv f), Environment.add x newx idenv

  let insert_let f (k: id -> KNorm.exp) = match f with
    | KNorm.Var x -> k x
    | _ as f -> 
      let x = genvar "_var" in
      let f' = k x in (* Var以外に自由な型変数への代入などは存在しないので、ここは[]で大丈夫 *)
      KNorm.LetExp (x, f, f') (* todo:考える。とりあえず[] *)
      (*多分大丈夫、applicationにしか不要で、(fun x...) vなら既に代入済み、(fun (x:?)...) vならcast済み*)

  let rec k_normalize_exp tvsenv f ~static = 
    let k_normalize_exp = k_normalize_exp ~static in 
    match f with
    | Var (x, tas) -> 
      let tvs = Environment.find x tvsenv in 
      if List.length tas = 0 && List.length tvs = 0 || static then KNorm.Var x
      else if List.length tas = List.length tvs then KNorm.AppTy (x, tvs, tas)
      else raise @@ KNormal_bug "tas and tvs don't have same length"
    | IConst i -> KNorm.IConst i
    | BConst b -> let i = if b then 1 else 0 in KNorm.IConst i
    | UConst -> KNorm.IConst 0
    | BinOp (op, f1, f2) as f -> begin match op with
      | Plus -> 
        let f1 = k_normalize_exp tvsenv f1 in
        let f2 = k_normalize_exp tvsenv f2 in
        insert_let f1 @@ fun x -> insert_let f2 @@ fun y -> KNorm.Add (x, y)
      | Minus ->
        let f1 = k_normalize_exp tvsenv f1 in
        let f2 = k_normalize_exp tvsenv f2 in
        insert_let f1 @@ fun x -> insert_let f2 @@ fun y -> KNorm.Sub (x, y)
      | Mult -> 
        let f1 = k_normalize_exp tvsenv f1 in
        let f2 = k_normalize_exp tvsenv f2 in
        insert_let f1 @@ fun x -> insert_let f2 @@ fun y -> KNorm.Mul (x, y)
      | Div -> 
        let f1 = k_normalize_exp tvsenv f1 in
        let f2 = k_normalize_exp tvsenv f2 in
        insert_let f1 @@ fun x -> insert_let f2 @@ fun y -> KNorm.Div (x, y)
      | Mod -> 
        let f1 = k_normalize_exp tvsenv f1 in
        let f2 = k_normalize_exp tvsenv f2 in
        insert_let f1 @@ fun x -> insert_let f2 @@ fun y -> KNorm.Mod (x, y)
      | _ -> k_normalize_exp tvsenv (IfExp (f, BConst true, BConst false))
      end
    | IfExp (f1, f2, f3) ->
      let f2' = k_normalize_exp tvsenv f2 in
      let f3' = k_normalize_exp tvsenv f3 in
      begin match f1 with
        | BinOp (op, f1, f2) -> 
          let f1 = k_normalize_exp tvsenv f1 in
          let f2 = k_normalize_exp tvsenv f2 in
          begin match op with
            | Eq -> insert_let f1 @@ fun x -> insert_let f2 @@ fun y -> IfEqExp (x, y, f2', f3')
            | Neq -> insert_let f1 @@ fun x -> insert_let f2 @@ fun y -> IfEqExp (x, y, f3', f2')
            | Lt -> insert_let f1 @@ fun x -> insert_let f2 @@ fun y -> IfLteExp (x, y, IfEqExp (x, y, f3', f2'), f3')
            | Lte -> insert_let f1 @@ fun x -> insert_let f2 @@ fun y -> IfLteExp (x, y, f2', f3')
            | Gt -> insert_let f1 @@ fun x -> insert_let f2 @@ fun y -> IfLteExp (x, y, f3', f2')
            | Gte -> insert_let f1 @@ fun x -> insert_let f2 @@ fun y -> IfLteExp (x, y, IfEqExp (x, y, f2', f3'), f2')
            | _ -> raise @@ KNormal_bug "if-cond type should bool"
          end
        | Var _ | BConst _ | IfExp _ | AppMExp _ | AppDExp _ | LetExp _ | CastExp _ | CAppExp _ | MatchExp _ as f ->
          let f = k_normalize_exp tvsenv f in 
          insert_let f @@ fun x -> insert_let (KNorm.IConst 1) @@ fun y -> IfEqExp (x, y, f2', f3')
        | IConst _ | UConst | FunBExp _ | FixBExp _ | FunSExp _ | FixSExp _ | FunAExp _ | FixAExp _ | CSeqExp _ | CoercionExp _ | NilExp _ | ConsExp _ | TupleExp _ -> raise @@ KNormal_bug "if-cond type should bool"
      end
    | FunBExp ((x, _), f) -> 
      let tent_var = genvar "_var" in
      let f = k_normalize_exp (Environment.add x [] tvsenv) f in
      KNorm.LetRecBExp (tent_var, [], x, f, KNorm.Var tent_var)
    | FixBExp _ -> raise @@ KNormal_bug "FixExp should appear in let"
    | FunSExp ((x, _), k, f) -> 
      let tent_var = genvar "_var" in
      let f = k_normalize_exp (Environment.add x [] @@ Environment.add k [] tvsenv) f in
      KNorm.LetRecSExp (tent_var, [], (x, k), f, KNorm.Var tent_var)
    | FixSExp _ -> raise @@ KNormal_bug "FixSExp should appear in let"
    | FunAExp ((x, _), k, (f1, f2)) ->
      let tent_var = genvar "_var" in
      let f1 = k_normalize_exp (Environment.add x [] tvsenv) f1 in
      let f2 = k_normalize_exp (Environment.add x [] @@ Environment.add k [] tvsenv) f2 in
      KNorm.LetRecAExp (tent_var, [], (x, k), (f1, f2), KNorm.Var tent_var)
    | FixAExp _ -> raise @@ KNormal_bug "FixAExp should appear in let"
    | AppMExp (f1, f2) ->
      let f1 = k_normalize_exp tvsenv f1 in 
      let f2 = k_normalize_exp tvsenv f2 in
      insert_let f1 @@ fun x -> insert_let f2 @@ fun y -> KNorm.AppMExp (x, y)
    | AppDExp (f1, (f2, f3)) ->
      let f1 = k_normalize_exp tvsenv f1 in 
      let f2 = k_normalize_exp tvsenv f2 in
      let f3 = k_normalize_exp tvsenv f3 in
      insert_let f1 @@ fun x -> insert_let f2 @@ fun y -> insert_let f3 @@ fun z -> KNorm.AppDExp (x, (y, z))
    | CastExp (f, u1, u2, r_p) ->
      if static then raise @@ KNormal_error "static but Cast appear";
      let f = k_normalize_exp tvsenv f in
      insert_let f @@ fun x -> KNorm.CastExp (x, u1, u2, r_p)
    | CAppExp (f1, f2) -> 
      let f1 = k_normalize_exp tvsenv f1 in
      let f2 = k_normalize_exp tvsenv f2 in 
      insert_let f1 @@ fun x -> insert_let f2 @@ fun y -> KNorm.CAppExp (x, y)
    | CSeqExp (f1, f2) ->
      let f1 = k_normalize_exp tvsenv f1 in
      let f2 = k_normalize_exp tvsenv f2 in 
      insert_let f1 @@ fun x -> insert_let f2 @@ fun y -> KNorm.CSeqExp (x, y)
    | CoercionExp c -> KNorm.CoercionExp c
    | MatchExp (f, ms) ->
      let f = k_normalize_exp tvsenv f in
      let msf = fun f -> List.map (fun (mf, f') -> let mf, tvsenv, decl_var = k_normalize_mf tvsenv f mf in mf, decl_var @@ k_normalize_exp tvsenv f') ms in
      insert_let f @@ fun x -> KNorm.MatchExp (x, msf (Var x))
    | NilExp _ -> KNorm.Nil
    | ConsExp (f1, f2) -> 
      let f1 = k_normalize_exp tvsenv f1 in
      let f2 = k_normalize_exp tvsenv f2 in
      insert_let f2 @@ fun y -> insert_let f1 @@ fun x -> KNorm.Cons (x, y)
    | TupleExp fs ->
      let rec make_tuple fs l = match fs with
      | f :: fs -> 
        let f = k_normalize_exp tvsenv f in
        insert_let f @@ fun x -> (make_tuple fs (x :: l))
      | [] -> KNorm.Tuple (List.rev l)
      in
      make_tuple fs []
    | LetExp (x, tvs, f1, f2) -> 
      begin match f1 with
        | FunBExp ((x', _), f1) ->
          let f1 = k_normalize_exp (Environment.add x' [] tvsenv) f1 in
          let f2 = k_normalize_exp (Environment.add x tvs tvsenv) f2 in
          KNorm.LetRecBExp (x, (if static then [] else tvs), x', f1, f2)
        | FixBExp ((x', y, _, _), f1) ->
          assert (x' = x);
          let f1 = k_normalize_exp (Environment.add y [] (Environment.add x' [] tvsenv)) f1 in
          let f2 = k_normalize_exp (Environment.add x tvs tvsenv) f2 in
          KNorm.LetRecBExp (x, (if static then [] else tvs), y, f1, f2)
        | FunSExp ((y, _), k, f1) ->
          let f1 = k_normalize_exp (Environment.add y [] @@ Environment.add k [] tvsenv) f1 in
          let f2 = k_normalize_exp (Environment.add x tvs tvsenv) f2 in
          KNorm.LetRecSExp (x, tvs, (y, k), f1, f2)
        | FixSExp ((x', y, _, _), k, f1) ->
          assert (x' = x);
          let f1 = k_normalize_exp (Environment.add y [] @@ Environment.add x' [] @@ Environment.add k [] tvsenv) f1 in
          let f2 = k_normalize_exp (Environment.add x tvs tvsenv) f2 in
          KNorm.LetRecSExp (x, tvs, (y, k), f1, f2)
        | FunAExp ((y, _), k, (f1, f1')) ->
          let f1 = k_normalize_exp (Environment.add y [] tvsenv) f1 in
          let f1' = k_normalize_exp (Environment.add y [] @@ Environment.add k [] tvsenv) f1' in
          let f2 = k_normalize_exp (Environment.add x tvs tvsenv) f2 in
          KNorm.LetRecAExp (x, tvs, (y, k), (f1, f1'), f2)
        | FixAExp ((x', y, _, _), k, (f1, f1')) ->
          assert (x' = x);
          let f1 = k_normalize_exp (Environment.add y [] @@ Environment.add x' [] tvsenv) f1 in
          let f1' = k_normalize_exp (Environment.add y [] @@ Environment.add x' [] @@ Environment.add k [] tvsenv) f1' in
          let f2 = k_normalize_exp (Environment.add x tvs tvsenv) f2 in
          KNorm.LetRecAExp (x, tvs, (y, k), (f1, f1'), f2)
        | f ->
          let f1 = k_normalize_exp tvsenv f in
          let f2 = k_normalize_exp (Environment.add x tvs tvsenv) f2 in
          KNorm.LetExp (x, f1, f2)
      end

  let k_normalize_program tvsenv ~static = function
    | Exp f -> let f = k_normalize_exp tvsenv f ~static in KNorm.Exp f, tvsenv
    | LetDecl (x, tvs, f) -> 
      begin match f with
        | FunBExp ((x', _), f) ->
          let f = k_normalize_exp (Environment.add x' [] tvsenv) f ~static in
          KNorm.LetRecBDecl (x, (if static then [] else tvs), x', f), Environment.add x tvs tvsenv
        | FixBExp ((x', y, _, _), f) ->
          assert (x' = x);
          let f = k_normalize_exp (Environment.add y [] (Environment.add x' [] tvsenv)) f ~static in
          KNorm.LetRecBDecl (x, (if static then [] else tvs), y, f), Environment.add x tvs tvsenv
        | FunSExp ((x', _), k, f) ->
          let f = k_normalize_exp (Environment.add x' [] @@ Environment.add k [] tvsenv) f ~static in
          KNorm.LetRecSDecl (x, tvs, (x', k), f), Environment.add x tvs tvsenv
        | FixSExp ((x', y, _, _), k, f) ->
          assert (x' = x);
          let f = k_normalize_exp (Environment.add y [] @@ Environment.add x' [] @@ Environment.add k [] tvsenv) f ~static in
          KNorm.LetRecSDecl (x, tvs, (y, k), f), Environment.add x tvs tvsenv
        | FunAExp ((x', _), k, (f1, f2)) ->
          let f1 = k_normalize_exp (Environment.add x' [] tvsenv) f1 ~static in
          let f2 = k_normalize_exp (Environment.add x' [] @@ Environment.add k [] tvsenv) f2 ~static in
          KNorm.LetRecADecl (x, tvs, (x', k), (f1, f2)), Environment.add x tvs tvsenv
        | FixAExp ((x', y, _, _), k, (f1, f2)) ->
          assert (x' = x);
          let f1 = k_normalize_exp (Environment.add y [] @@ Environment.add x' [] tvsenv) f1 ~static in
          let f2 = k_normalize_exp (Environment.add y [] @@ Environment.add x' [] @@ Environment.add k [] tvsenv) f2 ~static in
          KNorm.LetRecADecl (x, tvs, (y, k), (f1, f2)), Environment.add x tvs tvsenv
        | _ as f ->
          let f = k_normalize_exp tvsenv f ~static in KNorm.LetDecl (x, f), Environment.add x tvs tvsenv
      end
end

module KNorm = struct
  open Syntax.KNorm

  let find x idenv = try Environment.find x idenv with Not_found -> x

  (* beta : let x = y in ... となっているようなxをyに置き換える *)
  let rec beta_exp idenv = function
    | Var x -> Var (find x idenv)
    | IConst _ | Nil as f -> f
    | Add (x, y) -> Add (find x idenv, find y idenv)
    | Sub (x, y) -> Sub (find x idenv, find y idenv)
    | Mul (x, y) -> Mul (find x idenv, find y idenv)
    | Div (x, y) -> Div (find x idenv, find y idenv)
    | Mod (x, y) -> Mod (find x idenv, find y idenv)
    | Cons (x, y) -> Cons (find x idenv, find y idenv)
    | Tuple xs -> Tuple (List.map (fun x -> find x idenv) xs)
    | Hd x -> Hd (find x idenv)
    | Tl x -> Tl (find x idenv)
    | Tget (x, i) -> Tget (find x idenv, i)
    | IfEqExp (x, y, f1, f2) ->
      IfEqExp (find x idenv, find y idenv, beta_exp idenv f1, beta_exp idenv f2)
    | IfLteExp (x, y, f1, f2) ->
      IfLteExp (find x idenv, find y idenv, beta_exp idenv f1, beta_exp idenv f2)
    | MatchExp (x, ms) ->
      let x = find x idenv in
      let ms = List.map (fun (mf, f) -> mf, beta_exp idenv f) ms in
      MatchExp (x, ms)
    | AppDExp (x, (y, z)) -> AppDExp (find x idenv, (find y idenv, find z idenv))
    | AppTy (x, tvs, tas) -> AppTy (find x idenv, tvs, tas)
    | CAppExp (x, y) -> CAppExp (find x idenv, find y idenv)
    | CSeqExp (x, y) -> CSeqExp (find x idenv, find y idenv)
    | CastExp (x, u1, u2, r_p) -> CastExp (find x idenv, u1, u2, r_p)
    | LetExp (x, f1, f2) ->
      let f1 = beta_exp idenv f1 in
      begin match f1 with
        | Var x' -> beta_exp (Environment.add x x' idenv) f2
        | f1 -> LetExp (x, f1, beta_exp idenv f2)
      end
    | LetRecSExp (x, tvs, arg, f1, f2) ->
      LetRecSExp (x, tvs, arg, beta_exp idenv f1, beta_exp idenv f2)
    | CoercionExp _ as f -> f
    | AppMExp (x, y) -> AppMExp (find x idenv, find y idenv)
    | LetRecAExp (x, tvs, arg, (f1, f1'), f2) ->
      LetRecAExp (x, tvs, arg, (beta_exp idenv f1, beta_exp idenv f1'), beta_exp idenv f2)
    | LetRecBExp (x, tvs, arg, f1, f2) ->
      LetRecBExp (x, tvs, arg, beta_exp idenv f1, beta_exp idenv f2)

  let beta_program idenv = function
    | Exp f -> Exp (beta_exp idenv f), idenv
    | LetDecl (x, f) ->
      let f = beta_exp idenv f in
      begin match f with
      | Var x' as f -> Exp f, Environment.add x x' idenv
      | f -> LetDecl (x, f), idenv
      end
    | LetRecSDecl (x, tvs, arg, f) ->
      LetRecSDecl (x, tvs, arg, beta_exp idenv f), idenv
    | LetRecADecl (x, tvs, arg, (f1, f2)) ->
      LetRecADecl (x, tvs, arg, (beta_exp idenv f1, beta_exp idenv f2)), idenv
    | LetRecBDecl (x, tvs, arg, f) ->
      LetRecBDecl (x, tvs, arg, beta_exp idenv f), idenv

  (* assoc : let x = (let y = ... in ... ) in ...というようなネストされたletをlet y = ... in let x = ... in ...という形に平たくする *)
  let rec assoc_exp = function
    | IfEqExp (x, y, f1, f2) -> IfEqExp (x, y, assoc_exp f1, assoc_exp f2)
    | IfLteExp (x, y, f1, f2) -> IfLteExp (x, y, assoc_exp f1, assoc_exp f2)
    | MatchExp (x, ms) -> MatchExp (x, List.map (fun (mf, f) -> mf, assoc_exp f) ms)
    | LetExp (x, f1, f2) ->
      let rec insert = function
        | LetExp (x', f3, f4) -> LetExp (x', f3, insert f4)
        | LetRecSExp (x', tvs, arg, f3, f4) -> LetRecSExp (x', tvs, arg, f3, insert f4)
        | LetRecAExp (x', tvs, arg, (f3, f3'), f4) -> LetRecAExp (x', tvs, arg, (f3, f3'), insert f4)
        | LetRecBExp (x', tvs, arg, f3, f4) -> LetRecBExp (x', tvs, arg, f3, insert f4)
        | f1 -> LetExp (x, f1, assoc_exp f2)
      in insert (assoc_exp f1)
    | LetRecSExp (x, tvs, arg, f1, f2) ->
      LetRecSExp (x, tvs, arg, assoc_exp f1, assoc_exp f2)
    | LetRecAExp (x, tvs, arg, (f1, f1'), f2) ->
      LetRecAExp (x, tvs, arg, (assoc_exp f1, assoc_exp f1'), assoc_exp f2)
    | LetRecBExp (x, tvs, arg, f1, f2) ->
      LetRecBExp (x, tvs, arg, assoc_exp f1, assoc_exp f2)
    | f -> f
  
  let assoc_program = function
    | Exp f -> Exp (assoc_exp f)
    | LetDecl (x, f) -> LetDecl (x, assoc_exp f)
    | LetRecSDecl (x, tvs, arg, f) -> LetRecSDecl (x, tvs, arg, assoc_exp f)
    | LetRecADecl (x, tvs, arg, (f1, f2)) -> LetRecADecl (x, tvs, arg, (assoc_exp f1, assoc_exp f2))
    | LetRecBDecl (x, tvs, arg, f) -> LetRecBDecl (x, tvs, arg, assoc_exp f)
end

let kNorm_funs (tvsenv, alphaenv, betaenv) f = 
  let f, alphaenv = CC.alpha_program alphaenv f in
  let f, tvsenv = CC.k_normalize_program tvsenv f ~static:false in
  let rec iter betaenv f =
    let fbeta, betaenv = KNorm.beta_program betaenv f in
    let fassoc = KNorm.assoc_program fbeta in
    if f = fassoc then f, (tvsenv, alphaenv, betaenv)
    else iter betaenv fassoc
  in let kf, kfunenvs = iter betaenv f in
  kf, kfunenvs

(* let kNorm_funs_LS (tvsenv, alphaenv, betaenv) f = 
  let f, alphaenv = CC.alpha_program alphaenv f in
  let f, tvsenv = CC.k_normalize_program tvsenv f ~static:false in
  let rec iter betaenv f =
    let fbeta, betaenv = KNorm.beta_program betaenv f in
    let fassoc = KNorm.assoc_program fbeta in
    if f = fassoc then f, (tvsenv, alphaenv, betaenv)
    else iter betaenv fassoc
  in let kf, kfunenvs = iter betaenv f in
  kf, kfunenvs *)