open Format

open Pp
open Syntax

exception Type_error of string

(* Bug in this implementation *)
exception Type_bug of string

let fresh_tyvar =
  let counter = ref 0 in
  let body () =
    let v = !counter in
    counter := v + 1;
    TyVar (!counter, ref None)
  in body

(* for assertion in main and tests *)
let rec is_equal u1 u2 = match u1, u2 with
  | TyVar (_, { contents = Some u1 }), u2
  | u1, TyVar (_, { contents = Some u2 }) -> is_equal u1 u2
  | TyDyn, TyDyn
  | TyBool, TyBool
  | TyInt, TyInt
  | TyUnit, TyUnit -> true
  | TyVar (a1, _), TyVar (a2, _) when a1 = a2 -> true
  | TyFun (u11, u12), TyFun (u21, u22) ->
    (is_equal u11 u21) && (is_equal u12 u22)
  | TyList u1, TyList u2 -> is_equal u1 u2
  | TyTuple us1, TyTuple us2 -> List.fold_left2 (fun b u1 u2 -> b && u1 = u2) true us1 us2
  | _ -> false

let type_of_binop = function
  | Plus | Minus | Mult | Div | Mod -> TyInt, TyInt, TyInt
  | Eq | Neq | Lt | Lte | Gt | Gte -> TyInt, TyInt, TyBool

let type_of_tag = type_of_tag

let tag_of_ty = tag_of_ty

let rec is_static_type = function
  | TyVar (_, { contents = Some u }) -> is_static_type u
  | TyFun (u1, u2) -> (is_static_type u1) && (is_static_type u2)
  | TyDyn -> false
  | TyList u -> is_static_type u
  | TyTuple us -> List.fold_left (fun b u -> b && is_static_type u) true us
  | _ -> true

(* Substitutions for type variables *)

type substitution = tyvar * ty
type substitutions = substitution list

(* S(t) *)
let subst_type (s: substitutions) (u: ty) =
  (* {X':->U'}(U) *)
  let rec subst u ((a', _), u' as s0) = match u with
    | TyFun (u1, u2) -> TyFun (subst u1 s0, subst u2 s0)
    | TyList u -> TyList (subst u s0)
    | TyTuple us -> TyTuple (List.map (fun u -> subst u s0) us)
    | TyVar (a, { contents = None }) when a = a' -> u'
    | TyVar (_, { contents = Some u }) -> subst u s0
    | _ as u -> u
  in
  List.fold_left subst u s

(* When you're sure that this tyarg does not contain ν
 * you can convert it to ty *)
let tyarg_to_ty = function
  | Ty u -> u
  | TyNu -> raise @@ Type_bug "failed to cast tyarg to ty"

module ITGL = struct
  open Pp.ITGL
  open Syntax.ITGL

  (* Unification *)

  let rec unify = function
    (* CConsistent (U, U) *)
    (* When tyvar is already instantiated *)
    | CConsistent (TyVar (_, { contents = Some u1 }), u2)
    | CConsistent (u1, TyVar (_, { contents = Some u2 })) ->
      unify @@ CConsistent (u1, u2)
    (* iota ~ iota *)
    | CConsistent (u1, u2) when u1 = u2 && is_base_type u1 -> ()
    (* X ~ X *)
    | CConsistent (TyVar (a1, {contents = None}), TyVar (a2, {contents = None})) when a1 = a2 -> ()
    (* ? ~ U or U ~ ? *)
    | CConsistent (TyDyn, _) | CConsistent (_, TyDyn) -> ()
    (* U11->U12 ~ U21->U22 *)
    | CConsistent (TyFun (u11, u12), TyFun (u21, u22)) ->
      unify @@ CConsistent (u11, u21);
      unify @@ CConsistent (u12, u22)
    (* U1->U2 ~ X or X ~ U1->U2 *)
    | CConsistent (TyFun (u1, u2), TyVar x) | CConsistent (TyVar x, TyFun (u1, u2)) as c ->
      if TV.mem x (ftv_ty (TyFun (u1, u2))) then raise @@ Type_error (asprintf "cannot solve a constraint because of occurance: %a" pp_constr c)
      else let x1, x2 = fresh_tyvar (), fresh_tyvar () in
      unify @@ CEqual (TyVar x, TyFun (x1, x2));
      unify @@ CConsistent (x1, u1);
      unify @@ CConsistent (x2, u2)
    (* [U1] ~ [U2] *)
    | CConsistent (TyList u1, TyList u2) -> 
      unify @@ CConsistent (u1, u2)
    (* [U] ~ X or X ~ [U] *)
    | CConsistent (TyList u, TyVar x) | CConsistent (TyVar x, TyList u) as c ->
      if TV.mem x (ftv_ty (TyList u)) then raise @@ Type_error (asprintf "cannot solve a constraint because of occurance: %a" pp_constr c)
      else let y = fresh_tyvar () in
      unify @@ CEqual (TyVar x, TyList y);
      unify @@ CConsistent (y, u)
    (* (U11,...,U1n) ~ (U21,...,U2m) *)
    | CConsistent (TyTuple us1, TyTuple us2) as c ->
      begin try 
        List.iter2 (fun u1 u2 -> unify @@ CConsistent (u1, u2)) us1 us2
      with
        Invalid_argument _ -> raise @@ Type_error (asprintf "cannot solve a constraint because of the difference of the tuple length: %a" pp_constr c)
      end
    (* (U1,...,Un) ~ X or X ~ (U1,...,Un) *)
    | CConsistent (TyTuple us, TyVar x) | CConsistent (TyVar x, TyTuple us) as c ->
      if TV.mem x (ftv_ty (TyTuple us)) then raise @@ Type_error (asprintf "cannot solve a constraint because of occurance: %a" pp_constr c)
      else 
        let ys = List.map (fun _ -> fresh_tyvar ()) us in
        unify @@ CEqual (TyVar x, TyTuple ys);
        List.iter2 (fun y u -> unify @@ CConsistent (y, u)) ys us
    (* U ~ X or X ~ U *)
    | CConsistent (u, TyVar x) | CConsistent (TyVar x, u) ->
      unify @@ CEqual (TyVar x, u)
    (* CEqual (T, T) *)
    (* When tyvar is already instantiated *)
    | CEqual (TyVar (_, { contents = Some u1 }), u2)
    | CEqual (u1, TyVar (_, { contents = Some u2 })) ->
      unify @@ CEqual (u1, u2)
    (* CEqual can be used only for static types *)
    | CEqual (u1, u2) as c when not (is_static_type u1 && is_static_type u2) ->
      raise @@ Type_bug (asprintf "invalid constraint: %a" pp_constr c)
    (* iota = iota *)
    | CEqual (TyInt, TyInt) | CEqual (TyBool, TyBool) | CEqual (TyUnit, TyUnit) (*when t1 = t2 && is_base_type t1 *) -> ()
    (* X = X *)
    | CEqual (TyVar (a1, _), TyVar (a2, _)) when a1 = a2 -> ()
    (* T11->T12 = T21->T22 *)
    | CEqual (TyFun (t11, t12), TyFun (t21, t22)) ->
      unify @@ CEqual (t11, t21);
      unify @@ CEqual (t12, t22)
    (* [T1] = [T2] *)
    | CEqual (TyList t1, TyList t2) ->
      unify @@ CEqual (t1, t2)
    (* (U11,...,U1n) = (U21,...,U2n) *)
    | CEqual (TyTuple ts1, TyTuple ts2) as c ->
      begin try 
        List.iter2 (fun t1 t2 -> unify @@ CEqual (t1, t2)) ts1 ts2
      with
        Invalid_argument _ -> raise @@ Type_error (asprintf "cannot solve a constraint because of the difference of the tuple length: %a" pp_constr c)
      end
    (* T = X or X = T *)
    | CEqual (t, TyVar (_, tref as tv)) (*when not (is_tyvar t)*) | CEqual (TyVar (_, tref as tv), t) as c ->
      if TV.mem tv (ftv_ty t) then raise @@ Type_error (asprintf "cannot solve a constraint because of occurance: %a" pp_constr c)
      (* else if not @@ is_static_type t then raise @@ Type_bug "unify: constraint is ill-formed" *)
      else tref := Some t
    | _ as c ->
      raise @@ Type_error (asprintf "cannot solve a constraint: %a" pp_constr c)

  (* Utility functions for let polymorpism *)
  let closure_tyvars1 u1 env v1 =
    TV.elements @@ TV.diff (ftv_ty u1) @@ TV.union (ftv_tyenv env) (ftv_exp v1)

  (** Returns true if a given expression is a "value" under the given environment.
   * The definition of "value" slightly differs that in the paper
   * to allow more type variables are generalized by let. *)
  let rec is_value env e = 
    let rec is_base_value env u e = match e, u with 
      | _, (TyVar _ | TyDyn | TyFun _ | TyList _ | TyTuple _) -> 
        raise @@ Type_bug (asprintf "invalid base value: %a" pp_exp e)
      | Var (_, x, ys), u ->
        begin try
          let TyScheme (xs, u') = Environment.find x env in
          let s = Utils.List.zip xs !ys in
          subst_type s u' = u
        with Not_found ->
          raise @@ Type_bug (asprintf "variable '%s' not found in the environment" x)
        end
      | IConst _, TyInt -> true
      | BConst _, TyBool -> true
      | UConst _, TyUnit -> true
      | AscExp (r, e, TyVar (_, { contents = Some u' })), u ->
        is_base_value env u @@ AscExp (r, e, u')
      | AscExp (_, e, u'), u when u = u' -> is_base_value env u e
      | _ -> false
    in let rec is_fun_value env = function
      | Var (_, x, ys) ->
        begin try
          let TyScheme (xs, u') = Environment.find x env in
          let s = Utils.List.zip xs !ys in
          begin match subst_type s u' with
          | TyFun _ -> true
          | _ -> false
          end
        with Not_found ->
          raise @@ Type_bug (asprintf "variable '%s' not found in the environment" x)
        end
      | FunEExp _
      | FunIExp _
      | FixEExp _
      | FixIExp _ -> true
      | AscExp (_, e, TyFun _) -> is_fun_value env e
      | AscExp (r, e, TyVar (_, { contents = Some u })) -> is_fun_value env @@ AscExp (r, e, u)
      | _ -> false
    in let rec is_list_value env = function
      | Var (_, x, ys) ->  
        begin try
          let TyScheme (xs, u') = Environment.find x env in
          let s = Utils.List.zip xs !ys in
          begin match subst_type s u' with
          | TyList _ -> true
          | _ -> false
          end
        with Not_found ->
          raise @@ Type_bug (asprintf "variable '%s' not found in the environment" x)
        end
      | NilExp _ -> true
      | ConsExp (_, e1, e2) -> is_value env e1 && is_list_value env e2
      | AscExp (_, e, TyList _) -> is_list_value env e
      | AscExp (r, e, TyVar (_, { contents = Some u })) -> is_list_value env @@ AscExp (r, e, u)
      | _ -> false
    in let rec is_tuple_value env = function
      | Var (_, x, ys) ->  
        begin try
          let TyScheme (xs, u') = Environment.find x env in
          let s = Utils.List.zip xs !ys in
          begin match subst_type s u' with
          | TyTuple _ -> true
          | _ -> false
          end
        with Not_found ->
          raise @@ Type_bug (asprintf "variable '%s' not found in the environment" x)
        end
      (* | NilExp _ -> true
      | ConsExp (_, e1, e2) -> is_value env e1 && is_list_value env e2 *)
      | TupleExp (_, es) -> List.fold_left (fun b e -> b && is_value env e) true es
      | AscExp (_, e, TyTuple _) -> is_tuple_value env e
      | AscExp (r, e, TyVar (_, { contents = Some u })) -> is_tuple_value env @@ AscExp (r, e, u)
      | _ -> false
    in let rec is_tyvar_value env a = function
      | Var (_, x, ys) ->
        begin try
          let TyScheme (xs, u') = Environment.find x env in
          let s = Utils.List.zip xs !ys in
          begin match subst_type s u' with
          | TyVar (a', _) when a = a' -> true
          | _ -> false
          end 
        with Not_found ->
          raise @@ Type_bug (asprintf "variable '%s' not found in the environment" x)
        end
      | AscExp (r, e, TyVar (_, { contents = Some u })) ->
          is_tyvar_value env a @@ AscExp (r, e, u)
      | AscExp (_, e, TyVar (a', { contents = None })) when a = a' ->
          is_tyvar_value env a e
      | _ -> false 
    in match e with
    | Var _
    | IConst _
    | BConst _
    | UConst _
    | FunEExp _
    | FunIExp _
    | FixEExp _
    | FixIExp _ 
    | NilExp _ -> true
    | ConsExp (_, e1, e2) -> is_value env e1 && is_list_value env e2
    | TupleExp (_, es) -> List.fold_left (fun b e -> b && is_value env e) true es
    | AscExp (_, e, (TyInt | TyBool | TyUnit as u)) -> is_base_value env u e
    | AscExp (_, e, TyFun _) -> is_fun_value env e
    | AscExp (_, e, TyList _) -> is_list_value env e
    | AscExp (_, e, TyTuple _) -> is_tuple_value env e
    | AscExp (_, e, TyDyn) -> is_value env e
    | AscExp (r, e, TyVar (_, { contents = Some u })) -> is_value env @@ AscExp (r, e, u)
    | AscExp (_, e, TyVar (a, { contents = None })) -> is_tyvar_value env a e
    | _ -> false

  (* Type inference *)

  let rec type_of_meet u1 u2 = match u1, u2 with
    | TyVar (_, { contents = Some u1 }), u2
    | u1, TyVar (_, { contents = Some u2 }) ->
      type_of_meet u1 u2
    | TyBool, TyBool -> TyBool
    | TyInt, TyInt -> TyInt
    | TyUnit, TyUnit -> TyUnit
    | TyDyn, u | u, TyDyn ->
      unify @@ CConsistent (u, TyDyn);
      u
    | TyVar tv, u | u, TyVar tv ->
      unify @@ CConsistent (u, TyVar tv);
      TyVar tv
    | TyFun (u11, u12), TyFun (u21, u22) ->
      let u1 = type_of_meet u11 u21 in
      let u2 = type_of_meet u12 u22 in
      TyFun (u1, u2)
    | TyList u1, TyList u2 ->
      TyList (type_of_meet u1 u2)
    | TyTuple us1, TyTuple us2 ->
      TyTuple (List.map2 (fun u1 u2 -> type_of_meet u1 u2) us1 us2)
    | u1, u2 -> raise @@ Type_error (asprintf "failed to generate constraints: meet(%a, %a)" pp_ty u1 pp_ty u2)

  let rec type_of_mf env mf ids = match mf with
    | MatchILit _ -> (TyInt, env, ids)
    | MatchBLit _ -> (TyBool, env, ids)
    | MatchULit -> (TyUnit, env, ids)
    | MatchVar (id, u) ->
      if List.mem id ids then raise @@ Type_error "match: same var appeared"
      else let env = Environment.add id (tysc_of_ty u) env in
        (u, env, id :: ids)
    | MatchNil u -> (TyList u, env, ids)
    | MatchCons (mf1, mf2) ->
      let u2, env, ids = type_of_mf env mf2 ids in
      let u1, env, ids = type_of_mf env mf1 ids in
      unify @@ CConsistent (TyList u1, u2);
      type_of_meet (TyList u1) u2, env, ids
    | MatchTuple mfs ->
      let rec iter env ids l r = match l with
      | h :: t ->
        let u, env, ids = type_of_mf env h ids in
        iter env ids t (u :: r)
      | [] -> TyTuple (List.rev r), env, ids
      in
      iter env ids mfs []
    (* | MatchAsc (mf, u) ->
      let u', env, ids = type_of_matchform env mf ids in
      unify @@ CConsistent (u', u);
      u, env, ids *)
    | MatchWild u -> u, env, ids

  let rec type_of_exp env = function
    | Var (_, x, ys) ->
      begin try
        let TyScheme (xs, u) = Environment.find x env in
        (* Replace type variables with fresh ones *)
        ys := List.map (fun _ -> fresh_tyvar ()) xs;
        let s = Utils.List.zip xs !ys in
        subst_type s u 
      with Not_found ->
        raise @@ Type_error (asprintf "variable '%s' not found in the environment" x)
      end
    | IConst _ -> TyInt
    | BConst _ -> TyBool
    | UConst _ -> TyUnit
    | BinOp (_, op, e1, e2) ->
      let ui1, ui2, ui = type_of_binop op in
      let u1 = type_of_exp env e1 in
      let u2 = type_of_exp env e2 in
      unify @@ CConsistent (u1, ui1);
      unify @@ CConsistent (u2, ui2);
      ui
    | AscExp (_, e, u1) ->
      let u = type_of_exp env e in
      unify @@ CConsistent (u, u1);
      u1
    | IfExp (_, e1, e2, e3) ->
      let u1 = type_of_exp env e1 in
      let u2 = type_of_exp env e2 in
      let u3 = type_of_exp env e3 in
      unify @@ CConsistent (u1, TyBool);
      type_of_meet u2 u3
    | FunEExp (_, x, u1, e)
    | FunIExp (_, x, u1, e) ->
      let u2 = type_of_exp (Environment.add x (tysc_of_ty u1) env) e in
      TyFun (u1, u2)
    | FixEExp (_, x, y, u1, u2, e)
    | FixIExp (_, x, y, u1, u2, e) ->
      let env = Environment.add x (tysc_of_ty (TyFun (u1, u2))) env in
      let env = Environment.add y (tysc_of_ty u1) env in
      let u2' = type_of_exp env e in
      unify @@ CConsistent (u2, u2');
      TyFun (u1, u2)
    | AppExp (_, e1, e2) ->
      let rec unify_dom_type_of_cod ufun udom = match ufun with
        | TyVar (_, { contents = Some ufun }) -> unify_dom_type_of_cod ufun udom
        | TyVar (_, { contents = None }) ->
          let u1, u2 = fresh_tyvar (), fresh_tyvar () in
          unify @@ CEqual (ufun, (TyFun (u1, u2)));
          unify @@ CConsistent (u1, udom);
          u2
        | TyFun (u1, u2) ->
          unify @@ CConsistent (u1, udom);
          u2
        | TyDyn -> 
          unify @@ CConsistent (TyDyn, udom);
          TyDyn
        | _ as u -> raise @@ Type_error (asprintf "failed to generate constraints: cod(%a)" pp_ty u)
      in let u1 = type_of_exp env e1 in
      let u2 = type_of_exp env e2 in
      unify_dom_type_of_cod u1 u2
    | MatchExp (_, e, ms) ->
      let u_match = type_of_exp env e in
      let u_exp = fresh_tyvar () in
      type_of_ms env ms u_match u_exp;
      u_exp
    | LetExp (r, x, e1, e2) ->
      let u1 = type_of_exp env e1 in
      if is_value env e1 then
        let xs = closure_tyvars1 u1 env e1 in
        let us1 = TyScheme (xs, u1) in
        type_of_exp (Environment.add x us1 env) e2
      else
        type_of_exp env @@ AppExp (r, FunIExp (r, x, u1, e2), e1)
    | NilExp (_, u) -> TyList u
    | ConsExp (_, e1, e2) -> 
      let u2 = type_of_exp env e2 in
      let u1 = type_of_exp env e1 in
      unify @@ CConsistent (TyList u1, u2);
      type_of_meet (TyList u1) u2
    | TupleExp (_, es) ->
      TyTuple (List.map (fun e -> type_of_exp env e) es)
  and type_of_ms env ms u_match u_exp = match ms with
    | (mf, e) :: ms ->
      let u, env', _ = type_of_mf env mf [] in
      unify @@ CConsistent (u_match, u);
      let u_match = type_of_meet u_match u in
      let u = type_of_exp env' e in
      unify @@ CConsistent (u_exp, u);
      let u_exp = type_of_meet u_exp u in
      type_of_ms env ms u_match u_exp
    | [] -> () 

  let type_of_program env = function
    | Exp e ->
      Exp e, type_of_exp env e
    | LetDecl (x, e) ->
      let u = type_of_exp env e in
      LetDecl (x, e), u

  (* Normalize type variables *)

  let rec normalize_type = function
    | TyVar (_, { contents = Some u }) -> normalize_type u
    | TyFun (u1, u2) -> TyFun (normalize_type u1, normalize_type u2)
    | TyList u -> TyList (normalize_type u)
    | TyTuple us -> TyTuple (List.map (fun u -> normalize_type u) us)
    | _ as u -> u

  let normalize_tyenv =
    Environment.map @@ fun (TyScheme (xs, u)) -> TyScheme (xs, normalize_type u)

  let rec normalize_matchform = function
    | MatchILit _ | MatchBLit _ | MatchULit as mf -> mf
    | MatchWild u -> MatchWild (normalize_type u)
    | MatchVar (x, u) -> MatchVar (x, normalize_type u)
    | MatchNil u -> MatchNil (normalize_type u)
    | MatchCons (mf1, mf2) -> MatchCons (normalize_matchform mf1, normalize_matchform mf2)
    | MatchTuple mfs -> MatchTuple (List.map (fun mf -> normalize_matchform mf) mfs)
    (* | MatchAsc (mf, u) -> MatchAsc (normalize_matchform mf, normalize_type u) *)

  let rec normalize_exp = function
    | Var (r, x, ys) -> Var (r, x, ref @@ List.map normalize_type !ys)
    | IConst _
    | BConst _
    | UConst _ as e -> e
    | BinOp (r, op, e1, e2) ->
      BinOp (r, op, normalize_exp e1, normalize_exp e2)
    | AscExp (r, e, u) ->
      AscExp (r, normalize_exp e, normalize_type u)
    | IfExp (r, e1, e2, e3) ->
      IfExp (r, normalize_exp e1, normalize_exp e2, normalize_exp e3)
    | FunEExp (r, x1, u1, e) ->
      FunEExp (r, x1, normalize_type u1, normalize_exp e)
    | FunIExp (r, x1, u1, e) ->
      FunIExp (r, x1, normalize_type u1, normalize_exp e)
    | FixEExp (r, x, y, u1, u2, e) ->
      FixEExp (r, x, y, normalize_type u1, normalize_type u2, normalize_exp e)
    | FixIExp (r, x, y, u1, u2, e) ->
      FixIExp (r, x, y, normalize_type u1, normalize_type u2, normalize_exp e)
    | AppExp (r, e1, e2) ->
      AppExp (r, normalize_exp e1, normalize_exp e2)
    | MatchExp (r, e, ms) ->
      MatchExp (r, normalize_exp e, List.map (fun (mf, e) -> normalize_matchform mf, normalize_exp e) ms)
    | LetExp (r, y, e1, e2) ->
      LetExp (r, y, normalize_exp e1, normalize_exp e2)
    | NilExp (r, u) -> NilExp (r, normalize_type u)
    | ConsExp (r, e1, e2) -> ConsExp (r, normalize_exp e1, normalize_exp e2)
    | TupleExp (r, es) -> TupleExp (r, List.map (fun e -> normalize_exp e) es)

  let normalize_program = function
    | Exp e -> Exp (normalize_exp e)
    | LetDecl (x, e) -> LetDecl (x, normalize_exp e)

  let normalize env p u =
    normalize_tyenv env,
    normalize_program p,
    normalize_type u
end

let rec meet u1 u2 = match u1, u2 with
  | TyVar (_, { contents = Some _ }), _
  | _, TyVar (_, { contents = Some _ }) ->
    raise @@ Type_bug "meet: instantiated tyvar is given"
  | TyBool, TyBool -> TyBool
  | TyInt, TyInt -> TyInt
  | TyUnit, TyUnit -> TyUnit
  | TyVar (a1, _ as tv), TyVar (a2, _) when a1 = a2 -> TyVar tv
  | TyDyn, u | u, TyDyn -> u
  | TyFun (u11, u12), TyFun (u21, u22) -> TyFun (meet u11 u21, meet u12 u22)
  | TyList u1, TyList u2 -> TyList (meet u1 u2)
  | TyTuple us1, TyTuple us2 -> TyTuple (List.map2 (fun u1 u2 -> meet u1 u2) us1 us2)
  | _ ->
    raise @@ Type_bug (asprintf "failed to match: meet(%a, %a)" pp_ty u1 pp_ty u2)

let rec type_of_coercion = function
  | CInj t -> (type_of_tag t, TyDyn)
  | CProj (t, _) -> (TyDyn, type_of_tag t)
  | CTvInj (tv, _) -> (TyVar tv, TyDyn)
  | CTvProj (tv, _) -> (TyDyn, TyVar tv)
  | CTvProjInj _ -> (TyDyn, TyDyn)
  | CFun (c1, c2) -> 
    let (u11, u12) = type_of_coercion c1 in
    let (u21, u22) = type_of_coercion c2 in
    (TyFun (u12, u21), TyFun (u11, u22))
  | CList c ->
    let u1, u2 = type_of_coercion c in
    (TyList u1, TyList u2)
  | CTuple cs ->
    let us1, us2 = List.split (List.map (fun c -> type_of_coercion c) cs) in
    (TyTuple us1, TyTuple us2) 
  | CId u -> (u, u)
  | CSeq (c1, c2) ->
    let (u11, u12) = type_of_coercion c1 in
    let (u21, u22) = type_of_coercion c2 in
    if u12 = u21 then (u11, u22)
    else raise @@ Type_bug (asprintf "type mismatch in coercion sequence: %a, %a" pp_ty u12 pp_ty u21)
  | CFail _ -> assert false (* TODO *)

module CC = struct
  open Syntax.CC

  let rec type_of_matchform env mf = match mf with
    | MatchILit _ -> TyInt, env
    | MatchBLit _ -> TyBool, env
    | MatchULit -> TyUnit, env
    | MatchVar (id, u) ->
      let env = Environment.add id (tysc_of_ty u) env in
      u, env
    | MatchNil u -> TyList u, env
    | MatchCons (mf1, mf2) ->
      let u2, env = type_of_matchform env mf2 in
      let u1, env = type_of_matchform env mf1 in
      meet (TyList u1) u2, env
    | MatchTuple mfs ->
      let rec iter env l r = match l with
      | h :: t ->
        let u, env = type_of_matchform env h in
        iter env t (u :: r)
      | [] -> TyTuple (List.rev r), env
      in
      iter env mfs []
    (* | MatchAsc (mf, u) ->
      let u', env, ids = type_of_matchform env mf ids in
      unify @@ CConsistent (u', u);
      u, env, ids *)
    | MatchWild u -> u, env

  let rec type_of_exp env = function
    | Var (x, ys) -> begin
        try
          let TyScheme (xs, u) = Environment.find x env in
          if List.length xs = List.length ys then
            let ftvs = ftv_ty u in
            let s = Utils.List.zip xs ys in
            let s = List.filter (fun (x, _) -> TV.mem x ftvs) s in
            let s = List.map (fun (x, u) -> x, tyarg_to_ty u) s in
            subst_type s u
          else
            raise @@ Type_bug "invalid type application"
        with Not_found ->
          raise @@ Type_bug "variable not found"
      end
    | IConst _ -> TyInt
    | BConst _ -> TyBool
    | UConst -> TyUnit
    | BinOp (op, f1, f2) ->
      let u1 = type_of_exp env f1 in
      let u2 = type_of_exp env f2 in
      let ui1, ui2, ui = type_of_binop op in
      if (u1, u2) = (ui1, ui2) then
        ui
      else
        raise @@ Type_bug "binop"
    | IfExp (f1, f2, f3) ->
      let u1 = type_of_exp env f1 in
      let u2 = type_of_exp env f2 in
      let u3 = type_of_exp env f3 in
      if u1 = TyBool && u2 = u3 then
        u2
      else
        raise @@ Type_bug "if"
    | FunBExp ((x, u1), f) ->
      let u2 = type_of_exp (Environment.add x (tysc_of_ty u1) env) f in
      TyFun (u1, u2)
    | FixBExp ((x, y, u1, u), f) ->
      let u2 = type_of_exp (Environment.add y (tysc_of_ty u1) (Environment.add x (tysc_of_ty (TyFun (u1, u))) env)) f in
      TyFun (u1, u2)
    | AppMExp (f1, f2) ->
      let u1 = type_of_exp env f1 in
      let u2 = type_of_exp env f2 in
      begin match u1, u2 with
        | TyFun (u11, u12), u2 when u11 = u2 ->
          u12
        | _ -> raise @@ Type_bug (Format.asprintf "app::: u1:%a, u2:%a" Pp.pp_ty u1 Pp.pp_ty u2)
      end
    | CAppExp (f1, CoercionExp c) ->
      let u = type_of_exp env f1 in 
      let (u1, u2) = type_of_coercion c in 
      if u = u1 then
        if is_consistent u1 u2 then
          u2
        else
          raise @@ Type_bug "not consistent"
      else
        raise @@ Type_bug "invalid source type"
    | CAppExp _ -> raise @@ Type_bug "CappExp f2 is not CoercionExp"
    | CastExp (f, TyVar (_, { contents = Some u1 }), u2, r_p)
    | CastExp (f, u1, TyVar (_, { contents = Some u2 }), r_p) ->
      type_of_exp env @@ CastExp (f, u1, u2, r_p)
    | CastExp (f, u1, u2, _) ->
      let u = type_of_exp env f in
      if u = u1 then
        if is_consistent u1 u2 then
          u2
        else
          raise @@ Type_bug "not consistent"
      else
        raise @@ Type_bug "invalid source type"
    | MatchExp (f, ms) ->
      let u_match = type_of_exp env f in 
      let u = type_of_ms env u_match ms in
      u
    | LetExp (x, xs, f1, f2) (*when is_value f1*) ->
      let u1 = type_of_exp env f1 in
      let us1 = TyScheme (xs, u1) in
      let u2 = type_of_exp (Environment.add x us1 env) f2 in
      u2
    (* | LetExp _ ->
      raise @@ Type_bug "invalid translation for let expression" *)
    | NilExp u -> TyList u
    | ConsExp (f1, f2) ->
      let u2 = type_of_exp env f2 in
      let u1 = type_of_exp env f1 in
      if (TyList u1) = u2 then u2
      else raise @@ Type_bug (asprintf "cons: %a=%a" pp_ty (TyList u1) pp_ty u2)
    | TupleExp es -> TyTuple (List.map (fun e -> type_of_exp env e) es)
    | FunSExp _ | FixSExp _ | FunAExp _ | FixAExp _ | CoercionExp _ | AppDExp _ | CSeqExp _ -> raise @@ Occur_LS1 "yet"
  and type_of_ms env u_match = function
    | (mf, f) :: t ->
      let u_match', env' = type_of_matchform env mf in
      if u_match <> u_match' then raise @@ Type_bug ("match u_match")
      else 
        let u_exp' = type_of_exp env' f in
        if t = [] then u_exp'
        else let u_exp = type_of_ms env u_match t in
          if u_exp = u_exp' then u_exp
          else raise @@ Type_bug ("match u_exp")
    | [] -> raise @@ Type_bug ("match empty")

  let type_of_program env = function
    | Exp e -> type_of_exp env e
    | LetDecl (_, _, f) -> type_of_exp env f
end
