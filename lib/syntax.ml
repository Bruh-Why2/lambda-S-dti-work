open Utils.Error

(** Identifier used for names of variables. *)
type id = string

(** Module used to implement environment and type environment. *)
module Environment = Map.Make (
  struct
    type t = id
    let compare (x : id) y = compare x y
  end
  )

module V = struct
  include Set.Make (
    struct
      type t = id
      let compare (a1:id) a2 = compare a1 a2
    end
    )
  let big_union vars = List.fold_right union vars empty
end

type binop = Plus | Minus | Mult | Div | Mod | Eq | Neq | Lt | Lte | Gt | Gte

type ty =
  | TyDyn
  | TyVar of tyvar
  | TyInt
  | TyBool
  | TyUnit
  | TyFun of ty * ty
  | TyList of ty
  | TyTuple of ty list
  (* | TyCoercion of ty * ty *)
and tyvar = int * ty option ref
(* int value is used to identify type variables.
 * ty option ref value is used to implement instantiation.
 * Some u means this variable is instantiated with u. *)
  
type tysc = TyScheme of tyvar list * ty

(* creates monomorphic typescheme *)
let tysc_of_ty u = TyScheme ([], u) 

(** Returns true if the given argument is a ground type. Othewise returns false. *)
let rec is_ground = function
  | TyInt | TyBool | TyUnit -> true (* base type *)
  | TyFun (TyDyn, TyDyn) -> true    (* ★ → ★ *)
  | TyList TyDyn -> true
  | TyTuple us -> List.fold_left (fun b u -> b && u = TyDyn) true us
  | TyVar (_, { contents = Some u }) -> is_ground u
  | _ -> false

let rec is_base_type = function
  | TyBool | TyInt | TyUnit -> true
  | TyVar (_, { contents = Some u }) -> is_base_type u
  | _ -> false

let rec is_consistent u1 u2 = match u1, u2 with
  | TyVar (_, { contents = Some u1 }), u2
  | u1, TyVar (_, { contents = Some u2 }) ->
    is_consistent u1 u2
  | TyBool, TyBool | TyInt, TyInt | TyUnit, TyUnit -> true
  | TyVar (a1, _), TyVar (a2, _) when a1 = a2 -> true
  | TyDyn, _ | _, TyDyn -> true
  | TyFun (u11, u12), TyFun (u21, u22) ->
    (is_consistent u11 u21) && (is_consistent u12 u22)
  | TyList u1, TyList u2 -> is_consistent u1 u2
  | TyTuple us1, TyTuple us2 ->
    begin try
      List.fold_left2 (fun b u1 u2 -> b && is_consistent u1 u2) true us1 us2
    with Invalid_argument _ -> false end
  | _ -> false

let make_dyn_list n =
  let rec iter i r =
    if i = 0 then r
    else iter (i - 1) (TyDyn :: r)
  in iter n []

(* Set of type variables used for let polymorphism *)
(* Module for a set of type variables. *)
module TV = struct
  include Set.Make (
    struct
      type t = tyvar
      let compare (a1, _ : tyvar) (a2, _) = compare a1 a2
    end
    )
  let big_union vars = List.fold_right union vars empty
end

(** Returns a set of free type variables in a given type. *)
let rec ftv_ty: ty -> TV.t = function
  | TyVar (_, { contents = None } as tv) -> TV.singleton tv
  | TyVar (_, { contents = Some u }) -> ftv_ty u
  | TyFun (u1, u2) -> TV.union (ftv_ty u1) (ftv_ty u2)
  | TyList u -> ftv_ty u
  | TyTuple us -> TV.big_union (List.map ftv_ty us)
  | _ -> TV.empty

let ftv_tysc: tysc -> TV.t = function
  | TyScheme (xs, u) -> TV.diff (ftv_ty u) (TV.of_list xs)

let ftv_tyenv (env: tysc Environment.t): TV.t =
  Environment.fold (fun _ us vars -> TV.union vars (ftv_tysc us)) env TV.empty

type tyarg = Ty of ty | TyNu

type matchform = (*match式でmatchさせることのできる形の種類を定義*)
  | MatchVar of id * ty                      (*変数でmatchさせるMatchVar*)
  (* | MatchAsc of matchform * ty *)
  | MatchILit of int                    (*整数とmatchするMatchILit*)
  | MatchBLit of bool                   (*bool値とmatchするMatchBLit*)
  | MatchULit
  | MatchNil of ty                (*空列とmatchするMatchEmptyList*)
  | MatchCons of matchform * matchform  (*リストとmatchするMatchList*)
  | MatchTuple of matchform list
  | MatchWild of ty

let rec fv_matchform = function
  | MatchILit _ | MatchBLit _ | MatchULit | MatchWild _ | MatchNil _ -> V.empty
  | MatchVar (x, _) -> V.singleton x
  | MatchCons (mf1, mf2) -> V.big_union [fv_matchform mf1; fv_matchform mf2]
  | MatchTuple mfs -> V.big_union (List.map fv_matchform mfs)

let rec tv_matchform : matchform -> TV.t = function
  | MatchVar (_, u) -> ftv_ty u
  | MatchILit _ | MatchBLit _ | MatchULit | MatchWild _ -> TV.empty
  | MatchNil u -> ftv_ty u
  (* | MatchAsc (mf, u) -> TV.union (tv_matchform mf) (ftv_ty u) *)
  | MatchCons (mf1, mf2) -> TV.union (tv_matchform mf1) (tv_matchform mf2)
  | MatchTuple mfs -> TV.big_union (List.map tv_matchform mfs)

let rec ftv_matchform : matchform -> TV.t = function
  | MatchVar _ | MatchILit _ | MatchBLit _ | MatchULit | MatchWild _ -> TV.empty
  | MatchNil _ -> TV.empty
  (* | MatchAsc (mf, u) -> TV.union (ftv_matchform mf) (ftv_ty u) *)
  | MatchCons (mf1, mf2) -> TV.union (ftv_matchform mf1) (ftv_matchform mf2)
  | MatchTuple mfs -> TV.big_union (List.map ftv_matchform mfs)

type polarity = Pos | Neg

(** Returns the negation of the given polarity. *)
let neg = function Pos -> Neg | Neg -> Pos

type tag = I | B | U | Ar | Li | Tp of int

let type_of_tag = function
  | I -> TyInt
  | B -> TyBool
  | U -> TyUnit
  | Ar -> TyFun (TyDyn, TyDyn)
  | Li -> TyList TyDyn
  | Tp n -> TyTuple (make_dyn_list n)

let rec tag_of_ty = function
  | TyInt -> I
  | TyBool -> B
  | TyUnit -> U
  | TyFun (TyDyn, TyDyn) -> Ar
  | TyList TyDyn -> Li
  | TyTuple us ->
    if List.fold_left (fun b u -> b && u = TyDyn) true us then Tp (List.length us) else assert false
  | TyVar (_, {contents = Some u}) -> tag_of_ty u
  | _ -> assert false
  (* | _ -> raise @@ Type_bug "tag_of_ty: invalid type" *)

type coercion =
  | CInj of tag
  | CProj of tag * (range * polarity)
  | CTvInj of tyvar * (range * polarity)
  | CTvProj of tyvar * (range * polarity)
  | CTvProjInj of tyvar * (range * polarity) * (range * polarity)
  | CFun of coercion * coercion
  | CList of coercion
  | CTuple of coercion list
  | CId of ty
  | CSeq of coercion * coercion
  | CFail of tag * (range * polarity) * tag

let is_d = function
  | CSeq (CId _, CInj _)
  | CSeq (CFun _, CInj _)
  | CSeq (CList _, CInj _)
  | CSeq (CTuple _, CInj _)
  | CFun _
  | CList _
  | CTuple _ -> true (* TODO : CFun (s, t) when s <> CId _ or t <> CId _ *)
  | _ -> false

let rec ftv_coercion = function
  | CInj _ | CProj _ -> TV.empty
  | CTvInj (tv, _) | CTvProj (tv, _) | CTvProjInj (tv, _, _) -> TV.singleton tv
  | CFun (c1, c2) -> TV.union (ftv_coercion c1) (ftv_coercion c2)
  | CList c -> ftv_coercion c
  | CTuple cs -> TV.big_union (List.map ftv_coercion cs)
  | CId u -> ftv_ty u
  | CSeq (c1, c2) -> TV.union (ftv_coercion c1) (ftv_coercion c2)
  | CFail _ -> TV.empty

exception Blame of range * polarity

(** Syntax of the surface language, the ITGL with extensions. *)
module ITGL = struct
  (* for typing *)
  type constr =
    | CEqual of ty * ty
    | CConsistent of ty * ty

  type exp =
    | Var of range * id * ty list ref
    | IConst of range * int
    | BConst of range * bool
    | UConst of range
    | BinOp of range * binop * exp * exp
    | AscExp of range * exp * ty
    | IfExp of range * exp * exp * exp
    | FunEExp of range * id * ty * exp
    | FunIExp of range * id * ty * exp
    | FixEExp of range * id * id * ty * ty * exp
    | FixIExp of range * id * id * ty * ty * exp
    | AppExp of range * exp * exp
    | MatchExp of range * exp * (matchform * exp) list
    | LetExp of range * id * exp * exp
    | NilExp of range * ty
    | ConsExp of range * exp * exp
    | TupleExp of range * exp list

  let range_of_exp = function
    | Var (r, _, _)
    | IConst (r, _)
    | BConst (r, _)
    | UConst r
    | AscExp (r, _, _)
    | BinOp (r, _, _, _)
    | IfExp (r, _, _, _)
    | FunEExp (r, _, _, _)
    | FunIExp (r, _, _, _)
    | FixEExp (r, _, _, _, _, _)
    | FixIExp (r, _, _, _, _, _)
    | AppExp (r, _, _)
    | MatchExp (r, _, _)
    | LetExp (r, _, _, _) 
    | NilExp (r, _) 
    | ConsExp (r, _, _)
    | TupleExp (r, _) -> r
    
  (* for polymorphic let declaration *)
  let rec tv_exp: exp -> TV.t = function
    | Var _
    | IConst _
    | BConst _
    | UConst _ -> TV.empty
    | BinOp (_, _, e1, e2) -> TV.union (tv_exp e1) (tv_exp e2)
    | AscExp (_, e, u) -> TV.union (tv_exp e) (ftv_ty u)
    | IfExp (_, e1, e2, e3) -> TV.big_union @@ List.map tv_exp [e1; e2; e3]
    | FunEExp (_, _, u, e)
    | FunIExp (_, _, u, e) -> TV.union (ftv_ty u) (tv_exp e)
    | FixEExp (_, _, _, u1, _, e)
    | FixIExp (_, _, _, u1, _, e) -> TV.union (ftv_ty u1) (tv_exp e)
    | AppExp (_, e1, e2) -> TV.union (tv_exp e1) (tv_exp e2)
    | MatchExp (_, e, ms) -> TV.union (tv_exp e) (TV.big_union @@ List.map (fun (mf, e) -> TV.union (tv_matchform mf) (tv_exp e)) ms)
    | LetExp (_, _, e1, e2) -> TV.union (tv_exp e1) (tv_exp e2)
    | NilExp (_, u) -> ftv_ty u
    | ConsExp (_, e1, e2) -> TV.union (tv_exp e1) (tv_exp e2)
    | TupleExp (_, es) -> TV.big_union (List.map tv_exp es)

  let rec ftv_exp: exp -> TV.t = function
    | Var _
    | IConst _
    | BConst _
    | UConst _ -> TV.empty
    | BinOp (_, _, e1, e2) -> TV.union (ftv_exp e1) (ftv_exp e2)
    | AscExp (_, e, u) -> TV.union (ftv_exp e) (ftv_ty u)
    | IfExp (_, e1, e2, e3) -> TV.big_union @@ List.map ftv_exp [e1; e2; e3]
    | FunEExp (_, _, u, e) -> TV.union (ftv_ty u) (ftv_exp e)
    | FunIExp (_, _, _, e) -> ftv_exp e
    | FixEExp (_, _, _, u1, _, e) -> TV.union (ftv_ty u1) (ftv_exp e)
    | FixIExp (_, _, _, _, _, e) -> ftv_exp e
    | AppExp (_, e1, e2) -> TV.union (ftv_exp e1) (ftv_exp e2)
    | MatchExp (_, e, ms) -> TV.union (ftv_exp e) (TV.big_union @@ List.map (fun (mf, e) -> TV.union (ftv_matchform mf) (ftv_exp e)) ms)
    | LetExp (_, _, e1, e2) -> TV.union (ftv_exp e1) (ftv_exp e2)
    | NilExp _ -> TV.empty
    | ConsExp (_, e1, e2) -> TV.union (ftv_exp e1) (ftv_exp e2)
    | TupleExp (_, es) -> TV.big_union (List.map ftv_exp es)

  type program =
    | Exp of exp
    | LetDecl of id * exp
end

(** Syntax of the blame calculus with dynamic type inference. *)
module CC = struct
  type exp =
    | Var of id * tyarg list
    | IConst of int
    | BConst of bool
    | UConst
    | FunBExp of (id * ty) * exp
    | FixBExp of (id * id * ty * ty) * exp
    | FunSExp of (id * ty) * id * exp
    | FixSExp of (id * id * ty * ty) * id * exp
    | FunDualExp of (id * ty) * id * (exp * exp)
    | FixDualExp of (id * id * ty * ty) * id * (exp * exp)
    | CoercionExp of coercion
    | BinOp of binop * exp * exp
    | IfExp of exp * exp * exp
    | AppMExp of exp * exp
    | AppDExp of exp * (exp * exp)
    | LetExp of id * tyvar list * exp * exp
    | NilExp of ty
    | ConsExp of exp * exp
    | MatchExp of exp * (matchform * exp) list
    | TupleExp of exp list
    | CastExp of exp * ty * ty * (range * polarity)
    | CAppExp of exp * exp
    | CSeqExp of exp * exp

  exception Occur_LS1 of string

  (* let rec is_value = function
    | Var _
    | IConst _
    | BConst _
    | UConst
    | FunExp _
    | FixExp _ 
    | NilExp _ -> true
    | CastExp (_, v, TyFun _, TyFun _, _) -> is_value v
    | CastExp (_, v, TyList _, TyList _, _) -> is_value v
    | CastExp (_, v, g, TyDyn, _) -> is_value v && is_ground g
    | ConsExp (v1, v2) -> is_value v1 && is_value v2
    | _ -> false  *)

  let ftv_tyarg = function
    | Ty ty -> ftv_ty ty
    | TyNu -> TV.empty

  let rec ftv_exp: exp -> TV.t = function
    | Var (_, us) -> List.fold_right TV.union (List.map ftv_tyarg us) TV.empty
    | IConst _
    | BConst _
    | UConst -> TV.empty
    | FunBExp ((_, u), e) -> TV.union (ftv_ty u) (ftv_exp e)
    | FixBExp ((_, _, u1, _), f) -> TV.union (ftv_ty u1) (ftv_exp f)
    | FunSExp ((_, u), _, f) -> TV.union (ftv_ty u) (ftv_exp f)
    | FixSExp ((_, _, u1, _), _, f) -> TV.union (ftv_ty u1) (ftv_exp f)
    | FunDualExp ((_, u), _, (f1, f2)) -> TV.union (ftv_ty u) @@ TV.union (ftv_exp f1) (ftv_exp f2)
    | FixDualExp ((_, _, u1, _), _, (f1, f2)) -> TV.union (ftv_ty u1) @@ TV.union (ftv_exp f1) (ftv_exp f2)
    | CoercionExp c -> ftv_coercion c
    | BinOp (_, f1, f2) -> TV.union (ftv_exp f1) (ftv_exp f2)
    | IfExp (f1, f2, f3) ->
      List.fold_right TV.union (List.map ftv_exp [f1; f2; f3]) TV.empty
    | AppMExp (f1, f2) -> TV.union (ftv_exp f1) (ftv_exp f2)
    | AppDExp (f1, (f2, f3)) -> TV.union (ftv_exp f1) (TV.union (ftv_exp f2) (ftv_exp f3))
    | LetExp (_, xs, f1, f2) ->
      TV.union (TV.diff (ftv_exp f1) (TV.of_list xs)) (ftv_exp f2)
    | NilExp _ -> TV.empty
    | ConsExp (f1, f2) -> TV.union (ftv_exp f1) (ftv_exp f2)
    | MatchExp (f, ms) ->
      TV.union (ftv_exp f) (TV.big_union @@ List.map (fun (mf, e) -> TV.union (ftv_matchform mf) (ftv_exp e)) ms)
    | TupleExp es -> TV.big_union (List.map ftv_exp es)
    | CastExp (f, u1, u2, _) -> TV.union (ftv_exp f) @@ TV.union (ftv_ty u1) (ftv_ty u2)
    | CAppExp (f1, f2) -> TV.union (ftv_exp f1) (ftv_exp f2)
    | CSeqExp (f1, f2) -> TV.union (ftv_exp f1) (ftv_exp f2)

  type program =
    | Exp of exp
    | LetDecl of id * tyvar list * exp
  
  type value =
    | IntV of int
    | BoolV of bool
    | UnitV
    | FunBV of ((tyvar list * ty list) -> value -> value)
    | FunSV of ((tyvar list * ty list) -> (value * value) -> value)
    | FunDualV of ((tyvar list * ty list) -> ((value -> value) * ((value * value) -> value)))
    | CoercionV of coercion
    | NilV
    | ConsV of value * value
    | TupleV of value list
    | Tagged of tag * value
    | CoerceV of value * coercion
end

module KNorm = struct
  type exp =
    | Var of id
    | IConst of int
    | Add of id * id
    | Sub of id * id
    | Mul of id * id
    | Div of id * id
    | Mod of id * id
    | Nil
    | Cons of id * id
    | Hd of id
    | Tl of id
    | Tuple of id list
    | Tget of id * int
    | IfEqExp of id * id * exp * exp
    | IfLteExp of id * id * exp * exp
    | AppMExp of id * id
    | AppDExp of id * (id * id)
    | AppTy of id * tyvar list * tyarg list
    | CAppExp of id * id
    | CastExp of id * ty * ty * (range * polarity)
    | CSeqExp of id * id
    | MatchExp of id * (matchform * exp) list
    | CoercionExp of coercion
    | LetExp of id * exp * exp
    | LetRecBExp of id * tyvar list * id * exp * exp
    | LetRecSExp of id * tyvar list * (id * id) * exp * exp
    | LetRecDualExp of id * tyvar list * (id * id) * (exp * exp) * exp

  let rec fv_exp = function
    | Var x | Hd x | Tl x  | Tget (x, _) -> V.singleton x
    | IConst _ | Nil -> V.empty
    | Add (x, y) | Sub (x, y) | Mul (x, y) | Div (x, y) | Mod (x, y) | Cons (x, y) -> V.of_list [x; y]
    | Tuple xs -> V.of_list xs
    | IfEqExp (x, y, f1, f2) | IfLteExp (x, y, f1, f2) -> V.big_union [V.of_list [x; y]; fv_exp f1; fv_exp f2]
    | MatchExp (x, ms) -> 
      V.big_union (V.singleton x :: List.map (fun (mf, f) -> V.union (fv_matchform mf) (fv_exp f)) ms)
    | AppTy (x, _, _) -> V.singleton x
    | AppMExp (x, y) -> V.of_list [x; y]
    | AppDExp (x, (y, z)) -> V.of_list [x; y; z]
    | CastExp (x, _, _, _) -> V.singleton x
    | CAppExp (x, y) -> V.of_list [x; y]
    | CSeqExp (x, y) -> V.of_list [x; y]
    | CoercionExp _ -> V.empty
    | LetExp (x, f1, f2) -> V.union (fv_exp f1) (V.remove x (fv_exp f2))
    | LetRecBExp (x, _, y, f1, f2) -> V.union (V.remove x @@ V.remove y @@ fv_exp f1) (V.remove x @@ fv_exp f2)
    | LetRecSExp (x, _, (y, z), f1, f2) -> V.union (V.remove x @@ V.remove y @@ V.remove z @@ fv_exp f1) (V.remove x @@ fv_exp f2)
    | LetRecDualExp (x, _, (y, z), (f1, _), f2) -> V.union (V.remove x @@ V.remove y @@ V.remove z @@ fv_exp f1) (V.remove x @@ fv_exp f2)

  type program =
    | Exp of exp
    | LetDecl of id * exp
    | LetRecBDecl of id * tyvar list * id * exp
    | LetRecSDecl of id * tyvar list * (id * id) * exp
    | LetRecDualDecl of id * tyvar list * (id * id) * (exp * exp)

  type value =
    | IntV of int
    | NilV
    | ConsV of value * value
    | TupleV of value list
    | Tagged of tag * value
    | CoerceV of value * coercion
    | CoercionV of coercion
    | FunBV of ((tyvar list * ty list) -> value -> value)
    | FunSV of ((tyvar list * ty list) -> (value * value) -> value)
    | FunDualV of ((tyvar list * ty list) -> ((value -> value) * ((value * value) -> value)))
end

module Cls = struct
  type label = string

  let to_label (x:id) = (x:label)

  let to_id (x:label) = (x:id)

  type closure = { entry : label; actual_fv : id list }

  type ftv = { ftvs : tyarg list; offset : int }

  type coercion =
    | CId
    | CSeqInj of coercion * tag
    | CSeqProj of tag * (int * polarity) * coercion
    | CTvInj of tyvar * (int * polarity)
    | CTvProj of tyvar * (int * polarity)
    | CFun of coercion * coercion
    | CList of coercion
    | CTuple of coercion list

  type exp =
    | Var of id
    | Int of int
    | Nil
    | Add of id * id
    | Sub of id * id
    | Mul of id * id
    | Div of id * id
    | Mod of id * id
    | Cons of id * id
    | Tuple of id list
    | Hd of id
    | Tl of id
    | Tget of id * int
    | IfEq of id * id * exp * exp
    | IfLte of id * id * exp * exp
    | Match of id * (matchform * exp) list
    | AppTy of id * int * int * tyarg list
    | AppDCls of id * (id * id)
    | AppDDir of label * (id * id)
    | AppMCls of id * id
    | AppMDir of label * id
    | Cast of id * ty * ty * (int * polarity)
    | CApp of id * id
    | CSeq of id * id
    | Coercion of coercion
    | Let of id * exp * exp
    | MakeCls of id * closure * ftv * exp
    | SetTy of tyvar * exp
    | Insert of id * exp

  type fundef = 
    | FundefD of { name : label ; tvs : tyvar list * int; arg : id * id; formal_fv : id list; body : exp }
    | FundefM of { name : label ; tvs : tyvar list * int; arg : id; formal_fv : id list; body : exp }

  let rec fv_exp = function
    | Var x | Hd x | Tl x | Tget (x, _) -> V.singleton x
    | Int _ | Nil -> V.empty
    | Add (x, y) | Sub (x, y) | Mul (x, y) | Div (x, y) | Mod (x, y) | Cons (x, y) -> V.of_list [x; y]
    | Tuple xs -> V.of_list xs
    | IfEq (x, y, f1, f2) | IfLte (x, y, f1, f2) -> V.big_union [V.of_list [x; y]; fv_exp f1; fv_exp f2]
    | Match (x, ms) -> 
      V.big_union (V.singleton x :: List.map (fun (mf, f) -> V.union (fv_matchform mf) (fv_exp f)) ms)
    | AppTy (x, _, _, _) -> V.singleton x
    | SetTy (_, f) -> fv_exp f
    | AppDDir (_, (y, z)) -> V.of_list [y; z]
    | AppDCls (x, (y, z)) -> V.of_list [x; y; z]
    | AppMDir (_, y) -> V.singleton y
    | AppMCls (x, y) -> V.of_list [x; y]
    | Cast (x, _, _, _) -> V.singleton x
    | CApp (x, y) -> V.of_list [x; y]
    | CSeq (x, y) -> V.of_list [x; y]
    | Coercion _ -> V.empty
    | MakeCls (x, { entry = _; actual_fv = vs }, _, f) -> V.remove x (V.union (V.of_list vs) (fv_exp f))
    | Let (x, c, f) -> V.union (fv_exp c) (V.remove x (fv_exp f))
    | Insert (_, f) -> fv_exp f

  type program = Prog of fundef list * exp

end