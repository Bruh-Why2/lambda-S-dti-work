open Syntax

(** Type error in the given program. *)
exception Type_error of string
exception Type_bug of string

(** Returns a fresh type variable. *)
val fresh_tyvar : unit -> ty

val type_of_binop : binop -> ty * ty * ty

val is_equal : ty -> ty -> bool

(* [X:->u] *)
type substitution = tyvar * ty
(* if S = [X1:->X2], [X2:->u1], then S(X1)=u1 *)
type substitutions = substitution list
val subst_type : substitutions -> ty -> ty

val tyarg_to_ty : Syntax.tyarg -> ty

val type_of_tag : tag -> ty

val tag_of_ty : ty -> tag

module ITGL : sig
  open Syntax.ITGL

  val is_value : tysc Environment.t -> exp -> bool
  val type_of_program : tysc Environment.t -> program -> (program * ty)

  val closure_tyvars1 : ty -> tysc Environment.t -> exp -> tyvar list

  val normalize : tysc Environment.t -> program -> ty -> (tysc Environment.t * program * ty)
  val normalize_type : ty -> ty
  (* val normalize_coercion : coercion -> coercion *)
end

val type_of_coercion : coercion -> ty * ty

module CC : sig
  open Syntax.CC

  val type_of_program : tysc Environment.t -> program -> ty
end
