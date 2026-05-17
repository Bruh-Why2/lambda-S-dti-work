open Syntax

exception Eval_bug of string

val compose : ?debug:bool -> coercion -> coercion -> coercion

val tag_of_ty : ty -> tag

module CC : sig
  open Syntax.CC
  
  val eval_program : ?debug:bool -> (tyvar list * value) Environment.t -> program -> (tyvar list * value) Environment.t * id * value
  
  val coerce : ?debug:bool -> value -> coercion -> value
end 

module KNorm : sig
  open Syntax.KNorm

  val eval_program : ?debug:bool -> value Environment.t -> program -> value Environment.t * id * value
  
  val coerce : ?debug:bool -> value -> coercion -> value
end

