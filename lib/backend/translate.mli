open Syntax

exception Translation_bug of string

module ITGL : sig
	open Syntax.ITGL
	val translate : intoB:bool -> tysc Environment.t -> program -> (tysc Environment.t * CC.program * ty)
end

module CC : sig
	open Syntax.CC

	val translate : tysc Environment.t -> program -> program
	val translate_alt : tysc Environment.t -> program -> program
end
