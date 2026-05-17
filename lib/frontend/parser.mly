%{
open Syntax
open Syntax.ITGL
open Utils.Error

let tyvenv = ref Environment.empty

(* for function definition *)
let param_to_fun r (x, u) e = match u with
| None -> FunIExp (r, x.value, Typing.fresh_tyvar (), e)
| Some u -> FunEExp (r, x.value, u, e)

(* for recursive function definition *)
let param_to_fun_ty r (x, u1) (e, u) = match u1 with
| None ->
    let u1 = Typing.fresh_tyvar () in
    FunIExp (r, x.value, u1, e), TyFun (u1, u)
| Some u1 ->
    FunEExp (r, x.value, u1, e), TyFun (u1, u)

let opt_ty_to_fresh_ty = function
  | None -> Typing.fresh_tyvar ()
  | Some u -> u

exception Parser_bug of string

%}

%token <Utils.Error.range> LPAREN RPAREN SEMI SEMISEMI COLON EQ QUOTE
%token <Utils.Error.range> PLUS MINUS STAR DIV MOD LT LTE GT GTE NEQ LAND LOR
%token <Utils.Error.range> LET REC IN FUN IF THEN ELSE
%token <Utils.Error.range> INT BOOL UNIT QUESTION RARROW
%token <Utils.Error.range> TRUE FALSE
%token <Utils.Error.range> COLCOL LBRACKET RBRACKET
%token <Utils.Error.range> MATCH WITH VBAR UNDER
%token <Utils.Error.range> COMMA

%token <int Utils.Error.with_range> INTV
%token <Syntax.id Utils.Error.with_range> ID

%start toplevel
%type <Syntax.ITGL.program> toplevel

(* Ref: https://caml.inria.fr/pub/docs/manual-ocaml/expr.html *)
%right SEMI
%right prec_if
%right RARROW
%right LOR
%right LAND
%left  EQ NEQ LT LTE GT GTE
%right COLCOL
%left  PLUS MINUS
%left  STAR DIV MOD

%%

toplevel :
  | p=Program {
      tyvenv := Environment.empty;
      p
    }

Program :
  | Expr SEMISEMI { Exp $1 }
  | start=LET x=ID params=list(Param) u=OptTypeAnnot EQ e=Expr SEMISEMI {
      let r = join_range start (range_of_exp e) in
      let e = match u with None -> e | Some u -> AscExp (range_of_exp e, e, u) in
      let e = List.fold_right (param_to_fun r) params e in
      LetDecl (x.value, e)
    }
  | start=LET REC x=ID params=nonempty_list(Param) u2=OptTypeAnnot EQ e=Expr SEMISEMI {
      let r = join_range start (range_of_exp e) in
      let u2 = opt_ty_to_fresh_ty u2 in
      match params with
      | [] ->
        raise @@ Parser_bug "params must not be empty"
      | (y, None) :: params ->
        let u1 = Typing.fresh_tyvar () in
        let e, u2 = List.fold_right (param_to_fun_ty r) params (e, u2) in
        LetDecl (x.value, FixIExp (r, x.value, y.value, u1, u2, e))
      | (y, Some u1) :: params ->
        let e, u2 = List.fold_right (param_to_fun_ty r) params (e, u2) in
        LetDecl (x.value, FixEExp (r, x.value, y.value, u1, u2, e))
    }

Expr :
  | e=LetExpr { e }
  | e=FunExpr { e }
  | e=MatchExpr { e }
  | SeqExpr { $1 }

Param :
  | x=ID { (x, None) }
  | LPAREN x=ID COLON u=Type RPAREN { (x, Some u) }

%inline OptTypeAnnot :
  | /* empty */ { None }
  | COLON u=Type { Some u }

%inline OptSimpleTypeAnnot :
  | /* empty */ { None }
  | COLON u=SimpleType { Some u }

LetExpr :
  | start=LET x=ID params=list(Param) u1=OptTypeAnnot EQ e1=Expr IN e2=Expr {
      let r = join_range start (range_of_exp e2) in
      let e1 = match u1 with None -> e1 | Some u1 -> AscExp (range_of_exp e1, e1, u1) in
      let e1 = List.fold_right (param_to_fun r) params e1 in
      LetExp (r, x.value, e1, e2)
    }
  | start=LET REC x=ID params=nonempty_list(Param) u2=OptTypeAnnot EQ e1=Expr IN e2=Expr {
      let r = join_range start (range_of_exp e2) in
      let u2 = opt_ty_to_fresh_ty u2 in
      match params with
      | [] ->
        raise @@ Parser_bug "params must not be empty"
      | (y, None) :: params ->
        let u1 = Typing.fresh_tyvar () in
        let e1, u2 = List.fold_right (param_to_fun_ty r) params (e1, u2) in
        LetExp (r, x.value, FixIExp (r, x.value, y.value, u1, u2, e1), e2)
      | (y, Some u1) :: params ->
        let e1, u2 = List.fold_right (param_to_fun_ty r) params (e1, u2) in
        LetExp (r, x.value, FixEExp (r, x.value, y.value, u1, u2, e1), e2)
    }

FunExpr :
  | start=FUN params=nonempty_list(Param) u=OptSimpleTypeAnnot RARROW e=Expr {
      let r = join_range start (range_of_exp e) in
      let e = match u with None -> e | Some u -> AscExp (range_of_exp e, e, u) in
      List.fold_right (param_to_fun r) params e
    }

MatchExpr :
  | start=MATCH e=Expr WITH option(VBAR) ms=MatchCondExpr { 
    let last_exp = snd (List.hd (List.rev ms)) in
    let r = join_range start (range_of_exp last_exp) in
    MatchExp (r, e, ms) 
    }

MatchCondExpr :
  | m=MatchForm RARROW e=Expr { [(m, e)] }
  | m=MatchForm RARROW e=NotMatchExpr VBAR ms=MatchCondExpr { (m, e) :: ms }

MatchForm :
  | m1=LitMatchForm COMMA ms=separated_nonempty_list(COMMA, LitMatchForm) { MatchTuple (m1 :: ms) }
  | m1=MatchForm COLCOL m2=MatchForm { MatchCons (m1, m2) }
  | m=LitMatchForm { m }

LitMatchForm :
  | x=ID { MatchVar (x.value, Typing.fresh_tyvar ()) }
  | i=INTV { MatchILit i.value }
  | TRUE   { MatchBLit true }
  | FALSE  { MatchBLit false }
  | LPAREN RPAREN { MatchULit }
  | LBRACKET ms=separated_list(SEMI, LitMatchForm) RBRACKET {
    let rec makelist l = match l with
      | h :: t -> MatchCons (h, makelist t)
      | [] -> MatchNil (Typing.fresh_tyvar ())
    in makelist ms 
    }
  // | LPAREN m=MatchFormExpr COLON t=Type RPAREN { MatchAsc (m, t) }
  | LPAREN m=MatchForm RPAREN { m }
  | UNDER { MatchWild (Typing.fresh_tyvar ()) }

NotMatchExpr :
  | e=NotMatchLetExpr { e }
  | e=NotMatchFunExpr { e }
  | e=SeqExpr { e }

NotMatchLetExpr :
  | start=LET x=ID params=list(Param) u1=OptTypeAnnot EQ e1=Expr IN e2=NotMatchExpr {
      let r = join_range start (range_of_exp e2) in
      let e1 = match u1 with None -> e1 | Some u1 -> AscExp (range_of_exp e1, e1, u1) in
      let e1 = List.fold_right (param_to_fun r) params e1 in
      LetExp (r, x.value, e1, e2)
    }
  | start=LET REC x=ID params=nonempty_list(Param) u2=OptTypeAnnot EQ e1=Expr IN e2=NotMatchExpr {
      let r = join_range start (range_of_exp e2) in
      let u2 = opt_ty_to_fresh_ty u2 in
      match params with
      | [] ->
        raise @@ Parser_bug "params must not be empty"
      | (y, None) :: params ->
        let u1 = Typing.fresh_tyvar () in
        let e1, u2 = List.fold_right (param_to_fun_ty r) params (e1, u2) in
        LetExp (r, x.value, FixIExp (r, x.value, y.value, u1, u2, e1), e2)
      | (y, Some u1) :: params ->
        let e1, u2 = List.fold_right (param_to_fun_ty r) params (e1, u2) in
        LetExp (r, x.value, FixEExp (r, x.value, y.value, u1, u2, e1), e2)
    }

NotMatchFunExpr :
  | start=FUN params=nonempty_list(Param) u=OptSimpleTypeAnnot RARROW e=NotMatchExpr {
      let r = join_range start (range_of_exp e) in
      let e = match u with None -> e | Some u -> AscExp (range_of_exp e, e, u) in
      List.fold_right (param_to_fun r) params e
    }

SeqExpr :
  | e1=SeqExpr SEMI e2=SeqExpr {
      let r = join_range (range_of_exp e1) (range_of_exp e2) in
      LetExp (r, "_", AscExp (range_of_exp e1, e1, TyUnit), e2)
    }
  | start=IF e1=SeqExpr THEN e2=SeqExpr ELSE e3=SeqExpr %prec prec_if {
      let r = join_range start (range_of_exp e3) in
      IfExp (r, e1, e2, e3)
  }
  | e1=BinOpExpr COMMA es=separated_nonempty_list(COMMA, BinOpExpr) {
      let r = List.fold_left (fun r e -> join_range r (range_of_exp e)) (range_of_exp e1) es in
      TupleExp (r, e1 :: es)
    }
  | e=BinOpExpr { e }
  
BinOpExpr : 
  | e1=BinOpExpr LOR e2=BinOpExpr {
      let r = join_range (range_of_exp e1) (range_of_exp e2) in
      let t, f = BConst (r, true), BConst (r, false) in
      IfExp (r, e1, t, IfExp (r, e2, t, f))
    }
  | e1=BinOpExpr LAND e2=BinOpExpr {
      let r = join_range (range_of_exp e1) (range_of_exp e2) in
      let t, f = BConst (r, true), BConst (r, false) in
      IfExp (r, e1, IfExp (r, e2, t, f), f)
    }
  | e1=BinOpExpr op=Op e2=BinOpExpr {
      BinOp (join_range (range_of_exp e1) (range_of_exp e2), op, e1, e2)
    }
  | e1=BinOpExpr COLCOL e2=BinOpExpr {
      ConsExp (join_range (range_of_exp e1) (range_of_exp e2), e1, e2)
    }
  | UnaryExpr { $1 }

%inline Op :
  | PLUS { Plus }
  | MINUS { Minus }
  | STAR { Mult }
  | DIV { Div }
  | MOD { Mod }
  | EQ { Eq }
  | NEQ { Neq }
  | LT { Lt }
  | LTE { Lte }
  | GT { Gt }
  | GTE { Gte }

UnaryExpr :
  | PLUS e=UnaryExpr { e }
  | start_r=MINUS e=UnaryExpr {
      let r = join_range start_r (range_of_exp e) in
      let zero = IConst (dummy_range, 0) in
      BinOp (r, Minus, zero, e)
    }
  | AppExpr { $1 }

AppExpr :
  | e1=AppExpr e2=SimpleExpr {
      AppExp (join_range (range_of_exp e1) (range_of_exp e2), e1, e2)
    }
  | SimpleExpr { $1 }

SimpleExpr :
  | i=INTV { IConst (i.range, i.value) }
  | r=TRUE { BConst (r, true) }
  | r=FALSE { BConst (r, false) }
  | start=LPAREN last=RPAREN {
      UConst (join_range start last)
    }
  | x=ID { Var (x.range, x.value, ref []) }
  | start=LPAREN e=Expr COLON u=Type last=RPAREN {
      AscExp (join_range start last, e, u)
    }
  | start=LBRACKET l=ListElms last=RBRACKET {
      l (join_range start last) 
    }
  | LPAREN e=Expr RPAREN { e }

ListElms :
  | /* empty */ { fun r -> NilExp(r, Typing.fresh_tyvar ()) }
  | e=BinOpExpr { fun r ->
      ConsExp(range_of_exp e, e, NilExp(r, Typing.fresh_tyvar ()))
    }
  | e=BinOpExpr SEMI l=ListElms { fun r ->
      ConsExp(range_of_exp e, e, l r)
    }

Type :
  | u1=Type RARROW u2=Type { TyFun (u1, u2) }
  | u1=SimpleType STAR us=separated_nonempty_list(STAR, SimpleType) { TyTuple (u1 :: us) }
  | SimpleType { $1 }

SimpleType :
  | INT { TyInt }
  | BOOL { TyBool }
  | UNIT { TyUnit }
  | QUESTION { TyDyn }
  | QUOTE x=ID {
      try
        Environment.find x.value !tyvenv
      with Not_found ->
        let u = Typing.fresh_tyvar () in
        tyvenv := Environment.add x.value u !tyvenv;
        u
    }
  | LBRACKET u=Type RBRACKET { TyList u }
  | LPAREN u=Type RPAREN { u }
