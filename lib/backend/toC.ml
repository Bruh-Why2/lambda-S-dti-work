open Syntax
open Syntax.Cls
open Format
open Config
open Utils.Error
open Static_manage

exception ToC_bug of string
exception ToC_error of string

(*main関数かどうかを判定*)
let is_main = ref false

let is_alt = ref false

let is_B = ref false

let is_eager = ref false

let is_static = ref false

(*Utilities*)
(*型のCプログラム表記を出力する関数
  Ground typeとDynamic type以外の型はもともと全てポインタなので&はいらない*)
let c_of_ty = function
  | TyInt -> "&tyint"
  | TyBool -> "&tybool"
  | TyUnit -> "&tyunit"
  | TyDyn -> "&tydyn"
  | TyFun (TyDyn, TyDyn) -> "&tyar"
  | TyFun (_, _) as u -> "&" ^ TyManager.find u
  | TyList TyDyn -> "&tyli"
  | TyList _ as u -> "&" ^ TyManager.find u
  | TyTuple _ as u -> "&" ^ TyManager.find u
  | TyVar (i, { contents = None }) as u ->
    begin try 
      "&" ^ TyManager.find u
    with Not_found ->
      Format.asprintf "_ty%d" i
    end
  | TyVar (i, { contents = Some (TyFun _) }) -> Format.asprintf "_tyfun%d" i
  | TyVar (i, { contents = Some (TyList _) }) -> Format.asprintf "_tylist%d" i
  | TyVar (i, { contents = Some (TyTuple _) }) -> Format.asprintf "_tytuple%d" i
  | TyVar _ -> raise @@ ToC_bug "tyvar should cannot contain other than fun, list or tuple"

(*型引数のCプログラム表記を出力する関数*)
let c_of_tyarg = function
  | Ty u -> c_of_ty u
  | TyNu -> "newty()"

(*自由変数をクロージャに代入するプログラムを記述する関数*)
(*自由変数と型変数を共通のインデックスで管理*)
let cnt_env = ref 0

let toC_v x ppf v =
  fprintf ppf "((fun*)%s)->env[%d] = (void*)%s;"
    x
    !cnt_env
    v;
  cnt_env := !cnt_env + 1

let toC_vs ppf (x, vs) =
  let toC_sep ppf () = fprintf ppf "\n" in
  let toC_list ppf fv = pp_print_list (toC_v x) ppf fv ~pp_sep:toC_sep in
  fprintf ppf "%a"
    toC_list vs

(*型引数を代入するプログラムを記述する関数*)
let toC_ta x ppf u =
  fprintf ppf "((fun*)%s)->env[%d] = (void*)%s;"
    x
    !cnt_env
    (c_of_tyarg u);
  cnt_env := !cnt_env + 1

let toC_tas ppf (y, k, n, x, tas) =
  cnt_env := 0;

  while (!cnt_env < k) do
    fprintf ppf "((fun*)%s)->env[%d] = ((fun*)%s)->env[%d];\n" x !cnt_env y !cnt_env;
    cnt_env := !cnt_env + 1
  done;

  let toC_list ppf ta = pp_print_list (toC_ta x) ppf ta ~pp_sep:(fun ppf () -> fprintf ppf "\n") in
  fprintf ppf "%a\n" 
    toC_list tas;
  
  while (!cnt_env < n) do
    fprintf ppf "((fun*)%s)->env[%d] = ((fun*)%s)->env[%d];\n" x !cnt_env y !cnt_env;
    cnt_env := !cnt_env + 1
  done

(*束縛されていない型引数を代入するプログラムを記述する関数*)
let toC_ftas ppf (offset, x, ftas) =
  cnt_env := !cnt_env + offset;
  if List.length ftas = 0 then fprintf ppf ""
  else let toC_sep ppf () = fprintf ppf "\n" in
  let toC_list ppf fta = pp_print_list (toC_ta x) ppf fta ~pp_sep:toC_sep in
  fprintf ppf "%a\n"
    toC_list ftas

let toC_tag ppf = function
  | I -> pp_print_string ppf "INT"
  | B -> pp_print_string ppf "BOOL"
  | U -> pp_print_string ppf "UNIT"
  | Ar -> pp_print_string ppf "AR"
  | Li -> pp_print_string ppf "LI"
  | Tp _ -> pp_print_string ppf "TP"

let rec toC_crc ppf (c, x) = 
  if CrcManager.mem c then 
    fprintf ppf "%s = (value)&%s;" x (CrcManager.find c)
  else match c with
  | CId -> fprintf ppf "%s = (value)&crc_id;" x
  | CSeqInj (CId, (I | B | U | Ar | Li as t)) ->
    fprintf ppf "%s = (value)&crc_inj_%a;" x toC_tag t
  | CSeqInj (CId, Tp arity) ->
    fprintf ppf "crc %s_temp = {0};\n%s_temp.crckind = SEQ_INJ;\n%s_temp.g_inj = G_TP;\n%s_temp.arity_inj = %d;\n%s_temp.has_tv = 0;\n%s_temp.crcdat.seq_tv.ptr.s = &crc_id;\n%s = (value)alloc_crc(&%s_temp);"
      x x x x arity x x x x
  | CSeqInj (CFun _ as c1, Ar) ->
    fprintf ppf "value %s_cfun;\n%a\ncrc %s_temp = {0};\n%s_temp.crckind = SEQ_INJ;\n%s_temp.g_inj = G_AR;\n%s_temp.has_tv = ((crc*)%s_cfun)->has_tv;\n%s_temp.crcdat.seq_tv.ptr.s = (crc*)%s_cfun;\n%s = (value)alloc_crc(&%s_temp);"
      x toC_crc (c1, x ^ "_cfun") x x x x x x x x x
  | CSeqInj (CList _ as c1, Li) ->
    fprintf ppf "value %s_clist;\n%a\ncrc %s_temp = {0};\n%s_temp.crckind = SEQ_INJ;\n%s_temp.g_inj = G_LI;\n%s_temp.has_tv = ((crc*)%s_clist)->has_tv;\n%s_temp.crcdat.seq_tv.ptr.s = (crc*)%s_clist;\n%s = (value)alloc_crc(&%s_temp);"
      x toC_crc (c1, x ^ "_clist") x x x x x x x x x
  | CSeqInj (CTuple _ as c1, Tp arity) ->
    fprintf ppf "value %s_ctuple;\n%a\ncrc %s_temp = {0};\n%s_temp.crckind = SEQ_INJ;\n%s_temp.g_inj = G_TP;\n%s_temp.arity_inj = %d;\n%s_temp.has_tv = ((crc*)%s_ctuple)->has_tv;\n%s_temp.crcdat.seq_tv.ptr.s = (crc*)%s_ctuple;\n%s = (value)alloc_crc(&%s_temp);"
      x toC_crc (c1, x ^ "_ctuple") x x x x arity x x x x x x
  | CSeqProj ((I | B | U | Ar | Li as t), (r, p), CId) ->
    fprintf ppf "crc %s_temp = {0};\n%s_temp.crckind = SEQ_PROJ;\n%s_temp.g_proj = G_%a;\n%s_temp.p_proj = %d;\n%s_temp.has_tv = 0;\n%s_temp.crcdat.seq_tv.rid_proj = %d;\n%s_temp.crcdat.seq_tv.ptr.s = &crc_id;\n%s = (value)alloc_crc(&%s_temp);"
      x x x toC_tag t x (match p with Pos -> 1 | Neg -> 0) x x r x x x
  | CSeqProj (Tp arity, (r, p), CId) ->
    fprintf ppf "crc %s_temp = {0};\n%s_temp.crckind = SEQ_PROJ;\n%s_temp.g_proj = G_TP;\n%s_temp.arity_proj = %d;\n%s_temp.p_proj = %d;\n%s_temp.has_tv = 0;\n%s_temp.crcdat.seq_tv.rid_proj = %d;\n%s_temp.crcdat.seq_tv.ptr.s = (crc*)&crc_id;\n%s = (value)alloc_crc(&%s_temp);"
      x x x x arity x (match p with Pos -> 1 | Neg -> 0) x x r x x x
  | CSeqProj (Ar, (r, p), (CFun _ as c2)) ->
    fprintf ppf "value %s_cfun;\n%a\ncrc %s_temp = {0};\n%s_temp.crckind = SEQ_PROJ;\n%s_temp.g_proj = G_AR;\n%s_temp.p_proj = %d;\n%s_temp.has_tv = ((crc*)%s_cfun)->has_tv;\n%s_temp.crcdat.seq_tv.rid_proj = %d;\n%s_temp.crcdat.seq_tv.ptr.s = (crc*)%s_cfun;\n%s = (value)alloc_crc(&%s_temp);"
      x toC_crc (c2, x ^ "_cfun") x x x x (match p with Pos -> 1 | Neg -> 0) x x x r x x x x
  | CSeqProj (Li, (r, p), (CList _ as c2)) ->
    fprintf ppf "value %s_clist;\n%a\ncrc %s_temp = {0};\n%s_temp.crckind = SEQ_PROJ;\n%s_temp.g_proj = G_LI;\n%s_temp.p_proj = %d;\n%s_temp.has_tv = ((crc*)%s_clist)->has_tv;\n%s_temp.crcdat.seq_tv.rid_proj = %d;\n%s_temp.crcdat.seq_tv.ptr.s = (crc*)%s_clist;\n%s = (value)alloc_crc(&%s_temp);"
      x toC_crc (c2, x ^ "_clist") x x x x (match p with Pos -> 1 | Neg -> 0) x x x r x x x x
  | CSeqProj (Tp arity, (r, p), (CTuple _ as c2)) ->
    fprintf ppf "value %s_ctuple;\n%a\ncrc %s_temp = {0};\n%s_temp.crckind = SEQ_PROJ;\n%s_temp.g_proj = G_TP;\n%s_temp.arity_proj = %d;\n%s_temp.p_proj = %d;\n%s_temp.has_tv = ((crc*)%s_ctuple)->has_tv;\n%s_temp.crcdat.seq_tv.rid_proj = %d;\n%s_temp.crcdat.seq_tv.ptr.s = (crc*)%s_ctuple;\n%s = (value)alloc_crc(&%s_temp);"
      x toC_crc (c2, x ^ "_ctuple") x x x x arity x (match p with Pos -> 1 | Neg -> 0) x x x r x x x x
  | CTvInj (tv, (r, p)) ->
    fprintf ppf "crc %s_temp = {0};\n%s_temp.crckind = TV_INJ;\n%s_temp.p_inj = %d;\n%s_temp.has_tv = 1;\n%s_temp.crcdat.seq_tv.rid_inj = %d;\n%s_temp.crcdat.seq_tv.ptr.tv = %s;\n%s = (value)alloc_crc(&%s_temp);"
      x x x (match p with Pos -> 1 | Neg -> 0) x x r x (c_of_ty (TyVar tv)) x x
  | CTvProj (tv, (r, p)) ->
    fprintf ppf "crc %s_temp = {0};\n%s_temp.crckind = TV_PROJ;\n%s_temp.p_proj = %d;\n%s_temp.has_tv = 1;\n%s_temp.crcdat.seq_tv.rid_proj = %d;\n%s_temp.crcdat.seq_tv.ptr.tv = %s;\n%s = (value)alloc_crc(&%s_temp);"
      x x x (match p with Pos -> 1 | Neg -> 0) x x r x (c_of_ty (TyVar tv)) x x
  | CFun (c1, c2) ->
    fprintf ppf "value %s_c1;\n%a\nvalue %s_c2;\n%a\ncrc %s_temp = {0};\n%s_temp.crckind = FUN;\n%s_temp.has_tv = ((crc*)%s_c1)->has_tv | ((crc*)%s_c2)->has_tv;\n%s_temp.crcdat.fun_crc.c1 = (crc*)%s_c1;\n%s_temp.crcdat.fun_crc.c2 = (crc*)%s_c2;\n%s = (value)alloc_crc(&%s_temp);"
      x toC_crc (c1, x ^ "_c1") x toC_crc (c2, x ^ "_c2") x x x x x x x x x x x
  | CList c ->
    fprintf ppf "value %s_c;\n%a\ncrc %s_temp = {0};\n%s_temp.crckind = LIST;\n%s_temp.has_tv = ((crc*)%s_c)->has_tv;\n%s_temp.crcdat.lst_crc = (crc*)%s_c;\n%s = (value)alloc_crc(&%s_temp);" 
      x toC_crc (c, x ^ "_c") x x x x x x x x
  | CTuple cs ->
    let arity = List.length cs in
    let toC_sep ppf () = fprintf ppf "\n" in
    let counter = ref 0 in
    let toC_elem ppf c = 
      let i = !counter in
      counter := !counter + 1;
      fprintf ppf "value %s_c%d;\n%a\n%s_crcs[%d] = (crc*)%s_c%d;" x i toC_crc (c, Printf.sprintf "%s_c%d" x i) x i x i
    in
    fprintf ppf "crc **%s_crcs = (crc**)GC_MALLOC(sizeof(crc*) * %d);\n%a\ncrc %s_temp = {0};\n%s_temp.crckind = TUPLE;\n%s_temp.has_tv = 0;\n"
      x arity (pp_print_list toC_elem ~pp_sep:toC_sep) cs x x x;
    for i = 0 to arity - 1 do
       fprintf ppf "%s_temp.has_tv |= ((crc*)%s_c%d)->has_tv;\n" x x i
    done;
    fprintf ppf "%s_temp.crcdat.tpl_crc.arity = %d;\n%s_temp.crcdat.tpl_crc.crcs = %s_crcs;\n%s = (value)alloc_crc(&%s_temp);" x arity x x x x
  | _ -> raise @@ ToC_bug "bad coercion"

(* ======================================== *)
let rec toC_mf ppf (x, mf) = match mf with
  | MatchVar _ | MatchBLit _ | MatchULit -> raise @@ ToC_bug "MatchVar, MatchBLit, MatchULit does not appear in toC"
  | MatchILit i -> 
    fprintf ppf "%s == %d"
      x
      i
  | MatchNil _ -> 
    if !is_eager then
      fprintf ppf "((lst*)%s) == NULL"
        x
    else
      fprintf ppf "is_NULL((lst*)%s)"
        x
  | MatchCons (mf1, mf2) ->
    if !is_eager then
      fprintf ppf "((lst*)%s) != NULL && %a && %a"
        x
        toC_mf (asprintf "((lst*)%s)->h" x, mf1)
        toC_mf (asprintf "((lst*)%s)->t" x, mf2)
    else
      fprintf ppf "!(is_NULL((lst*)%s)) && %a && %a"
        x
        toC_mf (asprintf "hd((lst*)%s)" x, mf1)
        toC_mf (asprintf "tl((lst*)%s)" x, mf2)
  | MatchTuple mfs ->
    let counter = ref (-1) in
    let toC_mfi ppf mi =
      if !is_eager then
        toC_mf ppf (counter := !counter + 1; asprintf "((tpl*)%s)->fields[%d]" x !counter, mi)
      else
        toC_mf ppf (counter := !counter + 1; asprintf "tget((tpl*)%s, %d)" x !counter, mi)
    in
    let toC_sep ppf () = fprintf ppf " && " in
    let toC_list ppf ms = pp_print_list toC_mfi ppf ms ~pp_sep:toC_sep in
    fprintf ppf "%a"
      toC_list mfs
  | MatchWild _ -> 
    fprintf ppf "1"

let rec toC_exp ppf f = match f with
  | Let (x, f1, f2) -> (* 先にxを宣言しておいて，f1の内容をxに代入する *)
    fprintf ppf "value %s;\n%a%a"
      x
      toC_exp (Insert (x, f1))
      toC_exp f2
  | Insert (x, f) -> begin match f with
    | Var y -> 
      fprintf ppf "%s = %s;\n" (* Insert(x, y) ~> x = y; *)
        x
        y
    | Int i -> 
      fprintf ppf "%s = %d;\n" (* Insert(x, i) ~> x.i_b_u = i; *)
        x
        i
    | Nil -> 
      fprintf ppf "%s = 0;\n" (* Insert(x, []) ~> x.l = (lst* )NULL; *)
        x
    | Cons (y, z) -> (* Insert(x, y::z) ~> TODO *)
      fprintf ppf "%s = (value)GC_MALLOC(sizeof(lst));\n((lst*)%s)->h = %s;\n((lst*)%s)->t = %s;\n"
        x
        x
        y
        x
        z
    | Tuple ys ->
      let arity = List.length ys in
      let counter = ref (-1) in
      let toC_sep ppf () = fprintf ppf "\n" in
      let toC_list ppf ys = pp_print_list (fun ppf y -> counter := !counter + 1; fprintf ppf "((tpl_raw*)%s)->fields[%d] = %s;" x !counter y) ppf ys ~pp_sep:toC_sep in
      fprintf ppf "%s = (value)GC_MALLOC(sizeof(tpl_raw) + sizeof(value) * %d);\n((tpl_raw*)%s)->hdr.arity = %d;\n%a\n" x arity x arity toC_list ys;
    | Add (y, z) ->
      fprintf ppf "%s = %s + %s;\n" (* Insert (x, y+z) ~> x.i_b_u = y.i_b_u + z.i_b_u; *)
        x
        y
        z
    | Sub (y, z) ->
      fprintf ppf "%s = %s - %s;\n" (*Addと同じ*)
        x
        y
        z
    | Mul (y, z) ->
      fprintf ppf "%s = %s * %s;\n" (*Addと同じ*)
        x
        y
        z
    | Div (y, z) ->
      fprintf ppf "%s = %s / %s;\n" (*Addと同じ*)
        x
        y
        z
    | Mod (y, z) ->
      fprintf ppf "%s = %s %% %s;\n" (*Addと同じ*)
        x
        y
        z
    | Hd y -> (* TODO *)
      if !is_eager then
        fprintf ppf "%s = ((lst*)%s)->h;\n"
          x
          y
      else
        fprintf ppf "%s = hd((lst*)%s);\n"
          x
          y
    | Tl y -> (* TODO *)
      if !is_eager then
        fprintf ppf "%s = ((lst*)%s)->t;\n"
          x
          y
      else
        fprintf ppf "%s = tl((lst*)%s);\n"
          x
          y
    | Tget (y, i) ->
      if !is_eager then
        fprintf ppf "%s = ((tpl*)%s)->fields[%d];\n"
          x
          y
          i
      else
        fprintf ppf "%s = tget((tpl*)%s, %d);\n"
          x
          y
          i
    | AppDDir (y, (z1, z2)) ->
      fprintf ppf "%s = fun_%s(0, %s, %s);\n" (* Insert(x, y (z1, z2)) ~> x = fun_y(z1, z2); *) (*yが直接適用できる関数の場合*)
        x
        y
        z1
        z2
    | AppDCls (y, (z1, z2)) ->
      fprintf ppf "%s = (((fun*)%s)->funcD)(%s, %s, %s);\n" (* Insert(x, y (z1, z2)) ~> x = appD(y, z1, z2); *) (*yがクロージャを用いて適用する関数の場合*)
        x
        y
        y
        z1
        z2
    | AppMDir (y, z) ->
      fprintf ppf "%s = fun%s_%s(0, %s);\n" (* Insert(x, y z) ~> x = fun_y(z); *) (*yが直接適用できる関数の場合*)
        x
        (if !is_alt then "_alt" else "")
        y
        z
    | AppMCls (y, z) -> 
      fprintf ppf "%s = (((fun*)%s)->funcM)(%s, %s);\n" (* Insert(x, y z) ~> x = appM(y, z); *) (*yがクロージャを用いて適用する関数の場合*)
        x
        y
        y
        z
    | AppTy (y, k, n, tas) ->
      let total_env_size = k + n + List.length tas in
      fprintf ppf "%s = (value)GC_MALLOC(sizeof(fun) + sizeof(void*) * %d);\n*((fun*)%s) = *((fun*)%s);\n%a"
        x
        total_env_size
        x
        y
        toC_tas (y, k, total_env_size, x, tas)
    | Cast (y, u1, u2, (r, p)) -> 
      (*
      Insert(x, y:u1=>^(r, p)u2)
      ~>
      ran_pol x_r_p = { .filename = ~~, .startline = ~~, .startchr = ~~, .endline = ~~, .endchr = ~~, .polarity = ~~};
      x = cast(y, u1, u2, x_p_r);
      *)
      (*filenameやrangeの出力形式はUtilsを参照*)
      (*castの処理にはcast関数を用いる*)
      (*型の出力形式は関数c_of_tyによる TODO *)
      (* 名前の被りを防ぐために，Letとinsertはran_polにyではなくxを使う *)
      let c1, c2 = c_of_ty u1, c_of_ty u2 in
      fprintf ppf "%s = cast(%s, %s, %s, %d, %d);\n"
        x
        y
        c1
        c2
        r
        (match p with Pos -> 1 | Neg -> 0)
    | CApp (y, z) -> (* TODO *)
      if CrcManager.mem_inj z then
        let tag = CrcManager.find_inj z in
        fprintf ppf "#ifdef PROFILE\ncurrent_cast++;\n#endif\n%s = (%s << 3) | G_%a;\n"
          x
          y
          toC_tag tag
      else if CrcManager.mem_proj z then
        let (tag, rid, p) = CrcManager.find_proj z in
        fprintf ppf "#ifdef PROFILE\ncurrent_cast++;\n#endif\nif ((uint8_t)(%s & 0b111) == G_%a) {\n%s = %s >> 3;\n} else {\nblame(%d, %d);\n}"
          y
          toC_tag tag
          x
          y
          rid
          (match p with Pos -> 1 | Neg -> 0)
      else
        fprintf ppf "%s = coerce(%s, (crc*)%s);\n"
          x
          y
          z
    | Coercion c -> (* TODO *)
      fprintf ppf "%a\n"
        toC_crc (c, x)
    | CSeq (y, z) -> 
      fprintf ppf "%s = (value)compose((crc*)%s, (crc*)%s);\n"
        x
        y
        z
    (*以下は内部にexpがあるので，後者のexpまでinsertを送る
      letはf2のみに，ifはf1,f2の両方にinsertを送る*)
    | Let (y, f1, f2) -> toC_exp ppf (Let (y, f1, Insert (x, f2)))
    | IfEq (y, z, f1, f2) -> toC_exp ppf (IfEq (y, z, Insert (x, f1), Insert (x, f2)))
    | IfLte (y, z, f1, f2) -> toC_exp ppf (IfLte (y, z, Insert (x, f1), Insert (x, f2)))
    | Match (y, ms) -> toC_exp ppf (Match (y, List.map (fun (mf, f) -> mf, Insert (x, f)) ms))
    | MakeCls (y, c, tvs, f) -> toC_exp ppf (MakeCls (y, c, tvs, Insert (x, f)))
    | SetTy (tv, f) -> toC_exp ppf (SetTy (tv, Insert (x, f)))
    (*insertはletの一項目には最初の一回しか入らないので，二回insertがかぶさることはない*)
    | Insert _ -> raise @@ ToC_bug "Insert should not be doubled"
    end
  | IfEq (x, y, f1, f2) ->
    (*
    if x = y then f1 else f2
    ~>
    if(x.i_b_u == y.i_b_u) {
      f1
    } else {
      f2
    }
    *)
    (*等価判定はint型を用いて行うので，.i_b_uを取り出す*)
    fprintf ppf "if(%s == %s) {\n%a} else {\n%a}\n"
      x
      y
      toC_exp f1
      toC_exp f2
  | IfLte (x, y, f1, f2) -> (*IfEqと同じ*)
    fprintf ppf "if(%s <= %s) {\n%a} else {\n%a}\n"
      x
      y
      toC_exp f1
      toC_exp f2
  | Match (x, ms) ->
    begin match ms with
    | (mf, f) :: t ->
      fprintf ppf "if(%a) {\n%a} else %a"
        toC_mf (x, mf)
        toC_exp f
        toC_exp (Match (x, t))
    | [] -> 
      fprintf ppf "{\nprintf(\"didn't match\");\nexit(1);\n}\n"
    end
  | MakeCls (x, { entry = l; actual_fv = vs }, { ftvs = ftv; offset = n }, f) -> (*TODO*)
    let env_size = List.length vs + List.length ftv + n in
    cnt_env := 0;
    fprintf ppf "value %s;\n%s = (value)GC_MALLOC(sizeof(fun) + sizeof(void*) * %d);\n%s%a%a%a"
      x
      x
      env_size
      begin if !is_B || !is_static then
        asprintf "((fun*)%s)->funcM = fun_%s;\n" x l
      else if !is_alt then
        asprintf "((fun*)%s)->funcD = fun_%s;\n((fun*)%s)->funcM = fun_alt_%s;\n" x l x l
      else
        asprintf "((fun*)%s)->funcD = fun_%s;\n" x l
      end
      toC_vs (x, vs)
      toC_ftas (n, x, ftv)
      toC_exp f
  | SetTy ((i, { contents = opu }), f) -> begin match opu with (* ここはtoC_tycontentを参照 *)
    | None ->
        fprintf ppf "ty *_ty%d = (ty*)GC_MALLOC(sizeof(ty));\n_ty%d->tykind = TYVAR;\n%a"
          i
          i
          toC_exp f
    | Some (TyFun (u1, u2)) -> 
      fprintf ppf "ty *_tyfun%d = (ty*)GC_MALLOC(sizeof(ty));\n_tyfun%d->tykind = TYFUN;\n_tyfun%d->tydat.tyfun.left = (ty*)GC_MALLOC(sizeof(ty));\n_tyfun%d->tydat.tyfun.right = (ty*)GC_MALLOC(sizeof(ty));\n_tyfun%d->tydat.tyfun.left = %s;\n_tyfun%d->tydat.tyfun.right = %s;\n%a"
        i
        i
        i
        i
        i
        (c_of_ty u1)
        i
        (c_of_ty u2)
        toC_exp f
    | Some (TyList u) -> 
      fprintf ppf "ty *_tylist%d = (ty*)GC_MALLOC(sizeof(ty));\n_tylist%d->tykind = TYLIST;\n_tylist%d->tydat.tylist = (ty*)GC_MALLOC(sizeof(ty));\n_tylist%d->tydat.tylist = %s;\n%a"
        i
        i
        i
        i
        (c_of_ty u)
        toC_exp f
    | Some _ -> raise @@ ToC_bug "not tyfun or tylist is in tyvar option"
    end
  (*以下は項の中にexpを含まないので，main関数かどうかを判定してreturn文を変える必要がある．
    main関数ならreturn 0;でプログラムを終える．main関数でなければ，その値自体をreturnする．*)
  | Var _ | Int _ | Nil | Cons _ | Tuple _ | Add _ | Sub _ | Mul _ | Div _ | Mod _ | Hd _ | Tl _ | Tget _ | AppDDir _ | AppDCls _ | AppMDir _ | AppMCls _ | Cast _ | AppTy _ | CApp _ | Coercion _ | CSeq _ as f ->
    fprintf ppf "value retv;\n%areturn %s;\n"
      toC_exp (Insert ("retv", f))
      (if !is_main then "0" else "retv")

(* =================================== *)

(*型定義をするCプログラムを記述*)
(*ここで行われる型定義は，プログラム全体で共有される型についてのみである*)
(*型名の前方定義
  型はポインタなので，共有して型を扱うには，まず名前を先に定義する必要がある*)
let toC_tydecl ppf (_, name) =
  fprintf ppf "static ty %s;" name

let toC_tydecls ppf l = 
  if List.length l = 0 then fprintf ppf ""
  else let toC_sep ppf () = fprintf ppf "\n" in
  let toC_list ppf decls = pp_print_list toC_tydecl ppf decls ~pp_sep:toC_sep in
  fprintf ppf "%a\n"
    toC_list l

(*型の定義*)
let toC_tycontent ppf (u, name) = match u with
  | TyVar _ -> (* TyVarはtykindをTYVARにする *)
    fprintf ppf "static ty %s = { .tykind = TYVAR };"
      name
  | TyFun (u1, u2) -> 
    (*TyFunはtykindをTYFUNとする
      さらに，leftとrightにTyFunの二つの型をそれぞれ代入する*)
    fprintf ppf "static ty %s = { .tykind = TYFUN, .tydat.tyfun = { .left = %s, .right = %s } };"
      name
      (c_of_ty u1)
      (c_of_ty u2)
  | TyList u ->
    fprintf ppf "static ty %s = { .tykind = TYLIST, .tydat.tylist = %s };"
      name
      (c_of_ty u)
  | TyTuple us ->
    let arity = List.length us in
    let tys_str = String.concat ", " (List.map (fun u -> "(ty*)" ^ c_of_ty u) us) in
    fprintf ppf "static ty *%s_tys[] = { %s };\n" name tys_str;
    fprintf ppf "static ty %s = { .tykind = TYTUPLE, .tydat.tytuple = { .arity = %d, .tys = %s_tys } };"
      name arity name  | u -> raise @@ ToC_bug (Format.asprintf "not tyvar, tyfun or tylist in tycontent: %a" Pp.pp_ty2 u) 

let toC_tycontents ppf l = 
  let toC_sep ppf () = fprintf ppf "\n" in
  let toC_list ppf decls = pp_print_list toC_tycontent ppf decls ~pp_sep:toC_sep in
  fprintf ppf "%a\n"
    toC_list l

(*型定義全体を記述*)
let toC_tys ppf l =
  if l = [] then fprintf ppf ""
  else 
    fprintf ppf "%a%a\n\n"
      toC_tydecls l
      toC_tycontents l

(* ================================ *)

(*関数定義をするCプログラムを記述*)
(*関数定義の最初に，自由変数を詰める場所を設ける*)

(*引数zsから要素を取り出し，変数名xの値に代入*)
let toC_fv ppf x =
  fprintf ppf "value %s = (value)(((fun*)cls)->env[%d]);"
    x
    !cnt_env;
  cnt_env := !cnt_env + 1

let toC_fvs ppf fvl =
  if fvl = [] then fprintf ppf ""
  else let toC_sep ppf () = fprintf ppf "\n" in
  let toC_list ppf fv = pp_print_list toC_fv ppf fv ~pp_sep:toC_sep in
  fprintf ppf "%a\n"
    toC_list fvl

(*関数定義の最初に，型変数を詰める場所も設ける*)

let toC_tv ppf (i, _) = (* TODO *)
  fprintf ppf "ty *_ty%d = (ty*)(((fun*)cls)->env[%d]);"
    i
    !cnt_env;
  cnt_env := !cnt_env + 1

let toC_tvs ppf tvl =
  if tvl = [] then fprintf ppf ""
  else let toC_sep ppf () = fprintf ppf "\n" in
  let toC_list ppf tv = pp_print_list toC_tv ppf tv ~pp_sep:toC_sep in
  fprintf ppf "%a\n"
    toC_list tvl

(* ================================ *)

(*Castのran_polを記述する関数*)
(*toC_exp Let Castを参照*)
let toC_range ppf (r, _) =
  fprintf ppf "{ .filename = %s, .startline = %d, .startchr = %d, .endline = %d, .endchr = %d }"
    (if r.start_p.pos_fname <> "" then "\"File \\\""^r.start_p.pos_fname^"\\\", \"" else "\"\"")
    r.start_p.pos_lnum
    (r.start_p.pos_cnum - r.start_p.pos_bol)
    r.end_p.pos_lnum
    (r.end_p.pos_cnum - r.end_p.pos_bol)

let toC_ranges ppf ranges =
  let toC_sep ppf () = fprintf ppf ",\n" in
  let toC_list ppf range = pp_print_list toC_range ppf range ~pp_sep:toC_sep in
  if List.length ranges = 0 then 
    fprintf ppf ""(*"#ifndef STATIC\nstatic range local_range_list[] = { 0 };\n#endif\n\n"*)
  else
  fprintf ppf "static range local_range_list[] = {\n%a\n};\n\n"
    toC_list (List.sort (fun (_, i1) (_, i2) -> compare i1 i2) ranges)

(* ================================ *)

(*コアーション定義をするCプログラムを記述*)
(*ここで行われるコアーション定義は，プログラム全体で共有されるコアーションについてのみである*)
(*コアーション名の前方定義*)
let toC_crcdecl ppf (_, name) =
  fprintf ppf "static crc %s;" name

let toC_crcdecls ppf l = 
  if List.length l = 0 then fprintf ppf ""
  else let toC_sep ppf () = fprintf ppf "\n" in
  let toC_list ppf decls = pp_print_list toC_crcdecl ppf decls ~pp_sep:toC_sep in
  fprintf ppf "%a\n"
    toC_list l
    
let rec check_has_tv = function
  | CId -> false
  | CSeqInj (c', _) | CSeqProj (_, _, c') | CList c' -> check_has_tv c'
  | CTvInj _ | CTvProj _ -> true
  | CFun (c1, c2) -> (check_has_tv c1) || (check_has_tv c2)
  | CTuple cs -> List.fold_left (fun b c -> b || check_has_tv c) false cs

(* コアーションの定義 *)
let toC_crccontent ppf (c, name) = 
  let has_tv_val = if check_has_tv c then 1 else 0 in
  let c_of_crc c = match c with
  | CId -> "&crc_id"
  | CSeqInj (CId, g) -> Format.asprintf "&crc_inj_%a" toC_tag g
  | _ -> "&" ^ CrcManager.find c 
  in match c with
  | CSeqInj (c', g) ->
    let arity_str = match g with Tp arity -> Format.asprintf ", .arity_inj = %d" arity | _ -> "" in
    fprintf ppf "static crc %s = { .crckind = SEQ_INJ, .g_inj = G_%a%s, .has_tv = %d, .crcdat.seq_tv = { .ptr.s = (crc*)%s } };"
      name
      toC_tag g
      arity_str
      has_tv_val
      (c_of_crc c')
  | CSeqProj (g, (rid, p), c') -> 
    let arity_str = match g with Tp arity -> Format.asprintf ", .arity_proj = %d" arity | _ -> "" in
    fprintf ppf "static crc %s = { .crckind = SEQ_PROJ, .g_proj = G_%a%s, .p_proj = %d,  .has_tv = %d, .crcdat.seq_tv = { .rid_proj = %d, .ptr.s = (crc*)%s } };"
      name
      toC_tag g
      arity_str
      (match p with Pos -> 1 | Neg -> 0)
      has_tv_val
      rid
      (c_of_crc c')
  | CTuple cs ->
    let arity = List.length cs in
    let crcs_str = String.concat ", " (List.map (fun c -> "(crc*)" ^ c_of_crc c) cs) in
    fprintf ppf "static crc *%s_crcs[] = { %s };\n" name crcs_str;
    fprintf ppf "static crc %s = { .crckind = TUPLE, .has_tv = %d, .crcdat.tpl_crc = { .arity = %d, .crcs = %s_crcs } };"
      name has_tv_val arity name
  | CTvInj (tv, (rid, p)) ->
    fprintf ppf "static crc %s = { .crckind = TV_INJ, .p_inj = %d, .has_tv = %d, .crcdat.seq_tv = { .rid_inj = %d, .ptr.tv = %s } };"
      name
      (match p with Pos -> 1 | Neg -> 0)
      has_tv_val
      rid
      (c_of_ty (TyVar tv))
  | CTvProj (tv, (rid, p)) ->
    fprintf ppf "static crc %s = { .crckind = TV_PROJ, .p_proj = %d, .has_tv = %d, .crcdat.seq_tv = { .rid_proj = %d, .ptr.tv = %s } };"
      name
      (match p with Pos -> 1 | Neg -> 0)
      has_tv_val
      rid
      (c_of_ty (TyVar tv))
  | CFun (c1, c2) -> 
    fprintf ppf "static crc %s = { .crckind = FUN, .has_tv = %d, .crcdat.fun_crc = { .c1 = %s, .c2 = %s } };"
      name
      has_tv_val
      (c_of_crc c1)
      (c_of_crc c2)
  | CList c' ->
    fprintf ppf "static crc %s = { .crckind = LIST, .has_tv = %d, .crcdat.lst_crc = %s };"
      name
      has_tv_val
      (c_of_crc c')
  | _ -> raise @@ ToC_bug (Format.asprintf "not in crccontent")

let toC_crccontents ppf l = 
  let toC_sep ppf () = fprintf ppf "\n" in
  let toC_list ppf decls = pp_print_list toC_crccontent ppf decls ~pp_sep:toC_sep in
  fprintf ppf "%a\n"
    toC_list l

(*型定義全体を記述*)
let toC_crcs ppf l =
  let register_builtins ppf () =
    fprintf ppf "\tregister_static_crc(&crc_id);\n";
    fprintf ppf "\tregister_static_crc(&crc_inj_INT);\n";
    fprintf ppf "\tregister_static_crc(&crc_inj_BOOL);\n";
    fprintf ppf "\tregister_static_crc(&crc_inj_UNIT);\n";
    fprintf ppf "\tregister_static_crc(&crc_inj_AR);\n";
    fprintf ppf "\tregister_static_crc(&crc_inj_LI);\n"
  in
  if !is_static then fprintf ppf ""
  else if l = [] then 
    fprintf ppf "\n#ifdef HASH\nstatic void init_crcs() {\n%a}\n#endif\n\n"
      register_builtins ()
  else 
    fprintf ppf "%a%a\n#ifdef HASH\nstatic void init_crcs() {\n%a%a}\n#endif\n\n"
      toC_crcdecls l
      toC_crccontents l
      register_builtins ()
      (fun ppf decls ->
         List.iter (fun (_, name) -> fprintf ppf "\tregister_static_crc(&%s);\n" name) decls
      ) l

(* ================================ *)
  
(*関数名の前方定義
  再帰関数などに対応するために，関数本体の前に，名前を前方定義する
  ここで定義する内容はfun型の関数自体の定義 (*いらない：と，関数が格納されたvalue型の値の二つ*)
  fundef内のfvl(自由変数のリスト)とtvs(型変数のリスト)に要素が入っているかどうかで関数の型が異なるので，四通りの場合分けが発生する*)
let toC_label ppf fundef = match fundef with
| FundefD { name = l; tvs = (_, _); arg = (_, _); formal_fv = _; body = _ } ->
  fprintf ppf "static value fun_%s(value, value, value);"
    l
| FundefM { name = l; tvs = (_, _); arg = _; formal_fv = _; body = _ } ->
  fprintf ppf "static value fun%s_%s(value, value);"
    (if !is_alt then "_alt" else "")
    l

(*関数本体の定義*)
let toC_funv ppf (exists_fun, l) =
  if not exists_fun then
    fprintf ppf ""
  else
    fprintf ppf "value %s = cls;\n" l

let toC_fundef ppf fundef = match fundef with
| FundefD { name = l; tvs = (tvs, _); arg = (x, y); formal_fv = fvl; body = f } ->
  cnt_env := 0;
  fprintf ppf "static value fun_%s(value cls, value %s, value %s) {\n%a%a%a%a}"
    l
    x
    y
    toC_funv (V.mem (to_id l) (fv_exp f), l)
    toC_fvs fvl
    toC_tvs tvs
    toC_exp f
| FundefM { name = l; tvs = (tvs, _); arg = x; formal_fv = fvl; body = f } ->
  cnt_env := 0;
  fprintf ppf "static value fun%s_%s(value cls, value %s) {\n%a%a%a%a}"
    (if !is_alt then "_alt" else "")
    l
    x
    toC_funv (V.mem (to_id l) (fv_exp f), l)
    toC_fvs fvl
    toC_tvs tvs
    toC_exp f
  
(*関数定義全体を記述*)
let toC_fundefs ppf toplevel =
  (if toplevel = [] then pp_print_string ppf ""
  else let toC_sep ppf () = fprintf ppf "\n\n" in
  let toC_list ppf labels = pp_print_list toC_label ppf labels ~pp_sep:toC_sep in
  fprintf ppf "%a\n\n"
    toC_list toplevel;
  let toC_list ppf defs = pp_print_list toC_fundef ppf defs ~pp_sep:toC_sep in
  fprintf ppf "%a\n\n" 
    toC_list toplevel);
  is_main := true (*関数定義が終わったら，main関数に入ることを知らせる*)

(* =================================== *)

(*全体を記述*)
let toC_program ?(bench=0) ~config ppf (Prog (toplevel, f)) = 
  is_main := false;
  is_alt := config.alt;
  is_B := config.intoB;
  is_eager := config.eager;
  is_static := config.static;
  let tys = TyManager.get_definitions () in
  let ranges = RangeManager.get_definitions () in
  let crcs = CrcManager.get_definitions () in
  let init_crcs = if !is_static then "" else "#ifdef HASH\ninit_crcs();\n#endif\n" in
  fprintf ppf "%s\n%s\n%a%a%a%a%s%s%s%a%s"
    (asprintf "#include <gc.h>\n#include \"../%slibC/runtime.h\"\n"
      (if bench = 0 then "" else "../../"))
    (if bench = 0 then "#define GC_INITIAL_HEAP_SIZE 1048576\n" else "")
    toC_tys tys
    toC_ranges ranges
    toC_crcs crcs
    toC_fundefs toplevel
    (if bench = 0 && not !is_static then "range *range_list;\n\n" else "")
    (if bench = 0 then asprintf "int main() {\nGC_INIT();\n%s" init_crcs else asprintf "int mutant%d() {\n%s" bench init_crcs)
    (if List.length ranges != 0 then "range_list = local_range_list;\n" else "")
    toC_exp f
    "}"