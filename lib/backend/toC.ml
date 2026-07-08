open Syntax
open Syntax.Cls
open Format
open Config
open Utils.Error
open Static_manage
open Llvm
open Llvm_target
open Llvm_all_backends

exception ToLLVM_error of string
exception ToLLVM_bug of string
exception ToC_bug of string
exception ToC_error of string


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

let toC_tas ppf (y, num_zs, total, x, tas) =
  cnt_env := 0;

  (* yに登録されている自由変数をxにコピー *)
  while (!cnt_env < num_zs) do
    fprintf ppf "((fun*)%s)->env[%d] = ((fun*)%s)->env[%d];\n" x !cnt_env y !cnt_env;
    cnt_env := !cnt_env + 1
  done;

  (* 今回適用する型引数を代入 *)
  let toC_list ppf ta = pp_print_list (toC_ta x) ppf ta ~pp_sep:(fun ppf () -> fprintf ppf "\n") in
  fprintf ppf "%a\n" 
    toC_list tas;
  
  (* yに登録されている外側の型引数をxにコピー *)
  while (!cnt_env < total) do
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
let rec toC_mf ppf (x, mf) ~config =
  let toC_mf = toC_mf ~config in
  match mf with
  | MatchVar _ | MatchBLit _ | MatchULit -> raise @@ ToC_bug "MatchVar, MatchBLit, MatchULit does not appear in toC"
  | MatchILit i -> 
    fprintf ppf "%s == %d"
      x
      i
  | MatchNil _ -> 
    if config.eager then
      fprintf ppf "((lst*)%s) == NULL"
        x
    else
      fprintf ppf "is_NULL((lst*)%s)"
        x
  | MatchCons (mf1, mf2) ->
    if config.eager then
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
      if config.eager then
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

let rec toC_exp ppf f ~config ~is_main = 
  let toC_exp = toC_exp ~config ~is_main in
  match f with
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
      if config.eager then
        fprintf ppf "%s = ((lst*)%s)->h;\n"
          x
          y
      else
        fprintf ppf "%s = hd((lst*)%s);\n"
          x
          y
    | Tl y -> (* TODO *)
      if config.eager then
        fprintf ppf "%s = ((lst*)%s)->t;\n"
          x
          y
      else
        fprintf ppf "%s = tl((lst*)%s);\n"
          x
          y
    | Tget (y, i) ->
      if config.eager then
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
        (if config.alt then "_alt" else "")
        y
        z
    | AppMCls (y, z) -> 
      fprintf ppf "%s = (((fun*)%s)->funcM)(%s, %s);\n" (* Insert(x, y z) ~> x = appM(y, z); *) (*yがクロージャを用いて適用する関数の場合*)
        x
        y
        y
        z
    | AppTy (y, zs_len, outer_tvs_len, tas) ->
      let total_env_size = zs_len + List.length tas + outer_tvs_len in
      fprintf ppf "%s = (value)GC_MALLOC(sizeof(fun) + sizeof(void*) * %d);\n*((fun*)%s) = *((fun*)%s);\n%a"
        x
        total_env_size
        x
        y
        toC_tas (y, zs_len, total_env_size, x, tas)
    | AppTyFun (y, zs_len, outer_tvs_len, tas) ->
      let total_env_size = zs_len + List.length tas + outer_tvs_len in
      fprintf ppf "%s = (value)GC_MALLOC(sizeof(fun) + sizeof(void*) * %d);\n*((fun*)%s) = *((fun*)%s);\n%a%s = tfun_%s(%s, 0);\n"
        x
        total_env_size
        x
        y
        toC_tas (y, zs_len, total_env_size, x, tas)
        x
        y
        x
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
    | MakeTyCls (y, c, tvs, f) -> toC_exp ppf (MakeTyCls (y, c, tvs, Insert (x, f)))
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
        (toC_mf ~config) (x, mf)
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
      begin if config.intoB || config.static then
        asprintf "((fun*)%s)->funcM = fun_%s;\n" x l
      else if config.alt then
        asprintf "((fun*)%s)->funcD = fun_%s;\n((fun*)%s)->funcM = fun_alt_%s;\n" x l x l
      else
        asprintf "((fun*)%s)->funcD = fun_%s;\n" x l
      end
      toC_vs (x, vs)
      toC_ftas (n, x, ftv)
      toC_exp f
  | MakeTyCls (x, { entry = l; actual_fv = vs }, { ftvs = ftv; offset = n }, f) -> (*TODO*)
    let env_size = List.length vs + List.length ftv + n in
    cnt_env := 0;
    fprintf ppf "value %s;\n%s = (value)GC_MALLOC(sizeof(fun) + sizeof(void*) * %d);\n%s%a%a%a"
      x
      x
      env_size
      (asprintf "((fun*)%s)->funcM = tfun_%s;\n" x l)
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
  | Var _ | Int _ | Nil | Cons _ | Tuple _ | Add _ | Sub _ | Mul _ | Div _ | Mod _ | Hd _ | Tl _ | Tget _ | AppDDir _ | AppDCls _ | AppMDir _ | AppMCls _ | Cast _ | AppTy _ | AppTyFun _ | CApp _ | Coercion _ | CSeq _ as f ->
    fprintf ppf "value retv;\n%areturn %s;\n"
      toC_exp (Insert ("retv", f))
      (if is_main then "0" else "retv")

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
let toC_crcs ppf l ~config =
  let register_builtins ppf () =
    fprintf ppf "\tregister_static_crc(&crc_id);\n";
    fprintf ppf "\tregister_static_crc(&crc_inj_INT);\n";
    fprintf ppf "\tregister_static_crc(&crc_inj_BOOL);\n";
    fprintf ppf "\tregister_static_crc(&crc_inj_UNIT);\n";
    fprintf ppf "\tregister_static_crc(&crc_inj_AR);\n";
    fprintf ppf "\tregister_static_crc(&crc_inj_LI);\n"
  in
  if config.static then fprintf ppf ""
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
let toC_label ppf fundef ~config = match fundef with
| FundefD { name = l; tvs = (_, _); arg = (_, _); formal_fv = _; body = _ } ->
  fprintf ppf "static value fun_%s(value, value, value);"
    l
| FundefM { name = l; tvs = (_, _); arg = _; formal_fv = _; body = _ } ->
  fprintf ppf "static value fun%s_%s(value, value);"
    (if config.alt then "_alt" else "")
    l
| FundefTy { name = l; tvs = (_, _); formal_fv = _; body = _ } ->
  fprintf ppf "static value tfun_%s(value, value);"
    l

(*関数本体の定義*)
let toC_funv ppf (exists_fun, l) =
  if not exists_fun then
    fprintf ppf ""
  else
    fprintf ppf "value %s = cls;\n" l

let toC_fundef ppf fundef ~config = match fundef with
| FundefD { name = l; tvs = (tvs, _); arg = (x, y); formal_fv = fvl; body = f } ->
  cnt_env := 0;
  fprintf ppf "static value fun_%s(value cls, value %s, value %s) {\n%a%a%a%a}"
    l
    x
    y
    toC_funv (V.mem (to_id l) (fv_exp f), l)
    toC_fvs fvl
    toC_tvs tvs
    (toC_exp ~config ~is_main:false) f
| FundefM { name = l; tvs = (tvs, _); arg = x; formal_fv = fvl; body = f } ->
  cnt_env := 0;
  fprintf ppf "static value fun%s_%s(value cls, value %s) {\n%a%a%a%a}"
    (if config.alt then "_alt" else "")
    l
    x
    toC_funv (V.mem (to_id l) (fv_exp f), l)
    toC_fvs fvl
    toC_tvs tvs
    (toC_exp ~config ~is_main:false) f
| FundefTy { name = l; tvs = (tvs, _); formal_fv = fvl; body = f } ->
  cnt_env := 0;
  fprintf ppf "static value tfun_%s(value cls, value dummy) {\n%a%a%a%a}"
    l
    toC_funv (V.mem (to_id l) (fv_exp f), l)
    toC_fvs fvl
    toC_tvs tvs
    (toC_exp ~config ~is_main:false) f
  
(*関数定義全体を記述*)
let toC_fundefs ppf toplevel ~config =
  if toplevel = [] then pp_print_string ppf ""
  else let toC_sep ppf () = fprintf ppf "\n\n" in
  let toC_list ppf labels = pp_print_list (toC_label ~config) ppf labels ~pp_sep:toC_sep in
  fprintf ppf "%a\n\n"
    toC_list toplevel;
  let toC_list ppf defs = pp_print_list (toC_fundef ~config) ppf defs ~pp_sep:toC_sep in
  fprintf ppf "%a\n\n" 
    toC_list toplevel

(* =================================== *)
(* To LLVM *)
let context = global_context()
let the_module = create_module context "main"
let builder = builder context

let () =
  initialize ();
  let target_triple = Target.default_triple () in
  let target = Target.by_triple target_triple in
  let target_machine =
    TargetMachine.create ~triple:target_triple target
  in
  let data_layout = TargetMachine.data_layout target_machine in
  set_data_layout (DataLayout.as_string data_layout) the_module;
  set_target_triple target_triple the_module

let int_t = i64_type context
let bool_t = i1_type context
let ptr_t = pointer_type context
let uint8_t = i8_type context
let uint16_t = i16_type context
let uint32_t = i32_type context
let void_t = void_type context
let size_t = i64_type context
let value_t = i64_type context (* Value is intptr_t but gonna work with i64 for now*)
(*have to declare external struct types just like functions, especially lst and tpl, working with ptr for now?*)

(*lst_t, tpl_t, fn_t, crc_t(0?) definition have to be done*)
let lst_t =
  let t = named_struct_type context "lst" in
  struct_set_body t [| value_t; value_t |] false;
  t
  (*more complex definitions possible*)

let fun_t =
  let t = named_struct_type context "fun" in
  struct_set_body t [|ptr_t; ptr_t|] false;
  t

let tpl_t =
  let t = named_struct_type context "tpl" in
  struct_set_body t [| uint16_t |] false;
  t

let ty_t =
  let t = named_struct_type context "ty" in
  struct_set_body t [|
    uint8_t;(* tykind enum, uint8_t *)
    ptr_t;(* first word of union — covers tv, tylist *)
    ptr_t;(* second word — covers tyfun.right, or padding *)
  |] false;
  t
(* Assuming 'ground_ty' is an 8-bit type based on the "header: 6byte" comment, 
   but you can adjust this if it's actually an i32 or something else. *)
let crc_t =
  let t = named_struct_type context "struct.crc" in
  let crckind_ty = uint8_t in
  let bitfields_ty = uint8_t in 
  
  let g_proj_ty = uint8_t in (* Adjust if ground_ty is not uint8_t *)
  let g_inj_ty  = uint8_t in
  let arity_proj_ty = uint16_t in
  let arity_inj_ty  = uint16_t in
  let crcdat_payload_ty = array_type int_t 2 in
  struct_set_body t [|
    crckind_ty;       
    bitfields_ty;     
    g_proj_ty;          
    g_inj_ty;           
    arity_proj_ty;     
    arity_inj_ty;      
    crcdat_payload_ty  
  |] false; 
  t
let range_t =
  let t = named_struct_type context "range" in
  struct_set_body t [|
    ptr_t;                  (* filename: char* *)
    i32_type context;       (* startline *)
    i32_type context;       (* startchr *)
    i32_type context;       (* endline *)
    i32_type context;       (* endchr *)
  |] false;
  t

let declare_ty_globals () =
  ignore (declare_global ty_t "tydyn"  the_module);
  ignore (declare_global ty_t "tyint"  the_module);
  ignore (declare_global ty_t "tybool" the_module);
  ignore (declare_global ty_t "tyunit" the_module);
  ignore (declare_global ty_t "tyar"   the_module);
  ignore (declare_global ty_t "tyli"   the_module)

let declare_crc_globals () =
  ignore (declare_global crc_t "crc_id" the_module);
  ignore (declare_global crc_t "crc_inj_INT" the_module);
  ignore (declare_global crc_t "crc_inj_BOOL" the_module);
  ignore (declare_global crc_t "crc_inj_UNIT" the_module);
  ignore (declare_global crc_t "crc_inj_AR" the_module);
  ignore (declare_global crc_t "crc_inj_LI" the_module)

let declare_external name ret_ty param_tys =
  let fn_t = function_type ret_ty param_tys in
  declare_function name fn_t the_module
(* Check if call_function is correct? *)
let call_function name fn_t args result_name =
  let fn = match lookup_function name the_module with
    | Some f -> f
    | None -> dump_module the_module;
    raise @@ ToLLVM_error ("undeclared function: " ^ name)
  in
  Printf.eprintf "call_function1\n%!";
  (* let fn_t = function_type (return_type (element_type (type_of fn))) (Array.map type_of args) in *)
  build_call fn_t fn args result_name builder
let runtime () =
    ignore (declare_external "is_NULL" (bool_t) [|ptr_t|]);
    ignore (declare_external "hd" (value_t) [|ptr_t|]);
    ignore (declare_external "tl" (value_t) [|ptr_t|]);
    ignore (declare_external "tget" (value_t) [| ptr_t; uint16_t|]);
    ignore (declare_external "GC_malloc" (ptr_t) [|size_t|]);
    ignore (declare_external "compose" (ptr_t) [|ptr_t; ptr_t|]);(* crc* -> crc* -> crc* *)
    ignore (declare_external "newty" (ptr_t) [||]); (* ty* *)
    ignore (declare_external "cast" (value_t) [|value_t; ptr_t; ptr_t; uint32_t; uint8_t|]);
    ignore (declare_external "coerce" (value_t) [|value_t; ptr_t|]); (*value -> crc* -> value*)
    ignore (declare_external "blame" (void_t) [|uint32_t; uint8_t|]);
    ignore (declare_external "GC_init" void_t [||]);
    ignore (declare_external "register_static_crc" void_t [|ptr_t|]);
    (* Stdlib - Gotta make the _alt and _cast versions too,
    just doing the normal ones for now  *)
    ignore (declare_external "fun_print_int" value_t [|value_t; value_t; value_t|]);
    ignore (declare_external "fun_print_bool" value_t [|value_t; value_t; value_t|]);
    ignore (declare_external "fun_print_newline" value_t [|value_t; value_t; value_t|]);
    ignore (declare_external "fun_read_int" value_t [|value_t; value_t; value_t|]);
    ignore (declare_external "fun_ignore" value_t [|value_t; value_t; value_t|]);
    ignore (declare_external "fun_abs_ml" value_t [|value_t; value_t; value_t|]);
    ignore (declare_external "fun_max" value_t [|value_t; value_t; value_t|]);
    ignore (declare_external "fun_max_x" value_t [|value_t; value_t; value_t|]);
    ignore (declare_external "fun_min" value_t [|value_t; value_t; value_t|]);
    ignore (declare_external "fun_min_x" value_t [|value_t; value_t; value_t|]);
    ignore (declare_external "fun_prec" value_t [|value_t; value_t; value_t|]);
    ignore (declare_external "fun_succ" value_t [|value_t; value_t; value_t|]);
    ignore (declare_external "fun_not_ml" value_t [|value_t; value_t; value_t|])

let load_val ptr = build_load value_t ptr "load_val" builder (*can give naming later*)
let load_var named_values x = match Hashtbl.find_opt named_values x with
  | Some ptr -> load_val ptr
  | None -> dump_module the_module;
    raise (ToLLVM_bug ("Unbound variable: " ^ x))

let load_ptr ptr = build_load ptr_t ptr "ptr" builder 
(* let load_lst x = build_inttoptr (x) (ptr_t) "lst_ptr" builder (**)
let load_tpl x = build_inttoptr (x) (ptr_t) "tpl_ptr" builder *)
let load_lst x = build_inttoptr (x) (ptr_t) "lst_ptr" builder
let load_tpl x = build_inttoptr (x) (ptr_t) "tpl_ptr" builder
let load_fn x = build_inttoptr (x) (ptr_t) "fn_ptr" builder
let load_crc x = build_inttoptr (x) (ptr_t) "crc_ptr" builder
let load_ty x = build_inttoptr (x) (ptr_t) "crc_ptr" builder
(* Really confused on how to handle ptrs and variables, and values *)
(* load_var -> finds the variable and then loads its value as integer *)
(* load_ptr -> doesn't find the variable loads its value as ptr *)
(* load_lst, load_tpl, load_fn -> takes a value as integer and casts it to value as ptr *)
(* different type of ptrs like lst pointers, tpl pointers which have use different definitions for *)


(* Have to see correctness of this *)
let llvm_of_ty named_values = function
  | TyInt  ->
    (match lookup_global "tyint" the_module with
     | Some g -> g
     | None -> raise @@ ToLLVM_bug "tyint not declared")
  | TyBool ->
    (match lookup_global "tybool" the_module with
     | Some g -> g
     | None -> failwith "tybool not declared")

  | TyUnit ->
    (match lookup_global "tyunit" the_module with
     | Some g -> g
     | None -> failwith "tyunit not declared")

  | TyDyn  ->
    (match lookup_global "tydyn" the_module with
     | Some g -> g
     | None -> failwith "tydyn not declared")

  | TyFun (TyDyn, TyDyn) ->
    (match lookup_global "tyar" the_module with
     | Some g -> g
     | None -> failwith "tyar not declared")

  | TyFun (_, _) as u ->
    let name = TyManager.find u in
    (match lookup_global name the_module with
     | Some g -> g
     | None -> failwith (name ^ " not declared"))

  | TyList TyDyn ->
    (match lookup_global "tyli" the_module with
     | Some g -> g
     | None -> failwith "tyli not declared")

  | TyList _ as u ->
    let name = TyManager.find u in
    (match lookup_global name the_module with
     | Some g -> g
     | None -> failwith (name ^ " not declared"))

  | TyTuple _ as u ->
    let name = TyManager.find u in
    (match lookup_global name the_module with
     | Some g -> g
     | None -> failwith (name ^ " not declared"))

  | TyVar (i, { contents = None }) as u ->
    (try
       let name = TyManager.find u in
       (match lookup_global name the_module with
        | Some g -> g
        | None -> failwith (name ^ " not declared"))
     with Not_found ->
       let name = Printf.sprintf "_ty%d" i in
       (match Hashtbl.find_opt named_values name with
        | Some ptr -> ptr
        | None -> dump_module the_module; 
          raise (ToLLVM_bug ("unbound type variable: " ^ name))))

  | TyVar (i, { contents = Some (TyFun _) }) ->
    let name = Printf.sprintf "_tyfun%d" i in
    (match Hashtbl.find_opt named_values name with
     | Some ptr -> ptr
     | None -> dump_module the_module; 
      raise (ToLLVM_bug ("unbound type variable: " ^ name)))

  | TyVar (i, { contents = Some (TyList _) }) ->
    let name = Printf.sprintf "_tylist%d" i in
    (match Hashtbl.find_opt named_values name with
     | Some ptr -> ptr
     | None -> dump_module the_module; 
      raise (ToLLVM_bug ("unbound type variable: " ^ name)))

  | TyVar (i, { contents = Some (TyTuple _) }) ->
    let name = Printf.sprintf "_tytuple%d" i in
    (match Hashtbl.find_opt named_values name with
     | Some ptr -> ptr
     | None -> dump_module the_module; 
      raise (ToLLVM_bug ("unbound type variable: " ^ name)))

  | TyVar _ -> dump_module the_module; 
    raise (ToLLVM_bug "tyvar should cannot contain other than fun, list or tuple")
(*型引数のCプログラム表記を出力する関数*)
let llvm_of_ty_static = function
  | TyInt  ->
    (match lookup_global "tyint" the_module with
     | Some g -> g
     | None -> failwith "tyint not declared")

  | TyBool ->
    (match lookup_global "tybool" the_module with
     | Some g -> g
     | None -> failwith "tybool not declared")

  | TyUnit ->
    (match lookup_global "tyunit" the_module with
     | Some g -> g
     | None -> failwith "tyunit not declared")

  | TyDyn  ->
    (match lookup_global "tydyn" the_module with
     | Some g -> g
     | None -> failwith "tydyn not declared")

  | TyFun (TyDyn, TyDyn) ->
    (match lookup_global "tyar" the_module with
     | Some g -> g
     | None -> failwith "tyar not declared")

  | TyFun (_, _) as u ->
    let name = TyManager.find u in
    (match lookup_global name the_module with
     | Some g -> g
     | None -> failwith (name ^ " not declared"))

  | TyList TyDyn ->
    (match lookup_global "tyli" the_module with
     | Some g -> g
     | None -> failwith "tyli not declared")

  | TyList _ as u ->
    let name = TyManager.find u in
    (match lookup_global name the_module with
     | Some g -> g
     | None -> failwith (name ^ " not declared"))

  | TyTuple _ as u ->
    let name = TyManager.find u in
    (match lookup_global name the_module with
     | Some g -> g
     | None -> failwith (name ^ " not declared"))
  | TyVar _ -> dump_module the_module; 
    raise (ToLLVM_bug "static version")
let llvm_of_tyarg named_values = function
  | Ty u -> llvm_of_ty named_values u
  | TyNu -> 
    let fn_t = function_type ptr_t [||] in 
    call_function "newty" fn_t [||] "newty()"

let cnt_env_llvm = ref 0
let toLLVM_v named_values x v =
  let idx = !cnt_env_llvm in
  cnt_env_llvm := !cnt_env_llvm + 1;
  let fun_x = load_fn (load_var named_values x) in
  let hdr_size = build_ptrtoint (size_of fun_t) int_t "hdr_size" builder in
  let fun_int = build_ptrtoint fun_x int_t "fun_int" builder in
  let slot_offset = const_int int_t (idx * 8) in
  let addr = build_add fun_int (build_add hdr_size slot_offset "off" builder) "addr" builder in
  let elem_ptr = build_inttoptr addr ptr_t "elem_ptr" builder in
  let v_val = load_var named_values v in 
  ignore(build_store v_val elem_ptr builder)

let toLLVM_vs named_values (x, vs) = List.iter (toLLVM_v named_values x) vs

let toLLVM_ta named_values fun_x u =
  let idx = !cnt_env_llvm in
  cnt_env_llvm := !cnt_env_llvm + 1;
  let hdr_size = build_ptrtoint (size_of fun_t) int_t "hdr_size" builder in
  let fun_int = build_ptrtoint fun_x int_t "fun_int" builder in
  let slot_offset = const_int int_t (idx * 8) in
  let addr = build_add fun_int (build_add hdr_size slot_offset "off" builder) "addr" builder in
  let elem_ptr = build_inttoptr addr ptr_t "elem_ptr" builder in
  let u_val = llvm_of_tyarg named_values u in 
  ignore(build_store u_val elem_ptr builder)

let toLLVM_tas named_values (y, num_zs, total, fun_x, tas) =
  cnt_env_llvm := 0;
  let fun_y = load_fn(load_var named_values y) in
  (* yに登録されている自由変数をxにコピー *)
  while (!cnt_env_llvm < num_zs) do
    let idx = !cnt_env_llvm in
    cnt_env_llvm := !cnt_env_llvm + 1;
    let hdr_size = build_ptrtoint (size_of fun_t) int_t "hdr_size" builder in
    let fun_int = build_ptrtoint fun_x int_t "fun_int" builder in
    let slot_offset = const_int int_t (idx * 8) in
    let addr = build_add fun_int (build_add hdr_size slot_offset "off" builder) "addr" builder in
    let elem_ptr = build_inttoptr addr ptr_t "elem_ptr" builder in
    let hdr_size = build_ptrtoint (size_of fun_t) int_t "hdr_size" builder in
    let fun_int = build_ptrtoint fun_y int_t "fun_int" builder in
    let slot_offset = const_int int_t (idx * 8) in
    let addr = build_add fun_int (build_add hdr_size slot_offset "off" builder) "addr" builder in
    let str_ptr = build_inttoptr addr ptr_t "elem_ptr" builder in
    ignore(build_store str_ptr elem_ptr builder)
  done;
  (* 今回適用する型引数を代入 *)
  List.iter (toLLVM_ta named_values fun_x) tas;
  (* yに登録されている外側の型引数をxにコピー *)
  while (!cnt_env_llvm < total) do
    let idx = !cnt_env_llvm in
    cnt_env_llvm := !cnt_env_llvm + 1;
    let hdr_size = build_ptrtoint (size_of fun_t) int_t "hdr_size" builder in
    let fun_int = build_ptrtoint fun_x int_t "fun_int" builder in
    let slot_offset = const_int int_t (idx * 8) in
    let addr = build_add fun_int (build_add hdr_size slot_offset "off" builder) "addr" builder in
    let elem_ptr = build_inttoptr addr ptr_t "elem_ptr" builder in
    let hdr_size = build_ptrtoint (size_of fun_t) int_t "hdr_size" builder in
    let fun_int = build_ptrtoint fun_y int_t "fun_int" builder in
    let slot_offset = const_int int_t (idx * 8) in
    let addr = build_add fun_int (build_add hdr_size slot_offset "off" builder) "addr" builder in
    let str_ptr = build_inttoptr addr ptr_t "elem_ptr" builder in
    ignore(build_store str_ptr elem_ptr builder)
  done

(*束縛されていない型引数を代入するプログラムを記述する関数*)

let toLLVM_ftas named_values (offset, fun_x, ftas) =
  cnt_env_llvm := !cnt_env_llvm + offset;
  List.iter (toLLVM_ta named_values fun_x) ftas

let rec toLLVM_mf (x, mf) ~config=
  let toLLVM_mf = toLLVM_mf ~config in
  match mf with
  | MatchVar _ | MatchBLit _ | MatchULit -> raise @@ ToLLVM_bug "MatchVar, MatchBLit, MatchULit does not appear in toLLVM"
  | MatchILit i -> 
    build_icmp Icmp.Eq (x) (const_int int_t i) "comp" builder
  | MatchNil _ -> 
    let lst = load_lst x in
    if config.eager then
      build_is_null (lst) "cond_is_null" builder
    else
      let fn_t = function_type bool_t [|ptr_t|] in
      call_function "is_NULL" fn_t [|lst|] "cond_is_NULL"
  | MatchCons (mf1, mf2) ->
    let lst = load_lst x in
    if config.eager then begin
      let cond1 = build_is_not_null (lst) "cond1_is_null" builder in
      let hd_ptr = build_struct_gep lst_t (lst) 0 "hd_ptr" builder in
      let lst_hd = load_val hd_ptr in
      let tl_ptr = build_struct_gep lst_t (lst) 1 "tl_ptr" builder in
      let lst_tl = load_val tl_ptr in 
      let cond2 = build_and (toLLVM_mf(lst_hd, mf1)) (toLLVM_mf (lst_tl, mf2)) "cond2_and" builder in
      build_and cond1 cond2 "cond" builder
    end
    else begin
      let lst = load_lst x in
      let fn_t = function_type bool_t [|ptr_t|] in
      let cond1 = build_not (call_function "is_NULL" fn_t [|lst|] "is_NULL") "cond1_not_is_NULL" builder in
      let fn_t = function_type value_t [|ptr_t|] in
      let lst_hd = call_function "hd" fn_t[|lst|] "lst_hd" in
      let fn_t = function_type value_t [|ptr_t|] in
      let lst_tl = call_function "tl" fn_t [|lst|] "lst_tl" in
      let cond2 = build_and (toLLVM_mf (lst_hd, mf1)) (toLLVM_mf (lst_tl, mf2)) "cond2_and" builder in
      build_and cond1 cond2 "cond" builder
    end
  | MatchTuple mfs -> 
    let counter = ref (-1) in 
    let rec toLLVM_mfi mi = 
      match mi with 
      | [] -> const_int bool_t 1 (* can maybe do without this? using List.iter?*)
      | mf :: rest ->
        let tpl = load_tpl x in
        if config.eager then begin
          counter := !counter + 1;
          let idx = !counter in
          let fld_ptr = build_struct_gep tpl_t (tpl) idx "fld_ptr" builder in
          let tpl_fld = load_val fld_ptr in
          let cond1 = toLLVM_mf (tpl_fld, mf) in
          let cond2 = toLLVM_mfi rest in
          build_and cond1 cond2 "cond" builder
        end
        else begin
          counter := !counter + 1;
          let idx = const_int uint16_t !counter in
          let fn_t = function_type value_t [| ptr_t; uint16_t|] in
          let cond1 = call_function "tget" fn_t [|tpl ; idx|] "cond1_tget" in
          let cond2 = toLLVM_mfi rest in
          build_and cond1 cond2 "cond" builder
        end in
      toLLVM_mfi mfs
  | MatchWild _ -> const_int bool_t 1

let toLLVM_tag = function
  | I    -> const_int int_t 1
  | B    -> const_int int_t 2
  | U    -> const_int int_t 3
  | Ar   -> const_int int_t 4
  | Li   -> const_int int_t 5
  | Tp _ -> const_int int_t 6

let toLLVM_tykind = function
	| "DYN"         -> const_int int_t 0
	|	"BASE_INT"    -> const_int int_t 1
	|	"BASE_BOOL"   -> const_int int_t 2
	|	"BASE_UNIT"   -> const_int int_t 3
	|	"TYFUN"       -> const_int int_t 4
	|	"TYLIST"      -> const_int int_t 5
	|	"TYTUPLE"     -> const_int int_t 6
	|	"TYVAR"       -> const_int int_t 7
	|	"SUBSTITUTED" -> const_int int_t 8
  | _ -> raise @@ ToLLVM_error "Not a tykind"  

let toLLVM_crc c = 
  (* if CrcManager.mem c then 
    fprintf ppf "%s = (value)&%s;" x (CrcManager.find c)
else*)match c with 
  | CId -> 
    (match lookup_global "crc_id" the_module with
     | Some g -> g
     | None -> failwith "crc_id not declared")
    (* "%s = (value)&crc_id;"  *)
  (* | CSeqInj (CId, (I | B | U | Ar | Li as t)) ->
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
    fprintf ppf "%s_temp.crcdat.tpl_crc.arity = %d;\n%s_temp.crcdat.tpl_crc.crcs = %s_crcs;\n%s = (value)alloc_crc(&%s_temp);" x arity x x x x *)
  | _ -> raise @@ ToLLVM_bug "bad coercion"

let rec toLLVM_exp named_values (f) ~config = 
  let toLLVM_exp = toLLVM_exp named_values ~config in
  let load_var = load_var named_values in
  match f with
  | Let (x, f1, f2) -> 
    Printf.eprintf "Let\n%!";
    let ptr = build_alloca int_t x builder in
      ignore(build_store (toLLVM_exp(f1)) ptr builder);
    Hashtbl.add named_values x ptr;
    toLLVM_exp f2
  | Insert (x, f) -> 
    Printf.eprintf "Insert\n%!";
    let ptr = build_alloca int_t x builder in
      ignore(build_store (toLLVM_exp(f)) ptr builder);
    Hashtbl.add named_values x ptr;
    build_load int_t ptr x builder
  | Add (x, y) -> Printf.eprintf "Add\n%!"; build_add  (load_var x) (load_var y) "add_int" builder
  | Sub (x, y) -> Printf.eprintf "Sub\n%!"; build_sub  (load_var x) (load_var y) "sub_int" builder
  | Mul (x, y) -> Printf.eprintf "Mul\n%!"; build_mul  (load_var x) (load_var y) "mul_int" builder
  | Div (x, y) -> Printf.eprintf "Div\n%!"; build_sdiv (load_var x) (load_var y) "div_int" builder
  | Mod (x, y) -> Printf.eprintf "Mod\n%!"; build_srem (load_var x) (load_var y) "mod_int" builder
  | IfEq (x , y, f1, f2) -> 
    Printf.eprintf "IfEq\n%!";
    let cond = build_icmp Icmp.Eq  (load_var x) (load_var y) "cmp_eq"  builder in
    if_else named_values cond f1 f2 ~config
  | IfLte (x , y, f1, f2) -> 
    Printf.eprintf "IfLte\n%!";
    let cond = build_icmp Icmp.Sle (load_var x) (load_var y) "cmp_sle" builder in
    if_else named_values cond f1 f2 ~config
  | Match (x, ms) -> 
    Printf.eprintf "Match\n%!";
    begin match ms with
    | (mf, f) :: t -> 
      let cond = toLLVM_mf ((load_var x) , mf) ~config in
      if_else named_values cond f (Match (x,t)) ~config
    | [] -> raise @@ ToLLVM_bug "Didn't match"
    end
  | Var x -> Printf.eprintf "Var\n%!"; (load_var x)
  | Int i -> Printf.eprintf "Int\n%!"; const_int int_t i
  | Nil -> Printf.eprintf "Nil\n%!"; const_int int_t 0
  | Cons (x, y) -> 
    Printf.eprintf "Cons\n%!";
    let arg = build_ptrtoint (size_of lst_t) int_t "size" builder in
    let args = [|arg|] in
    let fn_t = function_type (ptr_t) [|size_t|] in
    let lst = call_function "GC_malloc" fn_t args "lst_alloc" in
    let hd_ptr = build_struct_gep lst_t (lst) 0 "hd_ptr" builder in
    let hd_elem = load_var x in
    ignore(build_store (hd_elem) hd_ptr builder);
    let tl_ptr = build_struct_gep lst_t (lst) 1 "tl_ptr" builder in
    let tl_elem = load_var y in
    ignore(build_store (tl_elem) tl_ptr builder);
    build_ptrtoint lst value_t "cast_value" builder
  | Tuple ys -> 
    Printf.eprintf "Tuple\n%!";
    let arity = List.length ys in
    let counter = ref (-1) in
    cnt_env_llvm := 0;
    let hdr_size = build_ptrtoint (size_of tpl_t) int_t "hdr_size" builder in
    let val_size = build_ptrtoint (size_of value_t) int_t "val_size" builder in
    let n_env = const_int int_t arity in
    let env_bytes = build_mul val_size n_env "env_bytes" builder in
    let arg = build_add hdr_size env_bytes "total_size" builder in
    let args = [|arg|] in
    let fn_t = function_type (ptr_t) [|size_t|] in
    let tpl_x = call_function "GC_malloc" fn_t args "fun_alloc" in
    let arity_ptr = build_struct_gep tpl_t tpl_x 0 "arity_ptr" builder in
    ignore (build_store (const_int uint16_t arity) arity_ptr builder);
    let toLLVM_iter y =
      counter := !counter + 1;
      let idx = !counter in
      (* fields start after the header — use pointer arithmetic *)
      let hdr_size_val = build_ptrtoint (size_of tpl_t) int_t "hdr_size" builder in
      let tpl_int      = build_ptrtoint tpl_x int_t "tpl_int" builder in
      let slot_offset  = const_int int_t (idx * 8) in
      let addr         = build_add tpl_int (build_add hdr_size_val slot_offset "off" builder) "addr" builder in
      let field_ptr    = build_inttoptr addr ptr_t "field_ptr" builder in
      ignore (build_store (load_var y) field_ptr builder)
    in
    let toLLVM_list ys = List.iter toLLVM_iter ys in
    toLLVM_list ys;
    tpl_x
  | Hd x -> 
    Printf.eprintf "Hd\n%!";
    let lst_ptr = load_lst(load_var x) in
    if config.eager then
      let hd_ptr = build_struct_gep lst_t (lst_ptr) 0 "hd_ptr" builder in
      load_val hd_ptr
    else
      let fn_t = function_type value_t [|ptr_t|] in
      call_function "hd" fn_t [|lst_ptr|] "lst_hd"
  | Tl x -> 
    Printf.eprintf "Tl\n%!";
    let lst_ptr = load_lst(load_var x) in
    if config.eager then
      let tl_ptr = build_struct_gep lst_t (lst_ptr) 1 "tl_ptr" builder in
      load_val tl_ptr
    else
      let fn_t = function_type value_t [|ptr_t|] in
      call_function "tl" fn_t [|lst_ptr|] "lst_tl"
  | Tget (x,i) -> 
    Printf.eprintf "Tget\n%!";
    let tpl_ptr = load_var x in
    if config.eager then begin
          let fld_ptr = build_struct_gep tpl_t (load_tpl tpl_ptr) i "fld_ptr" builder in
          load_val fld_ptr
        end
        else begin
          let idx = const_int uint16_t i in
          let fn_t = function_type value_t [| ptr_t; uint16_t|] in
          call_function "tget" fn_t [|load_tpl tpl_ptr ; idx|] "tpl_fld"
        end
  | AppDDir (x , (y1, y2)) -> 
    Printf.eprintf "AppDDir %s %s %s \n%!" x y1 y2;
    let args = [|const_int int_t 0; load_var y1; load_var y2|] in
    let fn_t = function_type value_t [| value_t; value_t; value_t|] in
    call_function ("fun_" ^ x) fn_t args ("fun_" ^ x)
  | AppDCls (x , (y1, y2)) -> 
    (*the location of the index might depend on is_alt, gotta add that*)
    Printf.eprintf "AppDCls\n%!";
    let fld_ptr = build_struct_gep fun_t (load_fn (load_var x)) 1 "fld_ptr" builder in 
    let fn_ptr = load_ptr fld_ptr in
    let args = [|load_var x; load_var y1; load_var y2|] in
    let fn_t = function_type value_t [|value_t; value_t; value_t|]in
    build_call fn_t fn_ptr args "AppDCls" builder 
  | AppMDir (x, y) -> 
    Printf.eprintf "AppMDir\n%!";
    let args = [|const_int int_t 0; load_var y|] in
    if config.alt then
      let fn_t = function_type value_t [| value_t; value_t|] in
      call_function ("fun_alt_" ^ x) fn_t args ("fun_alt_" ^ x)
    else
      let fn_t = function_type value_t [| value_t; value_t|] in
      call_function ("fun_" ^ x) fn_t args ("fun_" ^ x)
  | AppMCls (x, y) -> 
    Printf.eprintf "AppMCls\n%!";
    (*the location of the index might depend on is_alt, gotta add that*)
    let fld_ptr = build_struct_gep fun_t (load_fn (load_var x)) 0 "fld_ptr" builder in 
    let fn_ptr = load_ptr fld_ptr in
    let args = [|load_var x; load_var y|] in
    let fn_t = function_type value_t [|value_t; value_t|]in
    build_call fn_t fn_ptr args "AppMCls" builder 
  | AppTy (y, zs_len, outer_tvs_len, tas) -> 
    Printf.eprintf "AppTy\n%!";
    let total_env_size = zs_len + List.length tas + outer_tvs_len in 
    cnt_env_llvm := 0;
    let hdr_size = build_ptrtoint (size_of fun_t) int_t "hdr_size" builder in
    let ptr_size = build_ptrtoint (size_of ptr_t) int_t "ptr_size" builder in
    let n_env = const_int int_t total_env_size in
    let env_bytes = build_mul ptr_size n_env "env_bytes" builder in
    let arg = build_add hdr_size env_bytes "total_size" builder in
    let args = [|arg|] in
    let fn_t = function_type (ptr_t) [|size_t|] in
    let fun_x = call_function "GC_malloc" fn_t args "fun_alloc" in
    ignore(build_store fun_x (load_ptr(load_fn(load_var y)))builder);
    toLLVM_tas named_values (y, zs_len, total_env_size, fun_x, tas);
    fun_x
  | AppTyFun (y, zs_len, outer_tvs_len, tas) -> 
    Printf.eprintf "AppTyFun\n%!";
    let total_env_size = zs_len + List.length tas + outer_tvs_len in 
    cnt_env_llvm := 0;
    let hdr_size = build_ptrtoint (size_of fun_t) int_t "hdr_size" builder in
    let ptr_size = build_ptrtoint (size_of ptr_t) int_t "ptr_size" builder in
    let n_env = const_int int_t total_env_size in
    let env_bytes = build_mul ptr_size n_env "env_bytes" builder in
    let arg = build_add hdr_size env_bytes "total_size" builder in
    let args = [|arg|] in
    let fn_t = function_type (ptr_t) [|size_t|] in
    let fun_x = call_function "GC_malloc" fn_t args "fun_alloc" in
    ignore(build_store fun_x (load_ptr(load_fn(load_var y)))builder);
    toLLVM_tas named_values (y, zs_len, total_env_size, fun_x, tas);
    let fn_t = function_type value_t [|value_t; value_t|] in
    let args = [|fun_x ; const_int int_t 0|] in
    call_function ("tfun_" ^ y) fn_t args ("tfun_" ^ y)
  | Cast (x, u1, u2, (r, p)) ->
    Printf.eprintf "Cast\n%!";
    let c1, c2 = llvm_of_ty named_values u1, llvm_of_ty named_values u2 in
    let x_arg = load_var x in
    let r_arg = const_int uint32_t r in
    let sgn = const_int uint8_t begin match p with Pos -> 1 | Neg -> 0 end in
    let args = [|x_arg; c1; c2; r_arg; sgn|] in
    let fn_t = function_type (value_t) [|value_t; ptr_t; ptr_t; uint32_t; uint8_t|] in
    call_function "cast" fn_t args "cast"
  | CApp (x, y) -> 
    Printf.eprintf "CApp\n%!";
    if CrcManager.mem_inj y then
      let tag = CrcManager.find_inj y in
      (* PROFILE *)
        let shift = build_shl (load_var x) (const_int int_t 3) "lshift" builder in
        build_or shift (toLLVM_tag tag) "or_shift" builder
    else if CrcManager.mem_proj y then
      let (tag, rid, p) = CrcManager.find_proj y in
      (* PROFILE *)
      let cond1 = build_and (load_var x) (const_int int_t 7) "and" builder in
      let cond2 = toLLVM_tag tag in
      let cond = build_icmp Icmp.Eq cond1 cond2 "comp" builder in 
      (* if_else cond then_val else_val *)
      let start_bb = insertion_block builder in
      let the_function = block_parent start_bb in
      let then_bb = append_block context "then" the_function in
      position_at_end then_bb builder;
      let shift = build_ashr (load_var x) (const_int int_t 3) "lshift" builder in
      let then_val = shift in
      let new_then_bb = insertion_block builder in
      let else_bb = append_block context "else" the_function in
      position_at_end else_bb builder;
      let parity = const_int int_t (match p with Pos -> 1 | Neg -> 0) in
      let args = [|const_int int_t rid; parity|] in
      let fn_t = function_type (void_t) [|uint32_t; uint8_t|] in
      let else_val = call_function "blame" fn_t args "" in
      let new_else_bb = insertion_block builder in
      let merge_bb = append_block context "ifcont" the_function in
      position_at_end merge_bb builder;
      let incoming = [(then_val, new_then_bb); (else_val, new_else_bb)] in
      let phi = build_phi incoming "iftmp" builder in
      position_at_end start_bb builder;
      ignore (build_cond_br cond then_bb else_bb builder);
      position_at_end new_then_bb builder; ignore (build_br merge_bb builder);
      position_at_end new_else_bb builder; ignore (build_br merge_bb builder);
      position_at_end merge_bb builder;
      phi
    else
      let args = [|load_var x ; load_crc (load_var y)|] in
      let fn_t = function_type (value_t) [|value_t; ptr_t|] in
      call_function "coerce" fn_t args "CApp"
  | Coercion c -> 
    Printf.eprintf "Coercion\n%!"; 
    toLLVM_crc(c)
  | CSeq (x, y) -> 
    Printf.eprintf "CSeq\n%!";
    let arg1 = load_crc(load_var x) in
    let arg2 = load_crc(load_var y) in
    let args = [|arg1; arg2|] in
    let fn_t = function_type (ptr_t) [|ptr_t; ptr_t|] in
    call_function "compose" fn_t args "CSeq"   
  | MakeCls (x, {entry = l; actual_fv = vs}, {ftvs = ftv; offset = n}, f) ->
    Printf.eprintf "MakeCls\n%!";
    let ptr = build_alloca value_t x builder in
    let env_size = List.length vs + List.length ftv + n in 
    cnt_env_llvm := 0;
    let hdr_size = build_ptrtoint (size_of fun_t) int_t "hdr_size" builder in
    let ptr_size = build_ptrtoint (size_of ptr_t) int_t "ptr_size" builder in
    let n_env = const_int int_t env_size in
    let env_bytes = build_mul ptr_size n_env "env_bytes" builder in
    let arg = build_add hdr_size env_bytes "total_size" builder in
    let args = [|arg|] in
    let fn_t = function_type (ptr_t) [|size_t|] in
    let cls = call_function "GC_malloc" fn_t args "cls_alloc" in
    let val_cls = build_ptrtoint cls value_t "cls_value" builder in
    ignore(build_store val_cls ptr builder);
    Hashtbl.add named_values x ptr;
    (if config.intoB || config.static then
      let funcM_ptr = build_struct_gep fun_t (cls) 0 "funcM_ptr" builder in
      let funcM_elem = match lookup_function ("fun_"^x) the_module with
        | Some f -> f
        | None -> failwith ("fun_" ^ l ^ " not found") in
      ignore(build_store (funcM_elem) funcM_ptr builder)
    else if config.alt then
      let funcD_ptr = build_struct_gep fun_t (cls) 1 "funcD_ptr" builder in
      let funcD_elem = match lookup_function ("fun_"^x) the_module with
        | Some f -> f
        | None -> failwith ("fun_" ^ l ^ " not found") in
      ignore(build_store (funcD_elem) funcD_ptr builder);
      let funcM_ptr = build_struct_gep fun_t (cls) 0 "funcM_ptr" builder in
      let funcM_elem = match lookup_function ("fun_alt_"^x) the_module with
        | Some f -> f
        | None -> failwith ("fun_alt" ^ l ^ " not found") in
      ignore(build_store (funcM_elem) funcM_ptr builder)
    else begin
      let funcD_ptr = build_struct_gep fun_t (cls) 1 "funcD_ptr" builder in
      let funcD_elem = match lookup_function ("fun_"^x) the_module with
        | Some f -> f
        | None -> failwith ("fun_" ^ l ^ " not found") in
      ignore(build_store (funcD_elem) funcD_ptr builder)
    end);
    let fun_x = load_fn (load_var x) in
    toLLVM_vs named_values (x, vs);
    toLLVM_ftas named_values (n, fun_x, ftv);
    toLLVM_exp f
  | MakeTyCls (x, {entry = l; actual_fv = vs}, {ftvs = ftv; offset = n}, f) -> 
    Printf.eprintf "MakeTyCls\n%!";
    let ptr = build_alloca value_t x builder in
    let env_size = List.length vs + List.length ftv + n in 
    cnt_env_llvm := 0;
    let hdr_size = build_ptrtoint (size_of fun_t) int_t "hdr_size" builder in
    let ptr_size = build_ptrtoint (size_of ptr_t) int_t "ptr_size" builder in
    let n_env = const_int int_t env_size in
    let env_bytes = build_mul ptr_size n_env "env_bytes" builder in
    let arg = build_add hdr_size env_bytes "total_size" builder in
    let args = [|arg|] in
    let fn_t = function_type (ptr_t) [|size_t|] in
    let cls = call_function "GC_malloc" fn_t args "cls_alloc" in
    let val_cls = build_ptrtoint cls value_t "cls_value" builder in
    ignore(build_store val_cls ptr builder);
    Hashtbl.add named_values x ptr;
    let funcM_ptr = build_struct_gep fun_t (cls) 0 "funcM_ptr" builder in
    let funcM_elem = match lookup_function ("tfun_"^l) the_module with
      | Some f -> f
      | None -> failwith ("tfun_" ^ l ^ " not found") in
    ignore(build_store (funcM_elem) funcM_ptr builder);
    let fun_x = load_fn (load_var x) in
    toLLVM_vs named_values (x, vs);
    toLLVM_ftas named_values (n, fun_x, ftv);
    toLLVM_exp f
  | SetTy ((i, { contents = opu }), f) -> 
    Printf.eprintf "SetTy\n%!";
    (* const_int int_t 5; *)
    begin match opu with (* ここはtoC_tycontentを参照 *)
    | None ->
      let name = Printf.sprintf "_ty%d" i in
      let fn_t = function_type ptr_t [|size_t|] in
      let args = [| build_ptrtoint (size_of ty_t) int_t "size" builder |] in
      let ty_ptr = call_function "GC_malloc" fn_t
        args "tyvar_alloc" in
      let kind_ptr = build_struct_gep ty_t ty_ptr 0 "kind_ptr" builder in
      ignore (build_store (toLLVM_tykind "TYVAR") kind_ptr builder);
      let ptr_alloca = build_alloca ptr_t name builder in
      ignore (build_store ty_ptr ptr_alloca builder);
      Hashtbl.add named_values name ptr_alloca;
      toLLVM_exp f
    | Some (TyFun (u1, u2)) ->
      let name = Printf.sprintf "_tyfun%d" i in
      let fn_t = function_type ptr_t [|size_t|] in
      let ty_size = build_ptrtoint (size_of ty_t) int_t "size" builder in
      let args = [|ty_size|] in
      let tyfun_ptr = call_function "GC_malloc" fn_t args "tyfun_alloc" in
      let kind_ptr = build_struct_gep ty_t tyfun_ptr 0 "kind_ptr" builder in
      ignore (build_store (toLLVM_tykind "TYFUN") kind_ptr builder);
      let left_alloc = call_function "GC_malloc" fn_t args "tyfun_left_alloc" in
      let right_alloc = call_function "GC_malloc" fn_t args "tyfun_right_alloc" in
      let left_field  = build_struct_gep ty_t tyfun_ptr 1 "left_field" builder in
      let right_field = build_struct_gep ty_t tyfun_ptr 2 "right_field" builder in
      ignore (build_store left_alloc left_field builder);
      ignore (build_store right_alloc right_field builder);
      let u1_val = llvm_of_ty named_values u1 in
      let u2_val = llvm_of_ty named_values u2 in
      ignore (build_store u1_val left_field builder);
      ignore (build_store u2_val right_field builder);
      let ptr_alloca = build_alloca ptr_t name builder in
      ignore (build_store tyfun_ptr ptr_alloca builder);
      Hashtbl.add named_values name ptr_alloca;
      toLLVM_exp f
    | Some (TyList u) ->
      let name = Printf.sprintf "_tylist%d" i in
      let fn_t = function_type ptr_t [|size_t|] in
      let ty_size = build_ptrtoint (size_of ty_t) int_t "size" builder in
      let args = [|ty_size|] in
      let tylist_ptr = call_function "GC_malloc" fn_t args "tylist_alloc" in
      let kind_ptr = build_struct_gep ty_t tylist_ptr 0 "kind_ptr" builder in
      ignore (build_store (toLLVM_tykind "TYLIST") kind_ptr builder);
      let list_alloc = call_function "GC_malloc" fn_t args "tylist_list_alloc" in
      let tylist_field = build_struct_gep ty_t tylist_ptr 1 "tylist_field" builder in
      ignore (build_store list_alloc tylist_field builder);
      let u_val = llvm_of_ty named_values u in
      ignore (build_store u_val tylist_field builder);
      let ptr_alloca = build_alloca ptr_t name builder in
      ignore (build_store tylist_ptr ptr_alloca builder);
      Hashtbl.add named_values name ptr_alloca;
      toLLVM_exp f
    | Some _ -> raise @@ ToLLVM_bug "not tyfun or tylist is in tyvar option"
    end 
  (* do this later*)
and if_else named_values cond f1 f2 ~config =
  let start_bb = insertion_block builder in
  let the_function = block_parent start_bb in
  let then_bb = append_block context "then" the_function in
  position_at_end then_bb builder;
  let then_val = toLLVM_exp named_values f1 ~config in
  let new_then_bb = insertion_block builder in
  let else_bb = append_block context "else" the_function in
  position_at_end else_bb builder;
  let else_val = toLLVM_exp named_values f2 ~config in
  let new_else_bb = insertion_block builder in
  let merge_bb = append_block context "ifcont" the_function in
  position_at_end merge_bb builder;
  let incoming = [(then_val, new_then_bb); (else_val, new_else_bb)] in
  let phi = build_phi incoming "iftmp" builder in
  position_at_end start_bb builder;
  ignore (build_cond_br cond then_bb else_bb builder);
  position_at_end new_then_bb builder; ignore (build_br merge_bb builder);
  position_at_end new_else_bb builder; ignore (build_br merge_bb builder);
  position_at_end merge_bb builder;
  phi

let toLLVM_tydecl (_, name) =
  ignore (declare_global ty_t name the_module)

let toLLVM_tydecls l = 
  List.iter toLLVM_tydecl l

(*型の定義*)
let toLLVM_tycontent (u, name) = 
  let g = match lookup_global name the_module with
    | Some g -> g
    | None -> raise @@ ToLLVM_bug (name ^ " not declared")
  in
  match u with
  | TyVar _ -> (* TyVarはtykindをTYVARにする *)
    let init = const_named_struct ty_t [|toLLVM_tykind "TYVAR"; const_null ptr_t; const_null ptr_t|] in
    set_initializer init g;
    set_linkage Linkage.Internal g
  | TyFun (u1, u2) -> 
    (*TyFunはtykindをTYFUNとする
      さらに，leftとrightにTyFunの二つの型をそれぞれ代入する*)
    let left = llvm_of_ty_static u1 in
    let right = llvm_of_ty_static u2 in
    let init = const_named_struct ty_t [|toLLVM_tykind "TYFUN"; left; right|] in
    set_initializer init g;
    set_linkage Linkage.Internal g
  | TyList u ->
    let inner = llvm_of_ty_static u in
    let init = const_named_struct ty_t [|toLLVM_tykind "TYLIST"; inner; const_null ptr_t|] in
    set_initializer init g;
    set_linkage Linkage.Internal g
  | TyTuple us ->
    let arity = List.length us in
    let ty_ptrs = Array.of_list (List.map llvm_of_ty_static us) in
    (* let arr_t = array_type ptr_t arity in *)
    let arr = const_array ptr_t ty_ptrs in
    let arr_g = define_global (name ^ "_tys") arr the_module in
    set_linkage Linkage.Internal arr_g;
    let init = const_named_struct ty_t [|toLLVM_tykind "TYTUPLE"; const_int uint16_t arity; arr_g|] in
    set_initializer init g;
    set_linkage Linkage.Internal g
  | u -> raise @@ ToLLVM_bug (Format.asprintf "not tyvar, tyfun or tylist in tycontent: %a" Pp.pp_ty2 u) 

let toLLVM_tycontents l = 
  List.iter toLLVM_tycontent l

(*型定義全体を記述*)
let toLLVM_tys l =
  toLLVM_tydecls l;
  toLLVM_tycontents l

let toLLVM_range (r, _) =
  let filename = 
    if r.start_p.pos_fname <> "" then
      "\"File \\\"" ^ r.start_p.pos_fname ^ "\\\", \"" else "\"\"" in
  let filename_global = define_global ".range_filename" (const_stringz context filename) the_module in
  set_linkage Linkage.Private filename_global;
  let filename_ptr = const_gep ptr_t filename_global [| const_int uint32_t 0; const_int uint32_t 0|] in
  let startline = const_int uint32_t r.start_p.pos_lnum in
  let startchr = const_int uint32_t (r.start_p.pos_cnum - r.start_p.pos_bol) in
  let endline = const_int uint32_t r.end_p.pos_lnum in
  let endchr = const_int uint32_t (r.end_p.pos_cnum - r.end_p.pos_bol) in
  const_named_struct range_t [| filename_ptr; startline; startchr; endline; endchr|]

let toLLVM_ranges ranges = 
  let sorted = List.sort (fun (_, i1) (_, i2) -> compare i1 i2) ranges in
  let entries = Array.of_list (List.map toLLVM_range sorted) in
  (* let arr_t = array_type range_t (Array.length entries) in *)
  let arr = const_array range_t entries in
  let g = define_global "local_range_list" arr the_module in
  set_linkage Linkage.Internal g

let toLLVM_crcdecl (_, name) =
  ignore (declare_global crc_t name the_module)

let toLLVM_crcdecls l = 
  List.iter toLLVM_crcdecl l

let rec check_has_tv = function
  | CId -> false
  | CSeqInj (c', _) | CSeqProj (_, _, c') | CList c' -> check_has_tv c'
  | CTvInj _ | CTvProj _ -> true
  | CFun (c1, c2) -> (check_has_tv c1) || (check_has_tv c2)
  | CTuple cs -> List.fold_left (fun b c -> b || check_has_tv c) false cs

(* コアーションの定義 *)
(* let toLLVM_crccontent (c, name) = 
  let has_tv_val = if check_has_tv c then 1 else 0 in
  let llvm_of_crc c = match c with
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
      (llvm_of_crc c')
  | CSeqProj (g, (rid, p), c') -> 
    let arity_str = match g with Tp arity -> Format.asprintf ", .arity_proj = %d" arity | _ -> "" in
    fprintf ppf "static crc %s = { .crckind = SEQ_PROJ, .g_proj = G_%a%s, .p_proj = %d,  .has_tv = %d, .crcdat.seq_tv = { .rid_proj = %d, .ptr.s = (crc*)%s } };"
      name
      toC_tag g
      arity_str
      (match p with Pos -> 1 | Neg -> 0)
      has_tv_val
      rid
      (llvm_of_crc c')
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
      (llvm_of_ty (TyVar tv))
  | CTvProj (tv, (rid, p)) ->
    fprintf ppf "static crc %s = { .crckind = TV_PROJ, .p_proj = %d, .has_tv = %d, .crcdat.seq_tv = { .rid_proj = %d, .ptr.tv = %s } };"
      name
      (match p with Pos -> 1 | Neg -> 0)
      has_tv_val
      rid
      (llvm_of_ty (TyVar tv))
  | CFun (c1, c2) -> 
    fprintf ppf "static crc %s = { .crckind = FUN, .has_tv = %d, .crcdat.fun_crc = { .c1 = %s, .c2 = %s } };"
      name
      has_tv_val
      (llvm_of_crc c1)
      (llvm_of_crc c2)
  | CList c' ->
    fprintf ppf "static crc %s = { .crckind = LIST, .has_tv = %d, .crcdat.lst_crc = %s };"
      name
      has_tv_val
      (llvm_of_crc c') 
  | _ -> raise @@ ToLLVM_bug "not in crccontent" *)

(* let toLLVM_crccontents l = 
  List.iter toLLVM_crccontent l  *)

(*型定義全体を記述*)
let register_static_crc (_, name) = 
  let arg = 
    match lookup_global name the_module with
      | Some g -> g
      | None -> raise @@ ToLLVM_bug "undeclared crc"
    in 
  let fn_t = function_type void_t [|ptr_t|] in
  let args = [|arg|] in
  ignore(call_function "register_static_crc" fn_t args "")

(* let toLLVM_crcs l ~config =
  let register_builtins () =
    register_static_crc ( "", "crc_id");
    register_static_crc ( "", "crc_inj_INT");
    register_static_crc ( "", "crc_inj_BOOL");
    register_static_crc ( "", "crc_inj_UNIT");
    register_static_crc ( "", "crc_inj_AR");
    register_static_crc ( "", "crc_inj_LI")
  in
  if config.static then ()
  else 
    let init_crcs_ty = function_type void_t [||] in
    let init_crcs = define_function "init_crcs" init_crcs_ty the_module in
    set_linkage Linkage.Internal init_crcs;
    let bb = entry_block init_crcs in
    position_at_end bb builder;
    toLLVM_crcdecls l;
    (* toLLVM_crccontents l; *)
    register_builtins ();
    List.iter register_static_crc l;
    ignore (build_ret_void builder) *)

let toLLVM_fv named_valuesf x=
  let idx = !cnt_env_llvm in
  cnt_env_llvm := !cnt_env_llvm + 1;
  let fun_cls = load_fn (load_var named_valuesf "cls") in
  let hdr_size = build_ptrtoint (size_of fun_t) int_t "hdr_size" builder in
  let fun_int = build_ptrtoint fun_cls int_t "fun_int" builder in
  let slot_offset = const_int int_t (idx * 8) in
  let addr = build_add fun_int (build_add hdr_size slot_offset "off" builder) "addr" builder in
  let elem_ptr = build_inttoptr addr ptr_t "elem_ptr" builder in
  let fv_val = build_load value_t elem_ptr ("fv_" ^ x) builder in
  let x_ptr = build_alloca value_t x builder in
  ignore (build_store fv_val x_ptr builder);
  Hashtbl.add named_valuesf x x_ptr

let toLLVM_fvs named_valuesf fvl =
    List.iter (toLLVM_fv named_valuesf) fvl 

(*関数定義の最初に，型変数を詰める場所も設ける*)

let toLLVM_tv named_valuesf fun_cls (i, _)= (* TODO *)
  let idx = !cnt_env_llvm in
  cnt_env_llvm := !cnt_env_llvm + 1;
  let hdr_size = build_ptrtoint (size_of fun_t) int_t "hdr_size" builder in
  let fun_int = build_ptrtoint fun_cls int_t "fun_int" builder in
  let slot_offset = const_int int_t (idx * 8) in
  let addr = build_add fun_int (build_add hdr_size slot_offset "off" builder) "addr" builder in
  let elem_ptr = build_inttoptr addr ptr_t "elem_ptr" builder in
  let tyi = load_ty (load_var named_valuesf (Printf.sprintf "_ty%d" i)) in
  ignore(build_store elem_ptr tyi builder)

let toLLVM_tvs named_valuesf tvl cls =
  List.iter (toLLVM_tv named_valuesf cls) tvl

let toLLVM_funv named_valuesf (exists_fun, l) cls = 
  if not exists_fun then
    ()
  else
    let ptr = build_alloca value_t l builder in
    ignore(build_store cls ptr builder);
    ignore(Hashtbl.add named_valuesf l ptr)

let toLLVM_label fundef ~config =
  match fundef with
  | FundefD { name = l; _ } ->
    let func_t = function_type value_t [|value_t; value_t; value_t|] in
    ignore (declare_function ("fun_" ^ l) func_t the_module)
  | FundefM { name = l; _ } ->
    let func_t = function_type value_t [|value_t; value_t|] in
    let l_alt = if config.alt then ("alt_" ^ l) else l in 
    ignore (declare_function ("fun_" ^ l_alt) func_t the_module)
  | FundefTy { name = l; _ } ->
    let func_t = function_type value_t [|value_t; value_t|] in
    ignore (declare_function ("tfun_" ^ l) func_t the_module)
let toLLVM_fundef fundef ~config = match fundef with
  | FundefD { name = l; tvs = (tvs, _); arg = (x, y); formal_fv = fvl; body = f } ->
    let named_valuesf:(string, llvalue) Hashtbl.t = Hashtbl.create 16 in
    cnt_env_llvm := 0;
    (* let func_t = function_type value_t [|value_t; value_t ; value_t|] in *)
    Printf.eprintf "test3\n%!";
    let func = match lookup_function ("fun_" ^ l) the_module with
      | Some f -> f   (* use existing declaration from label *)
      | None -> raise @@ ToLLVM_bug "Should have been declared already"
    in
    Printf.eprintf "test4\n%!";
    set_linkage Linkage.Internal func;
    let bb = append_block context "entry" func in 
    position_at_end bb builder;
    let args = params func in
    (* Maybe i should make a local hashtable to which these arguments are loaded. which then can be called by the body? *)
    set_value_name "cls" args.(0);
    set_value_name x args.(1);
    set_value_name y args.(2);
    Printf.eprintf "test5\n%!";
    let cls_ptr = build_alloca int_t "cls" builder in
    ignore(build_store args.(0) cls_ptr builder);
    let x_ptr = build_alloca int_t x builder in
    ignore(build_store args.(1) x_ptr builder);
    let y_ptr = build_alloca int_t y builder in
    ignore(build_store args.(2) y_ptr builder);
    Hashtbl.add named_valuesf "cls" cls_ptr;
    Hashtbl.add named_valuesf x x_ptr;
    Hashtbl.add named_valuesf y y_ptr;
    toLLVM_funv named_valuesf (V.mem (to_id l) (fv_exp f), l) args.(0);
    toLLVM_fvs named_valuesf fvl;
    toLLVM_tvs named_valuesf tvs args.(0);
    let result = toLLVM_exp named_valuesf f ~config in
    ignore(build_ret result builder);
    Printf.eprintf "FundefD: %s\n%!" l
  | FundefM { name = l; tvs = (tvs, _); arg = x; formal_fv = fvl; body = f }  ->
    let named_valuesf:(string, llvalue) Hashtbl.t = Hashtbl.create 16 in
    cnt_env_llvm := 0;
    (* let func_t = function_type value_t [|value_t; value_t|] in *)
    let l_alt = if config.alt then ("alt_" ^ l) else l in 
    let func = match lookup_function ("fun_" ^ l_alt) the_module with
      | Some f -> f   (* use existing declaration from predeclare *)
      | None -> raise @@ ToLLVM_bug "Should have been declared already"
    in
    set_linkage Linkage.Internal func;
    let bb = append_block context "entry" func in 
    position_at_end bb builder;
    let args = params func in
    set_value_name "cls" args.(0);
    set_value_name x args.(1);
    let cls_ptr = build_alloca int_t "cls" builder in
    ignore(build_store args.(0) cls_ptr builder);
    let x_ptr = build_alloca int_t x builder in
    ignore(build_store args.(1) x_ptr builder);
    Hashtbl.add named_valuesf "cls" cls_ptr;
    Hashtbl.add named_valuesf x x_ptr;
    toLLVM_funv named_valuesf (V.mem (to_id l) (fv_exp f), l) args.(0);
    toLLVM_fvs named_valuesf fvl;
    toLLVM_tvs named_valuesf tvs args.(0);
    let result = toLLVM_exp named_valuesf f ~config in
    ignore(build_ret result builder);
    Printf.eprintf "FundefM: %s\n%!" l
  | FundefTy { name = l; tvs = (tvs, _); formal_fv = fvl; body = f } ->
    let named_valuesf:(string, llvalue) Hashtbl.t = Hashtbl.create 16 in
    cnt_env_llvm := 0;
    (* let func_t = function_type value_t [|value_t; value_t|] in *)
    let func = match lookup_function ("tfun_" ^ l) the_module with
      | Some f -> f   (* use existing declaration from predeclare *)
      | None -> raise @@ ToLLVM_bug "Should have been declared already"
    in
    set_linkage Linkage.Internal func;
    let bb = append_block context "entry" func in 
    position_at_end bb builder;
    let args = params func in
    set_value_name "cls" args.(0);
    set_value_name "dummy" args.(1);
    let cls_ptr = build_alloca int_t "cls" builder in
    ignore(build_store args.(0) cls_ptr builder);
    let dummy_ptr = build_alloca int_t "dummy" builder in
    ignore(build_store args.(1) dummy_ptr builder);
    Hashtbl.add named_valuesf "cls" cls_ptr;
    Hashtbl.add named_valuesf "dummy" dummy_ptr;
    toLLVM_funv named_valuesf (V.mem (to_id l) (fv_exp f), l) args.(0);
    toLLVM_fvs named_valuesf fvl;
    toLLVM_tvs named_valuesf tvs args.(0);
    let result = toLLVM_exp named_valuesf f ~config in
    ignore(build_ret result builder);
    Printf.eprintf "FundefTy: %s\n%!" l

let toLLVM_fundefs toplevel ~config =
  List.iter (toLLVM_label  ~config) toplevel;
  Printf.eprintf "test2\n%!";
  List.iter (toLLVM_fundef ~config) toplevel

  (* No normal logical operators and no binary operators? *)
(*全体を記述*)
(* We can use the module to remember previous instructions and therefore *)
(* create a continuous REPL, and add functionality to clear some of the instructions? *)
(* we could have each run create its own snippet of code, which are linked and released at the end? *)

let toC_program ?(bench=0) ~config ppf (Prog (toplevel, f)) =
  let tys = TyManager.get_definitions () in
  let ranges = RangeManager.get_definitions () in
  let crcs = CrcManager.get_definitions () in
  let init_crcs = if config.static then "" else "#ifdef HASH\ninit_crcs();\n#endif\n" in
  runtime ();
  declare_ty_globals ();
  toLLVM_tys tys;
  toLLVM_ranges ranges;
  declare_crc_globals ();
  (* (toLLVM_crcs ~config) crcs; *)
  Printf.eprintf "test1\n%!";
  toLLVM_fundefs toplevel ~config;
  (* in toC_program, before defining main *)
  if not config.static then begin
    let g = define_global "range_list" (const_null ptr_t) the_module in
    set_linkage Linkage.External g
  end;
  let main_t = function_type int_t [||] in
  let main = define_function "main" main_t the_module in
  let bb = entry_block main in
  position_at_end bb builder;
  let fn_t = function_type void_t [||] in
  ignore (call_function "GC_init" fn_t [||] "");
  let named_values:(string, llvalue) Hashtbl.t = Hashtbl.create 16 in
  ignore(toLLVM_exp named_values f ~config);
  ignore(build_ret (const_int int_t 0) builder);
  dump_module the_module;
  Llvm_analysis.assert_valid_module the_module;
  Llvm.print_module "result_C/output.ll" the_module;
  fprintf ppf "%s\n%s\n%a%a%a%a%s%s%s%a%s"
    (asprintf "#include <gc.h>\n#include \"../%slibC/runtime.h\"\n"
      (if bench = 0 then "" else "../../"))
    (if bench = 0 then "#define GC_INITIAL_HEAP_SIZE 1048576\n" else "")
    toC_tys tys
    toC_ranges ranges
    (toC_crcs ~config) crcs
    (toC_fundefs ~config) toplevel
    (if bench = 0 && not config.static then "range *range_list;\n\n" else "")
    (if bench = 0 then asprintf "int main() {\nGC_INIT();\n%s" init_crcs else asprintf "int mutant%d() {\n%s" bench init_crcs)
    (if List.length ranges != 0 then "range_list = local_range_list;\n" else "")
    (toC_exp ~config ~is_main:true) f
    "}"