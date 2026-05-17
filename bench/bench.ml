open Unix
(* open Core *)
(* open Lambda_S1_dti.Utils *)
open Lambda_S_dti

type mode = 
| SI | SC | AI | AC | BI | BC
| STATICI | STATICC

(* Base of Benchmark settings *)
let itr = 500
let files = [
  (* "church_2"; *)
  (* "church_4"; *)
  (* "church_65532"; *)
  (* "easy"; *)
  "evenodd";
  "fib";
  "fold";
  "fold_mono";
  "incsum";
  "loop";
  "loop_mono";
  "map";
  "map_mono";
  "mklist";
  "tak";
  "zipwith";
  "zipwith_mono";
]
let modes = [
  SI;
  SC;
  AI;
  AC;
  BI;
  BC;
  STATICI;
  STATICC;
  ]   
  (* [SC; SI] : SC と SI を実行 *)

(* ------------------ *)
let string_of_mode = function
  | SI -> "SI"
  | SC -> "SC"
  | AI -> "AI"
  | AC -> "AC"
  | BI -> "BI"
  | BC -> "BC"
  | STATICI -> "STATICI"
  | STATICC -> "STATICC"

let mode_of_string = function
  | "SI" -> SI
  | "SC" -> SC
  | "AI" -> AI
  | "AC" -> AC
  | "BI" -> BI
  | "BC" -> BC
  | "SLI" -> SI
  | "STATICI" -> STATICI
  | "STATICC" -> STATICC
  | _ -> failwith "mode_of_string"

let full_mode_name mode eager hash =
  let prefix, suffix = match mode with
    | SI -> "S", "I" | SC -> "S", "C"
    | AI -> "A", "I" | AC -> "A", "C"
    | BI -> "B", "I" | BC -> "B", "C"
    | STATICI -> "STATIC", "I" | STATICC -> "STATIC", "C"
  in
  Printf.sprintf "%s%s%s%s" prefix (if eager then "E" else "L") (if hash then "H" else "N") suffix
  
let split_pairs lst =
  List.fold_right
    (fun (a, b) (as_list, bs_list) -> (a :: as_list, b :: bs_list))
    lst ([], [])

(* メモリ計測（設定に応じて）を JSON に *)
let mem_json mode file idx ~compile ~eager ~hash =
  let mode_str = full_mode_name mode eager hash in
  let label = Printf.sprintf "%s/%s#%d" mode_str file idx in
  if compile then     
    let run () = ignore (Core_unix.system "logs/bench.out") in
    Bench_utils.measure_mem_to_json ~label run
  else raise @@ Failure "yet" 
  (* match mode with
  | SI ->
      let translated = Translate.CC.translate tyenv (Pipeline.CC.tv_renew decl) in
      let run () = 
        ignore (Eval.CC.eval_program Syntax.Environment.empty translated) in
      Bench_utils.measure_mem_to_json ~label run
  | AI ->
      let translated = Translate.CC.translate_alt tyenv (Pipeline.CC.tv_renew decl) in
      let run () = 
        ignore (Eval.CC.eval_program Syntax.Environment.empty translated) in
      Bench_utils.measure_mem_to_json ~label run
  | BI ->
      let translated = Pipeline.CC.tv_renew decl in
      let run () = 
        ignore (Eval.CC.eval_program Syntax.Environment.empty translated) in
      Bench_utils.measure_mem_to_json ~label run *)
  (* | SC | AC | BC ->  *)

(* -------- Parsing & mutation (1回で両モードに使い回す) --------------- *)
let parse_and_mutate ~is_compare (file : string) =
  (* is_compare が true なら compare用のディレクトリを、falseなら通常ディレクトリを見る *)
  let target_path = 
    if is_compare then Printf.sprintf "samples/church_compare/%s.ml" file
    else Printf.sprintf "samples/src/%s.ml" file 
  in
  let _, lexeme = Pipeline.lex Format.std_formatter (Some target_path) in
  let decl  = Parser.toplevel Lexer.main lexeme in
  
  (* is_compare が true ならミュータントを作らず、元の1つのプログラムだけ返す *)
  let lst_mutated = 
    if is_compare then [decl]
    else Mutate.mutate_all decl 
  in
  (lst_mutated : Syntax.ITGL.program list)
(* let parse_and_mutate (file : string) =
  let target_path = Printf.sprintf "samples/src/%s.ml" file in
  let _, lexeme = Pipeline.lex Format.std_formatter (Some target_path) in
  let decl  = Parser.toplevel Lexer.main lexeme in
  let lst_mutated = Mutate.mutate_all decl in
  (lst_mutated : Syntax.ITGL.program list) *)

(* -------- 1ファイル × 1モード（ターゲット）を実行 ------------------ *)
let bench_file_mode
    ~log_dir
    ~itr
    ~(ordinal:int)
    ~(total_targets:int)
    ~(file:string)
    ~(mode:mode)
    ~eager
    ~hash
    ~(mutants:Syntax.ITGL.program list)
  =
  let mode_str = full_mode_name mode eager hash in
  try begin
  (* modeに応じたconfigの生成 *)
  let config = match mode with
  | SI -> Config.create ~eager ~hash ~opt_file:(Some file) ()
  | SC -> Config.create ~eager ~hash ~opt_file:(Some file) ~compile:true ()
  | AI -> Config.create ~eager ~hash ~opt_file:(Some file) ~alt:true ()
  | AC -> Config.create ~eager ~hash ~opt_file:(Some file) ~alt:true ~compile:true ()
  | BI -> Config.create ~eager ~hash ~opt_file:(Some file) ~intoB:true ()
  | BC -> Config.create ~eager ~hash ~opt_file:(Some file) ~intoB:true ~compile:true ()
  | STATICI -> Config.create ~eager ~hash ~opt_file:(Some file) ~static:true()
  | STATICC -> Config.create ~eager ~hash ~opt_file:(Some file) ~static:true ~compile:true ()
  in

  Format.fprintf Format.std_formatter "debug: bench_file_mode\n";
  (* text用，json用のocとfmtを取得 *)
  let oc_opt, fmt, json_oc, json_first = 
    let null_fmt = Format.make_formatter (fun _buf _pos _len -> ()) (fun () -> ()) in
    match Bench_utils.out_mode with
    | Text -> 
      let file_path = Printf.sprintf "%s/%s_%s.log" log_dir mode_str file in
      let oc = open_out file_path in
      Some oc, Format.formatter_of_out_channel oc, None, ref true
    | JsonLines ->
      let jsonl_path = Printf.sprintf "%s/%s_%s.jsonl" log_dir mode_str file in
      let oc = open_out jsonl_path in
      None, null_fmt, Some oc, ref true
    | Json -> 
      let json_path = Printf.sprintf "%s/%s_%s.json" log_dir mode_str file in
      let oc = open_out json_path in
      Out_channel.output_string oc "{ \"file\": \""; Out_channel.output_string oc file; Out_channel.output_string oc "\", ";
      Out_channel.output_string oc "\"mode\": \""; Out_channel.output_string oc mode_str; Out_channel.output_string oc "\", ";
      Out_channel.output_string oc "\"settings\": {\"mem_mode\": \""; 
      Out_channel.output_string oc (match Bench_utils.mem_mode with Off->"off" | Fast->"fast" | Corebench->"corebench");
      Out_channel.output_string oc "\", \"fast_runs\": "; Out_channel.output_string oc (string_of_int Bench_utils.fast_runs);
      Out_channel.output_string oc "}, \"mutants\": [\n";
      None, null_fmt, Some oc, ref true
  in

  let ppf = Utils.Format.empty_formatter in

  (* ターゲット用 Progress を開始 *)
  let label = Printf.sprintf "%s_%s" mode_str file in
  let prog = Bench_utils.Target_progress.create
               ~label ~total:(List.length mutants)
               ~ordinal ~total_targets
  in

  (* compileモードなら，.c用のディレクトリを作成 *)
  if config.compile then begin
    let c_dir = Printf.sprintf "%s/%s" log_dir mode_str in
    if not (Sys.file_exists c_dir) then Core_unix.mkdir c_dir;
    let bench_dir = Printf.sprintf "%s/bench" log_dir in
    if not (Sys.file_exists bench_dir) then Core_unix.mkdir bench_dir
  end;
  
  let counter = ref 0 in
  List.iteri (fun i p ->
    try( 
      (* Printf.fprintf stdout "debug: iter is %d\n" i; *)
      let idx = i + 1 in
      (* ---- Mutant 見出し ---- *)
      Option.iter (fun oc ->
        Printf.fprintf oc "\n(*** Mutant %d ***)\n%!" idx
      ) oc_opt;
      Option.iter (fun oc ->
        incr counter;
        Printf.fprintf oc "\n(%d):\n" !counter
      ) oc_opt;

      (* JSON 出力用に各種文字列へ *)
      let after_mutate_str      = Format.asprintf "%a" Pp.ITGL.pp_program p in

      let initial_state = { (Pipeline.init_state () ~config) with Pipeline.program = p } in

      let lst_elapsed_time, after_translation_str =
        let cc_state = 
          initial_state
          |> Pipeline.typing_ITGL ppf
          |> Pipeline.translate_to_CC ppf ~config ~bench_ppf:fmt ~bench:idx
        in
        let ast_str = Format.asprintf "%a" Pp.CC.pp_program cc_state.Pipeline.program in

        let elapsed_time = 
          if config.compile then begin
            (* --- Compilation --- *)
            let toC_state =
              cc_state
              |> Pipeline.kNorm_funs ppf ~config
              |> Pipeline.closure ppf ~config
            in
            let c_code = Pipeline.toC ppf toC_state ~config ~bench:idx in
            let filename = Format.asprintf "%s/%s/%s%d.c" log_dir mode_str file idx in
            let oc = open_out filename in
            Printf.fprintf oc "%s" c_code;
            close_out oc;
            []
          end else begin
            (* --- Evaluation --- *)
            (* Bench_utils.measure_execution_time (fun () -> 
              ignore (Pipeline.eval Utils.Format.empty_formatter cc_state ~config)
            ) itr
            |> split_pairs
            |> snd *)
            raise @@ Failure "interpreter yet"
            (* TODO: test files now require their inputs *)
          end
        in
        elapsed_time, ast_str
      in

      (* File output of benchmarking score *)
      Option.iter (fun oc ->
        match lst_elapsed_time with
        | [] -> Printf.fprintf oc "\n"
        | _  -> List.iter (fun t -> Printf.fprintf oc "%f\n" t) lst_elapsed_time
      ) oc_opt;

      (* 実行時間（従来の itr 回計測）を JSON に *)
      let times_sec_json = Bench_utils.J.list (List.map (fun t -> Bench_utils.J.float t) lst_elapsed_time) in

      let mem = mem_json mode file idx ~compile:config.compile ~eager:config.eager ~hash:config.hash in

      (* 1ミュータントの JSON オブジェクト *)
      let mutant_json =
        Bench_utils.J.obj [
          ("mode", Bench_utils.J.str mode_str);
          ("mutant_index", Bench_utils.J.int idx);
          ("after_mutate", Bench_utils.J.str after_mutate_str);
          ("after_translation", Bench_utils.J.str after_translation_str);
          ("times_sec", times_sec_json);
          ("mem", (match mem with None -> `Null | Some j -> j));
          ("cast", `Null);
          ("inference", `Null);
          ("longest", `Null);
        ]
      in

      (* ファイルへ書き出し *)
      begin match json_oc, Bench_utils.out_mode with
      | None, _ -> ()
      | Some oc, JsonLines ->
          Bench_utils.J.to_channel_ln oc mutant_json
      | Some oc, Json ->
          if not !json_first then Out_channel.output_string oc ",\n";
          Yojson.Safe.to_channel oc mutant_json;
          json_first := false
      | Some _, Text -> raise @@ Failure "yet"
      end;

      Option.iter Out_channel.flush oc_opt;
      Bench_utils.Target_progress.tick prog;  (* ← 変異1件完了ごとに更新 *)
    )
    with
    | e -> 
      Format.fprintf Format.std_formatter "\n[Error] %s 変換中にエラーが発生しました: %s@." file (Printexc.to_string e)
  ) mutants;

  Option.iter Out_channel.close oc_opt;

  (match json_oc, Bench_utils.out_mode with
    | None, _ -> ()
    | Some oc, JsonLines -> Out_channel.close oc
    | Some oc, Json ->
       Out_channel.output_string oc "\n]}\n"; Out_channel.close oc
    | Some _, Text -> raise @@ Failure "yet");

  (* compileモードなら，build_run_benchでbenchmarking *)
  if config.compile then 
    Builder.build_run_bench ~log_dir ~file ~mode_str:mode_str ~itr ~mutants_length:(List.length mutants) ~config;

  (* ターゲットの進捗バーを確定（改行しない） *)
  Bench_utils.Target_progress.print ~final:false prog
  
  end
  with 
  | Failure msg -> Format.eprintf "[Skip] %s@." msg

let () =
  let files_ref = ref [] in
  let modes_ref = ref [] in
  let list_ref = ref [] in
  let hash_ref = ref [] in
  let itr_ref = ref 0 in
  let static = ref false in
  let dynamize = ref false in
  let grift = ref false in
  let is_compare = ref false in
  let specs = [
    ("-m", Arg.String (fun s -> modes_ref := mode_of_string s :: !modes_ref), " Select mode");
    ("-i", Arg.Int (fun i -> itr_ref := i), " Specify itration");
    ("-c", Arg.Unit (fun () -> modes_ref := [SC; AC; BC; STATICC] @ !modes_ref), " Benchmarking all compile mode");
    ("--static", Arg.Unit (fun () -> static := true), " Benchmarking fully-static programs");
    ("--dynamize", Arg.Unit (fun () -> dynamize := true), " Benchmarking mutated programs");
    ("--grift", Arg.Unit (fun () -> grift := true), " Benchmarking on grift");
    ("--all", Arg.Unit (fun () -> dynamize := true; static := true; grift := true), " Benchmarking all (--static --dynamize --grift)");
    ("--paper", Arg.Unit (fun () -> modes_ref := [SC; AC; STATICC] @ !modes_ref; list_ref := [false];), " Banchmarking modes for paper (SLC, ALC, STATICC)");
    ("--eager", Arg.Unit (fun () -> list_ref := true :: !list_ref), " Run eager mode");
    ("--lazy", Arg.Unit (fun () -> list_ref := false :: !list_ref), " Run lazy mode");
    ("--hash", Arg.Unit (fun () -> hash_ref := true :: !hash_ref), " Run hash-consing mode");
    ("--no-hash", Arg.Unit (fun () -> hash_ref := false :: !hash_ref), " Run no-hash-consing mode");
    ("--compare", Arg.Unit (fun () -> is_compare := true), " Run church comparison mode without mutation");
    ]
  in
  Arg.parse specs (fun f -> files_ref := f :: !files_ref) " Usage: ./bench [file...] [-m mode]";

  (* 指定がなければ全部、あればそれを対象にする *)
  let list_modes = if !list_ref = [] then [true; false] else List.sort_uniq compare !list_ref in
  let hash_modes = if !hash_ref = [] then [true; false] else List.sort_uniq compare !hash_ref in
  let files = if !files_ref = [] then files else !files_ref in
  let modes = if !modes_ref = [] then modes else !modes_ref in
  let itr = if !itr_ref = 0 then itr else !itr_ref in

  (* 1. 前処理: 全ファイルを parse→mutate *)
  Format.fprintf Format.std_formatter "debug: parse->mutate\n";
  let prepared : (string * Syntax.ITGL.program list) list =
    List.map (fun file -> (file, parse_and_mutate ~is_compare:!is_compare file)) files 
  in
    Format.fprintf Format.std_formatter "debug: parse->mutate done\n";

  (* モード展開してターゲット配列を作る *)
  Format.fprintf Format.std_formatter "debug: making targets lists\n";
  let targets : (string * mode * bool * bool * Syntax.ITGL.program list) list =
    List.concat_map (fun (file, muts) ->
      List.concat_map (fun m -> 
        List.concat_map (fun eager -> 
          List.map (fun hash -> 
            (file, m, eager, hash, muts)
          ) hash_modes
        ) list_modes
      ) modes
    ) prepared
  in
  Format.fprintf Format.std_formatter "debug: making targets lists done\n";
  Format.fprintf Format.std_formatter "debug: targets lists number is %d\n" (List.length targets);
  Format.fprintf Format.std_formatter "debug: first target's mutants number is %d\n" (match targets with (_, _, _, _, h) :: _ -> List.length h | _ -> 0);
  let total_targets = List.length targets in

  (* 2. ログディレクトリ準備 *)
  let tm = localtime (time ()) in
  let timestamp =
    Printf.sprintf "%04d%02d%02d-%02d:%02d:%02d"
      (tm.tm_year + 1900) (tm.tm_mon + 1) tm.tm_mday (tm.tm_hour) (tm.tm_min) (tm.tm_sec)
  in
  let log_base_dir = "logs" in
  let ts_dir = Printf.sprintf "%s/%s" log_base_dir timestamp in
  
  (* `--compare` の場合はタイムスタンプの下にさらに `compare` ディレクトリを掘る *)
  let log_dir = 
    (* if !is_compare then Printf.sprintf "%s/compare" ts_dir else  *)
    ts_dir in

  if not (Sys.file_exists log_base_dir) then Core_unix.mkdir log_base_dir;
  if not (Sys.file_exists ts_dir) then Core_unix.mkdir ts_dir;
  if not (Sys.file_exists log_dir) then Core_unix.mkdir log_dir;

  (* 3. 実行: 各ターゲットを順番に *)
  Format.fprintf Format.std_formatter "debug: main iteration\n";
  begin if !dynamize then
    List.iteri (fun i (file, mode, eager, hash, mutants) ->
      if mode = STATICI || mode = STATICC then () else
      bench_file_mode
        ~log_dir
        ~itr
        ~ordinal:(i + 1)
        ~total_targets
        ~file
        ~mode
        ~eager
        ~hash
        ~mutants
    ) targets
  else () end;

  begin if !static then 
    let targets = List.map (fun (file, m, eager, hash, muts) -> (file ^ "_fs", m, eager, hash, [List.hd muts])) targets in
    List.iteri (fun i (file, mode, eager, hash, mutants) ->
      if mode = STATICI || mode = STATICC then 
      bench_file_mode
        ~log_dir
        ~itr
        ~ordinal:(i + 1)
        ~total_targets
        ~file
        ~mode
        ~eager:true
        ~hash:false
        ~mutants
      else
      bench_file_mode
        ~log_dir
        ~itr
        ~ordinal:(i + 1)
        ~total_targets
        ~file
        ~mode
        ~eager
        ~hash
        ~mutants
    ) targets
  else () end;

  begin if !grift then begin
    Format.fprintf Format.std_formatter "debug: grift\n";
    List.iter 
      (fun file -> 
        let i = Sys.command (Format.asprintf "python3 benchC/run_grift.py samples/src_grift/%s.grift samples/input/%s.txt -i %d" file file itr) in
        if i != 0 then failwith "python grift\n";
        ()
      ) 
      files;
    begin if !static then
      List.iter 
        (fun file -> 
          let i = Sys.command (Format.asprintf "python3 benchC/run_grift.py samples/src_grift/%s.grift samples/input/%s_fs.txt --static -i %d" file file itr) in
          if i != 0 then failwith "python grift (fully-static)\n";
          ()
        ) 
        files
    else () end
  end else () end;

  Printf.printf "\n";
  Printf.printf "debug: everything was done\n"
