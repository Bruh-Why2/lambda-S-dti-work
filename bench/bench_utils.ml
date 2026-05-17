open Unix
open Lambda_S_dti

(* Measurement options (source-controlled) *)
type mem_mode = Off | Fast | Corebench
let mem_mode = Off          (* Off | Fast | Corebench *)
let fast_runs = 10                      (* Fast モードの1ミュータントあたりの実行回数 *)
let cb_quota_sec = 0.15                 (* Corebench モード: 1 テストあたりの時間上限(秒) *)
let cb_stabilize_gc_between_runs = false
let cb_silence_stdout = true            (* Core_benchの標準出力(推定時間など)を抑止 *)
let show_progress = true                (* 進捗バーを標準出力に出すか *)

(* 出力フォーマット：Text（従来）, Json（1ファイルに配列）, JsonLines（NDJSON） *)
type out_mode = Text | Json | JsonLines
let out_mode : out_mode = JsonLines  (* 推奨: NDJSON。1行=1ミュータント *)

module J = struct
  (* open Yojson.Safe *)

  let strf fmt = Format.asprintf fmt

  let opt f = function None -> `Null | Some x -> f x
  let float_opt = opt (fun x -> `Float x)
  let float x = `Float x
  let int x = `Int x
  let bool b = `Bool b
  let str s = `String s
  let list xs = `List xs
  let obj xs = `Assoc xs

  let to_channel_ln oc (j:Yojson.Safe.t) =
    Yojson.Safe.to_channel oc j; output_char oc '\n'
end

(* === Core_bench を使った alloc/gc/time 抽出 === *)
open Core
module Bench = Core_bench.Bench
module AR   = Bench.Analysis_result
module Reg  = AR.Regression
module Coef = AR.Coefficient
module Var  = Bench.Variable

(* core_bench が出す標準出力を一時的に /dev/null へ退避 *)
let with_silenced_stdout (f : unit -> 'a) : 'a =
  if not cb_silence_stdout then f ()
  else begin
    Out_channel.flush stdout; Out_channel.flush stderr;
    let saved   = Core_unix.dup Core_unix.stdout in
    let devnull = Core_unix.openfile "/dev/null" ~mode:[Core_unix.O_WRONLY] ~perm:0o666 in
    Core_unix.dup2 ~src:devnull ~dst:Core_unix.stdout ();
    Core_unix.close devnull;
    match f () with
    | v ->
        Out_channel.flush stdout;
        Core_unix.dup2 ~src:saved ~dst:Core_unix.stdout ();
        Core_unix.close saved;
        v
    | exception exn ->
        Out_channel.flush stdout;
        Core_unix.dup2 ~src:saved ~dst:Core_unix.stdout ();
        Core_unix.close saved;
        raise exn
  end

module Fast_alloc = struct
  let bytes_per_word =
    match Core.Word_size.word_size with
    | Core.Word_size.W32 -> 4
    | Core.Word_size.W64 -> 8

  let measure_and_log ~fmt ~label ~runs (thunk: unit -> unit) =
    (* Blame 等は事前検出してスキップ *)
    let ok =
      try thunk (); true with
      | Syntax.Blame _ ->
          Pipeline.log_section fmt "mem(fast) skipped"; Format.fprintf fmt "reason: Blame (C)@."; false
      (* | LambdaCSPolyMP.EvalS.Blame _ ->
          Pipeline.log_section fmt "mem(fast) skipped"; Format.fprintf fmt "reason: Blame (S)@."; false *)
      | exn ->
          Pipeline.log_section fmt "mem(fast) skipped";
          Format.fprintf fmt "reason: exception = %s@." (Core.Exn.to_string exn);
          false
    in
    if not ok then () else begin
      Gc.full_major ();
      let t0 = Core.Time_ns.now () in
      let s0 = Gc.quick_stat () in
      for _i = 1 to runs do thunk () done;
      Gc.full_major ();
      let s1 = Gc.quick_stat () in
      let dt_ns = Core.Time_ns.Span.to_ns (Core.Time_ns.diff (Core.Time_ns.now ()) t0) in
      let runs_f = Float.of_int runs in
      let per_run_ns = dt_ns /. runs_f in
      let fsub a b = a -. b in
      let words_minor = fsub s1.minor_words s0.minor_words /. runs_f in
      let words_major = fsub s1.major_words s0.major_words /. runs_f in
      let words_prom  = fsub s1.promoted_words s0.promoted_words /. runs_f in
      let gc_minor = float (s1.minor_collections - s0.minor_collections) /. runs_f in
      let gc_major = float (s1.major_collections - s0.major_collections) /. runs_f in
      let gc_comp  = float (s1.compactions        - s0.compactions)        /. runs_f in

      Pipeline.log_section fmt (Printf.sprintf "mem(fast) per run; runs=%d" runs);
      Format.fprintf fmt
        "@[<v2>%s@,\
         time:  %.0f ns/Run@,\
         alloc: minor=%.0f words/Run  major=%.0f words/Run  promoted=%.0f words/Run@,\
         alloc(bytes): minor=%.0f B/Run  major=%.0f B/Run  promoted=%.0f B/Run@,\
         gc:   minor=%.3f /Run  major=%.3f /Run  compactions=%.3f /Run@]@."
        label
        per_run_ns
        words_minor words_major words_prom
        (words_minor *. float bytes_per_word)
        (words_major *. float bytes_per_word)
        (words_prom  *. float bytes_per_word)
        gc_minor gc_major gc_comp
    end
end

module CB = struct
  let bytes_per_word =
    match Core.Word_size.word_size with
    | Core.Word_size.W32 -> 4
    | Core.Word_size.W64 -> 8

  let run_config =
    Bench.Run_config.create
      ~quota:(Bench.Quota.Span (Core.Time_float.Span.of_sec cb_quota_sec))
      ~stabilize_gc_between_runs:cb_stabilize_gc_between_runs
      ()

  let coef_per_run (reg : Reg.t) : float option =
    Array.find_map (AR.Regression.coefficients reg) ~f:(fun (c : Coef.t) ->
      match Coef.predictor c with
      | `Runs -> Some (Coef.estimate c)
      | _ -> None
    )

  let bench_one_and_log ~fmt ~(cb_label:string) (thunk: unit -> unit) =
    (* プレフライトで例外検出してスキップ *)
    let ok =
      try thunk (); true with
      | Syntax.Blame _ ->
          Pipeline.log_section fmt "core_bench (skipped)"; Format.fprintf fmt "reason: Blame (C)@."; false
      (* | LambdaCSPolyMP.EvalS.Blame _ ->
          Pipeline.log_section fmt "core_bench (skipped)"; Format.fprintf fmt "reason: Blame (S)@."; false *)
      | exn ->
          Pipeline.log_section fmt "core_bench (skipped)";
          Format.fprintf fmt "reason: exception = %s@." (Core.Exn.to_string exn);
          false
    in
    if not ok then () else begin
      let test = Bench.Test.create ~name:cb_label (fun () -> thunk ()) in
      let do_measure () =
        let ms = Bench.measure ~run_config [test] in
        match ms with
        | [m] -> Bench.analyze ~analysis_configs:Bench.Analysis_config.default m
        | _   -> Error (Error.of_string "measurement failed")
      in
      let analyzed =
        if cb_silence_stdout then with_silenced_stdout do_measure else do_measure ()
      in
      match analyzed with
      | Ok res ->
          let regs = AR.regressions res in
          let pick (resp : Var.t) : float option =
            Array.find_map regs ~f:(fun r ->
              if Core.Poly.(Reg.responder r = resp)
              then coef_per_run r
              else None)
          in
          let nanos    = pick `Nanos in
          let a_minor  = pick `Minor_allocated in
          let a_major  = pick `Major_allocated in
          let a_prom   = pick `Promoted in
          let gc_minor = pick `Minor_collections in
          let gc_major = pick `Major_collections in
          let gc_comp  = pick `Compactions in
          let w2b = Option.map ~f:(fun w -> w *. float_of_int bytes_per_word) in

          Pipeline.log_section fmt (Printf.sprintf "core_bench (per run; quota=%.2fs; stabilize=%b)"
                             cb_quota_sec cb_stabilize_gc_between_runs);
          Format.fprintf fmt
            "@[<v2>%s@,\
             time:  %s ns/Run@,\
             alloc: minor=%s words/Run  major=%s words/Run  promoted=%s words/Run@,\
             alloc(bytes): minor=%s B/Run  major=%s B/Run  promoted=%s B/Run@,\
             gc:   minor=%s /Run  major=%s /Run  compactions=%s /Run@]@."
            cb_label
            (Option.value_map nanos    ~default:"-" ~f:(Printf.sprintf "%.0f"))
            (Option.value_map a_minor  ~default:"-" ~f:(Printf.sprintf "%.0f"))
            (Option.value_map a_major  ~default:"-" ~f:(Printf.sprintf "%.0f"))
            (Option.value_map a_prom   ~default:"-" ~f:(Printf.sprintf "%.0f"))
            (Option.value_map (w2b a_minor) ~default:"-" ~f:(Printf.sprintf "%.0f"))
            (Option.value_map (w2b a_major) ~default:"-" ~f:(Printf.sprintf "%.0f"))
            (Option.value_map (w2b a_prom ) ~default:"-" ~f:(Printf.sprintf "%.0f"))
            (Option.value_map gc_minor ~default:"-" ~f:(Printf.sprintf "%.3f"))
            (Option.value_map gc_major ~default:"-" ~f:(Printf.sprintf "%.3f"))
            (Option.value_map gc_comp  ~default:"-" ~f:(Printf.sprintf "%.3f"))
      | Error _ ->
          Pipeline.log_section fmt "core_bench (analysis failed)";
          Format.fprintf fmt "n/a@."
    end
end

(* -------- Progress UI -------------------------------------------------- *)
(* -------- Target Progress UI (per file x mode) ------------------------- *)
module Target_progress = struct
  type t = {
    label : string;
    total : int;
    mutable done_ : int;
    start_t : float;
    width : int;
  }

  let create ~label ~total ~ordinal ~total_targets =
    (* 見出しを出してからバーを開始 *)
    Printf.printf "\n==> [%d/%d] %s (%d mutants)\n%!"
      ordinal total_targets label total;
    { label; total; done_ = 0; start_t = gettimeofday (); width = 28 }

  let print ?(final=false) (p:t) =
    if show_progress then begin
      let now     = gettimeofday () in
      let done_i  = p.done_ in
      let total_i = max 1 p.total in
      let frac    = Float.of_int done_i /. Float.of_int total_i in
      let elapsed = now -. p.start_t in
      let eta     = if Float.(frac > 0.0) then elapsed *. (1.0 -. frac) /. frac else Float.nan in
      let filled  = Int.of_float (Float.min 1.0 frac *. Float.of_int p.width) in
      let bar     = (String.make filled '#') ^ (String.make (p.width - filled) '-') in
      Printf.printf "\r%-16s [%s] %d/%d (%.1f%%)  t=%.1fs  ETA:%s%!"
        p.label bar done_i total_i (100. *. frac) elapsed
        (if Float.is_nan eta then " ?" else Printf.sprintf " %.1fs" eta);
      if final then Printf.printf "\n%!";
    end

  let tick (p:t) =
    p.done_ <- p.done_ + 1;
    print p
end

(* -------- Measurement -------------------------------------------------- *)
let measure_execution_time f itr =
  let result = ref [] in
  List.iter
    (List.range 0 itr)
    ~f:(fun _ ->
        let start_time = gettimeofday () in
        let v = f () in
        let end_time = gettimeofday () in
        let elapsed_time = end_time -. start_time in
        result := (v, elapsed_time) :: !result
      );
  !result

let measure_mem_to_json ~label (thunk: unit -> unit) : Yojson.Safe.t option =
  match mem_mode with
  | Off -> None
  | Fast ->
      (* Fast_alloc を呼びなおして値を作る（ログは emit_text_log のときだけ） *)
      let ok =
        try thunk (); true with
        | Syntax.Blame _ -> false
        (* | LambdaCSPolyMP.EvalS.Blame _ -> false *)
        | _ -> false
      in
      if not ok then None else begin
        Gc.full_major ();
        let t0 = Core.Time_ns.now () in
        let s0 = Gc.quick_stat () in
        for _i = 1 to fast_runs do thunk () done;
        Gc.full_major ();
        let s1 = Gc.quick_stat () in
        let dt_ns = Core.Time_ns.Span.to_ns (Core.Time_ns.diff (Core.Time_ns.now ()) t0) in
        let runs_f = float fast_runs in
        let per_run_ns = dt_ns /. runs_f in
        let fsub a b = a -. b in
        let words_minor = fsub s1.minor_words s0.minor_words /. runs_f in
        let words_major = fsub s1.major_words s0.major_words /. runs_f in
        let words_prom  = fsub s1.promoted_words s0.promoted_words /. runs_f in
        let gc_minor = float (s1.minor_collections - s0.minor_collections) /. runs_f in
        let gc_major = float (s1.major_collections - s0.major_collections) /. runs_f in
        let gc_comp  = float (s1.compactions        - s0.compactions)        /. runs_f in
        let bytes_per_word =
          match Core.Word_size.word_size with
          | Core.Word_size.W32 -> 4
          | Core.Word_size.W64 -> 8
        in
        let open J in
        Some (obj [
          ("mode", str "fast");
          ("runs", int fast_runs);
          ("time_ns_per_run", float per_run_ns);
          ("alloc_words_per_run",
            obj [("minor", float words_minor); ("major", float words_major); ("promoted", float words_prom)]);
          ("alloc_bytes_per_run",
            obj [("minor", float (words_minor *. float_of_int bytes_per_word));
                 ("major", float (words_major *. float_of_int bytes_per_word));
                 ("promoted", float (words_prom  *. float_of_int bytes_per_word))]);
          ("gc_per_run",
            obj [("minor", float gc_minor); ("major", float gc_major); ("compactions", float gc_comp)]);
        ])
      end
  | Corebench ->
      let open Core in
      let open Bench in
      let open J in
      let test = Test.create ~name:label (fun () -> thunk ()) in
      let do_measure () =
        let ms = Bench.measure ~run_config:CB.run_config [test] in
        match ms with
        | [m] -> Bench.analyze ~analysis_configs:Bench.Analysis_config.default m
        | _   -> Error (Error.of_string "measurement failed")
      in
      let analyzed =
        if cb_silence_stdout then with_silenced_stdout do_measure else do_measure ()
      in
      match analyzed with
      | Error _ -> None
      | Ok res ->
          let regs = AR.regressions res in
          let coef_per_run (reg : Reg.t) : float option =
            Array.find_map (AR.Regression.coefficients reg) ~f:(fun (c : Coef.t) ->
              match Coef.predictor c with
              | `Runs -> Some (Coef.estimate c)
              | _ -> None)
          in
          let pick (resp : Var.t) : float option =
            Array.find_map regs ~f:(fun r ->
              if Core.Poly.(Reg.responder r = resp) then coef_per_run r else None)
          in
          let nanos    = pick `Nanos in
          let a_minor  = pick `Minor_allocated in
          let a_major  = pick `Major_allocated in
          let a_prom   = pick `Promoted in
          let gc_minor = pick `Minor_collections in
          let gc_major = pick `Major_collections in
          let gc_comp  = pick `Compactions in
          let bytes_per_word =
            match Core.Word_size.word_size with
            | Core.Word_size.W32 -> 4
            | Core.Word_size.W64 -> 8
          in
          let w2b = Option.map ~f:(fun w -> w *. float_of_int bytes_per_word) in
          Some (obj [
            ("mode", str "corebench");
            ("quota_sec", J.float cb_quota_sec);
            ("stabilize_gc_between_runs", J.bool cb_stabilize_gc_between_runs);
            ("time_ns_per_run", float_opt nanos);
            ("alloc_words_per_run",
              obj [("minor", float_opt a_minor); ("major", float_opt a_major); ("promoted", float_opt a_prom)]);
            ("alloc_bytes_per_run",
              obj [("minor", float_opt (w2b a_minor));
                   ("major", float_opt (w2b a_major));
                   ("promoted", float_opt (w2b a_prom))]);
            ("gc_per_run",
              obj [("minor", float_opt gc_minor); ("major", float_opt gc_major); ("compactions", float_opt gc_comp)]);
          ])