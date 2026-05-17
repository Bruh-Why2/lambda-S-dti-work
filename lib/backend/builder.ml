open Format
open Config

exception Build_bad of string

let build_clang_cmd ?(log_dir="") ?(file="") ?(mode_str="") ?(src_files="") 
  ~config ~bench ~profile () =
  let intoB = config.intoB in
  let static = config.static in
  let eager = config.eager in
  let alt = config.alt in
  let hash = config.hash in
  let mode_var = (if intoB && not static then "-D CAST " else if alt && not static then "-D ALT " else "") in
  let lst_var = (if eager && not static then "-D EAGER " else "") in
  let hash_var = (if hash && not static then "-D HASH " else "") in
  let static_var = (if static then "-D STATIC " else "") in
  let profile_var = (if profile then "-D PROFILE " else "") in
  if bench then 
    asprintf "clang %s/bench/%s%s%s.c %s%s%s%s%slibC/*.c benchC/bench_json.c %s -o %s/bench/%s%s%s.out -lgc -lcjson -O3" (* -flto *) (* -falign-functions=32 -falign-loops=32 -falign-jumps=32 *)
      log_dir 
      file 
      mode_str
      (if profile then "_profile" else "")
      mode_var
      lst_var
      hash_var
      static_var
      profile_var
      src_files
      log_dir 
      file 
      mode_str
      (if profile then "_profile" else "")
  else match config.opt_file with
  | Some filename -> 
    asprintf "clang ../result_C/%s_out.c %s%s%s%s../libC/*.c -o ../result/%s.out -lgc -g3 -O3"
      filename
      mode_var
      lst_var
      hash_var
      static_var
      filename
  | None -> 
    (* clang result_C/stdin.c libC/*.c -o result/stdin.out -lgc -g3 -std=c2x -pg -O3 *)
    asprintf "clang result_C/stdin.c %s%s%s%slibC/*.c -o result/stdin.out -lgc -g3 -std=c2x -pg" (* TODO: -O3 *)
      mode_var
      lst_var
      hash_var
      static_var

let build_run c_code ~config = match config.opt_file with
  | Some filename ->
    (* ファイル入力モード *)
    let out_path = "../result_C/" ^ filename ^ "_out.c" in
    let oc = open_out out_path in
    Printf.fprintf oc "%s" c_code;
    close_out oc;
    (* print_debug "Generated C file: %s (Execution delegated)@." out_path *)
    let cmd = build_clang_cmd ~config ~bench:false ~profile:false () in
    if config.debug then fprintf err_formatter "@.%s@." cmd;
    let i = Sys.command cmd in
    if i != 0 then raise @@ Build_bad "clang fail";
    let cmd = ("../result/" ^ filename ^ ".out") in
    if config.debug then fprintf err_formatter "@.%s@." cmd;
    let i = Sys.command cmd in
    if i != 0 then raise @@ Build_bad ".out fail";
    ()
  | None ->
    (* 標準入力モード *)
    let out_path = "result_C/stdin.c" in
    let oc = open_out out_path in
    Printf.fprintf oc "%s" c_code;
    close_out oc;
    (* print_debug "%s" (Compiler.build_cmd_for_stdin ()); *)
    let cmd = build_clang_cmd ~config ~bench:false ~profile:false () in
    if config.debug then fprintf err_formatter "@.%s@." cmd;
    let i = Sys.command cmd in
    if i != 0 then raise @@ Build_bad "clang fail";
    let cmd = "result/stdin.out" in
    if config.debug then fprintf err_formatter "@.%s@." cmd;
    let i = Sys.command cmd in
    if i != 0 then raise @@ Build_bad ".out fail";
    ()

let build_run_bench ~log_dir ~file ~mode_str ~itr ~mutants_length ~config =
  let src_files = asprintf "%s/%s/%s*.c" log_dir mode_str file in
  (* _mutants.h 生成 *)
  let oc = open_out (asprintf "%s/bench/%s%s_mutants.h" log_dir file mode_str) in
  Printf.fprintf oc "#ifndef MUTANTS_H\n#define MUTANTS_H\n\n";
  let rec print_itr n =
    if n = mutants_length + 1 then ()
    else (Printf.fprintf oc "int mutant%d(void);\nint set_tys%d(void);\n" n n; print_itr (n + 1))
  in print_itr 1;
  Printf.fprintf oc "#endif";
  close_out oc;
  (* .c 生成 *)
  let oc = open_out (asprintf "%s/bench/%s%s.c" log_dir file mode_str) in
  Printf.fprintf oc "%s\n%s\n%s\n%s\n%s"
    (asprintf "#include <stdio.h>\n#include <gc.h>\n#include <sys/time.h>\n#include <sys/resource.h>\n#include \"../../../libC/types.h\"\n#include \"../../../benchC/bench_json.h\"\n#include \"%s%s_mutants.h\"\n#ifdef HASH\n#include \"../../../libC/crc.h\"\n#endif\n" file mode_str)
    "#define GC_INITIAL_HEAP_SIZE 1048576\n"
    (asprintf "#define MUTANTS_LENGTH %d\n#define ITR %d\n" mutants_length itr)
    "#ifndef STATIC\nrange *range_list;\n#endif\nstatic double times[MUTANTS_LENGTH][ITR];\nint i;\nstruct rusage start_usage, end_usage;\n"
    "int main(){\nGC_INIT();\n";
  let rec print_itr n =
    if n = mutants_length + 1 then ()
    else begin 
      Printf.fprintf oc "for (i = 0; i<ITR; i++){\n\n#ifdef HASH\nclear_crc_caches();\n#endif\ngetrusage(RUSAGE_SELF, &start_usage);\nmutant%d();\ngetrusage(RUSAGE_SELF, &end_usage);\ntimes[%d][i] = (double)(end_usage.ru_utime.tv_sec - start_usage.ru_utime.tv_sec) + (double)(end_usage.ru_utime.tv_usec - start_usage.ru_utime.tv_usec) * 1e-6;\nrewind(stdin);\n}\nfprintf(stderr, \"mutant%d done. \");\nfflush(stdout);\n"
       n (n - 1) n;
      print_itr (n + 1)
    end
  in print_itr 1;
  Printf.fprintf oc "return update_jsonl_file(\"%s/%s_%s.jsonl\", *times, MUTANTS_LENGTH, ITR);\n}" log_dir mode_str file;
  close_out oc;
  (* _profile.c 生成 *)
  let oc = open_out (asprintf "%s/bench/%s%s_profile.c" log_dir file mode_str) in
  Printf.fprintf oc "%s\n%s\n%s\n%s"
    (asprintf "#include <stdio.h>\n#include <gc.h>\n#include \"../../../libC/types.h\"\n#include \"../../../benchC/bench_json.h\"\n#include \"%s%s_mutants.h\"\n#ifdef HASH\n#include \"../../../libC/crc.h\"\n#endif\n" file mode_str)
    (asprintf "#define MUTANTS_LENGTH %d\n" mutants_length)
    "#ifndef STATIC\nrange *range_list;\n#endif\nstatic int gc_counts[MUTANTS_LENGTH], cast_counts[MUTANTS_LENGTH], inference_counts[MUTANTS_LENGTH], longest[MUTANTS_LENGTH];\nint i;\nint gc_num, gc_tmp, current_inference, current_cast, current_longest, current_compose, compose_cached, current_alloc, new_crc_num, alloc_hash, find_ty_num;\n"
    "int main(){\nGC_INIT();\n";
  let rec print_itr n =
    if n = mutants_length + 1 then ()
    else begin 
      Printf.fprintf oc "\n#ifdef HASH\nclear_crc_caches();\n#endif\nmutant%d();\ngc_tmp = GC_get_total_bytes();\ngc_counts[%d] = gc_tmp - gc_num;\ngc_num = gc_tmp;\ncast_counts[%d] = current_cast;\ninference_counts[%d] = current_inference;\nlongest[%d] = current_longest;\ncurrent_cast = 0;\ncurrent_inference = 0;\ncurrent_longest = 0;\nrewind(stdin);\nfprintf(stderr, \"mutant%d done. \");\nfflush(stdout);\n"
       n (n - 1) (n - 1) (n - 1) (n - 1) n;
      print_itr (n + 1)
    end
  in print_itr 1;
  Printf.fprintf oc "return update_jsonl_file_profile(\"%s/%s_%s.jsonl\", gc_counts, cast_counts, inference_counts, longest, MUTANTS_LENGTH);\n}" log_dir mode_str file;
  close_out oc;
  (* build *)
  let cmd = build_clang_cmd ~config ~bench:true ~log_dir ~file ~mode_str ~src_files ~profile:false () in
  fprintf std_formatter "@.%s@." cmd;
  let i = Sys.command cmd in
  if i != 0 then raise @@ Build_bad "clang(for time) fail";
  let cmd = build_clang_cmd ~config ~bench:true ~log_dir ~file ~mode_str ~src_files ~profile:true () in
  fprintf std_formatter "@.%s@." cmd;
  let i = Sys.command cmd in
  if i != 0 then raise @@ Build_bad "clang(for profile) fail";
  (* run *)
  let cmd = asprintf "%s/bench/%s%s.out < samples/input/%s.txt > /dev/null" log_dir file mode_str file in
  fprintf std_formatter "%s@." cmd;
  let i = Sys.command cmd in
  if i != 0 then raise @@ Build_bad ".out(for time) fail";
  let cmd = asprintf "%s/bench/%s%s_profile.out < samples/input/%s.txt > /dev/null" log_dir file mode_str file in
  fprintf std_formatter "%s@." cmd;
  let i = Sys.command cmd in
  if i != 0 then raise @@ Build_bad ".out(for profile) fail";
  ()