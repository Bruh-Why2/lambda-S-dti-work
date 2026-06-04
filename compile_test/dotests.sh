#!/bin/bash

# スクリプトのあるディレクトリに移動（CIのどこから呼んでも動くようにする）
cd "$(dirname "$0")"

# エラーがあったかを記録するフラグ
FAILED=0

# テスト実行用の関数
run_test() {
  file="$1"
  expected="$2"
  skip_flag="$3"

  # オプションのリスト
  declare -a options_list=("-c" "-c -a" "-c -b" "-c --static")

  for opt in "${options_list[@]}"; do

  	if [[ "$opt" == *"--static"* ]] && [[ "$skip_flag" == "skip_static" ]]; then
      echo "Testing $file ($opt) ... SKIPPED (As requested)"
      continue  # この回のループを飛ばして次へ
    fi

    echo -n "Testing $file ($opt) ... "

    # コマンド実行
    # $opt をダブルクォーテーションで囲まないことで、複数の引数として展開させる
    actual=$(lSdti "$file" $opt 2>&1)

    if [ "$actual" = "$expected" ]; then
      echo "OK"
    else
      echo "FAILED"
      echo "  Options:  $opt"
      echo "  Expected: \"$expected\""
      echo "  Got:      \"$actual\""
      FAILED=1
    fi
  done
}

# --- 以下、テストケース定義 ---

# --- minCaml tests without float, tuple, and array (https://github.com/esumii/min-caml) ---
  # omitting some "rec", introducing dummy variable name instead of _
run_test "ack.ml" "8189"
run_test "adder.ml" "10"
run_test "adder2.ml" "35"
run_test "cls-bug.ml" "912"
run_test "cls-bug2.ml" "9876543210" # using a list instead of an array
run_test "cls-rec.ml" "1230"
run_test "cls-reg-bug.ml" "$(printf "55\n")" # tuples are curried
run_test "even-odd.ml" "false" # introducing true and false
run_test "fib.ml" "832040"
# run_test "float.ml" : float
run_test "funcomp.ml" "247"
run_test "gcd.ml" "2700"
# run_test "inprod*.ml" : tuple
run_test "join-reg.ml" "912"
run_test "join-reg2.ml" "789"
run_test "join-stack.ml" "1037"
run_test "join-stack2.ml" "246"
run_test "join-stack3.ml" "912"
# run_test "matmul*.ml" : array
run_test "non-tail-if.ml" "-10" # using int nums instead of "truncate (float)"
run_test "non-tail-if2.ml" "80238" # using a list instead of an array
run_test "print.ml" "$(printf "123\ntrue")" # test other prints (print_newline, print_bool)
run_test "shuffle.ml" "214563"
run_test "spill.ml" "-431"
run_test "spill2.ml" "77880" # using a list instead of an array
run_test "spill3.ml" "1617"
run_test "sum-tail.ml" "50005000"
run_test "sum.ml" "50005000"
# --- examples on ldti paper (https://dl.acm.org/doi/pdf/10.1145/3290331) ---
run_test "example1_success.ml" "5" "skip_static"
run_test "example1_fail.ml" "$(printf "Blame on the expression side:\nFile \"example1_fail.ml\", line 1, character 25 -- line 1, character 26")" "skip_static"
run_test "example2.ml" "2" "skip_static"
run_test "example3.ml" "false" "skip_static"
# --- original tests ---
run_test "church_4.ml" "4"
run_test "cast-abort.ml" "$(printf "Blame on the expression side:\nFile \"cast-abort.ml\", line 2, character 10 -- line 2, character 15")" "skip_static"
run_test "many_coerce.ml" "4" "skip_static"
run_test "repeat_f_dyn.ml" "4" "skip_static"
run_test "repeat_x_dyn.ml" "4" "skip_static"
run_test "repeat.ml" "4"
# run_test "lst.ml" 
# run_test "cast_coercion_difference.ml" "$(printf "Blame on the expression side:\nFile \"cast_coercion_difference.ml\", line 1, character 28 -- line 1, character 33")" "skip_static"
# run_test "dummy_label.ml"
# run_test "occur_check.ml"
# --- issue 1 ---
# run_test "anoter_name.ml" "skip_static"
# --- issue 2 ---
run_test "issue2_example1.ml" "3" "skip_static"
run_test "issue2_example2.ml" "$(printf "Blame on the expression side:\nFile \"issue2_example2.ml\", line 1, character 33 -- line 1, character 81")" "skip_static"


# --- 判定結果 ---

if [ $FAILED -eq 1 ]; then
  echo "Some tests failed."
  exit 1
else
  echo "All tests passed."
  exit 0
fi