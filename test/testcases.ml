let constants = [
  ["1", "int", "1", "1", "1", "1"];
  ["true", "bool", "true", "true", "1", "1"];
  ["()", "unit", "()", "()", "0", "0"];
]

let unary_ops = [
  ["-1", "int", "-1", "-1", "-1", "-1"];
  ["--2", "int", "2", "2", "2", "2"];
  ["let x = 1 in x-1", "int", "0", "0", "0", "0"];
]

let binary_ops = [
  ["1 + 2 + 3", "int", "6", "6", "6", "6"];
  ["3 * 2 + 3", "int", "9", "9", "9", "9"];
  ["3 * (2 + 3)", "int", "15", "15", "15", "15"];
  ["3 = 3", "bool", "true", "true", "1", "1"];
  ["10 / 2", "int", "5", "5", "5", "5"];
  ["10 mod 3", "int", "1", "1", "1", "1"];
  ["2 <> 3", "bool", "true", "true", "1", "1"];
  ["3 <= 3", "bool", "true", "true", "1", "1"];
  ["4 >= 5", "bool", "false", "false", "0", "0"];
  ["true && false", "bool", "false", "false", "0", "0"];
  ["false || true", "bool", "true", "true", "1", "1"];
  ["(1 < 2) && (3 > 4)", "bool", "false", "false", "0", "0"];
  ["false && (((true:?):int):?)", "bool", "false", "false", "0", "0"];
]

let type_ascription = [
  ["(2 : ?)", "?", "2: int => ?", "2<<id{int};int!>>", "2: int => ?", "2<<id{int};int!>>"];
  ["((2: ?): int)", "int", "2", "2", "2", "2"];
]

let if_then_else = [
  ["if 2 < 3 then 4 else 5", "int", "4", "4", "4", "4"];
  ["if 3 < 3 then 4 else 5", "int",  "5", "5", "5", "5"];
  ["if true then 1, 2 else 3, 4", "int * int", "(1, 2)", "(1, 2)", "(1, 2)", "(1, 2)"];
]

let let_definition = [
  ["let x = 3 + 4 in x", "int", "7", "7", "7", "7"];
  ["let x = 3 + 4 in let y = 1 in let x = 2 in y + x", "int", "3", "3", "3", "3"];
  ["let x = 10 in let x = 100 in x * x", "int", "10000", "10000", "10000", "10000"];
]

let abstraction = [
  ["fun x -> x + 1", "int -> int", "<fun>", "<fun>", "<fun>", "<fun>"];
  ["fun (x:?) -> x + 1", "? -> int", "<fun>", "<fun>", "<fun>", "<fun>"];
  ["fun x -> x", "'a -> 'a", "<fun>", "<fun>", "<fun>", "<fun>"];
  ["fun (x: unit) -> ()", "unit -> unit", "<fun>", "<fun>", "<fun>", "<fun>"];
  ["fun (x: int -> bool) -> ()", "(int -> bool) -> unit", "<fun>", "<fun>", "<fun>", "<fun>"];
  ["fun (x: int -> bool -> int) -> ()", "(int -> bool -> int) -> unit", "<fun>", "<fun>", "<fun>", "<fun>"];
  ["fun (x: (int -> bool) -> int) -> ()", "((int -> bool) -> int) -> unit", "<fun>", "<fun>", "<fun>", "<fun>"];
  ["fun (x:'a) (y:'b) -> x y", "('a -> 'b) -> 'a -> 'b", "<fun>", "<fun>", "<fun>", "<fun>"];
  ["fun (x: int * bool -> int) -> 0", "(int * bool -> int) -> int", "<fun>", "<fun>", "<fun>", "<fun>"];
]

let application = [
  ["(fun x -> x + 1) 3", "int", "4", "4", "4", "4"];
  ["(fun (x:?) -> x + 1) 3", "int", "4", "4", "4", "4"];
  ["(fun (x:?) -> x + 1) false", "int", "blame+", "blame+", "blame+", "blame+"];
  ["(fun x y -> x + y) 3 4", "int", "7", "7", "7", "7"];
  ["(fun (x:?) -> x 2) (fun y -> y)", "?", "2: int => ?", "2<<id{int};int!>>", "2: int => ?", "2<<id{int};int!>>"];
  ["(fun (x:?) -> x 2) (fun (y: int) -> y)", "?", "2: int => ?", "2<<id{int};int!>>", "2: int => ?", "2<<id{int};int!>>"];
  ["(fun (x:?) -> x 2) (fun y -> true)", "?", "true: bool => ?", "true<<id{bool};bool!>>", "1: bool => ?", "1<<id{bool};bool!>>"];
  ["(fun (x:?) -> x) (fun y -> true)", "?", "<fun>: (? -> ?) => ?", "<fun><<'a?p->(id{bool};bool!);(? -> ?)!>>", "<fun>: (? -> ?) => ?", "<fun><<'a?p->(id{bool};bool!);(? -> ?)!>>"];
  ["(fun x -> 1 + ((fun (y:?) -> y) x)) 2", "int", "3", "3", "3", "3"];
  ["(fun (x: int * ?) -> x) (1, true)", "int * ?", "(1, true: bool => ?)", "(1, true)<<id{int}*(id{bool};bool!)>>", "(1, 1: bool => ?)", "(1, 1)<<id{int}*(id{bool};bool!)>>"];
  ["(fun (x: ?) -> x) (1, true)", "?", "(1: int => ?, true: bool => ?): (? * ?) => ?", "(1, true)<<(id{int};int!)*(id{bool};bool!);(? * ?)!>>", "(1: int => ?, 1: bool => ?): (? * ?) => ?", "(1, 1)<<(id{int};int!)*(id{bool};bool!);(? * ?)!>>"];
  ["(fun (x: ?) -> (x : int * int)) (1, 2)", "int * int", "(1, 2)", "(1, 2)", "(1, 2)", "(1, 2)"];
  ["(fun (x: ?) -> (x : int * int)) (1, true)", "int * int", "blame+", "(1, true)<<id{int}*⊥{bool,p,int}>>", "blame+", "(1, 1)<<id{int}*⊥{bool,p,int}>>"];
]

let sequence = [
  ["(); 1 + 2", "int", "3", "3", "3", "3"];
  ["(():?); 1 + 2", "int", "3", "3", "3", "3"];
]

let dti = [
  ["(fun (f:?) -> f 2) (fun y -> y)", "?", "2: int => ?", "2<<id{int};int!>>", "2: int => ?", "2<<id{int};int!>>"];
  ["(fun (f:?) -> f 2) ((fun x -> x) ((fun (y:?) -> y) (fun z -> z + 1)))", "?", "3: int => ?", "3<<id{int};int!>>", "3: int => ?", "3<<id{int};int!>>"];
  ["(fun (x:?) -> (fun y -> y) x) (fun (z:?) -> z + 1) 3", "int", "4", "4", "4", "4"];
  ["(fun x -> x) ((fun (y:?) -> y) (fun x -> x + 1)) 1", "int", "2", "2", "2", "2"];
  ["(fun (f:?) -> f (); f true) (fun (x:?) -> x)", "?", "true: bool => ?", "true<<id{bool};bool!>>", "1: bool => ?", "1<<id{bool};bool!>>"];
  ["(fun (f:?) -> f (); f true) (fun x -> x)", "?", "blame-", "blame-", "blame-", "blame-"];
  ["(fun (f:?) -> let d = f 2 in f true) (fun (x:?) -> x)", "?", "true: bool => ?", "true<<id{bool};bool!>>", "1: bool => ?", "1<<id{bool};bool!>>"];
  ["(fun (f:?) -> let d = f 2 in f true) (fun x -> x)", "?", "blame-", "blame-", "blame-", "blame-"];
]

let let_poly = [
  ["let s = fun x y z -> x z (y z) in s", "('a -> 'b -> 'c) -> ('a -> 'b) -> 'a -> 'c", "<fun>", "<fun>", "<fun>", "<fun>"];
  ["let k = fun x y -> x in k", "'a -> 'b -> 'a", "<fun>", "<fun>", "<fun>", "<fun>"];
  ["let s = fun x y z -> x z (y z) in let k = fun x y -> x in s k k", "'a -> 'a", "<fun>", "<fun>", "<fun>", "<fun>"];
  ["let s = fun x y z -> x z (y z) in let k = fun x y -> x in s k k 1", "int", "1", "1", "1", "1"];
  ["let s = fun (x:?) (y:?) (z:?) -> x z (y z) in let k = fun x y -> x in s k k 1", "?", "1: int => ?", "1<<id{int};int!>>", "1: int => ?", "1<<id{int};int!>>"];
  ["let succ x = x + 1 in let twice f x = f (f x) in twice succ 1", "int", "3", "3", "3", "3"];
  ["let id x = x in let did (x:?) = x in let succ x = x + 1 in (fun (x:?) -> x 1) (id (did succ))", "?", "2: int => ?", "2<<id{int};int!>>", "2: int => ?", "2<<id{int};int!>>"];
  ["let id x = x in id (); id true", "bool",  "true", "true", "1", "1"];
  ["let g = fun x -> ((fun y -> y) : ?->?) x in g (); g 3", "?", "3: int => ?", "3<<id{int};int!>>", "3: int => ?", "3<<id{int};int!>>"];
  ["let f = fun x -> 1 + ((fun (y:?) -> y) x) in 2", "int", "2", "2", "2", "2"];
]

let let_poly_toplevel = [
  [
    "let g = fun x -> ((fun y -> y) : ?->?) x", "'a -> ?", "<fun>", "<fun>", "<fun>", "<fun>";
    "g (); g true", "?", "true: bool => ?", "true<<id{bool};bool!>>", "1: bool => ?", "1<<id{bool};bool!>>";
  ];
  [
    "let f = (fun x -> x) (fun y -> y)", "'a -> 'a", "<fun>", "<fun>", "<fun>", "<fun>";
    "f", "'a -> 'a", "<fun>", "<fun>", "<fun>", "<fun>";
    "f 3", "int", "3", "3", "3", "3";
    "f", "int -> int", "<fun>", "<fun>", "<fun>", "<fun>";
  ];
  [
    "let twice f x = f (f x)", "('a -> 'a) -> 'a -> 'a", "<fun>", "<fun>", "<fun>", "<fun>";
    "twice succ 3", "int", "5", "5", "5", "5";
    "twice not true", "bool", "true", "true", "1", "1";
  ];
  [
    "let dtwice (f:?) (x:?) = f (f x)", "? -> ? -> ?", "<fun>", "<fun>", "<fun>", "<fun>";
    "dtwice succ 3", "?", "5: int => ?",  "5<<id{int};int!>>", "5: int => ?",  "5<<id{int};int!>>";
    "dtwice not true", "?", "true: bool => ?", "true<<id{bool};bool!>>", "1: bool => ?", "1<<id{bool};bool!>>";
  ];
  [
    "let f x: 'a = x", "'a -> 'a", "<fun>", "<fun>", "<fun>", "<fun>";
    "f 3", "int", "3", "3", "3", "3";
    "f true", "bool", "true", "true", "1", "1";
    "f", "'a -> 'a", "<fun>", "<fun>", "<fun>", "<fun>";
  ];
  [
    "let did (x:?) = x", "? -> ?", "<fun>", "<fun>", "<fun>", "<fun>";
    "let f x: 'a = did x", "'a -> 'b", "<fun>", "<fun>", "<fun>", "<fun>";
    "f 3", "int", "3", "3", "3", "3";
    "f true", "bool", "true", "true", "1", "1";
    "f", "'a -> 'b", "<fun>", "<fun>", "<fun>", "<fun>";
  ];
  [
    "let f: 'a -> 'a = fun x -> x", "'a -> 'a", "<fun>", "<fun>", "<fun>", "<fun>";
    "f 3", "int", "3", "3", "3", "3";
    "f true", "bool", "true", "true", "1", "1";
    "f", "'a -> 'a", "<fun>", "<fun>", "<fun>", "<fun>";
    "let g = f", "'a -> 'a", "<fun>", "<fun>", "<fun>", "<fun>";
    "g 3", "int", "3", "3", "3", "3";
    "g true", "bool", "true", "true", "1", "1";
    "g", "'a -> 'a", "<fun>", "<fun>", "<fun>", "<fun>";
    "let g: 'b = f", "'a -> 'a", "<fun>", "<fun>", "<fun>", "<fun>";
    "g 3", "int", "3", "3", "3", "3";
    "g true", "bool", "true", "true", "1", "1";
    "g", "'a -> 'a", "<fun>", "<fun>", "<fun>", "<fun>";
  ];
  [
    "let f: 'a = fun x -> x", "'a -> 'a", "<fun>", "<fun>", "<fun>", "<fun>";
    "f 3", "int", "3", "3", "3", "3";
    "f true", "bool", "true", "true", "1", "1";
    "f", "'a -> 'a", "<fun>", "<fun>", "<fun>", "<fun>";
    "let g = f", "'a -> 'a", "<fun>", "<fun>", "<fun>", "<fun>";
    "g 3", "int", "3", "3", "3", "3";
    "g true", "bool", "true", "true", "1", "1";
    "g", "'a -> 'a", "<fun>", "<fun>", "<fun>", "<fun>";
  ];
  [
    "let f = ((fun x -> x: 'a -> 'a): 'a -> 'a)", "'a -> 'a", "<fun>", "<fun>", "<fun>", "<fun>";
    "f 3", "int", "3", "3", "3", "3";
    "f true", "bool", "true", "true", "1", "1";
    "f", "'a -> 'a", "<fun>", "<fun>", "<fun>", "<fun>";
    "let g = f", "'a -> 'a", "<fun>", "<fun>", "<fun>", "<fun>";
    "g 3", "int", "3", "3", "3", "3";
    "g true", "bool", "true", "true", "1", "1";
    "g", "'a -> 'a", "<fun>", "<fun>", "<fun>", "<fun>";
  ];
  [
    "let f: 'a -> 'a -> ? = fun x y -> 0", "'a -> 'a -> ?", "<fun>", "<fun>", "<fun>", "<fun>";
    "let g1 x = ((fun y -> y) : ? -> ?) x", "'a -> ?", "<fun>", "<fun>", "<fun>", "<fun>";
    "fun x y -> f (g1 x) (g1 y)", "'a -> 'b -> ?", "<fun>", "<fun>", "<fun>", "<fun>";
    "let g2 (x: 'a) = ((fun y -> y) : ? -> ?) x", "'a -> ?", "<fun>", "<fun>", "<fun>", "<fun>";
    "fun x y -> f (g2 x) (g2 y)", "'a -> 'b -> ?", "<fun>", "<fun>", "<fun>", "<fun>";
  ];
  [
    "let f = ((((fun x -> x): 'a ->'a): ?): 'a->'a)", "'a -> 'a", "<fun>", "<fun>", "<fun>", "<fun>";
    "f 3", "int", "3", "3", "3", "3";
    "f", "int -> int", "<fun>", "<fun>", "<fun>", "<fun>";
  ];
  [
    "let f (x: int) (y: bool) = 0", "int -> bool -> int", "<fun>", "<fun>", "<fun>", "<fun>";
    "let dyn x = ((fun (y: 'b) -> y): ? -> ?) x", "'a -> ?", "<fun>", "<fun>", "<fun>", "<fun>";
    "f (dyn 2) (dyn true)", "int", "0", "0", "0", "0";
  ];
  [
    "let f = fun x -> x", "'a -> 'a", "<fun>", "<fun>", "<fun>", "<fun>";
    "let f = fun x -> x f", "(('a -> 'a) -> 'b) -> 'b", "<fun>", "<fun>", "<fun>", "<fun>";
    "f (fun x -> x) 4", "int", "4", "4", "4", "4";
  ];
]

let let_poly_recursion = [
  ["let rec fact n = if n <= 1 then 1 else n * fact (n - 1) in fact 5", "int", "120", "120", "120", "120"];
  ["let rec fact (n:?) = if n <= 1 then 1 else n * fact (n - 1) in fact 5", "int", "120", "120", "120", "120"];
  ["let rec f (x:?) = x in f 2", "int", "2", "2", "2", "2"];
  ["let rec f n x = if n < 0 then x else f (n - 1) x in f 100 true", "bool", "true", "true", "1", "1"];
  ["let rec f (n:?) (x:?) = if n < 0 then x else f (n - 1) x in f 100 true", "bool", "true", "true", "1", "1"];
  ["let rec f n (x:?) = if n <= 0 then x else f 0 x in f 0 true", "bool", "true", "true", "1", "1"];
  ["let rec f n (x:?) = if n <= 0 then x else f 0 x in f 10 true", "bool", "true", "true", "1", "1"];
  ["let rec id x = x in id (); id true", "bool", "true", "true", "1", "1"];
]

let lists = [
  ["[]", "['a]", "[]", "[]", "[]", "[]"];
  ["[[]]", "[['a]]", "[] :: []", "[] :: []", "[] :: []", "[] :: []"];
  ["([]:?)", "?", "[]: [?] => ?", "[]<<['a!];[?]!>>", "[]: [?] => ?", "[]<<['a!];[?]!>>"];
  ["[1; 2; 3]", "[int]", "1 :: 2 :: 3 :: []", "1 :: 2 :: 3 :: []", "1 :: 2 :: 3 :: []", "1 :: 2 :: 3 :: []"];
  ["1 :: 2 :: []", "[int]", "1 :: 2 :: []", "1 :: 2 :: []", "1 :: 2 :: []", "1 :: 2 :: []"];
  ["(1:?) :: []", "[int]", "1 :: []", "1 :: []", "1 :: []", "1 :: []"];
  ["1 :: ([]:?)", "[int]", "1 :: []", "1 :: []", "1 :: []", "1 :: []"];
  ["1 :: (2:?) :: ([]:?)", "[int]", "1 :: 2 :: []", "1 :: (2<<id{int};int!>> :: []<<['a!]>>)<<[int?p;id{int}]>>", "1 :: 2 :: []", "1 :: (2<<id{int};int!>> :: []<<['a!]>>)<<[int?p;id{int}]>>"];
  ["let x = [true; false] in x", "[bool]", "true :: false :: []", "true :: false :: []", "1 :: 0 :: []", "1 :: 0 :: []"];
  ["match ([(1, true); (2, false)] : ?) with | [] -> 0 | (x, y) :: t -> x", "int", "1", "1", "1", "1"];
  ["(([1; 2], true : ?) : [int] * bool)", "[int] * bool", "(1 :: 2 :: [], true)", "(1 :: 2 :: [], true)", "(1 :: 2 :: [], 1)", "(1 :: 2 :: [], 1)"];
  ["let x = [] in let y = 3 :: x in let z = true :: x in y", "[int]", "3 :: []", "3 :: []", "3 :: []", "3 :: []"];
  ["let x = ([]:?) in let y = 3 :: x in let z = true :: x in y", "[int]","3 :: []", "3 :: []", "3 :: []", "3 :: []"];
]

let matches = [
  ["match 1 with | 1 -> 10 | _ -> 20", "int", "10", "10", "10", "10"];
  ["match true with true -> 1 | false -> 0", "int", "1", "1", "1", "1"];
  ["let f x = match x with | [] -> 0 | h :: t -> h in f [3; 4]", "int", "3", "3", "3", "3"];
  ["let rec sum l = match l with [] -> 0 | h :: t -> h + sum t in sum [1; 2; 3; 4]", "int", "10", "10", "10", "10"];
  ["let rec sum (l:?) = match l with [] -> 0 | h :: t -> h + sum t in sum [1; 2; 3; 4]", "int", "10", "10", "10", "10"];
  ["let rec sum l :? = match l with [] -> 0 | h :: t -> h + sum t in sum [1; 2; 3; 4]", "?", "10: int => ?", "10<<id{int};int!>>", "10: int => ?", "10<<id{int};int!>>"];
  ["let rec sum (l:?) :? = match l with [] -> 0 | h :: t -> h + sum t in sum [1; 2; 3; 4]", "?", "10: int => ?", "10<<id{int};int!>>", "10: int => ?", "10<<id{int};int!>>"];
  ["match 1, true with (x, y) -> x", "int", "1", "1", "1", "1"];
  ["match (1, true : ?) with (x, y) -> x", "int", "1", "1", "1", "1"];
  ["match 1, (2, 3) with (x, (y, z)) -> y", "int", "2", "2", "2", "2"];
  ["match (1, (2, 3) : ?) with (x, (y, z)) -> z", "int", "3", "3", "3", "3"];
  ["let t = (((fun x -> x + 1), 2) : (? -> ?) * ?) in match t with (f, x) -> f x", "int", "3", "3", "3", "3"];
]

let tuples = [
  ["1, true", "int * bool", "(1, true)", "(1, true)", "(1, 1)", "(1, 1)"];
  ["(1, true : int * ?)", "int * ?", "(1, true: bool => ?)", "(1, true)<<id{int}*(id{bool};bool!)>>", "(1, 1: bool => ?)", "(1, 1)<<id{int}*(id{bool};bool!)>>"];
  ["(1, true : ? * ?)", "? * ?", "(1: int => ?, true: bool => ?)", "(1, true)<<(id{int};int!)*(id{bool};bool!)>>", "(1: int => ?, 1: bool => ?)", "(1, 1)<<(id{int};int!)*(id{bool};bool!)>>"];
  ["(1, true : ?)", "?", "(1: int => ?, true: bool => ?): (? * ?) => ?", "(1, true)<<(id{int};int!)*(id{bool};bool!);(? * ?)!>>", "(1: int => ?, 1: bool => ?): (? * ?) => ?", "(1, 1)<<(id{int};int!)*(id{bool};bool!);(? * ?)!>>"];
  ["((1, true : ?) : int * bool)", "int * bool", "(1, true)", "(1, true)", "(1, 1)", "(1, 1)"];
  ["((1, true : ?) : ? * ?)", "? * ?", "(1: int => ?, true: bool => ?)", "(1, true)<<(id{int};int!)*(id{bool};bool!)>>", "(1: int => ?, 1: bool => ?)", "(1, 1)<<(id{int};int!)*(id{bool};bool!)>>"];
  ["((1, true : ?) : bool * int)", "bool * int", "blame+", "(1, true)<<⊥{int,p,bool}*⊥{bool,p,int}>>", "blame+", "(1, 1)<<⊥{int,p,bool}*⊥{bool,p,int}>>"];
  ["((1, 2, 3 : ?) : int * int)", "int * int", "blame+", "blame+", "blame+", "blame+"];
  ["1 + 2, 3 * 4", "int * int", "(3, 12)", "(3, 12)", "(3, 12)", "(3, 12)"];
  ["(((1, true), 3 : ?) : (int * int) * int)", "(int * int) * int", "blame+", "((1, true), 3)<<(id{int}*⊥{bool,p,int})*id{int}>>", "blame+", "((1, 1), 3)<<(id{int}*⊥{bool,p,int})*id{int}>>"];
  ["((1, (2, 3) : ?) : int * int)", "int * int", "blame+", "(1, (2, 3))<<id{int}*⊥{(? * ?),p,int}>>", "blame+", "(1, (2, 3))<<id{int}*⊥{(? * ?),p,int}>>"];
]

let stdlibs = [
  ["succ 2", "int", "3", "3", "3", "3"];
  ["prec 0", "int", "-1", "-1", "-1", "-1"];
]

let kNorm_funs = [
  ["let x = 2 in let x = 4 in x + x", "int", "8", "8", "8", "8"];
  ["let x = 2 in let y = x in (fun y -> y) y", "int", "2", "2", "2", "2"];
  ["let x = 2 in let a = x in let b = a in let c = x in let d = a in let e = x in e", "int", "2", "2", "2", "2"];
]

(* ["match (1, true) : ? with ((x:int), (y:bool)) -> x", "int", "1", "1", "1", "1"]; *)
(* ["match (1, true) : ? with ((x:bool), (y:bool)) -> x", "bool", "blame+", "blame+", "blame+", "blame+"]; *)
(* ["let x, y = 1, true in x", "int", "1", "1", "1", "1"]; *)
(* ["let x, y = (1, true : ?) in x", "?", "1: int => ?", "...", "1: int => ?", "..."]; *)

(* let g = fun x -> ((fun y -> y):? -> ?) x in if g true then g 2 else g 3  *)

(* let minus_one x = x - 1 in let rec repeat n f x = if n = 0 then x else repeat (n-1) f (f x) in repeat 100000 minus_one 1000000;; *)

let suites = [
  "Constants", constants;
  "Unary Operations", unary_ops;
  "Binary Operations", binary_ops;
  "Type Ascription", type_ascription;
  "If Expression", if_then_else;
  "Let Definition", let_definition;
  "Abstraction", abstraction;
  "Application", application;
  "Sequence", sequence;
  "Dinamic Type Inference", dti;
  "Let Polymorphism", let_poly;
  "Let Polymorphism in Toplevel", let_poly_toplevel;
  "Let Polymorphism & Recursion", let_poly_recursion;
  "List", lists;
  "Match Expression", matches;
  "Tuple", tuples;
  "Functions in Standard Library", stdlibs;
  "K-Normalization", kNorm_funs;
]