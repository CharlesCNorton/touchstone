(* CLI driver for the Coq-extracted verification-condition generators (vcgen.ml). It reads one
   S-expression per line: `(query <prog> <post>)` runs the verified straight-line generator wpg and
   prints the verification condition; `(querycmd <kcmd> <post>)` runs the verified loop generator vcg
   and prints `(vc <precondition> <obligation>...)`. Both are the extracted, proven-sound generators
   executing; the Python engine's vcgen audits pipe random inputs through them and require the in-engine
   generators to produce the identical output. Grammar:
     expr ::= (v N) | (c Z) | (add E E) | (sub E E) | (mul E E) | (div E E) | (mod E E)
     prog ::= nil | (asgn N E P) | (cond E P P P)
     kcmd ::= kskip | (kasgn N E) | (kseq K K) | (kif E K K) | (kwhile F E K)
     form ::= true | false | (lt E E) | (le E E) | (eq E E) | (not F) | (and F F) | (or F F) | (impl F F) *)
open Vcgen

let rec nat_of_int n = if n <= 0 then O else S (nat_of_int (n - 1))
let rec int_of_nat = function O -> 0 | S k -> 1 + int_of_nat k
let rec pos_of_int n =
  if n = 1 then XH else if n land 1 = 1 then XI (pos_of_int (n asr 1)) else XO (pos_of_int (n asr 1))
let z_of_int n = if n = 0 then Z0 else if n > 0 then Zpos (pos_of_int n) else Zneg (pos_of_int (- n))
let rec int_of_pos = function XH -> 1 | XO p -> 2 * int_of_pos p | XI p -> 2 * int_of_pos p + 1
let int_of_z = function Z0 -> 0 | Zpos p -> int_of_pos p | Zneg p -> - (int_of_pos p)

type sexp = A of string | L of sexp list

let tokenize s =
  let n = String.length s and toks = ref [] and i = ref 0 in
  let sep c = c = '(' || c = ')' || c = ' ' || c = '\n' || c = '\t' || c = '\r' in
  while !i < n do
    let c = s.[!i] in
    if c = '(' then (toks := "(" :: !toks; incr i)
    else if c = ')' then (toks := ")" :: !toks; incr i)
    else if sep c then incr i
    else begin
      let j = ref !i in
      while !j < n && not (sep s.[!j]) do incr j done;
      toks := String.sub s !i (!j - !i) :: !toks; i := !j
    end
  done;
  List.rev !toks

let parse toks =
  let rec go = function
    | "(" :: rest ->
        let rec lst acc = function
          | ")" :: r -> (L (List.rev acc), r)
          | [] -> failwith "eof in list"
          | ts -> let (e, r) = go ts in lst (e :: acc) r
        in lst [] rest
    | a :: rest -> (A a, rest)
    | [] -> failwith "eof"
  in fst (go toks)

let rec to_expr = function
  | L [A "v"; A n] -> EVar (nat_of_int (int_of_string n))
  | L [A "c"; A z] -> EConst (z_of_int (int_of_string z))
  | L [A "add"; a; b] -> EAdd (to_expr a, to_expr b)
  | L [A "sub"; a; b] -> ESub (to_expr a, to_expr b)
  | L [A "mul"; a; b] -> EMul (to_expr a, to_expr b)
  | L [A "div"; a; b] -> EDiv (to_expr a, to_expr b)
  | L [A "mod"; a; b] -> EMod (to_expr a, to_expr b)
  | L [A "elt"; a; b] -> ELt (to_expr a, to_expr b)
  | L [A "ele"; a; b] -> ELe (to_expr a, to_expr b)
  | L [A "eeq"; a; b] -> EEq (to_expr a, to_expr b)
  | L [A "enot"; a] -> ENot (to_expr a)
  | L [A "eand"; a; b] -> EAnd (to_expr a, to_expr b)
  | L [A "eor"; a; b] -> EOr (to_expr a, to_expr b)
  | _ -> failwith "bad expr"

let rec to_prog = function
  | A "nil" -> PNil
  | L [A "asgn"; A n; e; p] -> PAsgn (nat_of_int (int_of_string n), to_expr e, to_prog p)
  | L [A "cond"; c; t; el; r] -> PCond (to_expr c, to_prog t, to_prog el, to_prog r)
  | _ -> failwith "bad prog"

let rec to_form = function
  | A "true" -> FTrue | A "false" -> FFalse
  | L [A "lt"; a; b] -> FLt (to_expr a, to_expr b)
  | L [A "le"; a; b] -> FLe (to_expr a, to_expr b)
  | L [A "eq"; a; b] -> FEq (to_expr a, to_expr b)
  | L [A "not"; f] -> FNot (to_form f)
  | L [A "and"; f; g] -> FAnd (to_form f, to_form g)
  | L [A "or"; f; g] -> FOr (to_form f, to_form g)
  | L [A "impl"; f; g] -> FImpl (to_form f, to_form g)
  | _ -> failwith "bad form"

let rec to_kcmd = function
  | A "kskip" -> KSkip
  | L [A "kasgn"; A n; e] -> KAsgn (nat_of_int (int_of_string n), to_expr e)
  | L [A "kseq"; a; b] -> KSeq (to_kcmd a, to_kcmd b)
  | L [A "kif"; c; t; el] -> KIf (to_expr c, to_kcmd t, to_kcmd el)
  | L [A "kwhile"; inv; c; body] -> KWhile (to_form inv, to_expr c, to_kcmd body)
  | _ -> failwith "bad kcmd"

let rec str_expr = function
  | EVar x -> Printf.sprintf "(v %d)" (int_of_nat x)
  | EConst z -> Printf.sprintf "(c %d)" (int_of_z z)
  | EAdd (a, b) -> Printf.sprintf "(add %s %s)" (str_expr a) (str_expr b)
  | ESub (a, b) -> Printf.sprintf "(sub %s %s)" (str_expr a) (str_expr b)
  | EMul (a, b) -> Printf.sprintf "(mul %s %s)" (str_expr a) (str_expr b)
  | EDiv (a, b) -> Printf.sprintf "(div %s %s)" (str_expr a) (str_expr b)
  | EMod (a, b) -> Printf.sprintf "(mod %s %s)" (str_expr a) (str_expr b)
  | ELt (a, b) -> Printf.sprintf "(elt %s %s)" (str_expr a) (str_expr b)
  | ELe (a, b) -> Printf.sprintf "(ele %s %s)" (str_expr a) (str_expr b)
  | EEq (a, b) -> Printf.sprintf "(eeq %s %s)" (str_expr a) (str_expr b)
  | ENot a -> Printf.sprintf "(enot %s)" (str_expr a)
  | EAnd (a, b) -> Printf.sprintf "(eand %s %s)" (str_expr a) (str_expr b)
  | EOr (a, b) -> Printf.sprintf "(eor %s %s)" (str_expr a) (str_expr b)

let rec str_form = function
  | FTrue -> "true" | FFalse -> "false"
  | FLt (a, b) -> Printf.sprintf "(lt %s %s)" (str_expr a) (str_expr b)
  | FLe (a, b) -> Printf.sprintf "(le %s %s)" (str_expr a) (str_expr b)
  | FEq (a, b) -> Printf.sprintf "(eq %s %s)" (str_expr a) (str_expr b)
  | FNot f -> Printf.sprintf "(not %s)" (str_form f)
  | FAnd (f, g) -> Printf.sprintf "(and %s %s)" (str_form f) (str_form g)
  | FOr (f, g) -> Printf.sprintf "(or %s %s)" (str_form f) (str_form g)
  | FImpl (f, g) -> Printf.sprintf "(impl %s %s)" (str_form f) (str_form g)

let str_vcg (pre, obs) =
  Printf.sprintf "(vc %s%s)" (str_form pre)
    (String.concat "" (List.map (fun o -> " " ^ str_form o) obs))

(* One `(query <prog> <post>)` per input line; one generated VC per output line. The Python engine's
   vcgen audit pipes a whole random corpus through a single invocation and compares line by line. *)
let () =
  try
    while true do
      let line = String.trim (input_line stdin) in
      if line <> "" then
        match parse (tokenize line) with
        | L [A "query"; p; q] -> print_string (str_form (wpg (to_prog p) (to_form q))); print_newline ()
        | L [A "querycmd"; k; q] -> print_string (str_vcg (vcg (to_kcmd k) (to_form q))); print_newline ()
        | _ -> prerr_endline "expected (query <prog> <post>) or (querycmd <kcmd> <post>)"; exit 1
    done
  with End_of_file -> ()
