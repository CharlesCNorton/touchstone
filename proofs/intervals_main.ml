(* CLI driver for the Coq-extracted interval operators (intervals.ml). It converts decimal
   integers to the extracted binary `z` representation, calls the verified operator, and prints
   the resulting interval bounds. This is the extracted, proven-sound code actually executing. *)
open Intervals

let rec pos_of_int n =
  if n = 1 then XH
  else if n land 1 = 1 then XI (pos_of_int (n asr 1))
  else XO (pos_of_int (n asr 1))

let z_of_int n =
  if n = 0 then Z0 else if n > 0 then Zpos (pos_of_int n) else Zneg (pos_of_int (- n))

let rec int_of_pos = function XH -> 1 | XO p -> 2 * int_of_pos p | XI p -> 2 * int_of_pos p + 1
let int_of_z = function Z0 -> 0 | Zpos p -> int_of_pos p | Zneg p -> - (int_of_pos p)

let pr = function Pair (lo, hi) -> Printf.printf "%d %d\n" (int_of_z lo) (int_of_z hi)

(* one verified interval operator on decimal-integer bounds; ineg takes 2 args, the rest 4 *)
let run op a =
  let zi i = z_of_int a.(i) in
  match op with
  | "iadd" -> iadd (zi 0) (zi 1) (zi 2) (zi 3)
  | "isub" -> isub (zi 0) (zi 1) (zi 2) (zi 3)
  | "ineg" -> ineg (zi 0) (zi 1)
  | "ijoin" -> ijoin (zi 0) (zi 1) (zi 2) (zi 3)
  | "imul" -> imul (zi 0) (zi 1) (zi 2) (zi 3)
  | _ -> prerr_endline "unknown op"; exit 1

(* `intervals <op> n...` prints one result (the build smoke test); with no argument it reads
   `<op> n...` lines from stdin and prints one result per line, so the Python intervals audit
   pipes its whole random corpus through a single invocation. *)
let () =
  if Array.length Sys.argv >= 2 then
    pr (run Sys.argv.(1) (Array.map int_of_string (Array.sub Sys.argv 2 (Array.length Sys.argv - 2))))
  else
    try
      while true do
        let line = String.trim (input_line stdin) in
        if line <> "" then
          match List.filter (fun s -> s <> "") (String.split_on_char ' ' line) with
          | op :: nums -> pr (run op (Array.of_list (List.map int_of_string nums)))
          | [] -> ()
      done
    with End_of_file -> ()
