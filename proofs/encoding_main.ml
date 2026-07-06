(* CLI driver for the Coq-extracted division encoding (encoding.ml). It converts decimal integers
   to the extracted `z` representation, calls the verified pyfloordiv / pymod, and prints the floor
   quotient and modulo. This is the extracted, proven-sound encoding actually executing. *)
open Encoding

let rec pos_of_int n =
  if n = 1 then XH
  else if n land 1 = 1 then XI (pos_of_int (n asr 1))
  else XO (pos_of_int (n asr 1))

let z_of_int n =
  if n = 0 then Z0 else if n > 0 then Zpos (pos_of_int n) else Zneg (pos_of_int (- n))

let rec int_of_pos = function XH -> 1 | XO p -> 2 * int_of_pos p | XI p -> 2 * int_of_pos p + 1
let int_of_z = function Z0 -> 0 | Zpos p -> int_of_pos p | Zneg p -> - (int_of_pos p)

let run a b = Printf.printf "%d %d\n" (int_of_z (pyfloordiv a b)) (int_of_z (pymod a b))

(* `encoding a b` prints one result (the build smoke test); with no argument it reads `a b` lines from
   stdin and prints one result per line, so the Python encoding audit pipes its grid through one call. *)
let () =
  if Array.length Sys.argv >= 3 then
    run (z_of_int (int_of_string Sys.argv.(1))) (z_of_int (int_of_string Sys.argv.(2)))
  else
    try
      while true do
        let line = String.trim (input_line stdin) in
        if line <> "" then
          match List.filter (fun s -> s <> "") (String.split_on_char ' ' line) with
          | [a; b] -> run (z_of_int (int_of_string a)) (z_of_int (int_of_string b))
          | _ -> prerr_endline "expected: a b"; exit 1
      done
    with End_of_file -> ()
