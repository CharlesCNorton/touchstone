#!/usr/bin/env bash
# Build and smoke-test the Coq-extracted verification-condition generator. touchstone_functor.v emits
# vcgen.ml via Extraction; this confirms the extracted wpg compiles behind the S-expression driver and
# produces the verification conditions the Python engine's generator must match. Run with the Rocq 9.0
# opam switch active:  eval "$(opam env --switch=rocq9)" && bash build_vcgen.sh
set -uo pipefail

COQC="coqc"; command -v coqc >/dev/null 2>&1 || COQC="rocq compile"
${COQC} touchstone_functor.v >/dev/null 2>&1 || { echo "  FAIL: touchstone_functor.v did not compile"; exit 1; }
[ -f vcgen.ml ] || { echo "  FAIL: extraction emitted no vcgen.ml"; exit 1; }
rm -f vcgen.mli                                      # the .ml is self-contained for the driver
command -v ocamlfind >/dev/null 2>&1 || { echo "  vcgen: SKIPPED (no ocamlfind)"; exit 0; }
ocamlfind ocamlopt vcgen.ml vcgen_main.ml -o vcgen >/dev/null 2>&1 \
  || { echo "  FAIL: extracted vcgen driver did not build"; exit 1; }

fail=0
check() { local exp="$1" inp="$2"; local got; got="$(printf '%s\n' "$inp" | ./vcgen)"
          [ "$got" = "$exp" ] || { echo "  FAIL: vcgen '$inp' -> '$got' (expected '$exp')"; fail=1; }; }
# x0 := 5 ; assert x0 == 5  ->  (and true (eq 5 5))    (assignment substitutes; no division obligation)
check "(and true (eq (c 5) (c 5)))" "(query (asgn 0 (c 5) nil) (eq (v 0) (c 5)))"
# x0 := 10 // x1 ; assert true  ->  the divisor-nonzero obligation x1 != 0 is emitted
check "(and (and true (and true (not (eq (v 1) (c 0))))) true)" "(query (asgn 0 (div (c 10) (v 1)) nil) true)"
# if x0 != 0 then x1:=1 else x1:=2 ; assert true  ->  guard defined, each arm an assignment VC
check "(and true (and (impl (not (eq (v 0) (c 0))) (and true true)) (impl (eq (v 0) (c 0)) (and true true))))" \
      "(query (cond (v 0) (asgn 1 (c 1) nil) (asgn 1 (c 2) nil) nil) true)"
[ "$fail" -eq 0 ] && echo "  extracted VC generator runs with the proven results" || exit 1
