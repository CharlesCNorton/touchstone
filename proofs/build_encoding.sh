#!/usr/bin/env bash
# Build and check the Coq-extracted division encoding. touchstone_encoding.v emits encoding.ml via
# Extraction; this confirms the extracted pyfloordiv / pymod compile and compute Python's floor // and %.
# Run with the Rocq 9.0 opam switch active:
#     eval "$(opam env --switch=rocq9)" && bash build_encoding.sh
set -uo pipefail

COQC="coqc"; command -v coqc >/dev/null 2>&1 || COQC="rocq compile"
${COQC} touchstone_encoding.v >/dev/null 2>&1 || { echo "  FAIL: touchstone_encoding.v did not compile"; exit 1; }
[ -f encoding.ml ] || { echo "  FAIL: extraction emitted no encoding.ml"; exit 1; }
rm -f encoding.mli                                   # the .ml is self-contained for the driver
command -v ocamlfind >/dev/null 2>&1 || { echo "  encoding: SKIPPED (no ocamlfind)"; exit 0; }
ocamlfind ocamlopt encoding.ml encoding_main.ml -o encoding >/dev/null 2>&1 \
  || { echo "  FAIL: extracted driver did not build"; exit 1; }

fail=0
check() { local exp="$1"; shift; local got; got="$(./encoding "$@")"
          [ "$got" = "$exp" ] || { echo "  FAIL: encoding $* -> '$got' (expected '$exp')"; fail=1; }; }
check "2 1"   7 3       # 7 // 3 == 2, 7 % 3 == 1
check "-3 2"  -7 3      # floor toward -inf; remainder takes the divisor's sign
check "-3 -2" 7 -3
check "2 -1"  -7 -3
check "0 0"   0 5
[ "$fail" -eq 0 ] && echo "  extracted division encoding runs with the proven results" || exit 1
