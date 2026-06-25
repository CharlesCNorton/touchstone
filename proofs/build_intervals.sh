#!/usr/bin/env bash
# Build and check the Coq-extracted interval operators. touchstone_domains.v emits intervals.ml via
# Extraction; this confirms the extracted operators (iadd / ineg / isub / ijoin / imul) compile and
# compute the proven closed forms. Run with the Rocq 9.0 opam switch active:
#     eval "$(opam env --switch=rocq9)" && bash build_intervals.sh
set -uo pipefail

COQC="coqc"; command -v coqc >/dev/null 2>&1 || COQC="rocq compile"
${COQC} touchstone_domains.v >/dev/null 2>&1 || { echo "  FAIL: touchstone_domains.v did not compile"; exit 1; }
[ -f intervals.ml ] || { echo "  FAIL: extraction emitted no intervals.ml"; exit 1; }
rm -f intervals.mli                                  # the .ml is self-contained for the driver
command -v ocamlfind >/dev/null 2>&1 || { echo "  intervals: SKIPPED (no ocamlfind)"; exit 0; }
ocamlfind ocamlopt intervals.ml intervals_main.ml -o intervals >/dev/null 2>&1 \
  || { echo "  FAIL: extracted driver did not build"; exit 1; }

fail=0
check() { local exp="$1"; shift; local got; got="$(./intervals "$@")"
          [ "$got" = "$exp" ] || { echo "  FAIL: intervals $* -> '$got' (expected '$exp')"; fail=1; }; }
check "3 8"   iadd 1 5 2 3        # [1,5] + [2,3]
check "-2 3"  isub 1 5 2 3        # [1,5] - [2,3]
check "-7 -2" ineg 2 7           # -[2,7]
check "0 9"   ijoin 0 4 2 9       # [0,4] join [2,9]
check "-12 15" imul -2 3 -4 5     # [-2,3] * [-4,5]
[ "$fail" -eq 0 ] && echo "  extracted interval operators run with the proven results" || exit 1
