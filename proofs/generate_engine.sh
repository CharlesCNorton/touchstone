#!/usr/bin/env bash
# Regenerate the engine's verified-extraction modules (touchstone/_generated/*.py) from the Rocq
# development: compile each .v (which emits its JSON abstract syntax) and transpile that to Python with
# json_to_python.py. The result is a mechanical image of the proven wpg / vcg / interval operators, so
# the generator that runs in the engine is not a hand transcription. Run with the Rocq 9.0 switch active:
#     eval "$(opam env --switch=rocq9)" && bash generate_engine.sh
# verify_coq.sh regenerates and diffs against the committed files, so the two can never drift.
set -euo pipefail
cd "$(dirname "$0")"

COQC="coqc"; command -v coqc >/dev/null 2>&1 || COQC="rocq compile"
PY="${PYTHON:-python3}"
OUT="../touchstone/_generated"
mkdir -p "$OUT"

emit() {                                   # <vfile> <jsonbase> <pymodule>
  ${COQC} "$1.v" >/dev/null 2>&1 || { echo "  FAIL: $1.v did not compile"; exit 1; }
  [ -f "$2.json" ] || { echo "  FAIL: $1.v emitted no $2.json"; exit 1; }
  ${PY} json_to_python.py "$2.json" > "$OUT/$3.py"
  echo "  $OUT/$3.py"
}

echo "regenerating the verified-extraction Python from the Rocq development:"
emit touchstone_functor  vcgen      vcgen_rocq
emit touchstone_domains  intervals  intervals_rocq
emit touchstone_encoding encoding   encoding_rocq
echo "done."
