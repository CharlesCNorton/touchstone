#!/usr/bin/env bash
# CI gate for the machine-checked trust base. Every theorem in the Rocq 9.0 companion
# files must be Closed under the global context (no axioms, no Admitted). Run from the
# directory holding the .v files, with the Rocq 9.0 opam switch active:
#     eval "$(opam env --switch=rocq9)" && bash verify_coq.sh
set -uo pipefail

# Rocq 9 ships `rocq compile`; the `coqc` alias may be absent (e.g. the rocq-prover Docker image).
COQC="coqc"
command -v coqc >/dev/null 2>&1 || COQC="rocq compile"

fail=0
for f in touchstone_encoding touchstone_functor touchstone_domains touchstone_encoders \
         touchstone_floats touchstone_seplogic touchstone_relyguarantee touchstone_lowering touchstone_heap \
         touchstone_strings touchstone_listmodel touchstone_setmodel touchstone_bitwise touchstone_ndshape \
         touchstone_partial; do
  echo "=== ${f}.v ==="
  out="$(${COQC} "${f}.v" 2>&1 || true)"
  if echo "${out}" | grep -iqE "error|admitted|\bAxiom\b"; then
    echo "${out}" | grep -iE "error|admitted|\bAxiom\b" || true
    echo "  FAIL: ${f} reported an error, Admitted, or Axiom"
    fail=1
    continue
  fi
  closed="$(echo "${out}" | grep -c 'Closed under the global context' || true)"
  echo "  ${closed} theorem(s) closed under the global context"
  if [ "${closed}" -lt 1 ]; then
    echo "  FAIL: ${f} produced no Print Assumptions evidence (compiler: ${COQC})"
    echo "${out}" | tail -5
    fail=1
  fi
done

# The interval operators are extracted to OCaml by touchstone_domains.v; build and run them, so the
# operators proven sound are exercised as code (skips cleanly where ocamlfind is absent).
echo "=== extracted interval operators ==="
if ! bash build_intervals.sh; then
  fail=1
fi

# The verification-condition generator is extracted to OCaml by touchstone_functor.v; build and run it
# behind its driver, so the generator proven sound and complete is exercised as code (the Python
# engine's vcgen audit then holds the in-engine generator equal to this extraction).
echo "=== extracted VC generator ==="
if ! bash build_vcgen.sh; then
  fail=1
fi

# The division encoding is extracted to OCaml by touchstone_encoding.v; build and run it behind its
# driver, so the encoding proven equal to Python's // and % is exercised as code (the Python engine's
# encoding audit then holds its py_floordiv / py_mod equal to this extraction).
echo "=== extracted division encoding ==="
if ! bash build_encoding.sh; then
  fail=1
fi

# The committed engine modules (touchstone/_generated/*.py) are the Python image of the extraction that
# json_to_python.py produces from each .json (emitted by the coqc runs above). Regenerate and diff, so the
# generator the engine runs can never drift from the proof. Skips cleanly where python3 is absent.
echo "=== generated engine modules match the extraction ==="
if command -v python3 >/dev/null 2>&1 && [ -f json_to_python.py ]; then
  gfail=0
  for pair in vcgen:vcgen_rocq intervals:intervals_rocq encoding:encoding_rocq encoders:encoders_rocq; do
    j="${pair%%:*}"; m="${pair##*:}"
    if [ -f "${j}.json" ]; then
      python3 json_to_python.py "${j}.json" > "_regen_${m}.py" 2>/dev/null
      if ! diff --strip-trailing-cr -q "_regen_${m}.py" "../touchstone/_generated/${m}.py" >/dev/null 2>&1; then
        echo "  FAIL: touchstone/_generated/${m}.py is not a fresh image of ${j}.json"; gfail=1
      fi
      rm -f "_regen_${m}.py"
    fi
  done
  [ "${gfail}" -eq 0 ] && echo "  committed engine modules are an exact image of the extraction"
  [ "${gfail}" -eq 0 ] || fail=1
else
  echo "  generated engine check: SKIPPED (no python3)"
fi

# touchstone_smtcoq.v runs under the separate Coq 8.20 + SMTCoq + veriT/cvc4 toolchain
# (see toolchain.lock). verify_smtcoq.sh runs it when that toolchain is present and skips
# cleanly otherwise, so certificate-checking is part of the standard gate.
if ! bash verify_smtcoq.sh; then
  fail=1
fi

if [ "${fail}" -eq 0 ]; then
  echo "COQ TRUST BASE OK"
else
  echo "COQ TRUST BASE FAILED"
  exit 1
fi
