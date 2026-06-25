#!/usr/bin/env bash
# One reproducible entry point for the whole machine-checked trust base, spanning the two opam switches the
# companion proofs need: the Rocq 9.0 switch (touchstone_encoding / functor / domains / encoders / floats /
# seplogic / relyguarantee and the OCaml extractions) and the separate Coq 8.20 + SMTCoq + veriT/cvc4 switch
# (touchstone_smtcoq / obligations, whose goals close by re-checking an SMT certificate in Coq's kernel).
# Each phase activates its switch with `opam env --switch=<name>`, so a single `bash verify_all.sh` checks
# everything that verify_coq.sh (under rocq9) and verify_smtcoq.sh (under certicoq-8.20) check separately.
# The switch names are overridable (ROCQ_SWITCH / SMTCOQ_SWITCH) and each phase skips cleanly when its switch
# is absent, so the driver runs in a partial environment (one switch installed) without failing what it cannot
# check. Provision both switches reproducibly with `docker build -f Dockerfile.trustbase .`, or per toolchain.lock.
set -uo pipefail
cd "$(dirname "$0")"

ROCQ_SWITCH="${ROCQ_SWITCH:-rocq9}"
SMTCOQ_SWITCH="${SMTCOQ_SWITCH:-certicoq-8.20}"
fail=0

have_switch() { opam switch list --short 2>/dev/null | grep -qx "$1"; }

echo "########## Rocq 9.0 trust base (opam switch: ${ROCQ_SWITCH}) ##########"
if ! command -v opam >/dev/null 2>&1; then
  echo "  SKIPPED: opam is not installed"
elif have_switch "${ROCQ_SWITCH}"; then
  # verify_coq.sh compiles the Rocq 9.0 files (Print Assumptions-clean), builds and runs the OCaml
  # extractions, and diffs the committed engine modules against a fresh extraction image. Its trailing
  # verify_smtcoq.sh call SKIPS here (SMTCoq is not on this switch); the SMTCoq phase below runs it for real.
  if ! ( eval "$(opam env --switch=${ROCQ_SWITCH} 2>/dev/null)"; bash verify_coq.sh ); then
    fail=1
  fi
else
  echo "  SKIPPED: opam switch ${ROCQ_SWITCH} is not installed (see toolchain.lock [rocq])"
fi

echo "########## SMTCoq certificate trust base (opam switch: ${SMTCOQ_SWITCH}) ##########"
if ! command -v opam >/dev/null 2>&1; then
  echo "  SKIPPED: opam is not installed"
elif have_switch "${SMTCOQ_SWITCH}"; then
  # verify_smtcoq.sh checks touchstone_smtcoq.v and touchstone_obligations.v under Coq 8.20 + SMTCoq, with
  # veriT / cvc4 supplying the certificates re-validated in Coq's kernel. It skips cleanly if SMTCoq or the
  # solvers are not reachable from this switch's coqc.
  if ! ( eval "$(opam env --switch=${SMTCOQ_SWITCH} 2>/dev/null)"; bash verify_smtcoq.sh ); then
    fail=1
  fi
else
  echo "  SKIPPED: opam switch ${SMTCOQ_SWITCH} is not installed (see toolchain.lock [smtcoq])"
fi

if [ "${fail}" -eq 0 ]; then
  echo "TRUST BASE OK (Rocq 9.0 + SMTCoq)"
else
  echo "TRUST BASE FAILED"
  exit 1
fi
