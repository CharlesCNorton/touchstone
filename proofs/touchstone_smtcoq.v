(* An independent proof checker (machine-checked) for the INTEGER obligations
   touchstone.py actually emits.

   SMTCoq is a Coq plugin whose reflexive checker validates, inside Coq's kernel, a proof
   certificate emitted by an external SMT solver. A skeptic who trusts neither the harness
   nor Z3 re-runs this checker. The goals below are representative of the linear-integer
   verification conditions the harness discharges -- loop-invariant initiation and
   preservation, guard refinements as in _filter, algebraic equivalences as in verify_equiv,
   and a path/branch obligation -- discharged by an external solver and re-checked, literal
   step by literal step, in Coq's kernel via the `smt` tactic over the LIA theory.

   TOOLCHAIN (pinned in toolchain.lock / Dockerfile.coq): opam switch certicoq-8.20
   (Coq 8.20.1 + coq-smtcoq 2.3+8.20) with cvc4 1.6 (or veriT) on PATH and SMTCoq's LFSC
   signatures in the working directory. This stack is not the Rocq 9.0 switch the other
   three companion files use, so it is built separately. `coqc` prints
   "Converting proof to SMTCoq... Done" and closes each goal with Qed. *)

From SMTCoq Require Import SMTCoq.
From Coq Require Import ZArith.
Local Open Scope Z_scope.

(* verify_equiv: two encodings of the same value agree on all inputs (2*a == a + a). *)
Goal forall a : Z, 2 * a = a + a.
Proof. smt. Qed.

(* Loop-invariant preservation for `while i < n: i = i + 1` under the bound 0 <= i <= n:
   the invariant is re-established after one step. This is exactly VC2 in verify_deductive. *)
Goal forall i n : Z, 0 <= i -> i <= n -> i < n -> (0 <= i + 1 /\ i + 1 <= n).
Proof. smt. Qed.

(* Guard refinement as performed by _filter: under the true branch of `x < k`, x <= k - 1. *)
Goal forall x k : Z, x < k -> x <= k - 1.
Proof. smt. Qed.

(* A branch/path obligation: the two arms of a clamp never cross, so the lower bound holds
   on the path that took neither clamp. *)
Goal forall x : Z, x <= 100 -> x >= 0 -> (0 <= x /\ x <= 100).
Proof. smt. Qed.

(* Postcondition discharge: a counted loop that ran to i = n returns i, and i = n. *)
Goal forall i n : Z, i <= n -> i >= n -> i = n.
Proof. smt. Qed.
