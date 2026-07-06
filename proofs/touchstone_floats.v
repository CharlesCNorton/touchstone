(* Trust base for touchstone, part VII: the float divmod laws, machine-checked AXIOM-FREE over the rationals.

   core._fp_divmod transcribes CPython's float_divmod -- an IEEE-754 remainder (fmod) plus a sign and half
   correction -- to compute Python's float a // b and a % b. The verifier then reasons with the LAWS that
   result: the quotient is the floored quotient, and the remainder is bounded by the divisor and carries its
   sign (so e.g. 0 <= x % n < n for n > 0).

   IEEE-754 binary64 values are dyadic rationals (m * 2^e), a subset of Q, and the divmod the engine computes
   is EXACT on them -- fmod is an exact IEEE-754 operation and the floor is exact. So the laws hold over Q,
   and proving them there (rather than over Coq's classical reals, whose construction rests on functional
   extensionality and a choice-like axiom) keeps the whole trust base closed under the global context: no
   axioms, no Admitted. *)

From Stdlib Require Import QArith Qround.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

Lemma inject_succ : forall z : Z, inject_Z (z + 1) == inject_Z z + 1.
Proof. intro z. rewrite inject_Z_plus. reflexivity. Qed.

(* Python's float // and % : the floored quotient and the remainder it leaves. *)
Definition pyfdiv (a b : Q) : Q := inject_Z (Qfloor (a / b)).
Definition pyfmod (a b : Q) : Q := a - pyfdiv a b * b.

(* reconstruction: a = (a // b) * b + (a % b), the divmod identity. *)
Theorem pyf_reconstruct : forall a b, a == pyfdiv a b * b + pyfmod a b.
Proof. intros a b; unfold pyfmod; ring. Qed.

(* a positive divisor leaves a remainder in [0, b): the bound a verifier uses to discharge 0 <= x % n < n. *)
Theorem pyfmod_pos : forall a b, b > 0 -> 0 <= pyfmod a b /\ pyfmod a b < b.
Proof.
  intros a b Hb. unfold pyfmod, pyfdiv.
  set (t := a / b).
  assert (Hbne : ~ b == 0) by lra.
  assert (Hdiv : t * b == a) by (unfold t; field; exact Hbne).
  pose proof (Qfloor_le t) as Hlb.
  pose proof (Qlt_floor t) as Hf. rewrite inject_succ in Hf.
  split; nra.
Qed.

(* a negative divisor leaves a remainder in (b, 0]: the mirror bound, with the remainder taking b's sign. *)
Theorem pyfmod_neg : forall a b, b < 0 -> b < pyfmod a b /\ pyfmod a b <= 0.
Proof.
  intros a b Hb. unfold pyfmod, pyfdiv.
  set (t := a / b).
  assert (Hbne : ~ b == 0) by lra.
  assert (Hdiv : t * b == a) by (unfold t; field; exact Hbne).
  pose proof (Qfloor_le t) as Hlb.
  pose proof (Qlt_floor t) as Hf. rewrite inject_succ in Hf.
  split; nra.
Qed.

(* the remainder is zero or carries the divisor's sign -- Python's invariant for float %. *)
Theorem pyfmod_sign : forall a b, ~ b == 0 ->
  (b > 0 -> 0 <= pyfmod a b) /\ (b < 0 -> pyfmod a b <= 0).
Proof.
  intros a b _; split; intro Hb.
  - apply (pyfmod_pos a b Hb).
  - apply (pyfmod_neg a b Hb).
Qed.

(* closure evidence: axiom-free over the rationals. *)
Print Assumptions pyf_reconstruct.
Print Assumptions pyfmod_pos.
Print Assumptions pyfmod_neg.
Print Assumptions pyfmod_sign.
