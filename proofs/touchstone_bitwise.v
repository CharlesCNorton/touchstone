(* Trust base, part VIII: the value engine's exact integer-bitwise identities (core.py ev): a << k = a*2^k,
   a >> k = a//2^k, a & (2^k - 1) = a mod 2^k, ~a = -a-1. Axiom-clean, gated by verify_coq.sh. *)

From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

(* a << k is multiplication by 2^k. *)
Theorem shl_mul : forall a k, 0 <= k -> Z.shiftl a k = a * 2 ^ k.
Proof. intros; apply Z.shiftl_mul_pow2; assumption. Qed.

(* a >> k is floor division by 2^k (Python's floored >>). *)
Theorem shr_div : forall a k, 0 <= k -> Z.shiftr a k = a / 2 ^ k.
Proof. intros; apply Z.shiftr_div_pow2; assumption. Qed.

(* ~a is -a-1. *)
Theorem lnot_eq : forall a, Z.lnot a = - a - 1.
Proof. intro a; unfold Z.lnot; lia. Qed.

(* a & (2^k - 1) masks the low k bits, equal to a mod 2^k. *)
Theorem land_low_mask : forall a k, 0 <= k -> Z.land a (2 ^ k - 1) = a mod 2 ^ k.
Proof.
  intros a k Hk; replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia).
  apply Z.land_ones; assumption.
Qed.

Print Assumptions shl_mul.
Print Assumptions shr_div.
Print Assumptions lnot_eq.
Print Assumptions land_low_mask.
