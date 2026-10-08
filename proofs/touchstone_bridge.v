(* Trust base for touchstone, part XVI: the integer images behind the int / float bridge, machine-checked
   axiom-free over Z and Q.

   z3 does not decide a conversion between int and float soundly, so core._solve_fp_bridge never hands it one.
   A comparison of a conversion float(R) with a double c is rewritten to a comparison of R itself with a
   rational threshold (core._rne_bounds), and that comparison is put in integer form (core._real_cmp_const); a
   query over bounded integers is re-expressed at a fixed bitvector width, where the SMT-LIB Euclidean div / mod
   are built from the truncating bitvector quotient and remainder (core._bv_translate). This file proves the
   facts those steps rest on:

   - any monotone rounding sends an upward-closed set of reals to an upward-closed set, so `f r >= c` is a
     single threshold on r: the rewrite needs one bound per comparison, never a union of intervals;
   - an integer t lies at or above a rational m exactly when t >= ceil m, strictly above it exactly when
     t >= floor m + 1;
   - a quotient a / b compares with m as a compares with m * b, the direction flipping for a negative b;
   - the Euclidean quotient and remainder are the truncating ones corrected by one step when the truncating
     remainder is negative.

   The rounding intervals themselves (where the midpoints between neighbouring doubles fall, and which end a
   tie belongs to) are CPython's, and audit.rounding_threshold_audit holds them against its correctly rounded
   conversion. *)

From Stdlib Require Import ZArith Lia QArith Qround.
From Stdlib Require Import Lqa.

(* ---------------------------------------------------------------- monotone rounding: one threshold *)

Section Monotone.
  Variable f : Q -> Q.
  Hypothesis f_mono : forall x y, x <= y -> f x <= f y.

  (* {r | c <= f r} is upward closed: a comparison of f r with a constant is a single threshold on r *)
  Theorem round_ge_upward : forall c r r', c <= f r -> r <= r' -> c <= f r'.
  Proof. intros c r r' Hc Hr. apply Qle_trans with (f r); [exact Hc | apply f_mono; exact Hr]. Qed.

  (* {r | f r <= c} is downward closed *)
  Theorem round_le_downward : forall c r r', f r <= c -> r' <= r -> f r' <= c.
  Proof. intros c r r' Hc Hr. apply Qle_trans with (f r); [apply f_mono; exact Hr | exact Hc]. Qed.

  (* the reals rounding to one value form an interval (a convex set) *)
  Theorem round_preimage_convex : forall c r1 r r2,
    f r1 == c -> f r2 == c -> r1 <= r -> r <= r2 -> f r == c.
  Proof.
    intros c r1 r r2 H1 H2 Ha Hb.
    pose proof (f_mono r1 r Ha) as L. pose proof (f_mono r r2 Hb) as U.
    rewrite H1 in L. rewrite H2 in U. apply Qle_antisym; assumption.
  Qed.
End Monotone.

(* ---------------------------------------------------------------- integer images of rational thresholds *)

Lemma inject_le : forall a b : Z, (a <= b)%Z -> inject_Z a <= inject_Z b.
Proof. intros a b H. rewrite <- Zle_Qle. exact H. Qed.

(* t >= m  iff  t >= ceil m (for an integer t) *)
Theorem int_ge_rational : forall (t : Z) (m : Q), m <= inject_Z t <-> (Qceiling m <= t)%Z.
Proof.
  intros t m. split.
  - intro H. pose proof (Qceiling_resp_le m (inject_Z t) H) as Hc. rewrite Qceiling_Z in Hc. exact Hc.
  - intro H. apply Qle_trans with (inject_Z (Qceiling m)).
    + apply Qle_ceiling.
    + apply inject_le. exact H.
Qed.

(* t > m  iff  t >= floor m + 1 (for an integer t) *)
Theorem int_gt_rational : forall (t : Z) (m : Q), m < inject_Z t <-> (Qfloor m + 1 <= t)%Z.
Proof.
  intros t m. split.
  - intro H. assert (Hf : (Qfloor m < t)%Z).
    { apply Z.nle_gt. intro Hle.
      assert (Hq : inject_Z t <= inject_Z (Qfloor m)) by (apply inject_le; exact Hle).
      pose proof (Qfloor_le m) as Hfl. apply (Qlt_irrefl m). apply Qlt_le_trans with (inject_Z t); auto.
      apply Qle_trans with (inject_Z (Qfloor m)); auto. }
    lia.
  - intro H. apply Qlt_le_trans with (inject_Z (Qfloor m + 1)).
    + pose proof (Qlt_floor m) as Hl. exact Hl.
    + apply inject_le. exact H.
Qed.

(* ---------------------------------------------------------------- a quotient against a threshold *)

(* for a positive divisor, a / b >= m iff a >= m * b *)
Theorem quot_ge_pos : forall a b m : Q, 0 < b -> (m <= a / b <-> m * b <= a).
Proof.
  intros a b m Hb. assert (Hbne : ~ b == 0) by (intro E; rewrite E in Hb; apply (Qlt_irrefl 0); exact Hb).
  split.
  - intro H. assert (E : a / b * b == a) by (field; exact Hbne).
    rewrite <- E. apply Qmult_le_compat_r; [exact H | apply Qlt_le_weak; exact Hb].
  - intro H. apply Qle_shift_div_l; [exact Hb | exact H].
Qed.

(* for a negative divisor the direction flips: a / b >= m iff a <= m * b *)
Theorem quot_ge_neg : forall a b m : Q, b < 0 -> (m <= a / b <-> a <= m * b).
Proof.
  intros a b m Hb.
  assert (Hnb : 0 < - b) by lra.
  assert (Hbne : ~ b == 0) by lra.
  assert (E : a / b == (- a) / (- b)) by (field; exact Hbne).
  rewrite E. rewrite (quot_ge_pos (- a) (- b) m Hnb). split; intro H; nra.
Qed.

(* ---------------------------------------------------------------- Euclidean division from truncation *)

(* SMT-LIB div / mod are Euclidean: a = b * q + r with 0 <= r < |b|. The bitvector image builds them from the
   truncating quotient and remainder (bvsdiv / bvsrem), corrected by one step when the remainder is negative. *)
Definition ediv (a b : Z) : Z :=
  let q := Z.quot a b in let r := Z.rem a b in
  if (r <? 0)%Z then (if (0 <? b)%Z then (q - 1)%Z else (q + 1)%Z) else q.
Definition emod (a b : Z) : Z :=
  let r := Z.rem a b in
  if (r <? 0)%Z then (if (0 <? b)%Z then (r + b)%Z else (r - b)%Z) else r.

Theorem ediv_emod_euclidean : forall a b : Z, b <> 0%Z ->
  a = (b * ediv a b + emod a b)%Z /\ (0 <= emod a b < Z.abs b)%Z.
Proof.
  intros a b Hb. unfold ediv, emod.
  pose proof (Z.quot_rem' a b) as Hqr.
  pose proof (Z.rem_bound_abs a b Hb) as Hbd.
  destruct (Z.rem a b <? 0)%Z eqn:Hr; destruct (0 <? b)%Z eqn:Hp;
    rewrite ?Z.ltb_lt, ?Z.ltb_ge in Hr, Hp; split; lia.
Qed.

(* the Euclidean pair is unique, so the image is SMT-LIB's div / mod themselves *)
Theorem euclidean_unique : forall a b q1 r1 q2 r2 : Z, b <> 0%Z ->
  a = (b * q1 + r1)%Z -> (0 <= r1 < Z.abs b)%Z ->
  a = (b * q2 + r2)%Z -> (0 <= r2 < Z.abs b)%Z -> q1 = q2 /\ r1 = r2.
Proof.
  intros a b q1 r1 q2 r2 Hb E1 B1 E2 B2.
  assert (Hq : q1 = q2).
  { destruct (Z.lt_total q1 q2) as [Hlt | [Heq | Hgt]]; [exfalso | exact Heq | exfalso].
    - destruct (Z.lt_total 0 b) as [Hpos | [Hz | Hneg]]; [| lia |];
        [rewrite Z.abs_eq in B1, B2 by lia | rewrite Z.abs_neq in B1, B2 by lia]; nia.
    - destruct (Z.lt_total 0 b) as [Hpos | [Hz | Hneg]]; [| lia |];
        [rewrite Z.abs_eq in B1, B2 by lia | rewrite Z.abs_neq in B1, B2 by lia]; nia. }
  subst q2. split; [reflexivity | lia].
Qed.

(* closure evidence: axiom-free over Z and Q. *)
Print Assumptions round_ge_upward.
Print Assumptions round_le_downward.
Print Assumptions round_preimage_convex.
Print Assumptions int_ge_rational.
Print Assumptions int_gt_rational.
Print Assumptions quot_ge_pos.
Print Assumptions quot_ge_neg.
Print Assumptions ediv_emod_euclidean.
Print Assumptions euclidean_unique.
