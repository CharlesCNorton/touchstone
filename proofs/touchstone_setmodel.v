(* Trust base, part VII: the heap engine's set-payload laws (core.py _heap_sin / _heap_sn) -- membership
   and size under add / remove, with dedup. Axiom-clean, gated by verify_coq.sh. *)

From Stdlib Require Import ZArith Lia List ListSet.
Import ListNotations.
Open Scope Z_scope.

Definition supd (m : Z -> bool) (x : Z) (b : bool) : Z -> bool :=
  fun j => if Z.eqb j x then b else m j.

(* a set: a membership predicate and a size. *)
Record vset := mkset { mem : Z -> bool; ssize : Z }.

Definition sadd (s : vset) (x : Z) : vset :=
  if mem s x then s else mkset (supd (mem s) x true) (ssize s + 1).
Definition srem (s : vset) (x : Z) : vset :=
  if mem s x then mkset (supd (mem s) x false) (ssize s - 1) else s.

(* x is a member after add. *)
Theorem sadd_mem : forall s x, mem (sadd s x) x = true.
Proof.
  intros s x; unfold sadd; destruct (mem s x) eqn:E; [exact E |].
  simpl; unfold supd; rewrite Z.eqb_refl; reflexivity.
Qed.

(* add frames every other element. *)
Theorem sadd_frame : forall s x y, y <> x -> mem (sadd s x) y = mem s y.
Proof.
  intros s x y H; unfold sadd; destruct (mem s x) eqn:E; [reflexivity |].
  simpl; unfold supd; destruct (Z.eqb y x) eqn:Eb; [apply Z.eqb_eq in Eb; lia | reflexivity].
Qed.

(* adding a new element grows the size by one; adding a present one leaves it. *)
Theorem sadd_size_new : forall s x, mem s x = false -> ssize (sadd s x) = ssize s + 1.
Proof. intros s x H; unfold sadd; rewrite H; reflexivity. Qed.

Theorem sadd_size_present : forall s x, mem s x = true -> ssize (sadd s x) = ssize s.
Proof. intros s x H; unfold sadd; rewrite H; reflexivity. Qed.

(* dedup: adding the same element twice adds it once (size and membership idempotent). *)
Theorem sadd_idem_size : forall s x, ssize (sadd (sadd s x) x) = ssize (sadd s x).
Proof. intros s x; apply sadd_size_present; apply sadd_mem. Qed.

(* x is not a member after remove. *)
Theorem srem_not_mem : forall s x, mem (srem s x) x = false.
Proof.
  intros s x; unfold srem; destruct (mem s x) eqn:E; [| exact E].
  simpl; unfold supd; rewrite Z.eqb_refl; reflexivity.
Qed.

Print Assumptions sadd_mem.
Print Assumptions sadd_frame.
Print Assumptions sadd_size_new.
Print Assumptions sadd_size_present.
Print Assumptions sadd_idem_size.
Print Assumptions srem_not_mem.

(* The value engine's set BINARY operations (core.py _set_binop / _seq_member): for a set-like operand of
   two sets it asserts to z3 the result's membership (union = Or, intersection = And, difference = And-not,
   symmetric difference = their union) and the size bounds below. Modelling a finite set as a
   duplicate-free list (cardinality = length), each fact the engine feeds the solver is proven sound. *)

Definition zunion := set_union Z.eq_dec.
Definition zinter := set_inter Z.eq_dec.
Definition zdiff  := set_diff  Z.eq_dec.
Definition zsymdiff (a b : set Z) : set Z := zunion (zdiff a b) (zdiff b a).
Definition card (a : set Z) : Z := Z.of_nat (length a).

(* membership: _seq_member combines the operands as Or / And / And-not, symmetric difference as their union. *)
Theorem union_member : forall a b x, set_In x (zunion a b) <-> set_In x a \/ set_In x b.
Proof. intros a b x; apply set_union_iff. Qed.

Theorem inter_member : forall a b x, set_In x (zinter a b) <-> set_In x a /\ set_In x b.
Proof. intros a b x; apply set_inter_iff. Qed.

Theorem diff_member : forall a b x, set_In x (zdiff a b) <-> set_In x a /\ ~ set_In x b.
Proof. intros a b x; apply set_diff_iff. Qed.

Theorem symdiff_member : forall a b x,
  set_In x (zsymdiff a b) <-> (set_In x a /\ ~ set_In x b) \/ (set_In x b /\ ~ set_In x a).
Proof.
  intros a b x; unfold zsymdiff, zunion, zdiff.
  rewrite set_union_iff, !set_diff_iff; reflexivity.
Qed.

(* length helper lemmas (nat). *)
Lemma set_add_len_le : forall (x : Z) s, (length (set_add Z.eq_dec x s) <= S (length s))%nat.
Proof.
  intros x s; induction s as [|y s IH]; simpl; [lia|].
  destruct (Z.eq_dec x y); simpl; lia.
Qed.

Lemma inter_len_le_l : forall a b, (length (set_inter Z.eq_dec a b) <= length a)%nat.
Proof.
  induction a as [|x a IH]; intro b; simpl; [lia|].
  pose proof (IH b) as H; destruct (set_mem Z.eq_dec x b); simpl; lia.
Qed.

Lemma diff_len_le : forall a b, (length (set_diff Z.eq_dec a b) <= length a)%nat.
Proof.
  induction a as [|x a IH]; intro b; simpl; [lia|].
  pose proof (IH b) as H; destruct (set_mem Z.eq_dec x b).
  - simpl; lia.
  - pose proof (set_add_len_le x (set_diff Z.eq_dec a b)) as Ha; simpl; lia.
Qed.

Lemma union_len_le : forall a b, (length (set_union Z.eq_dec a b) <= length a + length b)%nat.
Proof.
  intros a b; induction b as [|y b IH]; simpl; [lia|].
  pose proof (set_add_len_le y (set_union Z.eq_dec a b)) as Ha; lia.
Qed.

(* a is a subset of a | b, and NoDup a, so |a| <= |a | b|. *)
Lemma union_len_ge_l : forall a b, NoDup a -> (length a <= length (set_union Z.eq_dec a b))%nat.
Proof.
  intros a b Na; apply NoDup_incl_length; [exact Na|].
  intros x Hx; apply set_union_iff; left; exact Hx.
Qed.

Lemma union_len_ge_r : forall a b, NoDup b -> (length b <= length (set_union Z.eq_dec a b))%nat.
Proof.
  intros a b Nb; apply NoDup_incl_length; [exact Nb|].
  intros x Hx; apply set_union_iff; right; exact Hx.
Qed.

(* a & b is a subset of b and (for NoDup a) duplicate-free, so |a & b| <= |b|. *)
Lemma inter_len_le_r : forall a b, NoDup a -> NoDup b -> (length (set_inter Z.eq_dec a b) <= length b)%nat.
Proof.
  intros a b Na Nb; apply NoDup_incl_length.
  - apply set_inter_nodup; assumption.
  - intros x Hx; apply set_inter_iff in Hx; apply Hx.
Qed.

(* every element of a NoDup a is counted once, in exactly one of a & b or a - b. *)
Lemma partition_len : forall a b, NoDup a ->
  (length a = length (set_inter Z.eq_dec a b) + length (set_diff Z.eq_dec a b))%nat.
Proof.
  induction a as [|x a IH]; intros b Na; simpl; [reflexivity|].
  inversion Na as [|x0 a0 Hx Na' [Ex Ea]]; subst.
  specialize (IH b Na'); destruct (set_mem Z.eq_dec x b) eqn:Em.
  - simpl; lia.
  - assert (Hnin : ~ set_In x (set_diff Z.eq_dec a b)).
    { intro Hin; apply set_diff_iff in Hin; apply Hx, (proj1 Hin). }
    assert (Hlen : (length (set_add Z.eq_dec x (set_diff Z.eq_dec a b))
                   = S (length (set_diff Z.eq_dec a b)))%nat).
    { clear IH Em; induction (set_diff Z.eq_dec a b) as [|y d IHd]; simpl; [reflexivity|].
      destruct (Z.eq_dec x y) as [Exy|Exy].
      - exfalso; apply Hnin; left; symmetry; exact Exy.
      - simpl; rewrite IHd; [reflexivity | intro Hd; apply Hnin; right; exact Hd]. }
    simpl; rewrite Hlen; lia.
Qed.

(* the size bounds _set_binop asserts to z3: nonneg; union superset of each and <= their sum; intersection
   subset of each; difference drops at most |r| (>= |l| - |r|) and at most all of l; symmetric difference
   <= |l| + |r|. *)
Theorem card_nonneg : forall a, 0 <= card a.
Proof. intro a; unfold card; apply Zle_0_nat. Qed.

Theorem union_card_le : forall a b, card (zunion a b) <= card a + card b.
Proof. intros a b; unfold card, zunion; pose proof (union_len_le a b) as H; lia. Qed.

Theorem union_card_ge_l : forall a b, NoDup a -> card a <= card (zunion a b).
Proof. intros a b Na; unfold card, zunion; pose proof (union_len_ge_l a b Na) as H; lia. Qed.

Theorem union_card_ge_r : forall a b, NoDup b -> card b <= card (zunion a b).
Proof. intros a b Nb; unfold card, zunion; pose proof (union_len_ge_r a b Nb) as H; lia. Qed.

Theorem inter_card_le_l : forall a b, card (zinter a b) <= card a.
Proof. intros a b; unfold card, zinter; pose proof (inter_len_le_l a b) as H; lia. Qed.

Theorem inter_card_le_r : forall a b, NoDup a -> NoDup b -> card (zinter a b) <= card b.
Proof. intros a b Na Nb; unfold card, zinter; pose proof (inter_len_le_r a b Na Nb) as H; lia. Qed.

Theorem diff_card_le : forall a b, card (zdiff a b) <= card a.
Proof. intros a b; unfold card, zdiff; pose proof (diff_len_le a b) as H; lia. Qed.

Theorem diff_card_ge : forall a b, NoDup a -> NoDup b -> card a - card b <= card (zdiff a b).
Proof.
  intros a b Na Nb; unfold card, zdiff.
  pose proof (partition_len a b Na) as Hp.
  pose proof (inter_len_le_r a b Na Nb) as Hi.
  lia.
Qed.

Theorem symdiff_card_le : forall a b, NoDup a -> NoDup b -> card (zsymdiff a b) <= card a + card b.
Proof.
  intros a b Na Nb; unfold zsymdiff.
  pose proof (union_card_le (zdiff a b) (zdiff b a)) as Hu.
  pose proof (diff_card_le a b) as Ha.
  pose proof (diff_card_le b a) as Hb.
  lia.
Qed.

Print Assumptions union_member.
Print Assumptions inter_member.
Print Assumptions diff_member.
Print Assumptions symdiff_member.
Print Assumptions card_nonneg.
Print Assumptions union_card_le.
Print Assumptions union_card_ge_l.
Print Assumptions union_card_ge_r.
Print Assumptions inter_card_le_l.
Print Assumptions inter_card_le_r.
Print Assumptions diff_card_le.
Print Assumptions diff_card_ge.
Print Assumptions symdiff_card_le.
