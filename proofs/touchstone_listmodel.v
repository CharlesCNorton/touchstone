(* Trust base, part VI: the heap engine's list-payload laws (core.py _heap_arr / _heap_len) as
   McCarthy-array consequences. Axiom-clean, gated by verify_coq.sh. *)

From Stdlib Require Import ZArith List Lia.
Open Scope Z_scope.

Definition array := Z -> Z.
Definition select (a : array) (i : Z) : Z := a i.
Definition store (a : array) (i v : Z) : array := fun j => if Z.eqb j i then v else a j.

Lemma select_store_same : forall a i v, select (store a i v) i = v.
Proof. intros; unfold select, store; rewrite Z.eqb_refl; reflexivity. Qed.

Lemma select_store_other : forall a i j v, i <> j -> select (store a i v) j = select a j.
Proof.
  intros a i j v H; unfold select, store.
  destruct (Z.eqb j i) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity].
Qed.

(* a list value: a backing array of elements and a length. *)
Record vlist := mkvlist { backing : array; vlen : Z }.

Definition lget (l : vlist) (i : Z) : Z := select (backing l) i.
Definition lappend (l : vlist) (x : Z) : vlist := mkvlist (store (backing l) (vlen l) x) (vlen l + 1).
Definition lpop (l : vlist) : vlist := mkvlist (backing l) (vlen l - 1).

(* append increments the length. *)
Theorem lappend_len : forall l x, vlen (lappend l x) = vlen l + 1.
Proof. reflexivity. Qed.

(* the appended element reads back at the old length. *)
Theorem lappend_get_new : forall l x, lget (lappend l x) (vlen l) = x.
Proof. intros; unfold lget, lappend; simpl; apply select_store_same. Qed.

(* append frames every existing index: an element already in the list is unchanged. *)
Theorem lappend_frame : forall l x i, i <> vlen l -> lget (lappend l x) i = lget l i.
Proof. intros l x i H; unfold lget, lappend; simpl; apply select_store_other; lia. Qed.

(* pop decrements the length. *)
Theorem lpop_len : forall l, vlen (lpop l) = vlen l - 1.
Proof. reflexivity. Qed.

(* stack semantics: append x then pop returns x and restores the original length. *)
Theorem append_pop_top : forall l x,
  lget (lappend l x) (vlen (lpop (lappend l x))) = x /\ vlen (lpop (lappend l x)) = vlen l.
Proof.
  intros l x; unfold lpop, lappend, lget; simpl; split.
  - replace (vlen l + 1 - 1) with (vlen l) by lia; apply select_store_same.
  - lia.
Qed.

(* --- sum over a sequence: the fold the value engine's sum() abstracts, and the non-negativity law behind
   sum(range(...)) >= 0 (1.53.0). A sum of non-negative elements is non-negative; a range from a non-negative
   start (step 1) has every element >= the start, hence >= 0, hence a non-negative sum. *)
Fixpoint lsum (l : list Z) : Z :=
  match l with nil => 0 | cons x r => x + lsum r end.

Theorem lsum_nonneg : forall l, (forall x, In x l -> 0 <= x) -> 0 <= lsum l.
Proof.
  induction l as [| h t IH]; intros H; simpl.
  - lia.
  - assert (0 <= h) by (apply H; left; reflexivity).
    assert (0 <= lsum t) by (apply IH; intros x Hx; apply H; right; exact Hx).
    lia.
Qed.

(* range(a, a+n) as the value engine iterates it: n elements starting at a, step 1. *)
Fixpoint zrange (a : Z) (n : nat) : list Z :=
  match n with O => nil | S k => cons a (zrange (a + 1) k) end.

Theorem zrange_elem_ge : forall n a x, In x (zrange a n) -> a <= x.
Proof.
  induction n as [| k IH]; intros a x H; simpl in H.
  - contradiction.
  - destruct H as [E | H]; [subst; lia |].
    assert (a + 1 <= x) by (apply IH; exact H). lia.
Qed.

(* the 1.53.0 law: a range with a non-negative start has a non-negative sum. *)
Theorem zrange_sum_nonneg : forall n a, 0 <= a -> 0 <= lsum (zrange a n).
Proof.
  intros n a Ha. apply lsum_nonneg. intros x Hx.
  assert (a <= x) by (apply zrange_elem_ge with (n := n); exact Hx). lia.
Qed.

(* --- min / max element bounds: the sound model for the aggregate relational specs max(a) >= a[i] and
   min(a) <= a[i]. The engine currently returns a fresh element for min/max (sound but imprecise); these
   laws are what a precise model would preserve -- the maximum is >= every element, the minimum <= every
   element -- so a relational spec against a member would decide. *)
Fixpoint lmax (l : list Z) (d : Z) : Z :=
  match l with nil => d | cons x r => Z.max x (lmax r d) end.

Fixpoint lmin (l : list Z) (d : Z) : Z :=
  match l with nil => d | cons x r => Z.min x (lmin r d) end.

Theorem lmax_ge : forall l d x, In x l -> x <= lmax l d.
Proof.
  induction l as [| h t IH]; intros d x H; simpl in H; [contradiction |].
  destruct H as [E | H]; simpl.
  - subst. apply Z.le_max_l.
  - apply Z.le_trans with (lmax t d); [apply IH; exact H | apply Z.le_max_r].
Qed.

Theorem lmin_le : forall l d x, In x l -> lmin l d <= x.
Proof.
  induction l as [| h t IH]; intros d x H; simpl in H; [contradiction |].
  destruct H as [E | H]; simpl.
  - subst. apply Z.le_min_l.
  - apply Z.le_trans with (lmin t d); [apply Z.le_min_r | apply IH; exact H].
Qed.

(* No axioms: the list-payload laws hold in the kernel's own logic. *)
Print Assumptions lappend_len.
Print Assumptions lappend_get_new.
Print Assumptions lappend_frame.
Print Assumptions lpop_len.
Print Assumptions append_pop_top.
Print Assumptions lsum_nonneg.
Print Assumptions zrange_elem_ge.
Print Assumptions zrange_sum_nonneg.
Print Assumptions lmax_ge.
Print Assumptions lmin_le.
