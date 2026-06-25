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

(* No axioms: the list-payload laws hold in the kernel's own logic. *)
Print Assumptions lappend_len.
Print Assumptions lappend_get_new.
Print Assumptions lappend_frame.
Print Assumptions lpop_len.
Print Assumptions append_pop_top.
