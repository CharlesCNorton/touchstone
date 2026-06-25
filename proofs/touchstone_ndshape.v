(* Trust base, part X: the tensor (numpy / torch) shape algebra in core.py -- broadcasting, concatenation,
   matrix multiply, reshape, unsqueeze, and transpose -- over shapes as lists of natural dimensions.
   Axiom-clean (no axioms, no Admitted), gated by verify_coq.sh. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.

Definition shape := list nat.

(* The element count of a shape: the product of its dimensions (1 for the scalar shape []). _nd_size. *)
Definition numel (s : shape) : nat := fold_right Nat.mul 1 s.

Lemma numel_app : forall a b, numel (a ++ b) = numel a * numel b.
Proof.
  induction a as [|x a IH]; intro b; simpl.
  - lia.
  - rewrite IH; lia.
Qed.

Lemma numel_middle : forall pre x post,
  numel (pre ++ x :: post) = numel pre * (x * numel post).
Proof. intros; rewrite numel_app; reflexivity. Qed.

(* Concatenation (_cat_shape) along the middle axis sums that axis and adds the element counts. *)
Theorem cat_numel : forall pre a b post,
  numel (pre ++ a :: post) + numel (pre ++ b :: post) = numel (pre ++ (a + b) :: post).
Proof. intros; rewrite !numel_middle; lia. Qed.

(* Broadcasting one aligned dimension pair (_broadcast_shapes: when the accumulator is 1, take the other). *)
Definition compat (a b : nat) : Prop := a = b \/ a = 1 \/ b = 1.
Definition bcast_dim (a b : nat) : nat := if Nat.eqb a 1 then b else a.

Lemma bcast_dim_one_l : forall b, bcast_dim 1 b = b.
Proof. reflexivity. Qed.

Lemma bcast_dim_nonone : forall a b, a <> 1 -> bcast_dim a b = a.
Proof. intros a b H; unfold bcast_dim; destruct (Nat.eqb_spec a 1); [contradiction | reflexivity]. Qed.

(* The broadcast result is always one of the two operands. *)
Theorem bcast_dim_is_operand : forall a b, bcast_dim a b = a \/ bcast_dim a b = b.
Proof. intros a b; unfold bcast_dim; destruct (Nat.eqb_spec a 1); [right | left]; reflexivity. Qed.

(* For positive dimensions the broadcast is the larger one (a zero dimension is the degenerate
   empty-tensor case, where the model takes the zero -- as numpy does -- not the max). *)
Theorem bcast_dim_max : forall a b, compat a b -> 0 < a -> 0 < b -> bcast_dim a b = Nat.max a b.
Proof.
  intros a b H Pa Pb; unfold bcast_dim; destruct (Nat.eqb_spec a 1) as [Ha|Ha].
  - subst; lia.
  - destruct H as [H|[H|H]]; lia.
Qed.

(* A broadcast dimension dominates each positive compatible operand: the result fits both. *)
Theorem bcast_dim_ge : forall a b, compat a b -> 0 < a -> 0 < b ->
  a <= bcast_dim a b /\ b <= bcast_dim a b.
Proof. intros a b H Pa Pb; rewrite bcast_dim_max by assumption; lia. Qed.

(* Unsqueeze inserts a unit axis and preserves the element count (_nd_method unsqueeze). *)
Theorem unsqueeze_numel : forall pre post, numel (pre ++ 1 :: post) = numel (pre ++ post).
Proof. intros; rewrite numel_app, numel_app; simpl; lia. Qed.

(* Transpose / permute reverses (reorders) the axes and preserves the element count (_nd_method t). *)
Theorem transpose_numel : forall s, numel (rev s) = numel s.
Proof.
  induction s as [|x s IH]; simpl.
  - reflexivity.
  - rewrite numel_app; simpl; rewrite IH; lia.
Qed.

(* Matrix multiply output dimensions (_matmul): (m,k) @ (k,n) -> (m,n) with element count m*n; a
   mismatched inner dimension has no output (the RuntimeError the model emits as a trap). *)
Definition matmul_out (m k1 k2 n : nat) : option shape :=
  if Nat.eqb k1 k2 then Some [m; n] else None.

Theorem matmul_out_shape : forall m k n, matmul_out m k k n = Some [m; n].
Proof. intros; unfold matmul_out; rewrite Nat.eqb_refl; reflexivity. Qed.

Theorem matmul_out_numel : forall m k n s, matmul_out m k k n = Some s -> numel s = m * n.
Proof. intros m k n s H; rewrite matmul_out_shape in H; injection H as <-; simpl; lia. Qed.

Theorem matmul_mismatch : forall m k1 k2 n, k1 <> k2 -> matmul_out m k1 k2 n = None.
Proof. intros; unfold matmul_out; apply Nat.eqb_neq in H; rewrite H; reflexivity. Qed.

(* Reshape / view is faithful exactly when it preserves the element count (the total-size-mismatch trap),
   which the model checks as prod(new) = prod(old). *)
Definition reshape_ok (s s' : shape) : bool := Nat.eqb (numel s) (numel s').

Theorem reshape_ok_iff : forall s s', reshape_ok s s' = true <-> numel s = numel s'.
Proof. intros; unfold reshape_ok; apply Nat.eqb_eq. Qed.

Print Assumptions cat_numel.
Print Assumptions bcast_dim_max.
Print Assumptions matmul_out_numel.
Print Assumptions transpose_numel.
Print Assumptions reshape_ok_iff.
