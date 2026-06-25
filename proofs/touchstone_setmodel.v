(* Trust base, part VII: the heap engine's set-payload laws (core.py _heap_sin / _heap_sn) -- membership
   and size under add / remove, with dedup. Axiom-clean, gated by verify_coq.sh. *)

From Stdlib Require Import ZArith Lia.
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
