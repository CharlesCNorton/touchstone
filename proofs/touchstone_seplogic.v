(* Trust base for touchstone, part VI: soundness of the separation-logic frame reasoning, machine-checked.

   The heap / aliasing engine represents object fields, list payloads, and dict maps as McCarthy arrays and
   FRAMES every write: a store to one cell is invisible to any disjoint part of the heap. touchstone_encoders.v
   proved the operational core (read-after-write and frame on a single array); this file lifts it to the
   separation-logic level the framing relies on -- separating conjunction over disjoint heaps, and the FRAME
   RULE: a locally-acting command preserves any spatially-disjoint assertion R, so reasoning about one object
   never has to mention another. The concrete heap mutation is shown to be local and to satisfy its small
   triple, so the frame rule is not vacuous.

   Heaps are partial maps Z -> option Z compared by extensional equality (heq), deliberately avoiding
   functional extensionality, which is an axiom: every theorem here is closed under the global context, with
   no axioms and no Admitted. *)

From Stdlib Require Import ZArith.
Open Scope Z_scope.

(* ---- heaps as finite-domain partial maps, with extensional (pointwise) equality ---- *)
Definition heap := Z -> option Z.
Definition heq (h1 h2 : heap) : Prop := forall x, h1 x = h2 x.
Definition emp : heap := fun _ => None.
Definition hupd (a v : Z) (h : heap) : heap := fun x => if Z.eqb x a then Some v else h x.
Definition hsingle (a v : Z) : heap := hupd a v emp.                       (* the cell  a |-> v *)
Definition indom (h : heap) (a : Z) : Prop := exists v, h a = Some v.
Definition hdisjoint (h1 h2 : heap) : Prop := forall x, h1 x = None \/ h2 x = None.
Definition hunion (h1 h2 : heap) : heap := fun x => match h1 x with Some v => Some v | None => h2 x end.

Lemma heq_refl : forall h, heq h h.
Proof. intros h x; reflexivity. Qed.
Lemma heq_sym : forall h k, heq h k -> heq k h.
Proof. intros h k H x; symmetry; apply H. Qed.
Lemma heq_trans : forall h k m, heq h k -> heq k m -> heq h m.
Proof. intros h k m H1 H2 x; rewrite H1; apply H2. Qed.
Lemma hupd_cong : forall a v h k, heq h k -> heq (hupd a v h) (hupd a v k).
Proof. intros a v h k H x; unfold hupd; destruct (Z.eqb x a); [reflexivity | apply H]. Qed.
Lemma indom_heq : forall h k a, heq h k -> indom h a -> indom k a.
Proof. intros h k a H [v Hv]; exists v; rewrite <- H; exact Hv. Qed.

(* ---- assertions and the separating conjunction ---- *)
Definition assn := heap -> Prop.
Definition pointsto (a v : Z) : assn := fun h => heq h (hsingle a v).
Definition sepconj (P Q : assn) : assn :=
  fun h => exists h1 h2, P h1 /\ Q h2 /\ hdisjoint h1 h2 /\ heq h (hunion h1 h2).

(* ---- the calculational lemmas the frame rule turns on ---- *)
Lemma disjoint_indom_r : forall h1 h2 a, hdisjoint h1 h2 -> indom h1 a -> h2 a = None.
Proof.
  intros h1 h2 a Hdis [v Hv]. destruct (Hdis a) as [H | H]; [rewrite Hv in H; discriminate | exact H].
Qed.

Lemma indom_union_l : forall h1 h2 a, indom h1 a -> indom (hunion h1 h2) a.
Proof. intros h1 h2 a [v Hv]; exists v; unfold hunion; rewrite Hv; reflexivity. Qed.

(* a store to a cell of h1 distributes over a disjoint union: the frame h2 is untouched. *)
Lemma hupd_union_l : forall a v h1 h2, h2 a = None ->
  heq (hupd a v (hunion h1 h2)) (hunion (hupd a v h1) h2).
Proof.
  intros a v h1 h2 Hh2 x; unfold hupd, hunion.
  destruct (Z.eqb x a) eqn:E.
  - apply Z.eqb_eq in E; subst x. reflexivity.
  - destruct (h1 x); reflexivity.
Qed.

Lemma hupd_keeps_disjoint : forall a v h1 h2, h2 a = None -> hdisjoint h1 h2 -> hdisjoint (hupd a v h1) h2.
Proof.
  intros a v h1 h2 Hh2 Hdis x; unfold hupd.
  destruct (Z.eqb x a) eqn:E.
  - apply Z.eqb_eq in E; subst x. right; exact Hh2.
  - destruct (Hdis x) as [H | H]; [left; exact H | right; exact H].
Qed.

(* ---- commands as heap relations; locality (heq-insensitivity + safety monotonicity + frame property) ---- *)
Definition cmd := heap -> heap -> Prop.
Definition safe (c : cmd) (h : heap) : Prop := exists h', c h h'.

Definition local (c : cmd) : Prop :=
  (forall h k h', heq h k -> c h h' -> c k h')                                  (* insensitive to heq on entry *)
  /\ (forall h1 h2, hdisjoint h1 h2 -> safe c h1 -> safe c (hunion h1 h2))      (* safety monotonicity *)
  /\ (forall h1 h2 h', hdisjoint h1 h2 -> safe c h1 -> c (hunion h1 h2) h' ->   (* frame property *)
        exists h1', heq h' (hunion h1' h2) /\ hdisjoint h1' h2 /\ c h1 h1').

(* a Hoare triple, fault-avoiding: P guarantees the command is safe, and every result it reaches is in Q. *)
Definition triple (P : assn) (c : cmd) (Q : assn) : Prop :=
  forall h, P h -> safe c h /\ (forall h', c h h' -> Q h').

(* ===================================================================================================== *)
(* THE FRAME RULE: a locally-acting command preserves any disjoint frame R.                               *)
(* ===================================================================================================== *)
Theorem frame_rule : forall P c Q R,
  local c -> triple P c Q -> triple (sepconj P R) c (sepconj Q R).
Proof.
  intros P c Q R [Hcong [Hsm Hfp]] Hpcq h Hpr.
  destruct Hpr as [hp [hr [HP [HR [Hdis Heq]]]]].
  destruct (Hpcq hp HP) as [Hsafe_p HQ].
  split.
  - destruct (Hsm hp hr Hdis Hsafe_p) as [hu Hcu].
    exists hu. apply (Hcong (hunion hp hr) h hu (heq_sym _ _ Heq) Hcu).
  - intros h' Hch.
    assert (Hch' : c (hunion hp hr) h') by exact (Hcong h (hunion hp hr) h' Heq Hch).
    destruct (Hfp hp hr h' Hdis Hsafe_p Hch') as [hp' [Heq' [Hdis' Hc']]].
    exists hp', hr. repeat split.
    + exact (HQ hp' Hc').
    + exact HR.
    + exact Hdis'.
    + exact Heq'.
Qed.

(* ===================================================================================================== *)
(* The concrete heap mutation is local and satisfies its small triple, so the frame rule is not vacuous. *)
(* ===================================================================================================== *)
Definition mutate (a v : Z) : cmd := fun h h' => indom h a /\ heq h' (hupd a v h).

Lemma mutate_local : forall a v, local (mutate a v).
Proof.
  intros a v; split; [| split].
  - (* insensitive to heq on entry *)
    intros h k h' Hhk [Hind Hh']. split.
    + exact (indom_heq h k a Hhk Hind).
    + exact (heq_trans h' (hupd a v h) (hupd a v k) Hh' (hupd_cong a v h k Hhk)).
  - (* safety monotonicity *)
    intros h1 h2 Hdis [h' [Hind _]].
    exists (hupd a v (hunion h1 h2)). split; [apply indom_union_l; exact Hind | apply heq_refl].
  - (* frame property *)
    intros h1 h2 h' Hdis [hs [Hind _]] [_ Hh'].
    exists (hupd a v h1). split; [| split].
    + apply (heq_trans h' (hupd a v (hunion h1 h2)) (hunion (hupd a v h1) h2) Hh').
      apply hupd_union_l. exact (disjoint_indom_r h1 h2 a Hdis Hind).
    + apply hupd_keeps_disjoint; [exact (disjoint_indom_r h1 h2 a Hdis Hind) | exact Hdis].
    + split; [exact Hind | apply heq_refl].
Qed.

Theorem mutate_triple : forall a v0 v, triple (pointsto a v0) (mutate a v) (pointsto a v).
Proof.
  intros a v0 v h Hp; split.
  - exists (hupd a v h). split.
    + exists v0. rewrite (Hp a). unfold hsingle, hupd, emp. rewrite Z.eqb_refl. reflexivity.
    + apply heq_refl.
  - intros h' [_ Hh'] x. rewrite (Hh' x). unfold hsingle, hupd, emp.
    destruct (Z.eqb x a) eqn:E.
    + reflexivity.
    + rewrite (Hp x). unfold hsingle, hupd, emp. rewrite E. reflexivity.
Qed.

(* the framed instance, by the frame rule: mutating one cell leaves any disjoint assertion R intact. *)
Corollary framed_mutate : forall a v0 v R,
  triple (sepconj (pointsto a v0) R) (mutate a v) (sepconj (pointsto a v) R).
Proof. intros a v0 v R; apply frame_rule; [apply mutate_local | apply mutate_triple]. Qed.

(* closure evidence *)
Print Assumptions frame_rule.
Print Assumptions mutate_local.
Print Assumptions mutate_triple.
Print Assumptions framed_mutate.
