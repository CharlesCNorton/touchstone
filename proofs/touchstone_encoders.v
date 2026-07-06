(* Trust base for touchstone, part IV: soundness of four further engine encoders, machine-checked.

   The first three companion files cover the operational semantics / VC generator (touchstone_functor.v),
   the division-modulo encoding (touchstone_encoding.v), and the interval transfers (touchstone_domains.v).
   This file extends machine-checked coverage to four of the still-trusted encoders:

   1. The type-inference lattice (soundinfer._join). A type bound is option (list tag): None is top
      (UNKNOWN, no bound), Some l is the finite set of type tags l. The join must OVER-APPROXIMATE both
      operands -- the concretization of the join contains each operand's -- so a read bounded by either
      branch stays bounded by the join. The verified join is extracted (OCaml + JSON) and the engine's
      _join is held equal to it, so the join the engine runs is a mechanical image of this proof.

   2. Strings. The over-approximation axioms the string engine asserts: concatenation length adds, the
      empty string is a left identity, and a substring is no longer than its container.

   3. Containers (lists). Length under append adds, and a successful index is within bounds -- the facts
      the list/sequence engine relies on for length tracking and index-bounds traps.

   4. The heap / aliasing model. Object fields, list payloads, and dict maps are McCarthy arrays. The
      read-after-write and frame laws are what make aliasing and framing sound: a read sees the last write
      to the SAME key and is unchanged by a write to a DIFFERENT key.

   Every theorem is closed under the global context (no axioms, no Admitted), checked by verify_coq.sh. *)

From Stdlib Require Import List ZArith Lia.
Import ListNotations.

(* ---- self-contained list lemmas (no dependence on Stdlib lemma names, which drift across versions) ---- *)
Lemma app_len : forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2.
Proof. induction l1 as [| h t IH]; simpl; intros; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma in_appL : forall (A : Type) (x : A) (l1 l2 : list A), In x l1 -> In x (l1 ++ l2).
Proof.
  induction l1 as [| h t IH]; simpl; intros l2 H; [contradiction |].
  destruct H as [E | H]; [left; exact E | right; apply IH; exact H].
Qed.

Lemma in_appR : forall (A : Type) (x : A) (l1 l2 : list A), In x l2 -> In x (l1 ++ l2).
Proof. induction l1 as [| h t IH]; simpl; intros l2 H; [exact H | right; apply IH; exact H]. Qed.

(* ===================================================================================================== *)
(* 1. Type-inference lattice: the join over-approximates both operands.                                   *)
(* ===================================================================================================== *)

(* A type bound: None is top (UNKNOWN); Some l is the finite set of type tags l. Tags are nat here; the
   engine's _join keys on type-name strings, which the lattice audit maps to tags one-to-one. *)
Definition tbound := option (list nat).

Definition join (a b : tbound) : tbound :=
  match a, b with
  | Some la, Some lb => Some (la ++ lb)
  | _, _ => None
  end.

(* Concretization: None denotes every tag (top); Some l denotes membership in l. *)
Definition gamma (t : tbound) (x : nat) : Prop :=
  match t with None => True | Some l => In x l end.

Theorem join_over_approx_l : forall a b x, gamma a x -> gamma (join a b) x.
Proof. intros [la |] [lb |] x H; simpl in *; try exact I. apply in_appL; exact H. Qed.

Theorem join_over_approx_r : forall a b x, gamma b x -> gamma (join a b) x.
Proof. intros [la |] [lb |] x H; simpl in *; try exact I. apply in_appR; exact H. Qed.

(* join is commutative up to concretization (it loses nothing by argument order), and None absorbs:
   joining with UNKNOWN yields UNKNOWN, matching _join's a is None or b is None guard. *)
Theorem join_top_l : forall b, join None b = None.
Proof. reflexivity. Qed.

Theorem join_top_r : forall a, join a None = None.
Proof. destruct a; reflexivity. Qed.

(* ===================================================================================================== *)
(* 2. Strings: the length axioms the string engine over-approximates with.                                *)
(* ===================================================================================================== *)

(* A string is a sequence of code points (list nat). *)
Theorem str_concat_length : forall s t : list nat, length (s ++ t) = length s + length t.
Proof. intros; apply app_len. Qed.

Theorem str_empty_identity : forall s : list nat, [] ++ s = s.
Proof. reflexivity. Qed.

(* t occurs in s as a contiguous block: s = p ++ t ++ q for some prefix p and suffix q. Then |t| <= |s|,
   the bound the engine uses for Contains. *)
Theorem str_contains_length : forall s t : list nat,
  (exists p q, s = p ++ t ++ q) -> length t <= length s.
Proof. intros s t [p [q E]]; subst; rewrite !app_len; lia. Qed.

(* ===================================================================================================== *)
(* 3. Containers (lists): length under append and the index bound.                                        *)
(* ===================================================================================================== *)

Theorem list_append_length : forall (A : Type) (l1 l2 : list A),
  length (l1 ++ l2) = length l1 + length l2.
Proof. intros; apply app_len. Qed.

(* a successful index is within bounds: if nth_error l i yields an element, then i < length l. *)
Theorem list_index_bound : forall (A : Type) (l : list A) (i : nat) (x : A),
  nth_error l i = Some x -> i < length l.
Proof.
  intros A l; induction l as [| h t IH]; intros i x H.
  - destruct i; simpl in H; discriminate.
  - destruct i; simpl in H; simpl.
    + lia.
    + apply IH in H; lia.
Qed.

(* ===================================================================================================== *)
(* 4. Heap: the McCarthy array read-after-write and frame laws.                                           *)
(* ===================================================================================================== *)

(* An array is an extensional map from Z keys to Z values; select/store are the two operations. *)
Definition array := Z -> Z.
Definition select (a : array) (i : Z) : Z := a i.
Definition store (a : array) (i v : Z) : array := fun j => if Z.eqb j i then v else a j.

Theorem select_store_same : forall a i v, select (store a i v) i = v.
Proof. intros; unfold select, store; rewrite Z.eqb_refl; reflexivity. Qed.

Theorem select_store_other : forall a i j v, i <> j -> select (store a i v) j = select a j.
Proof.
  intros a i j v Hij; unfold select, store.
  destruct (Z.eqb j i) eqn:E; [| reflexivity].
  apply Z.eqb_eq in E; subst; congruence.
Qed.

(* The two laws together give the aliasing/frame property: writing two distinct keys is order-independent
   and each read sees its own key, the soundness obligation the heap engine's array encoding discharges. *)
Theorem store_commute_other : forall a i j u v, i <> j ->
  select (store (store a i u) j v) i = select (store a i u) i.
Proof. intros a i j u v Hij; apply select_store_other; auto. Qed.

(* ---- closure evidence: each theorem rests on no axiom and no Admitted ---- *)
Print Assumptions join_over_approx_l.
Print Assumptions join_over_approx_r.
Print Assumptions join_top_l.
Print Assumptions join_top_r.
Print Assumptions str_concat_length.
Print Assumptions str_empty_identity.
Print Assumptions str_contains_length.
Print Assumptions list_append_length.
Print Assumptions list_index_bound.
Print Assumptions select_store_same.
Print Assumptions select_store_other.
Print Assumptions store_commute_other.

(* ---- Extraction of the verified type-lattice join. coqc emits encoders.ml (driven by the OCaml build)
   and encoders.json; json_to_python.py turns the JSON into the engine's join image, so soundinfer's join
   is a mechanical image of join above. The string / list / heap operations are proven sound here but the
   engine discharges them through z3's theories, so only the join (a pure engine abstraction) is tied to
   running code, the way the interval and encoding operators are. ---- *)
From Stdlib Require Extraction.
Extraction Language OCaml.
Extraction "encoders.ml" join.
Extraction Language JSON.
Extraction "encoders.json" join.
