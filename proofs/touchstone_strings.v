(* Trust base, part V: the string-method over-approximation laws (strip / case / count / pad) the engine
   asserts and string_method_axiom_audit checks empirically, proved over an abstract string. Axiom-clean. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.

Definition str := list nat.

(* the relations z3's PrefixOf / SuffixOf / Contains denote over a string. *)
Definition is_prefix (p s : str) : Prop := exists q, s = p ++ q.
Definition is_suffix (r s : str) : Prop := exists p, s = p ++ r.
Definition is_infix  (t s : str) : Prop := exists p q, s = p ++ t ++ q.

(* self-contained helpers (no dependence on Stdlib lemma names, which drift across versions). *)
Lemma app_len : forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2.
Proof. induction l1 as [| h t IH]; simpl; intros; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma repeat_len : forall (x n : nat), length (repeat x n) = n.
Proof. induction n as [| n IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma filter_false : forall (A : Type) (p : A -> bool) (l : list A),
  (forall x, p x = false) -> filter p l = [].
Proof. induction l as [| h t IH]; simpl; intros Hf; [reflexivity | rewrite Hf; apply IH; exact Hf]. Qed.

(* strip / lstrip / rstrip: the result is a contiguous part (suffix / prefix / infix) no longer than s. *)

Theorem lstrip_suffix_length : forall r s : str, is_suffix r s -> length r <= length s.
Proof. intros r s [p E]; subst; rewrite app_len; lia. Qed.

Theorem rstrip_prefix_length : forall p s : str, is_prefix p s -> length p <= length s.
Proof. intros p s [q E]; subst; rewrite app_len; lia. Qed.

Theorem strip_infix_length : forall t s : str, is_infix t s -> length t <= length s.
Proof. intros t s [p [q E]]; subst; rewrite !app_len; lia. Qed.

(* case maps: empty iff s is empty (each code point maps to >= 1 code points, so length is irrelevant). *)

Theorem casemap_empty_iff : forall (f : nat -> str) (s : str),
  (forall c, f c <> []) -> (flat_map f s = [] <-> s = []).
Proof.
  intros f s Hf; split; intro H.
  - destruct s as [| c t]; [reflexivity |].
    simpl in H. destruct (f c) as [| a l] eqn:Ef.
    + exfalso; apply (Hf c); exact Ef.
    + simpl in H; discriminate.
  - subst; reflexivity.
Qed.

(* pad family (ljust / rjust / center / zfill): padding to width w gives length max(len(s), w). *)

Definition pad (fill : nat) (s : str) (w : nat) : str := s ++ repeat fill (w - length s).

Theorem pad_length : forall fill s w, length (pad fill s w) = max (length s) w.
Proof. intros fill s w; unfold pad; rewrite app_len, repeat_len; lia. Qed.

(* count: nonnegative, and zero when sub never occurs (count = number of positions where sub is a prefix). *)

Fixpoint prefixb (p s : str) : bool :=
  match p, s with
  | [], _ => true
  | _ :: _, [] => false
  | a :: p', b :: s' => Nat.eqb a b && prefixb p' s'
  end.

Definition count (sub s : str) : nat :=
  length (filter (fun i => prefixb sub (skipn i s)) (seq 0 (S (length s)))).

Theorem count_nonneg : forall sub s, 0 <= count sub s.
Proof. intros; lia. Qed.

(* prefixb decides is_prefix. *)
Lemma prefixb_true : forall p s, prefixb p s = true <-> is_prefix p s.
Proof.
  induction p as [| a p' IH]; intros s; simpl.
  - split; intro H; [exists s; reflexivity | reflexivity].
  - destruct s as [| b s'].
    + split; intro H; [discriminate | destruct H as [q Hq]; discriminate].
    + rewrite Bool.andb_true_iff. split.
      * intros [Hab Hpre]. apply Nat.eqb_eq in Hab; subst b.
        apply IH in Hpre. destruct Hpre as [q Hq]. exists q; simpl; rewrite Hq; reflexivity.
      * intros [q Hq]. simpl in Hq. injection Hq as Hb Hq'; subst b.
        split; [apply Nat.eqb_refl |]. apply IH. exists q; exact Hq'.
Qed.

(* when sub matches at no position (it is not a contiguous block of any suffix), count is zero. *)
Theorem count_absent_zero : forall sub s,
  (forall i, ~ is_prefix sub (skipn i s)) -> count sub s = 0.
Proof.
  intros sub s Hno. unfold count.
  assert (Hpf : forall i, prefixb sub (skipn i s) = false).
  { intro i. destruct (prefixb sub (skipn i s)) eqn:E; [| reflexivity].
    exfalso; apply (Hno i); apply prefixb_true; exact E. }
  rewrite (filter_false nat (fun i => prefixb sub (skipn i s)) (seq 0 (S (length s))) Hpf).
  reflexivity.
Qed.

(* concat: the length of s + t is the sum of lengths (the engine's len(s + t) == len(s) + len(t) model). *)
Theorem concat_length : forall s t : str, length (s ++ t) = length s + length t.
Proof. intros s t. apply app_len. Qed.

(* slice: s[i:n] is firstn n (skipn i s), no longer than s (the engine's len(s[i:j]) <= len(s) bound). *)
Lemma firstn_length_le : forall (A : Type) (n : nat) (l : list A), length (firstn n l) <= length l.
Proof.
  intros A n l. revert n. induction l as [| h t IH]; intros [| n]; simpl; try lia.
  specialize (IH n). lia.
Qed.

Lemma skipn_length_le : forall (A : Type) (n : nat) (l : list A), length (skipn n l) <= length l.
Proof.
  intros A n l. revert n. induction l as [| h t IH]; intros [| n]; simpl; try lia.
  specialize (IH n). lia.
Qed.

Theorem slice_length : forall i n (s : str), length (firstn n (skipn i s)) <= length s.
Proof.
  intros i n s. apply Nat.le_trans with (length (skipn i s));
  [apply firstn_length_le | apply skipn_length_le].
Qed.

(* split: splitting on a separator yields AT LEAST ONE part -- k separators give k+1 parts -- so result[0]
   never traps (the 1.7.2 bytes-split false-REFUTED fix rests on this). Split concretely so it is a theorem
   about the actual partition, not an assumption. *)
Fixpoint split_on (sep : nat) (s : str) : list str :=
  match s with
  | [] => [[]]
  | c :: rest =>
      if Nat.eqb c sep then [] :: split_on sep rest
      else match split_on sep rest with
           | [] => [[c]]                              (* unreachable: split_on is never empty *)
           | first :: more => (c :: first) :: more
           end
  end.

Theorem split_on_nonempty : forall sep s, split_on sep s <> [].
Proof.
  intros sep s. induction s as [| c rest IH]; simpl; [discriminate |].
  destruct (Nat.eqb c sep); [discriminate |].
  destruct (split_on sep rest); [contradiction | discriminate].
Qed.

Theorem split_on_len_ge_1 : forall sep s, 1 <= length (split_on sep s).
Proof.
  intros sep s. destruct (split_on sep s) eqn:E; [| simpl; lia].
  exfalso. apply (split_on_nonempty sep s). exact E.
Qed.

(* ---- closure evidence: each theorem rests on no axiom and no Admitted ---- *)
Print Assumptions concat_length.
Print Assumptions slice_length.
Print Assumptions split_on_nonempty.
Print Assumptions split_on_len_ge_1.
Print Assumptions lstrip_suffix_length.
Print Assumptions rstrip_prefix_length.
Print Assumptions strip_infix_length.
Print Assumptions casemap_empty_iff.
Print Assumptions pad_length.
Print Assumptions count_nonneg.
Print Assumptions prefixb_true.
Print Assumptions count_absent_zero.
