(* Trust base for touchstone.py: the heap model's MULTI-store semantics, beyond the single-store McCarthy laws
   of touchstone_encoders.v (select_store_same / _other / store_commute_other).

   The value engine threads a SEQUENCE of stores through a backing array -- a list built by append and item
   store, a dict written key by key -- and resolves a read newest-write-wins (core.py's _map_get scans the
   key/value list from the end, last write to a key winning); the heap engine frames a write to one address
   from another. This file models a store sequence as a list of (index, value) writes applied in program order
   and proves: a read after the sequence returns the LAST store to that index, else the initial array
   (newest-wins); a frame -- an index no store touches keeps its initial value across the whole sequence; a
   single store is invisible at every other index; and the sequence COMPOSES (running two store lists in turn
   equals running their concatenation), the heap analogue of the functor's denote_compose across statement
   boundaries. These are the soundness laws the engine's aliasing and dict / list mutation rest on.

   The array / select / store are re-declared verbatim from touchstone_encoders.v so the file is standalone
   like the other companion proofs; it is the same McCarthy array the engine's heap model uses. *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.
Open Scope Z_scope.

Definition array := Z -> Z.
Definition select (a : array) (i : Z) : Z := a i.
Definition store (a : array) (i v : Z) : array := fun j => if Z.eqb j i then v else a j.

(* a store to i is invisible at every other index (the frame for a single write). *)
Theorem store_frame_other : forall a i v j, i <> j -> select (store a i v) j = select a j.
Proof.
  intros a i v j H. unfold select, store.
  destruct (Z.eqb j i) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity].
Qed.

(* apply a list of (index, value) stores left to right -- program order, as the engine threads them. *)
Fixpoint stores (a : array) (ss : list (Z * Z)) : array :=
  match ss with
  | [] => a
  | (i, v) :: rest => stores (store a i v) rest
  end.

(* the most recent store to index j in the list, searched from the END (newest first) -- the dict
   newest-write-wins core.py's _map_get implements. None means j was never stored. *)
Fixpoint last_store (ss : list (Z * Z)) (j : Z) : option Z :=
  match ss with
  | [] => None
  | (i, v) :: rest =>
      match last_store rest j with
      | Some w => Some w                         (* a later store to j wins over this one *)
      | None => if Z.eqb i j then Some v else None
      end
  end.

(* reading after a store sequence: the value of the last store to j, else the initial array at j. *)
Theorem select_stores : forall ss a j,
  select (stores a ss) j = match last_store ss j with Some v => v | None => a j end.
Proof.
  induction ss as [| [i v] rest IH]; intros a j; simpl.
  - reflexivity.
  - rewrite IH. unfold store, select.
    destruct (last_store rest j) eqn:E.
    + reflexivity.
    + rewrite (Z.eqb_sym i j). destruct (Z.eqb j i); reflexivity.
Qed.

(* the frame over a whole sequence: an index no store in the list touches keeps its initial value. *)
Theorem stores_frame : forall ss a j, last_store ss j = None -> select (stores a ss) j = a j.
Proof.
  intros ss a j H. rewrite select_stores, H. reflexivity.
Qed.

(* the store sequence composes: running ss1 then ss2 equals running their concatenation -- the heap analogue
   of the functor's denote_compose, so threading the heap across statement and module boundaries is stable. *)
Theorem stores_app : forall ss1 ss2 a, stores a (ss1 ++ ss2) = stores (stores a ss1) ss2.
Proof.
  induction ss1 as [| [i v] rest IH]; intros ss2 a; simpl.
  - reflexivity.
  - apply IH.
Qed.

(* a corollary tying the two: a read after ss1 ++ ss2 is decided by ss2 first (the newer half), then ss1. *)
Theorem select_stores_app : forall ss1 ss2 a j,
  select (stores a (ss1 ++ ss2)) j
  = match last_store ss2 j with
    | Some v => v
    | None => match last_store ss1 j with Some v => v | None => a j end
    end.
Proof.
  intros ss1 ss2 a j. rewrite stores_app, (select_stores ss2 (stores a ss1) j).
  destruct (last_store ss2 j).
  - reflexivity.
  - apply (select_stores ss1 a j).
Qed.

(* --- Aliasing soundness: the laws behind the value engine's INVALIDATE-ON-STORE (core.py's dirty_attrs and
   the subscript-store parameter forgetting). Two object or container parameters may denote the same address
   (a caller passing f(o, o)); when the analysis cannot decide i = j, a store to i followed by a read of j must
   account for BOTH the aliased value and the framed value. That is exactly why the engine, on a store through
   a possibly-aliased parameter, forgets the stale field and reads a fresh value: these theorems show that is
   sound and complete for the unknown-alias case. *)

(* the aliased read: a store to i IS seen by a read of the same index. A naive "frame everything" that treats
   two distinct-looking references a.x and b.x as independent would wrongly miss this when a is b. *)
Theorem select_store_alias : forall a i v, select (store a i v) i = v.
Proof.
  intros a i v. unfold select, store. rewrite Z.eqb_refl. reflexivity.
Qed.

(* a post-store read is EXACTLY one of two known values -- the stored value (aliased) or the pre-store value
   (framed) -- and nothing else, so ranging over both is a complete account of the unknown-alias case. *)
Theorem select_store_dichotomy : forall a i v j,
  select (store a i v) j = v \/ select (store a i v) j = select a j.
Proof.
  intros a i v j. unfold select, store.
  destruct (Z.eqb j i) eqn:E; [left | right]; reflexivity.
Qed.

(* the invalidate-on-store soundness: a property that holds for BOTH the stored value and the framed
   (pre-store) value holds for the post-store read, whatever the alias relation. So the engine, treating a
   read after a possibly-aliased store as a value that could be either, concludes nothing the real read
   violates -- an unsound PROVED on aliased arguments is impossible. *)
Theorem store_read_sound : forall a i v j (P : Z -> Prop),
  P v -> P (select a j) -> P (select (store a i v) j).
Proof.
  intros a i v j P Hv Ho.
  destruct (select_store_dichotomy a i v j) as [E | E]; rewrite E; assumption.
Qed.

(* the strongest form and the one the engine actually uses: a property holding for EVERY value (a fresh,
   unconstrained read) holds for the post-store read -- an unconditional over-approximation, no alias case
   analysis needed. This is the fresh-value invalidation of dirty_attrs / the forgotten container field. *)
Theorem store_read_fresh_sound : forall a i v j (P : Z -> Prop),
  (forall w, P w) -> P (select (store a i v) j).
Proof.
  intros a i v j P H. apply H.
Qed.

(* generalized to a store SEQUENCE (the engine threads many writes before a read): the read is either some
   value written in the sequence or the initial value -- so a fresh over-approximation covering the writes'
   values and the initial is sound. *)
Theorem stores_read_dichotomy : forall ss a j,
  (exists v, last_store ss j = Some v /\ select (stores a ss) j = v)
  \/ (last_store ss j = None /\ select (stores a ss) j = a j).
Proof.
  intros ss a j. rewrite select_stores. destruct (last_store ss j) eqn:E.
  - left. exists z. split; reflexivity.
  - right. split; reflexivity.
Qed.

(* --- Identity determines aliasing: the `is` memoization (1.49-1.51) keeps `a is b` -- address equality -- a
   single consistent boolean per operand pair, and that boolean decides whether a store through a is visible to
   a read of b. This is precisely why the value engine, when it cannot decide a is b, forgets the field
   (1.47.0 attribute stores, 1.50.0 subscript stores): under aliasing the store IS visible, so a stale read
   would be unsound; and why an `is` precondition is load-bearing -- true there means the addresses are equal. *)
Definition is_ref (a b : Z) : bool := Z.eqb a b.

(* x is x (the 1.49.0 same-term short circuit) and a is b == b is a (the unordered memo key). *)
Theorem is_ref_refl : forall a, is_ref a a = true.
Proof. intro a. apply Z.eqb_refl. Qed.

Theorem is_ref_sym : forall a b, is_ref a b = is_ref b a.
Proof. intros a b. apply Z.eqb_sym. Qed.

(* an `is` precondition binds the operands: is_ref i j = true gives i = j (the 1.51.0 load-bearing property). *)
Theorem is_ref_precond : forall i j, is_ref i j = true -> i = j.
Proof. intros i j H. apply Z.eqb_eq. exact H. Qed.

(* aliased (a is b true): a store through i is seen at j -- the read is the stored value, not a stale one. *)
Theorem is_implies_aliased : forall a i v j, is_ref i j = true -> select (store a i v) j = v.
Proof. intros a i v j H. apply Z.eqb_eq in H. subst. apply select_store_alias. Qed.

(* not aliased (a is b false): the store is framed, so the read keeps its pre-store value. Together with
   is_implies_aliased this is the full case split the engine over-approximates when identity is unknown. *)
Theorem not_alias_frames : forall a i v j, is_ref i j = false -> select (store a i v) j = select a j.
Proof.
  intros a i v j H. apply store_frame_other. intro E. subst j.
  rewrite Z.eqb_refl in H. discriminate.
Qed.

(* No axioms: the multi-store heap laws hold in the kernel's own logic. *)
Print Assumptions store_frame_other.
Print Assumptions select_stores.
Print Assumptions stores_frame.
Print Assumptions stores_app.
Print Assumptions select_stores_app.
Print Assumptions select_store_alias.
Print Assumptions select_store_dichotomy.
Print Assumptions store_read_sound.
Print Assumptions store_read_fresh_sound.
Print Assumptions stores_read_dichotomy.
Print Assumptions is_ref_refl.
Print Assumptions is_ref_sym.
Print Assumptions is_ref_precond.
Print Assumptions is_implies_aliased.
Print Assumptions not_alias_frames.
