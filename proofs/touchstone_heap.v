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

(* No axioms: the multi-store heap laws hold in the kernel's own logic. *)
Print Assumptions store_frame_other.
Print Assumptions select_stores.
Print Assumptions stores_frame.
Print Assumptions stores_app.
Print Assumptions select_stores_app.
