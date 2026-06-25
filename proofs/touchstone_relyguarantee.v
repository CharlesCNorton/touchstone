(* Trust base for touchstone, part V: soundness of the rely-guarantee concurrency engine, machine-checked.

   theories.verify_rely_guarantee establishes a concurrency property for EVERY schedule and EVERY depth,
   not by enumerating interleavings but by a rely-guarantee argument over a global invariant. It discharges
   exactly three obligations with z3:

     (1) init(s)  -> inv(s)                         the invariant holds in every initial state
     (2) inv(s) /\ step(s,s') -> inv(s')            for each thread's atomic guarantee `step`
                                                    (stability under the rely = the others' guarantees)
     (3) inv(s)   -> post(s)                        the invariant implies the property

   The claim it then makes is that a global invariant which holds initially and is preserved by every
   thread's step holds in every state reachable under ANY interleaving, so the property holds for all
   schedules and all depths. This file proves that claim: with (1) and (2), inv holds at every reachable
   state (reachability being any finite sequence of any thread's atomic step, i.e. every interleaving at
   every depth); with (3) the property holds there too. Closed under the global context (no axioms, no
   Admitted). *)

From Stdlib Require Import List.
Import ListNotations.

Section RelyGuarantee.

  Variable State : Type.
  Variable init : State -> Prop.
  Variable inv : State -> Prop.
  (* the per-thread atomic guarantee relations; the rely seen by any thread is the union of the others. *)
  Variable steps : list (State -> State -> Prop).

  (* Reachability under any interleaving at any depth: an initial state is reachable, and any thread's
     atomic step from a reachable state reaches the next. A reachable state is precisely a state at the end
     of some finite schedule, so quantifying over reachable s quantifies over all schedules and all depths. *)
  Inductive reachable : State -> Prop :=
  | reach_init : forall s, init s -> reachable s
  | reach_step : forall s s' R, reachable s -> In R steps -> R s s' -> reachable s'.

  (* The two obligations verify_rely_guarantee discharges before reporting PROVED. *)
  Hypothesis init_establishes_inv : forall s, init s -> inv s.
  Hypothesis inv_stable : forall R, In R steps -> forall s s', inv s -> R s s' -> inv s'.

  (* Soundness of the argument: the invariant holds at every reachable state -- every interleaving, every
     depth -- which is what makes the bounded-interleaving search unnecessary. *)
  Theorem rg_invariant : forall s, reachable s -> inv s.
  Proof.
    intros s H; induction H as [s Hi | s s' R Hr IH Hin Hstep].
    - apply init_establishes_inv; exact Hi.
    - exact (inv_stable R Hin s s' IH Hstep).
  Qed.

  (* The property the invariant implies then holds at every reachable state too. *)
  Variable post : State -> Prop.
  Hypothesis inv_implies_post : forall s, inv s -> post s.

  Theorem rg_post : forall s, reachable s -> post s.
  Proof. intros s H; apply inv_implies_post, rg_invariant, H. Qed.

End RelyGuarantee.

(* closure evidence: the soundness theorems rest on no axiom and no Admitted; the section hypotheses are
   discharged as premises of the closed theorems (exactly the obligations the engine checks). *)
Print Assumptions rg_invariant.
Print Assumptions rg_post.
