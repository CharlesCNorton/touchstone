(* Trust base for touchstone.py: the PARTIAL-CORRECTNESS claim the prove engine discharges, and the role of
   the DIVERGING paths -- an assert failure or an intentional raise -- added in the 1.51-1.52 diverge mechanism
   (engines.py's ctx.diverge, gating the postcondition obligation in _prove_core and _prove_via_havoc).

   The engine forms  claim_false = pre AND (trap OR (NOT diverge AND NOT post))  over the symbolic input and
   reports PROVED exactly when claim_false is UNSATISFIABLE. This file abstracts each per-input condition to a
   predicate over an arbitrary input type and proves that an unsatisfiable claim_false delivers partial
   correctness: for every input meeting the precondition the function hits no (bug) trap, and it either
   DIVERGES -- raises AssertionError from a failed assert, or an intentional raise, neither of which returns a
   value, so no postcondition is owed -- or its postcondition holds at the returned value. It also proves the
   claim is COMPLETE (any real violation makes claim_false hold, so the engine never wrongly PROVES) and gives
   the decidable form recovering the disjunction (diverge \/ post) from the constructive double negation.

   SOUNDNESS ASSUMPTION (discharged by the engine, not here): `diverge x` holds only when the function truly
   returns no value on x. The engine's diverge conditions are exactly the assert-negations and the raise path
   conditions -- the inputs on which control leaves via an exception rather than a return -- so this holds by
   construction. Marking a RETURNING path as diverging would be unsound; the engine never does. *)

From Stdlib Require Import ZArith.

Section PartialCorrectness.
Variable Inp : Type.
Variable pre trap diverge post : Inp -> Prop.

(* the engine's claim_false: some input under the precondition either hits a bug trap, or on a NON-diverging
   path returns a value the postcondition rejects. PROVED is reported iff this is unsatisfiable. *)
Definition claim_false : Prop := exists x, pre x /\ (trap x \/ (~ diverge x /\ ~ post x)).

(* soundness (constructive): an unsatisfiable claim_false rules out, for every pre-input, a bug trap and a
   non-diverging postcondition violation. *)
Theorem prove_sound :
  ~ claim_false -> forall x, pre x -> ~ trap x /\ ~ (~ diverge x /\ ~ post x).
Proof.
  unfold claim_false. intros H x Hpre. split.
  - intro Ht. apply H. exists x. split; [ exact Hpre | left; exact Ht ].
  - intro Hbad. apply H. exists x. split; [ exact Hpre | right; exact Hbad ].
Qed.

(* the same with deciders for diverge and post (the engine's conditions are z3 booleans, hence decidable):
   this recovers the intended disjunction -- every pre-input either diverges or satisfies the postcondition,
   and never traps. *)
Theorem prove_sound_dec :
  (forall x, {diverge x} + {~ diverge x}) -> (forall x, {post x} + {~ post x}) ->
  ~ claim_false -> forall x, pre x -> ~ trap x /\ (diverge x \/ post x).
Proof.
  intros Ddiv Dpost H x Hpre.
  destruct (prove_sound H x Hpre) as [ Hnt Hnn ]. split; [ exact Hnt | ].
  destruct (Ddiv x) as [ Hd | Hd ]; [ left; exact Hd | ].
  destruct (Dpost x) as [ Hp | Hp ]; [ right; exact Hp | ].
  exfalso. apply Hnn. split; assumption.
Qed.

(* completeness: any real bug trap, or a non-diverging postcondition violation, makes claim_false hold, so the
   engine cannot report PROVED in its presence. The claim is not too weak. *)
Theorem prove_complete :
  forall x, pre x -> (trap x \/ (~ diverge x /\ ~ post x)) -> claim_false.
Proof. intros x Hpre Hbad. exists x. split; assumption. Qed.

(* a diverging input owes no postcondition: if the function diverges on x, the obligation clause is vacuous,
   whatever value the (unreturned) result would carry. This is exactly why an assert failure or a raise is
   never counted as a postcondition violation. *)
Theorem diverge_no_obligation : forall x, diverge x -> ~ (~ diverge x /\ ~ post x).
Proof. intros x Hd [ Hnd _ ]. exact (Hnd Hd). Qed.

(* trap freedom is independent of the postcondition: a bug trap under the precondition is a violation whatever
   post or diverge say, which is why claim_false keeps `trap` as a top-level disjunct. A raise is a diverge; a
   division by zero is a trap -- the two are handled on different branches. *)
Theorem trap_is_violation : forall x, pre x -> trap x -> claim_false.
Proof. intros x Hpre Ht. exists x. split; [ exact Hpre | left; exact Ht ]. Qed.

End PartialCorrectness.

(* --- try / except: an execution outcome and the catch semantics. This is the soundness behind check's
   already-sound try handling, and the proven-correct MODEL a future prove-side recovery should follow (the
   engine currently havocs a try/except, so a recovering `try: 10 // x except ZeroDivisionError: return 0` is
   sound but UNKNOWN). A Python trap is a catchable exception (Raised), matched to a handler by its type. *)

Inductive outcome (V : Type) := Ret (v : V) | Raised (exc : Z).
Arguments Ret {V} _.
Arguments Raised {V} _.

(* run body; an except that names `exc` turns a matching Raised into the handler's outcome, rethrows others. *)
Definition catch {V} (exc : Z) (handler body : outcome V) : outcome V :=
  match body with
  | Ret v => Ret v
  | Raised e => if Z.eqb e exc then handler else Raised e
  end.

(* a matching exception is caught -> the handler's outcome (try: raise exc; except exc: h  ==  h). *)
Theorem catch_matched : forall V exc (h : outcome V), catch exc h (Raised exc) = h.
Proof. intros V exc h. simpl. rewrite Z.eqb_refl. reflexivity. Qed.

(* a non-matching exception propagates unchanged (the handler does not fire). *)
Theorem catch_unmatched : forall V e exc (h : outcome V),
  e <> exc -> catch exc h (Raised e) = Raised e.
Proof.
  intros V e exc h H. simpl.
  destruct (Z.eqb e exc) eqn:E; [ apply Z.eqb_eq in E; contradiction | reflexivity ].
Qed.

(* a returning body ignores the handler (try: return v; except: h  ==  return v). *)
Theorem catch_returns : forall V (v : V) exc (h : outcome V), catch exc h (Ret v) = Ret v.
Proof. reflexivity. Qed.

(* the soundness a prove-side recovery would rest on: the try/except returns only a value the BODY or the
   HANDLER returns, so a postcondition holding for both holds for the whole construct. A caught div-by-zero
   the handler turns into `return 0` contributes 0, not a trap violation. *)
Theorem catch_sound : forall V (P : V -> Prop) exc h b,
  (forall v, b = Ret v -> P v) -> (forall v, h = Ret v -> P v) ->
  forall v, catch exc h b = Ret v -> P v.
Proof.
  intros V P exc h b Hb Hh v Hc. unfold catch in Hc. destruct b as [ vb | e ].
  - injection Hc; intro E; subst; apply Hb; reflexivity.
  - destruct (Z.eqb e exc); [ apply Hh; exact Hc | discriminate Hc ].
Qed.

(* No axioms: the partial-correctness claim decomposition holds in the kernel's own (constructive) logic. *)
Print Assumptions catch_matched.
Print Assumptions catch_unmatched.
Print Assumptions catch_returns.
Print Assumptions catch_sound.
Print Assumptions prove_sound.
Print Assumptions prove_sound_dec.
Print Assumptions prove_complete.
Print Assumptions diverge_no_obligation.
Print Assumptions trap_is_violation.
