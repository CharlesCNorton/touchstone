(* Trust base for touchstone.py, part II: the translation is a semantics-preserving functor.

   touchstone.py translates a program (a sequence of statements) into a semantic object (a
   state transformer over the store). For this translation to "compose cleanly across
   modules" it must be a functor from the category of programs (objects = states, morphisms
   = programs, composition = sequencing, identity = the empty program) to the category of
   state transformers (composition = function composition, identity = id).

   The modeled IR here covers arithmetic assignment AND conditional control flow, so the
   functor laws are proved across branching, not only straight-line code. Beyond the functor
   laws we give an independent big-step operational semantics and prove the denotation sound
   and complete with respect to it: the compositional translation computes exactly the
   operational result. That is the semantics-preservation content -- the engine's denotation
   is the operational semantics, over control flow. *)

From Stdlib Require Import ZArith Lia List.
Import ListNotations.
Open Scope Z_scope.

Definition var := nat.
Definition state := var -> Z.
Definition upd (s : state) (x : var) (v : Z) : state :=
  fun y => if Nat.eqb x y then v else s y.

Inductive expr :=
| EVar (x : var) | EConst (z : Z)
| EAdd (a b : expr) | ESub (a b : expr) | EMul (a b : expr)
| EDiv (a b : expr)        (* floor division, matching touchstone.py's modeled // *)
| EMod (a b : expr)        (* floored modulo, matching touchstone.py's modeled % *)
| ELt (a b : expr) | ELe (a b : expr) | EEq (a b : expr)   (* comparisons, 0/1-valued as in Python *)
| ENot (a : expr) | EAnd (a b : expr) | EOr (a b : expr).  (* boolean connectives on truthiness *)

Fixpoint eval (s : state) (e : expr) : Z :=
  match e with
  | EVar x => s x
  | EConst z => z
  | EAdd a b => eval s a + eval s b
  | ESub a b => eval s a - eval s b
  | EMul a b => eval s a * eval s b
  | EDiv a b => eval s a / eval s b      (* Coq's Z.div is floor division = Python's // *)
  | EMod a b => Z.modulo (eval s a) (eval s b)   (* Coq's Z.modulo is floored = Python's % *)
  | ELt a b => if Z.ltb (eval s a) (eval s b) then 1 else 0
  | ELe a b => if Z.leb (eval s a) (eval s b) then 1 else 0
  | EEq a b => if Z.eqb (eval s a) (eval s b) then 1 else 0
  | ENot a => if Z.eqb (eval s a) 0 then 1 else 0
  | EAnd a b => if andb (negb (Z.eqb (eval s a) 0)) (negb (Z.eqb (eval s b) 0)) then 1 else 0
  | EOr a b => if orb (negb (Z.eqb (eval s a) 0)) (negb (Z.eqb (eval s b) 0)) then 1 else 0
  end.

(* A program is a sequence of statements with conditional control flow. The branches and the
   continuation are direct sub-programs, so the denotation recurses on structural subterms. *)
Inductive prog :=
| PNil
| PAsgn (x : var) (e : expr) (rest : prog)
| PCond (c : expr) (thn els rest : prog).   (* if c <> 0 then thn else els; then rest *)

(* The engine's compositional denotation: a program is a state transformer. *)
Fixpoint denote (p : prog) (s : state) : state :=
  match p with
  | PNil => s
  | PAsgn x e rest => denote rest (upd s x (eval s e))
  | PCond c thn els rest =>
      denote rest (if Z.eqb (eval s c) 0 then denote els s else denote thn s)
  end.

(* Sequencing two programs: append q after p (p's terminal PNil becomes q). This is the
   composition of morphisms in the category of programs. *)
Fixpoint seq (p q : prog) : prog :=
  match p with
  | PNil => q
  | PAsgn x e rest => PAsgn x e (seq rest q)
  | PCond c thn els rest => PCond c thn els (seq rest q)
  end.

(* Functor law 1: the identity morphism (empty program) maps to the identity transformer. *)
Theorem denote_id : forall s, denote PNil s = s.
Proof. reflexivity. Qed.

(* Functor law 2: composition of morphisms (sequencing) maps to composition of transformers.
   Running p then q equals running their sequence -- stable across statement and module
   boundaries, and across the conditional in the head of p. *)
Theorem denote_compose : forall p q s, denote (seq p q) s = denote q (denote p s).
Proof.
  induction p as [| x e rest IHrest | c thn IHthn els IHels rest IHrest];
    intros q s; simpl.
  - reflexivity.
  - now rewrite IHrest.
  - now rewrite IHrest.
Qed.

(* Associativity of program composition (sanity of the category). *)
Theorem seq_assoc : forall p q r, seq (seq p q) r = seq p (seq q r).
Proof.
  induction p as [| x e rest IHrest | c thn IHthn els IHels rest IHrest]; intros q r; simpl.
  - reflexivity.
  - now rewrite IHrest.
  - now rewrite IHrest.
Qed.

Theorem denote_assoc :
  forall p q r s, denote (seq (seq p q) r) s = denote (seq p (seq q r)) s.
Proof. intros p q r s. now rewrite seq_assoc. Qed.

(* An independent big-step operational semantics for the same IR. *)
Inductive bigstep : prog -> state -> state -> Prop :=
| BS_nil  : forall s, bigstep PNil s s
| BS_asgn : forall x e rest s s',
    bigstep rest (upd s x (eval s e)) s' -> bigstep (PAsgn x e rest) s s'
| BS_cond_t : forall c thn els rest s st s',
    eval s c <> 0 -> bigstep thn s st -> bigstep rest st s' ->
    bigstep (PCond c thn els rest) s s'
| BS_cond_f : forall c thn els rest s se s',
    eval s c = 0 -> bigstep els s se -> bigstep rest se s' ->
    bigstep (PCond c thn els rest) s s'.

(* Semantic preservation, soundness: the denotation realizes the operational semantics. *)
Theorem denote_sound : forall p s, bigstep p s (denote p s).
Proof.
  induction p as [| x e rest IHrest | c thn IHthn els IHels rest IHrest]; intros s; simpl.
  - apply BS_nil.
  - apply BS_asgn. apply IHrest.
  - destruct (Z.eqb (eval s c) 0) eqn:Hc.
    + apply Z.eqb_eq in Hc. eapply BS_cond_f; [exact Hc | apply IHels | apply IHrest].
    + apply Z.eqb_neq in Hc. eapply BS_cond_t; [exact Hc | apply IHthn | apply IHrest].
Qed.

(* Semantic preservation, completeness (and determinism): the operational semantics has
   exactly the denotation as its result. *)
Theorem denote_complete : forall p s s', bigstep p s s' -> denote p s = s'.
Proof.
  intros p s s' H. induction H; simpl.
  - reflexivity.
  - exact IHbigstep.
  - apply Z.eqb_neq in H. rewrite H. rewrite IHbigstep1. exact IHbigstep2.
  - apply Z.eqb_eq in H. rewrite H. rewrite IHbigstep1. exact IHbigstep2.
Qed.

(* The denotation is exactly the operational semantics. *)
Theorem denote_iff_bigstep : forall p s s', denote p s = s' <-> bigstep p s s'.
Proof.
  intros p s s'. split; intro H.
  - subst s'. apply denote_sound.
  - apply denote_complete. exact H.
Qed.

(* The verification-condition generator: a weakest-precondition over the IR, propagating a
   postcondition backward through assignments and both arms of a conditional. This is the shape
   the engine's symbolic executor produces -- a first-order condition on the entry state. *)
Fixpoint wp (p : prog) (Q : state -> Prop) (s : state) : Prop :=
  match p with
  | PNil => Q s
  | PAsgn x e rest => wp rest Q (upd s x (eval s e))
  | PCond c thn els rest =>
      (eval s c <> 0 -> wp thn (wp rest Q) s) /\
      (eval s c =  0 -> wp els (wp rest Q) s)
  end.

(* VC soundness: if the generated condition holds at the entry state, the postcondition holds of
   the executed result. A discharged VC therefore guarantees the property under the operational
   semantics (denote = bigstep), so no faithful VC can manufacture a false PROVED. *)
Theorem wp_sound : forall p Q s, wp p Q s -> Q (denote p s).
Proof.
  induction p as [| x e rest IHrest | c thn IHthn els IHels rest IHrest];
    intros Q s H; simpl in *.
  - exact H.
  - apply IHrest. exact H.
  - destruct (Z.eqb (eval s c) 0) eqn:Hc.
    + apply Z.eqb_eq in Hc. destruct H as [_ H2]. specialize (H2 Hc).
      apply IHrest. apply IHels. exact H2.
    + apply Z.eqb_neq in Hc. destruct H as [H1 _]. specialize (H1 Hc).
      apply IHrest. apply IHthn. exact H1.
Qed.

(* VC completeness: the generated condition is the weakest such precondition, so it is exactly the
   set of entry states from which the postcondition is reached. The VC is neither too strong nor
   too weak -- it is faithful to the semantics. *)
Theorem wp_complete : forall p Q s, Q (denote p s) -> wp p Q s.
Proof.
  induction p as [| x e rest IHrest | c thn IHthn els IHels rest IHrest];
    intros Q s H; simpl in *.
  - exact H.
  - apply IHrest. exact H.
  - destruct (Z.eqb (eval s c) 0) eqn:Hc; split; intro Hcc.
    + apply Z.eqb_eq in Hc. rewrite Hc in Hcc. exfalso. apply Hcc. reflexivity.
    + apply IHels. apply IHrest. exact H.
    + apply IHthn. apply IHrest. exact H.
    + apply Z.eqb_neq in Hc. rewrite Hcc in Hc. exfalso. apply Hc. reflexivity.
Qed.

Theorem wp_iff : forall p Q s, wp p Q s <-> Q (denote p s).
Proof. intros p Q s. split; [apply wp_sound | apply wp_complete]. Qed.

(* End-to-end soundness for the modeled subset: a discharged verification condition implies the
   property holds of every operational result. Read as the verifier's contract: when the engine
   discharges the VC (wp p Q from the entry state), then for the state s' the program actually
   reaches under the operational semantics (bigstep), the postcondition Q holds. PROVED therefore
   implies the property under the program's semantics -- the pipeline is sound, not merely trusted,
   over this subset. *)
Theorem vc_sound_operational :
  forall p (Q : state -> Prop) s s', wp p Q s -> bigstep p s s' -> Q s'.
Proof.
  intros p Q s s' Hwp Hbs.
  apply denote_complete in Hbs.        (* bigstep p s s' -> denote p s = s' *)
  rewrite <- Hbs.                       (* goal: Q (denote p s) *)
  apply wp_sound. exact Hwp.
Qed.

(* The same end to end against a hypothetical solver: if the solver reports the VC valid (models it
   as a true proposition VC, with VC -> wp p Q s the faithful reading of "the emitted condition
   holds"), the property holds operationally. This is the shape the full pipeline theorem takes once
   the solver result is itself certificate-checked. *)
Theorem pipeline_sound :
  forall p (Q : state -> Prop) (VC : Prop) s s',
    (VC -> wp p Q s) -> VC -> bigstep p s s' -> Q s'.
Proof.
  intros p Q VC s s' Hfaithful Hvc Hbs.
  apply (vc_sound_operational p Q s s'); [ apply Hfaithful; exact Hvc | exact Hbs ].
Qed.

(* Traps. The engine treats a division by a possibly-zero divisor as a trap that refutes a totality
   claim, emitting at each division a divisor-nonzero obligation. The definedness predicates below say
   an expression / program runs without dividing by zero, and the trap-aware weakest precondition wpsafe
   carries those obligations alongside the postcondition. wpsafe_sound proves a discharged trap-aware VC
   implies BOTH freedom from division by zero and the postcondition -- the engine's trap obligations are
   sound, so a PROVED totality claim really is trap-free over this fragment. *)
Fixpoint edefined (s : state) (e : expr) : Prop :=
  match e with
  | EVar _ | EConst _ => True
  | EAdd a b | ESub a b | EMul a b
  | ELt a b | ELe a b | EEq a b | EAnd a b | EOr a b => edefined s a /\ edefined s b
  | ENot a => edefined s a
  | EDiv a b | EMod a b => edefined s a /\ edefined s b /\ eval s b <> 0
  end.

Fixpoint pdefined (p : prog) (s : state) : Prop :=
  match p with
  | PNil => True
  | PAsgn x e rest => edefined s e /\ pdefined rest (upd s x (eval s e))
  | PCond c thn els rest =>
      edefined s c
      /\ (eval s c =  0 -> pdefined els s /\ pdefined rest (denote els s))
      /\ (eval s c <> 0 -> pdefined thn s /\ pdefined rest (denote thn s))
  end.

Fixpoint wpsafe (p : prog) (Q : state -> Prop) (s : state) : Prop :=
  match p with
  | PNil => Q s
  | PAsgn x e rest => edefined s e /\ wpsafe rest Q (upd s x (eval s e))
  | PCond c thn els rest =>
      edefined s c
      /\ (eval s c <> 0 -> wpsafe thn (wpsafe rest Q) s)
      /\ (eval s c =  0 -> wpsafe els (wpsafe rest Q) s)
  end.

Theorem wpsafe_sound : forall p Q s, wpsafe p Q s -> pdefined p s /\ Q (denote p s).
Proof.
  induction p as [| x e rest IHrest | c thn IHthn els IHels rest IHrest]; intros Q s H; simpl in *.
  - split; [exact I | exact H].
  - destruct H as [He Hrest]. destruct (IHrest Q _ Hrest) as [Hd HQ].
    split; [split; [exact He | exact Hd] | exact HQ].
  - destruct H as [Hc [Ht Hf]]. destruct (Z.eqb (eval s c) 0) eqn:Hb.
    + apply Z.eqb_eq in Hb. specialize (Hf Hb).
      destruct (IHels (wpsafe rest Q) s Hf) as [HdE HrE].
      destruct (IHrest Q _ HrE) as [HdR HQ].
      split; [ split; [exact Hc | split; intro Hk] | exact HQ ].
      * split; [exact HdE | exact HdR].
      * exfalso. rewrite Hb in Hk. apply Hk. reflexivity.
    + apply Z.eqb_neq in Hb. specialize (Ht Hb).
      destruct (IHthn (wpsafe rest Q) s Ht) as [HdT HrT].
      destruct (IHrest Q _ HrT) as [HdR HQ].
      split; [ split; [exact Hc | split; intro Hk] | exact HQ ].
      * exfalso. apply Hb. exact Hk.
      * split; [exact HdT | exact HdR].
Qed.

(* The verification-condition generator as extractable data. The wp above is a Coq Prop; for the
   running engine to emit its goals THROUGH the verified generator, the generator must produce a
   piece of first-order data the engine can compute, serialize, and hand to a solver. form is that
   data (a first-order formula over the IR), and wpg is the weakest precondition as a form. It is
   trap-aware: at each division it emits the divisor-nonzero obligation (defined_expr), so a
   discharged VC certifies both freedom from division by zero and the postcondition. wpg is extracted
   to OCaml (vcgen.ml, below) and mirrored in the Python engine, which a differential audit holds
   equal to this extraction -- so the generator that runs is the one proven sound and complete here. *)
Inductive form :=
| FTrue | FFalse
| FLt (a b : expr) | FLe (a b : expr) | FEq (a b : expr)
| FNot (f : form) | FAnd (f g : form) | FOr (f g : form) | FImpl (f g : form).

Fixpoint eval_form (s : state) (f : form) : Prop :=
  match f with
  | FTrue => True | FFalse => False
  | FLt a b => eval s a < eval s b
  | FLe a b => eval s a <= eval s b
  | FEq a b => eval s a = eval s b
  | FNot g => ~ eval_form s g
  | FAnd g h => eval_form s g /\ eval_form s h
  | FOr g h => eval_form s g \/ eval_form s h
  | FImpl g h => eval_form s g -> eval_form s h
  end.

Fixpoint subst_expr (x : var) (e t : expr) : expr :=
  match t with
  | EVar y => if Nat.eqb x y then e else EVar y
  | EConst z => EConst z
  | EAdd a b => EAdd (subst_expr x e a) (subst_expr x e b)
  | ESub a b => ESub (subst_expr x e a) (subst_expr x e b)
  | EMul a b => EMul (subst_expr x e a) (subst_expr x e b)
  | EDiv a b => EDiv (subst_expr x e a) (subst_expr x e b)
  | EMod a b => EMod (subst_expr x e a) (subst_expr x e b)
  | ELt a b => ELt (subst_expr x e a) (subst_expr x e b)
  | ELe a b => ELe (subst_expr x e a) (subst_expr x e b)
  | EEq a b => EEq (subst_expr x e a) (subst_expr x e b)
  | ENot a => ENot (subst_expr x e a)
  | EAnd a b => EAnd (subst_expr x e a) (subst_expr x e b)
  | EOr a b => EOr (subst_expr x e a) (subst_expr x e b)
  end.

Fixpoint subst_form (x : var) (e : expr) (f : form) : form :=
  match f with
  | FTrue => FTrue | FFalse => FFalse
  | FLt a b => FLt (subst_expr x e a) (subst_expr x e b)
  | FLe a b => FLe (subst_expr x e a) (subst_expr x e b)
  | FEq a b => FEq (subst_expr x e a) (subst_expr x e b)
  | FNot g => FNot (subst_form x e g)
  | FAnd g h => FAnd (subst_form x e g) (subst_form x e h)
  | FOr g h => FOr (subst_form x e g) (subst_form x e h)
  | FImpl g h => FImpl (subst_form x e g) (subst_form x e h)
  end.

(* the divisor-nonzero obligations of an expression, as a formula *)
Fixpoint defined_expr (t : expr) : form :=
  match t with
  | EVar _ | EConst _ => FTrue
  | EAdd a b | ESub a b | EMul a b
  | ELt a b | ELe a b | EEq a b | EAnd a b | EOr a b => FAnd (defined_expr a) (defined_expr b)
  | ENot a => defined_expr a
  | EDiv a b | EMod a b => FAnd (defined_expr a) (FAnd (defined_expr b) (FNot (FEq b (EConst 0))))
  end.

Fixpoint wpg (p : prog) (Q : form) : form :=
  match p with
  | PNil => Q
  | PAsgn x e rest => FAnd (defined_expr e) (subst_form x e (wpg rest Q))
  | PCond c thn els rest =>
      FAnd (defined_expr c)
        (FAnd (FImpl (FNot (FEq c (EConst 0))) (wpg thn (wpg rest Q)))
              (FImpl (FEq c (EConst 0)) (wpg els (wpg rest Q))))
  end.

Lemma subst_expr_eval : forall x e t s, eval s (subst_expr x e t) = eval (upd s x (eval s e)) t.
Proof.
  intros x e t s. induction t; simpl;
    try (rewrite IHt1, IHt2; reflexivity); try (rewrite IHt; reflexivity).
  - unfold upd. destruct (Nat.eqb x x0); reflexivity.
  - reflexivity.
Qed.

Lemma subst_form_eval : forall f x e s, eval_form s (subst_form x e f) <-> eval_form (upd s x (eval s e)) f.
Proof.
  induction f; intros x e s; simpl; repeat rewrite subst_expr_eval; try tauto.
  - rewrite IHf; tauto.
  - rewrite IHf1, IHf2; tauto.
  - rewrite IHf1, IHf2; tauto.
  - rewrite IHf1, IHf2; tauto.
Qed.

Lemma defined_expr_eval : forall t s, eval_form s (defined_expr t) <-> edefined s t.
Proof.
  induction t; intros s; simpl;
    try tauto; try (rewrite IHt1, IHt2; tauto); try (rewrite IHt; tauto).
Qed.

(* Soundness: a discharged generated VC certifies both freedom from division by zero and the
   postcondition, under the operational semantics. A PROVED emitted through wpg is a real guarantee. *)
Theorem wpg_sound : forall p Q s, eval_form s (wpg p Q) -> pdefined p s /\ eval_form (denote p s) Q.
Proof.
  intros p. induction p as [| x e rest IHrest | c thn IHthn els IHels rest IHrest];
    intros Q s H; simpl in *.
  - split; [exact I | exact H].
  - destruct H as [Hd Hr]. apply defined_expr_eval in Hd.
    rewrite subst_form_eval in Hr. destruct (IHrest Q _ Hr) as [Hpd HQ].
    split; [split; [exact Hd | exact Hpd] | exact HQ].
  - destruct H as [Hc [Hnz Hz]]. apply defined_expr_eval in Hc.
    destruct (Z.eqb (eval s c) 0) eqn:Hb.
    + apply Z.eqb_eq in Hb. specialize (Hz Hb).
      destruct (IHels (wpg rest Q) s Hz) as [HpE HrE].
      destruct (IHrest Q _ HrE) as [HpR HQ].
      split; [ split; [exact Hc | split; intro Hk] | exact HQ ].
      * split; [exact HpE | exact HpR].
      * exfalso. apply Hk. exact Hb.
    + apply Z.eqb_neq in Hb. specialize (Hnz Hb).
      destruct (IHthn (wpg rest Q) s Hnz) as [HpT HrT].
      destruct (IHrest Q _ HrT) as [HpR HQ].
      split; [ split; [exact Hc | split; intro Hk] | exact HQ ].
      * exfalso. apply Hb. exact Hk.
      * split; [exact HpT | exact HpR].
Qed.

(* Completeness: the generated VC is the weakest precondition ensuring no trap and Q, so it holds at
   exactly the trap-free entry states from which Q is reached. The generator loses no precision. *)
Theorem wpg_complete : forall p Q s, pdefined p s -> eval_form (denote p s) Q -> eval_form s (wpg p Q).
Proof.
  intros p. induction p as [| x e rest IHrest | c thn IHthn els IHels rest IHrest];
    intros Q s Hpd HQ; simpl in *.
  - exact HQ.
  - destruct Hpd as [Hd Hpr]. split.
    + apply defined_expr_eval. exact Hd.
    + rewrite subst_form_eval. apply IHrest; [exact Hpr | exact HQ].
  - destruct Hpd as [Hc [Hz Hnz]]. split.
    + apply defined_expr_eval. exact Hc.
    + destruct (Z.eqb (eval s c) 0) eqn:Hb.
      * apply Z.eqb_eq in Hb. destruct (Hz Hb) as [HpE HpR]. split; intro Hk.
        -- exfalso. apply Hk. exact Hb.
        -- apply IHels; [exact HpE | apply IHrest; [exact HpR | exact HQ]].
      * apply Z.eqb_neq in Hb. destruct (Hnz Hb) as [HpT HpR]. split; intro Hk.
        -- apply IHthn; [exact HpT | apply IHrest; [exact HpR | exact HQ]].
        -- exfalso. apply Hb. exact Hk.
Qed.

(* Loops. The fragment above links denotation, big-step semantics, and the weakest precondition for
   straight-line code and conditionals. The engine also reasons about unbounded loops, discharging
   each by an annotated invariant -- initiation, preservation under the body, the postcondition on
   exit -- which is verify_chc / verify_deductive's verification condition. The command language
   below adds CWhile carrying that invariant, an operational semantics (ceval, relating terminating
   runs), and a weakest precondition wpc whose CWhile case is that three-part condition. wpc_sound
   proves it sound against the semantics: a discharged loop VC implies the postcondition of every run
   that reaches exit, extending the machine-checked guarantee from straight-line code to loops
   (partial correctness; termination is the ranking-function argument in touchstone_domains.v). *)
Inductive cmd :=
| CSkip
| CAsgn (x : var) (e : expr)
| CSeq (a b : cmd)
| CIf (c : expr) (t e : cmd)
| CWhile (Inv : state -> Prop) (c : expr) (body : cmd).

Inductive ceval : cmd -> state -> state -> Prop :=
| E_Skip : forall s, ceval CSkip s s
| E_Asgn : forall s x e, ceval (CAsgn x e) s (upd s x (eval s e))
| E_Seq : forall a b s s' s'', ceval a s s' -> ceval b s' s'' -> ceval (CSeq a b) s s''
| E_IfT : forall c t e s s', eval s c <> 0 -> ceval t s s' -> ceval (CIf c t e) s s'
| E_IfF : forall c t e s s', eval s c = 0 -> ceval e s s' -> ceval (CIf c t e) s s'
| E_WhileF : forall Inv c body s, eval s c = 0 -> ceval (CWhile Inv c body) s s
| E_WhileT : forall Inv c body s s' s'', eval s c <> 0 -> ceval body s s' ->
    ceval (CWhile Inv c body) s' s'' -> ceval (CWhile Inv c body) s s''.

Fixpoint wpc (k : cmd) (Q : state -> Prop) (s : state) : Prop :=
  match k with
  | CSkip => Q s
  | CAsgn x e => Q (upd s x (eval s e))
  | CSeq a b => wpc a (wpc b Q) s
  | CIf c t e => (eval s c <> 0 -> wpc t Q s) /\ (eval s c = 0 -> wpc e Q s)
  | CWhile Inv c body =>
      Inv s
      /\ (forall s', Inv s' -> eval s' c <> 0 -> wpc body Inv s')   (* invariant preserved by the body *)
      /\ (forall s', Inv s' -> eval s' c = 0 -> Q s')               (* invariant and exit imply the post *)
  end.

Theorem wpc_sound : forall k Q s s', wpc k Q s -> ceval k s s' -> Q s'.
Proof.
  intros k Q s s' Hwp Hev. revert Q Hwp.
  induction Hev; intros Q Hwp; simpl in Hwp.
  - exact Hwp.
  - exact Hwp.
  - apply IHHev2. apply (IHHev1 (wpc b Q)). exact Hwp.
  - destruct Hwp as [Ht _]. apply IHHev. apply Ht. exact H.
  - destruct Hwp as [_ He]. apply IHHev. apply He. exact H.
  - destruct Hwp as [Hi [_ Hexit]]. apply Hexit; assumption.
  - destruct Hwp as [Hi [Hpres Hexit]].
    apply IHHev2. simpl. split;
      [ apply (IHHev1 Inv); apply Hpres; assumption | split; assumption ].
Qed.

(* ---- An extractable, trap-aware verification-condition generator over loops ----

   The command language kcmd adds loops to the first-order data the engine emits. KWhile carries a
   syntactic invariant (a form), and vcg computes the entry precondition together with a list of side
   obligations, each a form required valid (true in every state). A loop's obligations are
   guard-definedness, invariant preservation across the body, and invariant-with-exit implies the
   postcondition; a division contributes its divisor-nonzero obligation, so vcg is trap-aware. The
   invariant is supplied to vcg by the engine (verify_deductive / verify_chc), and vcg_sound proves
   partial correctness: a discharged obligation set certifies the postcondition of every terminating
   run. vcg is extracted to OCaml alongside wpg. *)
Inductive kcmd :=
| KSkip
| KAsgn (x : var) (e : expr)
| KSeq (a b : kcmd)
| KIf (c : expr) (t e : kcmd)
| KWhile (Inv : form) (c : expr) (body : kcmd).

(* Big-step operational semantics, relating a command and an entry state to the state of a TERMINATING
   run; a non-terminating loop simply has no derivation, as for cmd / ceval above. *)
Inductive keval : kcmd -> state -> state -> Prop :=
| K_Skip   : forall s, keval KSkip s s
| K_Asgn   : forall s x e, keval (KAsgn x e) s (upd s x (eval s e))
| K_Seq    : forall a b s s' s'', keval a s s' -> keval b s' s'' -> keval (KSeq a b) s s''
| K_IfT    : forall c t e s s', eval s c <> 0 -> keval t s s' -> keval (KIf c t e) s s'
| K_IfF    : forall c t e s s', eval s c =  0 -> keval e s s' -> keval (KIf c t e) s s'
| K_WhileF : forall Inv c body s, eval s c = 0 -> keval (KWhile Inv c body) s s
| K_WhileT : forall Inv c body s s' s'', eval s c <> 0 -> keval body s s' ->
               keval (KWhile Inv c body) s' s'' -> keval (KWhile Inv c body) s s''.

(* vcg k Q = (precondition to hold at entry, list of side obligations, each required valid). For a loop
   the entry precondition is the invariant; the obligations are guard-definedness, invariant
   preservation across one body iteration, and invariant-and-exit implies the postcondition. *)
Fixpoint vcg (k : kcmd) (Q : form) : form * list form :=
  match k with
  | KSkip => (Q, nil)
  | KAsgn x e => (FAnd (defined_expr e) (subst_form x e Q), nil)
  | KSeq a b =>
      (fst (vcg a (fst (vcg b Q))),
       snd (vcg a (fst (vcg b Q))) ++ snd (vcg b Q))
  | KIf c t e =>
      (FAnd (defined_expr c)
        (FAnd (FImpl (FNot (FEq c (EConst 0))) (fst (vcg t Q)))
              (FImpl (FEq c (EConst 0)) (fst (vcg e Q)))),
       snd (vcg t Q) ++ snd (vcg e Q))
  | KWhile Inv c body =>
      (Inv,
       FImpl Inv (defined_expr c)
       :: FImpl (FAnd Inv (FNot (FEq c (EConst 0)))) (fst (vcg body Inv))
       :: FImpl (FAnd Inv (FEq c (EConst 0))) Q
       :: snd (vcg body Inv))
  end.

Definition valid (f : form) : Prop := forall s, eval_form s f.

(* Soundness (partial correctness): if every side obligation is valid and the entry precondition holds
   at s, then the postcondition holds of the state of every terminating run from s. A discharged loop
   VC therefore certifies the property under the operational semantics, extending the machine-checked
   guarantee from straight-line code and conditionals to loops. *)
Theorem vcg_sound : forall k s s', keval k s s' ->
  forall Q, Forall valid (snd (vcg k Q)) -> eval_form s (fst (vcg k Q)) -> eval_form s' Q.
Proof.
  intros k s s' Hev. induction Hev; intros Q Hobs Hpre; simpl in *.
  - (* K_Skip *) exact Hpre.
  - (* K_Asgn *) destruct Hpre as [_ Hsub]. rewrite subst_form_eval in Hsub. exact Hsub.
  - (* K_Seq *) rewrite Forall_app in Hobs. destruct Hobs as [Hoa Hob].
    apply (IHHev2 Q Hob). exact (IHHev1 (fst (vcg b Q)) Hoa Hpre).
  - (* K_IfT *) destruct Hpre as [_ [Ht _]]. rewrite Forall_app in Hobs. destruct Hobs as [Hot _].
    apply (IHHev Q Hot). apply Ht. exact H.
  - (* K_IfF *) destruct Hpre as [_ [_ He]]. rewrite Forall_app in Hobs. destruct Hobs as [_ Hoe].
    apply (IHHev Q Hoe). apply He. exact H.
  - (* K_WhileF *) pose proof (Forall_inv_tail (Forall_inv_tail Hobs)) as Ht2.
    pose proof (Forall_inv Ht2) as Hexit.
    apply (Hexit s). simpl. split; [exact Hpre | exact H].
  - (* K_WhileT *)
    pose proof (Forall_inv (Forall_inv_tail Hobs)) as Hpres.
    pose proof (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail Hobs))) as Hbodyobs.
    assert (Hbody : eval_form s (fst (vcg body Inv)))
      by (apply (Hpres s); simpl; split; [exact Hpre | exact H]).
    assert (Hinv' : eval_form s' Inv) by exact (IHHev1 Inv Hbodyobs Hbody).
    apply (IHHev2 Q Hobs). simpl. exact Hinv'.
Qed.

(* Trap-freedom over loops. ksafe k s s' holds for a terminating run that evaluates no division by a
   zero divisor (edefined at every expression it reaches). vcg_sound_safe strengthens vcg_sound: a
   discharged obligation set certifies both that the run is trap-free and that the postcondition holds,
   so a PROVED loop totality claim really is free of division by zero, not only correct on exit. *)
Inductive ksafe : kcmd -> state -> state -> Prop :=
| KS_Skip   : forall s, ksafe KSkip s s
| KS_Asgn   : forall s x e, edefined s e -> ksafe (KAsgn x e) s (upd s x (eval s e))
| KS_Seq    : forall a b s s' s'', ksafe a s s' -> ksafe b s' s'' -> ksafe (KSeq a b) s s''
| KS_IfT    : forall c t e s s', edefined s c -> eval s c <> 0 -> ksafe t s s' -> ksafe (KIf c t e) s s'
| KS_IfF    : forall c t e s s', edefined s c -> eval s c =  0 -> ksafe e s s' -> ksafe (KIf c t e) s s'
| KS_WhileF : forall Inv c body s, edefined s c -> eval s c = 0 -> ksafe (KWhile Inv c body) s s
| KS_WhileT : forall Inv c body s s' s'', edefined s c -> eval s c <> 0 -> ksafe body s s' ->
                ksafe (KWhile Inv c body) s' s'' -> ksafe (KWhile Inv c body) s s''.

Theorem vcg_sound_safe : forall k s s', keval k s s' ->
  forall Q, Forall valid (snd (vcg k Q)) -> eval_form s (fst (vcg k Q)) ->
  ksafe k s s' /\ eval_form s' Q.
Proof.
  intros k s s' Hev. induction Hev; intros Q Hobs Hpre; simpl in *.
  - (* K_Skip *) split; [apply KS_Skip | exact Hpre].
  - (* K_Asgn *) destruct Hpre as [Hd Hsub]. apply defined_expr_eval in Hd.
    rewrite subst_form_eval in Hsub. split; [apply KS_Asgn; exact Hd | exact Hsub].
  - (* K_Seq *) rewrite Forall_app in Hobs. destruct Hobs as [Hoa Hob].
    destruct (IHHev1 (fst (vcg b Q)) Hoa Hpre) as [Sa Pa].
    destruct (IHHev2 Q Hob Pa) as [Sb Pb].
    split; [eapply KS_Seq; [exact Sa | exact Sb] | exact Pb].
  - (* K_IfT *) destruct Hpre as [Hc [Ht _]]. apply defined_expr_eval in Hc.
    rewrite Forall_app in Hobs. destruct Hobs as [Hot _].
    destruct (IHHev Q Hot (Ht H)) as [St Pt].
    split; [apply KS_IfT; [exact Hc | exact H | exact St] | exact Pt].
  - (* K_IfF *) destruct Hpre as [Hc [_ He]]. apply defined_expr_eval in Hc.
    rewrite Forall_app in Hobs. destruct Hobs as [_ Hoe].
    destruct (IHHev Q Hoe (He H)) as [Se Pe].
    split; [apply KS_IfF; [exact Hc | exact H | exact Se] | exact Pe].
  - (* K_WhileF *)
    pose proof (Forall_inv Hobs s) as Hgd; simpl in Hgd.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail Hobs)) s) as Hexit; simpl in Hexit.
    assert (Hc : edefined s c) by (apply defined_expr_eval; apply Hgd; exact Hpre).
    split; [apply KS_WhileF; [exact Hc | exact H] | apply Hexit; split; [exact Hpre | exact H]].
  - (* K_WhileT *)
    pose proof (Forall_inv Hobs s) as Hgd; simpl in Hgd.
    pose proof (Forall_inv (Forall_inv_tail Hobs) s) as Hpres; simpl in Hpres.
    pose proof (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail Hobs))) as Hbodyobs.
    assert (Hc : edefined s c) by (apply defined_expr_eval; apply Hgd; exact Hpre).
    assert (Hbody : eval_form s (fst (vcg body Inv)))
      by (apply Hpres; split; [exact Hpre | exact H]).
    destruct (IHHev1 Inv Hbodyobs Hbody) as [Sbody Pbody].
    destruct (IHHev2 Q Hobs Pbody) as [Swhile Pwhile].
    split; [eapply KS_WhileT; [exact Hc | exact H | exact Sbody | exact Swhile] | exact Pwhile].
Qed.

Corollary vcg_trapfree : forall k s s', keval k s s' ->
  forall Q, Forall valid (snd (vcg k Q)) -> eval_form s (fst (vcg k Q)) -> ksafe k s s'.
Proof. intros k s s' Hev Q Ho Hp. exact (proj1 (vcg_sound_safe k s s' Hev Q Ho Hp)). Qed.

(* ---- Fixed-width machine integers ----

   eval above is over unbounded Z. A real machine stores a w-bit two's-complement integer, wrapping
   each result modulo 2^w into the signed range [-2^(w-1), 2^(w-1)). wrap is that reduction and inrange
   is membership in the signed range; evalm is the wrapping evaluation, applying wrap after every
   arithmetic operation. nooverflow s e is the per-operation obligation that each arithmetic result is
   representable, the condition the engine checks alongside the unbounded-Z proof. evalm_eq_eval proves
   that under those obligations the fixed-width result equals the exact one, so a property proved over Z
   holds of the machine execution whenever no operation overflows. *)
Section MachineInt.
Variable w : Z.
Hypothesis Hw : 0 < w.
Definition Modulus := 2 ^ w.
Definition Half := 2 ^ (w - 1).
Definition inrange (z : Z) : Prop := - Half <= z < Half.
Definition wrap (z : Z) : Z := (z + Half) mod Modulus - Half.

Lemma Modulus_pos : 0 < Modulus.
Proof. apply Z.pow_pos_nonneg; lia. Qed.

Lemma Modulus_eq : Modulus = 2 * Half.
Proof. unfold Modulus, Half. rewrite <- Z.pow_succ_r by lia. f_equal. lia. Qed.

Lemma wrap_inrange : forall z, inrange (wrap z).
Proof.
  intro z. unfold inrange, wrap.
  pose proof (Z.mod_pos_bound (z + Half) Modulus Modulus_pos) as Hb.
  pose proof Modulus_eq as Hm. lia.
Qed.

Lemma wrap_id : forall z, inrange z -> wrap z = z.
Proof.
  intros z Hr. unfold inrange in Hr. unfold wrap.
  rewrite Z.mod_small; [lia | rewrite Modulus_eq; lia].
Qed.

Fixpoint evalm (s : state) (e : expr) : Z :=
  match e with
  | EVar x => s x
  | EConst z => z
  | EAdd a b => wrap (evalm s a + evalm s b)
  | ESub a b => wrap (evalm s a - evalm s b)
  | EMul a b => wrap (evalm s a * evalm s b)
  | EDiv a b => wrap (evalm s a / evalm s b)
  | EMod a b => wrap (Z.modulo (evalm s a) (evalm s b))
  | ELt a b => if Z.ltb (evalm s a) (evalm s b) then 1 else 0
  | ELe a b => if Z.leb (evalm s a) (evalm s b) then 1 else 0
  | EEq a b => if Z.eqb (evalm s a) (evalm s b) then 1 else 0
  | ENot a => if Z.eqb (evalm s a) 0 then 1 else 0
  | EAnd a b => if andb (negb (Z.eqb (evalm s a) 0)) (negb (Z.eqb (evalm s b) 0)) then 1 else 0
  | EOr a b => if orb (negb (Z.eqb (evalm s a) 0)) (negb (Z.eqb (evalm s b) 0)) then 1 else 0
  end.

Fixpoint nooverflow (s : state) (e : expr) : Prop :=
  match e with
  | EVar _ | EConst _ => True
  | EAdd a b => nooverflow s a /\ nooverflow s b /\ inrange (eval s a + eval s b)
  | ESub a b => nooverflow s a /\ nooverflow s b /\ inrange (eval s a - eval s b)
  | EMul a b => nooverflow s a /\ nooverflow s b /\ inrange (eval s a * eval s b)
  | EDiv a b => nooverflow s a /\ nooverflow s b /\ inrange (eval s a / eval s b)
  | EMod a b => nooverflow s a /\ nooverflow s b /\ inrange (Z.modulo (eval s a) (eval s b))
  | ELt a b | ELe a b | EEq a b | EAnd a b | EOr a b => nooverflow s a /\ nooverflow s b
  | ENot a => nooverflow s a
  end.

(* Under the no-overflow obligations, fixed-width evaluation agrees with the unbounded-Z semantics. *)
Theorem evalm_eq_eval : forall s e, nooverflow s e -> evalm s e = eval s e.
Proof.
  intros s e. revert s.
  induction e as [ x | z | a IHa b IHb | a IHa b IHb | a IHa b IHb | a IHa b IHb | a IHa b IHb
                 | a IHa b IHb | a IHa b IHb | a IHa b IHb | a IHa | a IHa b IHb | a IHa b IHb ];
    intros s Hno; simpl in *;
    try reflexivity;
    try (destruct Hno as [Ha [Hb Hin]]; rewrite (IHa s Ha), (IHb s Hb); apply wrap_id; exact Hin);
    try (destruct Hno as [Ha Hb]; rewrite (IHa s Ha), (IHb s Hb); reflexivity);
    try (rewrite (IHa s Hno); reflexivity).
Qed.

End MachineInt.

Print Assumptions denote_id.
Print Assumptions denote_compose.
Print Assumptions denote_sound.
Print Assumptions denote_complete.
Print Assumptions denote_iff_bigstep.
Print Assumptions wp_sound.
Print Assumptions wp_complete.
Print Assumptions vc_sound_operational.
Print Assumptions pipeline_sound.
Print Assumptions wpsafe_sound.
Print Assumptions wpg_sound.
Print Assumptions wpg_complete.
Print Assumptions wpc_sound.
Print Assumptions vcg_sound.
Print Assumptions vcg_sound_safe.
Print Assumptions vcg_trapfree.
Print Assumptions evalm_eq_eval.
Print Assumptions wrap_inrange.
Print Assumptions wrap_id.

(* Extraction of the verified verification-condition generator to OCaml. coqc on this file emits
   vcgen.ml, whose wpg / subst_form / subst_expr / defined_expr are the exact functions proved sound
   and complete above. build_vcgen.sh compiles it behind a driver and the Python engine's vcgen audit
   holds the in-engine generator equal to it, so the generator that runs is the one verified here. *)
From Stdlib Require Extraction.
Extraction Language OCaml.
Extract Inductive list => "list" [ "[]" "(::)" ].   (* the loop obligations extract to a native OCaml list *)
Extract Inductive prod => "( * )" [ "(,)" ].        (* vcg's (precondition, obligations) is a native tuple *)
Extraction "vcgen.ml" wpg vcg subst_form subst_expr defined_expr.

(* The same generator extracted to the language-neutral JSON abstract syntax. json_to_python.py walks
   that syntax to emit the engine's Python generator, so the running wpg / vcg is a mechanical image of
   this development rather than a hand transcription; generate_engine.sh drives the regeneration and the
   committed result is checked against a fresh one. *)
Extraction Language JSON.
Extraction "vcgen.json" wpg vcg subst_form subst_expr defined_expr.
