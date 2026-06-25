(* Trust base for touchstone.py, part: the Python-to-IR lowering is semantics-preserving.

   touchstone/vcgen.py lowers the loop-free integer fragment of a Python function (_lower_expr / _lower_cond /
   _lower_prog) into the IR of touchstone_functor.v -- expr (arithmetic, comparisons, the boolean connectives)
   and prog (assignment and conditional control flow) -- which the verified VC generator then discharges. That
   lowering was cross-checked against CPython by sampling (vcgen._audit_against_cpython). Here it is proved
   correct against an INDEPENDENT Rocq model of the Python integer semantics: a distinct Python-subset AST
   (pyexpr / pycond / pyprog) whose evaluator is written directly as Python's rules, the lowering functions
   mirroring _lower_expr / _lower_cond / _lower_prog (with their real rewrites -- a > b lowers to b < a, a != b
   to not (a == b), -x to 0 - x), and theorems that the lowered IR denotes EXACTLY the Python semantics. So the
   front end's lowering rests on a theorem, not on samples. The residual gap -- that this Rocq model of Python
   matches CPython -- is the modeling gap the whole trust base shares; the differential audits still guard it.

   The IR (expr / eval / prog / denote) is re-declared here verbatim from touchstone_functor.v so this file is
   standalone like the other companion proofs; it is the same IR the functor proves sound and the engine runs. *)

From Stdlib Require Import ZArith Lia List Bool.
Import ListNotations.
Open Scope Z_scope.

(* ===================== the target IR (mirrors touchstone_functor.v) ===================== *)
Definition var := nat.
Definition state := var -> Z.
Definition upd (s : state) (x : var) (v : Z) : state :=
  fun y => if Nat.eqb x y then v else s y.

Inductive expr :=
| EVar (x : var) | EConst (z : Z)
| EAdd (a b : expr) | ESub (a b : expr) | EMul (a b : expr)
| EDiv (a b : expr) | EMod (a b : expr)
| ELt (a b : expr) | ELe (a b : expr) | EEq (a b : expr)
| ENot (a : expr) | EAnd (a b : expr) | EOr (a b : expr).

Fixpoint eval (s : state) (e : expr) : Z :=
  match e with
  | EVar x => s x
  | EConst z => z
  | EAdd a b => eval s a + eval s b
  | ESub a b => eval s a - eval s b
  | EMul a b => eval s a * eval s b
  | EDiv a b => eval s a / eval s b
  | EMod a b => Z.modulo (eval s a) (eval s b)
  | ELt a b => if Z.ltb (eval s a) (eval s b) then 1 else 0
  | ELe a b => if Z.leb (eval s a) (eval s b) then 1 else 0
  | EEq a b => if Z.eqb (eval s a) (eval s b) then 1 else 0
  | ENot a => if Z.eqb (eval s a) 0 then 1 else 0
  | EAnd a b => if andb (negb (Z.eqb (eval s a) 0)) (negb (Z.eqb (eval s b) 0)) then 1 else 0
  | EOr a b => if orb (negb (Z.eqb (eval s a) 0)) (negb (Z.eqb (eval s b) 0)) then 1 else 0
  end.

Inductive prog :=
| PNil
| PAsgn (x : var) (e : expr) (rest : prog)
| PCond (c : expr) (thn els rest : prog).

Fixpoint denote (p : prog) (s : state) : state :=
  match p with
  | PNil => s
  | PAsgn x e rest => denote rest (upd s x (eval s e))
  | PCond c thn els rest =>
      denote rest (if Z.eqb (eval s c) 0 then denote els s else denote thn s)
  end.

(* ===================== the source: a Python-subset AST, distinct from the IR ===================== *)
(* Python integer VALUE expressions (the fragment _lower_expr accepts). Comparisons evaluate to Python's 0/1;
   PyNeg is unary minus; PyNot is `not`. and/or are NOT here: _lower_expr declines them in value position
   (they return an operand and short-circuit), so they live only in a test (pycond) below. *)
Inductive pyexpr :=
| PyVar (x : var) | PyInt (z : Z)
| PyAdd (a b : pyexpr) | PySub (a b : pyexpr) | PyMul (a b : pyexpr)
| PyFloorDiv (a b : pyexpr) | PyMod (a b : pyexpr)
| PyLt (a b : pyexpr) | PyLe (a b : pyexpr) | PyGt (a b : pyexpr)
| PyGe (a b : pyexpr) | PyEq (a b : pyexpr) | PyNe (a b : pyexpr)
| PyNeg (a : pyexpr) | PyNot (a : pyexpr).

(* Python's value semantics for the integer fragment, written DIRECTLY (not via the IR): floor // and floored
   %, comparisons as 0/1 with each operator in its own orientation, unary minus, and `not` as the 0/1
   truthiness complement. *)
Fixpoint peval (s : state) (e : pyexpr) : Z :=
  match e with
  | PyVar x => s x
  | PyInt z => z
  | PyAdd a b => peval s a + peval s b
  | PySub a b => peval s a - peval s b
  | PyMul a b => peval s a * peval s b
  | PyFloorDiv a b => peval s a / peval s b
  | PyMod a b => Z.modulo (peval s a) (peval s b)
  | PyLt a b => if Z.ltb (peval s a) (peval s b) then 1 else 0
  | PyLe a b => if Z.leb (peval s a) (peval s b) then 1 else 0
  | PyGt a b => if Z.gtb (peval s a) (peval s b) then 1 else 0
  | PyGe a b => if Z.geb (peval s a) (peval s b) then 1 else 0
  | PyEq a b => if Z.eqb (peval s a) (peval s b) then 1 else 0
  | PyNe a b => if negb (Z.eqb (peval s a) (peval s b)) then 1 else 0
  | PyNeg a => - peval s a
  | PyNot a => if Z.eqb (peval s a) 0 then 1 else 0
  end.

(* The lowering of a value expression, mirroring vcgen._lower_expr together with _lower_cond's comparison
   table (_CMP_EXPR): a > b lowers to b < a, a >= b to b <= a, a != b to not (a == b), -a to 0 - a, not a to
   ENot a; the rest map structurally. *)
Fixpoint lower_expr (e : pyexpr) : expr :=
  match e with
  | PyVar x => EVar x
  | PyInt z => EConst z
  | PyAdd a b => EAdd (lower_expr a) (lower_expr b)
  | PySub a b => ESub (lower_expr a) (lower_expr b)
  | PyMul a b => EMul (lower_expr a) (lower_expr b)
  | PyFloorDiv a b => EDiv (lower_expr a) (lower_expr b)
  | PyMod a b => EMod (lower_expr a) (lower_expr b)
  | PyLt a b => ELt (lower_expr a) (lower_expr b)
  | PyLe a b => ELe (lower_expr a) (lower_expr b)
  | PyGt a b => ELt (lower_expr b) (lower_expr a)
  | PyGe a b => ELe (lower_expr b) (lower_expr a)
  | PyEq a b => EEq (lower_expr a) (lower_expr b)
  | PyNe a b => ENot (EEq (lower_expr a) (lower_expr b))
  | PyNeg a => ESub (EConst 0) (lower_expr a)
  | PyNot a => ENot (lower_expr a)
  end.

Lemma ne_lower : forall x y : Z,
  (if Z.eqb (if Z.eqb x y then 1 else 0) 0 then 1 else 0) = (if negb (Z.eqb x y) then 1 else 0).
Proof. intros x y. destruct (Z.eqb x y); reflexivity. Qed.

(* Semantics preservation for value expressions: the IR the lowering emits denotes exactly the Python value.
   The comparison-flip (PyGt / PyGe), the != rewrite, and the negation rewrite carry the content. *)
Theorem lower_expr_sound : forall s e, eval s (lower_expr e) = peval s e.
Proof.
  intros s e; induction e; simpl;
    repeat match goal with H : eval _ (lower_expr _) = _ |- _ => rewrite H; clear H end;
    try reflexivity.
  - rewrite Z.gtb_ltb; reflexivity.        (* PyGt:  b < a  ==  a > b *)
  - rewrite Z.geb_leb; reflexivity.        (* PyGe:  b <= a ==  a >= b *)
  - apply ne_lower.                        (* PyNe:  not (a == b) *)
  (* PyNeg (0 - a) reduces to (- a) definitionally, so it is already closed by reflexivity above. *)
Qed.

(* Python TEST expressions (the fragment _lower_cond accepts): a bare value (truthy iff nonzero), and the
   boolean connectives not / and / or over tests. A comparison test is a PyExpr of a comparison pyexpr. *)
Inductive pycond :=
| PCExpr (e : pyexpr)
| PCNot (c : pycond)
| PCAnd (c1 c2 : pycond)
| PCOr (c1 c2 : pycond).

(* Python truthiness of a test (a bool): nonzero value, and the short-circuit-agnostic connectives (sound in a
   test, where only the truth value matters -- exactly the position _lower_cond is used in). *)
Fixpoint pcond (s : state) (c : pycond) : bool :=
  match c with
  | PCExpr e => negb (Z.eqb (peval s e) 0)
  | PCNot c => negb (pcond s c)
  | PCAnd c1 c2 => andb (pcond s c1) (pcond s c2)
  | PCOr c1 c2 => orb (pcond s c1) (pcond s c2)
  end.

Fixpoint lower_cond (c : pycond) : expr :=
  match c with
  | PCExpr e => lower_expr e               (* _lower_cond on a bare expr returns _lower_expr (nonzero = truthy) *)
  | PCNot c => ENot (lower_cond c)
  | PCAnd c1 c2 => EAnd (lower_cond c1) (lower_cond c2)
  | PCOr c1 c2 => EOr (lower_cond c1) (lower_cond c2)
  end.

Lemma zeqb_if10 : forall b : bool, Z.eqb (if b then 1 else 0) 0 = negb b.
Proof. destruct b; reflexivity. Qed.

(* The lowered test is zero exactly when the Python test is false -- which is what the IR's conditional reads
   (PCond takes the else branch when its guard evaluates to 0). *)
Theorem lower_cond_sound : forall s c, Z.eqb (eval s (lower_cond c)) 0 = negb (pcond s c).
Proof.
  intros s c; induction c; simpl.
  - rewrite lower_expr_sound, Bool.negb_involutive; reflexivity.
  - rewrite zeqb_if10, IHc; reflexivity.
  - rewrite zeqb_if10, IHc1, IHc2, !Bool.negb_involutive; reflexivity.
  - rewrite zeqb_if10, IHc1, IHc2, !Bool.negb_involutive; reflexivity.
Qed.

(* Python loop-free statement programs in the IR's continuation form -- assignment and if/else with an explicit
   continuation -- which is the shape _lower_prog threads a statement list into. *)
Inductive pyprog :=
| PyDone
| PyAsgnP (x : var) (e : pyexpr) (rest : pyprog)
| PyIfP (c : pycond) (thn els rest : pyprog).

Fixpoint prun (p : pyprog) (s : state) : state :=
  match p with
  | PyDone => s
  | PyAsgnP x e rest => prun rest (upd s x (peval s e))
  | PyIfP c thn els rest => prun rest (if pcond s c then prun thn s else prun els s)
  end.

Fixpoint lower_prog (p : pyprog) : prog :=
  match p with
  | PyDone => PNil
  | PyAsgnP x e rest => PAsgn x (lower_expr e) (lower_prog rest)
  | PyIfP c thn els rest => PCond (lower_cond c) (lower_prog thn) (lower_prog els) (lower_prog rest)
  end.

(* Semantics preservation for the whole loop-free body: the IR the lowering emits denotes exactly the Python
   state transformer, over assignment AND branching. The expression and test lemmas supply each step. *)
Theorem lower_prog_sound : forall p s, denote (lower_prog p) s = prun p s.
Proof.
  intro p; induction p as [| x e rest IHrest | c thn IHthn els IHels rest IHrest];
    intro s; simpl.
  - reflexivity.
  - rewrite lower_expr_sound; apply IHrest.
  - rewrite lower_cond_sound. destruct (pcond s c); simpl.
    + rewrite IHthn; apply IHrest.
    + rewrite IHels; apply IHrest.
Qed.

(* No axioms: the lowering is semantics-preserving in the kernel's own logic. *)
Print Assumptions lower_expr_sound.
Print Assumptions lower_cond_sound.
Print Assumptions lower_prog_sound.
