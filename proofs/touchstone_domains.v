(* Trust base for touchstone.py, part III: soundness of two engines, machine-checked.

   1. The interval abstract domain. Each abstract operation in touchstone.py (_iadd, _ineg,
      _isub, _ijoin) must OVER-APPROXIMATE its concrete counterpart: if the inputs lie in
      their intervals, the concrete result lies in the abstract result. These are the
      soundness obligations of the interval transfer functions.

   2. The ranking-function termination principle (verify_termination / verify_ranking_synth):
      a measure that is bounded below and strictly decreases on every step cannot decrease
      forever, so the loop terminates.

   Both are closed under the global context (no axioms, no Admitted). *)

From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Definition mem (lo hi x : Z) : Prop := lo <= x <= hi.

(* _iadd: [a,b] + [c,d] = [a+c, b+d]. *)
Theorem iadd_sound : forall a b c d x y,
  mem a b x -> mem c d y -> mem (a + c) (b + d) (x + y).
Proof. unfold mem; intros; lia. Qed.

(* _ineg: -[a,b] = [-b, -a]. *)
Theorem ineg_sound : forall a b x, mem a b x -> mem (-b) (-a) (-x).
Proof. unfold mem; intros; lia. Qed.

(* _isub = _iadd . _ineg: [a,b] - [c,d] = [a-d, b-c]. *)
Theorem isub_sound : forall a b c d x y,
  mem a b x -> mem c d y -> mem (a - d) (b - c) (x - y).
Proof. unfold mem; intros; lia. Qed.

(* _ijoin over-approximates the union of two intervals. *)
Theorem ijoin_sound : forall a b c d x,
  (mem a b x \/ mem c d x) -> mem (Z.min a c) (Z.max b d) x.
Proof. unfold mem; intros a b c d x [H | H]; lia. Qed.

(* Ranking-function termination: a Z-valued measure that is always >= 0 and decreases by
   at least 1 each step admits no infinite descending chain. *)
Theorem ranking_terminates :
  forall f : nat -> Z,
    (forall n, 0 <= f n) ->
    (forall n, f (S n) <= f n - 1) ->
    False.
Proof.
  intros f Hpos Hdec.
  assert (Hchain : forall n, f n <= f 0%nat - Z.of_nat n).
  { intro n. induction n as [| k IH].
    - simpl. lia.
    - rewrite Nat2Z.inj_succ. specialize (Hdec k). lia. }
  specialize (Hchain (S (Z.to_nat (f 0%nat)))).
  rewrite Nat2Z.inj_succ in Hchain.
  rewrite Z2Nat.id in Hchain by apply (Hpos 0%nat).
  specialize (Hpos (S (Z.to_nat (f 0%nat)))).
  lia.
Qed.

(* _imul: interval multiplication. x*y, for x in [al,ah] and y in [bl,bh], is bounded by
   the min and max of the four corner products -- the bilinear extremes are at corners.
   This is the soundness obligation touchstone.py's _imul discharges and was the missing
   (and most error-prone) interval transfer. *)
Lemma mul_l_bound : forall al ah x y,
  al <= x -> x <= ah -> Z.min (al * y) (ah * y) <= x * y <= Z.max (al * y) (ah * y).
Proof.
  intros al ah x y Hl Hh.
  destruct (Z_le_gt_dec 0 y) as [Hy | Hy].
  - rewrite Z.min_l by nia. rewrite Z.max_r by nia. nia.
  - rewrite Z.min_r by nia. rewrite Z.max_l by nia. nia.
Qed.

Theorem imul_sound : forall al ah bl bh x y,
  al <= x -> x <= ah -> bl <= y -> y <= bh ->
  Z.min (Z.min (al * bl) (al * bh)) (Z.min (ah * bl) (ah * bh)) <= x * y <=
  Z.max (Z.max (al * bl) (al * bh)) (Z.max (ah * bl) (ah * bh)).
Proof.
  intros al ah bl bh x y Hax Hxa Hby Hyb.
  destruct (mul_l_bound al ah x y Hax Hxa) as [L1 U1].
  destruct (mul_l_bound bl bh y al Hby Hyb) as [La Ua].
  destruct (mul_l_bound bl bh y ah Hby Hyb) as [Lb Ub].
  split.
  - apply Z.le_trans with (Z.min (al * y) (ah * y)); [ | exact L1].
    apply Z.min_glb.
    + apply Z.le_trans with (Z.min (al * bl) (al * bh)); [apply Z.le_min_l |].
      replace (al * y) with (y * al) by ring.
      replace (al * bl) with (bl * al) by ring. replace (al * bh) with (bh * al) by ring. exact La.
    + apply Z.le_trans with (Z.min (ah * bl) (ah * bh)); [apply Z.le_min_r |].
      replace (ah * y) with (y * ah) by ring.
      replace (ah * bl) with (bl * ah) by ring. replace (ah * bh) with (bh * ah) by ring. exact Lb.
  - apply Z.le_trans with (Z.max (al * y) (ah * y)); [exact U1 |].
    apply Z.max_lub.
    + apply Z.le_trans with (Z.max (al * bl) (al * bh)); [ | apply Z.le_max_l].
      replace (al * y) with (y * al) by ring.
      replace (al * bl) with (bl * al) by ring. replace (al * bh) with (bh * al) by ring. exact Ua.
    + apply Z.le_trans with (Z.max (ah * bl) (ah * bh)); [ | apply Z.le_max_r].
      replace (ah * y) with (y * ah) by ring.
      replace (ah * bl) with (bl * ah) by ring. replace (ah * bh) with (bh * ah) by ring. exact Ub.
Qed.

(* _widen: widening over-approximates the new interval. Bounds are Z extended with an
   infinity (None), matching touchstone.py's math.inf endpoints: a bound that grew is
   dropped to infinity, so the result always contains the new interval. *)
Definition inL (l : option Z) (x : Z) : Prop := match l with None => True | Some a => a <= x end.
Definition inU (u : option Z) (x : Z) : Prop := match u with None => True | Some b => x <= b end.
Definition widenL (ol nl : option Z) : option Z :=
  match ol, nl with Some o, Some n => if o <=? n then Some o else None | _, _ => None end.
Definition widenU (ou nu : option Z) : option Z :=
  match ou, nu with Some o, Some n => if n <=? o then Some o else None | _, _ => None end.

Theorem widenL_sound : forall ol nl x, inL nl x -> inL (widenL ol nl) x.
Proof.
  intros [o|] [n|] x H; simpl in *; try exact I.
  destruct (o <=? n) eqn:E; simpl; [ | exact I]. apply Z.leb_le in E. lia.
Qed.

Theorem widenU_sound : forall ou nu x, inU nu x -> inU (widenU ou nu) x.
Proof.
  intros [o|] [n|] x H; simpl in *; try exact I.
  destruct (n <=? o) eqn:E; simpl; [ | exact I]. apply Z.leb_le in E. lia.
Qed.

(* Zone / octagon JOIN over-approximates the union. A difference V_i - V_j bounded by c in
   either operand is bounded by the pointwise maximum the join takes for the DBM entry. *)
Theorem dbm_join_sound : forall ca cb d, (d <= ca \/ d <= cb) -> d <= Z.max ca cb.
Proof. intros ca cb d [H | H]; lia. Qed.

(* ------------------------------------------------------------------------- *)
(* Extractable abstract-domain operators. The soundness lemmas above fix the operations as
   inline expressions; here the same operations are packaged as executable functions on
   interval bounds, and re-proved sound as functions. These are the definitions extracted to
   OCaml (Extraction below) and intended to drive the engine, so the operation that runs is
   literally the operation proven sound -- not a Python transcription of it. *)

Definition iadd (a b c d : Z) : Z * Z := (a + c, b + d).
Definition ineg (a b : Z) : Z * Z := (- b, - a).
Definition isub (a b c d : Z) : Z * Z := (a - d, b - c).
Definition ijoin (a b c d : Z) : Z * Z := (Z.min a c, Z.max b d).
Definition imul (al ah bl bh : Z) : Z * Z :=
  (Z.min (Z.min (al * bl) (al * bh)) (Z.min (ah * bl) (ah * bh)),
   Z.max (Z.max (al * bl) (al * bh)) (Z.max (ah * bl) (ah * bh))).

Theorem iadd_fn_sound : forall a b c d x y,
  mem a b x -> mem c d y -> mem (fst (iadd a b c d)) (snd (iadd a b c d)) (x + y).
Proof. unfold iadd, mem; simpl; intros; lia. Qed.

Theorem ineg_fn_sound : forall a b x,
  mem a b x -> mem (fst (ineg a b)) (snd (ineg a b)) (- x).
Proof. unfold ineg, mem; simpl; intros; lia. Qed.

Theorem isub_fn_sound : forall a b c d x y,
  mem a b x -> mem c d y -> mem (fst (isub a b c d)) (snd (isub a b c d)) (x - y).
Proof. unfold isub, mem; simpl; intros; lia. Qed.

Theorem ijoin_fn_sound : forall a b c d x,
  (mem a b x \/ mem c d x) -> mem (fst (ijoin a b c d)) (snd (ijoin a b c d)) x.
Proof. unfold ijoin, mem; simpl; intros a b c d x [H | H]; lia. Qed.

Theorem imul_fn_sound : forall al ah bl bh x y,
  mem al ah x -> mem bl bh y -> mem (fst (imul al ah bl bh)) (snd (imul al ah bl bh)) (x * y).
Proof.
  unfold imul, mem; simpl; intros al ah bl bh x y [Hal Hah] [Hbl Hbh].
  apply (imul_sound al ah bl bh x y); assumption.
Qed.

Print Assumptions iadd_sound.
Print Assumptions ijoin_sound.
Print Assumptions imul_sound.
Print Assumptions widenL_sound.
Print Assumptions widenU_sound.
Print Assumptions dbm_join_sound.
Print Assumptions ranking_terminates.
Print Assumptions iadd_fn_sound.
Print Assumptions imul_fn_sound.

(* Extraction of the verified operators to OCaml. coqc on this file emits intervals.ml, whose
   iadd / ineg / isub / ijoin / imul / widenL / widenU are the exact functions proved sound. *)
From Stdlib Require Extraction.
Extraction Language OCaml.
Extraction "intervals.ml" iadd ineg isub ijoin imul widenL widenU.

(* The same operators in the language-neutral JSON abstract syntax; json_to_python.py turns it into the
   engine's Python interval operators, so the running operators are a mechanical image of this development. *)
Extraction Language JSON.
Extraction "intervals.json" iadd ineg isub ijoin imul widenL widenU.
