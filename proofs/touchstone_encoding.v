(* Trust base for touchstone.py: the integer-encoding semantics-preservation theorem.

   The harness translates Python's `a // b` and `a % b` to Z3 integer terms.
   Z3's integer division/modulo are Euclidean (0 <= a mod b < |b|), while Python
   uses floor division. touchstone.py corrects this in py_floordiv:

       qe = a / b ; re = a % b ;            # Z3 (Euclidean)
       a // b  ==  If(re != 0 and b < 0, qe - 1, qe)
       a %  b  ==  a - (a // b) * b

   Coq's Z.div / Z.modulo ARE floor division/modulo, i.e. exactly Python's // and %.
   We model Z3's Euclidean div/mod (ediv/emod) and the harness encoding (pyfloordiv/
   pymod), and prove the encoding equals Z.div / Z.modulo for every nonzero divisor.
   This is the theorem the 300-sample soundness_probe was an approximation of.

   TRUST BOUNDARY: the harness emits Z3's integer `div`/`mod`, specified by the SMT-LIB Ints
   theory's Euclidean division (a = b*div + mod, 0 <= mod < |b|). Below we state that theory
   as axioms (SMTLIB_div_mod) and prove the harness encoding correct for EVERY div/mod that
   satisfies them (pyfloordiv_refines_smtlib), so the only remaining assumption is that Z3
   conforms to its published specification -- not that any particular Coq model equals Z3's
   implementation. division_encoding_audit() in touchstone.py corroborates that conformance
   against CPython; it no longer founds the result. *)

From Stdlib Require Import ZArith Lia Bool.
Open Scope Z_scope.

(* Z3 / SMT-LIB Euclidean division and modulo: 0 <= emod a b < |b|, a = b*ediv+emod. *)
Definition ediv (a b : Z) : Z := if 0 <? b then a / b else - (a / (- b)).
Definition emod (a b : Z) : Z := if 0 <? b then a mod b else a mod (- b).

(* The touchstone.py encoding of Python floor division and modulo. *)
Definition pyfloordiv (a b : Z) : Z :=
  if andb (negb (emod a b =? 0)) (b <? 0) then ediv a b - 1 else ediv a b.
Definition pymod (a b : Z) : Z := a - (pyfloordiv a b) * b.

(* Python's // is Coq's Z.div (floor division). *)
Theorem pyfloordiv_correct : forall a b, b <> 0 -> pyfloordiv a b = a / b.
Proof.
  intros a b Hb. unfold pyfloordiv, ediv, emod.
  destruct (0 <? b) eqn:Hgt.
  - apply Z.ltb_lt in Hgt.
    assert (b <? 0 = false) as Hlt by (apply Z.ltb_ge; lia).
    rewrite Hlt, andb_false_r. cbn [andb]. reflexivity.
  - apply Z.ltb_ge in Hgt.
    assert (b < 0) as Hneg by lia.
    assert (b <? 0 = true) as Hlt by (apply Z.ltb_lt; lia).
    assert (0 < - b) as Hmb by lia.
    pose proof (Z.mod_pos_bound a (- b) Hmb) as Hr.
    pose proof (Z.div_mod a (- b) ltac:(lia)) as Hdm.
    rewrite Hlt, andb_true_r.
    destruct (a mod (- b) =? 0) eqn:Hmod.
    + apply Z.eqb_eq in Hmod. cbn [negb].
      apply Z.div_unique with (r := 0).
      * lia.
      * replace (b * - (a / - b)) with (- b * (a / - b)) by ring. lia.
    + apply Z.eqb_neq in Hmod. cbn [negb].
      apply Z.div_unique with (r := a mod (- b) + b).
      * lia.
      * replace (b * (- (a / - b) - 1)) with (- b * (a / - b) + - b) by ring. lia.
Qed.

(* Python's % is Coq's Z.modulo, given the floor-division result above. *)
Theorem pymod_correct : forall a b, b <> 0 -> pymod a b = a mod b.
Proof.
  intros a b Hb. unfold pymod.
  rewrite (pyfloordiv_correct a b Hb).
  rewrite (Z.mod_eq a b Hb). ring.
Qed.

(* ------------------------------------------------------------------------- *)
(* Discharging the Z3-faithfulness assumption.

   Rather than take the concrete `ediv`/`emod` above to BE Z3's div/mod, we now state the
   SMT-LIB Ints theory as the axioms it specifies and prove the harness encoding correct for
   ANY div/mod satisfying them. The remaining trust is only that Z3 conforms to its published
   SMT-LIB specification -- not that any particular Coq model equals Z3's implementation. *)

(* The SMT-LIB Ints theory characterizes integer div/mod for a nonzero divisor by two axioms:
   the quotient and remainder reconstruct the dividend, and the remainder lies in [0, |b|). *)
Definition SMTLIB_div_mod (zdiv zmod : Z -> Z -> Z) : Prop :=
  forall a b, b <> 0 -> a = b * zdiv a b + zmod a b /\ 0 <= zmod a b < Z.abs b.

(* The harness encoding, parameterized over any conforming div/mod. *)
Definition pyfloordiv_of (zdiv zmod : Z -> Z -> Z) (a b : Z) : Z :=
  if andb (negb (zmod a b =? 0)) (b <? 0) then zdiv a b - 1 else zdiv a b.
Definition pymod_of (zdiv zmod : Z -> Z -> Z) (a b : Z) : Z := a - pyfloordiv_of zdiv zmod a b * b.

(* Refinement: for EVERY div/mod meeting the SMT-LIB axioms, the harness encoding is Python's
   floor division (Coq's Z.div), for every integer dividend and nonzero divisor. *)
Theorem pyfloordiv_refines_smtlib :
  forall zdiv zmod, SMTLIB_div_mod zdiv zmod ->
  forall a b, b <> 0 -> pyfloordiv_of zdiv zmod a b = a / b.
Proof.
  intros zdiv zmod Hsmt a b Hb. destruct (Hsmt a b Hb) as [Heq Hr].
  unfold pyfloordiv_of. destruct (b <? 0) eqn:Hbsign.
  - assert (Hblt : b < 0) by (apply Z.ltb_lt; exact Hbsign).
    rewrite Z.abs_neq in Hr by lia.
    destruct (zmod a b =? 0) eqn:Hm; simpl.
    + apply Z.eqb_eq in Hm.
      apply Z.div_unique with (r := zmod a b); [ lia | lia ].
    + apply Z.eqb_neq in Hm.
      apply Z.div_unique with (r := zmod a b + b);
        [ lia | replace (b * (zdiv a b - 1)) with (b * zdiv a b + - b) by ring; lia ].
  - assert (Hbge : 0 <= b) by (apply Z.ltb_ge; exact Hbsign).
    rewrite andb_false_r; simpl.
    rewrite Z.abs_eq in Hr by lia.
    apply Z.div_unique with (r := zmod a b); [ lia | lia ].
Qed.

Theorem pymod_refines_smtlib :
  forall zdiv zmod, SMTLIB_div_mod zdiv zmod ->
  forall a b, b <> 0 -> pymod_of zdiv zmod a b = a mod b.
Proof.
  intros zdiv zmod Hsmt a b Hb. unfold pymod_of.
  rewrite (pyfloordiv_refines_smtlib zdiv zmod Hsmt a b Hb).
  rewrite (Z.mod_eq a b Hb). ring.
Qed.

(* The concrete model used above DOES satisfy the SMT-LIB axioms, so it is one witness of the
   theory; the refinement theorems then specialize to it. The assumption is thereby reduced to
   Z3's conformance with SMT-LIB, which the differential audit corroborates rather than founds. *)
Theorem ediv_emod_conforms : SMTLIB_div_mod ediv emod.
Proof.
  intros a b Hb. unfold ediv, emod. destruct (0 <? b) eqn:Hgt.
  - apply Z.ltb_lt in Hgt.
    pose proof (Z.div_mod a b ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound a b ltac:(lia)) as Hr.
    rewrite Z.abs_eq by lia. lia.
  - apply Z.ltb_ge in Hgt. assert (b < 0) by lia.
    pose proof (Z.div_mod a (- b) ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound a (- b) ltac:(lia)) as Hr.
    rewrite Z.abs_neq by lia.
    split; [ replace (b * - (a / - b)) with (- b * (a / - b)) by ring; lia | lia ].
Qed.

(* The trap characterization: the encoding is total over nonzero divisors, and the
   only inputs Python rejects (and the harness flags as a trap) are b = 0. *)
Theorem trap_iff_zero_divisor :
  forall a b, (b = 0) <-> ~ (exists q r, a = b * q + r /\ 0 <= r < Z.abs b).
Proof.
  intros a b. split.
  - intros ->. intros [q [r [Heq Hr]]]. cbn in *. lia.
  - intros Hno. destruct (Z.eq_dec b 0) as [|Hne]; [assumption|].
    exfalso. apply Hno. exists (ediv a b), (emod a b).
    unfold ediv, emod. destruct (0 <? b) eqn:Hgt.
    + apply Z.ltb_lt in Hgt.
      pose proof (Z.div_mod a b ltac:(lia)) as Hdm.
      pose proof (Z.mod_pos_bound a b ltac:(lia)) as Hr.
      split; [lia | rewrite Z.abs_eq by lia; lia].
    + apply Z.ltb_ge in Hgt. assert (b < 0) by lia.
      pose proof (Z.div_mod a (- b) ltac:(lia)) as Hdm.
      pose proof (Z.mod_pos_bound a (- b) ltac:(lia)) as Hr.
      split.
      * replace (b * - (a / - b)) with (- b * (a / - b)) by ring. lia.
      * rewrite Z.abs_neq by lia. lia.
Qed.

(* Evidence of full proof: no axioms, no Admitted. *)
Print Assumptions pyfloordiv_correct.
Print Assumptions pymod_correct.
Print Assumptions pyfloordiv_refines_smtlib.
Print Assumptions pymod_refines_smtlib.
Print Assumptions ediv_emod_conforms.
Print Assumptions trap_iff_zero_divisor.

(* Extraction to OCaml: encoding.ml's pyfloordiv / pymod are the functions proved equal to Python's
   // and % above; the engine's encoding audit holds its py_floordiv / py_mod equal to these. *)
From Stdlib Require Extraction.
Extraction Language OCaml.
Extraction "encoding.ml" pyfloordiv pymod.

(* The same encoding in the language-neutral JSON abstract syntax, for json_to_python.py. *)
Extraction Language JSON.
Extraction "encoding.json" pyfloordiv pymod.
