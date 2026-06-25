(* GENERATED from the engine's actual integer obligations by touchstone.smtcoq_export.
   Each goal is a refutation query the engine discharged as PROVED; SMTCoq re-checks the veriT
   certificate in Coq's kernel. Regenerate: python -m touchstone.smtcoq_export proofs/touchstone_obligations.v *)
From SMTCoq Require Import SMTCoq.
From Coq Require Import Bool ZArith.
Local Open Scope Z_scope.

Goal forall (v0 : Z), (negb (andb (orb (Z.leb 0 v0) (orb (Z.leb 100 v0) (andb (Z.leb v0 0) (negb (Z.leb 100 v0))))) (orb (Z.leb 100 v0) (orb (Z.leb v0 100) (andb (Z.leb v0 0) (negb (Z.leb 100 v0))))))) = false.
Proof. verit. Qed.

Goal forall (v0 : Z), (negb (orb (Z.leb 10 v0) (Z.leb v0 10))) = false.
Proof. verit. Qed.

Goal forall (v0 : Z), (andb (Z.leb 0 v0) (negb (Z.leb 0 v0))) = false.
Proof. verit. Qed.

Goal forall (v0 v1 : Z), (andb (Z.leb 0 v0) (andb (Z.leb v0 v1) (andb (negb (Z.leb v1 v0)) (negb (andb (Z.leb (-1) v0) (Z.leb v0 ((-1) + v1))))))) = false.
Proof. verit. Qed.

Goal forall (v0 v1 : Z), (andb (Z.leb 0 v0) (andb (Z.leb v0 v1) (andb (Z.leb v1 v0) (negb (Z.eqb v0 v1))))) = false.
Proof. verit. Qed.
