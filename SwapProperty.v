From Proof Require Import Real.
From Proof Require Import Complex.
From Proof Require Import Matrix.
From Proof Require Import Qubit.
From Proof Require Import Multiqubit.

Property swap_helper : forall (U : Unitary 4),
  (I 2 ⊗ SWAP) × (U ⊗ I 2) × (I 2 ⊗ SWAP) ==
  (SWAP ⊗ I 2) × (I 2 ⊗ U) × (SWAP ⊗ I 2).
Proof.
  intros. lma. (* Takes a minute *)
Qed.