From Proof Require Import Real.
From Proof Require Import Complex.
From Proof Require Import Matrix.
From Proof Require Import Qubit.
From Proof Require Import Multiqubit.

(*From YT's code: reviewed*)
Lemma lemma_a7 : forall (a b : Vector 2),
  SWAP × (a ⊗ b) == b ⊗ a.
Proof.
  lma.
Qed.

(*From YT's code: reviewed*)
Lemma lemma_a8 : forall (A B : Unitary 2),
  SWAP × (A ⊗ B) × SWAP == B ⊗ A.
Proof.
  lma.
Qed.

