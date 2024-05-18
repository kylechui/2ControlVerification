Require Import QuantumLib.Quantum.
From Proof Require Import SwapHelpers.
From Proof Require Import GateHelpers.
From Proof Require Import MatrixHelpers.
From Proof Require Import SwapProperty.
From Proof Require Import WFHelpers.
Lemma a10 : forall (a b : Vector 2),
  WF_Matrix a -> WF_Matrix b ->
    swap × (a ⊗ b) = b ⊗ a.
Proof.
  apply swap_2q.
Qed.

Lemma a11 : forall (A B : Square 2),
  WF_Matrix A -> WF_Matrix B ->
    swap × (A ⊗ B) × swap = B ⊗ A.
Proof.
  apply swap_2gate.
Qed.

Lemma a12 : forall (U : Square 4),
  WF_Matrix U ->
    swapab × acgate U × swapab = bcgate U.
Proof.
  intros.
  unfold acgate, swapbc, abgate.
  rewrite swap_helper. 2: assumption.
  fold swapab.
  rewrite <- Mmult_assoc.
  rewrite <- Mmult_assoc with (A := swapab) (B := swapab) (C := I 2 ⊗ U).
  rewrite swapab_inverse.
  rewrite Mmult_assoc.
  rewrite swapab_inverse at 1.
  Msimpl_light; solve_WF_matrix.
  unfold bcgate.
  reflexivity.
Qed.

Lemma a13_1 : forall (D: Square 2),
  WF_Matrix D ->
    swapab × ccu D × swapab = ccu D.
Proof.
  intros.
  lma'.
Qed.

Lemma a13_2 : forall (c1 : C), swapbc × ccu (diag2 1 c1) × swapbc = ccu (diag2 1 c1).
Proof.
  intros.
  lma'; unfold ccu; solve_WF_matrix.
Qed.

Lemma a13_3 : forall (c1 : C),
  swapac × ccu (diag2 1 c1) × swapac = ccu (diag2 1 c1).
Proof.
  intros.
  unfold swapac.
  repeat rewrite <- Mmult_assoc.
  do 4 rewrite Mmult_assoc.
  rewrite <- Mmult_assoc with (B := ccu (diag2 C1 c1)).
  rewrite <- Mmult_assoc with (B := swapab).
  rewrite a13_1 at 1. 2: apply WF_diag2.
  rewrite Mmult_assoc.
  rewrite <- Mmult_assoc with (A := ccu (diag2 C1 c1)).
  do 2 rewrite <- Mmult_assoc with (A := swapbc).
  rewrite a13_2 at 1.
  rewrite <- Mmult_assoc.
  apply a13_1.
  apply WF_diag2.
Qed.
