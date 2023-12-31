Require Import QuantumLib.Quantum.
From Proof Require Import MatrixHelpers.

Definition swapab := swap ⊗ I 2.
Definition swapbc := I 2 ⊗ swap.
Definition swapac := swapab × swapbc × swapab.

Lemma WF_swapab : WF_Matrix swapab.
Proof.
solve_WF_matrix.
Qed.

Lemma WF_swapbc : WF_Matrix swapbc.
Proof.
solve_WF_matrix.
Qed.

Lemma WF_swapac : WF_Matrix swapac.
Proof.
apply WF_mult. solve_WF_matrix.
apply WF_swapab.
Qed.

Lemma swapab_unitary : WF_Unitary swapab.
Proof.
apply kron_unitary.
apply swap_unitary.
apply id_unitary.
Qed.

Lemma swapbc_unitary : WF_Unitary swapbc.
Proof.
apply kron_unitary.
apply id_unitary.
apply swap_unitary.
Qed.

Lemma swapac_unitary : WF_Unitary swapac.
Proof.
apply Mmult_unitary.
apply Mmult_unitary.
apply swapab_unitary.
apply swapbc_unitary. 
apply swapab_unitary.
Qed.

Lemma swapab_inverse : swapab × swapab = I 8.
Proof.
apply mat_equiv_eq. solve_WF_matrix. apply WF_I. 
unfold swapab.
rewrite kron_mixed_product.
rewrite swap_swap.
rewrite Mmult_1_l. 2: apply WF_I.
rewrite kron_I. 3: lia. 2: lia.
apply mat_equiv_refl.
Qed.

Lemma swapbc_inverse : swapbc × swapbc = I 8.
Proof.
apply mat_equiv_eq. solve_WF_matrix. apply WF_I.
unfold swapbc.
rewrite kron_mixed_product.
rewrite swap_swap.
rewrite Mmult_1_l. 2: apply WF_I.
rewrite kron_I. 3: lia. 2: lia.
apply mat_equiv_refl.
Qed.

Lemma swapac_inverse : swapac × swapac = I 8.
Proof.
apply mat_equiv_eq.
apply WF_mult. apply WF_swapac. apply WF_swapac.
apply WF_I.
unfold swapac.
repeat rewrite Mmult_assoc.
rewrite <- Mmult_assoc with (A := swapab) (B := swapab) (C:= swapbc × swapab).
rewrite <- Mmult_assoc with (A := swapbc) (B := swapab × swapab) (C:= swapbc × swapab).
rewrite swapab_inverse.
rewrite Mmult_1_r. 2: apply WF_swapbc.
rewrite <- Mmult_assoc with (A := swapbc) (B:= swapbc) (C:=swapab).
rewrite <- Mmult_assoc with (A := swapab) (B:= swapbc × swapbc) (C:=swapab).
rewrite swapbc_inverse.
rewrite Mmult_1_r. 2: apply WF_swapab.
rewrite <- swapab_inverse.
apply mat_equiv_refl.
Qed.

Lemma swap_2q : forall (A B : Square 2),
  WF_Matrix A -> WF_Matrix B ->
  swap × (A ⊗ B) × swap = B ⊗ A.
Proof.
  intros.
  lma'.
Qed.

Lemma swapab_3q : forall (A B C : Square 2), WF_Matrix A -> WF_Matrix B -> WF_Matrix C -> swapab × (A ⊗ B ⊗ C) × swapab = (B ⊗ A ⊗ C).
Proof. 
intros.
unfold swapab.
rewrite kron_mixed_product.
rewrite Mmult_1_l. 2: apply H1.
rewrite kron_mixed_product.
rewrite Mmult_1_r. 2: apply H1.
rewrite swap_2q. 3: apply H0. 2: apply H.
reflexivity.
Qed.

Lemma swapbc_3q : forall (A B C : Square 2), WF_Matrix A -> WF_Matrix B -> WF_Matrix C -> swapbc × (A ⊗ B ⊗ C) × swapbc = (A ⊗ C ⊗ B).
Proof. 
intros.
unfold swapbc.
rewrite kron_assoc. 4: apply H1. 3: apply H0. 2: apply H.
rewrite Mmult_assoc.
assert (A ⊗ (B ⊗ C) × (I 2 ⊗ swap) = (A × I 2) ⊗ ((B ⊗ C) × swap)).
{
    apply kron_mixed_product.
}
rewrite H2 at 1.
rewrite Mmult_1_r. 2: apply H.
assert (I 2 ⊗ swap × (A ⊗ (B ⊗ C × swap)) =
(I 2 × A) ⊗ (swap × (B ⊗ C × swap))).
{
    apply kron_mixed_product.
}
rewrite H3 at 1.
rewrite Mmult_1_l. 2: apply H.
rewrite <- Mmult_assoc.
rewrite swap_2q. 3: apply H1. 2: apply H0.
rewrite <- kron_assoc. 4: apply H0. 3: apply H1. 2: apply H. 
reflexivity.
Qed.

Lemma swapac_3q : forall (A B C : Square 2), WF_Matrix A -> WF_Matrix B -> WF_Matrix C -> swapac × (A ⊗ B ⊗ C) × swapac = (C ⊗ B ⊗ A).
Proof.
intros.
unfold swapac.
repeat rewrite <- Mmult_assoc.
rewrite Mmult_assoc. rewrite Mmult_assoc. rewrite Mmult_assoc. rewrite Mmult_assoc.
rewrite <- Mmult_assoc with (A:=swapab) (B:= A ⊗ B ⊗ C) (C:= (swapab × (swapbc × swapab))).
rewrite <- Mmult_assoc with (A := swapab) (B:= swapbc) (C:= swapab).
rewrite <- Mmult_assoc with (A:= swapab × (A ⊗ B ⊗ C)) (B :=swapab × swapbc) (C:= swapab).
rewrite <- Mmult_assoc with (A:= swapab × (A ⊗ B ⊗ C)) (B :=swapab) (C:= swapbc).
rewrite swapab_3q. 4: apply H1. 3: apply H0. 2: apply H.
rewrite Mmult_assoc.
rewrite <- Mmult_assoc with (A:=swapbc) (B:= B ⊗ A ⊗ C × swapbc) (C:= swapab).
rewrite <- Mmult_assoc with (A:=swapab) (B:= swapbc × (B ⊗ A ⊗ C × swapbc)) (C:= swapab).
rewrite <- Mmult_assoc with (A:= swapbc) (B:= B ⊗ A ⊗ C) (C:= swapbc).
rewrite swapbc_3q. 4: apply H1. 3: apply H. 2: apply H0.
rewrite swapab_3q. 4: apply H. 3: apply H1. 2: apply H0.
reflexivity.
Qed.  
