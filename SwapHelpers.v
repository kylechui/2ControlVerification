Require Import QuantumLib.Quantum.
From Proof Require Import MatrixHelpers.

Definition swapab := swap ⊗ I 2.
Definition swapbc := I 2 ⊗ swap.
Definition swapac := swapab × swapbc × swapab.

Lemma WF_swapab : WF_Matrix swapab.
Proof.
apply WF_kron.
reflexivity. reflexivity.
apply WF_swap. apply WF_I.
Qed.

Lemma WF_swapbc : WF_Matrix swapbc.
Proof.
apply WF_kron.
reflexivity. reflexivity.
apply WF_I. apply WF_swap.
Qed.

Lemma WF_swapac : WF_Matrix swapac.
Proof.
apply WF_mult. apply WF_mult.
apply WF_swapab. apply WF_swapbc. apply WF_swapab.
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
apply mat_equiv_eq.
apply WF_mult. apply WF_swapab. apply WF_swapab.
apply WF_I.
unfold swapab.
rewrite kron_mixed_product.
rewrite swap_swap.
rewrite Mmult_1_l.
rewrite kron_I.
simpl. apply mat_equiv_refl.
lia. lia. apply WF_I.
Qed.

Lemma swapbc_inverse : swapbc × swapbc = I 8.
Proof.
apply mat_equiv_eq.
apply WF_mult. apply WF_swapbc. apply WF_swapbc.
apply WF_I.
unfold swapbc.
rewrite kron_mixed_product.
rewrite swap_swap.
rewrite Mmult_1_l.
rewrite kron_I.
simpl. apply mat_equiv_refl.
lia. lia. apply WF_I.
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
rewrite Mmult_1_r.
rewrite <- Mmult_assoc with (A := swapbc) (B:= swapbc) (C:=swapab).
rewrite <- Mmult_assoc with (A := swapab) (B:= swapbc × swapbc) (C:=swapab).
rewrite swapbc_inverse.
rewrite Mmult_1_r.
rewrite <- swapab_inverse.
apply mat_equiv_refl.
apply WF_swapab. apply WF_swapbc.
Qed.