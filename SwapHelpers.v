Require Import QuantumLib.Quantum.

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