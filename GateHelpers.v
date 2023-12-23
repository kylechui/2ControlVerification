Require Import QuantumLib.Quantum. 
From Proof Require Import SwapHelpers.

Definition abgate (U : Square 4) := U ⊗ I 2.
Definition bcgate (U : Square 4) := I 2 ⊗ U.
Definition acgate (U : Square 4) := swapbc × (abgate U) × swapbc.
Definition ccu (U : Square 2) := control (control U).

Lemma WF_abgate : forall (U : Square 4), WF_Matrix U -> WF_Matrix (abgate U).
Proof.
intros.
apply WF_kron.
reflexivity. reflexivity.
apply H. apply WF_I.
Qed.

Lemma WF_bcgate : forall (U : Square 4), WF_Matrix U -> WF_Matrix (bcgate U).
Proof.
intros.
apply WF_kron.
reflexivity. reflexivity.
apply WF_I. apply H. 
Qed.

Lemma WF_acgate : forall (U : Square 4), WF_Matrix U -> WF_Matrix (acgate U).
Proof.
intros.
apply WF_mult. apply WF_mult.
apply WF_swapbc.
apply WF_abgate. apply H.
apply WF_swapbc.
Qed.

Lemma WF_ccu : forall (U : Square 2), WF_Matrix U -> WF_Matrix (ccu U).
Proof.
intros. apply WF_control. apply WF_control. apply H.
Qed.

Lemma abgate_unitary : forall (U : Square 4), WF_Unitary U -> WF_Unitary (abgate U).
Proof.
intros.
apply kron_unitary. apply H. apply id_unitary.
Qed.

Lemma bcgate_unitary : forall (U : Square 4), WF_Unitary U -> WF_Unitary (bcgate U).
Proof.
intros.
apply kron_unitary. apply id_unitary. apply H.
Qed.

Lemma acgate_unitary : forall (U : Square 4), WF_Unitary U -> WF_Unitary (acgate U).
Proof.
intros.
apply Mmult_unitary. apply Mmult_unitary.
apply swapbc_unitary.
apply abgate_unitary. apply H.
apply swapbc_unitary.
Qed.

Lemma ccu_unitary : forall (U : Square 2), WF_Unitary U -> WF_Unitary (ccu U).
Proof.
intros.
apply control_unitary. apply control_unitary. apply H.
Qed.