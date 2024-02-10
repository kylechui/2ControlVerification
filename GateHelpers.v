Require Import QuantumLib.Quantum.
From Proof Require Import MatrixHelpers. 
From Proof Require Import SwapHelpers.

Definition abgate (U : Square 4) := U ⊗ I 2.
Definition bcgate (U : Square 4) := I 2 ⊗ U.
Definition acgate (U : Square 4) := swapbc × (abgate U) × swapbc.
Definition ccu (U : Square 2) := control (control U).

Lemma WF_abgate : forall (U : Square 4), WF_Matrix U -> WF_Matrix (abgate U).
Proof.
intros. solve_WF_matrix.
Qed.

Lemma WF_bcgate : forall (U : Square 4), WF_Matrix U -> WF_Matrix (bcgate U).
Proof.
intros. solve_WF_matrix.
Qed.

Lemma WF_acgate : forall (U : Square 4), WF_Matrix U -> WF_Matrix (acgate U).
Proof.
intros.
apply WF_mult. solve_WF_matrix.
apply WF_swapbc.
Qed.

Lemma WF_ccu : forall (U : Square 2), WF_Matrix U -> WF_Matrix (ccu U).
Proof.
intros. solve_WF_matrix.
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

Lemma ccu_sum_expansion : forall (U : Square 2),
WF_Matrix U -> ccu U = ∣0⟩⟨0∣ ⊗ I 2 ⊗ I 2 .+ ∣1⟩⟨1∣ ⊗ (control U).
Proof. 
intros.
rewrite kron_assoc. 2,3,4: solve_WF_matrix.
lma'.
1,2: solve_WF_matrix.
all: unfold ccu.
all: rewrite Mplus_access.
all: rewrite upper_left_block_nonentries.
3,4,7,8,11,12,15,16: lia.
2,4,6,8: solve_WF_matrix.
all: rewrite lower_right_block_entries.
3,4,7,8,11,12,15,16: lia.
2,4,6,8: apply (@WF_control 2).
2,3,4,5: solve_WF_matrix.
all: unfold control.
all: simpl.
all: lca.
Qed.