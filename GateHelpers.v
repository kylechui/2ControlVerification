Require Import QuantumLib.Quantum.
From Proof Require Import MatrixHelpers. 
From Proof Require Import SwapHelpers.
From Proof Require Import SwapProperty.

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

Lemma bcgate_adjoint: forall (U : Square 4), WF_Matrix U -> 
(bcgate U) † = bcgate (U†).
Proof.
intros.
lma'.
apply WF_adjoint. apply WF_bcgate. assumption.
apply WF_bcgate. apply WF_adjoint. assumption.
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

Lemma swapab_ccu: forall (U: Square 2), WF_Matrix U ->
swapab × (ccu U) × swapab = ccu U.
Proof.
intros.
apply mat_equiv_eq.
apply WF_mult. apply WF_mult.
1,3: apply WF_swapab.
1,2: apply WF_ccu.
1,2: assumption.
by_cell.
lca. lca. lca. lca. lca. lca. lca. lca.
lca. lca. lca. lca. lca. lca. lca. lca.
lca. lca. lca. lca. lca. lca. lca. lca.
lca. lca. lca. lca. lca. lca. lca. lca.
lca. lca. lca. lca. lca. lca. lca. lca.
lca. lca. lca. lca. lca. lca. lca. lca.
lca. lca. lca. lca. lca. lca. lca. lca.
lca. lca. lca. lca. lca. lca. lca. lca.
Qed.

Lemma ccu_adjoint: forall (U: Square 2), WF_Matrix U ->
(ccu U)† = ccu U†.
Proof.
intros.
lma'.
apply WF_adjoint. apply WF_ccu. assumption.
apply WF_ccu. apply WF_adjoint. assumption.
all: rewrite Madj_explicit_decomp.
all: unfold ccu.
all: unfold control.
all: simpl.
all: lca.
Qed.

Lemma abgate_adjoint: forall (U : Square 4), WF_Matrix U -> 
(abgate U) † = abgate (U†).
Proof.
intros.
lma'.
apply WF_adjoint. apply WF_abgate. assumption.
apply WF_abgate. apply WF_adjoint. assumption.
Qed.

Lemma acgate_adjoint: forall (U : Square 4), WF_Matrix U -> 
(acgate U)† = acgate (U†).
Proof.
intros.
unfold acgate.
repeat rewrite Mmult_adjoint.
rewrite <- swapbc_sa. rewrite swapbc_sa at 1. rewrite adjoint_involutive.
rewrite abgate_adjoint. 2: solve_WF_matrix.
symmetry.
apply Mmult_assoc.
Qed.

Lemma acgate_alt_def: forall (U : Square 4), WF_Matrix U -> 
acgate U = swapab × bcgate U × swapab.
Proof.
intros.
unfold acgate, swapbc, abgate, swapab, bcgate.
apply swap_helper.
assumption.
Qed.

Lemma acgate_tens_eq: forall (U : Square 4) (a b c d e: Vector 2), 
WF_Matrix U -> WF_Matrix a -> WF_Matrix b -> WF_Matrix c -> WF_Matrix d -> WF_Matrix e ->
b <> Zero -> (acgate U) × (a ⊗ b ⊗ c) = d ⊗ b ⊗ e ->  U × (a ⊗ c) = d ⊗ e.
Proof.
intros U a b c d e WF_U WF_a WF_b WF_c WF_d WF_e bn0 gate_eq.
unfold acgate in gate_eq.
rewrite <- swapbc_3q with (a:= d) in gate_eq. 2,3,4: assumption.
apply (f_equal (fun f => swapbc × f)) in gate_eq.
repeat rewrite <- Mmult_assoc in gate_eq.
rewrite swapbc_inverse in gate_eq.
rewrite Mmult_1_l in gate_eq. 2: apply WF_abgate; solve_WF_matrix.
rewrite Mmult_1_l in gate_eq. 2: solve_WF_matrix.
rewrite Mmult_assoc in gate_eq.
rewrite swapbc_3q in gate_eq. 2,3,4: solve_WF_matrix.
unfold abgate in gate_eq.
assert (kron_mix_help: U ⊗ I 2 × (a ⊗ c ⊗ b) = (U × (a ⊗ c)) ⊗ (I 2 × b)). apply kron_mixed_product.
rewrite kron_mix_help in gate_eq at 1. clear kron_mix_help.
rewrite Mmult_1_l in gate_eq. 2: solve_WF_matrix.
apply (@kron_cancel_r 4 1 2 1) with (C:= b).
1,2,3: solve_WF_matrix.
1,2: assumption.
Qed.