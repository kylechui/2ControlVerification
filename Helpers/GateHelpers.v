Require Import QuantumLib.Quantum.
Require Import QuantumLib.Eigenvectors.
Require Import WFHelpers.
Require Import AlgebraHelpers.
Require Import MatrixHelpers.
Require Import SwapHelpers.
Require Import QubitHelpers.

Definition abgate (U : Square 4) := U ⊗ I 2.
Definition bcgate (U : Square 4) := I 2 ⊗ U.
Definition acgate (U : Square 4) := swapbc × (abgate U) × swapbc.
Definition ccu (U : Square 2) := control (control U).

#[global] Hint Unfold abgate bcgate acgate ccu : M_db.

Lemma WF_abgate : forall (U : Square 4), WF_Matrix U -> WF_Matrix (abgate U).
Proof.
  intros.
  solve_WF_matrix.
Qed.

Lemma WF_bcgate : forall (U : Square 4), WF_Matrix U -> WF_Matrix (bcgate U).
Proof.
  intros.
  solve_WF_matrix.
Qed.

Lemma WF_acgate : forall (U : Square 4), WF_Matrix U -> WF_Matrix (acgate U).
Proof.
  intros.
  solve_WF_matrix.
Qed.

Lemma WF_ccu : forall (U : Square 2), WF_Matrix U -> WF_Matrix (ccu U).
Proof.
  intros.
  solve_WF_matrix.
Qed.

#[export] Hint Resolve WF_abgate WF_bcgate WF_acgate WF_ccu : wf_db.

Lemma abgate_unitary : forall (U : Square 4), WF_Unitary U -> WF_Unitary (abgate U).
Proof.
  intros.
  autounfold with M_db; auto with unit_db.
Qed.

Lemma bcgate_unitary : forall (U : Square 4), WF_Unitary U -> WF_Unitary (bcgate U).
Proof.
  intros.
  autounfold with M_db; auto with unit_db.
Qed.

Lemma acgate_unitary : forall (U : Square 4), WF_Unitary U -> WF_Unitary (acgate U).
Proof.
  intros.
  autounfold with M_db; auto with unit_db.
Qed.

Lemma ccu_unitary : forall (U : Square 2), WF_Unitary U -> WF_Unitary (ccu U).
Proof.
  intros.
  autounfold with M_db; auto with unit_db.
Qed.

Lemma bcgate_adjoint: forall (U : Square 4), WF_Matrix U ->
  (bcgate U) † = bcgate (U†).
Proof.
  intros.
  unfold bcgate.
  rewrite kron_adjoint.
  rewrite id_adjoint_eq.
  reflexivity.
Qed.

Lemma ccu_sum_expansion : forall (U : Square 2),
  WF_Matrix U -> ccu U = ∣0⟩⟨0∣ ⊗ I 2 ⊗ I 2 .+ ∣1⟩⟨1∣ ⊗ (control U).
Proof.
  intros.
  unfold ccu.
  rewrite control_decomp.
  rewrite kron_assoc, id_kron.
  all: solve_WF_matrix.
Qed.

Lemma swapab_ccu: forall (U: Square 2), WF_Matrix U ->
  swapab × (ccu U) × swapab = ccu U.
Proof.
  intros.
  unfold swapab.
  unfold ccu.
  repeat rewrite control_decomp.
  rewrite kron_plus_distr_l.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite Mmult_plus_distr_r.
  rewrite <- id_kron.
  repeat rewrite <- kron_assoc.
  repeat rewrite (@kron_mixed_product 4 4 4 2 2 2).
  repeat rewrite swap_2gate.
  Msimpl_light.
  rewrite <- Mplus01 at 1 4.
  repeat rewrite kron_assoc.
  repeat rewrite kron_plus_distr_r.
  rewrite kron_plus_distr_l.
  rewrite Mplus_assoc.
  rewrite <- Mplus_assoc with (A := ∣1⟩⟨1∣ ⊗ (∣0⟩⟨0∣ ⊗ I 2)).
  rewrite Mplus_comm with (A := ∣1⟩⟨1∣ ⊗ (∣0⟩⟨0∣ ⊗ I 2)).
  repeat rewrite <- Mplus_assoc.
  all: solve_WF_matrix.
Qed.

Lemma ccu_adjoint: forall (U: Square 2), WF_Matrix U -> (ccu U)† = ccu U†.
Proof.
  intros.
  unfold ccu.
  repeat rewrite control_adjoint.
  reflexivity.
Qed.

Lemma abgate_adjoint: forall (U : Square 4), WF_Matrix U -> (abgate U) † = abgate (U†).
Proof.
  intros.
  unfold abgate.
  rewrite kron_adjoint, id_adjoint_eq.
  reflexivity.
Qed.

Lemma acgate_adjoint: forall (U : Square 4), WF_Matrix U -> 
(acgate U)† = acgate (U†).
Proof.
  intros.
  unfold acgate.
  repeat rewrite Mmult_adjoint.
  repeat rewrite <- swapbc_sa at 1.
  rewrite abgate_adjoint, Mmult_assoc.
  reflexivity.
  assumption.
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

Lemma abgate_control: forall (U W0 W1: Square 4), 
WF_Unitary U -> WF_Unitary W0 -> WF_Unitary W1 -> 
abgate U = ∣0⟩⟨0∣ ⊗ W0 .+ ∣1⟩⟨1∣ ⊗ W1 ->
exists (P0 P1: Square 2), WF_Unitary P0 /\ WF_Unitary P1 /\
abgate U = ∣0⟩⟨0∣ ⊗ P0 ⊗ I 2 .+ ∣1⟩⟨1∣ ⊗ P1 ⊗ I 2.
Proof.
intros U W0 W1 U_unitary W0_unitary W1_unitary abgate_c.
assert (temp: WF_Unitary W0). assumption. 
destruct temp as [WF_W0 W0_inv].
assert (temp: WF_Unitary W1). assumption. 
destruct temp as [WF_W1 W1_inv].
unfold abgate in *.
assert (W0_11: W0 1%nat 1%nat = W0 0%nat 0%nat).
{
    assert (W0 1%nat 1%nat = (U ⊗ I 2) 1%nat 1%nat). rewrite abgate_c. lca.
    assert (W0 0%nat 0%nat = (U ⊗ I 2) 0%nat 0%nat). rewrite abgate_c. lca.
    rewrite H, H0.
    lca.
}
assert (W0_13: W0 1%nat 3%nat = W0 0%nat 2%nat).
{
    assert (W0 1%nat 3%nat = (U ⊗ I 2) 1%nat 3%nat). rewrite abgate_c. lca.
    assert (W0 0%nat 2%nat = (U ⊗ I 2) 0%nat 2%nat). rewrite abgate_c. lca.
    rewrite H, H0.
    lca.
}
assert (W0_31: W0 3%nat 1%nat = W0 2%nat 0%nat).
{
    assert (W0 3%nat 1%nat = (U ⊗ I 2) 3%nat 1%nat). rewrite abgate_c. lca.
    assert (W0 2%nat 0%nat = (U ⊗ I 2) 2%nat 0%nat). rewrite abgate_c. lca.
    rewrite H, H0.
    lca.
}
assert (W0_33: W0 3%nat 3%nat = W0 2%nat 2%nat).
{
    assert (W0 3%nat 3%nat = (U ⊗ I 2) 3%nat 3%nat). rewrite abgate_c. lca.
    assert (W0 2%nat 2%nat = (U ⊗ I 2) 2%nat 2%nat). rewrite abgate_c. lca.
    rewrite H, H0.
    lca.
}
assert (W0_01: W0 0%nat 1%nat = 0).
{
    assert (W0 0%nat 1%nat = (U ⊗ I 2) 0%nat 1%nat). rewrite abgate_c. lca.
    rewrite H. 
    lca.
}
assert (W0_03: W0 0%nat 3%nat = 0).
{
    assert (W0 0%nat 3%nat = (U ⊗ I 2) 0%nat 3%nat). rewrite abgate_c. lca.
    rewrite H. 
    lca.
}
assert (W0_10: W0 1%nat 0%nat = 0).
{
    assert (W0 1%nat 0%nat = (U ⊗ I 2) 1%nat 0%nat). rewrite abgate_c. lca.
    rewrite H. 
    lca.
}
assert (W0_12: W0 1%nat 2%nat = 0).
{
    assert (W0 1%nat 2%nat = (U ⊗ I 2) 1%nat 2%nat). rewrite abgate_c. lca.
    rewrite H. 
    lca.
}
assert (W0_21: W0 2%nat 1%nat = 0).
{
    assert (W0 2%nat 1%nat = (U ⊗ I 2) 2%nat 1%nat). rewrite abgate_c. lca.
    rewrite H. 
    lca.
}
assert (W0_23: W0 2%nat 3%nat = 0).
{
    assert (W0 2%nat 3%nat = (U ⊗ I 2) 2%nat 3%nat). rewrite abgate_c. lca.
    rewrite H. 
    lca.
}
assert (W0_30: W0 3%nat 0%nat = 0).
{
    assert (W0 3%nat 0%nat = (U ⊗ I 2) 3%nat 0%nat). rewrite abgate_c. lca.
    rewrite H. 
    lca.
}
assert (W0_32: W0 3%nat 2%nat = 0).
{
    assert (W0 3%nat 2%nat = (U ⊗ I 2) 3%nat 2%nat). rewrite abgate_c. lca.
    rewrite H. 
    lca.
}
assert (P0_inv_00: (W0 0%nat 0%nat)^* * (W0 0%nat 0%nat) + (W0 2%nat 0%nat)^* * (W0 2%nat 0%nat) = 1).
{
    assert ((W0 0%nat 0%nat) ^* * W0 0%nat 0%nat + (W0 1%nat 0%nat) ^* * W0 1%nat 0%nat +
    (W0 2%nat 0%nat) ^* * W0 2%nat 0%nat + (W0 3%nat 0%nat) ^* * W0 3%nat 0%nat = ((W0) † × W0) 0%nat 0%nat). lca.
    rewrite W0_10 in H.
    rewrite W0_30 in H.
    rewrite Cmult_0_r in H.
    do 2 rewrite Cplus_0_r in H.
    rewrite H.
    rewrite W0_inv.
    lca.
}
assert (P0_inv_01: (W0 0%nat 0%nat)^* * (W0 0%nat 2%nat) + (W0 2%nat 0%nat)^* * (W0 2%nat 2%nat) = 0).
{
    assert ((W0 0%nat 0%nat) ^* * W0 0%nat 2%nat + (W0 1%nat 0%nat) ^* * W0 1%nat 2%nat +
    (W0 2%nat 0%nat) ^* * W0 2%nat 2%nat + (W0 3%nat 0%nat) ^* * W0 3%nat 2%nat = ((W0) † × W0) 0%nat 2%nat). lca.
    rewrite W0_10 in H.
    rewrite W0_30 in H.
    rewrite Cconj_0 in H.
    do 2 rewrite Cmult_0_l in H.
    do 2 rewrite Cplus_0_r in H.
    rewrite H.
    rewrite W0_inv.
    lca.
}
assert (P0_inv_10: (W0 0%nat 2%nat)^* * (W0 0%nat 0%nat) + (W0 2%nat 2%nat)^* * (W0 2%nat 0%nat) = 0).
{
    assert ((W0 0%nat 2%nat) ^* * W0 0%nat 0%nat + (W0 1%nat 2%nat) ^* * W0 1%nat 0%nat +
    (W0 2%nat 2%nat) ^* * W0 2%nat 0%nat + (W0 3%nat 2%nat) ^* * W0 3%nat 0%nat = ((W0) † × W0) 2%nat 0%nat). lca.
    rewrite W0_10 in H.
    rewrite W0_30 in H.
    rewrite Cmult_0_r in H.
    rewrite Cmult_0_r in H.
    do 2 rewrite Cplus_0_r in H.
    rewrite H.
    rewrite W0_inv.
    lca.
}
assert (P0_inv_11: (W0 0%nat 2%nat)^* * (W0 0%nat 2%nat) + (W0 2%nat 2%nat)^* * (W0 2%nat 2%nat) = 1).
{
    assert ((W0 0%nat 2%nat) ^* * W0 0%nat 2%nat + (W0 1%nat 2%nat) ^* * W0 1%nat 2%nat +
    (W0 2%nat 2%nat) ^* * W0 2%nat 2%nat + (W0 3%nat 2%nat) ^* * W0 3%nat 2%nat = ((W0) † × W0) 2%nat 2%nat). lca.
    rewrite W0_12 in H.
    rewrite W0_32 in H.
    rewrite Cmult_0_r in H.
    do 2 rewrite Cplus_0_r in H.
    rewrite H.
    rewrite W0_inv.
    lca.
}
set (P0 := (fun x y => match (x,y) with
| (0,0) => W0 0%nat 0%nat
| (0,1) => W0 0%nat 2%nat
| (1,0) => W0 2%nat 0%nat
| (1,1) => W0 2%nat 2%nat
| _ => 0
end) : Square 2).
assert (WF_P0: WF_Matrix P0).
{
    unfold WF_Matrix.
    intros.
    unfold P0.
    destruct H.
    {
        destruct x as [| x'].
        contradict H. lia.
        destruct x' as [|x].
        contradict H. lia. reflexivity.
    }
    {
        destruct x as [| x'].
        destruct y as [|y']. contradict H. lia.
        destruct y' as [|y]. contradict H. lia. reflexivity.
        destruct x' as [|x].
        destruct y as [|y']. contradict H. lia.
        destruct y' as [|y]. contradict H. lia. reflexivity. reflexivity.
    }
}
assert (P0_unitary: WF_Unitary P0).
{
    split. assumption.
    lma'.
    assert (unfold_help: ((P0) † × P0) 0%nat 0%nat = (P0 0%nat 0%nat) ^* * P0 0%nat 0%nat +
    (P0 1%nat 0%nat) ^* * P0 1%nat 0%nat). lca.
    rewrite unfold_help. unfold P0. rewrite P0_inv_00. lca.
    assert (unfold_help: ((P0) † × P0) 0%nat 1%nat = (P0 0%nat 0%nat) ^* * P0 0%nat 1%nat +
    (P0 1%nat 0%nat) ^* * P0 1%nat 1%nat). lca.
    rewrite unfold_help. unfold P0. rewrite P0_inv_01. lca. 
    assert (unfold_help: ((P0) † × P0) 1%nat 0%nat = (P0 0%nat 1%nat) ^* * P0 0%nat 0%nat +
    (P0 1%nat 1%nat) ^* * P0 1%nat 0%nat). lca.
    rewrite unfold_help. unfold P0. rewrite P0_inv_10. lca.
    assert (unfold_help: ((P0) † × P0) 1%nat 1%nat = (P0 0%nat 1%nat) ^* * P0 0%nat 1%nat +
    (P0 1%nat 1%nat) ^* * P0 1%nat 1%nat). lca.
    rewrite unfold_help. unfold P0. rewrite P0_inv_11. lca. 
}
assert (P0_tens_W0: P0 ⊗ I 2 = W0).
{
    lma'.
    unfold kron, P0. simpl. lca.
    rewrite W0_01. lca.
    unfold kron, P0. simpl. lca.
    rewrite W0_03. lca.
    rewrite W0_10. lca.
    unfold kron, P0. simpl. rewrite W0_11. lca.
    rewrite W0_12. lca.
    unfold kron, P0. simpl. rewrite W0_13. lca.
    unfold kron, P0. simpl. lca.
    rewrite W0_21. lca.
    unfold kron, P0. simpl. lca.
    rewrite W0_23. lca.
    rewrite W0_30. lca.
    unfold kron, P0. simpl. rewrite W0_31. lca.
    rewrite W0_32. lca.
    unfold kron, P0. simpl. rewrite W0_33. lca.
}
assert (W1_11: W1 1%nat 1%nat = W1 0%nat 0%nat).
{
    assert (W1 1%nat 1%nat = (U ⊗ I 2) 5%nat 5%nat). rewrite abgate_c. lca.
    assert (W1 0%nat 0%nat = (U ⊗ I 2) 4%nat 4%nat). rewrite abgate_c. lca.
    rewrite H, H0.
    lca.
}
assert (W1_13: W1 1%nat 3%nat = W1 0%nat 2%nat).
{
    assert (W1 1%nat 3%nat = (U ⊗ I 2) 5%nat 7%nat). rewrite abgate_c. lca.
    assert (W1 0%nat 2%nat = (U ⊗ I 2) 4%nat 6%nat). rewrite abgate_c. lca.
    rewrite H, H0.
    lca.
}
assert (W1_31: W1 3%nat 1%nat = W1 2%nat 0%nat).
{
    assert (W1 3%nat 1%nat = (U ⊗ I 2) 7%nat 5%nat). rewrite abgate_c. lca.
    assert (W1 2%nat 0%nat = (U ⊗ I 2) 6%nat 4%nat). rewrite abgate_c. lca.
    rewrite H, H0.
    lca.
}
assert (W1_33: W1 3%nat 3%nat = W1 2%nat 2%nat).
{
    assert (W1 3%nat 3%nat = (U ⊗ I 2) 7%nat 7%nat). rewrite abgate_c. lca.
    assert (W1 2%nat 2%nat = (U ⊗ I 2) 6%nat 6%nat). rewrite abgate_c. lca.
    rewrite H, H0.
    lca.
}
assert (W1_01: W1 0%nat 1%nat = 0).
{
    assert (W1 0%nat 1%nat = (U ⊗ I 2) 4%nat 5%nat). rewrite abgate_c. lca.
    rewrite H. 
    lca.
}
assert (W1_03: W1 0%nat 3%nat = 0).
{
    assert (W1 0%nat 3%nat = (U ⊗ I 2) 4%nat 7%nat). rewrite abgate_c. lca.
    rewrite H. 
    lca.
}
assert (W1_10: W1 1%nat 0%nat = 0).
{
    assert (W1 1%nat 0%nat = (U ⊗ I 2) 5%nat 4%nat). rewrite abgate_c. lca.
    rewrite H. 
    lca.
}
assert (W1_12: W1 1%nat 2%nat = 0).
{
    assert (W1 1%nat 2%nat = (U ⊗ I 2) 5%nat 6%nat). rewrite abgate_c. lca.
    rewrite H. 
    lca.
}
assert (W1_21: W1 2%nat 1%nat = 0).
{
    assert (W1 2%nat 1%nat = (U ⊗ I 2) 6%nat 5%nat). rewrite abgate_c. lca.
    rewrite H. 
    lca.
}
assert (W1_23: W1 2%nat 3%nat = 0).
{
    assert (W1 2%nat 3%nat = (U ⊗ I 2) 6%nat 7%nat). rewrite abgate_c. lca.
    rewrite H. 
    lca.
}
assert (W1_30: W1 3%nat 0%nat = 0).
{
    assert (W1 3%nat 0%nat = (U ⊗ I 2) 7%nat 4%nat). rewrite abgate_c. lca.
    rewrite H. 
    lca.
}
assert (W1_32: W1 3%nat 2%nat = 0).
{
    assert (W1 3%nat 2%nat = (U ⊗ I 2) 7%nat 6%nat). rewrite abgate_c. lca.
    rewrite H. 
    lca.
}
assert (P1_inv_00: (W1 0%nat 0%nat)^* * (W1 0%nat 0%nat) + (W1 2%nat 0%nat)^* * (W1 2%nat 0%nat) = 1).
{
    assert ((W1 0%nat 0%nat) ^* * W1 0%nat 0%nat + (W1 1%nat 0%nat) ^* * W1 1%nat 0%nat +
    (W1 2%nat 0%nat) ^* * W1 2%nat 0%nat + (W1 3%nat 0%nat) ^* * W1 3%nat 0%nat = ((W1) † × W1) 0%nat 0%nat). lca.
    rewrite W1_10 in H.
    rewrite W1_30 in H.
    rewrite Cmult_0_r in H.
    do 2 rewrite Cplus_0_r in H.
    rewrite H.
    rewrite W1_inv.
    lca.
}
assert (P1_inv_01: (W1 0%nat 0%nat)^* * (W1 0%nat 2%nat) + (W1 2%nat 0%nat)^* * (W1 2%nat 2%nat) = 0).
{
    assert ((W1 0%nat 0%nat) ^* * W1 0%nat 2%nat + (W1 1%nat 0%nat) ^* * W1 1%nat 2%nat +
    (W1 2%nat 0%nat) ^* * W1 2%nat 2%nat + (W1 3%nat 0%nat) ^* * W1 3%nat 2%nat = ((W1) † × W1) 0%nat 2%nat). lca.
    rewrite W1_10 in H.
    rewrite W1_30 in H.
    rewrite Cconj_0 in H.
    do 2 rewrite Cmult_0_l in H.
    do 2 rewrite Cplus_0_r in H.
    rewrite H.
    rewrite W1_inv.
    lca.
}
assert (P1_inv_10: (W1 0%nat 2%nat)^* * (W1 0%nat 0%nat) + (W1 2%nat 2%nat)^* * (W1 2%nat 0%nat) = 0).
{
    assert ((W1 0%nat 2%nat) ^* * W1 0%nat 0%nat + (W1 1%nat 2%nat) ^* * W1 1%nat 0%nat +
    (W1 2%nat 2%nat) ^* * W1 2%nat 0%nat + (W1 3%nat 2%nat) ^* * W1 3%nat 0%nat = ((W1) † × W1) 2%nat 0%nat). lca.
    rewrite W1_10 in H.
    rewrite W1_30 in H.
    rewrite Cmult_0_r in H.
    rewrite Cmult_0_r in H.
    do 2 rewrite Cplus_0_r in H.
    rewrite H.
    rewrite W1_inv.
    lca.
}
assert (P1_inv_11: (W1 0%nat 2%nat)^* * (W1 0%nat 2%nat) + (W1 2%nat 2%nat)^* * (W1 2%nat 2%nat) = 1).
{
    assert ((W1 0%nat 2%nat) ^* * W1 0%nat 2%nat + (W1 1%nat 2%nat) ^* * W1 1%nat 2%nat +
    (W1 2%nat 2%nat) ^* * W1 2%nat 2%nat + (W1 3%nat 2%nat) ^* * W1 3%nat 2%nat = ((W1) † × W1) 2%nat 2%nat). lca.
    rewrite W1_12 in H.
    rewrite W1_32 in H.
    rewrite Cmult_0_r in H.
    do 2 rewrite Cplus_0_r in H.
    rewrite H.
    rewrite W1_inv.
    lca.
}
set (P1 := (fun x y => match (x,y) with
| (0,0) => W1 0%nat 0%nat
| (0,1) => W1 0%nat 2%nat
| (1,0) => W1 2%nat 0%nat
| (1,1) => W1 2%nat 2%nat
| _ => 0
end) : Square 2).
assert (WF_P1: WF_Matrix P1).
{
    unfold WF_Matrix.
    intros.
    unfold P1.
    destruct H.
    {
        destruct x as [| x'].
        contradict H. lia.
        destruct x' as [|x].
        contradict H. lia. reflexivity.
    }
    {
        destruct x as [| x'].
        destruct y as [|y']. contradict H. lia.
        destruct y' as [|y]. contradict H. lia. reflexivity.
        destruct x' as [|x].
        destruct y as [|y']. contradict H. lia.
        destruct y' as [|y]. contradict H. lia. reflexivity. reflexivity.
    }
}
assert (P1_unitary: WF_Unitary P1).
{
    split. assumption.
    lma'.
    assert (unfold_help: ((P1) † × P1) 0%nat 0%nat = (P1 0%nat 0%nat) ^* * P1 0%nat 0%nat +
    (P1 1%nat 0%nat) ^* * P1 1%nat 0%nat). lca.
    rewrite unfold_help. unfold P1. rewrite P1_inv_00. lca.
    assert (unfold_help: ((P1) † × P1) 0%nat 1%nat = (P1 0%nat 0%nat) ^* * P1 0%nat 1%nat +
    (P1 1%nat 0%nat) ^* * P1 1%nat 1%nat). lca.
    rewrite unfold_help. unfold P1. rewrite P1_inv_01. lca. 
    assert (unfold_help: ((P1) † × P1) 1%nat 0%nat = (P1 0%nat 1%nat) ^* * P1 0%nat 0%nat +
    (P1 1%nat 1%nat) ^* * P1 1%nat 0%nat). lca.
    rewrite unfold_help. unfold P1. rewrite P1_inv_10. lca.
    assert (unfold_help: ((P1) † × P1) 1%nat 1%nat = (P1 0%nat 1%nat) ^* * P1 0%nat 1%nat +
    (P1 1%nat 1%nat) ^* * P1 1%nat 1%nat). lca.
    rewrite unfold_help. unfold P1. rewrite P1_inv_11. lca. 
}
assert (P1_tens_W1: P1 ⊗ I 2 = W1).
{
    lma'.
    unfold kron, P1. simpl. lca.
    rewrite W1_01. lca.
    unfold kron, P1. simpl. lca.
    rewrite W1_03. lca.
    rewrite W1_10. lca.
    unfold kron, P1. simpl. rewrite W1_11. lca.
    rewrite W1_12. lca.
    unfold kron, P1. simpl. rewrite W1_13. lca.
    unfold kron, P1. simpl. lca.
    rewrite W1_21. lca.
    unfold kron, P1. simpl. lca.
    rewrite W1_23. lca.
    rewrite W1_30. lca.
    unfold kron, P1. simpl. rewrite W1_31. lca.
    rewrite W1_32. lca.
    unfold kron, P1. simpl. rewrite W1_33. lca.
}
exists P0, P1.
split. assumption.
split. assumption.
rewrite kron_assoc. 2,3,4: solve_WF_matrix.
rewrite kron_assoc. 2,3,4: solve_WF_matrix.
rewrite P0_tens_W0. rewrite P1_tens_W1.
apply abgate_c.
Qed.

Lemma acgate_control: forall (U W0 W1: Square 4), 
WF_Unitary U -> WF_Unitary W0 -> WF_Unitary W1 -> 
acgate U = ∣0⟩⟨0∣ ⊗ W0 .+ ∣1⟩⟨1∣ ⊗ W1 ->
exists (P0 P1: Square 2), WF_Unitary P0 /\ WF_Unitary P1 /\
acgate U = ∣0⟩⟨0∣ ⊗ I 2 ⊗ P0 .+ ∣1⟩⟨1∣ ⊗ I 2 ⊗ P1.
Proof.
intros U W0 W1 U_unitary W0_unitary W1_unitary acgate_c.
assert (temp: WF_Unitary U). assumption.
destruct temp as [WF_U U_inv].
unfold acgate in acgate_c.
apply (f_equal (fun f => swapbc × f)) in acgate_c.
repeat rewrite <- Mmult_assoc in acgate_c.
rewrite swapbc_inverse in acgate_c. rewrite Mmult_1_l in acgate_c. 2: apply WF_abgate; solve_WF_matrix.
rewrite Mmult_plus_distr_l in acgate_c.
unfold swapbc in acgate_c at 2. rewrite (@kron_mixed_product 2 2 2 4 4 4) in acgate_c.
unfold swapbc in acgate_c at 2. rewrite (@kron_mixed_product 2 2 2 4 4 4) in acgate_c.
rewrite Mmult_1_l in acgate_c. 2: solve_WF_matrix.
rewrite Mmult_1_l in acgate_c. 2: solve_WF_matrix.
apply (f_equal (fun f => f × swapbc)) in acgate_c.
rewrite Mmult_assoc in acgate_c.
rewrite swapbc_inverse in acgate_c at 1. rewrite Mmult_1_r in acgate_c. 2: apply WF_abgate; solve_WF_matrix.
rewrite Mmult_plus_distr_r in acgate_c.
unfold swapbc in acgate_c at 2. rewrite (@kron_mixed_product 2 2 2 4 4 4) in acgate_c.
unfold swapbc in acgate_c at 1. rewrite (@kron_mixed_product 2 2 2 4 4 4) in acgate_c.
rewrite Mmult_1_r in acgate_c. 2: solve_WF_matrix.
rewrite Mmult_1_r in acgate_c. 2: solve_WF_matrix.
assert (swapW0_unit: WF_Unitary (swap × W0 × swap)). 
{
    apply Mmult_unitary. apply Mmult_unitary.
    apply swap_unitary. assumption. apply swap_unitary.
}
assert (swapW1_unit: WF_Unitary (swap × W1 × swap)). 
{
    apply Mmult_unitary. apply Mmult_unitary.
    apply swap_unitary. assumption. apply swap_unitary.
}
assert (abgate_control_partial := abgate_control U (swap × W0 × swap) (swap × W1 × swap) U_unitary
swapW0_unit swapW1_unit acgate_c).
destruct abgate_control_partial as [P0 [P1 [P0_unitary [P1_unitary abgate_prop]]]].
exists P0,P1.
split. assumption.
split. assumption.
unfold acgate.
rewrite abgate_prop.
destruct P0_unitary as [WF_P0 P0_inv].
destruct P1_unitary as [WF_P1 P1_inv].
rewrite Mmult_plus_distr_l.
rewrite Mmult_plus_distr_r.
rewrite swapbc_3gate; solve_WF_matrix.
rewrite swapbc_3gate; solve_WF_matrix.
Qed.

Lemma abgate_0prop_bottomleft_0block: forall (U: Square 4), 
WF_Unitary U -> (exists (y: Vector 2), WF_Qubit y /\ 
forall (x : Vector 2), WF_Qubit x -> (exists (phi: Vector 4), WF_Matrix phi /\
(abgate U) × (∣0⟩ ⊗ x ⊗ y)  =  ∣0⟩ ⊗ phi)) -> exists (TL TR BR: Square 4), 
WF_Matrix TL /\ WF_Matrix TR /\ WF_Matrix BR /\
abgate U = ∣0⟩⟨0∣ ⊗ TL .+ ∣0⟩⟨1∣ ⊗ TR .+ ∣1⟩⟨1∣ ⊗ BR.
Proof.
intros U U_unitary zeropassthrough.
destruct zeropassthrough as [y [WF_y zeropassthrough]].
destruct (@block_decomp 2 U) as [TL [TR [BL [BR [WF_TL [WF_TR [WF_BL [WF_BR decomp]]]]]]]].
apply U_unitary.
exists (TL ⊗ I 2), (TR ⊗ I 2), (BR ⊗ I 2).
split. solve_WF_matrix.
split. solve_WF_matrix.
split. solve_WF_matrix.
assert (abgate_decomp: abgate U = ∣0⟩⟨0∣ ⊗ (TL ⊗ I 2) .+ ∣0⟩⟨1∣ ⊗ (TR ⊗ I 2) .+ ∣1⟩⟨0∣ ⊗ (BL ⊗ I 2)
.+ ∣1⟩⟨1∣ ⊗ (BR ⊗ I 2)).
{
    rewrite decomp.   
    unfold abgate.
    repeat rewrite kron_plus_distr_r.
    repeat rewrite kron_assoc.
    reflexivity.
    all: solve_WF_matrix.
}
assert (goal_change: BL = Zero -> abgate U = ∣0⟩⟨0∣ ⊗ (TL ⊗ I 2) .+ ∣0⟩⟨1∣ ⊗ (TR ⊗ I 2)
 .+ ∣1⟩⟨1∣ ⊗ (BR ⊗ I 2)).
{
    intros.
    rewrite abgate_decomp.
    rewrite H.
    rewrite kron_0_l. rewrite kron_0_r.
    rewrite Mplus_0_r.
    reflexivity.
}
apply goal_change. clear goal_change.
assert (zerotens_040: forall (y0: Vector 2), (∣0⟩ ⊗ ∣0⟩ ⊗ y0) 4%nat 0%nat = 0). intros. lca.
assert (zerotens_050: forall (y0: Vector 2), (∣0⟩ ⊗ ∣0⟩ ⊗ y0) 5%nat 0%nat = 0). intros. lca.
assert (zerotens_060: forall (y0: Vector 2), (∣0⟩ ⊗ ∣0⟩ ⊗ y0) 6%nat 0%nat = 0). intros. lca.
assert (zerotens_070: forall (y0: Vector 2), (∣0⟩ ⊗ ∣0⟩ ⊗ y0) 7%nat 0%nat = 0). intros. lca.
assert (zerotens_140: forall (y0: Vector 2), (∣0⟩ ⊗ ∣1⟩ ⊗ y0) 4%nat 0%nat = 0). intros. lca.
assert (zerotens_150: forall (y0: Vector 2), (∣0⟩ ⊗ ∣1⟩ ⊗ y0) 5%nat 0%nat = 0). intros. lca.
assert (zerotens_160: forall (y0: Vector 2), (∣0⟩ ⊗ ∣1⟩ ⊗ y0) 6%nat 0%nat = 0). intros. lca.
assert (zerotens_170: forall (y0: Vector 2), (∣0⟩ ⊗ ∣1⟩ ⊗ y0) 7%nat 0%nat = 0). intros. lca.
assert (case000_goal_change: forall (U: Square 4) (y: Vector 2), 
(∣0⟩ ⊗ ∣0⟩ ⊗ y) 2%nat 0%nat = 0 -> (∣0⟩ ⊗ ∣0⟩ ⊗ y) 3%nat 0%nat = 0 ->
(∣0⟩ ⊗ ∣0⟩ ⊗ y) 0%nat 0%nat <> 0 -> (abgate U) 4%nat 0%nat <> 0 -> 
(abgate U) 4%nat 1%nat = 0 -> (abgate U × (∣0⟩ ⊗ ∣0⟩ ⊗ y)) 4%nat 0%nat <> 0).
{
    intros.
    replace ((abgate U0 × (∣0⟩ ⊗ ∣0⟩ ⊗ y0)) 4%nat 0%nat) with (
        (abgate U0 4%nat 0%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 0%nat 0%nat) + 
        (abgate U0 4%nat 1%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 1%nat 0%nat) + 
        (abgate U0 4%nat 2%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 2%nat 0%nat) + 
        (abgate U0 4%nat 3%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 3%nat 0%nat) + 
        (abgate U0 4%nat 4%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 4%nat 0%nat) + 
        (abgate U0 4%nat 5%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 5%nat 0%nat) + 
        (abgate U0 4%nat 6%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 6%nat 0%nat) + 
        (abgate U0 4%nat 7%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 7%nat 0%nat)
    ) by lca.
    rewrite H, H0, H3, zerotens_040, zerotens_050, zerotens_060, zerotens_070.
    Csimpl.
    apply Cmult_neq_0.
    all: assumption.
}
assert (case000_el_eq: abgate U 4%nat 0%nat = BL 0%nat 0%nat).
{
    rewrite abgate_decomp.
    repeat rewrite Mplus_access.
    unfold kron, Mmult, adjoint, qubit0, qubit1, I; simpl.
    lca.
}
assert (case001_goal_change: forall (U: Square 4) (y: Vector 2), 
(∣0⟩ ⊗ ∣0⟩ ⊗ y) 2%nat 0%nat = 0 -> (∣0⟩ ⊗ ∣0⟩ ⊗ y) 3%nat 0%nat = 0 ->
(∣0⟩ ⊗ ∣0⟩ ⊗ y) 1%nat 0%nat <> 0 -> (abgate U) 5%nat 1%nat <> 0 -> 
(abgate U) 5%nat 0%nat = 0 -> (abgate U × (∣0⟩ ⊗ ∣0⟩ ⊗ y)) 5%nat 0%nat <> 0).
{
    intros.
    replace ((abgate U0 × (∣0⟩ ⊗ ∣0⟩ ⊗ y0)) 5%nat 0%nat) with (
        (abgate U0 5%nat 0%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 0%nat 0%nat) + 
        (abgate U0 5%nat 1%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 1%nat 0%nat) + 
        (abgate U0 5%nat 2%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 2%nat 0%nat) + 
        (abgate U0 5%nat 3%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 3%nat 0%nat) + 
        (abgate U0 5%nat 4%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 4%nat 0%nat) + 
        (abgate U0 5%nat 5%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 5%nat 0%nat) + 
        (abgate U0 5%nat 6%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 6%nat 0%nat) + 
        (abgate U0 5%nat 7%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 7%nat 0%nat)
    ) by lca.
    rewrite H, H0, H3, zerotens_040, zerotens_050, zerotens_060, zerotens_070.
    Csimpl.
    apply Cmult_neq_0.
    all: assumption.
}
assert (case001_el_eq: abgate U 5%nat 1%nat = BL 0%nat 0%nat).
{
    rewrite abgate_decomp.
    repeat rewrite Mplus_access.
    unfold kron, Mmult, adjoint, qubit0, qubit1, I; simpl.
    lca.
}
assert (case010_goal_change: forall (U: Square 4) (y: Vector 2), 
(∣0⟩ ⊗ ∣1⟩ ⊗ y) 0%nat 0%nat = 0 -> (∣0⟩ ⊗ ∣1⟩ ⊗ y) 1%nat 0%nat = 0 ->
(∣0⟩ ⊗ ∣1⟩ ⊗ y) 2%nat 0%nat <> 0 -> (abgate U) 4%nat 2%nat <> 0 -> 
(abgate U) 4%nat 3%nat = 0 -> (abgate U × (∣0⟩ ⊗ ∣1⟩ ⊗ y)) 4%nat 0%nat <> 0).
{
    intros.
    replace ((abgate U0 × (∣0⟩ ⊗ ∣1⟩ ⊗ y0)) 4%nat 0%nat) with (
        (abgate U0 4%nat 0%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 0%nat 0%nat) + 
        (abgate U0 4%nat 1%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 1%nat 0%nat) + 
        (abgate U0 4%nat 2%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 2%nat 0%nat) + 
        (abgate U0 4%nat 3%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 3%nat 0%nat) + 
        (abgate U0 4%nat 4%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 4%nat 0%nat) + 
        (abgate U0 4%nat 5%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 5%nat 0%nat) + 
        (abgate U0 4%nat 6%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 6%nat 0%nat) + 
        (abgate U0 4%nat 7%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 7%nat 0%nat)
    ) by lca.
    rewrite H, H0, H3, zerotens_140, zerotens_150, zerotens_160, zerotens_170.
    Csimpl.
    apply Cmult_neq_0.
    all: assumption.
}
assert (case010_el_eq: abgate U 4%nat 2%nat = BL 0%nat 1%nat).
{
    rewrite abgate_decomp.
    repeat rewrite Mplus_access.
    unfold kron, Mmult, adjoint, qubit0, qubit1, I; simpl.
    lca.
}
assert (case011_goal_change: forall (U: Square 4) (y: Vector 2), 
(∣0⟩ ⊗ ∣1⟩ ⊗ y) 0%nat 0%nat = 0 -> (∣0⟩ ⊗ ∣1⟩ ⊗ y) 1%nat 0%nat = 0 ->
(∣0⟩ ⊗ ∣1⟩ ⊗ y) 3%nat 0%nat <> 0 -> (abgate U) 5%nat 3%nat <> 0 -> 
(abgate U) 5%nat 2%nat = 0 -> (abgate U × (∣0⟩ ⊗ ∣1⟩ ⊗ y)) 5%nat 0%nat <> 0).
{
    intros.
    replace ((abgate U0 × (∣0⟩ ⊗ ∣1⟩ ⊗ y0)) 5%nat 0%nat) with (
        (abgate U0 5%nat 0%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 0%nat 0%nat) + 
        (abgate U0 5%nat 1%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 1%nat 0%nat) + 
        (abgate U0 5%nat 2%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 2%nat 0%nat) + 
        (abgate U0 5%nat 3%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 3%nat 0%nat) + 
        (abgate U0 5%nat 4%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 4%nat 0%nat) + 
        (abgate U0 5%nat 5%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 5%nat 0%nat) + 
        (abgate U0 5%nat 6%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 6%nat 0%nat) + 
        (abgate U0 5%nat 7%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 7%nat 0%nat)
    ) by lca.
    rewrite H, H0, H3, zerotens_140, zerotens_150, zerotens_160, zerotens_170.
    Csimpl.
    apply Cmult_neq_0.
    all: assumption.
}
assert (case011_el_eq: abgate U 5%nat 3%nat = BL 0%nat 1%nat).
{
    rewrite abgate_decomp.
    repeat rewrite Mplus_access.
    unfold kron, Mmult, adjoint, qubit0, qubit1, I; simpl.
    lca.
}
assert (case100_goal_change: forall (U: Square 4) (y: Vector 2), 
(∣0⟩ ⊗ ∣0⟩ ⊗ y) 2%nat 0%nat = 0 -> (∣0⟩ ⊗ ∣0⟩ ⊗ y) 3%nat 0%nat = 0 ->
(∣0⟩ ⊗ ∣0⟩ ⊗ y) 0%nat 0%nat <> 0 -> (abgate U) 6%nat 0%nat <> 0 -> 
(abgate U) 6%nat 1%nat = 0 -> (abgate U × (∣0⟩ ⊗ ∣0⟩ ⊗ y)) 6%nat 0%nat <> 0).
{
    intros.
    replace ((abgate U0 × (∣0⟩ ⊗ ∣0⟩ ⊗ y0)) 6%nat 0%nat) with (
        (abgate U0 6%nat 0%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 0%nat 0%nat) + 
        (abgate U0 6%nat 1%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 1%nat 0%nat) + 
        (abgate U0 6%nat 2%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 2%nat 0%nat) + 
        (abgate U0 6%nat 3%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 3%nat 0%nat) + 
        (abgate U0 6%nat 4%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 4%nat 0%nat) + 
        (abgate U0 6%nat 5%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 5%nat 0%nat) + 
        (abgate U0 6%nat 6%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 6%nat 0%nat) + 
        (abgate U0 6%nat 7%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 7%nat 0%nat)
    ) by lca.
    rewrite H, H0, H3, zerotens_040, zerotens_050, zerotens_060, zerotens_070.
    Csimpl.
    apply Cmult_neq_0.
    all: assumption.
}
assert (case100_el_eq: abgate U 6%nat 0%nat = BL 1%nat 0%nat).
{
    rewrite abgate_decomp.
    repeat rewrite Mplus_access.
    unfold kron, Mmult, adjoint, qubit0, qubit1, I; simpl.
    lca.
}
assert (case101_goal_change: forall (U: Square 4) (y: Vector 2), 
(∣0⟩ ⊗ ∣0⟩ ⊗ y) 2%nat 0%nat = 0 -> (∣0⟩ ⊗ ∣0⟩ ⊗ y) 3%nat 0%nat = 0 ->
(∣0⟩ ⊗ ∣0⟩ ⊗ y) 1%nat 0%nat <> 0 -> (abgate U) 7%nat 1%nat <> 0 -> 
(abgate U) 7%nat 0%nat = 0 -> (abgate U × (∣0⟩ ⊗ ∣0⟩ ⊗ y)) 7%nat 0%nat <> 0).
{
    intros.
    replace ((abgate U0 × (∣0⟩ ⊗ ∣0⟩ ⊗ y0)) 7%nat 0%nat) with (
        (abgate U0 7%nat 0%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 0%nat 0%nat) + 
        (abgate U0 7%nat 1%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 1%nat 0%nat) + 
        (abgate U0 7%nat 2%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 2%nat 0%nat) + 
        (abgate U0 7%nat 3%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 3%nat 0%nat) + 
        (abgate U0 7%nat 4%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 4%nat 0%nat) + 
        (abgate U0 7%nat 5%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 5%nat 0%nat) + 
        (abgate U0 7%nat 6%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 6%nat 0%nat) + 
        (abgate U0 7%nat 7%nat) * ((∣0⟩ ⊗ ∣0⟩ ⊗ y0) 7%nat 0%nat)
    ) by lca.
    rewrite H, H0, H3, zerotens_040, zerotens_050, zerotens_060, zerotens_070.
    Csimpl.
    apply Cmult_neq_0.
    all: assumption.
}
assert (case101_el_eq: abgate U 7%nat 1%nat = BL 1%nat 0%nat).
{
    rewrite abgate_decomp.
    repeat rewrite Mplus_access.
    unfold kron, Mmult, adjoint, qubit0, qubit1, I; simpl.
    lca.
}
assert (case110_goal_change: forall (U: Square 4) (y: Vector 2), 
(∣0⟩ ⊗ ∣1⟩ ⊗ y) 0%nat 0%nat = 0 -> (∣0⟩ ⊗ ∣1⟩ ⊗ y) 1%nat 0%nat = 0 ->
(∣0⟩ ⊗ ∣1⟩ ⊗ y) 2%nat 0%nat <> 0 -> (abgate U) 6%nat 2%nat <> 0 -> 
(abgate U) 6%nat 3%nat = 0 -> (abgate U × (∣0⟩ ⊗ ∣1⟩ ⊗ y)) 6%nat 0%nat <> 0).
{
    intros.
    replace ((abgate U0 × (∣0⟩ ⊗ ∣1⟩ ⊗ y0)) 6%nat 0%nat) with (
        (abgate U0 6%nat 0%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 0%nat 0%nat) + 
        (abgate U0 6%nat 1%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 1%nat 0%nat) + 
        (abgate U0 6%nat 2%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 2%nat 0%nat) + 
        (abgate U0 6%nat 3%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 3%nat 0%nat) + 
        (abgate U0 6%nat 4%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 4%nat 0%nat) + 
        (abgate U0 6%nat 5%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 5%nat 0%nat) + 
        (abgate U0 6%nat 6%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 6%nat 0%nat) + 
        (abgate U0 6%nat 7%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 7%nat 0%nat)
    ) by lca.
    rewrite H, H0, H3, zerotens_140, zerotens_150, zerotens_160, zerotens_170.
    Csimpl.
    apply Cmult_neq_0.
    all: assumption.
}
assert (case110_el_eq: abgate U 6%nat 2%nat = BL 1%nat 1%nat).
{
    rewrite abgate_decomp.
    repeat rewrite Mplus_access.
    unfold kron, Mmult, adjoint, qubit0, qubit1, I; simpl.
    lca.
}
assert (case111_goal_change: forall (U: Square 4) (y: Vector 2), 
(∣0⟩ ⊗ ∣1⟩ ⊗ y) 0%nat 0%nat = 0 -> (∣0⟩ ⊗ ∣1⟩ ⊗ y) 1%nat 0%nat = 0 ->
(∣0⟩ ⊗ ∣1⟩ ⊗ y) 3%nat 0%nat <> 0 -> (abgate U) 7%nat 3%nat <> 0 -> 
(abgate U) 7%nat 2%nat = 0 -> (abgate U × (∣0⟩ ⊗ ∣1⟩ ⊗ y)) 7%nat 0%nat <> 0).
{
    intros.
    replace ((abgate U0 × (∣0⟩ ⊗ ∣1⟩ ⊗ y0)) 7%nat 0%nat) with (
        (abgate U0 7%nat 0%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 0%nat 0%nat) + 
        (abgate U0 7%nat 1%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 1%nat 0%nat) + 
        (abgate U0 7%nat 2%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 2%nat 0%nat) + 
        (abgate U0 7%nat 3%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 3%nat 0%nat) + 
        (abgate U0 7%nat 4%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 4%nat 0%nat) + 
        (abgate U0 7%nat 5%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 5%nat 0%nat) + 
        (abgate U0 7%nat 6%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 6%nat 0%nat) + 
        (abgate U0 7%nat 7%nat) * ((∣0⟩ ⊗ ∣1⟩ ⊗ y0) 7%nat 0%nat)
    ) by lca.
    rewrite H, H0, H3, zerotens_140, zerotens_150, zerotens_160, zerotens_170.
    Csimpl.
    apply Cmult_neq_0.
    all: assumption.
}
assert (case111_el_eq: abgate U 7%nat 3%nat = BL 1%nat 1%nat).
{
    rewrite abgate_decomp.
    repeat rewrite Mplus_access.
    unfold kron, Mmult, adjoint, qubit0, qubit1, I; simpl.
    lca.
}
assert (cntrps: not (BL = Zero) -> not (forall x : Vector 2,
WF_Qubit x -> exists phi : Vector 4,
WF_Matrix phi /\ abgate U × (∣0⟩ ⊗ x ⊗ y) = ∣0⟩ ⊗ phi)).
{
    intros BLn0.
    apply Coq.Logic.Classical_Pred_Type.ex_not_not_all.
    rewrite nonzero_def in BLn0.
    destruct BLn0 as [i [j n0point]].
    assert (y <> Zero). apply qubit_implies_nonzero. apply WF_y.
    assert (yeln0: (y 0%nat 0%nat) <> 0 \/ (y 1%nat 0%nat) <> 0).
    {
        apply Coq.Logic.Classical_Prop.not_and_or.
        unfold not.
        intro.
        apply H.
        destruct H0.
        lma'. apply WF_y.
        rewrite H0. lca.
        rewrite H1. lca.
    }
    destruct (le_lt_dec 2 i).
    {
        contradict n0point.
        rewrite WF_BL. reflexivity.
        left. lia.   
    }
    {
        destruct (le_lt_dec 1 i).
        {
            assert (ival := nat_tight_bound 1 i l0 l).
            destruct (le_lt_dec 2 j).
            {
                contradict n0point.
                rewrite WF_BL. reflexivity.
                right. lia.
            }
            {
                destruct (le_lt_dec 1 j).
                {
                    assert (jval := nat_tight_bound 1 j l2 l1).
                    destruct yeln0.
                    {
                        exists ∣1⟩.
                        rewrite implication_decomp.
                        apply Coq.Logic.Classical_Prop.and_not_or.
                        split. 
                        unfold not.
                        intro. apply H1. apply qubit1_qubit.
                        apply Coq.Logic.Classical_Pred_Type.all_not_not_ex.
                        intros.
                        apply Coq.Logic.Classical_Prop.or_not_and.
                        rewrite <- implication_decomp.
                        apply qubit_not_0tens. lia. solve_WF_matrix.
                        exists 6%nat.
                        split. lia.
                        apply case110_goal_change.
                        lca. lca.
                        replace ((∣0⟩ ⊗ ∣1⟩ ⊗ y) 2%nat 0%nat) with (y 0%nat 0%nat) by lca.
                        assumption.
                        replace (abgate U 6%nat 2%nat) with (BL 1%nat 1%nat).
                        rewrite ival at 1. rewrite jval. assumption. lca.
                    }
                    {
                        exists ∣1⟩.
                        rewrite implication_decomp.
                        apply Coq.Logic.Classical_Prop.and_not_or.
                        split. 
                        unfold not.
                        intro. apply H1. apply qubit1_qubit.
                        apply Coq.Logic.Classical_Pred_Type.all_not_not_ex.
                        intros.
                        apply Coq.Logic.Classical_Prop.or_not_and.
                        rewrite <- implication_decomp.
                        apply qubit_not_0tens. lia. unfold abgate; solve_WF_matrix.
                        exists 7%nat.
                        split. lia.
                        apply case111_goal_change.
                        lca. lca.
                        replace ((∣0⟩ ⊗ ∣1⟩ ⊗ y) 3%nat 0%nat) with (y 1%nat 0%nat) by lca.
                        assumption.
                        replace (abgate U 7%nat 3%nat) with (BL 1%nat 1%nat).
                        rewrite ival at 1. rewrite jval. assumption. lca.
                    }
                }
                {
                    rewrite Nat.lt_1_r in l2.
                    destruct yeln0.
                    {
                        exists ∣0⟩.
                        rewrite implication_decomp.
                        apply Coq.Logic.Classical_Prop.and_not_or.
                        split. 
                        unfold not.
                        intro. apply H1. apply qubit0_qubit.
                        apply Coq.Logic.Classical_Pred_Type.all_not_not_ex.
                        intros.
                        apply Coq.Logic.Classical_Prop.or_not_and.
                        rewrite <- implication_decomp.
                        apply qubit_not_0tens. lia. unfold abgate; solve_WF_matrix.
                        exists 6%nat.
                        split. lia.
                        apply case100_goal_change.
                        lca. lca.
                        replace ((∣0⟩ ⊗ ∣0⟩ ⊗ y) 0%nat 0%nat) with (y 0%nat 0%nat) by lca.
                        assumption.
                        replace (abgate U 6%nat 0%nat) with (BL 1%nat 0%nat).
                        rewrite ival at 1. rewrite <- l2. assumption. lca.
                    }
                    {
                        exists ∣0⟩.
                        rewrite implication_decomp.
                        apply Coq.Logic.Classical_Prop.and_not_or.
                        split. 
                        unfold not.
                        intro. apply H1. apply qubit0_qubit.
                        apply Coq.Logic.Classical_Pred_Type.all_not_not_ex.
                        intros.
                        apply Coq.Logic.Classical_Prop.or_not_and.
                        rewrite <- implication_decomp.
                        apply qubit_not_0tens. lia. unfold abgate; solve_WF_matrix.
                        exists 7%nat.
                        split. lia.
                        apply case101_goal_change.
                        lca. lca.
                        replace ((∣0⟩ ⊗ ∣0⟩ ⊗ y) 1%nat 0%nat) with (y 1%nat 0%nat) by lca.
                        assumption.
                        replace (abgate U 7%nat 1%nat) with (BL 1%nat 0%nat).
                        rewrite ival at 1. rewrite <- l2. assumption. lca.
                    }  
                }   
            }
        }
        {
            rewrite Nat.lt_1_r in l0.
            destruct (le_lt_dec 2 j).
            {
                contradict n0point.
                rewrite WF_BL. reflexivity.
                right. lia.
            }
            {
                destruct (le_lt_dec 1 j).
                {
                    assert (jval := nat_tight_bound 1 j l2 l1).
                    destruct yeln0.
                    {
                        exists ∣1⟩.
                        rewrite implication_decomp.
                        apply Coq.Logic.Classical_Prop.and_not_or.
                        split. 
                        unfold not.
                        intro. apply H1. apply qubit1_qubit.
                        apply Coq.Logic.Classical_Pred_Type.all_not_not_ex.
                        intros.
                        apply Coq.Logic.Classical_Prop.or_not_and.
                        rewrite <- implication_decomp.
                        apply qubit_not_0tens. lia. unfold abgate; solve_WF_matrix.
                        exists 4%nat.
                        split. lia.
                        apply case010_goal_change.
                        lca. lca.
                        replace ((∣0⟩ ⊗ ∣1⟩ ⊗ y) 2%nat 0%nat) with (y 0%nat 0%nat) by lca.
                        assumption.
                        replace (abgate U 4%nat 2%nat) with (BL 0%nat 1%nat).
                        rewrite <- l0 at 1. rewrite jval. assumption. lca.
                    }
                    {
                        exists ∣1⟩.
                        rewrite implication_decomp.
                        apply Coq.Logic.Classical_Prop.and_not_or.
                        split. 
                        unfold not.
                        intro. apply H1. apply qubit1_qubit.
                        apply Coq.Logic.Classical_Pred_Type.all_not_not_ex.
                        intros.
                        apply Coq.Logic.Classical_Prop.or_not_and.
                        rewrite <- implication_decomp.
                        apply qubit_not_0tens. lia. unfold abgate; solve_WF_matrix.
                        exists 5%nat.
                        split. lia.
                        apply case011_goal_change.
                        lca. lca.
                        replace ((∣0⟩ ⊗ ∣1⟩ ⊗ y) 3%nat 0%nat) with (y 1%nat 0%nat) by lca.
                        assumption.
                        replace (abgate U 5%nat 3%nat) with (BL 0%nat 1%nat).
                        rewrite <- l0 at 1. rewrite jval. assumption. lca.
                    }
                }
                {
                    rewrite Nat.lt_1_r in l2.
                    destruct yeln0.
                    {
                        exists ∣0⟩.
                        rewrite implication_decomp.
                        apply Coq.Logic.Classical_Prop.and_not_or.
                        split. 
                        unfold not.
                        intro. apply H1. apply qubit0_qubit.
                        apply Coq.Logic.Classical_Pred_Type.all_not_not_ex.
                        intros.
                        apply Coq.Logic.Classical_Prop.or_not_and.
                        rewrite <- implication_decomp.
                        apply qubit_not_0tens. lia. unfold abgate; solve_WF_matrix.
                        exists 4%nat.
                        split. lia.
                        apply case000_goal_change.
                        lca. lca.
                        replace ((∣0⟩ ⊗ ∣0⟩ ⊗ y) 0%nat 0%nat) with (y 0%nat 0%nat) by lca.
                        assumption.
                        replace (abgate U 4%nat 0%nat) with (BL 0%nat 0%nat).
                        rewrite <- l0 at 1. rewrite <- l2. assumption. lca.
                    }
                    {
                        exists ∣0⟩.
                        rewrite implication_decomp.
                        apply Coq.Logic.Classical_Prop.and_not_or.
                        split. 
                        unfold not.
                        intro. apply H1. apply qubit0_qubit.
                        apply Coq.Logic.Classical_Pred_Type.all_not_not_ex.
                        intros.
                        apply Coq.Logic.Classical_Prop.or_not_and.
                        rewrite <- implication_decomp.
                        apply qubit_not_0tens. lia. unfold abgate; solve_WF_matrix.
                        exists 5%nat.
                        split. lia.
                        apply case001_goal_change.
                        lca. lca.
                        replace ((∣0⟩ ⊗ ∣0⟩ ⊗ y) 1%nat 0%nat) with (y 1%nat 0%nat) by lca.
                        assumption.
                        replace (abgate U 5%nat 1%nat) with (BL 0%nat 0%nat).
                        rewrite <- l0 at 1. rewrite <- l2. assumption. lca.
                    }  
                }   
            }
        }
    }
}
apply Coq.Logic.Classical_Prop.NNPP.
unfold not at 1.
intros cntrps_premise.
apply cntrps in cntrps_premise.
apply cntrps_premise.
apply zeropassthrough.
Qed.

Lemma abgate_diagblock: forall (U: Square 4), 
WF_Unitary U -> (exists (y: Vector 2), WF_Qubit y /\ 
forall (x : Vector 2), WF_Qubit x -> (exists (phi: Vector 4), WF_Matrix phi /\
(abgate U) × (∣0⟩ ⊗ x ⊗ y)  =  ∣0⟩ ⊗ phi)) ->
exists (TL BR: Square 4), WF_Unitary TL /\ WF_Unitary BR /\
abgate U = ∣0⟩⟨0∣ ⊗ TL .+ ∣1⟩⟨1∣ ⊗ BR.
Proof.
intros U U_unitary zeropassthrough.
assert (zpass_decomp:= abgate_0prop_bottomleft_0block U U_unitary zeropassthrough).
destruct zpass_decomp as [TL0 [TR0 [BR0 [WF_TL0 [WF_TR0 [WF_BR0 zpass_decomp]]]]]].
replace (∣0⟩⟨0∣ ⊗ TL0 .+ ∣0⟩⟨1∣ ⊗ TR0 .+ ∣1⟩⟨1∣ ⊗ BR0) with
(∣0⟩⟨0∣ ⊗ TL0 .+ ∣0⟩⟨1∣ ⊗ TR0 .+ ∣1⟩⟨0∣ ⊗ Zero .+ ∣1⟩⟨1∣ ⊗ BR0) in zpass_decomp.
2: rewrite kron_0_r; rewrite Mplus_0_r; reflexivity.
assert (abgate_U_unitary: WF_Unitary (abgate U)). apply abgate_unitary; assumption.
destruct abgate_U_unitary as [WF_abU abU_inv].
replace (I (4 * 2)) with (∣0⟩⟨0∣ ⊗ I 4 .+ ∣0⟩⟨1∣ ⊗ Zero .+ ∣1⟩⟨0∣ ⊗ Zero .+ ∣1⟩⟨1∣ ⊗ I 4) in abU_inv.
2: lma'; solve_WF_matrix.
assert (block_mult_partial := @block_multiply 4 (abgate U) † (abgate U) TL0† Zero TR0† BR0†
TL0 TR0 Zero BR0).
assert (block_mult:  (abgate U) † × abgate U =
∣0⟩⟨0∣ ⊗ ((TL0) † × TL0 .+ (@Zero 4 4) × Zero) .+ ∣0⟩⟨1∣ ⊗ ((TL0) † × TR0 .+ Zero × BR0)
.+ ∣1⟩⟨0∣ ⊗ ((TR0) † × TL0 .+ (BR0) † × Zero)
.+ ∣1⟩⟨1∣ ⊗ ((TR0) † × TR0 .+ (BR0) † × BR0)).
{
    apply block_mult_partial.
    1,2,3,4,5,6,7,8: solve_WF_matrix.
    rewrite zpass_decomp.
    repeat rewrite Mplus_adjoint.
    repeat rewrite kron_adjoint.
    rewrite adjoint00, adjoint01, adjoint10, adjoint11.
    rewrite zero_adjoint_eq.
    repeat rewrite kron_0_r.
    repeat rewrite Mplus_0_r.
    reflexivity.
    apply zpass_decomp.
}
clear block_mult_partial.
repeat rewrite Mmult_0_r in block_mult.
repeat rewrite Mmult_0_l in block_mult.
repeat rewrite Mplus_0_r in block_mult.
repeat rewrite Mplus_0_l in block_mult.
assert (WF_TL0_inv: WF_Matrix ((TL0) † × TL0)). solve_WF_matrix.
assert (WF_TR_block: WF_Matrix ((TL0) † × TR0)). solve_WF_matrix.
assert (WF_BL_block: WF_Matrix ((TR0) † × TL0)). solve_WF_matrix.
assert (WF_BR_block: WF_Matrix ((TR0) † × TR0 .+ (BR0) † × BR0)). solve_WF_matrix.
assert (self_eq: (abgate U) † × abgate U = (abgate U) † × abgate U). reflexivity.
rewrite abU_inv in block_mult; symmetry in block_mult.
assert (block_eq:= @block_equalities 4%nat
((TL0) † × TL0) ((TL0) † × TR0) ((TR0) † × TL0) ((TR0) † × TR0 .+ (BR0) † × BR0) (I 4) Zero Zero (I 4)
WF_TL0_inv WF_TR_block WF_BL_block WF_BR_block
(@WF_I 4) (@WF_Zero 4 4) (@WF_Zero 4 4) (@WF_I 4) block_mult).
destruct block_eq as [TL0_inv [_ [TR_is_Zero BR0_inv]]].
assert (TL0_unitary: WF_Unitary TL0). split. 1,2: assumption.
apply unitary_mult_zero_cancel_r in TR_is_Zero. 2: solve_WF_matrix. 2: assumption.
rewrite <- zero_adjoint_eq in TR_is_Zero.
apply (f_equal (fun f => f †)) in TR_is_Zero.
repeat rewrite adjoint_involutive in TR_is_Zero.
rewrite TR_is_Zero in BR0_inv.
rewrite Mmult_0_r in BR0_inv.
rewrite Mplus_0_l in BR0_inv.
exists TL0, BR0.
split. assumption.
split. split. 1,2: assumption.
rewrite zpass_decomp.
rewrite TR_is_Zero.
Msimpl_light.
reflexivity.
Qed.

Lemma acgate_diagblock: forall (U: Square 4), 
WF_Unitary U -> (exists (x: Vector 2), WF_Qubit x /\ 
forall (y : Vector 2), WF_Qubit y -> (exists (phi: Vector 4), WF_Matrix phi /\
(acgate U) × (∣0⟩ ⊗ x ⊗ y)  =  ∣0⟩ ⊗ phi)) ->
exists (TL BR: Square 4), WF_Unitary TL /\ WF_Unitary BR /\
acgate U = ∣0⟩⟨0∣ ⊗ TL .+ ∣1⟩⟨1∣ ⊗ BR.
Proof.
intros U U_unitary zeropassthrough.
assert (goal_change: (exists TL BR : Square 4,
WF_Unitary TL /\ WF_Unitary BR /\ abgate U = ∣0⟩⟨0∣ ⊗ TL .+ ∣1⟩⟨1∣ ⊗ BR) -> 
exists TL BR : Square 4, WF_Unitary TL /\ WF_Unitary BR /\
acgate U = ∣0⟩⟨0∣ ⊗ TL .+ ∣1⟩⟨1∣ ⊗ BR).
{
    intros.
    destruct H as [TLs [BRs [TLs_unitary [BRs_unitary abs]]]].
    exists (swap × TLs × swap), (swap × BRs × swap).
    split. apply Mmult_unitary. apply Mmult_unitary. 1,3: apply swap_unitary. assumption.
    split. apply Mmult_unitary. apply Mmult_unitary. 1,3: apply swap_unitary. assumption.
    unfold acgate.
    rewrite abs.
    unfold swapbc.
    rewrite Mmult_plus_distr_l.
    repeat rewrite (@kron_mixed_product 2 2 2 4 4 4).
    repeat rewrite Mmult_1_l. 2,3: solve_WF_matrix.
    rewrite Mmult_plus_distr_r.
    repeat rewrite (@kron_mixed_product 2 2 2 4 4 4).
    repeat rewrite Mmult_1_r. 2,3: solve_WF_matrix.
    reflexivity.
}
apply goal_change.
apply abgate_diagblock.
assumption.
destruct zeropassthrough as [x [x_qubit zeropassthrough]].
exists x.
split. assumption.
intros y y_qubit.
specialize (zeropassthrough y y_qubit).
destruct zeropassthrough as [phis [WF_phis zeropassthrough]].
exists (swap × phis).
split. solve_WF_matrix.
unfold acgate in zeropassthrough.
apply (f_equal (fun f => swapbc × f)) in zeropassthrough.
repeat rewrite <- Mmult_assoc in zeropassthrough.
rewrite swapbc_inverse in zeropassthrough at 1.
rewrite Mmult_1_l in zeropassthrough. 2: apply WF_abgate; apply U_unitary.
rewrite Mmult_assoc in zeropassthrough.
rewrite swapbc_3q in zeropassthrough. 2: solve_WF_matrix. 2: apply x_qubit. 2: apply y_qubit.
rewrite zeropassthrough at 1.
unfold swapbc.
rewrite (@kron_mixed_product 2 2 1 4 4 1).
rewrite Mmult_1_l. 2: solve_WF_matrix.
reflexivity.
Qed.

Definition TwoQubitGate (U : Square 8) := exists (V : Square 4), WF_Unitary V /\ (U = abgate V \/ U = acgate V \/ U = bcgate V).

Lemma abgate_twoqubitgate : forall (U : Square 4), WF_Unitary U -> TwoQubitGate (abgate U).
Proof.
  intros U U_unitary.
  unfold TwoQubitGate.
  exists U.
  split. assumption.
  left. reflexivity.
Qed.

Lemma acgate_twoqubitgate : forall (U : Square 4), WF_Unitary U -> TwoQubitGate (acgate U).
Proof.
  intros U U_unitary.
  unfold TwoQubitGate.
  exists U.
  split. assumption.
  right. left. reflexivity.
Qed.

Lemma bcgate_twoqubitgate : forall (U : Square 4), WF_Unitary U -> TwoQubitGate (bcgate U).
Proof.
  intros U U_unitary.
  unfold TwoQubitGate.
  exists U.
  split. assumption.
  right. right. reflexivity.
Qed.

Lemma abgate_mult : forall (A B : Square 4), abgate A × abgate B = abgate (A × B).
Proof.
  intros A B.
  unfold abgate.
  rewrite kron_mixed_product.
  Msimpl_light; solve_WF_matrix.
Qed.

Lemma bcgate_mult : forall (A B : Square 4), bcgate A × bcgate B = bcgate (A × B).
Proof.
  intros A B.
  unfold bcgate.
  rewrite kron_mixed_product.
  Msimpl_light; solve_WF_matrix.
Qed.

Lemma acgate_mult : forall (A B : Square 4), WF_Matrix B -> acgate A × acgate B = acgate (A × B).
Proof.
  intros A B WF_B.
  unfold acgate.
  repeat rewrite Mmult_assoc.
  repeat rewrite <- Mmult_assoc with (A := swapbc).
  rewrite swapbc_inverse at 1.
  rewrite Mmult_1_l.
  rewrite Mmult_assoc with (A := swapbc).
  rewrite <- Mmult_assoc with (A := abgate A).
  rewrite abgate_mult.
  rewrite <- Mmult_assoc.
  all: solve_WF_matrix.
Qed.

Lemma WF_TwoQubitGate : forall (U : Square 8),
  TwoQubitGate U -> WF_Matrix U.
Proof.
  intros U U_gate.
  unfold TwoQubitGate in U_gate.
  destruct U_gate as [V [V_unitary [V_ab | [V_ac | V_bc]]]].
  rewrite V_ab; solve_WF_matrix.
  rewrite V_ac; solve_WF_matrix.
  rewrite V_bc; solve_WF_matrix.
Qed.

#[export] Hint Resolve WF_TwoQubitGate : wf_db.

Lemma swapab_conj_ac : forall (U : Square 4), WF_Matrix U ->
  swapab × acgate U × swapab = bcgate U.
Proof.
  intros.
  unfold acgate, swapbc, abgate.
  rewrite swap_helper. 2: assumption.
  rewrite <- Mmult_assoc.
  rewrite <- Mmult_assoc with (A := swapab) (B := swapab) (C := I 2 ⊗ U).
  rewrite swapab_inverse.
  rewrite Mmult_assoc.
  rewrite swapab_inverse at 1.
  Msimpl_light; solve_WF_matrix.
Qed.

Lemma swapab_conj_bc : forall (U : Square 4), WF_Matrix U ->
  swapab × bcgate U × swapab = acgate U.
Proof.
  intros.
  rewrite <- swapab_conj_ac; auto.
  repeat rewrite Mmult_assoc.
  rewrite swapab_inverse at 1.
  repeat rewrite <- Mmult_assoc.
  rewrite swapab_inverse.
  Msimpl_light; solve_WF_matrix.
Qed.

Lemma swapbc_conj_ab : forall (U : Square 4), WF_Matrix U ->
  swapbc × abgate U × swapbc = acgate U.
Proof.
  intros.
  reflexivity.
Qed.

Lemma swapbc_conj_ac : forall (U : Square 4), WF_Matrix U ->
  swapbc × acgate U × swapbc = abgate U.
Proof.
  intros.
  unfold acgate, abgate.
  repeat rewrite Mmult_assoc.
  rewrite swapbc_inverse at 1.
  repeat rewrite <- Mmult_assoc.
  rewrite swapbc_inverse.
  Msimpl_light; solve_WF_matrix.
Qed.

Lemma swapac_conj_ab : forall (U : Square 4), WF_Matrix U ->
  swapac × abgate U × swapac = bcgate (swap × U × swap).
Proof.
  intros.
  unfold swapac, swapab, abgate, bcgate.
  repeat rewrite Mmult_assoc.
  rewrite <- Mmult_assoc with (A := U ⊗ I 2).
  rewrite <- Mmult_assoc with (B := (U ⊗ I 2) × (swap ⊗ I 2)).
  rewrite <- Mmult_assoc with (B := U ⊗ I 2).
  repeat rewrite (@kron_mixed_product 4 4 4 2 2 2).
  Msimpl_light.
  replace (swap × U × swap ⊗ I 2) with (abgate (swap × U × swap)). 2: reflexivity.
  fold swapab.
  rewrite <- Mmult_assoc with (C := swapab).
  repeat rewrite <- Mmult_assoc with (A := swapbc).
  replace (swapbc × abgate (swap × U × swap) × swapbc) with (acgate (swap × U × swap)) at 1. 2: reflexivity.
  repeat rewrite <- Mmult_assoc.
  rewrite swapab_conj_ac; solve_WF_matrix.
Qed.

Lemma swapac_conj_bc : forall (U : Square 4), WF_Matrix U ->
  swapac × bcgate U × swapac = abgate (swap × U × swap).
Proof.
  intros.
  unfold swapac.
  repeat rewrite Mmult_assoc.
  repeat rewrite <- Mmult_assoc with (C := swapab).
  repeat rewrite <- Mmult_assoc with (C := swapbc).
  rewrite <- Mmult_assoc with (C := swapab).
  rewrite swapab_conj_bc.
  rewrite Mmult_assoc with (A := swapab).
  rewrite swapbc_conj_ac.
  unfold swapab, abgate.
  repeat rewrite (@kron_mixed_product 4 4 4 2 2 2).
  Msimpl_light.
  rewrite Mmult_assoc.
  all: solve_WF_matrix.
Qed.

Lemma swapab_twoqubitgate : forall (U : Square 4), TwoQubitGate U ->
  TwoQubitGate (swapab × U × swapab).
Proof.
  intros U U_gate.
  unfold TwoQubitGate in *.
  destruct U_gate as [V [V_unitary [V_ab | [V_ac | V_bc]]]].
  {
    rewrite V_ab; clear V_ab.
    exists (swap × V × swap).
    split. solve_WF_matrix.
    left.
    unfold abgate, swapab.
    repeat rewrite (@kron_mixed_product 4 4 4 2 2 2).
    Msimpl_light; reflexivity.
  }
  {
    rewrite V_ac; clear V_ac.
    exists V.
    split. solve_WF_matrix.
    right; right.
    apply swapab_conj_ac; solve_WF_matrix.
  }
  {
    rewrite V_bc; clear V_bc.
    exists V.
    split. solve_WF_matrix.
    right; left.
    apply swapab_conj_bc; solve_WF_matrix.
  }
Qed.

Lemma swapac_twoqubitgate : forall (U : Square 8), TwoQubitGate U ->
  TwoQubitGate (swapac × U × swapac).
Proof.
  intros U U_gate.
  unfold TwoQubitGate in *.
  destruct U_gate as [V [V_unitary [V_ab | [V_ac | V_bc]]]].
  {
    rewrite V_ab; clear V_ab.
    exists (swap × V × swap).
    split. solve_WF_matrix.
    right; right.
    apply swapac_conj_ab; solve_WF_matrix.
  }
  {
    rewrite V_ac; clear V_ac.
    exists (swap × V × swap).
    split. solve_WF_matrix.
    right; left.
    unfold swapac.
    repeat rewrite Mmult_assoc.
    repeat rewrite <- Mmult_assoc with (C := swapab).
    repeat rewrite <- Mmult_assoc with (C := swapbc).
    rewrite <- Mmult_assoc with (C := swapab).
    rewrite swapab_conj_ac.
    rewrite Mmult_assoc with (A := swapab).
    unfold swapbc, bcgate.
    repeat rewrite (@kron_mixed_product 2 2 2 4 4 4).
    Msimpl_light.
    replace (I 2 ⊗ (swap × V × swap)) with (bcgate (swap × V × swap)). 2: reflexivity.
    rewrite swapab_conj_bc.
    rewrite Mmult_assoc.
    all: solve_WF_matrix.
  }
  {
    rewrite V_bc; clear V_bc.
    exists (swap × V × swap).
    split. solve_WF_matrix.
    left.
    unfold swapac, acgate.
    repeat rewrite Mmult_assoc.
    repeat rewrite <- Mmult_assoc with (C := swapab).
    repeat rewrite <- Mmult_assoc with (C := swapbc).
    rewrite <- Mmult_assoc with (C := swapab).
    rewrite swapab_conj_bc.
    rewrite Mmult_assoc with (A := swapab).
    rewrite swapbc_conj_ac.
    unfold swapab, abgate.
    repeat rewrite (@kron_mixed_product 4 4 4 2 2 2).
    rewrite Mmult_assoc.
    Msimpl_light.
    all: solve_WF_matrix.
  }
Qed.
