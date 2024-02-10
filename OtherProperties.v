Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.
From Proof Require Import MatrixHelpers.
From Proof Require Import SwapHelpers.
From Proof Require Import GateHelpers.

Lemma id_tens_equiv_block_diag {n}: forall (A : Square n),
I 2 ⊗ A = ∣0⟩⟨0∣ ⊗ A .+ ∣1⟩⟨1∣ ⊗ A.
Proof.
intros.
assert (I 2 = ∣0⟩⟨0∣ .+ ∣1⟩⟨1∣). lma'.
rewrite H.
apply kron_plus_distr_r.
Qed.

Lemma a27: forall (V1 V2 V3 V4 U0 U1 : Square 4) (P0 P1: Square 2), 
WF_Unitary V1 -> WF_Unitary V2 -> WF_Unitary V3 -> WF_Unitary V4 -> 
WF_Unitary U0 -> WF_Unitary U1 -> WF_Unitary P0 -> WF_Unitary P1 -> 
(acgate V1) × (bcgate V2) × (acgate V3) × (bcgate V4) = ∣0⟩⟨0∣ ⊗ U0 .+ ∣1⟩⟨1∣ ⊗ U1 ->
V1 = ∣0⟩⟨0∣ ⊗ P0 .+ ∣1⟩⟨1∣ ⊗ P1 -> 
(exists (Q0 Q1: Square 2), WF_Unitary Q0 /\ WF_Unitary Q1 /\ V3 = ∣0⟩⟨0∣ ⊗ Q0 .+ ∣1⟩⟨1∣ ⊗ Q1).
Proof. 
intros V1 V2 V3 V4 U0 U1 P0 P1
V1_unitary V2_unitary V3_unitary V4_unitary U0_unitary U1_unitary P0_unitary P1_unitary
prod_prop V1_prop.
assert (temp: WF_Unitary V2). assumption.
destruct temp as [WF_v2 v2_inv].
assert (temp: WF_Unitary V3). assumption.
destruct temp as [WF_v3 v3_inv].
assert (temp: WF_Unitary P0). assumption.
destruct temp as [WF_p0 p0_inv].
assert (temp: WF_Unitary P1). assumption.
destruct temp as [WF_p1 p1_inv].
assert (temp: WF_Unitary (acgate V1)). apply acgate_unitary. assumption.
destruct temp as [WF_acv1 acv1_inv].
assert (temp: WF_Unitary (bcgate V2)). apply bcgate_unitary. assumption.
destruct temp as [WF_bcv2 bcv2_inv].
assert (temp: WF_Unitary (bcgate V4)†). apply transpose_unitary. apply bcgate_unitary. assumption.
destruct temp as [WF_bcv4dag bcv4dag_inv].
rewrite adjoint_involutive in bcv4dag_inv.
assert (acV1_decomp: acgate V1 = ∣0⟩⟨0∣ ⊗ I 2 ⊗ P0 .+ ∣1⟩⟨1∣ ⊗ I 2 ⊗ P1).
{
    unfold acgate.
    unfold abgate.
    rewrite V1_prop.
    rewrite kron_plus_distr_r.
    rewrite Mmult_plus_distr_l.
    rewrite Mmult_plus_distr_r.
    rewrite swapbc_3gate. rewrite swapbc_3gate.
    reflexivity.
    all: solve_WF_matrix.
}
assert (V3_way1 : acgate V1 × bcgate V2 × acgate V3 × bcgate V4 = ∣0⟩⟨0∣ ⊗ U0 .+ ∣1⟩⟨1∣ ⊗ U1). assumption.
apply (f_equal (fun f => (acgate V1) † × f)) in V3_way1.
repeat rewrite <- Mmult_assoc in V3_way1. rewrite acv1_inv in V3_way1.
rewrite Mmult_1_l in V3_way1. 2: apply WF_bcgate. 2: assumption.
apply (f_equal (fun f => (bcgate V2) † × f)) in V3_way1.
repeat rewrite <- Mmult_assoc in V3_way1. rewrite bcv2_inv in V3_way1.
rewrite Mmult_1_l in V3_way1. 2: apply WF_acgate. 2: assumption.
apply (f_equal (fun f => f × (bcgate V4) †)) in V3_way1.
repeat rewrite Mmult_assoc in V3_way1. rewrite bcv4dag_inv in V3_way1 at 1.
rewrite Mmult_1_r in V3_way1. 2: apply WF_acgate. 2: assumption.
unfold bcgate in V3_way1. do 2 rewrite kron_adjoint in V3_way1.
rewrite id_adjoint_eq in V3_way1.
do 2 rewrite id_tens_equiv_block_diag in V3_way1.
rewrite acV1_decomp in V3_way1.
rewrite Mplus_adjoint in V3_way1.
repeat rewrite kron_adjoint in V3_way1.
rewrite adjoint00 in V3_way1.
rewrite adjoint11 in V3_way1.
rewrite id_adjoint_eq in V3_way1.
rewrite Mmult_plus_distr_l in V3_way1.
assert (red_helper: (∣0⟩⟨0∣ ⊗ U0 .+ ∣1⟩⟨1∣ ⊗ U1) × (∣1⟩⟨1∣ ⊗ (V4) †) =
∣1⟩⟨1∣ ⊗ (U1 × (V4) †)).
{
    rewrite Mmult_plus_distr_r.
    repeat rewrite kron_mixed_product.
    repeat rewrite isolate_inner_mult.
    rewrite Mmult01, Mmult11.
    Msimpl.
    reflexivity.
}
rewrite red_helper in V3_way1 at 1. clear red_helper.
assert (red_helper: (∣0⟩⟨0∣ ⊗ U0 .+ ∣1⟩⟨1∣ ⊗ U1) × (∣0⟩⟨0∣ ⊗ (V4) †) = 
∣0⟩⟨0∣ ⊗ (U0 × (V4) †)).
{
    rewrite Mmult_plus_distr_r.
    repeat rewrite kron_mixed_product.
    repeat rewrite isolate_inner_mult.
    rewrite Mmult00, Mmult10.
    Msimpl.
    reflexivity.
}
rewrite red_helper in V3_way1 at 1. clear red_helper.
rewrite Mmult_plus_distr_l in V3_way1.
assert (red_helper: (∣0⟩⟨0∣ ⊗ I 2 ⊗ (P0) † .+ ∣1⟩⟨1∣ ⊗ I 2 ⊗ (P1) †)
× (∣1⟩⟨1∣ ⊗ (U1 × (V4) †)) = (∣1⟩⟨1∣ ⊗ ((I 2 ⊗ (P1) †) × U1 × (V4) †))).
{
    rewrite Mmult_plus_distr_r.
    rewrite kron_assoc. 2,3,4: solve_WF_matrix.
    assert (kron_mix_help: ∣0⟩⟨0∣ ⊗ (I 2 ⊗ (P0) †) × (∣1⟩⟨1∣ ⊗ (U1 × (V4) †)) 
    = ((∣0⟩⟨0∣ × ∣1⟩⟨1∣) ⊗ ((I 2 ⊗ (P0) †) × (U1 × (V4) †)))). apply kron_mixed_product.
    rewrite kron_mix_help at 1. clear kron_mix_help.
    rewrite isolate_inner_mult. rewrite Mmult01. Msimpl.
    rewrite kron_assoc. 2,3,4: solve_WF_matrix.
    assert (kron_mix_help: ∣1⟩⟨1∣ ⊗ (I 2 ⊗ (P1) †) × (∣1⟩⟨1∣ ⊗ (U1 × (V4) †)) = 
    (∣1⟩⟨1∣ × ∣1⟩⟨1∣) ⊗  ((I 2 ⊗ (P1) †) × (U1 × (V4) †))). apply kron_mixed_product.
    rewrite kron_mix_help at 1. clear kron_mix_help.
    rewrite isolate_inner_mult. rewrite Mmult11. Msimpl.
    rewrite Mmult_assoc.
    reflexivity.
}
rewrite red_helper in V3_way1 at 1. clear red_helper.
assert (red_helper: (∣0⟩⟨0∣ ⊗ I 2 ⊗ (P0) † .+ ∣1⟩⟨1∣ ⊗ I 2 ⊗ (P1) †)
× (∣0⟩⟨0∣ ⊗ (U0 × (V4) †)) = ∣0⟩⟨0∣ ⊗ ((I 2 ⊗ (P0) †) × U0 × (V4) †)).
{
    rewrite Mmult_plus_distr_r.
    rewrite kron_assoc. 2,3,4: solve_WF_matrix.
    assert (kron_mix_help: ∣0⟩⟨0∣ ⊗ (I 2 ⊗ (P0) †) × (∣0⟩⟨0∣ ⊗ (U0 × (V4) †)) 
    = ((∣0⟩⟨0∣ × ∣0⟩⟨0∣) ⊗ ((I 2 ⊗ (P0) †) × (U0 × (V4) †)))). apply kron_mixed_product.
    rewrite kron_mix_help at 1. clear kron_mix_help.
    rewrite isolate_inner_mult. rewrite Mmult00. Msimpl.
    rewrite kron_assoc. 2,3,4: solve_WF_matrix.
    assert (kron_mix_help: ∣1⟩⟨1∣ ⊗ (I 2 ⊗ (P1) †) × (∣0⟩⟨0∣ ⊗ (U0 × (V4) †)) = 
    (∣1⟩⟨1∣ × ∣0⟩⟨0∣) ⊗  ((I 2 ⊗ (P1) †) × (U0 × (V4) †))). apply kron_mixed_product.
    rewrite kron_mix_help at 1. clear kron_mix_help.
    rewrite isolate_inner_mult. rewrite Mmult10. Msimpl.
    rewrite Mmult_assoc.
    reflexivity.
}
rewrite red_helper in V3_way1 at 1. clear red_helper.
rewrite Mmult_plus_distr_l in V3_way1.
assert (red_helper: (∣0⟩⟨0∣ ⊗ (V2) † .+ ∣1⟩⟨1∣ ⊗ (V2) †)
× (∣1⟩⟨1∣ ⊗ (I 2 ⊗ (P1) † × U1 × (V4) †)) = (∣1⟩⟨1∣ ⊗ ((V2) † × (I 2 ⊗ (P1) †) × U1 × (V4) †))).
{
    rewrite Mmult_plus_distr_r.
    rewrite kron_mixed_product.
    rewrite isolate_inner_mult. rewrite Mmult01. Msimpl.
    rewrite isolate_inner_mult. rewrite Mmult11. Msimpl.
    repeat rewrite Mmult_assoc.
    reflexivity.
}
rewrite red_helper in V3_way1 at 1. clear red_helper.
assert (red_helper: (∣0⟩⟨0∣ ⊗ (V2) † .+ ∣1⟩⟨1∣ ⊗ (V2) †)
× (∣0⟩⟨0∣ ⊗ (I 2 ⊗ (P0) † × U0 × (V4) †)) = ∣0⟩⟨0∣ ⊗ ((V2) † × (I 2 ⊗ (P0) †) × U0 × (V4) †)).
{
    rewrite Mmult_plus_distr_r.
    rewrite kron_mixed_product.
    rewrite isolate_inner_mult. rewrite Mmult00. Msimpl.
    rewrite isolate_inner_mult. rewrite Mmult10. Msimpl.
    repeat rewrite Mmult_assoc.
    reflexivity.
}
rewrite red_helper in V3_way1 at 1. clear red_helper.
apply (f_equal (fun f => f .+ ∣0⟩⟨1∣ ⊗ (@Zero 4 4) .+ ∣1⟩⟨0∣ ⊗ (@Zero 4 4))) in V3_way1.
rewrite kron_0_r in V3_way1 at 1. rewrite kron_0_r in V3_way1 at 1.
do 2 rewrite Mplus_0_r in V3_way1.
do 2 rewrite Mplus_assoc in V3_way1. rewrite Mplus_comm with (A:= ∣1⟩⟨1∣
⊗ ((V2) † × (I 2 ⊗ (P1) †) × U1 × (V4) †)) in V3_way1.
repeat rewrite <- Mplus_assoc in V3_way1.
Admitted.