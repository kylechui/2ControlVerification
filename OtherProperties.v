Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.
From Proof Require Import MatrixHelpers.
From Proof Require Import SwapHelpers.
From Proof Require Import QubitHelpers.
From Proof Require Import GateHelpers.
From Proof Require Import ControlledUnitaries.
From Proof Require Import TensorProducts.

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
assert (temp: WF_Unitary V4). assumption.
destruct temp as [WF_v4 v4_inv].
assert (temp: WF_Unitary U0). assumption.
destruct temp as [WF_u0 u0_inv].
assert (temp: WF_Unitary U1). assumption.
destruct temp as [WF_u1 u1_inv].
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
assert (v3_decomp:= block_decomp_4 V3 WF_v3).
destruct v3_decomp as [Q00 [Q01 [Q10 [Q11 [WF_Q00 [WF_Q01 [WF_Q10 [WF_Q11 v3_decomp]]]]]]]].
assert (V3_way2: acgate V3 = swapbc × abgate V3 × swapbc). unfold acgate. reflexivity.
unfold abgate in V3_way2.
rewrite v3_decomp in V3_way2 at 2.
repeat rewrite kron_plus_distr_r in V3_way2.
repeat rewrite Mmult_plus_distr_l in V3_way2.
repeat rewrite Mmult_plus_distr_r in V3_way2.
rewrite swapbc_3gate in V3_way2. 2,3,4: solve_WF_matrix.
rewrite swapbc_3gate in V3_way2. 2,3,4: solve_WF_matrix.  
rewrite swapbc_3gate in V3_way2. 2,3,4: solve_WF_matrix.  
rewrite swapbc_3gate in V3_way2. 2,3,4: solve_WF_matrix.
rewrite kron_assoc in V3_way2. 2,3,4: solve_WF_matrix.
rewrite kron_assoc in V3_way2. 2,3,4: solve_WF_matrix.
rewrite kron_assoc in V3_way2. 2,3,4: solve_WF_matrix.
rewrite kron_assoc in V3_way2. 2,3,4: solve_WF_matrix.
assert (block_eq := @block_equalities_general 4 (acgate V3) (acgate V3)
((V2) † × (I 2 ⊗ (P0) †) × U0 × (V4) †) (@Zero 4 4) (@Zero 4 4) ((V2) † × (I 2 ⊗ (P1) †) × U1 × (V4) †)
(I 2 ⊗ Q00) (I 2 ⊗ Q01) (I 2 ⊗ Q10) (I 2 ⊗ Q11)).
assert (eq: (V2) † × (I 2 ⊗ (P0) †) × U0 × (V4) † = I 2 ⊗ Q00 /\
Zero = I 2 ⊗ Q01 /\
Zero = I 2 ⊗ Q10 /\
(V2) † × (I 2 ⊗ (P1) †) × U1 × (V4) † = I 2 ⊗ Q11).
{
    apply block_eq.
    lia.
    2,3,5,6,7,8: solve_WF_matrix.
    1,2: apply WF_mult. 2,4: solve_WF_matrix.
    1,2: apply WF_mult. 2,4: solve_WF_matrix.
    1,2: solve_WF_matrix.
    apply V3_way1. apply V3_way2.
    reflexivity.
}
destruct eq as [q00_val [q01_zero [q10_zero q11_val]]].
assert (ztotens: (@Zero 4 4) = I 2 ⊗ (@Zero 2 2)). lma'.
rewrite ztotens in q01_zero at 1.
rewrite ztotens in q10_zero at 1.
apply kron_cancel_l in q01_zero. 2,3: solve_WF_matrix. 2: apply I_neq_zero. 2: lia.
apply kron_cancel_l in q10_zero. 2,3: solve_WF_matrix. 2: apply I_neq_zero. 2: lia.
assert (block_unit: (V3) † × V3 = ∣0⟩⟨0∣ ⊗ I 2 .+ ∣0⟩⟨1∣ ⊗ Zero .+ ∣1⟩⟨0∣ ⊗ Zero .+ ∣1⟩⟨1∣ ⊗ I 2).
{
    rewrite v3_inv.
    lma'.
    solve_WF_matrix.
}
rewrite v3_decomp in block_unit.
assert (trans_help: (∣0⟩⟨0∣ ⊗ Q00 .+ ∣0⟩⟨1∣ ⊗ Q01 .+ ∣1⟩⟨0∣ ⊗ Q10 .+ ∣1⟩⟨1∣ ⊗ Q11) † =
(∣0⟩⟨0∣ ⊗ Q00† .+ ∣0⟩⟨1∣ ⊗ Q10† .+ ∣1⟩⟨0∣ ⊗ Q01† .+ ∣1⟩⟨1∣ ⊗ Q11†)).
{
    repeat rewrite Mplus_adjoint.
    repeat rewrite kron_adjoint.
    rewrite adjoint00, adjoint01, adjoint10, adjoint11.
    lma'.
    all: solve_WF_matrix.
}
rewrite trans_help in block_unit at 1. clear trans_help.
rewrite block_multiply with (U:= (∣0⟩⟨0∣ ⊗ (Q00) † .+ ∣0⟩⟨1∣ ⊗ (Q10) † .+ ∣1⟩⟨0∣ ⊗ (Q01) † .+ ∣1⟩⟨1∣ ⊗ (Q11) †))
(V:= (∣0⟩⟨0∣ ⊗ Q00 .+ ∣0⟩⟨1∣ ⊗ Q01 .+ ∣1⟩⟨0∣ ⊗ Q10 .+ ∣1⟩⟨1∣ ⊗ Q11)) (P00 := (Q00) †) (P01 := (Q10) †)
(P10 := (Q01) †) (P11 := (Q11) †) (Q00 := Q00) (Q01 := Q01) (Q10 := Q10) (Q11 := Q11) in block_unit at 1.
2,3,4,5,6,7,8,9: solve_WF_matrix.
2,3: reflexivity.
rewrite <- q01_zero, <- q10_zero in block_unit.
rewrite zero_adjoint_eq in block_unit.
repeat rewrite Mmult_0_r in block_unit.
repeat rewrite Mmult_0_l in block_unit.
repeat rewrite Mplus_0_r in block_unit.
repeat rewrite Mplus_0_l in block_unit.
assert (block_eq_2 := @block_equalities_general 2 (∣0⟩⟨0∣ ⊗ ((Q00) † × Q00) .+ ∣0⟩⟨1∣ ⊗ Zero .+ ∣1⟩⟨0∣ ⊗ Zero
.+ ∣1⟩⟨1∣ ⊗ ((Q11) † × Q11)) (∣0⟩⟨0∣ ⊗ I 2 .+ ∣0⟩⟨1∣ ⊗ Zero .+ ∣1⟩⟨0∣ ⊗ Zero .+ ∣1⟩⟨1∣ ⊗ I 2)
((Q00) † × Q00) (Zero) (Zero) ((Q11) † × Q11) (I 2) (Zero) (Zero) (I 2)).
assert (unit_eq: (Q00) † × Q00 = I 2 /\
(@Zero 2 2) = Zero /\ (@Zero 2 2) = Zero /\ (Q11) † × Q11 = I 2).
{
    apply block_eq_2.
    lia.
    1,2,3,4,5,6,7,8: solve_WF_matrix.
    reflexivity. reflexivity.
    apply block_unit.
}
destruct unit_eq as [Q00_unit [_ [_ Q11_unit]]].
exists Q00,Q11.
split.
{
    unfold WF_Unitary.
    split. all: assumption.   
}
split.
{
    unfold WF_Unitary.
    split. all: assumption.   
}
rewrite v3_decomp.
rewrite <- q01_zero, <- q10_zero.
Msimpl.
reflexivity.
Qed.

Lemma a28: forall (V1 V2 V3 V4: Square 4) (U : Square 2), 
WF_Unitary V1 -> WF_Unitary V2 -> WF_Unitary V3 -> WF_Unitary V4 ->
WF_Unitary U -> (acgate V1) × (bcgate V2) × (acgate V3) × (bcgate V4) = ccu U -> 
V3 × (∣0⟩ ⊗ ∣0⟩) = ∣0⟩ ⊗ ∣0⟩ -> (forall (x: Vector 2), WF_Qubit x -> 
(acgate V1) × (bcgate V2) × (∣0⟩ ⊗ x ⊗ ∣0⟩)  = (bcgate V4)† × (∣0⟩ ⊗ x ⊗ ∣0⟩)).
Proof.
intros V1 V2 V3 V4 U V1_unitary V2_unitary V3_unitary V4_unitary U_unitary cc_prop v3_prop x x_qubit.
assert (temp: WF_Unitary V3). assumption. 
destruct temp as [WF_v3 v3_inv].
assert (temp: WF_Unitary V4). assumption. 
destruct temp as [WF_v4 v4_inv].
assert (temp: WF_Unitary U). assumption. 
destruct temp as [WF_u u_inv].
assert (temp: WF_Qubit x). assumption.
destruct temp as [_ [WF_x x_unit]].
assert (acv3_id: acgate V3 × (∣0⟩ ⊗ x ⊗ ∣0⟩) = ∣0⟩ ⊗ x ⊗ ∣0⟩).
{
    unfold acgate.
    rewrite <- swapbc_3q at 1. 2,3,4: solve_WF_matrix.
    repeat rewrite Mmult_assoc.
    rewrite <- Mmult_assoc with (A:= swapbc) (B:= swapbc).
    rewrite swapbc_inverse at 1.
    rewrite Mmult_1_l. 2: solve_WF_matrix.
    unfold abgate.
    assert (kron_mix_help: (V3 ⊗ I 2 × (∣0⟩ ⊗ ∣0⟩ ⊗ x)) = (V3 × (∣0⟩ ⊗ ∣0⟩)) ⊗ (I 2 × x)). apply kron_mixed_product.
    rewrite kron_mix_help at 1. clear kron_mix_help.
    rewrite v3_prop. rewrite Mmult_1_l. 2: solve_WF_matrix.
    rewrite swapbc_3q. 2,3,4: solve_WF_matrix.
    reflexivity.
}
rewrite <- acv3_id at 1.
rewrite <- Mmult_1_r with (A := acgate V3). 2: apply WF_acgate. 2: assumption.
assert (temp: WF_Unitary (bcgate V4)†). apply transpose_unitary. apply bcgate_unitary. assumption.
destruct temp as [WF_bcv4dag bcv4dag_inv].
replace (2*2)%nat with 4%nat by lia.
rewrite <- bcv4dag_inv.
rewrite adjoint_involutive.
repeat rewrite <- Mmult_assoc.
rewrite cc_prop at 1.
rewrite bcgate_adjoint at 1. 2: assumption.
rewrite Mmult_assoc.
unfold bcgate at 1.
assert (assoc_help: (∣0⟩ ⊗ x ⊗ ∣0⟩) = (∣0⟩ ⊗ (x ⊗ ∣0⟩))). apply kron_assoc. 1,2,3: solve_WF_matrix.
rewrite assoc_help at 1.
rewrite kron_mixed_product at 1.
rewrite Mmult_1_l. 2: solve_WF_matrix.
rewrite ccu_sum_expansion.
rewrite Mmult_plus_distr_r.
rewrite kron_assoc. 2,3,4,5: solve_WF_matrix.
assert (kron_mix_help: ∣0⟩⟨0∣ ⊗ (I 2 ⊗ I 2) × (∣0⟩ ⊗ ((V4) † × (x ⊗ ∣0⟩))) = 
(∣0⟩⟨0∣ × ∣0⟩) ⊗ ((I 2 ⊗ I 2) × ((V4) † × (x ⊗ ∣0⟩)))). apply kron_mixed_product.
rewrite kron_mix_help at 1. clear kron_mix_help.
replace (I 2 ⊗ I 2) with (I 4) by lma'.
rewrite Mmult_1_l. 2: solve_WF_matrix.
rewrite Mmult_assoc. rewrite Mmult00. rewrite Mmult_1_r. 2: apply WF_qubit0.
assert (kron_mix_help: ∣1⟩⟨1∣ ⊗ control U × (∣0⟩ ⊗ ((V4) † × (x ⊗ ∣0⟩))) = 
(∣1⟩⟨1∣ × ∣0⟩) ⊗ (control U × ((V4) † × (x ⊗ ∣0⟩)))). apply kron_mixed_product.
rewrite kron_mix_help at 1. clear kron_mix_help.
rewrite Mmult_assoc. rewrite Mmult10. Msimpl.
rewrite bcgate_adjoint. 2: assumption.
unfold bcgate.
rewrite kron_assoc. 2,3,4: solve_WF_matrix.
rewrite kron_mixed_product.
rewrite Mmult_1_l. 2: solve_WF_matrix.
reflexivity.
Qed.

Lemma a29: forall (V1 V2 V3 V4: Square 4) (U : Square 2), 
WF_Unitary V1 -> WF_Unitary V2 -> WF_Unitary V3 -> WF_Unitary V4 ->
WF_Unitary U -> (acgate V1) × (bcgate V2) × (acgate V3) × (bcgate V4) = ccu U -> 
V2 × (∣0⟩ ⊗ ∣0⟩) = ∣0⟩ ⊗ ∣0⟩ -> (forall (x: Vector 2), WF_Qubit x -> 
(bcgate V4)† × (acgate V3)† × (x ⊗ ∣0⟩ ⊗ ∣0⟩)  = (acgate V1) × (x ⊗ ∣0⟩ ⊗ ∣0⟩)).
intros V1 V2 V3 V4 U V1_unitary V2_unitary V3_unitary V4_unitary U_unitary cc_prop v2_prop x x_qubit.
assert (temp: WF_Unitary V1). assumption.
destruct temp as [WF_V1 V1_inv].
assert (temp: WF_Unitary V2). assumption.
destruct temp as [WF_V2 V2_inv].
assert (temp: WF_Unitary V3). assumption.
destruct temp as [WF_V3 V3_inv].
assert (temp: WF_Unitary V4). assumption.
destruct temp as [WF_V4 V4_inv].
assert (temp: WF_Unitary U). assumption.
destruct temp as [WF_U U_inv].
assert (temp: WF_Qubit x). assumption.
destruct temp as [_ [WF_x x_unit]].
assert (ccu_dag_exp: ccu (U†) = (acgate V4†) × (bcgate V3†) × (acgate V2†) × (bcgate V1†)).
{
    rewrite <- swapab_ccu. 2: solve_WF_matrix.
    rewrite <- ccu_adjoint. 2: solve_WF_matrix.
    rewrite <- cc_prop.
    repeat rewrite Mmult_adjoint.
    rewrite bcgate_adjoint. 2: solve_WF_matrix.
    rewrite <- Mmult_1_r with (A := bcgate (V4) †). 2: apply WF_bcgate; solve_WF_matrix.
    simpl. rewrite <- swapab_inverse.
    repeat rewrite <- Mmult_assoc.
    rewrite <- acgate_alt_def. 2: solve_WF_matrix.
    repeat rewrite Mmult_assoc.
    apply (f_equal (fun f => (acgate V4†) × f)).
    rewrite acgate_adjoint. 2: solve_WF_matrix.
    rewrite acgate_alt_def. 2: solve_WF_matrix.
    repeat rewrite <- Mmult_assoc.
    rewrite swapab_inverse at 1.
    rewrite Mmult_1_l. 2: apply WF_bcgate; solve_WF_matrix.
    repeat rewrite Mmult_assoc.
    apply (f_equal (fun f => (bcgate V3†) × f)).
    rewrite bcgate_adjoint. 2: solve_WF_matrix.
    rewrite <- Mmult_1_r with (A := bcgate (V2) †). 2: apply WF_bcgate; solve_WF_matrix.
    simpl. rewrite <- swapab_inverse.
    repeat rewrite <- Mmult_assoc.
    rewrite <- acgate_alt_def. 2: solve_WF_matrix.
    repeat rewrite Mmult_assoc.
    apply (f_equal (fun f => (acgate V2†) × f)).
    rewrite acgate_adjoint. 2: solve_WF_matrix.
    rewrite acgate_alt_def. 2: solve_WF_matrix.
    repeat rewrite Mmult_assoc.
    rewrite swapab_inverse at 1.
    rewrite Mmult_1_r. 2: apply WF_bcgate; solve_WF_matrix.
    repeat rewrite <- Mmult_assoc.
    rewrite swapab_inverse at 1.
    apply Mmult_1_l.
    apply WF_bcgate. solve_WF_matrix.
}
assert (v2_dag_prop: V2† × (∣0⟩ ⊗ ∣0⟩) = ∣0⟩ ⊗ ∣0⟩).
{
    apply (f_equal (fun f => V2† × f)) in v2_prop.
    rewrite <- Mmult_assoc in v2_prop.
    rewrite V2_inv in v2_prop.
    rewrite Mmult_1_l in v2_prop. 2: solve_WF_matrix.
    symmetry.
    apply v2_prop. 
}
assert (a28_partial:= @a28 (V4) † (V3) † (V2) † (V1) † (U) †).
assert (a28_impl: forall x : Vector 2,
WF_Qubit x ->
acgate (V4) † × bcgate (V3) † × (∣0⟩ ⊗ x ⊗ ∣0⟩) =
(bcgate (V1) †) † × (∣0⟩ ⊗ x ⊗ ∣0⟩)).
{
    apply a28_partial.
    1,2,3,4,5: apply transpose_unitary; assumption.
    symmetry. assumption.
    assumption.
}
rewrite <- bcgate_adjoint with (U := V1) in a28_impl. 2: solve_WF_matrix.
rewrite adjoint_involutive in a28_impl.
rewrite bcgate_adjoint, acgate_adjoint. 2,3: solve_WF_matrix.
rewrite <- Mmult_1_l with (A:= bcgate (V4) †). 2: apply WF_bcgate; solve_WF_matrix.
simpl. rewrite <- swapab_inverse.
rewrite acgate_alt_def. 2: solve_WF_matrix.
repeat rewrite Mmult_assoc.
rewrite <- Mmult_assoc with (A:= swapab) (B:= bcgate (V4) †).
rewrite <- Mmult_assoc with (A:= swapab × bcgate (V4) †) (B:= swapab).
rewrite <- acgate_alt_def. 2: solve_WF_matrix.
rewrite swapab_3q. 2,3,4: solve_WF_matrix.
rewrite <- Mmult_assoc with (A:= acgate (V4) †).
rewrite a28_impl. 2: assumption.
rewrite <- swapab_3q. 2,3,4: solve_WF_matrix.
repeat rewrite <- Mmult_assoc.
rewrite <- acgate_alt_def. 2: solve_WF_matrix.
reflexivity.
Qed.

Lemma a30: forall (V1 V2 V3 V4: Square 4), 
WF_Unitary V1 -> WF_Unitary V2 -> WF_Unitary V3 -> WF_Unitary V4 ->
(exists (psi: Vector 2), WF_Qubit psi /\
 (forall (x: Vector 2), WF_Qubit x -> 
 (exists (z: Vector 2), WF_Qubit z /\ V2 × (x ⊗ ∣0⟩) = z ⊗ psi))) -> 
(exists (W1 W2 W4: Square 4) (P2 : Square 2), 
WF_Unitary W1 /\ WF_Unitary W2 /\ WF_Unitary W4 /\ WF_Unitary P2 /\
(acgate V1) × (bcgate V2) × (acgate V3) × (bcgate V4) = (acgate W1) × (bcgate W2) × (acgate V3) × (bcgate W4)
/\ W2 = I 2 ⊗ ∣0⟩⟨0∣ .+ P2 ⊗ ∣1⟩⟨1∣).
intros V1 V2 V3 V4 V1_unitary V2_unitary V3_unitary V4_unitary v2_prop.
assert (temp: WF_Unitary V2). assumption.
destruct temp as [WF_V2 V2_inv].
assert (temp: WF_Unitary V3). assumption.
destruct temp as [WF_V3 V3_inv].
assert (temp: WF_Unitary V4). assumption.
destruct temp as [WF_V4 V4_inv].
destruct v2_prop as [psi [psi_qubit v2_prop]].
assert (temp: WF_Qubit psi). assumption.
destruct temp as [_ [WF_psi psi_unit]].
assert (orth_q := exists_orthogonal_qubit psi psi_qubit).
destruct orth_q as [psip [psip_q psi_orth]].
assert (temp: WF_Qubit psip). assumption.
destruct temp as [_ [WF_psip psip_unit]].
assert (w0_def:= v2_prop ∣0⟩ qubit0_qubit).
destruct w0_def as [w0 [w0_qubit v2w0]].
assert (temp: WF_Qubit w0). assumption.
destruct temp as [_ [WF_w0 w0_unit]].
assert (w1_def:= v2_prop ∣1⟩ qubit1_qubit).
destruct w1_def as [w1 [w1_qubit v2w1]].
assert (temp: WF_Qubit w1). assumption.
destruct temp as [_ [WF_w1 w1_unit]].
assert (w0w1_orth: ⟨ w0, w1 ⟩ = 0).
{
    rewrite <- Cmult_1_r with (x := ⟨ w0, w1 ⟩).
    rewrite <- psi_unit.
    rewrite <- kron_inner_prod.
    rewrite <- v2w0. rewrite <- v2w1.
    rewrite <- unitary_preserves_inner_prod. 2: assumption. 2: solve_WF_matrix.
    lca.
}
set (P:= psi × ⟨0∣ .+ psip × ⟨1∣).
assert (P_unitary: WF_Unitary P).
{
    apply orth_qubit_unitary.
    all: assumption.
}
assert (temp: WF_Unitary P). assumption.
destruct temp as [WF_P P_inv].
assert (temp: WF_Unitary P †). apply transpose_unitary. assumption.
destruct temp as [_ Pdag_inv].
rewrite adjoint_involutive in Pdag_inv.
set (Q:= w0 × ⟨0∣ .+ w1 × ⟨1∣).
assert (Q_unitary: WF_Unitary Q).
{
    apply orth_qubit_unitary.
    all: assumption.
}
assert (temp: WF_Unitary Q). assumption.
destruct temp as [WF_Q Q_inv].
assert (temp: WF_Unitary Q †). apply transpose_unitary. assumption.
destruct temp as [_ Qdag_inv].
rewrite adjoint_involutive in Qdag_inv.
set (W1:= V1 × (I 2 ⊗ P)).
assert (W1_unitary: WF_Unitary W1).
{
    apply Mmult_unitary.
    assumption.
    apply kron_unitary.
    apply id_unitary.
    assumption.   
}
set (W2:= (I 2 ⊗ P)† × V2 × (Q ⊗ I 2)†).
assert (W2_unitary: WF_Unitary W2).
{
    apply Mmult_unitary.
    apply Mmult_unitary.
    apply transpose_unitary.
    apply kron_unitary.
    apply id_unitary.
    assumption. assumption.
    apply transpose_unitary.
    apply kron_unitary.
    assumption.
    apply id_unitary.
}
assert (temp: WF_Unitary W2). assumption. 
destruct temp as [WF_W2 W2_inv].
set (W4:= (Q ⊗ I 2) × V4).
assert (W4_unitary: WF_Unitary W4).
{
    apply Mmult_unitary.
    apply (@kron_unitary 2 2).
    assumption.
    apply id_unitary.
    assumption.
}
assert (temp: WF_Unitary W4). assumption. 
destruct temp as [WF_W4 W4_inv].
assert (W_mult_prop: acgate W1 × bcgate W2 × acgate V3 × bcgate W4 = acgate V1 × bcgate V2 × acgate V3 × bcgate V4).
{
    unfold acgate at 1.
    unfold abgate at 1.
    unfold W1.
    rewrite <- Mmult_1_l with (A:= I 2) at 2. 2: solve_WF_matrix.
    rewrite <- kron_mixed_product.
    rewrite <- swapbc_3gate. 2,3,4: solve_WF_matrix.
    repeat rewrite <- Mmult_assoc.
    assert (fold_help: swapbc × (V1 ⊗ I 2) × swapbc = acgate V1). unfold acgate, abgate. reflexivity.
    rewrite fold_help. clear fold_help.
    repeat rewrite Mmult_assoc.
    apply (f_equal (fun f => acgate V1 × f)).
    rewrite <- Mmult_assoc with (A:= swapbc) (B:= swapbc).
    rewrite swapbc_inverse at 1.
    rewrite Mmult_1_l. 2: apply WF_mult. 2: apply WF_bcgate; solve_WF_matrix. 2: apply WF_mult.
    2: apply WF_acgate; solve_WF_matrix. 2: apply WF_bcgate; solve_WF_matrix.
    unfold bcgate at 1.
    unfold W2.
    rewrite Mmult_assoc with (A:= (I 2 ⊗ P) †).
    rewrite <- Mmult_1_r with (A := I 2) at 3. 2: solve_WF_matrix.
    rewrite <- kron_mixed_product.
    rewrite kron_adjoint.
    rewrite id_adjoint_eq.
    repeat rewrite <- Mmult_assoc.
    rewrite kron_assoc. 2,3,4: solve_WF_matrix.
    assert (kron_mix_help: I 2 ⊗ (I 2 ⊗ P) × (I 2 ⊗ (I 2 ⊗ (P) †)) = 
    (I 2 × I 2) ⊗ ((I 2 ⊗ P) × (I 2 ⊗ (P) †))). apply kron_mixed_product.
    rewrite kron_mix_help at 1. clear kron_mix_help.
    assert (kron_mix_help: (I 2 ⊗ P × (I 2 ⊗ (P) †)) = 
    (I 2 × I 2) ⊗ (P × (P) †)). apply kron_mixed_product.
    rewrite kron_mix_help. clear kron_mix_help.
    rewrite Pdag_inv.
    rewrite Mmult_1_l. 2: solve_WF_matrix.
    rewrite id_kron. rewrite id_kron.
    rewrite Mmult_1_l. 2: solve_WF_matrix.
    rewrite <- Mmult_1_r with (A := I 2) at 1. 2: solve_WF_matrix.
    rewrite <- kron_mixed_product.
    assert (fold_help: I 2 ⊗ V2 = bcgate V2). unfold bcgate. reflexivity.
    rewrite fold_help at 1. clear fold_help.
    repeat rewrite Mmult_assoc.
    apply (f_equal (fun f => bcgate V2 × f)).
    rewrite kron_adjoint. rewrite id_adjoint_eq.
    assert (kron_assoc_help: I 2 ⊗ ((Q) † ⊗ I 2) = I 2 ⊗ (Q) † ⊗ I 2). 
    {
        symmetry. apply kron_assoc. all: solve_WF_matrix.
    }
    rewrite kron_assoc_help at 1. clear kron_assoc_help.
    rewrite <- swapbc_3gate. 2,3,4: solve_WF_matrix.
    unfold acgate at 1.
    repeat rewrite Mmult_assoc.
    rewrite <- Mmult_assoc with (A:= swapbc) (B:= swapbc).
    rewrite swapbc_inverse at 1.
    rewrite Mmult_1_l. 2: apply WF_mult. 2: apply WF_abgate;solve_WF_matrix. 2: apply WF_mult. 2: solve_WF_matrix.
    2: apply WF_bcgate; solve_WF_matrix.
    rewrite <- Mmult_assoc with (A:= I 2 ⊗ I 2 ⊗ (Q) †).
    unfold abgate.
    rewrite id_kron.
    assert (kron_mix_help: I (2 * 2) ⊗ (Q) † × (V3 ⊗ I 2) = (I (2 * 2) × V3) ⊗ ((Q) † × I 2)). apply kron_mixed_product.
    rewrite kron_mix_help at 1. clear kron_mix_help. simpl.
    rewrite Mmult_1_l. 2: solve_WF_matrix. 
    rewrite Mmult_1_r. 2: solve_WF_matrix.
    rewrite <- Mmult_1_r with (A := V3) at 1. 2: solve_WF_matrix.
    rewrite <- Mmult_1_l with (A := (Q) †). 2: solve_WF_matrix.
    rewrite <- kron_mixed_product.
    replace (4%nat) with (2*2)%nat by lia.
    rewrite <- id_kron.
    rewrite <- swapbc_3gate. 2,3,4: solve_WF_matrix.
    repeat rewrite <- Mmult_assoc.
    assert (fold_help: swapbc × (V3 ⊗ I 2) × swapbc = acgate V3). unfold acgate, abgate. reflexivity.
    rewrite fold_help at 1. clear fold_help.
    repeat rewrite Mmult_assoc.
    apply (f_equal (fun f => acgate V3 × f)).
    rewrite <- Mmult_assoc with (A:= swapbc).
    rewrite swapbc_inverse at 1.
    rewrite Mmult_1_l. 2: apply WF_bcgate; solve_WF_matrix.
    unfold bcgate at 1.
    unfold W4.
    rewrite <- Mmult_1_l with (A:= I 2) at 3. 2: solve_WF_matrix.
    rewrite <- kron_mixed_product.
    rewrite kron_assoc. 2,3,4: solve_WF_matrix.
    rewrite <- Mmult_assoc.
    assert (kron_mix_help: I 2 ⊗ ((Q) † ⊗ I 2) × (I 2 ⊗ (Q ⊗ I 2)) 
    = (I 2 × I 2) ⊗ (((Q) † ⊗ I 2) × (Q ⊗ I 2))). apply kron_mixed_product.
    rewrite kron_mix_help at 1. clear kron_mix_help.
    assert (kron_mix_help: ((Q) † ⊗ I 2 × (Q ⊗ I 2)) = 
    ((Q) † × Q) ⊗ (I 2 × I 2)). apply kron_mixed_product.
    rewrite kron_mix_help at 1. clear kron_mix_help.
    rewrite Mmult_1_l. 2: solve_WF_matrix.
    rewrite Q_inv.
    rewrite id_kron. rewrite id_kron.
    rewrite Mmult_1_l. 2: solve_WF_matrix.
    unfold bcgate. reflexivity.
}
assert (v2q_prop: forall (phi: Vector 2), WF_Matrix phi -> V2 × (phi ⊗ ∣0⟩) = (Q × phi) ⊗ (P × ∣0⟩)).
{
    intros phi WF_phi.
    assert (el_decomp:= qubit_decomposition1 phi WF_phi).
    rewrite el_decomp.
    rewrite kron_plus_distr_r.
    rewrite Mmult_plus_distr_l.
    repeat rewrite Mscale_kron_dist_l.
    repeat rewrite Mscale_mult_dist_r.
    rewrite v2w0 at 1.
    rewrite v2w1 at 1.
    replace (P × ∣0⟩) with psi. 2: lma'.
    rewrite Mmult_plus_distr_l.
    repeat rewrite Mscale_mult_dist_r.
    replace (Q × ∣0⟩) with w0 by lma'; solve_WF_matrix.
    replace (Q × ∣1⟩) with w1 by lma'; solve_WF_matrix.
    rewrite kron_plus_distr_r.
    repeat rewrite Mscale_kron_dist_l.
    reflexivity.
}
assert (a18_partial:= a18 W2 W2_unitary).
assert (w2_form: exists P2 : Square 2,
W2 = I 2 ⊗ ∣0⟩⟨0∣ .+ P2 ⊗ ∣1⟩⟨1∣ /\ WF_Unitary P2).
{
    apply a18_partial.
    intros beta WF_beta.
    unfold W2.
    repeat rewrite Mmult_assoc.
    repeat rewrite kron_adjoint.
    rewrite id_adjoint_eq.
    assert (kron_mix_help: ((Q) † ⊗ I 2 × (beta ⊗ ∣0⟩)) = ((Q) † × beta) ⊗ (I 2 × ∣0⟩)). apply kron_mixed_product.
    rewrite kron_mix_help at 1. clear kron_mix_help.
    rewrite Mmult_1_l. 2: solve_WF_matrix.
    rewrite v2q_prop. 2: solve_WF_matrix.
    rewrite <- Mmult_assoc.
    rewrite Qdag_inv.
    rewrite Mmult_1_l. 2: solve_WF_matrix.
    assert (kron_mix_help: I 2 ⊗ (P) † × (beta ⊗ (P × ∣0⟩)) = (I 2 × beta) ⊗ ((P) † × (P × ∣0⟩))). apply kron_mixed_product.
    rewrite kron_mix_help at 1. clear kron_mix_help.
    rewrite <- Mmult_assoc.
    rewrite P_inv.
    rewrite Mmult_1_l. 2: solve_WF_matrix.
    rewrite Mmult_1_l. 2: solve_WF_matrix.
    reflexivity.
}
destruct w2_form as [P2 [w2_form P2_unitary]].
exists W1, W2, W4, P2.
split. assumption.
split. assumption.
split. assumption.
split. assumption.
split. symmetry. assumption.
assumption.
Qed.

Lemma a31: forall (V1 V2 V3 V4: Square 4), 
WF_Unitary V1 -> WF_Unitary V2 -> WF_Unitary V3 -> WF_Unitary V4 ->
(exists (psi: Vector 2), WF_Qubit psi /\
 (forall (x: Vector 2), WF_Qubit x -> 
 (exists (z: Vector 2), WF_Qubit z /\ V3† × (x ⊗ ∣0⟩) = z ⊗ psi))) -> 
(exists (W1 W3 W4: Square 4) (P3 : Square 2), 
WF_Unitary W1 /\ WF_Unitary W3 /\ WF_Unitary W4 /\ WF_Unitary P3 /\
(acgate V1) × (bcgate V2) × (acgate V3) × (bcgate V4) = (acgate W1) × (bcgate V2) × (acgate W3) × (bcgate W4)
/\ W3 = I 2 ⊗ ∣0⟩⟨0∣ .+ P3 ⊗ ∣1⟩⟨1∣).
Proof.
intros V1 V2 V3 V4 V1_unitary V2_unitary V3_unitary V4_unitary v2_prop.
assert (temp: WF_Unitary V1). assumption.
destruct temp as [WF_V1 V1_inv].
assert (temp: WF_Unitary V2). assumption.
destruct temp as [WF_V2 V2_inv].
assert (temp: WF_Unitary V3). assumption.
destruct temp as [WF_V3 V3_inv].
assert (temp: WF_Unitary V4). assumption.
destruct temp as [WF_V4 V4_inv].
assert (a30_partial:= a30 V4† V3† V2† V1†).
assert (el_exist:  exists (W4t W3t W1t : Square 4) (P3t : Square 2),
WF_Unitary W4t /\
WF_Unitary W3t /\
WF_Unitary W1t /\
WF_Unitary P3t /\
acgate (V4) † × bcgate (V3) † × acgate (V2) † × bcgate (V1) † =
acgate W4t × bcgate W3t × acgate (V2) † × bcgate W1t /\
W3t = I 2 ⊗ ∣0⟩⟨0∣ .+ P3t ⊗ ∣1⟩⟨1∣).
{
    apply a30_partial.
    1,2,3,4: apply transpose_unitary.
    all: assumption.
}
destruct el_exist as [W4t [W3t [W1t [P3t [W4t_unitary [W3t_unitary [W1t_unitary [P3t_unitary [tprod t_form]]]]]]]]].
assert (temp: WF_Unitary W3t). assumption.
destruct temp as [WF_W3t W3t_inv].
assert (temp: WF_Unitary W1t). assumption.
destruct temp as [WF_W1t W1t_inv].
assert (temp: WF_Unitary W4t). assumption.
destruct temp as [WF_W4t W4t_inv].
do 2 rewrite <- acgate_adjoint in tprod. 2,3,4: solve_WF_matrix.
do 2 rewrite <- bcgate_adjoint in tprod. 2,3,4: solve_WF_matrix.
repeat rewrite <- Mmult_adjoint in tprod.
apply (f_equal (fun f => f †)) in tprod.
rewrite adjoint_involutive in tprod.
repeat rewrite Mmult_adjoint in tprod.
rewrite adjoint_involutive in tprod.
rewrite acgate_adjoint in tprod. 2: solve_WF_matrix.
do 2 rewrite bcgate_adjoint in tprod. 2,3,4: solve_WF_matrix.
repeat rewrite <- Mmult_assoc in tprod.
apply (f_equal (fun f => swapab × f × swapab)) in tprod.
rewrite acgate_alt_def in tprod. 2: solve_WF_matrix.
repeat rewrite <- Mmult_assoc in tprod.
do 2 rewrite <- acgate_alt_def in tprod. 2,3,4: solve_WF_matrix.
rewrite acgate_alt_def with (U := V4) in tprod. 2: solve_WF_matrix.
rewrite acgate_alt_def with (U := (W4t) †) in tprod. 2: solve_WF_matrix.
repeat rewrite Mmult_assoc in tprod.
rewrite <- Mmult_assoc with (A:= swapab) in tprod.
rewrite <- Mmult_assoc with (A:= swapab × bcgate V3) in tprod.
rewrite swapab_inverse in tprod at 1.
rewrite Mmult_1_r in tprod. 2: apply WF_bcgate; solve_WF_matrix.
rewrite swapab_inverse in tprod at 1.
rewrite Mmult_1_r in tprod. 2: apply WF_bcgate; solve_WF_matrix.
rewrite <- acgate_alt_def in tprod. 2: solve_WF_matrix.
rewrite <- Mmult_assoc with (A := swapab) in tprod.
rewrite <- Mmult_assoc with (A := swapab × bcgate (W3t) †) in tprod.
rewrite <- acgate_alt_def in tprod. 2: solve_WF_matrix.
repeat rewrite <- Mmult_assoc in tprod.
exists (W1t) †, (W3t) †, (W4t) †, (P3t) †.
split. apply transpose_unitary. assumption.
split. apply transpose_unitary. assumption.
split. apply transpose_unitary. assumption.
split. apply transpose_unitary. assumption.
split. assumption.
rewrite t_form.
rewrite Mplus_adjoint.
repeat rewrite kron_adjoint.
rewrite id_adjoint_eq.
rewrite adjoint00, adjoint11.
reflexivity.
Qed.

Lemma a32: forall (U1 U2 U3 U4: Square 4), 
WF_Unitary U1 -> WF_Unitary U2 -> WF_Unitary U3 -> WF_Unitary U4 ->
(exists (V1 V2 V3 V4: Square 4), 
WF_Unitary V1 /\ WF_Unitary V2 /\ WF_Unitary V3 /\ WF_Unitary V4 /\
(acgate U1) × (bcgate U2) × (acgate U3) × (bcgate U4) = (acgate V1) × (bcgate V2) × (acgate V3) × (bcgate V4) /\
V3 × (∣0⟩ ⊗ ∣0⟩) = ∣0⟩ ⊗ ∣0⟩).
Proof.
intros U1 U2 U3 U4 U1_unitary U2_unitary U3_unitary U4_unitary.
assert (temp: WF_Unitary U1). assumption.
destruct temp as [WF_U1 U1_inv].
assert (temp: WF_Unitary U2). assumption.
destruct temp as [WF_U2 U2_inv].
assert (temp: WF_Unitary U3). assumption.
destruct temp as [WF_U3 U3_inv].
assert (temp: WF_Unitary U4). assumption.
destruct temp as [WF_U4 U4_inv].
assert (a21_partial := a21 U3 U3_unitary).
destruct a21_partial as [w [w_qubit tensorprod]].
assert (temp: WF_Qubit w). assumption.
destruct temp as [_ [WF_w w_unit]].
rewrite tensor_prod_of_qubit in tensorprod.
2: {
    unfold WF_Qubit.
    split. exists 2%nat. trivial.
    split. solve_WF_matrix.
    rewrite <- unitary_preserves_inner_prod. 2,3: solve_WF_matrix.
    assert (kip_help: ⟨ ∣0⟩ ⊗ w, ∣0⟩ ⊗ w ⟩ = ⟨ ∣0⟩, ∣0⟩ ⟩ * ⟨ w, w ⟩). apply kron_inner_prod.
    rewrite kip_help at 1. clear kip_help.
    rewrite w_unit.
    lca.
}
unfold TensorProdQubit in tensorprod.
assert (temp: WF_Matrix (U3 × (∣0⟩ ⊗ w))). solve_WF_matrix.
apply tensorprod in temp. clear tensorprod.
destruct temp as [psi [phi [psi_qubit [phi_qubit ow_mult]]]].
assert (temp: WF_Qubit psi). assumption.
destruct temp as [_ [WF_psi psi_unit]].
assert (temp: WF_Qubit phi). assumption.
destruct temp as [_ [WF_phi phi_unit]].
assert (temp:= exists_orthogonal_qubit psi psi_qubit).
destruct temp as [psip [psip_qubit psi_orth]].
assert (temp: WF_Qubit psip). assumption.
destruct temp as [_ [WF_psip psip_unit]].
assert (temp:= exists_orthogonal_qubit phi phi_qubit).
destruct temp as [phip [phip_qubit phi_orth]].
assert (temp: WF_Qubit phip). assumption.
destruct temp as [_ [WF_phip phip_unit]].
assert (temp:= exists_orthogonal_qubit w w_qubit).
destruct temp as [wp [wp_qubit w_orth]].
set (W0 := psi × ⟨0∣ .+ psip × ⟨1∣).
assert (W0_unitary: WF_Unitary W0). apply orth_qubit_unitary. 1,2,3: assumption.
assert (temp: WF_Unitary W0). assumption. 
destruct temp as [WF_W0 W0_inv].
assert (temp: WF_Unitary W0†). apply transpose_unitary. assumption. 
destruct temp as [WF_W0dag W0dag_inv].
rewrite adjoint_involutive in W0dag_inv.
set (W1 := phi × ⟨0∣ .+ phip × ⟨1∣).
assert (W1_unitary: WF_Unitary W1). apply orth_qubit_unitary. 1,2,3: assumption.
assert (temp: WF_Unitary W1†). apply transpose_unitary. assumption. 
destruct temp as [WF_W1dag W1dag_inv].
rewrite adjoint_involutive in W1dag_inv.
assert (temp: WF_Unitary W1). assumption. 
destruct temp as [WF_W1 W1_inv].
set (W2 := w × ⟨0∣ .+ wp × ⟨1∣).
assert (W2_unitary: WF_Unitary W2). apply orth_qubit_unitary. 1,2,3: assumption.
assert (temp: WF_Unitary W2†). apply transpose_unitary. assumption. 
destruct temp as [WF_W2dag W2dag_inv].
rewrite adjoint_involutive in W2dag_inv.
assert (temp: WF_Unitary W2). assumption. 
destruct temp as [WF_W2 W2_inv].
set (V1 := U1 × (W0 ⊗ I 2)).
assert (V1_unitary: WF_Unitary V1).
{
    apply Mmult_unitary.
    assumption.
    apply kron_unitary.
    assumption. 
    apply id_unitary.   
}
set (V2 := U2 × (I 2 ⊗ W1)).
assert (V2_unitary: WF_Unitary V2).
{
    apply Mmult_unitary.
    assumption.
    apply kron_unitary.
    apply id_unitary.  
    assumption. 
}
set (V3 := (W0 ⊗ W1)† × U3 × (I 2 ⊗ W2)).
assert (V3_unitary: WF_Unitary V3).
{
    apply Mmult_unitary.
    apply Mmult_unitary.
    apply transpose_unitary.
    apply kron_unitary.
    1,2,3: assumption.
    apply kron_unitary.
    apply id_unitary.  
    assumption. 
}
set (V4 := (I 2 ⊗ W2)† × U4).
assert (V4_unitary: WF_Unitary V4).
{
    apply Mmult_unitary.
    apply transpose_unitary.
    apply kron_unitary.
    apply id_unitary.
    all: assumption.
}
exists V1, V2, V3, V4.
split. assumption. 
split. assumption.
split. assumption. 
split. assumption.
split.
{
    symmetry.
    unfold acgate at 1.
    unfold abgate at 1.
    unfold V1.
    rewrite <- Mmult_1_l with (A:= I 2) at 2. 2: solve_WF_matrix.
    rewrite <- kron_mixed_product.  
    rewrite <- Mmult_1_r with (A:= U1 ⊗ I 2). 2: solve_WF_matrix.
    simpl.
    rewrite <- swapbc_inverse.
    repeat rewrite <- Mmult_assoc.
    assert (fold_help: swapbc × (U1 ⊗ I 2) × swapbc = acgate U1). unfold acgate, abgate. reflexivity.
    rewrite fold_help at 1. clear fold_help.
    repeat rewrite Mmult_assoc.
    apply (f_equal (fun f => acgate U1 × f)).
    repeat rewrite <- Mmult_assoc.
    rewrite swapbc_3gate. 2,3,4: solve_WF_matrix.
    unfold bcgate at 1.
    unfold V2.
    rewrite <- Mmult_1_r with (A:= I 2) at 3. 2: solve_WF_matrix.
    rewrite <- kron_mixed_product.
    rewrite kron_assoc. 2,3,4: solve_WF_matrix.
    rewrite <- Mmult_assoc.
    rewrite id_kron. simpl.
    assert (kron_mix_help: W0 ⊗ I 4 × (I 2 ⊗ U2) = (W0 × I 2) ⊗ (I 4 × U2)). apply kron_mixed_product.
    rewrite kron_mix_help at 1. clear kron_mix_help.
    rewrite Mmult_1_r. 2: solve_WF_matrix.
    rewrite Mmult_1_l. 2: solve_WF_matrix.
    rewrite <- Mmult_1_l with (A:= W0). 2: solve_WF_matrix.
    rewrite <- Mmult_1_r with (A := U2) at 1. 2: solve_WF_matrix.
    rewrite <- kron_mixed_product.
    unfold bcgate at 2.
    repeat rewrite Mmult_assoc.
    apply (f_equal (fun f => I 2 ⊗ U2 × f)).
    assert (assoc_help: I 2 ⊗ (I 2 ⊗ W1) = I 2 ⊗ I 2 ⊗ W1). symmetry. apply kron_assoc. 1,2,3: solve_WF_matrix.
    rewrite assoc_help at 1.
    rewrite <- swapbc_3gate. 2,3,4: solve_WF_matrix.
    unfold acgate at 1.
    unfold abgate at 1.
    unfold V3.
    rewrite <- Mmult_1_l with (A := I 2) at 4. 2: solve_WF_matrix.
    rewrite <- kron_mixed_product.
    rewrite <- Mmult_1_l with (A := I 2) at 3. 2: solve_WF_matrix.
    rewrite <- kron_mixed_product.
    rewrite kron_adjoint.
    repeat rewrite Mmult_assoc.
    rewrite <- Mmult_assoc with (A:= swapbc) (B:= swapbc).
    rewrite swapbc_inverse at 1.
    rewrite Mmult_1_l. 
    2: {
        apply WF_mult. solve_WF_matrix.
        apply WF_mult. solve_WF_matrix.
        apply WF_mult. solve_WF_matrix.
        apply WF_mult. solve_WF_matrix.
        apply WF_bcgate. solve_WF_matrix.
    }
    rewrite <- Mmult_assoc with (A:= I 2 ⊗ W1 ⊗ I 2).
    assert (kron_mix_help: I 2 ⊗ W1 ⊗ I 2 × ((W0) † ⊗ (W1) † ⊗ I 2) =
    (I 2 ⊗ W1 × ((W0) † ⊗ (W1) †)) ⊗ (I 2 × I 2)). apply kron_mixed_product.
    rewrite kron_mix_help at 1. clear kron_mix_help.
    assert (kron_mix_help: I 2 ⊗ W1 × ((W0) † ⊗ (W1) †) =
    (I 2 × (W0) †) ⊗ (W1 × (W1) †)). apply kron_mixed_product.
    rewrite kron_mix_help at 1. clear kron_mix_help.
    rewrite W1dag_inv.
    rewrite Mmult_1_l. 2: solve_WF_matrix.
    rewrite Mmult_1_l. 2: solve_WF_matrix.
    rewrite <- swapbc_3gate. 2,3,4: solve_WF_matrix.
    repeat rewrite Mmult_assoc.
    rewrite <- Mmult_assoc with (A:= swapbc).
    rewrite swapbc_inverse at 1.
    rewrite Mmult_1_l.
    2: {
        apply WF_mult. solve_WF_matrix.
        apply WF_mult. solve_WF_matrix.
        apply WF_mult. solve_WF_matrix.
        apply WF_mult. solve_WF_matrix.
        apply WF_mult. solve_WF_matrix.
        apply WF_bcgate. solve_WF_matrix.
    }
    rewrite kron_assoc. 2,3,4: solve_WF_matrix.
    rewrite <- Mmult_assoc with (A:= W0 ⊗ I 4).
    rewrite id_kron. simpl.
    assert (kron_mix_help: W0 ⊗ I 4 × ((W0) † ⊗ I 4) = (W0 × (W0) †) ⊗ (I 4 × I 4)). apply kron_mixed_product.
    rewrite kron_mix_help at 1. clear kron_mix_help.
    rewrite W0dag_inv.
    rewrite Mmult_1_l. 2: solve_WF_matrix.
    rewrite id_kron.
    rewrite Mmult_1_l.
    2: 
    {
        apply WF_mult. solve_WF_matrix.
        apply WF_mult. solve_WF_matrix.
        apply WF_mult. solve_WF_matrix.
        apply WF_mult. solve_WF_matrix.
        apply WF_bcgate. solve_WF_matrix.
    }
    rewrite <- swapbc_3gate. 2,3,4: solve_WF_matrix.
    repeat rewrite <- Mmult_assoc.
    assert (fold_help: swapbc × (U3 ⊗ I 2) × swapbc = acgate U3). unfold acgate, abgate. reflexivity.
    rewrite fold_help at 1. clear fold_help.
    repeat rewrite Mmult_assoc.
    apply (f_equal (fun f => acgate U3 × f)).
    rewrite <- Mmult_assoc with (A:= swapbc).
    rewrite swapbc_inverse at 1.
    rewrite Mmult_1_l. 2: apply WF_bcgate; solve_WF_matrix. 
    unfold bcgate at 1.
    unfold V4.
    rewrite kron_adjoint.
    rewrite id_adjoint_eq.
    rewrite <- Mmult_1_l with (A:= I 2) at 3. 2: solve_WF_matrix.
    rewrite <- kron_mixed_product.
    rewrite kron_assoc. 2,3,4: solve_WF_matrix.
    rewrite <- Mmult_assoc.
    assert (kron_mix_help: I 2 ⊗ (I 2 ⊗ W2) × (I 2 ⊗ (I 2 ⊗ (W2) †)) = 
    (I 2 × I 2) ⊗ ((I 2 ⊗ W2) × (I 2 ⊗ (W2) †))). apply kron_mixed_product.
    rewrite kron_mix_help at 1. clear kron_mix_help.
    assert (kron_mix_help: (I 2 ⊗ W2 × (I 2 ⊗ (W2) †)) =
    (I 2 × I 2) ⊗ (W2 × (W2) †)). apply kron_mixed_product.
    rewrite kron_mix_help at 1. clear kron_mix_help.
    rewrite W2dag_inv.
    rewrite Mmult_1_l. 2: solve_WF_matrix.
    rewrite id_kron. rewrite id_kron.
    rewrite Mmult_1_l. 2: solve_WF_matrix.
    unfold bcgate.
    reflexivity.
}
{
    unfold V3.
    repeat rewrite Mmult_assoc.
    assert (kron_mix_help: (I 2 ⊗ W2 × (∣0⟩ ⊗ ∣0⟩)) = ((I 2 × ∣0⟩)  ⊗ (W2 × ∣0⟩))). apply kron_mixed_product.
    rewrite kron_mix_help at 1. clear kron_mix_help.
    assert (wres: W2 × ∣0⟩ = w). lma'.
    rewrite wres.
    rewrite Mmult_1_l. 2: solve_WF_matrix.
    rewrite ow_mult at 1.
    rewrite kron_adjoint.
    assert (kron_mix_help: (W0) † ⊗ (W1) † × (psi ⊗ phi) = ((W0) † × psi) ⊗ ((W1) † × phi)). apply kron_mixed_product.
    rewrite kron_mix_help at 1. clear kron_mix_help.
    assert (w0res: (W0) † × psi = ∣0⟩).
    {
        unfold W0.
        rewrite Mplus_adjoint.
        rewrite Mmult_adjoint.
        rewrite Mmult_plus_distr_r.
        rewrite Mmult_assoc.
        rewrite inner_prod_1_decomp in psi_unit. 2,3: solve_WF_matrix.
        rewrite psi_unit.
        rewrite adjoint_involutive.
        rewrite Mmult_1_r. 2: solve_WF_matrix.
        rewrite Mmult_adjoint.
        rewrite Mmult_assoc.
        rewrite inner_prod_0_comm in psi_orth. 2,3: solve_WF_matrix.
        rewrite inner_prod_0_decomp in psi_orth. 2,3: solve_WF_matrix.
        rewrite psi_orth.
        rewrite Mmult_0_r.
        apply Mplus_0_r.  
    }
    rewrite w0res.
    assert (w1res: (W1) † × phi = ∣0⟩).
    {
        unfold W1.
        rewrite Mplus_adjoint.
        rewrite Mmult_adjoint.
        rewrite Mmult_plus_distr_r.
        rewrite Mmult_assoc.
        rewrite inner_prod_1_decomp in phi_unit. 2,3: solve_WF_matrix.
        rewrite phi_unit.
        rewrite adjoint_involutive.
        rewrite Mmult_1_r. 2: solve_WF_matrix.
        rewrite Mmult_adjoint.
        rewrite Mmult_assoc.
        rewrite inner_prod_0_comm in phi_orth. 2,3: solve_WF_matrix.
        rewrite inner_prod_0_decomp in phi_orth. 2,3: solve_WF_matrix.
        rewrite phi_orth.
        rewrite Mmult_0_r.
        apply Mplus_0_r.  
    }
    rewrite w1res.
    reflexivity.
}
Qed.

Lemma Mmult_qubit {n}: forall (U : Square n) (x : Vector n), 
WF_Unitary U -> WF_Qubit x -> WF_Qubit (U × x).
Proof.
intros.
destruct H0 as [pow_prop [WF_x x_unit]].
split. apply pow_prop.
split. solve_WF_matrix. apply H.
rewrite <- unitary_preserves_inner_prod.
all: assumption.
Qed. 

Lemma kron_qubit {n}: forall (u v : Vector n), 
WF_Qubit u -> WF_Qubit v -> WF_Qubit (u ⊗ v).
Proof.
intros.
destruct H as [pow_prop [WF_u u_unit]].
destruct H0 as [_ [WF_v v_unit]].
destruct pow_prop as [m m_prop].
split. exists (m*2)%nat. rewrite <- m_prop.
rewrite Nat.pow_mul_r. rewrite Nat.pow_2_r. reflexivity.
split. solve_WF_matrix.
rewrite kron_inner_prod.
rewrite u_unit, v_unit.
apply Cmult_1_r.
Qed.

Lemma acgate_tens_eq: forall (U : Square 4) (a b c d e f: Vector 2), 
WF_Matrix U -> WF_Matrix a -> WF_Matrix b -> WF_Matrix c -> WF_Matrix d -> WF_Matrix e -> WF_Matrix f ->
(acgate U) × (a ⊗ b ⊗ c) = d ⊗ e ⊗ f ->  U × (a ⊗ c) = d ⊗ f.
Proof.
intros U a b c d e f WF_U WF_a WF_b WF_c WF_d WF_e WF_f gate_eq.
unfold acgate in gate_eq.
rewrite <- swapbc_3q with (a:= d) in gate_eq. 2,3,4: assumption.
apply (f_equal (fun f => swapbc × f)) in gate_eq.
repeat rewrite Mmult_assoc in gate_eq.
Admitted.


Lemma a33: forall (V1 V2 V4: Square 4), 
WF_Unitary V1 -> WF_Unitary V2 -> WF_Unitary V4 -> 
(forall (x: Vector 2), WF_Qubit x -> (acgate V1) × (bcgate V2) × (∣0⟩ ⊗ x ⊗ ∣0⟩) = (bcgate V4)† × (∣0⟩ ⊗ x ⊗ ∣0⟩))
-> (exists (psi: Vector 2), WF_Qubit psi /\ 
    (forall (x: Vector 2), WF_Qubit x -> 
        exists (z: Vector 2), WF_Qubit z /\ V2 × (x ⊗ ∣0⟩) = psi ⊗ z)) -> 
exists (P0 P1: Square 2), V1 = ∣0⟩⟨0∣ ⊗ P0 .+ ∣1⟩⟨1∣ ⊗ P1.
Proof.
intros V1 V2 V4 V1_unitary V2_unitary V4_unitary gate_prop v2_tens.
assert (temp: WF_Unitary V4). assumption.
destruct temp as [WF_V4 V4_inv].
assert (a25_partial:= a25 V2 V2_unitary v2_tens).
destruct a25_partial as [Q0 [Q0_unitary [psi1 [psi1_qubit v2q0_prop]]]].
assert (temp: WF_Unitary Q0). assumption.
destruct temp as [WF_Q0 Q0_inv].
assert (temp: WF_Qubit psi1). assumption.
destruct temp as [_ [WF_psi1 psi1_unit]]. 
assert (intermediary_step: forall (x: Vector 2), WF_Qubit x -> 
acgate V1 × (∣0⟩ ⊗ psi1 ⊗ (Q0 × x)) = ∣0⟩ ⊗ ((V4) † × (x ⊗ ∣0⟩))).
{
    intros x x_qubit.
    assert (temp: WF_Qubit x). assumption. 
    destruct temp as [_ [WF_x x_unit]].
    rewrite kron_assoc. 2,3,4: solve_WF_matrix.
    rewrite <- v2q0_prop. 2: assumption.
    rewrite <- Mmult_1_l with (A:= ∣0⟩) at 1. 2: solve_WF_matrix.
    rewrite <- kron_mixed_product.
    assert (fold_help: I 2 ⊗ V2 = bcgate V2). unfold bcgate. reflexivity.
    rewrite fold_help at 1. clear fold_help.
    repeat rewrite <- Mmult_assoc.
    assert (assoc_help: (∣0⟩ ⊗ (x ⊗ ∣0⟩)) = (∣0⟩ ⊗ x ⊗ ∣0⟩)). symmetry. apply kron_assoc. 1,2,3: solve_WF_matrix.
    rewrite assoc_help at 1. clear assoc_help.
    rewrite gate_prop at 1. 2: assumption.
    rewrite bcgate_adjoint. 2: solve_WF_matrix.
    rewrite <- Mmult_1_l with (A:= ∣0⟩) at 3. 2: solve_WF_matrix.
    rewrite <- kron_mixed_product.
    unfold bcgate.
    rewrite kron_assoc. 2,3,4: solve_WF_matrix.
    reflexivity.
}
assert (v4_tens: forall (x: Vector 2), WF_Qubit x -> 
    exists (w: Vector 2), WF_Qubit w /\ V4† × (x ⊗ ∣0⟩) = psi1 ⊗ w).
{
    intros x x_qubit.
    assert (a22_partial:= a22 V1 ∣0⟩ psi1 (Q0 × x) ∣0⟩ (V4† × (x ⊗ ∣0⟩))).
    apply a22_partial.
    assumption.
    apply qubit0_qubit.
    assumption.
    apply Mmult_qubit. 1,2: assumption.
    apply qubit0_qubit.
    apply Mmult_qubit.
    apply transpose_unitary. assumption.
    apply (@kron_qubit 2).
    assumption. apply qubit0_qubit.
    apply intermediary_step.
    assumption.
}
assert (exists_v4_tens: (exists psi : Vector 2,
WF_Qubit psi /\
(forall x : Vector 2,
 WF_Qubit x ->
 exists phi : Vector 2,
   WF_Qubit phi /\ (V4) † × (x ⊗ ∣0⟩) = psi ⊗ phi))). exists psi1. split. assumption. apply v4_tens.
assert (V4t_unitary: WF_Unitary (V4) †). apply transpose_unitary. assumption.
assert (a25_partial_2:= a25 (V4) † V4t_unitary exists_v4_tens).
destruct a25_partial_2 as [Q1 [Q1_unitary [psi2 [psi2_qubit v4tq1_prop]]]].
assert (temp: WF_Unitary Q1). assumption.
destruct temp as [WF_Q1 Q1_inv].
assert (temp: WF_Qubit psi2). assumption.
destruct temp as [_ [WF_psi2 psi2_unit]]. 
assert (main: forall (x: Vector 2), WF_Qubit x -> 
acgate V1 × (∣0⟩ ⊗ psi1 ⊗ (Q0 × x)) = ∣0⟩ ⊗ psi2 ⊗ (Q1 × x)).
{
    intros x x_qubit.
    assert (temp: WF_Qubit x). assumption. 
    destruct temp as [_ [WF_x x_unit]].
    rewrite intermediary_step. 2: assumption.
    rewrite v4tq1_prop. 2: assumption.
    symmetry. rewrite kron_assoc. 2,3,4: solve_WF_matrix.
    reflexivity.
}
Admitted.