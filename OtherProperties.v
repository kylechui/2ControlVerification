Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.
From Proof Require Import MatrixHelpers.
From Proof Require Import SwapHelpers.
From Proof Require Import QubitHelpers.
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