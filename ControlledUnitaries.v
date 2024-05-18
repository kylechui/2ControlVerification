Require Import QuantumLib.Quantum.
Require Import QuantumLib.VecSet. 
Require Import QuantumLib.Matrix.
From Proof Require Import MatrixHelpers.
From Proof Require Import QubitHelpers.
From Proof Require Import UnitaryMatrices.
From Proof Require Import Swaps.
From Proof Require Import SwapHelpers.
From Proof Require Import Vectors.
From Proof Require Import GateHelpers.
From Proof Require Import AlgebraHelpers.
From Proof Require Import WFHelpers.

Lemma a17: forall (U : Square 4) (beta beta_p : Vector 2), 
WF_Unitary U -> WF_Qubit beta -> WF_Qubit beta_p -> ⟨ beta , beta_p ⟩ = C0 -> 
(exists (psi phi : Vector 2), WF_Matrix psi /\ WF_Matrix phi /\ U × (∣0⟩ ⊗ beta) = ∣0⟩ ⊗ psi /\ U × (∣0⟩ ⊗ beta_p) = ∣0⟩ ⊗ phi) -> 
exists (P00 P11 : Square 2), 
U = ∣0⟩⟨0∣ ⊗ P00 .+ ∣1⟩⟨1∣ ⊗ P11 /\ WF_Unitary P00 /\ WF_Unitary P11.
Proof.
intros U beta beta_p U_unitary beta_qubit beta_p_qubit beta_orth special_vectors.
destruct beta_qubit as [_ [WF_beta beta_norm]].
destruct beta_p_qubit as [_ [WF_beta_p beta_p_norm]].
destruct special_vectors as [psi [phi [ WF_psi [ WF_phi [U_beta U_beta_p]]]]].
set (Q := beta × ⟨0∣ .+  beta_p × ⟨1∣).
assert (Q_unitary: WF_Unitary Q).
{
  unfold WF_Unitary.
  split.
  solve_WF_matrix.
  unfold Q.
  rewrite Mplus_adjoint. repeat rewrite Mmult_adjoint.
  rewrite Mmult_plus_distr_l. repeat rewrite Mmult_plus_distr_r.
  rewrite Mmult_assoc. rewrite <- Mmult_assoc with (A := (beta) †).
  apply inner_prod_1_decomp in beta_norm. 3,2: assumption.
  rewrite beta_norm.
  rewrite Mmult_assoc with (A := (⟨1∣) †). rewrite <- Mmult_assoc with (A := (beta_p) †).
  assert (beta_p_orth: ⟨ beta_p, beta ⟩ = C0). apply inner_prod_0_comm. 1,2,3: assumption.
  apply inner_prod_0_decomp in beta_p_orth. 2,3: assumption.
  rewrite beta_p_orth.
  rewrite Mmult_assoc with (A := (⟨0∣) †). rewrite <- Mmult_assoc with (A := (beta) †).
  apply inner_prod_0_decomp in beta_orth. 2,3: assumption.
  rewrite beta_orth.
  rewrite Mmult_assoc with (A := (⟨1∣) †). rewrite <- Mmult_assoc with (A := (beta_p) †).
  apply inner_prod_1_decomp in beta_p_norm. 2,3: assumption.
  rewrite beta_p_norm.
  lma'.
}

assert (prod_decomp_1 : forall (w : Vector 2), WF_Matrix w -> U × (I 2 ⊗ Q) × (∣0⟩ ⊗ w) = ∣0⟩ ⊗ ((w 0%nat 0%nat) .* psi .+ (w 1%nat 0%nat) .* phi)).
{
    intros.
    assert (w_decomp: w = ((w 0%nat 0%nat) .* ∣0⟩ .+ (w 1%nat 0%nat) .* ∣1⟩)). lma'.
    rewrite w_decomp at 1.
    rewrite Mmult_assoc.
    assert (kron_mix_helper: (I 2 ⊗ Q × (∣0⟩ ⊗ (w 0%nat 0%nat .* ∣0⟩ .+ w 1%nat 0%nat .* ∣1⟩))) = 
    (I 2 × ∣0⟩) ⊗ (Q × (w 0%nat 0%nat .* ∣0⟩ .+ w 1%nat 0%nat .* ∣1⟩))).
    {
      destruct Q_unitary as [WF_Q _].
      lma'.
    }
    rewrite kron_mix_helper at 1.
    rewrite Mmult_1_l. 2: apply WF_qubit0.
    unfold Q.
    rewrite Mmult_plus_distr_l. do 2 rewrite Mmult_plus_distr_r.
    rewrite Mmult_assoc with (A := beta_p) (B := ⟨1∣ ).
    rewrite Mscale_mult_dist_r with (A:= ⟨1∣) (B:= ∣0⟩).
    rewrite Mmult10. rewrite Mscale_0_r. rewrite Mmult_0_r. rewrite Mplus_0_r.
    rewrite Mmult_assoc with (A := beta) (C := w 1%nat 0%nat .* ∣1⟩ ).
    rewrite Mscale_mult_dist_r with (A:= ⟨0∣) (B:= ∣1⟩).
    rewrite Mmult01. rewrite Mscale_0_r. rewrite Mmult_0_r. rewrite Mplus_0_l.
    rewrite Mmult_assoc with (A := beta).
    rewrite Mscale_mult_dist_r with (A:= ⟨0∣).
    rewrite Mmult00. 
    assert (beta_helper: (beta × (w 0%nat 0%nat .* I 1)) = w 0%nat 0%nat .* beta). lma'.
    rewrite beta_helper. clear beta_helper.
    rewrite Mmult_assoc.
    rewrite Mscale_mult_dist_r.
    rewrite Mmult11. 
    assert (beta_p_helper: (beta_p × (w 1%nat 0%nat .* I 1)) = w 1%nat 0%nat .* beta_p). lma'.
    rewrite beta_p_helper. clear beta_p_helper.
    rewrite kron_plus_distr_l.
    do 2 rewrite Mscale_kron_dist_r.
    rewrite Mmult_plus_distr_l.
    do 2 rewrite Mscale_mult_dist_r.
    rewrite U_beta at 1. rewrite U_beta_p at 1.
    lma'.
}
destruct (@block_decomp 2 U) as [P00 [P01 [P10 [P11 [WF_P00 [WF_P01 [WF_P10 [WF_P11 U_block_decomp]]]]]]]].
apply U_unitary.
assert (prod_decomp_2: forall (w : Vector 2), WF_Matrix w -> U × (I 2 ⊗ Q) × (∣0⟩ ⊗ w) = ∣0⟩ ⊗ (P00 × Q × w) .+ ∣1⟩ ⊗ (P10 × Q × w)).
{
    intros w WF_w.
    rewrite Mmult_assoc.
    assert (kron_mix_helper: (I 2 ⊗ Q × (∣0⟩ ⊗ w)) = (I 2 × ∣0⟩) ⊗ (Q × w)).
    {
      destruct Q_unitary as [WF_Q _].
      lma'.
    }
    rewrite kron_mix_helper at 1. clear kron_mix_helper.
    rewrite Mmult_1_l. 2: apply WF_qubit0.
    rewrite U_block_decomp.
    do 3 rewrite Mmult_plus_distr_r.
    rewrite kron_mixed_product. rewrite Mmult_assoc. rewrite Mmult00. rewrite Mmult_1_r. 2: apply WF_qubit0.
    rewrite kron_mixed_product. rewrite Mmult_assoc. rewrite Mmult10. rewrite Mmult_0_r. rewrite kron_0_l. rewrite Mplus_0_r.
    rewrite kron_mixed_product. rewrite Mmult_assoc. rewrite Mmult00. rewrite Mmult_1_r. 2: apply WF_qubit1.
    rewrite kron_mixed_product. rewrite Mmult_assoc. rewrite Mmult10. rewrite Mmult_0_r. rewrite kron_0_l. rewrite Mplus_0_r.
    do 2 rewrite <- Mmult_assoc.
    reflexivity.
}
assert (tens_elem_2: forall (w: Vector 2), WF_Matrix w ->(∣1⟩ ⊗ (P10 × Q × w)) 2%nat 0%nat = C0).
{
    intros w WF_w.
    assert (U20_equiv: (∣1⟩ ⊗ (P10 × Q × w)) 2%nat 0%nat = (U × (I 2 ⊗ Q) × (∣0⟩ ⊗ w)) 2%nat 0%nat).
    {
        rewrite prod_decomp_2. 2: assumption.
        lca.
    }
    rewrite U20_equiv.
    rewrite prod_decomp_1. 2: assumption.
    lca.
}
assert (tens_elem_3: forall (w: Vector 2), WF_Matrix w ->(∣1⟩ ⊗ (P10 × Q × w)) 3%nat 0%nat = C0).
{
    intros w WF_w.
    assert (U30_equiv: (∣1⟩ ⊗ (P10 × Q × w)) 3%nat 0%nat = (U × (I 2 ⊗ Q) × (∣0⟩ ⊗ w)) 3%nat 0%nat).
    {
        rewrite prod_decomp_2. 2: assumption.
        lca.
    }
    rewrite U30_equiv.
    rewrite prod_decomp_1. 2: assumption.
    lca.
}
assert (tens_equiv_0: forall (w: Vector 2), WF_Matrix w ->(∣1⟩ ⊗ (P10 × Q × w)) = (Zero (m:=4) (n:=1))).
{
    intros w WF_w.
    destruct Q_unitary as [WF_Q _].
    lma'.
    apply tens_elem_2. assumption.
    apply tens_elem_3. assumption.
}
assert (prod_equiv_0: forall (w: Vector 2), WF_Matrix w -> P10 × Q × w = (Zero (m:=2) (n:=1))).
{
    intros w WF_w.
    assert (zero_tens: (Zero (m:=4) (n:=1)) = ∣1⟩ ⊗ (Zero (m:=2) (n:=1))). lma'.
    rewrite zero_tens in tens_equiv_0.
    apply kron_1_cancel_l; solve_WF_matrix.
    apply tens_equiv_0.
    assumption.
}
assert (P10Q_0: P10 × Q = Zero).
{
    apply vector_mult_simplify; solve_WF_matrix.
    intros.
    rewrite Mmult_0_l.
    apply prod_equiv_0.
    assumption.
}
assert (P10_0: P10 = Zero).
{
    apply unitary_mult_zero_cancel_r with (B := Q).
    all: assumption.
}
assert (P01_0: P01 = Zero).
{
    apply a9 with (V:=U) (P00 := P00) (P01:= P01) (P10 := P10) (P11:= P11).
    all: assumption.
}
exists P00, P11.
assert (U_adj_block_decomp: (U) † = ∣0⟩⟨0∣ ⊗ P00† .+ ∣0⟩⟨1∣ ⊗ P10† .+ ∣1⟩⟨0∣ ⊗ P01† .+ ∣1⟩⟨1∣ ⊗ P11†). 
{
    rewrite U_block_decomp. lma'.
    apply WF_adjoint. 1,2: apply (@WF_blockmatrix 2).
    5,6,7,8: apply WF_adjoint. all: assumption.
}
assert (U_adj_mult_1: (U) † × U = ∣0⟩⟨0∣ ⊗ (P00† × P00) .+ ∣0⟩⟨1∣ ⊗ Zero .+ ∣1⟩⟨0∣ ⊗ Zero .+ ∣1⟩⟨1∣ ⊗ (P11† × P11)).
{
    rewrite P10_0 in U_adj_block_decomp. rewrite zero_adjoint_eq in U_adj_block_decomp. 
    rewrite P10_0 in U_block_decomp.
    rewrite P01_0 in U_adj_block_decomp. rewrite zero_adjoint_eq in U_adj_block_decomp. 
    rewrite P01_0 in U_block_decomp.
    rewrite (@block_multiply 2) with (U := (U) †) (V := U)
    (P00 := P00†) (P01 := (Zero (m:= 2) (n:=2))) (P10 := (Zero (m:= 2) (n:=2))) (P11 := P11†)
    (Q00 := P00) (Q01 := (Zero (m:= 2) (n:=2))) (Q10 := (Zero (m:= 2) (n:=2))) (Q11 := P11) at 1; solve_WF_matrix.
    2,3: assumption.
    Msimpl_light; reflexivity.
}
assert (I_4_block_decomp: I 4 = ∣0⟩⟨0∣ ⊗ I 2 .+ ∣0⟩⟨1∣ ⊗ Zero .+ ∣1⟩⟨0∣ ⊗ Zero .+ ∣1⟩⟨1∣ ⊗ I 2). 
{
    lma'. apply (@WF_blockmatrix 2); solve_WF_matrix.
}
assert (equal_blocks: (P00) † × P00 = I 2 /\ (Zero (m:= 2) (n:=2)) = (Zero (m:= 2) (n:=2)) 
/\ (Zero (m:= 2) (n:=2)) = (Zero (m:= 2) (n:=2)) /\ (P11) † × P11 = I 2).
{
    apply block_equalities with (U := (U) † × U) (V := I 4); solve_WF_matrix.
    lia.
    1,2: assumption.
    apply U_unitary.
}
split.
{
    rewrite U_block_decomp.
    rewrite P10_0, P01_0.
    lma'.
    apply (@WF_blockmatrix 2); solve_WF_matrix.
}
split. 
{
    unfold WF_Unitary.
    split. assumption.
    apply equal_blocks.   
}
{
    unfold WF_Unitary.
    split. assumption.
    apply equal_blocks.   
}
Qed.

Lemma a18: forall (U : Square 4), 
WF_Unitary U -> 
(forall (beta: Vector 2), WF_Matrix beta -> U × (beta ⊗ ∣0⟩) = beta ⊗ ∣0⟩) -> 
exists (P1 : Square 2), 
U = I 2 ⊗ ∣0⟩⟨0∣ .+ P1 ⊗ ∣1⟩⟨1∣ /\ WF_Unitary P1.
Proof.
intros U U_unitary tens_eigenvec.
assert (SUS_tens_eigenvec: forall (beta: Vector 2), WF_Matrix beta -> (swap × U × swap)× (∣0⟩⊗ beta) = ∣0⟩⊗ beta).
{
    intros.
    repeat rewrite Mmult_assoc.
    rewrite a10. 2: apply WF_qubit0. 2: assumption.
    rewrite tens_eigenvec.
    rewrite a10. 2: assumption. 2: apply WF_qubit0.
    reflexivity.
    assumption.
}
assert (SUS_block_decomp: exists (P0 P1: Square 2), (swap × U × swap) = ∣0⟩⟨0∣ ⊗ P0 .+ ∣1⟩⟨1∣ ⊗ P1 /\
WF_Unitary P0 /\ WF_Unitary P1).
{
    apply a17 with (beta := ∣0⟩) (beta_p := ∣1⟩). 3: apply qubit1_qubit. 2: apply qubit0_qubit.
    apply Mmult_unitary. apply Mmult_unitary. 1,3: apply swap_unitary. assumption.
    lca.
    exists ∣0⟩,∣1⟩.
    split. apply WF_qubit0.
    split. apply WF_qubit1.
    split. apply SUS_tens_eigenvec. apply WF_qubit0.
    apply SUS_tens_eigenvec. apply WF_qubit1.
}
destruct SUS_block_decomp as [P0 [P1 [SUS_block_decomp [P0_unitary P1_unitary]]]].
assert (U_block_decomp: exists (P0 P1 : Square 2), U = P0 ⊗ ∣0⟩⟨0∣ .+ P1 ⊗ ∣1⟩⟨1∣ /\ WF_Unitary P0 /\ WF_Unitary P1).
{
    exists P0,P1.
    split. 2: split. 2,3: assumption.
    apply (f_equal (fun f => swap × f × swap)) in SUS_block_decomp.
    assert (swap_inverse_helper: swap × (swap × U × swap) × swap = U).
    {
        repeat rewrite <- Mmult_assoc.
        rewrite swap_swap.
        rewrite Mmult_1_l. 2: apply U_unitary.
        rewrite Mmult_assoc.
        (* @Kyle for some reason swap_swap doesn't work here *)
        lma'. 2: apply U_unitary.
        apply WF_mult. apply U_unitary.
        apply WF_mult. 1,2: apply WF_swap.
    }
    rewrite swap_inverse_helper in SUS_block_decomp.
    rewrite SUS_block_decomp.
    rewrite Mmult_plus_distr_l. rewrite Mmult_plus_distr_r.
    repeat rewrite a11; solve_WF_matrix.
    reflexivity.
}
clear P0 P1 P0_unitary P1_unitary SUS_block_decomp.
destruct U_block_decomp as [P0 [P1 [U_block_decomp [P0_unitary P1_unitary]]]].
assert (U_P0_tens_decomp: forall (w: Vector 2),  U × (w ⊗ ∣0⟩) = (P0 × w)⊗ ∣0⟩).
{
    intros.
    rewrite U_block_decomp.
    rewrite Mmult_plus_distr_r.
    rewrite kron_mixed_product.
    rewrite kron_mixed_product.
    rewrite Mmult_assoc. rewrite Mmult00. rewrite Mmult_1_r. 2: apply WF_qubit0.
    rewrite Mmult_assoc. rewrite Mmult10. rewrite Mmult_0_r.
    rewrite kron_0_r. rewrite Mplus_0_r.
    reflexivity.
}
assert (P0_I_same_transform: forall (w: Vector 2), WF_Matrix w -> P0 × w = w).
{
    intros.
    apply kron_0_cancel_r. 2: assumption.
    apply WF_mult. apply P0_unitary. assumption.
    rewrite <- U_P0_tens_decomp.
    rewrite tens_eigenvec.
    reflexivity.
    assumption. 
}
assert (P0_I: P0 = I 2).
{
    apply vector_mult_simplify. apply P0_unitary. apply WF_I.
    intros.
    rewrite Mmult_1_l. 2: assumption.
    apply P0_I_same_transform. assumption.
}
exists P1.
split.
rewrite <- P0_I. all: assumption.
Qed.

Lemma a19: forall (U : Square 4) (phi2q w : Vector 4), 
WF_Unitary U -> WF_Matrix phi2q -> WF_Matrix w -> ⟨ phi2q , phi2q ⟩ = C1 -> ⟨ w , w ⟩ = C1 -> 
Entangled phi2q -> acgate U × (∣0⟩ ⊗ phi2q) = ∣0⟩ ⊗ w -> 
exists(P0 P1: Square 2), 
U = ∣0⟩⟨0∣ ⊗ P0 .+ ∣1⟩⟨1∣ ⊗ P1 /\ WF_Unitary P0 /\ WF_Unitary P1.
Proof. 
intros U phi2q w U_unitary WF_phi2q WF_w phi2q_unit w_unit phi2q_entangled Uac_property.
assert (schmidt_decomp := a14 phi2q WF_phi2q phi2q_unit).
destruct schmidt_decomp as [beta [beta_p [gamma [gamma_p [r [qubit_beta [qubit_beta_p [qubit_gamma [qubit_gamma_p [beta_orth [gamma_orth [schmidt_decomp [rge0 [rle1 tensorprod_impl]]]]]]]]]]]]]].
assert (tens_w_decomp: ∣0⟩ ⊗ w = √ r .* (acgate U × (∣0⟩ ⊗ beta ⊗ gamma)) .+ √ (1-r) .* (acgate U × (∣0⟩ ⊗ beta_p ⊗ gamma_p))).
{
    rewrite <- Uac_property.
    rewrite schmidt_decomp.
    rewrite kron_plus_distr_l.
    do 2 rewrite Mscale_kron_dist_r.
    rewrite Mmult_plus_distr_l.
    do 2 rewrite Mscale_mult_dist_r.
    repeat rewrite <- kron_assoc; solve_WF_matrix.
    reflexivity.
}
assert (qubit_w: WF_Qubit w).
{
    unfold WF_Qubit.
    split. exists 2%nat. trivial.
    split. all: assumption.
}
assert (w_beta_decomp := a15 beta beta_p w qubit_beta qubit_beta_p qubit_w beta_orth).
destruct w_beta_decomp as [psi [phi [w_beta_decomp [WF_psi WF_phi]]]].
assert (Main: ∣0⟩ ⊗ psi ⊗ beta .+ ∣0⟩ ⊗ phi ⊗ beta_p =
(√ r .* (U × (∣0⟩ ⊗ gamma))) ⊗ beta
.+ (√ (1-r) .* (U × (∣0⟩ ⊗ gamma_p))) ⊗ beta_p).
{
    destruct qubit_beta as [_ [WF_beta beta_unit]].
    destruct qubit_beta_p as [_ [WF_beta_p beta_p_unit]].
    destruct qubit_gamma as [_ [WF_gamma gamma_unit]].
    destruct qubit_gamma_p as [_ [WF_gamma_p gamma_p_unit]].
    assert (Step1: ∣0⟩ ⊗ psi ⊗ beta .+ ∣0⟩ ⊗ phi ⊗ beta_p = swapbc × (∣0⟩ ⊗ (beta ⊗ psi) .+ ∣0⟩ ⊗ (beta_p ⊗ phi))).
    {
        rewrite <- swapbc_3q; solve_WF_matrix.
        rewrite <- swapbc_3q with (b := beta_p); solve_WF_matrix.
        rewrite <- Mmult_plus_distr_l.
        rewrite kron_assoc; solve_WF_matrix.
        rewrite kron_assoc; solve_WF_matrix.
        reflexivity.
    }
    rewrite Step1. clear Step1.
    assert (Step2: swapbc × (∣0⟩ ⊗ (beta ⊗ psi) .+ ∣0⟩ ⊗ (beta_p ⊗ phi)) = swapbc × (∣0⟩ ⊗ w)).
    {
        rewrite <- kron_plus_distr_l.
        rewrite <- w_beta_decomp.
        reflexivity.   
    }
    rewrite Step2. clear Step2.
    (* Step 3*)
    rewrite tens_w_decomp.
    (* Step 4 *)
    rewrite Mmult_plus_distr_l.
    do 2 rewrite Mscale_mult_dist_r.
    (* Step 5 *)
    rewrite <- Mmult_1_r with (A:= acgate U). 2: apply WF_acgate. 2: apply U_unitary.
    simpl.
    rewrite <- swapbc_inverse.
    assert (Step6: √ r .* (swapbc × (acgate U × (swapbc × swapbc) × (∣0⟩ ⊗ beta ⊗ gamma)))
    .+ √ (1 - r) .* (swapbc × (acgate U × (swapbc × swapbc) × (∣0⟩ ⊗ beta_p ⊗ gamma_p))) = 
    √ r .* ((abgate U × (∣0⟩ ⊗ gamma ⊗ beta))) .+ √ (1 - r) .* (abgate U × (∣0⟩ ⊗ gamma_p ⊗ beta_p))).
    {
        unfold acgate.
        rewrite Mmult_assoc. rewrite swapbc_inverse.
        rewrite Mmult_1_l. rewrite Mmult_1_r.
        repeat rewrite <- Mmult_assoc.
        rewrite swapbc_inverse.
        rewrite Mmult_1_l. 2: apply WF_abgate. 2: apply U_unitary. 2: apply WF_mult. 2: apply WF_mult.
        2,4: apply WF_swapbc. 2: apply WF_abgate. 2: apply U_unitary. 2: solve_WF_matrix.
        rewrite Mmult_assoc.
        rewrite swapbc_3q; solve_WF_matrix.
        rewrite Mmult_assoc.
        rewrite swapbc_3q; solve_WF_matrix.
        reflexivity.
    }
    rewrite Step6 at 1. clear Step6.
    (* Step7 *)
    unfold abgate.
    rewrite kron_mixed_product. rewrite kron_mixed_product.
    Msimpl_light; solve_WF_matrix.
    repeat rewrite <- Mscale_kron_dist_l.
    reflexivity.
}
(* Moving terms in main to apply a16*)
apply (f_equal (fun f => f .+ Mopp (∣0⟩ ⊗ phi ⊗ beta_p))) in Main.
rewrite Mplus_assoc in Main.
rewrite Mplus_opp_0_r in Main. 2: solve_WF_matrix.
rewrite Mplus_0_r in Main.
rewrite Mplus_assoc in Main.
rewrite kron_opp_distr_l in Main; solve_WF_matrix.
rewrite <- kron_plus_distr_r in Main.
apply (f_equal (fun f => Mopp (∣0⟩ ⊗ psi ⊗ beta) .+ f)) in Main.
rewrite Mplus_opp_0_l in Main; solve_WF_matrix.
rewrite kron_opp_distr_l in Main; solve_WF_matrix.
rewrite <- Mplus_assoc in Main.
rewrite Mplus_comm with (A := Mopp (∣0⟩ ⊗ psi) ⊗ beta) in Main.
rewrite <- kron_plus_distr_r in Main.
assert ((√ r .* (U × (∣0⟩ ⊗ gamma)) .+ Mopp (∣0⟩ ⊗ psi)) = Zero /\
(√ (1 - r) .* (U × (∣0⟩ ⊗ gamma_p)) .+ Mopp (∣0⟩ ⊗ phi)) = Zero).
{
    destruct qubit_gamma as [_ [WF_gamma gamma_unit]].
    destruct qubit_gamma_p as [_ [WF_gamma_p gamma_p_unit]].
    apply a16 with (a0:= beta) (a1 := beta_p); solve_WF_matrix.
    apply orthonormal_implies_lin_indep_2; solve_WF_matrix.
    apply qubit_beta.
    apply qubit_beta_p.
    assumption.
    symmetry; assumption.
}
destruct H as [U_g U_g_p].
assert (entangled_prop: Entangled phi2q -> not (r = 0 \/ r = 1)).
{
    unfold Entangled.
    intro not_tensor_prod.
    intro r01.
    apply tensorprod_impl in r01.
    apply not_tensor_prod.
    apply r01.
}
assert (rneq: r <> 0 /\ r <> 1).
{
    apply Coq.Logic.Classical_Prop.not_or_and.
    apply entangled_prop.
    assumption.
}
destruct rneq as [rneq0 rneq1].
assert (rsqrt_neq_0: √ r <> 0).
{
    intro sqrt_r_eq_0.
    apply rneq0.
    apply sqrt_eq_0.
    apply Rge_le. all: assumption.
}
assert (r1sqrt_neq_0: √ (1-r) <> 0).
{
    intro sqrt_1r_eq_0.
    apply rneq1.
    rewrite <- Rplus_0_r with (r := r).
    rewrite <- Rplus_0_r.
    rewrite <- (Rminus_diag_eq r r) at 2. 2: reflexivity.
    unfold Rminus.
    rewrite <- Rplus_assoc.
    rewrite Rplus_comm with (r1:= 1).
    rewrite Rplus_assoc.
    apply Rplus_eq_compat_l.
    symmetry.
    apply sqrt_eq_0.
    rewrite <- (Rminus_diag_eq r r). 2: reflexivity.
    apply Rplus_le_compat_r. all: assumption.
}
(* move around values to prep for a17 application *)
apply (f_equal (fun f => f .+ ∣0⟩ ⊗ psi)) in U_g.
rewrite Mplus_assoc in U_g.
rewrite Mplus_opp_0_l in U_g; solve_WF_matrix.
rewrite Mplus_0_l in U_g. rewrite Mplus_0_r in U_g.
apply (f_equal (fun f => /√ r .* f)) in U_g.
rewrite Mscale_assoc in U_g.
rewrite Cinv_l in U_g. 2: apply RtoC_neq. 2: assumption.
rewrite Mscale_1_l in U_g.
rewrite <- Mscale_kron_dist_r in U_g.
apply (f_equal (fun f => f .+ ∣0⟩ ⊗ phi)) in U_g_p.
rewrite Mplus_assoc in U_g_p.
rewrite Mplus_opp_0_l in U_g_p; solve_WF_matrix.
rewrite Mplus_0_l in U_g_p. rewrite Mplus_0_r in U_g_p.
apply (f_equal (fun f => /√ (1 - r) .* f)) in U_g_p.
rewrite Mscale_assoc in U_g_p.
rewrite Cinv_l in U_g_p. 2: apply RtoC_neq. 2: assumption.
rewrite Mscale_1_l in U_g_p.
rewrite <- Mscale_kron_dist_r in U_g_p.
apply a17 with (beta := gamma) (beta_p := gamma_p).
1,2,3,4: assumption.
exists (/ √ r .* psi), (/ √ (1 - r) .* phi).
split. solve_WF_matrix.
split. solve_WF_matrix.
split. all: assumption.
Qed.
