Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.
Require Import QuantumLib.VectorStates.
Require Import QuantumLib.Eigenvectors.
From Proof Require Import QubitHelpers.
From Proof Require Import MatrixHelpers.
From Proof Require Import AlgebraHelpers.

Lemma a14 : forall (psi : Vector 4), 
WF_Matrix psi -> ⟨ psi , psi ⟩ = 1 -> 
exists (beta beta_p gamma gamma_p: Vector 2) (r : R),
WF_Qubit beta /\ WF_Qubit beta_p /\ WF_Qubit gamma /\ WF_Qubit gamma_p /\
⟨ beta , beta_p ⟩ = 0 /\ ⟨ gamma , gamma_p ⟩ = 0 /\
psi = √ (r) .* (beta ⊗ gamma) .+ √ (1-r) .* (beta_p ⊗ gamma_p) /\ r >= 0 /\ r <= 1
/\ ((r = 0 \/ r = 1) -> TensorProd psi).
Proof.
intros psi WF_psi psi_unit_vector.
assert (psi_decomp: psi = (psi 0 0)%nat .* ∣0,0⟩ .+ (psi 1 0)%nat .* ∣0,1⟩ .+ (psi 2 0)%nat .* ∣1,0⟩ .+ (psi 3 0)%nat .* ∣1,1⟩).
{
  lma'. solve_WF_matrix.
}
set (A := (fun x y =>
match (x,y) with
| (0,0) => (psi 0 0)%nat
| (0,1) => (psi 1 0)%nat
| (1,0) => (psi 2 0)%nat
| (1,1) => (psi 3 0)%nat
| _ => C0
end) : (Square 2)).
assert (exists_svd_A: exists (U L V: Square 2), WF_Unitary U /\ WF_Unitary V /\ WF_Diagonal L /\ WF_Nonnegative L /\ A = U × L × V). apply SVD_2.
destruct exists_svd_A as [U [L [V [unitary_U [unitary_V [diag_L [nonneg_L A_decomp]]]]]]].
assert (A_elem_decomp: forall (j k: nat), A j k = U j 0%nat * L 0%nat 0%nat * V 0%nat k + U j 1%nat * L 1%nat 1%nat * V 1%nat k).
{
  intros.
  rewrite A_decomp.
  unfold Mmult. simpl. Csimpl.
  destruct diag_L as [WF_L ndiag_0_L].
  assert (L10_0: L 1%nat 0%nat = 0). apply ndiag_0_L. lia.
  assert (L01_0: L 0%nat 1%nat = 0). apply ndiag_0_L. lia.
  rewrite L10_0. rewrite L01_0. Csimpl.
  reflexivity.
}
clear A_decomp.
assert (psi_alt: psi = (U 0%nat 0%nat * L 0%nat 0%nat * V 0%nat 0%nat +
U 0%nat 1%nat * L 1%nat 1%nat * V 1%nat 0%nat) .* ∣ 0, 0 ⟩ .+ (U 0%nat 0%nat * L 0%nat 0%nat * V 0%nat 1%nat +
U 0%nat 1%nat * L 1%nat 1%nat * V 1%nat 1%nat) .* ∣ 0, 1 ⟩
.+ (U 1%nat 0%nat * L 0%nat 0%nat * V 0%nat 0%nat +
U 1%nat 1%nat * L 1%nat 1%nat * V 1%nat 0%nat) .* ∣ 1, 0 ⟩ .+ 
(U 1%nat 0%nat * L 0%nat 0%nat * V 0%nat 1%nat +
U 1%nat 1%nat * L 1%nat 1%nat * V 1%nat 1%nat) .* ∣ 1, 1 ⟩).
{
  assert (psi_0: (U 0%nat 0%nat * L 0%nat 0%nat * V 0%nat 0%nat +
  U 0%nat 1%nat * L 1%nat 1%nat * V 1%nat 0%nat) = psi 0%nat 0%nat). rewrite <- A_elem_decomp. unfold A. reflexivity.
  assert (psi_1: (U 0%nat 0%nat * L 0%nat 0%nat * V 0%nat 1%nat +
  U 0%nat 1%nat * L 1%nat 1%nat * V 1%nat 1%nat) = psi 1%nat 0%nat). rewrite <- A_elem_decomp. unfold A. reflexivity.
  assert (psi_2: (U 1%nat 0%nat * L 0%nat 0%nat * V 0%nat 0%nat +
  U 1%nat 1%nat * L 1%nat 1%nat * V 1%nat 0%nat) = psi 2%nat 0%nat). rewrite <- A_elem_decomp. unfold A. reflexivity.
  assert (psi_3: (U 1%nat 0%nat * L 0%nat 0%nat * V 0%nat 1%nat +
  U 1%nat 1%nat * L 1%nat 1%nat * V 1%nat 1%nat) = psi 3%nat 0%nat). rewrite <- A_elem_decomp. unfold A. reflexivity.
  rewrite psi_0. rewrite psi_1. rewrite psi_2. rewrite psi_3.
  apply psi_decomp.
}
clear psi_decomp A_elem_decomp A.
assert (tensor_decomp: psi = L 0%nat 0%nat .* ((U 0%nat 0%nat .* ∣0⟩ .+ U 1%nat 0%nat .* ∣1⟩) ⊗ (V 0%nat 0%nat .* ∣0⟩ .+ V 0%nat 1%nat .* ∣1⟩))
.+ L 1%nat 1%nat .* ((U 0%nat 1%nat .* ∣0⟩ .+ U 1%nat 1%nat .* ∣1⟩) ⊗ (V 1%nat 0%nat .* ∣0⟩ .+ V 1%nat 1%nat .* ∣1⟩))).
{
  rewrite psi_alt. lma'.
  solve_WF_matrix. solve_WF_matrix.
}
clear psi_alt.
set (beta := (U 0%nat 0%nat .* ∣0⟩ .+ U 1%nat 0%nat .* ∣1⟩)).
set (gamma := (V 0%nat 0%nat .* ∣0⟩ .+ V 0%nat 1%nat .* ∣1⟩)).
set (beta_p := (U 0%nat 1%nat .* ∣0⟩ .+ U 1%nat 1%nat .* ∣1⟩)).
set (gamma_p := (V 1%nat 0%nat .* ∣0⟩ .+ V 1%nat 1%nat .* ∣1⟩)).
set (r := ((Re (L 0%nat 0%nat))^2)%R).
assert (beta_qubit: WF_Qubit beta).
{
  unfold WF_Qubit.
  split. exists 1%nat. trivial.
  split. solve_WF_matrix.
  unfold beta.
  rewrite inner_product_plus_l. 
  do 2 rewrite inner_product_plus_r.
  repeat rewrite inner_product_scale_l.
  repeat rewrite inner_product_scale_r.
  unfold inner_product.
  rewrite Mmult00, Mmult01, Mmult10, Mmult11. 
  Csimpl.
  destruct unitary_U as [WF_U U_unit_prop].
  assert (mat_element_decomp: (U 0%nat 0%nat) ^* * U 0%nat 0%nat + (U 1%nat 0%nat) ^* * U 1%nat 0%nat = 
  ((U) † × U) 0%nat 0%nat). lca.
  rewrite mat_element_decomp. rewrite U_unit_prop. lca. 
}
assert (beta_p_qubit: WF_Qubit beta_p).
{
  unfold WF_Qubit.
  split. exists 1%nat. trivial.
  split. solve_WF_matrix.
  unfold beta_p.
  rewrite inner_product_plus_l. 
  do 2 rewrite inner_product_plus_r.
  repeat rewrite inner_product_scale_l.
  repeat rewrite inner_product_scale_r.
  unfold inner_product.
  rewrite Mmult00, Mmult01, Mmult10, Mmult11. 
  Csimpl.
  destruct unitary_U as [WF_U U_unit_prop].
  assert (mat_element_decomp: (U 0%nat 1%nat) ^* * U 0%nat 1%nat + (U 1%nat 1%nat) ^* * U 1%nat 1%nat = 
  ((U) † × U) 1%nat 1%nat). lca.
  rewrite mat_element_decomp. rewrite U_unit_prop. lca. 
}
assert (gamma_qubit: WF_Qubit gamma).
{
  unfold WF_Qubit.
  split. exists 1%nat. trivial.
  split. solve_WF_matrix.
  unfold gamma.
  rewrite inner_product_plus_l. 
  do 2 rewrite inner_product_plus_r.
  repeat rewrite inner_product_scale_l.
  repeat rewrite inner_product_scale_r.
  unfold inner_product.
  rewrite Mmult00, Mmult01, Mmult10, Mmult11. 
  Csimpl.
  apply transpose_unitary in unitary_V.
  destruct unitary_V as [WF_Vdag Vdag_unit_prop].
  rewrite adjoint_involutive in Vdag_unit_prop.
  assert (mat_element_decomp: (V 0%nat 0%nat) ^* * V 0%nat 0%nat + (V 0%nat 1%nat) ^* * V 0%nat 1%nat = 
  (V × (V) †) 0%nat 0%nat). lca.
  rewrite mat_element_decomp. rewrite Vdag_unit_prop. lca.
}
assert (gamma_p_qubit: WF_Qubit gamma_p).
{
  unfold WF_Qubit.
  split. exists 1%nat. trivial.
  split. solve_WF_matrix.
  unfold gamma_p.
  rewrite inner_product_plus_l. 
  do 2 rewrite inner_product_plus_r.
  repeat rewrite inner_product_scale_l.
  repeat rewrite inner_product_scale_r.
  unfold inner_product.
  rewrite Mmult00, Mmult01, Mmult10, Mmult11. 
  Csimpl.
  apply transpose_unitary in unitary_V.
  destruct unitary_V as [WF_Vdag Vdag_unit_prop].
  rewrite adjoint_involutive in Vdag_unit_prop.
  assert (mat_element_decomp: (V 1%nat 0%nat) ^* * V 1%nat 0%nat + (V 1%nat 1%nat) ^* * V 1%nat 1%nat = 
  (V × (V) †) 1%nat 1%nat). lca.
  rewrite mat_element_decomp. rewrite Vdag_unit_prop. lca.
}
assert (beta_orth : ⟨ beta, beta_p ⟩ = 0).
{
  unfold beta, beta_p.
  rewrite inner_product_plus_l. 
  do 2 rewrite inner_product_plus_r.
  repeat rewrite inner_product_scale_l.
  repeat rewrite inner_product_scale_r.
  unfold inner_product.
  rewrite Mmult00, Mmult01, Mmult10, Mmult11. 
  Csimpl.
  destruct unitary_U as [WF_U U_unit_prop].
  assert (mat_element_decomp: (U 0%nat 0%nat) ^* * U 0%nat 1%nat + (U 1%nat 0%nat) ^* * U 1%nat 1%nat = 
  ((U) † × U) 0%nat 1%nat). lca.
  rewrite mat_element_decomp. rewrite U_unit_prop. lca.
}
assert (gamma_orth : ⟨ gamma, gamma_p ⟩ = 0).
{
  unfold gamma, gamma_p.
  rewrite inner_product_plus_l. 
  do 2 rewrite inner_product_plus_r.
  repeat rewrite inner_product_scale_l.
  repeat rewrite inner_product_scale_r.
  unfold inner_product.
  rewrite Mmult00, Mmult01, Mmult10, Mmult11. 
  Csimpl.
  apply transpose_unitary in unitary_V.
  destruct unitary_V as [WF_Vdag Vdag_unit_prop].
  rewrite adjoint_involutive in Vdag_unit_prop.
  assert (mat_element_decomp: (V 0%nat 0%nat) ^* * V 1%nat 0%nat + (V 0%nat 1%nat) ^* * V 1%nat 1%nat = 
  (V × (V) †) 1%nat 0%nat). lca.
  rewrite mat_element_decomp. rewrite Vdag_unit_prop. lca.
}
exists beta,beta_p,gamma,gamma_p,r.
split. assumption.
split. assumption.
split. assumption.
split. assumption.
split. apply beta_orth.
split. apply gamma_orth.
assert (unit_coefs: (L 0%nat 0%nat) ^* * L 0%nat 0%nat + (L 1%nat 1%nat) ^* * L 1%nat 1%nat =
C1).
{
  set (v := (U 0%nat 0%nat .* ∣0⟩ .+ U 1%nat 0%nat .* ∣1⟩) ⊗ (V 0%nat 0%nat .* ∣0⟩ .+ V 0%nat 1%nat .* ∣1⟩) : Vector 4).
  fold v in tensor_decomp.
  set (w := (U 0%nat 1%nat .* ∣0⟩ .+ U 1%nat 1%nat .* ∣1⟩) ⊗ (V 1%nat 0%nat .* ∣0⟩ .+ V 1%nat 1%nat .* ∣1⟩) : Vector 4).
  fold w in tensor_decomp.
  apply (amplitudes_of_unit (L 0%nat 0%nat) (L 1%nat 1%nat) psi v w).
  apply tensor_decomp.
  apply psi_unit_vector.
  {
    unfold v.
    set (a := (U 0%nat 0%nat .* ∣0⟩ .+ U 1%nat 0%nat .* ∣1⟩)).
    set (b := (V 0%nat 0%nat .* ∣0⟩ .+ V 0%nat 1%nat .* ∣1⟩)).
    rewrite kron_inner_prod with (u := a) (w := b) at 1.
    unfold a,b.
    repeat rewrite inner_product_plus_l. repeat rewrite inner_product_plus_r.
    repeat rewrite inner_product_scale_l. repeat rewrite inner_product_scale_r.
    unfold inner_product.
    rewrite Mmult00, Mmult01, Mmult10, Mmult11. Csimpl.
    assert (U_norm_helper: ((U 0%nat 0%nat) ^* * U 0%nat 0%nat + (U 1%nat 0%nat) ^* * U 1%nat 0%nat) = ((U) † × U) 0%nat 0%nat). lca.
    assert (V_norm_helper: ((V 0%nat 0%nat) ^* * V 0%nat 0%nat + (V 0%nat 1%nat) ^* * V 0%nat 1%nat) = (V × (V) †) 0%nat 0%nat). lca.
    rewrite U_norm_helper, V_norm_helper. clear U_norm_helper V_norm_helper.
    destruct unitary_U as [_ unit_prop_U]. rewrite unit_prop_U.
    apply transpose_unitary in unitary_V. destruct unitary_V as [_ unit_prop_Vadj]. rewrite adjoint_involutive in unit_prop_Vadj.
    rewrite unit_prop_Vadj. lca.
  }
  {
    unfold w.
    set (a := (U 0%nat 1%nat .* ∣0⟩ .+ U 1%nat 1%nat .* ∣1⟩)).
    set (b := (V 1%nat 0%nat .* ∣0⟩ .+ V 1%nat 1%nat .* ∣1⟩)).
    rewrite kron_inner_prod with (u := a) (w := b) at 1.
    unfold a,b.
    repeat rewrite inner_product_plus_l. repeat rewrite inner_product_plus_r.
    repeat rewrite inner_product_scale_l. repeat rewrite inner_product_scale_r.
    unfold inner_product.
    rewrite Mmult00, Mmult01, Mmult10, Mmult11. Csimpl.
    assert (U_norm_helper: ((U 0%nat 1%nat) ^* * U 0%nat 1%nat + (U 1%nat 1%nat) ^* * U 1%nat 1%nat) = ((U) † × U) 1%nat 1%nat). lca.
    assert (V_norm_helper: ((V 1%nat 0%nat) ^* * V 1%nat 0%nat + (V 1%nat 1%nat) ^* * V 1%nat 1%nat) = (V × (V) †) 1%nat 1%nat). lca.
    rewrite U_norm_helper, V_norm_helper. clear U_norm_helper V_norm_helper.
    destruct unitary_U as [_ unit_prop_U]. rewrite unit_prop_U.
    apply transpose_unitary in unitary_V. destruct unitary_V as [_ unit_prop_Vadj]. rewrite adjoint_involutive in unit_prop_Vadj.
    rewrite unit_prop_Vadj. lca.
  }
  {
    unfold v,w.
    fold beta gamma beta_p gamma_p.
    rewrite kron_inner_prod with (u := beta) (w := gamma) at 1.
    rewrite beta_orth. rewrite gamma_orth. lca.
  }
}
assert (first_coef: RtoC (√ r) = L 0%nat 0%nat).
{
  unfold r, RtoC.
  apply c_proj_eq. unfold fst at 1.
  assert (help: √ (Re (L 0%nat 0%nat) ^ 2) = Re (L 0%nat 0%nat)).
  {
    destruct nonneg_L as [_ nonneg_L_elem].
    rewrite <- pow2_sqrt.
    apply sqrt_pow.
    all: apply Rge_le.
    all: apply nonneg_L_elem.
  }
  rewrite help. clear help. unfold Re. reflexivity.
  unfold snd at 1. destruct nonneg_L as [_ nonneg_L_elem].
  unfold Im in nonneg_L_elem.
  symmetry.
  apply nonneg_L_elem.
}
assert (r_ge_0: r >= 0).
{
  unfold r.
  apply Rle_ge.
  apply pow2_ge_0.
}
assert (r_unit_coefs: (Re (L 0%nat 0%nat) ^ 2 + Re (L 1%nat 1%nat)^ 2 = 1)%R).
{
  destruct nonneg_L as [_ nonneg_L_elem]. unfold Im in nonneg_L_elem.
  assert (L00_r: snd (L 0%nat 0%nat) = 0). apply nonneg_L_elem.
  assert (L11_r: snd (L 1%nat 1%nat) = 0). apply nonneg_L_elem.
  revert unit_coefs.
  unfold RtoC, Re, Cpow, Cmult. simpl.
  repeat rewrite L00_r. repeat rewrite L11_r. 
  repeat rewrite Rmult_0_r. repeat rewrite Rmult_0_l.
  repeat rewrite Rminus_0_r. repeat rewrite Rplus_0_r.
  repeat rewrite Rmult_1_r. repeat rewrite Rmult_0_r.
  repeat rewrite Rplus_0_l. repeat rewrite Ropp_0.
  repeat rewrite Rmult_0_l.
  intros unit_coefs. apply complex_split in unit_coefs.
  destruct unit_coefs as [unit_coefs _].
  revert unit_coefs. unfold Cplus. simpl.
  trivial.
}
assert (r_le_1 : r <= 1).
{
  destruct (Rle_dec r 1).
  apply r0.
  contradict r_unit_coefs.
  apply Rgt_not_eq.
  apply Rnot_le_gt in n.
  fold r.
  rewrite <- Rplus_0_r.
  apply Rplus_gt_ge_compat.
  assumption.
  apply Rle_ge.
  apply pow2_ge_0.
}
assert (second_coef: RtoC (√ (1 - r)) = L 1%nat 1%nat).
{
  unfold r, RtoC.
  apply c_proj_eq.
  unfold fst at 1.
  assert (r_unit_restate: (1 - Re (L 0%nat 0%nat) ^ 2 =Re (L 1%nat 1%nat) ^ 2)%R). 
  {
    rewrite <- r_unit_coefs.
    lra. 
  }
  rewrite r_unit_restate.
  assert (help: √ (Re (L 1%nat 1%nat) ^ 2) = Re (L 1%nat 1%nat)).
  {
    destruct nonneg_L as [_ nonneg_L_elem].
    rewrite <- pow2_sqrt.
    apply sqrt_pow.
    all: apply Rge_le.
    all: apply nonneg_L_elem.
  }
  rewrite help. clear help. unfold Re. reflexivity.
  unfold snd at 1. destruct nonneg_L as [_ nonneg_L_elem].
  unfold Im in nonneg_L_elem.
  symmetry.
  apply nonneg_L_elem.
}
assert (schmidt_decomp: psi =√ r .* (beta ⊗ gamma) .+ √ (1 - r) .* (beta_p ⊗ gamma_p)).
{
  rewrite first_coef. rewrite second_coef.
  apply tensor_decomp.
}
split.
apply schmidt_decomp.
split. apply r_ge_0.
split. apply r_le_1.
{
  intros.
  destruct H.
  all: revert schmidt_decomp.
  all: rewrite H.
  {
    rewrite sqrt_0.
    rewrite Mscale_0_l.
    rewrite Mplus_0_l.
    rewrite Rminus_0_r.
    rewrite sqrt_1.
    rewrite Mscale_1_l.
    intro psi_tens.
    unfold TensorProd.
    intro WF_psi2.
    exists beta_p, gamma_p.
    split. apply beta_p_qubit.
    split. apply gamma_p_qubit.
    assumption.
  }
  {
    rewrite Rminus_diag_eq. 2: reflexivity.
    rewrite sqrt_0.
    rewrite Mscale_0_l.
    rewrite Mplus_0_r.
    rewrite sqrt_1.
    rewrite Mscale_1_l.
    intro psi_tens.
    exists beta, gamma.
    split. apply beta_qubit. 
    split. apply gamma_qubit.
    assumption.
  }
}
Qed.

Lemma a15 : forall (beta beta_p : Vector 2) (w : Vector 4), 
WF_Qubit beta -> WF_Qubit beta_p -> WF_Qubit w -> 
⟨beta, beta_p⟩ = 0 -> exists (psi phi : Vector 2), w = beta ⊗ psi .+ beta_p ⊗ phi /\ WF_Matrix psi /\ WF_Matrix phi.
Proof.
intros. 
set (Q := beta ⊗ ⟨0∣ .+ beta_p ⊗ ⟨1∣).
assert (WF_Q : WF_Unitary Q).
{
  apply is_unitary_form with (a := beta) (b := beta_p).
  apply H. apply H0.
  split.
  unfold Q. reflexivity.
  apply H2.
}
assert (HQ_impl := qubit_decomposition2_implicit ((Q ⊗ I 2)† × w)).
assert (WF_QI2 : WF_Matrix (Q ⊗ I 2)).
{
  solve_WF_matrix. apply H. apply H0.
}
assert (HQ: WF_Matrix ((Q ⊗ I 2) † × w)). 
{
  solve_WF_matrix. apply H. apply H0. apply H1.
}
apply HQ_impl in HQ.
destruct HQ as [c00 [c01 [c10 [c11 HQ]]]].
repeat rewrite <- Mscale_kron_dist_r in HQ.
rewrite <- kron_plus_distr_l in HQ.
rewrite Mplus_assoc in HQ.
rewrite <- kron_plus_distr_l in HQ.
rewrite <- ket0_equiv in HQ.
rewrite <- ket1_equiv in HQ.
set (psi := c00 .* ∣0⟩ .+ c01 .* ∣1⟩).
set (phi := c10 .* ∣0⟩ .+ c11 .* ∣1⟩).
assert (WF_psi: WF_Matrix psi). solve_WF_matrix.
assert (WF_phi: WF_Matrix phi). solve_WF_matrix.
fold psi in HQ. fold phi in HQ.
exists psi, phi.
split.
assert (Step1: beta ⊗ psi .+ beta_p ⊗ phi = (Q ⊗ I 2) × (∣0⟩ ⊗ psi .+ ∣1⟩ ⊗ phi)).
{
  lma'.
  solve_WF_matrix. apply H. apply H0.
}
rewrite Step1.
rewrite <- HQ.
rewrite <- Mmult_assoc.
assert (WF_QI : WF_Unitary (Q ⊗ I 2)†).
{
  apply transpose_unitary.
  apply kron_unitary.
  apply WF_Q.
  apply id_unitary.
}
destruct WF_QI as [_ WF_QI].
rewrite adjoint_involutive in WF_QI.
rewrite WF_QI at 1.
rewrite Mmult_1_l. 2: apply H1.
reflexivity.
split. all: assumption. 
Qed.

(* Using old version of proof since beta is chosen constructively *)
Lemma a16_part1 {n}: forall (w0 w1 : Vector n) (a0 a1 : Vector 2), 
WF_Matrix w0 -> WF_Matrix w1 -> WF_Qubit a0 -> WF_Qubit a1 -> 
linearly_independent_2vec a0 a1 -> w0 ⊗ a0 .+ w1 ⊗ a1 = (Zero (m:= (n*2)%nat) (n := 1%nat)) -> w1 = Zero.
Proof.
intros w0 w1 a0 a1 WF_w0 WF_w1 a0_qubit a1_qubit a_lin_indep Zero_sum.
set (b := a1 .+ ((- ⟨a0, a1⟩) .* a0)).
assert (H0 : b† × a0 = Zero).
{
  destruct a0_qubit as [_ [WF_a0 a0_unit]].
  destruct a1_qubit as [_ [WF_a1 a1_unit]].
  unfold b.
  assert (Help1 : ((a1 .+ ((- ⟨ a0, a1 ⟩) .* a0)) † × a0) = 
    a1† × a0 .+ (- ⟨ a1, a0 ⟩ * ⟨ a0, a0 ⟩%C)%C .* (I 1)).
  {
    lma'.
    all: solve_WF_matrix.
  }
  rewrite Help1.    
  rewrite a0_unit. 
  lma'.
}
assert (Hb1 : ⟨b, a1⟩ <> 0).
{
  assert (Help1 : ⟨ b, a1 ⟩ = ⟨ a1, a1 ⟩ - (⟨ a1, a0 ⟩ * ⟨ a0, a1 ⟩)%C).
  {
    unfold b. lca.
  }
  rewrite Help1.
  assert (Help2: ⟨ a1, a1 ⟩ = C1). apply a1_qubit.
  rewrite Help2.
  assert (Help3 : (1 - ((⟨ a1, a0 ⟩ * ⟨ a0, a1 ⟩)%C)) = 1 -  ((Cmod ⟨ a0, a1 ⟩ )^ 2)%C).
  {
    rewrite Cmod_sqr.
    rewrite inner_product_conj_sym.
    reflexivity.
  }
  rewrite Help3.
  assert (Help5 := cauchy_schwarz_corollary a0 a1 a0_qubit a1_qubit).
  apply Help5 in a_lin_indep.
  unfold not.
  intros.
  apply eq_sym in H.
  apply addition_equivalence in H.
  revert H.
  rewrite Cplus_0_r.
  unfold Cpow.
  rewrite Cmult_1_r.
  unfold RtoC.
  unfold Cmult.
  simpl.
  rewrite Rmult_0_l. rewrite Rminus_0_r.
  intros.
  apply Ceq_implies_el_eq in H.
  destruct H as [H _].
  revert H. 
  simpl.
  intros.
  rewrite <- Rmult_1_r in H. 
  apply Rsqr_eq in H.
  destruct H.
  apply (Rlt_irrefl 1).
  rewrite <- H at 1.
  assumption.
  assert (not ((- (1))%R >= 0%R)). lra.
  assert (Cmod ⟨ a0, a1 ⟩ >= 0). apply Rle_ge. apply sqrt_pos.
  apply H1.
  rewrite <- H.
  apply H2.
}
assert (H1 : not ((b) † × a1 = Zero)).
{
  unfold not. intros.
  apply Hb1. unfold inner_product. rewrite H. lca.
}
assert (S1 : (Zero (m:= n) (n := 1%nat)) = w1 ⊗ ((b) † × a1)). 
{
  (* I n kron bdag is nxn kron 1 by 2 -> n x 2n
  zero_sum is 2n by 1
  zero should be n by 1 *)
  assert (S1: (Zero (m:= n) (n := 1%nat)) = (I n ⊗ (b †)) × (w0 ⊗ a0 .+ w1 ⊗ a1)).
  {
    rewrite Zero_sum.
    rewrite Mmult_0_r.
    reflexivity.
  }
  rewrite S1.
  rewrite Mmult_plus_distr_l.
  rewrite kron_mixed_product.
  rewrite H0.
  rewrite kron_0_r.
  rewrite Mplus_0_l.
  rewrite kron_mixed_product.
  rewrite Mmult_1_l. 2: assumption.
  reflexivity.
}
symmetry.
apply (@kron_cancel_r n 1%nat 1%nat 1%nat) with (A:= (Zero (m:= n) (n := 1%nat))) (B:= w1) (C:=((b) † × a1)).
1,2,3: solve_WF_matrix.
1,3: apply a1_qubit.
apply a0_qubit.
apply H1.
rewrite kron_0_l.
apply S1.
Qed.

(* Using old version of proof since beta is chosen constructively *)
Lemma a16_part2 {n}: forall (w0 w1 : Vector n) (a0 a1 : Vector 2), 
WF_Matrix w0 -> WF_Matrix w1 -> WF_Qubit a0 -> WF_Qubit a1 -> 
linearly_independent_2vec a0 a1 -> w0 ⊗ a0 .+ w1 ⊗ a1 = (Zero (m:= (n*2)%nat) (n := 1%nat)) -> w0 = Zero.
Proof.
intros.
rewrite Mplus_comm in H4.
rewrite lin_indep_comm_2vec in H3.
apply a16_part1 with (w0 := w1) (a0 := a1) (w1 := w0) (a1 := a0).
all: assumption.
Qed.

Lemma a16 {n}: forall (w0 w1 : Vector n) (a0 a1 : Vector 2), 
WF_Matrix w0 -> WF_Matrix w1 -> WF_Qubit a0 -> WF_Qubit a1 -> 
linearly_independent_2vec a0 a1 -> w0 ⊗ a0 .+ w1 ⊗ a1 = (Zero (m:= (n*2)%nat) (n := 1%nat)) -> w0 = Zero /\ w1 = Zero.
Proof. 
split.
apply a16_part2 with (w1:= w1) (a0:= a0) (a1:= a1).
7: apply a16_part1 with (w0:= w0) (a0:= a0) (a1:= a1).
all: assumption.
Qed.
