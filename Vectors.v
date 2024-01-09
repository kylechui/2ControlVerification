Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.
Require Import QuantumLib.VectorStates.
Require Import QuantumLib.Eigenvectors.
From Proof Require Import QubitHelpers.
From Proof Require Import MatrixHelpers.
From Proof Require Import AlgebraHelpers.

(* Definition of lemma from old file Multiqubit*)
Lemma qubit_decomposition2 : forall (phi : Vector 4), 
WF_Matrix phi -> exists (a b c d: C),
phi = a .* ∣0,0⟩ .+ b .* ∣0,1⟩ .+ c .* ∣1,0⟩ .+ d .* ∣1,1⟩.
Proof.
  intros.
  exists (phi 0 0)%nat, (phi 1 0)%nat, (phi 2 0)%nat, (phi 3 0)%nat.
  lma'.
  solve_WF_matrix.
Qed.

Definition WF_Nonnegative {m n} (A : Matrix m n) :=
WF_Matrix A /\ forall (i j: nat), Re (A i j) >= 0 /\ Im (A i j) = 0.

Lemma SVD_2: forall (A : Square 2), 
exists (U L V: Square 2), 
WF_Unitary U /\ WF_Unitary V /\ WF_Diagonal L /\ WF_Nonnegative L /\ A = U × L × V.
Proof. 
Admitted.

Lemma amplitudes_of_unit {n}: forall (a b : C) (u v w: Vector n), 
u = a .* v .+ b .* w -> ⟨ u , u ⟩ = C1 -> ⟨ v , v ⟩ = C1 -> ⟨ w , w ⟩ = C1 -> 
⟨ v , w ⟩ = C0 -> a ^* * a + b ^* * b = C1.
Proof.
intros a b u v w u_def u_unit v_unit w_unit vw_orthogonal.
revert u_unit.
rewrite u_def.
repeat rewrite inner_product_plus_l. repeat rewrite inner_product_plus_r.
repeat rewrite inner_product_scale_l. repeat rewrite inner_product_scale_r.
rewrite inner_product_conj_sym with (u := w).
repeat rewrite vw_orthogonal. rewrite v_unit. rewrite w_unit.
Csimpl.
trivial.
Qed.

Lemma kron_inner_prod {m n} : forall (u v: Vector m) (w z: Vector n),
  ⟨ u ⊗ w, v ⊗ z ⟩ = ⟨ u, v ⟩ * ⟨ w, z ⟩.
Proof.
  intros.
  destruct n.
  - unfold inner_product, Mmult.
    rewrite Nat.mul_0_r.
    lca.
  - unfold inner_product, Mmult.
    rewrite (@big_sum_product Complex.C _ _ _ C_is_ring). 2: auto.
    apply big_sum_eq.
    apply functional_extensionality; intro.
    lca.
Qed.

Lemma a14 : forall (psi : Vector 4), 
WF_Matrix psi -> ⟨ psi , psi ⟩ = 1 -> 
exists (beta beta_p gamma gamma_p: Vector 2) (r : R),
⟨ beta , beta_p ⟩ = 0 /\ ⟨ gamma , gamma_p ⟩ = 0 /\
psi = √ (r) .* (beta ⊗ gamma) .+ √ (1-r) .* (beta_p ⊗ gamma_p).
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
assert (second_coef: RtoC (√ (1 - r)) = L 1%nat 1%nat).
{
  unfold r, RtoC.
  apply c_proj_eq.
  unfold fst at 1.
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
rewrite first_coef. rewrite second_coef.
apply tensor_decomp.
Qed.

Property is_unitary_form : forall (M : Square 2) (a b : Vector 2), 
  WF_Qubit a -> WF_Qubit b ->
  M = a ⊗ ⟨0∣ .+ b ⊗ ⟨1∣ /\ ⟨a, b⟩ = 0 -> WF_Unitary M.
Proof.
  intros.
  destruct H1 as [H1 H2].
  rewrite H1.
  destruct H as [_ [H WF_a]].
  destruct H0 as [_ [H0 WF_b]].
  rewrite qubit_adj_mult in WF_a. 2: apply H.
  rewrite qubit_adj_mult in WF_b. 2: apply H0.
  unfold WF_Unitary.
  split. solve_WF_matrix.
  rewrite Mplus_adjoint.
  rewrite (kron_adjoint a ⟨0∣).
  rewrite (kron_adjoint b ⟨1∣).
  repeat rewrite adjoint_involutive.
  rewrite Mmult_plus_distr_l.
  repeat rewrite Mmult_plus_distr_r.
  rewrite (kron_mixed_product a† ∣0⟩ a ⟨0∣).
  rewrite WF_a.
  rewrite kron_1_l with (A := ∣0⟩⟨0∣). 2: apply WF_braqubit0.
  rewrite (kron_mixed_product b† ∣1⟩ a ⟨0∣).
  unfold inner_product in H2.
  assert (Main1 : a† × b = b† × a).
  {
    lma'.
    rewrite H2.
    apply (f_equal (fun f => f^*)) in H2.
    assert (Help : ((a† × b) 0%nat 0%nat)^* = ((b† × a) 0%nat 0%nat)). lca.
    rewrite Help in H2.
    rewrite Cconj_0 in H2.
    symmetry.
    apply H2.
  }
  rewrite <- Main1.
  assert (Main2 : a† × b = Zero).
  {
    lma'.
    apply H2.
  }
  rewrite Main2.
  rewrite kron_0_l.
  rewrite Mplus_0_r.
  rewrite (kron_mixed_product a† ∣0⟩ b ⟨1∣).
  rewrite Main2.
  rewrite kron_0_l.
  rewrite Mplus_0_l.
  rewrite (kron_mixed_product b† ∣1⟩ b ⟨1∣).
  rewrite WF_b.
  lma'.
Qed.

Lemma a15 : forall (beta beta_p : Vector 2) (w : Vector 4), 
WF_Qubit beta -> WF_Qubit beta_p -> WF_Qubit w -> 
⟨beta, beta_p⟩ = 0 -> exists (psi phi : Vector 2), w = beta ⊗ psi .+ beta_p ⊗ phi.
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
assert (HQ_impl := qubit_decomposition2 ((Q ⊗ I 2)† × w)).
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
Qed.

Definition linearly_independent_2vec {n} (v1 v2 : Vector n) := 
  forall (c1 c2 : C), c1 .* v1 .+ c2 .* v2 = Zero -> c1 = 0 /\ c2=0.

Lemma addition_equivalence: forall (a b c: C), 
a + b = c <-> b = c - a.
Proof.
split.
intros.
rewrite <- H.
lca.
intros.
rewrite H.
lca.
Qed.

Lemma opp_equivalence: forall (a b: C), 
a = b <-> -a = -b.
Proof.
split.
intros.
rewrite H. reflexivity.
intros.
rewrite <- Cplus_0_l.
rewrite <- (Cplus_opp_l a).
rewrite H.
lca.
Qed.

(* Lemma inner_prod_adj *)

(* Using old version of proof since beta is chosen constructively *)
(* Lemma a16_part1: forall (w0 w1 a0 a1 : Vector 2), 
WF_Qubit a0 -> WF_Qubit a1 -> linearly_independent_2vec a0 a1 -> 
w0 ⊗ a0 .+ w1 ⊗ a1 = Zero -> w0 = Zero.
Proof.
intros.
set (beta := a1 .+ -⟨a0, a1⟩ .* a0).
assert (Step1: ⟨beta, a0⟩ = 0).
{
  unfold beta, inner_product.
  rewrite Mplus_adjoint.
  rewrite Mmult_plus_distr_r.
  rewrite Mscale_adj.
  destruct H as [_ [WF_a0 H]].
  rewrite qubit_adj_mult in H. 2: apply WF_a0.
  rewrite Mscale_mult_dist_l.
  rewrite H.
  lca.
}
assert (Step2: ⟨beta, a1⟩ <> 0).
{
  unfold beta, inner_product.
  rewrite Mplus_adjoint.
  rewrite Mmult_plus_distr_r.
  destruct H0 as [_ [WF_a1 H0]].
  rewrite qubit_adj_mult in H0. 2: apply WF_a1.
  rewrite H0.
  rewrite Mscale_adj.
  rewrite Mscale_mult_dist_l.
  unfold Mplus. unfold I. simpl.
  unfold scale.
  fold (inner_product a0 a1).
  rewrite Cconj_opp. rewrite <- Copp_mult_distr_l.
  unfold not.
  rewrite addition_equivalence.
  rewrite Cminus_unfold.
  rewrite Cplus_0_l.
  rewrite <- opp_equivalence.
  assert (⟨ a0, a1 ⟩ = ((a0 0%nat 0%nat)^* * (a1 0%nat 0%nat) + (a0 1%nat 0%nat)^* * (a1 1%nat 0%nat))). lca.
  rewrite H3.
  rewrite Cconj_plus_distr. rewrite Cconj_mult_distr. rewrite Cconj_involutive.
  rewrite Cmult_plus_distr_l. rewrite Cmult_plus_distr_r. rewrite Cmult_plus_distr_r.
  intros. 
} *)
