Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.
Require Import QuantumLib.VectorStates.
From Proof Require Import QubitHelpers.

Lemma a14 : forall (psi : Vector 4), 
WF_Matrix psi -> ⟨ psi , psi ⟩ = 1 -> 
exists (beta beta_p gamma gamma_p: Vector 2) (r : R)
(* (WF_b : WF_Matrix beta) (WF_bp : WF_Matrix beta_p) (WF_g: WF_Matrix gamma) (WF_gp : WF_Matrix gamma_p) *),
⟨ beta , beta_p ⟩ = 0 /\ ⟨ gamma , gamma_p ⟩ = 0 /\
psi = √ (r) .* (beta ⊗ gamma) .+ √ (1-r) .* (beta_p ⊗ gamma_p).
intros.
Admitted.

(* Definition of lemma from old file Multiqubit*)
Lemma qubit_decomposition2 : forall (phi : Vector 4), 
WF_Matrix phi -> exists (a b c d: C),
phi = a .* ∣0,0⟩ .+ b .* ∣0,1⟩ .+ c .* ∣1,0⟩ .+ d .* ∣1,1⟩.
Proof.
  intros.
  exists (phi 0 0)%nat, (phi 1 0)%nat, (phi 2 0)%nat, (phi 3 0)%nat.
  lma'.
  apply WF_plus. apply WF_plus. apply WF_plus.
  apply WF_scale. apply WF_kron. reflexivity. reflexivity. apply WF_qubit0. apply WF_qubit0.
  apply WF_scale. apply WF_kron. reflexivity. reflexivity. apply WF_qubit0. apply WF_qubit1.
  apply WF_scale. apply WF_kron. reflexivity. reflexivity. apply WF_qubit1. apply WF_qubit0.
  apply WF_scale. apply WF_kron. reflexivity. reflexivity. apply WF_qubit1. apply WF_qubit1.
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
  split. 
  {
    apply WF_plus.
    apply WF_kron. reflexivity. reflexivity. apply H. apply WF_adjoint. apply WF_qubit0.
    apply WF_kron. reflexivity. reflexivity. apply H0. apply WF_adjoint. apply WF_qubit1.
  }
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
  apply WF_kron. reflexivity. reflexivity. apply WF_Q. apply WF_I.
}
assert (HQ: WF_Matrix ((Q ⊗ I 2) † × w)). 
{
  apply WF_mult. apply WF_adjoint. apply WF_QI2.
  apply H1.
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
assert (WF_psi: WF_Matrix psi).
{
  apply WF_plus. apply WF_scale. apply WF_qubit0. apply WF_scale. apply WF_qubit1.
}
assert (WF_phi: WF_Matrix phi).
{
  apply WF_plus. apply WF_scale. apply WF_qubit0. apply WF_scale. apply WF_qubit1.
}
fold psi in HQ. fold phi in HQ.
exists psi, phi.
assert (Step1: beta ⊗ psi .+ beta_p ⊗ phi = (Q ⊗ I 2) × (∣0⟩ ⊗ psi .+ ∣1⟩ ⊗ phi)).
{
  lma'.
  apply WF_plus. 
  apply WF_kron. reflexivity. reflexivity. apply H.
  apply WF_psi.
  apply WF_kron. reflexivity. reflexivity. apply H0.
  apply WF_phi.

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

