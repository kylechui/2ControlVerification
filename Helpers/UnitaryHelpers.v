Require Import QuantumLib.Matrix.
Require Import QuantumLib.Eigenvectors.
Require Import QuantumLib.Permutations.
Require Import WFHelpers.
Require Import MatrixHelpers.

Lemma other_unitary_decomp : forall {n : nat} (U : Square n),
  WF_Unitary U -> U × U† = I n.
Proof.
  intros n U Unitary_U.
  assert (step : WF_Unitary U†).
  {
    apply adjoint_unitary, Unitary_U.
  }
  destruct step as [_ step].
  rewrite <- step, adjoint_involutive.
  reflexivity.
Qed.

Lemma direct_sum_unitary : forall {n : nat} (P Q : Square n),
  WF_Unitary P -> WF_Unitary Q -> WF_Unitary (P .⊕ Q).
Proof.
  intros n P Q [WF_P Unitary_P] [WF_Q Unitary_Q].
  unfold WF_Unitary.
  split. apply WF_direct_sum; auto.
  rewrite direct_sum_decomp; auto.
  replace (n + n)%nat with (2 * n)%nat by lia.
  rewrite Mplus_adjoint.
  rewrite Mmult_plus_distr_r.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite kron_adjoint.
  repeat rewrite kron_mixed_product.
  rewrite adjoint00, adjoint11.
  rewrite cancel00, cancel01, cancel10, cancel11; solve_WF_matrix.
  repeat rewrite kron_0_l.
  rewrite Mplus_0_l, Mplus_0_r.
  rewrite Unitary_P, Unitary_Q.
  rewrite <- kron_plus_distr_r.
  rewrite Mplus01.
  rewrite id_kron.
  reflexivity.
Qed.

#[export] Hint Resolve direct_sum_unitary : unit_db.

Lemma diag2_unitary : forall (c1 c2 : C), Cmod c1 = 1 -> Cmod c2 = 1 -> WF_Unitary (diag2 c1 c2).
Proof.
  intros c1 c2 unit_c1 unit_c2.
  split; try apply WF_diag2.
  lma'.
  unfold Mmult, adjoint, diag2, I; simpl.
  Csimpl; rewrite <- Cmod_sqr, unit_c1; lca.
  unfold Mmult, adjoint, diag2, I; simpl.
  Csimpl; rewrite <- Cmod_sqr, unit_c2; lca.
Qed.

Lemma diag4_unitary : forall (c1 c2 c3 c4 : C),
  Cmod c1 = 1 -> Cmod c2 = 1 -> Cmod c3 = 1 -> Cmod c4 = 1 ->
  WF_Unitary (diag4 c1 c2 c3 c4).
Proof.
  intros c1 c2 c3 c4 unit_c1 unit_c2 unit_c3 unit_c4.
  split. apply WF_diag4.
  lma'.
  unfold Mmult, adjoint, diag4, I; simpl.
  Csimpl; rewrite <- Cmod_sqr, unit_c1; lca.
  unfold Mmult, adjoint, diag4, I; simpl.
  Csimpl; rewrite <- Cmod_sqr, unit_c2; lca.
  unfold Mmult, adjoint, diag4, I; simpl.
  Csimpl; rewrite <- Cmod_sqr, unit_c3; lca.
  unfold Mmult, adjoint, diag4, I; simpl.
  Csimpl; rewrite <- Cmod_sqr, unit_c4; lca.
Qed.

#[export] Hint Resolve diag2_unitary diag4_unitary : unit_db.
