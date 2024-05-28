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
