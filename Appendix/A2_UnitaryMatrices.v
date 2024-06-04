Require Import QuantumLib.Eigenvectors.
Require Import QuantumLib.Permutations.
Require Import WFHelpers.
Require Import MatrixHelpers.
Require Import DiagonalHelpers.
Require Import UnitaryHelpers.
Require Import PartialTraceDefinitions.
Require Import Permutations.

Theorem a3 : forall {n} (U : Square n),
  WF_Unitary U -> exists (V D : Square n),
    (WF_Unitary V /\ WF_Diagonal D /\ U = V × D × V†).
Proof.
  intros n U Unitary_U.
  pose proof (Spectral_Theorem U).
  destruct H.
  {
    apply Unitary_U.
  }
  {
    pose proof (adjoint_unitary n U Unitary_U).
    destruct Unitary_U, H.
    rewrite H1, <- H2.
    rewrite adjoint_involutive.
    reflexivity.
  }
  {
    destruct H.
    exists x, ((x) † × U × x).
    split; try exact H.
    split; try exact H0.
    pose proof (adjoint_unitary n x H).
    destruct H1.
    rewrite adjoint_involutive in H2.
    repeat rewrite <- Mmult_assoc.
    rewrite H2.
    repeat rewrite Mmult_assoc.
    rewrite H2.
    Msimpl; auto; try apply Unitary_U.
  }
Qed.

Lemma a4: forall {n} (v: Vector n) (c: C) (U V : Square n),
    WF_Matrix v -> WF_Unitary U -> WF_Unitary V ->
    Eigenpair V (v, c) <-> Eigenpair (U × V × U†) (U × v, c).
Proof.
  intros.
  destruct H0 as [H0 H2].
  unfold Eigenpair in *; simpl in *.
  do 2 (rewrite Mmult_assoc).
  rewrite <- Mmult_assoc with (A := U†).
  rewrite H2.
  rewrite Mmult_1_l. 2: apply H.
  split.
  - intro H3.
    rewrite H3.
    rewrite Mscale_mult_dist_r.
    reflexivity.
  - intro H3.
    rewrite <- Mmult_1_l with (A := V). 2: apply H1.
    rewrite <- H2.
    rewrite Mmult_assoc with (B := U).
    rewrite Mmult_assoc with (B := (U × V)).
    rewrite Mmult_assoc with (A := U).
    rewrite H3.
    rewrite Mscale_mult_dist_r.
    rewrite <- Mmult_assoc.
    rewrite H2.
    rewrite Mmult_1_l. 2: apply H.
    reflexivity.
Qed.

(* Since we discuss eigenvalues by looking at diagonal matrices, Lemma A.5 isn't
   needed, as we just tensor two diagonal matrices representing eigenvalues. *)

Lemma a6 : forall (P Q VP DP VQ DQ : Square 2) (V D : Square 4),
  WF_Unitary VP -> WF_Diagonal DP -> WF_Unitary VQ -> WF_Diagonal DQ ->
  WF_Unitary V -> WF_Diagonal D ->
  P = VP × DP × VP† -> Q = VQ × DQ × VQ† ->
  P .⊕ Q = V × D × V† ->
  exists (σ : nat -> nat), permutation 4%nat σ /\
  forall (i : nat), (DP .⊕ DQ) i i = D (σ i) (σ i).
Proof.
  intros P Q VP DP VQ DQ V D.
  intros Unitary_VP Diagonal_DP Unitary_VQ Diagonal_DQ Unitary_V Diagonal_D HP HQ.
  assert (step : P .⊕ Q = (VP .⊕ VQ) × (DP .⊕ DQ) × (VP .⊕ VQ)†).
  {
    repeat rewrite (direct_sum_decomp 2 2 2 2)%nat.
    rewrite HP, HQ; clear HP HQ.
    repeat rewrite Mmult_plus_distr_r.
    repeat rewrite Mmult_plus_distr_l.
    repeat rewrite kron_mixed_product.
    repeat rewrite cancel00; auto with wf_db.
    repeat rewrite cancel11; auto with wf_db.
    repeat rewrite cancel01; Msimpl.
    repeat rewrite cancel10; Msimpl.
    repeat rewrite Mmult_plus_distr_l.
    repeat rewrite kron_mixed_product.
    repeat rewrite cancel00; auto with wf_db.
    repeat rewrite cancel11; auto with wf_db.
    repeat rewrite cancel01; Msimpl.
    repeat rewrite cancel10; Msimpl.
    reflexivity.
    apply Diagonal_DP.
    apply Diagonal_DQ.
    apply Unitary_VP.
    apply Unitary_VQ.
    rewrite HP; repeat apply WF_mult.
    apply Unitary_VP.
    apply Diagonal_DP.
    apply WF_adjoint, Unitary_VP.
    rewrite HQ; repeat apply WF_mult.
    apply Unitary_VQ.
    apply Diagonal_DQ.
    apply WF_adjoint, Unitary_VQ.
  }
  rewrite step; clear step.
  assert (Unitary_VP_plus_VQ : WF_Unitary (VP .⊕ VQ)).
  {
    apply direct_sum_unitary; auto.
  }
  pose proof Unitary_VP_plus_VQ.
  destruct H as [WF_VP_plus_VQ VPVQ_Equation].
  intro H.
  apply (f_equal (fun f => (VP .⊕ VQ)† × f × (VP .⊕ VQ))) in H.
  revert H.
  repeat rewrite <- Mmult_assoc.
  rewrite VPVQ_Equation; Msimpl_light.
  repeat rewrite Mmult_assoc.
  rewrite VPVQ_Equation; Msimpl_light.
  intro H.
  assert (step : exists (U : Square 4), WF_Unitary U /\ U × DP .⊕ DQ × U† = D).
  {
    exists (V† × (VP .⊕ VQ)).
    split.
    {
      apply Mmult_unitary.
      apply adjoint_unitary.
      assumption.
      split; assumption.
    }
    {
      rewrite H, Mmult_adjoint.
      repeat rewrite <- Mmult_assoc.
      repeat rewrite Mmult_assoc.
      rewrite <- Mmult_assoc with (A := VP .⊕ VQ).
      replace 4%nat with (2 + 2)%nat by reflexivity.
      rewrite other_unitary_decomp; auto.
      rewrite <- Mmult_assoc with (A := VP .⊕ VQ).
      rewrite other_unitary_decomp; auto.
      rewrite adjoint_involutive.
      Msimpl_light; auto.
      destruct Unitary_V as [_ Unitary_V].
      rewrite Unitary_V.
      repeat rewrite <- Mmult_assoc.
      rewrite Unitary_V.
      Msimpl_light.
      reflexivity.
      apply Diagonal_D.
      apply Diagonal_D.
      apply Diagonal_D.
      apply Unitary_V.
      apply WF_mult.
      apply Unitary_V.
      apply WF_mult.
      apply Diagonal_D.
      apply WF_mult.
      apply WF_adjoint, Unitary_V.
      apply WF_mult.
      apply WF_I.
      apply Unitary_V.
    }
  }
  destruct step as [U [Unitary_U step]].
  apply (perm_eigenvalues U); auto.
  apply (direct_sum_diagonal DP); auto.
  apply (direct_sum_diagonal DP); auto.
  apply (direct_sum_diagonal DP); auto.
Qed.

Lemma a7_2q_a : forall (P : Square 2) (Q: Square 2),
    WF_Matrix Q ->
    partial_trace_2q_a (P ⊗ Q) = (trace P) .* Q.
Proof.
intros.
lma'.
Qed.

Lemma a7_2q_b : forall (P : Square 2) (Q: Square 2),
    WF_Matrix P ->
    partial_trace_2q_b (P ⊗ Q) = (trace Q) .* P.
Proof.
intros.
lma'.
Qed.

Lemma a7_3q_a : forall (A: Square 2) (B: Square 4),
    WF_Matrix B ->
    partial_trace_3q_a (A ⊗ B) = (trace A) .* (B).
Proof.
intros.
lma'.
Qed.

Lemma a7_3q_c : forall (A: Square 4) (B: Square 2),
    WF_Matrix A ->
    partial_trace_3q_c (A ⊗ B) = (trace B) .* (A).
Proof.
intros.
lma'.
Qed.

Lemma a8 : forall (Q : Square 2),
  WF_Unitary Q -> (Q × ∣0⟩) × (Q × ∣0⟩)† .+ (Q × ∣1⟩) × (Q × ∣1⟩)† = I 2.
Proof.
  intros.
  repeat rewrite Mmult_adjoint.
  repeat rewrite Mmult_assoc.
  rewrite <- Mmult_plus_distr_l.
  repeat rewrite <- Mmult_assoc.
  rewrite <- Mmult_plus_distr_r.
  rewrite Mplus01.
  rewrite Mmult_1_l.
  rewrite (other_unitary_decomp Q H).
  reflexivity.
  solve_WF_matrix.
Qed.

Lemma a9: forall (V : Square 4) (P00 P01 P10 P11 : Square 2),
  WF_Unitary V -> WF_Matrix P00 -> WF_Matrix P01 -> WF_Matrix P10 -> WF_Matrix P11 ->
  V = ∣0⟩⟨0∣ ⊗ P00 .+ ∣0⟩⟨1∣ ⊗ P01 .+ ∣1⟩⟨0∣ ⊗ P10 .+ ∣1⟩⟨1∣ ⊗ P11 ->
  P01 = Zero <-> P10 = Zero.
Proof.
  intros V P00 P01 P10 P11 [WF_V V_inv] WF_P00 WF_P01 WF_P10 WF_P11 V_decomp.
  rewrite V_decomp in V_inv; clear V_decomp.
  revert V_inv.
  repeat rewrite Mplus_adjoint.
  repeat rewrite kron_adjoint.
  rewrite adjoint00, adjoint01, adjoint10, adjoint11.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite Mmult_plus_distr_r.
  repeat rewrite kron_mixed_product.
  repeat rewrite cancel00.
  repeat rewrite cancel01.
  repeat rewrite cancel10.
  repeat rewrite cancel11.
  Msimpl_light.
  intro.
  assert (∣0⟩⟨0∣ ⊗ (P00† × P00) .+ ∣1⟩⟨0∣ ⊗ (P01† × P00) .+
         (∣0⟩⟨1∣ ⊗ (P00† × P01) .+ ∣1⟩⟨1∣ ⊗ (P01† × P01)) .+
         (∣0⟩⟨0∣ ⊗ (P10† × P10) .+ ∣1⟩⟨0∣ ⊗ (P11† × P10)) .+
         (∣0⟩⟨1∣ ⊗ (P10† × P11) .+ ∣1⟩⟨1∣ ⊗ (P11† × P11)) =
         ∣0⟩⟨0∣ ⊗ (P00† × P00 .+ P10† × P10) .+
         ∣0⟩⟨1∣ ⊗ (P00† × P01 .+ P10† × P11) .+
         ∣1⟩⟨0∣ ⊗ (P01† × P00 .+ P11† × P10) .+
         ∣1⟩⟨1∣ ⊗ (P01† × P01 .+ P11† × P11)) by lma.
  rewrite H in V_inv at 1; clear H.
  assert (P00† × P00 .+ P10† × P10 = I 2 /\
          P00† × P01 .+ P10† × P11 = Zero /\
          P01† × P00 .+ P11† × P10 = Zero /\
          P01† × P01 .+ P11† × P11 = I 2).
  {
    apply block_equalities; solve_WF_matrix.
    rewrite V_inv.
    Msimpl_light.
    rewrite <- kron_plus_distr_r.
    rewrite Mplus01, id_kron.
    reflexivity.
  }
  clear V_inv.
  destruct H as [H00 [H01 [H10 H11]]].
  split.
  {
    intro.
    rewrite H in H01, H11.
    rewrite Mmult_0_r, Mplus_0_l in H01, H11.
    apply (f_equal (fun f => f × P11†)) in H01.
    rewrite Mmult_assoc, (other_unitary_decomp P11) in H01.
    rewrite Mmult_1_r, Mmult_0_l in H01.
    apply (f_equal (fun f => f†)) in H01.
    rewrite adjoint_involutive, zero_adjoint_eq in H01.
    all: solve_WF_matrix.
    split; assumption.
  }
  {
    intro.
    rewrite H in H00, H10.
    rewrite Mmult_0_r, Mplus_0_r in H00, H10.
    apply (f_equal (fun f => f × P00†)) in H10.
    rewrite Mmult_assoc, (other_unitary_decomp P00) in H10.
    rewrite Mmult_1_r, Mmult_0_l in H10.
    apply (f_equal (fun f => f†)) in H10.
    rewrite adjoint_involutive, zero_adjoint_eq in H10.
    all: solve_WF_matrix.
    split; assumption.
  }
  all: solve_WF_matrix.
Qed.
