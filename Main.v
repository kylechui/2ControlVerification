Require Import Proof.UnitaryMatrices.
Require Import Proof.Permutations.
Require Import Proof.SquareMatrices.
Require Import Proof.AlgebraHelpers.
Require Import Proof.MatrixHelpers.
Require Import Proof.GateHelpers.
Require Import Proof.EigenvalueHelpers.
Require Import QuantumLib.Complex.
Require Import QuantumLib.Quantum.
Require Import QuantumLib.Eigenvectors.
Require Import QuantumLib.Matrix.
Require Import QuantumLib.Permutations.

Lemma m3_1 : forall (u0 u1 : C),
  Cmod u0 = 1 -> Cmod u1 = 1 ->
  forall (U : Square 8), WF_Unitary U ->
    (U × ((diag2 u0 u1) ⊗ (I 2) ⊗ (I 2)) = ((diag2 u0 u1) ⊗ (I 2) ⊗ (I 2)) × U <->
    u0 = u1 \/ (exists (V00 V11 : Square 4),
      WF_Unitary V00 /\ WF_Unitary V11 /\
      U = ∣0⟩⟨0∣ ⊗ V00 .+ ∣1⟩⟨1∣ ⊗ V11)).
Proof.
  intros u0 u1 unit_u0 unit_u1 U Unitary_U.
  split.
  {
    intro H.
    destruct (Ceq_dec u0 u1) as [u0_eq_u1 | u0_neq_u1].
    {
      left.
      exact u0_eq_u1.
    }
    {
      right.
      assert (block_matrices_U : exists V00 V01 V10 V11 : Square 4,
        WF_Matrix V00 /\
        WF_Matrix V01 /\
        WF_Matrix V10 /\
        WF_Matrix V11 /\
        U = ∣0⟩⟨0∣ ⊗ V00 .+ ∣0⟩⟨1∣ ⊗ V01 .+ ∣1⟩⟨0∣ ⊗ V10 .+ ∣1⟩⟨1∣ ⊗ V11
      ).
      {
        apply block_decomp.
        destruct Unitary_U; assumption.
      }
      destruct block_matrices_U as [V00 [V01 [V10 [V11 block_matrices_U]]]].
      destruct block_matrices_U as [WF_V00 [WF_V01 [WF_V10 [WF_V11 U_eq_blocks]]]].
      exists V00, V11.
      assert (W_eq_blocks : (diag2 u0 u1) ⊗ (I 2) ⊗ (I 2) = ∣0⟩⟨0∣ ⊗ (u0 .*(I 4)) .+ ∣0⟩⟨1∣ ⊗ Zero .+ ∣1⟩⟨0∣ ⊗ Zero .+ ∣1⟩⟨1∣ ⊗ (u1 .* (I 4))).
      {
        unfold diag2.
        lma'.
        solve_WF_matrix; apply WF_diag2.
        solve_WF_matrix.
      }
      assert (UW : U × (diag2 u0 u1 ⊗ I 2 ⊗ I 2) = ∣0⟩⟨0∣ ⊗ (u0 .* V00) .+ ∣0⟩⟨1∣ ⊗ (u1 .* V01) .+ ∣1⟩⟨0∣ ⊗ (u0 .* V10) .+ ∣1⟩⟨1∣ ⊗ (u1 .* V11)).
      {
        rewrite U_eq_blocks, W_eq_blocks; clear U_eq_blocks W_eq_blocks.
        rewrite block_multiply with
          (P00 := V00)
          (P01 := V01)
          (P10 := V10)
          (P11 := V11)
          (Q00 := u0 .* I 4)
          (Q01 := Zero)
          (Q10 := Zero)
          (Q11 := u1 .* I 4)
          (U := (∣0⟩⟨0∣ ⊗ V00 .+ ∣0⟩⟨1∣ ⊗ V01 .+ ∣1⟩⟨0∣ ⊗ V10 .+ ∣1⟩⟨1∣ ⊗ V11))
          (V := (∣0⟩⟨0∣ ⊗ (u0 .* I 4) .+ ∣0⟩⟨1∣ ⊗ Zero .+ ∣1⟩⟨0∣ ⊗ Zero .+ ∣1⟩⟨1∣ ⊗ (u1 .* I 4))) at 1; try solve_WF_matrix.
        repeat rewrite Mscale_mult_dist_r.
        Msimpl.
        reflexivity.
      }
      assert (WU : (diag2 u0 u1 ⊗ I 2 ⊗ I 2) × U = ∣0⟩⟨0∣ ⊗ (u0 .* V00) .+ ∣0⟩⟨1∣ ⊗ (u0 .* V01) .+ ∣1⟩⟨0∣ ⊗ (u1 .* V10) .+ ∣1⟩⟨1∣ ⊗ (u1 .* V11)).
      {
        rewrite U_eq_blocks, W_eq_blocks; clear U_eq_blocks W_eq_blocks.
        rewrite block_multiply with
          (P00 := u0 .* I 4)
          (P01 := Zero)
          (P10 := Zero)
          (P11 := u1 .* I 4)
          (Q00 := V00)
          (Q01 := V01)
          (Q10 := V10)
          (Q11 := V11)
          (U := (∣0⟩⟨0∣ ⊗ (u0 .* I 4) .+ ∣0⟩⟨1∣ ⊗ Zero .+ ∣1⟩⟨0∣ ⊗ Zero .+ ∣1⟩⟨1∣ ⊗ (u1 .* I 4)))
          (V := (∣0⟩⟨0∣ ⊗ V00 .+ ∣0⟩⟨1∣ ⊗ V01 .+ ∣1⟩⟨0∣ ⊗ V10 .+ ∣1⟩⟨1∣ ⊗ V11)) at 1; try solve_WF_matrix.
          repeat rewrite Mscale_mult_dist_l.
          Msimpl.
          reflexivity.
      }
      rewrite UW, WU in H; clear UW WU W_eq_blocks.
      apply (@block_equalities
        4%nat
        (∣0⟩⟨0∣ ⊗ (u0 .* V00) .+ ∣0⟩⟨1∣ ⊗ (u1 .* V01) .+ ∣1⟩⟨0∣ ⊗ (u0 .* V10) .+ ∣1⟩⟨1∣ ⊗ (u1 .* V11))
        (∣0⟩⟨0∣ ⊗ (u0 .* V00) .+ ∣0⟩⟨1∣ ⊗ (u0 .* V01) .+ ∣1⟩⟨0∣ ⊗ (u1 .* V10) .+ ∣1⟩⟨1∣ ⊗ (u1 .* V11))
        (u0 .* V00)
        (u1 .* V01)
        (u0 .* V10)
        (u1 .* V11)
        (u0 .* V00)
        (u0 .* V01)
        (u1 .* V10)
        (u1 .* V11)
      ) in H; try solve_WF_matrix; try lia.
      destruct H as [_ [V01_mult [V10_mult _]]].
      assert (H : forall {m n} (a b : C) (M : Matrix m n),
        WF_Matrix M -> a <> b -> a .* M = b .* M -> M = Zero).
      {
        intros.
        assert (H2 : a - b <> C0).
        {
          intro H2.
          apply H0.
          rewrite <- Cplus_0_l.
          rewrite <- H2.
          lca.
        }
        apply Mscale_cancel_l with (c := a - b); auto.
        unfold Cminus.
        rewrite Mscale_plus_distr_l.
        rewrite H1.
        lma'.
      }
      assert (Zero_V01 : V01 = Zero).
      {
        apply (H 4%nat 4%nat u1 u0); auto.
      }
      assert (Zero_V10 : V10 = Zero).
      {
        apply (H 4%nat 4%nat u0 u1); auto.
      }
      destruct Unitary_U as [WF_U Unitary_U].
      rewrite U_eq_blocks in Unitary_U.
      repeat rewrite Mplus_adjoint in Unitary_U.
      repeat rewrite kron_adjoint in Unitary_U.
      rewrite adjoint00, adjoint01, adjoint10, adjoint11 in Unitary_U.
      rewrite block_multiply with
        (P00 := V00†)
        (P01 := V10†)
        (P10 := V01†)
        (P11 := V11†)
        (Q00 := V00)
        (Q01 := V01)
        (Q10 := V10)
        (Q11 := V11)
        (U := (∣0⟩⟨0∣ ⊗ (V00) † .+ ∣1⟩⟨0∣ ⊗ (V01) † .+ ∣0⟩⟨1∣ ⊗ (V10) † .+ ∣1⟩⟨1∣ ⊗ (V11) †))
        (V := (∣0⟩⟨0∣ ⊗ V00 .+ ∣0⟩⟨1∣ ⊗ V01 .+ ∣1⟩⟨0∣ ⊗ V10 .+ ∣1⟩⟨1∣ ⊗ V11)) in Unitary_U at 1; solve_WF_matrix.
      {
        assert (H0 : I 8 = ∣0⟩⟨0∣ ⊗ I 4 .+ ∣0⟩⟨1∣ ⊗ Zero .+ ∣1⟩⟨0∣ ⊗ Zero .+ ∣1⟩⟨1∣ ⊗ I 4).
        {
          Msimpl.
          rewrite <- kron_plus_distr_r, Mplus01, id_kron.
          replace (2 * 4)%nat with 8%nat by lia.
          reflexivity.
        }
        rewrite H0 in Unitary_U; clear H0.
        rewrite Zero_V01, Zero_V10 in Unitary_U.
        repeat rewrite zero_adjoint_eq in Unitary_U.
        repeat rewrite Mmult_0_l in Unitary_U.
        repeat rewrite Mmult_0_r in Unitary_U.
        repeat rewrite Mplus_0_l in Unitary_U.
        repeat rewrite Mplus_0_r in Unitary_U.
        apply (
        @block_equalities
        4%nat
        (∣0⟩⟨0∣ ⊗ ((V00) † × V00) .+ ∣0⟩⟨1∣ ⊗ Zero .+ ∣1⟩⟨0∣ ⊗ Zero .+ ∣1⟩⟨1∣ ⊗ ((V11) † × V11))
        (∣0⟩⟨0∣ ⊗ I 4 .+ ∣0⟩⟨1∣ ⊗ Zero .+ ∣1⟩⟨0∣ ⊗ Zero .+ ∣1⟩⟨1∣ ⊗ I 4)
        (V00† × V00)
        Zero
        Zero
        (V11† × V11)
        (I 4)
        Zero
        Zero
        (I 4)
        ) in Unitary_U; try solve_WF_matrix; try lia.
        destruct Unitary_U as [Unitary_V00 [_ [_ Unitary_V11]]].
        split.
        {
          split; auto.
        }
        split.
        {
          split; auto.
        }
        {
          revert U_eq_blocks; rewrite Zero_V01, Zero_V10; Msimpl; intro U_eq_blocks.
          exact U_eq_blocks.
        }
      }
      {
        rewrite Zero_V01, Zero_V10; Msimpl.
        reflexivity.
      }
    }
  }
  {
    intro H.
    destruct H as [u0_eq_u1 | H].
    {
      rewrite u0_eq_u1.
      assert (diag_scale : diag2 u1 u1 = u1 .* I 2).
      {
        unfold diag2.
        lma'.
        apply WF_diag2.
      }
      rewrite diag_scale; clear diag_scale.
      repeat rewrite Mscale_kron_dist_l.
      replace (I 2 ⊗ I 2 ⊗ I 2) with (I 8) by lma'.
      rewrite Mscale_mult_dist_l.
      rewrite Mscale_mult_dist_r.
      destruct Unitary_U as [WF_U _].
      Msimpl; auto.
    }
    {
      destruct H as [V00 [V11 [[WF_V00 Unitary_V00] [[WF_V01 Unitary_V01] U_eq_blocks]]]].
      rewrite U_eq_blocks; clear U_eq_blocks.
      assert (H0 : ∣0⟩⟨0∣ ⊗ V00 .+ ∣1⟩⟨1∣ ⊗ V11 = ∣0⟩⟨0∣ ⊗ V00 .+ ∣0⟩⟨1∣ ⊗ Zero .+ ∣1⟩⟨0∣ ⊗ Zero .+ ∣1⟩⟨1∣ ⊗ V11).
      {
        Msimpl.
        reflexivity.
      }
      assert (H1 : diag2 u0 u1 ⊗ I 2 ⊗ I 2 = ∣0⟩⟨0∣ ⊗ (u0 .* I 4) .+ ∣0⟩⟨1∣ ⊗ Zero .+ ∣1⟩⟨0∣ ⊗ Zero .+ ∣1⟩⟨1∣ ⊗ (u1 .* I 4)).
      {
        unfold diag2; Msimpl; lma'.
        solve_WF_matrix; apply WF_diag2.
      }
      rewrite H0, H1; clear H0 H1.
      rewrite block_multiply with
        (P00 := V00)
        (P01 := Zero)
        (P10 := Zero)
        (P11 := V11)
        (Q00 := u0 .* I 4)
        (Q01 := Zero)
        (Q10 := Zero)
        (Q11 := u1 .* I 4)
        (U := (∣0⟩⟨0∣ ⊗ V00 .+ ∣0⟩⟨1∣ ⊗ Zero .+ ∣1⟩⟨0∣ ⊗ Zero .+ ∣1⟩⟨1∣ ⊗ V11))
        (V := (∣0⟩⟨0∣ ⊗ (u0 .* I 4) .+ ∣0⟩⟨1∣ ⊗ Zero .+ ∣1⟩⟨0∣ ⊗ Zero .+ ∣1⟩⟨1∣ ⊗ (u1 .* I 4))) at 1; try solve_WF_matrix.
      rewrite block_multiply with
        (P00 := u0 .* I 4)
        (P01 := Zero)
        (P10 := Zero)
        (P11 := u1 .* I 4)
        (Q00 := V00)
        (Q01 := Zero)
        (Q10 := Zero)
        (Q11 := V11)
        (U := (∣0⟩⟨0∣ ⊗ (u0 .* I 4) .+ ∣0⟩⟨1∣ ⊗ Zero .+ ∣1⟩⟨0∣ ⊗ Zero .+ ∣1⟩⟨1∣ ⊗ (u1 .* I 4)))
        (V := (∣0⟩⟨0∣ ⊗ V00 .+ ∣0⟩⟨1∣ ⊗ Zero .+ ∣1⟩⟨0∣ ⊗ Zero .+ ∣1⟩⟨1∣ ⊗ V11)) at 1; try solve_WF_matrix.
      repeat rewrite Mscale_mult_dist_l.
      repeat rewrite Mscale_mult_dist_r.
      Msimpl.
      reflexivity.
    }
  }
Qed.

Lemma m3_2 : forall (u0 u1 : C),
  Cmod u0 = 1 -> Cmod u1 = 1 ->
  (exists (P Q : Square 2) (V : Square 4),
    WF_Unitary P /\ WF_Unitary Q /\ WF_Unitary V /\
    P ⊗ Q = V × diag4 1 1 u0 u1 × V†)
  <-> u0 = u1 \/ u0 * u1 = C1.
Proof.
  intros u0 u1 unit_u0 unit_u1.
  split.
  {
    intro.
    destruct H as [P [Q [V [Unitary_P [Unitary_Q [Unitary_V H]]]]]].
    pose proof (a3 P Unitary_P).
    destruct H0 as [VP [DP [Unitary_VP [Diagonal_DP H0]]]].
    pose proof (a3 Q Unitary_Q).
    destruct H1 as [VQ [DQ [Unitary_VQ [Diagonal_DQ H1]]]].
    revert H.
    rewrite H0, H1; clear H0 H1.
    repeat rewrite <- kron_mixed_product.
    rewrite <- kron_adjoint.
    intro H.
    assert (H0 : (V† × (VP ⊗ VQ)) × (DP ⊗ DQ) × (V† × (VP ⊗ VQ))† = diag4 C1 C1 u0 u1).
    {
      apply (Mmult_simplify _ _ _ (V†) (V†)) in H; auto.
      apply (Mmult_simplify _ _ _ _ _ (V) (V)) in H; auto.
      symmetry in H.
      destruct Unitary_V.
      repeat rewrite Mmult_assoc in H.
      rewrite H1 in H.
      repeat rewrite <- Mmult_assoc with (A := V†) in H.
      rewrite H1 in H.
      rewrite Mmult_1_r, Mmult_1_l in H; try apply WF_diag4.
      rewrite H.
      rewrite Mmult_adjoint.
      rewrite adjoint_involutive.
      rewrite Mmult_assoc.
      reflexivity.
    }
    assert (H2 : WF_Unitary ((V) † × (VP ⊗ VQ))).
    {
      apply Mmult_unitary.
      apply adjoint_unitary; auto.
      apply kron_unitary; auto.
    }
    assert (case_A : forall (a b p q u0 u1 : C),
      a * p = C1 -> a * q = C1 -> b * p = u0 -> b * q = u1 -> u0 = u1).
    {
      intros.
      rewrite <- H4, <- H5; clear H4 H5.
      rewrite <- Cmult_1_l, <- H3 at 1.
      rewrite <- Cmult_1_l, <- H1.
      lca.
    }
    assert (case_B : forall (a b p q u0 u1 : C),
      a * p = u0 -> a * q = C1 -> b * p = C1 -> b * q = u1 -> u0 * u1 = C1).
    {
      intros.
      rewrite <- H1, <- H5; clear H1 H5.
      rewrite <- Cmult_1_l with (x := C1), <- H3, <- H4 at 1.
      lca.
    }
    pose proof (
      perm_eigenvalues (V† × (VP ⊗ VQ)) (DP ⊗ DQ) (diag4 1 1 u0 u1) H2
      (diag_kron DP DQ Diagonal_DP Diagonal_DQ) (Diag_diag4 C1 C1 u0 u1)
      H0
    ) as [σ [permutation_σ H1]].

    specialize (H1 0%nat) as H1_0; simpl in H1_0.
    specialize (H1 1%nat) as H1_1; simpl in H1_1.
    specialize (H1 2%nat) as H1_2; simpl in H1_2.
    specialize (H1 3%nat) as H1_3; simpl in H1_3.
    unfold kron, diag4 in H1_0, H1_1, H1_2, H1_3.

    pose proof (permutation_4_decomp σ permutation_σ) as perm.
    destruct_disjunctions perm.
    all: destruct perm as [σ0 [σ1 [σ2 σ3]]].
    all: rewrite σ0 in H1_0; simpl in H1_0; clear σ0.
    all: rewrite σ1 in H1_1; simpl in H1_1; clear σ1.
    all: rewrite σ2 in H1_2; simpl in H1_2; clear σ2.
    all: rewrite σ3 in H1_3; simpl in H1_3; clear σ3.
    {
      left.
      apply (case_A (DP 0 0) (DP 1 1) (DQ 0 0) (DQ 1 1))%nat; assumption.
    }
    {
      left.
      apply (case_A (DP 0 0) (DP 1 1) (DQ 1 1) (DQ 0 0))%nat; assumption.
    }
    {
      left.
      rewrite Cmult_comm in H1_0, H1_1, H1_2, H1_3.
      apply (case_A (DQ 0 0) (DQ 1 1) (DP 0 0) (DP 1 1))%nat; assumption.
    }
    {
      right.
      apply (case_B (DP 0 0) (DP 1 1) (DQ 1 1) (DQ 0 0))%nat; assumption.
    }
    {
      left.
      rewrite Cmult_comm in H1_0, H1_1, H1_2, H1_3.
      apply (case_A (DQ 0 0) (DQ 1 1) (DP 1 1) (DP 0 0))%nat; assumption.
    }
    {
      right.
      apply (case_B (DP 1 1) (DP 0 0) (DQ 0 0) (DQ 1 1))%nat; assumption.
    }
    {
      left.
      apply (case_A (DP 0 0) (DP 1 1) (DQ 0 0) (DQ 1 1))%nat; assumption.
    }
    {
      left.
      apply (case_A (DP 0 0) (DP 1 1) (DQ 1 1) (DQ 0 0))%nat; assumption.
    }
    {
      left.
      rewrite Cmult_comm in H1_0, H1_1, H1_2, H1_3.
      apply (case_A (DQ 0 0) (DQ 1 1) (DP 0 0) (DP 1 1))%nat; assumption.
    }
    {
      right.
      apply (case_B (DP 0 0) (DP 1 1) (DQ 1 1) (DQ 0 0))%nat; assumption.
    }
    {
      left.
      rewrite Cmult_comm in H1_0, H1_1, H1_2, H1_3.
      apply (case_A (DQ 0 0) (DQ 1 1) (DP 1 1) (DP 0 0))%nat; assumption.
    }
    {
      right.
      apply (case_B (DP 1 1) (DP 0 0) (DQ 0 0) (DQ 1 1))%nat; assumption.
    }
    {
      right.
      apply (case_B (DP 0 0) (DP 1 1) (DQ 0 0) (DQ 1 1))%nat; assumption.
    }
    {
      left.
      rewrite Cmult_comm in H1_0, H1_1, H1_2, H1_3.
      apply (case_A (DQ 1 1) (DQ 0 0) (DP 0 0) (DP 1 1))%nat; assumption.
    }
    {
      right.
      apply (case_B (DP 0 0) (DP 1 1) (DQ 0 0) (DQ 1 1))%nat; assumption.
    }
    {
      left.
      rewrite Cmult_comm in H1_0, H1_1, H1_2, H1_3.
      apply (case_A (DQ 1 1) (DQ 0 0) (DP 0 0) (DP 1 1))%nat; assumption.
    }
    {
      left.
      apply (case_A (DP 1 1) (DP 0 0) (DQ 0 0) (DQ 1 1))%nat; assumption.
    }
    {
      left.
      apply (case_A (DP 1 1) (DP 0 0) (DQ 0 0) (DQ 1 1))%nat; assumption.
    }
    {
      right.
      apply (case_B (DP 1 1) (DP 0 0) (DQ 1 1) (DQ 0 0))%nat; assumption.
    }
    {
      left.
      rewrite Cmult_comm in H1_0, H1_1, H1_2, H1_3.
      apply (case_A (DQ 1 1) (DQ 0 0) (DP 1 1) (DP 0 0))%nat; assumption.
    }
    {
      right.
      apply (case_B (DP 1 1) (DP 0 0) (DQ 1 1) (DQ 0 0))%nat; assumption.
    }
    {
      left.
      rewrite Cmult_comm in H1_0, H1_1, H1_2, H1_3.
      apply (case_A (DQ 1 1) (DQ 0 0) (DP 1 1) (DP 0 0))%nat; assumption.
    }
    {
      left.
      apply (case_A (DP 1 1) (DP 0 0) (DQ 1 1) (DQ 0 0))%nat; assumption.
    }
    {
      left.
      apply (case_A (DP 1 1) (DP 0 0) (DQ 1 1) (DQ 0 0))%nat; assumption.
    }
  }
  {
    intro.
    destruct H as [u0_eq_u1 | u0u1_eq_1].
    {
      exists (diag2 C1 u1), (I 2), (I 4).
      split.
      {
        unfold WF_Unitary.
        split; try apply WF_diag2.
        lma'.
        solve_WF_matrix; try apply WF_diag2.
        unfold adjoint, diag2, I, Mmult; simpl.
        Csimpl.
        rewrite <- Cmod_sqr, unit_u1.
        lca.
      }
      {
        split; try apply id_unitary.
        split; try apply id_unitary.
        Msimpl; try apply WF_diag4.
        rewrite u0_eq_u1.
        lma'.
        apply WF_kron; try apply WF_diag2; try apply WF_I; auto.
        apply WF_diag4.
        unfold kron, diag2, diag4, I; simpl; lca.
        unfold kron, diag2, diag4, I; simpl; lca.
      }
    }
    {
      exists (diag2 C1 u0), (diag2 C1 u1), notc.
      split.
      {
        unfold WF_Unitary; split; try apply WF_diag2.
        lma'; try solve_WF_matrix; try apply WF_diag2.
        unfold adjoint, diag2, Mmult, I; simpl; Csimpl.
        rewrite <- Cmod_sqr, unit_u0; lca.
      }
      split.
      {
        unfold WF_Unitary; split; try apply WF_diag2.
        lma'; try solve_WF_matrix; try apply WF_diag2.
        unfold adjoint, diag2, Mmult, I; simpl; Csimpl.
        rewrite <- Cmod_sqr, unit_u1; lca.
      }
      split.
      {
        exact notc_unitary.
      }
      {
        lma'.
        solve_WF_matrix; try apply WF_diag2.
        repeat apply WF_mult.
        apply WF_notc.
        apply WF_diag4.
        apply WF_adjoint, WF_notc.
        unfold diag2, diag4; lca.
        unfold diag2, diag4; lca.
        unfold notc, Mmult, adjoint; simpl; Csimpl.
        exact u0u1_eq_1.
      }
    }
  }
Qed.

Lemma m3_3 : forall (u0 u1 : C),
  Cmod u0 = 1 -> Cmod u1 = 1 ->
    (exists (P : Square 2), WF_Unitary P /\
      exists (U : Square 4), WF_Unitary U /\
        exists (c d : C), c <> C0 /\ d <> C0 /\
          ((I 2) ⊗ P) × control (diag2 u0 u1) = U × diag4 c c d d × U†)
    <-> u0 = u1 \/ u0 * u1 = C1.
Proof.
  intros u0 u1 unit_u0 unit_u1.
  split.
  {
    intro.
    destruct H as [P [Unitary_P [U [Unitary_U [c [d [c_neq_0 [d_neq_0 H]]]]]]]].
    set (PD := P × diag2 u0 u1).
    assert (Unitary_PD : WF_Unitary (P × diag2 u0 u1)).
    {
      apply Mmult_unitary; auto.
      unfold WF_Unitary; split; try apply WF_diag2.
      lma'; try solve_WF_matrix; try apply WF_diag2.
      unfold adjoint, diag2, Mmult, I; simpl; Csimpl.
      rewrite <- Cmod_sqr, unit_u0; lca.
      unfold adjoint, diag2, Mmult, I; simpl; Csimpl.
      rewrite <- Cmod_sqr, unit_u1; lca.
    }
    assert (step : control (diag2 u0 u1) = I 2 .⊕ diag2 u0 u1).
    {
      rewrite (direct_sum_decomp _ _ 2 2)%nat; auto.
      lma'.
      apply WF_control, WF_diag2.
      solve_WF_matrix; apply WF_diag2.
      unfold control, diag2, adjoint, I, kron, Mmult, Mplus; simpl; lca.
      unfold control, diag2, adjoint, I, kron, Mmult, Mplus; simpl; lca.
      apply WF_I.
      apply WF_diag2.
    }
    assert (step2 : (I 2 ⊗ P) × control (diag2 u0 u1) = P .⊕ PD).
    {
      rewrite step.
      repeat rewrite (direct_sum_decomp _ _ 2 2)%nat; auto.
      rewrite Mmult_plus_distr_l.
      repeat rewrite kron_mixed_product; Msimpl_light.
      reflexivity.
      apply Unitary_P.
      apply Unitary_P.
      apply Unitary_PD.
      apply WF_I.
      apply WF_diag2.
    }
    pose proof (a3 P Unitary_P) as [VP [DP [Unitary_VP [Diagonal_DP P_decomp]]]].
    pose proof (a3 PD Unitary_PD) as [VPD [DPD [Unitary_VPD [Diagonal_DPD PD_decomp]]]].
    assert (step3 : exists σ : nat -> nat,
      permutation 4 σ /\ (forall i : nat, (DP .⊕ DPD) i i = diag4 c c d d (σ i) (σ i))).
    {
      apply (a6 P PD VP DP VPD DPD U); auto.
      apply Diag_diag4.
      rewrite H in step2.
      symmetry; exact step2.
    }
    destruct step3 as [σ [permutation_σ step3]].

    all: specialize (step3 0%nat) as eigen0.
    all: specialize (step3 1%nat) as eigen1.
    all: specialize (step3 2%nat) as eigen2.
    all: specialize (step3 3%nat) as eigen3.

    assert (case_A : forall (c d : C), (c <> C0 -> DP 0 0 = c -> DP 1 1 = c ->
      DPD 0 0 = d -> DPD 1 1 = d -> u0 = u1)%nat).
    {
      intros.
      assert (DP_cI : DP = c0 .* I 2).
      {
        lma'.
        {
          apply Diagonal_DP.
        }
        {
          unfold scale, I; simpl.
          rewrite H1; lca.
        }
        {
          unfold scale, I; simpl.
          destruct Diagonal_DP as [_ DP_0].
          specialize (DP_0 0 1)%nat.
          rewrite DP_0; auto.
          lca.
        }
        {
          unfold scale, I; simpl.
          destruct Diagonal_DP as [_ DP_0].
          specialize (DP_0 1 0)%nat.
          rewrite DP_0; auto.
          lca.
        }
        {
          unfold scale, I; simpl.
          rewrite H2; lca.
        }
      }
      assert (DPD_dI : DPD = d0 .* I 2).
      {
        lma'.
        {
          apply Diagonal_DPD.
        }
        {
          unfold scale, I; simpl.
          rewrite H3; lca.
        }
        {
          destruct Diagonal_DPD as [_ DPD_0].
          specialize (DPD_0 0 1)%nat.
          rewrite DPD_0; auto.
          lca.
        }
        {
          destruct Diagonal_DPD as [_ DPD_0].
          specialize (DPD_0 1 0)%nat.
          rewrite DPD_0; auto.
          lca.
        }
        {
          unfold scale, I; simpl.
          rewrite H4; lca.
        }
      }
      rewrite DP_cI in P_decomp; clear DP_cI.
      rewrite DPD_dI in PD_decomp; clear DPD_dI.
      clear H1 H2.
      assert (diag2_decomp : forall (x : C), diag2 x x = x .* I 2).
      {
        intros.
        lma'.
        apply WF_diag2.
        unfold diag2; lca.
        unfold diag2; lca.
      }
      assert (P_cI : P = c0 .* I 2).
      {
        rewrite P_decomp.
        rewrite Mscale_mult_dist_r.
        rewrite Mmult_1_r; try apply Unitary_VP.
        rewrite Mscale_mult_dist_l.
        rewrite other_unitary_decomp; auto.
      }
      assert (PD_dI : PD = d0 .* I 2).
      {
        rewrite PD_decomp.
        rewrite Mscale_mult_dist_r.
        rewrite Mmult_1_r; try apply Unitary_VPD.
        rewrite Mscale_mult_dist_l.
        rewrite other_unitary_decomp; auto.
      }
      unfold PD in PD_dI.
      rewrite P_cI in PD_dI; clear P_cI.
      rewrite Mscale_mult_dist_l in PD_dI.
      rewrite Mmult_1_l in PD_dI; try apply WF_diag2.
      assert (cu0_d : c0 * u0 = d0).
      {
        apply (f_equal (fun f => f 0 0)%nat) in PD_dI.
        unfold scale, diag2, I in PD_dI; simpl in PD_dI.
        rewrite PD_dI; lca.
      }
      assert (cu1_d : c0 * u1 = d0).
      {
        apply (f_equal (fun f => f 1 1)%nat) in PD_dI.
        unfold scale, diag2, I in PD_dI; simpl in PD_dI.
        rewrite PD_dI; lca.
      }
      apply (Cmult_cancel_l c0); try apply H0.
      rewrite cu0_d, cu1_d; reflexivity.
    }
    assert (case_B : forall (c d : C), c <> C0 -> d <> C0 ->
      (DP 0 0)%nat = c -> (DP 1 1)%nat = d ->
      (DPD 0 0)%nat = c -> (DPD 1 1)%nat = d -> u0 * u1 = C1).
    {
      intros.
      assert (DP_diag : DP = diag2 c0 d0).
      {
        lma'.
        {
          apply Diagonal_DP.
        }
        {
          apply WF_diag2.
        }
        {
          unfold diag2; simpl.
          rewrite H2; reflexivity.
        }
        {
          destruct Diagonal_DP as [_ DP_0].
          specialize (DP_0 0 1)%nat.
          rewrite DP_0; auto.
        }
        {
          destruct Diagonal_DP as [_ DP_0].
          specialize (DP_0 1 0)%nat.
          rewrite DP_0; auto.
        }
        {
          unfold diag2; simpl.
          rewrite H3; reflexivity.
        }
      }
      assert (DPD_diag : DPD = diag2 c0 d0).
      {
        lma'.
        {
          apply Diagonal_DPD.
        }
        {
          apply WF_diag2.
        }
        {
          unfold diag2; simpl.
          rewrite H4; reflexivity.
        }
        {
          destruct Diagonal_DPD as [_ DPD_0].
          specialize (DPD_0 0 1)%nat.
          rewrite DPD_0; auto.
        }
        {
          destruct Diagonal_DPD as [_ DPD_0].
          specialize (DPD_0 1 0)%nat.
          rewrite DPD_0; auto.
        }
        {
          unfold diag2; simpl.
          rewrite H5; reflexivity.
        }
      }
      rewrite DP_diag in P_decomp; clear DP_diag.
      rewrite DPD_diag in PD_decomp; clear DPD_diag.
      assert (detP : Determinant P = c0 * d0).
      {
        rewrite P_decomp.
        repeat rewrite a1.
        rewrite Cmult_comm, Cmult_assoc.
        rewrite <- a1.
        destruct Unitary_VP as [_ Unitary_VP].
        rewrite Unitary_VP.
        rewrite Det_I, Cmult_1_l.
        apply Det_diag2.
      }
      assert (detPD : Determinant PD = c0 * d0).
      {
        rewrite PD_decomp.
        repeat rewrite a1.
        rewrite Cmult_comm, Cmult_assoc.
        rewrite <- a1.
        destruct Unitary_VPD as [_ Unitary_VPD].
        rewrite Unitary_VPD.
        rewrite Det_I, Cmult_1_l.
        rewrite Det_diag2; reflexivity.
      }
      unfold PD in detPD.
      rewrite a1 in detPD.
      rewrite detP, Det_diag2 in detPD.
      apply (Cmult_cancel_l (c0 * d0)).
      apply Cmult_nonzero; auto.
      rewrite detPD; lca.
    }
    assert (case_C : forall (c d : C), c <> C0 -> d <> C0 ->
      (DP 0 0)%nat = c -> (DP 1 1)%nat = d ->
      (DPD 0 0)%nat = d -> (DPD 1 1)%nat = c -> u0 * u1 = C1).
    {
      intros.
      assert (DP_diag : DP = diag2 c0 d0).
      {
        lma'.
        {
          apply Diagonal_DP.
        }
        {
          apply WF_diag2.
        }
        {
          unfold diag2; simpl.
          rewrite H2; reflexivity.
        }
        {
          destruct Diagonal_DP as [_ DP_0].
          specialize (DP_0 0 1)%nat.
          rewrite DP_0; auto.
        }
        {
          destruct Diagonal_DP as [_ DP_0].
          specialize (DP_0 1 0)%nat.
          rewrite DP_0; auto.
        }
        {
          unfold diag2; simpl.
          rewrite H3; reflexivity.
        }
      }
      assert (DPD_diag : DPD = diag2 d0 c0).
      {
        lma'.
        {
          apply Diagonal_DPD.
        }
        {
          apply WF_diag2.
        }
        {
          unfold diag2; simpl.
          rewrite H4; reflexivity.
        }
        {
          destruct Diagonal_DPD as [_ DPD_0].
          specialize (DPD_0 0 1)%nat.
          rewrite DPD_0; auto.
        }
        {
          destruct Diagonal_DPD as [_ DPD_0].
          specialize (DPD_0 1 0)%nat.
          rewrite DPD_0; auto.
        }
        {
          unfold diag2; simpl.
          rewrite H5; reflexivity.
        }
      }
      rewrite DP_diag in P_decomp; clear DP_diag.
      rewrite DPD_diag in PD_decomp; clear DPD_diag.
      unfold PD in PD_decomp.
      assert (detP : Determinant P = c0 * d0).
      {
        rewrite P_decomp.
        repeat rewrite a1.
        rewrite Cmult_comm, Cmult_assoc.
        rewrite <- a1.
        destruct Unitary_VP as [_ Unitary_VP].
        rewrite Unitary_VP.
        rewrite Det_I, Cmult_1_l.
        apply Det_diag2.
      }
      assert (detPD : Determinant PD = c0 * d0).
      {
        unfold PD.
        rewrite PD_decomp.
        repeat rewrite a1.
        rewrite Cmult_comm, Cmult_assoc.
        rewrite <- a1.
        destruct Unitary_VPD as [_ Unitary_VPD].
        rewrite Unitary_VPD.
        rewrite Det_I, Cmult_1_l.
        rewrite Det_diag2, Cmult_comm; reflexivity.
      }
      unfold PD in detPD.
      rewrite a1 in detPD.
      rewrite detP, Det_diag2 in detPD.
      apply (Cmult_cancel_l (c0 * d0)).
      apply Cmult_nonzero; auto.
      rewrite detPD; lca.
    }

    pose proof (permutation_4_decomp σ permutation_σ) as perm.
    destruct_disjunctions perm.
    all: destruct perm as [σ0 [σ1 [σ2 σ3]]].
    all: unfold direct_sum, diag4 in eigen0; rewrite σ0 in eigen0; simpl in eigen0; clear σ0.
    all: unfold direct_sum, diag4 in eigen1; rewrite σ1 in eigen1; simpl in eigen1; clear σ1.
    all: unfold direct_sum, diag4 in eigen2; rewrite σ2 in eigen2; simpl in eigen2; clear σ2.
    all: unfold direct_sum, diag4 in eigen3; rewrite σ3 in eigen3; simpl in eigen3; clear σ3.
    {
      left.
      apply (case_A c d); auto.
    }
    {
      left.
      apply (case_A c d); auto.
    }
    {
      right.
      apply (case_B c d); auto.
    }
    {
      right.
      apply (case_C c d); auto.
    }
    {
      right.
      apply (case_B c d); auto.
    }
    {
      right.
      apply (case_C c d); auto.
    }
    {
      left.
      apply (case_A c d); auto.
    }
    {
      left.
      apply (case_A c d); auto.
    }
    {
      right.
      apply (case_B c d); auto.
    }
    {
      right.
      apply (case_C c d); auto.
    }
    {
      right.
      apply (case_B c d); auto.
    }
    {
      right.
      apply (case_C c d); auto.
    }
    {
      right.
      apply (case_C d c); auto.
    }
    {
      right.
      apply (case_B d c); auto.
    }
    {
      right.
      apply (case_C d c); auto.
    }
    {
      right.
      apply (case_B d c); auto.
    }
    {
      left.
      apply (case_A d c); auto.
    }
    {
      left.
      apply (case_A d c); auto.
    }
    {
      right.
      apply (case_C d c); auto.
    }
    {
      right.
      apply (case_B d c); auto.
    }
    {
      right.
      apply (case_C d c); auto.
    }
    {
      right.
      apply (case_B d c); auto.
    }
    {
      left.
      apply (case_A d c); auto.
    }
    {
      left.
      apply (case_A d c); auto.
    }
  }
  {
    intro.
    destruct H as [u0_is_u1 | u0u1_is_1].
    {
      rewrite <- u0_is_u1.
      exists (I 2).
      split; try apply id_unitary.
      exists (I 4).
      split; try apply id_unitary.
      exists C1, u0.
      split; try apply C1_neq_C0.
      split. rewrite Cmod_gt_0, unit_u0; lra.
      rewrite id_kron; Msimpl; try apply WF_diag4.
      {
        lma'; solve_WF_matrix.
        apply WF_diag2.
        apply WF_diag4.
      }
      {
        apply WF_control, WF_diag2.
      }
    }
    {
      exists (diag2 C1 u0).
      split.
      {
        unfold WF_Unitary; split; try apply WF_diag2.
        lma'; try solve_WF_matrix; try apply WF_diag2.
        unfold adjoint, diag2, Mmult, I; simpl; Csimpl.
        rewrite <- Cmod_sqr, unit_u0; lca.
      }
      {
        exists notc.
        split.
        {
          exact notc_unitary.
        }
        {
          exists C1, u0.
          split; try apply C1_neq_C0.
          split; try rewrite Cmod_gt_0, unit_u0; try lra.
          assert (H : I 2 ⊗ diag2 C1 u0 × control (diag2 u0 u1) = diag4 C1 u0 u0 (u0 * u1)).
          {
            lma'; solve_WF_matrix; try apply WF_diag2; try apply WF_diag4.
            all: unfold diag4, diag2, kron, Mmult; simpl; Csimpl; reflexivity.
          }
          rewrite H; clear H.
          rewrite u0u1_is_1; clear u0u1_is_1.
          lma'.
          {
            apply WF_diag4.
          }
          {
            repeat apply WF_mult.
            apply WF_notc.
            apply WF_diag4.
            apply WF_adjoint, WF_notc.
          }
          all: unfold diag4, swap, cnot, Mmult, adjoint; simpl; Csimpl; reflexivity.
        }
      }
    }
  }
Qed.

Lemma m4_1 : forall (u0 u1 : C),
  Cmod u0 = 1 -> Cmod u1 = 1 ->
    (exists (U V : Square 4) (P0 P1 Q0 Q1: Square 2),
      WF_Unitary U /\ WF_Unitary V /\ WF_Unitary P0 /\ WF_Unitary P1 /\ WF_Unitary Q0 /\ WF_Unitary Q1 /\
      ∣0⟩⟨0∣ ⊗ (U × (P0 ⊗ Q0) × V) .+ ∣1⟩⟨1∣ ⊗ (U × (P1 ⊗ Q1) × V) = ccu (diag2 u0 u1))
    <-> u0 = u1 \/ u0 * u1 = 1.
Proof.
  split.
  - admit.
  - intros.
    destruct H1.
    + exists (I 4), (I 4), (I 2), (diag2 1 u1), (I 2), (I 2).
      assert (diag2_unitary : WF_Unitary (diag2 1 u1)).
      {
        split.
        - apply WF_diag2.
        - solve_matrix.
          unfold diag2; simpl.
          rewrite <- Cmod_sqr.
          rewrite H0.
          lca.
      }
      split. apply id_unitary.
      split. apply id_unitary.
      split. apply id_unitary.
      split. apply diag2_unitary.
      split. apply id_unitary.
      split. apply id_unitary.
      (* This line removes a lot of subgoals created by the following Msimpl *)
      assert (WF_my_diag2 : WF_Matrix (diag2 1 u1)). apply WF_diag2.
      Msimpl.
      lma'.
      do 2 apply WF_control; apply WF_diag2.
      {
        unfold kron, adjoint, Mmult, Mplus, ccu, control, diag2, I, qubit0, qubit1; simpl.
        Csimpl.
        symmetry; exact H1.
      }
      {
        unfold kron, adjoint, Mmult, Mplus, ccu, control, diag2, I, qubit0, qubit1; simpl.
        Csimpl.
        reflexivity.
      }
    + exists notc, notc, (I 2), (diag2 1 u0), (I 2), (diag2 1 u1).
      assert (diag2_unitary : forall u, Cmod u = 1 -> WF_Unitary (diag2 1 u)).
      {
        split.
        - apply WF_diag2.
        - solve_matrix.
          unfold diag2; simpl.
          rewrite <- Cmod_sqr.
          rewrite H2.
          lca.
      }
      split. apply notc_unitary.
      split. apply notc_unitary.
      split. apply id_unitary.
      split. apply diag2_unitary; exact H.
      split. apply id_unitary.
      split. apply diag2_unitary; exact H0.
      (* This line removes a lot of subgoals created by the following Msimpl *)
      assert (WF_my_diag2 : WF_Matrix (diag2 u0 1)). apply WF_diag2.
      Msimpl.
      lma'.
      {
        apply WF_plus.
        - apply WF_kron. lia. lia.
          solve_WF_matrix.
          apply WF_mult.
          solve_WF_matrix.
          apply WF_notc.
        - apply WF_kron. lia. lia.
          solve_WF_matrix.
          apply WF_mult.
          solve_WF_matrix.
          apply WF_diag2.
          apply WF_diag2.
          apply WF_notc.
      }
      do 2 apply WF_control; apply WF_diag2.
      {
        unfold kron, adjoint, Mmult, Mplus, ccu, control, diag2, I, qubit0, qubit1; simpl.
        Csimpl.
        assumption.
      }
      {
        unfold kron, adjoint, Mmult, Mplus, ccu, control, diag2, I, qubit0, qubit1; simpl.
        Csimpl.
        reflexivity.
      }
      {
        unfold kron, adjoint, Mmult, Mplus, ccu, control, diag2, I, qubit0, qubit1; simpl.
        Csimpl.
        reflexivity.
      }
Admitted.

Lemma m4_2 : forall (u0 u1 : C),
  Cmod u0 = 1 -> Cmod u1 = 1 ->
  forall (Q : Square 2),
    WF_Unitary Q ->
    let beta : Vector 2 := Q × ∣0⟩ in
    let beta_perp := Q × ∣1⟩ in
    (exists (P0 P1 : Square 2) (a b p q : C) (v1 v2 v3 v4 : Vector 2),
      WF_Unitary P0 /\ WF_Unitary P1 /\
      WF_Matrix v1 /\ WF_Matrix v2 /\ WF_Matrix v3 /\ WF_Matrix v4 /\
      v1 <> Zero /\ v2 <> Zero /\ v3 <> Zero /\ v4 <> Zero /\
      Eigenpair P0 (v1, a) /\ Eigenpair P0 (v2, b) /\
      Eigenpair P1 (v3, p) /\ Eigenpair P1 (v4, q) /\
      I 2 ⊗ I 2 ⊗ (beta × beta†) .+ P0 ⊗ P1 ⊗ (beta_perp × beta_perp†) = ccu (diag2 u0 u1))
    <-> u0 = 1 /\ u1 = 1.
Proof.
  intros.
  assert (WF_Q : WF_Matrix Q).
  {
    destruct H1.
    assumption.
  }
  assert (WF_beta : WF_Matrix beta) by solve_WF_matrix.
  assert (WF_beta_perp : WF_Matrix beta_perp) by solve_WF_matrix.
  assert (WF_beta_beta : WF_Matrix (beta × beta†)).
  {
    apply WF_mult.
    assumption.
    apply WF_adjoint.
    assumption.
  }
  pose (a := beta 0%nat 0%nat).
  pose (b := beta 1%nat 0%nat).
  split.
  - intros.
    destruct H2 as [P0 [P1 [c1 [c2 [c3 [c4 [v1 [v2 [v3 [v4 H2]]]]]]]]]].
    destruct H2 as [Unitary_P0 [Unitary_P1 H2]].
    destruct H2 as [WF_v1 [WF_v2 [WF_v3 [WF_v4 H2]]]].
    destruct H2 as [v1_nonzero [v2_nonzero [v3_nonzero [v4_nonzero H2]]]].
    destruct H2 as [epair1 [epair2 [epair3 [epair4 H2]]]].
    destruct (Ceq_dec a C0) as [a_zero | a_nonzero].
    + assert (unit_b : b^* * b = 1).
      {
        destruct H1.
        apply (f_equal (fun f => f 0%nat 0%nat)) in H3.
        unfold Mmult, adjoint, I in H3.
        simpl in H3.
        replace (Q 0%nat 0%nat) with a in H3 by lca.
        replace (Q 1%nat 0%nat) with b in H3 by lca.
        rewrite <- H3.
        rewrite a_zero.
        lca.
      }
      assert (beta_mult_1_1 : beta × beta† = ∣1⟩⟨1∣).
      {
        unfold beta, adjoint, qubit0, qubit1, Mmult.
        simpl.
        lma'.
        all: replace (Q 0%nat 0%nat) with a by lca.
        all: replace (Q 1%nat 0%nat) with b by lca.
        - rewrite a_zero.
          Csimpl.
          reflexivity.
        - rewrite a_zero.
          Csimpl.
          reflexivity.
        - rewrite a_zero.
          Csimpl.
          reflexivity.
        - Csimpl.
          rewrite Cmult_comm.
          rewrite unit_b.
          reflexivity.
      }
      assert (beta_perp_mult_0_0 : beta_perp × (beta_perp) † = ∣0⟩⟨0∣).
      {
        pose proof (a8 Q H1) as H3.
        unfold beta, beta_perp.
        apply Mplus_cancel_l with (A := ∣1⟩⟨1∣).
        rewrite Mplus10.
        rewrite <- H3.
        rewrite <- beta_mult_1_1.
        unfold beta.
        reflexivity.
      }
      rewrite beta_mult_1_1 in H2.
      rewrite beta_perp_mult_0_0 in H2.
      assert (u1_is_1 : u1 = C1).
      {
        apply f_equal with (f := fun f => f 7%nat 7%nat) in H2.
        unfold kron, Mmult, Mplus, adjoint, ccu, control, diag2, I, qubit0, qubit1 in H2; simpl in H2.
        revert H2; Csimpl; intro H2.
        auto.
      }
      assert (u0_is_1 : u0 = C1).
      {
        pose proof H2 as H3.
        pose proof H2 as H4.
        pose proof H2 as H5.
        pose proof H2 as H6.
        apply f_equal with (f := fun f => f 0%nat 0%nat) in H3.
        unfold kron, Mmult, Mplus, adjoint, ccu, control, diag2, I, qubit0, qubit1 in H3; simpl in H3.
        revert H3; Csimpl; intro H3.
        apply f_equal with (f := fun f => f 2%nat 2%nat) in H4.
        unfold kron, Mmult, Mplus, adjoint, ccu, control, diag2, I, qubit0, qubit1 in H4; simpl in H4.
        revert H4; Csimpl; intro H4.
        apply f_equal with (f := fun f => f 4%nat 4%nat) in H5.
        unfold kron, Mmult, Mplus, adjoint, ccu, control, diag2, I, qubit0, qubit1 in H5; simpl in H5.
        revert H5; Csimpl; intro H5.
        apply f_equal with (f := fun f => f 6%nat 6%nat) in H6.
        unfold kron, Mmult, Mplus, adjoint, ccu, control, diag2, I, qubit0, qubit1 in H6; simpl in H6.
        revert H6; Csimpl; intro H6.
        rewrite <- Cmult_1_l at 1.
        rewrite <- Cmult_1_l.
        rewrite <- H3 at 1.
        rewrite <- H4 at 1.
        rewrite <- H5 at 1.
        rewrite <- H6 at 1.
        lca.
      }
      split; auto.
    + destruct (Ceq_dec b C0) as [b_zero | b_nonzero].
      * assert (unit_a : a^* * a = 1).
        {
          destruct H1.
          apply (f_equal (fun f => f 0%nat 0%nat)) in H3.
          unfold Mmult, adjoint, I in H3.
          simpl in H3.
          replace (Q 0%nat 0%nat) with a in H3 by lca.
          replace (Q 1%nat 0%nat) with b in H3 by lca.
          rewrite <- H3.
          rewrite b_zero.
          lca.
        }
        assert (beta_mult_0_0 : beta × beta† = ∣0⟩⟨0∣).
        {
          unfold beta, adjoint, qubit0, qubit1, Mmult.
          simpl.
          lma'.
          all: replace (Q 0%nat 0%nat) with a by lca.
          all: replace (Q 1%nat 0%nat) with b by lca.
          Csimpl.
          rewrite Cmult_comm.
          rewrite unit_a.
          reflexivity.
          rewrite b_zero.
          Csimpl.
          reflexivity.
          rewrite b_zero.
          Csimpl.
          reflexivity.
          rewrite b_zero.
          Csimpl.
          reflexivity.
        }
        assert (beta_perp_mult_1_1 : beta_perp × (beta_perp) † = ∣1⟩⟨1∣).
        {
          pose proof (a8 Q H1) as H3.
          replace (Q × ∣0⟩) with beta in H3 by reflexivity.
          replace (Q × ∣1⟩) with beta_perp in H3 by reflexivity.
          rewrite beta_mult_0_0 in H3.
          rewrite <- Mplus01 in H3.
          apply Mplus_cancel_l in H3.
          assumption.
        }
        rewrite beta_mult_0_0 in H2.
        rewrite beta_perp_mult_1_1 in H2.
        assert (u0_is_1 : u0 = C1).
        {
          apply f_equal with (f := fun f => f 6%nat 6%nat) in H2.
          unfold kron, Mmult, Mplus, adjoint, ccu, control, diag2, I, qubit0, qubit1 in H2; simpl in H2.
          revert H2; Csimpl; intro H2.
          auto.
        }
        assert (u1_is_1 : u1 = C1).
        {
          pose proof H2 as H3.
          pose proof H2 as H4.
          pose proof H2 as H5.
          pose proof H2 as H6.
          apply f_equal with (f := fun f => f 1%nat 1%nat) in H3.
          unfold kron, Mmult, Mplus, adjoint, ccu, control, diag2, I, qubit0, qubit1 in H3; simpl in H3.
          revert H3; Csimpl; intro H3.
          apply f_equal with (f := fun f => f 3%nat 3%nat) in H4.
          unfold kron, Mmult, Mplus, adjoint, ccu, control, diag2, I, qubit0, qubit1 in H4; simpl in H4.
          revert H4; Csimpl; intro H4.
          apply f_equal with (f := fun f => f 5%nat 5%nat) in H5.
          unfold kron, Mmult, Mplus, adjoint, ccu, control, diag2, I, qubit0, qubit1 in H5; simpl in H5.
          revert H5; Csimpl; intro H5.
          apply f_equal with (f := fun f => f 7%nat 7%nat) in H6.
          unfold kron, Mmult, Mplus, adjoint, ccu, control, diag2, I, qubit0, qubit1 in H6; simpl in H6.
          revert H6; Csimpl; intro H6.
          rewrite <- Cmult_1_l at 1.
          rewrite <- Cmult_1_l.
          rewrite <- H3 at 1.
          rewrite <- H4 at 1.
          rewrite <- H5 at 1.
          rewrite <- H6 at 1.
          lca.
        }
        split; assumption.
      * apply (f_equal (fun f => f × (∣1⟩ ⊗ ∣1⟩ ⊗ beta))) in H2.
        assert (H3 : beta_perp† × beta = Zero).
        {
          unfold beta_perp, beta.
          rewrite Mmult_adjoint.
          rewrite <- Mmult_assoc.
          rewrite Mmult_assoc with (A := ⟨1∣).
          destruct H1.
          rewrite H3.
          rewrite Mmult_1_r. 2: exact (WF_bra 1).
          exact Mmult10.
        }
        assert (H4 : beta† × beta = I 1).
        {
          unfold beta, beta_perp.
          rewrite Mmult_adjoint.
          rewrite <- Mmult_assoc.
          do 2 rewrite Mmult_assoc.
          rewrite <- Mmult_assoc with (B := Q).
          destruct H1.
          rewrite H4.
          Msimpl.
          exact Mmult00.
        }
        rewrite Mmult_plus_distr_r in H2.
        assert (step1 : I 2 ⊗ I 2 ⊗ (beta × (beta) †) × (∣1⟩ ⊗ ∣1⟩ ⊗ beta) = ∣1⟩ ⊗ ∣1⟩ ⊗ beta).
        {
          repeat rewrite kron_mixed_product.
          rewrite Mmult_assoc.
          rewrite H4.
          Msimpl.
          reflexivity.
        }
        assert (step2 : P0 ⊗ P1 ⊗ (beta_perp × (beta_perp) †) × (∣1⟩ ⊗ ∣1⟩ ⊗ beta) = Zero).
        {
          repeat rewrite kron_mixed_product.
          rewrite Mmult_assoc.
          rewrite H3.
          Msimpl.
          reflexivity.
        }
        rewrite step1, step2 in H2; clear step1 step2.
        rewrite Mplus_0_r in H2.
        assert (step3 : ccu (diag2 u0 u1) × (∣1⟩ ⊗ ∣1⟩ ⊗ beta) = ∣1⟩ ⊗ ∣1⟩ ⊗ (diag2 u0 u1 × beta)).
        {
          assert (WF_lhs : WF_Matrix (ccu (diag2 u0 u1) × (∣1⟩ ⊗ ∣1⟩ ⊗ beta))).
          {
            apply WF_mult.
            apply WF_ccu.
            apply WF_diag2.
            solve_WF_matrix.
          }
          assert (WF_rhs : WF_Matrix (∣1⟩ ⊗ ∣1⟩ ⊗ (diag2 u0 u1 × beta))).
          {
            repeat apply WF_kron.
            all: try lia.
            exact WF_qubit1.
            exact WF_qubit1.
            apply WF_mult.
            apply WF_diag2.
            assumption.
          }
          unfold ccu, control, diag2, Mmult.
          lma'.
        }
        rewrite step3 in H2 at 1; clear step3.
        apply kron_cancel_l in H2; auto.
        2: {
          apply WF_mult.
          apply WF_diag2.
          exact WF_beta.
        }
        2: {
          apply nonzero_kron.
          exact WF_qubit1.
          exact WF_qubit1.
          exact nonzero_qubit1.
          exact nonzero_qubit1.
        }
        assert (u0_is_1 : u0 = C1).
        {
          apply (f_equal (fun f => f 0%nat 0%nat)) in H2.
          unfold diag2, Mmult in H2; simpl in H2.
          revert H2; Csimpl; intro H2.
          apply Cmult_cancel_r with (a := beta 0%nat 0%nat).
          exact a_nonzero.
          rewrite <- H2.
          rewrite Cmult_1_l.
          reflexivity.
        }
        assert (u1_is_1 : u1 = C1).
        {
          apply (f_equal (fun f => f 1%nat 0%nat)) in H2.
          unfold diag2, Mmult in H2; simpl in H2.
          revert H2; Csimpl; intro H2.
          apply Cmult_cancel_r with (a := beta 1%nat 0%nat).
          exact b_nonzero.
          rewrite <- H2.
          rewrite Cmult_1_l.
          reflexivity.
        }
        split.
        ** exact u0_is_1.
        ** exact u1_is_1.
  - intros.
    exists (I 2), (I 2).
    destruct H2 as [u0_is_1 u1_is_1].
    rewrite u0_is_1, u1_is_1.
    exists C1, C1, C1, C1.
    exists ∣0⟩, ∣1⟩, ∣0⟩, ∣1⟩.
    split.
    {
      apply id_unitary.
    }
    split.
    {
      apply id_unitary.
    }
    split.
    {
      apply WF_qubit0.
    }
    split.
    {
      apply WF_qubit1.
    }
    split.
    {
      apply WF_qubit0.
    }
    split.
    {
      apply WF_qubit1.
    }
    split.
    {
      apply nonzero_qubit0.
    }
    split.
    {
      apply nonzero_qubit1.
    }
    split.
    {
      apply nonzero_qubit0.
    }
    split.
    {
      apply nonzero_qubit1.
    }
    split.
    {
      apply id2_eigenpairs.
    }
    split.
    {
      apply id2_eigenpairs.
    }
    split.
    {
      apply id2_eigenpairs.
    }
    split.
    {
      apply id2_eigenpairs.
    }
    {
      rewrite <- kron_plus_distr_l.
      unfold beta, beta_perp.
      rewrite a8; auto.
      lma'.
      apply WF_ccu.
      apply WF_diag2.
    }
Qed.
