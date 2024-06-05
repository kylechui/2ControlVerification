Require Import Coq.Logic.Classical_Prop.
Require Import QuantumLib.Complex.
Require Import QuantumLib.Quantum.
Require Import QuantumLib.Eigenvectors.
Require Import QuantumLib.Matrix.
Require Import QuantumLib.Permutations.
Require Import WFHelpers.
Require Import AlgebraHelpers.
Require Import MatrixHelpers.
Require Import DiagonalHelpers.
Require Import UnitaryHelpers.
Require Import GateHelpers.
Require Import SwapHelpers.
Require Import EigenvalueHelpers.
Require Import QubitHelpers.
Require Import Permutations.
Require Import A1_SquareMatrices.
Require Import A2_UnitaryMatrices.
Require Import A3_Swaps.
Require Import A5_ControlledUnitaries.
Require Import A6_TensorProducts.
Require Import A7_OtherProperties.

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
        Msimpl_light.
        repeat rewrite Mscale_kron_dist_r.
        repeat rewrite <- Mscale_kron_dist_l.
        repeat rewrite <- kron_plus_distr_r.
        rewrite kron_assoc, id_kron; solve_WF_matrix.
        apply (kron_simplify 2 2 4 4).
        apply diag2_decomp.
        reflexivity.
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
          (V := (∣0⟩⟨0∣ ⊗ (u0 .* I 4) .+ ∣0⟩⟨1∣ ⊗ Zero .+ ∣1⟩⟨0∣ ⊗ Zero .+ ∣1⟩⟨1∣ ⊗ (u1 .* I 4))) at 1; solve_WF_matrix.
        repeat rewrite Mscale_mult_dist_r.
        Msimpl.
        all: reflexivity.
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
          (V := (∣0⟩⟨0∣ ⊗ V00 .+ ∣0⟩⟨1∣ ⊗ V01 .+ ∣1⟩⟨0∣ ⊗ V10 .+ ∣1⟩⟨1∣ ⊗ V11)) at 1; solve_WF_matrix.
          repeat rewrite Mscale_mult_dist_l.
          all: Msimpl_light; reflexivity.
      }
      rewrite UW, WU in H; clear UW WU W_eq_blocks.
      apply (@block_equalities
        4%nat
        (u0 .* V00)
        (u1 .* V01)
        (u0 .* V10)
        (u1 .* V11)
        (u0 .* V00)
        (u0 .* V01)
        (u1 .* V10)
        (u1 .* V11)
      ) in H; solve_WF_matrix.
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
        (V00† × V00)
        Zero
        Zero
        (V11† × V11)
        (I 4)
        Zero
        Zero
        (I 4)
        ) in Unitary_U; solve_WF_matrix.
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
      repeat rewrite id_kron.
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
        rewrite diag2_decomp, kron_assoc, id_kron.
        repeat rewrite Mscale_kron_dist_r.
        repeat rewrite <- Mscale_kron_dist_l.
        repeat rewrite kron_plus_distr_r.
        Msimpl_light.
        all: solve_WF_matrix.
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
        apply diag2_unitary; auto.
        apply Cmod_1.
      }
      {
        split; try apply id_unitary.
        split; try apply id_unitary.
        Msimpl; try apply WF_diag4.
        rewrite u0_eq_u1.
        lma'.
        all: unfold kron, diag2, diag4, I; simpl; lca.
      }
    }
    {
      exists (diag2 C1 u0), (diag2 C1 u1), notc.
      split.
      {
        apply diag2_unitary; auto.
        apply Cmod_1.
      }
      split.
      {
        apply diag2_unitary; auto.
        apply Cmod_1.
      }
      split.
      {
        exact notc_unitary.
      }
      {
        lma'.
        solve_WF_matrix.
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
        exists (c d : C), ((I 2) ⊗ P) × control (diag2 u0 u1) = U × diag4 c d c d × U†)
    <-> u0 = u1 \/ u0 * u1 = C1.
Proof.
  intros u0 u1 unit_u0 unit_u1.
  split.
  {
    intro.
    destruct H as [P [Unitary_P [U [Unitary_U [c [d H]]]]]].
    set (PD := P × diag2 u0 u1).
    assert (Unitary_PD : WF_Unitary (P × diag2 u0 u1)).
    {
      apply Mmult_unitary; auto.
      apply diag2_unitary; auto.
    }
    assert (step2 : (I 2 ⊗ P) × control (diag2 u0 u1) = P .⊕ PD).
    {
      rewrite control_decomp, (direct_sum_decomp _ _ 0 0).
      rewrite Mmult_plus_distr_l.
      repeat rewrite kron_mixed_product; Msimpl_light.
      all: solve_WF_matrix.
    }
    pose proof (a3 P Unitary_P) as [VP [DP [Unitary_VP [Diagonal_DP P_decomp]]]].
    pose proof (a3 PD Unitary_PD) as [VPD [DPD [Unitary_VPD [Diagonal_DPD PD_decomp]]]].
    assert (step3 : exists σ : nat -> nat,
      permutation 4 σ /\ (forall i : nat, (DP .⊕ DPD) i i = diag4 c d c d (σ i) (σ i))).
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

    assert (case_A : forall (c d : C), (DP 0 0 = c -> DP 1 1 = c ->
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
          rewrite H0; lca.
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
          rewrite H1; lca.
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
          rewrite H2; lca.
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
          rewrite H3; lca.
        }
      }
      assert (c0_neq_C0 : c0 <> C0).
      {
        assert (det_P : Determinant P = c0 * c0).
        {
          assert (VP_u : WF_Unitary (VP†)).
          {
            apply adjoint_unitary; assumption.
          }
          rewrite P_decomp, DP_cI.
          replace (c0 .* I 2) with (diag2 c0 c0).
          repeat rewrite <- Determinant_multiplicative.
          rewrite Cmult_comm, Cmult_assoc.
          rewrite Determinant_multiplicative.
          destruct Unitary_VP as [_ Unitary_VP].
          rewrite Unitary_VP, Det_I, Cmult_1_l.
          apply Det_diag2.
          lma'.
          all: unfold diag2, I, scale; simpl; lca.
        }
        pose proof (unit_det_neq_0 P Unitary_P).
        rewrite det_P in H4; clear det_P.
        intro.
        contradict H4.
        rewrite H5; lca.
      }
      rewrite DP_cI in P_decomp; clear DP_cI.
      rewrite DPD_dI in PD_decomp; clear DPD_dI.
      clear H1 H2.
      assert (diag2_decomp : forall (x : C), diag2 x x = x .* I 2).
      {
        intros.
        lma'.
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
      apply (Cmult_cancel_l c0); try apply H0; auto.
      rewrite cu0_d, cu1_d; reflexivity.
    }
    assert (case_B : forall (c d : C),
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
          unfold diag2; simpl.
          rewrite H0; reflexivity.
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
          rewrite H1; reflexivity.
        }
      }
      assert (DPD_diag : DPD = diag2 c0 d0).
      {
        lma'.
        {
          apply Diagonal_DPD.
        }
        {
          unfold diag2; simpl.
          rewrite H2; reflexivity.
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
          rewrite H3; reflexivity.
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
      assert (c0d0_neq_C0 : c0 * d0 <> C0).
      {
        rewrite <- detP.
        apply unit_det_neq_0; auto.
      }
      unfold PD in detPD.
      rewrite a1 in detPD.
      rewrite detP, Det_diag2 in detPD.
      apply (Cmult_cancel_l (c0 * d0)); auto.
      rewrite detPD; lca.
    }
    assert (case_C : forall (c d : C),
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
          unfold diag2; simpl.
          rewrite H0; reflexivity.
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
          rewrite H1; reflexivity.
        }
      }
      assert (DPD_diag : DPD = diag2 d0 c0).
      {
        lma'.
        {
          apply Diagonal_DPD.
        }
        {
          unfold diag2; simpl.
          rewrite H2; reflexivity.
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
          rewrite H3; reflexivity.
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
      assert (c0d0_neq_C0 : c0 * d0 <> C0).
      {
        rewrite <- detP.
        apply unit_det_neq_0; auto.
      }
      unfold PD in detPD.
      rewrite a1 in detPD.
      rewrite detP, Det_diag2 in detPD.
      apply (Cmult_cancel_l (c0 * d0)); auto.
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
      apply (case_C c d); auto.
    }
    {
      right.
      apply (case_B c d); auto.
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
      apply (case_B d c); auto.
    }
    {
      right.
      apply (case_C d c); auto.
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
  }
  {
    intro.
    destruct H as [u0_is_u1 | u0u1_is_1].
    {
      rewrite <- u0_is_u1.
      exists (I 2).
      split; try apply id_unitary.
      exists swap.
      split; try apply swap_unitary.
      exists C1, u0.
      rewrite id_kron; Msimpl_light.
      lma'; solve_WF_matrix.
      unfold control, diag2, diag4, swap, Mmult, adjoint; lca.
      unfold control, diag2, diag4, swap, Mmult, adjoint; lca.
    }
    {
      exists (diag2 C1 u0).
      split.
      {
        apply diag2_unitary; auto.
        apply Cmod_1.
      }
      {
        exists cnot.
        split.
        {
          apply cnot_unitary.
        }
        {
          exists C1, u0.
          assert (H : I 2 ⊗ diag2 C1 u0 × control (diag2 u0 u1) = diag4 C1 u0 u0 (u0 * u1)).
          {
            lma'; solve_WF_matrix.
            all: unfold diag4, diag2, kron, Mmult; simpl; Csimpl; reflexivity.
          }
          rewrite H; clear H.
          rewrite u0u1_is_1; clear u0u1_is_1.
          lma'.
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
  - intros [U [V [P0 [P1 [Q0 [Q1 [Unitary_U [Unitary_V [Unitary_P0 [Unitary_P1 [Unitary_Q0 [Unitary_Q1 H1]]]]]]]]]]]].
    rewrite <- (direct_sum_decomp _ _ 0 0) in H1; solve_WF_matrix.
    unfold ccu in H1.
    rewrite control_direct_sum in H1.
    assert (H2 : (U × (P0 ⊗ Q0) × V) = I 4 /\ (U × (P1 ⊗ Q1) × V) = control (diag2 u0 u1)).
    {
      apply direct_sum_simplify; solve_WF_matrix.
    }
    destruct H2.
    assert (H4 : control (diag2 u0 u1) = diag4 1 1 u0 u1).
    {
      lma'.
      all: unfold control, diag2, diag4; lca.
    }
    rewrite H4 in H3; clear H4.
    assert (H4 : diag4 1 1 u0 u1 = U × ((P1 × P0†) ⊗ (Q1 × Q0†)) × U†).
    {
      rewrite <- Mmult_1_r at 1; solve_WF_matrix.
      rewrite <- id_adjoint_eq.
      rewrite <- H2, <- H3; clear H2 H3.
      distribute_adjoint.
      pose proof (other_unitary_decomp V Unitary_V).
      rewrite Mmult_assoc.
      rewrite <- Mmult_assoc with (A := V), H2 at 1.
      Msimpl_light; solve_WF_matrix.
      rewrite kron_adjoint, <- kron_mixed_product.
      repeat rewrite Mmult_assoc; reflexivity.
    }
    apply m3_2; auto.
    exists (P1 × P0†), (Q1 × Q0†), (U†).
    split; solve_WF_matrix.
    split; solve_WF_matrix.
    split; solve_WF_matrix.
    rewrite adjoint_involutive.
    apply (f_equal (fun f => U† × f × U)) in H4.
    rewrite H4.
    destruct Unitary_U as [WF_U Unitary_U].
    repeat rewrite Mmult_assoc.
    rewrite Unitary_U at 1.
    repeat rewrite <- Mmult_assoc.
    rewrite Unitary_U at 1.
    Msimpl_light; solve_WF_matrix.
  - intros.
    destruct H1 as [u0_eq_u1 | u0u1_eq_1].
    + rewrite u0_eq_u1; clear u0_eq_u1.
      exists (I 4), (I 4), (I 2), (diag2 1 u1), (I 2), (I 2).
      split. apply id_unitary.
      split. apply id_unitary.
      split. apply id_unitary.
      split. apply diag2_unitary; auto; apply Cmod_1.
      split. apply id_unitary.
      split. apply id_unitary.
      rewrite id_kron.
      Msimpl_light.
      unfold ccu.
      rewrite <- (direct_sum_decomp _ _ 0 0); solve_WF_matrix.
      rewrite control_direct_sum.
      rewrite direct_sum_simplify; solve_WF_matrix.
      split. reflexivity.
      lma'; solve_WF_matrix.
      all: unfold diag2, control, kron; simpl; Csimpl; reflexivity.
    + exists notc, notc, (I 2), (diag2 1 u0), (I 2), (diag2 1 u1).
      split. apply notc_unitary.
      split. apply notc_unitary.
      split. apply id_unitary.
      split. apply diag2_unitary; auto; apply Cmod_1.
      split. apply id_unitary.
      split. apply diag2_unitary; auto; apply Cmod_1.
      rewrite id_kron, Mmult_1_r.
      rewrite notc_notc at 1.
      unfold ccu.
      rewrite <- (direct_sum_decomp _ _ 0 0).
      rewrite control_direct_sum.
      rewrite direct_sum_simplify.
      split. reflexivity.
      (* PERF: Can probably be sped up by omitting lma' *)
      lma'.
      all: solve_WF_matrix.
      all: unfold notc, Mmult, diag2, control, kron; simpl; Csimpl; auto.
Qed.

Lemma m4_2 : forall (u0 u1 : C),
  Cmod u0 = 1 -> Cmod u1 = 1 ->
  forall (Q : Square 2),
    WF_Unitary Q ->
    let beta : Vector 2 := Q × ∣0⟩ in
    let beta_perp := Q × ∣1⟩ in
    (exists (P0 P1 : Square 2), WF_Unitary P0 /\ WF_Unitary P1 /\
      I 2 ⊗ I 2 ⊗ (beta × beta†) .+ P0 ⊗ P1 ⊗ (beta_perp × beta_perp†) = ccu (diag2 u0 u1))
    <-> u0 = 1 /\ u1 = 1.
Proof.
  intros.
  pose (a := beta 0%nat 0%nat).
  pose (b := beta 1%nat 0%nat).
  split.
  - intros.
    destruct H2 as [P0 [P1 [Unitary_P0 [Unitary_P1 H2]]]].
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
        lma'.
        solve_WF_matrix.
        all: unfold beta, adjoint, qubit0, qubit1, Mmult; simpl.
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
          lma'.
          solve_WF_matrix.
          all: unfold beta, adjoint, qubit0, qubit1, Mmult; simpl.
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
          all: solve_WF_matrix.
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
          unfold ccu.
          do 2 rewrite control_decomp.
          rewrite Mmult_plus_distr_r.
          repeat rewrite kron_assoc.
          repeat rewrite (@kron_mixed_product 2 2 1 4 4 1).
          rewrite Mmult_plus_distr_r.
          repeat rewrite (@kron_mixed_product 2 2 1 2 2 1).
          replace (∣0⟩⟨0∣ × ∣1⟩) with (@Zero 2 1) by lma'.
          replace (∣1⟩⟨1∣ × ∣1⟩) with ∣1⟩ by lma'.
          Msimpl_light.
          all: solve_WF_matrix.
        }
        rewrite step3 in H2 at 1; clear step3.
        apply kron_cancel_l in H2; auto.
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
        ** solve_WF_matrix.
        ** solve_WF_matrix.
        ** apply nonzero_kron; solve_WF_matrix; apply nonzero_qubit1.
  - intros.
    exists (I 2), (I 2).
    destruct H2 as [u0_is_1 u1_is_1].
    rewrite u0_is_1, u1_is_1.
    split.
    {
      apply id_unitary.
    }
    split.
    {
      apply id_unitary.
    }
    {
      rewrite <- kron_plus_distr_l.
      unfold beta, beta_perp.
      rewrite a8; auto.
      assert (forall {n}, I 2 ⊗ I n = I n .⊕ I n).
      {
        intro n.
        rewrite <- Mplus01, kron_plus_distr_r, <- (direct_sum_decomp _ _ 0 0).
        all: solve_WF_matrix.
      }
      unfold ccu.
      rewrite kron_assoc.
      rewrite id_kron.
      rewrite H2, control_direct_sum.
      rewrite direct_sum_simplify.
      split. reflexivity.
      rewrite <- id_kron.
      rewrite H2, control_direct_sum.
      rewrite direct_sum_simplify.
      split. reflexivity.
      lma'.
      all: solve_WF_matrix.
    }
Qed.

Lemma m4_3 : forall (u0 u1 : C), Cmod u0 = 1 -> Cmod u1 = 1 ->
  (exists (V1 V2 V3 V4 : Square 4),
    WF_Unitary V1 /\ WF_Unitary V2 /\ WF_Unitary V3 /\ WF_Unitary V4 /\
    exists (P0 P1 : Square 2),
      WF_Unitary P0 /\ WF_Unitary P1 /\ V1 = ∣0⟩⟨0∣ ⊗ P0 .+ ∣1⟩⟨1∣ ⊗ P1 /\
      (acgate V1 × bcgate V2 × acgate V3 × bcgate V4 = ccu (diag2 u0 u1)))
  <-> u0 = u1 \/ u0 * u1 = C1.
Proof.
  intros u0 u1 unit_u0 unit_u1.
  split.
  {
    intro.
    destruct H as [V1 [V2 [V3 [V4 H]]]].
    destruct H as [Unitary_V1 [Unitary_V2 [Unitary_V3 [Unitary_V4 H]]]].
    destruct H as [P0 [P1 [Unitary_P0 [Unitary_P1 H]]]].
    destruct H as [H H0].
    assert (Unitary_diag : WF_Unitary (control (diag2 u0 u1))) by solve_WF_matrix.
    assert (ccdiag_decomp : ccu (diag2 u0 u1) = ∣0⟩⟨0∣ ⊗ (I 4) .+ ∣1⟩⟨1∣ ⊗ (control (diag2 u0 u1))).
    {
      unfold ccu.
      rewrite control_decomp; solve_WF_matrix.
    }
    rewrite ccdiag_decomp in H0.
    pose proof (
      a27
      V1 V2 V3 V4
      (I 4) (control (diag2 u0 u1))
      P0 P1
      Unitary_V1 Unitary_V2 Unitary_V3 Unitary_V4
      (id_unitary 4) Unitary_diag
      Unitary_P0 Unitary_P1
      H0 H
    ) as [Q0 [Q1 [Unitary_Q0 [Unitary_Q1 H2]]]].
    assert (H3 : acgate V1 × bcgate V2 × acgate V3 = ∣0⟩⟨0∣ ⊗ (((I 2) ⊗ P0) × V2 × ((I 2) ⊗ Q0)) .+ ∣1⟩⟨1∣ ⊗ (((I 2) ⊗ P1) × V2 × ((I 2) ⊗ Q1))).
    {
      unfold acgate, bcgate, abgate, swapbc.
      rewrite H, H2; clear H H2.
      repeat rewrite kron_plus_distr_r.
      repeat rewrite Mmult_plus_distr_l.
      repeat rewrite Mmult_plus_distr_r.
      repeat rewrite kron_assoc with (A := ∣0⟩⟨0∣); solve_WF_matrix.
      repeat rewrite kron_assoc with (A := ∣1⟩⟨1∣); solve_WF_matrix.
      repeat rewrite (@kron_mixed_product 2 2 2 4 4 4).
      Msimpl_light.
      repeat rewrite swap_2gate; solve_WF_matrix.
      repeat rewrite Mmult_plus_distr_l.
      repeat rewrite (@kron_mixed_product 2 2 2 4 4 4).
      rewrite cancel00, cancel01, cancel10, cancel11; solve_WF_matrix.
      Msimpl_light.
      reflexivity.
    }
    apply (f_equal (fun f => f × (bcgate V4)†)) in H0.
    rewrite Mmult_assoc in H0.
    pose proof (other_unitary_decomp (bcgate V4) (bcgate_unitary V4 Unitary_V4)).
    rewrite H1 in H0 at 1; clear H1.
    revert H0.
    Msimpl_light; solve_WF_matrix.
    rewrite Mmult_plus_distr_r.
    unfold bcgate at 2 3.
    rewrite kron_adjoint.
    rewrite id_adjoint_eq.
    repeat rewrite kron_mixed_product.
    Msimpl_light; solve_WF_matrix.
    rewrite H3; clear H3.
    intro H0.
    assert (H1 : (I 2 ⊗ P0) × V2 × (I 2 ⊗ Q0) = V4† /\ (I 2 ⊗ P1) × V2 × (I 2 ⊗ Q1) = control (diag2 u0 u1) × V4†).
    {
      apply direct_sum_simplify; solve_WF_matrix.
      repeat rewrite (direct_sum_decomp _ _ 0 0); solve_WF_matrix.
    }
    destruct H1 as [H1 H3].
    rewrite <- H1 in H3; clear H1.
    apply (f_equal (fun f => f × (I 2 ⊗ P0 × V2 × (I 2 ⊗ Q0))†)) in H3.
    assert (H4 : WF_Unitary (I 2 ⊗ P0 × V2 × (I 2 ⊗ Q0))†).
    {
      solve_WF_matrix.
    }
    destruct H4 as [_ H4].
    rewrite adjoint_involutive in H4.
    rewrite Mmult_assoc with (A := control (diag2 u0 u1)) in H3.
    rewrite H4 in H3; clear H4.
    rewrite Mmult_1_r in H3; solve_WF_matrix.

    apply (f_equal (fun f => (I 2 ⊗ (P0 × P1†)) × f)) in H3.
    repeat rewrite Mmult_adjoint in H3.
    repeat rewrite (@kron_adjoint 2 2 2 2) in H3.
    rewrite id_adjoint_eq in H3.
    repeat rewrite <- Mmult_assoc in H3.
    rewrite kron_mixed_product in H3.
    rewrite Mmult_assoc with (A := P0) in H3.
    pose proof (Unitary_P1) as [_ P1_adjoint].
    rewrite P1_adjoint in H3; clear P1_adjoint.
    repeat rewrite Mmult_assoc in H3.
    rewrite <- Mmult_assoc with (A := I 2 ⊗ Q1) in H3.
    rewrite (kron_mixed_product (I 2) Q1 (I 2) (Q0 †)) in H3 at 1.
    revert H3.
    Msimpl_light; solve_WF_matrix.
    rewrite <- id_adjoint_eq at 3.
    rewrite <- kron_adjoint, <- Mmult_adjoint.
    repeat rewrite <- Mmult_assoc.
    set (W := I 2 ⊗ P0 × V2).
    assert (H3 : WF_Unitary (Q1 × Q0†)) by solve_WF_matrix.
    pose proof (a3 (Q1 × Q0†) H3).
    destruct H1 as [V [D [Unitary_V [Diagonal_D Q1Q0_decomp]]]].
    apply (f_equal (fun f => I 2 ⊗ f)) in Q1Q0_decomp.
    do 2 rewrite <- Mmult_1_l with (A := I 2) in Q1Q0_decomp at 2; solve_WF_matrix.
    repeat rewrite <- kron_mixed_product in Q1Q0_decomp.
    rewrite Q1Q0_decomp; clear Q1Q0_decomp.
    rewrite <- id_adjoint_eq at 3.
    rewrite <- kron_adjoint.
    do 2 rewrite Mmult_assoc.
    rewrite <- Mmult_adjoint.
    repeat rewrite <- Mmult_assoc.
    intro H4.

    apply m3_3; auto.
    assert (I_D : (I 2 ⊗ D = diag4 (D 0 0) (D 1 1) (D 0 0) (D 1 1))%nat).
    {
      destruct Diagonal_D as [WF_D Diagonal_D].
      lma'.
      all: unfold kron, I, diag4; simpl; Csimpl.
      reflexivity.
      apply (Diagonal_D 0 1)%nat; auto.
      apply (Diagonal_D 1 0)%nat; auto.
      reflexivity.
      reflexivity.
      apply (Diagonal_D 0 1)%nat; auto.
      apply (Diagonal_D 1 0)%nat; auto.
      reflexivity.
    }
    rewrite I_D in H4; clear I_D.
    exists (P0 × P1†).
    split; solve_WF_matrix.
    exists (W × (I 2 ⊗ V)).
    split; solve_WF_matrix.
    exists (D 0 0)%nat, (D 1 1)%nat.
    rewrite <- H4.
    reflexivity.
  }
  {
    intros.
    destruct H as [u0_eq_u1 | u0u1_eq_1].
    {
      pose proof Cmod_1.
      rewrite u0_eq_u1; clear u0_eq_u1.
      exists (I 4), swap, (control (diag2 C1 u1)), swap.
      split. apply id_unitary.
      split. apply swap_unitary.
      split. solve_WF_matrix.
      split. apply swap_unitary.
      exists (I 2), (I 2).
      split. apply id_unitary.
      split. apply id_unitary.
      split. rewrite <- kron_plus_distr_r, Mplus01, id_kron; reflexivity.
      unfold acgate, abgate, bcgate, swapbc.
      repeat rewrite <- Mmult_assoc.
      rewrite id_kron; Msimpl_light.
      repeat rewrite kron_mixed_product.
      rewrite swap_swap.
      rewrite Mmult_assoc with (B := swap).
      rewrite Mmult_assoc.
      rewrite (kron_mixed_product (I 2) swap).
      repeat rewrite swap_swap.
      Msimpl_light.
      rewrite id_kron; Msimpl_light.
      unfold ccu.
      do 2 rewrite control_direct_sum.
      rewrite kron_direct_sum_distr_r with (A := I 2) at 1; solve_WF_matrix.
      rewrite direct_sum_simplify; solve_WF_matrix.
      split. rewrite id_kron; reflexivity.
      lma'; solve_WF_matrix.
      all: unfold kron, diag2, I, control; simpl; lca.
    }
    {
      pose proof (Cexp_Cmod u1 unit_u1) as [θ u1_Cexp].
      assert (u0_Cexp : Cexp (-θ) = u0).
      {
        rewrite <- Cexp_0 in u0u1_eq_1.
        replace 0%R with (θ + (-θ))%R in u0u1_eq_1 by lra.
        rewrite Cexp_add in u0u1_eq_1.
        rewrite u1_Cexp in u0u1_eq_1.
        symmetry.
        rewrite Cmult_comm in u0u1_eq_1.
        apply Cmult_cancel_l with (a := u1); auto.
        rewrite <- u1_Cexp.
        apply Cexp_nonzero.
      }
      set (u := Cexp (θ / 2)).
      set (P := diag2 (/ u) u).
      set (U := ∣0⟩⟨0∣ ⊗ σx .+ ∣1⟩⟨1∣ ⊗ I 2).
      set (V := control P).
      assert (unit_u : Cmod u = 1).
      {
        apply Cmod_Cexp.
      }
      assert (Unitary_P : WF_Unitary P).
      {
        solve_WF_matrix.
        apply diag2_unitary; auto.
        rewrite Cmod_inv, unit_u.
        lra.
        rewrite Cmod_gt_0, unit_u; lra.
      }
      assert (Unitary_U : WF_Unitary U).
      {
        solve_WF_matrix.
        rewrite <- (direct_sum_decomp _ _ 0 0); solve_WF_matrix.
        apply direct_sum_unitary.
        apply σx_unitary.
        apply id_unitary.
      }
      assert (Unitary_V : WF_Unitary V).
      {
        solve_WF_matrix.
      }
      exists V, U, V, (U†).
      split; auto.
      split; auto.
      split; auto.
      split; solve_WF_matrix.
      exists (I 2), P.
      split; solve_WF_matrix.
      split; auto.
      split.
      {
        unfold V.
        rewrite control_decomp; solve_WF_matrix.
      }
      {
        assert (step1 : P = (/ u) .* ∣0⟩⟨0∣ .+ u .* ∣1⟩⟨1∣).
        {
          lma'; solve_WF_matrix.
        }
        assert (step2 : P × P = diag2 u0 u1).
        {
          rewrite step1.
          repeat rewrite Mmult_plus_distr_l.
          repeat rewrite Mmult_plus_distr_r.
          repeat rewrite Mscale_mult_dist_l.
          repeat rewrite Mscale_mult_dist_r.
          rewrite cancel00, cancel01, cancel10, cancel11; solve_WF_matrix.
          Msimpl_light.
          repeat rewrite Mscale_assoc.
          unfold u.
          rewrite <- Cexp_neg.
          repeat rewrite <- Cexp_add.
          replace (θ / 2 + θ / 2)%R with θ by lra.
          replace (- (θ / 2) + - (θ / 2))%R with (-θ)%R by lra.
          rewrite u0_Cexp, u1_Cexp.
          lma'.
          all: unfold scale, Mmult, Mplus, adjoint, diag2; simpl; lca.
        }
        clear step1.
        assert (step3 : acgate V = ∣0⟩⟨0∣ ⊗ I 4 .+ ∣1⟩⟨1∣ ⊗ I 2 ⊗ P).
        {
          unfold acgate, abgate, swapbc, V.
          rewrite control_decomp; solve_WF_matrix.
          rewrite kron_plus_distr_r.
          rewrite kron_assoc; solve_WF_matrix.
          rewrite kron_assoc; solve_WF_matrix.
          rewrite Mmult_plus_distr_l.
          rewrite Mmult_plus_distr_r.
          repeat rewrite (@kron_mixed_product 2 2 2 4 4 4).
          rewrite id_kron.
          Msimpl_light.
          rewrite swap_swap, a11; solve_WF_matrix.
          rewrite <- kron_assoc; solve_WF_matrix.
        }
        assert (step4 : P × σx × P × σx = I 2).
        {
          lma'; solve_WF_matrix.
          all: unfold P, σx, Mmult, I, diag2; simpl; Csimpl.
          {
            rewrite Cinv_l; auto.
            unfold u.
            apply Cexp_nonzero.
          }
          {
            rewrite Cinv_r; auto.
            unfold u.
            apply Cexp_nonzero.
          }
        }
        assert (step5 : (I 2 ⊗ P) × U × (I 2 ⊗ P) × U† = control (P × P)).
        {
          unfold U.
          rewrite Mplus_adjoint.
          repeat rewrite kron_adjoint.
          rewrite id_adjoint_eq, adjoint00, adjoint11.
          repeat rewrite Mmult_plus_distr_l.
          repeat rewrite kron_mixed_product.
          Msimpl_light.
          rewrite <- Mmult_plus_distr_l.
          repeat rewrite Mmult_plus_distr_r.
          repeat rewrite kron_mixed_product.
          replace (σx†) with σx by lma'.
          repeat rewrite Mmult_plus_distr_l.
          repeat rewrite kron_mixed_product.
          Msimpl_light.
          rewrite cancel00, cancel01, cancel10, cancel11.
          Msimpl_light.
          rewrite step4.
          rewrite control_decomp.
          reflexivity.
          all: solve_WF_matrix.
        }
        rewrite step2 in step5.
        unfold ccu.
        rewrite <- step5; clear step5.
        rewrite step3; clear step3.
        unfold bcgate.
        unfold U.
        repeat rewrite Mplus_adjoint.
        repeat rewrite kron_adjoint.
        rewrite adjoint00, adjoint11, id_adjoint_eq.
        rewrite kron_plus_distr_l.
        replace (σx†) with σx by lma'.
        repeat rewrite Mmult_plus_distr_l.
        repeat rewrite Mmult_plus_distr_r.
        repeat rewrite kron_mixed_product.
        (* PERF: These Msimpl_lights are non-trivially expensive, can optimize later*)
        repeat rewrite Mmult_1_r.
        repeat rewrite <- kron_assoc.
        repeat rewrite (@kron_mixed_product 4 4 4 2 2 2).
        repeat rewrite Mmult_1_l.
        repeat rewrite Mmult_plus_distr_l.
        repeat rewrite (@kron_mixed_product 2 2 2 2 2 2).
        repeat rewrite cancel00.
        repeat rewrite cancel01.
        repeat rewrite cancel10.
        repeat rewrite cancel11.
        Msimpl_light.
        repeat rewrite kron_plus_distr_l.
        repeat rewrite kron_assoc.
        repeat rewrite (@kron_mixed_product 2 2 2 4 4 4).
        repeat rewrite cancel01.
        repeat rewrite cancel10.
        Msimpl_light.
        repeat rewrite Mmult_plus_distr_l.
        repeat rewrite cancel11.
        repeat rewrite <- kron_plus_distr_l.
        replace (σx × σx) with (I 2) by lma'.
        repeat rewrite <- kron_plus_distr_r.
        rewrite Mplus01, id_kron.
        repeat rewrite <- kron_assoc.
        repeat rewrite (@kron_mixed_product 4 4 4 2 2 2).
        repeat rewrite (@kron_mixed_product 2 2 2 2 2 2).
        repeat rewrite cancel00.
        repeat rewrite cancel01.
        repeat rewrite cancel10.
        repeat rewrite cancel11.
        Msimpl_light.
        rewrite step2, step4.
        repeat rewrite kron_assoc.
        rewrite <- (kron_plus_distr_l 2 2 4 4).
        rewrite <- (@direct_sum_decomp _ _ 0 0).
        rewrite control_direct_sum.
        reflexivity.
        all: solve_WF_matrix.
      }
    }
  }
Qed.

Lemma m4_4 : forall (u0 u1 : C), Cmod u0 = 1 -> Cmod u1 = 1 ->
  (exists (V1 V2 V3 V4 : Square 4),
    WF_Unitary V1 /\ WF_Unitary V2 /\ WF_Unitary V3 /\ WF_Unitary V4 /\
    exists (P0 P1 : Square 2),
      WF_Unitary P0 /\ WF_Unitary P1 /\ V4 = ∣0⟩⟨0∣ ⊗ P0 .+ ∣1⟩⟨1∣ ⊗ P1 /\
      (acgate V1 × bcgate V2 × acgate V3 × bcgate V4 = ccu (diag2 u0 u1)))
  <-> u0 = u1 \/ u0 * u1 = C1.
Proof.
  intros u0 u1 unit_u0 unit_u1.
  assert (conj : u0^* = u1^* \/ u0^* * u1^* = C1 <-> u0 = u1 \/ u0 * u1 = C1).
  {
    split.
    {
      intro.
      destruct H.
      {
        left.
        apply (f_equal (fun f => f^*)) in H.
        repeat rewrite Cconj_involutive in H.
        exact H.
      }
      {
        right.
        rewrite <- Cconj_mult_distr in H.
        apply (f_equal (fun f => f^*)) in H.
        rewrite Cconj_involutive in H.
        rewrite H; lca.
      }
    }
    {
      intro.
      destruct H.
      {
        left.
        rewrite H; lca.
      }
      {
        right.
        rewrite <- Cconj_mult_distr.
        rewrite H; lca.
      }
    }
  }
  assert (diag2_adjoint : diag2 (u0 ^*) (u1 ^*) = (diag2 u0 u1)†).
  {
    lma'.
    all: unfold diag2, adjoint; simpl; reflexivity.
  }
  split.
  {
    intro.
    destruct H as [V1 [V2 [V3 [V4 H]]]].
    destruct H as [Unitary_V1 [Unitary_V2 [Unitary_V3 [Unitary_V4 H]]]].
    destruct H as [P0 [P1 [Unitary_P0 [Unitary_P1 H]]]].
    destruct H as [H H0].
    rewrite <- conj; clear conj.
    rewrite <- m4_3.
    exists V4†, V3†, V2†, V1†.
    split; solve_WF_matrix.
    split; solve_WF_matrix.
    split; solve_WF_matrix.
    split; solve_WF_matrix.
    exists P0†, P1†.
    split; solve_WF_matrix.
    split; solve_WF_matrix.
    split.
    {
      rewrite H.
      rewrite Mplus_adjoint.
      repeat rewrite kron_adjoint.
      rewrite adjoint00, adjoint11.
      reflexivity.
    }
    {
      rewrite diag2_adjoint; clear diag2_adjoint.
      rewrite <- a13_1.
      unfold ccu. unfold ccu in H0.
      repeat rewrite <- control_adjoint.
      rewrite <- H0; clear H0.
      rewrite <- a12 with (U := V2).
      rewrite <- a12 with (U := V4).
      repeat rewrite Mmult_adjoint.
      repeat rewrite <- Mmult_assoc.
      restore_dims.
      repeat rewrite swapab_hermitian.
      rewrite swapab_inverse.
      rewrite Mmult_1_l.
      repeat rewrite Mmult_assoc.
      rewrite <- Mmult_assoc with (A := swapab).
      rewrite <- Mmult_assoc with (B := swapab).
      rewrite <- Mmult_assoc with (A := swapab).
      repeat rewrite acgate_adjoint.
      repeat rewrite a12.
      all: solve_WF_matrix.
    }
    {
      rewrite Cmod_Cconj; auto.
    }
    {
      rewrite Cmod_Cconj; auto.
    }
  }
  {
    intro.
    rewrite <- conj in H; clear conj.
    rewrite <- Cmod_Cconj in unit_u0, unit_u1.
    pose proof (
      m4_3
      (u0^*) (u1^*)
      unit_u0 unit_u1
    ).
    rewrite <- H0 in H; clear H0.
    destruct H as [V1 [V2 [V3 [V4 [Unitary_V1 [Unitary_V2 [Unitary_V3 [Unitary_V4 H]]]]]]]].
    destruct H as [P0 [P1 [Unitary_P0 [Unitary_P1 [H H0]]]]].
    exists V4†, V3†, V2†, V1†.
    split; solve_WF_matrix.
    split; solve_WF_matrix.
    split; solve_WF_matrix.
    split; solve_WF_matrix.
    exists P0†, P1†.
    split; solve_WF_matrix.
    split; solve_WF_matrix.
    split.
    {
      rewrite H.
      rewrite Mplus_adjoint.
      repeat rewrite kron_adjoint.
      rewrite adjoint00, adjoint11.
      reflexivity.
    }
    {
      (* TODO: A bit repetitive here; we can probably pull this out to an assertion*)
      rewrite diag2_adjoint in H0.
      unfold ccu in H0.
      repeat rewrite <- control_adjoint in H0.
      rewrite <- a13_1.
      unfold ccu.
      apply (f_equal (fun f => f†)) in H0.
      rewrite adjoint_involutive in H0.
      rewrite <- H0; clear H0.
      repeat rewrite Mmult_adjoint.
      repeat rewrite <- Mmult_assoc.
      rewrite <- a12 with (U := V2).
      rewrite <- a12 with (U := V4).
      repeat rewrite Mmult_adjoint.
      repeat rewrite <- Mmult_assoc.
      restore_dims.
      repeat rewrite swapab_hermitian.
      rewrite swapab_inverse.
      rewrite Mmult_1_l.
      repeat rewrite Mmult_assoc.
      rewrite <- Mmult_assoc with (A := swapab).
      rewrite <- Mmult_assoc with (B := swapab).
      rewrite <- Mmult_assoc with (A := swapab).
      repeat rewrite acgate_adjoint.
      repeat rewrite a12.
      all: solve_WF_matrix.
    }
  }
Qed.

Lemma m5_1 : forall (u0 u1 : C),
  Cmod u0 = 1 -> Cmod u1 = 1 ->
    (exists (U1 U2 U3 U4 : Square 4),
      WF_Unitary U1 /\ WF_Unitary U2 /\ WF_Unitary U3 /\ WF_Unitary U4 /\
      (bcgate U1 × acgate U2 × abgate U3 × bcgate U4) = ccu (diag2 u0 u1))
    <-> u0 = u1 \/ u0 * u1 = 1.

Proof.
  split.
  - intros [U1 [U2 [U3 [U4 [H_U1 [H_U2 [H_U3 [H_U4]]]]]]]].
    assert (adjoint_helper : acgate U2 × abgate U3 = (bcgate U1)† × ccu (diag2 u0 u1) × (bcgate U4)†).
    {
      rewrite <- H1.
      repeat rewrite <- Mmult_assoc.
      rewrite Mmult_assoc with (A := adjoint (bcgate U1) × bcgate U1 × acgate U2
× abgate U3) (B := bcgate U4) (C := adjoint (bcgate U4)).
      assert(bcgate U4 × adjoint (bcgate U4) = I 8).
      {
        unfold bcgate.
        Msimpl.
        rewrite other_unitary_decomp.
        rewrite id_kron.
        reflexivity.
        assumption.
      }
      rewrite H2 at 1.
      rewrite Mmult_1_r.
      repeat rewrite Mmult_assoc.
      rewrite <- Mmult_assoc with (C := acgate U2 × abgate U3).
      assert(adjoint (bcgate U1) × bcgate U1 = I 8).
      {
        unfold bcgate.
        Msimpl.
        destruct H_U1.
        rewrite H4.
        rewrite id_kron.
        reflexivity.
      }
      rewrite H3.
      rewrite Mmult_1_l.
      auto.
      solve_WF_matrix.
      solve_WF_matrix.
    }
    (* commutativity *)
    set (A := ((I 2) ⊗ U1)†).
    set (Q := (diag2 u0 u1) ⊗ (I 4)).
    assert (WF_U_commutativity_U1 : A × Q = Q × A).
    {
      subst A. subst Q.
      Msimpl.
      reflexivity.
      solve_WF_matrix.
      solve_WF_matrix.
    }
    set (B := ((I 2) ⊗ U4)†).
    assert (WF_U_commutativity_U4 : B × Q = Q × B).
    {
      subst B. subst Q.
      Msimpl.
      reflexivity.
      solve_WF_matrix.
      solve_WF_matrix.
    }
    set (C := ccu (diag2 u0 u1)).
    assert (diag2_diagonal : WF_Diagonal (diag2 u0 u1)).
      {
        unfold WF_Diagonal.
        split.
        solve_WF_matrix.
        intros i j H_neq.
        bdestruct (i =? j).
        {
          rewrite <- H2.
          unfold diag2.
          destruct i, j.
          all: try contradiction.
        }
        {
          unfold diag2.
          destruct i, j.
          contradiction.
          reflexivity.
          destruct i.
          all: try reflexivity.
          destruct i, j.
          contradiction.
          all: try reflexivity.
        }
      }
    assert (diag_commute_helper : C × Q = Q × C).
    {
      apply diag_commute.
      subst Q.
      apply diag_kron.
      assumption.
      apply diag_I.
      subst C.
      apply ccu_diag.
      assumption.
    }
    set (U2_ac := acgate U2).
    set (U3_ab := abgate U3).
    assert (H_Mmult_transitivity: (A × C × B) × Q = Q × (A × C × B)).
    {
      repeat rewrite Mmult_assoc.
      rewrite WF_U_commutativity_U4 at 1.
      rewrite <- Mmult_assoc with (A := C) (B := Q) (C := B).
      rewrite diag_commute_helper at 1.
      rewrite Mmult_assoc with (A := Q) (B := C) (C := B).
      repeat rewrite <- Mmult_assoc.
      rewrite WF_U_commutativity_U1.
      reflexivity.
    }
    assert (U2U3_commutativity_subst : (U2_ac × U3_ab) × Q = Q × (U2_ac × U3_ab)).
    {
      subst U2_ac U3_ab.
      rewrite adjoint_helper.
      subst A B Q C.
      unfold bcgate.
      assumption.
    }
    assert (WF_U2U3 : WF_Unitary (U2_ac × U3_ab)).
    {
      solve_WF_matrix.
    }
    subst Q.
    replace 4%nat with (2 * 2)%nat in U2U3_commutativity_subst by lia.
    rewrite <- (id_kron 2 2), <- kron_assoc in U2U3_commutativity_subst; solve_WF_matrix.
    assert (u0 = u1 \/ exists (V0 V1 : Square 4), WF_Unitary V0 /\ WF_Unitary V1 /\
      U2_ac × U3_ab = ∣0⟩⟨0∣ ⊗ V0 .+ ∣1⟩⟨1∣ ⊗ V1).
    {
      apply m3_1; assumption.
    }
    destruct H2 as [H2 | H3].
    left; assumption.
    destruct H3 as [V0 [V1 [Unitary_V0 [Unitary_V1 H3]]]].
    (* Use Lemma A.24 to actually get V0, V1 *)
    assert(exists (P0 Q0 P1 Q1 : Square 2),
WF_Unitary P0 /\ WF_Unitary Q0 /\ WF_Unitary P1 /\ WF_Unitary Q1 /\
U2_ac × U3_ab = ∣0⟩⟨0∣ ⊗ P0 ⊗ Q0 .+ ∣1⟩⟨1∣ ⊗ P1 ⊗ Q1).
    {
      apply a24 with (W00 := V0) (W11 := V1); assumption.
    }
    destruct H2 as [P0 [Q0 [P1 [Q1 [Unitary_P0 [Unitary_Q0 [Unitary_P1 [Unitary_Q1 H4]]]]]]]].
    set (U1_bc := bcgate U1).
    set (U4_bc := bcgate U4).
    assert (WF_Unitary U1_bc).
    {
      apply bcgate_unitary; assumption.
    }
    assert (WF_Unitary U4_bc).
    {
      apply bcgate_unitary; assumption.
    }
    assert (ccu(diag2 u0 u1) = ∣0⟩⟨0∣ ⊗ (U1 × (P0 ⊗ Q0) × U4) .+ ∣1⟩⟨1∣ ⊗ (U1 × (P1 ⊗ Q1) × U4)).
    {
      rewrite <- H1.
      unfold bcgate.
      repeat rewrite id_tens_equiv_block_diag.
      subst U2_ac U3_ab.
      repeat rewrite <- kron_plus_distr_r.
      rewrite Mplus01.
      repeat rewrite Mmult_assoc.
      rewrite <- Mmult_assoc with (A := acgate U2).
      rewrite <- Mmult_assoc with (B := acgate U2 × abgate U3).
      rewrite H4.
      repeat rewrite kron_assoc.
      repeat rewrite kron_plus_distr_l.
      repeat rewrite kron_plus_distr_r.
      repeat rewrite kron_mixed_product.
      rewrite <- Mmult_assoc.
      Msimpl_light.
      rewrite Mmult_plus_distr_l.
      rewrite Mmult_plus_distr_r.
      repeat rewrite kron_mixed_product.
      Msimpl_light.
      rewrite <- Mmult_assoc.
      reflexivity.
      all: repeat solve_WF_matrix.
    }
    (* apply lemma 4.1 to get the result *)
    assert (u0 = u1 \/ u0 * u1 = 1).
    {
      assert (∣0⟩⟨0∣ ⊗ (U1 × (P0 ⊗ Q0) × U4) .+ ∣1⟩⟨1∣ ⊗ (U1 × (P1 ⊗ Q1) × U4) = ccu(diag2 u0 u1)). auto.
      apply m4_1. all: try assumption.
      intros.
      exists U1, U4, P0, P1, Q0, Q1.
      split. assumption.
      split. assumption.
      split. assumption.
      split. assumption.
      split. assumption.
      split. assumption.
      rewrite H6. reflexivity.
    }
    assumption.
  - intros [H_eq | H_prod].
    + (* Case: u0 = u1 *)
      subst.
      exists (I 4), (I 4), (control (diag2 1 u1)) , (I 4).
      assert (control_diag2_unitary : WF_Unitary (control (diag2 C1 u1))).
      {
        apply control_unitary, diag2_unitary.
        exact Cmod_1.
        assumption.
      }
      split. apply id_unitary.
      split. apply id_unitary.
      split. apply control_diag2_unitary.
      split. apply id_unitary.
      assert (temp_bc : bcgate (I 4) = I 8).
      {
       unfold bcgate; simpl.
       apply id_kron.
      }
      rewrite temp_bc.
      Msimpl; solve_WF_matrix.
      assert (temp_ac : acgate (I 4) = I 8).
      {
       unfold acgate; simpl.
       unfold abgate; simpl.
       unfold swapbc; simpl.
       replace 4%nat with (2 * 2)%nat by lia.
       rewrite <- (id_kron 2 2).
       rewrite kron_assoc.
       repeat rewrite (@kron_mixed_product 2 2 2 4 4 4).
       rewrite id_kron; Msimpl_light.
       rewrite swap_swap.
       rewrite id_kron.
       reflexivity.
       all: apply WF_I.
      }
      rewrite temp_ac.
      Msimpl; solve_WF_matrix.
      unfold abgate; simpl.
      lma'; solve_WF_matrix.
      {
        unfold ccu, kron, diag2, kron, control, I; simpl.
        Csimpl.
        reflexivity.
      }
      {
        unfold kron, Mmult, ccu, control, diag2, I; simpl.
        Csimpl.
        reflexivity.
      }
    + (* Case: u0 * u1 = 1 *)
      exists notc, (∣0⟩⟨0∣ ⊗ I 2 .+ ∣1⟩⟨1∣ ⊗ (diag2 1 u1)), (∣0⟩⟨0∣ ⊗ I 2 .+ ∣1⟩⟨1∣ ⊗ (diag2 1 u0)), notc.
      split. apply notc_unitary.
      assert (WF_diag4_unitary_u1 : WF_Unitary (∣0⟩⟨0∣ ⊗ I 2 .+ ∣1⟩⟨1∣ ⊗ (diag2 1 u1))).
      {
        split.
        - solve_WF_matrix.
        - distribute_adjoint.
          repeat rewrite adjoint_involutive.
          rewrite id_adjoint_eq.
          rewrite Mmult_plus_distr_l.
          do 2 rewrite Mmult_plus_distr_r.
          repeat rewrite kron_mixed_product.
          rewrite cancel00, cancel01, cancel10, cancel11; solve_WF_matrix.
          Msimpl_light.
          pose proof (diag2_unitary 1 u1 Cmod_1 H0) as [_ H1].
          rewrite H1.
          rewrite <- kron_plus_distr_r, Mplus01, id_kron.
          reflexivity.
      }
      assert (WF_diag4_unitary_u0 : WF_Unitary (∣0⟩⟨0∣ ⊗ I 2 .+ ∣1⟩⟨1∣ ⊗ (diag2 1 u0))).
      {
        split.
        - solve_WF_matrix.
        - distribute_adjoint.
          repeat rewrite adjoint_involutive.
          rewrite id_adjoint_eq.
          rewrite Mmult_plus_distr_l.
          do 2 rewrite Mmult_plus_distr_r.
          repeat rewrite kron_mixed_product.
          rewrite cancel00, cancel01, cancel10, cancel11; solve_WF_matrix.
          Msimpl_light.
          pose proof (diag2_unitary 1 u0 Cmod_1 H) as [_ H1].
          rewrite H1.
          rewrite <- kron_plus_distr_r, Mplus01, id_kron.
          reflexivity.
      }
      split. apply WF_diag4_unitary_u1.
      split. apply WF_diag4_unitary_u0.
      split. apply notc_unitary.

      (* Define smaller pieces for better readability and easier manipulation *)
      set (X := ∣0⟩⟨0∣ ⊗ I 2 .+ ∣1⟩⟨1∣ ⊗ diag2 C1 u1 : Square 4).
      set (Y := ∣0⟩⟨0∣ ⊗ I 2 .+ ∣1⟩⟨1∣ ⊗ diag2 C1 u0 : Square 4).

      assert (ac_ab_simpl : acgate X × abgate Y = ∣0⟩⟨0∣ ⊗ I 4 .+ ∣1⟩⟨1∣ ⊗ diag2 C1 u0 ⊗ diag2 C1 u1).
      {
        subst X.
        subst Y.
        unfold acgate, abgate; simpl.
        unfold swapbc; simpl.
        repeat rewrite kron_plus_distr_r.
        repeat rewrite Mmult_plus_distr_l.
        repeat rewrite (@kron_assoc 2 2 2 2).
        repeat rewrite (@kron_mixed_product 2 2 2 4 4 4).
        repeat rewrite Mmult_1_l.
        repeat rewrite Mmult_assoc.
        repeat rewrite (@kron_mixed_product 2 2 2 4 4 4).
        Msimpl_light.
        repeat rewrite Mmult_plus_distr_r.
        repeat rewrite kron_mixed_product.
        repeat rewrite id_kron.
        rewrite cancel00, cancel01, cancel10, cancel11.
        Msimpl.
        rewrite swap_swap.
        repeat rewrite <- (@direct_sum_decomp _ _ 0 0).
        apply direct_sum_simplify; solve_WF_matrix.
        split.
        {
          reflexivity.
        }
        {
          rewrite <- Mmult_assoc.
          rewrite swap_2gate; solve_WF_matrix.
          rewrite kron_mixed_product.
          Msimpl_light; reflexivity.
        }
        all: solve_WF_matrix.
      }
      repeat rewrite Mmult_assoc.
      repeat rewrite <- Mmult_assoc with (C := bcgate notc).
      rewrite ac_ab_simpl at 1; clear ac_ab_simpl.
      rewrite kron_assoc.
      assert (diag_helper : diag2 C1 u0 ⊗ diag2 C1 u1 = diag4 C1 u1 u0 (u0 * u1)).
      {
        lma'.
        all: unfold diag2, diag4, kron; lca.
      }
      rewrite diag_helper; clear diag_helper.
      rewrite H_prod; clear H_prod.
      rewrite Mmult_plus_distr_l, Mmult_plus_distr_r.
      unfold bcgate.
      repeat rewrite (@kron_mixed_product 2 2 2 4 4 4).
      Msimpl_light.
      rewrite notc_notc.
      unfold ccu.
      rewrite control_direct_sum, <- (@direct_sum_decomp _ _ 0 0).
      rewrite direct_sum_simplify.
      split. reflexivity.
      lma'.
      all: solve_WF_matrix.
      all: unfold diag2, diag4, notc, Mmult, control; simpl; lca.
Qed.

Lemma m6_1 : forall (V : Square 4), WF_Unitary V ->
  (exists (x : Vector 2), WF_Qubit x /\ Entangled (V × (x ⊗ ∣0⟩))) \/
  (exists (ψ : Vector 2), WF_Qubit ψ /\
    forall (x : Vector 2), WF_Qubit x ->
    exists (z : Vector 2), WF_Qubit z /\ V × (x ⊗ ∣0⟩) = z ⊗ ψ) \/
  (exists (ψ : Vector 2), WF_Qubit ψ /\
    forall (x : Vector 2), WF_Qubit x ->
    exists (z : Vector 2), WF_Qubit z /\ V × (x ⊗ ∣0⟩) = ψ ⊗ z).
Proof.
  intros V Unitary_V.
  destruct (classic (exists (x : Vector 2), WF_Qubit x /\ Entangled (V × (x ⊗ ∣0⟩)))) as [case_A | case_B].
  {
    left.
    assumption.
  }
  {
    right.
    apply a23.
    assumption.
    intros x x_qubit.
    assert (~ (exists x : Vector 2, WF_Qubit x /\ Entangled (V × (x ⊗ ∣0⟩))) <-> (forall x : Vector 2, ~ (WF_Qubit x /\ Entangled (V × (x ⊗ ∣0⟩))))).
    {
      split.
      - intros H x0 Hx0.
        apply H.
        exists x0.
        assumption.
      - intros H [x0 Hx0].
        apply (H x0).
        assumption.
    }
    rewrite H in case_B; clear H.
    specialize (case_B x).
    apply not_and_or in case_B.
    destruct case_B.
    contradiction.
    unfold Entangled in H.
    apply NNPP in H.
    rewrite <- tensor_prod_of_qubit; auto.
    apply Mmult_qubit.
    assumption.
    apply (@kron_qubit 2 2).
    assumption.
    exact qubit0_qubit.
  }
Qed.

Lemma m6_2 : forall (u0 u1 : C), Cmod u0 = 1 -> Cmod u1 = 1 ->
  forall (U1 W2 V3 U4 : Square 4), WF_Unitary U1 -> WF_Unitary W2 -> WF_Unitary V3 -> WF_Unitary U4 ->
    ((acgate U1 × bcgate W2 × acgate V3 × bcgate U4) = ccu (diag2 u0 u1) /\
    V3 × (∣0⟩ ⊗ ∣0⟩) = ∣0⟩ ⊗ ∣0⟩ /\
    (forall (x : Vector 2), WF_Qubit x ->
      acgate U1 × (x ⊗ ∣0⟩ ⊗ ∣0⟩) = bcgate U4† × acgate V3† × (x ⊗ ∣0⟩ ⊗ ∣0⟩))) ->
  u0 = u1 \/ u0 * u1 = C1 \/ exists (W1 W3 W4 : Square 4), WF_Unitary W1 /\ WF_Unitary W3 /\ WF_Unitary W4 /\
  exists (P3 : Square 2), WF_Unitary P3 /\
    acgate U1 × bcgate W2 × acgate V3 × bcgate U4 = acgate W1 × bcgate W2 × acgate W3 × bcgate W4 /\
    W3 = I 2 ⊗ ∣0⟩⟨0∣ .+ P3 ⊗ ∣1⟩⟨1∣.
Proof.
  intros u0 u1 unit_u0 unit_u1 U1 W2 V3 U4 U1_unitary W2_unitary V3_unitary U4_unitary.
  intros [H [H0 H1]].
  assert (V3_d_unitary : WF_Unitary (V3†)) by solve_WF_matrix.
  pose proof (m6_1 V3† V3_d_unitary).
  destruct H2 as [case_A | [case_B | case_C]].
  {
    destruct case_A as [x [x_qubit entangled]].
    specialize (H1 x x_qubit).
    assert (swapab × acgate U1 × swapab × swapab × (x ⊗ ∣0⟩ ⊗ ∣0⟩) = swapab × bcgate U4† × swapab × (swapab × acgate V3† × swapab) × swapab × (x ⊗ ∣0⟩ ⊗ ∣0⟩)).
    {
      repeat rewrite Mmult_assoc.
      repeat rewrite <- Mmult_assoc with (A := swapab) (B := swapab).
      restore_dims.
      repeat rewrite swapab_inverse.
      repeat rewrite Mmult_1_l.
      rewrite H1 at 1; clear H1.
      repeat rewrite <- Mmult_assoc.
      all: solve_WF_matrix.
    }
    assert (bcgate U1 × (∣0⟩ ⊗ x ⊗ ∣0⟩) = acgate U4† × bcgate V3† × (∣0⟩ ⊗ x ⊗ ∣0⟩)).
    {
      do 2 rewrite a12 in H2.
      unfold swapab in H2.
      rewrite Mmult_assoc with (A := bcgate U1) in H2.
      rewrite (@kron_mixed_product 4 4 1 2 2 1) in H2.
      rewrite Mmult_1_l in H2.
      rewrite a10 in H2.
      rewrite H2 at 1; clear H2.
      fold swapab.
      rewrite <- a12 with (U := U4†).
      repeat rewrite <- Mmult_assoc.
      rewrite swapab_inverse.
      repeat rewrite Mmult_assoc.
      rewrite <- Mmult_assoc with (A := swapab).
      rewrite swapab_inverse at 1.
      unfold swapab.
      rewrite (@kron_mixed_product 4 4 1 2 2 1).
      rewrite a10.
      Msimpl_light.
      all: solve_WF_matrix.
    }
    assert (exists (Q0 Q1 : Square 2), U4† = ∣0⟩⟨0∣ ⊗ Q0 .+ ∣1⟩⟨1∣ ⊗ Q1 /\ WF_Unitary Q0 /\ WF_Unitary Q1).
    {
      assert (⟨ x ⊗ ∣0⟩, x ⊗ ∣0⟩ ⟩ = C1).
      {
        rewrite inner_product_kron.
        destruct x_qubit as [_ [_ x_unit]].
        rewrite x_unit.
        lca.
      }
      assert (U4_d_unitary : WF_Unitary (U4†)) by solve_WF_matrix.
      apply (a19 U4† (V3† × (x ⊗ ∣0⟩)) (U1 × (x ⊗ ∣0⟩))); solve_WF_matrix.
      {
        rewrite inner_product_adjoint_r, adjoint_involutive.
        rewrite <- Mmult_assoc.
        rewrite (other_unitary_decomp V3), Mmult_1_l.
        all: solve_WF_matrix.
      }
      {
        rewrite inner_product_adjoint_r.
        rewrite <- Mmult_assoc.
        destruct U1_unitary as [_ U1_unitary].
        rewrite U1_unitary, Mmult_1_l.
        all: solve_WF_matrix.
      }
      {
        unfold bcgate in H3.
        rewrite kron_assoc in H3.
        rewrite Mmult_assoc in H3.
        repeat rewrite (@kron_mixed_product 2 2 1 4 4 1) in H3.
        rewrite Mmult_1_l in H3.
        symmetry.
        all: solve_WF_matrix.
      }
    }
    destruct H4 as [Q0 [Q1 [U4_decomp [Q0_unitary Q1_unitary]]]].
    apply (f_equal (fun f => f†)) in U4_decomp.
    rewrite adjoint_involutive in U4_decomp.
    rewrite Mplus_adjoint in U4_decomp.
    do 2 rewrite kron_adjoint in U4_decomp.
    rewrite adjoint00, adjoint11 in U4_decomp.
    assert (u0 = u1 \/ u0 * u1 = C1).
    {
      apply m4_4; auto.
      exists U1, W2, V3, U4.
      split. assumption.
      split. assumption.
      split. assumption.
      split. assumption.
      exists Q0†, Q1†.
      split. solve_WF_matrix.
      split. solve_WF_matrix.
      split; assumption.
    }
    destruct H4.
    left; assumption.
    right; left; assumption.
  }
  {
    right; right.
    apply a31; auto.
  }
  {
    destruct case_C as [ψ [ψ_qubit case_C]].
    assert (exists (P0 : Square 2), WF_Unitary P0 /\
      forall (x : Vector 2), WF_Qubit x -> V3† × (x ⊗ ∣0⟩) = ψ ⊗ (P0 × x)).
    {
      apply (a25 V3† ψ); solve_WF_matrix.
    }
    destruct H2 as [P0 [P0_unitary H2]].
    assert (forall (x : Vector 2), WF_Qubit x -> acgate U1 × (x ⊗ ∣0⟩ ⊗ ∣0⟩) = ψ ⊗ (U4† × (∣0⟩ ⊗ (P0 × x)))).
    {
      intros x x_qubit.
      specialize (H1 x x_qubit).
      specialize (H2 x x_qubit).
      rewrite H1; clear H1.
      unfold acgate, abgate, swapbc.
      repeat rewrite Mmult_assoc.
      rewrite kron_assoc.
      rewrite (@kron_mixed_product 2 2 1 4 4 1).
      rewrite a10.
      rewrite Mmult_1_l.
      rewrite <- (@kron_assoc 2 1 2 1 2 1).
      rewrite (@kron_mixed_product 4 4 1 2 2 1).
      rewrite H2 at 1.
      rewrite Mmult_1_l.
      rewrite (@kron_assoc 2 1 2 1 2 1).
      rewrite (@kron_mixed_product 2 2 1 4 4 1).
      rewrite a10.
      unfold bcgate.
      rewrite kron_mixed_product.
      repeat rewrite Mmult_1_l.
      all: solve_WF_matrix.
    }
    assert (forall (x : Vector 2), WF_Qubit x ->
      exists (w : Vector 2), WF_Qubit w /\ U4† × (∣0⟩ ⊗ (P0 × x)) = ∣0⟩ ⊗ w).
    {
      intros x x_qubit.
      apply (a22 U1 x ∣0⟩ ∣0⟩ ψ); solve_WF_matrix.
      (* TODO: Integrate this into solve_WF_matrix *)
      apply qubit0_qubit.
      apply qubit0_qubit.
      apply Mmult_qubit.
      solve_WF_matrix.
      apply (@kron_qubit 2 2).
      apply qubit0_qubit.
      apply Mmult_qubit; assumption.
      specialize (H3 x x_qubit).
      assumption.
    }
    assert (exists (Q0 Q1 : Square 2), U4† = ∣0⟩⟨0∣ ⊗ Q0 .+ ∣1⟩⟨1∣ ⊗ Q1 /\ WF_Unitary Q0 /\ WF_Unitary Q1).
    {
      apply (a17 U4† (P0 × ∣0⟩) (P0 × ∣1⟩)); solve_WF_matrix.
      (* TODO: Integrate this into solve_WF_matrix *)
      apply Mmult_qubit.
      assumption.
      apply qubit0_qubit.
      apply Mmult_qubit.
      assumption.
      apply qubit1_qubit.
      rewrite inner_product_adjoint_r.
      destruct P0_unitary as [_ P0_unitary].
      rewrite <- Mmult_assoc, P0_unitary, Mmult_1_l.
      lca.
      solve_WF_matrix.
      pose proof H4.
      specialize (H4 ∣0⟩ qubit0_qubit).
      specialize (H5 ∣1⟩ qubit1_qubit).
      destruct H4 as [w [w_qubit H4]].
      destruct H5 as [φ [φ_qubit H5]].
      exists w, φ.
      split. apply w_qubit.
      split. apply φ_qubit.
      split; assumption.
    }
    destruct H5 as [Q0 [Q1 [U4_decomp [Q0_unitary Q1_unitary]]]].
    apply (f_equal (fun f => f†)) in U4_decomp.
    rewrite adjoint_involutive in U4_decomp.
    rewrite Mplus_adjoint in U4_decomp.
    do 2 rewrite kron_adjoint in U4_decomp.
    rewrite adjoint00, adjoint11 in U4_decomp.
    assert (u0 = u1 \/ u0 * u1 = C1).
    {
      apply m4_4; auto.
      exists U1, W2, V3, U4.
      split. assumption.
      split. assumption.
      split. assumption.
      split. assumption.
      exists Q0†, Q1†.
      split. solve_WF_matrix.
      split. solve_WF_matrix.
      split; assumption.
    }
    destruct H5.
    left; assumption.
    right; left; assumption.
  }
Qed.

Lemma m6_3 : forall (u0 u1 : C), Cmod u0 = 1 -> Cmod u1 = 1 ->
  forall (V1 V2 V3 V4 : Square 4), WF_Unitary V1 -> WF_Unitary V2 -> WF_Unitary V3 -> WF_Unitary V4 ->
  (acgate V1 × bcgate V2 × acgate V3 × bcgate V4 = ccu (diag2 u0 u1) /\
  (exists (ψ : Vector 2), WF_Qubit ψ /\
    forall (x : Vector 2), WF_Qubit x ->
      exists (z : Vector 2), WF_Qubit z /\
        V2 × (x ⊗ ∣0⟩) = z ⊗ ψ) /\
  V3 × (∣0⟩ ⊗ ∣0⟩) = ∣0⟩ ⊗ ∣0⟩) ->
  u0 = u1 \/ u0 * u1 = C1 \/ exists (W1 W2 W3 W4 : Square 4),
    WF_Unitary W1 /\ WF_Unitary W2 /\ WF_Unitary W3 /\ WF_Unitary W4 /\
    exists (P1 P2 P3 P4 Q : Square 2),
    WF_Unitary P1 /\ WF_Unitary P2 /\ WF_Unitary P3 /\ WF_Unitary P4 /\ WF_Unitary Q /\
      acgate W1 × bcgate W2 × acgate W3 × bcgate W4 = ccu (diag2 u0 u1) /\
      W1 = I 2 ⊗ (Q × ∣0⟩⟨0∣) .+ P1 ⊗ (Q × ∣1⟩⟨1∣) /\
      W2 = I 2 ⊗ ∣0⟩⟨0∣ .+ P2 ⊗ ∣1⟩⟨1∣ /\
      W3 = I 2 ⊗ ∣0⟩⟨0∣ .+ P3 ⊗ ∣1⟩⟨1∣ /\
      W4 = I 2 ⊗ (∣0⟩⟨0∣ × Q†) .+ P4 ⊗ (∣1⟩⟨1∣ × Q†).
Proof.
  intros u0 u1 unit_u0 unit_u1 V1 V2 V3 V4 V1_unitary V2_unitary V3_unitary V4_unitary [eq2 [eq3 eq4]].
  pose proof (a30 V1 V2 V3 V4 V1_unitary V2_unitary V3_unitary V4_unitary eq3) as eq5; clear eq3.
  destruct eq5 as [U1 [W2 [U4 [P2 [U1_unitary [W2_unitary [U4_unitary [P2_unitary [eq5 eq6]]]]]]]]].
  rewrite eq5 in eq2; clear eq5; rename eq2 into eq7.
  assert (eq8: forall (x : Vector 2), WF_Qubit x -> acgate U1 × (x ⊗ ∣0⟩ ⊗ ∣0⟩) = bcgate U4† × acgate V3† × (x ⊗ ∣0⟩ ⊗ ∣0⟩)).
  {
    symmetry.
    rewrite <- acgate_adjoint, <- bcgate_adjoint.
    apply (a29 U1 W2 V3 U4 (diag2 u0 u1)).
    all: solve_WF_matrix.
    rewrite eq6.
    lma'; solve_WF_matrix.
  }
  pose proof (
m6_2 u0 u1 unit_u0 unit_u1 U1 W2 V3 U4
    U1_unitary W2_unitary V3_unitary U4_unitary
  ) as H.
  assert (tmp : acgate U1 × bcgate W2 × acgate V3 × bcgate U4 = ccu (diag2 u0 u1) /\
    V3 × (∣0⟩ ⊗ ∣0⟩) = ∣0⟩ ⊗ ∣0⟩ /\
    (forall x : Vector 2, WF_Qubit x ->
      acgate U1 × (x ⊗ ∣0⟩ ⊗ ∣0⟩) = bcgate (U4) † × acgate (V3) † × (x ⊗ ∣0⟩ ⊗ ∣0⟩))).
  {
    split. assumption.
    split. assumption.
    intros x x_qubit.
    apply (eq8 x x_qubit).
  }
  specialize (H tmp); clear tmp.
  destruct H as [u0_eq_u1 | [u0_u1_eq_C1 | H]].
  {
    left; assumption.
  }
  {
    right; left; assumption.
  }
  {
    destruct H as [W1 [W3 [W4 [W1_unitary [W3_unitary [W4_unitary [P3 [P3_unitary [eq9 eq10]]]]]]]]].
    rewrite eq9 in eq7; rename eq7 into eq11; clear eq9.
    assert (eq12 : forall (z : Vector 2), WF_Qubit z ->
      acgate W1 × bcgate W2 × (∣0⟩ ⊗ z ⊗ ∣0⟩) = bcgate W4† × (∣0⟩ ⊗ z ⊗ ∣0⟩)).
    {
      rewrite <- bcgate_adjoint; solve_WF_matrix.
      apply (a28 W1 W2 W3 W4 (diag2 u0 u1)); solve_WF_matrix.
      rewrite eq10.
      lma'; solve_WF_matrix.
    }
    assert (eq13 : exists (β : Vector 2), WF_Qubit β /\
      forall (z : Vector 2), WF_Qubit z -> W4† × (z ⊗ ∣0⟩) = z ⊗ β).
    {
      assert (forall (z : Vector 2), WF_Qubit z ->
        acgate W1 × (∣0⟩ ⊗ z ⊗ ∣0⟩) = bcgate W4† × (∣0⟩ ⊗ z ⊗ ∣0⟩)).
      {
        intros z z_qubit.
        specialize (eq12 z z_qubit).
        rewrite <- eq12; clear eq12.
        rewrite eq6; clear eq6.
        unfold bcgate.
        rewrite kron_plus_distr_l.
        rewrite Mmult_assoc.
        rewrite Mmult_plus_distr_r.
        repeat rewrite <- kron_assoc.
        repeat rewrite (@kron_mixed_product 4 4 1 2 2 1).
        replace (∣1⟩⟨1∣ × ∣0⟩) with (@Zero 2 1) by lma'.
        replace (∣0⟩⟨0∣ × ∣0⟩) with ∣0⟩ by lma'.
        rewrite kron_0_r, Mplus_0_r.
        rewrite (@kron_mixed_product 2 2 1 2 2 1).
        repeat rewrite Mmult_1_l.
        all: solve_WF_matrix.
      }
      assert (forall (z : Vector 2), WF_Qubit z ->
        exists (w : Vector 2), WF_Qubit w /\ W4† × (z ⊗ ∣0⟩) = z ⊗ w).
      {
        intros z z_qubit.
        apply (a22 W1 ∣0⟩ z ∣0⟩ ∣0⟩); solve_WF_matrix.
        apply qubit0_qubit.
        apply qubit0_qubit.
        apply qubit0_qubit.
        apply Mmult_qubit.
        solve_WF_matrix.
        apply (@kron_qubit 2 2).
        assumption.
        apply qubit0_qubit.
        specialize (H z z_qubit).
        rewrite H; clear H.
        unfold bcgate.
        rewrite kron_assoc.
        rewrite kron_mixed_product.
        rewrite Mmult_1_l.
        all: solve_WF_matrix.
      }
      apply a26; solve_WF_matrix.
    }
    destruct eq13 as [β [β_qubit eq13]].
    assert (eq13_adjoint : forall (z : Vector 2), WF_Qubit z -> W4 × (z ⊗ β) = z ⊗ ∣0⟩).
    {
      intros z z_qubit.
      specialize (eq13 z z_qubit).
      rewrite <- eq13; clear eq13.
      rewrite <- Mmult_assoc.
      rewrite (other_unitary_decomp W4), Mmult_1_l.
      all: solve_WF_matrix.
    }
    set (β_perp := (fun x y => match x, y with
                                | 0, 0 => -(β 1 0)^*%nat
                                | 1, 0 => (β 0 0)^*%nat
                                | _, _ => C0
                                end) : Vector 2).
    assert (β_perp_qubit : WF_Qubit β_perp).
    {
      unfold WF_Qubit.
      split. exists 1%nat; trivial.
      split. show_wf.
      destruct β_qubit as [_ [_ β_unit]].
      rewrite <- β_unit; clear β_unit.
      lca.
    }
    assert (β_mult : β† × β = I 1).
    {
      lma'; solve_WF_matrix.
      destruct β_qubit as [_ [_ β_unit]].
      unfold I; simpl.
      rewrite <- β_unit; lca.
    }
    assert (β_perp_mult : β_perp† × β_perp = I 1).
    {
      lma'; solve_WF_matrix.
      destruct β_perp_qubit as [_ [_ β_perp_unit]].
      unfold I; simpl.
      rewrite <- β_perp_unit; lca.
    }
    set (Q := β × ⟨0∣ .+ β_perp × ⟨1∣).
    assert (Q_unitary : WF_Unitary Q).
    {
      assert (WF_Q : WF_Matrix Q) by solve_WF_matrix.
      unfold WF_Unitary.
      split. assumption.
      subst Q.
      distribute_adjoint.
      repeat rewrite adjoint_involutive.
      rewrite Mmult_plus_distr_l.
      do 2 rewrite Mmult_plus_distr_r.
      repeat rewrite <- Mmult_assoc.
      do 2 rewrite Mmult_assoc with (A := ∣0⟩).
      do 2 rewrite Mmult_assoc with (B := β_perp †).
      rewrite β_mult, β_perp_mult.
      assert (∣1⟩ × ((β_perp) † × β) × ⟨0∣ = Zero).
      {
        lma'; solve_WF_matrix.
      }
      assert (∣0⟩ × (β) † × β_perp × ⟨1∣ = Zero).
      {
        lma'; solve_WF_matrix.
      }
      rewrite H, H0.
      Msimpl_light.
      rewrite Mplus01.
      reflexivity.
    }
    assert (forall z, WF_Qubit z ->
      W4 × (I 2 ⊗ Q) × (z ⊗ ∣0⟩) = z ⊗ ∣0⟩).
    {
      intros z z_qubit.
      rewrite Mmult_assoc.
      rewrite (@kron_mixed_product 2 2 1 2 2 1).
      assert (Q × ∣0⟩ = β).
      {
        lma'; solve_WF_matrix.
      }
      rewrite H; clear H.
      rewrite Mmult_1_l.
      rewrite (eq13_adjoint z z_qubit).
      all: solve_WF_matrix.
    }
    assert (exists (P4 : Square 2), WF_Unitary P4 /\
        W4 × (I 2 ⊗ Q) = I 2 ⊗ ∣0⟩⟨0∣ .+ P4 ⊗ ∣1⟩⟨1∣).
    {
      apply (a18 (W4 × (I 2 ⊗ Q))); solve_WF_matrix.
    }
    assert (exists (P4 : Square 2), WF_Unitary P4 /\
      W4 = I 2 ⊗ (∣0⟩⟨0∣ × Q†) .+ P4 ⊗ (∣1⟩⟨1∣ × Q†)).
    {
      destruct H0 as [P4 [P4_unitary H0]].
      exists P4.
      split. assumption.
      apply (f_equal (fun x => x × (I 2 ⊗ Q)†)) in H0.
      rewrite kron_adjoint in H0.
      rewrite Mmult_assoc in H0.
      rewrite (@kron_mixed_product 2 2 2 2 2 2) in H0.
      rewrite (other_unitary_decomp Q) in H0.
      rewrite id_adjoint_eq, Mmult_1_l, id_kron, Mmult_1_r in H0.
      rewrite H0; clear H0.
      rewrite Mmult_plus_distr_r.
      do 2 rewrite kron_mixed_product.
      Msimpl_light.
      all: solve_WF_matrix.
    }
    assert (eq14 : forall (x : Vector 2), WF_Qubit x ->
      acgate W1 × (x ⊗ ∣0⟩ ⊗ ∣0⟩) = bcgate W4† × acgate W3† × (x ⊗ ∣0⟩ ⊗ ∣0⟩)).
    {
      intros x x_qubit.
      symmetry.
      rewrite <- bcgate_adjoint, <- acgate_adjoint.
      apply (a29 W1 W2 W3 W4 (diag2 u0 u1)).
      all: solve_WF_matrix.
      rewrite eq6.
      lma'; solve_WF_matrix.
    }
    assert (forall (x : Vector 2), WF_Qubit x ->
      (I 4 ⊗ Q†) × acgate W1 × (x ⊗ ∣0⟩ ⊗ ∣0⟩) = x ⊗ ∣0⟩ ⊗ ∣0⟩).
    {
      intros x x_qubit.
      rewrite Mmult_assoc.
      rewrite (eq14 x x_qubit) at 1; clear eq14.
      assert (acgate (W3) † × (x ⊗ ∣0⟩ ⊗ ∣0⟩) = x ⊗ ∣0⟩ ⊗ ∣0⟩).
      {
        unfold acgate, abgate, swapbc.
        repeat rewrite Mmult_assoc.
        rewrite kron_assoc.
        rewrite (@kron_mixed_product 2 2 1 4 4 1).
        rewrite a10.
        rewrite Mmult_1_l.
        rewrite <- Mmult_assoc.
        rewrite eq10.
        rewrite Mplus_adjoint.
        do 2 rewrite kron_adjoint.
        rewrite id_adjoint_eq, adjoint00, adjoint11.
        rewrite kron_plus_distr_r.
        rewrite Mmult_plus_distr_l.
        rewrite Mmult_plus_distr_r.
        repeat rewrite kron_assoc.
        repeat rewrite (@kron_mixed_product 2 2 2 4 4 4).
        repeat rewrite Mmult_1_l.
        do 2 rewrite (@kron_mixed_product 2 2 1 4 4 1).
        do 2 rewrite Mmult_assoc.
        do 2 rewrite (@kron_mixed_product 2 2 1 2 2 1).
        replace ((∣1⟩⟨1∣ × ∣0⟩)) with (@Zero 2 1)%nat by lma'.
        replace ((∣0⟩⟨0∣ × ∣0⟩)) with ∣0⟩ by lma'.
        Msimpl_light.
        repeat rewrite a10.
        all: solve_WF_matrix.
      }
      rewrite Mmult_assoc.
      rewrite H2 at 1; clear H2.
      unfold bcgate.
      rewrite kron_assoc, kron_mixed_product.
      rewrite (eq13 ∣0⟩) at 1.
      rewrite Mmult_1_l.
      rewrite <- kron_assoc.
      rewrite <- (@kron_assoc 2 1 2 1 2 1) at 1.
      rewrite (@kron_mixed_product 4 4 1 2 2 1).
      rewrite Mmult_1_l.
      unfold Q.
      distribute_adjoint.
      repeat rewrite adjoint_involutive.
      rewrite Mmult_plus_distr_r.
      repeat rewrite Mmult_assoc.
      rewrite β_mult.
      replace (β_perp† × β) with (@Zero 1 1).
      Msimpl_light.
      all: solve_WF_matrix.
      lma'; solve_WF_matrix.
      apply qubit0_qubit.
    }
    assert (forall (x : Vector 2), WF_Qubit x ->
      ((I 2 ⊗ Q†) × W1) × (x ⊗ ∣0⟩) = x ⊗ ∣0⟩).
    {
      intros x x_qubit.
      apply (@kron_cancel_r _ _ 2 1) with (C := ∣0⟩); solve_WF_matrix.
      apply nonzero_qubit0.
      specialize (H2 x x_qubit).
      apply (f_equal (fun x => (I 2 ⊗ swap) × x)) in H2.
      rewrite kron_assoc in H2.
      rewrite kron_mixed_product in H2.
      rewrite a10 in H2.
      rewrite Mmult_1_l in H2.
      rewrite kron_assoc, <- H2 at 1; clear H2.
      unfold acgate, abgate, swapbc.
      rewrite <- (@id_kron 2 2) at 1.
      repeat rewrite <- Mmult_assoc.
      repeat rewrite (@kron_assoc 2 2 2 2 2 2).
      repeat rewrite (@kron_mixed_product 2 2 2 4 4 4).
      rewrite a11.
      repeat rewrite Mmult_1_l.
      rewrite Mmult_assoc with (B := I 2 ⊗ swap).
      rewrite (@kron_mixed_product 2 2 1 4 4 1).
      rewrite a10, Mmult_1_l.
      rewrite <- (@kron_assoc 2 2 2 2 2 2).
      rewrite (@kron_mixed_product 4 4 4 2 2 2).
      rewrite Mmult_1_r.
      rewrite <- (@kron_assoc 2 1 2 1 2 1).
      rewrite (@kron_mixed_product 4 4 1 2 2 1).
      rewrite Mmult_1_l.
      all: solve_WF_matrix.
    }
    assert (exists (P1 : Square 2), WF_Unitary P1 /\
      (I 2 ⊗ Q†) × W1 = I 2 ⊗ ∣0⟩⟨0∣ .+ P1 ⊗ ∣1⟩⟨1∣).
    {
      apply a18.
      solve_WF_matrix.
      intros x x_qubit.
      apply H3; solve_WF_matrix.
    }
    assert (exists (P1 : Square 2), WF_Unitary P1 /\
      W1 = I 2 ⊗ (Q × ∣0⟩⟨0∣) .+ P1 ⊗ (Q × ∣1⟩⟨1∣)).
    {
      destruct H4 as [P1 [P1_unitary H4]].
      exists P1.
      split. assumption.
      apply (f_equal (fun x => (I 2 ⊗ Q†)† × x)) in H4.
      assert (WF_Unitary (I 2 ⊗ Q†)) by solve_WF_matrix.
      destruct H5 as [_ H5].
      rewrite <- Mmult_assoc in H4.
      rewrite H5 in H4; clear H5.
      rewrite Mmult_1_l in H4.
      rewrite H4; clear H4.
      rewrite kron_adjoint.
      rewrite id_adjoint_eq, adjoint_involutive.
      rewrite Mmult_plus_distr_l.
      repeat rewrite kron_mixed_product.
      Msimpl_light.
      all: solve_WF_matrix.
    }
    right; right.
    exists W1, W2, W3, W4.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    destruct H5 as [P1 [P1_unitary W1_decomp]].
    destruct H1 as [P4 [P4_unitary W4_decomp]].
    exists P1, P2, P3, P4, Q.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    assumption.
  }
Qed.

Lemma m6_4 : forall (u0 u1 : C), Cmod u0 = 1 -> Cmod u1 = 1 ->
  (exists (U1 U2 U3 U4 : Square 4),
    WF_Unitary U1 /\ WF_Unitary U2 /\ WF_Unitary U3 /\ WF_Unitary U4 /\
    acgate U1 × bcgate U2 × acgate U3 × bcgate U4 = ccu (diag2 u0 u1))
  <-> u0 = u1 \/ u0 * u1 = C1.
Proof.
  intros.
  split.
  {
    intro.
    destruct H1 as [U1 [U2 [U3 [U4 [U1_unitary [U2_unitary [U3_unitary [U4_unitary H1]]]]]]]].
    pose proof (a32 U1 U2 U3 U4 U1_unitary U2_unitary U3_unitary U4_unitary) as H2.
    destruct H2 as [V1 [V2 [V3 [V4 [V1_unitary [V2_unitary [V3_unitary [V4_unitary [H2 H3]]]]]]]]].
    rewrite H2 in H1; clear H2.
    assert (WF_Unitary (diag2 u0 u1)).
    {
      apply diag2_unitary; auto.
    }
    pose proof (
      a28 V1 V2 V3 V4 (diag2 u0 u1)
      V1_unitary V2_unitary V3_unitary V4_unitary H2
      H1 H3
    ).
    pose proof (m6_1 V2 V2_unitary).
    destruct H5 as [case_A | [case_B | case_C]].
    {
      destruct case_A as [x [x_qubit entangled]].
      specialize (H4 x x_qubit).
      (* TODO(Kyle): Reorder these arguments (in a19 as well) *)
      assert (exists (P0 P1 : Square 2),
        V1 = ∣0⟩⟨0∣ ⊗ P0 .+ ∣1⟩⟨1∣ ⊗ P1 /\  WF_Unitary P0 /\ WF_Unitary P1).
      {
        assert (⟨ x ⊗ ∣0⟩, x ⊗ ∣0⟩ ⟩ = C1).
        {
          rewrite inner_product_kron.
          destruct x_qubit as [_ [_ x_unit]].
          rewrite x_unit.
          lca.
        }
        apply (a19 V1 (V2 × (x ⊗ ∣0⟩)) (V4† × (x ⊗ ∣0⟩))); solve_WF_matrix.
        rewrite inner_product_adjoint_l.
        rewrite <- Mmult_assoc.
        destruct V2_unitary as [_ V2_unitary].
        rewrite V2_unitary, Mmult_1_l.
        all: solve_WF_matrix.
        rewrite inner_product_adjoint_r, adjoint_involutive.
        repeat rewrite <- Mmult_assoc.
        rewrite (other_unitary_decomp V4), Mmult_1_l.
        all: solve_WF_matrix.
        rewrite <- Mmult_1_l with (A := ∣0⟩) at 1.
        rewrite <- kron_mixed_product.
        fold (bcgate V2).
        rewrite <- Mmult_assoc.
        rewrite <- kron_assoc with (A := ∣0⟩) (B := x) (C := ∣0⟩) at 1.
        rewrite H4 at 1.
        unfold bcgate.
        rewrite kron_adjoint, id_adjoint_eq.
        rewrite kron_assoc.
        rewrite kron_mixed_product.
        rewrite Mmult_1_l.
        all: solve_WF_matrix.
      }
      destruct H5 as [P0 [P1 [V1_decomp [P0_unitary P1_unitary]]]].
      apply (m4_3 u0 u1 H H0); auto.
      exists V1, V2, V3, V4.
      split. assumption.
      split. assumption.
      split. assumption.
      split. assumption.
      exists P0, P1.
      split. assumption.
      split. assumption.
      split. assumption.
      assumption.
    }
    {
      destruct case_B as [ψ [ψ_qubit H5]].
      assert (acgate V1 × bcgate V2 × acgate V3 × bcgate V4 = ccu (diag2 u0 u1) /\
        (exists ψ0 : Vector 2, WF_Qubit ψ0 /\
          (forall x : Vector 2, WF_Qubit x ->
            exists z : Vector 2, WF_Qubit z /\
            V2 × (x ⊗ ∣0⟩) = z ⊗ ψ0)) /\ V3 × (∣0⟩ ⊗ ∣0⟩) = ∣0⟩ ⊗ ∣0⟩).
      {
        split.
        - assumption.
        - split.
          * exists ψ.
            split. assumption.
            assumption.
          * assumption.
      }
      pose proof (
        m6_3 u0 u1 H H0
        V1 V2 V3 V4
        V1_unitary V2_unitary V3_unitary V4_unitary
        H6
      ); clear H6.
      destruct H7 as [u0_eq_u1 | [u0u1_eq_C1 | H7]].
      {
        left; assumption.
      }
      {
        right; assumption.
      }
      {
        destruct H7 as [W1 [W2 [W3 [W4 [W1_unitary [W2_unitary [W3_unitary [W4_unitary H7]]]]]]]].
        destruct H7 as [P1 [P2 [P3 [P4 [Q [P1_unitary [P2_unitary [P3_unitary [P4_unitary [Q_unitary H7]]]]]]]]]].
        destruct H7 as [H7 [W1_decomp [W2_decomp [W3_decomp W4_decomp]]]].
        assert (ccu (diag2 u0 u1) = I 2 ⊗ I 2 ⊗ (Q × ∣0⟩⟨0∣ × Q†) .+ (P1 × P3) ⊗ (P2 × P4) ⊗ (Q × ∣1⟩⟨1∣ × Q†)).
        {
          rewrite <- H7; clear H7.
          rewrite W1_decomp, W2_decomp, W3_decomp, W4_decomp; clear W1_decomp W2_decomp W3_decomp W4_decomp.
          unfold acgate, bcgate, abgate, swapbc.
          repeat rewrite kron_plus_distr_l.
          repeat rewrite kron_plus_distr_r.
          repeat rewrite Mmult_plus_distr_l.
          repeat rewrite Mmult_plus_distr_r.
          repeat rewrite kron_assoc.
          repeat rewrite (@kron_mixed_product 2 2 2 4 4 4).
          repeat rewrite swap_2gate.
          repeat rewrite Mmult_1_l.
          repeat rewrite (@kron_mixed_product 2 2 2 2 2 2).
          repeat rewrite Mmult_assoc with (B := ∣0⟩⟨0∣).
          rewrite cancel00.
          rewrite cancel01.
          Msimpl_light.
          repeat rewrite Mmult_plus_distr_l.
          repeat rewrite Mmult_plus_distr_r.
          repeat rewrite (@kron_mixed_product 2 2 2 4 4 4).
          repeat rewrite (@kron_mixed_product 2 2 2 2 2 2).
          repeat rewrite Mmult_assoc with (A := Q).
          repeat rewrite cancel00.
          repeat rewrite cancel01.
          repeat rewrite cancel10.
          repeat rewrite cancel11.
          Msimpl_light.
          rewrite <- Mmult_assoc with (A := ∣0⟩⟨0∣) (B := ∣0⟩⟨0∣).
          rewrite <- Mmult_assoc with (A := ∣0⟩⟨0∣) (B := ∣1⟩⟨1∣).
          rewrite <- Mmult_assoc with (A := ∣1⟩⟨1∣) (B := ∣0⟩⟨0∣).
          rewrite <- Mmult_assoc with (A := ∣1⟩⟨1∣) (B := ∣1⟩⟨1∣).
          rewrite cancel00, cancel11.
          rewrite cancel01.
          repeat rewrite cancel10.
          Msimpl_light.
          all: solve_WF_matrix.
        }
        assert (u0 = C1 /\ u1 = C1).
        {
          rewrite <- (m4_2 u0 u1 H H0 Q Q_unitary).
          exists (P1 × P3), (P2 × P4).
          split. solve_WF_matrix.
          split. solve_WF_matrix.
          rewrite H6.
          repeat rewrite Mmult_adjoint.
          repeat rewrite <- Mmult_assoc.
          reflexivity.
        }
        destruct H8.
        rewrite H8, H9.
        left; reflexivity.
      }
    }
    {
      destruct case_C as [ψ [ψ_qubit H5]].
      assert (exists (P0 P1 : Square 2),
        V1 = ∣0⟩⟨0∣ ⊗ P0 .+ ∣1⟩⟨1∣ ⊗ P1 /\  WF_Unitary P0 /\ WF_Unitary P1).
      {
        apply (a33 V1 V2 V4); auto.
        exists ψ.
        split. assumption.
        intros x x_qubit.
        specialize (H5 x x_qubit).
        destruct H5 as [z [z_qubit H5]].
        exists z.
        split; assumption.
      }
      destruct H6 as [P0 [P1 [V1_decomp [P0_unitary P1_unitary]]]].
      apply (m4_3 u0 u1 H H0); auto.
      exists V1, V2, V3, V4.
      split. assumption.
      split. assumption.
      split. assumption.
      split. assumption.
      exists P0, P1.
      split. assumption.
      split. assumption.
      split. assumption.
      assumption.
    }
  }
  {
    intros.
    rewrite <- (m4_3 u0 u1) in H1.
    destruct H1 as [V1 [V2 [V3 [V4 [V1_unitary [V2_unitary [V3_unitary [V4_unitary [_ [_ [_ [_ [_ H1]]]]]]]]]]]]].
    exists V1, V2, V3, V4.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    assumption.
    assumption.
    assumption.
  }
Qed.

Lemma m7_1 : forall (u0 u1 : C), Cmod u0 = 1 -> Cmod u1 = 1 ->
  forall (U : Square 8), WF_Unitary U ->
  forall (W : Square 4), WF_Unitary W ->
  ccu (diag2 u0 u1) = abgate W × U -> exists (V : Square 4), WF_Unitary V /\
  ccu (diag2 C1 (u0^* * u1)) = abgate V × U.
Proof.
  intros u0 u1 u0_unit u1_unit U U_unitary W W_unitary H.
  exists (control (diag2 C1 (u0^*)) × W).
  split.
  {
    solve_WF_matrix.
    apply diag2_unitary.
    apply Cmod_1.
    rewrite Cmod_Cconj.
    exact u0_unit.
  }
  {
    unfold abgate.
    rewrite <- Mmult_1_l with (A := I 2); solve_WF_matrix.
    rewrite <- kron_mixed_product.
    unfold abgate in H.
    rewrite Mmult_assoc.
    rewrite <- H at 1; clear H.
    (* For performance reasons, we'll show both sides are diagonal first,
       instead of directly invoking lma'. *)
    assert (WF_Diagonal (ccu (diag2 C1 (u0 ^* * u1)))).
    {
      apply ccu_diag.
      apply Diag_diag2.
    }
    assert (WF_Diagonal (control (diag2 C1 (u0 ^*)) ⊗ I 2 × ccu (diag2 u0 u1))).
    {
      apply diag_mult.
      apply diag_kron.
      apply diag_control.
      apply Diag_diag2.
      apply diag_I.
      apply ccu_diag.
      apply Diag_diag2.
    }
    prep_matrix_equality.
    bdestruct (x =? y).
    {
      rewrite <- H1; clear H1.
      destruct H as [H _].
      destruct H0 as [H0 _].
      specialize (H x x).
      specialize (H0 x x).
      destruct x.
      unfold ccu, control, diag2, I, kron, Mmult; lca.
      destruct x.
      unfold ccu, control, diag2, I, kron, Mmult; lca.
      destruct x.
      unfold ccu, control, diag2, I, kron, Mmult; lca.
      destruct x.
      unfold ccu, control, diag2, I, kron, Mmult; lca.
      destruct x.
      unfold ccu, control, diag2, I, kron, Mmult; lca.
      destruct x.
      unfold ccu, control, diag2, I, kron, Mmult; lca.
      destruct x.
      unfold ccu, control, diag2, I, kron, Mmult; simpl; Csimpl.
      rewrite <- Cmod_sqr, u0_unit; lca.
      destruct x.
      unfold ccu, control, diag2, I, kron, Mmult; lca.
      rewrite H, <- H0.
      reflexivity.
      all: lia.
    }
    {
      destruct H as [_ H].
      destruct H0 as [_ H0].
      specialize (H x y H1).
      specialize (H0 x y H1).
      rewrite H, <- H0; reflexivity.
    }
  }
Qed.
