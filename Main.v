Require Import Proof.UnitaryMatrices.
Require Import Proof.Permutations.
Require Import Proof.SquareMatrices.
Require Import Proof.AlgebraHelpers.
Require Import Proof.MatrixHelpers.
Require Import Proof.GateHelpers.
Require Import Proof.SwapHelpers.
Require Import Proof.EigenvalueHelpers.
Require Import Proof.OtherProperties.
Require Import Proof.WFHelpers.
Require Import Proof.Swaps.
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
        lma'; solve_WF_matrix.
        show_wf.
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
        ) in Unitary_U; solve_WF_matrix; try lia.
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
        unfold diag2; Msimpl_light; lma'; solve_WF_matrix.
        show_wf.
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
    assert (step : control (diag2 u0 u1) = I 2 .⊕ diag2 u0 u1).
    {
      rewrite (direct_sum_decomp _ _ 2 2)%nat; solve_WF_matrix.
      lma'.
      all: unfold control, diag2, adjoint, I, kron, Mmult, Mplus; simpl; lca.
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
    rewrite control_decomp in H1.
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
      rewrite control_decomp, <- (direct_sum_decomp _ _ 0 0); solve_WF_matrix.
      rewrite direct_sum_simplify; solve_WF_matrix.
      split; try reflexivity.
      (* PERF: Can probably be sped up by omitting lma' *)
      lma'; solve_WF_matrix.
      all: unfold notc, Mmult, diag2, control, kron; simpl; Csimpl; reflexivity.
    + exists notc, notc, (I 2), (diag2 1 u0), (I 2), (diag2 1 u1).
      split. apply notc_unitary.
      split. apply notc_unitary.
      split. apply id_unitary.
      split. apply diag2_unitary; auto; apply Cmod_1.
      split. apply id_unitary.
      split. apply diag2_unitary; auto; apply Cmod_1.
      rewrite id_kron.
      Msimpl_light.
      rewrite notc_notc.
      unfold ccu.
      rewrite control_decomp, <- (direct_sum_decomp _ _ 0 0); solve_WF_matrix.
      rewrite direct_sum_simplify; solve_WF_matrix.
      split; try reflexivity.
      (* PERF: Can probably be sped up by omitting lma' *)
      lma'; solve_WF_matrix.
      all: unfold notc, Mmult, diag2, control, kron; simpl; Csimpl; auto.
Qed.

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
    assert (Unitary_diag : WF_Unitary (control (diag2 u0 u1))).
    {
      apply control_unitary, diag2_unitary; auto.
    }
    assert (ccdiag_decomp : ccu (diag2 u0 u1) = ∣0⟩⟨0∣ ⊗ (I 4) .+ ∣1⟩⟨1∣ ⊗ (control (diag2 u0 u1))).
    {
      unfold ccu.
      rewrite control_decomp.
      rewrite <- (direct_sum_decomp _ _ 0 0); solve_WF_matrix.
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
      repeat rewrite swap_kron; solve_WF_matrix.
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
      rewrite u0_eq_u1; clear u0_eq_u1.
      exists (I 4), swap, (control (diag2 C1 u1)), swap.
      split. apply id_unitary.
      split. apply swap_unitary.
      split. apply (@control_unitary 2), diag2_unitary. apply Cmod_1. assumption.
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
      do 2 rewrite control_decomp.
      (* TODO: prove kron distributes over direct sums *)
      repeat rewrite (direct_sum_decomp _ _ 0 0); solve_WF_matrix.
      rewrite kron_plus_distr_r.
      rewrite kron_assoc with (C := I 2); solve_WF_matrix.
      rewrite kron_assoc with (C := I 2); solve_WF_matrix.
      repeat rewrite <- (direct_sum_decomp 4 4 0 0); solve_WF_matrix.

      rewrite direct_sum_simplify; solve_WF_matrix.
      split. rewrite id_kron; reflexivity.
      lma'; solve_WF_matrix.
      all: unfold kron, diag2, I, control; simpl; lca.
    }
    {
      assert (Cexp_Cmod : forall (c : C), Cmod c = 1 -> exists (θ : R), Cexp θ = c).
      {
        admit.
      }
      pose proof (Cexp_Cmod u1 unit_u1) as [θ u1_Cexp]; clear Cexp_Cmod.
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
        rewrite control_decomp, (direct_sum_decomp _ _ 0 0); solve_WF_matrix.
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
          rewrite control_decomp, (direct_sum_decomp _ _ 0 0); solve_WF_matrix.
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
          rewrite control_decomp, (@direct_sum_decomp _ _ 0 0).
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
        rewrite control_decomp.
        reflexivity.
        all: solve_WF_matrix.
      }
    }
  }
Admitted.
