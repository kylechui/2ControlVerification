Require Import Proof.UnitaryMatrices.
Require Import Proof.AlgebraHelpers.
Require Import Proof.MatrixHelpers.
Require Import Proof.GateHelpers.
Require Import Proof.EigenvalueHelpers.
Require Import QuantumLib.Complex.
Require Import QuantumLib.Quantum.
Require Import QuantumLib.Eigenvectors.
Require Import QuantumLib.Matrix.

Lemma m3_2 : forall (u0 u1 : C),
  Cmod u0 = 1 -> Cmod u1 = 1 ->
  (exists (P Q : Square 2),
    WF_Unitary P /\ WF_Unitary Q /\
    (exists (a b p q : C) (v1 v2 v3 v4 : Vector 2),
      WF_Matrix v1 /\ WF_Matrix v2 /\ WF_Matrix v3 /\ WF_Matrix v4 /\
      v1 <> Zero /\ v2 <> Zero /\ v3 <> Zero /\ v4 <> Zero /\
      Eigenpair P (v1, a) /\ Eigenpair P (v2, b) /\
      Eigenpair Q (v3, p) /\ Eigenpair Q (v4, q) /\
        (Eigenpair (P ⊗ Q) (v1 ⊗ v3, C1) /\
        Eigenpair (P ⊗ Q) (v1 ⊗ v4, C1) /\
        Eigenpair (P ⊗ Q) (v2 ⊗ v3, u0) /\
        Eigenpair (P ⊗ Q) (v2 ⊗ v4, u1) \/
        Eigenpair (P ⊗ Q) (v1 ⊗ v3, C1) /\
        Eigenpair (P ⊗ Q) (v1 ⊗ v4, u1) /\
        Eigenpair (P ⊗ Q) (v2 ⊗ v3, u0) /\
        Eigenpair (P ⊗ Q) (v2 ⊗ v4, C1))))
  <-> u0 = u1 \/ u0 * u1 = C1.
Proof.
  intros u0 u1 unit_u0 unit_u1.
  split.
  {
    intro.
    destruct H as [P [Q [Unitary_P [Unitary_Q H]]]].
    destruct H as [a [b [p [q [v1 [v2 [v3 [v4 H]]]]]]]].
    destruct H as [WF_v1 [WF_v2 [WF_v3 [WF_v4 H]]]].
    destruct H as [v1_nonzero [v2_nonzero [v3_nonzero [v4_nonzero H]]]].
    destruct H as [epair1 [epair2 [epair3 [epair4 H]]]].
    assert (WF_P : WF_Matrix P).
    {
      destruct Unitary_P.
      assumption.
    }
    assert (WF_Q : WF_Matrix Q).
    {
      destruct Unitary_Q.
      assumption.
    }
    destruct H.
    {
      destruct H as [epair5 [epair6 [epair7 epair8]]].
      assert (help1 : a * p = C1).
      {
        pose proof (
          a5_left
          P Q
          Unitary_P Unitary_Q
          a p v1 v3
          WF_v1 WF_v3
          epair1 epair3
        ) as H.
        unfold Eigenpair in epair5, H; simpl in epair5, H.
        rewrite epair5 in H.
        apply @scale_cancel_r with (A := v1 ⊗ v3) (m := 4%nat) (n := 1%nat); auto.
        solve_WF_matrix.
        apply nonzero_kron; auto.
      }
      assert (help2 : a * q = C1).
      {
        pose proof (
          a5_left
          P Q
          Unitary_P Unitary_Q
          a q v1 v4
          WF_v1 WF_v4
          epair1 epair4
        ) as H.
        unfold Eigenpair in epair6, H; simpl in epair6, H.
        rewrite epair6 in H.
        apply @scale_cancel_r with (A := v1 ⊗ v4) (m := 4%nat) (n := 1%nat); auto.
        solve_WF_matrix.
        apply nonzero_kron; auto.
      }
      assert (help3 : b * p = u0).
      {
        pose proof (
          a5_left
          P Q
          Unitary_P Unitary_Q
          b p v2 v3
          WF_v2 WF_v3
          epair2 epair3
        ) as H.
        unfold Eigenpair in epair7, H; simpl in epair7, H.
        rewrite epair7 in H.
        apply @scale_cancel_r with (A := v2 ⊗ v3) (m := 4%nat) (n := 1%nat); auto.
        solve_WF_matrix.
        apply nonzero_kron; auto.
      }
      assert (help4 : b * q = u1).
      {
        pose proof (
          a5_left
          P Q
          Unitary_P Unitary_Q
          b q v2 v4
          WF_v2 WF_v4
          epair2 epair4
        ) as H.
        unfold Eigenpair in epair8, H; simpl in epair8, H.
        rewrite epair8 in H.
        apply @scale_cancel_r with (A := v2 ⊗ v4) (m := 4%nat) (n := 1%nat); auto.
        solve_WF_matrix.
        apply nonzero_kron; auto.
      }
      left.
      rewrite <- help3, <- help4.
      rewrite <- Cmult_1_l with (x := b).
      rewrite <- help2 at 1.
      rewrite <- help1 at 1.
      lca.
    }
    {
      destruct H as [epair5 [epair6 [epair7 epair8]]].
      assert (help1 : a * p = C1).
      {
        pose proof (
          a5_left
          P Q
          Unitary_P Unitary_Q
          a p v1 v3
          WF_v1 WF_v3
          epair1 epair3
        ) as H.
        unfold Eigenpair in epair5, H; simpl in epair5, H.
        rewrite epair5 in H.
        apply @scale_cancel_r with (A := v1 ⊗ v3) (m := 4%nat) (n := 1%nat); auto.
        solve_WF_matrix.
        apply nonzero_kron; auto.
      }
      assert (help2 : a * q = u1).
      {
        pose proof (
          a5_left
          P Q
          Unitary_P Unitary_Q
          a q v1 v4
          WF_v1 WF_v4
          epair1 epair4
        ) as H.
        unfold Eigenpair in epair6, H; simpl in epair6, H.
        rewrite epair6 in H.
        apply @scale_cancel_r with (A := v1 ⊗ v4) (m := 4%nat) (n := 1%nat); auto.
        solve_WF_matrix.
        apply nonzero_kron; auto.
      }
      assert (help3 : b * p = u0).
      {
        pose proof (
          a5_left
          P Q
          Unitary_P Unitary_Q
          b p v2 v3
          WF_v2 WF_v3
          epair2 epair3
        ) as H.
        unfold Eigenpair in epair7, H; simpl in epair7, H.
        rewrite epair7 in H.
        apply @scale_cancel_r with (A := v2 ⊗ v3) (m := 4%nat) (n := 1%nat); auto.
        solve_WF_matrix.
        apply nonzero_kron; auto.
      }
      assert (help4 : b * q = C1).
      {
        pose proof (
          a5_left
          P Q
          Unitary_P Unitary_Q
          b q v2 v4
          WF_v2 WF_v4
          epair2 epair4
        ) as H.
        unfold Eigenpair in epair8, H; simpl in epair8, H.
        rewrite epair8 in H.
        apply @scale_cancel_r with (A := v2 ⊗ v4) (m := 4%nat) (n := 1%nat); auto.
        solve_WF_matrix.
        apply nonzero_kron; auto.
      }
      right.
      rewrite <- help2, <- help3.
      rewrite <- Cmult_1_l with (x := C1).
      rewrite <- help1 at 1.
      rewrite <- help4 at 1.
      lca.
    }
  }
  {
    intros.
    destruct H.
    {
      exists (diag2 1 u1), (I 2).
      split.
      {
        unfold WF_Unitary.
        split.
        {
          apply WF_diag2.
        }
        {
          lma'.
          solve_WF_matrix.
          apply WF_diag2.
          apply WF_diag2.
          unfold diag2, I, adjoint, Mmult; simpl.
          Csimpl.
          rewrite <- Cmod_sqr.
          rewrite unit_u1.
          lca.
        }
      }
      split.
      {
        apply id_unitary.
      }
      exists C1, u1, C1, C1.
      exists ∣0⟩, ∣1⟩, ∣0⟩, ∣1⟩.
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
        apply diag2_eigenpairs.
      }
      split.
      {
        apply diag2_eigenpairs.
      }
      split.
      {
        apply id2_eigenpairs.
      }
      split.
      {
        apply id2_eigenpairs.
      }
      left.
      split.
      {
        unfold Eigenpair.
        lma'; simpl.
        solve_WF_matrix.
        apply WF_diag2.
        solve_WF_matrix.
      }
      split.
      {
        unfold Eigenpair.
        lma'; simpl.
        solve_WF_matrix.
        apply WF_diag2.
        solve_WF_matrix.
      }
      split.
      {
        rewrite H.
        unfold Eigenpair.
        lma'; simpl.
        solve_WF_matrix.
        apply WF_diag2.
        solve_WF_matrix.
        unfold scale, Mmult, kron, diag2, I; simpl.
        lca.
      }
      {
        unfold Eigenpair.
        lma'; simpl.
        solve_WF_matrix.
        apply WF_diag2.
        solve_WF_matrix.
        unfold scale, Mmult, kron, diag2, I; simpl.
        lca.
      }
    }
    {
      exists (diag2 1 u0), (diag2 1 u1).
      split.
      {
        unfold WF_Unitary.
        split.
        {
          apply WF_diag2.
        }
        {
          lma'.
          solve_WF_matrix.
          apply WF_diag2.
          apply WF_diag2.
          unfold diag2, I, adjoint, Mmult; simpl.
          Csimpl.
          rewrite <- Cmod_sqr.
          rewrite unit_u0.
          lca.
        }
      }
      split.
      {
        unfold WF_Unitary.
        split.
        {
          apply WF_diag2.
        }
        {
          lma'.
          solve_WF_matrix.
          apply WF_diag2.
          apply WF_diag2.
          unfold diag2, I, adjoint, Mmult; simpl.
          Csimpl.
          rewrite <- Cmod_sqr.
          rewrite unit_u1.
          lca.
        }
      }
      exists C1, u0, C1, u1.
      exists ∣0⟩, ∣1⟩, ∣0⟩, ∣1⟩.
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
        apply diag2_eigenpairs.
      }
      split.
      {
        apply diag2_eigenpairs.
      }
      split.
      {
        apply diag2_eigenpairs.
      }
      split.
      {
        apply diag2_eigenpairs.
      }
      right.
      split.
      {
        lma'.
        solve_WF_matrix.
        apply WF_diag2.
        apply WF_diag2.
        solve_WF_matrix.
      }
      split.
      {
        lma'.
        solve_WF_matrix.
        apply WF_diag2.
        apply WF_diag2.
        solve_WF_matrix.
        unfold scale, Mmult, kron, diag2, I, qubit0, qubit1; simpl.
        lca.
      }
      split.
      {
        lma'.
        solve_WF_matrix.
        apply WF_diag2.
        apply WF_diag2.
        solve_WF_matrix.
        unfold scale, Mmult, kron, diag2, I, qubit0, qubit1; simpl.
        lca.
      }
      {
        lma'.
        solve_WF_matrix.
        apply WF_diag2.
        apply WF_diag2.
        solve_WF_matrix.
        unfold scale, Mmult, kron, diag2, I, qubit0, qubit1; simpl.
        rewrite H.
        lca.
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
