Require Import Proof.UnitaryMatrices.
Require Import Proof.MatrixHelpers.
Require Import Proof.GateHelpers.
Require Import QuantumLib.Complex.
Require Import QuantumLib.Quantum.
Require Import QuantumLib.Eigenvectors.
Require Import QuantumLib.Matrix.

(* Lemma 3_2 : forall (u0 u1 : C),
  Cmod u0 = 1 -> Cmod u1 = 1 ->
  exists (P Q : Square 2),
    WF_Unitary P -> WF_Unitary Q -> *)

Definition Csqrt (x : C) : C :=
  let norm := Cmod x in
  match x with
  | (a, b) => (sqrt ((norm + a) / 2), sqrt ((norm - a) / 2))
  end.

Definition get_eigenvalues (A : Square 2) : list C :=
  let a := A 0%nat 0%nat in
  let b := A 0%nat 1%nat in
  let c := A 1%nat 0%nat in
  let d := A 1%nat 1%nat in
  let discriminant := (a + d)^2 - (4 * (a * d - b * c)) in
  let lambda1 := (((a + d) + Csqrt discriminant) / 2)%C in
  let lambda2 := (((a + d) - Csqrt discriminant) / 2)%C in
  [lambda1; lambda2].

Lemma eigenvalues_are_eigenvalues : forall (A : Square 2),
  WF_Matrix A ->
  forall (lambda : C), In lambda (get_eigenvalues A) -> 
    exists (v : Vector 2), Eigenpair A (v, lambda).
Proof.
  intros A WF_A lambda In_lambda.
  unfold get_eigenvalues in In_lambda.
  simpl in In_lambda.
  destruct In_lambda as [lambda1 | lambda2].
  - exists (∣0⟩).
    unfold Eigenpair.
Admitted.

Lemma m4_2 : forall (u0 u1 : C),
  Cmod u0 = 1 -> Cmod u1 = 1 ->
  forall (Q : Square 2),
    WF_Unitary Q ->
    let beta : Vector 2 := Q × ∣0⟩ in
    let beta_perp := Q × ∣1⟩ in
    (exists (P0 P1 : Square 2),
      WF_Unitary P0 /\
      WF_Unitary P1 /\
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
      admit. (* TODO: Eigenvalues! *)
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
        admit. (* TODO: Eigenvalues! *)
      * destruct H2 as [P0 [P1 [WF_P0 [WF_P1 H2]]]].
        apply (f_equal (fun f => f × (∣1⟩ ⊗ ∣1⟩ ⊗ beta))) in H2.
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
          intro absurd.
          apply (f_equal (fun f => f 3%nat 0%nat)) in absurd.
          unfold qubit1, Mmult, Zero in absurd.
          revert absurd; compute; intro absurd.
          replace ((R1 * R1 + - (R0 * R0))%R, (R1 * R0 + R0 * R1)%R) with C1 in absurd by lca.
          contradict absurd.
          apply C1_neq_C0.
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
    destruct H2.
    exists (I 2), (I 2).
    split.
    + exact (@id_unitary 2).
    + split.
      * exact (@id_unitary 2).
      * rewrite <- kron_plus_distr_l.
        unfold beta, beta_perp, ccu.
        rewrite a8. 2: assumption.
        rewrite H2, H3.
        lma'.
        apply WF_control with (n := 4%nat).
        apply WF_control with (n := 2%nat).
        apply WF_diag2.
Qed.
