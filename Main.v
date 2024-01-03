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
        replace (Q 0%nat 0%nat) with a by lca.
        rewrite a_zero.
        lca.
        replace (Q 0%nat 0%nat) with a by lca.
        rewrite a_zero.
        lca.
        replace (Q 0%nat 0%nat) with a by lca.
        rewrite a_zero.
        lca.
        replace (Q 1%nat 0%nat) with b by lca.
        rewrite Cmult_0_r.
        repeat rewrite Cplus_0_l.
        rewrite Cplus_0_r.
        rewrite Cmult_1_r.
        rewrite Cmult_comm.
        rewrite unit_b.
        lca.
      }
      assert (beta_perp_mult_0_0 : beta_perp × (beta_perp) † = ∣0⟩⟨0∣).
      {
        pose proof (a8 Q H1) as H3.
        replace (Q × ∣0⟩) with beta in H3 by reflexivity.
        replace (Q × ∣1⟩) with beta_perp in H3 by reflexivity.
        rewrite beta_mult_1_1 in H3.
        rewrite <- Mplus10 in H3.
        apply Mplus_cancel_l in H3.
        assumption.
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
          replace (Q 0%nat 0%nat) with a by lca.
          rewrite Cmult_0_r.
          repeat rewrite Cplus_0_l.
          rewrite Cplus_0_r.
          rewrite Cmult_1_r.
          rewrite Cmult_comm.
          rewrite unit_a.
          lca.
          replace (Q 1%nat 0%nat) with b by lca.
          rewrite b_zero.
          lca.
          replace (Q 1%nat 0%nat) with b by lca.
          rewrite b_zero.
          lca.
          replace (Q 1%nat 0%nat) with b by lca.
          rewrite b_zero.
          lca.
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
        assert (perp_inner_prod_0 : ⟨beta, beta_perp⟩ = C0).
        {
          unfold inner_product, beta_perp, beta.
          rewrite Mmult_adjoint.
          rewrite <- Mmult_assoc.
          rewrite Mmult_assoc with (A := ⟨0∣).
          destruct H1.
          rewrite H3.
          rewrite Mmult_1_r. 2: apply (WF_bra 0).
          rewrite Mmult01.
          unfold Zero; simpl.
          reflexivity.
        }
        rewrite Mmult_plus_distr_r in H2.
        assert (step1 : I 2 ⊗ I 2 ⊗ (beta × (beta) †) × (∣1⟩ ⊗ ∣1⟩ ⊗ beta) = ∣1⟩ ⊗ ∣1⟩ ⊗ beta).
        {}
        assert (step2 : P0 ⊗ P1 ⊗ (beta_perp × (beta_perp) †) × (∣1⟩ ⊗ ∣1⟩ ⊗ beta) = Zero). {}
        rewrite step1, step2 in H2; clear step1 step2.
        rewrite Mplus_0_r in H2.
        assert (step3 : ccu (diag2 u0 u1) × (∣1⟩ ⊗ ∣1⟩ ⊗ beta) = ∣1⟩ ⊗ ∣1⟩ ⊗ (diag2 u0 u1 × beta)). {}
        rewrite step3 in H2 at 1; clear step3.
        do 2 rewrite kron_assoc in H2.
        do 2 apply kron_1_cancel_l in H2.
        assert (u0_is_1 : u0 = C1).
        {
          apply (f_equal (fun f => f 0%nat 0%nat)) in H2.
          unfold diag2, Mmult in H2; simpl in H2.
          replace (beta 0%nat 0%nat) with a in H2 by reflexivity.
          rewrite Cmult_0_l in H2.
          rewrite Cplus_0_l in H2.
          rewrite Cplus_0_r in H2.
          apply Cmult_cancel_r with (a := a).
          exact a_nonzero.
          rewrite <- H2.
          rewrite Cmult_1_l.
          reflexivity.
        }
        assert (u1_is_1 : u1 = C1).
        {
          apply (f_equal (fun f => f 1%nat 0%nat)) in H2.
          unfold diag2, Mmult in H2; simpl in H2.
          replace (beta 1%nat 0%nat) with b in H2 by reflexivity.
          rewrite Cmult_0_l in H2.
          repeat rewrite Cplus_0_l in H2.
          apply Cmult_cancel_r with (a := b).
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
    intros _ _.
    rewrite <- kron_plus_distr_l.
    unfold beta, beta_perp.
    rewrite a8. 2: assumption.
    rewrite H2, H3.
    lma'.
    apply WF_control with (n := 4%nat).
    apply WF_control with (n := 2%nat).
    show_wf.
Qed.
