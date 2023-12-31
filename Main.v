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

Lemma Mplus_cancel_l : forall {m n} (A B C : Matrix m n),
  A .+ B = A .+ C -> B = C.
Proof.
  intros.
  apply (f_equal (fun f => Mopp A .+ f)) in H.
  rewrite <- Mscale_1_l with (A := A) in H at 2 4.
  unfold Mopp in H.
  repeat rewrite Mplus_assoc in H.
  repeat rewrite <- Mplus_assoc in H.
  rewrite <- Mscale_plus_distr_l with (A := A) in H.
  rewrite Cplus_opp_l in H.
  rewrite Mscale_0_l in H.
  repeat rewrite Mplus_0_l in H.
  exact H.
Qed.

Lemma Mplus_cancel_r : forall {m n} (A B C : Matrix m n),
  A .+ C = B .+ C -> A = B.
Proof.
  intros.
  apply (f_equal (fun f => f .+ Mopp C)) in H.
  rewrite <- Mscale_1_l with (A := C) in H at 1 3.
  unfold Mopp in H.
  repeat rewrite Mplus_assoc in H.
  rewrite <- Mscale_plus_distr_l with (A := C) in H.
  rewrite Cplus_opp_r in H.
  rewrite Mscale_0_l in H.
  repeat rewrite Mplus_0_r in H.
  exact H.
Qed.

Lemma m4_2 : forall (u0 u1 : C),
  Cmod u0 = 1 -> Cmod u1 = 1 ->
  forall (Q : Square 2),
    WF_Unitary Q ->
    let beta : Vector 2 := Q × ∣0⟩ in
    let beta_perp := Q × ∣1⟩ in
    (exists (P0 P1 : Square 2),
    WF_Unitary P0 -> WF_Unitary P1 ->
    I 2 ⊗ I 2 ⊗ (beta × beta†) .+ P0 ⊗ P1 ⊗ (beta_perp × beta_perp†) = ccu (diag2 u0 u1))
      <-> u0 = 1 /\ u1 = 1.
Proof.
  intros.
  assert (WF_Q : WF_Matrix Q).
  {
    unfold WF_Unitary in H1.
    destruct H1.
    assumption.
  }
  assert (WF_beta : WF_Matrix beta) by solve_WF_matrix.
  assert (WF_beta_perp : WF_Matrix beta_perp) by solve_WF_matrix.
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
        rewrite a_zero in H3.
        rewrite Cmult_0_r in H3.
        repeat rewrite Cplus_0_l in H3.
        assumption.
      }
      assert (beta_mult_1_1 : beta × beta† = ∣1⟩⟨1∣).
      {
        lma'.
        unfold beta, adjoint, qubit0, qubit1, Mmult.
        simpl.
        replace (Q 0%nat 0%nat) with a by lca.
        rewrite a_zero.
        lca.
        unfold beta, adjoint, qubit0, qubit1, Mmult.
        simpl.
        replace (Q 0%nat 0%nat) with a by lca.
        rewrite a_zero.
        lca.
        unfold beta, adjoint, qubit0, qubit1, Mmult.
        simpl.
        replace (Q 0%nat 0%nat) with a by lca.
        rewrite a_zero.
        lca.
        unfold beta, adjoint, qubit0, qubit1, Mmult.
        simpl.
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
          rewrite b_zero in H3.
          rewrite Cmult_0_r in H3.
          rewrite Cplus_0_l in H3.
          rewrite Cplus_0_r in H3.
          assumption.
        }
        assert (beta_mult_0_0 : beta × beta† = ∣0⟩⟨0∣).
        {
          lma'.
          unfold beta, adjoint, qubit0, qubit1, Mmult.
          simpl.
          replace (Q 0%nat 0%nat) with a by lca.
          rewrite Cmult_0_r.
          repeat rewrite Cplus_0_l.
          rewrite Cplus_0_r.
          rewrite Cmult_1_r.
          rewrite Cmult_comm.
          rewrite unit_a.
          lca.
          unfold beta, adjoint, qubit0, qubit1, Mmult.
          simpl.
          replace (Q 1%nat 0%nat) with b by lca.
          rewrite b_zero.
          lca.
          unfold beta, adjoint, qubit0, qubit1, Mmult.
          simpl.
          replace (Q 1%nat 0%nat) with b by lca.
          rewrite b_zero.
          lca.
          unfold beta, adjoint, qubit0, qubit1, Mmult.
          simpl.
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
        admit. (* TODO: Eigenvalues! *)
      * admit. (* TODO: a <> 0 /\ b <> 0 case! *)
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
