Require Import Proof.UnitaryMatrices.
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
    exists (P0 P1 : Square 2),
      WF_Unitary P0 -> WF_Unitary P1 ->
      I 2 ⊗ I 2 ⊗ beta ⊗ beta† .+ P0 ⊗ P1 ⊗ beta_perp ⊗ beta_perp† = control (control (list2D_to_matrix [[u0; C0]; [C0; u1]]))
      <-> u0 = 1 /\ u1 = 1.
Proof.
  intros.
  exists (I 2), (I 2).
  intros _ _.
  assert (WF_Q : WF_Matrix Q).
  {
    unfold WF_Unitary in H1.
    destruct H1.
    assumption.
  }
  assert (WF_beta : WF_Matrix beta).
  {
    unfold beta.
    apply WF_mult.
    exact WF_Q.
    exact WF_qubit0.
  }
  assert (WF_beta_perp : WF_Matrix beta_perp).
  {
    unfold beta.
    apply WF_mult.
    exact WF_Q.
    exact WF_qubit1.
  }
  pose (a := beta 0%nat 0%nat).
  pose (b := beta 1%nat 0%nat).
  split.
  - destruct (Ceq_dec a C0) as [a_zero | a_nonzero].
    + assert (unit_b : b^* * b = 1).
      {
        unfold WF_Unitary in H1.
        destruct H1.
        apply (f_equal (fun f => f 0%nat 0%nat)) in H2.
        unfold Mmult in H2.
        unfold adjoint in H2.
        unfold I in H2.
        simpl in H2.
        replace (Q 0%nat 0%nat) with a in H2 by lca.
        replace (Q 1%nat 0%nat) with b in H2 by lca.
        rewrite a_zero in H2.
        rewrite Cmult_0_r in H2.
        repeat rewrite Cplus_0_l in H2.
        assumption.
      }
      assert (bmult_1_1 : beta × beta† = ∣1⟩⟨1∣).
      {
        lma'.
        unfold beta, adjoint, qubit0, qubit1, Mmult.
        simpl.
        replace (Q 0%nat 0%nat) with a by lca.
        rewrite a_zero.
        repeat rewrite Cmult_0_r.
        lca.
        unfold beta, adjoint, qubit0, qubit1, Mmult.
        simpl.
        replace (Q 0%nat 0%nat) with a by lca.
        rewrite a_zero.
        repeat rewrite Cmult_0_r.
        lca.
        unfold beta, adjoint, qubit0, qubit1, Mmult.
        simpl.
        replace (Q 0%nat 0%nat) with a by lca.
        rewrite a_zero.
        repeat rewrite Cmult_0_r.
        lca.
        unfold beta, adjoint, qubit0, qubit1, Mmult.
        simpl.
        replace (Q 1%nat 0%nat) with b by lca.
        repeat rewrite Cmult_0_l.
        repeat rewrite Cmult_0_r.
        repeat rewrite Cplus_0_l.
        repeat rewrite Cplus_0_r.
        repeat rewrite Cmult_1_l.
        repeat rewrite Cmult_1_r.
        rewrite Cmult_comm.
        rewrite unit_b.
        lca.
      }
      pose proof (a8 Q H1) as H2.
      replace (Q × ∣0⟩) with beta in H2 by reflexivity.
      replace (Q × ∣1⟩) with beta_perp in H2 by reflexivity.
      rewrite bmult_1_1 in H2.
      assert (H3 : beta_perp × (beta_perp) † = ∣0⟩⟨0∣).
      {
        rewrite <- Mplus01 in H2.
        rewrite Mplus_comm in H2.
        apply Mplus_cancel_r with (C := ∣1⟩⟨1∣).
        assumption.
      }
      (* TODO: Finish this section! *)
    + destruct (Ceq_dec b C0) as [b_zero | b_nonzero].
      * assumption.
      * 
  - intros.
    destruct H2.
    (* TODO: Finish this proof! *)
Qed.
