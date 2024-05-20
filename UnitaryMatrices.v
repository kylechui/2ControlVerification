Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.
Require Import QuantumLib.Eigenvectors.
Require Import QuantumLib.Permutations.
From Proof Require Import MatrixHelpers.
From Proof Require Import PartialTraceDefinitions.
From Proof Require Import AlgebraHelpers.
From Proof Require Import SquareMatrices.
From Proof Require Import Permutations.
From Proof Require Import WFHelpers.
Require Import List.
Import ListNotations.

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

Lemma a5_left: forall {n} (P Q: Square n),
  WF_Unitary P -> WF_Unitary Q ->
  forall (a p: C) (psi phi: Vector n),
    WF_Matrix psi -> WF_Matrix phi ->
    Eigenpair P (psi, a) -> Eigenpair Q (phi, p) ->
    Eigenpair (P ⊗ Q) (psi ⊗ phi, a * p).
Proof.
intros.
unfold Eigenpair in *; simpl in *.
assert (Step1: P ⊗ Q × (psi ⊗ phi) = (P × psi) ⊗ (Q × phi)).
{
    apply kron_mixed_product.
}
rewrite Step1 at 1. clear Step1.
rewrite H3.
rewrite H4.
rewrite Mscale_kron_dist_r.
rewrite Mscale_kron_dist_l.
rewrite Mscale_assoc.
rewrite Cmult_comm.
reflexivity.
Qed.

(* Invalid argument until number of eigenvalues is adressed
    TODO: finish once spectral thm application is figured out
*)
(* Lemma a5_right: forall {n} (psi phi: Vector n) (a p: C) (P Q: Square n),
    WF_Matrix psi -> WF_Matrix phi -> WF_Unitary P -> WF_Unitary Q ->
    Eigenpair (P ⊗ Q) (psi ⊗ phi, a * p) -> Eigenpair P (psi, a) /\ Eigenpair Q (phi, p).
Proof.
intros.
unfold Eigenpair in *; simpl in *.
revert H3.
assert (Step1: P ⊗ Q × (psi ⊗ phi) = (P × psi) ⊗ (Q × phi)).
{
    apply kron_mixed_product.
}
rewrite Step1 at 1. clear Step1.
rewrite <- Mscale_assoc.
assert (Step2: a .* (p .* (psi ⊗ phi)) = (a .* psi) ⊗ (p .* phi)).
{
 rewrite <- Mscale_kron_dist_r.
 rewrite <- Mscale_kron_dist_l.
 reflexivity.
}
rewrite Step2 at 1. clear Step2.
rewrite <- kron_simplify.
intros H3.
rewrite <- Mscale_kron_dist_r in H3.
rewrite <- Mscale_kron_dist_l at 2.



intros H3.
rewrite kron_mixed_product' in H3. *)

Lemma direct_sum_unitary : forall {n : nat} (P Q : Square n),
  WF_Unitary P -> WF_Unitary Q -> WF_Unitary (P .⊕ Q).
Proof.
  intros n P Q [WF_P Unitary_P] [WF_Q Unitary_Q].
  unfold WF_Unitary.
  split; try apply WF_direct_sum; auto.
  repeat rewrite direct_sum_decomp; auto.
  replace (n + n)%nat with (2 * n)%nat by lia.
  rewrite Mplus_adjoint.
  repeat rewrite Mmult_plus_distr_r.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite kron_adjoint.
  repeat rewrite kron_mixed_product.
  replace ∣0⟩⟨0∣† with ∣0⟩⟨0∣ by lma'.
  replace ∣1⟩⟨1∣† with ∣1⟩⟨1∣ by lma'.
  repeat rewrite cancel00; auto with wf_db.
  repeat rewrite cancel11; auto with wf_db.
  repeat rewrite cancel01; Msimpl_light.
  repeat rewrite cancel10; Msimpl_light.
  rewrite Unitary_P, Unitary_Q.
  rewrite <- kron_plus_distr_r.
  rewrite Mplus01.
  rewrite id_kron.
  reflexivity.
Qed.

Lemma direct_sum_diagonal : forall {n : nat} (P Q : Square n),
  WF_Diagonal P -> WF_Diagonal Q -> WF_Diagonal (P .⊕ Q).
Proof.
  intros n P Q [WF_P Diagonal_P] [WF_Q Diagonal_Q].
  split.
  {
    apply WF_direct_sum; try lia; assumption.
  }
  {
    intros i j i_neq_j.
    specialize (Diagonal_P i j i_neq_j).
    specialize (Diagonal_Q (i - n) (j - n))%nat.
    unfold direct_sum.
    destruct (i <? n) eqn:L1.
    {
      simpl; exact Diagonal_P.
    }
    {
      destruct (j <? n) eqn:L2.
      {
        simpl; exact Diagonal_P.
      }
      {
        apply Nat.ltb_ge in L1, L2.
        simpl; apply Diagonal_Q.
        intro in_eq_jn.
        apply i_neq_j.
        apply (f_equal (fun x => x + n)%nat) in in_eq_jn.
        do 2 rewrite Nat.sub_add in in_eq_jn; auto.
      }
    }
  }
Qed.

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
    apply  direct_sum_unitary; auto.
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

(* Attempting to prove equality using sets *)
Lemma a6_leftP: forall (c: C) (psi: Vector 2) (P Q: Square 2),
    WF_Unitary P -> WF_Unitary Q -> WF_Matrix psi ->
    Eigenpair P (psi,c) -> Eigenpair (∣0⟩⟨0∣ ⊗ P .+ ∣1⟩⟨1∣ ⊗ Q) ((∣0⟩⊗psi),c).
Proof.
intros.
unfold Eigenpair in *; simpl in *.
rewrite Mmult_plus_distr_r.
assert (Step1: ∣0⟩⟨0∣ ⊗ P × (∣0⟩ ⊗ psi) = c .* (∣0⟩ ⊗ psi)).
{
    rewrite kron_mixed_product.
    rewrite Mmult_assoc.
    rewrite Mmult00.
    rewrite Mmult_1_r.
    rewrite H2.
    rewrite Mscale_kron_dist_r.
    reflexivity.
    apply WF_qubit0.
}
rewrite Step1 at 1. clear Step1.
assert (Step2: ∣1⟩⟨1∣ ⊗ Q × (∣0⟩ ⊗ psi) = Zero).
{
    rewrite kron_mixed_product.
    rewrite Mmult_assoc.
    rewrite Mmult10.
    rewrite Mmult_0_r.
    rewrite kron_0_l.
    reflexivity.
}
rewrite Step2 at 1. clear Step2.
rewrite Mplus_0_r.
reflexivity.
Qed.

Lemma a6_leftQ: forall (c: C) (phi: Vector 2) (P Q: Square 2),
    WF_Unitary P -> WF_Unitary Q -> WF_Matrix phi ->
    Eigenpair Q (phi,c) -> Eigenpair (∣0⟩⟨0∣ ⊗ P .+ ∣1⟩⟨1∣ ⊗ Q) ((∣1⟩⊗phi),c).
Proof.
intros.
unfold Eigenpair in *; simpl in *.
rewrite Mmult_plus_distr_r.
assert (Step1: ∣0⟩⟨0∣ ⊗ P × (∣1⟩ ⊗ phi) = Zero).
{
    rewrite kron_mixed_product.
    rewrite Mmult_assoc.
    rewrite Mmult01.
    rewrite Mmult_0_r.
    rewrite kron_0_l.
    reflexivity.
}
rewrite Step1 at 1. clear Step1.
rewrite Mplus_0_l.
assert (Step2: ∣1⟩⟨1∣ ⊗ Q × (∣1⟩ ⊗ phi) = c .* (∣1⟩ ⊗ phi)).
{
    rewrite kron_mixed_product.
    rewrite Mmult_assoc.
    rewrite Mmult11.
    rewrite Mmult_1_r.
    rewrite H2.
    rewrite Mscale_kron_dist_r.
    reflexivity.
    apply WF_qubit1.
}
apply Step2.
Qed.

Lemma a6_left: forall (c: C) (phi psi: Vector 2) (P Q: Square 2),
WF_Unitary P -> WF_Unitary Q -> WF_Matrix psi -> WF_Matrix phi ->
(Eigenpair P (psi,c) \/ Eigenpair Q (phi,c)) ->
(Eigenpair (∣0⟩⟨0∣ ⊗ P .+ ∣1⟩⟨1∣ ⊗ Q) ((∣0⟩⊗psi),c) \/ Eigenpair (∣0⟩⟨0∣ ⊗ P .+ ∣1⟩⟨1∣ ⊗ Q) ((∣1⟩⊗phi),c)).
Proof.
intros.
destruct H3.
{
 left.
 apply a6_leftP.
 apply H.
 apply H0.
 apply H1.
 apply H3.
}
{
 right.
 apply a6_leftQ.
 apply H.
 apply H0.
 apply H2.
 apply H3.
}
Qed.

Lemma a6_rightP: forall (c: C) (psi: Vector 2) (P Q: Square 2),
WF_Unitary P -> WF_Unitary Q -> WF_Matrix psi ->
Eigenpair (∣0⟩⟨0∣ ⊗ P .+ ∣1⟩⟨1∣ ⊗ Q) ((∣0⟩⊗psi),c) -> Eigenpair P (psi,c).
intros.
unfold Eigenpair in *; simpl in *.
revert H2.
rewrite Mmult_plus_distr_r.
assert (Step1: ∣1⟩⟨1∣ ⊗ Q × (∣0⟩ ⊗ psi) = Zero).
{
    rewrite kron_mixed_product.
    rewrite Mmult_assoc.
    rewrite Mmult10.
    rewrite Mmult_0_r.
    rewrite kron_0_l.
    reflexivity.
}
rewrite Step1 at 1. clear Step1.
rewrite Mplus_0_r.
assert (Step2: ∣0⟩⟨0∣ ⊗ P × (∣0⟩ ⊗ psi) = ∣0⟩⊗ (P× psi)).
{
    rewrite kron_mixed_product.
    rewrite Mmult_assoc.
    rewrite Mmult00.
    rewrite Mmult_1_r.
    reflexivity.
    apply WF_qubit0.
}
rewrite Step2 at 1. clear Step2.
assert (Step3: c .* (∣0⟩ ⊗ psi) =  ∣0⟩ ⊗ (c .* psi)).
{
    rewrite Mscale_kron_dist_r.
    reflexivity.
}
rewrite Step3 at 1. clear Step3.
set (B:= P × psi ).
set (C:=c .* psi).
apply kron_0_cancel_l.
{
    apply WF_mult.
    destruct H as [H2 _].
    apply H2.
    apply H1.
}
{
    apply WF_scale.
    apply H1.
}
Qed.

Lemma a6_rightQ: forall (c: C) (phi: Vector 2) (P Q: Square 2),
WF_Unitary P -> WF_Unitary Q -> WF_Matrix phi ->
Eigenpair (∣0⟩⟨0∣ ⊗ P .+ ∣1⟩⟨1∣ ⊗ Q) ((∣1⟩⊗phi),c) -> Eigenpair Q (phi,c).
intros.
unfold Eigenpair in *; simpl in *.
revert H2.
rewrite Mmult_plus_distr_r.
assert (Step1: ∣0⟩⟨0∣ ⊗ P × (∣1⟩ ⊗ phi) = Zero).
{
    rewrite kron_mixed_product.
    rewrite Mmult_assoc.
    rewrite Mmult01.
    rewrite Mmult_0_r.
    rewrite kron_0_l.
    reflexivity.
}
rewrite Step1 at 1. clear Step1.
rewrite Mplus_0_l.
assert (Step2: ∣1⟩⟨1∣ ⊗ Q × (∣1⟩ ⊗ phi) = ∣1⟩⊗ (Q× phi)).
{
    rewrite kron_mixed_product.
    rewrite Mmult_assoc.
    rewrite Mmult11.
    rewrite Mmult_1_r.
    reflexivity.
    apply WF_qubit1.
}
rewrite Step2 at 1. clear Step2.
assert (Step3: c .* (∣1⟩ ⊗ phi) =  ∣1⟩ ⊗ (c .* phi)).
{
    rewrite Mscale_kron_dist_r.
    reflexivity.
}
rewrite Step3 at 1. clear Step3.
set (B:= Q × phi ).
set (C:=c .* phi).
apply kron_1_cancel_l.
{
    apply WF_mult.
    destruct H0 as [H2 _].
    apply H2.
    apply H1.
}
{
    apply WF_scale.
    apply H1.   
}
Qed.

Lemma a6_right: forall (c: C) (phi psi: Vector 2) (P Q: Square 2),
WF_Unitary P -> WF_Unitary Q -> WF_Matrix psi -> WF_Matrix phi ->
(Eigenpair (∣0⟩⟨0∣ ⊗ P .+ ∣1⟩⟨1∣ ⊗ Q) ((∣0⟩⊗psi),c) \/ Eigenpair (∣0⟩⟨0∣ ⊗ P .+ ∣1⟩⟨1∣ ⊗ Q) ((∣1⟩⊗phi),c))
-> (Eigenpair P (psi,c) \/ Eigenpair Q (phi,c)).
Proof.
intros.
destruct H3.
{
 left.
 revert H3.
 apply a6_rightP.
 apply H.
 apply H0.
 apply H1.
}
{
 right.
 revert H3.
 apply a6_rightQ.
 apply H.
 apply H0.
 apply H2.
}
Qed.

Lemma a7_2q_a : forall (P : Square 2) (Q: Square 2),
    WF_Matrix Q ->
    partial_trace_2q_a (P ⊗ Q) = (trace P) .* Q.
Proof.
intros.
lma'.
apply WF_partial_trace_2q_a.
Qed.

Lemma a7_2q_b : forall (P : Square 2) (Q: Square 2),
    WF_Matrix P ->
    partial_trace_2q_b (P ⊗ Q) = (trace Q) .* P.
Proof.
intros.
lma'.
apply WF_partial_trace_2q_b.
Qed.

Lemma a7_3q_a : forall (A: Square 2) (B: Square 4),
    WF_Matrix B ->
    partial_trace_3q_a (A ⊗ B) = (trace A) .* (B).
Proof.
intros.
lma'.
apply WF_partial_trace_3q_a.
Qed.

Lemma a7_3q_c : forall (A: Square 4) (B: Square 2),
    WF_Matrix A ->
    partial_trace_3q_c (A ⊗ B) = (trace B) .* (A).
Proof.
intros.
lma'.
apply WF_partial_trace_3q_c.
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
  assert (Q_adjoint_unitary : WF_Unitary (Q†)).
  {
    apply adjoint_unitary.
    assumption.
  }
  destruct Q_adjoint_unitary.
  rewrite adjoint_involutive in H1.
  assumption.
  apply adjoint_unitary.
  assumption.
Qed.

Lemma a9_right: forall (V : Square 4) (P00 P01 P10 P11 : Square 2),
WF_Unitary V -> WF_Matrix P00 -> WF_Matrix P01 -> WF_Matrix P10 -> WF_Matrix P11 ->
V = ∣0⟩⟨0∣ ⊗ P00 .+ ∣0⟩⟨1∣ ⊗ P01 .+ ∣1⟩⟨0∣ ⊗ P10 .+ ∣1⟩⟨1∣ ⊗ P11 ->
P01 = Zero -> P10 = Zero.
Proof.
intros V P00 P01 P10 P11 V_unitary WF_P00 WF_P01 WF_P10 WF_P11 V_def P01_Zero.
assert (Vblock_adjoint : (∣0⟩⟨0∣ ⊗ P00 .+ ∣0⟩⟨1∣ ⊗ P01 .+ ∣1⟩⟨0∣ ⊗ P10 .+ ∣1⟩⟨1∣ ⊗ P11) † =
    ∣0⟩⟨0∣ ⊗ P00† .+ ∣0⟩⟨1∣ ⊗ P10† .+ ∣1⟩⟨0∣ ⊗ P01† .+ ∣1⟩⟨1∣ ⊗ P11† ). lma.
assert (rl_mult: V × V† = ∣0⟩⟨0∣ ⊗ (P00 × (P00) †) .+ ∣0⟩⟨1∣ ⊗ (P00 × (P10) †)
    .+ ∣1⟩⟨0∣ ⊗ (P10 × (P00) †) .+ ∣1⟩⟨1∣ ⊗ (P10 × (P10) † .+ P11 × (P11) †)).
{
    rewrite V_def.
    rewrite Vblock_adjoint at 1.
    rewrite (@block_multiply 2) with (Q00 := (P00) †) (Q01 := P10†) (Q10 := P01†) (Q11 := (P11) †)
    (P00 := (P00)) (P01 := (P01)) (P10 := (P10)) (P11 := (P11)).
    all: solve_WF_matrix.
    rewrite P01_Zero; Msimpl_light; reflexivity.
}
assert (lr_mult: V† × V = ∣0⟩⟨0∣ ⊗ ((P00) † × P00 .+ (P10) † × P10) .+ ∣0⟩⟨1∣ ⊗ ((P10) † × P11)
    .+ ∣1⟩⟨0∣ ⊗ ((P11) † × P10) .+ ∣1⟩⟨1∣ ⊗ ((P11) † × P11)).
{
    rewrite V_def.
    rewrite Vblock_adjoint at 1.
    rewrite (@block_multiply 2) with (P00 := (P00) †) (P01 := P10†) (P10 := P01†) (P11 := (P11) †)
    (Q00 := (P00)) (Q01 := (P01)) (Q10 := (P10)) (Q11 := (P11)).
    2,3,4,5,6,7,8,9,10,11: solve_WF_matrix.
    rewrite P01_Zero; Msimpl_light; reflexivity.
}
clear V_def P01_Zero Vblock_adjoint.
assert (Vadj_unitary: WF_Unitary V†).
{
    apply adjoint_unitary. apply V_unitary.
}
assert (block_decomp: ∣0⟩⟨0∣ ⊗ (P00 × P00†) .+ ∣0⟩⟨1∣ ⊗ (P00× P10†) .+ ∣1⟩⟨0∣ ⊗ (P10× P00†) .+ ∣1⟩⟨1∣ ⊗ (P10× P10† .+ P11× P11†)
= ∣0⟩⟨0∣ ⊗ (P00† × P00 .+ P10† × P10) .+ ∣0⟩⟨1∣ ⊗ (P10† × P11) .+ ∣1⟩⟨0∣ ⊗ (P11† × P10) .+ ∣1⟩⟨1∣ ⊗ (P11† × P11)).
{
    rewrite <- lr_mult.
    rewrite <- rl_mult.
    destruct V_unitary as [_ Vmult_id]. rewrite Vmult_id.
    destruct Vadj_unitary as [_ Vadjmult_id]. rewrite adjoint_involutive in Vadjmult_id.
    rewrite Vadjmult_id. reflexivity.
}
clear V_unitary Vadj_unitary lr_mult rl_mult.
assert (P00_decomp: P00 × P00† = P00† × P00 .+ P10† × P10).
{
    apply block_equalities with (P00:= P00 × (P00) †) (P01 := P00 × (P10) †) (P10:= P10 × (P00) †) (P11 := P10 × (P10) † .+ P11 × (P11) †)
    (Q00:= (P00) † × P00 .+ (P10) † × P10) (Q01 := (P10) † × P11) (Q10:= (P11) † × P10) (Q11 := (P11) † × P11) in block_decomp.
    2: lia.
    all: solve_WF_matrix.
    destruct block_decomp as [first_block _].
    apply first_block.
}
clear block_decomp WF_P00 WF_P01 WF_P11.
assert (tr_inner_sum: trace (P00 × P00†) = trace (P00† × P00 .+ P10† × P10)).
{
    rewrite P00_decomp.
    reflexivity.
}
clear P00_decomp.
assert (tr_sum: trace (P00 × P00†) = trace (P00 × P00†) + trace(P10 † × P10)).
{
    rewrite a2 at 2.
    rewrite <- trace_plus_dist.
    apply tr_inner_sum.
}
clear tr_inner_sum.
assert (tr_0: trace (P10† × P10) = 0).
{
    apply Cplus_cancel_l with (a:=trace (P00 × (P00) †)).
    symmetry.
    rewrite Cplus_0_r.
    apply tr_sum.
}
clear tr_sum.
assert (tr_def: trace (P10† × P10) = (P10 0%nat 0%nat) ^* * P10 0%nat 0%nat + (P10 0%nat 1%nat) ^* * P10 0%nat 1%nat +
    (P10 1%nat 0%nat) ^* * P10 1%nat 0%nat + (P10 1%nat 1%nat) ^* * P10 1%nat 1%nat). lca.
assert (all_0: (P10 0%nat 0%nat = 0 /\ P10 0%nat 1%nat = 0 /\ P10 1%nat 0%nat = 0 /\ P10 1%nat 1%nat = 0)%C).
{
    apply sum_of_squared_norms_eq_0_implies_0.
    rewrite <- tr_def.
    apply tr_0.
}
clear tr_def tr_0. 
lma'.
apply all_0. apply all_0. apply all_0. apply all_0.
Qed.

Lemma a9_left: forall (V : Square 4) (P00 P01 P10 P11 : Square 2),
WF_Unitary V -> WF_Matrix P00 -> WF_Matrix P01 -> WF_Matrix P10 -> WF_Matrix P11 ->
V = ∣0⟩⟨0∣ ⊗ P00 .+ ∣0⟩⟨1∣ ⊗ P01 .+ ∣1⟩⟨0∣ ⊗ P10 .+ ∣1⟩⟨1∣ ⊗ P11 ->
P10 = Zero -> P01 = Zero.
Proof.
intros V P00 P01 P10 P11 V_unitary WF_P00 WF_P01 WF_P10 WF_P11 V_def P10_Zero.
rewrite <- adjoint_involutive at 1. rewrite <- adjoint_involutive.
apply Madjoint_simplify.
rewrite zero_adjoint_eq.
assert (P10_adj_zero: P10 † = Zero).
{
    rewrite P10_Zero.
    rewrite zero_adjoint_eq. 
    reflexivity.
}
apply a9_right with (V := V†) (P00 := P00 †) (P01 := P10 †) (P10 := P01 †) (P11 := P11 †).
7: apply P10_adj_zero. 6: trivial. 5: solve_WF_matrix. 4: solve_WF_matrix. 3: solve_WF_matrix. 2: solve_WF_matrix.
apply adjoint_unitary.
apply V_unitary.
rewrite V_def. lma.
Qed.

Lemma a9: forall (V : Square 4) (P00 P01 P10 P11 : Square 2),
WF_Unitary V -> WF_Matrix P00 -> WF_Matrix P01 -> WF_Matrix P10 -> WF_Matrix P11 ->
V = ∣0⟩⟨0∣ ⊗ P00 .+ ∣0⟩⟨1∣ ⊗ P01 .+ ∣1⟩⟨0∣ ⊗ P10 .+ ∣1⟩⟨1∣ ⊗ P11 ->
P01 = Zero <-> P10 = Zero.
Proof.
split.
{
    intros.
    apply a9_right with (V:= V) (P00 := P00) (P01 := P01) (P10 := P10) (P11 := P11).
    apply H. apply H0. apply H1. apply H2. apply H3. apply H4. apply H5.
}
{
    intros.
    apply a9_left with (V:= V) (P00 := P00) (P01 := P01) (P10 := P10) (P11 := P11).
    apply H. apply H0. apply H1. apply H2. apply H3. apply H4. apply H5.
}
Qed.
