Require Import QuantumLib.Matrix.
Require Import QuantumLib.Eigenvectors.
Require Import QuantumLib.Permutations.
Require Import WFHelpers.
Require Import MatrixHelpers.
Require Import UnitaryHelpers.
Require Import PartialTraceDefinitions.
Require Import AlgebraHelpers.
Require Import Permutations.
Require Import A1_SquareMatrices.

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
  rewrite (other_unitary_decomp Q H).
  reflexivity.
  solve_WF_matrix.
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
    destruct block_decomp as [first_block _].
    all: solve_WF_matrix.
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
