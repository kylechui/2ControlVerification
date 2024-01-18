Require Import QuantumLib.Quantum.
Require Import QuantumLib.Eigenvectors.
Require Import QuantumLib.Matrix.
From Proof Require Import MatrixHelpers.
From Proof Require Import PartialTraceDefinitions.
From Proof Require Import AlgebraHelpers.
From Proof Require Import SquareMatrices.
Require Import List.
Import ListNotations.

Theorem a3: forall {n} (A : Square n), WF_Unitary A -> WF_Diagonalizable A.
Proof.
  intros.
  apply unit_implies_diagble.
  apply H.
Qed.

Lemma a4: forall {n} (v: Vector n) (c: C) (U V : Square n),
    WF_Matrix v -> WF_Unitary U -> WF_Unitary V ->
    Eigenpair V (v, c) <-> Eigenpair (U × V × U†) (U × v, c).
Proof.
  (* TODO: Proof is adapted from QuantumLib.Eigenvectors to step through the proof. Replace with application.*)
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

Lemma a5_left: forall {n} (psi phi: Vector n) (a p: C) (P Q: Square n),
    WF_Matrix psi -> WF_Matrix phi -> WF_Unitary P -> WF_Unitary Q ->
    Eigenpair P (psi, a) -> Eigenpair Q (phi, p) -> Eigenpair (P ⊗ Q) (psi ⊗ phi, a * p).
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

Lemma a7_3q_a : forall (A B C: Square 2),
    WF_Matrix B -> WF_Matrix C ->
    partial_trace_3q_a (A ⊗ B ⊗ C) = (trace A) .* (B ⊗ C).
Proof.
intros.
lma'.
apply WF_partial_trace_3q_a.
Qed.

Lemma a7_3q_c : forall (A B C: Square 2),
    WF_Matrix A -> WF_Matrix B ->
    partial_trace_3q_c (A ⊗ B ⊗ C) = (trace C) .* (A ⊗ B).
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
    apply transpose_unitary.
    assumption.
  }
  destruct Q_adjoint_unitary.
  rewrite adjoint_involutive in H1.
  assumption.
  apply transpose_unitary.
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
    rewrite block_multiply with (Q00 := (P00) †) (Q01 := P10†) (Q10 := P01†) (Q11 := (P11) †)
    (P00 := (P00)) (P01 := (P01)) (P10 := (P10)) (P11 := (P11)).
    11: reflexivity. 10: reflexivity.
    9: solve_WF_matrix. 8: solve_WF_matrix. 7: solve_WF_matrix. 6: solve_WF_matrix.
    5: assumption. 4: assumption. 3: assumption. 2: assumption.
    rewrite P01_Zero. rewrite zero_adjoint_eq. repeat rewrite Mmult_0_l. repeat rewrite Mmult_0_r.
    repeat rewrite Mplus_0_r. reflexivity.
}
assert (lr_mult: V† × V = ∣0⟩⟨0∣ ⊗ ((P00) † × P00 .+ (P10) † × P10) .+ ∣0⟩⟨1∣ ⊗ ((P10) † × P11)
    .+ ∣1⟩⟨0∣ ⊗ ((P11) † × P10) .+ ∣1⟩⟨1∣ ⊗ ((P11) † × P11)).
{
    rewrite V_def.
    rewrite Vblock_adjoint at 1.
    rewrite block_multiply with (P00 := (P00) †) (P01 := P10†) (P10 := P01†) (P11 := (P11) †)
    (Q00 := (P00)) (Q01 := (P01)) (Q10 := (P10)) (Q11 := (P11)).
    11: reflexivity. 10: reflexivity.
    9: assumption. 8: assumption. 7: assumption. 6: assumption.
    5: solve_WF_matrix. 4: solve_WF_matrix. 3: solve_WF_matrix. 2: solve_WF_matrix.
    rewrite P01_Zero. rewrite zero_adjoint_eq.
    repeat rewrite Mmult_0_l. repeat rewrite Mmult_0_r.
    repeat rewrite Mplus_0_l. reflexivity.
}
clear V_def P01_Zero Vblock_adjoint.
assert (Vadj_unitary: WF_Unitary V†).
{
    apply transpose_unitary. apply V_unitary.
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
    11: reflexivity. 10: reflexivity.
    9: solve_WF_matrix. 8: solve_WF_matrix. 7: solve_WF_matrix. 6: solve_WF_matrix.
    5: solve_WF_matrix. 4: solve_WF_matrix. 3: solve_WF_matrix. 2: solve_WF_matrix.
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
apply transpose_unitary.
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
