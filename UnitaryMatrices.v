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
apply kron_0_vec2_equiv.
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
apply kron_1_vec2_equiv.
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
apply mat_equiv_eq.
apply WF_partial_trace_2q_a.
apply WF_scale.
apply H.
by_cell.
unfold partial_trace_2q_a; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_2q_a; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_2q_a; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_2q_a; unfold kron; unfold trace; unfold scale. lca.
Qed.

Lemma a7_3q_a : forall (A B C: Square 2),
    WF_Matrix B -> WF_Matrix C ->
    partial_trace_3q_a (A ⊗ B ⊗ C) = (trace A) .* (B ⊗ C).
Proof.
intros.
apply mat_equiv_eq.
apply WF_partial_trace_3q_a.
apply WF_scale.
apply WF_kron.
lia. lia.
apply H. apply H0.
by_cell.
unfold partial_trace_3q_a; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_3q_a; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_3q_a; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_3q_a; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_3q_a; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_3q_a; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_3q_a; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_3q_a; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_3q_a; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_3q_a; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_3q_a; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_3q_a; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_3q_a; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_3q_a; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_3q_a; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_3q_a; unfold kron; unfold trace; unfold scale. lca.
Qed.

Lemma a7_3q_c : forall (A B C: Square 2),
    WF_Matrix A -> WF_Matrix B ->
    partial_trace_3q_c (A ⊗ B ⊗ C) = (trace C) .* (A ⊗ B).
Proof.
intros.
apply mat_equiv_eq.
apply WF_partial_trace_3q_c.
apply WF_scale.
apply WF_kron.
lia. lia.
apply H. apply H0.
by_cell.
unfold partial_trace_3q_c; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_3q_c; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_3q_c; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_3q_c; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_3q_c; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_3q_c; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_3q_c; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_3q_c; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_3q_c; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_3q_c; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_3q_c; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_3q_c; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_3q_c; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_3q_c; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_3q_c; unfold kron; unfold trace; unfold scale. lca.
unfold partial_trace_3q_c; unfold kron; unfold trace; unfold scale. lca.
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
  assert (Step1 : ∣0⟩⟨0∣ .+ ∣1⟩⟨1∣ = I 2).
  {
    apply mat_equiv_eq.
    apply WF_plus.
    apply WF_braqubit0.
    apply WF_braqubit1.
    apply WF_I.
    by_cell.
    lca. lca. lca. lca.
  }
  rewrite Step1. clear Step1.
  rewrite Mmult_1_l.
  assert (Step2: WF_Unitary (Q†)).
  {
    apply transpose_unitary.
    apply H.
  }
  destruct Step2 as [Step2_1 Step2_2].
  rewrite adjoint_involutive in Step2_2.
  apply Step2_2.
  apply transpose_unitary.
  apply H.
Qed.

Lemma a9_right: forall (V : Square 4) (P00 P01 P10 P11 : Square 2),
WF_Unitary V -> WF_Matrix P00 -> WF_Matrix P01 -> WF_Matrix P10 -> WF_Matrix P11 ->
V = ∣0⟩⟨0∣ ⊗ P00 .+ ∣0⟩⟨1∣ ⊗ P01 .+ ∣1⟩⟨0∣ ⊗ P10 .+ ∣1⟩⟨1∣ ⊗ P11 ->
P01 = Zero -> P10 = Zero.
Proof.
intros.
cut (WF_Unitary V†).
intros.
apply mat_equiv_eq.
apply H2.
apply WF_Zero.
cut ((P10 0%nat 0%nat = 0 /\ P10 0%nat 1%nat = 0 /\ P10 1%nat 0%nat = 0 /\ P10 1%nat 1%nat = 0)%C).
intros.
by_cell.
apply H7. apply H7. apply H7. apply H7.
apply sum_of_squared_norms_eq_0_implies_0.
cut (trace (P10† × P10) = (P10 0%nat 0%nat) ^* * P10 0%nat 0%nat + (P10 0%nat 1%nat) ^* * P10 0%nat 1%nat +
(P10 1%nat 0%nat) ^* * P10 1%nat 0%nat + (P10 1%nat 1%nat) ^* * P10 1%nat 1%nat).
cut (trace (P10† × P10) = 0).
intros.
rewrite <- H8.
apply H7.
cut (trace (P00 × P00†) = trace (P00 × P00†) + trace(P10 † × P10)).
intros.
apply C_l_cancel with (a:=trace (P00 × (P00) †)).
symmetry.
rewrite Cplus_0_r.
apply H7.
rewrite a2 at 2.
rewrite <- trace_plus_dist.
cut (trace (P00 × P00†) = trace (P00† × P00 .+ P10† × P10)).
intros.
apply H7.
cut (P00 × P00† = P00† × P00 .+ P10† × P10).
intros.
rewrite H7.
reflexivity.
cut (∣0⟩⟨0∣ ⊗ (P00 × P00†) .+ ∣0⟩⟨1∣ ⊗ (P00× P10†) .+ ∣1⟩⟨0∣ ⊗ (P10× P00†) .+ ∣1⟩⟨1∣ ⊗ (P10× P10† .+ P11× P11†)
= ∣0⟩⟨0∣ ⊗ (P00† × P00 .+ P10† × P10) .+ ∣0⟩⟨1∣ ⊗ (P10† × P11) .+ ∣1⟩⟨0∣ ⊗ (P11† × P10) .+ ∣1⟩⟨1∣ ⊗ (P11† × P11)).
intros.
set (A:= P00 × (P00) †). fold A in H7.
set (B := P00 × (P10) †). fold B in H7.
set (C:= P10 × (P00) †). fold C in H7.
set (D := P10 × (P10) † .+ P11 × (P11) †). fold D in H7.
set (E:= (P00) † × P00 .+ (P10) † × P10). fold E in H7.
set (F := (P10) † × P11). fold F in H7.
set (G:= (P11) † × P10). fold G in H7.
set (J := (P11) † × P11). fold J in H7.
apply block_equalities with (P00:= A) (P01 := B) (P10:= C) (P11 := D)
(Q00:= E) (Q01 := F) (Q10:= G) (Q11 := J) in H7.
destruct H7 as [H8 _].
apply H8.
{
    unfold A.
    apply WF_mult. 
    apply H0. 
    apply WF_adjoint. 
    apply H0.
}
{
    unfold B. 
    apply WF_mult. 
    apply H0. 
    apply WF_adjoint. 
    apply H2.
}
{
    unfold C. 
    apply WF_mult. 
    apply H2. 
    apply WF_adjoint.
    apply H0.
}
{
    unfold D. 
    apply WF_plus.
    apply WF_mult. 
    apply H2. 
    apply WF_adjoint. 
    apply H2.
    apply WF_mult. 
    apply H3. 
    apply WF_adjoint. 
    apply H3.
}
{
    unfold E. 
    apply WF_plus.
    apply WF_mult. 
    apply WF_adjoint. 
    apply H0. 
    apply H0.
    apply WF_mult. 
    apply WF_adjoint. 
    apply H2. 
    apply H2.
}
{
    unfold F. 
    apply WF_mult. 
    apply WF_adjoint.
    apply H2. 
    apply H3.
}
{
    unfold G. 
    apply WF_mult. 
    apply WF_adjoint.
    apply H3. 
    apply H2.
}
{
    unfold J. 
    apply WF_mult. 
    apply WF_adjoint.
    apply H3. 
    apply H3.
}
reflexivity. reflexivity.
cut (V × V† = ∣0⟩⟨0∣ ⊗ (P00 × (P00) †) .+ ∣0⟩⟨1∣ ⊗ (P00 × (P10) †)
.+ ∣1⟩⟨0∣ ⊗ (P10 × (P00) †) .+ ∣1⟩⟨1∣ ⊗ (P10 × (P10) † .+ P11 × (P11) †)).
cut (V† × V = ∣0⟩⟨0∣ ⊗ ((P00) † × P00 .+ (P10) † × P10) .+ ∣0⟩⟨1∣ ⊗ ((P10) † × P11)
.+ ∣1⟩⟨0∣ ⊗ ((P11) † × P10) .+ ∣1⟩⟨1∣ ⊗ ((P11) † × P11)).
intros.
rewrite <- H7.
rewrite <- H8.
destruct H. rewrite H9.
destruct H6. rewrite adjoint_involutive in H10. rewrite H10. reflexivity.
{
    rewrite H4.
    cut ((∣0⟩⟨0∣ ⊗ P00 .+ ∣0⟩⟨1∣ ⊗ P01 .+ ∣1⟩⟨0∣ ⊗ P10 .+ ∣1⟩⟨1∣ ⊗ P11) † =
    ∣0⟩⟨0∣ ⊗ P00† .+ ∣0⟩⟨1∣ ⊗ P10† .+ ∣1⟩⟨0∣ ⊗ P01† .+ ∣1⟩⟨1∣ ⊗ P11† ).
    intros.
    rewrite H7 at 1.
    set (A := ∣0⟩⟨0∣ ⊗ P00† .+ ∣0⟩⟨1∣ ⊗ P10† .+ ∣1⟩⟨0∣ ⊗ P01† .+ ∣1⟩⟨1∣ ⊗ P11†).
    set (B := (∣0⟩⟨0∣ ⊗ P00 .+ ∣0⟩⟨1∣ ⊗ P01 .+ ∣1⟩⟨0∣ ⊗ P10 .+ ∣1⟩⟨1∣ ⊗ P11)).
    rewrite block_multiply with (P00 := (P00) †) (P01 := P10†) (P10 := P01†) (P11 := (P11) †)
    (Q00 := (P00)) (Q01 := (P01)) (Q10 := (P10)) (Q11 := (P11)).
    rewrite H5. rewrite zero_adjoint_eq. repeat rewrite Mmult_0_l. repeat rewrite Mmult_0_r.
    repeat rewrite Mplus_0_l. reflexivity.
    apply WF_adjoint. apply H0.
    apply WF_adjoint. apply H2.
    apply WF_adjoint. apply H1.
    apply WF_adjoint. apply H3.
    apply H0. apply H1. apply H2. apply H3.
    unfold A. reflexivity.
    unfold B. reflexivity.
    lma.
}
{
    rewrite H4.
    cut ((∣0⟩⟨0∣ ⊗ P00 .+ ∣0⟩⟨1∣ ⊗ P01 .+ ∣1⟩⟨0∣ ⊗ P10 .+ ∣1⟩⟨1∣ ⊗ P11) † =
    ∣0⟩⟨0∣ ⊗ P00† .+ ∣0⟩⟨1∣ ⊗ P10† .+ ∣1⟩⟨0∣ ⊗ P01† .+ ∣1⟩⟨1∣ ⊗ P11† ).
    intros.
    rewrite H7 at 1.
    set (A := ∣0⟩⟨0∣ ⊗ P00† .+ ∣0⟩⟨1∣ ⊗ P10† .+ ∣1⟩⟨0∣ ⊗ P01† .+ ∣1⟩⟨1∣ ⊗ P11†).
    set (B := (∣0⟩⟨0∣ ⊗ P00 .+ ∣0⟩⟨1∣ ⊗ P01 .+ ∣1⟩⟨0∣ ⊗ P10 .+ ∣1⟩⟨1∣ ⊗ P11)).
    rewrite block_multiply with (Q00 := (P00) †) (Q01 := P10†) (Q10 := P01†) (Q11 := (P11) †)
    (P00 := (P00)) (P01 := (P01)) (P10 := (P10)) (P11 := (P11)).
    rewrite H5. rewrite zero_adjoint_eq. repeat rewrite Mmult_0_l. repeat rewrite Mmult_0_r.
    repeat rewrite Mplus_0_r. reflexivity.
    apply H0. apply H1. apply H2. apply H3.
    apply WF_adjoint. apply H0.
    apply WF_adjoint. apply H2.
    apply WF_adjoint. apply H1.
    apply WF_adjoint. apply H3.
    unfold B. reflexivity.
    unfold A. reflexivity.
    lma.
}
lca.
apply transpose_unitary. apply H.
Qed.

Lemma a9_left: forall (V : Square 4) (P00 P01 P10 P11 : Square 2),
WF_Unitary V -> WF_Matrix P00 -> WF_Matrix P01 -> WF_Matrix P10 -> WF_Matrix P11 ->
V = ∣0⟩⟨0∣ ⊗ P00 .+ ∣0⟩⟨1∣ ⊗ P01 .+ ∣1⟩⟨0∣ ⊗ P10 .+ ∣1⟩⟨1∣ ⊗ P11 ->
P10 = Zero -> P01 = Zero.
Proof.
intros.
rewrite <- adjoint_involutive at 1. rewrite <- adjoint_involutive.
apply Madjoint_simplify.
rewrite zero_adjoint_eq.
cut (P10 † = Zero).
intros.
set (U := ∣0⟩⟨0∣ ⊗ (P00 †) .+ ∣0⟩⟨1∣ ⊗ (P10 †) .+ ∣1⟩⟨0∣ ⊗ (P01 †) .+ ∣1⟩⟨1∣ ⊗ (P11 †)).
apply a9_right with (V := U) (P00 := P00 †) (P01 := P10 †) (P10 := P01 †) (P11 := P11 †).
assert (Step1: U = V†).
{
    unfold U. rewrite H4. lma.
}
rewrite Step1. clear Step1.
apply transpose_unitary. apply H.
apply WF_adjoint. apply H0.
apply WF_adjoint. apply H2.
apply WF_adjoint. apply H1.
apply WF_adjoint. apply H3.
trivial.
apply H6.
rewrite H5. rewrite zero_adjoint_eq. reflexivity.
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
