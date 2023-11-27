Require Import QuantumLib.Quantum.
Require Import QuantumLib.Eigenvectors.
Require Import QuantumLib.Matrix.
Require Import List. 
Import ListNotations.

Theorem a3: 
forall {n} (U: Square n), 
    WF_Unitary U -> exists (V W: Square n), 
        WF_Unitary V -> WF_Diagonal W-> forall i : nat,
         (i < n)%nat -> exists (v : Vector n), 
            WF_Matrix v -> Eigenpair (U) (v, W i i).
Proof.
    Admitted.

Lemma a4_left: forall {n} (v: Vector n) (c: C) (U V : Square n), 
    WF_Matrix v -> WF_Unitary U -> WF_Unitary V ->
    Eigenpair V (U × v, c) -> Eigenpair (U† × V × U) (v,c).
Proof.
(* TODO: Proof is adapted from QuantumLib.Eigenvectors to step through the proof. Replace with application.*)
intros.
destruct H0 as [H0 H3].
unfold Eigenpair in *; simpl in *.
do 2 (rewrite Mmult_assoc).
rewrite H2.
rewrite Mscale_mult_dist_r.
rewrite <- Mmult_assoc.
rewrite H3.
rewrite Mmult_1_l.
reflexivity.
apply H.
Qed.

Lemma a4_right: forall {n} (v: Vector n) (c: C) (U V : Square n), 
    WF_Matrix v -> WF_Unitary U -> WF_Unitary V ->
    Eigenpair (U† × V × U) (v,c) -> Eigenpair V (U × v, c).
Proof.
intros.
unfold Eigenpair in *; simpl in *.
assert (Step1: I n × V × (U × v) = V × (U × v)).
{
    rewrite Mmult_assoc.
    apply Mmult_1_l.
    apply WF_mult.
    apply H1.
    apply WF_mult.
    apply H0.
    apply H.   
}
rewrite <- Step1. clear Step1.
assert (Step2: WF_Unitary (U†)).
{
    apply transpose_unitary.
    apply H0.
}
destruct Step2 as [Step2_1 Step2_2].
rewrite <- Step2_2. clear Step2_1. clear Step2_2.
rewrite adjoint_involutive.
do 2 (rewrite Mmult_assoc).
rewrite Mmult_assoc in H2. rewrite Mmult_assoc in H2.
rewrite H2.
rewrite Mscale_mult_dist_r.
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

(*TODO: finish this proof after evaluating if its worth the time over just the |0>,|1> cases *)
Lemma kron_const_equiv: forall {a b c d} (A : Matrix a b) (B C: Matrix c d), 
A ⊗ B = A ⊗ C -> B = C.
Proof.
intros.
revert H.
Admitted.


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
apply kron_const_equiv.
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
apply kron_const_equiv.
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

(* only defined over 2 qubit systems *)
Definition partial_trace_l (M: Square 4): Square 2 := 
    fun x y =>
    match (x,y) with
    | (0,0) => (M 0 0)%nat + (M 2 2)%nat
    | (0,1) => (M 0 1)%nat + (M 2 3)%nat
    | (1,0) => (M 1 0)%nat + (M 3 2)%nat
    | (1,1) => (M 1 1)%nat + (M 3 3)%nat
    | _ => C0
    end.

Lemma WF_partial_trace : forall (A : Square 4),
    WF_Matrix (partial_trace_l A).
Proof. 
unfold WF_Matrix.
intros.
destruct H.
{
    unfold partial_trace_l.
    destruct x as [|x'].
    contradict H.
    lia.
    destruct x' as [|x''].
    contradict H.
    lia.
    reflexivity.
}
{
    unfold partial_trace_l.
    destruct x as [|x'].
    {
        destruct y as [|y'].
        contradict H.
        lia.
        destruct y' as [|y''].
        contradict H.
        lia.
        reflexivity.
    }
    {
        destruct x' as [|x''].
        destruct y as [|y'].
        contradict H.
        lia.
        destruct y' as [|y''].
        contradict H.
        lia.
        reflexivity.
        reflexivity.
    }
}
Qed.

Lemma kron_partial_trace_l : forall (P : Square 2) (Q: Square 2),
    WF_Matrix Q -> 
    partial_trace_l (P ⊗ Q) = (trace P) .* Q.
Proof.
intros.
apply mat_equiv_eq.
apply WF_partial_trace.
apply WF_scale.
apply H.
by_cell.
{
    unfold partial_trace_l; unfold kron; unfold trace; unfold scale.
    lca.   
}
{
    unfold partial_trace_l; unfold kron; unfold trace; unfold scale.
    lca.   
}
{
    unfold partial_trace_l; unfold kron; unfold trace; unfold scale.
    lca.   
}
{
    unfold partial_trace_l; unfold kron; unfold trace; unfold scale.
    lca.   
}
Qed.

Lemma partial_trace_linear_l : forall (c:C) (A B : Square 4),
  partial_trace_l (A .+ c .* B) = partial_trace_l A .+ c .* partial_trace_l B.
Proof.
intros.
apply mat_equiv_eq.
apply WF_partial_trace.
apply WF_plus.
apply WF_partial_trace.
apply WF_scale.
apply WF_partial_trace.
by_cell.
{
    unfold partial_trace_l; unfold scale; unfold Mplus.
    lca.
}
{
    unfold partial_trace_l; unfold scale; unfold Mplus.
    lca.
}
{
    unfold partial_trace_l; unfold scale; unfold Mplus.
    lca.
}
{
    unfold partial_trace_l; unfold scale; unfold Mplus.
    lca.
}
Qed.

Lemma partial_trace_compat_l : forall (A B : Square 4),
  A = B -> partial_trace_l A = partial_trace_l B.
Proof.
intros.
apply mat_equiv_eq.
apply WF_partial_trace.
apply WF_partial_trace.
by_cell.
{
    unfold partial_trace_l.
    rewrite H.
    reflexivity.
}
{
    unfold partial_trace_l.
    rewrite H.
    reflexivity.
}
{
    unfold partial_trace_l.
    rewrite H.
    reflexivity.
}
{
    unfold partial_trace_l.
    rewrite H.
    reflexivity.
}
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