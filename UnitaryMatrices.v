Require Import QuantumLib.Quantum.
Require Import QuantumLib.Eigenvectors.

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




