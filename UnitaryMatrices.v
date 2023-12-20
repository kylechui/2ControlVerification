Require Import QuantumLib.Quantum.
Require Import QuantumLib.Eigenvectors.
Require Import QuantumLib.Matrix.
From Proof Require Import SquareMatrices.
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

Lemma conj_mult_re_is_nonneg: forall (a: C),
Re (a^* * a) >= 0.
Proof.
intros.
unfold Re; unfold Cconj; unfold Cmult.
simpl.
rewrite <- Ropp_mult_distr_l.
assert (Step1: (fst a * fst a - - (snd a * snd a) = fst a * fst a + (snd a * snd a))%R).
{
    field.
}
rewrite Step1.
intros.
apply Rle_ge.
apply Rplus_le_le_0_compat.
apply Rle_0_sqr.
apply Rle_0_sqr.
Qed.

Lemma conj_mult_im_is_0: forall (a: C),
Im (a^* * a) = 0.
Proof.
intros.
unfold Im; unfold Cconj; unfold Cmult.
simpl.
lra.
Qed.

Lemma sum_of_pos_c_is_0_implies_0: forall (a b: C),
Re a >= 0 -> Im a = 0 -> Re b >= 0 -> Im b = 0 ->
a + b = C0 -> a = C0 /\ b = C0.
Proof.
intros.
unfold Re in *; unfold Im in *.
unfold Cplus in H3.
rewrite H0 in H3.
rewrite H2 in H3.
cut ((fst a + fst b = 0)%R).
intros.
split.
+
    apply c_proj_eq.
    simpl.
    revert H4.
    apply Rplus_eq_0_l.
    apply Rge_le.
    apply H.
    apply Rge_le.
    apply H1.
    apply H0.
+
    apply c_proj_eq.
    simpl.
    revert H4.
    rewrite Rplus_comm.
    apply Rplus_eq_0_l.
    apply Rge_le.
    apply H1.
    apply Rge_le.
    apply H.
    apply H2.
+
    inversion H3.
    reflexivity.
Qed.

Lemma complex_split: forall (a b: C),
a = b  -> fst a = fst b /\ snd a = snd b.
Proof.
intros.
split.
rewrite H.
reflexivity.
rewrite H.
reflexivity.
Qed.


Lemma squared_norm_eq_0_implies_0: forall (a: C),
a^* * a = 0 -> a = 0.
Proof.
intros.
apply c_proj_eq.
unfold Cconj in *; unfold Cmult in *.
simpl in *.
{
    cut ((fst a * fst a - - snd a * snd a)%R = 0).
    cut ((fst a * fst a)%R = 0 -> fst a = 0).
    cut (((fst a * fst a - - snd a * snd a)%R = 0 -> (fst a * fst a)%R = 0)).
    intros.
    apply H1.
    apply H0.
    apply H2.
    {
        rewrite <- Ropp_mult_distr_l.
        assert (Step1: (fst a * fst a - - (snd a * snd a) = fst a * fst a + (snd a * snd a))%R).
        {
            field.
        }
        rewrite Step1.
        set (b := fst a).
        set (c := snd a).
        set (d := (b * b)%R).
        set (e := (c*c)%R).
        assert (Step2: 0 <= d).
        {
            apply Rle_0_sqr.
        }
        assert (Step3: 0 <= e).
        {
            apply Rle_0_sqr.
        }
        apply Rplus_eq_0_l.
        apply Step2.
        apply Step3.
    }
    {
        apply Rsqr_0_uniq.
    }
    {
        inversion H.
        reflexivity.
    }
}
{
    cut ((fst a * fst a - - snd a * snd a)%R = 0).
    cut ((snd a * snd a)%R = 0 -> snd a = 0).
    cut (((fst a * fst a - - snd a * snd a)%R = 0 -> (snd a * snd a)%R = 0)).
    intros.
    apply H1.
    apply H0.
    apply H2.
    {
        rewrite <- Ropp_mult_distr_l.
        assert (Step1: (fst a * fst a - - (snd a * snd a) = fst a * fst a + (snd a * snd a))%R).
        {
            field.
        }
        rewrite Step1.
        set (b := fst a).
        set (c := snd a).
        set (d := (b * b)%R).
        set (e := (c*c)%R).
        rewrite Rplus_comm.
        apply Rplus_eq_0_l.
        apply Rle_0_sqr.
        apply Rle_0_sqr.
    }
    {
        apply Rsqr_0_uniq.
    }
    {
        inversion H.
        reflexivity.
    }
}
Qed.

Lemma sum_of_adjoints_re_nonneg: forall (b c d: C),
Re (b ^* * b + (c ^* * c + d ^* * d)) >= 0.
Proof.
intros.
unfold Re, Cplus.
simpl.
rewrite <- Ropp_mult_distr_l. rewrite <- Ropp_mult_distr_l. rewrite <- Ropp_mult_distr_l.
assert (Step1: (fst b * fst b - - (snd b * snd b) = fst b * fst b + snd b * snd b)%R). field.
rewrite Step1. clear Step1.
assert (Step2: (fst c * fst c - - (snd c * snd c) = fst c * fst c + snd c * snd c)%R). field.
rewrite Step2. clear Step2.
assert (Step3: (fst d * fst d - - (snd d * snd d) = fst d * fst d + snd d * snd d)%R). field.
rewrite Step3. clear Step3.
apply Rle_ge.
apply Rplus_le_le_0_compat.
apply Rplus_le_le_0_compat.
apply Rle_0_sqr.
apply Rle_0_sqr.
apply Rplus_le_le_0_compat.
apply Rplus_le_le_0_compat.
apply Rle_0_sqr.
apply Rle_0_sqr.
apply Rplus_le_le_0_compat.
apply Rle_0_sqr.
apply Rle_0_sqr.
Qed.

Lemma sum_of_adjoints_im_0: forall (b c d: C),
Im (b ^* * b + (c ^* * c + d ^* * d)) = 0.
Proof.
intros.
unfold Im, Cplus.
simpl.
lra.
Qed.

Lemma sum_of_squared_norms_eq_0_implies_0: forall (a b c d: C),
a ^* * a + b ^* * b + c ^* * c + d ^* * d = 0 -> a = 0 /\ b = 0 /\ c = 0 /\ d= 0.
Proof.
intros.
split.
{
    revert H.
    rewrite <- Cplus_assoc.
    rewrite <- Cplus_assoc.
    set (f := a^* * a).
    set (g := b ^* * b + (c ^* * c + d ^* * d)).
    cut (f+g = 0 -> f = 0).
    cut (f = 0 -> a = 0).
    intros.
    apply H.
    apply H0.
    apply H1.
    apply squared_norm_eq_0_implies_0.
    apply sum_of_pos_c_is_0_implies_0.
    apply conj_mult_re_is_nonneg.
    apply conj_mult_im_is_0.
    apply sum_of_adjoints_re_nonneg.
    apply sum_of_adjoints_im_0.
}
split.
{
    revert H.
    assert (Step1: a ^* * a + b ^* * b + c ^* * c + d ^* * d = b ^* * b + a ^* * a  + c ^* * c + d ^* * d).
    {
        lca.
    }
    rewrite Step1.
    rewrite <- Cplus_assoc.
    rewrite <- Cplus_assoc.
    set (f := b^* * b).
    set (g := a ^* * a + (c ^* * c + d ^* * d)).
    cut (f+g = 0 -> f = 0).
    cut (f = 0 -> b = 0).
    intros.
    apply H.
    apply H0.
    apply H1.
    apply squared_norm_eq_0_implies_0.
    apply sum_of_pos_c_is_0_implies_0.
    apply conj_mult_re_is_nonneg.
    apply conj_mult_im_is_0.
    apply sum_of_adjoints_re_nonneg.
    apply sum_of_adjoints_im_0.
}
split.
{
    revert H.
    assert (Step1: a ^* * a + b ^* * b + c ^* * c + d ^* * d = c ^* * c + a ^* * a + b ^* * b + d ^* * d).
    {
        lca.
    }
    rewrite Step1.
    rewrite <- Cplus_assoc.
    rewrite <- Cplus_assoc.
    set (f := c^* * c).
    set (g := a ^* * a + (b ^* * b + d ^* * d)).
    cut (f+g = 0 -> f = 0).
    cut (f = 0 -> c = 0).
    intros.
    apply H.
    apply H0.
    apply H1.
    apply squared_norm_eq_0_implies_0.
    apply sum_of_pos_c_is_0_implies_0.
    apply conj_mult_re_is_nonneg.
    apply conj_mult_im_is_0.
    apply sum_of_adjoints_re_nonneg.
    apply sum_of_adjoints_im_0.
}
{
    revert H.
    rewrite Cplus_comm.
    rewrite <- Cplus_assoc.
    set (f := d^* * d).
    set (g := a ^* * a + (b ^* * b + c ^* * c)).
    cut (f+g = 0 -> f = 0).
    cut (f = 0 -> d = 0).
    intros.
    apply H.
    apply H0.
    apply H1.
    apply squared_norm_eq_0_implies_0.
    apply sum_of_pos_c_is_0_implies_0.
    apply conj_mult_re_is_nonneg.
    apply conj_mult_im_is_0.
    apply sum_of_adjoints_re_nonneg.
    apply sum_of_adjoints_im_0.
}
Qed.

Lemma C_l_cancel: forall (a b c: C), 
a + b = a + c -> b = c.
(* Thanks Kyle *)
Proof.
  intros.
  rewrite <- (Cplus_0_l b).
  rewrite <- (Cplus_0_l c).
  rewrite <- (Cplus_opp_l a).
  rewrite <- Cplus_assoc.
  rewrite H.
  ring.
Qed.

Lemma WF_ket0bra1: WF_Matrix ∣0⟩⟨1∣.
Proof.
apply WF_mult.
apply WF_qubit0.
apply WF_adjoint.
apply WF_qubit1.
Qed.

Lemma WF_ket1bra0: WF_Matrix ∣1⟩⟨0∣.
Proof.
apply WF_mult.
apply WF_qubit1.
apply WF_adjoint.
apply WF_qubit0.
Qed.

Lemma WF_blockmatrix: forall (P00 P01 P10 P11: Square 2), 
WF_Matrix P00 -> WF_Matrix P01 -> WF_Matrix P10 -> WF_Matrix P11 ->
WF_Matrix (∣0⟩⟨0∣ ⊗ P00 .+ ∣0⟩⟨1∣ ⊗ P01 .+ ∣1⟩⟨0∣ ⊗ P10 .+ ∣1⟩⟨1∣ ⊗ P11).
Proof.
intros.
apply WF_plus.
apply WF_plus.
apply WF_plus.
apply WF_kron.
ring. ring.
apply WF_braqubit0.
apply H.
apply WF_kron.
ring. ring.
apply WF_ket0bra1.
apply H0.
apply WF_kron.
ring. ring.
apply WF_ket1bra0.
apply H1.
apply WF_kron.
ring. ring.
apply WF_braqubit1.
apply H2.
Qed.

Lemma block_multiply: forall (U V: Square 4) (P00 P01 P10 P11 Q00 Q01 Q10 Q11: Square 2), 
WF_Matrix P00 -> WF_Matrix P01 -> WF_Matrix P10 -> WF_Matrix P11
-> WF_Matrix Q00 -> WF_Matrix Q01 -> WF_Matrix Q10 -> WF_Matrix Q11 ->
U = ∣0⟩⟨0∣ ⊗ P00 .+ ∣0⟩⟨1∣ ⊗ P01 .+ ∣1⟩⟨0∣ ⊗ P10 .+ ∣1⟩⟨1∣ ⊗ P11 -> 
V = ∣0⟩⟨0∣ ⊗ Q00 .+ ∣0⟩⟨1∣ ⊗ Q01 .+ ∣1⟩⟨0∣ ⊗ Q10 .+ ∣1⟩⟨1∣ ⊗ Q11 -> 
U × V = ∣0⟩⟨0∣ ⊗ (P00 × Q00 .+ P01 × Q10) .+ ∣0⟩⟨1∣ ⊗ (P00 × Q01 .+ P01×Q11) .+ ∣1⟩⟨0∣ ⊗ (P10×Q00 .+ P11 × Q10) .+ ∣1⟩⟨1∣ ⊗ (P10 × Q01 .+ P11 × Q11).
Proof.
intros U V P00 P01 P10 P11 Q00 Q01 Q10 Q11 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
rewrite H9. rewrite H10.
apply mat_equiv_eq.
{
    apply WF_mult.
    apply WF_blockmatrix.
    apply H1. apply H2. apply H3. apply H4.
    apply WF_blockmatrix.
    apply H5. apply H6. apply H7. apply H8.
}
{
    apply WF_blockmatrix.
    apply WF_plus.
    apply WF_mult.
    apply H1. apply H5.
    apply WF_mult.
    apply H2. apply H7.
    apply WF_plus.
    apply WF_mult.
    apply H1. apply H6.
    apply WF_mult.
    apply H2. apply H8.  
    apply WF_plus.
    apply WF_mult.
    apply H3. apply H5.
    apply WF_mult.
    apply H4. apply H7.  
    apply WF_plus.
    apply WF_mult.
    apply H3. apply H6.
    apply WF_mult.
    apply H4. apply H8.     
}
{
    unfold Mmult. unfold Mplus. unfold kron.
    by_cell.
    lca. lca. lca. lca. lca. lca. lca. lca.
    lca. lca. lca. lca. lca. lca. lca. lca.
}
Qed.

Lemma block_equalities: forall (U V: Square 4) (P00 P01 P10 P11 Q00 Q01 Q10 Q11: Square 2), 
WF_Matrix P00 -> WF_Matrix P01 -> WF_Matrix P10 -> WF_Matrix P11
-> WF_Matrix Q00 -> WF_Matrix Q01 -> WF_Matrix Q10 -> WF_Matrix Q11 ->
U = ∣0⟩⟨0∣ ⊗ P00 .+ ∣0⟩⟨1∣ ⊗ P01 .+ ∣1⟩⟨0∣ ⊗ P10 .+ ∣1⟩⟨1∣ ⊗ P11 -> 
V = ∣0⟩⟨0∣ ⊗ Q00 .+ ∣0⟩⟨1∣ ⊗ Q01 .+ ∣1⟩⟨0∣ ⊗ Q10 .+ ∣1⟩⟨1∣ ⊗ Q11 -> 
U = V -> P00 = Q00 /\ P01 = Q01 /\ P10 = Q10 /\ P11 = Q11.
Proof.
intros U V P00 P01 P10 P11 Q00 Q01 Q10 Q11 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.
split.
{
    apply mat_equiv_eq.
    apply H1. apply H5.
    by_cell.
    cut (P00 0%nat 0%nat = U 0%nat 0%nat).
    cut (Q00 0%nat 0%nat = V 0%nat 0%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
    cut (P00 0%nat 1%nat = U 0%nat 1%nat).
    cut (Q00 0%nat 1%nat = V 0%nat 1%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
    cut (P00 1%nat 0%nat = U 1%nat 0%nat).
    cut (Q00 1%nat 0%nat = V 1%nat 0%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
    cut (P00 1%nat 1%nat = U 1%nat 1%nat).
    cut (Q00 1%nat 1%nat = V 1%nat 1%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
}
split.
{
    apply mat_equiv_eq.
    apply H2. apply H6.
    by_cell.
    cut (P01 0%nat 0%nat = U 0%nat 2%nat).
    cut (Q01 0%nat 0%nat = V 0%nat 2%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
    cut (P01 0%nat 1%nat = U 0%nat 3%nat).
    cut (Q01 0%nat 1%nat = V 0%nat 3%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
    cut (P01 1%nat 0%nat = U 1%nat 2%nat).
    cut (Q01 1%nat 0%nat = V 1%nat 2%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
    cut (P01 1%nat 1%nat = U 1%nat 3%nat).
    cut (Q01 1%nat 1%nat = V 1%nat 3%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
} 
split.
{
    apply mat_equiv_eq.
    apply H3. apply H7.
    by_cell.
    cut (P10 0%nat 0%nat = U 2%nat 0%nat).
    cut (Q10 0%nat 0%nat = V 2%nat 0%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
    cut (P10 0%nat 1%nat = U 2%nat 1%nat).
    cut (Q10 0%nat 1%nat = V 2%nat 1%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
    cut (P10 1%nat 0%nat = U 3%nat 0%nat).
    cut (Q10 1%nat 0%nat = V 3%nat 0%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
    cut (P10 1%nat 1%nat = U 3%nat 1%nat).
    cut (Q10 1%nat 1%nat = V 3%nat 1%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
}
{
    apply mat_equiv_eq.
    apply H4. apply H8.
    by_cell.
    cut (P11 0%nat 0%nat = U 2%nat 2%nat).
    cut (Q11 0%nat 0%nat = V 2%nat 2%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
    cut (P11 0%nat 1%nat = U 2%nat 3%nat).
    cut (Q11 0%nat 1%nat = V 2%nat 3%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
    cut (P11 1%nat 0%nat = U 3%nat 2%nat).
    cut (Q11 1%nat 0%nat = V 3%nat 2%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
    cut (P11 1%nat 1%nat = U 3%nat 3%nat).
    cut (Q11 1%nat 1%nat = V 3%nat 3%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
}
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