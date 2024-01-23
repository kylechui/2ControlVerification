From Proof Require Import AlgebraHelpers.
From Proof Require Import ExplicitDecompositions.
Require Import QuantumLib.Eigenvectors.
Require Import QuantumLib.Matrix.

Definition get_eigenpairs (A : Square 2) : (Vector 2 * C) * (Vector 2 * C) :=
  let a := A 0%nat 0%nat in
  let b := A 0%nat 1%nat in
  let c := A 1%nat 0%nat in
  let d := A 1%nat 1%nat in
  let discriminant := (a + d)^2 - (4 * (a * d - b * c)) in
  let lambda1 := (((a + d) + Complex_sqrt discriminant) / 2)%C in
  let lambda2 := (((a + d) - Complex_sqrt discriminant) / 2)%C in
  let v1 := fun x y => match x, y with
                       | 0, 0 => lambda1 - d
                       | 1, 0 => c
                       | _, _ => C0
                       end in
  let v2 := fun x y => match x, y with
                       | 0, 0 => lambda2 - d
                       | 1, 0 => c
                       | _, _ => C0
                       end in
  ((v1, lambda1), (v2, lambda2)).

Lemma WF_fst_eigenvector: forall (A : Square 2), 
match get_eigenpairs A with 
| ((v1, _), _) => WF_Matrix v1
end.
Proof.
intros.
simpl.
unfold WF_Matrix.
intros.
destruct H.
{
  destruct x as [|a]. contradict H. lia.
  destruct a as [|x]. contradict H. lia.
  reflexivity.
}
{
  destruct x as [|a].
  destruct y as [|a]. contradict H. lia.
  reflexivity.
  destruct a as [|x].
  destruct y as [|a]. contradict H. lia.
  reflexivity. reflexivity.
}
Qed.

Lemma WF_snd_eigenvector: forall (A : Square 2), 
match get_eigenpairs A with 
| (_, (v2, _)) => WF_Matrix v2
end.
Proof.
intros.
simpl.
unfold WF_Matrix.
intros.
destruct H.
{
  destruct x as [|a]. contradict H. lia.
  destruct a as [|x]. contradict H. lia.
  reflexivity.
}
{
  destruct x as [|a].
  destruct y as [|a]. contradict H. lia.
  reflexivity.
  destruct a as [|x].
  destruct y as [|a]. contradict H. lia.
  reflexivity. reflexivity.
}
Qed.

Lemma eigenpairs_are_eigenpairs : forall (A : Square 2),
  WF_Matrix A ->
    let (eigenpair1, eigenpair2) := get_eigenpairs A in
    Eigenpair A eigenpair1 /\ Eigenpair A eigenpair2.
Proof.
  intros A WF_A.
  split; simpl.
  - simpl.
    unfold Eigenpair.
    lma'.
    {
      simpl.
      unfold Mmult; unfold WF_Matrix; unfold big_sum; simpl.
      intros.
      destruct H.
      {
        unfold WF_Matrix in WF_A.
        specialize (WF_A x).
        assert (H2 : forall y, A x y = C0).
        {
          intro.
          apply WF_A.
          left.
          assumption.
        }
        do 2 rewrite H2; clear H2.
        lca.
      }
      {
        destruct y.
        - lia.
        - lca.
      }
    }
    {
      unfold scale; simpl.
      unfold WF_Matrix.
      intros.
      destruct H.
      {
        destruct x.
        + lia.
        + destruct x.
          * lia.
          * lca.
      }
      {
        destruct y.
        - lia.
        - destruct x.
          + lca.
          + destruct x; lca. (* I have no clue why this works *)
      }
    }
    {
      unfold Mmult; simpl.
      unfold scale.
      Csimpl.
      set (a := A 0%nat 0%nat).
      set (b := A 0%nat 1%nat).
      set (c := A 1%nat 0%nat).
      set (d := A 1%nat 1%nat).
      set (discriminant := (a + d) * (a + d) - (4 * (a * d - b * c))).
      replace ((a + d + Complex_sqrt discriminant) / C2 * ((a + d + Complex_sqrt discriminant) / C2 - d)) with (((a + Complex_sqrt discriminant) * (a + Complex_sqrt discriminant) - d * d) / 4) by lca.
      replace ((a + Complex_sqrt discriminant) * (a + Complex_sqrt discriminant) - d * d) with (a * a - d * d + Complex_sqrt discriminant * Complex_sqrt discriminant + 2 * a * Complex_sqrt discriminant) by lca.
      rewrite Complex_sqrt_sqrt.
      replace (a * ((a + d + Complex_sqrt discriminant) / C2 - d) + b * c) with ((2 * a * a - 2 * a * d + 4 * b * c + 2 * a * Complex_sqrt discriminant) / 4) by lca.
      unfold Cdiv.
      apply Cmult_simplify; auto.
      apply Cplus_simplify; auto.
      lca.
    }
  - unfold Eigenpair.
    lma'.
    {
      unfold Mmult, big_sum, WF_Matrix; simpl.
      intros.
      destruct H.
      {
        unfold WF_Matrix in WF_A.
        specialize (WF_A x).
        assert (H2 : forall y, A x y = C0).
        {
          intro.
          apply WF_A.
          left.
          assumption.
        }
        do 2 rewrite H2; clear H2.
        lca.
      }
      {
        destruct y.
        - lia.
        - lca.
      }
    }
    {
      unfold WF_Matrix, scale; simpl.
      intros.
      destruct H.
      {
        destruct x.
        + lia.
        + destruct x.
          * lia.
          * lca.
      }
      {
        destruct y.
        - lia.
        - destruct x.
          + lca.
          + destruct x; lca. (* I have no clue why this works *)
      }
    }
    {
      unfold Mmult, scale; simpl.
      set (a := A 0%nat 0%nat).
      set (b := A 0%nat 1%nat).
      set (c := A 1%nat 0%nat).
      set (d := A 1%nat 1%nat).
      Csimpl.
      set (discriminant := (a + d) * (a + d) - (4 * (a * d - b * c))).
      replace ((a + d - Complex_sqrt discriminant) / C2 * ((a + d - Complex_sqrt discriminant) / C2 - d)) with ((a * a + Complex_sqrt discriminant * Complex_sqrt discriminant - d * d - 2 * a * Complex_sqrt discriminant) / 4) by lca.
      replace (a * ((a + d - Complex_sqrt discriminant) / C2 - d) + b * c) with ((2 * a * a - 2 * a * d + 4 * b * c - 2 * a * Complex_sqrt discriminant) / 4) by lca.
      unfold Cdiv.
      apply Cmult_simplify; auto.
      apply Cplus_simplify; auto.
      rewrite Complex_sqrt_sqrt.
      lca.
    }
Qed.

Lemma Cconj_half_distr: forall (a : C), 
(a / C2)^* = (a^*)/C2.
Proof.
intros.
lca.
Qed.

Lemma Cmult_minus_distr_l: forall  (x y z : C),
 x * (y - z) = x * y - x * z.
Proof. intros. lca. Qed.

Lemma Cmult_minus_distr_r: forall (x y z: C), 
(x - y) * z = x*z - y*z.
Proof. intros. lca. Qed.

Lemma eigenvectors_are_orthogonal: forall (A : Square 2), 
match get_eigenpairs A with 
| ((v1, _), (v2, _)) => ⟨ v1 , v2 ⟩ = 0
end.
Proof.
intros.
simpl.
rewrite vector2_inner_prod_decomp. 2: apply WF_fst_eigenvector. 2: apply WF_snd_eigenvector.
Csimpl.
rewrite Cconj_minus_distr.
rewrite Cconj_half_distr.
rewrite Cconj_plus_distr.
rewrite Cconj_plus_distr.
rewrite Cmult_minus_distr_l.
repeat rewrite Cmult_minus_distr_r.
repeat rewrite Cmult_plus_distr_l.
unfold Complex_sqrt.
Csimpl.
simpl.
lca.