From Proof Require Import AlgebraHelpers.
From Proof Require Import ExplicitDecompositions.
Require Import QuantumLib.Eigenvectors.
Require Import QuantumLib.Matrix.
Require Import QuantumLib.Complex.

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

Lemma half_half_mult: forall (a b: C), 
(a / C2) * (b / C2) = (a * b)/ (C2 * C2).
Proof. 
intros.
lca.
Qed.

Lemma half_mult_r: forall (a b: C), 
(a) * (b / C2) = (a * b)/ (C2).
Proof. 
intros.
lca.
Qed.

Lemma half_mult_l: forall (a b: C), 
(a / C2) * (b) = (a * b)/ (C2).
Proof. 
intros.
lca.
Qed.

Lemma four_neq_0: RtoC 4 <> 0.
Proof.
apply rtoc_neq_decomp.
lra.
Qed.

Lemma quarter_mult_4_r: forall (a : C), 
(a / (C2 * C2)) * RtoC 4 = a.
Proof. intros. lca. Qed.

Lemma half_mult_4_r: forall (a : C), 
(a / C2) * RtoC 4 = a * C2.
Proof. intros. lca. Qed.

Lemma add_conj: forall (a: C), 
a + a^* = RtoC ((2 * fst a)%R).
Proof. intros. lca. Qed.

Lemma sub_conj: forall (a: C), 
a - a^* = (0, (2 * snd a)%R).
Proof. intros. lca. Qed.

Lemma pow2_equiv_Rsqr: forall (a : R),
(a ^ 2)%R = Rsqr a.
Proof.
intros. 
unfold pow, Rsqr.
lra.
Qed.

Lemma neg_pow2: forall (a: R), 
(a ^ 2)%R = ((-a)^2)%R.
Proof.
intros.
unfold pow.
lra.
Qed.

Lemma Complex_sqrt_adj_mult: forall (x: C), 
let norm := Cmod x in
(Complex_sqrt x)^* * (Complex_sqrt x) = 
  (norm, 0).
Proof.
intros.
unfold Complex_sqrt.
destruct (Req_EM_T (snd x) 0).
{
  destruct (Rlt_dec (fst x) 0).
  {
    unfold Cconj, Cmult.
    simpl.
    repeat rewrite Rmult_0_l.
    rewrite Rmult_0_r.
    apply c_proj_eq.
    {
      simpl.
      unfold Rminus.
      rewrite Rplus_0_l.
      rewrite Ropp_mult_distr_l.
      rewrite Ropp_involutive.
      rewrite sqrt_sqrt.
      unfold norm, Cmod.
      rewrite e.
      replace ((fst x ^ 2 + 0 ^ 2)%R) with ((fst x ^ 2)%R) by lra.
      symmetry.
      rewrite neg_pow2.
      rewrite pow2_equiv_Rsqr.
      apply sqrt_Rsqr.
      1,2: rewrite <- Rmult_0_r with (r := (-(1))%R).
      1,2: rewrite <- Rmult_1_l with (r := fst x).
      1,2: rewrite Ropp_mult_distr_l.
      1,2: apply Rmult_le_compat_neg_l.
      1,3: lra.
      1,2: apply Rlt_le.
      1,2: apply r.
    }
    {
      simpl.
      lra.
    }
  }
  {
    unfold Cconj, Cmult.
    simpl.
    rewrite Ropp_0.
    repeat rewrite Rmult_0_l.
    rewrite Rmult_0_r.
    repeat rewrite Rplus_0_r.
    rewrite Rminus_0_r.
    apply c_proj_eq.
    {
      simpl.
      apply Rnot_lt_le in n.
      rewrite sqrt_sqrt.
      unfold norm, Cmod.
      rewrite e.
      replace ((fst x ^ 2 + 0 ^ 2)%R) with ((fst x ^ 2)%R) by lra.
      rewrite pow2_equiv_Rsqr.
      symmetry.
      apply sqrt_Rsqr.
      all: assumption.
    }
    {
      simpl. reflexivity.
    }
  }
}
{
  unfold Cconj, Cmult.
  simpl.
  apply c_proj_eq.
  {
    simpl.
    rewrite sqrt_sqrt.
    rewrite <- Ropp_mult_distr_l.
    unfold Rminus.
    rewrite Ropp_involutive.
    replace ((Rabs (snd x) / snd x * √ ((Cmod x + - fst x) / 2) *
    (Rabs (snd x) / snd x * √ ((Cmod x + - fst x) / 2)))%R) with 
    (((√ ((Cmod x + - fst x) / 2)* √ ((Cmod x + - fst x) / 2)) *
    (Rabs (snd x) / snd x  * (Rabs (snd x) / snd x)))%R) by lra.
    rewrite sqrt_sqrt.
  }
  {
    simpl.
    lra.
  }
}
Admitted.

Lemma eigenvectors_are_orthogonal: forall (A : Square 2), 
match get_eigenpairs A with 
| ((v1, _), (v2, _)) => ⟨ v1 , v2 ⟩ = 0
end.
Proof.
intros.
simpl.
rewrite vector2_inner_prod_decomp. 2: apply WF_fst_eigenvector. 2: apply WF_snd_eigenvector.
set (a := A 0%nat 0%nat).
set (b := A 0%nat 1%nat).
set (c := A 1%nat 0%nat).
set (d := A 1%nat 1%nat).
Csimpl.
set (sqrt_term := (a + d) * (a + d) - 4 * (a * d - b * c)).
set (s := Complex_sqrt sqrt_term).
rewrite Cconj_minus_distr.
rewrite Cconj_half_distr.
rewrite Cconj_plus_distr.
rewrite Cconj_plus_distr.
rewrite Cmult_minus_distr_l.
repeat rewrite Cmult_minus_distr_r.
repeat rewrite Cmult_plus_distr_l.
rewrite half_half_mult.
rewrite half_mult_l. 
rewrite half_mult_r.
apply Cmult_cancel_r with (a:=RtoC 4). apply four_neq_0.
rewrite Cmult_0_l.
rewrite Cmult_plus_distr_r.
rewrite Cmult_minus_distr_r.
rewrite Cmult_minus_distr_r.
rewrite Cmult_minus_distr_r.
rewrite quarter_mult_4_r.
rewrite half_mult_4_r. rewrite half_mult_4_r.
repeat rewrite Cmult_minus_distr_l.
repeat rewrite Cmult_plus_distr_r.
repeat rewrite Cmult_plus_distr_l.
repeat rewrite Cmult_minus_distr_r.
repeat rewrite Cmult_plus_distr_r.
set (aa := a ^* * a).
set (ad := a ^* * d).
set (da := d ^* * a).
set (dd := d ^* * d).
set (sa := s ^* * a).
set (sd := s ^* * d).
set (as_ := a ^* * s).
set (ds := d ^* * s).
set (ss := s ^* * s).
set (cc := c ^* * c).
replace (aa + ad + (da + dd) + (sa + sd) - (as_ + ds + ss) -
(da * C2 + dd * C2 - ds * C2) - (ad * C2 + dd * C2 + sd * C2 - dd * 4) +
cc * 4) with ((aa) - (ad + da) + (dd) + (sa - as_) - (sd - ds) - (ss) +
cc * 4) by lca.
replace (da) with (ad ^*) by lca.
rewrite add_conj.
replace (ds) with (sd ^*) by lca.
rewrite sub_conj.
replace (as_) with (sa ^*) by lca.
rewrite sub_conj.
Admitted.