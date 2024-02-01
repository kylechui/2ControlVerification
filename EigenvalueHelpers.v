From Proof Require Import AlgebraHelpers.
From Proof Require Import ExplicitDecompositions.
From Proof Require Import MatrixHelpers.
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

Lemma neg_pow2: forall (a: R), 
(a ^ 2)%R = ((-a)^2)%R.
Proof.
intros.
unfold pow.
lra.
Qed.

Lemma Rle_lower_bound: forall (a b c d: R), 
a <= b + d -> b <= c -> a <= c + d.
Proof.
intros.
apply Rle_trans with (r2 := (b + d)%R).
assumption.
apply Rplus_le_compat_r.
assumption.
Qed.

Lemma Rabs_plus_le: forall (x : R), 
(0 <= Rabs x + x)%R.
Proof. 
intros.
unfold Rabs.
destruct (Rcase_abs x).
rewrite Rplus_opp_l.
apply Rle_refl.
replace (0%R) with ((2 * 0)%R) by lra.
replace ((x + x)%R) with ((2 * x)%R) by lra.
apply Rmult_le_compat_l. lra.
apply Rge_le. assumption.
Qed.

Lemma Rabs_minus_le: forall (x : R), 
(0 <= Rabs x + -x)%R.
Proof. 
intros.
unfold Rabs.
destruct (Rcase_abs x).
replace (0%R) with ((-(2) * 0)%R) by lra.
replace ((-x + - x)%R) with ((-(2) * x)%R) by lra.
apply Rmult_le_compat_neg_l. lra.
apply Rlt_le. assumption.
rewrite Rplus_opp_r.
apply Rle_refl.
Qed.

Lemma Rsqr_ge_0: forall (r: R), (0 <= (r)^2)%R.
Proof.
intros.
rewrite <- Rsqr_pow2.
destruct (Req_dec r 0).
rewrite H. unfold Rsqr. lra.
apply Rlt_le.
apply Rsqr_pos_lt.
assumption.
Qed.

Lemma sum_squares_pos: forall (a b : R), 
(0 <= a^2 + b^2)%R.
Proof.
intros.
rewrite <- Rplus_0_l with (r:= 0%R).
apply Rplus_le_compat.
all: apply Rsqr_ge_0.
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
      rewrite <- Rsqr_pow2.
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
      rewrite <- Rsqr_pow2.
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
    replace ((Rabs (snd x) / snd x * (Rabs (snd x) / snd x))%R) with
    (((Rabs (snd x) * Rabs (snd x)) *  ((/ snd x) * (/ snd x)))%R) by lra.
    replace ((Rabs (snd x) * Rabs (snd x))%R) with ((Rsqr (Rabs (snd x)))%R). 2: unfold Rsqr. 2: reflexivity.
    rewrite <- Rsqr_abs with (x:= snd x).
    unfold Rsqr.
    rewrite Rmult_assoc.
    rewrite <- Rmult_assoc with (r2 := (/ snd x)%R).
    rewrite Rinv_r.
    rewrite Rmult_1_l.
    rewrite Rinv_r.
    2,3: assumption.
    rewrite Rmult_1_r.
    unfold Rdiv.
    rewrite <- Rmult_plus_distr_r.
    replace (((Cmod x + fst x + (Cmod x + - fst x)) * / 2)%R) with (Cmod x) by lra.
    fold norm. reflexivity.
    all: rewrite <- Rmult_0_l with (r:= (/2)%R).
    all: unfold Rdiv.
    all: apply Rmult_le_compat_r.
    1,3: lra.
    all: unfold Cmod.
    all: apply Rle_lower_bound with (b := √ (fst x ^ 2)).
    1,3: rewrite <- Rsqr_pow2.
    1,2: rewrite sqrt_Rsqr_abs.
    apply Rabs_minus_le.
    apply Rabs_plus_le.
    all: apply sqrt_le_1.
    1,4: apply Rsqr_ge_0.
    1,3: apply sum_squares_pos.
    all: rewrite <- Rplus_0_r with (r:= (fst x ^ 2)%R) at 1.
    all: apply Rplus_le_compat.
    2,4: apply Rsqr_ge_0.
    all: apply Rle_refl.
  }
  {
    simpl.
    lra.
  }
}
Qed.

Definition WF_Hermitian {n} (A : Square n) := WF_Matrix A /\ A = A†.

Lemma gram_matrix_hermitian_2: forall (A : Square 2), 
WF_Matrix A -> WF_Hermitian (A† × A).
Proof.
intros.
unfold WF_Hermitian.
split. solve_WF_matrix.
lma'.
Qed.

Definition WF_PSD {n} (A : Square n) := WF_Hermitian A /\ forall (x: Vector n), WF_Matrix x -> 0 <= fst (⟨ A × x, x ⟩) /\ 0 = snd (⟨ A × x, x ⟩).

Lemma gram_matrix_psd_2: forall (A: Square 2), 
WF_Matrix A -> WF_PSD (A† × A).
Proof.
intros.
unfold WF_PSD.
split. apply gram_matrix_hermitian_2. assumption.
intros.
unfold inner_product.
rewrite Mmult_adjoint. rewrite Mmult_adjoint.
rewrite adjoint_involutive.
replace ((x) † × ((A) † × A) × x) with ((A × x) † × (A × x)) by lma'.
replace ((((A × x) † × (A × x)) 0%nat 0%nat)) with (⟨A × x, A × x⟩) by lca.
split. apply inner_product_ge_0. symmetry. apply norm_real.
Qed.

Lemma mult_adjoint_hermitian_2: forall (A : Square 2),
WF_Matrix A -> WF_Hermitian (A × A†).
Proof.
intros.
unfold WF_Hermitian.
split. solve_WF_matrix.
lma'.
Qed.

Lemma mult_adjoint_psd_2: forall (A : Square 2),
WF_Matrix A -> WF_PSD (A × A†).
intros.
unfold WF_PSD.
split. apply mult_adjoint_hermitian_2. assumption.
intros.
unfold inner_product.
rewrite Mmult_adjoint. rewrite Mmult_adjoint.
rewrite adjoint_involutive.
replace ((x) † × (A × (A) †) × x) with ((A† × x) † × (A† × x)) by lma'.
replace (((A† × x) † × (A† × x)) 0%nat 0%nat) with (⟨A† × x, A† × x⟩) by lca.
split. apply inner_product_ge_0. symmetry. apply norm_real.
Qed.

Lemma hermitian_inner_prod {n}: forall (A: Square n) (u v: Vector n), 
WF_Hermitian A -> ⟨ A × u, v ⟩ = ⟨ u, A × v ⟩.
Proof.
intros.
unfold inner_product.
rewrite Mmult_adjoint.
destruct H. rewrite <- H0.
rewrite <- Mmult_assoc.
reflexivity.
Qed.

Lemma hermitian_implies_real_eigenvalues {n}: forall (A: Square n), 
WF_Hermitian A -> forall (v : Vector n) (lambda : C), WF_Matrix v -> v <> Zero ->  
Eigenpair A (v, lambda) -> 0 = snd lambda.
intros A a_hermitian v lambda WF_v nonzero_v eigenpair_v_lambda.
revert eigenpair_v_lambda.
unfold Eigenpair. simpl.
intro eigenpair_v_lambda.
assert (hermitian_prop := hermitian_inner_prod A v v).
apply hermitian_prop in a_hermitian.
rewrite eigenpair_v_lambda in a_hermitian.
rewrite inner_product_scale_r, inner_product_scale_l in a_hermitian.
apply (f_equal (fun f => f * / (⟨ v, v ⟩))) in a_hermitian.
do 2 rewrite <- Cmult_assoc in a_hermitian.
rewrite Cinv_r in a_hermitian. 2: rewrite inner_product_zero_iff_zero. 2,3: assumption.
do 2 rewrite Cmult_1_r in a_hermitian.
rewrite surjective_pairing in a_hermitian.
apply pair_equal_spec in a_hermitian.
lra.
Qed.

Lemma psd_implies_nonneg_eigenvalues {n}: forall (A: Square n), 
WF_PSD A -> forall (v : Vector n) (lambda : C), WF_Matrix v -> v <> Zero ->  
Eigenpair A (v, lambda) -> 0 <= fst lambda /\ 0 = snd lambda.
intros A PSD v lambda WF_v nonzero_v eigenpair_v_lambda.
destruct PSD as [a_hermitian psd_prop].
specialize (psd_prop v).
rewrite hermitian_inner_prod in psd_prop. 2: assumption.
revert eigenpair_v_lambda.
unfold Eigenpair. simpl.
intro eigenpair_v_lambda.
rewrite eigenpair_v_lambda in psd_prop.
rewrite inner_product_scale_r in psd_prop.
set (vv:= ⟨ v, v ⟩).
fold vv in psd_prop.
assert (psd_spec: 0%R <= fst (lambda * vv) /\ 0%R = snd (lambda * vv)).
{
  apply psd_prop. apply WF_v.
}
revert psd_spec.
unfold Cmult.
replace (fst ((fst lambda * fst vv - snd lambda * snd vv)%R,
(fst lambda * snd vv + snd lambda * fst vv)%R)) with (fst lambda * fst vv - snd lambda * snd vv)%R by (simpl; reflexivity).
replace (snd
((fst lambda * fst vv - snd lambda * snd vv)%R,
(fst lambda * snd vv + snd lambda * fst vv)%R)) with (fst lambda * snd vv + snd lambda * fst vv)%R by (simpl; reflexivity).
replace (snd vv) with (0) by (symmetry; unfold vv; apply norm_real).
rewrite Rmult_0_r. rewrite Rmult_0_r.
rewrite Rminus_0_r. rewrite Rplus_0_l.
intro psd_spec.
destruct psd_spec as [psd_fst psd_snd].
assert (inner_gt_0: 0 < fst vv).
{
  assert (ge_0 := inner_product_ge_0 v).
  apply Rle_lt_or_eq_dec in ge_0.
  destruct ge_0.
  assumption.
  contradict nonzero_v.
  apply inner_product_zero_iff_zero. assumption.
  apply c_proj_eq.
  rewrite <- e.
  simpl. reflexivity.
  rewrite norm_real.
  simpl. reflexivity.
}
split.
{
  apply Rmult_le_reg_l with (r := fst vv).
  assumption.
  rewrite Rmult_0_r. rewrite Rmult_comm.
  assumption.
}
{
  apply (f_equal (fun f => (f * /(fst vv))%R)) in psd_snd.
  rewrite Rmult_assoc in psd_snd.
  rewrite Rinv_r in psd_snd. 2: apply Rgt_not_eq. 2: apply Rlt_gt. 2: assumption.
  rewrite Rmult_0_l in psd_snd. rewrite Rmult_1_r in psd_snd.
  assumption. 
}
Qed.

Lemma hermitian_implies_orthogonal_eigenvectors {n}: forall (A: Square n), 
WF_Hermitian A -> forall (v1 v2: Vector n) (l1 l2: C), 
WF_Matrix v1 -> WF_Matrix v2 -> v1 <> Zero -> 
l1 <> l2 ->
Eigenpair A (v1, l1) -> Eigenpair A (v2, l2) -> 
⟨ v1, v2 ⟩ = 0.
Proof.
intros A a_hermitian v1 v2 l1 l2 WF_v1 WF_v2 v1_nonz l1_neq_l2 eigenpair1 eigenpair2.
apply Cmult_0_cancel_l with (a:= (l1 - l2)).
apply Cminus_eq_contra. assumption.
rewrite Cmult_minus_distr_r.
apply Ceq_impl_minus_0.
assert (l1_real: l1 = l1^*).
{
  unfold Cconj.
  apply c_proj_eq.
  simpl. reflexivity.
  simpl.
  assert (real_eig:= hermitian_implies_real_eigenvalues A a_hermitian).
  specialize (real_eig v1 l1).
  apply real_eig in WF_v1. 2,3: assumption.
  rewrite <- WF_v1.
  lra.
}
rewrite l1_real.
rewrite <- inner_product_scale_l.
rewrite <- inner_product_scale_r.
unfold Eigenpair in eigenpair1, eigenpair2.
revert eigenpair1 eigenpair2.
simpl.
intros eigenpair1 eigenpair2.
rewrite <- eigenpair1, <- eigenpair2.
apply hermitian_inner_prod.
assumption.
Qed.
