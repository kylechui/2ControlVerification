Require Import QuantumLib.Complex.
Lemma conj_mult_re_is_nonneg: forall (a: C),
Re (a^* * a) >= 0.
Proof.
intros.
unfold Re, Cconj, Cmult. simpl.
rewrite <- Ropp_mult_distr_l.
unfold Rminus.
rewrite Ropp_involutive.
apply Rle_ge.
apply Rplus_le_le_0_compat.
apply Rle_0_sqr.
apply Rle_0_sqr.
Qed.

Lemma conj_mult_im_is_0: forall (a: C),
Im (a^* * a) = 0.
Proof.
intros.
unfold Im, Cconj, Cmult.
simpl. lra.
Qed.

Lemma complex_split: forall (a b: C),
a = b  -> fst a = fst b /\ snd a = snd b.
Proof.
intros.
split.
rewrite H. reflexivity.
rewrite H. reflexivity.
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
apply complex_split in H3.
destruct H3 as [H3 _].
split.
{
    apply c_proj_eq. simpl.
    revert H3.
    apply Rplus_eq_0_l.
    apply Rge_le. apply H.
    apply Rge_le. apply H1.
    apply H0.
}
{
    apply c_proj_eq. simpl.
    revert H3.
    rewrite Rplus_comm.
    apply Rplus_eq_0_l.
    apply Rge_le. apply H1.
    apply Rge_le. apply H.
    apply H2.
}
Qed.


Lemma squared_norm_eq_0_implies_0 : forall (a : C),
a^* * a = C0 -> a = C0.
Proof.
  intro a.
  rewrite <- Cmod_sqr.
  unfold Cpow; rewrite Cmult_1_r.
  intro H.
  apply Cmod_eq_0, RtoC_inj.
  apply Cmult_integral in H; destruct H.
  - assumption.
  - assumption.
Qed.

Lemma sum_of_adjoints_re_nonneg: forall (b c d: C),
Re (b ^* * b + (c ^* * c + d ^* * d)) >= 0.
Proof.
intros.
unfold Re, Cplus.
simpl.
unfold Rminus.
repeat (rewrite <- Ropp_mult_distr_l; rewrite Ropp_involutive).
apply Rle_ge.
repeat (try apply Rplus_le_le_0_compat; try apply Rle_0_sqr).
Qed.

Lemma sum_of_adjoints_im_0: forall (b c d: C),
Im (b ^* * b + (c ^* * c + d ^* * d)) = 0.
Proof.
intros.
unfold Im, Cplus. simpl.
lra.
Qed.

Lemma sum_of_squared_norms_eq_0_implies_single_0: forall (a b c d: C),
a ^* * a + b ^* * b + c ^* * c + d ^* * d = 0 -> a = 0.
Proof.
intros.
repeat rewrite <- Cplus_assoc in H.
set (f := a^* * a).
set (g := b ^* * b + (c ^* * c + d ^* * d)).
assert (f+g = 0 -> f = 0).
{
    apply sum_of_pos_c_is_0_implies_0.
    apply conj_mult_re_is_nonneg.
    apply conj_mult_im_is_0.
    apply sum_of_adjoints_re_nonneg.
    apply sum_of_adjoints_im_0.
}
apply squared_norm_eq_0_implies_0.
apply H0.
apply H.
Qed.


Lemma sum_of_squared_norms_eq_0_implies_0: forall (a b c d: C),
a ^* * a + b ^* * b + c ^* * c + d ^* * d = 0 -> a = 0 /\ b = 0 /\ c = 0 /\ d= 0.
Proof.
split.
{
    apply sum_of_squared_norms_eq_0_implies_single_0 with (a:=a) (b:=b) (c:=c) (d:=d).  
    apply H.
}
split.
{
    assert (Step1: a ^* * a + b ^* * b + c ^* * c + d ^* * d = b ^* * b + a ^* * a  + c ^* * c + d ^* * d).
    {
        lca.
    }
    rewrite Step1 in H.
    apply sum_of_squared_norms_eq_0_implies_single_0 with (a:=b) (b:=a) (c:=c) (d:=d).
    apply H.
}
split.
{
    assert (Step1: a ^* * a + b ^* * b + c ^* * c + d ^* * d = c ^* * c + a ^* * a + b ^* * b + d ^* * d).
    {
        lca.
    }
    rewrite Step1 in H.
    apply sum_of_squared_norms_eq_0_implies_single_0 with (a:=c) (b:=a) (c:=b) (d:=d).
    apply H.
}
{
    assert (Step1: a ^* * a + b ^* * b + c ^* * c + d ^* * d = d ^* * d + a ^* * a + b ^* * b + c ^* * c).
    {
        lca.
    }
    rewrite Step1 in H.
    apply sum_of_squared_norms_eq_0_implies_single_0 with (a:=d) (b:=a) (c:=b) (d:=c).
    apply H.
}
Qed.

Lemma Cplus_cancel_l: forall (a b c: C),
  a + b = a + c -> b = c.
Proof.
  intros.
  rewrite <- (Cplus_0_l b).
  rewrite <- (Cplus_opp_l a).
  rewrite <- Cplus_assoc.
  rewrite H.
  lca.
Qed.

Lemma Cplus_cancel_r: forall (a b c: C),
  a + c = b + c -> a = b.
Proof.
  intros.
  rewrite <- (Cplus_0_r a).
  rewrite <- (Cplus_opp_r c).
  rewrite Cplus_assoc.
  rewrite H.
  lca.
Qed.

Lemma addition_equivalence: forall (a b c: C), 
a + b = c <-> b = c - a.
Proof.
split.
intros.
rewrite <- H.
lca.
intros.
rewrite H.
lca.
Qed.

Lemma opp_equivalence: forall (a b: C), 
a = b <-> -a = -b.
Proof.
  split.
  - intros.
    rewrite H; reflexivity.
  - intros.
    apply f_equal with (f := fun x => -x) in H.
    repeat rewrite Copp_involutive in H.
    exact H.
Qed.

(* If b = 0, then the value is real, in which case we should be using sqrt *)
(* Could do casework here, but I think it might make `lca` fail *)
Definition Complex_sqrt (x : C) : C :=
  let norm := Cmod x in
  let a := fst x in
  let b := snd x in
    if Req_EM_T b 0 then
      if Rlt_dec a 0 then
        (0, sqrt (- a))%R
      else
        (sqrt a, 0)
    else
      (√ ((norm + a) / 2), Rabs b / b * √ ((norm - a) / 2))%R.

Lemma Complex_sqrt_sqrt : forall (x : C),
  Complex_sqrt x * Complex_sqrt x = x.
Proof.
  intros.
  assert (H0 : forall (r s : R), r <= sqrt (r * r + s * s)).
  {
    intros.
    destruct (Rle_dec 0 r).
    - rewrite <- sqrt_square at 1. 2: assumption.
      apply sqrt_le_1_alt.
      rewrite <- Rplus_0_r at 1.
      apply Rplus_le_compat_l.
      apply Rle_0_sqr.
    - apply Rnot_le_lt in n.
      apply Rlt_le in n.
      pose proof (sqrt_pos (r * r + s * s)) as H0.
      apply Rle_trans with (r2 := 0); assumption.
  }
  assert (nonneg1 : 0 <= (Cmod x - fst x) / 2).
  {
    apply Rmult_le_pos.
    rewrite <- Rplus_opp_r with (r := fst x).
    apply Rplus_le_compat_r.
    unfold Cmod; unfold pow; repeat rewrite Rmult_1_r.
    apply H0.
    lra.
  }
  assert (nonneg2 : 0 <= (Cmod x + fst x) / 2).
  {
    apply Rmult_le_pos.
    rewrite <- Rplus_opp_l with (r := fst x).
    apply Rplus_le_compat_r.
    unfold Cmod; unfold pow; repeat rewrite Rmult_1_r.
    replace (fst x * fst x)%R with ((- fst x) * (- fst x))%R by lra.
    apply H0.
    lra.
  }
  assert (nonneg3 : 0 <= fst x * fst x + snd x * snd x).
  {
    apply Rplus_le_le_0_compat.
    apply Rle_0_sqr.
    apply Rle_0_sqr.
  }
  unfold Complex_sqrt, Cmult; simpl.
  destruct (Req_EM_T (snd x) 0); simpl.
  {
    destruct (Rlt_dec (fst x) 0); simpl.
    {
      destruct x; simpl.
      rewrite sqrt_sqrt.
      simpl in e.
      rewrite e.
      lca.
      simpl in r.
      lra.
    }
    {
      destruct x; simpl.
      rewrite sqrt_sqrt.
      simpl in e.
      rewrite e.
      lca.
      simpl in n.
      lra.
    }
  }
  rewrite sqrt_sqrt; auto.
  replace (Rabs (snd x) / snd x * √ ((Cmod x - fst x) / 2) *
  (Rabs (snd x) / snd x * √ ((Cmod x - fst x) / 2)))%R with ((Rabs (snd x) / snd x) * (Rabs (snd x) / snd x) * (√ ((Cmod x - fst x) / 2) * √ ((Cmod x - fst x) / 2)))%R by lra.
  rewrite sqrt_sqrt; auto.
  assert (step1 : forall (r : R), (Rabs r * Rabs r = r * r)%R).
  {
    intros.
    destruct (Rle_dec 0 r).
    - rewrite Rabs_right; auto.
      lra.
    - apply Rnot_le_lt in n0.
      rewrite Rabs_left; auto.
      lra.
  }
  assert (step2 : forall (r : R), r <> 0 -> (Rabs r / r * (Rabs r / r) = 1)%R).
  {
    intros.
    destruct (Rle_dec 0 r).
    - rewrite Rabs_right; auto.
      field.
      assumption.
      apply Rle_ge.
      assumption.
    - apply Rnot_le_lt in n0.
      rewrite Rabs_left; auto.
      field.
      assumption.
  }
  rewrite step2; auto; rewrite Rmult_1_l.
  replace ((Cmod x + fst x) / 2 - (Cmod x - fst x) / 2)%R with (fst x) by lra.
  rewrite Rmult_comm; rewrite Rmult_assoc.
  rewrite <- sqrt_mult; auto.
  replace ((Cmod x - fst x) / 2 * ((Cmod x + fst x) / 2))%R with ((Cmod x * Cmod x - fst x * fst x) / 4)%R by lra.
  unfold Cmod.
  unfold pow; repeat rewrite Rmult_1_r.
  rewrite sqrt_sqrt; auto.
  replace (fst x * fst x + snd x * snd x - fst x * fst x)%R with (snd x * snd x)%R by lra.
  replace (snd x * snd x / 4)%R with (snd x / 2 * (snd x / 2))%R by lra.
  destruct (Rge_dec (snd x) 0).
  - rewrite Rabs_right; auto.
    rewrite sqrt_square; auto.
    unfold Rdiv at 1 3; rewrite Rinv_r.
    rewrite Rmult_1_l.
    replace (snd x / 2 + snd x / 2)%R with (snd x)%R by lra.
    destruct x; simpl; reflexivity.
    assumption.
    lra.
  - apply Rnot_ge_lt in n0.
    rewrite Rabs_left; auto.
    unfold Rdiv at 1 4.
    rewrite <- Ropp_mult_distr_l.
    rewrite Rinv_r; auto.
    replace (snd x / 2 * (snd x / 2))%R with (- (snd x / 2) * (- (snd x / 2)))%R by lra.
    rewrite sqrt_square; auto.
    rewrite <- Ropp_mult_distr_r.
    rewrite Ropp_mult_distr_l, Ropp_involutive, Rmult_1_l.
    replace (snd x / 2 + snd x / 2)%R with (snd x)%R by lra.
    destruct x; simpl; reflexivity.
    lra.
Qed.

Lemma Cmult_const_r: forall (a b c : C), 
a = b -> a * c = b * c.
Proof. 
intros. 
rewrite H. 
reflexivity.
Qed.

Lemma cneq_implies_sub_neq: forall (a b : C), 
a <> b -> a - b <> 0.
Proof.
intros.
unfold not. 
intro. 
apply H.
apply (f_equal (fun f => f + b)) in H0.
rewrite Cplus_0_l in H0.
rewrite <- H0.
lca.
Qed.

Lemma Cmult_0_cancel_l: forall (a b : C), 
a <> 0 -> a * b = 0 -> b = 0.
Proof.
intros.
apply (f_equal (fun f => /a * f)) in H0.
rewrite Cmult_0_r in H0.
rewrite Cmult_assoc in H0.
rewrite Cinv_l in H0. rewrite Cmult_1_l in H0. 
all: assumption.
Qed.

Lemma Ceq_impl_minus_0: forall (a b: C),
a = b -> a - b = 0. 
Proof.
intros.
rewrite H. 
lca.
Qed. 

Lemma Ceq_opp_implies_0: forall (a : C), 
a = -a -> a = 0.
Proof.
intros.
apply (f_equal (fun f => f + a)) in H.
revert H.
replace (a + a) with (2 * a) by lca.
replace (-a + a) with (C0) by lca.
intro H.
apply (f_equal (fun f => /C2 * f)) in H.
rewrite Cmult_0_r in H.
rewrite Cmult_assoc in H.
rewrite Cinv_l in H. 2: apply RtoC_neq. 2: lra.
rewrite Cmult_1_l in H.
assumption.
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
apply RtoC_neq.
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
      rewrite <- Rsqr_pow2.
      rewrite Rsqr_neg.
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

Lemma conj_n0_iff_n0: forall (a : C), 
a <> 0 <-> a^* <> 0.
Proof.
split.
{
    intros.
    unfold not. 
    intro. 
    apply H.
    apply Cconj_simplify.
    rewrite Cconj_0.
    assumption.
}
{
    intros.
    unfold not. 
    intro. 
    apply H.
    rewrite H0.
    apply Cconj_0.
}
Qed.

Lemma Cmult_neq_0_implies_n0_arg: forall (a b c : C),
c = a * b -> c <> 0 -> a <> 0 /\ b <> 0.
Proof.
intros.
split.
{
    destruct (Ceq_dec a 0).
    contradict H0.
    rewrite H. 
    rewrite e.
    apply Cmult_0_l.
    assumption.
}
{
    destruct (Ceq_dec b 0).
    contradict H0.
    rewrite H. 
    rewrite e.
    apply Cmult_0_r.
    assumption.
}
Qed.

Lemma RtoC_conj (x: R): (RtoC x)^* = RtoC x.
Proof. intros. unfold RtoC, Cconj. apply c_proj_eq. simpl. reflexivity. simpl. lra. Qed.

Lemma Rfrac_product: forall (a b c d: R), 
b <> 0 -> d <> 0 -> (a/b * (c/d) = (a*c)/(b*d))%R.
Proof.
intros.
unfold Rdiv.
rewrite Rinv_mult_distr. 2,3: assumption.
lra.
Qed.

Lemma Cfrac_product: forall (a b c d: C), 
b <> 0 -> d <> 0 -> (a/b) * (c/d) = (a*c)/(b*d).
Proof.
intros.
unfold Cdiv.
rewrite Cinv_mult_distr. 2,3: assumption.
lca.
Qed.

Lemma g0_sqn0: forall (x : R), 
0 < x -> sqrt x <> 0.
Proof.
unfold not.
intros.
assert (0 <> x). apply Rlt_not_eq. assumption.
apply H1.
symmetry.
apply sqrt_eq_0.
apply Rlt_le.
all: assumption.
Qed. 

Lemma quadratic_formula: forall (a b c x: C), 
a <>0 -> x = / (C2 * a) * (- b + Complex_sqrt (b * b - 4 * a * c)) ->
x^2 * a + x * b + c = 0.
Proof.
intros a b c x an0 xdef.
rewrite xdef.
set (denom := C2 * a).
set (sqrt_term := b * b - 4 * a * c).
unfold Cpow.
rewrite Cmult_1_r.
replace (/ denom * (- b + Complex_sqrt sqrt_term) * (/ denom * (- b + Complex_sqrt sqrt_term)) * a) with 
((/ denom * / denom * a) * ((- b + Complex_sqrt sqrt_term) * (- b + Complex_sqrt sqrt_term))) by lca.
replace ((- b + Complex_sqrt sqrt_term) * (- b + Complex_sqrt sqrt_term)) with 
(b * b + - (2*b * Complex_sqrt sqrt_term) + Complex_sqrt sqrt_term * Complex_sqrt sqrt_term) by lca.
rewrite Complex_sqrt_sqrt.
unfold denom.
assert (const_n0: forall (c: C), c <> 0 -> c * a <> 0). 
{
    intros.
    unfold not. intro. apply H.
    apply Cmult_cancel_r with (a:= a).
    assumption. rewrite Cmult_0_l. assumption.
}
rewrite <- Cinv_mult_distr.
replace ((C2 * a * (C2 * a))) with ((4 * a) * a) by lca.
rewrite Cinv_mult_distr.
replace (/ (4 * a) * / a * a) with (/ (4 * a) * (/ a * a)) by lca.
rewrite Cinv_l.
rewrite Cmult_1_r.
replace (/ (C2 * a) * (- b + Complex_sqrt sqrt_term) * b) with 
(/ (C2 * a) * (- (b*b) + b* Complex_sqrt sqrt_term)) by lca.
replace (/ (C2 * a) * (- (b * b) + b * Complex_sqrt sqrt_term)) with 
(/ (C2 * a) * C1 * (- (b * b) + b * Complex_sqrt sqrt_term)) by lca.
rewrite <- Cinv_l with (r:= C2).
replace (/ (C2 * a) * (/ C2 * C2) * (- (b * b) + b * Complex_sqrt sqrt_term)) with
((/ (C2 * a) * / C2) * ((- C2 * (b * b) + C2 * b * Complex_sqrt sqrt_term))) by lca.
rewrite <- Cinv_mult_distr.
replace (C2 * a * C2) with (4 * a) by lca.
rewrite <- Cmult_plus_distr_l.
replace (b * b + - (C2 * b * Complex_sqrt sqrt_term) + sqrt_term +
(- C2 * (b * b) + C2 * b * Complex_sqrt sqrt_term)) with 
(sqrt_term - (b * b)) by lca.
unfold sqrt_term.
replace (b * b - 4 * a * c - b * b) with (- 4 * a * c) by lca.
replace (/ (4 * a) * (-4 * a * c)) with (/ (4 * a) * (4 * a) * -c) by lca.
rewrite Cinv_l.
lca.
1,2,6,8,9: apply const_n0.
8,9: assumption.
all: apply RtoC_neq.
all: lra.
Qed.