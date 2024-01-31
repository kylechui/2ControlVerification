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

Lemma sum_of_pos_c_is_0_implies_0: forall (a b: C),
Re a >= 0 -> Im a = 0 -> Re b >= 0 -> Im b = 0 ->
a + b = C0 -> a = C0 /\ b = C0.
Proof.
intros.
unfold Re in *; unfold Im in *.
unfold Cplus in H3.
rewrite H0 in H3.
rewrite H2 in H3.
apply pair_equal_spec in H3.
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

Lemma rtoc_neq_decomp: forall (r: R), 
(r <> 0)%R -> RtoC r <> C0.
Proof.
intros. 
unfold RtoC.
intro.
apply pair_equal_spec in H0.
destruct H0 as [H0 _].
apply H.
trivial.
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
rewrite Cinv_l in H. 2: apply rtoc_neq_decomp. 2: lra.
rewrite Cmult_1_l in H.
assumption.
Qed.
