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


Lemma squared_norm_eq_0_implies_0: forall (a: C),
a^* * a = 0 -> a = 0.
Proof.
intros.
apply c_proj_eq.
unfold Cconj in *; unfold Cmult in *.
simpl in *.
{
    apply Rsqr_0_uniq.
    assert (((fst a * fst a - - snd a * snd a)%R = 0 -> (fst a * fst a)%R = 0)).
    {
        rewrite <- Ropp_mult_distr_l.
        unfold Rminus. rewrite Ropp_involutive.
        apply Rplus_eq_0_l. apply Rle_0_sqr. apply Rle_0_sqr.
    }
    apply H0.
    inversion H.
    reflexivity.   
}
{
    apply Rsqr_0_uniq. 
    assert (((fst a * fst a - - snd a * snd a)%R = 0 -> (snd a * snd a)%R = 0)).
    {
        rewrite <- Ropp_mult_distr_l.
        unfold Rminus. rewrite Ropp_involutive.
        rewrite Rplus_comm.
        apply Rplus_eq_0_l. apply Rle_0_sqr. apply Rle_0_sqr.
    }
    apply H0.
    inversion H.
    reflexivity. 
}
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

Lemma C_l_cancel: forall (a b c: C), 
a + b = a + c -> b = c.
(* Thanks Kyle *)
Proof.
  intros.
  rewrite <- (Cplus_0_l b).
  rewrite <- (Cplus_opp_l a).
  rewrite <- Cplus_assoc.
  rewrite H.
  lca.
Qed.

Definition Csqrt (x : C) : C :=
  let norm := Cmod x in
  match x with
  | (a, b) => (sqrt ((norm + a) / 2), sqrt ((norm - a) / 2))
  end.
