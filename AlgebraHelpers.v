Require Import QuantumLib.Complex.
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