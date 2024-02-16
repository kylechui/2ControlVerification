Require Import Proof.UnitaryMatrices.
Require Import Proof.AlgebraHelpers.
Require Import Proof.MatrixHelpers.
Require Import Proof.GateHelpers.
Require Import Proof.EigenvalueHelpers.
Require Import QuantumLib.Complex.
Require Import QuantumLib.Quantum.
Require Import QuantumLib.Eigenvectors.
Require Import QuantumLib.Matrix.

Lemma kron_uniq2: forall (a b c d : Vector 2),
  WF_Matrix a -> WF_Matrix b -> WF_Matrix c -> WF_Matrix d ->
  a <> Zero -> b <> Zero -> c <> Zero -> d <> Zero ->
  a ⊗ b = c ⊗ d -> exists (c1 c2: C), c1 .* a = c /\ c2 .* b = d.
Proof.
  assert (H1 : forall (a0 a1 b c0 c1 d : C),
  b <> C0 -> d <> C0 -> a0 * b = c0 * d -> a1 * b = c1 * d -> exists (k : C), k * a0 = c0 /\ k * a1 = c1).
  {
    intros.
    symmetry in H1.
    pose proof (Cmult_simplify _ _ _ _ H1 H2) as H3.
    replace (c0 * d * (a1 * b)) with (b * d * (a1 * c0)) in H3 by lca.
    replace (a0 * b * (c1 * d)) with (b * d * (a0 * c1)) in H3 by lca.
    assert (bd_nonzero : b * d <> C0) by (apply Cmult_neq_zero; assumption).
    pose proof (Cmult_cancel_l _ (a1 * c0) (a0 * c1) bd_nonzero H3) as H4.
    destruct (Ceq_dec a0 C0) as [a0_zero | a0_nonzero].
    {
      rewrite a0_zero.
      rewrite a0_zero, Cmult_0_l in H1.
      apply Cmult_integral in H1.
      destruct H1; try contradiction.
      rewrite H1.
      destruct (Ceq_dec a1 C0) as [a1_zero | a1_nonzero].
      {
        exists C0.
        rewrite a1_zero, Cmult_0_l in H2.
        symmetry in H2; apply Cmult_integral in H2.
        destruct H2; try contradiction.
        rewrite H2.
        split; lca.
      }
      {
        exists (c1 / a1).
        split.
        {
          lca.
        }
        {
          unfold Cdiv.
          rewrite <- Cmult_assoc.
          rewrite Cinv_l; auto.
          lca.
        }
      }
    }
    {
      destruct (Ceq_dec a1 C0) as [a1_zero | a1_nonzero].
      {
        rewrite a1_zero.
        rewrite a1_zero, Cmult_0_l in H2.
        symmetry in H2.
        apply Cmult_integral in H2.
        destruct H2; try contradiction.
        rewrite H2.
        exists (c0 / a0).
        split.
        {
          unfold Cdiv.
          rewrite <- Cmult_assoc.
          rewrite Cinv_l; auto.
          lca.
        }
        {
          lca.
        }
      }
      {
        exists (c0 / a0).
        split.
        {
          unfold Cdiv.
          rewrite <- Cmult_assoc.
          rewrite Cinv_l; auto.
          lca.
        }
        {
          replace (c0 / a0 * a1) with (a1 * c0 * / a0) by lca.
          rewrite H4.
          rewrite Cmult_comm.
          rewrite Cmult_assoc.
          rewrite Cinv_l; auto.
          lca.
        }
      }
    }
  }
  assert (H2 : forall (v w : Vector 2) (k : C),
    WF_Matrix v -> WF_Matrix w ->
    k * (v 0%nat 0%nat) = w 0%nat 0%nat ->
    k * (v 1%nat 0%nat) = w 1%nat 0%nat -> k .* v = w).
  {
    intros.
    unfold scale.
    prep_matrix_equality.
    unfold WF_Matrix in H, H0.
    specialize (H x y).
    specialize (H0 x y).
    destruct y.
    {
      destruct x.
      {
        assumption.
      }
      {
        destruct x.
        {
          assumption.
        }
        {
          assert (H4 : v (S (S x)) 0%nat = C0).
          {
            apply H.
            left.
            lia.
          }
          assert (H5 : w (S (S x)) 0%nat = C0).
          {
            apply H0.
            left.
            lia.
          }
          rewrite H4, H5.
          lca.
        }
      }
    }
    {
      assert (H4 : v x (S y) = C0).
      {
        apply H.
        right.
        lia.
      }
      assert (H5 : w x (S y) = C0).
      {
        apply H0.
        right.
        lia.
      }
      rewrite H4, H5.
      lca.
    }
  }
  assert (nonzero_def2 : forall (v : Vector 2), WF_Matrix v -> v <> Zero -> v 0%nat 0%nat <> C0 \/ v 1%nat 0%nat <> C0).
  {
    intros.
    destruct (Ceq_dec (v 1%nat 0%nat) C0).
    {
      left.
      unfold WF_Matrix in H.
      rewrite nonzero_def in H0.
      destruct H0 as [i [j H0]].
      specialize (H i j).
      destruct j.
      {
        destruct i.
        {
          assumption.
        }
        {
          destruct i.
          {
            contradiction.
          }
          {
            exfalso; apply H0.
            apply H.
            left.
            lia.
          }
        }
      }
      {
        exfalso.
        apply H0.
        apply H.
        right.
        lia.
      }
    }
    {
      right.
      assumption.
    }
  }
  intros a b c d WF_a WF_b WF_c WF_d an0 bn0 cn0 dn0 tens_eq.
  set (a0 := a 0%nat 0%nat).
  set (a1 := a 1%nat 0%nat).
  set (b0 := b 0%nat 0%nat).
  set (b1 := b 1%nat 0%nat).
  set (c0 := c 0%nat 0%nat).
  set (c1 := c 1%nat 0%nat).
  set (d0 := d 0%nat 0%nat).
  set (d1 := d 1%nat 0%nat).
  assert (ab0 : a0 * b0 = (a ⊗ b) 0%nat 0%nat). unfold a0, b0. lca.
  assert (ab1 : a0 * b1 = (a ⊗ b) 1%nat 0%nat). unfold a0, b1. lca.
  assert (ab2 : a1 * b0 = (a ⊗ b) 2%nat 0%nat). unfold a1, b0. lca.
  assert (ab3 : a1 * b1 = (a ⊗ b) 3%nat 0%nat). unfold a1, b1. lca.
  assert (cd0 : c0 * d0 = (c ⊗ d) 0%nat 0%nat). unfold c0, d0. lca.
  assert (cd1 : c0 * d1 = (c ⊗ d) 1%nat 0%nat). unfold c0, d1. lca.
  assert (cd2 : c1 * d0 = (c ⊗ d) 2%nat 0%nat). unfold c1, d0. lca.
  assert (cd3 : c1 * d1 = (c ⊗ d) 3%nat 0%nat). unfold c1, d1. lca.
  assert (el0: a0 * b0 = c0 * d0). rewrite ab0, cd0, tens_eq. reflexivity.
  assert (el1: a0 * b1 = c0 * d1). rewrite ab1, cd1, tens_eq. reflexivity.
  assert (el2: a1 * b0 = c1 * d0). rewrite ab2, cd2, tens_eq. reflexivity.
  assert (el3: a1 * b1 = c1 * d1). rewrite ab3, cd3, tens_eq. reflexivity.
  clear ab0 ab1 ab2 ab3 cd0 cd1 cd2 cd3.
  assert (a0_zero_iff_c0_zero : a0 = C0 <-> c0 = C0).
  {
    split.
    {
      intro.
      rewrite H in el0, el1.
      destruct (nonzero_def2 d WF_d dn0).
      {
        apply Cmult_cancel_r with (a := d0); auto.
        rewrite <- el0; lca.
      }
      {
        apply Cmult_cancel_r with (a := d1); auto.
        rewrite <- el1; lca.
      }
    }
    {
      intro.
      rewrite H in el0, el1.
      destruct (nonzero_def2 b WF_b bn0).
      {
        apply Cmult_cancel_r with (a := b0); auto.
        rewrite el0; lca.
      }
      {
        apply Cmult_cancel_r with (a := b1); auto.
        rewrite el1; lca.
      }
    }
  }
  assert (a1_zero_iff_c1_zero : a1 = C0 <-> c1 = C0).
  {
    split.
    {
      intro.
      rewrite H in el2, el3.
      destruct (nonzero_def2 d WF_d dn0).
      {
        apply Cmult_cancel_r with (a := d0); auto.
        rewrite <- el2; lca.
      }
      {
        apply Cmult_cancel_r with (a := d1); auto.
        rewrite <- el3; lca.
      }
    }
    {
      intro.
      rewrite H in el2, el3.
      destruct (nonzero_def2 b WF_b bn0).
      {
        apply Cmult_cancel_r with (a := b0); auto.
        rewrite el2; lca.
      }
      {
        apply Cmult_cancel_r with (a := b1); auto.
        rewrite el3; lca.
      }
    }
  }
  assert (b0_zero_iff_d0_zero : b0 = C0 <-> d0 = C0).
  {
    split.
    {
      intro.
      rewrite H in el0, el2.
      destruct (nonzero_def2 c WF_c cn0).
      {
        apply Cmult_cancel_l with (a := c0); auto.
        rewrite <- el0; lca.
      }
      {
        apply Cmult_cancel_l with (a := c1); auto.
        rewrite <- el2; lca.
      }
    }
    {
      intro.
      rewrite H in el0, el2.
      destruct (nonzero_def2 a WF_a an0).
      {
        apply Cmult_cancel_l with (a := a0); auto.
        rewrite el0; lca.
      }
      {
        apply Cmult_cancel_l with (a := a1); auto.
        rewrite el2; lca.
      }
    }
  }
  assert (b1_zero_iff_d1_zero : b1 = C0 <-> d1 = C0).
  {
    split.
    {
      intro.
      rewrite H in el1, el3.
      destruct (nonzero_def2 c WF_c cn0).
      {
        apply Cmult_cancel_l with (a := c0); auto.
        rewrite <- el1; lca.
      }
      {
        apply Cmult_cancel_l with (a := c1); auto.
        rewrite <- el3; lca.
      }
    }
    {
      intro.
      rewrite H in el1, el3.
      destruct (nonzero_def2 a WF_a an0).
      {
        apply Cmult_cancel_l with (a := a0); auto.
        rewrite el1; lca.
      }
      {
        apply Cmult_cancel_l with (a := a1); auto.
        rewrite el3; lca.
      }
    }
  }
  destruct (Ceq_dec a0 C0) as [a0_zero | a0_nonzero].
  {
    pose proof a0_zero as c0_zero; rewrite a0_zero_iff_c0_zero in c0_zero.
    destruct (nonzero_def2 a WF_a an0); try contradiction.
    destruct (nonzero_def2 c WF_c cn0); try contradiction.
    exists (c1 / a1).
    assert (a1c1_nonzero : a1 * c1 <> C0) by (apply Cmult_neq_zero; assumption).
    symmetry in el3.
    pose proof (Cmult_simplify _ _ _ _ el2 el3) as H3.
    replace (a1 * b0 * (c1 * d1)) with (a1 * c1 * (b0 * d1)) in H3 by lca.
    replace (c1 * d0 * (a1 * b1)) with (a1 * c1 * (b1 * d0)) in H3 by lca.
    apply Cmult_cancel_l in H3; auto.
    destruct (Ceq_dec b0 C0) as [b0_zero | b0_nonzero].
    {
      pose proof b0_zero as d0_zero; rewrite b0_zero_iff_d0_zero in d0_zero.
      destruct (nonzero_def2 b WF_b bn0); try contradiction.
      destruct (nonzero_def2 d WF_d dn0); try contradiction.
      exists (d1 / b1).
      split.
      {
        lma'.
        {
          unfold scale; simpl.
          fold a0 c0.
          rewrite a0_zero, c0_zero.
          lca.
        }
        {
          unfold scale; simpl.
          fold b0 d0.
          unfold Cdiv.
          rewrite <- Cmult_assoc.
          rewrite Cinv_l; auto.
          fold c1.
          lca.
        }
      }
      {
        lma'.
        {
          unfold scale; simpl.
          fold b0 d0.
          rewrite b0_zero, d0_zero.
          lca.
        }
        {
          unfold scale; simpl.
          fold b0 d0.
          unfold Cdiv.
          rewrite <- Cmult_assoc.
          rewrite Cinv_l; auto.
          fold d1.
          lca.
        }
      }
    }
    {
      exists (d0 / b0).
      split.
      {
        lma'.
        {
          unfold scale; simpl.
          fold a0 c0.
          rewrite a0_zero, c0_zero.
          lca.
        }
        {
          unfold scale; simpl.
          fold b0 d0.
          unfold Cdiv.
          rewrite <- Cmult_assoc.
          rewrite Cinv_l; auto.
          fold c1.
          lca.
        }
      }
      {
        lma'.
        {
          unfold scale; simpl.
          fold b0 d0.
          unfold Cdiv.
          rewrite <- Cmult_assoc.
          rewrite Cinv_l; auto.
          fold d0.
          lca.
        }
        {
          unfold scale, Cdiv; simpl.
          fold b1 d1.
          replace (d0 * / b0 * b1) with (b1 * d0 * / b0) by lca.
          rewrite <- H3.
          replace (b0 * d1 * / b0) with (b0 * / b0 * d1) by lca.
          rewrite Cinv_r; auto.
          lca.
        }
      }
    }
  }
  {
    exists (c0 / a0).
    assert (c0_nonzero : c0 <> C0).
    {
      intro contra.
      apply a0_nonzero.
      apply a0_zero_iff_c0_zero.
      exact contra.
    }
    assert (a0c0_nonzero : a0 * c0 <> C0) by (apply Cmult_neq_zero; assumption).
    symmetry in el1.
    pose proof (Cmult_simplify _ _ _ _ el0 el1) as H3.
    replace (a0 * b0 * (c0 * d1)) with (a0 * c0 * (b0 * d1)) in H3 by lca.
    replace (c0 * d0 * (a0 * b1)) with (a0 * c0 * (b1 * d0)) in H3 by lca.
    apply Cmult_cancel_l in H3; auto.
    destruct (Ceq_dec b0 C0) as [b0_zero | b0_nonzero].
    {
      pose proof b0_zero as d0_zero; rewrite b0_zero_iff_d0_zero in d0_zero.
      destruct (nonzero_def2 b WF_b bn0); try contradiction.
      destruct (nonzero_def2 d WF_d dn0); try contradiction.
      assert (b1d1_nonzero : b1 * d1 <> C0) by (apply Cmult_neq_zero; assumption).
      pose proof (Cmult_simplify _ _ _ _ el1 el3) as H6.
      replace (c0 * d1 * (a1 * b1)) with (a1 * c0 * (b1 * d1)) in H6 by lca.
      replace (a0 * b1 * (c1 * d1)) with (a0 * c1 * (b1 * d1)) in H6 by lca.
      apply Cmult_cancel_r in H6; auto.
      exists (d1 / b1).
      split.
      {
        lma'.
        {
          unfold scale, Cdiv; simpl.
          fold a0 c0.
          rewrite <- Cmult_assoc.
          rewrite Cinv_l; auto.
          lca.
        }
        {
          unfold scale, Cdiv; simpl.
          fold a1 c1.
          rewrite Cmult_comm.
          rewrite Cmult_assoc.
          rewrite H6.
          rewrite Cmult_comm.
          rewrite Cmult_assoc.
          rewrite Cinv_l; auto.
          lca.
        }
      }
      {
        lma'.
        {
          unfold scale, Cdiv; simpl.
          fold b0 d0.
          rewrite b0_zero, d0_zero.
          lca.
        }
        {
          unfold scale, Cdiv; simpl.
          fold b1 d1.
          rewrite <- Cmult_assoc.
          rewrite Cinv_l; auto.
          lca.
        }
      }
    }
    {
      exists (d0 / b0).
      split.
      {
        lma'.
        {
          unfold scale, Cdiv; simpl.
          fold a0 c0.
          rewrite <- Cmult_assoc.
          rewrite Cinv_l; auto.
          lca.
        }
        {
          assert (d0_nonzero : d0 <> C0).
          {
            intro contra.
            apply b0_nonzero.
            apply b0_zero_iff_d0_zero.
            exact contra.
          }
          assert (b0d0_nonzero : b0 * d0 <> C0) by (apply Cmult_neq_zero; assumption).
          symmetry in el0.
          pose proof (Cmult_simplify _ _ _ _ el0 el2) as H6.
          replace (c0 * d0 * (a1 * b0)) with (a1 * c0 * (b0 * d0)) in H6 by lca.
          replace (a0 * b0 * (c1 * d0)) with (a0 * c1 * (b0 * d0)) in H6 by lca.
          apply Cmult_cancel_r in H6; auto.
          unfold scale, Cdiv; simpl.
          fold a1 c1.
          rewrite Cmult_comm.
          rewrite Cmult_assoc.
          rewrite H6.
          rewrite Cmult_comm.
          rewrite Cmult_assoc.
          rewrite Cinv_l; auto.
          lca.
        }
      }
      {
        lma'.
        {
          unfold scale, Cdiv; simpl.
          fold b0 d0.
          rewrite <- Cmult_assoc.
          rewrite Cinv_l; auto.
          lca.
        }
        {
          unfold scale, Cdiv; simpl.
          fold b1 d1.
          rewrite Cmult_comm.
          rewrite Cmult_assoc.
          rewrite <- H3.
          rewrite Cmult_comm.
          rewrite Cmult_assoc.
          rewrite Cinv_l; auto.
          lca.
        }
      }
    }
  }
Qed.

Lemma m3_2 : forall (u0 u1 : C),
  Cmod u0 = 1 -> Cmod u1 = 1 ->
  (exists (P Q : Square 2),
    WF_Unitary P /\ WF_Unitary Q /\
    (exists (a b p q : C) (v1 v2 v3 v4 : Vector 2),
      WF_Matrix v1 /\ WF_Matrix v2 /\ WF_Matrix v3 /\ WF_Matrix v4 /\
      v1 <> Zero /\ v2 <> Zero /\ v3 <> Zero /\ v4 <> Zero /\
      Eigenpair P (v1, a) /\ Eigenpair P (v2, b) /\
      Eigenpair Q (v3, p) /\ Eigenpair Q (v4, q) /\
        (Eigenpair (P ⊗ Q) (v1 ⊗ v3, C1) /\
        Eigenpair (P ⊗ Q) (v1 ⊗ v4, C1) /\
        Eigenpair (P ⊗ Q) (v2 ⊗ v3, u0) /\
        Eigenpair (P ⊗ Q) (v2 ⊗ v4, u1) \/
        Eigenpair (P ⊗ Q) (v1 ⊗ v3, C1) /\
        Eigenpair (P ⊗ Q) (v1 ⊗ v4, u1) /\
        Eigenpair (P ⊗ Q) (v2 ⊗ v3, u0) /\
        Eigenpair (P ⊗ Q) (v2 ⊗ v4, C1))))
  <-> u0 = u1 \/ u0 * u1 = C1.
Proof.
  intros u0 u1 unit_u0 unit_u1.
  split.
  {
    intro.
    destruct H as [P [Q [Unitary_P [Unitary_Q H]]]].
    destruct H as [a [b [p [q [v1 [v2 [v3 [v4 H]]]]]]]].
    destruct H as [WF_v1 [WF_v2 [WF_v3 [WF_v4 H]]]].
    destruct H as [v1_nonzero [v2_nonzero [v3_nonzero [v4_nonzero H]]]].
    destruct H as [epair1 [epair2 [epair3 [epair4 H]]]].
    assert (WF_P : WF_Matrix P).
    {
      destruct Unitary_P.
      assumption.
    }
    assert (WF_Q : WF_Matrix Q).
    {
      destruct Unitary_Q.
      assumption.
    }
    destruct H.
    {
      destruct H as [epair5 [epair6 [epair7 epair8]]].
      assert (help1 : a * p = C1).
      {
        pose proof (
          a5_left
          P Q
          Unitary_P Unitary_Q
          a p v1 v3
          WF_v1 WF_v3
          epair1 epair3
        ) as H.
        unfold Eigenpair in epair5, H; simpl in epair5, H.
        rewrite epair5 in H.
        apply @Mscale_cancel_r with (A := v1 ⊗ v3) (m := 4%nat) (n := 1%nat); auto.
        solve_WF_matrix.
        apply nonzero_kron; auto.
      }
      assert (help2 : a * q = C1).
      {
        pose proof (
          a5_left
          P Q
          Unitary_P Unitary_Q
          a q v1 v4
          WF_v1 WF_v4
          epair1 epair4
        ) as H.
        unfold Eigenpair in epair6, H; simpl in epair6, H.
        rewrite epair6 in H.
        apply @Mscale_cancel_r with (A := v1 ⊗ v4) (m := 4%nat) (n := 1%nat); auto.
        solve_WF_matrix.
        apply nonzero_kron; auto.
      }
      assert (help3 : b * p = u0).
      {
        pose proof (
          a5_left
          P Q
          Unitary_P Unitary_Q
          b p v2 v3
          WF_v2 WF_v3
          epair2 epair3
        ) as H.
        unfold Eigenpair in epair7, H; simpl in epair7, H.
        rewrite epair7 in H.
        apply @Mscale_cancel_r with (A := v2 ⊗ v3) (m := 4%nat) (n := 1%nat); auto.
        solve_WF_matrix.
        apply nonzero_kron; auto.
      }
      assert (help4 : b * q = u1).
      {
        pose proof (
          a5_left
          P Q
          Unitary_P Unitary_Q
          b q v2 v4
          WF_v2 WF_v4
          epair2 epair4
        ) as H.
        unfold Eigenpair in epair8, H; simpl in epair8, H.
        rewrite epair8 in H.
        apply @Mscale_cancel_r with (A := v2 ⊗ v4) (m := 4%nat) (n := 1%nat); auto.
        solve_WF_matrix.
        apply nonzero_kron; auto.
      }
      left.
      rewrite <- help3, <- help4.
      rewrite <- Cmult_1_l with (x := b).
      rewrite <- help2 at 1.
      rewrite <- help1 at 1.
      lca.
    }
    {
      destruct H as [epair5 [epair6 [epair7 epair8]]].
      assert (help1 : a * p = C1).
      {
        pose proof (
          a5_left
          P Q
          Unitary_P Unitary_Q
          a p v1 v3
          WF_v1 WF_v3
          epair1 epair3
        ) as H.
        unfold Eigenpair in epair5, H; simpl in epair5, H.
        rewrite epair5 in H.
        apply @Mscale_cancel_r with (A := v1 ⊗ v3) (m := 4%nat) (n := 1%nat); auto.
        solve_WF_matrix.
        apply nonzero_kron; auto.
      }
      assert (help2 : a * q = u1).
      {
        pose proof (
          a5_left
          P Q
          Unitary_P Unitary_Q
          a q v1 v4
          WF_v1 WF_v4
          epair1 epair4
        ) as H.
        unfold Eigenpair in epair6, H; simpl in epair6, H.
        rewrite epair6 in H.
        apply @Mscale_cancel_r with (A := v1 ⊗ v4) (m := 4%nat) (n := 1%nat); auto.
        solve_WF_matrix.
        apply nonzero_kron; auto.
      }
      assert (help3 : b * p = u0).
      {
        pose proof (
          a5_left
          P Q
          Unitary_P Unitary_Q
          b p v2 v3
          WF_v2 WF_v3
          epair2 epair3
        ) as H.
        unfold Eigenpair in epair7, H; simpl in epair7, H.
        rewrite epair7 in H.
        apply @Mscale_cancel_r with (A := v2 ⊗ v3) (m := 4%nat) (n := 1%nat); auto.
        solve_WF_matrix.
        apply nonzero_kron; auto.
      }
      assert (help4 : b * q = C1).
      {
        pose proof (
          a5_left
          P Q
          Unitary_P Unitary_Q
          b q v2 v4
          WF_v2 WF_v4
          epair2 epair4
        ) as H.
        unfold Eigenpair in epair8, H; simpl in epair8, H.
        rewrite epair8 in H.
        apply @Mscale_cancel_r with (A := v2 ⊗ v4) (m := 4%nat) (n := 1%nat); auto.
        solve_WF_matrix.
        apply nonzero_kron; auto.
      }
      right.
      rewrite <- help2, <- help3.
      rewrite <- Cmult_1_l with (x := C1).
      rewrite <- help1 at 1.
      rewrite <- help4 at 1.
      lca.
    }
  }
  {
    intros.
    destruct H.
    {
      exists (diag2 1 u1), (I 2).
      split.
      {
        unfold WF_Unitary.
        split.
        {
          apply WF_diag2.
        }
        {
          lma'.
          solve_WF_matrix.
          apply WF_diag2.
          apply WF_diag2.
          unfold diag2, I, adjoint, Mmult; simpl.
          Csimpl.
          rewrite <- Cmod_sqr.
          rewrite unit_u1.
          lca.
        }
      }
      split.
      {
        apply id_unitary.
      }
      exists C1, u1, C1, C1.
      exists ∣0⟩, ∣1⟩, ∣0⟩, ∣1⟩.
      split.
      {
        apply WF_qubit0.
      }
      split.
      {
        apply WF_qubit1.
      }
      split.
      {
        apply WF_qubit0.
      }
      split.
      {
        apply WF_qubit1.
      }
      split.
      {
        apply nonzero_qubit0.
      }
      split.
      {
        apply nonzero_qubit1.
      }
      split.
      {
        apply nonzero_qubit0.
      }
      split.
      {
        apply nonzero_qubit1.
      }
      split.
      {
        apply diag2_eigenpairs.
      }
      split.
      {
        apply diag2_eigenpairs.
      }
      split.
      {
        apply id2_eigenpairs.
      }
      split.
      {
        apply id2_eigenpairs.
      }
      left.
      split.
      {
        unfold Eigenpair.
        lma'; simpl.
        solve_WF_matrix.
        apply WF_diag2.
        solve_WF_matrix.
      }
      split.
      {
        unfold Eigenpair.
        lma'; simpl.
        solve_WF_matrix.
        apply WF_diag2.
        solve_WF_matrix.
      }
      split.
      {
        rewrite H.
        unfold Eigenpair.
        lma'; simpl.
        solve_WF_matrix.
        apply WF_diag2.
        solve_WF_matrix.
        unfold scale, Mmult, kron, diag2, I; simpl.
        lca.
      }
      {
        unfold Eigenpair.
        lma'; simpl.
        solve_WF_matrix.
        apply WF_diag2.
        solve_WF_matrix.
        unfold scale, Mmult, kron, diag2, I; simpl.
        lca.
      }
    }
    {
      exists (diag2 1 u0), (diag2 1 u1).
      split.
      {
        unfold WF_Unitary.
        split.
        {
          apply WF_diag2.
        }
        {
          lma'.
          solve_WF_matrix.
          apply WF_diag2.
          apply WF_diag2.
          unfold diag2, I, adjoint, Mmult; simpl.
          Csimpl.
          rewrite <- Cmod_sqr.
          rewrite unit_u0.
          lca.
        }
      }
      split.
      {
        unfold WF_Unitary.
        split.
        {
          apply WF_diag2.
        }
        {
          lma'.
          solve_WF_matrix.
          apply WF_diag2.
          apply WF_diag2.
          unfold diag2, I, adjoint, Mmult; simpl.
          Csimpl.
          rewrite <- Cmod_sqr.
          rewrite unit_u1.
          lca.
        }
      }
      exists C1, u0, C1, u1.
      exists ∣0⟩, ∣1⟩, ∣0⟩, ∣1⟩.
      split.
      {
        apply WF_qubit0.
      }
      split.
      {
        apply WF_qubit1.
      }
      split.
      {
        apply WF_qubit0.
      }
      split.
      {
        apply WF_qubit1.
      }
      split.
      {
        apply nonzero_qubit0.
      }
      split.
      {
        apply nonzero_qubit1.
      }
      split.
      {
        apply nonzero_qubit0.
      }
      split.
      {
        apply nonzero_qubit1.
      }
      split.
      {
        apply diag2_eigenpairs.
      }
      split.
      {
        apply diag2_eigenpairs.
      }
      split.
      {
        apply diag2_eigenpairs.
      }
      split.
      {
        apply diag2_eigenpairs.
      }
      right.
      split.
      {
        lma'.
        solve_WF_matrix.
        apply WF_diag2.
        apply WF_diag2.
        solve_WF_matrix.
      }
      split.
      {
        lma'.
        solve_WF_matrix.
        apply WF_diag2.
        apply WF_diag2.
        solve_WF_matrix.
        unfold scale, Mmult, kron, diag2, I, qubit0, qubit1; simpl.
        lca.
      }
      split.
      {
        lma'.
        solve_WF_matrix.
        apply WF_diag2.
        apply WF_diag2.
        solve_WF_matrix.
        unfold scale, Mmult, kron, diag2, I, qubit0, qubit1; simpl.
        lca.
      }
      {
        lma'.
        solve_WF_matrix.
        apply WF_diag2.
        apply WF_diag2.
        solve_WF_matrix.
        unfold scale, Mmult, kron, diag2, I, qubit0, qubit1; simpl.
        rewrite H.
        lca.
      }
    }
  }
Qed.

Lemma m4_1 : forall (u0 u1 : C),
  Cmod u0 = 1 -> Cmod u1 = 1 ->
    (exists (U V : Square 4) (P0 P1 Q0 Q1: Square 2),
      WF_Unitary U /\ WF_Unitary V /\ WF_Unitary P0 /\ WF_Unitary P1 /\ WF_Unitary Q0 /\ WF_Unitary Q1 /\
      ∣0⟩⟨0∣ ⊗ (U × (P0 ⊗ Q0) × V) .+ ∣1⟩⟨1∣ ⊗ (U × (P1 ⊗ Q1) × V) = ccu (diag2 u0 u1))
    <-> u0 = u1 \/ u0 * u1 = 1.
Proof.
  split.
  - admit.
  - intros.
    destruct H1.
    + exists (I 4), (I 4), (I 2), (diag2 1 u1), (I 2), (I 2).
      assert (diag2_unitary : WF_Unitary (diag2 1 u1)).
      {
        split.
        - apply WF_diag2.
        - solve_matrix.
          unfold diag2; simpl.
          rewrite <- Cmod_sqr.
          rewrite H0.
          lca.
      }
      split. apply id_unitary.
      split. apply id_unitary.
      split. apply id_unitary.
      split. apply diag2_unitary.
      split. apply id_unitary.
      split. apply id_unitary.
      (* This line removes a lot of subgoals created by the following Msimpl *)
      assert (WF_my_diag2 : WF_Matrix (diag2 1 u1)). apply WF_diag2.
      Msimpl.
      lma'.
      do 2 apply WF_control; apply WF_diag2.
      {
        unfold kron, adjoint, Mmult, Mplus, ccu, control, diag2, I, qubit0, qubit1; simpl.
        Csimpl.
        symmetry; exact H1.
      }
      {
        unfold kron, adjoint, Mmult, Mplus, ccu, control, diag2, I, qubit0, qubit1; simpl.
        Csimpl.
        reflexivity.
      }
    + exists notc, notc, (I 2), (diag2 1 u0), (I 2), (diag2 1 u1).
      assert (diag2_unitary : forall u, Cmod u = 1 -> WF_Unitary (diag2 1 u)).
      {
        split.
        - apply WF_diag2.
        - solve_matrix.
          unfold diag2; simpl.
          rewrite <- Cmod_sqr.
          rewrite H2.
          lca.
      }
      split. apply notc_unitary.
      split. apply notc_unitary.
      split. apply id_unitary.
      split. apply diag2_unitary; exact H.
      split. apply id_unitary.
      split. apply diag2_unitary; exact H0.
      (* This line removes a lot of subgoals created by the following Msimpl *)
      assert (WF_my_diag2 : WF_Matrix (diag2 u0 1)). apply WF_diag2.
      Msimpl.
      lma'.
      {
        apply WF_plus.
        - apply WF_kron. lia. lia.
          solve_WF_matrix.
          apply WF_mult.
          solve_WF_matrix.
          apply WF_notc.
        - apply WF_kron. lia. lia.
          solve_WF_matrix.
          apply WF_mult.
          solve_WF_matrix.
          apply WF_diag2.
          apply WF_diag2.
          apply WF_notc.
      }
      do 2 apply WF_control; apply WF_diag2.
      {
        unfold kron, adjoint, Mmult, Mplus, ccu, control, diag2, I, qubit0, qubit1; simpl.
        Csimpl.
        assumption.
      }
      {
        unfold kron, adjoint, Mmult, Mplus, ccu, control, diag2, I, qubit0, qubit1; simpl.
        Csimpl.
        reflexivity.
      }
      {
        unfold kron, adjoint, Mmult, Mplus, ccu, control, diag2, I, qubit0, qubit1; simpl.
        Csimpl.
        reflexivity.
      }
Admitted.

Lemma m4_2 : forall (u0 u1 : C),
  Cmod u0 = 1 -> Cmod u1 = 1 ->
  forall (Q : Square 2),
    WF_Unitary Q ->
    let beta : Vector 2 := Q × ∣0⟩ in
    let beta_perp := Q × ∣1⟩ in
    (exists (P0 P1 : Square 2) (a b p q : C) (v1 v2 v3 v4 : Vector 2),
      WF_Unitary P0 /\ WF_Unitary P1 /\
      WF_Matrix v1 /\ WF_Matrix v2 /\ WF_Matrix v3 /\ WF_Matrix v4 /\
      v1 <> Zero /\ v2 <> Zero /\ v3 <> Zero /\ v4 <> Zero /\
      Eigenpair P0 (v1, a) /\ Eigenpair P0 (v2, b) /\
      Eigenpair P1 (v3, p) /\ Eigenpair P1 (v4, q) /\
      I 2 ⊗ I 2 ⊗ (beta × beta†) .+ P0 ⊗ P1 ⊗ (beta_perp × beta_perp†) = ccu (diag2 u0 u1))
    <-> u0 = 1 /\ u1 = 1.
Proof.
  intros.
  assert (WF_Q : WF_Matrix Q).
  {
    destruct H1.
    assumption.
  }
  assert (WF_beta : WF_Matrix beta) by solve_WF_matrix.
  assert (WF_beta_perp : WF_Matrix beta_perp) by solve_WF_matrix.
  assert (WF_beta_beta : WF_Matrix (beta × beta†)).
  {
    apply WF_mult.
    assumption.
    apply WF_adjoint.
    assumption.
  }
  pose (a := beta 0%nat 0%nat).
  pose (b := beta 1%nat 0%nat).
  split.
  - intros.
    destruct H2 as [P0 [P1 [c1 [c2 [c3 [c4 [v1 [v2 [v3 [v4 H2]]]]]]]]]].
    destruct H2 as [Unitary_P0 [Unitary_P1 H2]].
    destruct H2 as [WF_v1 [WF_v2 [WF_v3 [WF_v4 H2]]]].
    destruct H2 as [v1_nonzero [v2_nonzero [v3_nonzero [v4_nonzero H2]]]].
    destruct H2 as [epair1 [epair2 [epair3 [epair4 H2]]]].
    destruct (Ceq_dec a C0) as [a_zero | a_nonzero].
    + assert (unit_b : b^* * b = 1).
      {
        destruct H1.
        apply (f_equal (fun f => f 0%nat 0%nat)) in H3.
        unfold Mmult, adjoint, I in H3.
        simpl in H3.
        replace (Q 0%nat 0%nat) with a in H3 by lca.
        replace (Q 1%nat 0%nat) with b in H3 by lca.
        rewrite <- H3.
        rewrite a_zero.
        lca.
      }
      assert (beta_mult_1_1 : beta × beta† = ∣1⟩⟨1∣).
      {
        unfold beta, adjoint, qubit0, qubit1, Mmult.
        simpl.
        lma'.
        all: replace (Q 0%nat 0%nat) with a by lca.
        all: replace (Q 1%nat 0%nat) with b by lca.
        - rewrite a_zero.
          Csimpl.
          reflexivity.
        - rewrite a_zero.
          Csimpl.
          reflexivity.
        - rewrite a_zero.
          Csimpl.
          reflexivity.
        - Csimpl.
          rewrite Cmult_comm.
          rewrite unit_b.
          reflexivity.
      }
      assert (beta_perp_mult_0_0 : beta_perp × (beta_perp) † = ∣0⟩⟨0∣).
      {
        pose proof (a8 Q H1) as H3.
        unfold beta, beta_perp.
        apply Mplus_cancel_l with (A := ∣1⟩⟨1∣).
        rewrite Mplus10.
        rewrite <- H3.
        rewrite <- beta_mult_1_1.
        unfold beta.
        reflexivity.
      }
      rewrite beta_mult_1_1 in H2.
      rewrite beta_perp_mult_0_0 in H2.
      assert (u1_is_1 : u1 = C1).
      {
        apply f_equal with (f := fun f => f 7%nat 7%nat) in H2.
        unfold kron, Mmult, Mplus, adjoint, ccu, control, diag2, I, qubit0, qubit1 in H2; simpl in H2.
        revert H2; Csimpl; intro H2.
        auto.
      }
      assert (u0_is_1 : u0 = C1).
      {
        pose proof H2 as H3.
        pose proof H2 as H4.
        pose proof H2 as H5.
        pose proof H2 as H6.
        apply f_equal with (f := fun f => f 0%nat 0%nat) in H3.
        unfold kron, Mmult, Mplus, adjoint, ccu, control, diag2, I, qubit0, qubit1 in H3; simpl in H3.
        revert H3; Csimpl; intro H3.
        apply f_equal with (f := fun f => f 2%nat 2%nat) in H4.
        unfold kron, Mmult, Mplus, adjoint, ccu, control, diag2, I, qubit0, qubit1 in H4; simpl in H4.
        revert H4; Csimpl; intro H4.
        apply f_equal with (f := fun f => f 4%nat 4%nat) in H5.
        unfold kron, Mmult, Mplus, adjoint, ccu, control, diag2, I, qubit0, qubit1 in H5; simpl in H5.
        revert H5; Csimpl; intro H5.
        apply f_equal with (f := fun f => f 6%nat 6%nat) in H6.
        unfold kron, Mmult, Mplus, adjoint, ccu, control, diag2, I, qubit0, qubit1 in H6; simpl in H6.
        revert H6; Csimpl; intro H6.
        rewrite <- Cmult_1_l at 1.
        rewrite <- Cmult_1_l.
        rewrite <- H3 at 1.
        rewrite <- H4 at 1.
        rewrite <- H5 at 1.
        rewrite <- H6 at 1.
        lca.
      }
      split; auto.
    + destruct (Ceq_dec b C0) as [b_zero | b_nonzero].
      * assert (unit_a : a^* * a = 1).
        {
          destruct H1.
          apply (f_equal (fun f => f 0%nat 0%nat)) in H3.
          unfold Mmult, adjoint, I in H3.
          simpl in H3.
          replace (Q 0%nat 0%nat) with a in H3 by lca.
          replace (Q 1%nat 0%nat) with b in H3 by lca.
          rewrite <- H3.
          rewrite b_zero.
          lca.
        }
        assert (beta_mult_0_0 : beta × beta† = ∣0⟩⟨0∣).
        {
          unfold beta, adjoint, qubit0, qubit1, Mmult.
          simpl.
          lma'.
          all: replace (Q 0%nat 0%nat) with a by lca.
          all: replace (Q 1%nat 0%nat) with b by lca.
          Csimpl.
          rewrite Cmult_comm.
          rewrite unit_a.
          reflexivity.
          rewrite b_zero.
          Csimpl.
          reflexivity.
          rewrite b_zero.
          Csimpl.
          reflexivity.
          rewrite b_zero.
          Csimpl.
          reflexivity.
        }
        assert (beta_perp_mult_1_1 : beta_perp × (beta_perp) † = ∣1⟩⟨1∣).
        {
          pose proof (a8 Q H1) as H3.
          replace (Q × ∣0⟩) with beta in H3 by reflexivity.
          replace (Q × ∣1⟩) with beta_perp in H3 by reflexivity.
          rewrite beta_mult_0_0 in H3.
          rewrite <- Mplus01 in H3.
          apply Mplus_cancel_l in H3.
          assumption.
        }
        rewrite beta_mult_0_0 in H2.
        rewrite beta_perp_mult_1_1 in H2.
        assert (u0_is_1 : u0 = C1).
        {
          apply f_equal with (f := fun f => f 6%nat 6%nat) in H2.
          unfold kron, Mmult, Mplus, adjoint, ccu, control, diag2, I, qubit0, qubit1 in H2; simpl in H2.
          revert H2; Csimpl; intro H2.
          auto.
        }
        assert (u1_is_1 : u1 = C1).
        {
          pose proof H2 as H3.
          pose proof H2 as H4.
          pose proof H2 as H5.
          pose proof H2 as H6.
          apply f_equal with (f := fun f => f 1%nat 1%nat) in H3.
          unfold kron, Mmult, Mplus, adjoint, ccu, control, diag2, I, qubit0, qubit1 in H3; simpl in H3.
          revert H3; Csimpl; intro H3.
          apply f_equal with (f := fun f => f 3%nat 3%nat) in H4.
          unfold kron, Mmult, Mplus, adjoint, ccu, control, diag2, I, qubit0, qubit1 in H4; simpl in H4.
          revert H4; Csimpl; intro H4.
          apply f_equal with (f := fun f => f 5%nat 5%nat) in H5.
          unfold kron, Mmult, Mplus, adjoint, ccu, control, diag2, I, qubit0, qubit1 in H5; simpl in H5.
          revert H5; Csimpl; intro H5.
          apply f_equal with (f := fun f => f 7%nat 7%nat) in H6.
          unfold kron, Mmult, Mplus, adjoint, ccu, control, diag2, I, qubit0, qubit1 in H6; simpl in H6.
          revert H6; Csimpl; intro H6.
          rewrite <- Cmult_1_l at 1.
          rewrite <- Cmult_1_l.
          rewrite <- H3 at 1.
          rewrite <- H4 at 1.
          rewrite <- H5 at 1.
          rewrite <- H6 at 1.
          lca.
        }
        split; assumption.
      * apply (f_equal (fun f => f × (∣1⟩ ⊗ ∣1⟩ ⊗ beta))) in H2.
        assert (H3 : beta_perp† × beta = Zero).
        {
          unfold beta_perp, beta.
          rewrite Mmult_adjoint.
          rewrite <- Mmult_assoc.
          rewrite Mmult_assoc with (A := ⟨1∣).
          destruct H1.
          rewrite H3.
          rewrite Mmult_1_r. 2: exact (WF_bra 1).
          exact Mmult10.
        }
        assert (H4 : beta† × beta = I 1).
        {
          unfold beta, beta_perp.
          rewrite Mmult_adjoint.
          rewrite <- Mmult_assoc.
          do 2 rewrite Mmult_assoc.
          rewrite <- Mmult_assoc with (B := Q).
          destruct H1.
          rewrite H4.
          Msimpl.
          exact Mmult00.
        }
        rewrite Mmult_plus_distr_r in H2.
        assert (step1 : I 2 ⊗ I 2 ⊗ (beta × (beta) †) × (∣1⟩ ⊗ ∣1⟩ ⊗ beta) = ∣1⟩ ⊗ ∣1⟩ ⊗ beta).
        {
          repeat rewrite kron_mixed_product.
          rewrite Mmult_assoc.
          rewrite H4.
          Msimpl.
          reflexivity.
        }
        assert (step2 : P0 ⊗ P1 ⊗ (beta_perp × (beta_perp) †) × (∣1⟩ ⊗ ∣1⟩ ⊗ beta) = Zero).
        {
          repeat rewrite kron_mixed_product.
          rewrite Mmult_assoc.
          rewrite H3.
          Msimpl.
          reflexivity.
        }
        rewrite step1, step2 in H2; clear step1 step2.
        rewrite Mplus_0_r in H2.
        assert (step3 : ccu (diag2 u0 u1) × (∣1⟩ ⊗ ∣1⟩ ⊗ beta) = ∣1⟩ ⊗ ∣1⟩ ⊗ (diag2 u0 u1 × beta)).
        {
          assert (WF_lhs : WF_Matrix (ccu (diag2 u0 u1) × (∣1⟩ ⊗ ∣1⟩ ⊗ beta))).
          {
            apply WF_mult.
            apply WF_ccu.
            apply WF_diag2.
            solve_WF_matrix.
          }
          assert (WF_rhs : WF_Matrix (∣1⟩ ⊗ ∣1⟩ ⊗ (diag2 u0 u1 × beta))).
          {
            repeat apply WF_kron.
            all: try lia.
            exact WF_qubit1.
            exact WF_qubit1.
            apply WF_mult.
            apply WF_diag2.
            assumption.
          }
          unfold ccu, control, diag2, Mmult.
          lma'.
        }
        rewrite step3 in H2 at 1; clear step3.
        apply kron_cancel_l in H2; auto.
        2: {
          apply WF_mult.
          apply WF_diag2.
          exact WF_beta.
        }
        2: {
          apply nonzero_kron.
          exact WF_qubit1.
          exact WF_qubit1.
          exact nonzero_qubit1.
          exact nonzero_qubit1.
        }
        assert (u0_is_1 : u0 = C1).
        {
          apply (f_equal (fun f => f 0%nat 0%nat)) in H2.
          unfold diag2, Mmult in H2; simpl in H2.
          revert H2; Csimpl; intro H2.
          apply Cmult_cancel_r with (a := beta 0%nat 0%nat).
          exact a_nonzero.
          rewrite <- H2.
          rewrite Cmult_1_l.
          reflexivity.
        }
        assert (u1_is_1 : u1 = C1).
        {
          apply (f_equal (fun f => f 1%nat 0%nat)) in H2.
          unfold diag2, Mmult in H2; simpl in H2.
          revert H2; Csimpl; intro H2.
          apply Cmult_cancel_r with (a := beta 1%nat 0%nat).
          exact b_nonzero.
          rewrite <- H2.
          rewrite Cmult_1_l.
          reflexivity.
        }
        split.
        ** exact u0_is_1.
        ** exact u1_is_1.
  - intros.
    exists (I 2), (I 2).
    destruct H2 as [u0_is_1 u1_is_1].
    rewrite u0_is_1, u1_is_1.
    exists C1, C1, C1, C1.
    exists ∣0⟩, ∣1⟩, ∣0⟩, ∣1⟩.
    split.
    {
      apply id_unitary.
    }
    split.
    {
      apply id_unitary.
    }
    split.
    {
      apply WF_qubit0.
    }
    split.
    {
      apply WF_qubit1.
    }
    split.
    {
      apply WF_qubit0.
    }
    split.
    {
      apply WF_qubit1.
    }
    split.
    {
      apply nonzero_qubit0.
    }
    split.
    {
      apply nonzero_qubit1.
    }
    split.
    {
      apply nonzero_qubit0.
    }
    split.
    {
      apply nonzero_qubit1.
    }
    split.
    {
      apply id2_eigenpairs.
    }
    split.
    {
      apply id2_eigenpairs.
    }
    split.
    {
      apply id2_eigenpairs.
    }
    split.
    {
      apply id2_eigenpairs.
    }
    {
      rewrite <- kron_plus_distr_l.
      unfold beta, beta_perp.
      rewrite a8; auto.
      lma'.
      apply WF_ccu.
      apply WF_diag2.
    }
Qed.
