Require Import QuantumLib.Eigenvectors.
Require Import MatrixHelpers.
Require Import GateHelpers.

Lemma Diag_diag2: forall (c1 c2 : C), WF_Diagonal (diag2 c1 c2).
Proof.
  intros.
  unfold WF_Diagonal.
  split. apply WF_diag2.
  intros.
  unfold diag2; simpl.
  destruct i.
  - destruct j.
    + contradiction.
    + reflexivity.
  - destruct i.
    + destruct j.
      * reflexivity.
      * destruct j.
        -- contradiction.
        -- reflexivity.
    + reflexivity.
Qed.

Lemma Diag_diag4: forall (c1 c2 c3 c4 : C), WF_Diagonal (diag4 c1 c2 c3 c4).
Proof.
  intros.
  unfold WF_Diagonal.
  split; try apply WF_diag4.
  intros.
  unfold diag4; simpl.
  destruct i.
  - destruct j.
    + contradiction.
    + reflexivity.
  - destruct i.
    + destruct j.
      * reflexivity.
      * destruct j.
        -- contradiction.
        -- reflexivity.
    + destruct i.
      * destruct j.
        -- reflexivity.
        -- destruct j.
           ++ reflexivity.
           ++ destruct j.
              ** contradiction.
              ** reflexivity.
      * destruct i.
        -- destruct j.
           ++ reflexivity.
           ++ destruct j.
              ** reflexivity.
              ** destruct j.
                 --- reflexivity.
                 --- destruct j.
                     +++ contradiction.
                     +++ reflexivity.
        -- reflexivity.
Qed.


Lemma diag00 :  WF_Diagonal ∣0⟩⟨0∣.
Proof.
  split; auto with wf_db.
  intros.
  unfold qubit0, Mmult, adjoint.
  bdestruct (i =? j); try lia.
  simpl.
  destruct i; destruct j; try lia.
  destruct j; try lia; try lca.
  destruct i; try lia; try lca.
  destruct j; try lia; try lca.
Qed.

Lemma diag11 :  WF_Diagonal ∣1⟩⟨1∣.
Proof.
  split; auto with wf_db.
  intros.
  unfold qubit1, Mmult, adjoint.
  bdestruct (i =? j); try lia.
  simpl.
  destruct i; destruct j; try lia.
  destruct j; try lia; try lca.
  destruct i; try lia; try lca.
  destruct j; try lia; try lca.
  destruct i; try lia; try lca.
Qed.

Lemma diag_control : forall {n} (D : Square n),
  WF_Diagonal D -> WF_Diagonal (control D).
Proof.
  intros n D D_diag.
  rewrite control_decomp; try apply D_diag.
  apply diag_plus.
  apply diag_kron.
  apply diag00.
  apply diag_I.
  apply diag_kron.
  apply diag11.
  apply D_diag.
Qed.

Lemma ccu_diag: forall (U: Square 2), WF_Diagonal U -> WF_Diagonal (ccu U).
Proof.
    intros.
    unfold ccu.
    apply diag_control.
    apply diag_control.
    assumption.
Qed.

Lemma direct_sum_diagonal : forall {n : nat} (P Q : Square n),
  WF_Diagonal P -> WF_Diagonal Q -> WF_Diagonal (P .⊕ Q).
Proof.
  intros n P Q [WF_P Diagonal_P] [WF_Q Diagonal_Q].
  split.
  {
    apply WF_direct_sum; try lia; assumption.
  }
  {
    intros i j i_neq_j.
    specialize (Diagonal_P i j i_neq_j).
    specialize (Diagonal_Q (i - n) (j - n))%nat.
    unfold direct_sum.
    destruct (i <? n) eqn:L1.
    {
      simpl; exact Diagonal_P.
    }
    {
      destruct (j <? n) eqn:L2.
      {
        simpl; exact Diagonal_P.
      }
      {
        apply Nat.ltb_ge in L1, L2.
        simpl; apply Diagonal_Q.
        intro in_eq_jn.
        apply i_neq_j.
        apply (f_equal (fun x => x + n)%nat) in in_eq_jn.
        do 2 rewrite Nat.sub_add in in_eq_jn; auto.
      }
    }
  }
Qed.

Lemma diag_commute : forall {n} (D : Square n) (E : Square n),
  WF_Diagonal D -> WF_Diagonal E -> E × D = D × E.
Proof.
  intros n D E D_diag E_diag.
  unfold WF_Diagonal in *.
  destruct D_diag as [WF_D D_diag].
  destruct E_diag as [WF_E E_diag].
  unfold Mmult.
  apply functional_extensionality.
  intro x.
  apply functional_extensionality.
  intro y.
  apply big_sum_eq.
  apply functional_extensionality.
  intro i.
  bdestruct (x =? y).
  {
    rewrite <- H; clear H.
    bdestruct (x =? i).
    {
      rewrite H; lca.
    }
    {
      specialize (D_diag x i H) as D_zero.
      specialize (E_diag x i H) as E_zero.
      rewrite D_zero, E_zero; lca.
    }
  }
  {
    bdestruct (x =? i).
    {
      bdestruct (y =? x).
      {
        lia.
      }
      {
        rewrite H0 in H.
        specialize (D_diag i y H) as D_zero.
        specialize (E_diag i y H) as E_zero.
        rewrite D_zero, E_zero; lca.
      }
    }
    {
      specialize (D_diag x i H0) as D_zero.
      specialize (E_diag x i H0) as E_zero.
      rewrite D_zero, E_zero; lca.
    }
  }
Qed.

