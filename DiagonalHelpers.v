Require Import QuantumLib.Matrix.
Require Import QuantumLib.Eigenvectors.
Require Import Proof.MatrixHelpers.

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
