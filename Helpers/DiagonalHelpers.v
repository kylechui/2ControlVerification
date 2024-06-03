Require Import QuantumLib.Eigenvectors.

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
