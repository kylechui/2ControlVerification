Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.
Lemma kron_0_vec2_equiv: forall (B C : Vector 2),
WF_Matrix B -> WF_Matrix C -> ∣0⟩ ⊗ B = ∣0⟩ ⊗ C -> B = C.
Proof.
intros.
cut ((B 0 0 = (∣0⟩ ⊗ B) 0 0 )%nat).
cut ((B 1 0 = (∣0⟩ ⊗ B) 1 0 )%nat).
cut ((C 0 0 = (∣0⟩ ⊗ C) 0 0 )%nat).
cut ((C 1 0 = (∣0⟩ ⊗ C) 1 0 )%nat).
intros.
apply mat_equiv_eq.
apply H. apply H0.
by_cell.
rewrite H5. rewrite H3. rewrite H1. reflexivity.
rewrite H4. rewrite H2. rewrite H1. reflexivity.
lca. lca. lca. lca.
Qed.

Lemma kron_1_vec2_equiv: forall (B C: Vector 2),
WF_Matrix B -> WF_Matrix C -> ∣1⟩ ⊗ B = ∣1⟩ ⊗ C -> B = C.
Proof.
intros.
cut ((B 0 0 = (∣1⟩ ⊗ B) 2 0 )%nat).
cut ((B 1 0 = (∣1⟩ ⊗ B) 3 0 )%nat).
cut ((C 0 0 = (∣1⟩ ⊗ C) 2 0 )%nat).
cut ((C 1 0 = (∣1⟩ ⊗ C) 3 0 )%nat).
intros.
apply mat_equiv_eq.
apply H. apply H0.
by_cell.
rewrite H5. rewrite H3. rewrite H1. reflexivity.
rewrite H4. rewrite H2. rewrite H1. reflexivity.
lca. lca. lca. lca.
Qed.

Lemma WF_ket0bra1: WF_Matrix ∣0⟩⟨1∣.
Proof.
apply WF_mult.
apply WF_qubit0.
apply WF_adjoint.
apply WF_qubit1.
Qed.

Lemma WF_ket1bra0: WF_Matrix ∣1⟩⟨0∣.
Proof.
apply WF_mult.
apply WF_qubit1.
apply WF_adjoint.
apply WF_qubit0.
Qed.

Lemma WF_blockmatrix: forall (P00 P01 P10 P11: Square 2), 
WF_Matrix P00 -> WF_Matrix P01 -> WF_Matrix P10 -> WF_Matrix P11 ->
WF_Matrix (∣0⟩⟨0∣ ⊗ P00 .+ ∣0⟩⟨1∣ ⊗ P01 .+ ∣1⟩⟨0∣ ⊗ P10 .+ ∣1⟩⟨1∣ ⊗ P11).
Proof.
intros.
apply WF_plus.
apply WF_plus.
apply WF_plus.
apply WF_kron.
ring. ring.
apply WF_braqubit0.
apply H.
apply WF_kron.
ring. ring.
apply WF_ket0bra1.
apply H0.
apply WF_kron.
ring. ring.
apply WF_ket1bra0.
apply H1.
apply WF_kron.
ring. ring.
apply WF_braqubit1.
apply H2.
Qed.

Lemma block_multiply: forall (U V: Square 4) (P00 P01 P10 P11 Q00 Q01 Q10 Q11: Square 2), 
WF_Matrix P00 -> WF_Matrix P01 -> WF_Matrix P10 -> WF_Matrix P11
-> WF_Matrix Q00 -> WF_Matrix Q01 -> WF_Matrix Q10 -> WF_Matrix Q11 ->
U = ∣0⟩⟨0∣ ⊗ P00 .+ ∣0⟩⟨1∣ ⊗ P01 .+ ∣1⟩⟨0∣ ⊗ P10 .+ ∣1⟩⟨1∣ ⊗ P11 -> 
V = ∣0⟩⟨0∣ ⊗ Q00 .+ ∣0⟩⟨1∣ ⊗ Q01 .+ ∣1⟩⟨0∣ ⊗ Q10 .+ ∣1⟩⟨1∣ ⊗ Q11 -> 
U × V = ∣0⟩⟨0∣ ⊗ (P00 × Q00 .+ P01 × Q10) .+ ∣0⟩⟨1∣ ⊗ (P00 × Q01 .+ P01×Q11) .+ ∣1⟩⟨0∣ ⊗ (P10×Q00 .+ P11 × Q10) .+ ∣1⟩⟨1∣ ⊗ (P10 × Q01 .+ P11 × Q11).
Proof.
intros U V P00 P01 P10 P11 Q00 Q01 Q10 Q11 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
rewrite H9. rewrite H10.
apply mat_equiv_eq.
{
    apply WF_mult.
    apply WF_blockmatrix.
    apply H1. apply H2. apply H3. apply H4.
    apply WF_blockmatrix.
    apply H5. apply H6. apply H7. apply H8.
}
{
    apply WF_blockmatrix.
    apply WF_plus.
    apply WF_mult.
    apply H1. apply H5.
    apply WF_mult.
    apply H2. apply H7.
    apply WF_plus.
    apply WF_mult.
    apply H1. apply H6.
    apply WF_mult.
    apply H2. apply H8.  
    apply WF_plus.
    apply WF_mult.
    apply H3. apply H5.
    apply WF_mult.
    apply H4. apply H7.  
    apply WF_plus.
    apply WF_mult.
    apply H3. apply H6.
    apply WF_mult.
    apply H4. apply H8.     
}
{
    unfold Mmult. unfold Mplus. unfold kron.
    by_cell.
    lca. lca. lca. lca. lca. lca. lca. lca.
    lca. lca. lca. lca. lca. lca. lca. lca.
}
Qed.

Lemma block_equalities: forall (U V: Square 4) (P00 P01 P10 P11 Q00 Q01 Q10 Q11: Square 2), 
WF_Matrix P00 -> WF_Matrix P01 -> WF_Matrix P10 -> WF_Matrix P11
-> WF_Matrix Q00 -> WF_Matrix Q01 -> WF_Matrix Q10 -> WF_Matrix Q11 ->
U = ∣0⟩⟨0∣ ⊗ P00 .+ ∣0⟩⟨1∣ ⊗ P01 .+ ∣1⟩⟨0∣ ⊗ P10 .+ ∣1⟩⟨1∣ ⊗ P11 -> 
V = ∣0⟩⟨0∣ ⊗ Q00 .+ ∣0⟩⟨1∣ ⊗ Q01 .+ ∣1⟩⟨0∣ ⊗ Q10 .+ ∣1⟩⟨1∣ ⊗ Q11 -> 
U = V -> P00 = Q00 /\ P01 = Q01 /\ P10 = Q10 /\ P11 = Q11.
Proof.
intros U V P00 P01 P10 P11 Q00 Q01 Q10 Q11 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.
split.
{
    apply mat_equiv_eq.
    apply H1. apply H5.
    by_cell.
    cut (P00 0%nat 0%nat = U 0%nat 0%nat).
    cut (Q00 0%nat 0%nat = V 0%nat 0%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
    cut (P00 0%nat 1%nat = U 0%nat 1%nat).
    cut (Q00 0%nat 1%nat = V 0%nat 1%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
    cut (P00 1%nat 0%nat = U 1%nat 0%nat).
    cut (Q00 1%nat 0%nat = V 1%nat 0%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
    cut (P00 1%nat 1%nat = U 1%nat 1%nat).
    cut (Q00 1%nat 1%nat = V 1%nat 1%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
}
split.
{
    apply mat_equiv_eq.
    apply H2. apply H6.
    by_cell.
    cut (P01 0%nat 0%nat = U 0%nat 2%nat).
    cut (Q01 0%nat 0%nat = V 0%nat 2%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
    cut (P01 0%nat 1%nat = U 0%nat 3%nat).
    cut (Q01 0%nat 1%nat = V 0%nat 3%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
    cut (P01 1%nat 0%nat = U 1%nat 2%nat).
    cut (Q01 1%nat 0%nat = V 1%nat 2%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
    cut (P01 1%nat 1%nat = U 1%nat 3%nat).
    cut (Q01 1%nat 1%nat = V 1%nat 3%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
} 
split.
{
    apply mat_equiv_eq.
    apply H3. apply H7.
    by_cell.
    cut (P10 0%nat 0%nat = U 2%nat 0%nat).
    cut (Q10 0%nat 0%nat = V 2%nat 0%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
    cut (P10 0%nat 1%nat = U 2%nat 1%nat).
    cut (Q10 0%nat 1%nat = V 2%nat 1%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
    cut (P10 1%nat 0%nat = U 3%nat 0%nat).
    cut (Q10 1%nat 0%nat = V 3%nat 0%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
    cut (P10 1%nat 1%nat = U 3%nat 1%nat).
    cut (Q10 1%nat 1%nat = V 3%nat 1%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
}
{
    apply mat_equiv_eq.
    apply H4. apply H8.
    by_cell.
    cut (P11 0%nat 0%nat = U 2%nat 2%nat).
    cut (Q11 0%nat 0%nat = V 2%nat 2%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
    cut (P11 0%nat 1%nat = U 2%nat 3%nat).
    cut (Q11 0%nat 1%nat = V 2%nat 3%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
    cut (P11 1%nat 0%nat = U 3%nat 2%nat).
    cut (Q11 1%nat 0%nat = V 3%nat 2%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
    cut (P11 1%nat 1%nat = U 3%nat 3%nat).
    cut (Q11 1%nat 1%nat = V 3%nat 3%nat).
    intros H12 H13.
    rewrite H12. rewrite H13. rewrite H11. reflexivity.
    rewrite H10. lca.
    rewrite H9. lca.
}
Qed.

Lemma neq_implies_const_div_neq: forall (i j m: nat), (m <> 0)%nat -> (i <> j)%nat -> (i / m <> j / m)%nat \/ (i mod m <> j mod m)%nat.
Proof.
  intros.
  assert (H1 : ({i mod m = j mod m} + {i mod m <> j mod m})%nat).
  {
    intros.
    apply Nat.eq_dec.
  }
  destruct H1 as [H1|H1].
  - left.
    intro.
    apply H0.
    rewrite Nat.div_mod with (x := i) (y := m). 2: assumption.
    rewrite Nat.div_mod with (x := j) (y := m). 2: assumption.
    rewrite H2.
    rewrite H1.
    reflexivity.
  - right.
    assumption.
Qed.

Lemma kron_I {n m : nat} : (n > 0)%nat -> (m > 0)%nat -> I n ⊗ I m = I (n * m).
Proof.
  intros.
  apply mat_equiv_eq.
  apply WF_kron. reflexivity. reflexivity. apply WF_I. apply WF_I.
  apply WF_I.
  by_cell.
  destruct (Nat.eq_dec i j) as [Heq | Hneq].
  {
    rewrite Heq.
    unfold I at 3.
    rewrite Nat.eqb_refl; simpl.
    destruct (j <? n * m) eqn:Hlt.
    {
      unfold kron.
      unfold I.
      rewrite Nat.eqb_refl; rewrite Nat.eqb_refl; simpl.
      rewrite Nat.ltb_lt in Hlt.
      assert ((j / m <? n) = true).
      {
        apply Nat.ltb_lt.
        apply Nat.div_lt_upper_bound.
        lia.
        rewrite Nat.mul_comm.
        assumption.
      }
      assert ((j mod m <? m) = true).
      {
        apply Nat.ltb_lt.
        apply Nat.mod_upper_bound.
        lia.
      }
      rewrite H1; rewrite H2.
      lca.
    }
    {
      apply Nat.ltb_ge in Hlt.
      unfold kron; unfold I.
      cut ((j / m <? n) = false).
      intros.
      rewrite H1.
      rewrite Coq.Bool.Bool.andb_false_r.
      lca.
      apply Nat.ltb_ge.
      rewrite <- Nat.div_mul with (a := n) (b := m). 2: lia.
      apply Nat.div_le_mono. lia.
      lia.
    }
  }
  {
    unfold I at 3.
    assert ((i =? j) && (i <? n * m) = false).
    {
      rewrite <- Nat.eqb_neq in Hneq.
      rewrite Hneq.
      apply Coq.Bool.Bool.andb_false_l.
    }
    rewrite H1.
    unfold kron; unfold I.
    assert ((i / m =? j / m) = false \/ (i mod m =? j mod m) = false).
    {
      rewrite Nat.eqb_neq; rewrite Nat.eqb_neq.
      apply neq_implies_const_div_neq.
      lia.
      assumption.
    }
    assert (((i / m =? j / m) && (i / m <? n)) = false \/ (i mod m =? j mod m) && (i mod m <? m) = false).
    {
      destruct H2.
      rewrite H2.
      left.
      apply Coq.Bool.Bool.andb_false_l.
      right.
      rewrite H2.
      apply Coq.Bool.Bool.andb_false_l.
    }
    destruct H2.
    rewrite H2.
    lca.
    rewrite H2.
    lca.
  }
Qed.
