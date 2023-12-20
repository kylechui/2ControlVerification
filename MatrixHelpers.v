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