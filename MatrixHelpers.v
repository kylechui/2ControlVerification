Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.

Ltac solve_WF_matrix := 
    repeat (
      progress (
        try reflexivity;
        try assumption; 
        try apply WF_Zero;
        try apply WF_I;
        try apply WF_mult;
        try apply WF_plus;
        try apply WF_scale;
        try apply WF_adjoint;
        try apply WF_kron;
        try apply WF_bra0;
        try apply WF_bra1; 
        try apply WF_qubit0; 
        try apply WF_qubit1; 
        try apply WF_braqubit0; 
        try apply WF_braqubit1;
        try apply WF_swap;
        try solve [intros; exfalso; auto]
      )  
    ).

Definition diag2 (c1 c2 : C) : Square 2 :=
    fun x y =>
    match (x,y) with
    | (0,0) => c1
    | (1,1) => c2
    | _ => C0
    end.

Lemma WF_diag2: forall (c1 c2 : C), WF_Matrix (diag2 c1 c2).
Proof.
unfold WF_Matrix.
intros.
destruct H.
{
    unfold diag2.
    destruct x as [|x'].
    contradict H.
    lia.
    destruct x' as [|x''].
    contradict H.
    lia. reflexivity.
}
{
    unfold diag2.
    destruct x as [|x'].
    destruct y as [|y'].
    contradict H.
    lia. reflexivity.
    destruct x' as [|x''].
    destruct y as [|y'].
    contradict H.
    lia.
    destruct y' as [|y''].
    contradict H.
    lia. reflexivity. reflexivity.
}
Qed.

Lemma kron_0_vec2_equiv: forall (B C : Vector 2),
WF_Matrix B -> WF_Matrix C -> ∣0⟩ ⊗ B = ∣0⟩ ⊗ C -> B = C.
Proof.
intros.
lma'.
assert ((B 0 0 = (∣0⟩ ⊗ B) 0 0 )%nat). lca.
assert ((C 0 0 = (∣0⟩ ⊗ C) 0 0 )%nat). lca.
rewrite H2. rewrite H3. rewrite H1. reflexivity.
assert ((B 1 0 = (∣0⟩ ⊗ B) 1 0 )%nat). lca.
assert ((C 1 0 = (∣0⟩ ⊗ C) 1 0 )%nat). lca.
rewrite H2. rewrite H3. rewrite H1. reflexivity.
Qed.

Lemma kron_1_vec2_equiv: forall (B C: Vector 2),
WF_Matrix B -> WF_Matrix C -> ∣1⟩ ⊗ B = ∣1⟩ ⊗ C -> B = C.
Proof.
intros.
lma'.
assert ((B 0 0 = (∣1⟩ ⊗ B) 2 0 )%nat). lca.
assert ((C 0 0 = (∣1⟩ ⊗ C) 2 0 )%nat). lca.
rewrite H2. rewrite H3. rewrite H1. reflexivity.
assert ((B 1 0 = (∣1⟩ ⊗ B) 3 0 )%nat). lca.
assert ((C 1 0 = (∣1⟩ ⊗ C) 3 0 )%nat). lca.
rewrite H2. rewrite H3. rewrite H1. reflexivity.
Qed.

Lemma WF_ket0bra1: WF_Matrix ∣0⟩⟨1∣.
Proof.
solve_WF_matrix.
Qed.

Lemma WF_ket1bra0: WF_Matrix ∣1⟩⟨0∣.
Proof.
solve_WF_matrix.
Qed.

Lemma WF_blockmatrix: forall (P00 P01 P10 P11: Square 2), 
WF_Matrix P00 -> WF_Matrix P01 -> WF_Matrix P10 -> WF_Matrix P11 ->
WF_Matrix (∣0⟩⟨0∣ ⊗ P00 .+ ∣0⟩⟨1∣ ⊗ P01 .+ ∣1⟩⟨0∣ ⊗ P10 .+ ∣1⟩⟨1∣ ⊗ P11).
Proof.
intros.
solve_WF_matrix.
Qed.

Lemma block_multiply: forall (U V: Square 4) (P00 P01 P10 P11 Q00 Q01 Q10 Q11: Square 2), 
WF_Matrix P00 -> WF_Matrix P01 -> WF_Matrix P10 -> WF_Matrix P11
-> WF_Matrix Q00 -> WF_Matrix Q01 -> WF_Matrix Q10 -> WF_Matrix Q11 ->
U = ∣0⟩⟨0∣ ⊗ P00 .+ ∣0⟩⟨1∣ ⊗ P01 .+ ∣1⟩⟨0∣ ⊗ P10 .+ ∣1⟩⟨1∣ ⊗ P11 -> 
V = ∣0⟩⟨0∣ ⊗ Q00 .+ ∣0⟩⟨1∣ ⊗ Q01 .+ ∣1⟩⟨0∣ ⊗ Q10 .+ ∣1⟩⟨1∣ ⊗ Q11 -> 
U × V = ∣0⟩⟨0∣ ⊗ (P00 × Q00 .+ P01 × Q10) .+ ∣0⟩⟨1∣ ⊗ (P00 × Q01 .+ P01×Q11) .+ ∣1⟩⟨0∣ ⊗ (P10×Q00 .+ P11 × Q10) .+ ∣1⟩⟨1∣ ⊗ (P10 × Q01 .+ P11 × Q11).
Proof.
intros.
rewrite H7. rewrite H8.
lma'.
solve_WF_matrix.
solve_WF_matrix.
Qed.

Lemma block_equalities: forall (U V: Square 4) (P00 P01 P10 P11 Q00 Q01 Q10 Q11: Square 2), 
WF_Matrix P00 -> WF_Matrix P01 -> WF_Matrix P10 -> WF_Matrix P11
-> WF_Matrix Q00 -> WF_Matrix Q01 -> WF_Matrix Q10 -> WF_Matrix Q11 ->
U = ∣0⟩⟨0∣ ⊗ P00 .+ ∣0⟩⟨1∣ ⊗ P01 .+ ∣1⟩⟨0∣ ⊗ P10 .+ ∣1⟩⟨1∣ ⊗ P11 -> 
V = ∣0⟩⟨0∣ ⊗ Q00 .+ ∣0⟩⟨1∣ ⊗ Q01 .+ ∣1⟩⟨0∣ ⊗ Q10 .+ ∣1⟩⟨1∣ ⊗ Q11 -> 
U = V -> P00 = Q00 /\ P01 = Q01 /\ P10 = Q10 /\ P11 = Q11.
Proof.
intros U V P00 P01 P10 P11 Q00 Q01 Q10 Q11 WF_P00 WF_P01 WF_P10 WF_P11 WF_Q00 WF_Q01 WF_Q10 WF_Q11
def_U def_V H.
split.
{
    lma'.
    assert (peq: P00 0%nat 0%nat = U 0%nat 0%nat). rewrite def_U. lca.
    assert (qeq: Q00 0%nat 0%nat = V 0%nat 0%nat). rewrite def_V. lca.
    rewrite peq. rewrite qeq. rewrite H. reflexivity.
    assert (peq: P00 0%nat 1%nat = U 0%nat 1%nat). rewrite def_U. lca.
    assert (qeq: Q00 0%nat 1%nat = V 0%nat 1%nat). rewrite def_V. lca.
    rewrite peq. rewrite qeq. rewrite H. reflexivity.
    assert (peq: P00 1%nat 0%nat = U 1%nat 0%nat). rewrite def_U. lca.
    assert (qeq: Q00 1%nat 0%nat = V 1%nat 0%nat). rewrite def_V. lca.
    rewrite peq. rewrite qeq. rewrite H. reflexivity.
    assert (peq: P00 1%nat 1%nat = U 1%nat 1%nat). rewrite def_U. lca.
    assert (qeq: Q00 1%nat 1%nat = V 1%nat 1%nat). rewrite def_V. lca.
    rewrite peq. rewrite qeq. rewrite H. reflexivity.
}
split.
{
    lma'.
    assert (peq: P01 0%nat 0%nat = U 0%nat 2%nat). rewrite def_U. lca.
    assert (qeq: Q01 0%nat 0%nat = V 0%nat 2%nat). rewrite def_V. lca.
    rewrite peq. rewrite qeq. rewrite H. reflexivity.
    assert (peq: P01 0%nat 1%nat = U 0%nat 3%nat). rewrite def_U. lca.
    assert (qeq: Q01 0%nat 1%nat = V 0%nat 3%nat). rewrite def_V. lca.
    rewrite peq. rewrite qeq. rewrite H. reflexivity.
    assert (peq: P01 1%nat 0%nat = U 1%nat 2%nat). rewrite def_U. lca.
    assert (qeq: Q01 1%nat 0%nat = V 1%nat 2%nat). rewrite def_V. lca.
    rewrite peq. rewrite qeq. rewrite H. reflexivity.
    assert (peq: P01 1%nat 1%nat = U 1%nat 3%nat). rewrite def_U. lca.
    assert (qeq: Q01 1%nat 1%nat = V 1%nat 3%nat). rewrite def_V. lca.
    rewrite peq. rewrite qeq. rewrite H. reflexivity.
}
split.
{
    lma'.
    assert (peq: P10 0%nat 0%nat = U 2%nat 0%nat). rewrite def_U. lca.
    assert (qeq: Q10 0%nat 0%nat = V 2%nat 0%nat). rewrite def_V. lca.
    rewrite peq. rewrite qeq. rewrite H. reflexivity.
    assert (peq: P10 0%nat 1%nat = U 2%nat 1%nat). rewrite def_U. lca.
    assert (qeq: Q10 0%nat 1%nat = V 2%nat 1%nat). rewrite def_V. lca.
    rewrite peq. rewrite qeq. rewrite H. reflexivity.
    assert (peq: P10 1%nat 0%nat = U 3%nat 0%nat). rewrite def_U. lca.
    assert (qeq: Q10 1%nat 0%nat = V 3%nat 0%nat). rewrite def_V. lca.
    rewrite peq. rewrite qeq. rewrite H. reflexivity.
    assert (peq: P10 1%nat 1%nat = U 3%nat 1%nat). rewrite def_U. lca.
    assert (qeq: Q10 1%nat 1%nat = V 3%nat 1%nat). rewrite def_V. lca.
    rewrite peq. rewrite qeq. rewrite H. reflexivity.
}
{
    lma'.
    assert (peq: P11 0%nat 0%nat = U 2%nat 2%nat). rewrite def_U. lca.
    assert (qeq: Q11 0%nat 0%nat = V 2%nat 2%nat). rewrite def_V. lca.
    rewrite peq. rewrite qeq. rewrite H. reflexivity.
    assert (peq: P11 0%nat 1%nat = U 2%nat 3%nat). rewrite def_U. lca.
    assert (qeq: Q11 0%nat 1%nat = V 2%nat 3%nat). rewrite def_V. lca.
    rewrite peq. rewrite qeq. rewrite H. reflexivity.
    assert (peq: P11 1%nat 0%nat = U 3%nat 2%nat). rewrite def_U. lca.
    assert (qeq: Q11 1%nat 0%nat = V 3%nat 2%nat). rewrite def_V. lca.
    rewrite peq. rewrite qeq. rewrite H. reflexivity.
    assert (peq: P11 1%nat 1%nat = U 3%nat 3%nat). rewrite def_U. lca.
    assert (qeq: Q11 1%nat 1%nat = V 3%nat 3%nat). rewrite def_V. lca.
    rewrite peq. rewrite qeq. rewrite H. reflexivity.
}
Qed.

Lemma neq_implies_const_div_neq: forall (i j m: nat), (m <> 0)%nat -> (i <> j)%nat -> (i / m <> j / m)%nat \/ (i mod m <> j mod m)%nat.
(* Thanks Kyle *)
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
lma'.
destruct (eq_nat_decide i j) as [Heq | Hneq].
{
    apply eq_nat_is_eq in Heq.
    rewrite Heq.
    unfold I at 3.
    rewrite Nat.eqb_refl.
    simpl.
    destruct (j <? n * m) eqn:Hlt.
    {
        unfold kron.
        unfold I.
        rewrite Nat.eqb_refl.
        rewrite Nat.eqb_refl.
        simpl.
        cut ((j / m <? n) = true).
        cut ((j mod m <? m) = true).
        intros H4 H5.
        rewrite H4. rewrite H5.
        simpl. lca.
        apply Nat.ltb_lt.
        apply Nat.mod_upper_bound.
        lia.
        apply Nat.ltb_lt. apply Nat.ltb_lt in Hlt.
        apply Nat.div_lt_upper_bound.
        lia. rewrite Nat.mul_comm.
        apply Hlt.
    }
    {
        apply Nat.ltb_ge in Hlt.
        unfold kron. unfold I at 1.
        cut ((j / m <? n) = false).
        intros.
        rewrite H1.
        rewrite Coq.Bool.Bool.andb_false_r.
        lca.
        apply Nat.ltb_ge.
        cut ((n = (n * m) / m)%nat).
        intros.
        rewrite H1.
        apply Nat.div_le_mono.
        lia. apply Hlt.
        rewrite Nat.div_mul; try lia.
    }
}
{
    unfold I at 3.
    cut ((i =? j) && (i <? n * m) = false).
    intros.
    rewrite H1.
    unfold kron.
    unfold I.
    cut (((i / m =? j / m) && (i / m <? n)) = false \/ (i mod m =? j mod m) && (i mod m <? m) = false).
    intros.
    destruct H2.
    rewrite H2.
    lca.
    rewrite H2.
    lca.
    cut ((i / m =? j / m) = false \/ (i mod m =? j mod m) = false).
    intros.
    destruct H2.
    rewrite H2.
    left.
    apply Coq.Bool.Bool.andb_false_l.
    rewrite H2.
    right.
    apply Coq.Bool.Bool.andb_false_l.
    rewrite Nat.eqb_neq. rewrite Nat.eqb_neq.
    apply neq_implies_const_div_neq.
    lia.
    rewrite eq_nat_is_eq in Hneq.
    assumption.
    cut ((i =? j) = false).
    intros.
    rewrite H1.
    apply Coq.Bool.Bool.andb_false_l.
    apply Nat.eqb_neq.
    unfold not in Hneq.
    rewrite eq_nat_is_eq in Hneq.
    trivial.
}
Qed.