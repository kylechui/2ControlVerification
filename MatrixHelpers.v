Require Import Coq.Logic.Classical_Pred_Type.
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
      try apply WF_control;
      try solve [intros; exfalso; auto]
    )
  ).

Lemma Mplus_cancel_l : forall {m n} (A B C : Matrix m n),
  A .+ B = A .+ C -> B = C.
Proof.
  intros.
  apply (f_equal (fun f => Mopp A .+ f)) in H.
  rewrite <- Mscale_1_l with (A := A) in H at 2 4.
  unfold Mopp in H.
  repeat rewrite <- Mplus_assoc in H.
  rewrite <- Mscale_plus_distr_l in H.
  rewrite Cplus_opp_l in H.
  rewrite Mscale_0_l in H.
  repeat rewrite Mplus_0_l in H.
  assumption.
Qed.

Lemma Mplus_cancel_r : forall {m n} (A B C : Matrix m n),
  A .+ C = B .+ C -> A = B.
Proof.
  intros.
  apply (f_equal (fun f => f .+ Mopp C)) in H.
  rewrite <- Mscale_1_l with (A := C) in H at 1 3.
  unfold Mopp in H.
  repeat rewrite Mplus_assoc in H.
  rewrite <- Mscale_plus_distr_l in H.
  rewrite Cplus_opp_r in H.
  rewrite Mscale_0_l in H.
  repeat rewrite Mplus_0_r in H.
  assumption.
Qed.

Definition diag2 (c1 c2 : C) : Square 2 :=
  fun x y =>
    match (x,y) with
    | (0, 0) => c1
    | (1, 1) => c2
    | _      => C0
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

Lemma kron_cancel_l: forall {m n o p} (A : Matrix m n) (B C : Matrix o p),
  WF_Matrix B -> WF_Matrix C -> A <> Zero -> A ⊗ B = A ⊗ C -> B = C.
Proof.
  intros.
  assert (zero_def : forall (A : Matrix n m), A = Zero <-> forall (i j : nat), A i j = C0).
  {
    split.
    - intros.
      rewrite H3.
      unfold Zero.
      reflexivity.
    - intros.
      prep_matrix_equality.
      rewrite H3.
      unfold Zero.
      reflexivity.
  }
  assert (nonzero_def : exists i j, A i j <> 0).
  {
    assert (quantifier_negation : forall (A: Matrix n m),
              (~ forall (i j: nat), A i j = 0) -> exists (i j : nat), A i j <> 0).
    {
      intros.
      apply not_all_ex_not in H3. 
      destruct H3.
      apply not_all_ex_not in H3.
      destruct H3.
      exists x.
      exists x0.
      assumption.
    }
    apply quantifier_negation.
    rewrite <- zero_def.
    assumption.
  }
  destruct nonzero_def as [i [j nonzero_def]].
  prep_matrix_equality.
  apply (f_equal (fun f => f (i * o + x) (j * p + y)))%nat in H2.
  unfold kron in H2.
  destruct (x <? o) eqn:L1.
  apply Nat.ltb_lt in L1.
  - destruct (y <? p) eqn:L2.
    apply Nat.ltb_lt in L2.
    + revert H2.
      repeat rewrite Nat.div_add_l by lia.
      repeat rewrite Nat.div_small; auto.
      rewrite Nat.add_mod with (n := o) by lia.
      rewrite Nat.add_mod with (n := p) by lia.
      repeat rewrite Nat.mod_mul by lia.
      repeat rewrite Nat.mod_small; auto.
      intros.
      apply Cmult_cancel_l with (a := A i j); auto.
      repeat rewrite Nat.add_0_l in H2.
      repeat rewrite Nat.add_0_r in H2.
      assumption.
    + unfold WF_Matrix in H.
      unfold WF_Matrix in H0.
      apply Nat.ltb_ge in L2.
      specialize (H x y).
      specialize (H0 x y).
      assert (b_zero : B x y = C0).
      {
        apply H.
        right.
        assumption.
      }
      assert (c_zero : C x y = C0).
      {
        apply H0.
        right.
        assumption.
      }
      rewrite b_zero, c_zero.
      reflexivity.
  - unfold WF_Matrix in H.
    unfold WF_Matrix in H0.
    apply Nat.ltb_ge in L1.
    specialize (H x y).
    specialize (H0 x y).
    assert (b_zero : B x y = C0).
    {
      apply H.
      left.
      assumption.
    }
    assert (c_zero : C x y = C0).
    {
      apply H0.
      left.
      assumption.
    }
    rewrite b_zero, c_zero.
    reflexivity.
Qed.

Lemma kron_0_cancel_l: forall {m n} (B C : Matrix m n),
  WF_Matrix B -> WF_Matrix C -> ∣0⟩ ⊗ B = ∣0⟩ ⊗ C -> B = C.
Proof.
  assert (qubit0_neq_Zero : ∣0⟩ <> Zero).
  {
    intro.
    apply f_equal with (f := fun f => f 0%nat 0%nat) in H.
    contradict H.
    exact C1_neq_C0.
  }
  intros.
  apply (@kron_cancel_l m n) with (A := ∣0⟩); auto.
Qed.

Lemma kron_1_cancel_l: forall {m n} (B C : Matrix m n),
  WF_Matrix B -> WF_Matrix C -> ∣1⟩ ⊗ B = ∣1⟩ ⊗ C -> B = C.
Proof.
  assert (qubit1_neq_Zero : ∣1⟩ <> Zero).
  {
    intro.
    apply f_equal with (f := fun f => f 1%nat 0%nat) in H.
    contradict H.
    exact C1_neq_C0.
  }
  intros.
  apply (@kron_cancel_l m n) with (A := ∣1⟩); auto.
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
  WF_Matrix P00 -> WF_Matrix P01 -> WF_Matrix P10 -> WF_Matrix P11 ->
  WF_Matrix Q00 -> WF_Matrix Q01 -> WF_Matrix Q10 -> WF_Matrix Q11 ->
  U = ∣0⟩⟨0∣ ⊗ P00 .+ ∣0⟩⟨1∣ ⊗ P01 .+ ∣1⟩⟨0∣ ⊗ P10 .+ ∣1⟩⟨1∣ ⊗ P11 ->
  V = ∣0⟩⟨0∣ ⊗ Q00 .+ ∣0⟩⟨1∣ ⊗ Q01 .+ ∣1⟩⟨0∣ ⊗ Q10 .+ ∣1⟩⟨1∣ ⊗ Q11 ->
  U × V = ∣0⟩⟨0∣ ⊗ (P00 × Q00 .+ P01 × Q10) .+ ∣0⟩⟨1∣ ⊗ (P00 × Q01 .+ P01×Q11) .+ ∣1⟩⟨0∣ ⊗ (P10×Q00 .+ P11 × Q10) .+ ∣1⟩⟨1∣ ⊗ (P10 × Q01 .+ P11 × Q11).
Proof.
  intros.
  rewrite H7, H8.
  lma'.
  solve_WF_matrix.
  solve_WF_matrix.
Qed.

Lemma block_equalities: forall (U V: Square 4) (P00 P01 P10 P11 Q00 Q01 Q10 Q11: Square 2),
  WF_Matrix P00 -> WF_Matrix P01 -> WF_Matrix P10 -> WF_Matrix P11 ->
  WF_Matrix Q00 -> WF_Matrix Q01 -> WF_Matrix Q10 -> WF_Matrix Q11 ->
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
  destruct H1.
  - left.
    intro.
    apply H0.
    rewrite Nat.div_mod with (x := i) (y := m). 2: assumption.
    rewrite Nat.div_mod with (x := j) (y := m). 2: assumption.
    rewrite e.
    rewrite H1.
    reflexivity.
  - right.
    assumption.
Qed.
