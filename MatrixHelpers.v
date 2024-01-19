Require Import Coq.Logic.Classical_Pred_Type.
Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.
Require Import QuantumLib.Eigenvectors.
From Proof Require Import AlgebraHelpers.

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
      try apply WF_cnot;
      try apply WF_notc;
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

Lemma row_out_of_bounds: forall {m n} (A : Matrix m n) (i : nat),
  WF_Matrix A -> (i >= m)%nat -> forall (j : nat), A i j = C0.
Proof.
  intros m n A i WF_A row_oob j.
  unfold WF_Matrix in WF_A.
  apply WF_A.
  left.
  assumption.
Qed.

Lemma col_out_of_bounds: forall {m n} (A : Matrix m n) (j : nat),
  WF_Matrix A -> (j >= n)%nat -> forall (i : nat), A i j = C0.
Proof.
  intros m n A j WF_A col_oob i.
  unfold WF_Matrix in WF_A.
  apply WF_A.
  right.
  assumption.
Qed.

Lemma zero_def: forall {m n} (A : Matrix n m), A = Zero <-> forall (i j : nat), A i j = C0.
Proof.
  split.
  - intros.
    rewrite H.
    unfold Zero.
    reflexivity.
  - intros.
    prep_matrix_equality.
    rewrite H.
    unfold Zero.
    reflexivity.
Qed.

Lemma nonzero_def: forall {m n} (A : Matrix n m), A <> Zero <-> exists (i j : nat), A i j <> C0.
Proof.
  split.
  - intros.
    assert (quantifier_negation : forall (A: Matrix n m),
              (~ forall (i j: nat), A i j = C0) -> exists (i j : nat), A i j <> C0).
    {
      intros.
      apply not_all_ex_not in H0. 
      destruct H0.
      apply not_all_ex_not in H0.
      destruct H0.
      exists x.
      exists x0.
      assumption.
    }
    apply quantifier_negation.
    rewrite <- zero_def.
    assumption.
  - intros.
    destruct H as [i [j H]].
    intro.
    rewrite H0 in H.
    contradict H.
    reflexivity.
Qed.

Lemma nonzero_kron: forall {m n o p} (A : Matrix m n) (B : Matrix o p),
  WF_Matrix A -> WF_Matrix B -> A <> Zero -> B <> Zero -> A ⊗ B <> Zero.
Proof.
  intros.
  rewrite nonzero_def in H1, H2.
  destruct H1 as [i [j A_nonzero]].
  destruct H2 as [k [l B_nonzero]].
  rewrite nonzero_def.
  exists (i * o + k)%nat.
  exists (j * p + l)%nat.
  unfold kron.
  destruct (k <? o) eqn:L1.
  {
    apply Nat.ltb_lt in L1.
    destruct (l <? p) eqn:L2.
    apply Nat.ltb_lt in L2.
    - repeat rewrite Nat.div_add_l by lia.
      repeat rewrite Nat.div_small; auto.
      rewrite Nat.add_mod with (n := o) by lia.
      rewrite Nat.add_mod with (n := p) by lia.
      repeat rewrite Nat.mod_mul by lia.
      repeat rewrite Nat.mod_small; auto.
      repeat rewrite Nat.add_0_l.
      repeat rewrite Nat.add_0_r.
      intro absurd.
      apply Cmult_integral in absurd.
      destruct absurd.
      + contradiction.
      + contradiction.
    - apply Nat.ltb_ge in L2.
      pose proof (col_out_of_bounds B l H0 L2 k) as b_zero.
      contradiction.
  }
  {
    apply Nat.ltb_ge in L1.
    pose proof (row_out_of_bounds B k H0 L1 l) as b_zero.
    contradiction.
  }
Qed.

Lemma kron_cancel_l: forall {m n o p} (A : Matrix m n) (B C : Matrix o p),
  WF_Matrix B -> WF_Matrix C -> A <> Zero -> A ⊗ B = A ⊗ C -> B = C.
Proof.
  intros.
  rewrite nonzero_def in H1.
  destruct H1 as [i [j nonzero_def]].
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
    + apply Nat.ltb_ge in L2.
      pose proof (col_out_of_bounds B y H L2) as b_zero.
      pose proof (col_out_of_bounds C y H0 L2) as c_zero.
      rewrite b_zero, c_zero.
      reflexivity.
  - apply Nat.ltb_ge in L1.
    pose proof (row_out_of_bounds B x H L1) as b_zero.
    pose proof (row_out_of_bounds C x H0 L1) as c_zero.
    rewrite b_zero, c_zero.
    reflexivity.
Qed.

Lemma kron_cancel_r: forall {m n o p} (A B : Matrix m n) (C : Matrix o p),
  WF_Matrix A -> WF_Matrix B -> WF_Matrix C -> C <> Zero -> A ⊗ C = B ⊗ C -> A = B.
Proof.
  intros.
  rewrite nonzero_def in H2.
  destruct H2 as [i [j H2]].
  prep_matrix_equality.
  apply (f_equal (fun f => f (x * o + i) (y * p + j)))%nat in H3.
  unfold kron in H3.
  destruct (x <? m) eqn:L1.
  apply Nat.ltb_lt in L1.
  - destruct (y <? n) eqn:L2.
    apply Nat.ltb_lt in L2.
    + destruct (i <? o) eqn:L3.
      apply Nat.ltb_lt in L3.
      * destruct (j <? p) eqn:L4.
        apply Nat.ltb_lt in L4.
        -- revert H3.
           repeat rewrite Nat.div_add_l by lia.
           repeat rewrite Nat.div_small; auto.
           rewrite Nat.add_mod with (n := o) by lia.
           rewrite Nat.add_mod with (n := p) by lia.
           repeat rewrite Nat.mod_mul by lia.
           repeat rewrite Nat.mod_small; auto.
           repeat rewrite Nat.add_0_l.
           repeat rewrite Nat.add_0_r.
           intros.
           apply Cmult_cancel_r with (a := C i j); auto.
        -- apply Nat.ltb_ge in L4.
           pose proof (col_out_of_bounds C j H1 L4 i) as c_zero.
           contradiction.
      * apply Nat.ltb_ge in L3.
        pose proof (row_out_of_bounds C i H1 L3 j) as c_zero.
        contradiction.
    + apply Nat.ltb_ge in L2.
      pose proof (col_out_of_bounds A y H L2) as a_zero.
      pose proof (col_out_of_bounds B y H0 L2) as b_zero.
      rewrite a_zero, b_zero.
      reflexivity.
  - apply Nat.ltb_ge in L1.
    pose proof (row_out_of_bounds A x H L1) as a_zero.
    pose proof (row_out_of_bounds B x H0 L1) as b_zero.
    rewrite a_zero, b_zero.
    reflexivity.
Qed.

Lemma nonzero_qubit0: ∣0⟩ <> Zero.
Proof.
  intro.
  apply f_equal with (f := fun f => f 0%nat 0%nat) in H.
  contradict H.
  exact C1_neq_C0.
Qed.

Lemma nonzero_qubit1: ∣1⟩ <> Zero.
Proof.
  intro.
  apply f_equal with (f := fun f => f 1%nat 0%nat) in H.
  contradict H.
  exact C1_neq_C0.
Qed.

Lemma kron_0_cancel_l: forall {m n} (B C : Matrix m n),
  WF_Matrix B -> WF_Matrix C -> ∣0⟩ ⊗ B = ∣0⟩ ⊗ C -> B = C.
Proof.
  intros.
  apply (@kron_cancel_l 2 1) with (A := ∣0⟩); auto.
  exact nonzero_qubit0.
Qed.

Lemma kron_1_cancel_l: forall {m n} (B C : Matrix m n),
  WF_Matrix B -> WF_Matrix C -> ∣1⟩ ⊗ B = ∣1⟩ ⊗ C -> B = C.
Proof.
  intros.
  apply (@kron_cancel_l 2 1) with (A := ∣1⟩); auto.
  exact nonzero_qubit1.
Qed.

Lemma kron_0_cancel_r: forall {m n} (A B : Matrix m n),
  WF_Matrix A -> WF_Matrix B -> A ⊗ ∣0⟩ = B ⊗ ∣0⟩ -> A = B.
Proof.
  intros.
  apply (@kron_cancel_r _ _ 2 1) with (C := ∣0⟩); auto.
  exact WF_qubit0.
  exact nonzero_qubit0.
Qed.

Lemma kron_1_cancel_r: forall {m n} (A B : Matrix m n),
  WF_Matrix A -> WF_Matrix B -> A ⊗ ∣1⟩ = B ⊗ ∣1⟩ -> A = B.
Proof.
  intros.
  apply (@kron_cancel_r _ _ 2 1) with (C := ∣1⟩); auto.
  exact WF_qubit1.
  exact nonzero_qubit1.
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

Definition WF_Nonnegative {m n} (A : Matrix m n) :=
WF_Matrix A /\ forall (i j: nat), Re (A i j) >= 0 /\ Im (A i j) = 0.

Lemma SVD_2: forall (A : Square 2), 
exists (U L V: Square 2), 
WF_Unitary U /\ WF_Unitary V /\ WF_Diagonal L /\ WF_Nonnegative L /\ A = U × L × V.
Proof. 
Admitted.

Lemma amplitudes_of_unit {n}: forall (a b : C) (u v w: Vector n), 
u = a .* v .+ b .* w -> ⟨ u , u ⟩ = C1 -> ⟨ v , v ⟩ = C1 -> ⟨ w , w ⟩ = C1 -> 
⟨ v , w ⟩ = C0 -> a ^* * a + b ^* * b = C1.
Proof.
intros a b u v w u_def u_unit v_unit w_unit vw_orthogonal.
revert u_unit.
rewrite u_def.
repeat rewrite inner_product_plus_l. repeat rewrite inner_product_plus_r.
repeat rewrite inner_product_scale_l. repeat rewrite inner_product_scale_r.
rewrite inner_product_conj_sym with (u := w).
repeat rewrite vw_orthogonal. rewrite v_unit. rewrite w_unit.
Csimpl.
trivial.
Qed.

Lemma kron_inner_prod {m n} : forall (u v: Vector m) (w z: Vector n),
  ⟨ u ⊗ w, v ⊗ z ⟩ = ⟨ u, v ⟩ * ⟨ w, z ⟩.
Proof.
  intros.
  destruct n.
  - unfold inner_product, Mmult.
    rewrite Nat.mul_0_r.
    lca.
  - unfold inner_product, Mmult.
    rewrite (@big_sum_product Complex.C _ _ _ C_is_ring). 2: auto.
    apply big_sum_eq.
    apply functional_extensionality; intro.
    lca.
Qed.

Definition TensorProd (u : Vector 4) := WF_Matrix u -> exists (v w : Vector 2), WF_Matrix v /\ WF_Matrix w /\ u = v ⊗ w.
Definition Entangled (u : Vector 4) := not (TensorProd u).

Definition linearly_independent_2vec {n} (v1 v2 : Vector n) := 
  forall (c1 c2 : C), c1 .* v1 .+ c2 .* v2 = Zero -> c1 = 0 /\ c2=0.

Lemma lin_indep_comm_2vec {n}:
forall (v1 v2 : Vector n), 
linearly_independent_2vec v1 v2 <-> linearly_independent_2vec v2 v1.
Proof.
split.
{
  intros.
  unfold linearly_independent_2vec.
  intros.
  rewrite Mplus_comm in H0.
  rewrite and_comm.
  apply H. apply H0.
}
{
  intros.
  unfold linearly_independent_2vec.
  intros.
  rewrite Mplus_comm in H0.
  rewrite and_comm.
  apply H. apply H0.
}
Qed.

Lemma inner_prod_0_decomp {n}: forall (u v: Vector n), 
WF_Matrix u -> WF_Matrix v -> ⟨ u , v ⟩ = C0 <-> u† × v = Zero.
Proof.
split.
intros.
lma'.
unfold inner_product in H1.
rewrite H1. lca.
intros.
unfold inner_product.
rewrite H1. lca.
Qed.

Lemma inner_prod_1_decomp {n}: forall (u v: Vector n), 
WF_Matrix u -> WF_Matrix v -> ⟨ u , v ⟩ = C1 <-> u† × v = I 1.
Proof.
split.
intros.
lma'.
unfold inner_product in H1.
rewrite H1. lca.
intros.
unfold inner_product.
rewrite H1. lca.
Qed.

Lemma inner_prod_0_comm {n}: forall (u v: Vector n), 
WF_Matrix u -> WF_Matrix v -> ⟨ u , v ⟩ = C0 <-> ⟨ v , u ⟩ = C0.
split.
intros.
rewrite inner_product_conj_sym.
rewrite <- Cconj_0.
apply Cconj_simplify. do 2 rewrite Cconj_involutive. assumption.
intros.
rewrite inner_product_conj_sym.
rewrite <- Cconj_0.
apply Cconj_simplify. do 2 rewrite Cconj_involutive. assumption.
Qed.

Lemma block_decomp_4: forall (U: Square 4), WF_Matrix U ->
exists (P00 P01 P10 P11: Square 2), 
WF_Matrix P00 /\ WF_Matrix P01 /\ WF_Matrix P10 /\ WF_Matrix P11 /\
U = ∣0⟩⟨0∣ ⊗ P00 .+ ∣0⟩⟨1∣ ⊗ P01 .+ ∣1⟩⟨0∣ ⊗ P10 .+ ∣1⟩⟨1∣ ⊗ P11.
Proof.
intros U WF_U.
set (P00 := (fun x y =>
match (x,y) with
| (0,0) => (U 0 0)%nat
| (0,1) => (U 0 1)%nat
| (1,0) => (U 1 0)%nat
| (1,1) => (U 1 1)%nat
| _ => C0
end) : (Square 2)).
set (P01 := (fun x y =>
match (x,y) with
| (0,0) => (U 0 2)%nat
| (0,1) => (U 0 3)%nat
| (1,0) => (U 1 2)%nat
| (1,1) => (U 1 3)%nat
| _ => C0
end) : (Square 2)).
set (P10 := (fun x y =>
match (x,y) with
| (0,0) => (U 2 0)%nat
| (0,1) => (U 2 1)%nat
| (1,0) => (U 3 0)%nat
| (1,1) => (U 3 1)%nat
| _ => C0
end) : (Square 2)).
set (P11 := (fun x y =>
match (x,y) with
| (0,0) => (U 2 2)%nat
| (0,1) => (U 2 3)%nat
| (1,0) => (U 3 2)%nat
| (1,1) => (U 3 3)%nat
| _ => C0
end) : (Square 2)).
exists P00, P01, P10, P11.
assert (WF_P00: WF_Matrix P00). 
{
    unfold WF_Matrix. intros.
    unfold P00.
    destruct H.
    destruct x as [|x']. contradict H. lia.
    destruct x' as [| x'']. contradict H. lia. 
    reflexivity.
    destruct x as [|x'].
    destruct y as [|y']. contradict H. lia.
    destruct y' as [| y'']. contradict H. lia.
    reflexivity.
    destruct x' as [| x''].
    destruct y as [| y']. contradict H. lia. 
    destruct y' as [| y'']. contradict H. lia.
    reflexivity.
    reflexivity.
}
split. assumption.
assert (WF_P01: WF_Matrix P01). 
{
    unfold WF_Matrix. intros.
    unfold P01.
    destruct H.
    destruct x as [|x']. contradict H. lia.
    destruct x' as [| x'']. contradict H. lia. 
    reflexivity.
    destruct x as [|x'].
    destruct y as [|y']. contradict H. lia.
    destruct y' as [| y'']. contradict H. lia.
    reflexivity.
    destruct x' as [| x''].
    destruct y as [| y']. contradict H. lia. 
    destruct y' as [| y'']. contradict H. lia.
    reflexivity.
    reflexivity.
}
split. assumption.
assert (WF_P10: WF_Matrix P10). 
{
    unfold WF_Matrix. intros.
    unfold P10.
    destruct H.
    destruct x as [|x']. contradict H. lia.
    destruct x' as [| x'']. contradict H. lia. 
    reflexivity.
    destruct x as [|x'].
    destruct y as [|y']. contradict H. lia.
    destruct y' as [| y'']. contradict H. lia.
    reflexivity.
    destruct x' as [| x''].
    destruct y as [| y']. contradict H. lia. 
    destruct y' as [| y'']. contradict H. lia.
    reflexivity.
    reflexivity.
}
split. assumption.
assert (WF_P11: WF_Matrix P11). 
{
    unfold WF_Matrix. intros.
    unfold P11.
    destruct H.
    destruct x as [|x']. contradict H. lia.
    destruct x' as [| x'']. contradict H. lia. 
    reflexivity.
    destruct x as [|x'].
    destruct y as [|y']. contradict H. lia.
    destruct y' as [| y'']. contradict H. lia.
    reflexivity.
    destruct x' as [| x''].
    destruct y as [| y']. contradict H. lia. 
    destruct y' as [| y'']. contradict H. lia.
    reflexivity.
    reflexivity.
}
split. assumption.
lma'. apply WF_blockmatrix. 1,2,3,4: assumption.
all: unfold Mplus, kron, "∣0⟩⟨0∣", "∣0⟩⟨1∣", "∣1⟩⟨0∣", "∣1⟩⟨1∣", Mmult, adjoint.
all: simpl.
all: Csimpl.
1,2,5,6: unfold P00.
5,6,7,8: unfold P01.
9,10,13,14: unfold P10.
13,14,15,16: unfold P11.
all: lca.
Qed.

Lemma element_equiv_vec_element {m n}: forall (A: Matrix m n), 
WF_Matrix A -> 
forall (i j: nat), 
A i j = (get_vec j A) i 0%nat.
Proof. 
intros.
unfold get_vec.
simpl.
reflexivity.
Qed.

Lemma column_equal_implies_equal {m n}: forall (A B: Matrix m n),
WF_Matrix A -> WF_Matrix B ->
(forall (j: nat), get_vec j A = get_vec j B) -> A = B.
intros.
lma'.
rewrite element_equiv_vec_element. 2: assumption.
rewrite H1.
rewrite <- element_equiv_vec_element. 2: assumption. 
reflexivity.
Qed.


Lemma vector_mult_simplify {m n}: forall (A B: Matrix m n),
WF_Matrix A -> WF_Matrix B -> 
(forall (w : Vector n), WF_Matrix w -> A × w = B × w) -> A = B.
Proof.
intros.
apply column_equal_implies_equal. 1,2: assumption.
intros.
destruct (PeanoNat.Nat.lt_total j n).
rewrite matrix_by_basis. rewrite matrix_by_basis. 2,3: assumption.
apply H1. apply WF_e_i.
unfold get_vec.
apply functional_extensionality. intros.
apply functional_extensionality. intros y.
destruct (y =? 0). 2: reflexivity.
destruct H2.
unfold WF_Matrix in *.
rewrite H. rewrite H0. reflexivity.
1,2: right.
1,2: rewrite H2.
1,2: apply Nat.le_refl.
unfold WF_Matrix in *.
rewrite H. rewrite H0. reflexivity.
1,2: right.
1,2: apply Nat.lt_le_incl in H2.
1,2: apply H2.
Qed.

Lemma unitary_mult_zero_cancel_r {n}: 
forall (A B: Square n), 
WF_Matrix A -> WF_Unitary B -> A × B = Zero -> A = Zero.
Proof.
intros A B WF_a b_unitary prod_zero.
apply (f_equal (fun f => f × B†)) in prod_zero.
apply transpose_unitary in b_unitary.
destruct b_unitary as [WF_Bdag Bdag_I].
rewrite adjoint_involutive in Bdag_I.
rewrite Mmult_assoc in prod_zero.
rewrite Bdag_I in prod_zero.
rewrite Mmult_1_r in prod_zero. 2: assumption.
rewrite Mmult_0_l in prod_zero.
apply prod_zero.
Qed.

Lemma adjoint00: (∣0⟩⟨0∣) † = ∣0⟩⟨0∣. Proof. lma'. Qed.
Lemma adjoint01: (∣0⟩⟨1∣) † = ∣1⟩⟨0∣. Proof. lma'. Qed.
Lemma adjoint10: (∣1⟩⟨0∣) † = ∣0⟩⟨1∣. Proof. lma'. Qed.
Lemma adjoint11: (∣1⟩⟨1∣) † = ∣1⟩⟨1∣. Proof. lma'. Qed.

Lemma Mplus_opp_0_r {m n}: forall (A: Matrix m n), 
WF_Matrix A -> A .+ Mopp (A) = Zero.
intros.
lma'.
solve_WF_matrix.
Qed.

Lemma Mplus_opp_0_l {m n}: forall (A: Matrix m n), 
WF_Matrix A -> Mopp (A) .+ A = Zero.
intros.
rewrite Mplus_comm.
apply Mplus_opp_0_r.
assumption.
Qed.

Lemma kron_opp_distr_l {m n o p}: forall (A: Matrix m n) (B: Matrix o p), 
WF_Matrix A -> WF_Matrix B -> Mopp (A ⊗ B) = (Mopp A) ⊗ B.
Proof. 
intros.
lma'.
all: solve_WF_matrix.
Qed.

Lemma Mscale_eq_0_implies_0 {m n}: forall (A : Matrix m n) (c : C), 
WF_Matrix A -> A <> Zero -> c .* A = Zero -> c = 0.
Proof.
intros.
rewrite nonzero_def in H0.
destruct H0 as [x [y Aij_neq_0]].
rewrite zero_def in H1.
specialize (H1 x y).
apply Cmult_integral in H1.
destruct H1.
assumption.
contradict H0.
assumption.
Qed.

Lemma I_neq_zero: forall (n: nat), (n > 0)%nat -> I n <> Zero.
Proof.
intros.
rewrite nonzero_def.
exists 0%nat, 0%nat.
unfold I.
simpl.
destruct (0 <? n) eqn:Hlt.
apply C1_neq_C0.
apply Nat.ltb_ge in Hlt.
contradict H.
apply Nat.le_ngt.
assumption.
Qed.

Lemma orthonormal_implies_lin_indep_2 {n}: forall (a b: Vector n), 
WF_Matrix a -> WF_Matrix b -> ⟨ a, a ⟩ = 1 -> ⟨ b, b ⟩ = 1 -> ⟨ a, b ⟩ = 0
-> linearly_independent_2vec a b.
Proof.
unfold linearly_independent_2vec.
intros.
rewrite inner_prod_1_decomp in H1.
rewrite inner_prod_1_decomp in H2.
2,3,4,5: assumption.
split.
{
    rewrite inner_prod_0_decomp in H3. 2,3: assumption.
    apply (f_equal (fun f => (a) † × f)) in H4.
    rewrite Mmult_0_r in H4.
    rewrite Mmult_plus_distr_l in H4.
    do 2 rewrite Mscale_mult_dist_r in H4.
    rewrite H1, H3 in H4.
    rewrite Mscale_0_r in H4.
    rewrite Mplus_0_r in H4.
    apply (@Mscale_eq_0_implies_0 1 1) with (A:= I 1). 1: solve_WF_matrix.
    apply I_neq_zero. lia.
    assumption.
}
{
    apply (f_equal (fun f => (b) † × f)) in H4.
    rewrite Mmult_0_r in H4.
    rewrite Mmult_plus_distr_l in H4.
    do 2 rewrite Mscale_mult_dist_r in H4.
    rewrite inner_prod_0_comm in H3. 2,3: assumption.
    rewrite inner_prod_0_decomp in H3. 2,3: assumption.
    rewrite H2, H3 in H4.
    rewrite Mscale_0_r in H4.
    rewrite Mplus_0_l in H4.
    apply (@Mscale_eq_0_implies_0 1 1) with (A:= I 1). 1: solve_WF_matrix.
    apply I_neq_zero. lia.
    assumption.
}
Qed.

Lemma Mscale_access {m n}: forall (a : C) (B : Matrix m n) (i j : nat), 
a * (B i j) = (a .* B) i j.
Proof.
intros.
lca.
Qed.

Lemma Mplus_access {m n}: forall (A B : Matrix m n) (i j : nat), 
(A .+ B) i j = (A i j) + (B i j).
Proof.
intros.
lca.
Qed.

Lemma Mopp_scale_distr_l {m n}: forall (A : Matrix m n) (c : C), 
Mopp (c .* A) = c .* (Mopp A).
Proof.
intros.
unfold Mopp.
do 2 rewrite Mscale_assoc.
rewrite Cmult_comm.
reflexivity.
Qed.

Lemma Mscale_0_cancel {m n}: forall (c: C) (A: Matrix m n), 
A <> Zero -> Zero = c .* A -> c = 0.
Proof.
intros.
rewrite nonzero_def in H.
destruct H as [x0 [y0 nonzero_point]].
assert ((c .* A) x0 y0 = 0). rewrite <- H0. trivial.
rewrite <- Mscale_access in H.
apply (f_equal (fun f => f * /(A x0 y0))) in H.
rewrite Cmult_0_l in H.
rewrite <- Cmult_assoc in H.
rewrite Cinv_r in H.
rewrite Cmult_1_r in H.
all: assumption.
Qed.