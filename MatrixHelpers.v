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

Definition diag4 (c1 c2 c3 c4 : C) : Square 4 :=
  fun x y =>
    match (x,y) with
    | (0, 0) => c1
    | (1, 1) => c2
    | (2, 2) => c3
    | (3, 3) => c4
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

Lemma WF_diag4: forall (c1 c2 c3 c4 : C), WF_Matrix (diag4 c1 c2 c3 c4).
Proof.
  unfold WF_Matrix.
  intros.
  destruct H.
  {
    unfold diag4.
    destruct x.
    - lia.
    - destruct x.
      + lia.
      + destruct x.
        * lia.
        * destruct x.
          lia. reflexivity.
  }
  {
    unfold diag4.
    destruct y.
    - lia.
    - destruct y.
      + lia.
      + destruct y.
        * lia.
        * destruct y.
          -- lia.
          -- destruct x.
             ++ reflexivity.
             ++ destruct x.
                ** reflexivity.
                ** destruct x.
                   --- reflexivity.
                   --- destruct x; reflexivity.
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

Lemma Mscale_cancel_l: forall {m n} (c : C) (A B : Matrix m n),
  c <> C0 -> c .* A = c .* B -> A = B.
Proof.
  intros.
  prep_matrix_equality.
  apply Cmult_cancel_l with (a := c); auto.
  apply (f_equal (fun f => f x y)) in H0.
  unfold scale in H0.
  exact H0.
Qed.

Lemma Mscale_cancel_r: forall {m n} (c1 c2 : C) (A : Matrix m n),
  A <> Zero -> c1 .* A = c2 .* A -> c1 = c2.
Proof.
  intros.
  rewrite nonzero_def in H.
  destruct H as [i [j a_nonzero]].
  apply (f_equal (fun f => f i j)) in H0.
  unfold scale in H0.
  apply Cmult_cancel_r with (a := A i j); auto.
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

Lemma nat_tight_bound: forall (i j: nat), 
(i <= j -> j < S i -> i = j)%nat.
Proof.
intros i j lb up.
apply Nat.le_antisymm.
assumption.
apply le_S_n. apply up.
Qed.

Lemma sub_mod_equiv: forall (i j: nat), 
(i < j * 2 -> j <= i -> (i mod j) = i - j)%nat.
Proof.
intros.
assert ((i - j) = ((i - j) mod j))%nat.
{
  symmetry.
  apply Nat.mod_small.
  lia.
}
rewrite H1.
symmetry.
rewrite <- Nat.mul_1_l with (n := j) at 1.
apply sub_mul_mod.
rewrite Nat.mul_1_l.
assumption.
Qed.


Lemma upper_left_block_entries {n}: forall (A : Square n) (i j: nat), 
(i < n /\ j < n)%nat -> (∣0⟩⟨0∣ ⊗ A) i j = A i j.
Proof.
intros.
unfold kron.
destruct H.
rewrite Nat.div_small. 2: assumption.
rewrite Nat.div_small. 2: assumption.
rewrite Nat.mod_small. 2: assumption.
rewrite Nat.mod_small. 2: assumption.
lca.
Qed.

Lemma upper_left_block_nonentries {n}: forall (A : Square n) (i j: nat), 
WF_Matrix A -> n <> 0%nat -> (n <= i \/ n <= j)%nat -> (∣0⟩⟨0∣ ⊗ A) i j = 0.
Proof.
intros A i j WF_A nn0 ij_bound.
assert (WF_block: WF_Matrix (∣0⟩⟨0∣ ⊗ A)). solve_WF_matrix.
destruct ij_bound.
{
  rewrite <- Nat.mul_1_r with (n:=n) in H.
  apply Nat.div_le_lower_bound in H. 2: assumption.
  destruct (le_lt_dec (n*2)%nat i). rewrite WF_block. reflexivity. left. lia.
  apply Nat.div_lt_upper_bound in l. 2: lia.
  assert (ind_val:= nat_tight_bound 1 (i/n)%nat H l).
  unfold kron.
  rewrite <- ind_val.
  lca.
}
{
  rewrite <- Nat.mul_1_r with (n:=n) in H.
  apply Nat.div_le_lower_bound in H. 2: assumption.
  destruct (le_lt_dec (n*2)%nat j). rewrite WF_block. reflexivity. right. lia.
  apply Nat.div_lt_upper_bound in l. 2: lia.
  assert (ind_val:= nat_tight_bound 1 (j/n)%nat H l).
  unfold kron.
  rewrite <- ind_val.
  lca.
}
Qed.

Lemma lower_left_block_entries {n}: forall (A : Square n) (i j: nat), 
WF_Matrix A -> n <> 0%nat -> (i >= n /\ j < n)%nat -> (∣1⟩⟨0∣ ⊗ A) i j = A (i-n)%nat j.
Proof.
intros A i j WF_A n0 H.
destruct H.
assert (WF_block: WF_Matrix (∣1⟩⟨0∣ ⊗ A)). solve_WF_matrix.
destruct (le_lt_dec (n*2)%nat i). rewrite WF_block. rewrite WF_A. reflexivity. left. lia. left. lia.
unfold kron.
assert (n <= i)%nat. lia.
rewrite <- Nat.mul_1_r with (n:=n) in H1.
assert (ilb :  (n <= i)%nat). assumption.
apply Nat.div_le_lower_bound in H1. 2: assumption.
assert (iub : (i < n * 2)%nat). assumption.
apply Nat.div_lt_upper_bound in l. 2: lia.
assert (ind_val:= nat_tight_bound 1 (i/n)%nat H1 l).
rewrite <- ind_val.
rewrite Nat.div_small with (a:= j). 2: assumption.
assert (sub_mod:= sub_mod_equiv i n iub ilb).
rewrite sub_mod.
assert (j mod n = j). apply Nat.mod_small. assumption.
rewrite H2.
lca.
Qed.

Lemma lower_left_block_nonentries {n}: forall (A : Square n) (i j: nat), 
WF_Matrix A -> n <> 0%nat -> (i < n \/ n <= j)%nat -> (∣1⟩⟨0∣ ⊗ A) i j = 0.
Proof.
intros A i j WF_A nn0 ij_bound. 
assert (WF_block: WF_Matrix (∣1⟩⟨0∣ ⊗ A)). solve_WF_matrix.
destruct ij_bound.
{
  unfold kron.
  rewrite Nat.div_small. 2: assumption.
  lca.
}
{
  rewrite <- Nat.mul_1_r with (n:=n) in H.
  apply Nat.div_le_lower_bound in H. 2: assumption.
  destruct (le_lt_dec (n*2)%nat j). rewrite WF_block. reflexivity. right. lia.
  apply Nat.div_lt_upper_bound in l. 2: lia.
  assert (ind_val:= nat_tight_bound 1 (j/n)%nat H l).
  unfold kron.
  rewrite <- ind_val.
  lca.
}
Qed.

Lemma upper_right_block_entries {n}: forall (A : Square n) (i j: nat), 
WF_Matrix A -> n <> 0%nat -> (i < n /\ j >= n)%nat -> (∣0⟩⟨1∣ ⊗ A) i j = A i (j-n)%nat.
Proof.
intros A i j WF_A n0 H.
destruct H.
assert (WF_block: WF_Matrix (∣0⟩⟨1∣ ⊗ A)). solve_WF_matrix.
destruct (le_lt_dec (n*2)%nat j). rewrite WF_block. rewrite WF_A. reflexivity. right. lia. right. lia.
unfold kron.
assert (n <= j)%nat. lia.
rewrite <- Nat.mul_1_r with (n:=n) in H1.
assert (jlb :  (n <= j)%nat). assumption.
apply Nat.div_le_lower_bound in H1. 2: assumption.
assert (jub : (j < n * 2)%nat). assumption.
apply Nat.div_lt_upper_bound in l. 2: lia.
assert (ind_val:= nat_tight_bound 1 (j/n)%nat H1 l).
rewrite <- ind_val.
rewrite Nat.div_small with (a:= i). 2: assumption.
assert (sub_mod:= sub_mod_equiv j n jub jlb).
rewrite sub_mod.
assert (i mod n = i). apply Nat.mod_small. assumption.
rewrite H2.
lca.
Qed.

Lemma upper_right_block_nonentries {n}: forall (A : Square n) (i j: nat), 
WF_Matrix A -> n <> 0%nat -> (n <= i \/ j < n)%nat -> (∣0⟩⟨1∣ ⊗ A) i j = 0.
Proof.
intros A i j WF_A nn0 ij_bound. 
assert (WF_block: WF_Matrix (∣0⟩⟨1∣ ⊗ A)). solve_WF_matrix.
destruct ij_bound.
{
  rewrite <- Nat.mul_1_r with (n:=n) in H.
  apply Nat.div_le_lower_bound in H. 2: assumption.
  destruct (le_lt_dec (n*2)%nat i). rewrite WF_block. reflexivity. left. lia.
  apply Nat.div_lt_upper_bound in l. 2: lia.
  assert (ind_val:= nat_tight_bound 1 (i/n)%nat H l).
  unfold kron.
  rewrite <- ind_val.
  lca.
}
{
  unfold kron.
  rewrite Nat.div_small with (a:= j). 2: assumption.
  lca.
}
Qed.

Lemma lower_right_block_entries {n}: forall (A : Square n) (i j: nat), 
WF_Matrix A -> n <> 0%nat -> (i >= n /\ j >= n)%nat -> (∣1⟩⟨1∣ ⊗ A) i j = A (i-n)%nat (j-n)%nat.
Proof.
intros A i j WF_A n0 H.
destruct H.
assert (WF_block: WF_Matrix (∣1⟩⟨1∣ ⊗ A)). solve_WF_matrix.
destruct (le_lt_dec (n*2)%nat j). rewrite WF_block. rewrite WF_A. reflexivity. right. lia. right. lia.
destruct (le_lt_dec (n*2)%nat i). rewrite WF_block. rewrite WF_A. reflexivity. left. lia. left. lia.
unfold kron.
assert (n <= j)%nat. lia.
rewrite <- Nat.mul_1_r with (n:=n) in H1.
assert (jlb :  (n <= j)%nat). assumption.
apply Nat.div_le_lower_bound in H1. 2: assumption.
assert (jub : (j < n * 2)%nat). assumption.
apply Nat.div_lt_upper_bound in l. 2: lia.
assert (ind_val:= nat_tight_bound 1 (j/n)%nat H1 l).
rewrite <- ind_val.
assert (n <= i)%nat. lia.
rewrite <- Nat.mul_1_r with (n:=n) in H2.
assert (ilb :  (n <= i)%nat). assumption.
apply Nat.div_le_lower_bound in H2. 2: assumption.
assert (iub : (i < n * 2)%nat). assumption.
apply Nat.div_lt_upper_bound in l0. 2: lia.
assert (ind_val_i:= nat_tight_bound 1 (i/n)%nat H2 l0).
rewrite <- ind_val_i.
assert (sub_mod:= sub_mod_equiv j n jub jlb).
rewrite sub_mod.
assert (sub_mod_i:= sub_mod_equiv i n iub ilb).
rewrite sub_mod_i.
lca.
Qed.

Lemma lower_right_block_nonentries {n}: forall (A : Square n) (i j: nat), 
WF_Matrix A -> n <> 0%nat -> (i < n \/ j < n)%nat -> (∣1⟩⟨1∣ ⊗ A) i j = 0.
Proof.
intros A i j WF_A nn0 ij_bound. 
destruct ij_bound.
{
  unfold kron.
  rewrite Nat.div_small with (a:= i). 2: assumption.
  lca.
}
{
  unfold kron.
  rewrite Nat.div_small with (a:= j). 2: assumption.
  lca.
}
Qed.

Lemma block_equalities_general {n}: forall (U V: Square (n+n)) (P00 P01 P10 P11 Q00 Q01 Q10 Q11: Square n), 
WF_Matrix P00 -> WF_Matrix P01 -> WF_Matrix P10 -> WF_Matrix P11 ->
WF_Matrix Q00 -> WF_Matrix Q01 -> WF_Matrix Q10 -> WF_Matrix Q11 ->
U = ∣0⟩⟨0∣ ⊗ P00 .+ ∣0⟩⟨1∣ ⊗ P01 .+ ∣1⟩⟨0∣ ⊗ P10 .+ ∣1⟩⟨1∣ ⊗ P11 ->
V = ∣0⟩⟨0∣ ⊗ Q00 .+ ∣0⟩⟨1∣ ⊗ Q01 .+ ∣1⟩⟨0∣ ⊗ Q10 .+ ∣1⟩⟨1∣ ⊗ Q11 ->
U = V -> P00 = Q00 /\ P01 = Q01 /\ P10 = Q10 /\ P11 = Q11.
Proof.
intros U V P00 P01 P10 P11 Q00 Q01 Q10 Q11 WF_P00 WF_P01 WF_P10 WF_P11 WF_Q00 WF_Q01 WF_Q10 WF_Q11 u_def v_def u_eq_v.
split.
{
  lma'.
  destruct (le_lt_dec n i). rewrite WF_P00, WF_Q00. reflexivity. 1,2: left. 1,2: lia.
  destruct (le_lt_dec n j). rewrite WF_P00, WF_Q00. reflexivity. 1,2: right. 1,2: lia.
}
Admitted.

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
Definition linearly_dependent_2vec {n} (v1 v2 : Vector n) :=
  not (linearly_independent_2vec v1 v2).

Lemma implication_decomp: forall (P Q: Prop),
(P -> Q) <-> ((not P) \/ Q).
Proof.
split.
apply Coq.Logic.Classical_Prop.imply_to_or.
apply Coq.Logic.Classical_Prop.or_to_imply.
Qed.

Lemma Mscale_access {m n}: forall (a : C) (B : Matrix m n) (i j : nat), 
a * (B i j) = (a .* B) i j.
Proof.
intros.
lca.
Qed.

Lemma Cmult_neq_zero: forall (a b: C), 
a <> 0 -> b <> 0 -> a * b <> 0.
Proof.
intros.
unfold not.
intros.
apply H.
apply (f_equal (fun f => f * /b)) in H1.
rewrite Cmult_0_l in H1.
rewrite <- Cmult_assoc in H1.
rewrite Cinv_r in H1. 2: assumption.
rewrite Cmult_1_r in H1.
assumption.
Qed.

Lemma Mscale_neq_zero {m n}: forall (c: C) (A : Matrix m n), 
c <> 0 -> A <> Zero -> c .* A <> Zero.
Proof.
intros.
rewrite nonzero_def in *.
destruct H0. destruct H0.
exists x, x0.
rewrite <- Mscale_access.
apply Cmult_neq_zero.
all: assumption.
Qed.

Lemma Mplus_neq_zero {m n}: forall (A B: Matrix m n), 
A <> Zero -> A .+ B = Zero -> B <> Zero.
Proof.
intros.
unfold not.
intros.
apply H.
rewrite H1 in H0.
rewrite Mplus_0_r in H0.
assumption.
Qed.

Lemma Mscale_neq_zero_implies_all_nonzero {m n}: forall (c: C) (A : Matrix m n),
c .* A <> Zero -> (c <> 0 /\ A <> Zero).
Proof.
intros.
split.
{
  unfold not. 
  intros.
  apply H.
  rewrite H0.
  rewrite Mscale_0_l.
  reflexivity.
}
{
  unfold not. 
  intro.
  apply H.
  rewrite H0.
  rewrite Mscale_0_r.
  reflexivity.
}
Qed.

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

Lemma neq_equiv_oppneq: forall (a b : C), 
a <> b <-> -a <> -b.
Proof.
intros.
split.
{
  intros.
  unfold not.
  intros.
  apply H.
  rewrite <- Copp_involutive.
  rewrite <- H0.
  rewrite Copp_involutive.
  reflexivity.
}
{
  intros.
  unfold not. 
  intros. 
  apply H.
  rewrite H0.
  reflexivity.
}
Qed.

Lemma lin_dep_def_alt {n}: forall (v1 v2: Vector n),
WF_Matrix v1 ->  WF_Matrix v2 -> 
linearly_dependent_2vec v1 v2 <-> 
v1 = Zero \/ exists (c: C), c .* v1 = v2.
Proof.
intros v1 v2 WF_v1 WF_v2.
split.
{
 intros.
 destruct (vec_equiv_dec v1 Zero).
 left.
 apply mat_equiv_eq. 1,2: solve_WF_matrix. assumption. 
 right.
 assert (v1 <> Zero).
 {
  unfold not.
  intros.
  apply n0.
  rewrite H0.
  apply mat_equiv_refl.
 }
 clear n0.
 unfold linearly_dependent_2vec in H.
 unfold linearly_independent_2vec in H.
 apply Coq.Logic.Classical_Pred_Type.not_all_ex_not in H.
 destruct H as [c1 nfa].
 apply Coq.Logic.Classical_Pred_Type.not_all_ex_not in nfa.
 destruct nfa as [c2 nimpl].
 rewrite implication_decomp in nimpl.
 apply Coq.Logic.Classical_Prop.not_or_and in nimpl.
 destruct nimpl as [comb_zero const_zero].
 apply Coq.Logic.Classical_Prop.NNPP in comb_zero.
 apply Coq.Logic.Classical_Prop.not_and_or in const_zero.
 destruct const_zero.
 {
    assert (c1v1_n0 := Mscale_neq_zero c1 v1 H H0).
    assert (c2v2_n0 := Mplus_neq_zero (c1 .* v1) (c2 .* v2) c1v1_n0 comb_zero).
    assert (c2andv2_n0 := Mscale_neq_zero_implies_all_nonzero c2 v2 c2v2_n0).
    destruct c2andv2_n0 as [c2_n0 v2_n0].
    apply (f_equal (fun f => f .+ Mopp (c2 .* v2))) in comb_zero.
    rewrite Mplus_0_l in comb_zero.
    rewrite Mplus_assoc in comb_zero.
    rewrite Mplus_opp_0_r in comb_zero. 2: solve_WF_matrix.
    rewrite Mplus_0_r in comb_zero.
    unfold Mopp in comb_zero.
    rewrite Mscale_assoc in comb_zero.
    apply (f_equal (fun f => (/ (- C1 * c2)) .* f)) in comb_zero.
    do 2 rewrite Mscale_assoc in comb_zero.
    rewrite Cinv_l in comb_zero.
    rewrite Mscale_1_l in comb_zero.
    exists (/ (- C1 * c2) * c1).
    assumption.
    apply Cmult_neq_zero. 2: assumption.
    unfold not.
    intro.
    apply complex_split in H1.
    destruct H1.
    contradict H1.
    simpl.
    lra.
  }
  {
    apply (f_equal (fun f => f .+ Mopp (c2 .* v2))) in comb_zero.
    rewrite Mplus_0_l in comb_zero.
    rewrite Mplus_assoc in comb_zero.
    rewrite Mplus_opp_0_r in comb_zero. 2: solve_WF_matrix.
    rewrite Mplus_0_r in comb_zero.
    unfold Mopp in comb_zero.
    rewrite Mscale_assoc in comb_zero.
    apply (f_equal (fun f => (/ (- C1 * c2)) .* f)) in comb_zero.
    do 2 rewrite Mscale_assoc in comb_zero.
    rewrite Cinv_l in comb_zero.
    rewrite Mscale_1_l in comb_zero.
    exists (/ (- C1 * c2) * c1).
    assumption.
    apply Cmult_neq_zero. 2: assumption.
    unfold not.
    intro.
    apply complex_split in H1.
    destruct H1.
    contradict H1.
    simpl.
    lra.
  }
}
{
  intros.
  unfold linearly_dependent_2vec, linearly_independent_2vec.
  destruct H.
  {
    apply Coq.Logic.Classical_Pred_Type.ex_not_not_all.
    exists 1.
    apply Coq.Logic.Classical_Pred_Type.ex_not_not_all.
    exists 0.
    rewrite implication_decomp.
    apply Coq.Logic.Classical_Prop.and_not_or.
    split.
    {
      unfold not.
      intros.
      apply H0.
      rewrite H.
      rewrite Mscale_0_r.
      rewrite Mscale_0_l.
      rewrite Mplus_0_l.
      reflexivity.
    }
    {
      apply Coq.Logic.Classical_Prop.or_not_and.
      left.
      apply C1_neq_C0.
    }
  }
  {
    destruct H.
    apply Coq.Logic.Classical_Pred_Type.ex_not_not_all.
    exists x.
    apply Coq.Logic.Classical_Pred_Type.ex_not_not_all.
    exists (-C1).
    rewrite implication_decomp.
    apply Coq.Logic.Classical_Prop.and_not_or.
    split.
    {
      unfold not.
      intros.
      apply H0.
      rewrite H.
      rewrite <- Mscale_1_l with (A:= v2) at 1.
      rewrite <- Mscale_plus_distr_l.
      replace (C1 + -C1) with (C0) by lca.
      rewrite Mscale_0_l.
      reflexivity.
    }
    {
      apply Coq.Logic.Classical_Prop.or_not_and.
      right.
      rewrite <- Copp_0.
      rewrite <- neq_equiv_oppneq.
      apply C1_neq_C0.
    }
  }
}
Qed.

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

Lemma kron_opp_distr_l {m n o p}: forall (A: Matrix m n) (B: Matrix o p), 
WF_Matrix A -> WF_Matrix B -> Mopp (A ⊗ B) = (Mopp A) ⊗ B.
Proof. 
intros.
lma'.
all: solve_WF_matrix.
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
    apply @Mscale_cancel_r with (A := I 1) (m := 1%nat) (n := 1%nat).
    apply I_neq_zero. lia.
    rewrite H4.
    rewrite Mscale_0_l; reflexivity.
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
    apply @Mscale_cancel_r with (A := I 1) (m := 1%nat) (n := 1%nat).
    apply I_neq_zero. lia.
    rewrite H4.
    rewrite Mscale_0_l; reflexivity.
}
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

Lemma id2_diag2: I 2 = diag2 C1 C1.
Proof.
  lma'.
  apply WF_diag2.
Qed.

Lemma id4_diag4: I 4 = diag4 C1 C1 C1 C1.
Proof.
  lma'.
  apply WF_diag4.
Qed.

Lemma diag2_eigenpairs: forall (c1 c2 : C),
  Eigenpair (diag2 c1 c2) (∣0⟩, c1) /\ Eigenpair (diag2 c1 c2) (∣1⟩, c2).
Proof.
  intros.
  split; unfold Eigenpair; simpl.
  {
    lma'.
    solve_WF_matrix.
    apply WF_diag2.
    unfold Mmult, scale, diag2, qubit0; simpl.
    lca.
  }
  {
    lma'.
    solve_WF_matrix.
    apply WF_diag2.
    unfold Mmult, scale, diag2, qubit1; simpl.
    lca.
  }
Qed.

Lemma diag4_eigenpairs: forall (c1 c2 c3 c4 : C),
  Eigenpair (diag4 c1 c2 c3 c4) (∣0⟩ ⊗ ∣0⟩, c1) /\ Eigenpair (diag4 c1 c2 c3 c4) (∣0⟩ ⊗ ∣1⟩, c2) /\
  Eigenpair (diag4 c1 c2 c3 c4) (∣1⟩ ⊗ ∣0⟩, c3) /\ Eigenpair (diag4 c1 c2 c3 c4) (∣1⟩ ⊗ ∣1⟩, c4).
Proof.
  intros.
  split; unfold Eigenpair; simpl.
  {
    lma'.
    solve_WF_matrix.
    apply WF_diag4.
    unfold Mmult, scale, kron, diag4, qubit0; simpl.
    lca.
  }
  split.
  {
    lma'.
    solve_WF_matrix.
    apply WF_diag4.
    unfold Mmult, scale, kron, diag4, qubit1; simpl.
    lca.
  }
  split.
  {
    lma'.
    solve_WF_matrix.
    apply WF_diag4.
    unfold Mmult, scale, kron, diag4, qubit0; simpl.
    lca.
  }
  {
    lma'.
    solve_WF_matrix.
    apply WF_diag4.
    unfold Mmult, scale, kron, diag4, qubit1; simpl.
    lca.
  }
Qed.

Lemma id2_eigenpairs: Eigenpair (I 2) (∣0⟩, C1) /\ Eigenpair (I 2) (∣1⟩, C1).
Proof.
  rewrite id2_diag2.
  apply diag2_eigenpairs.
Qed.

Lemma id4_eigenpairs: Eigenpair (I 4) (∣0⟩ ⊗ ∣0⟩, C1) /\
  Eigenpair (I 4) (∣0⟩ ⊗ ∣1⟩, C1) /\
  Eigenpair (I 4) (∣1⟩ ⊗ ∣0⟩, C1) /\
  Eigenpair (I 4) (∣1⟩ ⊗ ∣1⟩, C1).
Proof.
  rewrite id4_diag4.
  apply diag4_eigenpairs.
Qed.

Lemma exists_orthogonal_vector: forall (a: Vector 2), 
WF_Matrix a -> exists (b: Vector 2), (WF_Matrix b /\ (b = Zero <-> a = Zero) /\ ⟨ a , b ⟩ = C0).
Proof.
intros.
set (b := (fun x y =>
    match (x,y) with
    | (0,0) => -((a 1%nat 0%nat)^*)
    | (1,0) => (a 0%nat 0%nat)^*
    | _ => C0
    end) : (Vector 2)).
assert (WF_b: WF_Matrix b). 
{
    unfold WF_Matrix.
    intros.
    unfold b. 
    destruct H0.
    destruct x as [|x']. contradict H. lia.
    destruct x' as [|x'']. contradict H. lia. reflexivity.
    destruct x as [|x']. destruct y as [|y']. contradict H. lia. reflexivity.
    destruct x' as [|x'']. destruct y as [|y']. contradict H. lia.
    reflexivity. reflexivity.
}
exists b.
split. assumption.
split. split.
{
    intro.
    lma'.
    replace (a 0%nat 0%nat) with ((b 1%nat 0%nat)^*). rewrite H0. lca.
    unfold b. apply Cconj_involutive.
    replace (a 1%nat 0%nat) with (-(b 0%nat 0%nat)^*). rewrite H0. lca.
    unfold b. lca.
}
{
    intro.
    lma'.
    unfold b. rewrite H0. lca.
    unfold b. rewrite H0. lca.
}
lca.
Qed.

Lemma unitary_preserves_inner_prod {n}: forall (U: Square n) (a b: Vector n), WF_Unitary U -> WF_Matrix b ->
⟨ a , b ⟩ = ⟨ U × a , U × b ⟩.
Proof.
intros.
destruct H as [WF_U u_inv].
unfold inner_product.
rewrite Mmult_adjoint.
rewrite Mmult_assoc.
rewrite <- Mmult_assoc with (B := U).
rewrite u_inv. rewrite Mmult_1_l. 2: assumption.
reflexivity.
Qed.

Lemma kron_11_r_is_scale {m n}: forall (A : Matrix m n) (B : Vector 1),
A ⊗ B = (B 0%nat 0%nat) .* A.
Proof.
intros.
prep_matrix_equality.
unfold kron, scale.
do 2 rewrite Coq.Arith.PeanoNat.Nat.div_1_r.
simpl.
apply Cmult_comm.
Qed.

Lemma lin_dep_comm_2vec {n}: forall (v1 v2 : Vector n), 
linearly_dependent_2vec v1 v2 <-> linearly_dependent_2vec v2 v1.
Proof. 
split.
all: intro.
all: unfold linearly_dependent_2vec in *.
all: unfold not in *.
all: intro.
all: apply H.
all: apply lin_indep_comm_2vec.
all: assumption.
Qed.

Lemma scale_eq_implies_0l_or_ldep {n}:
forall (a b: C) (u v: Vector n), 
WF_Matrix u -> WF_Matrix v -> 
a .* u = b .* v -> (a = 0 /\ b = 0) \/ linearly_dependent_2vec u v.
Proof.
intros.
destruct (Ceq_dec a C0).
destruct (Ceq_dec b C0).
{
    left. split. all: assumption. 
}
all: right.
2: rewrite lin_dep_comm_2vec.
all: rewrite lin_dep_def_alt. 2,3,5,6: assumption.
all: right.
apply (f_equal (fun f => /b .* f)) in H1.
2: apply (f_equal (fun f => /a .* f)) in H1.
all: repeat rewrite Mscale_assoc in H1.
all: rewrite Cinv_l in H1. 2,4: assumption.
all: rewrite Mscale_1_l in H1.
exists (/ b * a). assumption.
exists (/a * b). symmetry. assumption.
Qed.

Lemma cross_prod_equal_implies_scaled_vec: forall (a c: Vector 2),
WF_Matrix a -> WF_Matrix c ->
a 0%nat 0%nat <> 0 -> a 1%nat 0%nat <> 0 ->
(a 0%nat 0%nat) * (c 1%nat 0%nat) = (a 1%nat 0%nat) * (c 0%nat 0%nat) -> 
exists (b: C), b .* a = c.
Proof. 
intros a c WF_a WF_c a0n0 a1n0 cross.
exists ((c 0%nat 0%nat) * /(a 0%nat 0%nat)).
lma'.
{
    rewrite <- Mscale_access.
    rewrite <- Cmult_assoc.
    rewrite Cinv_l. 2: assumption.
    apply Cmult_1_r.
}
{
    assert (c 0%nat 0%nat * / a 0%nat 0%nat = c 1%nat 0%nat * / a 1%nat 0%nat).
    {
        apply (f_equal (fun f => / a 1%nat 0%nat * / a 0%nat 0%nat * f)) in cross.
        replace (/ a 1%nat 0%nat * / a 0%nat 0%nat *
        (a 0%nat 0%nat * c 1%nat 0%nat)) with ((a 0%nat 0%nat * / a 0%nat 0%nat) * c 1%nat 0%nat * / a 1%nat 0%nat) in cross by lca.
        rewrite Cinv_r in cross. 2: assumption. 
        rewrite Cmult_1_l in cross.
        replace (/ a 1%nat 0%nat * / a 0%nat 0%nat *
        (a 1%nat 0%nat * c 0%nat 0%nat)) with ((a 1%nat 0%nat * / a 1%nat 0%nat) * c 0%nat 0%nat * / a 0%nat 0%nat) in cross by lca.
        rewrite Cinv_r in cross. 2: assumption. 
        rewrite Cmult_1_l in cross.
        rewrite cross. reflexivity. 
    }
    rewrite H.
    rewrite <- Mscale_access.
    rewrite <- Cmult_assoc. 
    rewrite Cinv_l. 2: assumption.
    apply Cmult_1_r.
}
Qed.

Lemma unitary_n0_tensor_yields_n0_components: forall (U: Square 4) (a: Vector 4) (b c: Vector 2), 
WF_Unitary U -> WF_Matrix a -> WF_Matrix b -> WF_Matrix c -> 
U × a = b ⊗ c -> a <> Zero -> b <> Zero /\ c <> Zero.
Proof.
intros U a b c U_unitary WF_a WF_b WF_c tens an0.
rewrite <- inner_product_zero_iff_zero in an0. 2: assumption.
rewrite unitary_preserves_inner_prod with (U := U) in an0. 2,3: assumption.
rewrite tens in an0.
assert (kip_help: ⟨ b ⊗ c, b ⊗ c ⟩ = ⟨ b, b ⟩ * ⟨ c, c ⟩). apply kron_inner_prod.
rewrite kip_help in an0 at 1.
split.
{
    unfold not.
    intro. 
    apply an0.
    rewrite <- inner_product_zero_iff_zero in H. 2: assumption.
    rewrite H.
    apply Cmult_0_l.
}
{
    unfold not.
    intro. 
    apply an0.
    rewrite <- inner_product_zero_iff_zero in H. 2: assumption.
    rewrite H.
    apply Cmult_0_r.
}
Qed.

Lemma inner_prod_is_norm_squared {n}: forall (a: Vector n), 
norm a * norm a = ⟨ a, a ⟩.
Proof.
intros.
unfold norm, RtoC.
unfold Cmult.
apply c_proj_eq.
simpl.
rewrite Rmult_0_l.
rewrite Rminus_0_r.
apply sqrt_sqrt.
apply inner_product_ge_0.
simpl.
rewrite Rmult_0_l. rewrite Rmult_0_r.
rewrite Rplus_0_l.
symmetry.
apply norm_real.
Qed.

Lemma lin_indep_scale_invariant {n}: forall (a b : C) (u v: Vector n), 
a <> 0 -> b <> 0 -> (linearly_independent_2vec u v <-> linearly_independent_2vec (a .* u) (b .* v)).
Proof.
intros a b u v an0 bn0.
split.
{
    intro linindep.
    unfold linearly_independent_2vec in *.
    intros c1 c2 zero.
    repeat rewrite Mscale_assoc in zero.
    apply linindep in zero.
    destruct zero as [aprod bprod].
    rewrite Cmult_comm in aprod, bprod.
    apply Cmult_0_cancel_l in aprod, bprod.
    split. all: assumption.
}
{
    intro linindep.
    unfold linearly_independent_2vec in *.
    intros c1 c2 zero.
    specialize (linindep (c1 * /a) (c2 * /b)).
    repeat rewrite Mscale_assoc in linindep.
    repeat rewrite <- Cmult_assoc in linindep.
    rewrite Cinv_l in linindep.
    rewrite Cinv_l in linindep. 2,3: assumption.
    repeat rewrite Cmult_1_r in linindep.
    apply linindep in zero.
    destruct zero as [aprod bprod].
    rewrite Cmult_comm in aprod, bprod.
    apply Cmult_0_cancel_l in aprod, bprod.
    split. 1,2: assumption.
    all: apply nonzero_div_nonzero.
    all: assumption.
}
Qed.
