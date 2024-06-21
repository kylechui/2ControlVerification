Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.
Require Import QuantumLib.Eigenvectors.
Require Import WFHelpers.
Require Import AlgebraHelpers.

Lemma Mplus_cancel_l : forall {m n} (A B C : Matrix m n),
  A .+ B = A .+ C -> B = C.
Proof.
  intros.
  prep_matrix_equality.
  apply (f_equal (fun f => f x y)) in H.
  apply Cplus_cancel_l with (a := A x y).
  unfold Mplus in H.
  assumption.
Qed.

Lemma Mplus_cancel_r : forall {m n} (A B C : Matrix m n),
  A .+ C = B .+ C -> A = B.
Proof.
  intros.
  prep_matrix_equality.
  apply (f_equal (fun f => f x y)) in H.
  apply Cplus_cancel_r with (c := C x y).
  unfold Mplus in H.
  assumption.
Qed.

Lemma kron_direct_sum_distr_r : forall {m n o p} (A B : Matrix m n) (C : Matrix o p),
  WF_Matrix A -> WF_Matrix B -> WF_Matrix C -> (A .⊕ B) ⊗ C = (A ⊗ C) .⊕ (B ⊗ C).
Proof.
  intros.
  repeat rewrite (direct_sum_decomp _ _ 0 0).
  rewrite (kron_plus_distr_r (2 * m) (2 * n) o p (∣0⟩⟨0∣ ⊗ A) (∣1⟩⟨1∣ ⊗ B) C) at 1.
  repeat rewrite <- kron_assoc.
  all: solve_WF_matrix.
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
  intros.
  show_wf.
Qed.

Lemma WF_diag4: forall (c1 c2 c3 c4 : C), WF_Matrix (diag4 c1 c2 c3 c4).
Proof.
  intros.
  show_wf.
Qed.

#[export] Hint Resolve WF_diag2 WF_diag4 : wf_db.

Lemma diag2_decomp : forall (c1 c2 : C), diag2 c1 c2 = c1 .* ∣0⟩⟨0∣ .+ c2 .* ∣1⟩⟨1∣.
Proof.
  intros.
  solve_matrix.
Qed.

Lemma Det_diag2 : forall (c1 c2 : C), Determinant (diag2 c1 c2) = c1 * c2.
Proof.
  intros.
  unfold diag2, Determinant, big_sum, parity, get_minor; lca.
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
      rewrite Nat.Div0.add_mod with (n := o) by lia.
      rewrite Nat.Div0.add_mod with (n := p) by lia.
      repeat rewrite Nat.Div0.mod_mul by lia.
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
      rewrite Nat.Div0.add_mod with (n := o) by lia.
      rewrite Nat.Div0.add_mod with (n := p) by lia.
      repeat rewrite Nat.Div0.mod_mul by lia.
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
           rewrite Nat.Div0.add_mod with (n := o) by lia.
           rewrite Nat.Div0.add_mod with (n := p) by lia.
           repeat rewrite Nat.Div0.mod_mul by lia.
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

Lemma isolate_inner_mult {a b c d e}: forall (A: Matrix a b) (B: Matrix b c) (C: Matrix c d) (D: Matrix d e),
(A × B) × (C × D) = A × (B × C) × D.
Proof.
intros.
repeat rewrite <- Mmult_assoc.
reflexivity.
Qed.

Lemma block_multiply {n}: forall (U V: Square (2*n)%nat) (P00 P01 P10 P11 Q00 Q01 Q10 Q11: Square n),
  WF_Matrix P00 -> WF_Matrix P01 -> WF_Matrix P10 -> WF_Matrix P11 ->
  WF_Matrix Q00 -> WF_Matrix Q01 -> WF_Matrix Q10 -> WF_Matrix Q11 ->
  U = ∣0⟩⟨0∣ ⊗ P00 .+ ∣0⟩⟨1∣ ⊗ P01 .+ ∣1⟩⟨0∣ ⊗ P10 .+ ∣1⟩⟨1∣ ⊗ P11 ->
  V = ∣0⟩⟨0∣ ⊗ Q00 .+ ∣0⟩⟨1∣ ⊗ Q01 .+ ∣1⟩⟨0∣ ⊗ Q10 .+ ∣1⟩⟨1∣ ⊗ Q11 ->
  U × V = ∣0⟩⟨0∣ ⊗ (P00 × Q00 .+ P01 × Q10) .+ ∣0⟩⟨1∣ ⊗ (P00 × Q01 .+ P01×Q11) .+ ∣1⟩⟨0∣ ⊗ (P10×Q00 .+ P11 × Q10) .+ ∣1⟩⟨1∣ ⊗ (P10 × Q01 .+ P11 × Q11).
Proof.
  intros.
  rewrite H7, H8; clear H7 H8.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite Mmult_plus_distr_r.
  repeat rewrite kron_mixed_product.
  repeat rewrite cancel00.
  repeat rewrite cancel01.
  repeat rewrite cancel10.
  repeat rewrite cancel11.
  Msimpl_light.
  lma'.
  all: solve_WF_matrix.
Qed.

Lemma Mplus_access {m n}: forall (A B : Matrix m n) (i j : nat),
(A .+ B) i j = (A i j) + (B i j).
Proof.
  intros.
  lca.
Qed.

Lemma block_equalities {n}: forall (P00 P01 P10 P11 Q00 Q01 Q10 Q11: Square n),
  WF_Matrix P00 -> WF_Matrix P01 -> WF_Matrix P10 -> WF_Matrix P11 ->
  WF_Matrix Q00 -> WF_Matrix Q01 -> WF_Matrix Q10 -> WF_Matrix Q11 ->
  ∣0⟩⟨0∣ ⊗ P00 .+ ∣0⟩⟨1∣ ⊗ P01 .+ ∣1⟩⟨0∣ ⊗ P10 .+ ∣1⟩⟨1∣ ⊗ P11 = ∣0⟩⟨0∣ ⊗ Q00 .+ ∣0⟩⟨1∣ ⊗ Q01 .+ ∣1⟩⟨0∣ ⊗ Q10 .+ ∣1⟩⟨1∣ ⊗ Q11 ->
  P00 = Q00 /\ P01 = Q01 /\ P10 = Q10 /\ P11 = Q11.
Proof.
  intros P00 P01 P10 P11 Q00 Q01 Q10 Q11 WF_P00 WF_P01 WF_P10 WF_P11 WF_Q00 WF_Q01 WF_Q10 WF_Q11 H.
  bdestruct (n =? 0).
  {
    split.
    {
      prep_matrix_equality.
      rewrite WF_P00, WF_Q00.
      reflexivity.
      left; lia.
      left; lia.
    }
    split.
    {
      prep_matrix_equality.
      rewrite WF_P01, WF_Q01.
      reflexivity.
      left; lia.
      left; lia.
    }
    split.
    {
      prep_matrix_equality.
      rewrite WF_P10, WF_Q10.
      reflexivity.
      left; lia.
      left; lia.
    }
    {
      prep_matrix_equality.
      rewrite WF_P11, WF_Q11.
      reflexivity.
      left; lia.
      left; lia.
    }
  }
  {
    split.
    {
      prep_matrix_equality.
      apply (f_equal (fun f => f x y)) in H.
      unfold kron, Mplus in H; simpl in H.
      bdestruct (x <? n).
      {
        bdestruct (y <? n).
        {
          do 2 rewrite Nat.div_small, Nat.mod_small in H.
          unfold qubit0, qubit1, adjoint, Mmult in H; simpl in H.
          revert H.
          Csimpl.
          all: auto.
        }
        {
          rewrite WF_P00, WF_Q00.
          reflexivity.
          right; assumption.
          right; assumption.
        }
      }
      {
        rewrite WF_P00, WF_Q00.
        reflexivity.
        left; assumption.
        left; assumption.
      }
    }
    split.
    {
      prep_matrix_equality.
      apply (f_equal (fun f => f x (1 * n + y)%nat)) in H.
      unfold kron, Mplus in H; simpl in H.
      bdestruct (x <? n).
      {
        bdestruct (y <? n).
        {
          replace (n + 0)%nat with (1 * n)%nat in H by lia.
          rewrite Nat.div_add_l in H.
          rewrite Nat.add_comm with (m := y) in H.
          rewrite Nat.Div0.mod_add in H.
          do 2 rewrite Nat.div_small, Nat.mod_small in H.
          unfold qubit0, qubit1, adjoint, Mmult in H; simpl in H.
          revert H.
          Csimpl.
          all: auto.
        }
        {
          rewrite WF_P01, WF_Q01.
          reflexivity.
          right; assumption.
          right; assumption.
        }
      }
      {
        rewrite WF_P01, WF_Q01.
        reflexivity.
        left; assumption.
        left; assumption.
      }
    }
    split.
    {
      prep_matrix_equality.
      apply (f_equal (fun f => f (1 * n + x)%nat y)) in H.
      unfold kron, Mplus in H; simpl in H.
      bdestruct (x <? n).
      {
        bdestruct (y <? n).
        {
          replace (n + 0)%nat with (1 * n)%nat in H by lia.
          rewrite Nat.div_add_l in H.
          rewrite Nat.add_comm with (m := x) in H.
          rewrite Nat.Div0.mod_add in H.
          do 2 rewrite Nat.div_small, Nat.mod_small in H.
          unfold qubit0, qubit1, adjoint, Mmult in H; simpl in H.
          revert H.
          Csimpl.
          all: auto.
        }
        {
          rewrite WF_P10, WF_Q10.
          reflexivity.
          right; assumption.
          right; assumption.
        }
      }
      {
        rewrite WF_P10, WF_Q10.
        reflexivity.
        left; assumption.
        left; assumption.
      }
    }
    {
      prep_matrix_equality.
      apply (f_equal (fun f => f (1 * n + x) (1 * n + y))%nat) in H.
      unfold kron, Mplus in H; simpl in H.
      bdestruct (x <? n).
      {
        bdestruct (y <? n).
        {
          replace (n + 0)%nat with (1 * n)%nat in H by lia.
          do 2 rewrite Nat.div_add_l in H.
          rewrite Nat.add_comm with (m := x) in H.
          rewrite Nat.add_comm with (m := y) in H.
          do 2 rewrite Nat.Div0.mod_add in H.
          do 2 rewrite Nat.div_small, Nat.mod_small in H.
          unfold qubit0, qubit1, adjoint, Mmult in H; simpl in H.
          revert H.
          Csimpl.
          all: auto.
        }
        {
          rewrite WF_P11, WF_Q11.
          reflexivity.
          right; assumption.
          right; assumption.
        }
      }
      {
        rewrite WF_P11, WF_Q11.
        reflexivity.
        left; assumption.
        left; assumption.
      }
    }
  }
Qed.

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

Lemma Mscale_neq_zero {m n}: forall (c: C) (A : Matrix m n),
c <> 0 -> A <> Zero -> c .* A <> Zero.
Proof.
  intros.
  rewrite nonzero_def in *.
  destruct H0. destruct H0.
  exists x, x0.
  rewrite <- Mscale_access.
  apply Cmult_nonzero.
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
Proof.
  intros.
  lma'.
  apply WF_plus; auto.
  unfold Mopp.
  apply WF_scale.
  assumption.
Qed.

Lemma Mplus_opp_0_l {m n}: forall (A: Matrix m n),
  WF_Matrix A -> Mopp (A) .+ A = Zero.
Proof.
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
 apply mat_equiv_eq; auto; apply WF_Zero.
 right.
 assert (v1 <> Zero).
 {
  intro.
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
    rewrite Mplus_opp_0_r in comb_zero. 2: apply WF_scale; auto.
    rewrite Mplus_0_r in comb_zero.
    unfold Mopp in comb_zero.
    rewrite Mscale_assoc in comb_zero.
    apply (f_equal (fun f => (/ (- C1 * c2)) .* f)) in comb_zero.
    do 2 rewrite Mscale_assoc in comb_zero.
    rewrite Cinv_l in comb_zero.
    rewrite Mscale_1_l in comb_zero.
    exists (/ (- C1 * c2) * c1).
    assumption.
    apply Cmult_nonzero. 2: assumption.
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
    rewrite Mplus_opp_0_r in comb_zero. 2: apply WF_scale; auto.
    rewrite Mplus_0_r in comb_zero.
    unfold Mopp in comb_zero.
    rewrite Mscale_assoc in comb_zero.
    apply (f_equal (fun f => (/ (- C1 * c2)) .* f)) in comb_zero.
    do 2 rewrite Mscale_assoc in comb_zero.
    rewrite Cinv_l in comb_zero.
    rewrite Mscale_1_l in comb_zero.
    exists (/ (- C1 * c2) * c1).
    assumption.
    apply Cmult_nonzero. 2: assumption.
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

Lemma block_decomp {n}: forall (U: Square (2*n)), WF_Matrix U ->
  exists (TL TR BL BR : Square n),
  WF_Matrix TL /\ WF_Matrix TR /\ WF_Matrix BL /\ WF_Matrix BR /\
  U = ∣0⟩⟨0∣ ⊗ TL .+ ∣0⟩⟨1∣ ⊗ TR .+ ∣1⟩⟨0∣ ⊗ BL .+ ∣1⟩⟨1∣ ⊗ BR.
Proof.
  intros U WF_U.
  bdestruct (n =? 0).
  {
    exists Zero, Zero, Zero, Zero.
    split. apply WF_Zero.
    split. apply WF_Zero.
    split. apply WF_Zero.
    split. apply WF_Zero.
    repeat rewrite kron_0_r.
    repeat rewrite Mplus_0_r.
    prep_matrix_equality.
    unfold Zero; simpl.
    rewrite WF_U.
    reflexivity.
    left.
    rewrite H; lia.
  }
  {
    set (TL := (fun x y => if (x <? n) && (y <? n) then U x y else C0 ) : Square n).
    set (TR := (fun x y => if (x <? n) && (y <? n) then U x (n + y)%nat else C0 ) : Square n).
    set (BL := (fun x y => if (x <? n) && (y <? n) then U (n + x)%nat y else C0 ) : Square n).
    set (BR := (fun x y => if (x <? n) && (y <? n) then U (n + x)%nat (n + y)%nat else C0 ) : Square n).
    assert (WF_TL : WF_Matrix TL).
    {
      unfold WF_Matrix, TL.
      intros.
      destruct H0.
      {
        rewrite <- (Nat.ltb_ge x n) in H0.
        rewrite H0, andb_false_l.
        reflexivity.
      }
      {
        rewrite <- (Nat.ltb_ge y n) in H0.
        rewrite H0, andb_false_r.
        reflexivity.
      }
    }
    assert (WF_TR : WF_Matrix TR).
    {
      unfold WF_Matrix, TR.
      intros.
      destruct H0.
      {
        rewrite <- (Nat.ltb_ge x n) in H0.
        rewrite H0, andb_false_l.
        reflexivity.
      }
      {
        rewrite <- (Nat.ltb_ge y n) in H0.
        rewrite H0, andb_false_r.
        reflexivity.
      }
    }
    assert (WF_BL : WF_Matrix BL).
    {
      unfold WF_Matrix, BL.
      intros.
      destruct H0.
      {
        rewrite <- (Nat.ltb_ge x n) in H0.
        rewrite H0, andb_false_l.
        reflexivity.
      }
      {
        rewrite <- (Nat.ltb_ge y n) in H0.
        rewrite H0, andb_false_r.
        reflexivity.
      }
    }
    assert (WF_BR : WF_Matrix BR).
    {
      unfold WF_Matrix, BR.
      intros.
      destruct H0.
      {
        rewrite <- (Nat.ltb_ge x n) in H0.
        rewrite H0, andb_false_l.
        reflexivity.
      }
      {
        rewrite <- (Nat.ltb_ge y n) in H0.
        rewrite H0, andb_false_r.
        reflexivity.
      }
    }
    assert (REMOVE_ME : forall (z : nat), (z >= n * 2 -> z / n >= 2)%nat).
    {
      intros.
      rewrite <- Nat.div_mul with (a := 2%nat) (b := n).
      apply Nat.Div0.div_le_mono.
      lia.
      assumption.
    }
    exists TL, TR, BL, BR.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    prep_matrix_equality.
    specialize (WF_U x y).
    unfold TL, TR, BL, BR, kron, Mplus; simpl.
    replace (x mod n <? n) with true by (symmetry; apply Nat.ltb_lt, Nat.mod_upper_bound; assumption).
    replace (y mod n <? n) with true by (symmetry; apply Nat.ltb_lt, Nat.mod_upper_bound; assumption).
    simpl.
    bdestruct (x <? n).
    {
      rewrite Nat.div_small, Nat.mod_small; auto.
      bdestruct (y <? n); auto.
      {
        rewrite Nat.div_small, Nat.mod_small.
        unfold qubit0, qubit1, adjoint, Mmult; simpl.
        lca.
        all: assumption.
      }
      {
        bdestruct (y <? n * 2); auto.
        {
          apply Nat.Div0.div_le_mono with (c := n) in H1.
          rewrite Nat.div_same in H1.
          apply Nat.Div0.div_lt_upper_bound in H2.
          assert (y / n = 1)%nat by lia; clear H1 H2.
          rewrite H3.
          unfold qubit0, qubit1, adjoint, Mmult; simpl.
          Csimpl.
          rewrite <- Nat.mul_1_r with (n := n) at 1.
          rewrite <- H3, <- Nat.div_mod.
          reflexivity.
          all: assumption.
        }
        {
          pose proof (Nat.Div0.div_le_mono (n * 2) y n H2).
          rewrite Nat.mul_comm, Nat.div_mul in H3; auto.
          destruct (y / n)%nat. lia.
          destruct n0. lia.
          rewrite WF_U.
          unfold qubit0, qubit1, adjoint, Mmult; simpl.
          lca.
          right; lia.
        }
      }
    }
    {
      bdestruct (x <? n * 2).
      {
        apply Nat.Div0.div_le_mono with (c := n) in H0.
        rewrite Nat.div_same in H0; auto.
        apply Nat.Div0.div_lt_upper_bound in H1.
        assert (x / n = 1)%nat by lia; clear H0 H1.
        rewrite H2.
        bdestruct (y <? n); auto.
        {
          rewrite Nat.mod_small with (a := y), Nat.div_small with (a := y).
          unfold qubit0, qubit1, adjoint, Mmult; simpl.
          Csimpl.
          rewrite <- Nat.mul_1_r with (n := n) at 1.
          rewrite <- H2, <- Nat.div_mod.
          reflexivity.
          all: assumption.
        }
        {
          bdestruct (y <? n * 2).
          {
            apply Nat.Div0.div_le_mono with (c := n) in H0.
            rewrite Nat.div_same in H0.
            apply Nat.Div0.div_lt_upper_bound in H1.
            assert (y / n = 1)%nat by lia; clear H0 H1.
            rewrite H3.
            unfold qubit0, qubit1, adjoint, Mmult; simpl.
            Csimpl.
            rewrite <- Nat.mul_1_r with (n := n) at 1 3.
            rewrite <- H2 at 1.
            rewrite <- H3 at 1.
            rewrite <- Nat.div_mod.
            rewrite <- Nat.div_mod.
            reflexivity.
            all: assumption.
          }
          {
            pose proof (Nat.Div0.div_le_mono (n * 2) y n H1).
            rewrite Nat.mul_comm, Nat.div_mul in H3; auto.
            destruct (y / n)%nat. lia.
            destruct n0. lia.
            rewrite WF_U.
            unfold qubit0, qubit1, adjoint, Mmult; simpl.
            lca.
            right; lia.
          }
        }
      }
      {
        pose proof (Nat.Div0.div_le_mono (n * 2) x n H1).
        rewrite Nat.mul_comm, Nat.div_mul in H2; auto.
        destruct (x / n)%nat. lia.
        destruct n0. lia.
        rewrite WF_U.
        unfold qubit0, qubit1, adjoint, Mmult; simpl.
        lca.
        left; lia.
      }
    }
  }
Qed.

Lemma element_equiv_vec_element {m n}: forall (A: Matrix m n),
WF_Matrix A ->
forall (i j: nat),
A i j = (get_col A j) i 0%nat.
Proof.
intros.
unfold get_col.
simpl.
reflexivity.
Qed.

Lemma column_equal_implies_equal {m n}: forall (A B: Matrix m n),
WF_Matrix A -> WF_Matrix B ->
(forall (j: nat), get_col A j = get_col B j) -> A = B.
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
unfold get_col.
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
apply adjoint_unitary in b_unitary.
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
  unfold Mopp.
  rewrite Mscale_kron_dist_l.
  reflexivity.
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
Qed.

Lemma id4_diag4: I 4 = diag4 C1 C1 C1 C1.
Proof.
  lma'.
Qed.

Lemma diag2_eigenpairs: forall (c1 c2 : C),
  Eigenpair (diag2 c1 c2) (∣0⟩, c1) /\ Eigenpair (diag2 c1 c2) (∣1⟩, c2).
Proof.
  intros.
  split; unfold Eigenpair; simpl.
  {
    lma'.
    unfold Mmult, scale, diag2, qubit0; simpl.
    lca.
  }
  {
    lma'.
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
    unfold Mmult, scale, kron, diag4, qubit0; simpl.
    lca.
  }
  split.
  {
    lma'.
    unfold Mmult, scale, kron, diag4, qubit1; simpl.
    lca.
  }
  split.
  {
    lma'.
    unfold Mmult, scale, kron, diag4, qubit0; simpl.
    lca.
  }
  {
    lma'.
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
rewrite inner_product_adjoint_l.
rewrite <- Mmult_assoc.
rewrite u_inv, Mmult_1_l.
reflexivity.
assumption.
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

Lemma Madj_explicit_decomp {m n}: forall (i j : nat) (A : Matrix m n),
A† i j = (A j i)^*.
Proof.
intros.
lca.
Qed.

Lemma kron_uniq2: forall (a b c d : Vector 2),
  WF_Matrix a -> WF_Matrix b -> WF_Matrix c -> WF_Matrix d ->
  a <> Zero -> b <> Zero -> c <> Zero -> d <> Zero ->
  a ⊗ b = c ⊗ d -> exists (c1 c2: C), c1 .* a = c /\ c2 .* b = d.
Proof.
  assert (nonzero_def2 : forall (v : Vector 2), WF_Matrix v -> v <> Zero ->
    v 0%nat 0%nat <> C0 \/ v 1%nat 0%nat <> C0).
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
    assert (a1c1_nonzero : a1 * c1 <> C0) by (apply Cmult_nonzero; assumption).
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
    assert (a0c0_nonzero : a0 * c0 <> C0) by (apply Cmult_nonzero; assumption).
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
      assert (b1d1_nonzero : b1 * d1 <> C0) by (apply Cmult_nonzero; assumption).
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
          assert (b0d0_nonzero : b0 * d0 <> C0) by (apply Cmult_nonzero; assumption).
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

Lemma vector2_inner_prod_decomp: forall (a b : Vector 2),
(⟨ a, b ⟩ = (a 0%nat 0%nat)^* * (b 0%nat 0%nat) + (a 1%nat 0%nat)^* * (b 1%nat 0%nat)).
Proof.
intros.
lca.
Qed.

Lemma Mmult_square2_explicit: forall (A B: Square 2),
WF_Matrix A -> WF_Matrix B ->
(A × B) = (fun x y => A x 0%nat * B 0%nat y + A x 1%nat * B 1%nat y).
Proof.
intros. lma'.
unfold WF_Matrix.
intros.
destruct H1.
repeat rewrite H. lca. 1,2: lia.
repeat rewrite H0. lca. 1,2: lia.
Qed.

Lemma Mv_prod_21_explicit: forall (A: Square 2) (v : Vector 2),
WF_Matrix A -> WF_Matrix v ->
(A × v) = ((fun x y =>
match (x,y) with
| (0,0) => (A 0 0)%nat * (v 0 0)%nat + (A 0 1)%nat * (v 1 0)%nat
| (1,0) => (A 1 0)%nat * (v 0 0)%nat + (A 1 1)%nat * (v 1 0)%nat
| _ => C0
end): Square 2).
Proof.
intros.
lma'.
unfold WF_Matrix.
intros.
destruct H1.
destruct x as [|a]. contradict H. lia.
destruct a as [|x]. contradict H. lia. reflexivity.
destruct x as [|a]. destruct y as [|b]. contradict H. lia.
reflexivity.
destruct a as [|x]. destruct y as [|b]. contradict H. lia. reflexivity. reflexivity.
Qed.

Lemma id_tens_equiv_block_diag {n}: forall (A : Square n),
I 2 ⊗ A = ∣0⟩⟨0∣ ⊗ A .+ ∣1⟩⟨1∣ ⊗ A.
Proof.
intros.
assert (I 2 = ∣0⟩⟨0∣ .+ ∣1⟩⟨1∣). lma'.
rewrite H.
apply kron_plus_distr_r.
Qed.

Lemma control_direct_sum : forall {n} (A : Square n), control A = I n .⊕ A.
Proof.
  intros.
  prep_matrix_equality.
  unfold control, direct_sum, I.
  destruct (x <? n) eqn:L1.
  {
    rewrite Nat.ltb_lt, <- Nat.leb_gt in L1.
    rewrite L1.
    destruct (y =? x) eqn:L2.
    {
      rewrite Nat.eqb_eq in L2.
      symmetry in L2.
      apply Nat.eqb_eq in L2.
      rewrite L2.
      lca.
    }
    {
      assert (H : x =? y = false).
      {
        rewrite Nat.eqb_neq.
        rewrite Nat.eqb_neq in L2.
        intro.
        contradict L2.
        rewrite H; reflexivity.
      }
      rewrite H.
      lca.
    }
  }
  {
    rewrite Nat.ltb_ge, <- Nat.leb_le in L1.
    rewrite L1.
    destruct (y <? n) eqn:L2.
    {
      rewrite Nat.ltb_lt, <- Nat.leb_gt in L2.
      rewrite L2.
      assert (H : x <> y).
      {
        rewrite Nat.leb_le in L1.
        rewrite Nat.leb_gt in L2.
        lia.
      }
      rewrite <- Nat.eqb_neq in H.
      rewrite H.
      lca.
    }
    {
      rewrite Nat.ltb_ge, <- Nat.leb_le in L2.
      rewrite L2.
      lca.
    }
  }
Qed.

Lemma control_decomp : forall {n} (A : Square n),
  WF_Matrix A -> control A = ∣0⟩⟨0∣ ⊗ I n .+ ∣1⟩⟨1∣ ⊗ A.
Proof.
  intros.
  rewrite control_direct_sum, (@direct_sum_decomp _ _ 0 0).
  all: solve_WF_matrix.
Qed.

Lemma direct_sum_simplify : forall {n} (A B C D : Square n),
  WF_Matrix A -> WF_Matrix B -> WF_Matrix C -> WF_Matrix D ->
    A .⊕ B = C .⊕ D <-> A = C /\ B = D.
Proof.
  intros.
  split.
  {
    split.
    {
      lma'; try assumption.
      apply (f_equal (fun f => f i j)) in H3.
      unfold direct_sum in H3.
      destruct (i <? n) eqn:L1.
      {
        assumption.
      }
      {
        destruct (j <? n) eqn:L2.
        {
          assumption.
        }
        {
          rewrite Nat.ltb_ge in L1, L2.
          unfold WF_Matrix in H, H1.
          specialize (H i j).
          specialize (H1 i j).
          rewrite H, H1; auto.
        }
      }
    }
    {
      lma'; try assumption.
      apply (f_equal (fun f => f (i + n) (j + n))%nat) in H3.
      unfold direct_sum in H3.
      destruct (i <? n) eqn:L1.
      {
        assert (H4 : i + n <? n = false).
        {
          rewrite Nat.ltb_ge.
          lia.
        }
        rewrite H4 in H3.
        destruct (j <? n) eqn:L2.
        {
          assert (H5 : j + n <? n = false).
          {
            rewrite Nat.ltb_ge.
            lia.
          }
          rewrite H5 in H3.
          simpl in H3.
          repeat rewrite Nat.add_sub in H3.
          exact H3.
        }
        {
          rewrite Nat.ltb_ge in L2.
          unfold WF_Matrix in H0, H2.
          specialize (H0 i j).
          specialize (H2 i j).
          rewrite H0, H2; auto.
        }
      }
      {
        rewrite Nat.ltb_ge in L1.
        unfold WF_Matrix in H0, H2.
        specialize (H0 i j).
        specialize (H2 i j).
        rewrite H0, H2; auto.
      }
    }
  }
  {
    intros [H3 H4].
    rewrite H3, H4; reflexivity.
  }
Qed.

Lemma cnot_cnot : cnot × cnot = I 4.
Proof.
  lma'.
Qed.

Lemma notc_notc : notc × notc = I 4.
Proof.
  lma'.
Qed.

Lemma control_mult : forall (A B : Square 2), WF_Matrix A -> WF_Matrix B ->
  control A × control B = control (A × B).
Proof.
  intros A B WF_A WF_B.
  repeat rewrite control_decomp.
  rewrite Mmult_plus_distr_l.
  do 2 rewrite Mmult_plus_distr_r.
  repeat rewrite kron_mixed_product.
  rewrite cancel00, cancel01, cancel10, cancel11.
  Msimpl_light.
  all: solve_WF_matrix.
Qed.
