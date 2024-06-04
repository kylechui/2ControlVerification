Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.
Require Import WFHelpers.
Require Import MatrixHelpers.

Definition swapab : Square 8 := swap ⊗ I 2.
Definition swapbc : Square 8 := I 2 ⊗ swap.
Definition swapac : Square 8 := swapab × swapbc × swapab.

#[global] Hint Unfold swapab swapbc swapac : M_db.

Lemma WF_swapab : WF_Matrix swapab.
Proof.
  solve_WF_matrix.
Qed.

Lemma WF_swapbc : WF_Matrix swapbc.
Proof.
  solve_WF_matrix.
Qed.

Lemma WF_swapac : WF_Matrix swapac.
Proof.
  solve_WF_matrix.
Qed.

#[export] Hint Resolve WF_swapab WF_swapbc WF_swapac : wf_db.

Lemma swapab_unitary : WF_Unitary swapab.
Proof.
  solve_WF_matrix.
Qed.

Lemma swapbc_unitary : WF_Unitary swapbc.
Proof.
  solve_WF_matrix.
Qed.

Lemma swapac_unitary : WF_Unitary swapac.
Proof.
  solve_WF_matrix.
Qed.

#[export] Hint Resolve swapab_unitary swapbc_unitary swapac_unitary : unit_db.

Lemma swapab_inverse : swapab × swapab = I 8.
Proof.
  unfold swapab.
  rewrite (@kron_mixed_product 4 4 4 2 2 2).
  rewrite swap_swap at 1.
  rewrite Mmult_1_l, id_kron.
  reflexivity.
  apply WF_I.
Qed.

Lemma swapbc_inverse : swapbc × swapbc = I 8.
Proof.
  unfold swapbc.
  rewrite (@kron_mixed_product 2 2 2 4 4 4).
  rewrite swap_swap at 1.
  rewrite Mmult_1_l, id_kron.
  reflexivity.
  apply WF_I.
Qed.

Lemma swapac_inverse : swapac × swapac = I 8.
Proof.
  unfold swapac.
  repeat rewrite Mmult_assoc.
  rewrite <- Mmult_assoc with (A := swapab) (B := swapab).
  rewrite swapab_inverse, Mmult_1_l.
  rewrite <- Mmult_assoc with (A := swapbc).
  rewrite swapbc_inverse, Mmult_1_l.
  exact swapab_inverse.
  all: solve_WF_matrix.
Qed.

Lemma swapab_hermitian : swapab† = swapab.
Proof.
  unfold swapab.
  rewrite (@kron_adjoint 4 4 2 2).
  rewrite swap_hermitian, id_adjoint_eq.
  reflexivity.
Qed.

Lemma swap_2q : forall (a b : Vector 2),
  WF_Matrix a -> WF_Matrix b ->
    swap × (a ⊗ b) = b ⊗ a.
Proof.
  intros.
  lma'.
Qed.

Lemma swap_2gate : forall (A B : Square 2),
  WF_Matrix A -> WF_Matrix B ->
    swap × (A ⊗ B) × swap = B ⊗ A.
Proof.
  intros.
  lma'.
Qed.

Lemma swapab_3q : forall (a b c : Vector 2),
WF_Matrix a -> WF_Matrix b -> WF_Matrix c ->
    swapab × (a ⊗ b ⊗ c) = (b ⊗ a ⊗ c).
Proof.
intros.
unfold swapab.
rewrite (@kron_mixed_product 4 4 1 2 2 1).
rewrite Mmult_1_l. 2: assumption.
rewrite swap_2q. 2,3: assumption.
reflexivity.
Qed.

Lemma swapab_3gate : forall (A B C : Square 2),
  WF_Matrix A -> WF_Matrix B -> WF_Matrix C ->
    swapab × (A ⊗ B ⊗ C) × swapab = (B ⊗ A ⊗ C).
Proof.
  intros.
  unfold swapab.
  do 2 rewrite (@kron_mixed_product 4 4 4 2 2 2).
  rewrite swap_2gate, Mmult_1_l, Mmult_1_r.
  all: solve_WF_matrix.
Qed.

Lemma swapbc_3q : forall (a b c : Vector 2),
WF_Matrix a -> WF_Matrix b -> WF_Matrix c ->
    swapbc × (a ⊗ b ⊗ c) = (a ⊗ c ⊗ b).
Proof.
  intros.
  unfold swapbc.
  repeat rewrite kron_assoc.
  rewrite (@kron_mixed_product 2 2 1 4 4 1).
  rewrite swap_2q, Mmult_1_l.
  all: solve_WF_matrix.
Qed.

Lemma swapbc_3gate : forall (A B C : Square 2),
  WF_Matrix A -> WF_Matrix B -> WF_Matrix C ->
    swapbc × (A ⊗ B ⊗ C) × swapbc = (A ⊗ C ⊗ B).
Proof.
  intros.
  unfold swapbc.
  rewrite kron_assoc. 2: assumption. 2: assumption. 2: assumption.
  rewrite Mmult_assoc.
  rewrite kron_mixed_product with (A := A) (B := B ⊗ C) (C := I 2) (D := swap) at 1.
  rewrite Mmult_1_r. 2: assumption.
  rewrite kron_mixed_product with (A := I 2) (B := swap) (C := A) (D := B ⊗ C × swap) at 1.
  rewrite Mmult_1_l. 2: assumption.
  rewrite <- Mmult_assoc.
  rewrite swap_2gate. 2: assumption. 2: assumption.
  rewrite <- kron_assoc. 2: assumption. 2: assumption. 2: assumption.
  reflexivity.
Qed.

Lemma swapac_3gate : forall (A B C : Square 2),
  WF_Matrix A -> WF_Matrix B -> WF_Matrix C ->
    swapac × (A ⊗ B ⊗ C) × swapac = (C ⊗ B ⊗ A).
Proof.
  intros.
  unfold swapac.
  repeat rewrite <- Mmult_assoc.
  rewrite Mmult_assoc. rewrite Mmult_assoc. rewrite Mmult_assoc. rewrite Mmult_assoc.
  rewrite <- Mmult_assoc with (A:=swapab) (B:= A ⊗ B ⊗ C) (C:= (swapab × (swapbc × swapab))).
  rewrite <- Mmult_assoc with (A := swapab) (B:= swapbc) (C:= swapab).
  rewrite <- Mmult_assoc with (A:= swapab × (A ⊗ B ⊗ C)) (B :=swapab × swapbc) (C:= swapab).
  rewrite <- Mmult_assoc with (A:= swapab × (A ⊗ B ⊗ C)) (B :=swapab) (C:= swapbc).
  rewrite swapab_3gate. 2: assumption. 2: assumption. 2: assumption.
  rewrite Mmult_assoc.
  rewrite <- Mmult_assoc with (A:=swapbc) (B:= B ⊗ A ⊗ C × swapbc) (C:= swapab).
  rewrite <- Mmult_assoc with (A:=swapab) (B:= swapbc × (B ⊗ A ⊗ C × swapbc)) (C:= swapab).
  rewrite <- Mmult_assoc with (A:= swapbc) (B:= B ⊗ A ⊗ C) (C:= swapbc).
  rewrite swapbc_3gate. 2: assumption. 2: assumption. 2: assumption.
  rewrite swapab_3gate. 2: assumption. 2: assumption. 2: assumption.
  reflexivity.
Qed.

Lemma swapbc_sa: swapbc = (swapbc) †.
Proof.
  unfold swapbc.
  rewrite (@kron_adjoint 2 2 4 4).
  rewrite id_adjoint_eq.
  rewrite swap_hermitian.
  reflexivity.
Qed.

Property swap_helper : forall (U : Square 4),
  WF_Matrix U ->
  swapbc × (U ⊗ I 2) × swapbc = swapab × (I 2 ⊗ U) × swapab.
Proof.
  intros U WF_U.
  pose proof (@block_decomp 2 U WF_U).
  unfold swapab, swapbc.
  destruct H as [TL [TR [BL [BR [WF_TL [WF_TR [WF_BL [WF_BR H]]]]]]]].
  rewrite H; clear H.
  repeat rewrite kron_plus_distr_l.
  repeat rewrite kron_plus_distr_r.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite Mmult_plus_distr_r.
  repeat rewrite kron_assoc.
  repeat rewrite (@kron_mixed_product 2 2 2 4 4 4).
  repeat rewrite <- kron_assoc.
  repeat rewrite (@kron_mixed_product 4 4 4 2 2 2).
  repeat rewrite swap_2gate.
  repeat rewrite Mmult_1_l.
  repeat rewrite Mmult_1_r.
  repeat rewrite (@kron_assoc 2 2 2 2).
  reflexivity.
  all: solve_WF_matrix.
Qed.
