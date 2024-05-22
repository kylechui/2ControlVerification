Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.
From Proof Require Import MatrixHelpers.
From Proof Require Import WFHelpers.

Definition swapab := swap ⊗ I 2.
Definition swapbc := I 2 ⊗ swap.
Definition swapac := swapab × swapbc × swapab.

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
  autounfold with M_db; auto with unit_db.
Qed.

Lemma swapbc_unitary : WF_Unitary swapbc.
Proof.
  autounfold with M_db; auto with unit_db.
Qed.

Lemma swapac_unitary : WF_Unitary swapac.
Proof.
  apply Mmult_unitary.
  apply Mmult_unitary.
  apply swapab_unitary.
  apply swapbc_unitary.
  apply swapab_unitary.
Qed.

#[export] Hint Resolve swapab_unitary swapbc_unitary swapac_unitary : unit_db.

Lemma swapab_inverse : swapab × swapab = I 8.
Proof.
  unfold swapab.
  rewrite kron_mixed_product, swap_swap.
  Msimpl_light.
  rewrite id_kron.
  replace (2 * 2 * 2)%nat with 8%nat by lia.
  reflexivity.
Qed.

Lemma swapbc_inverse : swapbc × swapbc = I 8.
Proof.
  unfold swapbc.
  rewrite kron_mixed_product, swap_swap.
  Msimpl_light.
  rewrite id_kron.
  replace (2 * (2 * 2))%nat with 8%nat by lia.
  reflexivity.
Qed.

Lemma swapac_inverse : swapac × swapac = I 8.
Proof.
  apply mat_equiv_eq.
  apply WF_mult. apply WF_swapac. apply WF_swapac.
  apply WF_I.
  unfold swapac.
  repeat rewrite Mmult_assoc.
  rewrite <- Mmult_assoc with (A := swapab) (B := swapab) (C:= swapbc × swapab).
  rewrite <- Mmult_assoc with (A := swapbc) (B := swapab × swapab) (C:= swapbc × swapab).
  rewrite swapab_inverse.
  rewrite Mmult_1_r. 2: apply WF_swapbc.
  rewrite <- Mmult_assoc with (A := swapbc) (B:= swapbc) (C:=swapab).
  rewrite <- Mmult_assoc with (A := swapab) (B:= swapbc × swapbc) (C:=swapab).
  rewrite swapbc_inverse.
  rewrite Mmult_1_r. 2: apply WF_swapab.
  rewrite <- swapab_inverse.
  apply mat_equiv_refl.
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
rewrite kron_mixed_product.
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
  rewrite kron_mixed_product.
  rewrite Mmult_1_l. 2: assumption.
  rewrite kron_mixed_product.
  rewrite Mmult_1_r. 2: assumption.
  rewrite swap_2gate. 2: assumption. 2: assumption.
  reflexivity.
Qed.

Lemma swapbc_3q : forall (a b c : Vector 2),
WF_Matrix a -> WF_Matrix b -> WF_Matrix c ->
    swapbc × (a ⊗ b ⊗ c) = (a ⊗ c ⊗ b).
Proof.
intros.
unfold swapbc.
rewrite kron_assoc. 2,3,4: assumption.
rewrite kron_mixed_product.
rewrite Mmult_1_l. 2: assumption.
rewrite swap_2q. 2,3: assumption.
rewrite kron_assoc. 2,3,4: assumption.
reflexivity.
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
  rewrite kron_adjoint.
  rewrite id_adjoint_eq.
  rewrite swap_hermitian.
  reflexivity.
Qed.

Lemma Mmult88_explicit_decomp: forall (A B: Square 8), 
WF_Matrix A -> WF_Matrix B -> 
A × B = ((fun x y => 
A x 0%nat * B 0%nat y + A x 1%nat * B 1%nat y
+ A x 2%nat * B 2%nat y + A x 3%nat * B 3%nat y
+ A x 4%nat * B 4%nat y + A x 5%nat * B 5%nat y
+ A x 6%nat * B 6%nat y + A x 7%nat * B 7%nat y) : Square 8).
Proof.
intros.
lma'.
unfold WF_Matrix.
intros.
destruct H1.
repeat rewrite H. lca. 1,2,3,4,5,6,7,8: lia.
repeat rewrite H0. lca. all: lia.
Qed.


Property swap_helper : forall (U : Square 4),
  WF_Matrix U -> 
  swapbc × (U ⊗ I 2) × swapbc = swapab × (I 2 ⊗ U) × swapab.
Proof.
intros U WF_U.
assert (bc00: swapbc 0%nat 0%nat = C1). lca.
assert (bc01: swapbc 0%nat 1%nat = C0). lca.
assert (bc02: swapbc 0%nat 2%nat = C0). lca.
assert (bc03: swapbc 0%nat 3%nat = C0). lca.
assert (bc04: swapbc 0%nat 4%nat = C0). lca.
assert (bc05: swapbc 0%nat 5%nat = C0). lca.
assert (bc06: swapbc 0%nat 6%nat = C0). lca.
assert (bc07: swapbc 0%nat 7%nat = C0). lca.
assert (bc10: swapbc 1%nat 0%nat = C0). lca.
assert (bc11: swapbc 1%nat 1%nat = C0). lca.
assert (bc12: swapbc 1%nat 2%nat = C1). lca.
assert (bc13: swapbc 1%nat 3%nat = C0). lca.
assert (bc14: swapbc 1%nat 4%nat = C0). lca.
assert (bc15: swapbc 1%nat 5%nat = C0). lca.
assert (bc16: swapbc 1%nat 6%nat = C0). lca.
assert (bc17: swapbc 1%nat 7%nat = C0). lca.
assert (bc20: swapbc 2%nat 0%nat = C0). lca.
assert (bc21: swapbc 2%nat 1%nat = C1). lca.
assert (bc22: swapbc 2%nat 2%nat = C0). lca.
assert (bc23: swapbc 2%nat 3%nat = C0). lca.
assert (bc24: swapbc 2%nat 4%nat = C0). lca.
assert (bc25: swapbc 2%nat 5%nat = C0). lca.
assert (bc26: swapbc 2%nat 6%nat = C0). lca.
assert (bc27: swapbc 2%nat 7%nat = C0). lca.
assert (bc30: swapbc 3%nat 0%nat = C0). lca.
assert (bc31: swapbc 3%nat 1%nat = C0). lca.
assert (bc32: swapbc 3%nat 2%nat = C0). lca.
assert (bc33: swapbc 3%nat 3%nat = C1). lca.
assert (bc34: swapbc 3%nat 4%nat = C0). lca.
assert (bc35: swapbc 3%nat 5%nat = C0). lca.
assert (bc36: swapbc 3%nat 6%nat = C0). lca.
assert (bc37: swapbc 3%nat 7%nat = C0). lca.
assert (bc40: swapbc 4%nat 0%nat = C0). lca.
assert (bc41: swapbc 4%nat 1%nat = C0). lca.
assert (bc42: swapbc 4%nat 2%nat = C0). lca.
assert (bc43: swapbc 4%nat 3%nat = C0). lca.
assert (bc44: swapbc 4%nat 4%nat = C1). lca.
assert (bc45: swapbc 4%nat 5%nat = C0). lca.
assert (bc46: swapbc 4%nat 6%nat = C0). lca.
assert (bc47: swapbc 4%nat 7%nat = C0). lca.
assert (bc50: swapbc 5%nat 0%nat = C0). lca.
assert (bc51: swapbc 5%nat 1%nat = C0). lca.
assert (bc52: swapbc 5%nat 2%nat = C0). lca.
assert (bc53: swapbc 5%nat 3%nat = C0). lca.
assert (bc54: swapbc 5%nat 4%nat = C0). lca.
assert (bc55: swapbc 5%nat 5%nat = C0). lca.
assert (bc56: swapbc 5%nat 6%nat = C1). lca.
assert (bc57: swapbc 5%nat 7%nat = C0). lca.
assert (bc60: swapbc 6%nat 0%nat = C0). lca.
assert (bc61: swapbc 6%nat 1%nat = C0). lca.
assert (bc62: swapbc 6%nat 2%nat = C0). lca.
assert (bc63: swapbc 6%nat 3%nat = C0). lca.
assert (bc64: swapbc 6%nat 4%nat = C0). lca.
assert (bc65: swapbc 6%nat 5%nat = C1). lca.
assert (bc66: swapbc 6%nat 6%nat = C0). lca.
assert (bc67: swapbc 6%nat 7%nat = C0). lca.
assert (bc70: swapbc 7%nat 0%nat = C0). lca.
assert (bc71: swapbc 7%nat 1%nat = C0). lca.
assert (bc72: swapbc 7%nat 2%nat = C0). lca.
assert (bc73: swapbc 7%nat 3%nat = C0). lca.
assert (bc74: swapbc 7%nat 4%nat = C0). lca.
assert (bc75: swapbc 7%nat 5%nat = C0). lca.
assert (bc76: swapbc 7%nat 6%nat = C0). lca.
assert (bc77: swapbc 7%nat 7%nat = C1). lca.
assert (ab00: swapab 0%nat 0%nat = C1). lca.
assert (ab01: swapab 0%nat 1%nat = C0). lca.
assert (ab02: swapab 0%nat 2%nat = C0). lca.
assert (ab03: swapab 0%nat 3%nat = C0). lca.
assert (ab04: swapab 0%nat 4%nat = C0). lca.
assert (ab05: swapab 0%nat 5%nat = C0). lca.
assert (ab06: swapab 0%nat 6%nat = C0). lca.
assert (ab07: swapab 0%nat 7%nat = C0). lca.
assert (ab10: swapab 1%nat 0%nat = C0). lca.
assert (ab11: swapab 1%nat 1%nat = C1). lca.
assert (ab12: swapab 1%nat 2%nat = C0). lca.
assert (ab13: swapab 1%nat 3%nat = C0). lca.
assert (ab14: swapab 1%nat 4%nat = C0). lca.
assert (ab15: swapab 1%nat 5%nat = C0). lca.
assert (ab16: swapab 1%nat 6%nat = C0). lca.
assert (ab17: swapab 1%nat 7%nat = C0). lca.
assert (ab20: swapab 2%nat 0%nat = C0). lca.
assert (ab21: swapab 2%nat 1%nat = C0). lca.
assert (ab22: swapab 2%nat 2%nat = C0). lca.
assert (ab23: swapab 2%nat 3%nat = C0). lca.
assert (ab24: swapab 2%nat 4%nat = C1). lca.
assert (ab25: swapab 2%nat 5%nat = C0). lca.
assert (ab26: swapab 2%nat 6%nat = C0). lca.
assert (ab27: swapab 2%nat 7%nat = C0). lca.
assert (ab30: swapab 3%nat 0%nat = C0). lca.
assert (ab31: swapab 3%nat 1%nat = C0). lca.
assert (ab32: swapab 3%nat 2%nat = C0). lca.
assert (ab33: swapab 3%nat 3%nat = C0). lca.
assert (ab34: swapab 3%nat 4%nat = C0). lca.
assert (ab35: swapab 3%nat 5%nat = C1). lca.
assert (ab36: swapab 3%nat 6%nat = C0). lca.
assert (ab37: swapab 3%nat 7%nat = C0). lca.
assert (ab40: swapab 4%nat 0%nat = C0). lca.
assert (ab41: swapab 4%nat 1%nat = C0). lca.
assert (ab42: swapab 4%nat 2%nat = C1). lca.
assert (ab43: swapab 4%nat 3%nat = C0). lca.
assert (ab44: swapab 4%nat 4%nat = C0). lca.
assert (ab45: swapab 4%nat 5%nat = C0). lca.
assert (ab46: swapab 4%nat 6%nat = C0). lca.
assert (ab47: swapab 4%nat 7%nat = C0). lca.
assert (ab50: swapab 5%nat 0%nat = C0). lca.
assert (ab51: swapab 5%nat 1%nat = C0). lca.
assert (ab52: swapab 5%nat 2%nat = C0). lca.
assert (ab53: swapab 5%nat 3%nat = C1). lca.
assert (ab54: swapab 5%nat 4%nat = C0). lca.
assert (ab55: swapab 5%nat 5%nat = C0). lca.
assert (ab56: swapab 5%nat 6%nat = C0). lca.
assert (ab57: swapab 5%nat 7%nat = C0). lca.
assert (ab60: swapab 6%nat 0%nat = C0). lca.
assert (ab61: swapab 6%nat 1%nat = C0). lca.
assert (ab62: swapab 6%nat 2%nat = C0). lca.
assert (ab63: swapab 6%nat 3%nat = C0). lca.
assert (ab64: swapab 6%nat 4%nat = C0). lca.
assert (ab65: swapab 6%nat 5%nat = C0). lca.
assert (ab66: swapab 6%nat 6%nat = C1). lca.
assert (ab67: swapab 6%nat 7%nat = C0). lca.
assert (ab70: swapab 7%nat 0%nat = C0). lca.
assert (ab71: swapab 7%nat 1%nat = C0). lca.
assert (ab72: swapab 7%nat 2%nat = C0). lca.
assert (ab73: swapab 7%nat 3%nat = C0). lca.
assert (ab74: swapab 7%nat 4%nat = C0). lca.
assert (ab75: swapab 7%nat 5%nat = C0). lca.
assert (ab76: swapab 7%nat 6%nat = C0). lca.
assert (ab77: swapab 7%nat 7%nat = C1). lca.
apply mat_equiv_eq.
1,2: solve_WF_matrix.
by_cell.
all: rewrite Mmult88_explicit_decomp; solve_WF_matrix.
all: try rewrite bc00.
all: try rewrite bc01.
all: try rewrite bc02.
all: try rewrite bc03.
all: try rewrite bc04.
all: try rewrite bc05.
all: try rewrite bc06.
all: try rewrite bc07.
all: try rewrite bc10.
all: try rewrite bc11.
all: try rewrite bc12.
all: try rewrite bc13.
all: try rewrite bc14.
all: try rewrite bc15.
all: try rewrite bc16.
all: try rewrite bc17.
all: try rewrite bc20.
all: try rewrite bc21.
all: try rewrite bc22.
all: try rewrite bc23.
all: try rewrite bc24.
all: try rewrite bc25.
all: try rewrite bc26.
all: try rewrite bc27.
all: try rewrite bc30.
all: try rewrite bc31.
all: try rewrite bc32.
all: try rewrite bc33.
all: try rewrite bc34.
all: try rewrite bc35.
all: try rewrite bc36.
all: try rewrite bc37.
all: try rewrite bc40.
all: try rewrite bc41.
all: try rewrite bc42.
all: try rewrite bc43.
all: try rewrite bc44.
all: try rewrite bc45.
all: try rewrite bc46.
all: try rewrite bc47.
all: try rewrite bc50.
all: try rewrite bc51.
all: try rewrite bc52.
all: try rewrite bc53.
all: try rewrite bc54.
all: try rewrite bc55.
all: try rewrite bc56.
all: try rewrite bc57.
all: try rewrite bc60.
all: try rewrite bc61.
all: try rewrite bc62.
all: try rewrite bc63.
all: try rewrite bc64.
all: try rewrite bc65.
all: try rewrite bc66.
all: try rewrite bc67.
all: try rewrite bc70.
all: try rewrite bc71.
all: try rewrite bc72.
all: try rewrite bc73.
all: try rewrite bc74.
all: try rewrite bc75.
all: try rewrite bc76.
all: try rewrite bc77.
all: repeat rewrite Cmult_0_r.
all: repeat rewrite Cplus_0_r.
all: repeat rewrite Cplus_0_l.
all: rewrite Cmult_1_r.
all: rewrite Mmult88_explicit_decomp; solve_WF_matrix.
all: try rewrite bc00.
all: try rewrite bc01.
all: try rewrite bc02.
all: try rewrite bc03.
all: try rewrite bc04.
all: try rewrite bc05.
all: try rewrite bc06.
all: try rewrite bc07.
all: try rewrite bc10.
all: try rewrite bc11.
all: try rewrite bc12.
all: try rewrite bc13.
all: try rewrite bc14.
all: try rewrite bc15.
all: try rewrite bc16.
all: try rewrite bc17.
all: try rewrite bc20.
all: try rewrite bc21.
all: try rewrite bc22.
all: try rewrite bc23.
all: try rewrite bc24.
all: try rewrite bc25.
all: try rewrite bc26.
all: try rewrite bc27.
all: try rewrite bc30.
all: try rewrite bc31.
all: try rewrite bc32.
all: try rewrite bc33.
all: try rewrite bc34.
all: try rewrite bc35.
all: try rewrite bc36.
all: try rewrite bc37.
all: try rewrite bc40.
all: try rewrite bc41.
all: try rewrite bc42.
all: try rewrite bc43.
all: try rewrite bc44.
all: try rewrite bc45.
all: try rewrite bc46.
all: try rewrite bc47.
all: try rewrite bc50.
all: try rewrite bc51.
all: try rewrite bc52.
all: try rewrite bc53.
all: try rewrite bc54.
all: try rewrite bc55.
all: try rewrite bc56.
all: try rewrite bc57.
all: try rewrite bc60.
all: try rewrite bc61.
all: try rewrite bc62.
all: try rewrite bc63.
all: try rewrite bc64.
all: try rewrite bc65.
all: try rewrite bc66.
all: try rewrite bc67.
all: try rewrite bc70.
all: try rewrite bc71.
all: try rewrite bc72.
all: try rewrite bc73.
all: try rewrite bc74.
all: try rewrite bc75.
all: try rewrite bc76.
all: try rewrite bc77.
all: repeat rewrite Cmult_0_l.
all: repeat rewrite Cplus_0_r.
all: repeat rewrite Cplus_0_l.
all: rewrite Cmult_1_l.
all: rewrite Mmult88_explicit_decomp; solve_WF_matrix.
all: try rewrite ab00.
all: try rewrite ab01.
all: try rewrite ab02.
all: try rewrite ab03.
all: try rewrite ab04.
all: try rewrite ab05.
all: try rewrite ab06.
all: try rewrite ab07.
all: try rewrite ab10.
all: try rewrite ab11.
all: try rewrite ab12.
all: try rewrite ab13.
all: try rewrite ab14.
all: try rewrite ab15.
all: try rewrite ab16.
all: try rewrite ab17.
all: try rewrite ab20.
all: try rewrite ab21.
all: try rewrite ab22.
all: try rewrite ab23.
all: try rewrite ab24.
all: try rewrite ab25.
all: try rewrite ab26.
all: try rewrite ab27.
all: try rewrite ab30.
all: try rewrite ab31.
all: try rewrite ab32.
all: try rewrite ab33.
all: try rewrite ab34.
all: try rewrite ab35.
all: try rewrite ab36.
all: try rewrite ab37.
all: try rewrite ab40.
all: try rewrite ab41.
all: try rewrite ab42.
all: try rewrite ab43.
all: try rewrite ab44.
all: try rewrite ab45.
all: try rewrite ab46.
all: try rewrite ab47.
all: try rewrite ab50.
all: try rewrite ab51.
all: try rewrite ab52.
all: try rewrite ab53.
all: try rewrite ab54.
all: try rewrite ab55.
all: try rewrite ab56.
all: try rewrite ab57.
all: try rewrite ab60.
all: try rewrite ab61.
all: try rewrite ab62.
all: try rewrite ab63.
all: try rewrite ab64.
all: try rewrite ab65.
all: try rewrite ab66.
all: try rewrite ab67.
all: try rewrite ab70.
all: try rewrite ab71.
all: try rewrite ab72.
all: try rewrite ab73.
all: try rewrite ab74.
all: try rewrite ab75.
all: try rewrite ab76.
all: try rewrite ab77.
all: repeat rewrite Cmult_0_r.
all: repeat rewrite Cplus_0_r.
all: repeat rewrite Cplus_0_l.
all: rewrite Cmult_1_r.
all: rewrite Mmult88_explicit_decomp; solve_WF_matrix.
all: try rewrite ab00.
all: try rewrite ab01.
all: try rewrite ab02.
all: try rewrite ab03.
all: try rewrite ab04.
all: try rewrite ab05.
all: try rewrite ab06.
all: try rewrite ab07.
all: try rewrite ab10.
all: try rewrite ab11.
all: try rewrite ab12.
all: try rewrite ab13.
all: try rewrite ab14.
all: try rewrite ab15.
all: try rewrite ab16.
all: try rewrite ab17.
all: try rewrite ab20.
all: try rewrite ab21.
all: try rewrite ab22.
all: try rewrite ab23.
all: try rewrite ab24.
all: try rewrite ab25.
all: try rewrite ab26.
all: try rewrite ab27.
all: try rewrite ab30.
all: try rewrite ab31.
all: try rewrite ab32.
all: try rewrite ab33.
all: try rewrite ab34.
all: try rewrite ab35.
all: try rewrite ab36.
all: try rewrite ab37.
all: try rewrite ab40.
all: try rewrite ab41.
all: try rewrite ab42.
all: try rewrite ab43.
all: try rewrite ab44.
all: try rewrite ab45.
all: try rewrite ab46.
all: try rewrite ab47.
all: try rewrite ab50.
all: try rewrite ab51.
all: try rewrite ab52.
all: try rewrite ab53.
all: try rewrite ab54.
all: try rewrite ab55.
all: try rewrite ab56.
all: try rewrite ab57.
all: try rewrite ab60.
all: try rewrite ab61.
all: try rewrite ab62.
all: try rewrite ab63.
all: try rewrite ab64.
all: try rewrite ab65.
all: try rewrite ab66.
all: try rewrite ab67.
all: try rewrite ab70.
all: try rewrite ab71.
all: try rewrite ab72.
all: try rewrite ab73.
all: try rewrite ab74.
all: try rewrite ab75.
all: try rewrite ab76.
all: try rewrite ab77.
all: repeat rewrite Cmult_0_l.
all: repeat rewrite Cplus_0_r.
all: repeat rewrite Cplus_0_l.
all: rewrite Cmult_1_l.
all: unfold kron, I.
all: simpl.
all: apply Cmult_comm.
Qed.