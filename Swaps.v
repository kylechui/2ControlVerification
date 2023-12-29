Require Import QuantumLib.Quantum.
From Proof Require Import SwapHelpers.
From Proof Require Import GateHelpers.
From Proof Require Import MatrixHelpers.
From Proof Require Import SwapProperty.
Lemma a10 : forall (a b : Vector 2),
  WF_Matrix a -> WF_Matrix b -> 
  swap × (a ⊗ b) = b ⊗ a.
Proof.
  intros.
  lma'.
Qed.

Lemma a11 : forall (A B : Square 2),
  WF_Matrix A -> WF_Matrix B ->
  swap × (A ⊗ B) × swap = B ⊗ A.
Proof.
apply swap_2q.
Qed.

Lemma a12 : forall (U : Square 4),
  WF_Matrix U -> swapab × acgate U × swapab = bcgate U.
Proof.
intros.
unfold acgate. unfold swapbc. unfold abgate.
rewrite swap_helper. 2: apply H.
fold swapab.
rewrite <- Mmult_assoc.
rewrite <- Mmult_assoc with (A:= swapab) (B:= swapab) (C:=(I 2 ⊗ U)).
rewrite swapab_inverse. 
rewrite Mmult_assoc.
rewrite Mmult_1_l.
rewrite swapab_inverse at 1. 2: solve_WF_matrix.
rewrite Mmult_1_r. 2: solve_WF_matrix.
unfold bcgate.
reflexivity.
Qed.

Lemma a10_1 : forall (D: Square 2), WF_Matrix D -> swapab × ccu (D) × swapab  = ccu (D).
Proof.
intros.
lma'.
apply WF_mult. apply WF_mult. apply WF_swapab. apply WF_ccu. apply H. apply WF_swapab.
apply WF_ccu. apply H.
Qed.

Lemma a10_2 : forall (c1 : C), swapbc × ccu (diag2 1 c1) × swapbc = ccu (diag2 1 c1).
Proof.
intros.
lma'.
apply WF_mult. apply WF_mult. apply WF_swapbc. apply WF_ccu. apply WF_diag2. apply WF_swapbc.
apply WF_ccu. apply WF_diag2.
Qed.

Lemma a10_3 : forall (c1 : C), swapac × ccu (diag2 1 c1) × swapac = ccu (diag2 1 c1).
Proof.
intros.
assert (Help : ccu (diag2 1 c1) =
  ∣0⟩⟨0∣ ⊗ I 4 .+ ∣1⟩⟨1∣ ⊗ control (diag2 1 c1)).
{
  lma'.
  apply WF_ccu. apply WF_diag2.
  solve_WF_matrix. apply WF_diag2.
  unfold ccu, diag2, control.
  lca.
}
rewrite Help; clear Help.
rewrite Mmult_plus_distr_l.
repeat rewrite Mmult_plus_distr_r.
assert (Help : control (diag2 1 c1) = ∣0⟩⟨0∣ ⊗ I 2 .+ ∣1⟩⟨1∣ ⊗ diag2 1 c1).
{
  lma'.
  apply WF_control. apply WF_diag2.
  solve_WF_matrix. apply WF_diag2. 
  unfold control, diag2.  lca.
}
rewrite Help; clear Help.
rewrite kron_plus_distr_l.
rewrite Mmult_plus_distr_l.
repeat rewrite Mmult_plus_distr_r.
assert (Main1 : swapac × (∣0⟩⟨0∣ ⊗ I 4) × swapac = I 4 ⊗ ∣0⟩⟨0∣).
{
  set (A := ∣0⟩⟨0∣).
  assert (A ⊗ I 4 = (A ⊗ I 2) ⊗ I 2). lma'.
  rewrite H.
  rewrite swapac_3q. 4: apply WF_I. 3: apply WF_I. 2: apply WF_braqubit0.
  rewrite kron_I. 3: lia. 2: lia.
  reflexivity.
}
rewrite Main1 at 1.
rewrite <- Mplus_assoc.
assert (Main2 : swapac × (∣1⟩⟨1∣ ⊗ (∣0⟩⟨0∣ ⊗ I 2)) × swapac =
I 2  ⊗ ∣0⟩⟨0∣ ⊗ ∣1⟩⟨1∣).
{
  set (A := ∣0⟩⟨0∣).
  set (B := ∣1⟩⟨1∣).
  rewrite <- kron_assoc. 4: apply WF_I. 3: apply WF_braqubit0. 2: apply WF_braqubit1.
  apply swapac_3q. 3: apply WF_I. 2: apply WF_braqubit0. apply WF_braqubit1.
}
rewrite Main2 at 1.
assert (Main3 : swapac × (∣1⟩⟨1∣ ⊗ (∣1⟩⟨1∣ ⊗ diag2 C1 c1)) × swapac =
diag2 C1 c1 ⊗ ∣1⟩⟨1∣ ⊗ ∣1⟩⟨1∣).
{
  set (A := ∣1⟩⟨1∣).
  set (B := diag2 1 c1).
  rewrite <- kron_assoc. 4: apply WF_diag2. 3: apply WF_braqubit1. 2: apply WF_braqubit1.
  apply swapac_3q. 3: apply WF_diag2. 2: apply WF_braqubit1. apply WF_braqubit1.
}
rewrite Main3 at 1.
lma'. 2: solve_WF_matrix. 1: solve_WF_matrix.
apply WF_diag2. apply WF_diag2.
Qed.