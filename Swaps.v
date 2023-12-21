Require Import QuantumLib.Quantum.
From Proof Require Import SwapHelpers.
From Proof Require Import GateHelpers.
From Proof Require Import SwapProperty.
Lemma a10 : forall (a b : Vector 2),
  WF_Matrix a -> WF_Matrix b -> 
  swap × (a ⊗ b) = b ⊗ a.
Proof.
  intros.
  apply mat_equiv_eq.
  apply WF_mult.
  apply WF_swap.
  apply WF_kron. reflexivity. reflexivity. apply H. apply H0.
  apply WF_kron. reflexivity. reflexivity. apply H0. apply H.
  by_cell.
  lca. lca. lca. lca.
Qed.

Lemma a11 : forall (A B : Square 2),
  WF_Matrix A -> WF_Matrix B ->
  swap × (A ⊗ B) × swap = B ⊗ A.
Proof.
  intros.
  apply mat_equiv_eq.
  apply WF_mult. apply WF_mult.
  apply WF_swap.
  apply WF_kron. reflexivity. reflexivity. apply H. apply H0.
  apply WF_swap.
  apply WF_kron. reflexivity. reflexivity. apply H0. apply H.
  by_cell.
  lca. lca. lca. lca. lca. lca. lca. lca.
  lca. lca. lca. lca. lca. lca. lca. lca.
Qed.

Lemma a12 : forall (U : Square 4),
  WF_Matrix U -> swapab × acgate U × swapab = bcgate U.
Proof.
intros.
apply mat_equiv_eq.
apply WF_mult. apply WF_mult. apply WF_swapab. apply WF_acgate. apply H. apply WF_swapab.
apply WF_bcgate. apply H.
unfold acgate. unfold swapbc. unfold abgate.
rewrite swap_helper.
fold swapab.
rewrite <- Mmult_assoc.
rewrite <- Mmult_assoc with (A:= swapab) (B:= swapab) (C:=(I 2 ⊗ U)).
rewrite swapab_inverse. 
rewrite Mmult_1_l.
rewrite Mmult_assoc.
rewrite swapab_inverse at 1.
rewrite Mmult_1_r.
unfold bcgate.
apply mat_equiv_refl.
apply WF_kron. reflexivity. reflexivity. apply WF_I. apply H.
apply WF_kron. reflexivity. reflexivity. apply WF_I. apply H.
apply H.
Qed.

(* 
(* TODO: This proof has changed between versions. Is it better to outline the steps in the proof, 
if lma is sufficient to verify the lemma? *)
Lemma a10_1 : forall (D: Unitary 2), SWAPAB × CCU (D) × SWAPAB  == CCU (D).
Proof.
unfold CCU, Diag2.
lma.
Qed.

Lemma a10_2 : forall (c1 : C), SWAPBC × CCU (Diag2 1 c1) × SWAPBC == CCU (Diag2 1 c1).
Proof.
unfold CCU, Diag2.
lma.
Qed.

Lemma a10_3 : forall (c1 : C), SWAPAC × CCU (Diag2 1 c1) × SWAPAC == CCU (Diag2 1 c1).
Proof.
intros.
assert (Help : CCU (Diag2 1 c1) == 
  (∣0⟩ × ∣0⟩†) ⊗ I 4 + (∣1⟩ × ∣1⟩†) ⊗ CU (Diag2 1 c1)).
{
  unfold CCU, CU, Diag2. lma.
}
rewrite Help; clear Help.
rewrite Mmult_plus_dist_l.
repeat rewrite Mmult_plus_dist_r.
assert (Help : CU (Diag2 1 c1) == (∣0⟩ × ∣0⟩†) ⊗ I 2 + (∣1⟩ × ∣1⟩†) ⊗ Diag2 1 c1).
{
  unfold CU, Diag2. lma.
}
rewrite Help; clear Help.
rewrite kron_plus_dist_l.
rewrite Mmult_plus_dist_l.
repeat rewrite Mmult_plus_dist_r.
assert (Main1 : SWAPAC × 
  ((∣0⟩ × ∣0⟩†) ⊗ I 4) × SWAPAC ==
  I 4 ⊗ (∣0⟩ × ∣0⟩†)).
{
  set (A := ∣0⟩ × ∣0⟩†).
  assert (Isplit : I 4 == I 2 ⊗ I 2). lma.
  rewrite Isplit.
  rewrite <- kron_assoc_mat.
  apply a8_c.
}
rewrite Main1.
rewrite <- Mplus_assoc.
assert (Main2 : SWAPAC × (∣ 1 ⟩ × (∣ 1 ⟩) † ⊗ (∣ 0 ⟩ × (∣ 0 ⟩) † ⊗ I 2)) 
× SWAPAC == I 2 ⊗ (∣0⟩ × ∣0⟩†) ⊗ (∣1⟩ × ∣1⟩†)).
{
  set (A := ∣0⟩ × ∣0⟩†).
  set (B := ∣1⟩ × ∣1⟩†).
  rewrite <- kron_assoc_mat.
  apply a8_c.
}
rewrite Main2.
assert (Main3 : SWAPAC × (∣ 1 ⟩ × (∣ 1 ⟩) † ⊗ (∣ 1 ⟩ × (∣ 1 ⟩) † ⊗ Diag2 1 c1)) 
× SWAPAC == Diag2 1 c1 ⊗ (∣1⟩ × ∣1⟩†) ⊗ (∣1⟩ × ∣1⟩†)).
{
  set (A := ∣1⟩ × ∣1⟩†).
  set (B := Diag2 1 c1).
  rewrite <- kron_assoc_mat.
  apply a8_c.
}
rewrite Main3.
lma.
Qed. *)