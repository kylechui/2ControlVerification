From Proof Require Import Matrix.
From Proof Require Import Qubit.
From Proof Require Import Multiqubit.
From Proof Require Import HelperProperties.
From Proof Require Import SwapProperty.
From Proof Require Import Definitions.
Lemma a7 : forall (a b : Vector 2),
  SWAP × (a ⊗ b) == b ⊗ a.
Proof.
  lma.
Qed.

Lemma a7_a : forall (a b c : Vector 2),
  (I 2 ⊗ SWAP) × (a ⊗ b ⊗ c) == (a ⊗ c ⊗ b).
Proof.
  intros.
  rewrite kron_assoc_vect.
  rewrite kron_mixed_product.
  rewrite Mmult_1_l.
  rewrite a7.
  lma.
Qed.

Lemma a8 : forall (A B : Unitary 2),
  SWAP × (A ⊗ B) × SWAP == B ⊗ A.
Proof.
  lma.
Qed.

Definition SWAPBC := I 2 ⊗ SWAP.

Lemma a8_a : forall (A B C : Matrix 2 2),
  SWAPBC × (A ⊗ B ⊗ C) × SWAPBC == (A ⊗ C ⊗ B).
Proof.
  intros.
  rewrite kron_assoc_mat.
  rewrite (kron_mixed_product (I 2) SWAP A (B ⊗ C)).
  rewrite Mmult_1_l.
  rewrite (kron_mixed_product A (SWAP × (B ⊗ C)) (I 2) SWAP).
  rewrite Mmult_1_r.
  rewrite a8.
  rewrite <- kron_assoc_mat.
  reflexivity.
Qed.

Definition SWAPAB := SWAP ⊗ I 2.

Lemma a8_b : forall (A B C : Matrix 2 2),
  SWAPAB × (A ⊗ B ⊗ C) × SWAPAB == (B ⊗ A ⊗ C).
Proof.
  intros.
  rewrite (kron_mixed_product SWAP (I 2) (A ⊗ B) C).
  rewrite Mmult_1_l.
  rewrite (kron_mixed_product (SWAP × (A ⊗ B)) C SWAP (I 2)).
  rewrite Mmult_1_r.
  rewrite a8.
  reflexivity.
Qed.

Definition SWAPAC := SWAPBC × SWAPAB × SWAPBC.

Lemma a8_c : forall (A B C : Square 2), 
  SWAPAC × (A ⊗ B ⊗ C) × SWAPAC == (C ⊗ B ⊗ A).
Proof. 
  intros.
  unfold SWAPAC.
  rewrite <- Mmult_assoc.
  rewrite <- Mmult_assoc.
  rewrite Mmult_assoc with (A := SWAPBC × SWAPAB).
  rewrite Mmult_assoc with (A := SWAPBC × SWAPAB).
  rewrite a8_a.
  rewrite Mmult_assoc with (A := SWAPBC).
  rewrite Mmult_assoc with (A := SWAPBC).
  rewrite a8_b.
  rewrite a8_a.
  reflexivity.
Qed.

Lemma a9 : forall (V : Unitary 4),
  SWAPAB × SWAPBC × (V ⊗ I 2) × SWAPBC × SWAPAB == (I 2 ⊗ V).
Proof.
  intros.
  rewrite (Mmult_assoc (SWAP ⊗ I 2)).
  rewrite (Mmult_assoc (SWAP ⊗ I 2)).
  rewrite swap_helper.
  repeat rewrite <- Mmult_assoc.
  assert (H : SWAP ⊗ I 2 × (SWAP ⊗ I 2) == I 8). lma.
  rewrite H.
  rewrite Mmult_1_l.
  rewrite (Mmult_assoc (I 2 ⊗ V)).
  rewrite H.
  rewrite Mmult_1_r.
  reflexivity.
Qed.

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
Qed.