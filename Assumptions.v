From Proof Require Import Real.
From Proof Require Import Complex.
From Proof Require Import Matrix.
From Proof Require Import Qubit.
From Proof Require Import Multiqubit.
From Proof Require Import Definitions.
From Proof Require Import Permutation.
Require Import List.
Import ListNotations.

(* Eigenvalue assumptions *)

Definition Eigenvalues {n} (A : Square n) : list C. Admitted.

Property eigenvalues_of_square2 : forall (A : Square 2),
  exists (a b : C), Eigenvalues A = [a; b].
Admitted.

Property eigenvalues_of_tensor_product : forall (A B : Square 2),
  Eigenvalues (A ⊗ B) = [
    Cmult (nth 0 (Eigenvalues A) 0) (nth 0 (Eigenvalues B) 0);
    Cmult (nth 0 (Eigenvalues A) 0) (nth 1 (Eigenvalues B) 0);
    Cmult (nth 1 (Eigenvalues A) 0) (nth 0 (Eigenvalues B) 0);
    Cmult (nth 1 (Eigenvalues A) 0) (nth 1 (Eigenvalues B) 0)
  ].
Admitted.

Property eigenvalues_of_unitary : forall {n} (U : Unitary n) (WF_U : WF_Unitary U),
  forall (a : nat), (a < length (Eigenvalues U))%nat -> nth a (Eigenvalues U) 0 <> 0.
Admitted.

Property eigenvalues_compat : forall {n} (A B : Square n),
  A == B -> Eigenvalues A = Eigenvalues B.
Admitted.

Property eigenvalues_of_diag2 : forall (A : Square 2),
  Diagonal A -> Eigenvalues A = [(A 0 0)%nat ; (A 1 1)%nat].
Admitted.

Property eigenvalues_of_diag4 : forall (A : Square 4),
  Diagonal A -> Eigenvalues A = [(A 0 0)%nat ; (A 1 1)%nat ; (A 2 2)%nat ; (A 3 3)%nat].
Admitted.

Property corner_unitary_matrix_eigenvalues : forall (U : Unitary 4) (WF_U : WF_Unitary U)
  (A B : Unitary 2) (WF_A : WF_Unitary A) (WF_B : WF_Unitary B),
  U == (∣0⟩ × ∣0⟩†) ⊗ A + (∣1⟩ × ∣1⟩†) ⊗ B ->
  Permutation (Eigenvalues U) 
    [nth 0 (Eigenvalues A) 0;
     nth 1 (Eigenvalues A) 0;
     nth 0 (Eigenvalues B) 0;
     nth 1 (Eigenvalues B) 0].
Admitted.

Lemma product_of_eigenvalues_equals_determinant : forall (A : Square 2),
  Determinant2 A = Cmult (nth 0 (Eigenvalues A) 0) (nth 1 (Eigenvalues A) 0).
Admitted.

Lemma length_of_eigenvalues : forall (A : Square 2),
  length (Eigenvalues A) = 2%nat.
Proof.
  intros.
  assert (H := eigenvalues_of_square2 A).
  destruct H as [a [b H]].
  rewrite H.
  simpl.
  reflexivity.
Qed.

(* Partial trace assumptions *)

Definition partial_trace_l {m} (U : Square m) (n : nat) : Square n. Admitted.

Definition partial_trace_r {m} (U : Square m) (n : nat) : Square n. Admitted.

Lemma kron_partial_trace_l : forall {m n} (U : Square (m * n)) (A : Square m) (B : Square n),
  U == A ⊗ B -> partial_trace_l U n == trace A * B.
Admitted.

Lemma kron_partial_trace_r : forall {m n} (U : Square (m * n)) (A : Square m) (B : Square n),
  U == A ⊗ B -> partial_trace_r U m == trace B * A.
Admitted.

Lemma partial_trace_linear_l : forall {m} (n : nat) (U U' : Square m),
  partial_trace_l (U + U') n == partial_trace_l U n + partial_trace_l U' n.
Admitted.

Lemma partial_trace_linear_r : forall {m} (n : nat) (U U' : Square m),
  partial_trace_r (U + U') n == partial_trace_r U n + partial_trace_r U' n.
Admitted.

Lemma partial_trace_compat_l : forall {m} (n : nat) (U U' : Square m),
  U == U' -> partial_trace_l U n == partial_trace_l U' n.
Admitted.

Lemma partial_trace_compat_r : forall {m} (n : nat) (U U' : Square m),
  U == U' -> partial_trace_r U n == partial_trace_r U' n.
Admitted.

(* Determinant assumptions *)

Definition Determinant {n} (A: Square n) : C. Admitted.

Property determinant_of_I {n}: Determinant (I n) = 1. Admitted.


(* Miscellaneous assumptions *)

Definition Inverse {n} (A : Square n) : Square n. Admitted. 

Lemma mx_linverse : forall {n} (A : Square n), Invertible (A) -> (Inverse (A)) × A == I n. Proof. Admitted.
Lemma mx_rinverse : forall {n} (A : Square n), Invertible (A) -> A × (Inverse (A))   == I n. Proof. Admitted.

Lemma corner_matrices_are_unitary_8 : forall (U : Unitary 8) (WF_U : WF_Unitary U),
  Get8_01 U == Zero 4 4 /\ Get8_10 U == Zero 4 4 -> 
  WF_Unitary (Get8_00 U) /\ WF_Unitary (Get8_11 U).
Admitted.