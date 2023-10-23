From Proof Require Import Real.
From Proof Require Import Complex.
From Proof Require Import Matrix.
From Proof Require Import Assumptions.
From Proof Require Import Definitions.

Lemma a1 : forall {n} (D : Square n), (Invertible (D) -> Determinant (D) <> 0) /\ (Determinant (D) <> 0 -> Invertible(D)). Proof. Admitted.

Lemma a2 : forall {n} (D E : Square n), Determinant (D × E) = (Determinant(D) * Determinant(E))%C. Proof. Admitted.

Lemma a3 : forall {n} (D E : Square n), trace (D × E) = trace (E × D). 
Proof. 
    intros n D E.
    unfold trace.
    unfold Mmult.
    induction n.
    + trivial.
    + simpl.
        replace (Csum (fun x : nat => Csum (fun y : nat => E x y * D y x) n + E x n * D n x) n)%C 
          with (Csum (fun x : nat => Csum (fun y : nat => E x y * D y x) n ) n + Csum (fun x : nat => E x n * D n x) n)%C.
        replace (Csum (fun x : nat => Csum (fun y : nat => D x y * E y x) n + D x n * E n x) n)%C 
          with (Csum (fun x : nat => Csum (fun y : nat => D x y * E y x) n ) n + Csum (fun x : nat => D x n * E n x) n)%C.
        rewrite IHn.
        replace (Csum (fun y : nat => E n y * D y n) n)%C
          with (Csum (fun x : nat => D x n * E n x) n)%C.
        replace (Csum (fun x : nat => E x n * D n x) n)%C
          with (Csum (fun y : nat => D n y * E y n) n)%C.
        ring.
          - apply Csum_eq.
            intros.
            apply Cmult_comm.
          - apply Csum_eq.
            intros.
            apply Cmult_comm.
          - rewrite <- Csum_plus.
            reflexivity.
          - rewrite <- Csum_plus.
            reflexivity.
Qed.

Lemma a4 : forall {n} (D E : Square n), Invertible(E) -> Eigenvalues (E × D × Inverse(E)) = Eigenvalues (D). Proof. Admitted.

Lemma a5 : forall {n} (D E : Square n), (D × E) == I n -> (E × D) == I n.
Proof.
  intros.
  assert (invertible_D: Invertible(D)).
  {
   apply a1. 
  }

    