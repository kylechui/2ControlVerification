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

(* TODO: finish subproof. *)
Lemma Cmult_nonzero : forall (a b : C), (a*b <> 0 -> a<>0 /\ b<>0)%C. Admitted.

Lemma a5 : forall {n} (D E : Square n), (D × E) == I n -> (E × D) == I n.
Proof.
  intros.
  assert (det_de : Determinant(D × E) = 1).
  {
    replace (Determinant(D × E)) with (Determinant(I n)).
    apply determinant_of_I.
    apply determinant_eq.
    apply mat_equiv_sym.
    apply H.
  }
  assert (nonzero_det : Determinant(D)<>0 /\ Determinant(E)<>0).
  {
   rewrite a2 in det_de.
   apply Cmult_nonzero.
   rewrite det_de.
   apply C1_neq_C0.
  }
  assert (invertible_e : Invertible(E)).
  {
    apply a1.
    apply nonzero_det.
  }
  assert (right_inverse: I n == E × Inverse(E)).
  {
    rewrite mx_rinverse.
    apply mat_equiv_refl.
    apply invertible_e.
  }
  rewrite right_inverse.
  pattern E at 2.
  rewrite <- Mmult_1_r.
  replace (E × Inverse E) with (E × I n × Inverse E).
  rewrite <- H.
  rewrite Mmult_assoc.
  rewrite Mmult_assoc.
  rewrite <- right_inverse.
  rewrite Mmult_1_r.
  apply mat_equiv_refl.
  replace (E × I n) with (E).
  trivial.
  unfold Mmult.

    