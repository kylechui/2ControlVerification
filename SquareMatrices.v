From Proof Require Import Real.
From Proof Require Import Complex.
From Proof Require Import Matrix.
From Proof Require Import Assumptions.
From Proof Require Import Definitions.
From Proof Require Import Qubit.

Require Import List.
Import ListNotations.

Definition Nonzero_det_2 (A : Square 2) : Prop := Determinant2 A <> 0.

Definition Invertible_2 (A : Square 2) := exists (B : Square 2), B × A == I 2 /\ A × B == I 2.

Definition Inverse_2 (A : Square 2) (pf : Invertible_2 A) : Square 2 :=
  (1 /Determinant2(A))%C * (l2M [[(A 1 1)%nat; (-1 * (A 0 1)%nat)%C]; [(A 0 0)%nat; (-1 * (A 1 0)%nat)%C]]).

Lemma a1_2 : forall (D : Square 2), Determinant2 (D) <> 0 -> Invertible_2(D).
Proof.
Admitted.

Lemma a2_2 : forall (D E : Square 2), Determinant2 (D × E) = (Determinant2(D) * Determinant2(E))%C. Proof. Admitted.

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

(* TODO: add a4_4 after discussion on representation of invertible. *)
Lemma a4_2 : forall (D E : Square 2) (pf : Invertible_2 E), Eigenvalues (E × D × Inverse_2 E pf) = Eigenvalues (D). Proof. Admitted.

Property det2_of_I: Determinant2 (I 2) = 1. 
  Proof.
  intros.
  unfold I.
  unfold Determinant2.
  simpl.
  ring.
  Qed.

Lemma det2_eq: forall (A B: Square 2), A == B -> Determinant2(A) = Determinant2(B).
  Proof.
  intros.
  unfold Determinant2.
  unfold mat_equiv in H.
  repeat rewrite H ; auto.
  Qed.

Lemma Cmult_nonzero : forall (a b : C), (a * b)%C <> 0 -> a <> 0 /\ b <> 0.
  Proof.
  intros a b H.
  split.
  - intro Ha.
    apply H.
    rewrite Ha, Cmult_0_l.
    reflexivity.
  - intro Hb.
    apply H.
    rewrite Hb, Cmult_0_r.
    reflexivity.
  Qed.

Lemma mx_linverse_2 : forall (A : Square 2) (pf : Invertible_2 A), (Inverse_2 A pf) × A == I 2.
 Proof.
 Admitted.
Lemma mx_rinverse_2 : forall (A : Square 2) (pf : Invertible_2 A), A × (Inverse_2 A pf) == I 2.
 Proof.
 Admitted.

Lemma a5_2 : forall (D E : Square 2), (D × E) == I 2 -> (E × D) == I 2.
Proof.
  intros.
  assert (det_de : (Determinant2(D) * Determinant2(E) <> 0)%C).
  {
    rewrite <- a2_2.
    replace (Determinant2(D × E)) with (Determinant2(I 2)).
    rewrite det2_of_I.
    apply C1_neq_C0.
    apply det2_eq.
    apply mat_equiv_sym.
    apply H.
  }
  apply Cmult_nonzero in det_de.
  destruct det_de as [det_d det_e].
  assert (invertible_d : Invertible_2 D).
  {
    apply a1_2.
    apply det_d.
  }
  assert (invertible_e : Invertible_2 E).
  {
    apply a1_2.
    apply det_e.
  }

  assert (right_inverse: I 2 == E × (Inverse_2 E invertible_e)).
  {
    rewrite mx_rinverse_2. 
    apply mat_equiv_refl.
  }
  rewrite right_inverse.
  cut (E × Inverse_2 E invertible_e == E × I 2 × Inverse_2 E invertible_e).
  intros.
  rewrite H0.
  rewrite <- H.
  rewrite Mmult_assoc.
  rewrite Mmult_assoc.
  rewrite <- right_inverse.
  rewrite Mmult_1_r.
  apply mat_equiv_refl.
  rewrite Mmult_1_r.
  apply mat_equiv_refl.
Qed.

(* Supporting the only 2 needed sizes of lemma a6. To a human this is easily extended to size nxn. 
   Unclear how well that will translate to coq, since the trivial human proof is elementary pattern matching, on infinite sizes.
*)
  
(*Currently, the process of doing a cell wise comparison seems the best. 
  Working on shortening this proof won't help shorten complexity of paper.
*)
Lemma a6_2: forall (U00 U01 U10 U11 V00 V01 V10 V11 : Square 2),
(∣0⟩ × ∣0⟩†) ⊗ U00 + (∣0⟩ × ∣1⟩†) ⊗ U01 + (∣1⟩ × ∣0⟩†) ⊗ U10 + (∣1⟩ × ∣1⟩†) ⊗ U11 ==
(∣0⟩ × ∣0⟩†) ⊗ V00 + (∣0⟩ × ∣1⟩†) ⊗ V01 + (∣1⟩ × ∣0⟩†) ⊗ V10 + (∣1⟩ × ∣1⟩†) ⊗ V11 ->
U00 == V00 /\ U01 == V01 /\ U10 == V10 /\ U11 == V11. 
Proof.
intros.
set (A := (∣0⟩ × ∣0⟩†) ⊗ U00 + (∣0⟩ × ∣1⟩†) ⊗ U01 + (∣1⟩ × ∣0⟩†) ⊗ U10 + (∣1⟩ × ∣1⟩†) ⊗ U11).
set (B := (∣0⟩ × ∣0⟩†) ⊗ V00 + (∣0⟩ × ∣1⟩†) ⊗ V01 + (∣1⟩ × ∣0⟩†) ⊗ V10 + (∣1⟩ × ∣1⟩†) ⊗ V11).
fold A in H.
fold B in H.
split.
(* assert LHS equal to cells of A *)
assert (L0 : (U00 0 0)%nat = (A 0 0)%nat). lca.
assert (L1 : (U00 0 1)%nat = (A 0 1)%nat). lca.
assert (L2 : (U00 1 0)%nat = (A 1 0)%nat). lca.
assert (L3 : (U00 1 1)%nat = (A 1 1)%nat). lca.
(* assert RHS equal to cells of B *)
assert (R0 : (V00 0 0)%nat = (B 0 0)%nat). lca.
assert (R1 : (V00 0 1)%nat = (B 0 1)%nat). lca.
assert (R2 : (V00 1 0)%nat = (B 1 0)%nat). lca.
assert (R3 : (V00 1 1)%nat = (B 1 1)%nat). lca.
(* create subgoals to verify matrix equality by checking every element*)
by_cell.
(* use asserted properties to prove cell equality*)
rewrite L0; rewrite R0; rewrite H. lca. lia. lia.
rewrite L1; rewrite R1; rewrite H. lca. lia. lia.
rewrite L2; rewrite R2; rewrite H. lca. lia. lia.
rewrite L3; rewrite R3; rewrite H. lca. lia. lia.
(*repeat this tactic on each block*)

split.
assert (L0 : (U01 0 0)%nat = (A 0 2)%nat). lca.
assert (L1 : (U01 0 1)%nat = (A 0 3)%nat). lca.
assert (L2 : (U01 1 0)%nat = (A 1 2)%nat). lca.
assert (L3 : (U01 1 1)%nat = (A 1 3)%nat). lca.
assert (R0 : (V01 0 0)%nat = (B 0 2)%nat). lca.
assert (R1 : (V01 0 1)%nat = (B 0 3)%nat). lca.
assert (R2 : (V01 1 0)%nat = (B 1 2)%nat). lca.
assert (R3 : (V01 1 1)%nat = (B 1 3)%nat). lca.
by_cell.
rewrite L0; rewrite R0; rewrite H. lca. lia. lia.
rewrite L1; rewrite R1; rewrite H. lca. lia. lia.
rewrite L2; rewrite R2; rewrite H. lca. lia. lia.
rewrite L3; rewrite R3; rewrite H. lca. lia. lia.

split.
assert (L0 : (U10 0 0)%nat = (A 2 0)%nat). lca.
assert (L1 : (U10 0 1)%nat = (A 2 1)%nat). lca.
assert (L2 : (U10 1 0)%nat = (A 3 0)%nat). lca.
assert (L3 : (U10 1 1)%nat = (A 3 1)%nat). lca.
assert (R0 : (V10 0 0)%nat = (B 2 0)%nat). lca.
assert (R1 : (V10 0 1)%nat = (B 2 1)%nat). lca.
assert (R2 : (V10 1 0)%nat = (B 3 0)%nat). lca.
assert (R3 : (V10 1 1)%nat = (B 3 1)%nat). lca.
by_cell.
rewrite L0; rewrite R0; rewrite H. lca. lia. lia.
rewrite L1; rewrite R1; rewrite H. lca. lia. lia.
rewrite L2; rewrite R2; rewrite H. lca. lia. lia.
rewrite L3; rewrite R3; rewrite H. lca. lia. lia.

assert (L0 : (U11 0 0)%nat = (A 2 2)%nat). lca.
assert (L1 : (U11 0 1)%nat = (A 2 3)%nat). lca.
assert (L2 : (U11 1 0)%nat = (A 3 2)%nat). lca.
assert (L3 : (U11 1 1)%nat = (A 3 3)%nat). lca.
assert (R0 : (V11 0 0)%nat = (B 2 2)%nat). lca.
assert (R1 : (V11 0 1)%nat = (B 2 3)%nat). lca.
assert (R2 : (V11 1 0)%nat = (B 3 2)%nat). lca.
assert (R3 : (V11 1 1)%nat = (B 3 3)%nat). lca.
by_cell.
rewrite L0; rewrite R0; rewrite H. lca. lia. lia.
rewrite L1; rewrite R1; rewrite H. lca. lia. lia.
rewrite L2; rewrite R2; rewrite H. lca. lia. lia.
rewrite L3; rewrite R3; rewrite H. lca. lia. lia.
Qed.

(* From YT's code: reviewed*)
Lemma a6_4: forall (U00 U01 U10 U11 V00 V01 V10 V11 : Square 4),
(∣0⟩ × ∣0⟩†) ⊗ U00 + (∣0⟩ × ∣1⟩†) ⊗ U01 + (∣1⟩ × ∣0⟩†) ⊗ U10 + (∣1⟩ × ∣1⟩†) ⊗ U11 ==
(∣0⟩ × ∣0⟩†) ⊗ V00 + (∣0⟩ × ∣1⟩†) ⊗ V01 + (∣1⟩ × ∣0⟩†) ⊗ V10 + (∣1⟩ × ∣1⟩†) ⊗ V11 ->
U00 == V00 /\ U01 == V01 /\ U10 == V10 /\ U11 == V11.
Proof.
intros.
set (A := (∣0⟩ × ∣0⟩†) ⊗ U00 + (∣0⟩ × ∣1⟩†) ⊗ U01 + (∣1⟩ × ∣0⟩†) ⊗ U10 + (∣1⟩ × ∣1⟩†) ⊗ U11).
set (B := (∣0⟩ × ∣0⟩†) ⊗ V00 + (∣0⟩ × ∣1⟩†) ⊗ V01 + (∣1⟩ × ∣0⟩†) ⊗ V10 + (∣1⟩ × ∣1⟩†) ⊗ V11).
fold A in H.
fold B in H.
split.
assert (R0 : (U00 0 0)%nat = (A 0 0)%nat). lca.
assert (R1 : (U00 0 1)%nat = (A 0 1)%nat). lca.
assert (R2 : (U00 0 2)%nat = (A 0 2)%nat). lca.
assert (R3 : (U00 0 3)%nat = (A 0 3)%nat). lca.
assert (R4 : (U00 1 0)%nat = (A 1 0)%nat). lca.
assert (R5 : (U00 1 1)%nat = (A 1 1)%nat). lca.
assert (R6 : (U00 1 2)%nat = (A 1 2)%nat). lca.
assert (R7 : (U00 1 3)%nat = (A 1 3)%nat). lca.
assert (R8 : (U00 2 0)%nat = (A 2 0)%nat). lca.
assert (R9 : (U00 2 1)%nat = (A 2 1)%nat). lca.
assert (R10 : (U00 2 2)%nat = (A 2 2)%nat). lca.
assert (R11 : (U00 2 3)%nat = (A 2 3)%nat). lca.
assert (R12 : (U00 3 0)%nat = (A 3 0)%nat). lca.
assert (R13 : (U00 3 1)%nat = (A 3 1)%nat). lca.
assert (R14 : (U00 3 2)%nat = (A 3 2)%nat). lca.
assert (R15 : (U00 3 3)%nat = (A 3 3)%nat). lca.
assert (S0 : (V00 0 0)%nat = (B 0 0)%nat). lca.
assert (S1 : (V00 0 1)%nat = (B 0 1)%nat). lca.
assert (S2 : (V00 0 2)%nat = (B 0 2)%nat). lca.
assert (S3 : (V00 0 3)%nat = (B 0 3)%nat). lca.
assert (S4 : (V00 1 0)%nat = (B 1 0)%nat). lca.
assert (S5 : (V00 1 1)%nat = (B 1 1)%nat). lca.
assert (S6 : (V00 1 2)%nat = (B 1 2)%nat). lca.
assert (S7 : (V00 1 3)%nat = (B 1 3)%nat). lca.
assert (S8 : (V00 2 0)%nat = (B 2 0)%nat). lca.
assert (S9 : (V00 2 1)%nat = (B 2 1)%nat). lca.
assert (S10 : (V00 2 2)%nat = (B 2 2)%nat). lca.
assert (S11 : (V00 2 3)%nat = (B 2 3)%nat). lca.
assert (S12 : (V00 3 0)%nat = (B 3 0)%nat). lca.
assert (S13 : (V00 3 1)%nat = (B 3 1)%nat). lca.
assert (S14 : (V00 3 2)%nat = (B 3 2)%nat). lca.
assert (S15 : (V00 3 3)%nat = (B 3 3)%nat). lca.
by_cell.
rewrite R0; rewrite S0; rewrite H. lca. lia. lia.
rewrite R1; rewrite S1; rewrite H. lca. lia. lia.
rewrite R2; rewrite S2; rewrite H. lca. lia. lia.
rewrite R3; rewrite S3; rewrite H. lca. lia. lia.
rewrite R4; rewrite S4; rewrite H. lca. lia. lia.
rewrite R5; rewrite S5; rewrite H. lca. lia. lia.
rewrite R6; rewrite S6; rewrite H. lca. lia. lia.
rewrite R7; rewrite S7; rewrite H. lca. lia. lia.
rewrite R8; rewrite S8; rewrite H. lca. lia. lia.
rewrite R9; rewrite S9; rewrite H. lca. lia. lia.
rewrite R10; rewrite S10; rewrite H. lca. lia. lia.
rewrite R11; rewrite S11; rewrite H. lca. lia. lia.
rewrite R12; rewrite S12; rewrite H. lca. lia. lia.
rewrite R13; rewrite S13; rewrite H. lca. lia. lia.
rewrite R14; rewrite S14; rewrite H. lca. lia. lia.
rewrite R15; rewrite S15; rewrite H. lca. lia. lia.
split.
assert (R0 : (U01 0 0)%nat = (A 0 4)%nat). lca.
assert (R1 : (U01 0 1)%nat = (A 0 5)%nat). lca.
assert (R2 : (U01 0 2)%nat = (A 0 6)%nat). lca.
assert (R3 : (U01 0 3)%nat = (A 0 7)%nat). lca.
assert (R4 : (U01 1 0)%nat = (A 1 4)%nat). lca.
assert (R5 : (U01 1 1)%nat = (A 1 5)%nat). lca.
assert (R6 : (U01 1 2)%nat = (A 1 6)%nat). lca.
assert (R7 : (U01 1 3)%nat = (A 1 7)%nat). lca.
assert (R8 : (U01 2 0)%nat = (A 2 4)%nat). lca.
assert (R9 : (U01 2 1)%nat = (A 2 5)%nat). lca.
assert (R10 : (U01 2 2)%nat = (A 2 6)%nat). lca.
assert (R11 : (U01 2 3)%nat = (A 2 7)%nat). lca.
assert (R12 : (U01 3 0)%nat = (A 3 4)%nat). lca.
assert (R13 : (U01 3 1)%nat = (A 3 5)%nat). lca.
assert (R14 : (U01 3 2)%nat = (A 3 6)%nat). lca.
assert (R15 : (U01 3 3)%nat = (A 3 7)%nat). lca.
assert (S0 : (V01 0 0)%nat = (B 0 4)%nat). lca.
assert (S1 : (V01 0 1)%nat = (B 0 5)%nat). lca.
assert (S2 : (V01 0 2)%nat = (B 0 6)%nat). lca.
assert (S3 : (V01 0 3)%nat = (B 0 7)%nat). lca.
assert (S4 : (V01 1 0)%nat = (B 1 4)%nat). lca.
assert (S5 : (V01 1 1)%nat = (B 1 5)%nat). lca.
assert (S6 : (V01 1 2)%nat = (B 1 6)%nat). lca.
assert (S7 : (V01 1 3)%nat = (B 1 7)%nat). lca.
assert (S8 : (V01 2 0)%nat = (B 2 4)%nat). lca.
assert (S9 : (V01 2 1)%nat = (B 2 5)%nat). lca.
assert (S10 : (V01 2 2)%nat = (B 2 6)%nat). lca.
assert (S11 : (V01 2 3)%nat = (B 2 7)%nat). lca.
assert (S12 : (V01 3 0)%nat = (B 3 4)%nat). lca.
assert (S13 : (V01 3 1)%nat = (B 3 5)%nat). lca.
assert (S14 : (V01 3 2)%nat = (B 3 6)%nat). lca.
assert (S15 : (V01 3 3)%nat = (B 3 7)%nat). lca.
by_cell.
rewrite R0; rewrite S0; rewrite H. lca. lia. lia.
rewrite R1; rewrite S1; rewrite H. lca. lia. lia.
rewrite R2; rewrite S2; rewrite H. lca. lia. lia.
rewrite R3; rewrite S3; rewrite H. lca. lia. lia.
rewrite R4; rewrite S4; rewrite H. lca. lia. lia.
rewrite R5; rewrite S5; rewrite H. lca. lia. lia.
rewrite R6; rewrite S6; rewrite H. lca. lia. lia.
rewrite R7; rewrite S7; rewrite H. lca. lia. lia.
rewrite R8; rewrite S8; rewrite H. lca. lia. lia.
rewrite R9; rewrite S9; rewrite H. lca. lia. lia.
rewrite R10; rewrite S10; rewrite H. lca. lia. lia.
rewrite R11; rewrite S11; rewrite H. lca. lia. lia.
rewrite R12; rewrite S12; rewrite H. lca. lia. lia.
rewrite R13; rewrite S13; rewrite H. lca. lia. lia.
rewrite R14; rewrite S14; rewrite H. lca. lia. lia.
rewrite R15; rewrite S15; rewrite H. lca. lia. lia.
split.
assert (R0 : (U10 0 0)%nat = (A 4 0)%nat). lca.
assert (R1 : (U10 0 1)%nat = (A 4 1)%nat). lca.
assert (R2 : (U10 0 2)%nat = (A 4 2)%nat). lca.
assert (R3 : (U10 0 3)%nat = (A 4 3)%nat). lca.
assert (R4 : (U10 1 0)%nat = (A 5 0)%nat). lca.
assert (R5 : (U10 1 1)%nat = (A 5 1)%nat). lca.
assert (R6 : (U10 1 2)%nat = (A 5 2)%nat). lca.
assert (R7 : (U10 1 3)%nat = (A 5 3)%nat). lca.
assert (R8 : (U10 2 0)%nat = (A 6 0)%nat). lca.
assert (R9 : (U10 2 1)%nat = (A 6 1)%nat). lca.
assert (R10 : (U10 2 2)%nat = (A 6 2)%nat). lca.
assert (R11 : (U10 2 3)%nat = (A 6 3)%nat). lca.
assert (R12 : (U10 3 0)%nat = (A 7 0)%nat). lca.
assert (R13 : (U10 3 1)%nat = (A 7 1)%nat). lca.
assert (R14 : (U10 3 2)%nat = (A 7 2)%nat). lca.
assert (R15 : (U10 3 3)%nat = (A 7 3)%nat). lca.
assert (S0 : (V10 0 0)%nat = (B 4 0)%nat). lca.
assert (S1 : (V10 0 1)%nat = (B 4 1)%nat). lca.
assert (S2 : (V10 0 2)%nat = (B 4 2)%nat). lca.
assert (S3 : (V10 0 3)%nat = (B 4 3)%nat). lca.
assert (S4 : (V10 1 0)%nat = (B 5 0)%nat). lca.
assert (S5 : (V10 1 1)%nat = (B 5 1)%nat). lca.
assert (S6 : (V10 1 2)%nat = (B 5 2)%nat). lca.
assert (S7 : (V10 1 3)%nat = (B 5 3)%nat). lca.
assert (S8 : (V10 2 0)%nat = (B 6 0)%nat). lca.
assert (S9 : (V10 2 1)%nat = (B 6 1)%nat). lca.
assert (S10 : (V10 2 2)%nat = (B 6 2)%nat). lca.
assert (S11 : (V10 2 3)%nat = (B 6 3)%nat). lca.
assert (S12 : (V10 3 0)%nat = (B 7 0)%nat). lca.
assert (S13 : (V10 3 1)%nat = (B 7 1)%nat). lca.
assert (S14 : (V10 3 2)%nat = (B 7 2)%nat). lca.
assert (S15 : (V10 3 3)%nat = (B 7 3)%nat). lca.
by_cell.
rewrite R0; rewrite S0; rewrite H. lca. lia. lia.
rewrite R1; rewrite S1; rewrite H. lca. lia. lia.
rewrite R2; rewrite S2; rewrite H. lca. lia. lia.
rewrite R3; rewrite S3; rewrite H. lca. lia. lia.
rewrite R4; rewrite S4; rewrite H. lca. lia. lia.
rewrite R5; rewrite S5; rewrite H. lca. lia. lia.
rewrite R6; rewrite S6; rewrite H. lca. lia. lia.
rewrite R7; rewrite S7; rewrite H. lca. lia. lia.
rewrite R8; rewrite S8; rewrite H. lca. lia. lia.
rewrite R9; rewrite S9; rewrite H. lca. lia. lia.
rewrite R10; rewrite S10; rewrite H. lca. lia. lia.
rewrite R11; rewrite S11; rewrite H. lca. lia. lia.
rewrite R12; rewrite S12; rewrite H. lca. lia. lia.
rewrite R13; rewrite S13; rewrite H. lca. lia. lia.
rewrite R14; rewrite S14; rewrite H. lca. lia. lia.
rewrite R15; rewrite S15; rewrite H. lca. lia. lia.
assert (R0 : (U11 0 0)%nat = (A 4 4)%nat). lca.
assert (R1 : (U11 0 1)%nat = (A 4 5)%nat). lca.
assert (R2 : (U11 0 2)%nat = (A 4 6)%nat). lca.
assert (R3 : (U11 0 3)%nat = (A 4 7)%nat). lca.
assert (R4 : (U11 1 0)%nat = (A 5 4)%nat). lca.
assert (R5 : (U11 1 1)%nat = (A 5 5)%nat). lca.
assert (R6 : (U11 1 2)%nat = (A 5 6)%nat). lca.
assert (R7 : (U11 1 3)%nat = (A 5 7)%nat). lca.
assert (R8 : (U11 2 0)%nat = (A 6 4)%nat). lca.
assert (R9 : (U11 2 1)%nat = (A 6 5)%nat). lca.
assert (R10 : (U11 2 2)%nat = (A 6 6)%nat). lca.
assert (R11 : (U11 2 3)%nat = (A 6 7)%nat). lca.
assert (R12 : (U11 3 0)%nat = (A 7 4)%nat). lca.
assert (R13 : (U11 3 1)%nat = (A 7 5)%nat). lca.
assert (R14 : (U11 3 2)%nat = (A 7 6)%nat). lca.
assert (R15 : (U11 3 3)%nat = (A 7 7)%nat). lca.
assert (S0 : (V11 0 0)%nat = (B 4 4)%nat). lca.
assert (S1 : (V11 0 1)%nat = (B 4 5)%nat). lca.
assert (S2 : (V11 0 2)%nat = (B 4 6)%nat). lca.
assert (S3 : (V11 0 3)%nat = (B 4 7)%nat). lca.
assert (S4 : (V11 1 0)%nat = (B 5 4)%nat). lca.
assert (S5 : (V11 1 1)%nat = (B 5 5)%nat). lca.
assert (S6 : (V11 1 2)%nat = (B 5 6)%nat). lca.
assert (S7 : (V11 1 3)%nat = (B 5 7)%nat). lca.
assert (S8 : (V11 2 0)%nat = (B 6 4)%nat). lca.
assert (S9 : (V11 2 1)%nat = (B 6 5)%nat). lca.
assert (S10 : (V11 2 2)%nat = (B 6 6)%nat). lca.
assert (S11 : (V11 2 3)%nat = (B 6 7)%nat). lca.
assert (S12 : (V11 3 0)%nat = (B 7 4)%nat). lca.
assert (S13 : (V11 3 1)%nat = (B 7 5)%nat). lca.
assert (S14 : (V11 3 2)%nat = (B 7 6)%nat). lca.
assert (S15 : (V11 3 3)%nat = (B 7 7)%nat). lca.
by_cell.
rewrite R0; rewrite S0; rewrite H. lca. lia. lia.
rewrite R1; rewrite S1; rewrite H. lca. lia. lia.
rewrite R2; rewrite S2; rewrite H. lca. lia. lia.
rewrite R3; rewrite S3; rewrite H. lca. lia. lia.
rewrite R4; rewrite S4; rewrite H. lca. lia. lia.
rewrite R5; rewrite S5; rewrite H. lca. lia. lia.
rewrite R6; rewrite S6; rewrite H. lca. lia. lia.
rewrite R7; rewrite S7; rewrite H. lca. lia. lia.
rewrite R8; rewrite S8; rewrite H. lca. lia. lia.
rewrite R9; rewrite S9; rewrite H. lca. lia. lia.
rewrite R10; rewrite S10; rewrite H. lca. lia. lia.
rewrite R11; rewrite S11; rewrite H. lca. lia. lia.
rewrite R12; rewrite S12; rewrite H. lca. lia. lia.
rewrite R13; rewrite S13; rewrite H. lca. lia. lia.
rewrite R14; rewrite S14; rewrite H. lca. lia. lia.
rewrite R15; rewrite S15; rewrite H. lca. lia. lia.
Qed.
