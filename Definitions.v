From Proof Require Import Real.
From Proof Require Import Complex.
From Proof Require Import Matrix.
From Proof Require Import Qubit.
From Proof Require Import Multiqubit.
Require Import List.
Import ListNotations.

Definition Determinant2 (A : Square 2) :=
  Cmult (A 0 0)%nat (A 1 1)%nat - Cmult (A 0 1)%nat (A 1 0)%nat.

Definition TensorProduct (w : Vector 4) : Prop := exists (u v : Vector 2), w == u ⊗ v.

Definition Entangled (q : Vector 4) : Prop := ~ (TensorProduct q).

Definition WF_Qubit_2 (ϕ : QState 2) : Prop := 
  (⎸(ϕ 0 0)%nat⎸² + ⎸(ϕ 1 0)%nat⎸² + ⎸(ϕ 2 0)%nat⎸² + ⎸(ϕ 3 0)%nat⎸² = 1)%C.

Definition WF_Unitary_2 {n} (U : Unitary n) := U × U † == I n.

Definition LinearlyIndependent2 (a b : Vector 2) : Prop := forall (c0 c1 : C),
  (c0 * a) + (c1 * b) == Zero 2 1 -> c0 = 0 /\ c1 = 0.

Definition LinearlyDependent2 (a b : Vector 2) : Prop := 
  exists (c : C), a == c * b \/ b == c * a.

Definition LinearlyIndependent4 (a b c d : Vector 4) : Prop := forall (c0 c1 c2 c3 : C),
  (c0 * a) + (c1 * b) + (c2 * c) + (c3 * d) == Zero 4 1 -> c0 = 0 /\ c1 = 0 /\ c2 = 0 /\ c3 = 0.

Definition Diagonal {n} (A : Square n) : Prop :=
  forall (i j : nat), (i < n)%nat -> (j < n)%nat -> i <> j -> A i j = 0.

Definition Diag2 (u0 u1 : C) : Square 2 :=
  l2M [[u0; 0];
          [0; u1]].

Definition Diag4 (u0 u1 u2 u3 : C) : Square 4 :=
  l2M [[u0; 0; 0; 0];
          [0; u1; 0; 0];
          [0; 0; u2; 0];
          [0; 0; 0; u3]].

Definition CU (U : Unitary 2) : Unitary 4 :=
  l2M [[1; 0; 0; 0];
          [0; 1; 0; 0];
          [0; 0; (U 0 0)%nat; (U 0 1)%nat];
          [0; 0; (U 1 0)%nat; (U 1 1)%nat]].

Definition CCU (U : Unitary 2) : Unitary 8 := 
  l2M [[1; 0; 0; 0; 0; 0; 0; 0];
          [0; 1; 0; 0; 0; 0; 0; 0];
          [0; 0; 1; 0; 0; 0; 0; 0];
          [0; 0; 0; 1; 0; 0; 0; 0];
          [0; 0; 0; 0; 1; 0; 0; 0];
          [0; 0; 0; 0; 0; 1; 0; 0];
          [0; 0; 0; 0; 0; 0; (U 0 0)%nat; (U 0 1)%nat];
          [0; 0; 0; 0; 0; 0; (U 1 0)%nat; (U 1 1)%nat]].

Definition Get_00 (U : Matrix 4 4) : Matrix 2 2 :=
  l2M [[(U 0 0)%nat ; (U 0 1)%nat] ;
          [(U 1 0)%nat ; (U 1 1)%nat]].

Definition Get_01 (U : Matrix 4 4) : Matrix 2 2 :=
  l2M [[(U 0 2)%nat ; (U 0 3)%nat] ;
          [(U 1 2)%nat ; (U 1 3)%nat]].

Definition Get_10 (U : Matrix 4 4) : Matrix 2 2 :=
  l2M [[(U 2 0)%nat ; (U 2 1)%nat] ;
          [(U 3 0)%nat ; (U 3 1)%nat]].

Definition Get_11 (U : Matrix 4 4) : Matrix 2 2 :=
  l2M [[(U 2 2)%nat ; (U 2 3)%nat] ;
          [(U 3 2)%nat ; (U 3 3)%nat]].

Definition Get8_00 (U : Square 8) : Square 4 :=
  l2M [[(U 0 0)%nat ; (U 0 1)%nat ; (U 0 2)%nat ; (U 0 3)%nat] ;
          [(U 1 0)%nat ; (U 1 1)%nat ; (U 1 2)%nat ; (U 1 3)%nat] ;
          [(U 2 0)%nat ; (U 2 1)%nat ; (U 2 2)%nat ; (U 2 3)%nat] ;
          [(U 3 0)%nat ; (U 3 1)%nat ; (U 3 2)%nat ; (U 3 3)%nat]].

Definition Get8_01 (U : Square 8) : Square 4 :=
  l2M [[(U 0 4)%nat ; (U 0 5)%nat ; (U 0 6)%nat ; (U 0 7)%nat] ;
          [(U 1 4)%nat ; (U 1 5)%nat ; (U 1 6)%nat ; (U 1 7)%nat] ;
          [(U 2 4)%nat ; (U 2 5)%nat ; (U 2 6)%nat ; (U 2 7)%nat] ;
          [(U 3 4)%nat ; (U 3 5)%nat ; (U 3 6)%nat ; (U 3 7)%nat]].

Definition Get8_10 (U : Square 8) : Square 4 :=
  l2M [[(U 4 0)%nat ; (U 4 1)%nat ; (U 4 2)%nat ; (U 4 3)%nat] ;
          [(U 5 0)%nat ; (U 5 1)%nat ; (U 5 2)%nat ; (U 5 3)%nat] ;
          [(U 6 0)%nat ; (U 6 1)%nat ; (U 6 2)%nat ; (U 6 3)%nat] ;
          [(U 7 0)%nat ; (U 7 1)%nat ; (U 7 2)%nat ; (U 7 3)%nat]].

Definition Get8_11 (U : Square 8) : Square 4:=
  l2M [[(U 4 4)%nat ; (U 4 5)%nat ; (U 4 6)%nat ; (U 4 7)%nat] ;
          [(U 5 4)%nat ; (U 5 5)%nat ; (U 5 6)%nat ; (U 5 7)%nat] ;
          [(U 6 4)%nat ; (U 6 5)%nat ; (U 6 6)%nat ; (U 6 7)%nat] ;
          [(U 7 4)%nat ; (U 7 5)%nat ; (U 7 6)%nat ; (U 7 7)%nat]].