Require Import QuantumLib.Complex.
Require Import QuantumLib.Polynomial.
Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.
Require Import QuantumLib.Eigenvectors.
Require Import MatrixHelpers.
Require Import DiagonalHelpers.
Require Import UnitaryHelpers.
Require Import Permutations.

(* Open the polynomial scope *)
Local Open Scope poly_scope.

(* Define a notation for polynomial evaluation *)
Notation "p @ x" := (Peval p x) (at level 10) : poly_scope.

(* Define a function to create a polynomial with a root at a given point *)
Definition linear_poly (c : C) : Polynomial := [- c; C1].

(* Define a function to create a polynomial (x - c) *)
Definition x_minus_c (c : C) : Polynomial := linear_poly c.

(* Define a function to create a polynomial (c - x) *)
Definition c_minus_x (c : C) : Polynomial := [c; -C1].

Lemma Peval_nil : forall c, ([] @ c) = C0.
Proof. 
  intros.
  reflexivity.
Qed.

(* Lemma to show that (x - c) evaluates to (a - c) at x = a *)
Lemma x_minus_c_eval : forall (a c : C),
  (x_minus_c c) @ a = a - c.
Proof.
  intros a c.
  unfold x_minus_c, linear_poly.
  simpl.
  repeat rewrite cons_eval.
  rewrite Peval_nil.
  lca.
Qed.

(* Define a function to create a product of (x - c_i) terms *)
Fixpoint prod_x_minus_c (cs : list C) : Polynomial :=
  match cs with
  | [] => [C1]  (* Empty product is 1 *)
  | c :: cs' => (x_minus_c c) *, (prod_x_minus_c cs')
  end.

(* Define a function to create a product of (c_i - x) terms *)
Fixpoint prod_c_minus_x (cs : list C) : Polynomial :=
  match cs with
  | [] => [C1]  (* Empty product is 1 *)
  | c :: cs' => (c_minus_x c) *, (prod_c_minus_x cs')
  end.

(* Define a big product function for complex numbers *)
Fixpoint big_prod (f : nat -> C) (n : nat) : C :=
  match n with
  | 0 => C1  (* Empty product is 1 *)
  | S n' => (f n') * (big_prod f n')
  end.

(* Lemma 1.1 (Euclid's Lemma) *)
Lemma euclid_lemma : forall (n : nat) (d e : C) (p r : Polynomial),
  p *, c_minus_x d = r *, c_minus_x e  -> 
  d = e \/ exists (q : Polynomial), q *, c_minus_x d = r.
Proof.
Admitted.

(* Lemma poly_root_in_list : forall (n : nat) (d : C) (e_list : list C),
  length e_list = n ->
  (prod_x_minus_c e_list) @ d = C0 ->
  exists k, nth k e_list C0 = d.
Admitted. *)
