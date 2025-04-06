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

(* Define a function to create a polynomial with a root at a given point *)
Definition linear_poly (c : C) : Polynomial := [- c; C1].

(* Define a function to create a polynomial (x - c) *)
Definition x_minus_c (c : C) : Polynomial := linear_poly c.

(* Define a function to create a polynomial (c - x) *)
Definition c_minus_x (c : C) : Polynomial := [c; -C1].

Lemma Peval_nil : forall c, ([][[c]]) = C0.
Proof. 
  intros.
  reflexivity.
Qed.

(* Lemma to show that (x - c) evaluates to (a - c) at x = a *)
Lemma x_minus_c_eval : forall (a c : C),
  (x_minus_c c)[[a]] = a - c.
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
Lemma euclid_lemma : forall {d e : C} {p r : Polynomial},
  p *, [d; -C1] ≅ r *, [e; -C1] ->
  d = e \/ exists (q : Polynomial), q *, [d; -C1] ≅ r.
Proof.
  (* TODO: the polynomial theorem names collide with Coq.PArith *)

  intros d e p r Heq.
  destruct (Ceq_dec d e) as [| Hneq]; [auto | right].
  apply Cminus_eq_contra in Hneq.

  (* construct 1/(d - e) * (r - p) *)
  exists ([/ (d - e)] *, (r +, -,p)).
  rewrite Polynomial.Pmult_assoc.
  rewrite Polynomial.Pmult_plus_distr_r.
  unfold Popp.
  rewrite Polynomial.Pmult_assoc, Heq.
  rewrite <- Polynomial.Pmult_assoc.
  rewrite (Polynomial.Pmult_comm ([-C1])).
  rewrite Polynomial.Pmult_assoc.
  rewrite <- (Polynomial.Pmult_plus_distr_l r).
  simpl Polynomial.Pplus.
  replace (d + (((- C1) * e) + 0)) with (d - e) by lca.
  replace ((- C1) + ((- C1) * (- C1))) with C0 by lca.
  rewrite (p_Peq_compactify_p [d - e; C0]).

  unfold compactify.
  simpl prune.
  destruct (Ceq_dec 0 0); try easy.
  destruct (Ceq_dec (d - e) 0); try easy.
  simpl rev.

  rewrite (Polynomial.Pmult_comm r), <- Polynomial.Pmult_assoc.
  simpl Polynomial.Pmult at 2; rewrite Cplus_0_r.
  rewrite (Cinv_l _ Hneq).
  apply Pmult_1_l.
Qed.
