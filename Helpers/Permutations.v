Require Import Lia.
Require Import QuantumLib.Permutations.
Require Import QuantumLib.Eigenvectors.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.Logic.Classical_Prop.
Require Import DiagonalHelpers.

(* characteristic polynomial helpers *)
(* Define a scaled identity matrix *)
Definition scaled_identity (n : nat) (c : C) : Square n :=
  fun x y =>
    if (x =? y) then c else C0.

(* Define the characteristic polynomial using scaled_identity and Mminus *)
Definition char_poly {n} (A : Square n) (x : C) : C :=
  Determinant (Mminus (scaled_identity n x) A).

(* Conjugating a matrix with a unitary preserves the characteristic polynomial *)
Lemma char_poly_similarity : forall {n} (A B U : Square n) x,
  WF_Unitary U -> U × A × U† = B -> char_poly A x = char_poly B x.
Proof.
Admitted.

Fixpoint prod_f (f : nat -> C) (n : nat) : C :=
  match n with
  | 0 => C1 (* The product over an empty range is 1 *)
  | S n' => (f n') * (prod_f f n') (* Multiply the current value with the rest *)
  end.

Lemma char_poly_diagonal : forall {n} (D : Square n),
  WF_Diagonal D -> forall x, char_poly D x = prod_f (fun i => x - D i i) n.
Proof.
Admitted.

Lemma poly_roots_perm : forall {n} (f g : nat -> C),
  (forall x, prod_f (fun i => x - f i) n = prod_f (fun i => x - g i) n) ->
  exists (σ : nat -> nat), permutation n σ /\ forall (i : nat), f i = g (σ i).
Proof.
Admitted.

Lemma perm_eigenvalues : forall {n} (D E U : Square n),
  WF_Unitary U -> WF_Diagonal D -> WF_Diagonal E -> U × D × U† = E ->
  exists (σ : nat -> nat),
    permutation n σ /\ forall (i : nat), D i i = E (σ i) (σ i).
Proof.
  intros n D E U WF_U WF_D WF_E H_conj.
  (* assert (H_conj' : U × D × U† = E).
{ rewrite <- H_conj. reflexivity. } *)
  (* Step 1: Show that D and E have the same characteristic polynomial. *)
  assert (Hchar : forall x, char_poly D x = char_poly E x).
  {
    intros x.
    apply (char_poly_similarity D E U x); assumption.
  }
  
  assert (Hprod : forall x : C, prod_f (fun i => x - D i i) n = prod_f (fun i => x - E i i) n).
  {
    intros x.
    rewrite <- (char_poly_diagonal D WF_D x).
    rewrite <- (char_poly_diagonal E WF_E x).
    apply Hchar.
  }

  apply poly_roots_perm in Hprod.
  destruct Hprod as [σ [Hperm Heq]].
  exists σ.
  split. assumption.
  intros i.
  apply Heq.
Qed.

(* Lemma perm_eigenvalues : forall {n} (U D D' : Square n),
  WF_Unitary U -> WF_Diagonal D -> WF_Diagonal D' -> U × D × U† = D' ->
  exists (σ : nat -> nat),
    permutation n σ /\ forall (i : nat), D i i = D' (σ i) (σ i).
Proof.
Admitted. *)

(* To equate the eigenvalues of two matrices, we often need equality of matrices
   up to some permutation. This lemma allows us to take the existence of a
   permutation on 4 elements and decompose it into the 24 possible cases. *)
Lemma permutation_4_decomp : forall (σ : nat -> nat),
  permutation 4 σ -> (
    (σ 0 = 0 /\ σ 1 = 1 /\ σ 2 = 2 /\ σ 3 = 3) \/
    (σ 0 = 0 /\ σ 1 = 1 /\ σ 2 = 3 /\ σ 3 = 2) \/
    (σ 0 = 0 /\ σ 1 = 2 /\ σ 2 = 1 /\ σ 3 = 3) \/
    (σ 0 = 0 /\ σ 1 = 2 /\ σ 2 = 3 /\ σ 3 = 1) \/
    (σ 0 = 0 /\ σ 1 = 3 /\ σ 2 = 1 /\ σ 3 = 2) \/
    (σ 0 = 0 /\ σ 1 = 3 /\ σ 2 = 2 /\ σ 3 = 1) \/
    (σ 0 = 1 /\ σ 1 = 0 /\ σ 2 = 2 /\ σ 3 = 3) \/
    (σ 0 = 1 /\ σ 1 = 0 /\ σ 2 = 3 /\ σ 3 = 2) \/
    (σ 0 = 1 /\ σ 1 = 2 /\ σ 2 = 0 /\ σ 3 = 3) \/
    (σ 0 = 1 /\ σ 1 = 2 /\ σ 2 = 3 /\ σ 3 = 0) \/
    (σ 0 = 1 /\ σ 1 = 3 /\ σ 2 = 0 /\ σ 3 = 2) \/
    (σ 0 = 1 /\ σ 1 = 3 /\ σ 2 = 2 /\ σ 3 = 0) \/
    (σ 0 = 2 /\ σ 1 = 0 /\ σ 2 = 1 /\ σ 3 = 3) \/
    (σ 0 = 2 /\ σ 1 = 0 /\ σ 2 = 3 /\ σ 3 = 1) \/
    (σ 0 = 2 /\ σ 1 = 1 /\ σ 2 = 0 /\ σ 3 = 3) \/
    (σ 0 = 2 /\ σ 1 = 1 /\ σ 2 = 3 /\ σ 3 = 0) \/
    (σ 0 = 2 /\ σ 1 = 3 /\ σ 2 = 0 /\ σ 3 = 1) \/
    (σ 0 = 2 /\ σ 1 = 3 /\ σ 2 = 1 /\ σ 3 = 0) \/
    (σ 0 = 3 /\ σ 1 = 0 /\ σ 2 = 1 /\ σ 3 = 2) \/
    (σ 0 = 3 /\ σ 1 = 0 /\ σ 2 = 2 /\ σ 3 = 1) \/
    (σ 0 = 3 /\ σ 1 = 1 /\ σ 2 = 0 /\ σ 3 = 2) \/
    (σ 0 = 3 /\ σ 1 = 1 /\ σ 2 = 2 /\ σ 3 = 0) \/
    (σ 0 = 3 /\ σ 1 = 2 /\ σ 2 = 0 /\ σ 3 = 1) \/
    (σ 0 = 3 /\ σ 1 = 2 /\ σ 2 = 1 /\ σ 3 = 0)
  )%nat.
Proof.
  assert (perm_values : forall {n} (σ : nat -> nat),
    permutation n σ ->
      let N : Ensemble nat := (fun x => x < n)%nat in
      forall (i : nat),
        (i < n)%nat ->
          let Image := (fun x => exists (j : nat), (j < i)%nat /\ σ j = x) in
          In nat (Setminus nat N Image) (σ i)).
  {
    intros n σ permutation_σ N i i_lt_n Image.
    unfold Setminus, In, N, Image.
    split.
    {
      destruct permutation_σ as [σ_inv H].
      apply H.
      assumption.
    }
    {
      apply all_not_not_ex.
      intros m [m_lt_i σm_eq_σi].
      assert (m_lt_n : (m < n)%nat) by lia.
      pose proof (
        permutation_is_injective n σ permutation_σ m i m_lt_n i_lt_n σm_eq_σi
      ) as m_eq_i.
      lia.
    }
  }
  intros σ permutation_σ.
  pose proof (perm_values 4%nat σ permutation_σ) as perm_helper.

  specialize (perm_helper 0%nat) as perm_helper_0.
  destruct perm_helper_0 as [σ0_lt_4 _]; auto; unfold In in σ0_lt_4.

  specialize (perm_helper 1%nat) as perm_helper_1.
  destruct perm_helper_1 as [σ1_lt_4 help0]; auto; unfold In in σ1_lt_4.
  unfold In in help0.
  pose proof (not_ex_all_not _ _ help0) as helper0; clear help0.
  specialize (helper0 0%nat) as σ0_neq_σ1; clear helper0.
  revert σ0_neq_σ1; simpl; intro σ0_neq_σ1.
  apply not_and_or in σ0_neq_σ1.
  destruct σ0_neq_σ1 as [absurd | σ0_neq_σ1]. lia.

  specialize (perm_helper 2%nat) as perm_helper_2.
  destruct perm_helper_2 as [σ2_lt_4 help1]; auto; unfold In in σ2_lt_4.
  unfold In in help1.
  pose proof (not_ex_all_not _ _ help1) as helper1; clear help1.
  specialize (helper1 0%nat) as σ0_neq_σ2.
  specialize (helper1 1%nat) as σ1_neq_σ2; clear helper1.
  revert σ0_neq_σ2 σ1_neq_σ2. simpl. intros σ0_neq_σ2 σ1_neq_σ2.
  apply not_and_or in σ0_neq_σ2, σ1_neq_σ2.
  destruct σ0_neq_σ2 as [absurd | σ0_neq_σ2]. lia.
  destruct σ1_neq_σ2 as [absurd | σ1_neq_σ2]. lia.

  specialize (perm_helper 3%nat) as perm_helper_3.
  destruct perm_helper_3 as [σ3_lt_4 help2]; auto; unfold In in σ3_lt_4.
  unfold In in help2.
  pose proof (not_ex_all_not _ _ help2) as helper2; clear help2.
  specialize (helper2 0%nat) as σ0_neq_σ3.
  specialize (helper2 1%nat) as σ1_neq_σ3.
  specialize (helper2 2%nat) as σ2_neq_σ3; clear helper2.
  revert σ0_neq_σ3 σ1_neq_σ3 σ2_neq_σ3. simpl. intros σ0_neq_σ3 σ1_neq_σ3 σ2_neq_σ3.
  apply not_and_or in σ0_neq_σ3, σ1_neq_σ3, σ2_neq_σ3.
  destruct σ0_neq_σ3 as [absurd | σ0_neq_σ3]. lia.
  destruct σ1_neq_σ3 as [absurd | σ1_neq_σ3]. lia.
  destruct σ2_neq_σ3 as [absurd | σ2_neq_σ3]. lia.
  destruct (σ 0%nat).
  {
    destruct (σ 1%nat); try contradiction.
    destruct n.
    {
      destruct (σ 2%nat); try contradiction.
      destruct n; try contradiction.
      destruct n.
      {
        destruct (σ 3%nat); try contradiction.
        destruct n; try contradiction.
        destruct n; try contradiction.
        destruct n; try lia.
      }
      {
        destruct n; try lia.
      }
    }
    {
      destruct n.
      {
        destruct (σ 2%nat); try contradiction.
        destruct n.
        {
          destruct (σ 3%nat); try contradiction.
          destruct n; try contradiction.
          destruct n; try contradiction.
          destruct n; try lia.
        }
        {
          destruct n; try contradiction.
          destruct n; try lia.
        }
      }
      {
        destruct n; try lia.
      }
    }
  }
  {
    destruct n.
    {
      destruct (σ 1%nat).
      {
        destruct (σ 2%nat); try contradiction.
        destruct n; try contradiction.
        destruct n.
        {
          destruct (σ 3%nat); try contradiction.
          destruct n; try contradiction.
          destruct n; try contradiction.
          destruct n; try lia.
        }
        {
          destruct n; try lia.
        }
      }
      {
        destruct n; try contradiction.
        destruct n.
        {
          destruct (σ 2%nat); try contradiction.
          {
            destruct (σ 3%nat); try contradiction.
            destruct n; try contradiction.
            destruct n; try contradiction.
            destruct n; try lia.
          }
          {
            destruct n; try contradiction.
            destruct n; try contradiction.
            destruct n; try lia.
          }
        }
        {
          destruct n; try lia.
        }
      }
    }
    {
      destruct n.
      {
        destruct (σ 1%nat).
        {
          destruct (σ 2%nat); try contradiction.
          destruct n.
          {
            destruct (σ 3%nat); try contradiction.
            destruct n; try contradiction.
            destruct n; try contradiction.
            destruct n; try lia.
          }
          {
            destruct n; try contradiction.
            destruct n; try lia.
          }
        }
        {
          destruct n.
          {
            destruct (σ 2%nat).
            {
              destruct (σ 3%nat); try contradiction.
              destruct n; try contradiction.
              destruct n; try contradiction.
              destruct n; try lia.
            }
            {
              destruct n; try contradiction.
              destruct n; try contradiction.
              destruct n; try lia.
            }
          }
          {
            destruct n; try contradiction.
            destruct n; try lia.
          }
        }
      }
      {
        destruct n. 2: { exfalso. lia. }
        destruct (σ 1%nat).
        {
          destruct (σ 2%nat); try contradiction.
          destruct n.
          {
            destruct (σ 3%nat); try contradiction.
            destruct n; try contradiction.
            destruct n; try lia.
          }
          {
            destruct n; try lia.
          }
        }
        {
          destruct n.
          {
            destruct (σ 2%nat).
            {
              destruct (σ 3%nat); try contradiction.
              destruct n; try contradiction.
              destruct n; try lia.
            }
            {
              destruct n; try contradiction.
              destruct n; try lia.
            }
          }
          {
            destruct n; try lia.
          }
        }
      }
    }
  }
Qed.

(* Helper tactic to quickly destruct cases and assign them a uniform name *)
Ltac destruct_disjunctions name :=
  match goal with
  | [ H : _ \/ _ |- _ ] => destruct H as [name | H]; destruct_disjunctions name
  | _ => idtac
  end.
