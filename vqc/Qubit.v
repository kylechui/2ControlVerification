(** * Qubit: The Building Blocks of Quantum Computing *)

From VQC Require Export Matrix.
Require Import FunctionalExtensionality.
Require Import Bool.
Require Import List.
Import ListNotations.

(* ################################################################# *)
(** * Qubits *)

(** Let's start with the basic building block of quantum computing :
    The qubit *)

Notation Qubit := (Vector 2).

Definition qubit0 : Qubit := l2V [1;0]. 
Definition qubit1 : Qubit := l2V [0;1].

Notation "∣ 0 ⟩" := qubit0.
Notation "∣ 1 ⟩" := qubit1.

Arguments qubit0 _ _ /.
Arguments qubit1 _ _ /.

(** The nice thing about these basis qubits is that we can use them 
    to express any qubit. *)
Lemma qubit_decomposition : forall (ϕ : Qubit), exists (α β : C), ϕ == α * ∣0⟩ + β * ∣1⟩.
Proof.
  (* WORKED IN CLASS *)
  intros.
  exists (ϕ 0 0)%nat, (ϕ 1 0)%nat.
  lma.
Qed.
  
(** ⎸α⎸² + ⎸β⎸² = 1. *)
Definition WF_Qubit (ϕ : Qubit) : Prop := (⎸(ϕ 0 0)%nat⎸² + ⎸(ϕ 1 0)%nat⎸² = 1)%C.

(** Note that this is equivalent to saying that [⟨ϕ,ϕ⟩ = 1],
    which partially explains the notation for qubits below. *)

(** **** Exercise: 2 stars, standard, recommended (WF_Qubit_alt)  

    Prove this statement. *)
Theorem WF_Qubit_alt : forall ϕ : Qubit, WF_Qubit ϕ <-> ϕ† × ϕ == I 1.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** A brief aside : Emacs and other text editors, as well as a famous
    xkcd comic and any well-developed aethestics, don't like seeing
    left angle braces without corresponding right angle braces. (Blame
    here goes to Paul Dirac.) Since emacs' auto-indentation will
    probably go out of whack at this point in the file, I recommend
    disabling it via M-x electric-indent-mode. *) 

(** With that done, let's show that our two "basis" qubits are indeed
    proper qubits *)

Lemma WF_qubit0 : WF_Qubit ∣0⟩. Proof. lca. Qed.
Lemma WF_qubit1 : WF_Qubit ∣1⟩. Proof. lca. Qed.

(* ################################################################# *)
(** * Unitaries *)

(** The standard way of operating on a vector is multiplying it by a
    matrix. If A is an n × n matrix and v is a n-dimensional vector,
    then A v is another n-dimensional vector.

    In the quantum case, we want to restrict A so that for any qubit
    ϕ, A ϕ is also a valid qubit. Let's try to figure out what this
    restriction will look like in practice.

 *)

Lemma valid_qubit_function : exists (P : Matrix 2 2 -> Prop),
  forall (A : Matrix 2 2) (ϕ : Qubit), 
  P A -> WF_Qubit ϕ -> WF_Qubit (A × ϕ).
Proof.
  (* WORKED IN CLASS *)
  eexists.
  intros A ϕ p Q.
  rewrite WF_Qubit_alt. 
  rewrite WF_Qubit_alt in Q. 
  unfold inner_product.
  rewrite Mmult_adjoint. 
  rewrite Mmult_assoc.
  rewrite <- (Mmult_assoc (A†)).
  assert (P: A† × A = I 2). apply p.
  rewrite P.
  rewrite Mmult_1_l.
  apply Q.
Qed.
  
(** We will call these matrices _unitary_ for preserving the unit
    inner product *)

Notation Unitary n := (Matrix n n).

Definition WF_Unitary {n} (U : Unitary n) := U † × U == I n. 

(** We'll start with five useful unitaries: The Pauli matrices
    I, X, Y and Z and the Hadamard H. *)

Definition X : Unitary 2 := l2M [[0;1];
                                 [1;0]].

Lemma WF_X : WF_Unitary X. Proof. lma. Qed.

Lemma X0 : X × ∣0⟩ == ∣1⟩. Proof. lma. Qed.
Lemma X1 : X × ∣1⟩ == ∣0⟩. Proof. lma. Qed.

(* Sooner: Rename unitaries to lowercase so gates can be upper case. *)
Definition Y : Unitary 2 := l2M [[0; -i];
                                 [i;  0]].

Lemma WF_Y : WF_Unitary Y. Proof. lma. Qed.

Lemma Y0 : Y × ∣0⟩ == i * ∣1⟩. Proof. lma. Qed.
Lemma Y1 : Y × ∣1⟩ == -i * ∣0⟩. Proof. lma. Qed.


Definition Z : Unitary 2 := l2M [[1; 0];
                                 [0; -(1)]].

Lemma WF_Z : WF_Unitary Z. Proof. lma. Qed.

Lemma Z0 : Z × ∣0⟩ == ∣0⟩. Proof. lma. Qed.
Lemma Z1 : Z × ∣1⟩ == -(1) * ∣1⟩. Proof. lma. Qed.

Definition H : Unitary 2 := l2M [[/√2; /√2];
                                 [/√2;-/√2]].

Lemma WF_H : WF_Unitary H. 
Proof. 
  unfold WF_Unitary, H; autounfold with U_db; simpl.
  by_cell; try lca.
  - apply c_proj_eq; simpl; try lra.
    field_simplify.
    repeat rewrite pown_sqrt; simpl; lra.
    nonzero.
  - apply c_proj_eq; simpl; try lra.
    field_simplify.
    repeat rewrite pown_sqrt; simpl; lra.
    nonzero.
Qed.

Definition q_plus : Qubit := l2V [/√2; /√2].
Definition q_minus : Qubit := l2V [/√2; -/√2]. 

Arguments q_plus _ _ /.
Arguments q_minus _ _ /.

Notation "∣ + ⟩" := q_plus.
Notation "∣ - ⟩" := q_minus.

Lemma H0 : H × ∣0⟩ == ∣+⟩. Proof. lma. Qed.
Lemma H1 : H × ∣1⟩ == ∣-⟩. Proof. lma. Qed.

(** It's worth noticing that if we apply a Hadamard twice, we get our
    initial state back: *)

Lemma Hplus : H × ∣+⟩ == ∣0⟩.
Proof.
  unfold H, Mmult, q_plus; simpl.
  by_cell; simpl; try lca.
  C_field_simplify. 
  lca.
Qed.

Lemma Hminus : H × ∣-⟩ == ∣ 1 ⟩.
Proof. 
  unfold H, Mmult, q_minus; simpl.
  by_cell; C_field_simplify; lca.
Qed.

(** **** Exercise: 2 stars, standard, recommended (Htwice)  

    Prove the general form of double Hadamard application *)
Theorem Htwice : forall ϕ : Qubit, H × (H × ϕ) == ϕ.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** * Measurement **)

(** Measurement is a _probabilistic_ operation on a qubit. Since
    there are (generally) multiple possible outcomes of a measurement,
    we will represent measurement as a relation. 

    Note that some measurements, those with 0 probability, will never occur.
*)

Inductive measure : Qubit -> (R * Qubit) -> Prop :=
| measure0 : forall (ϕ : Qubit), measure ϕ (⎸ϕ 0%nat 0%nat ⎸², ∣0⟩)
| measure1 : forall (ϕ : Qubit), measure ϕ (⎸ϕ 1%nat 0%nat ⎸², ∣1⟩). 

(** **** Exercise: 3 stars, standard, optional (measure_sum)  

    State and prove that the sum of the measure outcomes for a valid qubit will always be 1. 
    Hint: Compare the definitions of norm2 and inner_product. *)
(* FILL IN HERE *)

(** [] *)

Lemma measure0_idem : forall ϕ p, measure ∣0⟩ (p, ϕ) -> p <> 0%R -> ϕ = ∣0⟩.
Proof.
  (* WORKED IN CLASS *)
  intros ϕ p M NZ.
  inversion M; subst.
  - reflexivity.
  - contradict NZ. lra.
Qed.
  
(** **** Exercise: 1 star, standard, recommended (measure1_idem)  *)
Lemma measure1_idem : forall ϕ p, measure ∣1⟩ (p, ϕ) -> p <> 0%R -> ϕ = ∣1⟩.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Lemma measure_plus : forall ϕ p, measure ∣+⟩ (p, ϕ) -> p = (1/2)%R.
Proof.
  intros ϕ p M.
  inversion M; subst. 
  - R_field.
  - R_field.
Qed.

(** **** Exercise: 2 stars, standard, recommended (measure_minus)  *)
Lemma measure_minus : forall ϕ p, measure ∣-⟩ (p, ϕ) -> p = (1/2)%R.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

#[export] Hint Unfold H X Y Z qubit0 qubit1 q_plus q_minus : U_db. 

(* *)

(* Sun Jan 19 21:29:28 CST 2020 *)
