(** * SQIR: Quantum Programming in Coq **)

Require Import Bool.
Require Import Setoid.
Require Import Reals.
Require Import Psatz.
From VQC Require Import Matrix.
From VQC Require Import Qubit.
From VQC Require Import Multiqubit.

(** * A Small Quantum Intermediate Representation **)

Declare Scope com_scope.
Delimit Scope com_scope with com.
Open Scope com_scope.
Open Scope matrix_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope C_scope.

(* ================================================================= *)
(** ** Unitaries as gates *)

Inductive Gate : nat -> Set := 
| G_I     : nat -> Gate 1
| G_H     : nat -> Gate 1 
| G_X     : nat -> Gate 1
| G_Z     : nat -> Gate 1
| G_CNOT  : nat -> nat -> Gate 2.

(** All of our programs will assume a fixed set of qubit registers.
    [app U q1 q2] will apply U to the registers q1 and q2. *)

Inductive com : Set :=
| skip : com
| seq  : com -> com -> com
| app  : forall {n}, Gate n -> com.

Notation "p1 ; p2" := (seq p1 p2) (at level 50) : com_scope.
Definition SKIP  := skip.
Definition _I_ q := app (G_I q).
Definition _H_ q := app (G_H q).
Definition _X_ q := app (G_X q).
Definition _Z_ q := app (G_Z q).
Definition _CNOT_ q1 q2 := app (G_CNOT q1 q2).  

Arguments _I_ q%nat.
Arguments _H_ q%nat.
Arguments _X_ q%nat.
Arguments _Z_ q%nat.
Arguments _CNOT_ q1%nat q2%nat.

(** ** Denotation of Commands **)

(** Pad the given unitary with identities *)
Definition pad (n to dim : nat) (U : Unitary (2^n)) : Unitary (2^dim) :=
  if (to + n <=? dim)%nat 
  then I (2^to) ⊗ U ⊗ I (2^(dim - n - to)) 
  else Zero (2^dim) (2^dim).

Definition eval_cnot (dim m n: nat) : Unitary (2^dim) :=
  if (m + 1 =? n) then
    pad 2 m dim CNOT
  else if (n + 1 =? m) then
    pad 2 n dim NOTC
  else
    Zero _ _.

Definition geval {n} (dim : nat) (g : Gate n) : Unitary (2^dim) :=
  match g with
  | G_I j => pad n j dim (I 2)
  | G_H j => pad n j dim H
  | G_X j => pad n j dim X
  | G_Z j => pad n j dim Z
  | G_CNOT j k => eval_cnot dim j k
  end.

Fixpoint eval (dim : nat) (c : com) : Unitary (2^dim) :=
  match c with
  | skip    => I (2^dim)
  | app g   => geval dim g
  | c1 ; c2 => eval dim c2 × eval dim c1 
  end.

Arguments eval_cnot /.
Arguments geval /.
Arguments pad /.

(* ================================================================= *)
(** ** New Gates and Proofs *)

(** A simple program to construct a bell state *)
Definition BELL := _H_ 0; _CNOT_ 0 1. 

Lemma eval_BELL : (eval 2 BELL) × ∣0,0⟩ == bell.
Proof. 
  (* WORKED IN CLASS *)
  simpl. Msimpl.
  repeat rewrite Mmult_assoc.
  rewrite (kron_mixed_product H (I 2)).
  rewrite H0. rewrite Mmult_1_l.
  rewrite CNOTp1.
  reflexivity.
Qed.
  
Definition _CZ_ (q1 q2 : nat) := _H_ q2; _CNOT_ q1 q2 ; _H_ q2.

Lemma _CZ_CZ : (eval 2 (_CZ_ 0 1)) == CZ.
Proof.
  (* WORKED IN CLASS *)
  simpl. Msimpl.
  by_cell; autounfold with U_db; simpl; C_field_simplify; lca.
Qed.
  
(** *** SWAPing qubits **)

Definition _SWAP_ (q1 q2 : nat) : com :=
  _CNOT_ q1 q2; _CNOT_ q2 q1; _CNOT_ q1 q2. 

Lemma _SWAP_SWAP : eval 2 (_SWAP_ 0 1) == SWAP.
Proof. simpl. Msimpl. lma. Qed.

Lemma _SWAP_01 : eval 2 (_SWAP_ 0 1) × ∣0,1⟩ == ∣1,0⟩.  
Proof.
(* WORKED IN CLASS *)
  simpl; Msimpl.
  repeat rewrite Mmult_assoc.
  rewrite CNOT01.
  rewrite NOTC01.
  rewrite CNOT11.
  reflexivity.
Qed.
  
Lemma _SWAP_separable : forall (ψ ϕ : Qubit), eval 2 (_SWAP_ 0 1) × (ϕ ⊗ ψ) == (ψ ⊗ ϕ).  
Proof.
  intros.
  rewrite _SWAP_SWAP.
  lma.
Qed.

Lemma SWAP_gen : forall (a b c d : C), 
  eval 2 (_SWAP_ 0 1) × (a * ∣0,0⟩ + b * ∣0,1⟩ + c * ∣1,0⟩ + d * ∣1,1⟩) ==
  (a * ∣0,0⟩ + c * ∣0,1⟩ + b * ∣1,0⟩ + d * ∣1,1⟩).
Proof.
  (* WORKED IN CLASS *)
  intros. simpl. Msimpl.
  repeat rewrite Mmult_plus_dist_l.
  repeat rewrite Mscale_mult_dist_r.
  repeat rewrite Mmult_assoc.
  autorewrite with ket_db.
  lma.
Qed.  
  
(** **** Exercise: 2 stars, standard, recommended (bell_hadamard)  *)
(* Prove that adding a hadamard to the first element of a bell pair
   is the same as adding it to the second. *)
Lemma BellH : (eval 2 (BELL ; _H_ 0) × ∣0,0⟩ == eval 2 (BELL ; _H_ 1) × ∣0,0⟩)%nat. 
Proof. 
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **  Rewriting Circuits **)

Definition com_equiv (c1 c2 : com) := forall dim, eval dim c1 == eval dim c2.

Infix "≡" := com_equiv (at level 80): com_scope.

Lemma XX : forall q, _X_ q ; _X_ q ≡ _I_ q.
Proof.
  (* WORKED IN CLASS *)
  intros q dim. simpl.
  destruct (q + 1 <=? dim) eqn:E.  
  - apply Nat.leb_le in E. Msimpl.
    repeat rewrite kron_mixed_product.
    assert (XX : X × X == I 2) by lma.
    rewrite XX.
    reflexivity.
  - Msimpl.
    reflexivity.
Qed.

Lemma slide_X_target : _X_ 1 ; _CNOT_ 0 1 ≡ _CNOT_ 0 1; _X_ 1.
Proof. 
  intros [|[]]; simpl; try reflexivity.
  repeat rewrite Nat.sub_0_r.  
  Msimpl.
  assert (E : CNOT × (I 2 ⊗ X) == (I 2 ⊗ X) × CNOT) by lma.
  rewrite E.
  reflexivity.
Qed.

(** **** Exercise: 1 star, standard, recommended (HI)  *)
Lemma HI : forall q, _H_ q ; _I_ q ≡ _H_ q.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Lemma com_equiv_refl : forall c1, c1 ≡ c1. 
Proof. easy. Qed.

Lemma com_equiv_sym : forall c1 c2, c1 ≡ c2 -> c2 ≡ c1. 
Proof. easy. Qed.

Lemma com_equiv_trans : forall c1 c2 c3, c1 ≡ c2 -> c2 ≡ c3 -> c1 ≡ c3. 
Proof. 
  intros c1 c2 c3 H12 H23 dim. 
  unfold com_equiv in H12. 
  rewrite H12. easy. 
Qed.

Lemma seq_assoc : forall c1 c2 c3, ((c1 ; c2) ; c3) ≡ (c1 ; (c2 ; c3)).
Proof.
  intros c1 c2 c3 dim. simpl.
  rewrite Mmult_assoc. easy.
Qed.

Lemma seq_congruence : forall c1 c1' c2 c2',
    c1 ≡ c1' ->
    c2 ≡ c2' ->
    c1 ; c2 ≡ c1' ; c2'.
Proof.
  intros c1 c1' c2 c2' Ec1 Ec2 dim.
  simpl.
  unfold com_equiv in *.
  rewrite Ec1, Ec2.
  reflexivity.
Qed.

Add Relation com com_equiv 
  reflexivity proved by com_equiv_refl
  symmetry proved by com_equiv_sym
  transitivity proved by com_equiv_trans
  as com_equiv_rel.

Add Morphism seq 
  with signature (@com_equiv) ==> (@com_equiv) ==> (@com_equiv) as seq_mor.
Proof. intros x y H x0 y0 H0. apply seq_congruence; easy. Qed.

Lemma HXCXH_CZ : _H_ 1 ; _X_ 1; _CNOT_ 0 1 ; _X_ 1 ; _H_ 1 ≡ _CZ_ 0 1.
Proof.
  rewrite (seq_assoc (_ _ (_X_ 1))).
  rewrite <- slide_X_target.
  repeat rewrite seq_assoc.
  rewrite <- (seq_assoc (_X_ 1)).
  rewrite XX.
  rewrite <- seq_assoc.
  rewrite HI.
  rewrite <- seq_assoc.
  reflexivity.
Qed.  


(** ** Circuit Families **)

Fixpoint kron_n n {m1 m2} (A : Matrix m1 m2) : Matrix (m1^n) (m2^n) :=
  match n with
  | 0    => I 1
  | S n' => (kron_n n' A) ⊗ A
  end.

Fixpoint par_n (n : nat) (c : nat -> com) : com :=
  match n with
  | 0 => SKIP
  | S n' => c n'; par_n n' c
  end.

Lemma eval_S : forall n, eval (S n) (par_n n _H_) = eval n (par_n n _H_) ⊗ I 2.
Admitted.

Lemma nplus : forall n, eval n (par_n n _H_) × (kron_n n ∣0⟩) == kron_n n ∣+⟩.
Proof.
  induction n.
  - simpl. lma.
  - simpl.
    rewrite Nat.add_1_r.
    rewrite Nat.leb_refl.
    rewrite Nat.sub_0_r, Nat.sub_diag.
    simpl.
    Msimpl.
    rewrite eval_S.
    Msimpl. 
    rewrite IHn.
    rewrite H0.
    reflexivity.
Qed.

(** ** Superdense coding **)

Definition encode (b1 b2 : bool): com :=
  (if b2 then _X_ 0 else SKIP);
  (if b1 then _Z_ 0 else SKIP).

Definition decode : com :=
  _CNOT_ 0 1;
  _H_ 0.

Definition superdense (b1 b2 : bool) := BELL; encode b1 b2; decode.
  
Definition BtoN (b : bool) : nat := if b then 1 else 0.
Coercion BtoN : bool >-> nat.

Lemma superdense_correct : forall b1 b2, (eval 2 (superdense b1 b2)) × ∣ 0,0 ⟩ == ∣ b1,b2 ⟩.
Proof.
(* WORKED IN CLASS *)
  intros.
  simpl. Msimpl.
  destruct b1, b2.
  - simpl; Msimpl.    
    repeat rewrite Mmult_assoc.
    qubit_simplify.
    rewrite <- Mscale_kron_dist_l.
    by_cell; autounfold with U_db; simpl; C_field_simplify; lca.
  - simpl; Msimpl.    
    repeat rewrite Mmult_assoc.
    qubit_simplify.
    rewrite <- Mscale_kron_dist_l.
    by_cell; autounfold with U_db; simpl; C_field_simplify; lca.
  - simpl; Msimpl.    
    repeat rewrite Mmult_assoc.
    qubit_simplify.
    rewrite <- Mscale_kron_dist_l.
    by_cell; autounfold with U_db; simpl; C_field_simplify; lca.
  - simpl; Msimpl.    
    repeat rewrite Mmult_assoc.
    qubit_simplify.
    rewrite <- Mscale_kron_dist_l.
    by_cell; autounfold with U_db; simpl; C_field_simplify; lca.
Qed.

(* ================================================================= *)
(** ** Deutsch's Algorithm *)

Definition f0 : com := SKIP.
Definition f1 : com := _X_ 1.
Definition f2 : com := _CNOT_ 0 1.
Definition f3 : com := _CNOT_ 0 1; _X_ 1.

Definition deutsch (Uf : com) := _H_ 0; _H_ 1; Uf ; _H_ 0.

Definition constant (Uf : com) := Uf ≡ f0 \/ Uf ≡ f1. 

Definition balanced (Uf : com) := Uf ≡ f2 \/ Uf ≡ f3. 

Lemma deutsch_constant_correct :
  forall (Uf : com), constant Uf -> 
  exists ψ,((eval 2 (deutsch Uf)) × ∣0,1⟩) == (∣0⟩ ⊗ ψ).
Proof.
  intros Uf C.    
  destruct C as [E1|E2]; unfold deutsch; simpl.
  - evar (ψ : Qubit). exists ψ. Msimpl.
    specialize (E1 2%nat). rewrite E1.
    qubit_simplify.
    unfold ψ. reflexivity.
  - evar (ψ : Qubit). exists ψ. Msimpl.
    specialize (E2 2%nat). rewrite E2.
    simpl. Msimpl.
    qubit_simplify. 
    unfold ψ. reflexivity.
Qed.

(* Sun Jan 19 21:29:28 CST 2020 *)
