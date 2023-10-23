(** * Matrix: Lightweight Complex Matrices *)

Require Import Psatz.
Require Import Setoid.
Require Import Arith.
Require Import Bool.
Require Import Program.
Require Import List.
Import ListNotations.
From Proof Require Export Complex.

(** * Matrix Definitions and Equivalence **)

Declare Scope matrix_scope.
Delimit Scope matrix_scope with M.
Open Scope matrix_scope.
Open Scope nat_scope.

(** We define a _matrix_ as a simple function from to nats
    (corresponding to a row and a column) to a complex number. In many
    contexts it would make sense to parameterize matrices over numeric
    types, but our use case is fairly narrow, so matrices of complex
    numbers will suffice. *)
    
Definition Matrix (m n : nat) := nat -> nat -> C.

Bind Scope matrix_scope with Matrix.
Notation Vector n := (Matrix n 1).
Notation Square n := (Matrix n n).

(* Lists to Vectors / Matrices. *)
Definition l2V (l : list C) : Vector (length l) :=
  (fun x y => nth x l 0%R).

Definition l2M (l : list (list C)) : Matrix (length l) (length (hd [] l)) :=
  (fun x y => nth y (nth x l []) 0%R).

Arguments l2V l i j /.
Arguments l2M l i j /.

(** Note that the dimensions of the matrix aren't being used here. In
    practice, a matrix is simply a function on any two nats. However,
    we will used these dimensions to define equality, as well as the
    multiplication and kronecker product operations to follow. *)

Definition mat_equiv {m n : nat} (A B : Matrix m n) : Prop := 
  forall i j, i < m -> j < n -> A i j = B i j.

Infix "==" := mat_equiv (at level 80).

(** Let's prove some important notions about matrix equality. *)

Lemma mat_equiv_refl : forall {m n} (A : Matrix m n), A == A.
Proof. intros m n A i j Hi Hj. reflexivity. Qed.

Lemma mat_equiv_sym : forall {m n} (A B : Matrix m n), A == B -> B == A.
Proof.
  intros m n A B H i j Hi Hj.
  rewrite H; easy.
Qed.

Lemma mat_equiv_trans : forall {m n} (A B C : Matrix m n),
    A == B -> B == C -> A == C.
Proof.
  intros m n A B C HAB HBC i j Hi Hj.
  rewrite HAB; trivial.
  apply HBC; easy.
Qed.

Add Parametric Relation m n : (Matrix m n) (@mat_equiv m n)
  reflexivity proved by mat_equiv_refl
  symmetry proved by mat_equiv_sym
  transitivity proved by mat_equiv_trans
    as mat_equiv_rel.

(** Now we can use matrix equivalence to rewrite! *)

Lemma mat_equiv_trans2 : forall {m n} (A B C : Matrix m n),
    A == B -> A == C -> B == C.
Proof.
  intros m n A B C HAB HAC.
  rewrite <- HAB.
  apply HAC.
Qed.

(* ################################################################# *)
(** * Basic Matrices and Operations *)

Close Scope nat_scope.
Open Scope C_scope.

(** Because we will use these so often, it is good to have them in matrix scope. *)
Notation "m =? n" := (Nat.eqb m n) (at level 70) : matrix_scope.
Notation "m <? n" := (Nat.ltb m n) (at level 70) : matrix_scope.
Notation "m <=? n" := (Nat.leb m n) (at level 70) : matrix_scope.

Open Scope matrix_scope.

Definition I (n : nat) : Matrix n n := fun i j => if (i =? j)%nat then 1 else 0.

Definition Zero (m n : nat) : Matrix m n := fun _ _ => 0. 

Definition Mscale {m n : nat} (c : C) (A : Matrix m n) : Matrix m n := 
  fun i j => c * A i j.

Definition Mplus {m n : nat} (A B : Matrix m n) : Matrix m n :=
  fun i j => A i j + B i j.

Infix "+" := Mplus (at level 50, left associativity) : matrix_scope.
Infix "*" := Mscale (at level 40, left associativity) : matrix_scope.

Lemma Mplus_assoc : forall {m n} (A B C : Matrix m n), (A + B) + C == A + (B + C).
Proof.
  intros m n A B C i j Hi Hj.
  unfold Mplus.
  lca.
Qed.

Lemma Mplus_comm : forall {m n} (A B : Matrix m n), A + B == B + A.
Proof.
  (* WORKED IN CLASS *)
  intros m n A B i j Hi Hj.
  unfold Mplus.
  lca.
Qed.
  
Lemma Mplus_0_l : forall {m n} (A : Matrix m n), Zero m n + A == A. 
Proof.
  (* WORKED IN CLASS *)
  intros m n A i j Hi Hj.
  unfold Zero, Mplus.
  lca.
Qed.
  
(* Let's try one without unfolding definitions. *)
Lemma Mplus_0_r : forall {m n} (A : Matrix m n), A + Zero m n == A. 
Proof.
  (* WORKED IN CLASS *)
  intros m n A.
  rewrite Mplus_comm.
  apply Mplus_0_l.
Qed.
  
Lemma Mplus3_first_try : forall {m n} (A B C : Matrix m n), (B + A) + C == A + (B + C).
Proof.
  (* WORKED IN CLASS *)
  intros m n A B C.
  Fail rewrite (Mplus_comm B A).
Abort.
  
(** What went wrong? While we can rewrite using [==], we don't
    know that [+] _respects_ [==]. That is, we don't know that if 
    [A == A'] and [B == B'] then [A + B == A' + B'] -- or at least, we
    haven't told Coq that.

   Let's take a look at an example of a unary function that doesn't
   respect [==] *)

Definition shift_right {m n} (A : Matrix m n) (k : nat) : Matrix m n :=
  fun i j => A i (j + k)%nat.

Lemma shift_unequal : exists m n (A A' : Matrix m n) (k : nat),
    A == A' /\ ~ (shift_right A k == shift_right A' k). 
Proof.
  set (A := (fun i j => if (j <? 2)%nat then 1 else 0) : Matrix 2 2).
  set (A' := (fun i j => if (j <? 3)%nat then 1 else 0) : Matrix 2 2).  
  exists _, _, A, A', 1%nat.
  split.
  - intros i j Hi Hj.
    unfold A, A'.  
    destruct j as [|[|]]; destruct i as [|[|]]; trivial; lia.
  - intros F.
    assert (1 < 2)%nat by lia.
    specialize (F _ _ H H).
    unfold A, A', shift_right in F.
    simpl in F.
    inversion F; lra.
Qed.

(** Let's show that [+] does respect [==] *)

Lemma Mplus_compat : forall {m n} (A B A' B' : Matrix m n),
    A == A' -> B == B' -> A + B == A' + B'.
Proof.
  (* WORKED IN CLASS *)
  intros m n A B A' B' HA HB.
  intros i j Hi Hj.
  unfold Mplus.
  rewrite HA by lia.
  rewrite HB by lia.
  reflexivity.
Qed.
    
Add Parametric Morphism m n : (@Mplus m n)
  with signature mat_equiv ==> mat_equiv ==> mat_equiv as Mplus_mor.
Proof.
  intros A A' HA B B' HB.
  apply Mplus_compat; easy.
Qed.

(** Now let's return to that lemma... *)

Lemma Mplus3 : forall {m n} (A B C : Matrix m n), (B + A) + C == A + (B + C).
Proof.
  (* WORKED IN CLASS *)
  intros m n A B C.
  rewrite (Mplus_comm B A).
  apply Mplus_assoc.
Qed.

(** Mscale is similarly compatible with [==], but requires a slightly
    different lemma: *)

Lemma Mscale_compat : forall {m n} (c c' : C) (A A' : Matrix m n),
    c = c' -> A == A' -> c * A == c' * A'.
Proof.
  intros m n c c' A A' Hc HA.
  intros i j Hi Hj.
  unfold Mscale.
  rewrite Hc, HA; easy.
Qed.

Add Parametric Morphism m n : (@Mscale m n)
  with signature eq ==> mat_equiv ==> mat_equiv as Mscale_mor.
Proof.
  intros; apply Mscale_compat; easy.
Qed.

(** Let's move on to the more interesting matrix functions: *)

Definition trace {n : nat} (A : Square n) : C := 
  Csum (fun x => A x x) n.

Definition Mmult {m n o : nat} (A : Matrix m n) (B : Matrix n o) : Matrix m o := 
  fun x z => Csum (fun y => A x y * B y z)%C n.

Open Scope nat_scope.

Definition kron {m n o p : nat} (A : Matrix m n) (B : Matrix o p) : 
  Matrix (m*o) (n*p) :=
  fun x y => Cmult (A (x / o) (y / p)) (B (x mod o) (y mod p)).

Definition transpose {m n} (A : Matrix m n) : Matrix n m := 
  fun x y => A y x.

Definition adjoint {m n} (A : Matrix m n) : Matrix n m := 
  fun x y => (A y x)^*.

(** We can derive the dot product and its complex analogue, the 
    _inner product_, from matrix multiplication. *)

Definition dot {n : nat} (A : Vector n) (B : Vector n) : C :=
  Mmult (transpose A) B 0 0.

Definition inner_product {n} (u v : Vector n) : C := 
  Mmult (adjoint u) (v) 0 0.

(** The _outer product_ produces a square matrix from two vectors. *)

Definition outer_product {n} (u v : Vector n) : Square n := 
  Mmult u (adjoint v).

Close Scope nat_scope.

Infix "×" := Mmult (at level 40, left associativity) : matrix_scope.
Infix "⊗" := kron (at level 40, left associativity) : matrix_scope.
Notation "A ⊤" := (transpose A) (at level 0) : matrix_scope. 
Notation "A †" := (adjoint A) (at level 0) : matrix_scope. 
Infix "∘" := dot (at level 40, left associativity) : matrix_scope.
Notation "⟨ A , B ⟩" := (inner_product A B) : matrix_scope.

(* ================================================================= *)
(** ** Compatibility lemmas *)

Lemma trace_compat : forall {n} (A A' : Square n),
    A == A' -> trace A = trace A'.
Proof.
  intros n A A' H.
  apply Csum_eq.
  intros x Hx.
  rewrite H; easy.
Qed.

Add Parametric Morphism n : (@trace n)
  with signature mat_equiv ==> eq as trace_mor.
Proof. intros; apply trace_compat; easy. Qed.

Lemma Mmult_compat : forall {m n o} (A A' : Matrix m n) (B B' : Matrix n o),
    A == A' -> B == B' -> A × B == A' × B'.
Proof.
  intros m n o A A' B B' HA HB i j Hi Hj.
  unfold Mmult.
  apply Csum_eq; intros x Hx.
  rewrite HA, HB; easy.
Qed.

Add Parametric Morphism m n o : (@Mmult m n o)
  with signature mat_equiv ==> mat_equiv ==> mat_equiv as Mmult_mor.
Proof. intros. apply Mmult_compat; easy. Qed.

Lemma kron_compat : forall {m n o p} (A A' : Matrix m n) (B B' : Matrix o p),
    A == A' -> B == B' -> A ⊗ B == A' ⊗ B'.
Proof.
  intros m n o p A A' B B' HA HB.
  intros i j Hi Hj.
  unfold kron.
  assert (Ho : o <> O). intros F. rewrite F in *. lia.
  assert (Hp : p <> O). intros F. rewrite F in *. lia.
  rewrite HA, HB. easy.
  - apply Nat.mod_upper_bound; easy.
  - apply Nat.mod_upper_bound; easy.
  - apply Nat.div_lt_upper_bound; lia.
  - apply Nat.div_lt_upper_bound; lia.
Qed.

Add Parametric Morphism m n o p : (@kron m n o p)
  with signature mat_equiv ==> mat_equiv ==> mat_equiv as kron_mor.
Proof. intros. apply kron_compat; easy. Qed.

Lemma transpose_compat : forall {m n} (A A' : Matrix m n),
    A == A' -> A⊤ == A'⊤.
Proof.
  intros m n A A' H.
  intros i j Hi Hj.
  unfold transpose.
  rewrite H; easy.
Qed.

Add Parametric Morphism m n : (@transpose m n)
  with signature mat_equiv ==> mat_equiv as transpose_mor.
Proof. intros. apply transpose_compat; easy. Qed.

Lemma adjoint_compat : forall {m n} (A A' : Matrix m n),
    A == A' -> A† == A'†.
Proof.
  intros m n A A' H.
  intros i j Hi Hj.
  unfold adjoint.
  rewrite H; easy.
Qed.

Add Parametric Morphism m n : (@adjoint m n)
  with signature mat_equiv ==> mat_equiv as adjoint_mor.
Proof. intros. apply adjoint_compat; easy. Qed.

(* ################################################################# *)
(** * Matrix Properties *)

Theorem Mmult_assoc : forall {m n o p : nat} (A : Matrix m n) (B : Matrix n o) 
  (C: Matrix o p), A × B × C == A × (B × C).
Proof.
  intros m n o p A B C i j Hi Hj.
  unfold Mmult.
  induction n.
  + simpl.
    clear B.
    induction o. reflexivity.
    simpl. rewrite IHo. lca.
  + simpl. 
    rewrite <- IHn.
    simpl.
    rewrite Csum_mult_l.
    rewrite <- Csum_plus.
    apply Csum_eq; intros.
    rewrite Cmult_plus_distr_r.
    rewrite Cmult_assoc.
    reflexivity.
Qed.

Lemma Mmult_adjoint : forall {m n o : nat} (A : Matrix m n) (B : Matrix n o),
      (A × B)† == B† × A†.
Proof.
  intros m n o A B i j Hi Hj.
  unfold Mmult, adjoint.
  rewrite Csum_conj_distr.
  apply Csum_eq; intros.
  rewrite Cconj_mult_distr.
  rewrite Cmult_comm.
  reflexivity.
Qed.

Lemma adjoint_involutive : forall {m n} (A : Matrix m n), A†† == A.
Proof.
  (* WORKED IN CLASS *)
  intros m n A i j _ _.
  lca.
Qed.  
  
Lemma kron_adjoint : forall {m n o p} (A : Matrix m n) (B : Matrix o p),
  (A ⊗ B)† == A† ⊗ B†.
Proof. 
  (* WORKED IN CLASS *)
  intros m n o p A B.
  intros i j Hi Hj.
  unfold adjoint, kron. 
  rewrite Cconj_mult_distr.
  reflexivity.
Qed.
  

(* ################################################################# *)
(** * Matrix Automation *)

(** A useful tactic for solving A == B for concrete A, B *)

Ltac solve_end :=
  match goal with
  | H : lt _ O |- _ => apply Nat.nlt_0_r in H; contradict H
  end.
                
Ltac by_cell := 
  intros;
  let i := fresh "i" in 
  let j := fresh "j" in 
  let Hi := fresh "Hi" in 
  let Hj := fresh "Hj" in 
  intros i j Hi Hj; try solve_end;
  repeat (destruct i as [|i]; simpl; [|apply lt_S_n in Hi]; try solve_end); clear Hi;
  repeat (destruct j as [|j]; simpl; [|apply lt_S_n in Hj]; try solve_end); clear Hj.

Ltac lma := by_cell; lca.

(** Let's test it! *)                                                     
Lemma scale0_concrete : 0 * I 10 == Zero _ _.
Proof. lma. Qed.

(* ################################################################# *)
(** * Matrix Library *)

(** These equalities will prove useful in the future. *)
    
Lemma id_kron : forall {m n : nat},  I m ⊗ I n == I (m * n).
Proof. 
  intros. intros i j Hi Hj.
  unfold I, kron.
  destruct (i =? j) eqn:E. apply Nat.eqb_eq in E. subst.
  - rewrite <- 2 beq_nat_refl. lca.
  - destruct (i / n =? j / n) eqn:E1; destruct (i mod n =? j mod n) eqn:E2; 
      try lca; try lia.
    apply Nat.eqb_eq in E1.
    apply Nat.eqb_eq in E2.
    apply  Nat.eqb_neq in E.
    contradict E.
    assert (n * m <> 0)%nat as Hnm by lia.
    apply Nat.neq_mul_0 in Hnm as [Hn _].
    rewrite (Nat.div_mod i n) by assumption. 
    rewrite (Nat.div_mod j n) by assumption. 
    rewrite E1, E2.
    reflexivity.
Qed.

Lemma Mscale_0_l : forall {m n : nat} (A : Matrix m n), 0 * A == Zero m n.
Proof. intros. lma. Qed.

Lemma Mscale_0_r : forall {m n : nat} (c : C), c * Zero m n == Zero m n.
Proof. intros. lma. Qed.

Lemma Mscale_1_l : forall {m n : nat} (A : Matrix m n), 1 * A == A.
Proof. intros. lma. Qed.

Lemma Mscale_1_r : forall {n : nat} (c : C),
    c * I n == fun x y => if (x =? y) then c else 0.
Proof.
  intros n c i j _ _.
  unfold I, Mscale; simpl. 
  destruct (i =? j); lca.
Qed.

Lemma Mmult_0_l : forall {m n o : nat} (A : Matrix n o), Zero m n × A == Zero m o.
Proof.
  intros m n o A i j Hi Hj.
  unfold Mmult, Zero.
  rewrite Csum_0. easy.
  intros. lca.
Qed.    

Lemma Mmult_0_r : forall {m n o : nat} (A : Matrix m n), A × Zero n o == Zero m o.
Proof.
  intros m n o A i j Hi Hj.
  unfold Mmult, Zero.
  rewrite Csum_0. easy.
  intros. lca.
Qed.

Lemma Mmult_1_l: forall {m n : nat} (A : Matrix m n), 
  I m × A == A.
Proof.
  intros m n A i j Hi Hj.
  unfold Mmult.
  eapply Csum_unique. apply Hi.
  unfold I. rewrite Nat.eqb_refl. lca.
  intros x Hx.
  unfold I.
  apply Nat.eqb_neq in Hx. rewrite Hx.
  lca.
Qed.

Lemma Mmult_1_r: forall {m n : nat} (A : Matrix m n), 
  A × I n == A.
Proof.
  intros m n A i j Hi Hj.
  unfold Mmult.
  eapply Csum_unique. apply Hj.
  unfold I. rewrite Nat.eqb_refl. lca.
  intros x Hx.
  unfold I.
  apply Nat.eqb_neq in Hx. rewrite Nat.eqb_sym. rewrite Hx.
  lca.
Qed.

Lemma kron_0_l : forall {m n o p : nat} (A : Matrix o p), 
  Zero m n ⊗ A == Zero _ _.
Proof. intros. lma. Qed.

Lemma kron_0_r : forall {m n o p : nat} (A : Matrix m n), 
   A ⊗ Zero o p == Zero _ _.
Proof. intros. lma. Qed.

Lemma kron_1_l : forall {m n : nat} (A : Matrix m n), I 1 ⊗ A == A.
Proof.
  intros m n A i j Hi Hj.
  unfold I, kron.
  rewrite 2 Nat.mod_small by lia.
  rewrite 2 Nat.div_small by lia.
  simpl; lca.
Qed.

Lemma kron_1_r : forall {m n : nat} (A : Matrix m n), A ⊗ I 1 == A.
Proof. 
  intros m n A i j Hi Hj.
  unfold I, kron.
  rewrite 2 Nat.div_1_r.
  rewrite 2 Nat.mod_1_r.
  simpl; lca.
Qed.

(* This lemma is between matrices of "different" dimensions,
   so we often need strict equality *)
Lemma kron_1_r' : forall {m n : nat} (A : Matrix m n), A ⊗ I 1 = A.
Proof. 
  intros m n A.
  unfold I, kron.
  apply functional_extensionality; intros.
  apply functional_extensionality; intros.
  rewrite 2 Nat.div_1_r.
  rewrite 2 Nat.mod_1_r.
  simpl; lca.
Qed.

Lemma kron_1_l_inv : forall {m n} (A : Matrix m n),
  A == I 1 ⊗ A.
Proof.
  intros.   
  specialize (kron_1_l A) as G.
  rewrite 2 Nat.mul_1_l in *.
  symmetry.
  apply G.
Qed.

Lemma kron_1_r_inv : forall {m n} (A : Matrix m n),
  A == A ⊗ I 1.
Proof.
  intros.   
  specialize (kron_1_r A) as G.
  rewrite 2 Nat.mul_1_r in *.
  symmetry.
  apply G.
Qed.

Lemma id_transpose_eq : forall {n : nat}, (I n)⊤ == (I n).
Proof. 
  intros. by_cell. 
  unfold transpose, I.
  rewrite Nat.eqb_sym.
  reflexivity.
Qed.

Lemma zero_transpose_eq : forall {m n : nat}, (@Zero m n)⊤ == @Zero m n.
Proof. reflexivity. Qed.

Lemma id_adjoint_eq : forall {n : nat}, (I n)† == (I n).
Proof.
  by_cell.
  unfold adjoint, I.
  rewrite Nat.eqb_sym.
  destruct (i =? j); lca.
Qed.

Lemma zero_adjoint_eq : forall {m n : nat}, (@Zero m n)† == @Zero n m.
Proof. 
  unfold adjoint, Zero. 
  rewrite Cconj_0. 
  reflexivity. 
Qed.

Lemma Mplus_adjoint : forall {m n : nat} (A : Matrix m n) (B : Matrix m n),
  (A + B)† == A† + B†.
Proof. lma. Qed.

Lemma Mscale_assoc : forall {m n : nat} (x y : C) (A : Matrix m n),
  x * (y * A) == (x * y)%C * A.
Proof. lma. Qed.

Lemma Mscale_plus_dist_l : forall {m n : nat} (x y : C) (A : Matrix m n),
  (x + y)%C * A == x * A + y * A.
Proof. lma. Qed.

Lemma Mscale_plus_dist_r : forall {m n : nat} (x : C) (A B : Matrix m n),
  x * (A + B) == x * A + x * B.
Proof. lma. Qed.

Lemma Mmult_plus_dist_l : forall {m n o : nat} (A : Matrix m n) (B C : Matrix n o), 
                           A × (B + C) == A × B + A × C.
Proof. 
  intros. intros i j _ _.
  unfold Mplus, Mmult.
  rewrite <- Csum_plus.
  apply Csum_eq_bounded; intros.
  rewrite Cmult_plus_dist_l. 
  reflexivity.
Qed.

Lemma Mmult_plus_dist_r : forall {m n o : nat} (A B : Matrix m n) (C : Matrix n o), 
                           (A + B) × C == A × C + B × C.
Proof. 
  intros. intros i j _ _.
  unfold Mplus, Mmult.
  rewrite <- Csum_plus.
  apply Csum_eq_bounded; intros.
  rewrite Cmult_plus_dist_r. 
  reflexivity.
Qed.

Lemma kron_plus_dist_l : forall {m n o p : nat} (A : Matrix m n) (B C : Matrix o p), 
                           A ⊗ (B + C) == A ⊗ B + A ⊗ C.
Proof. 
  intros m n o p A B C i j _ _.
  unfold Mplus, kron.
  rewrite Cmult_plus_dist_l.
  reflexivity.
Qed.

Lemma kron_plus_dist_r : forall {m n o p : nat} (A B : Matrix m n) (C : Matrix o p), 
                           (A + B) ⊗ C == A ⊗ C + B ⊗ C.
Proof. 
  intros m n o p A B C i j _ _.
  unfold Mplus, kron.
  rewrite Cmult_plus_dist_r.
  reflexivity.
Qed.

Lemma Mscale_mult_dist_l : forall {m n o : nat} (x : C) (A : Matrix m n) (B : Matrix n o), 
    ((x * A) × B) == x * (A × B).
Proof. 
  intros. intros i j _ _.
  unfold Mscale, Mmult.
  rewrite Csum_mult_l.
  apply Csum_eq_bounded; intros.
  lca.
Qed.

Lemma Mscale_mult_dist_r : forall {m n o : nat} (x : C) (A : Matrix m n) (B : Matrix n o),
    (A × (x * B)) == x * (A × B).
Proof.
  intros. intros i j _ _.
  unfold Mscale, Mmult.
  rewrite Csum_mult_l.
  apply Csum_eq_bounded; intros.
  lca.
Qed.

Lemma Mscale_kron_dist_l : forall {m n o p : nat} (x : C) (A : Matrix m n) (B : Matrix o p), 
    ((x * A) ⊗ B) == x * (A ⊗ B).
Proof. lma. Qed.

Lemma Mscale_kron_dist_r : forall {m n o p : nat} (x : C) (A : Matrix m n) (B : Matrix o p), 
    (A ⊗ (x * B)) == x * (A ⊗ B).
Proof. lma. Qed.

Lemma kron_mixed_product : forall {m n o p q r : nat} (A : Matrix m n) (B : Matrix p q ) 
  (C : Matrix n o) (D : Matrix q r), (A ⊗ B) × (C ⊗ D) == (A × C) ⊗ (B × D).
Proof.
  intros m n o p q r A B C D i j _ _.
  unfold kron, Mmult.
  destruct q.
  + simpl.
    rewrite mult_0_r.
    simpl.
    rewrite Cmult_0_r.
    reflexivity. 
  + rewrite Csum_product by lia.
    apply Csum_eq_bounded. intros.
    lca.
Qed.

(*******************************)
(* Automation *)
(*******************************)

Lemma double_mult : forall (n : nat), (n + n = 2 * n)%nat. Proof. intros. lia. Qed.
Lemma pow_two_succ_l : forall x, (2^x * 2 = 2 ^ (x + 1))%nat.
Proof. intros. rewrite mult_comm. rewrite <- Nat.pow_succ_r'. intuition. Qed.
Lemma pow_two_succ_r : forall x, (2 * 2^x = 2 ^ (x + 1))%nat.
Proof. intros. rewrite <- Nat.pow_succ_r'. intuition. Qed.
Lemma double_pow : forall (n : nat), (2^n + 2^n = 2^(n+1))%nat. 
Proof. intros. rewrite double_mult. rewrite pow_two_succ_r. reflexivity. Qed.
Lemma pow_components : forall (a b m n : nat), a = b -> m = n -> (a^m = b^n)%nat.
Proof. intuition. Qed.

Ltac unify_pows_two :=
  repeat match goal with
  (* NB: this first thing is potentially a bad idea, do not do with 2^1 *)
  | [ |- context[ 4%nat ]]                  => replace 4%nat with (2^2)%nat by reflexivity
  | [ |- context[ (0 + ?a)%nat]]            => rewrite plus_0_l 
  | [ |- context[ (?a + 0)%nat]]            => rewrite plus_0_r 
  | [ |- context[ (1 * ?a)%nat]]            => rewrite Nat.mul_1_l 
  | [ |- context[ (?a * 1)%nat]]            => rewrite Nat.mul_1_r 
  | [ |- context[ (2 * 2^?x)%nat]]          => rewrite <- Nat.pow_succ_r'
  | [ |- context[ (2^?x * 2)%nat]]          => rewrite pow_two_succ_l
  | [ |- context[ (2^?x + 2^?x)%nat]]       => rewrite double_pow 
  | [ |- context[ (2^?x * 2^?y)%nat]]       => rewrite <- Nat.pow_add_r 
  | [ |- context[ (?a + (?b + ?c))%nat ]]   => rewrite plus_assoc 
  | [ |- (2^?x = 2^?y)%nat ]                => apply pow_components; try lia 
  end.

(** Restoring Matrix dimensions *)
Ltac is_nat_equality :=
  match goal with 
  | |- ?A = ?B => match type of A with
                | nat => idtac
                end
  end.

Lemma f_equal_gen : forall {A B} (f g : A -> B) a b, f = g -> a = b -> f a = g b.
Proof. intros. subst. reflexivity. Qed.

Ltac unify_matrix_dims tac := 
  try reflexivity; 
  repeat (apply f_equal_gen; try reflexivity; 
          try (is_nat_equality; tac)).

Ltac restore_dims_rec A :=
   match A with
(* special cases *)
  | ?A × I _          => let A' := restore_dims_rec A in 
                        match type of A' with 
                        | Matrix ?m' ?n' => constr:(@Mmult m' n' n' A' (I n'))
                        end
  | I _ × ?B          => let B' := restore_dims_rec B in 
                        match type of B' with 
                        | Matrix ?n' ?o' => constr:(@Mmult n' n' o' (I n')  B')
                        end
  | ?A × @Zero ?n ?n  => let A' := restore_dims_rec A in 
                        match type of A' with 
                        | Matrix ?m' ?n' => constr:(@Mmult m' n' n' A' (@Zero n' n'))
                        end
  | @Zero ?n ?n × ?B  => let B' := restore_dims_rec B in 
                        match type of B' with 
                        | Matrix ?n' ?o' => constr:(@Mmult n' n' o' (@Zero n' n') B')
                        end
  | ?A × @Zero ?n ?o  => let A' := restore_dims_rec A in 
                        match type of A' with 
                        | Matrix ?m' ?n' => constr:(@Mmult m' n' o A' (@Zero n' o))
                        end
  | @Zero ?m ?n × ?B  => let B' := restore_dims_rec B in 
                        match type of B' with 
                        | Matrix ?n' ?o' => constr:(@Mmult n' n' o' (@Zero m n') B')
                        end
  | ?A + @Zero ?m ?n => let A' := restore_dims_rec A in 
                        match type of A' with 
                        | Matrix ?m' ?n' => constr:(@Mplus m' n' A' (@Zero m' n'))
                        end
  | @Zero ?m ?n + ?B => let B' := restore_dims_rec B in 
                        match type of B' with 
                        | Matrix ?m' ?n' => constr:(@Mplus m' n' (@Zero m' n') B')
                        end
(* general cases *)
  | ?A == ?B  => let A' := restore_dims_rec A in 
                let B' := restore_dims_rec B in 
                match type of A' with 
                | Matrix ?m' ?n' => constr:(@mat_equiv m' n' A' B')
                  end
  | ?A × ?B   => let A' := restore_dims_rec A in 
                let B' := restore_dims_rec B in 
                match type of A' with 
                | Matrix ?m' ?n' =>
                  match type of B' with 
                  | Matrix ?n'' ?o' => constr:(@Mmult m' n' o' A' B')
                  end
                end 
  | ?A ⊗ ?B   => let A' := restore_dims_rec A in 
                let B' := restore_dims_rec B in 
                match type of A' with 
                | Matrix ?m' ?n' =>
                  match type of B' with 
                  | Matrix ?o' ?p' => constr:(@kron m' n' o' p' A' B')
                  end
                end
  | ?A †      => let A' := restore_dims_rec A in 
                match type of A' with
                | Matrix ?m' ?n' => constr:(@adjoint m' n' A')
                end
  | ?A + ?B => let A' := restore_dims_rec A in 
               let B' := restore_dims_rec B in 
               match type of A' with 
               | Matrix ?m' ?n' =>
                 match type of B' with 
                 | Matrix ?m'' ?n'' => constr:(@Mplus m' n' A' B')
                 end
               end
  | ?c * ?A => let A' := restore_dims_rec A in 
               match type of A' with
               | Matrix ?m' ?n' => constr:(@Mscale m' n' c A')
               end
  (* Handle functions applied to matrices *)
  | ?f ?A    => let f' := restore_dims_rec f in 
               let A' := restore_dims_rec A in 
               constr:(f' A')
  (* default *)
  | ?A       => A
   end.

Ltac restore_dims tac := 
  match goal with
  | |- ?A      => let A' := restore_dims_rec A in 
                replace A with A' by unify_matrix_dims tac
  end.

Tactic Notation "restore_dims" tactic(tac) := restore_dims tac.

Tactic Notation "restore_dims" := restore_dims (try ring; unify_pows_two; simpl; lia).

(*************************)
(* Matrix Simplification *)
(*************************)

#[export] Hint Unfold Mplus Mmult Mscale kron adjoint I : U_db. 

#[export] Hint Rewrite  @kron_1_l @kron_1_r' @Mmult_1_l @Mmult_1_r @Mscale_1_l 
     @id_adjoint_eq @id_transpose_eq : M_db_light.
#[export] Hint Rewrite @kron_0_l @kron_0_r @Mmult_0_l @Mmult_0_r @Mplus_0_l @Mplus_0_r
     @Mscale_0_l @Mscale_0_r @zero_adjoint_eq @zero_transpose_eq : M_db_light.

(* I don't like always doing restore_dims first, but otherwise sometimes leaves 
   unsolvable WF_Matrix goals. *)
Ltac Msimpl_light := restore_dims; autorewrite with M_db_light.

#[export] Hint Rewrite @Mmult_adjoint @Mplus_adjoint @kron_adjoint @kron_mixed_product
     @adjoint_involutive : M_db.

Ltac Msimpl := restore_dims; autorewrite with M_db_light M_db;
  repeat match goal with
  | [|- context[I 1 ⊗ ?A]] => rewrite (kron_1_l A)
  | [|- context[I 1 ⊗ ?A]] => rewrite <- (kron_1_l_inv A)
  end.

  
  

  

  

(* Sun Jan 19 21:29:28 CST 2020 *)
