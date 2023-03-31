(** * Real: Coq's Axiomatic Real Numbers *)

Require Reals. 
Require Psatz.
Require Ring.
Require Field.

(* ################################################################# *)
(** * Axiomatizing the set R *)

(** Traditionally, real numbers are represented by Cauchy Sequences or
    Dedekind Cuts. These representations are mathematically rigorous
    and expressible in Coq, and implemented in libraries like the Coq
    Repository at Nijmegen (CoRN). However, these representations are
    difficult both to express and to compute with.

    Coq's standard library takes a very different approach to the real
    numbers: An _axiomatic_ approach. *)

Module OurR.

Parameter R : Set.

Delimit Scope R_scope with R.
Local Open Scope R_scope.

(** We'll start by _declaring_ two real numbers - the important ones. *)
Parameter R0 : R.
Parameter R1 : R.

(** Along with methods for obtaining (some of) the others *)
Parameter Rplus : R -> R -> R.
Parameter Rmult : R -> R -> R.
Parameter Ropp : R -> R.
Parameter Rinv : R -> R.

Infix "+" := Rplus : R_scope.
Infix "*" := Rmult : R_scope.
Notation "- x" := (Ropp x) : R_scope.
Notation "/ x" := (Rinv x) : R_scope.

(** Other basic operations are given in terms of our declared ones *)

Definition Rminus (r1 r2:R) : R := r1 + - r2.
Definition Rdiv (r1 r2:R) : R := r1 * / r2.

Infix "-" := Rminus : R_scope.
Infix "/" := Rdiv : R_scope.

(** We'd like to be able to convert natural numbers to Rs, thereby allowing
    ourselves to write numbers like 0, 1, 2, 3... *)

Fixpoint INR (n : nat) : R :=
  match n with
  | O    => R0
  | 1    => R1            
  | S n' => R1 + INR n'
  end.

(** The standard library defines a coercion from Z to R which is
    slightly more useful but also more difficult to parse. *)

(** A _coercion_ tells Coq to try applying a given function whenever
   types mismatch. For instance, [Rplus 4 5] will currently give a
   type error. *)

Fail Check (4 + 5).

Coercion INR : nat >-> R.
 
Check 4 + 5.
Compute (4 + 5).

(* ################################################################# *)
(** * The Field Equations *)

(** We can now proceed to the core of the real number library : The axioms *)

Axiom R1_neq_R0 : INR 1 <> INR 0.

(** Addition *)

Axiom Rplus_comm : forall r1 r2 : R, r1 + r2 = r2 + r1.

Axiom Rplus_assoc : forall r1 r2 r3 : R, r1 + r2 + r3 = r1 + (r2 + r3).

Axiom Rplus_opp_r : forall r : R, r + - r = 0.

Axiom Rplus_0_l : forall r : R, 0 + r = r.

(** Of course, not everything needs to be an axiom: We've left some things out. *)

Lemma Rplus_0_r : forall r : R, r + 0 = r.
Proof.
  (* WORKED IN CLASS *)
  intros r.
  rewrite Rplus_comm.
  apply Rplus_0_l.
Qed.
  
Lemma Rplus_opp_l : forall r, -r + r = 0.
Proof.
  (* WORKED IN CLASS *)
  intros r.
  rewrite Rplus_comm.
  apply Rplus_opp_r.
Qed.

Lemma Ropp_0 : -0 = 0.
Proof.
  rewrite <- (Rplus_0_l (-0)).
  rewrite Rplus_opp_r.
  reflexivity.
Qed.

Lemma Rplus_cancel_l : forall r1 r2 r3, r1 + r2 = r1 + r3 -> r2 = r3.
Proof.
  intros r1 r2 r3 H.
  rewrite <- Rplus_0_l.
  rewrite <- (Rplus_opp_l r1).
  rewrite Rplus_assoc.
  rewrite <- H.
  rewrite <- Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_l.
  reflexivity.
Qed.
    
Lemma R0_unique : forall r1 r2, r1 + r2 = r1 -> r2 = 0.
Proof.
  intros r1 r2 H.
  rewrite <- Rplus_0_r in H.
  eapply Rplus_cancel_l.
  apply H.
Qed.  

(** Multiplicative axioms *)

Axiom Rmult_comm : forall r1 r2:R, r1 * r2 = r2 * r1.

Axiom Rmult_assoc : forall r1 r2 r3:R, r1 * r2 * r3 = r1 * (r2 * r3).

Axiom Rinv_l : forall r:R, r <> 0 -> / r * r = 1.

Axiom Rmult_1_l : forall r:R, 1 * r = r.

Axiom Rmult_plus_distr_l : forall r1 r2 r3:R, r1 * (r2 + r3) = r1 * r2 + r1 * r3.

Lemma Rmult_0_r : forall r, r * 0 = 0.
Proof.
  (* WORKED IN CLASS *)
  intros r.
  apply (R0_unique (r * 0)).
  rewrite <- Rmult_plus_distr_l.
  rewrite Rplus_0_l.
  reflexivity.
Qed.

Lemma Rmult_plus_distr_r : forall r1 r2 r3:R, (r1 + r2) * r3 = r1 * r3 + r2 * r3.
Proof.
  (* WORKED IN CLASS *)
  intros r1 r2 r3.
  rewrite Rmult_comm.
  rewrite Rmult_plus_distr_l.
  rewrite 2 (Rmult_comm r3).
  reflexivity.
Qed.

Lemma Rinv_r : forall r:R, r <> 0 -> r * / r = 1.
Proof.
  (* WORKED IN CLASS *)
  intros. rewrite Rmult_comm.
  apply Rinv_l.
  assumption.
Qed.
  
(* ================================================================= *)
(** ** The Ring and Field tactics *)

(** Once we have some set of basic lemmas, we can tell Coq that R forms an
    algebraic _ring_ and _field_. *)

Export Ring.
Export Field.

Lemma R_Ring_Theory : ring_theory R0 R1 Rplus Rmult Rminus Ropp eq.
Proof.
  constructor.
  (* addition *)
  (* left identity *) apply Rplus_0_l.
  (* commutativity *) apply Rplus_comm.
  (* associativity *) intros; rewrite Rplus_assoc; easy.
  (* multiplication *)
  (* left identity *) apply Rmult_1_l.
  (* commutativity *) apply Rmult_comm.
  (* associativity *) intros; rewrite Rmult_assoc; easy.
  (* distributivity *) apply Rmult_plus_distr_r.
  (* sub = opp *) reflexivity.
  (* additive inverse *) apply Rplus_opp_r.
Defined.

Add Ring RRing : R_Ring_Theory.  

Lemma R_Field_Theory : field_theory R0 R1 Rplus Rmult Rminus Ropp Rdiv Rinv eq.
Proof.
  constructor.
  (* ring axioms *) apply R_Ring_Theory.
  (* 0 <> 1 *) apply R1_neq_R0.
  (* div = inv *) reflexivity.
  (* multiplicative inverse *) apply Rinv_l.
Defined.

Add Field RField : R_Field_Theory.  

(** Let's look at what these tactics can do *)

Example ring_test1 : forall (x : R), x + x = 2 * x. Proof. intros. simpl. ring. Qed.
Example ring_test2 : forall (x y z: R), x * y + z  = z + y * x. Proof. intros. ring. Qed.

Example field_test1 : forall (x y : R), x <> 0 -> x * y / x = y.
Proof. intros. Fail ring. field. assumption. Qed.

(* ################################################################# *)
(** * Ordering *)

(** We also impose the standard ordering on real numbers, again by
    means of axioms *)

Parameter Rlt : R -> R -> Prop.

Infix "<" := Rlt : R_scope.

Definition Rgt (r1 r2:R) : Prop := r2 < r1.
Definition Rle (r1 r2:R) : Prop := r1 < r2 \/ r1 = r2.
Definition Rge (r1 r2:R) : Prop := Rgt r1 r2 \/ r1 = r2.

Infix "<=" := Rle : R_scope.
Infix ">=" := Rge : R_scope.
Infix ">" := Rgt : R_scope.

Axiom total_order_T : forall r1 r2 : R, {r1 < r2} + {r1 = r2} + {r1 > r2}.
  
Axiom Rlt_asym : forall r1 r2 : R, r1 < r2 -> ~ r2 < r1.

Axiom Rlt_trans : forall r1 r2 r3 : R, r1 < r2 -> r2 < r3 -> r1 < r3.

Axiom Rplus_lt_compat_l : forall r r1 r2 : R, r1 < r2 -> r + r1 < r + r2.

Axiom Rmult_lt_compat_l : forall r r1 r2 : R, 0 < r -> r1 < r2 -> r * r1 < r * r2.

(* ################################################################# *)
(** * Completeness *)

(** Of course, not every field corresponds to the real numbers:
    Even the rational numbers (a strict subset of the reals) form a
    field. The last thing we need to "complete" the real numbers is
    the _completeness_ axiom. This states that every bounded set of
    real numbers has a least upper bound, which itself is a real
    number.

    As usual, we will express sets as functions of type [R -> Prop],
    indicating whether the given real number is a member of the
    set. *)

Definition is_upper_bound (E:R -> Prop) (m:R) := forall x:R, E x -> x <= m.

Definition bound (E:R -> Prop) := exists m : R, is_upper_bound E m.

Definition is_lub (E:R -> Prop) (m:R) :=
  is_upper_bound E m /\ (forall b:R, is_upper_bound E b -> m <= b).

Axiom
  completeness :
    forall E:R -> Prop,
      bound E -> (exists x : R, E x) -> { m:R | is_lub E m }.

(* ================================================================= *)
(** ** Defining irrational numbers *)

(** Let's see an example of the completeness axiom in practice.  We'll
    only need one new lemma, which we _can_ prove, but it's harder
    than you think. *)

Lemma Rlt_0_1 : 0 < 1. Admitted.

(** We want to define the square root of 2.  The square root of 2 is
    the least upper bound of the predicate [x * x < 2] (or [x * x <= 2]).
    Let's use the completeness axiom to show that such a least upper
    bound exists. *)

Definition lt_sqrt2 (x : R) := x * x < 2.

(** First we need to show that this predicate has an upper bound.  One
    reasonable upper bound is 2 (though 3/2 and 5 would also work). *)

Lemma upper_bound_2_sqrt_2 : is_upper_bound lt_sqrt2 2.
Proof.
  unfold is_upper_bound, lt_sqrt2; simpl.
  intros x H.
  left.
  destruct (total_order_T x 1) as [[L | E] | G].
  - rewrite <- (Rplus_0_r x).
    eapply Rlt_trans.
    apply Rplus_lt_compat_l.
    apply Rlt_0_1.
    rewrite Rplus_comm.
    apply Rplus_lt_compat_l.
    assumption.
  - rewrite E.
    rewrite <- (Rplus_0_r 1).
    apply Rplus_lt_compat_l.
    apply Rlt_0_1.
  - assert (x * 1 < x * x).
    apply Rmult_lt_compat_l. 
    eapply Rlt_trans. 
    apply Rlt_0_1.
    apply G. 
    apply G.
    rewrite Rmult_comm, Rmult_1_l in H0.
    eapply Rlt_trans.
    apply H0.
    apply H.
Qed.

Lemma bound_sqrt2 : bound lt_sqrt2.
Proof. exists 2. apply upper_bound_2_sqrt_2. Qed.

(** We also need to show that some number satisfies this predicate:
    0, 1 and -1 are all reasonable candidates. *)

Lemma ex_lt_sqrt2 : exists x, lt_sqrt2 x.
Proof. 
  exists 1. unfold lt_sqrt2. 
  rewrite Rmult_1_l. 
  rewrite <- (Rplus_0_r 1); simpl. 
  apply Rplus_lt_compat_l.
  apply Rlt_0_1.
Qed.

(** We can now plug these proofs into our completeness axiom/function,
    getting out a real number that is the least upper bound of
    [lt_sqrt2] -- that is, the square root of 2. *)

Definition sqrt2 := completeness lt_sqrt2 bound_sqrt2 ex_lt_sqrt2.

(** In subsequent chapters we will make use of real numbers like 
    √2, π and e, which are defined in the Coq real number library
    using the completeness axiom. **)

End OurR.

(** Let's take a look at our upper bound proof using Coq's own
    real numbers and definitions. Here we will benefit from 
    Coq's automation tactics. *)

Export Reals. 
Export Psatz.

Open Scope R_scope.

Definition lt_sqrt2 (x : R) := x * x < 2.

Lemma upper_bound_2_sqrt_2 : is_upper_bound lt_sqrt2 2.
Proof.
  unfold is_upper_bound, lt_sqrt2; simpl.
  intros x H.
  destruct (total_order_T x 1) as [[L | E] | G]; try lra.
  assert (x * 1 <= x * x).
  { apply Rmult_le_compat_l; lra. }
  lra.
Qed.

(** [lra] stands for Linear Real Arithmetic and is broadly useful in
    proving real number (in)equalities *)

Notation "√ x" := (sqrt x) (at level 0).

Lemma pow2_sqrt : forall x:R, 0 <= x -> (√ x) ^ 2 = x.
Proof. intros; simpl; rewrite Rmult_1_r, sqrt_def; auto. Qed.

Lemma pow2_sqrt2 : (√ 2) ^ 2 = 2.
Proof. apply pow2_sqrt; lra. Qed.

Lemma pown_sqrt : forall (x : R) (n : nat), 
  0 <= x -> √ x ^ (S (S n)) = (x * √ x ^ n)%R.
Proof.
  intros. simpl. rewrite <- Rmult_assoc. rewrite sqrt_sqrt; auto.
Qed.  

Lemma sqrt_neq_0_compat : forall r : R, 0 < r -> (√ r)%R <> 0.
Proof. intros. specialize (sqrt_lt_R0 r). lra. Qed.

Lemma sqrt_inv : forall (r : R), 0 < r -> √ (/ r) = (/ √ r)%R.
Proof.
  intros.
  replace (/r)%R with (1/r)%R by lra.
  rewrite sqrt_div_alt, sqrt_1 by lra.
  lra.
Qed.  

Lemma sqrt2_inv : √ (/ 2) = (/ √ 2)%R.
Proof.
  apply sqrt_inv; lra.
Qed.  

(* Sun Jan 19 21:29:28 CST 2020 *)
