Require Import QuantumLib.Matrix.
Require Import QuantumLib.Eigenvectors.

Definition partial_trace_2q_a (M: Square 4): Square 2 :=
    fun x y =>
    match (x,y) with
    | (0,0) => (M 0 0)%nat + (M 2 2)%nat
    | (0,1) => (M 0 1)%nat + (M 2 3)%nat
    | (1,0) => (M 1 0)%nat + (M 3 2)%nat
    | (1,1) => (M 1 1)%nat + (M 3 3)%nat
    | _ => C0
    end.

Lemma WF_partial_trace_2q_a : forall (A : Square 4),
    WF_Matrix (partial_trace_2q_a A).
Proof.
  intro A.
  show_wf.
Qed.

#[export] Hint Resolve WF_partial_trace_2q_a : wf_db.

Lemma partial_trace_2q_a_linear : forall (c:C) (A B : Square 4),
  partial_trace_2q_a (A .+ c .* B) = partial_trace_2q_a A .+ c .* partial_trace_2q_a B.
Proof.
  intros.
  lma'.
Qed.

Lemma partial_trace_2q_a_compat : forall (A B : Square 4),
  A = B -> partial_trace_2q_a A = partial_trace_2q_a B.
Proof.
  intros.
  rewrite H; reflexivity.
Qed.

Definition partial_trace_2q_b (M: Square 4): Square 2 :=
    fun x y =>
    match (x,y) with
    | (0,0) => (M 0 0)%nat + (M 1 1)%nat
    | (0,1) => (M 0 2)%nat + (M 1 3)%nat
    | (1,0) => (M 2 0)%nat + (M 3 1)%nat
    | (1,1) => (M 2 2)%nat + (M 3 3)%nat
    | _ => C0
    end.

Lemma WF_partial_trace_2q_b : forall (A : Square 4),
    WF_Matrix (partial_trace_2q_b A).
Proof.
  intro A.
  show_wf.
Qed.

#[export] Hint Resolve WF_partial_trace_2q_b : wf_db.

Lemma partial_trace_2q_b_linear : forall (c:C) (A B : Square 4),
  partial_trace_2q_b (A .+ c .* B) = partial_trace_2q_b A .+ c .* partial_trace_2q_b B.
Proof.
  intros.
  lma'.
Qed.

Lemma partial_trace_2q_b_plus : forall (A B : Square 4),
  partial_trace_2q_b (A .+ B) = partial_trace_2q_b A .+ partial_trace_2q_b B.
Proof.
intros.
rewrite <- Mscale_1_l with (A:= B) at 1.
rewrite <- Mscale_1_l with (A:= partial_trace_2q_b B).
apply partial_trace_2q_b_linear.
Qed.

Lemma partial_trace_2q_b_scale : forall (c: C) (A : Square 4),
  partial_trace_2q_b (c .* A) = c .* partial_trace_2q_b A.
Proof.
intros.
rewrite <- Mplus_0_l with (A:= c .* A).
rewrite <- Mplus_0_l with (A:= c .* partial_trace_2q_b A).
assert (Zero = partial_trace_2q_b Zero). lma'.
rewrite H.
apply partial_trace_2q_b_linear.
Qed.

Lemma partial_trace_2q_b_compat : forall (A B : Square 4),
  A = B -> partial_trace_2q_b A = partial_trace_2q_b B.
Proof.
  intros.
  rewrite H; reflexivity.
Qed.

Definition partial_trace_3q_a (M: Square 8): Square 4 :=
    fun x y =>
    match (x,y) with
    | (0,0) => (M 0 0)%nat + (M 4 4)%nat
    | (0,1) => (M 0 1)%nat + (M 4 5)%nat
    | (0,2) => (M 0 2)%nat + (M 4 6)%nat
    | (0,3) => (M 0 3)%nat + (M 4 7)%nat
    | (1,0) => (M 1 0)%nat + (M 5 4)%nat
    | (1,1) => (M 1 1)%nat + (M 5 5)%nat
    | (1,2) => (M 1 2)%nat + (M 5 6)%nat
    | (1,3) => (M 1 3)%nat + (M 5 7)%nat
    | (2,0) => (M 2 0)%nat + (M 6 4)%nat
    | (2,1) => (M 2 1)%nat + (M 6 5)%nat
    | (2,2) => (M 2 2)%nat + (M 6 6)%nat
    | (2,3) => (M 2 3)%nat + (M 6 7)%nat
    | (3,0) => (M 3 0)%nat + (M 7 4)%nat
    | (3,1) => (M 3 1)%nat + (M 7 5)%nat
    | (3,2) => (M 3 2)%nat + (M 7 6)%nat
    | (3,3) => (M 3 3)%nat + (M 7 7)%nat
    | _ => C0
    end.

Lemma WF_partial_trace_3q_a : forall (A : Square 8),
    WF_Matrix (partial_trace_3q_a A).
Proof.
  intro A.
  show_wf.
Qed.

#[export] Hint Resolve WF_partial_trace_3q_a : wf_db.

Lemma partial_trace_3q_a_linear : forall (c:C) (A B : Square 8),
  partial_trace_3q_a (A .+ c .* B) = partial_trace_3q_a A .+ c .* partial_trace_3q_a B.
Proof.
  intros.
  lma'.
Qed.

Lemma partial_trace_3q_a_compat : forall (A B : Square 8),
  A = B -> partial_trace_3q_a A = partial_trace_3q_a B.
Proof.
  intros.
  rewrite H; reflexivity.
Qed.

Definition partial_trace_3q_c (M: Square 8): Square 4 :=
    fun x y =>
    match (x,y) with
    | (0,0) => (M 0 0)%nat + (M 1 1)%nat
    | (0,1) => (M 0 2)%nat + (M 1 3)%nat
    | (0,2) => (M 0 4)%nat + (M 1 5)%nat
    | (0,3) => (M 0 6)%nat + (M 1 7)%nat
    | (1,0) => (M 2 0)%nat + (M 3 1)%nat
    | (1,1) => (M 2 2)%nat + (M 3 3)%nat
    | (1,2) => (M 2 4)%nat + (M 3 5)%nat
    | (1,3) => (M 2 6)%nat + (M 3 7)%nat
    | (2,0) => (M 4 0)%nat + (M 5 1)%nat
    | (2,1) => (M 4 2)%nat + (M 5 3)%nat
    | (2,2) => (M 4 4)%nat + (M 5 5)%nat
    | (2,3) => (M 4 6)%nat + (M 5 7)%nat
    | (3,0) => (M 6 0)%nat + (M 7 1)%nat
    | (3,1) => (M 6 2)%nat + (M 7 3)%nat
    | (3,2) => (M 6 4)%nat + (M 7 5)%nat
    | (3,3) => (M 6 6)%nat + (M 7 7)%nat
    | _ => C0
    end.

Lemma WF_partial_trace_3q_c : forall (A : Square 8),
    WF_Matrix (partial_trace_3q_c A).
Proof.
  intro A.
  show_wf.
Qed.

#[export] Hint Resolve WF_partial_trace_3q_c : wf_db.

Lemma partial_trace_3q_c_linear : forall (c:C) (A B : Square 8),
  partial_trace_3q_c (A .+ c .* B) = partial_trace_3q_c A .+ c .* partial_trace_3q_c B.
Proof.
  intros.
  lma'.
Qed.

Lemma partial_trace_3q_c_plus : forall (A B : Square 8),
  partial_trace_3q_c (A .+ B) = partial_trace_3q_c A .+ partial_trace_3q_c B.
Proof.
intros.
rewrite <- Mscale_1_l with (A:= B) at 1.
rewrite <- Mscale_1_l with (A:= partial_trace_3q_c B).
apply partial_trace_3q_c_linear.
Qed.

Lemma partial_trace_3q_c_scale : forall (c: C) (A : Square 8),
  partial_trace_3q_c (c .* A) = c .* partial_trace_3q_c A.
Proof.
intros.
rewrite <- Mplus_0_l with (A:= c .* A).
rewrite <- Mplus_0_l with (A:= c .* partial_trace_3q_c A).
assert (Zero = partial_trace_3q_c Zero). lma'.
rewrite H.
apply partial_trace_3q_c_linear.
Qed.

Lemma partial_trace_3q_c_compat : forall (A B : Square 8),
  A = B -> partial_trace_3q_c A = partial_trace_3q_c B.
Proof.
  intros.
  rewrite H; reflexivity.
Qed.

Lemma traceout_ac_method_equivalence: forall (A : Square 8),
partial_trace_2q_a (partial_trace_3q_c A) = partial_trace_2q_b (partial_trace_3q_a A).
Proof.
  intros.
  lma'.
Qed.
