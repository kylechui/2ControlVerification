Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.
From Proof Require Import MatrixHelpers.
From Proof Require Import SwapHelpers.
From Proof Require Import GateHelpers.
From Proof Require Import AlgebraHelpers. 
From Proof Require Import PartialTraceDefinitions.

Lemma swapbc_decomp_l: forall (B : Square 8),
WF_Matrix B -> 
(swapbc × B) = (fun x y =>
match x with
| 0 | 3 | 4 | 7 => B x y
| 1 => B 2%nat y
| 2 => B 1%nat y
| 5 => B 6%nat y
| 6 => B 5%nat y
| _ => C0
end).
Proof.
intros.
set (A := (fun x y =>
match x with
| 0 | 3 | 4 | 7 => B x y
| 1 => B 2%nat y
| 2 => B 1%nat y
| 5 => B 6%nat y
| 6 => B 5%nat y
| _ => C0
end) : (Square 8)).
lma'.
solve_WF_matrix.
{
    unfold WF_Matrix.
    intros.
    unfold A.
    destruct H0.
    destruct x as [|a]. contradict H0. lia.
    destruct a as [|b]. contradict H0. lia.
    destruct b as [|c]. contradict H0. lia.
    destruct c as [|d]. contradict H0. lia.
    destruct d as [|e]. contradict H0. lia.
    destruct e as [|f]. contradict H0. lia.
    destruct f as [|g]. contradict H0. lia.
    destruct g as [|h]. contradict H0. lia. reflexivity.
    destruct x as [|a]. apply H. lia.
    destruct a as [|b]. apply H. lia.
    destruct b as [|c]. apply H. lia.
    destruct c as [|d]. apply H. lia.
    destruct d as [|e]. apply H. lia.
    destruct e as [|f]. apply H. lia.
    destruct f as [|g]. apply H. lia.
    destruct g as [|h]. apply H. lia. reflexivity.
}
Qed.

Lemma swapbc_decomp_r: forall (B : Square 8),
WF_Matrix B -> 
(B × swapbc) = (fun x y =>
match y with
| 0 | 3 | 4 | 7 => B x y
| 1 => B x 2%nat
| 2 => B x 1%nat
| 5 => B x 6%nat
| 6 => B x 5%nat
| _ => C0
end).
Proof.
intros.
set (A := (fun x y =>
match y with
| 0 | 3 | 4 | 7 => B x y
| 1 => B x 2%nat
| 2 => B x 1%nat
| 5 => B x 6%nat
| 6 => B x 5%nat
| _ => C0
end) : (Square 8)).
lma'.
solve_WF_matrix.
{
    unfold WF_Matrix.
    intros.
    unfold A.
    destruct H0.
    destruct y as [|a]. apply H. lia.
    destruct a as [|b]. apply H. lia.
    destruct b as [|c]. apply H. lia.
    destruct c as [|d]. apply H. lia.
    destruct d as [|e]. apply H. lia.
    destruct e as [|f]. apply H. lia.
    destruct f as [|g]. apply H. lia.
    destruct g as [|h]. apply H. lia. reflexivity.
    destruct y as [|a]. contradict H0. lia.
    destruct a as [|b]. contradict H0. lia.
    destruct b as [|c]. contradict H0. lia.
    destruct c as [|d]. contradict H0. lia.
    destruct d as [|e]. contradict H0. lia.
    destruct e as [|f]. contradict H0. lia.
    destruct f as [|g]. contradict H0. lia.
    destruct g as [|h]. contradict H0. lia. reflexivity.
}
Qed.

Lemma kron42_explicit_decomp: forall (A: Square 4) (B: Square 2), 
WF_Matrix A -> WF_Matrix B -> 
A ⊗ B = ((fun x y => (match (x,y) with 
| (0,0) | (0,1) | (1,0) | (1,1) => (A 0 0)%nat
| (2,0) | (2,1) | (3,0) | (3,1) => (A 1 0)%nat
| (4,0) | (4,1) | (5,0) | (5,1) => (A 2 0)%nat
| (6,0) | (6,1) | (7,0) | (7,1) => (A 3 0)%nat
| (0,2) | (0,3) | (1,2) | (1,3) => (A 0 1)%nat
| (2,2) | (2,3) | (3,2) | (3,3) => (A 1 1)%nat
| (4,2) | (4,3) | (5,2) | (5,3) => (A 2 1)%nat
| (6,2) | (6,3) | (7,2) | (7,3) => (A 3 1)%nat
| (0,4) | (0,5) | (1,4) | (1,5) => (A 0 2)%nat
| (2,4) | (2,5) | (3,4) | (3,5) => (A 1 2)%nat
| (4,4) | (4,5) | (5,4) | (5,5) => (A 2 2)%nat
| (6,4) | (6,5) | (7,4) | (7,5) => (A 3 2)%nat
| (0,6) | (0,7) | (1,6) | (1,7) => (A 0 3)%nat
| (2,6) | (2,7) | (3,6) | (3,7) => (A 1 3)%nat
| (4,6) | (4,7) | (5,6) | (5,7) => (A 2 3)%nat
| (6,6) | (6,7) | (7,6) | (7,7) => (A 3 3)%nat
| _ => C0
end
)
 * B (x mod 2) (y mod 2)) : Square 8).
Proof.
intros.
lma'.
unfold WF_Matrix.
intros.
destruct H1.
destruct x as [|a]. contradict H1. lia.
destruct a as [|b]. contradict H1. lia.
destruct b as [|c]. contradict H1. lia.
destruct c as [|d]. contradict H1. lia.
destruct d as [|e]. contradict H1. lia.
destruct e as [|f]. contradict H1. lia.
destruct f as [|g]. contradict H1. lia.
destruct g as [|h]. contradict H1. lia. apply Cmult_0_l.
destruct x as [|a]. 
destruct y as [|b]. contradict H1. lia.
destruct b as [|c]. contradict H1. lia.
destruct c as [|d]. contradict H1. lia.
destruct d as [|e]. contradict H1. lia.
destruct e as [|f]. contradict H1. lia.
destruct f as [|g]. contradict H1. lia.
destruct g as [|h]. contradict H1. lia.
destruct h as [|i]. contradict H1. lia. apply Cmult_0_l.
destruct a as [|x]. 
destruct y as [|b]. contradict H1. lia.
destruct b as [|c]. contradict H1. lia.
destruct c as [|d]. contradict H1. lia.
destruct d as [|e]. contradict H1. lia.
destruct e as [|f]. contradict H1. lia.
destruct f as [|g]. contradict H1. lia.
destruct g as [|h]. contradict H1. lia.
destruct h as [|i]. contradict H1. lia. apply Cmult_0_l.
destruct x as [|a]. 
destruct y as [|b]. contradict H1. lia.
destruct b as [|c]. contradict H1. lia.
destruct c as [|d]. contradict H1. lia.
destruct d as [|e]. contradict H1. lia.
destruct e as [|f]. contradict H1. lia.
destruct f as [|g]. contradict H1. lia.
destruct g as [|h]. contradict H1. lia.
destruct h as [|i]. contradict H1. lia. apply Cmult_0_l.
destruct a as [|x]. 
destruct y as [|b]. contradict H1. lia.
destruct b as [|c]. contradict H1. lia.
destruct c as [|d]. contradict H1. lia.
destruct d as [|e]. contradict H1. lia.
destruct e as [|f]. contradict H1. lia.
destruct f as [|g]. contradict H1. lia.
destruct g as [|h]. contradict H1. lia.
destruct h as [|i]. contradict H1. lia. apply Cmult_0_l.
destruct x as [|a]. 
destruct y as [|b]. contradict H1. lia.
destruct b as [|c]. contradict H1. lia.
destruct c as [|d]. contradict H1. lia.
destruct d as [|e]. contradict H1. lia.
destruct e as [|f]. contradict H1. lia.
destruct f as [|g]. contradict H1. lia.
destruct g as [|h]. contradict H1. lia.
destruct h as [|i]. contradict H1. lia. apply Cmult_0_l.
destruct a as [|x]. 
destruct y as [|b]. contradict H1. lia.
destruct b as [|c]. contradict H1. lia.
destruct c as [|d]. contradict H1. lia.
destruct d as [|e]. contradict H1. lia.
destruct e as [|f]. contradict H1. lia.
destruct f as [|g]. contradict H1. lia.
destruct g as [|h]. contradict H1. lia.
destruct h as [|i]. contradict H1. lia. apply Cmult_0_l.
destruct x as [|a]. 
destruct y as [|b]. contradict H1. lia.
destruct b as [|c]. contradict H1. lia.
destruct c as [|d]. contradict H1. lia.
destruct d as [|e]. contradict H1. lia.
destruct e as [|f]. contradict H1. lia.
destruct f as [|g]. contradict H1. lia.
destruct g as [|h]. contradict H1. lia.
destruct h as [|i]. contradict H1. lia. apply Cmult_0_l.
destruct a as [|x]. 
destruct y as [|b]. contradict H1. lia.
destruct b as [|c]. contradict H1. lia.
destruct c as [|d]. contradict H1. lia.
destruct d as [|e]. contradict H1. lia.
destruct e as [|f]. contradict H1. lia.
destruct f as [|g]. contradict H1. lia.
destruct g as [|h]. contradict H1. lia.
destruct h as [|i]. contradict H1. lia. apply Cmult_0_l.
apply Cmult_0_l.
Qed.

Lemma Mmult44_explicit_decomp: forall (A B: Square 4), 
WF_Matrix A -> WF_Matrix B -> 
A × B = ((fun x y => 
A x 0%nat * B 0%nat y + A x 1%nat * B 1%nat y
+ A x 2%nat * B 2%nat y + A x 3%nat * B 3%nat y) : Square 4).
Proof.
intros.
lma'.
unfold WF_Matrix.
intros.
destruct H1.
repeat rewrite H. lca. 1,2,3,4: lia.
repeat rewrite H0. lca. all: lia.
Qed.

Lemma Madj_explicit_decomp {m n}: forall (i j : nat) (A : Matrix m n), 
A† i j = (A j i)^*.
Proof. 
intros. 
lca. 
Qed.

Lemma trace_explicit_decomp_square4: forall (A: Square 4), 
trace A = A 0%nat 0%nat + A 1%nat 1%nat + A 2%nat 2%nat + A 3%nat 3%nat.
Proof.
intros.
lca.
Qed.

Lemma trace_kron_square2: forall (A B: Square 2), 
trace (A ⊗ B) = trace (A) * trace (B).
Proof.
intros.
lca.
Qed.

Lemma trace_outer_vec2: forall (a b : Vector 2), 
trace (a × b†) = (b 0%nat 0%nat)^* * (a 0%nat 0%nat) + (b 1%nat 0%nat)^* * (a 1%nat 0%nat).
Proof.
intros.
lca.
Qed.

Lemma vector2_inner_prod_decomp: forall (a b : Vector 2), 
(⟨ a, b ⟩ = (a 0%nat 0%nat)^* * (b 0%nat 0%nat) + (a 1%nat 0%nat)^* * (b 1%nat 0%nat)).
Proof.
intros.
lca.
Qed.

Lemma Mmult_square2_explicit: forall (A B: Square 2), 
WF_Matrix A -> WF_Matrix B -> 
(A × B) = (fun x y => A x 0%nat * B 0%nat y + A x 1%nat * B 1%nat y).
Proof.
intros. lma'.
unfold WF_Matrix.
intros.
destruct H1.
repeat rewrite H. lca. 1,2: lia.
repeat rewrite H0. lca. 1,2: lia.
Qed.

Lemma Mv_prod_21_explicit: forall (A: Square 2) (v : Vector 2),
WF_Matrix A -> WF_Matrix v ->
(A × v) = ((fun x y => 
match (x,y) with 
| (0,0) => (A 0 0)%nat * (v 0 0)%nat + (A 0 1)%nat * (v 1 0)%nat
| (1,0) => (A 1 0)%nat * (v 0 0)%nat + (A 1 1)%nat * (v 1 0)%nat
| _ => C0
end): Square 2). 
Proof.
intros.
lma'.
unfold WF_Matrix.
intros.
destruct H1.
destruct x as [|a]. contradict H. lia.
destruct a as [|x]. contradict H. lia. reflexivity.
destruct x as [|a]. destruct y as [|b]. contradict H. lia.
reflexivity.
destruct a as [|x]. destruct y as [|b]. contradict H. lia. reflexivity. reflexivity.
Qed.

Lemma trace_outer_zero_vec2: forall (a : Vector 2),
WF_Matrix a ->  
trace (a × (a) †) = 0 -> a = Zero.
Proof.
intros.
rewrite trace_outer_vec2 in H0.
apply sum_of_pos_c_is_0_implies_0 in H0.
2,4: apply conj_mult_re_is_nonneg.
2,3: apply conj_mult_im_is_0.
destruct H0 as [a0_0 a1_0].
apply squared_norm_eq_0_implies_0 in a0_0, a1_0.
lma'.
rewrite a0_0.
2: rewrite a1_0.
all: lca.
Qed.