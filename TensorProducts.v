Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.
From Proof Require Import MatrixHelpers.
From Proof Require Import QubitHelpers.
From Proof Require Import GateHelpers.
From Proof Require Import SwapHelpers.
From Proof Require Import AlgebraHelpers.
From Proof Require Import PartialTraceDefinitions.
From Proof Require Import UnitaryMatrices.
From Proof Require Import Vectors.

Lemma Mscale_access {m n}: forall (a : C) (B : Matrix m n) (i j : nat), 
a * (B i j) = (a .* B) i j.
Proof.
intros.
lca.
Qed.

Lemma Mplus_acess {m n}: forall (A B : Matrix m n) (i j : nat), 
(A .+ B) i j = (A i j) + (B i j).
Proof.
intros.
lca.
Qed.

Lemma a20_part1: forall (w : Vector 4), 
WF_Matrix w -> 
(TensorProd w <-> (exists (b0 b1: C) (phi: Vector 2), 
WF_Matrix phi /\ (w 0%nat 0%nat) .* ∣0⟩ .+ (w 1%nat 0%nat) .* ∣1⟩ = b0 .* phi
/\ (w 2%nat 0%nat) .* ∣0⟩ .+ (w 3%nat 0%nat) .* ∣1⟩ = b1 .* phi)).
Proof.
split.
{
    intros.
    apply H0 in H.
    destruct H as [u [v [WF_v [WF_w w_decomp]]]].
    exists (u 0%nat 0%nat), (u 1%nat 0%nat), v.
    split. assumption.
    rewrite w_decomp.
    unfold kron.
    simpl.
    repeat rewrite <- Mscale_assoc.
    repeat rewrite <- Mscale_plus_distr_r.
    rewrite <- (qubit_decomposition1 v). 2: assumption.
    split. all: reflexivity.
}
{
    intros. intro.
    destruct H0 as [b0 [b1 [phi [WF_phi [tens_top tens_bot]]]]].
    set (v := (fun x y =>
    match (x,y) with
    | (0,0) => b0
    | (1,0) => b1
    | _ => C0
    end) : (Vector 2)).
    assert (WF_v: WF_Matrix v).
    {
        unfold WF_Matrix.
        intros.
        unfold v.
        destruct H0.
        destruct x as [|x']. contradict H0. lia.
        destruct x' as [|x'']. contradict H0. lia. reflexivity.
        destruct x as [|x']. destruct y as [|y']. contradict H0. lia. reflexivity.
        destruct x' as [|x'']. destruct y as [|y']. contradict H0. lia.
        reflexivity. reflexivity.
    }
    exists v, phi.
    split. 2: split. 1,2: assumption.
    lma'.
    all: unfold kron, v.
    all: simpl.
    all: rewrite Mscale_access.
    1,2: rewrite <- tens_top.
    3,4: rewrite <- tens_bot.
    all: lca.
}
Qed.

Lemma qubit_01_lin_indep: linearly_independent_2vec ∣0⟩ ∣1⟩.
Proof.
apply orthonormal_implies_lin_indep_2.
1,2: solve_WF_matrix.
all: lca.
Qed.

Lemma a20_part2: forall (w : Vector 4), 
WF_Matrix w -> 
((exists (b0 b1: C) (phi: Vector 2), 
WF_Matrix phi /\ (w 0%nat 0%nat) .* ∣0⟩ .+ (w 1%nat 0%nat) .* ∣1⟩ = b0 .* phi
/\ (w 2%nat 0%nat) .* ∣0⟩ .+ (w 3%nat 0%nat) .* ∣1⟩ = b1 .* phi) 
<-> ((exists (c: C), (w 0%nat 0%nat) .* ∣0⟩ .+ (w 1%nat 0%nat) .* ∣1⟩ = 
c .* ((w 2%nat 0%nat) .* ∣0⟩ .+ (w 3%nat 0%nat) .* ∣1⟩)) \/ ((w 2%nat 0%nat) = 0 /\ (w 3%nat 0%nat) = 0))).
Proof.
intros w WF_w.
split.
{
    intros.
    destruct H as [b0 [b1 [phi [WF_phi [w_tens_top w_tens_bot]]]]].
    destruct (Ceq_dec b1 0).
    {
        right.
        apply qubit_01_lin_indep.
        rewrite w_tens_bot.
        rewrite e.
        apply Mscale_0_l.
    }
    {
        left.
        exists (b0 * /b1).
        rewrite w_tens_bot.
        rewrite Mscale_assoc.
        rewrite <- Cmult_assoc.
        rewrite Cinv_l. 2: assumption.
        rewrite Cmult_1_r.
        apply w_tens_top.
    }
}
{
    intros.
    destruct H.
    {
      destruct H as [c eq_scale].
      exists c, C1, (w 2%nat 0%nat .* ∣0⟩ .+ w 3%nat 0%nat .* ∣1⟩).
      split. solve_WF_matrix.
      split. assumption.
      rewrite Mscale_1_l.
      reflexivity.    
    }
    {
      destruct H as [w2_0 w3_0].
      exists C1, C0, (w 0%nat 0%nat .* ∣0⟩ .+ w 1%nat 0%nat .* ∣1⟩).
      split. solve_WF_matrix.
      split. rewrite Mscale_1_l. reflexivity.
      rewrite w2_0, w3_0. lma'.
    }   
}
Qed.

Lemma Mopp_scale_distr_l {m n}: forall (A : Matrix m n) (c : C), 
Mopp (c .* A) = c .* (Mopp A).
Proof.
intros.
unfold Mopp.
do 2 rewrite Mscale_assoc.
rewrite Cmult_comm.
reflexivity.
Qed.

Lemma a20_part3: forall (w : Vector 4), 
WF_Matrix w -> 
((exists (c: C), (w 0%nat 0%nat) .* ∣0⟩ .+ (w 1%nat 0%nat) .* ∣1⟩ = 
c .* ((w 2%nat 0%nat) .* ∣0⟩ .+ (w 3%nat 0%nat) .* ∣1⟩)) 
<->
(exists (c: C), (w 0%nat 0%nat) = c * (w 2%nat 0%nat) /\
(w 1%nat 0%nat) = c * (w 3%nat 0%nat))
).
Proof.
intros w WF_w.
split.
{
  intros.
  destruct H as [c mat_scale_def].
  exists c.
  (* bringing terms into lin indep form *)
  rewrite Mscale_plus_distr_r in mat_scale_def.
  apply (f_equal (fun f => Mopp (c .* (w 2%nat 0%nat .* ∣0⟩)) .+ f)) in mat_scale_def.
  rewrite <- Mplus_assoc in mat_scale_def. rewrite <- Mplus_assoc in mat_scale_def.
  rewrite Mplus_opp_0_l in mat_scale_def. 2: solve_WF_matrix.
  rewrite Mplus_0_l in mat_scale_def.
  apply (f_equal (fun f => f .+ Mopp (c .* (w 3%nat 0%nat .* ∣1⟩)))) in mat_scale_def.
  rewrite Mplus_opp_0_r in mat_scale_def. 2: solve_WF_matrix.
  unfold Mopp in mat_scale_def.
  repeat rewrite Mscale_assoc in mat_scale_def.
  rewrite <- Mscale_plus_distr_l in mat_scale_def.
  rewrite Mplus_assoc in mat_scale_def.
  rewrite <- Mscale_plus_distr_l in mat_scale_def.
  apply qubit_01_lin_indep in mat_scale_def.
  destruct mat_scale_def as [leftH rightH].
  split.
  {
    apply (f_equal (fun f => C1 * c * w 2%nat 0%nat + f) ) in leftH.
    rewrite Cplus_assoc in leftH.
    rewrite <- Copp_mult_distr_l in leftH. rewrite <- Copp_mult_distr_l in leftH.
    rewrite Cplus_opp_r in leftH.
    rewrite Cplus_0_r in leftH. rewrite Cplus_0_l in leftH.
    rewrite Cmult_1_l in leftH.
    apply leftH.
  }
  {
    apply (f_equal (fun f => f + C1 * c * w 3%nat 0%nat) ) in rightH.
    rewrite <- Cplus_assoc in rightH.
    rewrite <- Copp_mult_distr_l in rightH. rewrite <- Copp_mult_distr_l in rightH.
    rewrite Cplus_opp_l in rightH.
    rewrite Cplus_0_r in rightH. rewrite Cplus_0_l in rightH.
    rewrite Cmult_1_l in rightH.
    apply rightH.
  }
}
{
    intros.
    destruct H as [c [w0_scale w1_scale]].
    exists c.
    rewrite w0_scale, w1_scale.
    lma'.
}
Qed.

Lemma a20_part4: forall (w : Vector 4), 
WF_Matrix w -> 
((exists (c: C), (w 0%nat 0%nat) = c * (w 2%nat 0%nat) /\
(w 1%nat 0%nat) = c * (w 3%nat 0%nat)) \/ ((w 2%nat 0%nat) = 0 /\ (w 3%nat 0%nat) = 0)
<->
(w 0%nat 0%nat) * (w 3%nat 0%nat) = (w 1%nat 0%nat) * (w 2%nat 0%nat)
).
Proof.
intros w WF_w.
split.
{
    intros.
    destruct H.
    {
        destruct H as [c [w0_scale w1_scale]].
        rewrite w0_scale, w1_scale.
        lca.
    }
    {
        destruct H as [w2_0 w3_0].
        rewrite w2_0, w3_0.
        lca.
    }    
}
{
    intros mult_eq.
    destruct (Ceq_dec (w 2%nat 0%nat) 0).
    {
        destruct (Ceq_dec (w 3%nat 0%nat) 0).
        {
            right.
            split. all: assumption.
        }
        {
            left.
            exists ((w 1%nat 0%nat) * /(w 3%nat 0%nat)).
            split.
            {
              apply (f_equal (fun f => f * / w 3%nat 0%nat)) in mult_eq.
              rewrite <- Cmult_assoc in mult_eq.
              rewrite Cinv_r in mult_eq. 2: assumption.
              rewrite Cmult_1_r in mult_eq.
              rewrite mult_eq.
              lca.
            }
            {
              rewrite <- Cmult_assoc.
              rewrite Cinv_l. 2: assumption.
              lca.   
            }
        }
    }
    {
        left.
        exists ((w 0%nat 0%nat) * /(w 2%nat 0%nat)).
        split.
        {
            rewrite <- Cmult_assoc.
            rewrite Cinv_l. 2: assumption.
            lca.  
        }
        {
            apply (f_equal (fun f => f * / w 2%nat 0%nat)) in mult_eq.
            rewrite <- Cmult_assoc in mult_eq. rewrite <- Cmult_assoc in mult_eq.
            rewrite Cinv_r in mult_eq. 2: assumption.
            rewrite Cmult_1_r in mult_eq.
            rewrite <- mult_eq.
            lca.
        }
    }
}
Qed.

Lemma a20: forall (w : Vector 4), 
WF_Matrix w -> 
(TensorProd w <-> (w 0%nat 0%nat) * (w 3%nat 0%nat) = (w 1%nat 0%nat) * (w 2%nat 0%nat)).
Proof.
intros.
rewrite a20_part1.
rewrite a20_part2.
rewrite a20_part3.
rewrite a20_part4.
reflexivity.
all: assumption.
Qed.

Lemma a21: forall (U : Square 4), 
WF_Unitary U -> exists (psi : Vector 2), 
TensorProd (U × (∣0⟩ ⊗ psi)).
Proof. 
intros U WF_U.
destruct (Classical_Prop.classic (TensorProd (U × (∣0⟩ ⊗ ∣0⟩)))).
{
    exists ∣0⟩. assumption.
}
{
    set (a00 := (U × (∣0⟩ ⊗ ∣0⟩)) 0%nat 0%nat).
    set (a01 := (U × (∣0⟩ ⊗ ∣0⟩)) 1%nat 0%nat).
    set (a10 := (U × (∣0⟩ ⊗ ∣0⟩)) 2%nat 0%nat).
    set (a11 := (U × (∣0⟩ ⊗ ∣0⟩)) 3%nat 0%nat).
    set (b00 := (U × (∣0⟩ ⊗ ∣1⟩)) 0%nat 0%nat).
    set (b01 := (U × (∣0⟩ ⊗ ∣1⟩)) 1%nat 0%nat).
    set (b10 := (U × (∣0⟩ ⊗ ∣1⟩)) 2%nat 0%nat).
    set (b11 := (U × (∣0⟩ ⊗ ∣1⟩)) 3%nat 0%nat).
    set (a := (a00 * a11 - a01 * a10)%C).
    set (b := (a00 * b11 + a11 * b00 - a01 * b10 - a10 * b01)%C).
    set (c := (b00 * b11 - b01 * b10)%C).
    admit.
    (* set (quad := sqrt (b * b - 4 * a * c)%C).
    set (p0 := (/ (2 * a)%C * (-b + quad))%C).
    set (c0 := 1 / √ ((Cmod p0)^2 + 1)). *)
}
Admitted.

Lemma vector2_inner_prod_decomp: forall (a b : Vector 2) (c : C), 
WF_Matrix a -> WF_Matrix b -> 
(⟨ a, b ⟩ = c <-> (a 0%nat 0%nat)^* * (b 0%nat 0%nat) + (a 1%nat 0%nat)^* * (b 1%nat 0%nat) = c).
Proof.
split.
{
    intros.
    rewrite <- H1.
    lca.
}
{
    intros.
    rewrite <- H1.
    lca.
}
Qed.



Lemma exists_orthogonal_qubit: forall (phi: Vector 2), 
WF_Qubit phi -> exists (psi: Vector 2), (WF_Qubit psi /\ ⟨ phi , psi ⟩ = C0).
Proof.
intros.
destruct H as [_ [WF_phi phi_unit]].
set (psi := (fun x y =>
    match (x,y) with
    | (0,0) => -((phi 1%nat 0%nat)^*)
    | (1,0) => (phi 0%nat 0%nat)^*
    | _ => C0
    end) : (Vector 2)).
assert (WF_psi: WF_Matrix psi). 
{
    unfold WF_Matrix.
    intros.
    unfold psi. 
    destruct H.
    destruct x as [|x']. contradict H. lia.
    destruct x' as [|x'']. contradict H. lia. reflexivity.
    destruct x as [|x']. destruct y as [|y']. contradict H. lia. reflexivity.
    destruct x' as [|x'']. destruct y as [|y']. contradict H. lia.
    reflexivity. reflexivity.
}
exists psi.
split.
{
    split.
    exists 1%nat. trivial.
    split. assumption.
    {
        rewrite vector2_inner_prod_decomp in *. 2,3,4,5: assumption.
        unfold psi.
        rewrite <- phi_unit.
        lca.
    }
}
{
    rewrite vector2_inner_prod_decomp. 2,3: assumption.
    unfold psi.
    lca.
}
Qed.

Lemma swapbc_sa: swapbc = (swapbc) †. Proof. lma'. 2: apply WF_adjoint. all: apply WF_swapbc. Qed.

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

Lemma Cmult_const_r: forall (a b c : C), 
a = b -> a * c = b * c.
Proof. 
intros. 
rewrite H. 
reflexivity.
Qed.

Lemma Madj_explicit_decomp {m n}: forall (i j : nat) (A : Matrix m n), 
A† i j = (A j i)^*.
Proof. 
intros. 
lca. 
Qed.

(* Lemma kron22_explicit_decomp: forall (A: Square 2) (B: Square 2), 
WF_Matrix A -> WF_Matrix B -> 
A ⊗ B = ((fun x y => (match (x,y) with 
| (0,0) | (0,1) | (1,0) | (1,1) => (A 0 0)%nat
| (2,0) | (2,1) | (3,0) | (3,1) => (A 1 0)%nat
| (0,2) | (0,3) | (1,2) | (1,3) => (A 0 1)%nat
| (2,2) | (2,3) | (3,2) | (3,3) => (A 1 1)%nat
| _ => C0
end
)
 * B (x mod 2) (y mod 2)) : Square 4).
Proof.
intros.
lma'.
unfold WF_Matrix.
intros.
destruct H1.
destruct x as [|a]. contradict H1. lia.
destruct a as [|b]. contradict H1. lia.
destruct b as [|c]. contradict H1. lia.
destruct c as [|d]. contradict H1. lia. apply Cmult_0_l.
destruct x as [|a]. 
destruct y as [|b]. contradict H1. lia.
destruct b as [|c]. contradict H1. lia.
destruct c as [|d]. contradict H1. lia.
destruct d as [|e]. contradict H1. lia. apply Cmult_0_l.
destruct a as [|x]. 
destruct y as [|b]. contradict H1. lia.
destruct b as [|c]. contradict H1. lia.
destruct c as [|d]. contradict H1. lia.
destruct d as [|e]. contradict H1. lia. apply Cmult_0_l.
destruct x as [|a]. 
destruct y as [|b]. contradict H1. lia.
destruct b as [|c]. contradict H1. lia.
destruct c as [|d]. contradict H1. lia.
destruct d as [|e]. contradict H1. lia. apply Cmult_0_l.
destruct a as [|x]. 
destruct y as [|b]. contradict H1. lia.
destruct b as [|c]. contradict H1. lia.
destruct c as [|d]. contradict H1. lia.
destruct d as [|e]. contradict H1. lia. apply Cmult_0_l.
apply Cmult_0_l.
Qed. *)

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

Lemma qubit_prop_explicit: forall (a: Vector 2), 
WF_Qubit a -> 
(a 0%nat 0%nat)^* * (a 0%nat 0%nat) + (a 1%nat 0%nat)^* * (a 1%nat 0%nat) = C1.
Proof.
intros.
destruct H as [_ [WF_a a_unit]].
rewrite <- a_unit.
lca.
Qed.

Lemma partial_trace_ac_on_acgate: forall (U : Square 4) (a b c: Vector 2), 
WF_Unitary U -> WF_Qubit a -> WF_Qubit b -> WF_Qubit c -> 
partial_trace_2q_a (partial_trace_3q_c (acgate U × (a ⊗ b ⊗ c) × (a ⊗ b ⊗ c)† × (acgate U)†))
= b × b†.
Proof.
intros U a b c U_unitary a_qubit b_qubit c_qubit.
assert (WF_U: WF_Matrix U). apply U_unitary.
assert (WF_a: WF_Matrix a). apply a_qubit. 
assert (WF_b: WF_Matrix b). apply b_qubit.
assert (WF_c: WF_Matrix c). apply c_qubit.
apply mat_equiv_eq.
apply WF_partial_trace_2q_a.
solve_WF_matrix.
rewrite kron_adjoint. rewrite kron_adjoint.
rewrite Mmult_assoc. rewrite Mmult_assoc.
rewrite <- Mmult_assoc with (A:=a ⊗ b ⊗ c).
assert (kron_mix_help: a ⊗ b ⊗ c × ((a) † ⊗ (b) † ⊗ (c) †) = (a × (a) †) ⊗ (b × (b) †) ⊗ (c × (c) †)). 
{
    rewrite kron_mixed_product with (A:= a ⊗ b) (B := c) (C:= (a) † ⊗ (b) †) (D:= (c) †).
    rewrite kron_mixed_product.
    reflexivity.
}
rewrite kron_mix_help at 1.
clear kron_mix_help.
unfold acgate.
rewrite Mmult_adjoint.
rewrite <- swapbc_sa at 1.
rewrite Mmult_adjoint.
rewrite <- swapbc_sa.
repeat rewrite Mmult_assoc.
rewrite <- Mmult_assoc with (A:= a × (a) † ⊗ (b × (b) †) ⊗ (c × (c) †)).
rewrite <- Mmult_assoc with (B := a × (a) † ⊗ (b × (b) †) ⊗ (c × (c) †) × swapbc).
rewrite <- Mmult_assoc with (B := a × (a) † ⊗ (b × (b) †) ⊗ (c × (c) †)).
rewrite swapbc_3gate. 2,3,4: solve_WF_matrix.
unfold abgate.
rewrite <- Mmult_assoc with (B := a × (a) † ⊗ (c × (c) †) ⊗ (b × (b) †)).
assert (kron_mix_help: U ⊗ I 2 × (a × (a) † ⊗ (c × (c) †) ⊗ (b × (b) †)) =
 (U × (a × (a) † ⊗ (c × (c) †))) ⊗ (b × (b) †) ).
{
    rewrite <- Mmult_1_l with (A:= (b × (b) †)) at 2.
    apply kron_mixed_product.
    solve_WF_matrix.
}
rewrite kron_mix_help at 1.
clear kron_mix_help.
rewrite <- Mmult_assoc with (C := swapbc).
assert (kron_adj_helper: (U ⊗ I 2) † = U† ⊗ I 2). lma'.
rewrite kron_adj_helper at 1.
clear kron_adj_helper. 
assert (kron_mix_help: U × (a × (a) † ⊗ (c × (c) †)) ⊗ (b × (b) †) × ((U) † ⊗ I 2) = 
(U × (a × (a) † ⊗ (c × (c) †)) × (U) †) ⊗ (b × (b) †)).
{
    rewrite <- Mmult_1_r with (A:= (b × (b) †)) at 2.
    apply kron_mixed_product.
    solve_WF_matrix.
}
rewrite kron_mix_help at 1.
assert (WF_helper1: WF_Matrix (U × (a × (a) † ⊗ (c × (c) †)) × (U) † ⊗ (b × (b) †) × swapbc)).
{
    apply WF_mult.
    apply WF_kron. reflexivity. reflexivity.
    apply WF_mult.
    apply WF_mult.
    all: solve_WF_matrix.
}
assert (WF_helper2: WF_Matrix (U × (a × (a) † ⊗ (c × (c) †)) × (U) † ⊗ (b × (b) †))).
{
    apply WF_kron. reflexivity. reflexivity.
    apply WF_mult.
    apply WF_mult.
    all: solve_WF_matrix.
}
assert (WF_helper3: WF_Matrix (U × (a × (a) † ⊗ (c × (c) †)) × (U) †)).
{
    apply WF_mult.
    apply WF_mult.
    all: solve_WF_matrix.
}
assert (WF_helper4: WF_Matrix ((b × (b) †))).
{
    solve_WF_matrix.
}
assert (WF_helper5: WF_Matrix (U × (a × (a) † ⊗ (c × (c) †)))).
{
    solve_WF_matrix.
}
assert (WF_helper6: WF_Matrix (U) †).
{
    apply WF_adjoint.
    apply U_unitary.
}
assert (WF_helper8: WF_Matrix (a × (a) † ⊗ (c × (c) †))).
{
    solve_WF_matrix. 
}
set (a00:= (a × (a) † ⊗ (c × (c) †)) 0%nat 0%nat).
set (a10:= (a × (a) † ⊗ (c × (c) †)) 1%nat 0%nat).
set (a20:= (a × (a) † ⊗ (c × (c) †)) 2%nat 0%nat).
set (a30:= (a × (a) † ⊗ (c × (c) †)) 3%nat 0%nat).
set (a01:= (a × (a) † ⊗ (c × (c) †)) 0%nat 1%nat).
set (a11:= (a × (a) † ⊗ (c × (c) †)) 1%nat 1%nat).
set (a21:= (a × (a) † ⊗ (c × (c) †)) 2%nat 1%nat).
set (a31:= (a × (a) † ⊗ (c × (c) †)) 3%nat 1%nat).
set (a02:= (a × (a) † ⊗ (c × (c) †)) 0%nat 2%nat).
set (a12:= (a × (a) † ⊗ (c × (c) †)) 1%nat 2%nat).
set (a22:= (a × (a) † ⊗ (c × (c) †)) 2%nat 2%nat).
set (a32:= (a × (a) † ⊗ (c × (c) †)) 3%nat 2%nat).
set (a03:= (a × (a) † ⊗ (c × (c) †)) 0%nat 3%nat).
set (a13:= (a × (a) † ⊗ (c × (c) †)) 1%nat 3%nat).
set (a23:= (a × (a) † ⊗ (c × (c) †)) 2%nat 3%nat).
set (a33:= (a × (a) † ⊗ (c × (c) †)) 3%nat 3%nat).
set (u00:= U 0%nat 0%nat).
set (u10:= U 1%nat 0%nat).
set (u20:= U 2%nat 0%nat).
set (u30:= U 3%nat 0%nat).
set (u01:= U 0%nat 1%nat).
set (u11:= U 1%nat 1%nat).
set (u21:= U 2%nat 1%nat).
set (u31:= U 3%nat 1%nat).
set (u02:= U 0%nat 2%nat).
set (u12:= U 1%nat 2%nat).
set (u22:= U 2%nat 2%nat).
set (u32:= U 3%nat 2%nat).
set (u03:= U 0%nat 3%nat).
set (u13:= U 1%nat 3%nat).
set (u23:= U 2%nat 3%nat).
set (u33:= U 3%nat 3%nat).
assert (Udag_U_I : (U) † × U = I 4). apply U_unitary.
assert (prod_redist: u00 * a00 * u00 ^* + u01 * a10 * u00 ^* + u02 * a20 * u00 ^* + u03 * a30 * u00 ^* +
(u00 * a01 * u01 ^* + u01 * a11 * u01 ^* + u02 * a21 * u01 ^* + u03 * a31 * u01 ^*) +
(u00 * a02 * u02 ^* + u01 * a12 * u02 ^* + u02 * a22 * u02 ^* + u03 * a32 * u02 ^*) +
(u00 * a03 * u03 ^* + u01 * a13 * u03 ^* + u02 * a23 * u03 ^* + u03 * a33 * u03 ^*) +
(u10 * a00 * u10 ^* + u11 * a10 * u10 ^* + u12 * a20 * u10 ^* + u13 * a30 * u10 ^* +
 (u10 * a01 * u11 ^* + u11 * a11 * u11 ^* + u12 * a21 * u11 ^* + u13 * a31 * u11 ^*) +
 (u10 * a02 * u12 ^* + u11 * a12 * u12 ^* + u12 * a22 * u12 ^* + u13 * a32 * u12 ^*) +
 (u10 * a03 * u13 ^* + u11 * a13 * u13 ^* + u12 * a23 * u13 ^* + u13 * a33 * u13 ^*)) +
(u20 * a00 * u20 ^* + u21 * a10 * u20 ^* + u22 * a20 * u20 ^* + u23 * a30 * u20 ^* +
 (u20 * a01 * u21 ^* + u21 * a11 * u21 ^* + u22 * a21 * u21 ^* + u23 * a31 * u21 ^*) +
 (u20 * a02 * u22 ^* + u21 * a12 * u22 ^* + u22 * a22 * u22 ^* + u23 * a32 * u22 ^*) +
 (u20 * a03 * u23 ^* + u21 * a13 * u23 ^* + u22 * a23 * u23 ^* + u23 * a33 * u23 ^*) +
 (u30 * a00 * u30 ^* + u31 * a10 * u30 ^* + u32 * a20 * u30 ^* + u33 * a30 * u30 ^* +
  (u30 * a01 * u31 ^* + u31 * a11 * u31 ^* + u32 * a21 * u31 ^* + u33 * a31 * u31 ^*) +
  (u30 * a02 * u32 ^* + u31 * a12 * u32 ^* + u32 * a22 * u32 ^* + u33 * a32 * u32 ^*) +
  (u30 * a03 * u33 ^* + u31 * a13 * u33 ^* + u32 * a23 * u33 ^* + u33 * a33 * u33 ^*))) = 
  (u00 * a00 * u00 ^* + u10 * a00 * u10 ^* + u20 * a00 * u20 ^* + u30 * a00 * u30 ^*)
+ (u01 * a10 * u00 ^* + u11 * a10 * u10 ^* + u21 * a10 * u20 ^* + u31 * a10 * u30 ^*)
+ (u02 * a20 * u00 ^* + u12 * a20 * u10 ^* + u22 * a20 * u20 ^* + u32 * a20 * u30 ^*)
+ (u03 * a30 * u00 ^* + u13 * a30 * u10 ^* + u23 * a30 * u20 ^* + u33 * a30 * u30 ^*)
+ (u00 * a01 * u01 ^* + u10 * a01 * u11 ^* + u20 * a01 * u21 ^* + u30 * a01 * u31 ^*)
+ (u01 * a11 * u01 ^* + u11 * a11 * u11 ^* + u21 * a11 * u21 ^* + u31 * a11 * u31 ^*)
+ (u02 * a21 * u01 ^* + u12 * a21 * u11 ^* + u22 * a21 * u21 ^* + u32 * a21 * u31 ^*)
+ (u03 * a31 * u01 ^* + u13 * a31 * u11 ^* + u23 * a31 * u21 ^* + u33 * a31 * u31 ^*)
+ (u00 * a02 * u02 ^* + u10 * a02 * u12 ^* + u20 * a02 * u22 ^* + u30 * a02 * u32 ^*)
+ (u01 * a12 * u02 ^* + u11 * a12 * u12 ^* + u21 * a12 * u22 ^* + u31 * a12 * u32 ^*)
+ (u02 * a22 * u02 ^* + u12 * a22 * u12 ^* + u22 * a22 * u22 ^* + u32 * a22 * u32 ^*)
+ (u03 * a32 * u02 ^* + u13 * a32 * u12 ^* + u23 * a32 * u22 ^* + u33 * a32 * u32 ^*)
+ (u00 * a03 * u03 ^* + u10 * a03 * u13 ^* + u20 * a03 * u23 ^* + u30 * a03 * u33 ^*)
+ (u01 * a13 * u03 ^* + u11 * a13 * u13 ^* + u21 * a13 * u23 ^* + u31 * a13 * u33 ^*)
+ (u02 * a23 * u03 ^* + u12 * a23 * u13 ^* + u22 * a23 * u23 ^* + u32 * a23 * u33 ^*)
+ (u03 * a33 * u03 ^* + u13 * a33 * u13 ^* + u23 * a33 * u23 ^* + u33 * a33 * u33 ^*)
).
{
    lca.
}
assert (a00_extract: 
u00 * a00 * u00 ^* + u10 * a00 * u10 ^* + u20 * a00 * u20 ^* + u30 * a00 * u30 ^* = 
((U† × U) 0%nat 0%nat) * a00).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
assert (a10_extract: 
u01 * a10 * u00 ^* + u11 * a10 * u10 ^* + u21 * a10 * u20 ^* + u31 * a10 * u30 ^* = 
((U† × U) 0%nat 1%nat) * a10).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
assert (a20_extract: 
u02 * a20 * u00 ^* + u12 * a20 * u10 ^* + u22 * a20 * u20 ^* + u32 * a20 * u30 ^* = 
((U† × U) 0%nat 2%nat) * a20).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
assert (a30_extract: 
u03 * a30 * u00 ^* + u13 * a30 * u10 ^* + u23 * a30 * u20 ^* + u33 * a30 * u30 ^* = 
((U† × U) 0%nat 3%nat) * a30).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
assert (a01_extract: 
u00 * a01 * u01 ^* + u10 * a01 * u11 ^* + u20 * a01 * u21 ^* + u30 * a01 * u31 ^* = 
((U† × U) 1%nat 0%nat) * a01).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
assert (a11_extract: 
u01 * a11 * u01 ^* + u11 * a11 * u11 ^* + u21 * a11 * u21 ^* + u31 * a11 * u31 ^* = 
((U† × U) 1%nat 1%nat) * a11).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
assert (a21_extract: 
u02 * a21 * u01 ^* + u12 * a21 * u11 ^* + u22 * a21 * u21 ^* + u32 * a21 * u31 ^* = 
((U† × U) 1%nat 2%nat) * a21).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
assert (a31_extract: 
u03 * a31 * u01 ^* + u13 * a31 * u11 ^* + u23 * a31 * u21 ^* + u33 * a31 * u31 ^* = 
((U† × U) 1%nat 3%nat) * a31).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
assert (a02_extract: 
u00 * a02 * u02 ^* + u10 * a02 * u12 ^* + u20 * a02 * u22 ^* + u30 * a02 * u32 ^* = 
((U† × U) 2%nat 0%nat) * a02).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
assert (a12_extract: 
u01 * a12 * u02 ^* + u11 * a12 * u12 ^* + u21 * a12 * u22 ^* + u31 * a12 * u32 ^* = 
((U† × U) 2%nat 1%nat) * a12).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
assert (a22_extract: 
u02 * a22 * u02 ^* + u12 * a22 * u12 ^* + u22 * a22 * u22 ^* + u32 * a22 * u32 ^* = 
((U† × U) 2%nat 2%nat) * a22).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
assert (a32_extract: 
u03 * a32 * u02 ^* + u13 * a32 * u12 ^* + u23 * a32 * u22 ^* + u33 * a32 * u32 ^* = 
((U† × U) 2%nat 3%nat) * a32).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
assert (a03_extract: 
u00 * a03 * u03 ^* + u10 * a03 * u13 ^* + u20 * a03 * u23 ^* + u30 * a03 * u33 ^* = 
((U† × U) 3%nat 0%nat) * a03).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
assert (a13_extract: 
u01 * a13 * u03 ^* + u11 * a13 * u13 ^* + u21 * a13 * u23 ^* + u31 * a13 * u33 ^* = 
((U† × U) 3%nat 1%nat) * a13).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
assert (a23_extract: 
u02 * a23 * u03 ^* + u12 * a23 * u13 ^* + u22 * a23 * u23 ^* + u32 * a23 * u33 ^* = 
((U† × U) 3%nat 2%nat) * a23).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
assert (a33_extract: 
u03 * a33 * u03 ^* + u13 * a33 * u13 ^* + u23 * a33 * u23 ^* + u33 * a33 * u33 ^* = 
((U† × U) 3%nat 3%nat) * a33).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
by_cell.
all: unfold partial_trace_2q_a, partial_trace_3q_c.
all: rewrite swapbc_decomp_l. 
2,4,6,8: assumption.
all: rewrite swapbc_decomp_r.
2,4,6,8: assumption.
all: rewrite kron42_explicit_decomp.
2,3,5,6,8,9,11,12: assumption.
all: simpl.
all: rewrite Mmult44_explicit_decomp.
2,3,5,6,8,9,11,12: assumption.
all: repeat rewrite <- Cmult_plus_distr_r.
all: rewrite <- Cmult_1_l.
all: apply Cmult_const_r.
all: rewrite Mmult44_explicit_decomp.
2,3,5,6,8,9,11,12: assumption.
all: fold a00 a01 a02 a03.
all: fold a10 a11 a12 a13.
all: fold a20 a21 a22 a23.
all: fold a30 a31 a32 a33.
all: repeat rewrite Madj_explicit_decomp.
all: fold u00 u01 u02 u03.
all: fold u10 u11 u12 u13.
all: fold u20 u21 u22 u23.
all: fold u30 u31 u32 u33.
all: repeat rewrite Cmult_plus_distr_r.
all: rewrite prod_redist.
all: rewrite a00_extract.
all: rewrite a10_extract.
all: rewrite a20_extract.
all: rewrite a30_extract.
all: rewrite a01_extract.
all: rewrite a11_extract.
all: rewrite a21_extract.
all: rewrite a31_extract.
all: rewrite a02_extract.
all: rewrite a12_extract.
all: rewrite a22_extract.
all: rewrite a32_extract.
all: rewrite a03_extract.
all: rewrite a13_extract.
all: rewrite a23_extract.
all: rewrite a33_extract.
all: rewrite Udag_U_I.
all: Csimpl.
all: unfold a00, a11, a22, a33.
all: rewrite <- trace_explicit_decomp_square4.
all: rewrite trace_kron_square2.
all: repeat rewrite trace_outer_vec2.
all: repeat rewrite qubit_prop_explicit.
1,4,7,10: apply Cmult_1_l.
1,3,5,7: apply c_qubit.
all: apply a_qubit.
Qed.

Lemma Mscale_0_cancel {m n}: forall (c: C) (A: Matrix m n), 
A <> Zero -> Zero = c .* A -> c = 0.
Proof.
intros.
rewrite nonzero_def in H.
destruct H as [x0 [y0 nonzero_point]].
assert ((c .* A) x0 y0 = 0). rewrite <- H0. trivial.
rewrite <- Mscale_access in H.
apply (f_equal (fun f => f * /(A x0 y0))) in H.
rewrite Cmult_0_l in H.
rewrite <- Cmult_assoc in H.
rewrite Cinv_r in H.
rewrite Cmult_1_r in H.
all: assumption.
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



Lemma a22: forall (U: Square 4) (a b g psi : Vector 2) (phi : Vector 4), 
WF_Unitary U -> WF_Qubit a -> WF_Qubit b -> WF_Qubit g -> WF_Qubit psi -> WF_Qubit phi -> 
(acgate U) × (a ⊗ b ⊗ g) = psi ⊗ phi -> 
exists (w : Vector 2), phi = b ⊗ w.
Proof.
intros U a b g psi phi U_unitary a_qubit b_qubit g_qubit psi_qubit phi_qubit acU_app.
assert (WF_U: WF_Matrix U). apply U_unitary.
assert (WF_a: WF_Matrix a). apply a_qubit.
assert (WF_b: WF_Matrix b). apply b_qubit.
assert (WF_g: WF_Matrix g). apply g_qubit.
assert (WF_psi: WF_Matrix psi). apply psi_qubit.
assert (WF_phi: WF_Matrix phi). apply phi_qubit.
assert (outer_prod_equiv : acgate U × (a ⊗ b ⊗ g) × (a ⊗ b ⊗ g)† × (acgate U)† = (psi ⊗ phi) × (psi† ⊗ phi†)).
{
    rewrite acU_app.
    rewrite Mmult_assoc.
    rewrite <- Mmult_adjoint.
    assert (app_helper: acgate U × (a ⊗ b ⊗ g) = psi ⊗ phi). apply acU_app.
    rewrite app_helper at 1. clear app_helper.
    rewrite kron_adjoint.
    reflexivity.
}
(* trace out ac qubits *)
apply partial_trace_3q_c_compat in outer_prod_equiv.
apply partial_trace_2q_a_compat in outer_prod_equiv.
rewrite partial_trace_ac_on_acgate in outer_prod_equiv. 2,3,4,5: assumption.
rewrite traceout_ac_method_equivalence in outer_prod_equiv.
rewrite kron_mixed_product in outer_prod_equiv.
rewrite a7_3q_a in outer_prod_equiv. 2: solve_WF_matrix.
rewrite trace_outer_vec2 in outer_prod_equiv.
rewrite qubit_prop_explicit in outer_prod_equiv. 2: assumption.
rewrite Mscale_1_l in outer_prod_equiv.
assert (orth_qubit := exists_orthogonal_qubit b b_qubit).
destruct orth_qubit as [bp [bp_qubit b_orth]].
assert (WF_bp: WF_Matrix bp). apply bp_qubit.
assert (phi_decomp:= a15 b bp phi b_qubit bp_qubit phi_qubit b_orth).
destruct phi_decomp as [w [z [phi_decomp [WF_w WF_z]]]].
assert (phi_outer_decomp: phi × (phi) † = (b × (b) †)⊗(w × (w) †) .+
(b × (bp) †)⊗(w × (z) †) .+ (bp × (b) †)⊗(z × (w) †) .+ (bp × (bp) †)⊗(z × (z) †)).
{
    rewrite phi_decomp.
    rewrite Mplus_adjoint.
    rewrite kron_adjoint. rewrite kron_adjoint.
    rewrite Mmult_plus_distr_l. repeat rewrite Mmult_plus_distr_r.
    repeat rewrite kron_mixed_product.
    rewrite Mplus_assoc. rewrite <- Mplus_assoc with (A:=bp × (b) † ⊗ (z × (w) †)).
    rewrite Mplus_comm with (A:=bp × (b) † ⊗ (z × (w) †)).
    repeat rewrite <- Mplus_assoc.
    reflexivity.   
}
(* prepare outer_prod_equiv for simplificiation with vector prods *)
rewrite phi_outer_decomp in outer_prod_equiv.
repeat rewrite Mplus_assoc in outer_prod_equiv.
repeat rewrite partial_trace_2q_b_plus in outer_prod_equiv.
rewrite a7_2q_b in outer_prod_equiv. 2: solve_WF_matrix.
rewrite a7_2q_b in outer_prod_equiv. 2: solve_WF_matrix.
rewrite a7_2q_b in outer_prod_equiv. 2: solve_WF_matrix.
rewrite a7_2q_b in outer_prod_equiv. 2: solve_WF_matrix.
(* mult by bpadj on left *)
assert (bp_inner_I : (bp) † × bp = I 1). apply inner_prod_1_decomp. 1,2: solve_WF_matrix. apply bp_qubit.
assert (bp_b_0 : (bp) † × b = Zero). apply inner_prod_0_decomp. 3: apply inner_prod_0_comm. 5: apply b_orth. 1,2,3,4: solve_WF_matrix.
apply (f_equal (fun f => (bp) † × f)) in outer_prod_equiv.
rewrite <- Mmult_assoc in outer_prod_equiv.
rewrite bp_b_0 in outer_prod_equiv.
rewrite Mmult_0_l in outer_prod_equiv.
rewrite Mmult_plus_distr_l in outer_prod_equiv.
rewrite Mscale_mult_dist_r in outer_prod_equiv.
rewrite <- Mmult_assoc in outer_prod_equiv.
rewrite bp_b_0 in outer_prod_equiv.
rewrite Mmult_0_l in outer_prod_equiv.
rewrite Mscale_0_r in outer_prod_equiv.
rewrite Mplus_0_l in outer_prod_equiv.
rewrite Mmult_plus_distr_l in outer_prod_equiv.
rewrite Mscale_mult_dist_r in outer_prod_equiv.
rewrite <- Mmult_assoc in outer_prod_equiv.
rewrite bp_b_0 in outer_prod_equiv.
rewrite Mmult_0_l in outer_prod_equiv.
rewrite Mscale_0_r in outer_prod_equiv.
rewrite Mplus_0_l in outer_prod_equiv.
rewrite Mmult_plus_distr_l in outer_prod_equiv.
rewrite Mscale_mult_dist_r in outer_prod_equiv.
rewrite <- Mmult_assoc in outer_prod_equiv.
rewrite bp_inner_I in outer_prod_equiv.
rewrite Mmult_1_l in outer_prod_equiv. 2: solve_WF_matrix.
rewrite Mscale_mult_dist_r in outer_prod_equiv.
rewrite <- Mmult_assoc in outer_prod_equiv.
rewrite bp_inner_I in outer_prod_equiv.
rewrite Mmult_1_l in outer_prod_equiv. 2: solve_WF_matrix.
(* mult by bp on right *)
assert (b_bp_0 : (b) † × bp = Zero). apply inner_prod_0_decomp. 3: apply b_orth. 1,2: solve_WF_matrix.
apply (f_equal (fun f => f × bp)) in outer_prod_equiv.
rewrite Mmult_0_l in outer_prod_equiv.
rewrite Mmult_plus_distr_r in outer_prod_equiv.
rewrite Mscale_mult_dist_l in outer_prod_equiv.
rewrite b_bp_0 in outer_prod_equiv.
rewrite Mscale_0_r in outer_prod_equiv.
rewrite Mplus_0_l in outer_prod_equiv.
rewrite Mscale_mult_dist_l in outer_prod_equiv.
rewrite bp_inner_I in outer_prod_equiv.
apply Mscale_0_cancel in outer_prod_equiv. 2: apply I_neq_zero. 2: lia.
apply trace_outer_zero_vec2 in outer_prod_equiv. 2: assumption.
(* replace this in phi to finish proof *)
rewrite outer_prod_equiv in phi_decomp.
rewrite kron_0_r in phi_decomp.
rewrite Mplus_0_r in phi_decomp.
exists w.
apply phi_decomp.
Qed.
