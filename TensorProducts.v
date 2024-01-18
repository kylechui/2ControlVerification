Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.
From Proof Require Import MatrixHelpers.
From Proof Require Import QubitHelpers.
From Proof Require Import GateHelpers.
From Proof Require Import SwapHelpers.
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

Lemma partial_trace_ac_on_acgate: forall (U : Square 4) (a b c: Vector 2), 
WF_Unitary U -> WF_Qubit a -> WF_Qubit b -> WF_Qubit c -> 
partial_trace_2q_a (partial_trace_3q_c (acgate U × (a ⊗ b ⊗ c) × (a ⊗ b ⊗ c)† × (acgate U)†))
= b × b†.
Proof.
intros U a b c U_unitary a_qubit b_qubit c_qubit.
apply mat_equiv_eq.
apply WF_partial_trace_2q_a.
solve_WF_matrix.
1,2: apply b_qubit.
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
rewrite swapbc_3gate. 2,3,4: solve_WF_matrix. 2,3: apply a_qubit. 2,3: apply b_qubit. 2,3: apply c_qubit.
unfold abgate.
rewrite <- Mmult_assoc with (B := a × (a) † ⊗ (c × (c) †) ⊗ (b × (b) †)).
assert (kron_mix_help: U ⊗ I 2 × (a × (a) † ⊗ (c × (c) †) ⊗ (b × (b) †)) =
 (U × (a × (a) † ⊗ (c × (c) †))) ⊗ (b × (b) †) ).
{
    rewrite <- Mmult_1_l with (A:= (b × (b) †)) at 2.
    apply kron_mixed_product.
    solve_WF_matrix.
    all: apply b_qubit.
}
rewrite kron_mix_help at 1.
clear kron_mix_help.
rewrite <- Mmult_assoc with (C := swapbc).
assert (kron_adj_helper: (U ⊗ I 2) † = U† ⊗ I 2). lma'. 1,2: solve_WF_matrix. 1,2: apply U_unitary.
rewrite kron_adj_helper at 1.
clear kron_adj_helper. 
assert (kron_mix_help: U × (a × (a) † ⊗ (c × (c) †)) ⊗ (b × (b) †) × ((U) † ⊗ I 2) = 
(U × (a × (a) † ⊗ (c × (c) †)) × (U) †) ⊗ (b × (b) †)).
{
    rewrite <- Mmult_1_r with (A:= (b × (b) †)) at 2.
    apply kron_mixed_product.
    solve_WF_matrix.
    all: apply b_qubit.
}
rewrite kron_mix_help at 1.
assert (WF_helper1: WF_Matrix (U × (a × (a) † ⊗ (c × (c) †)) × (U) † ⊗ (b × (b) †) × swapbc)).
{
    apply WF_mult.
    apply WF_kron. reflexivity. reflexivity.
    apply WF_mult.
    apply WF_mult.
    all: solve_WF_matrix.
    1,6: apply U_unitary.
    1,2: apply a_qubit.
    1,2: apply c_qubit.
    1,2: apply b_qubit.
}
assert (WF_helper2: WF_Matrix (U × (a × (a) † ⊗ (c × (c) †)) × (U) † ⊗ (b × (b) †))).
{
    apply WF_kron. reflexivity. reflexivity.
    apply WF_mult.
    apply WF_mult.
    all: solve_WF_matrix.
    1,6: apply U_unitary.
    1,2: apply a_qubit.
    1,2: apply c_qubit.
    1,2: apply b_qubit.  
}
assert (WF_helper3: WF_Matrix (U × (a × (a) † ⊗ (c × (c) †)) × (U) †)).
{
    apply WF_mult.
    apply WF_mult.
    all: solve_WF_matrix.
    1,6: apply U_unitary.
    1,2: apply a_qubit.
    1,2: apply c_qubit.  
}
assert (WF_helper4: WF_Matrix ((b × (b) †))).
{
    solve_WF_matrix.
    all: apply b_qubit.
}
assert (WF_helper5: WF_Matrix (U × (a × (a) † ⊗ (c × (c) †)))).
{
    solve_WF_matrix.
    apply U_unitary.
    1,2: apply a_qubit.
    all: apply c_qubit.
}
assert (WF_helper6: WF_Matrix (U) †).
{
    apply WF_adjoint.
    apply U_unitary.
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
all: rewrite Mmult44_explicit_decomp.
Admitted.


Lemma a22: forall (U: Square 4) (a b g psi : Vector 2) (phi : Vector 4), 
WF_Unitary U -> WF_Qubit a -> WF_Qubit b -> WF_Qubit g -> WF_Qubit psi -> WF_Qubit phi -> 
(acgate U) × (a ⊗ b ⊗ g) = psi ⊗ phi -> 
exists (w : Vector 2), phi = b ⊗ w.
Proof.
intros U a b g psi phi U_unitary a_qubit b_qubit g_qubit psi_qubit phi_qubit acU_app.
Admitted.
