Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.
Require Import WFHelpers.
Require Import MatrixHelpers.
Require Import QubitHelpers.
Require Import GateHelpers.
Require Import SwapHelpers.
Require Import AlgebraHelpers.
Require Import PartialTraceDefinitions.
Require Import ExplicitDecompositions.
Require Import TraceoutHelpers.
Require Import A2_UnitaryMatrices.
Require Import A4_Vectors.

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
WF_Qubit psi /\ TensorProd (U × (∣0⟩ ⊗ psi)).
Proof. 
intros U U_unitary.
destruct (Classical_Prop.classic (TensorProd (U × (∣0⟩ ⊗ ∣0⟩)))).
{
    exists ∣0⟩. split. apply qubit0_qubit. assumption.
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
    set (quad := Complex_sqrt (b * b - 4 * a * c)%C).
    set (p0 := (/ (2 * a)%C * (-b + quad))%C).
    set (c0 := 1 / √ ((Cmod p0)^2 + 1)%R).
    set (psi0 := c0 * p0 .* ∣0⟩ .+ c0 .* ∣1⟩).
    exists psi0.
    assert (div_g0: 0 < Cmod p0 ^ 2 + 1). 
    {
        rewrite <- Rplus_0_l with (r:= 0).
        apply Rplus_le_lt_compat. 2: lra.
        apply Rsqr_ge_0.
    }
    split. 
    {
        unfold WF_Qubit.
        split. exists (1%nat). trivial.
        split. solve_WF_matrix.
        rewrite vector2_inner_prod_decomp.
        unfold psi0.
        repeat rewrite Mplus_access.
        repeat rewrite <- Mscale_access.
        simpl.
        repeat rewrite Cmult_0_r.
        repeat rewrite Cmult_1_r.
        repeat rewrite Cplus_0_l, Cplus_0_r.
        rewrite Cconj_mult_distr.
        rewrite <- Cmult_assoc.
        rewrite Cmult_comm with (x := p0^*).
        rewrite <- Cmult_assoc. rewrite Cmult_assoc at 1.
        rewrite <- Cmult_1_r with (x:= c0 ^* * c0) at 2.
        rewrite <- Cmult_plus_distr_l with (x:= c0 ^* * c0).
        assert (expansion: c0^* * c0 = C1 / (Cmod p0 ^ 2 + 1)).
        {
            unfold c0.
            repeat rewrite <- RtoC_div.
            rewrite RtoC_conj.
            rewrite <- RtoC_mult.
            rewrite Rfrac_product with (a:= 1) .
            rewrite sqrt_sqrt.
            rewrite Rmult_1_l.
            rewrite RtoC_div.
            rewrite RtoC_plus.
            rewrite RtoC_pow.
            reflexivity.
            3,4,5: apply g0_sqn0.
            apply Rgt_not_eq.
            apply Rlt_gt.
            2: apply Rlt_le.
            all: apply div_g0.
        }
        rewrite expansion.
        rewrite Cmult_comm with (x:= p0).
        rewrite <- Cmod_sqr.
        unfold Cdiv.
        rewrite Cmult_1_l.
        apply Cinv_l.
        unfold not.
        intro.
        apply complex_split in H0.
        destruct H0.
        apply eq_sym in H0.
        revert H0.
        rewrite RtoC_pow.
        rewrite <- RtoC_plus.
        unfold RtoC.
        simpl.
        apply Rlt_not_eq.
        replace ((Cmod p0 * (Cmod p0 * 1))%R) with ((Cmod p0 ^ 2)%R) by lra.
        assumption.
    }
    apply a20. solve_WF_matrix.
    assert (psi0_def: psi0 = c0 * p0 .* ∣0⟩ .+ c0 .* ∣1⟩). unfold psi0. reflexivity.
    assert (prod_decomp: U × (∣0⟩ ⊗ psi0) = U × (∣0⟩ ⊗ psi0)). reflexivity.
    rewrite psi0_def in prod_decomp at 2.
    rewrite kron_plus_distr_l in prod_decomp.
    repeat rewrite Mscale_kron_dist_r in prod_decomp.
    rewrite Mmult_plus_distr_l in prod_decomp.
    repeat rewrite Mscale_mult_dist_r in prod_decomp.
    assert (def0: (U × (∣0⟩ ⊗ psi0)) 0%nat 0%nat = c0 * p0 * a00 + c0 * b00).
    {
        rewrite prod_decomp.
        rewrite Mplus_access.
        repeat rewrite <- Mscale_access.
        unfold a00, b00.
        reflexivity.
    }
    assert (def1: (U × (∣0⟩ ⊗ psi0)) 1%nat 0%nat = c0 * p0 * a01 + c0 * b01).
    {
        rewrite prod_decomp.
        rewrite Mplus_access.
        repeat rewrite <- Mscale_access.
        unfold a01, b01.
        reflexivity.
    }
    assert (def2: (U × (∣0⟩ ⊗ psi0)) 2%nat 0%nat = c0 * p0 * a10 + c0 * b10).
    {
        rewrite prod_decomp.
        rewrite Mplus_access.
        repeat rewrite <- Mscale_access.
        unfold a10, b10.
        reflexivity.
    }
    assert (def3: (U × (∣0⟩ ⊗ psi0)) 3%nat 0%nat = c0 * p0 * a11 + c0 * b11).
    {
        rewrite prod_decomp.
        rewrite Mplus_access.
        repeat rewrite <- Mscale_access.
        unfold a11, b11.
        reflexivity.
    }
    rewrite def0, def1, def2, def3.
    repeat rewrite <- Cmult_assoc.
    repeat rewrite <- Cmult_plus_distr_l.
    repeat rewrite <- Cmult_assoc.
    rewrite Cmult_comm with (x := (p0 * a00 + b00)).
    rewrite Cmult_comm with (x := (p0 * a01 + b01)).
    rewrite <- Cmult_assoc.
    rewrite Cmult_assoc with (y := c0).
    rewrite <- Cmult_assoc with (y := (p0 * a10 + b10)).
    rewrite Cmult_assoc with (y := c0).
    apply Cmult_simplify. reflexivity.
    rewrite <- Cplus_0_l with (x := (p0 * a11 + b11) * (p0 * a00 + b00)).
    rewrite <- Cplus_0_r with (x := (p0 * a10 + b10) * (p0 * a01 + b01)).
    rewrite <- Cplus_opp_r with (x := (p0 * a10 + b10) * (p0 * a01 + b01)) at 1.
    rewrite <- Cplus_assoc.
    apply Cplus_simplify. reflexivity.
    assert (replace_helper: forall (p0 a10 b10 a01 b01 a11 b11 a00 b00: C), 
    - ((p0 * a10 + b10) * (p0 * a01 + b01)) + (p0 * a11 + b11) * (p0 * a00 + b00) = 
    p0 ^ 2 * (a00 * a11 - a01 * a10) + p0 * (a00 * b11 + a11 * b00 - a01 * b10 - a10 * b01) + 
    (b00 * b11 - b01 * b10)). intros. lca.
    rewrite replace_helper.
    fold a b c.
    apply quadratic_formula. 2: unfold p0. 2: reflexivity.
    (* follows from U00 not a tensor prod *)
    unfold a. unfold not. intro.
    apply H.
    rewrite a20; solve_WF_matrix.
    apply (f_equal (fun f => f + a01 * a10)) in H0.
    rewrite Cplus_0_l in H0.
    unfold a00, a11, a01, a10 in H0.
    rewrite <- H0 at 1.
    lca.
}
Qed.

Lemma a21b: forall (U : Square 4), 
WF_Unitary U -> exists (psi : Vector 2), 
WF_Qubit psi /\ TensorProd (U × (∣1⟩ ⊗ psi)).
Proof. 
intros U U_unitary.
destruct (Classical_Prop.classic (TensorProd (U × (∣1⟩ ⊗ ∣0⟩)))).
{
    exists ∣0⟩. split. apply qubit0_qubit. assumption.
}
{
    set (a00 := (U × (∣1⟩ ⊗ ∣0⟩)) 0%nat 0%nat).
    set (a01 := (U × (∣1⟩ ⊗ ∣0⟩)) 1%nat 0%nat).
    set (a10 := (U × (∣1⟩ ⊗ ∣0⟩)) 2%nat 0%nat).
    set (a11 := (U × (∣1⟩ ⊗ ∣0⟩)) 3%nat 0%nat).
    set (b00 := (U × (∣1⟩ ⊗ ∣1⟩)) 0%nat 0%nat).
    set (b01 := (U × (∣1⟩ ⊗ ∣1⟩)) 1%nat 0%nat).
    set (b10 := (U × (∣1⟩ ⊗ ∣1⟩)) 2%nat 0%nat).
    set (b11 := (U × (∣1⟩ ⊗ ∣1⟩)) 3%nat 0%nat).
    set (a := (a00 * a11 - a01 * a10)%C).
    set (b := (a00 * b11 + a11 * b00 - a01 * b10 - a10 * b01)%C).
    set (c := (b00 * b11 - b01 * b10)%C).
    set (quad := Complex_sqrt (b * b - 4 * a * c)%C).
    set (p0 := (/ (2 * a)%C * (-b + quad))%C).
    set (c0 := 1 / √ ((Cmod p0)^2 + 1)%R).
    set (psi0 := c0 * p0 .* ∣0⟩ .+ c0 .* ∣1⟩).
    exists psi0.
    assert (div_g0: 0 < Cmod p0 ^ 2 + 1). 
    {
        rewrite <- Rplus_0_l with (r:= 0).
        apply Rplus_le_lt_compat. 2: lra.
        apply Rsqr_ge_0.
    }
    split. 
    {
        unfold WF_Qubit.
        split. exists (1%nat). trivial.
        split. solve_WF_matrix.
        rewrite vector2_inner_prod_decomp.
        unfold psi0.
        repeat rewrite Mplus_access.
        repeat rewrite <- Mscale_access.
        simpl.
        repeat rewrite Cmult_0_r.
        repeat rewrite Cmult_1_r.
        repeat rewrite Cplus_0_l, Cplus_0_r.
        rewrite Cconj_mult_distr.
        rewrite <- Cmult_assoc.
        rewrite Cmult_comm with (x := p0^*).
        rewrite <- Cmult_assoc. rewrite Cmult_assoc at 1.
        rewrite <- Cmult_1_r with (x:= c0 ^* * c0) at 2.
        rewrite <- Cmult_plus_distr_l with (x:= c0 ^* * c0).
        assert (expansion: c0^* * c0 = C1 / (Cmod p0 ^ 2 + 1)).
        {
            unfold c0.
            repeat rewrite <- RtoC_div.
            rewrite RtoC_conj.
            rewrite <- RtoC_mult.
            rewrite Rfrac_product with (a:= 1) .
            rewrite sqrt_sqrt.
            rewrite Rmult_1_l.
            rewrite RtoC_div.
            rewrite RtoC_plus.
            rewrite RtoC_pow.
            reflexivity.
            3,4,5: apply g0_sqn0.
            apply Rgt_not_eq.
            apply Rlt_gt.
            2: apply Rlt_le.
            all: apply div_g0.
        }
        rewrite expansion.
        rewrite Cmult_comm with (x:= p0).
        rewrite <- Cmod_sqr.
        unfold Cdiv.
        rewrite Cmult_1_l.
        apply Cinv_l.
        unfold not.
        intro.
        apply complex_split in H0.
        destruct H0.
        apply eq_sym in H0.
        revert H0.
        rewrite RtoC_pow.
        rewrite <- RtoC_plus.
        unfold RtoC.
        simpl.
        apply Rlt_not_eq.
        replace ((Cmod p0 * (Cmod p0 * 1))%R) with ((Cmod p0 ^ 2)%R) by lra.
        assumption.
    }
    apply a20. solve_WF_matrix.
    assert (psi0_def: psi0 = c0 * p0 .* ∣0⟩ .+ c0 .* ∣1⟩). unfold psi0. reflexivity.
    assert (prod_decomp: U × (∣1⟩ ⊗ psi0) = U × (∣1⟩ ⊗ psi0)). reflexivity.
    rewrite psi0_def in prod_decomp at 2.
    rewrite kron_plus_distr_l in prod_decomp.
    repeat rewrite Mscale_kron_dist_r in prod_decomp.
    rewrite Mmult_plus_distr_l in prod_decomp.
    repeat rewrite Mscale_mult_dist_r in prod_decomp.
    assert (def0: (U × (∣1⟩ ⊗ psi0)) 0%nat 0%nat = c0 * p0 * a00 + c0 * b00).
    {
        rewrite prod_decomp.
        rewrite Mplus_access.
        repeat rewrite <- Mscale_access.
        unfold a00, b00.
        reflexivity.
    }
    assert (def1: (U × (∣1⟩ ⊗ psi0)) 1%nat 0%nat = c0 * p0 * a01 + c0 * b01).
    {
        rewrite prod_decomp.
        rewrite Mplus_access.
        repeat rewrite <- Mscale_access.
        unfold a01, b01.
        reflexivity.
    }
    assert (def2: (U × (∣1⟩ ⊗ psi0)) 2%nat 0%nat = c0 * p0 * a10 + c0 * b10).
    {
        rewrite prod_decomp.
        rewrite Mplus_access.
        repeat rewrite <- Mscale_access.
        unfold a10, b10.
        reflexivity.
    }
    assert (def3: (U × (∣1⟩ ⊗ psi0)) 3%nat 0%nat = c0 * p0 * a11 + c0 * b11).
    {
        rewrite prod_decomp.
        rewrite Mplus_access.
        repeat rewrite <- Mscale_access.
        unfold a11, b11.
        reflexivity.
    }
    rewrite def0, def1, def2, def3.
    repeat rewrite <- Cmult_assoc.
    repeat rewrite <- Cmult_plus_distr_l.
    repeat rewrite <- Cmult_assoc.
    rewrite Cmult_comm with (x := (p0 * a00 + b00)).
    rewrite Cmult_comm with (x := (p0 * a01 + b01)).
    rewrite <- Cmult_assoc.
    rewrite Cmult_assoc with (y := c0).
    rewrite <- Cmult_assoc with (y := (p0 * a10 + b10)).
    rewrite Cmult_assoc with (y := c0).
    apply Cmult_simplify. reflexivity.
    rewrite <- Cplus_0_l with (x := (p0 * a11 + b11) * (p0 * a00 + b00)).
    rewrite <- Cplus_0_r with (x := (p0 * a10 + b10) * (p0 * a01 + b01)).
    rewrite <- Cplus_opp_r with (x := (p0 * a10 + b10) * (p0 * a01 + b01)) at 1.
    rewrite <- Cplus_assoc.
    apply Cplus_simplify. reflexivity.
    assert (replace_helper: forall (p0 a10 b10 a01 b01 a11 b11 a00 b00: C), 
    - ((p0 * a10 + b10) * (p0 * a01 + b01)) + (p0 * a11 + b11) * (p0 * a00 + b00) = 
    p0 ^ 2 * (a00 * a11 - a01 * a10) + p0 * (a00 * b11 + a11 * b00 - a01 * b10 - a10 * b01) + 
    (b00 * b11 - b01 * b10)). intros. lca.
    rewrite replace_helper.
    fold a b c.
    apply quadratic_formula. 2: unfold p0. 2: reflexivity.
    (* follows from U00 not a tensor prod *)
    unfold a. unfold not. intro.
    apply H.
    rewrite a20; solve_WF_matrix.
    apply (f_equal (fun f => f + a01 * a10)) in H0.
    rewrite Cplus_0_l in H0.
    unfold a00, a11, a01, a10 in H0.
    rewrite <- H0 at 1.
    lca.
}
Qed.

Lemma a22: forall (U: Square 4) (a b g psi : Vector 2) (phi : Vector 4), 
WF_Unitary U -> WF_Qubit a -> WF_Qubit b -> WF_Qubit g -> WF_Qubit psi -> WF_Qubit phi -> 
(acgate U) × (a ⊗ b ⊗ g) = psi ⊗ phi -> 
exists (w : Vector 2), WF_Qubit w /\ phi = b ⊗ w.
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
    rewrite (@kron_adjoint 2 1 4 1).
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
rewrite <- Mscale_0_l with (A := I 1) in outer_prod_equiv.
apply Mscale_cancel_r in outer_prod_equiv. 2: apply I_neq_zero. 2: lia.
symmetry in outer_prod_equiv. apply trace_outer_zero_vec2 in outer_prod_equiv. 2: assumption.
(* replace this in phi to finish proof *)
rewrite outer_prod_equiv in phi_decomp.
rewrite kron_0_r in phi_decomp.
rewrite Mplus_0_r in phi_decomp.
exists w.
split.
{
    split. exists 1%nat. trivial.
    split. assumption.
    rewrite <- Cmult_1_l at 1.
    destruct b_qubit as [_ [_ b_unit]].
    rewrite <- b_unit at 1.
    rewrite <- kron_inner_prod.
    rewrite <- phi_decomp.
    apply phi_qubit.
}
apply phi_decomp.
Qed.

Lemma a23 : forall (U : Square 4), WF_Unitary U ->
  (forall (x : Vector 2), WF_Qubit x -> TensorProdQubit (U × (x ⊗ ∣0⟩))) ->
  (exists (psi: Vector 2), WF_Qubit psi /\
    forall (x: Vector 2), WF_Qubit x ->
      exists (z: Vector 2), WF_Qubit z /\ U × (x ⊗ ∣0⟩) = z ⊗ psi) \/
  (exists (psi: Vector 2), WF_Qubit psi /\
    forall (x: Vector 2), WF_Qubit x ->
      exists (z: Vector 2), WF_Qubit z /\ U × (x ⊗ ∣0⟩) = psi ⊗ z).
Proof.
intros U U_unitary tensorProp.
assert (ts0 : TensorProdQubit (U × (∣0⟩ ⊗ ∣0⟩))). apply tensorProp, qubit0_qubit.
assert (ts1 : TensorProdQubit (U × (∣1⟩ ⊗ ∣0⟩))). apply tensorProp, qubit1_qubit.
assert (tsp : TensorProdQubit (U × (∣+⟩ ⊗ ∣0⟩))).
{
  apply tensorProp, xbasis_plus_qubit.
}
unfold TensorProdQubit in ts0, ts1, tsp.
assert (WF_Matrix (U × (∣0⟩ ⊗ ∣0⟩))). solve_WF_matrix.
apply ts0 in H. clear ts0.
destruct H as [a0 [b0 [a0_qubit [b0_qubit a0b0_def]]]].
assert (temp: WF_Qubit a0). assumption.
destruct temp as [_ [WF_a0 a0_unit]].
assert (temp: WF_Qubit b0). assumption.
destruct temp as [_ [WF_b0 b0_unit]].
assert (WF_Matrix (U × (∣1⟩ ⊗ ∣0⟩))). solve_WF_matrix.
apply ts1 in H. clear ts1.
destruct H as [a1 [b1 [a1_qubit [b1_qubit a1b1_def]]]].
assert (temp: WF_Qubit a1). assumption.
destruct temp as [_ [WF_a1 a1_unit]].
assert (temp: WF_Qubit b1). assumption.
destruct temp as [_ [WF_b1 b1_unit]].
assert (WF_Matrix (U × (∣+⟩ ⊗ ∣0⟩))). solve_WF_matrix.
apply tsp in H. clear tsp.
destruct H as [ap [bp [ap_qubit [bp_qubit apbp_def]]]].
destruct ap_qubit as [_ [WF_ap ap_unit]].
destruct bp_qubit as [_ [WF_bp bp_unit]].
assert (Main1: ap ⊗ bp = / (√ 2) .* (a0 ⊗ b0 .+ a1 ⊗ b1)).
{
    rewrite <- apbp_def.
    unfold "∣+⟩".
    rewrite Mscale_kron_dist_l.
    rewrite Mscale_mult_dist_r.
    rewrite kron_plus_distr_r.
    rewrite Mmult_plus_distr_l.
    rewrite <- a0b0_def. 
    rewrite <- a1b1_def.
    reflexivity.
}
assert (temp := exists_orthogonal_qubit b0 b0_qubit).
destruct temp as [b0_orth [b0orth_qubit b0_is_orth]].
assert (temp : WF_Qubit b0_orth). assumption. 
destruct temp as [_ [WF_b0orth b0orth_unit]].
apply inner_prod_0_comm in b0_is_orth. 2,3: assumption.
assert(Main2: ⟨ b0_orth, bp ⟩ .* ap = / √ 2 * ⟨ b0_orth, b1 ⟩ .* a1).
{
    apply (f_equal (fun f => (I 2 ⊗ b0_orth†) × f)) in Main1.
    rewrite kron_mixed_product in Main1.
    rewrite Mmult_1_l in Main1. 2: assumption.
    rewrite kron_11_r_is_scale in Main1.
    assert (ip_fold_helper: ((b0_orth) † × bp) 0%nat 0%nat = ⟨ b0_orth, bp⟩). unfold inner_product. reflexivity.
    rewrite ip_fold_helper in Main1. clear ip_fold_helper.
    rewrite Mscale_mult_dist_r in Main1.
    rewrite Mmult_plus_distr_l in Main1.
    rewrite kron_mixed_product in Main1.
    rewrite kron_11_r_is_scale in Main1.
    assert (ip_fold_helper: ((b0_orth) † × b0) 0%nat 0%nat = ⟨ b0_orth, b0⟩). unfold inner_product. reflexivity.
    rewrite ip_fold_helper in Main1. clear ip_fold_helper.
    rewrite b0_is_orth in Main1.
    rewrite Mscale_0_l in Main1. 
    rewrite Mplus_0_l in Main1.
    rewrite kron_mixed_product in Main1.
    rewrite Mmult_1_l in Main1. 2: assumption.
    rewrite kron_11_r_is_scale in Main1.
    assert (ip_fold_helper: ((b0_orth) † × b1) 0%nat 0%nat = ⟨ b0_orth, b1⟩). unfold inner_product. reflexivity.
    rewrite ip_fold_helper in Main1. clear ip_fold_helper.
    rewrite Mscale_assoc in Main1.
    assumption.
}
assert (casework: (⟨ b0_orth, bp ⟩ = C0) /\ (/(sqrt 2) * ⟨ b0_orth, b1 ⟩ = C0) \/ linearly_dependent_2vec ap a1).
{
    apply scale_eq_implies_0l_or_ldep.
    all: assumption.
}
destruct casework as [blindep|alindep].
{
    destruct blindep as [bpb0orth b1b0orth].
    apply (f_equal (fun f => √ 2 * f)) in b1b0orth.
    rewrite Cmult_0_r in b1b0orth.
    rewrite Cmult_assoc in b1b0orth.
    rewrite Cinv_r in b1b0orth. 2: apply Csqrt2_neq_0.
    rewrite Cmult_1_l in b1b0orth.
    assert (blindep: linearly_dependent_2vec b0 b1).
    {
        rewrite inner_prod_0_comm in b0_is_orth, b1b0orth.
        apply both_orth_qubit_implies_lin_dep2 with (b:= b0_orth).
        all: assumption.
    }
    rewrite lin_dep_def_alt in blindep. 2,3: assumption.
    destruct blindep as [b00 | proportional].
    {
        contradict b0_unit.
        rewrite <- inner_product_zero_iff_zero in b00. 2: assumption.
        rewrite b00.
        unfold not. 
        intro.
        apply eq_sym in H.
        apply C1_neq_C0.
        assumption.
    }
    {
        destruct proportional as [c lindepeq].
        left.
        exists b0.
        split. exact b0_qubit.
        intros x x_qubit.
        exists (x 0%nat 0%nat .* a0 .+ x 1%nat 0%nat .* (c .* a1)).
        assert (WF_Qubit (x 0%nat 0%nat .* a0 .+ x 1%nat 0%nat .* (c .* a1))).
        {
          unfold WF_Qubit.
          {
            split.
            {
              exists 1%nat.
              compute.
              reflexivity.
            }
            split.
            {
              solve_WF_matrix.
            }
            {
              assert (U × (x ⊗ ∣0⟩) = (x 0%nat 0%nat .* a0 .+ x 1%nat 0%nat .* (c .* a1)) ⊗ b0).
              {
                rewrite qubit_decomposition1 with (phi:= x) at 1. 2: apply x_qubit.
                rewrite kron_plus_distr_r.
                rewrite Mmult_plus_distr_l.
                do 2 rewrite Mscale_kron_dist_l.
                do 2 rewrite Mscale_mult_dist_r.
                assert (def_help: (U × (∣0⟩ ⊗ ∣0⟩)) = a0 ⊗ b0). apply a0b0_def.
                rewrite def_help at 1. clear def_help.
                assert (def_help: (U × (∣1⟩ ⊗ ∣0⟩)) = a1 ⊗ b1). apply a1b1_def.
                rewrite def_help at 1. clear def_help.
                rewrite <- lindepeq.
                rewrite kron_plus_distr_r.
                repeat rewrite Mscale_kron_dist_l.
                repeat rewrite Mscale_kron_dist_r.
                reflexivity.
              }
              rewrite <- Cmult_1_r at 1.
              rewrite <- b0_unit at 1.
              rewrite <- inner_product_kron.
              rewrite <- H.
              rewrite inner_product_adjoint_l.
              destruct U_unitary as [WF_U U_unitary].
              rewrite <- Mmult_assoc.
              rewrite U_unitary at 1.
              rewrite Mmult_1_l; solve_WF_matrix.
              rewrite (@inner_product_kron 2 2)%nat.
              destruct x_qubit as [_ [WF_x x_unit]].
              rewrite x_unit.
              unfold inner_product, qubit0, adjoint, Mmult; lca.
            }
          }
        }
        split. assumption.
        rewrite qubit_decomposition1 with (phi:= x) at 1. 2: apply x_qubit.
        rewrite kron_plus_distr_r.
        rewrite Mmult_plus_distr_l.
        do 2 rewrite Mscale_kron_dist_l.
        do 2 rewrite Mscale_mult_dist_r.
        assert (def_help: (U × (∣0⟩ ⊗ ∣0⟩)) = a0 ⊗ b0). apply a0b0_def.
        rewrite def_help at 1. clear def_help.
        assert (def_help: (U × (∣1⟩ ⊗ ∣0⟩)) = a1 ⊗ b1). apply a1b1_def.
        rewrite def_help at 1. clear def_help.
        rewrite <- lindepeq.
        rewrite Mscale_kron_dist_r.
        rewrite <- Mscale_kron_dist_l.
        rewrite kron_plus_distr_r.
        replace (x 0%nat 0%nat .* a0 ⊗ b0) with (x 0%nat 0%nat .* (a0 ⊗ b0)). 2: symmetry. 2: apply Mscale_kron_dist_l.
        replace (x 1%nat 0%nat .* (c .* a1) ⊗ b0) with (x 1%nat 0%nat .* (c .* a1 ⊗ b0)).
        reflexivity.
        lma'.
    }
}
{
    assert (linearly_dependent_2vec a0 a1).
    {
        unfold linearly_dependent_2vec, not.
        intro a10indep.
        apply lin_dep_comm_2vec in alindep.
        apply lin_dep_def_alt in alindep. 2,3: assumption.
        destruct alindep as [contr | proportional].
        {
            contradict a1_unit.
            rewrite <- inner_product_zero_iff_zero in contr. 2: assumption.
            rewrite contr.
            unfold not.
            intro.
            apply eq_sym in H.
            apply C1_neq_C0. 
            assumption.
        }
        {
            destruct proportional as [c  prop].
            rewrite <- prop in Main1.
            rewrite Mscale_kron_dist_l in Main1.
            rewrite <- Mscale_kron_dist_r in Main1.
            apply eq_sym in Main1.
            rewrite Mscale_plus_distr_r in Main1.
            do 2 rewrite <- Mscale_kron_dist_r in Main1.
            apply (f_equal (fun f => f .+ Mopp (a1 ⊗ (c .* bp)))) in Main1.
            rewrite Mplus_opp_0_r in Main1. 2: solve_WF_matrix.
            unfold Mopp in Main1.
            rewrite <- Mscale_kron_dist_r in Main1.
            rewrite Mplus_assoc in Main1.
            rewrite <- kron_plus_distr_l in Main1.
            assert (contr: / √ 2 .* b0 = Zero).
            {
                apply a16b_vec2_part2 with (a0 := a0) (a1 := a1) (w1 := (/ √ 2 .* b1 .+ - C1 .* (c .* bp))).
                1,2: solve_WF_matrix.
                all: assumption.
            }
            rewrite <- Mscale_0_r with (c := / √ 2) in contr.
            apply Mscale_cancel_l in contr.
            apply C1_neq_C0.
            rewrite <- b0_unit.
            apply inner_product_zero_iff_zero in contr. 2: assumption.
            assumption.
            unfold not. 
            intro.
            apply (f_equal (fun f => f * √ 2)) in H.
            rewrite Cmult_0_l in H.
            rewrite Cinv_l in H.
            revert H.
            apply C1_neq_C0.
            apply Csqrt2_neq_0.
        }
    }
    rewrite lin_dep_def_alt in H. 2,3: assumption.
    destruct H as [a00 | proportional].
    {
        contradict a0_unit.
        rewrite <- inner_product_zero_iff_zero in a00. 2: assumption.
        rewrite a00.
        unfold not. 
        intro.
        apply eq_sym in H.
        apply C1_neq_C0.
        assumption.
    }
    {
        destruct proportional as [c prop].
        right.
        exists a0.
        split. exact a0_qubit.
        intros x x_qubit.
        exists (x 0%nat 0%nat .* b0 .+ x 1%nat 0%nat .* (c .* b1)).
        assert (WF_Qubit (x 0%nat 0%nat .* b0 .+ x 1%nat 0%nat .* (c .* b1))).
        {
          unfold WF_Qubit.
          {
            split.
            {
              exists 1%nat.
              compute.
              reflexivity.
            }
            split.
            {
              solve_WF_matrix.
            }
            {
              assert (U × (x ⊗ ∣0⟩) = a0 ⊗ (x 0%nat 0%nat .* b0 .+ x 1%nat 0%nat .* (c .* b1))).
              {
                rewrite qubit_decomposition1 with (phi:= x) at 1. 2: apply x_qubit.
                rewrite kron_plus_distr_r.
                rewrite Mmult_plus_distr_l.
                do 2 rewrite Mscale_kron_dist_l.
                do 2 rewrite Mscale_mult_dist_r.
                assert (def_help: (U × (∣0⟩ ⊗ ∣0⟩)) = a0 ⊗ b0). apply a0b0_def.
                rewrite def_help at 1. clear def_help.
                assert (def_help: (U × (∣1⟩ ⊗ ∣0⟩)) = a1 ⊗ b1). apply a1b1_def.
                rewrite def_help at 1. clear def_help.
                rewrite <- prop.
                rewrite kron_plus_distr_l.
                repeat rewrite Mscale_kron_dist_l.
                repeat rewrite Mscale_kron_dist_r.
                reflexivity.
              }
              rewrite <- Cmult_1_l at 1.
              rewrite <- a0_unit at 1.
              rewrite <- inner_product_kron.
              rewrite <- H.
              rewrite inner_product_adjoint_l.
              destruct U_unitary as [WF_U U_unitary].
              rewrite <- Mmult_assoc.
              rewrite U_unitary at 1.
              rewrite Mmult_1_l; solve_WF_matrix.
              rewrite (@inner_product_kron 2 2)%nat.
              destruct x_qubit as [_ [WF_x x_unit]].
              rewrite x_unit.
              unfold inner_product, qubit0, adjoint, Mmult; lca.
            }
          }
        }
        split. assumption.
        rewrite qubit_decomposition1 with (phi:= x) at 1. 2: apply x_qubit.
        rewrite kron_plus_distr_r.
        rewrite Mmult_plus_distr_l.
        do 2 rewrite Mscale_kron_dist_l.
        do 2 rewrite Mscale_mult_dist_r.
        assert (def_help: (U × (∣0⟩ ⊗ ∣0⟩)) = a0 ⊗ b0). apply a0b0_def.
        rewrite def_help at 1. clear def_help.
        assert (def_help: (U × (∣1⟩ ⊗ ∣0⟩)) = a1 ⊗ b1). apply a1b1_def.
        rewrite def_help at 1. clear def_help.
        rewrite <- prop.
        rewrite Mscale_kron_dist_l.
        rewrite <- Mscale_kron_dist_r.
        rewrite kron_plus_distr_l.
        replace (a0 ⊗ (x 0%nat 0%nat .* b0)) with (x 0%nat 0%nat .* (a0 ⊗ b0)). 2: symmetry. 2: apply Mscale_kron_dist_r.
        replace (a0 ⊗ (x 1%nat 0%nat .* (c .* b1))) with (x 1%nat 0%nat .*(a0 ⊗ (c .* b1))).
        reflexivity.
        lma'.
    }
}
Qed.

Lemma a24: forall (U V W00 W11 : Square 4), 
WF_Unitary U -> WF_Unitary V -> WF_Unitary W00 -> WF_Unitary W11 -> 
acgate U × abgate V = ∣0⟩⟨0∣ ⊗ W00 .+ ∣1⟩⟨1∣ ⊗ W11 -> 
exists (P0 Q0 P1 Q1 : Square 2), 
WF_Unitary P0 /\ WF_Unitary Q0 /\ WF_Unitary P1 /\ WF_Unitary Q1 /\
acgate U × abgate V = ∣0⟩⟨0∣ ⊗ P0 ⊗ Q0 .+ ∣1⟩⟨1∣ ⊗ P1 ⊗ Q1.
Proof.
intros U V W00 W11 U_unitary V_unitary W00_unitary W11_unitary acgate_mult.
assert (temp: WF_Unitary V). assumption.
destruct temp as [WF_V V_inv].
assert (temp: WF_Unitary W00). assumption.
destruct temp as [WF_W00 W00_inv].
assert (temp: WF_Unitary W11). assumption.
destruct temp as [WF_W11 W11_inv].
assert (temp:= a21 V V_unitary).
destruct temp as [psi0 [psi0_qubit tens]].
assert (temp: WF_Qubit psi0). assumption.
destruct temp as [_ [WF_psi0 psi0_unit]].
rewrite tensor_prod_of_qubit in tens.
2: {
    unfold WF_Qubit.
    split. exists 2%nat. trivial.
    split. solve_WF_matrix.
    rewrite <- unitary_preserves_inner_prod. 2: assumption. 2: solve_WF_matrix.
    assert (kip_help: ⟨ ∣0⟩ ⊗ psi0, ∣0⟩ ⊗ psi0 ⟩ = ⟨ ∣0⟩, ∣0⟩ ⟩ * ⟨ psi0, psi0 ⟩). apply kron_inner_prod.
    rewrite kip_help at 1. clear kip_help.
    replace (⟨ ∣0⟩, ∣0⟩ ⟩) with (C1) by lca.
    rewrite psi0_unit.
    apply Cmult_1_l.
}
assert (temp: WF_Matrix (V × (∣0⟩ ⊗ psi0))). solve_WF_matrix.
unfold TensorProdQubit in tens.
apply tens in temp. clear tens.
destruct temp as [a0 [b0 [a0_qubit [b0_qubit ab0_decomp]]]].
destruct (exists_unitary_mapping_qubit_to_0 a0 a0_qubit) as [M0 [M0_unitary M0_prop]].
assert (temp: WF_Unitary M0). assumption.
destruct temp as [WF_M0 M0_inv].
assert (prod_decomp_0pass: acgate U × abgate V = acgate U × (M0† ⊗ I 2 ⊗ I 2) × (M0 ⊗ I 2 ⊗ I 2) × abgate V).
{
    rewrite Mmult_assoc. rewrite Mmult_assoc.
    rewrite <- Mmult_assoc with (C:= abgate V).
    assert (kron_mix_help: (M0) † ⊗ I 2 ⊗ I 2 × (M0 ⊗ I 2 ⊗ I 2) = ((M0) † ⊗ I 2 × (M0 ⊗ I 2))  ⊗ (I 2 × (I 2))).
    apply kron_mixed_product.
    rewrite kron_mix_help at 1.
    rewrite kron_mixed_product.
    rewrite Mmult_1_l. 2: solve_WF_matrix.
    rewrite M0_inv.
    rewrite id_kron. rewrite id_kron. rewrite Mmult_1_l.
    reflexivity.
    apply WF_abgate. assumption.
}
assert (ac_0pass: forall (y: Vector 2), WF_Qubit y -> 
(exists (phi : Vector 4), WF_Matrix phi /\ acgate U × abgate V × (∣0⟩ ⊗ psi0 ⊗ y)  =  ∣0⟩ ⊗ phi)).
{
    intros y y_qubit.
    destruct y_qubit as [_ [WF_y y_unit]].
    exists (W00 × (psi0 ⊗ y)).
    split. solve_WF_matrix.
    rewrite acgate_mult.
    rewrite Mmult_plus_distr_r.
    rewrite kron_assoc. 2,3,4: solve_WF_matrix.
    repeat rewrite kron_mixed_product.
    repeat rewrite Mmult_assoc.
    rewrite Mmult10 at 1.
    rewrite Mmult_0_r. rewrite kron_0_l. rewrite Mplus_0_r.
    rewrite Mmult00 at 1.
    rewrite Mmult_1_r. 2: solve_WF_matrix.
    reflexivity.   
}
rewrite prod_decomp_0pass in ac_0pass.
assert ((forall y : Vector 2,
WF_Qubit y -> exists phi : Vector 4, WF_Matrix phi /\ acgate U × ((M0) † ⊗ I 2 ⊗ I 2)
  × (M0 ⊗ I 2 ⊗ I 2) ×  abgate V × (∣0⟩ ⊗ psi0 ⊗ y) = ∣0⟩ ⊗ phi) -> 
  (forall y : Vector 2,
  WF_Qubit y -> exists phi : Vector 4, WF_Matrix phi /\ acgate U × ((M0) † ⊗ I 2 ⊗ I 2)
    × (∣0⟩ ⊗ b0 ⊗ y) = ∣0⟩ ⊗ phi)).
{
    intros H y y_qubit.
    specialize (H y y_qubit).
    destruct H as [phi [WF_phi H]].
    exists phi.
    split. assumption.
    rewrite <- H.
    repeat rewrite Mmult_assoc.
    unfold abgate.
    rewrite kron_mixed_product.
    rewrite Mmult_1_l. 2: apply y_qubit.
    rewrite ab0_decomp at 1.
    rewrite kron_mixed_product.
    rewrite Mmult_1_l. 2: apply y_qubit.
    rewrite kron_mixed_product.
    rewrite Mmult_1_l. 2: apply b0_qubit.
    rewrite M0_prop.
    reflexivity.
}
assert (ac_0pass_cor: forall y : Vector 2, WF_Qubit y ->
exists phi : Vector 4, WF_Matrix phi /\
  acgate U × ((M0) † ⊗ I 2 ⊗ I 2)
  × (∣0⟩ ⊗ b0 ⊗ y) = ∣0⟩ ⊗ phi). apply H. assumption.
clear H ac_0pass.
assert (acgate_condense: acgate U × ((M0) † ⊗ I 2 ⊗ I 2) = acgate (U × ((M0) † ⊗ I 2))).
{
    unfold acgate at 2.
    unfold abgate.
    rewrite <- Mmult_1_l with (A:= I 2) at 4. 2: solve_WF_matrix.
    rewrite <- kron_mixed_product.
    rewrite <- Mmult_1_r with (A:= (U ⊗ I 2)). 2: solve_WF_matrix; apply U_unitary.
    simpl.
    rewrite <- swapbc_inverse.
    unfold acgate.
    unfold abgate.
    repeat rewrite Mmult_assoc.
    rewrite <- Mmult_assoc with (B := (M0) † ⊗ I 2 ⊗ I 2).
    rewrite swapbc_3gate. 2,3,4: solve_WF_matrix.
    reflexivity.
}
rewrite acgate_condense in ac_0pass_cor.
assert (ac_inner_unitary: WF_Unitary (U × ((M0) † ⊗ I 2))). 
{
    apply Mmult_unitary. apply U_unitary.
    apply kron_unitary. apply adjoint_unitary. assumption.
    apply id_unitary.
}
assert (acgate_diagblock_partial := acgate_diagblock (U × ((M0) † ⊗ I 2)) ac_inner_unitary).
assert (acgate_diag: exists TL BR : Square 4, WF_Unitary TL /\ WF_Unitary BR /\
 acgate (U × ((M0) † ⊗ I 2)) = ∣0⟩⟨0∣ ⊗ TL .+ ∣1⟩⟨1∣ ⊗ BR). 
{
    apply acgate_diagblock_partial.
    exists b0.
    split. assumption.
    assumption.
}
clear acgate_diagblock_partial.
destruct acgate_diag as [acdiagTL [acdiagBR [acdiagTL_unitary [acdiagBR_unitary acgate_diag]]]].
assert (acgate_2control_partial:= acgate_control (U × ((M0) † ⊗ I 2)) acdiagTL acdiagBR
ac_inner_unitary acdiagTL_unitary acdiagBR_unitary acgate_diag).
destruct (acgate_2control_partial) as [Q0 [Q1 [Q0_unitary [Q1_unitary acgate_inner_prop]]]].
assert (abgate_0passthru_int : forall (y : Vector 2), WF_Qubit y -> forall (x: Vector 2), WF_Qubit x ->  
(exists (phi : Vector 4), WF_Matrix phi /\ acgate U × abgate V × (∣0⟩ ⊗ x ⊗ y)  =  ∣0⟩ ⊗ phi)).
{
    intros y y_qubit x x_qubit.
    exists (W00 × (x ⊗ y)).
    split. solve_WF_matrix.
    rewrite acgate_mult.
    rewrite Mmult_plus_distr_r.
    rewrite kron_assoc. 4: apply y_qubit. 3: apply x_qubit. 2: solve_WF_matrix.
    repeat rewrite kron_mixed_product.
    repeat rewrite Mmult_assoc.
    rewrite Mmult10 at 1.
    rewrite Mmult_0_r. rewrite kron_0_l. rewrite Mplus_0_r.
    rewrite Mmult00 at 1.
    rewrite Mmult_1_r. 2: solve_WF_matrix.
    reflexivity.
}
assert (abgate_condense: M0 ⊗ I 2 ⊗ I 2 × abgate V = abgate ((M0 ⊗ I 2) × V)).
{
    unfold abgate.
    rewrite kron_mixed_product.
    rewrite Mmult_1_l. 2: solve_WF_matrix.
    reflexivity.
}
assert (abgate_0passthru: (exists (y: Vector 2), WF_Qubit y /\ 
forall (x : Vector 2), WF_Qubit x -> (exists (phi: Vector 4), WF_Matrix phi /\
(abgate ((M0 ⊗ I 2) × V)) × (∣0⟩ ⊗ x ⊗ y)  =  ∣0⟩ ⊗ phi))).
{
    exists ∣0⟩.
    split. apply qubit0_qubit.
    intros x x_qubit.
    specialize (abgate_0passthru_int ∣0⟩ qubit0_qubit x x_qubit).
    destruct abgate_0passthru_int as [phi [WF_phi abgate_0passthru_int]].
    rewrite prod_decomp_0pass in abgate_0passthru_int.
    rewrite acgate_condense in abgate_0passthru_int.
    apply (f_equal (fun f => (acgate (U × ((M0) † ⊗ I 2)))† × f)) in abgate_0passthru_int.
    assert (acgate_condensed_unit: WF_Unitary (acgate (U × ((M0) † ⊗ I 2)))).
    {
        apply acgate_unitary. assumption.   
    }
    destruct acgate_condensed_unit as [WF_condensed condensed_inv].
    repeat rewrite <- Mmult_assoc in abgate_0passthru_int.
    rewrite condensed_inv in abgate_0passthru_int at 1.
    rewrite Mmult_1_l in abgate_0passthru_int. 2: solve_WF_matrix.
    rewrite abgate_condense in abgate_0passthru_int at 1.
    rewrite acgate_diag in abgate_0passthru_int.
    rewrite Mplus_adjoint in abgate_0passthru_int.
    repeat rewrite kron_adjoint in abgate_0passthru_int.
    rewrite adjoint00, adjoint11 in abgate_0passthru_int.
    rewrite Mmult_plus_distr_r in abgate_0passthru_int.
    rewrite kron_mixed_product in abgate_0passthru_int.
    rewrite Mmult_assoc in abgate_0passthru_int.
    rewrite Mmult00 in abgate_0passthru_int at 1.
    rewrite Mmult_1_r in abgate_0passthru_int. 2: solve_WF_matrix.
    rewrite kron_mixed_product in abgate_0passthru_int.
    rewrite Mmult_assoc in abgate_0passthru_int.
    rewrite Mmult10 in abgate_0passthru_int at 1.
    rewrite Mmult_0_r in abgate_0passthru_int.
    rewrite kron_0_l in abgate_0passthru_int.
    rewrite Mplus_0_r in abgate_0passthru_int.
    exists ((acdiagTL) † × phi).
    split. solve_WF_matrix.
    assumption.
}
assert (ab_inner_unitary: WF_Unitary ((M0 ⊗ I 2) × V)). 
{
    apply Mmult_unitary.
    apply (@kron_unitary 2 2). assumption.
    apply id_unitary.
    assumption.
}
assert (abgate_diagblock_partial := abgate_diagblock (M0 ⊗ I 2 × V) ab_inner_unitary).
assert (abgate_diag: exists TL BR : Square 4,
WF_Unitary TL /\ WF_Unitary BR /\
abgate (M0 ⊗ I 2 × V) = ∣0⟩⟨0∣ ⊗ TL .+ ∣1⟩⟨1∣ ⊗ BR). 
{
    apply abgate_diagblock_partial.
    assumption.
}
clear abgate_diagblock_partial.
destruct abgate_diag as [abdiagTL [abdiagBR [abdiagTL_unitary [abdiagBR_unitary abgate_diag]]]].
assert (abgate_2control_partial:= abgate_control (M0 ⊗ I 2 × V) abdiagTL abdiagBR
ab_inner_unitary abdiagTL_unitary abdiagBR_unitary abgate_diag).
destruct (abgate_2control_partial) as [P0 [P1 [P0_unitary [P1_unitary abgate_inner_prop]]]].
exists P0, Q0, P1, Q1.
split. assumption.
split. assumption.
split. assumption.
split. assumption.
rewrite prod_decomp_0pass.
rewrite acgate_condense.
rewrite Mmult_assoc.
rewrite abgate_condense.
rewrite acgate_inner_prop.
rewrite abgate_inner_prop.
rewrite Mmult_plus_distr_l.
repeat rewrite Mmult_plus_distr_r.
repeat rewrite kron_mixed_product.
repeat rewrite isolate_inner_mult.
rewrite Mmult00, Mmult01, Mmult10, Mmult11.
repeat rewrite Mmult_0_r.
repeat rewrite Mmult_0_l.
repeat rewrite kron_0_l.
rewrite Mplus_0_l.
rewrite Mplus_0_r.
repeat rewrite Mmult_1_r.
repeat rewrite Mmult_1_l.
reflexivity.
apply P1_unitary.
apply P0_unitary.
apply Q1_unitary.
solve_WF_matrix.
apply Q0_unitary.
solve_WF_matrix.
Qed.

Lemma a25: forall (V : Square 4) (psi: Vector 2), 
WF_Unitary V -> WF_Qubit psi ->
(forall (x : Vector 2), WF_Qubit x -> 
(exists (phi : Vector 2), WF_Qubit phi /\ V × (x ⊗ ∣0⟩) = psi ⊗ phi )) -> 
(exists (Q : Square 2), WF_Unitary Q /\
(forall (x : Vector 2), WF_Qubit x -> V × (x ⊗ ∣0⟩) = psi ⊗ (Q × x))).
Proof. 
intros V psi V_unitary psi_qubit first_prop.
assert(temp: WF_Qubit psi). assumption.
destruct temp as [_ [WF_psi psi_unit]].
assert(w0_def:= first_prop qubit0 qubit0_qubit).
destruct w0_def as [w0 [w0_qubit w0_decomp]].
assert(temp: WF_Qubit w0). assumption. 
destruct temp as [_ [WF_w0 w0_unit]].
assert(w1_def:= first_prop qubit1 qubit1_qubit).
destruct w1_def as [w1 [w1_qubit w1_decomp]].
assert(temp: WF_Qubit w1). assumption. 
destruct temp as [_ [WF_w1 w1_unit]].
assert(orth_prop: ⟨ ∣0⟩ ⊗ ∣0⟩, ∣1⟩ ⊗ ∣0⟩ ⟩ = C0). lca.
rewrite unitary_preserves_inner_prod with (U := V) in orth_prop. 2,3: solve_WF_matrix.
rewrite w0_decomp in orth_prop at 1.
rewrite w1_decomp in orth_prop at 1.
rewrite kron_inner_prod in orth_prop.
rewrite psi_unit in orth_prop.
rewrite Cmult_1_l in orth_prop.
set (Q:= w0 × ⟨0∣ .+ w1 × ⟨1∣).
assert (Q_unitary: WF_Unitary Q). { unfold Q. apply orth_qubit_unitary. all: assumption. }
assert (forall (x: Vector 2), WF_Qubit x -> Q × x = (x 0%nat 0%nat) .* w0 .+ (x 1%nat 0%nat) .* w1).
{
    intros x x_qubit.
    rewrite (qubit_decomposition1 x) at 1. 2: apply x_qubit.
    unfold Q.
    rewrite Mmult_plus_distr_l.
    repeat rewrite Mmult_plus_distr_r.
    repeat rewrite Mmult_assoc.
    repeat rewrite Mscale_mult_dist_r.
    rewrite Mmult00, Mmult01, Mmult10, Mmult11.
    repeat rewrite Mmult_0_r.
    repeat rewrite Mscale_0_r.
    repeat rewrite Mmult_1_r. 2,3: assumption.
    rewrite Mplus_0_l, Mplus_0_r.
    reflexivity.
}
exists Q.
split. assumption.
intros x x_qubit.
assert (temp: WF_Qubit x). assumption.
destruct temp as [_ [WF_x x_unit]].
rewrite (qubit_decomposition1 x) at 1. 2: assumption.
rewrite kron_plus_distr_r.
do 2 rewrite Mscale_kron_dist_l.
rewrite Mmult_plus_distr_l.
do 2 rewrite Mscale_mult_dist_r.
rewrite w0_decomp at 1.
rewrite w1_decomp at 1.
rewrite <- Mscale_kron_dist_r with (A := psi) (B:= w0) (x:= x 0%nat 0%nat) at 1.
rewrite <- Mscale_kron_dist_r with (A := psi) (B:= w1) (x:= x 1%nat 0%nat) at 1.
rewrite <- kron_plus_distr_l with (A:= psi) (B:= (x 0%nat 0%nat .* w0)) (C:= (x 1%nat 0%nat .* w1)) at 1.
specialize (H x). apply H in x_qubit.
rewrite x_qubit.
reflexivity.
Qed.

Lemma a26: forall (U : Square 4), 
WF_Unitary U -> (forall (z : Vector 2), WF_Qubit z -> 
exists (b : Vector 2), WF_Qubit b /\ U × (z ⊗ ∣0⟩) = z ⊗ b )
-> exists (b : Vector 2), WF_Qubit b /\ forall (z: Vector 2), WF_Qubit z -> U × (z ⊗ ∣0⟩) = z ⊗ b.
Proof.
intros U U_unitary all_q_tensor.
assert (temp: WF_Qubit ∣0⟩). apply qubit0_qubit.
apply all_q_tensor in temp.
destruct temp as [b0 [b0_qubit b0_def]].
assert (temp: WF_Qubit b0). assumption.
destruct temp as [_ [WF_b0 b0_unit]].
assert (temp: WF_Qubit ∣1⟩). apply qubit1_qubit.
apply all_q_tensor in temp.
destruct temp as [b1 [b1_qubit b1_def]].
assert (temp: WF_Qubit b1). assumption.
destruct temp as [_ [WF_b1 b1_unit]].
assert (temp: WF_Qubit ∣+⟩).
{
    unfold WF_Qubit.
    split. exists 1%nat. trivial.
    split. solve_WF_matrix.
    unfold xbasis_plus.
    rewrite vector2_inner_prod_decomp.
    repeat rewrite <- Mscale_access.
    repeat rewrite Mplus_access.
    Csimpl.
    rewrite <- RtoC_inv.
    rewrite RtoC_conj.
    rewrite <- RtoC_mult.
    rewrite <- Rinv_mult.
    rewrite sqrt_sqrt.
    lca.
    lra.
    apply sqrt2_neq_0.
}
apply all_q_tensor in temp.
destruct temp as [bp [bp_qubit bp_def]].
assert (temp: WF_Qubit bp). assumption. 
destruct temp as [_ [WF_bp bp_unit]].
assert (First_way: U × (∣+⟩ ⊗ ∣0⟩) = ((/ √ 2) .* ∣0⟩) ⊗ b0 .+ ((/ √ 2) .* ∣1⟩) ⊗ b1).
{
    unfold xbasis_plus.
    repeat rewrite Mscale_kron_dist_l.
    rewrite Mscale_mult_dist_r.
    rewrite kron_plus_distr_r.
    rewrite Mmult_plus_distr_l.
    rewrite <- b0_def. rewrite <- b1_def.
    rewrite <- Mscale_plus_distr_r.
    reflexivity.
}
assert (Second_way: ∣+⟩ ⊗ bp = ((/ √ 2) .* ∣0⟩) ⊗ bp .+ ((/ √ 2) .* ∣1⟩) ⊗ bp).
{
    unfold xbasis_plus.
    repeat rewrite Mscale_kron_dist_l.
    rewrite kron_plus_distr_r.
    rewrite Mscale_plus_distr_r.
    reflexivity.
}
rewrite First_way, Second_way in bp_def.
apply (f_equal (fun f => f .+ Mopp (/ √ 2 .* ∣1⟩ ⊗ bp))) in bp_def.
repeat rewrite Mplus_assoc in bp_def.
rewrite Mplus_opp_0_r in bp_def. 2: solve_WF_matrix.
rewrite Mplus_0_r in bp_def.
unfold Mopp in bp_def.
rewrite <- Mscale_kron_dist_r in bp_def.
rewrite <- kron_plus_distr_l in bp_def.
rewrite Mplus_comm in bp_def.
apply (f_equal (fun f => f .+ Mopp (/ √ 2 .* ∣0⟩ ⊗ bp))) in bp_def.
rewrite Mplus_opp_0_r in bp_def. 2: solve_WF_matrix.
rewrite Mplus_assoc in bp_def.
unfold Mopp in bp_def.
rewrite <- Mscale_kron_dist_r in bp_def.
rewrite <- kron_plus_distr_l in bp_def.
repeat rewrite Mscale_kron_dist_l in bp_def.
rewrite <- Mscale_plus_distr_r in bp_def.
apply (f_equal (fun f => √ 2 .* f)) in bp_def.
rewrite Mscale_assoc in bp_def.
rewrite Cinv_r in bp_def. 2: apply Csqrt2_neq_0.
rewrite Mscale_1_l in bp_def.
rewrite Mscale_0_r in bp_def.
apply a16b_vec2 in bp_def. 2,3: solve_WF_matrix. 2: apply qubit1_qubit. 2: apply qubit0_qubit.
2: apply lin_indep_comm_2vec. 2: apply qubit_01_lin_indep.
destruct bp_def as [b1bp b0bp].
apply (f_equal (fun f => f .+ bp)) in b1bp, b0bp.
replace (b1 .+ - C1 .* bp .+ bp) with (b1) in b1bp by lma'.
replace (b0 .+ - C1 .* bp .+ bp) with (b0) in b0bp by lma'.
rewrite Mplus_0_l in b1bp,b0bp.
exists bp.
split. assumption.
intros z z_qubit.
assert (temp: WF_Qubit z). assumption. 
destruct temp as [_ [WF_z z_unit]].
assert (z_decomp:= qubit_decomposition1 z WF_z).
rewrite z_decomp.
rewrite kron_plus_distr_r.
repeat rewrite Mscale_kron_dist_l.
rewrite Mmult_plus_distr_l.
repeat rewrite Mscale_mult_dist_r.
assert (def_help: (U × (∣0⟩ ⊗ ∣0⟩)) = ∣0⟩ ⊗ b0). apply b0_def.
rewrite def_help at 1. clear def_help.
assert (def_help: (U × (∣1⟩ ⊗ ∣0⟩)) = ∣1⟩ ⊗ b1). apply b1_def.
rewrite def_help at 1. clear def_help.
rewrite b1bp. rewrite b0bp.
lma'.
Qed.
