Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.
From Proof Require Import MatrixHelpers.
From Proof Require Import QubitHelpers.
From Proof Require Import GateHelpers.
From Proof Require Import SwapHelpers.
From Proof Require Import AlgebraHelpers.
From Proof Require Import PartialTraceDefinitions.
From Proof Require Import UnitaryMatrices.
From Proof Require Import ExplicitDecompositions.
From Proof Require Import Vectors.

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
