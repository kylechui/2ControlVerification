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

Lemma exists_orthogonal_vector: forall (a: Vector 2), 
WF_Matrix a -> exists (b: Vector 2), (WF_Matrix b /\ (b = Zero <-> a = Zero) /\ ⟨ a , b ⟩ = C0).
Proof.
intros.
set (b := (fun x y =>
    match (x,y) with
    | (0,0) => -((a 1%nat 0%nat)^*)
    | (1,0) => (a 0%nat 0%nat)^*
    | _ => C0
    end) : (Vector 2)).
assert (WF_b: WF_Matrix b). 
{
    unfold WF_Matrix.
    intros.
    unfold b. 
    destruct H0.
    destruct x as [|x']. contradict H. lia.
    destruct x' as [|x'']. contradict H. lia. reflexivity.
    destruct x as [|x']. destruct y as [|y']. contradict H. lia. reflexivity.
    destruct x' as [|x'']. destruct y as [|y']. contradict H. lia.
    reflexivity. reflexivity.
}
exists b.
split. assumption.
split. split.
{
    intro.
    lma'.
    replace (a 0%nat 0%nat) with ((b 1%nat 0%nat)^*). rewrite H0. lca.
    unfold b. apply Cconj_involutive.
    replace (a 1%nat 0%nat) with (-(b 0%nat 0%nat)^*). rewrite H0. lca.
    unfold b. lca.
}
{
    intro.
    lma'.
    unfold b. rewrite H0. lca.
    unfold b. rewrite H0. lca.
}
lca.
Qed.

Lemma unitary_preserves_inner_prod {n}: forall (U: Square n) (a b: Vector n), WF_Unitary U -> WF_Matrix b ->
⟨ a , b ⟩ = ⟨ U × a , U × b ⟩.
Proof.
intros.
destruct H as [WF_U u_inv].
unfold inner_product.
rewrite Mmult_adjoint.
rewrite Mmult_assoc.
rewrite <- Mmult_assoc with (B := U).
rewrite u_inv. rewrite Mmult_1_l. 2: assumption.
reflexivity.
Qed.

Lemma kron_11_r_is_scale {m n}: forall (A : Matrix m n) (B : Vector 1),
A ⊗ B = (B 0%nat 0%nat) .* A.
Proof.
intros.
prep_matrix_equality.
unfold kron, scale.
do 2 rewrite Coq.Arith.PeanoNat.Nat.div_1_r.
simpl.
apply Cmult_comm.
Qed.

(* Lemma kron_11_l_is_scale {m n}: forall (B : Matrix m n) (A : Vector 1),
WF_Matrix A -> WF_Matrix B ->
A ⊗ B = (A 0%nat 0%nat) .* B.
Proof.
intros.
prep_matrix_equality.
unfold kron, scale.
destruct (le_gt_dec m x).
Qed. *)

Lemma lin_dep_comm_2vec {n}: forall (v1 v2 : Vector n), 
linearly_dependent_2vec v1 v2 <-> linearly_dependent_2vec v2 v1.
Proof. 
split.
all: intro.
all: unfold linearly_dependent_2vec in *.
all: unfold not in *.
all: intro.
all: apply H.
all: apply lin_indep_comm_2vec.
all: assumption.
Qed.

Lemma Mscale_0_cancel_r {n}: forall (a : C) (v : Vector n), 
a <> 0 -> a .* v = Zero -> v = Zero.
Proof.
intros.
apply (f_equal (fun f => /a .* f)) in H0.
rewrite Mscale_0_r in H0.
rewrite Mscale_assoc in H0.
rewrite Cinv_l in H0. 2: assumption.
rewrite Mscale_1_l in H0.
assumption.
Qed.

Lemma scale_eq_implies_0l_or_ldep {n}:
forall (a b: C) (u v: Vector n), 
WF_Matrix u -> WF_Matrix v -> 
a .* u = b .* v -> (a = 0 /\ b = 0) \/ linearly_dependent_2vec u v.
Proof.
intros.
destruct (Ceq_dec a C0).
destruct (Ceq_dec b C0).
{
    left. split. all: assumption. 
}
all: right.
2: rewrite lin_dep_comm_2vec.
all: rewrite lin_dep_def_alt. 2,3,5,6: assumption.
all: right.
apply (f_equal (fun f => /b .* f)) in H1.
2: apply (f_equal (fun f => /a .* f)) in H1.
all: repeat rewrite Mscale_assoc in H1.
all: rewrite Cinv_l in H1. 2,4: assumption.
all: rewrite Mscale_1_l in H1.
exists (/ b * a). assumption.
exists (/a * b). symmetry. assumption.
Qed.

Lemma cross_prod_equal_implies_scaled_vec: forall (a c: Vector 2),
WF_Matrix a -> WF_Matrix c ->
a 0%nat 0%nat <> 0 -> a 1%nat 0%nat <> 0 ->
(a 0%nat 0%nat) * (c 1%nat 0%nat) = (a 1%nat 0%nat) * (c 0%nat 0%nat) -> 
exists (b: C), b .* a = c.
Proof. 
intros a c WF_a WF_c a0n0 a1n0 cross.
exists ((c 0%nat 0%nat) * /(a 0%nat 0%nat)).
lma'.
{
    rewrite <- Mscale_access.
    rewrite <- Cmult_assoc.
    rewrite Cinv_l. 2: assumption.
    apply Cmult_1_r.
}
{
    assert (c 0%nat 0%nat * / a 0%nat 0%nat = c 1%nat 0%nat * / a 1%nat 0%nat).
    {
        apply (f_equal (fun f => / a 1%nat 0%nat * / a 0%nat 0%nat * f)) in cross.
        replace (/ a 1%nat 0%nat * / a 0%nat 0%nat *
        (a 0%nat 0%nat * c 1%nat 0%nat)) with ((a 0%nat 0%nat * / a 0%nat 0%nat) * c 1%nat 0%nat * / a 1%nat 0%nat) in cross by lca.
        rewrite Cinv_r in cross. 2: assumption. 
        rewrite Cmult_1_l in cross.
        replace (/ a 1%nat 0%nat * / a 0%nat 0%nat *
        (a 1%nat 0%nat * c 0%nat 0%nat)) with ((a 1%nat 0%nat * / a 1%nat 0%nat) * c 0%nat 0%nat * / a 0%nat 0%nat) in cross by lca.
        rewrite Cinv_r in cross. 2: assumption. 
        rewrite Cmult_1_l in cross.
        rewrite cross. reflexivity. 
    }
    rewrite H.
    rewrite <- Mscale_access.
    rewrite <- Cmult_assoc. 
    rewrite Cinv_l. 2: assumption.
    apply Cmult_1_r.
}
Qed.

Lemma conj_n0_iff_n0: forall (a : C), 
a <> 0 <-> a^* <> 0.
Proof.
split.
{
    intros.
    unfold not. 
    intro. 
    apply H.
    apply Cconj_simplify.
    rewrite Cconj_0.
    assumption.
}
{
    intros.
    unfold not. 
    intro. 
    apply H.
    rewrite H0.
    apply Cconj_0.
}
Qed.

Lemma both_orth_implies_lin_dep2: forall (a b c : Vector 2), 
WF_Matrix a -> WF_Matrix b -> WF_Matrix c ->
b <> Zero -> ⟨ a, b ⟩ = 0 -> ⟨ c, b ⟩ = 0 -> linearly_dependent_2vec a c.
Proof.
intros a b c WF_a WF_b WF_c bn0 ab_orth cb_orth.
rewrite lin_dep_def_alt. 2,3: assumption.
destruct (vec_equiv_dec a Zero).
{
    left.
    apply mat_equiv_eq.
    1,3: assumption.
    apply WF_Zero.
}
right.
assert (an0: a <> Zero). unfold not. intro. apply n. rewrite H. apply mat_equiv_refl.
destruct (vec_equiv_dec c Zero).
{
    exists C0.
    rewrite Mscale_0_l. symmetry.
    apply mat_equiv_eq.
    1,3: assumption.
    apply WF_Zero.
}
assert (cn0: c <> Zero). unfold not. intro. apply n0. rewrite H. apply mat_equiv_refl.
rewrite vector2_inner_prod_decomp in ab_orth, cb_orth.
(* casing by which b val is nonzero *)
set (a0 := a 0%nat 0%nat).
set (a1 := a 1%nat 0%nat).
set (b0 := b 0%nat 0%nat).
set (b1 := b 1%nat 0%nat).
set (c0 := c 0%nat 0%nat).
set (c1 := c 1%nat 0%nat).
fold a0 a1 b0 b1 in ab_orth.
fold c0 c1 b0 b1 in cb_orth.
destruct (Ceq_dec b0 C0).
{
    assert (b1 <> 0).
    {
        unfold not.
        intro.
        apply bn0.
        unfold b0 in e. 
        unfold b1 in H.
        lma'.
        rewrite e. lca.
        rewrite H. lca.
    }
    assert (a1 = 0).
    {
        rewrite e in ab_orth.
        rewrite Cmult_0_r in ab_orth.
        rewrite Cplus_0_l in ab_orth.
        apply Cconj_simplify.
        rewrite Cconj_0.
        apply Cmult_0_cancel_l with (a:= b1).
        assumption.
        rewrite Cmult_comm. assumption.
    }
    assert (c1 = 0).
    {
        rewrite e in cb_orth.
        rewrite Cmult_0_r in cb_orth.
        rewrite Cplus_0_l in cb_orth.
        apply Cconj_simplify.
        rewrite Cconj_0.
        apply Cmult_0_cancel_l with (a:= b1).
        assumption.
        rewrite Cmult_comm. assumption.
    }
    assert (a0 <> 0).
    {
        unfold not.
        intro.
        apply an0.
        unfold a0 in H2. 
        unfold a1 in H0.
        lma'.
        rewrite H2. lca.
        rewrite H0. lca.
    }
    exists (c0 * /a0).
    lma'.
    all: rewrite <- Mscale_access.
    fold a0 c0.
    rewrite <- Cmult_assoc.
    rewrite Cinv_l. 2: assumption.
    apply Cmult_1_r.
    fold a1 c1.
    rewrite H0, H1.
    apply Cmult_0_r.
}
destruct (Ceq_dec b1 C0).
{
    assert (a0 = 0).
    {
        rewrite e in ab_orth.
        rewrite Cmult_0_r in ab_orth.
        rewrite Cplus_0_r in ab_orth.
        apply Cconj_simplify.
        rewrite Cconj_0.
        apply Cmult_0_cancel_l with (a:= b0).
        assumption.
        rewrite Cmult_comm. assumption.
    }
    assert (c0 = 0).
    {
        rewrite e in cb_orth.
        rewrite Cmult_0_r in cb_orth.
        rewrite Cplus_0_r in cb_orth.
        apply Cconj_simplify.
        rewrite Cconj_0.
        apply Cmult_0_cancel_l with (a:= b0).
        assumption.
        rewrite Cmult_comm. assumption.
    }
    assert (a1 <> 0).
    {
        unfold not.
        intro.
        apply an0.
        unfold a0 in H. 
        unfold a1 in H1.
        lma'.
        rewrite H. lca.
        rewrite H1. lca.
    }
    exists (c1 * /a1).
    lma'.
    all: rewrite <- Mscale_access.
    fold a0 c0.
    rewrite H0, H.
    apply Cmult_0_r.
    fold a1 c1.
    rewrite <- Cmult_assoc.
    rewrite Cinv_l. 2: assumption.
    apply Cmult_1_r.
}
{
    assert (a0n0: a0 <> 0).
    {
        unfold not. 
        intro. 
        apply an0.
        lma'.
        fold a0. rewrite H. lca.
        rewrite H in ab_orth.
        rewrite Cconj_0 in ab_orth.
        rewrite Cmult_0_l in ab_orth.
        rewrite Cplus_0_l in ab_orth.
        rewrite Cmult_comm in ab_orth.
        apply Cmult_0_cancel_l in ab_orth. 2: assumption.
        rewrite <- Cconj_0 in ab_orth.
        apply Cconj_simplify in ab_orth.
        fold a1.
        rewrite ab_orth.
        lca.
    }
    assert (a1n0: a1 <> 0).
    {
        unfold not. 
        intro. 
        apply an0.
        lma'.
        rewrite H in ab_orth.
        rewrite Cconj_0 in ab_orth.
        rewrite Cmult_0_l in ab_orth.
        rewrite Cplus_0_r in ab_orth.
        rewrite Cmult_comm in ab_orth.
        apply Cmult_0_cancel_l in ab_orth. 2: assumption.
        rewrite <- Cconj_0 in ab_orth.
        apply Cconj_simplify in ab_orth.
        fold a0.
        rewrite ab_orth.
        lca.
        fold a1. rewrite H. lca.
    }
    assert (c0n0: c0 <> 0).
    {
        unfold not. 
        intro. 
        apply cn0.
        lma'.
        fold c0. rewrite H. lca.
        rewrite H in cb_orth.
        rewrite Cconj_0 in cb_orth.
        rewrite Cmult_0_l in cb_orth.
        rewrite Cplus_0_l in cb_orth.
        rewrite Cmult_comm in cb_orth.
        apply Cmult_0_cancel_l in cb_orth. 2: assumption.
        rewrite <- Cconj_0 in cb_orth.
        apply Cconj_simplify in cb_orth.
        fold c1.
        rewrite cb_orth.
        lca.
    }
    apply (f_equal (fun f => f * /b1)) in ab_orth, cb_orth.
    rewrite Cmult_0_l in ab_orth, cb_orth.
    rewrite Cmult_plus_distr_r in ab_orth, cb_orth.
    revert ab_orth.
    rewrite <- Cmult_assoc with (x := a1^*).
    rewrite Cinv_r. 2: assumption.
    rewrite Cmult_1_r.
    intro ab_orth.
    apply (f_equal (fun f => f - a1^*)) in ab_orth.
    replace (a0 ^* * b0 * / b1 + a1 ^* - a1 ^*) with (a0 ^* * b0 * / b1) in ab_orth by lca.
    replace (0 - a1 ^*) with (- a1 ^*) in ab_orth by lca.
    apply (f_equal (fun f => /(a0^*) * f)) in ab_orth.
    repeat rewrite Cmult_assoc in ab_orth.
    rewrite Cinv_l in ab_orth. 2: apply conj_n0_iff_n0. 2: rewrite Cconj_involutive. 2: assumption.
    rewrite Cmult_1_l in ab_orth.
    revert cb_orth.
    rewrite <- Cmult_assoc with (x := c1^*).
    rewrite Cinv_r. 2: assumption.
    rewrite Cmult_1_r.
    intro cb_orth.
    apply (f_equal (fun f => f - c1^*)) in cb_orth.
    replace (c0 ^* * b0 * / b1 + c1 ^* - c1 ^*) with (c0 ^* * b0 * / b1) in cb_orth by lca.
    replace (0 - c1 ^*) with (- c1 ^*) in cb_orth by lca.
    apply (f_equal (fun f => /(c0^*) * f)) in cb_orth.
    repeat rewrite Cmult_assoc in cb_orth.
    rewrite Cinv_l in cb_orth. 2: apply conj_n0_iff_n0. 2: rewrite Cconj_involutive. 2: assumption.
    rewrite Cmult_1_l in cb_orth.
    assert (cross_prod: / a0 ^* * - a1 ^* = / c0 ^* * - c1 ^*). rewrite <- ab_orth. apply cb_orth.
    apply cross_prod_equal_implies_scaled_vec.
    1,2: assumption. 
    fold a0. assumption. 
    fold a1. assumption.
    do 2 rewrite <- Copp_mult_distr_r in cross_prod.
    apply (f_equal (fun f => -f)) in cross_prod.
    do 2 rewrite Copp_involutive in cross_prod.
    apply (f_equal (fun f => c0^* * a0^* * f)) in cross_prod.
    replace (c0 ^* * a0 ^* * (/ a0 ^* * a1 ^*)) with (a0 ^* * / a0 ^* * a1 ^* * c0 ^*) in cross_prod by lca.
    rewrite Cinv_r in cross_prod. 2: apply conj_n0_iff_n0. 2: rewrite Cconj_involutive. 2: assumption.
    rewrite Cmult_1_l in cross_prod.
    replace (c0 ^* * a0 ^* * (/ c0 ^* * c1 ^*)) with (c0 ^* * / c0 ^* * a0 ^* * c1 ^*) in cross_prod by lca.
    rewrite Cinv_r in cross_prod. 2: apply conj_n0_iff_n0. 2: rewrite Cconj_involutive. 2: assumption.
    rewrite Cmult_1_l in cross_prod.
    do 2 rewrite <- Cconj_mult_distr in cross_prod.
    apply Cconj_simplify in cross_prod.
    fold a1 c1 a0 c0.
    symmetry. apply cross_prod.
}
Qed.


Lemma a23: forall (U : Square 4), WF_Unitary U -> (forall (x : Vector 2), TensorProd (U × (x ⊗ ∣0⟩))) ->
(exists (psi: Vector 2), forall (x: Vector 2), exists (z: Vector 2), U × (x ⊗ ∣0⟩) = z ⊗ psi
\/
exists (psi: Vector 2), forall (x: Vector 2), exists (z: Vector 2), U × (x ⊗ ∣0⟩) = psi ⊗ z).
Proof. 
intros U U_unitary tensorProp.
assert (ts0 : TensorProd (U × (∣0⟩ ⊗ ∣0⟩))). apply tensorProp.
assert (ts1 : TensorProd (U × (∣1⟩ ⊗ ∣0⟩))). apply tensorProp.
assert (tsP : TensorProd (U × (∣+⟩ ⊗ ∣0⟩))). apply tensorProp.
unfold TensorProd in ts0, ts1, tsP.
assert (WF_Matrix (U × (∣0⟩ ⊗ ∣0⟩))). solve_WF_matrix. apply U_unitary.
apply ts0 in H. clear ts0.
destruct H as [a0 [b0 [WF_a0 [WF_b0 a0b0_def]]]].
assert (WF_Matrix (U × (∣1⟩ ⊗ ∣0⟩))). solve_WF_matrix. apply U_unitary.
apply ts1 in H. clear ts1.
destruct H as [a1 [b1 [WF_a1 [WF_b1 a1b1_def]]]].
assert (WF_Matrix (U × (∣+⟩ ⊗ ∣0⟩))). solve_WF_matrix. apply U_unitary.
apply tsP in H. clear tsP.
destruct H as [ap [bp [WF_ap [WF_bp apbp_def]]]].
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
assert (temp := exists_orthogonal_vector b0 WF_b0).
destruct temp as [b0_orth [WF_b0_orth [b0_orth_zero_cond b0_is_orth]]].
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
apply inner_prod_0_comm in b0_is_orth. 2,3: assumption.
rewrite b0_is_orth in Main1.
rewrite Mscale_0_l in Main1. 
rewrite Mplus_0_l in Main1.
rewrite kron_mixed_product in Main1.
rewrite Mmult_1_l in Main1. 2: assumption.
rewrite kron_11_r_is_scale in Main1.
assert (ip_fold_helper: ((b0_orth) † × b1) 0%nat 0%nat = ⟨ b0_orth, b1⟩). unfold inner_product. reflexivity.
rewrite ip_fold_helper in Main1. clear ip_fold_helper.
rewrite Mscale_assoc in Main1.
assert (casework: (⟨ b0_orth, bp ⟩ = C0) /\ (/(sqrt 2) * ⟨ b0_orth, b1 ⟩ = C0) \/ linearly_dependent_2vec ap a1).
{
    apply scale_eq_implies_0l_or_ldep.
    all: assumption.
}
Admitted.
