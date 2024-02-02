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
WF_Qubit psi /\ TensorProd (U × (∣0⟩ ⊗ psi)).
Proof. 
intros U WF_U.
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

Lemma both_orth_qubit_implies_lin_dep2: forall (a b c : Vector 2), 
WF_Qubit a -> WF_Qubit b -> WF_Qubit c ->
⟨ a, b ⟩ = 0 -> ⟨ c, b ⟩ = 0 -> linearly_dependent_2vec a c.
Proof.
intros a b c a_qubit b_qubit c_qubit ab_orth cb_orth.
destruct a_qubit as [_ [WF_a a_unit]].
destruct b_qubit as [_ [WF_b b_unit]].
destruct c_qubit as [_ [WF_c c_unit]].
rewrite lin_dep_def_alt. 2,3: assumption.
right.
assert (an0: a <> Zero). 
{
    unfold not.
    rewrite <- inner_product_zero_iff_zero. 2: assumption.
    rewrite a_unit.
    apply C1_neq_C0.
}
assert (bn0: b <> Zero). 
{
    unfold not.
    rewrite <- inner_product_zero_iff_zero. 2: assumption.
    rewrite b_unit.
    apply C1_neq_C0.
}
assert (cn0: c <> Zero). 
{
    unfold not.
    rewrite <- inner_product_zero_iff_zero. 2: assumption.
    rewrite c_unit.
    apply C1_neq_C0.
}
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

Lemma unitary_n0_tensor_yields_n0_components: forall (U: Square 4) (a: Vector 4) (b c: Vector 2), 
WF_Unitary U -> WF_Matrix a -> WF_Matrix b -> WF_Matrix c -> 
U × a = b ⊗ c -> a <> Zero -> b <> Zero /\ c <> Zero.
Proof.
intros U a b c U_unitary WF_a WF_b WF_c tens an0.
rewrite <- inner_product_zero_iff_zero in an0. 2: assumption.
rewrite unitary_preserves_inner_prod with (U := U) in an0. 2,3: assumption.
rewrite tens in an0.
assert (kip_help: ⟨ b ⊗ c, b ⊗ c ⟩ = ⟨ b, b ⟩ * ⟨ c, c ⟩). apply kron_inner_prod.
rewrite kip_help in an0 at 1.
split.
{
    unfold not.
    intro. 
    apply an0.
    rewrite <- inner_product_zero_iff_zero in H. 2: assumption.
    rewrite H.
    apply Cmult_0_l.
}
{
    unfold not.
    intro. 
    apply an0.
    rewrite <- inner_product_zero_iff_zero in H. 2: assumption.
    rewrite H.
    apply Cmult_0_r.
}
Qed.

Definition TensorProdQubit (c: Vector 4) := WF_Matrix c -> exists (a b : Vector 2), WF_Qubit a /\ WF_Qubit b /\ c = a ⊗ b.

Lemma qubit_tensor_inner_product: forall (a b : Vector 2) (c: Vector 4), 
WF_Qubit c -> c = a ⊗ b ->  ⟨ a, a ⟩* ⟨ b, b ⟩ = C1.
Proof.
intros.
destruct H as [_ [WF_c c_unit]].
rewrite <- kron_inner_prod.
rewrite <- H0.
assumption.
Qed.

Lemma Cmult_neq_0_implies_n0_arg: forall (a b c : C),
c = a * b -> c <> 0 -> a <> 0 /\ b <> 0.
Proof.
intros.
split.
{
    destruct (Ceq_dec a 0).
    contradict H0.
    rewrite H. 
    rewrite e.
    apply Cmult_0_l.
    assumption.
}
{
    destruct (Ceq_dec b 0).
    contradict H0.
    rewrite H. 
    rewrite e.
    apply Cmult_0_r.
    assumption.
}
Qed.

Lemma inner_prod_is_norm_squared {n}: forall (a: Vector n), 
norm a * norm a = ⟨ a, a ⟩.
Proof.
intros.
unfold norm, RtoC.
unfold Cmult.
apply c_proj_eq.
simpl.
rewrite Rmult_0_l.
rewrite Rminus_0_r.
apply sqrt_sqrt.
apply inner_product_ge_0.
simpl.
rewrite Rmult_0_l. rewrite Rmult_0_r.
rewrite Rplus_0_l.
symmetry.
apply norm_real.
Qed.

Lemma tensor_prod_of_qubit: forall (c : Vector 4), 
WF_Qubit c -> (TensorProd c <-> TensorProdQubit c).
Proof. 
intros c c_qubit.
unfold TensorProdQubit, TensorProd.
split.
{
    intro.
    assert (temp: WF_Qubit c). assumption.
    destruct temp as [_ [WF_c c_unit]].
    apply H in WF_c.
    destruct WF_c as [a [b [WF_a [WF_b c_def]]]].
    exists (normalize a), (normalize b).
    assert (inner_mult := qubit_tensor_inner_product a b c c_qubit c_def).
    assert (⟨ a, a ⟩ <> 0 /\ ⟨ b, b ⟩ <> 0). apply Cmult_neq_0_implies_n0_arg with (c:= C1). symmetry. assumption. apply C1_neq_C0.
    destruct H1.
    assert (norm a <> 0). 
    {
        unfold not.
        intro.
        apply H1.
        apply norm_zero_iff_zero in H3. 2: assumption.
        apply inner_product_zero_iff_zero. all: assumption.
    }
    assert (norm b <> 0). 
    {
        unfold not.
        intro.
        apply H2.
        apply norm_zero_iff_zero in H4. 2: assumption.
        apply inner_product_zero_iff_zero. all: assumption.
    }
    split.
    {
        unfold WF_Qubit.
        split. exists 1%nat. trivial.
        split. solve_WF_matrix.
        rewrite <- inner_prod_is_norm_squared.
        rewrite normalized_norm_1.
        apply Cmult_1_l.
        assumption.
    }
    split. 
    {
        unfold WF_Qubit.
        split. exists 1%nat. trivial.
        split. solve_WF_matrix.
        rewrite <- inner_prod_is_norm_squared.
        rewrite normalized_norm_1.
        apply Cmult_1_l.
        assumption.
    }
    unfold normalize.
    rewrite Mscale_kron_dist_l.
    rewrite Mscale_kron_dist_r.
    rewrite Mscale_assoc.
    rewrite <- Cinv_mult_distr. 2,3: apply RtoC_neq. 2,3: assumption.
    assert (norm a * norm b = C1).
    {
        rewrite <- inner_prod_is_norm_squared in inner_mult.
        rewrite <- inner_prod_is_norm_squared in inner_mult.
        apply complex_split in inner_mult.
        destruct inner_mult.
        revert H5.
        simpl.
        replace (((norm a * norm a - 0 * 0) *
        (norm b * norm b - 0 * 0) -
        (norm a * 0 + 0 * norm a) *
        (norm b * 0 + 0 * norm b))%R) with (((norm a * norm b) * (norm a * norm b))%R) by lra.
        replace ((norm a * norm b * (norm a * norm b))%R) with ((Rsqr (norm a * norm b))%R).
        2: unfold Rsqr. 2: lra.
        intro.
        apply (f_equal (fun f => sqrt f)) in H5.
        rewrite sqrt_Rsqr in H5.
        rewrite sqrt_1 in H5.
        apply c_proj_eq.
        simpl. rewrite H5. lra.
        simpl. lra.
        rewrite <- Rmult_0_l with (r:= norm b).
        apply Rmult_le_compat_r.
        all: apply norm_ge_0.
    }
    rewrite H5.
    replace (/C1) with (C1) by lca.
    rewrite Mscale_1_l.
    assumption.
}
{
    intro.
    destruct c_qubit as [_ [WF_c c_unit]].
    apply H in WF_c.
    destruct WF_c as [a [b [a_qubit [b_qubit c_def]]]].
    intro.
    exists a, b.
    split. apply a_qubit. 
    split. apply b_qubit. 
    assumption.
}
Qed.

Lemma a23: forall (U : Square 4), WF_Unitary U -> (forall (x : Vector 2), TensorProdQubit (U × (x ⊗ ∣0⟩))) ->
(exists (psi: Vector 2), forall (x: Vector 2), WF_Matrix x ->  exists (z: Vector 2), U × (x ⊗ ∣0⟩) = z ⊗ psi)
\/
(exists (psi: Vector 2), forall (x: Vector 2), WF_Matrix x -> exists (z: Vector 2), U × (x ⊗ ∣0⟩) = psi ⊗ z).
Proof. 
intros U U_unitary tensorProp.
assert (ts0 : TensorProdQubit (U × (∣0⟩ ⊗ ∣0⟩))). apply tensorProp.
assert (ts1 : TensorProdQubit (U × (∣1⟩ ⊗ ∣0⟩))). apply tensorProp.
assert (tsp : TensorProdQubit (U × (∣+⟩ ⊗ ∣0⟩))). apply tensorProp.
unfold TensorProdQubit in ts0, ts1, tsp.
assert (WF_Matrix (U × (∣0⟩ ⊗ ∣0⟩))). solve_WF_matrix. apply U_unitary.
apply ts0 in H. clear ts0.
destruct H as [a0 [b0 [a0_qubit [b0_qubit a0b0_def]]]].
assert (temp: WF_Qubit a0). assumption.
destruct temp as [_ [WF_a0 a0_unit]].
assert (temp: WF_Qubit b0). assumption.
destruct temp as [_ [WF_b0 b0_unit]].
assert (WF_Matrix (U × (∣1⟩ ⊗ ∣0⟩))). solve_WF_matrix. apply U_unitary.
apply ts1 in H. clear ts1.
destruct H as [a1 [b1 [a1_qubit [b1_qubit a1b1_def]]]].
assert (temp: WF_Qubit a1). assumption.
destruct temp as [_ [WF_a1 a1_unit]].
assert (temp: WF_Qubit b1). assumption.
destruct temp as [_ [WF_b1 b1_unit]].
assert (WF_Matrix (U × (∣+⟩ ⊗ ∣0⟩))). solve_WF_matrix. apply U_unitary.
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
        intros x WF_x.
        exists (x 0%nat 0%nat .* a0 .+ x 1%nat 0%nat .* (c .* a1)).
        rewrite qubit_decomposition1 with (phi:= x) at 1. 2: assumption.
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
            apply Mscale_0_cancel_r in contr.
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
        intros x WF_x.
        exists (x 0%nat 0%nat .* b0 .+ x 1%nat 0%nat .* (c .* b1)).
        rewrite qubit_decomposition1 with (phi:= x) at 1. 2: assumption.
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

Lemma exists_unitary_mapping_qubit_to_0: forall (a : Vector 2), 
WF_Qubit a -> exists (P : Square 2), WF_Unitary P /\ P × a = ∣0⟩.
Proof.
intros a a_qubit.
assert (temp: WF_Qubit a). assumption.
destruct temp as [_ [WF_a a_unit]].
set (P := (fun x y => 
match (x,y) with 
| (0,0) => (a 0%nat 0%nat)^*
| (0,1) => (a 1%nat 0%nat)^*
| (1,0) => - (a 1%nat 0%nat) 
| (1,1) => a 0%nat 0%nat
| _ => C0
end) : Square 2).
assert (WF_P: WF_Matrix P).
{
    unfold WF_Matrix.
    intros.
    unfold P.
    destruct H.
    destruct x as [|b]. contradict H. lia.
    destruct b as [|x]. contradict H. lia. reflexivity.
    destruct x as [|b]. destruct y as [|c]. contradict H. lia.
    destruct c as [|y]. contradict H. lia. reflexivity.
    destruct b as [|x]. destruct y as [|c]. contradict H. lia.
    destruct c as [|y]. contradict H. lia.
    reflexivity. reflexivity.   
}
exists P.
split.
{
    unfold WF_Unitary.
    split. assumption.
    lma'.
    all: rewrite Mmult_square2_explicit.
    2,3,5,6,8,9,11,12: solve_WF_matrix.
    all: repeat rewrite Madj_explicit_decomp.
    all: unfold P,I.
    all: simpl.
    2,3: lca.
    all: rewrite <- a_unit. 
    all: lca.
}
{
    lma'.
    all: rewrite Mv_prod_21_explicit.
    2,3,5,6: assumption.
    all: unfold P.
    rewrite <- a_unit. lca.
    lca.
}
Qed.

Lemma a24: forall (U V W00 W11 : Square 4), 
WF_Unitary U -> WF_Unitary V -> WF_Unitary W00 -> WF_Unitary W11 -> 
acgate U × acgate V = ∣0⟩⟨0∣ ⊗ W00 .+ ∣1⟩⟨1∣ ⊗ W11 -> 
exists (P0 Q0 P1 Q1 : Square 2), 
WF_Unitary P0 /\ WF_Unitary Q0 /\ WF_Unitary P1 /\ WF_Unitary Q1 /\
acgate U × acgate V = ∣0⟩⟨0∣ ⊗ P0 ⊗ Q0 .+ ∣1⟩⟨1∣ ⊗ P1 ⊗ Q1.
Proof.
intros U V W00 W11 U_unitary V_unitary W00_unitary W11_unitary acgate_mult.
assert (temp: WF_Unitary V). assumption.
destruct temp as [WF_V V_inv].
assert (temp:= a21 V V_unitary).
destruct temp as [psi [psi_qubit tens]].
assert (temp: WF_Qubit psi). assumption.
destruct temp as [_ [WF_psi psi_unit]].
rewrite tensor_prod_of_qubit in tens.
2: {
    unfold WF_Qubit.
    split. exists 2%nat. trivial.
    split. solve_WF_matrix.
    rewrite <- unitary_preserves_inner_prod. 2: assumption. 2: solve_WF_matrix.
    assert (kip_help: ⟨ ∣0⟩ ⊗ psi, ∣0⟩ ⊗ psi ⟩ = ⟨ ∣0⟩, ∣0⟩ ⟩ * ⟨ psi, psi ⟩). apply kron_inner_prod.
    rewrite kip_help at 1. clear kip_help.
    replace (⟨ ∣0⟩, ∣0⟩ ⟩) with (C1) by lca.
    rewrite psi_unit.
    apply Cmult_1_l.
}
assert (temp: WF_Matrix (V × (∣0⟩ ⊗ psi))). solve_WF_matrix.
unfold TensorProdQubit in tens.
apply tens in temp.
destruct temp as [a [b [a_qubit [b_qubit ab_decomp]]]].
Admitted.

Lemma RtoC_conj (x: R): (RtoC x)^* = RtoC x.
Proof. intros. unfold RtoC, Cconj. apply c_proj_eq. simpl. reflexivity. simpl. lra. Qed.

Lemma lin_indep_scale_invariant {n}: forall (a b : C) (u v: Vector n), 
a <> 0 -> b <> 0 -> (linearly_independent_2vec u v <-> linearly_independent_2vec (a .* u) (b .* v)).
Proof.
intros a b u v an0 bn0.
split.
{
    intro linindep.
    unfold linearly_independent_2vec in *.
    intros c1 c2 zero.
    repeat rewrite Mscale_assoc in zero.
    apply linindep in zero.
    destruct zero as [aprod bprod].
    rewrite Cmult_comm in aprod, bprod.
    apply Cmult_0_cancel_l in aprod, bprod.
    split. all: assumption.
}
{
    intro linindep.
    unfold linearly_independent_2vec in *.
    intros c1 c2 zero.
    specialize (linindep (c1 * /a) (c2 * /b)).
    repeat rewrite Mscale_assoc in linindep.
    repeat rewrite <- Cmult_assoc in linindep.
    rewrite Cinv_l in linindep.
    rewrite Cinv_l in linindep. 2,3: assumption.
    repeat rewrite Cmult_1_r in linindep.
    apply linindep in zero.
    destruct zero as [aprod bprod].
    rewrite Cmult_comm in aprod, bprod.
    apply Cmult_0_cancel_l in aprod, bprod.
    split. 1,2: assumption.
    all: apply nonzero_div_nonzero.
    all: assumption.
}
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
    rewrite <- Rinv_mult_distr.
    rewrite sqrt_sqrt.
    lca.
    lra.
    all: apply sqrt2_neq_0.
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