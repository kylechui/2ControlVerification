Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.
Require Import QuantumLib.CauchySchwarz.
From Proof Require Import MatrixHelpers.
From Proof Require Import AlgebraHelpers.


Definition WF_Qubit {n} (q: Vector n) := (exists m: nat, (2 ^ m = n)%nat) /\ WF_Matrix q /\ ⟨ q, q ⟩ = 1.

Lemma qubit_prop_explicit: forall (a: Vector 2), 
WF_Qubit a -> 
(a 0%nat 0%nat)^* * (a 0%nat 0%nat) + (a 1%nat 0%nat)^* * (a 1%nat 0%nat) = C1.
Proof.
intros.
destruct H as [_ [WF_a a_unit]].
rewrite <- a_unit.
lca.
Qed.

Lemma qubit_adj_mult {n}: forall (q : Vector n),
WF_Matrix q -> 
(⟨ q, q ⟩ = 1 <-> q † × q = I 1).
Proof.
intros.
split.
{
    intros.
    lma'.
    unfold inner_product in H0.
    rewrite H0.
    lca.
}
{
    intros.
    unfold inner_product.
    rewrite H0.
    lca.
}
Qed.

Lemma qubit0_qubit : WF_Qubit ∣0⟩.
Proof.
unfold WF_Qubit.
split.
exists 1%nat. trivial.
split.
apply WF_qubit0.
lca.
Qed.

Lemma qubit1_qubit : WF_Qubit ∣1⟩.
Proof.
unfold WF_Qubit.
split. 
exists 1%nat. trivial.
split. 
apply WF_qubit1.
lca.
Qed.

Lemma qubit_decomposition1: forall (phi : Vector 2),
WF_Matrix phi -> phi = (phi 0%nat 0%nat) .* ∣0⟩ .+ (phi 1%nat 0%nat) .* ∣1⟩.
Proof.
intros.
lma'.
Qed. 

Lemma qubit_decomposition2_explicit : forall (phi : Vector 4), 
WF_Matrix phi ->
phi = (phi 0 0)%nat .* ∣0,0⟩ .+ (phi 1 0)%nat .* ∣0,1⟩ .+
 (phi 2 0)%nat .* ∣1,0⟩ .+ (phi 3 0)%nat .* ∣1,1⟩.
Proof.
  intros.
  lma'.
  solve_WF_matrix.
Qed.

(* Definition of lemma from old file Multiqubit*)
Lemma qubit_decomposition2_implicit : forall (phi : Vector 4), 
WF_Matrix phi -> exists (a b c d: C),
phi = a .* ∣0,0⟩ .+ b .* ∣0,1⟩ .+ c .* ∣1,0⟩ .+ d .* ∣1,1⟩.
Proof.
  intros.
  exists (phi 0 0)%nat, (phi 1 0)%nat, (phi 2 0)%nat, (phi 3 0)%nat.
  lma'.
  solve_WF_matrix.
Qed.

Property is_unitary_form : forall (M : Square 2) (a b : Vector 2), 
  WF_Qubit a -> WF_Qubit b ->
  M = a ⊗ ⟨0∣ .+ b ⊗ ⟨1∣ /\ ⟨a, b⟩ = 0 -> WF_Unitary M.
Proof.
  intros.
  destruct H1 as [H1 H2].
  rewrite H1.
  destruct H as [_ [H WF_a]].
  destruct H0 as [_ [H0 WF_b]].
  rewrite qubit_adj_mult in WF_a. 2: apply H.
  rewrite qubit_adj_mult in WF_b. 2: apply H0.
  unfold WF_Unitary.
  split. solve_WF_matrix.
  rewrite Mplus_adjoint.
  rewrite (kron_adjoint a ⟨0∣).
  rewrite (kron_adjoint b ⟨1∣).
  repeat rewrite adjoint_involutive.
  rewrite Mmult_plus_distr_l.
  repeat rewrite Mmult_plus_distr_r.
  rewrite (kron_mixed_product a† ∣0⟩ a ⟨0∣).
  rewrite WF_a.
  rewrite kron_1_l with (A := ∣0⟩⟨0∣). 2: apply WF_braket0.
  rewrite (kron_mixed_product b† ∣1⟩ a ⟨0∣).
  unfold inner_product in H2.
  assert (Main1 : a† × b = b† × a).
  {
    lma'.
    rewrite H2.
    apply (f_equal (fun f => f^*)) in H2.
    assert (Help : ((a† × b) 0%nat 0%nat)^* = ((b† × a) 0%nat 0%nat)). lca.
    rewrite Help in H2.
    rewrite Cconj_0 in H2.
    symmetry.
    apply H2.
  }
  rewrite <- Main1.
  assert (Main2 : a† × b = Zero).
  {
    lma'.
    apply H2.
  }
  rewrite Main2.
  rewrite kron_0_l.
  rewrite Mplus_0_r.
  rewrite (kron_mixed_product a† ∣0⟩ b ⟨1∣).
  rewrite Main2.
  rewrite kron_0_l.
  rewrite Mplus_0_l.
  rewrite (kron_mixed_product b† ∣1⟩ b ⟨1∣).
  rewrite WF_b.
  lma'.
Qed.

Lemma cauchy_schwarz_corollary: 
forall (a b : Vector 2), 
WF_Qubit a -> WF_Qubit b -> linearly_independent_2vec a b -> Cmod (⟨ a, b ⟩) < 1.
Proof.
intros a b a_qubit b_qubit ab_indep.
apply Rsqr_incrst_0. 2: apply Cmod_ge_0. 2: lra.
unfold Rsqr at 2.
assert (a_1: 1 = fst ⟨ a, a ⟩).
{
    destruct a_qubit as [_ [WF_a a_unit]].
    rewrite a_unit.
    simpl. reflexivity.
}
rewrite a_1 at 1.
assert (b_1: 1 = fst ⟨ b, b ⟩).
{
    destruct b_qubit as [_ [WF_b b_unit]].
    rewrite b_unit.
    simpl. reflexivity.
}
rewrite b_1.
rewrite Rsqr_pow2.
apply Cauchy_Schwartz_strict_ver1.
apply a_qubit.
apply b_qubit.
unfold linearly_independent_2vec in ab_indep.
intros c d nz_cond.
apply Coq.Logic.Classical_Prop.or_not_and in nz_cond.
unfold not.
intro eq.
apply nz_cond.
assert (neg: d = 0 <-> -d = 0). 
{
    split.
    intro. rewrite H. lca.
    intro.
    apply (f_equal (fun f => - f)) in H.
    rewrite Copp_involutive in H.
    rewrite Copp_0 in H.
    assumption.
}
rewrite neg.
apply ab_indep.
rewrite eq.
lma'.
solve_WF_matrix.
all: apply b_qubit.
Qed.

Lemma qubit_01_lin_indep: linearly_independent_2vec ∣0⟩ ∣1⟩.
Proof.
apply orthonormal_implies_lin_indep_2.
1,2: solve_WF_matrix.
all: lca.
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
        rewrite <- phi_unit.
        lca.
    }
}
{
    lca.
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

Lemma exists_unitary_mapping_qubit_to_1: forall (a : Vector 2), 
WF_Qubit a -> exists (P : Square 2), WF_Unitary P /\ P × a = ∣1⟩.
Proof.
intros a a_qubit.
assert (temp: WF_Qubit a). assumption.
destruct temp as [_ [WF_a a_unit]].
set (P := (fun x y => 
match (x,y) with 
| (0,0) => - (a 1%nat 0%nat)
| (0,1) => (a 0%nat 0%nat)
| (1,0) => (a 0%nat 0%nat)^* 
| (1,1) => (a 1%nat 0%nat)^*
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
    lca.
    rewrite <- a_unit. lca.
}
Qed.

Lemma orth_qubit_unitary: forall (a b: Vector 2), 
WF_Qubit a -> WF_Qubit b -> ⟨ a, b ⟩ = 0 -> 
WF_Unitary (a × ⟨0∣ .+ b × ⟨1∣).
Proof.
intros a b a_qubit b_qubit orth.
assert (temp: WF_Qubit a). assumption. 
destruct temp as [_ [WF_a a_unit]].
assert (temp: WF_Qubit b). assumption. 
destruct temp as [_ [WF_b b_unit]].
unfold WF_Unitary.
split. solve_WF_matrix.
assert (a00: (a × ⟨0∣) 0%nat 0%nat = a 0%nat 0%nat). lca.
assert (a01: (a × ⟨0∣) 0%nat 1%nat = C0). lca.
assert (a10: (a × ⟨0∣) 1%nat 0%nat = a 1%nat 0%nat). lca.
assert (a11: (a × ⟨0∣) 1%nat 1%nat = C0). lca.
assert (b01: (b × ⟨1∣) 0%nat 1%nat = b 0%nat 0%nat). lca.
assert (b00: (b × ⟨1∣) 0%nat 0%nat = C0). lca.
assert (b11: (b × ⟨1∣) 1%nat 1%nat = b 1%nat 0%nat). lca.
assert (b10: (b × ⟨1∣) 1%nat 0%nat = C0). lca.
lma'.
all: rewrite Mmult_square2_explicit. 2,3,5,6,8,9,11,12: solve_WF_matrix.
all: repeat rewrite Madj_explicit_decomp.
all: repeat rewrite Mplus_access.
all: try rewrite a00.
all: try rewrite a01.
all: try rewrite a10.
all: try rewrite a11.
all: try rewrite b00.
all: try rewrite b01.
all: try rewrite b10.
all: try rewrite b11.
all: unfold I.
all: simpl.
all: Csimpl.
rewrite <- a_unit. lca.
rewrite <- orth. lca.
rewrite <- Cconj_0. rewrite <- orth. lca.
rewrite <- b_unit. lca.
Qed.

Lemma Mmult_qubit {n}: forall (U : Square n) (x : Vector n), 
WF_Unitary U -> WF_Qubit x -> WF_Qubit (U × x).
Proof.
intros.
destruct H0 as [pow_prop [WF_x x_unit]].
split. apply pow_prop.
split. solve_WF_matrix. apply H.
rewrite <- unitary_preserves_inner_prod.
all: assumption.
Qed. 

Lemma kron_qubit {n}: forall (u v : Vector n), 
WF_Qubit u -> WF_Qubit v -> WF_Qubit (u ⊗ v).
Proof.
intros.
destruct H as [pow_prop [WF_u u_unit]].
destruct H0 as [_ [WF_v v_unit]].
destruct pow_prop as [m m_prop].
split. exists (m*2)%nat. rewrite <- m_prop.
rewrite Nat.pow_mul_r. rewrite Nat.pow_2_r. reflexivity.
split. solve_WF_matrix.
rewrite kron_inner_prod.
rewrite u_unit, v_unit.
apply Cmult_1_r.
Qed.

Lemma qubit_implies_nonzero {n}: forall (q : Vector n), 
WF_Qubit q -> q <> Zero.
Proof.
intros.
destruct H as [_ [WF_q q_unit]].
unfold not.
intro.
rewrite <- inner_product_zero_iff_zero in H. 2: assumption.
apply C1_neq_C0.
rewrite <- H.
rewrite <- q_unit.
reflexivity.
Qed.

Lemma qubit_not_0tens {n}: forall (x : Vector (2*n)),
n <> 0%nat -> WF_Matrix x -> 
(exists i: nat, (n <= i)%nat /\ x i 0%nat <> 0) -> 
forall (y : Vector n), WF_Matrix y -> x <> ∣0⟩ ⊗ y.
Proof.
intros x nn0 WF_x eln0 y.
destruct eln0 as [i [ibound x0]].
unfold not. 
intros.
apply x0.
rewrite H0.
unfold kron.
rewrite <- Nat.mul_1_r with (n:= n) in ibound.
apply Nat.div_le_lower_bound in ibound. 2: assumption.
assert (iub : (i < n * 2)%nat).
{
    destruct (le_lt_dec (n*2) i).
    {
        contradict x0.
        rewrite WF_x.
        reflexivity.
        left. lia.
    }
    assumption.   
}
apply Nat.Div0.div_lt_upper_bound in iub.
assert (ind_val:= nat_tight_bound 1 (i/n)%nat ibound iub).
rewrite <- ind_val.
lca.
Qed.

Lemma qubit_not_1tens {n}: forall (x : Vector (2*n)),
n <> 0%nat -> WF_Matrix x -> 
(exists i: nat, (i < n)%nat /\ x i 0%nat <> 0) -> 
forall (y : Vector n), WF_Matrix y -> x <> ∣1⟩ ⊗ y.
Proof.
intros x nn0 WF_x eln0 y.
destruct eln0 as [i [ibound x0]].
unfold not. 
intros.
apply x0.
rewrite H0.
unfold kron.
rewrite Nat.div_small.
lca. assumption.
Qed.