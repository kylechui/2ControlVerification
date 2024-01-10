Require Import QuantumLib.Quantum.
From Proof Require Import MatrixHelpers.
From Proof Require Import QubitHelpers.

Lemma inner_prod_0_decomp {n}: forall (u v: Vector n), 
WF_Matrix u -> WF_Matrix v -> ⟨ u , v ⟩ = C0 <-> u† × v = Zero.
Proof.
split.
intros.
lma'.
unfold inner_product in H1.
rewrite H1. lca.
intros.
unfold inner_product.
rewrite H1. lca.
Qed.

Lemma inner_prod_1_decomp {n}: forall (u v: Vector n), 
WF_Matrix u -> WF_Matrix v -> ⟨ u , v ⟩ = C1 <-> u† × v = I 1.
Proof.
split.
intros.
lma'.
unfold inner_product in H1.
rewrite H1. lca.
intros.
unfold inner_product.
rewrite H1. lca.
Qed.

Lemma inner_prod_0_comm {n}: forall (u v: Vector n), 
WF_Matrix u -> WF_Matrix v -> ⟨ u , v ⟩ = C0 <-> ⟨ v , u ⟩ = C0.
split.
intros.
rewrite inner_product_conj_sym.
rewrite <- Cconj_0.
apply Cconj_simplify. do 2 rewrite Cconj_involutive. assumption.
intros.
rewrite inner_product_conj_sym.
rewrite <- Cconj_0.
apply Cconj_simplify. do 2 rewrite Cconj_involutive. assumption.
Qed.

Lemma block_decomp_4: forall (U: Square 4), WF_Matrix U ->
exists (P00 P01 P10 P11: Square 2), 
WF_Matrix P00 /\ WF_Matrix P01 /\ WF_Matrix P10 /\ WF_Matrix P11 /\
U = ∣0⟩⟨0∣ ⊗ P00 .+ ∣0⟩⟨1∣ ⊗ P01 .+ ∣1⟩⟨0∣ ⊗ P10 .+ ∣1⟩⟨1∣ ⊗ P11.
Proof.
intros U WF_U.
set (P00 := (fun x y =>
match (x,y) with
| (0,0) => (U 0 0)%nat
| (0,1) => (U 0 1)%nat
| (1,0) => (U 1 0)%nat
| (1,1) => (U 1 1)%nat
| _ => C0
end) : (Square 2)).
set (P01 := (fun x y =>
match (x,y) with
| (0,0) => (U 0 2)%nat
| (0,1) => (U 0 3)%nat
| (1,0) => (U 1 2)%nat
| (1,1) => (U 1 3)%nat
| _ => C0
end) : (Square 2)).
set (P10 := (fun x y =>
match (x,y) with
| (0,0) => (U 2 0)%nat
| (0,1) => (U 2 1)%nat
| (1,0) => (U 3 0)%nat
| (1,1) => (U 3 1)%nat
| _ => C0
end) : (Square 2)).
set (P11 := (fun x y =>
match (x,y) with
| (0,0) => (U 2 2)%nat
| (0,1) => (U 2 3)%nat
| (1,0) => (U 3 2)%nat
| (1,1) => (U 3 3)%nat
| _ => C0
end) : (Square 2)).
exists P00, P01, P10, P11.
assert (WF_P00: WF_Matrix P00). 
{
    unfold WF_Matrix. intros.
    unfold P00.
    destruct H.
    destruct x as [|x']. contradict H. lia.
    destruct x' as [| x'']. contradict H. lia. 
    reflexivity.
    destruct x as [|x'].
    destruct y as [|y']. contradict H. lia.
    destruct y' as [| y'']. contradict H. lia.
    reflexivity.
    destruct x' as [| x''].
    destruct y as [| y']. contradict H. lia. 
    destruct y' as [| y'']. contradict H. lia.
    reflexivity.
    reflexivity.
}
split. assumption.
assert (WF_P01: WF_Matrix P01). 
{
    unfold WF_Matrix. intros.
    unfold P01.
    destruct H.
    destruct x as [|x']. contradict H. lia.
    destruct x' as [| x'']. contradict H. lia. 
    reflexivity.
    destruct x as [|x'].
    destruct y as [|y']. contradict H. lia.
    destruct y' as [| y'']. contradict H. lia.
    reflexivity.
    destruct x' as [| x''].
    destruct y as [| y']. contradict H. lia. 
    destruct y' as [| y'']. contradict H. lia.
    reflexivity.
    reflexivity.
}
split. assumption.
assert (WF_P10: WF_Matrix P10). 
{
    unfold WF_Matrix. intros.
    unfold P10.
    destruct H.
    destruct x as [|x']. contradict H. lia.
    destruct x' as [| x'']. contradict H. lia. 
    reflexivity.
    destruct x as [|x'].
    destruct y as [|y']. contradict H. lia.
    destruct y' as [| y'']. contradict H. lia.
    reflexivity.
    destruct x' as [| x''].
    destruct y as [| y']. contradict H. lia. 
    destruct y' as [| y'']. contradict H. lia.
    reflexivity.
    reflexivity.
}
split. assumption.
assert (WF_P11: WF_Matrix P11). 
{
    unfold WF_Matrix. intros.
    unfold P11.
    destruct H.
    destruct x as [|x']. contradict H. lia.
    destruct x' as [| x'']. contradict H. lia. 
    reflexivity.
    destruct x as [|x'].
    destruct y as [|y']. contradict H. lia.
    destruct y' as [| y'']. contradict H. lia.
    reflexivity.
    destruct x' as [| x''].
    destruct y as [| y']. contradict H. lia. 
    destruct y' as [| y'']. contradict H. lia.
    reflexivity.
    reflexivity.
}
split. assumption.
lma'. apply WF_blockmatrix. 1,2,3,4: assumption.
all: unfold Mplus, kron, "∣0⟩⟨0∣", "∣0⟩⟨1∣", "∣1⟩⟨0∣", "∣1⟩⟨1∣", Mmult, adjoint.
all: simpl.
all: Csimpl.
1,2,5,6: unfold P00.
5,6,7,8: unfold P01.
9,10,13,14: unfold P10.
13,14,15,16: unfold P11.
all: lca.
Qed.

Lemma vector_mult_simplify {m n}: forall (A B: Matrix m n),
(forall (w : Vector n), WF_Matrix w -> A × w = B × w) -> A = B.
Proof.
Admitted.



Lemma a17: forall (U : Square 4) (beta beta_p : Vector 2), 
WF_Unitary U -> WF_Qubit beta -> WF_Qubit beta_p -> ⟨ beta , beta_p ⟩ = C0 -> 
(exists (psi phi : Vector 2), WF_Matrix psi /\ WF_Matrix phi /\ U × (∣0⟩ ⊗ beta) = ∣0⟩ ⊗ psi /\ U × (∣0⟩ ⊗ beta_p) = ∣0⟩ ⊗ phi) -> 
exists (P00 P11 : Square 2), 
U = ∣0⟩⟨0∣ ⊗ P00 .+ ∣1⟩⟨1∣ ⊗ P11 /\ WF_Unitary P00 /\ WF_Unitary P11.
Proof.
intros U beta beta_p U_unitary beta_qubit beta_p_qubit beta_orth special_vectors.
destruct beta_qubit as [_ [WF_beta beta_norm]].
destruct beta_p_qubit as [_ [WF_beta_p beta_p_norm]].
destruct special_vectors as [psi [phi [ WF_psi [ WF_phi [U_beta U_beta_p]]]]].
set (Q := beta × ⟨0∣ .+  beta_p × ⟨1∣).
assert (Q_unitary: WF_Unitary Q).
{
  unfold WF_Unitary.
  split.
  solve_WF_matrix.
  unfold Q.
  rewrite Mplus_adjoint. repeat rewrite Mmult_adjoint.
  rewrite Mmult_plus_distr_l. repeat rewrite Mmult_plus_distr_r.
  rewrite Mmult_assoc. rewrite <- Mmult_assoc with (A := (beta) †).
  apply inner_prod_1_decomp in beta_norm. 3,2: assumption.
  rewrite beta_norm.
  rewrite Mmult_assoc with (A := (⟨1∣) †). rewrite <- Mmult_assoc with (A := (beta_p) †).
  assert (beta_p_orth: ⟨ beta_p, beta ⟩ = C0). apply inner_prod_0_comm. 1,2,3: assumption.
  apply inner_prod_0_decomp in beta_p_orth. 2,3: assumption.
  rewrite beta_p_orth.
  rewrite Mmult_assoc with (A := (⟨0∣) †). rewrite <- Mmult_assoc with (A := (beta) †).
  apply inner_prod_0_decomp in beta_orth. 2,3: assumption.
  rewrite beta_orth.
  rewrite Mmult_assoc with (A := (⟨1∣) †). rewrite <- Mmult_assoc with (A := (beta_p) †).
  apply inner_prod_1_decomp in beta_p_norm. 2,3: assumption.
  rewrite beta_p_norm.
  lma'.
}

assert (prod_decomp_1 : forall (w : Vector 2), WF_Matrix w -> U × (I 2 ⊗ Q) × (∣0⟩ ⊗ w) = ∣0⟩ ⊗ ((w 0%nat 0%nat) .* psi .+ (w 1%nat 0%nat) .* phi)).
{
    intros.
    assert (w_decomp: w = ((w 0%nat 0%nat) .* ∣0⟩ .+ (w 1%nat 0%nat) .* ∣1⟩)). lma'.
    rewrite w_decomp at 1.
    rewrite Mmult_assoc.
    assert (kron_mix_helper: (I 2 ⊗ Q × (∣0⟩ ⊗ (w 0%nat 0%nat .* ∣0⟩ .+ w 1%nat 0%nat .* ∣1⟩))) = 
    (I 2 × ∣0⟩) ⊗ (Q × (w 0%nat 0%nat .* ∣0⟩ .+ w 1%nat 0%nat .* ∣1⟩))). lma'. 1,2: solve_WF_matrix.
    rewrite kron_mix_helper at 1.
    rewrite Mmult_1_l. 2: apply WF_qubit0.
    unfold Q.
    rewrite Mmult_plus_distr_l. do 2 rewrite Mmult_plus_distr_r.
    rewrite Mmult_assoc with (A := beta_p) (B := ⟨1∣ ).
    rewrite Mscale_mult_dist_r with (A:= ⟨1∣) (B:= ∣0⟩).
    rewrite Mmult10. rewrite Mscale_0_r. rewrite Mmult_0_r. rewrite Mplus_0_r.
    rewrite Mmult_assoc with (A := beta) (C := w 1%nat 0%nat .* ∣1⟩ ).
    rewrite Mscale_mult_dist_r with (A:= ⟨0∣) (B:= ∣1⟩).
    rewrite Mmult01. rewrite Mscale_0_r. rewrite Mmult_0_r. rewrite Mplus_0_l.
    rewrite Mmult_assoc with (A := beta).
    rewrite Mscale_mult_dist_r with (A:= ⟨0∣).
    rewrite Mmult00. 
    assert (beta_helper: (beta × (w 0%nat 0%nat .* I 1)) = w 0%nat 0%nat .* beta). lma'.
    rewrite beta_helper. clear beta_helper.
    rewrite Mmult_assoc.
    rewrite Mscale_mult_dist_r.
    rewrite Mmult11. 
    assert (beta_p_helper: (beta_p × (w 1%nat 0%nat .* I 1)) = w 1%nat 0%nat .* beta_p). lma'.
    rewrite beta_p_helper. clear beta_p_helper.
    rewrite kron_plus_distr_l.
    do 2 rewrite Mscale_kron_dist_r.
    rewrite Mmult_plus_distr_l.
    do 2 rewrite Mscale_mult_dist_r.
    rewrite U_beta at 1. rewrite U_beta_p at 1.
    lma'.
}
destruct (block_decomp_4 U) as [P00 [P01 [P10 [P11 [WF_P00 [WF_P01 [WF_P10 [WF_P11 U_block_decomp]]]]]]]]. apply U_unitary.
assert (prod_decomp_2: forall (w : Vector 2), WF_Matrix w -> U × (I 2 ⊗ Q) × (∣0⟩ ⊗ w) = ∣0⟩ ⊗ (P00 × Q × w) .+ ∣1⟩ ⊗ (P10 × Q × w)).
{
    intros w WF_w.
    rewrite Mmult_assoc.
    assert (kron_mix_helper: (I 2 ⊗ Q × (∣0⟩ ⊗ w)) = (I 2 × ∣0⟩) ⊗ (Q × w)). lma'. 1,2: solve_WF_matrix.
    rewrite kron_mix_helper at 1. clear kron_mix_helper.
    rewrite Mmult_1_l. 2: apply WF_qubit0.
    rewrite U_block_decomp.
    do 3 rewrite Mmult_plus_distr_r.
    rewrite kron_mixed_product. rewrite Mmult_assoc. rewrite Mmult00. rewrite Mmult_1_r. 2: apply WF_qubit0.
    rewrite kron_mixed_product. rewrite Mmult_assoc. rewrite Mmult10. rewrite Mmult_0_r. rewrite kron_0_l. rewrite Mplus_0_r.
    rewrite kron_mixed_product. rewrite Mmult_assoc. rewrite Mmult00. rewrite Mmult_1_r. 2: apply WF_qubit1.
    rewrite kron_mixed_product. rewrite Mmult_assoc. rewrite Mmult10. rewrite Mmult_0_r. rewrite kron_0_l. rewrite Mplus_0_r.
    do 2 rewrite <- Mmult_assoc.
    reflexivity.
}
assert (tens_elem_2: forall (w: Vector 2), WF_Matrix w ->(∣1⟩ ⊗ (P10 × Q × w)) 2%nat 0%nat = C0).
{
    intros w WF_w.
    assert (U20_equiv: (∣1⟩ ⊗ (P10 × Q × w)) 2%nat 0%nat = (U × (I 2 ⊗ Q) × (∣0⟩ ⊗ w)) 2%nat 0%nat).
    {
        rewrite prod_decomp_2. 2: assumption.
        lca.
    }
    rewrite U20_equiv.
    rewrite prod_decomp_1. 2: assumption.
    lca.
}
assert (tens_elem_3: forall (w: Vector 2), WF_Matrix w ->(∣1⟩ ⊗ (P10 × Q × w)) 3%nat 0%nat = C0).
{
    intros w WF_w.
    assert (U30_equiv: (∣1⟩ ⊗ (P10 × Q × w)) 3%nat 0%nat = (U × (I 2 ⊗ Q) × (∣0⟩ ⊗ w)) 3%nat 0%nat).
    {
        rewrite prod_decomp_2. 2: assumption.
        lca.
    }
    rewrite U30_equiv.
    rewrite prod_decomp_1. 2: assumption.
    lca.
}
assert (tens_equiv_0: forall (w: Vector 2), WF_Matrix w ->(∣1⟩ ⊗ (P10 × Q × w)) = (Zero (m:=4) (n:=1))).
{
    intros w WF_w.
    lma'.
    apply WF_kron. reflexivity. reflexivity. apply WF_qubit1. apply WF_mult. solve_WF_matrix. assumption.
    apply tens_elem_2. assumption.
    apply tens_elem_3. assumption.
}
assert (prod_equiv_0: forall (w: Vector 2), WF_Matrix w -> P10 × Q × w = (Zero (m:=2) (n:=1))).
{
    intros w WF_w.
    assert (zero_tens: (Zero (m:=4) (n:=1)) = ∣1⟩ ⊗ (Zero (m:=2) (n:=1))). lma'.
    rewrite zero_tens in tens_equiv_0.
    apply kron_1_cancel_l.
    apply WF_mult. solve_WF_matrix. assumption.
    apply WF_Zero.
    apply tens_equiv_0.
    assumption.
}
assert (P10Q_0: P10 × Q = Zero).
{
    apply vector_mult_simplify.
    intros.
    rewrite Mmult_0_l.
    apply prod_equiv_0.
    assumption.
}
assert (P10_0: P10 = Zero).
{
    rewrite <- P10Q_0.
}
Admitted.