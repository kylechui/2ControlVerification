Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.
From Proof Require Import MatrixHelpers.
Definition WF_Qubit {n} (q: Vector n) := (exists m: nat, (2 ^ m = n)%nat) /\ WF_Matrix q /\ ⟨ q, q ⟩ = 1.

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
  rewrite kron_1_l with (A := ∣0⟩⟨0∣). 2: apply WF_braqubit0.
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
WF_Qubit a -> WF_Qubit b -> linearly_independent_2vec a b <-> Cmod (⟨ a, b ⟩) < 1.
Proof.
Admitted.

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