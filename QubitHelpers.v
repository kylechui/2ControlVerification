Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.
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
