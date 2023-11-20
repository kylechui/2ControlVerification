Require Import QuantumLib.Matrix.
Require Import QuantumLib.VecSet.

(* Lemma a1 is already stated and proven in QuantumLib VecSet *)
(* Restating as a1 for clarity in reading rest of proof *)
Lemma a1 : forall {n} (D E : Square n),
    Determinant (D × E) = (Determinant D) * (Determinant E).
Proof.
intros.
symmetry. 
apply Determinant_multiplicative.
Qed.

Lemma a2: forall {n} (D E: Square n), 
    trace (D × E) = trace (E × D).
Proof.
intros.
unfold trace.
unfold Mmult.
induction n.
lca.
simpl.
assert (Step1: 
Σ  (fun x : nat => Σ  (fun y : nat => E x y * D y x) n + E x n * D n x) n 
= (Σ  (fun x : nat => Σ (fun y : nat => E x y * D y x) n ) n + Σ  (fun x : nat => E x n * D n x) n)).
{
    rewrite <- (@big_sum_plus Complex.C _ _ C_is_comm_group).
    reflexivity.
}
rewrite Step1. clear Step1.
assert (Step2:
Σ  (fun x : nat => Σ  (fun y : nat => D x y * E y x) n + D x n * E n x) n 
= Σ (fun x : nat => Σ (fun y : nat => D x y * E y x) n ) n + Σ (fun x : nat => D x n * E n x) n).
{
rewrite <- (@big_sum_plus Complex.C _ _ C_is_comm_group).
reflexivity.
}
rewrite Step2. clear Step2.
rewrite IHn.
assert (Step3: Σ (fun y : nat => E n y * D y n) n = Σ (fun x : nat => D x n * E n x) n).
{
    apply big_sum_eq.
    apply functional_extensionality. 
    intros.
    apply Cmult_comm.
}
rewrite Step3. clear Step3.
assert (Step4: Σ (fun x : nat => E x n * D n x) n = Σ (fun y : nat => D n y * E y n) n).
{
    apply big_sum_eq.
    apply functional_extensionality.
    intros.
    apply Cmult_comm.
}
rewrite Step4. clear Step4.
lca.
Qed.
