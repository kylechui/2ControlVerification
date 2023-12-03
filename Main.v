Require Import QuantumLib.Complex.
Require Import QuantumLib.Quantum.
Require Import QuantumLib.Eigenvectors.
Require Import QuantumLib.Matrix.

Lemma a4_2 : forall (u0 : C) (u1 : C),
  Cmod u0 = 1 -> Cmod u1 = 1 ->
  forall (Q : Square 2),
    WF_Unitary Q ->
    let beta : Vector 2 := Q × ∣0⟩ in
    let beta_perp := Q × ∣1⟩ in
    exists (P0 P1 : Square 2),
      WF_Unitary P0 -> WF_Unitary P1 ->
      I 2 ⊗ I 2 ⊗ beta ⊗ beta† .+ P0 ⊗ P1 ⊗ beta_perp ⊗ beta_perp† = control (control (list2D_to_matrix [[u0; C0]; [C0; u1]]))
      <-> u0 = 1 /\ u1 = 1.
Proof.
  intros u0 u1 Unit_u0 Unit_u1 Q Unitary_Q beta beta_perp.
  exists (I 2).
  exists (I 2).
  intros Unitary_I2 Unitary_I2'.
Admitted.
