From Proof Require Import Qubit.
Property kron_assoc_vect : forall (A B C : Vector 2),
  (A ⊗ B) ⊗ C == A ⊗ (B ⊗ C).
Proof.
  lma.
Qed.

Property kron_assoc_mat : forall (A B C : Matrix 2 2),
  (A ⊗ B) ⊗ C == A ⊗ (B ⊗ C).
Proof.
  lma.
Qed.