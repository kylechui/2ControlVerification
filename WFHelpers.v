Require Import QuantumLib.Matrix.
Require Import QuantumLib.Eigenvectors.

(* Ideally this definition wouldn't be here, but otherwise I can't autoresolve
   WF_Matrix goals using WF_Qubit hypotheses... *)
Definition WF_Qubit {n} (q: Vector n) := (exists m: nat, (2 ^ m = n)%nat) /\ WF_Matrix q /\ ⟨ q, q ⟩ = 1.

Ltac solve_WF_matrix :=
  repeat (
    progress (
      try match goal with
      | |- WF_Matrix (control _) => apply WF_control
      | |- WF_Matrix (adjoint _) => apply WF_adjoint
      | |- WF_Matrix (Mopp _) => unfold Mopp
      | |- WF_Matrix (_ .+ _) => apply WF_plus; try lia
      | |- WF_Matrix (_ .* _) => apply WF_scale
      | |- WF_Matrix (_ × _) => apply WF_mult
      | |- WF_Matrix (_ ⊗ _) => apply WF_kron; try lia
      | |- WF_Matrix (_ .⊕ _) => apply WF_direct_sum; try lia
      | |- WF_Matrix ?A => match goal with
                           | [ H : WF_Matrix A |- _ ] => apply H
                           | [ H : WF_Unitary A |- _ ] => apply H
                           | [ H : WF_Qubit A |- _ ] => apply H
                           | _ => auto_wf; autounfold with M_db; try unfold A
                           end
      | |- WF_Unitary _ => auto
      | |- WF_Qubit _ => auto
      end
    )
  ).
