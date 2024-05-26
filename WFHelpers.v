Require Import QuantumLib.Matrix.
Require Import QuantumLib.Eigenvectors.

(* Ideally this definition wouldn't be here, but otherwise I can't autoresolve
   WF_Matrix goals using WF_Qubit hypotheses... *)
Definition WF_Qubit {n} (q: Vector n) := (exists m: nat, (2 ^ m = n)%nat) /\ WF_Matrix q /\ ⟨ q, q ⟩ = 1.

(* Some apply statements provide explicit dimensions for wider applicability *)
Ltac solve_WF_matrix :=
  repeat (
    progress (
      try reflexivity;
      try assumption;
      try match goal with
      | [ A : Square ?n |- WF_Matrix (control ?A) ] => apply (@WF_control n)
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
      | |- WF_Unitary (adjoint _) => apply adjoint_unitary
      | |- WF_Unitary (Mopp _) => unfold Mopp
      | |- WF_Unitary (_ × _) => apply Mmult_unitary
      (* TODO: Upstream `direct_sum_unitary`, otherwise we can't have this case *)
      (*| |- WF_Unitary (_ .⊕ _) => apply direct_sum_unitary *)
      | [ A : Square ?m, B : Square ?n  |- WF_Unitary (?A ⊗ ?B) ] => apply (@kron_unitary m n)
      | [ A : Square ?n |- WF_Unitary (control ?A) ] => apply (@control_unitary n)
      | |- WF_Unitary ?A => match goal with
                            | [ H : WF_Unitary A |- _ ] => apply H
                            | _ => auto with unit_db; autounfold with M_db; try unfold A
                            end
      (* TODO: Make a database for this (and upstream it!), e.g. diag_db *)
      | |- WF_Diagonal ?A => match goal with
                             | [ H : WF_Diagonal A |- _ ] => apply H
                             | _ => idtac
                             end
      | |- WF_Qubit ?A => match goal with
                          | [ H : WF_Qubit A |- _ ] => apply H
      (* TODO: Make a database for this, e.g. qubit_db *)
                          | _ => idtac
                          end
      end
    )
  ).
