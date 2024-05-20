Require Import QuantumLib.Matrix.
Require Import QuantumLib.Eigenvectors.

(* Ideally this definition wouldn't be here, but otherwise I can't autoresolve
   WF_Matrix goals using WF_Qubit hypotheses... *)
Definition WF_Qubit {n} (q: Vector n) := (exists m: nat, (2 ^ m = n)%nat) /\ WF_Matrix q /\ ⟨ q, q ⟩ = 1.

Ltac solve_WF_matrix :=
  repeat (
    progress (
      try reflexivity;
      try assumption;
      try match goal with
      (* Not entirely sure why, but it seems to do better when you explicitly provide dimensions *)
      | |- WF_Matrix (control ?A) => match type of A with
                                     | Square ?n => apply (@WF_control n)
                                     end
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
      | |- WF_Unitary (control _) => apply control_unitary
      | |- WF_Unitary (adjoint _) => apply adjoint_unitary
      | |- WF_Unitary (Mopp _) => unfold Mopp
      | |- WF_Unitary (_ × _) => apply Mmult_unitary
      (* Not entirely sure why, but it seems to do better when you explicitly provide dimensions *)
      | |- WF_Unitary (?A ⊗ ?B) => match type of A with
                                   | Square ?m => match type of B with
                                                  | Square ?n => apply (@kron_unitary m n)
                                                  end
                                   end
      (* TODO: Make this lemma *)
      (*| |- WF_Unitary (_ .⊕ _) => apply direct_sum_unitary; try lia*)
      | |- WF_Unitary (control ?A) => match type of A with
                                      | Square ?n => apply (@control_unitary n)
                                      end
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
