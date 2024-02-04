Require Import QuantumLib.Quantum.

(* used no helper definitions to remove all dependences from this *)
Property swap_helper : forall (U : Square 4),
  WF_Matrix U -> 
  (I 2 ⊗ swap) × (U ⊗ I 2) × (I 2 ⊗ swap) = (swap ⊗ I 2) × (I 2 ⊗ U) × (swap ⊗ I 2).
Proof.
  intros. 
  apply mat_equiv_eq.
  apply WF_mult. apply WF_mult.
  apply WF_kron. reflexivity. reflexivity. apply WF_I. apply WF_swap.
  apply WF_kron. reflexivity. reflexivity. apply H. apply WF_I.
  apply WF_kron. reflexivity. reflexivity. apply WF_I. apply WF_swap.
  apply WF_mult. apply WF_mult.
  apply WF_kron. reflexivity. reflexivity. apply WF_swap. apply WF_I.
  apply WF_kron. reflexivity. reflexivity. apply WF_I. apply H.
  apply WF_kron. reflexivity. reflexivity. apply WF_swap. apply WF_I.
  by_cell.
  (* The lma that YT used fails, so running lcas by cell. Still takes a while. *)
  lca. lca. lca. lca. lca. lca. lca. lca.
  lca. lca. lca. lca. lca. lca. lca. lca.
  lca. lca. lca. lca. lca. lca. lca. lca.
  lca. lca. lca. lca. lca. lca. lca. lca.
  lca. lca. lca. lca. lca. lca. lca. lca.
  lca. lca. lca. lca. lca. lca. lca. lca.
  lca. lca. lca. lca. lca. lca. lca. lca.
  lca. lca. lca. lca. lca. lca. lca. lca.
Qed.