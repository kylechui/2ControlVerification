Require Import QuantumLib.Quantum.
From Proof Require Import GateHelpers.
From Proof Require Import SwapHelpers.

Property swap_helper : forall (U : Square 4),
  WF_Matrix U -> 
  acgate U = swapab × bcgate U × swapab.
Proof.
  intros. 
  apply mat_equiv_eq.
  apply WF_acgate. apply H.
  apply WF_mult. apply WF_mult. apply WF_swapab. apply WF_bcgate. apply H. apply WF_swapab.
  unfold acgate; unfold bcgate; unfold abgate.
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