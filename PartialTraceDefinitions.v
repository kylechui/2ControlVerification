Require Import QuantumLib.Matrix.
Definition partial_trace_2q_a (M: Square 4): Square 2 :=
    fun x y =>
    match (x,y) with
    | (0,0) => (M 0 0)%nat + (M 2 2)%nat
    | (0,1) => (M 0 1)%nat + (M 2 3)%nat
    | (1,0) => (M 1 0)%nat + (M 3 2)%nat
    | (1,1) => (M 1 1)%nat + (M 3 3)%nat
    | _ => C0
    end.

Lemma WF_partial_trace_2q_a : forall (A : Square 4),
    WF_Matrix (partial_trace_2q_a A).
Proof.
unfold WF_Matrix.
intros.
destruct H.
{
    unfold partial_trace_2q_a.
    destruct x as [|x'].
    contradict H.
    lia.
    destruct x' as [|x''].
    contradict H.
    lia.
    reflexivity.
}
{
    unfold partial_trace_2q_a.
    destruct x as [|x'].
    {
        destruct y as [|y'].
        contradict H.
        lia.
        destruct y' as [|y''].
        contradict H.
        lia.
        reflexivity.
    }
    {
        destruct x' as [|x''].
        destruct y as [|y'].
        contradict H.
        lia.
        destruct y' as [|y''].
        contradict H.
        lia.
        reflexivity.
        reflexivity.
    }
}
Qed.

Lemma partial_trace_2q_a_linear : forall (c:C) (A B : Square 4),
  partial_trace_2q_a (A .+ c .* B) = partial_trace_2q_a A .+ c .* partial_trace_2q_a B.
Proof.
intros.
apply mat_equiv_eq.
apply WF_partial_trace_2q_a.
apply WF_plus.
apply WF_partial_trace_2q_a.
apply WF_scale.
apply WF_partial_trace_2q_a.
by_cell.
{
    unfold partial_trace_2q_a; unfold scale; unfold Mplus.
    lca.
}
{
    unfold partial_trace_2q_a; unfold scale; unfold Mplus.
    lca.
}
{
    unfold partial_trace_2q_a; unfold scale; unfold Mplus.
    lca.
}
{
    unfold partial_trace_2q_a; unfold scale; unfold Mplus.
    lca.
}
Qed.

Lemma partial_trace_2q_a_compat : forall (A B : Square 4),
  A = B -> partial_trace_2q_a A = partial_trace_2q_a B.
Proof.
intros.
apply mat_equiv_eq.
apply WF_partial_trace_2q_a.
apply WF_partial_trace_2q_a.
by_cell.
{
    unfold partial_trace_2q_a.
    rewrite H.
    reflexivity.
}
{
    unfold partial_trace_2q_a.
    rewrite H.
    reflexivity.
}
{
    unfold partial_trace_2q_a.
    rewrite H.
    reflexivity.
}
{
    unfold partial_trace_2q_a.
    rewrite H.
    reflexivity.
}
Qed.