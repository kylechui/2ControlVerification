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

Definition partial_trace_3q_a (M: Square 8): Square 4 :=
    fun x y =>
    match (x,y) with
    | (0,0) => (M 0 0)%nat + (M 4 4)%nat
    | (0,1) => (M 0 1)%nat + (M 4 5)%nat
    | (0,2) => (M 0 2)%nat + (M 4 6)%nat
    | (0,3) => (M 0 3)%nat + (M 4 7)%nat
    | (1,0) => (M 1 0)%nat + (M 5 4)%nat
    | (1,1) => (M 1 1)%nat + (M 5 5)%nat
    | (1,2) => (M 1 2)%nat + (M 5 6)%nat
    | (1,3) => (M 1 3)%nat + (M 5 7)%nat
    | (2,0) => (M 2 0)%nat + (M 6 4)%nat
    | (2,1) => (M 2 1)%nat + (M 6 5)%nat
    | (2,2) => (M 2 2)%nat + (M 6 6)%nat
    | (2,3) => (M 2 3)%nat + (M 6 7)%nat
    | (3,0) => (M 3 0)%nat + (M 7 4)%nat
    | (3,1) => (M 3 1)%nat + (M 7 5)%nat
    | (3,2) => (M 3 2)%nat + (M 7 6)%nat
    | (3,3) => (M 3 3)%nat + (M 7 7)%nat
    | _ => C0
    end.

Lemma WF_partial_trace_3q_a : forall (A : Square 8),
    WF_Matrix (partial_trace_3q_a A).
Proof.
unfold WF_Matrix.
intros.
destruct H.
{
    unfold partial_trace_3q_a.
    destruct x as [|x'].
    contradict H.
    lia.
    destruct x' as [|x''].
    contradict H.
    lia.
    destruct x'' as [|x'''].
    contradict H.
    lia.
    destruct x''' as [|x''''].
    contradict H.
    lia.
    reflexivity.
}
{
    unfold partial_trace_3q_a.
    destruct x as [|x'].
    {
        destruct y as [|y'].
        contradict H.
        lia.
        destruct y' as [|y''].
        contradict H.
        lia.
        destruct y'' as [|y'''].
        contradict H.
        lia.
        destruct y''' as [|y''''].
        contradict H.
        lia.
        reflexivity.
    }
    destruct x' as [|x''].
    { 
        destruct y as [|y'].
        contradict H.
        lia.
        destruct y' as [|y''].
        contradict H.
        lia.
        destruct y'' as [|y'''].
        contradict H.
        lia.
        destruct y''' as [|y''''].
        contradict H.
        lia.
        reflexivity.
    }
    destruct x'' as [|x'''].
    { 
        destruct y as [|y'].
        contradict H.
        lia.
        destruct y' as [|y''].
        contradict H.
        lia.
        destruct y'' as [|y'''].
        contradict H.
        lia.
        destruct y''' as [|y''''].
        contradict H.
        lia.
        reflexivity.
    }
    destruct x''' as [|x''''].
    { 
        destruct y as [|y'].
        contradict H.
        lia.
        destruct y' as [|y''].
        contradict H.
        lia.
        destruct y'' as [|y'''].
        contradict H.
        lia.
        destruct y''' as [|y''''].
        contradict H.
        lia.
        reflexivity.
    }
    reflexivity.
}
Qed.

Lemma partial_trace_3q_a_linear : forall (c:C) (A B : Square 4),
  partial_trace_3q_a (A .+ c .* B) = partial_trace_3q_a A .+ c .* partial_trace_3q_a B.
Proof.
intros.
apply mat_equiv_eq.
apply WF_partial_trace_3q_a.
apply WF_plus.
apply WF_partial_trace_3q_a.
apply WF_scale.
apply WF_partial_trace_3q_a.
by_cell.
unfold partial_trace_3q_a; unfold scale; unfold Mplus. lca.
unfold partial_trace_3q_a; unfold scale; unfold Mplus. lca.
unfold partial_trace_3q_a; unfold scale; unfold Mplus. lca.
unfold partial_trace_3q_a; unfold scale; unfold Mplus. lca.
unfold partial_trace_3q_a; unfold scale; unfold Mplus. lca.
unfold partial_trace_3q_a; unfold scale; unfold Mplus. lca.
unfold partial_trace_3q_a; unfold scale; unfold Mplus. lca.
unfold partial_trace_3q_a; unfold scale; unfold Mplus. lca.
unfold partial_trace_3q_a; unfold scale; unfold Mplus. lca.
unfold partial_trace_3q_a; unfold scale; unfold Mplus. lca.
unfold partial_trace_3q_a; unfold scale; unfold Mplus. lca.
unfold partial_trace_3q_a; unfold scale; unfold Mplus. lca.
unfold partial_trace_3q_a; unfold scale; unfold Mplus. lca.
unfold partial_trace_3q_a; unfold scale; unfold Mplus. lca.
unfold partial_trace_3q_a; unfold scale; unfold Mplus. lca.
unfold partial_trace_3q_a; unfold scale; unfold Mplus. lca.
Qed.

Lemma partial_trace_3q_a_compat : forall (A B : Square 4),
  A = B -> partial_trace_3q_a A = partial_trace_3q_a B.
Proof.
intros.
apply mat_equiv_eq.
apply WF_partial_trace_3q_a.
apply WF_partial_trace_3q_a.
by_cell.
unfold partial_trace_3q_a. rewrite H. reflexivity.
unfold partial_trace_3q_a. rewrite H. reflexivity.
unfold partial_trace_3q_a. rewrite H. reflexivity.
unfold partial_trace_3q_a. rewrite H. reflexivity.
unfold partial_trace_3q_a. rewrite H. reflexivity.
unfold partial_trace_3q_a. rewrite H. reflexivity.
unfold partial_trace_3q_a. rewrite H. reflexivity.
unfold partial_trace_3q_a. rewrite H. reflexivity.
unfold partial_trace_3q_a. rewrite H. reflexivity.
unfold partial_trace_3q_a. rewrite H. reflexivity.
unfold partial_trace_3q_a. rewrite H. reflexivity.
unfold partial_trace_3q_a. rewrite H. reflexivity.
unfold partial_trace_3q_a. rewrite H. reflexivity.
unfold partial_trace_3q_a. rewrite H. reflexivity.
unfold partial_trace_3q_a. rewrite H. reflexivity.
unfold partial_trace_3q_a. rewrite H. reflexivity.
Qed.