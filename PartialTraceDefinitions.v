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
    destruct x as [|x']. contradict H. lia.
    destruct x' as [|x'']. contradict H. lia.
    reflexivity.
}
{
    unfold partial_trace_2q_a.
    destruct x as [|x'].
    {
        destruct y as [|y']. contradict H. lia.
        destruct y' as [|y'']. contradict H. lia.
        reflexivity.
    }
    {
        destruct x' as [|x''].
        destruct y as [|y']. contradict H. lia.
        destruct y' as [|y'']. contradict H. lia.
        reflexivity. reflexivity.
    }
}
Qed.

Lemma partial_trace_2q_a_linear : forall (c:C) (A B : Square 4),
  partial_trace_2q_a (A .+ c .* B) = partial_trace_2q_a A .+ c .* partial_trace_2q_a B.
Proof.
intros.
lma'.
apply WF_partial_trace_2q_a.
apply WF_plus.
apply WF_partial_trace_2q_a.
apply WF_scale.
apply WF_partial_trace_2q_a.
Qed.

Lemma partial_trace_2q_a_compat : forall (A B : Square 4),
  A = B -> partial_trace_2q_a A = partial_trace_2q_a B.
Proof.
intros.
lma'.
apply WF_partial_trace_2q_a.
apply WF_partial_trace_2q_a.
unfold partial_trace_2q_a. rewrite H. reflexivity.
unfold partial_trace_2q_a. rewrite H. reflexivity.
unfold partial_trace_2q_a. rewrite H. reflexivity.
unfold partial_trace_2q_a. rewrite H. reflexivity.
Qed.

Definition partial_trace_2q_b (M: Square 4): Square 2 :=
    fun x y =>
    match (x,y) with
    | (0,0) => (M 0 0)%nat + (M 1 1)%nat
    | (0,1) => (M 0 2)%nat + (M 1 3)%nat
    | (1,0) => (M 2 0)%nat + (M 3 1)%nat
    | (1,1) => (M 2 2)%nat + (M 3 3)%nat
    | _ => C0
    end.

Lemma WF_partial_trace_2q_b : forall (A : Square 4),
    WF_Matrix (partial_trace_2q_b A).
Proof.
unfold WF_Matrix.
intros.
unfold partial_trace_2q_b.
destruct H.
destruct x as [|a]. contradict H. lia.
destruct a as [|b]. contradict H. lia. reflexivity.
destruct x as [|a].
destruct y as [|b]. contradict H. lia.
destruct b as [|c]. contradict H. lia. reflexivity.
destruct a as [|x].
destruct y as [|b]. contradict H. lia.
destruct b as [|c]. contradict H. lia. reflexivity.
reflexivity.
Qed.

Lemma partial_trace_2q_b_linear : forall (c:C) (A B : Square 4),
  partial_trace_2q_b (A .+ c .* B) = partial_trace_2q_b A .+ c .* partial_trace_2q_b B.
Proof.
intros.
lma'.
apply WF_partial_trace_2q_b.
apply WF_plus.
apply WF_partial_trace_2q_b.
apply WF_scale.
apply WF_partial_trace_2q_b.
Qed.

Lemma partial_trace_2q_b_compat : forall (A B : Square 4),
  A = B -> partial_trace_2q_b A = partial_trace_2q_b B.
Proof.
intros.
lma'.
apply WF_partial_trace_2q_b.
apply WF_partial_trace_2q_b.
unfold partial_trace_2q_b. rewrite H. reflexivity.
unfold partial_trace_2q_b. rewrite H. reflexivity.
unfold partial_trace_2q_b. rewrite H. reflexivity.
unfold partial_trace_2q_b. rewrite H. reflexivity.
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
    destruct x as [|x']. contradict H. lia.
    destruct x' as [|x'']. contradict H. lia.
    destruct x'' as [|x''']. contradict H. lia.
    destruct x''' as [|x'''']. contradict H. lia.
    reflexivity.
}
{
    unfold partial_trace_3q_a.
    destruct x as [|x'].
    {
        destruct y as [|y']. contradict H. lia.
        destruct y' as [|y'']. contradict H. lia.
        destruct y'' as [|y''']. contradict H. lia.
        destruct y''' as [|y'''']. contradict H. lia.
        reflexivity.
    }
    destruct x' as [|x''].
    { 
        destruct y as [|y']. contradict H. lia.
        destruct y' as [|y'']. contradict H. lia.
        destruct y'' as [|y''']. contradict H. lia.
        destruct y''' as [|y'''']. contradict H. lia.
        reflexivity.
    }
    destruct x'' as [|x'''].
    { 
        destruct y as [|y']. contradict H. lia.
        destruct y' as [|y'']. contradict H. lia.
        destruct y'' as [|y''']. contradict H. lia.
        destruct y''' as [|y'''']. contradict H. lia.
        reflexivity.
    }
    destruct x''' as [|x''''].
    { 
        destruct y as [|y']. contradict H. lia.
        destruct y' as [|y'']. contradict H. lia.
        destruct y'' as [|y''']. contradict H. lia.
        destruct y''' as [|y'''']. contradict H. lia.
        reflexivity.
    }
    reflexivity.
}
Qed.

Lemma partial_trace_3q_a_linear : forall (c:C) (A B : Square 4),
  partial_trace_3q_a (A .+ c .* B) = partial_trace_3q_a A .+ c .* partial_trace_3q_a B.
Proof.
intros.
lma'.
apply WF_partial_trace_3q_a.
apply WF_plus.
apply WF_partial_trace_3q_a.
apply WF_scale.
apply WF_partial_trace_3q_a.
Qed.

Lemma partial_trace_3q_a_compat : forall (A B : Square 4),
  A = B -> partial_trace_3q_a A = partial_trace_3q_a B.
Proof.
intros.
lma'.
apply WF_partial_trace_3q_a.
apply WF_partial_trace_3q_a.
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

Definition partial_trace_3q_c (M: Square 8): Square 4 :=
    fun x y =>
    match (x,y) with
    | (0,0) => (M 0 0)%nat + (M 1 1)%nat
    | (0,1) => (M 0 2)%nat + (M 1 3)%nat
    | (0,2) => (M 0 4)%nat + (M 1 5)%nat
    | (0,3) => (M 0 6)%nat + (M 1 7)%nat
    | (1,0) => (M 2 0)%nat + (M 3 1)%nat
    | (1,1) => (M 2 2)%nat + (M 3 3)%nat
    | (1,2) => (M 2 4)%nat + (M 3 5)%nat
    | (1,3) => (M 2 6)%nat + (M 3 7)%nat
    | (2,0) => (M 4 0)%nat + (M 5 1)%nat
    | (2,1) => (M 4 2)%nat + (M 5 3)%nat
    | (2,2) => (M 4 4)%nat + (M 5 5)%nat
    | (2,3) => (M 4 6)%nat + (M 5 7)%nat
    | (3,0) => (M 6 0)%nat + (M 7 1)%nat
    | (3,1) => (M 6 2)%nat + (M 7 3)%nat
    | (3,2) => (M 6 4)%nat + (M 7 5)%nat
    | (3,3) => (M 6 6)%nat + (M 7 7)%nat
    | _ => C0
    end.

Lemma WF_partial_trace_3q_c : forall (A : Square 8),
    WF_Matrix (partial_trace_3q_c A).
Proof.
unfold WF_Matrix.
intros.
destruct H.
{
    unfold partial_trace_3q_c.
    destruct x as [|x']. contradict H. lia.
    destruct x' as [|x'']. contradict H. lia.
    destruct x'' as [|x''']. contradict H. lia.
    destruct x''' as [|x'''']. contradict H. lia.
    reflexivity.
}
{
    unfold partial_trace_3q_c.
    destruct x as [|x'].
    {
        destruct y as [|y']. contradict H. lia.
        destruct y' as [|y'']. contradict H. lia.
        destruct y'' as [|y''']. contradict H. lia.
        destruct y''' as [|y'''']. contradict H. lia.
        reflexivity.
    }
    destruct x' as [|x''].
    { 
        destruct y as [|y']. contradict H. lia.
        destruct y' as [|y'']. contradict H. lia.
        destruct y'' as [|y''']. contradict H. lia.
        destruct y''' as [|y'''']. contradict H. lia.
        reflexivity.
    }
    destruct x'' as [|x'''].
    { 
        destruct y as [|y']. contradict H. lia.
        destruct y' as [|y'']. contradict H. lia.
        destruct y'' as [|y''']. contradict H. lia.
        destruct y''' as [|y'''']. contradict H. lia.
        reflexivity.
    }
    destruct x''' as [|x''''].
    { 
        destruct y as [|y']. contradict H. lia.
        destruct y' as [|y'']. contradict H. lia.
        destruct y'' as [|y''']. contradict H. lia.
        destruct y''' as [|y'''']. contradict H. lia.
        reflexivity.
    }
    reflexivity.
}
Qed.

Lemma partial_trace_3q_c_linear : forall (c:C) (A B : Square 4),
  partial_trace_3q_c (A .+ c .* B) = partial_trace_3q_c A .+ c .* partial_trace_3q_c B.
Proof.
intros.
lma'.
apply WF_partial_trace_3q_c.
apply WF_plus.
apply WF_partial_trace_3q_c.
apply WF_scale.
apply WF_partial_trace_3q_c.
Qed.

Lemma partial_trace_3q_c_compat : forall (A B : Square 4),
  A = B -> partial_trace_3q_c A = partial_trace_3q_c B.
Proof.
intros.
lma'.
apply WF_partial_trace_3q_c.
apply WF_partial_trace_3q_c.
unfold partial_trace_3q_c. rewrite H. reflexivity.
unfold partial_trace_3q_c. rewrite H. reflexivity.
unfold partial_trace_3q_c. rewrite H. reflexivity.
unfold partial_trace_3q_c. rewrite H. reflexivity.
unfold partial_trace_3q_c. rewrite H. reflexivity.
unfold partial_trace_3q_c. rewrite H. reflexivity.
unfold partial_trace_3q_c. rewrite H. reflexivity.
unfold partial_trace_3q_c. rewrite H. reflexivity.
unfold partial_trace_3q_c. rewrite H. reflexivity.
unfold partial_trace_3q_c. rewrite H. reflexivity.
unfold partial_trace_3q_c. rewrite H. reflexivity.
unfold partial_trace_3q_c. rewrite H. reflexivity.
unfold partial_trace_3q_c. rewrite H. reflexivity.
unfold partial_trace_3q_c. rewrite H. reflexivity.
unfold partial_trace_3q_c. rewrite H. reflexivity.
unfold partial_trace_3q_c. rewrite H. reflexivity.
Qed.