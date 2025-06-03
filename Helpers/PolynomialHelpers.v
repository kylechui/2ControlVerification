Require Import QuantumLib.Complex.
Require Import QuantumLib.Polynomial.
Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.
Require Import QuantumLib.Eigenvectors.
Require Import QuantumLib.Permutations.
Require Import MatrixHelpers.
Require Import DiagonalHelpers.
Require Import UnitaryHelpers.
Require Import Permutations.
Require Import Setoid.

Module P := Polynomial.

(* Open the polynomial scope *)
Local Open Scope poly_scope.

(* Define a function to create a polynomial with a root at a given point *)
Definition linear_poly (c : C) : Polynomial := [- c; C1].

(* Define a function to create a polynomial (x - c) *)
Definition x_minus_c (c : C) : Polynomial := linear_poly c.

(* Define a function to create a polynomial (c - x) *)
Definition c_minus_x (c : C) : Polynomial := [c; -C1].

(* A collection of linear factors *)
Definition Factors := list C.

Fixpoint poly_prod (c : Factors) : Polynomial :=
  match c with
  | nil    => [C1]
  | h :: t => [h; -C1] *, poly_prod t
  end.

(* Lemma 1.1 *)
Lemma complex_poly_degree : forall (q : Polynomial) (d : C),
    Peval ([d; -C1] *, q) <> Peval [C1].
Proof.
  intros q d Heq'.
  apply degree_mor in Heq' as Hdeg.
  assert (Heq : ([d; - C1] *, q) ≅ [C1]) by apply Heq'.
  unfold degree at 2 in Hdeg.
  unfold compactify in Hdeg.
  simpl length in Hdeg.
  destruct (Ceq_dec C1 C0) as [H01 | _]; try (inversion H01; lra).
  simpl rev in Hdeg.
  assert (H_nil_neq_1 : ~ ([] ≅ [C1])).
  { intro H_nil_1.
    assert ([][[0]] = [C1][[0]]) by now rewrite H_nil_1.
    unfold Peval in H; simpl in H.
    inversion H; lra. }
  assert (Hq_neq_nil : ~ (q ≅ [])).
  { intro H_qnil.
    setoid_rewrite H_qnil in Heq.
    now rewrite P.Pmult_0_r in Heq. }
  assert (Hdx_neq_nil : ~ ([d; - C1] ≅ [])).
  { intro H_dxnil.
    setoid_rewrite H_dxnil in Heq.
    now simpl in Heq. }
  rewrite (Pmult_degree _ _ Hdx_neq_nil Hq_neq_nil) in Hdeg.

  unfold degree at 1 in Hdeg.
  unfold compactify in Hdeg.
  simpl in Hdeg.
  destruct (Ceq_dec (-C1) 0) as [H01 | _]; try (inversion H01; lra).
  simpl in Hdeg. lia.
Qed.

(* Lemma 1.2 (Euclid's Lemma) *)
Lemma euclid_lemma : forall {d e : C} {p r : Polynomial},
  [d; -C1] *, p ≅ r *, [e; -C1] ->
  d = e \/ exists (q : Polynomial), [d; -C1] *, q ≅ r.
Proof.
  (* TODO: the polynomial theorem names collide with Coq.PArith *)

  intros d e p r Heq.
  destruct (Ceq_dec d e) as [| Hneq]; [auto | right].
  apply Cminus_eq_contra in Hneq.

  (* construct 1/(d - e) * (r - p) *)
  exists ([/ (d - e)] *, (r +, -,p)).
  rewrite P.Pmult_comm.
  rewrite P.Pmult_assoc.
  rewrite P.Pmult_plus_distr_r.
  rewrite P.Pmult_comm in Heq.
  unfold Popp.
  rewrite P.Pmult_assoc, Heq.
  rewrite <- P.Pmult_assoc.
  rewrite (P.Pmult_comm ([-C1])).
  rewrite P.Pmult_assoc.
  rewrite <- (P.Pmult_plus_distr_l r).
  simpl P.Pplus.
  replace (d + (((- C1) * e) + 0)) with (d - e) by lca.
  replace ((- C1) + ((- C1) * (- C1))) with C0 by lca.
  rewrite (p_Peq_compactify_p [d - e; C0]).

  unfold compactify.
  simpl prune.
  destruct (Ceq_dec 0 0); try easy.
  destruct (Ceq_dec (d - e) 0); try easy.
  simpl rev.

  rewrite (P.Pmult_comm r), <- P.Pmult_assoc.
  simpl P.Pmult at 2; rewrite Cplus_0_r.
  rewrite (Cinv_l _ Hneq).
  apply Pmult_1_l.
Qed.

(* Lemma 1.3 *)
Lemma poly_isolate_factor : forall (d : C) (facs : list C),
    facs <> [] ->
    (forall (p : Polynomial),
      [d; -C1] *, p ≅ poly_prod facs ->
      exists (k : nat), nth_error facs k = Some d).
Proof.
  intros d facs.
  induction facs as [| f facs IH]; try contradiction.
  destruct facs as [| f0 facs].
  - (* singleton list *)
    intros _ p0 Heq. clear IH.
    exists 0%nat.
    simpl in *.

    repeat rewrite Cplus_0_r in Heq.
    repeat rewrite Cmult_1_r in Heq.

    rewrite <- (Pmult_1_l [f; -C1]) in Heq.
    destruct (euclid_lemma Heq) as [ Hdf | [q Hex] ]; try (subst; auto).
    now apply complex_poly_degree in Hex.

  - intros _ p0 Heq.
    specialize (IH ltac:(easy)).
    setoid_replace
      (poly_prod (f :: f0 :: facs)) with
      ([f; -C1] *, poly_prod (f0 :: facs))
      using relation Peq in Heq.
    2: {
      unfold poly_prod.
      now repeat rewrite <- P.Pmult_assoc.
    }
    unfold poly_prod in *.
    fold poly_prod in *.
    rewrite (P.Pmult_comm [f; -C1]) in Heq.
    destruct (euclid_lemma Heq) as [ Hdf | [q Hex] ].
    + exists 0%nat.
      subst. auto.
    + destruct (IH q Hex) as [k Hk].
      exists (S k).
      auto.
Qed.

Lemma singleton_list : forall {T} {l : list T},
  (length l = 1)%nat -> exists x, l = [x].
Proof.
  intros.
  destruct l; try inversion H.
  destruct l; try inversion H1.
  now exists t.
Qed.

Lemma poly_prod_middle : forall (l1 l2 : Factors) (f : C), poly_prod (l1 ++ f :: l2) ≅ poly_prod (f :: l1 ++ l2).
Proof.
  intro l1.
  induction l1; try reflexivity.
  intros l2 f.
  simpl app.
  unfold poly_prod; fold poly_prod.
  rewrite IHl1.
  unfold poly_prod; fold poly_prod.
  do 2 rewrite <- P.Pmult_assoc.
  now rewrite (P.Pmult_comm [a; -C1] [f; -C1]).
Qed.

Lemma Pmult_0_factor : forall (p1 p2 : Polynomial),
  (p1 *, p2) ≅ [] -> p1 ≅ [] \/ p2 ≅ [].
Proof.
  intros p1 p2 H.
  destruct (Peq_0_dec p1), (Peq_0_dec p2); try auto.
  destruct (Pmult_neq_0 _ _ n n0); auto.
Qed.

(* Lemma 1.4 *)
Lemma Pfac_cancel_l : forall (d : C) (p1 p2 : Polynomial),
    [d; -C1] *, p1 ≅ [d; -C1] *, p2 -> p1 ≅ p2.
Proof.
  intros d p1 p2 Hnil.
  pose proof (H := Pplus_mor _ _ Hnil ([d; -C1] *, -, p2) _ ltac:(reflexivity)).
  rewrite <- P.Pmult_plus_distr_l in H.
  unfold Popp in H.
  rewrite <- P.Pmult_assoc in H.
  rewrite (P.Pmult_comm [d; -C1] [- C1]) in H.
  rewrite P.Pmult_assoc in H.
  rewrite Pplus_opp_r in H.
  destruct (Pmult_0_factor _ _ H).
  - apply degree_mor in H0. unfold degree in H0.
    unfold compactify in H0.
    simpl in H0.
    destruct (Ceq_dec (-C1) 0%R) as [H01 | _]; try (inversion H01; lra).
    simpl in H0. lia.
  - pose proof (H' := Pplus_mor _ _ H0 p2  _ ltac:(reflexivity)).
    rewrite P.Pplus_assoc in H'.
    setoid_replace ([-C1] *, p2 +, p2) with
      ([] : Polynomial) in H' by now rewrite Pplus_opp_l.
    simpl in H'. now rewrite P.Pplus_0_r in H'.
Qed.

(* Lemma 1.5 *)
Lemma roots_equal_implies_permutation :
  forall (n : nat),
  (n > 0)%nat ->
  forall (ds es: list C),
  length ds = n -> length es = n ->
  (poly_prod ds ≅ poly_prod es) ->
  exists f, permutation n f /\ (forall i, ds !! i = es !! f i).
Proof.
  intros n.
  induction n; try lia.
  (* intros. *)
  intros H ds es Hdlen Helen Hpeq.
  destruct n as [| n].
  - exists idn.
    split.
    + (* Permutation *)
      apply idn_permutation.
    + (* perm_pair_eq *)
      destruct (singleton_list Hdlen) as [delem Hd].
      destruct (singleton_list Helen) as [eelem He].
      subst.
      destruct i.
      * unfold poly_prod in Hpeq.
        simpl; f_equal.
        simpl in Hpeq.
        apply Peq_head_eq in Hpeq.
        (* Why can't we use lca here? *)
        repeat rewrite Cplus_0_r in Hpeq.
        repeat rewrite Cmult_1_r in Hpeq.
        auto.
      * easy.
  - remember (S n) as N. clear H.
    specialize (IHn ltac:(lia)).
    destruct ds as [| d ds]; try easy.
    assert (Heneqnil : es <> []).
    { intro Hcontra.
      subst. easy. }
    destruct (poly_isolate_factor d es Heneqnil (poly_prod ds) Hpeq) as [k Hk].
    assert (Hk_le_n : (k < S N)%nat).
    { rewrite <- Helen.
      rewrite <- nth_error_Some.
      now rewrite Hk. }
    clear Heneqnil.

    (* break 'es' into multiple pieces *)
    destruct (nth_error_split es k Hk) as [e1 [e2 [Hcombine Hidx] ] ].
    rewrite Hcombine in Hpeq.

    rewrite poly_prod_middle in Hpeq.
    unfold poly_prod in Hpeq. fold poly_prod in Hpeq.

    assert (Hleneq : length (e1 ++ e2) = N).
    { subst.
      rewrite app_length in *.
      simpl in *.
      lia. }

    specialize (IHn ds (e1 ++ e2) ltac:(auto) Hleneq).

    assert (Hpeq' : poly_prod ds ≅ poly_prod (e1 ++ e2)).
    { now apply Pfac_cancel_l in Hpeq. }
    clear Hpeq.

    destruct (IHn ltac:(easy)) as [f' [Hperm Hpermeq] ].

    pose (f := fun i =>
              match i with
              | 0 => k
              | S i' =>
                  let j := f' i' in
                  if j <? k then j else S j
              end).

    exists f.

    split.
    { destruct Hperm as [f'inv Hf'inv].

      pose (finv := fun j =>
                if j =? k then 0%nat else
                  if j <? k then S (f'inv j)
                  else S (f'inv (pred j))).
      exists finv.
      intros x Hx.
      repeat split.
      - (* f x < S (S n) *)
        destruct x.
        + unfold f. subst.
          rewrite app_length in Helen.
          simpl in Helen.
          lia.
        + specialize (Hf'inv x ltac:(lia)).
          simpl. destruct (f' x <? k) eqn:E; lia.
      - (* finv x < S (S n) *)
        unfold finv.
        bdestruct_all; try (rewrite <- Nat.succ_lt_mono).
        + (* k <= N *)
          now destruct (Hf'inv x ltac:(lia)).
        + lia.
        + (* f'inv (pred x) < N *)
          destruct x; simpl.
          * now destruct (Hf'inv 0%nat ltac:(lia)).
          * now destruct (Hf'inv x ltac:(lia)).
      - (* finv (f x) = x *)
        unfold finv, f.
        destruct x.
        + (* x = 0 *)
          simpl.
          bdestruct (k =? k); [ lia | easy ].
        + bdestruct_all; simpl; destruct (Hf'inv x ltac:(lia)); lia.
      - (* f (finv x) = x *)
        unfold finv, f.
        destruct x.
        + bdestruct_all; try (destruct (Hf'inv 0%nat ltac:(lia))); lia.
        + bdestruct_all.
          * destruct (Hf'inv (S x) ltac:(lia)). lia.
          * destruct (Hf'inv (S x) ltac:(lia)). lia.
          * auto.
          * simpl in *. destruct (Hf'inv x ltac:(lia)). lia.
          * destruct (Hf'inv x ltac:(lia)). simpl. lia.
    }

    unfold permutation.
    intros i.
    destruct i as [| i']; try auto.
    subst.
    simpl.
    rewrite Hpermeq.
    bdestruct (f' i' <? length e1)%nat.
    + do 2 rewrite (nth_error_app1 _ _ H); reflexivity.
    + replace (e1 ++ d :: e2) with ((e1 ++ [d]) ++ e2)
        by ( rewrite <- app_assoc; auto ).
      assert (Hsecond : (length (e1 ++ [d]) <= S (f' i'))%nat).
      { rewrite app_length. simpl. lia. }
      rewrite (nth_error_app2 _ _ H).
      rewrite (nth_error_app2 _ _ Hsecond).
      rewrite app_length.
      simpl length.
      rewrite Nat.add_1_r.
      auto.
Qed.
