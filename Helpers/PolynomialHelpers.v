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

(* Given an assumption H : A -> B, prove A then specialize H with that proof, yielding H : B. *)
Ltac forward H :=
  match type of H with
  | (?A -> ?B) =>
    let H1 := fresh "H" in
    assert (H1 : A); [ | specialize (H H1); clear H1]
  end.

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

Lemma Peval_nil : forall c, ([][[c]]) = C0.
Proof.
  intros.
  reflexivity.
Qed.

(* Lemma to show that (x - c) evaluates to (a - c) at x = a *)
Lemma x_minus_c_eval : forall (a c : C),
  (x_minus_c c)[[a]] = a - c.
Proof.
  intros a c.
  unfold x_minus_c, linear_poly.
  simpl.
  repeat rewrite cons_eval.
  rewrite Peval_nil.
  lca.
Qed.

(* Define a function to create a product of (x - c_i) terms *)
Fixpoint prod_x_minus_c (cs : list C) : Polynomial :=
  match cs with
  | [] => [C1]  (* Empty product is 1 *)
  | c :: cs' => (x_minus_c c) *, (prod_x_minus_c cs')
  end.

(* Define a function to create a product of (c_i - x) terms *)
Fixpoint prod_c_minus_x (cs : list C) : Polynomial :=
  match cs with
  | [] => [C1]  (* Empty product is 1 *)
  | c :: cs' => (c_minus_x c) *, (prod_c_minus_x cs')
  end.

(* Define a big product function for complex numbers *)
Fixpoint big_prod (f : nat -> C) (n : nat) : C :=
  match n with
  | 0 => C1  (* Empty product is 1 *)
  | S n' => (f n') * (big_prod f n')
  end.

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
    inversion H; lra.}
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

(* Lemma 1.1 (Euclid's Lemma) *)
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
    forward IH. { easy. }
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
  unfold poly_prod.
  fold poly_prod.
  rewrite IHl1.
  unfold poly_prod.
  fold poly_prod.
  rewrite <- P.Pmult_assoc.
  rewrite <- P.Pmult_assoc.
  now rewrite (P.Pmult_comm [a; -C1] [f; -C1]).
Qed.

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
  - clear H.
    forward IHn. { lia. }
    destruct ds as [| d ds]; try easy.
    assert (Heneqnil : es <> []).
    { intro Hcontra.
      subst. easy. }
    destruct (poly_isolate_factor d es Heneqnil (poly_prod ds) Hpeq) as [k Hk].
    clear Heneqnil.

    (* break 'es' into multiple pieces *)
    destruct (nth_error_split es k Hk) as [e1 [e2 [Hcombine Hidx] ] ].
    rewrite Hcombine in Hpeq.

    rewrite poly_prod_middle in Hpeq.
    unfold poly_prod in Hpeq. fold poly_prod in Hpeq.

    specialize (IHn ds (e1 ++ e2)).
    forward IHn. { auto. }
    forward IHn.
    { rewrite Hcombine in Helen.
      rewrite app_length in *.
      simpl in Helen.
      lia. }

    (* We need rcancel_mul for polynomials *)
    assert (Hpeq' : poly_prod ds ≅ poly_prod (e1 ++ e2)). { admit. }
    clear Hpeq.
    forward IHn. { easy. }
    destruct IHn as [f [Hperm Hpermeq] ].

    exists (fun i =>
              match i with
              | 0 => k
              | S i' =>
                  let j := f i' in
                  if j <? k then j else S j
              end).

    (* need inverse of f0 *)
    split. { admit. }

    unfold permutation.
    intros i.
    destruct i as [| i']; try auto.
    subst.
    simpl.
    rewrite Hpermeq.
    bdestruct (f i' <? length e1)%nat.
    + do 2 rewrite (nth_error_app1 _ _ H); reflexivity.
    + replace (e1 ++ d :: e2) with ((e1 ++ [d]) ++ e2)
        by ( rewrite <- app_assoc; auto ).
      assert (Hsecond : (length (e1 ++ [d]) <= S (f i'))%nat).
      { rewrite app_length. simpl. lia. }
      rewrite (nth_error_app2 _ _ H).
      rewrite (nth_error_app2 _ _ Hsecond).
      rewrite app_length.
      simpl length.
      rewrite Nat.add_1_r.
      auto.
Admitted.
