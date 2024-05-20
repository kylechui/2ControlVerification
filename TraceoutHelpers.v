Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.
From Proof Require Import MatrixHelpers.
From Proof Require Import QubitHelpers.
From Proof Require Import PartialTraceDefinitions.
From Proof Require Import GateHelpers.
From Proof Require Import SwapHelpers.
From Proof Require Import ExplicitDecompositions.
From Proof Require Import AlgebraHelpers.
From Proof Require Import WFHelpers.
Lemma partial_trace_ac_on_acgate: forall (U : Square 4) (a b c: Vector 2), 
WF_Unitary U -> WF_Qubit a -> WF_Qubit b -> WF_Qubit c -> 
partial_trace_2q_a (partial_trace_3q_c (acgate U × (a ⊗ b ⊗ c) × (a ⊗ b ⊗ c)† × (acgate U)†))
= b × b†.
Proof.
intros U a b c U_unitary a_qubit b_qubit c_qubit.
assert (WF_U: WF_Matrix U). apply U_unitary.
assert (WF_a: WF_Matrix a). apply a_qubit. 
assert (WF_b: WF_Matrix b). apply b_qubit.
assert (WF_c: WF_Matrix c). apply c_qubit.
apply mat_equiv_eq.
apply WF_partial_trace_2q_a.
solve_WF_matrix.
rewrite kron_adjoint. rewrite kron_adjoint.
rewrite Mmult_assoc. rewrite Mmult_assoc.
rewrite <- Mmult_assoc with (A:=a ⊗ b ⊗ c).
assert (kron_mix_help: a ⊗ b ⊗ c × ((a) † ⊗ (b) † ⊗ (c) †) = (a × (a) †) ⊗ (b × (b) †) ⊗ (c × (c) †)). 
{
    rewrite kron_mixed_product with (A:= a ⊗ b) (B := c) (C:= (a) † ⊗ (b) †) (D:= (c) †).
    rewrite kron_mixed_product.
    reflexivity.
}
rewrite kron_mix_help at 1.
clear kron_mix_help.
unfold acgate.
rewrite Mmult_adjoint.
rewrite <- swapbc_sa at 1.
rewrite Mmult_adjoint.
rewrite <- swapbc_sa.
repeat rewrite Mmult_assoc.
rewrite <- Mmult_assoc with (A:= a × (a) † ⊗ (b × (b) †) ⊗ (c × (c) †)).
rewrite <- Mmult_assoc with (B := a × (a) † ⊗ (b × (b) †) ⊗ (c × (c) †) × swapbc).
rewrite <- Mmult_assoc with (B := a × (a) † ⊗ (b × (b) †) ⊗ (c × (c) †)).
rewrite swapbc_3gate. 2,3,4: solve_WF_matrix.
unfold abgate.
rewrite <- Mmult_assoc with (B := a × (a) † ⊗ (c × (c) †) ⊗ (b × (b) †)).
assert (kron_mix_help: U ⊗ I 2 × (a × (a) † ⊗ (c × (c) †) ⊗ (b × (b) †)) =
 (U × (a × (a) † ⊗ (c × (c) †))) ⊗ (b × (b) †) ).
{
    rewrite <- Mmult_1_l with (A:= (b × (b) †)) at 2; solve_WF_matrix.
    apply kron_mixed_product.
}
rewrite kron_mix_help at 1.
clear kron_mix_help.
rewrite <- Mmult_assoc with (C := swapbc).
assert (kron_adj_helper: (U ⊗ I 2) † = U† ⊗ I 2). lma'.
rewrite kron_adj_helper at 1.
clear kron_adj_helper. 
assert (kron_mix_help: U × (a × (a) † ⊗ (c × (c) †)) ⊗ (b × (b) †) × ((U) † ⊗ I 2) = 
(U × (a × (a) † ⊗ (c × (c) †)) × (U) †) ⊗ (b × (b) †)).
{
    rewrite <- Mmult_1_r with (A:= (b × (b) †)) at 2; solve_WF_matrix.
    apply kron_mixed_product.
}
rewrite kron_mix_help at 1.
assert (WF_helper1: WF_Matrix (U × (a × (a) † ⊗ (c × (c) †)) × (U) † ⊗ (b × (b) †) × swapbc)).
{
    solve_WF_matrix.
}
assert (WF_helper2: WF_Matrix (U × (a × (a) † ⊗ (c × (c) †)) × (U) † ⊗ (b × (b) †))).
{
    solve_WF_matrix.
}
assert (WF_helper3: WF_Matrix (U × (a × (a) † ⊗ (c × (c) †)) × (U) †)).
{
    solve_WF_matrix.
}
assert (WF_helper4: WF_Matrix ((b × (b) †))).
{
    solve_WF_matrix.
}
assert (WF_helper5: WF_Matrix (U × (a × (a) † ⊗ (c × (c) †)))).
{
    solve_WF_matrix.
}
assert (WF_helper6: WF_Matrix (U) †).
{
    solve_WF_matrix.
}
assert (WF_helper8: WF_Matrix (a × (a) † ⊗ (c × (c) †))).
{
    solve_WF_matrix. 
}
set (a00:= (a × (a) † ⊗ (c × (c) †)) 0%nat 0%nat).
set (a10:= (a × (a) † ⊗ (c × (c) †)) 1%nat 0%nat).
set (a20:= (a × (a) † ⊗ (c × (c) †)) 2%nat 0%nat).
set (a30:= (a × (a) † ⊗ (c × (c) †)) 3%nat 0%nat).
set (a01:= (a × (a) † ⊗ (c × (c) †)) 0%nat 1%nat).
set (a11:= (a × (a) † ⊗ (c × (c) †)) 1%nat 1%nat).
set (a21:= (a × (a) † ⊗ (c × (c) †)) 2%nat 1%nat).
set (a31:= (a × (a) † ⊗ (c × (c) †)) 3%nat 1%nat).
set (a02:= (a × (a) † ⊗ (c × (c) †)) 0%nat 2%nat).
set (a12:= (a × (a) † ⊗ (c × (c) †)) 1%nat 2%nat).
set (a22:= (a × (a) † ⊗ (c × (c) †)) 2%nat 2%nat).
set (a32:= (a × (a) † ⊗ (c × (c) †)) 3%nat 2%nat).
set (a03:= (a × (a) † ⊗ (c × (c) †)) 0%nat 3%nat).
set (a13:= (a × (a) † ⊗ (c × (c) †)) 1%nat 3%nat).
set (a23:= (a × (a) † ⊗ (c × (c) †)) 2%nat 3%nat).
set (a33:= (a × (a) † ⊗ (c × (c) †)) 3%nat 3%nat).
set (u00:= U 0%nat 0%nat).
set (u10:= U 1%nat 0%nat).
set (u20:= U 2%nat 0%nat).
set (u30:= U 3%nat 0%nat).
set (u01:= U 0%nat 1%nat).
set (u11:= U 1%nat 1%nat).
set (u21:= U 2%nat 1%nat).
set (u31:= U 3%nat 1%nat).
set (u02:= U 0%nat 2%nat).
set (u12:= U 1%nat 2%nat).
set (u22:= U 2%nat 2%nat).
set (u32:= U 3%nat 2%nat).
set (u03:= U 0%nat 3%nat).
set (u13:= U 1%nat 3%nat).
set (u23:= U 2%nat 3%nat).
set (u33:= U 3%nat 3%nat).
assert (Udag_U_I : (U) † × U = I 4). apply U_unitary.
assert (prod_redist: u00 * a00 * u00 ^* + u01 * a10 * u00 ^* + u02 * a20 * u00 ^* + u03 * a30 * u00 ^* +
(u00 * a01 * u01 ^* + u01 * a11 * u01 ^* + u02 * a21 * u01 ^* + u03 * a31 * u01 ^*) +
(u00 * a02 * u02 ^* + u01 * a12 * u02 ^* + u02 * a22 * u02 ^* + u03 * a32 * u02 ^*) +
(u00 * a03 * u03 ^* + u01 * a13 * u03 ^* + u02 * a23 * u03 ^* + u03 * a33 * u03 ^*) +
(u10 * a00 * u10 ^* + u11 * a10 * u10 ^* + u12 * a20 * u10 ^* + u13 * a30 * u10 ^* +
 (u10 * a01 * u11 ^* + u11 * a11 * u11 ^* + u12 * a21 * u11 ^* + u13 * a31 * u11 ^*) +
 (u10 * a02 * u12 ^* + u11 * a12 * u12 ^* + u12 * a22 * u12 ^* + u13 * a32 * u12 ^*) +
 (u10 * a03 * u13 ^* + u11 * a13 * u13 ^* + u12 * a23 * u13 ^* + u13 * a33 * u13 ^*)) +
(u20 * a00 * u20 ^* + u21 * a10 * u20 ^* + u22 * a20 * u20 ^* + u23 * a30 * u20 ^* +
 (u20 * a01 * u21 ^* + u21 * a11 * u21 ^* + u22 * a21 * u21 ^* + u23 * a31 * u21 ^*) +
 (u20 * a02 * u22 ^* + u21 * a12 * u22 ^* + u22 * a22 * u22 ^* + u23 * a32 * u22 ^*) +
 (u20 * a03 * u23 ^* + u21 * a13 * u23 ^* + u22 * a23 * u23 ^* + u23 * a33 * u23 ^*) +
 (u30 * a00 * u30 ^* + u31 * a10 * u30 ^* + u32 * a20 * u30 ^* + u33 * a30 * u30 ^* +
  (u30 * a01 * u31 ^* + u31 * a11 * u31 ^* + u32 * a21 * u31 ^* + u33 * a31 * u31 ^*) +
  (u30 * a02 * u32 ^* + u31 * a12 * u32 ^* + u32 * a22 * u32 ^* + u33 * a32 * u32 ^*) +
  (u30 * a03 * u33 ^* + u31 * a13 * u33 ^* + u32 * a23 * u33 ^* + u33 * a33 * u33 ^*))) = 
  (u00 * a00 * u00 ^* + u10 * a00 * u10 ^* + u20 * a00 * u20 ^* + u30 * a00 * u30 ^*)
+ (u01 * a10 * u00 ^* + u11 * a10 * u10 ^* + u21 * a10 * u20 ^* + u31 * a10 * u30 ^*)
+ (u02 * a20 * u00 ^* + u12 * a20 * u10 ^* + u22 * a20 * u20 ^* + u32 * a20 * u30 ^*)
+ (u03 * a30 * u00 ^* + u13 * a30 * u10 ^* + u23 * a30 * u20 ^* + u33 * a30 * u30 ^*)
+ (u00 * a01 * u01 ^* + u10 * a01 * u11 ^* + u20 * a01 * u21 ^* + u30 * a01 * u31 ^*)
+ (u01 * a11 * u01 ^* + u11 * a11 * u11 ^* + u21 * a11 * u21 ^* + u31 * a11 * u31 ^*)
+ (u02 * a21 * u01 ^* + u12 * a21 * u11 ^* + u22 * a21 * u21 ^* + u32 * a21 * u31 ^*)
+ (u03 * a31 * u01 ^* + u13 * a31 * u11 ^* + u23 * a31 * u21 ^* + u33 * a31 * u31 ^*)
+ (u00 * a02 * u02 ^* + u10 * a02 * u12 ^* + u20 * a02 * u22 ^* + u30 * a02 * u32 ^*)
+ (u01 * a12 * u02 ^* + u11 * a12 * u12 ^* + u21 * a12 * u22 ^* + u31 * a12 * u32 ^*)
+ (u02 * a22 * u02 ^* + u12 * a22 * u12 ^* + u22 * a22 * u22 ^* + u32 * a22 * u32 ^*)
+ (u03 * a32 * u02 ^* + u13 * a32 * u12 ^* + u23 * a32 * u22 ^* + u33 * a32 * u32 ^*)
+ (u00 * a03 * u03 ^* + u10 * a03 * u13 ^* + u20 * a03 * u23 ^* + u30 * a03 * u33 ^*)
+ (u01 * a13 * u03 ^* + u11 * a13 * u13 ^* + u21 * a13 * u23 ^* + u31 * a13 * u33 ^*)
+ (u02 * a23 * u03 ^* + u12 * a23 * u13 ^* + u22 * a23 * u23 ^* + u32 * a23 * u33 ^*)
+ (u03 * a33 * u03 ^* + u13 * a33 * u13 ^* + u23 * a33 * u23 ^* + u33 * a33 * u33 ^*)
).
{
    lca.
}
assert (a00_extract: 
u00 * a00 * u00 ^* + u10 * a00 * u10 ^* + u20 * a00 * u20 ^* + u30 * a00 * u30 ^* = 
((U† × U) 0%nat 0%nat) * a00).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
assert (a10_extract: 
u01 * a10 * u00 ^* + u11 * a10 * u10 ^* + u21 * a10 * u20 ^* + u31 * a10 * u30 ^* = 
((U† × U) 0%nat 1%nat) * a10).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
assert (a20_extract: 
u02 * a20 * u00 ^* + u12 * a20 * u10 ^* + u22 * a20 * u20 ^* + u32 * a20 * u30 ^* = 
((U† × U) 0%nat 2%nat) * a20).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
assert (a30_extract: 
u03 * a30 * u00 ^* + u13 * a30 * u10 ^* + u23 * a30 * u20 ^* + u33 * a30 * u30 ^* = 
((U† × U) 0%nat 3%nat) * a30).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
assert (a01_extract: 
u00 * a01 * u01 ^* + u10 * a01 * u11 ^* + u20 * a01 * u21 ^* + u30 * a01 * u31 ^* = 
((U† × U) 1%nat 0%nat) * a01).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
assert (a11_extract: 
u01 * a11 * u01 ^* + u11 * a11 * u11 ^* + u21 * a11 * u21 ^* + u31 * a11 * u31 ^* = 
((U† × U) 1%nat 1%nat) * a11).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
assert (a21_extract: 
u02 * a21 * u01 ^* + u12 * a21 * u11 ^* + u22 * a21 * u21 ^* + u32 * a21 * u31 ^* = 
((U† × U) 1%nat 2%nat) * a21).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
assert (a31_extract: 
u03 * a31 * u01 ^* + u13 * a31 * u11 ^* + u23 * a31 * u21 ^* + u33 * a31 * u31 ^* = 
((U† × U) 1%nat 3%nat) * a31).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
assert (a02_extract: 
u00 * a02 * u02 ^* + u10 * a02 * u12 ^* + u20 * a02 * u22 ^* + u30 * a02 * u32 ^* = 
((U† × U) 2%nat 0%nat) * a02).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
assert (a12_extract: 
u01 * a12 * u02 ^* + u11 * a12 * u12 ^* + u21 * a12 * u22 ^* + u31 * a12 * u32 ^* = 
((U† × U) 2%nat 1%nat) * a12).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
assert (a22_extract: 
u02 * a22 * u02 ^* + u12 * a22 * u12 ^* + u22 * a22 * u22 ^* + u32 * a22 * u32 ^* = 
((U† × U) 2%nat 2%nat) * a22).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
assert (a32_extract: 
u03 * a32 * u02 ^* + u13 * a32 * u12 ^* + u23 * a32 * u22 ^* + u33 * a32 * u32 ^* = 
((U† × U) 2%nat 3%nat) * a32).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
assert (a03_extract: 
u00 * a03 * u03 ^* + u10 * a03 * u13 ^* + u20 * a03 * u23 ^* + u30 * a03 * u33 ^* = 
((U† × U) 3%nat 0%nat) * a03).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
assert (a13_extract: 
u01 * a13 * u03 ^* + u11 * a13 * u13 ^* + u21 * a13 * u23 ^* + u31 * a13 * u33 ^* = 
((U† × U) 3%nat 1%nat) * a13).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
assert (a23_extract: 
u02 * a23 * u03 ^* + u12 * a23 * u13 ^* + u22 * a23 * u23 ^* + u32 * a23 * u33 ^* = 
((U† × U) 3%nat 2%nat) * a23).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
assert (a33_extract: 
u03 * a33 * u03 ^* + u13 * a33 * u13 ^* + u23 * a33 * u23 ^* + u33 * a33 * u33 ^* = 
((U† × U) 3%nat 3%nat) * a33).
{
    unfold u00, u01, u02, u03, u10, u11, u12, u13, u20, u21, u22, u23, u30, u31, u32, u33.
    lca.
}
by_cell.
all: unfold partial_trace_2q_a, partial_trace_3q_c.
all: rewrite swapbc_decomp_l. 
2,4,6,8: assumption.
all: rewrite swapbc_decomp_r.
2,4,6,8: assumption.
all: rewrite kron42_explicit_decomp.
2,3,5,6,8,9,11,12: assumption.
all: simpl.
all: rewrite Mmult44_explicit_decomp.
2,3,5,6,8,9,11,12: assumption.
all: repeat rewrite <- Cmult_plus_distr_r.
all: rewrite <- Cmult_1_l.
all: apply Cmult_const_r.
all: rewrite Mmult44_explicit_decomp.
2,3,5,6,8,9,11,12: assumption.
all: fold a00 a01 a02 a03.
all: fold a10 a11 a12 a13.
all: fold a20 a21 a22 a23.
all: fold a30 a31 a32 a33.
all: repeat rewrite Madj_explicit_decomp.
all: fold u00 u01 u02 u03.
all: fold u10 u11 u12 u13.
all: fold u20 u21 u22 u23.
all: fold u30 u31 u32 u33.
all: repeat rewrite Cmult_plus_distr_r.
all: rewrite prod_redist.
all: rewrite a00_extract.
all: rewrite a10_extract.
all: rewrite a20_extract.
all: rewrite a30_extract.
all: rewrite a01_extract.
all: rewrite a11_extract.
all: rewrite a21_extract.
all: rewrite a31_extract.
all: rewrite a02_extract.
all: rewrite a12_extract.
all: rewrite a22_extract.
all: rewrite a32_extract.
all: rewrite a03_extract.
all: rewrite a13_extract.
all: rewrite a23_extract.
all: rewrite a33_extract.
all: rewrite Udag_U_I.
all: Csimpl.
all: unfold a00, a11, a22, a33.
all: rewrite <- trace_explicit_decomp_square4.
all: rewrite trace_kron_square2.
all: repeat rewrite trace_outer_vec2.
all: repeat rewrite qubit_prop_explicit.
1,4,7,10: apply Cmult_1_l.
1,3,5,7: apply c_qubit.
all: apply a_qubit.
Qed.
