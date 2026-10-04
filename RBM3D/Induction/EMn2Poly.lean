/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.ContractPt
import RBM3D.Induction.Step2Defs

/-!
# ST2-09 (ticket T2102): the martingale estimate `lem: EMn2_N`, first estimate `(eq:MG_conclusion)`

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`): `(eq:MG_conclusion)`
`3_5:427-432`, the split `(eq:S1+S2)` `3_5:801`, the contraction inequality `(eq_sym_loop_bound)`,
`(eq_sym_loop_bound2)` `3_5:754`, `3_5:758`, `(eq:pointwise_loop)` `3_5:812`, `(eq:reduce4to3)`
`3_5:816`, `(eq:reduce4_bdd3)` `3_5:823`.

The pin `STEMn2Poly` (`RBM3D/Induction/Step2Defs.lean:441`) is proved outright:
`stEMn2Poly_holds (d : ℕ) : STEMn2Poly d`.  The proof follows `3_5:800-825` with one change, which
makes the two inputs `(GijGEX)`, `(GiiGEX)` unnecessary: the 4-loop and the 3-loop of the
paper's proof are bounded by 2-loops by Cauchy-Schwarz on the blocks, deterministically, for every
Hermitian `H` and every `z` with `Im z > 0` (`E_a = W^{-d} P_a`, `G(σ)^* = G(-σ)`):

* `(𝓛^{(4)}_{(σ,-σ,σ,-σ),(c',b,c',b)})^{1/2} ≤ |𝓛^{(2)}_{(σ,-σ),(c',b)}|`
  (`‖A‖_HS ≤ tr A` for `A = X X^*`, `X = P_b G P_{c'}`; `emn2Poly_norm_loop4_alt_le`);
* `|𝓛^{(3)}_{(s,σ₂,-σ₂),(a,b,a)}| ≤ |𝓛^{(2)}_{(s,-s),(a,a)}|^{1/2} |𝓛^{(2)}_{(σ₂,-σ₂),(b,a)}|`
  (`|tr(Y^* B Y)| ≤ ‖B‖_HS ‖Y‖²_HS`, `B = P_a G(s) P_a`, `Y = P_a G(σ₂) P_b`;
  `emn2Poly_norm_loop3_le`).

Both 2-loops are of the pattern `(σ, -σ)` of `(eq:LW_assm)` (`STLWassm`), at the pairs `(c', b)`,
`(a, a)`, `(b, a)`.  So `STLWassm` and `STPsiClass` alone give `(eq:pointwise_loop)` and
`(eq:reduce4_bdd3)`; the premise `STInitialGT2` and the entry bounds are not used (paper-delta
candidate `T2102a`).  The other steps are those of the paper: the split of the `c`-sum by
`|c-b| ≷ |c-a|` and the contraction inequality `stContractPt_holds` (T2094, `ContractPt.lean:463`)
for `S₁`; for `S₂` the partner `(eq_sym_loop_bound2)` is the same inequality at the exchanged
labels, by the rotation of a 6-loop by 3 positions (`emn2Poly_loop6_rot`, `trace_mul_comm`)
followed by the flip of all charges (`emn2Poly_contractPt_partner`).

* §1-§3 Hilbert-Schmidt norm, the adjoint `G(σ)^* = G(-σ)`, block projections
  (ported from `RBM3D/Induction/ContractPt.lean:53-250`, where they are private);
* §4 the loops as traces of `P`-words; the rotation; the bounds `emn2Poly_norm_loop4_alt_le`,
  `emn2Poly_norm_loop3_le`;
* §5 lattice facts: the triangle inequality of `zdistInf`, the support and size of `S^{(B)}`;
* §6 the deterministic bound `emn2_ee_le` (for the cut `k = 0`; `k = 1` is the same with the two
  edges exchanged);
* §7 the profile comparison `(eq:Psi)`; §8 the pin `stEMn2Poly_holds`; §9 compiled instances at
  `d = 3`.
-/

set_option linter.style.longLine false

noncomputable section

open Matrix Finset Filter MeasureTheory

namespace RBM.Gauss.Sizes

open RBM RBM.Gauss RBM.Loop RBM.Path

/-! ## 1. Hilbert-Schmidt Cauchy-Schwarz -/

section Generic

variable {ι : Type*} [Fintype ι]

/-- `‖A‖_{HS}² = Σ_{ij} |A_{ij}|²`.  `RBM3D/Induction/ContractPt.lean:58`. -/
private def hs (A : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

private lemma hs_nonneg (A : Matrix ι ι ℂ) : 0 ≤ hs A := by
  unfold hs; positivity

/-- `tr(A A^*) = ‖A‖_HS²`.  `RBM3D/Induction/ContractPt.lean:64`. -/
private lemma trace_mul_conjTranspose_eq (A : Matrix ι ι ℂ) :
    (A * Aᴴ).trace = (hs A : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, hs]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj']

/-- `‖A^*‖_HS = ‖A‖_HS`. -/
private lemma hs_conjTranspose (A : Matrix ι ι ℂ) : hs Aᴴ = hs A := by
  unfold hs
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.conjTranspose_apply, norm_star]

/-- Cauchy-Schwarz over the pair of indices.  `RBM3D/Induction/ContractPt.lean:73`. -/
private lemma sum_pair_le (A : Matrix ι ι ℂ) (v : ι → ℝ) :
    ∑ i, ∑ j, ‖A i j‖ * (v i * v j) ≤ √(hs A) * ∑ i, v i ^ 2 := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (ι × ι))
    (fun p => ‖A p.1 p.2‖) (fun p => v p.1 * v p.2)
  simp only [Fintype.sum_prod_type] at h
  have h2 : ∑ i, ∑ j, (v i * v j) ^ 2 = (∑ i, v i ^ 2) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h2, Real.sqrt_sq (Finset.sum_nonneg fun i _ => sq_nonneg (v i))] at h
  exact h

/-- **The quadratic-form Cauchy-Schwarz bound** `|tr(Ψ A Ψ^*)| ≤ ‖A‖_HS ‖Ψ‖²_HS`.
`RBM3D/Induction/ContractPt.lean:87`. -/
private lemma norm_trace_mul_mul_conjTranspose_le (Ψ A : Matrix ι ι ℂ) :
    ‖(Ψ * A * Ψᴴ).trace‖ ≤ √(hs A) * hs Ψ := by
  have h1 : ‖(Ψ * A * Ψᴴ).trace‖ ≤
      ∑ x, ∑ i, ∑ j, ‖A i j‖ * (‖Ψ x i‖ * ‖Ψ x j‖) := by
    calc ‖(Ψ * A * Ψᴴ).trace‖
        = ‖∑ x, ∑ j, (∑ i, Ψ x i * A i j) * star (Ψ x j)‖ := by
          simp [Matrix.trace, Matrix.mul_apply]
      _ ≤ ∑ x, ‖∑ j, (∑ i, Ψ x i * A i j) * star (Ψ x j)‖ := norm_sum_le _ _
      _ ≤ ∑ x, ∑ j, ‖(∑ i, Ψ x i * A i j) * star (Ψ x j)‖ :=
          Finset.sum_le_sum fun x _ => norm_sum_le _ _
      _ ≤ ∑ x, ∑ j, ∑ i, ‖Ψ x i * A i j * star (Ψ x j)‖ := by
          refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul, norm_star]
          calc ‖∑ i, Ψ x i * A i j‖ * ‖Ψ x j‖ ≤ (∑ i, ‖Ψ x i * A i j‖) * ‖Ψ x j‖ :=
                mul_le_mul_of_nonneg_right (norm_sum_le _ _) (norm_nonneg _)
            _ = ∑ i, ‖Ψ x i * A i j‖ * ‖Ψ x j‖ := Finset.sum_mul _ _ _
            _ = _ := by simp
      _ = ∑ x, ∑ i, ∑ j, ‖A i j‖ * (‖Ψ x i‖ * ‖Ψ x j‖) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [norm_mul, norm_mul, norm_star]
          ring
  refine h1.trans ?_
  calc ∑ x, ∑ i, ∑ j, ‖A i j‖ * (‖Ψ x i‖ * ‖Ψ x j‖)
      ≤ ∑ x, √(hs A) * ∑ i, ‖Ψ x i‖ ^ 2 :=
        Finset.sum_le_sum fun x _ => sum_pair_le A (fun i => ‖Ψ x i‖)
    _ = √(hs A) * hs Ψ := by rw [← Finset.mul_sum]; rfl

end Generic

/-! ## 2. The resolvent: adjoint -/

section Resolvent

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `G(σ)^* = G(-σ)` for Hermitian `H`.  `RBM3D/Induction/ContractPt.lean:125`. -/
private lemma Gres_conjTranspose {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (z : ℂ) (σ : Bool) :
    (Gres H z σ)ᴴ = Gres H z (!σ) := by
  have hH' : Hᴴ = H := hH
  cases σ with
  | true =>
    simp only [Gres, ↓reduceIte, Bool.not_true, Bool.false_eq_true,
      ← Matrix.nonsing_inv_eq_ringInverse, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH',
      Complex.star_def]
  | false =>
    simp only [Gres, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      ← Matrix.nonsing_inv_eq_ringInverse, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH',
      Complex.star_def, Complex.conj_conj]

end Resolvent

/-! ## 3. The block projections `P_a = W^d E_a` -/

section Proj

variable (d L W : ℕ) [NeZero L]

/-- The block projection `P_a = W^d E_a`: the diagonal matrix of the indicator of the block `a`.
`RBM3D/Induction/ContractPt.lean:207`. -/
private def Pm (a : Zd d L) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  Matrix.diagonal fun x => if x.1 = a then 1 else 0

variable {d L W}

omit [NeZero L] in
private lemma Eblk_eq_smul_Pm (a : Zd d L) :
    Eblk d L W a = ((W : ℂ) ^ d)⁻¹ • Pm d L W a := by
  ext x y
  by_cases hxy : x = y
  · subst hxy
    by_cases hx : x.1 = a <;> simp [Eblk, Pm, hx]
  · simp [Eblk, Pm, hxy]

omit [NeZero L] in
private lemma Pm_conjTranspose (a : Zd d L) : (Pm d L W a)ᴴ = Pm d L W a := by
  refine (Matrix.isHermitian_diagonal_iff.mpr fun x => ?_).eq
  by_cases h : x.1 = a <;> simp [h, IsSelfAdjoint]

private lemma Pm_mul_self (a : Zd d L) : Pm d L W a * Pm d L W a = Pm d L W a := by
  simp only [Pm, Matrix.diagonal_mul_diagonal]
  congr 1
  ext x
  by_cases h : x.1 = a <;> simp [h]

private lemma Pm_mul_Pm_mul (a : Zd d L) (X : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    Pm d L W a * (Pm d L W a * X) = Pm d L W a * X := by
  rw [← Matrix.mul_assoc, Pm_mul_self]

private lemma trace_Pm_sandwich (a : Zd d L) (X : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    (Pm d L W a * X * Pm d L W a).trace = (X * Pm d L W a).trace := by
  rw [Matrix.trace_mul_comm, Pm_mul_Pm_mul, Matrix.trace_mul_comm]

end Proj

/-! ## 4. The loops as traces of `P`-words -/

section LoopTraces

variable {d L W : ℕ} [NeZero L] [NeZero W] (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ)

/-- The two-loop: `𝓛^{(2)}_{(s,-s),(x,y)} = W^{-2d} tr(G(s) P_x G(-s) P_y)`. -/
private lemma loop2_eq (s : Bool) (x y : Zd d L) :
    loopFine d L W H z ![s, !s] ![x, y] =
      (((W : ℂ) ^ d)⁻¹) ^ 2 *
        (Gres (blockMat d L W H) z s * Pm d L W x * Gres (blockMat d L W H) z (!s) *
          Pm d L W y).trace := by
  conv_lhs => simp [loopFine, loopM, List.ofFn_succ]
  simp only [Eblk_eq_smul_Pm, Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.trace_smul,
    smul_eq_mul, Matrix.mul_assoc]
  ring

/-- The alternating four-loop: `𝓛^{(4)}_{alt,(c',b,c',b)} = W^{-4d} tr(G P_{c'} Ḡ P_b G P_{c'} Ḡ P_b)`
(`(eq:L4loop)`, `3_5:780`). -/
private lemma loop4_eq (s0 : Bool) (b c' : Zd d L) :
    loopFine d L W H z ![s0, !s0, s0, !s0] ![c', b, c', b] =
      (((W : ℂ) ^ d)⁻¹) ^ 4 *
        (Gres (blockMat d L W H) z s0 * Pm d L W c' * Gres (blockMat d L W H) z (!s0) *
          Pm d L W b * (Gres (blockMat d L W H) z s0 * Pm d L W c' *
          Gres (blockMat d L W H) z (!s0) * Pm d L W b)).trace := by
  conv_lhs => simp [loopFine, loopM, List.ofFn_succ]
  simp only [Eblk_eq_smul_Pm, Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.trace_smul,
    smul_eq_mul, Matrix.mul_assoc]
  ring

/-- The three-loop: `𝓛^{(3)}_{(s,σ₂,-σ₂),(a,b,a)} = W^{-3d} tr(G(s) P_a G₂ P_b Ḡ₂ P_a)`. -/
private lemma loop3_eq (s s1 : Bool) (a b : Zd d L) :
    loopFine d L W H z ![s, s1, !s1] ![a, b, a] =
      (((W : ℂ) ^ d)⁻¹) ^ 3 *
        (Gres (blockMat d L W H) z s * Pm d L W a * Gres (blockMat d L W H) z s1 * Pm d L W b *
          Gres (blockMat d L W H) z (!s1) * Pm d L W a).trace := by
  conv_lhs => simp [loopFine, loopM, List.ofFn_succ]
  simp only [Eblk_eq_smul_Pm, Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.trace_smul,
    smul_eq_mul, Matrix.mul_assoc]
  ring

end LoopTraces

section LoopRotation

variable {d L W : ℕ} [NeZero L] [NeZero W] (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ)

/-- **Rotation of a 6-loop by three positions** (trace cyclicity): the 6-loop
`𝓛^{(6)}_{(σ⊗σ̄)^{(1)},(a,b,c',b,a,c)}` of the contraction inequality is, read from its fourth
factor, the loop of the pin with all charges flipped and the labels `(a,b,c',c)` replaced by
`(b,a,c,c')`.  This is the exchange of roles in `(eq_sym_loop_bound2)` (`3_5:758`). -/
theorem emn2Poly_loop6_rot (s0 s1 : Bool) (a b c c' : Zd d L) :
    loopFine d L W H z ![s0, s1, s0, !s0, !s1, !s0] ![a, b, c', b, a, c] =
      loopFine d L W H z ![!s0, !s1, !s0, s0, s1, s0] ![b, a, c, a, b, c'] := by
  conv_lhs => simp [loopFine, loopM, List.ofFn_succ]
  conv_rhs => simp [loopFine, loopM, List.ofFn_succ]
  generalize Gres (blockMat d L W H) z s0 * Eblk d L W a = X1
  generalize Gres (blockMat d L W H) z s1 * Eblk d L W b = X2
  generalize Gres (blockMat d L W H) z s0 * Eblk d L W c' = X3
  generalize Gres (blockMat d L W H) z (!s0) * Eblk d L W b = X4
  generalize Gres (blockMat d L W H) z (!s1) * Eblk d L W a = X5
  generalize Gres (blockMat d L W H) z (!s0) * Eblk d L W c = X6
  have e1 : X1 * (X2 * (X3 * (X4 * (X5 * X6)))) = (X1 * X2 * X3) * (X4 * X5 * X6) := by
    simp only [Matrix.mul_assoc]
  have e2 : X4 * (X5 * (X6 * (X1 * (X2 * X3)))) = (X4 * X5 * X6) * (X1 * X2 * X3) := by
    simp only [Matrix.mul_assoc]
  rw [e1, e2, Matrix.trace_mul_comm]

end LoopRotation

/-- From `a ≤ √a x` (`a ≥ 0`): `a ≤ x²`. -/
private lemma le_sq_of_le_sqrt_mul {a x : ℝ} (ha : 0 ≤ a) (h : a ≤ √a * x) :
    a ≤ x ^ 2 := by
  rcases ha.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · have hs' : 0 < √a := Real.sqrt_pos.2 hpos
    have h3 : √a ≤ x := by
      have : √a * √a ≤ √a * x := by
        rw [Real.mul_self_sqrt ha]; exact h
      exact le_of_mul_le_mul_left this hs'
    calc a = √a ^ 2 := (Real.sq_sqrt ha).symm
      _ ≤ x ^ 2 := by gcongr

section LoopBounds

variable {d L W : ℕ} [NeZero L] [NeZero W] (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ)

/-- **The alternating 4-loop is dominated by the square of the 2-loop** (`(eq:L4loop)`, `3_5:780`,
with `‖A‖_HS ≤ tr A` for `A = X X^*` positive semidefinite): for every Hermitian `H`,
`(𝓛^{(4)}_{(σ,-σ,σ,-σ),(c',b,c',b)})^{1/2} ≤ |𝓛^{(2)}_{(σ,-σ),(c',b)}|`. -/
theorem emn2Poly_norm_loop4_alt_le (hH : H.IsHermitian) (s0 : Bool) (b c' : Zd d L) :
    ‖loopFine d L W H z ![s0, !s0, s0, !s0] ![c', b, c', b]‖ ^ (1 / 2 : ℝ) ≤
      ‖loopFine d L W H z ![s0, !s0] ![c', b]‖ := by
  have hHb : (blockMat d L W H).IsHermitian := hH.submatrix _
  set G : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ := Gres (blockMat d L W H) z with hGdef
  have hG : ∀ s, (G s)ᴴ = G (!s) := Gres_conjTranspose hHb z
  set w : ℝ := ((W : ℕ) : ℝ) ^ d with hwdef
  have hWpos : (0 : ℝ) < ((W : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hw : 0 < w := pow_pos hWpos d
  have hκ : ‖((W : ℂ) ^ d)⁻¹‖ = w⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_natCast]
  -- `X = P_b G P_{c'}`, `A = X X^*`
  obtain ⟨X, hXdef⟩ : ∃ X : Matrix (Vtx d L W) (Vtx d L W) ℂ,
      X = Pm d L W b * G s0 * Pm d L W c' := ⟨_, rfl⟩
  have hXH : Xᴴ = Pm d L W c' * G (!s0) * Pm d L W b := by
    rw [hXdef]; simp only [Matrix.conjTranspose_mul, Pm_conjTranspose, hG, Matrix.mul_assoc]
  obtain ⟨A, hAdef⟩ : ∃ A : Matrix (Vtx d L W) (Vtx d L W) ℂ, A = X * Xᴴ := ⟨_, rfl⟩
  have hAH : Aᴴ = A := by
    rw [hAdef]; simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hAeq : A = Pm d L W b * (G s0 * Pm d L W c' * G (!s0)) * Pm d L W b := by
    rw [hAdef, hXH, hXdef]; simp only [Matrix.mul_assoc, Pm_mul_Pm_mul]
  -- `𝓛^{(2)} = W^{-2d} ‖X‖²_HS`
  have hL2 : loopFine d L W H z ![s0, !s0] ![c', b] =
      (((W : ℂ) ^ d)⁻¹) ^ 2 * (hs X : ℂ) := by
    rw [loop2_eq, ← trace_mul_conjTranspose_eq, ← hAdef, hAeq, trace_Pm_sandwich]
  -- `𝓛^{(4)} = W^{-4d} ‖A‖²_HS`
  have hAA : (A * A).trace =
      (G s0 * Pm d L W c' * G (!s0) * Pm d L W b *
        (G s0 * Pm d L W c' * G (!s0) * Pm d L W b)).trace := by
    have : A * A = Pm d L W b * (G s0 * Pm d L W c' * G (!s0) * Pm d L W b * G s0 *
        Pm d L W c' * G (!s0)) * Pm d L W b := by
      rw [hAeq]; simp only [Matrix.mul_assoc, Pm_mul_Pm_mul]
    rw [this, trace_Pm_sandwich]
    simp only [Matrix.mul_assoc]
  have hhsA : (hs A : ℂ) = (A * A).trace := by
    rw [← trace_mul_conjTranspose_eq, hAH]
  have hL4 : loopFine d L W H z ![s0, !s0, s0, !s0] ![c', b, c', b] =
      (((W : ℂ) ^ d)⁻¹) ^ 4 * (hs A : ℂ) := by
    rw [loop4_eq, hhsA, hAA]
  have hn2 : ‖loopFine d L W H z ![s0, !s0] ![c', b]‖ = w⁻¹ ^ 2 * hs X := by
    rw [hL2, norm_mul, norm_pow, hκ, Complex.norm_real, Real.norm_of_nonneg (hs_nonneg _)]
  have hn4 : ‖loopFine d L W H z ![s0, !s0, s0, !s0] ![c', b, c', b]‖ = w⁻¹ ^ 4 * hs A := by
    rw [hL4, norm_mul, norm_pow, hκ, Complex.norm_real, Real.norm_of_nonneg (hs_nonneg _)]
  -- `‖A‖²_HS ≤ √(‖A‖²_HS) ‖X‖²_HS`
  have hkey : (hs A : ℂ) = (Xᴴ * A * (Xᴴ)ᴴ).trace := by
    rw [hhsA, Matrix.conjTranspose_conjTranspose]
    calc (A * A).trace = (A * (X * Xᴴ)).trace := by rw [← hAdef]
      _ = ((A * X) * Xᴴ).trace := by rw [Matrix.mul_assoc]
      _ = (Xᴴ * (A * X)).trace := Matrix.trace_mul_comm _ _
      _ = (Xᴴ * A * X).trace := by rw [Matrix.mul_assoc]
  have h1 : hs A ≤ √(hs A) * hs X := by
    have h := norm_trace_mul_mul_conjTranspose_le (Xᴴ) A
    rw [← hkey, Complex.norm_real, Real.norm_of_nonneg (hs_nonneg _), hs_conjTranspose X] at h
    exact h
  have h2 : hs A ≤ hs X ^ 2 := le_sq_of_le_sqrt_mul (hs_nonneg A) h1
  have h4 : ‖loopFine d L W H z ![s0, !s0, s0, !s0] ![c', b, c', b]‖ ≤
      ‖loopFine d L W H z ![s0, !s0] ![c', b]‖ ^ 2 := by
    rw [hn4, hn2]
    calc w⁻¹ ^ 4 * hs A ≤ w⁻¹ ^ 4 * hs X ^ 2 := by gcongr
      _ = (w⁻¹ ^ 2 * hs X) ^ 2 := by ring
  rw [← Real.sqrt_eq_rpow]
  calc √‖loopFine d L W H z ![s0, !s0, s0, !s0] ![c', b, c', b]‖
      ≤ √(‖loopFine d L W H z ![s0, !s0] ![c', b]‖ ^ 2) := Real.sqrt_le_sqrt h4
    _ = ‖loopFine d L W H z ![s0, !s0] ![c', b]‖ := Real.sqrt_sq (norm_nonneg _)

/-- **The 3-loop is dominated by two 2-loops** (`(eq:reduce4_bdd3)`, `3_5:821-825`, by
`|tr(Y^* B Y)| ≤ ‖B‖_HS ‖Y‖²_HS` with `B = P_a G(s) P_a`, `Y = P_a G(σ₂) P_b`): for every
Hermitian `H`, `|𝓛^{(3)}_{(s,σ₂,-σ₂),(a,b,a)}| ≤ |𝓛^{(2)}_{(s,-s),(a,a)}|^{1/2}
|𝓛^{(2)}_{(σ₂,-σ₂),(b,a)}|`: the short leg `P_a G P_a` gives `Ψ(0)`, the two long legs
`P_a G P_b` give `Ψ²(|a-b|)`. -/
theorem emn2Poly_norm_loop3_le (hH : H.IsHermitian) (s s1 : Bool) (a b : Zd d L) :
    ‖loopFine d L W H z ![s, s1, !s1] ![a, b, a]‖ ≤
      ‖loopFine d L W H z ![s, !s] ![a, a]‖ ^ (1 / 2 : ℝ) *
        ‖loopFine d L W H z ![s1, !s1] ![b, a]‖ := by
  have hHb : (blockMat d L W H).IsHermitian := hH.submatrix _
  set G : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ := Gres (blockMat d L W H) z with hGdef
  have hG : ∀ s, (G s)ᴴ = G (!s) := Gres_conjTranspose hHb z
  set w : ℝ := ((W : ℕ) : ℝ) ^ d with hwdef
  have hWpos : (0 : ℝ) < ((W : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hw : 0 < w := pow_pos hWpos d
  have hκ : ‖((W : ℂ) ^ d)⁻¹‖ = w⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_natCast]
  -- `Y = P_a G(σ₂) P_b` (a long leg), `B = P_a G(s) P_a` (the short leg)
  obtain ⟨Y, hYdef⟩ : ∃ Y : Matrix (Vtx d L W) (Vtx d L W) ℂ,
      Y = Pm d L W a * G s1 * Pm d L W b := ⟨_, rfl⟩
  have hYH : Yᴴ = Pm d L W b * G (!s1) * Pm d L W a := by
    rw [hYdef]; simp only [Matrix.conjTranspose_mul, Pm_conjTranspose, hG, Matrix.mul_assoc]
  obtain ⟨B, hBdef⟩ : ∃ B : Matrix (Vtx d L W) (Vtx d L W) ℂ,
      B = Pm d L W a * G s * Pm d L W a := ⟨_, rfl⟩
  have hBH : Bᴴ = Pm d L W a * G (!s) * Pm d L W a := by
    rw [hBdef]; simp only [Matrix.conjTranspose_mul, Pm_conjTranspose, hG, Matrix.mul_assoc]
  -- the three loops
  have htr : (G s * Pm d L W a * G s1 * Pm d L W b * G (!s1) * Pm d L W a).trace =
      (Yᴴ * B * Y).trace := by
    have h1 : Yᴴ * B * Y = Pm d L W b * (G (!s1) * Pm d L W a * G s * Pm d L W a * G s1) *
        Pm d L W b := by
      rw [hYH, hBdef, hYdef]; simp only [Matrix.mul_assoc, Pm_mul_Pm_mul]
    rw [h1, trace_Pm_sandwich]
    calc (G s * Pm d L W a * G s1 * Pm d L W b * G (!s1) * Pm d L W a).trace
        = ((G s * Pm d L W a * G s1 * Pm d L W b) * (G (!s1) * Pm d L W a)).trace := by
          simp only [Matrix.mul_assoc]
      _ = ((G (!s1) * Pm d L W a) * (G s * Pm d L W a * G s1 * Pm d L W b)).trace :=
          Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  have hL3 : loopFine d L W H z ![s, s1, !s1] ![a, b, a] =
      (((W : ℂ) ^ d)⁻¹) ^ 3 * (Yᴴ * B * (Yᴴ)ᴴ).trace := by
    rw [loop3_eq, Matrix.conjTranspose_conjTranspose, htr]
  have hL2a : loopFine d L W H z ![s, !s] ![a, a] = (((W : ℂ) ^ d)⁻¹) ^ 2 * (hs B : ℂ) := by
    rw [loop2_eq, ← trace_mul_conjTranspose_eq, hBH]
    have h1 : B * (Pm d L W a * G (!s) * Pm d L W a) =
        Pm d L W a * (G s * Pm d L W a * G (!s)) * Pm d L W a := by
      rw [hBdef]; simp only [Matrix.mul_assoc, Pm_mul_Pm_mul]
    rw [h1, trace_Pm_sandwich]
  have hL2b : loopFine d L W H z ![s1, !s1] ![b, a] = (((W : ℂ) ^ d)⁻¹) ^ 2 * (hs Y : ℂ) := by
    rw [loop2_eq, ← trace_mul_conjTranspose_eq, hYH]
    have h1 : Y * (Pm d L W b * G (!s1) * Pm d L W a) =
        Pm d L W a * (G s1 * Pm d L W b * G (!s1)) * Pm d L W a := by
      rw [hYdef]; simp only [Matrix.mul_assoc, Pm_mul_Pm_mul]
    rw [h1, trace_Pm_sandwich]
  -- norms
  have hn2a : ‖loopFine d L W H z ![s, !s] ![a, a]‖ = w⁻¹ ^ 2 * hs B := by
    rw [hL2a, norm_mul, norm_pow, hκ, Complex.norm_real, Real.norm_of_nonneg (hs_nonneg _)]
  have hn2b : ‖loopFine d L W H z ![s1, !s1] ![b, a]‖ = w⁻¹ ^ 2 * hs Y := by
    rw [hL2b, norm_mul, norm_pow, hκ, Complex.norm_real, Real.norm_of_nonneg (hs_nonneg _)]
  have h3 : ‖loopFine d L W H z ![s, s1, !s1] ![a, b, a]‖ ≤
      w⁻¹ ^ 3 * (√(hs B) * hs Y) := by
    rw [hL3, norm_mul, norm_pow, hκ]
    have h := norm_trace_mul_mul_conjTranspose_le (Yᴴ) B
    rw [hs_conjTranspose Y] at h
    gcongr
  -- `hs B = w² ‖𝓛^{(2)}_{aa}‖`, `hs Y = w² ‖𝓛^{(2)}_{ba}‖`
  have hB' : hs B = w ^ 2 * ‖loopFine d L W H z ![s, !s] ![a, a]‖ := by
    rw [hn2a]; field_simp
  have hY' : hs Y = w ^ 2 * ‖loopFine d L W H z ![s1, !s1] ![b, a]‖ := by
    rw [hn2b]; field_simp
  have hsq : √(hs B) = w * √‖loopFine d L W H z ![s, !s] ![a, a]‖ := by
    rw [hB', Real.sqrt_mul (sq_nonneg w), Real.sqrt_sq hw.le]
  rw [← Real.sqrt_eq_rpow]
  calc ‖loopFine d L W H z ![s, s1, !s1] ![a, b, a]‖ ≤ w⁻¹ ^ 3 * (√(hs B) * hs Y) := h3
    _ = √‖loopFine d L W H z ![s, !s] ![a, a]‖ * ‖loopFine d L W H z ![s1, !s1] ![b, a]‖ := by
        rw [hsq, hY']
        field_simp

end LoopBounds

/-! ## 5. Lattice facts: `zdistInf` and the support and size of `S^{(B)}` -/

section Lattice

private lemma zdistInf_zero_eq (d L : ℕ) : zdistInf d L (0 : Zd d L) = 0 := by
  unfold zdistInf
  exact Nat.eq_zero_of_le_zero (Finset.sup_le fun i _ => by simp)

private lemma zdistInf_neg_eq (d L : ℕ) [NeZero L] (x : Zd d L) :
    zdistInf d L (-x) = zdistInf d L x := by
  unfold zdistInf
  exact Finset.sup_congr rfl fun i _ => by simp [zdist_neg]

private lemma zdistInf_add_le_add (d L : ℕ) [NeZero L] (x y : Zd d L) :
    zdistInf d L (x + y) ≤ zdistInf d L x + zdistInf d L y := by
  unfold zdistInf
  refine Finset.sup_le fun i _ => ?_
  exact (zdist_add_le L (x i) (y i)).trans (add_le_add
    (Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i))
    (Finset.le_sup (f := fun j => zdist L (y j)) (Finset.mem_univ i)))

/-- The triangle inequality `|x - w| ≤ |x - y| + |y - w|` for the periodic `L^∞` distance. -/
private lemma zdistInf_tri (d L : ℕ) [NeZero L] (x y w : Zd d L) :
    zdistInf d L (x - w) ≤ zdistInf d L (x - y) + zdistInf d L (y - w) := by
  have : x - w = (x - y) + (y - w) := by abel
  rw [this]; exact zdistInf_add_le_add d L _ _

private lemma zdistInf_sub_comm (d L : ℕ) [NeZero L] (x y : Zd d L) :
    zdistInf d L (x - y) = zdistInf d L (y - x) := by
  rw [← neg_sub, zdistInf_neg_eq]

/-- Every entry of `S^{(B)}` is at most `1` in absolute value (`L ≥ 3`: the row sums are `1`). -/
private lemma norm_SB_le_one (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (g : ℝ) (c c' : Zd d L) :
    ‖SB d L g c c'‖ ≤ 1 := by
  calc ‖SB d L g c c'‖ ≤ ∑ b, ‖SB d L g c b‖ :=
        Finset.single_le_sum (f := fun b => ‖SB d L g c b‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ c')
    _ = 1 := sum_norm_SB_row d L g hL c

/-- `S^{(B)}_{cc'} = 0` unless `|c - c'|_∞ ≤ 1` (the blocks are equal or nearest neighbours). -/
private lemma SB_eq_zero_of_far (d L : ℕ) [NeZero L] (g : ℝ) (c c' : Zd d L)
    (h : 1 < zdistInf d L (c - c')) : SB d L g c c' = 0 := by
  rw [SB_apply, sbKernel]
  have h0 : c - c' ≠ 0 := by
    intro h0; rw [h0, zdistInf_zero_eq] at h; omega
  have h1 : zdistD d L (c - c') ≠ 1 := by
    intro h1; have := zdistInf_le_zdistD d L (c - c'); omega
  simp [h0, h1]

end Lattice

/-! ## 6. The deterministic bound of `(𝓔⊗𝓔)^{M,(2;k)}` -/

section EEBound

variable {d L W : ℕ} [NeZero L] [NeZero W] (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ)

/-- **The partner `(eq_sym_loop_bound2)` of the contraction inequality** (`3_5:758`, "by symmetry"):
the pin `stContractPt_holds` at the exchanged labels `(b, a)` and the flipped charges
`(-σ₁, -σ₂)`, applied to the rotation by three positions of the 6-loop `emn2Poly_loop6_rot`.  The sum runs
over `c ∈ 𝒜` (the point of the loop that carries `P_c` in the pin's `Ψ_c`) and its neighbours `c'`;
`(𝓛^{(4)}_{(-σ₁,σ₁,-σ₁,σ₁),(c,a,c,a)})^{1/2} ≤ M` on `𝒜`. -/
theorem emn2Poly_contractPt_partner (hH : H.IsHermitian) (hz : 0 < z.im) (s0 s1 : Bool)
    (a b : Zd d L) (𝒜 : Finset (Zd d L)) (M : ℝ) (hM : 0 ≤ M)
    (h4 : ∀ c ∈ 𝒜, ‖loopFine d L W H z ![!s0, s0, !s0, s0] ![c, a, c, a]‖ ^ (1 / 2 : ℝ) ≤ M) :
    ∑ c ∈ 𝒜, ∑ c' ∈ Finset.univ.filter (fun c' : Zd d L => zdistInf d L (c' - c) ≤ 1),
        ‖loopFine d L W H z ![s0, s1, s0, !s0, !s1, !s0] ![a, b, c', b, a, c]‖ ≤
      3 ^ d / (((W : ℕ) : ℝ) ^ d * z.im) * M *
        max ‖loopFine d L W H z ![true, !s1, s1] ![b, a, b]‖
          ‖loopFine d L W H z ![false, !s1, s1] ![b, a, b]‖ := by
  have h := stContractPt_holds d L W H z hH hz ![!s0, !s1] b a 𝒜 M hM
    (by simpa using h4)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Bool.not_not] at h
  refine le_of_eq_of_le (Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_) h
  rw [emn2Poly_loop6_rot]

/-- **`(eq:reduce4_bdd3)`** (`3_5:821-825`) in terms of the control of the 2-loops: if every
2-loop of the pattern `(s,-s)` is at most `y² Ψ²(|x - x'|)` then
`|𝓛^{(3)}_{(s,σ₂,-σ₂),(a,b,a)}| ≤ y Ψ(0) · y² Ψ²(|b - a|)`: the short leg `P_a G P_a` gives
`y Ψ(0)`, the two long legs `y² Ψ²(|a-b|)`. -/
private lemma loop3_ctrl (hH : H.IsHermitian) {y : ℝ} (hy : 0 ≤ y) {Ψf : ℕ → ℝ}
    (hΨ : ∀ r, 0 ≤ Ψf r)
    (h2 : ∀ (s : Bool) (x x' : Zd d L), ‖loopFine d L W H z ![s, !s] ![x, x']‖ ≤
      y ^ 2 * Ψf (zdistInf d L (x - x')) ^ 2) (s s1 : Bool) (a b : Zd d L) :
    ‖loopFine d L W H z ![s, s1, !s1] ![a, b, a]‖ ≤
      y * Ψf 0 * (y ^ 2 * Ψf (zdistInf d L (b - a)) ^ 2) := by
  refine (emn2Poly_norm_loop3_le H z hH s s1 a b).trans ?_
  have h1 := h2 s a a
  rw [sub_self, zdistInf_zero_eq] at h1
  have h3 := h2 s1 b a
  have h4 : ‖loopFine d L W H z ![s, !s] ![a, a]‖ ^ (1 / 2 : ℝ) ≤ y * Ψf 0 := by
    rw [← Real.sqrt_eq_rpow]
    calc √‖loopFine d L W H z ![s, !s] ![a, a]‖ ≤ √((y * Ψf 0) ^ 2) :=
          Real.sqrt_le_sqrt (by rw [mul_pow]; exact h1)
      _ = y * Ψf 0 := Real.sqrt_sq (mul_nonneg hy (hΨ 0))
  exact mul_le_mul h4 h3 (norm_nonneg _) (mul_nonneg hy (hΨ 0))

/-- **The sum over `R₁ = {c : |c - a| < |c - b|}` of the 6-loops** (the part `𝒮₁` of
`(eq:S1+S2)`, `3_5:801`): the contraction inequality `stContractPt_holds` with
`𝒜 = {c' : ∃ c ∈ R₁, |c - c'| ≤ 1}` and `M = y² K² Ψ²(r)`. -/
private lemma part1_le (hH : H.IsHermitian) (hz : 0 < z.im) (σ : Fin 2 → Bool)
    (a b : Zd d L) {y K : ℝ} (hy : 0 ≤ y) {Ψf : ℕ → ℝ} (hΨ : ∀ r, 0 ≤ Ψf r)
    (hcmp : ∀ r s : ℕ, r ≤ 2 * s + 1 → Ψf s ≤ K * Ψf r)
    (h2 : ∀ (s : Bool) (x x' : Zd d L), ‖loopFine d L W H z ![s, !s] ![x, x']‖ ≤
      y ^ 2 * Ψf (zdistInf d L (x - x')) ^ 2) :
    ∑ c ∈ Finset.univ.filter (fun c : Zd d L => zdistInf d L (c - a) < zdistInf d L (c - b)),
        ∑ c' : Zd d L, (if zdistInf d L (c - c') ≤ 1 then
          ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
          else 0) ≤
      3 ^ d / (((W : ℕ) : ℝ) ^ d * z.im) * (y ^ 2 * K ^ 2 * Ψf (zdistInf d L (a - b)) ^ 2) *
        (y * Ψf 0 * (y ^ 2 * Ψf (zdistInf d L (a - b)) ^ 2)) := by
  set R1 : Finset (Zd d L) :=
    Finset.univ.filter (fun c : Zd d L => zdistInf d L (c - a) < zdistInf d L (c - b)) with hR1
  set 𝒜 : Finset (Zd d L) :=
    Finset.univ.filter (fun c' : Zd d L => ∃ c ∈ R1, zdistInf d L (c - c') ≤ 1) with h𝒜
  -- the contraction inequality for `𝒜`
  have hM0 : 0 ≤ y ^ 2 * K ^ 2 * Ψf (zdistInf d L (a - b)) ^ 2 := by positivity
  have hM : ∀ c' ∈ 𝒜, ‖loopFine d L W H z ![σ 0, !(σ 0), σ 0, !(σ 0)] ![c', b, c', b]‖ ^
      (1 / 2 : ℝ) ≤ y ^ 2 * K ^ 2 * Ψf (zdistInf d L (a - b)) ^ 2 := by
    intro c' hc'
    obtain ⟨c, hc, hn⟩ := (Finset.mem_filter.mp hc').2
    have hc1 : zdistInf d L (c - a) < zdistInf d L (c - b) := (Finset.mem_filter.mp hc).2
    have hrs : zdistInf d L (a - b) ≤ 2 * zdistInf d L (c' - b) + 1 := by
      have t1 := zdistInf_tri d L a c b
      have t2 := zdistInf_tri d L c c' b
      have t3 := zdistInf_sub_comm d L a c
      omega
    calc ‖loopFine d L W H z ![σ 0, !(σ 0), σ 0, !(σ 0)] ![c', b, c', b]‖ ^ (1 / 2 : ℝ)
        ≤ ‖loopFine d L W H z ![σ 0, !(σ 0)] ![c', b]‖ := emn2Poly_norm_loop4_alt_le H z hH (σ 0) b c'
      _ ≤ y ^ 2 * Ψf (zdistInf d L (c' - b)) ^ 2 := h2 (σ 0) c' b
      _ ≤ y ^ 2 * (K * Ψf (zdistInf d L (a - b))) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hΨ _) (hcmp _ _ hrs) 2) (sq_nonneg y)
      _ = y ^ 2 * K ^ 2 * Ψf (zdistInf d L (a - b)) ^ 2 := by ring
  have hpin := stContractPt_holds d L W H z hH hz σ a b 𝒜 _ hM0 hM
  -- the maximum of the two 3-loops
  have hmax : max ‖loopFine d L W H z ![true, σ 1, !(σ 1)] ![a, b, a]‖
      ‖loopFine d L W H z ![false, σ 1, !(σ 1)] ![a, b, a]‖ ≤
      y * Ψf 0 * (y ^ 2 * Ψf (zdistInf d L (a - b)) ^ 2) := by
    have e : zdistInf d L (b - a) = zdistInf d L (a - b) := zdistInf_sub_comm d L b a
    have h3 := loop3_ctrl H z hH hy hΨ h2
    refine max_le ?_ ?_
    · have := h3 true (σ 1) a b; rwa [e] at this
    · have := h3 false (σ 1) a b; rwa [e] at this
  have hK : 0 ≤ 3 ^ d / (((W : ℕ) : ℝ) ^ d * z.im) * (y ^ 2 * K ^ 2 * Ψf (zdistInf d L (a - b)) ^ 2) := by
    have : (0 : ℝ) < ((W : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
    positivity
  -- rearrange the sum over `R₁`, `c'`
  have hrearr : ∑ c ∈ R1, ∑ c' : Zd d L, (if zdistInf d L (c - c') ≤ 1 then
      ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖ else 0) ≤
      ∑ c' ∈ 𝒜, ∑ c ∈ Finset.univ.filter (fun c : Zd d L => zdistInf d L (c - c') ≤ 1),
        ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖ := by
    rw [Finset.sum_comm]
    have hz0 : ∀ c' ∉ 𝒜, ∑ c ∈ R1, (if zdistInf d L (c - c') ≤ 1 then
        ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
        else 0) = 0 := by
      intro c' hc'
      refine Finset.sum_eq_zero fun c hc => ?_
      have hn : ¬ zdistInf d L (c - c') ≤ 1 := fun hn =>
        hc' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, c, hc, hn⟩)
      simp only [hn, ↓reduceIte]
    calc ∑ c' : Zd d L, ∑ c ∈ R1, (if zdistInf d L (c - c') ≤ 1 then
          ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
          else 0)
        = ∑ c' ∈ 𝒜, ∑ c ∈ R1, (if zdistInf d L (c - c') ≤ 1 then
          ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
          else 0) := by
          symm
          exact Finset.sum_subset (Finset.filter_subset _ _) fun c' _ hc' => hz0 c' hc'
      _ ≤ _ := by
          refine Finset.sum_le_sum fun c' _ => ?_
          rw [← Finset.sum_filter]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _)
          intro c hc
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hc).2⟩
  calc _ ≤ _ := hrearr
    _ ≤ _ := hpin
    _ ≤ _ := mul_le_mul_of_nonneg_left hmax hK

/-- **The sum over `R₂ = {c : |c - b| ≤ |c - a|}` of the 6-loops** (the part `𝒮₂` of
`(eq:S1+S2)`): the partner `emn2Poly_contractPt_partner` with `𝒜 = R₂`, `M = y² K² Ψ²(r)`
(`|c - a| ≥ r/2`). -/
private lemma part2_le (hH : H.IsHermitian) (hz : 0 < z.im) (σ : Fin 2 → Bool)
    (a b : Zd d L) {y K : ℝ} (hy : 0 ≤ y) {Ψf : ℕ → ℝ} (hΨ : ∀ r, 0 ≤ Ψf r)
    (hcmp : ∀ r s : ℕ, r ≤ 2 * s + 1 → Ψf s ≤ K * Ψf r)
    (h2 : ∀ (s : Bool) (x x' : Zd d L), ‖loopFine d L W H z ![s, !s] ![x, x']‖ ≤
      y ^ 2 * Ψf (zdistInf d L (x - x')) ^ 2) :
    ∑ c ∈ Finset.univ.filter (fun c : Zd d L => ¬ (zdistInf d L (c - a) < zdistInf d L (c - b))),
        ∑ c' : Zd d L, (if zdistInf d L (c - c') ≤ 1 then
          ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
          else 0) ≤
      3 ^ d / (((W : ℕ) : ℝ) ^ d * z.im) * (y ^ 2 * K ^ 2 * Ψf (zdistInf d L (a - b)) ^ 2) *
        (y * Ψf 0 * (y ^ 2 * Ψf (zdistInf d L (a - b)) ^ 2)) := by
  set R2 : Finset (Zd d L) :=
    Finset.univ.filter (fun c : Zd d L => ¬ (zdistInf d L (c - a) < zdistInf d L (c - b))) with hR2
  have hM0 : 0 ≤ y ^ 2 * K ^ 2 * Ψf (zdistInf d L (a - b)) ^ 2 := by positivity
  have h4 : ∀ c ∈ R2, ‖loopFine d L W H z ![!(σ 0), σ 0, !(σ 0), σ 0] ![c, a, c, a]‖ ^
      (1 / 2 : ℝ) ≤ y ^ 2 * K ^ 2 * Ψf (zdistInf d L (a - b)) ^ 2 := by
    intro c hc
    have hc2 : zdistInf d L (c - b) ≤ zdistInf d L (c - a) := by
      have := (Finset.mem_filter.mp hc).2
      omega
    have hrs : zdistInf d L (a - b) ≤ 2 * zdistInf d L (c - a) + 1 := by
      have t1 := zdistInf_tri d L a c b
      have t3 := zdistInf_sub_comm d L a c
      omega
    have h5 := emn2Poly_norm_loop4_alt_le H z hH (!(σ 0)) a c
    have h6 := h2 (!(σ 0)) c a
    simp only [Bool.not_not] at h5 h6
    calc ‖loopFine d L W H z ![!(σ 0), σ 0, !(σ 0), σ 0] ![c, a, c, a]‖ ^ (1 / 2 : ℝ)
        ≤ ‖loopFine d L W H z ![!(σ 0), σ 0] ![c, a]‖ := h5
      _ ≤ y ^ 2 * Ψf (zdistInf d L (c - a)) ^ 2 := h6
      _ ≤ y ^ 2 * (K * Ψf (zdistInf d L (a - b))) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hΨ _) (hcmp _ _ hrs) 2) (sq_nonneg y)
      _ = y ^ 2 * K ^ 2 * Ψf (zdistInf d L (a - b)) ^ 2 := by ring
  have hpin := emn2Poly_contractPt_partner H z hH hz (σ 0) (σ 1) a b R2 _ hM0 h4
  have hmax : max ‖loopFine d L W H z ![true, !(σ 1), σ 1] ![b, a, b]‖
      ‖loopFine d L W H z ![false, !(σ 1), σ 1] ![b, a, b]‖ ≤
      y * Ψf 0 * (y ^ 2 * Ψf (zdistInf d L (a - b)) ^ 2) := by
    have h3 := loop3_ctrl H z hH hy hΨ h2
    refine max_le ?_ ?_
    · have := h3 true (!(σ 1)) b a; simpa only [Bool.not_not] using this
    · have := h3 false (!(σ 1)) b a; simpa only [Bool.not_not] using this
  have hK : 0 ≤ 3 ^ d / (((W : ℕ) : ℝ) ^ d * z.im) * (y ^ 2 * K ^ 2 * Ψf (zdistInf d L (a - b)) ^ 2) := by
    have : (0 : ℝ) < ((W : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
    positivity
  have hrew : ∀ c ∈ R2, ∑ c' : Zd d L, (if zdistInf d L (c - c') ≤ 1 then
      ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖ else 0) =
      ∑ c' ∈ Finset.univ.filter (fun c' : Zd d L => zdistInf d L (c' - c) ≤ 1),
        ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖ := by
    intro c _
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [zdistInf_sub_comm d L c c']
  calc _ = ∑ c ∈ R2, ∑ c' ∈ Finset.univ.filter (fun c' : Zd d L => zdistInf d L (c' - c) ≤ 1),
        ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖ :=
        Finset.sum_congr rfl hrew
    _ ≤ _ := hpin
    _ ≤ _ := mul_le_mul_of_nonneg_left hmax hK

/-- **`(eq:MG_conclusion)` at the matrix level** (`3_5:800-825`), cut `k = 0`: for every Hermitian
`H`, `z` with `Im z > 0`, signs `σ` and labels `a, b`, if every 2-loop of the pattern `(s,-s)` is at
most `y² Ψ²(|x - x'|)` and `Ψ(s) ≤ K Ψ(r)` for `r ≤ 2 s + 1` (`(eq:Psi)`), then
`|W^d Σ_{c,c'} S^{(B)}_{cc'} 𝓛^{(6)}_{(σ⊗σ̄)^{(1)},(a,b,c',b,a,c)}|
  ≤ 2 · 3^d η⁻¹ K² y⁵ Ψ(0) Ψ(|a-b|)⁴`, `η = Im z`.  The factor `y⁵ = N^{5τ'/2}` is the loss of
the stochastic domination, the factor `2 · 3^d K²` the constant. -/
private theorem emn2_ee_le (hL : 3 ≤ L) (g : ℝ) (hH : H.IsHermitian) (hz : 0 < z.im)
    (σ : Fin 2 → Bool) (a b : Zd d L) {y K : ℝ} (hy : 0 ≤ y) {Ψf : ℕ → ℝ} (hΨ : ∀ r, 0 ≤ Ψf r)
    (hcmp : ∀ r s : ℕ, r ≤ 2 * s + 1 → Ψf s ≤ K * Ψf r)
    (h2 : ∀ (s : Bool) (x x' : Zd d L), ‖loopFine d L W H z ![s, !s] ![x, x']‖ ≤
      y ^ 2 * Ψf (zdistInf d L (x - x')) ^ 2) :
    ‖(((W : ℕ) : ℂ) ^ d) * ∑ c : Zd d L, ∑ c' : Zd d L, SB d L g c c' *
        loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖ ≤
      2 * 3 ^ d / z.im * K ^ 2 * y ^ 5 * Ψf 0 * Ψf (zdistInf d L (a - b)) ^ 4 := by
  have hW : (0 : ℝ) < ((W : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hWd : (0 : ℝ) < ((W : ℕ) : ℝ) ^ d := pow_pos hW d
  -- each summand is at most the 6-loop, supported on `|c - c'| ≤ 1`
  have hterm : ∀ c c' : Zd d L,
      ‖SB d L g c c' * loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)]
          ![a, b, c', b, a, c]‖ ≤
        if zdistInf d L (c - c') ≤ 1 then
          ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
        else 0 := by
    intro c c'
    by_cases hn : zdistInf d L (c - c') ≤ 1
    · simp only [hn, ↓reduceIte, norm_mul]
      calc ‖SB d L g c c'‖ * ‖loopFine d L W H z
            ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
          ≤ 1 * ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)]
            ![a, b, c', b, a, c]‖ :=
            mul_le_mul_of_nonneg_right (norm_SB_le_one d L hL g c c') (norm_nonneg _)
        _ = _ := one_mul _
    · simp only [hn, ↓reduceIte]
      rw [SB_eq_zero_of_far d L g c c' (by omega), zero_mul, norm_zero]
  have h1 : ‖(((W : ℕ) : ℂ) ^ d) * ∑ c : Zd d L, ∑ c' : Zd d L, SB d L g c c' *
        loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖ ≤
      ((W : ℕ) : ℝ) ^ d * ∑ c : Zd d L, ∑ c' : Zd d L, (if zdistInf d L (c - c') ≤ 1 then
        ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
        else 0) := by
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ hWd.le
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun c' _ => hterm c c')
  -- split the `c`-sum by `|c - a| < |c - b|` (`(eq:S1+S2)`)
  have hsplit : ∑ c : Zd d L, ∑ c' : Zd d L, (if zdistInf d L (c - c') ≤ 1 then
        ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
        else 0) =
      ∑ c ∈ Finset.univ.filter (fun c : Zd d L => zdistInf d L (c - a) < zdistInf d L (c - b)),
        ∑ c' : Zd d L, (if zdistInf d L (c - c') ≤ 1 then
          ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
          else 0) +
      ∑ c ∈ Finset.univ.filter (fun c : Zd d L => ¬ (zdistInf d L (c - a) < zdistInf d L (c - b))),
        ∑ c' : Zd d L, (if zdistInf d L (c - c') ≤ 1 then
          ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
          else 0) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hp1 := part1_le H z hH hz σ a b hy hΨ hcmp h2
  have hp2 := part2_le H z hH hz σ a b hy hΨ hcmp h2
  calc _ ≤ _ := h1
    _ ≤ ((W : ℕ) : ℝ) ^ d * (3 ^ d / (((W : ℕ) : ℝ) ^ d * z.im) *
          (y ^ 2 * K ^ 2 * Ψf (zdistInf d L (a - b)) ^ 2) *
          (y * Ψf 0 * (y ^ 2 * Ψf (zdistInf d L (a - b)) ^ 2)) +
        3 ^ d / (((W : ℕ) : ℝ) ^ d * z.im) * (y ^ 2 * K ^ 2 * Ψf (zdistInf d L (a - b)) ^ 2) *
          (y * Ψf 0 * (y ^ 2 * Ψf (zdistInf d L (a - b)) ^ 2))) := by
        rw [hsplit]
        exact mul_le_mul_of_nonneg_left (add_le_add hp1 hp2) hWd.le
    _ = _ := by
        field_simp
        ring

end EEBound

/-! ## 7. The profile comparison `(eq:Psi)` -/

section Profile

/-- **`Ψ_t(s) ≲ Ψ_t(r)` for `r ≤ 2 s + 1`** (`(eq:Psi)`, `3_5:391`): for `s ≥ r` monotonicity; for
`1 ≤ s < r ≤ 2 s + 1` the ratio condition with `r/s ≤ 3`; for `s = 0` (so `r ≤ 1`) the window
`Ψ(0) ≍ Ψ(r)`, `r ≤ 1`.  The constant `max (C₁ 3^{C₂}) c⁻¹` depends on the class only. -/
private lemma psi_cmp {Ψf : ℕ → ℝ} {C₁ C₂ c : ℝ} (hC₁ : 1 < C₁) (hC₂ : 1 < C₂) (hc : 0 < c)
    (hpos : ∀ r, 0 < Ψf r) (hmono : ∀ r r' : ℕ, r ≤ r' → Ψf r' ≤ Ψf r)
    (hratio : ∀ r₁ r₂ : ℕ, 1 ≤ r₁ → r₁ ≤ r₂ → Ψf r₁ / Ψf r₂ ≤ C₁ * ((r₂ : ℝ) / r₁) ^ C₂)
    (hwin : ∀ r : ℕ, r ≤ 1 → c * Ψf 0 ≤ Ψf r) (r s : ℕ) (hrs : r ≤ 2 * s + 1) :
    Ψf s ≤ max (C₁ * 3 ^ C₂) c⁻¹ * Ψf r := by
  have hK1 : 1 ≤ C₁ * (3 : ℝ) ^ C₂ := by
    have : (1 : ℝ) ≤ 3 ^ C₂ := Real.one_le_rpow (by norm_num) (by linarith)
    nlinarith
  have hΨr := hpos r
  rcases le_or_gt r s with h | h
  · calc Ψf s ≤ Ψf r := hmono r s h
      _ = 1 * Ψf r := (one_mul _).symm
      _ ≤ max (C₁ * 3 ^ C₂) c⁻¹ * Ψf r :=
          mul_le_mul_of_nonneg_right (hK1.trans (le_max_left _ _)) hΨr.le
  · rcases Nat.eq_zero_or_pos s with hs0 | hs
    · subst hs0
      have hr1 : r ≤ 1 := by omega
      have h1 := hwin r hr1
      calc Ψf 0 = c⁻¹ * (c * Ψf 0) := by field_simp
        _ ≤ c⁻¹ * Ψf r := by gcongr
        _ ≤ max (C₁ * 3 ^ C₂) c⁻¹ * Ψf r :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hΨr.le
    · have hratio' := hratio s r hs h.le
      have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
      have hr3 : (r : ℝ) / s ≤ 3 := by
        rw [div_le_iff₀ (by linarith)]
        have : (r : ℝ) ≤ 2 * s + 1 := by exact_mod_cast hrs
        linarith
      have h3 : ((r : ℝ) / s) ^ C₂ ≤ (3 : ℝ) ^ C₂ :=
        Real.rpow_le_rpow (by positivity) hr3 (by linarith)
      have h4 : Ψf s / Ψf r ≤ C₁ * 3 ^ C₂ :=
        hratio'.trans (mul_le_mul_of_nonneg_left h3 (by linarith))
      calc Ψf s = (Ψf s / Ψf r) * Ψf r := by field_simp
        _ ≤ (C₁ * 3 ^ C₂) * Ψf r := mul_le_mul_of_nonneg_right h4 hΨr.le
        _ ≤ max (C₁ * 3 ^ C₂) c⁻¹ * Ψf r :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hΨr.le

end Profile

/-! ## 8. The pin `STEMn2Poly` -/

section Pin

/-- A failure event eventually contained in the failure event of another domination, over a
different parameter type (`StochDomAt.of_subset` needs the same parameter type). -/
private theorem stochDomAt_of_subset' {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {size : ℕ → ℕ} {U U₁ : ℕ → Type*} {ξ ζ : ∀ l, U l → Ω → ℝ} {ξ₁ ζ₁ : ∀ l, U₁ l → Ω → ℝ}
    (h : StochDomAt P size ξ₁ ζ₁)
    (hsub : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop,
      badSetAt size ξ ζ τ l ⊆ badSetAt size ξ₁ ζ₁ τ' l) : StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hs⟩ := hsub τ hτ
  filter_upwards [hs, h τ' hτ' D hD] with l h1 h2
  exact (measure_mono h1).trans h2

variable {d : ℕ} (sz : Sizes d)

/-- `(𝓔⊗𝓔)^{M,(2;0)}` unfolded: `W^d Σ_{c,c'} S^{(B)}_{cc'} 𝓛^{(6)}` of the fine matrix. -/
private lemma STEEkM_zero_eq (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STEEkM sz n E u H 0 σ a = (((sz.W n : ℕ) : ℂ) ^ d) *
      ∑ c : Zd d (sz.L n), ∑ c' : Zd d (sz.L n), SB d (sz.L n) (sz.lam n) c c' *
        loopFine d (sz.L n) (sz.W n) H (zt E u)
          ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a 0, a 1, c', a 1, a 0, c] := by
  simp [STEEkM, STLM]

/-- The cut `k = 1` is the cut `k = 0` with the two edges exchanged: `(σ₁,σ₂), (a₁,a₂)` become
`(σ₂,σ₁), (a₂,a₁)` (`def:CALE`, `3_5:169-190`; `3_5:670-672`: "without loss of generality"). -/
private lemma STEEkM_one_eq (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STEEkM sz n E u H 1 σ a = STEEkM sz n E u H 0 ![σ 1, σ 0] ![a 1, a 0] := by
  simp [STEEkM, STLM]

/-- **`lem: EMn2_N`, first estimate `(eq:MG_conclusion)`** (`3_5:427-432`, proof `3_5:800-825`),
**proved outright**: for every `d`, under `STFlow`, `0 ≤ t ≤ lemT z`, the class `(eq:Psi)` of `Ψ`,
`(initialGT2)` and `(eq:LW_assm)`, each cut `k ∈ {1,2}` satisfies
`(𝓔⊗𝓔)^{M,(2;k)}_{t,σ,a,a} ≺ η_t^{-1} Ψ_t(0) Ψ_t⁴(|a-b|)`.

The proof is deterministic on the good event of `(eq:LW_assm)` at the exponent `τ/5`: with
`y = N^{τ/10}` every 2-loop of the pattern `(s,-s)` is at most `y² Ψ²(|x - x'|)` (the only
stochastic input), and `emn2_ee_le` bounds the quadratic variation by
`2 · 3^d η⁻¹ K² y⁵ Ψ(0) Ψ(|a-b|)⁴` (`y⁵ = N^{τ/2}`, so the loss is `N^{τ/2} · 2 · 3^d K² ≤ N^τ` for
large `N`).  `STInitialGT2`, `(GijGEX)` and `(GiiGEX)` are not used (paper-delta candidate
`T2102a`). -/
theorem stEMn2Poly_holds (d : ℕ) : STEMn2Poly d := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ Ψ hΨ hI hA
  obtain ⟨hΨ1, hΨmono, hΨwin, C₁, C₂, hC₁, hC₂, hratio⟩ := hΨ
  obtain ⟨c, hc, hwin⟩ := hΨwin 1
  have hsizeT : Tendsto (fun n => ((sz.size n : ℕ) : ℝ)) atTop atTop := hflow.1.2.2.1
  -- `η_t > 0`
  have hη : ∀ n, 0 < etaT (STflowE z n) (t n) := by
    intro n
    have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (sz.one_le_size n)
    have hzim : 0 < (z n).im := lt_of_lt_of_le (Real.rpow_pos_of_pos hN _) (hflow.2 n).2.1
    exact etaT_pos (abs_lemE_lt_two hzim) ((htT n).trans_lt (lemT_lt_one hzim))
  set K : ℝ := max (C₁ * 3 ^ C₂) c⁻¹ with hK
  have hK0 : 0 ≤ K := by
    have : (0 : ℝ) ≤ C₁ * 3 ^ C₂ := by positivity
    exact this.trans (le_max_left _ _)
  refine stochDomAt_of_subset' hA ?_
  intro τ hτ
  refine ⟨τ / 5, by positivity, ?_⟩
  have hev : ∀ᶠ n in atTop, (∀ r : ℕ, r ≤ 1 → c * Ψ n 0 ≤ Ψ n r) ∧
      2 * 3 ^ d * K ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    refine (hwin.mono fun n hn => hn.2).and ?_
    exact ((tendsto_rpow_atTop (by positivity : 0 < τ / 2)).comp hsizeT).eventually_ge_atTop _
  filter_upwards [hev] with n hn
  intro ω hω
  obtain ⟨u, hu⟩ := hω
  by_contra hno
  have hgood : ∀ u' : {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)),
      ‖Lloop sz n (STflowE z n) (t n) u'.1.1 u'.2 ω‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 5) * (Ψ n (zdistInf d (sz.L n) (u'.2 0 - u'.2 1))) ^ 2 :=
    fun u' => not_lt.mp fun h => hno ⟨u', h⟩
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (sz.one_le_size n)
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set y : ℝ := N ^ (τ / 10) with hy
  have hy0 : 0 ≤ y := Real.rpow_nonneg hNpos.le _
  have hy2 : y ^ 2 = N ^ (τ / 5) := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    congr 1; push_cast; ring
  have hy5 : y ^ 5 = N ^ (τ / 2) := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    congr 1; push_cast; ring
  have hNτ : N ^ τ = N ^ (τ / 2) * N ^ (τ / 2) := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  have hΨ0 : ∀ r : ℕ, 0 ≤ Ψ n r := fun r => (hΨ1 n r).1.le
  have hcmp : ∀ r s : ℕ, r ≤ 2 * s + 1 → Ψ n s ≤ K * Ψ n r :=
    psi_cmp hC₁ hC₂ hc (fun r => (hΨ1 n r).1) (hΨmono n) (hratio n) hn.1
  have hL3 : 3 ≤ sz.L n := sz.three_le_L n
  have hH : (sz.seqHflow n (t n) ω).IsHermitian := sz.seqHflow_isHermitian n (t n) ω
  have hz' : 0 < (zt (STflowE z n) (t n)).im := by
    rw [← etaT_eq_zt_im]; exact hη n
  have h2 : ∀ (s : Bool) (x x' : Zd d (sz.L n)),
      ‖loopFine d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω) (zt (STflowE z n) (t n))
          ![s, !s] ![x, x']‖ ≤ y ^ 2 * Ψ n (zdistInf d (sz.L n) (x - x')) ^ 2 := by
    intro s x x'
    have hne : (![s, !s] : Fin 2 → Bool) 0 ≠ (![s, !s] : Fin 2 → Bool) 1 := by
      cases s <;> simp
    rw [hy2]
    exact hgood (⟨![s, !s], hne⟩, ![x, x'])
  -- the cut `k = 0`
  have key : ∀ (σ' : Fin 2 → Bool) (a' : Fin 2 → Zd d (sz.L n)),
      ‖STEEkM sz n (STflowE z n) (t n) (sz.seqHflow n (t n) ω) 0 σ' a'‖ ≤
        2 * 3 ^ d / etaT (STflowE z n) (t n) * K ^ 2 * y ^ 5 * Ψ n 0 *
          Ψ n (zdistInf d (sz.L n) (a' 0 - a' 1)) ^ 4 := by
    intro σ' a'
    rw [STEEkM_zero_eq]
    have := emn2_ee_le (L := sz.L n) (W := sz.W n) (sz.seqHflow n (t n) ω)
      (zt (STflowE z n) (t n)) hL3 (sz.lam n) hH hz' σ' (a' 0) (a' 1) hy0 hΨ0 hcmp h2
    rwa [← etaT_eq_zt_im] at this
  -- the final comparison `2 · 3^d K² y⁵ ≤ N^τ`
  have hfin : ∀ r : ℕ, 2 * 3 ^ d / etaT (STflowE z n) (t n) * K ^ 2 * y ^ 5 * Ψ n 0 *
      Ψ n r ^ 4 ≤ N ^ τ * (etaT (STflowE z n) (t n))⁻¹ * Ψ n 0 * Ψ n r ^ 4 := by
    intro r
    have hηpos := hη n
    have e1 : 2 * 3 ^ d / etaT (STflowE z n) (t n) * K ^ 2 * y ^ 5 * Ψ n 0 * Ψ n r ^ 4 =
        ((2 * 3 ^ d * K ^ 2) * y ^ 5) * ((etaT (STflowE z n) (t n))⁻¹ * Ψ n 0 * Ψ n r ^ 4) := by
      field_simp
    have e2 : N ^ τ * (etaT (STflowE z n) (t n))⁻¹ * Ψ n 0 * Ψ n r ^ 4 =
        (N ^ (τ / 2) * N ^ (τ / 2)) * ((etaT (STflowE z n) (t n))⁻¹ * Ψ n 0 * Ψ n r ^ 4) := by
      rw [hNτ]; ring
    rw [e1, e2]
    have h5 : (2 * 3 ^ d * K ^ 2) * y ^ 5 ≤ N ^ (τ / 2) * N ^ (τ / 2) := by
      rw [hy5]
      exact mul_le_mul_of_nonneg_right hn.2 (Real.rpow_nonneg hNpos.le _)
    refine mul_le_mul_of_nonneg_right h5 ?_
    have := hΨ0 0
    have := hΨ0 r
    positivity
  obtain ⟨k, σ, a⟩ := u
  have hb : ‖STEEk sz n (STflowE z n) (t n) k σ a ω‖ ≤
      N ^ τ * (etaT (STflowE z n) (t n))⁻¹ * Ψ n 0 *
        Ψ n (zdistInf d (sz.L n) (a 0 - a 1)) ^ 4 := by
    fin_cases k
    · exact (key σ a).trans (hfin _)
    · have h1 : STEEk sz n (STflowE z n) (t n) 1 σ a ω =
          STEEkM sz n (STflowE z n) (t n) (sz.seqHflow n (t n) ω) 0 ![σ 1, σ 0] ![a 1, a 0] :=
        STEEkM_one_eq sz n (STflowE z n) (t n) (sz.seqHflow n (t n) ω) σ a
      have h3 := key ![σ 1, σ 0] ![a 1, a 0]
      have e : zdistInf d (sz.L n) (a 1 - a 0) = zdistInf d (sz.L n) (a 0 - a 1) :=
        zdistInf_sub_comm d (sz.L n) _ _
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e] at h3
      change ‖STEEk sz n (STflowE z n) (t n) 1 σ a ω‖ ≤ _
      rw [h1]
      exact h3.trans (hfin _)
  exact absurd hu (not_lt.mpr (by simpa [mul_assoc] using hb))

end Pin

end RBM.Gauss.Sizes

/-! ## 9. Compiled nonempty instances at `d = 3`

**The endpoint theorem** `stEMn2Poly_holds 3` at the merged size sequence `sz0`
(`RBM.Gauss.SizesInst.sz0`: `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `ilambda_n = (2(n+1))^{-6}`),
`κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `z_n = 1/2 + i N_n^{-4/5}` (`flow_z0`), `t ≡ 1/16 ≤ lemT z_n`,
`ε₀ = 1/20` and the profile `Ψ_n(r) = W_n^{-1}` of the class `(eq:Psi)` (`Ψ0_class`).  Every
deterministic hypothesis is discharged; what stays a hypothesis is `STInitialGT2` and `STLWassm`
(Step 1 / ST-6 chain, other gates' pins; the limit check of the preflight, report (a)).

**The deterministic core** `emn2_ee_le` at `d = 3`, `L = 3`, `W = 2` (`N = 216`, `W^d = 8` sites per
block, `L^d = 27` blocks), the Hermitian matrix `H_{ij} = (i)_0 + (j)_0` (not block diagonal, not a
multiple of the identity), `z = 1/2 + i/4`, `σ = (+,-)`, `a = 0`, `b = (1,1,1)`; the control is the
deterministic envelope `|𝓛^{(2)}| ≤ η⁻²` (`norm_loopM_le`), i.e. `y = η⁻¹`, `Ψ ≡ 1`, `K = 1`. -/

namespace RBM.Gauss.EMn2PolyInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst
  RBM.Gauss.Step2DefsInst RBM.Path Filter

/-- **`stEMn2Poly_holds` at `d = 3`** (`(eq:MG_conclusion)`): the conclusion at the data above. -/
example (hI : STInitialGT2 sz0 (STflowE z0) tInst (1 / 20) (fun n => Ψ0 n 0))
    (hA : STLWassm sz0 (STflowE z0) tInst Ψ0) :
    Prec sz0 (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖STEEk sz0 n (STflowE z0 n) (tInst n) p.1 p.2.1 p.2.2 ω‖)
      (fun n p _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * Ψ0 n 0 *
        (Ψ0 n (zdistInf 3 (sz0.L n) (p.2.2 0 - p.2.2 1))) ^ 4) :=
  stEMn2Poly_holds 3 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 tInst (fun n => by simp only [tInst]; norm_num) sixteenth_le_lemT (1 / 20)
    (by norm_num) Ψ0 Ψ0_class hI hA

/-- The same data, read through the merged instance `inst_EMn2Poly`: the pin `STEMn2Poly 3` is
now a theorem, so the instance has no hypothesis on the pin. -/
example (hI : STInitialGT2 sz0 (STflowE z0) tInst (1 / 20) (fun n => Ψ0 n 0))
    (hA : STLWassm sz0 (STflowE z0) tInst Ψ0) :
    Prec sz0 (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖STEEk sz0 n (STflowE z0 n) (tInst n) p.1 p.2.1 p.2.2 ω‖)
      (fun n p _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * Ψ0 n 0 *
        (Ψ0 n (zdistInf 3 (sz0.L n) (p.2.2 0 - p.2.2 1))) ^ 4) :=
  inst_EMn2Poly (stEMn2Poly_holds 3) hI hA

/-- The instance matrix `H_{ij} = (i)_0 + (j)_0` on `Idx 3 3 2`. -/
private noncomputable def emH : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ :=
  Matrix.of fun i j => (((i 0).val + (j 0).val : ℕ) : ℂ)

private theorem emH_herm : emH.IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, emH, Matrix.of_apply]
  rw [add_comm (j 0).val, star_natCast]

private def emZ : ℂ := ⟨1 / 2, 1 / 4⟩

private theorem emZ_im : 0 < emZ.im := by
  change (0 : ℝ) < 1 / 4
  norm_num

private def emB : Zd 3 3 := fun _ => 1

/-- The instance matrix has `N = 216` sites. -/
example : Fintype.card (Idx 3 3 2) = 216 := by
  rw [RBM.Gauss.card_Idx]; norm_num

/-- **`emn2_ee_le` at the instance**: every hypothesis is discharged (the 2-loops by the envelope
`‖𝓛^{(2)}‖ ≤ η⁻²`, `η = Im z = 1/4`; the profile `Ψ ≡ 1`, `K = 1`), the conclusion is the bound
`2 · 3^3 η⁻¹ · (η⁻¹)^5` for the quadratic-variation loop of the cut `k = 0`. -/
example :
    ‖(((2 : ℕ) : ℂ) ^ 3) * ∑ c : Zd 3 3, ∑ c' : Zd 3 3, SB 3 3 ((1 : ℝ) / 8) c c' *
        loopFine 3 3 2 emH emZ ![true, false, true, !true, !false, !true]
          ![0, emB, c', emB, 0, c]‖ ≤
      2 * 3 ^ 3 / emZ.im * 1 ^ 2 * (emZ.im⁻¹) ^ 5 * 1 * 1 ^ 4 := by
  have hη : (0 : ℝ) < emZ.im := emZ_im
  have hb : (blockMat 3 3 2 emH).IsHermitian := emH_herm.submatrix _
  have h := emn2_ee_le (L := 3) (W := 2) emH emZ le_rfl ((1 : ℝ) / 8) emH_herm emZ_im
    ![true, false] 0 emB (y := emZ.im⁻¹) (K := 1) (Ψf := fun _ => 1) (by positivity)
    (fun _ => zero_le_one) (fun _ _ _ => by simp) (fun s x x' => by
      have := norm_loopM_le (d := 3) (L := 3) (W := 2) (n := 1)
        hb (z := emZ) hη (by rw [abs_of_pos hη])
        ![s, !s] ![x, x']
      simpa [loopFine] using this)
  simpa using h

end RBM.Gauss.EMn2PolyInst
