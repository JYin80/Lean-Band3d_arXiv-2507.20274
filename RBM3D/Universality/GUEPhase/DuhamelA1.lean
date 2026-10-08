/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.GUEPhase.Drift
import RBM3D.Path.StepDecomp
import RBM3D.Induction.Split
import RBM3D.Induction.LoopC2N
import RBM3D.Induction.ConArgDet

/-!
# The loop Duhamel tail of the GUE phase, part I, first half (`d ≥ 3`)

Ticket T2345 (UN-36).  Port of RBM2D `Universality/GUEPhase/DuhamelA.lean`, sections 1-4
(lines 1-1040, RBM2D commit `9e0f275`; cited `DuhA:<line>`).  The unit-GUE variance of a linear
functional, the Ward bound of the quadratic variation (7.38)/(7.43), the conditional variance of
the linear part of one step, and crude and shift bounds on `loopMax`.

## Main results (namespace `RBM.Univ.GUEPhase`)

* `Duhamel_vGue_le`: `vGue A ≤ 8 ‖A‖_F²`.
* `DuhamelLoopCut`, `Duhamel_frobSq_loopCut_le`: the cut block `R_k` of the `k`-th edge and the Ward
  bound `‖R_k‖_F² ≤ |Im z|⁻² L^{(2n)}`.
* `Duhamel_vGue_gradMat_le`: `max(vGue(∇Φ), vGue(-i ∇Φ)) ≤ 8 n² |Im z|⁻² L^{(2n)}`,
  `Φ M = 𝓛(blockMat M, z, I)`, `n = |I|`.
* `Duhamel_loopMax_le_crude`: `L^{(m)} ≤ (L W)^d |Im z|^{-m}`.
* `Duhamel_loopMax_shift_le`: the Lipschitz bound of `loopMax` in the spectral parameter.
* `Duhamel_contDiffAt_loop` (public here, private in the source): the loop observable
  `M ↦ 𝓛(blockMat M, z, I)` is `C²` at every Hermitian point.

## Renaming (as T2330, T2343)

`d : Sizes` is `sz : Sizes d`, `Idx L W` is `Idx d L W`, `Z2 L` is `Zd d L`,
`BlockIndex L W` is `Vtx d L W`, `Coord L W` is `CoordF d L W`, `Gsig M z σ` is `Gres M z σ`,
`gloop L W (blockMat M)` is `loopL d L W (blockMat d L W M)`, `RBM.Ind.loopMax L W` is
`RBM.Ind.loopMax d L W`, `Eblk L W` is `Eblk d L W`, `splitEquiv L W` is `splitEquiv d L W`.
The helpers `Gsig_true/false/conjTranspose`, `hasDerivAt_line`, `hasDerivAt_lineInverse` and
`coordinateMatrix_apply` are re-derived below (`Duhamel_Gres_*`, `Duhamel_hasDerivAt_*`,
`Duhamel_coordinateMatrix_apply`); `green_sub_green(_conj')`, `isUnit_sub_smul_of_isHermitian`,
`OneStep_isHermitian_add_realSmul`, `Eblk_isHermitian`, `norm_Eblk_le_inv_W_sq`,
`norm_gloop_le_crude`, `norm_matrix_trace_le_card_mul`, `card_BlockIndex` are the merged ones.

## `d`-dependent lines (CLAUDE.md §5.2)

`card (Vtx d L W) = (L W)^d` (`Duhamel_loopMax_le_crude`, `Duhamel_loopMax_shift_le`);
`‖E_a‖ ≤ (W^d)⁻¹ ≤ 1` (`Duhamel_norm_Eblk_le_one`, the crude bound); the coordinate type is
`CoordF d L W` (the coordinates of `Sizes.seqXmat`), not the block coordinate `Gauss.Coord`.  The
constants `8`, `4`, `m²` contain no `d`, `W`, `L`; `S_GUE = 1/N` of (7.43) does not occur in the
statements (`vGue` is the unit-GUE variance; the factor `1/N` is applied by the consumers).  No
statement uses `3 ≤ d`.

Compiled nonempty instances: namespace `RBM.Univ.GUEPhase.DuhamelA1Inst` (last section).  Every
unpinned helper is `private` with the source prefix `Duhamel_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.LinearForm RBM.Path
  RBM.Loop
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-! ### 1. The unit-GUE variance of a linear functional is bounded by the Frobenius norm -/

section VGue

variable {d : ℕ} (sz : Sizes d)

/-- Entrywise definition of `coordinateMatrix` (`rfl`; no merged public twin). -/
private theorem Duhamel_coordinateMatrix_apply {L W : ℕ} [NeZero L] [NeZero W]
    (c : CoordF d L W) (k l : Idx d L W) :
    coordinateMatrix d L W c k l = Xentry d L W (Pi.single c (1 : ℝ)) k l := rfl

/-- The coordinate matrix of the slice is the coordinate matrix of the coordinate. -/
private theorem Duhamel_seqXmat_single (n : ℕ) (c : CoordF d (sz.L n) (sz.W n)) :
    Sizes.seqXmat sz n (Pi.single (⟨n, c⟩ : Sizes.SeqCoord sz) 1)
      = coordinateMatrix d (sz.L n) (sz.W n) c := by
  have hs : Sizes.slice sz n (Pi.single (⟨n, c⟩ : Sizes.SeqCoord sz) 1)
      = Pi.single c 1 := by
    funext c'
    change (Pi.single (⟨n, c⟩ : Sizes.SeqCoord sz) (1 : ℝ) : Sizes.SeqCoord sz → ℝ) ⟨n, c'⟩
      = (Pi.single c (1 : ℝ) : CoordF d (sz.L n) (sz.W n) → ℝ) c'
    by_cases h : c' = c
    · subst h; simp
    · have h' : (⟨n, c'⟩ : Sizes.SeqCoord sz) ≠ ⟨n, c⟩ := fun he =>
        h (eq_of_heq (Sigma.mk.inj he).2)
      rw [Pi.single_eq_of_ne h', Pi.single_eq_of_ne h]
  unfold Sizes.seqXmat
  rw [hs]
  rfl

private theorem Duhamel_cm_lt {L W : ℕ} [NeZero L] [NeZero W] {i j : Idx d L W}
    (h : idxKey d L W i < idxKey d L W j) (b : Bool) :
    coordinateMatrix d L W (i, j, b) =
      Matrix.single i j (if b then (1 : ℂ) else Complex.I) +
        Matrix.single j i (if b then (1 : ℂ) else -Complex.I) := by
  have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
  ext k l
  simp only [Duhamel_coordinateMatrix_apply, Xentry, Matrix.add_apply, Matrix.single_apply,
    Pi.single_apply, Prod.mk.injEq]
  cases b <;> split_ifs <;> (try push_cast) <;>
    (try simp only [zero_add, add_zero, mul_zero, mul_one, sub_zero, zero_sub]) <;> grind

private theorem Duhamel_cm_diag_true {L W : ℕ} [NeZero L] [NeZero W] (i : Idx d L W) :
    coordinateMatrix d L W (i, i, true) = Matrix.single i i (1 : ℂ) := by
  ext k l
  simp only [Duhamel_coordinateMatrix_apply, Xentry, Matrix.single_apply, Pi.single_apply, Prod.mk.injEq]
  split_ifs <;> (try push_cast) <;>
    (try simp only [zero_add, add_zero, mul_zero, mul_one, sub_zero, zero_sub]) <;> grind

private theorem Duhamel_cm_diag_false {L W : ℕ} [NeZero L] [NeZero W] (i : Idx d L W) :
    coordinateMatrix d L W (i, i, false) = 0 := by
  ext k l
  simp only [Duhamel_coordinateMatrix_apply, Xentry, Matrix.zero_apply, Pi.single_apply, Prod.mk.injEq]
  split_ifs <;> (try push_cast) <;>
    (try simp only [zero_add, add_zero, mul_zero, mul_one, sub_zero, zero_sub]) <;> grind

private theorem Duhamel_cm_gt {L W : ℕ} [NeZero L] [NeZero W] {i j : Idx d L W}
    (h : idxKey d L W j < idxKey d L W i) (b : Bool) :
    coordinateMatrix d L W (i, j, b) = 0 := by
  have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
  ext k l
  simp only [Duhamel_coordinateMatrix_apply, Xentry, Matrix.zero_apply, Pi.single_apply, Prod.mk.injEq]
  cases b <;> split_ifs <;> (try push_cast) <;>
    (try simp only [zero_add, add_zero, mul_zero, mul_one, sub_zero, zero_sub]) <;> grind

/-- The squared coefficient of one coordinate in `linTr n A ∘ seqXmat d n`. -/
private theorem Duhamel_lin_coord_sq_le (n : ℕ)
    (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (c : CoordF d (sz.L n) (sz.W n)) :
    (linTr n A (coordinateMatrix d (sz.L n) (sz.W n) c)) ^ 2
      ≤ 2 * (‖A c.1 c.2.1‖ ^ 2 + ‖A c.2.1 c.1‖ ^ 2) := by
  obtain ⟨i, j, b⟩ := c
  simp only
  have hnn : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
    intro x y _ _; nlinarith [sq_nonneg (x - y)]
  rcases idxKey_lt_or_eq_or_lt d (sz.L n) (sz.W n) i j with h | h | h
  · rw [Duhamel_cm_lt h]
    have hx : ‖(if b then (1 : ℂ) else Complex.I)‖ = 1 := by split_ifs <;> simp
    have hy : ‖(if b then (1 : ℂ) else -Complex.I)‖ = 1 := by split_ifs <;> simp
    have htr : Matrix.trace (A * (Matrix.single i j (if b then (1 : ℂ) else Complex.I) +
        Matrix.single j i (if b then (1 : ℂ) else -Complex.I)))
        = A j i * (if b then (1 : ℂ) else Complex.I) + A i j * (if b then (1 : ℂ) else -Complex.I) := by
      rw [Matrix.mul_add, Matrix.trace_add, Matrix.trace_mul_single, Matrix.trace_mul_single]
      simp [mul_comm]
    have hlin : |linTr n A (Matrix.single i j (if b then (1 : ℂ) else Complex.I) +
        Matrix.single j i (if b then (1 : ℂ) else -Complex.I))| ≤ ‖A j i‖ + ‖A i j‖ := by
      unfold linTr
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [htr]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, hx, hy, mul_one, mul_one]
    calc (linTr n A (Matrix.single i j (if b then (1 : ℂ) else Complex.I) +
        Matrix.single j i (if b then (1 : ℂ) else -Complex.I))) ^ 2
        = |linTr n A (Matrix.single i j (if b then (1 : ℂ) else Complex.I) +
        Matrix.single j i (if b then (1 : ℂ) else -Complex.I))| ^ 2 := (sq_abs _).symm
      _ ≤ (‖A j i‖ + ‖A i j‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hlin 2
      _ ≤ 2 * (‖A j i‖ ^ 2 + ‖A i j‖ ^ 2) := hnn _ _ (norm_nonneg _) (norm_nonneg _)
      _ = 2 * (‖A i j‖ ^ 2 + ‖A j i‖ ^ 2) := by ring
  · subst h
    cases b
    · rw [Duhamel_cm_diag_false]
      have h0 : linTr n A (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) = 0 := by
        simp [linTr]
      rw [h0]
      nlinarith [sq_nonneg ‖A i i‖]
    · rw [Duhamel_cm_diag_true]
      have hlin : |linTr n A (Matrix.single i i (1 : ℂ))| ≤ ‖A i i‖ := by
        unfold linTr
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [Matrix.trace_mul_single]
        simp
      calc (linTr n A (Matrix.single i i (1 : ℂ))) ^ 2
          = |linTr n A (Matrix.single i i (1 : ℂ))| ^ 2 := (sq_abs _).symm
        _ ≤ ‖A i i‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hlin 2
        _ ≤ 2 * (‖A i i‖ ^ 2 + ‖A i i‖ ^ 2) := by nlinarith [sq_nonneg ‖A i i‖]
  · rw [Duhamel_cm_gt h]
    have h0 : linTr n A (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) = 0 := by
      simp [linTr]
    rw [h0]
    nlinarith [sq_nonneg ‖A i j‖, sq_nonneg ‖A j i‖]

/-- `vGue` as the sum over the coordinates of the squared coefficient times the variance. -/
private theorem Duhamel_vGue_eq_sum (n : ℕ)
    (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    (vGue sz n A : ℝ) = ∑ c : CoordF d (sz.L n) (sz.W n),
      (linTr n A (coordinateMatrix d (sz.L n) (sz.W n) c)) ^ 2
        * (gueUnitVar sz ⟨n, c⟩ : ℝ) := by
  classical
  unfold vGue linVar coordFinset
  push_cast [NNReal.coe_mk]
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Function.Embedding.sigmaMk_apply, Duhamel_seqXmat_single]

/-- **`vGue A ≤ 8 ‖A‖_F²`**:
the unit-GUE variance of the linear functional `y ↦ Re tr (A · seqXmat d n y)` is at most
`8 ∑_{ij} |A_{ij}|²`. -/
theorem Duhamel_vGue_le (n : ℕ)
    (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    (vGue sz n A : ℝ) ≤ 8 * ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  classical
  have hvar : ∀ c : Sizes.SeqCoord sz, (gueUnitVar sz c : ℝ) ≤ 1 := by
    intro c; unfold gueUnitVar; split_ifs <;> norm_num
  rw [Duhamel_vGue_eq_sum]
  have hterm : ∀ c : CoordF d (sz.L n) (sz.W n),
      (linTr n A (coordinateMatrix d (sz.L n) (sz.W n) c)) ^ 2 * (gueUnitVar sz ⟨n, c⟩ : ℝ)
        ≤ 2 * (‖A c.1 c.2.1‖ ^ 2 + ‖A c.2.1 c.1‖ ^ 2) := by
    intro c
    calc (linTr n A (coordinateMatrix d (sz.L n) (sz.W n) c)) ^ 2 * (gueUnitVar sz ⟨n, c⟩ : ℝ)
        ≤ (linTr n A (coordinateMatrix d (sz.L n) (sz.W n) c)) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (hvar _) (sq_nonneg _)
      _ ≤ 2 * (‖A c.1 c.2.1‖ ^ 2 + ‖A c.2.1 c.1‖ ^ 2) := by
          rw [mul_one]; exact Duhamel_lin_coord_sq_le sz n A c
  refine (Finset.sum_le_sum fun c _ => hterm c).trans (le_of_eq ?_)
  have hsplit : ∑ c : CoordF d (sz.L n) (sz.W n), 2 * (‖A c.1 c.2.1‖ ^ 2 + ‖A c.2.1 c.1‖ ^ 2)
      = ∑ i : Idx d (sz.L n) (sz.W n), ∑ j : Idx d (sz.L n) (sz.W n),
          (4 * ‖A i j‖ ^ 2 + 4 * ‖A j i‖ ^ 2) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.sum_bool]
    ring
  rw [hsplit]
  have hswap : ∑ i : Idx d (sz.L n) (sz.W n), ∑ j : Idx d (sz.L n) (sz.W n), ‖A j i‖ ^ 2
      = ∑ i : Idx d (sz.L n) (sz.W n), ∑ j : Idx d (sz.L n) (sz.W n), ‖A i j‖ ^ 2 :=
    Finset.sum_comm
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hswap]
  ring

end VGue


/-! ### 1b. Re-derived algebra (private twins of `Gsig_true/false/conjTranspose`,
`hasDerivAt_line`, `hasDerivAt_lineInverse`; DuhA:`Hierarchy/Loops.lean:51-68`,
`Gauss/Envelope.lean:144-151`) -/

section Aux

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem Duhamel_Gres_true (H : Matrix ι ι ℂ) (z : ℂ) : Gres H z true = green H z := by
  simp only [Gres, green, ↓reduceIte, Matrix.nonsing_inv_eq_ringInverse]

private theorem Duhamel_Gres_false (H : Matrix ι ι ℂ) (z : ℂ) :
    Gres H z false = green H ((starRingEnd ℂ) z) := by
  simp only [Gres, green, Bool.false_eq_true, ↓reduceIte, Matrix.nonsing_inv_eq_ringInverse]

private theorem Duhamel_Gres_conjTranspose {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (z : ℂ)
    (σ : Bool) : (Gres H z σ)ᴴ = Gres H z (!σ) := by
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

/-- The affine line `s ↦ M + s • A` has derivative `A` (`OneStep_hasDerivAt_line`, private there). -/
private theorem Duhamel_hasDerivAt_line (M A : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => M + (s : ℂ) • A) A t := by
  have h : HasDerivAt (fun s : ℝ => (s : ℂ) • A) A t := by
    simpa using (hasDerivAt_id t).smul_const A
  simpa using h.const_add M

/-- Along the line `t ↦ M + t • A`, the inverse has derivative `-R A R`
(`OUHessian_hasDerivAt_lineInverse`, private there). -/
private theorem Duhamel_hasDerivAt_lineInverse {M A : Matrix ι ι ℂ}
    (hU : ∀ t : ℝ, IsUnit (M + (t : ℂ) • A)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Ring.inverse (M + (s : ℂ) • A))
      (-(Ring.inverse (M + (t : ℂ) • A) * A * Ring.inverse (M + (t : ℂ) • A))) t := by
  set u : (Matrix ι ι ℂ)ˣ := (hU t).unit
  have hus : (u : Matrix ι ι ℂ) = M + (t : ℂ) • A := IsUnit.unit_spec _
  have hinv : ((u⁻¹ : (Matrix ι ι ℂ)ˣ) : Matrix ι ι ℂ)
      = Ring.inverse (M + (t : ℂ) • A) := by
    rw [← hus, Ring.inverse_unit]
  have hF : HasFDerivAt (Ring.inverse (M₀ := Matrix ι ι ℂ))
      (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix ι ι ℂ) ↑u⁻¹) ↑u⁻¹)
      (M + (t : ℂ) • A) := by
    rw [← hus]; exact hasFDerivAt_ringInverse u
  have hcomp := hF.comp_hasDerivAt t (Duhamel_hasDerivAt_line M A t)
  simpa [Function.comp_def, ContinuousLinearMap.mulLeftRight_apply, hinv] using hcomp

/-- `getD` at an in-range index (core twin of Mathlib's `List.getD_eq_getElem`, whose module
`Mathlib.Data.List.GetD` is not in the import closure). -/
private theorem Duhamel_getD_eq {α : Type*} (l : List α) (a : α) {q : ℕ} (hq : q < l.length) :
    l.getD q a = l[q] := by
  simp [List.getD_eq_getElem?_getD, hq]

end Aux

/-! ### 2. The Ward bound of the quadratic variation ((7.43) with `S_GUE = 1/N`) -/

section Ward

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The word `∏_{p ∈ l} G_{p.1} E_{p.2}` of a list of `(sign, label)` pairs. -/
private def Duhamel_wd (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (l : List (Bool × Zd d L)) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  l.foldr (fun p X => Gres M z p.1 * Eblk d L W p.2 * X) 1

private theorem Duhamel_wd_cons (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (p : Bool × Zd d L) (l : List (Bool × Zd d L)) :
    Duhamel_wd M z (p :: l) = Gres M z p.1 * Eblk d L W p.2 * Duhamel_wd M z l := rfl

private theorem Duhamel_wd_append (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (l₁ l₂ : List (Bool × Zd d L)) :
    Duhamel_wd M z (l₁ ++ l₂) = Duhamel_wd M z l₁ * Duhamel_wd M z l₂ := by
  have Duhamel_wd_nil (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) :
      Duhamel_wd M z ([] : List (Bool × Zd d L)) = 1 := rfl
  induction l₁ with
  | nil => simp [Duhamel_wd_nil]
  | cons p l ih => simp [Duhamel_wd_cons, ih, Matrix.mul_assoc]

private theorem Duhamel_gloopProd_eq (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (I : LoopIdx (Zd d L)) : gloopProd d L W M z I = Duhamel_wd M z (I.σ.zip I.a) := rfl

private theorem Duhamel_loopL_eq (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (I : LoopIdx (Zd d L)) :
    loopL d L W M z I = Matrix.trace (Duhamel_wd M z (I.σ.zip I.a)) := rfl

private theorem Duhamel_Eblk_conjTranspose (b : Zd d L) : (Eblk d L W b)ᴴ = Eblk d L W b :=
  Eblk_isHermitian b

/-- A list of `(sign, label)` pairs read as a loop index. -/
private def Duhamel_ofPairs (l : List (Bool × Zd d L)) : LoopIdx (Zd d L) :=
  ⟨l.map Prod.fst, l.map Prod.snd⟩

private theorem Duhamel_ofPairs_zip (l : List (Bool × Zd d L)) :
    (Duhamel_ofPairs l).σ.zip (Duhamel_ofPairs l).a = l := by
  change (l.map Prod.fst).zip (l.map Prod.snd) = l
  rw [List.zip_map']
  simp

/-- Reverse a chain and flip its charges. -/
private def Duhamel_rflip (t : Bool) : List (Bool × Zd d L) → Zd d L → List (Bool × Zd d L)
  | [], c => [(t, c)]
  | p :: l, c => Duhamel_rflip t l p.2 ++ [(!p.1, c)]

private theorem Duhamel_rflip_length (t : Bool) (l : List (Bool × Zd d L)) (c : Zd d L) :
    (Duhamel_rflip t l c).length = l.length + 1 := by
  induction l generalizing c with
  | nil => simp [Duhamel_rflip]
  | cons p l ih => simp [Duhamel_rflip, ih]

/-- `G(t) · (∏ G E)ᴴ · E_c` is the word of `rflip t l c`, for Hermitian `M`. -/
private theorem Duhamel_wd_rflip {M : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hM : M.IsHermitian) (z : ℂ) (t : Bool) (l : List (Bool × Zd d L)) (c : Zd d L) :
    Gres M z t * (Duhamel_wd M z l)ᴴ * Eblk d L W c = Duhamel_wd M z (Duhamel_rflip t l c) := by
  have Duhamel_wd_nil (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) :
      Duhamel_wd M z ([] : List (Bool × Zd d L)) = 1 := rfl
  induction l generalizing c with
  | nil => simp [Duhamel_rflip, Duhamel_wd_nil, Duhamel_wd_cons]
  | cons p l ih =>
    rw [Duhamel_rflip, Duhamel_wd_append, ← ih p.2, Duhamel_wd_cons, Duhamel_wd_cons,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Duhamel_Eblk_conjTranspose,
      Duhamel_Gres_conjTranspose hM]
    simp [Matrix.mul_assoc, Duhamel_wd_nil]

/-- The two Ward products `G Gᴴ` and `Gᴴ G` are both `(2iη)⁻¹ (G(z) - G(z̄))`. -/
private theorem Duhamel_Gsig_mul_conj {M : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hM : M.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (s : Bool) :
    Gres M z s * (Gres M z s)ᴴ
        = (2 * Complex.I * (z.im : ℂ))⁻¹ • (green M z - green M ((starRingEnd ℂ) z)) ∧
      (Gres M z s)ᴴ * Gres M z s
        = (2 * Complex.I * (z.im : ℂ))⁻¹ • (green M z - green M ((starRingEnd ℂ) z)) := by
  have hu : IsUnit (M - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) :=
    isUnit_sub_smul_of_isHermitian hM hz
  have hu' : IsUnit (M - ((starRingEnd ℂ) z) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) :=
    isUnit_sub_smul_of_isHermitian hM (by simpa using hz)
  have hc : (2 * Complex.I * (z.im : ℂ)) ≠ 0 := by
    have : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hz
    exact mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) this
  have hzc : z - (starRingEnd ℂ) z = 2 * Complex.I * (z.im : ℂ) := by
    rw [Complex.sub_conj]; push_cast; ring
  have h1 : green M z * green M ((starRingEnd ℂ) z)
      = (2 * Complex.I * (z.im : ℂ))⁻¹ • (green M z - green M ((starRingEnd ℂ) z)) := by
    rw [green_sub_green hu hu', hzc, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have h2 : green M ((starRingEnd ℂ) z) * green M z
      = (2 * Complex.I * (z.im : ℂ))⁻¹ • (green M z - green M ((starRingEnd ℂ) z)) := by
    rw [green_sub_green_conj' hu hu', smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [Duhamel_Gres_conjTranspose hM]
  cases s
  · simp only [Bool.not_false, Duhamel_Gres_true, Duhamel_Gres_false]
    exact ⟨h2, h1⟩
  · simp only [Bool.not_true, Duhamel_Gres_true, Duhamel_Gres_false]
    exact ⟨h1, h2⟩

/-- A glued trace `tr(E P G_x Pᴴ E G_y)` is a `2m`-loop. -/
private theorem Duhamel_trace_glue_eq {M : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hM : M.IsHermitian) (z : ℂ) (rest : List (Bool × Zd d L)) (a : Zd d L) (x y : Bool) :
    Matrix.trace (Eblk d L W a * Duhamel_wd M z rest * Gres M z x
        * (Duhamel_wd M z rest)ᴴ * Eblk d L W a * Gres M z y)
      = loopL d L W M z (Duhamel_ofPairs ((y, a) :: rest ++ Duhamel_rflip x rest a)) := by
  rw [Duhamel_loopL_eq, Duhamel_ofPairs_zip, Duhamel_wd_append, Duhamel_wd_cons,
    ← Duhamel_wd_rflip hM z x rest a]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

private theorem Duhamel_norm_glue_le {M : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hM : M.IsHermitian) (z : ℂ) (rest : List (Bool × Zd d L)) (a : Zd d L) (x y : Bool)
    {m : ℕ} (hm : rest.length + 1 = m) :
    ‖Matrix.trace (Eblk d L W a * Duhamel_wd M z rest * Gres M z x
        * (Duhamel_wd M z rest)ᴴ * Eblk d L W a * Gres M z y)‖ ≤ RBM.Ind.loopMax d L W M z (2 * m) := by
  rw [Duhamel_trace_glue_eq hM]
  refine RBM.Ind.norm_gloop_le_loopMax _ ?_ ?_
  · simp [Duhamel_ofPairs, Duhamel_rflip_length]; omega
  · simp [Duhamel_ofPairs, Duhamel_rflip_length]; omega

/-- **The cut block `R_k` of the `k`-th edge** (`k` counted from `0`):
`R_k = G(σ_k) E_{a_k} · (∏_{i > k} ∏_{i < k} G(σ_i) E_{a_i}) · G(σ_k)`. -/
def DuhamelLoopCut (d L W : ℕ) [NeZero L] (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (I : LoopIdx (Zd d L)) (k : ℕ) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  Gres M z (I.σ.getD k true) * Eblk d L W (I.a.getD k 0) *
    gloopProd d L W M z ⟨I.σ.drop (k + 1) ++ I.σ.take k, I.a.drop (k + 1) ++ I.a.take k⟩ *
    Gres M z (I.σ.getD k true)

/-- **Ward, for one cut block**: `‖R_k‖_F² ≤ |Im z|⁻² L^{(2n)}`. -/
theorem Duhamel_frobSq_loopCut_le {M : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hM : M.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) {I : LoopIdx (Zd d L)} (hI : I.WF) {k : ℕ}
    (hk : k < I.length) :
    ∑ p, ∑ q, ‖DuhamelLoopCut d L W M z I k p q‖ ^ 2
      ≤ (|z.im|⁻¹) ^ 2 * RBM.Ind.loopMax d L W M z (2 * I.length) := by
  set s := I.σ.getD k true with hs
  set a := I.a.getD k 0 with ha
  set σ' := I.σ.drop (k + 1) ++ I.σ.take k with hσ'
  set a' := I.a.drop (k + 1) ++ I.a.take k with ha'
  have hσlen : I.σ.length = I.a.length := hI
  have hlen' : σ'.length = a'.length := by
    simp only [hσ', ha', List.length_append, List.length_drop, List.length_take, hσlen]
  set rest : List (Bool × Zd d L) := σ'.zip a' with hrest
  set P := Duhamel_wd M z rest with hP
  set G := Gres M z s with hG
  set Dl := green M z - green M ((starRingEnd ℂ) z) with hDl
  set c := (2 * Complex.I * (z.im : ℂ))⁻¹ with hcdef
  have hlen : rest.length + 1 = I.length := by
    have hk' : k < I.a.length := hk
    have : rest.length = σ'.length := by
      rw [hrest, List.length_zip, hlen', min_self]
    rw [this]
    simp only [hσ', List.length_append, List.length_drop, List.length_take, hσlen]
    change _ = I.a.length
    omega
  have hR : DuhamelLoopCut d L W M z I k = G * Eblk d L W a * P * G := by
    rw [DuhamelLoopCut]
    rfl
  obtain ⟨hGG, hGG'⟩ := Duhamel_Gsig_mul_conj hM hz s
  -- the Frobenius norm is the trace of `R Rᴴ`
  have hfrob : ∀ R : Matrix (Vtx d L W) (Vtx d L W) ℂ,
      ((∑ p, ∑ q, ‖R p q‖ ^ 2 : ℝ) : ℂ) = Matrix.trace (R * Rᴴ) := by
    intro R
    rw [Matrix.trace]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.conjTranspose_apply, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  have htr : Matrix.trace (DuhamelLoopCut d L W M z I k * (DuhamelLoopCut d L W M z I k)ᴴ)
      = c * c * Matrix.trace (Eblk d L W a * P * Dl * Pᴴ * Eblk d L W a * Dl) := by
    rw [hR]
    simp only [Matrix.conjTranspose_mul, Duhamel_Eblk_conjTranspose]
    have e1 : G * Eblk d L W a * P * G * (Gᴴ * (Pᴴ * (Eblk d L W a * Gᴴ)))
        = G * (Eblk d L W a * P * (G * Gᴴ) * Pᴴ * Eblk d L W a * Gᴴ) := by
      simp only [Matrix.mul_assoc]
    rw [e1, Matrix.trace_mul_comm, hGG]
    have e2 : Eblk d L W a * P * (c • Dl) * Pᴴ * Eblk d L W a * Gᴴ * G
        = Eblk d L W a * P * (c • Dl) * Pᴴ * Eblk d L W a * (Gᴴ * G) := by
      simp only [Matrix.mul_assoc]
    rw [e2, hGG']
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    ring
  -- expand `Dl = G₊ - G₋` in both slots
  have hexp : Matrix.trace (Eblk d L W a * P * Dl * Pᴴ * Eblk d L W a * Dl)
      = Matrix.trace (Eblk d L W a * P * Gres M z true * Pᴴ * Eblk d L W a * Gres M z true)
        - Matrix.trace (Eblk d L W a * P * Gres M z true * Pᴴ * Eblk d L W a * Gres M z false)
        - Matrix.trace (Eblk d L W a * P * Gres M z false * Pᴴ * Eblk d L W a * Gres M z true)
        + Matrix.trace (Eblk d L W a * P * Gres M z false * Pᴴ * Eblk d L W a * Gres M z false) := by
    rw [hDl, Duhamel_Gres_true, Duhamel_Gres_false]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub]
    ring
  have hb : ∀ x y : Bool,
      ‖Matrix.trace (Eblk d L W a * P * Gres M z x * Pᴴ * Eblk d L W a * Gres M z y)‖
        ≤ RBM.Ind.loopMax d L W M z (2 * I.length) :=
    fun x y => Duhamel_norm_glue_le hM z rest a x y hlen
  have hsum : ‖Matrix.trace (Eblk d L W a * P * Dl * Pᴴ * Eblk d L W a * Dl)‖
      ≤ 4 * RBM.Ind.loopMax d L W M z (2 * I.length) := by
    rw [hexp]
    have := hb true true; have := hb true false; have := hb false true; have := hb false false
    calc _ ≤ ‖Matrix.trace (Eblk d L W a * P * Gres M z true * Pᴴ * Eblk d L W a * Gres M z true)‖
          + ‖Matrix.trace (Eblk d L W a * P * Gres M z true * Pᴴ * Eblk d L W a * Gres M z false)‖
          + ‖Matrix.trace (Eblk d L W a * P * Gres M z false * Pᴴ * Eblk d L W a * Gres M z true)‖
          + ‖Matrix.trace (Eblk d L W a * P * Gres M z false * Pᴴ * Eblk d L W a
              * Gres M z false)‖ := by
          refine (norm_add_le _ _).trans ?_
          refine add_le_add_left ?_ _
          refine (norm_sub_le _ _).trans ?_
          refine add_le_add_left ?_ _
          exact norm_sub_le _ _
      _ ≤ _ := by linarith
  have hcnorm : ‖c * c‖ = (|z.im|⁻¹) ^ 2 / 4 := by
    rw [hcdef, norm_mul, norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs]
    norm_num
    field_simp
    rw [sq_abs]; ring
  have hre : (∑ p, ∑ q, ‖DuhamelLoopCut d L W M z I k p q‖ ^ 2 : ℝ)
      = (Matrix.trace (DuhamelLoopCut d L W M z I k * (DuhamelLoopCut d L W M z I k)ᴴ)).re := by
    rw [← hfrob, Complex.ofReal_re]
  rw [hre]
  refine (Complex.re_le_norm _).trans ?_
  rw [htr, norm_mul, hcnorm]
  have h0 : 0 ≤ (|z.im|⁻¹) ^ 2 / 4 := by positivity
  calc (|z.im|⁻¹) ^ 2 / 4 * ‖Matrix.trace (Eblk d L W a * P * Dl * Pᴴ * Eblk d L W a * Dl)‖
      ≤ (|z.im|⁻¹) ^ 2 / 4 * (4 * RBM.Ind.loopMax d L W M z (2 * I.length)) :=
        mul_le_mul_of_nonneg_left hsum h0
    _ = _ := by ring

end Ward


/-! ### 3. The conditional variance of the linear part of one step -/

section QV

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- Reindex a block matrix back to the fine lattice (the inverse of `blockMat`). -/
private def Duhamel_unblock (A : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    Matrix (Idx d L W) (Idx d L W) ℂ :=
  A.submatrix (splitEquiv d L W) (splitEquiv d L W)

private theorem Duhamel_blockMat_unblock (A : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    blockMat d L W (Duhamel_unblock A) = A := by
  ext p q
  simp [blockMat, Duhamel_unblock]

private theorem Duhamel_blockMat_mul (A B : Matrix (Idx d L W) (Idx d L W) ℂ) :
    blockMat d L W (A * B) = blockMat d L W A * blockMat d L W B :=
  (Matrix.submatrix_mul_equiv A B _ (splitEquiv d L W).symm _).symm

private theorem Duhamel_trace_blockMat (A : Matrix (Idx d L W) (Idx d L W) ℂ) :
    Matrix.trace (blockMat d L W A) = Matrix.trace A := by
  simp only [Matrix.trace, Matrix.diag, blockMat, Matrix.submatrix_apply]
  exact (splitEquiv d L W).symm.sum_comp (fun i => A i i)

private theorem Duhamel_trace_blockMat_mul (X : Matrix (Idx d L W) (Idx d L W) ℂ)
    (C : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    Matrix.trace (blockMat d L W X * C) = Matrix.trace (X * Duhamel_unblock C) := by
  have h : blockMat d L W X * C = blockMat d L W (X * Duhamel_unblock C) := by
    rw [Duhamel_blockMat_mul, Duhamel_blockMat_unblock]
  rw [h, Duhamel_trace_blockMat]

private theorem Duhamel_frobSq_unblock (A : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    ∑ i, ∑ j, ‖Duhamel_unblock A i j‖ ^ 2 = ∑ p, ∑ q, ‖A p q‖ ^ 2 := by
  simp only [Duhamel_unblock, Matrix.submatrix_apply]
  rw [← (splitEquiv d L W).sum_comp]
  refine Finset.sum_congr rfl fun p _ => ?_
  exact (splitEquiv d L W).sum_comp (fun q => ‖A (splitEquiv d L W p) q‖ ^ 2)

/-- A matrix is determined by its trace pairing with the Hermitian matrices. -/
private theorem Duhamel_eq_of_trace_herm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ}
    (h : ∀ X : Matrix ι ι ℂ, X.IsHermitian → Matrix.trace (A * X) = Matrix.trace (B * X)) :
    A = B := by
  ext i j
  have hmul : ∀ (C : Matrix ι ι ℂ) (a b : ι) (x : ℂ),
      Matrix.trace (C * Matrix.single a b x) = C b a * x := by
    intro C a b x
    rw [Matrix.trace_mul_single]
    simp [mul_comm]
  by_cases hij : i = j
  · subst hij
    have h0 := h (Matrix.single i i (1 : ℂ))
      (by simp [Matrix.IsHermitian, Matrix.conjTranspose_single])
    rw [hmul, hmul] at h0
    simpa using h0
  · have hS : (Matrix.single i j (1 : ℂ) + Matrix.single j i 1).IsHermitian := by
      simp [Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_single, add_comm]
    have hT : (Matrix.single i j Complex.I - Matrix.single j i Complex.I).IsHermitian := by
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_single, Matrix.conjTranspose_single]
      simp only [Complex.star_def, Complex.conj_I, ← Matrix.single_neg]
      abel
    have h1 := h _ hS
    have h2 := h _ hT
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub, hmul] at h1 h2
    have h2' : A j i - A i j = B j i - B i j := by
      refine mul_right_cancel₀ Complex.I_ne_zero ?_
      linear_combination h2
    linear_combination (h1 - h2') / 2

private theorem Duhamel_frobSq_sum_le {ι : Type*} [Fintype ι] (s : Finset ℕ)
    (R : ℕ → Matrix ι ι ℂ) :
    ∑ i, ∑ j, ‖(∑ k ∈ s, R k) i j‖ ^ 2
      ≤ (s.card : ℝ) * ∑ k ∈ s, ∑ i, ∑ j, ‖R k i j‖ ^ 2 := by
  have key : ∀ i j : ι, ‖(∑ k ∈ s, R k) i j‖ ^ 2 ≤ (s.card : ℝ) * ∑ k ∈ s, ‖R k i j‖ ^ 2 := by
    intro i j
    rw [Matrix.sum_apply]
    have h1 : ‖∑ k ∈ s, R k i j‖ ≤ ∑ k ∈ s, ‖R k i j‖ := norm_sum_le _ _
    have h2 : (∑ k ∈ s, ‖R k i j‖) ^ 2 ≤ (s.card : ℝ) * ∑ k ∈ s, ‖R k i j‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  calc ∑ i, ∑ j, ‖(∑ k ∈ s, R k) i j‖ ^ 2
      ≤ ∑ i, ∑ j, (s.card : ℝ) * ∑ k ∈ s, ‖R k i j‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
    _ = (s.card : ℝ) * ∑ i, ∑ j, ∑ k ∈ s, ‖R k i j‖ ^ 2 := by simp only [Finset.mul_sum]
    _ = (s.card : ℝ) * ∑ k ∈ s, ∑ i, ∑ j, ‖R k i j‖ ^ 2 := by
        congr 1
        calc ∑ i, ∑ j, ∑ k ∈ s, ‖R k i j‖ ^ 2 = ∑ i, ∑ k ∈ s, ∑ j, ‖R k i j‖ ^ 2 :=
              Finset.sum_congr rfl fun i _ => Finset.sum_comm
          _ = ∑ k ∈ s, ∑ i, ∑ j, ‖R k i j‖ ^ 2 := Finset.sum_comm


/-! #### The Leibniz rule for the loop observable at a Hermitian point

(Jets of the loop observable for a general spectral parameter `z`, `Im z ≠ 0`, and a general loop
index.) -/

/-- `blockMat` as a continuous real-linear map. -/
private def Duhamel_blockCLM (d L W : ℕ) [NeZero L] [NeZero W] :
    Matrix (Idx d L W) (Idx d L W) ℂ →L[ℝ] Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := blockMat d L W
      map_add' := fun A C => by ext p q; simp [blockMat]
      map_smul' := fun r A => by ext p q; simp [blockMat] }

private theorem Duhamel_blockMat_add_smul (A C : Matrix (Idx d L W) (Idx d L W) ℂ) (y : ℂ) :
    blockMat d L W (A + y • C) = blockMat d L W A + y • blockMat d L W C := by
  ext p q
  simp [blockMat]

/-- The trace as a continuous real-linear map. -/
private def Duhamel_trCLM (n : Type*) [Fintype n] [DecidableEq n] : Matrix n n ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap n ℝ ℂ)

/-- The resolvent along a Hermitian line has derivative `-G D G`. -/
private theorem Duhamel_hasDerivAt_green {n : Type*} [Fintype n] [DecidableEq n] {H D : Matrix n n ℂ}
    (hH : H.IsHermitian) (hD : D.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => green (H + (s : ℂ) • D) z)
      (-(green (H + (t : ℂ) • D) z * D * green (H + (t : ℂ) • D) z)) t := by
  have hgr : ∀ s : ℝ, green (H + (s : ℂ) • D) z
      = Ring.inverse (H - z • (1 : Matrix n n ℂ) + (s : ℂ) • D) := by
    intro s
    change (H + (s : ℂ) • D - z • (1 : Matrix n n ℂ))⁻¹ = _
    rw [Matrix.nonsing_inv_eq_ringInverse]
    congr 1
    abel
  have hU : ∀ s : ℝ, IsUnit (H - z • (1 : Matrix n n ℂ) + (s : ℂ) • D) := by
    intro s
    have he : H - z • (1 : Matrix n n ℂ) + (s : ℂ) • D
        = (H + (s : ℂ) • D) - z • (1 : Matrix n n ℂ) := by abel
    rw [he]
    exact isUnit_sub_smul_of_isHermitian (OneStep_isHermitian_add_realSmul hH hD s) hz
  have h := Duhamel_hasDerivAt_lineInverse hU t
  simp only [← hgr] at h
  exact h

private theorem Duhamel_hasDerivAt_Gsig {n : Type*} [Fintype n] [DecidableEq n] {H D : Matrix n n ℂ}
    (hH : H.IsHermitian) (hD : D.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (σ : Bool) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Gres (H + (s : ℂ) • D) z σ)
      (-(Gres (H + (t : ℂ) • D) z σ * D * Gres (H + (t : ℂ) • D) z σ)) t := by
  cases σ
  · simp only [Duhamel_Gres_false]
    exact Duhamel_hasDerivAt_green hH hD (by simpa using hz) t
  · simp only [Duhamel_Gres_true]
    exact Duhamel_hasDerivAt_green hH hD hz t

/-- Differentiate the first factor of the word `m`: `head (p :: m') = (-(G D G) E_p) · wd m'`. -/
private def Duhamel_head (H D : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) :
    List (Bool × Zd d L) → Matrix (Vtx d L W) (Vtx d L W) ℂ
  | [] => 0
  | p :: m => (-(Gres H z p.1 * D * Gres H z p.1) * Eblk d L W p.2) * Duhamel_wd H z m

/-- The Leibniz sum of a word: differentiate the `q`-th factor, `q < |l|`. -/
private def Duhamel_wordDeriv (H D : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (l : List (Bool × Zd d L)) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  ∑ q ∈ Finset.range l.length, Duhamel_wd H z (l.take q) * Duhamel_head H D z (l.drop q)

private theorem Duhamel_wordDeriv_cons (H D : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (p : Bool × Zd d L) (l : List (Bool × Zd d L)) :
    Duhamel_wordDeriv H D z (p :: l) = Duhamel_head H D z (p :: l) +
      Gres H z p.1 * Eblk d L W p.2 * Duhamel_wordDeriv H D z l := by
  have Duhamel_wd_nil (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) :
      Duhamel_wd M z ([] : List (Bool × Zd d L)) = 1 := rfl
  unfold Duhamel_wordDeriv
  rw [List.length_cons, Finset.sum_range_succ']
  simp only [List.take_succ_cons, List.drop_succ_cons, Duhamel_wd_cons, List.take_zero,
    List.drop_zero, Duhamel_wd_nil, Matrix.one_mul, Finset.mul_sum, Matrix.mul_assoc]
  rw [add_comm]

/-- **Leibniz rule for a word** along a Hermitian line. -/
private theorem Duhamel_hasDerivAt_wd {H D : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) (hD : D.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (l : List (Bool × Zd d L)) :
    HasDerivAt (fun y : ℝ => Duhamel_wd (H + (y : ℂ) • D) z l) (Duhamel_wordDeriv H D z l) 0 := by
  have Duhamel_wd_nil (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) :
      Duhamel_wd M z ([] : List (Bool × Zd d L)) = 1 := rfl
  induction l with
  | nil =>
      have h0 : Duhamel_wordDeriv H D z ([] : List (Bool × Zd d L)) = 0 := by
        simp [Duhamel_wordDeriv]
      rw [h0]
      simpa only [Duhamel_wd_nil] using
        hasDerivAt_const (0 : ℝ) (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)
  | cons p l ih =>
      have hG := Duhamel_hasDerivAt_Gsig hH hD hz p.1 0
      have h00 : H + ((0 : ℝ) : ℂ) • D = H := by simp
      rw [h00] at hG
      have hhead := hG.mul_const (Eblk d L W p.2)
      have h := hhead.mul ih
      rw [Duhamel_wordDeriv_cons]
      have hfun : (fun y : ℝ => Duhamel_wd (H + (y : ℂ) • D) z (p :: l)) =
          fun y : ℝ => Gres (H + (y : ℂ) • D) z p.1 * Eblk d L W p.2 *
            Duhamel_wd (H + (y : ℂ) • D) z l := rfl
      rw [hfun]
      convert h using 1
      simp [Duhamel_head]

/-- The `q`-th Leibniz term as a pairing against the cut chain:
`tr(wd(l[:q]) · ∂_q) = -tr(D · wd(l[q:] ++ l[:q]) · G^{l_q})` (cyclicity of the trace). -/
private theorem Duhamel_trace_term (H D : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (l : List (Bool × Zd d L)) {q : ℕ} (hq : q < l.length) :
    Matrix.trace (Duhamel_wd H z (l.take q) * Duhamel_head H D z (l.drop q)) =
      -Matrix.trace (D * (Duhamel_wd H z (l.drop q ++ l.take q) *
        Gres H z (l.getD q (true, 0)).1)) := by
  rw [Duhamel_getD_eq _ _ hq, List.drop_eq_getElem_cons hq, Duhamel_head,
    Duhamel_wd_append, Duhamel_wd_cons]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.trace_neg]
  congr 1
  rw [show Duhamel_wd H z (l.take q) * (Gres H z l[q].1 * D * Gres H z l[q].1 * Eblk d L W l[q].2 *
        Duhamel_wd H z (l.drop (q + 1))) =
      (Duhamel_wd H z (l.take q) * Gres H z l[q].1) *
        (D * (Gres H z l[q].1 * Eblk d L W l[q].2 * Duhamel_wd H z (l.drop (q + 1)))) by
    simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- The resolvent of `blockMat M` is `C²` at every `M` for which `blockMat M - w` is invertible. -/
private theorem Duhamel_contDiffAt_green {w : ℂ} {M : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hu : IsUnit (blockMat d L W M - w • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ))) :
    ContDiffAt ℝ 2 (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ => green (blockMat d L W M') w) M := by
  have hA : ContDiff ℝ 2 (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ =>
      blockMat d L W M' - w • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) :=
    ((Duhamel_blockCLM d L W).contDiff).sub contDiff_const
  have hinv : ContDiffAt ℝ 2 (Ring.inverse (M₀ := Matrix (Vtx d L W) (Vtx d L W) ℂ))
      (blockMat d L W M - w • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) := by
    obtain ⟨u, hu'⟩ := hu
    rw [← hu']
    exact contDiffAt_ringInverse ℝ u
  have h := hinv.comp M hA.contDiffAt
  have hfun : (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ => green (blockMat d L W M') w)
      = Ring.inverse ∘ (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ =>
        blockMat d L W M' - w • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) := by
    funext M'
    exact Matrix.nonsing_inv_eq_ringInverse _
  rw [hfun]
  exact h

private theorem Duhamel_contDiffAt_Gsig {z : ℂ} (hz : z.im ≠ 0) (σ : Bool)
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) :
    ContDiffAt ℝ 2 (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ => Gres (blockMat d L W M') z σ) M := by
  have hMb : (blockMat d L W M).IsHermitian := hM.submatrix _
  cases σ
  · simp only [Duhamel_Gres_false]
    exact Duhamel_contDiffAt_green (isUnit_sub_smul_of_isHermitian hMb (by simpa using hz))
  · simp only [Duhamel_Gres_true]
    exact Duhamel_contDiffAt_green (isUnit_sub_smul_of_isHermitian hMb hz)

private theorem Duhamel_contDiffAt_word {z : ℂ} (hz : z.im ≠ 0) (l : List (Bool × Zd d L))
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) :
    ContDiffAt ℝ 2 (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ =>
      l.foldr (fun p X => Gres (blockMat d L W M') z p.1 * Eblk d L W p.2 * X) 1) M := by
  induction l with
  | nil => exact contDiffAt_const
  | cons p l ih =>
    have hEp : ContDiffAt ℝ 2 (fun _ : Matrix (Idx d L W) (Idx d L W) ℂ => Eblk d L W p.2) M :=
      contDiffAt_const
    exact ((Duhamel_contDiffAt_Gsig hz p.1 hM).mul hEp).mul ih

/-- The loop observable `M ↦ 𝓛(blockMat M, z, I)` is `C²` at every Hermitian point (public here;
`private` in the source, `DuhA:713`; the declaration shared with `DuhamelA2`, `DuhamelB`, `DuhamelC`). -/
theorem Duhamel_contDiffAt_loop {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (Zd d L))
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) :
    ContDiffAt ℝ 2 (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ => loopL d L W (blockMat d L W M') z I) M :=
  (Duhamel_trCLM (Vtx d L W)).contDiff.contDiffAt.comp M
    (Duhamel_contDiffAt_word hz (I.σ.zip I.a) hM)

/-- **Leibniz decomposition of the loop derivative**: for Hermitian `M, X`,
`D𝓛(M)[X] = -∑_q tr(X̂ · A_q)`. -/
private theorem Duhamel_fderiv_loop {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (Zd d L))
    {M X : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) (hX : X.IsHermitian) :
    fderiv ℝ (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ => loopL d L W (blockMat d L W M') z I) M X
      = -∑ q ∈ Finset.range (I.σ.zip I.a).length,
          Matrix.trace (blockMat d L W X * (Duhamel_wd (blockMat d L W M) z
            ((I.σ.zip I.a).drop q ++ (I.σ.zip I.a).take q) *
              Gres (blockMat d L W M) z ((I.σ.zip I.a).getD q (true, 0)).1)) := by
  set Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ := fun M' => loopL d L W (blockMat d L W M') z I with hΦ
  set l : List (Bool × Zd d L) := I.σ.zip I.a with hl
  have hdiff : DifferentiableAt ℝ Φ M :=
    (Duhamel_contDiffAt_loop hz I hM).differentiableAt (by norm_num)
  have h1 : HasDerivAt (fun s : ℝ => Φ (M + (s : ℂ) • X)) (fderiv ℝ Φ M X) 0 := by
    have h := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (Duhamel_hasDerivAt_line M X 0)
      (by simp)
    simpa [Function.comp_def] using h
  have hMb : (blockMat d L W M).IsHermitian := hM.submatrix _
  have hXb : (blockMat d L W X).IsHermitian := hX.submatrix _
  have hfun : (fun s : ℝ => Φ (M + (s : ℂ) • X))
      = fun s : ℝ => Matrix.trace (Duhamel_wd (blockMat d L W M + (s : ℂ) • blockMat d L W X) z l) := by
    funext s
    simp only [hΦ]
    rw [Duhamel_blockMat_add_smul]
    rfl
  have h2 : HasDerivAt (fun s : ℝ => Φ (M + (s : ℂ) • X))
      (Matrix.trace (Duhamel_wordDeriv (blockMat d L W M) (blockMat d L W X) z l)) 0 := by
    rw [hfun]
    exact (Duhamel_trCLM (Vtx d L W)).hasFDerivAt.comp_hasDerivAt 0
      (Duhamel_hasDerivAt_wd hMb hXb hz l)
  rw [h1.unique h2, Duhamel_wordDeriv, Matrix.trace_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  exact Duhamel_trace_term (blockMat d L W M) (blockMat d L W X) z l (Finset.mem_range.1 hq)


private theorem Duhamel_gloopProd_mk (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (σ : List Bool) (a : List (Zd d L)) :
    gloopProd d L W M z ⟨σ, a⟩ = Duhamel_wd M z (σ.zip a) := rfl

/-- The zip of a rotated pair of lists is the rotation of the zip. -/
private theorem Duhamel_zip_drop_take {α β : Type*} (σ : List α) (a : List β)
    (h : σ.length = a.length) (p q : ℕ) :
    (σ.drop p ++ σ.take q).zip (a.drop p ++ a.take q) = (σ.zip a).drop p ++ (σ.zip a).take q := by
  rw [List.zip_append (by simp [h])]
  simp only [List.zip_eq_zipWith, List.drop_zipWith, List.take_zipWith]

/-- `DuhamelLoopCut` is the cut chain `wd(rot_k) · G^{σ_k}` of the Leibniz decomposition. -/
private theorem Duhamel_loopCut_eq (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    {I : LoopIdx (Zd d L)} (hI : I.WF) {k : ℕ} (hk : k < (I.σ.zip I.a).length) :
    DuhamelLoopCut d L W H z I k
      = Duhamel_wd H z ((I.σ.zip I.a).drop k ++ (I.σ.zip I.a).take k) *
          Gres H z ((I.σ.zip I.a).getD k (true, 0)).1 := by
  have hσlen : I.σ.length = I.a.length := hI
  have hσk : k < I.σ.length := lt_of_lt_of_le hk (by simp [List.length_zip])
  have hak : k < I.a.length := lt_of_lt_of_le hk (by simp [List.length_zip])
  have hgetD : (I.σ.zip I.a).getD k (true, 0) = (I.σ[k], I.a[k]) := by
    rw [Duhamel_getD_eq _ _ hk, List.getElem_zip]
  unfold DuhamelLoopCut
  rw [Duhamel_gloopProd_mk, Duhamel_zip_drop_take I.σ I.a hσlen (k + 1) k,
    List.drop_eq_getElem_cons hk, List.cons_append, Duhamel_wd_cons, hgetD,
    Duhamel_getD_eq _ _ hσk, Duhamel_getD_eq _ _ hak, List.getElem_zip]

/-- **`gradMat` of a loop observable is minus the sum of its cut blocks** at a Hermitian matrix. -/
private theorem Duhamel_gradMat_loop {z : ℂ} (hz : z.im ≠ 0) {I : LoopIdx (Zd d L)} (hI : I.WF)
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) :
    gradMat (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ => loopL d L W (blockMat d L W M') z I) M
      = -∑ k ∈ Finset.range I.a.length,
          Duhamel_unblock (DuhamelLoopCut d L W (blockMat d L W M) z I k) := by
  have hσlen : I.σ.length = I.a.length := hI
  have hlen : (I.σ.zip I.a).length = I.a.length := by
    rw [List.length_zip, hσlen, min_self]
  apply Duhamel_eq_of_trace_herm
  intro X hX
  rw [← fderiv_eq_trace_gradMat M hX, Duhamel_fderiv_loop hz I hM hX, Matrix.neg_mul,
    Matrix.sum_mul, Matrix.trace_neg, Matrix.trace_sum, hlen]
  congr 1
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq' : q < (I.σ.zip I.a).length := by rw [hlen]; exact Finset.mem_range.1 hq
  rw [← Duhamel_loopCut_eq (blockMat d L W M) z hI hq', Duhamel_trace_blockMat_mul,
    Matrix.trace_mul_comm]

private theorem Duhamel_frobSq_neg {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) :
    ∑ i, ∑ j, ‖(-A) i j‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  simp

private theorem Duhamel_frobSq_negI {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) :
    ∑ i, ∑ j, ‖(-Complex.I • A) i j‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  simp

/-- **(7.43) for the constant profile**: the unit-GUE Frobenius norm of the gradient of an
`n`-loop is at most `n² |Im z|⁻² L^{(2n)}`. -/
private theorem Duhamel_frobSq_gradMat_le {z : ℂ} (hz : z.im ≠ 0) {I : LoopIdx (Zd d L)}
    (hI : I.WF) {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) :
    ∑ i, ∑ j, ‖gradMat (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ =>
        loopL d L W (blockMat d L W M') z I) M i j‖ ^ 2
      ≤ (I.length : ℝ) ^ 2 * (|z.im|⁻¹) ^ 2 * RBM.Ind.loopMax d L W (blockMat d L W M) z (2 * I.length) := by
  rw [Duhamel_gradMat_loop hz hI hM, Duhamel_frobSq_neg]
  refine (Duhamel_frobSq_sum_le _ _).trans ?_
  rw [Finset.card_range]
  have hk : ∀ k ∈ Finset.range I.a.length,
      ∑ i, ∑ j, ‖Duhamel_unblock (DuhamelLoopCut d L W (blockMat d L W M) z I k) i j‖ ^ 2
      ≤ (|z.im|⁻¹) ^ 2 * RBM.Ind.loopMax d L W (blockMat d L W M) z (2 * I.length) := by
    intro k hk
    rw [Duhamel_frobSq_unblock]
    exact Duhamel_frobSq_loopCut_le (hM.submatrix _) hz hI (Finset.mem_range.1 hk)
  have h1 := Finset.sum_le_sum hk
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
  have hlen : (I.length : ℝ) = (I.a.length : ℝ) := rfl
  rw [hlen]
  have h0 : (0 : ℝ) ≤ (I.a.length : ℝ) := Nat.cast_nonneg _
  calc (I.a.length : ℝ) * ∑ k ∈ Finset.range I.a.length,
        ∑ i, ∑ j, ‖Duhamel_unblock (DuhamelLoopCut d L W (blockMat d L W M) z I k) i j‖ ^ 2
      ≤ (I.a.length : ℝ) * ((I.a.length : ℝ) * ((|z.im|⁻¹) ^ 2
          * RBM.Ind.loopMax d L W (blockMat d L W M) z (2 * I.length))) :=
        mul_le_mul_of_nonneg_left h1 h0
    _ = _ := by ring

end QV

/-- **The variance proxy of the linear part**: for a Hermitian `M`, a well-formed loop `I` and
`Im z ≠ 0`, with
`Φ M = 𝓛(blockMat M, z, I)`,
`max(vGue(∇Φ), vGue(-i ∇Φ)) ≤ 8 · n² |Im z|⁻² L^{(2n)}(blockMat M, z)`, `n = |I|`. -/
theorem Duhamel_vGue_gradMat_le {d : ℕ} {sz : Sizes d} {n : ℕ} {z : ℂ} (hz : z.im ≠ 0)
    {I : LoopIdx (Zd d (sz.L n))} (hwf : I.WF)
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian) :
    max (vGue sz n (gradMat (fun M' : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
          loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M') z I) M) : ℝ)
        (vGue sz n (-Complex.I • gradMat (fun M' : Matrix (Idx d (sz.L n) (sz.W n))
          (Idx d (sz.L n) (sz.W n)) ℂ => loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M') z I) M) : ℝ)
      ≤ 8 * ((I.length : ℝ) ^ 2 * (|z.im|⁻¹) ^ 2
          * RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) z (2 * I.length)) := by
  have h := Duhamel_frobSq_gradMat_le hz hwf hM
  refine max_le ?_ ?_
  · exact (Duhamel_vGue_le sz n _).trans (by linarith)
  · refine (Duhamel_vGue_le sz n _).trans ?_
    rw [Duhamel_frobSq_negI]
    linarith

/-! ### 4. Crude and Lipschitz bounds on `loopMax` -/

section LoopMaxBounds

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem Duhamel_norm_Eblk_le_one (a : Zd d L) : ‖Eblk d L W a‖ ≤ 1 := by
  refine (norm_Eblk_le_inv_W_sq d L W a).trans ?_
  have hW1 : (1 : ℝ) ≤ (W : ℝ) := Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne W))
  exact inv_le_one_of_one_le₀ (one_le_pow₀ hW1)

/-- `|L_{σ,a}| ≤ (LW)^d |Im z|^{-m}`, hence `L^{(m)} ≤ (LW)^d |Im z|^{-m}`
(`card (Vtx d L W) = (L W)^d`; the `d`-line, source `(L W)²`). -/
theorem Duhamel_loopMax_le_crude {M : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hM : M.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (m : ℕ) :
    RBM.Ind.loopMax d L W M z m ≤ ((L : ℝ) * (W : ℝ)) ^ d * (|z.im|⁻¹) ^ m := by
  refine RBM.Ind.loopMax_le fun I hσ ha => ?_
  have hwf : I.WF := by unfold LoopIdx.WF; rw [hσ, ha]
  have hη : 0 < |z.im| := abs_pos.mpr hz
  have h := norm_gloop_le_crude d L W hM hη le_rfl I hwf
  refine h.trans ?_
  rw [ha]
  have hLW : ((L * W) ^ d : ℕ) = ((L : ℝ) * (W : ℝ)) ^ d := by push_cast; ring
  have hW1 : (1 : ℝ) ≤ (W : ℝ) := Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne W))
  have hW2 : ((W : ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hW1)
  have hpow : (|z.im|⁻¹ * ((W : ℝ) ^ d)⁻¹) ^ m ≤ (|z.im|⁻¹) ^ m := by
    refine pow_le_pow_left₀ (by positivity) ?_ m
    calc |z.im|⁻¹ * ((W : ℝ) ^ d)⁻¹ ≤ |z.im|⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hW2 (by positivity)
      _ = |z.im|⁻¹ := mul_one _
  have h0 : (0 : ℝ) ≤ ((L : ℝ) * (W : ℝ)) ^ d := by positivity
  rw [hLW]
  exact mul_le_mul_of_nonneg_left hpow h0

/-- The telescoping bound for two signed words. -/
private theorem Duhamel_word_le (G : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ) {K : ℝ}
    (hK : 0 ≤ K) (hG : ∀ s, ‖G s‖ ≤ K) (l : List (Bool × Zd d L)) :
    ‖l.foldr (fun p X => G p.1 * Eblk d L W p.2 * X)
        (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)‖ ≤ K ^ l.length := by
  induction l with
  | nil => simp
  | cons p l ih =>
      simp only [List.foldr_cons, List.length_cons, pow_succ]
      calc ‖G p.1 * Eblk d L W p.2 *
            l.foldr (fun p X => G p.1 * Eblk d L W p.2 * X) 1‖
          ≤ ‖G p.1‖ * ‖Eblk d L W p.2‖ *
              ‖l.foldr (fun p X => G p.1 * Eblk d L W p.2 * X) 1‖ :=
            (norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ K * 1 * K ^ l.length :=
            mul_le_mul (mul_le_mul (hG p.1) (Duhamel_norm_Eblk_le_one p.2) (norm_nonneg _) hK)
              ih (norm_nonneg _) (by positivity)
        _ = K ^ l.length * K := by ring

private theorem Duhamel_word_sub_le (G₁ G₂ : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ)
    {K Δg : ℝ} (hK : 1 ≤ K) (hΔ : 0 ≤ Δg) (hG₁ : ∀ s, ‖G₁ s‖ ≤ K) (hG₂ : ∀ s, ‖G₂ s‖ ≤ K)
    (hGd : ∀ s, ‖G₁ s - G₂ s‖ ≤ Δg) (l : List (Bool × Zd d L)) :
    ‖l.foldr (fun p X => G₁ p.1 * Eblk d L W p.2 * X)
          (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)
      - l.foldr (fun p X => G₂ p.1 * Eblk d L W p.2 * X) 1‖
      ≤ (l.length : ℝ) * K ^ l.length * Δg := by
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK
  induction l with
  | nil => simp
  | cons p l ih =>
      simp only [List.foldr_cons, List.length_cons]
      set w₁ := l.foldr (fun p X => G₁ p.1 * Eblk d L W p.2 * X)
        (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) with hw₁
      set w₂ := l.foldr (fun p X => G₂ p.1 * Eblk d L W p.2 * X)
        (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) with hw₂
      have hsplit : G₁ p.1 * Eblk d L W p.2 * w₁ - G₂ p.1 * Eblk d L W p.2 * w₂
          = (G₁ p.1 - G₂ p.1) * Eblk d L W p.2 * w₁
            + G₂ p.1 * Eblk d L W p.2 * (w₁ - w₂) := by
        simp only [Matrix.sub_mul, Matrix.mul_sub]
        abel
      have hw1 : ‖w₁‖ ≤ K ^ l.length := Duhamel_word_le G₁ hK0 hG₁ l
      have hE := Duhamel_norm_Eblk_le_one (L := L) (W := W) p.2
      have hA : ‖(G₁ p.1 - G₂ p.1) * Eblk d L W p.2 * w₁‖ ≤ Δg * K ^ l.length := by
        calc ‖(G₁ p.1 - G₂ p.1) * Eblk d L W p.2 * w₁‖
            ≤ ‖G₁ p.1 - G₂ p.1‖ * ‖Eblk d L W p.2‖ * ‖w₁‖ :=
              (norm_mul_le _ _).trans
                (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
          _ ≤ Δg * 1 * K ^ l.length :=
              mul_le_mul (mul_le_mul (hGd p.1) hE (norm_nonneg _) hΔ) hw1 (norm_nonneg _)
                (by positivity)
          _ = Δg * K ^ l.length := by ring
      have hB : ‖G₂ p.1 * Eblk d L W p.2 * (w₁ - w₂)‖
          ≤ K * ((l.length : ℝ) * K ^ l.length * Δg) := by
        calc ‖G₂ p.1 * Eblk d L W p.2 * (w₁ - w₂)‖
            ≤ ‖G₂ p.1‖ * ‖Eblk d L W p.2‖ * ‖w₁ - w₂‖ :=
              (norm_mul_le _ _).trans
                (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
          _ ≤ K * 1 * ((l.length : ℝ) * K ^ l.length * Δg) :=
              mul_le_mul (mul_le_mul (hG₂ p.1) hE (norm_nonneg _) hK0) ih (norm_nonneg _)
                (by positivity)
          _ = K * ((l.length : ℝ) * K ^ l.length * Δg) := by ring
      have hpow : K ^ l.length ≤ K ^ (l.length + 1) := pow_le_pow_right₀ hK (Nat.le_succ _)
      rw [hsplit]
      calc ‖(G₁ p.1 - G₂ p.1) * Eblk d L W p.2 * w₁
            + G₂ p.1 * Eblk d L W p.2 * (w₁ - w₂)‖
          ≤ Δg * K ^ l.length + K * ((l.length : ℝ) * K ^ l.length * Δg) :=
            (norm_add_le _ _).trans (add_le_add hA hB)
        _ ≤ Δg * K ^ (l.length + 1) + K * ((l.length : ℝ) * K ^ l.length * Δg) := by
            have := mul_le_mul_of_nonneg_left hpow hΔ
            linarith
        _ = ((l.length + 1 : ℕ) : ℝ) * K ^ (l.length + 1) * Δg := by
            push_cast
            ring

/-- The Lipschitz bound of `loopMax` in the spectral parameter (the `d`-line:
`card (Vtx d L W) = (L W)^d`, source `(L W)²`). -/
theorem Duhamel_loopMax_shift_le {M : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hM : M.IsHermitian) {z z' : ℂ} (hz : z.im ≠ 0) (hz' : z'.im ≠ 0) {K : ℝ} (hK : 1 ≤ K)
    (hGz : ‖green M z‖ ≤ K) (hGz' : ‖green M z'‖ ≤ K) (m : ℕ) :
    RBM.Ind.loopMax d L W M z' m
      ≤ RBM.Ind.loopMax d L W M z m
          + ((L : ℝ) * (W : ℝ)) ^ d * m * K ^ m * (‖z' - z‖ * K ^ 2) := by
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK
  have hsub : ‖green M z' - green M z‖ ≤ ‖z' - z‖ * K ^ 2 := by
    rw [green_sub_green (isUnit_sub_smul_of_isHermitian hM hz')
      (isUnit_sub_smul_of_isHermitian hM hz), norm_smul]
    have h1 : ‖green M z' * green M z‖ ≤ K ^ 2 := by
      refine (norm_mul_le _ _).trans ?_
      rw [sq]
      exact mul_le_mul hGz' hGz (norm_nonneg _) hK0
    exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  have hΔ : 0 ≤ ‖z' - z‖ * K ^ 2 := by positivity
  have hF : ∀ w : ℂ, Gres M w false = (green M w)ᴴ := fun w => by
    have h := Duhamel_Gres_conjTranspose hM w true
    rw [← Duhamel_Gres_true, h]
    rfl
  have hGd : ∀ s : Bool, ‖Gres M z' s - Gres M z s‖ ≤ ‖z' - z‖ * K ^ 2 := by
    intro s
    cases s
    · rw [hF, hF, ← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
      exact hsub
    · rw [Duhamel_Gres_true, Duhamel_Gres_true]
      exact hsub
  have hGn : ∀ w : ℂ, ‖green M w‖ ≤ K → ∀ s : Bool, ‖Gres M w s‖ ≤ K := by
    intro w hGw s
    cases s
    · rw [hF, Matrix.l2_opNorm_conjTranspose]
      exact hGw
    · rw [Duhamel_Gres_true]
      exact hGw
  refine RBM.Ind.loopMax_le fun I hσ ha => ?_
  have hwf : I.WF := by unfold LoopIdx.WF; rw [hσ, ha]
  have hlen : (I.σ.zip I.a).length = m := by
    rw [List.length_zip, hσ, ha, min_self]
  have hword := Duhamel_word_sub_le (Gres M z') (Gres M z) hK hΔ (hGn z' hGz')
    (hGn z hGz) hGd (I.σ.zip I.a)
  rw [hlen] at hword
  have htrace := norm_matrix_trace_le_card_mul
    (gloopProd d L W M z' I - gloopProd d L W M z I)
  rw [Matrix.trace_sub] at htrace
  have hle : ‖loopL d L W M z I‖ ≤ RBM.Ind.loopMax d L W M z m :=
    RBM.Ind.norm_gloop_le_loopMax I hσ ha
  have hdiff : ‖loopL d L W M z' I - loopL d L W M z I‖
      ≤ ((L : ℝ) * (W : ℝ)) ^ d * (m * K ^ m * (‖z' - z‖ * K ^ 2)) := by
    refine htrace.trans ?_
    have hcard : (Fintype.card (Vtx d L W) : ℝ) = ((L : ℝ) * (W : ℝ)) ^ d := by
      rw [card_BlockIndex]; push_cast; ring
    rw [hcard]
    exact mul_le_mul_of_nonneg_left hword (by positivity)
  calc ‖loopL d L W M z' I‖ ≤ ‖loopL d L W M z I‖ + ‖loopL d L W M z' I - loopL d L W M z I‖ := by
        have := norm_add_le (loopL d L W M z I) (loopL d L W M z' I - loopL d L W M z I)
        simpa using this
    _ ≤ _ := by
        have := add_le_add hle hdiff
        linarith

end LoopMaxBounds

/-! ### 5. Compiled nonempty instances

Namespace `RBM.Univ.GUEPhase.DuhamelA1Inst`.  `Duhamel_vGue_le` and `Duhamel_vGue_gradMat_le` at the
merged `sz0` (`d = 3`, `L = 4`, `W = 32`, `N = 2097152`, size index `n = 0`); the loop statements at
`d = 3`, `L = W = 2` (`card (Vtx 3 2 2) = 64`), `M = 0` (Hermitian), `z = i`, the one-edge loop
`(+; 0)` and, for the shift bound, `z' = 2 i`, `K = 1`.  No hypothesis is left open: every
deterministic hypothesis (`M.IsHermitian`, `z.im ≠ 0`, `I.WF`, `k < |I|`, `1 ≤ K`,
`‖G(z)‖, ‖G(z')‖ ≤ K`) is discharged. -/

end RBM.Univ.GUEPhase

namespace RBM.Univ.GUEPhase.DuhamelA1Inst

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.LinearForm RBM.Path
  RBM.Loop RBM.Gauss.SizesInst RBM.Univ.GUEPhase
open scoped Matrix.Norms.L2Operator

/-- The one-edge loop `(+; 0)`. -/
private def DuhamelA1Inst_loop1 (d L : ℕ) : LoopIdx (Zd d L) := ⟨[true], [0]⟩

private theorem DuhamelA1Inst_loop1_wf (d L : ℕ) : (DuhamelA1Inst_loop1 d L).WF := rfl

/-- The fine-lattice index type at `sz0`, `n = 0`: `Z_{128}^3`, `N = 2097152`. -/
private abbrev DuhamelA1Inst_Idx0 : Type := Idx 3 (sz0.L 0) (sz0.W 0)

/-- `‖1‖_F² = N = 2097152` at `sz0`: the right side of `Duhamel_vGue_le` at `A = 1` is `8 N`. -/
theorem frobSq_one_sz0 :
    ∑ i, ∑ j, ‖(1 : Matrix DuhamelA1Inst_Idx0 DuhamelA1Inst_Idx0 ℂ) i j‖ ^ 2 = 2097152 := by
  have h : ∀ i j : DuhamelA1Inst_Idx0,
      ‖(1 : Matrix DuhamelA1Inst_Idx0 DuhamelA1Inst_Idx0 ℂ) i j‖ ^ 2 = if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  simp only [h, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  exact_mod_cast card_Idx_sz0

/-- `Duhamel_vGue_le` at `sz0`, `n = 0`, `A = 1`: `vGue 1 ≤ 8 N`, `N = 2097152`. -/
theorem vGue_le_inst :
    (vGue sz0 0 (1 : Matrix DuhamelA1Inst_Idx0 DuhamelA1Inst_Idx0 ℂ) : ℝ)
      ≤ 8 * ∑ i, ∑ j, ‖(1 : Matrix DuhamelA1Inst_Idx0 DuhamelA1Inst_Idx0 ℂ) i j‖ ^ 2 :=
  Duhamel_vGue_le sz0 0 1

theorem vGue_le_inst_value :
    (vGue sz0 0 (1 : Matrix DuhamelA1Inst_Idx0 DuhamelA1Inst_Idx0 ℂ) : ℝ) ≤ 8 * 2097152 := by
  have h := vGue_le_inst
  rwa [frobSq_one_sz0] at h

/-- `Duhamel_loopMax_le_crude` at `d = 3`, `L = W = 2`, `M = 0`, `z = i`, `m = 2`:
`L^{(2)} ≤ (2 · 2)^3 · 1^{-2}`. -/
theorem loopMax_le_crude_inst :
    RBM.Ind.loopMax 3 2 2 (0 : Matrix (Vtx 3 2 2) (Vtx 3 2 2) ℂ) Complex.I 2
      ≤ (((2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ)) ^ 3 * (|Complex.I.im|⁻¹) ^ 2 :=
  Duhamel_loopMax_le_crude (d := 3) (L := 2) (W := 2) Matrix.isHermitian_zero (by simp) 2

/-- The same statement at `m = 0` is an equality: `L^{(0)} = card (Vtx 3 2 2) = (2 · 2)^3 = 64`
(the crude bound is sharp, so the instance is not vacuous). -/
theorem loopMax_zero_eq :
    RBM.Ind.loopMax 3 2 2 (0 : Matrix (Vtx 3 2 2) (Vtx 3 2 2) ℂ) Complex.I 0 = 64 := by
  apply le_antisymm
  · have h := Duhamel_loopMax_le_crude (d := 3) (L := 2) (W := 2)
      (M := (0 : Matrix (Vtx 3 2 2) (Vtx 3 2 2) ℂ)) Matrix.isHermitian_zero
      (z := Complex.I) (by simp) 0
    norm_num at h
    exact h
  · have h := RBM.Ind.norm_gloop_le_loopMax (d := 3) (L := 2) (W := 2)
      (H := (0 : Matrix (Vtx 3 2 2) (Vtx 3 2 2) ℂ)) (z := Complex.I)
      (⟨[], []⟩ : LoopIdx (Zd 3 2)) rfl rfl
    have h64 : loopL 3 2 2 (0 : Matrix (Vtx 3 2 2) (Vtx 3 2 2) ℂ) Complex.I
        (⟨[], []⟩ : LoopIdx (Zd 3 2)) = 64 := by
      change Matrix.trace (1 : Matrix (Vtx 3 2 2) (Vtx 3 2 2) ℂ) = 64
      rw [Matrix.trace_one, card_BlockIndex]
      norm_num
    rw [h64] at h
    norm_num at h
    exact h

/-- `Duhamel_loopMax_shift_le` at `d = 3`, `L = W = 2`, `M = 0`, `z = i`, `z' = 2 i`, `K = 1`,
`m = 2` (`‖G(i)‖ = 1`, `‖G(2 i)‖ = 1/2`, both `≤ K = 1`). -/
theorem loopMax_shift_le_inst :
    RBM.Ind.loopMax 3 2 2 (0 : Matrix (Vtx 3 2 2) (Vtx 3 2 2) ℂ) (2 * Complex.I) 2
      ≤ RBM.Ind.loopMax 3 2 2 (0 : Matrix (Vtx 3 2 2) (Vtx 3 2 2) ℂ) Complex.I 2
          + (((2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ)) ^ 3 * ((2 : ℕ) : ℝ) * (1 : ℝ) ^ 2
              * (‖2 * Complex.I - Complex.I‖ * (1 : ℝ) ^ 2) := by
  have hG : ∀ w : ℂ, 1 ≤ |w.im| →
      ‖green (0 : Matrix (Vtx 3 2 2) (Vtx 3 2 2) ℂ) w‖ ≤ 1 := fun w hw => by
    have h := norm_Gsig_le_inv_eta (H := (0 : Matrix (Vtx 3 2 2) (Vtx 3 2 2) ℂ))
      Matrix.isHermitian_zero (z := w) (η := 1) one_pos hw true
    rw [Duhamel_Gres_true] at h
    simpa using h
  exact Duhamel_loopMax_shift_le (d := 3) (L := 2) (W := 2)
    (M := (0 : Matrix (Vtx 3 2 2) (Vtx 3 2 2) ℂ)) Matrix.isHermitian_zero
    (z := Complex.I) (z' := 2 * Complex.I) (by simp) (by simp) (K := 1) le_rfl
    (hG Complex.I (by simp)) (hG (2 * Complex.I) (by norm_num)) 2

/-- The cut block of the one-edge loop is `G E_0 G` (`rest = []`). -/
theorem loopCut_loop1 :
    DuhamelLoopCut 3 2 2 (0 : Matrix (Vtx 3 2 2) (Vtx 3 2 2) ℂ) Complex.I
        (DuhamelA1Inst_loop1 3 2) 0
      = Gres (0 : Matrix (Vtx 3 2 2) (Vtx 3 2 2) ℂ) Complex.I true * Eblk 3 2 2 0
          * Gres (0 : Matrix (Vtx 3 2 2) (Vtx 3 2 2) ℂ) Complex.I true := by
  simp [DuhamelLoopCut, DuhamelA1Inst_loop1, gloopProd]

/-- `Duhamel_frobSq_loopCut_le` at `d = 3`, `L = W = 2`, `M = 0`, `z = i`, the one-edge loop,
`k = 0 < |I| = 1`. -/
theorem frobSq_loopCut_le_inst :
    ∑ p, ∑ q, ‖DuhamelLoopCut 3 2 2 (0 : Matrix (Vtx 3 2 2) (Vtx 3 2 2) ℂ) Complex.I
        (DuhamelA1Inst_loop1 3 2) 0 p q‖ ^ 2
      ≤ (|Complex.I.im|⁻¹) ^ 2 * RBM.Ind.loopMax 3 2 2 (0 : Matrix (Vtx 3 2 2) (Vtx 3 2 2) ℂ)
          Complex.I (2 * (DuhamelA1Inst_loop1 3 2).length) :=
  Duhamel_frobSq_loopCut_le Matrix.isHermitian_zero (by simp) (DuhamelA1Inst_loop1_wf 3 2)
    (by simp [DuhamelA1Inst_loop1, LoopIdx.length])

/-- `Duhamel_vGue_gradMat_le` at `sz0`, `n = 0`, `M = 0`, `z = i`, the one-edge loop. -/
theorem vGue_gradMat_le_inst :
    max (vGue sz0 0 (gradMat (fun M' : Matrix DuhamelA1Inst_Idx0 DuhamelA1Inst_Idx0 ℂ =>
          loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0) M') Complex.I
            (DuhamelA1Inst_loop1 3 (sz0.L 0))) 0) : ℝ)
        (vGue sz0 0 (-Complex.I • gradMat (fun M' : Matrix DuhamelA1Inst_Idx0 DuhamelA1Inst_Idx0 ℂ =>
          loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0) M') Complex.I
            (DuhamelA1Inst_loop1 3 (sz0.L 0))) 0) : ℝ)
      ≤ 8 * (((DuhamelA1Inst_loop1 3 (sz0.L 0)).length : ℝ) ^ 2 * (|Complex.I.im|⁻¹) ^ 2
          * RBM.Ind.loopMax 3 (sz0.L 0) (sz0.W 0)
              (blockMat 3 (sz0.L 0) (sz0.W 0) (0 : Matrix DuhamelA1Inst_Idx0 DuhamelA1Inst_Idx0 ℂ))
              Complex.I (2 * (DuhamelA1Inst_loop1 3 (sz0.L 0)).length)) :=
  Duhamel_vGue_gradMat_le (sz := sz0) (n := 0) (by simp) (DuhamelA1Inst_loop1_wf 3 _)
    Matrix.isHermitian_zero

/-- `Duhamel_contDiffAt_loop` at `d = 3`, `L = W = 2`, `M = 0`, `z = i`, the one-edge loop. -/
theorem contDiffAt_loop_inst :
    ContDiffAt ℝ 2 (fun M' : Matrix (Idx 3 2 2) (Idx 3 2 2) ℂ =>
      loopL 3 2 2 (blockMat 3 2 2 M') Complex.I (DuhamelA1Inst_loop1 3 2)) 0 :=
  Duhamel_contDiffAt_loop (z := Complex.I) (by simp) _ Matrix.isHermitian_zero

end RBM.Univ.GUEPhase.DuhamelA1Inst

end

#print axioms RBM.Univ.GUEPhase.Duhamel_vGue_le
#print axioms RBM.Univ.GUEPhase.DuhamelLoopCut
#print axioms RBM.Univ.GUEPhase.Duhamel_frobSq_loopCut_le
#print axioms RBM.Univ.GUEPhase.Duhamel_vGue_gradMat_le
#print axioms RBM.Univ.GUEPhase.Duhamel_loopMax_le_crude
#print axioms RBM.Univ.GUEPhase.Duhamel_loopMax_shift_le
#print axioms RBM.Univ.GUEPhase.Duhamel_contDiffAt_loop
#print axioms RBM.Univ.GUEPhase.DuhamelA1Inst.vGue_le_inst_value
#print axioms RBM.Univ.GUEPhase.DuhamelA1Inst.loopMax_le_crude_inst
#print axioms RBM.Univ.GUEPhase.DuhamelA1Inst.loopMax_zero_eq
#print axioms RBM.Univ.GUEPhase.DuhamelA1Inst.loopMax_shift_le_inst
#print axioms RBM.Univ.GUEPhase.DuhamelA1Inst.loopCut_loop1
#print axioms RBM.Univ.GUEPhase.DuhamelA1Inst.frobSq_loopCut_le_inst
#print axioms RBM.Univ.GUEPhase.DuhamelA1Inst.vGue_gradMat_le_inst
#print axioms RBM.Univ.GUEPhase.DuhamelA1Inst.contDiffAt_loop_inst
