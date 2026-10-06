/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAVocab
import RBM3D.Graph.LWWeightExp
import RBM3D.BA.Ward
import RBM3D.BA.FlowPins
import RBM3D.Gauss.BlockAnderson

/-!
# BA-L2a: the Stein layer of the block Anderson flow, `lanlw` (T2295)

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:359-372` (cited `B:line`; `lanlw`,
`(eq:BE)`, [yang2024Del, Lemma B.9]).  The law is the block Anderson flow `H_t = g₀ Ψ + √t V` with
`S^{(B)}(0) = I`, i.e. `PF d L W 0` (DECISIONS §57 (3)).  Design: T2161 (split P.9, row BA-L2).

## Contents (namespace `RBM.Graph`, private prefix `BAExpand_`)

1. **Vocabulary and pin** (`BAlwH` ... `BAlanlw`), copied verbatim from
   `docs/tickets/checks/T2295-check.lean` section 2.
2. **The Stein layer of the shifted resolvent** `G = (g₀Ψ + H_u - z)⁻¹` on `Sizes.SeqΩ`: `baGm`,
   `baG`, `baG_tame1`, `dhSample_baG`, `dhSample_baG_star`, `baVar`, `baPoly`, `baPoly_tame1`,
   `stein_baPoly`; the bridge to `PF d L W 0` through `lwWxSizes d L W 0 hL` (`baWx_baG`,
   `baWx_baPoly`, `baWx_dh`).
3. **`baLanlw_holds : ∀ d, BAlanlw d`**, unconditionally (`gaussIBP` discharged), with the Stein
   defect `BAExpand_defect` and the pathwise identity `BAExpand_defect_identity`.
4. Compiled instances (`RBM.Graph.BAExpandInst`): (I1) the vocabulary and the Stein layer at
   `d = 3`, (I2) `baLanlw_holds` at `t = 0` and at a point with every hypothesis discharged.

Not in this file (cut BA-L2a1 / BA-L2a2 of the ticket, `Over 1500 at 1b`): `lanlw` as a graph
operation on `BAGraph` (target 3, instances (I3), (I4)).
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Graph

open RBM RBM.Gauss RBM.Green

/-! ## 1. Vocabulary and pin (verbatim from the check file, section 2) -/


section LWBA

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- `H_t = g₀ Ψ + √t V` at a sample `ω` of `PF d L W 0` (`(MBM)`, `1_2:685`; law `S^{(B)}(0) = I`, §57 (3)). -/
def BAlwH (g0 t : ℝ) (ω : Ω d L W) : Matrix (Idx d L W) (Idx d L W) ℂ :=
  (g0 : ℂ) • PsiI d L W + Hflow d L W t ω

/-- `M = (g₀ Ψ - E - m)⁻¹` on the fine lattice (`(def_G0)`, `1_2:631`). -/
def BAlwM (g0 E : ℝ) (m : ℂ) : Matrix (Idx d L W) (Idx d L W) ℂ := Mres ((g0 : ℂ) • PsiI d L W) (E : ℂ) m

/-- `G_{xy}` of the flow, `z_t = E + (1 - t) m`. -/
def BAlwG (g0 E t : ℝ) (m : ℂ) (ω : Ω d L W) (x y : Idx d L W) : ℂ :=
  Gres (BAlwH d L W g0 t ω) (ztOf m E t) true x y

/-- `Ǧ_{xy} = G_{xy} - M_{xy}`. -/
def BAlwGc (g0 E t : ℝ) (m : ℂ) (ω : Ω d L W) (x y : Idx d L W) : ℂ :=
  BAlwG d L W g0 E t m ω x y - BAlwM d L W g0 E m x y

/-- `S_{αβ} = t W^{-d} 1([α] = [β])`: the variance of `√t V` (`S^{(B)}(0) = I`). -/
def BAlwS (t : ℝ) (x y : Idx d L W) : ℂ := (t : ℂ) * svarF d L W 0 x y

/-- `M^+_{xy} = M_{xy} M_{yx}` (`B:388`). Shared with BA-L2b/L2c. -/
def BAlwMp (g0 E : ℝ) (m : ℂ) : Matrix (Idx d L W) (Idx d L W) ℂ :=
  Matrix.of fun x y => BAlwM d L W g0 E m x y * BAlwM d L W g0 E m y x

/-- `1 + M^+ S^+ = (1 - M^+ S)⁻¹` (`(eq:def-Spm)`, `7_8:110`). Shared with BA-L2b/L2c. -/
def BAlwW (g0 E t : ℝ) (m : ℂ) : Matrix (Idx d L W) (Idx d L W) ℂ :=
  Ring.inverse (1 - BAlwMp d L W g0 E m * Matrix.of (BAlwS d L W t))

/-- `f(G)` of the expansions: a resolvent polynomial at the flow matrix. -/
def BAlwf (g0 E t : ℝ) (m : ℂ) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) (ω : Ω d L W) : ℂ :=
  LWPins_resPoly d L W (ztOf m E t) P (BAlwH d L W g0 t ω)

/-- `∂_{h_{αw}} f(G)`. -/
def BAlwdf (g0 E t : ℝ) (m : ℂ) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) (ω : Ω d L W)
    (α w : Idx d L W) : ℂ :=
  LWPins_dH (LWPins_resPoly d L W (ztOf m E t) P) (BAlwH d L W g0 t ω) α w

end LWBA

section LWBAPins

variable (d L W : ℕ) [NeZero L] [NeZero W] (g0 E t : ℝ) (m : ℂ)
  (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ)

/-- Left side of `lanlw`: `Ǧ_{xy} f` (`B:359-372`, [yang2024Del, Lemma B.9]). -/
def BAlanlwL (x y : Idx d L W) (ω : Ω d L W) : ℂ :=
  BAlwGc d L W g0 E t m ω x y * BAlwf d L W g0 E t m P ω

/-- Right side of `lanlw` before `𝔼`: `Σ_{α,β} M_{xα} S_{αβ} Ǧ_{ββ} G_{αy} f - Σ_{α,β} M_{xα} S_{αβ} G_{βy} ∂_{h_{βα}} f`. -/
def BAlanlwR (x y : Idx d L W) (ω : Ω d L W) : ℂ :=
  (∑ α, ∑ β, BAlwM d L W g0 E m x α * BAlwS d L W t α β * BAlwGc d L W g0 E t m ω β β *
      BAlwG d L W g0 E t m ω α y * BAlwf d L W g0 E t m P ω -
    ∑ α, ∑ β, BAlwM d L W g0 E m x α * BAlwS d L W t α β * BAlwG d L W g0 E t m ω β y *
      BAlwdf d L W g0 E t m P ω β α)

variable {d L W g0 E t m P}

/-- **`lanlw`** (`B:359-372`, [yang2024Del, Lemma B.9]): `𝔼[BAlanlwL] = 𝔼[BAlanlwR]` for every resolvent polynomial `f`
over the BA law `PF d L W 0`.  Needs `(self_m)` (`M_{ββ} = m`; false for an arbitrary `m`, T2161 report (b.7)).
Registry: proved (T2295). -/
def BAlanlw (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (E : ℂ) m →
    0 ≤ t → t < 1 →
    ∀ (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) (x y : Idx d L W),
      ∫ ω, BAlanlwL d L W g0 E t m P x y ω ∂(PF d L W 0) = ∫ ω, BAlanlwR d L W g0 E t m P x y ω ∂(PF d L W 0)

end LWBAPins


/-! ## 2. The Stein layer of the shifted resolvent `G = (g₀ Ψ + H_u - z)⁻¹`

The twins of the merged `lwGm`, `lwG`, `dhSample_lwG`, `lwG_tame1`, `lwPoly`, `lwPoly_tame1` (`Graph/LWStein.lean:469-967`),
with `H_u` replaced by `g₀ Ψ + H_u`: the shift is a constant matrix, so every calculus step is the merged one. -/

section BAStein

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

/-- `g₀ Ψ + H_u` at a sample of the common space: the block Anderson flow matrix at size `n` (`(MBM)`, `1_2:686`). -/
def BAExpand_Hm (g0 u : ℝ) (ω : Sizes.SeqΩ sz) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  (g0 : ℂ) • PsiI d (sz.L n) (sz.W n) + sz.seqHflow n u ω

theorem BAExpand_Hm_isHermitian (g0 u : ℝ) (ω : Sizes.SeqΩ sz) : (BAExpand_Hm sz n g0 u ω).IsHermitian := by
  have h1 : ((g0 : ℂ) • PsiI d (sz.L n) (sz.W n)).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_smul, (PsiI_isHermitian d (sz.L n) (sz.W n)).eq,
      show star (g0 : ℂ) = (g0 : ℂ) from Complex.conj_ofReal _]
  exact h1.add (Sizes.seqHflow_isHermitian sz n u ω)

/-- The resolvent matrix `G = (g₀Ψ + H_u - z)⁻¹` of the block Anderson flow, as a function of the sample. -/
def baGm (g0 : ℝ) (z : ℂ) (u : ℝ) (ω : Sizes.SeqΩ sz) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  Gres (BAExpand_Hm sz n g0 u ω) z true

/-- The entry `G_{ij}` of the resolvent of the block Anderson flow. -/
def baG (g0 : ℝ) (z : ℂ) (u : ℝ) (i j : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) : ℂ :=
  baGm sz n g0 z u ω i j

/-- The derivative of `G_{ij}` along one real coordinate: `∂_c G_{ij} = -√u (G D_c G)_{ij}`
(the twin of `lwStein_hasDerivAt_lwG`; the shift `g₀ Ψ` is constant). -/
theorem BAExpand_hasDerivAt_baG {z : ℂ} (hz : z.im ≠ 0) (g0 u : ℝ) (ω : Sizes.SeqΩ sz)
    (c : CoordF d (sz.L n) (sz.W n)) (i j : Idx d (sz.L n) (sz.W n)) :
    HasDerivAt (fun t : ℝ => baG sz n g0 z u i j (Function.update ω ⟨n, c⟩ t))
      (-((Real.sqrt u : ℂ) * (baGm sz n g0 z u ω * coordinateMatrix d (sz.L n) (sz.W n) c *
        baGm sz n g0 z u ω) i j)) (ω ⟨n, c⟩) := by
  have hU : IsUnit (BAExpand_Hm sz n g0 u ω - z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) :=
    isUnit_sub_smul_of_isHermitian (BAExpand_Hm_isHermitian sz n g0 u ω) hz
  have h := lwStein_hasDerivAt_inv hU (ω ⟨n, c⟩) i j
    (B := (Real.sqrt u : ℂ) • coordinateMatrix d (sz.L n) (sz.W n) c)
  have hfun : (fun t : ℝ => baG sz n g0 z u i j (Function.update ω ⟨n, c⟩ t)) = fun t : ℝ =>
      Ring.inverse ((BAExpand_Hm sz n g0 u ω - z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) +
        (t - ω ⟨n, c⟩) • ((Real.sqrt u : ℂ) • coordinateMatrix d (sz.L n) (sz.W n) c)) i j := by
    funext t
    simp only [baG, baGm, Gres, ite_true, BAExpand_Hm, lwStein_seqHflow_update]
    rw [show (g0 : ℂ) • PsiI d (sz.L n) (sz.W n) + (sz.seqHflow n u ω +
        (t - ω ⟨n, c⟩) • ((Real.sqrt u : ℂ) • coordinateMatrix d (sz.L n) (sz.W n) c)) -
        z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =
        ((g0 : ℂ) • PsiI d (sz.L n) (sz.W n) + sz.seqHflow n u ω -
          z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) +
        (t - ω ⟨n, c⟩) • ((Real.sqrt u : ℂ) • coordinateMatrix d (sz.L n) (sz.W n) c) by abel]
  rw [hfun]
  refine h.congr_deriv ?_
  simp only [baGm, Gres, ite_true, BAExpand_Hm, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]

theorem BAExpand_partial_baG {z : ℂ} (hz : z.im ≠ 0) (g0 u : ℝ) (ω : Sizes.SeqΩ sz)
    (c : CoordF d (sz.L n) (sz.W n)) (i j : Idx d (sz.L n) (sz.W n)) :
    lwPartial sz n c (baG sz n g0 z u i j) ω =
      -((Real.sqrt u : ℂ) * (baGm sz n g0 z u ω * coordinateMatrix d (sz.L n) (sz.W n) c *
        baGm sz n g0 z u ω) i j) :=
  (BAExpand_hasDerivAt_baG sz n hz g0 u ω c i j).deriv

variable {sz n}

/-- **`∂_{h_{αw}}` from the partials** (the generic core of `dhSample_lwG`): if every real partial of `F` at `ω`
is `-√u (Gm D_c Gm)_{ij}`, then `∂_{h_{αw}} F = -Gm_{iα} Gm_{wj}`. -/
theorem BAExpand_dh_of_partial {u : ℝ} (hu : 0 < u) (α w i j : Idx d (sz.L n) (sz.W n))
    (F : Sizes.SeqΩ sz → ℂ) (ω : Sizes.SeqΩ sz)
    (Gm : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (h : ∀ c, lwPartial sz n c F ω =
      -((Real.sqrt u : ℂ) * (Gm * coordinateMatrix d (sz.L n) (sz.W n) c * Gm) i j)) :
    dhSample sz n u α w F ω = -(Gm i α * Gm w j) := by
  have hs := lwStein_sqrt_ne hu
  have h2s : (2 * (Real.sqrt u : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hs
  unfold dhSample
  rcases idxKey_lt_or_eq_or_lt d (sz.L n) (sz.W n) α w with hk | rfl | hk
  · rw [ite_eq_left hk, h, h, lwStein_coordMat_true_lt _ _ _ _ _ hk, lwStein_coordMat_false_lt _ _ _ _ _ hk]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, lwStein_mul_single_mul_apply]
    rw [inv_mul_eq_iff_eq_mul₀ h2s]
    linear_combination ((Real.sqrt u : ℂ) * (Gm i α * Gm w j - Gm i w * Gm α j)) * Complex.I_sq
  · rw [ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _), h, lwStein_coordMat_diag]
    simp only [lwStein_mul_single_mul_apply]
    field_simp
  · rw [ite_eq_right hk.not_gt, ite_eq_left hk, h, h, lwStein_coordMat_true_lt _ _ _ _ _ hk,
      lwStein_coordMat_false_lt _ _ _ _ _ hk]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, lwStein_mul_single_mul_apply]
    rw [inv_mul_eq_iff_eq_mul₀ h2s]
    linear_combination ((Real.sqrt u : ℂ) * (Gm i α * Gm w j - Gm i w * Gm α j)) * Complex.I_sq

/-- **`∂_{h_{αw}} \bar F`** (the generic core of `dhSample_lwG_star`). -/
theorem BAExpand_dh_star_of_partial {u : ℝ} (hu : 0 < u) (α w i j : Idx d (sz.L n) (sz.W n))
    (F : Sizes.SeqΩ sz → ℂ) (ω : Sizes.SeqΩ sz)
    (Gm : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (h : ∀ c, lwPartial sz n c F ω =
      -((Real.sqrt u : ℂ) * (Gm * coordinateMatrix d (sz.L n) (sz.W n) c * Gm) i j)) :
    dhSample sz n u α w (fun ω => star (F ω)) ω = -star (Gm i w * Gm α j) := by
  have hs := lwStein_sqrt_ne hu
  have h2s : (2 * (Real.sqrt u : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hs
  unfold dhSample
  simp only [lwStein_partial_star]
  rcases idxKey_lt_or_eq_or_lt d (sz.L n) (sz.W n) α w with hk | rfl | hk
  · rw [ite_eq_left hk, h, h, lwStein_coordMat_true_lt _ _ _ _ _ hk, lwStein_coordMat_false_lt _ _ _ _ _ hk]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, lwStein_mul_single_mul_apply]
    simp only [star_neg, star_mul', star_add, Complex.star_def, Complex.conj_ofReal, Complex.conj_I,
      one_mul]
    rw [inv_mul_eq_iff_eq_mul₀ h2s]
    linear_combination ((Real.sqrt u : ℂ) * ((starRingEnd ℂ) (Gm i w) * (starRingEnd ℂ) (Gm α j)
      - (starRingEnd ℂ) (Gm i α) * (starRingEnd ℂ) (Gm w j))) * Complex.I_sq
  · rw [ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _), h, lwStein_coordMat_diag]
    simp only [lwStein_mul_single_mul_apply, star_neg, star_mul', Complex.star_def,
      Complex.conj_ofReal, one_mul]
    field_simp
  · rw [ite_eq_right hk.not_gt, ite_eq_left hk, h, h, lwStein_coordMat_true_lt _ _ _ _ _ hk,
      lwStein_coordMat_false_lt _ _ _ _ _ hk]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, lwStein_mul_single_mul_apply]
    simp only [star_neg, star_mul', star_add, Complex.star_def, Complex.conj_ofReal, Complex.conj_I,
      one_mul]
    rw [inv_mul_eq_iff_eq_mul₀ h2s]
    linear_combination ((Real.sqrt u : ℂ) * ((starRingEnd ℂ) (Gm i w) * (starRingEnd ℂ) (Gm α j)
      - (starRingEnd ℂ) (Gm i α) * (starRingEnd ℂ) (Gm w j))) * Complex.I_sq

/-- **`∂_{h_{αw}} G_{ij} = -G_{iα} G_{wj}`** for the shifted resolvent (`dhSample_lwG` for `g₀ Ψ + H_u`),
`0 < u`, `Im z ≠ 0`. -/
theorem dhSample_baG {z : ℂ} (hz : z.im ≠ 0) {u : ℝ} (hu : 0 < u) (g0 : ℝ)
    (α w i j : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    dhSample sz n u α w (baG sz n g0 z u i j) ω = -(baG sz n g0 z u i α ω * baG sz n g0 z u w j ω) :=
  BAExpand_dh_of_partial hu α w i j _ ω _ (fun c => BAExpand_partial_baG sz n hz g0 u ω c i j)

/-- **`∂_{h_{αw}} \bar G_{ij} = -\overline{G_{iw} G_{αj}}`** for the shifted resolvent. -/
theorem dhSample_baG_star {z : ℂ} (hz : z.im ≠ 0) {u : ℝ} (hu : 0 < u) (g0 : ℝ)
    (α w i j : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    dhSample sz n u α w (fun ω => star (baG sz n g0 z u i j ω)) ω =
      -star (baG sz n g0 z u i w ω * baG sz n g0 z u α j ω) :=
  BAExpand_dh_star_of_partial hu α w i j _ ω _ (fun c => BAExpand_partial_baG sz n hz g0 u ω c i j)

end BAStein

section BATame

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

theorem BAExpand_continuous_Hm (g0 u : ℝ) : Continuous (BAExpand_Hm sz n g0 u) :=
  continuous_const.add (lwStein_continuous_seqHflow sz n u)

/-- The shifted resolvent is a continuous function of the sample (`Im z ≠ 0`). -/
theorem BAExpand_continuous_baGm {z : ℂ} (hz : z.im ≠ 0) (g0 u : ℝ) : Continuous (baGm sz n g0 z u) :=
  continuous_green_of_isHermitian (BAExpand_continuous_Hm sz n g0 u)
    (fun ω => BAExpand_Hm_isHermitian sz n g0 u ω) hz

/-- The entries of the shifted resolvent obey the envelope `|G_{ij}| ≤ |Im z|⁻¹` at every sample. -/
theorem BAExpand_norm_baG_le {z : ℂ} (hz : z.im ≠ 0) (g0 u : ℝ) (i j : Idx d (sz.L n) (sz.W n))
    (ω : Sizes.SeqΩ sz) : ‖baG sz n g0 z u i j ω‖ ≤ |z.im|⁻¹ := by
  simpa [baG, baGm, Gres] using norm_inverse_entry_le (BAExpand_Hm_isHermitian sz n g0 u ω) hz i j

/-- An entry of the shifted resolvent is tame: continuous, finitely dependent, bounded by `|Im z|⁻¹`. -/
theorem BAExpand_tame_baG {z : ℂ} (hz : z.im ≠ 0) (g0 u : ℝ) (i j : Idx d (sz.L n) (sz.W n)) :
    Tame sz (baG sz n g0 z u i j) :=
  Tame.ofBdd (((continuous_apply j).comp ((continuous_apply i).comp (BAExpand_continuous_baGm sz n hz g0 u))))
    (lwStein_finDep_of_slice sz n _ fun ω ω' h => by
      have : sz.seqHflow n u ω = sz.seqHflow n u ω' := by
        unfold Sizes.seqHflow Sizes.seqXmat; rw [h]
      simp only [baG, baGm, BAExpand_Hm, this])
    (BAExpand_norm_baG_le sz n hz g0 u i j)

theorem BAExpand_tame_GDG {z : ℂ} (hz : z.im ≠ 0) (g0 u : ℝ)
    (D : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (i j : Idx d (sz.L n) (sz.W n)) :
    Tame sz (fun ω => (baGm sz n g0 z u ω * D * baGm sz n g0 z u ω) i j) := by
  have h : (fun ω => (baGm sz n g0 z u ω * D * baGm sz n g0 z u ω) i j) = fun ω =>
      ∑ k, (∑ l, baG sz n g0 z u i l ω * D l k) * baG sz n g0 z u k j ω := by
    funext ω
    simp [Matrix.mul_apply, baG]
  rw [h]
  exact Tame.sum _ fun k _ => (Tame.sum _ fun l _ =>
    (BAExpand_tame_baG sz n hz g0 u i l).mul (Tame.const _)).mul (BAExpand_tame_baG sz n hz g0 u k j)

variable {sz n}

/-- A shifted resolvent entry `G_{ij}` is `C¹`-tame (`Im z ≠ 0`). -/
theorem baG_tame1 {z : ℂ} (hz : z.im ≠ 0) (g0 u : ℝ) (i j : Idx d (sz.L n) (sz.W n)) :
    Tame1 sz n (baG sz n g0 z u i j) where
  tame := BAExpand_tame_baG sz n hz g0 u i j
  diff := fun c ω => (BAExpand_hasDerivAt_baG sz n hz g0 u ω c i j).differentiableAt
  tame_partial := fun c => by
    have : lwPartial sz n c (baG sz n g0 z u i j) = fun ω =>
        -((Real.sqrt u : ℂ) * (baGm sz n g0 z u ω * coordinateMatrix d (sz.L n) (sz.W n) c *
          baGm sz n g0 z u ω) i j) := funext (BAExpand_partial_baG sz n hz g0 u · c i j)
    rw [this]
    exact ((Tame.const _).mul (BAExpand_tame_GDG sz n hz g0 u _ i j)).neg

variable (sz n) in
/-- **A resolvent polynomial of the block Anderson flow**: a polynomial in the entries `G_{ij}` (variable `(i, j, true)`)
and `\bar G_{ij}` (variable `(i, j, false)`) of `G = (g₀Ψ + H_u - z)⁻¹`, evaluated at the sample (the twin of `lwVar`). -/
def baVar (g0 : ℝ) (z : ℂ) (u : ℝ) (v : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool)
    (ω : Sizes.SeqΩ sz) : ℂ :=
  if v.2.2 then baG sz n g0 z u v.1 v.2.1 ω else star (baG sz n g0 z u v.1 v.2.1 ω)

variable (sz n) in
/-- The twin of `lwPoly`. -/
def baPoly (g0 : ℝ) (z : ℂ) (u : ℝ)
    (P : MvPolynomial (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool) ℂ)
    (ω : Sizes.SeqΩ sz) : ℂ :=
  MvPolynomial.eval (fun v => baVar sz n g0 z u v ω) P

theorem BAExpand_baVar_tame1 {z : ℂ} (hz : z.im ≠ 0) (g0 u : ℝ)
    (v : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool) :
    Tame1 sz n (baVar sz n g0 z u v) := by
  unfold baVar
  cases h : v.2.2
  · simpa using (baG_tame1 (sz := sz) (n := n) hz g0 u v.1 v.2.1).conj
  · simpa using baG_tame1 (sz := sz) (n := n) hz g0 u v.1 v.2.1

/-- **A resolvent polynomial of the block Anderson flow is `C¹`-tame** (the twin of `lwPoly_tame1`). -/
theorem baPoly_tame1 {z : ℂ} (hz : z.im ≠ 0) (g0 u : ℝ)
    (P : MvPolynomial (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool) ℂ) :
    Tame1 sz n (baPoly sz n g0 z u P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    convert Tame1.const (sz := sz) (n := n) a using 1
    funext ω; simp [baPoly]
  | add p q hp hq =>
    convert hp.add hq using 1
    funext ω; simp [baPoly, map_add]
  | mul_X p v hp =>
    convert hp.mul (BAExpand_baVar_tame1 hz g0 u v) using 1
    funext ω; simp [baPoly, map_mul, MvPolynomial.eval_X]

/-- **Stein for resolvent polynomials of the block Anderson flow**: `GaussIBP sz` is the only input. -/
theorem stein_baPoly (hG : GaussIBP sz) {z : ℂ} (hz : z.im ≠ 0) (g0 : ℝ) {u : ℝ} (hu : 0 ≤ u)
    (P : MvPolynomial (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool) ℂ)
    (α w : Idx d (sz.L n) (sz.W n)) :
    ∫ ω, sz.seqHflow n u ω w α * baPoly sz n g0 z u P ω ∂(Sizes.seqP sz) =
      lwS sz n u w α * ∫ ω, dhSample sz n u α w (baPoly sz n g0 z u P) ω ∂(Sizes.seqP sz) :=
  stein_sample hG (baPoly_tame1 hz g0 u P) hu α w

end BATame

/-! ### The bridge to the one-size law `PF d L W 0`

The twins of `lwWx_lwG`, `lwWx_lwPoly_eval`, `lwWx_dh_var`, `lwWx_hasDerivAt`, `lwWx_dh` (`Graph/LWWeightExp.lean:70-271`)
at the constant size sequence `lwWxSizes d L W 0 hL` (the coupling of the law is `0`: `S^{(B)}(0) = I`, DECISIONS §57 (3)). -/

section BABridge

variable {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L)

/-- The shifted flow matrix of the sequence space is `BAlwH` of the one-size sample. -/
theorem BAExpand_Hm_eq (g0 u : ℝ) (ω : Sizes.SeqΩ (lwWxSizes d L W 0 hL)) :
    BAExpand_Hm (lwWxSizes d L W 0 hL) 0 g0 u ω =
      (g0 : ℂ) • PsiI d L W + Hflow d L W u (Sizes.slice (lwWxSizes d L W 0 hL) 0 ω) := rfl

/-- (b) the resolvent entry of the one-size law is that of the sequence-space block Anderson flow. -/
theorem baWx_baG (g0 E t : ℝ) (m : ℂ) (ω : Sizes.SeqΩ (lwWxSizes d L W 0 hL)) (x y : Idx d L W) :
    baG (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t x y ω =
      BAlwG d L W g0 E t m (Sizes.slice (lwWxSizes d L W 0 hL) 0 ω) x y := rfl

/-- (c) the resolvent polynomial of the sequence space at the renamed `P` is `P` at the resolvents `Gres` of the
shifted flow matrix (any `z`, `u`). -/
theorem BAExpand_bridge_baPoly_eval (g0 : ℝ) (z : ℂ) (u : ℝ) (ω : Sizes.SeqΩ (lwWxSizes d L W 0 hL))
    (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) :
    baPoly (lwWxSizes d L W 0 hL) 0 g0 z u (lwWxRename d L W P) ω =
      MvPolynomial.eval (fun v => Gres ((g0 : ℂ) • PsiI d L W +
        Hflow d L W u (Sizes.slice (lwWxSizes d L W 0 hL) 0 ω)) z v.1 v.2.1 v.2.2) P := by
  unfold baPoly lwWxRename
  rw [MvPolynomial.eval_rename]
  refine congrArg (fun F => MvPolynomial.eval F P) (funext fun v => ?_)
  rcases v with ⟨σ, a, b⟩
  have hH := BAExpand_Hm_isHermitian (lwWxSizes d L W 0 hL) 0 g0 u ω
  cases σ
  · simp only [Function.comp_apply, lwWxVar, baVar, baG, baGm, Bool.false_eq_true, ↓reduceIte]
    exact (lwWx_Gres_false hH z a b).symm
  · rfl

/-- (c) `baPoly sz 0 g₀ z_t t P' ω = BAlwf P (slice ω)`. -/
theorem baWx_baPoly (g0 E t : ℝ) (m : ℂ) (ω : Sizes.SeqΩ (lwWxSizes d L W 0 hL))
    (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) :
    baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P) ω =
      BAlwf d L W g0 E t m P (Sizes.slice (lwWxSizes d L W 0 hL) 0 ω) :=
  BAExpand_bridge_baPoly_eval hL g0 (ztOf m E t) t ω P

/-- (d) the derivative of a variable: `∂_{h_{αw}}` of `baVar (lwWxVar v)` is the matrix-level derivative
`-G^σ_{aα} G^σ_{wb}` of the entry `(σ, a, b)` of `Gres` of the shifted flow matrix. -/
theorem BAExpand_bridge_dh_var {z : ℂ} (hz : z.im ≠ 0) {u : ℝ} (hu : 0 < u) (g0 : ℝ) (α w : Idx d L W)
    (ω : Sizes.SeqΩ (lwWxSizes d L W 0 hL)) (v : Bool × Idx d L W × Idx d L W) :
    dhSample (lwWxSizes d L W 0 hL) 0 u α w (baVar (lwWxSizes d L W 0 hL) 0 g0 z u (lwWxVar d L W v)) ω =
      -(Gres ((g0 : ℂ) • PsiI d L W + Hflow d L W u (Sizes.slice (lwWxSizes d L W 0 hL) 0 ω)) z v.1 v.2.1 α *
        Gres ((g0 : ℂ) • PsiI d L W + Hflow d L W u (Sizes.slice (lwWxSizes d L W 0 hL) 0 ω)) z v.1 w v.2.2) := by
  rcases v with ⟨σ, a, b⟩
  have hH : ((g0 : ℂ) • PsiI d L W + Hflow d L W u (Sizes.slice (lwWxSizes d L W 0 hL) 0 ω)).IsHermitian :=
    BAExpand_Hm_isHermitian (lwWxSizes d L W 0 hL) 0 g0 u ω
  cases σ
  · have h1 : dhSample (lwWxSizes d L W 0 hL) 0 u α w
        (baVar (lwWxSizes d L W 0 hL) 0 g0 z u (lwWxVar d L W (false, a, b))) ω =
        dhSample (lwWxSizes d L W 0 hL) 0 u α w
          (fun ω => star (baG (lwWxSizes d L W 0 hL) 0 g0 z u b a ω)) ω := by
      rfl
    rw [h1, dhSample_baG_star hz hu g0 α w b a ω]
    simp only [baG, baGm, lwWx_Gres_false hH z, star_mul']
    rw [mul_comm]
    rfl
  · have h1 : dhSample (lwWxSizes d L W 0 hL) 0 u α w
        (baVar (lwWxSizes d L W 0 hL) 0 g0 z u (lwWxVar d L W (true, a, b))) ω =
        dhSample (lwWxSizes d L W 0 hL) 0 u α w (baG (lwWxSizes d L W 0 hL) 0 g0 z u a b) ω := by
      rfl
    rw [h1, dhSample_baG hz hu g0 α w a b ω]
    rfl

/-- (d) **the derivatives agree**: for a resolvent polynomial `P`, the map `s ↦ f_P(H' + s E_{αw})` (`H' = g₀Ψ + H_u`)
has at `s = 0` the derivative `∂_{h_{αw}}` of `baPoly (P')` (`dhSample`). -/
theorem BAExpand_bridge_hasDerivAt {z : ℂ} (hz : z.im ≠ 0) {u : ℝ} (hu : 0 < u) (g0 : ℝ) (α w : Idx d L W)
    (ω : Sizes.SeqΩ (lwWxSizes d L W 0 hL)) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) :
    HasDerivAt (fun s : ℂ => MvPolynomial.eval (fun v => Gres ((g0 : ℂ) • PsiI d L W +
        Hflow d L W u (Sizes.slice (lwWxSizes d L W 0 hL) 0 ω) + s • single α w (1 : ℂ)) z v.1 v.2.1 v.2.2) P)
      (dhSample (lwWxSizes d L W 0 hL) 0 u α w (baPoly (lwWxSizes d L W 0 hL) 0 g0 z u (lwWxRename d L W P)) ω) 0 := by
  have hH : ((g0 : ℂ) • PsiI d L W + Hflow d L W u (Sizes.slice (lwWxSizes d L W 0 hL) 0 ω)).IsHermitian :=
    BAExpand_Hm_isHermitian (lwWxSizes d L W 0 hL) 0 g0 u ω
  have hval : ∀ P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ,
      MvPolynomial.eval (fun v => Gres ((g0 : ℂ) • PsiI d L W +
        Hflow d L W u (Sizes.slice (lwWxSizes d L W 0 hL) 0 ω) + (0 : ℂ) • single α w (1 : ℂ)) z v.1 v.2.1 v.2.2) P =
        baPoly (lwWxSizes d L W 0 hL) 0 g0 z u (lwWxRename d L W P) ω := by
    intro P
    simp only [zero_smul, add_zero]
    exact (BAExpand_bridge_baPoly_eval hL g0 z u ω P).symm
  have ht1 := fun P => baPoly_tame1 (sz := lwWxSizes d L W 0 hL) (n := 0) hz g0 u (lwWxRename d L W P)
  induction P using MvPolynomial.induction_on with
  | C a =>
    have e : baPoly (lwWxSizes d L W 0 hL) 0 g0 z u (lwWxRename d L W (MvPolynomial.C a)) = fun _ => a := by
      funext ω'
      simp [baPoly, lwWxRename]
    rw [e, lwStein_dh_const]
    exact (hasDerivAt_const (0 : ℂ) a).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => by simp)
  | add p q hp hq =>
    have e : baPoly (lwWxSizes d L W 0 hL) 0 g0 z u (lwWxRename d L W (p + q)) = fun ω' =>
        baPoly (lwWxSizes d L W 0 hL) 0 g0 z u (lwWxRename d L W p) ω' +
          baPoly (lwWxSizes d L W 0 hL) 0 g0 z u (lwWxRename d L W q) ω' := by
      funext ω'
      simp [baPoly, lwWxRename]
    rw [e, lwStein_dh_add (ht1 p) (ht1 q)]
    exact (hp.add hq).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by simp)
  | mul_X p v hp =>
    have e : baPoly (lwWxSizes d L W 0 hL) 0 g0 z u (lwWxRename d L W (p * MvPolynomial.X v)) = fun ω' =>
        baPoly (lwWxSizes d L W 0 hL) 0 g0 z u (lwWxRename d L W p) ω' *
          baVar (lwWxSizes d L W 0 hL) 0 g0 z u (lwWxVar d L W v) ω' := by
      funext ω'
      simp [baPoly, lwWxRename]
    rw [e, lwStein_dh_mul (ht1 p) (BAExpand_baVar_tame1 hz g0 u _), BAExpand_bridge_dh_var hL hz hu g0 α w ω v]
    have hv := lwWx_hasDerivAt_Gres hH hz v.1 α w v.2.1 v.2.2
    have hm := hp.mul hv
    refine (hm.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    · have hvar : Gres ((g0 : ℂ) • PsiI d L W + Hflow d L W u (Sizes.slice (lwWxSizes d L W 0 hL) 0 ω) +
          (0 : ℂ) • single α w (1 : ℂ)) z v.1 v.2.1 v.2.2 =
          baVar (lwWxSizes d L W 0 hL) 0 g0 z u (lwWxVar d L W v) ω := by
        have := hval (MvPolynomial.X v)
        simpa [baPoly, lwWxRename, MvPolynomial.eval_X, MvPolynomial.rename_X] using this
      rw [hval p, hvar]
    · simp

/-- (d) **the derivatives agree** (the matrix-level `BAlwdf` against `dhSample`), for `0 < t` and `Im z ≠ 0`. -/
theorem baWx_dh {z : ℂ} (hz : z.im ≠ 0) {u : ℝ} (hu : 0 < u) (g0 : ℝ) (α w : Idx d L W)
    (ω : Sizes.SeqΩ (lwWxSizes d L W 0 hL)) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) :
    dhSample (lwWxSizes d L W 0 hL) 0 u α w (baPoly (lwWxSizes d L W 0 hL) 0 g0 z u (lwWxRename d L W P)) ω =
      LWPins_dH (LWPins_resPoly d L W z P) ((g0 : ℂ) • PsiI d L W +
        Hflow d L W u (Sizes.slice (lwWxSizes d L W 0 hL) 0 ω)) α w :=
  (BAExpand_bridge_hasDerivAt hL hz hu g0 α w ω P).deriv.symm

end BABridge

/-! ## 3. `lanlw` (`B:359-372`): the pathwise identity and the Stein identity

`(M1)`: `Ǧ = -M (V_t + t m) G` (`G⁻¹ - M⁻¹ = V_t + t m`, `z_t = E + (1 - t) m`); `(M2)`: Stein; `(M3)`: `Σ_β S_{αβ} = t`
and `M_{ββ} = m`.  The identity is pathwise with the Stein defect `Z_α` of each row; `E Z_α = 0` is the Stein identity. -/

section BAAlg

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- (M1): `A⁻¹ - B⁻¹ = -B⁻¹ (A - B) A⁻¹` for invertible `A`, `B`. -/
theorem BAExpand_inv_sub_inv {A B : Matrix ι ι ℂ} (hA : IsUnit A) (hB : IsUnit B) :
    Ring.inverse A - Ring.inverse B = -(Ring.inverse B * (A - B) * Ring.inverse A) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Ring.inverse_mul_cancel _ hB, Matrix.mul_assoc, Ring.mul_inverse_cancel _ hA,
    Matrix.mul_one, Matrix.one_mul]
  abel

/-- The Stein defect of the row `α` of `lanlw` for `Ǧ_{xy} f`: `Z_α = Σ_β (H_{αβ} G_{βy} f - S_{αβ} ∂_{h_{βα}}(G_{βy} f))`
with `∂_{h_{βα}} G_{βy} = -G_{ββ} G_{αy}` inserted; `f` and the array `df β α = ∂_{h_{βα}} f` are data. -/
def BAExpand_defect (G H S : Matrix ι ι ℂ) (f : ℂ) (df : ι → ι → ℂ) (y α : ι) : ℂ :=
  ∑ β, H α β * (G β y * f) - ∑ β, S α β * (-(G β β * G α y) * f + G β y * df β α)

/-- **`lanlw` is the Stein identity plus linear algebra**: for every `f`, `df`, the difference of the two sides of `lanlw` is,
pathwise and exactly, `-Σ_α M_{xα} Z_α`.  Hypotheses: `G - M = -M (H + t m) G`, `M_{ββ} = m` and the rows of `S` sum to `t`. -/
theorem BAExpand_defect_identity (G M H S : Matrix ι ι ℂ) (t m : ℂ)
    (hGM : G - M = -(M * (H + (t * m) • (1 : Matrix ι ι ℂ)) * G)) (hMd : ∀ β, M β β = m)
    (hS : ∀ i, ∑ j, S i j = t) (f : ℂ) (df : ι → ι → ℂ) (x y : ι) :
    (G x y - M x y) * f - (∑ α, ∑ β, M x α * S α β * (G β β - M β β) * G α y * f -
        ∑ α, ∑ β, M x α * S α β * G β y * df β α) =
      -∑ α, M x α * BAExpand_defect G H S f df y α := by
  have h1 : (G x y - M x y) = -∑ α, M x α * (∑ β, H α β * G β y + t * m * G α y) := by
    have := congrFun (congrFun hGM x) y
    rw [Matrix.sub_apply] at this
    rw [this, Matrix.neg_apply, Matrix.mul_assoc, Matrix.mul_apply]
    congr 1
    refine Finset.sum_congr rfl fun α _ => ?_
    congr 1
    simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, add_mul, Finset.sum_add_distrib]
  have hrow : ∀ α, ∑ β, S α β * M β β = t * m := by
    intro α
    simp only [hMd]
    rw [← Finset.sum_mul, hS]
  rw [h1]
  unfold BAExpand_defect
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  have step : -(M x α * (∑ β, H α β * G β y + t * m * G α y)) * f =
      ∑ β, (-(M x α * f) * (H α β * G β y) - M x α * G α y * f * (S α β * M β β)) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hrow α]; ring
  rw [step, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun β _ => ?_
  ring

end BAAlg

section BAMain

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

/-- **`(M1)` on the model**: `G - M = -M (H_u + u m) G` for `G = (g₀Ψ + H_u - z_u)⁻¹`, `M = (g₀Ψ - E - m)⁻¹`,
`z_u = E + (1 - u) m`, `Im m > 0`, `u < 1` (so that `G⁻¹ - M⁻¹ = H_u + u m`). -/
theorem BAExpand_G_sub_M (g0 E u : ℝ) (m : ℂ) (hm : 0 < m.im) (hu : u < 1) (ω : Sizes.SeqΩ sz) :
    baGm sz n g0 (ztOf m E u) u ω - Mres ((g0 : ℂ) • PsiI d (sz.L n) (sz.W n)) (E : ℂ) m =
      -(Mres ((g0 : ℂ) • PsiI d (sz.L n) (sz.W n)) (E : ℂ) m *
        (sz.seqHflow n u ω + ((u : ℂ) * m) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) *
        baGm sz n g0 (ztOf m E u) u ω) := by
  have hz : (ztOf m E u).im ≠ 0 := by
    rw [ztOf_im, etaOf]; exact (mul_pos (by linarith) hm).ne'
  have hw : ((E : ℂ) + m).im ≠ 0 := by simpa using hm.ne'
  have hPsi : ((g0 : ℂ) • PsiI d (sz.L n) (sz.W n)).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_smul, (PsiI_isHermitian d (sz.L n) (sz.W n)).eq,
      show star (g0 : ℂ) = (g0 : ℂ) from Complex.conj_ofReal _]
  have hA := isUnit_sub_smul_of_isHermitian (BAExpand_Hm_isHermitian sz n g0 u ω) hz
  have hB := isUnit_sub_smul_of_isHermitian hPsi hw
  have h := BAExpand_inv_sub_inv hA hB
  have hAB : (BAExpand_Hm sz n g0 u ω - ztOf m E u • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) -
      ((g0 : ℂ) • PsiI d (sz.L n) (sz.W n) - ((E : ℂ) + m) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) =
      sz.seqHflow n u ω + ((u : ℂ) * m) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) := by
    have e : ((u : ℂ) * m) = ((E : ℂ) + m) - ztOf m E u := by simp only [ztOf]; ring
    rw [e, sub_smul, BAExpand_Hm]
    abel
  rw [hAB] at h
  simpa [baGm, Gres, Mres] using h

end BAMain

section BAIntegral

variable {d : ℕ} {sz : Sizes d} {n : ℕ}

/-- Closure of `Tame` under the operations of the expansion (the twin of the local macro `lw_tame`), with the
shifted resolvent entries, the entries of `H_u` and the derivatives as leaves. -/
local macro "ba_tame" : tactic =>
  `(tactic| repeat' first
    | exact Tame.const _
    | assumption
    | (apply BAExpand_tame_baG; assumption)
    | (apply lwStein_tame_dhSample; assumption)
    | apply lwStein_tame_hflow
    | apply Tame.mul
    | apply Tame.add
    | apply Tame.sub
    | apply Tame.neg
    | (apply Tame.sum; intros; skip))

/-- **`E Z_α = 0`** (`lanlw`, `B:359-372`): for a resolvent polynomial `f`, `df β α = ∂_{h_{βα}} f`, the Stein defect `Z_α`
of the row `α` (`BAExpand_defect`, with `S = S^{(u)} = u · svarF`) has mean zero.  From the complex Stein identity applied to
`G_{βy} f` and `∂_{h_{βα}} G_{βy} = -G_{ββ} G_{αy}`. -/
theorem BAExpand_integral_defect (hG : GaussIBP sz) {z : ℂ} (hz : z.im ≠ 0) (g0 : ℝ) {u : ℝ} (hu : 0 < u)
    (P : MvPolynomial (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool) ℂ)
    (y α : Idx d (sz.L n) (sz.W n)) :
    ∫ ω, BAExpand_defect (baGm sz n g0 z u ω) (sz.seqHflow n u ω) (lwS sz n u) (baPoly sz n g0 z u P ω)
      (fun α' w' => dhSample sz n u α' w' (baPoly sz n g0 z u P) ω) y α ∂(Sizes.seqP sz) = 0 := by
  classical
  have hf : Tame1 sz n (baPoly sz n g0 z u P) := baPoly_tame1 hz g0 u P
  have hQ : ∀ β : Idx d (sz.L n) (sz.W n),
      Tame1 sz n (fun ω => baG sz n g0 z u β y ω * baPoly sz n g0 z u P ω) :=
    fun β => (baG_tame1 hz g0 u β y).mul hf
  have hdQ : ∀ (β : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz),
      dhSample sz n u β α (fun ω => baG sz n g0 z u β y ω * baPoly sz n g0 z u P ω) ω =
        -(baG sz n g0 z u β β ω * baG sz n g0 z u α y ω) * baPoly sz n g0 z u P ω +
          baG sz n g0 z u β y ω * dhSample sz n u β α (baPoly sz n g0 z u P) ω := by
    intro β ω
    rw [lwStein_dh_mul (baG_tame1 hz g0 u β y) hf, dhSample_baG hz hu]
  have hpt : ∀ ω : Sizes.SeqΩ sz,
      BAExpand_defect (baGm sz n g0 z u ω) (sz.seqHflow n u ω) (lwS sz n u) (baPoly sz n g0 z u P ω)
        (fun α' w' => dhSample sz n u α' w' (baPoly sz n g0 z u P) ω) y α =
      ∑ β, (sz.seqHflow n u ω α β * (baG sz n g0 z u β y ω * baPoly sz n g0 z u P ω) -
        lwS sz n u α β * dhSample sz n u β α (fun ω => baG sz n g0 z u β y ω * baPoly sz n g0 z u P ω) ω) := by
    intro ω
    unfold BAExpand_defect
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [hdQ]
    simp only [baG]
  simp_rw [hpt]
  have iA : ∀ β : Idx d (sz.L n) (sz.W n), Integrable (fun ω => sz.seqHflow n u ω α β *
      (baG sz n g0 z u β y ω * baPoly sz n g0 z u P ω)) (Sizes.seqP sz) := fun β =>
    Tame.integrable hG ((lwStein_tame_hflow sz n u α β).mul (hQ β).tame)
  have iB : ∀ β : Idx d (sz.L n) (sz.W n), Integrable (fun ω => lwS sz n u α β *
      dhSample sz n u β α (fun ω => baG sz n g0 z u β y ω * baPoly sz n g0 z u P ω) ω) (Sizes.seqP sz) :=
    fun β => Tame.integrable hG ((Tame.const _).mul (lwStein_tame_dhSample (hQ β) u β α))
  have iC : ∀ β : Idx d (sz.L n) (sz.W n), Integrable (fun ω => sz.seqHflow n u ω α β *
      (baG sz n g0 z u β y ω * baPoly sz n g0 z u P ω) - lwS sz n u α β *
      dhSample sz n u β α (fun ω => baG sz n g0 z u β y ω * baPoly sz n g0 z u P ω) ω) (Sizes.seqP sz) :=
    fun β => (iA β).sub (iB β)
  rw [integral_finsetSum _ fun β _ => iC β]
  refine Finset.sum_eq_zero fun β _ => ?_
  rw [integral_sub (iA β) (iB β), integral_const_mul, stein_sample hG (hQ β) hu.le β α]
  ring

/-- **`lanlw` in expectation on the sequence space** (`B:359-372`): for the shifted resolvent, a resolvent polynomial `f`,
a matrix `M` with `M_{ββ} = m` and `G - M = -M (H_u + u m) G` at every sample.  Hypotheses: `GaussIBP sz`. -/
theorem BAExpand_integral (hG : GaussIBP sz) {z : ℂ} (hz : z.im ≠ 0) (g0 : ℝ) {u : ℝ} (hu : 0 < u)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (m : ℂ) (hMd : ∀ β, M β β = m)
    (hGM : ∀ ω, baGm sz n g0 z u ω - M = -(M * (sz.seqHflow n u ω + ((u : ℂ) * m) •
      (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) * baGm sz n g0 z u ω))
    (P : MvPolynomial (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool) ℂ)
    (x y : Idx d (sz.L n) (sz.W n)) :
    ∫ ω, (baG sz n g0 z u x y ω - M x y) * baPoly sz n g0 z u P ω ∂(Sizes.seqP sz) =
      ∫ ω, (∑ α, ∑ β, M x α * lwS sz n u α β * (baG sz n g0 z u β β ω - M β β) * baG sz n g0 z u α y ω *
            baPoly sz n g0 z u P ω -
          ∑ α, ∑ β, M x α * lwS sz n u α β * baG sz n g0 z u β y ω *
            dhSample sz n u β α (baPoly sz n g0 z u P) ω) ∂(Sizes.seqP sz) := by
  classical
  have hf : Tame1 sz n (baPoly sz n g0 z u P) := baPoly_tame1 hz g0 u P
  have tf : Tame sz (baPoly sz n g0 z u P) := hf.tame
  have tD : ∀ α β : Idx d (sz.L n) (sz.W n), Tame sz (dhSample sz n u α β (baPoly sz n g0 z u P)) :=
    fun α β => lwStein_tame_dhSample hf u α β
  have tG : ∀ i j : Idx d (sz.L n) (sz.W n), Tame sz (baG sz n g0 z u i j) :=
    fun i j => BAExpand_tame_baG sz n hz g0 u i j
  have hpt : ∀ ω : Sizes.SeqΩ sz,
      ((baG sz n g0 z u x y ω - M x y) * baPoly sz n g0 z u P ω -
        (∑ α, ∑ β, M x α * lwS sz n u α β * (baG sz n g0 z u β β ω - M β β) * baG sz n g0 z u α y ω *
            baPoly sz n g0 z u P ω -
          ∑ α, ∑ β, M x α * lwS sz n u α β * baG sz n g0 z u β y ω *
            dhSample sz n u β α (baPoly sz n g0 z u P) ω)) =
      -∑ α, M x α * BAExpand_defect (baGm sz n g0 z u ω) (sz.seqHflow n u ω) (lwS sz n u)
        (baPoly sz n g0 z u P ω) (fun α' w' => dhSample sz n u α' w' (baPoly sz n g0 z u P) ω) y α :=
    fun ω => BAExpand_defect_identity (baGm sz n g0 z u ω) M (sz.seqHflow n u ω) (lwS sz n u) (u : ℂ) m
      (hGM ω) hMd (lwS_row_sum u) (baPoly sz n g0 z u P ω)
      (fun α' w' => dhSample sz n u α' w' (baPoly sz n g0 z u P) ω) x y
  have iZ : ∀ α : Idx d (sz.L n) (sz.W n), Integrable (fun ω => BAExpand_defect (baGm sz n g0 z u ω)
      (sz.seqHflow n u ω) (lwS sz n u) (baPoly sz n g0 z u P ω)
      (fun α' w' => dhSample sz n u α' w' (baPoly sz n g0 z u P) ω) y α) (Sizes.seqP sz) := by
    intro α
    refine Tame.integrable hG ?_
    unfold BAExpand_defect
    ba_tame
  have hzero : ∫ ω, ((baG sz n g0 z u x y ω - M x y) * baPoly sz n g0 z u P ω -
        (∑ α, ∑ β, M x α * lwS sz n u α β * (baG sz n g0 z u β β ω - M β β) * baG sz n g0 z u α y ω *
            baPoly sz n g0 z u P ω -
          ∑ α, ∑ β, M x α * lwS sz n u α β * baG sz n g0 z u β y ω *
            dhSample sz n u β α (baPoly sz n g0 z u P) ω)) ∂(Sizes.seqP sz) = 0 := by
    simp_rw [hpt]
    rw [integral_neg, integral_finsetSum _ fun α _ => (iZ α).const_mul _]
    simp [integral_const_mul, BAExpand_integral_defect hG hz g0 hu P y]
  have iL : Integrable (fun ω => (baG sz n g0 z u x y ω - M x y) * baPoly sz n g0 z u P ω) (Sizes.seqP sz) := by
    refine Tame.integrable hG ?_
    ba_tame
  have iR : Integrable (fun ω => (∑ α, ∑ β, M x α * lwS sz n u α β * (baG sz n g0 z u β β ω - M β β) *
            baG sz n g0 z u α y ω * baPoly sz n g0 z u P ω -
          ∑ α, ∑ β, M x α * lwS sz n u α β * baG sz n g0 z u β y ω *
            dhSample sz n u β α (baPoly sz n g0 z u P) ω)) (Sizes.seqP sz) := by
    refine Tame.integrable hG ?_
    ba_tame
  rw [integral_sub iL iR] at hzero
  linear_combination hzero

end BAIntegral

section BAPin

/-- Closure of `Tame` (as in the section above). -/
local macro "ba_tame" : tactic =>
  `(tactic| repeat' first
    | exact Tame.const _
    | assumption
    | (apply BAExpand_tame_baG; assumption)
    | (apply lwStein_tame_dhSample; assumption)
    | apply lwStein_tame_hflow
    | apply Tame.mul
    | apply Tame.add
    | apply Tame.sub
    | apply Tame.neg
    | (apply Tame.sum; intros; skip))

/-- **`M_{ββ} = m`** at a solution of `(self_m)`: `M = M^{(B)} ⊗ I` (`BAMres_fine_apply`) and `BAMB_diag_eq`. -/
theorem BAExpand_M_diag {d L W : ℕ} [NeZero L] [NeZero W] (g0 E : ℝ) (m : ℂ)
    (h : RBM.BA.BASelf d L g0 (E : ℂ) m) (β : Idx d L W) : BAlwM d L W g0 E m β β = m := by
  have hw : ((E : ℂ) + m).im ≠ 0 := by simpa using h.1.ne'
  unfold BAlwM
  rw [RBM.BA.BAMres_fine_apply d L W g0 (E : ℂ) m hw β β]
  simp only [ite_true]
  exact RBM.BA.BAMB_diag_eq d L g0 (E : ℂ) m h _

/-- **`t = 0`**: `H_0 = 0`, `z_0 = E + m`, `G = M`, so `Ǧ = 0`. -/
theorem BAExpand_Gc_zero {d L W : ℕ} [NeZero L] [NeZero W] (g0 E : ℝ) (m : ℂ) (ω : Ω d L W)
    (x y : Idx d L W) : BAlwGc d L W g0 E 0 m ω x y = 0 := by
  have hH : Hflow d L W 0 ω = 0 := by simp [Hflow]
  have hG : BAlwG d L W g0 E 0 m ω x y = BAlwM d L W g0 E m x y := by
    unfold BAlwG BAlwM BAlwH Mres Gres
    rw [hH]
    simp [ztOf]
  unfold BAlwGc
  rw [hG, sub_self]

/-- **`lanlw`** (`B:359-372`, [yang2024Del, Lemma B.9]) on the block Anderson law `PF d L W 0`, for every `d`: the pin
`BAlanlw`.  For `0 < t < 1`: `BAExpand_integral` (hypothesis `gaussIBP`, proved) through the bridge, with `M_{ββ} = m`
(`BASelf`); for `t = 0` both sides vanish.  No condition on `g₀`, `E`. -/
theorem baLanlw_holds (d : ℕ) : BAlanlw d := by
  intro L W _ _ hL g0 E t m hSelf ht0 ht1 P x y
  have hm : 0 < m.im := hSelf.1
  rcases ht0.eq_or_lt with rfl | ht
  · have hL0 : ∀ ω, BAlanlwL d L W g0 E 0 m P x y ω = 0 := fun ω => by
      simp [BAlanlwL, BAExpand_Gc_zero]
    have hR0 : ∀ ω, BAlanlwR d L W g0 E 0 m P x y ω = 0 := fun ω => by
      simp [BAlanlwR, BAlwS]
    simp [hL0, hR0]
  · have hz : (ztOf m E t).im ≠ 0 := by
      rw [ztOf_im, etaOf]; exact (mul_pos (by linarith) hm).ne'
    have key := BAExpand_integral (sz := lwWxSizes d L W 0 hL) (n := 0) (gaussIBP (lwWxSizes d L W 0 hL)) hz g0 ht
      (BAlwM d L W g0 E m) m (BAExpand_M_diag g0 E m hSelf)
      (fun ω => BAExpand_G_sub_M (lwWxSizes d L W 0 hL) 0 g0 E t m hm ht1 ω) (lwWxRename d L W P) x y
    have hf : Tame1 (lwWxSizes d L W 0 hL) 0 (baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P)) :=
      baPoly_tame1 (sz := lwWxSizes d L W 0 hL) (n := 0) hz g0 t (lwWxRename d L W P)
    have tf : Tame (lwWxSizes d L W 0 hL) (baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P)) :=
      hf.tame
    have tG : ∀ i j : Idx d L W, Tame (lwWxSizes d L W 0 hL) (baG (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t i j) :=
      fun i j => BAExpand_tame_baG (lwWxSizes d L W 0 hL) 0 hz g0 t i j
    refine (lwWx_integral hL ?_ ?_).trans (key.trans (lwWx_integral hL ?_ ?_).symm)
    · refine Tame.cont ?_
      ba_tame
    · intro ω'
      unfold BAlanlwL
      rw [← baWx_baPoly hL g0 E t m ω' P]
      rfl
    · refine Tame.cont ?_
      ba_tame
    · intro ω'
      have hdf : ∀ β α : Idx d L W, BAlwdf d L W g0 E t m P (Sizes.slice (lwWxSizes d L W 0 hL) 0 ω') β α =
          dhSample (lwWxSizes d L W 0 hL) 0 t β α
            (baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P)) ω' :=
        fun β α => (baWx_dh hL hz ht g0 β α ω' P).symm
      unfold BAlanlwR
      simp only [hdf, ← baWx_baPoly hL g0 E t m ω' P, lwWx_lwS_apply hL t]
      rfl

end BAPin

/-! ## 4. Compiled instances of the pin and of the Stein layer (namespace `RBM.Graph.BAExpandInst`) -/

namespace BAExpandInst

/-- (I1) the vocabulary at `d = 3`, `L = 3`, `W = 1`: `S_{xx} = t W^{-d} = 1/2` (here `t = 1/2`, `W = 1`). -/
theorem baS_diag (x : Idx 3 3 1) : BAlwS 3 3 1 (1 / 2) x x = 1 / 2 := by
  simp [BAlwS, svarF_diag]

/-- (I1) the row sum of `S` is `t`: `Σ_y S_{xy} = 1/2` (`lwS_row_sum` through the bridge). -/
theorem baS_row_sum (x : Idx 3 3 1) : ∑ y, BAlwS 3 3 1 (1 / 2) x y = 1 / 2 := by
  have h := lwS_row_sum (sz := lwWxSizes 3 3 1 0 (by norm_num)) (n := 0) (1 / 2) x
  simp only [lwWx_lwS_apply (by norm_num : 3 ≤ 3)] at h
  simpa [BAlwS, LWPins_lwS] using h

/-- (I2) at `t = 0` both sides of `lanlw` vanish pointwise (`H_0 = 0`, `G = M`, `S = 0`); `baLanlw_holds 3` at `t = 0`
is the equality `0 = 0` of the two integrals. -/
theorem baLanlw_t0 (g0 E : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf 3 3 g0 (E : ℂ) m)
    (P : MvPolynomial (Bool × Idx 3 3 1 × Idx 3 3 1) ℂ) (x y : Idx 3 3 1) :
    ∫ ω, BAlanlwL 3 3 1 g0 E 0 m P x y ω ∂(PF 3 3 1 0) = 0 ∧
      ∫ ω, BAlanlwR 3 3 1 g0 E 0 m P x y ω ∂(PF 3 3 1 0) = 0 ∧
      ∫ ω, BAlanlwL 3 3 1 g0 E 0 m P x y ω ∂(PF 3 3 1 0) =
        ∫ ω, BAlanlwR 3 3 1 g0 E 0 m P x y ω ∂(PF 3 3 1 0) := by
  have hL0 : ∀ ω, BAlanlwL 3 3 1 g0 E 0 m P x y ω = 0 := fun ω => by
    simp [BAlanlwL, BAExpand_Gc_zero]
  have hR0 : ∀ ω, BAlanlwR 3 3 1 g0 E 0 m P x y ω = 0 := fun ω => by
    simp [BAlanlwR, BAlwS]
  refine ⟨by simp [hL0], by simp [hR0], ?_⟩
  exact baLanlw_holds 3 3 1 (by norm_num) g0 E 0 m hSelf le_rfl one_pos P x y

/-- The size sequence of the instances: `L = 3`, `W = 1`, coupling `0` (`S^{(B)}(0) = I`). -/
abbrev baInstSz : Sizes 3 := lwWxSizes 3 3 1 0 (le_refl 3)

/-- (I1b) the closed forms of the derivative at `d = 3`, `L = 3`, `W = 1`, `g₀ = 1/2`, `z = i`, `u = 1/2`, at every sample. -/
example (α w i j : Idx 3 3 1) (ω : Sizes.SeqΩ baInstSz) :
    dhSample baInstSz 0 (1 / 2) α w (baG baInstSz 0 (1 / 2) Complex.I (1 / 2) i j) ω =
      -(baG baInstSz 0 (1 / 2) Complex.I (1 / 2) i α ω * baG baInstSz 0 (1 / 2) Complex.I (1 / 2) w j ω) :=
  dhSample_baG (by simp) (by norm_num) (1 / 2) α w i j ω

example (α w i j : Idx 3 3 1) (ω : Sizes.SeqΩ baInstSz) :
    dhSample baInstSz 0 (1 / 2) α w (fun ω => star (baG baInstSz 0 (1 / 2) Complex.I (1 / 2) i j ω)) ω =
      -star (baG baInstSz 0 (1 / 2) Complex.I (1 / 2) i w ω * baG baInstSz 0 (1 / 2) Complex.I (1 / 2) α j ω) :=
  dhSample_baG_star (by simp) (by norm_num) (1 / 2) α w i j ω

/-- (I1b) tameness of the entries and of a resolvent polynomial (`G_{ij} \bar G_{ij}`). -/
example (i j : Idx 3 3 1) : Tame1 baInstSz 0 (baG baInstSz 0 (1 / 2) Complex.I (1 / 2) i j) :=
  baG_tame1 (sz := baInstSz) (n := 0) (z := Complex.I) (by simp) (1 / 2) (1 / 2) i j

example (i j : Idx 3 3 1) : Tame1 baInstSz 0 (baPoly baInstSz 0 (1 / 2) Complex.I (1 / 2)
    (MvPolynomial.X (i, j, true) * MvPolynomial.X (i, j, false))) :=
  baPoly_tame1 (sz := baInstSz) (n := 0) (z := Complex.I) (by simp) (1 / 2) (1 / 2) _

/-- (I1b) the Stein identity for the resolvent polynomial `G_{ij} \bar G_{ij}` (`gaussIBP` proved). -/
example (i j α w : Idx 3 3 1) :
    ∫ ω, baInstSz.seqHflow 0 (1 / 2) ω w α * baPoly baInstSz 0 (1 / 2) Complex.I (1 / 2)
        (MvPolynomial.X (i, j, true) * MvPolynomial.X (i, j, false)) ω ∂(Sizes.seqP baInstSz) =
      lwS baInstSz 0 (1 / 2) w α * ∫ ω, dhSample baInstSz 0 (1 / 2) α w (baPoly baInstSz 0 (1 / 2) Complex.I (1 / 2)
        (MvPolynomial.X (i, j, true) * MvPolynomial.X (i, j, false))) ω ∂(Sizes.seqP baInstSz) :=
  stein_baPoly (gaussIBP baInstSz) (by simp) (1 / 2) (by norm_num) _ α w

/-- (I1b) the bridge to `PF 3 3 1 0`: the resolvent entry, the polynomial and the derivative agree. -/
example (ω : Sizes.SeqΩ baInstSz) (x y : Idx 3 3 1) :
    baG baInstSz 0 (1 / 2) (ztOf Complex.I 0 (1 / 2)) (1 / 2) x y ω =
      BAlwG 3 3 1 (1 / 2) 0 (1 / 2) Complex.I (Sizes.slice baInstSz 0 ω) x y :=
  baWx_baG (le_refl 3) (1 / 2) 0 (1 / 2) Complex.I ω x y

example (ω : Sizes.SeqΩ baInstSz) (x y : Idx 3 3 1) :
    baPoly baInstSz 0 (1 / 2) (ztOf Complex.I 0 (1 / 2)) (1 / 2)
        (lwWxRename 3 3 1 (MvPolynomial.X (true, x, y) * MvPolynomial.X (false, x, y))) ω =
      BAlwf 3 3 1 (1 / 2) 0 (1 / 2) Complex.I (MvPolynomial.X (true, x, y) * MvPolynomial.X (false, x, y))
        (Sizes.slice baInstSz 0 ω) :=
  baWx_baPoly (le_refl 3) (1 / 2) 0 (1 / 2) Complex.I ω _

example (ω : Sizes.SeqΩ baInstSz) (α w x y : Idx 3 3 1) :
    dhSample baInstSz 0 (1 / 2) α w (baPoly baInstSz 0 (1 / 2) (ztOf Complex.I 0 (1 / 2)) (1 / 2)
        (lwWxRename 3 3 1 (MvPolynomial.X (true, x, y) * MvPolynomial.X (false, x, y)))) ω =
      LWPins_dH (LWPins_resPoly 3 3 1 (ztOf Complex.I 0 (1 / 2))
        (MvPolynomial.X (true, x, y) * MvPolynomial.X (false, x, y)))
        ((1 / 2 : ℝ) • PsiI 3 3 1 + Hflow 3 3 1 (1 / 2) (Sizes.slice baInstSz 0 ω)) α w :=
  baWx_dh (le_refl 3) (by norm_num [ztOf]) (by norm_num) (1 / 2) α w ω _

/-- `(self_m)` at `g = 0`, `z = 0`: `m = i` (`M^{(B)} = i I`, `L^{-d} tr = i`). -/
theorem baSelf_zero : RBM.BA.BASelf 3 3 0 ((0 : ℝ) : ℂ) Complex.I := by
  refine ⟨by simp, ?_⟩
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hB : RBM.BA.BAMB 3 3 0 ((0 : ℝ) : ℂ) Complex.I = Complex.I • (1 : Matrix (Zd 3 3) (Zd 3 3) ℂ) := by
    unfold RBM.BA.BAMB Mres
    have : ((0 : ℝ) : ℂ) • PsiB 3 3 - (((0 : ℝ) : ℂ) + Complex.I) • (1 : Matrix (Zd 3 3) (Zd 3 3) ℂ) =
        (-Complex.I) • (1 : Matrix (Zd 3 3) (Zd 3 3) ℂ) := by simp
    rw [this, ring_inverse_smul_one (neg_ne_zero.2 hI), inv_neg, Complex.inv_I, neg_neg]
  rw [hB, Matrix.trace_smul, Matrix.trace_one, RBM.BA.BAcard_Zd]
  simp
  ring

/-- **Instance of `baLanlw_holds`** (the point `g₀ = 0`, `E = 0`, `m = i`, every hypothesis discharged;
`d = 3`, `L = 3`, `W = 1`, `t = 1/2`; `x = 0`, `y = e₀ ≠ x`, `P = X (true, e₀, 0)`, i.e. `f = G_{e₀ 0}`). -/
example :
    ∫ ω, BAlanlwL 3 3 1 0 0 (1 / 2) Complex.I (MvPolynomial.X (true, (fun i => if i = 0 then 1 else 0), 0)) 0
      (fun i => if i = 0 then 1 else 0) ω ∂(PF 3 3 1 0) =
    ∫ ω, BAlanlwR 3 3 1 0 0 (1 / 2) Complex.I (MvPolynomial.X (true, (fun i => if i = 0 then 1 else 0), 0)) 0
      (fun i => if i = 0 then 1 else 0) ω ∂(PF 3 3 1 0) :=
  baLanlw_holds 3 3 1 (by norm_num) 0 0 (1 / 2) Complex.I baSelf_zero (by norm_num) (by norm_num) _ _ _

/-- **Instance of `baLanlw_holds` at `g₀ = 1/2`** (`d = 3`, `L = 3`, `W = 1`, `E = 3/10`, `t = 1/2`; `x = 0`, `y = e₀`,
`P = X (true, e₀, 0) * X (false, e₀, 0)`): the datum `m` solving `(self_m)` is a hypothesis of the example (`hSelf`);
every other hypothesis is discharged. -/
example (m : ℂ) (hSelf : RBM.BA.BASelf 3 3 (1 / 2) (((3 / 10 : ℝ)) : ℂ) m) :
    ∫ ω, BAlanlwL 3 3 1 (1 / 2) (3 / 10) (1 / 2) m
      (MvPolynomial.X (true, (fun i => if i = 0 then 1 else 0), 0) *
        MvPolynomial.X (false, (fun i => if i = 0 then 1 else 0), 0)) 0
      (fun i => if i = 0 then 1 else 0) ω ∂(PF 3 3 1 0) =
    ∫ ω, BAlanlwR 3 3 1 (1 / 2) (3 / 10) (1 / 2) m
      (MvPolynomial.X (true, (fun i => if i = 0 then 1 else 0), 0) *
        MvPolynomial.X (false, (fun i => if i = 0 then 1 else 0), 0)) 0
      (fun i => if i = 0 then 1 else 0) ω ∂(PF 3 3 1 0) :=
  baLanlw_holds 3 3 1 (by norm_num) (1 / 2) (3 / 10) (1 / 2) m hSelf (by norm_num) (by norm_num) _ _ _

end BAExpandInst

end RBM.Graph

end
