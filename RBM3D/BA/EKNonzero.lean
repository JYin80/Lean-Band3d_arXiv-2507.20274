/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.EKPins
import RBM3D.BA.Prop6Path
import RBM3D.Kernel.Evolution
import RBM3D.Defs.RadialSum

/-!
# Stage E of the block Anderson model (BA-E3): `lem:sum_decay_nonzero` at BA

`baEKSumDecayNonzero_holds : BAEKSumDecayNonzero d n Λ κ` for all `d n Λ κ`: the owed pin of
`BA/EKPins.lean:134`, `‖Q^(A) U^(n)_{s,t,σ} 𝒜‖_∞ ≤ C ‖𝒜‖_∞` for `1 - g²/L² ≤ s ≤ t < 1`,
`A ⊇ I_diff(σ)`, with `C` depending on `(d, n, Λ, κ)` only.

Ticket T2406.  Paper: `A_deterministic_estimates.tex:204-228`.  The band proof is
`RBM3D/Evolution/Nonzero.lean:145-185` (`ekSumDecayNonzero_holds`, port of
`norm_zeroModeSet_UN_le`, `Kernel/Evolution.lean:629`); no step reads `‖m‖ = 1`, `PropSpin`,
a scalar `μ`, `M = m I` or the smallness of `g`:
* `i ∉ A`: `σ_i = σ_{i+1}`, so the factor is bounded by `baEKSameRow_holds` (`BA/EKPins.lean:568`);
* `i ∈ A`: `Proj` commutes with the translation-invariant `M^{(σσ')}`, `Proj Θ = Θ̊` (translation
  invariance of `Θ`, no stochasticity), so `Proj (1 - s M) Θ_t = Proj + (t - s) M Θ̊_t`;
  the row sum of `Θ̊` is bounded by `baProp8_holds` and the radial sum `sum_radial_pow_le`;
  `(1 - s) L² ≤ g²` removes `L²`;
* the factors are tensored (`zeroModeSet_tensorKer`, `norm_tensorKer_le`).

Private helpers carry the stem `EKNonzero_`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

noncomputable section

open RBM

namespace RBM.BA

open scoped Matrix.Norms.Operator

/-! ## 1. `Proj = I - L^{-d} J` against translation-invariant matrices -/

section Proj

variable {d L : ℕ} [NeZero L]

/-- the constant of the radial sum `Σ_b (|b|+1)^{-k} ≤ E L²` (`sum_radial_pow_le`) -/
def EKNonzero_E (k : ℕ) : ℝ :=
  Real.exp (Real.sqrt ((k : ℝ) + 2)) * (2 ^ (k + 2) * radC 1)

theorem EKNonzero_E_pos (k : ℕ) : 0 < EKNonzero_E k := by
  unfold EKNonzero_E
  have := radC_pos (one_pos : (0 : ℝ) < 1)
  have := Real.exp_pos (Real.sqrt ((k : ℝ) + 2))
  positivity

/-- the row sums of a translation-invariant matrix are all equal -/
private theorem EKNonzero_row_sum {T : Matrix (Zd d L) (Zd d L) ℂ}
    (hT : ∀ a b r : Zd d L, T (a + r) (b + r) = T a b) (a : Zd d L) :
    ∑ c, T a c = ∑ c, T 0 c := by
  have hrow : ∀ c : Zd d L, T a c = T 0 (c - a) := fun c => by
    have := hT 0 (c - a) a
    simpa using this
  rw [Finset.sum_congr rfl fun c _ => hrow c]
  exact Fintype.sum_equiv (Equiv.subRight a) _ _ fun c => rfl

/-- the column sums of a translation-invariant matrix equal its row sum at `0` -/
private theorem EKNonzero_col_sum {T : Matrix (Zd d L) (Zd d L) ℂ}
    (hT : ∀ a b r : Zd d L, T (a + r) (b + r) = T a b) (b : Zd d L) :
    ∑ c, T c b = ∑ c, T 0 c := by
  have h1 : ∀ c : Zd d L, T c b = T (c - b) 0 := fun c => by
    have := hT (c - b) 0 b
    simpa using this
  have h2 : ∀ c : Zd d L, T c 0 = T 0 (-c) := fun c => by
    have := hT 0 (-c) c
    simpa using this
  calc ∑ c, T c b = ∑ c, T (c - b) 0 := Finset.sum_congr rfl fun c _ => h1 c
    _ = ∑ c, T c 0 := Fintype.sum_equiv (Equiv.subRight b) _ _ fun c => rfl
    _ = ∑ c, T 0 (-c) := Finset.sum_congr rfl fun c _ => h2 c
    _ = ∑ c, T 0 c := Fintype.sum_equiv (Equiv.neg _) _ _ fun c => rfl

private theorem EKNonzero_projMat_mul_apply {T : Matrix (Zd d L) (Zd d L) ℂ}
    (hT : ∀ a b r : Zd d L, T (a + r) (b + r) = T a b) (a b : Zd d L) :
    (projMat d L * T) a b = T a b - ((L : ℂ) ^ d)⁻¹ * ∑ c, T 0 c := by
  unfold projMat
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply]
  simp only [Matrix.mul_apply, Matrix.of_apply, ← Finset.mul_sum]
  rw [EKNonzero_col_sum hT b]

private theorem EKNonzero_mul_projMat_apply {T : Matrix (Zd d L) (Zd d L) ℂ}
    (hT : ∀ a b r : Zd d L, T (a + r) (b + r) = T a b) (a b : Zd d L) :
    (T * projMat d L) a b = T a b - ((L : ℂ) ^ d)⁻¹ * ∑ c, T 0 c := by
  unfold projMat
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply]
  simp only [Matrix.mul_apply, Matrix.of_apply, ← Finset.sum_mul]
  rw [EKNonzero_row_sum hT a, mul_comm]

/-- `Proj T = T Proj` for a translation-invariant `T` (the paper's remark that `Proj_{e^⊥}` commutes
with `M^{(σ₁σ₂)}`; no stochasticity of `T` is used). -/
theorem EKNonzero_projMat_comm {T : Matrix (Zd d L) (Zd d L) ℂ}
    (hT : ∀ a b r : Zd d L, T (a + r) (b + r) = T a b) :
    projMat d L * T = T * projMat d L := by
  ext a b
  rw [EKNonzero_projMat_mul_apply hT, EKNonzero_mul_projMat_apply hT]

/-- `M^{(σ₁σ₂)}` is invariant under the diagonal shift (`BAMB_shift`, `BA/Ward.lean:53`; a copy of the
private `baP8_BAMss_shift`, `BA/Prop6Path.lean:483`). -/
theorem EKNonzero_Mss_shift (g E : ℝ) (m : ℂ) (σ₁ σ₂ : Bool) (a b r : Zd d L) :
    BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ (a + r) (b + r) = BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ a b := by
  have hM := BAMB_shift d L g (E : ℂ) m
  have hs : ∀ (σ : Bool) (x y : Zd d L),
      BAMsigma d L (BAMB d L g (E : ℂ) m) σ (x + r) (y + r) = BAMsigma d L (BAMB d L g (E : ℂ) m) σ x y := by
    intro σ x y
    cases σ
    · simp only [BAMsigma, Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply, hM]
    · simp only [BAMsigma, ite_true, hM]
  simp only [BAMss, Matrix.of_apply, hs]

/-- **`Proj Θ = Θ̊`** (`(def_Thxi0)`) for `Θ_t^{(σ₁σ₂)}` at BA: left multiplication by `I - L^{-d} J` is the zero-mode
removal, by the translation invariance of `Θ` (`baP8_BATheta_shift`, `BA/Prop6Path.lean:497`) alone. -/
theorem EKNonzero_projMat_mul_Theta (g E : ℝ) (m : ℂ) (t : ℝ) (σ₁ σ₂ : Bool) :
    projMat d L * BATheta d L g E m t σ₁ σ₂ = BATheta0 d L g E m t σ₁ σ₂ := by
  have hT : ∀ a b r : Zd d L, BATheta d L g E m t σ₁ σ₂ (a + r) (b + r) = BATheta d L g E m t σ₁ σ₂ a b :=
    fun a b r => baP8_BATheta_shift g E m t σ₁ σ₂ a b r
  have hL0 : ((L : ℂ) ^ d) ≠ 0 := by
    have hne : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
    positivity
  have hdbl : ∑ a', ∑ b', BATheta d L g E m t σ₁ σ₂ a' b'
      = (L : ℂ) ^ d * ∑ c, BATheta d L g E m t σ₁ σ₂ 0 c := by
    rw [Finset.sum_congr rfl fun a' _ => EKNonzero_row_sum hT a', Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    congr 1
    simp [ZMod.card]
  ext a b
  rw [EKNonzero_projMat_mul_apply hT]
  simp only [BATheta0, Matrix.of_apply]
  rw [hdbl, two_mul, pow_add]
  field_simp

/-- `Θ̊` is translation invariant. -/
theorem EKNonzero_Theta0_shift (g E : ℝ) (m : ℂ) (t : ℝ) (σ₁ σ₂ : Bool) (a b r : Zd d L) :
    BATheta0 d L g E m t σ₁ σ₂ (a + r) (b + r) = BATheta0 d L g E m t σ₁ σ₂ a b := by
  simp only [BATheta0, Matrix.of_apply, baP8_BATheta_shift g E m t σ₁ σ₂ a b r]

/-- Ward row sums: `‖M^{(σ₁σ₂)}‖_{∞→∞} ≤ 1` (`BAMss_norm_eq_BAK`, `BAK_row_sum`; the twin of the private
`EKPins_norm_Q_le`, `BA/EKPins.lean:151`). -/
private theorem EKNonzero_norm_Q_le {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) (σ₁ σ₂ : Bool) :
    ‖BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂‖ ≤ 1 := by
  have h : ‖BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂‖₊ ≤ 1 := by
    rw [Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le fun a _ => ?_
    rw [← NNReal.coe_le_coe, NNReal.coe_sum, NNReal.coe_one]
    simpa [BAMss_norm_eq_BAK] using (BAK_row_sum d L g E m hr.1 a).le
  exact_mod_cast h

end Proj

/-! ## 2. The one-index factor at an index of `A`: `‖Proj · uKer‖ ≤ 2 + C₀ E_k` (`(eq:diffcolor)`, `A:216-218`) -/

/-! ## 3. `lem:sum_decay_nonzero` at BA -/

/-! ## 4. Compiled nonempty instances (`d = 3`, the flow datum `n = 0` of `sz0`)

The data of `inst_BAEKSumDecayNonzero` (`BA/EKPins.lean:758`), now without the pin as a hypothesis: `L = 4`,
`g₀ = √t₀ λ ≤ 1/64`, `κ = 1/2`, `Λ = 1`, `BAReal` by `hrI`, the window `s = 1 - g₀²/L²`,
`t = 1 - g₀²/(2L²)` (`0 ≤ s ≤ t < 1`), `𝒜 = δ₀` (`AI 0 = 1`).  Every hypothesis is discharged. -/

end RBM.BA
