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
private def EKNonzero_E (k : ℕ) : ℝ :=
  Real.exp (Real.sqrt ((k : ℝ) + 2)) * (2 ^ (k + 2) * radC 1)

private theorem EKNonzero_E_pos (k : ℕ) : 0 < EKNonzero_E k := by
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
private theorem EKNonzero_projMat_comm {T : Matrix (Zd d L) (Zd d L) ℂ}
    (hT : ∀ a b r : Zd d L, T (a + r) (b + r) = T a b) :
    projMat d L * T = T * projMat d L := by
  ext a b
  rw [EKNonzero_projMat_mul_apply hT, EKNonzero_mul_projMat_apply hT]

/-- `M^{(σ₁σ₂)}` is invariant under the diagonal shift (`BAMB_shift`, `BA/Ward.lean:53`; a copy of the
private `baP8_BAMss_shift`, `BA/Prop6Path.lean:483`). -/
private theorem EKNonzero_Mss_shift (g E : ℝ) (m : ℂ) (σ₁ σ₂ : Bool) (a b r : Zd d L) :
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
private theorem EKNonzero_projMat_mul_Theta (g E : ℝ) (m : ℂ) (t : ℝ) (σ₁ σ₂ : Bool) :
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
private theorem EKNonzero_Theta0_shift (g E : ℝ) (m : ℂ) (t : ℝ) (σ₁ σ₂ : Bool) (a b r : Zd d L) :
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

section OneIndex

variable {k : ℕ} {L : ℕ} [NeZero L]

omit [NeZero L] in
/-- `(1 - s) L² ≤ g²`, `g² + |1 - t| ≥ g²`, `t - s ≤ 1 - s`: the coefficient `(t - s) (g² + |1 - t|)⁻¹ L² ≤ 1`. -/
private theorem EKNonzero_coef {g s t : ℝ} (hg : 0 < g) (hL : 3 ≤ L) (hsg : 1 - g ^ 2 / (L : ℝ) ^ 2 ≤ s)
    (hst : s ≤ t) (ht : t < 1) :
    (t - s) * ((g ^ 2 + |1 - t|)⁻¹ * (L : ℝ) ^ 2) ≤ 1 := by
  have hg2 : (0 : ℝ) < g ^ 2 := by positivity
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_of_lt (by omega : 1 < L)
  have h1 : (g ^ 2 + |1 - t|)⁻¹ ≤ (g ^ 2)⁻¹ :=
    inv_anti₀ hg2 (by have := abs_nonneg (1 - t); linarith)
  have h2 : t - s ≤ 1 - s := by linarith
  have hs2 : (1 - s) * (L : ℝ) ^ 2 ≤ g ^ 2 := by
    have hsg' : 1 - s ≤ g ^ 2 / (L : ℝ) ^ 2 := by linarith
    rw [le_div_iff₀ (by positivity)] at hsg'
    linarith
  have h3 : (g ^ 2 + |1 - t|)⁻¹ * (L : ℝ) ^ 2 ≤ (g ^ 2)⁻¹ * (L : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  calc (t - s) * ((g ^ 2 + |1 - t|)⁻¹ * (L : ℝ) ^ 2)
      ≤ (1 - s) * ((g ^ 2)⁻¹ * (L : ℝ) ^ 2) :=
        mul_le_mul h2 h3 (by positivity) (by linarith)
    _ = ((1 - s) * (L : ℝ) ^ 2) / g ^ 2 := by field_simp
    _ ≤ 1 := by rw [div_le_one hg2]; exact hs2

/-- `(eq:diffcolor)` at BA: at an index carrying `Proj_{e^⊥}` the one-index factor `Proj (1 - s M) Θ_t` is bounded
by `2 + C₀ E_k`, from the bound of `BAProp8` (constant `C₀`, here as a row bound of `Θ̊`) and the Ward bound
`‖M‖_{∞→∞} ≤ 1`; valid for every charge pair `(σ₁, σ₂)`, including `σ₁ = σ₂`. -/
private theorem EKNonzero_norm_projMat_mul_uKer_le {κ C₀ g E : ℝ} {m : ℂ} (hC₀ : 0 < C₀) (hL : 3 ≤ L)
    (hg : 0 < g) (hr : BAReal (k + 2) L g κ E m) {s t : ℝ} (hs : 0 ≤ s)
    (hsg : 1 - g ^ 2 / (L : ℝ) ^ 2 ≤ s) (hst : s ≤ t) (ht : t < 1) (σ₁ σ₂ : Bool)
    (hbd : ∀ a : Zd (k + 2) L, ‖BATheta0 (k + 2) L g E m t σ₁ σ₂ 0 a‖
      ≤ C₀ * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD (k + 2) L a : ℝ) + 1) ^ (k + 2 - 2))⁻¹) :
    ‖projMat (k + 2) L * BAuKer (k + 2) L g E m s t σ₁ σ₂‖ ≤ 2 + C₀ * EKNonzero_E k := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_of_lt (by omega : 1 < L)
  have ht0 : 0 ≤ t := hs.trans hst
  have hE0 := EKNonzero_E_pos k
  -- the zero-mode-removed propagator: `BAProp8` plus the radial sum
  have hTheta0 : ‖BATheta0 (k + 2) L g E m t σ₁ σ₂‖
      ≤ C₀ * (g ^ 2 + |1 - t|)⁻¹ * (EKNonzero_E k * (L : ℝ) ^ 2) := by
    refine (norm_le_sum_row_zero _ (fun a b c => EKNonzero_Theta0_shift g E m t σ₁ σ₂ a b c)).trans ?_
    calc ∑ b : Zd (k + 2) L, ‖BATheta0 (k + 2) L g E m t σ₁ σ₂ 0 b‖
        ≤ ∑ b : Zd (k + 2) L, C₀ * (g ^ 2 + |1 - t|)⁻¹
            * (((zdistD (k + 2) L b : ℝ) + 1) ^ (k + 2 - 2))⁻¹ :=
          Finset.sum_le_sum fun b _ => hbd b
      _ = C₀ * (g ^ 2 + |1 - t|)⁻¹
            * ∑ b : Zd (k + 2) L, (((zdistD (k + 2) L b : ℝ) + 1) ^ k)⁻¹ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun b _ => by norm_num
      _ ≤ C₀ * (g ^ 2 + |1 - t|)⁻¹ * (EKNonzero_E k * (L : ℝ) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have := sum_radial_pow_le (L := L) k hL1
          unfold EKNonzero_E
          rw [mul_assoc]
          exact this
  have hcoef := EKNonzero_coef hg hL hsg hst ht
  -- `Proj * uKer = Proj + (t - s) • (M * Θ̊)`
  have hsplit : projMat (k + 2) L * BAuKer (k + 2) L g E m s t σ₁ σ₂
      = projMat (k + 2) L + ((t : ℂ) - s) •
        (BAMss (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₁ σ₂ * BATheta0 (k + 2) L g E m t σ₁ σ₂) := by
    rw [BAuKer_eq_one_add hr ht0 ht, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
      ← Matrix.mul_assoc, EKNonzero_projMat_comm (fun a b r => EKNonzero_Mss_shift g E m σ₁ σ₂ a b r),
      Matrix.mul_assoc, EKNonzero_projMat_mul_Theta]
  rw [hsplit]
  have hQ := EKNonzero_norm_Q_le hr σ₁ σ₂
  have hsmul := norm_smul_le ((t : ℂ) - s)
    (BAMss (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₁ σ₂ * BATheta0 (k + 2) L g E m t σ₁ σ₂)
  have hmul := norm_mul_le (BAMss (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₁ σ₂)
    (BATheta0 (k + 2) L g E m t σ₁ σ₂)
  have hmul' : ‖BAMss (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₁ σ₂ * BATheta0 (k + 2) L g E m t σ₁ σ₂‖
      ≤ ‖BATheta0 (k + 2) L g E m t σ₁ σ₂‖ := by
    refine hmul.trans ?_
    calc _ ≤ 1 * ‖BATheta0 (k + 2) L g E m t σ₁ σ₂‖ := mul_le_mul_of_nonneg_right hQ (norm_nonneg _)
      _ = _ := one_mul _
  have hc : ‖(t : ℂ) - s‖ = t - s := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hterm : ‖((t : ℂ) - s) • (BAMss (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₁ σ₂ *
      BATheta0 (k + 2) L g E m t σ₁ σ₂)‖ ≤ C₀ * EKNonzero_E k := by
    calc _ ≤ (t - s) * ‖BATheta0 (k + 2) L g E m t σ₁ σ₂‖ := by
          rw [← hc]
          exact hsmul.trans (mul_le_mul_of_nonneg_left hmul' (norm_nonneg _))
      _ ≤ (t - s) * (C₀ * (g ^ 2 + |1 - t|)⁻¹ * (EKNonzero_E k * (L : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hTheta0 (by linarith)
      _ = (C₀ * EKNonzero_E k) * ((t - s) * ((g ^ 2 + |1 - t|)⁻¹ * (L : ℝ) ^ 2)) := by ring
      _ ≤ (C₀ * EKNonzero_E k) * 1 :=
          mul_le_mul_of_nonneg_left hcoef (by positivity)
      _ = C₀ * EKNonzero_E k := mul_one _
  calc _ ≤ ‖projMat (k + 2) L‖ + ‖((t : ℂ) - s) • (BAMss (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₁ σ₂ *
        BATheta0 (k + 2) L g E m t σ₁ σ₂)‖ := norm_add_le _ _
    _ ≤ 2 + C₀ * EKNonzero_E k := add_le_add norm_projMat_le hterm

end OneIndex

/-! ## 3. `lem:sum_decay_nonzero` at BA -/

/-- **`lem:sum_decay_nonzero` for the block Anderson model** (`A:204-228`, `(sum_res_Ndecay_nonzero)`), loss-free:
the pin `BAEKSumDecayNonzero` for every `(d, n, Λ, κ)`.  Only uniform BA facts are used (`BAReal`, the row sums
of `BAMss`, `baEKSameRow_holds`, `baProp8_holds`); the constant `Ci ^ n` depends on `(d, n, Λ, κ)` only. -/
theorem baEKSumDecayNonzero_holds (d n : ℕ) (Λ κ : ℝ) : BAEKSumDecayNonzero d n Λ κ := by
  intro hd _hn hΛ hκ
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  obtain ⟨Cs, hCs, hsame⟩ := baEKSameRow_holds (k + 2) Λ κ hd hΛ hκ
  obtain ⟨C₀, hC₀, hbd⟩ := baProp8_holds (k + 2) Λ κ hd hΛ hκ
  have hE0 := EKNonzero_E_pos k
  set Ci : ℝ := max Cs (2 + C₀ * EKNonzero_E k) with hCi
  have hCi0 : 0 < Ci := lt_of_lt_of_le hCs (le_max_left _ _)
  refine ⟨Ci ^ n, pow_pos hCi0 n, ?_⟩
  intro L hL g hg hgΛ s t hs hsg hst ht E m hr σ A hA 𝒜
  have : NeZero L := ⟨by omega⟩
  -- the bound of the one-index factor at each `i`
  have key : ∀ i : Fin n,
      ‖(if i ∈ A then projMat (k + 2) L * BAuKer (k + 2) L g E m s t (σ i) (σ (finRotate n i))
          else BAuKer (k + 2) L g E m s t (σ i) (σ (finRotate n i)))‖ ≤ Ci := by
    intro i
    by_cases hi : i ∈ A
    · simp only [hi, ite_true]
      exact (EKNonzero_norm_projMat_mul_uKer_le hC₀ hL hg hr hs hsg hst ht (σ i) (σ (finRotate n i))
        (fun a => hbd L hL g hg hgΛ E m hr t (hs.trans hst) ht (σ i) (σ (finRotate n i)) a)).trans
        (le_max_right _ _)
    · have hσ : σ i = σ (finRotate n i) := by
        by_contra hne
        exact hi (hA i hne)
      simp only [hi, ite_false]
      rw [← hσ]
      exact (hsame L hL g hg hgΛ E m hr (σ i) s t hs hst ht).trans (le_max_left _ _)
  have hUN : BAUN (k + 2) L g E m σ s t 𝒜
      = tensorKer (k + 2) L (fun i : Fin n => BAuKer (k + 2) L g E m s t (σ i) (σ (finRotate n i))) 𝒜 := rfl
  rw [hUN, zeroModeSet_tensorKer]
  calc ‖tensorKer (k + 2) L
        (fun i => if i ∈ A then projMat (k + 2) L * BAuKer (k + 2) L g E m s t (σ i) (σ (finRotate n i))
          else BAuKer (k + 2) L g E m s t (σ i) (σ (finRotate n i))) 𝒜‖
      ≤ (∏ i, ‖(if i ∈ A then projMat (k + 2) L * BAuKer (k + 2) L g E m s t (σ i) (σ (finRotate n i))
          else BAuKer (k + 2) L g E m s t (σ i) (σ (finRotate n i)))‖) * ‖𝒜‖ := norm_tensorKer_le _ _
    _ ≤ (∏ _i : Fin n, Ci) * ‖𝒜‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => key i
    _ = Ci ^ n * ‖𝒜‖ := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ## 4. Compiled nonempty instances (`d = 3`, the flow datum `n = 0` of `sz0`)

The data of `inst_BAEKSumDecayNonzero` (`BA/EKPins.lean:758`), now without the pin as a hypothesis: `L = 4`,
`g₀ = √t₀ λ ≤ 1/64`, `κ = 1/2`, `Λ = 1`, `BAReal` by `hrI`, the window `s = 1 - g₀²/L²`,
`t = 1 - g₀²/(2L²)` (`0 ≤ s ≤ t < 1`), `𝒜 = δ₀` (`AI 0 = 1`).  Every hypothesis is discharged. -/

namespace EKNonzeroInst

open RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.BA.FlowPinsInst RBM.BA.EKPinsInst

/-- the window `0 ≤ s`, `1 - g₀²/L² ≤ s ≤ t < 1` of the instances -/
theorem window_s : 0 ≤ 1 - gI ^ 2 / ((sz0.L 0 : ℕ) : ℝ) ^ 2 := by
  have := gI_sq_le
  linarith

theorem window_st : 1 - gI ^ 2 / ((sz0.L 0 : ℕ) : ℝ) ^ 2 ≤ 1 - gI ^ 2 / (2 * ((sz0.L 0 : ℕ) : ℝ) ^ 2) := by
  have hL4 : (0 : ℝ) < ((sz0.L 0 : ℕ) : ℝ) ^ 2 := by rw [LI_real]; norm_num
  have hq : 0 < gI ^ 2 / ((sz0.L 0 : ℕ) : ℝ) ^ 2 := div_pos (pow_pos gI_pos 2) hL4
  have hst : gI ^ 2 / (2 * ((sz0.L 0 : ℕ) : ℝ) ^ 2) = (gI ^ 2 / ((sz0.L 0 : ℕ) : ℝ) ^ 2) / 2 := by
    field_simp
  rw [hst]
  linarith

theorem window_t : 1 - gI ^ 2 / (2 * ((sz0.L 0 : ℕ) : ℝ) ^ 2) < 1 := by
  have hL4 : (0 : ℝ) < ((sz0.L 0 : ℕ) : ℝ) ^ 2 := by rw [LI_real]; norm_num
  have : 0 < gI ^ 2 / (2 * ((sz0.L 0 : ℕ) : ℝ) ^ 2) := div_pos (pow_pos gI_pos 2) (by positivity)
  linarith

/-- The tensor `δ₀` on `(Z_L^3)^3`. -/
def AI3 : (Fin 3 → Zd 3 (sz0.L 0)) → ℂ := fun a => if a = 0 then 1 else 0

theorem AI3_zero : AI3 0 = 1 := by simp [AI3]

/-- `baEKSumDecayNonzero_holds` at `n = 2`, `σ = (+,-)`, `A = {0, 1} ⊇ I_diff(σ) = {0, 1}`, `𝒜 = δ₀`. -/
theorem inst_baEKSumDecayNonzero_n2 : ∃ C : ℝ, 0 < C ∧ AI 0 = 1 ∧
    ‖zeroModeSet 3 (sz0.L 0) ({0, 1} : Finset (Fin 2)) (BAUN 3 (sz0.L 0) gI EI mI ![true, false]
      (1 - gI ^ 2 / ((sz0.L 0 : ℕ) : ℝ) ^ 2) (1 - gI ^ 2 / (2 * ((sz0.L 0 : ℕ) : ℝ) ^ 2)) AI)‖
        ≤ C * ‖AI‖ := by
  obtain ⟨C, hC, H⟩ := baEKSumDecayNonzero_holds 3 2 1 (1 / 2) (by norm_num) le_rfl one_pos (by norm_num)
  refine ⟨C, hC, AI_zero, H (sz0.L 0) (sz0.three_le_L 0) gI gI_pos (gI_le.trans (by norm_num)) _ _ window_s
    le_rfl window_st window_t EI mI hrI ![true, false] ({0, 1} : Finset (Fin 2)) (fun i _ => by fin_cases i <;> simp) AI⟩

/-- `baEKSumDecayNonzero_holds` at `n = 3`, `σ = (+,+,-)`, `A = {1, 2}` the two sign-change indices: index `0` has
`σ₀ = σ₁`, `0 ∉ A`, so the same-row branch (`baEKSameRow_holds`) is used at index `0` and the `Proj` branch at `1, 2`. -/
theorem inst_baEKSumDecayNonzero_n3 : ∃ C : ℝ, 0 < C ∧ AI3 0 = 1 ∧ (0 : Fin 3) ∉ ({1, 2} : Finset (Fin 3)) ∧
    ‖zeroModeSet 3 (sz0.L 0) ({1, 2} : Finset (Fin 3)) (BAUN 3 (sz0.L 0) gI EI mI ![true, true, false]
      (1 - gI ^ 2 / ((sz0.L 0 : ℕ) : ℝ) ^ 2) (1 - gI ^ 2 / (2 * ((sz0.L 0 : ℕ) : ℝ) ^ 2)) AI3)‖
        ≤ C * ‖AI3‖ := by
  obtain ⟨C, hC, H⟩ := baEKSumDecayNonzero_holds 3 3 1 (1 / 2) (by norm_num) (by norm_num) one_pos (by norm_num)
  refine ⟨C, hC, AI3_zero, by decide, H (sz0.L 0) (sz0.three_le_L 0) gI gI_pos (gI_le.trans (by norm_num)) _ _
    window_s le_rfl window_st window_t EI mI hrI ![true, true, false] ({1, 2} : Finset (Fin 3))
    (by decide) AI3⟩

end EKNonzeroInst

end RBM.BA
