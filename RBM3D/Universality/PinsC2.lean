/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.Step1Good
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum

/-!
# The mean bound and the free-convolution step for the centred model

For the DBM initial matrix `ouInit = a H + (1 - a) μ` (`a = e^{-t*/2}`, `μ` the deterministic mean of the centred
model) the local law needs a tolerance that contains `t*`, and the eigenvalues of `ouInit` are bounded through a
bound on the mean.  This file states `UNTrLocalInit'` (tolerance `W^τ (Bctl + t*)`), the mean bound `UNMeanBound`,
and the statements `UNStep1GoodC''` and `UNCoreC''`; it proves `UNStep1GoodC''` (`step1GoodC''`).

*Why the tolerance contains `t*`.*  The spectrum of `ouInit` is shifted by `O(t*)` against a `τ_s`-independent
`m` (for the band model, `ouInit = e^{-t*/2} H` is dilated by `1 - e^{-t*/2} ≈ t*/2`), so the local law for
`ouInit` cannot have the tolerance `W^τ Bctl` of `UNTrLocalInit` for large `τ_s`.

*Why the mean bound.*  The hypotheses `UNTrLocalInit` (a statement about `stieltjesN (ouInit …)`) and `UNNormBound` (a statement
about `H`) never observe the deterministic mean `μ` of the centred model, but the regularity event reads all
eigenvalues of `ouInit = a H + (1 - a) μ` (condition (2.3) of [LSY, Definition 2.1]).  A change of `μ` by `R_n` in one
eigenvalue moves `stieltjesN` only by `≤ 2/(N Im z)`, below the tolerance.  Hence `UNMeanBound` bounds the mean.

Sections: the statements; elementary helpers (private); matrix facts and the dictionary between `ouInit` and
`mV`; monotonicity in the window; the free-convolution step (strip closeness, regularity, rate, the deterministic
half and the probabilistic statement `step1GoodC''`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal ENNReal ComplexOrder

namespace RBM.Univ

/-! ## The statements -/

section Init

variable {d : ℕ}

/-- **`UNTrLocalInit'`**: `UNTrLocalInit` with the tolerance
`W^τ (Bctl n (1 - Im z) + t*)`, `t* = ouTStar sz τs n`: the spectrum of `ouInit` is shifted by
`O(t*)` against a `τ_s`-independent `m`. -/
def UNTrLocalInit' (sz : Sizes d) (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E δ : ℝ) : Prop :=
  ∀ τs : ℝ, 0 < τs → τs < 1 → ∀ ε τ D : ℝ, 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop,
    M.μ {ω | ∃ z : ℂ, |z.re - E| ≤ δ ∧ Nsz sz n ^ (-1 + ε) ≤ z.im ∧ z.im ≤ 1 ∧
        ((sz.W n : ℕ) : ℝ) ^ τ * (sz.Bctl n (1 - z.im) + ouTStar sz τs n) <
          ‖stieltjesN (ouInit M n (ouTStar sz τs n) ω) z - m n z‖} ≤
      ENNReal.ofReal (Nsz sz n ^ (-D))

/-- **`UNMeanBound`**: the deterministic mean of a centred model has all eigenvalues `≤ N^{CV₀}` in
modulus, eventually.  Band: mean `0`; block Anderson: `‖λΨ‖ ≤ 2d 𝔡⁻¹ ≤ N^{CV₀}` eventually for `CV₀ > 0`. -/
def UNMeanBound (sz : Sizes d) (M : UNModelC sz) (CV₀ : ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ i, |(M.mean_herm n).eigenvalues i| ≤ Nsz sz n ^ CV₀

end Init

/-- **`UNStep1GoodC''`** (proved by `step1GoodC''`): `UNStep1GoodC` with `UNTrLocalInit` replaced by
`UNTrLocalInit'` and `UNMeanBound sz M CV₀` beside `UNNormBound sz M.toUNModel CV₀`. -/
def UNStep1GoodC'' : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
      UNDens' m E ρ δ → UNTrLocalInit' sz M m E δ → ∀ CV₀ : ℝ, 0 ≤ CV₀ → UNNormBound sz M.toUNModel CV₀ → UNMeanBound sz M CV₀ →
      ∀ τs D : ℝ, 0 < τs → τs < 1 → τs ≤ 𝔠 * 𝔡 → 0 < D →
        ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop,
          M.μ {ω | ¬ (IsRegular32 (vOUC sz M n τs E ω) (Nsz sz n ^ (-1 + τs / 4))
                (Nsz sz n ^ (-(min (τs / 4) ((1 - τs) / 3)))) c C (CV₀ + 1) ∧
              ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOUC sz M n τs E ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧
                ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
                  |ρ' - ρ n| ≤ Nsz sz n ^ (-(3 * τs / 8)))} ≤
            ENNReal.ofReal (Nsz sz n ^ (-D))

/-- **`UNCoreC''`**: the dilated universality statement `UNUnivDilAt` for a centred model, from `UNL32`,
`UNGUELocal`, `UNGreenCorrAllC`, `UNDens'`, `UNTrLocal`, `UNTrLocalInit'`, the norm and mean bounds `UNNormBound`,
`UNMeanBound` (at one `CV₀`) and the Claim `UNClaimAllC`. -/
def UNCoreC'' : Prop :=
  UNL32 → UNGUELocal → UNGreenCorrAllC →
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
        UNDens' m E ρ δ → UNTrLocal sz M.toUNModel m E δ → UNTrLocalInit' sz M m E δ →
          (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz M.toUNModel CV₀ ∧ UNMeanBound sz M CV₀) → UNClaimAllC sz M E →
          ∀ E' : ℝ, |E'| < 2 → ∀ k : ℕ, 1 ≤ k → ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
            UNUnivDilAt sz M.toUNModel ρ E E' k O

/-! ## Elementary helpers (private) -/

private theorem PinsC2_one_le_Nsz {d : ℕ} (sz : Sizes d) (n : ℕ) : (1 : ℝ) ≤ Nsz sz n := by
  have h1 : 1 ≤ sz.size n := by
    simp only [Sizes.size]
    have := sz.three_le_L n
    have := sz.W_pos n
    exact Nat.one_le_pow _ _ (Nat.mul_pos (sz.W_pos n) (by omega))
  exact_mod_cast h1

private theorem PinsC2_inv_mul_re (a : ℝ) (X : ℂ) : (((a : ℝ) : ℂ)⁻¹ * X).re = a⁻¹ * X.re := by
  rw [← Complex.ofReal_inv, Complex.re_ofReal_mul]

private theorem PinsC2_inv_mul_im (a : ℝ) (X : ℂ) : (((a : ℝ) : ℂ)⁻¹ * X).im = a⁻¹ * X.im := by
  rw [← Complex.ofReal_inv, Complex.im_ofReal_mul]

private theorem PinsC2_exp_le_one {T : ℝ} (hT : 0 ≤ T) : Real.exp (-T / 2) ≤ 1 := by
  rw [Real.exp_le_one_iff]; linarith

private theorem PinsC2_one_le_inv {T : ℝ} (hT : 0 ≤ T) : 1 ≤ (Real.exp (-T / 2))⁻¹ := by
  rw [one_le_inv₀ (Real.exp_pos _)]
  exact PinsC2_exp_le_one hT

/-- `(e^{-T/2})⁻¹ ≤ 1 + T` for `0 ≤ T ≤ 1`. -/
private theorem PinsC2_inv_le {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    (Real.exp (-T / 2))⁻¹ ≤ 1 + T := by
  have h := Real.add_one_le_exp (-T / 2)
  have h1 : (0 : ℝ) < -T / 2 + 1 := by linarith
  refine (inv_anti₀ h1 h).trans ?_
  rw [inv_le_iff_one_le_mul₀ h1]
  nlinarith

/-- `1 - e^{-T} ≤ T`. -/
private theorem PinsC2_one_sub_exp_le (T : ℝ) : 1 - Real.exp (-T) ≤ T := by
  have := Real.add_one_le_exp (-T); linarith

/-- `T / 2 ≤ 1 - e^{-T}` for `0 ≤ T ≤ 1`. -/
private theorem PinsC2_half_le_one_sub_exp {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    T / 2 ≤ 1 - Real.exp (-T) := by
  have h := Real.add_one_le_exp T
  have h1 : (0 : ℝ) < T + 1 := by linarith
  have h2 : Real.exp (-T) ≤ (T + 1)⁻¹ := by
    rw [Real.exp_neg]; exact inv_anti₀ h1 h
  have h3 : (T + 1)⁻¹ ≤ 1 - T / 2 := by
    rw [inv_le_iff_one_le_mul₀ h1]; nlinarith
  linarith

private theorem PinsC2_one_sub_exp_pos {T : ℝ} (hT : 0 < T) : 0 < 1 - Real.exp (-T) := by
  have : Real.exp (-T) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  linarith

private theorem PinsC2_sqrt_exp (T : ℝ) : Real.sqrt (Real.exp (-T)) = Real.exp (-T / 2) :=
  (Real.exp_half (-T)).symm

private theorem PinsC2_rpow_ev {e c : ℝ} (he : e < 0) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, x ^ e ≤ c := by
  have h := (tendsto_rpow_neg_atTop (y := -e) (by linarith)).eventually (ge_mem_nhds hc)
  simpa using h

/-- `W ≤ N`: `W ≤ W L ≤ (W L)^d` for `d ≥ 1`. -/
private theorem PinsC2_W_le_size {d : ℕ} (sz : Sizes d) (hd : 0 < d) (n : ℕ) :
    ((sz.W n : ℕ) : ℝ) ≤ Nsz sz n := by
  have hL : 0 < sz.L n := by have := sz.three_le_L n; omega
  have h1 : sz.W n ≤ sz.W n * sz.L n := Nat.le_mul_of_pos_right _ hL
  have h2 : sz.W n * sz.L n ≤ (sz.W n * sz.L n) ^ d := Nat.le_self_pow hd.ne' _
  exact_mod_cast h1.trans h2

/-- `W → ∞` along an admissible sequence (`W ≥ N^𝔠` and `N → ∞`). -/
private theorem PinsC2_W_tendsto {d : ℕ} {sz : Sizes d} {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) :
    Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := by
  obtain ⟨h𝔠, -, hN, hB, -⟩ := hA
  have h1 : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop :=
    (tendsto_rpow_atTop h𝔠).comp hN
  exact tendsto_atTop_mono' atTop hB h1

/-- `Bctl (1 - η) ≥ (N η)⁻¹` for `η > 0`: the second summand of `Bparam`. -/
private theorem PinsC2_Bctl_ge {d : ℕ} (sz : Sizes d) (n : ℕ) {η : ℝ} (hη : 0 < η) :
    (Nsz sz n * η)⁻¹ ≤ sz.Bctl n (1 - η) := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    have := sz.three_le_L n; exact_mod_cast (by omega : 0 < sz.L n)
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hN : Nsz sz n = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    unfold Nsz Sizes.size
    push_cast; rw [mul_pow]
  have habs : |1 - (1 - η)| = η := by rw [sub_sub_cancel, abs_of_pos hη]
  unfold Sizes.Bctl Bparam
  rw [habs]
  have e1 : (((0 : ℕ) : ℝ) + 1) ^ (d - 2) = 1 := by simp
  rw [e1, inv_one, mul_one, mul_add]
  have t1 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + η)⁻¹ := by
    have : 0 < sz.lam n ^ 2 + η := by positivity
    positivity
  have t2 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d * η)⁻¹ = (Nsz sz n * η)⁻¹ := by
    rw [hN, ← mul_inv, mul_assoc]
  rw [t2]
  linarith

/-- `Bctl (1 - η) ≥ 0` for `η > 0`. -/
private theorem PinsC2_Bctl_nonneg {d : ℕ} (sz : Sizes d) (n : ℕ) {η : ℝ} (hη : 0 < η) :
    0 ≤ sz.Bctl n (1 - η) := by
  have hN0 : 0 < Nsz sz n := lt_of_lt_of_le one_pos (PinsC2_one_le_Nsz sz n)
  exact (inv_nonneg.2 (by positivity)).trans (PinsC2_Bctl_ge sz n hη)

/-- **The local-law precision at height `y`** (the analogue of `Step1Good_bctl`):
`W^{τ_s/8} Bctl n (1 - y) ≤ N^{-15τ_s/16} + N^{τ_s/8} (N y)⁻¹`, for `τ_s ≤ 𝔠𝔡`, `𝔠 < 1`. -/
private theorem PinsC2_bctl {d : ℕ} (sz : Sizes d) (n : ℕ) {𝔠 𝔡 τs : ℝ} (hd : 0 < d) (h𝔠 : 0 < 𝔠)
    (h𝔠1 : 𝔠 < 1) (h𝔡 : 0 < 𝔡) (hτs : 0 < τs) (hτ𝔠 : τs ≤ 𝔠 * 𝔡) (hN1 : 1 ≤ Nsz sz n)
    (hB : Nsz sz n ^ 𝔠 ≤ (sz.W n : ℝ))
    (hWO : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ sz.lam n) {y : ℝ} (hy : 0 < y) :
    ((sz.W n : ℕ) : ℝ) ^ (τs / 8) * sz.Bctl n (1 - y) ≤
      Nsz sz n ^ (-(15 * τs / 16)) + Nsz sz n ^ (τs / 8) * (Nsz sz n * y)⁻¹ := by
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hApos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) := Real.rpow_pos_of_pos hW0 _
  have hlam := Sizes.lam_sq_mul_pow_ge sz n hWO
  have hb := un_Bctl_le sz n hy hApos hlam
  have hfloor := un_step1_floor hN1 hW1 h𝔠 h𝔠1 h𝔡 hτs hτ𝔠 hB
  have hWN : ((sz.W n : ℕ) : ℝ) ^ (τs / 8) ≤ Nsz sz n ^ (τs / 8) :=
    Real.rpow_le_rpow hW0.le (PinsC2_W_le_size sz hd n) (by linarith)
  have hAinv : (((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡))⁻¹ = ((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡)) :=
    (Real.rpow_neg hW0.le _).symm
  have hy' : 0 ≤ (Nsz sz n * y)⁻¹ := by
    have : 0 < Nsz sz n := by linarith
    positivity
  calc ((sz.W n : ℕ) : ℝ) ^ (τs / 8) * sz.Bctl n (1 - y)
      ≤ ((sz.W n : ℕ) : ℝ) ^ (τs / 8) *
          ((((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡))⁻¹ + (Nsz sz n * y)⁻¹) :=
        mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hW0.le _)
    _ = ((sz.W n : ℕ) : ℝ) ^ (τs / 8) * ((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡)) +
          ((sz.W n : ℕ) : ℝ) ^ (τs / 8) * (Nsz sz n * y)⁻¹ := by rw [hAinv]; ring
    _ ≤ Nsz sz n ^ (-(15 * τs / 16)) + Nsz sz n ^ (τs / 8) * (Nsz sz n * y)⁻¹ :=
        add_le_add hfloor (mul_le_mul_of_nonneg_right hWN hy')


/-! ## Matrix facts and the dictionary for `ouInit` -/

section MatrixFacts

/-- A Hermitian matrix is positive semidefinite iff its real spectrum is nonnegative. -/
private theorem PinsC2_psd_iff {ι : Type} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    X.PosSemidef ↔ ∀ y ∈ spectrum ℝ X, 0 ≤ y := by
  rw [hX.posSemidef_iff_eigenvalues_nonneg, hX.spectrum_real_eq_range_eigenvalues]
  constructor
  · rintro h y ⟨i, rfl⟩
    exact h i
  · intro h i
    exact h _ ⟨i, rfl⟩

private theorem PinsC2_spec_sub {ι : Type} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (R : ℝ) {y : ℝ} :
    y ∈ spectrum ℝ (R • (1 : Matrix ι ι ℂ) - X) ↔ ∃ x ∈ spectrum ℝ X, y = R - x := by
  have h := spectrum.singleton_sub_eq X R
  rw [Algebra.algebraMap_eq_smul_one] at h
  rw [← h]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [Set.mem_singleton_iff] at ha
    exact ⟨b, hb, by rw [ha]⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨R, rfl, x, hx, rfl⟩

private theorem PinsC2_spec_add {ι : Type} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (R : ℝ) {y : ℝ} :
    y ∈ spectrum ℝ (R • (1 : Matrix ι ι ℂ) + X) ↔ ∃ x ∈ spectrum ℝ X, y = R + x := by
  have h := spectrum.singleton_add_eq X R
  rw [Algebra.algebraMap_eq_smul_one] at h
  rw [← h]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [Set.mem_singleton_iff] at ha
    exact ⟨b, hb, by rw [ha]⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨R, rfl, x, hx, rfl⟩

private theorem PinsC2_herm_sub {ι : Type} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ} (hX : X.IsHermitian)
    (R : ℝ) : (R • (1 : Matrix ι ι ℂ) - X).IsHermitian :=
  (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _)).sub hX

private theorem PinsC2_herm_add {ι : Type} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ} (hX : X.IsHermitian)
    (R : ℝ) : (R • (1 : Matrix ι ι ℂ) + X).IsHermitian :=
  (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _)).add hX

/-- `|λ_i(A)| ≤ R` for all `i` iff `R • 1 - A` and `R • 1 + A` are positive semidefinite. -/
private theorem PinsC2_abs_iff_psd {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (R : ℝ) :
    (∀ i, |hA.eigenvalues i| ≤ R) ↔
      (R • (1 : Matrix ι ι ℂ) - A).PosSemidef ∧ (R • (1 : Matrix ι ι ℂ) + A).PosSemidef := by
  rw [PinsC2_psd_iff (PinsC2_herm_sub hA R), PinsC2_psd_iff (PinsC2_herm_add hA R)]
  constructor
  · intro h
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · obtain ⟨x, hx, rfl⟩ := (PinsC2_spec_sub A R).1 hy
      rw [hA.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      linarith [(abs_le.1 (h i)).2]
    · obtain ⟨x, hx, rfl⟩ := (PinsC2_spec_add A R).1 hy
      rw [hA.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      linarith [(abs_le.1 (h i)).1]
  · rintro ⟨h1, h2⟩ i
    have hmem : hA.eigenvalues i ∈ spectrum ℝ A := hA.eigenvalues_mem_spectrum_real i
    have a1 := h1 (R - hA.eigenvalues i) ((PinsC2_spec_sub A R).2 ⟨_, hmem, rfl⟩)
    have a2 := h2 (R + hA.eigenvalues i) ((PinsC2_spec_add A R).2 ⟨_, hmem, rfl⟩)
    exact abs_le.2 ⟨by linarith, by linarith⟩

/-- **Weyl for a convex combination** (proof outline: `|λ_i| ≤ R` for all `i` iff `R • 1 ∓ A` positive semidefinite;
`R • 1 - C = a (R • 1 - A) + (1 - a) (R • 1 - B)`).  Used for `ouInit = a H + (1 - a) μ`. -/
theorem un_eigenvalues_abs_le_convex :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {A B C : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
      (hC : C.IsHermitian) {a R : ℝ}, 0 ≤ a → a ≤ 1 → C = a • A + (1 - a) • B →
        (∀ i, |hA.eigenvalues i| ≤ R) → (∀ i, |hB.eigenvalues i| ≤ R) → ∀ i, |hC.eigenvalues i| ≤ R := by
  intro ι _ _ A B C hA hB hC a R ha0 ha1 hCeq hAR hBR
  obtain ⟨hA1, hA2⟩ := (PinsC2_abs_iff_psd hA R).1 hAR
  obtain ⟨hB1, hB2⟩ := (PinsC2_abs_iff_psd hB R).1 hBR
  rw [PinsC2_abs_iff_psd hC R]
  have e1 : R • (1 : Matrix ι ι ℂ) - C = a • (R • (1 : Matrix ι ι ℂ) - A) + (1 - a) • (R • (1 : Matrix ι ι ℂ) - B) := by
    rw [hCeq]; module
  have e2 : R • (1 : Matrix ι ι ℂ) + C = a • (R • (1 : Matrix ι ι ℂ) + A) + (1 - a) • (R • (1 : Matrix ι ι ℂ) + B) := by
    rw [hCeq]; module
  refine ⟨?_, ?_⟩
  · rw [e1]; exact (hA1.smul ha0).add (hB1.smul (by linarith))
  · rw [e2]; exact (hA2.smul ha0).add (hB2.smul (by linarith))

/-- `|(a - z)⁻¹| ≤ 1 / Im z`. -/
private theorem PinsC2_norm_inv_le (a : ℝ) {z : ℂ} (hz : 0 < z.im) : ‖((a : ℂ) - z)⁻¹‖ ≤ 1 / z.im := by
  rw [norm_inv]
  have h1 : z.im ≤ ‖(a : ℂ) - z‖ := by
    have := Complex.abs_im_le_norm ((a : ℂ) - z)
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at this
    rwa [abs_of_pos hz] at this
  rw [one_div]
  exact inv_anti₀ hz h1

/-- The `η`-Lipschitz bridge on a vertical line (`stieltjesN_eq_mV`, termwise
`|(λ - z)⁻¹ - (λ - z')⁻¹| ≤ |z - z'| / (Im z Im z')`). -/
theorem stieltjesN_vert_le :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}, H.IsHermitian → ∀ (x y y' : ℝ), 0 < y → 0 < y' →
      ‖stieltjesN H ⟨x, y⟩ - stieltjesN H ⟨x, y'⟩‖ ≤ |y - y'| / (y * y') := by
  intro ι _ _ H hH x y y' hy hy'
  rw [stieltjesN_eq_mV hH (z := ⟨x, y⟩) hy, stieltjesN_eq_mV hH (z := ⟨x, y'⟩) hy']
  unfold mV
  have hterm : ∀ i : ι, ‖((hH.eigenvalues i : ℂ) - ⟨x, y⟩)⁻¹ - ((hH.eigenvalues i : ℂ) - ⟨x, y'⟩)⁻¹‖ ≤
      |y - y'| / (y * y') := by
    intro i
    set l : ℝ := hH.eigenvalues i
    have hz1 : (⟨x, y⟩ : ℂ) ≠ (l : ℂ) := fun h => by
      have := congrArg Complex.im h; simp at this; linarith
    have hne1 : (l : ℂ) - ⟨x, y⟩ ≠ 0 := sub_ne_zero.2 hz1.symm
    have hne2 : (l : ℂ) - ⟨x, y'⟩ ≠ 0 := by
      intro h
      have := congrArg Complex.im h; simp at this; linarith
    have e : ((l : ℂ) - ⟨x, y⟩)⁻¹ - ((l : ℂ) - ⟨x, y'⟩)⁻¹ =
        ((l : ℂ) - ⟨x, y⟩)⁻¹ * ((l : ℂ) - ⟨x, y'⟩)⁻¹ * (((l : ℂ) - ⟨x, y'⟩) - ((l : ℂ) - ⟨x, y⟩)) := by
      field_simp
    rw [e, norm_mul, norm_mul]
    have h1 : ‖((l : ℂ) - ⟨x, y⟩)⁻¹‖ ≤ 1 / y := PinsC2_norm_inv_le l (z := ⟨x, y⟩) hy
    have h2 : ‖((l : ℂ) - ⟨x, y'⟩)⁻¹‖ ≤ 1 / y' := PinsC2_norm_inv_le l (z := ⟨x, y'⟩) hy'
    have h3 : ‖((l : ℂ) - ⟨x, y'⟩) - ((l : ℂ) - ⟨x, y⟩)‖ = |y - y'| := by
      have : ((l : ℂ) - ⟨x, y'⟩) - ((l : ℂ) - ⟨x, y⟩) = ((y - y' : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [h3]
    calc ‖((l : ℂ) - ⟨x, y⟩)⁻¹‖ * ‖((l : ℂ) - ⟨x, y'⟩)⁻¹‖ * |y - y'|
        ≤ (1 / y) * (1 / y') * |y - y'| :=
          mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) (abs_nonneg _)
      _ = |y - y'| / (y * y') := by field_simp
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
  · rw [h0]; simp only [Nat.cast_zero, _root_.inv_zero, zero_mul, sub_self, norm_zero]; positivity
  · have hc : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hpos
    rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_inv, Complex.norm_natCast]
    calc (Fintype.card ι : ℝ)⁻¹ * ‖∑ i, (((hH.eigenvalues i : ℂ) - ⟨x, y⟩)⁻¹ - ((hH.eigenvalues i : ℂ) - ⟨x, y'⟩)⁻¹)‖
        ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ i : ι, |y - y'| / (y * y') :=
          mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hterm i)) (by positivity)
      _ = |y - y'| / (y * y') := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp

/-- The spectral dictionary `mV (λ(A) - E) (w) = stieltjesN A (w + E)` for a Hermitian `A`. -/
private theorem PinsC2_mV_shift {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (E : ℝ) {w : ℂ} (hw : 0 < w.im) :
    mV (fun i => hA.eigenvalues i - E) w = stieltjesN A (w + (E : ℂ)) := by
  have hz : 0 < (w + (E : ℂ)).im := by
    rw [Complex.add_im, Complex.ofReal_im, add_zero]; exact hw
  rw [stieltjesN_eq_mV hA hz]
  unfold mV
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  push_cast
  ring

/-- `stieltjesN (a H) z = a⁻¹ stieltjesN H (a⁻¹ z)` (`Gres`; `a H - z = a (H - a⁻¹ z)`, `Ring.inverse_mul`). -/
private theorem PinsC2_stieltjesN_smul {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) {a : ℂ}
    (ha : a ≠ 0) (z : ℂ) : stieltjesN (a • H) z = a⁻¹ * stieltjesN H (a⁻¹ * z) := by
  unfold stieltjesN Gres
  simp only [ite_true]
  have hmat : a • H - z • (1 : Matrix ι ι ℂ) = (a • (1 : Matrix ι ι ℂ)) * (H - ((a⁻¹ * z) • (1 : Matrix ι ι ℂ))) := by
    rw [Matrix.smul_mul, Matrix.one_mul, smul_sub, smul_smul, mul_inv_cancel_left₀ ha]
  have hu : IsUnit (a • (1 : Matrix ι ι ℂ)) := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (isUnit_iff_ne_zero.2 ha).map _
  have hinv : Ring.inverse (a • (1 : Matrix ι ι ℂ)) = a⁻¹ • (1 : Matrix ι ι ℂ) := by
    rw [← Matrix.nonsing_inv_eq_ringInverse]
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ ha, one_smul]
  rw [hmat, Ring.inverse_mul (Or.inl hu), hinv, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul]
  simp only [smul_eq_mul]
  ring

end MatrixFacts

/-! ## Monotonicity in the window -/

/-- `2 X B ≤ X² B` for `X ≥ 2`, `B ≥ 0`. -/
private theorem PinsC2_aux1 {X B : ℝ} (hX : 2 ≤ X) (hB : 0 ≤ B) : 2 * (X * B) ≤ X * X * B := by
  have h : 2 * X ≤ X * X := by nlinarith
  calc 2 * (X * B) = (2 * X) * B := by ring
    _ ≤ (X * X) * B := mul_le_mul_of_nonneg_right h hB

/-- `T C ≤ X² T` for `C ≤ X`, `X ≥ 1`, `T ≥ 0`. -/
private theorem PinsC2_aux2 {X T Cb : ℝ} (hX : 1 ≤ X) (hC : Cb ≤ X) (hT : 0 ≤ T) : T * Cb ≤ X * X * T := by
  have h : Cb ≤ X * X := by nlinarith
  calc T * Cb ≤ T * (X * X) := mul_le_mul_of_nonneg_left h hT
    _ = X * X * T := by ring

/-! ## Norms of vertical points -/

/-- The norm of `(y : ℝ) * I`. -/
private theorem PinsC2_norm_re_zero (y : ℝ) : ‖((y : ℝ) : ℂ) * Complex.I‖ = |y| := by
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

set_option maxHeartbeats 1000000 in
/-! ## The free-convolution step -/

/-- **The closeness hypothesis of `freeConv_stable_lip`** on the strip, for the initial matrix `A` (the
analogue of `Step1Good_strip` with `v = λ(A) - E`, no `e^{-T/2}` factor in the dictionary, the local law at the tolerance
`N^{-15τ_s/16} + N^{τ_s/8} (N y)⁻¹ + N^{-1+9τ_s/8}` and the bridge term `T (K + Lp (|E| + δ + 1))` of
`‖m ζ - a⁻¹ m (a⁻¹ ζ)‖`): for `|Re w| ≤ c₁`, `c₀ t/4 ≤ Im w ≤ 1/2`. -/
private theorem PinsC2_strip {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (mr : ℂ → ℂ) {N T E δ τs c₀ c₁ K Lp : ℝ}
    (hN1 : 1 ≤ N) (hc₀ : 0 < c₀) (hδ : 0 < δ) (hc₁ : c₁ ≤ δ / 4) (hK0 : 0 ≤ K) (hLp0 : 0 ≤ Lp)
    (hTN : T = N ^ (-1 + τs)) (hT1 : T ≤ 1 / 2) (hET : |E| * T ≤ δ / 4)
    (hedge : N ^ (-1 + τs / 8) ≤ c₀ / 8 * T)
    (hK : ∀ z : ℂ, |z.re - E| ≤ δ → 0 < z.im → z.im ≤ 1 → ‖mr z‖ ≤ K)
    (hlip : ∀ z z' : ℂ, |z.re - E| ≤ δ → 0 < z.im → z.im ≤ 1 →
      |z'.re - E| ≤ δ → 0 < z'.im → z'.im ≤ 1 → ‖mr z - mr z'‖ ≤ Lp * ‖z - z'‖)
    (hpt : ∀ ζ : ℂ, |ζ.re - E| ≤ δ → N ^ (-1 + τs / 8) ≤ ζ.im → ζ.im ≤ 1 →
      ‖stieltjesN A ζ - mr ζ‖ ≤ N ^ (-(15 * τs / 16)) + N ^ (τs / 8) * (N * ζ.im)⁻¹ + N ^ (-1 + 9 * τs / 8))
    {w : ℂ} (hw : |w.re| ≤ c₁) (hlow : c₀ * (1 - Real.exp (-T)) / 4 ≤ w.im) (hw1 : w.im ≤ 1 / 2) :
    ‖mV (fun i => hA.eigenvalues i - E) w -
        (Real.sqrt (Real.exp (-T)) : ℂ)⁻¹ * mr ((Real.sqrt (Real.exp (-T)) : ℂ)⁻¹ * (w + E))‖ ≤
      (N ^ (-(15 * τs / 16)) + 8 * c₀⁻¹ * N ^ (-(7 * τs / 8))) + N ^ (-1 + 9 * τs / 8) +
        (K + Lp * (|E| + δ + 1)) * T := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hTpos : 0 < T := by rw [hTN]; exact Real.rpow_pos_of_pos hN0 _
  have hT1' : T ≤ 1 := by linarith
  rw [PinsC2_sqrt_exp]
  have ha0 : 0 < Real.exp (-T / 2) := Real.exp_pos _
  have hainv : (Real.exp (-T / 2))⁻¹ ≤ 1 + T := PinsC2_inv_le hTpos.le hT1'
  have hainv1 : 1 ≤ (Real.exp (-T / 2))⁻¹ := PinsC2_one_le_inv hTpos.le
  have hhalf := PinsC2_half_le_one_sub_exp hTpos.le hT1'
  have hy : c₀ / 8 * T ≤ w.im := by
    have : c₀ / 8 * T ≤ c₀ * (1 - Real.exp (-T)) / 4 := by nlinarith
    exact this.trans hlow
  have hy0 : 0 < c₀ / 8 * T := by positivity
  have hw0 : 0 < w.im := lt_of_lt_of_le hy0 hy
  have hc₁0 : 0 ≤ c₁ := (abs_nonneg _).trans hw
  have hdict : mV (fun i => hA.eigenvalues i - E) w = stieltjesN A (w + (E : ℂ)) := PinsC2_mV_shift hA E hw0
  rw [hdict]
  set a : ℝ := Real.exp (-T / 2) with ha
  set ζ : ℂ := w + (E : ℂ) with hζ
  set ζ' : ℂ := ((a : ℝ) : ℂ)⁻¹ * ζ with hζ'
  have hζre : ζ.re = w.re + E := by rw [hζ, Complex.add_re, Complex.ofReal_re]
  have hζim : ζ.im = w.im := by rw [hζ, Complex.add_im, Complex.ofReal_im, add_zero]
  have hζ're : ζ'.re = a⁻¹ * (w.re + E) := by rw [hζ', PinsC2_inv_mul_re, hζre]
  have hζ'im : ζ'.im = a⁻¹ * w.im := by rw [hζ', PinsC2_inv_mul_im, hζim]
  have hζdom : |ζ.re - E| ≤ δ := by
    rw [hζre]; have : w.re + E - E = w.re := by ring
    rw [this]; linarith
  have hζ'dom : |ζ'.re - E| ≤ δ := by
    rw [hζ're]
    have e1 : a⁻¹ * (w.re + E) - E = a⁻¹ * w.re + (a⁻¹ - 1) * E := by ring
    rw [e1]
    have h1 : |a⁻¹ * w.re| ≤ (1 + T) * c₁ := by
      rw [abs_mul, abs_of_pos (inv_pos.2 ha0)]
      exact mul_le_mul hainv hw (abs_nonneg _) (by linarith)
    have h2 : |(a⁻¹ - 1) * E| ≤ T * |E| := by
      rw [abs_mul, abs_of_nonneg (by linarith)]
      exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    calc |a⁻¹ * w.re + (a⁻¹ - 1) * E| ≤ |a⁻¹ * w.re| + |(a⁻¹ - 1) * E| := abs_add_le _ _
      _ ≤ (1 + T) * c₁ + T * |E| := add_le_add h1 h2
      _ ≤ δ := by nlinarith [abs_nonneg E]
  have hζ'pos : 0 < ζ'.im := by rw [hζ'im]; positivity
  have hζ'le : ζ'.im ≤ 1 := by
    rw [hζ'im]
    calc a⁻¹ * w.im ≤ (1 + T) * (1 / 2) := mul_le_mul hainv hw1 hw0.le (by linarith)
      _ ≤ 1 := by linarith
  have hζpos : 0 < ζ.im := by rw [hζim]; exact hw0
  have hζle : ζ.im ≤ 1 := by rw [hζim]; linarith
  have hdomlo : N ^ (-1 + τs / 8) ≤ ζ.im := by rw [hζim]; exact hedge.trans hy
  have herrz := hpt ζ hζdom hdomlo hζle
  -- `(N Im ζ)⁻¹ ≤ 8 c₀⁻¹ N^{-τs}`
  have hNT : N * T = N ^ τs := by
    have : N ^ (1 + (-1 + τs)) = N * N ^ (-1 + τs) := by rw [Real.rpow_add hN0, Real.rpow_one]
    rw [hTN, ← this]; congr 1; ring
  have hinv : (N * ζ.im)⁻¹ ≤ 8 * c₀⁻¹ * (N ^ τs)⁻¹ := by
    have h1 : N * (c₀ / 8 * T) ≤ N * ζ.im := by
      rw [hζim]; exact mul_le_mul_of_nonneg_left hy hN0.le
    have h2 : 0 < N * (c₀ / 8 * T) := by positivity
    refine (inv_anti₀ h2 h1).trans (le_of_eq ?_)
    rw [← hNT]
    have : N * (c₀ / 8 * T) = c₀ / 8 * (N * T) := by ring
    rw [this, mul_inv, inv_div]
    have hNTpos : 0 < N * T := by positivity
    field_simp
  have hsplit : N ^ (τs / 8) * (N ^ τs)⁻¹ = N ^ (-(7 * τs / 8)) := by
    rw [← Real.rpow_neg hN0.le, ← Real.rpow_add hN0]; congr 1; ring
  have herr' : ‖stieltjesN A ζ - mr ζ‖ ≤
      (N ^ (-(15 * τs / 16)) + 8 * c₀⁻¹ * N ^ (-(7 * τs / 8))) + N ^ (-1 + 9 * τs / 8) := by
    refine herrz.trans ?_
    have hNa : 0 ≤ N ^ (τs / 8) := Real.rpow_nonneg hN0.le _
    have h1 : N ^ (τs / 8) * (N * ζ.im)⁻¹ ≤ 8 * c₀⁻¹ * N ^ (-(7 * τs / 8)) := by
      calc N ^ (τs / 8) * (N * ζ.im)⁻¹ ≤ N ^ (τs / 8) * (8 * c₀⁻¹ * (N ^ τs)⁻¹) :=
            mul_le_mul_of_nonneg_left hinv hNa
        _ = 8 * c₀⁻¹ * (N ^ (τs / 8) * (N ^ τs)⁻¹) := by ring
        _ = _ := by rw [hsplit]
    linarith
  -- the bridge `‖m ζ - a⁻¹ m (a⁻¹ ζ)‖ ≤ T (K + Lp (|E| + δ + 1))`
  have hmζ' : ‖mr ζ'‖ ≤ K := hK ζ' hζ'dom hζ'pos hζ'le
  have hζζ' : ‖ζ - ζ'‖ ≤ T * (|E| + δ + 1) := by
    have e : ζ - ζ' = (((1 - a⁻¹ : ℝ) : ℂ)) * ζ := by
      rw [hζ']; push_cast; ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    have hζn : ‖ζ‖ ≤ |E| + δ + 1 := by
      refine (Complex.norm_le_abs_re_add_abs_im ζ).trans ?_
      rw [abs_of_pos hζpos, hζre]
      have : |w.re + E| ≤ |E| + δ := by
        calc |w.re + E| ≤ |w.re| + |E| := abs_add_le _ _
          _ ≤ δ + |E| := by linarith
          _ = |E| + δ := add_comm _ _
      linarith
    exact mul_le_mul (by linarith) hζn (norm_nonneg _) hTpos.le
  have hm1 : ‖mr ζ - mr ζ'‖ ≤ Lp * (T * (|E| + δ + 1)) :=
    (hlip ζ ζ' hζdom hζpos hζle hζ'dom hζ'pos hζ'le).trans (mul_le_mul_of_nonneg_left hζζ' hLp0)
  have hm2 : ‖mr ζ' - ((a : ℝ) : ℂ)⁻¹ * mr ζ'‖ ≤ T * K := by
    have e : mr ζ' - ((a : ℝ) : ℂ)⁻¹ * mr ζ' = (((1 - a⁻¹ : ℝ) : ℂ)) * mr ζ' := by
      push_cast; ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    exact mul_le_mul (by linarith) hmζ' (norm_nonneg _) hTpos.le
  have hbridge : ‖mr ζ - ((a : ℝ) : ℂ)⁻¹ * mr ζ'‖ ≤ (K + Lp * (|E| + δ + 1)) * T := by
    have e : mr ζ - ((a : ℝ) : ℂ)⁻¹ * mr ζ' = (mr ζ - mr ζ') + (mr ζ' - ((a : ℝ) : ℂ)⁻¹ * mr ζ') := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    nlinarith
  have e2 : stieltjesN A ζ - ((a : ℝ) : ℂ)⁻¹ * mr ζ' =
      (stieltjesN A ζ - mr ζ) + (mr ζ - ((a : ℝ) : ℂ)⁻¹ * mr ζ') := by ring
  rw [e2]
  refine (norm_add_le _ _).trans ?_
  linarith


/-- **The regularity part** (the analogue of `Step1Good_regular`): regularity ((2.2), (2.3) of [LSY, Definition 2.1])
of `v = λ(A) - E` with `g = N^{-1+τ_s/4}`, `c = c_box/40`, `C = 2K + c_box + 2`, `CV = CV₀ + 1`, from the
local law at the points `x + E + iη` (`η ≤ 1/2`: `Im m_V ∈ [c_box/2, K + c_box/2]`; `1/2 < η ≤ 10`: `η Im m_V`
nondecreasing and `Im m_V ≤ 1/η`) and from `|λ_i(A)| ≤ N^{CV₀}`. -/
private theorem PinsC2_regular {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (mr : ℂ → ℂ) {N T E δ τs cb K CV₀ G : ℝ}
    (hN : |E| + 2 ≤ N) (hcard : (Fintype.card ι : ℝ) = N) (hcb : 0 < cb) (hK : 0 < K) (hδ : 0 < δ)
    (hτs : 0 < τs) (hTN : T = N ^ (-1 + τs)) (hT1 : T ≤ 1 / 2) (hG : G ≤ δ)
    (hbox : ∀ z : ℂ, |z.re - E| ≤ δ → 0 < z.im → z.im ≤ 1 → cb ≤ (mr z).im ∧ ‖mr z‖ ≤ K)
    (hpt : ∀ ζ : ℂ, |ζ.re - E| ≤ δ → N ^ (-1 + τs / 8) ≤ ζ.im → ζ.im ≤ 1 →
      ‖stieltjesN A ζ - mr ζ‖ ≤ N ^ (-(15 * τs / 16)) + N ^ (τs / 8) * (N * ζ.im)⁻¹ + N ^ (-1 + 9 * τs / 8))
    (herr : N ^ (-(15 * τs / 16)) + N ^ (-(τs / 8)) + N ^ (-1 + 9 * τs / 8) ≤ cb / 2)
    (hnorm : ∀ i, |hA.eigenvalues i| ≤ N ^ CV₀) (hCV : 0 ≤ CV₀) :
    IsRegular32 (fun i => hA.eigenvalues i - E) (N ^ (-1 + τs / 4)) G
      (cb / 40) (2 * K + cb + 2) (CV₀ + 1) := by
  have hN1 : (1 : ℝ) ≤ N := by linarith [abs_nonneg E]
  have hN0 : (0 : ℝ) < N := by linarith
  have hTpos : 0 < T := by rw [hTN]; exact Real.rpow_pos_of_pos hN0 _
  have hgpos : 0 < N ^ (-1 + τs / 4) := Real.rpow_pos_of_pos hN0 _
  have hg12 : N ^ (-1 + τs / 4) ≤ 1 / 2 := by
    calc N ^ (-1 + τs / 4) ≤ N ^ (-1 + τs) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = T := hTN.symm
      _ ≤ 1 / 2 := hT1
  have hK0 : 0 < K := hK
  -- the bulk claim: `η ≤ 1/2`
  have hmain : ∀ E' η : ℝ, |E'| ≤ G → N ^ (-1 + τs / 4) ≤ η → η ≤ 1 / 2 →
      cb / 2 ≤ (mV (fun i => hA.eigenvalues i - E) ⟨E', η⟩).im ∧
        (mV (fun i => hA.eigenvalues i - E) ⟨E', η⟩).im ≤ K + cb / 2 := by
    intro E' η hE' hgη hη1
    have hη0 : 0 < η := lt_of_lt_of_le hgpos hgη
    set ζ : ℂ := (⟨E', η⟩ : ℂ) + (E : ℂ) with hζ
    have hzre : ζ.re = E' + E := by rw [hζ, Complex.add_re, Complex.ofReal_re]
    have hzim : ζ.im = η := by rw [hζ, Complex.add_im, Complex.ofReal_im, add_zero]
    have hdomre : |ζ.re - E| ≤ δ := by
      rw [hzre]; have : E' + E - E = E' := by ring
      rw [this]; linarith
    have hgg : N ^ (-1 + τs / 8) ≤ N ^ (-1 + τs / 4) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hdomlo : N ^ (-1 + τs / 8) ≤ ζ.im := by rw [hzim]; exact hgg.trans hgη
    have hzpos : 0 < ζ.im := by rw [hzim]; exact hη0
    have hdomhi : ζ.im ≤ 1 := by rw [hzim]; linarith
    have herrz := hpt ζ hdomre hdomlo hdomhi
    have hNg : N * N ^ (-1 + τs / 4) = N ^ (τs / 4) := by
      have : N ^ (1 + (-1 + τs / 4)) = N * N ^ (-1 + τs / 4) := by rw [Real.rpow_add hN0, Real.rpow_one]
      rw [← this]; congr 1; ring
    have hinv : (N * ζ.im)⁻¹ ≤ (N ^ (τs / 4))⁻¹ := by
      rw [← hNg]
      exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left (by rw [hzim]; exact hgη) hN0.le)
    have hsplit : N ^ (τs / 8) * (N ^ (τs / 4))⁻¹ = N ^ (-(τs / 8)) := by
      rw [← Real.rpow_neg hN0.le, ← Real.rpow_add hN0]; congr 1; ring
    have hloc : ‖stieltjesN A ζ - mr ζ‖ ≤ cb / 2 := by
      refine herrz.trans (le_trans ?_ herr)
      have hNa : 0 ≤ N ^ (τs / 8) := Real.rpow_nonneg hN0.le _
      have : N ^ (τs / 8) * (N * ζ.im)⁻¹ ≤ N ^ (-(τs / 8)) := by
        calc N ^ (τs / 8) * (N * ζ.im)⁻¹ ≤ N ^ (τs / 8) * (N ^ (τs / 4))⁻¹ :=
              mul_le_mul_of_nonneg_left hinv hNa
          _ = _ := hsplit
      linarith
    obtain ⟨hb1, hb2⟩ := hbox ζ hdomre hzpos hdomhi
    have hIm : |(stieltjesN A ζ).im - (mr ζ).im| ≤ cb / 2 := by
      calc |(stieltjesN A ζ).im - (mr ζ).im| = |(stieltjesN A ζ - mr ζ).im| := by rw [Complex.sub_im]
        _ ≤ ‖stieltjesN A ζ - mr ζ‖ := Complex.abs_im_le_norm _
        _ ≤ cb / 2 := hloc
    have hmrim : (mr ζ).im ≤ K := (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans hb2)
    obtain ⟨h1, h2⟩ := abs_le.mp hIm
    have hdict : mV (fun i => hA.eigenvalues i - E) ⟨E', η⟩ = stieltjesN A ζ :=
      PinsC2_mV_shift hA E (w := ⟨E', η⟩) hη0
    rw [hdict]
    exact ⟨by linarith, by linarith⟩
  refine ⟨?_, ?_⟩
  · intro E' η hE' hgη hη10
    have hη0 : 0 < η := lt_of_lt_of_le hgpos hgη
    by_cases hη12 : η ≤ 1 / 2
    · obtain ⟨h1, h2⟩ := hmain E' η hE' hgη hη12
      exact ⟨by linarith, by linarith⟩
    · have hη12' : 1 / 2 < η := not_le.mp hη12
      obtain ⟨hl, -⟩ := hmain E' (1 / 2) hE' hg12 le_rfl
      have hmono := mV_eta_mul_im_mono
        (fun i => hA.eigenvalues i - E) E' (1 / 2) η (by norm_num) hη12'.le
      set S := (mV (fun i => hA.eigenvalues i - E) ⟨E', η⟩).im with hS
      have h4 : cb / 4 ≤ η * S := by nlinarith
      have hSpos : 0 < S := by
        by_contra hneg
        push Not at hneg
        nlinarith [mul_nonneg hη0.le (neg_nonneg.2 hneg)]
      refine ⟨?_, ?_⟩
      · nlinarith [mul_le_mul_of_nonneg_right hη10 hSpos.le]
      · have hle := mV_im_le_inv (fun i => hA.eigenvalues i - E) E' η hη0
        have : 1 / η ≤ 2 := by
          rw [div_le_iff₀ hη0]; linarith
        linarith
  · intro i
    rw [hcard]
    have hlam := hnorm i
    have h1 : |hA.eigenvalues i - E| ≤ N ^ CV₀ + |E| := by
      calc |hA.eigenvalues i - E| ≤ |hA.eigenvalues i| + |E| := abs_sub _ _
        _ ≤ N ^ CV₀ + |E| := by linarith
    have hx1 : (1 : ℝ) ≤ N ^ CV₀ := Real.one_le_rpow hN1 hCV
    have hpow : N ^ (CV₀ + 1) = N ^ CV₀ * N := by rw [Real.rpow_add hN0, Real.rpow_one]
    rw [hpow]
    nlinarith [mul_le_mul_of_nonneg_right hx1 (by linarith [abs_nonneg E] : (0 : ℝ) ≤ N - 1)]

/-- The size conditions of the rate: `C₀ (ε + 2T) ≤ N^{-3τ_s/8}` for
`ε = (N^{-15τ_s/16} + 8 c₀⁻¹ N^{-7τ_s/8}) + N^{-1+9τ_s/8} + Kb T`, `T = N^{-1+τ_s}`; the four exponent gaps `9τ_s/16`,
`τ_s/2`, `1 - 3τ_s/2`, `1 - 11τ_s/8` (positive iff `τ_s < 2/3`). -/
private theorem PinsC2_rate {N τs C₀ c₀ Kb : ℝ} (hN0 : 0 < N) (hC₀ : 0 < C₀) (hc₀ : 0 < c₀) (hKb : 0 ≤ Kb)
    (h1 : N ^ (-(9 * τs / 16)) ≤ 1 / (5 * C₀)) (h2 : N ^ (-(τs / 2)) ≤ c₀ / (40 * C₀))
    (h3 : N ^ (-(1 - 3 * τs / 2)) ≤ 1 / (5 * C₀))
    (h4 : N ^ (-(1 - 11 * τs / 8)) ≤ 1 / (5 * C₀ * (Kb + 1))) :
    C₀ * ((N ^ (-(15 * τs / 16)) + 8 * c₀⁻¹ * N ^ (-(7 * τs / 8))) + N ^ (-1 + 9 * τs / 8) +
        Kb * N ^ (-1 + τs) + N ^ (-1 + τs)) ≤ N ^ (-(3 * τs / 8)) := by
  have hX : 0 < N ^ (-(3 * τs / 8)) := Real.rpow_pos_of_pos hN0 _
  have eA : N ^ (-(15 * τs / 16)) = N ^ (-(9 * τs / 16)) * N ^ (-(3 * τs / 8)) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have eB : N ^ (-(7 * τs / 8)) = N ^ (-(τs / 2)) * N ^ (-(3 * τs / 8)) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have eC : N ^ (-1 + 9 * τs / 8) = N ^ (-(1 - 3 * τs / 2)) * N ^ (-(3 * τs / 8)) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have eD : N ^ (-1 + τs) = N ^ (-(1 - 11 * τs / 8)) * N ^ (-(3 * τs / 8)) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  set X := N ^ (-(3 * τs / 8)) with hXdef
  set p := N ^ (-(9 * τs / 16)) with hp
  set q := N ^ (-(τs / 2)) with hq
  set r := N ^ (-(1 - 3 * τs / 2)) with hr
  set r' := N ^ (-(1 - 11 * τs / 8)) with hr'
  rw [eA, eB, eC, eD]
  have q1 : p * (5 * C₀) ≤ 1 := (le_div_iff₀ (by positivity)).1 h1
  have q2 : q * (40 * C₀) ≤ c₀ := (le_div_iff₀ (by positivity)).1 h2
  have q3 : r * (5 * C₀) ≤ 1 := (le_div_iff₀ (by positivity)).1 h3
  have q4 : r' * (5 * C₀ * (Kb + 1)) ≤ 1 := (le_div_iff₀ (by positivity)).1 h4
  have hq2 : c₀⁻¹ * (q * (40 * C₀)) ≤ 1 := by
    calc c₀⁻¹ * (q * (40 * C₀)) ≤ c₀⁻¹ * c₀ := mul_le_mul_of_nonneg_left q2 (by positivity)
      _ = 1 := inv_mul_cancel₀ hc₀.ne'
  have hs : C₀ * p + 8 * C₀ * c₀⁻¹ * q + C₀ * r + C₀ * (Kb + 1) * r' ≤ 1 := by
    have e : 8 * C₀ * c₀⁻¹ * q = c₀⁻¹ * (q * (40 * C₀)) / 5 := by ring
    rw [e]
    nlinarith
  calc C₀ * ((p * X + 8 * c₀⁻¹ * (q * X)) + r * X + Kb * (r' * X) + r' * X)
      = X * (C₀ * p + 8 * C₀ * c₀⁻¹ * q + C₀ * r + C₀ * (Kb + 1) * r') := by ring
    _ ≤ X * 1 := mul_le_mul_of_nonneg_left hs hX.le
    _ = X := mul_one _


/-- **The deterministic half at one `n`** (the analogue of `Step1Good_at_n`): all the size conditions
are hypotheses.  Regularity from `PinsC2_regular`; the free-convolution part from `freeConv_stable_lip` (the
three conjuncts used) with the strip closeness `PinsC2_strip` at `ε = (N^{-15τ_s/16} + 8 c₀⁻¹ N^{-7τ_s/8}) +
N^{-1+9τ_s/8} + Kb T`, and `ρ₀ = ρ_n` by uniqueness of limits. -/
private theorem PinsC2_at_n {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (mr : ℂ → ℂ) (ρn : ℝ) {N T E δ τs cb K Lp C₀ c₀ c₁ CV₀ G : ℝ}
    (hδ : 0 < δ) (hcb : 0 < cb) (hK : 0 < K) (hLp : 0 < Lp) (hC₀ : 0 < C₀) (hc₀ : 0 < c₀)
    (hc₁ : c₁ ≤ δ / 4) (hτs : 0 < τs) (hCV : 0 ≤ CV₀)
    (hN : |E| + 2 ≤ N) (hcard : (Fintype.card ι : ℝ) = N) (hTN : T = N ^ (-1 + τs))
    (hTc : T ≤ c₀) (hT1 : T ≤ 1 / 2) (hET : |E| * T ≤ δ / 4) (hG : G ≤ δ)
    (hedge : N ^ (-1 + τs / 8) ≤ c₀ / 8 * T)
    (hXc : N ^ (-(3 * τs / 8)) ≤ C₀ * c₀)
    (herr : N ^ (-(15 * τs / 16)) + N ^ (-(τs / 8)) + N ^ (-1 + 9 * τs / 8) ≤ cb / 2)
    (hrate : C₀ * ((N ^ (-(15 * τs / 16)) + 8 * c₀⁻¹ * N ^ (-(7 * τs / 8))) + N ^ (-1 + 9 * τs / 8) +
        (K + Lp * (|E| + δ + 1)) * T + T) ≤ N ^ (-(3 * τs / 8)))
    (hbox : ∀ z : ℂ, |z.re - E| ≤ δ → 0 < z.im → z.im ≤ 1 → cb ≤ (mr z).im ∧ ‖mr z‖ ≤ K)
    (hlip : ∀ z z' : ℂ, |z.re - E| ≤ δ → 0 < z.im → z.im ≤ 1 →
      |z'.re - E| ≤ δ → 0 < z'.im → z'.im ≤ 1 → ‖mr z - mr z'‖ ≤ Lp * ‖z - z'‖)
    (hρn : Tendsto (fun η : ℝ => (mr ⟨E, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρn))
    (hFC : ∀ (v : ι → ℝ) (s t ε : ℝ), 0 < t → t ≤ c₀ → s = 1 - t → 0 ≤ ε → ε ≤ c₀ →
      (∀ w : ℂ, |w.re| ≤ c₁ → c₀ * t / 4 ≤ w.im → w.im ≤ 1 / 2 →
        ‖mV v w - (Real.sqrt s : ℂ)⁻¹ * mr ((Real.sqrt s : ℂ)⁻¹ * (w + E))‖ ≤ ε) →
      ∃ ρ ρ₀ : ℝ, Tendsto (fun η : ℝ => (freeConvST v t ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ) ∧
        Tendsto (fun η : ℝ => (mr ⟨E, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ₀) ∧ |ρ - ρ₀| ≤ C₀ * (ε + t))
    (hpt : ∀ ζ : ℂ, |ζ.re - E| ≤ δ → N ^ (-1 + τs / 8) ≤ ζ.im → ζ.im ≤ 1 →
      ‖stieltjesN A ζ - mr ζ‖ ≤ N ^ (-(15 * τs / 16)) + N ^ (τs / 8) * (N * ζ.im)⁻¹ + N ^ (-1 + 9 * τs / 8))
    (hnorm : ∀ i, |hA.eigenvalues i| ≤ N ^ CV₀) :
    IsRegular32 (fun i => hA.eigenvalues i - E) (N ^ (-1 + τs / 4)) G
        (cb / 40) (2 * K + cb + 2) (CV₀ + 1) ∧
      ∃ mfc : ℂ → ℂ, IsFreeConv32 (fun i => hA.eigenvalues i - E) (1 - Real.exp (-T)) mfc ∧
        ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
          |ρ' - ρn| ≤ N ^ (-(3 * τs / 8)) := by
  have hN1 : (1 : ℝ) ≤ N := by linarith [abs_nonneg E]
  have hN0 : (0 : ℝ) < N := by linarith
  have hTpos : 0 < T := by rw [hTN]; exact Real.rpow_pos_of_pos hN0 _
  refine ⟨PinsC2_regular hA mr hN hcard hcb hK hδ hτs hTN hT1 hG hbox hpt herr hnorm hCV, ?_⟩
  have ht : 0 < 1 - Real.exp (-T) := PinsC2_one_sub_exp_pos hTpos
  have htT : 1 - Real.exp (-T) ≤ T := PinsC2_one_sub_exp_le T
  set ε : ℝ := (N ^ (-(15 * τs / 16)) + 8 * c₀⁻¹ * N ^ (-(7 * τs / 8))) + N ^ (-1 + 9 * τs / 8) +
    (K + Lp * (|E| + δ + 1)) * T with hεdef
  have hε0 : 0 ≤ ε := by positivity
  have hεc : ε ≤ c₀ := by
    have h1 : C₀ * ε ≤ C₀ * c₀ := by
      refine le_trans ?_ (hrate.trans hXc)
      have : C₀ * ε ≤ C₀ * (ε + T) := mul_le_mul_of_nonneg_left (by linarith) hC₀.le
      exact this
    exact le_of_mul_le_mul_left h1 hC₀
  have hK0 : 0 ≤ K := hK.le
  have hLp0 : 0 ≤ Lp := hLp.le
  obtain ⟨ρ, ρ₀, h1, h2, h3⟩ := hFC (fun i => hA.eigenvalues i - E)
    (Real.exp (-T)) (1 - Real.exp (-T)) ε
    ht (htT.trans hTc) (by ring) hε0 hεc
    (fun w hw hlow hw1 => PinsC2_strip hA mr hN1 hc₀ hδ hc₁ hK0 hLp0 hTN hT1 hET hedge
      (fun z hz hz1 hz2 => (hbox z hz hz1 hz2).2) hlip hpt hw hlow hw1)
  have hρ : ρ₀ = ρn := tendsto_nhds_unique h2 hρn
  refine ⟨freeConvST (fun i => hA.eigenvalues i - E) (1 - Real.exp (-T)),
    isFreeConv51_freeConvST _ ht.le, ρ, h1, ?_⟩
  rw [← hρ]
  refine h3.trans (le_trans ?_ hrate)
  exact mul_le_mul_of_nonneg_left (by linarith) hC₀.le


set_option maxHeartbeats 1000000 in
-- the deterministic half has 16 eventual conditions in one proof
/-- **`step1GoodC''_det`**: eventually in `n`, every `ω` on which the `UNTrLocalInit'` local law holds at heights
`≥ N^{-1+τ_s/8}` (at `τ = τ_s/8`) and all eigenvalues of `H` are `≤ N^{CV₀}` has the good event of `UNStep1GoodC''`.
The free-convolution part uses `freeConv_stable_lip` at `mref = m n`, `E₀ = E`, `A = |E|`, `v = vOUC`, `s = e^{-t*}`,
`t = 1 - e^{-t*}`;
strip closeness through the dictionary `PinsC2_mV_shift` and the Lipschitz bridge `‖m ζ - a⁻¹ m (a⁻¹ ζ)‖ ≤ t* (K + Lp (|E| + δ + 1))`;
`ε_n = (N^{-15τ_s/16} + 8 c₀⁻¹ N^{-7τ_s/8}) + N^{-1+9τ_s/8} + (K + Lp (|E| + δ + 1)) N^{-1+τ_s}`; (2.3) by
`un_eigenvalues_abs_le_convex` with `UNMeanBound`; `ρ₀ = ρ n` by uniqueness of limits.  Constants `c C` before
`∀ᶠ n` (`c = c_box/40`, `C = 2K + c_box + 2`). -/
theorem step1GoodC''_det :
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
        UNDens' m E ρ δ → ∀ CV₀ : ℝ, 0 ≤ CV₀ → UNMeanBound sz M CV₀ →
        ∀ τs : ℝ, 0 < τs → τs < 1 → τs ≤ 𝔠 * 𝔡 →
          ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ ω : Sizes.SeqΩ sz,
            (∀ z : ℂ, |z.re - E| ≤ δ → Nsz sz n ^ (-1 + τs / 8) ≤ z.im → z.im ≤ 1 →
              ‖stieltjesN (ouInit M n (ouTStar sz τs n) ω) z - m n z‖ ≤
                ((sz.W n : ℕ) : ℝ) ^ (τs / 8) * (sz.Bctl n (1 - z.im) + ouTStar sz τs n)) →
            (∀ i, |(M.herm n ω).eigenvalues i| ≤ Nsz sz n ^ CV₀) →
            (IsRegular32 (vOUC sz M n τs E ω) (Nsz sz n ^ (-1 + τs / 4))
                  (Nsz sz n ^ (-(min (τs / 4) ((1 - τs) / 3)))) c C (CV₀ + 1) ∧
              ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOUC sz M n τs E ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧
                ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
                  |ρ' - ρ n| ≤ Nsz sz n ^ (-(3 * τs / 8))) := by
  intro d hd 𝔠 𝔡 sz hA M m E ρ δ hD CV₀ hCV hMean τs hτs0 hτs1 hτs𝔠𝔡
  obtain ⟨hδ, c', C', Lp', hc', hC', hLp', hUev⟩ := hD.1
  obtain ⟨cb, K, Lp, hcb, hK, hLp, hbev⟩ := hD.2
  obtain ⟨c₀, c₁, C₀, hc₀, hc₀c₁, hc₁δ, hC₀, hFC⟩ :=
    freeConv_stable_lip cb K Lp δ |E| hcb hK hLp hδ (abs_nonneg E)
  have hd0 : 0 < d := by omega
  have h𝔠 : 0 < 𝔠 := hA.1
  have h𝔡 : 0 < 𝔡 := hA.2.1
  have hcd := un_admissible_cd_lt_half sz hd0 hA
  have h𝔠1 : 𝔠 < 1 := by
    have h1 := un_admissible_c_mul_lt_one sz hd0 hA
    have h2 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
    nlinarith
  have hτs23 : τs < 2 / 3 := by linarith
  have hσ0 : 0 < min (τs / 4) ((1 - τs) / 3) := lt_min (by linarith) (by linarith)
  set Kb : ℝ := K + Lp * (|E| + δ + 1) with hKbdef
  have hKb : 0 ≤ Kb := by positivity
  refine ⟨cb / 40, 2 * K + cb + 2, by positivity, ?_⟩
  have hNtend : Tendsto (fun n => Nsz sz n) atTop atTop := hA.2.2.1
  have hc₁4 : c₁ ≤ δ / 4 := by
    refine hc₁δ.trans ?_
    exact div_le_div_of_nonneg_left hδ.le (by norm_num) (by nlinarith [abs_nonneg E])
  filter_upwards [hbev, hUev, hA.2.2.2.1, hA.2.2.2.2, hNtend.eventually_ge_atTop (|E| + 2), hMean,
    hNtend.eventually (PinsC2_rpow_ev (e := -1 + τs) (c := min c₀ (1 / 2)) (by linarith)
      (lt_min hc₀ (by norm_num))),
    hNtend.eventually (PinsC2_rpow_ev (e := -(min (τs / 4) ((1 - τs) / 3))) (c := δ / 4)
      (by linarith) (by positivity)),
    hNtend.eventually (PinsC2_rpow_ev (e := -(7 * τs / 8)) (c := c₀ / 8) (by linarith)
      (by positivity)),
    hNtend.eventually (PinsC2_rpow_ev (e := -(15 * τs / 16)) (c := cb / 6) (by linarith)
      (by positivity)),
    hNtend.eventually (PinsC2_rpow_ev (e := -(τs / 8)) (c := cb / 6) (by linarith)
      (by positivity)),
    hNtend.eventually (PinsC2_rpow_ev (e := -1 + 9 * τs / 8) (c := cb / 6) (by linarith)
      (by positivity)),
    hNtend.eventually (PinsC2_rpow_ev (e := -(9 * τs / 16)) (c := 1 / (5 * C₀)) (by linarith)
      (by positivity)),
    hNtend.eventually (PinsC2_rpow_ev (e := -(τs / 2)) (c := c₀ / (40 * C₀)) (by linarith)
      (by positivity)),
    hNtend.eventually (PinsC2_rpow_ev (e := -(1 - 3 * τs / 2)) (c := 1 / (5 * C₀)) (by linarith)
      (by positivity)),
    hNtend.eventually (PinsC2_rpow_ev (e := -(1 - 11 * τs / 8)) (c := 1 / (5 * C₀ * (Kb + 1)))
      (by linarith) (by positivity)),
    hNtend.eventually (PinsC2_rpow_ev (e := -(3 * τs / 8)) (c := C₀ * c₀) (by linarith)
      (by positivity))] with
    n hbn hUn hB hWO hNE hMn eT eG eedge e15 e18 e19 e9 e12 er er' eX
  intro ω hLL hnorm
  have : Nonempty (Idx d (sz.L n) (sz.W n)) := ⟨fun _ => 0⟩
  have hN1 : (1 : ℝ) ≤ Nsz sz n := by linarith [abs_nonneg E]
  have hN0 : (0 : ℝ) < Nsz sz n := by linarith
  have hTpos : 0 < ouTStar sz τs n := Real.rpow_pos_of_pos hN0 _
  have hTc : ouTStar sz τs n ≤ c₀ := eT.trans (min_le_left _ _)
  have hT1 : ouTStar sz τs n ≤ 1 / 2 := eT.trans (min_le_right _ _)
  have hET : |E| * ouTStar sz τs n ≤ δ / 4 := by
    have h1 : ouTStar sz τs n ≤ δ / (4 * (1 + |E|)) := hTc.trans (hc₀c₁.trans hc₁δ)
    calc |E| * ouTStar sz τs n ≤ |E| * (δ / (4 * (1 + |E|))) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg E)
      _ ≤ δ / 4 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [abs_nonneg E]
  have hedge : Nsz sz n ^ (-1 + τs / 8) ≤ c₀ / 8 * ouTStar sz τs n := by
    have hsplit : Nsz sz n ^ (-1 + τs / 8) =
        Nsz sz n ^ (-(7 * τs / 8)) * Nsz sz n ^ (-1 + τs) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right eedge (Real.rpow_nonneg hN0.le _)
  have hpt : ∀ ζ : ℂ, |ζ.re - E| ≤ δ → Nsz sz n ^ (-1 + τs / 8) ≤ ζ.im → ζ.im ≤ 1 →
      ‖stieltjesN (ouInit M n (ouTStar sz τs n) ω) ζ - m n ζ‖ ≤
        Nsz sz n ^ (-(15 * τs / 16)) + Nsz sz n ^ (τs / 8) * (Nsz sz n * ζ.im)⁻¹ +
          Nsz sz n ^ (-1 + 9 * τs / 8) := by
    intro ζ h1 h2 h3
    have hpos : 0 < ζ.im := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) h2
    refine (hLL ζ h1 h2 h3).trans ?_
    rw [mul_add]
    have hb := PinsC2_bctl sz n hd0 h𝔠 h𝔠1 h𝔡 hτs0 hτs𝔠𝔡 hN1 hB hWO.1 hpos
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have hWN : ((sz.W n : ℕ) : ℝ) ^ (τs / 8) ≤ Nsz sz n ^ (τs / 8) :=
      Real.rpow_le_rpow hW0.le (PinsC2_W_le_size sz hd0 n) (by linarith)
    have hWT : ((sz.W n : ℕ) : ℝ) ^ (τs / 8) * ouTStar sz τs n ≤ Nsz sz n ^ (τs / 8) * Nsz sz n ^ (-1 + τs) :=
      mul_le_mul hWN le_rfl hTpos.le (Real.rpow_nonneg hN0.le _)
    have hsplit : Nsz sz n ^ (τs / 8) * Nsz sz n ^ (-1 + τs) = Nsz sz n ^ (-1 + 9 * τs / 8) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    linarith
  have hnormA : ∀ i, |(ouInit_isHermitian M n (ouTStar sz τs n) ω).eigenvalues i| ≤ Nsz sz n ^ CV₀ := by
    have ha0 : 0 ≤ Real.exp (-(ouTStar sz τs n) / 2) := (Real.exp_pos _).le
    have ha1 : Real.exp (-(ouTStar sz τs n) / 2) ≤ 1 := PinsC2_exp_le_one hTpos.le
    refine un_eigenvalues_abs_le_convex (M.herm n ω) (M.mean_herm n)
      (ouInit_isHermitian M n (ouTStar sz τs n) ω) ha0 ha1 ?_ hnorm hMn
    unfold ouInit
    module
  have hrate := PinsC2_rate (τs := τs) hN0 hC₀ hc₀ hKb e9 e12 er er'
  have hcard : (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ) = Nsz sz n := by
    exact_mod_cast sz.card_Idx n
  have hFC' : ∀ (v : Idx d (sz.L n) (sz.W n) → ℝ) (s t ε : ℝ), 0 < t → t ≤ c₀ → s = 1 - t → 0 ≤ ε →
      ε ≤ c₀ →
      (∀ w : ℂ, |w.re| ≤ c₁ → c₀ * t / 4 ≤ w.im → w.im ≤ 1 / 2 →
        ‖mV v w - (Real.sqrt s : ℂ)⁻¹ * m n ((Real.sqrt s : ℂ)⁻¹ * (w + E))‖ ≤ ε) →
      ∃ ρ ρ₀ : ℝ, Tendsto (fun η : ℝ => (freeConvST v t ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ) ∧
        Tendsto (fun η : ℝ => (m n ⟨E, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ₀) ∧
          |ρ - ρ₀| ≤ C₀ * (ε + t) := by
    intro v s t ε h1 h2 h3 h4 h5 h6
    obtain ⟨ρ, ρ₀, a, b, c, -⟩ := hFC (m n) E le_rfl hbn.1 hbn.2 v s t ε h1 h2 h3 h4 h5 h6
    exact ⟨ρ, ρ₀, a, b, c⟩
  exact PinsC2_at_n (ouInit_isHermitian M n (ouTStar sz τs n) ω) (m n) (ρ n) hδ hcb hK hLp hC₀ hc₀ hc₁4 hτs0
    hCV hNE hcard rfl hTc hT1 hET (by linarith) hedge eX (by linarith) hrate hbn.1 hbn.2 hUn.2.2 hFC' hpt hnormA

/-- **`step1GoodC''`**: the statement `UNStep1GoodC''`, from `step1GoodC''_det`, `UNTrLocalInit'` at
`(τ_s, τ_s/8, τ_s/8, D + 1)` and `UNNormBound` at `D + 1` (two bad events, `2 N^{-D-1} ≤ N^{-D}` for `N ≥ 2`;
`UNMeanBound` is deterministic). -/
theorem step1GoodC'' : UNStep1GoodC'' := by
  intro d hd 𝔠 𝔡 sz hA M m E ρ δ hD hT CV₀ hCV hN hMean τs D hτs0 hτs1 hτs𝔠𝔡 hD0
  obtain ⟨c, C, hc, hdet⟩ := step1GoodC''_det d hd 𝔠 𝔡 sz hA M m E ρ δ hD CV₀ hCV hMean τs hτs0 hτs1 hτs𝔠𝔡
  refine ⟨c, C, hc, ?_⟩
  have hT1 := hT τs hτs0 hτs1 (τs / 8) (τs / 8) (D + 1) (by positivity) (by positivity) (by linarith)
  have hN1 := hN (D + 1) (by linarith)
  filter_upwards [hdet, hT1, hN1, (hA.2.2.1 : Tendsto (fun n => Nsz sz n) atTop atTop).eventually_ge_atTop 2]
    with n hdn hTn hNn hN2
  have hN0 : (0 : ℝ) < Nsz sz n := by linarith
  set A : Set (Sizes.SeqΩ sz) := {ω | ∃ z : ℂ, |z.re - E| ≤ δ ∧ Nsz sz n ^ (-1 + τs / 8) ≤ z.im ∧
    z.im ≤ 1 ∧ ((sz.W n : ℕ) : ℝ) ^ (τs / 8) * (sz.Bctl n (1 - z.im) + ouTStar sz τs n) <
      ‖stieltjesN (ouInit M n (ouTStar sz τs n) ω) z - m n z‖} with hAdef
  set B : Set (Sizes.SeqΩ sz) := {ω | ∃ i, Nsz sz n ^ CV₀ < |(M.herm n ω).eigenvalues i|} with hBdef
  have hsub : {ω | ¬ (IsRegular32 (vOUC sz M n τs E ω) (Nsz sz n ^ (-1 + τs / 4))
                (Nsz sz n ^ (-(min (τs / 4) ((1 - τs) / 3)))) c C (CV₀ + 1) ∧
              ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOUC sz M n τs E ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧
                ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
                  |ρ' - ρ n| ≤ Nsz sz n ^ (-(3 * τs / 8)))} ⊆ A ∪ B := by
    intro ω hω
    by_contra hnot
    simp only [hAdef, hBdef, Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_and,
      not_lt] at hnot
    obtain ⟨h1, h2⟩ := hnot
    exact hω (hdn ω (fun z hz1 hz2 hz3 => h1 z hz1 hz2 hz3) (fun i => h2 i))
  calc M.μ _ ≤ M.μ (A ∪ B) := measure_mono hsub
    _ ≤ M.μ A + M.μ B := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Nsz sz n ^ (-(D + 1))) + ENNReal.ofReal (Nsz sz n ^ (-(D + 1))) :=
        add_le_add hTn hNn
    _ = ENNReal.ofReal (Nsz sz n ^ (-(D + 1)) + Nsz sz n ^ (-(D + 1))) :=
        (ENNReal.ofReal_add (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hN0.le _)).symm
    _ ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e : Nsz sz n ^ (-(D + 1)) = Nsz sz n ^ (-D) * (Nsz sz n)⁻¹ := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add hN0]; congr 1; ring
        have hinv : (Nsz sz n)⁻¹ ≤ 1 / 2 := by
          rw [inv_eq_one_div]
          exact one_div_le_one_div_of_le (by norm_num) hN2
        have hpos : 0 ≤ Nsz sz n ^ (-D) := Real.rpow_nonneg hN0.le _
        rw [e]
        nlinarith



end RBM.Univ

end
