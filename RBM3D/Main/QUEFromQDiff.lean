/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Main.QUECore
import RBM3D.Green.LDE

/-!
# `QUE` from `QDiff`: the scale `η_Q`, the exponent chain for every `d ≥ 3`, `MAQUE`, `QUE_of_QDiff`

The deduction of Theorem 2.3 (`MR:QUE`) from the quantum diffusion estimates (Theorem 2.5
`MR:QuDiff`); everything at one fixed `(sz, n, z)` is in `Main/QUECore`.  The argument is the
outline of the proof of Theorem 2.3 (Section 2.1).  Of RBM2D (`QUE_of_QDiff`) only the shape of
`queFixed`/`QUE_of_QDiff` is
used; the `d = 2` scale `W^{2/3}/N` and the `log L` bound do not transfer.

* The scale `η_Q = W^{-ε₀} lam W^{d/2} / N` of (2.27) `ssfa2`, `etaQ`; `queDomain`
  (`η_Q ∈ 𝐃_{κ,ε_Q}`, `ε_Q = 𝔠(𝔡 - ε₀)`, eventually, uniformly in `|E| ≤ 2 - κ`), `calB_le_two_inv`
  ((2.26) `eq:BetaK`), `que_three_terms`, `etaQ_le` and the statement `MAQUE := QDiff → QUE`.  The
  three private scalars of `Endpoints` are re-declared privately (private names of `RBM3D.Endpoints`
  are not visible here).
* `queRowDiff`: from `thetaDiff`, `max |profPM a b - profPM a b'| ≤ C lam^{-2} W^{-d}` (the bound
  after (2.28) `ssfa2_deter`, `‖m‖ < 1`), the constant `C(d, 𝔡, κ)` independent of `(sz, n)`: no
  `log L`.
* `queFixed`: (2.27) `ssfa2` + (2.28) `ssfa2_deter` + Markov at one `(sz, n, E)`, `z = E + iη_Q`:
  `queX_core` at `c = δ_a` and `c = 1_A/|A|`, `queBad_sub`/`que2Bad_sub` (the window of `queWindow`
  is `|x - E| ≤ η_Q`), `queMarkov` with `s = W^{-2c}`, `f = 4N²η_Q² X_c`.
* `queChain` ((2.28) `ssfa2_deter` and the final Markov bound): `N²η_Q² K = C W^{-2ε₀}`,
  `N η_Q 𝓑_{η_Q,0} ≤ 2`, `(lam² W^d)^{-1/5} ≤ W^{-2𝔡/5}`, `(Nη_Q)⁻¹ ≤ W^{ε₀-𝔡}`, `que_three_terms`;
  the constant `3 max(16C, 128)` is absorbed into `W^{τ/2}`.  Needs only `d ≥ 3`, `ε₀ < 𝔡/2`
  (`ε₀ ≤ 3𝔡/5` suffices), `τ > 0`, `C > 0`; `c` is any real.
* `QUE_of_QDiff : MAQUE`: `QDiff` at `(κ, ε, τ/2, D) = (κ, 𝔠(𝔡 - ε₀), τ/2, 1)` (`N₀` uniform over
  `𝐃_{κ,ε}`), `z = E + iη_Q`.  The hypotheses `0 < c`, `c < ε₀`, `c < 𝔡/5` of `QUE` are not used.
* Consumer: `Main/BandTerminal` (`QUE_holds`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ
open scoped NNReal ENNReal ComplexConjugate

namespace RBM.Endpoints

/-! ## 1. The private scalars of `Endpoints` (re-declared) -/

section QUEScalars

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

private theorem W_pos_real : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n

private theorem L_pos_real : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
  have := sz.three_le_L n
  exact_mod_cast (by omega : 0 < sz.L n)

private theorem size_cast : ((sz.size n : ℕ) : ℝ) = (((sz.W n : ℕ) : ℝ) * ((sz.L n : ℕ) : ℝ)) ^ d := by
  simp [Sizes.size]

end QUEScalars

/-! ## 2. The scale `η_Q`, `queDomain`, (2.26) `eq:BetaK`, `MAQUE` -/

section QUE

variable {d : ℕ}

/-- The QUE scale `η_Q = W^{-ε₀} lam W^{d/2} / N` of (2.27) `ssfa2`, the half-width of `𝓘_E(ε₀)` ((2.17) `eq:defIE`). -/
def etaQ (sz : Sizes d) (n : ℕ) (ε₀ : ℝ) : ℝ :=
  ((sz.W n : ℕ) : ℝ) ^ (-ε₀) * (sz.lam n * ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2) / Nsz sz n)

/-- **`η_Q ∈ 𝐃_{κ,ε_Q}` with `ε_Q = 𝔠(𝔡 - ε₀)`** (the QUE deduction consumes `QDiff` at `ε = 𝔠(𝔡 - ε₀)`, so
`ε` of `QDiff` is a free parameter that must stay a `∀`): `η_Q N ≥ W^{𝔡-ε₀} ≥ N^{𝔠(𝔡-ε₀)}` from (2.10) `eq:WO` and
(2.9) `Main_DEL_COND`; `η_Q ≤ 1` eventually from `W → ∞` and `lam ≤ 𝔡⁻¹`. -/
theorem queDomain (sz : Sizes d) {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) {ε₀ κ : ℝ} (hε₀ : 0 < ε₀) (hε₀𝔡 : ε₀ < 𝔡) :
    ∀ᶠ n in atTop, ∀ E : ℝ, |E| ≤ 2 - κ →
      sz.locDomain κ (𝔠 * (𝔡 - ε₀)) n ((E : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I) := by
  obtain ⟨h𝔠, h𝔡, hsz, hbw, hWO⟩ := hA
  have hW := RBM.Green.tendsto_W sz h𝔠 hsz hbw
  filter_upwards [hWO, hbw, hW.eventually_ge_atTop 1,
    ((tendsto_rpow_atTop hε₀).comp hW).eventually_ge_atTop (𝔡⁻¹ + 1)] with n hWOn hbwn hW1 hWε
  intro E hE
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hNpos : (0 : ℝ) < Nsz sz n := Nsz_pos sz n
  have hlam : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos _) hWOn.1
  have hWd : ((sz.W n : ℕ) : ℝ) ^ d ≤ Nsz sz n := by
    have h : (sz.W n) ^ d ≤ (sz.W n * sz.L n) ^ d :=
      Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by have := sz.three_le_L n; omega)) d
    exact_mod_cast h
  refine ⟨by simpa using hE, ?_, ?_⟩
  · -- `N^{-1+ε_Q} ≤ η_Q`
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_add, add_zero]
    have h1 : Nsz sz n ^ (-1 + 𝔠 * (𝔡 - ε₀)) = Nsz sz n ^ (𝔠 * (𝔡 - ε₀)) / Nsz sz n := by
      rw [Real.rpow_add hNpos, Real.rpow_neg_one]; field_simp
    have h2 : Nsz sz n ^ (𝔠 * (𝔡 - ε₀)) ≤ ((sz.W n : ℕ) : ℝ) ^ (𝔡 - ε₀) := by
      rw [Real.rpow_mul hNpos.le]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hNpos.le _) hbwn (by linarith)
    have h3 : ((sz.W n : ℕ) : ℝ) ^ (𝔡 - ε₀) ≤
        ((sz.W n : ℕ) : ℝ) ^ (-ε₀) * (sz.lam n * ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2)) := by
      have h4 : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) * ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2) =
          ((sz.W n : ℕ) : ℝ) ^ 𝔡 := by
        rw [← Real.rpow_add hWpos]; congr 1; ring
      calc ((sz.W n : ℕ) : ℝ) ^ (𝔡 - ε₀) = ((sz.W n : ℕ) : ℝ) ^ (-ε₀) * ((sz.W n : ℕ) : ℝ) ^ 𝔡 := by
            rw [← Real.rpow_add hWpos]; congr 1; ring
        _ = ((sz.W n : ℕ) : ℝ) ^ (-ε₀) * (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) *
              ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2)) := by rw [h4]
        _ ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀) * (sz.lam n * ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2)) := by
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hWpos.le _)
            exact mul_le_mul_of_nonneg_right hWOn.1 (Real.rpow_nonneg hWpos.le _)
    unfold etaQ
    rw [h1]
    calc Nsz sz n ^ (𝔠 * (𝔡 - ε₀)) / Nsz sz n ≤ ((sz.W n : ℕ) : ℝ) ^ (𝔡 - ε₀) / Nsz sz n :=
          div_le_div_of_nonneg_right h2 hNpos.le
      _ ≤ (((sz.W n : ℕ) : ℝ) ^ (-ε₀) * (sz.lam n * ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2))) / Nsz sz n :=
          div_le_div_of_nonneg_right h3 hNpos.le
      _ = ((sz.W n : ℕ) : ℝ) ^ (-ε₀) * (sz.lam n * ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2) / Nsz sz n) := by ring
  · -- `η_Q ≤ 1`
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_add, add_zero]
    unfold etaQ
    have hWε' : 𝔡⁻¹ + 1 ≤ ((sz.W n : ℕ) : ℝ) ^ ε₀ := hWε
    have hneg : ((sz.W n : ℕ) : ℝ) ^ (-ε₀) = (((sz.W n : ℕ) : ℝ) ^ ε₀)⁻¹ := Real.rpow_neg hWpos.le _
    have h𝔡inv : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
    have hhalf : ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2) ≤ Nsz sz n := by
      have h1 : ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2) ≤ ((sz.W n : ℕ) : ℝ) ^ (d : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le hW1
        have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
        linarith
      rw [Real.rpow_natCast] at h1
      exact h1.trans hWd
    have hq : sz.lam n * ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2) / Nsz sz n ≤ 𝔡⁻¹ := by
      rw [div_le_iff₀ hNpos]
      have hl : sz.lam n ≤ 𝔡⁻¹ := hWOn.2
      exact mul_le_mul hl hhalf (Real.rpow_nonneg hWpos.le _) h𝔡inv.le
    have hq0 : 0 ≤ sz.lam n * ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2) / Nsz sz n := by
      have := Real.rpow_nonneg hWpos.le ((d : ℝ) / 2)
      positivity
    have hWinv : ((sz.W n : ℕ) : ℝ) ^ (-ε₀) ≤ (𝔡⁻¹ + 1)⁻¹ := by
      rw [hneg]; exact inv_anti₀ (by positivity) hWε'
    have hfin : ((sz.W n : ℕ) : ℝ) ^ (-ε₀) * (sz.lam n * ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2) / Nsz sz n) ≤
        (𝔡⁻¹ + 1)⁻¹ * 𝔡⁻¹ := mul_le_mul hWinv hq hq0 (by positivity)
    have hlast : (𝔡⁻¹ + 1)⁻¹ * 𝔡⁻¹ ≤ 1 := by
      rw [inv_mul_le_iff₀ (by positivity)]; linarith
    exact hfin.trans hlast


/-- **(2.26) `eq:BetaK`** with explicit constants: for `η ≤ lam² / L^d`,
`(Nη)⁻¹ ≤ 𝓑_{η,K} ≤ 2 (Nη)⁻¹` for every distance `K ≥ 0`. -/
theorem calB_le_two_inv (sz : Sizes d) (n : ℕ) (hd : 2 ≤ d) {η K : ℝ} (hη : 0 < η) (hK : 0 ≤ K)
    (hηL : η ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d) (hlam : 0 < sz.lam n) :
    calB sz n η K ≤ 2 * (Nsz sz n * η)⁻¹ := by
  have hW := W_pos_real sz n
  have hL := L_pos_real sz n
  have hLd : 0 < ((sz.L n : ℕ) : ℝ) ^ d := by positivity
  have hWd : 0 < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hLη : ((sz.L n : ℕ) : ℝ) ^ d * η ≤ sz.lam n ^ 2 := by
    rw [le_div_iff₀ hLd] at hηL; linarith
  have hWK : ((sz.W n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ 2 * (K + ((sz.W n : ℕ) : ℝ)) ^ (d - 2) := by
    calc ((sz.W n : ℕ) : ℝ) ^ d = ((sz.W n : ℕ) : ℝ) ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (d - 2) := by
          rw [← pow_add]; congr 1; omega
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ 2 * (K + ((sz.W n : ℕ) : ℝ)) ^ (d - 2) := by
          gcongr; linarith
  have h1 : (sz.lam n ^ 2 + η)⁻¹ / (((sz.W n : ℕ) : ℝ) ^ 2 * (K + ((sz.W n : ℕ) : ℝ)) ^ (d - 2)) ≤
      (Nsz sz n * η)⁻¹ := by
    have ha : (sz.lam n ^ 2 + η)⁻¹ ≤ (((sz.L n : ℕ) : ℝ) ^ d * η)⁻¹ :=
      inv_anti₀ (by positivity) (by linarith)
    calc (sz.lam n ^ 2 + η)⁻¹ / (((sz.W n : ℕ) : ℝ) ^ 2 * (K + ((sz.W n : ℕ) : ℝ)) ^ (d - 2))
        ≤ (sz.lam n ^ 2 + η)⁻¹ / ((sz.W n : ℝ) ^ d) :=
          div_le_div_of_nonneg_left (by positivity) hWd hWK
      _ ≤ (((sz.L n : ℕ) : ℝ) ^ d * η)⁻¹ / ((sz.W n : ℝ) ^ d) := div_le_div_of_nonneg_right ha hWd.le
      _ = (Nsz sz n * η)⁻¹ := by
          rw [Nsz, size_cast sz n, mul_pow]; field_simp
  unfold calB
  linarith

/-- The three terms of (2.28) `ssfa2_deter`: for `x = W ≥ 1`, `0 < ε₀ ≤ 3𝔡/5`,
`x^{ε₀-𝔡} + x^{-2𝔡/5} + x^{-2ε₀} ≤ 3 x^{-(2ε₀)∧(2𝔡/5)}` (`-𝔡+ε₀ ≤ -2𝔡/5` iff `ε₀ ≤ 3𝔡/5`; slack `𝔡/10` at the
paper's `ε₀ < 𝔡/2`). -/
theorem que_three_terms {x ε₀ 𝔡 : ℝ} (hx : 1 ≤ x) (hε₀ : 0 < ε₀) (h𝔡 : 0 < 𝔡) (hε : ε₀ ≤ 3 * 𝔡 / 5) :
    x ^ (ε₀ - 𝔡) + x ^ (-(2 * 𝔡 / 5)) + x ^ (-(2 * ε₀)) ≤ 3 * x ^ (-(min (2 * ε₀) (2 * 𝔡 / 5))) := by
  have h1 : x ^ (ε₀ - 𝔡) ≤ x ^ (-(min (2 * ε₀) (2 * 𝔡 / 5))) :=
    Real.rpow_le_rpow_of_exponent_le hx (by have := min_le_right (2 * ε₀) (2 * 𝔡 / 5); linarith)
  have h2 : x ^ (-(2 * 𝔡 / 5)) ≤ x ^ (-(min (2 * ε₀) (2 * 𝔡 / 5))) :=
    Real.rpow_le_rpow_of_exponent_le hx (by have := min_le_right (2 * ε₀) (2 * 𝔡 / 5); linarith)
  have h3 : x ^ (-(2 * ε₀)) ≤ x ^ (-(min (2 * ε₀) (2 * 𝔡 / 5))) :=
    Real.rpow_le_rpow_of_exponent_le hx (by have := min_le_left (2 * ε₀) (2 * 𝔡 / 5); linarith)
  linarith

/-- **`η_Q ≤ lam² / L^d`** ((2.26) `eq:BetaK` applies at `η_Q`): `η_Q L^d = lam W^{-ε₀-d/2} ≤ lam²` iff
`lam ≥ W^{-d/2-ε₀}`; from (2.10) `eq:WO` (`lam ≥ W^{-d/2+𝔡}`) the slack is the factor `W^{𝔡+ε₀}`. -/
theorem etaQ_le (sz : Sizes d) (n : ℕ) {ε₀ 𝔡 : ℝ} (hε₀ : 0 < ε₀) (h𝔡 : 0 < 𝔡)
    (hW1 : 1 ≤ ((sz.W n : ℕ) : ℝ))
    (hlo : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ sz.lam n) :
    etaQ sz n ε₀ ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d := by
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hlam : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos _) hlo
  have hL := L_pos_real sz n
  have hLd : 0 < ((sz.L n : ℕ) : ℝ) ^ d := by positivity
  have h1 : ((sz.W n : ℕ) : ℝ) ^ (-ε₀ - (d : ℝ) / 2) ≤ sz.lam n := by
    refine le_trans ?_ hlo
    exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hWh : 0 < ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos hWpos _
  have hsq : ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2) * ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2) =
      ((sz.W n : ℕ) : ℝ) ^ d := by
    rw [← Real.rpow_add hWpos, ← Real.rpow_natCast]; congr 1; ring
  have h2 : etaQ sz n ε₀ = sz.lam n * ((sz.W n : ℕ) : ℝ) ^ (-ε₀ - (d : ℝ) / 2) / ((sz.L n : ℕ) : ℝ) ^ d := by
    unfold etaQ
    rw [Nsz, size_cast sz n, mul_pow, Real.rpow_sub hWpos, ← hsq]
    field_simp
  rw [h2, div_le_div_iff_of_pos_right hLd, pow_two]
  exact mul_le_mul_of_nonneg_left h1 hlam.le

/-- **`MAQUE`**: `QUE` from `QDiff` (RBM2D `QUE_of_QDiff`), used only
through its expectation half (2.24) `Meq:QdS1`, (2.25) `Meq:QdS2` at `z = E + iη_Q`, `ε = 𝔠(𝔡 - ε₀)` (`queDomain`), with
(2.27) `ssfa2`, (2.28) `ssfa2_deter`, `thetaDiff` and Markov.  The Markov step needs (2.24) `Meq:QdS1`, (2.25) `Meq:QdS2` with `N₀` uniform over
`𝐃_{κ,ε}` (the `z` runs over `E ∈ [-2+κ, 2-κ]` and over `n`). -/
def MAQUE : Prop := QDiff → QUE

end QUE

/-! ## 3. The chain for every `d ≥ 3`: `queRowDiff`, `queFixed`, `queChain`, `QUE_of_QDiff` -/

section QUEChain

/-- **Row differences of the profiles** (the bound after (2.28) `ssfa2_deter`): from `thetaDiff`, with the same
constant for every `(sz, n)`: `K = C lam^{-2} W^{-d}` (the factor `‖m‖² < 1` absorbed). -/
theorem queRowDiff : ∀ d : ℕ, 3 ≤ d → ∀ 𝔡 κ : ℝ, 0 < 𝔡 → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (sz : Sizes d) (n : ℕ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
      ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → |z.re| ≤ 2 - κ → ∀ a b b' : Zd d (sz.L n),
        ‖profPM sz n z a b - profPM sz n z a b'‖ ≤ C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d ∧
        ‖profPP sz n z a b - profPP sz n z a b'‖ ≤ C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d := by
  intro d hd 𝔡 κ h𝔡 hκ
  obtain ⟨C, hC, H⟩ := thetaDiff d hd 𝔡 κ h𝔡 hκ
  refine ⟨C, hC, fun sz n hl hl1 z hz hz1 hre a b b' => ?_⟩
  obtain ⟨h1, h2⟩ := H (sz.L n) (sz.three_le_L n) (sz.lam n) hl hl1 z hz hz1 hre a b b'
  have hm : ‖msc z‖ < 1 := norm_msc_lt_one hz
  have hm0 := norm_nonneg (msc z)
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have := W_pos_real sz n
    positivity
  have hmm : ‖msc z‖ ^ 2 ≤ 1 := by nlinarith
  refine ⟨?_, ?_⟩
  · have e : profPM sz n z a b - profPM sz n z a b' =
        (((‖msc z‖ ^ 2 : ℝ)) : ℂ) * (Theta d (sz.L n) (sz.lam n) (((‖msc z‖ ^ 2 : ℝ)) : ℂ) a b -
          Theta d (sz.L n) (sz.lam n) (((‖msc z‖ ^ 2 : ℝ)) : ℂ) a b') / ((sz.W n : ℕ) : ℂ) ^ d := by
      unfold profPM ThetaPM; ring
    rw [e, norm_div, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    refine div_le_div_of_nonneg_right ?_ hWd.le
    calc ‖msc z‖ ^ 2 * ‖Theta d (sz.L n) (sz.lam n) (((‖msc z‖ ^ 2 : ℝ)) : ℂ) a b -
          Theta d (sz.L n) (sz.lam n) (((‖msc z‖ ^ 2 : ℝ)) : ℂ) a b'‖
        ≤ 1 * (C * (sz.lam n ^ 2)⁻¹) := mul_le_mul hmm h1 (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  · have e : profPP sz n z a b - profPP sz n z a b' =
        msc z ^ 2 * (Theta d (sz.L n) (sz.lam n) (msc z ^ 2) a b -
          Theta d (sz.L n) (sz.lam n) (msc z ^ 2) a b') / ((sz.W n : ℕ) : ℂ) ^ d := by
      unfold profPP ThetaPP; ring
    rw [e, norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_natCast]
    refine div_le_div_of_nonneg_right ?_ hWd.le
    calc ‖msc z‖ ^ 2 * ‖Theta d (sz.L n) (sz.lam n) (msc z ^ 2) a b -
          Theta d (sz.L n) (sz.lam n) (msc z ^ 2) a b'‖
        ≤ 1 * (C * (sz.lam n ^ 2)⁻¹) := mul_le_mul hmm h2 (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _

/-- **QUE at one `(sz, n, E)`** ((2.27) `ssfa2` + (2.28) `ssfa2_deter` + Markov, at `z = E + iη_Q`): `queX_core` with
`c = δ_a` and `c = 1_A/|A|`, `queBad_sub`/`que2Bad_sub` (the window is `[E - η_Q, E + η_Q]`), `queMarkov` with
`s = W^{-2c}`, `f = 4N²η_Q² X_c`, `T = 4N²η_Q² · 4(K + ε)`. -/
theorem queFixed : ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (ε₀ c E ε K : ℝ) (z : ℂ),
    z = (E : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I → 0 < etaQ sz n ε₀ →
    (∀ a b : Zd d (sz.L n),
      ‖(∫ ω, avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP sz)) -
          profPM sz n z a b‖ ≤ ε ∧
      ‖(∫ ω, avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) a b ∂(Sizes.seqP sz)) -
          profPP sz n z a b‖ ≤ ε) →
    (∀ a b b' : Zd d (sz.L n),
      ‖profPM sz n z a b - profPM sz n z a b'‖ ≤ K ∧ ‖profPP sz n z a b - profPP sz n z a b'‖ ≤ K) →
    (∀ a : Zd d (sz.L n),
      Sizes.seqP sz {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E a (sz.seqXmat n ω)} ≤
        ENNReal.ofReal (4 * Nsz sz n ^ 2 * etaQ sz n ε₀ ^ 2 * (4 * (K + ε)) /
          ((sz.W n : ℕ) : ℝ) ^ (-(2 * c)))) ∧
    (∀ A : Finset (Zd d (sz.L n)), A.Nonempty →
      Sizes.seqP sz {ω | que2BadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E A (sz.seqXmat n ω)} ≤
        ENNReal.ofReal (4 * Nsz sz n ^ 2 * etaQ sz n ε₀ ^ 2 * (4 * (K + ε)) /
          ((sz.W n : ℕ) : ℝ) ^ (-(2 * c)))) := by
  intro d sz n ε₀ c E ε K z hz hη hQ hK
  subst hz
  have hz0 : 0 < ((E : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I).im := by simpa using hη
  have hwin : ∀ x : ℝ, queWindow d (sz.L n) (sz.W n) (sz.lam n) ε₀ E x → |x - E| ≤ etaQ sz n ε₀ :=
    fun x hx => hx
  have hs : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ (-(2 * c)) := Real.rpow_pos_of_pos (W_pos_real sz n) _
  have key : ∀ cc : Zd d (sz.L n) → ℝ, (∀ u, 0 ≤ cc u) → ∑ u, cc u = 1 →
      ∀ S : Set sz.SeqΩ, S ⊆ {ω | ((sz.W n : ℕ) : ℝ) ^ (-(2 * c)) ≤
          4 * Nsz sz n ^ 2 * etaQ sz n ε₀ ^ 2 *
            queX sz n ((E : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I) cc ω} →
        Sizes.seqP sz S ≤ ENNReal.ofReal (4 * Nsz sz n ^ 2 * etaQ sz n ε₀ ^ 2 * (4 * (K + ε)) /
          ((sz.W n : ℕ) : ℝ) ^ (-(2 * c))) := by
    intro cc hc0 hc1 S hS
    obtain ⟨hint, hnn, hI⟩ := queX_core sz n _ hz0 ε K hQ hK cc hc0 hc1
    have hN := Nsz_pos sz n
    refine queMarkov (Sizes.seqP sz)
      (fun ω => 4 * Nsz sz n ^ 2 * etaQ sz n ε₀ ^ 2 *
        queX sz n ((E : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I) cc ω)
      (hint.const_mul _) (fun ω => mul_nonneg (by positivity) (hnn ω)) hs ?_ S hS
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hI (by positivity)
  refine ⟨fun a => key _ ?_ ?_ _ (queBad_sub sz n ε₀ c E _ hη hwin a), fun A hA => ?_⟩
  · intro u; split_ifs <;> norm_num
  · simp
  · have hcard : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
    refine key _ ?_ ?_ _ (que2Bad_sub sz n ε₀ c E _ hη hwin A hA)
    · intro u; split_ifs <;> positivity
    · rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      exact mul_inv_cancel₀ hcard.ne'

/-- The real-number core of `queChain` ((2.28) `ssfa2_deter`), at one `n`, in terms of the reals
`W, lam, N, η, B = 𝓑_{η,0}`. -/
private theorem queChain_real {W lam N η B : ℝ} (d : ℕ) {𝔡 ε₀ c τ C : ℝ}
    (h𝔡 : 0 < 𝔡) (hε₀ : 0 < ε₀) (hε : ε₀ ≤ 3 * 𝔡 / 5) (hτ : 0 < τ) (hC : 0 < C)
    (hW1 : 1 ≤ W) (hlam : 0 < lam) (hN : 0 < N) (hη : 0 < η)
    (hsq : W ^ ((d : ℝ) / 2) * W ^ ((d : ℝ) / 2) = W ^ d)
    (hNη : N * η = W ^ (-ε₀) * (lam * W ^ ((d : ℝ) / 2)))
    (hlo : W ^ (-(d : ℝ) / 2 + 𝔡) ≤ lam) (hlam2 : W ^ (2 * 𝔡) ≤ lam ^ 2 * W ^ d)
    (hB0 : 0 ≤ B) (hB : B ≤ 2 * (N * η)⁻¹)
    (hbig : 3 * max (16 * C) 128 ≤ W ^ (τ / 2)) :
    4 * N ^ 2 * η ^ 2 * (4 * (C * (lam ^ 2)⁻¹ / W ^ d +
        W ^ (τ / 2) * B ^ 2 * ((lam ^ 2 * W ^ d) ^ (-(1 : ℝ) / 5) + B))) / W ^ (-(2 * c)) ≤
      W ^ (-(min (2 * ε₀) (2 * 𝔡 / 5)) + 2 * c + τ) := by
  have hW0 : 0 < W := by linarith
  have hWd : 0 < W ^ d := by positivity
  have hWh : 0 < W ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos hW0 _
  have hu : 0 < N * η := mul_pos hN hη
  have hM1 : 16 * C ≤ max (16 * C) 128 := le_max_left _ _
  have hM2 : (128 : ℝ) ≤ max (16 * C) 128 := le_max_right _ _
  have ht1 : 1 ≤ W ^ (τ / 2) := by linarith
  have ht0 : 0 < W ^ (τ / 2) := by linarith
  have hs : (0 : ℝ) < W ^ (-(2 * c)) := Real.rpow_pos_of_pos hW0 _
  -- `(Nη)² = W^{-2ε₀} (lam² W^d)`
  have hmid : W ^ (-(2 * ε₀)) = W ^ (-ε₀) * W ^ (-ε₀) := by
    rw [← Real.rpow_add hW0]; congr 1; ring
  have hNη2 : N ^ 2 * η ^ 2 = W ^ (-(2 * ε₀)) * (lam ^ 2 * W ^ d) := by
    rw [← mul_pow, hNη, mul_pow, mul_pow, hmid, ← hsq]; ring
  have h4 : 4 * N ^ 2 * η ^ 2 = 4 * (W ^ (-(2 * ε₀)) * (lam ^ 2 * W ^ d)) := by
    rw [mul_assoc, hNη2]
  -- term 1: `16 N²η² K = 16 C W^{-2ε₀}`
  have hT1 : 4 * N ^ 2 * η ^ 2 * (4 * (C * (lam ^ 2)⁻¹ / W ^ d)) = 16 * C * W ^ (-(2 * ε₀)) := by
    rw [h4]
    field_simp
    norm_num
  -- `N η B ≤ 2`
  have huB : N * η * B ≤ 2 := by
    calc N * η * B ≤ N * η * (2 * (N * η)⁻¹) := mul_le_mul_of_nonneg_left hB hu.le
      _ = 2 := by field_simp
  have huB2 : (N * η * B) ^ 2 ≤ 4 := by
    have h0 : 0 ≤ N * η * B := by positivity
    nlinarith
  -- `(lam² W^d)^{-1/5} ≤ W^{-2𝔡/5}`
  have hA : (lam ^ 2 * W ^ d) ^ (-(1 : ℝ) / 5) ≤ W ^ (-(2 * 𝔡 / 5)) := by
    have h1 : (lam ^ 2 * W ^ d) ^ (-(1 : ℝ) / 5) ≤ (W ^ (2 * 𝔡)) ^ (-(1 : ℝ) / 5) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hW0 _) hlam2 (by norm_num)
    rw [← Real.rpow_mul hW0.le] at h1
    have e : 2 * 𝔡 * (-(1 : ℝ) / 5) = -(2 * 𝔡 / 5) := by ring
    rwa [e] at h1
  -- `(Nη)⁻¹ ≤ W^{ε₀-𝔡}`
  have hI : (N * η)⁻¹ ≤ W ^ (ε₀ - 𝔡) := by
    have h1 : W ^ 𝔡 ≤ lam * W ^ ((d : ℝ) / 2) := by
      have e : W ^ (-(d : ℝ) / 2 + 𝔡) * W ^ ((d : ℝ) / 2) = W ^ 𝔡 := by
        rw [← Real.rpow_add hW0]; congr 1; ring
      rw [← e]; exact mul_le_mul_of_nonneg_right hlo hWh.le
    have h2 : W ^ (𝔡 - ε₀) ≤ N * η := by
      have e : W ^ (𝔡 - ε₀) = W ^ (-ε₀) * W ^ 𝔡 := by
        rw [← Real.rpow_add hW0]; congr 1; ring
      rw [hNη, e]; exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hW0.le _)
    have h3 : (N * η)⁻¹ ≤ (W ^ (𝔡 - ε₀))⁻¹ := inv_anti₀ (Real.rpow_pos_of_pos hW0 _) h2
    rw [← Real.rpow_neg hW0.le] at h3
    have e : -(𝔡 - ε₀) = ε₀ - 𝔡 := by ring
    rwa [e] at h3
  -- term 2: `16 N²η² (W^{τ/2} B² (A + B)) ≤ 64 W^{τ/2} (W^{-2𝔡/5} + 2 W^{ε₀-𝔡})`
  have hX2 : 0 ≤ W ^ (-(2 * 𝔡 / 5)) := Real.rpow_nonneg hW0.le _
  have hX3 : 0 ≤ W ^ (ε₀ - 𝔡) := Real.rpow_nonneg hW0.le _
  have hAnn : 0 ≤ (lam ^ 2 * W ^ d) ^ (-(1 : ℝ) / 5) := Real.rpow_nonneg (by positivity) _
  have hAB : (lam ^ 2 * W ^ d) ^ (-(1 : ℝ) / 5) + B ≤ W ^ (-(2 * 𝔡 / 5)) + 2 * W ^ (ε₀ - 𝔡) := by
    have : 2 * (N * η)⁻¹ ≤ 2 * W ^ (ε₀ - 𝔡) := by linarith
    linarith
  have hT2 : 4 * N ^ 2 * η ^ 2 * (4 * (W ^ (τ / 2) * B ^ 2 *
        ((lam ^ 2 * W ^ d) ^ (-(1 : ℝ) / 5) + B))) ≤
      64 * W ^ (τ / 2) * (W ^ (-(2 * 𝔡 / 5)) + 2 * W ^ (ε₀ - 𝔡)) := by
    have e : 4 * N ^ 2 * η ^ 2 * (4 * (W ^ (τ / 2) * B ^ 2 *
        ((lam ^ 2 * W ^ d) ^ (-(1 : ℝ) / 5) + B))) =
        16 * W ^ (τ / 2) * (N * η * B) ^ 2 * ((lam ^ 2 * W ^ d) ^ (-(1 : ℝ) / 5) + B) := by ring
    rw [e]
    have h1 : 16 * W ^ (τ / 2) * (N * η * B) ^ 2 ≤ 16 * W ^ (τ / 2) * 4 :=
      mul_le_mul_of_nonneg_left huB2 (by positivity)
    calc 16 * W ^ (τ / 2) * (N * η * B) ^ 2 * ((lam ^ 2 * W ^ d) ^ (-(1 : ℝ) / 5) + B)
        ≤ 16 * W ^ (τ / 2) * 4 * ((lam ^ 2 * W ^ d) ^ (-(1 : ℝ) / 5) + B) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ 16 * W ^ (τ / 2) * 4 * (W ^ (-(2 * 𝔡 / 5)) + 2 * W ^ (ε₀ - 𝔡)) :=
          mul_le_mul_of_nonneg_left hAB (by positivity)
      _ = _ := by ring
  -- the three terms
  have h3t := que_three_terms hW1 hε₀ h𝔡 hε
  set M := max (16 * C) 128 with hM
  have hX1 : 0 ≤ W ^ (-(2 * ε₀)) := Real.rpow_nonneg hW0.le _
  have hXm : 0 ≤ W ^ (-(min (2 * ε₀) (2 * 𝔡 / 5))) := Real.rpow_nonneg hW0.le _
  have hnum : 4 * N ^ 2 * η ^ 2 * (4 * (C * (lam ^ 2)⁻¹ / W ^ d +
        W ^ (τ / 2) * B ^ 2 * ((lam ^ 2 * W ^ d) ^ (-(1 : ℝ) / 5) + B))) ≤
      W ^ (τ) * W ^ (-(min (2 * ε₀) (2 * 𝔡 / 5))) := by
    have e : 4 * N ^ 2 * η ^ 2 * (4 * (C * (lam ^ 2)⁻¹ / W ^ d +
        W ^ (τ / 2) * B ^ 2 * ((lam ^ 2 * W ^ d) ^ (-(1 : ℝ) / 5) + B))) =
        4 * N ^ 2 * η ^ 2 * (4 * (C * (lam ^ 2)⁻¹ / W ^ d)) + 4 * N ^ 2 * η ^ 2 * (4 * (W ^ (τ / 2) * B ^ 2 *
          ((lam ^ 2 * W ^ d) ^ (-(1 : ℝ) / 5) + B))) := by ring
    rw [e, hT1]
    have hs1 : 16 * C * W ^ (-(2 * ε₀)) + 64 * W ^ (τ / 2) * (W ^ (-(2 * 𝔡 / 5)) + 2 * W ^ (ε₀ - 𝔡)) ≤
        M * W ^ (τ / 2) * (W ^ (ε₀ - 𝔡) + W ^ (-(2 * 𝔡 / 5)) + W ^ (-(2 * ε₀))) := by
      have hM0 : 0 ≤ M := by linarith
      have hMt : M ≤ M * W ^ (τ / 2) := le_mul_of_one_le_right hM0 ht1
      have a1 : 16 * C * W ^ (-(2 * ε₀)) ≤ M * W ^ (τ / 2) * W ^ (-(2 * ε₀)) :=
        mul_le_mul_of_nonneg_right (by linarith) hX1
      have a2 : 64 * W ^ (τ / 2) * W ^ (-(2 * 𝔡 / 5)) ≤ M * W ^ (τ / 2) * W ^ (-(2 * 𝔡 / 5)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) ht0.le) hX2
      have a3 : 128 * W ^ (τ / 2) * W ^ (ε₀ - 𝔡) ≤ M * W ^ (τ / 2) * W ^ (ε₀ - 𝔡) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) ht0.le) hX3
      linarith
    have hs2 : M * W ^ (τ / 2) * (W ^ (ε₀ - 𝔡) + W ^ (-(2 * 𝔡 / 5)) + W ^ (-(2 * ε₀))) ≤
        M * W ^ (τ / 2) * (3 * W ^ (-(min (2 * ε₀) (2 * 𝔡 / 5)))) :=
      mul_le_mul_of_nonneg_left h3t (by positivity)
    have hs3 : M * W ^ (τ / 2) * (3 * W ^ (-(min (2 * ε₀) (2 * 𝔡 / 5)))) ≤
        W ^ (τ / 2) * W ^ (τ / 2) * W ^ (-(min (2 * ε₀) (2 * 𝔡 / 5))) := by
      have : 3 * M ≤ W ^ (τ / 2) := hbig
      have e : M * W ^ (τ / 2) * (3 * W ^ (-(min (2 * ε₀) (2 * 𝔡 / 5)))) =
          (3 * M) * W ^ (τ / 2) * W ^ (-(min (2 * ε₀) (2 * 𝔡 / 5))) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this ht0.le) hXm
    have hτ2 : W ^ (τ / 2) * W ^ (τ / 2) = W ^ τ := by
      rw [← Real.rpow_add hW0]; congr 1; ring
    rw [hτ2] at hs3
    linarith
  rw [div_le_iff₀ hs]
  refine hnum.trans (le_of_eq ?_)
  rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]
  congr 1; ring

/-- **The `d ≥ 3` exponent chain** ((2.28) `ssfa2_deter`): with `K = C lam^{-2} W^{-d}` and `ε = qdBoundExp` at
`τ/2`, `η_Q`, the Markov bound of `queFixed` is eventually below `W^{-(2ε₀)∧(2𝔡/5)+2c+τ}`
(`N²η_Q²K = C W^{-2ε₀}`; `Nη_Q 𝓑_{η_Q,0} ≤ 2`; `(lam² W^d)^{-1/5} ≤ W^{-2𝔡/5}`; `(Nη_Q)⁻¹ ≤ W^{ε₀-𝔡}`;
`que_three_terms`; the constant `3 max(16C, 128)` absorbed into `W^{τ/2}`). -/
theorem queChain : ∀ {d : ℕ}, 3 ≤ d → ∀ {𝔠 𝔡 : ℝ} (sz : Sizes d), sz.Admissible 𝔠 𝔡 →
    ∀ ε₀ c τ C : ℝ, 0 < ε₀ → ε₀ < 𝔡 / 2 → 0 < τ → 0 < C →
      ∀ᶠ n in atTop,
        4 * Nsz sz n ^ 2 * etaQ sz n ε₀ ^ 2 *
            (4 * (C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d + qdBoundExp sz n (τ / 2) (etaQ sz n ε₀))) /
          ((sz.W n : ℕ) : ℝ) ^ (-(2 * c)) ≤
        ((sz.W n : ℕ) : ℝ) ^ (-(min (2 * ε₀) (2 * 𝔡 / 5)) + 2 * c + τ) := by
  intro d hd 𝔠 𝔡 sz hA ε₀ c τ C hε₀ hε hτ hC
  obtain ⟨h𝔠, h𝔡, hsz, hbw, hWO⟩ := hA
  have hW := RBM.Green.tendsto_W sz h𝔠 hsz hbw
  filter_upwards [hWO, hW.eventually_ge_atTop 1,
    ((tendsto_rpow_atTop (half_pos hτ)).comp hW).eventually_ge_atTop (3 * max (16 * C) 128)] with n hWOn hW1 hbig
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hlam : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) hWOn.1
  have hN : 0 < Nsz sz n := Nsz_pos sz n
  have hη : 0 < etaQ sz n ε₀ := by
    unfold etaQ
    have := Real.rpow_pos_of_pos hW0 ((d : ℝ) / 2)
    have := Real.rpow_pos_of_pos hW0 (-ε₀)
    positivity
  have hsq : ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2) * ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2) =
      ((sz.W n : ℕ) : ℝ) ^ d := by
    rw [← Real.rpow_add hW0, ← Real.rpow_natCast]; congr 1; ring
  have hNη : Nsz sz n * etaQ sz n ε₀ =
      ((sz.W n : ℕ) : ℝ) ^ (-ε₀) * (sz.lam n * ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2)) := by
    unfold etaQ; field_simp
  have hηL : etaQ sz n ε₀ ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d := etaQ_le sz n hε₀ h𝔡 hW1 hWOn.1
  have hB := calB_le_two_inv sz n (by omega) hη (le_refl (0 : ℝ)) hηL hlam
  have hB0 : 0 ≤ calB sz n (etaQ sz n ε₀) 0 := calB_nonneg sz n hη le_rfl
  have := queChain_real (W := ((sz.W n : ℕ) : ℝ)) (lam := sz.lam n) (N := Nsz sz n) (η := etaQ sz n ε₀)
    (B := calB sz n (etaQ sz n ε₀) 0) (c := c) d h𝔡 hε₀ (by linarith) hτ hC hW1 hlam hN hη hsq hNη hWOn.1
    (lam_sq_mul_pow_ge sz n hWOn.1) hB0 hB hbig
  unfold qdBoundExp
  exact this

/-- **`QUE` from `QDiff`** (the statement `MAQUE`; RBM2D `QUE_of_QDiff`, for every `d ≥ 3`):
`QDiff` at `(κ, ε, τ/2, D) = (κ, 𝔠(𝔡 - ε₀), τ/2, 1)` and `z = E + iη_Q ∈ 𝐃_{κ,ε}` (`queDomain`), the row
differences `queRowDiff`, `queFixed` at each `(n, E)` and the exponent count `queChain`.  The hypotheses
`0 < c`, `c < ε₀`, `c < 𝔡/5` of `QUE` are not used. -/
theorem QUE_of_QDiff : MAQUE := by
  intro hQD d hd 𝔠 𝔡 sz hA κ hκ ε₀ c τ hε₀ hε₀𝔡 hc hcε hc𝔡 hτ
  have h𝔠 : 0 < 𝔠 := hA.1
  have h𝔡 : 0 < 𝔡 := hA.2.1
  obtain ⟨C, hC, hrow⟩ := queRowDiff d hd 𝔡 κ h𝔡 hκ
  have hε : 0 < 𝔠 * (𝔡 - ε₀) := mul_pos h𝔠 (by linarith)
  have hQ := hQD d hd 𝔠 𝔡 sz hA κ (𝔠 * (𝔡 - ε₀)) (τ / 2) 1 hκ hε (half_pos hτ) one_pos
  have hdom := queDomain sz hA (κ := κ) hε₀ (by linarith)
  have hch := queChain hd sz hA ε₀ c τ C hε₀ hε₀𝔡 hτ hC
  filter_upwards [hQ, hdom, hch, hA.2.2.2.2] with n hQn hdomn hchn hWOn
  intro E hE
  have hD := hdomn E hE
  have hz0 := locDomain_im_pos hD
  have him : (((E : ℝ) : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I).im = etaQ sz n ε₀ := by simp
  have hlam : 0 < sz.lam n :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos (W_pos_real sz n) _) hWOn.1
  have hη : 0 < etaQ sz n ε₀ := by rw [← him]; exact hz0
  have hz1 : (((E : ℝ) : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I).im ≤ 1 := hD.2.2
  have hK := hrow sz n hlam hWOn.2 _ hz0 hz1 hD.1
  have hQ' : ∀ a b : Zd d (sz.L n),
      ‖(∫ ω, avg2 sz n (fun x y => ((‖sz.Gn n (((E : ℝ) : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I) ω x y‖ ^ 2 : ℝ) : ℂ)) a b
          ∂(Sizes.seqP sz)) - profPM sz n (((E : ℝ) : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I) a b‖ ≤
        qdBoundExp sz n (τ / 2) (etaQ sz n ε₀) ∧
      ‖(∫ ω, avg2 sz n (fun x y => sz.Gn n (((E : ℝ) : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I) ω x y *
          sz.Gn n (((E : ℝ) : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I) ω y x) a b ∂(Sizes.seqP sz)) -
          profPP sz n (((E : ℝ) : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I) a b‖ ≤
        qdBoundExp sz n (τ / 2) (etaQ sz n ε₀) := by
    intro a b
    have h := hQn.2 _ hD a b
    rwa [him] at h
  obtain ⟨h1, h2⟩ := queFixed sz n ε₀ c E (qdBoundExp sz n (τ / 2) (etaQ sz n ε₀))
    (C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d) _ rfl hη hQ' (fun a b b' => hK a b b')
  refine ⟨fun a => (h1 a).trans ?_, fun A hA' => (h2 A hA').trans ?_⟩ <;>
    exact ENNReal.ofReal_le_ofReal hchn

end QUEChain

end RBM.Endpoints

end
