/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.TwistAvgA2

/-!
# The twisted averaged law at the block Anderson model, part C: `BATwistAvgProd`

Proof of Lemma 8.6 (`lem:TL1_BA`), last part: the bootstrap with the quadratic step `TwistAvgB_S1`, Markov at the law, and the union over the pairs.

`BA/TwistAvgA` and `BA/TwistAvgA2` proved the recursion `BATwistAvgRec` (`baTwistAvgRec_holds`).  This file bootstraps it:
`baTwistAvgProd_of_rec : T2427_TL1b` and `baTwistAvgProd_holds`.

Constants (for `τ, D > 0`, the datum `𝔠, 𝔡, ε`, `c = min(2𝔡𝔠, ε)/2`):
`p = ⌈(D+4)/τ⌉`, `ε' = d min(c, τ/2)`, `D' = 2p+2`, `C' = (4p+2)K+2`.

Contents: section 1 the quadratic step `TwistAvgB_S1` (the real-algebra step; `N^{-D'} ≤ B^{2p}` from `B ≥ N⁻¹`, so no
case split on a floor constant); section 2 `Bctl` ceiling along `BAFlow` and absorption
`K W^{ε'} B ≤ 1/2`; section 3 the maximum `X ≤ C' W^{ε'} B`; section 4 Markov per pair, the exponent
count and the union bound; section 5 one size `n`; section 6 `TwistAvgB_law_of_recAt`,
`baTwistAvgProd_of_rec`, `baTwistAvgProd_holds`.
Helpers carry the stem `TwistAvgB_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedFintypeInType false

open MeasureTheory Filter
open scoped Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph RBM.Green

/-! ## 1. The quadratic bootstrap at the maximizer -/

section S1

/-- The quadratic step (`TwistAvgB_S1`): at the maximizer `X = X_{c₁c₂}`, `a = K w B ≤ 1/2`, `w = W^{ε'} ≥ 1`,
`e ≤ B^{2p}` (so `N^{-D'} ≤ B^{2p}` from `B ≥ N⁻¹`, `D' = 2p + 2`) and the recursion give `X ≤ ((4p+2)K+2) w B`.
Case `X ≤ B`: trivial.  Case `X > B`: `e ≤ B² X^{2p-2}`, divide by `X^{2p-2}`, `X² ≤ 2K w B X + (4pK w + 2) B²`, and a direct contradiction with
`X > C' w B` (no square root). -/
private theorem TwistAvgB_S1 {p : ℕ} (hp : 1 ≤ p) {K w B X e : ℝ} (hK : 0 < K) (hw : 1 ≤ w) (hB : 0 < B)
    (ha : K * (w * B) ≤ 1 / 2) (he : e ≤ B ^ (2 * p))
    (h : X ^ (2 * p) ≤ K * (w * B) * (X ^ (2 * p - 1) + X * X ^ (2 * p - 1)) +
      2 * (p : ℝ) * K * (w * B ^ 2) * X ^ (2 * p - 2) + e) :
    X ≤ ((4 * p + 2) * K + 2) * (w * B) := by
  by_contra hcon
  replace hcon := not_le.mp hcon
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hy : 0 < w * B := mul_pos (by linarith) hB
  have hC1 : 1 ≤ (4 * (p : ℝ) + 2) * K + 2 := by nlinarith [mul_nonneg hp0 hK.le]
  have hyB : B ≤ w * B := by nlinarith
  have hXy : w * B ≤ ((4 * (p : ℝ) + 2) * K + 2) * (w * B) := by nlinarith
  have hXB : B < X := lt_of_le_of_lt (hyB.trans hXy) hcon
  have hX0 : 0 < X := hB.trans hXB
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 2 * p = m + 2 := ⟨2 * p - 2, by omega⟩
  have h1 : 2 * p - 1 = m + 1 := by omega
  have h2 : 2 * p - 2 = m := by omega
  rw [h1, h2] at h
  rw [hm] at h he
  have hXm : 0 < X ^ m := pow_pos hX0 m
  have hBm : B ^ m ≤ X ^ m := pow_le_pow_left₀ hB.le hXB.le m
  have he' : e ≤ X ^ m * B ^ 2 := by
    calc e ≤ B ^ (m + 2) := he
      _ = B ^ m * B ^ 2 := by ring
      _ ≤ X ^ m * B ^ 2 := mul_le_mul_of_nonneg_right hBm (sq_nonneg _)
  have key0 : X ^ m * X ^ 2 ≤ X ^ m * (K * (w * B) * X + K * (w * B) * X ^ 2 + 2 * (p : ℝ) * K * (w * B ^ 2) + B ^ 2) := by
    have e1 : X ^ (m + 2) = X ^ m * X ^ 2 := by ring
    have e2 : X ^ (m + 1) = X ^ m * X := by ring
    rw [e1, e2] at h
    nlinarith [h, he']
  have key : X ^ 2 ≤ K * (w * B) * X + K * (w * B) * X ^ 2 + 2 * (p : ℝ) * K * (w * B ^ 2) + B ^ 2 :=
    le_of_mul_le_mul_left key0 hXm
  have hq : X ^ 2 ≤ 2 * K * (w * B) * X + (4 * (p : ℝ) * K * w + 2) * B ^ 2 := by
    have hX2 : 0 ≤ X ^ 2 := sq_nonneg X
    nlinarith [mul_nonneg hX2 (by linarith : (0 : ℝ) ≤ 1 / 2 - K * (w * B))]
  -- contradiction with `X > C' y`, `y = w B`
  set y := w * B with hydef
  set c2 : ℝ := 4 * (p : ℝ) * K + 2 with hc2
  have hc2pos : 0 < c2 := by rw [hc2]; nlinarith [mul_nonneg hp0 hK.le]
  have hd : c2 * y < X - 2 * K * y := by
    have : (4 * (p : ℝ) + 2) * K + 2 = 2 * K + c2 := by rw [hc2]; ring
    rw [this] at hcon
    nlinarith
  have h3 : ((4 * (p : ℝ) + 2) * K + 2) * y * (c2 * y) < X * (X - 2 * K * y) :=
    mul_lt_mul'' hcon hd (by positivity) (by positivity)
  have h4 : c2 * y ^ 2 ≤ ((4 * (p : ℝ) + 2) * K + 2) * y * (c2 * y) := by
    have : 0 ≤ (((4 * (p : ℝ) + 2) * K + 2) - 1) * (c2 * y ^ 2) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith
  have h5 : (4 * (p : ℝ) * K * w + 2) * B ^ 2 ≤ c2 * y ^ 2 := by
    have hw1 : 0 ≤ w - 1 := by linarith
    have : 0 ≤ B ^ 2 * (4 * (p : ℝ) * K * w * (w - 1) + 2 * (w ^ 2 - 1)) := by
      apply mul_nonneg (sq_nonneg _)
      have : 0 ≤ w ^ 2 - 1 := by nlinarith
      have : 0 ≤ 4 * (p : ℝ) * K * w * (w - 1) := by
        have : 0 ≤ 4 * (p : ℝ) * K * w := by positivity
        exact mul_nonneg this hw1
      linarith
    rw [hc2, hydef]
    nlinarith
  nlinarith

end S1

/-! ## 2. `Bctl` along `BAFlow`: the ceiling `B ≤ N^{-2𝔡𝔠} + 2N^{-ε}`, the floor `B ≥ N⁻¹`, the absorption `K W^{ε'} B ≤ 1/2` -/

section Bctl

variable {d : ℕ} {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}

/-- Ceiling (`B_{t,0} = (λ² + 1 - t)⁻¹ + (L^d (1-t))⁻¹`, `W^{-d} B ≤ (λ² W^d)⁻¹ + (N (1-t))⁻¹`; `(λ² W^d)⁻¹ ≤ W^{-2𝔡} ≤ N^{-2𝔡𝔠}` from `WO`, `Bandwidth`;
`1 - t ≥ Im z/2 ≥ N^{-1+ε}/2`, `BAExp14a_one_sub_t`, `BAdom`): eventually `W^{-d} B_{t_n,0} ≤ N^{-2𝔡𝔠} + 2 N^{-ε}`.  Adapted from `lwN_Bctl_le`
(`Graph/LWTermExpN`, `STFlow`) to `BAFlow`. -/
private theorem TwistAvgB_Bctl_le (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (htT : ∀ n, t n ≤ BAflowT0 sz z n) :
    ∀ᶠ n in atTop, sz.Bctl n (t n) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(2 * 𝔡 * 𝔠)) + 2 * ((sz.size n : ℕ) : ℝ) ^ (-ε) := by
  have hband : sz.Bandwidth 𝔠 := hflow.1.2.2.2.1
  have hWO : sz.WO 𝔡 := hflow.1.2.2.2.2
  filter_upwards [hWO, hband] with n hwo hbn
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  obtain ⟨hzpos, -, -, hT1⟩ := BAflow_T0_bounds hκ hflow n
  have hu1 : t n < 1 := lt_of_le_of_lt (htT n) hT1
  have hlam : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) hwo.1
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW d
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := pow_pos hL d
  have hone := BAExp14a_one_sub_t hκ hflow n (htT n)
  have hNim : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) ≤ (z n).im := (hflow.2 n).2.1
  have hsz2 : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    unfold Sizes.size; push_cast; ring
  have hBc : sz.Bctl n (t n) = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - t n))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - t n))⁻¹) := by
    unfold Sizes.Bctl Bparam
    rw [abs_of_pos (by linarith : (0 : ℝ) < 1 - t n)]
    simp
  have hA : (((sz.L n : ℕ) : ℝ) ^ d * (1 - t n))⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (-ε) := by
    have h1 : (((sz.L n : ℕ) : ℝ) ^ d * (1 - t n))⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ = (((sz.size n : ℕ) : ℝ) * (1 - t n))⁻¹ := by
      rw [hsz2]; field_simp
    rw [h1]
    have hNε : 0 < ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) := Real.rpow_pos_of_pos hN0 _
    have h2 : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 2 ≤ 1 - t n := by linarith
    have h3 : ((sz.size n : ℕ) : ℝ) * (((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 2) ≤ ((sz.size n : ℕ) : ℝ) * (1 - t n) :=
      mul_le_mul_of_nonneg_left h2 hN0.le
    have h4 : ((sz.size n : ℕ) : ℝ) * (((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 2) = ((sz.size n : ℕ) : ℝ) ^ ε / 2 := by
      have : ((sz.size n : ℕ) : ℝ) ^ ε = ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) := by
        conv_lhs => rw [show ε = 1 + (-1 + ε) by ring]
        rw [Real.rpow_add hN0, Real.rpow_one]
      rw [this]; ring
    rw [h4] at h3
    have h5 : 0 < ((sz.size n : ℕ) : ℝ) ^ ε / 2 := by positivity
    calc (((sz.size n : ℕ) : ℝ) * (1 - t n))⁻¹ ≤ (((sz.size n : ℕ) : ℝ) ^ ε / 2)⁻¹ := inv_anti₀ h5 h3
      _ = 2 * ((sz.size n : ℕ) : ℝ) ^ (-ε) := by rw [Real.rpow_neg hN0.le]; field_simp
  have hB : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-(2 * 𝔡 * 𝔠)) := by
    have h1 := Sizes.lam_sq_mul_pow_ge sz n hwo.1
    have h2 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹ = (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
      rw [mul_comm, mul_inv]
    rw [h2]
    have hNc : 0 < ((sz.size n : ℕ) : ℝ) ^ 𝔠 := Real.rpow_pos_of_pos hN0 _
    calc (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡))⁻¹ :=
          inv_anti₀ (Real.rpow_pos_of_pos hW _) h1
      _ = ((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡)) := (Real.rpow_neg hW.le _).symm
      _ ≤ (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (-(2 * 𝔡)) := Real.rpow_le_rpow_of_nonpos hNc hbn (by linarith [hflow.1.2.1])
      _ = ((sz.size n : ℕ) : ℝ) ^ (-(2 * 𝔡 * 𝔠)) := by rw [← Real.rpow_mul hN0.le]; congr 1; ring
  rw [hBc, mul_add]
  have hfirst : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + (1 - t n))⁻¹ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹ :=
    mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (by linarith)) (inv_nonneg.mpr hWd.le)
  have hsecond : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d * (1 - t n))⁻¹ ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (-ε) := by
    rw [mul_comm]; exact hA
  linarith

/-- Absorption: for `ε' / d ≤ c = min(2𝔡𝔠, ε)/2` and `K > 0`, eventually `K W^{ε'} B ≤ 1/2`
(`W^{ε'} ≤ N^{ε'/d} ≤ N^c` by `Sizes.W_rpow_le`; `B ≤ 3N^{-2c}`; `3K N^{-c} ≤ 1/2` once `N^c ≥ 6K`). -/
private theorem TwistAvgB_absorb (hd : 0 < d) (hκ : 0 < κ) (hε : 0 < ε) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ}
    (htT : ∀ n, t n ≤ BAflowT0 sz z n) {K ε' : ℝ} (hK : 0 < K) (hε' : 0 ≤ ε') (hεc : ε' / d ≤ min (2 * 𝔡 * 𝔠) ε / 2) :
    ∀ᶠ n in atTop, K * (((sz.W n : ℕ) : ℝ) ^ ε' * sz.Bctl n (t n)) ≤ 1 / 2 := by
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have h𝔡 : 0 < 𝔡 := hflow.1.2.1
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hsize := Sizes.tendsto_size sz hsz
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = min (2 * 𝔡 * 𝔠) ε / 2 := ⟨_, rfl⟩
  have hc : 0 < c := by
    rw [hcdef]; have := lt_min (mul_pos (mul_pos two_pos h𝔡) h𝔠) hε; linarith
  have hc1 : 2 * c ≤ 2 * 𝔡 * 𝔠 := by rw [hcdef]; have := min_le_left (2 * 𝔡 * 𝔠) ε; linarith
  have hc2 : 2 * c ≤ ε := by rw [hcdef]; have := min_le_right (2 * 𝔡 * 𝔠) ε; linarith
  rw [← hcdef] at hεc
  have hbig : ∀ᶠ n in atTop, 6 * K ≤ ((sz.size n : ℕ) : ℝ) ^ c :=
    ((tendsto_rpow_atTop hc).comp (tendsto_natCast_atTop_iff.2 hsize)).eventually (eventually_ge_atTop (6 * K))
  filter_upwards [TwistAvgB_Bctl_le hκ hflow htT, hbig, hsize.eventually (eventually_ge_atTop 1)] with n hB hN6 hN1
  have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hNc : 0 < ((sz.size n : ℕ) : ℝ) ^ c := Real.rpow_pos_of_pos hN0 _
  have hW1 : ((sz.W n : ℕ) : ℝ) ^ ε' ≤ ((sz.size n : ℕ) : ℝ) ^ c :=
    (Sizes.W_rpow_le sz hd n hε').trans (Real.rpow_le_rpow_of_exponent_le hN1' hεc)
  have hB3 : sz.Bctl n (t n) ≤ 3 * ((sz.size n : ℕ) : ℝ) ^ (-(2 * c)) := by
    have e1 : ((sz.size n : ℕ) : ℝ) ^ (-(2 * 𝔡 * 𝔠)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(2 * c)) :=
      Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
    have e2 : ((sz.size n : ℕ) : ℝ) ^ (-ε) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(2 * c)) :=
      Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
    linarith
  have hBnn : 0 ≤ sz.Bctl n (t n) := by unfold Sizes.Bctl Bparam; positivity
  have hprod : ((sz.size n : ℕ) : ℝ) ^ c * ((sz.size n : ℕ) : ℝ) ^ (-(2 * c)) = ((sz.size n : ℕ) : ℝ) ^ (-c) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hinv : ((sz.size n : ℕ) : ℝ) ^ (-c) * ((sz.size n : ℕ) : ℝ) ^ c = 1 := by
    rw [← Real.rpow_add hN0]; simp
  calc K * (((sz.W n : ℕ) : ℝ) ^ ε' * sz.Bctl n (t n))
      ≤ K * (((sz.size n : ℕ) : ℝ) ^ c * (3 * ((sz.size n : ℕ) : ℝ) ^ (-(2 * c)))) := by
        apply mul_le_mul_of_nonneg_left _ hK.le
        exact mul_le_mul hW1 hB3 hBnn hNc.le
    _ = 3 * K * ((sz.size n : ℕ) : ℝ) ^ (-c) := by rw [← hprod]; ring
    _ ≤ 1 / 2 := by
        have hp : 0 < ((sz.size n : ℕ) : ℝ) ^ (-c) := Real.rpow_pos_of_pos hN0 _
        nlinarith [mul_le_mul_of_nonneg_left hN6 hp.le]

end Bctl

/-! ## 3. The maximum: `X ≤ C' W^{ε'} B` -/

section Xmax

variable {d : ℕ} {sz : Sizes d}

/-- `X_{c₁c₂} ≥ 0`. -/
private theorem TwistAvgB_X_nonneg (C : FlowFM sz) (μ : Measure sz.SeqΩ) (n : ℕ) (t : ℝ) (p : ℕ) (c₁ c₂ : Zd d (sz.L n)) :
    0 ≤ twAvgX C μ n t p c₁ c₂ :=
  Real.rpow_nonneg (integral_nonneg fun ω => pow_nonneg (norm_nonneg _) _) _

/-- `X_{c₁c₂}^{2p} = 𝔼‖twTr‖^{2p}`. -/
private theorem TwistAvgB_X_pow (C : FlowFM sz) (μ : Measure sz.SeqΩ) (n : ℕ) (t : ℝ) {p : ℕ} (hp : 1 ≤ p) (c₁ c₂ : Zd d (sz.L n)) :
    twAvgX C μ n t p c₁ c₂ ^ (2 * p) = ∫ ω, ‖twTr C n t ω c₁ c₂‖ ^ (2 * p) ∂μ := by
  have hE : 0 ≤ ∫ ω, ‖twTr C n t ω c₁ c₂‖ ^ (2 * p) ∂μ := integral_nonneg fun ω => pow_nonneg (norm_nonneg _) _
  have hp0 : (p : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ p := by exact_mod_cast hp
                               linarith
  unfold twAvgX
  rw [← Real.rpow_natCast, ← Real.rpow_mul hE]
  have : (1 : ℝ) / (2 * (p : ℝ)) * ((2 * p : ℕ) : ℝ) = 1 := by push_cast; field_simp
  rw [this, Real.rpow_one]

/-- Apply `TwistAvgB_S1` at a pair attaining `twAvgXmax` (`Finset.exists_mem_eq_sup'`): `twAvgXmax ≤ ((4p+2)K+2) w B` from the recursion at that pair. -/
private theorem TwistAvgB_Xmax_le (C : FlowFM sz) (μ : Measure sz.SeqΩ) (n : ℕ) (t : ℝ) {p : ℕ} (hp : 1 ≤ p) {K w B e : ℝ}
    (hK : 0 < K) (hw : 1 ≤ w) (hB : 0 < B) (ha : K * (w * B) ≤ 1 / 2) (he : e ≤ B ^ (2 * p))
    (hrec : ∀ c₁ c₂ : Zd d (sz.L n), twAvgX C μ n t p c₁ c₂ ^ (2 * p) ≤
      K * (w * B) * (twAvgX C μ n t p c₁ c₂ ^ (2 * p - 1) + twAvgXmax C μ n t p * twAvgX C μ n t p c₁ c₂ ^ (2 * p - 1)) +
      2 * (p : ℝ) * K * (w * B ^ 2) * twAvgX C μ n t p c₁ c₂ ^ (2 * p - 2) + e) :
    twAvgXmax C μ n t p ≤ ((4 * p + 2) * K + 2) * (w * B) := by
  obtain ⟨q, -, hq⟩ := Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (Zd d (sz.L n) × Zd d (sz.L n))))
    ⟨((0 : Zd d (sz.L n)), (0 : Zd d (sz.L n))), Finset.mem_univ _⟩ (fun q : Zd d (sz.L n) × Zd d (sz.L n) => twAvgX C μ n t p q.1 q.2)
  have hqX : twAvgXmax C μ n t p = twAvgX C μ n t p q.1 q.2 := hq
  have h := hrec q.1 q.2
  rw [← hqX] at h
  rw [hqX]
  rw [hqX] at h
  exact TwistAvgB_S1 hp hK hw hB ha he h

end Xmax

/-! ## 4. Markov per pair, the exponent count, the union over the pairs -/

section Markov

/-- Markov at the law (`mul_meas_ge_le_integral_of_nonneg` with `f = T^{2p}`, level `s^{2p}`): `μ{s < T} ≤ (X_b/s)^{2p}` if `𝔼 T^{2p} ≤ X_b^{2p}`. -/
private theorem TwistAvgB_markov {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] {T : Ω → ℝ} (hT0 : ∀ ω, 0 ≤ T ω)
    {p : ℕ} (hint : Integrable (fun ω => T ω ^ (2 * p)) μ) {s Xb : ℝ} (hs : 0 < s) (hXb : ∫ ω, T ω ^ (2 * p) ∂μ ≤ Xb ^ (2 * p)) :
    μ {ω | s < T ω} ≤ ENNReal.ofReal ((Xb / s) ^ (2 * p)) := by
  have hM := mul_meas_ge_le_integral_of_nonneg (μ := μ) (f := fun ω => T ω ^ (2 * p))
    (Filter.Eventually.of_forall fun ω => pow_nonneg (hT0 ω) _) hint (s ^ (2 * p))
  have hsub : {ω | s < T ω} ⊆ {ω | s ^ (2 * p) ≤ T ω ^ (2 * p)} :=
    fun ω hω => pow_le_pow_left₀ hs.le (le_of_lt hω) _
  have hsp : 0 < s ^ (2 * p) := pow_pos hs _
  calc μ {ω | s < T ω} ≤ μ {ω | s ^ (2 * p) ≤ T ω ^ (2 * p)} := measure_mono hsub
    _ = ENNReal.ofReal (μ.real {ω | s ^ (2 * p) ≤ T ω ^ (2 * p)}) := (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal ((Xb / s) ^ (2 * p)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [div_pow, le_div_iff₀ hsp]
        nlinarith [hM, hXb]

/-- The exponent count (`N ≥ 1`, `w ≤ N^{τ/2}`, `pτ ≥ D + 4`, `C'^{2p} ≤ N²`): `(C' w / N^τ)^{2p} ≤ N^{-(D+2)}`. -/
private theorem TwistAvgB_expo {N τ D w C' : ℝ} {p : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w) (hC : 0 < C') (hwN : w ≤ N ^ (τ / 2))
    (hpτ : D + 4 ≤ p * τ) (hCN : C' ^ (2 * p) ≤ N ^ 2) :
    (C' * w / N ^ τ) ^ (2 * p) ≤ N ^ (-(D + 2)) := by
  have hN0 : 0 < N := by linarith
  have ha : 0 < N ^ (τ / 2) := Real.rpow_pos_of_pos hN0 _
  have hNτ : N ^ τ = N ^ (τ / 2) * N ^ (τ / 2) := by rw [← Real.rpow_add hN0]; congr 1; ring
  have h1 : C' * w / N ^ τ ≤ C' / N ^ (τ / 2) := by
    rw [hNτ]
    calc C' * w / (N ^ (τ / 2) * N ^ (τ / 2)) ≤ C' * N ^ (τ / 2) / (N ^ (τ / 2) * N ^ (τ / 2)) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hwN hC.le) (by positivity)
      _ = C' / N ^ (τ / 2) := by field_simp
  have h2 : (C' * w / N ^ τ) ^ (2 * p) ≤ (C' / N ^ (τ / 2)) ^ (2 * p) :=
    pow_le_pow_left₀ (by positivity) h1 _
  have h3 : (N ^ (τ / 2)) ^ (2 * p) = N ^ ((p : ℝ) * τ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  have h4 : N ^ (D + 4) ≤ N ^ ((p : ℝ) * τ) := Real.rpow_le_rpow_of_exponent_le hN hpτ
  have h5 : N ^ (-(D + 2)) = N ^ 2 / N ^ (D + 4) := by
    rw [show (-(D + 2)) = (2 : ℝ) - (D + 4) by ring, Real.rpow_sub hN0, Real.rpow_two]
  calc (C' * w / N ^ τ) ^ (2 * p) ≤ (C' / N ^ (τ / 2)) ^ (2 * p) := h2
    _ = C' ^ (2 * p) / N ^ ((p : ℝ) * τ) := by rw [div_pow, h3]
    _ ≤ N ^ 2 / N ^ (D + 4) := div_le_div₀ (by positivity) hCN (Real.rpow_pos_of_pos hN0 _) h4
    _ = N ^ (-(D + 2)) := h5.symm

/-- Union bound over a finite index set (`measure_iUnion_fintype_le`). -/
private theorem TwistAvgB_union {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {ι : Type*} [Fintype ι] (S : ι → Set Ω) {r : ℝ}
    (hr : ∀ i, μ (S i) ≤ ENNReal.ofReal r) :
    μ (⋃ i, S i) ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * r) := by
  calc μ (⋃ i, S i) ≤ ∑ i, μ (S i) := measure_iUnion_fintype_le μ S
    _ ≤ ∑ _i : ι, ENNReal.ofReal r := Finset.sum_le_sum fun i _ => hr i
    _ = ENNReal.ofReal ((Fintype.card ι : ℝ) * r) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

end Markov

/-! ## 5. One size `n`: the bad event of `BATwistAvgLaw` has probability `≤ N^{-D}` -/

section Step

variable {d : ℕ} {sz : Sizes d}

/-- The number of ordered pairs of blocks is at most `N²` (`L^{2d} ≤ (WL)^{2d}`, `W ≥ 1`). -/
private theorem TwistAvgB_card_le (n : ℕ) : Fintype.card (Zd d (sz.L n) × Zd d (sz.L n)) ≤ sz.size n ^ 2 := by
  have hL : (sz.L n) ^ d ≤ sz.size n := by
    rw [Sizes.size]; exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d
  rw [Fintype.card_prod, card_Zd, sq]
  exact Nat.mul_le_mul hL hL

/-- Markov and union at one size (per `τ`, no net): if `X ≤ C' w B` (`w = W^{ε'}`), `w ≤ N^{τ/2}`, `pτ ≥ D + 4`, `C'^{2p} ≤ N²`, then
`μ{∃ (c₁,c₂), ‖twTr c₁ c₂‖ > N^τ B} ≤ N^{-D}`: per pair `≤ (C' w / N^τ)^{2p} ≤ N^{-(D+2)}`, `L^{2d} ≤ N²` pairs. -/
private theorem TwistAvgB_step (C : FlowFM sz) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ] (n : ℕ) (t : ℝ) {p : ℕ} (hp : 1 ≤ p)
    {τ D C' w B : ℝ} (hB : 0 < B) (hC' : 0 < C') (hw : 0 < w)
    (hint : ∀ c₁ c₂ : Zd d (sz.L n), Integrable (fun ω => ‖twTr C n t ω c₁ c₂‖ ^ (2 * p)) μ)
    (hXmax : twAvgXmax C μ n t p ≤ C' * (w * B)) (hN1 : 1 ≤ ((sz.size n : ℕ) : ℝ))
    (hwN : w ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2)) (hpτ : D + 4 ≤ p * τ) (hCN : C' ^ (2 * p) ≤ ((sz.size n : ℕ) : ℝ) ^ 2) :
    μ {ω | ∃ q : Zd d (sz.L n) × Zd d (sz.L n), ((sz.size n : ℕ) : ℝ) ^ τ * B < ‖twTr C n t ω q.1 q.2‖} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hs : 0 < ((sz.size n : ℕ) : ℝ) ^ τ * B := mul_pos (Real.rpow_pos_of_pos hN0 _) hB
  have hper : ∀ q : Zd d (sz.L n) × Zd d (sz.L n), μ {ω | ((sz.size n : ℕ) : ℝ) ^ τ * B < ‖twTr C n t ω q.1 q.2‖} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D + 2))) := by
    intro q
    have hXq : twAvgX C μ n t p q.1 q.2 ≤ C' * (w * B) :=
      (Finset.le_sup' (fun q : Zd d (sz.L n) × Zd d (sz.L n) => twAvgX C μ n t p q.1 q.2) (Finset.mem_univ q)).trans hXmax
    have hXpow : ∫ ω, ‖twTr C n t ω q.1 q.2‖ ^ (2 * p) ∂μ ≤ (C' * (w * B)) ^ (2 * p) := by
      rw [← TwistAvgB_X_pow C μ n t hp q.1 q.2]
      exact pow_le_pow_left₀ (TwistAvgB_X_nonneg C μ n t p q.1 q.2) hXq _
    refine (TwistAvgB_markov μ (fun ω => norm_nonneg _) (hint q.1 q.2) hs hXpow).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have hq : C' * (w * B) / (((sz.size n : ℕ) : ℝ) ^ τ * B) = C' * w / ((sz.size n : ℕ) : ℝ) ^ τ := by
      rw [← mul_assoc]; exact mul_div_mul_right _ _ hB.ne'
    rw [hq]
    exact TwistAvgB_expo hN1 hw hC' hwN hpτ hCN
  have hset : {ω | ∃ q : Zd d (sz.L n) × Zd d (sz.L n), ((sz.size n : ℕ) : ℝ) ^ τ * B < ‖twTr C n t ω q.1 q.2‖} =
      ⋃ q : Zd d (sz.L n) × Zd d (sz.L n), {ω | ((sz.size n : ℕ) : ℝ) ^ τ * B < ‖twTr C n t ω q.1 q.2‖} := by
    ext ω; simp
  rw [hset]
  refine (TwistAvgB_union μ _ hper).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hc : (Fintype.card (Zd d (sz.L n) × Zd d (sz.L n)) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast TwistAvgB_card_le (sz := sz) n
  have hpos : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-(D + 2)) := Real.rpow_nonneg hN0.le _
  calc (Fintype.card (Zd d (sz.L n) × Zd d (sz.L n)) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-(D + 2))
      ≤ ((sz.size n : ℕ) : ℝ) ^ 2 * ((sz.size n : ℕ) : ℝ) ^ (-(D + 2)) := mul_le_mul_of_nonneg_right hc hpos
    _ = ((sz.size n : ℕ) : ℝ) ^ (-D) := by
        rw [← Real.rpow_two, ← Real.rpow_add hN0]; congr 1; ring

end Step

/-! ## 6. The bootstrap: `baTwistAvgProd_of_rec`, `baTwistAvgProd_holds` -/

section Main

variable {d : ℕ} {sz : Sizes d}

/-- The core of the bootstrap: the recursion `BATwistAvgRecAt` at the constant `K` gives `BATwistAvgLaw`.  For `τ, D > 0`: `p = ⌈(D+4)/τ⌉`,
`ε' = d min(c, τ/2)`, `c = min(2𝔡𝔠, ε)/2`, `D' = 2p + 2`, `C' = (4p+2)K + 2`; eventually `K W^{ε'} B ≤ 1/2` (`TwistAvgB_absorb`),
`N^{-D'} ≤ B^{2p}` (`B ≥ N⁻¹`), `C'^{2p} ≤ N²`, `N ≥ 1`; then `X ≤ C' W^{ε'} B` (`TwistAvgB_S1`), Markov per pair and the union over the pairs (`TwistAvgB_step`).
No net, no `STLKgL`, `BAGbEXPii`, `BAGbEXPav`: the premises are those of `BATwistAvgRecAt`, integrability is `twAvgReg_holds`. -/
private theorem TwistAvgB_law_of_recAt (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) {z : ℕ → ℂ} (hflow : BAFlow sz κ ε 𝔠 𝔡 z)
    {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n) (htT : ∀ n, t n ≤ BAflowT0 sz z n) {K : ℝ} (hK : 0 < K)
    (hrec : BATwistAvgRecAt (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t K) :
    BATwistAvgLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t := by
  have hd0 : 0 < d := by omega
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have h𝔡 : 0 < 𝔡 := hflow.1.2.1
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = min (2 * 𝔡 * 𝔠) ε / 2 := ⟨_, rfl⟩
  have hc : 0 < c := by
    rw [hcdef]; have := lt_min (mul_pos (mul_pos two_pos h𝔡) h𝔠) hε; linarith
  intro τ hτ D hD
  obtain ⟨p, hpdef⟩ : ∃ p : ℕ, p = ⌈(D + 4) / τ⌉₊ := ⟨_, rfl⟩
  have hp1 : 1 ≤ p := by rw [hpdef]; exact Nat.ceil_pos.2 (by positivity)
  have hpτ : D + 4 ≤ (p : ℝ) * τ := by
    have h := Nat.le_ceil ((D + 4) / τ)
    rw [← hpdef, div_le_iff₀ hτ] at h
    exact h
  have hmin : 0 < min c (τ / 2) := lt_min hc (by linarith)
  obtain ⟨ε', hε'def⟩ : ∃ ε' : ℝ, ε' = (d : ℝ) * min c (τ / 2) := ⟨_, rfl⟩
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hε'pos : 0 < ε' := by rw [hε'def]; exact mul_pos hdR hmin
  have hε'd : ε' / d = min c (τ / 2) := by rw [hε'def]; field_simp
  have hεc : ε' / d ≤ min (2 * 𝔡 * 𝔠) ε / 2 := by rw [hε'd, ← hcdef]; exact min_le_left _ _
  have hετ : ε' / d ≤ τ / 2 := by rw [hε'd]; exact min_le_right _ _
  obtain ⟨C', hC'def⟩ : ∃ C' : ℝ, C' = (4 * (p : ℝ) + 2) * K + 2 := ⟨_, rfl⟩
  have hC'pos : 0 < C' := by rw [hC'def]; positivity
  have R := hrec p hp1 ε' (2 * (p : ℝ) + 2) hε'pos (by positivity)
  obtain ⟨hcont, -, -⟩ := twAvgReg_holds d κ ε 𝔠 𝔡 sz z hκ hε hflow
  have habs := TwistAvgB_absorb hd0 hκ hε hflow htT hK hε'pos.le hεc
  have hbigC : ∀ᶠ n in atTop, C' ^ (2 * p) ≤ ((sz.size n : ℕ) : ℝ) := hsz.eventually (eventually_ge_atTop _)
  filter_upwards [R, habs, hbigC, Sizes.tendsto_size sz hsz |>.eventually (eventually_ge_atTop 1)] with n hR hab hCN hN1
  have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have ht1 : t n < 1 := (ba_G_data hκ sz hflow n (ht0 n) (htT n)).1
  have hBpos : 0 < sz.Bctl n (t n) := STBctl_pos sz n ht1
  have hBfloor : ((sz.size n : ℕ) : ℝ)⁻¹ ≤ sz.Bctl n (t n) := RBM.Ind.ContinuityNet.cont_inv_size_le_Bctl sz n (ht0 n) ht1
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hw1 : 1 ≤ ((sz.W n : ℕ) : ℝ) ^ ε' := Real.one_le_rpow hW1 hε'pos.le
  have he : ((sz.size n : ℕ) : ℝ) ^ (-(2 * (p : ℝ) + 2)) ≤ sz.Bctl n (t n) ^ (2 * p) := by
    have h1 : ((sz.size n : ℕ) : ℝ) ^ (-(2 * (p : ℝ) + 2)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-((2 * p : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hN1' (by push_cast; linarith)
    have h2 : ((sz.size n : ℕ) : ℝ) ^ (-((2 * p : ℕ) : ℝ)) = (((sz.size n : ℕ) : ℝ)⁻¹) ^ (2 * p) := by
      rw [Real.rpow_neg hN0.le, Real.rpow_natCast, inv_pow]
    exact h1.trans (h2.le.trans (pow_le_pow_left₀ (inv_nonneg.2 hN0.le) hBfloor _))
  have hXmax := TwistAvgB_Xmax_le (baFMz sz z) (Sizes.seqP (sz.withLam 0)) n (t n) hp1 hK hw1 hBpos hab he hR
  have hwN : ((sz.W n : ℕ) : ℝ) ^ ε' ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    (Sizes.W_rpow_le sz hd0 n hε'pos.le).trans (Real.rpow_le_rpow_of_exponent_le hN1' hετ)
  have hCN' : C' ^ (2 * p) ≤ ((sz.size n : ℕ) : ℝ) ^ 2 := by nlinarith
  have hint : ∀ c₁ c₂ : Zd d (sz.L n), Integrable (fun ω => ‖twTr (baFMz sz z) n (t n) ω c₁ c₂‖ ^ (2 * p)) (Sizes.seqP (sz.withLam 0)) :=
    fun c₁ c₂ => (hcont n (t n) (ht0 n) (htT n) c₁ c₂).2.2.2.2 (2 * p)
  have hC'eq : ((4 * p + 2) * K + 2) = C' := by rw [hC'def]
  rw [hC'eq] at hXmax
  exact TwistAvgB_step (baFMz sz z) (Sizes.seqP (sz.withLam 0)) n (t n) hp1 hBpos hC'pos (lt_of_lt_of_le one_pos hw1) hint hXmax hN1' hwN hpτ hCN'

/-- `baTwistAvgProd_of_rec : T2427_TL1b`: the recursion gives the producer. -/
theorem baTwistAvgProd_of_rec : T2427_TL1b := by
  intro d hRec hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨K, hK, H⟩ := hRec hd κ ε 𝔡 hκ hε h𝔡
  intro 𝔠 sz z hflow t ht0 htT μ hA hM
  exact TwistAvgB_law_of_recAt hd hκ hε hflow ht0 htT hK (H 𝔠 sz z hflow t ht0 htT hA hM)

/-- `BATwistAvgProd` is proved (`baTwistAvgRec_holds` and `baTwistAvgProd_of_rec`): TL1 at the BA carrier, per `τ`, from `LWAvgLawgL` and `STLmaxgL`. -/
theorem baTwistAvgProd_holds (d : ℕ) : BATwistAvgProd d :=
  baTwistAvgProd_of_rec d (baTwistAvgRec_holds d)

end Main

end RBM.BA

end
