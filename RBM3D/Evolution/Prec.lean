/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step34Pins
import RBM3D.Evolution.SumDecay
import RBM3D.Evolution.SumDecayZero
import RBM3D.Evolution.Nonzero
import RBM3D.Propagator.Prop6Hold

/-!
# EK-6 (ticket T2053): the evolution-kernel lemmas at scale `N = (WL)^d`, as Steps 3-4 consume them

The five consumer pins `STEKSumNdecay`, `STEKSumRes1`, `STEKSumRes2NAL`, `STEKSumRes2`,
`STEKNonzero` (`RBM3D/Induction/Step34Pins.lean`, section 4) are proved from the merged
evolution-kernel theorems `ekSumNdecay_holds`, `ekSumDecay1_holds`, `ekSumDecayNAL_holds`,
`ekSumDecay2_holds`, `ekSumDecayNonzero_holds`; the propagator antecedents are discharged by
`prop5Decay_holds`, `prop5Short_holds`, `prop6Diff1_holds`, `prop8ZeroMode_holds`.

Source: the compiled probe `git show 3c58211:RBM3D/Probe/T2041Pins.lean`, lines 684-832
(`stek_sumNdecay`, `stek_sumRes2NAL`, copied verbatim as the bodies of `stek_sumNdecay_holds` and
`stek_sumRes2NAL_holds`); the other three are derived the same way (`prec_core` carries the shared
absorption step).  Paper: arXiv:2507.20274, `lem:sum_Ndecay`, `lem:sum_decay` (`3_5:1615-1659`),
`lem:sum_decay_nonzero` (`3_5:1666`).

How the pin constants are discharged along a sequence (`N = sz.size n`, `K = 1/𝔠`):
`W^{Cε} ≤ N^{τ/4}` from `W ≤ N^{1/d}` with `ε = min(1/2, τ d/(4C))`; `W^{-D₀+C} ≤ N^{-D}` from
`W ≥ N^𝔠` with `D₀ = C + 1 + D/𝔠`; `4 ≤ W^ε` and `log L ≤ W^ε` eventually (`W ≥ N^𝔠 → ∞`);
`L^d ≤ N ≤ W^{1/𝔠}`; `g ≤ 𝔡⁻¹` from `(eq:WO)` (DECISIONS §21, T2042a).
`STEKNonzero` carries `0 ≤ s` (DECISIONS §27, T2053 Amend 1).
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ## 1. Eventual facts along an admissible sequence -/

/-- `0 < ilambda ≤ 𝔡⁻¹` eventually, from `(eq:WO)`. -/
private theorem prec_lam_bounds {d : ℕ} (sz : Sizes d) {𝔡 : ℝ} (hWO : sz.WO 𝔡) :
    ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
  filter_upwards [hWO] with n hn
  exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _) hn.1, hn.2⟩

/-- `M ≤ W^a` eventually, for `a > 0`: `W ≥ N^𝔠 → ∞`. -/
private theorem prec_W_rpow_ge {d : ℕ} (sz : Sizes d) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (hSz : sz.SizeTendsto)
    (hBw : sz.Bandwidth 𝔠) {a : ℝ} (ha : 0 < a) (M : ℝ) :
    ∀ᶠ n in atTop, M ≤ ((sz.W n : ℕ) : ℝ) ^ a := by
  have hf : ∀ᶠ n in atTop, M ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * a) :=
    ((tendsto_rpow_atTop (mul_pos h𝔠 ha)).comp hSz).eventually (eventually_ge_atTop M)
  filter_upwards [hf, hBw] with n hn hb
  have hN : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  calc M ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * a) := hn
    _ = (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ a := Real.rpow_mul hN _ _
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ a := Real.rpow_le_rpow (Real.rpow_nonneg hN _) hb ha.le

/-- `4 ≤ W^ε` (with `ε > 0`) gives `1 < W`. -/
private theorem prec_one_lt_W {W ε : ℝ} (hW0 : 0 ≤ W) (hε : 0 < ε) (h4 : 4 ≤ W ^ ε) : 1 < W := by
  by_contra hcon
  push Not at hcon
  have := Real.rpow_le_one hW0 hcon hε.le
  linarith

/-- `L^d ≤ N ≤ W^{1/𝔠}` from `W ≥ N^𝔠` (`K = 1/𝔠`, DECISIONS §21). -/
private theorem prec_L_pow_le {d : ℕ} (sz : Sizes d) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (n : ℕ)
    (hb : ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ (sz.W n : ℝ)) :
    ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠) := by
  have hLW : (sz.L n) ^ d ≤ sz.size n := by
    have hW : 0 < sz.W n := sz.W_pos n
    exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ hW) d
  have h1 : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hLW
  have h2 := sz.size_rpow_le_W_rpow h𝔠 n hb (τ := 1) zero_le_one
  rw [Real.rpow_one] at h2
  exact h1.trans h2

/-- `log L ≤ W^ε` from `L^d ≤ W^K` and `W^{ε/2} ≥ 2K/(ε d)` (`log y ≤ y^a / a`, `a = ε d/(2K)`;
the paper's absorption of `log L`, T2016a). -/
private theorem prec_log_le {L W K ε : ℝ} {d : ℕ} (hd0 : 0 < d) (hL : 0 ≤ L) (hK : 0 < K) (hε : 0 < ε)
    (hW : 0 < W) (hLK : L ^ d ≤ W ^ K) (hM : 2 * K / (ε * d) ≤ W ^ (ε / 2)) : Real.log L ≤ W ^ ε := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd0
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ε * d / (2 * K) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  have h1 : Real.log L ≤ L ^ a / a := Real.log_le_rpow_div hL ha0
  have h2 : L ^ a ≤ W ^ (ε / 2) := by
    calc L ^ a = (L ^ (d : ℝ)) ^ (a / d) := by
          rw [← Real.rpow_mul hL]; congr 1; field_simp
      _ = (L ^ d) ^ (a / d) := by rw [Real.rpow_natCast]
      _ ≤ (W ^ K) ^ (a / d) := Real.rpow_le_rpow (pow_nonneg hL _) hLK (by positivity)
      _ = W ^ (ε / 2) := by
          rw [← Real.rpow_mul hW.le]; congr 1; rw [ha]; field_simp
  have hinv : 1 / a = 2 * K / (ε * d) := by rw [ha]; field_simp
  calc Real.log L ≤ L ^ a / a := h1
    _ ≤ W ^ (ε / 2) / a := div_le_div_of_nonneg_right h2 ha0.le
    _ = W ^ (ε / 2) * (2 * K / (ε * d)) := by rw [div_eq_mul_one_div, hinv]
    _ ≤ W ^ (ε / 2) * W ^ (ε / 2) := mul_le_mul_of_nonneg_left hM (Real.rpow_nonneg hW.le _)
    _ = W ^ ε := by rw [← Real.rpow_add hW]; congr 1; ring

/-- The window `W⁻¹ ≤ (1-t)/(1-s)` passes to every `v ∈ [s,t]`. -/
private theorem prec_window {W s t v : ℝ} (hsv : s ≤ v) (hvt : v ≤ t) (ht : t < 1)
    (hW : W⁻¹ ≤ (1 - t) / (1 - s)) : W⁻¹ ≤ (1 - t) / (1 - v) :=
  hW.trans (div_le_div_of_nonneg_left (by linarith) (by linarith : 0 < 1 - v) (by linarith))

/-- The ratio `(g²+|1-v|)/(g²+|1-t|) ≥ 1` for `v ≤ t < 1`. -/
private theorem prec_ratio_ge_one {g v t : ℝ} (hvt : v ≤ t) (ht : t < 1) :
    1 ≤ (g ^ 2 + |1 - v|) / (g ^ 2 + |1 - t|) := by
  have h1 : 0 < 1 - t := by linarith
  have h0 : 0 < g ^ 2 + |1 - t| := by
    have : 0 < |1 - t| := abs_pos.2 h1.ne'
    positivity
  rw [one_le_div h0]
  have : |1 - t| ≤ |1 - v| := by
    rw [abs_of_pos h1, abs_of_pos (by linarith : 0 < 1 - v)]; linarith
  linarith

/-! ## 2. The shared absorption step

The pins of `lem:sum_decay` have the shape `‖U∘A‖ ≤ W^{Cε} ρ ‖A‖ + W^{-D₀+C}` with `ρ ≥ 1` the ratio factor.
With `ε = min(1/2, τ d/(4C))`, `D₀ = C + 1 + D/𝔠`, the decay hypothesis w.h.p., `‖𝒜‖ ≺ X` and `X ≥ N^{-b}`
w.h.p., this gives `‖U∘A‖ ≺ ρ X` (`StochDomAt.of_highProbAt_add_rpow_neg`). -/

/-- Shared by `stek_sumRes1_holds` and `stek_sumRes2_holds` (`stek_sumRes2NAL_holds` is the probe text). -/
private theorem prec_core {d : ℕ} (sz : Sizes d) (hd0 : 0 < d) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠)
    (hSz : sz.SizeTendsto) (hBw : sz.Bandwidth 𝔠) {s t : ℕ → ℝ} {k : ℕ}
    (𝒜 : ∀ n, TimeIcc s t n → sz.SeqΩ → (Fin k → Zd d (sz.L n)) → ℂ) (hdec : STEKDecay sz s t 𝒜)
    (X : ∀ n, TimeIcc s t n → sz.SeqΩ → ℝ) (hlow : STEKLow sz s t X)
    (hdom : Prec sz (U := fun n => TimeIcc s t n) (fun n v ω => ‖𝒜 n v ω‖) X)
    (f : ∀ n, TimeIcc s t n → sz.SeqΩ → ℝ) (ρ : ∀ n, TimeIcc s t n → ℝ) {C : ℝ} (hC : 0 < C)
    (hρ : ∀ᶠ n in atTop, ∀ v : TimeIcc s t n, 1 ≤ ρ n v)
    (hpin : ∀ ε D₀ : ℝ, 0 < ε → ε < 1 → 1 < D₀ → ∀ᶠ n in atTop,
      ∀ (v : TimeIcc s t n) (ω : sz.SeqΩ),
        EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε D₀ (𝒜 n v ω) →
        f n v ω ≤ ((sz.W n : ℕ) : ℝ) ^ (C * ε) * ρ n v * ‖𝒜 n v ω‖ + ((sz.W n : ℕ) : ℝ) ^ (-D₀ + C)) :
    Prec sz (U := fun n => TimeIcc s t n) f (fun n v ω => ρ n v * X n v ω) := by
  have hsize : Tendsto sz.size atTop atTop := tendsto_size sz hSz
  obtain ⟨b, hb⟩ := hlow
  refine StochDomAt.of_highProbAt_add_rpow_neg (b := b) hsize ?_ ?_
  · refine Gauss.HighProbAt.mono hb ?_
    filter_upwards [hρ] with n hρn ω hω v
    have hXn := hω v
    have hX0 : 0 ≤ X n v ω := le_trans (Real.rpow_nonneg (Nat.cast_nonneg _) _) hXn
    calc ((sz.size n : ℕ) : ℝ) ^ (-b) ≤ X n v ω := hXn
      _ = 1 * X n v ω := by ring
      _ ≤ _ := by gcongr; exact hρn v
  · intro τ hτ D hD
    have hε0 : 0 < min (1 / 2 : ℝ) (τ * d / (4 * C)) := lt_min (by norm_num) (by positivity)
    obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (1 / 2 : ℝ) (τ * d / (4 * C)) := ⟨_, rfl⟩
    rw [← hεdef] at hε0
    have hε1 : ε < 1 := by rw [hεdef]; exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have hεle : ε ≤ τ * d / (4 * C) := by rw [hεdef]; exact min_le_right _ _
    have hCε : C * ε / d ≤ τ / 4 := by
      rw [div_le_iff₀ (by exact_mod_cast hd0)]
      calc C * ε ≤ C * (τ * d / (4 * C)) := by gcongr
        _ = τ / 4 * d := by field_simp
    have hD₀ : 1 < C + 1 + D / 𝔠 := by
      have : 0 < D / 𝔠 := by positivity
      linarith
    have hE1 := hdec ε (C + 1 + D / 𝔠) hε0 (by linarith)
    have hE2 := Prec.whp sz hdom (τ := τ / 4) (by positivity)
    refine Gauss.HighProbAt.mono (Gauss.HighProbAt.inter hsize hE1 hE2) ?_
    have hf1 : ∀ᶠ n in atTop, (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) :=
      Eventually.of_forall fun n => by exact_mod_cast sz.one_le_size n
    filter_upwards [hf1, hBw, hpin ε (C + 1 + D / 𝔠) hε0 hε1 hD₀, hρ] with n h1 h2 hpn hρn
    intro ω hω v
    obtain ⟨hω1, hω2⟩ := hω
    have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have hpv := hpn v ω (hω1 v)
    have ha : ((sz.W n : ℕ) : ℝ) ^ (C * ε) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 4) :=
      (sz.W_rpow_le hd0 n (by positivity)).trans (Real.rpow_le_rpow_of_exponent_le h1 hCε)
    have hy := hω2 v
    have hw : ((sz.W n : ℕ) : ℝ) ^ (-(C + 1 + D / 𝔠) + C) ≤ ((sz.size n : ℕ) : ℝ) ^ (-D) := by
      have e1 : -(C + 1 + D / 𝔠) + C = -(1 + D / 𝔠) := by ring
      rw [e1]
      have hneg : -(1 + D / 𝔠) ≤ 0 := by
        have : 0 < D / 𝔠 := by positivity
        linarith
      calc ((sz.W n : ℕ) : ℝ) ^ (-(1 + D / 𝔠)) ≤ (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (-(1 + D / 𝔠)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) h2 hneg
        _ = ((sz.size n : ℕ) : ℝ) ^ (𝔠 * (-(1 + D / 𝔠))) := by rw [← Real.rpow_mul hNpos.le]
        _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D) := by
            refine Real.rpow_le_rpow_of_exponent_le h1 ?_
            have : 𝔠 * (-(1 + D / 𝔠)) = -𝔠 - D := by field_simp; ring
            rw [this]; linarith
    have hNq : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) ^ (τ / 4) := Real.rpow_pos_of_pos hNpos _
    have hX0 : 0 ≤ X n v ω := by
      by_contra hneg
      push Not at hneg
      have := mul_neg_of_pos_of_neg hNq hneg
      linarith [norm_nonneg (𝒜 n v ω)]
    have hr0 : 0 ≤ ρ n v := le_trans zero_le_one (hρn v)
    have hq : ((sz.size n : ℕ) : ℝ) ^ (τ / 4) * ((sz.size n : ℕ) : ℝ) ^ (τ / 4) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by
      rw [← Real.rpow_add hNpos]
      exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    calc f n v ω
        ≤ ((sz.W n : ℕ) : ℝ) ^ (C * ε) * ρ n v * ‖𝒜 n v ω‖ +
          ((sz.W n : ℕ) : ℝ) ^ (-(C + 1 + D / 𝔠) + C) := hpv
      _ ≤ (((sz.size n : ℕ) : ℝ) ^ (τ / 4) * ρ n v) * (((sz.size n : ℕ) : ℝ) ^ (τ / 4) * X n v ω) +
            ((sz.size n : ℕ) : ℝ) ^ (-D) :=
          add_le_add (mul_le_mul (mul_le_mul_of_nonneg_right ha hr0) hy (norm_nonneg _)
            (mul_nonneg hNq.le hr0)) hw
      _ = (((sz.size n : ℕ) : ℝ) ^ (τ / 4) * ((sz.size n : ℕ) : ℝ) ^ (τ / 4)) * (ρ n v * X n v ω) +
            ((sz.size n : ℕ) : ℝ) ^ (-D) := by ring
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (ρ n v * X n v ω) + ((sz.size n : ℕ) : ℝ) ^ (-D) :=
          add_le_add (mul_le_mul_of_nonneg_right hq (mul_nonneg hr0 hX0)) le_rfl

/-! ## 3. The five consumer forms -/

theorem stek_sumNdecay_holds (d : ℕ) : STEKSumNdecay d := by
  intro hd n_ hn 𝔠 𝔡 sz hAdm s t hs hst ht m hm σ 𝒜 X hX hdom
  have hsize : Tendsto sz.size atTop atTop := tendsto_size sz hAdm.2.2.1
  have hlam : ∀ᶠ n in atTop, 0 < sz.lam n := by
    filter_upwards [hAdm.2.2.2.2] with n hn'
    exact lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _) hn'.1
  have hr : ∀ n (v : TimeIcc s t n), 0 ≤ (1 - (v : ℝ)) / (1 - t n) := fun n v =>
    div_nonneg (by linarith [(v.2).2, ht n, hst n]) (by linarith [ht n])
  have h1 : Prec sz (U := fun n => TimeIcc s t n)
      (fun n v ω => ((1 - (v : ℝ)) / (1 - t n)) ^ n_ * ‖𝒜 n v ω‖)
      (fun n v ω => ((1 - (v : ℝ)) / (1 - t n)) ^ n_ * X n v ω) :=
    StochDomAt.mul (ξ₁ := fun n (v : TimeIcc s t n) (_ : sz.SeqΩ) => ((1 - (v : ℝ)) / (1 - t n)) ^ n_)
      (ξ₂ := fun n v ω => ‖𝒜 n v ω‖) (ζ₁ := fun n (v : TimeIcc s t n) (_ : sz.SeqΩ) => ((1 - (v : ℝ)) / (1 - t n)) ^ n_)
      (ζ₂ := X) hsize (fun _ _ _ => norm_nonneg _) (fun n v _ => pow_nonneg (hr n v) _)
      (StochDomAt.refl hsize (fun n v _ => pow_nonneg (hr n v) _)) hdom
  refine StochDomAt.of_subset h1 fun τ hτ => ⟨τ, hτ, ?_⟩
  filter_upwards [hlam] with n hn' ω hω
  obtain ⟨v, hv⟩ := hω
  refine ⟨v, lt_of_lt_of_le hv ?_⟩
  have hk := ekSumNdecay_holds d n_ hd hn (sz.L n) (sz.three_le_L n) (sz.lam n) hn' (m n) (hm n) σ
    (v : ℝ) (t n) (hs n |>.trans (v.2).1) (v.2).2 (ht n) (𝒜 n v ω)
  exact hk

/-- **`(sum_res_2_NAL)` at scale `N` from the merged `ekSumDecayNAL_holds`** (EK-3): the shape with `W^{Cε}`,
`W^{-D+C}`, `4 ≤ W^ε`, the window `W⁻¹ ≤ (1-t)/(1-s)` and the high-probability decay hypothesis.  Choices:
`ε = min(1/2, τ d/(4C))` (so `W^{Cε} ≤ N^{τ/4}`, `W ≤ N^{1/d}`), `D₀ = C + 1 + D/𝔠` (`W^{-D₀+C} ≤ N^{-D}`,
`W ≥ N^𝔠`), then `StochDomAt.of_highProbAt_add_rpow_neg`. -/
theorem stek_sumRes2NAL_holds (d : ℕ) : STEKSumRes2NAL d := by
  intro hd n_ hn κ 𝔠 𝔡 hκ sz hAdm s t hwin m hm hκm σ hσ 𝒜 hdec X hlow hdom
  obtain ⟨h𝔠, h𝔡, hSz, hBw, hWO⟩ := hAdm
  obtain ⟨hs, hst, ht, ht1, hW⟩ := hwin
  have hsize : Tendsto sz.size atTop atTop := tendsto_size sz hSz
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  obtain ⟨C, hC, hpin⟩ := ekSumDecayNAL_holds d n_ 𝔡⁻¹ κ (prop5Decay_holds d 𝔡⁻¹)
    (prop5Short_holds d 𝔡⁻¹ κ) hd hn hΛ hκ
  obtain ⟨b, hb⟩ := hlow
  have hd0 : 0 < d := by omega
  have hr1 : ∀ n (v : TimeIcc s t n),
      1 ≤ (sz.lam n ^ 2 + |1 - (v : ℝ)|) / (sz.lam n ^ 2 + |1 - t n|) := by
    intro n v
    have hv1 : (v : ℝ) ≤ t n := (v.2).2
    have h1 : 0 < 1 - t n := by linarith [ht1 n]
    have h0 : 0 < sz.lam n ^ 2 + |1 - t n| := by
      have : 0 < |1 - t n| := abs_pos.2 h1.ne'
      positivity
    rw [one_le_div h0]
    have : |1 - t n| ≤ |1 - (v : ℝ)| := by
      rw [abs_of_pos h1, abs_of_pos (by linarith : 0 < 1 - (v : ℝ))]; linarith
    linarith
  refine StochDomAt.of_highProbAt_add_rpow_neg (b := b) hsize ?_ ?_
  · refine Gauss.HighProbAt.mono hb (Eventually.of_forall fun n ω hω v => ?_)
    have hXn := hω v
    have hX0 : 0 ≤ X n v ω := le_trans (Real.rpow_nonneg (Nat.cast_nonneg _) _) hXn
    calc ((sz.size n : ℕ) : ℝ) ^ (-b) ≤ X n v ω := hXn
      _ = 1 * X n v ω := by ring
      _ ≤ _ := by gcongr; exact one_le_pow₀ (hr1 n v)
  · intro τ hτ D hD
    have hε0 : 0 < min (1 / 2 : ℝ) (τ * d / (4 * C)) := lt_min (by norm_num) (by positivity)
    obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (1 / 2 : ℝ) (τ * d / (4 * C)) := ⟨_, rfl⟩
    rw [← hεdef] at hε0
    have hε1 : ε < 1 := by rw [hεdef]; exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have hεle : ε ≤ τ * d / (4 * C) := by rw [hεdef]; exact min_le_right _ _
    have hCε : C * ε / d ≤ τ / 4 := by
      rw [div_le_iff₀ (by exact_mod_cast hd0)]
      calc C * ε ≤ C * (τ * d / (4 * C)) := by gcongr
        _ = τ / 4 * d := by field_simp
    have hD₀ : 1 < C + 1 + D / 𝔠 := by
      have : 0 < D / 𝔠 := by positivity
      linarith
    have hE1 := hdec ε (C + 1 + D / 𝔠) hε0 (by linarith)
    have hE2 := Prec.whp sz hdom (τ := τ / 4) (by positivity)
    refine Gauss.HighProbAt.mono (Gauss.HighProbAt.inter hsize hE1 hE2) ?_
    have hf1 : ∀ᶠ n in atTop, (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) :=
      Eventually.of_forall fun n => by exact_mod_cast sz.one_le_size n
    have hf4 : ∀ᶠ n in atTop, (4 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε) :=
      ((tendsto_rpow_atTop (mul_pos h𝔠 hε0)).comp hSz).eventually (eventually_ge_atTop 4)
    filter_upwards [hf1, hBw, hWO, hf4, hW] with n h1 h2 h3 h4 hWn
    intro ω hω v
    obtain ⟨hω1, hω2⟩ := hω
    have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have hW4 : (4 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ ε := by
      refine le_trans h4 ?_
      rw [Real.rpow_mul hNpos.le]
      exact Real.rpow_le_rpow (by positivity) h2 hε0.le
    have hW1 : (1 : ℝ) < ((sz.W n : ℕ) : ℝ) := by
      by_contra hcon
      push Not at hcon
      have := Real.rpow_le_one hWpos.le hcon hε0.le
      linarith
    have hg0 : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos _) h3.1
    have hWv : ((sz.W n : ℕ) : ℝ)⁻¹ ≤ (1 - t n) / (1 - (v : ℝ)) :=
      hWn.trans (div_le_div_of_nonneg_left (by linarith [ht1 n])
        (by linarith [(v.2).2, ht1 n] : 0 < 1 - (v : ℝ)) (by linarith [(v.2).1] : 1 - (v : ℝ) ≤ 1 - s n))
    have hpv := hpin (sz.L n) (sz.three_le_L n) (sz.lam n) hg0 h3.2 ((sz.W n : ℕ) : ℝ) ε (C + 1 + D / 𝔠)
      hW1 hε0 hε1 hD₀ hW4 (v : ℝ) (t n) ((hs n).trans (v.2).1) (v.2).2 (ht n) hWv (m n) (hm n) (hκm n) σ hσ
      (𝒜 n v ω) (hω1 v)
    have ha : ((sz.W n : ℕ) : ℝ) ^ (C * ε) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 4) :=
      (sz.W_rpow_le hd0 n (by positivity)).trans (Real.rpow_le_rpow_of_exponent_le h1 hCε)
    have hy := hω2 v
    have hw : ((sz.W n : ℕ) : ℝ) ^ (-(C + 1 + D / 𝔠) + C) ≤ ((sz.size n : ℕ) : ℝ) ^ (-D) := by
      have e1 : -(C + 1 + D / 𝔠) + C = -(1 + D / 𝔠) := by ring
      rw [e1]
      have hneg : -(1 + D / 𝔠) ≤ 0 := by
        have : 0 < D / 𝔠 := by positivity
        linarith
      calc ((sz.W n : ℕ) : ℝ) ^ (-(1 + D / 𝔠)) ≤ (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (-(1 + D / 𝔠)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) h2 hneg
        _ = ((sz.size n : ℕ) : ℝ) ^ (𝔠 * (-(1 + D / 𝔠))) := by rw [← Real.rpow_mul hNpos.le]
        _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D) := by
            refine Real.rpow_le_rpow_of_exponent_le h1 ?_
            have : 𝔠 * (-(1 + D / 𝔠)) = -𝔠 - D := by field_simp; ring
            rw [this]; linarith
    have hNq : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) ^ (τ / 4) := Real.rpow_pos_of_pos hNpos _
    have hX0 : 0 ≤ X n v ω := by
      by_contra hneg
      push Not at hneg
      have := mul_neg_of_pos_of_neg hNq hneg
      linarith [norm_nonneg (𝒜 n v ω)]
    have hr0 : 0 ≤ ((sz.lam n ^ 2 + |1 - (v : ℝ)|) / (sz.lam n ^ 2 + |1 - t n|)) ^ (n_ - 1) :=
      pow_nonneg (le_trans zero_le_one (hr1 n v)) _
    have hq : ((sz.size n : ℕ) : ℝ) ^ (τ / 4) * ((sz.size n : ℕ) : ℝ) ^ (τ / 4) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by
      rw [← Real.rpow_add hNpos]
      exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    calc ‖UN d (sz.L n) (sz.lam n) (EKsgn (m n) σ) (v : ℝ) (t n) (𝒜 n v ω)‖
        ≤ ((sz.W n : ℕ) : ℝ) ^ (C * ε) *
            ((sz.lam n ^ 2 + |1 - (v : ℝ)|) / (sz.lam n ^ 2 + |1 - t n|)) ^ (n_ - 1) * ‖𝒜 n v ω‖ +
          ((sz.W n : ℕ) : ℝ) ^ (-(C + 1 + D / 𝔠) + C) := hpv
      _ ≤ (((sz.size n : ℕ) : ℝ) ^ (τ / 4) *
            ((sz.lam n ^ 2 + |1 - (v : ℝ)|) / (sz.lam n ^ 2 + |1 - t n|)) ^ (n_ - 1)) *
            (((sz.size n : ℕ) : ℝ) ^ (τ / 4) * X n v ω) + ((sz.size n : ℕ) : ℝ) ^ (-D) :=
          add_le_add (mul_le_mul (mul_le_mul_of_nonneg_right ha hr0) hy (norm_nonneg _)
            (mul_nonneg hNq.le hr0)) hw
      _ = (((sz.size n : ℕ) : ℝ) ^ (τ / 4) * ((sz.size n : ℕ) : ℝ) ^ (τ / 4)) *
            (((sz.lam n ^ 2 + |1 - (v : ℝ)|) / (sz.lam n ^ 2 + |1 - t n|)) ^ (n_ - 1) * X n v ω) +
          ((sz.size n : ℕ) : ℝ) ^ (-D) := by ring
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
            (((sz.lam n ^ 2 + |1 - (v : ℝ)|) / (sz.lam n ^ 2 + |1 - t n|)) ^ (n_ - 1) * X n v ω) +
          ((sz.size n : ℕ) : ℝ) ^ (-D) :=
          add_le_add (mul_le_mul_of_nonneg_right hq (mul_nonneg hr0 hX0)) le_rfl

/-- **`(sum_res_1)` at scale `N`** from the merged `ekSumDecay1_holds` (EK-2): the ratio factor is
`ρ = (ℓ_t²/ℓ_v²)·ratio^n ≥ 1` (`ℓ` is monotone in time). -/
theorem stek_sumRes1_holds (d : ℕ) : STEKSumRes1 d := by
  intro hd n_ hn 𝔠 𝔡 sz hAdm s t hwin m hm σ 𝒜 hdec X hlow hdom
  obtain ⟨h𝔠, h𝔡, hSz, hBw, hWO⟩ := hAdm
  obtain ⟨hs, hst, ht, ht1, hW⟩ := hwin
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  have hd0 : 0 < d := by omega
  obtain ⟨C, hC, hpin⟩ := ekSumDecay1_holds d n_ 𝔡⁻¹ (prop5Decay_holds d 𝔡⁻¹) hd hn hΛ
  have hg := prec_lam_bounds sz hWO
  refine prec_core sz hd0 h𝔠 hSz hBw 𝒜 hdec X hlow hdom
    (fun n v ω => ‖UN d (sz.L n) (sz.lam n) (EKsgn (m n) σ) (v : ℝ) (t n) (𝒜 n v ω)‖)
    (fun n v => (ellT (sz.L n) (sz.lam n) (t n) ^ 2 / ellT (sz.L n) (sz.lam n) (v : ℝ) ^ 2) *
      ((sz.lam n ^ 2 + |1 - (v : ℝ)|) / (sz.lam n ^ 2 + |1 - t n|)) ^ n_) hC ?_ ?_
  · filter_upwards [hg] with n hgn v
    have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
      have := sz.three_le_L n
      exact_mod_cast (by omega : 1 ≤ sz.L n)
    have h1 : 1 ≤ ellT (sz.L n) (sz.lam n) (t n) ^ 2 / ellT (sz.L n) (sz.lam n) (v : ℝ) ^ 2 := by
      rw [one_le_div (pow_pos (ellT_pos hL1) 2)]
      exact pow_le_pow_left₀ (ellT_pos hL1).le (ellT_mono hgn.1.le (v.2).2 (ht1 n)) 2
    exact one_le_mul_of_one_le_of_one_le h1 (one_le_pow₀ (prec_ratio_ge_one (v.2).2 (ht1 n)))
  · intro ε D₀ hε0 hε1 hD₀
    filter_upwards [prec_W_rpow_ge sz h𝔠 hSz hBw hε0 4, hg, hW] with n h4 hgn hWn v ω hdecay
    have hWpos : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hW1 := prec_one_lt_W hWpos hε0 h4
    have hpv := hpin (sz.L n) (sz.three_le_L n) (sz.lam n) hgn.1 hgn.2 ((sz.W n : ℕ) : ℝ) ε D₀
      hW1 hε0 hε1 hD₀ h4 (v : ℝ) (t n) ((hs n).trans (v.2).1) (v.2).2 (ht n)
      (prec_window (v.2).1 (v.2).2 (ht1 n) hWn) (m n) (hm n) σ
      (𝒜 n v ω) hdecay
    refine hpv.trans (le_of_eq ?_)
    ring

/-- **`(sum_res_2)` at scale `N`** from the merged `ekSumDecay2_holds` (EK-4), `K = 1/𝔠`: `L^d ≤ W^K` from
`W ≥ N^𝔠` and `log L ≤ W^ε` from it (eventually, `W → ∞`). -/
theorem stek_sumRes2_holds (d : ℕ) : STEKSumRes2 d := by
  intro hd n_ hn κ 𝔠 𝔡 hκ sz hAdm s t hwin m hm hκm σ 𝒜 hdec hzero X hlow hdom
  obtain ⟨h𝔠, h𝔡, hSz, hBw, hWO⟩ := hAdm
  obtain ⟨hs, hst, ht, ht1, hW⟩ := hwin
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  have hd0 : 0 < d := by omega
  have hK : 0 < 1 / 𝔠 := one_div_pos.2 h𝔠
  obtain ⟨C, hC, hpin⟩ := ekSumDecay2_holds d n_ 𝔡⁻¹ κ (prop5Decay_holds d 𝔡⁻¹)
    (prop5Short_holds d 𝔡⁻¹ κ) (prop6Diff1_holds d 𝔡⁻¹ κ (1 / 2)) hd hn hΛ hκ (1 / 𝔠) hK
  have hg := prec_lam_bounds sz hWO
  refine prec_core sz hd0 h𝔠 hSz hBw 𝒜 hdec X hlow hdom
    (fun n v ω => ‖UN d (sz.L n) (sz.lam n) (EKsgn (m n) σ) (v : ℝ) (t n) (𝒜 n v ω)‖)
    (fun n v => ((sz.lam n ^ 2 + |1 - (v : ℝ)|) / (sz.lam n ^ 2 + |1 - t n|)) ^ n_) hC ?_ ?_
  · exact Eventually.of_forall fun n v =>
      one_le_pow₀ (prec_ratio_ge_one (v.2).2 (ht1 n))
  · intro ε D₀ hε0 hε1 hD₀
    filter_upwards [prec_W_rpow_ge sz h𝔠 hSz hBw hε0 4,
      prec_W_rpow_ge sz h𝔠 hSz hBw (half_pos hε0) (2 * (1 / 𝔠) / (ε * d)), hg, hW, hBw]
      with n h4 hM hgn hWn hb v ω hdecay
    have hWpos : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hW1 := prec_one_lt_W hWpos hε0 h4
    have hLK := prec_L_pow_le sz h𝔠 n hb
    have hlog : Real.log ((sz.L n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ ε :=
      prec_log_le hd0 (Nat.cast_nonneg _) hK hε0 (by linarith) hLK hM
    exact (hpin (sz.L n) (sz.three_le_L n) (sz.lam n) hgn.1 hgn.2 ((sz.W n : ℕ) : ℝ) ε D₀
      hW1 hε0 hε1 hD₀ h4 hlog hLK (v : ℝ) (t n) ((hs n).trans (v.2).1) (v.2).2 (ht n)
      (prec_window (v.2).1 (v.2).2 (ht1 n) hWn) (m n) (hm n) (hκm n)
      σ (𝒜 n v ω) hdecay (hzero n v ω)).trans (le_of_eq (by ring))

/-- **`lem:sum_decay_nonzero` at scale `N`** from the merged `ekSumDecayNonzero_holds` (EK-5), `0 ≤ s`
(DECISIONS §27): the constant `C` of the pin is absorbed by `StochDomAt.const_mul_left`. -/
theorem stek_nonzero_holds (d : ℕ) : STEKNonzero d := by
  intro hd n_ hn κ 𝔠 𝔡 hκ sz hAdm s t hsg hs hst ht m hm hκm σ A hA 𝒜 X hX hdom
  obtain ⟨h𝔠, h𝔡, hSz, hBw, hWO⟩ := hAdm
  have hsize : Tendsto sz.size atTop atTop := tendsto_size sz hSz
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  obtain ⟨C, hC, hpin⟩ := ekSumDecayNonzero_holds d n_ 𝔡⁻¹ κ (prop5Short_holds d 𝔡⁻¹ κ)
    (prop8ZeroMode_holds d 𝔡⁻¹ κ) hd hn hΛ hκ
  have hg := prec_lam_bounds sz hWO
  have h1 : Prec sz (U := fun n => TimeIcc s t n) (fun n v ω => C * ‖𝒜 n v ω‖) X :=
    StochDomAt.const_mul_left hsize hC.le hX hdom
  refine StochDomAt.of_subset h1 fun τ hτ => ⟨τ, hτ, ?_⟩
  filter_upwards [hg] with n hgn ω hω
  obtain ⟨v, hv⟩ := hω
  refine ⟨v, lt_of_lt_of_le hv ?_⟩
  exact hpin (sz.L n) (sz.three_le_L n) (sz.lam n) hgn.1 hgn.2 (v : ℝ) (t n)
    ((hs n).trans (v.2).1) ((hsg n).trans (v.2).1) (v.2).2 (ht n) (m n) (hm n) (hκm n) σ A hA (𝒜 n v ω)

end RBM.Gauss.Sizes

/-! ## 4. Compiled nonempty instances at `d = 3`

The two size sequences of `Step34Pins.lean` §7 (`sz0` merged: `L = 4(n+1)`, `W = (2(n+1))^5`, `ilambda = (2(n+1))^{-6}`;
`szB`: `L = 4`, `W = n + 4`, `ilambda = 1`), `n_ = 2`, `m ≡ i` (`‖m‖ = 1`, `Im m = 1 ≥ κ = 1/2`), `𝔠 = 1/6`, `𝔡 = 1/10`
(`Admissible`: `sz0_admissible`, `szB_admissible`), control `X ≡ 1`.  The tensor family is deterministic, so the
stochastic hypotheses of the five forms are discharged, not assumed:
* `δ₀` (point mass at `0`) for `(sum_res_Ndecay)`, `(sum_res_1)`, `(sum_res_2_NAL)`, `lem:sum_decay_nonzero`;
* `Az L = δ₀ ⊗ (δ₀ - δ_e)`, `e = (1,0,0)`, the sum-zero tensor of `(sum_res_2)` (`Az L (0,0) = 1`).
`(deccA0)` holds eventually for `Az` (`W^ε ℓ_v > 1` once `W^ε ≥ 4`) and for all `n` for `δ₀`; `‖𝒜‖ ≺ 1` by `prec_of_le`.
Windows: case (i) `STEKWin` at `(sz0, 0, 1/16)` and `(szB, 7/8, 15/16)`; case (ii) at `(szB, 15/16, 31/32)`
(`1 - ilambda²/L² = 15/16 ≤ s`). -/

namespace RBM.Gauss.PrecInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.Step34Inst RBM.Gauss.InductionDefsInst
  RBM.Path Filter

private theorem norm_delta0_le (n d L : ℕ) [NeZero L] : ‖ekDelta0 n d L‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => ?_
  unfold ekDelta0
  split_ifs <;> simp

private theorem prec_delta0 (sz : Sizes 3) (s t : ℕ → ℝ) :
    Prec sz (U := fun n => TimeIcc s t n) (fun n _ _ => ‖ekDelta0 2 3 (sz.L n)‖) (fun _ _ _ => (1 : ℝ)) :=
  prec_of_le sz (fun _ _ _ => zero_le_one) (fun n _ _ => norm_delta0_le 2 3 (sz.L n))

private theorem decay_delta0 (sz : Sizes 3) (s t : ℕ → ℝ) :
    STEKDecay sz s t (fun n _ _ => ekDelta0 2 3 (sz.L n)) := by
  intro ε D hε hD
  refine Gauss.HighProbAt.of_eventually_univ (Eventually.of_forall fun n ω v => ?_)
  intro a ⟨i, j, hij⟩
  by_cases ha : a = 0
  · exfalso
    subst ha
    have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
      have := sz.three_le_L n
      exact_mod_cast (by omega : 1 ≤ sz.L n)
    have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have := mul_pos (Real.rpow_pos_of_pos hW ε) (ellT_pos (g := sz.lam n) (t := (v : ℝ)) hL1)
    simp at hij
    linarith
  · simp only [ekDelta0, ha, ↓reduceIte, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _

private theorem low_one (sz : Sizes 3) (s t : ℕ → ℝ) : STEKLow sz s t (fun _ _ _ => (1 : ℝ)) :=
  ⟨0, Gauss.HighProbAt.of_eventually_univ (Eventually.of_forall fun n ω v => by simp)⟩

/-- the sum-zero tensor `δ₀ ⊗ (δ₀ - δ_e)`, `e = (1,0,0)`. -/
private noncomputable def Az (L : ℕ) : (Fin 2 → Zd 3 L) → ℂ := fun b =>
  if b 0 = 0 then (if b 1 = 0 then 1 else 0) - (if b 1 = (Pi.single 0 1 : Zd 3 L) then 1 else 0) else 0

private theorem Az_zero (L : ℕ) (hL : 3 ≤ L) : Az L ![0, 0] = 1 := by
  have hne : (0 : Zd 3 L) ≠ Pi.single 0 1 := by
    intro h
    have := congrArg (zdistD 3 L) h
    rw [zdistD_zero, zdistD_single, zdist_one hL] at this
    omega
  simp [Az, hne]

private theorem norm_Az_le (L : ℕ) [NeZero L] : ‖Az L‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => ?_
  unfold Az
  split_ifs <;> simp

private theorem prec_Az (sz : Sizes 3) (s t : ℕ → ℝ) :
    Prec sz (U := fun n => TimeIcc s t n) (fun n _ _ => ‖Az (sz.L n)‖) (fun _ _ _ => (1 : ℝ)) :=
  prec_of_le sz (fun _ _ _ => zero_le_one) (fun n _ _ => norm_Az_le (sz.L n))

private theorem Az_sumZero (L : ℕ) [NeZero L] : EKSumZero (Az L) := by
  intro i₀ hi₀ x
  have hi : i₀ = 0 := Fin.ext hi₀
  subst hi
  rw [Finset.sum_filter, ek_sum_fin_two]
  have e : ∀ x' y : Zd 3 L, (if (![x', y] : Fin 2 → Zd 3 L) 0 = x then Az L ![x', y] else 0)
      = if x' = x then (if x' = 0 then (if y = 0 then (1 : ℂ) else 0) -
          (if y = (Pi.single 0 1 : Zd 3 L) then 1 else 0) else 0) else 0 := by
    intro x' y
    simp [Az]
  simp only [e]
  by_cases hx : x = 0
  · subst hx
    simp [Finset.sum_ite_eq', Finset.sum_sub_distrib]
  · simp

private theorem Az_decay (L : ℕ) [NeZero L] (hL : 3 ≤ L) (g s W ε D : ℝ) (hW : 0 < W)
    (h : 1 < W ^ ε * ellT L g s) : EKFastDecay g s W ε D (Az L) := by
  intro a ⟨i, j, hij⟩
  by_cases hne : Az L a = 0
  · rw [hne]; simp only [norm_zero]; exact Real.rpow_nonneg hW.le _
  · exfalso
    have h0 : a 0 = 0 := by
      by_contra hc; simp [Az, hc] at hne
    have h1 : a 1 = 0 ∨ a 1 = (Pi.single 0 1 : Zd 3 L) := by
      by_contra hc
      rw [not_or] at hc
      simp [Az, h0, hc.1, hc.2] at hne
    have hE : ∀ y : Zd 3 L, y = 0 ∨ y = (Pi.single 0 1 : Zd 3 L) → zdistD 3 L y ≤ 1 := by
      rintro y (rfl | rfl)
      · simp
      · rw [zdistD_single, zdist_one hL]
    have hd : ∀ i j : Fin 2, zdistD 3 L (a i - a j) ≤ 1 := by
      refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩,
        Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
      · simp
      · rw [h0, zero_sub, zdistD_neg]; exact hE _ h1
      · rw [h0, sub_zero]; exact hE _ h1
      · simp
    have h2 : (zdistD 3 L (a i - a j) : ℝ) ≤ 1 := by exact_mod_cast hd i j
    linarith

private theorem decay_Az (sz : Sizes 3) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (hSz : sz.SizeTendsto) (hBw : sz.Bandwidth 𝔠)
    (s t : ℕ → ℝ) : STEKDecay sz s t (fun n _ _ => Az (sz.L n)) := by
  intro ε D hε hD
  refine Gauss.HighProbAt.of_eventually_univ ?_
  filter_upwards [prec_W_rpow_ge sz h𝔠 hSz hBw hε 4] with n h4 ω v
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    have := sz.three_le_L n
    exact_mod_cast (by omega : 1 ≤ sz.L n)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  refine Az_decay (sz.L n) (sz.three_le_L n) _ _ _ _ _ hW ?_
  have h1 := one_le_ellT (g := sz.lam n) (t := (v : ℝ)) hL1
  nlinarith

/-- the windows of the instance data -/
private theorem win_sz0 : STEKWin sz0 sInst tInst := by
  refine ⟨fun n => le_rfl, fun n => by simp only [sInst, tInst]; norm_num, fun n => ?_,
    fun n => by simp only [tInst]; norm_num, Eventually.of_forall fun n => ?_⟩
  · have := sz0_caseI n
    simp only [tInst] at this ⊢
    linarith
  · simp only [sInst, tInst]
    calc (((sz0.W n : ℕ) : ℝ))⁻¹ ≤ 32⁻¹ := inv_anti₀ (by norm_num) (W_ge_32 n)
      _ ≤ (1 - 1 / 16) / (1 - 0) := by norm_num

private theorem win_szB_I : STEKWin szB (fun _ => 7 / 8) (fun _ => 15 / 16) := by
  refine ⟨fun n => by norm_num, fun n => by norm_num, fun n => by norm_num [szB],
    fun n => by norm_num, Eventually.of_forall fun n => ?_⟩
  have h4 : (4 : ℝ) ≤ ((szB.W n : ℕ) : ℝ) := by
    change (4 : ℝ) ≤ ((n + 4 : ℕ) : ℝ)
    exact_mod_cast Nat.le_add_left 4 n
  calc (((szB.W n : ℕ) : ℝ))⁻¹ ≤ 4⁻¹ := inv_anti₀ (by norm_num) h4
    _ ≤ (1 - 15 / 16) / (1 - 7 / 8) := by norm_num

private theorem I_im : (1 / 2 : ℝ) ≤ Complex.I.im := by rw [Complex.I_im]; norm_num

/-! ### `lem:sum_Ndecay`: the three windows (no `STEKWin`, only `0 ≤ s ≤ t < 1`) -/

example := stek_sumNdecay_holds 3 le_rfl 2 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible sInst tInst
  (fun _ => le_rfl) (fun n => by simp only [sInst, tInst]; norm_num) (fun n => by simp only [tInst]; norm_num)
  (fun _ => Complex.I) (fun _ => Complex.norm_I) ![true, false]
  (fun n _ _ => ekDelta0 2 3 (sz0.L n)) (fun _ _ _ => (1 : ℝ)) (fun _ _ _ => zero_le_one)
  (prec_delta0 sz0 sInst tInst)

example := stek_sumNdecay_holds 3 le_rfl 2 le_rfl (1 / 6) (1 / 10) szB szB_admissible
  (fun _ => 7 / 8) (fun _ => 15 / 16) (fun n => by norm_num) (fun n => by norm_num) (fun n => by norm_num)
  (fun _ => Complex.I) (fun _ => Complex.norm_I) ![true, false]
  (fun n _ _ => ekDelta0 2 3 (szB.L n)) (fun _ _ _ => (1 : ℝ)) (fun _ _ _ => zero_le_one)
  (prec_delta0 szB (fun _ => 7 / 8) (fun _ => 15 / 16))

example := stek_sumNdecay_holds 3 le_rfl 2 le_rfl (1 / 6) (1 / 10) szB szB_admissible
  (fun _ => 15 / 16) (fun _ => 31 / 32) (fun n => by norm_num) (fun n => by norm_num) (fun n => by norm_num)
  (fun _ => Complex.I) (fun _ => Complex.norm_I) ![true, false]
  (fun n _ _ => ekDelta0 2 3 (szB.L n)) (fun _ _ _ => (1 : ℝ)) (fun _ _ _ => zero_le_one)
  (prec_delta0 szB (fun _ => 15 / 16) (fun _ => 31 / 32))

/-! ### `(sum_res_1)`: case (i) at `(sz0, 0, 1/16)` and `(szB, 7/8, 15/16)` -/

example := stek_sumRes1_holds 3 le_rfl 2 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible sInst tInst win_sz0
  (fun _ => Complex.I) (fun _ => Complex.norm_I) ![true, false]
  (fun n _ _ => ekDelta0 2 3 (sz0.L n)) (decay_delta0 sz0 sInst tInst)
  (fun _ _ _ => (1 : ℝ)) (low_one sz0 sInst tInst) (prec_delta0 sz0 sInst tInst)

example := stek_sumRes1_holds 3 le_rfl 2 le_rfl (1 / 6) (1 / 10) szB szB_admissible
  (fun _ => 7 / 8) (fun _ => 15 / 16) win_szB_I
  (fun _ => Complex.I) (fun _ => Complex.norm_I) ![true, false]
  (fun n _ _ => ekDelta0 2 3 (szB.L n)) (decay_delta0 szB _ _)
  (fun _ _ _ => (1 : ℝ)) (low_one szB _ _) (prec_delta0 szB _ _)

/-! ### `(sum_res_2_NAL)`: `σ = (+,+)` non-alternating, `κ = 1/2` -/

example := stek_sumRes2NAL_holds 3 le_rfl 2 le_rfl (1 / 2) (1 / 6) (1 / 10) (by norm_num) sz0 sz0_admissible
  sInst tInst win_sz0 (fun _ => Complex.I) (fun _ => Complex.norm_I) (fun _ => I_im)
  ![true, true] ⟨0, by decide⟩
  (fun n _ _ => ekDelta0 2 3 (sz0.L n)) (decay_delta0 sz0 sInst tInst)
  (fun _ _ _ => (1 : ℝ)) (low_one sz0 sInst tInst) (prec_delta0 sz0 sInst tInst)

example := stek_sumRes2NAL_holds 3 le_rfl 2 le_rfl (1 / 2) (1 / 6) (1 / 10) (by norm_num) szB szB_admissible
  (fun _ => 7 / 8) (fun _ => 15 / 16) win_szB_I (fun _ => Complex.I) (fun _ => Complex.norm_I) (fun _ => I_im)
  ![true, true] ⟨0, by decide⟩
  (fun n _ _ => ekDelta0 2 3 (szB.L n)) (decay_delta0 szB _ _)
  (fun _ _ _ => (1 : ℝ)) (low_one szB _ _) (prec_delta0 szB _ _)

/-! ### `(sum_res_2)`: the sum-zero tensor `Az`, `σ = (+,-)`, `κ = 1/2` -/

example := stek_sumRes2_holds 3 le_rfl 2 le_rfl (1 / 2) (1 / 6) (1 / 10) (by norm_num) sz0 sz0_admissible
  sInst tInst win_sz0 (fun _ => Complex.I) (fun _ => Complex.norm_I) (fun _ => I_im) ![true, false]
  (fun n _ _ => Az (sz0.L n)) (decay_Az sz0 (by norm_num) sz0_tendsto sz0_bandwidth sInst tInst)
  (fun n _ _ => Az_sumZero (sz0.L n))
  (fun _ _ _ => (1 : ℝ)) (low_one sz0 sInst tInst) (prec_Az sz0 sInst tInst)

example := stek_sumRes2_holds 3 le_rfl 2 le_rfl (1 / 2) (1 / 6) (1 / 10) (by norm_num) szB szB_admissible
  (fun _ => 7 / 8) (fun _ => 15 / 16) win_szB_I (fun _ => Complex.I) (fun _ => Complex.norm_I) (fun _ => I_im)
  ![true, false]
  (fun n _ _ => Az (szB.L n)) (decay_Az szB (by norm_num) szB_tendsto szB_bandwidth _ _)
  (fun n _ _ => Az_sumZero (szB.L n))
  (fun _ _ _ => (1 : ℝ)) (low_one szB _ _) (prec_Az szB _ _)

/-! ### `lem:sum_decay_nonzero`: case (ii) at `(szB, 15/16, 31/32)`, `σ = (+,-)`, `A = {0,1}` -/

example := stek_nonzero_holds 3 le_rfl 2 le_rfl (1 / 2) (1 / 6) (1 / 10) (by norm_num) szB szB_admissible
  (fun _ => 15 / 16) (fun _ => 31 / 32) (fun n => by norm_num [szB]) (fun n => by norm_num)
  (fun n => by norm_num) (fun n => by norm_num) (fun _ => Complex.I) (fun _ => Complex.norm_I)
  (fun _ => I_im) ![true, false] Finset.univ (fun i _ => Finset.mem_univ i)
  (fun n _ _ => ekDelta0 2 3 (szB.L n)) (fun _ _ _ => (1 : ℝ)) (fun _ _ _ => zero_le_one)
  (prec_delta0 szB _ _)

end RBM.Gauss.PrecInst
