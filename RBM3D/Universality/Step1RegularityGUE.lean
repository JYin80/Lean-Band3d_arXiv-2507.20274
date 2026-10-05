/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.Step1Good
import RBM3D.Universality.FreeConvStability
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# `RBM3D.Universality.Step1RegularityGUE` (UN-11): the GUE side of the Step-1 regularity event

Ticket T2220.  Port of RBM2D `Universality/Step1RegularityGUE.lean` (commit `c9a24cf`, 1221
lines; read-only) to `Sizes d`, `Ω d L W`, `CoordF d L W`, `N = (W L)^d = Nsz sz n`.

Proves, from the weak pin `UNGUELocal` (a hypothesis, owed: UN-09/UN-10) and the Gaussian
entry tail:
* S7a `guelocalEventHighProb`: the GUE local event (`Step1LocalEventGUE`) fails with
  probability `≤ N^{-D}`;
* S7b `guedetHalf`: deterministically, on that event at `0 < τ < τs/8`, the shifted GUE
  spectrum `vGUE` is `[32]`-regular and its free-convolution density at `t = 1 - e^{-t*}` is
  within `N^{-3τs/8}` of `ρ_sc(E₀)`;
* S7 `gueGoodHighProb`: the composition at `τ = τs/16`, the input of UN-14 (`UNInfty1Row'`).

`d` enters only through `Idx d`, `CoordF d`, `gueVar d`; every exponent involves `τs`, `τ`
only; there is no `Admissible` and no `τs ≤ 𝔠𝔡`.  Not ported (UN-14 uses the merged
`step1Band_gue_count`): RBM2D `gue_count_exponents` `:160`, `gue_count_rate_free` `:180`,
`gue_window_rate` `:154`.  Reused from Step1Good: `stieltjesN_eq_mV`, `mV_eta_mul_im_mono`,
`mV_im_le_inv`; the `a = e^{-T/2}` elementary facts and the affine dictionary are re-proved
here under the prefix `Step1RegularityGUE_` (the originals are private).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal ENNReal

namespace RBM.Univ

/-! ## 1. Vocabulary and the three Props (check 2.1 of `docs/tickets/checks/T2220-check.lean`) -/

/-- `vGUE`: the shifted, rescaled GUE diagonal `v_i = e^{-t*/2} λ_i(X) - E₀`, `X` under `gueP`, `t* = N^{-1+τs}`
(RBM2D `vGUE`, `Step1RegularityGUE.lean:56`; the GUE analogue of `vOU`, `Pins.lean:573`). -/
def vGUE {d : ℕ} (sz : Sizes d) (n : ℕ) (τs E₀ : ℝ) (ω : Ω d (sz.L n) (sz.W n)) :
    Idx d (sz.L n) (sz.W n) → ℝ :=
  fun i => Real.exp (-(ouTStar sz τs n) / 2) * (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues i - E₀

/-- `Step1LocalEventGUE`: the averaged law at the precision of `UNGUELocal` on `|Re z| ≤ 2 - κ`,
`N^{-1+τ} ≤ Im z ≤ 10`, and every entry of `X` of modulus `≤ 1` (RBM2D `:67`). -/
def Step1LocalEventGUE {d : ℕ} (sz : Sizes d) (n : ℕ) (κ τ : ℝ) (ω : Ω d (sz.L n) (sz.W n)) : Prop :=
  (∀ z : ℂ, |z.re| ≤ 2 - κ → Nsz sz n ^ (-1 + τ) ≤ z.im → z.im ≤ 10 →
      ‖stieltjesN (Xmat d (sz.L n) (sz.W n) ω) z - msc z‖ ≤ Nsz sz n ^ τ / Real.sqrt (Nsz sz n * z.im)) ∧
    ∀ x y : Idx d (sz.L n) (sz.W n), ‖Xmat d (sz.L n) (sz.W n) ω x y‖ ≤ 1

/-- `GUEGoodAt`: the GUE-side good event (RBM2D `:78`) in the shape of the event of `UNStep1Good'`
(`PinsDens.lean:73`): `vGUE` is `[32]`-regular with `g = N^{-1+τs/4}`, `G = N^{-min(τs/4,(1-τs)/3)}`,
`c = min κ 1 / 960`, `C = 2`, `CV = 2`; a solution `mfc` of (2.5) at `t = 1 - e^{-t*}` has a density `ρ'` at `0`
within `N^{-3τs/8}` of `ρ_sc(E₀)`. -/
def GUEGoodAt {d : ℕ} (sz : Sizes d) (n : ℕ) (κ τs E₀ : ℝ) (ω : Ω d (sz.L n) (sz.W n)) : Prop :=
  IsRegular32 (vGUE sz n τs E₀ ω) (Nsz sz n ^ (-1 + τs / 4))
      (Nsz sz n ^ (-(min (τs / 4) ((1 - τs) / 3)))) (min κ 1 / 960) 2 2 ∧
    ∃ mfc : ℂ → ℂ, IsFreeConv32 (vGUE sz n τs E₀ ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧
      ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
        |ρ' - rhoSC E₀| ≤ Nsz sz n ^ (-(3 * τs / 8))

/-- `UNGUELocalEventHighProb` (S7a; proved by target 2a): from `UNGUELocal` and the Gaussian entry tail. -/
def UNGUELocalEventHighProb : Prop :=
  UNGUELocal → ∀ d : ℕ, 3 ≤ d → ∀ sz : Sizes d, Tendsto (fun n => sz.size n) atTop atTop →
    ∀ κ τ D : ℝ, 0 < κ → 0 < τ → 0 < D →
      ∀ᶠ n in atTop, gueP d (sz.L n) (sz.W n) {ω | ¬ Step1LocalEventGUE sz n κ τ ω} ≤
        ENNReal.ofReal (Nsz sz n ^ (-D))

/-- `UNGUEDetHalf` (S7b; proved by target 3): deterministic, for `0 < τ < τs/8`. -/
def UNGUEDetHalf : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ sz : Sizes d, Tendsto (fun n => sz.size n) atTop atTop →
    ∀ κ τs E₀ : ℝ, 0 < κ → 0 < τs → τs < 1 → |E₀| ≤ 2 - κ →
      ∀ τ : ℝ, 0 < τ → τ < τs / 8 →
        ∀ᶠ n in atTop, ∀ ω : Ω d (sz.L n) (sz.W n),
          Step1LocalEventGUE sz n (κ / 2) τ ω → GUEGoodAt sz n κ τs E₀ ω

/-- `UNGUEGoodHighProb` (S7; proved by target 4): the GUE-side good event has probability `≥ 1 - N^{-D}`. -/
def UNGUEGoodHighProb : Prop :=
  UNGUELocal → ∀ d : ℕ, 3 ≤ d → ∀ sz : Sizes d, Tendsto (fun n => sz.size n) atTop atTop →
    ∀ κ τs E₀ D : ℝ, 0 < κ → 0 < τs → τs < 1 → |E₀| ≤ 2 - κ → 0 < D →
      ∀ᶠ n in atTop, gueP d (sz.L n) (sz.W n) {ω | ¬ GUEGoodAt sz n κ τs E₀ ω} ≤
        ENNReal.ofReal (Nsz sz n ^ (-D))

/-! ## 2. Exponent arithmetic (RBM2D `:132-205`) -/

/-- **Target 1a** `gue_window` (RBM2D `:140`): `0 < τ < τs/8` meets the four constraints of the
deterministic half. -/
theorem gue_window :
    ∀ {τs τ : ℝ}, 0 < τ → τ < τs / 8 →
      τ ≤ τs / 4 ∧ τ - τs / 8 < 0 ∧ τ - τs / 2 < -(3 * τs / 8) ∧ τ < τs := by
  intro τs τ hτ0 hτ
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- **Target 1b** `gue_window_sharp` (RBM2D `:148`): the window is sharp. -/
theorem gue_window_sharp :
    ∀ {τs τ : ℝ}, τs / 8 ≤ τ → ¬ (τ - τs / 8 < 0) ∧ ¬ (τ - τs / 2 < -(3 * τs / 8)) := by
  intro τs τ h
  exact ⟨not_lt.2 (by linarith), not_lt.2 (by linarith)⟩

/-- **Target 1c** `gue_l32_exponents` (RBM2D `:196`): the `UNL32` exponents at
`σ = δ = min(τs/4, (1-τs)/3)`. -/
theorem gue_l32_exponents :
    ∀ {τs : ℝ}, 0 < τs → τs < 1 →
      0 < min (τs / 4) ((1 - τs) / 3) ∧
      -1 + min (τs / 4) ((1 - τs) / 3) ≤ -1 + τs / 4 ∧
      -1 + τs / 4 ≤ -(min (τs / 4) ((1 - τs) / 3)) ∧
      -1 + τs / 4 + min (τs / 4) ((1 - τs) / 3) ≤ -1 + τs / 2 ∧
      -1 + τs ≤ -(min (τs / 4) ((1 - τs) / 3)) - 2 * min (τs / 4) ((1 - τs) / 3) := by
  intro τs h0 h1
  have hm1 : min (τs / 4) ((1 - τs) / 3) ≤ τs / 4 := min_le_left _ _
  have hm2 : min (τs / 4) ((1 - τs) / 3) ≤ (1 - τs) / 3 := min_le_right _ _
  refine ⟨lt_min (by linarith) (by linarith), by linarith, by linarith, by linarith, by linarith⟩

/-! ## 3. S7a: the GUE entry tail, the union bound and `UNGUELocal` (RBM2D `:207-430`) -/

private theorem Step1RegularityGUE_card_Coord (d L W : ℕ) [NeZero L] [NeZero W] :
    (Fintype.card (CoordF d L W) : ℝ) = 2 * ((((W * L) ^ d : ℕ)) : ℝ) ^ 2 := by
  have : Fintype.card (CoordF d L W) = 2 * ((W * L) ^ d) ^ 2 := by
    change Fintype.card (Idx d L W × Idx d L W × Bool) = _
    rw [Fintype.card_prod (Idx d L W) (Idx d L W × Bool), Fintype.card_prod (Idx d L W) Bool,
      Fintype.card_bool, RBM.Gauss.card_Idx]
    ring
  rw [this]; push_cast; ring

private theorem Step1RegularityGUE_gueVar_le (d L W : ℕ) [NeZero L] [NeZero W] (c : CoordF d L W) :
    (gueVar d L W c : ℝ) ≤ ((((W * L) ^ d : ℕ) : ℝ))⁻¹ := by
  unfold gueVar
  split_ifs
  · simp
  · have hpos : (0 : ℝ) ≤ ((((W * L) ^ d : ℕ) : ℝ))⁻¹ := by positivity
    push_cast at hpos ⊢
    rw [mul_inv]
    nlinarith [hpos]

/-- If every real coordinate is at most `1/2` in absolute value, every entry has modulus `≤ 1`. -/
private theorem Step1RegularityGUE_Xentry_le (d L W : ℕ) [NeZero L] [NeZero W] (s : Ω d L W)
    (hs : ∀ c, |s c| ≤ 1 / 2) (i j : Idx d L W) : ‖Xentry d L W s i j‖ ≤ 1 := by
  have hn : ∀ a b : ℝ, |a| ≤ 1 / 2 → |b| ≤ 1 / 2 → ‖(a : ℂ) + Complex.I * (b : ℂ)‖ ≤ 1 := by
    intro a b ha hb
    calc ‖(a : ℂ) + Complex.I * (b : ℂ)‖ ≤ ‖(a : ℂ)‖ + ‖Complex.I * (b : ℂ)‖ := norm_add_le _ _
      _ = |a| + |b| := by simp
      _ ≤ 1 := by linarith
  have hn' : ∀ a b : ℝ, |a| ≤ 1 / 2 → |b| ≤ 1 / 2 → ‖(a : ℂ) - Complex.I * (b : ℂ)‖ ≤ 1 := by
    intro a b ha hb
    calc ‖(a : ℂ) - Complex.I * (b : ℂ)‖ ≤ ‖(a : ℂ)‖ + ‖Complex.I * (b : ℂ)‖ := norm_sub_le _ _
      _ = |a| + |b| := by simp
      _ ≤ 1 := by linarith
  unfold Xentry
  split_ifs
  · exact hn _ _ (hs _) (hs _)
  · exact hn' _ _ (hs _) (hs _)
  · have := hs (i, j, true)
    simp only [Complex.norm_real, Real.norm_eq_abs]
    linarith

/-- Each real coordinate of the GUE is sub-Gaussian with variance proxy `1/N` (`gueVar ≤ 1/N`, `N = (W L)^d`). -/
private theorem Step1RegularityGUE_subgaussian (d L W : ℕ) [NeZero L] [NeZero W] (c : CoordF d L W) :
    HasSubgaussianMGF (fun ω : Ω d L W => ω c)
      (⟨((((W * L) ^ d : ℕ) : ℝ))⁻¹, by positivity⟩ : ℝ≥0) (gueP d L W) := by
  set v : ℝ≥0 := ⟨((((W * L) ^ d : ℕ) : ℝ))⁻¹, by positivity⟩ with hv
  have hmap : (gueP d L W).map (fun ω : Ω d L W => ω c) = gaussianReal 0 (gueVar d L W c) := by
    unfold gueP; exact Measure.infinitePi_map_eval _ c
  have hX : AEMeasurable (fun ω : Ω d L W => ω c) (gueP d L W) :=
    (measurable_pi_apply _).aemeasurable
  rw [← HasSubgaussianMGF.id_map_iff hX, hmap]
  refine ⟨fun t => integrable_exp_mul_gaussianReal t, fun t => ?_⟩
  rw [mgf_id_gaussianReal]
  simp only [zero_mul, zero_add]
  apply Real.exp_le_exp.2
  have h := Step1RegularityGUE_gueVar_le d L W c
  have : (gueVar d L W c : ℝ) ≤ (v : ℝ) := h
  nlinarith [sq_nonneg t]

/-- Chernoff bound for one coordinate: `P(|g| ≥ 1/2) ≤ 2 exp(-N/8)`. -/
private theorem Step1RegularityGUE_coord_tail (d L W : ℕ) [NeZero L] [NeZero W] (c : CoordF d L W) :
    (gueP d L W).real ({ω | 1 / 2 ≤ ω c} ∪ {ω | 1 / 2 ≤ -(ω c)}) ≤
      2 * Real.exp (-((((W * L) ^ d : ℕ) : ℝ) / 8)) := by
  have hsg := Step1RegularityGUE_subgaussian d L W c
  have h1 : (gueP d L W).real {ω | 1 / 2 ≤ ω c} ≤
      Real.exp (-(1 / 2 : ℝ) ^ 2 / (2 * ((((W * L) ^ d : ℕ) : ℝ))⁻¹)) :=
    hsg.measure_ge_le (ε := 1 / 2) (by norm_num)
  have h2 : (gueP d L W).real {ω | 1 / 2 ≤ -(ω c)} ≤
      Real.exp (-(1 / 2 : ℝ) ^ 2 / (2 * ((((W * L) ^ d : ℕ) : ℝ))⁻¹)) :=
    hsg.neg.measure_ge_le (ε := 1 / 2) (by norm_num)
  have hN : (0 : ℝ) < ((W * L) ^ d : ℕ) := by
    have h1 : 0 < W := Nat.pos_of_ne_zero (NeZero.ne W)
    have h2 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hexp : Real.exp (-(1 / 2 : ℝ) ^ 2 / (2 * ((((W * L) ^ d : ℕ) : ℝ))⁻¹)) =
      Real.exp (-((((W * L) ^ d : ℕ) : ℝ) / 8)) := by
    congr 1
    field_simp
    ring
  rw [hexp] at h1 h2
  calc (gueP d L W).real ({ω | 1 / 2 ≤ ω c} ∪ {ω | 1 / 2 ≤ -(ω c)})
      ≤ (gueP d L W).real {ω | 1 / 2 ≤ ω c} + (gueP d L W).real {ω | 1 / 2 ≤ -(ω c)} :=
        measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-((((W * L) ^ d : ℕ) : ℝ) / 8)) := by linarith

/-- The union bound over the `2 N²` real coordinates: some entry exceeds `1` with probability at
most `4 N² exp(-N/8)`. -/
private theorem Step1RegularityGUE_entry_bound (d L W : ℕ) [NeZero L] [NeZero W] :
    gueP d L W {ω | ¬ ∀ x y : Idx d L W, ‖Xmat d L W ω x y‖ ≤ 1} ≤
      ENNReal.ofReal (4 * ((((W * L) ^ d : ℕ)) : ℝ) ^ 2 *
        Real.exp (-((((W * L) ^ d : ℕ) : ℝ) / 8))) := by
  classical
  have hsub : {ω : Ω d L W | ¬ ∀ x y : Idx d L W, ‖Xmat d L W ω x y‖ ≤ 1} ⊆
      ⋃ c : CoordF d L W, ({ω : Ω d L W | 1 / 2 ≤ ω c} ∪ {ω : Ω d L W | 1 / 2 ≤ -(ω c)}) := by
    intro ω hω
    by_contra hcon
    apply hω
    intro x y
    have hs : ∀ c, |ω c| ≤ 1 / 2 := by
      intro c
      by_contra hc
      push Not at hc
      apply hcon
      refine Set.mem_iUnion.2 ⟨c, ?_⟩
      rcases lt_abs.1 hc with h | h
      · exact Or.inl h.le
      · exact Or.inr h.le
    exact Step1RegularityGUE_Xentry_le d L W ω hs x y
  have hterm : ∀ c : CoordF d L W,
      gueP d L W ({ω : Ω d L W | 1 / 2 ≤ ω c} ∪ {ω : Ω d L W | 1 / 2 ≤ -(ω c)}) ≤
        ENNReal.ofReal (2 * Real.exp (-((((W * L) ^ d : ℕ) : ℝ) / 8))) := by
    intro c
    refine (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).2 ?_
    exact Step1RegularityGUE_coord_tail d L W c
  calc gueP d L W {ω | ¬ ∀ x y : Idx d L W, ‖Xmat d L W ω x y‖ ≤ 1}
      ≤ gueP d L W (⋃ c : CoordF d L W,
        ({ω : Ω d L W | 1 / 2 ≤ ω c} ∪ {ω : Ω d L W | 1 / 2 ≤ -(ω c)})) := measure_mono hsub
    _ ≤ ∑ c : CoordF d L W,
        gueP d L W ({ω : Ω d L W | 1 / 2 ≤ ω c} ∪ {ω : Ω d L W | 1 / 2 ≤ -(ω c)}) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _c : CoordF d L W, ENNReal.ofReal (2 * Real.exp (-((((W * L) ^ d : ℕ) : ℝ) / 8))) :=
        Finset.sum_le_sum fun c _ => hterm c
    _ = ENNReal.ofReal (4 * ((((W * L) ^ d : ℕ)) : ℝ) ^ 2 *
        Real.exp (-((((W * L) ^ d : ℕ) : ℝ) / 8))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), Step1RegularityGUE_card_Coord]
        congr 1
        ring

/-- `4 N² e^{-N/8} ≤ N^{-(D+1)}` eventually, from `N → ∞` only (`x^s e^{-b x} → 0`). -/
private theorem Step1RegularityGUE_entry_eventually (D : ℝ) {d : ℕ} (sz : Sizes d)
    (hd : Tendsto (fun n => sz.size n) atTop atTop) :
    ∀ᶠ n in atTop, 4 * Nsz sz n ^ 2 * Real.exp (-(Nsz sz n / 8)) ≤ Nsz sz n ^ (-(D + 1)) := by
  have hNtend : Tendsto (fun n => Nsz sz n) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hd
  have hdecay := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (D + 3) (1 / 8) (by norm_num)
  have hsmall : ∀ᶠ x : ℝ in atTop, x ^ (D + 3) * Real.exp (-(1 / 8) * x) ≤ 1 / 4 :=
    hdecay.eventually (ge_mem_nhds (by norm_num))
  filter_upwards [hNtend.eventually hsmall, hNtend.eventually_ge_atTop 1] with n hn hN1
  set N : ℝ := Nsz sz n with hNdef
  have hNpos : 0 < N := by linarith
  have h3 : N ^ 2 * N ^ (D + 1) = N ^ (D + 3) := by
    rw [← Real.rpow_natCast N 2, ← Real.rpow_add hNpos]
    congr 1
    push_cast
    ring
  have hpos : 0 < N ^ (D + 1) := Real.rpow_pos_of_pos hNpos _
  have hexp : Real.exp (-(N / 8)) = Real.exp (-(1 / 8) * N) := by
    congr 1; ring
  have h4 : 4 * N ^ 2 * Real.exp (-(N / 8)) * N ^ (D + 1) ≤ 1 := by
    calc 4 * N ^ 2 * Real.exp (-(N / 8)) * N ^ (D + 1)
        = 4 * (N ^ 2 * N ^ (D + 1)) * Real.exp (-(N / 8)) := by ring
      _ = 4 * (N ^ (D + 3) * Real.exp (-(1 / 8) * N)) := by rw [h3, hexp]; ring
      _ ≤ 4 * (1 / 4) := by gcongr
      _ = 1 := by norm_num
  rw [Real.rpow_neg hNpos.le, ← one_div]
  exact (le_div_iff₀ hpos).2 h4

/-- **Target 2a** `guelocalEventHighProb` (S7a; RBM2D `:381`): `UNGUELocal` at `(κ, τ, D + 1)`, the entry
bound at `D + 1`, and `2 N^{-(D+1)} ≤ N^{-D}` for `N ≥ 2`. -/
theorem guelocalEventHighProb : UNGUELocalEventHighProb := by
  intro hG d hd3 sz hd κ τ D hκ hτ hD
  have h1 := hG d hd3 sz hd κ τ (D + 1) hκ hτ (by linarith)
  have h2 := Step1RegularityGUE_entry_eventually D sz hd
  have hNtend : Tendsto (fun n => Nsz sz n) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hd
  filter_upwards [h1, h2, hNtend.eventually_ge_atTop 2] with n hn1 hn2 hN2
  set N : ℝ := Nsz sz n with hNdef
  have hNpos : 0 < N := by linarith
  have hentry := Step1RegularityGUE_entry_bound d (sz.L n) (sz.W n)
  have hsub : {ω : Ω d (sz.L n) (sz.W n) | ¬ Step1LocalEventGUE sz n κ τ ω} ⊆
      {ω | ∃ z : ℂ, |z.re| ≤ 2 - κ ∧ N ^ (-1 + τ) ≤ z.im ∧ z.im ≤ 10 ∧
          N ^ τ / Real.sqrt (N * z.im) <
            ‖stieltjesN (Xmat d (sz.L n) (sz.W n) ω) z - msc z‖} ∪
        {ω | ¬ ∀ x y : Idx d (sz.L n) (sz.W n), ‖Xmat d (sz.L n) (sz.W n) ω x y‖ ≤ 1} := by
    intro ω hω
    by_cases hent : ∀ x y : Idx d (sz.L n) (sz.W n), ‖Xmat d (sz.L n) (sz.W n) ω x y‖ ≤ 1
    · left
      by_contra hcon
      apply hω
      refine ⟨fun z hz1 hz2 hz3 => ?_, hent⟩
      by_contra hlt
      push Not at hlt
      exact hcon ⟨z, hz1, hz2, hz3, hlt⟩
    · exact Or.inr hent
  have hN2' : 2 * N ^ (-(D + 1)) ≤ N ^ (-D) := by
    have : N ^ (-D) = N * N ^ (-(D + 1)) := by
      rw [← Real.rpow_one_add' hNpos.le (by linarith [hD])]
      congr 1; ring
    rw [this]
    have := Real.rpow_nonneg hNpos.le (-(D + 1))
    nlinarith
  have hentry' : gueP d (sz.L n) (sz.W n)
      {ω | ¬ ∀ x y : Idx d (sz.L n) (sz.W n), ‖Xmat d (sz.L n) (sz.W n) ω x y‖ ≤ 1} ≤
        ENNReal.ofReal (N ^ (-(D + 1))) := by
    refine hentry.trans ?_
    exact ENNReal.ofReal_le_ofReal hn2
  calc gueP d (sz.L n) (sz.W n) {ω | ¬ Step1LocalEventGUE sz n κ τ ω}
      ≤ gueP d (sz.L n) (sz.W n) ({ω | ∃ z : ℂ, |z.re| ≤ 2 - κ ∧ N ^ (-1 + τ) ≤ z.im ∧ z.im ≤ 10 ∧
          N ^ τ / Real.sqrt (N * z.im) <
            ‖stieltjesN (Xmat d (sz.L n) (sz.W n) ω) z - msc z‖} ∪
        {ω | ¬ ∀ x y : Idx d (sz.L n) (sz.W n), ‖Xmat d (sz.L n) (sz.W n) ω x y‖ ≤ 1}) :=
        measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (N ^ (-(D + 1))) + ENNReal.ofReal (N ^ (-(D + 1))) :=
        add_le_add hn1 hentry'
    _ = ENNReal.ofReal (2 * N ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add (Real.rpow_nonneg hNpos.le _) (Real.rpow_nonneg hNpos.le _)]
        congr 1; ring
    _ ≤ ENNReal.ofReal (N ^ (-D)) := ENNReal.ofReal_le_ofReal hN2'

/-- **Target 2b** `gue_err_pow` (RBM2D `:437`): where the weak precision enters: on the event, at
`Im z ≥ c N^{-1+σ}`, `‖m_N(z) - m_sc(z)‖ ≤ c^{-1/2} N^{τ - σ/2}`. -/
theorem gue_err_pow :
    ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {κ τ : ℝ} {ω : Ω d (sz.L n) (sz.W n)},
      Step1LocalEventGUE sz n κ τ ω → 1 ≤ sz.size n → ∀ {z : ℂ},
        |z.re| ≤ 2 - κ → Nsz sz n ^ (-1 + τ) ≤ z.im → z.im ≤ 10 → ∀ {c σ : ℝ}, 0 < c →
          c * Nsz sz n ^ (-1 + σ) ≤ z.im →
            ‖stieltjesN (Xmat d (sz.L n) (sz.W n) ω) z - msc z‖ ≤ Real.sqrt c⁻¹ * Nsz sz n ^ (τ - σ / 2) := by
  intro d sz n κ τ ω hev hN z hz1 hz2 hz3 c σ hc hzc
  set N : ℝ := Nsz sz n with hNdef
  have hNr1 : (1 : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast hN
  have hNr0 : 0 < N := by linarith
  have h := hev.1 z hz1 hz2 hz3
  have hzim : 0 < z.im := lt_of_lt_of_le (Real.rpow_pos_of_pos hNr0 _) hz2
  have hNz : c * N ^ σ ≤ N * z.im := by
    calc c * N ^ σ = N * (c * N ^ (-1 + σ)) := by
          rw [Real.rpow_add hNr0, Real.rpow_neg_one]; field_simp
      _ ≤ N * z.im := mul_le_mul_of_nonneg_left hzc hNr0.le
  have hsq : Real.sqrt c * N ^ (σ / 2) ≤ Real.sqrt (N * z.im) := by
    have : Real.sqrt (c * N ^ σ) = Real.sqrt c * N ^ (σ / 2) := by
      rw [Real.sqrt_mul hc.le, Real.sqrt_eq_rpow (N ^ σ), ← Real.rpow_mul hNr0.le]
      congr 2; ring
    rw [← this]; exact Real.sqrt_le_sqrt hNz
  have hc0 : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hp : 0 < N ^ (σ / 2) := Real.rpow_pos_of_pos hNr0 _
  calc ‖stieltjesN (Xmat d (sz.L n) (sz.W n) ω) z - msc z‖ ≤ N ^ τ / Real.sqrt (N * z.im) := h
    _ ≤ N ^ τ / (Real.sqrt c * N ^ (σ / 2)) :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hNr0.le _) (by positivity) hsq
    _ = Real.sqrt c⁻¹ * N ^ (τ - σ / 2) := by
        rw [Real.sqrt_inv, Real.rpow_sub hNr0]; field_simp

/-! ## 4. S7b: the deterministic half under the weak precision (RBM2D `:465-1111`)

Elementary facts on `a = e^{-T/2}` and the eigenvalue dictionary are re-proved under the prefix
`Step1RegularityGUE_` (the `Step1Good_` versions are private); `stieltjesN_eq_mV`, `mV_eta_mul_im_mono`,
`mV_im_le_inv` (Step1Good) and `stieltjesN_eta_mul_im_mono` (InjSum) are reused. -/

private theorem Step1RegularityGUE_exp_le_one {T : ℝ} (hT : 0 ≤ T) :
    Real.exp (-T / 2) ≤ 1 := by
  rw [Real.exp_le_one_iff]; linarith

private theorem Step1RegularityGUE_one_le_inv {T : ℝ} (hT : 0 ≤ T) :
    1 ≤ (Real.exp (-T / 2))⁻¹ := by
  rw [one_le_inv₀ (Real.exp_pos _)]
  exact Step1RegularityGUE_exp_le_one hT

/-- `(e^{-T/2})⁻¹ ≤ 1 + T` for `0 ≤ T ≤ 1`. -/
private theorem Step1RegularityGUE_inv_le {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    (Real.exp (-T / 2))⁻¹ ≤ 1 + T := by
  have h := Real.add_one_le_exp (-T / 2)
  have h1 : (0 : ℝ) < -T / 2 + 1 := by linarith
  refine (inv_anti₀ h1 h).trans ?_
  rw [inv_le_iff_one_le_mul₀ h1]
  nlinarith

/-- `1 - e^{-T} ≤ T`. -/
private theorem Step1RegularityGUE_one_sub_exp_le (T : ℝ) : 1 - Real.exp (-T) ≤ T := by
  have := Real.add_one_le_exp (-T); linarith

/-- `T / 2 ≤ 1 - e^{-T}` for `0 ≤ T ≤ 1`. -/
private theorem Step1RegularityGUE_half_le_one_sub_exp {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    T / 2 ≤ 1 - Real.exp (-T) := by
  have h := Real.add_one_le_exp T
  have h1 : (0 : ℝ) < T + 1 := by linarith
  have h2 : Real.exp (-T) ≤ (T + 1)⁻¹ := by
    rw [Real.exp_neg]; exact inv_anti₀ h1 h
  have h3 : (T + 1)⁻¹ ≤ 1 - T / 2 := by
    rw [inv_le_iff_one_le_mul₀ h1]; nlinarith
  linarith

private theorem Step1RegularityGUE_one_sub_exp_pos {T : ℝ} (hT : 0 < T) :
    0 < 1 - Real.exp (-T) := by
  have : Real.exp (-T) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  linarith

private theorem Step1RegularityGUE_sqrt_exp (T : ℝ) :
    Real.sqrt (Real.exp (-T)) = Real.exp (-T / 2) :=
  (Real.exp_half (-T)).symm

private theorem Step1RegularityGUE_inv_mul_re (a : ℝ) (X : ℂ) :
    (((a : ℝ) : ℂ)⁻¹ * X).re = a⁻¹ * X.re := by
  rw [← Complex.ofReal_inv, Complex.re_ofReal_mul]

private theorem Step1RegularityGUE_inv_mul_im (a : ℝ) (X : ℂ) :
    (((a : ℝ) : ℂ)⁻¹ * X).im = a⁻¹ * X.im := by
  rw [← Complex.ofReal_inv, Complex.im_ofReal_mul]

/-- The affine dictionary: `m_V(w) = a⁻¹ m_N(a⁻¹ (w + E₀))` for `v_i = a λ_i - E₀`, `a > 0`
(copy of the private `Step1Good_mV_affine`, `Step1Good.lean:107`). -/
private theorem Step1RegularityGUE_mV_affine {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {a : ℝ} (ha : 0 < a) (E₀ : ℝ) {w : ℂ}
    (hw : 0 < w.im) :
    mV (fun i => a * hH.eigenvalues i - E₀) w =
      ((a : ℝ) : ℂ)⁻¹ * stieltjesN H (((a : ℝ) : ℂ)⁻¹ * (w + E₀)) := by
  have hz : 0 < (((a : ℝ) : ℂ)⁻¹ * (w + E₀)).im := by
    rw [Step1RegularityGUE_inv_mul_im, Complex.add_im, Complex.ofReal_im, add_zero]
    positivity
  rw [stieltjesN_eq_mV hH hz]
  unfold mV
  rw [mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  set lami : ℝ := hH.eigenvalues i with hlam_def
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hkey : ((a : ℝ) : ℂ) * lami - (E₀ : ℂ) - w =
      (a : ℂ) * ((lami : ℂ) - (((a : ℝ) : ℂ)⁻¹ * (w + E₀))) := by
    rw [mul_sub]
    rw [show (a : ℂ) * (((a : ℝ) : ℂ)⁻¹ * (w + E₀)) = w + E₀ by field_simp]
    ring
  rw [show ((a * lami - E₀ : ℝ) : ℂ) - w = ((a : ℝ) : ℂ) * lami - (E₀ : ℂ) - w by push_cast; ring,
    hkey, mul_inv]

/-- **Bulk lower bound** (RBM1D `step1_msc_im_ge`, RBM2D `:625`):
`Im m_sc(z) ≥ κ'/12` for `|Re z| ≤ 2 - κ'/2`, `0 < Im z ≤ 3`, `0 < κ' ≤ 1`. -/
private theorem Step1RegularityGUE_msc_im_ge {κ' : ℝ} (hκ0 : 0 < κ') (hκ1 : κ' ≤ 1) {z : ℂ}
    (hre : |z.re| ≤ 2 - κ' / 2) (him0 : 0 < z.im) (him1 : z.im ≤ 3) :
    κ' / 12 ≤ (msc z).im := by
  set a := msc z with ha_def
  have hapos : 0 < a.im := msc_im_pos him0
  have hne : a ≠ 0 := fun h0 => by rw [h0, Complex.zero_im] at hapos; exact lt_irrefl _ hapos
  have hnz : ‖z‖ ≤ 5 := by
    have := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos him0] at this
    have h2 : |z.re| ≤ 2 := by linarith
    linarith
  set R := Complex.normSq a with hR_def
  have hRpos : 0 < R := Complex.normSq_pos.mpr hne
  have hR : (1 : ℝ) / 36 ≤ R := by
    have h1 := lemT_ge him0
    unfold lemT at h1
    rw [hR_def, Complex.normSq_eq_norm_sq]
    have h2 : ((1 + 5 : ℝ) ^ 2)⁻¹ ≤ ((1 + ‖z‖) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (by nlinarith [norm_nonneg z])
    calc (1 : ℝ) / 36 = ((1 + 5 : ℝ) ^ 2)⁻¹ := by norm_num
      _ ≤ ((1 + ‖z‖) ^ 2)⁻¹ := h2
      _ ≤ ‖msc z‖ ^ 2 := h1
  have hre_rel : z.re * R = -(a.re * (R + 1)) := by
    have h := congrArg Complex.re (msc_add_eq_neg_inv him0)
    simp only [Complex.add_re, Complex.neg_re, Complex.inv_re] at h
    rw [← ha_def, ← hR_def] at h
    field_simp at h
    linear_combination h
  have hsq : z.re ^ 2 * R ^ 2 = a.re ^ 2 * (R + 1) ^ 2 := by
    have := congrArg (· ^ 2) hre_rel
    linear_combination this
  have hx : a.re ^ 2 * (4 * R) ≤ z.re ^ 2 * R ^ 2 := by
    rw [hsq]
    have : 4 * R ≤ (R + 1) ^ 2 := by nlinarith [sq_nonneg (R - 1)]
    exact mul_le_mul_of_nonneg_left this (sq_nonneg _)
  have hx2 : a.re ^ 2 * 4 ≤ z.re ^ 2 * R := by
    have h := hx
    have : a.re ^ 2 * (4 * R) = (a.re ^ 2 * 4) * R := by ring
    rw [this, show z.re ^ 2 * R ^ 2 = (z.re ^ 2 * R) * R by ring] at h
    exact le_of_mul_le_mul_right h hRpos
  have hzre2 : z.re ^ 2 ≤ (2 - κ' / 2) ^ 2 := by
    have h0 : 0 ≤ |z.re| := abs_nonneg _
    have := mul_le_mul hre hre h0 (by linarith)
    rw [← sq, sq_abs] at this
    simpa [sq] using this
  have hRdef : R = a.re ^ 2 + a.im ^ 2 := by
    rw [hR_def, Complex.normSq_apply]; ring
  have hy2 : κ' ^ 2 / 144 ≤ a.im ^ 2 := by
    have h1 : a.re ^ 2 * 4 ≤ (2 - κ' / 2) ^ 2 * R :=
      hx2.trans (mul_le_mul_of_nonneg_right hzre2 hRpos.le)
    have h2 : R * (κ' / 4) ≤ a.im ^ 2 := by nlinarith
    have h3 : κ' / 144 ≤ R * (κ' / 4) := by nlinarith
    nlinarith
  by_contra hcon
  push Not at hcon
  have : a.im ^ 2 < (κ' / 12) ^ 2 := by
    have := mul_lt_mul'' hcon hcon hapos.le hapos.le
    nlinarith
  nlinarith

/-- If `|E₀| ≤ 2 - κ`, `|Re w| ≤ R ≤ κ'/4`, `y ≤ Im w ≤ 1/2`, `N^{-1+τ} ≤ y` and `0 ≤ T ≤ κ'/240`
(`κ' = min κ 1`), then `z = a⁻¹ (w + E₀)`, `a = e^{-T/2}`, satisfies `|Re z| ≤ 2 - κ/2`,
`N^{-1+τ} ≤ Im z ≤ 1` (the `locDomain N (κ/2) τ` conditions) and `Im w ≤ Im z`. -/
private theorem Step1RegularityGUE_domain {N κ τ E₀ T R y : ℝ} (hκ : 0 < κ)
    (hE₀ : |E₀| ≤ 2 - κ) (hT0 : 0 ≤ T) (hT : T ≤ min κ 1 / 240) (hR : R ≤ min κ 1 / 4)
    (hy0 : 0 < y) (hy : N ^ (-1 + τ) ≤ y) {w : ℂ} (hw : |w.re| ≤ R) (hwy : y ≤ w.im)
    (hw1 : w.im ≤ 1 / 2) :
    (|(((Real.exp (-T / 2) : ℝ) : ℂ)⁻¹ * (w + E₀)).re| ≤ 2 - κ / 2 ∧
      N ^ (-1 + τ) ≤ (((Real.exp (-T / 2) : ℝ) : ℂ)⁻¹ * (w + E₀)).im ∧
      (((Real.exp (-T / 2) : ℝ) : ℂ)⁻¹ * (w + E₀)).im ≤ 1) ∧
      w.im ≤ ((((Real.exp (-T / 2) : ℝ) : ℂ)⁻¹ * (w + E₀))).im := by
  have ha0 : 0 < Real.exp (-T / 2) := Real.exp_pos _
  have hκ' : min κ 1 ≤ κ := min_le_left _ _
  have hκ'1 : min κ 1 ≤ 1 := min_le_right _ _
  have hκ'0 : 0 < min κ 1 := lt_min hκ one_pos
  have hT1 : T ≤ 1 := by linarith
  have hainv1 : 1 ≤ (Real.exp (-T / 2))⁻¹ := Step1RegularityGUE_one_le_inv hT0
  have hainv : (Real.exp (-T / 2))⁻¹ ≤ 1 + T := Step1RegularityGUE_inv_le hT0 hT1
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E₀]
  have hR0 : 0 ≤ R := le_trans (abs_nonneg _) hw
  have hwim0 : 0 < w.im := lt_of_lt_of_le hy0 hwy
  have hre : (((Real.exp (-T / 2) : ℝ) : ℂ)⁻¹ * (w + E₀)).re =
      (Real.exp (-T / 2))⁻¹ * (w.re + E₀) := by
    rw [Step1RegularityGUE_inv_mul_re, Complex.add_re, Complex.ofReal_re]
  have him : (((Real.exp (-T / 2) : ℝ) : ℂ)⁻¹ * (w + E₀)).im =
      (Real.exp (-T / 2))⁻¹ * w.im := by
    rw [Step1RegularityGUE_inv_mul_im, Complex.add_im, Complex.ofReal_im, add_zero]
  have hge : w.im ≤ (Real.exp (-T / 2))⁻¹ * w.im := by
    calc w.im = 1 * w.im := (one_mul _).symm
      _ ≤ (Real.exp (-T / 2))⁻¹ * w.im := mul_le_mul_of_nonneg_right hainv1 hwim0.le
  refine ⟨⟨?_, ?_, ?_⟩, by rw [him]; exact hge⟩
  · rw [hre, abs_mul, abs_of_pos (inv_pos.2 ha0)]
    have h1 : |w.re + E₀| ≤ R + (2 - κ) := (abs_add_le _ _).trans (add_le_add hw hE₀)
    have h2 : 0 ≤ R + (2 - κ) := by linarith
    have h3 : T * (R + (2 - κ)) ≤ min κ 1 / 240 * (R + (2 - κ)) :=
      mul_le_mul_of_nonneg_right hT h2
    calc (Real.exp (-T / 2))⁻¹ * |w.re + E₀| ≤ (1 + T) * (R + (2 - κ)) :=
          mul_le_mul hainv h1 (abs_nonneg _) (by linarith)
      _ ≤ 2 - κ / 2 := by nlinarith
  · rw [him]; exact hy.trans (hwy.trans hge)
  · rw [him]
    calc (Real.exp (-T / 2))⁻¹ * w.im ≤ (1 + T) * (1 / 2) :=
          mul_le_mul hainv hw1 hwim0.le (by linarith)
      _ ≤ 1 := by linarith

/-- The point of the event attached to `w = E + iη`. -/
private theorem Step1RegularityGUE_arg_eq (a E₀ E η : ℝ) :
    ((a : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀)) =
      ((a⁻¹ * (E + E₀) : ℝ) : ℂ) + ((a⁻¹ * η : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · rw [Step1RegularityGUE_inv_mul_re]; simp
  · rw [Step1RegularityGUE_inv_mul_im]; simp

/-- `|λ_i| ≤ N` when every entry has modulus at most `1`: from `H ψ = λ ψ`,
`|λ| |ψ_x| ≤ Σ_y |ψ_y|`, summed over `x`. -/
private theorem Step1RegularityGUE_eigenvalue_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (hent : ∀ x y, ‖H x y‖ ≤ 1) (i : ι) :
    |hH.eigenvalues i| ≤ (Fintype.card ι : ℝ) := by
  set ψ : EuclideanSpace ℂ ι := hH.eigenvectorBasis i with hψ
  have hψn : ‖ψ‖ = 1 := hH.eigenvectorBasis.norm_eq_one i
  have hmv := hH.mulVec_eigenvectorBasis i
  have hsq : ∑ y, ‖ψ.ofLp y‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, hψn]; norm_num
  have hle1 : ∀ y, ‖ψ.ofLp y‖ ≤ 1 := by
    intro y
    have : ‖ψ.ofLp y‖ ^ 2 ≤ 1 := by
      rw [← hsq]
      exact Finset.single_le_sum (f := fun y => ‖ψ.ofLp y‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ y)
    nlinarith [norm_nonneg (ψ.ofLp y)]
  set S : ℝ := ∑ y, ‖ψ.ofLp y‖ with hS
  have hS1 : 1 ≤ S := by
    calc (1 : ℝ) = ∑ y, ‖ψ.ofLp y‖ ^ 2 := hsq.symm
      _ ≤ ∑ y, ‖ψ.ofLp y‖ := Finset.sum_le_sum fun y _ => by
          nlinarith [norm_nonneg (ψ.ofLp y), hle1 y]
  have hrow : ∀ x, |hH.eigenvalues i| * ‖ψ.ofLp x‖ ≤ S := by
    intro x
    have h1 : (H.mulVec ψ.ofLp) x = (hH.eigenvalues i • ψ.ofLp) x := by rw [hmv]
    have h2 : ‖(hH.eigenvalues i • ψ.ofLp) x‖ = |hH.eigenvalues i| * ‖ψ.ofLp x‖ := by
      simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs]
    rw [← h2, ← h1]
    calc ‖(H.mulVec ψ.ofLp) x‖ = ‖∑ y, H x y * ψ.ofLp y‖ := rfl
      _ ≤ ∑ y, ‖H x y * ψ.ofLp y‖ := norm_sum_le _ _
      _ ≤ ∑ y, ‖ψ.ofLp y‖ := Finset.sum_le_sum fun y _ => by
          rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hent x y)
  have hsum : |hH.eigenvalues i| * S ≤ (Fintype.card ι : ℝ) * S := by
    calc |hH.eigenvalues i| * S = ∑ x, |hH.eigenvalues i| * ‖ψ.ofLp x‖ := by
          rw [hS, Finset.mul_sum]
      _ ≤ ∑ _x : ι, S := Finset.sum_le_sum fun x _ => hrow x
      _ = (Fintype.card ι : ℝ) * S := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact le_of_mul_le_mul_right hsum (by linarith)

private theorem Step1RegularityGUE_rpow_ev {e c : ℝ} (he : e < 0) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, x ^ e ≤ c := by
  have h := (tendsto_rpow_neg_atTop (y := -e) (by linarith)).eventually (ge_mem_nhds hc)
  simpa using h

/-- Regime 1 of (2.2): for `|E| ≤ R`, `N^{-1+σ} ≤ η ≤ 1/2`, on the event, the imaginary part of
`m_N` at the rescaled point is in `[κ'/24, 1 + κ'/24]`, provided the event error
`N^{τ - σ/2} ≤ κ'/24`. -/
private theorem Step1RegularityGUE_bulk {d : ℕ} (sz : Sizes d) (n : ℕ) {κ τ E₀ T R σ : ℝ}
    {ω : Ω d (sz.L n) (sz.W n)}
    (hκ : 0 < κ) (hE₀ : |E₀| ≤ 2 - κ) (hev : Step1LocalEventGUE sz n (κ / 2) τ ω)
    (hN : 1 ≤ sz.size n) (hT0 : 0 ≤ T) (hT : T ≤ min κ 1 / 240)
    (hR : R ≤ min κ 1 / 4) (hτσ : τ ≤ σ)
    (herr : Nsz sz n ^ (τ - σ / 2) ≤ min κ 1 / 24)
    {E η : ℝ} (hE : |E| ≤ R) (hη : Nsz sz n ^ (-1 + σ) ≤ η) (hη1 : η ≤ 1 / 2) :
    min κ 1 / 24 ≤ (stieltjesN (Xmat d (sz.L n) (sz.W n) ω)
        (((Real.exp (-T / 2) : ℝ) : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀))).im ∧
      (stieltjesN (Xmat d (sz.L n) (sz.W n) ω)
        (((Real.exp (-T / 2) : ℝ) : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀))).im ≤ 1 + min κ 1 / 24 := by
  have hNr1 : (1 : ℝ) ≤ Nsz sz n := by exact_mod_cast hN
  have hNr0 : (0 : ℝ) < Nsz sz n := by linarith
  have hκ'0 : 0 < min κ 1 := lt_min hκ one_pos
  have hκ'1 : min κ 1 ≤ 1 := min_le_right _ _
  have hκ'κ : min κ 1 ≤ κ := min_le_left _ _
  have hy0 : 0 < Nsz sz n ^ (-1 + σ) := Real.rpow_pos_of_pos hNr0 _
  have hyτ : Nsz sz n ^ (-1 + τ) ≤ Nsz sz n ^ (-1 + σ) :=
    Real.rpow_le_rpow_of_exponent_le hNr1 (by linarith)
  obtain ⟨hdom, hdomim⟩ := Step1RegularityGUE_domain (N := Nsz sz n) (τ := τ) (w := ⟨E, η⟩)
    hκ hE₀ hT0 hT hR hy0 hyτ hE hη hη1
  have herrz := gue_err_pow sz n hev hN hdom.1 hdom.2.1 (hdom.2.2.trans (by norm_num))
    (c := 1) (σ := σ) one_pos (by rw [one_mul]; exact hη.trans hdomim)
  set z : ℂ := ((Real.exp (-T / 2) : ℝ) : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀) with hz
  have hzim : 0 < z.im := lt_of_lt_of_le (lt_of_lt_of_le hy0 hη) hdomim
  have hnorm : ‖stieltjesN (Xmat d (sz.L n) (sz.W n) ω) z - msc z‖ ≤ min κ 1 / 24 := by
    refine herrz.trans ?_
    rw [inv_one, Real.sqrt_one, one_mul]; exact herr
  have hIm : |(stieltjesN (Xmat d (sz.L n) (sz.W n) ω) z).im - (msc z).im| ≤ min κ 1 / 24 := by
    calc |(stieltjesN (Xmat d (sz.L n) (sz.W n) ω) z).im - (msc z).im|
        = |(stieltjesN (Xmat d (sz.L n) (sz.W n) ω) z - msc z).im| := by rw [Complex.sub_im]
      _ ≤ ‖stieltjesN (Xmat d (sz.L n) (sz.W n) ω) z - msc z‖ := Complex.abs_im_le_norm _
      _ ≤ min κ 1 / 24 := hnorm
  have hzre : |z.re| ≤ 2 - min κ 1 / 2 := by
    have := hdom.1; linarith
  have hmsc := Step1RegularityGUE_msc_im_ge hκ'0 hκ'1 hzre hzim (by linarith [hdom.2.2])
  have hmscn := norm_msc_lt_one (z := z) hzim
  have hmscim : (msc z).im < 1 :=
    lt_of_le_of_lt ((le_abs_self _).trans (Complex.abs_im_le_norm _)) hmscn
  obtain ⟨h1, h2⟩ := abs_le.mp hIm
  constructor <;> linarith

/-- **The regularity part** (RBM2D `:839`), deterministic on the event (no grid): `[32]`-regularity of
`vGUE` with `g = N^{-1+τs/4}`, `G = N^{-σ}`, `c = min κ 1 / 960`, `C = 2`, `CV = 2`. -/
private theorem Step1RegularityGUE_regular {d : ℕ} (sz : Sizes d) (n : ℕ) {κ τ τs E₀ : ℝ}
    {ω : Ω d (sz.L n) (sz.W n)}
    (hκ : 0 < κ) (hE₀ : |E₀| ≤ 2 - κ) (hτ4 : τ ≤ τs / 4)
    (hev : Step1LocalEventGUE sz n (κ / 2) τ ω) (hN : 2 ≤ sz.size n)
    (hg : Nsz sz n ^ (-1 + τs / 4) ≤ 1 / 2)
    (hG : Nsz sz n ^ (-(min (τs / 4) ((1 - τs) / 3))) ≤ min κ 1 / 4)
    (hT : Nsz sz n ^ (-1 + τs) ≤ min κ 1 / 240)
    (herr : Nsz sz n ^ (τ - τs / 8) ≤ min κ 1 / 24) :
    IsRegular32 (vGUE sz n τs E₀ ω) (Nsz sz n ^ (-1 + τs / 4))
      (Nsz sz n ^ (-(min (τs / 4) ((1 - τs) / 3)))) (min κ 1 / 960) 2 2 := by
  have hN1 : 1 ≤ sz.size n := by omega
  have hNr1 : (1 : ℝ) ≤ Nsz sz n := by exact_mod_cast hN1
  have hNr2 : (2 : ℝ) ≤ Nsz sz n := by exact_mod_cast hN
  have hNr0 : (0 : ℝ) < Nsz sz n := by linarith
  have hκ'0 : 0 < min κ 1 := lt_min hκ one_pos
  have hκ'1 : min κ 1 ≤ 1 := min_le_right _ _
  have hT0 : 0 ≤ ouTStar sz τs n := Real.rpow_nonneg hNr0.le _
  have hT' : ouTStar sz τs n ≤ min κ 1 / 240 := hT
  have hT1 : ouTStar sz τs n ≤ 1 := by linarith
  have ha0 : 0 < Real.exp (-(ouTStar sz τs n) / 2) := Real.exp_pos _
  have hainv1 : 1 ≤ (Real.exp (-(ouTStar sz τs n) / 2))⁻¹ := Step1RegularityGUE_one_le_inv hT0
  have hainv : (Real.exp (-(ouTStar sz τs n) / 2))⁻¹ ≤ 1 + ouTStar sz τs n :=
    Step1RegularityGUE_inv_le hT0 hT1
  have hH := Xmat_isHermitian d (sz.L n) (sz.W n) ω
  have hgpos : 0 < Nsz sz n ^ (-1 + τs / 4) := Real.rpow_pos_of_pos hNr0 _
  have hbulk : ∀ E η : ℝ, |E| ≤ Nsz sz n ^ (-(min (τs / 4) ((1 - τs) / 3))) →
      Nsz sz n ^ (-1 + τs / 4) ≤ η → η ≤ 1 / 2 →
      min κ 1 / 24 ≤ (stieltjesN (Xmat d (sz.L n) (sz.W n) ω)
          (((Real.exp (-(ouTStar sz τs n) / 2) : ℝ) : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀))).im ∧
        (stieltjesN (Xmat d (sz.L n) (sz.W n) ω)
          (((Real.exp (-(ouTStar sz τs n) / 2) : ℝ) : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀))).im ≤
          1 + min κ 1 / 24 := fun E η hE hη hη1 =>
    Step1RegularityGUE_bulk sz n hκ hE₀ hev hN1 hT0 hT hG (σ := τs / 4) hτ4
      (by rw [show τ - τs / 4 / 2 = τ - τs / 8 by ring]; exact herr) hE hη hη1
  refine ⟨?_, ?_⟩
  · intro E η hE hgη hη10
    have hηpos : 0 < η := lt_of_lt_of_le hgpos hgη
    have hdict : mV (vGUE sz n τs E₀ ω) ⟨E, η⟩ =
        ((Real.exp (-(ouTStar sz τs n) / 2) : ℝ) : ℂ)⁻¹ * stieltjesN (Xmat d (sz.L n) (sz.W n) ω)
          (((Real.exp (-(ouTStar sz τs n) / 2) : ℝ) : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀)) :=
      Step1RegularityGUE_mV_affine hH ha0 E₀ (w := ⟨E, η⟩) hηpos
    have hdictIm : (mV (vGUE sz n τs E₀ ω) ⟨E, η⟩).im =
        (Real.exp (-(ouTStar sz τs n) / 2))⁻¹ * (stieltjesN (Xmat d (sz.L n) (sz.W n) ω)
          (((Real.exp (-(ouTStar sz τs n) / 2) : ℝ) : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀))).im := by
      rw [hdict, Step1RegularityGUE_inv_mul_im]
    by_cases hη12 : η ≤ 1 / 2
    · obtain ⟨hb1, hb2⟩ := hbulk E η hE hgη hη12
      rw [hdictIm]
      have hS0 : 0 ≤ (stieltjesN (Xmat d (sz.L n) (sz.W n) ω)
          (((Real.exp (-(ouTStar sz τs n) / 2) : ℝ) : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀))).im := by
        linarith
      refine ⟨?_, ?_⟩
      · calc min κ 1 / 960 ≤ min κ 1 / 24 := by linarith
          _ ≤ _ := hb1
          _ = 1 * _ := (one_mul _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_right hainv1 hS0
      · calc _ ≤ (1 + ouTStar sz τs n) * (1 + min κ 1 / 24) :=
              mul_le_mul hainv hb2 hS0 (by linarith)
          _ ≤ 2 := by nlinarith
    · have hη12' : 1 / 2 < η := not_le.mp hη12
      have hainv0 : 0 < (Real.exp (-(ouTStar sz τs n) / 2))⁻¹ := inv_pos.2 ha0
      have hlb := (hbulk E (1 / 2) hE (by linarith) le_rfl).1
      have hmono : (Real.exp (-(ouTStar sz τs n) / 2))⁻¹ * (1 / 2) *
            (stieltjesN (Xmat d (sz.L n) (sz.W n) ω)
              (((Real.exp (-(ouTStar sz τs n) / 2) : ℝ) : ℂ)⁻¹ *
                ((⟨E, 1 / 2⟩ : ℂ) + E₀))).im ≤
          (Real.exp (-(ouTStar sz τs n) / 2))⁻¹ * η *
            (stieltjesN (Xmat d (sz.L n) (sz.W n) ω)
              (((Real.exp (-(ouTStar sz τs n) / 2) : ℝ) : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀))).im := by
        rw [Step1RegularityGUE_arg_eq, Step1RegularityGUE_arg_eq]
        exact stieltjesN_eta_mul_im_mono (Xmat d (sz.L n) (sz.W n) ω) hH _ _ _ (by positivity)
          (mul_le_mul_of_nonneg_left hη12'.le hainv0.le)
      set S₂ := (stieltjesN (Xmat d (sz.L n) (sz.W n) ω)
          (((Real.exp (-(ouTStar sz τs n) / 2) : ℝ) : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀))).im with hS₂
      have h3 : (Real.exp (-(ouTStar sz τs n) / 2))⁻¹ * (1 / 2) * (min κ 1 / 24) ≤
          (Real.exp (-(ouTStar sz τs n) / 2))⁻¹ * (η * S₂) := by
        rw [← mul_assoc]
        exact le_trans (mul_le_mul_of_nonneg_left hlb (by positivity)) hmono
      have h4 : 1 / 2 * (min κ 1 / 24) ≤ η * S₂ := by
        have : (Real.exp (-(ouTStar sz τs n) / 2))⁻¹ * (1 / 2 * (min κ 1 / 24)) ≤
            (Real.exp (-(ouTStar sz τs n) / 2))⁻¹ * (η * S₂) := by
          rw [← mul_assoc]; exact h3
        exact le_of_mul_le_mul_left this hainv0
      have hS₂pos : 0 < S₂ := by
        by_contra hneg
        push Not at hneg
        nlinarith [mul_nonneg hηpos.le (neg_nonneg.2 hneg)]
      have h5 : min κ 1 / 480 ≤ S₂ := by
        nlinarith [mul_le_mul_of_nonneg_right hη10 hS₂pos.le]
      refine ⟨?_, ?_⟩
      · rw [hdictIm]
        calc min κ 1 / 960 ≤ min κ 1 / 480 := by linarith
          _ ≤ S₂ := h5
          _ = 1 * S₂ := (one_mul _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_right hainv1 hS₂pos.le
      · have hle := mV_im_le_inv (vGUE sz n τs E₀ ω) E η hηpos
        calc (mV (vGUE sz n τs E₀ ω) ⟨E, η⟩).im ≤ 1 / η := hle
          _ ≤ 2 := by
              rw [div_le_iff₀ hηpos]
              linarith
  · intro i
    have hc : (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ) = Nsz sz n := by
      rw [Sizes.card_Idx]
    have hlam := Step1RegularityGUE_eigenvalue_le hH hev.2 i
    rw [hc] at hlam
    rw [hc, Real.rpow_two]
    set a := Real.exp (-(ouTStar sz τs n) / 2) with ha
    have ha1 : a ≤ 1 := Step1RegularityGUE_exp_le_one hT0
    have hE₀2 : |E₀| ≤ 2 := by linarith [abs_nonneg E₀]
    have h1 : |vGUE sz n τs E₀ ω i| ≤ a * |hH.eigenvalues i| + |E₀| := by
      change |a * hH.eigenvalues i - E₀| ≤ _
      calc |a * hH.eigenvalues i - E₀| ≤ |a * hH.eigenvalues i| + |E₀| := abs_sub _ _
        _ = a * |hH.eigenvalues i| + |E₀| := by rw [abs_mul, abs_of_pos ha0]
    have h2 : a * |hH.eigenvalues i| ≤ Nsz sz n :=
      (mul_le_of_le_one_left (abs_nonneg _) ha1).trans hlam
    nlinarith

/-- **The closeness hypothesis of `FreeConvStability.freeConv_stable_local`** (RBM2D `:964`), on the event,
at every `w` of the strip `|Re w| ≤ κ'/16`, `c₀ t/4 ≤ Im w ≤ 1/2`, `t = 1 - e^{-T}`: the lower edge of the
strip is above the domain edge `N^{-1+τ}` (`hedge`), so the strip stays inside the domain of the event. -/
private theorem Step1RegularityGUE_strip {d : ℕ} (sz : Sizes d) (n : ℕ) {κ τ τs E₀ c₀ C₀ : ℝ}
    {ω : Ω d (sz.L n) (sz.W n)}
    (hκ : 0 < κ) (hE₀ : |E₀| ≤ 2 - κ) (hc₀ : 0 < c₀) (hC₀ : 0 < C₀)
    (hev : Step1LocalEventGUE sz n (κ / 2) τ ω) (hN : 1 ≤ sz.size n)
    (hT : Nsz sz n ^ (-1 + τs) ≤ min κ 1 / 240)
    (hedge : Nsz sz n ^ (-1 + τ) ≤ c₀ / 8 * Nsz sz n ^ (-1 + τs))
    (hrate : Nsz sz n ^ (τ - τs / 8) ≤ Real.sqrt (min 1 (c₀ / 8)) / (2 * C₀))
    {w : ℂ} (hw : |w.re| ≤ min κ 1 / 16)
    (hlow : c₀ * (1 - Real.exp (-(ouTStar sz τs n))) / 4 ≤ w.im) (hw1 : w.im ≤ 1 / 2) :
    ‖mV (vGUE sz n τs E₀ ω) w - (Real.sqrt (Real.exp (-(ouTStar sz τs n))) : ℂ)⁻¹ *
        msc ((Real.sqrt (Real.exp (-(ouTStar sz τs n))) : ℂ)⁻¹ * (w + E₀))‖ ≤
      Nsz sz n ^ (-(3 * τs / 8)) / C₀ := by
  have hNr1 : (1 : ℝ) ≤ Nsz sz n := by exact_mod_cast hN
  have hNr0 : (0 : ℝ) < Nsz sz n := by linarith
  have hκ'0 : 0 < min κ 1 := lt_min hκ one_pos
  have hTpos : 0 < ouTStar sz τs n := Real.rpow_pos_of_pos hNr0 _
  have hT' : ouTStar sz τs n ≤ min κ 1 / 240 := hT
  have hT1 : ouTStar sz τs n ≤ 1 := by
    have : min κ 1 ≤ 1 := min_le_right _ _
    linarith
  have hH := Xmat_isHermitian d (sz.L n) (sz.W n) ω
  rw [Step1RegularityGUE_sqrt_exp]
  have ha0 : 0 < Real.exp (-(ouTStar sz τs n) / 2) := Real.exp_pos _
  have hainv : (Real.exp (-(ouTStar sz τs n) / 2))⁻¹ ≤ 1 + ouTStar sz τs n :=
    Step1RegularityGUE_inv_le hTpos.le hT1
  have hhalf := Step1RegularityGUE_half_le_one_sub_exp hTpos.le hT1
  have hy : c₀ / 8 * ouTStar sz τs n ≤ w.im := by
    have : c₀ / 8 * ouTStar sz τs n ≤ c₀ * (1 - Real.exp (-(ouTStar sz τs n))) / 4 := by
      nlinarith
    exact this.trans hlow
  have hy0 : 0 < c₀ / 8 * ouTStar sz τs n := by positivity
  have hw0 : 0 < w.im := lt_of_lt_of_le hy0 hy
  obtain ⟨hdom, hdomim⟩ := Step1RegularityGUE_domain (N := Nsz sz n) (τ := τ)
    (R := min κ 1 / 16) hκ hE₀ hTpos.le hT' (by linarith) hy0 hedge hw hy hw1
  set c₁ : ℝ := min 1 (c₀ / 8) with hc₁
  have hc₁0 : 0 < c₁ := lt_min one_pos (by positivity)
  have hc₁1 : c₁ ≤ 1 := min_le_left _ _
  have hc₁c : c₁ ≤ c₀ / 8 := min_le_right _ _
  have herrz := gue_err_pow sz n hev hN hdom.1 hdom.2.1 (hdom.2.2.trans (by norm_num)) hc₁0
    (σ := τs)
    (by
      calc c₁ * Nsz sz n ^ (-1 + τs) ≤ c₀ / 8 * ouTStar sz τs n :=
            mul_le_mul_of_nonneg_right hc₁c hTpos.le
        _ ≤ w.im := hy
        _ ≤ _ := hdomim)
  have hdict : mV (vGUE sz n τs E₀ ω) w =
      ((Real.exp (-(ouTStar sz τs n) / 2) : ℝ) : ℂ)⁻¹ * stieltjesN (Xmat d (sz.L n) (sz.W n) ω)
        (((Real.exp (-(ouTStar sz τs n) / 2) : ℝ) : ℂ)⁻¹ * (w + E₀)) :=
    Step1RegularityGUE_mV_affine hH ha0 E₀ hw0
  rw [hdict, ← mul_sub, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg ha0.le]
  have ha2 : (Real.exp (-(ouTStar sz τs n) / 2))⁻¹ ≤ 2 := by linarith [hT', min_le_right κ 1]
  have hsplit : Nsz sz n ^ (τ - τs / 2) =
      Nsz sz n ^ (τ - τs / 8) * Nsz sz n ^ (-(3 * τs / 8)) := by
    rw [← Real.rpow_add hNr0]; congr 1; ring
  have hY0 : 0 ≤ Nsz sz n ^ (-(3 * τs / 8)) := Real.rpow_nonneg hNr0.le _
  have hsc : 0 < Real.sqrt c₁ := Real.sqrt_pos.2 hc₁0
  calc (Real.exp (-(ouTStar sz τs n) / 2))⁻¹ * ‖stieltjesN (Xmat d (sz.L n) (sz.W n) ω)
          (((Real.exp (-(ouTStar sz τs n) / 2) : ℝ) : ℂ)⁻¹ * (w + E₀)) -
        msc (((Real.exp (-(ouTStar sz τs n) / 2) : ℝ) : ℂ)⁻¹ * (w + E₀))‖
      ≤ 2 * (Real.sqrt c₁⁻¹ * Nsz sz n ^ (τ - τs / 2)) :=
        mul_le_mul ha2 herrz (norm_nonneg _) (by norm_num)
    _ = 2 * Real.sqrt c₁⁻¹ * (Nsz sz n ^ (τ - τs / 8) * Nsz sz n ^ (-(3 * τs / 8))) := by
        rw [hsplit]; ring
    _ ≤ 2 * Real.sqrt c₁⁻¹ * ((Real.sqrt c₁ / (2 * C₀)) * Nsz sz n ^ (-(3 * τs / 8))) := by
        gcongr
    _ = Nsz sz n ^ (-(3 * τs / 8)) / C₀ := by
        rw [Real.sqrt_inv]; field_simp

/-- **Deterministic part of the good event** (RBM2D `Step1RegularityGUE_det`, `:1044`): for `0 < τ < τs/8`,
eventually in `n`, every `ω` of the event `Step1LocalEventGUE sz n (κ/2) τ` has `vGUE` `[32]`-regular and a
free-convolution density (witness `freeConvST`) within `N^{-3τs/8}` of `ρ_sc(E₀)`.  All the size conditions
are of the form `N^{-e} ≤ c` with `e > 0`.  No `Admissible`, no `τs ≤ 𝔠𝔡`. -/
private theorem Step1RegularityGUE_det {d : ℕ} (sz : Sizes d)
    (hd : Tendsto (fun n => sz.size n) atTop atTop)
    {κ τ τs E₀ : ℝ} (hκ : 0 < κ) (_hτs0 : 0 < τs) (hτs1 : τs < 1) (hE₀ : |E₀| ≤ 2 - κ)
    (hτ0 : 0 < τ) (hτ : τ < τs / 8) :
    ∀ᶠ n in atTop, ∀ ω : Ω d (sz.L n) (sz.W n),
      Step1LocalEventGUE sz n (κ / 2) τ ω → GUEGoodAt sz n κ τs E₀ ω := by
  obtain ⟨c₀, C₀, hc₀, hC₀, hFC⟩ := FreeConvStability.freeConv_stable_local hκ
  have hNtend : Tendsto (fun n => Nsz sz n) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hd
  have hκ'0 : 0 < min κ 1 := lt_min hκ one_pos
  have hc₁0 : 0 < min 1 (c₀ / 8) := lt_min one_pos (by positivity)
  have hσ0 : 0 < min (τs / 4) ((1 - τs) / 3) := lt_min (by linarith) (by linarith)
  have eg := Step1RegularityGUE_rpow_ev (e := -1 + τs / 4) (c := 1 / 2) (by linarith)
    (by norm_num)
  have eG := Step1RegularityGUE_rpow_ev (e := -(min (τs / 4) ((1 - τs) / 3)))
    (c := min κ 1 / 4) (by linarith) (by positivity)
  have eT := Step1RegularityGUE_rpow_ev (e := -1 + τs) (c := min (min κ 1 / 240) c₀)
    (by linarith) (lt_min (by positivity) hc₀)
  have eerr := Step1RegularityGUE_rpow_ev (e := τ - τs / 8)
    (c := min (min κ 1 / 24) (Real.sqrt (min 1 (c₀ / 8)) / (2 * C₀)))
    (by linarith) (lt_min (by positivity) (by positivity))
  have eedge := Step1RegularityGUE_rpow_ev (e := τ - τs) (c := c₀ / 8)
    (by linarith) (by positivity)
  have eeps := Step1RegularityGUE_rpow_ev (e := -(3 * τs / 8)) (c := c₀ * C₀)
    (by linarith) (by positivity)
  filter_upwards [hNtend.eventually eg, hNtend.eventually eG, hNtend.eventually eT,
    hNtend.eventually eerr, hNtend.eventually eedge, hNtend.eventually eeps,
    hNtend.eventually_ge_atTop 2] with n hg hG hT herr hedge heps hN2
  intro ω hev
  have hNr1 : (1 : ℝ) ≤ Nsz sz n := by linarith
  have hNr0 : (0 : ℝ) < Nsz sz n := by linarith
  have hN2' : 2 ≤ sz.size n := by exact_mod_cast hN2
  have hN1 : 1 ≤ sz.size n := by omega
  have hT1 : Nsz sz n ^ (-1 + τs) ≤ min κ 1 / 240 := hT.trans (min_le_left _ _)
  have hT2 : Nsz sz n ^ (-1 + τs) ≤ c₀ := hT.trans (min_le_right _ _)
  have herr1 : Nsz sz n ^ (τ - τs / 8) ≤ min κ 1 / 24 :=
    herr.trans (min_le_left _ _)
  have herr2 : Nsz sz n ^ (τ - τs / 8) ≤ Real.sqrt (min 1 (c₀ / 8)) / (2 * C₀) :=
    herr.trans (min_le_right _ _)
  unfold GUEGoodAt
  refine ⟨Step1RegularityGUE_regular sz n hκ hE₀ (by linarith) hev hN2' hg hG hT1 herr1, ?_⟩
  -- the free-convolution part
  have hTpos : 0 < ouTStar sz τs n := Real.rpow_pos_of_pos hNr0 _
  have ht : 0 < 1 - Real.exp (-(ouTStar sz τs n)) := Step1RegularityGUE_one_sub_exp_pos hTpos
  have htc : 1 - Real.exp (-(ouTStar sz τs n)) ≤ c₀ :=
    (Step1RegularityGUE_one_sub_exp_le _).trans hT2
  have hε0 : 0 ≤ Nsz sz n ^ (-(3 * τs / 8)) / C₀ := by positivity
  have hεc : Nsz sz n ^ (-(3 * τs / 8)) / C₀ ≤ c₀ := by
    rw [div_le_iff₀ hC₀]; exact heps
  have hedge' : Nsz sz n ^ (-1 + τ) ≤ c₀ / 8 * Nsz sz n ^ (-1 + τs) := by
    have hsplit : Nsz sz n ^ (-1 + τ) = Nsz sz n ^ (τ - τs) * Nsz sz n ^ (-1 + τs) := by
      rw [← Real.rpow_add hNr0]; congr 1; ring
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right hedge (Real.rpow_nonneg hNr0.le _)
  obtain ⟨ρ, hρ1, hρ2, -⟩ := hFC (vGUE sz n τs E₀ ω) (Real.exp (-(ouTStar sz τs n)))
    (1 - Real.exp (-(ouTStar sz τs n))) E₀ (Nsz sz n ^ (-(3 * τs / 8)) / C₀)
    ht htc (by ring) hE₀ hε0 hεc
    (fun w hw hlow hw1 => Step1RegularityGUE_strip sz n hκ hE₀ hc₀ hC₀ hev hN1 hT1
      hedge' herr2 hw hlow hw1)
  refine ⟨freeConvST (vGUE sz n τs E₀ ω) (1 - Real.exp (-(ouTStar sz τs n))),
    isFreeConv51_freeConvST _ ht.le, ρ, hρ1, ?_⟩
  calc |ρ - rhoSC E₀| ≤ C₀ * (Nsz sz n ^ (-(3 * τs / 8)) / C₀) := hρ2
    _ = Nsz sz n ^ (-(3 * τs / 8)) := by field_simp

/-- **Target 3** `guedetHalf` (S7b proved; RBM2D `:1109`). -/
theorem guedetHalf : UNGUEDetHalf := by
  intro d hd3 sz hd κ τs E₀ hκ hτs0 hτs1 hE₀ τ hτ0 hτ
  exact Step1RegularityGUE_det sz hd hκ hτs0 hτs1 hE₀ hτ0 hτ

/-! ## 5. The composition (RBM2D `:123`, `:1116`) -/

/-- **Target 4a** `gueGoodHighProb_of` (RBM2D `:123`): `S7 = S7a + S7b` at `τ = τs/16`:
`measure_mono` from `{¬Good} ⊆ {¬Event}`. -/
theorem gueGoodHighProb_of : UNGUELocalEventHighProb → UNGUEDetHalf → UNGUEGoodHighProb := by
  intro h1 h2 hG d hd3 sz hd κ τs E₀ D hκ hτs0 hτs1 hE₀ hD
  have hev := h1 hG d hd3 sz hd (κ / 2) (τs / 16) D (by positivity) (by positivity) hD
  have hdet := h2 d hd3 sz hd κ τs E₀ hκ hτs0 hτs1 hE₀ (τs / 16) (by positivity) (by linarith)
  filter_upwards [hev, hdet] with n hn hdn
  refine le_trans (measure_mono ?_) hn
  intro ω hω hevω
  exact hω (hdn ω hevω)

/-- **Target 4b** `gueGoodHighProb` (S7 proved; RBM2D `:1116`): the input of UN-14. -/
theorem gueGoodHighProb : UNGUEGoodHighProb :=
  gueGoodHighProb_of guelocalEventHighProb guedetHalf

/-! ## 6. Compiled nonempty instances (target 5; DECISIONS §56)

`d = 3`, `sz0` (`N_n = 2097152 (n+1)^18`), `κ = 1`, `τs = 1/60`, `E₀ = 1`, `τ = τs/16 = 1/960`.  The one
kept hypothesis is `UNGUELocal` (another gate's pin; owed UN-09/UN-10); every deterministic hypothesis is
discharged.  The conclusions are eventual in `n` (the `ln N` thresholds are in the report). -/

namespace Step1RegularityGUEInst

open RBM.Gauss.SizesInst

/-- `size → ∞` in `ℕ` at `sz0` (from `sz0_tendsto`). -/
theorem inst_sz0_size_tendsto : Tendsto (fun n => sz0.size n) atTop atTop :=
  tendsto_natCast_atTop_iff.1 sz0_tendsto

/-- S7a at `κ = 1/2`, `τ = 1/960`, `D = 1`. -/
theorem inst_guelocalEvent_sz0 :
    UNGUELocal → ∀ᶠ n in atTop,
      gueP 3 (sz0.L n) (sz0.W n) {ω | ¬ Step1LocalEventGUE sz0 n (1 / 2) (1 / 960) ω} ≤
        ENNReal.ofReal (Nsz sz0 n ^ (-(1 : ℝ))) :=
  fun h => guelocalEventHighProb h 3 le_rfl sz0 inst_sz0_size_tendsto (1 / 2) (1 / 960) 1
    (by norm_num) (by norm_num) one_pos

/-- The premise of S7b is eventually satisfiable: the complement of the event has measure `≤ N^{-1} < 1`. -/
theorem inst_event_nonempty_sz0 :
    UNGUELocal → ∀ᶠ n in atTop, ∃ ω : Ω 3 (sz0.L n) (sz0.W n),
      Step1LocalEventGUE sz0 n (1 / 2) (1 / 960) ω := by
  intro h
  have h1 := inst_guelocalEvent_sz0 h
  filter_upwards [h1, sz0_tendsto.eventually_ge_atTop 2] with n hn hN2
  by_contra hcon
  push Not at hcon
  have huniv : {ω : Ω 3 (sz0.L n) (sz0.W n) | ¬ Step1LocalEventGUE sz0 n (1 / 2) (1 / 960) ω} =
      Set.univ := Set.eq_univ_of_forall fun ω => hcon ω
  rw [huniv, measure_univ] at hn
  have hNpos : (0 : ℝ) < Nsz sz0 n := by linarith
  have hlt : Nsz sz0 n ^ (-(1 : ℝ)) < 1 := by
    rw [Real.rpow_neg_one]
    exact inv_lt_one_of_one_lt₀ (by linarith)
  exact absurd hn (not_le.2 (ENNReal.ofReal_lt_one.2 hlt))

/-- S7b, every hypothesis discharged. -/
theorem inst_guedetHalf_sz0 :
    ∀ᶠ n in atTop, ∀ ω : Ω 3 (sz0.L n) (sz0.W n),
      Step1LocalEventGUE sz0 n (1 / 2) (1 / 960) ω → GUEGoodAt sz0 n 1 (1 / 60) 1 ω :=
  guedetHalf 3 le_rfl sz0 inst_sz0_size_tendsto 1 (1 / 60) 1 one_pos (by norm_num) (by norm_num)
    (by norm_num) (1 / 960) (by norm_num) (by norm_num)

/-- S7 at `D = 2` (`= k + 1` at `k = 1`, the call UN-14 makes). -/
theorem inst_gueGood_sz0 :
    UNGUELocal → ∀ᶠ n in atTop,
      gueP 3 (sz0.L n) (sz0.W n) {ω | ¬ GUEGoodAt sz0 n 1 (1 / 60) 1 ω} ≤
        ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) :=
  fun h => gueGoodHighProb h 3 le_rfl sz0 inst_sz0_size_tendsto 1 (1 / 60) 1 2
    one_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Target 4a at the instance: `gueGoodHighProb_of` applied to the proved S7a and S7b (`D = 2`). -/
theorem inst_gueGoodHighProb_of_sz0 :
    UNGUELocal → ∀ᶠ n in atTop,
      gueP 3 (sz0.L n) (sz0.W n) {ω | ¬ GUEGoodAt sz0 n 1 (1 / 60) 1 ω} ≤
        ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) :=
  fun h => gueGoodHighProb_of guelocalEventHighProb guedetHalf h 3 le_rfl sz0 inst_sz0_size_tendsto
    1 (1 / 60) 1 2 one_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Nondegeneracy of the data: the matrices are `2097152 × 2097152` at `n = 0` (`d = 3`, `L = 4`,
`W = 32`). -/
theorem inst_size_zero_sz0 : Nsz sz0 0 = 2097152 ∧ sz0.L 0 = 4 ∧ sz0.W 0 = 32 := by
  have h := sz0_values
  exact ⟨by simp only [Nsz]; exact_mod_cast h.2.2.1, h.1, h.2.1⟩

/-- The good event is eventually nonempty (nondegeneracy). -/
theorem inst_gueGood_nonempty_sz0 :
    UNGUELocal → ∀ᶠ n in atTop, ∃ ω : Ω 3 (sz0.L n) (sz0.W n), GUEGoodAt sz0 n 1 (1 / 60) 1 ω := by
  intro h
  have h1 := inst_gueGood_sz0 h
  filter_upwards [h1, sz0_tendsto.eventually_ge_atTop 2] with n hn hN2
  by_contra hcon
  push Not at hcon
  have huniv : {ω : Ω 3 (sz0.L n) (sz0.W n) | ¬ GUEGoodAt sz0 n 1 (1 / 60) 1 ω} = Set.univ :=
    Set.eq_univ_of_forall fun ω => hcon ω
  rw [huniv, measure_univ] at hn
  have hNpos : (0 : ℝ) < Nsz sz0 n := by linarith
  have hlt : Nsz sz0 n ^ (-(2 : ℝ)) < 1 := by
    rw [Real.rpow_neg hNpos.le, Real.rpow_two]
    exact inv_lt_one_of_one_lt₀ (by nlinarith)
  exact absurd hn (not_le.2 (ENNReal.ofReal_lt_one.2 hlt))

/-- Targets 1a-1c at the instance exponents `τs = 1/60`, `τ = 1/960`. -/
theorem inst_exponents_sz0 :
    (1 / 960 : ℝ) ≤ (1 / 60 : ℝ) / 4 ∧ (1 / 960 : ℝ) - (1 / 60 : ℝ) / 8 < 0 ∧
      (1 / 960 : ℝ) - (1 / 60 : ℝ) / 2 < -(3 * (1 / 60 : ℝ) / 8) ∧ (1 / 960 : ℝ) < 1 / 60 ∧
    (¬ ((1 / 480 : ℝ) - (1 / 60 : ℝ) / 8 < 0) ∧ ¬ ((1 / 480 : ℝ) - (1 / 60 : ℝ) / 2 < -(3 * (1 / 60 : ℝ) / 8))) ∧
    0 < min ((1 / 60 : ℝ) / 4) ((1 - 1 / 60) / 3) :=
  ⟨(gue_window (τs := 1 / 60) (τ := 1 / 960) (by norm_num) (by norm_num)).1,
    (gue_window (τs := 1 / 60) (τ := 1 / 960) (by norm_num) (by norm_num)).2.1,
    (gue_window (τs := 1 / 60) (τ := 1 / 960) (by norm_num) (by norm_num)).2.2.1,
    (gue_window (τs := 1 / 60) (τ := 1 / 960) (by norm_num) (by norm_num)).2.2.2,
    gue_window_sharp (τs := 1 / 60) (τ := 1 / 480) (by norm_num),
    (gue_l32_exponents (τs := 1 / 60) (by norm_num) (by norm_num)).1⟩

/-- `gue_err_pow` at the instance: on the event at `(κ, τ) = (1/2, 1/960)`, at `z = i`, `c = 1`, `σ = 1/60`. -/
theorem inst_gue_err_pow_sz0 :
    UNGUELocal → ∀ᶠ n in atTop, ∃ ω : Ω 3 (sz0.L n) (sz0.W n),
      ‖stieltjesN (Xmat 3 (sz0.L n) (sz0.W n) ω) ⟨0, 1⟩ - msc ⟨0, 1⟩‖ ≤
        Real.sqrt (1 : ℝ)⁻¹ * Nsz sz0 n ^ ((1 / 960 : ℝ) - (1 / 60 : ℝ) / 2) := by
  intro h
  filter_upwards [inst_event_nonempty_sz0 h, sz0_tendsto.eventually_ge_atTop 1] with n ⟨ω, hω⟩ hN1
  have hN1' : 1 ≤ sz0.size n := by exact_mod_cast hN1
  refine ⟨ω, gue_err_pow sz0 n hω hN1' (z := ⟨0, 1⟩) (by norm_num) ?_ (by norm_num) (c := 1)
    (σ := 1 / 60) one_pos ?_⟩
  · exact (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)).trans (by norm_num)
  · rw [one_mul]
    exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)

end Step1RegularityGUEInst

end RBM.Univ

end
