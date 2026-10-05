/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Path.DifREP1
import RBM3D.Induction.NQGood1
import RBM3D.Induction.QVN
import RBM3D.Induction.AzumaProxyN2
import RBM3D.Path.Azuma
import RBM3D.Path.Markov
import RBM3D.Induction.OptL2b

/-!
# `STGridRepN`, part 2: the plain martingale tail by a maximal Azuma bound (`d ≥ 3`)

Ticket T2180 (ST2-13a, stochastic layer ST-2).  Paper: arXiv:2507.20274, `3_5`: `(aaswtghh)`
(`3_5:220`, `lem:DIfREP`: the Burkholder-Davis-Gundy step of `[YY_25]` Lemma 5.5), replaced by an
Azuma-Hoeffding bound on the grid with a random predictable proxy (DECISIONS §7, paper-delta D90 =
T2039h).  The pin is `GridRepTailNAt d m` of the merged `Path/DifREP1.lean` (T2168, `3df1812`,
clause (iii) of `STGridRepNAt`).  RBM1D and RBM2D have no counterpart of the tail (no random-proxy
Azuma bound, no exponential supermartingale); the file copies only the private helpers listed below.

## Main results (namespace `RBM.Ind`)

* §1 **`azumaRandProxy_max`** (target 1, model-free): the maximal Azuma bound with a random
  predictable proxy, `μ(∃ k ≤ K, x ≤ Σ_{j<k} 1_{G_j} ζ_j) ≤ e^{-x²/(2V)}`, uniformly in `K`.  The
  exponential supermartingale `X_k = exp (r S_k - r²/2 Σ_{j<k} 1_{G_j} v_j)` has `∫⁻ X_k ≤ 1` (a
  `lintegral` step lemma with an `m`-measurable nonnegative factor, so no integrability of the
  product is needed); the running maximum is handled by a second switch
  `G'_j = G_j ∩ {S_i < x ∀ i ≤ j}`, not by optional stopping; then Markov at `r = x/V`.
  §1b: the two-sided form, **`difRep2_peel`** (Amend 2 (ii): the peeling of step 3(c) for any
  adapted complex increments with a predictable proxy) and **`difRep2_peel_N`** (its form at
  `δ = N^{-D}`, `ρ = N^{ε'}`, `c = m`, the bound `(L + 1) · 4 e^{-N^{2ε'}/(64 m)}` of the amend);
  §1c: Doob's `L²` tail for martingale differences.
* §2-§5 copies, with the prefix `difRepTail_`, of the private helpers of the merged
  `Induction/AzumaProxyN.lean:122-232` (RBM3D `43ab861`, T2159; ports of RBM2D
  `Induction/AzumaProxyN.lean:200-260` at `c9a24cf`) and of `Path/Markov.lean:263-305, 319-321,
  393-435, 572-604` (RBM3D `58bedae`, T2021; ports of RBM2D `Path/Markov.lean:417-620` at
  `c9a24cf`).  The conditional exponential moment of a frozen linear functional keeps the random
  variance `linTrVar n (A ω)` (`difRepTail_condExp_exp`) instead of the deterministic bound of
  `condMGF_le`.
* §6 the crude bounds of step 3(a) (Amend 2 (i)): **`difRep2_norm_STeeM_le`**,
  **`difRep2_norm_STeeM_le_N`** (`‖(𝓔⊗𝓔)_u(M)‖ ≤ m N (16 N)^{2m+2}`), **`difRep2_eeShiftErrN_le`**,
  **`difRep2_eeShift_sum_le`**.
* §7 **`difRepTail_condMGF_Z`** (target 2): the conditional mgf of `Re`, `Im` of `Σ_b κ_b Z_{j,b}`
  with the random proxy `Δ k Re Σ κ κ̄ (𝓔⊗𝓔)_{u_{j+1}}(H_j)`, for general weights `κ`.
* §8-§11 the `Z` part (through `difRep2_peel`), the `Y` part (Doob), the tail at one size index
  (`difRepTail_core`) and the asymptotics of the budgets.
* §12 **`gridRepTailN_holds`** (target 3): `∀ d m, 2 ≤ m → GridRepTailNAt d m`, with
  `CK = 2m + 2D + 16`.  §13 **`stGridMart_holds`**, **`stGridMartAt_holds`** (target 4):
  `STGridMart d` and `STGridMartAt d 11` for `3 ≤ d`.
* §14 compiled nonempty instances at `d = 3` (namespace `RBM.Ind.DifREP2Inst`).

`3 ≤ d` enters only in target 4 (`stGridMart_of_tail`, `gridRepRemN_holds`); targets 1-3 and the
public pieces of Amend 2 hold for every `d`.  Every unpinned helper is `private` with the prefix
`difRepTail_`; the pieces of Amend 2 carry the prefix `difRep2_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path
  RBM.Gauss.LinearForm
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-! ## 1. Target 1: the maximal Azuma bound with a random predictable proxy -/

/-- Step lemma: pulling an `m`-measurable nonnegative factor out of a `lintegral`. -/
private theorem difRepTail_lintegral_mul_le {Ω' : Type*} {m m0 : MeasurableSpace Ω'} (hm : m ≤ m0)
    {μ : Measure Ω'} [IsFiniteMeasure μ] {X Y : Ω' → ℝ}
    (hX : StronglyMeasurable[m] X) (hX0 : ∀ ω, 0 ≤ X ω) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hY : Integrable Y μ) (hc : μ[Y | m] ≤ᵐ[μ] fun _ => 1) :
    ∫⁻ ω, ENNReal.ofReal (X ω * Y ω) ∂μ ≤ ∫⁻ ω, ENNReal.ofReal (X ω) ∂μ := by
  have : SigmaFinite (μ.trim hm) := inferInstance
  set Xn : ℕ → Ω' → ℝ := fun n ω => min (X ω) n with hXn
  have hXnm' : ∀ n, Measurable[m] (Xn n) := fun n => hX.measurable.min measurable_const
  have hXnm : ∀ n, StronglyMeasurable[m] (Xn n) := fun n => (hXnm' n).stronglyMeasurable
  have hXn0 : ∀ n ω, 0 ≤ Xn n ω := fun n ω => le_min (hX0 ω) (Nat.cast_nonneg n)
  have hXnle : ∀ n ω, Xn n ω ≤ X ω := fun n ω => min_le_left _ _
  have hXnle' : ∀ n ω, Xn n ω ≤ n := fun n ω => min_le_right _ _
  have hXnmeas : ∀ n, Measurable (Xn n) := fun n => (hXnm' n).mono hm le_rfl
  have hXnint : ∀ n, Integrable (Xn n) μ := fun n =>
    Integrable.of_bound (hXnmeas n).aestronglyMeasurable n
      (ae_of_all _ fun ω => by
        rw [Real.norm_of_nonneg (hXn0 n ω)]; exact hXnle' n ω)
  have hXnY : ∀ n, Integrable (Xn n * Y) μ := fun n => by
    have := hY.bdd_mul (c := n) (hXnmeas n).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_of_nonneg (hXn0 n ω)]; exact hXnle' n ω)
    exact this
  have hstep : ∀ n, ∫⁻ ω, ENNReal.ofReal (Xn n ω * Y ω) ∂μ ≤ ∫⁻ ω, ENNReal.ofReal (X ω) ∂μ := by
    intro n
    have h1 : ∫ ω, (Xn n * Y) ω ∂μ ≤ ∫ ω, Xn n ω ∂μ := by
      rw [← integral_condExp hm (f := Xn n * Y)]
      have hcm := condExp_mul_of_stronglyMeasurable_left (hXnm n) (hXnY n) hY
      have hint1 : Integrable (Xn n * μ[Y | m]) μ :=
        (integrable_condExp (f := Xn n * Y) (m := m)).congr hcm
      refine (integral_congr_ae hcm).trans_le ?_
      refine integral_mono_ae hint1 (hXnint n) ?_
      filter_upwards [hc] with ω hω
      simp only [Pi.mul_apply]
      calc Xn n ω * μ[Y | m] ω ≤ Xn n ω * 1 := mul_le_mul_of_nonneg_left hω (hXn0 n ω)
        _ = Xn n ω := mul_one _
    have h2 : ENNReal.ofReal (∫ ω, (Xn n * Y) ω ∂μ) = ∫⁻ ω, ENNReal.ofReal (Xn n ω * Y ω) ∂μ :=
      ofReal_integral_eq_lintegral_ofReal (hXnY n) (ae_of_all _ fun ω => mul_nonneg (hXn0 n ω) (hY0 ω))
    have h3 : ENNReal.ofReal (∫ ω, Xn n ω ∂μ) = ∫⁻ ω, ENNReal.ofReal (Xn n ω) ∂μ :=
      ofReal_integral_eq_lintegral_ofReal (hXnint n) (ae_of_all _ fun ω => hXn0 n ω)
    rw [← h2]
    calc ENNReal.ofReal (∫ ω, (Xn n * Y) ω ∂μ) ≤ ENNReal.ofReal (∫ ω, Xn n ω ∂μ) :=
          ENNReal.ofReal_le_ofReal h1
      _ = ∫⁻ ω, ENNReal.ofReal (Xn n ω) ∂μ := h3
      _ ≤ ∫⁻ ω, ENNReal.ofReal (X ω) ∂μ :=
          lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hXnle n ω)
  have hsup : (fun ω => ENNReal.ofReal (X ω * Y ω)) =
      fun ω => ⨆ n : ℕ, ENNReal.ofReal (Xn n ω * Y ω) := by
    funext ω
    apply le_antisymm
    · refine le_iSup_of_le ⌈X ω⌉₊ ?_
      have : Xn ⌈X ω⌉₊ ω = X ω := min_eq_left (Nat.le_ceil _)
      rw [this]
    · refine iSup_le fun n => ENNReal.ofReal_le_ofReal ?_
      exact mul_le_mul_of_nonneg_right (hXnle n ω) (hY0 ω)
  rw [hsup, lintegral_iSup']
  · exact iSup_le hstep
  · intro n
    exact (ENNReal.measurable_ofReal.comp_aemeasurable
      ((hXnmeas n).aemeasurable.mul hY.aestronglyMeasurable.aemeasurable))
  · exact ae_of_all _ fun ω n n' hnn' => ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (min_le_min_left _ (Nat.cast_le.mpr hnn')) (hY0 ω))


/-- One step of the exponential supermartingale: with the switch `G ∈ m` and the `m`-measurable proxy
`v ≥ 0`, `Y = exp (r 1_G ζ - r²/2 1_G v)` is integrable with `𝔼[Y | m] ≤ 1`. -/
private theorem difRepTail_step_cond {Ω' : Type*} {m m0 : MeasurableSpace Ω'} (hm : m ≤ m0)
    {μ : Measure Ω'} [IsFiniteMeasure μ] {ζ v : Ω' → ℝ} {G : Set Ω'} (hG : MeasurableSet[m] G)
    (hv : StronglyMeasurable[m] v) (hv0 : ∀ ω, 0 ≤ v ω) (r : ℝ)
    (hint : Integrable (fun ω => Real.exp (r * ζ ω)) μ)
    (hmgf : μ[fun ω => Real.exp (r * ζ ω) | m] ≤ᵐ[μ] fun ω => Real.exp (r ^ 2 * v ω / 2)) :
    Integrable (fun ω => Real.exp (r * G.indicator ζ ω - r ^ 2 / 2 * G.indicator v ω)) μ ∧
      μ[fun ω => Real.exp (r * G.indicator ζ ω - r ^ 2 / 2 * G.indicator v ω) | m]
        ≤ᵐ[μ] fun _ => 1 := by
  have : SigmaFinite (μ.trim hm) := inferInstance
  set e : Ω' → ℝ := fun ω => Real.exp (r * ζ ω) with he
  set b : Ω' → ℝ := G.indicator (fun ω => Real.exp ((-(r ^ 2 / 2)) * v ω)) with hb
  set a : Ω' → ℝ := fun ω => 1 - G.indicator (fun _ => (1 : ℝ)) ω with ha
  have hY : (fun ω => Real.exp (r * G.indicator ζ ω - r ^ 2 / 2 * G.indicator v ω)) = a + b * e := by
    funext ω
    by_cases h : ω ∈ G
    · simp only [ha, hb, he, Set.indicator_of_mem h, Pi.add_apply, Pi.mul_apply]
      rw [← Real.exp_add]
      simp only [sub_self, zero_add]
      congr 1
      ring
    · simp [ha, hb, he, Set.indicator_of_notMem h]
  have hbm : StronglyMeasurable[m] b :=
    (Real.continuous_exp.comp_stronglyMeasurable (hv.const_mul (-(r ^ 2 / 2)))).indicator hG
  have hbm' : StronglyMeasurable b := hbm.mono hm
  have hb0 : ∀ ω, 0 ≤ b ω := fun ω => by
    by_cases h : ω ∈ G
    · simp only [hb, Set.indicator_of_mem h]; exact (Real.exp_pos _).le
    · simp [hb, Set.indicator_of_notMem h]
  have hb1 : ∀ ω, b ω ≤ 1 := fun ω => by
    by_cases h : ω ∈ G
    · simp only [hb, Set.indicator_of_mem h]
      rw [Real.exp_le_one_iff]
      have := hv0 ω
      nlinarith [sq_nonneg r, mul_nonneg (sq_nonneg r) this]
    · simp [hb, Set.indicator_of_notMem h]
  have hbe : Integrable (b * e) μ := by
    have := hint.bdd_mul (f := b) (c := 1) hbm'.aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_of_nonneg (hb0 ω)]; exact hb1 ω)
    exact this
  have ham : StronglyMeasurable[m] a :=
    stronglyMeasurable_const.sub (stronglyMeasurable_const.indicator hG)
  have hai : Integrable a μ := by
    refine Integrable.of_bound (ham.mono hm).aestronglyMeasurable 1 (ae_of_all _ fun ω => ?_)
    by_cases h : ω ∈ G
    · simp [ha, Set.indicator_of_mem h]
    · simp [ha, Set.indicator_of_notMem h]
  rw [hY]
  refine ⟨hai.add hbe, ?_⟩
  have h1 := condExp_add hai hbe m
  have h2 : μ[a | m] = a := condExp_of_stronglyMeasurable hm ham hai
  have h3 := condExp_mul_of_stronglyMeasurable_left hbm hbe hint
  filter_upwards [h1, h3, hmgf] with ω hω1 hω3 hω4
  rw [hω1]
  simp only [Pi.add_apply, h2]
  rw [hω3]
  simp only [Pi.mul_apply]
  by_cases h : ω ∈ G
  · have : b ω * μ[e | m] ω ≤ b ω * Real.exp (r ^ 2 * v ω / 2) :=
      mul_le_mul_of_nonneg_left hω4 (hb0 ω)
    have h5 : b ω * Real.exp (r ^ 2 * v ω / 2) = 1 := by
      simp only [hb, Set.indicator_of_mem h]
      rw [← Real.exp_add]
      simp only [Real.exp_eq_one_iff]
      ring
    have h6 : a ω = 0 := by simp [ha, Set.indicator_of_mem h]
    rw [h6]; linarith
  · have h5 : b ω = 0 := by simp [hb, Set.indicator_of_notMem h]
    have h6 : a ω = 1 := by simp [ha, Set.indicator_of_notMem h]
    rw [h5, h6]; simp

/-- Strong measurability of the switched partial sums `Σ_{j<k} 1_{G_j} ζ_j` and `Σ_{j<k} 1_{G_j} v_j`
with respect to `ℱ k`, for `k ≤ K`. -/
private theorem difRepTail_sums_sm {Ω' : Type} {mΩ' : MeasurableSpace Ω'} (ℱ : Filtration ℕ mΩ')
    (ζ v : ℕ → Ω' → ℝ) (G : ℕ → Set Ω') (K : ℕ)
    (hζ : ∀ j < K, StronglyMeasurable[ℱ (j + 1)] (ζ j))
    (hv : ∀ j < K, StronglyMeasurable[ℱ j] (v j))
    (hG : ∀ j < K, MeasurableSet[ℱ j] (G j)) :
    ∀ k ≤ K, StronglyMeasurable[ℱ k] (fun ω => ∑ j ∈ Finset.range k, (G j).indicator (ζ j) ω) ∧
      StronglyMeasurable[ℱ k] (fun ω => ∑ j ∈ Finset.range k, (G j).indicator (v j) ω) := by
  intro k hkK
  refine ⟨?_, ?_⟩
  · refine Finset.stronglyMeasurable_fun_sum _ fun j hj => ?_
    have hj' : j < k := Finset.mem_range.1 hj
    exact ((hζ j (lt_of_lt_of_le hj' hkK)).mono (ℱ.mono (Nat.succ_le_of_lt hj'))).indicator
      (ℱ.mono hj'.le _ (hG j (lt_of_lt_of_le hj' hkK)))
  · refine Finset.stronglyMeasurable_fun_sum _ fun j hj => ?_
    have hj' : j < k := Finset.mem_range.1 hj
    exact ((hv j (lt_of_lt_of_le hj' hkK)).mono (ℱ.mono hj'.le)).indicator
      (ℱ.mono hj'.le _ (hG j (lt_of_lt_of_le hj' hkK)))

/-- The partial exponential martingale is `ℱ k`-strongly measurable. -/
private theorem difRepTail_X_sm {Ω' : Type} {mΩ' : MeasurableSpace Ω'} (ℱ : Filtration ℕ mΩ')
    (ζ v : ℕ → Ω' → ℝ) (G : ℕ → Set Ω') (K : ℕ)
    (hζ : ∀ j < K, StronglyMeasurable[ℱ (j + 1)] (ζ j))
    (hv : ∀ j < K, StronglyMeasurable[ℱ j] (v j))
    (hG : ∀ j < K, MeasurableSet[ℱ j] (G j)) (r : ℝ) :
    ∀ k ≤ K, StronglyMeasurable[ℱ k] (fun ω => Real.exp (r * ∑ j ∈ Finset.range k,
        (G j).indicator (ζ j) ω - r ^ 2 / 2 * ∑ j ∈ Finset.range k, (G j).indicator (v j) ω)) := by
  intro k hk
  obtain ⟨h1, h2⟩ := difRepTail_sums_sm ℱ ζ v G K hζ hv hG k hk
  exact Real.continuous_exp.comp_stronglyMeasurable ((h1.const_mul r).sub (h2.const_mul (r ^ 2 / 2)))

/-- The exponential supermartingale `X_k = exp (r S_k - r²/2 W_k)` has `∫⁻ X_k ≤ 1` for `k ≤ K`. -/
private theorem difRepTail_lintegral_X_le {Ω' : Type} {mΩ' : MeasurableSpace Ω'} (μ : Measure Ω')
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ') (ζ v : ℕ → Ω' → ℝ) (G : ℕ → Set Ω') (K : ℕ)
    (hζ : ∀ j < K, StronglyMeasurable[ℱ (j + 1)] (ζ j))
    (hv : ∀ j < K, StronglyMeasurable[ℱ j] (v j))
    (hG : ∀ j < K, MeasurableSet[ℱ j] (G j)) (hv0 : ∀ j < K, ∀ ω, 0 ≤ v j ω)
    (hint : ∀ j < K, ∀ r : ℝ, Integrable (fun ω => Real.exp (r * ζ j ω)) μ)
    (hmgf : ∀ j < K, ∀ r : ℝ, μ[fun ω => Real.exp (r * ζ j ω) | ℱ j] ≤ᵐ[μ]
      fun ω => Real.exp (r ^ 2 * v j ω / 2)) (r : ℝ) :
    ∀ k ≤ K, ∫⁻ ω, ENNReal.ofReal (Real.exp (r * ∑ j ∈ Finset.range k, (G j).indicator (ζ j) ω
        - r ^ 2 / 2 * ∑ j ∈ Finset.range k, (G j).indicator (v j) ω)) ∂μ ≤ 1 := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hkK : k < K := hk
    have ih' := ih hkK.le
    have hXm := difRepTail_X_sm ℱ ζ v G K hζ hv hG r k hkK.le
    obtain ⟨hYint, hYcond⟩ := difRepTail_step_cond (ℱ.le k) (hG k hkK) (hv k hkK) (hv0 k hkK) r
      (hint k hkK r) (hmgf k hkK r)
    have hmul := difRepTail_lintegral_mul_le (ℱ.le k) hXm (fun ω => (Real.exp_pos _).le)
      (fun ω => (Real.exp_pos _).le) hYint hYcond
    have heq : (fun ω => ENNReal.ofReal (Real.exp (r * ∑ j ∈ Finset.range (k + 1), (G j).indicator (ζ j) ω
        - r ^ 2 / 2 * ∑ j ∈ Finset.range (k + 1), (G j).indicator (v j) ω))) =
        fun ω => ENNReal.ofReal (Real.exp (r * ∑ j ∈ Finset.range k, (G j).indicator (ζ j) ω
          - r ^ 2 / 2 * ∑ j ∈ Finset.range k, (G j).indicator (v j) ω) *
          Real.exp (r * (G k).indicator (ζ k) ω - r ^ 2 / 2 * (G k).indicator (v k) ω)) := by
      funext ω
      rw [← Real.exp_add, Finset.sum_range_succ, Finset.sum_range_succ]
      congr 2
      ring
    rw [heq]
    exact hmul.trans ih'

/-- **Target 1, `azumaRandProxy_max`** (model-free): the maximal Azuma bound with a random predictable
proxy.  Increments `ζ_j` (`ℱ_{j+1}`-measurable) with `𝔼[e^{r ζ_j} | ℱ_j] ≤ e^{r² v_j / 2}` for an
`ℱ_j`-measurable proxy `0 ≤ v_j ≤ B`, switched on by `ℱ_j`-measurable sets `G_j`; if the switched
proxy sums to at most `V` on every path, the running maximum of the switched sum exceeds `x` with
probability at most `e^{-x²/(2V)}`, uniformly in the horizon `K`. -/
theorem azumaRandProxy_max :
    ∀ {Ω' : Type} {mΩ' : MeasurableSpace Ω'} (μ : Measure Ω') [IsProbabilityMeasure μ]
      (ℱ : Filtration ℕ mΩ') (ζ v : ℕ → Ω' → ℝ) (G : ℕ → Set Ω') (K : ℕ) (B V x : ℝ),
      (∀ j < K, StronglyMeasurable[ℱ (j + 1)] (ζ j)) →
      (∀ j < K, StronglyMeasurable[ℱ j] (v j)) →
      (∀ j < K, MeasurableSet[ℱ j] (G j)) →
      (∀ j < K, ∀ ω, 0 ≤ v j ω ∧ v j ω ≤ B) →
      (∀ j < K, ∀ r : ℝ, Integrable (fun ω => Real.exp (r * ζ j ω)) μ) →
      (∀ j < K, ∀ r : ℝ,
        μ[fun ω => Real.exp (r * ζ j ω) | ℱ j] ≤ᵐ[μ] fun ω => Real.exp (r ^ 2 * v j ω / 2)) →
      (∀ ω, ∑ j ∈ Finset.range K, (G j).indicator (v j) ω ≤ V) → 0 < V → 0 ≤ x →
      μ.real {ω | ∃ k, k ≤ K ∧ x ≤ ∑ j ∈ Finset.range k, (G j).indicator (ζ j) ω} ≤
        Real.exp (-x ^ 2 / (2 * V)) := by
  intro Ω' mΩ' μ _ ℱ ζ v G K B V x hζ hv hG hvB hint hmgf hsum hV hx
  have hv0 : ∀ j < K, ∀ ω, 0 ≤ v j ω := fun j hj ω => (hvB j hj ω).1
  rcases hx.eq_or_lt with hx0 | hxpos
  · rw [← hx0]
    simp only [neg_zero, zero_pow two_ne_zero, zero_div, Real.exp_zero]
    exact measureReal_le_one
  set S : ℕ → Ω' → ℝ := fun i ω => ∑ l ∈ Finset.range i, (G l).indicator (ζ l) ω with hS
  set G' : ℕ → Set Ω' := fun j => G j ∩ {ω | ∀ i ≤ j, S i ω < x} with hG'
  -- measurability of the second switch
  have hSm : ∀ i ≤ K, StronglyMeasurable[ℱ i] (S i) := fun i hi =>
    (difRepTail_sums_sm ℱ ζ v G K hζ hv hG i hi).1
  have hG'm : ∀ j < K, MeasurableSet[ℱ j] (G' j) := by
    intro j hj
    refine (hG j hj).inter ?_
    have : {ω | ∀ i ≤ j, S i ω < x} = ⋂ i ∈ Finset.range (j + 1), {ω | S i ω < x} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range, Nat.lt_succ_iff]
    rw [this]
    refine Finset.measurableSet_biInter _ fun i hi => ?_
    have hij : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have h1 : StronglyMeasurable[ℱ j] (S i) :=
      (hSm i (hij.trans hj.le)).mono (ℱ.mono hij)
    exact measurableSet_lt h1.measurable measurable_const
  -- the inclusion
  have hincl : {ω | ∃ k, k ≤ K ∧ x ≤ S k ω} ⊆
      {ω | x ≤ ∑ j ∈ Finset.range K, (G' j).indicator (ζ j) ω} := by
    intro ω hω
    obtain ⟨k, hk, hxk⟩ := hω
    classical
    have hex : ∃ k, k ≤ K ∧ x ≤ S k ω := ⟨k, hk, hxk⟩
    set k₀ := Nat.find hex with hk₀
    have hk₀spec := Nat.find_spec hex
    have hk₀K : k₀ ≤ K := hk₀spec.1
    have hmin : ∀ i < k₀, S i ω < x := by
      intro i hi
      have := Nat.find_min hex hi
      push Not at this
      exact this (hi.le.trans hk₀K)
    have hterm : ∀ j ∈ Finset.range K, j ∉ Finset.range k₀ → (G' j).indicator (ζ j) ω = 0 := by
      intro j hjK hjk
      have hjk' : k₀ ≤ j := by simpa using hjk
      refine Set.indicator_of_notMem ?_ _
      intro hmem
      have := hmem.2 k₀ hjk'
      exact absurd hk₀spec.2 (not_le.2 this)
    have hsub : Finset.range k₀ ⊆ Finset.range K := Finset.range_subset_range.2 hk₀K
    rw [Set.mem_ofPred_eq, ← Finset.sum_subset hsub hterm]
    have : ∀ j ∈ Finset.range k₀, (G' j).indicator (ζ j) ω = (G j).indicator (ζ j) ω := by
      intro j hj
      have hj' : j < k₀ := Finset.mem_range.1 hj
      by_cases hmem : ω ∈ G j
      · have hmem' : ω ∈ G' j := ⟨hmem, fun i hi => hmin i (lt_of_le_of_lt hi hj')⟩
        rw [Set.indicator_of_mem hmem', Set.indicator_of_mem hmem]
      · have hmem' : ω ∉ G' j := fun h => hmem h.1
        rw [Set.indicator_of_notMem hmem', Set.indicator_of_notMem hmem]
    rw [Finset.sum_congr rfl this]
    exact hk₀spec.2
  -- the exponential bound for the second switch
  set r : ℝ := x / V with hr
  have hr0 : 0 ≤ r := div_nonneg hx hV.le
  have hmain := difRepTail_lintegral_X_le μ ℱ ζ v G' K hζ hv hG'm hv0 hint hmgf r K le_rfl
  set Xf : Ω' → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (r * ∑ j ∈ Finset.range K,
    (G' j).indicator (ζ j) ω - r ^ 2 / 2 * ∑ j ∈ Finset.range K, (G' j).indicator (v j) ω)) with hXf
  have hXfm : Measurable Xf := by
    have := (difRepTail_X_sm ℱ ζ v G' K hζ hv hG'm r K le_rfl).measurable
    exact ENNReal.measurable_ofReal.comp (this.mono (ℱ.le K) le_rfl)
  set c : ℝ := Real.exp (r * x - r ^ 2 / 2 * V) with hc
  have hcpos : 0 < c := Real.exp_pos _
  have hsub2 : {ω | x ≤ ∑ j ∈ Finset.range K, (G' j).indicator (ζ j) ω} ⊆
      {ω | ENNReal.ofReal c ≤ Xf ω} := by
    intro ω hω
    have hW : ∑ j ∈ Finset.range K, (G' j).indicator (v j) ω ≤ V := by
      refine le_trans ?_ (hsum ω)
      refine Finset.sum_le_sum fun j hj => ?_
      exact Set.indicator_le_indicator_of_subset (fun ω' h => h.1)
        (fun ω' => hv0 j (Finset.mem_range.1 hj) ω') ω
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have h1 : r * x ≤ r * ∑ j ∈ Finset.range K, (G' j).indicator (ζ j) ω :=
      mul_le_mul_of_nonneg_left hω hr0
    have h2 : r ^ 2 / 2 * ∑ j ∈ Finset.range K, (G' j).indicator (v j) ω ≤ r ^ 2 / 2 * V :=
      mul_le_mul_of_nonneg_left hW (by positivity)
    linarith
  have hmk := mul_meas_ge_le_lintegral (μ := μ) hXfm (ENNReal.ofReal c)
  set A := {ω | x ≤ ∑ j ∈ Finset.range K, (G' j).indicator (ζ j) ω} with hA
  have hAle : ENNReal.ofReal c * μ A ≤ 1 :=
    (by gcongr : ENNReal.ofReal c * μ A ≤ ENNReal.ofReal c * μ {x | ENNReal.ofReal c ≤ Xf x}).trans (hmk.trans hmain)
  have hAreal : c * μ.real A ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top hAle
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hcpos.le, ENNReal.toReal_one] at this
  have hcexp : c = Real.exp (x ^ 2 / (2 * V)) := by
    rw [hc, hr]
    congr 1
    field_simp
    ring
  have hfinal : μ.real A ≤ Real.exp (-x ^ 2 / (2 * V)) := by
    rw [neg_div, Real.exp_neg, ← hcexp, ← one_div, le_div_iff₀ hcpos]
    linarith [mul_comm c (μ.real A)]
  exact (measureReal_mono hincl).trans hfinal
/-! ## 1b. The two-sided form, the switch sum, and the peeling lemma (Amend 2 (ii)) -/

/-- The two-sided form of `azumaRandProxy_max` (the mgf hypotheses are symmetric under `ζ ↦ -ζ`). -/
private theorem difRepTail_max_abs {Ω' : Type} {mΩ' : MeasurableSpace Ω'} (μ : Measure Ω')
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ') (ζ v : ℕ → Ω' → ℝ) (G : ℕ → Set Ω') (K : ℕ)
    (B V x : ℝ)
    (hζ : ∀ j < K, StronglyMeasurable[ℱ (j + 1)] (ζ j))
    (hv : ∀ j < K, StronglyMeasurable[ℱ j] (v j))
    (hG : ∀ j < K, MeasurableSet[ℱ j] (G j))
    (hvB : ∀ j < K, ∀ ω, 0 ≤ v j ω ∧ v j ω ≤ B)
    (hint : ∀ j < K, ∀ r : ℝ, Integrable (fun ω => Real.exp (r * ζ j ω)) μ)
    (hmgf : ∀ j < K, ∀ r : ℝ,
      μ[fun ω => Real.exp (r * ζ j ω) | ℱ j] ≤ᵐ[μ] fun ω => Real.exp (r ^ 2 * v j ω / 2))
    (hsum : ∀ ω, ∑ j ∈ Finset.range K, (G j).indicator (v j) ω ≤ V) (hV : 0 < V) (hx : 0 ≤ x) :
    μ.real {ω | ∃ k, k ≤ K ∧ x ≤ |∑ j ∈ Finset.range k, (G j).indicator (ζ j) ω|} ≤
      2 * Real.exp (-x ^ 2 / (2 * V)) := by
  have h1 := azumaRandProxy_max μ ℱ ζ v G K B V x hζ hv hG hvB hint hmgf hsum hV hx
  have h2 := azumaRandProxy_max μ ℱ (fun j ω => -ζ j ω) v G K B V x
    (fun j hj => (hζ j hj).neg) hv hG hvB
    (fun j hj r => by
      have := hint j hj (-r)
      simpa only [neg_mul, mul_neg, neg_neg] using this)
    (fun j hj r => by
      have h := hmgf j hj (-r)
      simp only [neg_sq] at h
      have heq : (fun ω => Real.exp (r * -ζ j ω)) = fun ω => Real.exp (-r * ζ j ω) := by
        funext ω; ring_nf
      rw [heq]
      exact h)
    hsum hV hx
  have hsub : {ω | ∃ k, k ≤ K ∧ x ≤ |∑ j ∈ Finset.range k, (G j).indicator (ζ j) ω|} ⊆
      {ω | ∃ k, k ≤ K ∧ x ≤ ∑ j ∈ Finset.range k, (G j).indicator (ζ j) ω} ∪
      {ω | ∃ k, k ≤ K ∧ x ≤ ∑ j ∈ Finset.range k, (G j).indicator (fun ω => -ζ j ω) ω} := by
    intro ω hω
    obtain ⟨k, hk, hxk⟩ := hω
    have hneg : ∑ j ∈ Finset.range k, (G j).indicator (fun ω => -ζ j ω) ω =
        -∑ j ∈ Finset.range k, (G j).indicator (ζ j) ω := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : ω ∈ G j
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h]
    rcases le_abs'.1 hxk with h | h
    · right; exact ⟨k, hk, by rw [hneg]; linarith⟩
    · left; exact ⟨k, hk, h⟩
  calc μ.real {ω | ∃ k, k ≤ K ∧ x ≤ |∑ j ∈ Finset.range k, (G j).indicator (ζ j) ω|}
      ≤ μ.real ({ω | ∃ k, k ≤ K ∧ x ≤ ∑ j ∈ Finset.range k, (G j).indicator (ζ j) ω} ∪
        {ω | ∃ k, k ≤ K ∧ x ≤ ∑ j ∈ Finset.range k, (G j).indicator (fun ω => -ζ j ω) ω}) :=
        measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ Real.exp (-x ^ 2 / (2 * V)) + Real.exp (-x ^ 2 / (2 * V)) := add_le_add h1 h2
    _ = 2 * Real.exp (-x ^ 2 / (2 * V)) := by ring

/-- The switched proxy sum of a level: `Σ_{j<K} 1[A_{j+1} ≤ L] a_j ≤ L` for nonnegative `a_j`,
`A_{j+1} = Σ_{i ≤ j} a_i`. -/
private theorem difRepTail_switch_sum (a : ℕ → ℝ) {L : ℝ} (hL : 0 ≤ L) (K : ℕ)
    (ha : ∀ j < K, 0 ≤ a j) :
    ∑ j ∈ Finset.range K, (if ∑ i ∈ Finset.range (j + 1), a i ≤ L then a j else 0) ≤ L := by
  induction K with
  | zero => simpa using hL
  | succ K ih =>
    rw [Finset.sum_range_succ]
    by_cases h : ∑ i ∈ Finset.range (K + 1), a i ≤ L
    · have hall : ∀ j ∈ Finset.range (K + 1),
          (if ∑ i ∈ Finset.range (j + 1), a i ≤ L then a j else 0) = a j := by
        intro j hj
        have hj' : j + 1 ≤ K + 1 := Finset.mem_range.1 hj
        have : ∑ i ∈ Finset.range (j + 1), a i ≤ ∑ i ∈ Finset.range (K + 1), a i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hj')
            (fun i hi _ => ha i (Finset.mem_range.1 hi))
        simp [this.trans h]
      rw [← Finset.sum_range_succ (fun j => if ∑ i ∈ Finset.range (j + 1), a i ≤ L then a j else 0) K]
      rw [Finset.sum_congr rfl hall]
      exact h
    · simpa [h] using ih (fun j hj => ha j (Nat.lt_succ_of_lt hj))

/-- **Amend 2 (ii), `difRep2_peel`** (peeling of step 3(c) of T2180, for any adapted complex increments
`ζ_j` with a predictable proxy; docstring cites `docs/tickets/T2180-amend-2.md`).  The increments
`ζ_j` (`Re`, `Im` conditionally sub-Gaussian with the `ℱ_j`-measurable proxy `0 ≤ v_j ≤ c (a_j + e_j)`,
`a_j ≥ 0` `ℱ_j`-measurable the threshold increments, `e_j ≥ 0` deterministic with `Σ e_j ≤ δ`) have
the maximal tail `μ(∃ k ≤ K, ρ (Σ_{j<k} a_j + δ)^{1/2} < |Σ_{j<k} ζ_j|) ≤ (L + 1) · 4 e^{-ρ²/(16 c)}`
whenever `Σ_{j<K} a_j ≤ 2^L δ` on every path: the levels are `V_ℓ = 2^ℓ δ`, `ℓ ≤ L`, the switches
`G^ℓ_j = {Σ_{i ≤ j} a_i ≤ V_ℓ}`, and `azumaRandProxy_max` at `x = ρ (V_ℓ/2)^{1/2}/√2`.
At `δ = N^{-D}`, `ρ = N^{ε'}/2`, `c = m` this is the bound `(L_n + 1) · 4 e^{-N^{2ε'}/(64 m)}`. -/
theorem difRep2_peel {Ω' : Type} {mΩ' : MeasurableSpace Ω'} (μ : Measure Ω')
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ') (ζ : ℕ → Ω' → ℂ) (a v : ℕ → Ω' → ℝ)
    (e : ℕ → ℝ) (K Lmax : ℕ) (c δ ρ : ℝ) (hc : 0 < c) (hδ : 0 < δ) (hρ : 0 ≤ ρ)
    (hζre : ∀ j < K, StronglyMeasurable[ℱ (j + 1)] (fun ω => (ζ j ω).re))
    (hζim : ∀ j < K, StronglyMeasurable[ℱ (j + 1)] (fun ω => (ζ j ω).im))
    (ha : ∀ j < K, StronglyMeasurable[ℱ j] (a j))
    (hv : ∀ j < K, StronglyMeasurable[ℱ j] (v j))
    (ha0 : ∀ j < K, ∀ ω, 0 ≤ a j ω) (hv0 : ∀ j < K, ∀ ω, 0 ≤ v j ω)
    (he0 : ∀ j < K, 0 ≤ e j) (hve : ∀ j < K, ∀ ω, v j ω ≤ c * (a j ω + e j))
    (hesum : ∑ j ∈ Finset.range K, e j ≤ δ)
    (haL : ∀ ω, ∑ j ∈ Finset.range K, a j ω ≤ 2 ^ Lmax * δ)
    (hintRe : ∀ j < K, ∀ r : ℝ, Integrable (fun ω => Real.exp (r * (ζ j ω).re)) μ)
    (hintIm : ∀ j < K, ∀ r : ℝ, Integrable (fun ω => Real.exp (r * (ζ j ω).im)) μ)
    (hmgfRe : ∀ j < K, ∀ r : ℝ, μ[fun ω => Real.exp (r * (ζ j ω).re) | ℱ j] ≤ᵐ[μ]
      fun ω => Real.exp (r ^ 2 * v j ω / 2))
    (hmgfIm : ∀ j < K, ∀ r : ℝ, μ[fun ω => Real.exp (r * (ζ j ω).im) | ℱ j] ≤ᵐ[μ]
      fun ω => Real.exp (r ^ 2 * v j ω / 2)) :
    μ.real {ω | ∃ k, k ≤ K ∧
        ρ * (∑ j ∈ Finset.range k, a j ω + δ) ^ (1 / 2 : ℝ) < ‖∑ j ∈ Finset.range k, ζ j ω‖} ≤
      ((Lmax : ℝ) + 1) * (4 * Real.exp (-ρ ^ 2 / (16 * c))) := by
  set A : ℕ → Ω' → ℝ := fun k ω => ∑ j ∈ Finset.range k, a j ω with hA
  set B : ℝ := c * (2 ^ Lmax * δ + δ) with hB
  have hlev : ∀ l : ℕ, 0 < (2 : ℝ) ^ l * δ := fun l => by positivity
  -- the switches of level `l`
  set Gl : ℕ → ℕ → Set Ω' := fun l j => {ω | A (j + 1) ω ≤ 2 ^ l * δ} with hGl
  have hGm : ∀ l, ∀ j < K, MeasurableSet[ℱ j] (Gl l j) := by
    intro l j hj
    have hAm : StronglyMeasurable[ℱ j] (A (j + 1)) := by
      refine Finset.stronglyMeasurable_fun_sum _ fun i hi => ?_
      have hij : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      exact (ha i (lt_of_le_of_lt hij hj)).mono (ℱ.mono hij)
    exact measurableSet_le hAm.measurable measurable_const
  have hvB : ∀ j < K, ∀ ω, 0 ≤ v j ω ∧ v j ω ≤ B := by
    intro j hj ω
    refine ⟨hv0 j hj ω, (hve j hj ω).trans ?_⟩
    have h1 : a j ω ≤ 2 ^ Lmax * δ :=
      (Finset.single_le_sum (fun i hi => ha0 i (Finset.mem_range.1 hi) ω)
        (Finset.mem_range.2 hj)).trans (haL ω)
    have h2 : e j ≤ δ :=
      (Finset.single_le_sum (fun i hi => he0 i (Finset.mem_range.1 hi)) (Finset.mem_range.2 hj)).trans
        hesum
    rw [hB]
    exact mul_le_mul_of_nonneg_left (add_le_add h1 h2) hc.le
  -- the switched proxy sum of a level
  have hsumv : ∀ l ω, ∑ j ∈ Finset.range K, (Gl l j).indicator (v j) ω ≤ 2 * c * (2 ^ l * δ) := by
    intro l ω
    have hsa : ∑ j ∈ Finset.range K, (Gl l j).indicator (a j) ω ≤ 2 ^ l * δ := by
      have := difRepTail_switch_sum (fun j => a j ω) (hlev l).le K (fun j hj => ha0 j hj ω)
      simpa only [Set.indicator_apply, hGl, hA, Set.mem_ofPred_eq] using this
    have hpt : ∀ j ∈ Finset.range K,
        (Gl l j).indicator (v j) ω ≤ c * ((Gl l j).indicator (a j) ω + e j) := by
      intro j hj
      have hj' := Finset.mem_range.1 hj
      by_cases hmem : ω ∈ Gl l j
      · simp only [Set.indicator_of_mem hmem]
        exact hve j hj' ω
      · simp only [Set.indicator_of_notMem hmem, zero_add]
        exact mul_nonneg hc.le (he0 j hj')
    calc ∑ j ∈ Finset.range K, (Gl l j).indicator (v j) ω
        ≤ ∑ j ∈ Finset.range K, c * ((Gl l j).indicator (a j) ω + e j) := Finset.sum_le_sum hpt
      _ = c * (∑ j ∈ Finset.range K, (Gl l j).indicator (a j) ω + ∑ j ∈ Finset.range K, e j) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ c * (2 ^ l * δ + 2 ^ l * δ) := by
          refine mul_le_mul_of_nonneg_left (add_le_add hsa ?_) hc.le
          refine hesum.trans ?_
          have : (1 : ℝ) ≤ 2 ^ l := one_le_pow₀ (by norm_num)
          nlinarith
      _ = 2 * c * (2 ^ l * δ) := by ring
  -- the level tails
  set y : ℕ → ℝ := fun l => ρ * Real.sqrt (2 ^ l * δ / 2) with hy
  set x : ℕ → ℝ := fun l => y l / Real.sqrt 2 with hx
  have hx0 : ∀ l, 0 ≤ x l := fun l => by
    have := hlev l
    simp only [hx, hy]
    positivity
  have hexp : ∀ l, -(x l) ^ 2 / (2 * (2 * c * (2 ^ l * δ))) = -ρ ^ 2 / (16 * c) := by
    intro l
    have h1 : (x l) ^ 2 = ρ ^ 2 * (2 ^ l * δ) / 4 := by
      have := hlev l
      simp only [hx, hy]
      rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)]
      ring
    rw [h1]
    have := (hlev l).ne'
    field_simp
    ring
  have hlevRe : ∀ l, μ.real {ω | ∃ k, k ≤ K ∧
      x l ≤ |∑ j ∈ Finset.range k, (Gl l j).indicator (fun ω => (ζ j ω).re) ω|} ≤
      2 * Real.exp (-ρ ^ 2 / (16 * c)) := by
    intro l
    have := difRepTail_max_abs μ ℱ (fun j ω => (ζ j ω).re) v (Gl l) K B (2 * c * (2 ^ l * δ)) (x l)
      hζre hv (hGm l) hvB hintRe hmgfRe (hsumv l) (by have := hlev l; positivity) (hx0 l)
    rwa [hexp l] at this
  have hlevIm : ∀ l, μ.real {ω | ∃ k, k ≤ K ∧
      x l ≤ |∑ j ∈ Finset.range k, (Gl l j).indicator (fun ω => (ζ j ω).im) ω|} ≤
      2 * Real.exp (-ρ ^ 2 / (16 * c)) := by
    intro l
    have := difRepTail_max_abs μ ℱ (fun j ω => (ζ j ω).im) v (Gl l) K B (2 * c * (2 ^ l * δ)) (x l)
      hζim hv (hGm l) hvB hintIm hmgfIm (hsumv l) (by have := hlev l; positivity) (hx0 l)
    rwa [hexp l] at this
  -- the inclusion
  set E : ℕ → Set Ω' := fun l =>
    {ω | ∃ k, k ≤ K ∧ x l ≤ |∑ j ∈ Finset.range k, (Gl l j).indicator (fun ω => (ζ j ω).re) ω|} ∪
    {ω | ∃ k, k ≤ K ∧ x l ≤ |∑ j ∈ Finset.range k, (Gl l j).indicator (fun ω => (ζ j ω).im) ω|}
    with hE
  have hincl : {ω | ∃ k, k ≤ K ∧
      ρ * (∑ j ∈ Finset.range k, a j ω + δ) ^ (1 / 2 : ℝ) < ‖∑ j ∈ Finset.range k, ζ j ω‖} ⊆
      ⋃ l ∈ Finset.range (Lmax + 1), E l := by
    intro ω hω
    obtain ⟨k, hk, hlt⟩ := hω
    classical
    have hAk0 : 0 ≤ A k ω := Finset.sum_nonneg fun i hi =>
      ha0 i (lt_of_lt_of_le (Finset.mem_range.1 hi) hk) ω
    have hAkL : A k ω ≤ 2 ^ Lmax * δ :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hk)
        (fun i hi _ => ha0 i (Finset.mem_range.1 hi) ω)).trans (haL ω)
    have hexl : ∃ l, A k ω ≤ 2 ^ l * δ := ⟨Lmax, hAkL⟩
    set l := Nat.find hexl with hl
    have hl1 : A k ω ≤ 2 ^ l * δ := Nat.find_spec hexl
    have hlL : l ≤ Lmax := Nat.find_min' hexl hAkL
    have hl2 : 2 ^ l * δ / 2 ≤ A k ω + δ := by
      by_cases hl0 : l = 0
      · rw [hl0]
        simp only [pow_zero, one_mul]
        linarith
      · obtain ⟨l', hl'⟩ := Nat.exists_eq_succ_of_ne_zero hl0
        have hmin := Nat.find_min hexl (show l' < l by omega)
        push Not at hmin
        rw [hl', pow_succ]
        nlinarith
    -- the threshold is exceeded at level `l`
    have hyS : y l < ‖∑ j ∈ Finset.range k, ζ j ω‖ := by
      refine lt_of_le_of_lt ?_ hlt
      simp only [hy]
      refine mul_le_mul_of_nonneg_left ?_ hρ
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow (by have := hlev l; positivity) hl2 (by norm_num)
    have hxS : x l < max |(∑ j ∈ Finset.range k, ζ j ω).re| |(∑ j ∈ Finset.range k, ζ j ω).im| := by
      have h1 := Complex.norm_le_sqrt_two_mul_max (∑ j ∈ Finset.range k, ζ j ω)
      have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
      simp only [hx]
      rw [div_lt_iff₀ hs2]
      nlinarith
    have hon : ∀ j ∈ Finset.range k, ω ∈ Gl l j := by
      intro j hj
      have hj' : j < k := Finset.mem_range.1 hj
      change A (j + 1) ω ≤ 2 ^ l * δ
      refine le_trans ?_ hl1
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hj')
        (fun i hi _ => ha0 i (lt_of_lt_of_le (Finset.mem_range.1 hi) hk) ω)
    refine Set.mem_iUnion₂.2 ⟨l, Finset.mem_range.2 (Nat.lt_succ_of_le hlL), ?_⟩
    rcases lt_max_iff.1 hxS with h | h
    · left
      refine ⟨k, hk, ?_⟩
      have : ∑ j ∈ Finset.range k, (Gl l j).indicator (fun ω => (ζ j ω).re) ω =
          (∑ j ∈ Finset.range k, ζ j ω).re := by
        rw [Complex.re_sum]
        exact Finset.sum_congr rfl fun j hj => Set.indicator_of_mem (hon j hj) _
      rw [this]; exact h.le
    · right
      refine ⟨k, hk, ?_⟩
      have : ∑ j ∈ Finset.range k, (Gl l j).indicator (fun ω => (ζ j ω).im) ω =
          (∑ j ∈ Finset.range k, ζ j ω).im := by
        rw [Complex.im_sum]
        exact Finset.sum_congr rfl fun j hj => Set.indicator_of_mem (hon j hj) _
      rw [this]; exact h.le
  calc μ.real {ω | ∃ k, k ≤ K ∧
        ρ * (∑ j ∈ Finset.range k, a j ω + δ) ^ (1 / 2 : ℝ) < ‖∑ j ∈ Finset.range k, ζ j ω‖}
      ≤ μ.real (⋃ l ∈ Finset.range (Lmax + 1), E l) := measureReal_mono hincl (measure_ne_top _ _)
    _ ≤ ∑ l ∈ Finset.range (Lmax + 1), μ.real (E l) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ l ∈ Finset.range (Lmax + 1), (4 * Real.exp (-ρ ^ 2 / (16 * c))) := by
        refine Finset.sum_le_sum fun l _ => ?_
        refine (measureReal_union_le _ _).trans ?_
        linarith [hlevRe l, hlevIm l]
    _ = ((Lmax : ℝ) + 1) * (4 * Real.exp (-ρ ^ 2 / (16 * c))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
/-! ## 1c. Doob's `L²` tail for martingale differences -/

/-- A function with integrable fourth power is square-integrable (probability space). -/
private theorem difRepTail_memLp_two_of_pow4 {Ω' : Type*} {m : MeasurableSpace Ω'} {μ : Measure Ω'}
    [IsFiniteMeasure μ] {f : Ω' → ℝ} (hf : AEStronglyMeasurable f μ)
    (h4 : Integrable (fun ω => f ω ^ 4) μ) : MemLp f 2 μ := by
  rw [memLp_two_iff_integrable_sq hf]
  have hg : AEStronglyMeasurable (fun ω => f ω ^ 2) μ := hf.pow 2
  have h2 : MemLp (fun ω => f ω ^ 2) 2 μ := by
    rw [memLp_two_iff_integrable_sq hg]
    refine h4.congr (ae_of_all _ fun ω => ?_)
    simp only
    ring
  exact memLp_one_iff_integrable.1 (h2.mono_exponent (by norm_num))

/-- **Doob's `L²` tail for martingale differences**: `F_j` is `ℱ_{j+1}`-measurable, square-integrable,
conditionally centred, with `𝔼 F_j² ≤ q`; then `μ(∃ k ≤ K, x ≤ |Σ_{j<k} F_j|) ≤ K q / x²`. -/
private theorem difRepTail_doob_tail {Ω' : Type} {mΩ' : MeasurableSpace Ω'} (μ : Measure Ω')
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ') (F : ℕ → Ω' → ℝ) (K : ℕ) (q x : ℝ)
    (hF : ∀ j < K, StronglyMeasurable[ℱ (j + 1)] (F j))
    (hL2 : ∀ j < K, MemLp (F j) 2 μ)
    (hmean : ∀ j < K, μ[F j | ℱ j] =ᵐ[μ] 0)
    (hq : ∀ j < K, ∫ ω, (F j ω) ^ 2 ∂μ ≤ q) (hx : 0 < x) :
    μ.real {ω | ∃ k, k ≤ K ∧ x ≤ |∑ j ∈ Finset.range k, F j ω|} ≤ K * q / x ^ 2 := by
  classical
  set F' : ℕ → Ω' → ℝ := fun j ω => if j < K then F j ω else 0 with hF'
  set M : ℕ → Ω' → ℝ := fun k ω => ∑ j ∈ Finset.range k, F' j ω with hM
  have hF'm : ∀ j, StronglyMeasurable[ℱ (j + 1)] (F' j) := fun j => by
    by_cases h : j < K
    · simpa only [hF', h, ↓reduceIte] using hF j h
    · simp only [hF', h, ↓reduceIte]
      exact stronglyMeasurable_const
  have hF'L2 : ∀ j, MemLp (F' j) 2 μ := fun j => by
    by_cases h : j < K
    · simpa only [hF', h, ↓reduceIte] using hL2 j h
    · simp only [hF', h, ↓reduceIte]
      exact MemLp.zero'
  have hMad : StronglyAdapted ℱ M := fun k =>
    Finset.stronglyMeasurable_fun_sum _ fun j hj =>
      (hF'm j).mono (ℱ.mono (Nat.succ_le_of_lt (Finset.mem_range.1 hj)))
  have hML2 : ∀ k, MemLp (M k) 2 μ := fun k =>
    memLp_finsetSum _ fun j _ => hF'L2 j
  have hMint : ∀ k, Integrable (M k) μ := fun k => (memLp_one_iff_integrable.1
    ((hML2 k).mono_exponent (by norm_num)))
  have hMsub : ∀ k, M (k + 1) - M k = F' k := fun k => by
    funext ω
    simp only [hM, Pi.sub_apply, Finset.sum_range_succ]
    ring
  have hmart : Martingale M ℱ μ := by
    refine martingale_of_condExp_sub_eq_zero_nat hMad hMint fun k => ?_
    rw [hMsub]
    by_cases h : k < K
    · have : F' k = F k := funext fun ω => by simp only [hF', h, ↓reduceIte]
      rw [this]
      exact hmean k h
    · have : F' k = 0 := funext fun ω => by simp only [hF', h, ↓reduceIte, Pi.zero_apply]
      rw [this]
      exact (condExp_zero).eventuallyEq
  have hM0 : M 0 = 0 := by funext ω; simp [hM]
  have hdoob := doob_L2_max hmart hM0 hML2 K hx
  have hset : {ω | ∃ k, k ≤ K ∧ x ≤ |∑ j ∈ Finset.range k, F j ω|} =
      {ω | x ≤ (Finset.range (K + 1)).sup' Finset.nonempty_range_add_one fun k => |M k ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Finset.le_sup'_iff, Finset.mem_range, Nat.lt_succ_iff]
    constructor
    · rintro ⟨k, hk, hxk⟩
      refine ⟨k, hk, ?_⟩
      have : M k ω = ∑ j ∈ Finset.range k, F j ω :=
        Finset.sum_congr rfl fun j hj => by
          simp only [hF', lt_of_lt_of_le (Finset.mem_range.1 hj) hk, ↓reduceIte]
      rw [this]; exact hxk
    · rintro ⟨k, hk, hxk⟩
      refine ⟨k, hk, ?_⟩
      have : M k ω = ∑ j ∈ Finset.range k, F j ω :=
        Finset.sum_congr rfl fun j hj => by
          simp only [hF', lt_of_lt_of_le (Finset.mem_range.1 hj) hk, ↓reduceIte]
      rw [← this]; exact hxk
  rw [hset]
  refine hdoob.trans ?_
  gcongr
  rw [martingale_sq_eq_sum hmart hM0 hML2 K]
  calc ∑ k ∈ Finset.range K, ∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ
      ≤ ∑ k ∈ Finset.range K, q := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' : k < K := Finset.mem_range.1 hk
        have : (fun ω => (M (k + 1) ω - M k ω) ^ 2) = fun ω => (F k ω) ^ 2 := by
          funext ω
          have := congrFun (hMsub k) ω
          simp only [Pi.sub_apply, hF', hk', ↓reduceIte] at this
          rw [this]
        rw [this]
        exact hq k hk'
    _ = K * q := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Amend 2 (ii), `difRep2_peel_N`: the form of `docs/tickets/T2180-amend-2.md`**.  The peeling lemma
`difRep2_peel` at `δ = N^{-D}`, `ρ = N^{ε'}`, `c = m`: for increments `ζ_j` whose `Re`, `Im` are
conditionally sub-Gaussian with an `ℱ_j`-measurable proxy `0 ≤ v_j ≤ m (a_j + e_j)` (`a_j ≥ 0` the threshold
increments, `e_j ≥ 0` deterministic with `Σ e_j ≤ N^{-D}`) and `Σ_{j<K} a_j ≤ 2^L N^{-D}` on every path
(the levels `V_ℓ = 2^ℓ N^{-D}`, `ℓ ≤ L`),
`μ(∃ k ≤ K, |Σ_{j<k} ζ_j| > N^{ε'} (Σ_{j<k} a_j + N^{-D})^{1/2}) ≤ (L + 1) · 4 e^{-N^{2ε'}/(64 m)}`
(the exponent is `N^{2ε'}/(16 m)` before `64 m` is read off). -/
theorem difRep2_peel_N {Ω' : Type} {mΩ' : MeasurableSpace Ω'} (μ : Measure Ω')
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ') (ζ : ℕ → Ω' → ℂ) (a v : ℕ → Ω' → ℝ)
    (e : ℕ → ℝ) (K Lmax m : ℕ) (N D ε' : ℝ) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (hζre : ∀ j < K, StronglyMeasurable[ℱ (j + 1)] (fun ω => (ζ j ω).re))
    (hζim : ∀ j < K, StronglyMeasurable[ℱ (j + 1)] (fun ω => (ζ j ω).im))
    (ha : ∀ j < K, StronglyMeasurable[ℱ j] (a j))
    (hv : ∀ j < K, StronglyMeasurable[ℱ j] (v j))
    (ha0 : ∀ j < K, ∀ ω, 0 ≤ a j ω) (hv0 : ∀ j < K, ∀ ω, 0 ≤ v j ω)
    (he0 : ∀ j < K, 0 ≤ e j) (hve : ∀ j < K, ∀ ω, v j ω ≤ (m : ℝ) * (a j ω + e j))
    (hesum : ∑ j ∈ Finset.range K, e j ≤ N ^ (-D))
    (haL : ∀ ω, ∑ j ∈ Finset.range K, a j ω ≤ 2 ^ Lmax * N ^ (-D))
    (hintRe : ∀ j < K, ∀ r : ℝ, Integrable (fun ω => Real.exp (r * (ζ j ω).re)) μ)
    (hintIm : ∀ j < K, ∀ r : ℝ, Integrable (fun ω => Real.exp (r * (ζ j ω).im)) μ)
    (hmgfRe : ∀ j < K, ∀ r : ℝ, μ[fun ω => Real.exp (r * (ζ j ω).re) | ℱ j] ≤ᵐ[μ]
      fun ω => Real.exp (r ^ 2 * v j ω / 2))
    (hmgfIm : ∀ j < K, ∀ r : ℝ, μ[fun ω => Real.exp (r * (ζ j ω).im) | ℱ j] ≤ᵐ[μ]
      fun ω => Real.exp (r ^ 2 * v j ω / 2)) :
    μ.real {ω | ∃ k, k ≤ K ∧
        N ^ ε' * (∑ j ∈ Finset.range k, a j ω + N ^ (-D)) ^ (1 / 2 : ℝ) <
          ‖∑ j ∈ Finset.range k, ζ j ω‖} ≤
      ((Lmax : ℝ) + 1) * (4 * Real.exp (-N ^ (2 * ε') / (64 * (m : ℝ)))) := by
  have hN0 : 0 < N := by linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h := difRep2_peel μ ℱ ζ a v e K Lmax (m : ℝ) (N ^ (-D)) (N ^ ε') hm0
    (Real.rpow_pos_of_pos hN0 _) (Real.rpow_nonneg hN0.le _) hζre hζim ha hv ha0 hv0 he0 hve hesum
    haL hintRe hintIm hmgfRe hmgfIm
  refine h.trans ?_
  have hpow : (N ^ ε') ^ 2 = N ^ (2 * ε') := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have hexp : -(N ^ ε') ^ 2 / (16 * (m : ℝ)) ≤ -N ^ (2 * ε') / (64 * (m : ℝ)) := by
    rw [hpow]
    have h0 : 0 ≤ N ^ (2 * ε') := Real.rpow_nonneg hN0.le _
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left h0 (by positivity) (by nlinarith)
  gcongr

/-! ## 2. Copies of the private helpers of the merged `Induction/AzumaProxyN.lean:122-232`

(RBM3D `43ab861`, T2159: `azumaProxy_hasDerivAt_dir` ... `azumaProxy_trace_eq`; ports of RBM2D
`Induction/AzumaProxyN.lean:200-260` at `c9a24cf`), renamed with the prefix `difRepTail_`. -/

section Copies

variable {d : ℕ} (sz : Sizes d)

/-- The directional derivative along the real line `y ↦ M + y X` at `0` is `fderiv ℝ Ψ M X`, for
`Ψ` differentiable at `M` (copy of the private `StepDecompN_hasDerivAt_dir`). -/
private theorem difRepTail_hasDerivAt_dir {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ψ : Matrix ι ι ℂ → ℂ} {M : Matrix ι ι ℂ} (X : Matrix ι ι ℂ) (hd : DifferentiableAt ℝ Ψ M) :
    HasDerivAt (fun y : ℝ => Ψ (M + (y : ℂ) • X)) (fderiv ℝ Ψ M X) 0 := by
  have hadd : HasDerivAt (fun t' : ℝ => M + t' • X) X 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add M
  have hp0 : HasDerivAt (fun t' : ℝ => Ψ (M + t' • X)) (fderiv ℝ Ψ M X) 0 := by
    have h1 : HasFDerivAt Ψ (fderiv ℝ Ψ (M + (0 : ℝ) • X)) (M + (0 : ℝ) • X) := by
      simpa using hd.hasFDerivAt
    have h2 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) h1 hadd
    simp only [zero_smul, add_zero, Function.comp_def] at h2
    exact h2
  simpa only [Complex.coe_smul] using hp0

/-- `dirDerivN` is `fderiv ℝ` where the observable is differentiable. -/
private theorem difRepTail_dirDerivN_eq {L W : ℕ} [NeZero L] [NeZero W]
    {Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ} {M : Matrix (Idx d L W) (Idx d L W) ℂ}
    (X : Matrix (Idx d L W) (Idx d L W) ℂ) (hd : DifferentiableAt ℝ Φ M) :
    dirDerivN Φ M X = fderiv ℝ Φ M X :=
  (difRepTail_hasDerivAt_dir X hd).deriv

/-- `linTr` at the direction `(-I) • A` reads the imaginary part of `trace (A * X)` (copy of the
private `StepDecompN_linTr_neg_I_smul`). -/
private theorem difRepTail_linTr_neg_I_smul (n : ℕ)
    (A X : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    linTr n ((-Complex.I) • A) X = (Matrix.trace (A * X)).im := by
  unfold linTr
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  ring

/-- The coordinate matrix of the slice is the coordinate matrix of the coordinate (copy of the
private `QVForm_seqXmat_single`, `Path/QVIdentity.lean:264`). -/
private theorem difRepTail_seqXmat_single (n : ℕ) (c : CoordF d (sz.L n) (sz.W n)) :
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
  unfold Sizes.seqXmat coordinateMatrix
  rw [hs]

/-- `linTrVar` as the sum over the coordinates of one size. -/
private theorem difRepTail_linTrVar_eq (n : ℕ)
    (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    linTrVar n A = ∑ c : CoordF d (sz.L n) (sz.W n),
      (gvarF d (sz.L n) (sz.W n) (sz.lam n) c : ℝ) *
      (linTr n A (coordinateMatrix d (sz.L n) (sz.W n) c)) ^ 2 := by
  classical
  rw [← vB_self (sz := sz)]
  unfold vB coordFinset
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Function.Embedding.sigmaMk_apply, difRepTail_seqXmat_single]
  change (gvarF d (sz.L n) (sz.W n) (sz.lam n) c : ℝ) * _ * _ = _
  ring

private theorem difRepTail_sq_re_le (z : ℂ) : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
  calc z.re ^ 2 = |z.re| ^ 2 := (sq_abs _).symm
    _ ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm z) 2

private theorem difRepTail_sq_im_le (z : ℂ) : z.im ^ 2 ≤ ‖z‖ ^ 2 := by
  calc z.im ^ 2 = |z.im| ^ 2 := (sq_abs _).symm
    _ ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm z) 2

/-- **The variance identity**: for `A` with `tr (A X_c) = D_c`, `linTrVar A` and
`linTrVar ((-I) • A)` are `Σ_c gvar_c (Re D_c)²` and `Σ_c gvar_c (Im D_c)²`, hence at most
`Σ_c gvar_c ‖D_c‖²`. -/
private theorem difRepTail_linTrVar_le (n : ℕ)
    (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (D : CoordF d (sz.L n) (sz.W n) → ℂ)
    (hD : ∀ c, Matrix.trace (A * coordinateMatrix d (sz.L n) (sz.W n) c) = D c) :
    linTrVar n A ≤ ∑ c : CoordF d (sz.L n) (sz.W n),
        (gvarF d (sz.L n) (sz.W n) (sz.lam n) c : ℝ) * ‖D c‖ ^ 2 ∧
    linTrVar n ((-Complex.I) • A) ≤
      ∑ c : CoordF d (sz.L n) (sz.W n), (gvarF d (sz.L n) (sz.W n) (sz.lam n) c : ℝ) * ‖D c‖ ^ 2 := by
  constructor
  · rw [difRepTail_linTrVar_eq]
    refine Finset.sum_le_sum fun c _ =>
      mul_le_mul_of_nonneg_left ?_ (gvarF d (sz.L n) (sz.W n) (sz.lam n) c).2
    have : linTr n A (coordinateMatrix d (sz.L n) (sz.W n) c) = (D c).re := by
      rw [← hD c]; rfl
    rw [this]
    exact difRepTail_sq_re_le _
  · rw [difRepTail_linTrVar_eq]
    refine Finset.sum_le_sum fun c _ =>
      mul_le_mul_of_nonneg_left ?_ (gvarF d (sz.L n) (sz.W n) (sz.lam n) c).2
    rw [difRepTail_linTr_neg_I_smul, hD c]
    exact difRepTail_sq_im_le _

/-- `tr (A X)` for `A = Σ_a κ_a gradMat Φ_a M` at a Hermitian direction `X` is the `κ`-weighted sum
of the directional derivatives. -/
private theorem difRepTail_trace_eq {ι : Type*} [Fintype ι] {n : ℕ}
    {Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (hΦ : ∀ b, HermTestFun sz n (Φ b)) (κ : ι → ℂ)
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian)
    {X : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hX : X.IsHermitian) :
    Matrix.trace ((∑ a, κ a • gradMat (Φ a) M) * X) = ∑ a, κ a * dirDerivN (Φ a) M X := by
  rw [Matrix.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hd : DifferentiableAt ℝ (Φ a) M := ((hΦ a).contDiffAt M hM).differentiableAt (by norm_num)
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ← fderiv_eq_trace_gradMat M hX,
    difRepTail_dirDerivN_eq X hd]

end Copies

/-! ## 3. Grid arithmetic (private) -/

section GridArith

private theorem difRepTail_gridTime_nonneg {s t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hs0 : 0 ≤ s n)
    (hst : s n ≤ t n) (j : ℕ) : 0 ≤ gridTime s t K n j := by
  have hΔ := ST_gridStep_nonneg s t K n hst
  unfold gridTime
  have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg this hΔ]

private theorem difRepTail_gridTime_le {s t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hst : s n ≤ t n)
    (hK0 : K n ≠ 0) {j : ℕ} (hj : j ≤ K n) : gridTime s t K n j ≤ t n := by
  have hΔ := ST_gridStep_nonneg s t K n hst
  have hj' : (j : ℝ) ≤ (K n : ℝ) := by exact_mod_cast hj
  have h := mul_le_mul_of_nonneg_right hj' hΔ
  have hlast := gridTime_last s t K n hK0
  unfold gridTime at hlast ⊢
  nlinarith

private theorem difRepTail_gridTime_succ (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) :
    gridTime s t K n (j + 1) = gridTime s t K n j + gridStep s t K n := by
  unfold gridTime; push_cast; ring

private theorem difRepTail_K_mul_step (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hK : K n ≠ 0) :
    (K n : ℝ) * gridStep s t K n = t n - s n := by
  have hK' : (K n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK
  unfold gridStep
  field_simp

private theorem difRepTail_size_cast {d : ℕ} (sz : Sizes d) (n : ℕ) :
    (sz.W n : ℝ) ^ d * (sz.L n : ℝ) ^ d = ((sz.size n : ℕ) : ℝ) := by
  have : ((sz.size n : ℕ) : ℝ) = (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) := rfl
  rw [this]
  push_cast
  ring

end GridArith

/-! ## 4. The first-chaos increment as a frozen linear functional -/

section ZLinear

variable {d : ℕ} (sz : Sizes d)

/-- `Σ_b κ_b Z_b` is `stepZCN` of the loop family with the kernel `(·, a) ↦ κ_a`
(the `hFeq` of the merged `azumaSubGN`, `AzumaProxyN.lean:271`, with `ZfamN` the `ZvecN` of the loop family
by definition). -/
private theorem difRepTail_sum_Z_eq (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n)
    {k : ℕ} (σ : Fin k → Bool) (κ : (Fin k → Zd d (sz.L n)) → ℂ) (b₀ : Fin k → Zd d (sz.L n))
    (ω : PathΩ sz) :
    ∑ b, κ b * ZvecN sz E s t K n j σ ω b =
      stepZCN sz s t K n j (loopFamN sz E s t K n j σ) (fun _ a => κ a) b₀ ω := by
  have hK : K n ≠ 0 := by omega
  have hu0 := difRepTail_gridTime_nonneg (K := K) hs0 hst (j + 1)
  have hu1 : gridTime s t K n (j + 1) < 1 := (difRepTail_gridTime_le hst hK hj).trans_lt ht1
  have hΦ : ∀ a, HermTestFun sz n (loopFamN sz E s t K n j σ a) := fun a =>
    (hermTestFunLoopN sz k n (E n) (gridTime s t K n (j + 1)) hE hu0 hu1 σ a).1
  have hH := pathH_isHermitian sz s t K n j ω
  have hX := Sizes.seqXmat_isHermitian sz n (ω (j + 1))
  have htr := difRepTail_trace_eq sz hΦ κ hH hX
  have hA : AbCN sz s t K n j (loopFamN sz E s t K n j σ) (fun _ a => κ a) b₀ ω =
      ∑ a, κ a • gradMat (loopFamN sz E s t K n j σ a) (pathH sz s t K n j ω) := rfl
  set w := Matrix.trace (AbCN sz s t K n j (loopFamN sz E s t K n j σ) (fun _ a => κ a) b₀ ω *
    Sizes.seqXmat sz n (ω (j + 1))) with hw
  have hre : linTr n (AbCN sz s t K n j (loopFamN sz E s t K n j σ) (fun _ a => κ a) b₀ ω)
      (Sizes.seqXmat sz n (ω (j + 1))) = w.re := rfl
  have him : linTr n ((-Complex.I) • AbCN sz s t K n j (loopFamN sz E s t K n j σ)
      (fun _ a => κ a) b₀ ω) (Sizes.seqXmat sz n (ω (j + 1))) = w.im :=
    difRepTail_linTr_neg_I_smul sz n _ _
  have hw' : w = ∑ a, κ a * dirDerivN (loopFamN sz E s t K n j σ a) (pathH sz s t K n j ω)
      (Sizes.seqXmat sz n (ω (j + 1))) := by rw [hw, hA]; exact htr
  have hsum : ∑ b, κ b * ZvecN sz E s t K n j σ ω b = (Real.sqrt (gridStep s t K n) : ℂ) * w := by
    rw [hw', Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold ZvecN dirDerivN loopFamN loopDerivN
    ring
  rw [hsum]
  unfold stepZCN stepZCN_re stepZCN_im
  rw [hre, him]
  have hreim := Complex.re_add_im w
  push_cast
  linear_combination (Real.sqrt (gridStep s t K n) : ℂ) * hreim.symm

/-- The conditional-variance proxy of `Σ_b κ_b Z_b`: `linTrVar` of the frozen gradient direction (and of
`(-I)` times it) is at most `k Re Σ_{b,b'} κ_b conj κ_{b'} (𝓔⊗𝓔)_{u_{j+1}}(H_j)_{σ,b,b'}`
(`difRepTail_linTrVar_le`, `azumaProxy_trace_eq` and the merged `qvPropagatedN`, `QVN.lean:813`). -/
private theorem difRepTail_linTrVar_le_QV (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n)
    {k : ℕ} (hk : 2 ≤ k) (σ : Fin k → Bool) (κ : (Fin k → Zd d (sz.L n)) → ℂ)
    (b₀ : Fin k → Zd d (sz.L n)) (ω : PathΩ sz) :
    linTrVar n (AbCN sz s t K n j (loopFamN sz E s t K n j σ) (fun _ a => κ a) b₀ ω) ≤
        (k : ℝ) * (∑ b : Fin k → Zd d (sz.L n), ∑ b' : Fin k → Zd d (sz.L n),
          κ b * (starRingEnd ℂ) (κ b') *
            sz.STeeM n (E n) (gridTime s t K n (j + 1)) (pathH sz s t K n j ω) σ b b').re ∧
    linTrVar n ((-Complex.I) • AbCN sz s t K n j (loopFamN sz E s t K n j σ) (fun _ a => κ a) b₀ ω) ≤
        (k : ℝ) * (∑ b : Fin k → Zd d (sz.L n), ∑ b' : Fin k → Zd d (sz.L n),
          κ b * (starRingEnd ℂ) (κ b') *
            sz.STeeM n (E n) (gridTime s t K n (j + 1)) (pathH sz s t K n j ω) σ b b').re := by
  have hK : K n ≠ 0 := by omega
  have hu0 := difRepTail_gridTime_nonneg (K := K) hs0 hst (j + 1)
  have hu1 : gridTime s t K n (j + 1) < 1 := (difRepTail_gridTime_le hst hK hj).trans_lt ht1
  have hΦ : ∀ a, HermTestFun sz n (loopFamN sz E s t K n j σ a) := fun a =>
    (hermTestFunLoopN sz k n (E n) (gridTime s t K n (j + 1)) hE hu0 hu1 σ a).1
  have hH := pathH_isHermitian sz s t K n j ω
  set D : CoordF d (sz.L n) (sz.W n) → ℂ := fun c => ∑ b, κ b *
    dirDerivN (loopFamN sz E s t K n j σ b) (pathH sz s t K n j ω)
      (coordinateMatrix d (sz.L n) (sz.W n) c) with hD
  have hDeq : ∀ c, Matrix.trace (AbCN sz s t K n j (loopFamN sz E s t K n j σ) (fun _ a => κ a) b₀ ω *
      coordinateMatrix d (sz.L n) (sz.W n) c) = D c :=
    fun c => difRepTail_trace_eq sz hΦ κ hH (coordinateMatrix_isHermitian _ _ _ c)
  obtain ⟨h1, h2⟩ := difRepTail_linTrVar_le sz n _ D hDeq
  have hqv := qvPropagatedN d sz n (E n) hE _ hu0 hu1 (pathH sz s t K n j ω) hH k hk σ κ
  have hqv' : ∑ c : CoordF d (sz.L n) (sz.W n), (gvarF d (sz.L n) (sz.W n) (sz.lam n) c : ℝ) *
      ‖D c‖ ^ 2 ≤ (k : ℝ) * (∑ b : Fin k → Zd d (sz.L n), ∑ b' : Fin k → Zd d (sz.L n),
          κ b * (starRingEnd ℂ) (κ b') *
            sz.STeeM n (E n) (gridTime s t K n (j + 1)) (pathH sz s t K n j ω) σ b b').re := hqv
  exact ⟨h1.trans hqv', h2.trans hqv'⟩

end ZLinear

/-! ## 5. The conditional exponential moment of a frozen linear functional, random variance

Copies (renamed with the prefix `difRepTail_`) of the private helpers of the merged `Path/Markov.lean`
(RBM3D `58bedae`, T2021): `measurable_seqXmat'` `:263`, `linTr_eq_sum` `:268`, `measurable_linTr_uncurry`
`:275`, `measurable_linTr_seqXmat` `:295`, the standard Borel instance of matrices `:319`,
`measurable_linTr_left` `:394`, `linTrVar_eq_sum` `:406`, `measurable_linTrVar` `:415`,
`mgf_linTr_seqXmat` `:425`, and the first half of `condMGF_le` `:572-604` (ports of RBM2D
`Path/Markov.lean:417-620` at `c9a24cf`; `condMGF_le` `:564`).  The new point: the conditional
expectation keeps the random variance `linTrVar n (A ω)` instead of the deterministic bound `c`. -/

section Frozen

variable {d : ℕ} {sz : Sizes d}

private theorem difRepTail_measurable_seqXmat (n : ℕ) : Measurable (Sizes.seqXmat sz n) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j =>
    (measurable_Xentry d (sz.L n) (sz.W n) i j).comp (Sizes.measurable_slice sz n)

private theorem difRepTail_linTr_eq_sum (n : ℕ)
    (A X : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    linTr n A X = ∑ i : Idx d (sz.L n) (sz.W n), ∑ k : Idx d (sz.L n) (sz.W n),
      (A i k * X k i).re := by
  unfold linTr
  rw [Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]

private theorem difRepTail_measurable_linTr_uncurry (n : ℕ) :
    Measurable (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ × Sizes.SeqΩ sz =>
      linTr n p.1 (Sizes.seqXmat sz n p.2)) := by
  have heq : (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ × Sizes.SeqΩ sz =>
      linTr n p.1 (Sizes.seqXmat sz n p.2))
      = fun p => ∑ i : Idx d (sz.L n) (sz.W n), ∑ k : Idx d (sz.L n) (sz.W n),
          (p.1 i k * Sizes.seqXmat sz n p.2 k i).re :=
    funext fun p => difRepTail_linTr_eq_sum n p.1 (Sizes.seqXmat sz n p.2)
  rw [heq]
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ => ?_
  have hM : Measurable
      (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ × Sizes.SeqΩ sz => p.1 i k) :=
    Measurable.eval_matrix (i := i) (j := k) measurable_fst
  have hX : Measurable
      (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ × Sizes.SeqΩ sz =>
        Sizes.seqXmat sz n p.2 k i) :=
    Measurable.eval_matrix (i := k) (j := i) ((difRepTail_measurable_seqXmat n).comp measurable_snd)
  exact Complex.measurable_re.comp (hM.mul hX)

private theorem difRepTail_measurable_linTr_seqXmat (n : ℕ)
    (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    Measurable (fun x : Sizes.SeqΩ sz => linTr n A (Sizes.seqXmat sz n x)) := by
  have heq : (fun x : Sizes.SeqΩ sz => linTr n A (Sizes.seqXmat sz n x))
      = fun x => ∑ i : Idx d (sz.L n) (sz.W n), ∑ k : Idx d (sz.L n) (sz.W n),
          (A i k * Sizes.seqXmat sz n x k i).re :=
    funext fun x => difRepTail_linTr_eq_sum n A (Sizes.seqXmat sz n x)
  rw [heq]
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ => ?_
  exact Complex.measurable_re.comp
    (measurable_const.mul (Measurable.eval_matrix (i := k) (j := i) (difRepTail_measurable_seqXmat n)))

private theorem difRepTail_measurable_linTr_left (n : ℕ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    Measurable (fun A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => linTr n A M) := by
  have heq : (fun A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => linTr n A M)
      = fun A => ∑ i : Idx d (sz.L n) (sz.W n), ∑ k : Idx d (sz.L n) (sz.W n), (A i k * M k i).re :=
    funext fun A => difRepTail_linTr_eq_sum n A M
  rw [heq]
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ => ?_
  exact Complex.measurable_re.comp
    ((Matrix.measurable_apply (i := i) (j := k)).mul measurable_const)

private theorem difRepTail_linTrVar_eq_sum (n : ℕ)
    (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    linTrVar n A = ∑ c ∈ coordFinset n,
      (linTr n A (Sizes.seqXmat sz n (Pi.single c 1))) ^ 2 * (Sizes.seqGvar sz c : ℝ) := by
  unfold linTrVar linVar
  push_cast [NNReal.coe_mk]
  rfl

private theorem difRepTail_measurable_linTrVar (n : ℕ) :
    Measurable (fun A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      linTrVar n A) := by
  have heq : (fun A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => linTrVar n A)
      = fun A => ∑ c ∈ coordFinset n,
          (linTr n A (Sizes.seqXmat sz n (Pi.single c 1))) ^ 2 * (Sizes.seqGvar sz c : ℝ) :=
    funext (difRepTail_linTrVar_eq_sum n)
  rw [heq]
  exact Finset.measurable_sum _ fun c _ =>
    ((difRepTail_measurable_linTr_left n _).pow_const 2).mul_const _

private theorem difRepTail_mgf_linTr_seqXmat (n : ℕ)
    (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (r : ℝ) :
    mgf (fun x => linTr n A (Sizes.seqXmat sz n x)) (Sizes.seqP sz) r
      = Real.exp (linTrVar n A * r ^ 2 / 2) := by
  have hmeas : Measurable (fun x : Sizes.SeqΩ sz => linTr n A (Sizes.seqXmat sz n x)) :=
    difRepTail_measurable_linTr_seqXmat n A
  have hlaw : HasLaw (fun x => linTr n A (Sizes.seqXmat sz n x))
      (gaussianReal 0 (NNReal.mk (linTrVar n A) (linTrVar_nonneg n A))) (Sizes.seqP sz) :=
    ⟨hmeas.aemeasurable, map_linTr_seqXmat n A⟩
  rw [mgf_gaussianReal hlaw]
  congr 1
  push_cast [NNReal.coe_mk]
  ring

private instance difRepTail_standardBorelMatrix (n : ℕ) :
    StandardBorelSpace (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
  inferInstanceAs (StandardBorelSpace (Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ))

/-- **The conditional exponential moment of the frozen linear functional**, with the random
variance: for a `filt sz j`-measurable direction `A`, a.e. `𝔼[exp (r √Δ linTr (A) X_{j+1}) | F_j]
= exp (linTrVar (A ω) (r √Δ)² / 2)`; `condExp_freeze` and the Gaussian mgf (the first half of the
merged `condMGF_le`, `Path/Markov.lean:572-604`). -/
private theorem difRepTail_condExp_exp {n j : ℕ}
    {A : PathΩ sz → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hA : Measurable[filt sz j] A) (Δ r : ℝ)
    (hInt : Integrable (fun ω : PathΩ sz => Real.exp (r * (Real.sqrt Δ *
      linTr n (A ω) (Sizes.seqXmat sz n (ω (j + 1)))))) (pathP sz)) :
    (pathP sz)[fun ω : PathΩ sz => Real.exp (r * (Real.sqrt Δ *
        linTr n (A ω) (Sizes.seqXmat sz n (ω (j + 1))))) | filt sz j]
      =ᵐ[pathP sz] fun ω => Real.exp (linTrVar n (A ω) * (r * Real.sqrt Δ) ^ 2 / 2) := by
  set Gr : PathΩ sz → ℝ := fun ρ => Real.exp (r * (Real.sqrt Δ *
    linTr n (A ρ) (Sizes.seqXmat sz n (ρ (j + 1))))) with hGrdef
  set Fr : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → Sizes.SeqΩ sz → ℝ :=
    fun y x => Real.exp (r * (Real.sqrt Δ * linTr n y (Sizes.seqXmat sz n x))) with hFrdef
  have hFrmeas : Measurable
      (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ × Sizes.SeqΩ sz =>
        Fr p.1 p.2) := by
    have h1 : Measurable
        (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ × Sizes.SeqΩ sz =>
          linTr n p.1 (Sizes.seqXmat sz n p.2)) := difRepTail_measurable_linTr_uncurry n
    exact Real.measurable_exp.comp ((h1.const_mul _).const_mul _)
  have hGreq : (fun ρ : PathΩ sz => Fr (A ρ) (ρ (j + 1))) = Gr := by
    funext ρ; rw [hFrdef, hGrdef]
  have hfreeze := condExp_freeze j hA hFrmeas (hGreq ▸ hInt)
  have hRHS : (fun ρ : PathΩ sz => ∫ x, Fr (A ρ) x ∂ (Sizes.seqP sz))
      = fun ρ => Real.exp (linTrVar n (A ρ) * (r * Real.sqrt Δ) ^ 2 / 2) := by
    funext ρ
    have hmgf := difRepTail_mgf_linTr_seqXmat n (A ρ) (r * Real.sqrt Δ)
    rw [mgf] at hmgf
    rw [← hmgf]
    have hpt : ∀ x, Fr (A ρ) x
        = Real.exp ((r * Real.sqrt Δ) * linTr n (A ρ) (Sizes.seqXmat sz n x)) := by
      intro x; rw [hFrdef]; ring_nf
    simp_rw [hpt]
  rw [hRHS] at hfreeze
  rw [hGreq] at hfreeze
  exact hfreeze

end Frozen

/-! ## 6. The crude bounds of step 3(a) (Amend 2 (i), public `difRep2_*`) -/

section Crude

/-- The two lists of `STeeLoop` at a cut edge `1 ≤ k ≤ m` have length `2m + 2`. -/
private theorem difRepTail_STeeLoop_length {α : Type*} {m : ℕ} (σ : Fin m → Bool)
    (a a' : Fin m → α) {k : ℕ} (hk1 : 1 ≤ k) (hkm : k ≤ m) (b b' : α) :
    (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b').σ.length = 2 * m + 2 ∧
    (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b').a.length = 2 * m + 2 := by
  simp only [STeeLoop, List.length_append, List.length_drop, List.length_take, List.length_reverse,
    List.length_map, List.length_ofFn, List.length_cons, List.length_nil]
  omega

/-- `Σ_{b,b'} ‖S^{(B)}_{bb'}‖ = L^d` (copy of the private `nqGood1_sum_sum_norm_SB`,
`Induction/NQGood1.lean`, RBM3D `691566a`). -/
private theorem difRepTail_sum_sum_norm_SB {d L : ℕ} [NeZero L] (g : ℝ) (hL : 3 ≤ L) :
    ∑ b : Zd d L, ∑ b' : Zd d L, ‖SB d L g b b'‖ = (L : ℝ) ^ d := by
  simp only [sum_norm_SB_row d L g hL, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have : Fintype.card (Zd d L) = L ^ d := by simp [Zd, ZMod.card]
  rw [this]
  push_cast
  rfl

/-- **Amend 2 (i), `difRep2_norm_STeeM_le`** (step 3(a) of T2180; `docs/tickets/T2180-amend-2.md`): for
Hermitian `M`, `|E| < 2` and `u < 1`, the quadratic-variation loop obeys
`‖(𝓔⊗𝓔)_{u,σ,a,a'}(M)‖ ≤ W^d m L^d η_u^{-(2m+2)} (W^{-d})^{2m+1}` (`STeeLoop` has length `2m+2`;
`norm_gloop_le_of_le_abs_im` and `Σ_{b,b'} ‖S^{(B)}_{bb'}‖ = L^d`). -/
theorem difRep2_norm_STeeM_le {d : ℕ} (sz : Sizes d) (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu1 : u < 1)
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian)
    {m : ℕ} (σ : Fin m → Bool) (a a' : Fin m → Zd d (sz.L n)) :
    ‖sz.STeeM n E u M σ a a'‖ ≤
      ((sz.W n : ℝ) ^ d) * ((m : ℝ) * (((sz.L n : ℝ) ^ d) *
        ((etaT E u)⁻¹ ^ (2 * m + 2) * (((sz.W n : ℝ) ^ d)⁻¹) ^ (2 * m + 1)))) := by
  have hη := etaT_pos hE hu1
  have hpos : 0 < (1 - u) * (mE E).im := mul_pos (by linarith) (mE_im_pos hE)
  have hz : etaT E u ≤ |(zt E u).im| := by
    rw [zt_im, abs_of_pos hpos]
    exact le_of_eq rfl
  have hMb : (blockMat d (sz.L n) (sz.W n) M).IsHermitian := hM.submatrix _
  have hW : ‖(((sz.W n : ℕ) : ℂ)) ^ d‖ = ((sz.W n : ℕ) : ℝ) ^ d := by simp
  set C : ℝ := (etaT E u)⁻¹ ^ (2 * m + 2) * (((sz.W n : ℝ) ^ d)⁻¹) ^ (2 * m + 1) with hC
  have hloop : ∀ k ∈ Finset.Icc 1 m, ∀ b b' : Zd d (sz.L n),
      ‖sz.STLIM n E u M (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b')‖ ≤ C := by
    intro k hk b b'
    have hk' := Finset.mem_Icc.1 hk
    obtain ⟨hl1, hl2⟩ := difRepTail_STeeLoop_length σ a a' hk'.1 hk'.2 b b'
    have := norm_gloop_le_of_le_abs_im (L := sz.L n) (W := sz.W n) hMb hη hz
      (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b') (hl1.trans hl2.symm)
      (by rw [hl2]; omega)
    rw [hl2] at this
    simpa [Sizes.STLIM, hC] using this
  unfold Sizes.STeeM
  rw [norm_mul, hW]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans ?_
  have hk : ∀ k ∈ Finset.Icc 1 m,
      ‖∑ b : Zd d (sz.L n), ∑ b' : Zd d (sz.L n), SB d (sz.L n) (sz.lam n) b b' *
        sz.STLIM n E u M (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b')‖ ≤
      ((sz.L n : ℝ) ^ d) * C := by
    intro k hk
    refine (norm_sum_le _ _).trans ?_
    calc ∑ b : Zd d (sz.L n), ‖∑ b' : Zd d (sz.L n), SB d (sz.L n) (sz.lam n) b b' *
          sz.STLIM n E u M (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b')‖
        ≤ ∑ b : Zd d (sz.L n), ∑ b' : Zd d (sz.L n), ‖SB d (sz.L n) (sz.lam n) b b'‖ * C := by
          refine Finset.sum_le_sum fun b _ => (norm_sum_le _ _).trans ?_
          refine Finset.sum_le_sum fun b' _ => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hloop k hk b b') (norm_nonneg _)
      _ = ((sz.L n : ℝ) ^ d) * C := by
          simp only [← Finset.sum_mul]
          rw [difRepTail_sum_sum_norm_SB (sz.lam n) (sz.three_le_L n)]
  refine (Finset.sum_le_sum hk).trans ?_
  rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]

/-- `STeeM` is measurable in the matrix argument (`walk_measurable_loopL`, `walk_measurable_blockMat`,
`Path/Walk.lean:780, 788`). -/
private theorem difRepTail_measurable_STeeM {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) {m : ℕ}
    (σ : Fin m → Bool) (a a' : Fin m → Zd d (sz.L n)) :
    Measurable (fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      sz.STeeM n E u M σ a a') := by
  unfold Sizes.STeeM
  refine measurable_const.mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun b _ =>
    Finset.measurable_sum _ fun b' _ => measurable_const.mul ?_)
  exact (walk_measurable_loopL d (sz.L n) (sz.W n) (zt E u) _).comp
    (walk_measurable_blockMat d (sz.L n) (sz.W n))

/-- **Amend 2 (i) (`docs/tickets/T2180-amend-2.md`), `difRep2_norm_STeeM_le_N`**: with `η_u ≥ 1/(16 N)`, `N = (W L)^d`,
`‖(𝓔⊗𝓔)_{u,σ,a,a'}(M)‖ ≤ m N (16 N)^{2m+2}` for Hermitian `M` (the form of step 3(a), `W^{-d} ≤ 1`). -/
theorem difRep2_norm_STeeM_le_N {d : ℕ} (sz : Sizes d) (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu1 : u < 1)
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian)
    (hη : 1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaT E u)
    {m : ℕ} (σ : Fin m → Bool) (a a' : Fin m → Zd d (sz.L n)) :
    ‖sz.STeeM n E u M σ a a'‖ ≤
      (m : ℝ) * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ (2 * m + 2) := by
  refine (difRep2_norm_STeeM_le sz n hE hu1 hM σ a a').trans ?_
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hη0 : 0 < etaT E u := etaT_pos hE hu1
  have hinv : (etaT E u)⁻¹ ≤ 16 * ((sz.size n : ℕ) : ℝ) := by
    calc (etaT E u)⁻¹ ≤ (1 / (16 * ((sz.size n : ℕ) : ℝ)))⁻¹ := inv_anti₀ (by positivity) hη
      _ = 16 * ((sz.size n : ℕ) : ℝ) := by rw [one_div, inv_inv]
  have hWd : (1 : ℝ) ≤ (sz.W n : ℝ) ^ d :=
    one_le_pow₀ (by exact_mod_cast sz.W_pos n)
  have hWinv : (((sz.W n : ℝ) ^ d)⁻¹) ^ (2 * m + 1) ≤ 1 :=
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hWd)
  have hpow : (etaT E u)⁻¹ ^ (2 * m + 2) ≤ (16 * ((sz.size n : ℕ) : ℝ)) ^ (2 * m + 2) :=
    pow_le_pow_left₀ (by positivity) hinv _
  have hsize := difRepTail_size_cast sz n
  calc ((sz.W n : ℝ) ^ d) * ((m : ℝ) * (((sz.L n : ℝ) ^ d) *
        ((etaT E u)⁻¹ ^ (2 * m + 2) * (((sz.W n : ℝ) ^ d)⁻¹) ^ (2 * m + 1))))
      ≤ ((sz.W n : ℝ) ^ d) * ((m : ℝ) * (((sz.L n : ℝ) ^ d) *
        ((16 * ((sz.size n : ℕ) : ℝ)) ^ (2 * m + 2) * 1))) := by
        gcongr
    _ = (m : ℝ) * (((sz.W n : ℝ) ^ d) * ((sz.L n : ℝ) ^ d)) *
        (16 * ((sz.size n : ℕ) : ℝ)) ^ (2 * m + 2) := by ring
    _ = (m : ℝ) * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ (2 * m + 2) := by
        rw [hsize]

/-- `eeShiftErrN` is nonnegative for `η_{u'} > 0`, `u ≤ u'`. -/
private theorem difRepTail_eeShiftErrN_nonneg {d : ℕ} (L W : ℕ) (E : ℝ) (m : ℕ) {u u' : ℝ}
    (hη : 0 ≤ etaT E u') (huu' : u ≤ u') : 0 ≤ eeShiftErrN d L W E m u u' := by
  unfold eeShiftErrN
  have := nqGood1_loopShiftErrN_nonneg hη (sub_nonneg.2 huu') d W (2 * m + 2)
  positivity

/-- **Amend 2 (i) (`docs/tickets/T2180-amend-2.md`), `difRep2_eeShiftErrN_le`**: one shift error of the pair form,
`eeShiftErrN (u, u') ≤ m (2m+2) N (16 N)^{2m+3} (u' - u)` when `η_{u'} ≥ 1/(16 N)`. -/
theorem difRep2_eeShiftErrN_le {d : ℕ} (sz : Sizes d) (n : ℕ) (E : ℝ) {u u' : ℝ} (huu' : u ≤ u')
    (hη : 1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaT E u') (m : ℕ) :
    eeShiftErrN d (sz.L n) (sz.W n) E m u u' ≤
      (m : ℝ) * (2 * m + 2) * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ (2 * m + 3) *
        (u' - u) := by
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hη0 : 0 < etaT E u' := lt_of_lt_of_le (by positivity) hη
  have hinv : (etaT E u')⁻¹ ≤ 16 * ((sz.size n : ℕ) : ℝ) := by
    calc (etaT E u')⁻¹ ≤ (1 / (16 * ((sz.size n : ℕ) : ℝ)))⁻¹ := inv_anti₀ (by positivity) hη
      _ = 16 * ((sz.size n : ℕ) : ℝ) := by rw [one_div, inv_inv]
  have hWd : (1 : ℝ) ≤ (sz.W n : ℝ) ^ d :=
    one_le_pow₀ (by exact_mod_cast sz.W_pos n)
  have hWinv : (((sz.W n : ℝ) ^ d)⁻¹) ^ (2 * m + 1) ≤ 1 :=
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hWd)
  have hpow : (etaT E u')⁻¹ ^ (2 * m + 3) ≤ (16 * ((sz.size n : ℕ) : ℝ)) ^ (2 * m + 3) :=
    pow_le_pow_left₀ (by positivity) hinv _
  have hsize := difRepTail_size_cast sz n
  have hΔ0 : 0 ≤ u' - u := sub_nonneg.2 huu'
  unfold eeShiftErrN loopShiftErrN
  have h2 : 2 * m + 2 - 1 = 2 * m + 1 := by omega
  rw [h2]
  have hcast : (((2 * m + 2 : ℕ) : ℝ)) = 2 * (m : ℝ) + 2 := by push_cast; ring
  rw [hcast]
  calc ((sz.W n : ℝ) ^ d) * ((m : ℝ) * (((sz.L n : ℝ) ^ d) *
        ((2 * (m : ℝ) + 2) * ((etaT E u')⁻¹ ^ (2 * m + 2 + 1) *
          (((sz.W n : ℝ) ^ d)⁻¹) ^ (2 * m + 1) * (u' - u)))))
      ≤ ((sz.W n : ℝ) ^ d) * ((m : ℝ) * (((sz.L n : ℝ) ^ d) *
        ((2 * (m : ℝ) + 2) * ((16 * ((sz.size n : ℕ) : ℝ)) ^ (2 * m + 3) * 1 * (u' - u))))) := by
        gcongr
    _ = (m : ℝ) * (2 * m + 2) * (((sz.W n : ℝ) ^ d) * ((sz.L n : ℝ) ^ d)) *
        (16 * ((sz.size n : ℕ) : ℝ)) ^ (2 * m + 3) * (u' - u) := by ring
    _ = _ := by rw [hsize]

/-- **Amend 2 (i) (`docs/tickets/T2180-amend-2.md`), `difRep2_eeShift_sum_le`**: the shift errors of the grid sum to
`Σ_{j<K} Δ · eeShiftErrN (u_j, u_{j+1}) ≤ m (2m+2) 16^{2m+3} N^{2m+4} Δ` (`KΔ ≤ 1`, `η_{u_{j+1}} ≥ 1/(16 N)`),
the first part of the budget `≤ N^{-D}` of step 3(a). -/
theorem difRep2_eeShift_sum_le {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n m : ℕ)
    (hst : s n ≤ t n) (hKΔ : (K n : ℝ) * gridStep s t K n ≤ 1)
    (hη : ∀ j, j + 1 ≤ K n →
      1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaT (E n) (gridTime s t K n (j + 1))) :
    ∑ j ∈ Finset.range (K n), gridStep s t K n * eeShiftErrN d (sz.L n) (sz.W n) (E n) m
        (gridTime s t K n j) (gridTime s t K n (j + 1)) ≤
      ((m : ℝ) * (2 * m + 2) * 16 ^ (2 * m + 3) * ((sz.size n : ℕ) : ℝ) ^ (2 * m + 4)) *
        gridStep s t K n := by
  have hΔ := ST_gridStep_nonneg s t K n hst
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  set X : ℝ := (m : ℝ) * (2 * m + 2) * ((sz.size n : ℕ) : ℝ) *
    (16 * ((sz.size n : ℕ) : ℝ)) ^ (2 * m + 3) with hX
  have hX0 : 0 ≤ X := by positivity
  have hXeq : X = (m : ℝ) * (2 * m + 2) * 16 ^ (2 * m + 3) * ((sz.size n : ℕ) : ℝ) ^ (2 * m + 4) := by
    rw [hX, mul_pow]
    ring
  have hterm : ∀ j ∈ Finset.range (K n), gridStep s t K n * eeShiftErrN d (sz.L n) (sz.W n) (E n) m
      (gridTime s t K n j) (gridTime s t K n (j + 1)) ≤ gridStep s t K n * (X * gridStep s t K n) := by
    intro j hj
    have hj' : j + 1 ≤ K n := Finset.mem_range.1 hj
    refine mul_le_mul_of_nonneg_left ?_ hΔ
    have hsucc := difRepTail_gridTime_succ s t K n j
    have h := difRep2_eeShiftErrN_le sz n (E n) (u := gridTime s t K n j)
      (u' := gridTime s t K n (j + 1)) (by rw [hsucc]; linarith) (hη j hj') m
    rw [hsucc] at h ⊢
    simpa using h
  calc ∑ j ∈ Finset.range (K n), gridStep s t K n * eeShiftErrN d (sz.L n) (sz.W n) (E n) m
        (gridTime s t K n j) (gridTime s t K n (j + 1))
      ≤ ∑ j ∈ Finset.range (K n), gridStep s t K n * (X * gridStep s t K n) := Finset.sum_le_sum hterm
    _ = ((K n : ℝ) * gridStep s t K n) * (X * gridStep s t K n) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
    _ ≤ 1 * (X * gridStep s t K n) :=
        mul_le_mul_of_nonneg_right hKΔ (by positivity)
    _ = X * gridStep s t K n := one_mul _
    _ = _ := by rw [hXeq]

end Crude

/-! ## 7. Target 2: the conditional exponential moment of the first-chaos increment -/

/-- **Target 2, `difRepTail_condMGF_Z`**: the conditional mgf of a weighted first-chaos increment, with its
random proxy.  For weights `κ`, the real and imaginary parts of `Σ_b κ_b Z_{j,b}` (`Z = ZvecN`, the step
`j → j+1`) are exponentially integrable and have conditional mgf at most
`exp(r² Δ k Re Σ_{b,b'} κ_b conj(κ_{b'}) (𝓔⊗𝓔)_{u_{j+1}}(H_j)_{σ,b,b'} / 2)` given `F_j` (the Gaussian
mgf with the variance `Δ linTrVar` of the frozen gradient, bounded by `qvPropagatedN`).  Route: `Σ_b κ_b Z_b
= stepZCN` of the loop family with the kernel `(·, a) ↦ κ_a` (`√Δ linTr (A_j, X_{j+1})`,
`A_j = Σ_a κ_a gradMat (𝓛_a) (H_j)`, `F_j`-measurable by `stepDecompCN`); `condExp_freeze` with the Gaussian
mgf gives the conditional mgf exactly (`difRepTail_condExp_exp`); `linTrVar ≤ k Re Σ κ κ̄ 𝓔⊗𝓔`
(`qvPropagatedN`); integrability from the deterministic bound of `difRep2_norm_STeeM_le` through
`stepDecompCN_Z_subG` at `E = univ`. -/
theorem difRepTail_condMGF_Z :
    ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ),
      |E n| < 2 → 0 ≤ s n → s n ≤ t n → t n < 1 → j + 1 ≤ K n →
      ∀ {k : ℕ}, 2 ≤ k → ∀ (σ : Fin k → Bool) (κ : (Fin k → Zd d (sz.L n)) → ℂ) (r : ℝ),
        Integrable (fun ω => Real.exp (r * (∑ b, κ b * ZvecN sz E s t K n j σ ω b).re))
          (pathP sz) ∧
        Integrable (fun ω => Real.exp (r * (∑ b, κ b * ZvecN sz E s t K n j σ ω b).im))
          (pathP sz) ∧
        (pathP sz)[fun ω => Real.exp (r * (∑ b, κ b * ZvecN sz E s t K n j σ ω b).re) | filt sz j]
          ≤ᵐ[pathP sz] (fun ω => Real.exp (r ^ 2 * (gridStep s t K n * ((k : ℝ) *
            (∑ b : Fin k → Zd d (sz.L n), ∑ b' : Fin k → Zd d (sz.L n),
              κ b * (starRingEnd ℂ) (κ b') *
              sz.STeeM n (E n) (gridTime s t K n (j + 1)) (pathH sz s t K n j ω) σ b b').re)) / 2)) ∧
        (pathP sz)[fun ω => Real.exp (r * (∑ b, κ b * ZvecN sz E s t K n j σ ω b).im) | filt sz j]
          ≤ᵐ[pathP sz] (fun ω => Real.exp (r ^ 2 * (gridStep s t K n * ((k : ℝ) *
            (∑ b : Fin k → Zd d (sz.L n), ∑ b' : Fin k → Zd d (sz.L n),
              κ b * (starRingEnd ℂ) (κ b') *
              sz.STeeM n (E n) (gridTime s t K n (j + 1)) (pathH sz s t K n j ω) σ b b').re)) / 2)) := by
  intro d sz E s t K n j hE hs0 hst ht1 hj k hk σ κ r
  have hK : K n ≠ 0 := by omega
  have hΔ := ST_gridStep_nonneg s t K n hst
  have hu0 := difRepTail_gridTime_nonneg (K := K) hs0 hst (j + 1)
  have hu1 : gridTime s t K n (j + 1) < 1 := (difRepTail_gridTime_le hst hK hj).trans_lt ht1
  set Φ := loopFamN sz E s t K n j σ with hΦdef
  have hΦ : ∀ a, HermTestFun sz n (Φ a) := fun a =>
    (hermTestFunLoopN sz k n (E n) (gridTime s t K n (j + 1)) hE hu0 hu1 σ a).1
  set η := etaT (E n) (gridTime s t K n (j + 1)) with hη
  set C₂ : ℝ := ((k * (k + 1) : ℕ) : ℝ) * (Sizes.size sz n : ℝ) * η⁻¹ ^ (k + 2) with hC₂def
  have hC₂ : ∀ a (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2 :=
    fun a M y hM hy => (hermTestFunLoopN sz k n (E n) (gridTime s t K n (j + 1)) hE hu0 hu1 σ a).2
      M y hM hy
  set U : (Fin k → Zd d (sz.L n)) → (Fin k → Zd d (sz.L n)) → ℂ := fun _ a => κ a with hU
  set b₀ : Fin k → Zd d (sz.L n) := fun _ => 0 with hb₀
  have hIntRe := integrable_stepZCN_re_of_hermTestFun sz s t K n j hΦ hC₂ hΔ U b₀
  have hIntIm := integrable_stepZCN_im_of_hermTestFun sz s t K n j hΦ hC₂ hΔ U b₀
  obtain ⟨-, hAm, -, -⟩ := stepDecompCN sz s t K n j hΦ hC₂ hΔ U b₀ hIntRe hIntIm
  -- the deterministic bound on the variance
  set S1 : ℝ := ∑ b, ‖κ b‖ with hS1
  set Bk : ℝ := ((sz.W n : ℝ) ^ d) * ((k : ℝ) * (((sz.L n : ℝ) ^ d) *
    (η⁻¹ ^ (2 * k + 2) * (((sz.W n : ℝ) ^ d)⁻¹) ^ (2 * k + 1)))) with hBk
  have hη0 : 0 < η := etaT_pos hE hu1
  have hBk0 : 0 ≤ Bk := by positivity
  set c0 : ℝ := gridStep s t K n * ((k : ℝ) * (S1 ^ 2 * Bk)) with hc0def
  have hc0 : 0 ≤ c0 := by positivity
  have hRe : ∀ ω : PathΩ sz, (∑ b : Fin k → Zd d (sz.L n), ∑ b' : Fin k → Zd d (sz.L n),
      κ b * (starRingEnd ℂ) (κ b') *
        sz.STeeM n (E n) (gridTime s t K n (j + 1)) (pathH sz s t K n j ω) σ b b').re ≤
      S1 ^ 2 * Bk := by
    intro ω
    have hH := pathH_isHermitian sz s t K n j ω
    refine (Complex.re_le_norm _).trans ?_
    refine (norm_sum_le _ _).trans ?_
    calc ∑ b : Fin k → Zd d (sz.L n), ‖∑ b' : Fin k → Zd d (sz.L n), κ b * (starRingEnd ℂ) (κ b') *
          sz.STeeM n (E n) (gridTime s t K n (j + 1)) (pathH sz s t K n j ω) σ b b'‖
        ≤ ∑ b : Fin k → Zd d (sz.L n), ∑ b' : Fin k → Zd d (sz.L n), ‖κ b‖ * ‖κ b'‖ * Bk := by
          refine Finset.sum_le_sum fun b _ => (norm_sum_le _ _).trans ?_
          refine Finset.sum_le_sum fun b' _ => ?_
          rw [norm_mul, norm_mul, Complex.norm_conj]
          exact mul_le_mul_of_nonneg_left
            (difRep2_norm_STeeM_le sz n hE hu1 hH σ b b') (by positivity)
      _ = S1 ^ 2 * Bk := by
          rw [hS1, sq, Finset.sum_mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_mul]
  have hvar : ∀ ω : PathΩ sz, linTrVar n (AbCN sz s t K n j Φ U b₀ ω) ≤ (k : ℝ) * (S1 ^ 2 * Bk) ∧
      linTrVar n ((-Complex.I) • AbCN sz s t K n j Φ U b₀ ω) ≤ (k : ℝ) * (S1 ^ 2 * Bk) := by
    intro ω
    obtain ⟨h1, h2⟩ := difRepTail_linTrVar_le_QV sz E s t K n j hE hs0 hst ht1 hj hk σ κ b₀ ω
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    exact ⟨h1.trans (mul_le_mul_of_nonneg_left (hRe ω) hk0),
      h2.trans (mul_le_mul_of_nonneg_left (hRe ω) hk0)⟩
  have hZ := stepDecompCN_Z_subG sz s t K n j hΦ U b₀ Set.univ MeasurableSet.univ c0 hc0
    (fun ω _ => mul_le_mul_of_nonneg_left (hvar ω).1 hΔ)
    (fun ω _ => mul_le_mul_of_nonneg_left (hvar ω).2 hΔ)
  -- the real and imaginary parts as frozen linear functionals
  have hre_eq : ∀ ω : PathΩ sz, (∑ b, κ b * ZvecN sz E s t K n j σ ω b).re =
      Real.sqrt (gridStep s t K n) *
        linTr n (AbCN sz s t K n j Φ U b₀ ω) (Sizes.seqXmat sz n (ω (j + 1))) := by
    intro ω
    rw [difRepTail_sum_Z_eq sz E s t K n j hE hs0 hst ht1 hj σ κ b₀ ω]
    simp only [stepZCN, stepZCN_re, stepZCN_im, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, add_zero,
      sub_self]
    rfl
  have him_eq : ∀ ω : PathΩ sz, (∑ b, κ b * ZvecN sz E s t K n j σ ω b).im =
      Real.sqrt (gridStep s t K n) *
        linTr n ((-Complex.I) • AbCN sz s t K n j Φ U b₀ ω) (Sizes.seqXmat sz n (ω (j + 1))) := by
    intro ω
    rw [difRepTail_sum_Z_eq sz E s t K n j hE hs0 hst ht1 hj σ κ b₀ ω]
    simp only [stepZCN, stepZCN_re, stepZCN_im, Complex.add_im, Complex.ofReal_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_add, one_mul]
    rfl
  have hfre : (fun ω : PathΩ sz => Real.exp (r * (∑ b, κ b * ZvecN sz E s t K n j σ ω b).re)) =
      fun ω => Real.exp (r * (Real.sqrt (gridStep s t K n) *
        linTr n (AbCN sz s t K n j Φ U b₀ ω) (Sizes.seqXmat sz n (ω (j + 1))))) :=
    funext fun ω => by rw [hre_eq]
  have hfim : (fun ω : PathΩ sz => Real.exp (r * (∑ b, κ b * ZvecN sz E s t K n j σ ω b).im)) =
      fun ω => Real.exp (r * (Real.sqrt (gridStep s t K n) *
        linTr n ((-Complex.I) • AbCN sz s t K n j Φ U b₀ ω) (Sizes.seqXmat sz n (ω (j + 1))))) :=
    funext fun ω => by rw [him_eq]
  have hIre : Integrable (fun ω : PathΩ sz => Real.exp (r * (Real.sqrt (gridStep s t K n) *
      linTr n (AbCN sz s t K n j Φ U b₀ ω) (Sizes.seqXmat sz n (ω (j + 1)))))) (pathP sz) := by
    have := hZ.1.integrable_exp_mul r
    simpa [Set.indicator_univ, stepZCN_re] using this
  have hIim : Integrable (fun ω : PathΩ sz => Real.exp (r * (Real.sqrt (gridStep s t K n) *
      linTr n ((-Complex.I) • AbCN sz s t K n j Φ U b₀ ω) (Sizes.seqXmat sz n (ω (j + 1))))))
      (pathP sz) := by
    have := hZ.2.integrable_exp_mul r
    simpa [Set.indicator_univ, stepZCN_im] using this
  have hAm' : Measurable[filt sz j] (fun ω => (-Complex.I) • AbCN sz s t K n j Φ U b₀ ω) :=
    hAm.const_smul (-Complex.I)
  have hce_re := difRepTail_condExp_exp hAm (gridStep s t K n) r hIre
  have hce_im := difRepTail_condExp_exp hAm' (gridStep s t K n) r hIim
  have hsq : (r * Real.sqrt (gridStep s t K n)) ^ 2 = r ^ 2 * gridStep s t K n := by
    rw [mul_pow, Real.sq_sqrt hΔ]
  refine ⟨by rw [hfre]; exact hIre, by rw [hfim]; exact hIim, ?_, ?_⟩
  · rw [hfre]
    refine hce_re.le.trans (Eventually.of_forall fun ω => ?_)
    simp only
    refine Real.exp_le_exp.2 ?_
    rw [hsq]
    have := (hvar ω).1
    have h1 := (difRepTail_linTrVar_le_QV sz E s t K n j hE hs0 hst ht1 hj hk σ κ b₀ ω).1
    have hrr : 0 ≤ r ^ 2 * gridStep s t K n := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h1 hrr]
  · rw [hfim]
    refine hce_im.le.trans (Eventually.of_forall fun ω => ?_)
    simp only
    refine Real.exp_le_exp.2 ?_
    rw [hsq]
    have h1 := (difRepTail_linTrVar_le_QV sz E s t K n j hE hs0 hst ht1 hj hk σ κ b₀ ω).2
    have hrr : 0 ≤ r ^ 2 * gridStep s t K n := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h1 hrr]

/-! ## 8. The first-chaos fields at a label `a`: the proxy, the threshold, the shift -/

section ZFields

variable {d : ℕ} (sz : Sizes d)

/-- The threshold increment `a_j = Δ ‖(𝓔⊗𝓔)_{u_j}(H_j)_{σ,a,a}‖` of the pin of `GridRepTailNAt`. -/
private def difRepTail_aSeq (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ} (σ : Fin m → Bool)
    (a : Fin m → Zd d (sz.L n)) (j : ℕ) (ω : PathΩ sz) : ℝ :=
  gridStep s t K n * ‖sz.STeeM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) σ a a‖

/-- The proxy `v_j = Δ m Re (𝓔⊗𝓔)_{u_{j+1}}(H_j)_{σ,a,a}` of `Re Z_{j,a}` and `Im Z_{j,a}`
(`difRepTail_condMGF_Z` at `κ = δ_a`). -/
private def difRepTail_vSeq (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ} (σ : Fin m → Bool)
    (a : Fin m → Zd d (sz.L n)) (j : ℕ) (ω : PathΩ sz) : ℝ :=
  gridStep s t K n * ((m : ℝ) *
    (sz.STeeM n (E n) (gridTime s t K n (j + 1)) (pathH sz s t K n j ω) σ a a).re)

/-- The deterministic shift slack `e_j = Δ · eeShiftErrN (u_j, u_{j+1})`. -/
private def difRepTail_eSeq (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (m : ℕ) (j : ℕ) : ℝ :=
  gridStep s t K n * eeShiftErrN d (sz.L n) (sz.W n) (E n) m (gridTime s t K n j)
    (gridTime s t K n (j + 1))

/-- The point mass `κ = δ_a` on the labels. -/
private def difRepTail_delta {n m : ℕ} (a : Fin m → Zd d (sz.L n)) :
    (Fin m → Zd d (sz.L n)) → ℂ :=
  fun b => if b = a then 1 else 0

private theorem difRepTail_delta_sum {n m : ℕ} (a : Fin m → Zd d (sz.L n))
    (g : (Fin m → Zd d (sz.L n)) → ℂ) :
    ∑ b, difRepTail_delta sz a b * g b = g a := by
  simp [difRepTail_delta]

private theorem difRepTail_delta_double_sum {n m : ℕ} (a : Fin m → Zd d (sz.L n))
    (f : (Fin m → Zd d (sz.L n)) → (Fin m → Zd d (sz.L n)) → ℂ) :
    ∑ b, ∑ b', difRepTail_delta sz a b * (starRingEnd ℂ) (difRepTail_delta sz a b') * f b b' =
      f a a := by
  simp [difRepTail_delta]

/-- `Re (𝓔⊗𝓔)_{u,σ,a,a}(M) ≥ 0` for Hermitian `M` (the left side of `qvPropagatedN` at `κ = δ_a` is a
sum of nonnegative terms). -/
private theorem difRepTail_re_STeeM_nonneg (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u)
    (hu1 : u < 1) {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hM : M.IsHermitian) {m : ℕ} (hm : 2 ≤ m) (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) :
    0 ≤ (sz.STeeM n E u M σ a a).re := by
  have h := qvPropagatedN d sz n E hE u hu0 hu1 M hM m hm σ (difRepTail_delta sz a)
  rw [difRepTail_delta_double_sum sz a (fun b b' => sz.STeeM n E u M σ b b')] at h
  have hnn : 0 ≤ ∑ c : CoordF d (sz.L n) (sz.W n), (gvarF d (sz.L n) (sz.W n) (sz.lam n) c : ℝ) *
      ‖∑ b : Fin m → Zd d (sz.L n), difRepTail_delta sz a b *
        loopDerivN d (sz.L n) (sz.W n) E u M (coordinateMatrix d (sz.L n) (sz.W n) c) σ b‖ ^ 2 :=
    Finset.sum_nonneg fun c _ => mul_nonneg (gvarF d (sz.L n) (sz.W n) (sz.lam n) c).2
      (sq_nonneg _)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  exact nonneg_of_mul_nonneg_right (hnn.trans h) hm0

private theorem difRepTail_aSeq_nonneg (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hst : s n ≤ t n)
    {m : ℕ} (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) (j : ℕ) (ω : PathΩ sz) :
    0 ≤ difRepTail_aSeq sz E s t K n σ a j ω :=
  mul_nonneg (ST_gridStep_nonneg s t K n hst) (norm_nonneg _)

private theorem difRepTail_vSeq_nonneg (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n)
    {m : ℕ} (hm : 2 ≤ m) (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) (ω : PathΩ sz) :
    0 ≤ difRepTail_vSeq sz E s t K n σ a j ω := by
  have hK : K n ≠ 0 := by omega
  have hu0 := difRepTail_gridTime_nonneg (K := K) hs0 hst (j + 1)
  have hu1 : gridTime s t K n (j + 1) < 1 := (difRepTail_gridTime_le hst hK hj).trans_lt ht1
  have := difRepTail_re_STeeM_nonneg sz n hE hu0 hu1 (pathH_isHermitian sz s t K n j ω) hm σ a
  unfold difRepTail_vSeq
  exact mul_nonneg (ST_gridStep_nonneg s t K n hst) (mul_nonneg (Nat.cast_nonneg _) this)

private theorem difRepTail_eSeq_nonneg (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n) (m : ℕ) :
    0 ≤ difRepTail_eSeq sz E s t K n m j := by
  have hK : K n ≠ 0 := by omega
  have hu1 : gridTime s t K n (j + 1) < 1 := (difRepTail_gridTime_le hst hK hj).trans_lt ht1
  have hsucc := difRepTail_gridTime_succ s t K n j
  have hΔ := ST_gridStep_nonneg s t K n hst
  unfold difRepTail_eSeq
  refine mul_nonneg hΔ (difRepTail_eeShiftErrN_nonneg _ _ _ _ (etaT_pos hE hu1).le ?_)
  rw [hsucc]; linarith

/-- The proxy is bounded by `m (a_j + e_j)`: the shift `u_j → u_{j+1}` costs `e_j`
(`norm_STeeM_shiftN_le`). -/
private theorem difRepTail_vSeq_le (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n)
    {m : ℕ} (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) (ω : PathΩ sz) :
    difRepTail_vSeq sz E s t K n σ a j ω ≤
      (m : ℝ) * (difRepTail_aSeq sz E s t K n σ a j ω + difRepTail_eSeq sz E s t K n m j) := by
  have hK : K n ≠ 0 := by omega
  have hu1 : gridTime s t K n (j + 1) < 1 := (difRepTail_gridTime_le hst hK hj).trans_lt ht1
  have hsucc := difRepTail_gridTime_succ s t K n j
  have hΔ := ST_gridStep_nonneg s t K n hst
  have hH := pathH_isHermitian sz s t K n j ω
  have hshift := norm_STeeM_shiftN_le sz n hE hH (u := gridTime s t K n j)
    (u' := gridTime s t K n (j + 1)) (by rw [hsucc]; linarith) hu1 σ a a
  have h1 : (sz.STeeM n (E n) (gridTime s t K n (j + 1)) (pathH sz s t K n j ω) σ a a).re ≤
      ‖sz.STeeM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) σ a a‖ +
        eeShiftErrN d (sz.L n) (sz.W n) (E n) m (gridTime s t K n j) (gridTime s t K n (j + 1)) := by
    calc (sz.STeeM n (E n) (gridTime s t K n (j + 1)) (pathH sz s t K n j ω) σ a a).re
        ≤ ‖sz.STeeM n (E n) (gridTime s t K n (j + 1)) (pathH sz s t K n j ω) σ a a‖ :=
          Complex.re_le_norm _
      _ ≤ ‖sz.STeeM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) σ a a‖ +
          ‖sz.STeeM n (E n) (gridTime s t K n (j + 1)) (pathH sz s t K n j ω) σ a a -
            sz.STeeM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) σ a a‖ := by
          have := norm_add_le (sz.STeeM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) σ a a)
            (sz.STeeM n (E n) (gridTime s t K n (j + 1)) (pathH sz s t K n j ω) σ a a -
              sz.STeeM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) σ a a)
          simpa using this
      _ ≤ _ := add_le_add le_rfl hshift
  unfold difRepTail_vSeq difRepTail_aSeq difRepTail_eSeq
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  calc gridStep s t K n * ((m : ℝ) *
        (sz.STeeM n (E n) (gridTime s t K n (j + 1)) (pathH sz s t K n j ω) σ a a).re)
      ≤ gridStep s t K n * ((m : ℝ) *
        (‖sz.STeeM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) σ a a‖ +
        eeShiftErrN d (sz.L n) (sz.W n) (E n) m (gridTime s t K n j) (gridTime s t K n (j + 1)))) := by
        gcongr
    _ = (m : ℝ) * (gridStep s t K n * ‖sz.STeeM n (E n) (gridTime s t K n j)
          (pathH sz s t K n j ω) σ a a‖ + gridStep s t K n * eeShiftErrN d (sz.L n) (sz.W n) (E n) m
          (gridTime s t K n j) (gridTime s t K n (j + 1))) := by ring

/-- `ω ↦ a_j(ω)` and `ω ↦ v_j(ω)` are `filt sz j`-strongly measurable. -/
private theorem difRepTail_aSeq_sm (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    {m : ℕ} (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) :
    StronglyMeasurable[filt sz j] (difRepTail_aSeq sz E s t K n σ a j) := by
  have hH := pathH_measurable_filt sz s t K n j
  have hS : Measurable[filt sz j] (fun ω => sz.STeeM n (E n) (gridTime s t K n j)
      (pathH sz s t K n j ω) σ a a) :=
    (difRepTail_measurable_STeeM sz n (E n) (gridTime s t K n j) σ a a).comp hH
  exact hS.stronglyMeasurable.norm.const_mul _

private theorem difRepTail_vSeq_sm (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    {m : ℕ} (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) :
    StronglyMeasurable[filt sz j] (difRepTail_vSeq sz E s t K n σ a j) := by
  have hH := pathH_measurable_filt sz s t K n j
  have hS : Measurable[filt sz j] (fun ω => sz.STeeM n (E n) (gridTime s t K n (j + 1))
      (pathH sz s t K n j ω) σ a a) :=
    (difRepTail_measurable_STeeM sz n (E n) (gridTime s t K n (j + 1)) σ a a).comp hH
  exact ((Complex.measurable_re.comp hS).stronglyMeasurable.const_mul _).const_mul _

/-- **The mgf facts of `Re Z_{j,a}`, `Im Z_{j,a}` with the proxy `v_j`** (`difRepTail_condMGF_Z` at
`κ = δ_a`). -/
private theorem difRepTail_Z_mgf (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n)
    {m : ℕ} (hm : 2 ≤ m) (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) (r : ℝ) :
    Integrable (fun ω => Real.exp (r * (ZvecN sz E s t K n j σ ω a).re)) (pathP sz) ∧
    Integrable (fun ω => Real.exp (r * (ZvecN sz E s t K n j σ ω a).im)) (pathP sz) ∧
    (pathP sz)[fun ω => Real.exp (r * (ZvecN sz E s t K n j σ ω a).re) | filt sz j]
      ≤ᵐ[pathP sz] (fun ω => Real.exp (r ^ 2 * difRepTail_vSeq sz E s t K n σ a j ω / 2)) ∧
    (pathP sz)[fun ω => Real.exp (r * (ZvecN sz E s t K n j σ ω a).im) | filt sz j]
      ≤ᵐ[pathP sz] (fun ω => Real.exp (r ^ 2 * difRepTail_vSeq sz E s t K n σ a j ω / 2)) := by
  obtain ⟨h1, h2, h3, h4⟩ := difRepTail_condMGF_Z sz E s t K n j hE hs0 hst ht1 hj hm σ
    (difRepTail_delta sz a) r
  have e1 : ∀ ω : PathΩ sz, (∑ b, difRepTail_delta sz a b * ZvecN sz E s t K n j σ ω b) =
      ZvecN sz E s t K n j σ ω a := fun ω => difRepTail_delta_sum sz a _
  have e2 : ∀ ω : PathΩ sz, gridStep s t K n * ((m : ℝ) *
      (∑ b : Fin m → Zd d (sz.L n), ∑ b' : Fin m → Zd d (sz.L n),
        difRepTail_delta sz a b * (starRingEnd ℂ) (difRepTail_delta sz a b') *
        sz.STeeM n (E n) (gridTime s t K n (j + 1)) (pathH sz s t K n j ω) σ b b').re) =
      difRepTail_vSeq sz E s t K n σ a j ω := fun ω => by
    rw [difRepTail_delta_double_sum sz a (fun b b' =>
      sz.STeeM n (E n) (gridTime s t K n (j + 1)) (pathH sz s t K n j ω) σ b b')]
    rfl
  simp only [e1, e2] at h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-- `Re Z_{j,a}` and `Im Z_{j,a}` are `filt sz (j+1)`-strongly measurable. -/
private theorem difRepTail_Zre_sm (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {m : ℕ} (σ : Fin m → Bool)
    (a : Fin m → Zd d (sz.L n)) :
    StronglyMeasurable[filt sz (j + 1)] (fun ω => (ZvecN sz E s t K n j σ ω a).re) :=
  Complex.continuous_re.comp_stronglyMeasurable ((continuous_apply a).comp_stronglyMeasurable
    (gridAsm_stronglyMeasurable_ZvecN sz E s t K n j σ))

private theorem difRepTail_Zim_sm (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {m : ℕ} (σ : Fin m → Bool)
    (a : Fin m → Zd d (sz.L n)) :
    StronglyMeasurable[filt sz (j + 1)] (fun ω => (ZvecN sz E s t K n j σ ω a).im) :=
  Complex.continuous_im.comp_stronglyMeasurable ((continuous_apply a).comp_stronglyMeasurable
    (gridAsm_stronglyMeasurable_ZvecN sz E s t K n j σ))

/-- The proxy is at most `Δ m (m N (16 N)^{2m+2})` when `η_{u_{j+1}} ≥ 1/(16 N)` (the crude bound
`difRep2_norm_STeeM_le_N`). -/
private theorem difRepTail_vSeq_le_crude (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n)
    {m : ℕ} (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n))
    (hη : 1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaT (E n) (gridTime s t K n (j + 1)))
    (ω : PathΩ sz) :
    difRepTail_vSeq sz E s t K n σ a j ω ≤ gridStep s t K n * ((m : ℝ) * ((m : ℝ) *
      ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ (2 * m + 2))) := by
  have hK : K n ≠ 0 := by omega
  have hu1 : gridTime s t K n (j + 1) < 1 := (difRepTail_gridTime_le hst hK hj).trans_lt ht1
  have hΔ := ST_gridStep_nonneg s t K n hst
  have h1 := difRep2_norm_STeeM_le_N sz n hE hu1 (pathH_isHermitian sz s t K n j ω) hη σ a a
  unfold difRepTail_vSeq
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  gcongr
  exact (Complex.re_le_norm _).trans h1

/-- **The `Z` part of the tail**, through the peeling lemma `difRep2_peel` (`ζ_j = Z_{j,a}`,
`a_j = Δ ‖(𝓔⊗𝓔)_{u_j}(H_j)_{σ,a,a}‖`, `v_j = Δ m Re (𝓔⊗𝓔)_{u_{j+1}}(H_j)_{σ,a,a}`,
`e_j = Δ eeShiftErrN`, `c = m`). -/
private theorem difRepTail_Z_tail (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1)
    {m : ℕ} (hm : 2 ≤ m) (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n))
    (Lmax : ℕ) {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 ≤ ρ)
    (hesum : ∑ j ∈ Finset.range (K n), difRepTail_eSeq sz E s t K n m j ≤ δ)
    (haL : ∀ ω, ∑ j ∈ Finset.range (K n), difRepTail_aSeq sz E s t K n σ a j ω ≤ 2 ^ Lmax * δ) :
    (pathP sz).real {ω | ∃ k, k ≤ K n ∧
        ρ * (∑ j ∈ Finset.range k, difRepTail_aSeq sz E s t K n σ a j ω + δ) ^ (1 / 2 : ℝ) <
          ‖∑ j ∈ Finset.range k, ZvecN sz E s t K n j σ ω a‖} ≤
      ((Lmax : ℝ) + 1) * (4 * Real.exp (-ρ ^ 2 / (16 * m))) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  exact difRep2_peel (pathP sz) (filt sz) (fun j ω => ZvecN sz E s t K n j σ ω a)
    (fun j => difRepTail_aSeq sz E s t K n σ a j) (fun j => difRepTail_vSeq sz E s t K n σ a j)
    (fun j => difRepTail_eSeq sz E s t K n m j) (K n) Lmax (m : ℝ) δ ρ hm0 hδ hρ
    (fun j _ => difRepTail_Zre_sm sz E s t K n j σ a)
    (fun j _ => difRepTail_Zim_sm sz E s t K n j σ a)
    (fun j _ => difRepTail_aSeq_sm sz E s t K n j σ a)
    (fun j _ => difRepTail_vSeq_sm sz E s t K n j σ a)
    (fun j _ ω => difRepTail_aSeq_nonneg sz E s t K n hst σ a j ω)
    (fun j hj ω => difRepTail_vSeq_nonneg sz E s t K n j hE hs0 hst ht1 hj hm σ a ω)
    (fun j hj => difRepTail_eSeq_nonneg sz E s t K n j hE hs0 hst ht1 hj m)
    (fun j hj ω => difRepTail_vSeq_le sz E s t K n j hE hs0 hst ht1 hj σ a ω)
    hesum haL
    (fun j hj r => (difRepTail_Z_mgf sz E s t K n j hE hs0 hst ht1 hj hm σ a r).1)
    (fun j hj r => (difRepTail_Z_mgf sz E s t K n j hE hs0 hst ht1 hj hm σ a r).2.1)
    (fun j hj r => (difRepTail_Z_mgf sz E s t K n j hE hs0 hst ht1 hj hm σ a r).2.2.1)
    (fun j hj r => (difRepTail_Z_mgf sz E s t K n j hE hs0 hst ht1 hj hm σ a r).2.2.2)

end ZFields

/-! ## 9. The second-order part `Y`: Doob's `L²` maximal inequality -/

section YPart

variable {d : ℕ} (sz : Sizes d)

/-- The stopped weighted increment at `τ ≡ K n`, `κ = δ_a`, is `Y_{j,a}` for `j < K n`. -/
private theorem difRepTail_stopW_eq (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hj : j < K n) {m : ℕ}
    (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) (ω : PathΩ sz) :
    AzumaProxyN_stopW sz E s t K n j σ (difRepTail_delta sz a) (fun _ => K n) ω =
      YvecN sz E s t K n j σ ω a := by
  unfold AzumaProxyN_stopW
  have hset : {ω' : PathΩ sz | j < (fun _ => K n) ω'} = Set.univ := by
    ext ω'; simpa using hj
  rw [hset, Set.indicator_univ]
  exact difRepTail_delta_sum sz a (fun b => YvecN sz E s t K n j σ ω b)

/-- **The `Y` part of the tail**: for `x > 0`, with `C2 = m (m+1) N (16 N)^{m+2}` and any `P ≥ 2000 C2² N⁸`,
`μ (∃ k ≤ K, x ≤ |Σ_{j<k} Y_{j,a}|) ≤ 4 K Δ² P / x²` (`AzumaProxyN_YfieldsW` at `κ = δ_a`, `τ ≡ K n`,
and `difRepTail_doob_tail` for `Re` and `Im`). -/
private theorem difRepTail_Y_tail (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1)
    {m : ℕ} (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n))
    (hη : ∀ j, j + 1 ≤ K n →
      1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaT (E n) (gridTime s t K n (j + 1)))
    {P : ℝ} (hP : 2000 * (((m * (m + 1) : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) *
        (16 * ((sz.size n : ℕ) : ℝ)) ^ (m + 2)) ^ 2 * ((sz.size n : ℕ) : ℝ) ^ 8 ≤ P)
    {x : ℝ} (hx : 0 < x) :
    (pathP sz).real {ω | ∃ k, k ≤ K n ∧ x ≤ ‖∑ j ∈ Finset.range k, YvecN sz E s t K n j σ ω a‖} ≤
      4 * ((K n : ℝ) * (gridStep s t K n ^ 2 * P)) / x ^ 2 := by
  have hΔ := ST_gridStep_nonneg s t K n hst
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN1 : 1 ≤ N := by rw [hN]; exact_mod_cast sz.one_le_size n
  set C2 : ℝ := ((m * (m + 1) : ℕ) : ℝ) * N * (16 * N) ^ (m + 2) with hC2def
  have hC20 : 0 ≤ C2 := by positivity
  have hτ : ∀ j, MeasurableSet[filt sz j] {ω : PathΩ sz | j < (fun _ => K n) ω} := fun j =>
    MeasurableSet.const _
  have hrow : ∑ c, ‖difRepTail_delta sz a c‖ ≤ 1 := by
    have : ∀ c, ‖difRepTail_delta sz a c‖ = if c = a then (1 : ℝ) else 0 := by
      intro c
      by_cases h : c = a <;> simp [difRepTail_delta, h]
    simp [this]
  -- the moment fields of `Y_{j,a}` for `j < K n`
  have hfields : ∀ j < K n,
      (pathP sz)[fun ω => (YvecN sz E s t K n j σ ω a).re | filt sz j] =ᵐ[pathP sz] 0 ∧
      (pathP sz)[fun ω => (YvecN sz E s t K n j σ ω a).im | filt sz j] =ᵐ[pathP sz] 0 ∧
      Integrable (fun ω => (YvecN sz E s t K n j σ ω a).re ^ 4) (pathP sz) ∧
      Integrable (fun ω => (YvecN sz E s t K n j σ ω a).im ^ 4) (pathP sz) ∧
      (pathP sz)[fun ω => (YvecN sz E s t K n j σ ω a).re ^ 2 | filt sz j]
        ≤ᵐ[pathP sz] (fun _ => gridStep s t K n ^ 2 * P) ∧
      (pathP sz)[fun ω => (YvecN sz E s t K n j σ ω a).im ^ 2 | filt sz j]
        ≤ᵐ[pathP sz] (fun _ => gridStep s t K n ^ 2 * P) := by
    intro j hj
    have hj' : j + 1 ≤ K n := hj
    have hK : K n ≠ 0 := by omega
    have hu0 := difRepTail_gridTime_nonneg (K := K) hs0 hst (j + 1)
    have hu1 : gridTime s t K n (j + 1) < 1 := (difRepTail_gridTime_le hst hK hj').trans_lt ht1
    have hη0 : 0 < etaT (E n) (gridTime s t K n (j + 1)) := etaT_pos hE hu1
    have hinv : (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ≤ 16 * N := by
      calc (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ≤ (1 / (16 * N))⁻¹ :=
            inv_anti₀ (by positivity) (hη j hj')
        _ = 16 * N := by rw [one_div, inv_inv]
    have hC2 : ∀ (a' : Fin m → Zd d (sz.L n))
        (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), M.IsHermitian →
        y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (loopFamN sz E s t K n j σ a')) M y y‖ ≤
          C2 * ‖y‖ ^ 2 := by
      intro a' M y hM hy
      refine ((hermTestFunLoopN sz m n (E n) (gridTime s t K n (j + 1)) hE hu0 hu1 σ a').2 M y hM
        hy).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [hC2def]
      gcongr
    have hP' : 2000 * ((1 : ℝ) * C2) ^ 2 * (sz.size n : ℝ) ^ 8 ≤ P := by
      simpa [hC2def, hN, one_mul] using hP
    have h := AzumaProxyN_YfieldsW sz E s t K n j hE hs0 hst ht1 hj' σ (difRepTail_delta sz a)
      zero_le_one hC20 hrow hC2 hP' (fun _ => K n) hτ
    simp only [difRepTail_stopW_eq sz E s t K n j hj σ a] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩
  have hYm : ∀ j, StronglyMeasurable[filt sz (j + 1)] (fun ω => YvecN sz E s t K n j σ ω a) :=
    fun j => (continuous_apply a).comp_stronglyMeasurable
      (gridAsm_stronglyMeasurable_YvecN sz E s t K n j σ)
  have hxs : 0 < x / Real.sqrt 2 := div_pos hx (Real.sqrt_pos.2 (by norm_num))
  have hq : ∀ (F : ℕ → PathΩ sz → ℝ) (j : ℕ), j < K n →
      (pathP sz)[fun ω => F j ω ^ 2 | filt sz j] ≤ᵐ[pathP sz] (fun _ => gridStep s t K n ^ 2 * P) →
      ∫ ω, (F j ω) ^ 2 ∂(pathP sz) ≤ gridStep s t K n ^ 2 * P := by
    intro F j hj h5
    rw [← integral_condExp ((filt sz).le j) (f := fun ω => F j ω ^ 2)]
    calc ∫ ω, ((pathP sz)[fun ω => F j ω ^ 2 | filt sz j]) ω ∂(pathP sz)
        ≤ ∫ _ω, gridStep s t K n ^ 2 * P ∂(pathP sz) :=
          integral_mono_ae integrable_condExp (integrable_const _) h5
      _ = gridStep s t K n ^ 2 * P := by simp
  have hRe := difRepTail_doob_tail (pathP sz) (filt sz) (fun j ω => (YvecN sz E s t K n j σ ω a).re)
    (K n) (gridStep s t K n ^ 2 * P) (x / Real.sqrt 2)
    (fun j _ => Complex.continuous_re.comp_stronglyMeasurable (hYm j))
    (fun j hj => difRepTail_memLp_two_of_pow4
      ((Complex.continuous_re.comp_stronglyMeasurable
        ((hYm j).mono ((filt sz).le (j + 1)))).aestronglyMeasurable) (hfields j hj).2.2.1)
    (fun j hj => (hfields j hj).1)
    (fun j hj => hq (fun j ω => (YvecN sz E s t K n j σ ω a).re) j hj (hfields j hj).2.2.2.2.1)
    hxs
  have hIm := difRepTail_doob_tail (pathP sz) (filt sz) (fun j ω => (YvecN sz E s t K n j σ ω a).im)
    (K n) (gridStep s t K n ^ 2 * P) (x / Real.sqrt 2)
    (fun j _ => Complex.continuous_im.comp_stronglyMeasurable (hYm j))
    (fun j hj => difRepTail_memLp_two_of_pow4
      ((Complex.continuous_im.comp_stronglyMeasurable
        ((hYm j).mono ((filt sz).le (j + 1)))).aestronglyMeasurable) (hfields j hj).2.2.2.1)
    (fun j hj => (hfields j hj).2.1)
    (fun j hj => hq (fun j ω => (YvecN sz E s t K n j σ ω a).im) j hj (hfields j hj).2.2.2.2.2)
    hxs
  have hsub : {ω | ∃ k, k ≤ K n ∧ x ≤ ‖∑ j ∈ Finset.range k, YvecN sz E s t K n j σ ω a‖} ⊆
      {ω | ∃ k, k ≤ K n ∧ x / Real.sqrt 2 ≤
        |∑ j ∈ Finset.range k, (YvecN sz E s t K n j σ ω a).re|} ∪
      {ω | ∃ k, k ≤ K n ∧ x / Real.sqrt 2 ≤
        |∑ j ∈ Finset.range k, (YvecN sz E s t K n j σ ω a).im|} := by
    intro ω hω
    obtain ⟨k, hk, hxk⟩ := hω
    have h1 := Complex.norm_le_sqrt_two_mul_max (∑ j ∈ Finset.range k, YvecN sz E s t K n j σ ω a)
    have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have h2 : x / Real.sqrt 2 ≤ max |(∑ j ∈ Finset.range k, YvecN sz E s t K n j σ ω a).re|
        |(∑ j ∈ Finset.range k, YvecN sz E s t K n j σ ω a).im| := by
      rw [div_le_iff₀ hs2]
      linarith
    rw [Complex.re_sum, Complex.im_sum] at h2
    rcases le_max_iff.1 h2 with h | h
    · exact Or.inl ⟨k, hk, h⟩
    · exact Or.inr ⟨k, hk, h⟩
  calc (pathP sz).real {ω | ∃ k, k ≤ K n ∧
        x ≤ ‖∑ j ∈ Finset.range k, YvecN sz E s t K n j σ ω a‖}
      ≤ (pathP sz).real ({ω | ∃ k, k ≤ K n ∧ x / Real.sqrt 2 ≤
          |∑ j ∈ Finset.range k, (YvecN sz E s t K n j σ ω a).re|} ∪
        {ω | ∃ k, k ≤ K n ∧ x / Real.sqrt 2 ≤
          |∑ j ∈ Finset.range k, (YvecN sz E s t K n j σ ω a).im|}) := measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ (K n : ℝ) * (gridStep s t K n ^ 2 * P) / (x / Real.sqrt 2) ^ 2 +
        (K n : ℝ) * (gridStep s t K n ^ 2 * P) / (x / Real.sqrt 2) ^ 2 := add_le_add hRe hIm
    _ = 4 * ((K n : ℝ) * (gridStep s t K n ^ 2 * P)) / x ^ 2 := by
        rw [div_pow, Real.sq_sqrt (by norm_num)]
        field_simp
        ring

end YPart

/-! ## 10. One size index: the tail of `Mart = S^Z + S^Y` -/

section Core

variable {d : ℕ} (sz : Sizes d)

/-- The threshold sum is at most `m N (16 N)^{2m+2}` (the crude bound of `difRep2_norm_STeeM_le_N` over the
`K` steps, `K Δ ≤ 1`). -/
private theorem difRepTail_aSum_le (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (hE : |E n| < 2) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0)
    {m : ℕ} (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n))
    (hη : ∀ j, j ≤ K n →
      1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaT (E n) (gridTime s t K n j))
    (hKΔ : (K n : ℝ) * gridStep s t K n ≤ 1) (ω : PathΩ sz) :
    ∑ j ∈ Finset.range (K n), difRepTail_aSeq sz E s t K n σ a j ω ≤
      (m : ℝ) * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ (2 * m + 2) := by
  have hΔ := ST_gridStep_nonneg s t K n hst
  set Bm : ℝ := (m : ℝ) * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ (2 * m + 2)
    with hBm
  have hBm0 : 0 ≤ Bm := by positivity
  have hterm : ∀ j ∈ Finset.range (K n), difRepTail_aSeq sz E s t K n σ a j ω ≤
      gridStep s t K n * Bm := by
    intro j hj
    have hj' : j < K n := Finset.mem_range.1 hj
    have hu1 : gridTime s t K n j < 1 := (difRepTail_gridTime_le hst hK hj'.le).trans_lt ht1
    refine mul_le_mul_of_nonneg_left ?_ hΔ
    exact difRep2_norm_STeeM_le_N sz n hE hu1 (pathH_isHermitian sz s t K n j ω) (hη j hj'.le)
      σ a a
  calc ∑ j ∈ Finset.range (K n), difRepTail_aSeq sz E s t K n σ a j ω
      ≤ ∑ j ∈ Finset.range (K n), gridStep s t K n * Bm := Finset.sum_le_sum hterm
    _ = ((K n : ℝ) * gridStep s t K n) * Bm := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ ≤ 1 * Bm := mul_le_mul_of_nonneg_right hKΔ hBm0
    _ = Bm := one_mul _

/-- **The tail at one size index** (steps 3(b)-(e) of T2180): given the three numerical budgets (shift sum,
`Y` part, `Z` levels) and the spectral height `η_{u_j} ≥ 1/(16 N)` along the grid, the martingale
`Mart_k = S^Z_k + S^Y_k` at the label `(σ, a)` obeys the pin of `GridRepTailNAt`:
`μ(∃ k ≤ K, N^{ε'} (Σ_{j<k} Δ ‖𝓔⊗𝓔_{u_j}(H_j)_{σ,a,a}‖ + N^{-D})^{1/2} < |Mart_k|) ≤ N^{-D}`. -/
private theorem difRepTail_core (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0)
    {m : ℕ} (hm : 2 ≤ m) (D ε' : ℝ) (hD : 0 < D) (hε' : 0 < ε')
    (hη : ∀ j, j ≤ K n →
      1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaT (E n) (gridTime s t K n j))
    (hshift : ((m : ℝ) * (2 * m + 2) * 16 ^ (2 * m + 3) * ((sz.size n : ℕ) : ℝ) ^ (2 * m + 4)) *
      gridStep s t K n ≤ ((sz.size n : ℕ) : ℝ) ^ (-D))
    (hY : 16 * gridStep s t K n * (2000 * (((m * (m + 1) : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) *
        (16 * ((sz.size n : ℕ) : ℝ)) ^ (m + 2)) ^ 2 * ((sz.size n : ℕ) : ℝ) ^ 8) *
        ((sz.size n : ℕ) : ℝ) ^ D ≤ ((sz.size n : ℕ) : ℝ) ^ (-D) / 2)
    (hZ : ((⌈(m : ℝ) * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ (2 * m + 2) *
        ((sz.size n : ℕ) : ℝ) ^ D⌉₊ : ℝ) + 1) *
        (4 * Real.exp (-(((sz.size n : ℕ) : ℝ) ^ ε' / 2) ^ 2 / (16 * (m : ℝ)))) ≤
        ((sz.size n : ℕ) : ℝ) ^ (-D) / 2)
    (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) :
    pathP sz {ω | ∃ k, k ≤ K n ∧
      ((sz.size n : ℕ) : ℝ) ^ ε' * (∑ j ∈ Finset.range k, gridStep s t K n *
        ‖sz.STeeM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) σ a a‖ +
          ((sz.size n : ℕ) : ℝ) ^ (-D)) ^ (1 / 2 : ℝ) <
        ‖difRepMartN sz E s t K n (σ, a) k ω‖} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN1 : 1 ≤ N := by rw [hN]; exact_mod_cast sz.one_le_size n
  have hN0 : 0 < N := by linarith
  set Δ := gridStep s t K n with hΔdef
  have hΔ : 0 ≤ Δ := ST_gridStep_nonneg s t K n hst
  have hKΔ : (K n : ℝ) * Δ ≤ 1 := by
    rw [hΔdef, difRepTail_K_mul_step s t K n hK]; linarith
  set δ : ℝ := N ^ (-D) with hδdef
  have hδ : 0 < δ := Real.rpow_pos_of_pos hN0 _
  have hNδ : N ^ D * δ = 1 := by
    rw [hδdef, ← Real.rpow_add hN0]; simp
  set ρ : ℝ := N ^ ε' / 2 with hρdef
  have hNε1 : 1 ≤ N ^ ε' := Real.one_le_rpow hN1 hε'.le
  have hρ : 0 ≤ ρ := by positivity
  set Bm : ℝ := (m : ℝ) * N * (16 * N) ^ (2 * m + 2) with hBm
  have hBm0 : 0 ≤ Bm := by positivity
  set Lmax : ℕ := ⌈Bm * N ^ D⌉₊ with hLmax
  -- the shift budget
  have hesum : ∑ j ∈ Finset.range (K n), difRepTail_eSeq sz E s t K n m j ≤ δ := by
    have := difRep2_eeShift_sum_le sz E s t K n m hst hKΔ (fun j hj => hη (j + 1) hj)
    exact this.trans hshift
  -- the threshold sum is at most `2^Lmax δ`
  have haL : ∀ ω, ∑ j ∈ Finset.range (K n), difRepTail_aSeq sz E s t K n σ a j ω ≤ 2 ^ Lmax * δ := by
    intro ω
    refine (difRepTail_aSum_le sz E s t K n hE hst ht1 hK σ a hη hKΔ ω).trans ?_
    have h1 : Bm * N ^ D ≤ (Lmax : ℝ) := Nat.le_ceil _
    have h2 : (Lmax : ℝ) < 2 ^ Lmax := by exact_mod_cast Nat.lt_two_pow_self
    have h3 : Bm * N ^ D * δ ≤ 2 ^ Lmax * δ :=
      mul_le_mul_of_nonneg_right (h1.trans h2.le) hδ.le
    calc Bm = Bm * (N ^ D * δ) := by rw [hNδ, mul_one]
      _ = Bm * N ^ D * δ := by ring
      _ ≤ 2 ^ Lmax * δ := h3
  -- the `Z` part
  have hZtail := difRepTail_Z_tail sz E s t K n hE hs0 hst ht1 hm σ a Lmax hδ hρ hesum haL
  have hZb : ((Lmax : ℝ) + 1) * (4 * Real.exp (-ρ ^ 2 / (16 * m))) ≤ δ / 2 := hZ
  -- the `Y` part
  set P : ℝ := 2000 * (((m * (m + 1) : ℕ) : ℝ) * N * (16 * N) ^ (m + 2)) ^ 2 * N ^ 8 with hP
  have hxY : 0 < ρ * Real.sqrt δ := by
    have : 0 < ρ := by rw [hρdef]; positivity
    positivity
  have hYtail := difRepTail_Y_tail sz E s t K n hE hs0 hst ht1 σ a
    (fun j hj => hη (j + 1) hj) (P := P) (le_refl _) hxY
  have hYb : 4 * ((K n : ℝ) * (Δ ^ 2 * P)) / (ρ * Real.sqrt δ) ^ 2 ≤ δ / 2 := by
    have hx2 : (ρ * Real.sqrt δ) ^ 2 = ρ ^ 2 * δ := by rw [mul_pow, Real.sq_sqrt hδ.le]
    have hρ2 : 1 / 4 ≤ ρ ^ 2 := by rw [hρdef]; nlinarith
    have hP0 : 0 ≤ P := by positivity
    have hY' : 16 * Δ * P ≤ δ / 2 * δ := by
      calc 16 * Δ * P = (16 * Δ * P * N ^ D) * δ := by
            rw [mul_assoc (16 * Δ * P), hNδ, mul_one]
        _ ≤ δ / 2 * δ := mul_le_mul_of_nonneg_right hY hδ.le
    rw [hx2, div_le_iff₀ (by positivity)]
    have h1 : (K n : ℝ) * (Δ ^ 2 * P) ≤ Δ * P := by
      calc (K n : ℝ) * (Δ ^ 2 * P) = ((K n : ℝ) * Δ) * (Δ * P) := by ring
        _ ≤ 1 * (Δ * P) := mul_le_mul_of_nonneg_right hKΔ (by positivity)
        _ = Δ * P := one_mul _
    nlinarith [mul_le_mul_of_nonneg_left hρ2 (by positivity : (0 : ℝ) ≤ δ / 2 * δ)]
  -- the pathwise inclusion `{pin event} ⊆ E_Z ∪ E_Y`
  set EZ : Set (PathΩ sz) := {ω | ∃ k, k ≤ K n ∧
    ρ * (∑ j ∈ Finset.range k, difRepTail_aSeq sz E s t K n σ a j ω + δ) ^ (1 / 2 : ℝ) <
      ‖∑ j ∈ Finset.range k, ZvecN sz E s t K n j σ ω a‖} with hEZ
  set EY : Set (PathΩ sz) := {ω | ∃ k, k ≤ K n ∧
    ρ * Real.sqrt δ ≤ ‖∑ j ∈ Finset.range k, YvecN sz E s t K n j σ ω a‖} with hEY
  have hincl : {ω | ∃ k, k ≤ K n ∧
      N ^ ε' * (∑ j ∈ Finset.range k, Δ *
        ‖sz.STeeM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) σ a a‖ + N ^ (-D)) ^
        (1 / 2 : ℝ) < ‖difRepMartN sz E s t K n (σ, a) k ω‖} ⊆ EZ ∪ EY := by
    intro ω hω
    obtain ⟨k, hk, hlt⟩ := hω
    have hMart : difRepMartN sz E s t K n (σ, a) k ω =
        ∑ j ∈ Finset.range k, ZvecN sz E s t K n j σ ω a +
          ∑ j ∈ Finset.range k, YvecN sz E s t K n j σ ω a := by
      unfold difRepMartN
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      unfold YvecN
      ring
    have hA0 : 0 ≤ ∑ j ∈ Finset.range k, difRepTail_aSeq sz E s t K n σ a j ω :=
      Finset.sum_nonneg fun j _ => difRepTail_aSeq_nonneg sz E s t K n hst σ a j ω
    set T : ℝ := (∑ j ∈ Finset.range k, difRepTail_aSeq sz E s t K n σ a j ω + δ) ^ (1 / 2 : ℝ)
      with hT
    have hlt' : N ^ ε' * T < ‖difRepMartN sz E s t K n (σ, a) k ω‖ := hlt
    have hTδ : Real.sqrt δ ≤ T := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow hδ.le (by linarith) (by norm_num)
    have hρ2 : N ^ ε' = 2 * ρ := by rw [hρdef]; ring
    by_cases hZ' : ρ * T < ‖∑ j ∈ Finset.range k, ZvecN sz E s t K n j σ ω a‖
    · exact Or.inl ⟨k, hk, hZ'⟩
    · right
      refine ⟨k, hk, ?_⟩
      have h1 : N ^ ε' * T < ‖∑ j ∈ Finset.range k, ZvecN sz E s t K n j σ ω a‖ +
          ‖∑ j ∈ Finset.range k, YvecN sz E s t K n j σ ω a‖ := by
        refine hlt'.trans_le ?_
        rw [hMart]
        exact norm_add_le _ _
      have h2 : ρ * T < ‖∑ j ∈ Finset.range k, YvecN sz E s t K n j σ ω a‖ := by
        rw [hρ2] at h1
        push Not at hZ'
        linarith
      calc ρ * Real.sqrt δ ≤ ρ * T := mul_le_mul_of_nonneg_left hTδ hρ
        _ ≤ _ := h2.le
  have hEZm : pathP sz EZ ≤ ENNReal.ofReal (δ / 2) := by
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (hZtail.trans hZb)
  have hEYm : pathP sz EY ≤ ENNReal.ofReal (δ / 2) := by
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (hYtail.trans hYb)
  calc pathP sz {ω | ∃ k, k ≤ K n ∧
      N ^ ε' * (∑ j ∈ Finset.range k, Δ *
        ‖sz.STeeM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) σ a a‖ + N ^ (-D)) ^
        (1 / 2 : ℝ) < ‖difRepMartN sz E s t K n (σ, a) k ω‖}
      ≤ pathP sz (EZ ∪ EY) := measure_mono hincl
    _ ≤ pathP sz EZ + pathP sz EY := measure_union_le _ _
    _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := add_le_add hEZm hEYm
    _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end Core

/-! ## 11. The asymptotics of the `Z` budget -/

section Asymptotics

/-- A polynomial against a stretched exponential: `N^s e^{-b N^{c}} → 0` as `N → ∞`
(`tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero` after the substitution `x = N^c`). -/
private theorem difRepTail_tendsto_rpow_exp (s b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    Tendsto (fun N : ℝ => N ^ s * Real.exp (-b * N ^ c)) atTop (nhds 0) := by
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s / c) b hb
  have h2 : Tendsto (fun N : ℝ => N ^ c) atTop atTop := tendsto_rpow_atTop hc
  have h3 := h1.comp h2
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
  simp only [Function.comp]
  rw [← Real.rpow_mul hN]
  congr 2
  field_simp

/-- **The `Z` budget holds for large `N`**: `(⌈m N (16 N)^{2m+2} N^D⌉ + 1) · 4 e^{-(N^{ε'}/2)²/(16 m)}
≤ N^{-D}/2` eventually (the polynomial number of levels is beaten by the stretched exponential). -/
private theorem difRepTail_eventually_Z (m : ℕ) (hm : 0 < m) (D ε' : ℝ) (hD : 0 < D) (hε' : 0 < ε') :
    ∀ᶠ N : ℝ in atTop, 1 ≤ N ∧
      ((⌈(m : ℝ) * N * (16 * N) ^ (2 * m + 2) * N ^ D⌉₊ : ℝ) + 1) *
        (4 * Real.exp (-(N ^ ε' / 2) ^ 2 / (16 * (m : ℝ)))) ≤ N ^ (-D) / 2 := by
  set c₃ : ℝ := (m : ℝ) * 16 ^ (2 * m + 2) with hc₃
  set q : ℝ := ((2 * m + 3 : ℕ) : ℝ) + D with hq
  set c₄ : ℝ := 8 * (c₃ + 2) with hc₄
  have hc₃0 : 0 < c₃ := by positivity
  have hc₄0 : 0 < c₄ := by positivity
  have hlim := difRepTail_tendsto_rpow_exp (q + D) (1 / (64 * (m : ℝ))) (2 * ε')
    (by positivity) (by positivity)
  have hev := hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / c₄))
  filter_upwards [hev, eventually_ge_atTop (1 : ℝ)] with N hN hN1
  refine ⟨hN1, ?_⟩
  have hN0 : 0 < N := by linarith
  have hND : 0 < N ^ D := Real.rpow_pos_of_pos hN0 _
  set x : ℝ := (m : ℝ) * N * (16 * N) ^ (2 * m + 2) * N ^ D with hx
  have hx0 : 0 ≤ x := by positivity
  have hceil : (⌈x⌉₊ : ℝ) + 1 ≤ x + 2 := by
    have := Nat.ceil_lt_add_one hx0
    linarith
  have hxq : x = c₃ * N ^ q := by
    rw [hx, hc₃, hq, Real.rpow_add hN0, Real.rpow_natCast]
    rw [mul_pow]
    ring
  have hNq1 : 1 ≤ N ^ q := Real.one_le_rpow hN1 (by positivity)
  have hexp : -(N ^ ε' / 2) ^ 2 / (16 * (m : ℝ)) = -(1 / (64 * (m : ℝ))) * N ^ (2 * ε') := by
    have : (N ^ ε') ^ 2 = N ^ (2 * ε') := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
      congr 1
      push_cast
      ring
    rw [div_pow, this]
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [hexp]
  set E : ℝ := Real.exp (-(1 / (64 * (m : ℝ))) * N ^ (2 * ε')) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hG : N ^ (q + D) * E < 1 / c₄ := hN
  have hNqD : N ^ (q + D) = N ^ q * N ^ D := Real.rpow_add hN0 _ _
  -- `8 (x + 2) N^D E ≤ c₄ N^{q+D} E < 1`
  have hkey : (x + 2) * (4 * E) * (2 * N ^ D) ≤ 1 := by
    have h1 : x + 2 ≤ (c₃ + 2) * N ^ q := by rw [hxq]; nlinarith
    calc (x + 2) * (4 * E) * (2 * N ^ D) = 8 * (x + 2) * (N ^ D * E) := by ring
      _ ≤ 8 * ((c₃ + 2) * N ^ q) * (N ^ D * E) := by gcongr
      _ = c₄ * (N ^ (q + D) * E) := by rw [hNqD, hc₄]; ring
      _ ≤ c₄ * (1 / c₄) := by gcongr
      _ = 1 := by field_simp
  have hnegD : N ^ (-D) = (N ^ D)⁻¹ := Real.rpow_neg hN0.le D
  rw [hnegD]
  refine (mul_le_mul_of_nonneg_right hceil (by positivity)).trans ?_
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), ← one_div, le_div_iff₀ hND] at *
  nlinarith [hkey]

end Asymptotics

/-! ## 12. Target 3: `gridRepTailN_holds` -/

/-- **Target 3, `gridRepTailN_holds`**: the owed plain martingale tail (clause (iii) of `STGridRepNAt`
for `difRepMartN`) at every loop length `m ≥ 2`, for every `d` (no input is stated only for `d ≥ 3`).
The grid exponent is `CK = 2m + 2D + 16` (it depends on `m, D` only, not on `ε'`, `κ`, `ε`).
Route (T2180 step 3): `Mart_k = S^Z_k + S^Y_k` (`YvecN = martIncN - ZvecN`); the `Z` part by the peeling
lemma `difRep2_peel` (levels `V_ℓ = 2^ℓ N^{-D}`, the random predictable proxy `v_j = Δ m Re 𝓔⊗𝓔_{u_{j+1}}`
of `difRepTail_condMGF_Z`, moved to `u_j` at the cost `N^{2m+4} Δ` of `difRep2_eeShift_sum_le`) with
`ρ = N^{ε'}/2`; the `Y` part by Doob's `L²` maximal inequality (`difRepTail_Y_tail`).  The two budgets
are `32 c_P ≤ N²` (`Y`) and `(L + 1) · 4 e^{-N^{2ε'}/(64 m)} ≤ N^{-D}/2` with `L` polynomial in `N` (`Z`,
`difRepTail_eventually_Z`).  The statement is `∀ᶠ n`, from `SizeTendsto` (`STFlow`). -/
theorem gridRepTailN_holds : ∀ d m : ℕ, 2 ≤ m → GridRepTailNAt d m := by
  intro d m hm κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz s t hs hst htT D hD
  refine ⟨((2 * m + 2 * D + 16 : ℝ)), by positivity, ?_⟩
  intro K hK0 hKN ε' hε'
  have hfl : ∀ n, |STflowE z n| ≤ 2 - κ ∧ lemT (z n) < 1 := fun n =>
    let h := difRep_flow_bounds sz hκ hz n (htT n)
    ⟨h.1, h.2.1⟩
  have hE : ∀ n, |STflowE z n| < 2 := fun n => by linarith [(hfl n).1]
  have ht1 : ∀ n, t n < 1 := fun n => lt_of_le_of_lt (htT n) (hfl n).2
  have hsize : sz.SizeTendsto := hz.1.2.2.1
  set c₂ : ℝ := (m : ℝ) * (2 * m + 2) * 16 ^ (2 * m + 3) with hc₂
  set cP : ℝ := 2000 * (((m * (m + 1) : ℕ) : ℝ)) ^ 2 * 16 ^ (2 * m + 4) with hcP
  have hbig := hsize.eventually (eventually_ge_atTop (max c₂ (32 * cP)))
  have hZev := hsize.eventually (difRepTail_eventually_Z m (by omega) D ε' hD hε')
  filter_upwards [hKN, hbig, hZev] with n hKNn hbign hZn
  intro i
  obtain ⟨hN1, hZn⟩ := hZn
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN0 : 0 < N := by linarith
  set Δ := gridStep s t K n with hΔdef
  have hΔ : 0 ≤ Δ := ST_gridStep_nonneg s t K n (hst n)
  have hKΔ : (K n : ℝ) * Δ ≤ 1 := by
    rw [hΔdef, difRepTail_K_mul_step s t K n (hK0 n)]; linarith [hs n, ht1 n]
  have hΔN : Δ * N ^ ((2 * m + 2 * D + 16 : ℝ)) ≤ 1 := by
    calc Δ * N ^ ((2 * m + 2 * D + 16 : ℝ)) ≤ Δ * (K n : ℝ) := mul_le_mul_of_nonneg_left hKNn hΔ
      _ = (K n : ℝ) * Δ := mul_comm _ _
      _ ≤ 1 := hKΔ
  have hΔle : Δ ≤ N ^ (-((2 * m + 2 * D + 16 : ℝ))) := by
    rw [Real.rpow_neg hN0.le, ← one_div, le_div_iff₀ (Real.rpow_pos_of_pos hN0 _)]
    exact hΔN
  have hc₂N : c₂ ≤ N ^ (D + 12) := by
    have h1 : c₂ ≤ N := (le_max_left _ _).trans hbign
    calc c₂ ≤ N := h1
      _ = N ^ (1 : ℝ) := (Real.rpow_one N).symm
      _ ≤ N ^ (D + 12) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hcPN : 32 * cP ≤ N ^ 2 := by
    have h1 : 32 * cP ≤ N := (le_max_right _ _).trans hbign
    nlinarith
  -- the spectral height along the grid
  have hη : ∀ j, j ≤ K n →
      1 / (16 * N) ≤ etaT (STflowE z n) (gridTime s t K n j) := by
    intro j hj
    have hu : gridTime s t K n j ≤ lemT (z n) :=
      (difRepTail_gridTime_le (hst n) (hK0 n) hj).trans (htT n)
    have h := (difRep_flow_bounds sz hκ hz n hu).2.2.1
    refine le_trans ?_ h
    have h2 : N ^ (-1 : ℝ) ≤ N ^ (-1 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    rw [Real.rpow_neg_one] at h2
    calc 1 / (16 * N) = N⁻¹ / 16 := by field_simp
      _ ≤ N ^ (-1 + ε) / 16 := by gcongr
  -- the shift budget
  have hshift : (c₂ * N ^ (2 * m + 4)) * Δ ≤ N ^ (-D) := by
    have h1 : N ^ (2 * m + 4) * N ^ (-((2 * m + 2 * D + 16 : ℝ))) = N ^ (-(2 * D) - 12) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hN0]
      congr 1
      push_cast
      ring
    calc c₂ * N ^ (2 * m + 4) * Δ ≤ c₂ * N ^ (2 * m + 4) * N ^ (-((2 * m + 2 * D + 16 : ℝ))) := by
          gcongr
      _ = c₂ * N ^ (-(2 * D) - 12) := by rw [mul_assoc, h1]
      _ ≤ N ^ (D + 12) * N ^ (-(2 * D) - 12) := by gcongr
      _ = N ^ (-D) := by
          rw [← Real.rpow_add hN0]
          congr 1
          ring
  -- the `Y` budget
  have hY : 16 * Δ * (2000 * (((m * (m + 1) : ℕ) : ℝ) * N * (16 * N) ^ (m + 2)) ^ 2 * N ^ 8) *
      N ^ D ≤ N ^ (-D) / 2 := by
    have hPeq : 2000 * (((m * (m + 1) : ℕ) : ℝ) * N * (16 * N) ^ (m + 2)) ^ 2 * N ^ 8 =
        cP * N ^ (2 * m + 14) := by
      rw [hcP]
      ring
    have h1 : N ^ (2 * m + 14) * N ^ D * N ^ (-((2 * m + 2 * D + 16 : ℝ))) = N ^ (-D - 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      congr 1
      push_cast
      ring
    have hcP0 : 0 ≤ cP := by positivity
    have h2 : N ^ (-D) = N ^ (-D - 2) * N ^ 2 := by
      rw [← Real.rpow_natCast N 2, ← Real.rpow_add hN0]
      congr 1
      push_cast
      ring
    have hND2 : 0 < N ^ (-D - 2) := Real.rpow_pos_of_pos hN0 _
    rw [hPeq]
    calc 16 * Δ * (cP * N ^ (2 * m + 14)) * N ^ D
        = 16 * cP * Δ * (N ^ (2 * m + 14) * N ^ D) := by ring
      _ ≤ 16 * cP * N ^ (-((2 * m + 2 * D + 16 : ℝ))) * (N ^ (2 * m + 14) * N ^ D) := by gcongr
      _ = 16 * cP * (N ^ (2 * m + 14) * N ^ D * N ^ (-((2 * m + 2 * D + 16 : ℝ)))) := by ring
      _ = 16 * cP * N ^ (-D - 2) := by rw [h1]
      _ ≤ N ^ (-D) / 2 := by
          rw [h2]
          nlinarith [mul_le_mul_of_nonneg_left hcPN hND2.le]
  exact difRepTail_core sz (STflowE z) s t K n (hE n) (hs n) (hst n) (ht1 n) (hK0 n) hm D ε' hD hε'
    hη hshift hY hZn i.1 i.2

/-! ## 13. Target 4: `STGridMart` and `STGridMartAt d 11` unconditional for `3 ≤ d` -/

/-- **Target 4, `stGridMart_holds`**: the pin `STGridMart` (the Step 2 martingale input) is unconditional for
`3 ≤ d`: `stGridMart_of_tail` and the owed tail `gridRepTailN_holds` at `m = 2`.  The hypothesis `3 ≤ d`
comes from `stGridMart_of_tail` (through `stKbound_of_flow`, DECISIONS §36): the tail itself holds for every
`d`; the consumers (`stOptL2_of_pins`, `ST_step2_of_pins'`) are under `3 ≤ d`. -/
theorem stGridMart_holds : ∀ d : ℕ, 3 ≤ d → STGridMart d :=
  fun d hd => stGridMart_of_tail d hd (gridRepTailN_holds d 2 le_rfl)

/-- **Target 4, `stGridMartAt_holds`**: the loop-length-`2` pin at the explicit constant `C₀ = 2 + 9 = 11`
(`stGridMartAt_of_parts2`, `gridRepRemN_holds` at `m = 2` and `gridRepTailN_holds`). -/
theorem stGridMartAt_holds : ∀ d : ℕ, 3 ≤ d → STGridMartAt d 11 := by
  intro d hd
  have h := stGridMartAt_of_parts2 d (((2 : ℕ) : ℝ) + 9) (by positivity)
    (gridRepRemN_holds d hd 2 le_rfl) (gridRepTailN_holds d 2 le_rfl)
  have h11 : (((2 : ℕ) : ℝ) + 9) = 11 := by norm_num
  rwa [h11] at h
end RBM.Ind

namespace RBM.Ind.DifREP2Inst

open MeasureTheory ProbabilityTheory Filter RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Ind
  RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step2DefsInst

/-! ## 14. Compiled nonempty instances at `d = 3`

The size data are the merged preflight sequence `sz0` (`d = 3`, `L_n = 4 (n+1)`, `W_n = (2 (n+1))^5`,
`N_0 = 2097152`) and the flow block of `Induction/Defs.lean` (`z0`, `flow_z0` with
`κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `s ≡ 0`, `t ≡ 1/16 ≤ lemT z0`).  Targets 1-2 and the two public pieces
of Amend 2 are applied at the grid `K ≡ 4` (`Δ = 1/64`), `n = 0`, `E ≡ 1/2`, the loop `(+,-,+)` of length
`3` and the label `a = 0`; target 3 at the flow data.  Every deterministic hypothesis is discharged. -/

theorem hs0 : ∀ n, 0 ≤ sInst n := fun _ => le_rfl

theorem hst : ∀ n, sInst n ≤ tInst n := fun n => by simp only [sInst, tInst]; norm_num

theorem htT : ∀ n, tInst n ≤ lemT (z0 n) := fun n => sixteenth_le_lemT n

/-- The instance grid is nondegenerate: `K ≡ 4` on `[0, 1/16]` has `Δ = 1/64`. -/
theorem gridStep_inst : gridStep sInst tInst (fun _ => 4) 0 = 1 / 64 := by
  norm_num [gridStep, sInst, tInst]

/-- The energy `E ≡ 1/2` of the instances of targets 1-2. -/
def E12 : ℕ → ℝ := fun _ => 1 / 2

/-- The loop `(+,-,+)` of length `3`. -/
def σ3 : Fin 3 → Bool := ![true, false, true]

/-- The label `a = 0`. -/
def a0 : Fin 3 → Zd 3 (sz0.L 0) := fun _ => 0

/-- The weights `κ = δ_0`. -/
def κ0 : (Fin 3 → Zd 3 (sz0.L 0)) → ℂ := fun b => if b = a0 then 1 else 0

theorem hE12 : |E12 0| < 2 := by
  simp only [E12]
  rw [abs_of_pos (by norm_num)]
  norm_num

theorem ht0 : tInst 0 < 1 := by simp only [tInst]; norm_num

theorem N0_pos : (0 : ℝ) < ((sz0.size 0 : ℕ) : ℝ) := by
  exact_mod_cast sz0.one_le_size 0

/-- `η_u ≥ 1/2` for `E = 1/2`, `u ≤ 1/16`. -/
theorem eta12 {u : ℝ} (hu : u ≤ 1 / 16) : (1 / 2 : ℝ) ≤ etaT (E12 0) u := by
  have hm : (mE (E12 0)).im = Real.sqrt (4 - (E12 0) ^ 2) / 2 := by
    simp [mE, E12]
  have hs : (19 / 10 : ℝ) ≤ Real.sqrt (4 - (E12 0) ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    simp only [E12]
    norm_num
  unfold etaT
  rw [hm]
  nlinarith

/-- The grid times of the instance are at most `1/16`. -/
theorem gridTime_inst_le {j : ℕ} (hj : j ≤ 4) : gridTime sInst tInst (fun _ => 4) 0 j ≤ 1 / 16 := by
  have h := difRepTail_gridTime_le (s := sInst) (t := tInst) (K := fun _ => 4) (n := 0)
    (by simp only [sInst, tInst]; norm_num) (by norm_num) hj
  simpa [tInst] using h

/-- `η_u ≥ 1/(16 N_0)` for `E = 1/2`, `u ≤ 1/16`. -/
theorem eta_ge {u : ℝ} (hu : u ≤ 1 / 16) :
    1 / (16 * ((sz0.size 0 : ℕ) : ℝ)) ≤ etaT (E12 0) u := by
  refine le_trans ?_ (eta12 hu)
  have hN : (1 : ℝ) ≤ ((sz0.size 0 : ℕ) : ℝ) := by exact_mod_cast sz0.one_le_size 0
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- `η_{u_j} ≥ 1/(16 N_0)` along the instance grid. -/
theorem eta_inst : ∀ j, j ≤ 4 →
    1 / (16 * ((sz0.size 0 : ℕ) : ℝ)) ≤ etaT (E12 0) (gridTime sInst tInst (fun _ => 4) 0 j) :=
  fun j hj => eta_ge (gridTime_inst_le hj)

/-- **`difRepTail_condMGF_Z` (target 2) at the data** (`E ≡ 1/2`, `K ≡ 4`, `n = 0`, `j = 0`, `k = 3`,
`σ = (+,-,+)`, `κ = δ_0`, `r = 1`): the integrability and the conditional mgf bounds of `Re` and `Im` of
`Z_{0,0}` with the random proxy `Δ k Re (𝓔⊗𝓔)_{u_1}(H_0)_{σ,0,0}`. -/
example := difRepTail_condMGF_Z sz0 E12 sInst tInst (fun _ => 4) 0 0 hE12 (hs0 0) (hst 0) ht0
  (by norm_num) (k := 3) (by norm_num) σ3 κ0 1


/-- The zero state is a Hermitian matrix (the arguments of the crude bounds below). -/
theorem herm0 : (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ).IsHermitian :=
  Matrix.isHermitian_zero

/-- **`difRep2_norm_STeeM_le` (Amend 2 (i)) at the data** (`n = 0`, `E = 1/2`, `u = 1/16`, `M = 0`,
`σ = (+,-,+)`, `a = a' = 0`). -/
example := difRep2_norm_STeeM_le sz0 0 (E := E12 0) (u := 1 / 16) hE12 (by norm_num) herm0 σ3 a0 a0

/-- **`difRep2_norm_STeeM_le_N` (Amend 2 (i)) at the data**: `‖𝓔⊗𝓔‖ ≤ m N (16 N)^{2m+2}` for `m = 3`. -/
example := difRep2_norm_STeeM_le_N sz0 0 (E := E12 0) (u := 1 / 16) hE12 (by norm_num) herm0
  (eta_ge le_rfl) σ3 a0 a0

/-- **`difRep2_eeShiftErrN_le` (Amend 2 (i)) at the data** (`u = 0`, `u' = 1/64`, `m = 3`). -/
example := difRep2_eeShiftErrN_le sz0 0 (E12 0) (u := 0) (u' := 1 / 64) (by norm_num)
  (eta_ge (u := 1 / 64) (by norm_num)) 3

/-- **`difRep2_eeShift_sum_le` (Amend 2 (i)) at the data** (`K ≡ 4`, `m = 3`): the shift errors of the
four grid steps sum to at most `m (2m+2) 16^{2m+3} N^{2m+4} Δ`. -/
example := difRep2_eeShift_sum_le sz0 E12 sInst tInst (fun _ => 4) 0 3 (hst 0)
  (by rw [gridStep_inst]; norm_num) (fun j hj => eta_inst (j + 1) (by omega))

/-- The crude bound `B = Δ m (m N (16 N)^{2m+2})` of the proxy at the data (`m = 3`). -/
def B3 : ℝ := gridStep sInst tInst (fun _ => 4) 0 * ((3 : ℕ) * (((3 : ℕ) : ℝ) *
  ((sz0.size 0 : ℕ) : ℝ) * (16 * ((sz0.size 0 : ℕ) : ℝ)) ^ (2 * 3 + 2)))

theorem B3_pos : 0 < B3 := by
  have hN := N0_pos
  unfold B3
  rw [gridStep_inst]
  positivity

/-- **`azumaRandProxy_max` (target 1) at the data**: on `(PathΩ sz0, pathP sz0, filt sz0)`, the increments
`ζ_j = Re Z_{j,0}` of the grid `K ≡ 4` (`E ≡ 1/2`, `σ = (+,-,+)`), the proxy `v_j` of target 2, the switches
`G_j = univ`, `B` the crude bound, `V = 4 B`, `x = 1`: `μ(∃ k ≤ 4, 1 ≤ Σ_{j<k} Re Z_{j,0}) ≤ e^{-1/(2V)}`. -/
theorem inst_azumaRandProxy_max :
    (pathP sz0).real {ω | ∃ k, k ≤ 4 ∧ 1 ≤ ∑ j ∈ Finset.range k, (Set.univ : Set (PathΩ sz0)).indicator
      (fun ω => (ZvecN sz0 E12 sInst tInst (fun _ => 4) 0 j σ3 ω a0).re) ω} ≤
      Real.exp (-(1 : ℝ) ^ 2 / (2 * (4 * B3))) := by
  have hZ := fun (j : ℕ) (hj : j < 4) (r : ℝ) =>
    difRepTail_Z_mgf sz0 E12 sInst tInst (fun _ => 4) 0 j hE12 (hs0 0) (hst 0) ht0 (by omega)
      (m := 3) (by norm_num) σ3 a0 r
  have hcrude := fun (j : ℕ) (hj : j < 4) (ω : PathΩ sz0) =>
    difRepTail_vSeq_le_crude sz0 E12 sInst tInst (fun _ => 4) 0 j hE12 (hs0 0) (hst 0) ht0
      (by omega) (m := 3) σ3 a0 (eta_inst (j + 1) (by omega)) ω
  refine azumaRandProxy_max (pathP sz0) (filt sz0)
    (fun j ω => (ZvecN sz0 E12 sInst tInst (fun _ => 4) 0 j σ3 ω a0).re)
    (fun j ω => difRepTail_vSeq sz0 E12 sInst tInst (fun _ => 4) 0 σ3 a0 j ω)
    (fun _ => Set.univ) 4 B3 (4 * B3) 1
    (fun j _ => difRepTail_Zre_sm sz0 E12 sInst tInst (fun _ => 4) 0 j σ3 a0)
    (fun j _ => difRepTail_vSeq_sm sz0 E12 sInst tInst (fun _ => 4) 0 j σ3 a0)
    (fun j _ => MeasurableSet.univ)
    (fun j hj ω => ⟨difRepTail_vSeq_nonneg sz0 E12 sInst tInst (fun _ => 4) 0 j hE12 (hs0 0) (hst 0)
      ht0 (by omega) (m := 3) (by norm_num) σ3 a0 ω, hcrude j hj ω⟩)
    (fun j hj r => (hZ j hj r).1)
    (fun j hj r => (hZ j hj r).2.2.1)
    (fun ω => ?_) (by have := B3_pos; positivity) (by norm_num)
  simp only [Set.indicator_univ]
  calc ∑ j ∈ Finset.range 4, difRepTail_vSeq sz0 E12 sInst tInst (fun _ => 4) 0 σ3 a0 j ω
      ≤ ∑ j ∈ Finset.range 4, B3 := Finset.sum_le_sum fun j hj => hcrude j (Finset.mem_range.1 hj) ω
    _ = 4 * B3 := by simp

example := inst_azumaRandProxy_max

/-- The shift slack `δ = 1 + Σ_{j<4} e_j` of the peeling instance. -/
def δ3 : ℝ := 1 + ∑ j ∈ Finset.range 4, difRepTail_eSeq sz0 E12 sInst tInst (fun _ => 4) 0 3 j

theorem δ3_pos : 0 < δ3 := by
  unfold δ3
  have : 0 ≤ ∑ j ∈ Finset.range 4, difRepTail_eSeq sz0 E12 sInst tInst (fun _ => 4) 0 3 j :=
    Finset.sum_nonneg fun j hj => difRepTail_eSeq_nonneg sz0 E12 sInst tInst (fun _ => 4) 0 j hE12
      (hs0 0) (hst 0) ht0 (by have := Finset.mem_range.1 hj; omega) 3
  linarith

/-- The number of levels of the peeling instance: `⌈m N (16 N)^{2m+2} / δ⌉` at `m = 3`. -/
def Lmax3 : ℕ := ⌈((3 : ℕ) : ℝ) * ((sz0.size 0 : ℕ) : ℝ) * (16 * ((sz0.size 0 : ℕ) : ℝ)) ^ (2 * 3 + 2) /
  δ3⌉₊

/-- **`difRep2_peel` (Amend 2 (ii)) at the data**: the complex increments `ζ_j = Z_{j,0}` of the grid
`K ≡ 4`, the threshold increments `a_j = Δ ‖𝓔⊗𝓔_{u_j}‖`, the proxy `v_j = Δ m Re 𝓔⊗𝓔_{u_{j+1}}`, the
slack `e_j = Δ eeShiftErrN`, `c = m = 3`, `δ = 1 + Σ e_j`, `ρ = 1`, `L = ⌈m N (16 N)^{2m+2}/δ⌉`:
`μ(∃ k ≤ 4, (Σ_{j<k} a_j + δ)^{1/2} < |Σ_{j<k} Z_{j,0}|) ≤ (L + 1) · 4 e^{-1/(16 · 3)}`. -/
theorem inst_peel :
    (pathP sz0).real {ω | ∃ k, k ≤ 4 ∧
      1 * (∑ j ∈ Finset.range k, difRepTail_aSeq sz0 E12 sInst tInst (fun _ => 4) 0 σ3 a0 j ω + δ3) ^
        (1 / 2 : ℝ) < ‖∑ j ∈ Finset.range k, ZvecN sz0 E12 sInst tInst (fun _ => 4) 0 j σ3 ω a0‖} ≤
      ((Lmax3 : ℝ) + 1) * (4 * Real.exp (-(1 : ℝ) ^ 2 / (16 * ((3 : ℕ) : ℝ)))) := by
  have hmgf := fun (j : ℕ) (hj : j < 4) (r : ℝ) =>
    difRepTail_Z_mgf sz0 E12 sInst tInst (fun _ => 4) 0 j hE12 (hs0 0) (hst 0) ht0 (by omega)
      (m := 3) (by norm_num) σ3 a0 r
  have hesum : ∑ j ∈ Finset.range 4, difRepTail_eSeq sz0 E12 sInst tInst (fun _ => 4) 0 3 j ≤ δ3 := by
    unfold δ3; linarith
  have haL : ∀ ω : PathΩ sz0, ∑ j ∈ Finset.range 4,
      difRepTail_aSeq sz0 E12 sInst tInst (fun _ => 4) 0 σ3 a0 j ω ≤ 2 ^ Lmax3 * δ3 := by
    intro ω
    refine (difRepTail_aSum_le sz0 E12 sInst tInst (fun _ => 4) 0 hE12 (hst 0) ht0 (by norm_num)
      (m := 3) σ3 a0 eta_inst (by rw [gridStep_inst]; norm_num) ω).trans ?_
    have h1 : ((3 : ℕ) : ℝ) * ((sz0.size 0 : ℕ) : ℝ) * (16 * ((sz0.size 0 : ℕ) : ℝ)) ^ (2 * 3 + 2) /
        δ3 ≤ (Lmax3 : ℝ) := Nat.le_ceil _
    have h2 : (Lmax3 : ℝ) < 2 ^ Lmax3 := by exact_mod_cast Nat.lt_two_pow_self
    rw [div_le_iff₀ δ3_pos] at h1
    nlinarith [δ3_pos]
  exact difRep2_peel (pathP sz0) (filt sz0)
    (fun j ω => ZvecN sz0 E12 sInst tInst (fun _ => 4) 0 j σ3 ω a0)
    (fun j => difRepTail_aSeq sz0 E12 sInst tInst (fun _ => 4) 0 σ3 a0 j)
    (fun j => difRepTail_vSeq sz0 E12 sInst tInst (fun _ => 4) 0 σ3 a0 j)
    (fun j => difRepTail_eSeq sz0 E12 sInst tInst (fun _ => 4) 0 3 j) 4 Lmax3 ((3 : ℕ) : ℝ) δ3 1
    (by norm_num) δ3_pos zero_le_one
    (fun j _ => difRepTail_Zre_sm sz0 E12 sInst tInst (fun _ => 4) 0 j σ3 a0)
    (fun j _ => difRepTail_Zim_sm sz0 E12 sInst tInst (fun _ => 4) 0 j σ3 a0)
    (fun j _ => difRepTail_aSeq_sm sz0 E12 sInst tInst (fun _ => 4) 0 j σ3 a0)
    (fun j _ => difRepTail_vSeq_sm sz0 E12 sInst tInst (fun _ => 4) 0 j σ3 a0)
    (fun j _ ω => difRepTail_aSeq_nonneg sz0 E12 sInst tInst (fun _ => 4) 0 (hst 0) σ3 a0 j ω)
    (fun j hj ω => difRepTail_vSeq_nonneg sz0 E12 sInst tInst (fun _ => 4) 0 j hE12 (hs0 0) (hst 0)
      ht0 (by omega) (m := 3) (by norm_num) σ3 a0 ω)
    (fun j hj => difRepTail_eSeq_nonneg sz0 E12 sInst tInst (fun _ => 4) 0 j hE12 (hs0 0) (hst 0)
      ht0 (by omega) 3)
    (fun j hj ω => difRepTail_vSeq_le sz0 E12 sInst tInst (fun _ => 4) 0 j hE12 (hs0 0) (hst 0)
      ht0 (by omega) σ3 a0 ω)
    hesum haL
    (fun j hj r => (hmgf j hj r).1) (fun j hj r => (hmgf j hj r).2.1)
    (fun j hj r => (hmgf j hj r).2.2.1) (fun j hj r => (hmgf j hj r).2.2.2)

example := inst_peel

/-- The threshold increments `a_j = v_j / m` of the literal peeling instance (so `e ≡ 0`, `m = 3`). -/
def aN (j : ℕ) (ω : PathΩ sz0) : ℝ :=
  (1 / ((3 : ℕ) : ℝ)) * difRepTail_vSeq sz0 E12 sInst tInst (fun _ => 4) 0 σ3 a0 j ω

/-- The number of levels of the literal peeling instance: `⌈4 B N⌉` (`D = 1`). -/
def LmaxN : ℕ := ⌈4 * B3 * ((sz0.size 0 : ℕ) : ℝ) ^ (1 : ℝ)⌉₊

/-- **`difRep2_peel_N` (Amend 2 (ii), the literal form) at the data**: `N = N_0`, `D = 1`, `ε' = 1/10`,
`m = 3`, the complex increments `Z_{j,0}` of the grid `K ≡ 4`, the thresholds `a_j = v_j/m`, `e ≡ 0`:
`μ(∃ k ≤ 4, N^{ε'} (Σ_{j<k} a_j + N^{-1})^{1/2} < |Σ_{j<k} Z_{j,0}|) ≤ (L + 1) · 4 e^{-N^{2ε'}/(64 m)}`. -/
theorem inst_peel_N :
    (pathP sz0).real {ω | ∃ k, k ≤ 4 ∧
      ((sz0.size 0 : ℕ) : ℝ) ^ (1 / 10 : ℝ) *
        (∑ j ∈ Finset.range k, aN j ω + ((sz0.size 0 : ℕ) : ℝ) ^ (-(1 : ℝ))) ^ (1 / 2 : ℝ) <
          ‖∑ j ∈ Finset.range k, ZvecN sz0 E12 sInst tInst (fun _ => 4) 0 j σ3 ω a0‖} ≤
      ((LmaxN : ℝ) + 1) * (4 * Real.exp (-((sz0.size 0 : ℕ) : ℝ) ^ (2 * (1 / 10 : ℝ)) /
        (64 * ((3 : ℕ) : ℝ)))) := by
  have hmgf := fun (j : ℕ) (hj : j < 4) (r : ℝ) =>
    difRepTail_Z_mgf sz0 E12 sInst tInst (fun _ => 4) 0 j hE12 (hs0 0) (hst 0) ht0 (by omega)
      (m := 3) (by norm_num) σ3 a0 r
  have hN : (1 : ℝ) ≤ ((sz0.size 0 : ℕ) : ℝ) := by exact_mod_cast sz0.one_le_size 0
  have hv0 := fun (j : ℕ) (hj : j < 4) (ω : PathΩ sz0) =>
    difRepTail_vSeq_nonneg sz0 E12 sInst tInst (fun _ => 4) 0 j hE12 (hs0 0) (hst 0) ht0
      (by omega) (m := 3) (by norm_num) σ3 a0 ω
  have haL : ∀ ω : PathΩ sz0, ∑ j ∈ Finset.range 4, aN j ω ≤
      2 ^ LmaxN * ((sz0.size 0 : ℕ) : ℝ) ^ (-(1 : ℝ)) := by
    intro ω
    have hcrude := fun (j : ℕ) (hj : j < 4) =>
      difRepTail_vSeq_le_crude sz0 E12 sInst tInst (fun _ => 4) 0 j hE12 (hs0 0) (hst 0) ht0
        (by omega) (m := 3) σ3 a0 (eta_inst (j + 1) (by omega)) ω
    have hsum : ∑ j ∈ Finset.range 4, aN j ω ≤ 4 * B3 := by
      calc ∑ j ∈ Finset.range 4, aN j ω ≤ ∑ j ∈ Finset.range 4, B3 := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hj' := Finset.mem_range.1 hj
            unfold aN
            have h1 : difRepTail_vSeq sz0 E12 sInst tInst (fun _ => 4) 0 σ3 a0 j ω ≤ B3 :=
              hcrude j hj'
            have h2 := hv0 j hj' ω
            have hB := B3_pos
            norm_num
            linarith
        _ = 4 * B3 := by simp
    refine hsum.trans ?_
    have h1 : 4 * B3 * ((sz0.size 0 : ℕ) : ℝ) ^ (1 : ℝ) ≤ (LmaxN : ℝ) := Nat.le_ceil _
    have h2 : (LmaxN : ℝ) < 2 ^ LmaxN := by exact_mod_cast Nat.lt_two_pow_self
    rw [Real.rpow_one] at h1
    rw [Real.rpow_neg_one]
    have hN0 : (0 : ℝ) < ((sz0.size 0 : ℕ) : ℝ) := by linarith
    rw [← div_eq_mul_inv, le_div_iff₀ hN0]
    linarith
  exact difRep2_peel_N (pathP sz0) (filt sz0)
    (fun j ω => ZvecN sz0 E12 sInst tInst (fun _ => 4) 0 j σ3 ω a0) aN
    (fun j => difRepTail_vSeq sz0 E12 sInst tInst (fun _ => 4) 0 σ3 a0 j) (fun _ => 0) 4 LmaxN 3
    ((sz0.size 0 : ℕ) : ℝ) 1 (1 / 10) (by norm_num) hN
    (fun j _ => difRepTail_Zre_sm sz0 E12 sInst tInst (fun _ => 4) 0 j σ3 a0)
    (fun j _ => difRepTail_Zim_sm sz0 E12 sInst tInst (fun _ => 4) 0 j σ3 a0)
    (fun j _ => (difRepTail_vSeq_sm sz0 E12 sInst tInst (fun _ => 4) 0 j σ3 a0).const_mul _)
    (fun j _ => difRepTail_vSeq_sm sz0 E12 sInst tInst (fun _ => 4) 0 j σ3 a0)
    (fun j hj ω => mul_nonneg (by positivity) (hv0 j hj ω)) hv0
    (fun j _ => le_rfl)
    (fun j hj ω => by
      unfold aN
      have : ((3 : ℕ) : ℝ) ≠ 0 := by norm_num
      field_simp
      simp)
    (by simp only [Finset.sum_const_zero]; positivity) haL
    (fun j hj r => (hmgf j hj r).1) (fun j hj r => (hmgf j hj r).2.1)
    (fun j hj r => (hmgf j hj r).2.2.1) (fun j hj r => (hmgf j hj r).2.2.2)

example := inst_peel_N

/-- **`gridRepTailN_holds` (target 3) at the flow data**, every loop length `m ≥ 2` (`D = 1`,
`ε' = 1/10`): the grid exponent `CK` it returns, the grid `K_n = ⌈N^{CK}⌉ + 1`, and the tail bound
`≤ N^{-1}` eventually, for every label `(σ, a)`. -/
theorem inst_gridRepTailN (m : ℕ) (hm : 2 ≤ m) :
    ∃ CK : ℝ, 0 ≤ CK ∧ ∃ K : ℕ → ℕ, (∀ n, K n ≠ 0) ∧
      (∀ᶠ n in atTop, ((sz0.size n : ℕ) : ℝ) ^ CK ≤ K n) ∧
      (∀ᶠ n in atTop, ∀ i : (Fin m → Bool) × (Fin m → Zd 3 (sz0.L n)),
        pathP sz0 {ω | ∃ k, k ≤ K n ∧
          ((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) *
              (∑ j ∈ Finset.range k, gridStep sInst tInst K n *
                ‖sz0.STeeM n (STflowE z0 n) (gridTime sInst tInst K n j)
                  (pathH sz0 sInst tInst K n j ω) i.1 i.2 i.2‖ +
                ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) ^ (1 / 2 : ℝ) <
            ‖difRepMartN sz0 (STflowE z0) sInst tInst K n i k ω‖} ≤
          ENNReal.ofReal (((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)))) := by
  obtain ⟨CK, hCK, h⟩ := gridRepTailN_holds 3 m hm (1 / 10) (1 / 10) (1 / 10)
    (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0 sInst tInst hs0 hst htT 1
    one_pos
  have hK0 : ∀ n, ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ + 1 ≠ 0 := fun n => Nat.succ_ne_zero _
  have hKN : ∀ᶠ n in atTop, ((sz0.size n : ℕ) : ℝ) ^ CK ≤
      ((⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ + 1 : ℕ) : ℝ) :=
    Eventually.of_forall fun n => (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ _)
  exact ⟨CK, hCK, fun n => ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ + 1, hK0, hKN,
    h (fun n => ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ + 1) hK0 hKN (1 / 10) (by norm_num)⟩

/-- `gridRepTailN_holds` at `m = 2` and `m = 3` on the flow data. -/
example := inst_gridRepTailN 2 le_rfl
example := inst_gridRepTailN 3 (by norm_num)

/-- **`stGridMart_holds` (target 4) at `d = 3`**: the pin `STGridMart 3` is unconditional. -/
example : STGridMart 3 := stGridMart_holds 3 (by norm_num)

/-- **`stGridMartAt_holds` (target 4) at `d = 3`**: the loop-length-`2` pin at `C₀ = 11`. -/
example : STGridMartAt 3 11 := stGridMartAt_holds 3 (by norm_num)

/-- **`STOptL2 3` through `stOptL2_of_pins`** with `STLWB 3` (another gate's pin) as the only hypothesis:
the `STGridMart` premise is the proved `stGridMart_holds`. -/
example (hLWB : STLWB 3) : STOptL2 3 :=
  stOptL2_of_pins (by norm_num) hLWB (stGridMart_holds 3 (by norm_num))

/-- **`STStep2 3` through `ST_step2_of_pins'`**: the `hMart` premise is the proved `stGridMart_holds`;
the other pins of the chain (`STNewKLK`, `STLWT`, `STEMn2Exp`, `STOptL2`, `STLocalAvgOfL2`) stay hypotheses
(CLAUDE.md §4 step 2; DECISIONS §36 (iii)). -/
example (hNew : STNewKLK 3) (hLWT : STLWT 3) (hEMe : STEMn2Exp 3) (hOpt : STOptL2 3)
    (hClos : STLocalAvgOfL2 3) : STStep2 3 :=
  ST_step2_of_pins' hNew hLWT hEMe (stGridMart_holds 3 (by norm_num)) hOpt hClos

end RBM.Ind.DifREP2Inst

end
