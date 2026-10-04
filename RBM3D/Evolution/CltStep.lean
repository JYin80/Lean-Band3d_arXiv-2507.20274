/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Evolution.CltGood
import RBM3D.Evolution.CltPath
import RBM3D.Evolution.CltSwap
import RBM3D.Induction.Step5Pins

/-!
# The CLT step and the isolation bound `STCltIso` (ticket T2152, row S5-21)

Paper (arXiv:2507.20274): `(eq:bound_isolated)` (`3_5:2245-2248`, "does not depend on `d`", cited
from [DYYY25, (7.39)] and [RBSO1D, (A.112)]).  The proof here is the i.i.d.-copy route of RBM2D,
which is not in the paper (the paper cites the estimate).  Port of RBM2D `Evolution/CltStep.lean`
(`cltstep_core`, `cltStep`) and of the assembly `cltFar` of
`Evolution/CltDecorrelation.lean:286-376` (commit `c9a24cf`; `cltdec_core`, `cltdec_exponent`) onto
the fine model
`RBM3D/Gauss/FineModel.lean`, with the dictionary `Coord ↦ CoordF d`, `P L W ↦ PF d L W g`,
`Z2, zdist2 ↦ Zd d, zdistInf`, `LocalForm L W 1 K ↦ LocalForm d L W k K`.  What is new against
RBM2D (portmap P.5 row S5-21, finding F-B):

* the factors are the `2p` two-label forms `𝗕_{b^{(k)}}` of `STcltB` (`3_5:2217`), not one common
  one-label form: the path bound is `cltPathMulti_bound` with `k = 2` labels, applied factor by
  factor;
* the scales are logarithmic (DECISIONS §43): window `w_n = (log W)^3 ℓ_s`, locality radius
  `ρ = w_n + 1`, separation `R = 8 w_n` (isolation `10 w_n` on the first labels, `cltFarGeomHalf`,
  then the window: `5 w_n - w_n = 4 w_n = R/2`), far threshold `θ_n = max (3 w_n - 2) w_n` with
  `θ_n ≤ R/2 - ρ - 1 = 3 w_n - 2` for `w_n ≥ 1` (`cltStep_geom`, `cltStep`);
* the good event is the single event of `cltGood_whp` (bad pair set of measure `≤ 4 N^{-D''}`, not
  `6 N^{-D''}`), and the coefficients are bounded eventually (`(eq:WO)`), not for all `n`.

Results (namespace `RBM.Evol` unless stated):

* item 1: `cltStep_loopForm` (the two-label local form of `STcltB`:
  `scale · W^{-2d} Σ_{y∈[b₂], x∈[b₁]} G(σ₁)_{yx} G(σ₂)_{xy}` in the window, `0` outside),
  `cltStep_loopForm_eval`, `cltStep_loopForm_stcltB` (`STcltB = cltEvalAt − scale · 𝒦`),
  `cltStep_loopForm_local` (`Local (w_n + 1)`), `cltStep_loopForm_coef_le`, `cltStep_scale_le`,
  `cltStep_loopForm_coef_le_eventually` (`‖coef‖ ≤ N²` eventually);
* item 2: `cltStep` (one real coordinate of the telescoping:
  `‖∫ (X_i(T_j) - X_i(T_{j+1})) Γ_i‖ ≤ N^{-D-3}`, eventually, uniformly in the labels, the isolated
  index, the enumeration and the step);
* item 3: `RBM.Gauss.Sizes.stCltIso_holds : STCltIso d` (the registry line of `STCltIso` is
  deleted).

The regime `STReg5I`, the condition `σ₁ ≠ σ₂` and the Step 1-4 premises other than `STFlow`,
`STStep2Concl` (inside `HClt`) are not used.  Instances (`d = 3`, `Step5Inst.szCL`): section 8 at
the end of the file.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Evol

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal ENNReal

/-! ## 1. The factors `X_m` and `Γ_i` -/

section Defs

variable {d L W K k : ℕ} [NeZero L] [NeZero W]

/-- The centred factor `X_m`: `Y_{b_m} - 𝔼Y_{b_m}` for `m < p`, its conjugate for `m ≥ p`
(the integrand of `(eq:bound_isolated)`, on the finite model `PF d L W g`). -/
def cltStep_Xo {p : ℕ} (F : LocalForm d L W k K) (g E u : ℝ) (b : Fin (2 * p) → Fin k → Zd d L)
    (m : Fin (2 * p)) (ω : Ω d L W) : ℂ :=
  if (m : ℕ) < p then
    cltEvalAt F E u ω (b m) - ∫ ω', cltEvalAt F E u ω' (b m) ∂(PF d L W g)
  else (starRingEnd ℂ) (cltEvalAt F E u ω (b m) - ∫ ω', cltEvalAt F E u ω' (b m) ∂(PF d L W g))

/-- `Γ_i = ∏_{m ≠ i} X_m`. -/
def cltStep_Gamma {p : ℕ} (F : LocalForm d L W k K) (g E u : ℝ) (b : Fin (2 * p) → Fin k → Zd d L)
    (i : Fin (2 * p)) (ω : Ω d L W) : ℂ :=
  ∏ m ∈ Finset.univ.erase i, cltStep_Xo F g E u b m ω

end Defs

/-! ## 2. Private helpers -/

section Helpers

variable {d L W K k : ℕ} [NeZero L] [NeZero W]

private theorem cltStep_gEntry_meas (E s u : ℝ) (σ : Bool) (x y : Idx d L W) :
    Measurable fun ω : Ω d L W => gEntry d L W E s (Hflow d L W u ω) σ x y := by
  have hH : Measurable fun ω : Ω d L W => Hflow d L W u ω :=
    Measurable.of_eval fun a => Measurable.of_eval fun b => measurable_Hflow d L W u a b
  exact (walk_measurable_Gres_apply (zt E s) σ x y).comp hH

private theorem cltStep_eval_meas (F : LocalForm d L W k K) (E u : ℝ) (b : Fin k → Zd d L) :
    Measurable fun ω : Ω d L W => cltEvalAt F E u ω b := by
  unfold cltEvalAt LocalForm.eval
  refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun q _ => ?_
  exact measurable_const.mul
    (Finset.measurable_prod _ fun i _ => cltStep_gEntry_meas E u u _ _ _)

private theorem cltStep_Xo_meas {p : ℕ} (F : LocalForm d L W k K) (g E u : ℝ)
    (b : Fin (2 * p) → Fin k → Zd d L) (m : Fin (2 * p)) :
    Measurable (cltStep_Xo F g E u b m) := by
  have h1 := (cltStep_eval_meas F E u (b m)).sub_const
    (∫ ω', cltEvalAt F E u ω' (b m) ∂(PF d L W g))
  by_cases hm : (m : ℕ) < p
  · have h : cltStep_Xo F g E u b m =
        fun ω => cltEvalAt F E u ω (b m) - ∫ ω', cltEvalAt F E u ω' (b m) ∂(PF d L W g) := by
      funext ω; simp only [cltStep_Xo, hm, ↓reduceIte]
    rw [h]; exact h1
  · have h : cltStep_Xo F g E u b m =
        fun ω => (starRingEnd ℂ)
          (cltEvalAt F E u ω (b m) - ∫ ω', cltEvalAt F E u ω' (b m) ∂(PF d L W g)) := by
      funext ω; simp only [cltStep_Xo, hm, ↓reduceIte]
    rw [h]; exact Complex.continuous_conj.measurable.comp h1

private theorem cltStep_Gamma_meas {p : ℕ} (F : LocalForm d L W k K) (g E u : ℝ)
    (b : Fin (2 * p) → Fin k → Zd d L) (i : Fin (2 * p)) :
    Measurable (cltStep_Gamma F g E u b i) := by
  have h : cltStep_Gamma F g E u b i = fun ω => ∏ m ∈ Finset.univ.erase i, cltStep_Xo F g E u b m ω := rfl
  rw [h]
  exact Finset.measurable_prod _ fun m _ => cltStep_Xo_meas F g E u b m

/-- The centring cancels in a difference, and conjugation is an isometry. -/
private theorem cltStep_Xo_sub {p : ℕ} (F : LocalForm d L W k K) (g E u : ℝ)
    (b : Fin (2 * p) → Fin k → Zd d L) (m : Fin (2 * p)) (ω ω' : Ω d L W) :
    ‖cltStep_Xo F g E u b m ω - cltStep_Xo F g E u b m ω'‖ =
      ‖cltEvalAt F E u ω (b m) - cltEvalAt F E u ω' (b m)‖ := by
  by_cases hm : (m : ℕ) < p
  · simp only [cltStep_Xo, hm, ↓reduceIte, sub_sub_sub_cancel_right]
  · simp only [cltStep_Xo, hm, ↓reduceIte]
    rw [← map_sub, Complex.norm_conj, sub_sub_sub_cancel_right]

private theorem cltStep_Xo_le {p : ℕ} (F : LocalForm d L W k K) (g E u : ℝ)
    (b : Fin (2 * p) → Fin k → Zd d L) {BY : ℝ} (hY : ∀ ω b', ‖cltEvalAt F E u ω b'‖ ≤ BY)
    (m : Fin (2 * p)) (ω : Ω d L W) : ‖cltStep_Xo F g E u b m ω‖ ≤ 2 * BY := by
  have hint : ‖∫ ω', cltEvalAt F E u ω' (b m) ∂(PF d L W g)‖ ≤ BY := by
    have h := norm_integral_le_of_norm_le_const (μ := PF d L W g)
      (f := fun ω' => cltEvalAt F E u ω' (b m)) (Filter.Eventually.of_forall fun ω' => hY ω' (b m))
    simpa using h
  have h1 : ‖cltEvalAt F E u ω (b m) - ∫ ω', cltEvalAt F E u ω' (b m) ∂(PF d L W g)‖ ≤ 2 * BY := by
    have := norm_sub_le (cltEvalAt F E u ω (b m)) (∫ ω', cltEvalAt F E u ω' (b m) ∂(PF d L W g))
    linarith [hY ω (b m)]
  by_cases hm : (m : ℕ) < p
  · simpa only [cltStep_Xo, hm, ↓reduceIte] using h1
  · simpa only [cltStep_Xo, hm, ↓reduceIte, Complex.norm_conj] using h1

private theorem cltStep_Gamma_le {p : ℕ} (F : LocalForm d L W k K) (g E u : ℝ)
    (b : Fin (2 * p) → Fin k → Zd d L) {X : ℝ} (hX1 : 1 ≤ X)
    (hX : ∀ m ω, ‖cltStep_Xo F g E u b m ω‖ ≤ X) (i : Fin (2 * p)) (ω : Ω d L W) :
    ‖cltStep_Gamma F g E u b i ω‖ ≤ X ^ (2 * p) := by
  unfold cltStep_Gamma
  rw [norm_prod]
  calc ∏ m ∈ Finset.univ.erase i, ‖cltStep_Xo F g E u b m ω‖ ≤ ∏ _m ∈ Finset.univ.erase i, X :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun m _ => hX m ω
    _ = X ^ (Finset.univ.erase i).card := Finset.prod_const X
    _ ≤ X ^ (2 * p) := pow_le_pow_right₀ hX1 (Finset.card_erase_le.trans (by simp))

/-- `X_m` is centred: `∫ X_m dPF = 0`. -/
private theorem cltStep_Xo_integral {p : ℕ} (F : LocalForm d L W k K) (g E u : ℝ) {BY : ℝ}
    (hY : ∀ ω b', ‖cltEvalAt F E u ω b'‖ ≤ BY) (b : Fin (2 * p) → Fin k → Zd d L)
    (m : Fin (2 * p)) : ∫ ω, cltStep_Xo F g E u b m ω ∂(PF d L W g) = 0 := by
  have hint : Integrable (fun ω => cltEvalAt F E u ω (b m)) (PF d L W g) :=
    Integrable.of_bound (cltStep_eval_meas F E u (b m)).aestronglyMeasurable BY
      (Filter.Eventually.of_forall fun ω => hY ω (b m))
  have h0 : ∫ ω, (cltEvalAt F E u ω (b m) - ∫ ω', cltEvalAt F E u ω' (b m) ∂(PF d L W g))
      ∂(PF d L W g) = 0 := by
    rw [integral_sub hint (integrable_const _), integral_const]
    simp
  by_cases hm : (m : ℕ) < p
  · simp only [cltStep_Xo, hm, ↓reduceIte]
    exact h0
  · simp only [cltStep_Xo, hm, ↓reduceIte]
    rw [integral_conj, h0]
    simp

private theorem cltStep_coefSum_nonneg (F : LocalForm d L W k K) (b : Fin k → Zd d L) :
    0 ≤ cltCoefSumMulti F b :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

/-- The coefficient weight in terms of the coefficient bound and `card Idx`. -/
private theorem cltStep_coefSum_le (F : LocalForm d L W k K) {C0 : ℝ} (hC0 : 0 ≤ C0)
    (hC : ∀ b j q, ‖F.coef b j q‖ ≤ C0) (b : Fin k → Zd d L) :
    cltCoefSumMulti F b ≤
      (K + 1) * ((2 * (Fintype.card (Idx d L W) : ℝ) ^ 2) ^ K * (C0 * K * 4 ^ K)) := by
  unfold cltCoefSumMulti
  have h1 : 1 ≤ 2 * (Fintype.card (Idx d L W) : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ Fintype.card (Idx d L W) := by exact_mod_cast Fintype.card_pos
    nlinarith
  have hA : 0 ≤ C0 * K * 4 ^ K := by positivity
  calc ∑ j : Fin (K + 1), ∑ q : Fin j → Idx d L W × Idx d L W × Bool,
        ‖F.coef b j q‖ * (j : ℝ) * 4 ^ (j : ℕ)
      ≤ ∑ j : Fin (K + 1), ∑ _q : Fin j → Idx d L W × Idx d L W × Bool, C0 * K * 4 ^ K := by
        refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun q _ => ?_
        have hj : (j : ℕ) ≤ K := Nat.lt_succ_iff.mp j.2
        have hj' : ((j : ℕ) : ℝ) ≤ K := by exact_mod_cast hj
        have h4 : (4 : ℝ) ^ (j : ℕ) ≤ 4 ^ K := pow_le_pow_right₀ (by norm_num) hj
        exact mul_le_mul (mul_le_mul (hC _ j q) hj' (Nat.cast_nonneg _) hC0) h4 (by positivity)
          (mul_nonneg hC0 (Nat.cast_nonneg _))
    _ = ∑ j : Fin (K + 1), (2 * (Fintype.card (Idx d L W) : ℝ) ^ 2) ^ (j : ℕ) * (C0 * K * 4 ^ K) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        congr 1
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod (Idx d L W) (Idx d L W × Bool),
          Fintype.card_prod (Idx d L W) Bool, Fintype.card_bool]
        push_cast
        ring
    _ ≤ ∑ _j : Fin (K + 1), (2 * (Fintype.card (Idx d L W) : ℝ) ^ 2) ^ K * (C0 * K * 4 ^ K) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ h1 (Nat.lt_succ_iff.mp j.2)) hA
    _ = (K + 1) * ((2 * (Fintype.card (Idx d L W) : ℝ) ^ 2) ^ K * (C0 * K * 4 ^ K)) := by
        simp

end Helpers

/-- The finite-product difference bound: `|∏ f - ∏ g| ≤ #s · X^{#s} · δ` when all factors are
`≤ X` (`X ≥ 1`) and differ by `≤ δ`. -/
private theorem cltStep_prod_sub_le {ι : Type*} (s : Finset ι) (f g : ι → ℂ)
    {X δ : ℝ} (hX : 1 ≤ X) (hδ : 0 ≤ δ) (hf : ∀ j ∈ s, ‖f j‖ ≤ X) (hg : ∀ j ∈ s, ‖g j‖ ≤ X)
    (hfg : ∀ j ∈ s, ‖f j - g j‖ ≤ δ) :
    ‖∏ j ∈ s, f j - ∏ j ∈ s, g j‖ ≤ s.card * X ^ s.card * δ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have ih' := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => hg j (Finset.mem_insert_of_mem hj))
      (fun j hj => hfg j (Finset.mem_insert_of_mem hj))
    have hX0 : 0 ≤ X := by linarith
    have hfs : ‖∏ j ∈ s, f j‖ ≤ X ^ s.card := by
      rw [norm_prod]
      calc ∏ j ∈ s, ‖f j‖ ≤ ∏ _j ∈ s, X :=
            Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
              fun j hj => hf j (Finset.mem_insert_of_mem hj)
        _ = X ^ s.card := Finset.prod_const X
    have hga := hg a (Finset.mem_insert_self a s)
    have hfga := hfg a (Finset.mem_insert_self a s)
    have e : f a * ∏ j ∈ s, f j - g a * ∏ j ∈ s, g j =
        (f a - g a) * ∏ j ∈ s, f j + g a * (∏ j ∈ s, f j - ∏ j ∈ s, g j) := by ring
    have hpow : X ^ s.card ≤ X ^ s.card * X := le_mul_of_one_le_right (pow_nonneg hX0 _) hX
    have hp0 : 0 ≤ X ^ s.card := pow_nonneg hX0 _
    have hc0 : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
    rw [e]
    calc ‖(f a - g a) * ∏ j ∈ s, f j + g a * (∏ j ∈ s, f j - ∏ j ∈ s, g j)‖
        ≤ ‖f a - g a‖ * ‖∏ j ∈ s, f j‖ + ‖g a‖ * ‖∏ j ∈ s, f j - ∏ j ∈ s, g j‖ := by
          refine (norm_add_le _ _).trans (le_of_eq ?_)
          rw [norm_mul, norm_mul]
      _ ≤ δ * X ^ s.card + X * (s.card * X ^ s.card * δ) := by
          gcongr
      _ ≤ ((s.card + 1 : ℕ) : ℝ) * X ^ (s.card + 1) * δ := by
          have h := mul_le_mul_of_nonneg_left hpow hδ
          rw [pow_succ]
          push_cast
          nlinarith [mul_nonneg (mul_nonneg hc0 hp0) hδ]

/-- `‖∫ H‖ ≤ g + M ε` when `‖H‖ ≤ M` everywhere, `‖H‖ ≤ g` off `B`, and `μ B ≤ ε` (no
measurability of `H` or `B` is needed). -/
private theorem cltStep_norm_integral_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (H : α → ℂ) (B : Set α) {g M ε : ℝ} (hg : 0 ≤ g) (hM : 0 ≤ M)
    (hε : 0 ≤ ε) (hB : μ B ≤ ENNReal.ofReal ε) (hall : ∀ x, ‖H x‖ ≤ M)
    (hgood : ∀ x, x ∉ B → ‖H x‖ ≤ g) : ‖∫ x, H x ∂μ‖ ≤ g + M * ε := by
  have hBm : MeasurableSet (toMeasurable μ B) := measurableSet_toMeasurable μ B
  have hdom : ∀ x, ‖H x‖ ≤ g + (toMeasurable μ B).indicator (fun _ => M) x := by
    intro x
    by_cases hx : x ∈ toMeasurable μ B
    · rw [Set.indicator_of_mem hx]; linarith [hall x]
    · rw [Set.indicator_of_notMem hx, add_zero]
      exact hgood x fun h => hx (subset_toMeasurable μ B h)
  have hi1 : Integrable (fun _ : α => g) μ := integrable_const g
  have hi2 : Integrable (fun x => (toMeasurable μ B).indicator (fun _ => M) x) μ :=
    (integrable_const M).indicator hBm
  have hreal : μ.real (toMeasurable μ B) ≤ ε := by
    rw [measureReal_def, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hε hB
  calc ‖∫ x, H x ∂μ‖ ≤ ∫ x, (g + (toMeasurable μ B).indicator (fun _ => M) x) ∂μ :=
        norm_integral_le_of_norm_le (hi1.add hi2) (Filter.Eventually.of_forall hdom)
    _ = g + μ.real (toMeasurable μ B) * M := by
        rw [integral_add hi1 hi2, integral_const, integral_indicator hBm, setIntegral_const]
        simp [smul_eq_mul]
    _ ≤ g + M * ε := by nlinarith

/-- Pull-back of any set along a measure-preserving map. -/
private theorem cltStep_pull_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → β} (hf : MeasurePreserving f μ ν) (S : Set β) :
    μ (f ⁻¹' S) ≤ ν S := by
  calc μ (f ⁻¹' S) ≤ μ.map f S := Measure.le_map_apply hf.measurable.aemeasurable S
    _ = ν S := by rw [hf.map_eq]

/-- A coordinate of variance `0` is `0` almost surely. -/
private theorem cltStep_ae_zero {d L W : ℕ} [NeZero L] [NeZero W] (g : ℝ) (c : CoordF d L W)
    (hc : gvarF d L W g c = 0) : ∀ᵐ ω ∂(PF d L W g), ω c = 0 := by
  have hmap : (PF d L W g).map (fun ω : Ω d L W => ω c) = gaussianReal 0 (gvarF d L W g c) :=
    Measure.infinitePi_map_eval _ c
  rw [hc, gaussianReal_zero_var] at hmap
  have h : ∀ᵐ x ∂((PF d L W g).map (fun ω : Ω d L W => ω c)), x = 0 := by
    rw [hmap]
    exact (ae_dirac_iff (measurableSet_singleton (0 : ℝ))).2 rfl
  exact ae_of_ae_map (measurable_pi_apply c).aemeasurable h

/-! ## 3. The step at one size -/

/-- **The step at one size** (deterministic inputs and probability bounds as hypotheses).  With
`‖X_m‖ ≤ X` (`X ≥ 1`), `4 · cltCoefSumMulti ≤ Bc`, the coordinate tails and the good set of
probability `≥ 1 - ε`, and the side conditions of `cltPathMulti_bound`, one step of the telescoping
is bounded by `4p X^{2p+1} Bc W^{-D'} + 4 X^{2p+1} · 4ε`.  The geometry enters through `hgeom`:
every block `a` is far (`R/2`) from all labels of `b_i` (case A) or from all labels of every
`b_m`, `m ≠ i` (case B). -/
private theorem cltStep_core {d L W K k : ℕ} [NeZero L] [NeZero W] (g : ℝ)
    (F : LocalForm d L W k K) (E u ρ R θ D' : ℝ) {p : ℕ} (hp : 1 ≤ p)
    (b : Fin (2 * p) → Fin k → Zd d L) (i : Fin (2 * p))
    (e : CoordF d L W ≃ Fin (Fintype.card (CoordF d L W))) (j : ℕ)
    (hj : j < Fintype.card (CoordF d L W))
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hz : (zt E u).im ≠ 0) (hloc : F.Local ρ)
    (hθ : 16 * (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1) (hθR : θ ≤ R / 2 - ρ - 1)
    (hgeom : ∀ a : Zd d L, (∀ m', R / 2 ≤ (zdistInf d L (a - b i m') : ℝ)) ∨
      (∀ m, m ≠ i → ∀ m', R / 2 ≤ (zdistInf d L (a - b m m') : ℝ)))
    {X Bc ε : ℝ} (hX1 : 1 ≤ X) (hX : ∀ m ω, ‖cltStep_Xo F g E u b m ω‖ ≤ X)
    (hBc0 : 0 ≤ Bc) (hBc : ∀ b', 4 * cltCoefSumMulti F b' ≤ Bc) (hε : 0 ≤ ε)
    (hE1 : ∀ c : CoordF d L W,
      PF d L W g {ω | (W : ℝ) ^ (-(1 / 2 : ℝ)) < |ω c|} ≤ ENNReal.ofReal ε)
    (hE2 : PF d L W g {ω | ¬ cltGoodAt d L W E u θ D' ω} ≤ ENNReal.ofReal ε) :
    ‖∫ q, (cltStep_Xo F g E u b i (cltHyb d L W e j q.1 q.2) -
          cltStep_Xo F g E u b i (cltHyb d L W e (j + 1) q.1 q.2)) * cltStep_Gamma F g E u b i q.1
        ∂((PF d L W g).prod (PF d L W g))‖ ≤
      4 * p * (X * X ^ (2 * p)) * (Bc * (W : ℝ) ^ (-D')) + 4 * (X * X ^ (2 * p)) * (4 * ε) := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : CoordF d L W, e.symm ⟨j, hj⟩ = c := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by linarith
  have hQ0 : 0 ≤ X ^ (2 * p) := pow_nonneg hX0 _
  have hγ0 : 0 ≤ (W : ℝ) ^ (-D') := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hG0 : 0 ≤ Bc * (W : ℝ) ^ (-D') := mul_nonneg hBc0 hγ0
  have hv0 : 0 ≤ (W : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hv1 : (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := by linarith
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hXQ0 : 0 ≤ X * X ^ (2 * p) := mul_nonneg hX0 hQ0
  have hg0 : 0 ≤ 4 * p * (X * X ^ (2 * p)) * (Bc * (W : ℝ) ^ (-D')) := by positivity
  have hM0 : 0 ≤ 4 * (X * X ^ (2 * p)) := by positivity
  have h4ε : 0 ≤ 4 * ε := by linarith
  -- the hybrids at `c`
  have hTk : ∀ q : Ω d L W × Ω d L W, cltHyb d L W e j q.1 q.2 c = q.1 c := by
    intro q
    have h := cltHyb_eq_update_succ d L W e j hj q.1 q.2
    rw [hc] at h
    rw [h, Function.update_self]
  have hTk1 : ∀ q : Ω d L W × Ω d L W, cltHyb d L W e (j + 1) q.1 q.2 =
      Function.update (cltHyb d L W e j q.1 q.2) c (q.2 c) := by
    intro q
    have h := cltHyb_succ d L W e j hj q.1 q.2
    rw [hc] at h
    exact h
  -- the bound of the difference factor
  have hdiff : ∀ q : Ω d L W × Ω d L W, ‖cltStep_Xo F g E u b i (cltHyb d L W e j q.1 q.2) -
      cltStep_Xo F g E u b i (cltHyb d L W e (j + 1) q.1 q.2)‖ ≤ 2 * X := by
    intro q
    have h1 := hX i (cltHyb d L W e j q.1 q.2)
    have h2 := hX i (cltHyb d L W e (j + 1) q.1 q.2)
    exact (norm_sub_le _ _).trans (by linarith)
  -- Case 0: `gvarF c = 0`
  by_cases hg : gvarF d L W g c = 0
  · have h1 : ∀ᵐ q ∂((PF d L W g).prod (PF d L W g)), q.1 c = 0 := by
      have h := cltStep_ae_zero g c hg
      rw [← (measurePreserving_fst (μ := PF d L W g) (ν := PF d L W g)).map_eq] at h
      exact ae_of_ae_map measurable_fst.aemeasurable h
    have h2 : ∀ᵐ q ∂((PF d L W g).prod (PF d L W g)), q.2 c = 0 := by
      have h := cltStep_ae_zero g c hg
      rw [← (measurePreserving_snd (μ := PF d L W g) (ν := PF d L W g)).map_eq] at h
      exact ae_of_ae_map measurable_snd.aemeasurable h
    have h0 : ∫ q, (cltStep_Xo F g E u b i (cltHyb d L W e j q.1 q.2) -
          cltStep_Xo F g E u b i (cltHyb d L W e (j + 1) q.1 q.2)) * cltStep_Gamma F g E u b i q.1
        ∂((PF d L W g).prod (PF d L W g)) = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [h1, h2] with q hq1 hq2
      have hq : cltHyb d L W e (j + 1) q.1 q.2 = cltHyb d L W e j q.1 q.2 := by
        rw [hTk1 q, hq2, Function.update_eq_self_iff, hTk q, hq1]
      simp only [Pi.zero_apply, hq, sub_self, zero_mul]
    rw [h0, norm_zero]
    positivity
  have hadj := (cltCoord_adj d L W g c).1 hg
  -- the bad pair set
  obtain ⟨Sb, hSb⟩ : ∃ S : Set (Ω d L W), S = {ω | ¬ cltGoodAt d L W E u θ D' ω} := ⟨_, rfl⟩
  have hSbP : PF d L W g Sb ≤ ENNReal.ofReal ε := by rw [hSb]; exact hE2
  obtain ⟨A1, hA1⟩ : ∃ A : Set (Ω d L W × Ω d L W),
      A = Prod.fst ⁻¹' {ω | (W : ℝ) ^ (-(1 / 2 : ℝ)) < |ω c|} := ⟨_, rfl⟩
  obtain ⟨A2, hA2⟩ : ∃ A : Set (Ω d L W × Ω d L W),
      A = Prod.snd ⁻¹' {ω | (W : ℝ) ^ (-(1 / 2 : ℝ)) < |ω c|} := ⟨_, rfl⟩
  obtain ⟨A3, hA3⟩ : ∃ A : Set (Ω d L W × Ω d L W), A = Prod.fst ⁻¹' Sb := ⟨_, rfl⟩
  obtain ⟨A4, hA4⟩ : ∃ A : Set (Ω d L W × Ω d L W),
      A = (fun q : Ω d L W × Ω d L W => cltHyb d L W e j q.1 q.2) ⁻¹' Sb := ⟨_, rfl⟩
  have hmpT : MeasurePreserving (fun q : Ω d L W × Ω d L W => cltHyb d L W e j q.1 q.2)
      ((PF d L W g).prod (PF d L W g)) (PF d L W g) :=
    measurePreserving_cltSplit d L W g (cltHybSet d L W e j)
  have hmpT1 : MeasurePreserving (fun q : Ω d L W × Ω d L W => cltHyb d L W e (j + 1) q.1 q.2)
      ((PF d L W g).prod (PF d L W g)) (PF d L W g) :=
    measurePreserving_cltSplit d L W g (cltHybSet d L W e (j + 1))
  have hBq : ((PF d L W g).prod (PF d L W g)) (A1 ∪ A2 ∪ A3 ∪ A4) ≤ ENNReal.ofReal (4 * ε) := by
    have h1 : ((PF d L W g).prod (PF d L W g)) A1 ≤ ENNReal.ofReal ε := by
      rw [hA1]; exact (cltStep_pull_le measurePreserving_fst _).trans (hE1 c)
    have h2 : ((PF d L W g).prod (PF d L W g)) A2 ≤ ENNReal.ofReal ε := by
      rw [hA2]; exact (cltStep_pull_le measurePreserving_snd _).trans (hE1 c)
    have h3 : ((PF d L W g).prod (PF d L W g)) A3 ≤ ENNReal.ofReal ε := by
      rw [hA3]; exact (cltStep_pull_le measurePreserving_fst _).trans hSbP
    have h4 : ((PF d L W g).prod (PF d L W g)) A4 ≤ ENNReal.ofReal ε := by
      rw [hA4]; exact (cltStep_pull_le hmpT _).trans hSbP
    calc ((PF d L W g).prod (PF d L W g)) (A1 ∪ A2 ∪ A3 ∪ A4)
        ≤ ((PF d L W g).prod (PF d L W g)) (A1 ∪ A2 ∪ A3) +
            ((PF d L W g).prod (PF d L W g)) A4 :=
          measure_union_le _ _
      _ ≤ ((PF d L W g).prod (PF d L W g)) (A1 ∪ A2) + ((PF d L W g).prod (PF d L W g)) A3 +
            ((PF d L W g).prod (PF d L W g)) A4 := add_le_add (measure_union_le _ _) le_rfl
      _ ≤ ((PF d L W g).prod (PF d L W g)) A1 + ((PF d L W g).prod (PF d L W g)) A2 +
            ((PF d L W g).prod (PF d L W g)) A3 + ((PF d L W g).prod (PF d L W g)) A4 :=
          add_le_add (add_le_add (measure_union_le _ _) le_rfl) le_rfl
      _ ≤ ENNReal.ofReal ε + ENNReal.ofReal ε + ENNReal.ofReal ε + ENNReal.ofReal ε :=
          add_le_add (add_le_add (add_le_add h1 h2) h3) h4
      _ = ENNReal.ofReal (4 * ε) := by
          rw [← ENNReal.ofReal_add hε hε, ← ENNReal.ofReal_add (by linarith) hε,
            ← ENNReal.ofReal_add (by linarith) hε]
          ring_nf
  have hgoodq : ∀ q : Ω d L W × Ω d L W, q ∉ A1 ∪ A2 ∪ A3 ∪ A4 →
      |q.1 c| ≤ (W : ℝ) ^ (-(1 / 2 : ℝ)) ∧ |q.2 c| ≤ (W : ℝ) ^ (-(1 / 2 : ℝ)) ∧
        cltGoodAt d L W E u θ D' q.1 ∧ cltGoodAt d L W E u θ D' (cltHyb d L W e j q.1 q.2) := by
    intro q hq
    rw [hA1, hA2, hA3, hA4, hSb] at hq
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_ofPred_eq, not_or, not_lt, not_not] at hq
    exact ⟨hq.1.1.1, hq.1.1.2, hq.1.2, hq.2⟩
  -- the geometry
  rcases hgeom (split d L W c.1).1 with hA | hB
  · -- Case A: the block of `c` is far from every label of `b_i`
    refine cltStep_norm_integral_le ((PF d L W g).prod (PF d L W g)) _ (A1 ∪ A2 ∪ A3 ∪ A4) hg0
      hM0 h4ε hBq (fun q => ?_) (fun q hq => ?_)
    · rw [norm_mul]
      calc _ ≤ (2 * X) * X ^ (2 * p) :=
            mul_le_mul (hdiff q) (cltStep_Gamma_le F g E u b hX1 hX i q.1) (norm_nonneg _)
              (by linarith)
        _ ≤ 4 * (X * X ^ (2 * p)) := by nlinarith
    · obtain ⟨hq1, hq2, -, hq4⟩ := hgoodq q hq
      have hs : |q.2 c - cltHyb d L W e j q.1 q.2 c| ≤ 2 * (W : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [hTk q]
        have a1 := abs_le.1 hq1
        have a2 := abs_le.1 hq2
        exact abs_le.2 ⟨by linarith, by linarith⟩
      have hpb := cltPathMulti_bound d L W k K F E u ρ R θ D' (b i) c (cltHyb d L W e j q.1 q.2)
        (q.2 c) hu0 hu1 hz hloc hθ hadj hA hθR hq4 hs
      have hcs := cltStep_coefSum_nonneg F (b i)
      have hY : ‖cltStep_Xo F g E u b i (cltHyb d L W e j q.1 q.2) -
          cltStep_Xo F g E u b i (cltHyb d L W e (j + 1) q.1 q.2)‖ ≤ 2 * (Bc * (W : ℝ) ^ (-D')) := by
        rw [cltStep_Xo_sub, hTk1 q, norm_sub_rev]
        refine hpb.trans ?_
        have ha : |q.2 c - cltHyb d L W e j q.1 q.2 c| ≤ 2 := by linarith
        have hb : |q.2 c - cltHyb d L W e j q.1 q.2 c| * (4 * cltCoefSumMulti F (b i)) ≤ 2 * Bc :=
          mul_le_mul ha (hBc (b i)) (by positivity) (by norm_num)
        calc |q.2 c - cltHyb d L W e j q.1 q.2 c| * 4 * cltCoefSumMulti F (b i) * (W : ℝ) ^ (-D')
            = (|q.2 c - cltHyb d L W e j q.1 q.2 c| * (4 * cltCoefSumMulti F (b i))) *
                (W : ℝ) ^ (-D') := by ring
          _ ≤ (2 * Bc) * (W : ℝ) ^ (-D') := mul_le_mul_of_nonneg_right hb hγ0
          _ = 2 * (Bc * (W : ℝ) ^ (-D')) := by ring
      rw [norm_mul]
      have hΓ := cltStep_Gamma_le F g E u b hX1 hX i q.1
      calc _ ≤ (2 * (Bc * (W : ℝ) ^ (-D'))) * X ^ (2 * p) :=
            mul_le_mul hY hΓ (norm_nonneg _) (by positivity)
        _ ≤ 4 * p * (X * X ^ (2 * p)) * (Bc * (W : ℝ) ^ (-D')) := by
            have h := mul_nonneg (mul_nonneg hG0 hQ0)
              (show (0 : ℝ) ≤ 4 * p * X - 2 by nlinarith)
            nlinarith
  · -- Case B: the block of `c` is far from every label of every `b_m`, `m ≠ i`
    obtain ⟨H0, hH0⟩ : ∃ H : Ω d L W × Ω d L W → ℂ, H = fun q =>
        (cltStep_Xo F g E u b i (cltHyb d L W e j q.1 q.2) -
          cltStep_Xo F g E u b i (cltHyb d L W e (j + 1) q.1 q.2)) *
          cltStep_Gamma F g E u b i (Function.update q.1 c 0) := ⟨_, rfl⟩
    have hanti : ∀ q, H0 (cltSwap d L W c q) = -H0 q := by
      intro q
      have h1 := cltHyb_cltSwap d L W e j hj q
      have h2 := cltHyb_succ_cltSwap d L W e j hj q
      rw [hc] at h1 h2
      rw [hH0]
      simp only [h1, h2, update_cltSwap_fst]
      ring
    have hint0 : ∫ q, H0 q ∂((PF d L W g).prod (PF d L W g)) = 0 :=
      integral_eq_zero_of_cltSwap_neg d L W g c H0 hanti
    have hmU : Measurable fun q : Ω d L W × Ω d L W => Function.update q.1 c (0 : ℝ) :=
      measurable_update'.comp (measurable_fst.prodMk measurable_const)
    have hmD : Measurable fun q : Ω d L W × Ω d L W =>
        cltStep_Xo F g E u b i (cltHyb d L W e j q.1 q.2) -
          cltStep_Xo F g E u b i (cltHyb d L W e (j + 1) q.1 q.2) :=
      ((cltStep_Xo_meas F g E u b i).comp hmpT.measurable).sub
        ((cltStep_Xo_meas F g E u b i).comp hmpT1.measurable)
    have hiF : Integrable (fun q : Ω d L W × Ω d L W =>
        (cltStep_Xo F g E u b i (cltHyb d L W e j q.1 q.2) -
          cltStep_Xo F g E u b i (cltHyb d L W e (j + 1) q.1 q.2)) * cltStep_Gamma F g E u b i q.1)
        ((PF d L W g).prod (PF d L W g)) := by
      refine Integrable.of_bound
        (hmD.mul ((cltStep_Gamma_meas F g E u b i).comp measurable_fst)).aestronglyMeasurable
        ((2 * X) * X ^ (2 * p)) (Filter.Eventually.of_forall fun q => ?_)
      rw [norm_mul]
      exact mul_le_mul (hdiff q) (cltStep_Gamma_le F g E u b hX1 hX i q.1) (norm_nonneg _)
        (by linarith)
    have hiF0 : Integrable H0 ((PF d L W g).prod (PF d L W g)) := by
      rw [hH0]
      refine Integrable.of_bound
        (hmD.mul ((cltStep_Gamma_meas F g E u b i).comp hmU)).aestronglyMeasurable
        ((2 * X) * X ^ (2 * p)) (Filter.Eventually.of_forall fun q => ?_)
      rw [norm_mul]
      exact mul_le_mul (hdiff q) (cltStep_Gamma_le F g E u b hX1 hX i _) (norm_nonneg _)
        (by linarith)
    have hsplit : ∫ q, (cltStep_Xo F g E u b i (cltHyb d L W e j q.1 q.2) -
          cltStep_Xo F g E u b i (cltHyb d L W e (j + 1) q.1 q.2)) * cltStep_Gamma F g E u b i q.1
        ∂((PF d L W g).prod (PF d L W g)) =
        ∫ q, ((cltStep_Xo F g E u b i (cltHyb d L W e j q.1 q.2) -
          cltStep_Xo F g E u b i (cltHyb d L W e (j + 1) q.1 q.2)) * cltStep_Gamma F g E u b i q.1 - H0 q)
        ∂((PF d L W g).prod (PF d L W g)) := by
      rw [integral_sub hiF hiF0, hint0, sub_zero]
    rw [hsplit]
    have hH0q : ∀ q, (cltStep_Xo F g E u b i (cltHyb d L W e j q.1 q.2) -
          cltStep_Xo F g E u b i (cltHyb d L W e (j + 1) q.1 q.2)) * cltStep_Gamma F g E u b i q.1 - H0 q =
        (cltStep_Xo F g E u b i (cltHyb d L W e j q.1 q.2) -
          cltStep_Xo F g E u b i (cltHyb d L W e (j + 1) q.1 q.2)) *
          (cltStep_Gamma F g E u b i q.1 - cltStep_Gamma F g E u b i (Function.update q.1 c 0)) := by
      intro q; rw [hH0]; ring
    refine cltStep_norm_integral_le ((PF d L W g).prod (PF d L W g)) _ (A1 ∪ A2 ∪ A3 ∪ A4) hg0
      hM0 h4ε hBq (fun q => ?_) (fun q hq => ?_)
    · rw [hH0q, norm_mul]
      have hΓ1 := cltStep_Gamma_le F g E u b hX1 hX i q.1
      have hΓ2 := cltStep_Gamma_le F g E u b hX1 hX i (Function.update q.1 c 0)
      have hΓ : ‖cltStep_Gamma F g E u b i q.1 - cltStep_Gamma F g E u b i (Function.update q.1 c 0)‖ ≤
          2 * X ^ (2 * p) := (norm_sub_le _ _).trans (by linarith)
      calc _ ≤ (2 * X) * (2 * X ^ (2 * p)) :=
            mul_le_mul (hdiff q) hΓ (norm_nonneg _) (by linarith)
        _ = 4 * (X * X ^ (2 * p)) := by ring
    · obtain ⟨hq1, -, hq3, -⟩ := hgoodq q hq
      have hs : |0 - q.1 c| ≤ 2 * (W : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [zero_sub, abs_neg]; linarith
      have hm : ∀ m ∈ Finset.univ.erase i,
          ‖cltStep_Xo F g E u b m q.1 - cltStep_Xo F g E u b m (Function.update q.1 c 0)‖ ≤
            Bc * (W : ℝ) ^ (-D') := by
        intro m hm
        have hmi : m ≠ i := Finset.ne_of_mem_erase hm
        have hpb := cltPathMulti_bound d L W k K F E u ρ R θ D' (b m) c q.1 0 hu0 hu1 hz hloc hθ
          hadj (hB m hmi) hθR hq3 hs
        have hcs := cltStep_coefSum_nonneg F (b m)
        rw [cltStep_Xo_sub, norm_sub_rev]
        refine hpb.trans ?_
        have ha : |0 - q.1 c| ≤ 1 := by rw [zero_sub, abs_neg]; linarith
        have hb : |0 - q.1 c| * (4 * cltCoefSumMulti F (b m)) ≤ 1 * Bc :=
          mul_le_mul ha (hBc (b m)) (by positivity) (by norm_num)
        calc |0 - q.1 c| * 4 * cltCoefSumMulti F (b m) * (W : ℝ) ^ (-D')
            = (|0 - q.1 c| * (4 * cltCoefSumMulti F (b m))) * (W : ℝ) ^ (-D') := by ring
          _ ≤ (1 * Bc) * (W : ℝ) ^ (-D') := mul_le_mul_of_nonneg_right hb hγ0
          _ = Bc * (W : ℝ) ^ (-D') := by ring
      have hprod := cltStep_prod_sub_le (Finset.univ.erase i) (fun m => cltStep_Xo F g E u b m q.1)
        (fun m => cltStep_Xo F g E u b m (Function.update q.1 c 0)) hX1 hG0
        (fun m _ => hX m q.1) (fun m _ => hX m _) hm
      have hcard : (Finset.univ.erase i).card ≤ 2 * p := Finset.card_erase_le.trans (by simp)
      have hcard' : (((Finset.univ.erase i).card : ℕ) : ℝ) ≤ 2 * p := by exact_mod_cast hcard
      have hpowc : X ^ (Finset.univ.erase i).card ≤ X ^ (2 * p) := pow_le_pow_right₀ hX1 hcard
      have hΓ : ‖cltStep_Gamma F g E u b i q.1 - cltStep_Gamma F g E u b i (Function.update q.1 c 0)‖ ≤
          2 * p * X ^ (2 * p) * (Bc * (W : ℝ) ^ (-D')) := by
        refine hprod.trans ?_
        have := mul_le_mul hcard' hpowc (pow_nonneg hX0 _) (by positivity)
        exact mul_le_mul_of_nonneg_right this hG0
      rw [hH0q, norm_mul]
      calc _ ≤ (2 * X) * (2 * p * X ^ (2 * p) * (Bc * (W : ℝ) ^ (-D'))) :=
            mul_le_mul (hdiff q) hΓ (norm_nonneg _) (by linarith)
        _ = 4 * p * (X * X ^ (2 * p)) * (Bc * (W : ℝ) ^ (-D')) := by ring


/-! ## 4. The assembly on the finite model -/

/-- The finite-model core of the assembly: if every step of the telescoping has `‖·‖ ≤ η`, then
`‖∫ ∏_m X_m dPF‖ ≤ card (CoordF) · η` (the centring of `X_i`, the product `∏ X_m = X_i Γ_i`,
the telescope `cltTelescope`). -/
private theorem cltStep_assembly {d L W K k : ℕ} [NeZero L] [NeZero W] (g : ℝ) {p : ℕ}
    (F : LocalForm d L W k K) (E u : ℝ) {BY : ℝ} (hY : ∀ ω b', ‖cltEvalAt F E u ω b'‖ ≤ BY)
    (b : Fin (2 * p) → Fin k → Zd d L) (i : Fin (2 * p))
    (e : CoordF d L W ≃ Fin (Fintype.card (CoordF d L W))) {η : ℝ}
    (hstep : ∀ j : ℕ, j < Fintype.card (CoordF d L W) →
      ‖∫ q, (cltStep_Xo F g E u b i (cltHyb d L W e j q.1 q.2) -
          cltStep_Xo F g E u b i (cltHyb d L W e (j + 1) q.1 q.2)) * cltStep_Gamma F g E u b i q.1
        ∂((PF d L W g).prod (PF d L W g))‖ ≤ η) :
    ‖∫ ω, ∏ m : Fin (2 * p), cltStep_Xo F g E u b m ω ∂(PF d L W g)‖ ≤
      Fintype.card (CoordF d L W) * η := by
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = max (2 * BY) 1 := ⟨_, rfl⟩
  have hX1 : 1 ≤ X := by rw [hXdef]; exact le_max_right _ _
  have hX : ∀ m ω, ‖cltStep_Xo F g E u b m ω‖ ≤ X := fun m ω => by
    rw [hXdef]; exact (cltStep_Xo_le F g E u b hY m ω).trans (le_max_left _ _)
  have hG : ∀ ω, ‖cltStep_Gamma F g E u b i ω‖ ≤ X ^ (2 * p) := cltStep_Gamma_le F g E u b hX1 hX i
  have hXm : Measurable (cltStep_Xo F g E u b i) := cltStep_Xo_meas F g E u b i
  have hGm : Measurable (cltStep_Gamma F g E u b i) := cltStep_Gamma_meas F g E u b i
  have hX0 : 0 ≤ X := by linarith
  -- integrability of the difference integrands
  have hdiffInt : ∀ f f' : Ω d L W × Ω d L W → Ω d L W, Measurable f → Measurable f' →
      Integrable (fun q : Ω d L W × Ω d L W =>
        (cltStep_Xo F g E u b i (f q) - cltStep_Xo F g E u b i (f' q)) * cltStep_Gamma F g E u b i q.1)
        ((PF d L W g).prod (PF d L W g)) := by
    intro f f' hf hf'
    refine Integrable.of_bound (C := (X + X) * X ^ (2 * p)) ?_ ?_
    · exact (((hXm.comp hf).sub (hXm.comp hf')).mul
        (hGm.comp measurable_fst)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun q => ?_
      rw [norm_mul]
      exact mul_le_mul ((norm_sub_le _ _).trans (add_le_add (hX _ _) (hX _ _))) (hG _)
        (norm_nonneg _) (by linarith)
  have hTm : ∀ j : ℕ, Measurable fun q : Ω d L W × Ω d L W => cltHyb d L W e j q.1 q.2 :=
    fun j => (measurePreserving_cltSplit d L W g (cltHybSet d L W e j)).measurable
  have hi1 := hdiffInt Prod.fst Prod.snd measurable_fst measurable_snd
  have hi2 : Integrable (fun q : Ω d L W × Ω d L W =>
      cltStep_Gamma F g E u b i q.1 * cltStep_Xo F g E u b i q.2) ((PF d L W g).prod (PF d L W g)) := by
    refine Integrable.of_bound (C := X ^ (2 * p) * X) ?_ ?_
    · exact ((hGm.comp measurable_fst).mul (hXm.comp measurable_snd)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun q => ?_
      rw [norm_mul]
      exact mul_le_mul (hG _) (hX _ _) (norm_nonneg _) (by positivity)
  -- factor `∏ X_m = X_i Γ_i`
  have hfac : ∀ ω, ∏ m : Fin (2 * p), cltStep_Xo F g E u b m ω =
      cltStep_Xo F g E u b i ω * cltStep_Gamma F g E u b i ω := fun ω =>
    (Finset.mul_prod_erase Finset.univ (fun m => cltStep_Xo F g E u b m ω) (Finset.mem_univ i)).symm
  -- transfer to the product space
  have h1 : ∫ ω, ∏ m : Fin (2 * p), cltStep_Xo F g E u b m ω ∂(PF d L W g) =
      ∫ q, cltStep_Xo F g E u b i q.1 * cltStep_Gamma F g E u b i q.1
        ∂((PF d L W g).prod (PF d L W g)) := by
    have := integral_fun_fst (μ := PF d L W g) (ν := PF d L W g)
      (fun ω => cltStep_Xo F g E u b i ω * cltStep_Gamma F g E u b i ω)
    simp only [probReal_univ, one_smul] at this
    rw [this]
    exact integral_congr_ae (Filter.Eventually.of_forall hfac)
  -- the centred term vanishes
  have h0 : ∫ q, cltStep_Gamma F g E u b i q.1 * cltStep_Xo F g E u b i q.2
      ∂((PF d L W g).prod (PF d L W g)) = 0 := by
    have := integral_prod_mul (μ := PF d L W g) (ν := PF d L W g) (cltStep_Gamma F g E u b i)
      (cltStep_Xo F g E u b i)
    rw [this, cltStep_Xo_integral F g E u hY b i, mul_zero]
  have h2 : ∫ q, cltStep_Xo F g E u b i q.1 * cltStep_Gamma F g E u b i q.1
        ∂((PF d L W g).prod (PF d L W g)) =
      ∫ q, (cltStep_Xo F g E u b i q.1 - cltStep_Xo F g E u b i q.2) * cltStep_Gamma F g E u b i q.1
        ∂((PF d L W g).prod (PF d L W g)) := by
    have h3 : ∫ q, cltStep_Xo F g E u b i q.1 * cltStep_Gamma F g E u b i q.1
          ∂((PF d L W g).prod (PF d L W g)) =
        ∫ q, (cltStep_Xo F g E u b i q.1 - cltStep_Xo F g E u b i q.2) * cltStep_Gamma F g E u b i q.1
          ∂((PF d L W g).prod (PF d L W g)) +
        ∫ q, cltStep_Gamma F g E u b i q.1 * cltStep_Xo F g E u b i q.2
          ∂((PF d L W g).prod (PF d L W g)) := by
      rw [← integral_add hi1 hi2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
      simp only
      ring
    rw [h3, h0, add_zero]
  -- telescoping
  have h4 : ∫ q, (cltStep_Xo F g E u b i q.1 - cltStep_Xo F g E u b i q.2) * cltStep_Gamma F g E u b i q.1
        ∂((PF d L W g).prod (PF d L W g)) =
      ∑ j ∈ Finset.range (Fintype.card (CoordF d L W)),
        ∫ q, (cltStep_Xo F g E u b i (cltHyb d L W e j q.1 q.2) -
          cltStep_Xo F g E u b i (cltHyb d L W e (j + 1) q.1 q.2)) * cltStep_Gamma F g E u b i q.1
        ∂((PF d L W g).prod (PF d L W g)) := by
    rw [← integral_finsetSum _ fun j _ => hdiffInt _ _ (hTm j) (hTm (j + 1))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only
    rw [← Finset.sum_mul, ← cltTelescope d L W e (cltStep_Xo F g E u b i) q.1 q.2]
  rw [h1, h2, h4]
  calc ‖∑ j ∈ Finset.range (Fintype.card (CoordF d L W)),
        ∫ q, (cltStep_Xo F g E u b i (cltHyb d L W e j q.1 q.2) -
          cltStep_Xo F g E u b i (cltHyb d L W e (j + 1) q.1 q.2)) * cltStep_Gamma F g E u b i q.1
        ∂((PF d L W g).prod (PF d L W g))‖
      ≤ ∑ j ∈ Finset.range (Fintype.card (CoordF d L W)), η :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj =>
          hstep j (Finset.mem_range.mp hj))
    _ = Fintype.card (CoordF d L W) * η := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]


/-! ## 5. The step at the sequence level (item 2) -/

section SeqStep

private theorem cltStep_zdistInf_neg {d L : ℕ} [NeZero L] (x : Zd d L) : zdistInf d L (-x) = zdistInf d L x := by
  simp only [zdistInf, Pi.neg_apply, zdist_neg]

private theorem cltStep_zdistInf_add_le {d L : ℕ} [NeZero L] (x y : Zd d L) :
    zdistInf d L (x + y) ≤ zdistInf d L x + zdistInf d L y := by
  refine Finset.sup_le fun i _ => ?_
  calc zdist L ((x + y) i) = zdist L (x i + y i) := rfl
    _ ≤ zdist L (x i) + zdist L (y i) := zdist_add_le L _ _
    _ ≤ _ := add_le_add (Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i))
          (Finset.le_sup (f := fun j => zdist L (y j)) (Finset.mem_univ i))

/-- `c_κ > 0` for `0 < κ`, `|E| ≤ 2 - κ` (a re-proof of the private `cltres_ck_pos` of
`RBM3D/Evolution/CltResolvent.lean`). -/
private theorem cltStep_ck_pos {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) : 0 < cltCk κ := by
  have h1 : κ ≤ 2 := by have := abs_nonneg E; linarith
  unfold cltCk
  have : 0 < κ * (4 - κ) := mul_pos hκ (by linarith)
  positivity

/-- Absorption of a constant `A ≤ N` into one power of `N`. -/
private theorem cltStep_absorb {N A x y : ℝ} (hN : 1 ≤ N) (hA : A ≤ N) (hxy : x + 1 ≤ y) :
    A * N ^ x ≤ N ^ y := by
  have hN0 : 0 < N := by linarith
  calc A * N ^ x ≤ N * N ^ x := mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg hN0.le _)
    _ = N ^ (x + 1) := by rw [Real.rpow_add_one hN0.ne', mul_comm]
    _ ≤ N ^ y := Real.rpow_le_rpow_of_exponent_le hN hxy

/-- **The geometry of the two-label cluster** (`ρ = w + 1`, `R/2 = 4w`).  If every label pair is
in the window `|b_m1 - b_m2|_∞ ≤ w` and the first labels satisfy `10 w ≤ |b_i1 - b_m1|_∞`
(`m ≠ i`), then every block `a` is at distance `≥ 4w` from both labels of `b_i`, or from both
labels of every `b_m`, `m ≠ i` (the dichotomy `cltFarGeomHalf` on the first labels, then the
window). -/
private theorem cltStep_geom {d L : ℕ} [NeZero L] {p : ℕ} (b : Fin (2 * p) → Fin 2 → Zd d L)
    (i : Fin (2 * p)) {w : ℝ}
    (hwin : ∀ m, (zdistInf d L (b m 0 - b m 1) : ℝ) ≤ w)
    (hiso : ∀ m, m ≠ i → 10 * w ≤ (zdistInf d L (b i 0 - b m 0) : ℝ)) (a : Zd d L) :
    (∀ m', 4 * w ≤ (zdistInf d L (a - b i m') : ℝ)) ∨
      (∀ m, m ≠ i → ∀ m', 4 * w ≤ (zdistInf d L (a - b m m') : ℝ)) := by
  have key : ∀ m, 5 * w ≤ (zdistInf d L (a - b m 0) : ℝ) → ∀ m', 4 * w ≤ (zdistInf d L (a - b m m') : ℝ) := by
    intro m hm m'
    fin_cases m'
    · simp only [Fin.zero_eta]; linarith
    · simp only [Fin.mk_one]
      have h := cltStep_zdistInf_add_le (a - b m 1) (b m 1 - b m 0)
      rw [show a - b m 1 + (b m 1 - b m 0) = a - b m 0 by abel] at h
      have hs : zdistInf d L (b m 1 - b m 0) = zdistInf d L (b m 0 - b m 1) := by
        rw [← neg_sub, cltStep_zdistInf_neg]
      rw [hs] at h
      have h' : (zdistInf d L (a - b m 0) : ℝ) ≤
          (zdistInf d L (a - b m 1) : ℝ) + (zdistInf d L (b m 0 - b m 1) : ℝ) := by exact_mod_cast h
      linarith [hwin m]
  rcases cltFarGeomHalf d L (2 * p) (fun m => b m 0) i (10 * w) a hiso with hA | hB
  · left
    exact key i (by linarith)
  · right
    intro m hm
    exact key m (by have := hB m hm; linarith)

variable {d : ℕ} (sz : Sizes d)

/-- The log-scale window `w_n = (log W_n)^3 ℓ_s` of `(eq:bound_isolated)` (`3_5:2245`). -/
def cltStep_win (n : ℕ) (s : ℝ) : ℝ :=
  Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s

/-- **Item 2: one real coordinate of the telescoping** (`CltStep` of RBM2D, `CltStep.lean:579-600`,
for the two-label forms `STcltB`).  Under `HClt` at `τ = s`, a `2`-label local form `F` that is
`(w_n + 1)`-local (`w_n = (log W_n)^3 ℓ_s`) with coefficients `≤ N^{C'}`, for every `p ≥ 1`, `D > 0`,
eventually in `n`, for every `b : Fin (2p) → (Fin 2 → Zd)` with all labels in the window
`|b_m1 - b_m2|_∞ ≤ w_n` and an isolated index `i` (`10 w_n ≤ |b_i1 - b_m1|_∞`, `m ≠ i`), every
enumeration `e` of the real coordinates and every step `j`:
`‖∫ (X_i(T_j) - X_i(T_{j+1})) Γ_i(ω) d(P⊗P)‖ ≤ N^{-D-3}`.  The far threshold of the good event is
`θ_n = max (3 w_n - 2) w_n` (`= 3 w_n - 2` for `w_n ≥ 1`), the locality radius `ρ = w_n + 1`, the
separation `R = 8 w_n` (`cltStep_geom`). -/
theorem cltStep (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) (s t : ℕ → ℝ) (Cd : ℝ)
    (hH : HClt sz κ ε 𝔠 𝔡 z s s t Cd) (K : ℕ) (C' : ℝ) (hC' : 0 ≤ C')
    (F : ∀ n, LocalForm d (sz.L n) (sz.W n) 2 K)
    (hcoef : ∀ᶠ n in atTop, ∀ b j q, ‖(F n).coef b j q‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C')
    (hloc : ∀ n, (F n).Local (cltStep_win sz n (s n) + 1))
    (p : ℕ) (hp : 1 ≤ p) (D : ℝ) (hD : 0 < D) :
    ∀ᶠ n in atTop,
      ∀ (b : Fin (2 * p) → Fin 2 → Zd d (sz.L n)) (i : Fin (2 * p)),
        (∀ m, ((zdistInf d (sz.L n) (b m 0 - b m 1) : ℕ) : ℝ) ≤ cltStep_win sz n (s n)) →
        (∀ m, m ≠ i →
          10 * cltStep_win sz n (s n) ≤ ((zdistInf d (sz.L n) (b i 0 - b m 0) : ℕ) : ℝ)) →
        ∀ (e : CoordF d (sz.L n) (sz.W n) ≃ Fin (Fintype.card (CoordF d (sz.L n) (sz.W n))))
          (j : ℕ), j < Fintype.card (CoordF d (sz.L n) (sz.W n)) →
          ‖∫ q, (cltStep_Xo (F n) (sz.lam n) (STflowE z n) (s n) b i
                  (cltHyb d (sz.L n) (sz.W n) e j q.1 q.2) -
                cltStep_Xo (F n) (sz.lam n) (STflowE z n) (s n) b i
                  (cltHyb d (sz.L n) (sz.W n) e (j + 1) q.1 q.2)) *
              cltStep_Gamma (F n) (sz.lam n) (STflowE z n) (s n) b i q.1
            ∂((PF d (sz.L n) (sz.W n) (sz.lam n)).prod (PF d (sz.L n) (sz.W n) (sz.lam n)))‖ ≤
            ((sz.size n : ℕ) : ℝ) ^ (-D - 3) := by
  have hH' := hH
  obtain ⟨hd, hκ, hε, hflow, hs0, -, hst, htl, -⟩ := hH
  obtain ⟨⟨h𝔠, -, hN, hBW, -⟩, hE, ht1, hRC⟩ :=
    RBM.Green.v3_premises_of_stFlow sz hκ hε hflow htl
  have hκ' : 0 < κ / 2 := by linarith
  have hδ : 0 < ε / 2 := by linarith
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = C' + 3 * K + 2 := ⟨_, rfl⟩
  obtain ⟨D'', hD''⟩ : ∃ x : ℝ, x = a * (2 * p + 2) + D + 4 := ⟨_, rfl⟩
  obtain ⟨D', hD'⟩ : ∃ x : ℝ, x = D'' / 𝔠 := ⟨_, rfl⟩
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have ha0 : 0 < a := by rw [ha]; linarith
  have hD''0 : 0 < D'' := by
    have : 0 ≤ a * (2 * p + 2) := mul_nonneg ha0.le (by positivity)
    rw [hD'']; linarith
  have hD'0 : 0 < D' := by rw [hD']; exact div_pos hD''0 h𝔠
  have hck : 0 < cltCk (κ / 2) := cltStep_ck_pos (E := STflowE z 0) hκ' (hE 0).le
  obtain ⟨C1, hC1⟩ : ∃ C : ℝ, C = 2 * (K + 1) * (2 / cltCk (κ / 2)) ^ K := ⟨_, rfl⟩
  obtain ⟨C2, hC2⟩ : ∃ C : ℝ, C = 4 * (K + 1) * 2 ^ K * K * 4 ^ K := ⟨_, rfl⟩
  have hWt : Tendsto (fun n => (sz.W n : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop hBW ((tendsto_rpow_atTop h𝔠).comp hN)
  -- the good event at `θ_n = max (3 w_n - 2) w_n`
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℕ → ℝ, θ = fun n =>
      max (3 * cltStep_win sz n (s n) - 2) (cltStep_win sz n (s n)) := ⟨_, rfl⟩
  have hgood := cltGood_whp sz κ ε 𝔠 𝔡 z s s t Cd hH' 1 θ one_pos
    (fun n => by rw [hθdef]; simp only [one_mul]; exact le_max_right _ _) D' hD'0 D'' hD''0
  have htail := cltCoord_tail sz (by omega) 𝔠 h𝔠 hN hBW D'' hD''0
  filter_upwards [hN.eventually_ge_atTop (max (max C1 C2) (max (4 * p + 16) 1)), hBW, hRC, hcoef,
    hWt.eventually_ge_atTop 3,
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hWt).eventually_ge_atTop 16,
    htail, hgood] with n hNn hBWn hRn hcoefn hW3 hW12 hE1 hE2
  intro b i hwin hiso e j hj
  have hW12' : 16 ≤ (sz.W n : ℝ) ^ (1 / 2 : ℝ) := hW12
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN1 : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hNn
  have hN0 : 0 < N := by linarith
  have hNC1 : C1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hNn
  have hNC2 : C2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hNn
  have hNC3 : 4 * p + 16 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hNn
  have hL3 := sz.three_le_L n
  have hu0 : 0 ≤ s n := hs0 n
  have hu1 : s n < 1 := (hst n).trans_lt (ht1 n)
  have hR : N ^ (-1 + ε / 2) ≤ 1 - s n := by have := hst n; linarith [hRn]
  have hE' : |STflowE z n| ≤ 2 - κ / 2 := (hE n).le
  have hηlow := cltEta_lower d (sz.L n) (sz.W n) (κ / 2) (ε / 2) (STflowE z n) (s n) hκ' hδ hE' hR
  have hz : (zt (STflowE z n) (s n)).im ≠ 0 := by
    have h0 : 0 < cltCk (κ / 2) / N := div_pos hck hN0
    exact (lt_of_lt_of_le h0 hηlow).ne'
  have hℓ : 1 ≤ ellT (sz.L n) (sz.lam n) (s n) := one_le_ellT (by exact_mod_cast (by omega : 1 ≤ sz.L n))
  have hlogW : 1 ≤ Real.log ((sz.W n : ℕ) : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact (Real.exp_one_lt_three.le).trans hW3
  have hw1 : 1 ≤ cltStep_win sz n (s n) := by
    unfold cltStep_win
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hlogW) hℓ
  set w : ℝ := cltStep_win sz n (s n) with hwdef
  have hθ : 16 * (sz.W n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
    have hpos : 0 < (sz.W n : ℝ) ^ (1 / 2 : ℝ) := by linarith
    rw [Real.rpow_neg (Nat.cast_nonneg _), ← div_eq_mul_inv, div_le_one hpos]
    exact hW12'
  have hθR : θ n ≤ (8 * w) / 2 - (w + 1) - 1 := by
    rw [hθdef]
    simp only
    refine max_le (by linarith) (by linarith)
  -- `‖X_m‖ ≤ N^a`
  have hNsize : ((sz.size n : ℕ) : ℝ) = ((((sz.W n * sz.L n) ^ d : ℕ)) : ℝ) := rfl
  have hYn : ∀ (ω : Ω d (sz.L n) (sz.W n)) (b' : Fin 2 → Zd d (sz.L n)),
      ‖cltEvalAt (F n) (STflowE z n) (s n) ω b'‖ ≤ (K + 1) * N ^ C' * (2 * N ^ 3 / cltCk (κ / 2)) ^ K :=
    fun ω b' => cltEval_detMulti_le d (sz.L n) (sz.W n) 2 (κ / 2) (ε / 2) (STflowE z n) (s n) K (F n) C'
      (Hflow d (sz.L n) (sz.W n) (s n) ω) b' hκ' hδ hE' hR hcoefn (Hflow_isHermitian _ _ _ _ _)
  have hBY : 2 * ((K + 1) * N ^ C' * (2 * N ^ 3 / cltCk (κ / 2)) ^ K) ≤ N ^ a := by
    have e1 : (2 * N ^ 3 / cltCk (κ / 2)) ^ K = (2 / cltCk (κ / 2)) ^ K * N ^ ((3 * K : ℕ) : ℝ) := by
      rw [Real.rpow_natCast, pow_mul, ← mul_pow]
      congr 1
      ring
    have e2 : 2 * ((K + 1) * N ^ C' * (2 * N ^ 3 / cltCk (κ / 2)) ^ K) =
        C1 * N ^ (C' + ((3 * K : ℕ) : ℝ)) := by
      rw [e1, Real.rpow_add hN0, hC1]
      ring
    rw [e2]
    exact cltStep_absorb hN1 hNC1 (by rw [ha]; push_cast; linarith)
  have hX : ∀ m ω, ‖cltStep_Xo (F n) (sz.lam n) (STflowE z n) (s n) b m ω‖ ≤ N ^ a := fun m ω =>
    (cltStep_Xo_le (F n) (sz.lam n) (STflowE z n) (s n) b hYn m ω).trans hBY
  have hX1 : 1 ≤ N ^ a := Real.one_le_rpow hN1 ha0.le
  -- `4 · cltCoefSumMulti ≤ N^a`
  have hcard : (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ) = N := by
    rw [hNdef, Sizes.card_Idx]
  have hBc : ∀ b', 4 * cltCoefSumMulti (F n) b' ≤ N ^ a := by
    intro b'
    have h1 := cltStep_coefSum_le (F n) (Real.rpow_nonneg hN0.le C') hcoefn b'
    rw [hcard] at h1
    have e1 : 4 * ((K + 1) * ((2 * N ^ 2) ^ K * (N ^ C' * K * 4 ^ K))) =
        C2 * N ^ (C' + ((2 * K : ℕ) : ℝ)) := by
      rw [Real.rpow_add hN0, Real.rpow_natCast, hC2, mul_pow, pow_mul]
      ring
    calc 4 * cltCoefSumMulti (F n) b' ≤ 4 * ((K + 1) * ((2 * N ^ 2) ^ K * (N ^ C' * K * 4 ^ K))) := by
          linarith
      _ = C2 * N ^ (C' + ((2 * K : ℕ) : ℝ)) := e1
      _ ≤ N ^ a := cltStep_absorb hN1 hNC2 (by rw [ha]; push_cast; linarith)
  -- the geometry
  have hiso' : ∀ m, m ≠ i → 10 * w ≤ ((zdistInf d (sz.L n) (b i 0 - b m 0) : ℕ) : ℝ) := hiso
  have hgeom := cltStep_geom b i hwin hiso'
  -- the step at size `n`
  have hcore := cltStep_core (sz.lam n) (F n) (STflowE z n) (s n) (w + 1) (8 * w) (θ n) D' hp b i e j hj
    hu0 hu1 hz (hloc n) hθ hθR (fun a => by
      have := hgeom a
      simpa only [show (8 * w) / 2 = 4 * w by ring] using this)
    (X := N ^ a) (Bc := N ^ a) (ε := N ^ (-D'')) hX1 hX (Real.rpow_nonneg hN0.le a) hBc
    (Real.rpow_nonneg hN0.le _) hE1 hE2
  refine hcore.trans ?_
  -- the exponent count
  have hγρ : (sz.W n : ℝ) ^ (-D') ≤ N ^ (-D'') := by
    have hNc : 0 < N ^ 𝔠 := Real.rpow_pos_of_pos hN0 𝔠
    calc (sz.W n : ℝ) ^ (-D') ≤ (N ^ 𝔠) ^ (-D') :=
          Real.rpow_le_rpow_of_nonpos hNc hBWn (by linarith)
      _ = N ^ (-D'') := by
          rw [← Real.rpow_mul hN0.le]
          congr 1
          rw [hD']
          field_simp
  have hΛ : N ^ a * (N ^ a) ^ (2 * p) * N ^ a * N ^ (-D'') = N ^ (-D - 4) := by
    have e1 : N ^ a * (N ^ a) ^ (2 * p) * N ^ a = (N ^ a) ^ (2 * p + 2) := by ring
    rw [e1, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
    congr 1
    rw [hD'']
    push_cast
    ring
  have hZ0 : 0 ≤ N ^ a := Real.rpow_nonneg hN0.le a
  have hQ0 : 0 ≤ (N ^ a) ^ (2 * p) := pow_nonneg hZ0 _
  have hρ0 : 0 ≤ N ^ (-D'') := Real.rpow_nonneg hN0.le _
  have hZQ : N ^ a * (N ^ a) ^ (2 * p) ≤ N ^ a * (N ^ a) ^ (2 * p) * N ^ a :=
    le_mul_of_one_le_right (mul_nonneg hZ0 hQ0) hX1
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hT0 : 0 ≤ 4 * (p : ℝ) * (N ^ a * (N ^ a) ^ (2 * p) * N ^ a) := by
    have := mul_nonneg (mul_nonneg hZ0 hQ0) hZ0
    positivity
  calc 4 * (p : ℝ) * (N ^ a * (N ^ a) ^ (2 * p)) * (N ^ a * (sz.W n : ℝ) ^ (-D')) +
        4 * (N ^ a * (N ^ a) ^ (2 * p)) * (4 * N ^ (-D''))
      = 4 * (p : ℝ) * (N ^ a * (N ^ a) ^ (2 * p) * N ^ a) * (sz.W n : ℝ) ^ (-D') +
          16 * (N ^ a * (N ^ a) ^ (2 * p)) * N ^ (-D'') := by ring
    _ ≤ 4 * (p : ℝ) * (N ^ a * (N ^ a) ^ (2 * p) * N ^ a) * N ^ (-D'') +
          16 * (N ^ a * (N ^ a) ^ (2 * p) * N ^ a) * N ^ (-D'') :=
        add_le_add (mul_le_mul_of_nonneg_left hγρ hT0)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hZQ (by norm_num)) hρ0)
    _ = (4 * p + 16) * N ^ (-D - 4) := by rw [← hΛ]; ring
    _ ≤ N ^ (-D - 3) := cltStep_absorb hN1 hNC3 (by linarith)

end SeqStep

/-! ## 6. The local form of `STcltB` (item 1) -/

section Forms

variable {d L W k : ℕ} [NeZero L] [NeZero W]

/-- A degree-2 local form (`K = 2`) whose only non-zero coefficients are those of the monomials
`G_{q₀} G_{q₁}`, with coefficient `c2 b q₀ q₁`. -/
def cltStep_pairForm (c2 : (Fin k → Zd d L) → (Idx d L W × Idx d L W × Bool) →
    (Idx d L W × Idx d L W × Bool) → ℂ) : LocalForm d L W k 2 where
  coef b j q := if h : (j : ℕ) = 2 then c2 b (q ⟨0, by omega⟩) (q ⟨1, by omega⟩) else 0

/-- The evaluation of `cltStep_pairForm`: the double sum over the two monomial slots. -/
theorem cltStep_pairForm_eval (c2 : (Fin k → Zd d L) → (Idx d L W × Idx d L W × Bool) →
    (Idx d L W × Idx d L W × Bool) → ℂ) (E s : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (b : Fin k → Zd d L) :
    (cltStep_pairForm (W := W) c2).eval E s M b =
      ∑ q0 : Idx d L W × Idx d L W × Bool, ∑ q1 : Idx d L W × Idx d L W × Bool,
        c2 b q0 q1 * (gEntry d L W E s M q0.2.2 q0.1 q0.2.1 *
          gEntry d L W E s M q1.2.2 q1.1 q1.2.1) := by
  unfold LocalForm.eval
  rw [Finset.sum_eq_single (⟨2, by norm_num⟩ : Fin (2 + 1))]
  · rw [← Fintype.sum_prod_type']
    refine Fintype.sum_equiv (piFinTwoEquiv (fun _ : Fin 2 => Idx d L W × Idx d L W × Bool)) _ _ ?_
    intro q
    simp only [cltStep_pairForm, piFinTwoEquiv_apply, ↓reduceDIte, Fin.prod_univ_two]
    rfl
  · intro j _ hj
    have : (j : ℕ) ≠ 2 := fun h => hj (Fin.ext h)
    simp [cltStep_pairForm, this]
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem cltStep_gres_blockMat (H : Matrix (Idx d L W) (Idx d L W) ℂ)
    (z : ℂ) (σ : Bool) (x y : Vtx d L W) :
    Gres (blockMat d L W H) z σ x y =
      Gres H z σ ((splitEquiv d L W).symm x) ((splitEquiv d L W).symm y) := by
  unfold Gres blockMat
  generalize (if σ = true then z else (starRingEnd ℂ) z) = z'
  have e1 : H.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm -
        z' • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) =
      (H - z' • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)).submatrix
        (splitEquiv d L W).symm (splitEquiv d L W).symm := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply]
  rw [e1, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.inv_submatrix_equiv]
  rfl

/-- The two-loop in entries: `𝓛^{(2)}_{σ,(b₁,b₂)} = W^{-2d} Σ_{y∈[b₂], x∈[b₁]} G(σ₁)_{yx} G(σ₂)_{xy}`
(`Eblk` carries `W^{-d}`), on the fine lattice. -/
private theorem cltStep_loopFine_two (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ)
    (σ : Fin 2 → Bool) (b : Fin 2 → Zd d L) :
    loopFine d L W H z σ b =
      (((W : ℂ) ^ d)⁻¹) ^ 2 * ∑ y : Idx d L W, ∑ x : Idx d L W,
        (if (split d L W y).1 = b 1 ∧ (split d L W x).1 = b 0 then
          Gres H z (σ 0) y x * Gres H z (σ 1) x y else 0) := by
  unfold loopFine loopM
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    Fin.succ_zero_eq_one]
  have hE : ∀ c : Zd d L, Eblk d L W c = Matrix.diagonal fun x : Vtx d L W =>
      if x.1 = c then (((W : ℂ)) ^ d)⁻¹ else 0 := fun c => rfl
  rw [hE (b 0), hE (b 1)]
  set A := Gres (blockMat d L W H) z (σ 0) with hA
  set B := Gres (blockMat d L W H) z (σ 1) with hB
  have h1 : A * Matrix.diagonal (fun x : Vtx d L W => if x.1 = b 0 then (((W : ℂ)) ^ d)⁻¹ else 0) =
      Matrix.of fun i j => A i j * (if j.1 = b 0 then (((W : ℂ)) ^ d)⁻¹ else 0) := by
    ext i j; simp [Matrix.mul_diagonal]
  have h2 : B * Matrix.diagonal (fun x : Vtx d L W => if x.1 = b 1 then (((W : ℂ)) ^ d)⁻¹ else 0) =
      Matrix.of fun i j => B i j * (if j.1 = b 1 then (((W : ℂ)) ^ d)⁻¹ else 0) := by
    ext i j; simp [Matrix.mul_diagonal]
  rw [h1, h2]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.mul_sum]
  have hsum : ∀ F : Vtx d L W → Vtx d L W → ℂ, ∑ v, ∑ w, F v w =
      ∑ y : Idx d L W, ∑ x : Idx d L W, F (splitEquiv d L W y) (splitEquiv d L W x) := by
    intro F
    calc ∑ v, ∑ w, F v w = ∑ y, ∑ w, F (splitEquiv d L W y) w :=
          (Equiv.sum_comp (splitEquiv d L W) (fun v => ∑ w, F v w)).symm
      _ = _ := Finset.sum_congr rfl fun y _ =>
          (Equiv.sum_comp (splitEquiv d L W) (fun w => F (splitEquiv d L W y) w)).symm
  rw [hsum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [hA, hB, cltStep_gres_blockMat, Equiv.symm_apply_apply]
  have e1 : (splitEquiv d L W y).1 = (split d L W y).1 := rfl
  have e2 : (splitEquiv d L W x).1 = (split d L W x).1 := rfl
  rw [e1, e2]
  by_cases h1 : (split d L W y).1 = b 1
  · by_cases h2 : (split d L W x).1 = b 0
    · simp only [h1, h2, and_self, ↓reduceIte]
      ring
    · simp [h1, h2]
  · simp [h1]

end Forms

section LoopForm

variable {d : ℕ} (sz : Sizes d)

/-- The scale `(ilambda² W^d)^{6/5}` of `𝗕_b` (`3_5:2217`). -/
def cltStep_scale (n : ℕ) : ℝ := (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ)

/-- The coefficient of the monomial pair `G(σ₁)_{yx} G(σ₂)_{xy}` of the two-label loop
`𝓛^{(2)}_{σ,b}`, `x ∈ [b₁]`, `y ∈ [b₂]`, supported on the window `|b₁ - b₂|_∞ ≤ w`. -/
def cltStep_c2 (n : ℕ) (σ : Fin 2 → Bool) (w : ℝ) (c : ℂ) (b : Fin 2 → Zd d (sz.L n))
    (q0 q1 : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool) : ℂ :=
  if (zdistInf d (sz.L n) (b 0 - b 1) : ℝ) ≤ w ∧ (split d (sz.L n) (sz.W n) q0.1).1 = b 1 ∧
      (split d (sz.L n) (sz.W n) q0.2.1).1 = b 0 ∧ q0.2.2 = σ 0 ∧ q1 = (q0.2.1, q0.1, σ 1)
    then c else 0

/-- **The two-label local form of `𝗕_b`** (item 1): `scale · W^{-2d} Σ_{y∈[b₂], x∈[b₁]}
G(σ₁)_{yx} G(σ₂)_{xy}` for the labels in the window `|b₁ - b₂|_∞ ≤ w_n = (log W)^3 ℓ_s`, and `0`
outside it; the deterministic `𝒦` part of `STcltB` is a constant and drops out of `STcltX`. -/
def cltStep_loopForm (n : ℕ) (s : ℝ) (σ : Fin 2 → Bool) : LocalForm d (sz.L n) (sz.W n) 2 2 :=
  cltStep_pairForm (cltStep_c2 sz n σ (cltStep_win sz n s)
    ((cltStep_scale sz n * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ 2 : ℝ) : ℂ))

/-- **Item 1, evaluation.**  In the window, `cltStep_loopForm` evaluates to `scale · 𝓛^{(2)}_{σ,b}`. -/
theorem cltStep_loopForm_eval (n : ℕ) (s : ℝ) (σ : Fin 2 → Bool) (E u : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (b : Fin 2 → Zd d (sz.L n))
    (hb : (zdistInf d (sz.L n) (b 0 - b 1) : ℝ) ≤ cltStep_win sz n s) :
    (cltStep_loopForm sz n s σ).eval E u M b =
      ((cltStep_scale sz n : ℝ) : ℂ) * loopFine d (sz.L n) (sz.W n) M (zt E u) σ b := by
  unfold cltStep_loopForm
  rw [cltStep_pairForm_eval, cltStep_loopFine_two]
  set c : ℂ := ((cltStep_scale sz n * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ 2 : ℝ) : ℂ) with hc
  have hc' : c = ((cltStep_scale sz n : ℝ) : ℂ) * (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ ^ 2 := by
    rw [hc]; push_cast; ring
  have step1 : ∀ q0 : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool,
      ∑ q1 : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool,
        cltStep_c2 sz n σ (cltStep_win sz n s) c b q0 q1 *
          (gEntry d (sz.L n) (sz.W n) E u M q0.2.2 q0.1 q0.2.1 *
            gEntry d (sz.L n) (sz.W n) E u M q1.2.2 q1.1 q1.2.1) =
      if (split d (sz.L n) (sz.W n) q0.1).1 = b 1 ∧ (split d (sz.L n) (sz.W n) q0.2.1).1 = b 0 ∧
          q0.2.2 = σ 0 then
        c * (gEntry d (sz.L n) (sz.W n) E u M q0.2.2 q0.1 q0.2.1 *
          gEntry d (sz.L n) (sz.W n) E u M (σ 1) q0.2.1 q0.1) else 0 := by
    intro q0
    rw [Finset.sum_eq_single (q0.2.1, q0.1, σ 1)]
    · unfold cltStep_c2
      by_cases h : (split d (sz.L n) (sz.W n) q0.1).1 = b 1 ∧
          (split d (sz.L n) (sz.W n) q0.2.1).1 = b 0 ∧ q0.2.2 = σ 0
      · simp [h, hb]
      · simp [h]
    · intro q1 _ hq1
      unfold cltStep_c2
      have : ¬ (q1 = (q0.2.1, q0.1, σ 1)) := hq1
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  have step2 : ∀ y x : Idx d (sz.L n) (sz.W n),
      ∑ β : Bool, (if (split d (sz.L n) (sz.W n) y).1 = b 1 ∧ (split d (sz.L n) (sz.W n) x).1 = b 0 ∧
          β = σ 0 then
        c * (gEntry d (sz.L n) (sz.W n) E u M β y x *
          gEntry d (sz.L n) (sz.W n) E u M (σ 1) x y) else 0) =
      if (split d (sz.L n) (sz.W n) y).1 = b 1 ∧ (split d (sz.L n) (sz.W n) x).1 = b 0 then
        c * (Gres M (zt E u) (σ 0) y x * Gres M (zt E u) (σ 1) x y) else 0 := by
    intro y x
    rw [Finset.sum_eq_single (σ 0)]
    · by_cases h : (split d (sz.L n) (sz.W n) y).1 = b 1 ∧ (split d (sz.L n) (sz.W n) x).1 = b 0
      · simp [h, gEntry]
      · simp [h]
    · intro β _ hβ
      simp [hβ]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp only [step1, Fintype.sum_prod_type]
  simp only [step2]
  rw [hc', Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : (split d (sz.L n) (sz.W n) y).1 = b 1 ∧ (split d (sz.L n) (sz.W n) x).1 = b 0
  · simp only [h, and_self, ↓reduceIte]
    ring
  · simp [h]

/-- **Item 1, locality.**  `cltStep_loopForm` is `(w_n + 1)`-local, `w_n = (log W)^3 ℓ_s`: a non-zero
coefficient has `x ∈ [b₁]`, `y ∈ [b₂]` with `|b₁ - b₂|_∞ ≤ w_n`, and the sum of the distances of
`[x]`, `[y]` to one of the two labels is `|b₁ - b₂|_∞`. -/
theorem cltStep_loopForm_local (n : ℕ) (s : ℝ) (σ : Fin 2 → Bool) :
    (cltStep_loopForm sz n s σ).Local (cltStep_win sz n s + 1) := by
  intro b j q hq i
  by_cases hj : (j : ℕ) = 2
  · simp only [cltStep_loopForm, cltStep_pairForm, hj, ↓reduceDIte] at hq
    unfold cltStep_c2 at hq
    by_cases hc : (zdistInf d (sz.L n) (b 0 - b 1) : ℝ) ≤ cltStep_win sz n s ∧
        (split d (sz.L n) (sz.W n) (q ⟨0, by omega⟩).1).1 = b 1 ∧
        (split d (sz.L n) (sz.W n) (q ⟨0, by omega⟩).2.1).1 = b 0 ∧ (q ⟨0, by omega⟩).2.2 = σ 0 ∧
        q ⟨1, by omega⟩ = ((q ⟨0, by omega⟩).2.1, (q ⟨0, by omega⟩).1, σ 1)
    · obtain ⟨hw, hA, hB, -, hq1⟩ := hc
      have hs : zdistInf d (sz.L n) (b 1 - b 0) = zdistInf d (sz.L n) (b 0 - b 1) := by
        rw [← neg_sub, cltStep_zdistInf_neg]
      have hz : zdistInf d (sz.L n) (0 : Zd d (sz.L n)) = 0 := by simp [zdistInf]
      have h0 : 0 < (j : ℕ) := by omega
      have h1 : 1 < (j : ℕ) := by omega
      have hi : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by have := i.2; omega
      rcases hi with hi | hi
      · have hi' : i = ⟨0, h0⟩ := Fin.ext hi
        rw [hi']
        refine ⟨1, ?_⟩
        rw [hA, hB, sub_self, hz]
        push_cast
        linarith
      · have hi' : i = ⟨1, h1⟩ := Fin.ext hi
        rw [hi', hq1]
        refine ⟨0, ?_⟩
        simp only
        rw [hB, hA, sub_self, hz, hs]
        push_cast
        linarith
    · exact absurd hq (by simp [hc])
  · exact absurd hq (by simp [cltStep_loopForm, cltStep_pairForm, hj])

/-- **Item 1, coefficient bound.**  Every coefficient of `cltStep_loopForm` is at most `cltStep_scale`. -/
theorem cltStep_loopForm_coef_le (n : ℕ) (s : ℝ) (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n))
    (j : Fin (2 + 1)) (q : Fin j → Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool) :
    ‖(cltStep_loopForm sz n s σ).coef b j q‖ ≤ cltStep_scale sz n := by
  have hW : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hs0 : 0 ≤ cltStep_scale sz n := by
    unfold cltStep_scale
    exact Real.rpow_nonneg (by positivity) _
  have hWd : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ hW)
  have hc : ‖(((cltStep_scale sz n * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ 2 : ℝ)) : ℂ)‖ ≤ cltStep_scale sz n := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    calc cltStep_scale sz n * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ 2 ≤ cltStep_scale sz n * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (by positivity) hWd) hs0
      _ = cltStep_scale sz n := mul_one _
  simp only [cltStep_loopForm, cltStep_pairForm]
  split_ifs with hj
  · unfold cltStep_c2
    split_ifs
    · exact hc
    · simpa using hs0
  · simpa using hs0

/-- `cltStep_scale ≤ N²` once `N ≥ 𝔡^{-3}`, from `(eq:WO)` (`ilambda ≤ 𝔡⁻¹`) and `W^d ≤ N`. -/
theorem cltStep_scale_le (n : ℕ) {𝔡 : ℝ} (h𝔡 : 0 < 𝔡) (hlam0 : 0 ≤ sz.lam n) (hlam : sz.lam n ≤ 𝔡⁻¹)
    (hN : (𝔡⁻¹) ^ 3 ≤ ((sz.size n : ℕ) : ℝ)) :
    cltStep_scale sz n ≤ ((sz.size n : ℕ) : ℝ) ^ (2 : ℝ) := by
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set u : ℝ := 𝔡⁻¹ with hu
  have hu0 : 0 < u := inv_pos.2 h𝔡
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    exact this
  have hN0 : 0 < N := by linarith
  have hWd : ((sz.W n : ℕ) : ℝ) ^ d ≤ N := by
    have h1 : sz.W n ^ d ≤ sz.size n := by
      unfold Sizes.size
      exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by have := sz.three_le_L n; omega)) d
    have := (Nat.cast_le (α := ℝ)).mpr h1
    simpa using this
  have hA0 : 0 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hAle : sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d ≤ u ^ 2 * N := by
    have h1 : sz.lam n ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hlam0 hlam 2
    exact mul_le_mul h1 hWd (by positivity) (by positivity)
  have hu2 : u ^ 2 ≤ N ^ (2 / 3 : ℝ) := by
    calc u ^ 2 = (u ^ 3) ^ (2 / 3 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hu0.le]
          norm_num
      _ ≤ N ^ (2 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) hN (by norm_num)
  have hA : sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d ≤ N ^ (5 / 3 : ℝ) := by
    calc _ ≤ u ^ 2 * N := hAle
      _ ≤ N ^ (2 / 3 : ℝ) * N := mul_le_mul_of_nonneg_right hu2 hN0.le
      _ = N ^ (5 / 3 : ℝ) := by
          rw [← Real.rpow_add_one hN0.ne']
          norm_num
  unfold cltStep_scale
  calc (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ) ≤ (N ^ (5 / 3 : ℝ)) ^ (6 / 5 : ℝ) :=
        Real.rpow_le_rpow hA0 hA (by norm_num)
    _ = N ^ (2 : ℝ) := by
        rw [← Real.rpow_mul hN0.le]
        norm_num

/-- **Item 1, the identity.**  `STcltB` is `cltEvalAt` of the two-label form `cltStep_loopForm`, up to the
deterministic constant `scale · 𝒦^{(2)}_{s,σ,b}` (which cancels in `STcltX`), for the labels in
the window. -/
theorem cltStep_loopForm_stcltB (n : ℕ) (E s : ℝ) (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n))
    (hb : (zdistInf d (sz.L n) (b 0 - b 1) : ℝ) ≤ cltStep_win sz n s) (ω : sz.SeqΩ) :
    STcltB sz n E s σ b ω =
      cltEvalAt (cltStep_loopForm sz n s σ) E s (sz.slice n ω) b -
        ((cltStep_scale sz n : ℝ) : ℂ) * STKloop sz n E s σ b := by
  unfold STcltB STLKM STLM cltEvalAt
  rw [cltStep_loopForm_eval sz n s σ E s _ b hb]
  change ((cltStep_scale sz n : ℝ) : ℂ) * (loopFine d (sz.L n) (sz.W n) (Hflow d (sz.L n) (sz.W n) s (sz.slice n ω))
    (zt E s) σ b - STKloop sz n E s σ b) = _
  ring


/-- **Item 1, coefficient bound, eventually**: under `(eq:WO)` (`ilambda ≤ 𝔡⁻¹`) and `N → ∞`, every
coefficient of `cltStep_loopForm` is at most `N²` (`C' = 2`), eventually in `n`, for every `σ`. -/
theorem cltStep_loopForm_coef_le_eventually {𝔡 : ℝ} (h𝔡 : 0 < 𝔡) (hN : sz.SizeTendsto) (hWO : sz.WO 𝔡)
    (s : ℕ → ℝ) (σ : Fin 2 → Bool) :
    ∀ᶠ n in atTop, ∀ b j q, ‖(cltStep_loopForm sz n (s n) σ).coef b j q‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ (2 : ℝ) := by
  filter_upwards [hWO, hN.eventually_ge_atTop ((𝔡⁻¹) ^ 3)] with n hWOn hNn b j q
  have hlam0 : 0 ≤ sz.lam n := le_trans (Real.rpow_nonneg (Nat.cast_nonneg _) _) hWOn.1
  exact (cltStep_loopForm_coef_le sz n (s n) σ b j q).trans (cltStep_scale_le sz n h𝔡 hlam0 hWOn.2 hNn)


end LoopForm

/-! ## 7. The assembly: `stCltIso_holds` (item 3) -/

section Iso

variable {d : ℕ} (sz : Sizes d)

/-- The centred factor `STcltX` of the pin is the centred factor `cltStep_Xo` of the finite model for the
form `cltStep_loopForm` (the constant `scale · 𝒦` cancels in the centring). -/
private theorem cltStep_STcltX_eq {p : ℕ} (n : ℕ) (E s : ℝ) (σ : Fin 2 → Bool)
    (b : Fin (2 * p) → Fin 2 → Zd d (sz.L n))
    (hb : ∀ k, (zdistInf d (sz.L n) (b k 0 - b k 1) : ℝ) ≤ cltStep_win sz n s) {BY : ℝ}
    (hY : ∀ ω b', ‖cltEvalAt (cltStep_loopForm sz n s σ) E s ω b'‖ ≤ BY) (k : Fin (2 * p))
    (ω : sz.SeqΩ) :
    STcltX sz n E s σ (b k) (decide (p ≤ (k : ℕ))) ω =
      cltStep_Xo (cltStep_loopForm sz n s σ) (sz.lam n) E s b k (sz.slice n ω) := by
  set F := cltStep_loopForm sz n s σ with hF
  set K : ℂ := ((cltStep_scale sz n : ℝ) : ℂ) * STKloop sz n E s σ (b k) with hK
  have hB : ∀ ω', STcltB sz n E s σ (b k) ω' = cltEvalAt F E s (sz.slice n ω') (b k) - K :=
    fun ω' => cltStep_loopForm_stcltB sz n E s σ (b k) (hb k) ω'
  have hmeas : Measurable fun η : Ω d (sz.L n) (sz.W n) => cltEvalAt F E s η (b k) - K :=
    (cltStep_eval_meas F E s (b k)).sub_const K
  have hint : ∫ ω', STcltB sz n E s σ (b k) ω' ∂(sz.seqP) =
      (∫ η, cltEvalAt F E s η (b k) ∂(PF d (sz.L n) (sz.W n) (sz.lam n))) - K := by
    have h1 : ∫ ω', STcltB sz n E s σ (b k) ω' ∂(sz.seqP) =
        ∫ ω', (fun η => cltEvalAt F E s η (b k) - K) (sz.slice n ω') ∂(sz.seqP) :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω' => hB ω')
    rw [h1, cltTransfer sz n _ hmeas]
    have hi : Integrable (fun η => cltEvalAt F E s η (b k)) (PF d (sz.L n) (sz.W n) (sz.lam n)) :=
      Integrable.of_bound (cltStep_eval_meas F E s (b k)).aestronglyMeasurable BY
        (Filter.Eventually.of_forall fun η => hY η (b k))
    rw [integral_sub hi (integrable_const _), integral_const]
    simp
  have hdiff : STcltB sz n E s σ (b k) ω - ∫ ω', STcltB sz n E s σ (b k) ω' ∂(sz.seqP) =
      cltEvalAt F E s (sz.slice n ω) (b k) -
        ∫ η, cltEvalAt F E s η (b k) ∂(PF d (sz.L n) (sz.W n) (sz.lam n)) := by
    rw [hint, hB]; ring
  unfold STcltX cltStep_Xo
  rcases lt_or_ge (k : ℕ) p with hlt | hge
  · have h1 : ¬ p ≤ (k : ℕ) := not_le.2 hlt
    simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte, hlt]
    exact hdiff
  · have h1 : ¬ (k : ℕ) < p := not_lt.2 hge
    simp only [hge, decide_true, ↓reduceIte, h1]
    rw [hdiff]

/-- The number of real coordinates: `card (CoordF d L W) = 2 N²`. -/
private theorem cltStep_card_coord (n : ℕ) :
    (Fintype.card (CoordF d (sz.L n) (sz.W n)) : ℝ) = 2 * ((sz.size n : ℕ) : ℝ) ^ 2 := by
  have h : Fintype.card (CoordF d (sz.L n) (sz.W n)) =
      Fintype.card (Idx d (sz.L n) (sz.W n)) * (Fintype.card (Idx d (sz.L n) (sz.W n)) * 2) := by
    simp [CoordF, Fintype.card_prod, Fintype.card_bool]
  rw [h]
  push_cast
  rw [Sizes.card_Idx]
  ring

/-- The exponent bound: `2 N² · N^{-D-3} ≤ W^{-D}` for `N ≥ 2`, `0 < W ≤ N`, `D > 0`. -/
private theorem cltStep_exponent {N Wn D : ℝ} (hN2 : 2 ≤ N) (hW : 0 < Wn) (hWN : Wn ≤ N)
    (hD : 0 < D) : 2 * N ^ 2 * N ^ (-D - 3) ≤ Wn ^ (-D) := by
  have hN0 : 0 < N := by linarith
  have e1 : 2 * N ^ 2 * N ^ (-D - 3) = 2 * N ^ (-D - 1) := by
    have h : N ^ 2 = N ^ ((2 : ℕ) : ℝ) := (Real.rpow_natCast N 2).symm
    rw [h, mul_assoc, ← Real.rpow_add hN0]
    congr 2
    push_cast
    ring
  have e2 : N ^ (-D) = N ^ (-D - 1) * N := by
    rw [← Real.rpow_add_one hN0.ne']
    congr 1
    ring
  have hpos : 0 < N ^ (-D - 1) := Real.rpow_pos_of_pos hN0 _
  calc 2 * N ^ 2 * N ^ (-D - 3) = 2 * N ^ (-D - 1) := e1
    _ ≤ N ^ (-D - 1) * N := by nlinarith
    _ = N ^ (-D) := e2.symm
    _ ≤ Wn ^ (-D) := Real.rpow_le_rpow_of_nonpos hW hWN (by linarith)

end Iso


end RBM.Evol

namespace RBM.Gauss.Sizes

open Filter MeasureTheory RBM RBM.Gauss RBM.Evol

/-- **`(eq:bound_isolated)`** (`3_5:2245-2248`, cited from [DYYY25, (7.39)], [RBSO1D, (A.112)]): the
pin `STCltIso d`, proved by the i.i.d.-copy route of RBM2D (`Evolution/CltStep.lean`,
`CltDecorrelation.lean:286-376`): the centring of the isolated factor `X_i`, the coordinate telescope
over the `2 N²` real coordinates (`cltTelescope`), and the per-step bound `cltStep` (each step
`≤ N^{-D-3}`), generalised to the `2p` two-label factors `STcltX`.  Uses `HClt` at `τ = s`
(`STFlow`, `STStep2Concl`), the transfer `cltTransfer` and `cltGood_whp`, `cltCoord_tail`.  The
regime `STReg5I` and the condition `σ₁ ≠ σ₂` are not used. -/
theorem stCltIso_holds (d : ℕ) : STCltIso d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htl _ _ _ _ _ _ _ _ hS2 _ _
  have hH : HClt sz κ ε 𝔠 𝔡 z s s t Cd :=
    ⟨hd, hκ, hε, hflow, hs0, fun n => le_rfl, fun n => (hst n).le, htl, hS2⟩
  obtain ⟨⟨h𝔠, -, hN, hBW, hWO⟩, hE, ht1, hRC⟩ :=
    RBM.Green.v3_premises_of_stFlow sz hκ hε hflow htl
  have hκ' : 0 < κ / 2 := by linarith
  have hδ : 0 < ε / 2 := by linarith
  intro p hp D hD
  have key : ∀ σ : Fin 2 → Bool, ∀ᶠ n in atTop,
      ∀ b : Fin (2 * p) → (Fin 2 → Zd d (sz.L n)),
        (∀ k, ((zdistInf d (sz.L n) ((b k) 0 - (b k) 1) : ℕ) : ℝ) ≤
          Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (s n)) →
        (∃ i, ∀ j, j ≠ i → 10 * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (s n) ≤
          ((zdistInf d (sz.L n) ((b i) 0 - (b j) 0) : ℕ) : ℝ)) →
        ‖∫ ω, ∏ k : Fin (2 * p), STcltX sz n (STflowE z n) (s n) σ (b k) (decide (p ≤ k.val)) ω
            ∂(sz.seqP)‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := by
    intro σ
    have hcoef := cltStep_loopForm_coef_le_eventually sz h𝔡 hN hWO s σ
    have hstep := cltStep sz κ ε 𝔠 𝔡 z s t Cd hH 2 2 (by norm_num)
      (fun n => cltStep_loopForm sz n (s n) σ) hcoef (fun n => cltStep_loopForm_local sz n (s n) σ) p hp D hD
    filter_upwards [hstep, hRC, hcoef, hN.eventually_ge_atTop 2] with n hstepn hRn hcoefn hN2
    intro b hwin hisoEx
    obtain ⟨i, hiso⟩ := hisoEx
    set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
    have hN0 : 0 < N := by linarith
    have hwin' : ∀ k, ((zdistInf d (sz.L n) (b k 0 - b k 1) : ℕ) : ℝ) ≤ cltStep_win sz n (s n) := hwin
    have hiso' : ∀ m, m ≠ i →
        10 * cltStep_win sz n (s n) ≤ ((zdistInf d (sz.L n) (b i 0 - b m 0) : ℕ) : ℝ) := by
      intro m hm
      have := hiso m hm
      unfold cltStep_win
      rw [← mul_assoc]
      exact this
    have hR : N ^ (-1 + ε / 2) ≤ 1 - s n := by have := hst n; linarith [hRn]
    have hE' : |STflowE z n| ≤ 2 - κ / 2 := (hE n).le
    have hY : ∀ (ω : Ω d (sz.L n) (sz.W n)) (b' : Fin 2 → Zd d (sz.L n)),
        ‖cltEvalAt (cltStep_loopForm sz n (s n) σ) (STflowE z n) (s n) ω b'‖ ≤
          (((2 : ℕ) : ℝ) + 1) * N ^ (2 : ℝ) * (2 * N ^ 3 / cltCk (κ / 2)) ^ 2 :=
      fun ω b' => cltEval_detMulti_le d (sz.L n) (sz.W n) 2 (κ / 2) (ε / 2) (STflowE z n) (s n) 2
        (cltStep_loopForm sz n (s n) σ) 2 (Hflow d (sz.L n) (sz.W n) (s n) ω) b' hκ' hδ hE' hR hcoefn
        (Hflow_isHermitian _ _ _ _ _)
    -- the transfer to the finite model
    have hprodm : Measurable fun η : Ω d (sz.L n) (sz.W n) =>
        ∏ m : Fin (2 * p), cltStep_Xo (cltStep_loopForm sz n (s n) σ) (sz.lam n) (STflowE z n) (s n) b m η :=
      Finset.measurable_prod _ fun m _ => cltStep_Xo_meas _ _ _ _ b m
    have htr := cltTransfer sz n (fun η => ∏ m : Fin (2 * p),
      cltStep_Xo (cltStep_loopForm sz n (s n) σ) (sz.lam n) (STflowE z n) (s n) b m η) hprodm
    have hEq : ∫ ω, ∏ k : Fin (2 * p),
          STcltX sz n (STflowE z n) (s n) σ (b k) (decide (p ≤ k.val)) ω ∂(sz.seqP) =
        ∫ η, ∏ m : Fin (2 * p),
          cltStep_Xo (cltStep_loopForm sz n (s n) σ) (sz.lam n) (STflowE z n) (s n) b m η
          ∂(PF d (sz.L n) (sz.W n) (sz.lam n)) := by
      rw [← htr]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      exact Finset.prod_congr rfl fun k _ => cltStep_STcltX_eq sz n (STflowE z n) (s n) σ b hwin' hY k ω
    rw [hEq]
    have hcore := cltStep_assembly (sz.lam n) (cltStep_loopForm sz n (s n) σ) (STflowE z n) (s n) hY b i
      (Fintype.equivFin (CoordF d (sz.L n) (sz.W n))) (η := N ^ (-D - 3))
      (fun j hj => hstepn b i hwin' hiso' (Fintype.equivFin (CoordF d (sz.L n) (sz.W n))) j hj)
    refine hcore.trans ?_
    rw [cltStep_card_coord sz n]
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have hWN : ((sz.W n : ℕ) : ℝ) ≤ N := by
      have hL1 : 1 ≤ sz.L n := by have := sz.three_le_L n; omega
      have h1 : sz.W n ≤ sz.size n := by
        unfold Sizes.size
        calc sz.W n = sz.W n * 1 := (mul_one _).symm
          _ ≤ sz.W n * sz.L n := Nat.mul_le_mul_left _ hL1
          _ ≤ (sz.W n * sz.L n) ^ d := Nat.le_self_pow (by omega) _
      exact (Nat.cast_le (α := ℝ)).mpr h1
    exact cltStep_exponent hN2 hW0 hWN hD
  have hall := Filter.eventually_all.2 key
  filter_upwards [hall] with n hn σ _ b hwin hiso
  exact hn σ b hwin hiso

end RBM.Gauss.Sizes

/-! ## 8. Compiled nonempty instances

At `d = 3` on the merged `Step5Inst.szCL` (`Induction/Step5Pins.lean:640`: `m = n + 24`,
`L_n = 2 m^5`, `W_n = 2^m`, `lam ≡ 1`), the flow `flow_zCL` (`κ = ε = 1/10`, `𝔠 = 1/6`,
`𝔡 = 1/10`, `z = zCL`), `s ≡ 0` (`sCL`), `t = tCL`, `C_d = 1`.  Only `STStep2Concl` (the Step 2
pins, another gate) stays a hypothesis of the instance of `cltStep`; every deterministic hypothesis is
discharged (`cltGood_hclt_szCL`, the coefficient bound from `szCL_WO`, the locality
`cltStep_loopForm_local`).  The statements go through the generic definitions applied to `szCL` (the
elaboration trap of T2141).  The label configuration `cltStep_szCL_witness` has the window
`|b₁ - b₂|_∞ = m² > 0` (not the degenerate window `0` of `szCL_cltIso_witness`) and is isolated. -/

namespace RBM.Gauss.Step5Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Evol Filter

/-- The point `y_n = (m², 0, 0)`, `m = n + 24`, of `Z_{L_n}^3`: `|y_n| = m²`. -/
def cltStep_yCL (n : ℕ) : Zd 3 (szCL.L n) := Pi.single 0 (((n + 24) ^ 2 : ℕ) : ZMod (szCL.L n))

theorem cltStep_zdistInf_yCL (n : ℕ) : zdistInf 3 (szCL.L n) (cltStep_yCL n) = (n + 24) ^ 2 := by
  have h1 : (n + 24) ^ 2 ≤ (n + 24) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 1 ≤ (n + 24) ^ 5 := Nat.one_le_pow _ _ (by omega)
  have hlt : (n + 24) ^ 2 < szCL.L n := by
    change (n + 24) ^ 2 < 2 * (n + 24) ^ 5
    omega
  have hz : zdist (szCL.L n) (((n + 24) ^ 2 : ℕ) : ZMod (szCL.L n)) = (n + 24) ^ 2 := by
    unfold zdist
    rw [ZMod.val_cast_of_lt hlt]
    change min ((n + 24) ^ 2) (2 * (n + 24) ^ 5 - (n + 24) ^ 2) = (n + 24) ^ 2
    omega
  apply le_antisymm
  · calc zdistInf 3 (szCL.L n) (cltStep_yCL n) ≤ zdistD 3 (szCL.L n) (cltStep_yCL n) := zdistInf_le_zdistD _ _ _
      _ = (n + 24) ^ 2 := by rw [cltStep_yCL, zdistD_single, hz]
  · calc (n + 24) ^ 2 = zdist (szCL.L n) (cltStep_yCL n 0) := by rw [cltStep_yCL, Pi.single_eq_same, hz]
      _ ≤ zdistInf 3 (szCL.L n) (cltStep_yCL n) :=
          Finset.le_sup (f := fun i => zdist (szCL.L n) (cltStep_yCL n i)) (Finset.mem_univ 0)

/-- **A label configuration with a positive window satisfying the premises of `cltStep` and of
`STCltIsoConcl`** at `(szCL, sCL)`, `p = 1`, every `n`: `b^{(1)} = (0, y_n)` (window `|b₁ - b₂| =
m² > 0`, `m² ≤ (log W)^3 ℓ_s`) and `b^{(2)} = (x_n, x_n)`; `b^{(1)}` is isolated:
`10 (log W)^3 ℓ_s ≤ 10 m³ ≤ m⁵ = |x_n|`. -/
theorem cltStep_szCL_witness (n : ℕ) :
    ∃ b : Fin (2 * 1) → (Fin 2 → Zd 3 (szCL.L n)),
      (∀ k, ((zdistInf 3 (szCL.L n) ((b k) 0 - (b k) 1) : ℕ) : ℝ) ≤ cltStep_win szCL n (sCL n)) ∧
      0 < zdistInf 3 (szCL.L n) ((b 0) 0 - (b 0) 1) ∧
      (∀ j, j ≠ 0 → 10 * cltStep_win szCL n (sCL n) ≤
        ((zdistInf 3 (szCL.L n) ((b 0) 0 - (b j) 0) : ℕ) : ℝ)) := by
  have hlog1 := szCL_one_le_log_W n
  have hlogm := szCL_log_W_le n
  have hlogeq := szCL_log_W n
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hw : cltStep_win szCL n (sCL n) = Real.log ((szCL.W n : ℕ) : ℝ) ^ 3 := by
    unfold cltStep_win
    rw [szCL_ellT_s, mul_one]
  have hlow : ((n : ℝ) + 24) ^ 2 ≤ Real.log ((szCL.W n : ℕ) : ℝ) ^ 3 := by
    rw [hlogeq]
    have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have h24 : (24 : ℝ) ≤ (n : ℝ) + 24 := by linarith
    have hm0 : (0 : ℝ) ≤ (n : ℝ) + 24 := by linarith
    have h3 : ((n : ℝ) + 24) ^ 3 * (1 / 8) ≤ ((n : ℝ) + 24) ^ 3 * Real.log 2 ^ 3 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc (1 / 8 : ℝ) = (1 / 2) ^ 3 := by norm_num
        _ ≤ Real.log 2 ^ 3 := pow_le_pow_left₀ (by norm_num) hl2 3
    calc ((n : ℝ) + 24) ^ 2 ≤ ((n : ℝ) + 24) ^ 3 * (1 / 8) := by
          have : ((n : ℝ) + 24) ^ 3 = ((n : ℝ) + 24) ^ 2 * ((n : ℝ) + 24) := by ring
          rw [this]
          nlinarith [sq_nonneg ((n : ℝ) + 24)]
      _ ≤ ((n : ℝ) + 24) ^ 3 * Real.log 2 ^ 3 := h3
      _ = (((n : ℝ) + 24) * Real.log 2) ^ 3 := by ring
  refine ⟨fun k => if k = 0 then ![0, cltStep_yCL n] else ![xCL n, xCL n], fun k => ?_, ?_, fun j hj => ?_⟩
  · rw [hw]
    by_cases hk : k = 0
    · have h : zdistInf 3 (szCL.L n)
          (((fun k : Fin (2 * 1) => if k = 0 then ![0, cltStep_yCL n] else
              (![xCL n, xCL n] : Fin 2 → Zd 3 (szCL.L n))) k) 0 -
            ((fun k : Fin (2 * 1) => if k = 0 then ![0, cltStep_yCL n] else
              (![xCL n, xCL n] : Fin 2 → Zd 3 (szCL.L n))) k) 1) = (n + 24) ^ 2 := by
        simp only [hk, ↓reduceIte]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_sub]
        rw [cltStep_zdistInf_neg, cltStep_zdistInf_yCL]
      rw [h]
      push_cast
      exact hlow
    · have h : zdistInf 3 (szCL.L n)
          (((fun k : Fin (2 * 1) => if k = 0 then ![0, cltStep_yCL n] else
              (![xCL n, xCL n] : Fin 2 → Zd 3 (szCL.L n))) k) 0 -
            ((fun k : Fin (2 * 1) => if k = 0 then ![0, cltStep_yCL n] else
              (![xCL n, xCL n] : Fin 2 → Zd 3 (szCL.L n))) k) 1) = 0 := by
        simp [hk, zdistInf]
      rw [h]
      push_cast
      exact pow_nonneg (by linarith) 3
  · simp only [↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one, zero_sub]
    rw [cltStep_zdistInf_neg, cltStep_zdistInf_yCL]
    positivity
  · have h : ((fun k : Fin (2 * 1) => if k = 0 then ![0, cltStep_yCL n] else
          (![xCL n, xCL n] : Fin 2 → Zd 3 (szCL.L n))) 0) 0 -
        ((fun k : Fin (2 * 1) => if k = 0 then ![0, cltStep_yCL n] else
          (![xCL n, xCL n] : Fin 2 → Zd 3 (szCL.L n))) j) 0 = -xCL n := by
      simp [hj]
    rw [h, cltStep_zdistInf_neg, zdistInf_xCL, hw]
    have h3 : Real.log ((szCL.W n : ℕ) : ℝ) ^ 3 ≤ ((n : ℝ) + 24) ^ 3 :=
      pow_le_pow_left₀ (by linarith) hlogm 3
    have h24 : (24 : ℝ) ≤ (n : ℝ) + 24 := by linarith
    have hm3 : (0 : ℝ) ≤ ((n : ℝ) + 24) ^ 3 := by positivity
    have h10 : 10 * ((n : ℝ) + 24) ^ 3 ≤ ((n : ℝ) + 24) ^ 5 := by
      have : ((n : ℝ) + 24) ^ 5 = ((n : ℝ) + 24) ^ 2 * ((n : ℝ) + 24) ^ 3 := by ring
      rw [this]
      have : (10 : ℝ) ≤ ((n : ℝ) + 24) ^ 2 := by nlinarith
      nlinarith
    push_cast
    linarith

/-- **Instance of `stCltIso_holds`** (`d = 3`): the pin `STCltIso 3` applied at `(szCL, zCL, sCL,
tCL)`, `C_d = 1`; every deterministic hypothesis (flow, time ranges, regime, `(con_st_ind)`) is
discharged by the merged `inst_cltIso`, and the premises of `STCltIsoConcl` are satisfiable with a
positive window at every `n` (`cltStep_szCL_witness`). -/
example : InstIng5Concl (fun sz E s t => STCltIsoConcl sz E s t) szCL zCL sCL tCL 1 :=
  inst_cltIso (stCltIso_holds 3) 1 one_pos

example : ∀ n, ∃ b : Fin (2 * 1) → (Fin 2 → Zd 3 (szCL.L n)),
    (∀ k, ((zdistInf 3 (szCL.L n) ((b k) 0 - (b k) 1) : ℕ) : ℝ) ≤
      Real.log ((szCL.W n : ℕ) : ℝ) ^ 3 * ellT (szCL.L n) (szCL.lam n) (sCL n)) ∧
    0 < zdistInf 3 (szCL.L n) ((b 0) 0 - (b 0) 1) ∧
    (∃ i, ∀ j, j ≠ i → 10 * Real.log ((szCL.W n : ℕ) : ℝ) ^ 3 * ellT (szCL.L n) (szCL.lam n) (sCL n) ≤
      ((zdistInf 3 (szCL.L n) ((b i) 0 - (b j) 0) : ℕ) : ℝ)) := by
  intro n
  obtain ⟨b, h1, h2, h3⟩ := cltStep_szCL_witness n
  refine ⟨b, h1, h2, 0, fun j hj => ?_⟩
  have := h3 j hj
  unfold cltStep_win at this
  rw [← mul_assoc] at this
  exact this

/-- **Instance of `stCltIso_holds` as a statement about the pin itself** (`STCltIso 3`). -/
example : STCltIso 3 := stCltIso_holds 3

/-- **Instance of item 1** at `(szCL, sCL)`, `σ = (+,-)`, every `n`: for the label pair `b = (0, y_n)`
of positive window `m² > 0` (`cltStep_szCL_witness`), `STcltB` is `cltEvalAt` of the two-label form
`cltStep_loopForm` up to the constant `scale · 𝒦`, and the form is `(w_n + 1)`-local with
coefficients `≤ scale`. -/
example (n : ℕ) (E : ℝ) (ω : szCL.SeqΩ) :
    ∃ b : Fin 2 → Zd 3 (szCL.L n), 0 < zdistInf 3 (szCL.L n) (b 0 - b 1) ∧
      STcltB szCL n E (sCL n) ![true, false] b ω =
        cltEvalAt (cltStep_loopForm szCL n (sCL n) ![true, false]) E (sCL n) (szCL.slice n ω) b -
          ((cltStep_scale szCL n : ℝ) : ℂ) * STKloop szCL n E (sCL n) ![true, false] b ∧
      (cltStep_loopForm szCL n (sCL n) ![true, false]).Local (cltStep_win szCL n (sCL n) + 1) ∧
      ∀ b' j q, ‖(cltStep_loopForm szCL n (sCL n) ![true, false]).coef b' j q‖ ≤
        cltStep_scale szCL n := by
  obtain ⟨b, h1, h2, -⟩ := cltStep_szCL_witness n
  exact ⟨b 0, h2, cltStep_loopForm_stcltB szCL n E (sCL n) ![true, false] (b 0) (h1 0) ω,
    cltStep_loopForm_local szCL n (sCL n) ![true, false],
    fun b' j q => cltStep_loopForm_coef_le szCL n (sCL n) ![true, false] b' j q⟩

/-- The coefficient bound of `cltStep_loopForm` at `szCL`: `‖coef‖ ≤ N²`, eventually (`szCL_WO`,
`szCL_tendsto`). -/
theorem cltStep_szCL_coef (σ : Fin 2 → Bool) :
    ∀ᶠ n in atTop, ∀ b j q, ‖(cltStep_loopForm szCL n (sCL n) σ).coef b j q‖ ≤
      ((szCL.size n : ℕ) : ℝ) ^ (2 : ℝ) :=
  cltStep_loopForm_coef_le_eventually szCL (by norm_num) szCL_tendsto szCL_WO (fun n => sCL n) σ

/-- **Instance of item 2 (`cltStep`)** at `(szCL, zCL, sCL, tCL)`, `p = 1`, `D = 1`, `σ = (+,-)`,
the form `cltStep_loopForm` of `STcltB`: `HClt` from `cltGood_hclt_szCL`; the coefficient bound and the
locality are discharged; only `STStep2Concl` stays a hypothesis.  The premises (window and isolation)
are satisfiable at every `n` (`cltStep_szCL_witness`). -/
example (hStep2 : STStep2Concl szCL (STflowE zCL) sCL tCL 1) :=
  cltStep szCL (1 / 10) (1 / 10) (1 / 6) (1 / 10) zCL sCL tCL 1 (cltGood_hclt_szCL hStep2) 2 2
    (by norm_num) (fun n => cltStep_loopForm szCL n (sCL n) ![true, false])
    (cltStep_szCL_coef ![true, false]) (fun n => cltStep_loopForm_local szCL n (sCL n) ![true, false])
    1 le_rfl 1 one_pos

/-- **Instance of item 2 at nondegenerate labels**: the conclusion of `cltStep` at `(szCL, zCL, sCL,
tCL)`, `p = 1`, `D = 1`, `σ = (+,-)`, specialised to the label configuration `b = (cltStep_szCL_witness n)`
(window `m² > 0`, `b^{(1)}` isolated), for every enumeration `e` of the real coordinates and every
step `j`: the type is inferred (the elaboration trap forbids writing `Idx 3 (szCL.L n) …`). -/
example (hStep2 : STStep2Concl szCL (STflowE zCL) sCL tCL 1) :=
  (cltStep szCL (1 / 10) (1 / 10) (1 / 6) (1 / 10) zCL sCL tCL 1 (cltGood_hclt_szCL hStep2) 2 2
    (by norm_num) (fun n => cltStep_loopForm szCL n (sCL n) ![true, false])
    (cltStep_szCL_coef ![true, false])
    (fun n => cltStep_loopForm_local szCL n (sCL n) ![true, false]) 1 le_rfl 1 one_pos).mono
    fun n hn => hn (cltStep_szCL_witness n).choose 0 (cltStep_szCL_witness n).choose_spec.1
      (cltStep_szCL_witness n).choose_spec.2.2

end RBM.Gauss.Step5Inst

namespace RBM.Evol

#print axioms cltStep_pairForm_eval
#print axioms cltStep_loopForm_eval
#print axioms cltStep_loopForm_local
#print axioms cltStep_loopForm_coef_le
#print axioms cltStep_loopForm_coef_le_eventually
#print axioms cltStep_loopForm_stcltB
#print axioms cltStep_scale_le
#print axioms cltStep
#print axioms RBM.Gauss.Sizes.stCltIso_holds
#print axioms RBM.Gauss.Step5Inst.cltStep_zdistInf_yCL
#print axioms RBM.Gauss.Step5Inst.cltStep_szCL_witness
#print axioms RBM.Gauss.Step5Inst.cltStep_szCL_coef

end RBM.Evol

end
