/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.ExpEtermsAGen
import RBM3D.Induction.ExpEtermsB
import RBM3D.Chain.DecayGen
import RBM3D.Chain.SEforLnGen2

/-!
# `(eq:Exp(L-K)2)`, `(eq:ExpLWn=2_smalleta)`, `(deccA0)` of `D_u` over the carrier (BA-V row V1s2', ticket T2506 row a, targets 3-5)

Additive restatement of `Induction/ExpEtermsB.lean` (not edited) over a carrier `C : FlowFM sz` and a law `μ`, on the vocabulary of `Chain/Step6Gen.lean`.
Paper: arXiv:2507.20274, `paper/tex/6_Step6_two_loop.tex:63-79` (`(eq:Exp(L-K)2)`, `(eq:ExpLWn=2_smalleta)`, regime (iv)) and
`paper/tex/3_5_Loop_Hierarchy.tex:1634` (`(deccA0)` for the drift `D_u`).

* **Target 3** (split and kit): the split `𝔼ℰ^{G̃} = (𝔼 avg)·S·𝒦^{(3)} + 𝔼[avg·S·(𝓛-𝒦)^{(3)}]` (private twins of the band `expDrEGtLKM`, `expDrEGtK`), the polynomial envelopes
  `≤ N⁶` of `ℰ^{LK×LK}`, `ℰ^{G̃}` and its `(𝓛-𝒦)^{(3)}` part (**W-a**: `CltRepg` of row 9', `stKbound_timeIccgL` of row 17, `K^{(1)} = m` of row 19 for `‖m‖ ≤ N`),
  `≺ → 𝔼` (`ExpEtermsBGen_expect`), the two random estimates `expDr_LK_precg`, `expDr_EGtLK_precg` (from `STLKUgL`, `k = 1, 2, 3`) and the deterministic one
  `expDr_EGtK_precg` (from `STExpAvgUgL` and `stKbound_timeIccgL` at `k = 3`).  The size-level lemmas `expDr_Bctl_le_IV`, `expAvg_Bctl_ge`, `expDr_floor` are reused.
* **Target 4**: `STExpDriftLoConclgL_of_LKU` (per carrier) and `stExpDriftLogL_of` (the pin `STExpDriftLogL`, per family); the band pin `stExpDriftLo_holds` is re-derived
  (`stExpDriftLo_of_gL`, through `STExpDriftLo_iff_gL`).
* **Target 5** (**W-d**): `STExpDriftDecayConclgL_of_GdecayW` (per carrier) and `stExpDriftDecaygL_of` (the pin `STExpDriftDecaygL`); the E-term decays are premises of
  family row 18 stated at the `FlowFM` labels `STELKLKg C`, `STEGtg C` (discharged at BA by `baEtermDecaygL`, at the band by `stEtermDecay` through the term bridges);
  the band pin `stExpDriftDecay_holds` is re-derived (`stExpDriftDecay_of_gL`).

No `def`, `abbrev` or `structure` is public; the two twins are `private`.  The family premises of the wrappers are written inline (ticket table, rows 2, 9', 17, 18, 19, 20).
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open private expDr_first_moment expDr_floor expDr_decay_step expDr_W_le_size from RBM3D.Induction.ExpEtermsB
open private walk_measurable_seqHflow from RBM3D.Path.Walk

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The two cuts of `ℰ^{G̃}` over the carrier kernel -/

section Cuts

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz)

/-- The bilinear sum with the carrier kernel: `‖Σ_{x,y} A_x S_{xy} C_y‖ ≤ α β L^d` if `|A| ≤ α`, `|C| ≤ β`, and the column sums of `|S|` are `≤ 1` (family row 20;
band `expDr_bilin_le`, `ExpEtermsB:148`). -/
private theorem ExpEtermsBGen_bilin_le (n : ℕ) (hcol : ∀ y : Zd d (sz.L n), ∑ x : Zd d (sz.L n), ‖C.S n x y‖ ≤ 1)
    (A C' : Zd d (sz.L n) → ℂ) {α β : ℝ} (hA : ∀ x, ‖A x‖ ≤ α) (hC : ∀ y, ‖C' y‖ ≤ β) :
    ‖∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n), A x * C.S n x y * C' y‖ ≤ α * β * ((sz.L n : ℕ) : ℝ) ^ d := by
  have hα : 0 ≤ α := (norm_nonneg _).trans (hA 0)
  have hβ : 0 ≤ β := (norm_nonneg _).trans (hC 0)
  calc _ ≤ ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n), ‖A x * C.S n x y * C' y‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => norm_sum_le _ _)
    _ ≤ ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n), (α * β) * ‖C.S n x y‖ :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => by
          rw [norm_mul, norm_mul]
          calc ‖A x‖ * ‖C.S n x y‖ * ‖C' y‖ = ‖A x‖ * ‖C' y‖ * ‖C.S n x y‖ := by ring
            _ ≤ (α * β) * ‖C.S n x y‖ :=
              mul_le_mul_of_nonneg_right (mul_le_mul (hA x) (hC y) (norm_nonneg _) hα) (norm_nonneg _)
    _ ≤ ∑ y : Zd d (sz.L n), (α * β) := by
        rw [Finset.sum_comm]
        refine Finset.sum_le_sum fun y _ => ?_
        rw [← Finset.mul_sum]
        calc (α * β) * ∑ x : Zd d (sz.L n), ‖C.S n x y‖ ≤ (α * β) * 1 :=
              mul_le_mul_of_nonneg_left (hcol y) (mul_nonneg hα hβ)
          _ = α * β := mul_one _
    _ = α * β * ((sz.L n : ℕ) : ℝ) ^ d := by
        rw [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
        push_cast; ring

/-- The two cuts of `ℰ^{G̃}` with a common bound: `‖W^d Σ_{x,y} (A₀ S C₀ + A₁ S C₁)‖ ≤ 2 W^d L^d α β` (band `expDr_cuts_le`, `ExpEtermsB:173`). -/
private theorem ExpEtermsBGen_cuts_le (n : ℕ) (hcol : ∀ y : Zd d (sz.L n), ∑ x : Zd d (sz.L n), ‖C.S n x y‖ ≤ 1)
    (A₀ A₁ C₀ C₁ : Zd d (sz.L n) → ℂ) {α β : ℝ} (hA₀ : ∀ x, ‖A₀ x‖ ≤ α) (hA₁ : ∀ x, ‖A₁ x‖ ≤ α)
    (hC₀ : ∀ y, ‖C₀ y‖ ≤ β) (hC₁ : ∀ y, ‖C₁ y‖ ≤ β) :
    ‖(((sz.W n : ℕ) : ℂ) ^ d) * ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
        (A₀ x * C.S n x y * C₀ y + A₁ x * C.S n x y * C₁ y)‖ ≤
      2 * (((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d) * (α * β) := by
  have h0 := ExpEtermsBGen_bilin_le C n hcol A₀ C₀ hA₀ hC₀
  have h1 := ExpEtermsBGen_bilin_le C n hcol A₁ C₁ hA₁ hC₁
  have hsum : ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
        (A₀ x * C.S n x y * C₀ y + A₁ x * C.S n x y * C₁ y) =
      (∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n), A₀ x * C.S n x y * C₀ y) +
        ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n), A₁ x * C.S n x y * C₁ y := by
    simp only [Finset.sum_add_distrib]
  rw [hsum, norm_mul, norm_pow, Complex.norm_natCast]
  have hW : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  calc ((sz.W n : ℕ) : ℝ) ^ d * ‖_‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d *
        (α * β * ((sz.L n : ℕ) : ℝ) ^ d + α * β * ((sz.L n : ℕ) : ℝ) ^ d) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add h0 h1)) hW
    _ = _ := by ring

/-- The `(𝓛-𝒦)^{(3)}` part of `ℰ^{G̃,(2)}` over the carrier: `STEGtg` with `𝓛^{(3)}` replaced by `(𝓛-𝒦)^{(3)}` in the cut 3-loops (private twin of the band `expDrEGtLKM`,
`ExpEtermsB:53`). -/
private def ExpEtermsBGen_EGtLK (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
    ((C.L n u (fun _ : Fin 1 => σ 0) (fun _ => x) ω - (if σ 0 then C.m n else (starRingEnd ℂ) (C.m n))) * C.S n x y *
        (C.L n u ![σ 0, σ 0, σ 1] ![y, a 0, a 1] ω - C.K n u ![σ 0, σ 0, σ 1] ![y, a 0, a 1]) +
      (C.L n u (fun _ : Fin 1 => σ 1) (fun _ => x) ω - (if σ 1 then C.m n else (starRingEnd ℂ) (C.m n))) * C.S n x y *
        (C.L n u ![σ 0, σ 1, σ 1] ![a 0, y, a 1] ω - C.K n u ![σ 0, σ 1, σ 1] ![a 0, y, a 1]))

/-- The deterministic part `W^d Σ_k Σ_{x,y} (𝔼 𝓛^{(1)}_{σ_k,x} - m_{σ_k}) S_{xy} 𝒦^{(3)}(cut_k y)` of `𝔼ℰ^{G̃,(2)}` (private twin of the band `expDrEGtK`, `ExpEtermsB:63`;
`𝔼 avg = 𝔼 𝓛^{(1)} - m` is the carrier reading of the average of `STExpAvgUgL`). -/
private def ExpEtermsBGen_EGtK (μ : Measure sz.SeqΩ) (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
    (((∫ ω, C.L n u (fun _ : Fin 1 => σ 0) (fun _ => x) ω ∂μ) - (if σ 0 then C.m n else (starRingEnd ℂ) (C.m n))) * C.S n x y *
        C.K n u ![σ 0, σ 0, σ 1] ![y, a 0, a 1] +
      ((∫ ω, C.L n u (fun _ : Fin 1 => σ 1) (fun _ => x) ω ∂μ) - (if σ 1 then C.m n else (starRingEnd ℂ) (C.m n))) * C.S n x y *
        C.K n u ![σ 0, σ 1, σ 1] ![a 0, y, a 1])

end Cuts

/-! ## 2. Measurability, integrability and the envelope of `ℰ^{G̃}` (from `CltRepg`) -/

section Env

variable {d : ℕ} {sz : Sizes d} {C : FlowFM sz} {μ : Measure sz.SeqΩ}
  {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}

/-- The loops of the carrier are measurable random variables (`CltRepg`: they are `loopFine` of the matrix `H₀ n + H_u(ω)`, measurable in the sample). -/
private theorem ExpEtermsBGen_meas_L (hrep : CltRepg C μ H₀ g' E) (n : ℕ) (u : ℝ) {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) : Measurable fun ω : sz.SeqΩ => C.L n u σ a ω := by
  obtain ⟨-, -, hr⟩ := hrep
  have hf : (fun ω : sz.SeqΩ => C.L n u σ a ω) = fun ω => loopFine d (sz.L n) (sz.W n)
      (H₀ n + Matrix.of fun i j : Idx d (sz.L n) (sz.W n) => Sizes.seqHflow (sz.withLam g') n u ω i j)
      (ztOf (C.m n) (E n) u) σ a := funext fun ω => (hr n u ω).2 k σ a
  rw [hf]
  have h1 : Measurable fun ω : sz.SeqΩ => Sizes.seqHflow (sz.withLam g') n u ω :=
    walk_measurable_seqHflow (sz.withLam g') n u
  have h2 : Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => H₀ n + H :=
    (continuous_const.add continuous_id).measurable
  exact (walk_measurable_loopFine d (sz.L n) (sz.W n) (ztOf (C.m n) (E n) u) σ a).comp (h2.comp h1)

/-- `𝓛^{(1)}` is integrable (bounded by `η⁻¹`, measurable). -/
private theorem ExpEtermsBGen_integrable_L1 [IsProbabilityMeasure μ] (hrep : CltRepg C μ H₀ g' E) (n : ℕ) {u : ℝ} (hu : u < 1)
    (him : 0 < (C.m n).im) (τ : Bool) (x : Zd d (sz.L n)) :
    Integrable (fun ω => C.L n u (fun _ : Fin 1 => τ) (fun _ => x) ω) μ :=
  Integrable.of_bound (ExpEtermsBGen_meas_L hrep n u _ _).aestronglyMeasurable (etaOf (C.m n) u)⁻¹
    (Eventually.of_forall fun ω => by
      have := ExpEtermsAGen_norm_L_le hrep n hu him (k := 0) (fun _ : Fin 1 => τ) (fun _ => x) ω
      simpa using this)

/-- `‖avg‖ ≤ η⁻¹ + c_m` for `avg = 𝓛^{(1)}_{τ,x} - m_τ` (`‖𝓛^{(1)}‖ ≤ η⁻¹`, `‖m_τ‖ = ‖m‖ ≤ c_m`). -/
private theorem ExpEtermsBGen_avg_le (hrep : CltRepg C μ H₀ g' E) (n : ℕ) {u : ℝ} (hu : u < 1) (him : 0 < (C.m n).im) {cm : ℝ}
    (hcm : ‖C.m n‖ ≤ cm) (τ : Bool) (x : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    ‖C.L n u (fun _ : Fin 1 => τ) (fun _ => x) ω - (if τ then C.m n else (starRingEnd ℂ) (C.m n))‖ ≤
      (etaOf (C.m n) u)⁻¹ + cm := by
  have hmσ : ‖(if τ then C.m n else (starRingEnd ℂ) (C.m n))‖ ≤ cm := by
    cases τ
    · simpa using hcm
    · simpa using hcm
  have h1 : ‖C.L n u (fun _ : Fin 1 => τ) (fun _ => x) ω‖ ≤ (etaOf (C.m n) u)⁻¹ := by
    have := ExpEtermsAGen_norm_L_le hrep n hu him (k := 0) (fun _ : Fin 1 => τ) (fun _ => x) ω
    simpa using this
  exact (norm_sub_le _ _).trans (add_le_add h1 hmσ)

/-- **The envelope of `ℰ^{G̃}`** (band `expDr_envEGt`, `ExpEtermsB:207`): `‖avg‖ ≤ η⁻¹ + c_m`, `‖𝓛^{(3)}‖ ≤ η⁻³`, the column sums of `S` and the two cuts. -/
private theorem ExpEtermsBGen_envEGt (hrep : CltRepg C μ H₀ g' E) (n : ℕ) {u : ℝ} (hu : u < 1) (him : 0 < (C.m n).im) {cm : ℝ}
    (hcm : ‖C.m n‖ ≤ cm) (hcol : ∀ y : Zd d (sz.L n), ∑ x : Zd d (sz.L n), ‖C.S n x y‖ ≤ 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    ‖STEGtg C n u σ a ω‖ ≤
      2 * (((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d) * (((etaOf (C.m n) u)⁻¹ + cm) * (etaOf (C.m n) u)⁻¹ ^ 3) := by
  have hL3 : ∀ (σ' : Fin 3 → Bool) (b : Fin 3 → Zd d (sz.L n)), ‖C.L n u σ' b ω‖ ≤ (etaOf (C.m n) u)⁻¹ ^ 3 :=
    fun σ' b => ExpEtermsAGen_norm_L_le hrep n hu him (k := 2) σ' b ω
  exact ExpEtermsBGen_cuts_le C n hcol _ _ _ _ (fun x => ExpEtermsBGen_avg_le hrep n hu him hcm (σ 0) x ω)
    (fun x => ExpEtermsBGen_avg_le hrep n hu him hcm (σ 1) x ω) (fun y => hL3 _ _) (fun y => hL3 _ _)

/-- `𝓔^{G̃}` is integrable (measurable and bounded; the bound of `ExpEtermsBGen_envEGt` with `c_m = ‖m‖`). -/
private theorem ExpEtermsBGen_integrable_EGt [IsProbabilityMeasure μ] (hrep : CltRepg C μ H₀ g' E) (n : ℕ) {u : ℝ} (hu : u < 1)
    (him : 0 < (C.m n).im) (hcol : ∀ y : Zd d (sz.L n), ∑ x : Zd d (sz.L n), ‖C.S n x y‖ ≤ 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    Integrable (fun ω => STEGtg C n u σ a ω) μ := by
  refine Integrable.of_bound ?_ _ (Eventually.of_forall fun ω => ExpEtermsBGen_envEGt hrep n hu him (le_refl ‖C.m n‖) hcol σ a ω)
  refine Measurable.aestronglyMeasurable ?_
  unfold STEGtg
  refine measurable_const.mul (Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun y _ => ?_)
  exact ((((ExpEtermsBGen_meas_L hrep n u _ _).sub_const _).mul_const _).mul (ExpEtermsBGen_meas_L hrep n u _ _)).add
    ((((ExpEtermsBGen_meas_L hrep n u _ _).sub_const _).mul_const _).mul (ExpEtermsBGen_meas_L hrep n u _ _))

end Env

/-! ## 3. The split `𝔼ℰ^{G̃} = (𝔼 avg)·S·𝒦^{(3)} + 𝔼[avg·S·(𝓛-𝒦)^{(3)}]` -/

section Split

variable {d : ℕ} {sz : Sizes d} {C : FlowFM sz} {μ : Measure sz.SeqΩ}
  {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}

/-- `𝔼 avg = 𝔼 𝓛^{(1)} - m_τ` (`μ` is a probability measure). -/
private theorem ExpEtermsBGen_int_avg [IsProbabilityMeasure μ] (hrep : CltRepg C μ H₀ g' E) (n : ℕ) {u : ℝ} (hu : u < 1)
    (him : 0 < (C.m n).im) (τ : Bool) (x : Zd d (sz.L n)) :
    ∫ ω, (C.L n u (fun _ : Fin 1 => τ) (fun _ => x) ω - (if τ then C.m n else (starRingEnd ℂ) (C.m n))) ∂μ =
      (∫ ω, C.L n u (fun _ : Fin 1 => τ) (fun _ => x) ω ∂μ) - (if τ then C.m n else (starRingEnd ℂ) (C.m n)) := by
  rw [integral_sub (ExpEtermsBGen_integrable_L1 hrep n hu him τ x) (integrable_const _), integral_const]
  simp

/-- **The split** `𝔼𝓔^{G̃} = (𝔼 avg)·S·𝒦^{(3)} + 𝔼[avg·S·(𝓛-𝒦)^{(3)}]` (band `expDr_EGt_split`, `ExpEtermsB:284`): `𝓛^{(3)} = 𝒦^{(3)} + (𝓛-𝒦)^{(3)}` pointwise and linearity of the integral
(`avg` bounded and measurable, `𝓔^{G̃}` bounded and measurable). -/
private theorem ExpEtermsBGen_split [IsProbabilityMeasure μ] (hrep : CltRepg C μ H₀ g' E) (n : ℕ) {u : ℝ} (hu : u < 1)
    (him : 0 < (C.m n).im) (hcol : ∀ y : Zd d (sz.L n), ∑ x : Zd d (sz.L n), ‖C.S n x y‖ ≤ 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STExpEGtg C μ n u σ a =
      ExpEtermsBGen_EGtK C μ n u σ a + ∫ ω, ExpEtermsBGen_EGtLK C n u σ a ω ∂μ := by
  set Kpart : sz.SeqΩ → ℂ := fun ω => (((sz.W n : ℕ) : ℂ) ^ d) * ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
    ((C.L n u (fun _ : Fin 1 => σ 0) (fun _ => x) ω - (if σ 0 then C.m n else (starRingEnd ℂ) (C.m n))) * C.S n x y *
        C.K n u ![σ 0, σ 0, σ 1] ![y, a 0, a 1] +
      (C.L n u (fun _ : Fin 1 => σ 1) (fun _ => x) ω - (if σ 1 then C.m n else (starRingEnd ℂ) (C.m n))) * C.S n x y *
        C.K n u ![σ 0, σ 1, σ 1] ![a 0, y, a 1]) with hKpart
  have hpt : ∀ ω, STEGtg C n u σ a ω = Kpart ω + ExpEtermsBGen_EGtLK C n u σ a ω := by
    intro ω
    unfold STEGtg ExpEtermsBGen_EGtLK
    simp only [hKpart]
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  have hint_avg : ∀ (τ : Bool) (x : Zd d (sz.L n)),
      Integrable (fun ω => C.L n u (fun _ : Fin 1 => τ) (fun _ => x) ω - (if τ then C.m n else (starRingEnd ℂ) (C.m n))) μ :=
    fun τ x => (ExpEtermsBGen_integrable_L1 hrep n hu him τ x).sub (integrable_const _)
  have hint_K : Integrable Kpart μ := by
    refine Integrable.const_mul (integrable_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ => ?_) _
    exact (((hint_avg _ x).mul_const _).mul_const _).add (((hint_avg _ x).mul_const _).mul_const _)
  have hint_E := ExpEtermsBGen_integrable_EGt hrep n hu him hcol σ a
  have hLK : (fun ω => ExpEtermsBGen_EGtLK C n u σ a ω) = fun ω => STEGtg C n u σ a ω - Kpart ω := by
    funext ω
    rw [hpt ω]; ring
  set F : Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℂ := fun x y ω =>
    (C.L n u (fun _ : Fin 1 => σ 0) (fun _ => x) ω - (if σ 0 then C.m n else (starRingEnd ℂ) (C.m n))) * C.S n x y *
        C.K n u ![σ 0, σ 0, σ 1] ![y, a 0, a 1] +
      (C.L n u (fun _ : Fin 1 => σ 1) (fun _ => x) ω - (if σ 1 then C.m n else (starRingEnd ℂ) (C.m n))) * C.S n x y *
        C.K n u ![σ 0, σ 1, σ 1] ![a 0, y, a 1] with hF
  have hFint : ∀ x y, Integrable (F x y) μ := fun x y =>
    (((hint_avg _ x).mul_const _).mul_const _).add (((hint_avg _ x).mul_const _).mul_const _)
  have e1 : ∫ ω, (∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n), F x y ω) ∂μ =
      ∑ x : Zd d (sz.L n), ∫ ω, (∑ y : Zd d (sz.L n), F x y ω) ∂μ :=
    integral_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ => hFint x y
  have e2 : ∀ x : Zd d (sz.L n), ∫ ω, (∑ y : Zd d (sz.L n), F x y ω) ∂μ =
      ∑ y : Zd d (sz.L n), ∫ ω, F x y ω ∂μ :=
    fun x => integral_finsetSum _ fun y _ => hFint x y
  have e3 : ∀ x y : Zd d (sz.L n), ∫ ω, F x y ω ∂μ =
      ((∫ ω, C.L n u (fun _ : Fin 1 => σ 0) (fun _ => x) ω ∂μ) - (if σ 0 then C.m n else (starRingEnd ℂ) (C.m n))) *
          C.S n x y * C.K n u ![σ 0, σ 0, σ 1] ![y, a 0, a 1] +
        ((∫ ω, C.L n u (fun _ : Fin 1 => σ 1) (fun _ => x) ω ∂μ) - (if σ 1 then C.m n else (starRingEnd ℂ) (C.m n))) *
          C.S n x y * C.K n u ![σ 0, σ 1, σ 1] ![a 0, y, a 1] := by
    intro x y
    rw [hF, integral_add (((hint_avg _ x).mul_const _).mul_const _) (((hint_avg _ x).mul_const _).mul_const _),
      integral_mul_const, integral_mul_const, integral_mul_const, integral_mul_const,
      ExpEtermsBGen_int_avg hrep n hu him, ExpEtermsBGen_int_avg hrep n hu him]
  have hKint : ∫ ω, Kpart ω ∂μ = ExpEtermsBGen_EGtK C μ n u σ a := by
    have : ∫ ω, Kpart ω ∂μ =
        (((sz.W n : ℕ) : ℂ) ^ d) * ∫ ω, (∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n), F x y ω) ∂μ :=
      integral_const_mul _ _
    rw [this, e1]
    simp only [e2, e3]
    rfl
  rw [hLK, integral_sub hint_E hint_K, hKint]
  unfold STExpEGtg
  ring

end Split

/-! ## 4. The envelopes are polynomial along the flow (W-a) -/

section EnvPoly

variable {d : ℕ} {sz : Sizes d} {C : FlowFM sz}

/-- **The envelopes are polynomial** along the flow, uniformly in `u ∈ [s_n,t_n]`, `σ`, `a`, `ω` (band `expDr_env_poly`, `ExpEtermsB:416`; **W-a**): `ℰ^{LK×LK}` (the merged
`expLK_env_polyg`), `ℰ^{G̃}` and its `(𝓛-𝒦)^{(3)}` part are `≤ N⁶` eventually.  `‖m‖ ≤ N` (row 19, `K^{(1)} = m_σ`, and row 17 at `k = 1`), `‖𝓛^{(1)}‖ ≤ η⁻¹ ≤ N`, `‖𝓛^{(3)}‖ ≤ η⁻³ ≤ N³`,
`‖𝒦^{(3)}‖ ≤ N B² ≤ 4N³` (row 17 at `k = 3`, `B ≤ 2(1-u)⁻¹ ≤ 2N`): `4N⁵` and `20N⁵ ≤ N⁶` for `N ≥ 20`. -/
private theorem ExpEtermsBGen_env_poly (μ : Measure sz.SeqΩ) (hμ : IsProbabilityMeasure μ) (hsz : sz.SizeTendsto)
    {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    (hrep : CltRepg C μ H₀ g' E) {κ' δ : ℝ} (hκ' : 0 < κ') (hδ : 0 < δ) (hm : ∀ n, κ' ≤ (C.m n).im)
    {s t T : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (htT : ∀ n, t n ≤ T n) (hT1 : ∀ n, T n < 1)
    (hrange : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - T n) (hKb : STKboundgL C μ)
    (hcol : ∀ (n : ℕ) (y : Zd d (sz.L n)), ∑ x : Zd d (sz.L n), ‖C.S n x y‖ ≤ 1)
    (hK1 : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (τ : Bool) (x : Zd d (sz.L n)),
      C.K n u (fun _ : Fin 1 => τ) (fun _ => x) = if τ then C.m n else (starRingEnd ℂ) (C.m n)) :
    ∀ᶠ n in atTop, ∀ (p : STIdx2 sz s t n) (ω : sz.SeqΩ),
      ‖STELKLKg C n (p.1 : ℝ) p.2.1 p.2.2 ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (6 : ℝ) ∧
      ‖STEGtg C n (p.1 : ℝ) p.2.1 p.2.2 ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (6 : ℝ) ∧
      ‖ExpEtermsBGen_EGtLK C n (p.1 : ℝ) p.2.1 p.2.2 ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (6 : ℝ) := by
  have := hμ
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (hT1 n)
  have hELK := expLK_env_polyg C μ hμ hsz hrep hκ' hδ hm hs0 hst htT hT1 hrange hKb hcol
  have hKK : ∀ k : ℕ, 1 ≤ k → ∀ᶠ n in atTop, ∀ v : TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)),
      ‖C.K n (v.1 : ℝ) v.2.1 v.2.2‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * sz.Bctl n (v.1 : ℝ) ^ (k - 1) := by
    intro k hk
    exact (st6_prec_det_iffg sz μ hμ hsz (V := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p => ‖C.K n (p.1 : ℝ) p.2.1 p.2.2‖) (fun n p => (sz.Bctl n (p.1 : ℝ)) ^ (k - 1))).1
      (stKbound_timeIccgL sz C μ hsz hKb s t hs0 hst ht1 k hk) 1 one_pos
  filter_upwards [ExpEtermsAGen_ctrl hsz hκ' hδ hm htT hrange, hELK, hKK 3 (by norm_num), hKK 1 le_rfl, hK1]
    with n ⟨hN20, hc⟩ hELKn hK3n hK1n hK1m
  rintro ⟨⟨u, hu⟩, σ, a⟩ ω
  obtain ⟨h0, hη, hy⟩ := hc u hu.2
  have hu1 : u < 1 := by linarith
  have hu0 : 0 ≤ u := (hs0 n).trans hu.1
  have hm0 : 0 < (C.m n).im := hκ'.trans_le (hm n)
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have h6 : N ^ (6 : ℝ) = N ^ 6 := by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hη0 : 0 ≤ (etaOf (C.m n) u)⁻¹ := inv_nonneg.2 (mul_pos h0 hm0).le
  have hN5 : ∀ c : ℝ, 0 ≤ c → c ≤ 20 → c * N ^ 5 ≤ N ^ 6 := by
    intro c hc0 hc20
    have h5 : 0 ≤ N ^ 5 := by positivity
    nlinarith
  have hWL : ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d = N := by
    rw [hNdef]; simp only [Sizes.size, Nat.cast_pow, Nat.cast_mul, mul_pow]
  -- `‖m‖ ≤ N`
  have hmN : ‖C.m n‖ ≤ N := by
    have hs1 : s n < 1 := (hst n).trans_lt (ht1 n)
    have h := hK1n (⟨s n, le_rfl, hst n⟩, fun _ => true, fun _ => 0)
    simp only [Nat.sub_self, pow_zero, mul_one, Real.rpow_one] at h
    have hk := hK1m (s n) (hs0 n) hs1 true 0
    simp only [ite_true] at hk
    rw [hk] at h
    exact h
  have hB : sz.Bctl n u ≤ 2 * N := by
    have := ExpEtermsAGen_Bctl_le_two sz n hu1
    linarith
  have hB0 : 0 ≤ sz.Bctl n u := (STBctl_pos sz n hu1).le
  have hK3 : ∀ (σ' : Fin 3 → Bool) (b : Fin 3 → Zd d (sz.L n)), ‖C.K n u σ' b‖ ≤ 4 * N ^ 3 := by
    intro σ' b
    have h := hK3n (⟨u, hu⟩, σ', b)
    simp only [Nat.reduceSub, Real.rpow_one] at h
    refine h.trans ?_
    calc N * sz.Bctl n u ^ 2 ≤ N * (2 * N) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB0 hB 2) (by linarith)
      _ = 4 * N ^ 3 := by ring
  have hx3 : (etaOf (C.m n) u)⁻¹ ^ 3 ≤ N ^ 3 := pow_le_pow_left₀ hη0 hη 3
  have h1 : (etaOf (C.m n) u)⁻¹ + N ≤ 2 * N := by linarith
  refine ⟨?_, ?_, ?_⟩
  · exact hELKn (⟨u, hu⟩, σ, a) ω
  · -- `ℰ^{G̃}`
    rw [h6]
    refine (ExpEtermsBGen_envEGt hrep n hu1 hm0 hmN (hcol n) σ a ω).trans ?_
    rw [hWL]
    have h13 : ((etaOf (C.m n) u)⁻¹ + N) * (etaOf (C.m n) u)⁻¹ ^ 3 ≤ (2 * N) * N ^ 3 :=
      mul_le_mul h1 hx3 (by positivity) (by positivity)
    calc 2 * N * (((etaOf (C.m n) u)⁻¹ + N) * (etaOf (C.m n) u)⁻¹ ^ 3) ≤ 2 * N * ((2 * N) * N ^ 3) :=
          mul_le_mul_of_nonneg_left h13 (by linarith)
      _ = 4 * N ^ 5 := by ring
      _ ≤ N ^ 6 := hN5 4 (by norm_num) (by norm_num)
  · -- the `(𝓛-𝒦)^{(3)}` part
    rw [h6]
    have hLK3 : ∀ (σ' : Fin 3 → Bool) (b : Fin 3 → Zd d (sz.L n)),
        ‖C.L n u σ' b ω - C.K n u σ' b‖ ≤ N ^ 3 + 4 * N ^ 3 := fun σ' b =>
      (norm_sub_le _ _).trans (add_le_add ((ExpEtermsAGen_norm_L_le hrep n hu1 hm0 (k := 2) σ' b ω).trans hx3) (hK3 σ' b))
    unfold ExpEtermsBGen_EGtLK
    refine (ExpEtermsBGen_cuts_le C n (hcol n) _ _ _ _ (fun x => ExpEtermsBGen_avg_le hrep n hu1 hm0 hmN (σ 0) x ω)
      (fun x => ExpEtermsBGen_avg_le hrep n hu1 hm0 hmN (σ 1) x ω) (fun y => hLK3 _ _) (fun y => hLK3 _ _)).trans ?_
    rw [hWL]
    calc 2 * N * (((etaOf (C.m n) u)⁻¹ + N) * (N ^ 3 + 4 * N ^ 3)) ≤ 2 * N * ((2 * N) * (N ^ 3 + 4 * N ^ 3)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (by positivity)) (by linarith)
      _ = 20 * N ^ 5 := by ring
      _ ≤ N ^ 6 := hN5 20 (by norm_num) (by norm_num)

end EnvPoly

/-! ## 5. `≺ → 𝔼` and the three estimates of regime (iv) -/

section Prec

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- **`≺ → 𝔼`** (generic; band `expDr_expect`, `ExpEtermsB:553`) at a probability law: from the `≺` of `‖X_v‖` against a deterministic `R`, a polynomial envelope `N^{Kenv}` and a polynomial
floor `R ≥ N^{-Kf}`: `𝔼‖X_v‖ ≤ N^{τ/2} R + N^{Kenv} P(S_n)`, `P(S_n) ≤ N^{-(|Kenv|+|Kf|+1)}`; the deterministic `PrecL` through `st6_prec_det_iffg`. -/
private theorem ExpEtermsBGen_expect (hμ : IsProbabilityMeasure μ) {V : ℕ → Type} (X : ∀ n, V n → sz.SeqΩ → ℂ)
    (R : ∀ n, V n → ℝ) {Kenv Kf : ℝ} (hsz : sz.SizeTendsto)
    (henv : ∀ᶠ n in atTop, ∀ v ω, ‖X n v ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ Kenv)
    (hfloor : ∀ᶠ n in atTop, ∀ v, ((sz.size n : ℕ) : ℝ) ^ (-Kf) ≤ R n v)
    (hprec : PrecL sz μ (U := V) (fun n v ω => ‖X n v ω‖) (fun n v _ => R n v)) :
    PrecL sz μ (U := V) (fun n v _ => ‖∫ ω, X n v ω ∂μ‖) (fun n v _ => R n v) := by
  have := hμ
  refine (st6_prec_det_iffg sz μ hμ hsz (fun n v => ‖∫ ω, X n v ω ∂μ‖) R).2 ?_
  intro τ hτ
  have hτ2 : 0 < τ / 2 := by positivity
  have hDp : 0 < |Kenv| + |Kf| + 1 := by positivity
  have hC : ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop hτ2).comp hsz).eventually (eventually_ge_atTop 2)
  filter_upwards [hprec (τ / 2) hτ2 (|Kenv| + |Kf| + 1) hDp, henv, hfloor, hC,
    hsz.eventually (eventually_ge_atTop 1)] with n hP hEnv hFl hN2 hN1
  intro v
  have hN : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hN1
  have hNpos : 0 < ((sz.size n : ℕ) : ℝ) := by linarith
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hR0 : 0 ≤ R n v := (Real.rpow_nonneg hNpos.le _).trans (hFl v)
  set S : Set sz.SeqΩ := badSetAt sz.size (fun n v ω => ‖X n v ω‖) (fun n v _ => R n v) (τ / 2) n with hS
  have hPS : (μ S).toReal ≤ N ^ (-(|Kenv| + |Kf| + 1)) :=
    ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg hNpos.le _) hP
  have hin : ∀ ω, ω ∉ S → ‖X n v ω‖ ≤ N ^ (τ / 2) * R n v := by
    intro ω hω
    by_contra hc
    exact hω ⟨v, lt_of_not_ge hc⟩
  have hfm := expDr_first_moment (P := μ) (f := fun ω => X n v ω) (S := S)
    (c := N ^ (τ / 2) * R n v) (B := N ^ Kenv) (mul_nonneg (Real.rpow_nonneg hNpos.le _) hR0)
    (fun ω => hEnv v ω) hin
  have htail : N ^ Kenv * (μ S).toReal ≤ R n v := by
    calc N ^ Kenv * (μ S).toReal ≤ N ^ Kenv * N ^ (-(|Kenv| + |Kf| + 1)) :=
          mul_le_mul_of_nonneg_left hPS (Real.rpow_nonneg hNpos.le _)
      _ = N ^ (Kenv + -(|Kenv| + |Kf| + 1)) := (Real.rpow_add hNpos _ _).symm
      _ ≤ N ^ (-Kf) := by
          refine Real.rpow_le_rpow_of_exponent_le hN ?_
          have h1 := le_abs_self Kenv
          have h2 := le_abs_self Kf
          linarith
      _ ≤ R n v := hFl v
  have hX2 : 0 ≤ N ^ (τ / 2) := Real.rpow_nonneg hNpos.le _
  calc ‖∫ ω, X n v ω ∂μ‖ ≤ ∫ ω, ‖X n v ω‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ N ^ (τ / 2) * R n v + N ^ Kenv * (μ S).toReal := hfm
    _ ≤ N ^ (τ / 2) * R n v + R n v := add_le_add le_rfl htail
    _ ≤ N ^ (τ / 2) * R n v + N ^ (τ / 2) * R n v := by
        have : R n v ≤ N ^ (τ / 2) * R n v := by nlinarith
        linarith
    _ ≤ N ^ (τ / 2) * (N ^ (τ / 2) * R n v) := by
        have h3 : 0 ≤ N ^ (τ / 2) * R n v := mul_nonneg hX2 hR0
        linarith [mul_le_mul_of_nonneg_right hN2 h3]
    _ = N ^ τ * R n v := by
        rw [← mul_assoc, ← Real.rpow_add hNpos]; congr 2; ring

/-- **`ℰ^{LK×LK}` in regime (iv), random, no regime used** (band `expDr_LK_prec`, `ExpEtermsB:608`): off the failure event of `STLKUgL … 2` at `τ/2`, both factors are `≤ N^{τ/2}B²` for every
index, so `‖ℰ‖ ≤ W^d L^d N^τ B⁴ = N^τ · N B⁴` (`expLK_window_leg` with `M = f = N^{τ/2}B²`).  No grid lift (`STLKUgL` is uniform in `u`). -/
private theorem ExpEtermsBGen_LK_prec (hsz : sz.SizeTendsto) {s t : ℕ → ℝ}
    (hcol : ∀ (n : ℕ) (y : Zd d (sz.L n)), ∑ x : Zd d (sz.L n), ‖C.S n x y‖ ≤ 1) (hLKU : STLKUgL C μ s t) :
    PrecL sz μ (U := STIdx2 sz s t)
      (fun n p ω => ‖STELKLKg C n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => ((sz.size n : ℕ) : ℝ) * (sz.Bctl n (p.1 : ℝ)) ^ 4) := by
  refine StochDomAt.of_subset (hLKU 2 (by norm_num)) ?_
  intro τ hτ
  refine ⟨τ / 2, by positivity, ?_⟩
  filter_upwards [hsz.eventually (eventually_ge_atTop 1)] with n hN1 ω hω
  by_contra hcon
  have hN : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hN1
  have hNpos : 0 < ((sz.size n : ℕ) : ℝ) := by linarith
  have hg : ∀ p : STIdx2 sz s t n,
      ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1 p.2.2‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * sz.Bctl n (p.1 : ℝ) ^ 2 := by
    intro p
    by_contra hc
    exact hcon ⟨p, lt_of_not_ge hc⟩
  obtain ⟨p, hp⟩ := hω
  obtain ⟨⟨u, hu⟩, σ, a⟩ := p
  have key := expLK_window_leg C n u ω σ a
    (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * sz.Bctl n u ^ 2) (fun _ => ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * sz.Bctl n u ^ 2)
    (hcol n) (fun x => hg (⟨u, hu⟩, σ, ![x, a 1])) (fun y => hg (⟨u, hu⟩, σ, ![a 0, y]))
  have hsum : ∑ _y : Zd d (sz.L n), ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * sz.Bctl n u ^ 2 =
      ((sz.L n : ℕ) : ℝ) ^ d * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * sz.Bctl n u ^ 2) := by
    rw [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
    push_cast; ring
  rw [hsum] at key
  have hWL : ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d = ((sz.size n : ℕ) : ℝ) := by
    simp only [Sizes.size, Nat.cast_pow, Nat.cast_mul, mul_pow]
  have hXX : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) = ((sz.size n : ℕ) : ℝ) ^ τ := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  have hle : ‖STELKLKg C n u σ a ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (((sz.size n : ℕ) : ℝ) * sz.Bctl n u ^ 4) := by
    refine key.trans (le_of_eq ?_)
    rw [← hXX, ← hWL]
    ring
  exact absurd hp (not_lt.2 hle)

/-- **`X_B` (the `(𝓛-𝒦)^{(3)}` part of `ℰ^{G̃}`), random** (band `expDr_EGtLK_prec`, `ExpEtermsB:648`): `STLKUgL … 1` (`avg = (𝓛-𝒦)^{(1)}`, from `K^{(1)} = m_σ`, family row 19) and `STLKUgL … 3` at the
cut indices, `of_subset_union`, `τ' = τ/3`: `‖X_B‖ ≤ 2 N^{2τ/3} N B⁴ ≤ N^τ · N B⁴`. -/
private theorem ExpEtermsBGen_EGtLK_prec (hsz : sz.SizeTendsto) {s t : ℕ → ℝ}
    (hcol : ∀ (n : ℕ) (y : Zd d (sz.L n)), ∑ x : Zd d (sz.L n), ‖C.S n x y‖ ≤ 1)
    (hK1 : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (τ : Bool) (x : Zd d (sz.L n)),
      C.K n u (fun _ : Fin 1 => τ) (fun _ => x) = if τ then C.m n else (starRingEnd ℂ) (C.m n))
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hLKU : STLKUgL C μ s t) :
    PrecL sz μ (U := STIdx2 sz s t)
      (fun n p ω => ‖ExpEtermsBGen_EGtLK C n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => ((sz.size n : ℕ) : ℝ) * (sz.Bctl n (p.1 : ℝ)) ^ 4) := by
  refine StochDomAt.of_subset_union (tendsto_size sz hsz) (hLKU 1 le_rfl) (hLKU 3 (by norm_num)) ?_
  intro τ hτ
  refine ⟨τ / 3, by positivity, ?_⟩
  have hτ3 : 0 < τ / 3 := by positivity
  have hC : ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 3) :=
    ((tendsto_rpow_atTop hτ3).comp hsz).eventually (eventually_ge_atTop 2)
  filter_upwards [hC, hsz.eventually (eventually_ge_atTop 1), hK1] with n hN2 hN1 hK1n ω hω
  by_contra hcon
  simp only [Set.mem_union, not_or] at hcon
  obtain ⟨hn1, hn3⟩ := hcon
  have hN : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hN1
  have hNpos : 0 < ((sz.size n : ℕ) : ℝ) := by linarith
  have hg1 : ∀ p : TimeIcc s t n × (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n)),
      ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1 p.2.2‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 3) * sz.Bctl n (p.1 : ℝ) ^ 1 := by
    intro p
    by_contra hc
    exact hn1 ⟨p, lt_of_not_ge hc⟩
  have hg3 : ∀ p : TimeIcc s t n × (Fin 3 → Bool) × (Fin 3 → Zd d (sz.L n)),
      ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1 p.2.2‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 3) * sz.Bctl n (p.1 : ℝ) ^ 3 := by
    intro p
    by_contra hc
    exact hn3 ⟨p, lt_of_not_ge hc⟩
  obtain ⟨p, hp⟩ := hω
  obtain ⟨⟨u, hu⟩, σ, a⟩ := p
  have hu0 : 0 ≤ u := (hs0 n).trans hu.1
  have hu1 : u < 1 := hu.2.trans_lt (ht1 n)
  have hav : ∀ (τ' : Bool) (x : Zd d (sz.L n)),
      ‖C.L n u (fun _ : Fin 1 => τ') (fun _ => x) ω - (if τ' then C.m n else (starRingEnd ℂ) (C.m n))‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 3) * sz.Bctl n u ^ 1 := by
    intro τ' x
    have h := hg1 (⟨u, hu⟩, fun _ => τ', fun _ => x)
    rw [hK1n u hu0 hu1 τ' x] at h
    exact h
  have key := ExpEtermsBGen_cuts_le C n (hcol n)
    (fun x => C.L n u (fun _ : Fin 1 => σ 0) (fun _ => x) ω - (if σ 0 then C.m n else (starRingEnd ℂ) (C.m n)))
    (fun x => C.L n u (fun _ : Fin 1 => σ 1) (fun _ => x) ω - (if σ 1 then C.m n else (starRingEnd ℂ) (C.m n)))
    (fun y => C.L n u ![σ 0, σ 0, σ 1] ![y, a 0, a 1] ω - C.K n u ![σ 0, σ 0, σ 1] ![y, a 0, a 1])
    (fun y => C.L n u ![σ 0, σ 1, σ 1] ![a 0, y, a 1] ω - C.K n u ![σ 0, σ 1, σ 1] ![a 0, y, a 1])
    (α := ((sz.size n : ℕ) : ℝ) ^ (τ / 3) * sz.Bctl n u ^ 1) (β := ((sz.size n : ℕ) : ℝ) ^ (τ / 3) * sz.Bctl n u ^ 3)
    (fun x => hav (σ 0) x) (fun x => hav (σ 1) x)
    (fun y => hg3 (⟨u, hu⟩, ![σ 0, σ 0, σ 1], ![y, a 0, a 1]))
    (fun y => hg3 (⟨u, hu⟩, ![σ 0, σ 1, σ 1], ![a 0, y, a 1]))
  have hWL : ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d = ((sz.size n : ℕ) : ℝ) := by
    simp only [Sizes.size, Nat.cast_pow, Nat.cast_mul, mul_pow]
  have hXXX : ((sz.size n : ℕ) : ℝ) ^ (τ / 3) * ((sz.size n : ℕ) : ℝ) ^ (τ / 3) *
      ((sz.size n : ℕ) : ℝ) ^ (τ / 3) = ((sz.size n : ℕ) : ℝ) ^ τ := by
    rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]; congr 1; ring
  have hX0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 3) := Real.rpow_nonneg hNpos.le _
  have hNB : 0 ≤ ((sz.size n : ℕ) : ℝ) * sz.Bctl n u ^ 4 := by
    have := (STBctl_pos sz n hu1).le
    positivity
  have hle : ‖ExpEtermsBGen_EGtLK C n u σ a ω‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ τ * (((sz.size n : ℕ) : ℝ) * sz.Bctl n u ^ 4) := by
    unfold ExpEtermsBGen_EGtLK
    refine key.trans ?_
    rw [hWL, ← hXXX]
    have h2 : 2 * (((sz.size n : ℕ) : ℝ) ^ (τ / 3) * ((sz.size n : ℕ) : ℝ) ^ (τ / 3)) ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 3) * ((sz.size n : ℕ) : ℝ) ^ (τ / 3) * ((sz.size n : ℕ) : ℝ) ^ (τ / 3) := by
      have := mul_nonneg hX0 hX0
      nlinarith
    calc 2 * ((sz.size n : ℕ) : ℝ) * ((((sz.size n : ℕ) : ℝ) ^ (τ / 3) * sz.Bctl n u ^ 1) *
          (((sz.size n : ℕ) : ℝ) ^ (τ / 3) * sz.Bctl n u ^ 3))
        = 2 * (((sz.size n : ℕ) : ℝ) ^ (τ / 3) * ((sz.size n : ℕ) : ℝ) ^ (τ / 3)) *
          (((sz.size n : ℕ) : ℝ) * sz.Bctl n u ^ 4) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 hNB
  exact absurd hp (not_lt.2 hle)

/-- **The deterministic part of `𝔼ℰ^{G̃}`** (band `expDr_EGtK_prec`, `ExpEtermsB:723`; **target 3**): `(res_ELK_n=1)` (`STExpAvgUgL`, `|𝔼 𝓛^{(1)} - m| ≺ B²`) and `(eq:bcal_k)` at `k = 3` uniformly in `u`
(`stKbound_timeIccgL`, `|𝒦^{(3)}| ≺ B²`), both deterministic (`st6_prec_det_iffg`), and the two cuts: `|A| ≤ 2 N (N^{τ/4}B²)² ≤ N^τ · N B⁴`.  The per-flow average is `STExpAvgUgL`
(V1L-C1: no global `STImproveExpAvergL`). -/
theorem expDr_EGtK_precg (hμ : IsProbabilityMeasure μ) (hsz : sz.SizeTendsto) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n)
    (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hKb : STKboundgL C μ)
    (hcol : ∀ (n : ℕ) (y : Zd d (sz.L n)), ∑ x : Zd d (sz.L n), ‖C.S n x y‖ ≤ 1) (hAvg : STExpAvgUgL C μ s t) :
    PrecL sz μ (U := STIdx2 sz s t)
      (fun n p _ => ‖ExpEtermsBGen_EGtK C μ n (p.1 : ℝ) p.2.1 p.2.2‖)
      (fun n p _ => ((sz.size n : ℕ) : ℝ) * (sz.Bctl n (p.1 : ℝ)) ^ 4) := by
  refine (st6_prec_det_iffg sz μ hμ hsz (V := STIdx2 sz s t)
    (fun n p => ‖ExpEtermsBGen_EGtK C μ n (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p => ((sz.size n : ℕ) : ℝ) * (sz.Bctl n (p.1 : ℝ)) ^ 4)).2 ?_
  intro τ hτ
  have hτ4 : 0 < τ / 4 := by positivity
  have hA := (st6_prec_det_iffg sz μ hμ hsz (V := fun n => TimeIcc s t n × Bool × Zd d (sz.L n))
    (fun n p => ‖(∫ ω, C.L n (p.1 : ℝ) (fun _ : Fin 1 => p.2.1) (fun _ => p.2.2) ω ∂μ) -
      (if p.2.1 then C.m n else (starRingEnd ℂ) (C.m n))‖)
    (fun n p => (sz.Bctl n (p.1 : ℝ)) ^ 2)).1 hAvg (τ / 4) hτ4
  have hK := (st6_prec_det_iffg sz μ hμ hsz (V := fun n => TimeIcc s t n × (Fin 3 → Bool) × (Fin 3 → Zd d (sz.L n)))
    (fun n p => ‖C.K n (p.1 : ℝ) p.2.1 p.2.2‖) (fun n p => (sz.Bctl n (p.1 : ℝ)) ^ (3 - 1))).1
    (stKbound_timeIccgL sz C μ hsz hKb s t hs0 hst ht1 3 (by norm_num)) (τ / 4) hτ4
  have hτ2 : 0 < τ / 2 := by positivity
  have hC : ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop hτ2).comp hsz).eventually (eventually_ge_atTop 2)
  filter_upwards [hA, hK, hC, hsz.eventually (eventually_ge_atTop 1)] with n hAn hKn hN2 hN1
  rintro ⟨⟨u, hu⟩, σ, a⟩
  have hN : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hN1
  have hNpos : 0 < ((sz.size n : ℕ) : ℝ) := by linarith
  have hu1 : u < 1 := hu.2.trans_lt (ht1 n)
  have hK3 : ∀ y : Zd d (sz.L n) → Fin 3 → Zd d (sz.L n), True := fun _ => trivial
  have key := ExpEtermsBGen_cuts_le C n (hcol n)
    (fun x => (∫ ω, C.L n u (fun _ : Fin 1 => σ 0) (fun _ => x) ω ∂μ) - (if σ 0 then C.m n else (starRingEnd ℂ) (C.m n)))
    (fun x => (∫ ω, C.L n u (fun _ : Fin 1 => σ 1) (fun _ => x) ω ∂μ) - (if σ 1 then C.m n else (starRingEnd ℂ) (C.m n)))
    (fun y => C.K n u ![σ 0, σ 0, σ 1] ![y, a 0, a 1]) (fun y => C.K n u ![σ 0, σ 1, σ 1] ![a 0, y, a 1])
    (α := ((sz.size n : ℕ) : ℝ) ^ (τ / 4) * sz.Bctl n u ^ 2) (β := ((sz.size n : ℕ) : ℝ) ^ (τ / 4) * sz.Bctl n u ^ 2)
    (fun x => hAn (⟨u, hu⟩, σ 0, x)) (fun x => hAn (⟨u, hu⟩, σ 1, x))
    (fun y => hKn (⟨u, hu⟩, ![σ 0, σ 0, σ 1], ![y, a 0, a 1]))
    (fun y => hKn (⟨u, hu⟩, ![σ 0, σ 1, σ 1], ![a 0, y, a 1]))
  have hWL : ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d = ((sz.size n : ℕ) : ℝ) := by
    simp only [Sizes.size, Nat.cast_pow, Nat.cast_mul, mul_pow]
  have hXX : ((sz.size n : ℕ) : ℝ) ^ (τ / 4) * ((sz.size n : ℕ) : ℝ) ^ (τ / 4) = ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  have hXX2 : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) = ((sz.size n : ℕ) : ℝ) ^ τ := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  have hX0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg hNpos.le _
  have hNB : 0 ≤ ((sz.size n : ℕ) : ℝ) * sz.Bctl n u ^ 4 := by
    have := (STBctl_pos sz n hu1).le
    positivity
  unfold ExpEtermsBGen_EGtK
  refine key.trans ?_
  rw [hWL]
  have h2 : 2 * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    nlinarith
  calc 2 * ((sz.size n : ℕ) : ℝ) * ((((sz.size n : ℕ) : ℝ) ^ (τ / 4) * sz.Bctl n u ^ 2) *
        (((sz.size n : ℕ) : ℝ) ^ (τ / 4) * sz.Bctl n u ^ 2))
      = 2 * (((sz.size n : ℕ) : ℝ) ^ (τ / 4) * ((sz.size n : ℕ) : ℝ) ^ (τ / 4)) *
        (((sz.size n : ℕ) : ℝ) * sz.Bctl n u ^ 4) := by ring
    _ = 2 * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (((sz.size n : ℕ) : ℝ) * sz.Bctl n u ^ 4) := by rw [hXX]
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (((sz.size n : ℕ) : ℝ) * sz.Bctl n u ^ 4) :=
        mul_le_mul_of_nonneg_right h2 hNB
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * (((sz.size n : ℕ) : ℝ) * sz.Bctl n u ^ 4) := by rw [hXX2]

end Prec

/-! ## 6. Regime (iv): the conclusion from the premises it uses, and the pin (target 4) -/

/-- **(iv) assembly** (band `STExpDriftLoConcl_of_LKU`, `ExpEtermsB:818`; `(eq:Exp(L-K)2)`, `(eq:ExpLWn=2_smalleta)`) per carrier: `D_u = 𝔼ℰ^{LK×LK} + A + 𝔼 X_B`
(`ExpEtermsBGen_split`); `ExpEtermsBGen_expect` (`Kenv = 6` from `ExpEtermsBGen_env_poly`, `Kf = 3` from the floor `B ≥ N⁻¹`) turns `ExpEtermsBGen_LK_prec`, `ExpEtermsBGen_EGtLK_prec` into
deterministic bounds `≺ N B⁴`, `expDr_EGtK_precg` is already deterministic; then `N B⁴ ≤ 16 R_u` (`expDr_Bctl_le_IV`, `1-u ≤ 1-s`).  The regime `STReg5IV` is used only there.
Family data of the carrier: `CltRepg` with `κ' ≤ Im m` and `N^{-1+δ} ≤ 1 - T0` (row 9'), `STKboundgL` (row 17), the column sums of `C.S` (row 20), `K^{(1)} = m_σ` (row 19). -/
theorem STExpDriftLoConclgL_of_LKU {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (hμ : IsProbabilityMeasure μ)
    {𝔠 𝔡 : ℝ} (hadm : sz.Admissible 𝔠 𝔡)
    {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    (hrep : CltRepg C μ H₀ g' E) {κ' δ : ℝ} (hκ' : 0 < κ') (hδ : 0 < δ) (hm : ∀ n, κ' ≤ (C.m n).im)
    {s t T : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (htT : ∀ n, t n ≤ T n) (hT1 : ∀ n, T n < 1)
    (hrange : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - T n) (hKb : STKboundgL C μ)
    (hcol : ∀ (n : ℕ) (y : Zd d (sz.L n)), ∑ x : Zd d (sz.L n), ‖C.S n x y‖ ≤ 1)
    (hK1 : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (τ : Bool) (x : Zd d (sz.L n)),
      C.K n u (fun _ : Fin 1 => τ) (fun _ => x) = if τ then C.m n else (starRingEnd ℂ) (C.m n))
    (hR : STReg5IV sz s t) (hLKU : STLKUgL C μ s t) (hAvg : STExpAvgUgL C μ s t) :
    STExpDriftLoConclgL C μ s t := by
  have := hμ
  have hsz := hadm.2.2.1
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (hT1 n)
  have henv := ExpEtermsBGen_env_poly μ hμ hsz hrep hκ' hδ hm hs0 hst htT hT1 hrange hKb hcol hK1
  have hfloor := expDr_floor sz hsz hs0 ht1
  have P1 := ExpEtermsBGen_expect μ hμ (V := STIdx2 sz s t)
    (fun n p ω => STELKLKg C n (p.1 : ℝ) p.2.1 p.2.2 ω)
    (fun n p => ((sz.size n : ℕ) : ℝ) * (sz.Bctl n (p.1 : ℝ)) ^ 4) (Kenv := 6) (Kf := 3) hsz
    (henv.mono fun n h p ω => (h p ω).1) hfloor (ExpEtermsBGen_LK_prec C μ hsz hcol hLKU)
  have P3 := ExpEtermsBGen_expect μ hμ (V := STIdx2 sz s t)
    (fun n p ω => ExpEtermsBGen_EGtLK C n (p.1 : ℝ) p.2.1 p.2.2 ω)
    (fun n p => ((sz.size n : ℕ) : ℝ) * (sz.Bctl n (p.1 : ℝ)) ^ 4) (Kenv := 6) (Kf := 3) hsz
    (henv.mono fun n h p ω => (h p ω).2.2) hfloor (ExpEtermsBGen_EGtLK_prec C μ hsz hcol hK1 hs0 hst ht1 hLKU)
  have P2 := expDr_EGtK_precg C μ hμ hsz hs0 hst ht1 hKb hcol hAvg
  have D1 := (st6_prec_det_iffg sz μ hμ hsz (V := STIdx2 sz s t)
    (fun n p => ‖∫ ω, STELKLKg C n (p.1 : ℝ) p.2.1 p.2.2 ω ∂μ‖)
    (fun n p => ((sz.size n : ℕ) : ℝ) * (sz.Bctl n (p.1 : ℝ)) ^ 4)).1 P1
  have D3 := (st6_prec_det_iffg sz μ hμ hsz (V := STIdx2 sz s t)
    (fun n p => ‖∫ ω, ExpEtermsBGen_EGtLK C n (p.1 : ℝ) p.2.1 p.2.2 ω ∂μ‖)
    (fun n p => ((sz.size n : ℕ) : ℝ) * (sz.Bctl n (p.1 : ℝ)) ^ 4)).1 P3
  have D2 := (st6_prec_det_iffg sz μ hμ hsz (V := STIdx2 sz s t)
    (fun n p => ‖ExpEtermsBGen_EGtK C μ n (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p => ((sz.size n : ℕ) : ℝ) * (sz.Bctl n (p.1 : ℝ)) ^ 4)).1 P2
  unfold STExpDriftLoConclgL
  refine (st6_prec_det_iffg sz μ hμ hsz (V := STIdx2 sz s t)
    (fun n p => ‖STExpDriftg C μ n (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p => (1 - (p.1 : ℝ))⁻¹ * ((((sz.size n : ℕ) : ℝ) * (1 - (p.1 : ℝ)))⁻¹) ^ 3)).2 ?_
  intro τ hτ
  have hτ2 : 0 < τ / 2 := by positivity
  have hC : ∀ᶠ n in atTop, (48 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop hτ2).comp hsz).eventually (eventually_ge_atTop 48)
  filter_upwards [D1 (τ / 2) hτ2, D2 (τ / 2) hτ2, D3 (τ / 2) hτ2, hC,
    hsz.eventually (eventually_ge_atTop 1)] with n h1 h2 h3 hN48 hN1
  intro p
  have hNpos : 0 < ((sz.size n : ℕ) : ℝ) := by linarith
  obtain ⟨⟨u, hu⟩, σ, a⟩ := p
  have hu1 : u < 1 := hu.2.trans_lt (ht1 n)
  have hu0 : 0 ≤ u := (hs0 n).trans hu.1
  have h1u : 0 < 1 - u := by linarith
  have him : 0 < (C.m n).im := hκ'.trans_le (hm n)
  have hBpos : 0 < sz.Bctl n u := STBctl_pos sz n hu1
  have hreg : 1 - u ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d := by
    have := hR n
    linarith [hu.1]
  have hB := expDr_Bctl_le_IV sz n hu1 hreg
  -- `N B⁴ ≤ 16 R_u`
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hw : N * (sz.Bctl n u) ^ 4 ≤ 16 * ((1 - u)⁻¹ * ((N * (1 - u))⁻¹) ^ 3) := by
    calc N * (sz.Bctl n u) ^ 4 ≤ N * (2 * (N * (1 - u))⁻¹) ^ 4 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hBpos.le hB 4) hNpos.le
      _ = 16 * ((1 - u)⁻¹ * ((N * (1 - u))⁻¹) ^ 3) := by
          field_simp
          ring
  have hRu : 0 ≤ (1 - u)⁻¹ * ((N * (1 - u))⁻¹) ^ 3 := by positivity
  have hX0 : 0 ≤ N ^ (τ / 2) := Real.rpow_nonneg hNpos.le _
  have hsplit := ExpEtermsBGen_split hrep n hu1 him (hcol n) σ a
  have e1 := h1 (⟨u, hu⟩, σ, a)
  have e2 := h2 (⟨u, hu⟩, σ, a)
  have e3 := h3 (⟨u, hu⟩, σ, a)
  have hXX : N ^ (τ / 2) * N ^ (τ / 2) = N ^ τ := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  calc ‖STExpDriftg C μ n u σ a‖
      = ‖(∫ ω, STELKLKg C n u σ a ω ∂μ) + (ExpEtermsBGen_EGtK C μ n u σ a +
          ∫ ω, ExpEtermsBGen_EGtLK C n u σ a ω ∂μ)‖ := by
        unfold STExpDriftg STExpELKLKg
        rw [hsplit]
    _ ≤ ‖∫ ω, STELKLKg C n u σ a ω ∂μ‖ + (‖ExpEtermsBGen_EGtK C μ n u σ a‖ +
          ‖∫ ω, ExpEtermsBGen_EGtLK C n u σ a ω ∂μ‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ N ^ (τ / 2) * (N * sz.Bctl n u ^ 4) + (N ^ (τ / 2) * (N * sz.Bctl n u ^ 4) +
          N ^ (τ / 2) * (N * sz.Bctl n u ^ 4)) := add_le_add e1 (add_le_add e2 e3)
    _ = 3 * N ^ (τ / 2) * (N * sz.Bctl n u ^ 4) := by ring
    _ ≤ 3 * N ^ (τ / 2) * (16 * ((1 - u)⁻¹ * ((N * (1 - u))⁻¹) ^ 3)) :=
        mul_le_mul_of_nonneg_left hw (by positivity)
    _ = (48 * N ^ (τ / 2)) * ((1 - u)⁻¹ * ((N * (1 - u))⁻¹) ^ 3) := by ring
    _ ≤ (N ^ (τ / 2) * N ^ (τ / 2)) * ((1 - u)⁻¹ * ((N * (1 - u))⁻¹) ^ 3) :=
        mul_le_mul_of_nonneg_right (by nlinarith) hRu
    _ = N ^ τ * ((1 - u)⁻¹ * ((N * (1 - u))⁻¹) ^ 3) := by rw [hXX]

/-- **`(eq:Exp(L-K)2)` and `(eq:ExpLWn=2_smalleta)` over the carrier family** (band `stExpDriftLo_holds`, `ExpEtermsB:901`): the pin `STExpDriftLogL` of `Chain/Step6Gen`, proved with `𝔠_d = 1/100`.
Family premises (ticket table): the laws (row 1), `Step2EventsGen_Flow` (row 2), the class `IniTermGen_CltFlow` (row 9': `κ'`, `δ` before `(𝔠, sz, z)`, `CltRepg`), `STKboundgL` (row 17),
the column sums of `C.S` (row 20) and `K^{(1)} = m_σ` (row 19, first conjunct of `Step2IterGen_OneLoop`; needed for `avg = (𝓛-𝒦)^{(1)}` and `‖m‖ ≤ N`), each guarded by `0 < κ → Flow`.
Premises of the pin used: `0 ≤ s`, `s < t` (as `≤`), `t ≤ T0`, `STReg5IV`, `STLKUgL`, `STExpAvgUgL`; unused: `STLKgL`, `STDecaygL`, `STExp2gL`, `STConStInd`, `STStep2CoregL`, `STLmaxUgL`,
`STGdecayWgL … 0`. -/
theorem stExpDriftLogL_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hμ : ∀ sz : Sizes d, IsProbabilityMeasure (law sz))
    (hFl : Step2EventsGen_Flow d Flow T0) (hClt : IniTermGen_CltFlow d law Flow mk T0)
    (hK : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → STKboundgL (mk sz z) (law sz))
    (hS : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ (n : ℕ) (y : Zd d (sz.L n)), ∑ x : Zd d (sz.L n), ‖(mk sz z).S n x y‖ ≤ 1)
    (hK1 : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (τ : Bool) (x : Zd d (sz.L n)),
        (mk sz z).K n u (fun _ : Fin 1 => τ) (fun _ => x) =
          if τ then (mk sz z).m n else (starRingEnd ℂ) ((mk sz z).m n)) :
    STExpDriftLogL d law Flow mk T0 := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨κ', δ, hκ', -, hδ, H⟩ := hClt hd κ ε 𝔡 hκ hε h𝔡
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR hLK hDec hExp hcon hS2 hLmax hLKU hGd hAvg
  obtain ⟨H₀, g', E, hm, hrange, hrep, -⟩ := H 𝔠 sz z hflow
  exact STExpDriftLoConclgL_of_LKU (mk sz z) (law sz) (hμ sz) (hFl.1 sz κ ε 𝔠 𝔡 z hflow) hrep hκ' hδ hm hs0
    (fun n => (hst n).le) htT (hFl.2 sz κ ε 𝔠 𝔡 z hκ hflow) hrange (hK sz κ ε 𝔠 𝔡 z hκ hflow)
    (hS sz κ ε 𝔠 𝔡 z hκ hflow) (hK1 sz κ ε 𝔠 𝔡 z hκ hflow) hR hLKU hAvg

/-! ## 7. The decay `(deccA0)` of the drift `D_u` (target 5, W-d) -/

/-- **`(deccA0)` for `D_u` from `STGdecayWgL … 0`** (band `STExpDriftDecayConcl_of_GdecayW`, `ExpEtermsB:968`; `3_5:1634`) per carrier.  Family row 18 (**W-d**): `hDL` is
`STGdecayWgL … Cd → STDecayLoopUgL` (form of `baDecayLoopU_of`; band `stDecayLoopUgL_of_step2`) and `hDE` the E-term decays of `STDecayLoopUgL` at the `FlowFM` labels `STELKLKg C`, `STEGtg C`
(`k = 2`, form of `baEtermDecaygL`; band `stEtermDecay` through the term bridges).  `STDecayLoopUgL` at `Cd = 0` gives, w.h.p., `|ℰ^{G̃}|, |ℰ^{LK×LK}| ≤ W^{-(D+1)}` for every `v ∈ [s_n,t_n]` and every far `a`;
the first moment with the envelope `N⁶` (`ExpEtermsBGen_env_poly`) and `P ≤ N^{-(D+7)}` gives `|𝔼ℰ| ≤ 2 W^{-(D+1)}`, so `|D_v(a)| ≤ 4 W^{-(D+1)} ≤ W^{-D}` (`W ≥ 4` eventually, `W ≤ N`).
The statement `STEKDecaygL` of the deterministic `D` is a `HighProbAt` of a set that is eventually full.  The regime `STReg5I` is not used: the bound holds in every regime. -/
theorem STExpDriftDecayConclgL_of_GdecayW {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (hμ : IsProbabilityMeasure μ)
    (hd : 3 ≤ d) {𝔠 𝔡 : ℝ} (hadm : sz.Admissible 𝔠 𝔡)
    {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    (hrep : CltRepg C μ H₀ g' E) {κ' δ : ℝ} (hκ' : 0 < κ') (hδ : 0 < δ) (hm : ∀ n, κ' ≤ (C.m n).im)
    {s t T : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (htT : ∀ n, t n ≤ T n) (hT1 : ∀ n, T n < 1)
    (hrange : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - T n) (hKb : STKboundgL C μ)
    (hcol : ∀ (n : ℕ) (y : Zd d (sz.L n)), ∑ x : Zd d (sz.L n), ‖C.S n x y‖ ≤ 1)
    (hK1 : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (τ : Bool) (x : Zd d (sz.L n)),
      C.K n u (fun _ : Fin 1 => τ) (fun _ => x) = if τ then C.m n else (starRingEnd ℂ) (C.m n))
    (hGd : STGdecayWgL C μ s t 0)
    (hDL : ∀ Cd : ℝ, STGdecayWgL C μ s t Cd → STDecayLoopUgL C μ s t)
    (hDE : STDecayLoopUgL C μ s t → ∀ σ : Fin 2 → Bool,
      STEKDecaygL μ s t (fun n v ω (a : Fin 2 → Zd d (sz.L n)) => STELKLKg C n (v : ℝ) σ a ω) ∧
        STEKDecaygL μ s t (fun n v ω (a : Fin 2 → Zd d (sz.L n)) => STEGtg C n (v : ℝ) σ a ω)) :
    STExpDriftDecayConclgL C μ s t := by
  have := hμ
  have hsz := hadm.2.2.1
  have henv := ExpEtermsBGen_env_poly μ hμ hsz hrep hκ' hδ hm hs0 hst htT hT1 hrange hKb hcol hK1
  have hDEσ := hDE (hDL 0 hGd)
  have hW4 : ∀ᶠ n in atTop, (4 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by
    have h1 : ∀ᶠ n in atTop, (4 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ 𝔠 :=
      ((tendsto_rpow_atTop hadm.1).comp hsz).eventually (eventually_ge_atTop 4)
    filter_upwards [h1, hadm.2.2.2.1] with n h1 h2
    exact h1.trans h2
  intro σ ε' D hε' hD
  have hG1 := (hDEσ σ).2 ε' (D + 1) hε' (by linarith)
  have hG2 := (hDEσ σ).1 ε' (D + 1) hε' (by linarith)
  have hev : ∀ᶠ n in atTop, ∀ v : TimeIcc s t n,
      EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε' D
        (fun a : Fin 2 → Zd d (sz.L n) => STExpDriftg C μ n (v : ℝ) σ a) := by
    filter_upwards [hG1 (D + 7) (by linarith), hG2 (D + 7) (by linarith), henv, hW4,
      hsz.eventually (eventually_ge_atTop 1)] with n hP1 hP2 hEnv hW4n hN1
    intro v a hfar
    have hN : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hN1
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
    have hWN := expDr_W_le_size sz hd n
    have hP1' : (μ {ω | ∀ v : TimeIcc s t n, EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε' (D + 1)
        (fun a : Fin 2 → Zd d (sz.L n) => STEGtg C n (v : ℝ) σ a ω)}ᶜ).toReal ≤
        ((sz.size n : ℕ) : ℝ) ^ (-(D + 7)) :=
      ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg (by linarith) _) hP1
    have hP2' : (μ {ω | ∀ v : TimeIcc s t n, EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε' (D + 1)
        (fun a : Fin 2 → Zd d (sz.L n) => STELKLKg C n (v : ℝ) σ a ω)}ᶜ).toReal ≤
        ((sz.size n : ℕ) : ℝ) ^ (-(D + 7)) :=
      ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg (by linarith) _) hP2
    have hE1 := expDr_decay_step (P := μ) (f := fun ω => STEGtg C n (v : ℝ) σ a ω)
      (hD.le) hN hW0 hWN (fun ω => (hEnv (v, σ, a) ω).2.1)
      (fun ω hω => by
        have hω' : ω ∈ {ω | ∀ v : TimeIcc s t n, EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε' (D + 1)
            (fun a : Fin 2 → Zd d (sz.L n) => STEGtg C n (v : ℝ) σ a ω)} := by
          simpa using hω
        exact hω' v a hfar) hP1'
    have hE2 := expDr_decay_step (P := μ) (f := fun ω => STELKLKg C n (v : ℝ) σ a ω)
      (hD.le) hN hW0 hWN (fun ω => (hEnv (v, σ, a) ω).1)
      (fun ω hω => by
        have hω' : ω ∈ {ω | ∀ v : TimeIcc s t n, EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε' (D + 1)
            (fun a : Fin 2 → Zd d (sz.L n) => STELKLKg C n (v : ℝ) σ a ω)} := by
          simpa using hω
        exact hω' v a hfar) hP2'
    have hdr : STExpDriftg C μ n (v : ℝ) σ a =
        (∫ ω, STELKLKg C n (v : ℝ) σ a ω ∂μ) + ∫ ω, STEGtg C n (v : ℝ) σ a ω ∂μ := rfl
    have hpow : ((sz.W n : ℕ) : ℝ) ^ (-D) = ((sz.W n : ℕ) : ℝ) ^ (-(D + 1)) * ((sz.W n : ℕ) : ℝ) := by
      have := Real.rpow_add hW0 (-(D + 1)) 1
      rw [Real.rpow_one] at this
      rw [← this]; congr 1; ring
    have hc : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg hW0.le _
    change ‖STExpDriftg C μ n (v : ℝ) σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D)
    rw [hdr]
    calc _ ≤ ‖∫ ω, STELKLKg C n (v : ℝ) σ a ω ∂μ‖ + ‖∫ ω, STEGtg C n (v : ℝ) σ a ω ∂μ‖ := norm_add_le _ _
      _ ≤ 2 * ((sz.W n : ℕ) : ℝ) ^ (-(D + 1)) + 2 * ((sz.W n : ℕ) : ℝ) ^ (-(D + 1)) := add_le_add hE2 hE1
      _ = 4 * ((sz.W n : ℕ) : ℝ) ^ (-(D + 1)) := by ring
      _ ≤ ((sz.W n : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-(D + 1)) := mul_le_mul_of_nonneg_right hW4n hc
      _ = ((sz.W n : ℕ) : ℝ) ^ (-D) := by rw [hpow]; ring
  intro D' hD'
  filter_upwards [hev] with n hn
  have h0 : {ω | ∀ v : TimeIcc s t n, EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε' D
      (fun a : Fin 2 → Zd d (sz.L n) => STExpDriftg C μ n (v : ℝ) σ a)}ᶜ = (∅ : Set sz.SeqΩ) := by
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact hn
  rw [h0, measure_empty]
  exact zero_le

/-- **`(deccA0)` for `D_u` over the carrier family** (band `stExpDriftDecay_holds`, `ExpEtermsB:1049`; `3_5:1634`): the pin `STExpDriftDecaygL` of `Chain/Step6Gen`, proved with `𝔠_d = 1/100`.
Family premises as `stExpDriftLogL_of`, and row 18 (`hDec`: `STGdecayWgL … Cd → STDecayLoopUgL`, then the E-term decays of `STDecayLoopUgL` at the labels `STELKLKg`, `STEGtg`, guarded by
`3 ≤ d`, `0 < κ`, `0 < ε`, `Flow` and the window `0 ≤ s ≤ t ≤ T0`, as the forms `baDecayLoopU_of`, `baEtermDecaygL` and the band `stDecayLoopU_of_step2`).  Premises of the pin used: `0 ≤ s`, `s < t` (as `≤`), `t ≤ T0`, `STGdecayWgL … 0`; unused: `STReg5I`, `STLKgL`, `STDecaygL`, `STExp2gL`, `STConStInd`,
`STStep2CoregL`, `STLmaxUgL`, `STLKUgL`. -/
theorem stExpDriftDecaygL_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hμ : ∀ sz : Sizes d, IsProbabilityMeasure (law sz))
    (hFl : Step2EventsGen_Flow d Flow T0) (hClt : IniTermGen_CltFlow d law Flow mk T0)
    (hK : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → STKboundgL (mk sz z) (law sz))
    (hS : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ (n : ℕ) (y : Zd d (sz.L n)), ∑ x : Zd d (sz.L n), ‖(mk sz z).S n x y‖ ≤ 1)
    (hK1 : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (τ : Bool) (x : Zd d (sz.L n)),
        (mk sz z).K n u (fun _ : Fin 1 => τ) (fun _ => x) =
          if τ then (mk sz z).m n else (starRingEnd ℂ) ((mk sz z).m n))
    (hDec : 3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → Flow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
      (∀ Cd : ℝ, STGdecayWgL (mk sz z) (law sz) s t Cd → STDecayLoopUgL (mk sz z) (law sz) s t) ∧
      (STDecayLoopUgL (mk sz z) (law sz) s t → ∀ σ : Fin 2 → Bool,
        STEKDecaygL (law sz) s t (fun n v ω (a : Fin 2 → Zd d (sz.L n)) => STELKLKg (mk sz z) n (v : ℝ) σ a ω) ∧
        STEKDecaygL (law sz) s t (fun n v ω (a : Fin 2 → Zd d (sz.L n)) => STEGtg (mk sz z) n (v : ℝ) σ a ω))) :
    STExpDriftDecaygL d law Flow mk T0 := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨κ', δ, hκ', -, hδ, H⟩ := hClt hd κ ε 𝔡 hκ hε h𝔡
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR hLK hDec' hExp hcon hS2 hLmax hLKU hGd
  obtain ⟨H₀, g', E, hm, hrange, hrep, -⟩ := H 𝔠 sz z hflow
  obtain ⟨hDL, hDE⟩ := hDec hd sz κ ε 𝔠 𝔡 z hκ hε hflow s t hs0 (fun n => (hst n).le) htT
  exact STExpDriftDecayConclgL_of_GdecayW (mk sz z) (law sz) (hμ sz) hd (hFl.1 sz κ ε 𝔠 𝔡 z hflow) hrep hκ' hδ hm hs0
    (fun n => (hst n).le) htT (hFl.2 sz κ ε 𝔠 𝔡 z hκ hflow) hrange (hK sz κ ε 𝔠 𝔡 z hκ hflow)
    (hS sz κ ε 𝔠 𝔡 z hκ hflow) (hK1 sz κ ε 𝔠 𝔡 z hκ hflow) hGd hDL hDE

/-! ## 8. The band re-derivations -/

/-! ## 9. Compiled nonempty instances at `d = 3` (targets 3-5)

Data: the merged ones of `Step5Pins`/`Step6Pins` (`κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`; flow `zB`): regime (iv) at `szG` (`L = 4`, `W_n = n + 4`, `lam = 5`), window `[5/8, 3/4]` (`szG_reg4`),
regime (i) at `szB`, window `[7/8, 15/16]`.  Discharged: the flow, the admissibility, the time ranges, the representation `CltRepg` and the class `IniTermGen_CltFlow` (`iniTermGen_cltFlow_band`),
`STKboundgL` (`stKbound_of_flow`), the column sums, `K^{(1)} = m_σ` (`ExpEtermsBGen_band_K1`), the law and, for target 5, row 18 (`ExpEtermsBGen_band_decay`).  Hypotheses: the stochastic
premises `STLKUgL`, `STExpAvgUgL`, `STGdecayWgL … 0` of other gates (Step 2). -/

end RBM.BA
