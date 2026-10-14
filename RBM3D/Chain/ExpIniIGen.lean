/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step6KitGen
import RBM3D.Induction.ExpIniI
import RBM3D.Induction.QopNorm
import RBM3D.Chain.CltFarUGen

/-!
# The initial term of regime (i) over the carrier (BA-V row V1s2', ticket T2506 row b, targets 6-8)

Additive restatement of `Induction/ExpIniI.lean` (not edited) over a carrier `C : FlowFM sz` and a law `μ`, on the one kernel `Step2Gen_UN C` and the vocabulary and
pins of `Chain/Step6Gen.lean`.  Paper: arXiv:2507.20274, `6:97, 117` (initial term of regime (i)), `3_5:1285` (`lem_+Q`), `3_5:1649` (`(sum_res_2_NAL)`),
`3_5:1659` (`(sum_res_2)`).

* **Target 6** (vocabulary).  `STExpIniIConclgL'` (band `STExpIniIConcl'`, `ExpIniI:1089`: `STExpIniIConclgL`, `Step6Gen:294`, with `0 < Cq → 0 < c →`) and `STExpIniIgL'`
  (band `STExpIniI'`, `:1102`); the bridges `bandFM_STExpIniIConcl'`, `STExpIniI'_iff_gL'` (pattern `Step6Gen_ingR6_iff_congr`).
* **Target 7** (kit).  `expIniI_fastDecayg` (band `expIniI_fastDecay`, `:309`): `(deccA0)` of `f_s = 𝔼(𝓛-𝒦)^{(2)}_s` from `STDecaygL` at `s` through `≺ → 𝔼` at the fixed time
  `s` (W-a).  The loops of the carrier are measurable and bounded by `η_s^{-2}` (`CltRepg`, `κ' ≤ Im m`; `meanFarG_lenv_of_rep`, `Evolution/MeanFarG:68`), `|𝒦^{(2)}| ≤ N B`
  is the pin `STKboundgL` (row 17) and `(1-s)⁻¹ ≤ N^{1-δ}` is the range `N^{-1+δ} ≤ 1 - T0` of the class `IniTermGen_CltFlow` (row 9'); the exponents are those of the band
  with `q = 2` (`η_s⁻¹, B ≤ N²`, `‖f_s‖_∞ ≤ N⁶`).  `expIniI_fastDecay_mono` (`:495`) is model-free and reused by name.
  `expIniI_sameg` (band `expIniI_same`, `:646`) is `(sum_res_2_NAL)` (`STEKSumRes2NALgL`) at the kernel coupling `gK` (W-b): the window `gK² ≤ lam²`, the decay class
  `lam² ≤ A gK²` and the ratio `(gK² + 1-s)/(gK² + 1-u) ≤ A · 2` are the comparison R1 and `STReg5I` at `sz.lam`, through the toolkit `step34Gen_*` of `Chain/Step34Gen`.
  `expIniI_Qopg`, `expIniI_mixedg` (band `expIniI_Qop`, `expIniI_mixed`, `:735`, `:892`) are `lem_+Q` (`stQopNorm_holds`, `stQop_sub_fastDecay`, `QopAlgebra_Psum_Qop`)
  and `(sum_res_2)` (`STEKSumRes2gL`).
* **Target 8.**  `stExpIniIgL'_of` (→ `STExpIniIgL'`) from the family premises; the band `stExpIniI'_holds` (`:1106`) is re-derived.  `ST_step6_caseI_of_pins'` (`:1127`) is band
  only (V1L-C1: its global average input `STImproveExpAver` is not read here).

Coupling (UBA-C1): every size-level quantity reads `sz.lam`; R1 (`∀ n, 0 ≤ gK n * lam n ∧ gK n ^ 2 ≤ lam n ^ 2 ∧ lam n ^ 2 ≤ Aof κm * gK n ^ 2`) enters only at the window, the
decay class and the ratio of the two kernel pins.  No `def`, `abbrev` or `structure` is added beyond the two of target 6; helpers are `private` and prefixed `ExpIniIGen_`.
The private model-free lemmas of the band file (`expIniI_window`, `expIniI_Bctl_le`, `expIniI_STWB_le`, `expIniI_norm_integral_le`, `expIniI_superpoly`, `expIniI_W_le_size`,
`expIniI_Ts_ge`, `expIniI_W_rpow_ge`, `expIniI_L_pow_le`) are used by `open private`.  Ports: none from `../RBM1D`, `../RBM2D`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open private expIniI_Bctl_le expIniI_STWB_le expIniI_norm_integral_le expIniI_superpoly expIniI_W_le_size expIniI_window
  expIniI_Ts_ge expIniI_W_rpow_ge expIniI_L_pow_le from RBM3D.Induction.ExpIniI

open private Step5CasesGen_prec_mono from RBM3D.Chain.Step5CasesGen

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The primed vocabulary and its bridges (target 6) -/

/-- **Target 6, `STExpIniIConclgL'`** (band `STExpIniIConcl'`, `ExpIniI:1089`): `STExpIniIConclgL` (`Step6Gen:294`) with `0 < Cq → 0 < c →`. -/
def STExpIniIConclgL' {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := STIdx2P sz STSigSame s t)
    (fun n p _ => ‖Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ) (fun b => STExpErrg C μ n (s n) p.2.1.1 b) p.2.2‖)
    (fun n p _ => STExpTarget sz n (p.1 : ℝ)) ∧
  ∀ (Cq c : ℝ), 0 < Cq → 0 < c → ∀ ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ,
    (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) Cq c (ϑ n)) →
    PrecL sz μ (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ)
        (STQop (d := d) (ϑ n) (s n) (fun b => STExpErrg C μ n (s n) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => STExpTarget sz n (p.1 : ℝ))

/-- **Target 6, `STExpIniIgL'`** (band `STExpIniI'`, `ExpIniI:1102`) over the carrier tuple. -/
def STExpIniIgL' (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngR6gL d STReg5I law Flow mk T0 (fun sz z s t => STExpIniIConclgL' (mk sz z) (law sz) s t)

section Bridges

variable {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ)

/-- Band `STExpIniIConcl'` is `STExpIniIConclgL'` at `bandFM`: through `bandStep2_Ugen`, nothing else. -/
theorem bandFM_STExpIniIConcl' :
    STExpIniIConcl' sz E s t ↔ STExpIniIConclgL' (bandFM sz E) (Sizes.seqP sz) s t := by
  unfold STExpIniIConcl' STExpIniIConclgL'
  simp only [bandStep2_Ugen]
  exact Iff.rfl

end Bridges

/-- Band `STExpIniI'` is `STExpIniIgL'` at the band tuple `(seqP, STFlow, bandFM ∘ STflowE, lemT)`. -/
theorem STExpIniI'_iff_gL' (d : ℕ) :
    STExpIniI' d ↔ STExpIniIgL' d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  Step6Gen_ingR6_iff_congr d STReg5I (fun sz E s t => STExpIniIConcl' sz E s t) _
    (fun sz z s t => bandFM_STExpIniIConcl' sz (STflowE z) s t)

/-! ## 2. Polynomial facts along the flow and the expectation step (W-a) -/

section Expect

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- **The polynomial facts at the fixed time `s`** (W-a; band `expIniI_inv_one_sub_le`, `expIniI_Bctl_le` and the opening of `expIniI_fastDecay`): eventually in `n`,
`η_s⁻¹ ≤ N²`, `B_s ≤ N²` and `|𝒦^{(2)}_{s,σ,a}| ≤ N B_s`.  Inputs: `κ' ≤ Im m` (so `η_s = (1-s) Im m ≥ (1-s) κ'`), the range `N^{-1+δ} ≤ 1 - T` of row 9' with `s ≤ T`
(so `(1-s)⁻¹ ≤ N^{1-δ} ≤ N`) and the pin `STKboundgL` at the time `s` (row 17). -/
private theorem ExpIniIGen_poly {κ' δ 𝔠 𝔡 : ℝ} (hκ' : 0 < κ') (hadm : sz.Admissible 𝔠 𝔡) (hμ : IsProbabilityMeasure μ)
    (hmn : ∀ n, κ' ≤ (C.m n).im) (hKb : STKboundgL C μ) {s T : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hsT : ∀ n, s n ≤ T n)
    (hT1 : ∀ n, T n < 1) (hev : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - T n) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, (etaOf (C.m n) (s n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (2 : ℝ) ∧
      sz.Bctl n (s n) ≤ ((sz.size n : ℕ) : ℝ) ^ (2 : ℝ) ∧
      ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖C.K n (s n) σ a‖ ≤ ((sz.size n : ℕ) : ℝ) * sz.Bctl n (s n) := by
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have hs1 : ∀ n, s n < 1 := fun n => (hsT n).trans_lt (hT1 n)
  have hKb2 := (st6_prec_det_iffg sz μ hμ hsz (V := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
    (fun n p => ‖C.K n (s n) p.1 p.2‖) (fun n _ => (sz.Bctl n (s n)) ^ (2 - 1))).1 (hKb s hs0 hs1 2 (by norm_num)) 1 one_pos
  have hNge : ∀ᶠ n in atTop, max 2 κ'⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := hsz.eventually (eventually_ge_atTop _)
  filter_upwards [hKb2, hNge, hev] with n hKn hNn hevn
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hNn
  have hNκ : κ'⁻¹ ≤ N := (le_max_right _ _).trans hNn
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have h1s : 0 < 1 - s n := by linarith [hs1 n]
  have hlow : N ^ (-1 + δ) ≤ 1 - s n := hevn.trans (by linarith [hsT n])
  have hxinv : (1 - s n)⁻¹ ≤ N := by
    calc (1 - s n)⁻¹ ≤ (N ^ (-1 + δ))⁻¹ := inv_anti₀ (Real.rpow_pos_of_pos hN0 _) hlow
      _ = N ^ (-(-1 + δ)) := (Real.rpow_neg hN0.le _).symm
      _ ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = N := Real.rpow_one N
  refine ⟨?_, ?_, fun σ a => ?_⟩
  · have hηlow : (1 - s n) * κ' ≤ etaOf (C.m n) (s n) := by
      unfold etaOf; exact mul_le_mul_of_nonneg_left (hmn n) h1s.le
    have hpos : 0 < (1 - s n) * κ' := by positivity
    calc (etaOf (C.m n) (s n))⁻¹ ≤ ((1 - s n) * κ')⁻¹ := inv_anti₀ hpos hηlow
      _ = (1 - s n)⁻¹ * κ'⁻¹ := mul_inv _ _
      _ ≤ N * N := mul_le_mul hxinv hNκ (by positivity) hN0.le
      _ = N ^ (2 : ℝ) := by rw [Real.rpow_two, sq]
  · calc sz.Bctl n (s n) ≤ 2 * (1 - s n)⁻¹ := expIniI_Bctl_le sz n (hs1 n)
      _ ≤ 2 * N := by gcongr
      _ ≤ N * N := by nlinarith
      _ = N ^ (2 : ℝ) := by rw [Real.rpow_two, sq]
  · have := hKn (σ, a)
    simpa [Real.rpow_one] using this

/-- `f_s = 𝔼(𝓛-𝒦)^{(2)}_s` is the integral of `𝓛 - 𝒦` (band `expIniI_expErr_eq`, `:183`). -/
private theorem ExpIniIGen_expErr_eq (hμ : IsProbabilityMeasure μ)
    {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    (hrep : CltRepg C μ H₀ g' E) {κ : ℝ} (hκ : 0 < κ) (n : ℕ) (hm : κ ≤ (C.m n).im) {u : ℝ} (hu : u < 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STExpErrg C μ n u σ a = ∫ ω, (C.L n u σ a ω - C.K n u σ a) ∂μ := by
  have : IsProbabilityMeasure μ := hμ
  have hL := (meanFarG_lenv_of_rep C μ hrep hκ n hm hu) σ a
  unfold STExpErrg
  rw [integral_sub (Integrable.of_bound hL.1.aestronglyMeasurable _ (Filter.Eventually.of_forall hL.2)) (integrable_const _),
    integral_const]
  simp

/-- **The pointwise `≺ → 𝔼` bound** (band `expIniI_bound`, `:194`; pattern `meanFarG_B_bound`, `Evolution/MeanFarG:149`): if the `≺` bound `N^τ Z` fails with probability
`≤ N^{-D₁}`, then `‖f_{u,σ,a}‖ ≤ N^τ Z + (η_u^{-2} + |𝒦_{σ,a}|) N^{-D₁}` (a.s. envelope `|𝓛^{(2)}| ≤ η_u^{-2}`, `meanFarG_lenv_of_rep`). -/
private theorem ExpIniIGen_bound (hμ : IsProbabilityMeasure μ)
    {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    (hrep : CltRepg C μ H₀ g' E) {κ : ℝ} (hκ : 0 < κ) (n : ℕ) (hm : κ ≤ (C.m n).im) {u : ℝ} (hu : u < 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) {τ Z D₁ : ℝ} (hZ : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ * Z)
    (hP : μ {ω | ((sz.size n : ℕ) : ℝ) ^ τ * Z < ‖C.L n u σ a ω - C.K n u σ a‖} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₁))) :
    ‖STExpErrg C μ n u σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * Z +
      ((etaOf (C.m n) u)⁻¹ ^ 2 + ‖C.K n u σ a‖) * ((sz.size n : ℕ) : ℝ) ^ (-D₁) := by
  have : IsProbabilityMeasure μ := hμ
  have hL := (meanFarG_lenv_of_rep C μ hrep hκ n hm hu) σ a
  have hmeas : Measurable fun ω => C.L n u σ a ω - C.K n u σ a := hL.1.sub measurable_const
  have hall : ∀ ω, ‖C.L n u σ a ω - C.K n u σ a‖ ≤ (etaOf (C.m n) u)⁻¹ ^ 2 + ‖C.K n u σ a‖ :=
    fun ω => (norm_sub_le _ _).trans (add_le_add (hL.2 ω) le_rfl)
  have h := expIniI_norm_integral_le μ (fun ω => C.L n u σ a ω - C.K n u σ a) hmeas _ _ hZ hall
  have hreal : μ.real {ω | ((sz.size n : ℕ) : ℝ) ^ τ * Z < ‖C.L n u σ a ω - C.K n u σ a‖} ≤
      ((sz.size n : ℕ) : ℝ) ^ (-D₁) := by
    rw [Measure.real]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hP
    rwa [ENNReal.toReal_ofReal (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at this
  have hC : 0 ≤ (etaOf (C.m n) u)⁻¹ ^ 2 + ‖C.K n u σ a‖ := by positivity
  rw [ExpIniIGen_expErr_eq C μ hμ hrep hκ n hm hu]
  refine h.trans ?_
  gcongr

/-- `|f_{u,σ,a}| ≤ η_u^{-2} + |𝒦_{σ,a}|` (a.s. envelope of `𝓛^{(2)}`; band `expIniI_envelope`, `:221`). -/
private theorem ExpIniIGen_envelope (hμ : IsProbabilityMeasure μ)
    {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    (hrep : CltRepg C μ H₀ g' E) {κ : ℝ} (hκ : 0 < κ) (n : ℕ) (hm : κ ≤ (C.m n).im) {u : ℝ} (hu : u < 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ‖STExpErrg C μ n u σ a‖ ≤ (etaOf (C.m n) u)⁻¹ ^ 2 + ‖C.K n u σ a‖ := by
  have : IsProbabilityMeasure μ := hμ
  have hL := (meanFarG_lenv_of_rep C μ hrep hκ n hm hu) σ a
  have hmeas : Measurable fun ω => C.L n u σ a ω - C.K n u σ a := hL.1.sub measurable_const
  have hall : ∀ ω, ‖C.L n u σ a ω - C.K n u σ a‖ ≤ (etaOf (C.m n) u)⁻¹ ^ 2 + ‖C.K n u σ a‖ :=
    fun ω => (norm_sub_le _ _).trans (add_le_add (hL.2 ω) le_rfl)
  have h := expIniI_norm_integral_le μ (fun ω => C.L n u σ a ω - C.K n u σ a) hmeas 0 _ le_rfl hall
  have hC : 0 ≤ (etaOf (C.m n) u)⁻¹ ^ 2 + ‖C.K n u σ a‖ := by positivity
  rw [ExpIniIGen_expErr_eq C μ hμ hrep hκ n hm hu]
  refine h.trans ?_
  have : μ.real {ω | (0 : ℝ) < ‖C.L n u σ a ω - C.K n u σ a‖} ≤ 1 := measureReal_le_one
  nlinarith

/-! ## 3. The decay `(deccA0)` of `f_s` (`≺ → 𝔼` at the fixed time `s`; target 7) -/

/-- **The decay `(deccA0)` of `f_s = 𝔼(𝓛-𝒦)^{(2)}_s`** for every `(ε', D)` (`EKFastDecay`, scale `W^{ε'} ℓ_s`; band `expIniI_fastDecay`, `ExpIniI:309`), from `(Eq:Gdecay+IND)` at `s`
(`STDecaygL`) through `≺ → 𝔼`: with `τ = 𝔠`, `D' = D + 2`, `D₁ = (2q+1)/𝔠 + D + 1`, `q = 2`, off an event of probability `≤ N^{-D₁}` `|𝓛-𝒦| ≤ N^𝔠 (B^{1/5} W^{-d}B_{|a₁-a₂|}
e^{-(|a₁-a₂|/ℓ)^{1/2}} + W^{-D'})`; the a.s. envelope `η_s^{-2}` and `|𝒦| ≤ N B` are polynomial in `N` (`ExpIniIGen_poly`), `W ≤ N ≤ W^{1/𝔠}`, and the stretched
exponential `e^{-(W^{ε'}/d)^{1/2}}` beats every power of `W`.  Deterministic conclusion.  The time `T ≥ s` carries the range `N^{-1+δ} ≤ 1 - T` (row 9'). -/
theorem expIniI_fastDecayg (hd : 3 ≤ d) {κ' δ 𝔠 𝔡 : ℝ} (hκ' : 0 < κ') (hδ : 0 < δ) (hadm : sz.Admissible 𝔠 𝔡)
    (hμ : IsProbabilityMeasure μ) {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    (hrep : CltRepg C μ H₀ g' E) (hmn : ∀ n, κ' ≤ (C.m n).im) (hKb : STKboundgL C μ) {s T : ℕ → ℝ}
    (hs0 : ∀ n, 0 ≤ s n) (hsT : ∀ n, s n ≤ T n) (hT1 : ∀ n, T n < 1)
    (hev : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - T n) (hDec : STDecaygL C μ s) (ε' D : ℝ)
    (hε' : 0 < ε') (hD : 0 < D) :
    ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool,
      EKFastDecay (sz.lam n) (s n) ((sz.W n : ℕ) : ℝ) ε' D (fun b => STExpErrg C μ n (s n) σ b) := by
  obtain ⟨h𝔠, h𝔡, hSz, hBw, hWO⟩ := id hadm
  have hs1 : ∀ n, s n < 1 := fun n => (hsT n).trans_lt (hT1 n)
  have hd0 : 0 < d := by omega
  have hd0' : (0 : ℝ) < d := by exact_mod_cast hd0
  set D' : ℝ := D + 2 with hD'
  set D₁ : ℝ := (2 * 2 + 1) / 𝔠 + D + 1 with hD₁
  have hD₁pos : 0 < D₁ := by positivity
  set c₁ : ℝ := 1 + 6 * 2 / (5 * 𝔠) with hc₁
  have hP := hDec D' (by linarith) 𝔠 h𝔠 D₁ hD₁pos
  have hpoly := ExpIniIGen_poly C μ hκ' hadm hμ hmn hKb hs0 hsT hT1 hev hδ
  have hWt : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := step34Gen_W_tendsto hadm
  have hWsuper := hWt.eventually (expIniI_superpoly hd0 ε' c₁ D hε')
  have hWge : ∀ᶠ n in atTop, max 8 κ'⁻¹ ≤ ((sz.W n : ℕ) : ℝ) := hWt.eventually (eventually_ge_atTop _)
  filter_upwards [hP, hpoly, hBw, hWsuper, hWge] with n hPn hpn hBn hSn hWn
  obtain ⟨hη, hB, hK⟩ := hpn
  intro σ a ⟨i, j, hij⟩
  -- notation
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  set ℓ : ℝ := ellT (sz.L n) (sz.lam n) (s n) with hℓdef
  set B : ℝ := sz.Bctl n (s n) with hBdef
  have hW8 : 8 ≤ W := (le_max_left _ _).trans hWn
  have hW0 : 0 < W := by linarith
  have hWN : W ≤ N := expIniI_W_le_size sz hd0 n
  have hN8 : 8 ≤ N := hW8.trans hWN
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hℓ1 : 1 ≤ ℓ := one_le_ellT hL1
  have hBpos : 0 < B := STBctl_pos sz n (hs1 n)
  -- the polynomial bounds, with `q = 2`
  generalize hq : (2 : ℝ) = q at hη hB
  have hq1 : 1 ≤ q := by rw [← hq]; norm_num
  have hK2 : ‖C.K n (s n) σ a‖ ≤ N ^ (1 + q) := by
    refine (hK σ a).trans ?_
    rw [Real.rpow_add hN0, Real.rpow_one]
    exact mul_le_mul_of_nonneg_left hB hN0.le
  -- the `≺` bound at `(σ, a)`
  set r : ℕ := zdistInf d (sz.L n) (a 0 - a 1) with hr
  set Y₀ : ℝ := Real.exp (-(W ^ ε' / (d : ℝ)) ^ (1 / 2 : ℝ)) with hY₀
  have hfar : W ^ ε' * ℓ ≤ (d : ℝ) * (r : ℝ) := by
    have hWe : 0 < W ^ ε' := Real.rpow_pos_of_pos hW0 _
    have hpos : 0 < W ^ ε' * ℓ := by positivity
    have hD01 : (zdistD d (sz.L n) (a 0 - a 1) : ℝ) ≤ (d : ℝ) * (r : ℝ) := by
      have := zdistD_le_mul_zdistInf d (sz.L n) (a 0 - a 1)
      exact_mod_cast this
    have hcase : (zdistD d (sz.L n) (a i - a j) : ℝ) ≤ (zdistD d (sz.L n) (a 0 - a 1) : ℝ) := by
      fin_cases i <;> fin_cases j
      · simp only [Fin.zero_eta, sub_self, zdistD_zero, Nat.cast_zero] at hij ⊢; linarith
      · exact le_rfl
      · have : a 1 - a 0 = -(a 0 - a 1) := by ring
        simp only [Fin.mk_one, Fin.zero_eta, this, zdistD_neg]
        exact le_rfl
      · simp only [Fin.mk_one, sub_self, zdistD_zero, Nat.cast_zero] at hij ⊢; linarith
    linarith
  have hYle : Real.exp (-(((r : ℕ) : ℝ) / ℓ) ^ (1 / 2 : ℝ)) ≤ Y₀ := by
    rw [hY₀]
    apply Real.exp_le_exp.2
    apply neg_le_neg
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    rw [div_le_div_iff₀ hd0' (by linarith)]
    nlinarith
  -- the `≺ → 𝔼` bound
  have hSTWB0 : 0 ≤ STWB sz n (s n) r := by
    unfold STWB Bparam; positivity
  have hZnn : 0 ≤ N ^ 𝔠 * (B ^ (1 / 5 : ℝ) * STWB sz n (s n) r *
      Real.exp (-((r : ℝ) / ℓ) ^ (1 / 2 : ℝ)) + W ^ (-D')) := by positivity
  have hbd := ExpIniIGen_bound C μ hμ hrep hκ' n (hmn n) (hs1 n) σ a (τ := 𝔠) (D₁ := D₁)
    (Z := B ^ (1 / 5 : ℝ) * STWB sz n (s n) r * Real.exp (-((r : ℝ) / ℓ) ^ (1 / 2 : ℝ)) + W ^ (-D')) hZnn
    (by
      refine le_trans (measure_mono ?_) hPn
      intro ω hω
      exact ⟨(σ, a), hω⟩)
  have hB65 : B ^ (1 / 5 : ℝ) * B = B ^ (6 / 5 : ℝ) := by
    rw [show (6 / 5 : ℝ) = 1 / 5 + 1 by norm_num, Real.rpow_add hBpos, Real.rpow_one]
  have hZle : B ^ (1 / 5 : ℝ) * STWB sz n (s n) r * Real.exp (-((r : ℝ) / ℓ) ^ (1 / 2 : ℝ)) + W ^ (-D') ≤
      B ^ (6 / 5 : ℝ) * Y₀ + W ^ (-D') := by
    have h1 : B ^ (1 / 5 : ℝ) * STWB sz n (s n) r ≤ B ^ (6 / 5 : ℝ) := by
      rw [← hB65]
      exact mul_le_mul_of_nonneg_left (expIniI_STWB_le sz n (s n) r) (Real.rpow_nonneg hBpos.le _)
    have h2 := mul_le_mul h1 hYle (Real.exp_pos _).le (Real.rpow_nonneg hBpos.le _)
    linarith
  -- `T1`: `N^𝔠 B^{6/5} Y₀ ≤ W^{c₁} Y₀`
  have hB65N : B ^ (6 / 5 : ℝ) ≤ W ^ (6 * q / (5 * 𝔠)) := by
    have h1 : B ^ (6 / 5 : ℝ) ≤ (N ^ q) ^ (6 / 5 : ℝ) := Real.rpow_le_rpow hBpos.le hB (by norm_num)
    rw [← Real.rpow_mul hN0.le] at h1
    have h2 := size_rpow_le_W_rpow sz h𝔠 n hBn (τ := q * (6 / 5)) (by positivity)
    have e : q * (6 / 5) / 𝔠 = 6 * q / (5 * 𝔠) := by field_simp
    rw [e] at h2
    exact h1.trans h2
  have hT1 : N ^ 𝔠 * (B ^ (6 / 5 : ℝ) * Y₀) ≤ W ^ c₁ * Y₀ := by
    have hY0 : 0 ≤ Y₀ := (Real.exp_pos _).le
    have hWc : W ^ c₁ = W * W ^ (6 * q / (5 * 𝔠)) := by
      rw [hc₁, ← hq, Real.rpow_add hW0, Real.rpow_one]
    rw [hWc]
    have h1 : N ^ 𝔠 * B ^ (6 / 5 : ℝ) ≤ W * W ^ (6 * q / (5 * 𝔠)) :=
      mul_le_mul hBn hB65N (Real.rpow_nonneg hBpos.le _) hW0.le
    calc N ^ 𝔠 * (B ^ (6 / 5 : ℝ) * Y₀) = (N ^ 𝔠 * B ^ (6 / 5 : ℝ)) * Y₀ := by ring
      _ ≤ (W * W ^ (6 * q / (5 * 𝔠))) * Y₀ := mul_le_mul_of_nonneg_right h1 hY0
  -- `T2`: `N^𝔠 W^{-D'} ≤ W^{-D}/8`
  have hWD1 : W ^ (-D') = W ^ (-D) * W⁻¹ ^ 2 := by
    rw [hD', show -(D + 2) = -D + (-1) + (-1) by ring, Real.rpow_add hW0, Real.rpow_add hW0,
      Real.rpow_neg_one]; ring
  have hWm1 : W⁻¹ ≤ 1 / 8 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hW8
  have hWD0 : 0 < W ^ (-D) := Real.rpow_pos_of_pos hW0 _
  have hT2 : N ^ 𝔠 * W ^ (-D') ≤ W ^ (-D) / 8 := by
    have hexp : W * W ^ (-D') = W ^ (-D) * W⁻¹ := by
      rw [hWD1]; field_simp
    calc N ^ 𝔠 * W ^ (-D') ≤ W * W ^ (-D') := mul_le_mul_of_nonneg_right hBn (Real.rpow_nonneg hW0.le _)
      _ = W ^ (-D) * W⁻¹ := hexp
      _ ≤ W ^ (-D) * (1 / 8) := by gcongr
      _ = W ^ (-D) / 8 := by ring
  -- `T3`: `(η⁻² + |𝒦|) N^{-D₁} ≤ W^{-D}/4`
  have hη2 : (etaOf (C.m n) (s n))⁻¹ ^ 2 ≤ N ^ (2 * q) := by
    have h0 : 0 ≤ (etaOf (C.m n) (s n))⁻¹ := by
      have : 0 < etaOf (C.m n) (s n) := by
        unfold etaOf; exact mul_pos (by linarith [hs1 n]) (lt_of_lt_of_le hκ' (hmn n))
      exact (inv_pos.2 this).le
    calc (etaOf (C.m n) (s n))⁻¹ ^ 2 ≤ (N ^ q) ^ 2 := pow_le_pow_left₀ h0 hη 2
      _ = N ^ (2 * q) := by
        rw [← Real.rpow_natCast (N ^ q) 2, ← Real.rpow_mul hN0.le]; norm_num; ring_nf
  have hsum : (etaOf (C.m n) (s n))⁻¹ ^ 2 + ‖C.K n (s n) σ a‖ ≤ 2 * N ^ (2 * q + 1) := by
    have h1 : N ^ (2 * q) ≤ N ^ (2 * q + 1) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have h2 : N ^ (1 + q) ≤ N ^ (2 * q + 1) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    linarith
  have hN21 : N ^ (2 * q + 1) ≤ W ^ ((2 * q + 1) / 𝔠) :=
    size_rpow_le_W_rpow sz h𝔠 n hBn (τ := 2 * q + 1) (by positivity)
  have hND : N ^ (-D₁) ≤ W ^ (-D₁) :=
    Real.rpow_le_rpow_of_nonpos hW0 hWN (by linarith)
  have hT3 : ((etaOf (C.m n) (s n))⁻¹ ^ 2 + ‖C.K n (s n) σ a‖) * N ^ (-D₁) ≤ W ^ (-D) / 4 := by
    have hpp : W ^ ((2 * q + 1) / 𝔠) * W ^ (-D₁) = W ^ (-D) * W⁻¹ := by
      rw [← Real.rpow_add hW0, show (2 * q + 1) / 𝔠 + -D₁ = -D + (-1) by rw [hD₁, ← hq]; ring,
        Real.rpow_add hW0, Real.rpow_neg_one]
    calc ((etaOf (C.m n) (s n))⁻¹ ^ 2 + ‖C.K n (s n) σ a‖) * N ^ (-D₁)
        ≤ (2 * W ^ ((2 * q + 1) / 𝔠)) * W ^ (-D₁) := by
          apply mul_le_mul (hsum.trans (by linarith)) hND (Real.rpow_nonneg hN0.le _) (by positivity)
      _ = 2 * (W ^ (-D) * W⁻¹) := by rw [mul_assoc, hpp]
      _ ≤ 2 * (W ^ (-D) * (1 / 8)) := by gcongr
      _ = W ^ (-D) / 4 := by ring
  -- assembly
  change ‖STExpErrg C μ n (s n) σ a‖ ≤ W ^ (-D)
  refine hbd.trans ?_
  have hmul := mul_le_mul_of_nonneg_left hZle (Real.rpow_nonneg hN0.le 𝔠)
  have hexp : N ^ 𝔠 * (B ^ (6 / 5 : ℝ) * Y₀ + W ^ (-D')) = N ^ 𝔠 * (B ^ (6 / 5 : ℝ) * Y₀) + N ^ 𝔠 * W ^ (-D') := by
    ring
  have hYS : W ^ c₁ * Y₀ ≤ W ^ (-D) / 2 := by
    have := hSn
    rw [show W ^ c₁ * Y₀ = W ^ c₁ * Real.exp (-(W ^ ε' / (d : ℝ)) ^ (1 / 2 : ℝ)) from rfl]
    linarith [this]
  linarith

/-- **A polynomial bound on `f_s`** (W-a; band `expIniI_env_poly`, `:564`): `‖f_{s,σ}‖_∞ ≤ N⁶` (a.s. envelope `η_s^{-2} ≤ N⁴`, `|𝒦| ≤ N B ≤ N³`); the cap of the ticket is `N⁶`. -/
private theorem ExpIniIGen_env_poly {κ' δ 𝔠 𝔡 : ℝ} (hκ' : 0 < κ') (hδ : 0 < δ) (hadm : sz.Admissible 𝔠 𝔡)
    (hμ : IsProbabilityMeasure μ) {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    (hrep : CltRepg C μ H₀ g' E) (hmn : ∀ n, κ' ≤ (C.m n).im) (hKb : STKboundgL C μ) {s T : ℕ → ℝ}
    (hs0 : ∀ n, 0 ≤ s n) (hsT : ∀ n, s n ≤ T n) (hT1 : ∀ n, T n < 1)
    (hev : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - T n) :
    ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool,
      ‖(fun b => STExpErrg C μ n (s n) σ b)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (6 : ℝ) := by
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have hs1 : ∀ n, s n < 1 := fun n => (hsT n).trans_lt (hT1 n)
  have hpoly := ExpIniIGen_poly C μ hκ' hadm hμ hmn hKb hs0 hsT hT1 hev hδ
  have hNge : ∀ᶠ n in atTop, 8 ≤ ((sz.size n : ℕ) : ℝ) := hsz.eventually (eventually_ge_atTop _)
  filter_upwards [hpoly, hNge] with n hpn hN8
  obtain ⟨hη, hB, hK⟩ := hpn
  intro σ
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hnn : 0 ≤ N ^ (6 : ℝ) := Real.rpow_nonneg hN0.le _
  refine (pi_norm_le_iff_of_nonneg hnn).2 fun a => ?_
  have h0 : 0 ≤ (etaOf (C.m n) (s n))⁻¹ := by
    have : 0 < etaOf (C.m n) (s n) := by
      unfold etaOf; exact mul_pos (by linarith [hs1 n]) (lt_of_lt_of_le hκ' (hmn n))
    exact (inv_pos.2 this).le
  rw [Real.rpow_two] at hη hB
  have hη2 : (etaOf (C.m n) (s n))⁻¹ ^ 2 ≤ N ^ 4 :=
    calc (etaOf (C.m n) (s n))⁻¹ ^ 2 ≤ (N ^ 2) ^ 2 := pow_le_pow_left₀ h0 hη 2
      _ = N ^ 4 := by ring
  have hK3 : ‖C.K n (s n) σ a‖ ≤ N ^ 3 :=
    (hK σ a).trans (calc N * sz.Bctl n (s n) ≤ N * N ^ 2 := by gcongr
      _ = N ^ 3 := by ring)
  have h34 : N ^ 3 ≤ N ^ 4 := pow_le_pow_right₀ hN1 (by norm_num)
  have h46 : 2 * N ^ 4 ≤ N ^ 6 :=
    calc 2 * N ^ 4 ≤ N ^ 2 * N ^ 4 := mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
      _ = N ^ 6 := by ring
  have henv := ExpIniIGen_envelope C μ hμ hrep hκ' n (hmn n) (hs1 n) σ a
  rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  linarith

end Expect

/-! ## 4. `σ₁ = σ₂`: `(sum_res_2_NAL)` (target 7, W-b) -/

section Same

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz)

/-- `T_s ≥ N^{-3}` for every `n`: the event of `STEKLow` is the whole space (band `expIniI_low`, `:534`), at a law `μ`. -/
private theorem ExpIniIGen_low (μ : Measure sz.SeqΩ) {s u : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hs1 : ∀ n, s n < 1) :
    STEKLowgL μ s u (fun n _ _ => STExpTarget sz n (s n)) :=
  ⟨3, HighProbAt.of_eventually_univ (Eventually.of_forall fun n _ _ => expIniI_Ts_ge sz n (hs0 n) (hs1 n))⟩

/-- **`(sum_res_2_NAL)` applied to `f_s`** (`3_5:1649`; band `expIniI_same`, `ExpIniI:646`): for `σ₁ = σ₂`, regime (i), `𝒰_{s,u,σ} f_s ≺ T_u` uniformly in `u ∈ [s,t]`, from the
kernel pin `STEKSumRes2NALgL` at the coupling `gK` (class `Ker` at `κm`) and the comparison R1: the window `gK² ≤ lam²` (`step34Gen_winK_of_cmp`), the decay class `lam² ≤ A gK²` for
`(deccA0)` (`step34Gen_decayK_of_cmp`, `expIniI_fastDecayg`, `expIniI_fastDecay_mono`) and the ratio `(gK² + 1-s)/(gK² + 1-u) ≤ A · 2` (`step34Gen_ratio_le`; `1-s ≤ lam²`), `A = Aof κm`;
the first conjunct of `STExpIniIConclgL'` with an explicit `𝔠_d` (`d 𝔠_d < 1`).  The `L^∞` hypothesis is `(Eq:Gtlp_exp+IND)` (`STExp2gL`), the decay of `f_s` is `STDecaygL`. -/
theorem expIniI_sameg {law : ∀ sz : Sizes d, Measure sz.SeqΩ} {Ker : STEKKer d} {Aof : ℝ → ℝ}
    (hSR : STEKSumRes2NALgL d law Ker) (hd : 3 ≤ d) {κm κ' δ 𝔠 𝔡 𝔠d : ℝ} (hκm : 0 < κm) (hAof : 1 ≤ Aof κm)
    (h𝔠d : 0 < 𝔠d) (hdc : (d : ℝ) * 𝔠d < 1) (hκ' : 0 < κ') (hδ : 0 < δ) (hadm : sz.Admissible 𝔠 𝔡)
    (gK : ℕ → ℝ) (hKer : Ker sz C gK κm) (hg : ∀ᶠ n in atTop, 0 < gK n ∧ gK n ≤ 𝔡⁻¹)
    (hcmp : ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ Aof κm * gK n ^ 2)
    (hμ : IsProbabilityMeasure (law sz))
    {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    (hrep : CltRepg C (law sz) H₀ g' E) (hmn : ∀ n, κ' ≤ (C.m n).im) (hKb : STKboundgL C (law sz)) {s t : ℕ → ℝ}
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1)
    (hev : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - t n) (hR : STReg5I sz s t)
    (hDec : STDecaygL C (law sz) s) (hExp : STExp2gL C (law sz) s) (hcon : STConStInd sz 𝔠d s t) :
    PrecL sz (law sz) (U := STIdx2P sz STSigSame s t)
      (fun n p _ => ‖Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ) (fun b => STExpErrg C (law sz) n (s n) p.2.1.1 b) p.2.2‖)
      (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := by
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have hs1 : ∀ n, s n < 1 := fun n => lt_trans (hst n) (ht1 n)
  have hX : ∀ n, 0 ≤ STExpTarget sz n (s n) := fun n => st6_target_nonneg sz n (hs1 n)
  have hlam0 : ∀ᶠ n in atTop, 0 ≤ sz.lam n := (st6_lam_pos sz hadm.2.2.2.2).mono fun n h => h.le
  have hWt := step34Gen_W_tendsto hadm
  have hA0 : 0 ≤ Aof κm := by linarith
  refine st6_precU_of_forall_seqg sz (law sz) hμ hsz (fun n => (hst n).le)
    (W := fun n => {σ : Fin 2 → Bool // STSigSame σ} × (Fin 2 → Zd d (sz.L n)))
    (fun n u w => ‖Step2Gen_UN C n w.1.1 (s n) u (fun b => STExpErrg C (law sz) n (s n) w.1.1 b) w.2‖)
    (fun n u _ => STExpTarget sz n u) ?_
  intro u hsu hut
  have hu1 : ∀ n, u n < 1 := fun n => lt_of_le_of_lt (hut n) (ht1 n)
  have hwin : STEKWinKgL sz gK s u :=
    step34Gen_winK_of_cmp hcmp (expIniI_window sz h𝔠d hdc hadm.2.2.2.2 hWt hs0 hst hsu hut ht1 hcon hR)
  have key : ∀ σ : {σ : Fin 2 → Bool // STSigSame σ}, PrecL sz (law sz) (U := fun n => Fin 2 → Zd d (sz.L n))
      (fun n a _ => ‖Step2Gen_UN C n σ.1 (s n) (u n) (fun b => STExpErrg C (law sz) n (s n) σ.1 b) a‖)
      (fun n _ _ => STExpTarget sz n (u n)) := by
    intro σ
    have hσ : ∃ k, σ.1 k = σ.1 (finRotate 2 k) := by
      refine ⟨0, ?_⟩
      have : finRotate 2 (0 : Fin 2) = 1 := by decide
      rw [this]; exact σ.2
    have hdec : STEKDecayKgL gK (law sz) s u (fun n _ _ => fun b => STExpErrg C (law sz) n (s n) σ.1 b) := by
      refine step34Gen_decayK_of_cmp hcmp hAof hWt (law sz) ?_
      intro ε' D hε' hD
      refine HighProbAt.of_eventually_univ ?_
      filter_upwards [expIniI_fastDecayg C (law sz) hd hκ' hδ hadm hμ hrep hmn hKb hs0 (fun n => (hst n).le) ht1 hev hDec
        ε' D hε' hD, hlam0] with n hn hl ω v
      exact expIniI_fastDecay_mono _ hl (Nat.cast_nonneg _) v.2.1 (lt_of_le_of_lt v.2.2 (hu1 n)) (hn σ.1)
    have hdom := st6_prec_pi_normg sz (law sz) hsz hX C hExp σ.1 (V := fun n => TimeIcc s u n)
    have hk := hSR hd 2 le_rfl κm 𝔠 𝔡 hκm sz hadm C gK hKer hg s u hwin σ.1 hσ
      (fun n _ _ => fun b => STExpErrg C (law sz) n (s n) σ.1 b) hdec
      (fun n _ _ => STExpTarget sz n (s n)) (ExpIniIGen_low (law sz) hs0 hs1) hdom
    have h2 := StochDomAt.precomp_param hk
      (fun n (_ : Fin 2 → Zd d (sz.L n)) => (⟨s n, le_rfl, hsu n⟩ : TimeIcc s u n))
    have h3 : PrecL sz (law sz) (U := fun n => Fin 2 → Zd d (sz.L n))
        (fun n a _ => ‖Step2Gen_UN C n σ.1 (s n) (u n) (fun b => STExpErrg C (law sz) n (s n) σ.1 b) a‖)
        (fun n _ _ => ((gK n ^ 2 + |1 - s n|) / (gK n ^ 2 + |1 - u n|)) ^ (2 - 1) * STExpTarget sz n (s n)) := by
      refine StochDomAt.of_le_left (ξ₁ := fun n (_ : Fin 2 → Zd d (sz.L n)) (_ : sz.SeqΩ) =>
        ‖Step2Gen_UN C n σ.1 (s n) (u n) (fun b => STExpErrg C (law sz) n (s n) σ.1 b)‖) (fun n a ω => ?_) h2
      exact norm_le_pi_norm (Step2Gen_UN C n σ.1 (s n) (u n) (fun b => STExpErrg C (law sz) n (s n) σ.1 b)) a
    refine Step5CasesGen_prec_mono sz (law sz) hsz (c := 2 * Aof κm) h3 (Eventually.of_forall fun n a ω => ?_)
      (fun n a ω => st6_target_nonneg sz n (hu1 n))
    have hx0 : 0 < 1 - u n := by linarith [hu1 n]
    have hxs : 0 ≤ 1 - s n := by linarith [hs1 n]
    have hden : 0 < sz.lam n ^ 2 + |1 - u n| := by
      rw [abs_of_pos hx0]; positivity
    have hratio : (sz.lam n ^ 2 + |1 - s n|) / (sz.lam n ^ 2 + |1 - u n|) ≤ 2 := by
      rw [div_le_iff₀ hden, abs_of_nonneg hxs, abs_of_pos hx0]
      nlinarith [(hR n).2, sq_nonneg (sz.lam n)]
    have hrg : (gK n ^ 2 + |1 - s n|) / (gK n ^ 2 + |1 - u n|) ≤ Aof κm * 2 :=
      (step34Gen_ratio_le hcmp hAof n (hu1 n)).trans (mul_le_mul_of_nonneg_left hratio hA0)
    have hTs := st6_target_mono sz n (hsu n) (hu1 n)
    have hT0 := hX n
    simp only [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    calc (gK n ^ 2 + |1 - s n|) / (gK n ^ 2 + |1 - u n|) * STExpTarget sz n (s n)
        ≤ (Aof κm * 2) * STExpTarget sz n (s n) := mul_le_mul_of_nonneg_right hrg hT0
      _ ≤ (Aof κm * 2) * STExpTarget sz n (u n) := mul_le_mul_of_nonneg_left hTs (by positivity)
      _ = 2 * Aof κm * STExpTarget sz n (u n) := by ring
  exact st6_prec_of_forall_fing sz (law sz) hsz
    (fun n (σ : {σ : Fin 2 → Bool // STSigSame σ}) (a : Fin 2 → Zd d (sz.L n)) (_ : sz.SeqΩ) =>
      ‖Step2Gen_UN C n σ.1 (s n) (u n) (fun b => STExpErrg C (law sz) n (s n) σ.1 b) a‖)
    (fun n _ _ _ => STExpTarget sz n (u n)) key

end Same

/-! ## 5. `σ₁ ≠ σ₂`: `lem_+Q` and `(sum_res_2)` (target 7) -/

section Mixed

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz)

/-- **The three inputs of `(sum_res_2)` for `𝒬_s f_s`** (deterministic, eventually; band `expIniI_Qop`, `ExpIniI:735`): (i) `‖𝒬_s f_s‖_∞ ≤ N^τ T_s` by `lem_+Q`
(`stQopNorm_holds`, `m = 1`, `Λ = 𝔡⁻¹`, `K = 1/𝔠`; `ε_Q = min(1/2, τ d/(4 C_n))`, `D_Q = C_n + 5/𝔠 + 1`) from `‖f_s‖ ≤ N^{τ/4} T_s` (`STExp2gL`) and the decay of `f_s`
(`expIniI_fastDecayg`); (ii) `(deccA0)` of `𝒬_s f_s = f_s - (f_s - 𝒬_s f_s)` (`expIniI_fastDecayg`, `stQop_sub_fastDecay`, `‖f_s‖ ≤ N⁶ ≤ W^{6/𝔠}`); (iii) `(sumAzero)`
(`𝒫 ∘ 𝒬_s = 0`, `QopAlgebra_Psum_Qop`).  Positive mollifier constants: both lemmas of `lem_+Q` use `0 < c`. -/
theorem expIniI_Qopg (μ : Measure sz.SeqΩ) (hd : 3 ≤ d) {κ' δ 𝔠 𝔡 : ℝ} (hκ' : 0 < κ') (hδ : 0 < δ) (hadm : sz.Admissible 𝔠 𝔡)
    (hμ : IsProbabilityMeasure μ) {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    (hrep : CltRepg C μ H₀ g' E) (hmn : ∀ n, κ' ≤ (C.m n).im) (hKb : STKboundgL C μ) {s T : ℕ → ℝ}
    (hs0 : ∀ n, 0 ≤ s n) (hsT : ∀ n, s n ≤ T n) (hT1 : ∀ n, T n < 1)
    (hev : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - T n) (hDec : STDecaygL C μ s) (hExp : STExp2gL C μ s)
    (Cq c : ℝ) (hC : 0 < Cq) (hc : 0 < c) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ)
    (hϑ : ∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) Cq c (ϑ n)) :
    (∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool,
      ‖STQop (d := d) (ϑ n) (s n) (fun b => STExpErrg C μ n (s n) σ b)‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * STExpTarget sz n (s n)) ∧
    (∀ ε' D : ℝ, 0 < ε' → 0 < D → ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool,
      EKFastDecay (sz.lam n) (s n) ((sz.W n : ℕ) : ℝ) ε' D
        (STQop (d := d) (ϑ n) (s n) (fun b => STExpErrg C μ n (s n) σ b))) ∧
    (∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool,
      EKSumZero (STQop (d := d) (ϑ n) (s n) (fun b => STExpErrg C μ n (s n) σ b))) := by
  obtain ⟨h𝔠, h𝔡, hSz, hBw, hWO⟩ := id hadm
  have hs1 : ∀ n, s n < 1 := fun n => (hsT n).trans_lt (hT1 n)
  have hd0 : 0 < d := by omega
  have hd0' : (0 : ℝ) < d := by exact_mod_cast hd0
  have hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := step34Gen_band_hg hadm
  have hWt : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := step34Gen_W_tendsto hadm
  have hf1 := fun ε' D (hε' : 0 < ε') (hD : 0 < D) =>
    expIniI_fastDecayg C μ hd hκ' hδ hadm hμ hrep hmn hKb hs0 hsT hT1 hev hDec ε' D hε' hD
  refine ⟨?_, ?_, ?_⟩
  · -- (i) `lem_+Q`
    intro τ hτ
    obtain ⟨Cn, hCn, hpin⟩ := stQopNorm_holds d hd 1 𝔡⁻¹ (1 / 𝔠) Cq c (inv_pos.2 h𝔡) (one_div_pos.2 h𝔠) hC hc
    set εQ : ℝ := min (1 / 2) (τ * d / (4 * Cn)) with hεQ
    have hεQ0 : 0 < εQ := lt_min (by norm_num) (by positivity)
    have hεQ1 : εQ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    set DQ : ℝ := Cn + 5 / 𝔠 + 1 with hDQ
    have h5c' : 0 < 5 / 𝔠 := by positivity
    have hDQ1 : 1 < DQ := by rw [hDQ]; linarith
    have hExpD := (st6_prec_det_iffg sz μ hμ hSz (V := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p => ‖STExpErrg C μ n (s n) p.1 p.2‖)
      (fun n _ => (sz.Bctl n (s n)) ^ 2 *
        ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n (s n)))).1 hExp (τ / 4) (by positivity)
    filter_upwards [hϑ, hf1 εQ DQ hεQ0 (by linarith), hExpD, hBw, hlam,
      expIniI_W_rpow_ge sz h𝔠 hSz hBw hεQ0 4, hSz.eventually (eventually_ge_atTop (1 : ℝ)),
      ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < τ / 2)).comp hSz).eventually (eventually_ge_atTop (2 : ℝ))]
      with n hϑn hfn hExpn hBn hlamn h4 hN1 hN2 σ
    set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
    set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
    have hN0 : 0 < N := by linarith
    have hW0 : 0 ≤ W := Nat.cast_nonneg _
    have hW1 : 1 < W := by
      by_contra hcon
      push Not at hcon
      have := Real.rpow_le_one hW0 hcon hεQ0.le
      linarith
    have hLW : ((sz.L n : ℕ) : ℝ) ^ d ≤ W ^ (1 / 𝔠) := expIniI_L_pow_le sz h𝔠 n hBn
    have hQ := hpin (sz.L n) (sz.three_le_L n) (sz.lam n) hlamn.1 hlamn.2 W εQ DQ hW1 hεQ0 hεQ1 hDQ1 h4 hLW
      (ϑ n) hϑn (s n) (hs0 n) (hs1 n) (fun b => STExpErrg C μ n (s n) σ b) (hfn σ)
    have hT0 : 0 ≤ STExpTarget sz n (s n) := st6_target_nonneg sz n (hs1 n)
    have hfnorm : ‖(fun b => STExpErrg C μ n (s n) σ b)‖ ≤ N ^ (τ / 4) * STExpTarget sz n (s n) :=
      (pi_norm_le_iff_of_nonneg (mul_nonneg (Real.rpow_nonneg hN0.le _) hT0)).2 fun a => hExpn (σ, a)
    have hWC : W ^ (Cn * εQ) ≤ N ^ (τ / 4) := by
      have h1 : W ^ (Cn * εQ) ≤ N ^ (Cn * εQ / d) := sz.W_rpow_le hd0 n (by positivity)
      refine h1.trans (Real.rpow_le_rpow_of_exponent_le hN1 ?_)
      rw [div_le_iff₀ hd0']
      have : Cn * εQ ≤ Cn * (τ * d / (4 * Cn)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hCn.le
      have e : Cn * (τ * d / (4 * Cn)) = τ / 4 * d := by field_simp
      linarith
    have hTail : W ^ (-DQ + Cn) ≤ N ^ (-(5 : ℝ)) := by
      have hexp : -DQ + Cn ≤ -(5 / 𝔠) := by rw [hDQ]; linarith
      have h1 : W ^ (-DQ + Cn) ≤ W ^ (-(5 / 𝔠)) := Real.rpow_le_rpow_of_exponent_le hW1.le hexp
      have hNc : 0 < N ^ 𝔠 := Real.rpow_pos_of_pos hN0 _
      have h5c : 0 < 5 / 𝔠 := by positivity
      have h2 : W ^ (-(5 / 𝔠)) ≤ (N ^ 𝔠) ^ (-(5 / 𝔠)) :=
        Real.rpow_le_rpow_of_nonpos hNc hBn (by linarith)
      have h3 : (N ^ 𝔠) ^ (-(5 / 𝔠)) = N ^ (-(5 : ℝ)) := by
        rw [← Real.rpow_mul hN0.le]; congr 1; field_simp
      exact h1.trans (h2.trans h3.le)
    have hN35 : N ^ (-(5 : ℝ)) ≤ N ^ (-(3 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
    have hTs : N ^ (-(3 : ℝ)) ≤ STExpTarget sz n (s n) := expIniI_Ts_ge sz n (hs0 n) (hs1 n)
    have hxx : N ^ (τ / 2) * N ^ (τ / 2) = N ^ τ := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have hyy : N ^ (τ / 4) * N ^ (τ / 4) = N ^ (τ / 2) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    set x : ℝ := N ^ (τ / 2) with hx
    set T' : ℝ := STExpTarget sz n (s n) with hT
    have ha : W ^ (Cn * εQ) * ‖(fun b => STExpErrg C μ n (s n) σ b)‖ ≤ x * T' := by
      calc W ^ (Cn * εQ) * ‖(fun b => STExpErrg C μ n (s n) σ b)‖
          ≤ N ^ (τ / 4) * (N ^ (τ / 4) * T') :=
            mul_le_mul hWC hfnorm (norm_nonneg _) (Real.rpow_nonneg hN0.le _)
        _ = x * T' := by rw [← mul_assoc, hyy]
    have hkey : x * x * T' - x * T' - T' = T' * (x * x - x - 1) := by ring
    have hN2' : 2 ≤ x := hN2
    have hpos : 0 ≤ x * x - x - 1 := by nlinarith
    calc ‖STQop (d := d) (ϑ n) (s n) (fun b => STExpErrg C μ n (s n) σ b)‖
        ≤ W ^ (Cn * εQ) * ‖(fun b => STExpErrg C μ n (s n) σ b)‖ + W ^ (-DQ + Cn) := hQ
      _ ≤ x * T' + T' := add_le_add ha (hTail.trans (hN35.trans hTs))
      _ ≤ N ^ τ * T' := by
        rw [← hxx]; nlinarith [mul_nonneg hT0 hpos]
  · -- (ii) `(deccA0)` of `𝒬_s f_s`
    intro ε' D hε' hD
    obtain ⟨W₀, hW₀1, hW₀⟩ := stQop_sub_fastDecay d 1 (1 / 𝔠) Cq c (6 / 𝔠) ε' (D + 1) hC hc hε'
    filter_upwards [hϑ, hf1 ε' (D + 1) hε' (by linarith), ExpIniIGen_env_poly C μ hκ' hδ hadm hμ hrep hmn hKb hs0 hsT hT1 hev,
      hBw, hlam, hWt.eventually (eventually_ge_atTop (max W₀ 2))] with n hϑn hfn henv hBn hlamn hWn σ
    intro a ⟨i, j, hij⟩
    set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
    have hW0 : W₀ ≤ W := (le_max_left _ _).trans hWn
    have hW2 : 2 ≤ W := (le_max_right _ _).trans hWn
    have hWpos : 0 < W := by linarith
    have hLW : ((sz.L n : ℕ) : ℝ) ^ d ≤ W ^ (1 / 𝔠) := expIniI_L_pow_le sz h𝔠 n hBn
    have hA : ‖(fun b => STExpErrg C μ n (s n) σ b)‖ ≤ W ^ (6 / 𝔠) :=
      (henv σ).trans (sz.size_rpow_le_W_rpow h𝔠 n hBn (τ := 6) (by positivity))
    have h1 := hfn σ a ⟨i, j, hij⟩
    have h2 := hW₀ (sz.L n) (sz.three_le_L n) (sz.lam n) hlamn.1 W hW0 hLW (ϑ n) hϑn (s n) (hs0 n) (hs1 n)
      (fun b => STExpErrg C μ n (s n) σ b) hA a ⟨i, j, hij⟩
    change ‖STQop (d := d) (ϑ n) (s n) (fun b => STExpErrg C μ n (s n) σ b) a‖ ≤ W ^ (-D)
    have e : STQop (d := d) (ϑ n) (s n) (fun b => STExpErrg C μ n (s n) σ b) a =
        STExpErrg C μ n (s n) σ a -
          ((fun b => STExpErrg C μ n (s n) σ b) -
            STQop (d := d) (ϑ n) (s n) (fun b => STExpErrg C μ n (s n) σ b)) a := by
      simp only [Pi.sub_apply]; ring
    rw [e]
    have hWD : W ^ (-(D + 1)) = W ^ (-D) * W⁻¹ := by
      rw [show -(D + 1) = -D + (-1) by ring, Real.rpow_add hWpos, Real.rpow_neg_one]
    have hWi : W⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hW2
    have hWD0 : 0 < W ^ (-D) := Real.rpow_pos_of_pos hWpos _
    calc ‖STExpErrg C μ n (s n) σ a -
          ((fun b => STExpErrg C μ n (s n) σ b) -
            STQop (d := d) (ϑ n) (s n) (fun b => STExpErrg C μ n (s n) σ b)) a‖
        ≤ ‖STExpErrg C μ n (s n) σ a‖ +
          ‖((fun b => STExpErrg C μ n (s n) σ b) -
            STQop (d := d) (ϑ n) (s n) (fun b => STExpErrg C μ n (s n) σ b)) a‖ := norm_sub_le _ _
      _ ≤ 2 * W ^ (-(D + 1)) := by linarith
      _ = 2 * (W ^ (-D) * W⁻¹) := by rw [hWD]
      _ ≤ 2 * (W ^ (-D) * (1 / 2)) := by gcongr
      _ = W ^ (-D) := by ring
  · -- (iii) `(sumAzero)`
    filter_upwards [hϑ] with n hn σ
    intro i₀ hi₀ x
    have : i₀ = 0 := Fin.ext hi₀
    subst this
    exact QopAlgebra_Psum_Qop (ϑ n) (hn.1 (s n)) _ x

open Classical in
/-- **`(sum_res_2)` applied to `𝒬_s f_s`** (`3_5:1659`; band `expIniI_mixed`, `ExpIniI:892`): for `σ₁ ≠ σ₂`, regime (i), positive mollifier constants, `𝒰_{s,u,σ} 𝒬_s f_s ≺ T_u` uniformly in
`u ∈ [s,t]`: the three inputs are `expIniI_Qopg`; the kernel pin `STEKSumRes2gL` asks `(sumAzero)` for every `n` while the mollifier hypothesis is eventual, so the tensor is
`if STMollifierProps … then 𝒬_s f_s else 0` (equal to `𝒬_s f_s` eventually); the window, the decay class and the ratio are read through R1 as in `expIniI_sameg` (ratio `≤ (A · 2)²`).
The second conjunct of `STExpIniIConclgL'`. -/
theorem expIniI_mixedg {law : ∀ sz : Sizes d, Measure sz.SeqΩ} {Ker : STEKKer d} {Aof : ℝ → ℝ}
    (hSR2 : STEKSumRes2gL d law Ker) (hd : 3 ≤ d) {κm κ' δ 𝔠 𝔡 𝔠d : ℝ} (hκm : 0 < κm) (hAof : 1 ≤ Aof κm)
    (h𝔠d : 0 < 𝔠d) (hdc : (d : ℝ) * 𝔠d < 1) (hκ' : 0 < κ') (hδ : 0 < δ) (hadm : sz.Admissible 𝔠 𝔡)
    (gK : ℕ → ℝ) (hKer : Ker sz C gK κm) (hg : ∀ᶠ n in atTop, 0 < gK n ∧ gK n ≤ 𝔡⁻¹)
    (hcmp : ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ Aof κm * gK n ^ 2)
    (hμ : IsProbabilityMeasure (law sz))
    {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    (hrep : CltRepg C (law sz) H₀ g' E) (hmn : ∀ n, κ' ≤ (C.m n).im) (hKb : STKboundgL C (law sz)) {s t : ℕ → ℝ}
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1)
    (hev : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - t n) (hR : STReg5I sz s t)
    (hDec : STDecaygL C (law sz) s) (hExp : STExp2gL C (law sz) s) (hcon : STConStInd sz 𝔠d s t)
    (Cq c : ℝ) (hC : 0 < Cq) (hc : 0 < c) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ)
    (hϑ : ∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) Cq c (ϑ n)) :
    PrecL sz (law sz) (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ)
        (STQop (d := d) (ϑ n) (s n) (fun b => STExpErrg C (law sz) n (s n) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := by
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have hs1 : ∀ n, s n < 1 := fun n => lt_trans (hst n) (ht1 n)
  have hX : ∀ n, 0 ≤ STExpTarget sz n (s n) := fun n => st6_target_nonneg sz n (hs1 n)
  have hlam0 : ∀ᶠ n in atTop, 0 ≤ sz.lam n := (st6_lam_pos sz hadm.2.2.2.2).mono fun n h => h.le
  have hWt := step34Gen_W_tendsto hadm
  have hA0 : 0 ≤ Aof κm := by linarith
  obtain ⟨hQ1, hQ2, hQ3⟩ := expIniI_Qopg C (law sz) hd hκ' hδ hadm hμ hrep hmn hKb hs0 (fun n => (hst n).le) ht1 hev hDec hExp
    Cq c hC hc ϑ hϑ
  refine st6_precU_of_forall_seqg sz (law sz) hμ hsz (fun n => (hst n).le)
    (W := fun n => {σ : Fin 2 → Bool // STSigMixed σ} × (Fin 2 → Zd d (sz.L n)))
    (fun n u w => ‖Step2Gen_UN C n w.1.1 (s n) u
      (STQop (d := d) (ϑ n) (s n) (fun b => STExpErrg C (law sz) n (s n) w.1.1 b)) w.2‖)
    (fun n u _ => STExpTarget sz n u) ?_
  intro u hsu hut
  have hu1 : ∀ n, u n < 1 := fun n => lt_of_le_of_lt (hut n) (ht1 n)
  have hwin : STEKWinKgL sz gK s u :=
    step34Gen_winK_of_cmp hcmp (expIniI_window sz h𝔠d hdc hadm.2.2.2.2 hWt hs0 hst hsu hut ht1 hcon hR)
  have key : ∀ σ : {σ : Fin 2 → Bool // STSigMixed σ}, PrecL sz (law sz) (U := fun n => Fin 2 → Zd d (sz.L n))
      (fun n a _ => ‖Step2Gen_UN C n σ.1 (s n) (u n)
        (STQop (d := d) (ϑ n) (s n) (fun b => STExpErrg C (law sz) n (s n) σ.1 b)) a‖)
      (fun n _ _ => STExpTarget sz n (u n)) := by
    intro σ
    -- the tensor of the kernel pin: `𝒬_s f_s` where the mollifier hypothesis holds, `0` elsewhere
    let Q0 : ∀ n, (Fin 2 → Zd d (sz.L n)) → ℂ := fun n =>
      if STMollifierProps (d := d) (sz.lam n) Cq c (ϑ n) then
        STQop (d := d) (ϑ n) (s n) (fun b => STExpErrg C (law sz) n (s n) σ.1 b) else 0
    let 𝒜 : ∀ n, TimeIcc s u n → sz.SeqΩ → (Fin 2 → Zd d (sz.L n)) → ℂ := fun n _ _ => Q0 n
    have hQ0 : ∀ n, STMollifierProps (d := d) (sz.lam n) Cq c (ϑ n) →
        Q0 n = STQop (d := d) (ϑ n) (s n) (fun b => STExpErrg C (law sz) n (s n) σ.1 b) :=
      fun n hn => by simp [Q0, hn]
    have hdec : STEKDecayKgL gK (law sz) s u 𝒜 := by
      refine step34Gen_decayK_of_cmp hcmp hAof hWt (law sz) ?_
      intro ε' D hε' hD
      refine HighProbAt.of_eventually_univ ?_
      filter_upwards [hQ2 ε' D hε' hD, hϑ, hlam0] with n hn hϑn hl ω v
      change EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε' D (Q0 n)
      rw [hQ0 n hϑn]
      exact expIniI_fastDecay_mono _ hl (Nat.cast_nonneg _) v.2.1 (lt_of_le_of_lt v.2.2 (hu1 n)) (hn σ.1)
    have hzero : ∀ n v ω, EKSumZero (𝒜 n v ω) := by
      intro n v ω
      change EKSumZero (Q0 n)
      by_cases hn : STMollifierProps (d := d) (sz.lam n) Cq c (ϑ n)
      · rw [hQ0 n hn]
        intro i₀ hi₀ x
        have : i₀ = 0 := Fin.ext hi₀
        subst this
        exact QopAlgebra_Psum_Qop (ϑ n) (hn.1 (s n)) _ x
      · have : Q0 n = 0 := by simp [Q0, hn]
        rw [this]
        intro i₀ hi₀ x
        simp
    have hdom : PrecL sz (law sz) (U := fun n => TimeIcc s u n) (fun n v ω => ‖𝒜 n v ω‖)
        (fun n _ _ => STExpTarget sz n (s n)) := by
      refine (st6_prec_det_iffg sz (law sz) hμ hsz (V := fun n => TimeIcc s u n)
        (fun n _ => ‖Q0 n‖) (fun n _ => STExpTarget sz n (s n))).2 ?_
      intro τ hτ
      filter_upwards [hQ1 τ hτ, hϑ] with n hn hϑn v
      rw [hQ0 n hϑn]
      exact hn σ.1
    have hk := hSR2 hd 2 le_rfl κm 𝔠 𝔡 hκm sz hadm C gK hKer hg s u hwin σ.1 𝒜 hdec hzero
      (fun n _ _ => STExpTarget sz n (s n)) (ExpIniIGen_low (law sz) hs0 hs1) hdom
    have h2 := StochDomAt.precomp_param hk
      (fun n (_ : Fin 2 → Zd d (sz.L n)) => (⟨s n, le_rfl, hsu n⟩ : TimeIcc s u n))
    have h3 : PrecL sz (law sz) (U := fun n => Fin 2 → Zd d (sz.L n))
        (fun n a _ => ‖Step2Gen_UN C n σ.1 (s n) (u n)
          (STQop (d := d) (ϑ n) (s n) (fun b => STExpErrg C (law sz) n (s n) σ.1 b)) a‖)
        (fun n _ _ => ((gK n ^ 2 + |1 - s n|) / (gK n ^ 2 + |1 - u n|)) ^ 2 * STExpTarget sz n (s n)) := by
      refine StochDomAt.of_subset (ξ₁ := fun n (_ : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) =>
        ‖Step2Gen_UN C n σ.1 (s n) (u n) (Q0 n)‖)
        (ζ₁ := fun n _ _ => ((gK n ^ 2 + |1 - s n|) / (gK n ^ 2 + |1 - u n|)) ^ 2 * STExpTarget sz n (s n))
        h2 (fun τ hτ => ⟨τ, hτ, ?_⟩)
      filter_upwards [hϑ] with n hn ω ⟨a, ha⟩
      refine ⟨a, lt_of_lt_of_le ha ?_⟩
      change ‖Step2Gen_UN C n σ.1 (s n) (u n)
          (STQop (d := d) (ϑ n) (s n) (fun b => STExpErrg C (law sz) n (s n) σ.1 b)) a‖ ≤
        ‖Step2Gen_UN C n σ.1 (s n) (u n) (Q0 n)‖
      rw [hQ0 n hn]
      exact norm_le_pi_norm (Step2Gen_UN C n σ.1 (s n) (u n)
        (STQop (d := d) (ϑ n) (s n) (fun b => STExpErrg C (law sz) n (s n) σ.1 b))) a
    refine Step5CasesGen_prec_mono sz (law sz) hsz (c := 4 * Aof κm ^ 2) h3 (Eventually.of_forall fun n a ω => ?_)
      (fun n a ω => st6_target_nonneg sz n (hu1 n))
    have hx0 : 0 < 1 - u n := by linarith [hu1 n]
    have hxs : 0 ≤ 1 - s n := by linarith [hs1 n]
    have hden : 0 < sz.lam n ^ 2 + |1 - u n| := by
      rw [abs_of_pos hx0]; positivity
    have hratio : (sz.lam n ^ 2 + |1 - s n|) / (sz.lam n ^ 2 + |1 - u n|) ≤ 2 := by
      rw [div_le_iff₀ hden, abs_of_nonneg hxs, abs_of_pos hx0]
      nlinarith [(hR n).2, sq_nonneg (sz.lam n)]
    have hrg : (gK n ^ 2 + |1 - s n|) / (gK n ^ 2 + |1 - u n|) ≤ Aof κm * 2 :=
      (step34Gen_ratio_le hcmp hAof n (hu1 n)).trans (mul_le_mul_of_nonneg_left hratio hA0)
    have hr0 : 0 ≤ (gK n ^ 2 + |1 - s n|) / (gK n ^ 2 + |1 - u n|) := by positivity
    have hr2 : ((gK n ^ 2 + |1 - s n|) / (gK n ^ 2 + |1 - u n|)) ^ 2 ≤ 4 * Aof κm ^ 2 := by
      calc ((gK n ^ 2 + |1 - s n|) / (gK n ^ 2 + |1 - u n|)) ^ 2 ≤ (Aof κm * 2) ^ 2 := pow_le_pow_left₀ hr0 hrg 2
        _ = 4 * Aof κm ^ 2 := by ring
    have hTs := st6_target_mono sz n (hsu n) (hu1 n)
    have hT0 := hX n
    calc ((gK n ^ 2 + |1 - s n|) / (gK n ^ 2 + |1 - u n|)) ^ 2 * STExpTarget sz n (s n)
        ≤ (4 * Aof κm ^ 2) * STExpTarget sz n (s n) := mul_le_mul_of_nonneg_right hr2 hT0
      _ ≤ (4 * Aof κm ^ 2) * STExpTarget sz n (u n) := mul_le_mul_of_nonneg_left hTs (by positivity)
  exact st6_prec_of_forall_fing sz (law sz) hsz
    (fun n (σ : {σ : Fin 2 → Bool // STSigMixed σ}) (a : Fin 2 → Zd d (sz.L n)) (_ : sz.SeqΩ) =>
      ‖Step2Gen_UN C n σ.1 (s n) (u n)
        (STQop (d := d) (ϑ n) (s n) (fun b => STExpErrg C (law sz) n (s n) σ.1 b)) a‖)
    (fun n _ _ _ => STExpTarget sz n (u n)) key

end Mixed

/-! ## 6. The pin `STExpIniIgL'` (target 8) -/

/-- **Target 8, the pin `STExpIniIgL'`** (band `stExpIniI'_holds`, `ExpIniI:1106`) from the family premises: probability law (row 1), flow facts (row 3), the class
`IniTermGen_CltFlow` (row 9': `κ' ≤ Im m`, `N^{-1+δ} ≤ 1 - T0`, `CltRepg`; BA `baIniTermGen_cltFlow`), `STKboundgL` along the flow (row 17; BA `baKbound_holds`), the kernel pins
`STEKSumRes2NALgL`, `STEKSumRes2gL` with the class `Ker` at the coupling `gK`, the comparison R1 `∃ A` (written `Aof κm`, `κm` before `(sz, z)`) (row 16; U3-BA (a)).  The constant is
`𝔠_d = 1/(100 d)` (`𝔠_d ≤ 1/100`, `d 𝔠_d = 1/100 < 1`): the first conjunct is `expIniI_sameg`, the second is `expIniI_mixedg`. -/
theorem stExpIniIgL'_of {d : ℕ} {law : ∀ sz : Sizes d, Measure sz.SeqΩ}
    {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop} {mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz}
    {T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ} {Ker : STEKKer d} {Aof : ℝ → ℝ}
    (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hμ : ∀ sz, IsProbabilityMeasure (law sz))
    (hFF : Step5CasesGen_FlowFacts d Flow mk T0) (hClt : IniTermGen_CltFlow d law Flow mk T0)
    (hKb : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → STKboundgL (mk sz z) (law sz))
    (hSR : STEKSumRes2NALgL d law Ker) (hSR2 : STEKSumRes2gL d law Ker) (hAof : ∀ κm : ℝ, 0 < κm → 1 ≤ Aof κm)
    (hKer : ∀ κ : ℝ, 0 < κ → ∃ κm : ℝ, 0 < κm ∧ ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      (∀ n, κm ≤ ((mk sz z).m n).im) ∧ Ker sz (mk sz z) (gK sz z) κm ∧ (∀ᶠ n in atTop, 0 < gK sz z n ∧ gK sz z n ≤ 𝔡⁻¹) ∧
        ∀ n, 0 ≤ gK sz z n * sz.lam n ∧ gK sz z n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ Aof κm * gK sz z n ^ 2) :
    STExpIniIgL' d law Flow mk T0 := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have h𝔠d : 0 < 1 / (100 * (d : ℝ)) := by positivity
  have hdc : (d : ℝ) * (1 / (100 * (d : ℝ))) < 1 := by
    rw [show (d : ℝ) * (1 / (100 * (d : ℝ))) = 1 / 100 by field_simp]; norm_num
  obtain ⟨κ', δ, hκ', -, hδ, HC⟩ := hClt hd κ ε 𝔡 hκ hε h𝔡
  refine ⟨1 / (100 * (d : ℝ)), h𝔠d, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  · intro 𝔠 sz z hflow s t hs0 hst htT hR _ hDec hExp hcon _ _ _ _
    obtain ⟨_, _, hFl⟩ := hFF κ hκ
    obtain ⟨hadm, hT0, -, -⟩ := hFl sz ε 𝔠 𝔡 z hflow
    obtain ⟨κm, hκm, hKF⟩ := hKer κ hκ
    obtain ⟨-, hKer', hg', hR1'⟩ := hKF sz ε 𝔠 𝔡 z hflow
    obtain ⟨H₀, g', E, hm', hev', hrep, -⟩ := HC 𝔠 sz z hflow
    have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (hT0 n)
    have hev : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - t n :=
      hev'.mono fun n hn => hn.trans (by linarith [htT n])
    exact ⟨expIniI_sameg (mk sz z) hSR hd hκm (hAof κm hκm) h𝔠d hdc hκ' hδ hadm (gK sz z) hKer' hg' hR1' (hμ sz) hrep hm'
        (hKb sz κ ε 𝔠 𝔡 z hκ hflow) hs0 hst ht1 hev hR hDec hExp hcon,
      fun Cq c hC hc ϑ hϑ => expIniI_mixedg (mk sz z) hSR2 hd hκm (hAof κm hκm) h𝔠d hdc hκ' hδ hadm (gK sz z) hKer' hg' hR1'
        (hμ sz) hrep hm' (hKb sz κ ε 𝔠 𝔡 z hκ hflow) hs0 hst ht1 hev hR hDec hExp hcon Cq c hC hc ϑ hϑ⟩

/-! ## 7. The band re-derivation -/

open private Step6KitGen_KerFR1_band from RBM3D.Chain.Step6KitGen

/-- `STKboundgL` along a band flow (`d ≥ 3`): the merged `stKbound_holds` at `E = STflowE z`, `gmax = 𝔡⁻¹` (`|E n| ≤ 2 - κ` from the flow, `0 < lam ≤ 𝔡⁻¹` from `WO`). -/
private theorem ExpIniIGen_Kb_band {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) (hκ : 0 < κ)
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) : STKboundgL (bandFM sz (STflowE z)) (Sizes.seqP sz) := by
  have him : ∀ n, 0 < (z n).im := fun n =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.one_le_size n) _) (hflow.2 n).2.1
  exact stKbound_holds sz hd (E := STflowE z) (κ := κ) (gmax := 𝔡⁻¹) hκ (inv_pos.2 hflow.1.2.1) hflow.1.2.2.1
    (Eventually.of_forall fun n => (abs_lemE_le (him n)).trans (hflow.2 n).1) (step34Gen_band_hg hflow.1)

/-- **Band `stExpIniI'_holds` re-derived** (`ExpIniI:1106`) from `stExpIniIgL'_of` through `STExpIniI'_iff_gL'`: the premises at the band tuple are the merged
`step5CasesGen_flowFacts_band`, `iniTermGen_cltFlow_band`, `stKbound_holds`, `stek_sumRes2NALgL_band`, `stek_sumRes2gL_band` and the class `STEKBandKer` with `gK = sz.lam`, `Aof = 1`. -/
theorem stExpIniI'_gen_band (d : ℕ) : STExpIniI' d := fun hd =>
  ((STExpIniI'_iff_gL' d).2 (stExpIniIgL'_of (Ker := @STEKBandKer d) (Aof := fun _ => 1) (fun sz _ => sz.lam)
    (fun sz => inferInstance) (step5CasesGen_flowFacts_band d) (iniTermGen_cltFlow_band d)
    (fun sz κ ε 𝔠 𝔡 z hκ hflow => ExpIniIGen_Kb_band hd sz κ ε 𝔠 𝔡 z hκ hflow) (stek_sumRes2NALgL_band d)
    (stek_sumRes2gL_band d) (fun _ _ => le_rfl) Step6KitGen_KerFR1_band)) hd

/-! ## 8. Compiled nonempty instances at `d = 3` (regime (i) data of the band: `szB`, `zB`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `(s, t) = (7/8, 15/16)`, `𝔠_d = 1/300`)

`szB`: `L = 4`, `W_n = n + 4`, `lam = 1`; `1/16 = lam²/L² ≤ 1 - t = 1/16 ≤ 1 - s = 1/8 ≤ lam² = 1`.  Discharged: flow, times, regime, `(con_st_ind)` (`conStInd_const`), admissibility,
probability law, flow facts, the class `IniTermGen_CltFlow` (`iniTermGen_cltFlow_band`: `κ'`, `δ`, `CltRepg`, the range `N^{-1+δ} ≤ 1 - T0`), `STKboundgL` (`stKbound_holds`), the kernel pins
`stek_sumRes2NALgL_band`, `stek_sumRes2gL_band`, the class `STEKBandKer` with `gK = lam`, R1 at `Aof = 1`, the mollifier family `st6_mollifier_familyg`.  What stays a hypothesis is
`STDecaygL`, `STExp2gL` at `s ≡ 7/8` (`(Eq:Gdecay+IND)`, `(Eq:Gtlp_exp+IND)`: stochastic premises of other gates). -/

section Instances

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst RBM.Gauss.Step5Inst RBM.Gauss.Step6Inst

/-- The row-9' data of the band flow `zB` at the time `T ≡ 15/16`: `κ'`, `δ`, `H₀ = 0`, `g' = lam`, `E`, `κ' ≤ Im m`, the range and `CltRepg`. -/
private theorem ExpIniIGen_bandData :
    ∃ (κ' δ : ℝ) (H₀ : ∀ n, Matrix (Idx 3 (szB.L n) (szB.W n)) (Idx 3 (szB.L n) (szB.W n)) ℂ) (g' E : ℕ → ℝ),
      0 < κ' ∧ 0 < δ ∧ (∀ n, κ' ≤ ((bandFM szB (STflowE zB)).m n).im) ∧
      (∀ᶠ n in atTop, ((szB.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - (15 / 16 : ℝ)) ∧
      CltRepg (bandFM szB (STflowE zB)) (Sizes.seqP szB) H₀ g' E := by
  obtain ⟨κ', δ, hκ', -, hδ, HC⟩ := iniTermGen_cltFlow_band 3 (by norm_num) (1 / 10) (1 / 10) (1 / 10) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨H₀, g', E, hm', hev', hrep, -⟩ := HC (1 / 6) szB zB flow_zB
  refine ⟨κ', δ, H₀, g', E, hκ', hδ, hm', hev'.mono fun n hn => hn.trans ?_, hrep⟩
  have := szB_flow_ht (t0 := 15 / 16) (by norm_num) n
  linarith

/-- **Target 6**: the bridge of the conclusion and of the pin at the band data. -/
example (h : STExpIniIConcl' szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16)) :
    STExpIniIConclgL' (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  (bandFM_STExpIniIConcl' szB (STflowE zB) _ _).1 h

example (h : STExpIniIgL' 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) :
    InstIng6Concl (fun sz E s t => STExpIniIConcl' sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_ing6_I STReg5I _ ((STExpIniI'_iff_gL' 3).2 h) szB_reg5I

/-- **`expIniI_fastDecayg`** at `(szB, zB, s ≡ 7/8, T ≡ 15/16)`: the stochastic premise `STDecaygL` at `s` stays a hypothesis. -/
example (hDec : STDecaygL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8)) (ε' D : ℝ) (hε' : 0 < ε') (hD : 0 < D) :
    ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool,
      EKFastDecay (szB.lam n) (7 / 8) ((szB.W n : ℕ) : ℝ) ε' D
        (fun b => STExpErrg (bandFM szB (STflowE zB)) (Sizes.seqP szB) n (7 / 8) σ b) := by
  obtain ⟨κ', δ, H₀, g', E, hκ', hδ, hm', hev, hrep⟩ := ExpIniIGen_bandData
  exact expIniI_fastDecayg (bandFM szB (STflowE zB)) (Sizes.seqP szB) (by norm_num) hκ' hδ szB_admissible inferInstance hrep hm'
    (ExpIniIGen_Kb_band (by norm_num) szB (1 / 10) (1 / 10) (1 / 6) (1 / 10) zB (by norm_num) flow_zB) (fun _ => by norm_num)
    (fun _ => by norm_num) (fun _ => by norm_num) hev hDec ε' D hε' hD

/-- **`expIniI_sameg`** at `(szB, zB, 7/8, 15/16)`, `𝔠_d = 1/300`: the kernel pin is the proved `stek_sumRes2NALgL_band` (class `STEKBandKer` at `κm = √(2κ)/2`, `gK = lam`, R1
at `A = 1`); the stochastic premises stay hypotheses. -/
example (hDec : STDecaygL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8))
    (hExp : STExp2gL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8)) :
    PrecL szB (Sizes.seqP szB) (U := STIdx2P szB STSigSame (fun _ => 7 / 8) (fun _ => 15 / 16))
      (fun n p _ => ‖Step2Gen_UN (bandFM szB (STflowE zB)) n p.2.1.1 (7 / 8) (p.1 : ℝ)
        (fun b => STExpErrg (bandFM szB (STflowE zB)) (Sizes.seqP szB) n (7 / 8) p.2.1.1 b) p.2.2‖)
      (fun n p _ => STExpTarget szB n (p.1 : ℝ)) := by
  obtain ⟨κ', δ, H₀, g', E, hκ', hδ, hm', hev, hrep⟩ := ExpIniIGen_bandData
  obtain ⟨κm, hκm, H⟩ := Step6KitGen_KerFR1_band (d := 3) (1 / 10) (by norm_num)
  obtain ⟨-, hKer, hg, hR1⟩ := H szB (1 / 10) (1 / 6) (1 / 10) zB flow_zB
  exact expIniI_sameg (bandFM szB (STflowE zB)) (Aof := fun _ => 1) (stek_sumRes2NALgL_band 3) (by norm_num) hκm le_rfl
    (𝔠d := 1 / 300) (by norm_num) (by norm_num) hκ' hδ szB_admissible szB.lam hKer hg hR1 inferInstance hrep hm'
    (ExpIniIGen_Kb_band (by norm_num) szB (1 / 10) (1 / 10) (1 / 6) (1 / 10) zB (by norm_num) flow_zB)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) hev szB_reg5I hDec hExp
    (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) (by norm_num))

/-- **`expIniI_Qopg`** at `(szB, zB, s ≡ 7/8, T ≡ 15/16)` for the mollifier family `st6_mollifier_familyg` (positive `Cq`, `c`). -/
example (hDec : STDecaygL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8))
    (hExp : STExp2gL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8)) :
    ∃ Cq c : ℝ, 0 < Cq ∧ 0 < c ∧ ∃ ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd 3 (szB.L n)) → ℂ,
      (∀ᶠ n in atTop, STMollifierProps (d := 3) (szB.lam n) Cq c (ϑ n)) ∧
      (∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool,
        ‖STQop (d := 3) (ϑ n) (7 / 8) (fun b => STExpErrg (bandFM szB (STflowE zB)) (Sizes.seqP szB) n (7 / 8) σ b)‖ ≤
          ((szB.size n : ℕ) : ℝ) ^ τ * STExpTarget szB n (7 / 8)) ∧
      (∀ ε' D : ℝ, 0 < ε' → 0 < D → ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool,
        EKFastDecay (szB.lam n) (7 / 8) ((szB.W n : ℕ) : ℝ) ε' D
          (STQop (d := 3) (ϑ n) (7 / 8) (fun b => STExpErrg (bandFM szB (STflowE zB)) (Sizes.seqP szB) n (7 / 8) σ b))) ∧
      (∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool,
        EKSumZero (STQop (d := 3) (ϑ n) (7 / 8) (fun b => STExpErrg (bandFM szB (STflowE zB)) (Sizes.seqP szB) n (7 / 8) σ b))) := by
  obtain ⟨κ', δ, H₀, g', E, hκ', hδ, hm', hev, hrep⟩ := ExpIniIGen_bandData
  obtain ⟨Cq, c, hC, hc, ϑ, hϑ⟩ := st6_mollifier_familyg szB (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) szB_WO
  exact ⟨Cq, c, hC, hc, ϑ, hϑ, expIniI_Qopg (bandFM szB (STflowE zB)) (Sizes.seqP szB) (by norm_num) hκ' hδ szB_admissible inferInstance
    hrep hm' (ExpIniIGen_Kb_band (by norm_num) szB (1 / 10) (1 / 10) (1 / 6) (1 / 10) zB (by norm_num) flow_zB)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) hev hDec hExp Cq c hC hc ϑ hϑ⟩

/-- **`expIniI_mixedg`** at `(szB, zB, 7/8, 15/16)`, `𝔠_d = 1/300`, for the mollifier family `st6_mollifier_familyg`; the kernel pin is the proved `stek_sumRes2gL_band`. -/
example (hDec : STDecaygL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8))
    (hExp : STExp2gL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8)) :
    ∃ Cq c : ℝ, 0 < Cq ∧ 0 < c ∧ ∃ ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd 3 (szB.L n)) → ℂ,
      (∀ᶠ n in atTop, STMollifierProps (d := 3) (szB.lam n) Cq c (ϑ n)) ∧
      PrecL szB (Sizes.seqP szB) (U := STIdx2P szB STSigMixed (fun _ => 7 / 8) (fun _ => 15 / 16))
        (fun n p _ => ‖Step2Gen_UN (bandFM szB (STflowE zB)) n p.2.1.1 (7 / 8) (p.1 : ℝ)
          (STQop (d := 3) (ϑ n) (7 / 8) (fun b => STExpErrg (bandFM szB (STflowE zB)) (Sizes.seqP szB) n (7 / 8) p.2.1.1 b)) p.2.2‖)
        (fun n p _ => STExpTarget szB n (p.1 : ℝ)) := by
  obtain ⟨κ', δ, H₀, g', E, hκ', hδ, hm', hev, hrep⟩ := ExpIniIGen_bandData
  obtain ⟨κm, hκm, H⟩ := Step6KitGen_KerFR1_band (d := 3) (1 / 10) (by norm_num)
  obtain ⟨-, hKer, hg, hR1⟩ := H szB (1 / 10) (1 / 6) (1 / 10) zB flow_zB
  obtain ⟨Cq, c, hC, hc, ϑ, hϑ⟩ := st6_mollifier_familyg szB (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) szB_WO
  exact ⟨Cq, c, hC, hc, ϑ, hϑ, expIniI_mixedg (bandFM szB (STflowE zB)) (Aof := fun _ => 1) (stek_sumRes2gL_band 3)
    (by norm_num) hκm le_rfl (𝔠d := 1 / 300) (by norm_num) (by norm_num) hκ' hδ szB_admissible szB.lam hKer hg hR1 inferInstance hrep hm'
    (ExpIniIGen_Kb_band (by norm_num) szB (1 / 10) (1 / 10) (1 / 6) (1 / 10) zB (by norm_num) flow_zB)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) hev szB_reg5I hDec hExp
    (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) (by norm_num)) Cq c hC hc ϑ hϑ⟩

/-- **Target 8, `stExpIniIgL'_of`, the pin at the band tuple, `d = 3`**: every family premise is discharged; no hypothesis remains. -/
example : STExpIniIgL' 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  stExpIniIgL'_of (Ker := @STEKBandKer 3) (Aof := fun _ => 1) (fun sz _ => sz.lam) (fun sz => inferInstance)
    (step5CasesGen_flowFacts_band 3) (iniTermGen_cltFlow_band 3)
    (fun sz κ ε 𝔠 𝔡 z hκ hflow => ExpIniIGen_Kb_band (by norm_num) sz κ ε 𝔠 𝔡 z hκ hflow) (stek_sumRes2NALgL_band 3)
    (stek_sumRes2gL_band 3) (fun _ _ => le_rfl) Step6KitGen_KerFR1_band

/-- **The band re-derivation `stExpIniI'_gen_band`**, read at the data of regime (i) `(szB, zB, 7/8, 15/16)` through the merged `inst_ing6_I`; the stochastic premises of
`STIngR6` are the hypotheses of the produced statement. -/
example : InstIng6Concl (fun sz E s t => STExpIniIConcl' sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_ing6_I STReg5I _ (stExpIniI'_gen_band 3) szB_reg5I

end Instances

end RBM.BA

end
