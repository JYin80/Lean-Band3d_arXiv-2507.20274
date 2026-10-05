/-
Release check for T2220 (dispatcher V1, Mon Oct  5 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20, §29, §45 (O2),
§50, §54, §56, §57 (1), §66 (3), §69 B).
UN-11: the GUE side of the Step-1 regularity event under the weak pin `UNGUELocal`: port of RBM2D
`Universality/Step1RegularityGUE.lean` (c9a24cf, `guelocalEventHighProb` `:381`, `guedetHalf` `:1109`,
`gueGoodHighProb` `:1116`) to `Sizes d`, `Ω d L W`, `N = (W L)^d`; new file `RBM3D/Universality/Step1RegularityGUE.lean`.
It is the prerequisite of UN-14 (`UNInfty1Row'`, `PinsDens.lean:88`, owed), whose GUE translation consumes
`UNGUEGoodHighProb` (RBM2D `GUETranslation.lean:6` imports `Step1RegularityGUE`; `:1015` `_uniform` takes `hGood`).
The C form (UN-12b) and the refuted pins are not used.  The prime is the ASCII `'` of `main`.
Section 1: the merged names the new file builds on (and the names UN-14 will join it with); Mathlib names of the route.
Section 2: the new vocabulary (2.1, bodies to be copied verbatim into namespace `RBM.Univ`) and the statements of the
theorems of T2220 as `def T2220_<name> : Prop`; the library states the theorem `<name>` (namespace in the docstring)
with exactly this body (binder names may be added to hypotheses).
Section 3: UN-14's consumer shape (not a target of T2220; information for the next ticket).
Definitions, statements and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2220-check.lean`.
-/
import RBM3D
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! ## 1. Merged names -/

-- UN-01 (`Universality/Pins.lean`, T2174, merged f8ad4b4): GUE law, vocabulary, `UNGUELocal`, `UNL32`, `UNInfty1`
#check @RBM.Univ.gueVar
#check @RBM.Univ.gueP
#check @RBM.Univ.isProbabilityMeasure_gueP
#check @RBM.Univ.kPoint
#check @RBM.Univ.rhoSC
#check @RBM.Univ.stieltjesN
#check @RBM.Univ.IsTestFun
#check @RBM.Univ.isTestFun_comp_smul
#check @RBM.Univ.ouTStar
#check @RBM.Univ.mV
#check @RBM.Univ.IsRegular32
#check @RBM.Univ.IsFreeConv32
#check @RBM.Univ.dbmMat
#check @RBM.Univ.dbmMat_isHermitian
#check @RBM.Univ.UNL32
#check @RBM.Univ.un_L32_arith
#check @RBM.Univ.Nsz
#check @RBM.Univ.UNGUELocal
#check @RBM.Univ.UNInfty1
#check @RBM.Univ.UNTrLocal
#check @RBM.Univ.UNNormBound
#check @RBM.Univ.UNDens
#check @RBM.Univ.UNDensBandRow
#check @RBM.Univ.UNUnivMainRow
#check @RBM.Univ.vOU
-- UN-01c (`Universality/PinsDens.lean`, T2201, merged 3fc9d03): the primed pins; `UNInfty1Row'` is owed (UN-14)
#check @RBM.Univ.UNDens'
#check @RBM.Univ.UNStep1Good'
#check @RBM.Univ.UNInfty1Row'
#check @RBM.Univ.UNCore'
#check @RBM.Univ.un_core_of_rows'
#check @RBM.Univ.un_bUniv_of_rows'
#check @RBM.Univ.un_dens'_msc_zero
-- UN-12 (`Universality/Step1Good.lean`, T2208, merged a42cad0): public helpers reusable on the GUE side; the band
-- deterministic half `step1Good'_det` is the template of target 3 (not reusable as is: see the ticket, "Route")
#check @RBM.Univ.stieltjesN_eq_mV
#check @RBM.Univ.mV_vOU
#check @RBM.Univ.mV_eta_mul_im_mono
#check @RBM.Univ.mV_im_le_inv
#check @RBM.Univ.un_admissible_cd_lt_half
#check @RBM.Univ.step1Good'_det
#check @RBM.Univ.step1Good'
-- UN-13 (`Universality/Step1Band.lean`, T2214, merged 18a41d3): the public helpers UN-14 reuses
#check @RBM.Univ.step1Band_abs_integral_kPoint_le
#check @RBM.Univ.step1Band_kPoint_shift
#check @RBM.Univ.step1Band_eventually_forall
#check @RBM.Univ.step1Band_gue_count
#check @RBM.Univ.step1Band_integral_ouP
#check @RBM.Univ.step1Band
#check @RBM.Univ.step1Band_row
#check @RBM.Univ.Step1BandInst.inst_rhoSC_one_lt_zero
-- UN-02b (`Universality/Step1Cond.lean`, T2183, merged 7771372): GUE stationarity of the OU flow (UN-14)
#check @RBM.Univ.Step1Cond_gueMatPairing_eq_integral
-- UN-08 (`Universality/GUEInvariance.lean`, T2175, merged d5e2848): UN-14's other dependency
#check @RBM.Univ.gueP_map_unitary_conj
-- UN-06 (`Universality/FreeConv.lean`, `FreeConvStability.lean`, T2176, merged 52c856e): free convolution, stability
#check @RBM.Univ.freeConvST
#check @RBM.Univ.isFreeConv51_freeConvST
#check @RBM.Univ.exists_isFreeConv32
#check @RBM.Univ.FreeConvStability.freeConv_stable_local
#check @RBM.Univ.FreeConvStability.msc_tendsto_mE
-- the semicircle (`Defs/Semicircle.lean`, fbc9870)
#check @RBM.msc
-- size sequences and the fine-lattice model (`Defs/Sizes.lean`, `Gauss/FineModel.lean`, T2006, merged 0a873f1)
#check @RBM.Gauss.Ω
#check @RBM.Gauss.CoordF
#check @RBM.Gauss.Xmat
#check @RBM.Gauss.Xmat_isHermitian
#check @RBM.Gauss.measurable_Xentry
#check @RBM.Gauss.Sizes.size
#check @RBM.Gauss.Sizes.card_Idx
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.SizesInst.sz0_tendsto
#check @RBM.Gauss.SizesInst.sz0_admissible
-- Mathlib (the Gaussian coordinate tail; `x^s e^{-bx} → 0`; `size → ∞` in `ℕ` from `ℝ`)
#check @ProbabilityTheory.HasSubgaussianMGF.measure_ge_le
#check @ProbabilityTheory.HasSubgaussianMGF.id_map_iff
#check @ProbabilityTheory.mgf_id_gaussianReal
#check @ProbabilityTheory.integrable_exp_mul_gaussianReal
#check @tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
#check @tendsto_natCast_atTop_iff

noncomputable section

namespace RBM.Univ.T2220Check

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ
open scoped NNReal ENNReal

/-! ## 2. New vocabulary and statements (namespace `RBM.Univ` in the library) -/

/-! ### 2.1 Vocabulary (copied verbatim into the library, namespace `RBM.Univ`) -/

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

/-! ### 2.2 Exponent arithmetic (RBM2D §2) -/

/-- `gue_window` (RBM2D `:140`): `0 < τ < τs/8` meets the four constraints of the deterministic half. -/
def T2220_gue_window : Prop :=
  ∀ {τs τ : ℝ}, 0 < τ → τ < τs / 8 →
    τ ≤ τs / 4 ∧ τ - τs / 8 < 0 ∧ τ - τs / 2 < -(3 * τs / 8) ∧ τ < τs

/-- `gue_window_sharp` (RBM2D `:148`). -/
def T2220_gue_window_sharp : Prop :=
  ∀ {τs τ : ℝ}, τs / 8 ≤ τ → ¬ (τ - τs / 8 < 0) ∧ ¬ (τ - τs / 2 < -(3 * τs / 8))

/-- `gue_l32_exponents` (RBM2D `:196`): the `UNL32` exponents at `σ = δ = min(τs/4, (1-τs)/3)`. -/
def T2220_gue_l32_exponents : Prop :=
  ∀ {τs : ℝ}, 0 < τs → τs < 1 →
    0 < min (τs / 4) ((1 - τs) / 3) ∧
    -1 + min (τs / 4) ((1 - τs) / 3) ≤ -1 + τs / 4 ∧
    -1 + τs / 4 ≤ -(min (τs / 4) ((1 - τs) / 3)) ∧
    -1 + τs / 4 + min (τs / 4) ((1 - τs) / 3) ≤ -1 + τs / 2 ∧
    -1 + τs ≤ -(min (τs / 4) ((1 - τs) / 3)) - 2 * min (τs / 4) ((1 - τs) / 3)

/-! ### 2.3 S7a: the probabilistic half -/

/-- `guelocalEventHighProb` (RBM2D `:381`): `UNGUELocal` at `(κ, τ, D + 1)`, the entry tail
`P(∃ x y, ‖X x y‖ > 1) ≤ 4 N² e^{-N/8} ≤ N^{-(D+1)}` (`gueVar ≤ 1/N`, `2N²` real coordinates), `2N^{-(D+1)} ≤ N^{-D}`. -/
def T2220_guelocalEventHighProb : Prop := UNGUELocalEventHighProb

/-- `gue_err_pow` (RBM2D `:437`): where the weak precision enters: on the event, at `Im z ≥ c N^{-1+σ}`,
`‖m_N(z) - m_sc(z)‖ ≤ c^{-1/2} N^{τ - σ/2}`. -/
def T2220_gue_err_pow : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {κ τ : ℝ} {ω : Ω d (sz.L n) (sz.W n)},
    Step1LocalEventGUE sz n κ τ ω → 1 ≤ sz.size n → ∀ {z : ℂ},
      |z.re| ≤ 2 - κ → Nsz sz n ^ (-1 + τ) ≤ z.im → z.im ≤ 10 → ∀ {c σ : ℝ}, 0 < c →
        c * Nsz sz n ^ (-1 + σ) ≤ z.im →
          ‖stieltjesN (Xmat d (sz.L n) (sz.W n) ω) z - msc z‖ ≤ Real.sqrt c⁻¹ * Nsz sz n ^ (τ - σ / 2)

/-! ### 2.4 S7b: the deterministic half; S7: the composition -/

/-- `guedetHalf` (RBM2D `:1109`, proof `Step1RegularityGUE_det` `:1044`). -/
def T2220_guedetHalf : Prop := UNGUEDetHalf

/-- `gueGoodHighProb_of` (RBM2D `:123`): S7 = S7a + S7b at `τ = τs/16`. -/
def T2220_gueGoodHighProb_of : Prop := UNGUELocalEventHighProb → UNGUEDetHalf → UNGUEGoodHighProb

/-- `gueGoodHighProb` (RBM2D `:1116`): the input of UN-14. -/
def T2220_gueGoodHighProb : Prop := UNGUEGoodHighProb

/-! ### 2.5 Compiled nonempty instances (namespace `RBM.Univ.Step1RegularityGUEInst`; `d = 3`, `sz0`, `κ = 1`,
`τs = 1/60 = 𝔠𝔡` (the `τ_U` of the UN-13 instances), `E₀ = 1`, `τ = τs/16 = 1/960`) -/

/-- `inst_sz0_size_tendsto`: `size → ∞` in `ℕ` at `sz0` (from `sz0_tendsto`). -/
def T2220_inst_sz0_size_tendsto : Prop :=
  Tendsto (fun n => RBM.Gauss.SizesInst.sz0.size n) atTop atTop

/-- `inst_guelocalEvent_sz0`: S7a at `κ = 1/2`, `τ = 1/960`, `D = 1`. -/
def T2220_inst_guelocalEvent_sz0 : Prop :=
  UNGUELocal → ∀ᶠ n in atTop,
    gueP 3 (RBM.Gauss.SizesInst.sz0.L n) (RBM.Gauss.SizesInst.sz0.W n)
      {ω | ¬ Step1LocalEventGUE RBM.Gauss.SizesInst.sz0 n (1 / 2) (1 / 960) ω} ≤
      ENNReal.ofReal (Nsz RBM.Gauss.SizesInst.sz0 n ^ (-(1 : ℝ)))

/-- `inst_event_nonempty_sz0`: the premise of S7b is eventually satisfiable. -/
def T2220_inst_event_nonempty_sz0 : Prop :=
  UNGUELocal → ∀ᶠ n in atTop, ∃ ω : Ω 3 (RBM.Gauss.SizesInst.sz0.L n) (RBM.Gauss.SizesInst.sz0.W n),
    Step1LocalEventGUE RBM.Gauss.SizesInst.sz0 n (1 / 2) (1 / 960) ω

/-- `inst_guedetHalf_sz0`: S7b, every hypothesis discharged. -/
def T2220_inst_guedetHalf_sz0 : Prop :=
  ∀ᶠ n in atTop, ∀ ω : Ω 3 (RBM.Gauss.SizesInst.sz0.L n) (RBM.Gauss.SizesInst.sz0.W n),
    Step1LocalEventGUE RBM.Gauss.SizesInst.sz0 n (1 / 2) (1 / 960) ω →
      GUEGoodAt RBM.Gauss.SizesInst.sz0 n 1 (1 / 60) 1 ω

/-- `inst_gueGood_sz0`: S7 at `D = 2` (`= k + 1` at `k = 1`, the call UN-14 makes). -/
def T2220_inst_gueGood_sz0 : Prop :=
  UNGUELocal → ∀ᶠ n in atTop,
    gueP 3 (RBM.Gauss.SizesInst.sz0.L n) (RBM.Gauss.SizesInst.sz0.W n)
      {ω | ¬ GUEGoodAt RBM.Gauss.SizesInst.sz0 n 1 (1 / 60) 1 ω} ≤
      ENNReal.ofReal (Nsz RBM.Gauss.SizesInst.sz0 n ^ (-(2 : ℝ)))

/-- `inst_gueGood_nonempty_sz0`: the good event is eventually nonempty (nondegeneracy). -/
def T2220_inst_gueGood_nonempty_sz0 : Prop :=
  UNGUELocal → ∀ᶠ n in atTop, ∃ ω : Ω 3 (RBM.Gauss.SizesInst.sz0.L n) (RBM.Gauss.SizesInst.sz0.W n),
    GUEGoodAt RBM.Gauss.SizesInst.sz0 n 1 (1 / 60) 1 ω

/-! ## 3. UN-14's consumer shape (not a target of T2220) -/

/-- The GUE translation UN-14 proves from `UNGUEGoodHighProb` (RBM2D `GUETranslation`, `GUETranslation.lean:59`, with
`ContDiff ∧ HasCompactSupport` as `IsTestFun`, `Sizes` → `Sizes d`, `3 ≤ d`).  With `O ↦ O(ρ_sc(E')·)`
(`isTestFun_comp_smul`) it is the step from the GUE side of `UNInfty1 … E 0` (`step1Band`) to that of `UNInfty1 … E E'`
(`Tendsto.add` in `ℝ`, `τ₁ = 𝔠𝔡` from `step1Band_row`), i.e. `UNInfty1Row'`. -/
def T2220_UN14_GUETranslation : Prop :=
  UNL32 → UNGUELocal →
    ∀ d : ℕ, 3 ≤ d → ∀ sz : Sizes d, Tendsto (fun n => sz.size n) atTop atTop →
      ∀ k : ℕ, ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ →
        ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
          Tendsto (fun n =>
            (∫ ω, kPoint k (fun α => O ((rhoSC 0 / rhoSC E) • α)) 0
                (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues ∂(gueP d (sz.L n) (sz.W n))) -
            (∫ ω, kPoint k O E (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues
                ∂(gueP d (sz.L n) (sz.W n))))
            atTop (𝓝 0)

/-- UN-14's row shape (RBM2D `GUETranslationRow`, `:73`), with the input of this ticket as its hypothesis. -/
def T2220_UN14_GUETranslationRow : Prop := UNGUEGoodHighProb → T2220_UN14_GUETranslation

end RBM.Univ.T2220Check
