/-
Release check for T2226 (dispatcher V1, Mon Oct  5 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20, §29, §45 (O2),
§50, §54, §56, §57 (1), §65, §66 (3), §69 B).
UN-14: the GUE translation `0 → E'` and the owed row `UNInfty1Row'` (`PinsDens.lean:88`): port of RBM2D
`Universality/GUETranslation.lean` (c9a24cf; `GUETranslation` `:59`, `GUETranslationRow` `:73`, `_core` `:736`,
`_uniform` `:1015`, `guetranslationRow` `:1057`, `infty1Row_of_translation` `:1151`) to `Sizes d`, `Ω d L W`,
`N = (W L)^d`; new file `RBM3D/Universality/GUETranslation.lean`.  Inputs: `step1Band_row` (UN-13, `E' = 0`),
`gueGoodHighProb` (UN-11), `Step1Cond_gueMatPairing_eq_integral` (UN-02b), the borrowed `UNL32`, the owed
`UNGUELocal` (hypothesis inside the row shape).  The C form (UN-12b) and the refuted pins are not used.
The prime is the ASCII `'` of `main`.
Section 1: the merged names the new file builds on; Mathlib names of the route.
Section 2: the new vocabulary (2.1, bodies to be copied verbatim into namespace `RBM.Univ`), the statements of the
theorems of T2226 as `def T2226_<name> : Prop` (2.2-2.4), the instances (2.5); the library states the theorem
`<name>` (namespace in the docstring) with exactly this body (binder names may be added to hypotheses).
Section 3: downstream shapes (not targets; information).
Definitions, statements and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2226-check.lean`.
-/
import RBM3D
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Algebra.Group.Action.Defs

/-! ## 1. Merged names -/

-- UN-01 (`Universality/Pins.lean`, T2174, merged f8ad4b4)
#check @RBM.Univ.gueP
#check @RBM.Univ.isProbabilityMeasure_gueP
#check @RBM.Univ.kPoint
#check @RBM.Univ.rhoSC
#check @RBM.Univ.rhoSC_pos
#check @RBM.Univ.IsTestFun
#check @RBM.Univ.isTestFun_comp_smul
#check @RBM.Univ.UNModel
#check @RBM.Univ.UNModel.band
#check @RBM.Univ.ouTStar
#check @RBM.Univ.ouP
#check @RBM.Univ.ouMat_isHermitian
#check @RBM.Univ.IsRegular32
#check @RBM.Univ.IsFreeConv32
#check @RBM.Univ.dbmMat
#check @RBM.Univ.dbmMat_isHermitian
#check @RBM.Univ.UNL32
#check @RBM.Univ.un_L32_arith
#check @RBM.Univ.Nsz
#check @RBM.Univ.UNLocAvgBand
#check @RBM.Univ.UNTrLocal
#check @RBM.Univ.UNNormBound
#check @RBM.Univ.UNGUELocal
#check @RBM.Univ.UNGreenCorrAll
#check @RBM.Univ.UNClaimAll
#check @RBM.Univ.UNUnivDilAt
#check @RBM.Univ.UNInfty1
#check @RBM.Univ.UNUnivMainRow
#check @RBM.Univ.UNDensBandRow
#check @RBM.Univ.UNNormBandRow
#check @RBM.Univ.UNTrLocalBandRow
#check @RBM.Univ.UNBUniv
#check @RBM.Univ.UNQueBand
#check @RBM.Univ.UNMLOut
#check @RBM.Univ.UNOURow
#check @RBM.Univ.UNEMCTE2Row
#check @RBM.Univ.UNJakUywRow
#check @RBM.Univ.UNClaimRow
#check @RBM.Univ.UNInst.bump
#check @RBM.Univ.UNInst.bump_testFun
#check @RBM.Univ.UNInst.bump_nondegenerate
#check @RBM.Univ.UNInst.sz0_adm
-- UN-01c (`Universality/PinsDens.lean`, T2201, merged 3fc9d03): the primed pins; `UNInfty1Row'` owed (this ticket)
#check @RBM.Univ.UNDens'
#check @RBM.Univ.UNDens'.toUNDens
#check @RBM.Univ.UNInfty1Row'
#check @RBM.Univ.UNCore'
#check @RBM.Univ.UNDensBandRow'
#check @RBM.Univ.unDensBandRow'_of_row
#check @RBM.Univ.un_core_of_rows'
#check @RBM.Univ.un_bUniv_of_rows'
#check @RBM.Univ.un_dens'_msc_zero
-- UN-02 (`Universality/Step1Cond.lean`, T2183, merged 7771372; `EigenMeasurable.lean`, T2177, merged a52eb85)
#check @RBM.Univ.Step1Cond_gueMatPairing_eq_integral
#check @RBM.Univ.Step1Cond_scaledPairing_lipschitz
#check @RBM.Univ.Step1Cond_exists_dominating_testFun
#check @RBM.Univ.measurable_kPoint_eigenvalues
#check @RBM.Univ.eigenvalues₀_abs_sub_le
-- UN-08 (`Universality/GUEInvariance.lean`, T2175, merged d5e2848): transitive (imported by `Step1Cond`)
#check @RBM.Univ.gueP_map_unitary_conj
-- UN-12 (`Universality/Step1Good.lean`, T2208, merged a42cad0)
#check @RBM.Univ.un_admissible_cd_lt_half
-- UN-13 (`Universality/Step1Band.lean`, T2214, merged 18a41d3): public helpers and the `E' = 0` row
#check @RBM.Univ.step1Band_abs_integral_kPoint_le
#check @RBM.Univ.step1Band_kPoint_shift
#check @RBM.Univ.step1Band_eventually_forall
#check @RBM.Univ.step1Band_gue_count
#check @RBM.Univ.step1Band_integral_ouP
#check @RBM.Univ.step1Band
#check @RBM.Univ.step1Band_row
#check @RBM.Univ.Step1BandInst.inst_rhoSC_one_lt_zero
#check @RBM.Univ.Step1BandInst.inst_step1Band_row_band
-- UN-11 (`Universality/Step1RegularityGUE.lean`, T2220, merged e9ef940): the GUE-side good event
#check @RBM.Univ.vGUE
#check @RBM.Univ.GUEGoodAt
#check @RBM.Univ.UNGUEGoodHighProb
#check @RBM.Univ.gue_l32_exponents
#check @RBM.Univ.gueGoodHighProb
#check @RBM.Univ.Step1RegularityGUEInst.inst_sz0_size_tendsto
-- the semicircle (`Defs/Semicircle.lean`, fbc9870)
#check @RBM.msc
-- size sequences and the fine-lattice model (`Defs/Sizes.lean`, `Gauss/FineModel.lean`, T2006, merged 0a873f1)
#check @RBM.Gauss.Ω
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
-- Mathlib (composition in `ℝ`; dilation algebra; `size → ∞` in `ℕ` from `ℝ`; squeeze)
#check @Filter.Tendsto.add
#check @smul_smul
#check @Metric.tendsto_nhds
#check @squeeze_zero'
#check @tendsto_natCast_atTop_iff

noncomputable section

namespace RBM.Univ.T2226Check

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ
open scoped NNReal ENNReal

/-! ## 2. New vocabulary and statements (namespace `RBM.Univ` in the library) -/

/-! ### 2.1 Vocabulary (copied verbatim into the library, namespace `RBM.Univ`; = `T2220_UN14_GUETranslation`,
`T2220_UN14_GUETranslationRow` of `docs/tickets/checks/T2220-check.lean` section 3) -/

/-- `UNGUETranslation` (proved here by `guetranslation`; not registered): the GUE translation `0 → E` (RBM2D
`GUETranslation`, `GUETranslation.lean:59`; RBM1D `gue_translation'`): for a bulk energy `E`, the GUE `k`-point
functional at `E` is asymptotically the GUE functional at energy `0` with the test function dilated by
`ρ_sc(0)/ρ_sc(E)`.  The carrier is the GUE alone (`gueP`): no `Admissible`, no `τ_U`. -/
def UNGUETranslation : Prop :=
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

/-- `UNGUETranslationRow` (proved here by `guetranslationRow`; not registered): the translation from the GUE-side
good event (RBM2D `GUETranslationRow`, `:73`). -/
def UNGUETranslationRow : Prop := UNGUEGoodHighProb → UNGUETranslation

/-! ### 2.2 Target 1: conditioning on the first GUE block (RBM2D `_integral_gue` `:720` + `_integral_dbm_shift`) -/

/-- `guetranslation_integral_gue` (namespace `RBM.Univ`): the GUE functional at `E₀` is the `gueP`-average of the
DBM functional of `vGUE` at energy `0`, time `1 - e^{-t*}` (GUE analogue of `step1Band_integral_ouP`). -/
def T2226_guetranslation_integral_gue : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (τs E₀ : ℝ) (k : ℕ) (O : (Fin k → ℝ) → ℝ), IsTestFun O →
    ∫ ω, kPoint k O E₀ (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues ∂(gueP d (sz.L n) (sz.W n)) =
      ∫ ω, (∫ y, kPoint k O 0 (dbmMat_isHermitian d (sz.L n) (sz.W n) (vGUE sz n τs E₀ ω)
          (1 - Real.exp (-(ouTStar sz τs n))) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n)))
        ∂(gueP d (sz.L n) (sz.W n))

/-! ### 2.3 Targets 2-3: worst-sequence core, uniformity, the translation -/

/-- `guetranslation_core` (namespace `RBM.Univ`; RBM2D `GUETranslation_core` `:736`): along any sequence eventually in
`GUEGoodAt`, `UNL32` at `v n = vGUE … (ω n)`, `E n = 0`, `t n = 1 - e^{-t*}`, `δ = σ = min(τs/4, (1-τs)/3)`,
`q = 1/2`, `c = min κ 1 / 960`, `C = CV = 2`, `m n`/`ρ' n` by `Classical.choose` from `GUEGoodAt`, test function
`O(ρ_sc(E₀)⁻¹ ·)`, then the Lipschitz step `ρ'_n → ρ_sc(E₀)` (`Step1Cond_scaledPairing_lipschitz`) with the count
`step1Band_gue_count`. -/
def T2226_guetranslation_core : Prop :=
  UNL32 → UNGUELocal →
    ∀ d : ℕ, 3 ≤ d → ∀ sz : Sizes d, Tendsto (fun n => sz.size n) atTop atTop →
      ∀ κ : ℝ, 0 < κ → ∀ τs : ℝ, 0 < τs → τs < 1 → ∀ E₀ : ℝ, |E₀| ≤ 2 - κ →
        ∀ k : ℕ, ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
          ∀ ω : ∀ n, Ω d (sz.L n) (sz.W n), (∀ᶠ n in atTop, GUEGoodAt sz n κ τs E₀ (ω n)) →
            Tendsto (fun n =>
              (∫ y, kPoint k O 0 (dbmMat_isHermitian d (sz.L n) (sz.W n) (vGUE sz n τs E₀ (ω n))
                  (1 - Real.exp (-(ouTStar sz τs n))) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n))) -
              ∫ y, kPoint k (fun α => O ((rhoSC 0 / rhoSC E₀) • α)) 0
                (Xmat_isHermitian d (sz.L n) (sz.W n) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n)))
              atTop (𝓝 0)

/-- `guetranslation_uniform` (namespace `RBM.Univ`; RBM2D `GUETranslation_uniform` `:1015`): the core uniformly on the
good event (nonempty from `UNGUEGoodHighProb` at `D = 1`; `step1Band_eventually_forall` on the carrier
`Ω d (sz.L n) (sz.W n)`). -/
def T2226_guetranslation_uniform : Prop :=
  UNGUEGoodHighProb → UNL32 → UNGUELocal →
    ∀ d : ℕ, 3 ≤ d → ∀ sz : Sizes d, Tendsto (fun n => sz.size n) atTop atTop →
      ∀ κ : ℝ, 0 < κ → ∀ τs : ℝ, 0 < τs → τs < 1 → ∀ E₀ : ℝ, |E₀| ≤ 2 - κ →
        ∀ k : ℕ, ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O → ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n in atTop, ∀ ω : Ω d (sz.L n) (sz.W n), GUEGoodAt sz n κ τs E₀ ω →
            |(∫ y, kPoint k O 0 (dbmMat_isHermitian d (sz.L n) (sz.W n) (vGUE sz n τs E₀ ω)
                (1 - Real.exp (-(ouTStar sz τs n))) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n))) -
              ∫ y, kPoint k (fun α => O ((rhoSC 0 / rhoSC E₀) • α)) 0
                (Xmat_isHermitian d (sz.L n) (sz.W n) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n))| ≤ ε

/-- `guetranslationRow` (namespace `RBM.Univ`; RBM2D `:1057`, internal time `τs = 1/2`; bad event from
`UNGUEGoodHighProb` at `D = k + 1` and `step1Band_abs_integral_kPoint_le`). -/
def T2226_guetranslationRow : Prop := UNGUETranslationRow

/-- `guetranslation` (namespace `RBM.Univ`): `guetranslationRow gueGoodHighProb`. -/
def T2226_guetranslation : Prop := UNGUETranslation

/-! ### 2.4 Target 4: the row `UNInfty1Row'` and its composition -/

/-- `un_infty1Row'_of_translation` (namespace `RBM.Univ`; RBM2D `infty1Row_of_translation` `:1151`): `step1Band_row`
(`E' = 0`, `τ₁ = 𝔠𝔡`) plus `UNGUETranslation` at `κ = (2 - |E'|)/2`, `E := E'`, test function `O(ρ_sc(E') ·)`
(`isTestFun_comp_smul`, `rhoSC_pos`; `ρ_sc(E') • ((ρ_sc(0)/ρ_sc(E')) • α) = ρ_sc(0) • α` by `smul_smul`), added in
`ℝ` (`Filter.Tendsto.add`). -/
def T2226_un_infty1Row'_of_translation : Prop := UNGUETranslation → UNInfty1Row'

/-- `un_infty1Row'` (namespace `RBM.Univ`): **the owed row, proved** (`un_infty1Row'_of_translation guetranslation`). -/
def T2226_un_infty1Row' : Prop := UNInfty1Row'

/-- `un_core'_of_univMainRow` (namespace `RBM.Univ`): `un_core_of_rows' un_infty1Row'`. -/
def T2226_un_core'_of_univMainRow : Prop := UNUnivMainRow → UNCore'

/-! ### 2.5 Instances (namespace `RBM.Univ.GUETranslationInst`; `d = 3`, `sz0`, `k = 1`, `bump`) -/

/-- `inst_dilation_ne_one`: the dilation of the translation at `E = 1` is not `1` (`ρ_sc(0)/ρ_sc(1) = 2/√3`;
from `Step1BandInst.inst_rhoSC_one_lt_zero`). -/
def T2226_inst_dilation_ne_one : Prop := rhoSC 0 / rhoSC 1 ≠ 1

/-- `inst_guetranslation_sz0`: `guetranslation` at `sz0`, `k = 1`, `κ = 1`, `E = 1`, `O = bump`. -/
def T2226_inst_guetranslation_sz0 : Prop :=
  UNL32 → UNGUELocal →
    Tendsto (fun n =>
      (∫ ω, kPoint 1 (fun α => (RBM.Univ.UNInst.bump : (Fin 1 → ℝ) → ℝ) ((rhoSC 0 / rhoSC 1) • α)) 0
          (Xmat_isHermitian 3 (RBM.Gauss.SizesInst.sz0.L n) (RBM.Gauss.SizesInst.sz0.W n) ω).eigenvalues
          ∂(gueP 3 (RBM.Gauss.SizesInst.sz0.L n) (RBM.Gauss.SizesInst.sz0.W n))) -
      (∫ ω, kPoint 1 (RBM.Univ.UNInst.bump : (Fin 1 → ℝ) → ℝ) 1
          (Xmat_isHermitian 3 (RBM.Gauss.SizesInst.sz0.L n) (RBM.Gauss.SizesInst.sz0.W n) ω).eigenvalues
          ∂(gueP 3 (RBM.Gauss.SizesInst.sz0.L n) (RBM.Gauss.SizesInst.sz0.W n))))
      atTop (𝓝 0)

/-- `inst_un_infty1Row'_band_zero`: `un_infty1Row'` at `sz0` (`𝔠 = 1/6`, `𝔡 = 1/10`), the band model, `msc`,
`E = 0`, `ρ = rhoSC 0`, `δ = 1/2` (`un_dens'_msc_zero`), the local law from `UNTrLocalBandRow` at `κ = 1`, the
norm bound from `UNNormBandRow`, GUE energy `E' = 1` (the translation is nontrivial: `E' ≠ E`). -/
def T2226_inst_un_infty1Row'_band_zero : Prop :=
  UNL32 → UNGUELocal → UNLocAvgBand → UNTrLocalBandRow → UNNormBandRow →
    ∃ τ₁ : ℝ, 0 < τ₁ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₁ →
      UNInfty1 RBM.Gauss.SizesInst.sz0 (UNModel.band RBM.Gauss.SizesInst.sz0) (fun _ => rhoSC 0) 0 1 1
        (RBM.Univ.UNInst.bump : (Fin 1 → ℝ) → ℝ) τU

/-- `inst_un_infty1Row'_band_one`: the same at `E = E' = 1` (`κ = 1/2`), `ρ = rhoSC 1`; the density from
`UNDensBandRow` through `unDensBandRow'_of_row` (as `Step1BandInst.inst_step1Band_band_one`). -/
def T2226_inst_un_infty1Row'_band_one : Prop :=
  UNL32 → UNGUELocal → UNLocAvgBand → UNTrLocalBandRow → UNNormBandRow → UNDensBandRow →
    ∃ τ₁ : ℝ, 0 < τ₁ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₁ →
      UNInfty1 RBM.Gauss.SizesInst.sz0 (UNModel.band RBM.Gauss.SizesInst.sz0) (fun _ => rhoSC 1) 1 1 1
        (RBM.Univ.UNInst.bump : (Fin 1 → ℝ) → ℝ) τU

/-! ## 3. Downstream shapes (not targets of T2226; information) -/

/-- The band chain after T2226: `un_bUniv_of_rows' un_infty1Row'` has this type (`PinsDens.lean:233`); the open rows
are `UNUnivMainRow` (UN `Apriori`/`UnivMain`), the claim rows and the band rows (other tickets). -/
def T2226_D_un_bUniv : Prop :=
  UNUnivMainRow → UNClaimRow → UNEMCTE2Row → UNJakUywRow → UNOURow → UNDensBandRow → UNTrLocalBandRow →
    UNNormBandRow → UNL32 → (∀ d : ℕ, UNMLOut d) → UNLocAvgBand → UNQueBand → UNGUELocal → UNGreenCorrAll →
      UNBUniv

end RBM.Univ.T2226Check
