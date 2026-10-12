/-
Release check for T2477 (dispatcher V3, Mon Oct 12 21:29 UTC 2026; DECISIONS §278).  BA M/N N3b (stage M/N; design T2449 MN3, §4, row :133;
supervisor 2049 GMN-C2): E3 and E4 written in place in C form, for every centred model `M : UNModelC sz`, in the merged
band files `Universality/GreenCorr`, `Step1Band`, `UnivMain` (`PinsDens` expected unchanged).
Part 1: merged names (band originals, the C-form vocabulary, the consumer `baBUniv_of_rows`, the band terminal).
Part 2: the target statements as Prop values (prefix `T2477_`; content binding up to binder implicitness or a dropped
premise).  The T2449 probe (`t/T2449` 921369b) has no N3b pin: every `T2477_*` is built from merged Props only
(`UNGreenCorrC`, `UNGreenCorrAllC`, `UNInfty1C`, `UNUnivMainC`, `UNCoreC''`, `vOUC`, `ouMatC`).
Then shapes (not binding): band readings, compositions, the consumer, the instance data.
Merged names only.  No proofs.
Run: lake env lean docs/tickets/checks/T2477-check.lean
-/
import RBM3D.Universality.GreenCorr
import RBM3D.Universality.UnivMain
import RBM3D.Universality.Step1Band
import RBM3D.Universality.Step1Cond
import RBM3D.Universality.PinsDens
import RBM3D.Universality.PinsK
import RBM3D.Universality.PinsC2
import RBM3D.Universality.GUETranslation
import RBM3D.Universality.Apriori
import RBM3D.Universality.OU
import RBM3D.BA.UNPins
import RBM3D.Main.BandTerminal
import RBM3D.Main.BUnivHolds

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- E4 band originals (`Universality/GreenCorr.lean`): the carrier-generic step, the per-model comparison, the pin
#check @RBM.Univ.greenCorr_step
#check @RBM.Univ.unGreenCorr
#check @RBM.Univ.greenCorrAll
#check @RBM.Univ.GreenCorrCheck.instance_ba
#check @RBM.Univ.GreenCorrCheck.instance_greenCorrAll
#check @RBM.Univ.GreenCorrCheck.sz0_size_tendsto
-- E3 band originals (`Universality/Step1Band.lean`; the public helpers read in `GUETranslation`, `Step1RegularityGUE`)
#check @RBM.Univ.step1Band
#check @RBM.Univ.step1Band_row
#check @RBM.Univ.step1Band_integral_ouP
#check @RBM.Univ.step1Band_abs_integral_kPoint_le
#check @RBM.Univ.step1Band_kPoint_shift
#check @RBM.Univ.step1Band_eventually_forall
#check @RBM.Univ.step1Band_gue_count
#check @RBM.Univ.Step1BandInst.inst_step1Band_band
#check @RBM.Univ.integral_kPoint_ouMat_cond
-- E3 band originals (`Universality/UnivMain.lean`)
#check @RBM.Univ.unClaim417C_of_rows
#check @RBM.Univ.unClaimRowk
#check @RBM.Univ.unClaimRow
#check @RBM.Univ.unDens_rho_bounds
#check @RBM.Univ.univMain_transfer
#check @RBM.Univ.univMainRow
#check @RBM.Univ.unCore'_holds
#check @RBM.Univ.UnivMainInst.inst_core'_band_zero
-- E3 band originals in files that are not writable here (`GUETranslation`, `Apriori`, `OU`)
#check @RBM.Univ.UNGUETranslation
#check @RBM.Univ.guetranslation
#check @RBM.Univ.un_infty1Row'_of_translation
#check @RBM.Univ.un_infty1Row'
#check @RBM.Univ.un_core'_of_univMainRow
#check @RBM.Univ.unApriori_of_trLocal
#check @RBM.Univ.apriori_ouMat_zero_integral
#check @RBM.Univ.measurable_ouMat
-- `Universality/PinsDens.lean` (expected unchanged; its public names read elsewhere)
#check @RBM.Univ.UNDens'
#check @RBM.Univ.UNDens'.toUNDens
#check @RBM.Univ.unDensShift
#check @RBM.Univ.UNStep1Good'
#check @RBM.Univ.UNInfty1Row'
#check @RBM.Univ.UNCore'
#check @RBM.Univ.UNStep1GoodC'
#check @RBM.Univ.UNCoreC'
#check @RBM.Univ.unDensBandRow'_of_row
#check @RBM.Univ.unDens'_freeConvST
#check @RBM.Univ.un_core_of_rows'
#check @RBM.Univ.un_bUniv_of_rows'
#check @RBM.Univ.not_UNStep1Good
#check @RBM.Univ.not_UNStep1GoodC
#check @RBM.Univ.un_dens'_msc_zero
#check @RBM.Univ.UNDensInst.not_UNStep1Good_band
-- the band vocabulary (`Universality/Pins.lean`)
#check @RBM.Univ.UNModel
#check @RBM.Univ.UNModel.band
#check @RBM.Univ.UNModel.ba
#check @RBM.Univ.ouMat
#check @RBM.Univ.ouMat_isHermitian
#check @RBM.Univ.ouMat_zero
#check @RBM.Univ.ouP
#check @RBM.Univ.ouTStar
#check @RBM.Univ.kPoint
#check @RBM.Univ.vOU
#check @RBM.Univ.dbmMat
#check @RBM.Univ.dbmMat_isHermitian
#check @RBM.Univ.gueP
#check @RBM.Univ.IsTestFun
#check @RBM.Univ.rhoSC
#check @RBM.Univ.UNL32
#check @RBM.Univ.UNGUELocal
#check @RBM.Univ.UNDens
#check @RBM.Univ.UNTrLocal
#check @RBM.Univ.UNNormBound
#check @RBM.Univ.UNClaim417
#check @RBM.Univ.UNClaimAll
#check @RBM.Univ.UNApriori
#check @RBM.Univ.UNGreenCorr
#check @RBM.Univ.UNGreenCorrAll
#check @RBM.Univ.UNInfty1
#check @RBM.Univ.UNInfty1Row
#check @RBM.Univ.UNUnivMain
#check @RBM.Univ.UNUnivMainRow
#check @RBM.Univ.UNUnivDilAt
#check @RBM.Univ.UNCore
#check @RBM.Univ.un_core_of_rows
-- the C-form vocabulary and bridges (`Universality/PinsK.lean`, T2187)
#check @RBM.Univ.UNModelC
#check @RBM.Univ.UNModel.toC
#check @RBM.Univ.ouMatC
#check @RBM.Univ.ouInit
#check @RBM.Univ.ouMatC_isHermitian
#check @RBM.Univ.ouInit_isHermitian
#check @RBM.Univ.ouMatC_zero
#check @RBM.Univ.ouMatC_eq_ouInit_add
#check @RBM.Univ.ouMatC_eq_ouMat_add
#check @RBM.Univ.unPinsK_toC_toUNModel
#check @RBM.Univ.ouMatC_toC_apply
#check @RBM.Univ.ouMatC_toC
#check @RBM.Univ.ouInit_toC
#check @RBM.Univ.vOUC
#check @RBM.Univ.UNClaim417C
#check @RBM.Univ.UNClaimAllC
#check @RBM.Univ.UNClaim417C_toC
#check @RBM.Univ.UNClaimAllC_toC
#check @RBM.Univ.UNGreenCorrC
#check @RBM.Univ.UNGreenCorrAllC
#check @RBM.Univ.UNGreenCorrC_toC
#check @RBM.Univ.UNGreenCorrAllC.toAll
#check @RBM.Univ.UNInfty1C
#check @RBM.Univ.UNUnivMainC
#check @RBM.Univ.UNInfty1C_toC
#check @RBM.Univ.UNUnivMainC_toC
#check @RBM.Univ.UNTrLocalInit
#check @RBM.Univ.UNCoreC
#check @RBM.Univ.UNKInst.inst_ouMatC_ne_ouMat
-- the C-form Step 1 and the core pin (`Universality/PinsC2.lean`, T2213)
#check @RBM.Univ.UNTrLocalInit'
#check @RBM.Univ.UNMeanBound
#check @RBM.Univ.UNStep1GoodC''
#check @RBM.Univ.step1GoodC''
#check @RBM.Univ.step1GoodC''_det
#check @RBM.Univ.UNCoreC''
#check @RBM.Univ.unMeanBound_toC
#check @RBM.Univ.unTrLocalInit'_of_unTrLocal
#check @RBM.Univ.unTrLocalInit'_band_zero
#check @RBM.Univ.UNDens'.mono
#check @RBM.Univ.UNTrLocal.mono
#check @RBM.Univ.PinsC2Inst.inst_coreC_band''
-- the consumer and the BA model (`BA/UNPins.lean`)
#check @RBM.Univ.baBUniv_of_rows
#check @RBM.Univ.UNModelC.ba
#check @RBM.Univ.UNModelC.ba_spec
#check @RBM.Univ.unMeanBound_ba
#check @RBM.Univ.ouMatC_ba_eq_ouMat
#check @RBM.Univ.ouMatC_ba_eq_band_add
#check @RBM.Univ.UNDensBARow'
#check @RBM.Univ.UNTrLocalBARow
#check @RBM.Univ.UNTrLocalInitBARow'
#check @RBM.Univ.UNNormBARow
#check @RBM.Univ.UNClaimRowBA
#check @RBM.Univ.UNEMCTE2RowBA
#check @RBM.Univ.UNJakUywRowBA
#check @RBM.Univ.UNOURowBA
#check @RBM.Univ.UNMLOutBA
#check @RBM.Univ.UNLocAvgBA
#check @RBM.Univ.UNQueBA
#check @RBM.BA.BAEnd_BUnivL
-- the band terminal whose axioms must not change (GMN-C2 (c))
#check @RBM.Endpoints.band_terminal
#check @RBM.Endpoints.bUniv_holds
-- instance data
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Univ.UNInst.sz0_adm
#check @RBM.Univ.UNInst.bump
#check @RBM.Univ.UNInst.bump_testFun
#check @RBM.msc

/-! ## Part 2: the target statements (content binding) and shapes -/

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open scoped NNReal ENNReal

noncomputable section

namespace RBM.Univ
open RBM RBM.Gauss RBM.Gauss.Sizes

/-- **Target 1** (`GreenCorr`, `unGreenCorrC`): the comparison `UNGreenCorrC` (`PinsK:187`) for every centred model along
every size sequence with `size n → ∞`; band original `unGreenCorr` (`GreenCorr:864`). -/
def T2477_GreenCorrC : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), Tendsto (fun n => sz.size n) atTop atTop → ∀ M : UNModelC sz, UNGreenCorrC sz M

/-- **Target 2** (`GreenCorr`, `greenCorrAllC`): the pin `UNGreenCorrAllC` (`PinsK:204`) itself; band original
`greenCorrAll` (`GreenCorr:873`). -/
def T2477_GreenCorrAllC : Prop :=
  UNGreenCorrAllC

/-- **Target 3** (`Step1Band`, `step1Band_integral_ouPC`): conditioning of the centred flow at `t* = ouTStar sz τU n` on the
first block: the DBM functional at the diagonal `vOUC` (`PinsK:268`), time `1 - e^{-t*}`, energy `0`; band original
`step1Band_integral_ouP` (`Step1Band:643`). -/
def T2477_integral_ouPC : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (M : UNModelC sz) (n : ℕ) (τU E : ℝ) (k : ℕ) (O : (Fin k → ℝ) → ℝ), IsTestFun O →
    ∫ ω, kPoint k O E (ouMatC_isHermitian M n (ouTStar sz τU n) ω).eigenvalues ∂(ouP M.toUNModel n) =
      ∫ ω, (∫ y, kPoint k O 0 (dbmMat_isHermitian d (sz.L n) (sz.W n) (vOUC sz M n τU E ω)
          (1 - Real.exp (-(ouTStar sz τU n))) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n))) ∂M.μ

/-- **Target 4a** (`Step1Band`, `step1BandC''`): Step 1 of `(1infyuniv)` for the centred flow, at the GUE energy `0`;
the good event is the merged `step1GoodC''` (`PinsC2:1469`), so `UNTrLocal` is not a premise and `UNMeanBound` is;
band original `step1Band` (`Step1Band:1006`). -/
def T2477_Step1BandC : Prop :=
  UNL32 → UNGUELocal →
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
        UNDens' m E ρ δ → UNTrLocalInit' sz M m E δ →
          (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz M.toUNModel CV₀ ∧ UNMeanBound sz M CV₀) →
            ∀ k : ℕ, ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
              ∀ τU : ℝ, 0 < τU → τU ≤ 𝔠 * 𝔡 → UNInfty1C sz M ρ E 0 k O τU

/-- **Target 4b** (`Step1Band`, `step1Band_rowC''`): the row shape with `τ₁`; band original `step1Band_row`
(`Step1Band:1121`). -/
def T2477_Step1BandRowC : Prop :=
  UNL32 → UNGUELocal →
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
        UNDens' m E ρ δ → UNTrLocalInit' sz M m E δ →
          (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz M.toUNModel CV₀ ∧ UNMeanBound sz M CV₀) →
            ∀ k : ℕ, ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
              ∃ τ₁ : ℝ, 0 < τ₁ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₁ → UNInfty1C sz M ρ E 0 k O τU

/-- **Target 5** (`UnivMain`, `un_infty1RowC''`): the centred `(1infyuniv)` row at every GUE energy `|E'| < 2`; band
original `un_infty1Row'_of_translation guetranslation` (`GUETranslation:763, 787`). -/
def T2477_Infty1RowC : Prop :=
  UNL32 → UNGUELocal →
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
        UNDens' m E ρ δ → UNTrLocalInit' sz M m E δ →
          (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz M.toUNModel CV₀ ∧ UNMeanBound sz M CV₀) →
            ∀ E' : ℝ, |E'| < 2 → ∀ k : ℕ, ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
              ∃ τ₁ : ℝ, 0 < τ₁ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₁ → UNInfty1C sz M ρ E E' k O τU

/-- **Target 6** (`UnivMain`, `univMain_transferC`): the law transfer at `t = 0` for the centred flow; band original
`univMain_transfer` (`UnivMain:509`). -/
def T2477_univMain_transferC : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (M : UNModelC sz) (n k : ℕ) (O : (Fin k → ℝ) → ℝ) (E : ℝ),
    ∫ ω, kPoint k O E (M.herm n ω).eigenvalues ∂M.μ =
      ∫ ω, kPoint k O E (ouMatC_isHermitian M n 0 ω).eigenvalues ∂(ouP M.toUNModel n)

/-- **Target 7** (`UnivMain`, `univMainRowC`): the centred `(univ-main)` row; band original `univMainRow`
(`UnivMain:533`, pin `UNUnivMainRow` `Pins:745`). -/
def T2477_UnivMainRowC : Prop :=
  UNGreenCorrAllC →
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
        UNDens m E ρ δ → UNTrLocal sz M.toUNModel m E δ → UNClaimAllC sz M E →
          ∀ k : ℕ, ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
            ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O → UNUnivMainC sz M ρ E k O τU

/-- **Target 8** (`UnivMain`, `unCoreC''_holds`): the pin `UNCoreC''` (`PinsC2:106`) itself; band original
`unCore'_holds` (`UnivMain:557`). -/
def T2477_CoreC : Prop :=
  UNCoreC''

/-! ### Shapes (not binding) -/

-- E4 band recovery: the merged `UNGreenCorrAllC.toAll` (`PinsK:251`) and `UNGreenCorrC_toC` (`PinsK:232`)
example : Prop := T2477_GreenCorrAllC → UNGreenCorrAll
example : Prop := ∀ {d : ℕ} {sz : Sizes d} (M : UNModel sz), UNGreenCorrC sz M.toC ↔ UNGreenCorr sz M
example : Prop := T2477_GreenCorrC → T2477_GreenCorrAllC

-- E3 band readings at `M.toC` (merged `UNInfty1C_toC`, `UNUnivMainC_toC`, `UNClaimAllC_toC`, `unMeanBound_toC`)
example : Prop := ∀ {d : ℕ} {sz : Sizes d} (M : UNModel sz) (ρ : ℕ → ℝ) (E E' : ℝ) (k : ℕ)
    (O : (Fin k → ℝ) → ℝ) (τU : ℝ), UNInfty1C sz M.toC ρ E E' k O τU ↔ UNInfty1 sz M ρ E E' k O τU
example : Prop := ∀ {d : ℕ} {sz : Sizes d} (M : UNModel sz) (ρ : ℕ → ℝ) (E : ℝ) (k : ℕ)
    (O : (Fin k → ℝ) → ℝ) (τU : ℝ), UNUnivMainC sz M.toC ρ E k O τU ↔ UNUnivMain sz M ρ E k O τU
example : Prop := ∀ {d : ℕ} {sz : Sizes d} (M : UNModel sz) (E : ℝ), UNClaimAllC sz M.toC E ↔ UNClaimAll sz M E
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (M : UNModel sz) (CV₀ : ℝ), UNMeanBound sz M.toC CV₀

-- the composition (targets 3-8; the C-form of `un_core_of_rows'`, `PinsDens:220`, is target 8)
example : Prop := T2477_integral_ouPC → UNStep1GoodC'' → T2477_Step1BandC
example : Prop := T2477_Step1BandC → T2477_Step1BandRowC
example : Prop := T2477_Step1BandRowC → UNGUETranslation → T2477_Infty1RowC
example : Prop := T2477_univMain_transferC → T2477_UnivMainRowC
example : Prop := T2477_Infty1RowC → T2477_UnivMainRowC → T2477_CoreC

-- S5, the consumer: `baBUniv_of_rows` (`BA/UNPins:367`) with `hcore`, `hGC` supplied from targets 8 and 2
example : Prop :=
  T2477_CoreC → UNL32 → UNGUELocal → T2477_GreenCorrAllC → UNDensBARow' → UNTrLocalBARow →
    UNTrLocalInitBARow' → UNNormBARow → UNClaimRowBA → UNEMCTE2RowBA → UNJakUywRowBA → UNOURowBA →
      (∀ d : ℕ, UNMLOutBA d) → UNLocAvgBA → UNQueBA → ∀ d : ℕ, RBM.BA.BAEnd_BUnivL d

-- every centred model, read at BA (T2449 :123): no BA restatement
example : Prop :=
  T2477_GreenCorrC → ∀ sz : Sizes 3, Tendsto (fun n => sz.size n) atTop atTop → UNGreenCorrC sz (UNModelC.ba sz)

-- instance data (target 9 and the auditor's nonzero-mean checks)
open RBM.Gauss.SizesInst RBM.Univ.UNInst in
example : Prop := sz0.Admissible (1 / 6) (1 / 10) ∧ UNMeanBound sz0 (UNModelC.ba sz0) 1
open RBM.Gauss.SizesInst RBM.Univ.UNInst in
example : Prop := UNTrLocal sz0 (UNModel.band sz0) (fun _ => msc) 0 (1 / 2) →
  UNTrLocalInit' sz0 (UNModel.band sz0).toC (fun _ => msc) 0 (1 / 4)
open RBM.Gauss.SizesInst RBM.Univ.UNInst in
example : Prop := UNDens' (fun _ => msc) 0 (fun _ => rhoSC 0) (1 / 2) ∧ IsTestFun (bump : (Fin 1 → ℝ) → ℝ)
open RBM.Gauss.SizesInst RBM.Univ.UNInst in
example : Prop :=
  T2477_CoreC → UNL32 → UNGUELocal → T2477_GreenCorrAllC →
    UNTrLocal sz0 (UNModel.band sz0) (fun _ => msc) 0 (1 / 2) →
    (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz0 (UNModel.band sz0) CV₀) →
    UNClaimAllC sz0 (UNModel.band sz0).toC 0 →
      UNUnivDilAt sz0 (UNModel.band sz0) (fun _ => rhoSC 0) 0 0 1 (bump : (Fin 1 → ℝ) → ℝ)

end RBM.Univ

end
