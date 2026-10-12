/-
Release check for T2462 (dispatcher V3, Mon Oct 12 15:53 UTC 2026; DECISIONS §270).  U U4s1 (ST side, additive): the Step 5 kit over the
carrier in three new files `Chain/Step5CasesGen.lean`, `Chain/Step5KerGen.lean`, `Chain/NewKLKLGen.lean`; the band files
`Step5Kit`, `Step5Cases`, `Step5Kernel`, `TailtoTail`, `TailtoTailSq`, `WardII`, `NewKLKL` are not edited (outside the
certificate lane).  One kernel (supervisor 1152 U-C4): `Step2Gen_uKer`, `Step2Gen_thetaKer`, `Step2Gen_UN` of T8b.
Coupling (1457 UBA-C1, DECISIONS §269 (2)): size-level quantities at `sz.lam`; the kernel decay at a coupling `gK`; one
comparison hypothesis `∀ n, gK n ≤ sz.lam n ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2`.
Part 1: merged names.  Part 2: the target statements as `Prop` values (prefix `T2462_`; content binding up to the name, except
`T2462_WardIdent`, `T2462_stWardIIgL_of`, `T2462_ThDecayK`, `T2462_ThDecayK_band`, `T2462_ProfileK`: D1/D2 defaults, fixed at
the 1a-audit), then shapes (not binding): band and BA readings.  Part 3 (G1): the public names of the seven band files, unchanged.
Merged names only.  No proof terms, no placeholders.
Run: lake env lean docs/tickets/checks/T2462-check.lean
-/
import RBM3D.Chain.Step5Gen
import RBM3D.Chain.NewKLKGen
import RBM3D.Chain.Step2Kern
import RBM3D.Induction.Step5Kernel
import RBM3D.Induction.TailtoTailSq
import RBM3D.Induction.WardII
import RBM3D.Induction.NewKLKL
import RBM3D.Induction.IniTermI
import RBM3D.Induction.IniTermII
import RBM3D.Induction.DuhamelI
import RBM3D.Induction.DuhamelII
import RBM3D.Induction.EtermsMid
import RBM3D.Induction.PfStep5
import RBM3D.Induction.MainIndRegimes
import RBM3D.BA.NewKLKBA
import RBM3D.BA.TwistStep2
import RBM3D.BA.TwistGrid
import RBM3D.BA.KWard
import RBM3D.BA.KSolve
import RBM3D.BA.KInduct
import RBM3D.BA.EKPins

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the carrier and the law-level pins (row 0, T8)
#check @RBM.BA.FlowFM
#check @RBM.BA.PrecL
#check @RBM.BA.bandFM
#check @RBM.BA.STDecaygL
#check @RBM.BA.STDecayStronggL
#check @RBM.BA.STStep2ConclgL
-- U6 (`Chain/Step5Gen`, T2458): conclusions, the pin shape, the regimes, the wrapped case pins, the matrix-level pins
#check @RBM.BA.STStep5ConclgL
#check @RBM.BA.STDecayStrongUgL
#check @RBM.BA.STWardIIConclgL
#check @RBM.BA.STIngR5gL
#check @RBM.BA.STStep5RgL
#check @RBM.BA.STStep5IgL
#check @RBM.BA.STStep5IIgL
#check @RBM.BA.STStep5IIIgL
#check @RBM.BA.STStep5IVgL
#check @RBM.BA.STEtermsMidgL
#check @RBM.BA.STDuhamelIgL
#check @RBM.BA.STIniTermIgL
#check @RBM.BA.STDuhamelIIgL
#check @RBM.BA.STIniTermIIgL
#check @RBM.BA.STWardIIgL
#check @RBM.BA.STPfStep5gL
#check @RBM.BA.STNewKLKLAtgL'
#check @RBM.BA.STNewKLKLgL'
#check @RBM.BA.STTailtoTailConclgL
#check @RBM.BA.STTailtoTailgL'
#check @RBM.BA.stNewKLKLgL'_band
#check @RBM.BA.stTailtoTailgL'_band
-- U6 bridges, band name to generic name (the band re-derivations of target 13 go through them)
#check @RBM.BA.bandFM_STStep5Concl
#check @RBM.BA.bandFM_STWardIIConcl
#check @RBM.BA.STIngR5_iff_gL
#check @RBM.BA.STStep5R_iff_gL
#check @RBM.BA.STStep5I_iff_gL
#check @RBM.BA.STStep5II_iff_gL
#check @RBM.BA.STStep5III_iff_gL
#check @RBM.BA.STStep5IV_iff_gL
#check @RBM.BA.STEtermsMid_iff_gL
#check @RBM.BA.STDuhamelI_iff_gL
#check @RBM.BA.STIniTermI_iff_gL
#check @RBM.BA.STDuhamelII_iff_gL
#check @RBM.BA.STIniTermII_iff_gL
#check @RBM.BA.STWardII_iff_gL
#check @RBM.BA.STPfStep5_iff_gL
-- the one kernel (U-C4; T8b, T4s1)
#check @RBM.BA.Step2Mat
#check @RBM.BA.Step2Data
#check @RBM.BA.bandStep2Mat
#check @RBM.BA.bandStep2Data
#check @RBM.BA.Step2Gen_Theta
#check @RBM.BA.Step2Kern_Mss
#check @RBM.BA.Step2Gen_thetaKer
#check @RBM.BA.Step2Gen_uKer
#check @RBM.BA.Step2Gen_UN
#check @RBM.BA.Step2Kern_Mss_band
#check @RBM.BA.Step2Kern_thetaKer_band
#check @RBM.BA.Step2Kern_uKer_band
#check @RBM.BA.Step2Kern_UN_band
#check @RBM.BA.Step2Gen_USemigroup
#check @RBM.BA.step2Gen_USemigroup_band
#check @RBM.BA.Step2Gen_UN_self
#check @RBM.BA.Step2Gen_UN_comp
#check @RBM.BA.bandStep2_Ugen
-- T3 (`Chain/NewKLKGen`): the hypothesis class of `lem:newKLK` over a family (target 10)
#check @RBM.BA.NewKLKGenHyp
#check @RBM.BA.newKLKGenHyp_band
#check @RBM.BA.STNewKLKgL'
#check @RBM.BA.stNewKLKgL'_of
-- band facts of the band discharges (sizes, spectral data, kernel, Ward)
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.lemT
#check @RBM.lemT_lt_one
#check @RBM.Gauss.etaOf
#check @RBM.Gauss.etaT_eq_etaOf
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.STBctl_mono
#check @RBM.Gauss.Sizes.seqHflow_isHermitian
#check @RBM.zeroModeSet
#check @RBM.tailT
#check @RBM.tailW
#check @RBM.Gauss.zdistInf
#check @RBM.Gauss.Sizes.STprof
#check @RBM.ekPropTInf_holds
#check @RBM.Theta
#check @RBM.norm_Theta_apply_le
#check @RBM.sum_norm_Theta_row_le
#check @RBM.mul_Theta_of_three_le
#check @RBM.Loop.KLward_two
#check @RBM.Loop.KLK_rotate
#check @RBM.Loop.KLK_one
-- BA readings (statement level only; U4-BA)
#check @RBM.BA.baFM
#check @RBM.BA.baFMz
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowLam0
#check @RBM.BA.baStep2Mat
#check @RBM.BA.baStep2Fam
#check @RBM.BA.baStep2Data
#check @RBM.BA.EMn2BA_T0_lt_one
#check @RBM.BA.EMn2BA_mF_data
#check @RBM.BA.TwistStep2_T0_ge
#check @RBM.BA.TwistStep2_lam0_sq
#check @RBM.BA.Bctl_le_one_of_conStInd
#check @RBM.BA.BAuKer_self
#check @RBM.BA.BAuKer_comp
#check @RBM.BA.Step2Kern_uKer_BA
#check @RBM.BA.Step2Kern_thetaKer_BA
#check @RBM.BA.Step2Kern_UN_BA
#check @RBM.BA.BAUN
#check @RBM.BA.baNewKLKGenHyp
#check @RBM.BA.stNewKLKgL'_ba
#check @RBM.BA.baK_ward
#check @RBM.BA.BAKsol_rotate
#check @RBM.BA.baKsol_one
-- consumers: band proofs of the case pins (owners U4s2, U4s3, U5) and V2's step assembly
#check @RBM.Gauss.Sizes.stEtermsMid_of_LWT
#check @RBM.Gauss.Sizes.stDuhamelI_holds
#check @RBM.Gauss.Sizes.stDuhamelII_holds
#check @RBM.Gauss.Sizes.stIniTermI_holds
#check @RBM.Gauss.Sizes.stIniTermII_holds
#check @RBM.Gauss.Sizes.stPfStep5_holds
#check @RBM.Gauss.Sizes.ST_mainIndR_of_steps

/-! ## Part 2: the target statements (content binding) and shapes (not binding) -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Target 1** (content binding): the flow facts of a carrier tuple.  At every `κ > 0`, one `κm > 0`: admissible sizes,
`T0 < 1`, `κm ≤ Im m` and `η_t = (1 - t) Im m` (band: `STFlow`, `lemT_lt_one`, `st5_mE_im_ge` with the semicircle domain
fact, `etaT_eq_etaOf`; BA: `BAFlow`, `EMn2BA_T0_lt_one`, `EMn2BA_mF_data`, the `eta` field of `baFM`). -/
def T2462_FlowFacts (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ κm : ℝ, 0 < κm ∧
    ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      sz.Admissible 𝔠 𝔡 ∧ (∀ n, T0 sz z n < 1) ∧ (∀ n, κm ≤ ((mk sz z).m n).im) ∧
        ∀ (n : ℕ) (t : ℝ), (mk sz z).eta n t = (1 - t) * ((mk sz z).m n).im

/-- **Target 1, band result** (content binding): the band tuple satisfies the flow facts. -/
def T2462_FlowFacts_band (d : ℕ) : Prop :=
  T2462_FlowFacts d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z))
    (fun _ z n => lemT (z n))

/-- **Target 7, D1 default**: the `(zYU1)` identity (`3_5:2257-2262`) as a carrier datum, mixed charges, every sample:
`(𝓛-𝒦)_{u,σ,a} - [Q^{(1)}(𝓛-𝒦)_{u,σ}]_a = Im (𝓛-𝒦)^{(1)}_{u,+,a₂} / (N η_u)`, `N = (WL)^d` (band: `stWardII_identity`). -/
def T2462_WardIdent {d : ℕ} {sz : Sizes d} (C : FlowFM sz) : Prop :=
  ∀ (n : ℕ) (u : ℝ), 0 ≤ u → u < 1 → ∀ (ω : sz.SeqΩ) (σ : Fin 2 → Bool), σ 0 ≠ σ 1 →
    ∀ a : Fin 2 → Zd d (sz.L n),
      (C.L n u σ a ω - C.K n u σ a) -
          zeroModeSet d (sz.L n) {0} (fun a' => C.L n u σ a' ω - C.K n u σ a') a =
        (((C.L n u (fun _ : Fin 1 => true) (fun _ => a 1) ω -
            C.K n u (fun _ : Fin 1 => true) (fun _ => a 1)).im : ℝ) : ℂ) /
          ((((sz.size n : ℕ) : ℂ)) * (C.eta n u : ℂ))

/-- **Target 7, band result, D1 default**: `bandFM sz E` satisfies the identity when `|E n| < 2` for every `n`. -/
def T2462_WardIdent_band : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ), (∀ n, |E n| < 2) → T2462_WardIdent (bandFM sz E)

section Tuple

variable (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
  (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
  (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)

/-- **Target 2** (content binding): case (i) of Step 5 over a carrier tuple (band `ST_step5_caseI_of_pins`, `Step5Kit:292`). -/
def T2462_caseI : Prop :=
  T2462_FlowFacts d Flow mk T0 → STEtermsMidgL d law Flow mk T0 → STDuhamelIgL d law Flow mk T0 →
    STIniTermIgL d law Flow mk T0 → STStep5IgL d law Flow mk T0

/-- **Target 3** (content binding): case (ii) (band `ST_step5_caseII_of_pins`, `Step5Cases:542`). -/
def T2462_caseII : Prop :=
  T2462_FlowFacts d Flow mk T0 → STEtermsMidgL d law Flow mk T0 → STDuhamelIIgL d law Flow mk T0 →
    STIniTermIIgL d law Flow mk T0 → STWardIIgL d law Flow mk T0 → STStep5IIgL d law Flow mk T0

/-- **Target 4** (content binding): case (iii) from `lem:pf_step5` (band `ST_step5_caseIII_of_pf`, `Step5Cases:311`). -/
def T2462_caseIII : Prop :=
  T2462_FlowFacts d Flow mk T0 → STPfStep5gL d law Flow mk T0 → STStep5IIIgL d law Flow mk T0

/-- **Target 5** (content binding): case (iv) with no ingredient pin (band `stStep5IV_holds`, `Step5Kit:549`). -/
def T2462_caseIV : Prop :=
  T2462_FlowFacts d Flow mk T0 → STStep5IVgL d law Flow mk T0

/-- **Target 7, D1 default**: the Ward term over a carrier tuple (band `stWardII_holds`, `WardII:269`). -/
def T2462_stWardIIgL_of : Prop :=
  T2462_FlowFacts d Flow mk T0 →
    (∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → T2462_WardIdent (mk sz z)) →
      STWardIIgL d law Flow mk T0

end Tuple

/-- **Target 6** (content binding): the assembly at the endpoint `u = t` (band `ST_step5_assembly`, `Step5Kit:79`). -/
def T2462_assembly {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  (∀ n, s n ≤ t n) → STStep5ConclgL C μ s t → STDecaygL C μ t ∧ STDecayStronggL C μ t

/-- **Target 8** (content binding): `(eq:decompU)` for the one kernel, `uKer_{s,t} = 1 + (t - s) thetaKer_t`, under the
semigroup law of T4s1 (band `step5Kernel_decompU`, `Step5Kernel:57`, with `‖μ‖ = 1`). -/
def T2462_uKerDecomp {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) : Prop :=
  Step2Gen_USemigroup C n → ∀ (σ σ' : Bool) (s t : ℝ), 0 ≤ t → t < 1 →
    Step2Gen_uKer C n σ σ' s t = 1 + ((t - s : ℝ) : ℂ) • Step2Gen_thetaKer C n σ σ' t

/-- **Target 8** (content binding): the same inside `Step2Gen_UN` (band `step5Kernel_UN_decompU`, `Step5Kernel:74`). -/
def T2462_UNDecomp {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) : Prop :=
  Step2Gen_USemigroup C n → ∀ {k : ℕ} (σ : Fin k → Bool) (s t : ℝ), 0 ≤ t → t < 1 →
    ∀ (A : (Fin k → Zd d (sz.L n)) → ℂ) (a : Fin k → Zd d (sz.L n)),
      Step2Gen_UN C n σ s t A a =
        ∑ b : Fin k → Zd d (sz.L n),
          (∏ i, (1 + ((t - s : ℝ) : ℂ) • Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) t) (a i) (b i)) * A b

/-- **Target 9, D2 default**: decay and row sum of the carrier kernel `thetaKer` for every charge pair, read at the kernel
coupling `gK` (band `gK = sz.lam`, from `step5Kernel_theta_decay`, `Step5Kernel:135`; BA `gK = BAflowLam0 sz z`, U4-BA (a)). -/
def T2462_ThDecayK {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (gK : ℕ → ℝ) (Λ C₆ : ℝ) : Prop :=
  ∀ n : ℕ, 0 < gK n → gK n ≤ Λ → ∀ (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 →
    (∀ a b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' t a b‖ ≤
        C₆ * tailT d (sz.L n) (gK n) t ((zdistInf d (sz.L n) (b - a) : ℕ) : ℝ)) ∧
      ∀ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' t a b‖ ≤ C₆ / (1 - t)

/-- **Target 9, band result, D2 default**: at `bandFM sz E` with `|E n| ≤ 2`, coupling `sz.lam`, constant `C₆(d, Λ)`. -/
def T2462_ThDecayK_band : Prop :=
  ∀ (d : ℕ) (Λ : ℝ), 3 ≤ d → 0 < Λ → ∃ C₆ : ℝ, 0 < C₆ ∧
    ∀ (sz : Sizes d) (E : ℕ → ℝ), (∀ n, |E n| ≤ 2) → T2462_ThDecayK (bandFM sz E) sz.lam Λ C₆

/-- **Target 9, D2 default**: `(uwp2-92kj)` (`3_5:2048-2053`) for the carrier kernel, profile and windows at `sz.lam`
(size level), decay at `gK`, one comparison hypothesis (UBA-C1); band `step5Kernel_profile_explicit_holds`
(`Step5Kernel:199`). -/
def T2462_ProfileK (d : ℕ) : Prop :=
  3 ≤ d → ∀ Λ C₆ A : ℝ, 0 < Λ → 0 < C₆ → 1 ≤ A → ∃ Cp : ℝ, 0 < Cp ∧
    ∀ (sz : Sizes d) (C : FlowFM sz) (gK : ℕ → ℝ), T2462_ThDecayK C gK Λ C₆ →
      (∀ n, gK n ≤ sz.lam n ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2) →
      ∀ (n : ℕ) (σ σ' : Bool) (W D u t : ℝ), 0 < gK n → gK n ≤ Λ → 0 < W → 0 ≤ u → u ≤ t → t < 1 →
        (sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t ∨ 1 - u ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) →
        ∀ a₁ a₂ : Zd d (sz.L n),
          (1 - u) * ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' t a₁ b‖ *
              tailW d (sz.L n) (sz.lam n) u ((sz.L n : ℕ) : ℝ) W D ((zdistInf d (sz.L n) (b - a₂) : ℕ) : ℝ) ≤
            Cp * tailT d (sz.L n) (sz.lam n) t ((zdistInf d (sz.L n) (a₁ - a₂) : ℕ) : ℝ) +
              Cp * ((1 - u) / (1 - t) * W ^ (-D))

/-- **Target 10** (content binding): `lem:newKLK` at `ℓ = L` (U6's primed pin) for every family satisfying T3's class
(band `stNewKLKL_holds`, `NewKLKL:836`). -/
def T2462_stNewKLKLgL'_of (d : ℕ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) : Prop :=
  (3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → NewKLKGenHyp d κ 𝔡 mk) → STNewKLKLgL' d mk

/-- **Target 10, band result** (content binding). -/
def T2462_NewKLKL_band (d : ℕ) : Prop := STNewKLKLgL' d (fun sz E => bandStep2Mat sz E)

/-- **Target 11, band result** (content binding): U6's target 7 at the band family. -/
def T2462_TailtoTail_band (d : ℕ) : Prop := STTailtoTailgL' d (fun sz E => bandFM sz E)

/-! ### Shapes (not binding): band readings -/

/-- Target 2 at the band tuple re-derives the band case (i) (with target 1 and U6's bridges). -/
example : Prop := ∀ d : ℕ,
  T2462_caseI d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) →
    T2462_FlowFacts_band d → STEtermsMid d → STDuhamelI d → STIniTermI d → STStep5I d
example : Prop := ∀ d : ℕ,
  T2462_caseII d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) →
    T2462_FlowFacts_band d → STEtermsMid d → STDuhamelII d → STIniTermII d → STWardII d → STStep5II d
example : Prop := ∀ d : ℕ,
  T2462_caseIII d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) →
    T2462_FlowFacts_band d → STPfStep5 d → STStep5III d
example : Prop := ∀ d : ℕ,
  T2462_caseIV d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) →
    T2462_FlowFacts_band d → STStep5IV d
/-- Target 6 at `bandFM`, law `seqP sz`. -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ), T2462_assembly (bandFM sz E) (Sizes.seqP sz) s t
/-- Target 8 at `bandFM` (the semigroup law holds for `|E n| ≤ 2`, `step2Gen_USemigroup_band`). -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ), |E n| ≤ 2 → T2462_UNDecomp (bandFM sz E) n
/-- Target 9 at the band coupling `gK = sz.lam`, `A = 1`. -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d), ∀ n, sz.lam n ≤ sz.lam n ∧ sz.lam n ^ 2 ≤ 1 * sz.lam n ^ 2
example : Prop := T2462_ProfileK 3
/-- Target 10, U6's route to the same band result. -/
example : Prop := ∀ d : ℕ, STNewKLKL d → T2462_NewKLKL_band d
example : Prop := ∀ d : ℕ, STTailtoTail d → T2462_TailtoTail_band d

/-! ### Shapes (not binding): BA readings (U4-BA; U5 for case (iii)) -/

example : Prop := T2462_FlowFacts 3 (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0
example : Prop := T2462_caseI 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
  baFMz BAflowT0
example : Prop := T2462_caseII 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
  baFMz BAflowT0
example : Prop := T2462_caseIII 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
  baFMz BAflowT0
example : Prop := T2462_caseIV 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
  baFMz BAflowT0
example : Prop := T2462_stWardIIgL_of 3 (fun sz => Sizes.seqP (sz.withLam 0))
  (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ), T2462_WardIdent (baFMz sz z)
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), T2462_UNDecomp (baFMz sz z) n
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (Λ C₆ : ℝ), T2462_ThDecayK (baFMz sz z) (BAflowLam0 sz z) Λ C₆
/-- UBA-C1 at BA: the one comparison hypothesis with `gK = BAflowLam0 sz z` and `A = (κ+1)/κ` (from `TwistStep2_lam0_sq`). -/
example : Prop := ∀ {d : ℕ} (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
  ∀ n, BAflowLam0 sz z n ≤ sz.lam n ∧ sz.lam n ^ 2 ≤ (κ + 1) / κ * BAflowLam0 sz z n ^ 2
/-- Target 10 at the BA family of T3-BA (`baNewKLKGenHyp`). -/
example : Prop := ∀ d : ℕ, T2462_stNewKLKLgL'_of d (fun sz E => baStep2Fam sz E)

end RBM.BA

end

/-! ## Part 3 (G1): the public names of the seven band files (files not edited; statements unchanged) -/
-- `Induction/Step5Kit.lean`
#check @RBM.Gauss.Sizes.st5_prec_mono
#check @RBM.Gauss.Sizes.st5_prec_cover
#check @RBM.Gauss.Sizes.ST_step5_assembly
#check @RBM.Gauss.Sizes.st5_zeroModeSet_empty
#check @RBM.Gauss.Sizes.st5_conStInd_mono
#check @RBM.Gauss.Sizes.st5_Bctl_ge
#check @RBM.Gauss.Sizes.st5_zdistInf_le
#check @RBM.Gauss.Sizes.st5_STprof_le
#check @RBM.Gauss.Sizes.st5_STprof_nonneg
#check @RBM.Gauss.Sizes.st5_STAI_nonneg
#check @RBM.Gauss.Sizes.st5_t_lt_one
#check @RBM.Gauss.Sizes.st5_eventually_A_ge_one
#check @RBM.Gauss.Sizes.st5_compare_I
#check @RBM.Gauss.Sizes.st5_prec_of_isEmpty
#check @RBM.Gauss.Sizes.ST_step5_caseI_of_pins
#check @RBM.Gauss.Sizes.st5_mE_im_le_one
#check @RBM.Gauss.Sizes.st5_Bctl_le_one
#check @RBM.Gauss.Sizes.st5_exp_one_lt_three
#check @RBM.Gauss.Sizes.st5_compare_IV
#check @RBM.Gauss.Sizes.stStep5IV_holds
#check @RBM.Gauss.Step5Inst.inst_step5I
#check @RBM.Gauss.Step5Inst.inst_step5II
#check @RBM.Gauss.Step5Inst.inst_step5III
#check @RBM.Gauss.Step5Inst.inst_step5IV
#check @RBM.Gauss.Step5Inst.inst_step5IV_proved
#check @RBM.Gauss.Step5Inst.inst_step5
#check @RBM.Gauss.Step5Inst.inst_assembly
#check @RBM.Gauss.Step5Inst.inst_skeletonI
-- `Induction/Step5Cases.lean`
#check @RBM.Gauss.Sizes.st5_prec_mono'
#check @RBM.Gauss.Sizes.st5_one_add_log_pow_le
#check @RBM.Gauss.Sizes.st5_ellT_one
#check @RBM.Gauss.Sizes.st5_Bctl_ge_III
#check @RBM.Gauss.Sizes.st5_STWB_ge_III
#check @RBM.Gauss.Sizes.st5_compare_IIIa
#check @RBM.Gauss.Sizes.st5_compare_IIIb
#check @RBM.Gauss.Sizes.st5_polylog_le_W
#check @RBM.Gauss.Sizes.ST_step5_caseIII_of_pf
#check @RBM.Gauss.Sizes.st5_mE_im_ge
#check @RBM.Gauss.Sizes.st5_A15_le
#check @RBM.Gauss.Sizes.st5_compare_IIward
#check @RBM.Gauss.Sizes.st5_reg5II_mid
#check @RBM.Gauss.Sizes.ST_step5_caseII_of_pins
#check @RBM.Gauss.Step5Inst.inst_skeletonII
#check @RBM.Gauss.Step5Inst.inst_skeletonIII
-- `Induction/Step5Kernel.lean`
#check @RBM.step5Kernel_decompU
#check @RBM.step5Kernel_UN_decompU
#check @RBM.step5Kernel_norm_Theta_eq_re
#check @RBM.step5Kernel_theta_decay
#check @RBM.step5Kernel_profile_explicit_holds
#check @RBM.step5Kernel_profile_holds
#check @RBM.step5Kernel_profile_not_unconditional
#check @RBM.Gauss.Sizes.step5Kernel_Th
#check @RBM.Gauss.Sizes.step5Kernel_calA
#check @RBM.Gauss.Sizes.step5Kernel_calA_holds
#check @RBM.Gauss.Sizes.step5Kernel_calA_explicit_holds
#check @RBM.Gauss.Sizes.step5Kernel_calA_sup_holds
#check @RBM.step5Kernel_instSz
#check @RBM.step5Kernel_decompU_inst
#check @RBM.step5Kernel_UN_decompU_inst
#check @RBM.step5Kernel_row_sum_inst
#check @RBM.step5Kernel_profile_inst
#check @RBM.step5Kernel_profile_explicit_inst
#check @RBM.step5Kernel_calA_inst
#check @RBM.step5Kernel_calA_explicit_inst
#check @RBM.step5Kernel_calA_sup_inst
-- `Induction/TailtoTail.lean`, `Induction/TailtoTailSq.lean`
#check @RBM.Gauss.Sizes.stTailtoTail_holds
#check @RBM.Gauss.Sizes.inst_tailtoTail_zero
#check @RBM.Gauss.Sizes.inst_tailtoTail_extremal
#check @RBM.Gauss.Sizes.tailtoTailSq_kernelGen
#check @RBM.Gauss.Sizes.tailtoTailSq_kernel
#check @RBM.Gauss.Sizes.inst_tailtoTailSq_c
-- `Induction/WardII.lean`, `Induction/NewKLKL.lean`
#check @RBM.Gauss.Sizes.stWardII_identity
#check @RBM.Gauss.Sizes.stWardII_holds
#check @RBM.Gauss.Sizes.stNewKLKL_holds

/-! ## Part 4: not this row -/
-- U5 (T2459 U5-1): the band case-(iii) kernel bounds `STTailtoTail`, `tailtoTailSq_kernel` get no generic proof here
#check @RBM.Gauss.Sizes.STTailtoTail
