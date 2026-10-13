/-
Release check for T2484 (dispatcher V3, Tue Oct 13 01:28 UTC 2026; DECISIONS §284).  U U4s2 (sub-stage U, ST side): the initial terms of Step 5 over
the carrier, case (i) `(iksjuwjx0)` with the `u`-uniform `lem;CLT` and the flow-tuple wrapper of X1's far pin, and case (ii)
`(zYU2)`, in the new files `Chain/IniTermIIGen.lean` (U4s2a), `Chain/CltFarUGen.lean` and `Chain/IniTermIGen.lean` (U4s2b); the
band files `Induction/IniTermI`, `IniTermII` are not edited (outside the certificate lane).
Part 1: merged names.  Part 2: the target statements as Prop values (prefix `T2484_`).  Binding: the conclusions of
`T2484_IniTermIIOf`, `T2484_CltFarUOf`, `T2484_IniTermIOf` (their hypothesis lists are shapes fixed at the 1a-audit), the
definition `T2484_CltFarUConclgL` and the band bridge `T2484_BandCltFarU`.  Design-gate defaults (D1, D2; their text is fixed
at the 1a-audit): `T2484_KerFacts`, `T2484_CltFlow`.  Then shapes (not binding): the restriction lemma, the band discharges,
the BA readings (U4-BA), the UBA-C1 literal (R1, DECISIONS §273 (1)) and its per-index consequence.
Part 3 (G1): the public band names restated here or read elsewhere, unchanged; the auditor adds `example : <statement> := <name>`.
Merged names only; statements only.
Run: lake env lean docs/tickets/checks/T2484-check.lean
-/
import RBM3D.Evolution.CltFarG
import RBM3D.Evolution.FarEntry
import RBM3D.Evolution.ExpInv
import RBM3D.Induction.IniTermI
import RBM3D.Chain.CltGen
import RBM3D.Chain.Step5Gen
import RBM3D.Chain.Step5CasesGen
import RBM3D.Chain.Step5KerGen
import RBM3D.Chain.ZeroModeGen
import RBM3D.Chain.Step34Gen
import RBM3D.Chain.GridDuhamelGen
import RBM3D.Propagator.Prop5Hold
import RBM3D.Propagator.Prop5Short
import RBM3D.Propagator.Props4
import RBM3D.Green.Pins
import RBM3D.Gauss.BlockAnderson
import RBM3D.BA.FlowPins
import RBM3D.BA.Step2BA
import RBM3D.BA.Prop6Path
import RBM3D.BA.Prop5Short
import RBM3D.BA.TwistStep2
import RBM3D.BA.TwistGrid
import RBM3D.BA.KBase
import RBM3D.BA.KKernel
import RBM3D.BA.EMn2BA
import RBM3D.BA.Ward
import RBM3D.BA.GreenOff

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- U6 (`Chain/Step5Gen`): the conclusions and pins this row proves, their band bridges
#check @RBM.BA.STIniTermIgL
#check @RBM.BA.STIniTermIIgL
#check @RBM.BA.STIniTermConclgL
#check @RBM.BA.STIngR5gL
#check @RBM.BA.STIniTermI_iff_gL
#check @RBM.BA.STIniTermII_iff_gL
#check @RBM.BA.bandFM_STIniTermConcl
#check @RBM.BA.Step5Gen_ingR5_iff_congr
-- the carrier, the Step 1-4 premises of `STIngR5gL` (row 0, T8b, U3s1)
#check @RBM.BA.FlowFM
#check @RBM.BA.bandFM
#check @RBM.BA.PrecL
#check @RBM.BA.STDecaygL
#check @RBM.BA.STStep1LoopgL
#check @RBM.BA.STStep2ConclgL
#check @RBM.BA.STLocalEntryUgL
#check @RBM.BA.STAvgUgL
#check @RBM.BA.STGdecayWgL
#check @RBM.BA.STLmaxUgL
#check @RBM.BA.STLKUgL
-- the one kernel and propagator (U-C4) and T4s1's semigroup law
#check @RBM.BA.Step2Gen_UN
#check @RBM.BA.Step2Gen_uKer
#check @RBM.BA.Step2Gen_thetaKer
#check @RBM.BA.Step2Gen_Theta
#check @RBM.BA.Step2Kern_Mss
#check @RBM.BA.Step2Gen_USemigroup
#check @RBM.BA.step2Gen_USemigroup_band
#check @RBM.BA.bandStep2_Ugen
-- U4s1 (`Chain/Step5CasesGen`, `Step5KerGen`): flow facts, case assemblies, the D2 kernel facts
#check @RBM.BA.Step5CasesGen_FlowFacts
#check @RBM.BA.step5CasesGen_flowFacts_band
#check @RBM.BA.ST_step5_caseI_of_pinsgL
#check @RBM.BA.ST_step5_caseII_of_pinsgL
#check @RBM.BA.Step5KerGen_ThDecay
#check @RBM.BA.step5KerGen_thDecay_band
#check @RBM.BA.step5KerGen_profile_holds
#check @RBM.BA.Step5KerGen_uKer_eq
#check @RBM.BA.Step5KerGen_UN_decomp
-- U1s1 (`Chain/ZeroModeGen`): the one Ward text (UN-C3)
#check @RBM.BA.ZeroModeGen_WardCls
#check @RBM.BA.zeroModeGen_wardCls_band
-- X1a (`Chain/CltGen`): the propagator, `f^{far}`, the premise block and the far pin (X1-C4: imported, never restated)
#check @RBM.BA.STThg
#check @RBM.BA.STfFarg
#check @RBM.BA.STCltFarConclgL
#check @RBM.BA.HCltOf
#check @RBM.BA.CltRepg
#check @RBM.BA.STGijDecgL
#check @RBM.BA.STKfargL
#check @RBM.BA.STMfarg
#check @RBM.BA.STThPropsg
#check @RBM.BA.STKpropsg
#check @RBM.BA.STExpInvgL
#check @RBM.BA.STCltFargL
#check @RBM.BA.cltRepg_band
#check @RBM.BA.bandFM_M_le
#check @RBM.BA.bandFM_STMfarg
#check @RBM.BA.bandFM_STThg
#check @RBM.BA.bandFM_STfFarg
#check @RBM.BA.bandFM_STCltFarConcl
-- X1b (`Evolution/CltFarG`) and the band producers of the wrapper's fields
#check @RBM.BA.stCltFargL_holds
#check @RBM.BA.bandFM_STThPropsg
#check @RBM.BA.bandFM_STKpropsg
#check @RBM.BA.stCltFar_of_gL
#check @RBM.BA.bandFM_STGijDecgL_of_three_le
#check @RBM.BA.bandFM_STKfargL
#check @RBM.BA.stExpInvgL_band
#check @RBM.BA.stExpInvgL_of_rep
#check @RBM.Green.v3_premises_of_stFlow
-- band producers of the D1 fields (target 1 at the band) and the model-free reuse
#check @RBM.prop8ZeroMode_holds
#check @RBM.prop5Short_holds
#check @RBM.prop5Decay_holds
#check @RBM.Theta0_apply_eq
#check @RBM.sum_Theta_row_of_three_le
#check @RBM.Theta_transpose_of_three_le
#check @RBM.Theta_apply_add_right_of_three_le
#check @RBM.ekPropTInf_holds
-- size-level band names reused as they are
#check @RBM.Gauss.Sizes.STReg5I
#check @RBM.Gauss.Sizes.STReg5II
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.STSigAll
#check @RBM.Gauss.Sizes.STSigMixed
#check @RBM.Gauss.Sizes.STSigSame
#check @RBM.Gauss.Sizes.STCltFarIdx
#check @RBM.Gauss.Sizes.STCltFarZeta
-- BA names read in the shapes and in the 1a source tables (U4-BA; names only)
#check @RBM.BA.BAFlow
#check @RBM.BA.baFMz
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs
#check @RBM.BA.baStep2Mat
#check @RBM.BA.TwistStep2_lam0_sq
#check @RBM.BA.BAuKer_self
#check @RBM.BA.BAuKer_comp
#check @RBM.BA.baComp_row_le
#check @RBM.BA.BAProp5s
#check @RBM.BA.BAProp8
#check @RBM.BA.baProp5s_holds
#check @RBM.BA.baProp8_holds
#check @RBM.BA.baProp5to8_holds
#check @RBM.BA.baP8_BATheta_shift
#check @RBM.BA.BATheta_isSymm
#check @RBM.BA.BATheta_row_sum_pm
#check @RBM.BA.BAK_col_sum
#check @RBM.BA.baEMn2ExpHK
#check @RBM.BA.baOffDiag_holds
#check @RBM.BA.baGbEXPij'_holds
#check @RBM.Gauss.PsiI

/-! ## Part 2: the target statements, then shapes (not binding) -/

open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Target 1, class `IniTermGen_KerFacts`** (D1 default; the text is fixed at the 1a-audit): the kernel facts of a flow family
that the initial terms read beyond D2.  The semigroup law (T4s1), the decay and row sums of `thetaKer` at the kernel coupling
`gK` (`Step5KerGen_ThDecay`, one text), the one comparison hypothesis R1, and at each index with `0 < gK n ≤ 𝔡⁻¹` three
entrywise facts of X1a's propagator `STThg` at `gK`: the mixed column sum `(1 - t)⁻¹` (band `IniTermII:963`), the mixed zero
mode `(prop:ThfadC0)` (band `prop8ZeroMode_holds`, `IniTermII:1051`), the same-charge short range `(prop:ThfadC_short)` (band
`prop5Short_holds`, `IniTermII:1378`, `IniTermI:1229`).  Band `gK = sz.lam`, `A = 1`; BA `gK = BAflowLam0 sz z`,
`A = (κ+1)/κ` (stage P at `g₀`, U4-BA (a)). -/
def T2484_KerFacts (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C₆ C₈ Cs c₀ A : ℝ, 0 < C₆ ∧ 0 < C₈ ∧ 0 < Cs ∧ 0 < c₀ ∧ 1 ≤ A ∧
    ∀ (sz : Sizes d) (ε 𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      (∀ n : ℕ, Step2Gen_USemigroup (mk sz z) n) ∧
      Step5KerGen_ThDecay (mk sz z) (gK sz z) 𝔡⁻¹ C₆ ∧
      (∀ n : ℕ, 0 ≤ gK sz z n * sz.lam n ∧ gK sz z n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK sz z n ^ 2) ∧
      ∀ n : ℕ, 0 < gK sz z n → gK sz z n ≤ 𝔡⁻¹ → ∀ t : ℝ, 0 ≤ t → t < 1 →
        (∀ (σ : Bool) (b : Zd d (sz.L n)),
          ∑ a : Zd d (sz.L n), STThg (mk sz z) n σ (!σ) t a b = (((1 - t : ℝ) : ℂ))⁻¹) ∧
        (∀ (σ : Bool) (a b : Zd d (sz.L n)),
          ‖STThg (mk sz z) n σ (!σ) t a b - (((sz.L n : ℕ) : ℂ) ^ d)⁻¹ * (((1 - t : ℝ) : ℂ))⁻¹‖ ≤
            C₈ * (gK sz z n ^ 2 + |1 - t|)⁻¹ * ((((zdistD d (sz.L n) (b - a) : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹) ∧
        ∀ (σ : Bool) (a b : Zd d (sz.L n)),
          ‖STThg (mk sz z) n σ σ t a b‖ ≤
            Cs * ((if a = b then (1 : ℝ) else 0) +
              gK sz z n ^ 2 * Real.exp (-(c₀ * ((zdistD d (sz.L n) (b - a) : ℕ) : ℝ))))

/-- **Target 4, the pin `stIniTermIIgL_of`** (conclusion head `STIniTermIIgL` binding; the hypothesis list is a shape fixed at
the 1a-audit): the initial terms of case (ii) over a carrier tuple, for every law (band `stIniTermII_holds`, `IniTermII:1718`,
re-derived through `STIniTermII_iff_gL`). -/
def T2484_IniTermIIOf : Prop :=
  ∀ (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ),
    Step5CasesGen_FlowFacts d Flow mk T0 → T2484_KerFacts d Flow mk gK →
    STIniTermIIgL d law Flow mk T0

/-- **Target 5, class `IniTermGen_CltFlow`** (D2 default, the flow-tuple wrapper of X1's far pin, §270 (2), §279 (4); the text is
fixed at the 1a-audit): the fields of `HCltOf` that do not depend on the end time, plus `STThPropsg`, `STExpInvgL`, and, at
each start time `s` of a case-(i) window, `STMfarg`, `STGijDecgL`, `STKfargL`, `STKpropsg`.  With the restricted Step-2 premises
(`STLocalEntryUgL`, `STGdecayWgL`) and the flow facts (admissibility) they give `HCltOf` at every grid time `t' ∈ (s, t]`.  Band:
the construction inside `stCltFar_of_gL` (`Evolution/CltFarG.lean:926-950`), `κ' = cltCk (κ/2)`, `δ = ε/2`; BA: U4-BA (C9). -/
def T2484_CltFlow (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ κ' δ : ℝ, 0 < κ' ∧ κ' ≤ 1 ∧ 0 < δ ∧
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∃ (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (g' E : ℕ → ℝ),
        (∀ n, κ' ≤ ((mk sz z).m n).im) ∧
        (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - T0 sz z n) ∧
        CltRepg (mk sz z) (law sz) H₀ g' E ∧
        (∀ n x, ∑ y, ‖(mk sz z).M n x y‖ ^ 2 ≤ 1) ∧
        STThPropsg (mk sz z) ∧ STExpInvgL (mk sz z) (law sz) ∧
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ T0 sz z n) → STReg5I sz s t →
          STMfarg (mk sz z) s ∧ STGijDecgL (mk sz z) (law sz) s ∧ STKfargL (mk sz z) s ∧ STKpropsg (mk sz z) s

/-- **Target 6, `STCltFarUConclgL`** (binding): `lem;CLT` uniformly in the propagator time `u ∈ [s,t]` over a carrier, on the
index set of `STCltFarConcl` with `ℓ_u` in place of `ℓ_t` (band `STCltFarUConcl`, `IniTermI:1786`; paper-delta `T2329b`). -/
def T2484_CltFarUConclgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => Σ u : TimeIcc s t n, sz.STCltFarIdx s n (u : ℝ))
    (fun n q ω => ‖STfFarg C n (s n) (q.1 : ℝ) q.2.1.1.1 q.2.1.2 ω‖)
    (fun n q _ => sz.STCltFarZeta n q.2.1.2)

/-- **Target 6, band bridge `bandFM_STCltFarUConcl`** (binding; through `bandFM_STfFarg`). -/
def T2484_BandCltFarU : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ),
    sz.STCltFarUConcl E s t ↔ T2484_CltFarUConclgL (bandFM sz E) (Sizes.seqP sz) s t

/-- **Target 7, `stCltFarUgL_of`** (conclusion binding; the hypothesis list is a shape fixed at the 1a-audit): the `u`-uniform
`lem;CLT` as a Step-5 pin of case (i) over a carrier tuple (band `stCltFar_uniform`, `IniTermI:2005`, re-derived through
`Step5Gen_ingR5_iff_congr` and target 6).  X1's far pin is `stCltFargL_holds` (merged), not a hypothesis. -/
def T2484_CltFarUOf : Prop :=
  ∀ (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ),
    (∀ sz : Sizes d, IsProbabilityMeasure (law sz)) →
    Step5CasesGen_FlowFacts d Flow mk T0 → T2484_KerFacts d Flow mk gK → T2484_CltFlow d law Flow mk T0 →
    STIngR5gL d STReg5I law Flow mk T0 (fun sz z s t => T2484_CltFarUConclgL (mk sz z) (law sz) s t)

/-- **Target 9, the pin `stIniTermIgL_of`** (conclusion head `STIniTermIgL` binding; the hypothesis list is a shape fixed at the
1a-audit): the initial term of case (i) over a carrier tuple (band `stIniTermI_holds`, `IniTermI:3715`, re-derived through
`STIniTermI_iff_gL`).  The Ward step reads the one Ward text `ZeroModeGen_WardCls` (UN-C3). -/
def T2484_IniTermIOf : Prop :=
  ∀ (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ),
    (∀ sz : Sizes d, IsProbabilityMeasure (law sz)) →
    Step5CasesGen_FlowFacts d Flow mk T0 → T2484_KerFacts d Flow mk gK →
    (∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ZeroModeGen_WardCls sz (mk sz z)) →
    T2484_CltFlow d law Flow mk T0 →
    STIniTermIgL d law Flow mk T0

/-! ### Shapes (not binding) -/

/-- Target 6, `stIngR5gL_hyps_restrict` (band `stIngR5_hyps_restrict`, `IniTermI:1577`): the premises of a case-(i) pin restrict
from `[s,t]` to `[s,t']`, `s < t' ≤ t`. -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t t' : ℕ → ℝ) (𝔠d Cd : ℝ),
  0 < 𝔠d → (∀ n, s n < t' n) → (∀ n, t' n ≤ t n) → (∀ n, t n < 1) →
  STReg5I sz s t → sz.STConStInd 𝔠d s t → STStep1LoopgL C μ s t → STStep2ConclgL C μ s t Cd →
  STLmaxUgL C μ s t → STLKUgL C μ s t →
  STReg5I sz s t' ∧ sz.STConStInd 𝔠d s t' ∧ STStep1LoopgL C μ s t' ∧ STStep2ConclgL C μ s t' Cd ∧
    STLmaxUgL C μ s t' ∧ STLKUgL C μ s t'

/-- Targets 1 and 5 at the band family `(seqP, STFlow, bandFM ∘ STflowE, lemT)`, `gK = sz.lam`. -/
example : Prop := ∀ d : ℕ,
  T2484_KerFacts d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun sz _ => sz.lam) ∧
    T2484_CltFlow d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))

/-- Targets 4 and 9 at the band family (then `STIniTermII_iff_gL`, `STIniTermI_iff_gL` give `stIniTermII_holds`, `stIniTermI_holds`). -/
example : Prop := ∀ d : ℕ,
  STIniTermIIgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) ∧
    STIniTermIgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))

/-- The BA readings (U4-BA (a), (b); C9): targets 1 and 5 at `(seqP ∘ withLam 0, BAFlow, baFMz, BAflowT0)`, `gK = BAflowLam0`. -/
example : Prop := ∀ d : ℕ,
  T2484_KerFacts d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowLam0 sz z) ∧
    T2484_CltFlow d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)

/-- The other BA inputs of targets 4, 7, 9: the flow facts (U4-BA (b)) and the Ward class (the UN-C3 owner, U1-BA or U4-BA (b)). -/
example : Prop := ∀ d : ℕ,
  Step5CasesGen_FlowFacts d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) ∧
    ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → ZeroModeGen_WardCls sz (baFMz sz z)

/-- The BA conclusions (U4-BA (b)): targets 4 and 9 at the BA carrier tuple. -/
example : Prop := ∀ d : ℕ,
  STIniTermIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) ∧
    STIniTermIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)

/-- UBA-C1 (DECISIONS §273 (1)): the only comparison text (a conjunct of target 1). -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (gK : ℕ → ℝ) (A : ℝ),
  ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2

/-- The per-index consequence of R1 (private three-line lemma; as `Step5KerGen_cmp_pos`, `Step5KerGen:263`). -/
example : Prop := ∀ g l A : ℝ, (0 ≤ g * l ∧ g ^ 2 ≤ l ^ 2 ∧ l ^ 2 ≤ A * g ^ 2) →
  (0 < g → 0 < l ∧ g ≤ l) ∧ (0 < l → 0 < g)

end RBM.BA

end

/-! ## Part 3 (G1): public band names restated here or read elsewhere; statements unchanged -/

-- the two pins (readers `MainIndHolds:49, 53`, `MainIndOut:163-164`) and their statements
#check @RBM.Gauss.Sizes.STIniTermI
#check @RBM.Gauss.Sizes.STIniTermII
#check @RBM.Gauss.Sizes.STIniTermConcl
#check @RBM.Gauss.Sizes.stIniTermI_holds
#check @RBM.Gauss.Sizes.stIniTermII_holds
-- the band statements restated over the carrier (targets 2-3, 6-8)
#check @RBM.Gauss.Sizes.STCltFar
#check @RBM.Gauss.Sizes.STCltFarUConcl
#check @RBM.Gauss.Sizes.stCltFar_uniform
#check @RBM.Gauss.Sizes.stIngR5_hyps_restrict
#check @RBM.Gauss.Sizes.iniTermII_core
#check @RBM.Gauss.Sizes.iniTermII_core_same
#check @RBM.Gauss.Sizes.iniTermII_concl
#check @RBM.Gauss.Sizes.iniTermI_stageA
#check @RBM.Gauss.Sizes.iniTermI_Ugen_rep
#check @RBM.Gauss.Sizes.iniTermI_core_same
#check @RBM.Gauss.Sizes.iniTermI_core_mixed
#check @RBM.Gauss.Sizes.iniTermI_core_lossy
#check @RBM.Gauss.Sizes.iniTermI_Sfull_decomp
#check @RBM.Gauss.Sizes.iniTermI_Theta_lip
#check @RBM.Gauss.Sizes.iniTermI_fSum_lip
#check @RBM.Gauss.Sizes.iniTermI_grid
#check @RBM.Gauss.Sizes.iniTermI_theta_pi
#check @RBM.Gauss.Sizes.iniTermI_theta_far
#check @RBM.Gauss.Sizes.iniTermI_theta_conv
#check @RBM.Gauss.Sizes.iniTermI_mixed_bound
#check @RBM.Gauss.Sizes.iniTermI_mixed_tail
#check @RBM.Gauss.Sizes.iniTermI_ward
#check @RBM.Gauss.Sizes.iniTermI_ward_bound
#check @RBM.Gauss.Sizes.iniTermI_rl_all
#check @RBM.Gauss.Sizes.iniTermI_concl
-- the compiled instances (patterns of target 10)
#check @RBM.Gauss.Step5Inst.iniTermII_core_inst
#check @RBM.Gauss.Step5Inst.iniTermII_core_same_inst
#check @RBM.Gauss.Step5Inst.iniTermII_concl_inst
#check @RBM.Gauss.Step5Inst.inst_iniTermII_proved
#check @RBM.Gauss.Step5Inst.iniTermI_core_same_inst
#check @RBM.Gauss.Step5Inst.iniTermI_core_mixed_inst
#check @RBM.Gauss.Step5Inst.iniTermI_restrict_inst
#check @RBM.Gauss.Step5Inst.inst_cltFarU_proved
#check @RBM.Gauss.Step5Inst.inst_iniTermI_proved
