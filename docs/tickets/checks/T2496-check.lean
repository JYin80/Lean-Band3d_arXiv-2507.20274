/-
Release check for T2496 (dispatcher V3, 2026-10-13 07:57 UTC; DECISIONS §298).  U U4s3 (sub-stage U, ST side): Step 5 cases (i)-(ii), the
ℰ-terms, the integrated hierarchy and `lem_dec_calE` over the flow carrier, converted IN PLACE in the band files
`Induction/LemDecCalELip`, `EtermsMid`, `DuhamelI`, `DuhamelII` (sibling `Induction/DuhamelI2`, new); `LemDecCalEPrec` stays band
(D4 draft).  Supervisor 0658 UP-C2: band statements generalized over the carrier, every frozen or outside-read band declaration
kept as a band corollary with its old name and type (G1).
Part 1: merged names.  Part 2: Prop values (prefix `T2496_`).  Binding: `T2496_LemDecCalEConclgL`, `T2496_LemDecCalEgL`,
`T2496_BandLemDecCalE` and the three conclusion heads `T2496_EtermsMidHead`, `T2496_DuhamelIHead`, `T2496_DuhamelIIHead` (their
hypothesis lists are fixed at the 1a-audit).  Design-gate defaults (text fixed at the 1a-audit): `T2496_DuhamelForm` (D1),
`T2496_FlowMod` (D2).  Then shapes (not binding): D3 (the `𝒦` modulus at `k = 2`, the text of `T2491_KLip`), band and BA
readings, R1.
Part 3 (G1): the frozen and outside-read band names; statements unchanged after the row (the auditor adds the G1 lines).
Merged names only; statements only.
Run: lake env lean docs/tickets/checks/T2496-check.lean
-/
import RBM3D.Induction.DuhamelII
import RBM3D.Induction.LemDecCalEPrec
import RBM3D.Induction.ContinuityNet
import RBM3D.Chain.Step5Gen
import RBM3D.Chain.Step5CasesGen
import RBM3D.Chain.Step5KerGen
import RBM3D.Chain.IniTermIIGen
import RBM3D.Chain.CltFarUGen
import RBM3D.Chain.IniTermIGen2
import RBM3D.Chain.Step34Gen
import RBM3D.Chain.StepDecompGen
import RBM3D.Chain.GridRepTailGen
import RBM3D.Chain.NQGood1Gen
import RBM3D.Chain.NewKLKGen
import RBM3D.Chain.NewKLKLGen
import RBM3D.Chain.Step2EventsGen
import RBM3D.Chain.Step2IterGen2
import RBM3D.BA.FlowPins
import RBM3D.BA.Step2BA
import RBM3D.BA.GridMartBA
import RBM3D.BA.GridRepTailBA
import RBM3D.BA.GreenSchur
import RBM3D.BA.GreenLDE
import RBM3D.BA.Ward
import RBM3D.BA.NewKLKBA
import RBM3D.BA.Step2IterBA
import RBM3D.BA.EMn2BA
import RBM3D.BA.KInduct
import RBM3D.BA.NetLiftBA

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- U6 (`Chain/Step5Gen`): the three pins this row proves, their conclusions, shape and band bridges
#check @RBM.BA.STEtermsMidgL
#check @RBM.BA.STDuhamelIgL
#check @RBM.BA.STDuhamelIIgL
#check @RBM.BA.STEtermsMidConclgL
#check @RBM.BA.STDuhamelConclgL
#check @RBM.BA.STIngR5gL
#check @RBM.BA.STLK2g
#check @RBM.BA.STELKLKg
#check @RBM.BA.STEtermsMid_iff_gL
#check @RBM.BA.STDuhamelI_iff_gL
#check @RBM.BA.STDuhamelII_iff_gL
#check @RBM.BA.bandFM_STEtermsMidConcl
#check @RBM.BA.bandFM_STDuhamelConcl
#check @RBM.BA.bandFM_STLK2
#check @RBM.BA.bandFM_STELKLK
#check @RBM.BA.Step5Gen_ingR5_iff_congr
-- the carrier, the Step 2 vocabulary and the pins EtermsMid reads (row 0, T8b, T1, U3s1)
#check @RBM.BA.FlowFM
#check @RBM.BA.Step2Mat
#check @RBM.BA.bandFM
#check @RBM.BA.bandStep2Mat
#check @RBM.BA.PrecL
#check @RBM.BA.STEGtg
#check @RBM.BA.bandFM_STEGt
#check @RBM.BA.STEEg
#check @RBM.BA.STeeg
#check @RBM.BA.bandStep34_STee
#check @RBM.BA.STLmaxUgL
#check @RBM.BA.STLKUgL
#check @RBM.BA.STStep2ConclgL
#check @RBM.BA.STGdecayWgL
#check @RBM.BA.STDecayStronggL
#check @RBM.BA.STLWTgL
#check @RBM.BA.STEMn2ExpgL
#check @RBM.Gauss.Sizes.stEMn2ExpgL_of
#check @RBM.Gauss.Sizes.emn2ExpFacts
#check @RBM.Gauss.Sizes.emn2ExpHK
#check @RBM.BA.ST_LW_sectionsg
#check @RBM.BA.STBdatagL
#check @RBM.BA.stBdatagL_band
#check @RBM.BA.stLWTgL_of_LWtermExpG
#check @RBM.BA.STNewKLKLgL'
#check @RBM.BA.stNewKLKLgL'_of
#check @RBM.BA.STK2decaygL'
#check @RBM.BA.stK2decaygL_of_primed
#check @RBM.BA.stK2decaygL'_band
-- the grid layer (TN-C4: `STGridMartgL` or `STGridRepNAtgL d 2` only; `STGridRepNgL` is named here to be excluded)
#check @RBM.BA.STGridMartgL
#check @RBM.BA.STGridRepNAtgL
#check @RBM.BA.STGridRepNgL
#check @RBM.BA.Step2Gen_UN
#check @RBM.BA.Step2Gen_ThetaN
#check @RBM.BA.Step2Gen_uKer
#check @RBM.BA.GridRepTailGen_Ker
#check @RBM.BA.Step2EventsGen_Grid
-- U4s1, U4s2 (`Chain/Step5CasesGen`, `Step5KerGen`, `IniTermIIGen`, `CltFarUGen`, `IniTermIGen2`)
#check @RBM.BA.Step5CasesGen_FlowFacts
#check @RBM.BA.step5CasesGen_flowFacts_band
#check @RBM.BA.ST_step5_caseI_of_pinsgL
#check @RBM.BA.ST_step5_caseII_of_pinsgL
#check @RBM.BA.Step5KerGen_ThDecay
#check @RBM.BA.step5KerGen_profile_holds
#check @RBM.BA.Step5KerGen_UN_decomp
#check @RBM.BA.IniTermGen_KerFacts
#check @RBM.BA.iniTermGen_kerFacts_band
#check @RBM.BA.stIngR5gL_hyps_restrict
#check @RBM.BA.stIniTermIgL_of
#check @RBM.BA.stIniTermIIgL_of
-- T5s2, U3s1, U3s2a (`StepDecompGen`, `Step34Gen`, `NQGood1Gen`, merged 9df6a9e7): loop form, compatibility, crude and shift bounds
#check @RBM.BA.StepDecompGen_LoopForm
#check @RBM.BA.stepDecompGen_loopForm_band
#check @RBM.BA.Step34Gen_LCompat
#check @RBM.BA.Step34Gen_KCompat
#check @RBM.BA.bandStep34_LCompat
#check @RBM.BA.norm_loopFine_crudeNg
#check @RBM.BA.loopFine_shiftNg_le
-- the net-lift engine and the band good event (model-free; D2 band discharge)
#check @RBM.Gauss.HighProbAt
#check @RBM.Ind.ContinuityNet.contGood
#check @RBM.Ind.ContinuityNet.cont_highProbAt_good
#check @RBM.Ind.ContinuityNet.cont_core
#check @RBM.Gauss.Sizes.seqHflow
-- BA sources of the family premises (merged)
#check @RBM.BA.baFMz
#check @RBM.BA.baStep2Mat
#check @RBM.BA.baStep2Mat_toFlowFM
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs
#check @RBM.BA.baGridMart_holds
#check @RBM.BA.gridRepTailGen_ker_BA
#check @RBM.BA.BAflow_real
#check @RBM.BA.ba_G_data
#check @RBM.BA.BAm_norm_le_one
#check @RBM.BA.EMn2BA_T0_lt_one
#check @RBM.BA.EMn2BA_mF_data
#check @RBM.BA.baEMn2ExpFacts
#check @RBM.BA.baEMn2ExpHK
#check @RBM.BA.stK2decaygL'_ba
#check @RBM.BA.baSTBdatagL_holds
#check @RBM.BA.baKsol_two
#check @RBM.BA.baNetLift2_holds

/-! ## Part 2: the target statements, then shapes (not binding) -/

open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Target 2, `STLemDecCalEConclgL`** (binding; T2458 item 11 moved here, `T2458-prove.md:186`): `lem_dec_calE` (`3_5:2314-2338`)
over a sample carrier `(Cm, Hf)` and a law `μ`, the text of `STLemDecCalEConcl` (`Step5Pins:161`) with `STLK2g`, `STELKLKg`,
`STEGtg` of `Cm.toFlowFM` and U3s1's `STeeg Cm Hf`. -/
def T2496_LemDecCalEConclgL {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz)
    (Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ Jst : ℕ → ℝ → ℝ → ℝ, (∀ n u D, 1 ≤ Jst n u D) →
    (∀ n u D, Jst n u D ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ)) →
    ∀ D : ℝ, 0 < D →
      (∀ᶠ n in atTop, (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D) →
      PrecL sz μ (U := STIdx2 sz s t)
        (fun n p ω => STLK2g Cm.toFlowFM n (p.1 : ℝ) p.2.1 p.2.2 ω)
        (fun n p _ => Jst n (p.1 : ℝ) D * STtailTD sz n (p.1 : ℝ) D p.2.2) →
      PrecL sz μ (U := STIdx2 sz s t)
        (fun n p ω => ‖STELKLKg Cm.toFlowFM n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - (p.1 : ℝ)|)⁻¹ * Jst n (p.1 : ℝ) D ^ 2 *
          STtailTD sz n (p.1 : ℝ) D p.2.2) ∧
      PrecL sz μ (U := STIdx2 sz s t)
        (fun n p ω => ‖STEGtg Cm.toFlowFM n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => (1 - (p.1 : ℝ))⁻¹ *
          ((if ((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)
              then 1 else 0) +
            (((sz.W n : ℕ) : ℝ) ^ d * |1 - (p.1 : ℝ)|)⁻¹ ^ (1 / 2 : ℝ) * Jst n (p.1 : ℝ) D ^ (3 / 2 : ℝ)) *
          STtailTD sz n (p.1 : ℝ) D p.2.2) ∧
      PrecL sz μ
        (U := fun n => {q : STIdx2 sz s t n × (Fin 2 → Zd d (sz.L n)) //
          ∀ i : Fin 2, ((zdistInf d (sz.L n) (q.1.2.2 i - q.2 i) : ℕ) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)})
        (fun n q ω => ‖STeeg Cm Hf n (q.1.1.1 : ℝ) ω q.1.1.2.1 q.1.1.2.2 q.1.2‖)
        (fun n q _ => (1 - (q.1.1.1 : ℝ))⁻¹ *
          ((if ((zdistInf d (sz.L n) (q.1.1.2.2 0 - q.1.1.2.2 1) : ℕ) : ℝ) ≤ 4 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)
              then 1 else 0) +
            (((sz.W n : ℕ) : ℝ) ^ d * |1 - (q.1.1.1 : ℝ)|)⁻¹ ^ (1 / 2 : ℝ) * Jst n (q.1.1.1 : ℝ) D ^ (3 : ℝ)) *
          STtailTD sz n (q.1.1.1 : ℝ) D q.1.1.2.2 ^ 2)

/-- **Target 2, `STLemDecCalEgL`** (binding): regime (iii) pin over a sample carrier tuple, the shape of `STSEforLngL`
(`Step34Gen:404`). -/
def T2496_LemDecCalEgL (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngR5gL d STReg5III law Flow (fun sz z => (mkM sz z).toFlowFM) T0
    (fun sz z s t => T2496_LemDecCalEConclgL (mkM sz z) (Hf sz z) (law sz) s t)

/-- **Target 2, band bridge `STLemDecCalE_iff_gL`** (binding; through `Step5Gen_ingR5_iff_congr`, `bandFM_STLK2`, `bandFM_STELKLK`,
`bandFM_STEGt`, `bandStep34_STee`). -/
def T2496_BandLemDecCalE : Prop :=
  ∀ d : ℕ, STLemDecCalE d ↔
    T2496_LemDecCalEgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandStep2Mat sz (STflowE z)) (fun sz _ => seqHflow sz) (fun _ z n => lemT (z n))

/-- **Target 5, conclusion head of `stEtermsMidgL_of`** (binding; band `stEtermsMid_of_LWT`, `EtermsMid:1670`). -/
def T2496_EtermsMidHead (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STEtermsMidgL d law Flow (fun sz z => (mkM sz z).toFlowFM) T0

/-- **Target 8, conclusion head of `stDuhamelIgL_of`** (binding; band `stDuhamelI_holds`, `DuhamelI:1943`). -/
def T2496_DuhamelIHead (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STDuhamelIgL d law Flow (fun sz z => (mkM sz z).toFlowFM) T0

/-- **Target 9, conclusion head of `stDuhamelIIgL_of`** (binding; band `stDuhamelII_holds`, `DuhamelII:923`). -/
def T2496_DuhamelIIHead (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STDuhamelIIgL d law Flow (fun sz z => (mkM sz z).toFlowFM) T0

/-- **D1 default, the grid Duhamel form over the carrier** (text fixed at the 1a-audit): `PfStep5Grid_duhamel_pin`
(`PfStep5Grid:130`) with `Step2Gen_ThetaN`, `Step2Gen_UN` of `C` in place of `ThetaN`, `Ugen` at `mSigma E`; proved from the
model-free private `pfStep5Grid_abs` (`PfStep5Grid:287`, `open private`) and K1-K3 of `GridRepTailGen_Ker` (T2493 1a row 13:
constants `64`, `7`). -/
def T2496_DuhamelForm {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) : Prop :=
  ∀ (Δ M R : ℝ) (σ : Fin 2 → Bool) (k : ℕ) (u : ℕ → ℝ) (A F Rem Mart : ℕ → (Fin 2 → Zd d (sz.L n)) → ℂ),
    0 ≤ Δ → 0 ≤ u 0 → (∀ j, u (j + 1) = u j + Δ) → u k < 1 →
    (∀ j, j ≤ k → ∀ b, ‖A j b‖ ≤ M) → (∀ j, j ≤ k → ∀ b, ‖Rem j b‖ ≤ R) →
    (∀ j, j ≤ k → ∀ b, A j b = A 0 b + (Δ : ℂ) * ∑ i ∈ Finset.range j,
        (Step2Gen_ThetaN C n σ (u i) (A i) b + F i b) + Rem j b + Mart j b) →
    ∀ a, ‖A k a - Step2Gen_UN C n σ (u 0) (u k) (A 0) a -
        ∑ j ∈ Finset.range k, (Δ : ℂ) * Step2Gen_UN C n σ (u j) (u k) (F j) a -
        ∑ j ∈ Finset.range k, Step2Gen_UN C n σ (u j) (u k) (fun b => Mart (j + 1) b - Mart j b) a‖ ≤
      64 * ((1 - u k)⁻¹) ^ 7 * (R + Δ * M)

/-- **D2 default, the flow modulus** (text fixed at the 1a-audit): a model matrix `Hm` reading the loops (the second conjunct of
F9 `Step2EventsGen_Grid`), Hermitian, Hölder-1/2 in the time entrywise with exponent `c` on a high-probability event `G`.
Band: `Hm = seqHflow sz` (`√u • seqXmat`), `G = contGood sz` (`cont_highProbAt_good`), `c = 1`; BA: `g₀ Ψ + seqHflow (sz.withLam 0)`,
`G = contGood (sz.withLam 0)` (the `g₀ Ψ` shift cancels in differences; U4-BA). -/
def T2496_FlowMod {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ) (c : ℝ) : Prop :=
  ∃ (Hm : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (G : ℕ → Set sz.SeqΩ),
    (∀ (n : ℕ) (u : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) ω, Cm.LM n u (Hm n u ω) σ a = Cm.L n u σ a ω) ∧
    HighProbAt μ sz.size G ∧
    ∀ n, ∀ ω ∈ G n, ∀ u u' : ℝ, 0 ≤ u → u ≤ 1 → 0 ≤ u' → u' ≤ 1 → (Hm n u ω).IsHermitian ∧
      ∀ x y, ‖Hm n u ω x y - Hm n u' ω x y‖ ≤ ((sz.size n : ℕ) : ℝ) ^ c * Real.sqrt |u - u'|

/-! ### Shapes (not binding) -/

/-- D1 as used: per index, from K1-K4. -/
example : Prop := ∀ {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ), GridRepTailGen_Ker C n → T2496_DuhamelForm C n

/-- D2 family form (guarded; the exponent `c` is pinned before `(sz, z)`). -/
example : Prop := ∀ (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz),
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ c : ℝ, 0 ≤ c ∧
    ∀ (sz : Sizes d) (𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → T2496_FlowMod (mkM sz z) (law sz) c

/-- D3 (inline premise, no name): the time modulus of `𝒦^{(2)}` = `T2491_KLip C t 2` (T2491 check `:363`; owner T2491, U3s2c,
`NQEndFlowGen_KLip`; not importable from `LemDecCalELip`, which `NQEndFlowLift` imports). -/
example : Prop := ∀ {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (t : ℕ → ℝ),
  ∀ᶠ n in atTop, ∀ u u' : ℝ, 0 ≤ u → u ≤ t n → 0 ≤ u' → u' ≤ t n →
    ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      ‖C.K n u σ a - C.K n u' σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * 2 + 2) * |u - u'|

/-- The spectral premise (inline, T2491 D3 text): `‖m‖ ≤ 1` under the flow (band `norm_mE`; BA `ba_G_data`, `BAm_norm_le_one`). -/
example : Prop := ∀ (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz),
  ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ n : ℕ, ‖(mkM sz z).m n‖ ≤ 1

/-- Targets 2, 5, 8, 9 at the band tuple (`seqP`, `STFlow`, `bandStep2Mat ∘ STflowE`, `lemT`); then the `_iff_gL` bridges give
`stEtermsMid_of_LWT` (from `STLWT`), `stDuhamelI_holds`, `stDuhamelII_holds`. -/
example : Prop := ∀ d : ℕ,
  T2496_DuhamelIHead d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandStep2Mat sz (STflowE z)) (fun _ z n => lemT (z n)) ∧
    T2496_DuhamelIIHead d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandStep2Mat sz (STflowE z)) (fun _ z n => lemT (z n)) ∧
    (STLWT d → T2496_EtermsMidHead d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandStep2Mat sz (STflowE z)) (fun _ z n => lemT (z n)))

/-- The BA readings (U4-BA (b)): targets 5, 8, 9 at `(seqP ∘ withLam 0, BAFlow, baStep2Mat (BAflowLam0) (BAflowEs), BAflowT0)`. -/
example : Prop := ∀ d : ℕ,
  T2496_EtermsMidHead d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => BAflowT0 sz z) ∧
    T2496_DuhamelIHead d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => BAflowT0 sz z) ∧
    T2496_DuhamelIIHead d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => BAflowT0 sz z)

/-- Family rows 1-4 at BA (merged sources; row 2 is U4-BA (a)). -/
example : Prop := ∀ d : ℕ,
  Step5CasesGen_FlowFacts d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) ∧
    IniTermGen_KerFacts d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowLam0 sz z) ∧
    STGridMartgL d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => BAflowT0 sz z)

/-- UBA-C1 (DECISIONS §273 (1)): the only comparison text (inside `IniTermGen_KerFacts`). -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (gK : ℕ → ℝ) (A : ℝ),
  ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2

/-- The per-index consequence of R1 (a private three-line helper, guard (g)). -/
example : Prop := ∀ g l A : ℝ, (0 ≤ g * l ∧ g ^ 2 ≤ l ^ 2 ∧ l ^ 2 ≤ A * g ^ 2) →
  (0 < g → 0 < l ∧ g ≤ l) ∧ (0 < l → 0 < g)

end RBM.BA

end

/-! ## Part 3 (G1): frozen and outside-read band names; name and statement unchanged after the row -/

-- the three frozen endpoints (readers `MainIndHolds:45, 49, 53`, `MainIndOut:159, 163-164`) and their pins
#check @RBM.Gauss.Sizes.STEtermsMid
#check @RBM.Gauss.Sizes.STDuhamelI
#check @RBM.Gauss.Sizes.STDuhamelII
#check @RBM.Gauss.Sizes.STEtermsMidConcl
#check @RBM.Gauss.Sizes.STDuhamelConcl
#check @RBM.Gauss.Sizes.STIngR5
#check @RBM.Gauss.Sizes.stEtermsMid_of_LWT
#check @RBM.Gauss.Sizes.stDuhamelI_holds
#check @RBM.Gauss.Sizes.stDuhamelII_holds
#check @RBM.Gauss.Sizes.stDuhamelConcl_engine
-- `lem_dec_calE`: band pin and endpoint (unchanged; D4)
#check @RBM.Gauss.Sizes.STLemDecCalE
#check @RBM.Gauss.Sizes.STLemDecCalEConcl
#check @RBM.Gauss.Sizes.stLemDecCalE_holds
-- `LemDecCalELip` names read outside the five files (U3s2 `NQEndFlowLift`, U3s4 `Qt*Lift`, V1s3 `ExpIntIQ`, U5 `PfStep5*`)
#check @RBM.Gauss.Sizes.LemDecCalELip_Lloop_sub
#check @RBM.Gauss.Sizes.LemDecCalELip_STKloop_two_norm
#check @RBM.Gauss.Sizes.LemDecCalELip_env
#check @RBM.Gauss.Sizes.LemDecCalELip_LK2
#check @RBM.Gauss.Sizes.LemDecCalELip_relcont
#check @RBM.Gauss.Sizes.LemDecCalELip_tail_pos
#check @RBM.Gauss.Sizes.LemDecCalELip_Jsharp_basic
-- read inside the row (EtermsMid, DuhamelII, LemDecCalEPrec); §4 names converted with band corollaries, `_lift` (§7) unchanged
#check @RBM.Gauss.Sizes.LemDecCalELip_LK_sub
#check @RBM.Gauss.Sizes.LemDecCalELip_ee_sub
#check @RBM.Gauss.Sizes.LemDecCalELip_ELKLK
#check @RBM.Gauss.Sizes.LemDecCalELip_EGt
#check @RBM.Gauss.Sizes.LemDecCalELip_ee
#check @RBM.Gauss.Sizes.LemDecCalELip_lift
-- definitions that band readers outside unfold (never converted: `PfStep5Grid:193`, `PfStep5:364, 1093-1142`)
#check @RBM.Gauss.Sizes.LemDecCalELip_Jsharp
#check @RBM.Gauss.Sizes.lemDecCalEPrec_good
#check @RBM.Gauss.Sizes.lemDecCalEPrec_R1
#check @RBM.Gauss.Sizes.lemDecCalEPrec_R2₀
#check @RBM.Gauss.Sizes.lemDecCalEPrec_R2
#check @RBM.Gauss.Sizes.lemDecCalEPrec_R3₀
#check @RBM.Gauss.Sizes.lemDecCalEPrec_R3
-- `LemDecCalEPrec` names read outside (`PfStep5`, `PfStep5Alg`, V1s3 `ExpWardI`); the file is not edited (D4)
#check @RBM.Gauss.Sizes.lemDecCalEPrec_lossWG_eventually
#check @RBM.Gauss.Sizes.lemDecCalEPrec_STKloop_one
#check @RBM.Gauss.Sizes.lemDecCalEPrec_Kbound
#check @RBM.Gauss.Sizes.lemDecCalEPrec_gij
#check @RBM.Gauss.Sizes.lemDecCalEPrec_prob
#check @RBM.Gauss.Sizes.lemDecCalEPrec_goodDet
#check @RBM.Gauss.Sizes.lemDecCalEPrec_numeric
#check @RBM.Gauss.Sizes.lemDecCalEPrec_kell
#check @RBM.Gauss.Sizes.lemDecCalEPrec_QW
#check @RBM.Gauss.Sizes.lemDecCalEPrec_card_V12
#check @RBM.Gauss.Sizes.lemDecCalEPrec_lift
#check @RBM.Gauss.Sizes.lemDecCalEPrec_tail_ge
#check @RBM.Gauss.Sizes.lemDecCalEPrec_htN
-- band inputs replaced in the generic text (not edited): the grid Duhamel pin, the all-`m` grid route (TN-C4), the crude bound
#check @RBM.Gauss.Sizes.PfStep5Grid_duhamel_pin
#check @RBM.Gauss.Sizes.pfStep5Grid_duhamel
#check @RBM.Gauss.Sizes.ST_gridMart_of_repN
#check @RBM.Ind.stGridRepN_holds
#check @RBM.Ind.norm_loopFine_crudeN
#check @RBM.Gauss.Sizes.STLK2
#check @RBM.Gauss.Sizes.STELKLK
#check @RBM.Gauss.Sizes.STEGt
#check @RBM.Gauss.Sizes.STee
#check @RBM.Gauss.Sizes.STtailTD
#check @RBM.Gauss.Sizes.STIdx2
-- the compiled instances (patterns of target 10)
#check @RBM.Gauss.Step5Inst.inst_etermsMid
#check @RBM.Gauss.Step5Inst.inst_duhamelI
#check @RBM.Gauss.Step5Inst.inst_duhamelII
#check @RBM.Gauss.Step5Inst.inst_lemDecCalE
#check @RBM.Gauss.Step5Inst.inst_duhamelI_proved
