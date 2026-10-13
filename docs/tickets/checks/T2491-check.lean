/-
Release check for T2491 (dispatcher V3, 2026-10-13 05:43 UTC; DECISIONS §294).  U U3s2 (sub-stage U, ST side): the Step 3 `NQ*` layer
(`lem:STOeq_NQ`, non-alternating, route (R)) over the flow carrier, in the new files `Chain/NQGood1Gen`, `Chain/NQGood2Gen`
(U3s2a), `Chain/NQBudgetGen`, `Chain/NQLinGen` (U3s2b), `Chain/NQEndLinGen`, `Chain/NQEndFlowGen` (U3s2c).  The band files
`Induction/NQGood1`, `NQGood2`, `NQBudget`, `NQLin`, `NQEndLin`, `NQEndFlow`, `NQEndFlowLift` are not edited (outside the lane).
Part 1: merged names.  Part 2: the target statements as Prop values (prefix `T2491_`).  Binding: the definitions
`T2491_GoodLinNg`, `T2491_NQLinConclg`, `T2491_NQLinGoodgL`, the ten R2* texts (`T2491_XiBootgL'` … `T2491_IterationsIIgL'`),
`T2491_HQg` (the conclusion head of `hQ_nonAltNg`), and the conclusions of `T2491_NQLinGoodOf` and `T2491_OeqNQPTOf` (their
hypothesis lists are shapes fixed at the 1a-audit).  Design-gate defaults (text fixed at the 1a-audit): D1 `T2491_KerNAL`,
`T2491_KerNALFam`; D2 `T2491_KLip`, `T2491_KLipFam`; D3 `T2491_ShiftSpec`; the R1 family `T2491_R1Fam` (UBA-C1, DECISIONS
§273 (1)).  Then shapes (not binding): band and BA readings.
Part 3 (G1): the public band names restated here or read in U3s3, U3s4, U1s2, U4s3; unchanged; the auditor adds
`example : <statement> := <name>`.
Merged names only; statements only.
Run: lake env lean docs/tickets/checks/T2491-check.lean
-/
import RBM3D.Induction.NQEndFlowLift
import RBM3D.Chain.AzumaProxyGen
import RBM3D.Chain.GridEnvelopeGen
import RBM3D.Chain.HierDriftGen
import RBM3D.Chain.GridRepTailGen2
import RBM3D.Chain.Step2EventsGenTw
import RBM3D.Chain.DecayGenTw
import RBM3D.Chain.Step34GenTw
import RBM3D.BA.EKSum
import RBM3D.BA.GridRepTailBA
import RBM3D.BA.EMn2BA
import RBM3D.BA.GreenLDE
import RBM3D.BA.Ward
import RBM3D.BA.TwistStep2
import RBM3D.BA.GreenSchur
import RBM3D.BA.Step2BA
import RBM3D.BA.FlowPins

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the carrier and T8b's kernel (U-C4: the one kernel)
#check @RBM.BA.FlowFM
#check @RBM.BA.Step2Mat
#check @RBM.BA.bandFM
#check @RBM.BA.bandStep2Mat
#check @RBM.BA.PrecL
#check @RBM.BA.PrecPTL
#check @RBM.BA.Step2Gen_UN
#check @RBM.BA.bandStep2_Ugen
#check @RBM.BA.Step2Kern_UN_BA
#check @RBM.BA.STksimLKMg
#check @RBM.BA.STelklkMg
#check @RBM.BA.STegtMg
#check @RBM.BA.STLKMg
#check @RBM.BA.STKboundgL
#check @RBM.BA.STKwardgL
#check @RBM.BA.STLKgL
#check @RBM.BA.STStep1LoopgL
#check @RBM.BA.STStep2ConclgL
-- U3s1 (`Chain/Step34Gen`): the setting, the controls, the unprimed `NQ` texts, R1 crossing lemmas
#check @RBM.BA.STIngRgL
#check @RBM.BA.bandFM_STIngR
#check @RBM.BA.STXiLg
#check @RBM.BA.STXiLKg
#check @RBM.BA.STXiBootgL
#check @RBM.BA.STNQConclgL
#check @RBM.BA.STNQConclgL'
#check @RBM.BA.STOeqNQgL
#check @RBM.BA.STIterRgL
#check @RBM.BA.STIterHypgL
#check @RBM.BA.STSEforLngL
#check @RBM.BA.STSEforLnConclgL
#check @RBM.BA.STEKDecaygL
#check @RBM.BA.STLmaxUgL
#check @RBM.BA.STLKUgL
#check @RBM.BA.Step34Gen_LCompat
#check @RBM.BA.Step34Gen_KCompat
#check @RBM.BA.step34Gen_winK_of_cmp
#check @RBM.BA.step34Gen_ratio_pow_le
#check @RBM.BA.step34Gen_decayK_of_cmp
#check @RBM.BA.step34Gen_ellT_ge
#check @RBM.BA.step34Gen_band_hg
-- T4s2 (`Chain/GridGoodGen`, `GridEnvelopeGen`, `GridAssemblyGen`, `AzumaProxyGen`)
#check @RBM.BA.GoodSetNg
#check @RBM.BA.STmaxLMg
#check @RBM.BA.STXiLMg
#check @RBM.BA.STXiLKMg
#check @RBM.BA.goodExitTauNg
#check @RBM.BA.measurableGoodSetNg
#check @RBM.BA.goodExitMeasNg
#check @RBM.BA.GridGoodNConclg
#check @RBM.BA.GridGoodNgL
#check @RBM.BA.gridGoodNConclg_of
#check @RBM.BA.gridGoodNgL_of
#check @RBM.BA.sum_gridStep_div_etaNg_le
#check @RBM.BA.sum_weighted_stepErrNg_le
#check @RBM.BA.gridDriftNg_envelope
#check @RBM.BA.qvFormNg
#check @RBM.BA.GridAssemblyHypNg
#check @RBM.BA.AssembledNg
#check @RBM.BA.assembledNg
#check @RBM.BA.YMomentBoundsNg
#check @RBM.BA.azumaSubGNg
#check @RBM.BA.azumaProxy_subG_ugeng
#check @RBM.BA.azumaProxy_subG_goodExitg
#check @RBM.BA.YMomentsUnifNg
#check @RBM.BA.yMomentsUnifNg
-- T5s2 (`Chain/StepDecompGen`, `HierDriftGen`), P1b-1 (`GridRepTailGen`), T7 (`DecayGen`), T1 / U2 texts
#check @RBM.BA.StepDecompGen_LoopForm
#check @RBM.BA.StepDecompGen_WalkForm
#check @RBM.BA.stepDecompGen_loopForm_band
#check @RBM.BA.stepDecompGen_walkForm_band
#check @RBM.BA.QVPropagatedNg
#check @RBM.BA.qvPropagatedNg
#check @RBM.BA.ZvecNg
#check @RBM.BA.SubGaussStopNg
#check @RBM.BA.stepErrNg
#check @RBM.BA.GridDriftNg
#check @RBM.BA.gridDriftNg
#check @RBM.BA.HierDriftGen_Expand
#check @RBM.BA.HierDriftGen_KLoop
#check @RBM.BA.HierDriftGen_KTwo
#check @RBM.BA.HierDriftGen_UStep
#check @RBM.BA.HierDriftGen_KLink
#check @RBM.BA.GridRepTailGen_Ker
#check @RBM.BA.gridRepTailGen_ker_band
#check @RBM.BA.Step2EventsGen_Law
#check @RBM.BA.Step2EventsGen_Flow
#check @RBM.BA.DecayGen_Spec
#check @RBM.BA.DecayGen_WardPair
#check @RBM.BA.STKcalDecaygL
-- band inputs of D1 and D2, the spectral reading
#check @RBM.ekSumDecayNAL_holds
#check @RBM.EKFastDecay
#check @RBM.Green.etaT_le_of_le
#check @RBM.Green.v3_premises_of_stFlow
#check @RBM.Gauss.Sizes.RangeCond
#check @RBM.Ind.nqGood1_mE_im_ge
-- BA sources of the family premises (read only; owners U3-BA, T5-BA, U2-BA)
#check @RBM.BA.BAEKSumDecayNAL
#check @RBM.BA.baEKSumDecayNAL_holds
#check @RBM.BA.gridRepTailGen_ker_BA
#check @RBM.BA.Step2EventsGenTw_baFlow
#check @RBM.BA.Step2EventsGenTw_baLaw
#check @RBM.BA.DecayGenTw_baWardPair
#check @RBM.BA.EMn2BA_mF_data
#check @RBM.BA.EMn2BA_one_sub_T0
#check @RBM.BA.ba_G_data
#check @RBM.BA.BAm_norm_le_one
#check @RBM.BA.TwistStep2_lam0_sq
#check @RBM.BA.BAflow_lam0_window
#check @RBM.BA.BAflow_real
#check @RBM.BA.baStep2Mat
#check @RBM.BA.baStep2Mat_KI
#check @RBM.BA.baFMz
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs
#check @RBM.BA.BAflowT0

/-! ## Part 2: the target statements, then shapes (not binding) -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Target 8, `GoodLinNg`** (binding; band `GoodLinN`, `Induction/NQLin.lean:66`): the linear set over a carrier, the clauses
(D1'), (D2'), (D3') of `GoodSetNg` at separate deterministic levels; `etaT E u` is `Cm.eta n u`, `sz.Bctl` stays (size level). -/
def T2491_GoodLinNg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (n : ℕ) (u : ℝ) (k : ℕ) (Γ Φ₁ Φ₂ Φ₃ : ℝ) :
    Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
  {H | (∀ l : ℕ, 3 ≤ l → l ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖STksimLKMg Cm n u H l (loopOf σ a)‖ ≤ Γ * (Γ * Φ₁) * ((sz.Bctl n u) ^ k / Cm.eta n u)) ∧
    (∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖STelklkMg Cm n u H (loopOf σ a)‖ ≤ Γ * (Γ * Φ₂) * ((sz.Bctl n u) ^ k / Cm.eta n u)) ∧
    (∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖STegtMg Cm n u H (loopOf σ a)‖ ≤ Γ * (Γ * Φ₃) * ((sz.Bctl n u) ^ k / Cm.eta n u))}

/-- **Target 8, `NQLinConclg`** (binding; band `NQLinConcl`, `NQLin.lean:102`): `Prec sz` is `PrecL sz μ`, `STXiL`/`STXiLK` are
U3s1's `STXiLg`/`STXiLKg`, `pathP`/`pathH` are `Cm.Pp`/`Cm.Hpath`, `GoodLinN` is `T2491_GoodLinNg`; the levels are the band's
model-free `nqLinPhi1`-`3` (reused under their names). -/
def T2491_NQLinConclg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ v : ℕ → ℝ, (∀ n, s n ≤ v n) → (∀ n, v n ≤ t n) → ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) →
    ∀ k : ℕ, 2 ≤ k → ∀ XL XLK : ℕ → ℕ → ℝ, (∀ m n, 1 ≤ XL m n) → (∀ m n, 1 ≤ XLK m n) →
    (∀ m : ℕ, 1 ≤ m → m ≤ k + 1 →
      PrecL sz μ (U := fun n => TimeIcc s v n)
        (fun n u ω => STXiLg Cm.toFlowFM n (u : ℝ) m ω) (fun n _ _ => XL m n)) →
    (∀ m : ℕ, 1 ≤ m → m ≤ k →
      PrecL sz μ (U := fun n => TimeIcc s v n)
        (fun n u ω => STXiLKg Cm.toFlowFM n (u : ℝ) m ω) (fun n _ _ => XLK m n)) →
    ∀ C : ℝ, (∀ᶠ n in atTop, ((K n + 1 : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C) →
    ∀ ε : ℝ, 0 < ε →
      HighProbAt Cm.Pp sz.size (fun n => {ω | ∀ j ≤ K n,
        Cm.Hpath s v K n j ω ∈ T2491_GoodLinNg Cm n (gridTime s v K n j) k
          (((sz.size n : ℕ) : ℝ) ^ ε) (nqLinPhi1 (fun m => XLK m n) k)
          (nqLinPhi2 (fun m => XL m n) (fun m => XLK m n) (sz.Bctl n (v n)) k (XLK k n))
          (nqLinPhi3 (fun m => XL m n) k)})

/-- **Target 8, the pin `NQLinGoodgL`** (binding; band `NQLinGood`, `NQLin.lean:121`): `STIngRgL d STAny` over a carrier family
with the conclusion `T2491_NQLinConclg` (the shape of `GridGoodNgL`, `Chain/GridGoodGen.lean:474`). -/
def T2491_NQLinGoodgL (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngRgL d STAny law Flow (fun sz z => (mkM sz z).toFlowFM) T0
    (fun sz z s t => T2491_NQLinConclg (mkM sz z) (law sz) s t)

/-- **Target 9, `nqLinGoodgL_of`** (conclusion binding; the hypothesis list is a shape fixed at the 1a-audit; band
`nqLinGood_holds`, `NQLin.lean:591`): rows 1-5 of the family-premise table (U5S-C3): the pin `lem:SEforLn`, the flow facts,
`LoopForm`, `WalkForm` (guarded), `Law`, `LCompat` (unguarded, merged unguarded BA discharges). -/
def T2491_NQLinGoodOf : Prop :=
  ∀ (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (E lam' : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Ψ : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
    STSEforLngL d STAny law Flow mkM Hf T0 → Step2EventsGen_Flow d Flow T0 →
    (∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_LoopForm (mkM sz z) (E sz z)) →
    (∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_WalkForm (mkM sz z) (lam' sz z) (Ψ sz z)) →
    (∀ (sz : Sizes d) (z : ℕ → ℂ), Step2EventsGen_Law (mkM sz z) (law sz) (Hf sz z)) →
    (∀ (sz : Sizes d) (z : ℕ → ℂ), Step34Gen_LCompat (mkM sz z) (Hf sz z)) →
    T2491_NQLinGoodgL d law Flow mkM T0

/-- **Target 13, `STXiBootgL'`** (binding; band `STXiBoot'`, `NQEndFlow.lean:95`): U3s1's `STXiBootgL` with the first summand of
`STbootRHS` at the window start `B_s = sz.Bctl n (s n)` (R2*, DECISIONS §80 (1)). -/
def T2491_XiBootgL' {d : ℕ} {sz : Sizes d} (Cf : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cf n q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m + 1 ≤ n_ →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 n_ ω)
      (fun n q _ => STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p)

/-- **Target 13, `STNQConclgL''`** (binding; band `STNQConcl''`, `NQEndFlow.lean:79`): U3s1's `STNQConclgL'` with `B_s` in the
first summand of `STbootRHS`. -/
def T2491_NQConclgL'' {d : ℕ} {sz : Sizes d} (Cf : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cf n q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    PrecL sz μ (U := fun n => TimeIcc s t n × {σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} ×
        (Fin n_ → Zd d (sz.L n)))
      (fun n q ω => ‖Cf.L n (q.1 : ℝ) q.2.1.1 q.2.2 ω - Cf.K n (q.1 : ℝ) q.2.1.1 q.2.2‖ / (sz.Bctl n (q.1 : ℝ)) ^ n_)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * XLK n_ n (q.1 : ℝ) +
        STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ)) (sz.Bctl n (s n)) n_ p)

/-- **Target 13, `STNQConclPTgL''`** (binding; band `STNQConclPT''`, `NQEndFlow.lean:107`): the per-time form (`PrecPTL` in the
conclusion). -/
def T2491_NQConclPTgL'' {d : ℕ} {sz : Sizes d} (Cf : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cf n q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    PrecPTL sz μ (U := fun n => TimeIcc s t n × {σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} ×
        (Fin n_ → Zd d (sz.L n)))
      (fun n q ω => ‖Cf.L n (q.1 : ℝ) q.2.1.1 q.2.2 ω - Cf.K n (q.1 : ℝ) q.2.1.1 q.2.2‖ / (sz.Bctl n (q.1 : ℝ)) ^ n_)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * XLK n_ n (q.1 : ℝ) +
        STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ)) (sz.Bctl n (s n)) n_ p)

/-- **Target 13, `STOeqNQgL''`** (binding text; band `STOeqNQ''`, `NQEndFlow.lean:124`; no proof here, note 2). -/
def T2491_OeqNQgL'' (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngRgL d STCaseI law Flow mk T0 (fun sz z s t => T2491_NQConclgL'' (mk sz z) (law sz) s t)

/-- **Target 13/14, `STOeqNQPTgL''`** (binding; band `STOeqNQPT''`, `NQEndFlow.lean:155`): the per-time R2* pin, case (i). -/
def T2491_OeqNQPTgL'' (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngRgL d STCaseI law Flow mk T0 (fun sz z s t => T2491_NQConclPTgL'' (mk sz z) (law sz) s t)

/-- **Target 13, `STOeqQtgL'`** (binding text; band `STOeqQt'`, `NQEndFlow.lean:127`; proof U3s3). -/
def T2491_OeqQtgL' (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngRgL d STCaseI law Flow mk T0 (fun sz z s t => T2491_XiBootgL' (mk sz z) (law sz) s t)

/-- **Target 13, `STOeqQtNZgL'`** (binding text; band `STOeqQtNZ'`, `NQEndFlow.lean:130`; proof U3s4). -/
def T2491_OeqQtNZgL' (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngRgL d STCaseII law Flow mk T0 (fun sz z s t => T2491_XiBootgL' (mk sz z) (law sz) s t)

/-- **Target 13, `STIterRgL'`** (binding text; band `STIterR'`, `NQEndFlow.lean:134`; proof U1s2): U3s1's `STIterRgL` with the
hypothesis `T2491_XiBootgL'` in place of `STXiBootgL`. -/
def T2491_IterRgL' (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Aof : ∀ sz : Sizes d, (ℕ → ℝ) → ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ T0 sz z n) →
          R sz s t → STKboundgL (mk sz z) (law sz) → STLKgL (mk sz z) (law sz) s → sz.STConStInd 𝔠d s t →
          STStep1LoopgL (mk sz z) (law sz) s t → STStep2ConclgL (mk sz z) (law sz) s t Cd →
          T2491_XiBootgL' (mk sz z) (law sz) s t →
          ∀ n_ k : ℕ, 2 ≤ n_ → 1 ≤ k →
            (∀ r, 2 ≤ r → r + 1 ≤ n_ → STIterHypgL (mk sz z) (law sz) s t (Aof sz s) r k) →
            (∀ r, 2 ≤ r → r ≤ n_ + 2 → STIterHypgL (mk sz z) (law sz) s t (Aof sz s) r (k - 1)) →
            STIterHypgL (mk sz z) (law sz) s t (Aof sz s) n_ k

/-- **Target 13, `STIterationsgL'`** (binding text; band `STIterations'`, `NQEndFlow.lean:149`). -/
def T2491_IterationsgL' (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  T2491_IterRgL' d STRegIterI law Flow mk T0 (fun sz _ n => STAI sz n)

/-- **Target 13, `STIterationsIIgL'`** (binding text; band `STIterationsII'`, `NQEndFlow.lean:152`). -/
def T2491_IterationsIIgL' (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  T2491_IterRgL' d STCaseII law Flow mk T0 (fun sz s n => STAII sz s n)

/-- **Target 14, `stOeqNQPTgL''_of`** (conclusion binding; `Hyp` is the family-premise bundle of the ticket's table, fixed at
the 1a-audit; band `stOeqNQPT''_holds`, `NQEndFlow.lean:921`). -/
def T2491_OeqNQPTOf
    (Hyp : ∀ (d : ℕ), (∀ sz : Sizes d, Measure sz.SeqΩ) → (∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) →
      (∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) → (∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) → Prop) : Prop :=
  ∀ (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ),
    Hyp d law Flow mkM T0 → T2491_OeqNQPTgL'' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0

/-- **Target 6, the conclusion head of `hQ_nonAltNg`** (binding): the majorant hypothesis `hQ` of the merged
`azumaProxy_subG_goodExitg` (`Chain/AzumaProxyGen.lean:237-238`), verbatim, at a proxy `Q` (the generic `cQVNonAltNg`, text fixed
at the 1a-audit; band `hQ_nonAltN`, `NQGood2.lean:519`). -/
def T2491_HQg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (σ : Fin k → Bool)
    (Γ Λ Φ : ℕ → ℝ) (τ' D' : ℝ) (m : ℕ) (a : Fin k → Zd d (sz.L n)) (j : ℕ) (Q : ℝ≥0) : Prop :=
  ∀ M, GoodSetNg Cm n (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D' M → M.IsHermitian →
    gridStep s v K n * ((k : ℝ) * qvFormNg Cm n (gridTime s v K n (j + 1)) (gridTime s v K n m) σ M a) ≤ (Q : ℝ)

/-- **D1 default, `NQGoodGen_KerNAL`** (text fixed at the 1a-audit): the deterministic `(sum_res_2_NAL)` (EK-6) for the carrier
kernel `Step2Gen_UN C` at the kernel coupling `gK`, index `n`, explicit constant `Ck` (band `hker_of_case1N`'s input
`ekSumDecayNAL_holds`, `NQGood1.lean:310`; BA `BAEKSumDecayNAL`, `BA/EKPins.lean:113`). -/
def T2491_KerNAL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (gK : ℕ → ℝ) (k : ℕ) (Ck : ℝ) (n : ℕ) : Prop :=
  1 < ((sz.W n : ℕ) : ℝ) →
  ∀ ε D : ℝ, 0 < ε → ε < 1 → 1 < D → 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε →
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 - gK n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 →
      (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - t) / (1 - s) →
      ∀ σ : Fin k → Bool, (∃ i, σ i = σ (finRotate k i)) →
      ∀ A : (Fin k → Zd d (sz.L n)) → ℂ, EKFastDecay (gK n) s ((sz.W n : ℕ) : ℝ) ε D A →
        ‖Step2Gen_UN C n σ s t A‖ ≤
          ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) * ((gK n ^ 2 + |1 - s|) / (gK n ^ 2 + |1 - t|)) ^ (k - 1) * ‖A‖ +
            ((sz.W n : ℕ) : ℝ) ^ (-D + Ck)

/-- **D1 default, the family form** (guarded; `∃ Ck` after `(k, κ, ε, 𝔡)` and before `(sz, z)`: U5S-C3, no F1 case). Band
`gK = sz.lam`; BA `gK = BAflowLam0 sz z` (U3-BA (a), from `baEKSumDecayNAL_holds`). -/
def T2491_KerNALFam (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ k : ℕ, 2 ≤ k → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ Ck : ℝ, 0 < Ck ∧
    ∀ (sz : Sizes d) (𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n in atTop, T2491_KerNAL (mk sz z) (gK sz z) k Ck n

/-- **D2 default, `NQEndFlowGen_KLip`** (class (t), C6; text fixed at the 1a-audit): the time modulus of `𝒦^{(k)}` on `[0, t_n]`
(the conclusion of `stKloop_lip`, `NQEndFlowLift.lean:581`, with `STKloop` read as `C.K`). -/
def T2491_KLip {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (t : ℕ → ℝ) (k : ℕ) : Prop :=
  ∀ᶠ n in atTop, ∀ u u' : ℝ, 0 ≤ u → u ≤ t n → 0 ≤ u' → u' ≤ t n →
    ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖C.K n u σ a - C.K n u' σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * k + 2) * |u - u'|

/-- **D2 default, the family form** (guarded; consumers U3s4; BA twin U3-BA). -/
def T2491_KLipFam (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → Flow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, t n ≤ T0 sz z n) → ∀ k : ℕ, 2 ≤ k → T2491_KLip (mk sz z) t k

/-- **D3 default, the spectral premise of the shift layer** (inline in the 1b, no name, no registry line; named here only for
the check): `‖m‖ ≤ 1` under the flow (band `norm_mE`; BA `ba_G_data` + `BAm_norm_le_one`). -/
def T2491_ShiftSpec (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) : Prop :=
  ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ n : ℕ, ‖(mkM sz z).m n‖ ≤ 1

/-- **R1, the only comparison text (UBA-C1, TN-C1, DECISIONS §273 (1))**, as a guarded family premise with the kernel window;
`Aof κ` is fixed before `(sz, z)` (band `gK = sz.lam`, `Aof = 1`; BA `gK = BAflowLam0 sz z`, `Aof κ = (κ+1)/κ`,
`TwistStep2_lam0_sq`, `BAflow_lam0_window`). -/
def T2491_R1Fam (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (Aof : ℝ → ℝ) : Prop :=
  ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
    1 ≤ Aof κ ∧
    (∀ n, 0 ≤ gK sz z n * sz.lam n ∧ gK sz z n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ Aof κ * gK sz z n ^ 2) ∧
    ∀ᶠ n in atTop, 0 < gK sz z n ∧ gK sz z n ≤ 𝔡⁻¹

/-! ### Shapes (not binding): band readings (re-derivations of the band pins) -/

/-- Band reading of target 8 (bridge through `bandFM_STIngR`). -/
example : Prop := ∀ d : ℕ,
  NQLinGood d ↔ T2491_NQLinGoodgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandStep2Mat sz (STflowE z)) (fun _ z n => lemT (z n))

/-- Band reading of targets 13-14. -/
example : Prop := ∀ d : ℕ,
  STOeqNQPT'' d ↔ T2491_OeqNQPTgL'' d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))

/-- Band reading of target 13 (the text U1s2 proves). -/
example : Prop := ∀ d : ℕ,
  STIterations' d ↔ T2491_IterationsgL' d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))

/-- Band discharges of D1, D2, D3 and R1. -/
example : Prop := ∀ d : ℕ,
  T2491_KerNALFam d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun sz _ => sz.lam) ∧
    T2491_KLipFam d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) ∧
    T2491_ShiftSpec d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandStep2Mat sz (STflowE z)) ∧
    T2491_R1Fam d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz _ => sz.lam) (fun _ => 1)

/-! ### Shapes (not binding): BA readings (U3-BA; statement level only) -/

/-- Targets 8 and 14 at the BA carrier family `(seqP ∘ withLam 0, BAFlow, baStep2Mat, BAflowT0)` (as `Step34GenTw:84-90`). -/
example : Prop := ∀ d : ℕ,
  T2491_NQLinGoodgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => BAflowT0 sz z) ∧
    T2491_OeqNQPTgL'' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)

/-- D1, D2, D3 and R1 at the BA family (owners: U3-BA (a) for D1, U3-BA class-(t) twin for D2). -/
example : Prop := ∀ d : ℕ,
  T2491_KerNALFam d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowLam0 sz z) ∧
    T2491_KLipFam d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) ∧
    T2491_ShiftSpec d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) ∧
    T2491_R1Fam d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => BAflowLam0 sz z) (fun κ => (κ + 1) / κ)

end RBM.BA

end

/-! ## Part 3 (G1): band names restated here or read in U3s3, U3s4, U1s2, U4s3 (files not edited) -/

-- `NQGood1`
#check @RBM.Ind.driftTensorN
#check @RBM.Ind.driftTensorN_norm_le_of_goodSet
#check @RBM.Ind.nqGood1C
#check @RBM.Ind.hker_of_case1N
#check @RBM.Ind.qvFormN_le_of_goodSetN
#check @RBM.Ind.loopShiftErrN
#check @RBM.Ind.STXiLM_shiftN_le
#check @RBM.Ind.goodSetN_dec_shiftN
#check @RBM.Ind.norm_loopFine_crudeN
#check @RBM.Ind.eeShiftErrN
#check @RBM.Ind.norm_STeeM_shiftN_le
-- `NQGood2`
#check @RBM.Ind.kappaNonAltN
#check @RBM.Ind.qvBdNonAltN
#check @RBM.Ind.cQVNonAltN
#check @RBM.Ind.nonAlt_hkerN
#check @RBM.Ind.qvFormN_le_of_goodSetN_shiftN
#check @RBM.Ind.hQ_nonAltN
#check @RBM.Ind.subGaussStop_nonAltN
-- `NQBudget`
#check @RBM.Ind.budgetNonAltN
#check @RBM.Ind.nqBudget_merged_inputs
-- `NQLin`
#check @RBM.Gauss.Sizes.GoodLinN
#check @RBM.Gauss.Sizes.nqLinPhi1
#check @RBM.Gauss.Sizes.nqLinPhi2
#check @RBM.Gauss.Sizes.nqLinPhi3
#check @RBM.Gauss.Sizes.NQLinConcl
#check @RBM.Gauss.Sizes.NQLinGood
#check @RBM.Gauss.Sizes.nqLinGood_holds
#check @RBM.Gauss.Sizes.measurableGoodLinN
#check @RBM.Ind.dDriftLinN
#check @RBM.Ind.nqLinExitTauN
#check @RBM.Ind.subGaussStop_linN
#check @RBM.Ind.budgetNonAltLinN
-- `NQEndLin`
#check @RBM.Ind.nqGridEndLinN
-- `NQEndFlow`
#check @RBM.Gauss.Sizes.STNQConcl''
#check @RBM.Gauss.Sizes.STXiBoot'
#check @RBM.Gauss.Sizes.STNQConclPT''
#check @RBM.Gauss.Sizes.STOeqNQ''
#check @RBM.Gauss.Sizes.STOeqQt'
#check @RBM.Gauss.Sizes.STOeqQtNZ'
#check @RBM.Gauss.Sizes.STIterR'
#check @RBM.Gauss.Sizes.STIterations'
#check @RBM.Gauss.Sizes.STIterationsII'
#check @RBM.Gauss.Sizes.STOeqNQPT''
#check @RBM.Ind.nqFlowLam
#check @RBM.Ind.nqFlowPhiC
#check @RBM.Ind.stOeqNQPT''_holds
-- `NQEndFlowLift` (§1 reused under its name; §5 = D2's band discharge; the lift is not converted, note 2)
#check @RBM.Ind.nqFlowSharp
#check @RBM.Gauss.Sizes.stKloop_lip
#check @RBM.Ind.stOeqNQ''_holds
