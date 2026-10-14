/-
Release check for T2509 (dispatcher V4, 2026-10-14; DECISIONS §330 (3), §331, §328 (1) (2); not compiled by the dispatcher).  U U3-BA (b):
Steps 3–4 of `lem:main_ind` at the BA tuple (REQ-1418 `:51-54`): the generic Steps 3–4 producers (`Chain/Step34RGen`, port of band
`Induction/Step3` §1–§4 and `Step4` §1–§2), T2505 D1 at BA (T2507 target 7, Decision (2)), the two bootstraps at BA, and `STStep3RgL` /
`STStep4RgL` at the BA tuple per regime (`BA/Step34BA`).  BA tuple `(fun sz => Sizes.seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`;
`gK = BAflowLam0`; `Aof κ = (κ+1)/κ`.  Part 1: merged names (`main` 22467000).  Part 2: pins `T2509_*` (binding), then shapes (not binding);
statements only, merged modules only.  Run: lake env lean docs/tickets/checks/T2509-check.lean
-/
import RBM3D.Chain.Step34Gen
import RBM3D.Chain.Step34GenTw
import RBM3D.Chain.NQEndFlowGen
import RBM3D.Chain.QtBootGen
import RBM3D.Chain.QtXiRoundLiftGen
import RBM3D.Chain.QtNonzeroGen
import RBM3D.Chain.QtNonzeroBootGen
import RBM3D.Chain.IterationsGen2
import RBM3D.Chain.Step2EventsGenTw
import RBM3D.Chain.DecayGenTw
import RBM3D.Induction.Step3
import RBM3D.Induction.Step4
import RBM3D.Induction.ScaleFacts3
import RBM3D.Induction.MainIndRegimes
import RBM3D.BA.EKGenBA
import RBM3D.BA.KLipBA
import RBM3D.BA.SEforLnBA
import RBM3D.BA.ZeroModeBA
import RBM3D.BA.GridDriftBA
import RBM3D.BA.GridRepTailBA
import RBM3D.BA.Step5KerBA
import RBM3D.BA.B45BA
import RBM3D.BA.KDecayBA
import RBM3D.BA.NetLiftBA
import RBM3D.BA.Step2BA
import RBM3D.BA.Ward
import RBM3D.BA.FlowPins
import RBM3D.BA.TwistPins

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- U3s1 = T2457: the Steps 3–4 pins, their conclusions (TLF-C5), the bridges, the window
#check @RBM.BA.STStep3RgL -- Chain/Step34Gen.lean:347
#check @RBM.BA.STStep4RgL -- Chain/Step34Gen.lean:359
#check @RBM.BA.STIngRgL -- Chain/Step34Gen.lean:373
#check @RBM.BA.STLmaxUgL -- Chain/Step34Gen.lean:58
#check @RBM.BA.STLKUgL -- Chain/Step34Gen.lean:65
#check @RBM.BA.bandFM_STStep3R -- Chain/Step34Gen.lean:433
#check @RBM.BA.twSteps -- BA/TwistPins.lean:133
-- U3s2 / U1s2 = T2491 / T2497: the R2* texts, the bundle of `lem:iterations` and its producers
#check @RBM.BA.STXiBootgL' -- Chain/NQEndFlowGen.lean:57
#check @RBM.BA.STOeqQtgL' -- Chain/NQEndFlowGen.lean:110
#check @RBM.BA.STOeqQtNZgL' -- Chain/NQEndFlowGen.lean:116
#check @RBM.BA.STIterationsgL' -- Chain/NQEndFlowGen.lean:140
#check @RBM.BA.STIterationsIIgL' -- Chain/NQEndFlowGen.lean:146
#check @RBM.BA.IterationsGen2_Fam -- Chain/IterationsGen2.lean:373
#check @RBM.BA.stIterationsgL'_of -- Chain/IterationsGen2.lean:389
#check @RBM.BA.stIterationsIIgL'_of -- Chain/IterationsGen2.lean:409
#check @RBM.BA.IterationsGen2_famBand -- Chain/IterationsGen2.lean:432
#check @RBM.BA.IterationsGen_eta_ratio -- Chain/IterationsGen.lean:326
#check @RBM.BA.iterationsA_scale_Ig -- Chain/IterationsGen.lean:505
#check @RBM.BA.iterationsA_scale_IIg -- Chain/IterationsGen.lean:514
-- U3s3 / U3s4 = T2498 / T2505: the round, the bootstraps, D1 (case (ii))
#check @RBM.BA.STXiRoundgL' -- Chain/QtBootGen.lean:55
#check @RBM.BA.stXiBootgL'_of_round -- Chain/QtBootGen.lean:346
#check @RBM.BA.stOeqQtgL'_of -- Chain/QtXiRoundLiftGen.lean:466
#check @RBM.BA.QtXiRoundLiftGenCheck.stOeqQtgL'_band -- Chain/QtXiRoundLiftGen.lean:590
#check @RBM.BA.QtNZGen_KerNZFam -- Chain/QtNonzeroGen.lean:62
#check @RBM.BA.stOeqQtNZgL'_of -- Chain/QtNonzeroBootGen.lean:507
#check @RBM.BA.QtNonzeroBootGenCheck.stOeqQtNZgL'_band -- Chain/QtNonzeroBootGen.lean:623
-- the band sources of file 1 (not edited; `step3_skeleton` `:153`, `step3_assemble` `:334`, `step4_skeleton` `Step4:60`, `step4_of_ing` `:156`, `step4R_mono` `:172` are private)
#check @RBM.Gauss.Sizes.STStep3R -- Induction/Step34Pins.lean:250
#check @RBM.Gauss.Sizes.STCaseI -- Induction/Step34Pins.lean:237
#check @RBM.Gauss.Sizes.STCaseII -- Induction/Step34Pins.lean:241
#check @RBM.Gauss.Sizes.STReg5I -- Induction/Step5Pins.lean:44
#check @RBM.Gauss.Sizes.STReg5III -- Induction/Step5Pins.lean:58
#check @RBM.Ind.stStep3RegIII_holds -- Induction/Step3.lean:377
#check @RBM.Ind.stStep3RegI_holds -- Induction/Step3.lean:408
#check @RBM.Ind.stStep3II_holds -- Induction/Step3.lean:432
#check @RBM.Ind.stStep4I_holds -- Induction/Step4.lean:189
#check @RBM.Ind.stStep4II_holds -- Induction/Step4.lean:193
#check @RBM.Gauss.Sizes.ST_mainInd_of_pins' -- Induction/Step4.lean:209
#check @RBM.Gauss.Sizes.ST_mainIndR_of_steps -- Induction/MainIndRegimes.lean:165
#check @RBM.Gauss.Sizes.st_caseI_of_reg5III -- Induction/MainIndRegimes.lean:125
#check @RBM.Gauss.Sizes.st_caseI_of_reg5I -- Induction/MainIndRegimes.lean:137
#check @RBM.Gauss.Sizes.st_hscale_I' -- Induction/ScaleFacts3.lean:303
#check @RBM.Gauss.Sizes.st_hscale_II' -- Induction/ScaleFacts3.lean:310
#check @RBM.Gauss.Sizes.st_hBA_I -- Induction/ScaleFacts3.lean:323
#check @RBM.Gauss.Sizes.st_hBA_II -- Induction/ScaleFacts3.lean:380
-- BA discharges of the family slots (U3-BA (a) = T2507, U2-BA = T2486, T5-BA = T2492, T2500, U4-BA = T2501, U2 = KDecayBA)
#check @RBM.BA.baEKSumDecayNonzeroA_holds -- BA/EKGenBA.lean:262
#check @RBM.BA.baNQGoodGen_kerNAL -- BA/EKGenBA.lean:456
#check @RBM.BA.baQProxyG_kerEK4 -- BA/EKGenBA.lean:471
#check @RBM.BA.baKloop_lip -- BA/KLipBA.lean:208
#check @RBM.BA.baSEforLn_holds -- BA/SEforLnBA.lean:221
#check @RBM.BA.baStep34_LCompat -- BA/SEforLnBA.lean:122
#check @RBM.BA.baStep2Mat_loopForm -- BA/SEforLnBA.lean:135
#check @RBM.BA.baStep5CasesGen_flowFacts -- BA/SEforLnBA.lean:152
#check @RBM.BA.baEtermDecaygL -- BA/SEforLnBA.lean:271
#check @RBM.BA.baIterationsGen2_fam -- BA/ZeroModeBA.lean:120
#check @RBM.BA.baSTIterationsgL'_holds -- BA/ZeroModeBA.lean:132
#check @RBM.BA.baSTIterationsIIgL'_holds -- BA/ZeroModeBA.lean:140
#check @RBM.BA.baStep2Mat_walkForm -- BA/GridDriftBA.lean:71
#check @RBM.BA.baStep2Mat_S -- BA/GridDriftBA.lean:86
#check @RBM.BA.baStep2Mat_S_rowSum -- BA/GridDriftBA.lean:90
#check @RBM.BA.baHierDrift_classes -- BA/GridDriftBA.lean:631
#check @RBM.BA.gridRepTailGen_ker_BA -- BA/GridRepTailBA.lean:60
#check @RBM.BA.baStep5KerGen_thDecay -- BA/Step5KerBA.lean:132
#check @RBM.BA.baLemDecCalELipG_flowMod -- BA/Step5KerBA.lean:390
#check @RBM.BA.baB45Gen_facts -- BA/B45BA.lean:205
#check @RBM.BA.baKcalDecay_holds -- BA/KDecayBA.lean:692
#check @RBM.BA.baFlow_premises -- BA/NetLiftBA.lean:65
#check @RBM.BA.Step2EventsGenTw_baFlow -- Chain/Step2EventsGenTw.lean:53
#check @RBM.BA.DecayGenTw_baWardPair -- Chain/DecayGenTw.lean:44
#check @RBM.BA.Step2Kern_UN_BA -- Chain/Step2Kern.lean:124
#check @RBM.BA.baStep2Mat_toFlowFM -- BA/Step2BA.lean:75
#check @RBM.BA.BAflow_real -- BA/GreenSchur.lean:59
#check @RBM.BA.BAflow_lam0_window -- BA/GreenSchur.lean:72
#check @RBM.BA.TwistStep2_lam0_sq -- BA/TwistStep2.lean:740
#check @RBM.BA.BAm_norm_le_one -- BA/Ward.lean:136
#check @RBM.BA.BAflowT0 -- BA/FlowPins.lean:380
#check @RBM.BA.BAflowLam0 -- BA/FlowPins.lean:386
#check @RBM.BA.BAFlow -- BA/FlowPins.lean:389
#check @RBM.BA.baFMz -- BA/FlowPins.lean:393
-- `d = 3` data (regimes (i), (ii) are empty at `sz0`)
#check @RBM.Gauss.SizesInst.sz0 -- Defs/Sizes.lean:260
#check @RBM.BA.FlowPinsInst.zSeq -- BA/FlowPins.lean:1181
#check @RBM.BA.FlowPinsInst.flow_sz0 -- BA/FlowPins.lean:1214
#check @RBM.BA.FlowPinsInst.t0_sz0 -- BA/FlowPins.lean:1227
#check @RBM.BA.TwistStep2_szII -- BA/TwistStep2.lean:1341
#check @RBM.BA.TwistStep2_flowII -- BA/TwistStep2.lean:1353
#check @RBM.BA.TwistStep2_no_caseII_sz0 -- BA/TwistStep2.lean:1547

/-! ## Part 2: the target statements (prefix `T2509_`), then shapes (not binding) -/

open MeasureTheory Filter

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ### File 1 (`Chain/Step34RGen`, generic; the theorems state `∀ d law Flow mkM Hf Es T0, T2509_X d law Flow mkM Hf Es T0`) -/

/-- **Target 1, `stStep3RegIIIgL_of`** (binding; band `stStep3RegIII_holds`, `Induction/Step3.lean:377`; `𝔠d = 1/100`). -/
def T2509_Step3RegIIIOf (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (Es T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  IterationsGen2_Fam d law Flow mkM Hf Es T0 → STStep3RgL d STReg5III law Flow (fun sz z => (mkM sz z).toFlowFM) T0

/-- **Target 2, `stStep3RegIgL_of`** (binding; band `stStep3RegI_holds`, `:408`; `𝔠d = min` of the two pins' constants). -/
def T2509_Step3RegIOf (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (Es T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  IterationsGen2_Fam d law Flow mkM Hf Es T0 → STOeqQtgL' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 →
    STIterationsgL' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 →
      STStep3RgL d STReg5I law Flow (fun sz z => (mkM sz z).toFlowFM) T0

/-- **Target 3, `stStep3IIgL_of`** (binding; band `stStep3II_holds`, `:432`). -/
def T2509_Step3IIOf (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (Es T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  IterationsGen2_Fam d law Flow mkM Hf Es T0 → STOeqQtNZgL' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 →
    STIterationsIIgL' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 →
      STStep3RgL d STCaseII law Flow (fun sz z => (mkM sz z).toFlowFM) T0

/-- **Target 4, `stStep4RgL_of_ing`** (binding; band private `step4_of_ing`, `Induction/Step4.lean:156`; the target also quantifies `R`). -/
def T2509_Step4ROfIng (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (Es T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  IterationsGen2_Fam d law Flow mkM Hf Es T0 →
    STIngRgL d R law Flow (fun sz z => (mkM sz z).toFlowFM) T0 (fun sz z s t => STXiBootgL' (mkM sz z).toFlowFM (law sz) s t) →
      STStep4RgL d R law Flow (fun sz z => (mkM sz z).toFlowFM) T0

/-- **Target 5, `stStep34RgL_mono`** (binding; band private `step4R_mono`, `:172`, and its Step 3 twin). -/
def T2509_Step34Mono (d : ℕ) (R R' : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  (∀ (sz : Sizes d) (s t : ℕ → ℝ), R' sz s t → R sz s t) →
    (STStep3RgL d R law Flow mk T0 → STStep3RgL d R' law Flow mk T0) ∧ (STStep4RgL d R law Flow mk T0 → STStep4RgL d R' law Flow mk T0)

/-! ### File 2 (`BA/Step34BA`; the theorems state `(d : ℕ) : T2509_X d`) -/

/-- **Target 6, `baQtNZGen_kerNZ`** (binding; = T2507 target 7 `T2507_KerNZBA`, `T2507-check.lean:201`, at the merged class). -/
def T2509_KerNZBA (d : ℕ) : Prop :=
  QtNZGen_KerNZFam d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowLam0 sz z) (fun κ => (κ + 1) / κ)

/-- **Target 7 (a), `baOeqQtgL'_holds`** (binding): the case-(i) bootstrap at the BA tuple. -/
def T2509_OeqQtBA (d : ℕ) : Prop :=
  STOeqQtgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)

/-- **Target 7 (b), `baOeqQtNZgL'_holds`** (binding): the case-(ii) bootstrap at the BA tuple. -/
def T2509_OeqQtNZBA (d : ℕ) : Prop :=
  STOeqQtNZgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)

def T2509_Step3BA (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  STStep3RgL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)

def T2509_Step4BA (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  STStep4RgL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)

/-- **Target 8**, `baStep3RegIII_holds` / `baStep3RegI_holds` / `baStep3II_holds` (binding). -/
def T2509_Step3RegIIIBA (d : ℕ) : Prop := T2509_Step3BA d STReg5III
def T2509_Step3RegIBA (d : ℕ) : Prop := T2509_Step3BA d STReg5I
def T2509_Step3IIBA (d : ℕ) : Prop := T2509_Step3BA d STCaseII

/-- **Target 9**, `baStep4I_holds` / `baStep4II_holds` / `baStep4RegIII_holds` / `baStep4RegI_holds` (binding). -/
def T2509_Step4IBA (d : ℕ) : Prop := T2509_Step4BA d STCaseI
def T2509_Step4IIBA (d : ℕ) : Prop := T2509_Step4BA d STCaseII
def T2509_Step4RegIIIBA (d : ℕ) : Prop := T2509_Step4BA d STReg5III
def T2509_Step4RegIBA (d : ℕ) : Prop := T2509_Step4BA d STReg5I

/-! ### Shapes (not binding) -/

/-- Dispatcher note (3): V2a's per-regime reading with `R34 = R` for (iii), (i) (band `ST_mainInd_of_pins'`, `Induction/Step4.lean:209-228`)
and `STCaseII` for (ii), (iv) (`st_caseII_of_reg5II/IV`); `T2503-check.lean:282, 284` read `STCaseI` (Step 3 there = the superseded `STStep3I`). -/
def T2509_shape_V2aRead (d : ℕ) : Prop :=
  (T2509_Step3RegIIIBA d ∧ T2509_Step4RegIIIBA d) ∧ (T2509_Step3RegIBA d ∧ T2509_Step4RegIBA d) ∧
    (T2509_Step3IIBA d ∧ T2509_Step4IIBA d)

end RBM.BA

end
