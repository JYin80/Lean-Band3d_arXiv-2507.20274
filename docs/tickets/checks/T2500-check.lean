/-
Release check for T2500 (dispatcher V4, 2026-10-14; DECISIONS §311).  U U1-BA = the BA side of U1 (U1s1 = T2463,
U1s2 = T2497) in one new BA leaf `BA/ZeroModeBA` (proposed name).  Targets: (1) T2463's conditional target 9 `stNewPQgL_wardCls`
(moved to U1-BA, DECISIONS §274 (1)); (2) its BA reading at the class of BA carriers along a BA flow; (3) REQ-1418's
`baZeroModeSet_UN` (`BAUN` form) and `baZeroModeSet_ThetaN`; (4) the kernel semigroup class at BA (T2497 decision (10));
(5) U1s2b's family bundle `IterationsGen2_Fam` at the BA tuple; (6) the R2* pins `STIterationsgL'`, `STIterationsIIgL'` at the BA
tuple `(seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)` (as T2499).  Every input is merged: U2-BA (T2486: `baZeroModeGen_wardCls`,
`baZeroModeGen_kerSums`, `baStep2Mat_loopForm`, `baStep34_LCompat`), P1b-2 (T2471: `gridRepTailGen_ker_BA`), U1s2b (T2497:
`stIterationsgL'_of`, `stIterationsIIgL'_of`).  Nothing from U3s3 (T2498) or U3s4.
Coupling (UBA-C1; R1 = DECISIONS §273 (1)): no crossing, R1 is not read.  TN-C4: no `STGridRepNgL`.  UP-C4: no drift is read.
Part 1: merged names (file:line on `main` 086d9091).  Part 2: pins (prefix `T2500_`; binding: `T2500_NewPQWardCls`,
`T2500_NewPQBA`, `T2500_ZeroModeSetUNBA`, `T2500_ZeroModeSetThetaNBA`, `T2500_USemigroupBA`, `T2500_IterFamBA`,
`T2500_IterationsBA`, `T2500_IterationsIIBA`), then shapes (not binding).  Part 3: the registry names (owner text only).
Merged names only; statements only.
Run: lake env lean docs/tickets/checks/T2500-check.lean
-/
import RBM3D.Chain.ZeroModeGen
import RBM3D.Chain.Step34Gen
import RBM3D.Chain.IterationsGen2
import RBM3D.Chain.QGridGen
import RBM3D.Chain.Step2Kern
import RBM3D.Chain.Step2EventsGenTw
import RBM3D.Chain.GridRepTailGen
import RBM3D.BA.SEforLnBA
import RBM3D.BA.B45BA
import RBM3D.BA.GridRepTailBA
import RBM3D.BA.TwistGrid
import RBM3D.BA.TwistStep2
import RBM3D.BA.Step1Fam
import RBM3D.BA.GreenSchur
import RBM3D.BA.Ward
import RBM3D.BA.EMn2BA
import RBM3D.BA.GridGoodBA
import RBM3D.Induction.QopNorm
import RBM3D.Induction.QopAlgebra
import RBM3D.Induction.NQEndFlow
import RBM3D.Induction.Step34Pins

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- U3s1 = T2457 (merged 6e7d2602, `Chain/Step34Gen.lean`): `lem: newPQ` over a class `:823`, its band class `:838`
#check @RBM.BA.STNewPQgL
#check @RBM.BA.stNewPQgL_band
-- U1s1 = T2463 (merged 01b4c521, `Chain/ZeroModeGen.lean`): `KerSums` `:54`, commutation `:161`, `:170`, `:179`, the grid
-- Duhamel with `Q^{(A)}` inside `:197`, the Ward family `:226`, model-free `lem: newPQ` `:249`, the Ward class `:289`, its band
-- discharge `:299`, the `(𝓛 - 𝒦)` expansion `:329`
#check @RBM.BA.ZeroModeGen_KerSums
#check @RBM.BA.zeroModeSet_UNg
#check @RBM.BA.zeroModeOp_ThetaNg
#check @RBM.BA.zeroModeSet_ThetaNg
#check @RBM.BA.zeroModeCalc_duhamel_inside_atg
#check @RBM.BA.ZeroModeGen_WardFam
#check @RBM.BA.zeroModeGen_newPQ
#check @RBM.BA.ZeroModeGen_WardCls
#check @RBM.BA.zeroModeGen_wardCls_band
#check @RBM.BA.zeroModeCalc_LK_expansiong
-- the tensor operators (`Kernel/Evolution.lean:194, 199`) and the carrier kernels (`Chain/Step2Gen.lean:192, 197, 202`)
#check @RBM.zeroModeOp
#check @RBM.zeroModeSet
#check @RBM.BA.Step2Gen_uKer
#check @RBM.BA.Step2Gen_ThetaN
#check @RBM.BA.Step2Gen_UN
-- the semigroup class (T4s1, `Chain/GridDuhamelGen.lean:51`, band `:58`); P1b's kernel class (`Chain/GridRepTailGen.lean:54`)
-- and its BA discharge (P1b-2 = T2471, merged ae791953, `BA/GridRepTailBA.lean:60`; first conjunct = the semigroup class)
#check @RBM.BA.Step2Gen_USemigroup
#check @RBM.BA.step2Gen_USemigroup_band
#check @RBM.BA.GridRepTailGen_Ker
#check @RBM.BA.gridRepTailGen_ker_BA
-- stage E's kernels and their bridges (E-C1): `BA/EKPins.lean:49, 53`, `Chain/Step2Kern.lean:112, 124`; TL's semigroup law
-- (`BA/TwistGrid.lean:184, 188, 199`)
#check @RBM.BA.BAuKer
#check @RBM.BA.BAUN
#check @RBM.BA.Step2Kern_uKer_BA
#check @RBM.BA.Step2Kern_UN_BA
#check @RBM.BA.BAuKer_self
#check @RBM.BA.BAuKer_comp
#check @RBM.BA.BAuKerSemigroup_holds
-- U2-BA = T2486 (merged 7be99aae, 5fbefff2): the Ward class at BA `BA/SEforLnBA.lean:66`, the carrier facts `:122`, `:135`, the
-- flow facts `:152`, `KerSums` at BA `BA/B45BA.lean:110`; their instances at the data (`SEforLnBA:314`, `B45BA:314`)
#check @RBM.BA.baZeroModeGen_wardCls
#check @RBM.BA.baStep34_LCompat
#check @RBM.BA.baStep2Mat_loopForm
#check @RBM.BA.baStep5CasesGen_flowFacts
#check @RBM.BA.baZeroModeGen_kerSums
#check @RBM.BA.SEforLnBAInst.inst_wardCls
#check @RBM.BA.B45BAInst.inst_kerSums
-- the other BA family discharges: `Chain/Step2EventsGen.lean:68`, `Chain/Step2EventsGenTw.lean:53`, `BA/EMn2BA.lean:68, 125`,
-- `BA/Ward.lean:136`, `BA/GreenSchur.lean:59`, `BA/MFixedPoint.lean:432`, `Gauss/FineModel.lean:171`, `Gauss/BlockAnderson.lean:83`
#check @RBM.BA.Step2EventsGen_Flow
#check @RBM.BA.Step2EventsGenTw_baFlow
#check @RBM.BA.EMn2BA_seqHflowBA_herm
#check @RBM.BA.EMn2BA_mF_data
#check @RBM.BA.BAm_norm_le_one
#check @RBM.BA.BAflow_real
#check @RBM.BA.BAReal
#check @RBM.Gauss.Sizes.isProbabilityMeasure_seqP
#check @RBM.Gauss.Sizes.seqHflowBA
-- U1s2b = T2497 (merged 0bf9dc0c, `Chain/IterationsGen2.lean`): the bundle `:373`, target 14 `:389`, `:409`, the band bundle
-- `:432`, the band instances `:468`, `:490`
#check @RBM.BA.IterationsGen2_Fam
#check @RBM.BA.stIterationsgL'_of
#check @RBM.BA.stIterationsIIgL'_of
#check @RBM.BA.IterationsGen2_famBand
#check @RBM.BA.IterationsGen2Inst.inst_iterationsgL'
#check @RBM.BA.IterationsGen2Inst.inst_iterationsIIgL'
-- U3s2c = T2491c (merged c72bc745, `Chain/NQEndFlowGen.lean`): the R2* texts `:57`, `:123`, `:140`, `:146`
#check @RBM.BA.STXiBootgL'
#check @RBM.BA.STIterRgL'
#check @RBM.BA.STIterationsgL'
#check @RBM.BA.STIterationsIIgL'
-- U1s2a = T2497 (merged 2ee4af8a, `Chain/QGridGen.lean:75, 794`): target 7 (the BA reading of its premise is target 4 here)
#check @RBM.BA.aFrozQNg
#check @RBM.BA.stoppedDuhamelQNg
-- the BA tuple and carrier (`BA/FlowPins.lean:252, 322, 380-393`, `BA/Step2BA.lean:54`), the law (`Gauss/FineModel.lean:169`,
-- `Defs/Sizes.lean:182`), the regimes (`Induction/Step34Pins.lean:79, 82, 237, 241, 493`)
#check @RBM.BA.BAmF
#check @RBM.BA.baFM
#check @RBM.BA.BAFlow
#check @RBM.BA.baFMz
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs
#check @RBM.BA.baStep2Mat
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.withLam
#check @RBM.Gauss.Sizes.STAI
#check @RBM.Gauss.Sizes.STAII
#check @RBM.Gauss.Sizes.STCaseI
#check @RBM.Gauss.Sizes.STCaseII
#check @RBM.Gauss.Sizes.STRegIterI
-- instance data: `sz0` (`Defs/Sizes.lean:260, 267`), `zSeq`, `flow_sz0`, `t0_sz0` (`BA/FlowPins.lean:1181, 1214, 1227`),
-- `t0_sz0_le` (`BA/Step1Fam.lean:753`), `conStInd_const` (`Induction/Step34Pins.lean:825`); TL's case-(ii) datum and its flow
-- (`BA/TwistStep2.lean:1341, 1350, 1353`), the horizon bound `:731`, and the reason `sz0` has no case-(ii) window `:1547`
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.SizesInst.sz0_values
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.t0_sz0
#check @RBM.BA.Step1FamInst.t0_sz0_le
#check @RBM.Gauss.Step34Inst.conStInd_const
#check @RBM.BA.TwistStep2_szII
#check @RBM.BA.TwistStep2_zII
#check @RBM.BA.TwistStep2_flowII
#check @RBM.BA.TwistStep2_T0_ge
#check @RBM.BA.TwistStep2_no_caseII_sz0
-- not here, for the record: the model-free `STQopNorm`, `STMollifierEx` hold for every `g` (`Induction/QopNorm.lean:261`,
-- `Induction/QopAlgebra.lean:573`), so their BA readings (REQ-1418 `:35`) need nothing; the BA drift envelope (UP-C4,
-- `BA/GridGoodBA.lean:197`) is not read; the Ward identity text of U4s1 (`Chain/Step5CasesGen.lean:187`) is U4-BA (b)'s bridge
#check @RBM.Gauss.Sizes.STQopNorm
#check @RBM.Gauss.Sizes.STMollifierEx
#check @RBM.Gauss.Sizes.stQopNorm_holds
#check @RBM.Gauss.Sizes.stMollifierEx_holds
#check @RBM.BA.baGridDrift_envelope
#check @RBM.BA.Step5CasesGen_WardIdent

/-! ## Part 2: pins (binding as marked) and shapes (not binding) -/

open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Target 1** (binding; T2463 target 9, `docs/tickets/T2463.md:22`, moved to U1-BA, DECISIONS §274 (1)): `lem: newPQ`
(`STNewPQgL`, `Chain/Step34Gen.lean:823`) over U1s1's carrier class `ZeroModeGen_WardCls` (`Chain/ZeroModeGen.lean:289`), every `d`;
from `zeroModeGen_newPQ` (`:249`) at the class witnesses. -/
def T2500_NewPQWardCls : Prop := ∀ d : ℕ, STNewPQgL d (fun sz C => ZeroModeGen_WardCls sz C)

/-- **Target 2** (binding; REQ-1418 `:35`, `BANewPQCls` written inline): `lem: newPQ` at the class of BA carriers along a BA flow;
from target 1 and U2-BA's `baZeroModeGen_wardCls` (`BA/SEforLnBA.lean:66`, UN-C3's one BA Ward proof). -/
def T2500_NewPQBA : Prop :=
  ∀ d : ℕ, STNewPQgL d (fun sz C => ∃ (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ ∧ BAFlow sz κ ε 𝔠 𝔡 z ∧ C = baFMz sz z)

/-- **Target 3, `UN`** (binding; REQ-1418 `:35` `baZeroModeSet_UN` "with `BAUN` for `UN`"; band `zeroModeSet_UN`, ZMC:332):
`Q^{(A)}` commutes with stage E's `BAUN` at `(g₀, E, m)` of the flow, every `s, t`; from `zeroModeSet_UNg` (`ZeroModeGen:161`) at
`baZeroModeGen_kerSums` and `Step2Kern_UN_BA` (`Chain/Step2Kern.lean:124`). -/
def T2500_ZeroModeSetUNBA : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ (n k : ℕ) (σ : Fin k → Bool) (s t : ℝ) (A : Finset (Fin k)) (T : (Fin k → Zd d (sz.L n)) → ℂ),
      zeroModeSet d (sz.L n) A
          (BAUN d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) σ s t T) =
        BAUN d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) σ s t
          (zeroModeSet d (sz.L n) A T)

/-- **Target 3, `ThetaN`** (binding; band `zeroModeSet_ThetaN`, ZMC:395): `Q^{(A)}` commutes with the carrier `Step2Gen_ThetaN` of
`baFMz` (there is no BA `ThetaN` twin, `Chain/Step2Kern.lean:122-123`); from `zeroModeSet_ThetaNg` (`ZeroModeGen:179`). -/
def T2500_ZeroModeSetThetaNBA : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ (n k : ℕ) (σ : Fin k → Bool) (t : ℝ) (A : Finset (Fin k)) (T : (Fin k → Zd d (sz.L n)) → ℂ),
      zeroModeSet d (sz.L n) A (Step2Gen_ThetaN (baFMz sz z) n σ t T) =
        Step2Gen_ThetaN (baFMz sz z) n σ t (zeroModeSet d (sz.L n) A T)

/-- **Target 4** (binding; T2497 decision (10) and family row 10, `docs/tickets/T2497.md:56, 97`): the semigroup class of the BA
carrier at every index along a BA flow; the first conjunct of `gridRepTailGen_ker_BA` (`BA/GridRepTailBA.lean:60`) at `BAflow_real`. -/
def T2500_USemigroupBA : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ n : ℕ, Step2Gen_USemigroup (baFMz sz z) n

/-- **Target 5** (binding; the BA reading of T2497 targets 12-14, `docs/tickets/checks/T2497-check.lean:407-415`): U1s2b's family
bundle (`Chain/IterationsGen2.lean:373`) at `(seqP ∘ withLam 0, BAFlow, baStep2Mat (BAflowLam0) (BAflowEs), seqHflowBA (BAflowLam0),
BAflowEs, BAflowT0)`; rows 1-6 of the ticket's family table. -/
def T2500_IterFamBA : Prop := ∀ d : ℕ,
  IterationsGen2_Fam d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => sz.seqHflowBA (BAflowLam0 sz z))
    (fun sz z => BAflowEs sz z) (fun sz z => BAflowT0 sz z)

/-- **Target 6, case (i)** (binding): the R2* pin `STIterationsgL'` (`Chain/NQEndFlowGen.lean:140`) at the BA tuple. -/
def T2500_IterationsBA : Prop := ∀ d : ℕ,
  STIterationsgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
    (fun sz z => BAflowT0 sz z)

/-- **Target 6, case (ii)** (binding): `STIterationsIIgL'` (`Chain/NQEndFlowGen.lean:146`) at the BA tuple. -/
def T2500_IterationsIIBA : Prop := ∀ d : ℕ,
  STIterationsIIgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
    (fun sz z => BAflowT0 sz z)

/-! ### Shapes (not binding) -/

/-- Target 2 from target 1: the class inclusion through U2-BA's Ward class along the flow. -/
example : Prop := T2500_NewPQWardCls →
  (∀ (d : ℕ) (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → ZeroModeGen_WardCls sz (baFMz sz z)) →
    T2500_NewPQBA

/-- Target 3 at the carrier kernel (the merged `zeroModeSet_UNg` at `baFMz`); `Step2Kern_UN_BA` turns it into the `BAUN` pin. -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ (n k : ℕ) (σ : Fin k → Bool) (s t : ℝ) (A : Finset (Fin k)) (T : (Fin k → Zd d (sz.L n)) → ℂ),
      zeroModeSet d (sz.L n) A (Step2Gen_UN (baFMz sz z) n σ s t T) =
        Step2Gen_UN (baFMz sz z) n σ s t (zeroModeSet d (sz.L n) A T)

/-- Target 4's source: P1b's kernel class at the BA carrier along the flow (its first conjunct is the semigroup class). -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ n : ℕ, GridRepTailGen_Ker (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).toFlowFM n

/-- Target 6 as `stIterationsgL'_of`, `stIterationsIIgL'_of` conclude it from target 5 (carrier `(baStep2Mat …).toFlowFM`, which is
`baFMz sz z` after unfolding `baStep2Mat`, `baFMz`). -/
example : Prop := T2500_IterFamBA → ∀ d : ℕ,
  STIterationsgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).toFlowFM) (fun sz z => BAflowT0 sz z) ∧
    STIterationsIIgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).toFlowFM) (fun sz z => BAflowT0 sz z)

/-- Target 7 (a)-(b): the carrier classes at the data `(sz0, zSeq, flow_sz0)` (merged `inst_wardCls`, `inst_kerSums`; target 4). -/
example : Prop := ZeroModeGen_WardCls SizesInst.sz0 (baFMz SizesInst.sz0 FlowPinsInst.zSeq) ∧
  ∀ n : ℕ, ZeroModeGen_KerSums (baFMz SizesInst.sz0 FlowPinsInst.zSeq) n ∧
    Step2Gen_USemigroup (baFMz SizesInst.sz0 FlowPinsInst.zSeq) n

/-- Target 7 (c): the two carrier premises of U1s1 target 3 (`zeroModeCalc_duhamel_inside_atg`) and U1s2 target 7
(`stoppedDuhamelQNg`) at `baStep2Mat sz0 …`, index `0`. -/
example : Prop :=
  Step2Gen_USemigroup (baStep2Mat SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq)
      (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq)).toFlowFM 0 ∧
    ZeroModeGen_KerSums (baStep2Mat SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq)
      (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq)).toFlowFM 0

/-- Target 7 (d), why case (i) needs a new datum: at `sz0` no window satisfies `STRegIterI` (`n = 0`: `1 - s₀ ≤ lam₀² = 1/4096`
against `t₀ ≤ T0_0 ≤ 25/36`, `t0_sz0_le`); the pattern of `TwistStep2_no_caseII_sz0`.  The 1a confirms it with a script. -/
example : Prop := ¬ ∃ s t : ℕ → ℝ, (∀ n, s n < t n) ∧ (∀ n, t n ≤ BAflowT0 SizesInst.sz0 FlowPinsInst.zSeq n) ∧
  STRegIterI SizesInst.sz0 s t

/-- Target 7 (d), case (ii) at TL's datum: the flow, the window `s ≡ 0 < t ≡ 1/2000 ≤ T₀`, the regime (`1 ≤ 25/16`). -/
example : Prop := BAFlow TwistStep2_szII (3 / 5000) (1 / 2) (1 / 9) (1 / 10) TwistStep2_zII ∧
  (∀ n, (1 / 2000 : ℝ) ≤ BAflowT0 TwistStep2_szII TwistStep2_zII n) ∧
    STCaseII TwistStep2_szII (fun _ => (0 : ℝ)) (fun _ => (1 / 2000 : ℝ))

/-- UBA-C1 (DECISIONS §273 (1)): the only comparison text; not used in this row (no crossing, ticket table). -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (gK : ℕ → ℝ) (A : ℝ),
  ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2

end RBM.BA

/-! ## Part 3: registry names (`RBM3D/Test/Axioms.lean`, located through the name): the owner text of `STIterR'` ("BA: U1-BA") changes;
`STXiBootgL'` stays (owner U3-BA, DECISIONS §310 (1)); the band results named in the owner text are unchanged -/

#check @RBM.Gauss.Sizes.STIterR'
#check @RBM.Gauss.Sizes.stIterations'_holds
#check @RBM.Gauss.Sizes.stIterationsII'_holds

end
