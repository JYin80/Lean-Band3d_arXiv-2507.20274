/-
Release check for T2499 (dispatcher V4, 2026-10-14; DECISIONS §310).  U U5e = `BA/Step5IIITargets`: the targets of BA case (iii)
of Step 5, the last row of U5 (design `docs/reports/T2459-design.md` U5-4 `:194-196`, row U5e `:258`; probe
`t/T2459:RBM3D/Probe/T2459Pins.lean` `:31-55`, `:227-236`, `:322-342`, never merged).
Targets: `STPfStep5gL` (U6 target 10, `Chain/Step5Gen.lean:252`) and `STStep5IIIgL` (U6 target 9, `:228`) at the BA tuple
`(seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`, d = 3 (U-C5, DECISIONS §263 (5)); the composition `main_of_parts` from the
two merged U5d texts `BAStep5IIIWalk`, `BAStep5IIIFromWalk` (`BA/Step5IIIWalk2.lean:73, 79`).  Case (iii) from `lem:pf_step5`
is the merged U4s1 result `ST_step5_caseIII_of_pfgL` (`Chain/Step5CasesGen.lean:406`, = `T2462_caseIII`), whose premise
`Step5CasesGen_FlowFacts` (`:140`) holds at BA through the merged `baStep5CasesGen_flowFacts` (`BA/SEforLnBA.lean:152`).
Coupling (UBA-C1; R1 = DECISIONS §273 (1)): no crossing in this row, R1 is not read.  TN-C4: no `STGridRepNgL`.
Part 1: merged names.  Part 2: pins (prefix `T2499_`; binding: `T2499_STPfStep5BA`, `T2499_STStep5IIIBA`,
`T2499_MainOfParts`), then shapes (not binding).  Part 3: the band twins and the band consumer (unchanged, not edited).
Merged names only; statements only.
Run: lake env lean docs/tickets/checks/T2499-check.lean
-/
import RBM3D.BA.Step5IIIWalk2
import RBM3D.BA.SEforLnBA
import RBM3D.Chain.Step5CasesGen
import RBM3D.Chain.Step34Gen
import RBM3D.Induction.PfStep5
import RBM3D.Induction.Step5Cases
import RBM3D.Induction.MainIndRegimes
import RBM3D.Induction.Step1Setup

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- U6 = T2458 (merged 1debc230, `Chain/Step5Gen.lean`): the pin shape `:191`, the regime form `:214`, case (iii) `:228`,
-- `lem:pf_step5` `:252`, the conclusions `:139`, `:62`
#check @RBM.BA.STIngR5gL
#check @RBM.BA.STStep5RgL
#check @RBM.BA.STStep5IIIgL
#check @RBM.BA.STPfStep5gL
#check @RBM.BA.STPfConclgL
#check @RBM.BA.STStep5ConclgL
-- U4s1a = T2462 (merged c9f69dba, `Chain/Step5CasesGen.lean`): target 1 `:140` (= `T2462_FlowFacts`), target 4 `:406`
-- (= `T2462_caseIII`), target 6 `:169` (assembly), the band flow facts `:156`
#check @RBM.BA.Step5CasesGen_FlowFacts
#check @RBM.BA.ST_step5_caseIII_of_pfgL
#check @RBM.BA.ST_step5_assemblygL
#check @RBM.BA.step5CasesGen_flowFacts_band
-- U2-BA (a) = T2486 (merged 7be99aae, `BA/SEforLnBA.lean:152`): the BA flow facts (`T2486_BAFlowFacts`; `κm = κ`)
#check @RBM.BA.baStep5CasesGen_flowFacts
-- U5d = T2493 (merged f2af0245, f7470f58, `BA/Step5IIIWalk2.lean`): the grid conclusion `:63`, the walk `:73`, `:763`,
-- the lift `:79`, `:977`, the per-flow walk `:582`
#check @RBM.BA.BAStep5IIIWalkConcl
#check @RBM.BA.BAStep5IIIWalk
#check @RBM.BA.BAStep5IIIFromWalk
#check @RBM.BA.baStep5III_walk_at
#check @RBM.BA.baStep5IIIWalk_holds
#check @RBM.BA.baStep5IIIFromWalk_holds
-- the BA tuple (`BA/FlowPins.lean:380-393`), the law (`Gauss/FineModel.lean:169`, `Defs/Sizes.lean:182`), size-level names
-- (`Induction/Step5Pins.lean:58`, `Induction/Defs.lean:168`)
#check @RBM.BA.BAFlow
#check @RBM.BA.baFMz
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.withLam
#check @RBM.Gauss.Sizes.STReg5III
#check @RBM.Gauss.Sizes.STConStInd
-- the carrier predicates among the binders of `STIngR5gL` (hypotheses of the instances; `Chain/Carrier.lean`,
-- `Chain/Step2Gen.lean:514`, `Chain/Step34Gen.lean:58, 65`)
#check @RBM.BA.STKboundgL
#check @RBM.BA.STKwardgL
#check @RBM.BA.STLKgL
#check @RBM.BA.STDecaygL
#check @RBM.BA.STDecayStronggL
#check @RBM.BA.STStep1LoopgL
#check @RBM.BA.STStep2ConclgL
#check @RBM.BA.STLmaxUgL
#check @RBM.BA.STLKUgL
-- the instance data (U5d's instance route, `BA/Step5IIIWalk2.lean:994-1065`): `Defs/Sizes.lean:260`,
-- `BA/FlowPins.lean:1181, 1214, 1254`, `BA/Step5IIIGood.lean:623`, `Induction/Step1Setup.lean:1226`
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.half_lt_t0
#check @RBM.BA.Step5IIIGood_reg_sz0
#check @RBM.Ind.Step1SetupInst.s1Setup_conStInd_const

/-! ## Part 2: pins (binding as marked) and shapes (not binding) -/

open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Target 2** (binding; the probe's `T2459_STPfStep5BA`, `:35`): `lem:pf_step5` (`3_5:2364-2383`) at the BA tuple, d = 3;
U6 target 10 (`STPfStep5gL`, `Chain/Step5Gen.lean:252`) read at `(seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`. -/
def T2499_STPfStep5BA : Prop :=
  STPfStep5gL 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0

/-- **Target 3** (binding; the probe's `T2459_STStep5IIIBA`, `:36`): Step 5 in case (iii) (`STReg5III`: `lam² ≤ 1 - t`) at the
BA tuple, d = 3; U6 target 9 (`STStep5IIIgL`, `Chain/Step5Gen.lean:228`). -/
def T2499_STStep5IIIBA : Prop :=
  STStep5IIIgL 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0

/-- **Target 1** (binding; the probe's `T2459_main_of_parts`, `:227`, with the merged U5d texts in place of the probe's
`T2459_BAWalk` `:213` and `T2459_BAfromWalk` `:218`): the target 2 statement from the walk and the lift.  Both premises are
merged and concluded (`baStep5IIIWalk_holds`, `baStep5IIIFromWalk_holds`). -/
def T2499_MainOfParts : Prop := BAStep5IIIWalk → BAStep5IIIFromWalk → T2499_STPfStep5BA

/-! ### Shapes (not binding) -/

/-- Target 3 from target 2: the merged U4s1 result `ST_step5_caseIII_of_pfgL` at the BA tuple (the probe's
`T2459_caseIII_succ`, `:47`).  Its premise, family row 1 (guarded: `∀ κ > 0, ∃ κm > 0, … Flow → …`), is the merged
`baStep5CasesGen_flowFacts 3`, stated with `fun sz z => baFMz sz z`, `fun sz z => BAflowT0 sz z` (eta forms of the tuple). -/
example : Prop :=
  Step5CasesGen_FlowFacts 3 (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 → T2499_STPfStep5BA → T2499_STStep5IIIBA

/-- The probe's chain `:234-236` with the merged names: target 3 from the two U5d texts and the flow facts. -/
example : Prop :=
  BAStep5IIIWalk → BAStep5IIIFromWalk →
    Step5CasesGen_FlowFacts 3 (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 → T2499_STStep5IIIBA

/-- Target 4 (a): target 2 at the instance (`sz0`, `zSeq`, `flow_sz0` with `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`,
`s ≡ 1/10 < t ≡ 1/2 < t₀`, `Cd = 1`); the regime (`Step5IIIGood_reg_sz0`) and `(con_st_ind)` (`s1Setup_conStInd_const`) are
discharged; the nine carrier predicates stay hypotheses (the probe's `T2459_inst_IngR5` route, `:328`). -/
example : Prop := T2499_STPfStep5BA →
  STKboundgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) →
  STKwardgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) →
  STLKgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) →
  STDecaygL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) →
  STDecayStronggL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) →
  STStep1LoopgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) →
  STStep2ConclgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) 1 →
  STLmaxUgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) →
  STLKUgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) →
    STPfConclgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ))

/-- Target 4 (b): target 3 at the same instance gives the uniform Step-5 conclusion. -/
example : Prop := T2499_STStep5IIIBA →
  STKboundgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) →
  STKwardgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) →
  STLKgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) →
  STDecaygL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) →
  STDecayStronggL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) →
  STStep1LoopgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) →
  STStep2ConclgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) 1 →
  STLmaxUgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) →
  STLKUgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) →
    STStep5ConclgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ))

/-- Target 4 (c), the consumer side: the conclusion of 4 (b) through `ST_step5_assemblygL` (`Chain/Step5CasesGen.lean:169`)
is `(Eq:Gdecay)` and `(Eq:Gdecay+s<g)` at `t ≡ 1/2`, the induction hypothesis of the next step (BA main induction, V). -/
example : Prop :=
  STStep5ConclgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) →
    STDecaygL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 2 : ℝ)) ∧
      STDecayStronggL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 2 : ℝ))

end RBM.BA

/-! ## Part 3: the band twins (`stPfStep5_holds` `Induction/PfStep5.lean:2457`, `stStep5III_holds` `:2473`,
`ST_step5_caseIII_of_pf` `Induction/Step5Cases.lean:311`), the band bridges (`Chain/Step5Gen.lean:403, 464`) and the band
consumer of case (iii) (`ST_mainIndR_III_of_steps`, `Induction/MainIndRegimes.lean:217`); unchanged, not edited -/

#check @RBM.Gauss.Sizes.stPfStep5_holds
#check @RBM.Gauss.Sizes.stStep5III_holds
#check @RBM.Gauss.Sizes.ST_step5_caseIII_of_pf
#check @RBM.BA.STStep5III_iff_gL
#check @RBM.BA.STPfStep5_iff_gL
#check @RBM.Gauss.Sizes.ST_mainIndR_III_of_steps

end
