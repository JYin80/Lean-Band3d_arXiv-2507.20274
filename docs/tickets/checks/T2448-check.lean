/-
Release check for T2448 (dispatcher V3, Mon Oct 12 10:39 UTC 2026; DECISIONS §260).  BA-L L3d3 `BAEngine`: the BA engine at the start terms of `G = Ǧ + M` on
`fxyPowGraph p`: the six-conjunct conclusion at BA (`BALocRegConcl`), black waved edges along `BAReach`, the assembly, `ba_localregularX`
(T2387 §6 row L3d3, twin of `LWEngine 1-937`; under S′ the `m`-tag half of the band file has no BA content and the recursion is L3a5's).
Part 1: merged names.  Part 2: the target statements as Prop values (prefix `T2448_`; the 1b names them `BALocRegConcl`, `baStep_nWS`,
`ba_nWS_ge`, `baStart_nWS`, `baEngine_assemble`, `ba_localregularX`, or as the 1a fixes; content binding), the O2R-C3 binder verbatim, and
shapes (not binding) of the route and of the instances.
Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2448-check.lean
-/
import RBM3D.Graph.BALvl1C
import RBM3D.Graph.BAStepS
import RBM3D.Graph.BAScost
import RBM3D.Graph.BALvl1A
import RBM3D.Graph.BASim
import RBM3D.Graph.BASim3
import RBM3D.Graph.BAAtomic
import RBM3D.Graph.BAAtom
import RBM3D.Graph.BAAtom2
import RBM3D.Graph.BASymm1
import RBM3D.Graph.BAVocab
import RBM3D.Graph.BAWeightOp
import RBM3D.Graph.BAGGOp
import RBM3D.Graph.BAExpandW
import RBM3D.Graph.BAExpandId
import RBM3D.Graph.LWEngine
import RBM3D.Graph.LWProv
import RBM3D.Graph.LWMoment
import RBM3D.Graph.LWLvl1
import RBM3D.Graph.LWSymm
import RBM3D.Graph.LWWeightExp
import RBM3D.Graph.LocalRegular
import RBM3D.Gauss.FineModel
import RBM3D.Defs.Sizes
import RBM3D.BA.MFixedPoint
import RBM3D.BA.CouplingWindow

set_option linter.style.longLine false
noncomputable section
open MeasureTheory
open RBM RBM.Gauss RBM.Graph

/-! ## Part 1: merged names -/
-- L3a5 (T2446, `Graph/BALvl1C`, merged 7f23e96): the data-free lists per graph (the engine's recursion), the paper form at the cutoff, the induction
#check @RBM.Graph.BAlvl1Lemma
#check @RBM.Graph.BAlvl1LemmaSize
#check @RBM.Graph.baLvl1Lemma_holds
#check @RBM.Graph.baLvl1LemmaSize_holds
#check @RBM.Graph.baLvl1ExistsStep_holds
#check @RBM.Graph.BAReach.trans
#check @RBM.Graph.ba_lvl1_induction
-- L3b4′ (T2443, `Graph/BAStepS`, merged 9eaf866): (6) along `BAReach` from a start term, under the shape binder (`:100`)
#check @RBM.Graph.BALocReg6
#check @RBM.Graph.baLocReg6_reach
#check @RBM.Graph.BAFrameStepTN
#check @RBM.Graph.baInit_locReg6InvA
#check @RBM.Graph.baShapeLL_s1_tn
#check @RBM.Graph.baShapeLL_e1_tn
#check @RBM.Graph.baReach_bReach
-- L3b3′ (T2426, `Graph/BAScost`): the shapes, the shape predicate, the cost invariant
#check @RBM.Graph.BAShape
#check @RBM.Graph.BAShape.e2
#check @RBM.Graph.BAShape.macroA
#check @RBM.Graph.BAShape.macroB
#check @RBM.Graph.BAShapeLL
#check @RBM.Graph.BTStep
#check @RBM.Graph.locReg6InvA
-- L3a3 (T2440, `Graph/BALvl1A`): the step, reachability, integrability, packing, instances
#check @RBM.Graph.BALocStep
#check @RBM.Graph.BAReach
#check @RBM.Graph.BAReach.refl
#check @RBM.Graph.BAReach.step
#check @RBM.Graph.baLvl1StepIdentity_holds
#check @RBM.Graph.BALvl1A_integrable_val
#check @RBM.Graph.BALvl1A_val_of_factor
#check @RBM.Graph.BALvl1A_val_of_not
#check @RBM.Graph.BALvl1A_comb_append
#check @RBM.Graph.BALvl1AInst.locStepB
#check @RBM.Graph.BALvl1AInst.normalB
-- R1 (T2423, `Graph/BASim`): the five frame steps and their output lists (target 2 reads every output)
#check @RBM.Graph.BAFrameStep
#check @RBM.Graph.BAFrameStep.weight
#check @RBM.Graph.BAFrameStep.within
#check @RBM.Graph.BAFrameStep.edge
#check @RBM.Graph.BAFrameStep.gg
#check @RBM.Graph.BAFrameStep.ggSplit
#check @RBM.Graph.BAPGraph.outsOf
#check @RBM.Graph.BAPGraph.withinOuts
#check @RBM.Graph.BAPGraph.splitOuts
#check @RBM.Graph.BAPGraph.twist
-- L2c1, L2c2, `BAExpandW`, L3a1: the terms are `owxExt` on the parent (its waved edges mapped, new ones appended); the twist is `lwSymmTwistG`
#check @RBM.Graph.BAGraph.ext
#check @RBM.Graph.bpW
#check @RBM.Graph.BAGraph.lw2
#check @RBM.Graph.BAGraph.lw4
#check @RBM.Graph.BAGraph.gg2
#check @RBM.Graph.BAGraph.gg4
#check @RBM.Graph.BAGraph.lanlwExt
#check @RBM.Graph.BAGraph.lanlwT1
#check @RBM.Graph.BAGraph.lanlwD
#check @RBM.Graph.BAGraph.lanlwTerms
#check @RBM.Graph.BAGraph.twist
#check @RBM.Graph.lwSymmTwistG
#check @RBM.Graph.LGraph.owxExt
#check @RBM.Graph.WEdge.conj
#check @RBM.Graph.WEdge.transpose
#check @RBM.Graph.WEdge.map
-- R0 / `BAVocab` / `BAAtomic`: the start terms, the partition (value, normality, edge counts), counters, values, atoms, the data and law
#check @RBM.Graph.BAGraph.ofLGraph
#check @RBM.Graph.BAGraph.splitG
#check @RBM.Graph.BAGraph.splitG_edges
#check @RBM.Graph.BAGraph.merge
#check @RBM.Graph.BAGraph.packMerge
#check @RBM.Graph.BAGraph.partition
#check @RBM.Graph.BAGraph.val_eq_partition
#check @RBM.Graph.BAGraph.partition_normal
#check @RBM.Graph.BAGraph.val
#check @RBM.Graph.BAPGraph
#check @RBM.Graph.BAPGraph.val
#check @RBM.Graph.BAComb.val
#check @RBM.Graph.BAPGraph.scalingOrder
#check @RBM.Graph.BAGraph.scalingOrder
#check @RBM.Graph.BAGraph.scalingSize
#check @RBM.Graph.BAGraph.counters
#check @RBM.Graph.BAGraph.nM
#check @RBM.Graph.BAGraph.nA
#check @RBM.Graph.BAGraph.nW
#check @RBM.Graph.BAGraph.Normal
#check @RBM.Graph.BAGraph.LocStd
#check @RBM.Graph.atomSetoid
#check @RBM.Graph.baPG
#check @RBM.Graph.BAlwData
#check @RBM.Gauss.PF
#check @RBM.Gauss.Idx
#check @RBM.BA.BASelf
-- L4d (T2419, `Graph/BAExpandId`, merged 977d5da): listed in T2387 for `expandG`; at BA no exponent pairs (`:86-88`); not expected to be read
#check @RBM.Graph.BAG5Identity
#check @RBM.Graph.baExpandIdentity_holds
#check @RBM.Graph.BARCand.kids
-- generic band lemmas used as is
#check @RBM.Graph.fxyPowGraph
#check @RBM.Graph.fxyPowGraph_counters
#check @RBM.Graph.lvl1Cutoff
#check @RBM.Graph.lvl1_size_le
#check @RBM.Graph.lvl1_choose_list
#check @RBM.Graph.lvl1_sum_flatMap
#check @RBM.Graph.owx_integrable_list_sum
#check @RBM.Graph.owx_integral_list_sum
-- the band twin (`Graph/LWEngine`): §1 conclusion, §1-§4 tags (no BA content), §5 black waved edges, §6 recursion (L3a5's at BA) and assembly
#check @RBM.Graph.LWLocRegConcl
#check @RBM.Graph.lwEvX
#check @RBM.Graph.LocStepX
#check @RBM.Graph.LocStepX.eval
#check @RBM.Gauss.Sizes.partitionX
#check @RBM.Graph.lwEngine_nWS
#check @RBM.Graph.lwEngine_col_conj
#check @RBM.Graph.lwEngine_col_transpose
#check @RBM.Graph.lwEngine_part_nWS
#check @RBM.Graph.lwEngine_locStep_nWS
#check @RBM.Graph.lw_nWS_ge
#check @RBM.Graph.lwEngine_exists
#check @RBM.Graph.lwEngine_assemble
#check @RBM.Graph.lwEngine_fxy_nWS
#check @RBM.Graph.lw_localregularX
-- band consumers that the BA consumers L3d2 (`BAMomentGen`), L3d4 (`BAProv`) twin; the BA (1)-(5) as the merged BA readers take them
#check @RBM.Graph.LWEngineProv
#check @RBM.Graph.lwEngineProv_imp_localregularX
#check @RBM.Graph.lw_localregularXP
#check @RBM.Gauss.Sizes.lwMoment_expand
#check @RBM.Gauss.Sizes.lwMoment_prec_far
#check @RBM.Graph.PGraph.LocReg345
#check @RBM.Graph.BAShadowPG
#check @RBM.Graph.baAuxNested_holds
-- instance data (`BALvl1CInst`): the flow point, the external labelling
#check @RBM.BA.CouplingWindowInst.flowP_data
#check @RBM.BA.CouplingWindowInst.g0P
#check @RBM.BA.CouplingWindowInst.EP
#check @RBM.BA.CouplingWindowInst.t0P
#check @RBM.BA.CouplingWindowInst.m0P
#check @RBM.Graph.BASymm1Inst.ℓ0

/-! ## Part 2: the target statements (Prop values; no proof) -/

/-- The binder of `BALocReg6` (`BAStepS:100`), verbatim (supervisor 0948 O2R-C3): the three shape inputs of T2426 audit O2.  Carried as the first
hypothesis of targets 3-4 while T2447 is not merged; never restated as a new `Prop`, no owed registry line. -/
def T2448_Binder : Prop :=
  ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapeLL sh BAFrameStepTN

/-- Target 1 (`BALocRegConcl`, the BA twin of `LWLocRegConcl`, `LWEngine:61-77`): at the start terms `(BAGraph.ofLGraph (fxyPowGraph p)).partition`,
(a) the outputs are locally standard at atoms with (6) in its BA form (the far half at distinct atoms, 0951 L4-C4 (b)); (b) the errors have scaling size
`≤ W^{-D}`; (c) every graph is reached from a start term below that term's cutoff, normal, with the counters of `BAlvl1LemmaSize`; (d) the identity of
expectations at `BAlwData` (`BASelf`, `0 ≤ t < 1` only, C1).  No `m`-tags (BA steps carry no exponent pairs); no (1)-(5) (L3b1, L3b2). -/
def T2448_LocRegConcl (p : ℕ) (c : ℝ) (K0 d : ℕ) (D : ℝ) (outs errs : List (BAPGraph (Fin 2))) : Prop :=
  (∀ Q ∈ outs, Q.g.LocStd ∧ 2 * (p : ℤ) ≤ Q.scalingOrder ∧
    (¬ atomSetoid Q.g (Sum.inl (Q.ext 0)) (Sum.inl (Q.ext 1)) → 3 * (p : ℤ) ≤ Q.scalingOrder)) ∧
  (∀ Q ∈ errs, ∀ (W L : ℕ) (Ψ : ℝ), 1 ≤ W → 1 ≤ L → (L : ℝ) ^ d ≤ (W : ℝ) ^ K0 →
    (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ → Ψ ≤ (W : ℝ) ^ (-c) → Q.g.scalingSize Ψ W d L ≤ (W : ℝ) ^ (-D)) ∧
  (∀ Q ∈ outs ++ errs, ∃ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition,
    BAReach (lvl1Cutoff c K0 d D P0.g.counters : ℤ) P0 Q ∧ Q.g.Normal ∧ P0.g.scalingOrder ≤ Q.g.scalingOrder ∧
      Q.g.nM ≤ P0.g.nM ∧ (Q.g.nA : ℤ) - Q.g.nW ≤ (P0.g.nA : ℤ) - P0.g.nW) ∧
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
    ∀ ℓe : Fin 2 → Idx d L W,
      ∫ ω, (BAGraph.ofLGraph (fxyPowGraph p)).val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
        ∫ ω, BAComb.val (outs ++ errs) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)

/-- Target 2 (`baStep_nWS`, twin of `lwEngine_locStep_nWS`, `LWEngine:560`): one BA step does not lower the number of black waved edges. -/
def T2448_StepNWS : Prop :=
  ∀ {E : Type} (P : BAPGraph E) (outs : List (BAPGraph E)), BALocStep P outs →
    ∀ Q ∈ outs, P.g.waved.countP (fun e => !e.col) ≤ Q.g.waved.countP (fun e => !e.col)

/-- Target 2 (`ba_nWS_ge`, twin of `lw_nWS_ge`, `LWEngine:605`): along `BAReach`. -/
def T2448_NWSGe : Prop :=
  ∀ {E : Type} {K : ℤ} {P Q : BAPGraph E}, BAReach K P Q → P.g.waved.countP (fun e => !e.col) ≤ Q.g.waved.countP (fun e => !e.col)

/-- Target 2 (`baStart_nWS`, twin of `lwEngine_fxy_nWS`, `LWEngine:765`): every start term has `p` black waved edges. -/
def T2448_StartNWS : Prop :=
  ∀ (p : ℕ), ∀ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition, P0.g.waved.countP (fun e => !e.col) = p

/-- Target 3 (`baEngine_assemble`, twin of `lwEngine_assemble`, `LWEngine:725`): lists with the conclusion of `BAlvl1LemmaSize` (`BALvl1C:63-73`) at every
start term give `BALocRegConcl` for the concatenated lists (its conclusion head is `BALocRegConcl`: the premise scan's producer).  Before T2447 merges the
1b proves `T2448_Binder → T2448_Assemble`. -/
def T2448_Assemble : Prop :=
  ∀ (p : ℕ) (c : ℝ) (K0 d : ℕ) (D : ℝ) (fo fe : BAPGraph (Fin 2) → List (BAPGraph (Fin 2))),
    (∀ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition,
      (∀ Q ∈ fo P0, Q.g.LocStd ∧ P0.g.scalingOrder ≤ Q.g.scalingOrder) ∧
      (∀ Q ∈ fe P0, ∀ (W L : ℕ) (Ψ : ℝ), 1 ≤ W → 1 ≤ L → (L : ℝ) ^ d ≤ (W : ℝ) ^ K0 →
        (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ → Ψ ≤ (W : ℝ) ^ (-c) → Q.g.scalingSize Ψ W d L ≤ (W : ℝ) ^ (-D)) ∧
      (∀ Q ∈ fo P0 ++ fe P0, BAReach (lvl1Cutoff c K0 d D P0.g.counters : ℤ) P0 Q ∧ Q.g.Normal ∧ P0.g.scalingOrder ≤ Q.g.scalingOrder ∧
        Q.g.nM ≤ P0.g.nM ∧ (Q.g.nA : ℤ) - Q.g.nW ≤ (P0.g.nA : ℤ) - P0.g.nW) ∧
      ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
        ∀ ℓe : Fin 2 → Idx d L W,
          ∫ ω, P0.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
            ∫ ω, BAComb.val (fo P0 ++ fe P0) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)) →
    T2448_LocRegConcl p c K0 d D (((BAGraph.ofLGraph (fxyPowGraph p)).partition).flatMap fo)
      (((BAGraph.ofLGraph (fxyPowGraph p)).partition).flatMap fe)

/-- Target 4 (`ba_localregularX`, twin of `lw_localregularX`, `LWEngine:771`): one pair of data-free lists with `BALocRegConcl` and at least `p` black
waved edges in every graph (the band's `∀ m ≠ 0` has no BA counterpart: the lists and the conclusion read no `m`).  Before T2447 merges the 1b proves
`T2448_Binder → T2448_LocRegX`. -/
def T2448_LocRegX : Prop :=
  ∀ (p : ℕ) (c : ℝ), 0 < c → ∀ (K0 d : ℕ) (D : ℝ), ∃ outs errs : List (BAPGraph (Fin 2)),
    T2448_LocRegConcl p c K0 d D outs errs ∧ ∀ Q ∈ outs ++ errs, p ≤ Q.g.waved.countP (fun e => !e.col)

/-- Statement level: the binder forms of targets 3-4 (before T2447 merges), the route of target 2, of target 3 (merged (6) + binder), of target 4
(L3a5's paper form per start term + targets 2-3).  Shapes, not binding. -/
example : Prop := T2448_Binder → T2448_Assemble
example : Prop := T2448_Binder → T2448_LocRegX
example : Prop := T2448_StepNWS → T2448_NWSGe
example : Prop := BALocReg6 → T2448_Binder → T2448_Assemble
example : Prop := (∀ d, BAlvl1LemmaSize d) → T2448_Assemble → T2448_StartNWS → T2448_NWSGe → T2448_LocRegX

/-- Shape (not binding) of the instance of target 4 at `p = 2`, `c = 1/4`, `K0 = 2`, `d = 3`, `D = 10` (T2446 target 5 values), with the identity at the
flow point of `BALvl1CInst` (`d = 3`, `L = 4`, `W = 2`, `ℓ0`); before T2447 merges, the instance takes the binder as a hypothesis (as `BAStepS:508`). -/
example : Prop := ∃ outs errs : List (BAPGraph (Fin 2)), T2448_LocRegConcl 2 (1 / 4) 2 3 10 outs errs ∧
  (∀ Q ∈ outs ++ errs, 2 ≤ Q.g.waved.countP (fun e => !e.col)) ∧
  ∫ ω, (BAGraph.ofLGraph (fxyPowGraph 2)).val
      (BAlwData 3 4 2 RBM.BA.CouplingWindowInst.g0P RBM.BA.CouplingWindowInst.EP RBM.BA.CouplingWindowInst.t0P RBM.BA.CouplingWindowInst.m0P ω)
      BASymm1Inst.ℓ0 ∂(PF 3 4 2 0) =
    ∫ ω, BAComb.val (outs ++ errs)
      (BAlwData 3 4 2 RBM.BA.CouplingWindowInst.g0P RBM.BA.CouplingWindowInst.EP RBM.BA.CouplingWindowInst.t0P RBM.BA.CouplingWindowInst.m0P ω)
      BASymm1Inst.ℓ0 ∂(PF 3 4 2 0)

/-- Shape (not binding) of the nondegenerate instance of target 2: a start term at `p = 2` that is not locally standard, a step from it, and every output
keeps the two black waved edges. -/
example : Prop := ∃ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph 2)).partition, ¬ P0.g.LocStd ∧
  ∃ outs, BALocStep P0 outs ∧ outs ≠ [] ∧ ∀ Q ∈ outs, 2 ≤ Q.g.waved.countP (fun e => !e.col)
