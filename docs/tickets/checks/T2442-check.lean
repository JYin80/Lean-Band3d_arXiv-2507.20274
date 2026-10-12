/-
Release check for T2442 (dispatcher V3, Mon Oct 12 06:18 UTC 2026; DECISIONS §252).  BA-L L3a4 `BALvl1B`: the BA measure predicates, the counter half of Lemma S
`BAstepMono`, and `BAlvl1StepGood` by the S′ reduction from R1's `BAsim'` (T2395 §6 row L3a4; twin of LWLvl1 §1 and `lvl1_step_good`).
Part 1: merged names.  Part 2: the target statements as Prop values (prefix `T2442_`; the 1b names them `BALvl1Good`, `BALvl1GoodLit`,
`BAlvl1StepGood`, `BAstepMono`, and the reduction e.g. `ba_lvl1StepGood_of_sim'`, or as the 1a fixes; content binding).
Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2442-check.lean
-/
import RBM3D.Graph.BALvl1A
import RBM3D.Graph.BASim
import RBM3D.Graph.BASim2
import RBM3D.Graph.BASim3
import RBM3D.Graph.BAAtomic
import RBM3D.Graph.BASymm1
import RBM3D.Graph.BAVocab
import RBM3D.Graph.BAWeightOp
import RBM3D.Graph.BAGGOp
import RBM3D.Graph.BAExpandW
import RBM3D.Graph.BAExpandWOrd
import RBM3D.Graph.BAScost
import RBM3D.Graph.LWLvl1

set_option linter.style.longLine false
noncomputable section
open RBM RBM.Graph

/-! ## Part 1: merged names -/
-- L3a3 (T2440, `Graph/BALvl1A`): the BA step, reachability, the step identity, the instance steps
#check @RBM.Graph.BALocStep
#check @RBM.Graph.BAReach
#check @RBM.Graph.BAlvl1StepIdentity
#check @RBM.Graph.baLvl1StepIdentity_holds
#check @RBM.Graph.BALvl1AInst.hFA
#check @RBM.Graph.BALvl1AInst.hFB
#check @RBM.Graph.BALvl1AInst.hFC
#check @RBM.Graph.BALvl1AInst.hFW
#check @RBM.Graph.BALvl1AInst.hFE
#check @RBM.Graph.BALvl1AInst.locStepB
#check @RBM.Graph.BALvl1AInst.locStepC
#check @RBM.Graph.BALvl1AInst.normalB
#check @RBM.Graph.BALvl1AInst.normalC
-- R1 (T2423, `Graph/BASim*`): the frame step, the simulation (`BAsim'` proved; `BAsim` pinned, proved nowhere), Lemma E, the matching
#check @RBM.Graph.BAFrameStep
#check @RBM.Graph.BAPGraph.outsOf
#check @RBM.Graph.BAPGraph.withinOuts
#check @RBM.Graph.BAPGraph.splitOuts
#check @RBM.Graph.BAPGraph.twist
#check @RBM.Graph.BAsim
#check @RBM.Graph.BAsim'
#check @RBM.Graph.baSim'_holds
#check @RBM.Graph.BAPGraph.baInv
#check @RBM.Graph.PGraph.baInv
#check @RBM.Graph.BAMatch
#check @RBM.Graph.baMatch_holds
#check @RBM.Graph.BAExtraGood
#check @RBM.Graph.baExtraGood_holds
-- R1's public helpers for target 3-4 (order families, output invariants, coarsening, transfer graphs, macro (b) terms)
#check @RBM.Graph.BASim_Ext
#check @RBM.Graph.BASim_Ext_split
#check @RBM.Graph.BASim_Ext_atomAdj
#check @RBM.Graph.BASim_splitG_normal
#check @RBM.Graph.BASim_merge_nExt
#check @RBM.Graph.BASim_outOf_baInv
#check @RBM.Graph.BASim_inv
#check @RBM.Graph.BASim_Fam
#check @RBM.Graph.BASim_fam_lw2
#check @RBM.Graph.BASim_fam_lw4
#check @RBM.Graph.BASim_fam_lanlw
#check @RBM.Graph.BASim_fam_gg2
#check @RBM.Graph.BASim_fam_gg4
#check @RBM.Graph.BASim_Fwithin
#check @RBM.Graph.BASim_fam_within
#check @RBM.Graph.BASim_Fd1
#check @RBM.Graph.BASim_fam_d1
#check @RBM.Graph.BASim_nExt_le
#check @RBM.Graph.BASim_Cons
#check @RBM.Graph.BASim_Cons.nExt
#check @RBM.Graph.BASim_Cons.nA_le
#check @RBM.Graph.BASim_counters_tr2
#check @RBM.Graph.BASim_inv_trA
#check @RBM.Graph.BASim_trB_facts
#check @RBM.Graph.BASim_Ttr
#check @RBM.Graph.BASim_ord_d2
#check @RBM.Graph.BASim_ord_d3
#check @RBM.Graph.BASim_d4
#check @RBM.Graph.BASim_inv_d4_A1
#check @RBM.Graph.BAGraph.BAScost_trA
#check @RBM.Graph.BAGraph.BAScost_trB
#check @RBM.Graph.BASimInst.baPB
#check @RBM.Graph.BASimInst.pB
-- R0 (T2417, `Graph/BAAtomic`): the atomic image and the atom-level measure pieces
#check @RBM.Graph.BAimg
#check @RBM.Graph.BAimg_holds
#check @RBM.Graph.BAGraph.img
#check @RBM.Graph.BAPGraph.img
#check @RBM.Graph.baPG
#check @RBM.Graph.BAGraph.sameAtom
#check @RBM.Graph.BAGraph.intAtom
#check @RBM.Graph.BAGraph.nLoops
#check @RBM.Graph.BAGraph.nExt
#check @RBM.Graph.BAGraph.nShare
#check @RBM.Graph.BAGraph.nPairs
#check @RBM.Graph.BAGraph.atEdges
#check @RBM.Graph.BAGraph.atCharge
#check @RBM.Graph.BAGraph.LocStd
-- L3a1 (T2425, `Graph/BASymm1`): the twist keeps the counters, normality, `nExt`, loops, pairs
#check @RBM.Graph.BAGraph.twist
#check @RBM.Graph.ba_twist_counters
#check @RBM.Graph.BAtwistInv
#check @RBM.Graph.baTwistInv_holds
-- counters, partition, order (`BAVocab`)
#check @RBM.Graph.BAPGraph
#check @RBM.Graph.BAGraph.atom
#check @RBM.Graph.BAGraph.mol
#check @RBM.Graph.BAGraph.nA
#check @RBM.Graph.BAGraph.nM
#check @RBM.Graph.BAGraph.nS
#check @RBM.Graph.BAGraph.nW
#check @RBM.Graph.BAGraph.counters
#check @RBM.Graph.BAGraph.scalingOrder
#check @RBM.Graph.BAGraph.Normal
#check @RBM.Graph.BAGraph.splitG
#check @RBM.Graph.BAGraph.packMerge
#check @RBM.Graph.BAGraph.partition
#check @RBM.Graph.BAGraph.scalingOrderG
#check @RBM.Graph.BAGraph.partition_normal
#check @RBM.Graph.BAGraph.le_scalingOrderG_iff
-- the term counters and orders of the three expansions (L2c1, L2c2, `lanlw`)
#check @RBM.Graph.BAWeightOp_circ
#check @RBM.Graph.BAGraph.lw2
#check @RBM.Graph.BAGraph.lw4
#check @RBM.Graph.lw_counters
#check @RBM.Graph.lw_scalingOrderG
#check @RBM.Graph.lw_mono
#check @RBM.Graph.BAGraph.gg2
#check @RBM.Graph.BAGraph.gg4
#check @RBM.Graph.gg_counters
#check @RBM.Graph.gg_scalingOrderG
#check @RBM.Graph.gg_mono
#check @RBM.Graph.BAGraph.lanlwTerms
#check @RBM.Graph.BAGraph.lanlwT1
#check @RBM.Graph.BAGraph.lanlwD
#check @RBM.Graph.lanlwT1_counters
#check @RBM.Graph.lanlwD_counters
#check @RBM.Graph.lanlw_scalingOrderG
-- the band twin (`LWLvl1` §1, §10)
#check @RBM.Graph.Lvl1Good
#check @RBM.Graph.LGraph.lvl1NLoops
#check @RBM.Graph.LGraph.lvl1NPairs
#check @RBM.Graph.LocStep
#check @RBM.Graph.PGraph.lvl1Comp
#check @RBM.Graph.lvl1_step_good

/-! ## Part 2: the target statements (Prop values; no proof) -/
section Targets
variable {E₁ I₁ E₂ I₂ : Type} [Fintype E₁] [DecidableEq E₁] [Fintype I₁] [DecidableEq I₁] [Fintype E₂] [DecidableEq E₂] [Fintype I₂] [DecidableEq I₂]

/-- Target 1 (`BALvl1Good`, `t/T2395` probe 44-48 verbatim): the band's `Lvl1Good` on atoms, `nExt` after `ord`. -/
def T2442_Good (Γ : BAGraph E₁ I₁) (Q : BAGraph E₂ I₂) : Prop :=
  Γ.scalingOrder ≤ Q.scalingOrder ∧ Q.nM ≤ Γ.nM ∧ ((Q.nA : ℤ) - Q.nW ≤ (Γ.nA : ℤ) - Γ.nW) ∧ Q.nExt ≤ Γ.nExt ∧
    (Γ.scalingOrder < Q.scalingOrder ∨ (Q.scalingOrder = Γ.scalingOrder ∧
      (Q.nExt < Γ.nExt ∨ (Q.nExt = Γ.nExt ∧ (Q.nLoops < Γ.nLoops ∨ (Q.nLoops = Γ.nLoops ∧
        (Q.nS < Γ.nS ∨ (Q.nS = Γ.nS ∧ Q.nPairs < Γ.nPairs))))))))

/-- Target 1 (`BALvl1GoodLit`, probe 50-53 verbatim): the band-literal measure on atoms, without `nExt`. -/
def T2442_GoodLit (Γ : BAGraph E₁ I₁) (Q : BAGraph E₂ I₂) : Prop :=
  Γ.scalingOrder ≤ Q.scalingOrder ∧ Q.nM ≤ Γ.nM ∧ ((Q.nA : ℤ) - Q.nW ≤ (Γ.nA : ℤ) - Γ.nW) ∧
    (Γ.scalingOrder < Q.scalingOrder ∨ (Q.scalingOrder = Γ.scalingOrder ∧
      (Q.nLoops < Γ.nLoops ∨ (Q.nLoops = Γ.nLoops ∧ (Q.nS < Γ.nS ∨ (Q.nS = Γ.nS ∧ Q.nPairs < Γ.nPairs))))))

end Targets

/-- Target 1 (`BAlvl1StepGood`, probe 259-260 verbatim with `BALvl1Good` read as `T2442_Good`): every output of a BA step is normal and good. -/
def T2442_StepGood : Prop := ∀ {E : Type} (P : BAPGraph E) (outs : List (BAPGraph E)), BALocStep P outs → P.g.Normal →
  ∀ Q ∈ outs, Q.g.Normal ∧ T2442_Good P.g Q.g

/-- Target 1 (`BAstepMono`, probe 269-270 verbatim; proved as target 4): the counter half of Lemma S at a frame step. -/
def T2442_StepMono : Prop := ∀ {E : Type} (P : BAPGraph E) (outs : List (BAPGraph E)), BAFrameStep P outs → P.g.Normal → ∀ Q ∈ outs, Q.g.Normal ∧
  P.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.nM ≤ P.g.nM ∧ ((Q.g.nA : ℤ) - Q.g.nW ≤ (P.g.nA : ℤ) - P.g.nW) ∧ Q.g.nExt ≤ P.g.nExt

/-- Target 2 (the reduction of probe 323 restated for R1's `BAsim'`, `BASim.lean:222`): the hypothesis `BAsim m` becomes `BAsim' m`, the rest is unchanged. -/
def T2442_Reduction : Prop := ∀ m : ℂ, BAimg → BAsim' m → T2442_StepMono → BAtwistInv → T2442_StepGood

/-- Statement level: targets 4 and 5 (`baStepMono_holds`, `baLvl1StepGood_holds`), and target 5 at the twisted macro step (a) of `P_B` (`BALvl1AInst.locStepB`). -/
example : Prop := T2442_StepMono
example : Prop := T2442_StepGood
example : Prop := T2442_Reduction
example : Prop := ∀ Q ∈ ((baPG BASimInst.baPB).withinOuts BASimInst.pB).map (BAPGraph.twist true true),
  Q.g.Normal ∧ T2442_Good ((baPG BASimInst.baPB).twist true true).g Q.g
