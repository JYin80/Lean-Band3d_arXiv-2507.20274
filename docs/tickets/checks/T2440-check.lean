/-
Release check for T2440 (dispatcher V3, Mon Oct 12 04:33 UTC 2026; DECISIONS §247).  BA-L L3a3 `BALvl1A`: the BA local step `BALocStep`, packing and the step
identity `BAlvl1StepIdentity` (twin of LWLvl1 §9-§11; T2395 §6 row L3a3).  Part 1: merged names.  Part 2: the target statements as Prop values
(prefix `T2440_`; the 1b names them `BALocStep`, `BAtwistComb`, `BAframeStepIdentity`, `BAlvl1StepIdentity` or as the 1a fixes; content binding).
Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2440-check.lean
-/
import RBM3D.Graph.BASim
import RBM3D.Graph.BASim3
import RBM3D.Graph.BASymm1
import RBM3D.Graph.BASymm2
import RBM3D.Graph.BAVocab
import RBM3D.Graph.BAAtomic
import RBM3D.Graph.BAExpandW
import RBM3D.Graph.BAWeightOp
import RBM3D.Graph.BAGGOp
import RBM3D.Graph.LWSymm
import RBM3D.Graph.LWWeightExp
import RBM3D.Graph.LWLvl1
import RBM3D.Gauss.FineModel
import RBM3D.Defs.Sizes
import RBM3D.BA.MFixedPoint
import RBM3D.BA.CouplingWindow

set_option linter.style.longLine false
noncomputable section
open MeasureTheory
open RBM RBM.Gauss RBM.Graph

/-! ## Part 1: merged names -/
-- R1 (T2423, `Graph/BASim*`): the frame vocabulary (= `t/T2395` probe 154-205, 157) and the instance data of the five kinds
#check @RBM.Graph.BAPGraph.outsOf
#check @RBM.Graph.BAPGraph.withinOuts
#check @RBM.Graph.BAPGraph.splitOuts
#check @RBM.Graph.BAFrameStep
#check @RBM.Graph.BAFrameStep.within
#check @RBM.Graph.BAFrameStep.ggSplit
#check @RBM.Graph.BAPGraph.twist
#check @RBM.Graph.BAFrameStepT
#check @RBM.Graph.baFrameStepT_untag_holds
#check @RBM.Graph.BAsim'
#check @RBM.Graph.BASimInst.baPA
#check @RBM.Graph.BASimInst.pA
#check @RBM.Graph.BASimInst.qA
#check @RBM.Graph.BASimInst.baPB
#check @RBM.Graph.BASimInst.pB
#check @RBM.Graph.BASimInst.baPC
#check @RBM.Graph.BASimInst.pC
#check @RBM.Graph.BASimInst.qC
#check @RBM.Graph.BASimInst.baPW
#check @RBM.Graph.BASimInst.pW
#check @RBM.Graph.BASimInst.baPE
#check @RBM.Graph.BASimInst.pE
-- packed graphs, values, the partition (`BAVocab`), atoms (R0)
#check @RBM.Graph.BAPGraph
#check @RBM.Graph.BAPGraph.val
#check @RBM.Graph.BAComb.val
#check @RBM.Graph.BAGraph.partition
#check @RBM.Graph.BAGraph.val_eq_partition
#check @RBM.Graph.BAGraph.val_splitG
#check @RBM.Graph.BAGraph.Normal
#check @RBM.Graph.BAGraph.scalingOrder
#check @RBM.Graph.BAGraph.LocStd
#check @RBM.Graph.BAGraph.sameAtom
#check @RBM.Graph.BAGraph.intAtom
#check @RBM.Graph.BAGraph.atEdges
#check @RBM.Graph.BAGraph.atCharge
#check @RBM.Graph.baPG
-- L3a1, L3a2 (T2425, T2432): the twist and its integral
#check @RBM.Graph.BAGraph.twist
#check @RBM.Graph.BAGraph.twist_invol
#check @RBM.Graph.BAGraph.BASymm1_val_twist
#check @RBM.Graph.BASymm1_dataTr
#check @RBM.Graph.BASymm1_data_real
#check @RBM.Graph.baTwistInv_holds
#check @RBM.Graph.baSum_twist
#check @RBM.Graph.baTwistIntegral_gen
#check @RBM.Graph.baTwistSum_holds
#check @RBM.Graph.baTwistFormE_holds
#check @RBM.Graph.lwSymmCj
-- the frame identities and the term lists (`lanlw`, L2c1, L2c2)
#check @RBM.Graph.lanlw_val
#check @RBM.Graph.BAGraph.lanlwTerms
#check @RBM.Graph.BAGraph.lanlwT1
#check @RBM.Graph.BAGraph.lanlwD
#check @RBM.Graph.BAGraph.ext
#check @RBM.Graph.bpS
#check @RBM.Graph.bpM
#check @RBM.Graph.bpW
#check @RBM.Graph.bpv
#check @RBM.Graph.BAGraph.lw2
#check @RBM.Graph.BAGraph.lw4
#check @RBM.Graph.BAGraph.gg2
#check @RBM.Graph.BAGraph.gg4
#check @RBM.Graph.baSum
#check @RBM.Graph.BAexpFrameE
#check @RBM.Graph.baExpFrameE_holds
#check @RBM.Graph.owxEmb
#check @RBM.Graph.owxDE
#check @RBM.Graph.LGraph.owxExt
#check @RBM.Graph.owx_integral_list_sum
#check @RBM.Graph.owx_integrable_list_sum
-- data, law, instance datum
#check @RBM.Graph.BAlwData
#check @RBM.Gauss.PF
#check @RBM.Gauss.Idx
#check @RBM.BA.BASelf
#check @RBM.BA.CouplingWindowInst.flowP_data
-- the band twin (`LWLvl1` §9-§11)
#check @RBM.Graph.PGraph.lvl1Comp
#check @RBM.Graph.lvl1Pack
#check @RBM.Graph.LocStep
#check @RBM.Graph.Lvl1Reach
#check @RBM.Graph.lvl1_pack_identity
#check @RBM.Graph.lvl1_step_identity

/-! ## Part 2: the target statements (Prop values; no proof) -/

/-- Target 1 (`BALocStep`, `t/T2395` probe 207-208 verbatim): a frame step at the twisted graph, every output twisted back. -/
def T2440_LocStep {E : Type} (P : BAPGraph E) (outs : List (BAPGraph E)) : Prop :=
  ∃ (c t : Bool) (F : List (BAPGraph E)), BAFrameStep (P.twist c t) F ∧ outs = F.map (BAPGraph.twist c t)

/-- Target 3 (`BAtwistComb d`): the twist of a list of packed graphs in expectation at the BA law (no `BASelf`, no integrability). -/
def T2440_TwistComb (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (g0 Em t : ℝ) (m : ℂ) {E : Type} (c t' : Bool) (Ls : List (BAPGraph E)) (ℓe : E → Idx d L W),
    ∫ ω, BAComb.val (Ls.map (BAPGraph.twist c t')) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
      (if c then (star : ℂ → ℂ) else id) (∫ ω, BAComb.val Ls (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0))

/-- Target 4 (`BAframeStepIdentity d`): one frame step (five kinds) is an identity of expectations at the BA law; no normality. -/
def T2440_FrameIdentity (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
    ∀ {E : Type} (P : BAPGraph E) (F : List (BAPGraph E)), BAFrameStep P F → ∀ ℓe : E → Idx d L W,
      ∫ ω, P.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) = ∫ ω, BAComb.val F (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)

/-- Target 5 (`BAlvl1StepIdentity d`, probe 254-257 verbatim with `BALocStep` read as `T2440_LocStep`). -/
def T2440_StepIdentity (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
    ∀ {E : Type} (P : BAPGraph E) (outs : List (BAPGraph E)), T2440_LocStep P outs → P.g.Normal → ∀ ℓe : E → Idx d L W,
      ∫ ω, P.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) = ∫ ω, BAComb.val outs (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)

/-- Statement level at `d = 3` (the instances of the 1b use `L = 4`, `W = 2`, `flowP_data`), and target 1 at the twist of R1's macro datum `P_B`. -/
example : Prop := T2440_TwistComb 3
example : Prop := T2440_FrameIdentity 3
example : Prop := T2440_StepIdentity 3
