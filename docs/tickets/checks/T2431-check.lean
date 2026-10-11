/-
Release check for T2431 (dispatcher V3, Sun Oct 11 22:07 UTC 2026; DECISIONS §241).  BA-TL TL-V: the base case of TL2 and the chain of times
with the TL2 conjunct (supervisor 1049 Q2; design T2413 §6 D6).  Part 1: the target statements (merged pins of TL0; no new
pin).  Part 2: merged names.  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2431-check.lean
-/
import RBM3D.BA.TwistPins
import RBM3D.BA.FlowPins
import RBM3D.BA.GreenSchur
import RBM3D.BA.MFixedPoint
import RBM3D.Propagator.Pins
import RBM3D.Defs.Sizes
import RBM3D.Defs.StochDomAt
import RBM3D.Chain.Carrier
import RBM3D.Induction.Step34Pins
import RBM3D.Induction.MainIndBase
import RBM3D.Induction.MainIndChain
import RBM3D.Induction.MainIndOut

/-! ## Part 1: the target statements -/
example : Prop := ∀ d : ℕ, RBM.BA.BATwistLoopBase d
example : Prop := ∀ d : ℕ, RBM.BA.BAChainTL d

/-! ## Part 2: merged names -/
#check @RBM.BA.BATwistLoopBase
#check @RBM.BA.BAChainTL
#check @RBM.BA.BAMainIndTL
#check @RBM.BA.BAMLOutTL
#check @RBM.BA.BATwistLoopLaw
#check @RBM.BA.twL2'
#check @RBM.BA.twK
#check @RBM.BA.twLoopX
#check @RBM.BA.twTrP
#check @RBM.BA.twChg
#check @RBM.BA.twBlk
#check @RBM.BA.twMB_ba
#check @RBM.BA.twCirc_holds
#check @RBM.BA.STG0M
#check @RBM.BA.STBaseG
#check @RBM.BA.STConclgL
#check @RBM.BA.mainIndBase_bctl_nonneg
#check @RBM.BA.STHorizonG
#check @RBM.BA.STMainIndG
#check @RBM.BA.stPosConclG_of_mainIndG
#check @RBM.BA.stChainTime_zero
#check @RBM.BA.stChainTime_top
#check @RBM.BA.stChainTime_facts
#check @RBM.BA.stChainSteps
#check @RBM.BA.STLocalMaxgL_of_STLocalEntrygL
#check @RBM.BA.STMLOutG
#check @RBM.BA.stMLOutG_of_mainIndG
#check @RBM.BA.BAFlow
#check @RBM.BA.baFMz
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflow_real
#check @RBM.BA.BAMfine_eq
#check @RBM.BA.BAMsigma
#check @RBM.PropThetaQ
#check @RBM.Gauss.card_Iblk
#check @RBM.BA.PrecL
#check @RBM.badSetAt
#check @RBM.StochDomAt.of_eventually_empty
#check @RBM.StochDomAt.of_subset_union
#check @RBM.Gauss.Sizes.STAny
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.half_lt_t0
