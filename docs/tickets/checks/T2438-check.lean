/-
Release check for T2438 (dispatcher V3, Mon Oct 12 01:42 UTC 2026; DECISIONS §246).  BA-TL TL2a3: clause (iii) of T2428 4 (b), the martingale
tail of `twMart` with the QV `twEEk` (`BATwistGridTail`).  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2438-check.lean
-/
import RBM3D.BA.TwistGrid2
import RBM3D.BA.TwistGrid
import RBM3D.BA.TwistPins
import RBM3D.BA.Step2BA
import RBM3D.BA.FlowPins
import RBM3D.Defs.Sizes
import RBM3D.Path.DifREP1
import RBM3D.Path.DifREP2
import RBM3D.Path.StepDecomp
import RBM3D.Path.Markov
import RBM3D.Path.Walk
import RBM3D.Induction.StepDecompN
import RBM3D.Induction.QVN
import RBM3D.Gauss.BlockAnderson

-- the pin and its consumer (merged, T2428)
#check @RBM.BA.BATwistGridTail
#check @RBM.BA.BATwistGridRem
#check @RBM.BA.BATwistGridWTail
#check @RBM.BA.BATwistGridMart
#check @RBM.BA.BATwistGridAssemble
#check @RBM.BA.baTwistGridAssemble_holds
-- the vocabulary
#check @RBM.BA.twMart
#check @RBM.BA.twMartInc
#check @RBM.BA.twAk
#check @RBM.BA.twEEk
#check @RBM.BA.twEEM
#check @RBM.BA.twDerM
#check @RBM.BA.twL2M
#check @RBM.BA.twK
#check @RBM.BA.baStep2Mat
#check @RBM.Gauss.PsiI_isHermitian
-- generic one-step split, freeze, variance
#check @RBM.Ind.StepDecompCN_Stmt
#check @RBM.Ind.stepDecompCN
#check @RBM.Ind.stepDecompCN_Z_subG
#check @RBM.Ind.stepDecompCN_Y_sq
#check @RBM.Path.HermTestFun
#check @RBM.Path.condExp_freeze
#check @RBM.Path.linTrVar
#check @RBM.Path.pathH_isHermitian
#check @RBM.Path.pathP
#check @RBM.Path.filt
-- the band twin (DifREP2): model-free pieces and the loop-specific ones to be re-proved
#check @RBM.Ind.GridRepTailNAt
#check @RBM.Ind.gridRepTailN_holds
#check @RBM.Ind.azumaRandProxy_max
#check @RBM.Ind.difRep2_peel
#check @RBM.Ind.difRep2_peel_N
#check @RBM.Ind.difRepTail_condMGF_Z
#check @RBM.Ind.difRep2_norm_STeeM_le_N
#check @RBM.Ind.difRep2_eeShiftErrN_le
#check @RBM.Ind.difRep2_eeShift_sum_le
#check @RBM.Ind.qvPropagatedN
-- the instance datum
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.t0_sz0

namespace RBM.BA.T2438Check
/-- Target 1 as a Prop value (every `d`). -/
example : Prop := ∀ d : ℕ, RBM.BA.BATwistGridTail d
/-- The band twin's shape (every `d`). -/
example : Prop := ∀ d m : ℕ, 2 ≤ m → RBM.Ind.GridRepTailNAt d m
end RBM.BA.T2438Check
