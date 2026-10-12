/-
Release check for T2437 (dispatcher V3, Mon Oct 12 01:42 UTC 2026; DECISIONS §246).  BA-TL TL2a2: clause (ii) of T2428 4 (b), the grid
remainder bound `‖twRem‖ ≤ N^{C₀} √Δ` (`BATwistGridRem`) through a twisted one-step envelope.  Merged names only.
No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2437-check.lean
-/
import RBM3D.BA.TwistGrid2
import RBM3D.BA.TwistGrid
import RBM3D.BA.TwistPins
import RBM3D.BA.Step2BA
import RBM3D.BA.GreenSchur
import RBM3D.BA.MFixedPoint
import RBM3D.BA.KBase
import RBM3D.BA.EKPins
import RBM3D.BA.FlowPins
import RBM3D.Defs.Sizes
import RBM3D.Path.OneStep
import RBM3D.Path.LoopStep
import RBM3D.Path.Markov
import RBM3D.Path.Walk
import RBM3D.Path.DifREP1
import RBM3D.Gauss.FineModel
import RBM3D.Gauss.FlowCalculus
import RBM3D.Gauss.BlockAnderson
import RBM3D.Induction.GridEnvelopeN

-- the pin, its consumer and clause (i) (merged, T2428)
#check @RBM.BA.BATwistGridRem
#check @RBM.BA.BATwistGridTail
#check @RBM.BA.BATwistGridWTail
#check @RBM.BA.BATwistGridMart
#check @RBM.BA.BATwistGridMartAt
#check @RBM.BA.BATwistGridAssemble
#check @RBM.BA.baTwistGridAssemble_holds
#check @RBM.BA.baTwistGrid_decomp
#check @RBM.BA.baTwistGrid_decomp_ae
-- the vocabulary
#check @RBM.BA.twRem
#check @RBM.BA.twAk
#check @RBM.BA.twDriftk
#check @RBM.BA.twL2M
#check @RBM.BA.twGenM
#check @RBM.BA.twDriftM
#check @RBM.BA.twK
#check @RBM.BA.baStep2Mat
#check @RBM.BA.BATwistHier
#check @RBM.BA.BATwistHier_holds
-- BA inputs
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflow_real
#check @RBM.BA.BAReal
#check @RBM.BA.BAdom
#check @RBM.BA.BAt0_lt_one
#check @RBM.BA.BATheta_hasDerivAt
#check @RBM.BA.BATheta_resolvent
#check @RBM.BA.EKPins_norm_Theta_le
#check @RBM.BA.EKPins_norm_Q_le
#check @RBM.Gauss.PsiI_isHermitian
-- walk, freeze, resolvent bound
#check @RBM.Path.pathP
#check @RBM.Path.filt
#check @RBM.Path.gridStep
#check @RBM.Path.gridTime
#check @RBM.Path.pathH_isHermitian
#check @RBM.Path.pathH_succ
#check @RBM.Path.condExp_freeze
#check @RBM.Path.condExp_loop_step
#check @RBM.Gauss.Sizes.seqP_map_slice
#check @RBM.Gauss.norm_Gsig_le_inv_eta
-- the band twin
#check @RBM.Path.OneStepEnvelope
#check @RBM.Path.oneStepEnvelope
#check @RBM.Path.envConst
#check @RBM.Ind.gridDriftN_envelope
#check @RBM.Ind.GridRepRemNAt
#check @RBM.Ind.gridRepRemN_holds
-- the instance datum
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.t0_sz0

namespace RBM.BA.T2437Check
/-- Target 1 as a Prop value (every `d`; `C₀` per `d`, its value fixed by the 1a). -/
example : Prop := ∀ d : ℕ, ∃ C₀ : ℝ, 0 ≤ C₀ ∧ RBM.BA.BATwistGridRem d C₀
/-- The consumer: with the two other parts, target 1 gives `BATwistGridMart d` (TL2d's corollary of `baTwistGridAssemble_holds`). -/
example : Prop := ∀ d : ℕ, (∃ C₀ : ℝ, 0 ≤ C₀ ∧ RBM.BA.BATwistGridRem d C₀) → RBM.BA.BATwistGridTail d →
  RBM.BA.BATwistGridWTail d → RBM.BA.BATwistGridMart d
/-- The band twin's shape (`3 ≤ d` there only through `stKbound_of_flow`). -/
example : Prop := ∀ d : ℕ, 3 ≤ d → ∀ m : ℕ, 2 ≤ m → RBM.Ind.GridRepRemNAt d m ((m : ℝ) + 9)
end RBM.BA.T2437Check
