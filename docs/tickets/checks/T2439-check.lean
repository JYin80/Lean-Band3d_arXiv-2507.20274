/-
Release check for T2439 (dispatcher V3, Mon Oct 12 01:42 UTC 2026; DECISIONS §246).  BA-TL TL2a4: clause (iv) of T2428 4 (b), the
`Ũ`-weighted martingale tail with the weighted QV `twEEUk` (`BATwistGridWTail`).  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2439-check.lean
-/
import RBM3D.BA.TwistGrid2
import RBM3D.BA.TwistGrid
import RBM3D.BA.TwistPins
import RBM3D.BA.EKPins
import RBM3D.BA.KBase
import RBM3D.BA.KKernel
import RBM3D.BA.FlowPins
import RBM3D.Defs.Sizes
import RBM3D.Path.DifREP1
import RBM3D.Path.DifREP2
import RBM3D.Path.DifREP3
import RBM3D.Induction.StepDecompN

-- the pin and its consumer (merged, T2428)
#check @RBM.BA.BATwistGridWTail
#check @RBM.BA.BATwistGridRem
#check @RBM.BA.BATwistGridTail
#check @RBM.BA.BATwistGridMart
#check @RBM.BA.BATwistGridAssemble
#check @RBM.BA.baTwistGridAssemble_holds
-- the vocabulary
#check @RBM.BA.twMart
#check @RBM.BA.twEEUk
#check @RBM.BA.twEEUM
#check @RBM.BA.twEEM
#check @RBM.BA.twU
#check @RBM.BA.BAuKer
-- the kernel facts (every `d`)
#check @RBM.BA.BAuKer_self
#check @RBM.BA.BAuKer_comp
#check @RBM.BA.BAuKerSemigroup_holds
#check @RBM.BA.BAuKer_eq_one_add
#check @RBM.BA.EKPins_norm_Q_le
#check @RBM.BA.EKPins_norm_Theta_le
#check @RBM.BA.EKPins_norm_uKer_le
#check @RBM.BA.BATheta_conj
#check @RBM.BA.BAMss_pm_eq
#check @RBM.BA.BAMss_mp_eq
#check @RBM.BA.BATheta_pm_eq
-- not used (carries `3 ≤ d`)
#check @RBM.BA.BATwKerA
-- generic one-step split and the band twin (DifREP3, DifREP2)
#check @RBM.Ind.stepDecompCN
#check @RBM.Ind.difRep2_peel_N
#check @RBM.Ind.difRepTail_condMGF_Z
#check @RBM.Ind.GridRepWTailNAt
#check @RBM.Ind.gridRepWTailN_holds
#check @RBM.Ind.gridRepWTailQN_holds
#check @RBM.Ind.difRep3_UN_transfer
#check @RBM.Ind.uKerQ
-- the instance datum
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.t0_sz0

namespace RBM.BA.T2439Check
/-- Target 1 as a Prop value (every `d`). -/
example : Prop := ∀ d : ℕ, RBM.BA.BATwistGridWTail d
/-- The band twin's shape (every `d`). -/
example : Prop := ∀ d m : ℕ, 2 ≤ m → RBM.Ind.GridRepWTailNAt d m
end RBM.BA.T2439Check
