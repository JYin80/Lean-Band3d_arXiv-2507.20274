/-
Release check for T2392 (dispatcher V2, Sat Oct 10 21:20 UTC 2026; DECISIONS §205).  BA-E2: the owed stage-E pins
`BAEKSumDecay1`, `BAEKSumDecayNAL`, `BAEKSumDecay2` (new `BA/EKSum.lean`).  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2392-check.lean
-/
import RBM3D.BA.EKPins
import RBM3D.BA.Prop6Path
import RBM3D.Evolution.SumDecay
import RBM3D.Evolution.SumDecayZero

#check @RBM.BA.BAEKSumDecay1
#check @RBM.BA.BAEKSumDecayNAL
#check @RBM.BA.BAEKSumDecay2
#check @RBM.BA.BAUN
#check @RBM.BA.BAXi
#check @RBM.BA.baEKXiDecay_holds
#check @RBM.BA.baEKXiBall_holds
#check @RBM.BA.baEKSameRow_holds
#check @RBM.BA.baEKSumNdecay_holds
#check @RBM.BA.baProp5s_holds
#check @RBM.BA.baProp6_holds
#check @RBM.ekSumDecay1_holds
#check @RBM.ekSumDecayNAL_holds
#check @RBM.ekSumDecay2_holds
