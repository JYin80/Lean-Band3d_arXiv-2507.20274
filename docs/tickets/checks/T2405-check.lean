/-
Release check for T2405 (dispatcher V2, Sun Oct 11 01:35 UTC 2026; DECISIONS §217).  BA-T T3: `lem:newKLK` over the carrier
(layout (A): new `Chain/NewKLKGen.lean`; (B): `Induction/NewKLK.lean` in place).  G1: the band pins below stay unchanged; the
auditor adds `example : <statement> := <name>` for each.  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2405-check.lean
-/
import RBM3D.Induction.NewKLK
import RBM3D.Chain.Step2Gen
import RBM3D.Evolution.PropTInf
import RBM3D.BA.KSolve

#check @RBM.Gauss.Sizes.STNewKLK
#check @RBM.Gauss.Sizes.STNewKLKAt
#check @RBM.Gauss.Sizes.STK2decay
#check @RBM.Gauss.Sizes.stNewKLK_holds
#check @RBM.Gauss.Sizes.stNewKLKAt_holds
#check @RBM.Gauss.Sizes.stK2decay_holds
#check @RBM.BA.STNewKLKAtgL
#check @RBM.BA.STNewKLKgL
#check @RBM.BA.STK2decaygL
#check @RBM.BA.bandStep2_STNewKLKAt
#check @RBM.BA.bandStep2_STNewKLK
#check @RBM.BA.bandStep2_STK2decay
#check @RBM.BA.Step2Mat
#check @RBM.BA.bandStep2Mat
#check @RBM.ekPropTInf_holds
#check @RBM.Loop.KLK_two
#check @RBM.BA.BAKsolve
