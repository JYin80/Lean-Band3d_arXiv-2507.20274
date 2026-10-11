/-
Release check for T2421 (dispatcher V2, Sun Oct 11 10:28 UTC 2026; DECISIONS §234).  BA-TL TL0: the pins file of stage TL
(supervisor 0853 TL-C2, TL-C3).  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2421-check.lean
-/
import RBM3D.BA.LWPinsBA
import RBM3D.BA.GreenSchur
import RBM3D.BA.EKPins
import RBM3D.Induction.Step1Setup
import RBM3D.Kernel.Evolution
import RBM3D.Induction.DecayLoopA
import RBM3D.Induction.MainIndChain

#check @RBM.BA.baFMz
#check @RBM.BA.FlowFM.GM
#check @RBM.BA.BAuKer
#check @RBM.BA.BAEKSameRow
#check @RBM.BA.baEKSameRow_holds
#check @RBM.BA.STLKgL
#check @RBM.BA.STLmaxgL
#check @RBM.BA.LWAvgLawgL
#check @RBM.BA.STG0M
#check @RBM.BA.STHorizonG
#check @RBM.BA.BAMss
#check @RBM.BA.BATheta
