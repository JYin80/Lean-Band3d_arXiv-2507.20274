/-
Release check for T2362 (dispatcher V2, Fri Oct 9 20:59 UTC 2026; DECISIONS §168).  BA-K00: BAMLoop in place + the Θ_BA calculus.
Merged names on main.  #check only: no proofs, no sorry.  Run: lake env lean docs/tickets/checks/T2362-check.lean
-/
import RBM3D.BA.FlowPins
import RBM3D.BA.Step1Fam
import RBM3D.BA.KKernel
import RBM3D.Propagator.Basic
import RBM3D.Propagator.Deriv
import RBM3D.Loop.GLoopFlow

#check @RBM.BA.BAMLoop
#check @RBM.BA.BAKsol
#check @RBM.BA.BAKloop
#check @RBM.BA.baFM_eqAt
#check @RBM.BA.BATheta
#check @RBM.BA.BAMss
#check @RBM.BA.BAMsigma
#check @RBM.BA.BAMB
#check @RBM.BA.BAReal
#check @RBM.BA.BATheta_pm_eq
#check @RBM.BA.BAMss_norm_eq_BAK
#check @RBM.PropThetaQ
#check @RBM.Loop.IsKLoopS
#check @RBM.Gauss.loopM
#check @RBM.hasDerivAt_Theta_mul_apply
#check @RBM.sum_Theta_row
