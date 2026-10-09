/-
Release check for T2351 (dispatcher V1, Thu Oct 8 23:52 UTC 2026; DECISIONS §159).  UN-39/40 DuhamelC: port of RBM2D `GUEPhase`.
Merged names (`main` 9c3bfc7).  Run: `lake env lean docs/tickets/checks/T2351-check.lean`.
-/
import RBM3D.Universality.GUEPhase.DuhamelB
import RBM3D.Universality.GUEPhase.Proc
import RBM3D.Induction.PerTimeCalc
import RBM3D.Green.Pins

#check @RBM.Univ.GUEPhase.DuhamelGood
#check @RBM.Univ.GUEPhase.Duhamel_norm_T_le
#check @RBM.Univ.GUEPhase.Duhamel_vGue_gradMat_le
#check @RBM.Univ.GUEPhase.gueStop
#check @RBM.Univ.GUEPhase.gueLmax
#check @RBM.Univ.GUEPhase.gueH
#check @RBM.Univ.GUEPhase.Pgue
#check @RBM.Path.gridTime
#check @RBM.Path.gridStep
