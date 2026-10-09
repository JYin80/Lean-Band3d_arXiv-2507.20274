/-
Release check for T2353 (dispatcher V1, Thu Oct 8 23:52 UTC 2026; DECISIONS §159).  UN-45/46 OneLoop: port of RBM2D `GUEPhase`.
Merged names (`main` 9c3bfc7).  Run: `lake env lean docs/tickets/checks/T2353-check.lean`.
-/
import RBM3D.Universality.GUEPhase.Grid
import RBM3D.Gauss.SteinMatrix

#check @RBM.Univ.GUEPhase.gueH
#check @RBM.Univ.GUEPhase.Pgue
#check @RBM.Univ.GUEPhase.gueUnit
#check @RBM.Univ.GUEPhase.gueUnitVar
#check @RBM.Gauss.Sizes.seqXmat
#check @RBM.Path.gridTime
#check @RBM.Path.gridStep
#check @RBM.Path.PathΩ
