/-
Release check for T2352 (dispatcher V1, Thu Oct 8 23:52 UTC 2026; DECISIONS §159).  UN-48 HypA: port of RBM2D `GUEPhase`.
Merged names (`main` 9c3bfc7).  Run: `lake env lean docs/tickets/checks/T2352-check.lean`.
-/
import RBM3D.Universality.GUEPhase.Proc
import RBM3D.Universality.GUEPhase.EntryTailMain
import RBM3D.Loop.KBound

#check @RBM.Univ.GUEPhase.gueStop
#check @RBM.Univ.GUEPhase.gueLmax
#check @RBM.Univ.GUEPhase.gueDev
#check @RBM.Univ.GUEPhase.primBilGUE
#check @RBM.Univ.GUEPhase.primRhsGUE
#check @RBM.Univ.GUEPhase.egtNGUE
#check @RBM.Univ.GUEPhase.genMatGUE
#check @RBM.Univ.gueEntryMix
#check @RBM.Ind.loopMax
#check @RBM.Path.gridTime
#check @RBM.Path.gridStep
