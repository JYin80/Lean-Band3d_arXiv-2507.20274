/-
Release check for T2350 (dispatcher V1, Thu Oct 8 22:52 UTC 2026; DECISIONS §158).  UN-44: port of RBM2D `GUEPhase/Eq729A.lean`.
Merged names (`main` f9f498d).  Run: `lake env lean docs/tickets/checks/T2350-check.lean`.
-/
import RBM3D.Universality.GUEPhase.Drift

#check @RBM.Univ.GUEPhase.condExp_loop_drift_gue    -- Drift (T2343)
#check @RBM.Univ.GUEPhase.oneStepEnvelopeGUE        -- Drift (T2343)
#check @RBM.Univ.GUEPhase.primBilGUE                -- Bootstrap.lean:173
#check @RBM.Univ.GUEPhase.primRhsGUE                -- Bootstrap.lean:178
#check @RBM.Univ.GUEPhase.SBgue                     -- Bootstrap.lean:54
#check @RBM.Univ.GUEPhase.egtNGUE                   -- Generator.lean:97
#check @RBM.Univ.GUEPhase.genMatGUE                 -- Generator.lean:89
#check @RBM.Univ.GUEPhase.loopGenGUE                -- Generator.lean:1229
#check @RBM.Univ.GUEPhase.gueH                      -- Grid.lean:77
#check @RBM.Univ.GUEPhase.Pgue                      -- Grid.lean:61
#check @RBM.Path.envConst                           -- Path/OneStep.lean:78
#check @RBM.Path.gridTime                           -- Path/Walk.lean:70
#check @RBM.Path.gridStep                           -- Path/Walk.lean:67
#check @RBM.zt                                      -- Defs/Semicircle.lean:179
