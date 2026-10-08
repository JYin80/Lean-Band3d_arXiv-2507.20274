/-
Release check for T2349 (dispatcher V1, Thu Oct 8 22:52 UTC 2026; DECISIONS §158).  UN-38: port of RBM2D `GUEPhase/DuhamelB.lean`.
Merged names (`main` f9f498d).  Run: `lake env lean docs/tickets/checks/T2349-check.lean`.
-/
import RBM3D.Universality.GUEPhase.DuhamelA1
import RBM3D.Universality.GUEPhase.DuhamelA2
import RBM3D.Universality.GUEPhase.Markov
import RBM3D.Path.Azuma
import RBM3D.Path.Stop
import RBM3D.Induction.LoopC2N

#check @RBM.Univ.GUEPhase.Duhamel_vGue_gradMat_le   -- DuhamelA1.lean:926 (T2345)
#check @RBM.Univ.GUEPhase.Duhamel_loopMax_le_crude  -- DuhamelA1 (T2345)
#check @RBM.Univ.GUEPhase.Duhamel_loopMax_shift_le  -- DuhamelA1 (T2345)
#check @RBM.Univ.GUEPhase.DuhamelGood               -- DuhamelA2.lean:166 (T2346)
#check @RBM.Univ.GUEPhase.DuhamelT                  -- DuhamelA2.lean:180
#check @RBM.Univ.GUEPhase.DuhamelB                  -- DuhamelA2.lean:185
#check @RBM.Univ.GUEPhase.Duhamel_norm_T_le         -- DuhamelA2.lean:594
#check @RBM.Univ.GUEPhase.gueH_succ                 -- Drift (T2343)
#check @RBM.Univ.GUEPhase.gueHasCondSubgaussianMGF_of_frozen -- Markov.lean:184
#check @RBM.Ind.hermTestFunLoopN                    -- Induction/LoopC2N.lean:469
#check @RBM.Path.HermTestFun                        -- Path/StepDecomp.lean:186
