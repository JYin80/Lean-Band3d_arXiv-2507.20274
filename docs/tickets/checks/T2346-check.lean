/-
Release check for T2346 (dispatcher V1, Thu Oct 8 20:54 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §155, §145, §91 (1)).
UN-37: `RBM3D/Universality/GUEPhase/DuhamelA2.lean`, port of RBM2D `Universality/GUEPhase/DuhamelA.lean` §5–§7
(lines 1041–1985 at RBM2D HEAD 9e0f275): one step (linear part, Taylor remainder, truncation), the truncation bias, the grid
facts and the drift remainder.  Independent of T2345 (UN-36) except `Duhamel_contDiffAt_loop`, re-derived here.
Section 1: merged names.  The targets are the public declarations listed in the ticket (statements = source + port map;
the auditor checks the translation table).  Run (after T2343 is merged): `lake env lean docs/tickets/checks/T2346-check.lean`.
-/
import RBM3D.Universality.GUEPhase.Drift
import RBM3D.Path.StepDecomp
import RBM3D.Induction.Split
import RBM3D.Induction.LoopC2N

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.LinearForm RBM.Path RBM.Univ RBM.Loop
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-! ## 1. Merged names -/

#check @RBM.Univ.GUEPhase.oneStepEnvelopeGUE     -- GUEPhase/Drift.lean (T2343)
#check @RBM.Univ.GUEPhase.condExp_loop_drift_gue  -- GUEPhase/Drift.lean (T2343)
#check @RBM.Univ.GUEPhase.gueH_succ               -- GUEPhase/Drift.lean (T2343)
#check @RBM.Univ.GUEPhase.vGue                    -- GUEPhase/Markov.lean:291
#check @RBM.Univ.GUEPhase.gueUnitVar              -- GUEPhase/Grid.lean:49
#check @RBM.Univ.GUEPhase.gueH                    -- GUEPhase/Grid.lean:77
#check @RBM.Univ.GUEPhase.Pgue                    -- GUEPhase/Grid.lean:61
#check @RBM.Path.linTr                            -- Path/Markov.lean:134
#check @RBM.Path.gradMat                          -- Path/StepDecomp.lean:80
#check @RBM.Path.fderiv_eq_trace_gradMat          -- Path/StepDecomp.lean:123
#check @RBM.Path.HermTestFun                      -- Path/StepDecomp.lean:186
#check @RBM.Ind.loopMax                           -- Induction/Split.lean:515
#check @RBM.Ind.loopMax_le                        -- Induction/Split.lean:533
#check @RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero -- Induction/ConArgDet.lean:380
#check @RBM.green_sub_green                       -- Induction/ConArgDet.lean:73
#check @RBM.green                                 -- Green/EntryCore.lean:34
#check @RBM.Gauss.loopL                           -- Loop/GLoopFlow.lean:123
#check @RBM.Gauss.blockMat                        -- Loop/GLoopFlow.lean:105
#check @RBM.Gauss.gloopProd                       -- Loop/GLoopFlow.lean:384
#check @RBM.Gauss.Gres                            -- Loop/GLoopFlow.lean:74
#check @RBM.Gauss.Eblk                            -- Loop/GLoop.lean:55
#check @RBM.Gauss.Vtx                             -- Gauss/Model.lean:60
#check @RBM.Gauss.coordinateMatrix                -- Gauss/FineModel.lean:384
#check @RBM.Gauss.Sizes.seqXmat                   -- Gauss/FineModel.lean:218
#check @RBM.Gauss.Sizes.seqHflow                  -- Gauss/FineModel.lean:225
#check @RBM.Gauss.LinearForm.linVar               -- Gauss/LinearForm.lean:130
#check @RBM.Univ.GUEPhase.gue_highProb_incr_le   -- GUEPhase/Markov.lean:863 (the truncation event)
#check @RBM.Path.envConst                         -- Path/OneStep.lean:78
#check @RBM.Path.filt                             -- Path/Walk.lean:62
#check @RBM.Path.gridTime                         -- Path/Walk.lean:70
#check @RBM.Path.gridStep                         -- Path/Walk.lean:67
