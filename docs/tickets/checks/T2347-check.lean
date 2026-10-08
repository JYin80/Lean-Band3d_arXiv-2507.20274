/-
Release check for T2347 (dispatcher V1, Thu Oct 8 21:53 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §157, §145, §91 (1)).
UN-43: `RBM3D/Universality/GUEPhase/EntryGrid.lean`, port of RBM2D `Universality/GUEPhase/EntryGrid.lean`
(902 lines, HEAD 9e0f275): the one-time law of the grid path (`map_gueH_eq_mixMat`) and Lemma 4.1 on the grid
(`gueGrid_entry_bound`); the mixed-grid machinery is **reused** from `GUEPhase/Grid.lean` (keyword `private` deleted there).
Section 1: merged names (`main` 5d0b6da).  `#check` only; the targets are listed in the ticket (statements = source + port map,
translation table in the prove report).  Run: `lake env lean docs/tickets/checks/T2347-check.lean`.
-/
import RBM3D.Universality.GUEPhase.EntryTailMain
import RBM3D.Universality.GUEPhase.Proc

/-! ## 1. Merged names -/

#check @RBM.Univ.gueEntryMix                      -- GUEPhase/EntryTailMain.lean:545 (Lemma 4.1 at the mixture profile)
#check @RBM.Univ.GUEEntryMix                      -- GUEPhase/EntryTail.lean:94
#check @RBM.Univ.mixMat                           -- GUEPhase/EntryTail.lean:54
#check @RBM.Univ.ouP                              -- Universality/Pins.lean:145
#check @RBM.Univ.GUEPhase.Pgue                    -- GUEPhase/Grid.lean:61
#check @RBM.Univ.GUEPhase.gueH                    -- GUEPhase/Grid.lean:77
#check @RBM.Univ.GUEPhase.gueUnit                 -- GUEPhase/Grid.lean:52
#check @RBM.Univ.GUEPhase.gueUnitVar              -- GUEPhase/Grid.lean:49
#check @RBM.Univ.GUEPhase.gueLmax                 -- GUEPhase/Proc.lean:93
#check @RBM.Univ.GUEPhase.gueDev                  -- GUEPhase/Proc.lean:83
#check @RBM.Green.llErrMat                        -- Green/Pins.lean:73
#check @RBM.Green.maxLoopPM                       -- Green/Pins.lean:94
#check @RBM.Green.loopPM                          -- Green/Pins.lean:78
#check @RBM.Gauss.Sizes.Admissible                -- Defs/Sizes.lean:177
#check @RBM.Gauss.Sizes.seqXmat                   -- Gauss/FineModel.lean:218
#check @RBM.Path.gridTime                         -- Path/Walk.lean:70
#check @RBM.Path.gridStep                         -- Path/Walk.lean:67
#check @RBM.Path.PathΩ                            -- Path/Walk.lean:54
