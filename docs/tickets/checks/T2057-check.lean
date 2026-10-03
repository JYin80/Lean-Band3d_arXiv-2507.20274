/-
Release check for T2057 (dispatcher V1, Sat Oct  3 13:10 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19, §22).
`#check` only: no proofs, no `sorry`.  Never imported or merged.
S1-16 ports RBM2D `Green/EntryBlock.lean` and `Green/EntryDom.lean` onto the merged MD layer and the merged ST-1 files;
this file checks that the names it builds on exist.  (`RBM3D/Induction/PerTimeCalc.lean` comes with T2045; the ticket
starts only after it merges.)
Run from the main worktree: `lake env lean docs/tickets/checks/T2057-check.lean`.
-/
import RBM3D

#check @RBM.green
#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.seqHflow
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.Bandwidth
#check @RBM.Path.PerTimeDomAt
#check @RBM.Path.TimeIcc
#check @RBM.Green.Kstab3
#check @RBM.Green.eventually_Kstab3_mul_rpow_le
#check @RBM.Green.eventually_stable_svar_bulk
#check @RBM.Green.gexRHS
#check @RBM.Green.maxLoopPM
#check @RBM.Gauss.etaT
