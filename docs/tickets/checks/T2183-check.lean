/-
Release check for T2183 (dispatcher V1, Mon Oct  5 06:18 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
UN-02b (Step1Cond): the merged UN ports it builds on (Pins T2174, GUEInvariance T2175, OU and EigenMeasurable T2177);
this file checks that they exist on `main`.  `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2183-check.lean`.
-/
import RBM3D

#check @RBM.Univ.gueP
#check @RBM.Univ.kPoint
#check @RBM.Univ.ouMat
#check @RBM.Univ.gueP_map_unitary_conj
#check @RBM.Univ.ouSample
#check @RBM.Univ.ouSample_law
#check @RBM.Univ.ouMat_zero_map
#check @RBM.Univ.measurable_corrSum
#check @RBM.Univ.measurable_kPoint_eigenvalues
#check @RBM.Univ.UNInst.bump
