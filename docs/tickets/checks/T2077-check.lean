/-
Release check for T2077 (dispatcher V1, Sat Oct  3 21:59 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S1-06: ports RBM2D loop-generator files at `c9a24cf` onto the merged MD layer and S1-03/04/05; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2077-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.expected_samplewise_loop_flow_derivative
#check @RBM.Gauss.loop_flow_derivative_actual_coordinate_chain
#check @RBM.Gauss.sum_twoEdge_mixed_deriv
#check @RBM.prop5to8_holds
#check @RBM.prop5Short_holds
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.svarF
