/-
Release check for T2174 (dispatcher V1, Mon Oct  5 03:38 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
UN-01: promote the UN-D1 probe (`t/T2162` at 73b451c) to `RBM3D/Universality/Pins.lean`: the merged modules and
names the probe builds on; this file checks that they exist on `main`.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2174-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.Hmat
#check @RBM.Gauss.Xmat
#check @RBM.Gauss.Gres
#check @RBM.mE
#check @RBM.msc_eq_integral
#check @RBM.Gauss.PsiB
#check @RBM.Gauss.Sizes.seqHBA
#check @RBM.Audit.allowedAxioms
#check @RBM.Audit.borrowedProps
#check @RBM.Audit.owedProps
