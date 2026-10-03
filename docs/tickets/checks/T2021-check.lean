/-
Release check for T2021 (dispatcher V1, Sat Oct  3 03:36 UTC 2026; CLAUDE.md §4 step 0).
`#check` only: no proofs, no `sorry`.  Never imported or merged.
MD-5 ports `RBM2D/Path/{Markov,Stop,Azuma}.lean` at `c9a24cf` (class a); this file checks that the merged
declarations the port builds on exist on `main` (MD-4 = T2018 merged ddf5f74; `Gauss/LinearForm.lean` from T2006).
Run from the main worktree: `lake env lean docs/tickets/checks/T2021-check.lean`.
-/
import RBM3D

#check @RBM.Path.PathΩ
#check @RBM.Path.pathP
#check @RBM.Path.filt
#check @RBM.Path.pathH
#check @RBM.Path.measurable_pathH
#check @RBM.Path.pathH_adapted
#check @RBM.Path.indepIncr
#check @RBM.Path.transferLaw
#check @RBM.Gauss.Sizes.SeqCoord
#check @RBM.Gauss.Sizes.seqXmat
