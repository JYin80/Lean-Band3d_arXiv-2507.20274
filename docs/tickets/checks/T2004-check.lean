/-
Release check for T2004 (dispatcher V1, Fri Oct  2 17:26 UTC 2026; CLAUDE.md §4 step 0, DECISIONS §3–§7).
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2004-check.lean`.
-/
import RBM3D

-- the RBM3D loop vocabulary on `main`
#check @RBM.Loop.LoopIdx
#check @RBM.Loop.LoopIdx.cutGlueL
#check @RBM.Loop.LoopIdx.cutGlueR
#check @RBM.Loop.treeEqRhs
#check @RBM.Loop.MLoop
#check @RBM.Loop.IsKLoop
#check @RBM.Loop.TwoLoopBounded
#check @RBM.Loop.TSP
#check @RBM.Loop.GammaSum
-- the two old-mode `Prop` hypotheses to be retired (item 2)
#check @RBM.Loop.KTreeRep
#check @RBM.Loop.KLoopBound
-- merged results on 2- and 3-loops
#check @RBM.Loop.kTwo
#check @RBM.Loop.kThree
#check @RBM.Loop.isKLoop_unique
#check @RBM.Loop.kTwoFormula_of_isKLoop
#check @RBM.Loop.KTwoFormula
#check @RBM.Loop.pureLoop_two
#check @RBM.Loop.pureLoop_three
-- the propagator objects the `𝒦`-formulas use
#check @RBM.Theta
#check @RBM.Bparam
#check @RBM.ellT
