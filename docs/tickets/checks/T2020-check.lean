/-
Release check for T2020 (dispatcher V1, Sat Oct  3 03:35 UTC 2026; CLAUDE.md §4 step 0).
Pinned `Prop` of KL3: the probe pin `KLisKLoopPin` (`64b58eb:RBM3D/Probe/T2004Pins.lean` lines 755–760),
verbatim.  Namespace `RBM.Loop.T2020Check` here; the theorem goes to `RBM.Loop`.
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2020-check.lean`.
-/
import RBM3D

#check @RBM.mSigma
#check @RBM.Loop.IsKLoop
#check @RBM.Loop.treeEqRhs
#check @RBM.Loop.MLoop
#check @RBM.Loop.KLK
#check @RBM.Loop.KLK_one
#check @RBM.Loop.KLtreeValW
#check @RBM.Loop.KLtreeValG
#check @RBM.Loop.KLtreeValW_cut
#check @RBM.Loop.KLsum_cut
#check @RBM.Loop.KLgval
#check @RBM.hasDerivAt_Theta_mul_apply

namespace RBM.Loop.T2020Check

open RBM RBM.Loop

/-- **Pin `Def_Ktza`** (`(pro_dyncalK)`, `(calGonIND)`, `(eq:initial_K)`, `(eq:KMloop)`): the tree
sum `KLK` solves the convolution tree equations on `t ∈ [0,1)`, takes the `M`-loop value at
`t = 0`, and `𝒦^{(1)} = m(σ)`.  (The paper writes `t ∈ [0,1]`; `Θ_1` does not exist.) -/
def KLisKLoopPin : Prop :=
  ∀ (d L W : ℕ) [NeZero L] (g E : ℝ), 3 ≤ L → 1 ≤ W → |E| < 2 →
    IsKLoop d L W g (mSigma E) (Set.Ico 0 1) (fun t I => KLK d L g W E t I)

end RBM.Loop.T2020Check
