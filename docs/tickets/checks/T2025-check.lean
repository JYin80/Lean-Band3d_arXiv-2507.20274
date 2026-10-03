/-
Release check for T2025 (dispatcher V1, Sat Oct  3 04:39 UTC 2026; CLAUDE.md §4 step 0).
Pinned `Prop` of KL4: the probe pin `KLuniquePin` (`64b58eb:RBM3D/Probe/T2004Pins.lean` lines 762–768),
verbatim.  Namespace `RBM.Loop.T2025Check` here; the theorem goes to `RBM.Loop`.
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2025-check.lean`.
-/
import RBM3D

#check @RBM.Loop.IsKLoop
#check @RBM.Loop.KLK
#check @RBM.Loop.KLK_isKLoop
#check @RBM.Loop.isKLoop_unique
#check @RBM.Loop.TwoLoopBounded
#check @RBM.Loop.kTwoFormula_of_isKLoop
#check @RBM.Loop.kThree_eq_of_isKLoop
#check @RBM.Loop.LoopIdx.WF
#check @RBM.mSigma

namespace RBM.Loop.T2025Check

open RBM RBM.Loop

/-- **Pin `Def_Ktza`, "unique"**: every family of `K`-loops on `[0,1)` is `KLK` (no a priori
bound on the `2`-loops: it follows from continuity on `[0,t] ⊆ [0,1)`). -/
def KLuniquePin : Prop :=
  ∀ (d L W : ℕ) [NeZero L] (g E : ℝ), 3 ≤ L → 1 ≤ W → |E| < 2 →
    ∀ K : ℝ → LoopIdx (Zd d L) → ℂ, IsKLoop d L W g (mSigma E) (Set.Ico 0 1) K →
      ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ I : LoopIdx (Zd d L), I.WF → 1 ≤ I.length →
        K t I = KLK d L g W E t I

end RBM.Loop.T2025Check
