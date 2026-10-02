/-
Release check for T2005 (dispatcher V1, Fri Oct  2 19:21 UTC 2026; CLAUDE.md §4 step 0).
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2005-check.lean`.
-/
import RBM3D

#check @RBM.msc
#check @RBM.msc_mul
#check @RBM.msc_im_pos
#check @RBM.norm_msc_lt_one
#check @RBM.mscDisc_sq

namespace RBM.T2005Check

open RBM

/-- The pin of T2005: `(eq:defmzsc)`, 1_2:337–340. -/
def Stmt : Prop :=
  ∀ {z : ℂ}, 0 < z.im →
    msc z = ∫ x in (-2 : ℝ)..2,
      ((Real.sqrt (4 - x ^ 2) / (2 * Real.pi) : ℝ) : ℂ) / ((x : ℂ) - z)

end RBM.T2005Check
