/-
Release check for T2335 (dispatcher V1, Thu Oct  8 12:52 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §148, §146 (supervisor 1048 C1, C3, O1, O4)).
BA-P4b (BA stage P, row 2 of 6): `RBM3D/BA/KHeatTail.lean`: regime (i) `τ ≤ L²` of the heat kernel `kBA` (P4a, T2331 merged
8a6c908): `kBA_le`, the verbatim twin of `kProd_le` (`HeatProduct.lean:439`) with `kProd d L τ ↦ kBA d L g E m τ`, proved by the
centered lift of the torus kernel, a coordinate Chernoff bound from `BAK_exp_moment_le`, and the semigroup combination.
Section 1: merged names (`main` 8a6c908).  Section 2: the target statement.  Statements and `#check` only.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2335-check.lean`.
-/
import RBM3D.BA.KHeat

/-! ## 1. Merged names -/

#check @RBM.BA.BAP                      -- BA/KHeat.lean:50
#check @RBM.BA.kBA                      -- BA/KHeat.lean:54
#check @RBM.BA.BAP_nonneg               -- BA/KHeat.lean:90
#check @RBM.BA.BAP_row_sum              -- BA/KHeat.lean:97
#check @RBM.BA.BAP_shift                -- BA/KHeat.lean:118
#check @RBM.BA.BAP_neg                  -- BA/KHeat.lean:129
#check @RBM.BA.kBA_fourier              -- BA/KHeat.lean:355
#check @RBM.BA.kBA_basic                -- BA/KHeat.lean:387
#check @RBM.BA.BAP_semigroup_shift      -- BA/KHeat.lean:411
#check @RBM.BA.kBA_gap                  -- BA/KHeat.lean:989
#check @RBM.BA.kBA_diag_le              -- BA/KHeat.lean:1221
#check @RBM.BA.BAK_exp_moment_le        -- BA/KKernel.lean:228
#check @RBM.BA.BAK_off_le               -- BA/KKernel.lean:198
#check @RBM.BA.BAK_zero_neg             -- BA/KKernel.lean:70
#check @RBM.BA.BAK_second_moment        -- BA/KSymbol.lean:700
#check @RBM.BA.BAct_rate                -- BA/CombesThomas.lean:45
#check @RBM.Heat.kProd_le               -- Propagator/HeatProduct.lean:439 (the statement to twin)
#check @RBM.zdistD                      -- Defs/Lattice.lean:71

noncomputable section

namespace RBM.BA.T2335Check

open RBM RBM.Gauss

/-- **Regime (i) `τ ≤ L²`** (twin of `kProd_le`, verbatim with `kProd d L τ ↦ kBA d L g E m τ`; supervisor 1048 C1 (i), O1):
no floor `L^{-d}`, Gaussian-then-exponential decay in the torus `ℓ¹` distance `zdistD`. -/
def T2335_kBA_le : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 → ∀ a : Zd d L,
        kBA d L g E m τ a ≤ C * min 1 (τ ^ (-(d : ℝ) / 2))
          * Real.exp (-c * min ((zdistD d L a : ℝ) ^ 2 / τ) (zdistD d L a : ℝ))

example : Prop := T2335_kBA_le

end RBM.BA.T2335Check

end
