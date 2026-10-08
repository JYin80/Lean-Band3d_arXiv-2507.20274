/-
Release check for T2336 (dispatcher V1, Thu Oct  8 12:52 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §148, §146 (supervisor 1048 C4, O2)).
BA-P4c (BA stage P, row 3 of 6; the risk row): `RBM3D/BA/KHeatDiff.lean`: regime (i) unit first and second differences of the
heat kernel `kBA` (P4a, T2331) with polynomial decay of order `M = ⌊d/2⌋ + 1`, by one-direction summation by parts on the torus
Fourier sum, using the one-direction regularity of the symbol `BAKhat` from `BAK_off_le`.
Section 1: merged names (`main` 8a6c908).  Section 2: the two target statements (dispatcher's form: `max τ 1` in the polynomial
factor, see the ticket).  Statements and `#check` only.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2336-check.lean`.
-/
import RBM3D.BA.KHeat

/-! ## 1. Merged names -/

#check @RBM.BA.kBA                      -- BA/KHeat.lean:54
#check @RBM.BA.kBA_fourier              -- BA/KHeat.lean:355
#check @RBM.BA.kBA_gap                  -- BA/KHeat.lean:989 (regime (ii) differences, done)
#check @RBM.BA.kBA_diag_le              -- BA/KHeat.lean:1221
#check @RBM.BA.BAKhat                   -- BA/KSymbol.lean:478
#check @RBM.BA.BAthetaSq                -- BA/KSymbol.lean:483
#check @RBM.BA.BAKhat_eq                -- BA/KSymbol.lean:543
#check @RBM.BA.BAK_gap                  -- BA/KSymbol.lean:642
#check @RBM.BA.BAK_off_le               -- BA/KKernel.lean:198
#check @RBM.BA.BAK_zero_neg             -- BA/KKernel.lean:70
#check @RBM.Heat.kProd_diff1_le         -- Propagator/HeatProduct.lean:462 (band twin, exponential form)
#check @RBM.Heat.kProd_diff2_le         -- Propagator/HeatProduct.lean:518
#check @RBM.zdistD                      -- Defs/Lattice.lean:71

noncomputable section

namespace RBM.BA.T2336Check

open RBM RBM.Gauss

/-- **Unit first differences, regime (i)**, polynomial decay `M = ⌊d/2⌋ + 1` (supervisor 1048 C4), with `max τ 1` in the decay
factor (for `τ → 0` at fixed `a ≠ 0` the difference is `≍ τ e^{-c|a|}`, which is not `O(τ^M)`). -/
def T2336_kBA_diff1_le : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 → ∀ (a : Zd d L) (j : Fin d),
        |kBA d L g E m τ (a + Pi.single j 1) - kBA d L g E m τ a|
          ≤ C * min 1 (τ ^ (-((d : ℝ) + 1) / 2))
            * (1 + (zdistD d L a : ℝ) ^ 2 / max τ 1) ^ (-(((d / 2 + 1 : ℕ) : ℝ)))

/-- **Unit second differences, regime (i)**, same decay factor, `τ^{-(d+2)/2}`. -/
def T2336_kBA_diff2_le : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 → ∀ (a : Zd d L) (i j : Fin d),
        |kBA d L g E m τ (a + Pi.single i 1 + Pi.single j 1) - kBA d L g E m τ (a + Pi.single i 1)
            - kBA d L g E m τ (a + Pi.single j 1) + kBA d L g E m τ a|
          ≤ C * min 1 (τ ^ (-((d : ℝ) + 2) / 2))
            * (1 + (zdistD d L a : ℝ) ^ 2 / max τ 1) ^ (-(((d / 2 + 1 : ℕ) : ℝ)))

example : Prop := T2336_kBA_diff1_le

end RBM.BA.T2336Check

end
