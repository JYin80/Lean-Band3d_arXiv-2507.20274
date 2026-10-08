/-
Release check for T2331 (dispatcher V1, Thu Oct  8 11:00 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §146, §144).
BA-P4a (BA stage P, first row; supervisor 2026-10-08-1048 PASS with C1–C5): `RBM3D/BA/KHeat.lean`, the Poisson
semigroup `P_s = e^{-s} Σ_n sⁿ/n! Kⁿ` of the kernel `K = BAK` (`= M^{(+,-)}`), its heat kernel in diffusive time
`kBA τ = P_{τ/g²}(0, ·)`, the Laplace identity for `Θ^{(+,-)}` (twin of `Theta_eq_laplace_prod`), the Fourier form,
the torus on-diagonal bound, and regime (ii) `τ ≥ L²` (twin of `kProd_gap`, statement verbatim with `kProd ↦ kBA`).
Section 1: merged names (exact namespaces; `main` c99e133).  Section 2: the two definitions (copied verbatim into
`RBM.BA`) and the target statements.  Statements, definitions and `#check` only.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2331-check.lean`.
-/
import RBM3D.BA.KSymbol
import RBM3D.Propagator.HeatProduct

/-! ## 1. Merged names -/

#check @RBM.BA.BAK                         -- BA/KKernel.lean:48
#check @RBM.BA.BAK_apply                   -- BA/KKernel.lean:51
#check @RBM.BA.BAK_nonneg                  -- BA/KKernel.lean:54
#check @RBM.BA.BAK_symm                    -- BA/KKernel.lean:57
#check @RBM.BA.BAK_shift                   -- BA/KKernel.lean:66
#check @RBM.BA.BAK_zero_neg                -- BA/KKernel.lean:70
#check @RBM.BA.BATheta_pm_eq               -- BA/KKernel.lean:107
#check @RBM.BA.BAK_row_sum                 -- BA/KKernel.lean:124
#check @RBM.BA.BAK_col_sum                 -- BA/KKernel.lean:128
#check @RBM.BA.BAK_pow_nonneg              -- BA/KKernel.lean:149
#check @RBM.BA.BAK_pow_row_sum             -- BA/KKernel.lean:158
#check @RBM.BA.BAK_pow_shift               -- BA/KKernel.lean:176
#check @RBM.BA.BAK_off_le                  -- BA/KKernel.lean:198
#check @RBM.BA.BAK_exp_moment_le           -- BA/KKernel.lean:228
#check @RBM.BA.BAKhat                      -- BA/KSymbol.lean:478
#check @RBM.BA.BAthetaSq                   -- BA/KSymbol.lean:483
#check @RBM.BA.BAKhat_eq                   -- BA/KSymbol.lean:543
#check @RBM.BA.BAK_lazy                    -- BA/KSymbol.lean:567
#check @RBM.BA.BAK_gap                     -- BA/KSymbol.lean:642
#check @RBM.BA.BAK_second_moment           -- BA/KSymbol.lean:700
#check @RBM.BA.BAK_dir_ge                  -- BA/KSymbol.lean:460
#check @RBM.BA.BATheta                     -- BA/MFixedPoint.lean:515
#check @RBM.BA.BASelf                      -- BA/MFixedPoint.lean:193
#check @RBM.BA.BAReal                      -- BA/MFixedPoint.lean:432
#check @RBM.PropThetaQ                     -- Propagator/Pins.lean:214
#check @RBM.Heat.kProd                     -- Propagator/HeatProduct.lean:270 (the band twin)
#check @RBM.Heat.kProd_gap                 -- Propagator/HeatProduct.lean:626 (the statement to twin)
#check @RBM.Heat.kProd_le                  -- Propagator/HeatProduct.lean:439 (P4b's twin, not this ticket)
#check @RBM.Heat.Theta_eq_laplace_prod     -- Propagator/HeatProduct.lean:1171 (the identity to twin)
#check @RBM.Heat.hkT_gap                   -- Propagator/HeatTorus1D.lean:608

noncomputable section

namespace RBM.BA.T2331Check

open RBM RBM.Gauss MeasureTheory Set

/-! ## 2. Definitions (copied verbatim into `RBM.BA`) and target statements -/

section Defs

variable (d L : ℕ) [NeZero L]

/-- The Poisson semigroup of `K` (supervisor 1048 C2): `P_s = e^{-s} Σ_n sⁿ/n! Kⁿ`, entrywise. -/
def BAP (g E : ℝ) (m : ℂ) (s : ℝ) (a b : Zd d L) : ℝ :=
  Real.exp (-s) * ∑' n : ℕ, s ^ n / (n.factorial : ℝ) * (BAK d L g E m ^ n) a b

/-- The heat kernel of `K` in diffusive time `τ = g² s`: `kBA τ a = P_{τ/g²}(0, a)`. -/
def kBA (g E : ℝ) (m : ℂ) (τ : ℝ) (a : Zd d L) : ℝ :=
  BAP d L g E m (τ / g ^ 2) 0 a

end Defs

/-- **Laplace identity** (twin of `Theta_eq_laplace_prod`; `Θ = Σ tⁿ Kⁿ = ∫₀^∞ e^{-(1-t)u} P_{tu} du`, diffusive time
`τ = t g² u`). -/
def T2331_BATheta_eq_laplace_kBA : Prop :=
  ∀ (d L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ) (t : ℝ), 0 < g → BASelf d L g (E : ℂ) m →
    0 ≤ t → t < 1 → ∀ a : Zd d L,
      BATheta d L g E m t true false 0 a =
        ((∫ u in Ioi (0 : ℝ), Real.exp (-(1 - t) * u) * kBA d L g E m (t * g ^ 2 * u) a : ℝ) : ℂ)

/-- **Semigroup and translation invariance** of `P_s`. -/
def T2331_BAP_semigroup_shift : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ), BASelf d L g (E : ℂ) m →
    (∀ s s' : ℝ, 0 ≤ s → 0 ≤ s' → ∀ a b : Zd d L,
      BAP d L g E m (s + s') a b = ∑ c : Zd d L, BAP d L g E m s a c * BAP d L g E m s' c b) ∧
    (∀ s : ℝ, ∀ a b : Zd d L, BAP d L g E m s a b = BAP d L g E m s 0 (b - a))

/-- **Basic properties** of `kBA`: nonnegative, mass one, at most one, `δ` at `τ = 0`, even, continuous in `τ`. -/
def T2331_kBA_basic : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ), 0 < g → BASelf d L g (E : ℂ) m →
    (∀ τ : ℝ, 0 ≤ τ → ∀ a : Zd d L, 0 ≤ kBA d L g E m τ a) ∧
    (∀ τ : ℝ, 0 ≤ τ → ∑ a : Zd d L, kBA d L g E m τ a = 1) ∧
    (∀ τ : ℝ, 0 ≤ τ → ∀ a : Zd d L, kBA d L g E m τ a ≤ 1) ∧
    (∀ a : Zd d L, kBA d L g E m 0 a = if a = 0 then 1 else 0) ∧
    (∀ τ : ℝ, ∀ a : Zd d L, kBA d L g E m τ (-a) = kBA d L g E m τ a) ∧
    (∀ a : Zd d L, Continuous fun τ : ℝ => kBA d L g E m τ a)

/-- **Fourier form** on the torus (finite sums; `θ_k = 2π k / L`, symbol `BAKhat`). -/
def T2331_kBA_fourier : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ), 0 < g → ∀ (τ : ℝ) (a : Zd d L),
    kBA d L g E m τ a = (((L : ℝ) ^ d)⁻¹) * ∑ k : Zd d L,
      Real.exp (-(τ / g ^ 2) * (1 - BAKhat d L g E m k)) *
        Real.cos (2 * Real.pi / L * ∑ j, ((k j).val : ℝ) * ((a j).val : ℝ))

/-- **Torus on-diagonal bound** (from `BAK_gap` and the 1D sums; the floor `L^{-d}` is harmless in regime (i)). -/
def T2331_kBA_diag_le : Prop :=
  ∀ d : ℕ, 0 < d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ τ : ℝ, 0 < τ → ∀ a : Zd d L,
        kBA d L g E m τ a ≤ C * (min 1 (τ ^ (-(d : ℝ) / 2)) + ((L : ℝ) ^ d)⁻¹)

/-- **Regime (ii) `τ ≥ L²`** (twin of `kProd_gap`, `HeatProduct.lean:626`, verbatim with `kProd d L τ ↦ kBA d L g E m τ`;
supervisor 1048 C1 (ii), O1). -/
def T2331_kBA_gap : Prop :=
  ∀ d : ℕ, 0 < d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ τ : ℝ, (L : ℝ) ^ 2 ≤ τ → ∀ (a : Zd d L) (i j : Fin d),
        |kBA d L g E m τ a - ((L : ℝ) ^ d)⁻¹| ≤ C * ((L : ℝ) ^ d)⁻¹ * Real.exp (-c * τ / (L : ℝ) ^ 2) ∧
        |kBA d L g E m τ (a + Pi.single j 1) - kBA d L g E m τ a|
          ≤ C * ((L : ℝ) ^ (d + 1))⁻¹ * Real.exp (-c * τ / (L : ℝ) ^ 2) ∧
        |kBA d L g E m τ (a + Pi.single i 1 + Pi.single j 1) - kBA d L g E m τ (a + Pi.single i 1)
            - kBA d L g E m τ (a + Pi.single j 1) + kBA d L g E m τ a|
          ≤ C * ((L : ℝ) ^ (d + 2))⁻¹ * Real.exp (-c * τ / (L : ℝ) ^ 2)

example : Prop := T2331_kBA_gap

end RBM.BA.T2331Check

end
