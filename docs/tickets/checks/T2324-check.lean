/-
Release check for T2324 (dispatcher V1, Thu Oct  8 04:05 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §136, §135 (2), supervisor
2026-10-08-0344 Q2/O2, D614).
BA-P3 (block Anderson, deterministic layer; T2161 split P.9 row BA-P3 `BA/KSymbol`): the variance lower bound
`1 - |m|² ≥ 2dg²/R⁴`, coordinate-permutation invariance of `M^{(B)}`, the per-direction neighbour bound `K_{0,±e_i} ≥ c g²`
uniformly in `L` (cut P3a), and the Fourier symbol of `K = |M^{(B)}|²` on the dual torus with its gap, laziness and second
moment (cut P3b): `RBM3D/BA/KSymbol.lean`.
Section 1: merged names (exact namespaces; file:line on `main` fc74699).
Section 2: the two new definitions (copied verbatim by T2324 into namespace `RBM.BA`).
Section 3: the target statements as `Prop`s (T2324 proves them with these texts).
Statements, definitions and `#check` only: no theorem, no proof, no tactic block.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2324-check.lean`.
-/
import RBM3D.BA.KKernel
import RBM3D.BA.FlowPins

open MeasureTheory Filter Topology

/-! ## 1. Merged names -/

-- BA-P2 (T2317, fc0904a), `BA/KKernel.lean`, namespace `RBM.BA`
#check @RBM.BA.BAK                  -- :48
#check @RBM.BA.BAK_symm             -- :57
#check @RBM.BA.BAK_shift            -- :66
#check @RBM.BA.BAK_zero_neg         -- :70
#check @RBM.BA.BAK_diag             -- :120
#check @RBM.BA.BAK_row_sum          -- :124
#check @RBM.BA.BAK_diag_bounds      -- :140
#check @RBM.BA.BAK_off_le           -- :198
#check @RBM.BA.BAK_exp_moment_le    -- :228
#check @RBM.BA.BAK_adj_ge_small     -- :281
#check @RBM.BA.BAMB_adj_sum         -- :291
#check @RBM.BA.BAK_adj_sum_ge       -- :352
-- the fixed point and the spectral bridge (`BA/MFixedPoint.lean`, `BA/Ward.lean`, `BA/FlowPins.lean`)
#check @RBM.BA.BAMB                 -- MFixedPoint.lean:190
#check @RBM.BA.BASelf               -- :193
#check @RBM.BA.BAReal               -- :432
#check @RBM.BA.BAspec               -- :371
#check @RBM.BA.BAMB_trace_eq_sum    -- :655
#check @RBM.BA.BAMB_symm            -- Ward.lean:83
#check @RBM.BA.BAMB_shift           -- Ward.lean:53
#check @RBM.BA.BAm_norm_le_one      -- Ward.lean:136
#check @RBM.BA.baSelf_none_of_gt    -- FlowPins.lean:785
#check @RBM.BA.BAct_rate            -- CombesThomas.lean:45
#check @RBM.BA.BAp5s_A              -- Prop5Short.lean:49
#check @RBM.BA.BAp5s_S              -- Prop5Short.lean:52
-- model and lattice
#check @RBM.Gauss.PsiB              -- Gauss/BlockAnderson.lean:45
#check @RBM.Gauss.Mres              -- Loop/GLoopFlow.lean:81
#check @RBM.Zd                      -- Defs/Lattice.lean:63
#check @RBM.zdist                   -- :25
#check @RBM.zdistD                  -- :71
#check @RBM.Adj                     -- :108
#check @RBM.unitVec                 -- Defs/Neighbours.lean:76
#check @RBM.card_adj                -- Defs/Neighbours.lean:168

noncomputable section

namespace RBM.BA.T2324Check

open RBM RBM.Gauss RBM.BA

/-! ## 2. New definitions (copied verbatim into `RBM.BA`) -/

section Defs

variable (d L : ℕ) [NeZero L]

/-- The Fourier symbol of `K` on the dual torus, `K̂(θ_k) = Σ_a K_{0a} cos(θ_k · a)`, `θ_k = 2π k / L`
(real: `K_{0,-a} = K_{0a}`, `BAK_zero_neg`). -/
def BAKhat (g E : ℝ) (m : ℂ) (k : Zd d L) : ℝ :=
  ∑ a : Zd d L, BAK d L g E m 0 a *
    Real.cos (2 * Real.pi / L * ∑ j, ((k j).val : ℝ) * ((a j).val : ℝ))

/-- `|θ_k|²` with each coordinate taken in `(-π, π]`: `Σ_j (2π |k_j|_L / L)²`. -/
def BAthetaSq (k : Zd d L) : ℝ :=
  ∑ j, (2 * Real.pi * (zdist L (k j) : ℝ) / L) ^ 2

end Defs

/-! ## 3. Target statements -/

/-- Target 1 (P3a): the variance lower bound (supervisor 0344 Q2; D614). -/
def T2324_BAvar_lower : Prop :=
  ∀ (d L : ℕ) [NeZero L], 3 ≤ L → 0 < d → ∀ (g κ E : ℝ) (m : ℂ), 0 < g → 0 < κ → BAReal d L g κ E m →
    2 * (d : ℝ) * g ^ 2 / (2 * (d : ℝ) * g + ‖(E : ℂ) + m‖) ^ 4 ≤ 1 - ‖m‖ ^ 2

/-- Target 2 (P3a): `M^{(B)}` is invariant under coordinate permutations of `Z_L^d`. -/
def T2324_BAMB_perm : Prop :=
  ∀ (d L : ℕ) [NeZero L] (σ : Equiv.Perm (Fin d)) (g : ℝ) (z m : ℂ) (a b : Zd d L),
    BAMB d L g z m (fun j => a (σ j)) (fun j => b (σ j)) = BAMB d L g z m a b

/-- Target 3 (P3a): every neighbour of `0` carries the same weight. -/
def T2324_BAK_dir_eq : Prop :=
  ∀ (d L : ℕ) [NeZero L], 3 ≤ L → 0 < d → ∀ (g E : ℝ) (m : ℂ) (i : Fin d) (s : Bool),
    BAK d L g E m 0 (unitVec d L (i, s)) =
      (2 * (d : ℝ))⁻¹ * ∑ b ∈ Finset.univ.filter (fun b : Zd d L => Adj d L 0 b), BAK d L g E m 0 b

/-- Target 4 (P3a): the per-direction neighbour bound `K_{0,±e_i} ≥ c g²`, uniformly in `L` and `g ∈ (0, Λ]`. -/
def T2324_BAK_dir_ge : Prop :=
  ∀ d : ℕ, 0 < d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ c : ℝ, 0 < c ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ (i : Fin d) (s : Bool), c * g ^ 2 ≤ BAK d L g E m 0 (unitVec d L (i, s))

/-- Target 5 (P3b): `BAKhat` is the Fourier transform of the row `K_{0,·}` (the sine part vanishes). -/
def T2324_BAKhat_eq : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (k : Zd d L),
    (∑ a : Zd d L, (BAK d L g E m 0 a : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I / L * ∑ j, ((k j).val : ℂ) * ((a j).val : ℂ))) =
      (BAKhat d L g E m k : ℂ)

/-- Target 6 (P3b): the spectral gap `1 - K̂(θ) ≥ c g² |θ|²`, uniformly in `L` and `g ∈ (0, Λ]`. -/
def T2324_BAK_gap : Prop :=
  ∀ d : ℕ, 0 < d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ c : ℝ, 0 < c ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ k : Zd d L, c * g ^ 2 * BAthetaSq d L k ≤ 1 - BAKhat d L g E m k

/-- Target 7 (P3b): laziness `1 + K̂(θ) ≥ 2κ²`. -/
def T2324_BAK_lazy : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ), 0 < κ → BAReal d L g κ E m →
    ∀ k : Zd d L, 2 * κ ^ 2 ≤ 1 + BAKhat d L g E m k

/-- Target 8 (P3b): the second moment `Σ_a K_{0a} |a|² ≤ C g²`, uniformly in `L` and `g ∈ (0, Λ]`. -/
def T2324_BAK_second_moment : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∑ a : Zd d L, BAK d L g E m 0 a * (zdistD d L a : ℝ) ^ 2 ≤ C * g ^ 2

example : Prop := T2324_BAvar_lower ∧ T2324_BAMB_perm ∧ T2324_BAK_dir_eq ∧ T2324_BAK_dir_ge ∧
  T2324_BAKhat_eq ∧ T2324_BAK_gap ∧ T2324_BAK_lazy ∧ T2324_BAK_second_moment

end RBM.BA.T2324Check

end
