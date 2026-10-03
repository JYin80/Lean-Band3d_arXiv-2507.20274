/-
Release check for T2024 (dispatcher V1, Sat Oct  3 04:09 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §13, §14).
Pinned `Prop` statements of PT-F2: the unit first and second differences of `Θ` (the "unit pins" U1, U2s, U2m of
T2003 N5 and Fable F7), which PT-G turns into `(prop:BD1)`, `(prop:BD2)` by the path lemma.
Namespace `RBM.T2024Check` here becomes `RBM` in the ticket.
Statements and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2024-check.lean`.
-/
import RBM3D

#check @RBM.Theta
#check @RBM.PropSpin
#check @RBM.zdistD
#check @RBM.prop5Short_holds
#check @RBM.norm_Theta_apply_le
#check @RBM.Heat.Theta_eq_laplace_prod
#check @RBM.Heat.kProd_diff1_le
#check @RBM.Heat.kProd_diff2_le
#check @RBM.Heat.kProd_gap
#check @RBM.Heat.lg_bulk
#check @RBM.Heat.lg_zero
#check @RBM.Heat.lg_tail
#check @RBM.Heat.lg_convA

namespace RBM.T2024Check

open RBM

/-- **Unit pin 1**: `|Θ_t(0, a + e_j) − Θ_t(0, a)| ≤ C (g² + |1−t|)⁻¹ (|a| + 1)^{-(d−1)}`; constants `(d, Λ, κ)`;
bulk `κ ≤ Im m` (idle for `σ₁ ≠ σ₂`, as in the merged P6–P8 pins). -/
def PropUnit1 (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ₁ σ₂ : Bool,
          ∀ (a : Zd d L) (j : Fin d),
            haveI : NeZero L := ⟨by omega⟩
            ‖Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 (a + Pi.single j 1)
                - Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 a‖
              ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹

/-- **Unit pin 2**: the unit second differences, mixed (`i ≠ j`) and same-direction (`i = j`):
`|Θ(a+e_i+e_j) − Θ(a+e_i) − Θ(a+e_j) + Θ(a)| ≤ C (g² + |1−t|)⁻¹ (|a| + 1)^{-d}`. -/
def PropUnit2 (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ₁ σ₂ : Bool,
          ∀ (a : Zd d L) (i j : Fin d),
            haveI : NeZero L := ⟨by omega⟩
            ‖Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 (a + Pi.single i 1 + Pi.single j 1)
                - Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 (a + Pi.single i 1)
                - Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 (a + Pi.single j 1)
                + Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 a‖
              ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ d)⁻¹

end RBM.T2024Check
