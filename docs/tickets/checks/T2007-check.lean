/-
Release check for T2007 (dispatcher V1, Fri Oct  2 23:16 UTC 2026; CLAUDE.md §4 step 0).
Pinned `Prop` text copied verbatim from `d6e6054:RBM3D/Probe/T2003Pins.lean` (lines 27–105 and the
definitions `PropThetaQ`, `Prop5DecayQ`); namespace `RBM.T2007Check` here becomes `RBM` in the
ticket.  Definitions and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2007-check.lean`.
-/
import RBM3D

#check @RBM.Theta
#check @RBM.Theta0
#check @RBM.SB
#check @RBM.SB_apply
#check @RBM.SBR
#check @RBM.sbKernelR
#check @RBM.Bparam
#check @RBM.ellT
#check @RBM.zdistD
#check @RBM.Theta_eq_tsum_of_three_le
#check @RBM.summable_smul_SB_pow
#check @RBM.norm_Theta_apply_le
#check @RBM.exists_step
#check @RBM.ThetaDecay
#check @RBM.ThetaDecayShort
#check @RBM.ThetaZeroMode
#check @RBM.ThetaDiffOne
#check @RBM.ThetaDiffTwo
#check @RBM.PropTH

namespace RBM.T2007Check

/-- `m(σ)` of the paper: `σ = true` is `+` (`m(+) = m`), `σ = false` is `-` (`m(-) = m̄`). -/
noncomputable def PropSpin (m : ℂ) : Bool → ℂ := fun σ => if σ then m else (starRingEnd ℂ) m

/-- **Pin 5** `(prop:ThfadC)`: `|Θ_t(0,a)| ≤ C_d B_{t,|a|} e^{-c_d |a| / ℓ_t}`; constants `(d, Λ)`;
all `m` with `‖m‖ = 1`, all sign pairs, no bulk condition. -/
def Prop5Decay (d : ℕ) (Λ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ →
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → ∀ σ₁ σ₂ : Bool, ∀ a : Zd d L,
          haveI : NeZero L := ⟨by omega⟩
          ‖Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 a‖
            ≤ C * Bparam d L g t (zdistD d L a)
                * Real.exp (-c * (zdistD d L a : ℝ) / ellT L g t)

/-- **Pin 5s** `(prop:ThfadC_short)`, `σ₁ = σ₂ = σ`: `|Θ_t(0,a)| ≤ C_κ (1_{a=0} + g² e^{-c_κ|a|})`;
constants `(d, Λ, κ)`; bulk `κ ≤ Im m`. -/
def Prop5Short (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ : Bool, ∀ a : Zd d L,
          haveI : NeZero L := ⟨by omega⟩
          ‖Theta d L g ((t : ℂ) * (PropSpin m σ * PropSpin m σ)) 0 a‖
            ≤ C * ((if a = 0 then (1 : ℝ) else 0) + g ^ 2 * Real.exp (-c * (zdistD d L a : ℝ)))

/-- **Pin 6** `(prop:BD1)`: `|Θ_t(0,a+r) - Θ_t(0,a)| ≤ C (g²+|1-t|)⁻¹ |r| (|a|+1)^{-(d-1)}` for
`|r| ≤ c |a|`, `0 < c < 1`; constants `(d, Λ, κ, c)`; no loss. -/
def Prop6Diff1 (d : ℕ) (Λ κ c : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ → 0 < c → c < 1 →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ₁ σ₂ : Bool, ∀ a r : Zd d L,
          (zdistD d L r : ℝ) ≤ c * (zdistD d L a : ℝ) →
          haveI : NeZero L := ⟨by omega⟩
          ‖Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 (a + r)
              - Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 a‖
            ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (zdistD d L r : ℝ)
                * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹

/-- **Pin 7** `(prop:BD2)`:
`|Θ_t(0,a+r) + Θ_t(0,a-r) - 2Θ_t(0,a)| ≤ C (g²+|1-t|)⁻¹ |r|² (|a|+1)^{-d}` for `|r| ≤ c |a|`,
`0 < c < 1`; constants `(d, Λ, κ, c)`; no loss. -/
def Prop7Diff2 (d : ℕ) (Λ κ c : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ → 0 < c → c < 1 →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ₁ σ₂ : Bool, ∀ a r : Zd d L,
          (zdistD d L r : ℝ) ≤ c * (zdistD d L a : ℝ) →
          haveI : NeZero L := ⟨by omega⟩
          ‖Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 (a + r)
              + Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 (a - r)
              - 2 * Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 a‖
            ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (zdistD d L r : ℝ) ^ 2
                * (((zdistD d L a : ℝ) + 1) ^ d)⁻¹

/-- **Pin 8** `(prop:ThfadC0)`: `|Θ̊_t(0,a)| ≤ C (g²+|1-t|)⁻¹ (|a|+1)^{-(d-2)}`; constants
`(d, Λ, κ)`; no loss. -/
def Prop8ZeroMode (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ₁ σ₂ : Bool, ∀ a : Zd d L,
          haveI : NeZero L := ⟨by omega⟩
          ‖Theta0 d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 a‖
            ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹

/-- The bundle: properties 5-8 of `lem_propTH` at one `(d, Λ, κ, c)`. -/
structure Prop5to8 (d : ℕ) (Λ κ c : ℝ) : Prop where
  /-- `(prop:ThfadC)` -/
  decay : Prop5Decay d Λ
  /-- `(prop:ThfadC_short)` -/
  short : Prop5Short d Λ κ
  /-- `(prop:BD1)` -/
  diffOne : Prop6Diff1 d Λ κ c
  /-- `(prop:BD2)` -/
  diffTwo : Prop7Diff2 d Λ κ c
  /-- `(prop:ThfadC0)` -/
  zeroMode : Prop8ZeroMode d Λ κ


/-! The shape gate BA reuses (probe item 6). -/

/-- `Θ_t = (1 - t Q)⁻¹` for an arbitrary transition matrix `Q = M^{(σ₁,σ₂)} S^{(B)}`. -/
noncomputable def PropThetaQ {d L : ℕ} [NeZero L] (Q : Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) :
    Matrix (Zd d L) (Zd d L) ℂ :=
  Ring.inverse (1 - (t : ℂ) • Q)

/-- Pin 5 for a model-indexed family `Q L g σ₁ σ₂`; the model is the family. -/
def Prop5DecayQ (d : ℕ) (Λ : ℝ)
    (Q : ∀ (L : ℕ) [NeZero L], ℝ → Bool → Bool → Matrix (Zd d L) (Zd d L) ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
    ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, ∀ a : Zd d L,
        haveI : NeZero L := ⟨by omega⟩
        ‖PropThetaQ (Q L g σ₁ σ₂) t 0 a‖
          ≤ C * Bparam d L g t (zdistD d L a) * Real.exp (-c * (zdistD d L a : ℝ) / ellT L g t)


/-- The pin of target 2. -/
def Stmt : Prop := ∀ (d : ℕ) (Λ κ : ℝ), Prop5Short d Λ κ

end RBM.T2007Check
