/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Propagator.Basic

/-!
# Statements of properties 5-8 of `lem_propTH` (random band model, `d ≥ 3`)

The statements of properties 5-8 of Lemma 2.19 (`lem_propTH`) for the random band model:
`Prop5Decay`, `Prop5Short`,
`Prop6Diff1`, `Prop7Diff2`, `Prop8ZeroMode` (namespace `RBM`, name prefix `Prop` + number) and their
bundle `Prop5to8`; `PropSpin` is the notation they use, and `PropThetaQ` is the propagator for a
general transition matrix.  Form common to all of them (Lemma 2.19):
* the constants are quantified **before** `L` and `g` (`g = λ` of the paper) and depend only on
  `d`, `Λ` (the upper end of (2.10) `eq:WO`, `Λ = 𝔡⁻¹`), and where the paper says so on `κ`, `c`;
* `g ∈ (0, Λ]`, `L ≥ 3`, `t ∈ [0, 1)`, both sign pairs `(σ₁, σ₂)`: `Θ_t^{(σ₁,σ₂)}` is
  `Theta d L g (t * (m(σ₁) m(σ₂)))` with `m(+) = m`, `m(-) = m̄`, `‖m‖ = 1`;
* the bulk condition is `κ ≤ Im m`;
* `≺` of properties 6-8 is no loss; `|r| ≲ |a|` of properties 6, 7 is `|r| ≤ c |a|`, `0 < c < 1`.
-/

namespace RBM

/-- `m(σ)` of the paper: `σ = true` is `+` (`m(+) = m`), `σ = false` is `-` (`m(-) = m̄`). -/
noncomputable def PropSpin (m : ℂ) : Bool → ℂ := fun σ => if σ then m else (starRingEnd ℂ) m

/-- **Property 5**, (2.66) `prop:ThfadC`: `|Θ_t(0,a)| ≤ C_d B_{t,|a|} e^{-c_d |a| / ℓ_t}`; constants
`(d, Λ)`; all `m` with `‖m‖ = 1`, all sign pairs, no bulk condition. -/
def Prop5Decay (d : ℕ) (Λ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ →
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → ∀ σ₁ σ₂ : Bool, ∀ a : Zd d L,
          haveI : NeZero L := ⟨by omega⟩
          ‖Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 a‖
            ≤ C * Bparam d L g t (zdistD d L a)
                * Real.exp (-c * (zdistD d L a : ℝ) / ellT L g t)

/-- **Property 5, short form**, (2.67) `prop:ThfadC_short`, `σ₁ = σ₂ = σ`:
`|Θ_t(0,a)| ≤ C_κ (1_{a=0} + g² e^{-c_κ|a|})`;
constants `(d, Λ, κ)`; bulk `κ ≤ Im m`. -/
def Prop5Short (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ : Bool, ∀ a : Zd d L,
          haveI : NeZero L := ⟨by omega⟩
          ‖Theta d L g ((t : ℂ) * (PropSpin m σ * PropSpin m σ)) 0 a‖
            ≤ C * ((if a = 0 then (1 : ℝ) else 0) + g ^ 2 * Real.exp (-c * (zdistD d L a : ℝ)))

/-- **Property 6**, (2.68) `prop:BD1`:
`|Θ_t(0,a+r) - Θ_t(0,a)| ≤ C (g²+|1-t|)⁻¹ |r| (|a|+1)^{-(d-1)}` for
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

/-- **Property 7**, (2.69) `prop:BD2`:
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

/-- **Property 8**, (2.70) `prop:ThfadC0`: `|Θ̊_t(0,a)| ≤ C (g²+|1-t|)⁻¹ (|a|+1)^{-(d-2)}`;
constants `(d, Λ, κ)`; no loss. -/
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
  /-- (2.66) `prop:ThfadC` -/
  decay : Prop5Decay d Λ
  /-- (2.67) `prop:ThfadC_short` -/
  short : Prop5Short d Λ κ
  /-- (2.68) `prop:BD1` -/
  diffOne : Prop6Diff1 d Λ κ c
  /-- (2.69) `prop:BD2` -/
  diffTwo : Prop7Diff2 d Λ κ c
  /-- (2.70) `prop:ThfadC0` -/
  zeroMode : Prop8ZeroMode d Λ κ

/-! ### Remark: the constants of property 5 depend on `Λ`

At `t = 0`, `Θ_0 = 1` and `B_{0,0} = (g²+1)⁻¹ + L⁻ᵈ`, so `|Θ_0(0,0)| = 1 ≤ C B_{0,0}` forces
`C ≥ (1+g²)/(1+(1+g²)L⁻ᵈ)`.  With `g` unbounded this has no uniform `C`: the paper's "constants
depending on `d`" is correct only with `g ≤ Λ`, `Λ = 𝔡⁻¹` of (2.10) `eq:WO`, and `C ≥ 1 + Λ²`. -/

/-! ### The shape for the block Anderson model

In the block Anderson model `S^{(B)} = 1` and `M^{(σ₁,σ₂)}_{ab} = M^{(B)}_{ba}(σ₁) M^{(B)}_{ab}(σ₂)`
is a complex symmetric matrix with `|M^{(σ₁,σ₂)}_{ab}| ≤ M^{(+,-)}_{ab}` and unit row sums for
`(+,-)` (Ward).  `Θ_t^{(σ₁,σ₂)} = (1 - t Q)⁻¹` with `Q = M^{(σ₁,σ₂)} S^{(B)}`.  The statements of
properties 5-8 keep their form for any such family `Q`; only the proofs depend on `Q`
(the RBM family is `Q = (m(σ₁)m(σ₂)) • SB d L g`). -/

/-- `Θ_t = (1 - t Q)⁻¹` for an arbitrary transition matrix `Q = M^{(σ₁,σ₂)} S^{(B)}`. -/
noncomputable def PropThetaQ {d L : ℕ} [NeZero L] (Q : Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) :
    Matrix (Zd d L) (Zd d L) ℂ :=
  Ring.inverse (1 - (t : ℂ) • Q)

end RBM
