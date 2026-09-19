/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.Matrix.Normed
import RBM3D.Defs.Block
import RBM3D.Defs.Params

/-!
# The `Θ`-propagator

`def_Theta` of Section 2.5 sets, for `t ∈ [0,1]` and `σ₁ σ₂ ∈ {+,-}`,

  `Θ_t^(σ₁,σ₂) := (1 - t M^(σ₁,σ₂) S^(B))⁻¹`,   `(def_Thxi)`

and the zero-mode-removed propagator

  `Θ̊_t^(σ₁,σ₂)(a,b) := Θ_t^(σ₁,σ₂)(a,b) - L^(-2d) Σ_{a',b'} Θ_t^(σ₁,σ₂)(a',b')`.  `(def_Thxi0)`

For the **random band matrix** model `M^(σ₁,σ₂) = m(σ₁) m(σ₂) I`, so `M^(σ₁,σ₂) S^(B)`
is the scalar multiple `m(σ₁)m(σ₂) S^(B)` and the propagator depends on the two signs
only through the product `m := m(σ₁)m(σ₂)`.  That is the case formalized here, as
`RBM.ThetaRBM`; the block Anderson model, where `S^(B) = I` and `M^(σ₁,σ₂)` carries all
the structure, is a separate ticket (`docs/TASKS.md`).

`RBM.Theta` is the definition for a general pair `(M, S)`, which is what the paper
actually writes; `ThetaRBM` is its specialization.
-/

namespace RBM

open Matrix

/-- `(def_Thxi)` for a general pair `(M, S)`: `Θ_t := (1 - t M S)⁻¹`. -/
noncomputable def Theta {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M S : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  (1 - (t : ℂ) • (M * S))⁻¹

variable (d L : ℕ) [NeZero L] (g : ℝ) (m : ℂ) (t : ℝ)

/-- `(def_Thxi)` for the random band matrix model, where `M^(σ₁,σ₂) = m(σ₁)m(σ₂) I`.
The argument `m` is the product `m(σ₁) m(σ₂)`. -/
noncomputable def ThetaRBM : Matrix (Zd d L) (Zd d L) ℂ :=
  (1 - ((t : ℂ) * m) • SB d L g)⁻¹

theorem ThetaRBM_eq_Theta : ThetaRBM d L g m t = Theta (m • (1 : Matrix (Zd d L) (Zd d L) ℂ))
    (SB d L g) t := by
  simp only [ThetaRBM, Theta, Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_comm]

/-- `(def_Thxi0)`: the propagator with its zero mode removed. -/
noncomputable def ThetaRBM0 : Matrix (Zd d L) (Zd d L) ℂ :=
  Matrix.of fun a b => ThetaRBM d L g m t a b
    - ((L : ℂ) ^ (2 * d))⁻¹ * ∑ a', ∑ b', ThetaRBM d L g m t a' b'

theorem ThetaRBM0_apply (a b : Zd d L) :
    ThetaRBM0 d L g m t a b = ThetaRBM d L g m t a b
      - ((L : ℂ) ^ (2 * d))⁻¹ * ∑ a', ∑ b', ThetaRBM d L g m t a' b' := rfl

end RBM
