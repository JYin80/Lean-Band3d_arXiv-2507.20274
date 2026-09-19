/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Defs.Block
import RBM3D.Defs.Params
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Matrix.Normed

/-!
# The `Θ`-propagator

`def_Theta` of Section 2.5 sets `Θ_t^(σ₁,σ₂) := (1 - t M^(σ₁,σ₂) S^(B))⁻¹`, and
`(def_Thxi0)` the zero-mode-removed propagator
`Θ̊_t(a,b) := Θ_t(a,b) - L^(-2d) Σ_{a',b'} Θ_t(a',b')`.

For the **random band matrix** model `M^(σ₁,σ₂) = m(σ₁) m(σ₂) I`, so `M^(σ₁,σ₂) S^(B)`
is the scalar multiple `m(σ₁)m(σ₂) S^(B)` and the propagator depends on the two signs
only through the product.  `RBM.Theta` therefore takes the single spectral parameter
`ξ = t · m(σ₁)m(σ₂)`, and `RBM.ThetaRBM` is the specialization.  The block Anderson
model, where `S^(B) = I` and `M^(σ₁,σ₂)` carries the structure, is a separate ticket.

## The one idea in this file

Everything structural about `Θ` -- symmetry, translation invariance, commutativity --
comes from a single lemma, `RBM.eq_Theta_of_mul`: *any* left inverse of `1 - ξ S^(B)`
**is** `Θ_ξ`.  To prove `Θ` has a property, exhibit a matrix with that property which is
a left inverse, and invoke uniqueness.  This is the route the sister project `RBM1D`
takes in `RBM1D/Propagator/Basic.lean`, and it transfers to `d ≥ 3` unchanged: nothing
in it uses the dimension.

Concretely: take `Ring.inverse` in the matrix ring under the `ℓ^∞` operator norm --
**not** `Matrix.inv`, which drags in determinants and invertibility instances for no
benefit.  `‖S^(B)(g)‖ = 1` makes `1 - ξ S^(B)` a unit via `Units.oneSub` whenever
`‖ξ‖ < 1`, and that is exactly the paper's standing assumption `t ∈ [0,1)` together with
`|m(σ)| = 1`.

## The hypothesis `hS`

`‖S^(B)(g)‖ = 1` is the statement that `S^(B)(g)` is doubly stochastic with non-negative
entries.  Proving it needs the neighbour count `#{x : |x| = 1} = 2d`, which is where
`3 ≤ L` enters and which is ticket **T4**.  Rather than block this whole file on T4, the
results below carry `hS` as a hypothesis, exactly as the paper carries "S^(B) is doubly
stochastic".  When T4 lands, `RBM.norm_SB` discharges it at every call site.

## Main results

* `RBM.Theta_mul`, `RBM.mul_Theta` : `Θ_ξ` is a two-sided inverse of `1 - ξ S^(B)`
* `RBM.eq_Theta_of_mul`  : uniqueness -- the workhorse for everything below
* `RBM.Theta_transpose`  : property 1 of `lem_propTH`, symmetry
* `RBM.Theta_apply_add_right` : property 2, translation invariance
* `RBM.Theta_commute_SB`, `RBM.Theta_commute` : property 3, commutativity
* `RBM.sum_Theta_row`    : `Σ_b (Θ_ξ)_{ab} = (1-ξ)⁻¹`, the input to property 4
* `RBM.Theta_eq_tsum`    : the Neumann series `(eq;Taylor)`
-/

namespace RBM

open Matrix
open scoped NNReal Matrix.Norms.Operator

variable (d L : ℕ) [NeZero L] (g : ℝ)

section Defs

/-- `(def_Thxi)` for the random band matrix model, with spectral parameter
`ξ = t · m(σ₁)m(σ₂)`: the propagator `Θ_ξ = (1 - ξ S^(B))⁻¹`. -/
noncomputable def Theta (ξ : ℂ) : Matrix (Zd d L) (Zd d L) ℂ :=
  Ring.inverse (1 - ξ • SB d L g)

theorem norm_smul_SB_lt_one (hS : ‖SB d L g‖ = 1) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    ‖ξ • SB d L g‖ < 1 := by
  rw [norm_smul, hS, mul_one]
  exact hξ

theorem isUnit_one_sub_smul_SB (hS : ‖SB d L g‖ = 1) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    IsUnit (1 - ξ • SB d L g) :=
  ⟨Units.oneSub _ (norm_smul_SB_lt_one d L g hS hξ), Units.val_oneSub _ _⟩

theorem Theta_mul (hS : ‖SB d L g‖ = 1) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    Theta d L g ξ * (1 - ξ • SB d L g) = 1 :=
  Ring.inverse_mul_cancel _ (isUnit_one_sub_smul_SB d L g hS hξ)

theorem mul_Theta (hS : ‖SB d L g‖ = 1) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    (1 - ξ • SB d L g) * Theta d L g ξ = 1 :=
  Ring.mul_inverse_cancel _ (isUnit_one_sub_smul_SB d L g hS hξ)

/-- Uniqueness of the inverse: any left inverse of `1 - ξ S^(B)` equals `Θ_ξ`.
This is the workhorse used to transfer structural properties of `S^(B)` to `Θ_ξ`. -/
theorem eq_Theta_of_mul (hS : ‖SB d L g‖ = 1) {ξ : ℂ} (hξ : ‖ξ‖ < 1)
    {B : Matrix (Zd d L) (Zd d L) ℂ} (h : B * (1 - ξ • SB d L g) = 1) :
    B = Theta d L g ξ := by
  calc B = B * ((1 - ξ • SB d L g) * Theta d L g ξ) := by rw [mul_Theta d L g hS hξ, mul_one]
    _ = (B * (1 - ξ • SB d L g)) * Theta d L g ξ := (mul_assoc _ _ _).symm
    _ = Theta d L g ξ := by rw [h, one_mul]

end Defs

section Structure

/-- Property 1 of `lem_propTH`: `Θ_ξ` is symmetric. -/
theorem Theta_transpose (hS : ‖SB d L g‖ = 1) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    (Theta d L g ξ)ᵀ = Theta d L g ξ := by
  refine eq_Theta_of_mul d L g hS hξ ?_
  have hsym : (1 - ξ • SB d L g)ᵀ = 1 - ξ • SB d L g := by
    rw [transpose_sub, transpose_one, transpose_smul, SB_transpose]
  calc (Theta d L g ξ)ᵀ * (1 - ξ • SB d L g)
      = (Theta d L g ξ)ᵀ * (1 - ξ • SB d L g)ᵀ := by rw [hsym]
    _ = ((1 - ξ • SB d L g) * Theta d L g ξ)ᵀ := (transpose_mul _ _).symm
    _ = 1 := by rw [mul_Theta d L g hS hξ, transpose_one]

theorem Theta_isSymm (hS : ‖SB d L g‖ = 1) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    (Theta d L g ξ).IsSymm :=
  Theta_transpose d L g hS hξ

/-- Property 3 of `lem_propTH`: `Θ_ξ` commutes with `S^(B)`. -/
theorem Theta_commute_SB (hS : ‖SB d L g‖ = 1) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    Commute (Theta d L g ξ) (SB d L g) := by
  have hb : Commute (1 - ξ • SB d L g) (SB d L g) := by
    unfold Commute SemiconjBy
    simp [sub_mul, mul_sub]
  change Theta d L g ξ * SB d L g = SB d L g * Theta d L g ξ
  calc Theta d L g ξ * SB d L g
      = Theta d L g ξ * SB d L g * ((1 - ξ • SB d L g) * Theta d L g ξ) := by
        rw [mul_Theta d L g hS hξ, mul_one]
    _ = Theta d L g ξ * ((1 - ξ • SB d L g) * SB d L g) * Theta d L g ξ := by
        rw [hb.eq]; noncomm_ring
    _ = (Theta d L g ξ * (1 - ξ • SB d L g)) * SB d L g * Theta d L g ξ := by noncomm_ring
    _ = SB d L g * Theta d L g ξ := by rw [Theta_mul d L g hS hξ, one_mul]

/-- Property 3 of `lem_propTH`: propagators at different spectral parameters commute. -/
theorem Theta_commute (hS : ‖SB d L g‖ = 1) {ξ ξ' : ℂ} (hξ : ‖ξ‖ < 1) (hξ' : ‖ξ'‖ < 1) :
    Commute (Theta d L g ξ) (Theta d L g ξ') := by
  have h1 : Commute (Theta d L g ξ) (1 - ξ' • SB d L g) := by
    have := Theta_commute_SB d L g hS hξ
    unfold Commute SemiconjBy at this ⊢
    simp [mul_sub, sub_mul, this]
  change Theta d L g ξ * Theta d L g ξ' = Theta d L g ξ' * Theta d L g ξ
  calc Theta d L g ξ * Theta d L g ξ'
      = Theta d L g ξ' * (1 - ξ' • SB d L g) * (Theta d L g ξ * Theta d L g ξ') := by
        rw [Theta_mul d L g hS hξ', one_mul]
    _ = Theta d L g ξ' * ((1 - ξ' • SB d L g) * Theta d L g ξ) * Theta d L g ξ' := by
        noncomm_ring
    _ = Theta d L g ξ' * (Theta d L g ξ * (1 - ξ' • SB d L g)) * Theta d L g ξ' := by
        rw [h1.eq]
    _ = Theta d L g ξ' * Theta d L g ξ * ((1 - ξ' • SB d L g) * Theta d L g ξ') := by
        noncomm_ring
    _ = Theta d L g ξ' * Theta d L g ξ := by rw [mul_Theta d L g hS hξ', mul_one]

/-- Property 2 of `lem_propTH`: translation invariance,
`Θ_ξ(a + c, b + c) = Θ_ξ(a, b)`. -/
theorem Theta_apply_add_right (hS : ‖SB d L g‖ = 1) {ξ : ℂ} (hξ : ‖ξ‖ < 1)
    (a b c : Zd d L) : Theta d L g ξ (a + c) (b + c) = Theta d L g ξ a b := by
  set e : Zd d L ≃ Zd d L := Equiv.addRight c with he
  have hone : ((1 : Matrix (Zd d L) (Zd d L) ℂ)).submatrix e e = 1 :=
    Matrix.submatrix_one_equiv e
  have hSB : (SB d L g).submatrix e e = SB d L g := by
    ext i j
    simpa [he] using SB_apply_add_right d L g i j c
  have hsub : (1 - ξ • SB d L g).submatrix e e = 1 - ξ • SB d L g := by
    simp [Matrix.submatrix_sub, Matrix.submatrix_smul, hSB, hone]
  have hkey : (Theta d L g ξ).submatrix e e = Theta d L g ξ := by
    refine eq_Theta_of_mul d L g hS hξ ?_
    calc (Theta d L g ξ).submatrix e e * (1 - ξ • SB d L g)
        = (Theta d L g ξ).submatrix e e * (1 - ξ • SB d L g).submatrix e e := by rw [hsub]
      _ = (Theta d L g ξ * (1 - ξ • SB d L g)).submatrix e e :=
          Matrix.submatrix_mul_equiv _ _ _ _ _
      _ = 1 := by rw [Theta_mul d L g hS hξ, hone]
  calc Theta d L g ξ (a + c) (b + c) = (Theta d L g ξ).submatrix e e a b := rfl
    _ = Theta d L g ξ a b := by rw [hkey]

end Structure

section RowSum

theorem one_sub_ne_zero {ξ : ℂ} (hξ : ‖ξ‖ < 1) : (1 : ℂ) - ξ ≠ 0 := by
  intro h
  have hone : ξ = 1 := by linear_combination -h
  rw [hone] at hξ
  simp at hξ

/-- `Θ_ξ` applied to the constant vector `1`.  Needs `S^(B) 1 = 1`, which is ticket T4;
it is carried here as the hypothesis `hone`. -/
theorem Theta_mulVec_one (hS : ‖SB d L g‖ = 1)
    (hone : SB d L g *ᵥ (1 : Zd d L → ℂ) = 1) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    Theta d L g ξ *ᵥ (1 : Zd d L → ℂ) = (1 - ξ)⁻¹ • (1 : Zd d L → ℂ) := by
  have hne : (1 : ℂ) - ξ ≠ 0 := one_sub_ne_zero hξ
  have h1 : (1 - ξ • SB d L g) *ᵥ (1 : Zd d L → ℂ) = (1 - ξ) • (1 : Zd d L → ℂ) := by
    rw [sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hone, sub_smul, one_smul]
  calc Theta d L g ξ *ᵥ (1 : Zd d L → ℂ)
      = (1 - ξ)⁻¹ • (Theta d L g ξ *ᵥ ((1 - ξ) • (1 : Zd d L → ℂ))) := by
        rw [Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hne, one_smul]
    _ = (1 - ξ)⁻¹ • (Theta d L g ξ *ᵥ ((1 - ξ • SB d L g) *ᵥ (1 : Zd d L → ℂ))) := by rw [h1]
    _ = (1 - ξ)⁻¹ • ((Theta d L g ξ * (1 - ξ • SB d L g)) *ᵥ (1 : Zd d L → ℂ)) := by
        rw [Matrix.mulVec_mulVec]
    _ = (1 - ξ)⁻¹ • (1 : Zd d L → ℂ) := by
        rw [Theta_mul d L g hS hξ, Matrix.one_mulVec]

/-- The row sums of the propagator.  With `ξ = t` this is the identity
`Σ_b Θ^(+,-)_{t,ab} = (1-t)⁻¹` that Appendix A.1 uses for property 4. -/
theorem sum_Theta_row (hS : ‖SB d L g‖ = 1)
    (hone : SB d L g *ᵥ (1 : Zd d L → ℂ) = 1) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (a : Zd d L) :
    ∑ b : Zd d L, Theta d L g ξ a b = (1 - ξ)⁻¹ := by
  have h := congrFun (Theta_mulVec_one d L g hS hone hξ) a
  simpa [Matrix.mulVec, dotProduct] using h

end RowSum

section Series

/-- `(eq;Taylor)`: the random-walk (Neumann) representation
`Θ_ξ = Σ_k ξ^k (S^(B))^k`.  This is the expansion Appendix A.1 uses for properties 1--4. -/
theorem Theta_eq_tsum (hS : ‖SB d L g‖ = 1) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    Theta d L g ξ = ∑' k : ℕ, (ξ • SB d L g) ^ k := by
  rw [Theta, NormedRing.inverse_one_sub _ (norm_smul_SB_lt_one d L g hS hξ)]
  rfl

end Series

section ZeroMode

/-- `(def_Thxi0)`: the propagator with its zero mode removed. -/
noncomputable def Theta0 (ξ : ℂ) : Matrix (Zd d L) (Zd d L) ℂ :=
  Matrix.of fun a b => Theta d L g ξ a b
    - ((L : ℂ) ^ (2 * d))⁻¹ * ∑ a', ∑ b', Theta d L g ξ a' b'

theorem Theta0_apply (ξ : ℂ) (a b : Zd d L) :
    Theta0 d L g ξ a b = Theta d L g ξ a b
      - ((L : ℂ) ^ (2 * d))⁻¹ * ∑ a', ∑ b', Theta d L g ξ a' b' := rfl

end ZeroMode

end RBM
