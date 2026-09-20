/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Propagator.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Topology.Instances.Matrix

/-!
# The derivative of the propagator

`∂_ξ Θ_ξ = Θ_ξ S^(B) Θ_ξ`, the `d ≥ 3` form of equation `(2.51)` of the sister paper
*Delocalization of One-Dimensional Random Band Matrices* -- in this paper it is the
computation behind the primitive loop equation of Appendix A.5, which is what makes that
equation quadratic.

The proof goes through the resolvent identity
`Θ_ζ - Θ_ξ = (ζ - ξ) Θ_ζ S^(B) Θ_ξ`
together with continuity of `ξ ↦ Θ_ξ`, rather than differentiating the Neumann series
term by term.

The statement is given **entrywise**.  That is both what the loop layer uses -- every
sum there is over block indices -- and what avoids the instance diamond between the Pi
topology on `Matrix` and the topology of the `ℓ^∞` operator norm.  Do not restate it for
the whole matrix.

As everywhere in `Propagator/`, the lemmas carry the hypothesis `hS : ‖S^(B)‖ = 1`
(`RBM.norm_SB` discharges it from `3 ≤ L`); `d` stays a parameter and never enters the
argument, exactly as `Θ`'s definition does not.
-/

namespace RBM

open Matrix Filter Topology
open scoped Matrix.Norms.Operator

variable (d L : ℕ) [NeZero L] (g : ℝ)

theorem continuousAt_Theta (hS : ‖SB d L g‖ = 1) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    ContinuousAt (fun ζ : ℂ => Theta d L g ζ) ξ := by
  obtain ⟨u, hu⟩ := isUnit_one_sub_smul_SB d L g hS hξ
  have hinv : ContinuousAt (Ring.inverse : Matrix (Zd d L) (Zd d L) ℂ → _)
      (1 - ξ • SB d L g) := by
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  have hlin : ContinuousAt (fun ζ : ℂ => 1 - ζ • SB d L g) ξ :=
    continuousAt_const.sub (continuousAt_id.smul continuousAt_const)
  simp only [Theta]
  exact ContinuousAt.comp (g := Ring.inverse) (f := fun ζ : ℂ => 1 - ζ • SB d L g) hinv hlin

/-- The resolvent identity for the propagator. -/
theorem Theta_sub_Theta (hS : ‖SB d L g‖ = 1) {ξ ζ : ℂ} (hξ : ‖ξ‖ < 1) (hζ : ‖ζ‖ < 1) :
    Theta d L g ζ - Theta d L g ξ
      = (ζ - ξ) • (Theta d L g ζ * SB d L g * Theta d L g ξ) := by
  have hd : (1 - ξ • SB d L g) - (1 - ζ • SB d L g) = (ζ - ξ) • SB d L g := by
    rw [sub_sub_sub_cancel_left, ← sub_smul]
  calc Theta d L g ζ - Theta d L g ξ
      = Theta d L g ζ * ((1 - ξ • SB d L g) * Theta d L g ξ)
        - Theta d L g ζ * (1 - ζ • SB d L g) * Theta d L g ξ := by
        rw [mul_Theta d L g hS hξ, Theta_mul d L g hS hζ, mul_one, one_mul]
    _ = Theta d L g ζ * ((1 - ξ • SB d L g) - (1 - ζ • SB d L g)) * Theta d L g ξ := by
        noncomm_ring
    _ = Theta d L g ζ * ((ζ - ξ) • SB d L g) * Theta d L g ξ := by rw [hd]
    _ = (ζ - ξ) • (Theta d L g ζ * SB d L g * Theta d L g ξ) := by simp

omit [NeZero L] in
theorem continuous_matrix_entry (a b : Zd d L) :
    Continuous fun M : Matrix (Zd d L) (Zd d L) ℂ => M a b :=
  (continuous_apply b).comp (continuous_apply a)

/-- **The derivative of the propagator**, entrywise:
`∂_ξ (Θ_ξ)_{ab} = (Θ_ξ S^(B) Θ_ξ)_{ab}`. -/
theorem hasDerivAt_Theta_apply (hS : ‖SB d L g‖ = 1) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (a b : Zd d L) :
    HasDerivAt (fun ζ : ℂ => Theta d L g ζ a b)
      ((Theta d L g ξ * SB d L g * Theta d L g ξ) a b) ξ := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hball : ∀ᶠ ζ : ℂ in 𝓝[≠] ξ, ‖ζ‖ < 1 :=
    eventually_nhdsWithin_of_eventually_nhds
      ((isOpen_lt continuous_norm continuous_const).mem_nhds hξ)
  have hslope : ∀ᶠ ζ : ℂ in 𝓝[≠] ξ,
      (Theta d L g ζ * SB d L g * Theta d L g ξ) a b
        = slope (fun ζ : ℂ => Theta d L g ζ a b) ξ ζ := by
    filter_upwards [hball, self_mem_nhdsWithin] with ζ hζ hmem
    have hne : ζ - ξ ≠ 0 := sub_ne_zero_of_ne hmem
    have hdiff : Theta d L g ζ a b - Theta d L g ξ a b
        = (ζ - ξ) * (Theta d L g ζ * SB d L g * Theta d L g ξ) a b := by
      have h := congrFun (congrFun (Theta_sub_Theta d L g hS hξ hζ) a) b
      simpa [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using h
    rw [slope_def_field, hdiff, mul_comm, mul_div_assoc, div_self hne, mul_one]
  refine Tendsto.congr' hslope ?_
  have hM : Tendsto (fun ζ : ℂ => Theta d L g ζ) (𝓝[≠] ξ) (𝓝 (Theta d L g ξ)) :=
    (continuousAt_Theta d L g hS hξ).tendsto.mono_left nhdsWithin_le_nhds
  have hmul : Tendsto (fun ζ : ℂ => Theta d L g ζ * SB d L g * Theta d L g ξ) (𝓝[≠] ξ)
      (𝓝 (Theta d L g ξ * SB d L g * Theta d L g ξ)) :=
    (hM.mul tendsto_const_nhds).mul tendsto_const_nhds
  exact ((continuous_matrix_entry d L a b).continuousAt.tendsto).comp hmul

/-- The derivative **in `t`** along the spectral parameter `ξ = t μ` of `(def_Theta)`,
which is the form the loop layer uses: `∂_t (Θ_{tμ})_{ab} = μ (Θ_{tμ} S^(B) Θ_{tμ})_{ab}`.

For the random band matrix model `μ = m(σ₁)m(σ₂)`, so this is the `t`-derivative of
`Θ_t^{(σ₁,σ₂)}` itself. -/
theorem hasDerivAt_Theta_mul_apply (hS : ‖SB d L g‖ = 1) {μ : ℂ} {t : ℝ}
    (hξ : ‖(t : ℂ) * μ‖ < 1) (a b : Zd d L) :
    HasDerivAt (fun s : ℝ => Theta d L g ((s : ℂ) * μ) a b)
      (μ * (Theta d L g ((t : ℂ) * μ) * SB d L g * Theta d L g ((t : ℂ) * μ)) a b) t := by
  have hlin : HasDerivAt (fun ζ : ℂ => ζ * μ) μ (t : ℂ) := by
    simpa using HasDerivAt.mul_const (hasDerivAt_id ((t : ℂ))) μ
  have hg := HasDerivAt.comp (t : ℂ) (hasDerivAt_Theta_apply d L g hS hξ a b) hlin
  have := HasDerivAt.comp_ofReal hg
  simpa [Function.comp_def, mul_comm] using this

end RBM
