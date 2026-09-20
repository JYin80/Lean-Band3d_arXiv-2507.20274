/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Gauss.Stein

/-!
# Towards Stein's identity for the matrix, by resampling one coordinate

The route to the matrix form of Stein's identity avoids disintegration entirely.  Write
`upd c (ω, t)` for `ω` with its `c`-th coordinate replaced by `t`.  Because the coordinates
of the Gaussian ensemble are independent and the `c`-th one has law `gaussianReal 0 v_c`,
replacing it by an independent sample of its own law leaves the measure invariant:

  `(P ⊗ γ_c).map (upd c) = P`.

Both sides of Stein's identity are then pushed through that map, Fubini on the product
separates the coordinate `t` from the rest, and the inner integral is the one-dimensional
complex identity of `Gauss/Stein.lean` (Q43a).  **Independence enters exactly once**, in
that invariance, and it is checked on measurable boxes.

## What is here

* `RBM.Gauss.integral_mul_gaussianReal_complex'` : the one-dimensional complex identity
  with **no hypothesis on the variance**.  At `v = 0` the Gaussian is a Dirac mass at `0`
  and both sides vanish, so the degenerate case needs no separate treatment downstream --
  which is one of the two reasons the resampling route is preferable to Fubini.
* `RBM.Gauss.upd` and its measurability and continuity, stated for an arbitrary index type.
  These are facts about `Function.update`, not about the ensemble, so they are proved here
  once and will apply to whatever index type the model ends up using.

## What is missing, and why

The invariance `(P ⊗ γ_c).map (upd c) = P` and the matrix identity itself need the Gaussian
band-matrix **model** -- the measure `P` on `Z_L^d`-indexed entries with variance profile
`S^(B)` -- which this project does not have yet.  It is not a port: `RBM1D/Gauss/Model.lean`
(489 lines) is built on the one-dimensional index set, whereas here the entries are indexed
by the lattice `RBM.Zd d L` and the variance profile is `RBM.SB`.  See `docs/QUEUE.md`, Q48.
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-! ### Stein in one real variable, with no restriction on the variance -/

/-- The complex one-dimensional Stein identity without the hypothesis `v ≠ 0`: at `v = 0`
the Gaussian is a Dirac mass at `0` and both sides vanish. -/
theorem integral_mul_gaussianReal_complex' {var : ℝ≥0} {f f' : ℝ → ℂ} {C : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf'c : Continuous f')
    (hb : ∀ x, ‖f x‖ ≤ C) (hb' : ∀ x, ‖f' x‖ ≤ C) :
    ∫ x : ℝ, (x : ℂ) * f x ∂(gaussianReal 0 var)
      = ((var : ℝ) : ℂ) * ∫ x : ℝ, f' x ∂(gaussianReal 0 var) := by
  by_cases hv : var = 0
  · subst hv
    simp [gaussianReal_zero_var]
  · exact RBM.integral_mul_gaussianReal_complex hv hf hf'c hb hb'

/-! ### Updating one coordinate

Nothing here knows about the ensemble; these are facts about `Function.update` on a
product, stated for an arbitrary index type so that they survive whatever indexing the
model chooses. -/

variable {ι : Type*} [DecidableEq ι]

/-- `upd c (ω, t)` is `ω` with its `c`-th coordinate replaced by `t`. -/
def upd (c : ι) (p : (ι → ℝ) × ℝ) : ι → ℝ := Function.update p.1 c p.2

@[simp] theorem upd_self (c : ι) (p : (ι → ℝ) × ℝ) : upd c p c = p.2 :=
  Function.update_self _ _ _

theorem upd_of_ne (c : ι) (p : (ι → ℝ) × ℝ) {i : ι} (h : i ≠ c) : upd c p i = p.1 i :=
  Function.update_of_ne h _ _

theorem measurable_upd (c : ι) : Measurable (upd (ι := ι) c) := by
  refine Measurable.of_eval fun i => ?_
  by_cases h : i = c
  · subst h
    simpa only [upd_self] using measurable_snd
  · simpa only [upd_of_ne c _ h, Function.comp_def] using
      (measurable_pi_apply i).comp measurable_fst

/-- Moving one coordinate is continuous in the product topology. -/
theorem continuous_update_coord (c : ι) (ω : ι → ℝ) :
    Continuous fun t : ℝ => Function.update ω c t := by
  refine continuous_pi fun i => ?_
  by_cases h : i = c
  · subst h
    simpa only [Function.update_self] using continuous_id'
  · simpa only [Function.update_of_ne h] using continuous_const

end RBM.Gauss
