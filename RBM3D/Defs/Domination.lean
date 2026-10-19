/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Deterministic stochastic domination `≺`

The deterministic convention that follows (1.13) `stoch_domination` of *Delocalization of
non-mean-field random matrices in dimensions `d ≥ 3`* (arXiv:2507.20274): for two
deterministic `N`-dependent quantities, `ξ ≺ ζ` if `ξ ≤ N^τ ζ` for every `τ > 0` and all
sufficiently large `N`.

The definition (1.13) is uniform in a possibly `N`-dependent parameter `u ∈ U(N)`, and the
deterministic estimates of the paper -- `(prop:BD1)`, `(prop:BD2)`, `(prop:ThfadC0)`, which hold
uniformly in the lattice points -- are used in that uniform form.  We therefore take the uniform
version `UnifDetDom` as the basic notion, with `N₀` independent of `u`, and obtain the scalar
version `DetDom` as the case of a one-point parameter set.

The definition does not require the quantities to be non-negative; the lemmas that need
non-negativity (as the paper assumes throughout) take it as an explicit hypothesis.

## Main definitions

* `UnifDetDom f g` : `f ≺ g` uniformly in `u ∈ U(N)`
* `DetDom f g`     : `f ≺ g` for scalar sequences; scoped notation `f ≺ g`

## Main results

* `eventually_le_rpow` : for `τ > 0`, `N^τ` eventually exceeds any fixed constant
* `UnifDetDom.rpow_half_mul_rpow_half` : `N^{τ/2} N^{τ/2} = N^τ`
* `detDom_log_pow` : `(log N)^m ≺ 1`
-/

namespace RBM

open Filter

/-- The definition (1.13) `stoch_domination`, uniformly in a possibly `N`-dependent parameter
`u ∈ U(N)`: `f ≺ g` if for every `τ > 0` there is `N₀` with `f(N, u) ≤ N^τ g(N, u)` for all
`N ≥ N₀` and all `u ∈ U(N)`. -/
def UnifDetDom {U : ℕ → Type*} (f g : ∀ N, U N → ℝ) : Prop :=
  ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ u, f N u ≤ (N : ℝ) ^ τ * g N u

/-- The deterministic convention after (1.13): for two deterministic `N`-dependent quantities,
`f ≺ g` if `f N ≤ N^τ g N` for every `τ > 0` and all sufficiently large `N`. -/
def DetDom (f g : ℕ → ℝ) : Prop :=
  UnifDetDom (U := fun _ => Unit) (fun N _ => f N) (fun N _ => g N)

@[inherit_doc] scoped infix:50 " ≺ " => DetDom

/-- For `τ > 0` the factor `N^τ` eventually exceeds any fixed constant. -/
theorem eventually_le_rpow (C : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in atTop, C ≤ (N : ℝ) ^ τ :=
  ((tendsto_rpow_atTop hτ).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop C

namespace UnifDetDom

/-- Splitting `N^τ = N^{τ/2} N^{τ/2}`. -/
theorem rpow_half_mul_rpow_half (N : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) = (N : ℝ) ^ τ := by
  rw [← Real.rpow_add' (Nat.cast_nonneg N) (by linarith), add_halves]

end UnifDetDom

/-! ### Logarithmic factors are invisible to `≺`

The paper writes `≺` rather than `≲` exactly where a power of `log W` has been absorbed.
The lemma below does the absorbing: for every `τ > 0` a polynomial in `log N` is eventually
below `N^τ`.  An instance is (7.63) `eq:key_T_reudce`, where `ℓ ≤ (log W)^{10} ℓ_t` costs a
factor `(log W)^{20}`.
-/

/-- **`(log N)^m ≺ 1`**: any fixed power of a logarithm is dominated. -/
theorem detDom_log_pow (m : ℕ) : DetDom (fun N : ℕ => Real.log N ^ m) (fun _ => 1) := by
  intro τ hτ
  have h0 := (_root_.isLittleO_log_rpow_rpow_atTop (m : ℝ) hτ).def (c := 1) one_pos
  have h1 : ∀ᶠ N : ℕ in Filter.atTop,
      ‖Real.log (N : ℝ) ^ (m : ℝ)‖ ≤ 1 * ‖((N : ℝ)) ^ τ‖ :=
    tendsto_natCast_atTop_atTop.eventually h0
  filter_upwards [h1, Filter.eventually_ge_atTop 1] with N hN hN1 _
  have hlog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN1)
  have hrpow : Real.log (N : ℝ) ^ (m : ℝ) = Real.log (N : ℝ) ^ m := Real.rpow_natCast _ m
  have hN0 : (0 : ℝ) ≤ (N : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg N) τ
  rw [hrpow, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hN0, one_mul] at hN
  simpa using hN

end RBM
