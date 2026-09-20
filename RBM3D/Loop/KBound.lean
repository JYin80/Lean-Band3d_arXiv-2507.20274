/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Loop.TreeThree

/-!
# `ML:Kbound`, and the "additional modifications to handle `d ≥ 3`"

`ML:Kbound` is the upper bound on `K`-loops:
`max_σ max_a |K^(n)_{t,σ,a}| ≺ (W^{-d} B_{t,0})^{n-1}` for every `n` and `t ∈ [0,1)`.

Appendix A.5 says its proof "is analogous to that of Lemma 3.11 in `[YY_25]`, but requires
additional modifications to handle the higher-dimensional setting `d ≥ 3`".  This file
**locates that modification** and proves it.

## Where `d ≥ 3` enters

The proof reduces to `(eq:ind-step-bound)`, and there to case (ii).4: two of the external
edges are hit by the antisymmetric part `f₁` of the long-edge decomposition, each
contributing `(|a-b|^{d-1}+1)^{-1}`, and one has to sum the product over `b`.  The paper's
step is

  `(|x|^{d-1}+1)^{-1}(|y|^{d-1}+1)^{-1}`
      `≲ (|x|^d+1)^{-1}(|y|^{d-2}+1)^{-1} + (|x|^{d-2}+1)^{-1}(|y|^d+1)^{-1}`,

after which the lattice sum over `b` converges.  `RBM.Loop.inv_pow_pair_le` is that step,
with the constant `2` and no hypothesis beyond `0 ≤ x, y`.

**Why the asymmetric split, rather than bounding one `(d-1)`-factor by `1`?**  Because the
naive route diverges: `Σ_b (|a-b|^d+1)^{-1}` over `Z_L^d` is of order `log L`, not `O(1)`.
The `d-2` left over in the other factor is exactly what makes the sum converge, and it is
`≥ 1` only when `d ≥ 3` -- at `d = 2` the second factor is `1` and the logarithm is back,
at `d = 1` neither exponent is of any use.  That is the "additional modification": in
`[YY_25]`'s `d = 1` setting `|·|^{d-1} = 1` carries no decay at all, so the whole case (ii)
has to be run differently.

`RBM.Loop.not_inv_pow_pair_le_single` records, machine-checked, that one term of the split
does not suffice: the case distinction `x ≤ y` / `y ≤ x` is not cosmetic.

## What is here

* `RBM.Loop.KLoopBound` : `ML:Kbound` stated verbatim, as a `Prop` (`docs/QUEUE.md`, Q24).
  It is *not* proved here: the proof needs the molecule layer (`Σ^(π)`, the sum-zero
  property) which the project does not have yet.  The paper *does* prove it -- A.5 says
  "For the reader's convenience, we provide the proof below" -- so in the audit
  (`RBM3D/Test/Axioms.lean`) this is an **owed** premise, a debt of this formalization,
  not one of the results the paper borrows.
* `RBM.Loop.inv_pow_pair_le`, `RBM.Loop.not_inv_pow_pair_le_single` : the `d ≥ 3` step and
  the negative test.
-/

namespace RBM.Loop

open Finset

/-! ### The statement -/

variable (d L : ℕ) [NeZero L] (W : ℕ) (g : ℝ)

/-- **`ML:Kbound`**: for every `n` and every `t ∈ [0,1)`,
`max_σ max_a |K^(n)_{t,σ,a}| ≺ (W^{-d} B_{t,0})^{n-1}`.

`≺` is read as in `RBM.DetDom`: for every `τ > 0` there is a constant `C` with
`… ≤ C L^τ (W^{-d} B_{t,0})^{n-1}`, uniformly in `L`, `t`, `σ` and `a` (the paper's `≺`
for deterministic quantities, Definition 2.1(ii), in the uniform form of
`docs/paper-deltas.md`).  The constant may depend on `d`, `n`, `g` and `τ`.

Carried as a hypothesis, in the repository's usual form: the proof in Appendix A.5 runs
through the molecule decomposition `(eq:wtKpi)` and the sum-zero property
`(eq:Sigma-empty-sum-zero)`, neither of which is formalized.  It is an *owed* premise, not
a borrowed one: the paper gives the proof. -/
def KLoopBound (K : ℝ → LoopIdx (Zd d L) → ℂ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ τ : ℝ, 0 < τ → ∃ C > (0 : ℝ),
    ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ : List Bool) (a : List (Zd d L)),
      σ.length = n → a.length = n →
      ‖K t ⟨σ, a⟩‖ ≤ C * (L : ℝ) ^ τ * ((((W : ℝ) ^ d)⁻¹ * Bparam d L g t 0) ^ (n - 1))

variable {d L W g}

/-! ### The `d ≥ 3` step -/

/-- **The "additional modification to handle `d ≥ 3`"**, in the dimensionless form
`d = k + 2`: a product of two `(d-1)`-decays is dominated by a `d`-decay times a
`(d-2)`-decay, in one order or the other.

`(|x|^{d-1}+1)^{-1}(|y|^{d-1}+1)^{-1}
  ≤ 2[(|x|^d+1)^{-1}(|y|^{d-2}+1)^{-1} + (|x|^{d-2}+1)^{-1}(|y|^d+1)^{-1}]`. -/
theorem inv_pow_pair_le (k : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ((x ^ (k + 1) + 1) * (y ^ (k + 1) + 1))⁻¹
      ≤ 2 * (((x ^ (k + 2) + 1) * (y ^ k + 1))⁻¹
        + ((x ^ k + 1) * (y ^ (k + 2) + 1))⁻¹) := by
  -- the ordered half: for `x ≤ y` the first term already dominates
  have half : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → u ≤ v →
      (u ^ (k + 2) + 1) * (v ^ k + 1) ≤ 2 * ((u ^ (k + 1) + 1) * (v ^ (k + 1) + 1)) := by
    intro u v hu hv huv
    have hu1 : 0 ≤ u ^ (k + 1) := by positivity
    have hv1 : 0 ≤ v ^ (k + 1) := by positivity
    have hvk : v ^ k ≤ v ^ (k + 1) + 1 := by
      rcases le_total v 1 with h | h
      · have : v ^ k ≤ 1 := pow_le_one₀ hv h
        linarith
      · calc v ^ k ≤ v ^ (k + 1) := pow_le_pow_right₀ h (by omega)
          _ ≤ v ^ (k + 1) + 1 := by linarith
    have hstep : u ^ (k + 2) ≤ u ^ (k + 1) * v := by
      have : u ^ (k + 2) = u ^ (k + 1) * u := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left huv hu1
    have huv1 : u ^ (k + 1) * v ≤ u ^ (k + 1) * (v ^ (k + 1) + 1) := by
      refine mul_le_mul_of_nonneg_left ?_ hu1
      rcases le_total v 1 with h | h
      · linarith
      · calc v ≤ v ^ (k + 1) := le_self_pow₀ h (by omega)
          _ ≤ v ^ (k + 1) + 1 := by linarith
    have hprod : u ^ (k + 2) * v ^ k ≤ u ^ (k + 1) * v ^ (k + 1) := by
      calc u ^ (k + 2) * v ^ k = u ^ (k + 1) * u * v ^ k := by ring
        _ ≤ u ^ (k + 1) * v * v ^ k := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left huv hu1) (by positivity)
        _ = u ^ (k + 1) * v ^ (k + 1) := by ring
    nlinarith [mul_nonneg hu1 hv1]
  have key : ∀ A B : ℝ, 0 < A → 0 < B → B ≤ 2 * A → A⁻¹ ≤ 2 * B⁻¹ := by
    intro A B hA hB hBA
    have h : 2 * B⁻¹ - A⁻¹ = (2 * A - B) / (A * B) := by field_simp
    have h2 : (0 : ℝ) ≤ (2 * A - B) / (A * B) := div_nonneg (by linarith) (by positivity)
    linarith
  have hxy : (0 : ℝ) < (x ^ (k + 1) + 1) * (y ^ (k + 1) + 1) := by positivity
  rcases le_total x y with h | h
  · have hpos : (0 : ℝ) < (x ^ (k + 2) + 1) * (y ^ k + 1) := by positivity
    have hrest : (0 : ℝ) ≤ ((x ^ k + 1) * (y ^ (k + 2) + 1))⁻¹ := by positivity
    have hkey := key _ _ hxy hpos (half x y hx hy h)
    linarith
  · have hpos : (0 : ℝ) < (y ^ (k + 2) + 1) * (x ^ k + 1) := by positivity
    have hrest : (0 : ℝ) ≤ ((x ^ (k + 2) + 1) * (y ^ k + 1))⁻¹ := by positivity
    have hcomm : (x ^ k + 1) * (y ^ (k + 2) + 1) = (y ^ (k + 2) + 1) * (x ^ k + 1) := by ring
    have hcomm' : (x ^ (k + 1) + 1) * (y ^ (k + 1) + 1)
        = (y ^ (k + 1) + 1) * (x ^ (k + 1) + 1) := by ring
    have hxy' : (0 : ℝ) < (y ^ (k + 1) + 1) * (x ^ (k + 1) + 1) := by positivity
    have hkey := key _ _ hxy' hpos (half y x hy hx h)
    rw [hcomm, hcomm']
    linarith

/-- **Negative test: one term of the split does not suffice.**  At `d = 3`, `x = 3`,
`y = 0` the first term of `inv_pow_pair_le` is already too small, so the case distinction
`x ≤ y` / `y ≤ x` is not cosmetic. -/
theorem not_inv_pow_pair_le_single :
    ¬ ∀ (k : ℕ) (x y : ℝ), 0 ≤ x → 0 ≤ y →
        ((x ^ (k + 1) + 1) * (y ^ (k + 1) + 1))⁻¹
          ≤ 2 * ((x ^ (k + 2) + 1) * (y ^ k + 1))⁻¹ := by
  intro h
  have := h 1 3 0 (by norm_num) (by norm_num)
  norm_num at this

end RBM.Loop
