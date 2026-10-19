/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.AnpKey2
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.GroupWithZero.Basic

/-!
# `lem:Anp_key_gh`, Case (I) of the induction step: Cauchy-Schwarz at the fixed vertex

Paper: proof of Lemma 7.24 (`lem:Anp_key_gh`), Case (I) of the induction step (an internal vertex
`α_q` with two ending edges): the sum over `x` of the product `ξ(e₁, x) ξ(e₂, x)` of the two
factors at the fixed vertex is bounded by Cauchy-Schwarz (`2xy ≤ x² + y²`).

* `anpKey3_sum_xx`: for a nonnegative kernel `ξ` whose squared row sums are bounded by `θ`,
  `Σ_{x ∈ R} ξ(e₁, x) ξ(e₂, x) ≤ θ` for every finite set `R` and rows `e₁`, `e₂`.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.style.show false

namespace RBM.Graph

open RBM RBM.Gauss RBM.Gauss.Sizes

section CS

/-- `Σ_x ξ(e₁, x) ξ(e₂, x) ≤ θ` from `2xy ≤ x² + y²` and `Σ_β ξ_{αβ}² ≤ θ` for the rows `e₁` and `e₂`. -/
theorem anpKey3_sum_xx {ι : Type*} [Fintype ι] (ξ : ι → ι → ℝ) (θ : ℝ)
    (hξ : ∀ α β, 0 ≤ ξ α β) (hrow : ∀ α, ∑ β, ξ α β ^ 2 ≤ θ) (R : Finset ι) (e₁ e₂ : ι) :
    ∑ x ∈ R, ξ e₁ x * ξ e₂ x ≤ θ := by
  have h1 : ∑ x ∈ R, ξ e₁ x * ξ e₂ x ≤ ∑ x, ξ e₁ x * ξ e₂ x :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ R)
      (fun x _ _ => mul_nonneg (hξ _ _) (hξ _ _))
  have h2 : ∑ x, ξ e₁ x * ξ e₂ x ≤ ∑ x, (ξ e₁ x ^ 2 + ξ e₂ x ^ 2) / 2 :=
    Finset.sum_le_sum fun x _ => by
      have := two_mul_le_add_sq (ξ e₁ x) (ξ e₂ x)
      linarith
  have h3 : ∑ x, (ξ e₁ x ^ 2 + ξ e₂ x ^ 2) / 2 = (∑ x, ξ e₁ x ^ 2 + ∑ x, ξ e₂ x ^ 2) / 2 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib]
  have h4 := hrow e₁
  have h5 := hrow e₂
  linarith

end CS

end RBM.Graph
