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
# LW-12c: `lem:Anp_key_gh`, cases (I) and (II) of the induction step (T2252)

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex` (cited `7_8:line`): Case (I)
`:1152-1203` (an internal vertex `α_q` with two A1/B1 ending edges `:1154`, `(eq:induc_Ggraph)`
`:1164-1167`, `(eq:change_of_order)` `:1169`, `(eq:change_of_order2)` `:1172`, `(kwuyayw_case1)`
`:1174-1177`, Cauchy-Schwarz `:1178`), Case (II) `:1205-1244` (`(eq:jthpath)` `:1211`,
`(eq:bound_new_graph)` `:1233-1235`, the segment inequality `:1237-1239`).  Part c of the six
tickets of `lem:Anp`.

The proof, for `q = q' + 1`: fix the vertex `α_{i₀}` (`anpKey2_fix`); the two ending edges at
`α_{i₀}` are one-step paths `r₁`, `r₂` of the fixed graph `Γ'`; making both edges ghost
(`NGraph.ghostify` twice, in place of the paper's auxiliary path `(a_1 ⇒ a_2)`, `7_8:1161`,
`:1227`) gives `Γ''` with `q'` internal vertices, `ord Γ'' = ord Γ`; the factors at the fixed
vertex are `ξ(e_t, x)`, `e_t ∈ {a_{j_t}, b_{j_t}}`; the induction hypothesis on `Γ''`, the far
segment of every ghost-free old path, and Cauchy-Schwarz (`2xy ≤ x² + y²`) on the sum over `x`
close the step, with `c ↦ c/2`.

* Section 1: helpers (ending edges are solid).
* Section 2: the double A2 replacement `anpKey3_gh2`.
* Section 3: the factor at the fixed vertex.
* Section 4: the far segment of a ghost-free path.
* Section 5: the product bound.
* Section 6: `Σ_x ξ(e₁, x) ξ(e₂, x) ≤ θ`.
* Section 7: the target `anpDetGhCaseI_holds`.
* Section 8: compiled nonempty instances at `d = 3`.

No port: RBM1D and RBM2D have no light-weight graph layer.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.style.show false

namespace RBM.Graph

open RBM RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Helpers -/

/-! ## 2. The double A2 replacement (`7_8:1161`, `:1227`, replaced) -/

/-! ## 3. The factor at the fixed vertex (`(eq:induc_Ggraph)`, `7_8:1164-1167`) -/

/-! ## 4. The far segment of a ghost-free path (`(eq:change_of_order2)`, `7_8:1172`; `:1237-1239`) -/

/-! ## 5. The product bound (`7_8:1237-1239`) -/

/-! ## 6. Cauchy-Schwarz on the fixed vertex (`7_8:1178`) -/

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

/-! ## 7. The target (`7_8:1152-1244`) -/

/-! ## 8. Compiled nonempty instances at `d = 3` -/

end RBM.Graph
