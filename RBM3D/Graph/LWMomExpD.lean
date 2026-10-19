/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWMomExp

/-!
# The domain-restricted value `lwMomExp_valOnD` and `NGraph.valOn` on `D^q`

The domain-restricted value `lwMomExp_valOnD` of a normal graph agrees with the graph value
`NGraph.valOn` summed over the product set `D^q = piFinset D`.
-/

namespace RBM.Graph

/-- **Identity** (proof of Lemma 7.26 `lem:LW_moment_exp_near`): the domain-restricted value
`lwMomExp_valOnD Γ ξ a b D` equals `NGraph.valOn` restricted to `D^q = piFinset D`.
It bridges the near bound (stated with `lwMomExp_valOnD`) and the far bound `AnpFarAndAt`
(stated with `NGraph.valOn`) in the domain decomposition of Lemma 7.2 (`lem:LW_moment_exp`). -/
theorem lwMomExp_valOnD_eq_valOn {p q : ℕ} {ι : Type*}
    (Γ : NGraph p q) (ξ : ι → ι → ℝ) (a b : Fin p → ι) (D : Finset ι) :
    lwMomExp_valOnD Γ ξ a b D =
      Γ.valOn ξ a b (Fintype.piFinset (fun _ : Fin q => D)) := by
  unfold lwMomExp_valOnD NGraph.valOn
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [← List.ofFn_getElem_eq_map, List.prod_ofFn]
  rfl

end RBM.Graph
