/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWMomExp

/-!
# LW-13b-1: the identity twin `lwMomExp_valOnD = NGraph.valOn` on `D^q`
-/

namespace RBM.Graph

/-- **LW-13b-1 identity twin** (`7_8:1636`, DECISIONS §123): the domain-restricted value
`lwMomExp_valOnD Γ ξ a b D` equals `NGraph.valOn` restricted to `D^q = piFinset D`.
Bridges `AnpDetNearAt` (near, `lwMomExp_valOnD`) and `AnpFarAndAt` (far, `NGraph.valOn`)
in the domain decomposition of `lem:LW_moment_exp`. -/
theorem lwMomExp_valOnD_eq_valOn {p q : ℕ} {ι : Type*}
    (Γ : NGraph p q) (ξ : ι → ι → ℝ) (a b : Fin p → ι) (D : Finset ι) :
    lwMomExp_valOnD Γ ξ a b D =
      Γ.valOn ξ a b (Fintype.piFinset (fun _ : Fin q => D)) := by
  unfold lwMomExp_valOnD NGraph.valOn
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [← List.ofFn_getElem_eq_map, List.prod_ofFn]
  rfl

/-- Compiled nonempty instance: `p = 1`, `q = 2`, `ι = Fin 3`, proper subdomain `D = {0, 1}`,
a solid edge `a₀–α₀`, a solid edge `α₀–α₁`, a ghost edge `α₁–b₀`, an asymmetric weight `ξ`. -/
example :
    lwMomExp_valOnD
      (⟨[⟨false, Sum.inl (Sum.inl 0), Sum.inr 0⟩, ⟨false, Sum.inr 0, Sum.inr 1⟩,
          ⟨true, Sum.inr 1, Sum.inl (Sum.inr 0)⟩], fun _ => []⟩ : NGraph 1 2)
      (fun x y : Fin 3 => ((x : ℕ) + 2 * (y : ℕ) + 1 : ℝ)) (fun _ => 0) (fun _ => 2)
      ({0, 1} : Finset (Fin 3)) =
    NGraph.valOn
      (⟨[⟨false, Sum.inl (Sum.inl 0), Sum.inr 0⟩, ⟨false, Sum.inr 0, Sum.inr 1⟩,
          ⟨true, Sum.inr 1, Sum.inl (Sum.inr 0)⟩], fun _ => []⟩ : NGraph 1 2)
      (fun x y : Fin 3 => ((x : ℕ) + 2 * (y : ℕ) + 1 : ℝ)) (fun _ => 0) (fun _ => 2)
      (Fintype.piFinset (fun _ : Fin 2 => ({0, 1} : Finset (Fin 3)))) :=
  lwMomExp_valOnD_eq_valOn _ _ _ _ _

end RBM.Graph
