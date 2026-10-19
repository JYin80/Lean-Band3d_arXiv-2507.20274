/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.HierAlgebra

/-!
# The general-`n` `(𝓛 - 𝒦)` hierarchy identity

The drift part of the loop hierarchy for `𝓛 - 𝒦` (`eq_L-Keee`, (3.8)), for loops of every length
`k ≥ 2` and every size index `n` of a size sequence `sz : Sizes d`, at coupling `g = sz.lam n`.

* `STLoopGenNForm d` : the general-`n` loop-generator identity `genMat(𝓛_I) = pair + 𝓔^{G̃}`
  (`eq:mainStoflow`, (2.47), drift part).  It is the explicit hypothesis of
  `hierarchyN_of_loopGenN`; `stLoopGenNForm_holds` (`Induction/LoopGenN.lean`) proves it.
* `HierarchyN d` : the drift part of (3.8):
  `genMat(𝓛) - ∂_u 𝒦 = Θ^{(k)}_{u,σ}(𝓛-𝒦) + Σ_{l=3}^k [𝒦^{(l)} ∼ (𝓛-𝒦)]^{(k)} + 𝓔^{LK×LK} + 𝓔^{G̃}`,
  the shape of `STgDriftN` at `H = M` plus `genMat`.
* `hierarchyN_of_loopGenN` : `STLoopGenNForm d → HierarchyN d`, from `loopDrift_sub_K_deriv_n`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Ind

open Matrix RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **The general-`n` loop generator (`eq:mainStoflow`, (2.47), drift part)**: for Hermitian `M`
and every loop `(σ, a)` of length `k ≥ 2`,
`genMat(𝓛_{σ,a}) = W^d Σ_{k<l} Σ_{a,b} 𝓛 S^{(B)} 𝓛 + 𝓔^{(G̃)}` (`STllPairN`, `STegtM`), with
`g = sz.lam n`.  It is a hypothesis of `hierarchyN_of_loopGenN` and is proved as
`stLoopGenNForm_holds` (`Induction/LoopGenN.lean`). -/
def STLoopGenNForm (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian →
      ∀ (k : ℕ), 2 ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
        genMat d (sz.L n) (sz.W n) (sz.lam n) E u M (loopOf σ a) =
          sz.STllPairN n E u M (loopOf σ a) + sz.STegtM n E u M (loopOf σ a)

/-- **The general-`n` hierarchy identity `HierarchyN`** ((3.8) `eq_L-Keee`, drift part;
(3.9) `DefKsimLK`, (3.10) `def_ELKLK`, Definition 3.3 `DefTHUST`): for
Hermitian `M` and every loop `(σ, a)` of length `k ≥ 2`,
`genMat(𝓛) - ∂_u 𝒦 = Θ^{(k)}_{u,σ}∘(𝓛-𝒦) (a) + Σ_{l=3}^k [𝒦^{(l)}∼(𝓛-𝒦)]^{(k)} + 𝓔^{LK×LK} + 𝓔^{G̃}`.
Here `g = sz.lam n`, and the right side is `STgDriftN` of `Step2Defs` at `H = M`. -/
def HierarchyN (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian →
      ∀ (k : ℕ), 2 ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
        genMat d (sz.L n) (sz.W n) (sz.lam n) E u M (loopOf σ a) -
            deriv (fun v : ℝ => sz.STKloop n E v σ a) u =
          ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma E (σ i)) u
              (fun b => sz.STLKIM n E u M (loopOf σ b)) a +
            ∑ l ∈ Finset.Icc 3 k, sz.STksimLKM n E u M l (loopOf σ a) +
            sz.STelklkM n E u M (loopOf σ a) + sz.STegtM n E u M (loopOf σ a)

/-- **`hierarchyN_of_loopGenN`**: the general-`n` hierarchy identity from the general-`n`
loop generator (`STLoopGenNForm`) and the matrix-level identity `loopDrift_sub_K_deriv_n`. -/
theorem hierarchyN_of_loopGenN (d : ℕ) : STLoopGenNForm d → HierarchyN d := by
  intro h sz n E hE u hu0 hu1 M hM k hk σ a
  rw [h sz n E hE u hu0 hu1 M hM k hk σ a]
  exact loopDrift_sub_K_deriv_n sz n E hE u hu0 hu1 M hk σ a

end RBM.Ind

end
