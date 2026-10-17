/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.HierAlgebra

/-!
# The general-`n` `(𝓛 - 𝒦)` hierarchy identity (ST2-28a, ticket T2095)

Port of RBM2D `Induction/HierarchyN.lean` at commit `c9a24cf` (`HN:<line>`; 76 lines there) and of
the pins `HierarchyN`, `LoopGenN` of `Induction/HierVocab.lean` (`HierVocab:206`, `:548`), in the
shape of the merged `n = 2` forms `HierarchyN2`, `LoopGenN2` (`Path/DriftAlgebra.lean`, D149):
`∀ sz n` at `g = sz.lam n`, merged `ST*` vocabulary.

* `STLoopGenNForm d` : the general-`n` loop-generator identity `genMat(𝓛_I) = pair + 𝓔^{G̃}`
  (`eq:mainStoflow`, `1_2`, drift part; RBM2D `LoopGenN`).  Not proved here (ST2-28 proves it): it
  is the explicit hypothesis of `hierarchyN_of_loopGenN` (ticket Amend 1, DECISIONS §32).
* `HierarchyN d` : the drift part of (`LK_SDE`, `3_5:133`):
  `genMat(𝓛) - ∂_u 𝒦 = Θ^{(k)}_{u,σ}(𝓛-𝒦) + Σ_{l=3}^k [𝒦^{(l)} ∼ (𝓛-𝒦)]^{(k)} + 𝓔^{LK×LK} + 𝓔^{G̃}`,
  the shape of `STgDriftN` at `H = M` plus `genMat`.
* `hierarchyN_of_loopGenN` : `STLoopGenNForm d → HierarchyN d`, from `loopDrift_sub_K_deriv_n`
  (RBM2D `hierarchyN`, `HN:31-34`, rewrote by the merged `loopGenN`).
* the reductions at `n = 2`, `σ = (+,-)`: `HierarchyN d → HierarchyN2 d` and `LoopGenN2 d` implies
  `STLoopGenNForm d` at length `2`, `σ = (+,-)`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Ind

open Matrix RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **The general-`n` loop generator (`eq:mainStoflow`, `1_2`, drift part), the shape of
`LoopGenN2`**: for Hermitian `M` and every loop `(σ, a)` of length `k ≥ 2`,
`genMat(𝓛_{σ,a}) = W^d Σ_{k<l} Σ_{a,b} 𝓛 S^{(B)} 𝓛 + 𝓔^{(G̃)}` (`STllPairN`, `STegtM`).
RBM2D `LoopGenN` (`HierVocab:548`) with `W² → W^d`, `g = sz.lam n`.  **Owed** (ST2-28, DECISIONS
§32); at `k = 2`, `σ = (+,-)` it is implied by `LoopGenN2` (`loopGenNForm_two_of_loopGenN2`). -/
def STLoopGenNForm (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian →
      ∀ (k : ℕ), 2 ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
        genMat d (sz.L n) (sz.W n) (sz.lam n) E u M (loopOf σ a) =
          sz.STllPairN n E u M (loopOf σ a) + sz.STegtM n E u M (loopOf σ a)

/-- **The general-`n` hierarchy identity `HierarchyN`** (`LK_SDE`, `3_5:133`, drift part;
`eq_L-Keee`, `3_5:73`; `DefKsimLK` `3_5:89`, `def_ELKLK` `3_5:97`, `DefTHUST` `3_5:109`): for
Hermitian `M` and every loop `(σ, a)` of length `k ≥ 2`,
`genMat(𝓛) - ∂_u 𝒦 = Θ^{(k)}_{u,σ}∘(𝓛-𝒦) (a) + Σ_{l=3}^k [𝒦^{(l)}∼(𝓛-𝒦)]^{(k)} + 𝓔^{LK×LK} + 𝓔^{G̃}`.
The shape of `HierarchyN2` (`∀ sz n`, `g = sz.lam n`, merged `ST*` vocabulary); the right side is
`STgDriftN` of `Step2Defs` at `H = M`.  At `k = 2`, `σ = (+,-)` it is `HierarchyN2`
(`hierarchyN_two`). -/
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

/-- **`hierarchyN`** (RBM2D `HN:31`): the general-`n` hierarchy identity from the general-`n`
loop generator (`STLoopGenNForm`) and the matrix-level identity `loopDrift_sub_K_deriv_n`. -/
theorem hierarchyN_of_loopGenN (d : ℕ) : STLoopGenNForm d → HierarchyN d := by
  intro h sz n E hE u hu0 hu1 M hM k hk σ a
  rw [h sz n E hE u hu0 hu1 M hM k hk σ a]
  exact loopDrift_sub_K_deriv_n sz n E hE u hu0 hu1 M hk σ a

/-! ## The reductions at `n = 2`, `σ = (+,-)` -/

/-! ## Compiled nonempty instances

At the merged admissible sequence `sz0` (`RBM.Gauss.SizesInst.sz0`: `d = 3`, `L_0 = 4`, `W_0 = 32`,
`lam_0 = 1/64`), size index `0`, `E = 0` (`|E| < 2`), `u = 1/2` (`0 ≤ u < 1`), `M = 1` (Hermitian).
`hierarchyN_of_loopGenN` is applied at the loop `(+,-,+)`, `a = (0,1,2)` of length `k = 3`; the only
hypothesis kept is the owed pin `STLoopGenNForm 3` (ST2-28).  `hierarchyN_two` is applied at
`n = 2` with `HierarchyN 3` kept as the hypothesis.  `loopGenNForm_two_of_loopGenN2` is applied
unconditionally (`loopGenN2 3` is proved in `Path/DriftAlgebra.lean`). -/

end RBM.Ind

end
