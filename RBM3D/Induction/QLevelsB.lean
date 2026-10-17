/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.QLevelsA
import RBM3D.Induction.ScaleFacts
import RBM3D.Induction.Step2Core
import RBM3D.Induction.Step2Events
import RBM3D.Induction.AzumaProxyN

/-!
# The decay clause of `GoodSetN` in the shape of `altB45N_levelM`

Paper: (4.35) `int_K-L+Q` (`ℬ₀…ℬ₅`), Claim 4.9 (`lem_+Q`) with (4.32) `normQA`, the integrand
`𝒬_v Σ_{k=1}^3 ℬ_k(v)` in the proof of Lemma 4.17 (Subsection 4.5 `subsec:support`), (4.59) `y27kasdfg`,
(4.60) `A5`, (4.61) `A4`.

RBM2D's `AltLevelsQ` is used in its deterministic, per-matrix form: no per-time stochastic good set, no
`≺`, no lift, no probability.  `GoodSetN` membership is a hypothesis (pathwise on `{j < τ}`).

* `goodSetN_LKM_far`: the decay clause of `GoodSetN` in the `hF` shape of `altB45N_levelM` (window
  `ωf = W^{τ'}`, `Fv = W^{-D'}`);
* `goodSetNg_LKM_far`: its twin over a carrier `Cm : Step2Mat sz` (namespace `RBM.Ind`, `open RBM.BA`).

Helpers are `private` or prefixed `QLevelsB_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.BA

/-! ## 1. The decay clause of `GoodSetN` as an entry bound -/

/-- **`goodSetN_LKM_far`** (the decay clause of `GoodSetN` in the `hF` shape of `altB45N_levelM`, window
`ωf = W^{τ'}`, `Fv = W^{-D'}`). -/
theorem goodSetN_LKM_far :
    ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (E u : ℝ) (k : ℕ) (Γ Λ Φ τ' D' : ℝ)
      (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      H ∈ sz.GoodSetN n E u k Γ Λ Φ τ' D' → ∀ j : ℕ, 1 ≤ j → j ≤ 2 * k + 2 →
        ∀ (σ' : Fin j → Bool) (a' : Fin j → Zd d (sz.L n)),
          ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a' : ℝ) →
            ‖sz.STLKM n E u H σ' a'‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D') := by
  intro d sz n E u k Γ Λ Φ τ' D' H hH j hj1 hj σ' a' hfar
  have h := hH.2.2.1 j hj1 hj σ' a' hfar
  have e : sz.STLKM n E u H σ' a' =
      loopFine d (sz.L n) (sz.W n) H (zt E u) σ' a' - STKloop sz n E u σ' a' := rfl
  rw [e]
  exact le_trans (le_add_of_nonneg_left (norm_nonneg _)) h

/-- **`goodSetNg_LKM_far`** (band `goodSetN_LKM_far`): the decay clause of `GoodSetNg` over a carrier in the `hF` shape of `altB45Ng_levelM`
(window `ωf = W^{τ'}`, `Fv = W^{-D'}`); `STLKMg = LM - K`. -/
theorem goodSetNg_LKM_far :
    ∀ (d : ℕ) (sz : Sizes d) (Cm : Step2Mat sz) (n : ℕ) (u : ℝ) (k : ℕ) (Γ Λ Φ τ' D' : ℝ)
      (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      GoodSetNg Cm n u k Γ Λ Φ τ' D' H → ∀ j : ℕ, 1 ≤ j → j ≤ 2 * k + 2 →
        ∀ (σ' : Fin j → Bool) (a' : Fin j → Zd d (sz.L n)),
          ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a' : ℝ) →
            ‖STLKMg Cm n u H σ' a'‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D') := by
  intro d sz Cm n u k Γ Λ Φ τ' D' H hH j hj1 hj σ' a' hfar
  have h := hH.2.2.1 j hj1 hj σ' a' hfar
  exact le_trans (le_add_of_nonneg_left (norm_nonneg _)) h


end RBM.Ind

end
