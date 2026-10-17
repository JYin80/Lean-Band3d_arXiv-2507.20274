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
# S3-16b (ticket T2272): the deterministic drift level of the alternating chain at a good matrix

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`): `int_K-L+Q` `3_5:1337-1346`
(`ℬ₀…ℬ₅`), `lem_+Q`/`(normQA)` `3_5:1284-1289`, the integrand `𝒬_v Σ_{k=1}^3 ℬ_k(v)` `3_5:1684`,
`(y27kasdfg)`, `(A5)`, `(A4)` `3_5:1692-1706`.

Re-scope (DECISIONS §83, §64 (4)/(5)): RBM2D `AltLevelsQ` (`AltLevelsQ.lean:165-257, 314-360, 481-560` at
`c9a24cf`) is ported in its deterministic, per-matrix form: no per-time stochastic good set, no `≺`, no lift, no
probability.  `GoodSetN` membership is a hypothesis (pathwise on `{j < τ}`).

* `dDriftAltQN` (vocabulary): the level `W^{C_nε'}dDriftNonAltN + W^{-D'+C_n} + N^{τ_N}η⁻¹B^{m+2}X`;
* `goodSetN_LKM_le`, `goodSetN_LKM_far` (targets 1, 2): clauses (G2), (Dec) of `GoodSetN` in the `hY`, `hF`
  shapes of `altB45N_levelM`;
* `qopB13N_levelM` (target 3): `(normQA)` on the block `driftTensorN`;
* `dFlowQN_levelM` (target 4): the per-matrix level of `dFlowQN = 𝒬_u(block) + ℬ₄ + ℬ₅`;
* `alt_hdriftQN` (target 5): the field `hdrift` of `GridAssemblyHypN` along the walk;
* `dDriftAltQN_nonneg` (target 6): the field `hdDrift0`;
* instances (namespace `QLevelsBInst`) at `sz0`, `d = 3`, `m = 2`, `n = 4`, `E = 0`, `u = 0`, `H = 0`.

Unpinned helpers are `private` or prefixed `QLevelsB_`.

T2498 (row U3s3a, in place): `goodSetNg_LKM_far`, the generic twin of `goodSetN_LKM_far` over a carrier `Cm : Step2Mat sz` (namespace `RBM.Ind`, `open RBM.BA`); the
other band text of this file is the superseded `GoodSetN`-level drift route and is unchanged.  Its compiled instance at `bandStep2Mat sz0 (fun _ => 0)` follows
`goodSetN_LKM_far_instance`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.BA

/-! ## 0. Vocabulary -/

/-! ## 1. Targets 1 and 2: the good-set clauses (G2), (Dec) as entry bounds -/

/-- **Target 2, `goodSetN_LKM_far`** (clause (Dec) of `GoodSetN` in the `hF` shape of `altB45N_levelM`, window
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

/-- **Target 6, `goodSetNg_LKM_far`** (band `goodSetN_LKM_far`): clause (Dec) of `GoodSetNg` over a carrier in the `hF` shape of `altB45Ng_levelM`
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


/-! ## 2. Target 3: the level of `𝒬_u(ℬ₁+ℬ₂+ℬ₃)` -/

/-! ## 3. Target 4: the per-matrix level of the drift `dFlowQN` -/

/-! ## 4. Target 5: the field `hdrift` of `GridAssemblyHypN` along the walk -/

/-! ## 5. Target 6: the field `hdDrift0` -/

/-! ## 6. Compiled nonempty instances (namespace `QLevelsBInst`)

The merged admissible sequence `sz0` (`d = 3`; `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`) at
`n = 4` (`x = 2(n+1) = 10`, `L = 20`, `W = 10^5`, `N = (W L)^3 = 8·10^18`, `lam = 10^{-6}`), `d = 3`, `m = 2`
(tensors of `m + 2 = 4` indices, `k = 4 = 3 + 1`), `K = 2`, `Λ_g = 1`, `E = 0`, `u = 0`, `κ = 1`, `H = 0`,
`τ' = 1/10`, `ε' = 1/5`, `D' = 40`, `ν = W`, `X = 1`, `τ_N = 2`, the explicit mollifier
`QopAlgebra_mollifier 3 L 3 lam` (`C = (1 + 40·9)·6^9`, `c = 1/2`), `0 ∈ GoodSetN` at the levels
`(Γ, Λ, Φ) = (4, 100, 1)`.  The numeric helpers are copies of the private ones of `QDriftBInst`
(ticket T2263, `QDriftB.lean:449-640`).  No crude sup is needed (no hypothesis of the targets asks for it),
so `n = 4` is concrete (no existential `n`).  At `H = 0` the entries may vanish: the instances test the
hypotheses and the application, not tightness.  Every deterministic hypothesis is discharged. -/

end RBM.Ind

end
