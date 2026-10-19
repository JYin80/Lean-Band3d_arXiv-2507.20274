/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.QGridGen
import RBM3D.Induction.QGridB
import RBM3D.Chain.GridEnvelopeGen

/-!
# The summed envelope of the `𝒬`-grid remainders over a flow carrier

`sum_weighted_qErrQNg_le` is the form of `sum_weighted_qErrQN_le` (`Induction/QGridB`) over a carrier
`Cm : Step2Mat sz` (namespace `RBM.BA`).  Its four size conditions are those of
`SumWeightedStepErrNg_Stmt` (`Chain/GridEnvelopeGen`) at `(k, D_t) = (m + 1, D_t + (m + 1))`; the
hypotheses are `DecayGen_Spec` and `∀ n, (Cm.m n).im ≤ 1` in place of `|E n| ≤ 2 - κ`.

Proof outline: the case of the band energies, applied at the energy `E'_n = 2 √(1 - (Im m_n)²)`
(`κ = κ_m²`), for which `Im m(E'_n) = Im m_n` and `|E'_n| ≤ 2 - κ_m²`
(`GridEnvelopeGen_mE_im_Ep`, `GridEnvelopeGen_abs_Ep_le`); `qErrQNg` reads the carrier only through
`Cm.eta`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace RBM.BA

open Matrix RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal ENNReal

section Weighted

variable {d : ℕ} {sz : Sizes d}

/-- `qErrQNg` reads the carrier only through `C.eta n` (as `GridEnvelopeGen_stepErrNg_eta`). -/
private theorem QGridGen2_qErrQNg_eta {C C' : FlowFM sz} (h : ∀ n u, C.eta n u = C'.eta n u)
    (s t : ℕ → ℝ) (K : ℕ → ℕ) (n m : ℕ) (c c₂ Bk : ℝ) (j : ℕ) :
    qErrQNg C s t K n m c c₂ Bk j = qErrQNg C' s t K n m c c₂ Bk j := by
  unfold qErrQNg lkEnvNg driftEnvNg
  rw [GridEnvelopeGen_stepErrNg_eta n (m + 1) _ _ _ _ (fun u => h n u)]
  simp only [h]

/-- `sum_weighted_qErrQNg_le`, the carrier form of `sum_weighted_qErrQN_le` (`Induction/QGridB`): on the
grid `u_j = gridTime s t K n j` with `K n ≥ N^{C_K}`, the one-step remainders `qErrQNg` at the envelope
`B_{m+1} = N^{τ_K} η_{u_{j+1}}^{-(m+1)}`, weighted by the coarse row bound `(1 + (1 - u_p)⁻¹)^{m+1}` of the kernel, sum over `j < p` to
at most `N^{-D_t}` for every `p ≤ K n`, eventually, for any constants `0 ≤ C, C₂`. -/
theorem sum_weighted_qErrQNg_le :
    ∀ (d : ℕ) (sz : Sizes d) (Cm : Step2Mat sz) {κm τ' τK C_K D_t C C₂ : ℝ} {s t : ℕ → ℝ} {K : ℕ → ℕ} (m : ℕ),
    0 ≤ C → 0 ≤ C₂ → DecayGen_Spec Cm.toFlowFM κm → (∀ n, (Cm.m n).im ≤ 1) → 0 < τ' → τ' ≤ 1 → 0 < τK →
    0 ≤ D_t → 1 ≤ m → sz.SizeTendsto → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → (∀ n, K n ≠ 0) →
    sz.RangeCond τ' t →
    8 + (4 * ((m : ℝ) + 1) + 8) * (1 - τ') + 2 * (D_t + ((m : ℝ) + 1)) < C_K →
    3 + 4 * τK + 5 * ((m : ℝ) + 1) * (1 - τ') + (D_t + ((m : ℝ) + 1)) < C_K →
    2 * (1 - τ') + τK + 2 * ((m : ℝ) + 1) * (1 - τ') + (D_t + ((m : ℝ) + 1)) < C_K → 1 - τ' < C_K →
    (∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) →
    ∀ᶠ n : ℕ in atTop, ∀ p ≤ K n,
      ∑ j ∈ Finset.range p, (1 + (1 - gridTime s t K n p)⁻¹) ^ (m + 1) *
          qErrQNg Cm.toFlowFM s t K n m C C₂
            (((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (gridTime s t K n (j + 1)))⁻¹ ^ (m + 1)) j ≤
        ((sz.size n : ℕ) : ℝ) ^ (-D_t) := by
  intro d sz Cm κm τ' τK C_K D_t C C₂ s t K m hC hC₂ hspec him1 hτ' hτ'1 hτK hDt hm hsize hs0 hst ht1 hK0 hrange h1 h2 h3 h4 hKN
  set E' : ℕ → ℝ := fun n => 2 * Real.sqrt (1 - ((Cm.m n).im) ^ 2) with hE'
  have hκm : 0 < κm := hspec.1
  have hE'2 : ∀ n, |E' n| ≤ 2 - κm ^ 2 := fun n =>
    GridEnvelopeGen_abs_Ep_le hκm (hspec.2.1 n) (him1 n)
  have hmE : ∀ n, (mE (E' n)).im = (Cm.m n).im := fun n =>
    GridEnvelopeGen_mE_im_Ep (hκm.le.trans (hspec.2.1 n)) (him1 n)
  have hetaE : ∀ n u, etaT (E' n) u = Cm.eta n u := fun n u => by
    rw [hspec.2.2 n u]; unfold etaT; rw [hmE n]
  have hq : ∀ n B j, RBM.Ind.qErrQN sz E' s t K n m C C₂ B j = qErrQNg Cm.toFlowFM s t K n m C C₂ B j :=
    fun n B j => (QGridGen_bandFM_qErrQN sz E' s t K n j m C C₂ B).trans
      (QGridGen2_qErrQNg_eta (fun n u => hetaE n u) s t K n m C C₂ B j)
  have hband := RBM.Ind.sum_weighted_qErrQN_le d sz (κ := κm ^ 2) (E := E') m hC hC₂ (by positivity) hτ' hτ'1 hτK hDt hm
    hsize hE'2 hs0 hst ht1 hK0 hrange h1 h2 h3 h4 hKN
  refine hband.mono fun n hn p hp => ?_
  have := hn p hp
  simp only [hq, hetaE] at this
  exact this

end Weighted

end RBM.BA

end
