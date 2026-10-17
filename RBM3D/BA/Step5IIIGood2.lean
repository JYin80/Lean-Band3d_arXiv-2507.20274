/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.Step5IIIGood
import RBM3D.Path.LemDecCalEwG

/-!
# Step 5, case `1 - t ≥ λ²`, block Anderson model: the scalar hypotheses of Lemma 5.2 along a flow

Paper: Lemma 5.2 (`lem_dec_calE`) in the proof of Step 5, case `1 - t ≥ λ²` (Subsection 5.3,
`sec:Step5_larget`), whose scalar hypotheses are `M_u = W^d(1-u)`, `ℓ_u = 1` (because
`lam² ≤ 1 - u`) and a parameter `J ≤ W^{1/2}`. For the block Anderson model the paper omits the
details (proof of Steps 3-6 for Theorem 8.2, `lem:main_ind_BA`).

`baStep5III_scalar_flow`: along a flow in the regime, eventually, every `u ∈ [s_n, t_n]`, every
level `D' ≥ D` and every `J` with `1 ≤ J ≤ W^{1/2}` satisfy the scalar part of the hypothesis bundle
of Lemma 5.2 (written inline; it is the list of clauses of `BAStep5IIIEScalar`) at
`Λ = K₀ = N^{τ'}`.  The inputs are `Sizes.WO` (`0 < lam`, and `lam_sq_mul_pow_ge`),
`Sizes.Bandwidth` and `Sizes.SizeTendsto` (`4 ≤ log W`).
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Matrix

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

variable {d : ℕ}

/-! ## The scalar part along a flow -/

section ScalarFlow

/-- Along a flow in the regime, eventually, every `u ∈ [s_n, t_n]`, every level `D' ≥ D` and every parameter
`1 ≤ J ≤ W^{1/2}` satisfy the scalar part of the hypothesis bundle (inline) at `Λ = K₀ = N^{τ'}`; the floor
premise is `(L^d W^{6d})² ≤ W^D` eventually. -/
theorem baStep5III_scalar_flow (d : ℕ) (hd : 3 ≤ d) :
    ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) →
      STReg5III sz s t → ∀ D τ' : ℝ, 0 ≤ τ' →
        (∀ᶠ n in atTop, (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D) →
        ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (D' J : ℝ), D ≤ D' → 1 ≤ J → J ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ) →
          3 ≤ d ∧ 0 ≤ (u : ℝ) ∧ (u : ℝ) < 1 ∧ 0 < sz.lam n ∧ sz.lam n ^ 2 ≤ 1 - (u : ℝ) ∧
            1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d ∧ 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ' ∧ 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ' ∧
            4 ≤ Real.log ((sz.W n : ℕ) : ℝ) ∧ (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D' ∧
            1 ≤ J ∧ J ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ) := by
  intro κ ε 𝔠 𝔡 sz z hflow s t hs hst hReg D τ' hτ' hfl
  obtain ⟨h𝔠, h𝔡, hsize, hband, hWO⟩ := hflow.1
  have hNtop : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop := (tendsto_rpow_atTop h𝔠).comp hsize
  have hWtop : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := tendsto_atTop_mono' _ hband hNtop
  have hlog : ∀ᶠ n in atTop, 4 ≤ Real.log ((sz.W n : ℕ) : ℝ) :=
    (Real.tendsto_log_atTop.comp hWtop).eventually_ge_atTop 4
  filter_upwards [hWO, hlog, hfl] with n hwo hlogn hfln
  intro u D' J hDD' hJ1 hJW
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hlam : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) hwo.1
  have hreg : sz.lam n ^ 2 ≤ 1 - (u : ℝ) := by have := hReg n; linarith [u.2.2]
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hQ : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ' := Real.one_le_rpow hN1 hτ'
  refine ⟨hd, (hs n).trans u.2.1, ?_, hlam, hreg, ?_, hQ, hQ, hlogn, ?_, hJ1, hJW⟩
  · nlinarith [pow_pos hlam 2]
  · exact (Real.one_le_rpow hW1 (by linarith)).trans (sz.lam_sq_mul_pow_ge n hwo.1)
  · exact hfln.trans (Real.rpow_le_rpow_of_exponent_le hW1 hDD')

end ScalarFlow

end RBM.BA
