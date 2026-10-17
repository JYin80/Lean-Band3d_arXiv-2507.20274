/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.Step5IIIGood
import RBM3D.Path.LemDecCalEwG

/-!
# U5c, part 2: the scalar part of U5b's bundle along a flow, and the composed instance

Ticket T2485.  Paper: the scalar hypotheses of `lem_dec_calE` (`3_5:2314-2338`): `M_u = W^d(1-u)`,
`ℓ_u = 1` as `lam² ≤ 1 - u`, `J ≤ W^{1/2}`; BA `7_8:2101` (omitted details, paper-delta candidate
T2459a).  Design `docs/reports/T2459-design.md` U5-2; audit `docs/reports/T2459-audit.md` O2
(second half).

1. `baStep5III_scalar_flow` (target 4): along a flow in the regime, eventually, every
   `u ∈ [s_n, t_n]`, every level `D' ≥ D` and every control `1 ≤ J ≤ W^{1/2}` meet the scalar part
   of the bundle (written inline) at `Λ = K₀ = N^{τ'}`.  Sources: `Sizes.WO` (`0 < lam`;
   `lam_sq_mul_pow_ge`, `Defs/Sizes.lean:193`), `Sizes.Bandwidth`, `Sizes.SizeTendsto`
   (`4 ≤ log W`).
2. Compiled nonempty instances (target 5) at `d = 3`, `sz0`, `zSeq`, `flow_sz0`: target 4 with its
   floor premise discharged, and the composed instance (audit O2): on `G ∩ {J♯ ≤ W^{1/2}}` both
   parts of the bundle hold, and the three ℰ-bounds follow through an exact-type hypothesis
   `Step5IIIGood2_Edet 3` (the text of `T2482_BAEdet`, `docs/tickets/checks/T2482-check.lean:180`;
   U5b-2's pin, not merged).  The private bundle copies `Step5IIIGood2_Scalar`, `_Matrix`,
   `_EdetConcl`, `_Edet` appear only in this section.

Helpers carry the stem `Step5IIIGood2_`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Matrix

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Target 4: the scalar part at the flow -/

section ScalarFlow

/-- **Target 4** (content binding `T2485_ScalarFlow`; audit O2, second half): along a flow in the regime, eventually, every
`u ∈ [s_n, t_n]`, every level `D' ≥ D` and every control `1 ≤ J ≤ W^{1/2}` meet the scalar part of the bundle (inline) at
`Λ = K₀ = N^{τ'}`; the floor premise is `(L^d W^{6d})² ≤ W^D` eventually. -/
theorem baStep5III_scalar_flow :
    ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes 3) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) →
      STReg5III sz s t → ∀ D τ' : ℝ, 0 ≤ τ' →
        (∀ᶠ n in atTop, (((sz.L n : ℕ) : ℝ) ^ 3 * ((sz.W n : ℕ) : ℝ) ^ (6 * 3)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D) →
        ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (D' J : ℝ), D ≤ D' → 1 ≤ J → J ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ) →
          3 ≤ 3 ∧ 0 ≤ (u : ℝ) ∧ (u : ℝ) < 1 ∧ 0 < sz.lam n ∧ sz.lam n ^ 2 ≤ 1 - (u : ℝ) ∧
            1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ 3 ∧ 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ' ∧ 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ' ∧
            4 ≤ Real.log ((sz.W n : ℕ) : ℝ) ∧ (((sz.L n : ℕ) : ℝ) ^ 3 * ((sz.W n : ℕ) : ℝ) ^ (6 * 3)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D' ∧
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
  refine ⟨le_rfl, (hs n).trans u.2.1, ?_, hlam, hreg, ?_, hQ, hQ, hlogn, ?_, hJ1, hJW⟩
  · nlinarith [pow_pos hlam 2]
  · exact (Real.one_le_rpow hW1 (by linarith)).trans (sz.lam_sq_mul_pow_ge n hwo.1)
  · exact hfln.trans (Real.rpow_le_rpow_of_exponent_le hW1 hDD')

end ScalarFlow

/-! ## 2. Compiled nonempty instances at `d = 3`, `sz0`, `zSeq`, `flow_sz0`

Data: `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`, `s ≡ 1/10 < t ≡ 1/2 < t₀`, `D = 40`, `Cd = 1`, `θ = 1/10`.  The four Steps 2-4 predicates
and `Step5IIIGood2_Edet 3` stay hypotheses. -/

end RBM.BA
