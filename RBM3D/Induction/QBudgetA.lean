/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.QLevelsB
import RBM3D.Induction.QProxy
import RBM3D.Induction.NQLin

/-!
# S3-17a (ticket T2279): the budget of the alternating endpoint at `d ≥ 3`

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`): `lem:STOeq_Qt`
`3_5:1364-1378`, `(am;asoi222)` `3_5:1366`, the alternating case `3_5:1676-1714`
(`(eq:alternatecase1)` `3_5:1680-1690`, `(y27kasdfg)`, `(A4)`, `(A5)` `3_5:1692-1706`,
`(eq:alternatecase2)` `3_5:1711-1714`: "applying `(sum_res_2)` ... and performing the
integral over `v`"), the non-alternating budget it refers to `3_5:1152-1180`.

Re-scope (DECISIONS §83, §62 (2)/(4), §64 (4)/(5), §91 (2)): RBM2D `AltBudgetTerms` /
`AltBudget` (`c9a24cf`) are ported in the RBM3D non-alternating form on the merged generic
budgets of `NQBudget` (`tbInitN`, `tbDriftN`, `tbQvN`): one kernel `kappaAltQN`, one drift level
(entering generically, `dd j ≤ Pa Φd B_{u_j}^k/η_{u_j} + b`), no `ℚ/𝔼` split, no Case-4 weights,
no `AltBudgetHyp` structure.  No probability, no `Prec`, no lift, no prime, no good set.

* §0 the vocabulary (check file `docs/tickets/checks/T2279-check.lean` §2, verbatim):
  `altBudget_kapFar`, `altBudget_qvFar`, `qvBdAltQN`, `cQVAltQN`, `dDriftAltLinQN`,
  `assembledRHSAltQN`;
* §1 targets 1-3: the sharp kernel `κ_{i,m} B_{u_i}^k ≤ W^{C₄ε} B_{u_m}^k` and the far bound;
* §2 targets 4-7: the three term budgets (`qvBdAltQN_eq_qvShape`, `tbInitAltQN`, `tbDriftAltQN`,
  `tbQvAltQN`);
* §3 targets 8-9: the two drift levels in the generic shape (`dDriftAltLinQN_le_shape`,
  `dDriftAltQN_le_shape`);
* §4 target 10: `budgetAltQN` (the proof of `budgetNonAltLinN`, `NQLin.lean:966`, with the
  generic drift level, the extra `he0` and the `b` part of `he1`);
* §5 compiled nonempty instances (namespace `QBudgetAInst`) at `d = 3`, `sz0`, `n = 0`.

Unpinned helpers are `private` or prefixed `QBudgetA_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-! ## 0. Vocabulary (the six definitions of the ticket, verbatim) -/

/-- **The far bound of the alternating kernel weight**: `κ_{i,m} ≤ W^{C₄ε} ((1+g²) N)^k` when `(1-u_m)⁻¹ ≤ N`
(`kappaAltQN`, `QDriftA.lean:100`, exponent `k`, not `k-1`; analogue of `nqBudget_kapFar`, `NQBudget.lean:101`). -/
def altBudget_kapFar {d : ℕ} (sz : Sizes d) (n k : ℕ) (Λg κ' KL ε : ℝ) : ℝ :=
  ((sz.W n : ℕ) : ℝ) ^ (qProxy4C d k Λg κ' KL * ε) *
    ((1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ)) ^ k

/-- **The far coefficient of the alternating quadratic variation**: `C_far (C_far + C_e) + C_c` of the generic
`tbQvN` (`NQBudget.lean:269`) at `C_far = altBudget_kapFar`, `C_e = W^{C₄}`, `C_c = W^{C₄} W^k`. -/
def altBudget_qvFar {d : ℕ} (sz : Sizes d) (n k : ℕ) (Λg κ' KL ε : ℝ) : ℝ :=
  altBudget_kapFar sz n k Λg κ' KL ε *
      (altBudget_kapFar sz n k Λg κ' KL ε + ((sz.W n : ℕ) : ℝ) ^ qProxy4C d k Λg κ' KL) +
    ((sz.W n : ℕ) : ℝ) ^ qProxy4C d k Λg κ' KL * ((sz.W n : ℕ) : ℝ) ^ k

/-- **The variance majorant of the `𝒬`-process** (tensors of `m + 1 + 1` indices): the right side of the merged
`qvFormQN_le_of_goodSetN` (`QProxy.lean:1167`) with its `m` at `m + 1`. -/
def qvBdAltQN {d : ℕ} (sz : Sizes d) (n : ℕ) (E : ℝ) (m : ℕ) (Λg κ' KL C c ε Γ Λ D u w : ℝ) : ℝ :=
  (((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) *
      ((sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - w|)) ^ (m + 1 + 1)) *
    ((((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) *
        ((sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - w|)) ^ (m + 1 + 1)) *
      (((sz.W n : ℕ) : ℝ) ^ (2 * qProxyCn d (m + 1) Λg KL C c * ε) *
          (Γ * (Γ * Λ) * ((sz.Bctl n u) ^ (2 * (m + 1 + 1)) / etaT E u)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D + qProxyCQ d (m + 1) Λg KL C c)) +
      ((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1 + 1) Λg κ' KL *
        ((sz.W n : ℕ) : ℝ) ^ (-D + qProxyCQ d (m + 1) Λg KL C c)) +
    ((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1 + 1) Λg κ' KL *
      (((sz.W n : ℕ) : ℝ) ^ (m + 1 + 1) * ((sz.W n : ℕ) : ℝ) ^ (-D + qProxyCQ d (m + 1) Λg KL C c))

/-- **The sub-Gaussian proxy of the `j`-th propagated `𝒬`-increment towards `u_p`**: `Δ · (m+2) · qvBdAltQN(u_{j+1}, u_p)`
(the left side of the `hQ` premise of `azumaSubGQ_gridExitN`, `QProxy.lean:409`, at its `m` = `m + 1`; the label does
not enter; pattern `cQVNonAltN`, `NQGood2.lean:115`). -/
def cQVAltQN {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n m : ℕ) (Λg κ' KL C c ε : ℝ)
    (Γ Λ : ℕ → ℝ) (D'' : ℝ) (p : ℕ) (_a : Fin (m + 1 + 1) → Zd d (sz.L n)) (j : ℕ) : ℝ≥0 :=
  (gridStep s v K n * (((m + 1 + 1 : ℕ) : ℝ) * qvBdAltQN sz n (E n) m Λg κ' KL C c ε (Γ n) (Λ n) D''
    (gridTime s v K n (j + 1)) (gridTime s v K n p))).toNNReal

/-- **The linear drift level of the alternating chain** (DECISIONS §62 (2)/(4)): `dDriftAltQN` (`QLevelsB.lean:53`)
with the quadratic `dDriftNonAltN` replaced by the linear `dDriftLinN` (`NQLin.lean:711`):
`W^{C_n ε'} Γ²(B^k/η)((k-2)Φ₁ + Φ₂ + Φ₃) + W^{-D'+C_n} + N^{τ_N} η⁻¹ B^{m+2} X`, `k = m + 2`. -/
def dDriftAltLinQN {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (m : ℕ) (Γ Φ₁ Φ₂ Φ₃ Cn ε' D' τN X : ℝ) : ℝ :=
  ((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * dDriftLinN sz n E u (m + 1 + 1) Γ Φ₁ Φ₂ Φ₃ +
    ((sz.W n : ℕ) : ℝ) ^ (-D' + Cn) +
    ((sz.size n : ℕ) : ℝ) ^ τN * ((etaT E u)⁻¹ * sz.Bctl n u ^ (m + 2) * X)

/-- **The right-hand side of the merged `AssembledN` at the target `K n` for the alternating chain** (tensors of
`m + 1 + 1` indices; pattern `assembledRHSLinN`, `NQLin.lean:825`): `κ = kappaAltQN`, `εK = epsAltQN` at `g = lam n`
(`alt_hkerQN`), initial supremum `X0`, initial decay error `δ0` (`alt_hA0clsQN`), drift levels `dd j` (generic:
`dDriftAltLinQN` or `dDriftAltQN` at `u_j`), drift decay error `δD` (`alt_hDclsQN`: `4 W^{-D'}`), proxy `cQVAltQN`,
`N^{-D_Y}`, `stepErrN` at the envelope `N^{τ_K} η_{u_{j+1}}^{-k}`. -/
def assembledRHSAltQN {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n m : ℕ)
    (Λg κ' KL C c ε : ℝ) (Γ Λ : ℕ → ℝ) (dd : ℕ → ℝ) (δ0 δD D'' D_Y τK εq X0 : ℝ)
    (a : Fin (m + 1 + 1) → Zd d (sz.L n)) : ℝ :=
  kappaAltQN d (m + 1 + 1) Λg κ' KL (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) 0 (K n) * X0 +
    epsAltQN d (m + 1 + 1) Λg κ' KL ((sz.W n : ℕ) : ℝ) 0 (K n) * δ0 +
    gridStep s v K n * ∑ j ∈ Finset.range (K n),
      (kappaAltQN d (m + 1 + 1) Λg κ' KL (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) (j + 1) (K n) *
          dd j +
        epsAltQN d (m + 1 + 1) Λg κ' KL ((sz.W n : ℕ) : ℝ) (j + 1) (K n) * δD) +
    ((sz.size n : ℕ) : ℝ) ^ εq * Real.sqrt (∑ j ∈ Finset.range (K n),
      (cQVAltQN sz E s v K n m Λg κ' KL C c ε Γ Λ D'' (K n) a j : ℝ)) +
    ((sz.size n : ℕ) : ℝ) ^ (-D_Y) +
    ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ (m + 1 + 1) *
      stepErrN d (sz.L n) (sz.W n) (E n) (m + 1 + 1) (gridTime s v K n j) (gridTime s v K n (j + 1))
        (gridStep s v K n)
        (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ (m + 1 + 1))

/-! ## 1. Elementary facts and targets 1-3: the sharp kernel -/

section Kernel

private theorem QBudgetA_kappa_nonneg (d k : ℕ) (Λg κ' KL g W ε : ℝ) (hW : 0 ≤ W) (u : ℕ → ℝ)
    (i m : ℕ) : 0 ≤ kappaAltQN d k Λg κ' KL g W ε u i m := by
  unfold kappaAltQN
  exact mul_nonneg (Real.rpow_nonneg hW _)
    (pow_nonneg (div_nonneg (by positivity) (by positivity)) _)

private theorem QBudgetA_eps_nonneg (d k : ℕ) (Λg κ' KL W : ℝ) (hW : 0 ≤ W) (i m : ℕ) :
    0 ≤ epsAltQN d k Λg κ' KL W i m := by
  unfold epsAltQN
  exact Real.rpow_nonneg hW _

/-- Target 1 (sharp kernel, initial datum; analogue of `kappaNonAltN_mul_Bctl_pow_le`, `NQGood2.lean:188`). -/
theorem kappaAltQN_mul_Bctl_pow_le :
  ∀ {d : ℕ} (sz : Sizes d) (n k : ℕ) (Λg κ' KL ε : ℝ) {W : ℝ}, 0 ≤ W →
    ∀ (u : ℕ → ℝ) {i m : ℕ}, u i ≤ u m → u m < 1 →
      kappaAltQN d k Λg κ' KL (sz.lam n) W ε u i m * (sz.Bctl n (u i)) ^ k ≤
        W ^ (qProxy4C d k Λg κ' KL * ε) * (sz.Bctl n (u m)) ^ k := by
  intro d sz n k Λg κ' KL ε W hW u i m him hm1
  have hi1 : u i < 1 := him.trans_lt hm1
  have hBu : 0 < sz.Bctl n (u i) := Sizes.STBctl_pos sz n hi1
  have hr0 : 0 ≤ (sz.lam n ^ 2 + |1 - u i|) / (sz.lam n ^ 2 + |1 - u m|) :=
    div_nonneg (by positivity) (by positivity)
  have hrB := nqGood2_ratio_mul_Bctl_le sz n him hm1
  have hWC : 0 ≤ W ^ (qProxy4C d k Λg κ' KL * ε) := Real.rpow_nonneg hW _
  unfold kappaAltQN
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hr0 hBu.le) hrB k) hWC

/-- Target 2 (sharp kernel, drift; analogue of `kappaNonAltN_succ_mul_Bctl_pow_le`, `NQGood2.lean:206`). -/
theorem kappaAltQN_succ_mul_Bctl_pow_le :
  ∀ {d : ℕ} (sz : Sizes d) (n k : ℕ) (Λg κ' KL ε : ℝ) {W : ℝ}, 0 ≤ W →
    ∀ (u : ℕ → ℝ) (j m : ℕ), u j ≤ u (j + 1) → u (j + 1) ≤ u m → u m < 1 →
      kappaAltQN d k Λg κ' KL (sz.lam n) W ε u (j + 1) m * (sz.Bctl n (u j)) ^ k ≤
        W ^ (qProxy4C d k Λg κ' KL * ε) * (sz.Bctl n (u m)) ^ k := by
  intro d sz n k Λg κ' KL ε W hW u j m hjj hj1m hm1
  have hj1 : u (j + 1) < 1 := hj1m.trans_lt hm1
  have hBle : sz.Bctl n (u j) ≤ sz.Bctl n (u (j + 1)) := Sizes.STBctl_mono sz n hjj hj1
  have hBj : 0 < sz.Bctl n (u j) := Sizes.STBctl_pos sz n (hjj.trans_lt hj1)
  have hκ := QBudgetA_kappa_nonneg d k Λg κ' KL (sz.lam n) W ε hW u (j + 1) m
  calc kappaAltQN d k Λg κ' KL (sz.lam n) W ε u (j + 1) m * (sz.Bctl n (u j)) ^ k
      ≤ kappaAltQN d k Λg κ' KL (sz.lam n) W ε u (j + 1) m * (sz.Bctl n (u (j + 1))) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hBj.le hBle k) hκ
    _ ≤ W ^ (qProxy4C d k Λg κ' KL * ε) * (sz.Bctl n (u m)) ^ k :=
        kappaAltQN_mul_Bctl_pow_le sz n k Λg κ' KL ε hW u hj1m hm1

/-- Target 3 (far bound; analogue of `nqBudget_kappa_le_kapFar`, `NQBudget.lean:163`). -/
theorem kappaAltQN_le_kapFar :
  ∀ {d : ℕ} (sz : Sizes d) (n k : ℕ) (Λg κ' KL ε : ℝ) (u : ℕ → ℝ) {i m : ℕ},
    0 ≤ u i → u i ≤ u m → u m < 1 → (1 - u m)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) →
      kappaAltQN d k Λg κ' KL (sz.lam n) ((sz.W n : ℕ) : ℝ) ε u i m ≤ altBudget_kapFar sz n k Λg κ' KL ε := by
  intro d sz n k Λg κ' KL ε u i m hu0 hium hm1 hN
  have hi1 : u i < 1 := hium.trans_lt hm1
  have hxm : 0 < 1 - u m := by linarith
  have hg : 0 ≤ sz.lam n ^ 2 := sq_nonneg _
  have hden : 0 < sz.lam n ^ 2 + |1 - u m| := by
    rw [abs_of_pos hxm]; linarith
  have hr0 : 0 ≤ (sz.lam n ^ 2 + |1 - u i|) / (sz.lam n ^ 2 + |1 - u m|) :=
    div_nonneg (by positivity) hden.le
  have hnum : sz.lam n ^ 2 + |1 - u i| ≤ 1 + sz.lam n ^ 2 := by
    rw [abs_of_pos (by linarith : 0 < 1 - u i)]; linarith
  have hr : (sz.lam n ^ 2 + |1 - u i|) / (sz.lam n ^ 2 + |1 - u m|) ≤
      (1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ) := by
    have h1 : (sz.lam n ^ 2 + |1 - u i|) / (sz.lam n ^ 2 + |1 - u m|) ≤
        (1 + sz.lam n ^ 2) * (1 - u m)⁻¹ := by
      rw [div_le_iff₀ hden]
      have e : (1 + sz.lam n ^ 2) * (1 - u m)⁻¹ * (sz.lam n ^ 2 + |1 - u m|) =
          (1 + sz.lam n ^ 2) * (1 + sz.lam n ^ 2 * (1 - u m)⁻¹) := by
        rw [abs_of_pos hxm]
        field_simp
        ring
      rw [e]
      have h2 : 1 ≤ 1 + sz.lam n ^ 2 * (1 - u m)⁻¹ := by
        have : 0 ≤ sz.lam n ^ 2 * (1 - u m)⁻¹ := mul_nonneg hg (inv_nonneg.2 hxm.le)
        linarith
      nlinarith [hnum, hg]
    exact h1.trans (mul_le_mul_of_nonneg_left hN (by linarith))
  have hWC : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (qProxy4C d k Λg κ' KL * ε) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  unfold kappaAltQN altBudget_kapFar
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr _) hWC

end Kernel

/-! ## 2. Targets 4-7: the three term budgets -/

section Terms

variable {d : ℕ} (sz : Sizes d)

/-- `0 ≤ u_i` on the grid `0 ≤ s_n ≤ v_n` (copy of the private `nqBudget_gridTime_nonneg`, `NQBudget.lean:334`). -/
private theorem QBudgetA_gridTime_nonneg {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hs0 : 0 ≤ s n)
    (hsv : s n ≤ v n) (i : ℕ) : 0 ≤ gridTime s v K n i := by
  have h := ST_gridTime_mono s v K n hsv (Nat.zero_le i)
  rw [ST_gridTime_zero] at h
  linarith

/-- `u_i ≤ v_n` for `i ≤ K_n`, `K_n ≠ 0` (copy of `nqBudget_gridTime_le`, `NQBudget.lean:341`). -/
private theorem QBudgetA_gridTime_le {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hsv : s n ≤ v n)
    (hK : K n ≠ 0) {i : ℕ} (hi : i ≤ K n) : gridTime s v K n i ≤ v n :=
  (ST_gridTime_mono s v K n hsv hi).trans_eq (gridTime_last s v K n hK)

/-- `K Δ = v - s` (copy of `nqBudget_K_mul_step`, `NQBudget.lean:346`). -/
private theorem QBudgetA_K_mul_step {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hK : K n ≠ 0) :
    (K n : ℝ) * gridStep s v K n = v n - s n := by
  have hK' : (K n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK
  unfold gridStep
  rw [mul_div_cancel₀ _ hK']

/-- Target 4 (the variance majorant is a `nqBudget_qvShape`; analogue of `qvBdNonAltN_eq_qvShape`,
`NQBudget.lean:355`). -/
theorem qvBdAltQN_eq_qvShape :
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E : ℝ) (m : ℕ) (Λg κ' KL C c ε Γ Λ D u w : ℝ),
    qvBdAltQN sz n E m Λg κ' KL C c ε Γ Λ D u w =
      nqBudget_qvShape (m + 1 + 1)
        (((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) *
          ((sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - w|)) ^ (m + 1 + 1))
        (((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1 + 1) Λg κ' KL)
        (((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1 + 1) Λg κ' KL * ((sz.W n : ℕ) : ℝ) ^ (m + 1 + 1))
        (((sz.W n : ℕ) : ℝ) ^ (2 * qProxyCn d (m + 1) Λg KL C c * ε) * (Γ * (Γ * Λ)))
        (((sz.W n : ℕ) : ℝ) ^ (-D + qProxyCQ d (m + 1) Λg KL C c))
        (sz.Bctl n u) (etaT E u) := by
  intro d sz n E m Λg κ' KL C c ε Γ Λ D u w
  unfold qvBdAltQN nqBudget_qvShape
  ring

/-- Target 5 (initial term; analogue of `tbInitNonAltN`, `NQBudget.lean:368`). -/
theorem tbInitAltQN :
  ∀ {d : ℕ} (sz : Sizes d) {s v : ℕ → ℝ} {K : ℕ → ℕ} (n k : ℕ) (Λg κ' KL ε G X0 : ℝ),
    0 ≤ s n → s n ≤ v n → v n < 1 → K n ≠ 0 → 0 ≤ G → X0 ≤ G * (sz.Bctl n (s n)) ^ k →
      kappaAltQN d k Λg κ' KL (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) 0 (K n) * X0 ≤
        ((sz.W n : ℕ) : ℝ) ^ (qProxy4C d k Λg κ' KL * ε) * G * (sz.Bctl n (v n)) ^ k := by
  intro d sz s v K n k Λg κ' KL ε G X0 hs0 hsv hv1 hK hG hX0
  have hW : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  have huK := gridTime_last s v K n hK
  have hu0 := ST_gridTime_zero s v K n
  have hκ0 := QBudgetA_kappa_nonneg d k Λg κ' KL (sz.lam n) ((sz.W n : ℕ) : ℝ) ε hW
    (gridTime s v K n) 0 (K n)
  have hker := kappaAltQN_mul_Bctl_pow_le sz n k Λg κ' KL ε hW (gridTime s v K n)
    (i := 0) (m := K n) (by rw [hu0, huK]; exact hsv) (by rw [huK]; exact hv1)
  rw [hu0, huK] at hker
  have h := tbInitN (k := k) (K := K n) (Cκ := ((sz.W n : ℕ) : ℝ) ^ (qProxy4C d k Λg κ' KL * ε))
    (G := G) (X0 := X0) (fun i => sz.Bctl n (gridTime s v K n i))
    (kappaAltQN d k Λg κ' KL (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n)) hκ0 hG
    (by simpa only [hu0, huK] using hker) (by simpa only [hu0] using hX0)
  simpa only [huK] using h

/-- Target 6 (drift term at a generic level `dd j ≤ Pa Φd B_{u_j}^k/η_{u_j} + b`; the merged generic `tbDriftN`,
`NQBudget.lean:221`, with targets 2 and 3; analogue of `tbDriftLinN`, `NQLin.lean:876`). -/
theorem tbDriftAltQN :
  ∀ {d : ℕ} (sz : Sizes d) {E s v : ℕ → ℝ} {K : ℕ → ℕ} (n k : ℕ) (Λg κ' KL ε : ℝ)
    (dd : ℕ → ℝ) (Pa Φd b δD : ℝ),
    |E n| < 2 → 0 ≤ s n → s n ≤ v n → v n < 1 → K n ≠ 0 →
    0 ≤ Pa → 0 ≤ Φd → 0 ≤ b → 0 ≤ δD →
    (etaT (E n) (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) →
    (∀ j < K n, dd j ≤ Pa * Φd * ((sz.Bctl n (gridTime s v K n j)) ^ k / etaT (E n) (gridTime s v K n j)) + b) →
      gridStep s v K n * ∑ j ∈ Finset.range (K n),
        (kappaAltQN d k Λg κ' KL (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) (j + 1) (K n) * dd j +
          epsAltQN d k Λg κ' KL ((sz.W n : ℕ) : ℝ) (j + 1) (K n) * δD) ≤
        ((sz.W n : ℕ) : ℝ) ^ (qProxy4C d k Λg κ' KL * ε) * (Pa * Φd) * (sz.Bctl n (v n)) ^ k *
            ∑ j ∈ Finset.range (K n), gridStep s v K n / etaT (E n) (gridTime s v K n j) +
          ((K n : ℝ) * gridStep s v K n) *
            (altBudget_kapFar sz n k Λg κ' KL ε * b + ((sz.W n : ℕ) : ℝ) ^ qProxy4C d k Λg κ' KL * δD) := by
  intro d sz E s v K n k Λg κ' KL ε dd Pa Φd b δD hE hs0 hsv hv1 hK hPa hΦd hb hδD hη hdd
  have hW : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hu0 : ∀ i, 0 ≤ gridTime s v K n i := fun i => QBudgetA_gridTime_nonneg hs0 hsv i
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi =>
    (QBudgetA_gridTime_le hsv hK hi).trans_lt hv1
  have huK := gridTime_last s v K n hK
  have hmono : ∀ i m, i ≤ m → gridTime s v K n i ≤ gridTime s v K n m := fun i m him =>
    ST_gridTime_mono s v K n hsv him
  have hΔ0 : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n hsv
  have hN1 : (1 - v n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := nqBudget_inv_one_sub_le hE hv1 hη
  have hsucc : ∀ j < K n, kappaAltQN d k Λg κ' KL (sz.lam n) ((sz.W n : ℕ) : ℝ) ε
      (gridTime s v K n) (j + 1) (K n) * (sz.Bctl n (gridTime s v K n j)) ^ k ≤
      ((sz.W n : ℕ) : ℝ) ^ (qProxy4C d k Λg κ' KL * ε) *
        (sz.Bctl n (gridTime s v K n (K n))) ^ k := fun j hj =>
    kappaAltQN_succ_mul_Bctl_pow_le sz n k Λg κ' KL ε hW (gridTime s v K n) j (K n)
      (hmono j (j + 1) (by omega)) (hmono (j + 1) (K n) (by omega)) (hu1 _ le_rfl)
  have h := tbDriftN (E := E n) (k := k) (K := K n) (Δ := gridStep s v K n)
    (Cκ := ((sz.W n : ℕ) : ℝ) ^ (qProxy4C d k Λg κ' KL * ε))
    (Cε := ((sz.W n : ℕ) : ℝ) ^ qProxy4C d k Λg κ' KL)
    (Cfar := altBudget_kapFar sz n k Λg κ' KL ε)
    (a := Pa * Φd) (b := b) (δmax := δD) (gridTime s v K n)
    (fun i => sz.Bctl n (gridTime s v K n i))
    (kappaAltQN d k Λg κ' KL (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n))
    (epsAltQN d k Λg κ' KL ((sz.W n : ℕ) : ℝ)) dd (fun _ => δD) hΔ0 (mul_nonneg hPa hΦd) hb
    (fun j hj => QBudgetA_kappa_nonneg d k Λg κ' KL (sz.lam n) ((sz.W n : ℕ) : ℝ) ε hW _
      (j + 1) (K n))
    (fun j hj => QBudgetA_eps_nonneg d k Λg κ' KL ((sz.W n : ℕ) : ℝ) hW (j + 1) (K n))
    hsucc
    (fun j hj => kappaAltQN_le_kapFar sz n k Λg κ' KL ε (gridTime s v K n) (hu0 (j + 1))
      (hmono (j + 1) (K n) (by omega)) (hu1 _ le_rfl) (by rw [huK]; exact hN1))
    (fun _ _ => le_rfl) hdd (fun _ _ => hδD) (fun _ _ => le_rfl)
    (fun j hj => etaT_pos hE (hu1 j hj.le))
  rw [huK] at h
  exact h

/-- `qvBdAltQN ≥ 0` for `Λ ≥ 0`, `|E| < 2`, `u < 1` (so the `toNNReal` of `cQVAltQN` is the identity). -/
private theorem QBudgetA_qvBd_nonneg (n : ℕ) {E : ℝ} (m : ℕ) (Λg κ' KL C c ε Γ Λ D u w : ℝ)
    (hE : |E| < 2) (hu1 : u < 1) (hΛ : 0 ≤ Λ) :
    0 ≤ qvBdAltQN sz n E m Λg κ' KL C c ε Γ Λ D u w := by
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hB : 0 < sz.Bctl n u := Sizes.STBctl_pos sz n hu1
  have hW0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hG : 0 ≤ Γ * (Γ * Λ) := by
    have : Γ * (Γ * Λ) = Γ ^ 2 * Λ := by ring
    rw [this]; positivity
  have hG' : 0 ≤ Γ * (Γ * Λ) * ((sz.Bctl n u) ^ (2 * (m + 1 + 1)) / etaT E u) :=
    mul_nonneg hG (div_nonneg (pow_nonneg hB.le _) hη.le)
  have hr : 0 ≤ (sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - w|) :=
    div_nonneg (by positivity) (by positivity)
  unfold qvBdAltQN
  positivity

/-- Target 7 (quadratic-variation term; the merged generic `tbQvN`, `NQBudget.lean:269`, with targets 1 and 4;
analogue of `tbQvNonAltN`, `NQBudget.lean:458`). -/
theorem tbQvAltQN :
  ∀ {d : ℕ} (sz : Sizes d) {E s v : ℕ → ℝ} {K : ℕ → ℕ} (n m : ℕ) (Λg κ' KL C c ε : ℝ)
    (Γ Λ : ℕ → ℝ) (D'' : ℝ) (a : Fin (m + 1 + 1) → Zd d (sz.L n)),
    |E n| < 2 → 0 ≤ s n → s n ≤ v n → v n < 1 → K n ≠ 0 → 0 ≤ Λ n →
    (etaT (E n) (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) →
      ∑ j ∈ Finset.range (K n), (cQVAltQN sz E s v K n m Λg κ' KL C c ε Γ Λ D'' (K n) a j : ℝ) ≤
        ((m + 1 + 1 : ℕ) : ℝ) * (((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε)) ^ 2 *
            (((sz.W n : ℕ) : ℝ) ^ (2 * qProxyCn d (m + 1) Λg KL C c * ε) * (Γ n * (Γ n * Λ n))) *
            ((sz.Bctl n (v n)) ^ (m + 1 + 1)) ^ 2 *
            ∑ j ∈ Finset.range (K n), gridStep s v K n / etaT (E n) (gridTime s v K n (j + 1)) +
          ((K n : ℝ) * gridStep s v K n) *
            (((m + 1 + 1 : ℕ) : ℝ) * (altBudget_qvFar sz n (m + 1 + 1) Λg κ' KL ε *
              ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c))) := by
  intro d sz E s v K n m Λg κ' KL C c ε Γ Λ D'' a hE hs0 hsv hv1 hK hΛ hη
  have hW : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hu0 : ∀ i, 0 ≤ gridTime s v K n i := fun i => QBudgetA_gridTime_nonneg hs0 hsv i
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi =>
    (QBudgetA_gridTime_le hsv hK hi).trans_lt hv1
  have huK := gridTime_last s v K n hK
  have hmono : ∀ i m, i ≤ m → gridTime s v K n i ≤ gridTime s v K n m := fun i m him =>
    ST_gridTime_mono s v K n hsv him
  have hΔ0 : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n hsv
  have hN1 : (1 - v n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := nqBudget_inv_one_sub_le hE hv1 hη
  have hWd : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c) :=
    Real.rpow_nonneg hW _
  have hWC : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1 + 1) Λg κ' KL :=
    Real.rpow_nonneg hW _
  have hG : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (2 * qProxyCn d (m + 1) Λg KL C c * ε) * (Γ n * (Γ n * Λ n)) := by
    have : Γ n * (Γ n * Λ n) = Γ n ^ 2 * Λ n := by ring
    rw [this]; have := Real.rpow_nonneg hW (2 * qProxyCn d (m + 1) Λg KL C c * ε); positivity
  have hcoe : ∀ j ∈ Finset.range (K n),
      (cQVAltQN sz E s v K n m Λg κ' KL C c ε Γ Λ D'' (K n) a j : ℝ) =
        gridStep s v K n * (((m + 1 + 1 : ℕ) : ℝ) * nqBudget_qvShape (m + 1 + 1)
          (kappaAltQN d (m + 1 + 1) Λg κ' KL (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n)
            (j + 1) (K n))
          (((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1 + 1) Λg κ' KL)
          (((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1 + 1) Λg κ' KL * ((sz.W n : ℕ) : ℝ) ^ (m + 1 + 1))
          (((sz.W n : ℕ) : ℝ) ^ (2 * qProxyCn d (m + 1) Λg KL C c * ε) * (Γ n * (Γ n * Λ n)))
          (((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c))
          (sz.Bctl n (gridTime s v K n (j + 1))) (etaT (E n) (gridTime s v K n (j + 1)))) := by
    intro j hj
    have hjK := Finset.mem_range.1 hj
    have hpos := QBudgetA_qvBd_nonneg sz n (E := E n) m Λg κ' KL C c ε (Γ n) (Λ n) D''
      (gridTime s v K n (j + 1)) (gridTime s v K n (K n)) hE (hu1 (j + 1) (by omega)) hΛ
    unfold cQVAltQN
    rw [Real.coe_toNNReal _ (by positivity), qvBdAltQN_eq_qvShape]
    rfl
  rw [Finset.sum_congr rfl hcoe]
  have h := tbQvN (E := E n) (k := m + 1 + 1) (K := K n)
    (Cκ := ((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε))
    (Cfar := altBudget_kapFar sz n (m + 1 + 1) Λg κ' KL ε)
    (Ce := ((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1 + 1) Λg κ' KL)
    (Cc := ((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1 + 1) Λg κ' KL * ((sz.W n : ℕ) : ℝ) ^ (m + 1 + 1))
    (G := ((sz.W n : ℕ) : ℝ) ^ (2 * qProxyCn d (m + 1) Λg KL C c * ε) * (Γ n * (Γ n * Λ n)))
    (Wd := ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c)) (Δ := gridStep s v K n)
    (gridTime s v K n) (fun i => sz.Bctl n (gridTime s v K n i))
    (fun j => kappaAltQN d (m + 1 + 1) Λg κ' KL (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n)
      (j + 1) (K n))
    (fun j hj => (Sizes.STBctl_pos sz n (hu1 (j + 1) (by omega))).le)
    (fun j hj => QBudgetA_kappa_nonneg d (m + 1 + 1) Λg κ' KL (sz.lam n) ((sz.W n : ℕ) : ℝ) ε hW _
      (j + 1) (K n))
    (fun j hj => kappaAltQN_mul_Bctl_pow_le sz n (m + 1 + 1) Λg κ' KL ε hW (gridTime s v K n)
      (hmono (j + 1) (K n) (by omega)) (hu1 _ le_rfl))
    (fun j hj => kappaAltQN_le_kapFar sz n (m + 1 + 1) Λg κ' KL ε (gridTime s v K n) (hu0 (j + 1))
      (hmono (j + 1) (K n) (by omega)) (hu1 _ le_rfl) (by rw [huK]; exact hN1))
    hG hWd hWC hΔ0 (fun j hj => etaT_pos hE (hu1 (j + 1) (by omega)))
  rw [huK] at h
  unfold altBudget_qvFar
  exact h

end Terms

/-! ## 3. Targets 8-9: the two drift levels in the generic shape -/

section Levels

/-- Target 8 (the linear level in the generic shape of target 6: `Pa = W^{C_nε'}Γ²k + N^{τ_N}`,
`Φd = Φ₁ + Φ₂ + Φ₃ + X`, `b = W^{-D'+C_n}`). -/
theorem dDriftAltLinQN_le_shape :
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (m : ℕ) (Γ Φ₁ Φ₂ Φ₃ Cn ε' D' τN X : ℝ),
    |E| < 2 → u < 1 → 0 ≤ Φ₁ → 0 ≤ Φ₂ → 0 ≤ Φ₃ → 0 ≤ X →
      dDriftAltLinQN sz n E u m Γ Φ₁ Φ₂ Φ₃ Cn ε' D' τN X ≤
        (((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * (Γ * Γ) * ((m + 1 + 1 : ℕ) : ℝ) + ((sz.size n : ℕ) : ℝ) ^ τN) *
            (Φ₁ + Φ₂ + Φ₃ + X) * ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u) +
          ((sz.W n : ℕ) : ℝ) ^ (-D' + Cn) := by
  intro d sz n E u m Γ Φ₁ Φ₂ Φ₃ Cn ε' D' τN X hE hu h1 h2 h3 hX
  have hη : 0 < etaT E u := etaT_pos hE hu
  have hB : 0 < sz.Bctl n u := Sizes.STBctl_pos sz n hu
  have hW0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hP : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (Cn * ε') := Real.rpow_nonneg hW0 _
  have hNτ : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τN := Real.rpow_nonneg hN0 _
  have hT : 0 ≤ (sz.Bctl n u) ^ (m + 1 + 1) / etaT E u := div_nonneg (pow_nonneg hB.le _) hη.le
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hk : ((m + 1 + 1 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
  unfold dDriftAltLinQN dDriftLinN
  -- `m + 2` and `m + 1 + 1` are definitionally equal; `ring` identifies the two exponents
  have e : (etaT E u)⁻¹ * sz.Bctl n u ^ (m + 2) * X =
      X * ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u) := by
    rw [div_eq_mul_inv]; ring
  rw [e]
  have key : (((m + 1 + 1 : ℕ) : ℝ) - 2) * Φ₁ + Φ₂ + Φ₃ ≤
      ((m + 1 + 1 : ℕ) : ℝ) * (Φ₁ + Φ₂ + Φ₃ + X) := by
    rw [hk]
    nlinarith [mul_nonneg hm0 h1, mul_nonneg hm0 h2, mul_nonneg hm0 h3, mul_nonneg hm0 hX]
  have A : ((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * (Γ * Γ * ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u) *
        ((((m + 1 + 1 : ℕ) : ℝ) - 2) * Φ₁ + Φ₂ + Φ₃)) ≤
      ((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * (Γ * Γ) * ((m + 1 + 1 : ℕ) : ℝ) * (Φ₁ + Φ₂ + Φ₃ + X) *
        ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u) := by
    calc ((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * (Γ * Γ * ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u) *
          ((((m + 1 + 1 : ℕ) : ℝ) - 2) * Φ₁ + Φ₂ + Φ₃))
        = (((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * (Γ * Γ) * ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u)) *
          ((((m + 1 + 1 : ℕ) : ℝ) - 2) * Φ₁ + Φ₂ + Φ₃) := by ring
      _ ≤ (((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * (Γ * Γ) * ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u)) *
          (((m + 1 + 1 : ℕ) : ℝ) * (Φ₁ + Φ₂ + Φ₃ + X)) :=
          mul_le_mul_of_nonneg_left key (mul_nonneg (mul_nonneg hP (mul_self_nonneg Γ)) hT)
      _ = _ := by ring
  have B : ((sz.size n : ℕ) : ℝ) ^ τN * (X * ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u)) ≤
      ((sz.size n : ℕ) : ℝ) ^ τN * (Φ₁ + Φ₂ + Φ₃ + X) * ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u) := by
    calc ((sz.size n : ℕ) : ℝ) ^ τN * (X * ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u))
        ≤ ((sz.size n : ℕ) : ℝ) ^ τN * ((Φ₁ + Φ₂ + Φ₃ + X) *
          ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hT) hNτ
      _ = _ := by ring
  nlinarith [A, B]

/-- Target 9 (the merged quadratic level `dDriftAltQN` of S3-16b in the generic shape of target 6: `Pa` carries
the factor `1 + ΓΦ`, see Design (c)). -/
theorem dDriftAltQN_le_shape :
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (m : ℕ) (Γ Φ Cn ε' D' τN X : ℝ),
    |E| < 2 → u < 1 → 0 ≤ Γ → 0 ≤ Φ → 0 ≤ X →
      dDriftAltQN sz n E u m Γ Φ Cn ε' D' τN X ≤
        (((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * (Γ * Γ) * ((m + 1 + 1 : ℕ) : ℝ) * (1 + Γ * Φ) +
            ((sz.size n : ℕ) : ℝ) ^ τN) *
            (Φ + X) * ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u) +
          ((sz.W n : ℕ) : ℝ) ^ (-D' + Cn) := by
  intro d sz n E u m Γ Φ Cn ε' D' τN X hE hu hΓ hΦ hX
  have hη : 0 < etaT E u := etaT_pos hE hu
  have hB : 0 < sz.Bctl n u := Sizes.STBctl_pos sz n hu
  have hW0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hP : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (Cn * ε') := Real.rpow_nonneg hW0 _
  have hNτ : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τN := Real.rpow_nonneg hN0 _
  have hT : 0 ≤ (sz.Bctl n u) ^ (m + 1 + 1) / etaT E u := div_nonneg (pow_nonneg hB.le _) hη.le
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hk0 : (0 : ℝ) ≤ ((m + 1 + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold dDriftAltQN dDriftNonAltN
  have e : (etaT E u)⁻¹ * sz.Bctl n u ^ (m + 2) * X =
      X * ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u) := by
    rw [div_eq_mul_inv]; ring
  rw [e]
  have c1 : (((m + 1 + 1 : ℕ) : ℝ) - 1) + ((m + 1 + 1 : ℕ) : ℝ) * (Γ * Φ) ≤
      ((m + 1 + 1 : ℕ) : ℝ) * (1 + Γ * Φ) := by linarith
  have c2 : 0 ≤ Γ * Γ * Φ * ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u) :=
    mul_nonneg (mul_nonneg (mul_self_nonneg Γ) hΦ) hT
  have c3 : 0 ≤ Γ * Γ * ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u) *
      (((m + 1 + 1 : ℕ) : ℝ) * (1 + Γ * Φ)) :=
    mul_nonneg (mul_nonneg (mul_self_nonneg Γ) hT) (mul_nonneg hk0 (by positivity))
  have A : ((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * (Γ * (Γ * Φ) *
        ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u) *
        ((((m + 1 + 1 : ℕ) : ℝ) - 1) + ((m + 1 + 1 : ℕ) : ℝ) * (Γ * Φ))) ≤
      ((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * (Γ * Γ) * ((m + 1 + 1 : ℕ) : ℝ) * (1 + Γ * Φ) * (Φ + X) *
        ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u) := by
    have a1 : Γ * (Γ * Φ) * ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u) *
        ((((m + 1 + 1 : ℕ) : ℝ) - 1) + ((m + 1 + 1 : ℕ) : ℝ) * (Γ * Φ)) ≤
        Γ * Γ * ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u) *
          (((m + 1 + 1 : ℕ) : ℝ) * (1 + Γ * Φ)) * (Φ + X) := by
      calc Γ * (Γ * Φ) * ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u) *
            ((((m + 1 + 1 : ℕ) : ℝ) - 1) + ((m + 1 + 1 : ℕ) : ℝ) * (Γ * Φ))
          = (Γ * Γ * Φ * ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u)) *
            ((((m + 1 + 1 : ℕ) : ℝ) - 1) + ((m + 1 + 1 : ℕ) : ℝ) * (Γ * Φ)) := by ring
        _ ≤ (Γ * Γ * Φ * ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u)) *
            (((m + 1 + 1 : ℕ) : ℝ) * (1 + Γ * Φ)) := mul_le_mul_of_nonneg_left c1 c2
        _ = (Γ * Γ * ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u) *
            (((m + 1 + 1 : ℕ) : ℝ) * (1 + Γ * Φ))) * Φ := by ring
        _ ≤ (Γ * Γ * ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u) *
            (((m + 1 + 1 : ℕ) : ℝ) * (1 + Γ * Φ))) * (Φ + X) :=
            mul_le_mul_of_nonneg_left (by linarith) c3
    calc ((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * (Γ * (Γ * Φ) *
          ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u) *
          ((((m + 1 + 1 : ℕ) : ℝ) - 1) + ((m + 1 + 1 : ℕ) : ℝ) * (Γ * Φ)))
        ≤ ((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * (Γ * Γ * ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u) *
          (((m + 1 + 1 : ℕ) : ℝ) * (1 + Γ * Φ)) * (Φ + X)) := mul_le_mul_of_nonneg_left a1 hP
      _ = _ := by ring
  have B : ((sz.size n : ℕ) : ℝ) ^ τN * (X * ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u)) ≤
      ((sz.size n : ℕ) : ℝ) ^ τN * (Φ + X) * ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u) := by
    calc ((sz.size n : ℕ) : ℝ) ^ τN * (X * ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u))
        ≤ ((sz.size n : ℕ) : ℝ) ^ τN * ((Φ + X) * ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hT) hNτ
      _ = _ := by ring
  nlinarith [A, B]

end Levels

/-! ## 4. Target 10: the budget `budgetAltQN` -/

section Budget

/-- The absorption step of a far part (copy of the private `nqLin_absorb`, `NQLin.lean:847`):
`y N_p ≤ B`, `N_p⁻¹ ≤ X`, `B ≥ 0` give `y ≤ B X`. -/
private theorem QBudgetA_absorb {y Np B X : ℝ} (hNp : 0 < Np) (hB : 0 ≤ B) (h : y * Np ≤ B)
    (hX : Np⁻¹ ≤ X) : y ≤ B * X := by
  have h1 : y ≤ B * Np⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hNp]; exact h
  exact h1.trans (mul_le_mul_of_nonneg_left hX hB)

/-- `W^{2 C ε} = (W^{C ε})²` for `W ≥ 0` (the `G`-weight of `qvBdAltQN` is the square of the QV weight). -/
private theorem QBudgetA_rpow_two_mul {W : ℝ} (hW : 0 ≤ W) (C ε : ℝ) :
    W ^ (2 * C * ε) = (W ^ (C * ε)) ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hW]
  congr 1
  push_cast
  ring

/-- The final bookkeeping on plain reals: the six term bounds `t₁ ≤ P₀X/6`, `t₂ ≤ P₀X/12`,
`t₃ ≤ P₀Φd X/12 + P₀X/12`, `t₄ ≤ P₀Λ^{1/2}X/12 + P₀X/12`, `t₅, t₆ ≤ P₀X/6` give
`Σ t ≤ P₀ (Λ^{1/2} + Φd) X` (copy of `nqLin_final`, `NQLin.lean:943`, with `Φ₁ + Φ₂ + Φ₃ ↦ Φd`). -/
private theorem QBudgetA_final {t1 t2 t3 t4 t5 t6 P0 X Λr Φd : ℝ} (hP0 : 0 ≤ P0) (hX : 0 ≤ X)
    (hΛr : 1 ≤ Λr) (hΦd : 0 ≤ Φd) (T1 : t1 ≤ P0 / 6 * X) (T2 : t2 ≤ P0 / 12 * X)
    (T3 : t3 ≤ P0 / 12 * (Φd * X) + P0 / 12 * X)
    (T4 : t4 ≤ P0 / 12 * (Λr * X) + P0 / 12 * X) (T5 : t5 ≤ P0 / 6 * X)
    (T6 : t6 ≤ P0 / 6 * X) :
    t1 + t2 + t3 + t4 + t5 + t6 ≤ P0 * (Λr + Φd) * X := by
  have hPX : P0 * X ≤ P0 * (Λr * X) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hX hΛr) hP0
  have hΦX : 0 ≤ P0 * (Φd * X) := mul_nonneg hP0 (mul_nonneg hΦd hX)
  have e : P0 * (Λr + Φd) * X = P0 * (Λr * X) + P0 * (Φd * X) := by ring
  rw [e]
  nlinarith [T1, T2, T3, T4, T5, T6, hPX, hΦX]

/-- Target 10 (**the budget of the alternating endpoint**, `d ≥ 3`; analogue of `budgetNonAltLinN`, `NQLin.lean:966`):
at a fixed `n`, under explicit numerical inequalities only (eventual forms: S3-17b),
`assembledRHSAltQN ≤ N^{ε₀} (Λ^{1/2} + Φd) B_v^k`, `k = m + 2`, `C₄ = qProxy4C d k Λg κ' KL`,
`C_n = qProxyCn d (m+1) Λg KL C c`, `C_Q = qProxyCQ d (m+1) Λg KL C c`. -/
theorem budgetAltQN :
  ∀ {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n m : ℕ) (Λg κ' KL C c ε : ℝ)
    (Γ Λ : ℕ → ℝ) (dd : ℕ → ℝ) (Pa Φd b δ0 δD D'' D_Y D_t τK εq ε₀ ε₁ X0 : ℝ)
    (a : Fin (m + 1 + 1) → Zd d (sz.L n)),
    0 ≤ ε₁ → |E n| < 2 → 0 ≤ s n → s n ≤ v n → v n < 1 → K n ≠ 0 →
    (etaT (E n) (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) →
    gridStep s v K n * (etaT (E n) (v n))⁻¹ ≤ 1 →
    Γ n = ((sz.size n : ℕ) : ℝ) ^ ε₁ → 1 ≤ Λ n →
    0 ≤ Pa → 0 ≤ Φd → 0 ≤ b → 0 ≤ δ0 → 0 ≤ δD →
    (∀ j < K n, dd j ≤ Pa * Φd * ((sz.Bctl n (gridTime s v K n j)) ^ (m + 1 + 1) /
      etaT (E n) (gridTime s v K n j)) + b) →
    -- `hlog` (merged input, `nqBudget_merged_inputs` conjunct 1)
    ∑ j ∈ Finset.range (K n), gridStep s v K n / etaT (E n) (gridTime s v K n j) ≤
      (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) →
    -- `hX0` (initial level; S3-18a: `startLevelQN`)
    X0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ (m + 1 + 1) →
    -- `hR` (merged input, `nqBudget_merged_inputs` conjunct 2 at `k = m + 2`)
    ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ (m + 1 + 1) *
        stepErrN d (sz.L n) (sz.W n) (E n) (m + 1 + 1) (gridTime s v K n j) (gridTime s v K n (j + 1))
          (gridStep s v K n)
          (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ (m + 1 + 1)) ≤
      ((sz.size n : ℕ) : ℝ) ^ (-D_t) →
    -- `ha1` (initial term)
    ((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) * ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 →
    -- `ha2` (drift, main part)
    ((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) * Pa *
        ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 →
    -- `ha3` (quadratic variation, main part)
    ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) *
        ((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε) * ((sz.size n : ℕ) : ℝ) ^ ε₁ *
        Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1))) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 →
    -- `he0` (initial decay error)
    ((sz.size n : ℕ) : ℝ) ^ (m + 1 + 1) * (((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1 + 1) Λg κ' KL * δ0) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 →
    -- `he1` (drift, far part)
    ((sz.size n : ℕ) : ℝ) ^ (m + 1 + 1) * (altBudget_kapFar sz n (m + 1 + 1) Λg κ' KL ε * b +
        ((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1 + 1) Λg κ' KL * δD) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 →
    -- `he2` (quadratic variation, far part)
    ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.size n : ℕ) : ℝ) ^ (m + 1 + 1) *
        Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) * (altBudget_qvFar sz n (m + 1 + 1) Λg κ' KL ε *
          ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c)))) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 →
    -- `he3`, `he4`
    ((sz.size n : ℕ) : ℝ) ^ (m + 1 + 1) * ((sz.size n : ℕ) : ℝ) ^ (-D_Y) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 →
    ((sz.size n : ℕ) : ℝ) ^ (m + 1 + 1) * ((sz.size n : ℕ) : ℝ) ^ (-D_t) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 →
      assembledRHSAltQN sz E s v K n m Λg κ' KL C c ε Γ Λ dd δ0 δD D'' D_Y τK εq X0 a ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φd) * (sz.Bctl n (v n)) ^ (m + 1 + 1) := by
  intro d sz E s v K n m Λg κ' KL C c ε Γ Λ dd Pa Φd b δ0 δD D'' D_Y D_t τK εq ε₀ ε₁ X0 a hε₁ hE hs0
    hsv hv1 hK hη hΔη hΓ hΛ hPa hΦd hb hδ0 hδD hdd hlog hX0 hR ha1 ha2 ha3 he0 he1 he2 he3 he4
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
    have h : 1 ≤ (sz.W n * sz.L n) ^ d :=
      Nat.one_le_pow _ _ (Nat.mul_pos (sz.W_pos n) (by have := sz.three_le_L n; omega))
    exact_mod_cast (show 1 ≤ sz.size n from h)
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hNk : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) ^ (m + 1 + 1) := pow_pos hN0 _
  have hW0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hu0 : ∀ i, 0 ≤ gridTime s v K n i := fun i => QBudgetA_gridTime_nonneg hs0 hsv i
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi =>
    (QBudgetA_gridTime_le hsv hK hi).trans_lt hv1
  have huK := gridTime_last s v K n hK
  have hΔ0 : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n hsv
  have hKΔ1 : (K n : ℝ) * gridStep s v K n ≤ 1 := by
    rw [QBudgetA_K_mul_step hK]; linarith
  have hΓ0 : 0 ≤ Γ n := by rw [hΓ]; exact Real.rpow_nonneg hN0.le _
  have hΛ0 : 0 ≤ Λ n := by linarith
  have hBv0 := Sizes.STBctl_pos sz n hv1
  have hX0' : 0 ≤ (sz.Bctl n (v n)) ^ (m + 1 + 1) := pow_nonneg hBv0.le _
  have hXN : (((sz.size n : ℕ) : ℝ) ^ (m + 1 + 1))⁻¹ ≤ (sz.Bctl n (v n)) ^ (m + 1 + 1) := by
    rw [← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 hN0.le)
      (ContinuityNet.cont_inv_size_le_Bctl sz n (hs0.trans hsv) hv1) _
  have hP0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ := Real.rpow_nonneg hN0.le _
  have hLs0 : 0 ≤ (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) :=
    mul_nonneg (inv_nonneg.2 (mE_im_pos hE).le) (Real.log_nonneg hN1)
  have hWC0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1 + 1) Λg κ' KL :=
    Real.rpow_nonneg hW0 _
  have hWCε0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) :=
    Real.rpow_nonneg hW0 _
  have hWQ0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε) :=
    Real.rpow_nonneg hW0 _
  have hΛr1 : 1 ≤ Λ n ^ ((1 : ℝ) / 2) := Real.one_le_rpow hΛ (by norm_num)
  have hkap0 : 0 ≤ altBudget_kapFar sz n (m + 1 + 1) Λg κ' KL ε := by
    unfold altBudget_kapFar
    have hr : 0 ≤ (1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ) := by positivity
    positivity
  -- the far parts are absorbed once each (`he0`, `he1`)
  have hfar0 : ((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1 + 1) Λg κ' KL * δ0 ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ (m + 1 + 1) :=
    QBudgetA_absorb hNk (by positivity) ((mul_comm _ _).trans_le he0) hXN
  have hfar1 : altBudget_kapFar sz n (m + 1 + 1) Λg κ' KL ε * b +
      ((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1 + 1) Λg κ' KL * δD ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ (m + 1 + 1) :=
    QBudgetA_absorb hNk (by positivity) ((mul_comm _ _).trans_le he1) hXN
  have hfar1' : 0 ≤ altBudget_kapFar sz n (m + 1 + 1) Λg κ' KL ε * b +
      ((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1 + 1) Λg κ' KL * δD :=
    add_nonneg (mul_nonneg hkap0 hb) (mul_nonneg hWC0 hδD)
  -- T1: the initial term
  have T1 : _ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 * (sz.Bctl n (v n)) ^ (m + 1 + 1) :=
    (tbInitAltQN sz n (m + 1 + 1) Λg κ' KL ε (((sz.size n : ℕ) : ℝ) ^ ε₁) X0 hs0 hsv hv1 hK
      (Real.rpow_nonneg hN0.le _) hX0).trans (mul_le_mul_of_nonneg_right ha1 hX0')
  -- T2: the initial decay error
  have T2 : epsAltQN d (m + 1 + 1) Λg κ' KL ((sz.W n : ℕ) : ℝ) 0 (K n) * δ0 ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ (m + 1 + 1) := by
    unfold epsAltQN
    exact hfar0
  -- T3: the drift term (generic level `Pa Φd B^k/η + b`)
  have T3 : gridStep s v K n * ∑ j ∈ Finset.range (K n),
      (kappaAltQN d (m + 1 + 1) Λg κ' KL (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n)
          (j + 1) (K n) * dd j +
        epsAltQN d (m + 1 + 1) Λg κ' KL ((sz.W n : ℕ) : ℝ) (j + 1) (K n) * δD) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (Φd * (sz.Bctl n (v n)) ^ (m + 1 + 1)) +
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ (m + 1 + 1) := by
    have h := tbDriftAltQN sz (E := E) (s := s) (v := v) (K := K) n (m + 1 + 1) Λg κ' KL ε dd Pa
      Φd b δD hE hs0 hsv hv1 hK hPa hΦd hb hδD hη hdd
    refine h.trans ?_
    have m1 : ((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) * (Pa * Φd) *
          (sz.Bctl n (v n)) ^ (m + 1 + 1) *
          ∑ j ∈ Finset.range (K n), gridStep s v K n / etaT (E n) (gridTime s v K n j) ≤
        ((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) * (Pa * Φd) *
          (sz.Bctl n (v n)) ^ (m + 1 + 1) *
          ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (mul_nonneg (mul_nonneg hWCε0 (mul_nonneg hPa hΦd)) hX0')
    have m3 : ((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) * (Pa * Φd) *
          (sz.Bctl n (v n)) ^ (m + 1 + 1) *
          ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) =
        (((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) * Pa *
          ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ))) *
          (Φd * (sz.Bctl n (v n)) ^ (m + 1 + 1)) := by ring
    have m4 : (((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) * Pa *
          ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ))) *
          (Φd * (sz.Bctl n (v n)) ^ (m + 1 + 1)) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (Φd * (sz.Bctl n (v n)) ^ (m + 1 + 1)) :=
      mul_le_mul_of_nonneg_right ha2 (mul_nonneg hΦd hX0')
    have f1 : ((K n : ℝ) * gridStep s v K n) *
          (altBudget_kapFar sz n (m + 1 + 1) Λg κ' KL ε * b +
            ((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1 + 1) Λg κ' KL * δD) ≤
        altBudget_kapFar sz n (m + 1 + 1) Λg κ' KL ε * b +
          ((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1 + 1) Λg κ' KL * δD :=
      (mul_le_mul_of_nonneg_right hKΔ1 hfar1').trans_eq (one_mul _)
    exact add_le_add (m1.trans (m3.le.trans m4)) (f1.trans hfar1)
  -- T4: the quadratic-variation term
  have T4 : ((sz.size n : ℕ) : ℝ) ^ εq * Real.sqrt (∑ j ∈ Finset.range (K n),
      (cQVAltQN sz E s v K n m Λg κ' KL C c ε Γ Λ D'' (K n) a j : ℝ)) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (Λ n ^ ((1 : ℝ) / 2) * (sz.Bctl n (v n)) ^ (m + 1 + 1)) +
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ (m + 1 + 1) := by
    have h := tbQvAltQN sz n m Λg κ' KL C c ε Γ Λ D'' a hE hs0 hsv hv1 hK hΛ0 hη
    have hSv : ∑ j ∈ Finset.range (K n),
        gridStep s v K n / etaT (E n) (gridTime s v K n (j + 1)) ≤
        (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1 := by
      have hsucc := nqBudget_sum_succ_le (K := K n)
        (fun j => gridStep s v K n / etaT (E n) (gridTime s v K n j))
        (div_nonneg hΔ0 (etaT_pos hE (hu1 0 (Nat.zero_le _))).le)
      simp only [huK] at hsucc
      have hlast : gridStep s v K n / etaT (E n) (v n) ≤ 1 := by
        rw [div_eq_mul_inv]; exact hΔη
      linarith
    have hk0 : (0 : ℝ) ≤ ((m + 1 + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hWd0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c) :=
      Real.rpow_nonneg hW0 _
    have hqv0 : 0 ≤ altBudget_qvFar sz n (m + 1 + 1) Λg κ' KL ε := by
      unfold altBudget_qvFar
      have h2 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (m + 1 + 1) := by positivity
      positivity
    have hQe0 : 0 ≤ ((m + 1 + 1 : ℕ) : ℝ) * (altBudget_qvFar sz n (m + 1 + 1) Λg κ' KL ε *
        ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c)) := by positivity
    have hΓX : 0 ≤ Γ n * (sz.Bctl n (v n)) ^ (m + 1 + 1) := mul_nonneg hΓ0 hX0'
    have hA0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) *
        ((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε) *
        (Γ n * (sz.Bctl n (v n)) ^ (m + 1 + 1)) := mul_nonneg (mul_nonneg hWCε0 hWQ0) hΓX
    have hZ0 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) *
        ((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε) *
        (Γ n * (sz.Bctl n (v n)) ^ (m + 1 + 1))) ^ 2 * (((m + 1 + 1 : ℕ) : ℝ) * (
        (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) * Λ n) := by
      have : 0 ≤ (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1 := by linarith
      positivity
    have hsum : ∑ j ∈ Finset.range (K n),
        (cQVAltQN sz E s v K n m Λg κ' KL C c ε Γ Λ D'' (K n) a j : ℝ) ≤
        (((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) *
          ((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε) *
          (Γ n * (sz.Bctl n (v n)) ^ (m + 1 + 1))) ^ 2 *
          (((m + 1 + 1 : ℕ) : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) * Λ n) +
        ((m + 1 + 1 : ℕ) : ℝ) * (altBudget_qvFar sz n (m + 1 + 1) Λg κ' KL ε *
          ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c)) := by
      refine h.trans ?_
      have hc0 : 0 ≤ ((m + 1 + 1 : ℕ) : ℝ) *
          (((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε)) ^ 2 *
          (((sz.W n : ℕ) : ℝ) ^ (2 * qProxyCn d (m + 1) Λg KL C c * ε) * (Γ n * (Γ n * Λ n))) *
          ((sz.Bctl n (v n)) ^ (m + 1 + 1)) ^ 2 := by
        have e : Γ n * (Γ n * Λ n) = Γ n ^ 2 * Λ n := by ring
        have h2 := Real.rpow_nonneg hW0 (2 * qProxyCn d (m + 1) Λg KL C c * ε)
        rw [e]; positivity
      have n1 := mul_le_mul_of_nonneg_left hSv hc0
      have n2 : ((K n : ℝ) * gridStep s v K n) *
          (((m + 1 + 1 : ℕ) : ℝ) * (altBudget_qvFar sz n (m + 1 + 1) Λg κ' KL ε *
            ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c))) ≤
          ((m + 1 + 1 : ℕ) : ℝ) * (altBudget_qvFar sz n (m + 1 + 1) Λg κ' KL ε *
            ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c)) :=
        (mul_le_mul_of_nonneg_right hKΔ1 hQe0).trans_eq (one_mul _)
      have e : ((m + 1 + 1 : ℕ) : ℝ) *
            (((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε)) ^ 2 *
            (((sz.W n : ℕ) : ℝ) ^ (2 * qProxyCn d (m + 1) Λg KL C c * ε) * (Γ n * (Γ n * Λ n))) *
            ((sz.Bctl n (v n)) ^ (m + 1 + 1)) ^ 2 *
            ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) =
          (((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) *
            ((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε) *
            (Γ n * (sz.Bctl n (v n)) ^ (m + 1 + 1))) ^ 2 *
            (((m + 1 + 1 : ℕ) : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) *
              Λ n) := by
        rw [QBudgetA_rpow_two_mul hW0]; ring
      linarith
    have hs1 := Real.sqrt_le_sqrt hsum
    have hs2 : Real.sqrt ((((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) *
          ((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε) *
          (Γ n * (sz.Bctl n (v n)) ^ (m + 1 + 1))) ^ 2 *
          (((m + 1 + 1 : ℕ) : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) * Λ n) +
        ((m + 1 + 1 : ℕ) : ℝ) * (altBudget_qvFar sz n (m + 1 + 1) Λg κ' KL ε *
          ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c))) ≤
        ((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) *
          ((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε) *
          (Γ n * (sz.Bctl n (v n)) ^ (m + 1 + 1)) *
          (Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) *
            ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)) * Real.sqrt (Λ n)) +
        Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) * (altBudget_qvFar sz n (m + 1 + 1) Λg κ' KL ε *
          ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c))) := by
      refine (nqBudget_sqrt_add_le hZ0 hQe0).trans ?_
      have hP00 : 0 ≤ ((m + 1 + 1 : ℕ) : ℝ) *
          ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) :=
        mul_nonneg hk0 (by linarith)
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hA0, Real.sqrt_mul hP00]
    have hsΛ : Real.sqrt (Λ n) = Λ n ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow (Λ n)
    have hNe : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ εq := Real.rpow_nonneg hN0.le _
    have k1 : ((sz.size n : ℕ) : ℝ) ^ εq *
        (((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) *
          ((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε) *
          (Γ n * (sz.Bctl n (v n)) ^ (m + 1 + 1)) *
          (Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) *
            ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)) * Real.sqrt (Λ n))) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (Λ n ^ ((1 : ℝ) / 2) * (sz.Bctl n (v n)) ^ (m + 1 + 1)) := by
      have e : ((sz.size n : ℕ) : ℝ) ^ εq *
          (((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) *
            ((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε) *
            (Γ n * (sz.Bctl n (v n)) ^ (m + 1 + 1)) *
            (Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) *
              ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)) * Real.sqrt (Λ n))) =
          (((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) *
            ((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε) *
            ((sz.size n : ℕ) : ℝ) ^ ε₁ *
            Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) *
              ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)))) *
          (Λ n ^ ((1 : ℝ) / 2) * (sz.Bctl n (v n)) ^ (m + 1 + 1)) := by
        rw [hsΛ, hΓ]; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right ha3 (mul_nonneg (by linarith) hX0')
    have k2 : ((sz.size n : ℕ) : ℝ) ^ εq *
        Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) * (altBudget_qvFar sz n (m + 1 + 1) Λg κ' KL ε *
          ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c))) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ (m + 1 + 1) := by
      refine QBudgetA_absorb hNk (by positivity) ?_ hXN
      have e : ((sz.size n : ℕ) : ℝ) ^ εq *
          Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) * (altBudget_qvFar sz n (m + 1 + 1) Λg κ' KL ε *
            ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c))) *
            ((sz.size n : ℕ) : ℝ) ^ (m + 1 + 1) =
          ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.size n : ℕ) : ℝ) ^ (m + 1 + 1) *
            Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) * (altBudget_qvFar sz n (m + 1 + 1) Λg κ' KL ε *
              ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c)))) := by ring
      rw [e]; exact he2
    calc ((sz.size n : ℕ) : ℝ) ^ εq * Real.sqrt (∑ j ∈ Finset.range (K n),
          (cQVAltQN sz E s v K n m Λg κ' KL C c ε Γ Λ D'' (K n) a j : ℝ))
        ≤ ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) *
            ((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε) *
            (Γ n * (sz.Bctl n (v n)) ^ (m + 1 + 1)) *
            (Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) *
              ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)) * Real.sqrt (Λ n)) +
          Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) * (altBudget_qvFar sz n (m + 1 + 1) Λg κ' KL ε *
            ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c)))) :=
          mul_le_mul_of_nonneg_left (hs1.trans hs2) hNe
      _ = ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) *
            ((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε) *
            (Γ n * (sz.Bctl n (v n)) ^ (m + 1 + 1)) *
            (Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) *
              ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)) * Real.sqrt (Λ n))) +
          ((sz.size n : ℕ) : ℝ) ^ εq *
            Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) * (altBudget_qvFar sz n (m + 1 + 1) Λg κ' KL ε *
              ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c))) := by ring
      _ ≤ _ := add_le_add k1 k2
  -- T5, T6
  have T5 : ((sz.size n : ℕ) : ℝ) ^ (-D_Y) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 * (sz.Bctl n (v n)) ^ (m + 1 + 1) :=
    QBudgetA_absorb hNk (by positivity) ((mul_comm _ _).trans_le he3) hXN
  have T6 : _ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 * (sz.Bctl n (v n)) ^ (m + 1 + 1) :=
    hR.trans (QBudgetA_absorb hNk (by positivity) ((mul_comm _ _).trans_le he4) hXN)
  unfold assembledRHSAltQN
  exact QBudgetA_final hP0 hX0' hΛr1 hΦd T1 T2 T3 T4 T5 T6

end Budget

/-! ## 5. Compiled nonempty instances at `d = 3`

Data (the instance data of `NQLinInst`, `NQLin.lean:1256-1739`): `sz0` (`n = 0`: `L = 4`, `W = 32`, `N = 2^21`,
`lam = 1/64`), `E ≡ 1/2` (`Im m = √15/4 ≈ 0.968`), `s ≡ 0`, `v ≡ 1/32`, `K ≡ 4` (`Δ = 1/128`, `u_j = j/128`), `m = 1`
(`k = 3`), `Λ_g = 10`, `κ' = 1/2`, `K_L = 1`, `C = 1`, `c = 1/2`, `ε = 4/5`, `(Γ, Λ) = (4, 3)` with `Γ = N^{2/21}`,
`D'' = 7 + 2 C_n` (so that `-D'' + C_Q = -5`, and the hypothesis `(m+1)+2+C_Q < D''` of
`qvFormQN_le_of_goodSetN` at `m ↦ m+1` holds), `D_Y = 1`, `D_t = -5`, `τ_K = 1/21`, `ε_q = 1`, label `aFar`,
the drift level `dd j = dDriftAltLinQN(u_j)` at `(Γ, Φ₁, Φ₂, Φ₃, C_n, ε', D', τ_N, X) = (4, 1, 12, 1, C_n, 1/5, 6, 1, 1)`
and `ε₀ = C₄ + C_n + 12` with the abstract constants `C₄ = qProxy4C 3 3 10 (1/2) 1 > 0`,
`C_n = qProxyCn 3 2 10 1 1 (1/2) > 0`.  The eight absorption inequalities `ha1`-`he4` are proved for every
`C₄, C_n > 0` (private lemmas `*_inst`); `hlog`, `hR` are the merged `NQBudgetInst.hlog_instance`,
`hR_instance`; `hdd` is target 8 at the data. -/

namespace QBudgetAInst

open Filter RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst
  RBM.Gauss.GridGoodNInst RBM.Ind.AzumaProxyNInst RBM.Ind.NQGood1Inst

private theorem W0 : ((sz0.W 0 : ℕ) : ℝ) = 32 := by rw [sz0_values.2.1]; norm_num

private theorem lam0 : sz0.lam 0 = 1 / 64 := sz0_values.2.2.2

private theorem N0 : ((sz0.size 0 : ℕ) : ℝ) = 2097152 := by rw [sz0_values.2.2.1]; norm_num

private theorem abs_half : |(1 / 2 : ℝ)| < 2 := by norm_num [abs_of_pos]

private theorem im_ge : (24 / 25 : ℝ) ≤ (mE (1 / 2)).im := by
  rw [mE_im]
  have : (48 / 25 : ℝ) ≤ Real.sqrt (4 - (1 / 2) ^ 2) := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num
  linarith

private theorem eta_inv_le {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 32) : (etaT (1 / 2) t)⁻¹ ≤ 11 / 10 := by
  have hpos : 0 < etaT (1 / 2) t := etaT_pos abs_half (by linarith)
  rw [inv_eq_one_div, div_le_iff₀ hpos]
  have h1 : (31 / 32 : ℝ) ≤ 1 - t := by linarith
  have h2 := im_ge
  have h3 : (31 / 32 : ℝ) * (24 / 25) ≤ (1 - t) * (mE (1 / 2)).im :=
    mul_le_mul h1 h2 (by norm_num) (by linarith)
  unfold etaT
  linarith

private theorem eta_inv_le_N : (etaT (Einst 0) (vg 0))⁻¹ ≤ ((sz0.size 0 : ℕ) : ℝ) := by
  rw [N0]
  have h := eta_inv_le (t := vg 0) (by norm_num [vg]) (by norm_num [vg])
  have e : Einst 0 = 1 / 2 := rfl
  rw [e]
  linarith

private theorem eta_inv_le_v : (etaT (Einst 0) (vg 0))⁻¹ ≤ 11 / 10 :=
  eta_inv_le (t := vg 0) (by norm_num [vg]) (by norm_num [vg])

private theorem step0 : gridStep sInst vg Kg 0 = 1 / 128 := grid_data.1

private theorem two_pow_rpow (m : ℕ) (y : ℝ) : ((2 : ℝ) ^ m) ^ y = (2 : ℝ) ^ ((m : ℝ) * y) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]

private theorem two_rpow_nat_mul (C : ℝ) (m : ℕ) : (2 : ℝ) ^ ((m : ℝ) * C) = ((2 : ℝ) ^ C) ^ m := by
  rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_natCast]

private theorem W_rpow (y : ℝ) : ((sz0.W 0 : ℕ) : ℝ) ^ y = (2 : ℝ) ^ ((5 : ℝ) * y) := by
  have h := two_pow_rpow 5 y
  rw [W0, show (32 : ℝ) = 2 ^ 5 by norm_num, h]; norm_num

private theorem N_rpow (y : ℝ) : ((sz0.size 0 : ℕ) : ℝ) ^ y = (2 : ℝ) ^ ((21 : ℝ) * y) := by
  have h := two_pow_rpow 21 y
  rw [N0, show (2097152 : ℝ) = 2 ^ 21 by norm_num, h]; norm_num

/-- `W^{C ε} = (2^C)^4` (`W = 2^5`, `ε = 4/5`). -/
private theorem W_eps (C : ℝ) : ((sz0.W 0 : ℕ) : ℝ) ^ (C * (4 / 5)) = ((2 : ℝ) ^ C) ^ 4 := by
  rw [W_rpow, show (5 : ℝ) * (C * (4 / 5)) = ((4 : ℕ) : ℝ) * C by push_cast; ring, two_rpow_nat_mul]

/-- `W^{C ε'} = 2^C` (`ε' = 1/5`). -/
private theorem W_fifth (C : ℝ) : ((sz0.W 0 : ℕ) : ℝ) ^ (C * (1 / 5)) = (2 : ℝ) ^ C := by
  rw [W_rpow, show (5 : ℝ) * (C * (1 / 5)) = C by ring]

private theorem W_C (C : ℝ) : ((sz0.W 0 : ℕ) : ℝ) ^ C = ((2 : ℝ) ^ C) ^ 5 := by
  rw [W_rpow, show (5 : ℝ) * C = ((5 : ℕ) : ℝ) * C by push_cast; ring, two_rpow_nat_mul]

/-- `N^{ε₀} = (2^{C₄})^21 (2^{C_n})^21 2^252` for `ε₀ = C₄ + C_n + 12` (`N = 2^21`). -/
private theorem N_eps0 (C4 Cn : ℝ) :
    ((sz0.size 0 : ℕ) : ℝ) ^ (C4 + Cn + 12) = ((2 : ℝ) ^ C4) ^ 21 * ((2 : ℝ) ^ Cn) ^ 21 * 2 ^ 252 := by
  rw [N_rpow, show (21 : ℝ) * (C4 + Cn + 12) =
      ((21 : ℕ) : ℝ) * C4 + ((21 : ℕ) : ℝ) * Cn + ((252 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_add (by norm_num), Real.rpow_add (by norm_num), two_rpow_nat_mul, two_rpow_nat_mul,
    Real.rpow_natCast]

private theorem N_eps1 : ((sz0.size 0 : ℕ) : ℝ) ^ ((2 : ℝ) / 21) = 4 := by
  rw [N_rpow, show (21 : ℝ) * (2 / 21) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num

private theorem N_one : ((sz0.size 0 : ℕ) : ℝ) ^ (1 : ℝ) = 2097152 := by
  rw [Real.rpow_one, N0]

private theorem N_negone : ((sz0.size 0 : ℕ) : ℝ) ^ (-(1 : ℝ)) = 2097152⁻¹ := by
  rw [Real.rpow_neg_one, N0]

private theorem N_five : ((sz0.size 0 : ℕ) : ℝ) ^ (-(-5 : ℝ)) = 2097152 ^ 5 := by
  rw [neg_neg, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, N0]

private theorem W_neg (m : ℕ) : ((sz0.W 0 : ℕ) : ℝ) ^ (-(m : ℝ)) = ((32 : ℝ) ^ m)⁻¹ := by
  rw [Real.rpow_neg (by rw [W0]; norm_num), Real.rpow_natCast, W0]

private theorem W_neg6 : ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ)) = ((32 : ℝ) ^ 6)⁻¹ := by
  rw [show (-(6 : ℝ)) = -((6 : ℕ) : ℝ) by norm_num, W_neg]

private theorem W_neg5 : ((sz0.W 0 : ℕ) : ℝ) ^ (-(5 : ℝ)) = ((32 : ℝ) ^ 5)⁻¹ := by
  rw [show (-(5 : ℝ)) = -((5 : ℕ) : ℝ) by norm_num, W_neg]

/-- `W^{-6 + C} = (32^6)⁻¹ (2^C)^5`. -/
private theorem W_neg6_add (C : ℝ) :
    ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ) + C) = ((32 : ℝ) ^ 6)⁻¹ * ((2 : ℝ) ^ C) ^ 5 := by
  rw [Real.rpow_add (by rw [W0]; norm_num), W_neg6, W_C]

private theorem log_N : Real.log ((sz0.size 0 : ℕ) : ℝ) = 21 * Real.log 2 := by
  rw [N0, show (2097152 : ℝ) = 2 ^ 21 by norm_num, Real.log_pow]; norm_num

private theorem Ls_bounds :
    14 ≤ (mE (Einst 0)).im⁻¹ * Real.log ((sz0.size 0 : ℕ) : ℝ) ∧
      (mE (Einst 0)).im⁻¹ * Real.log ((sz0.size 0 : ℕ) : ℝ) ≤ 16 := by
  have e : Einst 0 = 1 / 2 := rfl
  rw [e, log_N]
  have hpos : 0 < (mE (1 / 2)).im := mE_im_pos abs_half
  have h1 : 1 ≤ (mE (1 / 2)).im⁻¹ := (one_le_inv₀ hpos).2 (nqBudget_im_le_one _)
  have h2 : (mE (1 / 2)).im⁻¹ ≤ 25 / 24 := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]; linarith [im_ge]
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  constructor
  · nlinarith
  · nlinarith

/-- The common absorption step: `x^a y^b c ≤ x^21 y^21 2^244` for `x, y ≥ 1`, `a, b ≤ 21`, `0 ≤ c ≤ 2^244`. -/
private theorem le_P {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) {a b : ℕ} (ha : a ≤ 21) (hb : b ≤ 21) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c ≤ 2 ^ 244) : x ^ a * y ^ b * c ≤ x ^ 21 * y ^ 21 * 2 ^ 244 := by
  have h1 : x ^ a ≤ x ^ 21 := pow_le_pow_right₀ hx ha
  have h2 : y ^ b ≤ y ^ 21 := pow_le_pow_right₀ hy hb
  have h3 : 0 ≤ x ^ a := by positivity
  have h4 : 0 ≤ y ^ b := by positivity
  calc x ^ a * y ^ b * c ≤ x ^ 21 * y ^ 21 * c :=
        mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 h4 (by positivity)) hc0
    _ ≤ x ^ 21 * y ^ 21 * 2 ^ 244 := mul_le_mul_of_nonneg_left hc (by positivity)

/-! ### The eight absorption inequalities at the data, for every `C₄, C_n > 0`
(`x = 2^{C₄}`, `y = 2^{C_n}`, `N^{ε₀} = x^21 y^21 2^252`) -/

private theorem ha1_inst (C4 Cn : ℝ) (hC4 : 0 < C4) (hCn : 0 < Cn) :
    ((sz0.W 0 : ℕ) : ℝ) ^ (C4 * (4 / 5)) * ((sz0.size 0 : ℕ) : ℝ) ^ ((2 : ℝ) / 21) ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (C4 + Cn + 12) / 6 := by
  have hx : 1 ≤ (2 : ℝ) ^ C4 := Real.one_le_rpow (by norm_num) hC4.le
  have hy : 1 ≤ (2 : ℝ) ^ Cn := Real.one_le_rpow (by norm_num) hCn.le
  rw [W_eps, N_eps1, N_eps0]
  have h := le_P hx hy (a := 4) (b := 0) (c := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hQ : 0 ≤ ((2 : ℝ) ^ C4) ^ 21 * ((2 : ℝ) ^ Cn) ^ 21 := by positivity
  simp only [pow_zero, mul_one] at h
  linarith

private theorem ha2_inst (C4 Cn : ℝ) (hC4 : 0 < C4) (hCn : 0 < Cn) :
    ((sz0.W 0 : ℕ) : ℝ) ^ (C4 * (4 / 5)) *
        (((sz0.W 0 : ℕ) : ℝ) ^ (Cn * (1 / 5)) * (Γ4 0 * Γ4 0) * (((1 + 1 + 1 : ℕ)) : ℝ) +
          ((sz0.size 0 : ℕ) : ℝ) ^ (1 : ℝ)) *
        ((mE (Einst 0)).im⁻¹ * Real.log ((sz0.size 0 : ℕ) : ℝ)) ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (C4 + Cn + 12) / 12 := by
  have hx : 1 ≤ (2 : ℝ) ^ C4 := Real.one_le_rpow (by norm_num) hC4.le
  have hy : 1 ≤ (2 : ℝ) ^ Cn := Real.one_le_rpow (by norm_num) hCn.le
  have hLs := Ls_bounds
  have hk : (((1 + 1 + 1 : ℕ)) : ℝ) = 3 := by norm_num
  have hΓ : Γ4 0 = 4 := rfl
  rw [W_eps, W_fifth, N_one, N_eps0, hk, hΓ]
  have hx4 : 0 ≤ ((2 : ℝ) ^ C4) ^ 4 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hLs.2
    (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ C4) ^ 4 * ((2 : ℝ) ^ Cn * (4 * 4) * 3 + 2097152))
  have hA := le_P hx hy (a := 4) (b := 1) (c := 768) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hB := le_P hx hy (a := 4) (b := 0) (c := 2 ^ 25) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hQ : 0 ≤ ((2 : ℝ) ^ C4) ^ 21 * ((2 : ℝ) ^ Cn) ^ 21 := by positivity
  simp only [pow_zero, mul_one, pow_one] at hA hB
  nlinarith

private theorem ha3_inst (C4 Cn : ℝ) (hC4 : 0 < C4) (hCn : 0 < Cn) :
    ((sz0.size 0 : ℕ) : ℝ) ^ (1 : ℝ) * (((sz0.W 0 : ℕ) : ℝ) ^ (C4 * (4 / 5)) *
        ((sz0.W 0 : ℕ) : ℝ) ^ (Cn * (4 / 5)) * ((sz0.size 0 : ℕ) : ℝ) ^ ((2 : ℝ) / 21) *
        Real.sqrt ((((1 + 1 + 1 : ℕ)) : ℝ) *
          ((mE (Einst 0)).im⁻¹ * Real.log ((sz0.size 0 : ℕ) : ℝ) + 1))) ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (C4 + Cn + 12) / 12 := by
  have hx : 1 ≤ (2 : ℝ) ^ C4 := Real.one_le_rpow (by norm_num) hC4.le
  have hy : 1 ≤ (2 : ℝ) ^ Cn := Real.one_le_rpow (by norm_num) hCn.le
  have hLs := Ls_bounds
  have hk : (((1 + 1 + 1 : ℕ)) : ℝ) = 3 := by norm_num
  have hs : Real.sqrt (3 * ((mE (Einst 0)).im⁻¹ * Real.log ((sz0.size 0 : ℕ) : ℝ) + 1)) ≤ 8 :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith [hLs.2]⟩
  rw [W_eps, W_eps, N_eps1, N_eps0, N_one, hk]
  have hxy : 0 ≤ ((2 : ℝ) ^ C4) ^ 4 * ((2 : ℝ) ^ Cn) ^ 4 := by positivity
  have h1 : ((2 : ℝ) ^ C4) ^ 4 * ((2 : ℝ) ^ Cn) ^ 4 * 4 * Real.sqrt (3 *
      ((mE (Einst 0)).im⁻¹ * Real.log ((sz0.size 0 : ℕ) : ℝ) + 1)) ≤
      ((2 : ℝ) ^ C4) ^ 4 * ((2 : ℝ) ^ Cn) ^ 4 * 4 * 8 :=
    mul_le_mul_of_nonneg_left hs (by positivity)
  have h := le_P hx hy (a := 4) (b := 4) (c := 2 ^ 26) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hQ : 0 ≤ ((2 : ℝ) ^ C4) ^ 21 * ((2 : ℝ) ^ Cn) ^ 21 := by positivity
  nlinarith

private theorem he0_inst (C4 Cn : ℝ) (hC4 : 0 < C4) (hCn : 0 < Cn) :
    ((sz0.size 0 : ℕ) : ℝ) ^ (1 + 1 + 1) *
        (((sz0.W 0 : ℕ) : ℝ) ^ C4 * (4 * ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ)))) ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (C4 + Cn + 12) / 12 := by
  have hx : 1 ≤ (2 : ℝ) ^ C4 := Real.one_le_rpow (by norm_num) hC4.le
  have hy : 1 ≤ (2 : ℝ) ^ Cn := Real.one_le_rpow (by norm_num) hCn.le
  rw [W_C, W_neg6, N_eps0, N0]
  have e : (2097152 : ℝ) ^ (1 + 1 + 1) * (((2 : ℝ) ^ C4) ^ 5 * (4 * ((32 : ℝ) ^ 6)⁻¹)) =
      ((2 : ℝ) ^ C4) ^ 5 * ((2 : ℝ) ^ Cn) ^ 0 * 34359738368 := by ring
  have h := le_P hx hy (a := 5) (b := 0) (c := 34359738368) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hQ : 0 ≤ ((2 : ℝ) ^ C4) ^ 21 * ((2 : ℝ) ^ Cn) ^ 21 := by positivity
  rw [e]
  nlinarith

private theorem he1_inst (C4 Cn : ℝ) (hC4 : 0 < C4) (hCn : 0 < Cn) :
    ((sz0.size 0 : ℕ) : ℝ) ^ (1 + 1 + 1) *
        (((sz0.W 0 : ℕ) : ℝ) ^ (C4 * (4 / 5)) *
              ((1 + sz0.lam 0 ^ 2) * ((sz0.size 0 : ℕ) : ℝ)) ^ (1 + 1 + 1) *
            ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ) + Cn) +
          ((sz0.W 0 : ℕ) : ℝ) ^ C4 * (4 * ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ)))) ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (C4 + Cn + 12) / 12 := by
  have hx : 1 ≤ (2 : ℝ) ^ C4 := Real.one_le_rpow (by norm_num) hC4.le
  have hy : 1 ≤ (2 : ℝ) ^ Cn := Real.one_le_rpow (by norm_num) hCn.le
  rw [W_eps, W_neg6_add, W_C, W_neg6, N_eps0, lam0, N0]
  have e : (2097152 : ℝ) ^ (1 + 1 + 1) * (((2 : ℝ) ^ C4) ^ 4 *
        ((1 + (1 / 64 : ℝ) ^ 2) * 2097152) ^ (1 + 1 + 1) * (((32 : ℝ) ^ 6)⁻¹ * ((2 : ℝ) ^ Cn) ^ 5) +
        ((2 : ℝ) ^ C4) ^ 5 * (4 * ((32 : ℝ) ^ 6)⁻¹)) =
      ((2 : ℝ) ^ C4) ^ 4 * ((2 : ℝ) ^ Cn) ^ 5 * ((2097152 : ℝ) ^ (1 + 1 + 1) *
        ((1 + (1 / 64 : ℝ) ^ 2) * 2097152) ^ (1 + 1 + 1) * ((32 : ℝ) ^ 6)⁻¹) +
      ((2 : ℝ) ^ C4) ^ 5 * ((2 : ℝ) ^ Cn) ^ 0 * 34359738368 := by ring
  have hA := le_P hx hy (a := 4) (b := 5) (c := (2097152 : ℝ) ^ (1 + 1 + 1) *
    ((1 + (1 / 64 : ℝ) ^ 2) * 2097152) ^ (1 + 1 + 1) * ((32 : ℝ) ^ 6)⁻¹) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hB := le_P hx hy (a := 5) (b := 0) (c := 34359738368) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have hQ : 0 ≤ ((2 : ℝ) ^ C4) ^ 21 * ((2 : ℝ) ^ Cn) ^ 21 := by positivity
  rw [e]
  nlinarith

private theorem he2_inst (C4 Cn : ℝ) (hC4 : 0 < C4) (hCn : 0 < Cn) :
    ((sz0.size 0 : ℕ) : ℝ) ^ (1 : ℝ) * (((sz0.size 0 : ℕ) : ℝ) ^ (1 + 1 + 1) *
        Real.sqrt ((((1 + 1 + 1 : ℕ)) : ℝ) *
          (((((sz0.W 0 : ℕ) : ℝ) ^ (C4 * (4 / 5)) *
                ((1 + sz0.lam 0 ^ 2) * ((sz0.size 0 : ℕ) : ℝ)) ^ (1 + 1 + 1)) *
              (((sz0.W 0 : ℕ) : ℝ) ^ (C4 * (4 / 5)) *
                  ((1 + sz0.lam 0 ^ 2) * ((sz0.size 0 : ℕ) : ℝ)) ^ (1 + 1 + 1) +
                ((sz0.W 0 : ℕ) : ℝ) ^ C4) +
              ((sz0.W 0 : ℕ) : ℝ) ^ C4 * ((sz0.W 0 : ℕ) : ℝ) ^ (1 + 1 + 1)) *
            ((sz0.W 0 : ℕ) : ℝ) ^ (-(5 : ℝ))))) ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (C4 + Cn + 12) / 12 := by
  have hx : 1 ≤ (2 : ℝ) ^ C4 := Real.one_le_rpow (by norm_num) hC4.le
  have hy : 1 ≤ (2 : ℝ) ^ Cn := Real.one_le_rpow (by norm_num) hCn.le
  have hk : (((1 + 1 + 1 : ℕ)) : ℝ) = 3 := by norm_num
  rw [W_eps, W_neg5, W_C, N_eps0, lam0, N_one, hk, W0, N0]
  generalize (2 : ℝ) ^ C4 = x at hx ⊢
  have hx0 : 0 ≤ x := by linarith
  have h8 : x ^ 8 ≤ x ^ 10 := pow_le_pow_right₀ hx (by norm_num)
  have h9 : x ^ 9 ≤ x ^ 10 := pow_le_pow_right₀ hx (by norm_num)
  have h5 : x ^ 5 ≤ x ^ 10 := pow_le_pow_right₀ hx (by norm_num)
  have hq : 3 * ((x ^ 4 * ((1 + (1 / 64 : ℝ) ^ 2) * 2097152) ^ (1 + 1 + 1) *
        (x ^ 4 * ((1 + (1 / 64 : ℝ) ^ 2) * 2097152) ^ (1 + 1 + 1) + x ^ 5) +
        x ^ 5 * (32 : ℝ) ^ (1 + 1 + 1)) * ((32 : ℝ) ^ 5)⁻¹) ≤ (x ^ 5 * 2 ^ 53) ^ 2 := by
    norm_num
    nlinarith [h8, h9, h5]
  have hs := Real.sqrt_le_iff.2 ⟨by positivity, hq⟩
  have h1 := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 2097152 ^ (1 + 1 + 1))
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2097152)
  have e : (2097152 : ℝ) * (2097152 ^ (1 + 1 + 1) * (x ^ 5 * 2 ^ 53)) = x ^ 5 * 2 ^ 137 := by ring
  rw [e] at h2
  have h := le_P hx hy (a := 5) (b := 0) (c := 2 ^ 137) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have hQ : 0 ≤ x ^ 21 * ((2 : ℝ) ^ Cn) ^ 21 := by positivity
  simp only [pow_zero, mul_one] at h
  linarith

private theorem he3_inst (C4 Cn : ℝ) (hC4 : 0 < C4) (hCn : 0 < Cn) :
    ((sz0.size 0 : ℕ) : ℝ) ^ (1 + 1 + 1) * ((sz0.size 0 : ℕ) : ℝ) ^ (-(1 : ℝ)) ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (C4 + Cn + 12) / 6 := by
  have hx : 1 ≤ (2 : ℝ) ^ C4 := Real.one_le_rpow (by norm_num) hC4.le
  have hy : 1 ≤ (2 : ℝ) ^ Cn := Real.one_le_rpow (by norm_num) hCn.le
  rw [N_eps0, N_negone, N0]
  have h := le_P hx hy (a := 0) (b := 0) (c := (2097152 : ℝ) ^ (1 + 1 + 1) * 2097152⁻¹)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hQ : 0 ≤ ((2 : ℝ) ^ C4) ^ 21 * ((2 : ℝ) ^ Cn) ^ 21 := by positivity
  simp only [pow_zero, mul_one, one_mul] at h
  linarith

private theorem he4_inst (C4 Cn : ℝ) (hC4 : 0 < C4) (hCn : 0 < Cn) :
    ((sz0.size 0 : ℕ) : ℝ) ^ (1 + 1 + 1) * ((sz0.size 0 : ℕ) : ℝ) ^ (-(-5 : ℝ)) ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (C4 + Cn + 12) / 6 := by
  have hx : 1 ≤ (2 : ℝ) ^ C4 := Real.one_le_rpow (by norm_num) hC4.le
  have hy : 1 ≤ (2 : ℝ) ^ Cn := Real.one_le_rpow (by norm_num) hCn.le
  rw [N_eps0, N_five, N0]
  have h := le_P hx hy (a := 0) (b := 0) (c := (2097152 : ℝ) ^ (1 + 1 + 1) * 2097152 ^ 5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hQ : 0 ≤ ((2 : ℝ) ^ C4) ^ 21 * ((2 : ℝ) ^ Cn) ^ 21 := by positivity
  have e : (2097152 : ℝ) ^ (1 + 1 + 1) * 2097152 ^ 5 = 2 ^ 168 := by norm_num
  rw [e] at h ⊢
  simp only [pow_zero, mul_one, one_mul] at h
  linarith

/-! ### Instances of targets 1-9 and of the budget (target 10) -/

local notation "C4₀" => qProxy4C 3 (1 + 1 + 1) 10 (1 / 2) 1
local notation "Cn₀" => qProxyCn 3 (1 + 1) 10 1 1 (1 / 2)

private theorem C4₀_pos : 0 < C4₀ :=
  qProxy4C_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem Cn₀_pos : 0 < Cn₀ :=
  qProxyCn_pos (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem s0 : 0 ≤ sInst 0 := by norm_num [sInst]

private theorem sv : sInst 0 ≤ vg 0 := by norm_num [sInst, vg]

private theorem v1 : vg 0 < 1 := by norm_num [vg]

private theorem K0 : Kg 0 ≠ 0 := by norm_num [Kg]

private theorem u_nonneg (j : ℕ) : 0 ≤ gridTime sInst vg Kg 0 j :=
  QBudgetA_gridTime_nonneg (K := Kg) s0 sv j

private theorem u_lt (j : ℕ) (hj : j ≤ Kg 0) : gridTime sInst vg Kg 0 j < 1 :=
  (QBudgetA_gridTime_le sv K0 hj).trans_lt v1

private theorem u_mono (i m : ℕ) (him : i ≤ m) : gridTime sInst vg Kg 0 i ≤ gridTime sInst vg Kg 0 m :=
  ST_gridTime_mono sInst vg Kg 0 sv him

private theorem u_zero : gridTime sInst vg Kg 0 0 = 0 := grid_data.2.1

private theorem u_last : gridTime sInst vg Kg 0 (Kg 0) = 1 / 32 := grid_data.2.2.2

private theorem inv_one_sub_le : (1 - gridTime sInst vg Kg 0 (Kg 0))⁻¹ ≤ ((sz0.size 0 : ℕ) : ℝ) := by
  rw [u_last, N0]; norm_num

private theorem Pa_nonneg (Cn : ℝ) : 0 ≤ ((sz0.W 0 : ℕ) : ℝ) ^ (Cn * (1 / 5)) * (Γ4 0 * Γ4 0) *
      (((1 + 1 + 1 : ℕ)) : ℝ) + ((sz0.size 0 : ℕ) : ℝ) ^ (1 : ℝ) :=
  add_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (mul_self_nonneg _))
    (Nat.cast_nonneg _)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- **The drift level at the data is below the generic shape** (target 8 at every grid time `u_j`, `j ≤ K`,
levels `(Γ, Φ₁, Φ₂, Φ₃, C_n, ε', D', τ_N, X) = (4, 1, 12, 1, C_n, 1/5, 6, 1, 1)`: `Pa = W^{C_n/5} 16 · 3 + N`,
`Φd = 15`, `b = W^{-6 + C_n}`). -/
private theorem hdd_inst (Cn : ℝ) : ∀ j < Kg 0,
    dDriftAltLinQN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 j) 1 (Γ4 0) 1 12 1 Cn (1 / 5) 6 1 1 ≤
      (((sz0.W 0 : ℕ) : ℝ) ^ (Cn * (1 / 5)) * (Γ4 0 * Γ4 0) * (((1 + 1 + 1 : ℕ)) : ℝ) +
          ((sz0.size 0 : ℕ) : ℝ) ^ (1 : ℝ)) * (1 + 12 + 1 + 1) *
        ((sz0.Bctl 0 (gridTime sInst vg Kg 0 j)) ^ (1 + 1 + 1) /
          etaT (Einst 0) (gridTime sInst vg Kg 0 j)) +
      ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ) + Cn) :=
  fun j hj => dDriftAltLinQN_le_shape sz0 0 (Einst 0) (gridTime sInst vg Kg 0 j) 1 (Γ4 0) 1 12 1 Cn
    (1 / 5) 6 1 1 (Einst_abs_lt 0) (u_lt j hj.le) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- **Instance of targets 1-3** (`k = 3`, `W = 32`, `(i, m) = (0, K_0)`, `u_i = 0 ≤ u_m = 1/32 < 1`). -/
example : kappaAltQN 3 3 10 (1 / 2) 1 (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (4 / 5) (gridTime sInst vg Kg 0) 0
      (Kg 0) * (sz0.Bctl 0 (gridTime sInst vg Kg 0 0)) ^ 3 ≤
    ((sz0.W 0 : ℕ) : ℝ) ^ (qProxy4C 3 3 10 (1 / 2) 1 * (4 / 5)) *
      (sz0.Bctl 0 (gridTime sInst vg Kg 0 (Kg 0))) ^ 3 :=
  kappaAltQN_mul_Bctl_pow_le sz0 0 3 10 (1 / 2) 1 (4 / 5) (Nat.cast_nonneg _) (gridTime sInst vg Kg 0)
    (u_mono 0 (Kg 0) (Nat.zero_le _)) (u_lt _ le_rfl)

example : kappaAltQN 3 3 10 (1 / 2) 1 (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (4 / 5) (gridTime sInst vg Kg 0) (0 + 1)
      (Kg 0) * (sz0.Bctl 0 (gridTime sInst vg Kg 0 0)) ^ 3 ≤
    ((sz0.W 0 : ℕ) : ℝ) ^ (qProxy4C 3 3 10 (1 / 2) 1 * (4 / 5)) *
      (sz0.Bctl 0 (gridTime sInst vg Kg 0 (Kg 0))) ^ 3 :=
  kappaAltQN_succ_mul_Bctl_pow_le sz0 0 3 10 (1 / 2) 1 (4 / 5) (Nat.cast_nonneg _) (gridTime sInst vg Kg 0) 0
    (Kg 0) (u_mono 0 1 (by norm_num)) (u_mono 1 (Kg 0) (by simp [Kg])) (u_lt _ le_rfl)

example : kappaAltQN 3 3 10 (1 / 2) 1 (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (4 / 5) (gridTime sInst vg Kg 0) 0
      (Kg 0) ≤ altBudget_kapFar sz0 0 3 10 (1 / 2) 1 (4 / 5) :=
  kappaAltQN_le_kapFar sz0 0 3 10 (1 / 2) 1 (4 / 5) (gridTime sInst vg Kg 0) (u_nonneg 0)
    (u_mono 0 (Kg 0) (Nat.zero_le _)) (u_lt _ le_rfl) inv_one_sub_le

/-- **Instance of target 4** (`m = 1`, `Γ = 4`, `Λ = 3`, `D = 7 + 2 C_n`, `u = 1/128`, `w = 1/32`). -/
example : qvBdAltQN sz0 0 (1 / 2) 1 10 (1 / 2) 1 1 (1 / 2) (4 / 5) 4 3 (7 + 2 * Cn₀) (1 / 128) (1 / 32) =
    nqBudget_qvShape (1 + 1 + 1)
      (((sz0.W 0 : ℕ) : ℝ) ^ (qProxy4C 3 (1 + 1 + 1) 10 (1 / 2) 1 * (4 / 5)) *
        ((sz0.lam 0 ^ 2 + |1 - 1 / 128|) / (sz0.lam 0 ^ 2 + |1 - 1 / 32|)) ^ (1 + 1 + 1))
      (((sz0.W 0 : ℕ) : ℝ) ^ qProxy4C 3 (1 + 1 + 1) 10 (1 / 2) 1)
      (((sz0.W 0 : ℕ) : ℝ) ^ qProxy4C 3 (1 + 1 + 1) 10 (1 / 2) 1 * ((sz0.W 0 : ℕ) : ℝ) ^ (1 + 1 + 1))
      (((sz0.W 0 : ℕ) : ℝ) ^ (2 * qProxyCn 3 (1 + 1) 10 1 1 (1 / 2) * (4 / 5)) * (4 * (4 * 3)))
      (((sz0.W 0 : ℕ) : ℝ) ^ (-(7 + 2 * Cn₀) + qProxyCQ 3 (1 + 1) 10 1 1 (1 / 2)))
      (sz0.Bctl 0 (1 / 128)) (etaT (1 / 2) (1 / 128)) :=
  qvBdAltQN_eq_qvShape sz0 0 (1 / 2) 1 10 (1 / 2) 1 1 (1 / 2) (4 / 5) 4 3 (7 + 2 * Cn₀) (1 / 128) (1 / 32)

/-- **Instance of target 5** (`X0 = 4 B_s^3`, `G = 4`). -/
example := tbInitAltQN sz0 (s := sInst) (v := vg) (K := Kg) 0 3 10 (1 / 2) 1 (4 / 5) 4
  (4 * (sz0.Bctl 0 (sInst 0)) ^ 3) s0 sv v1 K0 (by norm_num) le_rfl

/-- **Instance of target 6** (the drift level `dd j = dDriftAltLinQN(u_j)` of target 8, the shape data of
`hdd_inst`, `δ_D = 4 W^{-6}`). -/
example := tbDriftAltQN sz0 (E := Einst) (s := sInst) (v := vg) (K := Kg) 0 3 10 (1 / 2) 1 (4 / 5)
  (fun j => dDriftAltLinQN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 j) 1 (Γ4 0) 1 12 1 Cn₀ (1 / 5) 6 1 1)
  (((sz0.W 0 : ℕ) : ℝ) ^ (Cn₀ * (1 / 5)) * (Γ4 0 * Γ4 0) * (((1 + 1 + 1 : ℕ)) : ℝ) +
    ((sz0.size 0 : ℕ) : ℝ) ^ (1 : ℝ)) (1 + 12 + 1 + 1) (((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ) + Cn₀))
  (4 * ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ))) (Einst_abs_lt 0) s0 sv v1 K0 (Pa_nonneg Cn₀) (by norm_num)
  (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity) eta_inv_le_N (hdd_inst Cn₀)

/-- **Instance of target 7** (label `aFar`, `D'' = 7 + 2 C_n`). -/
example := tbQvAltQN sz0 (E := Einst) (s := sInst) (v := vg) (K := Kg) 0 1 10 (1 / 2) 1 1 (1 / 2) (4 / 5)
  Γ4 Λ3 (7 + 2 * Cn₀) aFar (Einst_abs_lt 0) s0 sv v1 K0 (by norm_num [Λ3]) eta_inv_le_N

/-- **Instance of target 8** (`u = 0`, `E = 1/2`, `m = 1`, levels `(4, 1, 12, 1)`). -/
example := dDriftAltLinQN_le_shape sz0 0 (1 / 2) 0 1 4 1 12 1 Cn₀ (1 / 5) 6 1 1 abs_half (by norm_num)
  (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Instance of target 9** (`u = 0`, `E = 1/2`, `m = 1`, `Γ = 4`, `Φ = 1`). -/
example := dDriftAltQN_le_shape sz0 0 (1 / 2) 0 1 4 1 Cn₀ (1 / 5) 6 1 1 abs_half (by norm_num)
  (by norm_num) (by norm_num) (by norm_num)

/-- **Instance of target 10** (`budgetAltQN` at the data above: `d = 3`, `sz0`, `n = 0`, `m = 1`): every hypothesis
is discharged (`hlog`, `hR` by the merged `NQBudgetInst`, `hdd` by target 8, `ha1`-`he4` for the abstract
positive constants `C₄ = qProxy4C 3 3 10 (1/2) 1`, `C_n = qProxyCn 3 2 10 1 1 (1/2)`); nothing is left open.
The right side is `N^{ε₀}(Λ^{1/2} + Φd) B_v^3` with `Φd = 1 + 12 + 1 + 1`. -/
theorem budgetAltQN_instance :
    assembledRHSAltQN sz0 Einst sInst vg Kg 0 1 10 (1 / 2) 1 1 (1 / 2) (4 / 5) Γ4 Λ3
        (fun j => dDriftAltLinQN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 j) 1 (Γ4 0) 1 12 1 Cn₀
          (1 / 5) 6 1 1)
        (4 * ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ))) (4 * ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ)))
        (7 + 2 * Cn₀) 1 (1 / 21) 1 (4 * (sz0.Bctl 0 (sInst 0)) ^ 3) aFar ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (C4₀ + Cn₀ + 12) *
        (Λ3 0 ^ ((1 : ℝ) / 2) + (1 + 12 + 1 + 1)) * (sz0.Bctl 0 (vg 0)) ^ (1 + 1 + 1) := by
  have hexp : -(7 + 2 * Cn₀) + qProxyCQ 3 (1 + 1) 10 1 1 (1 / 2) = -(5 : ℝ) := by
    unfold qProxyCQ; ring
  refine budgetAltQN sz0 Einst sInst vg Kg 0 1 10 (1 / 2) 1 1 (1 / 2) (4 / 5) Γ4 Λ3
    (fun j => dDriftAltLinQN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 j) 1 (Γ4 0) 1 12 1 Cn₀
      (1 / 5) 6 1 1)
    (((sz0.W 0 : ℕ) : ℝ) ^ (Cn₀ * (1 / 5)) * (Γ4 0 * Γ4 0) * (((1 + 1 + 1 : ℕ)) : ℝ) +
      ((sz0.size 0 : ℕ) : ℝ) ^ (1 : ℝ)) (1 + 12 + 1 + 1) (((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ) + Cn₀))
    (4 * ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ))) (4 * ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ)))
    (7 + 2 * Cn₀) 1 (-5) (1 / 21) 1 (C4₀ + Cn₀ + 12) (2 / 21) (4 * (sz0.Bctl 0 (sInst 0)) ^ 3) aFar
    (by norm_num) (Einst_abs_lt 0) s0 sv v1 K0 eta_inv_le_N (by rw [step0]; linarith [eta_inv_le_v])
    (by rw [N_eps1]) (by norm_num [Λ3]) (Pa_nonneg Cn₀) (by norm_num)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity) (by positivity) (hdd_inst Cn₀)
    NQBudgetInst.hlog_instance (by rw [N_eps1]) NQBudgetInst.hR_instance
    (ha1_inst _ _ C4₀_pos Cn₀_pos) (ha2_inst _ _ C4₀_pos Cn₀_pos) (ha3_inst _ _ C4₀_pos Cn₀_pos)
    (he0_inst _ _ C4₀_pos Cn₀_pos) (he1_inst _ _ C4₀_pos Cn₀_pos) ?_
    (he3_inst _ _ C4₀_pos Cn₀_pos) (he4_inst _ _ C4₀_pos Cn₀_pos)
  rw [hexp]
  exact he2_inst _ _ C4₀_pos Cn₀_pos

end QBudgetAInst

end RBM.Ind

end

#print axioms RBM.Ind.altBudget_kapFar
#print axioms RBM.Ind.altBudget_qvFar
#print axioms RBM.Ind.qvBdAltQN
#print axioms RBM.Ind.cQVAltQN
#print axioms RBM.Ind.dDriftAltLinQN
#print axioms RBM.Ind.assembledRHSAltQN
#print axioms RBM.Ind.kappaAltQN_mul_Bctl_pow_le
#print axioms RBM.Ind.kappaAltQN_succ_mul_Bctl_pow_le
#print axioms RBM.Ind.kappaAltQN_le_kapFar
#print axioms RBM.Ind.qvBdAltQN_eq_qvShape
#print axioms RBM.Ind.tbInitAltQN
#print axioms RBM.Ind.tbDriftAltQN
#print axioms RBM.Ind.tbQvAltQN
#print axioms RBM.Ind.dDriftAltLinQN_le_shape
#print axioms RBM.Ind.dDriftAltQN_le_shape
#print axioms RBM.Ind.budgetAltQN
#print axioms RBM.Ind.QBudgetAInst.budgetAltQN_instance
