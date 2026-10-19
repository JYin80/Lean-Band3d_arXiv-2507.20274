/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.QLevelsB
import RBM3D.Induction.QProxy
import RBM3D.Induction.NQLin
import RBM3D.Chain.NQBudgetGen
import RBM3D.Chain.NQLinGen

/-!
# The budget of the alternating endpoint at `d ≥ 3`

Paper: Lemma 4.10 (`lem:STOeq_Qt`), (4.36) `am;asoi222`, and the alternating case in the proof of
Lemma 4.17 (`lem:sum_decay_nonzero`), Subsection 4.5 `subsec:support`: (4.58) `eq:alternatecase1`,
(4.59) `y27kasdfg`, (4.61) `A4`, (4.60) `A5`, (4.62) `eq:alternatecase2` ("applying `(sum_res_2)` ... and
performing the integral over `v`"); the non-alternating budget it refers to is that of the proof of
Lemma 4.6 (`lem:STOeq_NQ`).

The `d ≥ 3` form of RBM2D's `AltBudgetTerms` / `AltBudget`, in the non-alternating shape on the generic
budgets of `NQBudget` (`tbInitN`, `tbDriftN`, `tbQvN`): one kernel `kappaAltQN`, one drift level
(entering generically, `dd j ≤ Pa Φd B_{u_j}^k/η_{u_j} + b`), no `ℚ/𝔼` split, no `AltBudgetHyp`
structure.  No probability, no `Prec`, no lift, no good set.

* §0 the vocabulary (band): `altBudget_kapFar`, `altBudget_qvFar`, `qvBdAltQN`, `cQVAltQN`,
  `dDriftAltLinQN`, `assembledRHSAltQN`; and over a carrier `Cm : Step2Mat sz` (namespace `RBM.Ind`,
  `open RBM.BA`): `altBudget_kapFarg`, `altBudget_qvFarg`, `qvBdAltQNg`, `cQVAltQNg`,
  `dDriftAltLinQNg`, `assembledRHSAltQNg` (§0g; explicit `Cv` for `qProxy4C`, `η_u = Cm.eta n u`,
  `stepErrNg`);
* §1g the kernel weights `kappaAltQNg_*`: the sharp kernel `κ_{i,m} B_{u_i}^k ≤ W^{C₄ε} B_{u_m}^k` and
  the far bound;
* §2g the term budgets `tbInitAltQNg`, `tbDriftAltQNg`, `tbQvAltQNg` on `tbInitNg`/`tbDriftNg`/`tbQvNg`
  (`LoopForm` and the inline `‖Cm.m n‖ ≤ 1` in place of `|E n| < 2`);
* §3g `dDriftAltLinQNg_le_shape`: the linear drift level in the generic shape;
* §4g `budgetAltQNg` (the proof of `budgetNonAltLinN` with the generic drift level, the extra `he0` and
  the `b` part of `he1`);
* §3b the band statements `dDriftAltLinQN_le_shape` and `budgetAltQN` (read by `QEndGrid`) are the
  corollaries at `bandStep2Mat`.

Helpers are `private` or prefixed `QBudgetA_`.
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

/-- **The far bound of the alternating kernel weight**: `κ_{i,m} ≤ W^{C₄ε} ((1+g²) N)^k` when `(1-u_m)⁻¹ ≤ N`
(`kappaAltQN`, exponent `k`, not `k-1`; analogue of `nqBudget_kapFar`). -/
def altBudget_kapFar {d : ℕ} (sz : Sizes d) (n k : ℕ) (Λg κ' KL ε : ℝ) : ℝ :=
  ((sz.W n : ℕ) : ℝ) ^ (qProxy4C d k Λg κ' KL * ε) *
    ((1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ)) ^ k

/-- **The far coefficient of the alternating quadratic variation**: `C_far (C_far + C_e) + C_c` of the generic
`tbQvN` at `C_far = altBudget_kapFar`, `C_e = W^{C₄}`, `C_c = W^{C₄} W^k`. -/
def altBudget_qvFar {d : ℕ} (sz : Sizes d) (n k : ℕ) (Λg κ' KL ε : ℝ) : ℝ :=
  altBudget_kapFar sz n k Λg κ' KL ε *
      (altBudget_kapFar sz n k Λg κ' KL ε + ((sz.W n : ℕ) : ℝ) ^ qProxy4C d k Λg κ' KL) +
    ((sz.W n : ℕ) : ℝ) ^ qProxy4C d k Λg κ' KL * ((sz.W n : ℕ) : ℝ) ^ k

/-- **The variance majorant of the `𝒬`-process** (tensors of `m + 1 + 1` indices): the right side of
`qvFormQNg_le_of_bounds` with its `m` at `m + 1`. -/
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
(the left side of the `hQ` premise of `azumaSubGQ_gridExitN`, at its `m` = `m + 1`; the label does
not enter; pattern `cQVNonAltN`). -/
def cQVAltQN {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n m : ℕ) (Λg κ' KL C c ε : ℝ)
    (Γ Λ : ℕ → ℝ) (D'' : ℝ) (p : ℕ) (_a : Fin (m + 1 + 1) → Zd d (sz.L n)) (j : ℕ) : ℝ≥0 :=
  (gridStep s v K n * (((m + 1 + 1 : ℕ) : ℝ) * qvBdAltQN sz n (E n) m Λg κ' KL C c ε (Γ n) (Λ n) D''
    (gridTime s v K n (j + 1)) (gridTime s v K n p))).toNNReal

/-- **The linear drift level of the alternating chain**, with the block level of `dDriftLinN`:
`W^{C_n ε'} Γ²(B^k/η)((k-2)Φ₁ + Φ₂ + Φ₃) + W^{-D'+C_n} + N^{τ_N} η⁻¹ B^{m+2} X`, `k = m + 2`. -/
def dDriftAltLinQN {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (m : ℕ) (Γ Φ₁ Φ₂ Φ₃ Cn ε' D' τN X : ℝ) : ℝ :=
  ((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * dDriftLinN sz n E u (m + 1 + 1) Γ Φ₁ Φ₂ Φ₃ +
    ((sz.W n : ℕ) : ℝ) ^ (-D' + Cn) +
    ((sz.size n : ℕ) : ℝ) ^ τN * ((etaT E u)⁻¹ * sz.Bctl n u ^ (m + 2) * X)

/-- **The right-hand side of the `AssembledN` at the target `K n` for the alternating chain** (tensors of
`m + 1 + 1` indices; pattern `assembledRHSLinN`): `κ = kappaAltQN`, `εK = epsAltQN` at `g = lam n`
(`alt_hkerQN`), initial supremum `X0`, initial decay error `δ0` (`alt_hA0clsQN`), drift levels `dd j` (generic:
`dDriftAltLinQN` at `u_j`), drift decay error `δD` (`alt_hDclsQN`: `4 W^{-D'}`), proxy `cQVAltQN`,
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

/-! ## 0b. Model-free private helpers -/

/-- `0 ≤ u_i` on the grid `0 ≤ s_n ≤ v_n` (as the private `nqBudget_gridTime_nonneg`). -/
private theorem QBudgetA_gridTime_nonneg {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hs0 : 0 ≤ s n)
    (hsv : s n ≤ v n) (i : ℕ) : 0 ≤ gridTime s v K n i := by
  have h := ST_gridTime_mono s v K n hsv (Nat.zero_le i)
  rw [ST_gridTime_zero] at h
  linarith

/-- `u_i ≤ v_n` for `i ≤ K_n`, `K_n ≠ 0` (as `nqBudget_gridTime_le`). -/
private theorem QBudgetA_gridTime_le {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hsv : s n ≤ v n)
    (hK : K n ≠ 0) {i : ℕ} (hi : i ≤ K n) : gridTime s v K n i ≤ v n :=
  (ST_gridTime_mono s v K n hsv hi).trans_eq (gridTime_last s v K n hK)

/-- `K Δ = v - s`. -/
private theorem QBudgetA_K_mul_step {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hK : K n ≠ 0) :
    (K n : ℝ) * gridStep s v K n = v n - s n := by
  have hK' : (K n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK
  unfold gridStep
  rw [mul_div_cancel₀ _ hK']

/-- The absorption step of a far part (as the private `nqLin_absorb`):
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
`Σ t ≤ P₀ (Λ^{1/2} + Φd) X` (as `nqLin_final`, with `Φ₁ + Φ₂ + Φ₃ ↦ Φd`). -/
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

/-! ## 0g. The vocabulary over a carrier -/

section VocabG

variable {d : ℕ} {sz : Sizes d}

/-- The far bound of the alternating kernel weight with the explicit constant `Cv` (band `altBudget_kapFar`, `Cv = qProxy4C d k Λg κ' KL`). -/
def altBudget_kapFarg (sz : Sizes d) (n k : ℕ) (Cv ε : ℝ) : ℝ :=
  ((sz.W n : ℕ) : ℝ) ^ (Cv * ε) * ((1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ)) ^ k

/-- The far coefficient of the alternating quadratic variation with the explicit constant `Cv` (band `altBudget_qvFar`). -/
def altBudget_qvFarg (sz : Sizes d) (n k : ℕ) (Cv ε : ℝ) : ℝ :=
  altBudget_kapFarg sz n k Cv ε * (altBudget_kapFarg sz n k Cv ε + ((sz.W n : ℕ) : ℝ) ^ Cv) +
    ((sz.W n : ℕ) : ℝ) ^ Cv * ((sz.W n : ℕ) : ℝ) ^ k

/-- The variance majorant of the `𝒬`-process over a carrier (band `qvBdAltQN`; `η_u = Cm.eta n u`, `C₄ = Cv` explicit,
`C_n`, `C_Q` the model-free `qProxyCn`, `qProxyCQ`). -/
def qvBdAltQNg (Cm : Step2Mat sz) (n m : ℕ) (Cv Λg KL C c ε Γ Λ D u w : ℝ) : ℝ :=
  (((sz.W n : ℕ) : ℝ) ^ (Cv * ε) *
      ((sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - w|)) ^ (m + 1 + 1)) *
    ((((sz.W n : ℕ) : ℝ) ^ (Cv * ε) *
        ((sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - w|)) ^ (m + 1 + 1)) *
      (((sz.W n : ℕ) : ℝ) ^ (2 * qProxyCn d (m + 1) Λg KL C c * ε) *
          (Γ * (Γ * Λ) * ((sz.Bctl n u) ^ (2 * (m + 1 + 1)) / Cm.eta n u)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D + qProxyCQ d (m + 1) Λg KL C c)) +
      ((sz.W n : ℕ) : ℝ) ^ Cv * ((sz.W n : ℕ) : ℝ) ^ (-D + qProxyCQ d (m + 1) Λg KL C c)) +
    ((sz.W n : ℕ) : ℝ) ^ Cv *
      (((sz.W n : ℕ) : ℝ) ^ (m + 1 + 1) * ((sz.W n : ℕ) : ℝ) ^ (-D + qProxyCQ d (m + 1) Λg KL C c))

/-- The sub-Gaussian proxy of the `j`-th propagated `𝒬`-increment towards `u_p` over a carrier (band `cQVAltQN`). -/
def cQVAltQNg (Cm : Step2Mat sz) (s v : ℕ → ℝ) (K : ℕ → ℕ) (n m : ℕ) (Cv Λg KL C c ε : ℝ)
    (Γ Λ : ℕ → ℝ) (D'' : ℝ) (p : ℕ) (_a : Fin (m + 1 + 1) → Zd d (sz.L n)) (j : ℕ) : ℝ≥0 :=
  (gridStep s v K n * (((m + 1 + 1 : ℕ) : ℝ) * qvBdAltQNg Cm n m Cv Λg KL C c ε (Γ n) (Λ n) D''
    (gridTime s v K n (j + 1)) (gridTime s v K n p))).toNNReal

/-- The linear drift level of the alternating chain over a carrier (band `dDriftAltLinQN`; `dDriftLinNg` of `Chain/NQLinGen`). -/
def dDriftAltLinQNg (Cm : Step2Mat sz) (n : ℕ) (u : ℝ) (m : ℕ) (Γ Φ₁ Φ₂ Φ₃ Cn ε' D' τN X : ℝ) : ℝ :=
  ((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * dDriftLinNg Cm n u (m + 1 + 1) Γ Φ₁ Φ₂ Φ₃ +
    ((sz.W n : ℕ) : ℝ) ^ (-D' + Cn) +
    ((sz.size n : ℕ) : ℝ) ^ τN * ((Cm.eta n u)⁻¹ * sz.Bctl n u ^ (m + 2) * X)

/-- The right-hand side of `AssembledNg` at the target `K n` for the alternating chain over a carrier (band `assembledRHSAltQN`). -/
def assembledRHSAltQNg (Cm : Step2Mat sz) (s v : ℕ → ℝ) (K : ℕ → ℕ) (n m : ℕ)
    (Cv Λg KL C c ε : ℝ) (Γ Λ : ℕ → ℝ) (dd : ℕ → ℝ) (δ0 δD D'' D_Y τK εq X0 : ℝ)
    (a : Fin (m + 1 + 1) → Zd d (sz.L n)) : ℝ :=
  kappaAltQNg (m + 1 + 1) Cv (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) 0 (K n) * X0 +
    epsAltQNg Cv ((sz.W n : ℕ) : ℝ) 0 (K n) * δ0 +
    gridStep s v K n * ∑ j ∈ Finset.range (K n),
      (kappaAltQNg (m + 1 + 1) Cv (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) (j + 1) (K n) *
          dd j +
        epsAltQNg Cv ((sz.W n : ℕ) : ℝ) (j + 1) (K n) * δD) +
    ((sz.size n : ℕ) : ℝ) ^ εq * Real.sqrt (∑ j ∈ Finset.range (K n),
      (cQVAltQNg Cm s v K n m Cv Λg KL C c ε Γ Λ D'' (K n) a j : ℝ)) +
    ((sz.size n : ℕ) : ℝ) ^ (-D_Y) +
    ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ (m + 1 + 1) *
      stepErrNg Cm.toFlowFM n (m + 1 + 1) (gridTime s v K n j) (gridTime s v K n (j + 1))
        (gridStep s v K n)
        (((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (gridTime s v K n (j + 1)))⁻¹ ^ (m + 1 + 1))

end VocabG

/-! ## 1g. The sharp kernel over a carrier -/

section KernelG

private theorem QBudgetA_kappag_nonneg (k : ℕ) (Cv g W ε : ℝ) (hW : 0 ≤ W) (u : ℕ → ℝ) (i m : ℕ) :
    0 ≤ kappaAltQNg k Cv g W ε u i m := by
  unfold kappaAltQNg
  exact mul_nonneg (Real.rpow_nonneg hW _)
    (pow_nonneg (div_nonneg (by positivity) (by positivity)) _)

private theorem QBudgetA_epsg_nonneg (Cv W : ℝ) (hW : 0 ≤ W) (i m : ℕ) : 0 ≤ epsAltQNg Cv W i m := by
  unfold epsAltQNg
  exact Real.rpow_nonneg hW _

/-- Sharp kernel, initial datum (model-free in the carrier). -/
theorem kappaAltQNg_mul_Bctl_pow_le {d : ℕ} (sz : Sizes d) (n k : ℕ) (Cv ε : ℝ) {W : ℝ} (hW : 0 ≤ W)
    (u : ℕ → ℝ) {i m : ℕ} (him : u i ≤ u m) (hm1 : u m < 1) :
    kappaAltQNg k Cv (sz.lam n) W ε u i m * (sz.Bctl n (u i)) ^ k ≤ W ^ (Cv * ε) * (sz.Bctl n (u m)) ^ k := by
  have hi1 : u i < 1 := him.trans_lt hm1
  have hBu : 0 < sz.Bctl n (u i) := Sizes.STBctl_pos sz n hi1
  have hr0 : 0 ≤ (sz.lam n ^ 2 + |1 - u i|) / (sz.lam n ^ 2 + |1 - u m|) :=
    div_nonneg (by positivity) (by positivity)
  have hrB := nqGood2_ratio_mul_Bctl_le sz n him hm1
  have hWC : 0 ≤ W ^ (Cv * ε) := Real.rpow_nonneg hW _
  unfold kappaAltQNg
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hr0 hBu.le) hrB k) hWC

/-- Sharp kernel, drift. -/
theorem kappaAltQNg_succ_mul_Bctl_pow_le {d : ℕ} (sz : Sizes d) (n k : ℕ) (Cv ε : ℝ) {W : ℝ} (hW : 0 ≤ W)
    (u : ℕ → ℝ) (j m : ℕ) (hjj : u j ≤ u (j + 1)) (hj1m : u (j + 1) ≤ u m) (hm1 : u m < 1) :
    kappaAltQNg k Cv (sz.lam n) W ε u (j + 1) m * (sz.Bctl n (u j)) ^ k ≤ W ^ (Cv * ε) * (sz.Bctl n (u m)) ^ k := by
  have hj1 : u (j + 1) < 1 := hj1m.trans_lt hm1
  have hBle : sz.Bctl n (u j) ≤ sz.Bctl n (u (j + 1)) := Sizes.STBctl_mono sz n hjj hj1
  have hBj : 0 < sz.Bctl n (u j) := Sizes.STBctl_pos sz n (hjj.trans_lt hj1)
  have hκ := QBudgetA_kappag_nonneg k Cv (sz.lam n) W ε hW u (j + 1) m
  calc kappaAltQNg k Cv (sz.lam n) W ε u (j + 1) m * (sz.Bctl n (u j)) ^ k
      ≤ kappaAltQNg k Cv (sz.lam n) W ε u (j + 1) m * (sz.Bctl n (u (j + 1))) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hBj.le hBle k) hκ
    _ ≤ W ^ (Cv * ε) * (sz.Bctl n (u m)) ^ k := kappaAltQNg_mul_Bctl_pow_le sz n k Cv ε hW u hj1m hm1

/-- Far bound. -/
theorem kappaAltQNg_le_kapFar {d : ℕ} (sz : Sizes d) (n k : ℕ) (Cv ε : ℝ) (u : ℕ → ℝ) {i m : ℕ}
    (hu0 : 0 ≤ u i) (hium : u i ≤ u m) (hm1 : u m < 1) (hN : (1 - u m)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) :
    kappaAltQNg k Cv (sz.lam n) ((sz.W n : ℕ) : ℝ) ε u i m ≤ altBudget_kapFarg sz n k Cv ε := by
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
  have hWC : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (Cv * ε) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  unfold kappaAltQNg altBudget_kapFarg
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr _) hWC

end KernelG

/-! ## 2g. The three term budgets over a carrier -/

section TermsG

variable {d : ℕ} {sz : Sizes d}

/-- The variance majorant is an `nqBudget_qvShape`. -/
theorem qvBdAltQNg_eq_qvShape (Cm : Step2Mat sz) (n m : ℕ) (Cv Λg KL C c ε Γ Λ D u w : ℝ) :
    qvBdAltQNg Cm n m Cv Λg KL C c ε Γ Λ D u w =
      nqBudget_qvShape (m + 1 + 1)
        (((sz.W n : ℕ) : ℝ) ^ (Cv * ε) * ((sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - w|)) ^ (m + 1 + 1))
        (((sz.W n : ℕ) : ℝ) ^ Cv) (((sz.W n : ℕ) : ℝ) ^ Cv * ((sz.W n : ℕ) : ℝ) ^ (m + 1 + 1))
        (((sz.W n : ℕ) : ℝ) ^ (2 * qProxyCn d (m + 1) Λg KL C c * ε) * (Γ * (Γ * Λ)))
        (((sz.W n : ℕ) : ℝ) ^ (-D + qProxyCQ d (m + 1) Λg KL C c)) (sz.Bctl n u) (Cm.eta n u) := by
  unfold qvBdAltQNg nqBudget_qvShape
  ring

/-- The initial term (no spectral hypothesis). -/
theorem tbInitAltQNg (sz : Sizes d) {s v : ℕ → ℝ} {K : ℕ → ℕ} (n k : ℕ) (Cv ε G X0 : ℝ)
    (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1) (hK : K n ≠ 0) (hG : 0 ≤ G)
    (hX0 : X0 ≤ G * (sz.Bctl n (s n)) ^ k) :
    kappaAltQNg k Cv (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) 0 (K n) * X0 ≤
      ((sz.W n : ℕ) : ℝ) ^ (Cv * ε) * G * (sz.Bctl n (v n)) ^ k := by
  have hW : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  have huK := gridTime_last s v K n hK
  have hu0 := ST_gridTime_zero s v K n
  have hκ0 := QBudgetA_kappag_nonneg k Cv (sz.lam n) ((sz.W n : ℕ) : ℝ) ε hW (gridTime s v K n) 0 (K n)
  have hker := kappaAltQNg_mul_Bctl_pow_le sz n k Cv ε hW (gridTime s v K n)
    (i := 0) (m := K n) (by rw [hu0, huK]; exact hsv) (by rw [huK]; exact hv1)
  rw [hu0, huK] at hker
  have h := tbInitNg (k := k) (K := K n) (Cκ := ((sz.W n : ℕ) : ℝ) ^ (Cv * ε))
    (G := G) (X0 := X0) (fun i => sz.Bctl n (gridTime s v K n i))
    (kappaAltQNg k Cv (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n)) hκ0 hG
    (by simpa only [hu0, huK] using hker) (by simpa only [hu0] using hX0)
  simpa only [huK] using h

/-- The drift term at a generic level `dd j ≤ Pa Φd B_{u_j}^k/η_{u_j} + b` (`LoopForm` and the inline `‖m‖ ≤ 1`
replace `|E n| < 2`). -/
theorem tbDriftAltQNg {E : ℕ → ℝ} {s v : ℕ → ℝ} {K : ℕ → ℕ} (Cm : Step2Mat sz) (hL : StepDecompGen_LoopForm Cm E)
    (n k : ℕ) (Cv ε : ℝ) (dd : ℕ → ℝ) (Pa Φd b δD : ℝ) (hm : ‖Cm.m n‖ ≤ 1) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n)
    (hv1 : v n < 1) (hK : K n ≠ 0) (hPa : 0 ≤ Pa) (hΦd : 0 ≤ Φd) (hb : 0 ≤ b) (hδD : 0 ≤ δD)
    (hη : (Cm.eta n (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ))
    (hdd : ∀ j < K n, dd j ≤ Pa * Φd * ((sz.Bctl n (gridTime s v K n j)) ^ k / Cm.eta n (gridTime s v K n j)) + b) :
    gridStep s v K n * ∑ j ∈ Finset.range (K n),
      (kappaAltQNg k Cv (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) (j + 1) (K n) * dd j +
        epsAltQNg Cv ((sz.W n : ℕ) : ℝ) (j + 1) (K n) * δD) ≤
      ((sz.W n : ℕ) : ℝ) ^ (Cv * ε) * (Pa * Φd) * (sz.Bctl n (v n)) ^ k *
          ∑ j ∈ Finset.range (K n), gridStep s v K n / Cm.eta n (gridTime s v K n j) +
        ((K n : ℝ) * gridStep s v K n) *
          (altBudget_kapFarg sz n k Cv ε * b + ((sz.W n : ℕ) : ℝ) ^ Cv * δD) := by
  have hW : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hu0 : ∀ i, 0 ≤ gridTime s v K n i := fun i => QBudgetA_gridTime_nonneg hs0 hsv i
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi =>
    (QBudgetA_gridTime_le hsv hK hi).trans_lt hv1
  have huK := gridTime_last s v K n hK
  have hmono : ∀ i m, i ≤ m → gridTime s v K n i ≤ gridTime s v K n m := fun i m him =>
    ST_gridTime_mono s v K n hsv him
  have hΔ0 : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n hsv
  have hN1 : (1 - v n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := NQBudgetGen_inv_one_sub_le hL hm hv1 hη
  have hsucc : ∀ j < K n, kappaAltQNg k Cv (sz.lam n) ((sz.W n : ℕ) : ℝ) ε
      (gridTime s v K n) (j + 1) (K n) * (sz.Bctl n (gridTime s v K n j)) ^ k ≤
      ((sz.W n : ℕ) : ℝ) ^ (Cv * ε) *
        (sz.Bctl n (gridTime s v K n (K n))) ^ k := fun j hj =>
    kappaAltQNg_succ_mul_Bctl_pow_le sz n k Cv ε hW (gridTime s v K n) j (K n)
      (hmono j (j + 1) (by omega)) (hmono (j + 1) (K n) (by omega)) (hu1 _ le_rfl)
  have h := tbDriftNg Cm n (k := k) (K := K n) (Δ := gridStep s v K n)
    (Cκ := ((sz.W n : ℕ) : ℝ) ^ (Cv * ε))
    (Cε := ((sz.W n : ℕ) : ℝ) ^ Cv)
    (Cfar := altBudget_kapFarg sz n k Cv ε)
    (a := Pa * Φd) (b := b) (δmax := δD) (gridTime s v K n)
    (fun i => sz.Bctl n (gridTime s v K n i))
    (kappaAltQNg k Cv (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n))
    (epsAltQNg Cv ((sz.W n : ℕ) : ℝ)) dd (fun _ => δD) hΔ0 (mul_nonneg hPa hΦd) hb
    (fun j hj => QBudgetA_kappag_nonneg k Cv (sz.lam n) ((sz.W n : ℕ) : ℝ) ε hW _
      (j + 1) (K n))
    (fun j hj => QBudgetA_epsg_nonneg Cv ((sz.W n : ℕ) : ℝ) hW (j + 1) (K n))
    hsucc
    (fun j hj => kappaAltQNg_le_kapFar sz n k Cv ε (gridTime s v K n) (hu0 (j + 1))
      (hmono (j + 1) (K n) (by omega)) (hu1 _ le_rfl) (by rw [huK]; exact hN1))
    (fun _ _ => le_rfl) hdd (fun _ _ => hδD) (fun _ _ => le_rfl)
    (fun j hj => NQGood1Gen_eta_pos hL n (hu1 j hj.le))
  rw [huK] at h
  exact h

/-- `qvBdAltQNg ≥ 0` for `Λ ≥ 0`, `u < 1` (so the `toNNReal` of `cQVAltQNg` is the identity). -/
private theorem QBudgetA_qvBdg_nonneg {E : ℕ → ℝ} (Cm : Step2Mat sz) (hL : StepDecompGen_LoopForm Cm E) (n m : ℕ)
    (Cv Λg KL C c ε Γ Λ D u w : ℝ) (hu1 : u < 1) (hΛ : 0 ≤ Λ) :
    0 ≤ qvBdAltQNg Cm n m Cv Λg KL C c ε Γ Λ D u w := by
  have hη : 0 < Cm.eta n u := NQGood1Gen_eta_pos hL n hu1
  have hB : 0 < sz.Bctl n u := Sizes.STBctl_pos sz n hu1
  have hW0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hG : 0 ≤ Γ * (Γ * Λ) := by
    have : Γ * (Γ * Λ) = Γ ^ 2 * Λ := by ring
    rw [this]; positivity
  have hG' : 0 ≤ Γ * (Γ * Λ) * ((sz.Bctl n u) ^ (2 * (m + 1 + 1)) / Cm.eta n u) :=
    mul_nonneg hG (div_nonneg (pow_nonneg hB.le _) hη.le)
  have hr : 0 ≤ (sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - w|) :=
    div_nonneg (by positivity) (by positivity)
  unfold qvBdAltQNg
  positivity

/-- The quadratic-variation term. -/
theorem tbQvAltQNg {E : ℕ → ℝ} {s v : ℕ → ℝ} {K : ℕ → ℕ} (Cm : Step2Mat sz) (hL : StepDecompGen_LoopForm Cm E)
    (n m : ℕ) (Cv Λg KL C c ε : ℝ) (Γ Λ : ℕ → ℝ) (D'' : ℝ) (a : Fin (m + 1 + 1) → Zd d (sz.L n))
    (hm : ‖Cm.m n‖ ≤ 1) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1) (hK : K n ≠ 0) (hΛ : 0 ≤ Λ n)
    (hη : (Cm.eta n (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) :
    ∑ j ∈ Finset.range (K n), (cQVAltQNg Cm s v K n m Cv Λg KL C c ε Γ Λ D'' (K n) a j : ℝ) ≤
      ((m + 1 + 1 : ℕ) : ℝ) * (((sz.W n : ℕ) : ℝ) ^ (Cv * ε)) ^ 2 *
          (((sz.W n : ℕ) : ℝ) ^ (2 * qProxyCn d (m + 1) Λg KL C c * ε) * (Γ n * (Γ n * Λ n))) *
          ((sz.Bctl n (v n)) ^ (m + 1 + 1)) ^ 2 *
          ∑ j ∈ Finset.range (K n), gridStep s v K n / Cm.eta n (gridTime s v K n (j + 1)) +
        ((K n : ℝ) * gridStep s v K n) *
          (((m + 1 + 1 : ℕ) : ℝ) * (altBudget_qvFarg sz n (m + 1 + 1) Cv ε *
            ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c))) := by
  have hW : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hu0 : ∀ i, 0 ≤ gridTime s v K n i := fun i => QBudgetA_gridTime_nonneg hs0 hsv i
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi =>
    (QBudgetA_gridTime_le hsv hK hi).trans_lt hv1
  have huK := gridTime_last s v K n hK
  have hmono : ∀ i m, i ≤ m → gridTime s v K n i ≤ gridTime s v K n m := fun i m him =>
    ST_gridTime_mono s v K n hsv him
  have hΔ0 : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n hsv
  have hN1 : (1 - v n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := NQBudgetGen_inv_one_sub_le hL hm hv1 hη
  have hWd : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c) :=
    Real.rpow_nonneg hW _
  have hWC : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ Cv :=
    Real.rpow_nonneg hW _
  have hG : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (2 * qProxyCn d (m + 1) Λg KL C c * ε) * (Γ n * (Γ n * Λ n)) := by
    have : Γ n * (Γ n * Λ n) = Γ n ^ 2 * Λ n := by ring
    rw [this]; have := Real.rpow_nonneg hW (2 * qProxyCn d (m + 1) Λg KL C c * ε); positivity
  have hcoe : ∀ j ∈ Finset.range (K n),
      (cQVAltQNg Cm s v K n m Cv Λg KL C c ε Γ Λ D'' (K n) a j : ℝ) =
        gridStep s v K n * (((m + 1 + 1 : ℕ) : ℝ) * nqBudget_qvShape (m + 1 + 1)
          (kappaAltQNg (m + 1 + 1) Cv (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n)
            (j + 1) (K n))
          (((sz.W n : ℕ) : ℝ) ^ Cv)
          (((sz.W n : ℕ) : ℝ) ^ Cv * ((sz.W n : ℕ) : ℝ) ^ (m + 1 + 1))
          (((sz.W n : ℕ) : ℝ) ^ (2 * qProxyCn d (m + 1) Λg KL C c * ε) * (Γ n * (Γ n * Λ n)))
          (((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c))
          (sz.Bctl n (gridTime s v K n (j + 1))) (Cm.eta n (gridTime s v K n (j + 1)))) := by
    intro j hj
    have hjK := Finset.mem_range.1 hj
    have hpos := QBudgetA_qvBdg_nonneg Cm hL n m Cv Λg KL C c ε (Γ n) (Λ n) D''
      (gridTime s v K n (j + 1)) (gridTime s v K n (K n)) (hu1 (j + 1) (by omega)) hΛ
    unfold cQVAltQNg
    rw [Real.coe_toNNReal _ (by positivity), qvBdAltQNg_eq_qvShape]
    rfl
  rw [Finset.sum_congr rfl hcoe]
  have h := tbQvNg Cm n (k := m + 1 + 1) (K := K n)
    (Cκ := ((sz.W n : ℕ) : ℝ) ^ (Cv * ε))
    (Cfar := altBudget_kapFarg sz n (m + 1 + 1) Cv ε)
    (Ce := ((sz.W n : ℕ) : ℝ) ^ Cv)
    (Cc := ((sz.W n : ℕ) : ℝ) ^ Cv * ((sz.W n : ℕ) : ℝ) ^ (m + 1 + 1))
    (G := ((sz.W n : ℕ) : ℝ) ^ (2 * qProxyCn d (m + 1) Λg KL C c * ε) * (Γ n * (Γ n * Λ n)))
    (Wd := ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c)) (Δ := gridStep s v K n)
    (gridTime s v K n) (fun i => sz.Bctl n (gridTime s v K n i))
    (fun j => kappaAltQNg (m + 1 + 1) Cv (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n)
      (j + 1) (K n))
    (fun j hj => (Sizes.STBctl_pos sz n (hu1 (j + 1) (by omega))).le)
    (fun j hj => QBudgetA_kappag_nonneg (m + 1 + 1) Cv (sz.lam n) ((sz.W n : ℕ) : ℝ) ε hW _
      (j + 1) (K n))
    (fun j hj => kappaAltQNg_mul_Bctl_pow_le sz n (m + 1 + 1) Cv ε hW (gridTime s v K n)
      (hmono (j + 1) (K n) (by omega)) (hu1 _ le_rfl))
    (fun j hj => kappaAltQNg_le_kapFar sz n (m + 1 + 1) Cv ε (gridTime s v K n) (hu0 (j + 1))
      (hmono (j + 1) (K n) (by omega)) (hu1 _ le_rfl) (by rw [huK]; exact hN1))
    hG hWd hWC hΔ0 (fun j hj => NQGood1Gen_eta_pos hL n (hu1 (j + 1) (by omega)))
  rw [huK] at h
  unfold altBudget_qvFarg
  exact h

end TermsG

/-! ## 3g. The linear drift level in the generic shape over a carrier -/

section LevelsG

variable {d : ℕ} {sz : Sizes d}

/-- The linear level in the generic shape of `tbDriftAltQNg` (band `dDriftAltLinQN_le_shape`: `Pa = W^{C_nε'}Γ²k + N^{τ_N}`,
`Φd = Φ₁ + Φ₂ + Φ₃ + X`, `b = W^{-D'+C_n}`). -/
theorem dDriftAltLinQNg_le_shape {E : ℕ → ℝ} (Cm : Step2Mat sz) (hL : StepDecompGen_LoopForm Cm E) (n : ℕ) (u : ℝ)
    (m : ℕ) (Γ Φ₁ Φ₂ Φ₃ Cn ε' D' τN X : ℝ) (hu : u < 1) (h1 : 0 ≤ Φ₁) (h2 : 0 ≤ Φ₂) (h3 : 0 ≤ Φ₃) (hX : 0 ≤ X) :
    dDriftAltLinQNg Cm n u m Γ Φ₁ Φ₂ Φ₃ Cn ε' D' τN X ≤
      (((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * (Γ * Γ) * ((m + 1 + 1 : ℕ) : ℝ) + ((sz.size n : ℕ) : ℝ) ^ τN) *
          (Φ₁ + Φ₂ + Φ₃ + X) * ((sz.Bctl n u) ^ (m + 1 + 1) / Cm.eta n u) +
        ((sz.W n : ℕ) : ℝ) ^ (-D' + Cn) := by
  have hη : 0 < Cm.eta n u := NQGood1Gen_eta_pos hL n hu
  have hB : 0 < sz.Bctl n u := Sizes.STBctl_pos sz n hu
  have hW0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hP : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (Cn * ε') := Real.rpow_nonneg hW0 _
  have hNτ : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τN := Real.rpow_nonneg hN0 _
  have hT : 0 ≤ (sz.Bctl n u) ^ (m + 1 + 1) / Cm.eta n u := div_nonneg (pow_nonneg hB.le _) hη.le
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hk : ((m + 1 + 1 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
  unfold dDriftAltLinQNg dDriftLinNg
  have e : (Cm.eta n u)⁻¹ * sz.Bctl n u ^ (m + 2) * X =
      X * ((sz.Bctl n u) ^ (m + 1 + 1) / Cm.eta n u) := by
    rw [div_eq_mul_inv]; ring
  rw [e]
  have key : (((m + 1 + 1 : ℕ) : ℝ) - 2) * Φ₁ + Φ₂ + Φ₃ ≤
      ((m + 1 + 1 : ℕ) : ℝ) * (Φ₁ + Φ₂ + Φ₃ + X) := by
    rw [hk]
    nlinarith [mul_nonneg hm0 h1, mul_nonneg hm0 h2, mul_nonneg hm0 h3, mul_nonneg hm0 hX]
  have A : ((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * (Γ * Γ * ((sz.Bctl n u) ^ (m + 1 + 1) / Cm.eta n u) *
        ((((m + 1 + 1 : ℕ) : ℝ) - 2) * Φ₁ + Φ₂ + Φ₃)) ≤
      ((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * (Γ * Γ) * ((m + 1 + 1 : ℕ) : ℝ) * (Φ₁ + Φ₂ + Φ₃ + X) *
        ((sz.Bctl n u) ^ (m + 1 + 1) / Cm.eta n u) := by
    calc ((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * (Γ * Γ * ((sz.Bctl n u) ^ (m + 1 + 1) / Cm.eta n u) *
          ((((m + 1 + 1 : ℕ) : ℝ) - 2) * Φ₁ + Φ₂ + Φ₃))
        = (((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * (Γ * Γ) * ((sz.Bctl n u) ^ (m + 1 + 1) / Cm.eta n u)) *
          ((((m + 1 + 1 : ℕ) : ℝ) - 2) * Φ₁ + Φ₂ + Φ₃) := by ring
      _ ≤ (((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * (Γ * Γ) * ((sz.Bctl n u) ^ (m + 1 + 1) / Cm.eta n u)) *
          (((m + 1 + 1 : ℕ) : ℝ) * (Φ₁ + Φ₂ + Φ₃ + X)) :=
          mul_le_mul_of_nonneg_left key (mul_nonneg (mul_nonneg hP (mul_self_nonneg Γ)) hT)
      _ = _ := by ring
  have B : ((sz.size n : ℕ) : ℝ) ^ τN * (X * ((sz.Bctl n u) ^ (m + 1 + 1) / Cm.eta n u)) ≤
      ((sz.size n : ℕ) : ℝ) ^ τN * (Φ₁ + Φ₂ + Φ₃ + X) * ((sz.Bctl n u) ^ (m + 1 + 1) / Cm.eta n u) := by
    calc ((sz.size n : ℕ) : ℝ) ^ τN * (X * ((sz.Bctl n u) ^ (m + 1 + 1) / Cm.eta n u))
        ≤ ((sz.size n : ℕ) : ℝ) ^ τN * ((Φ₁ + Φ₂ + Φ₃ + X) *
          ((sz.Bctl n u) ^ (m + 1 + 1) / Cm.eta n u)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hT) hNτ
      _ = _ := by ring
  nlinarith [A, B]

end LevelsG

/-! ## 4g. The budget `budgetAltQNg` -/

section BudgetG

variable {d : ℕ} {sz : Sizes d}

/-- **The budget of the alternating endpoint over a carrier** (band `budgetAltQN`; Subsection 4.5, proof of
Lemma 4.17): at a fixed `n`, under explicit
numerical inequalities only, `assembledRHSAltQNg ≤ N^{ε₀} (Λ^{1/2} + Φd) B_v^k`, `k = m + 2`, `C₄ = Cv` explicit,
`C_n = qProxyCn d (m+1) Λg KL C c`, `C_Q = qProxyCQ d (m+1) Λg KL C c`; `LoopForm` and the inline `‖Cm.m n‖ ≤ 1` replace `|E n| < 2`. -/
theorem budgetAltQNg {E : ℕ → ℝ} (Cm : Step2Mat sz) (hL : StepDecompGen_LoopForm Cm E) (s v : ℕ → ℝ) (K : ℕ → ℕ) (n m : ℕ)
    (Cv Λg KL C c ε : ℝ) (Γ Λ : ℕ → ℝ) (dd : ℕ → ℝ) (Pa Φd b δ0 δD D'' D_Y D_t τK εq ε₀ ε₁ X0 : ℝ)
    (a : Fin (m + 1 + 1) → Zd d (sz.L n))
    (hε₁ : 0 ≤ ε₁) (hm : ‖Cm.m n‖ ≤ 1) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1) (hK : K n ≠ 0)
    (hη : (Cm.eta n (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ))
    (hΔη : gridStep s v K n * (Cm.eta n (v n))⁻¹ ≤ 1)
    (hΓ : Γ n = ((sz.size n : ℕ) : ℝ) ^ ε₁) (hΛ : 1 ≤ Λ n)
    (hPa : 0 ≤ Pa) (hΦd : 0 ≤ Φd) (hb : 0 ≤ b) (hδ0 : 0 ≤ δ0) (hδD : 0 ≤ δD)
    (hdd : ∀ j < K n, dd j ≤ Pa * Φd * ((sz.Bctl n (gridTime s v K n j)) ^ (m + 1 + 1) /
      Cm.eta n (gridTime s v K n j)) + b)
    -- `hlog` (input, `nqBudget_merged_inputsg` conjunct 1)
    (hlog : ∑ j ∈ Finset.range (K n), gridStep s v K n / Cm.eta n (gridTime s v K n j) ≤
      (Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ))
    -- `hX0` (initial level; `startLevelQNg`)
    (hX0 : X0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ (m + 1 + 1))
    -- `hR` (input, `nqBudget_merged_inputsg` conjunct 2 at `k = m + 2`)
    (hR : ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ (m + 1 + 1) *
        stepErrNg Cm.toFlowFM n (m + 1 + 1) (gridTime s v K n j) (gridTime s v K n (j + 1))
          (gridStep s v K n)
          (((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (gridTime s v K n (j + 1)))⁻¹ ^ (m + 1 + 1)) ≤
      ((sz.size n : ℕ) : ℝ) ^ (-D_t))
    -- `ha1` (initial term), `ha2` (drift, main part), `ha3` (quadratic variation, main part)
    (ha1 : ((sz.W n : ℕ) : ℝ) ^ (Cv * ε) * ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6)
    (ha2 : ((sz.W n : ℕ) : ℝ) ^ (Cv * ε) * Pa * ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12)
    (ha3 : ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ (Cv * ε) *
        ((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε) * ((sz.size n : ℕ) : ℝ) ^ ε₁ *
        Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) * ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1))) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12)
    -- `he0` (initial decay error), `he1` (drift, far part), `he2` (quadratic variation, far part), `he3`, `he4`
    (he0 : ((sz.size n : ℕ) : ℝ) ^ (m + 1 + 1) * (((sz.W n : ℕ) : ℝ) ^ Cv * δ0) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12)
    (he1 : ((sz.size n : ℕ) : ℝ) ^ (m + 1 + 1) * (altBudget_kapFarg sz n (m + 1 + 1) Cv ε * b +
        ((sz.W n : ℕ) : ℝ) ^ Cv * δD) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12)
    (he2 : ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.size n : ℕ) : ℝ) ^ (m + 1 + 1) *
        Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) * (altBudget_qvFarg sz n (m + 1 + 1) Cv ε *
          ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c)))) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12)
    (he3 : ((sz.size n : ℕ) : ℝ) ^ (m + 1 + 1) * ((sz.size n : ℕ) : ℝ) ^ (-D_Y) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6)
    (he4 : ((sz.size n : ℕ) : ℝ) ^ (m + 1 + 1) * ((sz.size n : ℕ) : ℝ) ^ (-D_t) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6) :
    assembledRHSAltQNg Cm s v K n m Cv Λg KL C c ε Γ Λ dd δ0 δD D'' D_Y τK εq X0 a ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φd) * (sz.Bctl n (v n)) ^ (m + 1 + 1) := by
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
  have hLs0 : 0 ≤ (Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) :=
    mul_nonneg (inv_nonneg.2 (hL n).1.le) (Real.log_nonneg hN1)
  have hWC0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ Cv :=
    Real.rpow_nonneg hW0 _
  have hWCε0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (Cv * ε) :=
    Real.rpow_nonneg hW0 _
  have hWQ0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε) :=
    Real.rpow_nonneg hW0 _
  have hΛr1 : 1 ≤ Λ n ^ ((1 : ℝ) / 2) := Real.one_le_rpow hΛ (by norm_num)
  have hkap0 : 0 ≤ altBudget_kapFarg sz n (m + 1 + 1) Cv ε := by
    unfold altBudget_kapFarg
    have hr : 0 ≤ (1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ) := by positivity
    positivity
  -- the far parts are absorbed once each (`he0`, `he1`)
  have hfar0 : ((sz.W n : ℕ) : ℝ) ^ Cv * δ0 ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ (m + 1 + 1) :=
    QBudgetA_absorb hNk (by positivity) ((mul_comm _ _).trans_le he0) hXN
  have hfar1 : altBudget_kapFarg sz n (m + 1 + 1) Cv ε * b +
      ((sz.W n : ℕ) : ℝ) ^ Cv * δD ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ (m + 1 + 1) :=
    QBudgetA_absorb hNk (by positivity) ((mul_comm _ _).trans_le he1) hXN
  have hfar1' : 0 ≤ altBudget_kapFarg sz n (m + 1 + 1) Cv ε * b +
      ((sz.W n : ℕ) : ℝ) ^ Cv * δD :=
    add_nonneg (mul_nonneg hkap0 hb) (mul_nonneg hWC0 hδD)
    -- the initial term
  have T1 : _ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 * (sz.Bctl n (v n)) ^ (m + 1 + 1) :=
    (tbInitAltQNg sz n (m + 1 + 1) Cv ε (((sz.size n : ℕ) : ℝ) ^ ε₁) X0 hs0 hsv hv1 hK
      (Real.rpow_nonneg hN0.le _) hX0).trans (mul_le_mul_of_nonneg_right ha1 hX0')
    -- the initial decay error
  have T2 : epsAltQNg Cv ((sz.W n : ℕ) : ℝ) 0 (K n) * δ0 ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ (m + 1 + 1) := by
    unfold epsAltQNg
    exact hfar0
    -- the drift term (generic level `Pa Φd B^k/η + b`)
  have T3 : gridStep s v K n * ∑ j ∈ Finset.range (K n),
      (kappaAltQNg (m + 1 + 1) Cv (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n)
          (j + 1) (K n) * dd j +
        epsAltQNg Cv ((sz.W n : ℕ) : ℝ) (j + 1) (K n) * δD) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (Φd * (sz.Bctl n (v n)) ^ (m + 1 + 1)) +
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ (m + 1 + 1) := by
    have h := tbDriftAltQNg (E := E) (s := s) (v := v) (K := K) Cm hL n (m + 1 + 1) Cv ε dd Pa
      Φd b δD hm hs0 hsv hv1 hK hPa hΦd hb hδD hη hdd
    refine h.trans ?_
    have m1 : ((sz.W n : ℕ) : ℝ) ^ (Cv * ε) * (Pa * Φd) *
          (sz.Bctl n (v n)) ^ (m + 1 + 1) *
          ∑ j ∈ Finset.range (K n), gridStep s v K n / Cm.eta n (gridTime s v K n j) ≤
        ((sz.W n : ℕ) : ℝ) ^ (Cv * ε) * (Pa * Φd) *
          (sz.Bctl n (v n)) ^ (m + 1 + 1) *
          ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (mul_nonneg (mul_nonneg hWCε0 (mul_nonneg hPa hΦd)) hX0')
    have m3 : ((sz.W n : ℕ) : ℝ) ^ (Cv * ε) * (Pa * Φd) *
          (sz.Bctl n (v n)) ^ (m + 1 + 1) *
          ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) =
        (((sz.W n : ℕ) : ℝ) ^ (Cv * ε) * Pa *
          ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ))) *
          (Φd * (sz.Bctl n (v n)) ^ (m + 1 + 1)) := by ring
    have m4 : (((sz.W n : ℕ) : ℝ) ^ (Cv * ε) * Pa *
          ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ))) *
          (Φd * (sz.Bctl n (v n)) ^ (m + 1 + 1)) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (Φd * (sz.Bctl n (v n)) ^ (m + 1 + 1)) :=
      mul_le_mul_of_nonneg_right ha2 (mul_nonneg hΦd hX0')
    have f1 : ((K n : ℝ) * gridStep s v K n) *
          (altBudget_kapFarg sz n (m + 1 + 1) Cv ε * b +
            ((sz.W n : ℕ) : ℝ) ^ Cv * δD) ≤
        altBudget_kapFarg sz n (m + 1 + 1) Cv ε * b +
          ((sz.W n : ℕ) : ℝ) ^ Cv * δD :=
      (mul_le_mul_of_nonneg_right hKΔ1 hfar1').trans_eq (one_mul _)
    exact add_le_add (m1.trans (m3.le.trans m4)) (f1.trans hfar1)
    -- the quadratic-variation term
  have T4 : ((sz.size n : ℕ) : ℝ) ^ εq * Real.sqrt (∑ j ∈ Finset.range (K n),
      (cQVAltQNg Cm s v K n m Cv Λg KL C c ε Γ Λ D'' (K n) a j : ℝ)) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (Λ n ^ ((1 : ℝ) / 2) * (sz.Bctl n (v n)) ^ (m + 1 + 1)) +
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ (m + 1 + 1) := by
    have h := tbQvAltQNg (E := E) (s := s) (v := v) (K := K) Cm hL n m Cv Λg KL C c ε Γ Λ D'' a hm hs0 hsv hv1 hK hΛ0 hη
    have hSv : ∑ j ∈ Finset.range (K n),
        gridStep s v K n / Cm.eta n (gridTime s v K n (j + 1)) ≤
        (Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1 := by
      have hsucc := nqBudget_sum_succ_le (K := K n)
        (fun j => gridStep s v K n / Cm.eta n (gridTime s v K n j))
        (div_nonneg hΔ0 (NQGood1Gen_eta_pos hL n (hu1 0 (Nat.zero_le _))).le)
      simp only [huK] at hsucc
      have hlast : gridStep s v K n / Cm.eta n (v n) ≤ 1 := by
        rw [div_eq_mul_inv]; exact hΔη
      linarith
    have hk0 : (0 : ℝ) ≤ ((m + 1 + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hWd0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c) :=
      Real.rpow_nonneg hW0 _
    have hqv0 : 0 ≤ altBudget_qvFarg sz n (m + 1 + 1) Cv ε := by
      unfold altBudget_qvFarg
      have h2 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (m + 1 + 1) := by positivity
      positivity
    have hQe0 : 0 ≤ ((m + 1 + 1 : ℕ) : ℝ) * (altBudget_qvFarg sz n (m + 1 + 1) Cv ε *
        ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c)) := by positivity
    have hΓX : 0 ≤ Γ n * (sz.Bctl n (v n)) ^ (m + 1 + 1) := mul_nonneg hΓ0 hX0'
    have hA0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (Cv * ε) *
        ((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε) *
        (Γ n * (sz.Bctl n (v n)) ^ (m + 1 + 1)) := mul_nonneg (mul_nonneg hWCε0 hWQ0) hΓX
    have hZ0 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ (Cv * ε) *
        ((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε) *
        (Γ n * (sz.Bctl n (v n)) ^ (m + 1 + 1))) ^ 2 * (((m + 1 + 1 : ℕ) : ℝ) * (
        (Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) * Λ n) := by
      have : 0 ≤ (Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1 := by linarith
      positivity
    have hsum : ∑ j ∈ Finset.range (K n),
        (cQVAltQNg Cm s v K n m Cv Λg KL C c ε Γ Λ D'' (K n) a j : ℝ) ≤
        (((sz.W n : ℕ) : ℝ) ^ (Cv * ε) *
          ((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε) *
          (Γ n * (sz.Bctl n (v n)) ^ (m + 1 + 1))) ^ 2 *
          (((m + 1 + 1 : ℕ) : ℝ) * ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) * Λ n) +
        ((m + 1 + 1 : ℕ) : ℝ) * (altBudget_qvFarg sz n (m + 1 + 1) Cv ε *
          ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c)) := by
      refine h.trans ?_
      have hc0 : 0 ≤ ((m + 1 + 1 : ℕ) : ℝ) *
          (((sz.W n : ℕ) : ℝ) ^ (Cv * ε)) ^ 2 *
          (((sz.W n : ℕ) : ℝ) ^ (2 * qProxyCn d (m + 1) Λg KL C c * ε) * (Γ n * (Γ n * Λ n))) *
          ((sz.Bctl n (v n)) ^ (m + 1 + 1)) ^ 2 := by
        have e : Γ n * (Γ n * Λ n) = Γ n ^ 2 * Λ n := by ring
        have h2 := Real.rpow_nonneg hW0 (2 * qProxyCn d (m + 1) Λg KL C c * ε)
        rw [e]; positivity
      have n1 := mul_le_mul_of_nonneg_left hSv hc0
      have n2 : ((K n : ℝ) * gridStep s v K n) *
          (((m + 1 + 1 : ℕ) : ℝ) * (altBudget_qvFarg sz n (m + 1 + 1) Cv ε *
            ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c))) ≤
          ((m + 1 + 1 : ℕ) : ℝ) * (altBudget_qvFarg sz n (m + 1 + 1) Cv ε *
            ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c)) :=
        (mul_le_mul_of_nonneg_right hKΔ1 hQe0).trans_eq (one_mul _)
      have e : ((m + 1 + 1 : ℕ) : ℝ) *
            (((sz.W n : ℕ) : ℝ) ^ (Cv * ε)) ^ 2 *
            (((sz.W n : ℕ) : ℝ) ^ (2 * qProxyCn d (m + 1) Λg KL C c * ε) * (Γ n * (Γ n * Λ n))) *
            ((sz.Bctl n (v n)) ^ (m + 1 + 1)) ^ 2 *
            ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) =
          (((sz.W n : ℕ) : ℝ) ^ (Cv * ε) *
            ((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε) *
            (Γ n * (sz.Bctl n (v n)) ^ (m + 1 + 1))) ^ 2 *
            (((m + 1 + 1 : ℕ) : ℝ) * ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) *
              Λ n) := by
        rw [QBudgetA_rpow_two_mul hW0]; ring
      linarith
    have hs1 := Real.sqrt_le_sqrt hsum
    have hs2 : Real.sqrt ((((sz.W n : ℕ) : ℝ) ^ (Cv * ε) *
          ((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε) *
          (Γ n * (sz.Bctl n (v n)) ^ (m + 1 + 1))) ^ 2 *
          (((m + 1 + 1 : ℕ) : ℝ) * ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) * Λ n) +
        ((m + 1 + 1 : ℕ) : ℝ) * (altBudget_qvFarg sz n (m + 1 + 1) Cv ε *
          ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c))) ≤
        ((sz.W n : ℕ) : ℝ) ^ (Cv * ε) *
          ((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε) *
          (Γ n * (sz.Bctl n (v n)) ^ (m + 1 + 1)) *
          (Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) *
            ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)) * Real.sqrt (Λ n)) +
        Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) * (altBudget_qvFarg sz n (m + 1 + 1) Cv ε *
          ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c))) := by
      refine (nqBudget_sqrt_add_le hZ0 hQe0).trans ?_
      have hP00 : 0 ≤ ((m + 1 + 1 : ℕ) : ℝ) *
          ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) :=
        mul_nonneg hk0 (by linarith)
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hA0, Real.sqrt_mul hP00]
    have hsΛ : Real.sqrt (Λ n) = Λ n ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow (Λ n)
    have hNe : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ εq := Real.rpow_nonneg hN0.le _
    have k1 : ((sz.size n : ℕ) : ℝ) ^ εq *
        (((sz.W n : ℕ) : ℝ) ^ (Cv * ε) *
          ((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε) *
          (Γ n * (sz.Bctl n (v n)) ^ (m + 1 + 1)) *
          (Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) *
            ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)) * Real.sqrt (Λ n))) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (Λ n ^ ((1 : ℝ) / 2) * (sz.Bctl n (v n)) ^ (m + 1 + 1)) := by
      have e : ((sz.size n : ℕ) : ℝ) ^ εq *
          (((sz.W n : ℕ) : ℝ) ^ (Cv * ε) *
            ((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε) *
            (Γ n * (sz.Bctl n (v n)) ^ (m + 1 + 1)) *
            (Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) *
              ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)) * Real.sqrt (Λ n))) =
          (((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ (Cv * ε) *
            ((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε) *
            ((sz.size n : ℕ) : ℝ) ^ ε₁ *
            Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) *
              ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)))) *
          (Λ n ^ ((1 : ℝ) / 2) * (sz.Bctl n (v n)) ^ (m + 1 + 1)) := by
        rw [hsΛ, hΓ]; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right ha3 (mul_nonneg (by linarith) hX0')
    have k2 : ((sz.size n : ℕ) : ℝ) ^ εq *
        Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) * (altBudget_qvFarg sz n (m + 1 + 1) Cv ε *
          ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c))) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ (m + 1 + 1) := by
      refine QBudgetA_absorb hNk (by positivity) ?_ hXN
      have e : ((sz.size n : ℕ) : ℝ) ^ εq *
          Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) * (altBudget_qvFarg sz n (m + 1 + 1) Cv ε *
            ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c))) *
            ((sz.size n : ℕ) : ℝ) ^ (m + 1 + 1) =
          ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.size n : ℕ) : ℝ) ^ (m + 1 + 1) *
            Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) * (altBudget_qvFarg sz n (m + 1 + 1) Cv ε *
              ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c)))) := by ring
      rw [e]; exact he2
    calc ((sz.size n : ℕ) : ℝ) ^ εq * Real.sqrt (∑ j ∈ Finset.range (K n),
          (cQVAltQNg Cm s v K n m Cv Λg KL C c ε Γ Λ D'' (K n) a j : ℝ))
        ≤ ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ (Cv * ε) *
            ((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε) *
            (Γ n * (sz.Bctl n (v n)) ^ (m + 1 + 1)) *
            (Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) *
              ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)) * Real.sqrt (Λ n)) +
          Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) * (altBudget_qvFarg sz n (m + 1 + 1) Cv ε *
            ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c)))) :=
          mul_le_mul_of_nonneg_left (hs1.trans hs2) hNe
      _ = ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ (Cv * ε) *
            ((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε) *
            (Γ n * (sz.Bctl n (v n)) ^ (m + 1 + 1)) *
            (Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) *
              ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)) * Real.sqrt (Λ n))) +
          ((sz.size n : ℕ) : ℝ) ^ εq *
            Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) * (altBudget_qvFarg sz n (m + 1 + 1) Cv ε *
              ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c))) := by ring
      _ ≤ _ := add_le_add k1 k2
    -- the last two terms
  have T5 : ((sz.size n : ℕ) : ℝ) ^ (-D_Y) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 * (sz.Bctl n (v n)) ^ (m + 1 + 1) :=
    QBudgetA_absorb hNk (by positivity) ((mul_comm _ _).trans_le he3) hXN
  have T6 : _ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 * (sz.Bctl n (v n)) ^ (m + 1 + 1) :=
    hR.trans (QBudgetA_absorb hNk (by positivity) ((mul_comm _ _).trans_le he4) hXN)
  unfold assembledRHSAltQNg
  exact QBudgetA_final hP0 hX0' hΛr1 hΦd T1 T2 T3 T4 T5 T6

end BudgetG

/-! ## 3b. The band statements read by `QEndGrid` (name and type unchanged): corollaries at `bandStep2Mat` -/

/-- `dDriftAltLinQN_le_shape`, name and type as stated: the corollary of `dDriftAltLinQNg_le_shape` at `bandStep2Mat sz (fun _ => E)`
(`LoopForm` from `|E| < 2`, `stepDecompGen_loopForm_band`). -/
theorem dDriftAltLinQN_le_shape :
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (m : ℕ) (Γ Φ₁ Φ₂ Φ₃ Cn ε' D' τN X : ℝ),
    |E| < 2 → u < 1 → 0 ≤ Φ₁ → 0 ≤ Φ₂ → 0 ≤ Φ₃ → 0 ≤ X →
      dDriftAltLinQN sz n E u m Γ Φ₁ Φ₂ Φ₃ Cn ε' D' τN X ≤
        (((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * (Γ * Γ) * ((m + 1 + 1 : ℕ) : ℝ) + ((sz.size n : ℕ) : ℝ) ^ τN) *
            (Φ₁ + Φ₂ + Φ₃ + X) * ((sz.Bctl n u) ^ (m + 1 + 1) / etaT E u) +
          ((sz.W n : ℕ) : ℝ) ^ (-D' + Cn) := by
  intro d sz n E u m Γ Φ₁ Φ₂ Φ₃ Cn ε' D' τN X hE hu h1 h2 h3 hX
  exact dDriftAltLinQNg_le_shape (bandStep2Mat sz (fun _ => E))
    (stepDecompGen_loopForm_band sz (fun _ => E) (fun _ => hE)) n u m Γ Φ₁ Φ₂ Φ₃ Cn ε' D' τN X hu h1 h2 h3 hX

/-- `budgetAltQN`, name and type as stated: the corollary of `budgetAltQNg` at `bandStep2Mat sz (fun _ => E n)`,
`Cv = qProxy4C d (m + 2) Λg κ' KL` (`‖mE (E n)‖ = 1` from `|E n| < 2`). -/
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
    -- `hlog` (input, `nqBudget_merged_inputs` conjunct 1)
    ∑ j ∈ Finset.range (K n), gridStep s v K n / etaT (E n) (gridTime s v K n j) ≤
      (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) →
        -- `hX0` (initial level; `startLevelQN`)
    X0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ (m + 1 + 1) →
    -- `hR` (input, `nqBudget_merged_inputs` conjunct 2 at `k = m + 2`)
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
  exact budgetAltQNg (bandStep2Mat sz (fun _ => E n)) (stepDecompGen_loopForm_band sz (fun _ => E n) (fun _ => hE))
    s v K n m (qProxy4C d (m + 1 + 1) Λg κ' KL) Λg KL C c ε Γ Λ dd Pa Φd b δ0 δD D'' D_Y D_t τK εq ε₀ ε₁ X0 a
    hε₁ (norm_mE hE.le).le hs0 hsv hv1 hK hη hΔη hΓ hΛ hPa hΦd hb hδ0 hδD hdd hlog hX0 hR ha1 ha2 ha3 he0 he1 he2 he3 he4

end RBM.Ind

end
