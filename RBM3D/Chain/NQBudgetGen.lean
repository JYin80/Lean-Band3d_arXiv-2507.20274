/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.NQGood2Gen
import RBM3D.Induction.NQBudget

/-!
# The term budgets of the non-alternating assembled bound over the carrier (U3s2b, file 1; ticket T2491)

Generic forms of `Induction/NQBudget.lean` (not edited) over a carrier `Cm : Step2Mat sz`, namespace `RBM.BA`, no `BA/*` import.
Paper: arXiv:2507.20274, `lem:STOeq_NQ` (`3_5:1136`, proof `3_5:1152`), (5.93) (`3_5:1158`).  `etaT E` is `Cm.eta n` (`LoopForm`), the
constant `nqGood1C d k Λg κ'` is an explicit `Ck`, `stepErrN` is `stepErrNg`, `(mE E).im` is `(Cm.m n).im`; the spectral facts
`0 < Im m` (`LoopForm`) and `‖Cm.m n‖ ≤ 1` (D3, inline, per index) replace `|E n| < 2`.

* **Target 7** `assembledRHSNonAltNg`, `NQBudgetGen_kapFar`, `NQBudgetGen_qvFar` (the vocabulary), `NQBudgetGen_inv_one_sub_le`,
  `NQBudgetGen_kappa_le_kapFar`, the generic budgets `tbInitNg` (model-free: the band `tbInitN`), `tbDriftNg`, `tbQvNg`, their instances at the
  data `qvBdNonAltNg_eq_qvShape`, `tbInitNonAltNg`, `tbDriftNonAltNg`, `tbQvNonAltNg`, the budget `budgetNonAltNg` (band `budgetNonAltN`,
  `NQBudget:555`), and `nqBudget_merged_inputsg` (the hypotheses `hlog`, `hR` of `budgetNonAltNg` are the conclusions of the merged
  `sum_gridStep_div_etaNg_le` and `sum_weighted_stepErrNg_le` at `m = K n`).  The scalar `nqBudget_qvShape`, `nqBudget_sum_succ_le`,
  `nqBudget_sqrt_add_le` are model-free and used by name.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open private nqBudget_absorb nqBudget_gridTime_nonneg nqBudget_gridTime_le nqBudget_K_mul_step nqBudget_final
  from RBM3D.Induction.NQBudget

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes
open RBM.Ind (nqBudget_qvShape nqBudget_sum_succ_le nqBudget_sqrt_add_le tbInitN nqGood1C)

/-! ## 1. The vocabulary -/

section Vocab

variable {d : ℕ}

/-- **The right-hand side of `AssembledNg` at `m = K n`** with the data of the non-alternating endpoint (band `assembledRHSNonAltN`,
`NQBudget:57`): `κ = kappaNonAltNg`, `εK = epsNonAltNg`, `δ₀ = δ_D = W^{-D'}`, `d_j = dDriftNonAltNg(u_j)`, `c = cQVNonAltNg`,
`stepErr_j = stepErrNg` at the envelope `B_k = N^{τ_K} η_{u_{j+1}}^{-k}`, initial supremum `X0`, Azuma exponent `εq`, `D = D_Y`. -/
def assembledRHSNonAltNg {sz : Sizes d} (Cm : Step2Mat sz) (s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (Ck ε : ℝ) (Γ Λ Φ : ℕ → ℝ)
    (D' D'' D_Y τK εq X0 : ℝ) (a : Fin k → Zd d (sz.L n)) : ℝ :=
  kappaNonAltNg k Ck (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) 0 (K n) * X0 +
    epsNonAltNg Ck ((sz.W n : ℕ) : ℝ) 0 (K n) * ((sz.W n : ℕ) : ℝ) ^ (-D') +
    gridStep s v K n * ∑ j ∈ Finset.range (K n),
      (kappaNonAltNg k Ck (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) (j + 1) (K n) *
          dDriftNonAltNg Cm n (gridTime s v K n j) k (Γ n) (Φ n) +
        epsNonAltNg Ck ((sz.W n : ℕ) : ℝ) (j + 1) (K n) * ((sz.W n : ℕ) : ℝ) ^ (-D')) +
    ((sz.size n : ℕ) : ℝ) ^ εq * Real.sqrt (∑ j ∈ Finset.range (K n),
      (cQVNonAltNg Cm s v K n k Ck ε Γ Λ D'' (K n) a j : ℝ)) +
    ((sz.size n : ℕ) : ℝ) ^ (-D_Y) +
    ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k *
      stepErrNg Cm.toFlowFM n k (gridTime s v K n j) (gridTime s v K n (j + 1))
        (gridStep s v K n)
        (((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (gridTime s v K n (j + 1)))⁻¹ ^ k)

/-- **The far bound of the kernel weight** (band `nqBudget_kapFar`, `NQBudget:101`): `κ_{i,m} ≤ W^{Ck ε} ((1+g²) N)^{k-1}` when
`(1-u_m)⁻¹ ≤ N` (see `NQBudgetGen_kappa_le_kapFar`). -/
def NQBudgetGen_kapFar (sz : Sizes d) (n k : ℕ) (Ck ε : ℝ) : ℝ :=
  ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) * ((1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ)) ^ (k - 1)

/-- **The far coefficient of the quadratic variation** (band `nqBudget_qvFar`): the coefficient of `W^{-D''}` in `nqBudget_qvShape` at
`κ ≤ NQBudgetGen_kapFar`, `Ce = W^{Ck}`, `Cc = W^{Ck} W^k`. -/
def NQBudgetGen_qvFar (sz : Sizes d) (n k : ℕ) (Ck ε : ℝ) : ℝ :=
  NQBudgetGen_kapFar sz n k Ck ε * (NQBudgetGen_kapFar sz n k Ck ε + ((sz.W n : ℕ) : ℝ) ^ Ck) +
    ((sz.W n : ℕ) : ℝ) ^ Ck * ((sz.W n : ℕ) : ℝ) ^ k

/-- Band bridges of the vocabulary at `Ck = nqGood1C d k Λg κ'` (definitional). -/
theorem assembledRHSNonAltNg_band (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (Λg κ' ε : ℝ) (Γ Λ Φ : ℕ → ℝ)
    (D' D'' D_Y τK εq X0 : ℝ) (a : Fin k → Zd d (sz.L n)) :
    assembledRHSNonAltNg (bandStep2Mat sz E) s v K n k (nqGood1C d k Λg κ') ε Γ Λ Φ D' D'' D_Y τK εq X0 a =
      RBM.Ind.assembledRHSNonAltN sz E s v K n k Λg κ' ε Γ Λ Φ D' D'' D_Y τK εq X0 a := rfl

theorem NQBudgetGen_kapFar_band (sz : Sizes d) (n k : ℕ) (Λg κ' ε : ℝ) :
    NQBudgetGen_kapFar sz n k (nqGood1C d k Λg κ') ε = RBM.Ind.nqBudget_kapFar sz n k Λg κ' ε := rfl

theorem NQBudgetGen_qvFar_band (sz : Sizes d) (n k : ℕ) (Λg κ' ε : ℝ) :
    NQBudgetGen_qvFar sz n k (nqGood1C d k Λg κ') ε = RBM.Ind.nqBudget_qvFar sz n k Λg κ' ε := rfl

end Vocab

/-! ## 2. Elementary facts -/

section Basic

variable {d : ℕ}

/-- `η_v⁻¹ ≤ N` gives `(1-v)⁻¹ ≤ N` (band `nqBudget_inv_one_sub_le`, `NQBudget:125`): `(1-v)⁻¹ = Im m · η_v⁻¹` (`LoopForm`), `Im m ≤ 1` (`‖m‖ ≤ 1`). -/
theorem NQBudgetGen_inv_one_sub_le {sz : Sizes d} {Cm : Step2Mat sz} {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E) {n : ℕ}
    (hm : ‖Cm.m n‖ ≤ 1) {v Nn : ℝ} (hv1 : v < 1) (hη : (Cm.eta n v)⁻¹ ≤ Nn) : (1 - v)⁻¹ ≤ Nn := by
  have hm1 := NQGood1Gen_im_le_one hm
  have hm0 := (hL n).1
  have h1 : 0 < 1 - v := by linarith
  have heq : (1 - v)⁻¹ = (Cm.m n).im * (Cm.eta n v)⁻¹ := by
    rw [NQGood1Gen_eta_eq hL]
    field_simp
  rw [heq]
  have h0 : 0 ≤ (Cm.eta n v)⁻¹ := inv_nonneg.2 (NQGood1Gen_eta_pos hL n hv1).le
  nlinarith

/-- **The far bound of the kernel weight** (band `nqBudget_kappa_le_kapFar`, `NQBudget:163`): for `0 ≤ u_i ≤ u_m < 1` and
`(1-u_m)⁻¹ ≤ N`, `κ_{i,m} = W^{Ck ε} r_{i,m}^{k-1} ≤ W^{Ck ε} ((1+g²) N)^{k-1}` (`r_{i,m} ≤ (1+g²)(1-u_m)⁻¹`), for every real `g = sz.lam n`. -/
theorem NQBudgetGen_kappa_le_kapFar (sz : Sizes d) (n k : ℕ) (Ck ε : ℝ) (u : ℕ → ℝ)
    {i m : ℕ} (hu0 : 0 ≤ u i) (hium : u i ≤ u m) (hm1 : u m < 1)
    (hN : (1 - u m)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) :
    kappaNonAltNg k Ck (sz.lam n) ((sz.W n : ℕ) : ℝ) ε u i m ≤ NQBudgetGen_kapFar sz n k Ck ε := by
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
  have hWC : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  unfold kappaNonAltNg NQBudgetGen_kapFar
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr _) hWC

end Basic

/-! ## 3. Generic term budgets (abstract kernel weights) -/

section Generic

variable {d : ℕ} {sz : Sizes d}

/-- **Generic initial term** (band `tbInitN`, `NQBudget:207`; model-free, so the band theorem is reused): for weights `κ` with
`κ(0,K) B_0^k ≤ C_κ B_K^k` and an initial supremum `X0 ≤ G B_0^k`, `κ(0,K) X0 ≤ C_κ G B_K^k`. -/
theorem tbInitNg {k K : ℕ} {Cκ G X0 : ℝ} (B : ℕ → ℝ) (κ : ℕ → ℕ → ℝ)
    (hκ0 : 0 ≤ κ 0 K) (hG : 0 ≤ G)
    (hker : κ 0 K * B 0 ^ k ≤ Cκ * B K ^ k) (hX0 : X0 ≤ G * B 0 ^ k) :
    κ 0 K * X0 ≤ Cκ * G * B K ^ k :=
  tbInitN B κ hκ0 hG hker hX0

/-- **Generic drift term** (band `tbDriftN`, `NQBudget:221`), with `η_u = Cm.eta n u`: for weights `κ, ε` with
`κ(j+1,K) B_j^k ≤ C_κ B_K^k`, `κ(j+1,K) ≤ C_far`, `ε(j+1,K) ≤ C_ε` and drift levels `d_j ≤ a (B_j^k / η_{u_j}) + b`,
`0 ≤ δ_j ≤ δ_max`: `Δ Σ_{j<K} (κ(j+1,K) d_j + ε(j+1,K) δ_j) ≤
C_κ a B_K^k Σ_j Δ/η_{u_j} + (K Δ)(C_far b + C_ε δ_max)`. -/
theorem tbDriftNg (Cm : Step2Mat sz) (n : ℕ) {k K : ℕ} {Δ Cκ Cε Cfar a b δmax : ℝ} (u B : ℕ → ℝ)
    (κ ε : ℕ → ℕ → ℝ) (dd δ : ℕ → ℝ) (hΔ : 0 ≤ Δ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hκ0 : ∀ j < K, 0 ≤ κ (j + 1) K) (hε0 : ∀ j < K, 0 ≤ ε (j + 1) K)
    (hκM : ∀ j < K, κ (j + 1) K * B j ^ k ≤ Cκ * B K ^ k)
    (hκfar : ∀ j < K, κ (j + 1) K ≤ Cfar) (hεC : ∀ j < K, ε (j + 1) K ≤ Cε)
    (hd : ∀ j < K, dd j ≤ a * (B j ^ k / Cm.eta n (u j)) + b)
    (hδ0 : ∀ j < K, 0 ≤ δ j) (hδ : ∀ j < K, δ j ≤ δmax) (hη : ∀ j < K, 0 < Cm.eta n (u j)) :
    Δ * ∑ j ∈ Finset.range K, (κ (j + 1) K * dd j + ε (j + 1) K * δ j) ≤
      Cκ * a * B K ^ k * ∑ j ∈ Finset.range K, Δ / Cm.eta n (u j) +
        ((K : ℝ) * Δ) * (Cfar * b + Cε * δmax) := by
  have hstep : ∀ j ∈ Finset.range K,
      Δ * (κ (j + 1) K * dd j + ε (j + 1) K * δ j) ≤
        Cκ * a * B K ^ k * (Δ / Cm.eta n (u j)) + Δ * (Cfar * b + Cε * δmax) := by
    intro j hj
    have hjK := Finset.mem_range.1 hj
    have h1 : κ (j + 1) K * dd j ≤ κ (j + 1) K * (a * (B j ^ k / Cm.eta n (u j)) + b) :=
      mul_le_mul_of_nonneg_left (hd j hjK) (hκ0 j hjK)
    have h2 : κ (j + 1) K * (a * (B j ^ k / Cm.eta n (u j)) + b) =
        (a * (Cm.eta n (u j))⁻¹) * (κ (j + 1) K * B j ^ k) + κ (j + 1) K * b := by
      rw [div_eq_mul_inv]; ring
    have h3 : (a * (Cm.eta n (u j))⁻¹) * (κ (j + 1) K * B j ^ k) ≤
        (a * (Cm.eta n (u j))⁻¹) * (Cκ * B K ^ k) :=
      mul_le_mul_of_nonneg_left (hκM j hjK) (mul_nonneg ha (inv_nonneg.2 (hη j hjK).le))
    have h4 : κ (j + 1) K * b ≤ Cfar * b := mul_le_mul_of_nonneg_right (hκfar j hjK) hb
    have h5 : ε (j + 1) K * δ j ≤ Cε * δmax :=
      calc ε (j + 1) K * δ j ≤ ε (j + 1) K * δmax :=
            mul_le_mul_of_nonneg_left (hδ j hjK) (hε0 j hjK)
        _ ≤ Cε * δmax := mul_le_mul_of_nonneg_right (hεC j hjK) ((hδ0 j hjK).trans (hδ j hjK))
    have h6 : κ (j + 1) K * dd j + ε (j + 1) K * δ j ≤
        (a * (Cm.eta n (u j))⁻¹) * (Cκ * B K ^ k) + (Cfar * b + Cε * δmax) := by
      linarith
    have h7 := mul_le_mul_of_nonneg_left h6 hΔ
    have e : Δ * ((a * (Cm.eta n (u j))⁻¹) * (Cκ * B K ^ k) + (Cfar * b + Cε * δmax)) =
        Cκ * a * B K ^ k * (Δ / Cm.eta n (u j)) + Δ * (Cfar * b + Cε * δmax) := by
      rw [div_eq_mul_inv]; ring
    rw [e] at h7
    exact h7
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum hstep).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  ring

/-- **Generic quadratic-variation term** (band `tbQvN`, `NQBudget:269`), with `η_u = Cm.eta n u`: for weights `0 ≤ κ_j ≤ C_far` with
`κ_j B_{j+1}^k ≤ C_κ B_K^k`, `Σ_{j<K} Δ k qvShape ≤ k C_κ² G (B_K^k)² Σ_j Δ/η_{u_{j+1}} +
(K Δ) k ((C_far (C_far + C_e) + C_c) Wd)`. -/
theorem tbQvNg (Cm : Step2Mat sz) (n : ℕ) {k K : ℕ} {Cκ Cfar Ce Cc G Wd Δ : ℝ} (u B κ : ℕ → ℝ)
    (hB0 : ∀ j < K, 0 ≤ B (j + 1)) (hκ0 : ∀ j < K, 0 ≤ κ j)
    (hκM : ∀ j < K, κ j * B (j + 1) ^ k ≤ Cκ * B K ^ k) (hκfar : ∀ j < K, κ j ≤ Cfar)
    (hG : 0 ≤ G) (hWd : 0 ≤ Wd) (hCe : 0 ≤ Ce) (hΔ : 0 ≤ Δ)
    (hη : ∀ j < K, 0 < Cm.eta n (u (j + 1))) :
    ∑ j ∈ Finset.range K, Δ * ((k : ℝ) * nqBudget_qvShape k (κ j) Ce Cc G Wd (B (j + 1))
        (Cm.eta n (u (j + 1)))) ≤
      (k : ℝ) * Cκ ^ 2 * G * (B K ^ k) ^ 2 * ∑ j ∈ Finset.range K, Δ / Cm.eta n (u (j + 1)) +
        ((K : ℝ) * Δ) * ((k : ℝ) * ((Cfar * (Cfar + Ce) + Cc) * Wd)) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hstep : ∀ j ∈ Finset.range K,
      Δ * ((k : ℝ) * nqBudget_qvShape k (κ j) Ce Cc G Wd (B (j + 1)) (Cm.eta n (u (j + 1)))) ≤
        (k : ℝ) * Cκ ^ 2 * G * (B K ^ k) ^ 2 * (Δ / Cm.eta n (u (j + 1))) +
          Δ * ((k : ℝ) * ((Cfar * (Cfar + Ce) + Cc) * Wd)) := by
    intro j hj
    have hjK := Finset.mem_range.1 hj
    have hκj := hκ0 j hjK
    have hη0 := hη j hjK
    have hkB : 0 ≤ κ j * B (j + 1) ^ k := mul_nonneg hκj (pow_nonneg (hB0 j hjK) _)
    have hsq : (κ j * B (j + 1) ^ k) ^ 2 ≤ (Cκ * B K ^ k) ^ 2 :=
      pow_le_pow_left₀ hkB (hκM j hjK) 2
    have hq1 : κ j * κ j * (G * (B (j + 1) ^ (2 * k) / Cm.eta n (u (j + 1)))) ≤
        Cκ ^ 2 * G * (B K ^ k) ^ 2 * (Cm.eta n (u (j + 1)))⁻¹ := by
      have e : κ j * κ j * (G * (B (j + 1) ^ (2 * k) / Cm.eta n (u (j + 1)))) =
          (G * (Cm.eta n (u (j + 1)))⁻¹) * (κ j * B (j + 1) ^ k) ^ 2 := by
        rw [div_eq_mul_inv, pow_mul']; ring
      rw [e]
      calc (G * (Cm.eta n (u (j + 1)))⁻¹) * (κ j * B (j + 1) ^ k) ^ 2
          ≤ (G * (Cm.eta n (u (j + 1)))⁻¹) * (Cκ * B K ^ k) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (mul_nonneg hG (inv_nonneg.2 hη0.le))
        _ = _ := by ring
    have hf1 : κ j * κ j * Wd ≤ Cfar * Cfar * Wd :=
      mul_le_mul_of_nonneg_right (mul_le_mul (hκfar j hjK) (hκfar j hjK) hκj (hκj.trans (hκfar j hjK)))
        hWd
    have hf2 : κ j * Ce * Wd ≤ Cfar * Ce * Wd :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hκfar j hjK) hCe) hWd
    have hshape : nqBudget_qvShape k (κ j) Ce Cc G Wd (B (j + 1)) (Cm.eta n (u (j + 1))) ≤
        Cκ ^ 2 * G * (B K ^ k) ^ 2 * (Cm.eta n (u (j + 1)))⁻¹ + (Cfar * (Cfar + Ce) + Cc) * Wd := by
      unfold nqBudget_qvShape
      nlinarith [hq1, hf1, hf2]
    have h1 := mul_le_mul_of_nonneg_left hshape hk0
    have h2 := mul_le_mul_of_nonneg_left h1 hΔ
    refine h2.trans (le_of_eq ?_)
    rw [div_eq_mul_inv]; ring
  refine (Finset.sum_le_sum hstep).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

end Generic

/-! ## 4. The generic budgets at the non-alternating data, and the budget -/

section Instances

variable {d : ℕ} {sz : Sizes d}

/-- **`qvBdNonAltNg` has the shape `nqBudget_qvShape`** with `κ = W^{Ck ε} r^{k-1}`, `Ce = W^{Ck}`, `Cc = W^{Ck} W^k`, `G = Γ(ΓΛ)`,
`Wd = W^{-D''}`, `B = B_u`, `η = η_u` (band `qvBdNonAltN_eq_qvShape`, `NQBudget:355`). -/
theorem qvBdNonAltNg_eq_qvShape (Cm : Step2Mat sz) (n k : ℕ) (Ck ε Γ Λ D'' u w : ℝ) :
    qvBdNonAltNg Cm n k Ck ε Γ Λ D'' u w =
      nqBudget_qvShape k
        (((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
          ((sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - w|)) ^ (k - 1))
        (((sz.W n : ℕ) : ℝ) ^ Ck)
        (((sz.W n : ℕ) : ℝ) ^ Ck * ((sz.W n : ℕ) : ℝ) ^ k)
        (Γ * (Γ * Λ)) (((sz.W n : ℕ) : ℝ) ^ (-D'')) (sz.Bctl n u) (Cm.eta n u) := by
  unfold qvBdNonAltNg nqBudget_qvShape
  ring

/-- **The initial term at the data** (band `tbInitNonAltN`, `NQBudget:368`): `κ_{0,K} X0 ≤ W^{Ck ε} G B_v^k` for `X0 ≤ G B_{s}^k`
(`kappaNonAltNg_mul_Bctl_pow_le`).  No spectral hypothesis is needed. -/
theorem tbInitNonAltNg (sz : Sizes d) {s v : ℕ → ℝ} {K : ℕ → ℕ} (n k : ℕ) (Ck ε G X0 : ℝ)
    (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1) (hK : K n ≠ 0) (hG : 0 ≤ G)
    (hX0 : X0 ≤ G * (sz.Bctl n (s n)) ^ k) :
    kappaNonAltNg k Ck (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) 0 (K n) * X0 ≤
      ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) * G * (sz.Bctl n (v n)) ^ k := by
  have hW : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  have huK := gridTime_last s v K n hK
  have hu0 := ST_gridTime_zero s v K n
  have hκ0 := nonAlt_hκ0Ng k Ck (sz.lam n) ((sz.W n : ℕ) : ℝ) ε hW (K n) (gridTime s v K n)
    0 (K n) (Nat.zero_le _) le_rfl
  have hker := kappaNonAltNg_mul_Bctl_pow_le sz n k Ck ε hW (gridTime s v K n)
    (i := 0) (m := K n) (by rw [hu0, huK]; exact hsv) (by rw [huK]; exact hv1)
  rw [hu0, huK] at hker
  have h := tbInitNg (k := k) (K := K n) (Cκ := ((sz.W n : ℕ) : ℝ) ^ (Ck * ε))
    (G := G) (X0 := X0) (fun i => sz.Bctl n (gridTime s v K n i))
    (kappaNonAltNg k Ck (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n)) hκ0 hG
    (by simpa only [hu0, huK] using hker) (by simpa only [hu0] using hX0)
  simpa only [huK] using h

/-- **The drift term at the data** (band `tbDriftNonAltN`, `NQBudget:391`): the drift term of `assembledRHSNonAltNg` is at most
`W^{Ck ε} Γ(ΓΦ)((k-1) + kΓΦ) B_v^k Σ_j Δ/η_{u_j} + (KΔ)(W^{Ck} W^{-D'})` (`dDriftNonAltNg = a B_{u_j}^k/η_{u_j}`, `b = 0`; sharp kernel
`kappaNonAltNg_succ_mul_Bctl_pow_le`).  `LoopForm` and `‖Cm.m n‖ ≤ 1` replace `|E n| < 2`. -/
theorem tbDriftNonAltNg {E s v : ℕ → ℝ} {K : ℕ → ℕ} (Cm : Step2Mat sz) (hL : StepDecompGen_LoopForm Cm E) (n k : ℕ) (Ck ε : ℝ)
    (Γ Φ : ℕ → ℝ) (D' : ℝ) (hm : ‖Cm.m n‖ ≤ 1) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1)
    (hK : K n ≠ 0) (hk : 1 ≤ k) (hΓ : 0 ≤ Γ n) (hΦ : 0 ≤ Φ n)
    (hη : (Cm.eta n (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) :
    gridStep s v K n * ∑ j ∈ Finset.range (K n),
      (kappaNonAltNg k Ck (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) (j + 1) (K n) *
          dDriftNonAltNg Cm n (gridTime s v K n j) k (Γ n) (Φ n) +
        epsNonAltNg Ck ((sz.W n : ℕ) : ℝ) (j + 1) (K n) * ((sz.W n : ℕ) : ℝ) ^ (-D')) ≤
      ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
          (Γ n * (Γ n * Φ n) * (((k : ℝ) - 1) + (k : ℝ) * (Γ n * Φ n))) *
          (sz.Bctl n (v n)) ^ k *
          ∑ j ∈ Finset.range (K n), gridStep s v K n / Cm.eta n (gridTime s v K n j) +
        ((K n : ℝ) * gridStep s v K n) *
          (((sz.W n : ℕ) : ℝ) ^ Ck * ((sz.W n : ℕ) : ℝ) ^ (-D')) := by
  have hW : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hu0 : ∀ i, 0 ≤ gridTime s v K n i := fun i => nqBudget_gridTime_nonneg hs0 hsv i
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi =>
    (nqBudget_gridTime_le hsv hK hi).trans_lt hv1
  have huK := gridTime_last s v K n hK
  have hmono : ∀ i m, i ≤ m → gridTime s v K n i ≤ gridTime s v K n m := fun i m him =>
    ST_gridTime_mono s v K n hsv him
  have hΔ0 : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n hsv
  have hN1 : (1 - v n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := NQBudgetGen_inv_one_sub_le hL hm hv1 hη
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ha0 : 0 ≤ Γ n * (Γ n * Φ n) * (((k : ℝ) - 1) + (k : ℝ) * (Γ n * Φ n)) := by
    have h1 : 0 ≤ ((k : ℝ) - 1) + (k : ℝ) * (Γ n * Φ n) := by
      have : 0 ≤ (k : ℝ) * (Γ n * Φ n) := mul_nonneg (by linarith) (mul_nonneg hΓ hΦ)
      linarith
    exact mul_nonneg (mul_nonneg hΓ (mul_nonneg hΓ hΦ)) h1
  have hsucc : ∀ j < K n, kappaNonAltNg k Ck (sz.lam n) ((sz.W n : ℕ) : ℝ) ε
      (gridTime s v K n) (j + 1) (K n) * (sz.Bctl n (gridTime s v K n j)) ^ k ≤
      ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
        (sz.Bctl n (gridTime s v K n (K n))) ^ k := fun j hj =>
    kappaNonAltNg_succ_mul_Bctl_pow_le sz n k Ck ε hW (gridTime s v K n) j (K n)
      (hmono j (j + 1) (by omega)) (hmono (j + 1) (K n) (by omega)) (hu1 _ le_rfl)
  have h := tbDriftNg Cm n (k := k) (K := K n) (Δ := gridStep s v K n)
    (Cκ := ((sz.W n : ℕ) : ℝ) ^ (Ck * ε))
    (Cε := ((sz.W n : ℕ) : ℝ) ^ Ck)
    (Cfar := NQBudgetGen_kapFar sz n k Ck ε)
    (a := Γ n * (Γ n * Φ n) * (((k : ℝ) - 1) + (k : ℝ) * (Γ n * Φ n))) (b := 0)
    (δmax := ((sz.W n : ℕ) : ℝ) ^ (-D')) (gridTime s v K n)
    (fun i => sz.Bctl n (gridTime s v K n i))
    (kappaNonAltNg k Ck (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n))
    (epsNonAltNg Ck ((sz.W n : ℕ) : ℝ))
    (fun j => dDriftNonAltNg Cm n (gridTime s v K n j) k (Γ n) (Φ n))
    (fun _ => ((sz.W n : ℕ) : ℝ) ^ (-D')) hΔ0 ha0 le_rfl
    (fun j hj => nonAlt_hκ0Ng k Ck (sz.lam n) ((sz.W n : ℕ) : ℝ) ε hW (K n) _ (j + 1) (K n)
      (by omega) le_rfl)
    (fun j hj => nonAlt_hε0Ng Ck ((sz.W n : ℕ) : ℝ) hW (K n) (j + 1) (K n) (by omega) le_rfl)
    hsucc
    (fun j hj => NQBudgetGen_kappa_le_kapFar sz n k Ck ε (gridTime s v K n) (hu0 (j + 1))
      (hmono (j + 1) (K n) (by omega)) (hu1 _ le_rfl) (by rw [huK]; exact hN1))
    (fun _ _ => le_rfl)
    (fun j hj => by
      unfold dDriftNonAltNg
      rw [add_zero]
      apply le_of_eq
      rw [div_eq_mul_inv]; ring)
    (fun _ _ => Real.rpow_nonneg hW _) (fun _ _ => le_rfl)
    (fun j hj => NQGood1Gen_eta_pos hL n (hu1 j hj.le))
  rw [huK] at h
  simpa only [mul_zero, zero_add] using h

/-- **The quadratic-variation term at the data** (band `tbQvNonAltN`, `NQBudget:458`): the sum of the sub-Gaussian proxies `cQVNonAltNg`
at the target `u_K = v` is at most `k (W^{Ck ε})² Γ(ΓΛ) (B_v^k)² Σ_j Δ/η_{u_{j+1}} + (KΔ) k (NQBudgetGen_qvFar W^{-D''})`
(`toNNReal` removed by `qvBdNonAltNg_pos`). -/
theorem tbQvNonAltNg {E s v : ℕ → ℝ} {K : ℕ → ℕ} (Cm : Step2Mat sz) (hL : StepDecompGen_LoopForm Cm E) (n k : ℕ) (Ck ε : ℝ)
    (Γ Λ : ℕ → ℝ) (D'' : ℝ) (a : Fin k → Zd d (sz.L n)) (hm : ‖Cm.m n‖ ≤ 1) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n)
    (hv1 : v n < 1) (hK : K n ≠ 0) (hΛ : 0 ≤ Λ n)
    (hη : (Cm.eta n (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) :
    ∑ j ∈ Finset.range (K n), (cQVNonAltNg Cm s v K n k Ck ε Γ Λ D'' (K n) a j : ℝ) ≤
      (k : ℝ) * (((sz.W n : ℕ) : ℝ) ^ (Ck * ε)) ^ 2 * (Γ n * (Γ n * Λ n)) *
          ((sz.Bctl n (v n)) ^ k) ^ 2 *
          ∑ j ∈ Finset.range (K n),
            gridStep s v K n / Cm.eta n (gridTime s v K n (j + 1)) +
        ((K n : ℝ) * gridStep s v K n) *
          ((k : ℝ) * (NQBudgetGen_qvFar sz n k Ck ε * ((sz.W n : ℕ) : ℝ) ^ (-D''))) := by
  have hW : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hu0 : ∀ i, 0 ≤ gridTime s v K n i := fun i => nqBudget_gridTime_nonneg hs0 hsv i
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi =>
    (nqBudget_gridTime_le hsv hK hi).trans_lt hv1
  have huK := gridTime_last s v K n hK
  have hmono : ∀ i m, i ≤ m → gridTime s v K n i ≤ gridTime s v K n m := fun i m him =>
    ST_gridTime_mono s v K n hsv him
  have hΔ0 : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n hsv
  have hN1 : (1 - v n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := NQBudgetGen_inv_one_sub_le hL hm hv1 hη
  have hWd : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'') := Real.rpow_nonneg hW _
  have hWC : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ Ck := Real.rpow_nonneg hW _
  have hG : 0 ≤ Γ n * (Γ n * Λ n) := by
    have : Γ n * (Γ n * Λ n) = Γ n ^ 2 * Λ n := by ring
    rw [this]; positivity
  have hcoe : ∀ j ∈ Finset.range (K n),
      (cQVNonAltNg Cm s v K n k Ck ε Γ Λ D'' (K n) a j : ℝ) =
        gridStep s v K n * ((k : ℝ) * nqBudget_qvShape k
          (kappaNonAltNg k Ck (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) (j + 1) (K n))
          (((sz.W n : ℕ) : ℝ) ^ Ck)
          (((sz.W n : ℕ) : ℝ) ^ Ck * ((sz.W n : ℕ) : ℝ) ^ k)
          (Γ n * (Γ n * Λ n)) (((sz.W n : ℕ) : ℝ) ^ (-D''))
          (sz.Bctl n (gridTime s v K n (j + 1))) (Cm.eta n (gridTime s v K n (j + 1)))) := by
    intro j hj
    have hjK := Finset.mem_range.1 hj
    have hpos := qvBdNonAltNg_pos Cm hL n (k := k) (Ck := Ck) (ε := ε)
      (Γ := Γ n) (D'' := D'') (w := gridTime s v K n (K n)) hΛ
      (hu1 (j + 1) (by omega)).le
    unfold cQVNonAltNg
    rw [Real.coe_toNNReal _ (by positivity), qvBdNonAltNg_eq_qvShape]
    rfl
  rw [Finset.sum_congr rfl hcoe]
  have h := tbQvNg Cm n (k := k) (K := K n) (Cκ := ((sz.W n : ℕ) : ℝ) ^ (Ck * ε))
    (Cfar := NQBudgetGen_kapFar sz n k Ck ε) (Ce := ((sz.W n : ℕ) : ℝ) ^ Ck)
    (Cc := ((sz.W n : ℕ) : ℝ) ^ Ck * ((sz.W n : ℕ) : ℝ) ^ k)
    (G := Γ n * (Γ n * Λ n)) (Wd := ((sz.W n : ℕ) : ℝ) ^ (-D'')) (Δ := gridStep s v K n)
    (gridTime s v K n) (fun i => sz.Bctl n (gridTime s v K n i))
    (fun j => kappaNonAltNg k Ck (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) (j + 1) (K n))
    (fun j hj => (Sizes.STBctl_pos sz n (hu1 (j + 1) (by omega))).le)
    (fun j hj => nonAlt_hκ0Ng k Ck (sz.lam n) ((sz.W n : ℕ) : ℝ) ε hW (K n) _ (j + 1) (K n)
      (by omega) le_rfl)
    (fun j hj => kappaNonAltNg_mul_Bctl_pow_le sz n k Ck ε hW (gridTime s v K n)
      (hmono (j + 1) (K n) (by omega)) (hu1 _ le_rfl))
    (fun j hj => NQBudgetGen_kappa_le_kapFar sz n k Ck ε (gridTime s v K n) (hu0 (j + 1))
      (hmono (j + 1) (K n) (by omega)) (hu1 _ le_rfl) (by rw [huK]; exact hN1))
    hG hWd hWC hΔ0 (fun j hj => NQGood1Gen_eta_pos hL n (hu1 (j + 1) (by omega)))
  rw [huK] at h
  exact h

end Instances

/-! ## 4b. The budget `budgetNonAltNg` -/

section Budget

variable {d : ℕ} {sz : Sizes d}

/-- **The (5.93) budget of the non-alternating endpoint over a carrier** (band `budgetNonAltN`, `NQBudget:555`): at a fixed `n`, under explicit
numerical inequalities only, `assembledRHSNonAltNg ≤ N^{ε₀} (Λ^{1/2} + Φ + Φ²) B_v^k`.  The `Φ²` is the `k Γ³ Φ²` part of
`dDriftNonAltNg` (clause (D2) of `GoodSetNg`).

* regime: `hk` (`2 ≤ k`), `hε₁`, `hL`, `hm` (`LoopForm` and `‖Cm.m n‖ ≤ 1`, in place of `|E n| < 2`), `hs0`, `hsv`, `hv1`, `hK`, `hη`
  (`η_v⁻¹ ≤ N`), `hΔη` (`Δ η_v⁻¹ ≤ 1`);
* levels: `hΓ` (`Γ_n = N^{ε₁}`), `hΛ` (`1 ≤ Λ_n`), `hΦ` (`0 ≤ Φ_n`);
* merged inputs, per index `n`: `hlog` (the conclusion of `sum_gridStep_div_etaNg_le`), `hX0` (the initial datum), `hR` (the conclusion of
  `sum_weighted_stepErrNg_le` at `m = K n`; see `nqBudget_merged_inputsg`);
* absorption: `ha1`-`ha3` (the three main terms, against `N^{ε₀}/6, /12, /12`) and `he1`-`he4` (the four far parts, against
  `N^{ε₀}/12, /12, /6, /6`); the far parts carry `W^{Ck}`, so `D', D''` are chosen after `Ck`. -/
theorem budgetNonAltNg {E : ℕ → ℝ} (Cm : Step2Mat sz) (hL : StepDecompGen_LoopForm Cm E) (s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (Ck ε : ℝ) (Γ Λ Φ : ℕ → ℝ) (D' D'' D_Y D_t τK εq ε₀ ε₁ X0 : ℝ)
    (a : Fin k → Zd d (sz.L n))
    (hk : 2 ≤ k) (hε₁ : 0 ≤ ε₁) (hm : ‖Cm.m n‖ ≤ 1) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n)
    (hv1 : v n < 1) (hK : K n ≠ 0)
    (hη : (Cm.eta n (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ))
    (hΔη : gridStep s v K n * (Cm.eta n (v n))⁻¹ ≤ 1)
    (hΓ : Γ n = ((sz.size n : ℕ) : ℝ) ^ ε₁) (hΛ : 1 ≤ Λ n) (hΦ : 0 ≤ Φ n)
    (hlog : ∑ j ∈ Finset.range (K n), gridStep s v K n / Cm.eta n (gridTime s v K n j) ≤
      (Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ))
    (hX0 : X0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ k)
    (hR : ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k *
        stepErrNg Cm.toFlowFM n k (gridTime s v K n j) (gridTime s v K n (j + 1))
          (gridStep s v K n)
          (((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (gridTime s v K n (j + 1)))⁻¹ ^ k) ≤
      ((sz.size n : ℕ) : ℝ) ^ (-D_t))
    (ha1 : ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) * ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6)
    (ha2 : (k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
        (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 3 *
        ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12)
    (ha3 : ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
        ((sz.size n : ℕ) : ℝ) ^ ε₁ *
        Real.sqrt ((k : ℝ) * ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1))) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12)
    (he1 : ((sz.size n : ℕ) : ℝ) ^ k *
        (((sz.W n : ℕ) : ℝ) ^ Ck * ((sz.W n : ℕ) : ℝ) ^ (-D')) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12)
    (he2 : ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.size n : ℕ) : ℝ) ^ k *
        Real.sqrt ((k : ℝ) * (NQBudgetGen_qvFar sz n k Ck ε * ((sz.W n : ℕ) : ℝ) ^ (-D'')))) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12)
    (he3 : ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-D_Y) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6)
    (he4 : ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-D_t) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6) :
    assembledRHSNonAltNg Cm s v K n k Ck ε Γ Λ Φ D' D'' D_Y τK εq X0 a ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φ n + Φ n ^ 2) *
        (sz.Bctl n (v n)) ^ k := by
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
    have h : 1 ≤ (sz.W n * sz.L n) ^ d :=
      Nat.one_le_pow _ _ (Nat.mul_pos (sz.W_pos n) (by have := sz.three_le_L n; omega))
    exact_mod_cast (show 1 ≤ sz.size n from h)
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hNk : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) ^ k := pow_pos hN0 k
  have hW0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hu0 : ∀ i, 0 ≤ gridTime s v K n i := fun i => nqBudget_gridTime_nonneg hs0 hsv i
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi =>
    (nqBudget_gridTime_le hsv hK hi).trans_lt hv1
  have huK := gridTime_last s v K n hK
  have hΔ0 : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n hsv
  have hKΔ1 : (K n : ℝ) * gridStep s v K n ≤ 1 := by
    rw [nqBudget_K_mul_step hK]; linarith
  have hΓ0 : 0 ≤ Γ n := by rw [hΓ]; exact Real.rpow_nonneg hN0.le _
  have hΓ1 : 1 ≤ Γ n := by rw [hΓ]; exact Real.one_le_rpow hN1 hε₁
  have hΛ0 : 0 ≤ Λ n := by linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hBv0 := Sizes.STBctl_pos sz n hv1
  have hX0' : 0 ≤ (sz.Bctl n (v n)) ^ k := pow_nonneg hBv0.le _
  have hXN : (((sz.size n : ℕ) : ℝ) ^ k)⁻¹ ≤ (sz.Bctl n (v n)) ^ k := by
    rw [← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 hN0.le)
      (RBM.Ind.ContinuityNet.cont_inv_size_le_Bctl sz n (hs0.trans hsv) hv1) k
  have hP0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ := Real.rpow_nonneg hN0.le _
  have hLs0 : 0 ≤ (Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) :=
    mul_nonneg (inv_nonneg.2 (hL n).1.le) (Real.log_nonneg hN1)
  have hWC0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ Ck := Real.rpow_nonneg hW0 _
  have hWD0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D') := Real.rpow_nonneg hW0 _
  have hWCε0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) :=
    Real.rpow_nonneg hW0 _
  have hΛr1 : 1 ≤ Λ n ^ ((1 : ℝ) / 2) := Real.one_le_rpow hΛ (by norm_num)
  -- the far part `W^C W^{-D'}` is absorbed once (`he1`)
  have hfar : ((sz.W n : ℕ) : ℝ) ^ Ck * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ k :=
    nqBudget_absorb hNk (by positivity) ((mul_comm _ _).trans_le he1) hXN
  -- T1: the initial term
  have T1 : _ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 * (sz.Bctl n (v n)) ^ k :=
    (tbInitNonAltNg sz n k Ck ε (((sz.size n : ℕ) : ℝ) ^ ε₁) X0 hs0 hsv hv1 hK
      (Real.rpow_nonneg hN0.le _) hX0).trans (mul_le_mul_of_nonneg_right ha1 hX0')
  -- T2: the initial decay error
  have T2 : epsNonAltNg Ck ((sz.W n : ℕ) : ℝ) 0 (K n) * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ k := by
    unfold epsNonAltNg
    exact hfar
  -- T3: the drift term
  have T3 : gridStep s v K n * ∑ j ∈ Finset.range (K n),
      (kappaNonAltNg k Ck (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) (j + 1) (K n) *
          dDriftNonAltNg Cm n (gridTime s v K n j) k (Γ n) (Φ n) +
        epsNonAltNg Ck ((sz.W n : ℕ) : ℝ) (j + 1) (K n) * ((sz.W n : ℕ) : ℝ) ^ (-D')) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * ((Φ n + Φ n ^ 2) * (sz.Bctl n (v n)) ^ k) +
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ k := by
    have h := tbDriftNonAltNg Cm hL n k Ck ε Γ Φ D' hm hs0 hsv hv1 hK (by omega) hΓ0 hΦ hη
    refine h.trans ?_
    have ha0 : 0 ≤ Γ n * (Γ n * Φ n) * (((k : ℝ) - 1) + (k : ℝ) * (Γ n * Φ n)) := by
      have h1 : 0 ≤ ((k : ℝ) - 1) + (k : ℝ) * (Γ n * Φ n) := by
        have : 0 ≤ (k : ℝ) * (Γ n * Φ n) := mul_nonneg (by linarith) (mul_nonneg hΓ0 hΦ)
        linarith
      exact mul_nonneg (mul_nonneg hΓ0 (mul_nonneg hΓ0 hΦ)) h1
    have ha_le : Γ n * (Γ n * Φ n) * (((k : ℝ) - 1) + (k : ℝ) * (Γ n * Φ n)) ≤
        (k : ℝ) * Γ n ^ 3 * (Φ n + Φ n ^ 2) := by
      have h0 : 0 ≤ Φ n * Γ n ^ 2 * ((k : ℝ) * Γ n - ((k : ℝ) - 1)) := by
        refine mul_nonneg (by positivity) ?_
        nlinarith
      have e : (k : ℝ) * Γ n ^ 3 * (Φ n + Φ n ^ 2) -
          Γ n * (Γ n * Φ n) * (((k : ℝ) - 1) + (k : ℝ) * (Γ n * Φ n)) =
          Φ n * Γ n ^ 2 * ((k : ℝ) * Γ n - ((k : ℝ) - 1)) := by ring
      linarith
    have m1 : ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
          (Γ n * (Γ n * Φ n) * (((k : ℝ) - 1) + (k : ℝ) * (Γ n * Φ n))) *
          (sz.Bctl n (v n)) ^ k *
          ∑ j ∈ Finset.range (K n), gridStep s v K n / Cm.eta n (gridTime s v K n j) ≤
        ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
          (Γ n * (Γ n * Φ n) * (((k : ℝ) - 1) + (k : ℝ) * (Γ n * Φ n))) *
          (sz.Bctl n (v n)) ^ k *
          ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (mul_nonneg (mul_nonneg hWCε0 ha0) hX0')
    have m2 : ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
          (Γ n * (Γ n * Φ n) * (((k : ℝ) - 1) + (k : ℝ) * (Γ n * Φ n))) *
          (sz.Bctl n (v n)) ^ k *
          ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) ≤
        ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
          ((k : ℝ) * Γ n ^ 3 * (Φ n + Φ n ^ 2)) *
          (sz.Bctl n (v n)) ^ k *
          ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha_le hWCε0) hX0') hLs0
    have m3 : ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
          ((k : ℝ) * Γ n ^ 3 * (Φ n + Φ n ^ 2)) *
          (sz.Bctl n (v n)) ^ k *
          ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) =
        ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
          (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 3 *
          ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ))) *
          ((Φ n + Φ n ^ 2) * (sz.Bctl n (v n)) ^ k) := by
      rw [hΓ]; ring
    have m4 : ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
          (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 3 *
          ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ))) *
          ((Φ n + Φ n ^ 2) * (sz.Bctl n (v n)) ^ k) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * ((Φ n + Φ n ^ 2) * (sz.Bctl n (v n)) ^ k) :=
      mul_le_mul_of_nonneg_right ha2 (mul_nonneg (by positivity) hX0')
    have f1 : ((K n : ℝ) * gridStep s v K n) *
          (((sz.W n : ℕ) : ℝ) ^ Ck * ((sz.W n : ℕ) : ℝ) ^ (-D')) ≤
        ((sz.W n : ℕ) : ℝ) ^ Ck * ((sz.W n : ℕ) : ℝ) ^ (-D') :=
      (mul_le_mul_of_nonneg_right hKΔ1 (mul_nonneg hWC0 hWD0)).trans_eq (one_mul _)
    exact add_le_add (m1.trans (m2.trans (m3.le.trans m4))) (f1.trans hfar)
  -- T4: the quadratic-variation term
  have T4 : ((sz.size n : ℕ) : ℝ) ^ εq * Real.sqrt (∑ j ∈ Finset.range (K n),
      (cQVNonAltNg Cm s v K n k Ck ε Γ Λ D'' (K n) a j : ℝ)) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (Λ n ^ ((1 : ℝ) / 2) * (sz.Bctl n (v n)) ^ k) +
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ k := by
    have h := tbQvNonAltNg Cm hL n k Ck ε Γ Λ D'' a hm hs0 hsv hv1 hK hΛ0 hη
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
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hQe0 : 0 ≤ (k : ℝ) * (NQBudgetGen_qvFar sz n k Ck ε * ((sz.W n : ℕ) : ℝ) ^ (-D'')) := by
      have hq : 0 ≤ NQBudgetGen_qvFar sz n k Ck ε := by
        unfold NQBudgetGen_qvFar NQBudgetGen_kapFar
        have hr : 0 ≤ (1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ) := by positivity
        have h1 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
            ((1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ)) ^ (k - 1) := by positivity
        have h2 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ k := by positivity
        have h3 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ Ck := hWC0
        positivity
      positivity
    have hΓX : 0 ≤ Γ n * (sz.Bctl n (v n)) ^ k := mul_nonneg hΓ0 hX0'
    have hZ0 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
        (Γ n * (sz.Bctl n (v n)) ^ k)) ^ 2 * ((k : ℝ) * (
        (Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) * Λ n) := by
      have : 0 ≤ (Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1 := by linarith
      positivity
    have hsum : ∑ j ∈ Finset.range (K n),
        (cQVNonAltNg Cm s v K n k Ck ε Γ Λ D'' (K n) a j : ℝ) ≤
        (((sz.W n : ℕ) : ℝ) ^ (Ck * ε) * (Γ n * (sz.Bctl n (v n)) ^ k)) ^ 2 *
          ((k : ℝ) * ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) * Λ n) +
        (k : ℝ) * (NQBudgetGen_qvFar sz n k Ck ε * ((sz.W n : ℕ) : ℝ) ^ (-D'')) := by
      refine h.trans ?_
      have hc0 : 0 ≤ (k : ℝ) * (((sz.W n : ℕ) : ℝ) ^ (Ck * ε)) ^ 2 *
          (Γ n * (Γ n * Λ n)) * ((sz.Bctl n (v n)) ^ k) ^ 2 := by
        have : Γ n * (Γ n * Λ n) = Γ n ^ 2 * Λ n := by ring
        rw [this]; positivity
      have n1 := mul_le_mul_of_nonneg_left hSv hc0
      have n2 : ((K n : ℝ) * gridStep s v K n) *
          ((k : ℝ) * (NQBudgetGen_qvFar sz n k Ck ε * ((sz.W n : ℕ) : ℝ) ^ (-D''))) ≤
          (k : ℝ) * (NQBudgetGen_qvFar sz n k Ck ε * ((sz.W n : ℕ) : ℝ) ^ (-D'')) :=
        (mul_le_mul_of_nonneg_right hKΔ1 hQe0).trans_eq (one_mul _)
      have e : (k : ℝ) * (((sz.W n : ℕ) : ℝ) ^ (Ck * ε)) ^ 2 *
            (Γ n * (Γ n * Λ n)) * ((sz.Bctl n (v n)) ^ k) ^ 2 *
            ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) =
          (((sz.W n : ℕ) : ℝ) ^ (Ck * ε) * (Γ n * (sz.Bctl n (v n)) ^ k)) ^ 2 *
            ((k : ℝ) * ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) * Λ n) := by ring
      linarith
    have hs1 := Real.sqrt_le_sqrt hsum
    have hs2 : Real.sqrt ((((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
          (Γ n * (sz.Bctl n (v n)) ^ k)) ^ 2 *
          ((k : ℝ) * ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) * Λ n) +
        (k : ℝ) * (NQBudgetGen_qvFar sz n k Ck ε * ((sz.W n : ℕ) : ℝ) ^ (-D''))) ≤
        ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) * (Γ n * (sz.Bctl n (v n)) ^ k) *
          (Real.sqrt ((k : ℝ) * ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)) *
            Real.sqrt (Λ n)) +
        Real.sqrt ((k : ℝ) * (NQBudgetGen_qvFar sz n k Ck ε * ((sz.W n : ℕ) : ℝ) ^ (-D''))) := by
      refine (nqBudget_sqrt_add_le hZ0 hQe0).trans ?_
      have hA0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
          (Γ n * (sz.Bctl n (v n)) ^ k) := mul_nonneg hWCε0 hΓX
      have hP00 : 0 ≤ (k : ℝ) * ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) :=
        mul_nonneg hk0 (by linarith)
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hA0, Real.sqrt_mul hP00]
    have hsΛ : Real.sqrt (Λ n) = Λ n ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow (Λ n)
    have hNe : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ εq := Real.rpow_nonneg hN0.le _
    have k1 : ((sz.size n : ℕ) : ℝ) ^ εq *
        (((sz.W n : ℕ) : ℝ) ^ (Ck * ε) * (Γ n * (sz.Bctl n (v n)) ^ k) *
          (Real.sqrt ((k : ℝ) * ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)) *
            Real.sqrt (Λ n))) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (Λ n ^ ((1 : ℝ) / 2) * (sz.Bctl n (v n)) ^ k) := by
      have e : ((sz.size n : ℕ) : ℝ) ^ εq *
          (((sz.W n : ℕ) : ℝ) ^ (Ck * ε) * (Γ n * (sz.Bctl n (v n)) ^ k) *
            (Real.sqrt ((k : ℝ) * ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)) *
              Real.sqrt (Λ n))) =
          (((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
            ((sz.size n : ℕ) : ℝ) ^ ε₁ *
            Real.sqrt ((k : ℝ) * ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)))) *
          (Λ n ^ ((1 : ℝ) / 2) * (sz.Bctl n (v n)) ^ k) := by
        rw [hsΛ, hΓ]; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right ha3 (mul_nonneg (by linarith) hX0')
    have k2 : ((sz.size n : ℕ) : ℝ) ^ εq *
        Real.sqrt ((k : ℝ) * (NQBudgetGen_qvFar sz n k Ck ε * ((sz.W n : ℕ) : ℝ) ^ (-D''))) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ k := by
      refine nqBudget_absorb hNk (by positivity) ?_ hXN
      have e : ((sz.size n : ℕ) : ℝ) ^ εq *
          Real.sqrt ((k : ℝ) * (NQBudgetGen_qvFar sz n k Ck ε * ((sz.W n : ℕ) : ℝ) ^ (-D''))) *
            ((sz.size n : ℕ) : ℝ) ^ k =
          ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.size n : ℕ) : ℝ) ^ k *
            Real.sqrt ((k : ℝ) * (NQBudgetGen_qvFar sz n k Ck ε *
              ((sz.W n : ℕ) : ℝ) ^ (-D'')))) := by ring
      rw [e]; exact he2
    calc ((sz.size n : ℕ) : ℝ) ^ εq * Real.sqrt (∑ j ∈ Finset.range (K n),
          (cQVNonAltNg Cm s v K n k Ck ε Γ Λ D'' (K n) a j : ℝ))
        ≤ ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
            (Γ n * (sz.Bctl n (v n)) ^ k) *
            (Real.sqrt ((k : ℝ) * ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)) *
              Real.sqrt (Λ n)) +
          Real.sqrt ((k : ℝ) * (NQBudgetGen_qvFar sz n k Ck ε * ((sz.W n : ℕ) : ℝ) ^ (-D'')))) :=
          mul_le_mul_of_nonneg_left (hs1.trans hs2) hNe
      _ = ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
            (Γ n * (sz.Bctl n (v n)) ^ k) *
            (Real.sqrt ((k : ℝ) * ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)) *
              Real.sqrt (Λ n))) +
          ((sz.size n : ℕ) : ℝ) ^ εq *
            Real.sqrt ((k : ℝ) * (NQBudgetGen_qvFar sz n k Ck ε *
              ((sz.W n : ℕ) : ℝ) ^ (-D''))) := by ring
      _ ≤ _ := add_le_add k1 k2
  -- T5, T6
  have T5 : ((sz.size n : ℕ) : ℝ) ^ (-D_Y) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 * (sz.Bctl n (v n)) ^ k :=
    nqBudget_absorb hNk (by positivity) ((mul_comm _ _).trans_le he3) hXN
  have T6 : _ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 * (sz.Bctl n (v n)) ^ k :=
    hR.trans (nqBudget_absorb hNk (by positivity) ((mul_comm _ _).trans_le he4) hXN)
  unfold assembledRHSNonAltNg
  exact nqBudget_final hP0 hX0' hΛr1 hΦ T1 T2 T3 T4 T5 T6

end Budget

/-! ## 5. The merged inputs `hlog`, `hR` are the conclusions of merged theorems

`hlog` and `hR` of `budgetNonAltNg` are, at each `n`, exactly the conclusions of the merged `sum_gridStep_div_etaNg_le` and
`sum_weighted_stepErrNg_le` (at `m = K n`): the theorem below is the compiled interface for the consumers (the side conditions are those
of the two merged theorems; the spectral data are `DecayGen_Spec` and the inline `∀ n, (Cm.m n).im ≤ 1`). -/

section MergedInputs

variable {d : ℕ} {sz : Sizes d}

/-- **`nqBudget_merged_inputsg`** (band `nqBudget_merged_inputs`, `NQBudget:834`): `hlog`, `hR` of `budgetNonAltNg` hold eventually. -/
theorem nqBudget_merged_inputsg (Cm : Step2Mat sz) {κm τ' τK C_K D_t : ℝ} {s v : ℕ → ℝ} {K : ℕ → ℕ} (k : ℕ)
    (hspec : DecayGen_Spec Cm.toFlowFM κm) (him1 : ∀ n, (Cm.m n).im ≤ 1) (hτ' : 0 < τ') (hτ'1 : τ' ≤ 1) (hτK : 0 < τK)
    (hDt : 0 ≤ D_t) (hk : 2 ≤ k) (hsize : sz.SizeTendsto) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1)
    (hK0 : ∀ n, K n ≠ 0) (hrange : sz.RangeCond τ' v)
    (h1 : 8 + (4 * (k : ℝ) + 8) * (1 - τ') + 2 * D_t < C_K)
    (h2 : 3 + 4 * τK + 5 * (k : ℝ) * (1 - τ') + D_t < C_K)
    (h3 : 2 * (1 - τ') + τK + 2 * (k : ℝ) * (1 - τ') + D_t < C_K) (h4 : 1 - τ' < C_K)
    (hKN : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      (∑ j ∈ Finset.range (K n), gridStep s v K n / Cm.eta n (gridTime s v K n j) ≤
        (Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) ∧
      (∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k *
          stepErrNg Cm.toFlowFM n k (gridTime s v K n j) (gridTime s v K n (j + 1))
            (gridStep s v K n)
            (((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (gridTime s v K n (j + 1)))⁻¹ ^ k) ≤
        ((sz.size n : ℕ) : ℝ) ^ (-D_t)) := by
  filter_upwards [sum_gridStep_div_etaNg_le Cm hspec hτ' hs0 hsv hv1 hK0 hrange,
    sum_weighted_stepErrNg_le d sz Cm k hspec him1 hτ' hτ'1 hτK hDt hk hsize hs0 hsv hv1 hK0 hrange h1 h2 h3 h4 hKN] with n hn1 hn2
  exact ⟨hn1, hn2 (K n) le_rfl⟩

end MergedInputs

/-! ## 6. Compiled nonempty instances (`d = 3`, band carrier `bandStep2Mat sz0 Einst`, `n = 0`)

Data of the band instances `NQBudgetInst` (public facts by name, private ones by `open private`): `sz0` (`n = 0`: `L = 4`, `W = 32`,
`N = 2^21`, `lam = 1/64`), `E ≡ 1/2` (`Im m = √15/4 ≈ 0.968`), `s ≡ 0`, `v ≡ 1/32`, `K ≡ 4` (`Δ = 1/128`, `u_j = j/128`), `k = 3`,
`ε = 4/5`, levels `(Γ, Λ, Φ) = (4, 3, 1)`, `D' = 6`, `D'' = 5`, label `aFar`.  The constant `Ck = nqGood1C 3 3 10 (1/2)` stays abstract
(only `Ck > 0` is known), so every instance holds for the actual `Ck`; the exponent `ε₀ = Ck + 12` of the budget is chosen so that all
seven absorption inequalities hold for every `Ck > 0`.  The carrier facts `LoopForm` and `‖Cm.m 0‖ ≤ 1` are the band lemmas;
`hlog` and `hR` of the budget are the band's explicit bounds at the data (`hlog_instance`, `hR_instance`, which are the same statements at the
band carrier), so nothing is left open. -/

section Inst

open private W0 lam0 N0 im_ge u_le u_nonneg u_lt_one u_mono eta_inv_le_N eta_inv_le_v Bseq Bseq_pos Bseq_mono
  Kg0 u4 step0 N_eps1 ha1_inst ha2_inst ha3_inst he1_inst he2_inst he3_inst he4_inst Cpos
  from RBM3D.Induction.NQBudget

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.GridGoodNInst RBM.Ind.AzumaProxyNInst RBM.Ind.NQGood1Inst
  RBM.Ind.NQGood2Inst RBM.Ind.NQBudgetInst

private abbrev NQBudgetGen_Cm0 : Step2Mat sz0 := bandStep2Mat sz0 Einst

private abbrev NQBudgetGen_C : ℝ := nqGood1C 3 3 10 (1 / 2)

private theorem NQBudgetGen_hL0 : StepDecompGen_LoopForm NQBudgetGen_Cm0 Einst := stepDecompGen_loopForm_band sz0 Einst Einst_abs_lt

private theorem NQBudgetGen_hm0 : ‖NQBudgetGen_Cm0.m 0‖ ≤ 1 := (norm_mE (by norm_num [abs_of_pos])).le

private theorem NQBudgetGen_eta_pos (j : ℕ) (hj : j ≤ 4) : 0 < NQBudgetGen_Cm0.eta 0 (gridTime sInst vg Kg 0 j) :=
  NQGood1Gen_eta_pos NQBudgetGen_hL0 0 (u_lt_one j hj)

/-! ### The vocabulary, the elementary facts -/

/-- Band bridges of the vocabulary at the data (`Ck = nqGood1C 3 3 10 (1/2)`, `E ≡ 1/2`). -/
example : assembledRHSNonAltNg NQBudgetGen_Cm0 sInst vg Kg 0 3 NQBudgetGen_C (4 / 5) Γ4 Λ3 Φ1 6 5 1 (1 / 21) 1
      (4 * (sz0.Bctl 0 (sInst 0)) ^ 3) aFar =
    RBM.Ind.assembledRHSNonAltN sz0 Einst sInst vg Kg 0 3 10 (1 / 2) (4 / 5) Γ4 Λ3 Φ1 6 5 1 (1 / 21) 1
      (4 * (sz0.Bctl 0 (sInst 0)) ^ 3) aFar ∧
    NQBudgetGen_kapFar sz0 0 3 NQBudgetGen_C (4 / 5) = RBM.Ind.nqBudget_kapFar sz0 0 3 10 (1 / 2) (4 / 5) ∧
    NQBudgetGen_qvFar sz0 0 3 NQBudgetGen_C (4 / 5) = RBM.Ind.nqBudget_qvFar sz0 0 3 10 (1 / 2) (4 / 5) :=
  ⟨assembledRHSNonAltNg_band sz0 Einst sInst vg Kg 0 3 10 (1 / 2) (4 / 5) Γ4 Λ3 Φ1 6 5 1 (1 / 21) 1 _ aFar,
    NQBudgetGen_kapFar_band sz0 0 3 10 (1 / 2) (4 / 5), NQBudgetGen_qvFar_band sz0 0 3 10 (1 / 2) (4 / 5)⟩

/-- `NQBudgetGen_inv_one_sub_le` at `E = 1/2`, `v = 1/32`, `N = 2^21`: `(1 - v)⁻¹ ≤ N`. -/
example : (1 - (1 / 32 : ℝ))⁻¹ ≤ 2097152 :=
  NQBudgetGen_inv_one_sub_le NQBudgetGen_hL0 NQBudgetGen_hm0 (n := 0) (by norm_num : (1 / 32 : ℝ) < 1)
    (by
      have h := eta_inv_le_v
      change (NQBudgetGen_Cm0.eta 0 (vg 0))⁻¹ ≤ 11 / 10 at h
      have e : vg 0 = 1 / 32 := by norm_num [vg]
      rw [e] at h
      linarith)

/-- `NQBudgetGen_kappa_le_kapFar` at `sz0`, `n = 0`, `i = 1`, `m = 4` on the grid. -/
example : kappaNonAltNg 3 NQBudgetGen_C (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (4 / 5) (gridTime sInst vg Kg 0) 1 4 ≤
    NQBudgetGen_kapFar sz0 0 3 NQBudgetGen_C (4 / 5) :=
  NQBudgetGen_kappa_le_kapFar sz0 0 3 NQBudgetGen_C (4 / 5) (gridTime sInst vg Kg 0)
    (i := 1) (m := 4) (u_nonneg 1) (u_mono 1 4 (by norm_num)) (u_lt_one 4 le_rfl)
    (by
      have h := NQBudgetGen_inv_one_sub_le NQBudgetGen_hL0 NQBudgetGen_hm0 (n := 0) (u_lt_one 4 le_rfl) (Nn := 2097152)
        (by
          have h := eta_inv_le_v
          change (NQBudgetGen_Cm0.eta 0 (vg 0))⁻¹ ≤ 11 / 10 at h
          have e : vg 0 = gridTime sInst vg Kg 0 4 := by rw [u4]; norm_num [vg]
          rw [e] at h
          linarith)
      rw [N0]; exact h)

/-! ### (a) The three generic budgets, constant weights `κ ≡ 2`, `ε ≡ 1`, at `u = gridTime sInst vg Kg 0` and `B i = sz0.Bctl 0 (u i)` -/

/-- Instance of `tbInitNg`: `K = 4`, `κ ≡ 2`, `C_κ = 2`, `G = 3`, `X0 = 3 B_0^3`. -/
example : (2 : ℝ) * (3 * Bseq 0 ^ 3) ≤ 2 * 3 * Bseq 4 ^ 3 :=
  tbInitNg (k := 3) (K := 4) (Cκ := 2) (G := 3) (X0 := 3 * Bseq 0 ^ 3) Bseq (fun _ _ => 2)
    (by norm_num) (by norm_num)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Bseq_pos 0 (by norm_num)).le
      (Bseq_mono 0 4 (by norm_num) le_rfl) 3) (by norm_num))
    le_rfl

/-- Instance of `tbDriftNg`: `Δ = 1/128`, `K = 4`, `κ ≡ 2`, `ε ≡ 1`, `C_κ = C_far = 2`, `C_ε = 1`, `a = 1`, `b = δ = δ_max = 1/2`,
`d_j = B_j^3/η_{u_j}`. -/
example : (1 / 128 : ℝ) * ∑ j ∈ Finset.range 4,
        (2 * (Bseq j ^ 3 / NQBudgetGen_Cm0.eta 0 (gridTime sInst vg Kg 0 j)) + 1 * (1 / 2)) ≤
      2 * 1 * Bseq 4 ^ 3 * ∑ j ∈ Finset.range 4,
          (1 / 128 : ℝ) / NQBudgetGen_Cm0.eta 0 (gridTime sInst vg Kg 0 j) +
        ((4 : ℕ) * (1 / 128 : ℝ)) * (2 * (1 / 2) + 1 * (1 / 2)) :=
  tbDriftNg NQBudgetGen_Cm0 0 (k := 3) (K := 4) (Δ := 1 / 128) (Cκ := 2) (Cε := 1) (Cfar := 2)
    (a := 1) (b := 1 / 2) (δmax := 1 / 2) (gridTime sInst vg Kg 0) Bseq (fun _ _ => 2)
    (fun _ _ => 1) (fun j => Bseq j ^ 3 / NQBudgetGen_Cm0.eta 0 (gridTime sInst vg Kg 0 j))
    (fun _ => 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    (fun j hj => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Bseq_pos j (by omega)).le
      (Bseq_mono j 4 (by omega) le_rfl) 3) (by norm_num))
    (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun j hj => by simp only [one_mul]; linarith)
    (fun _ _ => by norm_num) (fun _ _ => le_rfl) (fun j hj => NQBudgetGen_eta_pos j (by omega))

/-- Instance of `tbQvNg`: `Δ = 1/128`, `K = 4`, `k = 3`, `κ ≡ 2`, `C_κ = C_far = 2`, `C_e = C_c = 1`, `G = 3`, `Wd = 1/2`. -/
example : ∑ j ∈ Finset.range 4, (1 / 128 : ℝ) * (((3 : ℕ) : ℝ) * nqBudget_qvShape 3 2 1 1 3 (1 / 2)
        (Bseq (j + 1)) (NQBudgetGen_Cm0.eta 0 (gridTime sInst vg Kg 0 (j + 1)))) ≤
      ((3 : ℕ) : ℝ) * 2 ^ 2 * 3 * (Bseq 4 ^ 3) ^ 2 * ∑ j ∈ Finset.range 4,
          (1 / 128 : ℝ) / NQBudgetGen_Cm0.eta 0 (gridTime sInst vg Kg 0 (j + 1)) +
        (((4 : ℕ) : ℝ) * (1 / 128)) * (((3 : ℕ) : ℝ) * ((2 * (2 + 1) + 1) * (1 / 2))) :=
  tbQvNg NQBudgetGen_Cm0 0 (k := 3) (K := 4) (Cκ := 2) (Cfar := 2) (Ce := 1) (Cc := 1) (G := 3)
    (Wd := 1 / 2) (Δ := 1 / 128) (gridTime sInst vg Kg 0) Bseq (fun _ => 2)
    (fun j hj => (Bseq_pos (j + 1) (by omega)).le) (fun _ _ => by norm_num)
    (fun j hj => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Bseq_pos (j + 1) (by omega)).le
      (Bseq_mono (j + 1) 4 (by omega) le_rfl) 3) (by norm_num))
    (fun _ _ => le_rfl) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun j hj => NQBudgetGen_eta_pos (j + 1) (by omega))

/-! ### (b) The budgets at the data of the non-alternating endpoint -/

/-- `qvBdNonAltNg_eq_qvShape` at `n = 0`, `k = 3`, `ε = 4/5`, `(Γ, Λ) = (4, 3)`, `D'' = 5`, `(u, w) = (u_1, u_4)`. -/
example : qvBdNonAltNg NQBudgetGen_Cm0 0 3 NQBudgetGen_C (4 / 5) 4 3 5 (gridTime sInst vg Kg 0 1) (gridTime sInst vg Kg 0 4) =
    nqBudget_qvShape 3
      (((sz0.W 0 : ℕ) : ℝ) ^ (NQBudgetGen_C * (4 / 5)) *
        ((sz0.lam 0 ^ 2 + |1 - gridTime sInst vg Kg 0 1|) / (sz0.lam 0 ^ 2 + |1 - gridTime sInst vg Kg 0 4|)) ^ (3 - 1))
      (((sz0.W 0 : ℕ) : ℝ) ^ NQBudgetGen_C) (((sz0.W 0 : ℕ) : ℝ) ^ NQBudgetGen_C * ((sz0.W 0 : ℕ) : ℝ) ^ 3)
      (4 * (4 * 3)) (((sz0.W 0 : ℕ) : ℝ) ^ (-(5 : ℝ))) (sz0.Bctl 0 (gridTime sInst vg Kg 0 1))
      (NQBudgetGen_Cm0.eta 0 (gridTime sInst vg Kg 0 1)) :=
  qvBdNonAltNg_eq_qvShape NQBudgetGen_Cm0 0 3 NQBudgetGen_C (4 / 5) 4 3 5 _ _

/-- `tbInitNonAltNg` at the data: `G = 4`, `X0 = 4 B_0^3`. -/
example :
    kappaNonAltNg 3 NQBudgetGen_C (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (4 / 5) (gridTime sInst vg Kg 0) 0 (Kg 0) *
        (4 * (sz0.Bctl 0 (sInst 0)) ^ 3) ≤
      ((sz0.W 0 : ℕ) : ℝ) ^ (NQBudgetGen_C * (4 / 5)) * 4 * (sz0.Bctl 0 (vg 0)) ^ 3 :=
  tbInitNonAltNg sz0 (s := sInst) (v := vg) (K := Kg) 0 3 NQBudgetGen_C (4 / 5) 4
    (4 * (sz0.Bctl 0 (sInst 0)) ^ 3) (by norm_num [sInst]) (by norm_num [sInst, vg])
    (by norm_num [vg]) (by norm_num [Kg]) (by norm_num) le_rfl

/-- `tbDriftNonAltNg` at the data: levels `(Γ, Φ) = (4, 1)`, `D' = 6`. -/
example :
    gridStep sInst vg Kg 0 * ∑ j ∈ Finset.range (Kg 0),
      (kappaNonAltNg 3 NQBudgetGen_C (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (4 / 5) (gridTime sInst vg Kg 0) (j + 1) (Kg 0) *
          dDriftNonAltNg NQBudgetGen_Cm0 0 (gridTime sInst vg Kg 0 j) 3 (Γ4 0) (Φ1 0) +
        epsNonAltNg NQBudgetGen_C ((sz0.W 0 : ℕ) : ℝ) (j + 1) (Kg 0) * ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ))) ≤
      ((sz0.W 0 : ℕ) : ℝ) ^ (NQBudgetGen_C * (4 / 5)) *
          (Γ4 0 * (Γ4 0 * Φ1 0) * (((3 : ℕ) : ℝ) - 1 + ((3 : ℕ) : ℝ) * (Γ4 0 * Φ1 0))) *
          (sz0.Bctl 0 (vg 0)) ^ 3 *
          ∑ j ∈ Finset.range (Kg 0), gridStep sInst vg Kg 0 / NQBudgetGen_Cm0.eta 0 (gridTime sInst vg Kg 0 j) +
        ((Kg 0 : ℕ) * gridStep sInst vg Kg 0) * (((sz0.W 0 : ℕ) : ℝ) ^ NQBudgetGen_C * ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ))) :=
  tbDriftNonAltNg NQBudgetGen_Cm0 NQBudgetGen_hL0 (s := sInst) (v := vg) (K := Kg) 0 3 NQBudgetGen_C (4 / 5) Γ4 Φ1 6
    NQBudgetGen_hm0 (by norm_num [sInst]) (by norm_num [sInst, vg]) (by norm_num [vg])
    (by norm_num [Kg]) (by norm_num) (by norm_num [Γ4]) (by norm_num [Φ1]) eta_inv_le_N

/-- `tbQvNonAltNg` at the data: levels `(Γ, Λ) = (4, 3)`, `D'' = 5`, label `aFar`. -/
example :
    ∑ j ∈ Finset.range (Kg 0), (cQVNonAltNg NQBudgetGen_Cm0 sInst vg Kg 0 3 NQBudgetGen_C (4 / 5) Γ4 Λ3 5 (Kg 0) aFar j : ℝ) ≤
      ((3 : ℕ) : ℝ) * (((sz0.W 0 : ℕ) : ℝ) ^ (NQBudgetGen_C * (4 / 5))) ^ 2 *
          (Γ4 0 * (Γ4 0 * Λ3 0)) * ((sz0.Bctl 0 (vg 0)) ^ 3) ^ 2 *
          ∑ j ∈ Finset.range (Kg 0),
            gridStep sInst vg Kg 0 / NQBudgetGen_Cm0.eta 0 (gridTime sInst vg Kg 0 (j + 1)) +
        ((Kg 0 : ℕ) * gridStep sInst vg Kg 0) *
          (((3 : ℕ) : ℝ) * (NQBudgetGen_qvFar sz0 0 3 NQBudgetGen_C (4 / 5) * ((sz0.W 0 : ℕ) : ℝ) ^ (-(5 : ℝ)))) :=
  tbQvNonAltNg NQBudgetGen_Cm0 NQBudgetGen_hL0 (s := sInst) (v := vg) (K := Kg) 0 3 NQBudgetGen_C (4 / 5) Γ4 Λ3 5
    aFar NQBudgetGen_hm0 (by norm_num [sInst]) (by norm_num [sInst, vg]) (by norm_num [vg])
    (by norm_num [Kg]) (by norm_num [Λ3]) eta_inv_le_N

/-- **`budgetNonAltNg` at the data** (`d = 3`, `sz0`, `n = 0`: `L = 4`, `W = 32`, `N = 2^21`; `E ≡ 1/2`, grid `(sInst, vg, Kg)`: `Δ = 1/128`,
`u_j = j/128`; `k = 3`, `ε = 4/5`; levels `(Γ, Λ, Φ) = (4, 3, 1)` with `Γ = N^{2/21}`; `D' = 6`, `D'' = 5`, `D_Y = 1`, `D_t = -5`, `τ_K = 1/21`,
`ε_q = 1`, `ε₀ = Ck + 12` with the abstract `Ck = nqGood1C 3 3 10 (1/2) > 0`; `X0 = 4 B_0^3`; label `aFar`): every hypothesis is discharged
(`hlog`, `hR` by the explicit bounds of the band instance, `ha1`-`he4` for every `Ck > 0`); nothing is left open. -/
example :
    assembledRHSNonAltNg NQBudgetGen_Cm0 sInst vg Kg 0 3 NQBudgetGen_C (4 / 5) Γ4 Λ3 Φ1 6 5 1 (1 / 21) 1
        (4 * (sz0.Bctl 0 (sInst 0)) ^ 3) aFar ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (NQBudgetGen_C + 12) *
        (Λ3 0 ^ ((1 : ℝ) / 2) + Φ1 0 + Φ1 0 ^ 2) * (sz0.Bctl 0 (vg 0)) ^ 3 :=
  budgetNonAltNg NQBudgetGen_Cm0 NQBudgetGen_hL0 sInst vg Kg 0 3 NQBudgetGen_C (4 / 5) Γ4 Λ3 Φ1 6 5 1 (-5) (1 / 21) 1
    (NQBudgetGen_C + 12) (2 / 21) (4 * (sz0.Bctl 0 (sInst 0)) ^ 3) aFar
    (by norm_num) (by norm_num) NQBudgetGen_hm0 (by norm_num [sInst]) (by norm_num [sInst, vg])
    (by norm_num [vg]) (by norm_num [Kg]) eta_inv_le_N
    (by
      have h : (NQBudgetGen_Cm0.eta 0 (vg 0))⁻¹ ≤ 11 / 10 := eta_inv_le_v
      rw [step0]; linarith)
    (by rw [N_eps1]) (by norm_num [Λ3]) (by norm_num [Φ1])
    hlog_instance (by rw [N_eps1]) hR_instance
    (ha1_inst _ Cpos) (ha2_inst _ Cpos) (ha3_inst _ Cpos) (he1_inst _ Cpos) (he2_inst Cpos)
    (he3_inst _ Cpos) (he4_inst _ Cpos)

/-! ### (c) `nqBudget_merged_inputsg` at the data of `GridEnvelopeNCheck` -/

section Merged

open RBM.Ind.GridEnvelopeNCheck

private abbrev NQBudgetGen_Cm00 : Step2Mat sz0 := bandStep2Mat sz0 (fun _ => 0)

private theorem NQBudgetGen_hspec00 : DecayGen_Spec NQBudgetGen_Cm00.toFlowFM (Real.sqrt 1 / 2) :=
  DecayGen_bandSpec sz0 (κ := 1) (by norm_num) (fun n => by norm_num)

private theorem NQBudgetGen_him00 (n : ℕ) : (NQBudgetGen_Cm00.m n).im ≤ 1 := by
  change (mE 0).im ≤ 1
  rw [mE_im]
  have h4 : Real.sqrt (4 - (0 : ℝ) ^ 2) = 2 := by
    rw [show (4 - (0 : ℝ) ^ 2) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [h4]
  norm_num

/-- **`nqBudget_merged_inputsg` at the data of `GridEnvelopeNCheck`** (`d = 3`, `sz0`, `κ_m = 1/2`, `τ' = τ_K = 1/2`, `C_K = 21`, `D_t = 1`,
`E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `K n = N_n^{21}`, `k = 3`): every hypothesis is discharged (`sz0_tendsto`, `rangeCond_half`, `rpow_21_le_Kc`,
`Kc_ne_zero`, the four `C_K` inequalities); `hlog` and `hR` hold eventually, and there is an index `n` at which both hold. -/
example :
    ∀ᶠ n : ℕ in atTop,
      (∑ j ∈ Finset.range (Kc n), gridStep (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n /
          NQBudgetGen_Cm00.eta n (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n j) ≤
        (NQBudgetGen_Cm00.m n).im⁻¹ * Real.log ((sz0.size n : ℕ) : ℝ)) ∧
      (∑ j ∈ Finset.range (Kc n),
          (1 + (1 - gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n (Kc n))⁻¹) ^ 3 *
          stepErrNg NQBudgetGen_Cm00.toFlowFM n 3 (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n j)
            (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n (j + 1))
            (gridStep (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n)
            (((sz0.size n : ℕ) : ℝ) ^ (1 / 2 : ℝ) *
              (NQBudgetGen_Cm00.eta n (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n (j + 1)))⁻¹ ^ 3) ≤
        ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) :=
  nqBudget_merged_inputsg NQBudgetGen_Cm00 (κm := Real.sqrt 1 / 2) (τ' := 1 / 2) (τK := 1 / 2) (C_K := 21) (D_t := 1)
    (s := fun _ => 0) (v := fun _ => 1 / 2) (K := Kc) 3 NQBudgetGen_hspec00 NQBudgetGen_him00 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) sz0_tendsto (fun _ => le_rfl) (fun _ => by norm_num) (fun _ => by norm_num)
    Kc_ne_zero rangeCond_half (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Eventually.of_forall rpow_21_le_Kc)

end Merged

end Inst

end RBM.BA

end
