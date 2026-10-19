/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.NQGood2Gen
import RBM3D.Induction.NQBudget

/-!
# The term budgets of the non-alternating assembled bound over the carrier

Generic forms of `Induction/NQBudget` over a carrier `Cm : Step2Mat sz`, namespace `RBM.BA`.  Paper:
Lemma 4.6 (`lem:STOeq_NQ`) and its proof, (4.22) `am;asoiuw`.  `etaT E` is `Cm.eta n` (`LoopForm`), the
constant `nqGood1C d k Λg κ'` is an explicit `Ck`, `stepErrN` is `stepErrNg`, `(mE E).im` is
`(Cm.m n).im`; the spectral facts `0 < Im m` (`LoopForm`) and `‖Cm.m n‖ ≤ 1` (inline, per index)
replace `|E n| < 2`.

* The vocabulary `NQBudgetGen_kapFar`, `NQBudgetGen_qvFar`, the elementary facts
  `NQBudgetGen_inv_one_sub_le`, `NQBudgetGen_kappa_le_kapFar`, the generic budgets `tbInitNg`
  (model-free: the band `tbInitN`), `tbDriftNg`, `tbQvNg`, and their instances at the data
  `qvBdNonAltNg_eq_qvShape`, `tbInitNonAltNg`, `tbQvNonAltNg`.
* `nqBudget_merged_inputsg`: eventually in `n`, the two sums `Σ_j Δ/η_{u_j} ≤ (Im m)⁻¹ log N` and the
  weighted step errors `≤ N^{-D_t}` at `m = K n`, the conclusions of `sum_gridStep_div_etaNg_le` and
  `sum_weighted_stepErrNg_le`.  The scalar `nqBudget_qvShape`, `nqBudget_sum_succ_le`,
  `nqBudget_sqrt_add_le` are model-free and used by name.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open private nqBudget_gridTime_nonneg nqBudget_gridTime_le
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

/-- **The far bound of the kernel weight** (band `nqBudget_kapFar`): `κ_{i,m} ≤ W^{Ck ε} ((1+g²) N)^{k-1}` when
`(1-u_m)⁻¹ ≤ N` (see `NQBudgetGen_kappa_le_kapFar`). -/
def NQBudgetGen_kapFar (sz : Sizes d) (n k : ℕ) (Ck ε : ℝ) : ℝ :=
  ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) * ((1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ)) ^ (k - 1)

/-- **The far coefficient of the quadratic variation** (band `nqBudget_qvFar`): the coefficient of `W^{-D''}` in `nqBudget_qvShape` at
`κ ≤ NQBudgetGen_kapFar`, `Ce = W^{Ck}`, `Cc = W^{Ck} W^k`. -/
def NQBudgetGen_qvFar (sz : Sizes d) (n k : ℕ) (Ck ε : ℝ) : ℝ :=
  NQBudgetGen_kapFar sz n k Ck ε * (NQBudgetGen_kapFar sz n k Ck ε + ((sz.W n : ℕ) : ℝ) ^ Ck) +
    ((sz.W n : ℕ) : ℝ) ^ Ck * ((sz.W n : ℕ) : ℝ) ^ k

end Vocab

/-! ## 2. Elementary facts -/

section Basic

variable {d : ℕ}

/-- `η_v⁻¹ ≤ N` gives `(1-v)⁻¹ ≤ N` (band `nqBudget_inv_one_sub_le`): `(1-v)⁻¹ = Im m · η_v⁻¹` (`LoopForm`), `Im m ≤ 1` (`‖m‖ ≤ 1`). -/
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

/-- **The far bound of the kernel weight** (band `nqBudget_kappa_le_kapFar`): for `0 ≤ u_i ≤ u_m < 1` and
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

/-- **Generic initial term** (band `tbInitN`; model-free, so the band theorem is reused): for weights `κ` with
`κ(0,K) B_0^k ≤ C_κ B_K^k` and an initial supremum `X0 ≤ G B_0^k`, `κ(0,K) X0 ≤ C_κ G B_K^k`. -/
theorem tbInitNg {k K : ℕ} {Cκ G X0 : ℝ} (B : ℕ → ℝ) (κ : ℕ → ℕ → ℝ)
    (hκ0 : 0 ≤ κ 0 K) (hG : 0 ≤ G)
    (hker : κ 0 K * B 0 ^ k ≤ Cκ * B K ^ k) (hX0 : X0 ≤ G * B 0 ^ k) :
    κ 0 K * X0 ≤ Cκ * G * B K ^ k :=
  tbInitN B κ hκ0 hG hker hX0

/-- **Generic drift term** (band `tbDriftN`), with `η_u = Cm.eta n u`: for weights `κ, ε` with
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

/-- **Generic quadratic-variation term** (band `tbQvN`), with `η_u = Cm.eta n u`: for weights `0 ≤ κ_j ≤ C_far` with
`κ_j B_{j+1}^k ≤ C_κ B_K^k`, `Σ_{j<K} Δ k nqBudget_qvShape ≤ k C_κ² G (B_K^k)² Σ_j Δ/η_{u_{j+1}} +
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

/-! ## 4. The generic budgets at the non-alternating data -/

section Instances

variable {d : ℕ} {sz : Sizes d}

/-- **`qvBdNonAltNg` has the shape `nqBudget_qvShape`** with `κ = W^{Ck ε} r^{k-1}`, `Ce = W^{Ck}`, `Cc = W^{Ck} W^k`, `G = Γ(ΓΛ)`,
`Wd = W^{-D''}`, `B = B_u`, `η = η_u` (band `qvBdNonAltN_eq_qvShape`). -/
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

/-- **The initial term at the data** (band `tbInitNonAltN`): `κ_{0,K} X0 ≤ W^{Ck ε} G B_v^k` for `X0 ≤ G B_{s}^k`
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

/-- **The quadratic-variation term at the data** (band `tbQvNonAltN`): the sum of the sub-Gaussian proxies `cQVNonAltNg`
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

/-! ## 5. The two sums of the budget as consequences of two theorems

The two inequalities `Σ_j Δ/η_{u_j} ≤ (Im m)⁻¹ log N` and `Σ_j (1 + (1 - u_{K n})⁻¹)^k (step error) ≤ N^{-D_t}` are, at each `n`, exactly the conclusions of
`sum_gridStep_div_etaNg_le` and `sum_weighted_stepErrNg_le` (at `m = K n`); the side conditions are those
of the two theorems, the spectral data are `DecayGen_Spec` and the hypothesis `∀ n, (Cm.m n).im ≤ 1`. -/

section MergedInputs

variable {d : ℕ} {sz : Sizes d}

/-- **`nqBudget_merged_inputsg`** (band `nqBudget_merged_inputs`): the two inequalities above hold eventually. -/
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

end RBM.BA

end
