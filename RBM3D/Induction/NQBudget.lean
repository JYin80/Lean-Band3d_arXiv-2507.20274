/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.NQGood2
import RBM3D.Induction.GridEnvelopeN
import RBM3D.Induction.ContinuityNet

/-!
# The term budgets of the non-alternating assembled bound at the `d ≥ 3` data of `NQGood2`

Generic budgets for the initial, drift and quadratic-variation terms of the non-alternating assembled
bound, and their instances at the data of `Induction/NQGood2` (the `d ≥ 3` form of RBM2D's
`NonAltBudget`).  The ratio inequality `nqGood2_ratio_mul_Bctl_le`
(`((ℓ²+|1-u|)/(ℓ²+|1-t|)) B_{u,0} ≤ B_{t,0}`, used in the proof of Lemma 4.6 `lem:STOeq_NQ`) takes the
place of the two-dimensional identity `ρ_{s,t} M_s⁻¹ = M_t⁻¹` (`scaleM⁻¹ ↦ Bctl`); the kernel weights
are `W^{Cε} r^{k-1}` and `W^C` with `C = nqGood1C` (abstract), and the drift level has no additive
part.
Paper: Lemma 4.6 (`lem:STOeq_NQ`) and its proof.

## Sections (namespace `RBM.Ind`)

1. The vocabulary: `nqBudget_qvShape`, `nqBudget_kapFar`, `nqBudget_qvFar`.
2. Elementary facts (prefix `nqBudget_`): `nqBudget_im_le_one`, `nqBudget_inv_one_sub_le`,
   `nqBudget_sum_succ_le`, `nqBudget_sqrt_add_le`, `nqBudget_kappa_le_kapFar`.
3. Generic budgets for abstract kernel weights (`B : ℕ → ℝ` the scale sequence): `tbInitN`,
   `tbDriftN`, `tbQvN`.
4. Their instances at the data of `NQGood2`: `qvBdNonAltN_eq_qvShape`, `tbInitNonAltN`,
   `tbQvNonAltN`.
5. `nqBudget_merged_inputs`: the two summation bounds `hlog`, `hR` of the assembled budget are the
   conclusions of `sum_gridStep_div_etaT_le`, `sum_weighted_stepErrN_le` at `m = K n`.

Every helper that is not part of the statements is `private` or prefixed `nqBudget_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-! ## 1. The vocabulary -/

/-- **The shape of the quadratic-variation majorant** (the `d ≥ 3` form of RBM2D's `NonAltBudget_qvShape`):
`κ(κ(G B^{2k}/η + Wd) + Ce Wd) + Cc Wd`; `qvBdNonAltN` is the
case `κ = W^{Cε} r^{k-1}`, `Ce = W^C`, `Cc = W^C W^k`, `G = Γ(ΓΛ)`, `Wd = W^{-D''}`, `B = B_u`, `η = η_u`. -/
def nqBudget_qvShape (k : ℕ) (κ Ce Cc G Wd B η : ℝ) : ℝ :=
  κ * (κ * (G * (B ^ (2 * k) / η) + Wd) + Ce * Wd) + Cc * Wd

/-- **The far bound of the kernel weight**: `κ_{i,m} ≤ W^{Cε} ((1+g²) N)^{k-1}` when
`(1-u_m)⁻¹ ≤ N` (`r_{i,m} ≤ (1+g²)(1-u_m)⁻¹`). -/
def nqBudget_kapFar {d : ℕ} (sz : Sizes d) (n k : ℕ) (Λg κ' ε : ℝ) : ℝ :=
  ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
    ((1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ)) ^ (k - 1)

/-- **The far coefficient of the quadratic variation**: the coefficient of `W^{-D''}` in
`nqBudget_qvShape` at `κ ≤ nqBudget_kapFar`, `Ce = W^C`, `Cc = W^C W^k`. -/
def nqBudget_qvFar {d : ℕ} (sz : Sizes d) (n k : ℕ) (Λg κ' ε : ℝ) : ℝ :=
  nqBudget_kapFar sz n k Λg κ' ε *
      (nqBudget_kapFar sz n k Λg κ' ε + ((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ') +
    ((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' * ((sz.W n : ℕ) : ℝ) ^ k

/-! ## 2. Elementary facts -/

section Basic

/-- `Im m(E) ≤ 1` for every real `E` (`Im m(E) = √(4 - E²)/2`; the square root is `0` off the bulk
and `≤ 2` on it). -/
theorem nqBudget_im_le_one (E : ℝ) : (mE E).im ≤ 1 := by
  rw [mE_im]
  have h : Real.sqrt (4 - E ^ 2) ≤ 2 :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith [sq_nonneg E]⟩
  linarith

/-- `η_v⁻¹ ≤ N` gives `(1-v)⁻¹ ≤ N` (`(1-v)⁻¹ = Im m · η_v⁻¹`, `Im m ≤ 1`). -/
theorem nqBudget_inv_one_sub_le {E v Nn : ℝ} (hE : |E| < 2) (hv1 : v < 1)
    (hη : (etaT E v)⁻¹ ≤ Nn) : (1 - v)⁻¹ ≤ Nn := by
  have hm := nqBudget_im_le_one E
  have hm0 := mE_im_pos hE
  have h1 : 0 < 1 - v := by linarith
  have heq : (1 - v)⁻¹ = (mE E).im * (etaT E v)⁻¹ := by
    unfold etaT
    field_simp
  rw [heq]
  have h0 : 0 ≤ (etaT E v)⁻¹ := by
    have := etaT_pos hE hv1
    positivity
  nlinarith

/-- Reindexing the time sum: `Σ_{j<K} f(j+1) ≤ Σ_{j<K} f j + f K` for
`0 ≤ f 0`. -/
theorem nqBudget_sum_succ_le {K : ℕ} (f : ℕ → ℝ) (hf0 : 0 ≤ f 0) :
    ∑ j ∈ Finset.range K, f (j + 1) ≤ ∑ j ∈ Finset.range K, f j + f K := by
  have h := Finset.sum_range_succ' f K
  have h2 := Finset.sum_range_succ f K
  linarith

/-- `√(x + y) ≤ √x + √y` for `x, y ≥ 0`. -/
theorem nqBudget_sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have h : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    have h1 := Real.sq_sqrt hx
    have h2 := Real.sq_sqrt hy
    have h3 : 0 ≤ Real.sqrt x * Real.sqrt y := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith
  calc Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt x + Real.sqrt y :=
        Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- **The far bound of the kernel weight**: for `0 ≤ u_i ≤ u_m < 1` and `(1-u_m)⁻¹ ≤ N`,
`κ_{i,m} = W^{Cε} r_{i,m}^{k-1} ≤ W^{Cε} ((1+g²) N)^{k-1}` (`r_{i,m} ≤ (1+g²)(1-u_m)⁻¹`), for every
real `g = sz.lam n`. -/
theorem nqBudget_kappa_le_kapFar {d : ℕ} (sz : Sizes d) (n k : ℕ) (Λg κ' ε : ℝ) (u : ℕ → ℝ)
    {i m : ℕ} (hu0 : 0 ≤ u i) (hium : u i ≤ u m) (hm1 : u m < 1)
    (hN : (1 - u m)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) :
    kappaNonAltN d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε u i m ≤
      nqBudget_kapFar sz n k Λg κ' ε := by
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
  have hWC : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  unfold kappaNonAltN nqBudget_kapFar
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr _) hWC

end Basic

/-! ## 3. Generic term budgets (abstract kernel weights) -/

section Generic

/-- **Generic initial term** (the form of RBM2D's `tbInit`): for weights `κ` with
`κ(0,K) B_0^k ≤ C_κ B_K^k` and an initial supremum `X0 ≤ G B_0^k`, `κ(0,K) X0 ≤ C_κ G B_K^k`. -/
theorem tbInitN {k K : ℕ} {Cκ G X0 : ℝ} (B : ℕ → ℝ) (κ : ℕ → ℕ → ℝ)
    (hκ0 : 0 ≤ κ 0 K) (hG : 0 ≤ G)
    (hker : κ 0 K * B 0 ^ k ≤ Cκ * B K ^ k) (hX0 : X0 ≤ G * B 0 ^ k) :
    κ 0 K * X0 ≤ Cκ * G * B K ^ k := by
  calc κ 0 K * X0 ≤ κ 0 K * (G * B 0 ^ k) := mul_le_mul_of_nonneg_left hX0 hκ0
    _ = G * (κ 0 K * B 0 ^ k) := by ring
    _ ≤ G * (Cκ * B K ^ k) := mul_le_mul_of_nonneg_left hker hG
    _ = _ := by ring

/-- **Generic drift term** (the form of RBM2D's `tbDrift`): for weights `κ, ε` with
`κ(j+1,K) B_j^k ≤ C_κ B_K^k`,
`κ(j+1,K) ≤ C_far`, `ε(j+1,K) ≤ C_ε` and drift levels `d_j ≤ a (B_j^k / η_{u_j}) + b`,
`0 ≤ δ_j ≤ δ_max`: `Δ Σ_{j<K} (κ(j+1,K) d_j + ε(j+1,K) δ_j) ≤
C_κ a B_K^k Σ_j Δ/η_{u_j} + (K Δ)(C_far b + C_ε δ_max)`. -/
theorem tbDriftN {E : ℝ} {k K : ℕ} {Δ Cκ Cε Cfar a b δmax : ℝ} (u B : ℕ → ℝ)
    (κ ε : ℕ → ℕ → ℝ) (dd δ : ℕ → ℝ) (hΔ : 0 ≤ Δ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hκ0 : ∀ j < K, 0 ≤ κ (j + 1) K) (hε0 : ∀ j < K, 0 ≤ ε (j + 1) K)
    (hκM : ∀ j < K, κ (j + 1) K * B j ^ k ≤ Cκ * B K ^ k)
    (hκfar : ∀ j < K, κ (j + 1) K ≤ Cfar) (hεC : ∀ j < K, ε (j + 1) K ≤ Cε)
    (hd : ∀ j < K, dd j ≤ a * (B j ^ k / etaT E (u j)) + b)
    (hδ0 : ∀ j < K, 0 ≤ δ j) (hδ : ∀ j < K, δ j ≤ δmax) (hη : ∀ j < K, 0 < etaT E (u j)) :
    Δ * ∑ j ∈ Finset.range K, (κ (j + 1) K * dd j + ε (j + 1) K * δ j) ≤
      Cκ * a * B K ^ k * ∑ j ∈ Finset.range K, Δ / etaT E (u j) +
        ((K : ℝ) * Δ) * (Cfar * b + Cε * δmax) := by
  have hstep : ∀ j ∈ Finset.range K,
      Δ * (κ (j + 1) K * dd j + ε (j + 1) K * δ j) ≤
        Cκ * a * B K ^ k * (Δ / etaT E (u j)) + Δ * (Cfar * b + Cε * δmax) := by
    intro j hj
    have hjK := Finset.mem_range.1 hj
    have h1 : κ (j + 1) K * dd j ≤ κ (j + 1) K * (a * (B j ^ k / etaT E (u j)) + b) :=
      mul_le_mul_of_nonneg_left (hd j hjK) (hκ0 j hjK)
    have h2 : κ (j + 1) K * (a * (B j ^ k / etaT E (u j)) + b) =
        (a * (etaT E (u j))⁻¹) * (κ (j + 1) K * B j ^ k) + κ (j + 1) K * b := by
      rw [div_eq_mul_inv]; ring
    have h3 : (a * (etaT E (u j))⁻¹) * (κ (j + 1) K * B j ^ k) ≤
        (a * (etaT E (u j))⁻¹) * (Cκ * B K ^ k) :=
      mul_le_mul_of_nonneg_left (hκM j hjK) (mul_nonneg ha (inv_nonneg.2 (hη j hjK).le))
    have h4 : κ (j + 1) K * b ≤ Cfar * b := mul_le_mul_of_nonneg_right (hκfar j hjK) hb
    have h5 : ε (j + 1) K * δ j ≤ Cε * δmax :=
      calc ε (j + 1) K * δ j ≤ ε (j + 1) K * δmax :=
            mul_le_mul_of_nonneg_left (hδ j hjK) (hε0 j hjK)
        _ ≤ Cε * δmax := mul_le_mul_of_nonneg_right (hεC j hjK) ((hδ0 j hjK).trans (hδ j hjK))
    have h6 : κ (j + 1) K * dd j + ε (j + 1) K * δ j ≤
        (a * (etaT E (u j))⁻¹) * (Cκ * B K ^ k) + (Cfar * b + Cε * δmax) := by
      linarith
    have h7 := mul_le_mul_of_nonneg_left h6 hΔ
    have e : Δ * ((a * (etaT E (u j))⁻¹) * (Cκ * B K ^ k) + (Cfar * b + Cε * δmax)) =
        Cκ * a * B K ^ k * (Δ / etaT E (u j)) + Δ * (Cfar * b + Cε * δmax) := by
      rw [div_eq_mul_inv]; ring
    rw [e] at h7
    exact h7
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum hstep).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  ring

/-- **Generic quadratic-variation term** (the form of RBM2D's `tbQv`; the proxies are
`c_j = Δ k nqBudget_qvShape(κ_j, …, B_{j+1}, η_{u_{j+1}})`): for weights
`0 ≤ κ_j ≤ C_far` with `κ_j B_{j+1}^k ≤ C_κ B_K^k`,
`Σ_{j<K} Δ k qvShape ≤ k C_κ² G (B_K^k)² Σ_j Δ/η_{u_{j+1}} +
(K Δ) k ((C_far (C_far + C_e) + C_c) Wd)`. -/
theorem tbQvN {E : ℝ} {k K : ℕ} {Cκ Cfar Ce Cc G Wd Δ : ℝ} (u B κ : ℕ → ℝ)
    (hB0 : ∀ j < K, 0 ≤ B (j + 1)) (hκ0 : ∀ j < K, 0 ≤ κ j)
    (hκM : ∀ j < K, κ j * B (j + 1) ^ k ≤ Cκ * B K ^ k) (hκfar : ∀ j < K, κ j ≤ Cfar)
    (hG : 0 ≤ G) (hWd : 0 ≤ Wd) (hCe : 0 ≤ Ce) (hΔ : 0 ≤ Δ)
    (hη : ∀ j < K, 0 < etaT E (u (j + 1))) :
    ∑ j ∈ Finset.range K, Δ * ((k : ℝ) * nqBudget_qvShape k (κ j) Ce Cc G Wd (B (j + 1))
        (etaT E (u (j + 1)))) ≤
      (k : ℝ) * Cκ ^ 2 * G * (B K ^ k) ^ 2 * ∑ j ∈ Finset.range K, Δ / etaT E (u (j + 1)) +
        ((K : ℝ) * Δ) * ((k : ℝ) * ((Cfar * (Cfar + Ce) + Cc) * Wd)) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hstep : ∀ j ∈ Finset.range K,
      Δ * ((k : ℝ) * nqBudget_qvShape k (κ j) Ce Cc G Wd (B (j + 1)) (etaT E (u (j + 1)))) ≤
        (k : ℝ) * Cκ ^ 2 * G * (B K ^ k) ^ 2 * (Δ / etaT E (u (j + 1))) +
          Δ * ((k : ℝ) * ((Cfar * (Cfar + Ce) + Cc) * Wd)) := by
    intro j hj
    have hjK := Finset.mem_range.1 hj
    have hκj := hκ0 j hjK
    have hη0 := hη j hjK
    have hkB : 0 ≤ κ j * B (j + 1) ^ k := mul_nonneg hκj (pow_nonneg (hB0 j hjK) _)
    have hsq : (κ j * B (j + 1) ^ k) ^ 2 ≤ (Cκ * B K ^ k) ^ 2 :=
      pow_le_pow_left₀ hkB (hκM j hjK) 2
    have hq1 : κ j * κ j * (G * (B (j + 1) ^ (2 * k) / etaT E (u (j + 1)))) ≤
        Cκ ^ 2 * G * (B K ^ k) ^ 2 * (etaT E (u (j + 1)))⁻¹ := by
      have e : κ j * κ j * (G * (B (j + 1) ^ (2 * k) / etaT E (u (j + 1)))) =
          (G * (etaT E (u (j + 1)))⁻¹) * (κ j * B (j + 1) ^ k) ^ 2 := by
        rw [div_eq_mul_inv, pow_mul']; ring
      rw [e]
      calc (G * (etaT E (u (j + 1)))⁻¹) * (κ j * B (j + 1) ^ k) ^ 2
          ≤ (G * (etaT E (u (j + 1)))⁻¹) * (Cκ * B K ^ k) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (mul_nonneg hG (inv_nonneg.2 hη0.le))
        _ = _ := by ring
    have hf1 : κ j * κ j * Wd ≤ Cfar * Cfar * Wd :=
      mul_le_mul_of_nonneg_right (mul_le_mul (hκfar j hjK) (hκfar j hjK) hκj (hκj.trans (hκfar j hjK)))
        hWd
    have hf2 : κ j * Ce * Wd ≤ Cfar * Ce * Wd :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hκfar j hjK) hCe) hWd
    have hshape : nqBudget_qvShape k (κ j) Ce Cc G Wd (B (j + 1)) (etaT E (u (j + 1))) ≤
        Cκ ^ 2 * G * (B K ^ k) ^ 2 * (etaT E (u (j + 1)))⁻¹ + (Cfar * (Cfar + Ce) + Cc) * Wd := by
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

/-! ## 4. The generic budgets at the data of `NQGood2` -/

section Instances

variable {d : ℕ} (sz : Sizes d)

/-- `0 ≤ u_i` on the grid `0 ≤ s_n ≤ v_n`. -/
private theorem nqBudget_gridTime_nonneg {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hs0 : 0 ≤ s n)
    (hsv : s n ≤ v n) (i : ℕ) : 0 ≤ gridTime s v K n i := by
  have h := ST_gridTime_mono s v K n hsv (Nat.zero_le i)
  rw [ST_gridTime_zero] at h
  linarith

/-- `u_i ≤ v_n` for `i ≤ K_n`, `K_n ≠ 0`. -/
private theorem nqBudget_gridTime_le {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hsv : s n ≤ v n)
    (hK : K n ≠ 0) {i : ℕ} (hi : i ≤ K n) : gridTime s v K n i ≤ v n :=
  (ST_gridTime_mono s v K n hsv hi).trans_eq (gridTime_last s v K n hK)

/-- **`qvBdNonAltN` has the shape `nqBudget_qvShape`** with `κ = W^{Cε} r^{k-1}`, `Ce = W^C`,
`Cc = W^C W^k`, `G = Γ(ΓΛ)`, `Wd = W^{-D''}`, `B = B_u`, `η = η_u`. -/
theorem qvBdNonAltN_eq_qvShape (n k : ℕ) (E : ℝ) (Λg κ' ε Γ Λ D'' u w : ℝ) :
    qvBdNonAltN sz n E k Λg κ' ε Γ Λ D'' u w =
      nqBudget_qvShape k
        (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
          ((sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - w|)) ^ (k - 1))
        (((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ')
        (((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' * ((sz.W n : ℕ) : ℝ) ^ k)
        (Γ * (Γ * Λ)) (((sz.W n : ℕ) : ℝ) ^ (-D'')) (sz.Bctl n u) (etaT E u) := by
  unfold qvBdNonAltN nqBudget_qvShape
  ring

/-- **The initial term at the data of `NQGood2`**: `κ_{0,K} X0 ≤
W^{Cε} G B_v^k` for `X0 ≤ G B_{s}^k` (`kappaNonAltN_mul_Bctl_pow_le`).  `|E n| < 2` is not needed. -/
theorem tbInitNonAltN {s v : ℕ → ℝ} {K : ℕ → ℕ} (n k : ℕ) (Λg κ' ε G X0 : ℝ)
    (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1) (hK : K n ≠ 0) (hG : 0 ≤ G)
    (hX0 : X0 ≤ G * (sz.Bctl n (s n)) ^ k) :
    kappaNonAltN d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) 0 (K n) * X0 ≤
      ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) * G * (sz.Bctl n (v n)) ^ k := by
  have hW : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  have huK := gridTime_last s v K n hK
  have hu0 := ST_gridTime_zero s v K n
  have hκ0 := nonAlt_hκ0N d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε hW (K n) (gridTime s v K n)
    0 (K n) (Nat.zero_le _) le_rfl
  have hker := kappaNonAltN_mul_Bctl_pow_le sz n k Λg κ' ε hW (gridTime s v K n)
    (i := 0) (m := K n) (by rw [hu0, huK]; exact hsv) (by rw [huK]; exact hv1)
  rw [hu0, huK] at hker
  have h := tbInitN (k := k) (K := K n) (Cκ := ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε))
    (G := G) (X0 := X0) (fun i => sz.Bctl n (gridTime s v K n i))
    (kappaNonAltN d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n)) hκ0 hG
    (by simpa only [hu0, huK] using hker) (by simpa only [hu0] using hX0)
  simpa only [huK] using h

/-- **The quadratic-variation term at the data of `NQGood2`**: the sum of
the sub-Gaussian proxies `cQVNonAltN` at the target `u_K = v` is at most
`k (W^{Cε})² Γ(ΓΛ) (B_v^k)² Σ_j Δ/η_{u_{j+1}} + (KΔ) k (nqBudget_qvFar W^{-D''})`
(`toNNReal` removed by `qvBdNonAltN_pos`). -/
theorem tbQvNonAltN {E s v : ℕ → ℝ} {K : ℕ → ℕ} (n k : ℕ) (Λg κ' ε : ℝ) (Γ Λ : ℕ → ℝ)
    (D'' : ℝ) (a : Fin k → Zd d (sz.L n)) (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n)
    (hv1 : v n < 1) (hK : K n ≠ 0) (hΛ : 0 ≤ Λ n)
    (hη : (etaT (E n) (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) :
    ∑ j ∈ Finset.range (K n), (cQVNonAltN sz E s v K n k Λg κ' ε Γ Λ D'' (K n) a j : ℝ) ≤
      (k : ℝ) * (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε)) ^ 2 * (Γ n * (Γ n * Λ n)) *
          ((sz.Bctl n (v n)) ^ k) ^ 2 *
          ∑ j ∈ Finset.range (K n),
            gridStep s v K n / etaT (E n) (gridTime s v K n (j + 1)) +
        ((K n : ℝ) * gridStep s v K n) *
          ((k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε * ((sz.W n : ℕ) : ℝ) ^ (-D''))) := by
  have hW : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hu0 : ∀ i, 0 ≤ gridTime s v K n i := fun i => nqBudget_gridTime_nonneg hs0 hsv i
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi =>
    (nqBudget_gridTime_le hsv hK hi).trans_lt hv1
  have huK := gridTime_last s v K n hK
  have hmono : ∀ i m, i ≤ m → gridTime s v K n i ≤ gridTime s v K n m := fun i m him =>
    ST_gridTime_mono s v K n hsv him
  have hΔ0 : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n hsv
  have hN1 : (1 - v n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := nqBudget_inv_one_sub_le hE hv1 hη
  have hWd : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'') := Real.rpow_nonneg hW _
  have hWC : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' := Real.rpow_nonneg hW _
  have hG : 0 ≤ Γ n * (Γ n * Λ n) := by
    have : Γ n * (Γ n * Λ n) = Γ n ^ 2 * Λ n := by ring
    rw [this]; positivity
  have hcoe : ∀ j ∈ Finset.range (K n),
      (cQVNonAltN sz E s v K n k Λg κ' ε Γ Λ D'' (K n) a j : ℝ) =
        gridStep s v K n * ((k : ℝ) * nqBudget_qvShape k
          (kappaNonAltN d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) (j + 1) (K n))
          (((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ')
          (((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' * ((sz.W n : ℕ) : ℝ) ^ k)
          (Γ n * (Γ n * Λ n)) (((sz.W n : ℕ) : ℝ) ^ (-D''))
          (sz.Bctl n (gridTime s v K n (j + 1))) (etaT (E n) (gridTime s v K n (j + 1)))) := by
    intro j hj
    have hjK := Finset.mem_range.1 hj
    have hpos := qvBdNonAltN_pos sz n (E := E n) (k := k) (Λg := Λg) (κ' := κ') (ε := ε)
      (Γ := Γ n) (D'' := D'') (w := gridTime s v K n (K n)) hΛ
      (hu1 (j + 1) (by omega)).le
    unfold cQVNonAltN
    rw [Real.coe_toNNReal _ (by positivity), qvBdNonAltN_eq_qvShape]
    rfl
  rw [Finset.sum_congr rfl hcoe]
  have h := tbQvN (E := E n) (k := k) (K := K n) (Cκ := ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε))
    (Cfar := nqBudget_kapFar sz n k Λg κ' ε) (Ce := ((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ')
    (Cc := ((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' * ((sz.W n : ℕ) : ℝ) ^ k)
    (G := Γ n * (Γ n * Λ n)) (Wd := ((sz.W n : ℕ) : ℝ) ^ (-D'')) (Δ := gridStep s v K n)
    (gridTime s v K n) (fun i => sz.Bctl n (gridTime s v K n i))
    (fun j => kappaNonAltN d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) (j + 1) (K n))
    (fun j hj => (Sizes.STBctl_pos sz n (hu1 (j + 1) (by omega))).le)
    (fun j hj => nonAlt_hκ0N d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε hW (K n) _ (j + 1) (K n)
      (by omega) le_rfl)
    (fun j hj => kappaNonAltN_mul_Bctl_pow_le sz n k Λg κ' ε hW (gridTime s v K n)
      (hmono (j + 1) (K n) (by omega)) (hu1 _ le_rfl))
    (fun j hj => nqBudget_kappa_le_kapFar sz n k Λg κ' ε (gridTime s v K n) (hu0 (j + 1))
      (hmono (j + 1) (K n) (by omega)) (hu1 _ le_rfl) (by rw [huK]; exact hN1))
    hG hWd hWC hΔ0 (fun j hj => etaT_pos hE (hu1 (j + 1) (by omega)))
  rw [huK] at h
  exact h

end Instances

/-! ## 5. The two summation bounds of the assembled budget

`hlog` and `hR` of the assembled budget are, at each `n`, exactly the conclusions of
`sum_gridStep_div_etaT_le` and `sum_weighted_stepErrN_le` (at `m = K n`); the theorem below states them
(the side conditions are those of the two theorems). -/

section MergedInputs

theorem nqBudget_merged_inputs {d : ℕ} (sz : Sizes d) {κ τ' τK C_K D_t : ℝ} {E s v : ℕ → ℝ}
    {K : ℕ → ℕ} (k : ℕ) (hκ : 0 < κ) (hτ' : 0 < τ') (hτ'1 : τ' ≤ 1) (hτK : 0 < τK)
    (hDt : 0 ≤ D_t) (hk : 2 ≤ k) (hsize : sz.SizeTendsto) (hE : ∀ n, |E n| ≤ 2 - κ)
    (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1) (hK0 : ∀ n, K n ≠ 0)
    (hrange : sz.RangeCond τ' v)
    (h1 : 8 + (4 * (k : ℝ) + 8) * (1 - τ') + 2 * D_t < C_K)
    (h2 : 3 + 4 * τK + 5 * (k : ℝ) * (1 - τ') + D_t < C_K)
    (h3 : 2 * (1 - τ') + τK + 2 * (k : ℝ) * (1 - τ') + D_t < C_K) (h4 : 1 - τ' < C_K)
    (hKN : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      (∑ j ∈ Finset.range (K n), gridStep s v K n / etaT (E n) (gridTime s v K n j) ≤
        (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) ∧
      (∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k *
          stepErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1))
            (gridStep s v K n)
            (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ k) ≤
        ((sz.size n : ℕ) : ℝ) ^ (-D_t)) := by
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith
  filter_upwards [sum_gridStep_div_etaT_le sz hτ' hE2 hs0 hsv hv1 hK0 hrange,
    sum_weighted_stepErrN_le d sz k hκ hτ' hτ'1 hτK hDt hk hsize hE hs0 hsv hv1 hK0 hrange h1 h2 h3
      h4 hKN] with n hn1 hn2
  exact ⟨hn1, hn2 (K n) le_rfl⟩

end MergedInputs

end RBM.Ind

end
