/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.NQGood2
import RBM3D.Induction.GridEnvelopeN
import RBM3D.Induction.ContinuityNet

/-!
# The term budgets of the non-alternating assembled bound at the `d ≥ 3` data of S3-10b

Ticket T2179 (S3-11, stochastic layer ST-3).  Port of RBM2D `Induction/NonAltBudget.lean`, sections
1-5b (`NAB:57-839`, commit `c9a24cf`), on the merged S3-10b (`Induction/NQGood2`): the sharp
identity `ρ_{s,t} M_s⁻¹ = M_t⁻¹` of d = 2 is the merged inequality (5.93)
`nqGood2_ratio_mul_Bctl_le` (`scaleM⁻¹ ↦ Bctl`), the kernel weights are `W^{Cε} r^{k-1}` and
`W^C` with `C = nqGood1C` (abstract), the drift level has no additive part, and the budget gains
the `Φ²` term of (D2).
Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`), `lem:STOeq_NQ`
(`3_5:1136`, proof `3_5:1152`), (5.93) (`3_5:1158`).

## Sections (namespace `RBM.Ind`)

1. The vocabulary (the four definitions of the ticket, verbatim): `assembledRHSNonAltN`,
   `nqBudget_qvShape`, `nqBudget_kapFar`, `nqBudget_qvFar`.
2. Elementary facts (public, prefix `nqBudget_`): `nqBudget_im_le_one`, `nqBudget_inv_one_sub_le`,
   `nqBudget_sum_succ_le`, `nqBudget_sqrt_add_le`, `nqBudget_kappa_le_kapFar`.
3. Generic budgets for abstract kernel weights (`B : ℕ → ℝ` the scale sequence): `tbInitN`,
   `tbDriftN`, `tbQvN`.
4. Their instances at the S3-10b data and the budget: `qvBdNonAltN_eq_qvShape`, `tbInitNonAltN`,
   `tbDriftNonAltN`, `tbQvNonAltN`, `budgetNonAltN`.
5. `nqBudget_merged_inputs`: `hlog`, `hR` of `budgetNonAltN` are the conclusions of the merged
   `sum_gridStep_div_etaT_le`, `sum_weighted_stepErrN_le` at `m = K n`.
6. Compiled nonempty instances (namespace `NQBudgetInst`) at `d = 3`, `sz0`, `n = 0`.

## Port map (RBM2D at `c9a24cf`; `NAB` = `Induction/NonAltBudget.lean`)

`assembledRHSNonAlt` `NAB:57` → `assembledRHSNonAltN`; `NonAltBudget_im_le_one` `:77` →
`nqBudget_im_le_one`; `NonAltBudget_inv_one_sub_le` `:105` → `nqBudget_inv_one_sub_le`;
`NonAltBudget_sum_succ_le` `:139` → `nqBudget_sum_succ_le`; `NonAltBudget_sqrt_add_le` `:146` →
`nqBudget_sqrt_add_le`; `NonAltBudget_absorb` `:158` → `nqBudget_absorb` (private); `tbInit` `:173`
→ `tbInitN`; `tbDrift` `:189` → `tbDriftN`; `NonAltBudget_qvShape` `:240` → `nqBudget_qvShape`;
`NonAltBudget_qv_step` `:247` → inlined in `tbQvN`; `tbQv` `:307` → `tbQvN`; `tbInitNonAlt` `:386`
→ `tbInitNonAltN`; `NonAltBudget_far_kappa` `:415` → `nqBudget_kappa_le_kapFar` (the far bound is
`r ≤ (1+g²)(1-u_m)⁻¹ ≤ (1+g²)N`, not `M_j ≤ N`); `tbDriftNonAlt` `:446` → `tbDriftNonAltN`;
`NonAltBudget_qvBdNonAlt_eq_qvShape` `:506` → `qvBdNonAltN_eq_qvShape`; `tbQvNonAlt` `:516` →
`tbQvNonAltN`; `budgetNonAlt` `:587` → `budgetNonAltN`; `NonAltBudget_merged_inputs` `:815` →
`nqBudget_merged_inputs`.
Not ported: `NonAltBudget_far_eps` `:432` (`ε_{i,m} = W^C` is constant at `d ≥ 3`),
`NonAltBudget_scaleM_le`, `_scaleM_le_size`, `_size_eq` (`M_u ≤ N` becomes
`N⁻¹ ≤ B_u`, `cont_inv_size_le_Bctl`), `_cCase1_nonneg`, `_cPair1_nonneg`, `_cKap`, `_aQv` (no such
constants at `d ≥ 3`), and the §6 numerical facts about `cCase1 3 1`, `cPair1 3 1`, `log 3`,
`gridK sizes 28 2`.

Every unpinned helper is `private` or prefixed `nqBudget_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-! ## 1. The vocabulary (the four definitions of the ticket, verbatim) -/

/-- **The right-hand side of the merged `AssembledN` at `m = K n`** with the data of S3-10b
(RBM2D `assembledRHSNonAlt`, `NonAltBudget.lean:57`): `κ = kappaNonAltN`, `εK = epsNonAltN`,
`δ₀ = δ_D = W^{-D'}`, `d_j = dDriftNonAltN(u_j)`, `c = cQVNonAltN`, `stepErr_j = stepErrN` at the
envelope `B_k = N^{τ_K} η_{u_{j+1}}^{-k}`, initial supremum `X0`, Azuma exponent `εq`, `D = D_Y`. -/
def assembledRHSNonAltN {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (Λg κ' ε : ℝ) (Γ Λ Φ : ℕ → ℝ) (D' D'' D_Y τK εq X0 : ℝ) (a : Fin k → Zd d (sz.L n)) : ℝ :=
  kappaNonAltN d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) 0 (K n) * X0 +
    epsNonAltN d k Λg κ' ((sz.W n : ℕ) : ℝ) 0 (K n) * ((sz.W n : ℕ) : ℝ) ^ (-D') +
    gridStep s v K n * ∑ j ∈ Finset.range (K n),
      (kappaNonAltN d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) (j + 1) (K n) *
          dDriftNonAltN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ n) +
        epsNonAltN d k Λg κ' ((sz.W n : ℕ) : ℝ) (j + 1) (K n) * ((sz.W n : ℕ) : ℝ) ^ (-D')) +
    ((sz.size n : ℕ) : ℝ) ^ εq * Real.sqrt (∑ j ∈ Finset.range (K n),
      (cQVNonAltN sz E s v K n k Λg κ' ε Γ Λ D'' (K n) a j : ℝ)) +
    ((sz.size n : ℕ) : ℝ) ^ (-D_Y) +
    ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k *
      stepErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1))
        (gridStep s v K n)
        (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ k)

/-- **The shape of the quadratic-variation majorant** (RBM2D `NonAltBudget_qvShape`,
`NonAltBudget.lean:240`, at `d ≥ 3`): `κ(κ(G B^{2k}/η + Wd) + Ce Wd) + Cc Wd`; `qvBdNonAltN` is the
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

/-- Reindexing the time sum (RBM1D `sum_succ_le`): `Σ_{j<K} f(j+1) ≤ Σ_{j<K} f j + f K` for
`0 ≤ f 0`. -/
theorem nqBudget_sum_succ_le {K : ℕ} (f : ℕ → ℝ) (hf0 : 0 ≤ f 0) :
    ∑ j ∈ Finset.range K, f (j + 1) ≤ ∑ j ∈ Finset.range K, f j + f K := by
  have h := Finset.sum_range_succ' f K
  have h2 := Finset.sum_range_succ f K
  linarith

/-- `√(x + y) ≤ √x + √y` for `x, y ≥ 0` (RBM1D `sqrt_add_le514`). -/
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

/-- **The far bound of the kernel weight** (RBM2D `NonAltBudget_far_kappa`, `:415`, there for
`κ M^{-k} ≤ C_κ M_K^{-k}`): for `0 ≤ u_i ≤ u_m < 1` and `(1-u_m)⁻¹ ≤ N`,
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

/-- **Generic initial term** (RBM2D `tbInit`, `NonAltBudget.lean:173`; RBM1D `tb_init`, `:2863`),
with `(scaleM^k)⁻¹ ↦ B^k`: for weights `κ` with `κ(0,K) B_0^k ≤ C_κ B_K^k` and an initial supremum
`X0 ≤ G B_0^k`, `κ(0,K) X0 ≤ C_κ G B_K^k`. -/
theorem tbInitN {k K : ℕ} {Cκ G X0 : ℝ} (B : ℕ → ℝ) (κ : ℕ → ℕ → ℝ)
    (hκ0 : 0 ≤ κ 0 K) (hG : 0 ≤ G)
    (hker : κ 0 K * B 0 ^ k ≤ Cκ * B K ^ k) (hX0 : X0 ≤ G * B 0 ^ k) :
    κ 0 K * X0 ≤ Cκ * G * B K ^ k := by
  calc κ 0 K * X0 ≤ κ 0 K * (G * B 0 ^ k) := mul_le_mul_of_nonneg_left hX0 hκ0
    _ = G * (κ 0 K * B 0 ^ k) := by ring
    _ ≤ G * (Cκ * B K ^ k) := mul_le_mul_of_nonneg_left hker hG
    _ = _ := by ring

/-- **Generic drift term** (RBM2D `tbDrift`, `NonAltBudget.lean:189`; RBM1D `tb_drift`, `:2539`),
with `(scaleM^k)⁻¹ ↦ B^k`: for weights `κ, ε` with `κ(j+1,K) B_j^k ≤ C_κ B_K^k`,
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

/-- **Generic quadratic-variation term** (RBM2D `tbQv`, `NonAltBudget.lean:307`; RBM1D `tb_qv`,
`:2748`; the proxies are `c_j = Δ k nqBudget_qvShape(κ_j, …, B_{j+1}, η_{u_{j+1}})`): for weights
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

/-! ## 4. The generic budgets at the data of S3-10b, and the budget -/

section Instances

variable {d : ℕ} (sz : Sizes d)

/-- The absorption step of a far part (RBM2D `NonAltBudget_absorb`, `:158`): `y N_p ≤ B`,
`N_p⁻¹ ≤ X`, `B ≥ 0` give `y ≤ B X`. -/
private theorem nqBudget_absorb {y Np B X : ℝ} (hNp : 0 < Np) (hB : 0 ≤ B) (h : y * Np ≤ B)
    (hX : Np⁻¹ ≤ X) : y ≤ B * X := by
  have h1 : y ≤ B * Np⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hNp]; exact h
  exact h1.trans (mul_le_mul_of_nonneg_left hX hB)

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

/-- `K Δ = v - s`. -/
private theorem nqBudget_K_mul_step {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hK : K n ≠ 0) :
    (K n : ℝ) * gridStep s v K n = v n - s n := by
  have hK' : (K n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK
  unfold gridStep
  rw [mul_div_cancel₀ _ hK']

/-- **`qvBdNonAltN` has the shape `nqBudget_qvShape`** with `κ = W^{Cε} r^{k-1}`, `Ce = W^C`,
`Cc = W^C W^k`, `G = Γ(ΓΛ)`, `Wd = W^{-D''}`, `B = B_u`, `η = η_u` (RBM2D
`NonAltBudget_qvBdNonAlt_eq_qvShape`, `:506`). -/
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

/-- **The initial term at the data of S3-10b** (RBM2D `tbInitNonAlt`, `:386`): `κ_{0,K} X0 ≤
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

/-- **The drift term at the data of S3-10b** (RBM2D `tbDriftNonAlt`, `:446`): the drift term of
`assembledRHSNonAltN` is at most `W^{Cε} Γ(ΓΦ)((k-1) + kΓΦ) B_v^k Σ_j Δ/η_{u_j} +
(KΔ)(W^C W^{-D'})` (`dDriftNonAltN = a B_{u_j}^k/η_{u_j}`, `b = 0`; sharp kernel
`kappaNonAltN_succ_mul_Bctl_pow_le`). -/
theorem tbDriftNonAltN {E s v : ℕ → ℝ} {K : ℕ → ℕ} (n k : ℕ) (Λg κ' ε : ℝ) (Γ Φ : ℕ → ℝ)
    (D' : ℝ) (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1)
    (hK : K n ≠ 0) (hk : 1 ≤ k) (hΓ : 0 ≤ Γ n) (hΦ : 0 ≤ Φ n)
    (hη : (etaT (E n) (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) :
    gridStep s v K n * ∑ j ∈ Finset.range (K n),
      (kappaNonAltN d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) (j + 1) (K n) *
          dDriftNonAltN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ n) +
        epsNonAltN d k Λg κ' ((sz.W n : ℕ) : ℝ) (j + 1) (K n) * ((sz.W n : ℕ) : ℝ) ^ (-D')) ≤
      ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
          (Γ n * (Γ n * Φ n) * (((k : ℝ) - 1) + (k : ℝ) * (Γ n * Φ n))) *
          (sz.Bctl n (v n)) ^ k *
          ∑ j ∈ Finset.range (K n), gridStep s v K n / etaT (E n) (gridTime s v K n j) +
        ((K n : ℝ) * gridStep s v K n) *
          (((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' * ((sz.W n : ℕ) : ℝ) ^ (-D')) := by
  have hW : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hu0 : ∀ i, 0 ≤ gridTime s v K n i := fun i => nqBudget_gridTime_nonneg hs0 hsv i
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi =>
    (nqBudget_gridTime_le hsv hK hi).trans_lt hv1
  have huK := gridTime_last s v K n hK
  have hmono : ∀ i m, i ≤ m → gridTime s v K n i ≤ gridTime s v K n m := fun i m him =>
    ST_gridTime_mono s v K n hsv him
  have hΔ0 : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n hsv
  have hN1 : (1 - v n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := nqBudget_inv_one_sub_le hE hv1 hη
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ha0 : 0 ≤ Γ n * (Γ n * Φ n) * (((k : ℝ) - 1) + (k : ℝ) * (Γ n * Φ n)) := by
    have h1 : 0 ≤ ((k : ℝ) - 1) + (k : ℝ) * (Γ n * Φ n) := by
      have : 0 ≤ (k : ℝ) * (Γ n * Φ n) := mul_nonneg (by linarith) (mul_nonneg hΓ hΦ)
      linarith
    exact mul_nonneg (mul_nonneg hΓ (mul_nonneg hΓ hΦ)) h1
  have hsucc : ∀ j < K n, kappaNonAltN d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε
      (gridTime s v K n) (j + 1) (K n) * (sz.Bctl n (gridTime s v K n j)) ^ k ≤
      ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
        (sz.Bctl n (gridTime s v K n (K n))) ^ k := fun j hj =>
    kappaNonAltN_succ_mul_Bctl_pow_le sz n k Λg κ' ε hW (gridTime s v K n) j (K n)
      (hmono j (j + 1) (by omega)) (hmono (j + 1) (K n) (by omega)) (hu1 _ le_rfl)
  have h := tbDriftN (E := E n) (k := k) (K := K n) (Δ := gridStep s v K n)
    (Cκ := ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε))
    (Cε := ((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ')
    (Cfar := nqBudget_kapFar sz n k Λg κ' ε)
    (a := Γ n * (Γ n * Φ n) * (((k : ℝ) - 1) + (k : ℝ) * (Γ n * Φ n))) (b := 0)
    (δmax := ((sz.W n : ℕ) : ℝ) ^ (-D')) (gridTime s v K n)
    (fun i => sz.Bctl n (gridTime s v K n i))
    (kappaNonAltN d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n))
    (epsNonAltN d k Λg κ' ((sz.W n : ℕ) : ℝ))
    (fun j => dDriftNonAltN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ n))
    (fun _ => ((sz.W n : ℕ) : ℝ) ^ (-D')) hΔ0 ha0 le_rfl
    (fun j hj => nonAlt_hκ0N d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε hW (K n) _ (j + 1) (K n)
      (by omega) le_rfl)
    (fun j hj => nonAlt_hε0N d k Λg κ' ((sz.W n : ℕ) : ℝ) hW (K n) (j + 1) (K n) (by omega) le_rfl)
    hsucc
    (fun j hj => nqBudget_kappa_le_kapFar sz n k Λg κ' ε (gridTime s v K n) (hu0 (j + 1))
      (hmono (j + 1) (K n) (by omega)) (hu1 _ le_rfl) (by rw [huK]; exact hN1))
    (fun _ _ => le_rfl)
    (fun j hj => by
      unfold dDriftNonAltN
      rw [add_zero]
      apply le_of_eq
      rw [div_eq_mul_inv]; ring)
    (fun _ _ => Real.rpow_nonneg hW _) (fun _ _ => le_rfl)
    (fun j hj => etaT_pos hE (hu1 j hj.le))
  rw [huK] at h
  simpa only [mul_zero, zero_add] using h

/-- **The quadratic-variation term at the data of S3-10b** (RBM2D `tbQvNonAlt`, `:516`): the sum of
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

/-! ## 4b. The budget `budgetNonAltN` -/

section Budget

/-- The final bookkeeping of the budget on plain reals: the six term bounds
`t₁ ≤ P₀X/6`, `t₂ ≤ P₀X/12`, `t₃ ≤ P₀(Φ+Φ²)X/12 + P₀X/12`, `t₄ ≤ P₀Λ^{1/2}X/12 + P₀X/12`,
`t₅, t₆ ≤ P₀X/6` give `Σ t ≤ P₀ (Λ^{1/2} + Φ + Φ²) X` (coefficients of `Λ^{1/2}X`: `5/6`; of
`ΦX`, `Φ²X`: `1/12`; `X ≤ Λ^{1/2} X` for `Λ^{1/2} ≥ 1`). -/
private theorem nqBudget_final {t1 t2 t3 t4 t5 t6 P0 X Λr Φ : ℝ} (hP0 : 0 ≤ P0) (hX : 0 ≤ X)
    (hΛr : 1 ≤ Λr) (hΦ : 0 ≤ Φ) (T1 : t1 ≤ P0 / 6 * X) (T2 : t2 ≤ P0 / 12 * X)
    (T3 : t3 ≤ P0 / 12 * ((Φ + Φ ^ 2) * X) + P0 / 12 * X)
    (T4 : t4 ≤ P0 / 12 * (Λr * X) + P0 / 12 * X) (T5 : t5 ≤ P0 / 6 * X)
    (T6 : t6 ≤ P0 / 6 * X) :
    t1 + t2 + t3 + t4 + t5 + t6 ≤ P0 * (Λr + Φ + Φ ^ 2) * X := by
  have hPX : P0 * X ≤ P0 * (Λr * X) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hX hΛr) hP0
  have hΦX : 0 ≤ P0 * (Φ * X) := mul_nonneg hP0 (mul_nonneg hΦ hX)
  have hΦ2X : 0 ≤ P0 * (Φ ^ 2 * X) := mul_nonneg hP0 (mul_nonneg (sq_nonneg Φ) hX)
  have e : P0 * (Λr + Φ + Φ ^ 2) * X = P0 * (Λr * X) + P0 * (Φ * X) + P0 * (Φ ^ 2 * X) := by ring
  rw [e]
  nlinarith [T1, T2, T3, T4, T5, T6, hPX, hΦX, hΦ2X]

/-- **The (5.93) budget of the non-alternating endpoint at `d ≥ 3`** (RBM2D `budgetNonAlt`,
`NonAltBudget.lean:587`; RBM1D `budget514`, `:2990`): at a fixed `n`, under explicit numerical
inequalities only, `assembledRHSNonAltN ≤ N^{ε₀} (Λ^{1/2} + Φ + Φ²) B_v^k`.  The `Φ²` is the
`k Γ³ Φ²` part of `dDriftNonAltN` (clause (D2) of `GoodSetN`).

* regime: `hk` (`2 ≤ k`), `hε₁`, `hE` (`|E| < 2`), `hs0`, `hsv`, `hv1`, `hK`, `hη`
  (`η_v⁻¹ ≤ N`), `hΔη` (`Δ η_v⁻¹ ≤ 1`, in place of RBM2D's `Δ N ≤ 1`);
* levels: `hΓ` (`Γ_n = N^{ε₁}`), `hΛ` (`1 ≤ Λ_n`), `hΦ` (`0 ≤ Φ_n`);
* merged inputs, per index `n`: `hlog` (the conclusion of `sum_gridStep_div_etaT_le`), `hX0` (the
  initial datum), `hR` (the conclusion of `sum_weighted_stepErrN_le` at `m = K n`);
* absorption: `ha1`-`ha3` (the three main terms, against `N^{ε₀}/6, /12, /12`) and `he1`-`he4`
  (the four far parts, against `N^{ε₀}/12, /12, /6, /6`); the far parts carry `W^C`
  (`C = nqGood1C`), so `D', D''` are chosen after `C`.  No `L^d ≤ W^K`, no `W ≥ N^𝔠` here: the far
  parts become small only in S3-12 through `Bandwidth`. -/
theorem budgetNonAltN {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (Λg κ' ε : ℝ) (Γ Λ Φ : ℕ → ℝ) (D' D'' D_Y D_t τK εq ε₀ ε₁ X0 : ℝ)
    (a : Fin k → Zd d (sz.L n))
    (hk : 2 ≤ k) (hε₁ : 0 ≤ ε₁) (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n)
    (hv1 : v n < 1) (hK : K n ≠ 0)
    (hη : (etaT (E n) (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ))
    (hΔη : gridStep s v K n * (etaT (E n) (v n))⁻¹ ≤ 1)
    (hΓ : Γ n = ((sz.size n : ℕ) : ℝ) ^ ε₁) (hΛ : 1 ≤ Λ n) (hΦ : 0 ≤ Φ n)
    (hlog : ∑ j ∈ Finset.range (K n), gridStep s v K n / etaT (E n) (gridTime s v K n j) ≤
      (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ))
    (hX0 : X0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ k)
    (hR : ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k *
        stepErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1))
          (gridStep s v K n)
          (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ k) ≤
      ((sz.size n : ℕ) : ℝ) ^ (-D_t))
    (ha1 : ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) * ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6)
    (ha2 : (k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
        (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 3 *
        ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12)
    (ha3 : ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
        ((sz.size n : ℕ) : ℝ) ^ ε₁ *
        Real.sqrt ((k : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1))) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12)
    (he1 : ((sz.size n : ℕ) : ℝ) ^ k *
        (((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' * ((sz.W n : ℕ) : ℝ) ^ (-D')) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12)
    (he2 : ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.size n : ℕ) : ℝ) ^ k *
        Real.sqrt ((k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε * ((sz.W n : ℕ) : ℝ) ^ (-D'')))) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12)
    (he3 : ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-D_Y) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6)
    (he4 : ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-D_t) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6) :
    assembledRHSNonAltN sz E s v K n k Λg κ' ε Γ Λ Φ D' D'' D_Y τK εq X0 a ≤
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
      (ContinuityNet.cont_inv_size_le_Bctl sz n (hs0.trans hsv) hv1) k
  have hP0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ := Real.rpow_nonneg hN0.le _
  have hLs0 : 0 ≤ (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) :=
    mul_nonneg (inv_nonneg.2 (mE_im_pos hE).le) (Real.log_nonneg hN1)
  have hWC0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' := Real.rpow_nonneg hW0 _
  have hWD0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D') := Real.rpow_nonneg hW0 _
  have hWCε0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) :=
    Real.rpow_nonneg hW0 _
  have hΛr1 : 1 ≤ Λ n ^ ((1 : ℝ) / 2) := Real.one_le_rpow hΛ (by norm_num)
  -- the far part `W^C W^{-D'}` is absorbed once (`he1`)
  have hfar : ((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ k :=
    nqBudget_absorb hNk (by positivity) ((mul_comm _ _).trans_le he1) hXN
  -- T1: the initial term
  have T1 : _ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 * (sz.Bctl n (v n)) ^ k :=
    (tbInitNonAltN sz n k Λg κ' ε (((sz.size n : ℕ) : ℝ) ^ ε₁) X0 hs0 hsv hv1 hK
      (Real.rpow_nonneg hN0.le _) hX0).trans (mul_le_mul_of_nonneg_right ha1 hX0')
  -- T2: the initial decay error
  have T2 : epsNonAltN d k Λg κ' ((sz.W n : ℕ) : ℝ) 0 (K n) * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ k := by
    unfold epsNonAltN
    exact hfar
  -- T3: the drift term
  have T3 : gridStep s v K n * ∑ j ∈ Finset.range (K n),
      (kappaNonAltN d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) (j + 1) (K n) *
          dDriftNonAltN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ n) +
        epsNonAltN d k Λg κ' ((sz.W n : ℕ) : ℝ) (j + 1) (K n) * ((sz.W n : ℕ) : ℝ) ^ (-D')) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * ((Φ n + Φ n ^ 2) * (sz.Bctl n (v n)) ^ k) +
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ k := by
    have h := tbDriftNonAltN sz n k Λg κ' ε Γ Φ D' hE hs0 hsv hv1 hK (by omega) hΓ0 hΦ hη
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
    have m1 : ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
          (Γ n * (Γ n * Φ n) * (((k : ℝ) - 1) + (k : ℝ) * (Γ n * Φ n))) *
          (sz.Bctl n (v n)) ^ k *
          ∑ j ∈ Finset.range (K n), gridStep s v K n / etaT (E n) (gridTime s v K n j) ≤
        ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
          (Γ n * (Γ n * Φ n) * (((k : ℝ) - 1) + (k : ℝ) * (Γ n * Φ n))) *
          (sz.Bctl n (v n)) ^ k *
          ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (mul_nonneg (mul_nonneg hWCε0 ha0) hX0')
    have m2 : ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
          (Γ n * (Γ n * Φ n) * (((k : ℝ) - 1) + (k : ℝ) * (Γ n * Φ n))) *
          (sz.Bctl n (v n)) ^ k *
          ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) ≤
        ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
          ((k : ℝ) * Γ n ^ 3 * (Φ n + Φ n ^ 2)) *
          (sz.Bctl n (v n)) ^ k *
          ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha_le hWCε0) hX0') hLs0
    have m3 : ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
          ((k : ℝ) * Γ n ^ 3 * (Φ n + Φ n ^ 2)) *
          (sz.Bctl n (v n)) ^ k *
          ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) =
        ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
          (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 3 *
          ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ))) *
          ((Φ n + Φ n ^ 2) * (sz.Bctl n (v n)) ^ k) := by
      rw [hΓ]; ring
    have m4 : ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
          (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 3 *
          ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ))) *
          ((Φ n + Φ n ^ 2) * (sz.Bctl n (v n)) ^ k) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * ((Φ n + Φ n ^ 2) * (sz.Bctl n (v n)) ^ k) :=
      mul_le_mul_of_nonneg_right ha2 (mul_nonneg (by positivity) hX0')
    have f1 : ((K n : ℝ) * gridStep s v K n) *
          (((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' * ((sz.W n : ℕ) : ℝ) ^ (-D')) ≤
        ((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' * ((sz.W n : ℕ) : ℝ) ^ (-D') :=
      (mul_le_mul_of_nonneg_right hKΔ1 (mul_nonneg hWC0 hWD0)).trans_eq (one_mul _)
    exact add_le_add (m1.trans (m2.trans (m3.le.trans m4))) (f1.trans hfar)
  -- T4: the quadratic-variation term
  have T4 : ((sz.size n : ℕ) : ℝ) ^ εq * Real.sqrt (∑ j ∈ Finset.range (K n),
      (cQVNonAltN sz E s v K n k Λg κ' ε Γ Λ D'' (K n) a j : ℝ)) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (Λ n ^ ((1 : ℝ) / 2) * (sz.Bctl n (v n)) ^ k) +
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ k := by
    have h := tbQvNonAltN sz n k Λg κ' ε Γ Λ D'' a hE hs0 hsv hv1 hK hΛ0 hη
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
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hQe0 : 0 ≤ (k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε * ((sz.W n : ℕ) : ℝ) ^ (-D'')) := by
      have hq : 0 ≤ nqBudget_qvFar sz n k Λg κ' ε := by
        unfold nqBudget_qvFar nqBudget_kapFar
        have hr : 0 ≤ (1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ) := by positivity
        have h1 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
            ((1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ)) ^ (k - 1) := by positivity
        have h2 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ k := by positivity
        have h3 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' := hWC0
        positivity
      positivity
    have hΓX : 0 ≤ Γ n * (sz.Bctl n (v n)) ^ k := mul_nonneg hΓ0 hX0'
    have hZ0 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
        (Γ n * (sz.Bctl n (v n)) ^ k)) ^ 2 * ((k : ℝ) * (
        (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) * Λ n) := by
      have : 0 ≤ (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1 := by linarith
      positivity
    have hsum : ∑ j ∈ Finset.range (K n),
        (cQVNonAltN sz E s v K n k Λg κ' ε Γ Λ D'' (K n) a j : ℝ) ≤
        (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) * (Γ n * (sz.Bctl n (v n)) ^ k)) ^ 2 *
          ((k : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) * Λ n) +
        (k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε * ((sz.W n : ℕ) : ℝ) ^ (-D'')) := by
      refine h.trans ?_
      have hc0 : 0 ≤ (k : ℝ) * (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε)) ^ 2 *
          (Γ n * (Γ n * Λ n)) * ((sz.Bctl n (v n)) ^ k) ^ 2 := by
        have : Γ n * (Γ n * Λ n) = Γ n ^ 2 * Λ n := by ring
        rw [this]; positivity
      have n1 := mul_le_mul_of_nonneg_left hSv hc0
      have n2 : ((K n : ℝ) * gridStep s v K n) *
          ((k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε * ((sz.W n : ℕ) : ℝ) ^ (-D''))) ≤
          (k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε * ((sz.W n : ℕ) : ℝ) ^ (-D'')) :=
        (mul_le_mul_of_nonneg_right hKΔ1 hQe0).trans_eq (one_mul _)
      have e : (k : ℝ) * (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε)) ^ 2 *
            (Γ n * (Γ n * Λ n)) * ((sz.Bctl n (v n)) ^ k) ^ 2 *
            ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) =
          (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) * (Γ n * (sz.Bctl n (v n)) ^ k)) ^ 2 *
            ((k : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) * Λ n) := by ring
      linarith
    have hs1 := Real.sqrt_le_sqrt hsum
    have hs2 : Real.sqrt ((((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
          (Γ n * (sz.Bctl n (v n)) ^ k)) ^ 2 *
          ((k : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) * Λ n) +
        (k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε * ((sz.W n : ℕ) : ℝ) ^ (-D''))) ≤
        ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) * (Γ n * (sz.Bctl n (v n)) ^ k) *
          (Real.sqrt ((k : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)) *
            Real.sqrt (Λ n)) +
        Real.sqrt ((k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε * ((sz.W n : ℕ) : ℝ) ^ (-D''))) := by
      refine (nqBudget_sqrt_add_le hZ0 hQe0).trans ?_
      have hA0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
          (Γ n * (sz.Bctl n (v n)) ^ k) := mul_nonneg hWCε0 hΓX
      have hP00 : 0 ≤ (k : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) :=
        mul_nonneg hk0 (by linarith)
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hA0, Real.sqrt_mul hP00]
    have hsΛ : Real.sqrt (Λ n) = Λ n ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow (Λ n)
    have hNe : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ εq := Real.rpow_nonneg hN0.le _
    have k1 : ((sz.size n : ℕ) : ℝ) ^ εq *
        (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) * (Γ n * (sz.Bctl n (v n)) ^ k) *
          (Real.sqrt ((k : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)) *
            Real.sqrt (Λ n))) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (Λ n ^ ((1 : ℝ) / 2) * (sz.Bctl n (v n)) ^ k) := by
      have e : ((sz.size n : ℕ) : ℝ) ^ εq *
          (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) * (Γ n * (sz.Bctl n (v n)) ^ k) *
            (Real.sqrt ((k : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)) *
              Real.sqrt (Λ n))) =
          (((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
            ((sz.size n : ℕ) : ℝ) ^ ε₁ *
            Real.sqrt ((k : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)))) *
          (Λ n ^ ((1 : ℝ) / 2) * (sz.Bctl n (v n)) ^ k) := by
        rw [hsΛ, hΓ]; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right ha3 (mul_nonneg (by linarith) hX0')
    have k2 : ((sz.size n : ℕ) : ℝ) ^ εq *
        Real.sqrt ((k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε * ((sz.W n : ℕ) : ℝ) ^ (-D''))) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ k := by
      refine nqBudget_absorb hNk (by positivity) ?_ hXN
      have e : ((sz.size n : ℕ) : ℝ) ^ εq *
          Real.sqrt ((k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε * ((sz.W n : ℕ) : ℝ) ^ (-D''))) *
            ((sz.size n : ℕ) : ℝ) ^ k =
          ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.size n : ℕ) : ℝ) ^ k *
            Real.sqrt ((k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε *
              ((sz.W n : ℕ) : ℝ) ^ (-D'')))) := by ring
      rw [e]; exact he2
    calc ((sz.size n : ℕ) : ℝ) ^ εq * Real.sqrt (∑ j ∈ Finset.range (K n),
          (cQVNonAltN sz E s v K n k Λg κ' ε Γ Λ D'' (K n) a j : ℝ))
        ≤ ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
            (Γ n * (sz.Bctl n (v n)) ^ k) *
            (Real.sqrt ((k : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)) *
              Real.sqrt (Λ n)) +
          Real.sqrt ((k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε * ((sz.W n : ℕ) : ℝ) ^ (-D'')))) :=
          mul_le_mul_of_nonneg_left (hs1.trans hs2) hNe
      _ = ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
            (Γ n * (sz.Bctl n (v n)) ^ k) *
            (Real.sqrt ((k : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)) *
              Real.sqrt (Λ n))) +
          ((sz.size n : ℕ) : ℝ) ^ εq *
            Real.sqrt ((k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε *
              ((sz.W n : ℕ) : ℝ) ^ (-D''))) := by ring
      _ ≤ _ := add_le_add k1 k2
  -- T5, T6
  have T5 : ((sz.size n : ℕ) : ℝ) ^ (-D_Y) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 * (sz.Bctl n (v n)) ^ k :=
    nqBudget_absorb hNk (by positivity) ((mul_comm _ _).trans_le he3) hXN
  have T6 : _ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 * (sz.Bctl n (v n)) ^ k :=
    hR.trans (nqBudget_absorb hNk (by positivity) ((mul_comm _ _).trans_le he4) hXN)
  unfold assembledRHSNonAltN
  exact nqBudget_final hP0 hX0' hΛr1 hΦ T1 T2 T3 T4 T5 T6

end Budget

/-! ## 5. The merged inputs `hlog`, `hR` are the conclusions of merged theorems

`hlog` and `hR` of `budgetNonAltN` are, at each `n`, exactly the conclusions of the merged
`sum_gridStep_div_etaT_le` and `sum_weighted_stepErrN_le` (at `m = K n`): the theorem below is the
compiled interface for S3-12 (the side conditions are those of the two merged theorems). -/

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

/-! ## 6. Compiled nonempty instances at `d = 3`

Data (the merged instance data of `GridGoodN` §7, `AzumaProxyN` §6, `NQGood1` §6, `NQGood2` §5):
`sz0` (`n = 0`: `L = 4`, `W = 32`, `N = 2^21`, `lam = 1/64`), `E ≡ 1/2` (`Im m = √15/4 ≈ 0.968`),
`s ≡ 0`, `v ≡ 1/32`, `K ≡ 4` (`Δ = 1/128`, `u_j = j/128`), `k = 3`, `Λ_g = 10`, `κ' = 1/2`,
`ε = 4/5`, levels `(Γ, Λ, Φ) = (4, 3, 1)`, `D' = 6`, `D'' = 5`, label `aFar`.  The constant
`C = nqGood1C 3 3 10 (1/2)` stays abstract (only `C > 0` is known), so every instance holds for the
actual `C`; the exponent `ε₀ = C + 12` of the budget is chosen so that all seven absorption
inequalities hold for every `C > 0` (the left sides grow at most like `2^{5C}` against `2^{21C}`).
Part (a): the three generic budgets with constant weights.  Part (b): targets 2 and 4 (except the
budget) at the S3-10b data.  Part (c): `budgetNonAltN`, every hypothesis discharged (`hlog`, `hR`
included).  Part (d): `nqBudget_merged_inputs` at the data of `GridEnvelopeNCheck`. -/

namespace NQBudgetInst

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.GridGoodNInst
  RBM.Ind.AzumaProxyNInst RBM.Ind.NQGood1Inst RBM.Ind.NQGood2Inst

private theorem W0 : ((sz0.W 0 : ℕ) : ℝ) = 32 := by rw [sz0_values.2.1]; norm_num

private theorem lam0 : sz0.lam 0 = 1 / 64 := sz0_values.2.2.2

private theorem N0 : ((sz0.size 0 : ℕ) : ℝ) = 2097152 := by rw [sz0_values.2.2.1]; norm_num

private theorem abs_half : |(1 / 2 : ℝ)| < 2 := by norm_num [abs_of_pos]

private theorem im_ge : (24 / 25 : ℝ) ≤ (mE (1 / 2)).im := by
  rw [mE_im]
  have : (48 / 25 : ℝ) ≤ Real.sqrt (4 - (1 / 2) ^ 2) := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num
  linarith

private theorem im_le : (mE (1 / 2)).im ≤ 1 := nqBudget_im_le_one _

private theorem u_le (j : ℕ) (hj : j ≤ 4) : gridTime sInst vg Kg 0 j ≤ 1 / 32 := by
  rw [gridTime_inst]
  have : (j : ℝ) ≤ 4 := by exact_mod_cast hj
  linarith

private theorem u_nonneg (j : ℕ) : 0 ≤ gridTime sInst vg Kg 0 j := by
  rw [gridTime_inst]; positivity

private theorem u_lt_one (j : ℕ) (hj : j ≤ 4) : gridTime sInst vg Kg 0 j < 1 :=
  (u_le j hj).trans_lt (by norm_num)

private theorem u_mono (i m : ℕ) (him : i ≤ m) :
    gridTime sInst vg Kg 0 i ≤ gridTime sInst vg Kg 0 m := by
  rw [gridTime_inst, gridTime_inst]
  have : (i : ℝ) ≤ m := by exact_mod_cast him
  linarith

/-- `η_t⁻¹ ≤ 11/10` for `0 ≤ t ≤ 1/32` at `E = 1/2`. -/
private theorem eta_inv_le {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 32) :
    (etaT (1 / 2) t)⁻¹ ≤ 11 / 10 := by
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

/-- The scale sequence `B_i = W^{-d} B_{u_i,0}` of the grid at `n = 0`. -/
private def Bseq (i : ℕ) : ℝ := sz0.Bctl 0 (gridTime sInst vg Kg 0 i)

private theorem Bseq_pos (i : ℕ) (hi : i ≤ 4) : 0 < Bseq i :=
  Sizes.STBctl_pos sz0 0 (u_lt_one i hi)

private theorem Bseq_mono (i m : ℕ) (him : i ≤ m) (hm : m ≤ 4) : Bseq i ≤ Bseq m :=
  Sizes.STBctl_mono sz0 0 (u_mono i m him) (u_lt_one m hm)

private theorem eta_pos' (j : ℕ) (hj : j ≤ 4) : 0 < etaT (1 / 2) (gridTime sInst vg Kg 0 j) :=
  etaT_pos abs_half (u_lt_one j hj)

/-! ### (a) The three generic budgets, constant weights `κ ≡ 2`, `ε ≡ 1`, at
`u = gridTime sInst vg Kg 0` and `B i = sz0.Bctl 0 (u i)` -/

/-- Instance of `tbInitN`: `K = 4`, `κ ≡ 2`, `C_κ = 2`, `G = 3`, `X0 = 3 B_0^3`. -/
theorem tbInitN_instance :
    (2 : ℝ) * (3 * Bseq 0 ^ 3) ≤ 2 * 3 * Bseq 4 ^ 3 :=
  tbInitN (k := 3) (K := 4) (Cκ := 2) (G := 3) (X0 := 3 * Bseq 0 ^ 3) Bseq (fun _ _ => 2)
    (by norm_num) (by norm_num)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Bseq_pos 0 (by norm_num)).le
      (Bseq_mono 0 4 (by norm_num) le_rfl) 3) (by norm_num))
    le_rfl

/-- Instance of `tbDriftN`: `E = 1/2`, `Δ = 1/128`, `K = 4`, `κ ≡ 2`, `ε ≡ 1`, `C_κ = C_far = 2`,
`C_ε = 1`, `a = 1`, `b = δ = δ_max = 1/2`, `d_j = B_j^3/η_{u_j}`. -/
theorem tbDriftN_instance :
    (1 / 128 : ℝ) * ∑ j ∈ Finset.range 4,
        (2 * (Bseq j ^ 3 / etaT (1 / 2) (gridTime sInst vg Kg 0 j)) + 1 * (1 / 2)) ≤
      2 * 1 * Bseq 4 ^ 3 * ∑ j ∈ Finset.range 4,
          (1 / 128 : ℝ) / etaT (1 / 2) (gridTime sInst vg Kg 0 j) +
        ((4 : ℕ) * (1 / 128 : ℝ)) * (2 * (1 / 2) + 1 * (1 / 2)) :=
  tbDriftN (E := 1 / 2) (k := 3) (K := 4) (Δ := 1 / 128) (Cκ := 2) (Cε := 1) (Cfar := 2)
    (a := 1) (b := 1 / 2) (δmax := 1 / 2) (gridTime sInst vg Kg 0) Bseq (fun _ _ => 2)
    (fun _ _ => 1) (fun j => Bseq j ^ 3 / etaT (1 / 2) (gridTime sInst vg Kg 0 j))
    (fun _ => 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    (fun j hj => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Bseq_pos j (by omega)).le
      (Bseq_mono j 4 (by omega) le_rfl) 3) (by norm_num))
    (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun j hj => by simp only [one_mul]; linarith)
    (fun _ _ => by norm_num) (fun _ _ => le_rfl) (fun j hj => eta_pos' j (by omega))

/-- Instance of `tbQvN`: `E = 1/2`, `Δ = 1/128`, `K = 4`, `k = 3`, `κ ≡ 2`, `C_κ = C_far = 2`,
`C_e = C_c = 1`, `G = 3`, `Wd = 1/2`. -/
theorem tbQvN_instance :
    ∑ j ∈ Finset.range 4, (1 / 128 : ℝ) * (((3 : ℕ) : ℝ) * nqBudget_qvShape 3 2 1 1 3 (1 / 2)
        (Bseq (j + 1)) (etaT (1 / 2) (gridTime sInst vg Kg 0 (j + 1)))) ≤
      ((3 : ℕ) : ℝ) * 2 ^ 2 * 3 * (Bseq 4 ^ 3) ^ 2 * ∑ j ∈ Finset.range 4,
          (1 / 128 : ℝ) / etaT (1 / 2) (gridTime sInst vg Kg 0 (j + 1)) +
        (((4 : ℕ) : ℝ) * (1 / 128)) * (((3 : ℕ) : ℝ) * ((2 * (2 + 1) + 1) * (1 / 2))) :=
  tbQvN (E := 1 / 2) (k := 3) (K := 4) (Cκ := 2) (Cfar := 2) (Ce := 1) (Cc := 1) (G := 3)
    (Wd := 1 / 2) (Δ := 1 / 128) (gridTime sInst vg Kg 0) Bseq (fun _ => 2)
    (fun j hj => (Bseq_pos (j + 1) (by omega)).le) (fun _ _ => by norm_num)
    (fun j hj => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Bseq_pos (j + 1) (by omega)).le
      (Bseq_mono (j + 1) 4 (by omega) le_rfl) 3) (by norm_num))
    (fun _ _ => le_rfl) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun j hj => eta_pos' (j + 1) (by omega))

/-! ### (b) Targets 2 and 4 (except the budget) at the data of S3-10b -/

/-- `nqBudget_im_le_one` at `E = 1/2`. -/
example : (mE (1 / 2)).im ≤ 1 := nqBudget_im_le_one (1 / 2)

/-- `nqBudget_inv_one_sub_le` at `E = 1/2`, `v = 1/32`, `N = 2^21`: `(1 - v)⁻¹ ≤ N`. -/
example : (1 - (1 / 32 : ℝ))⁻¹ ≤ 2097152 :=
  nqBudget_inv_one_sub_le (E := 1 / 2) abs_half (by norm_num : (1 / 32 : ℝ) < 1)
    (by
      have h := eta_inv_le (t := 1 / 32) (by norm_num) le_rfl
      linarith)

/-- `nqBudget_sum_succ_le` for `f j = Δ/η_{u_j}` on the grid, `K = 4`. -/
example : ∑ j ∈ Finset.range 4, (1 / 128 : ℝ) / etaT (1 / 2) (gridTime sInst vg Kg 0 (j + 1)) ≤
    ∑ j ∈ Finset.range 4, (1 / 128 : ℝ) / etaT (1 / 2) (gridTime sInst vg Kg 0 j) +
      (1 / 128 : ℝ) / etaT (1 / 2) (gridTime sInst vg Kg 0 4) :=
  nqBudget_sum_succ_le (K := 4) (fun j => (1 / 128 : ℝ) / etaT (1 / 2) (gridTime sInst vg Kg 0 j))
    (div_nonneg (by norm_num) (eta_pos' 0 (by norm_num)).le)

/-- `nqBudget_sqrt_add_le` at `x = 1`, `y = 3`. -/
example : Real.sqrt (1 + 3) ≤ Real.sqrt 1 + Real.sqrt 3 :=
  nqBudget_sqrt_add_le (by norm_num) (by norm_num)

/-- `nqBudget_kappa_le_kapFar` at `sz0`, `n = 0`, `i = 1`, `m = 4` on the grid. -/
example : kappaNonAltN 3 3 10 (1 / 2) (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (4 / 5)
      (gridTime sInst vg Kg 0) 1 4 ≤ nqBudget_kapFar sz0 0 3 10 (1 / 2) (4 / 5) :=
  nqBudget_kappa_le_kapFar sz0 0 3 10 (1 / 2) (4 / 5) (gridTime sInst vg Kg 0)
    (i := 1) (m := 4) (u_nonneg 1) (u_mono 1 4 (by norm_num)) (u_lt_one 4 le_rfl)
    (by
      have h := nqBudget_inv_one_sub_le (E := 1 / 2) abs_half (u_lt_one 4 le_rfl)
        (Nn := 2097152)
        (by
          have h := eta_inv_le (t := gridTime sInst vg Kg 0 4) (u_nonneg 4) (u_le 4 le_rfl)
          linarith)
      rw [N0]; exact h)

/-- `qvBdNonAltN_eq_qvShape` at `sz0`, `n = 0`, `E = 1/2`, `k = 3`, `Λ_g = 10`, `κ' = 1/2`,
`ε = 4/5`, `(Γ, Λ) = (4, 3)`, `D'' = 5`, `(u, w) = (u_1, u_4)`. -/
example : qvBdNonAltN sz0 0 (1 / 2) 3 10 (1 / 2) (4 / 5) 4 3 5 (gridTime sInst vg Kg 0 1)
      (gridTime sInst vg Kg 0 4) =
    nqBudget_qvShape 3
      (((sz0.W 0 : ℕ) : ℝ) ^ (nqGood1C 3 3 10 (1 / 2) * (4 / 5)) *
        ((sz0.lam 0 ^ 2 + |1 - gridTime sInst vg Kg 0 1|) /
          (sz0.lam 0 ^ 2 + |1 - gridTime sInst vg Kg 0 4|)) ^ (3 - 1))
      (((sz0.W 0 : ℕ) : ℝ) ^ nqGood1C 3 3 10 (1 / 2))
      (((sz0.W 0 : ℕ) : ℝ) ^ nqGood1C 3 3 10 (1 / 2) * ((sz0.W 0 : ℕ) : ℝ) ^ 3)
      (4 * (4 * 3)) (((sz0.W 0 : ℕ) : ℝ) ^ (-(5 : ℝ))) (sz0.Bctl 0 (gridTime sInst vg Kg 0 1))
      (etaT (1 / 2) (gridTime sInst vg Kg 0 1)) :=
  qvBdNonAltN_eq_qvShape sz0 0 3 (1 / 2) 10 (1 / 2) (4 / 5) 4 3 5 _ _

/-- `tbInitNonAltN` at the data: `G = 4`, `X0 = 4 B_0^3`. -/
example :
    kappaNonAltN 3 3 10 (1 / 2) (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (4 / 5)
        (gridTime sInst vg Kg 0) 0 (Kg 0) * (4 * (sz0.Bctl 0 (sInst 0)) ^ 3) ≤
      ((sz0.W 0 : ℕ) : ℝ) ^ (nqGood1C 3 3 10 (1 / 2) * (4 / 5)) * 4 *
        (sz0.Bctl 0 (vg 0)) ^ 3 :=
  tbInitNonAltN sz0 (s := sInst) (v := vg) (K := Kg) 0 3 10 (1 / 2) (4 / 5) 4
    (4 * (sz0.Bctl 0 (sInst 0)) ^ 3) (by norm_num [sInst]) (by norm_num [sInst, vg])
    (by norm_num [vg]) (by norm_num [Kg]) (by norm_num) le_rfl

/-- `tbDriftNonAltN` at the data: levels `(Γ, Φ) = (4, 1)`, `D' = 6`. -/
example :
    gridStep sInst vg Kg 0 * ∑ j ∈ Finset.range (Kg 0),
      (kappaNonAltN 3 3 10 (1 / 2) (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (4 / 5)
          (gridTime sInst vg Kg 0) (j + 1) (Kg 0) *
          dDriftNonAltN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 j) 3 (Γ4 0) (Φ1 0) +
        epsNonAltN 3 3 10 (1 / 2) ((sz0.W 0 : ℕ) : ℝ) (j + 1) (Kg 0) *
          ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ))) ≤
      ((sz0.W 0 : ℕ) : ℝ) ^ (nqGood1C 3 3 10 (1 / 2) * (4 / 5)) *
          (Γ4 0 * (Γ4 0 * Φ1 0) * (((3 : ℕ) : ℝ) - 1 + ((3 : ℕ) : ℝ) * (Γ4 0 * Φ1 0))) *
          (sz0.Bctl 0 (vg 0)) ^ 3 *
          ∑ j ∈ Finset.range (Kg 0), gridStep sInst vg Kg 0 /
            etaT (Einst 0) (gridTime sInst vg Kg 0 j) +
        ((Kg 0 : ℕ) * gridStep sInst vg Kg 0) *
          (((sz0.W 0 : ℕ) : ℝ) ^ nqGood1C 3 3 10 (1 / 2) * ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ))) :=
  tbDriftNonAltN sz0 (E := Einst) (s := sInst) (v := vg) (K := Kg) 0 3 10 (1 / 2) (4 / 5) Γ4 Φ1 6
    (Einst_abs_lt 0) (by norm_num [sInst]) (by norm_num [sInst, vg]) (by norm_num [vg])
    (by norm_num [Kg]) (by norm_num) (by norm_num [Γ4]) (by norm_num [Φ1]) eta_inv_le_N

/-- `tbQvNonAltN` at the data: levels `(Γ, Λ) = (4, 3)`, `D'' = 5`, label `aFar`. -/
example :
    ∑ j ∈ Finset.range (Kg 0), (cQVNonAltN sz0 Einst sInst vg Kg 0 3 10 (1 / 2) (4 / 5) Γ4 Λ3 5
        (Kg 0) aFar j : ℝ) ≤
      ((3 : ℕ) : ℝ) * (((sz0.W 0 : ℕ) : ℝ) ^ (nqGood1C 3 3 10 (1 / 2) * (4 / 5))) ^ 2 *
          (Γ4 0 * (Γ4 0 * Λ3 0)) * ((sz0.Bctl 0 (vg 0)) ^ 3) ^ 2 *
          ∑ j ∈ Finset.range (Kg 0),
            gridStep sInst vg Kg 0 / etaT (Einst 0) (gridTime sInst vg Kg 0 (j + 1)) +
        ((Kg 0 : ℕ) * gridStep sInst vg Kg 0) *
          (((3 : ℕ) : ℝ) * (nqBudget_qvFar sz0 0 3 10 (1 / 2) (4 / 5) *
            ((sz0.W 0 : ℕ) : ℝ) ^ (-(5 : ℝ)))) :=
  tbQvNonAltN sz0 (E := Einst) (s := sInst) (v := vg) (K := Kg) 0 3 10 (1 / 2) (4 / 5) Γ4 Λ3 5
    aFar (Einst_abs_lt 0) (by norm_num [sInst]) (by norm_num [sInst, vg]) (by norm_num [vg])
    (by norm_num [Kg]) (by norm_num [Λ3]) eta_inv_le_N

/-! ### (c) `budgetNonAltN` at the data: grid facts, powers of `2`, `hR`, `hlog`, `ha1`-`he4` -/

private theorem Kg0 : Kg 0 = 4 := rfl

private theorem u4 : gridTime sInst vg Kg 0 4 = 1 / 32 := by
  rw [gridTime_inst]; norm_num

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

private theorem W_eps (C : ℝ) : ((sz0.W 0 : ℕ) : ℝ) ^ (C * (4 / 5)) = ((2 : ℝ) ^ C) ^ 4 := by
  rw [W_rpow, show (5 : ℝ) * (C * (4 / 5)) = ((4 : ℕ) : ℝ) * C by push_cast; ring, two_rpow_nat_mul]

private theorem W_C (C : ℝ) : ((sz0.W 0 : ℕ) : ℝ) ^ C = ((2 : ℝ) ^ C) ^ 5 := by
  rw [W_rpow, show (5 : ℝ) * C = ((5 : ℕ) : ℝ) * C by push_cast; ring, two_rpow_nat_mul]

private theorem N_eps0 (C : ℝ) :
    ((sz0.size 0 : ℕ) : ℝ) ^ (C + 12) = ((2 : ℝ) ^ C) ^ 21 * 2 ^ 252 := by
  rw [N_rpow, show (21 : ℝ) * (C + 12) = ((21 : ℕ) : ℝ) * C + ((252 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_add (by norm_num), two_rpow_nat_mul, Real.rpow_natCast]

private theorem N_eps1 : ((sz0.size 0 : ℕ) : ℝ) ^ ((2 : ℝ) / 21) = 4 := by
  rw [N_rpow, show (21 : ℝ) * (2 / 21) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num

private theorem N_tauK : ((sz0.size 0 : ℕ) : ℝ) ^ ((1 : ℝ) / 21) = 2 := by
  rw [N_rpow, show (21 : ℝ) * (1 / 21) = 1 by norm_num, Real.rpow_one]

private theorem N_one : ((sz0.size 0 : ℕ) : ℝ) ^ (1 : ℝ) = 2097152 := by
  rw [Real.rpow_one, N0]

private theorem N_negone : ((sz0.size 0 : ℕ) : ℝ) ^ (-(1 : ℝ)) = 2097152⁻¹ := by
  rw [Real.rpow_neg_one, N0]

private theorem N_five : ((sz0.size 0 : ℕ) : ℝ) ^ (-(-5 : ℝ)) = 2097152 ^ 5 := by
  rw [neg_neg, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, N0]

private theorem W_neg (m : ℕ) : ((sz0.W 0 : ℕ) : ℝ) ^ (-(m : ℝ)) = ((32 : ℝ) ^ m)⁻¹ := by
  rw [Real.rpow_neg (by rw [W0]; norm_num), Real.rpow_natCast, W0]

private theorem log_N : Real.log ((sz0.size 0 : ℕ) : ℝ) = 21 * Real.log 2 := by
  rw [N0, show (2097152 : ℝ) = 2 ^ 21 by norm_num, Real.log_pow]; norm_num

private theorem Ls_bounds :
    14 ≤ (mE (Einst 0)).im⁻¹ * Real.log ((sz0.size 0 : ℕ) : ℝ) ∧
      (mE (Einst 0)).im⁻¹ * Real.log ((sz0.size 0 : ℕ) : ℝ) ≤ 16 := by
  have e : Einst 0 = 1 / 2 := rfl
  rw [e, log_N]
  have hpos : 0 < (mE (1 / 2)).im := mE_im_pos abs_half
  have h1 : 1 ≤ (mE (1 / 2)).im⁻¹ := (one_le_inv₀ hpos).2 im_le
  have h2 : (mE (1 / 2)).im⁻¹ ≤ 25 / 24 := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]; linarith [im_ge]
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  constructor
  · nlinarith
  · nlinarith


/-! ### `hR` at the data -/

private theorem rpow_three_halves : ((1 : ℝ) / 128) ^ ((3 : ℝ) / 2) ≤ 1 / 1408 := by
  have h : ((1 : ℝ) / 128) ^ ((3 : ℝ) / 2) = (1 / 128) * Real.sqrt (1 / 128) := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  rw [h]
  have : Real.sqrt (1 / 128) ≤ 1 / 11 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  nlinarith [Real.sqrt_nonneg (1 / 128 : ℝ)]

private theorem uStepC_le_one {v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ 1 / 32) : uStepC 3 (1 / 128) v ≤ 1 := by
  unfold uStepC
  have hpos : 0 < 1 - v := by linarith
  have hy1 : (1 - v)⁻¹ ≤ 32 / 31 := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]; linarith
  have hy0 : 0 ≤ (1 - v)⁻¹ := inv_nonneg.2 hpos.le
  generalize (1 - v)⁻¹ = y at hy1 hy0 ⊢
  simp only [Nat.cast_ofNat]
  have hw0 : 0 ≤ (1 / 128 : ℝ) * y := by positivity
  have hw1 : (1 / 128 : ℝ) * y ≤ 1 / 100 := by nlinarith
  have e : 3 * (1 / 128 : ℝ) ^ 2 * y ^ 2 + ((1 + (1 / 128) * y) ^ 3 - 1 - 3 * (1 / 128) * y) =
      6 * ((1 / 128 : ℝ) * y) ^ 2 + ((1 / 128 : ℝ) * y) ^ 3 := by ring
  rw [e]
  have h2 := pow_le_pow_left₀ hw0 hw1 2
  have h3 := pow_le_pow_left₀ hw0 hw1 3
  norm_num at h2 h3
  linarith

private theorem kStepC_le {Bk : ℝ} (h0 : 0 ≤ Bk) (h3 : Bk ≤ 3) :
    kStepC 3 4 32 3 Bk ≤ kStepC 3 4 32 3 3 := by
  unfold kStepC
  gcongr


/-- One step error at the data: `stepErrN` at `(L, W) = (4, 32)`, `E = 1/2`, `k = 3`, `Δ = 1/128`,
`B_k = N^{1/21} η_v⁻³ = 2 η_v⁻³` is at most `SE` for `0 ≤ u ≤ v ≤ 1/32`. -/
private theorem stepErr_le {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1 / 32) :
    stepErrN 3 4 32 (1 / 2) 3 u v (1 / 128) (2 * (etaT (1 / 2) v) ⁻¹ ^ 3) ≤
      16 * 6 ^ 4 * 2097152 ^ 4 * (21 / 10) ^ 7 * (1 / 1408) +
        kStepC 3 4 32 3 3 * (1 / 128) ^ 2 + 5 := by
  have hv0 : 0 ≤ v := hu0.trans huv
  have hq0 : 0 ≤ (etaT (1 / 2) v)⁻¹ := inv_nonneg.2 (etaT_pos abs_half (by linarith)).le
  have hq := eta_inv_le hv0 hv
  have hr0 : 0 ≤ (etaT (1 / 2) u)⁻¹ := inv_nonneg.2 (etaT_pos abs_half (by linarith)).le
  have hr := eta_inv_le hu0 (huv.trans hv)
  have hE : envConst 3 4 32 (1 / 2) 3 v ≤ 16 * 6 ^ 4 * 2097152 ^ 4 * (21 / 10) ^ 7 := by
    unfold envConst
    have h1 : (1 + (etaT (1 / 2) v)⁻¹) ^ (3 + 4) ≤ (21 / 10) ^ 7 :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    norm_num at h1 ⊢
    linarith
  have hΔ32 := rpow_three_halves
  have hΔ0 : (0 : ℝ) ≤ ((1 : ℝ) / 128) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hA : envConst 3 4 32 (1 / 2) 3 v * ((1 : ℝ) / 128) ^ ((3 : ℝ) / 2) ≤
      16 * 6 ^ 4 * 2097152 ^ 4 * (21 / 10) ^ 7 * (1 / 1408) :=
    mul_le_mul hE hΔ32 hΔ0 (by norm_num)
  have hBk0 : 0 ≤ 2 * (etaT (1 / 2) v)⁻¹ ^ 3 := by positivity
  have hBk3 : 2 * (etaT (1 / 2) v)⁻¹ ^ 3 ≤ 3 := by
    have h := pow_le_pow_left₀ hq0 hq 3
    rw [show ((11 : ℝ) / 10) ^ 3 = 1331 / 1000 by norm_num] at h
    linarith
  have hB : kStepC 3 4 32 3 (2 * (etaT (1 / 2) v)⁻¹ ^ 3) * (1 / 128) ^ 2 ≤
      kStepC 3 4 32 3 3 * (1 / 128) ^ 2 :=
    mul_le_mul_of_nonneg_right (kStepC_le hBk0 hBk3) (by norm_num)
  have hU := uStepC_le_one hv0 hv
  have hbr0 : 0 ≤ (etaT (1 / 2) u)⁻¹ ^ 3 * (((32 : ℕ) : ℝ) ^ 3)⁻¹ ^ (3 - 1) +
      2 * (etaT (1 / 2) v)⁻¹ ^ 3 := by positivity
  have hbr : (etaT (1 / 2) u)⁻¹ ^ 3 * (((32 : ℕ) : ℝ) ^ 3)⁻¹ ^ (3 - 1) +
      2 * (etaT (1 / 2) v)⁻¹ ^ 3 ≤ 5 := by
    have h1 := pow_le_pow_left₀ hr0 hr 3
    have h2 : (((32 : ℕ) : ℝ) ^ 3)⁻¹ ^ (3 - 1) ≤ 1 := by norm_num
    have h3 : (etaT (1 / 2) u)⁻¹ ^ 3 * (((32 : ℕ) : ℝ) ^ 3)⁻¹ ^ (3 - 1) ≤ 3 / 2 := by
      calc (etaT (1 / 2) u)⁻¹ ^ 3 * (((32 : ℕ) : ℝ) ^ 3)⁻¹ ^ (3 - 1) ≤ (11 / 10) ^ 3 * 1 :=
            mul_le_mul h1 h2 (by positivity) (by norm_num)
        _ ≤ 3 / 2 := by norm_num
    linarith
  have hC : uStepC 3 (1 / 128) v * ((etaT (1 / 2) u)⁻¹ ^ 3 * (((32 : ℕ) : ℝ) ^ 3)⁻¹ ^ (3 - 1) +
      2 * (etaT (1 / 2) v)⁻¹ ^ 3) ≤ 1 * 5 := mul_le_mul hU hbr hbr0 (by norm_num)
  have e : stepErrN 3 4 32 (1 / 2) 3 u v (1 / 128) (2 * (etaT (1 / 2) v)⁻¹ ^ 3) =
      envConst 3 4 32 (1 / 2) 3 v * ((1 : ℝ) / 128) ^ ((3 : ℝ) / 2) +
        kStepC 3 4 32 3 (2 * (etaT (1 / 2) v)⁻¹ ^ 3) * (1 / 128) ^ 2 +
        uStepC 3 (1 / 128) v * ((etaT (1 / 2) u)⁻¹ ^ 3 * (((32 : ℕ) : ℝ) ^ 3)⁻¹ ^ (3 - 1) +
          2 * (etaT (1 / 2) v)⁻¹ ^ 3) := rfl
  rw [e]
  linarith

/-- **`hR` at the data**: the weighted step errors on the grid of `n = 0` sum to at most
`N^5 = N^{-D_t}` (`D_t = -5`): the sum is about `2^{100}`, `N^5 = 2^{105}`. -/
theorem hR_instance :
    ∑ j ∈ Finset.range (Kg 0), (1 + (1 - gridTime sInst vg Kg 0 (Kg 0))⁻¹) ^ 3 *
        stepErrN 3 (sz0.L 0) (sz0.W 0) (Einst 0) 3 (gridTime sInst vg Kg 0 j)
          (gridTime sInst vg Kg 0 (j + 1)) (gridStep sInst vg Kg 0)
          (((sz0.size 0 : ℕ) : ℝ) ^ ((1 : ℝ) / 21) *
            (etaT (Einst 0) (gridTime sInst vg Kg 0 (j + 1)))⁻¹ ^ 3) ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (-(-5 : ℝ)) := by
  rw [N_tauK, N_five, step0, sz0_values.1, sz0_values.2.1, Kg0, u4]
  have hterm : ∀ j ∈ Finset.range 4,
      (1 + (1 - (1 / 32 : ℝ))⁻¹) ^ 3 *
        stepErrN 3 4 32 (Einst 0) 3 (gridTime sInst vg Kg 0 j) (gridTime sInst vg Kg 0 (j + 1))
          (1 / 128) (2 * (etaT (Einst 0) (gridTime sInst vg Kg 0 (j + 1)))⁻¹ ^ 3) ≤
      (1 + (1 - (1 / 32 : ℝ))⁻¹) ^ 3 * (16 * 6 ^ 4 * 2097152 ^ 4 * (21 / 10) ^ 7 * (1 / 1408) +
        kStepC 3 4 32 3 3 * (1 / 128) ^ 2 + 5) := by
    intro j hj
    have hj4 := Finset.mem_range.1 hj
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact stepErr_le (u := gridTime sInst vg Kg 0 j) (v := gridTime sInst vg Kg 0 (j + 1))
      (u_nonneg j) (u_mono j (j + 1) (Nat.le_succ j)) (u_le (j + 1) (by omega))
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  unfold kStepC
  norm_num

/-! ### `hlog` and the seven absorption inequalities at the data, for every `C > 0` -/

private theorem eta_inv_le_v : (etaT (Einst 0) (vg 0))⁻¹ ≤ 11 / 10 :=
  eta_inv_le (t := vg 0) (by norm_num [vg]) (by norm_num [vg])

/-- **`hlog` at the data**: `Σ_j Δ/η_{u_j} ≤ 4 Δ (11/10) < 1 ≤ Ls = 21 log 2/Im m(1/2)`. -/
theorem hlog_instance :
    ∑ j ∈ Finset.range (Kg 0), gridStep sInst vg Kg 0 /
        etaT (Einst 0) (gridTime sInst vg Kg 0 j) ≤
      (mE (Einst 0)).im⁻¹ * Real.log ((sz0.size 0 : ℕ) : ℝ) := by
  refine le_trans ?_ Ls_bounds.1
  rw [Kg0, step0]
  have hterm : ∀ j ∈ Finset.range 4, (1 / 128 : ℝ) / etaT (Einst 0) (gridTime sInst vg Kg 0 j) ≤
      1 / 128 * (11 / 10) := by
    intro j hj
    have hj4 := Finset.mem_range.1 hj
    have e : Einst 0 = 1 / 2 := rfl
    rw [e, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (eta_inv_le (u_nonneg j) (u_le j (by omega))) (by norm_num)
  calc ∑ j ∈ Finset.range 4, (1 / 128 : ℝ) / etaT (Einst 0) (gridTime sInst vg Kg 0 j)
      ≤ ∑ j ∈ Finset.range 4, (1 / 128 : ℝ) * (11 / 10) := Finset.sum_le_sum hterm
    _ = 4 * (1 / 128 * (11 / 10)) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
    _ ≤ 14 := by norm_num

private theorem le_P0 {x : ℝ} (hx : 1 ≤ x) {m : ℕ} (hm : m ≤ 21) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c ≤ 2 ^ 252 / 12) : x ^ m * c ≤ x ^ 21 * 2 ^ 252 / 12 := by
  have h1 : x ^ m ≤ x ^ 21 := pow_le_pow_right₀ hx hm
  have h0 : 0 ≤ x ^ 21 := by positivity
  calc x ^ m * c ≤ x ^ 21 * c := mul_le_mul_of_nonneg_right h1 hc0
    _ ≤ x ^ 21 * (2 ^ 252 / 12) := mul_le_mul_of_nonneg_left hc h0
    _ = _ := by ring

private theorem ha1_inst (C : ℝ) (hC : 0 < C) :
    ((sz0.W 0 : ℕ) : ℝ) ^ (C * (4 / 5)) * ((sz0.size 0 : ℕ) : ℝ) ^ ((2 : ℝ) / 21) ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (C + 12) / 6 := by
  have hx : 1 ≤ (2 : ℝ) ^ C := Real.one_le_rpow (by norm_num) hC.le
  rw [W_eps, N_eps1, N_eps0]
  have h := le_P0 hx (m := 4) (c := 4) (by norm_num) (by norm_num) (by norm_num)
  have h21 : 0 ≤ ((2 : ℝ) ^ C) ^ 21 * 2 ^ 252 := by positivity
  linarith

private theorem ha2_inst (C : ℝ) (hC : 0 < C) :
    ((3 : ℕ) : ℝ) * ((sz0.W 0 : ℕ) : ℝ) ^ (C * (4 / 5)) *
        (((sz0.size 0 : ℕ) : ℝ) ^ ((2 : ℝ) / 21)) ^ 3 *
        ((mE (Einst 0)).im⁻¹ * Real.log ((sz0.size 0 : ℕ) : ℝ)) ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (C + 12) / 12 := by
  have hx : 1 ≤ (2 : ℝ) ^ C := Real.one_le_rpow (by norm_num) hC.le
  have hLs := Ls_bounds
  rw [W_eps, N_eps1, N_eps0]
  have hx0 : 0 ≤ ((2 : ℝ) ^ C) ^ 4 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hLs.2 (by positivity : (0 : ℝ) ≤ 3 * ((2 : ℝ) ^ C) ^ 4 * 4 ^ 3)
  have h := le_P0 hx (m := 4) (c := 3072) (by norm_num) (by norm_num) (by norm_num)
  push_cast
  nlinarith

private theorem ha3_inst (C : ℝ) (hC : 0 < C) :
    ((sz0.size 0 : ℕ) : ℝ) ^ (1 : ℝ) * (((sz0.W 0 : ℕ) : ℝ) ^ (C * (4 / 5)) *
        ((sz0.size 0 : ℕ) : ℝ) ^ ((2 : ℝ) / 21) *
        Real.sqrt (((3 : ℕ) : ℝ) * ((mE (Einst 0)).im⁻¹ * Real.log ((sz0.size 0 : ℕ) : ℝ) + 1))) ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (C + 12) / 12 := by
  have hx : 1 ≤ (2 : ℝ) ^ C := Real.one_le_rpow (by norm_num) hC.le
  have hLs := Ls_bounds
  have hs : Real.sqrt (((3 : ℕ) : ℝ) * ((mE (Einst 0)).im⁻¹ * Real.log ((sz0.size 0 : ℕ) : ℝ) + 1)) ≤ 8 :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by push_cast; nlinarith [hLs.2]⟩
  rw [W_eps, N_eps1, N_eps0, N_one]
  have hx0 : 0 ≤ ((2 : ℝ) ^ C) ^ 4 := by positivity
  have h1 : ((2 : ℝ) ^ C) ^ 4 * 4 * Real.sqrt (((3 : ℕ) : ℝ) *
      ((mE (Einst 0)).im⁻¹ * Real.log ((sz0.size 0 : ℕ) : ℝ) + 1)) ≤ ((2 : ℝ) ^ C) ^ 4 * 4 * 8 :=
    mul_le_mul_of_nonneg_left hs (by positivity)
  have h := le_P0 hx (m := 4) (c := 2 ^ 26) (by norm_num) (by norm_num) (by norm_num)
  nlinarith

private theorem W_neg6 : ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ)) = ((32 : ℝ) ^ 6)⁻¹ := by
  rw [show (-(6 : ℝ)) = -((6 : ℕ) : ℝ) by norm_num, W_neg]

private theorem W_neg5 : ((sz0.W 0 : ℕ) : ℝ) ^ (-(5 : ℝ)) = ((32 : ℝ) ^ 5)⁻¹ := by
  rw [show (-(5 : ℝ)) = -((5 : ℕ) : ℝ) by norm_num, W_neg]

private theorem he1_inst (C : ℝ) (hC : 0 < C) :
    ((sz0.size 0 : ℕ) : ℝ) ^ 3 * (((sz0.W 0 : ℕ) : ℝ) ^ C * ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ))) ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (C + 12) / 12 := by
  have hx : 1 ≤ (2 : ℝ) ^ C := Real.one_le_rpow (by norm_num) hC.le
  rw [W_C, W_neg6, N_eps0, N0]
  have h := le_P0 hx (m := 5) (c := 8589934592) (by norm_num) (by norm_num) (by norm_num)
  have e : (2097152 : ℝ) ^ 3 * (((2 : ℝ) ^ C) ^ 5 * ((32 : ℝ) ^ 6)⁻¹) =
      ((2 : ℝ) ^ C) ^ 5 * 8589934592 := by ring
  rw [e]
  exact h

private theorem he3_inst (C : ℝ) (hC : 0 < C) :
    ((sz0.size 0 : ℕ) : ℝ) ^ 3 * ((sz0.size 0 : ℕ) : ℝ) ^ (-(1 : ℝ)) ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (C + 12) / 6 := by
  have hx : 1 ≤ (2 : ℝ) ^ C := Real.one_le_rpow (by norm_num) hC.le
  rw [N_eps0, N_negone, N0]
  have h := le_P0 hx (m := 0) (c := 4398046511104) (by norm_num) (by norm_num) (by norm_num)
  have h21 : 0 ≤ ((2 : ℝ) ^ C) ^ 21 * 2 ^ 252 := by positivity
  have e : (2097152 : ℝ) ^ 3 * (2097152 : ℝ)⁻¹ = 4398046511104 := by norm_num
  rw [e]
  simp only [pow_zero, one_mul] at h
  linarith

private theorem he4_inst (C : ℝ) (hC : 0 < C) :
    ((sz0.size 0 : ℕ) : ℝ) ^ 3 * ((sz0.size 0 : ℕ) : ℝ) ^ (-(-5 : ℝ)) ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (C + 12) / 6 := by
  have hx : 1 ≤ (2 : ℝ) ^ C := Real.one_le_rpow (by norm_num) hC.le
  rw [N_eps0, N_five, N0]
  have h1 : 1 ≤ ((2 : ℝ) ^ C) ^ 21 := one_le_pow₀ hx
  nlinarith

private theorem he2_inst (hC : 0 < nqGood1C 3 3 10 (1 / 2)) :
    ((sz0.size 0 : ℕ) : ℝ) ^ (1 : ℝ) * (((sz0.size 0 : ℕ) : ℝ) ^ 3 *
        Real.sqrt (((3 : ℕ) : ℝ) * (nqBudget_qvFar sz0 0 3 10 (1 / 2) (4 / 5) *
          ((sz0.W 0 : ℕ) : ℝ) ^ (-(5 : ℝ))))) ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (nqGood1C 3 3 10 (1 / 2) + 12) / 12 := by
  unfold nqBudget_qvFar nqBudget_kapFar
  generalize nqGood1C 3 3 10 (1 / 2) = C at hC ⊢
  have hx : 1 ≤ (2 : ℝ) ^ C := Real.one_le_rpow (by norm_num) hC.le
  rw [W_eps, W_C, W_neg5, N_eps0, lam0, N_one]
  generalize (2 : ℝ) ^ C = x at hx ⊢
  have hx0 : 0 ≤ x := by linarith
  simp only [Nat.cast_ofNat]
  rw [W0, N0]
  have h8 : x ^ 8 ≤ x ^ 10 := pow_le_pow_right₀ hx (by norm_num)
  have h9 : x ^ 9 ≤ x ^ 10 := pow_le_pow_right₀ hx (by norm_num)
  have h5 : x ^ 5 ≤ x ^ 10 := pow_le_pow_right₀ hx (by norm_num)
  have hq : 3 * ((x ^ 4 * ((1 + (1 / 64 : ℝ) ^ 2) * 2097152) ^ (3 - 1) *
        (x ^ 4 * ((1 + (1 / 64 : ℝ) ^ 2) * 2097152) ^ (3 - 1) + x ^ 5) + x ^ 5 * 32 ^ 3) *
        ((32 : ℝ) ^ 5)⁻¹) ≤ (x ^ 5 * 2 ^ 31) ^ 2 := by
    norm_num
    nlinarith [h8, h9, h5]
  have hs := Real.sqrt_le_iff.2 ⟨by positivity, hq⟩
  have h1 := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 2097152 ^ 3)
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2097152)
  have e : (2097152 : ℝ) * (2097152 ^ 3 * (x ^ 5 * 2 ^ 31)) = x ^ 5 * 2 ^ 115 := by ring
  rw [e] at h2
  have h := le_P0 hx (m := 5) (c := 2 ^ 115) (by norm_num) (by positivity) (by norm_num)
  linarith

private theorem Cpos : 0 < nqGood1C 3 3 10 (1 / 2) :=
  nqGood1C_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **`budgetNonAltN` at the data of S3-10b** (`d = 3`, `sz0`, `n = 0`: `L = 4`, `W = 32`,
`N = 2^21`; `E = 1/2`, grid `(sInst, vg, Kg)`: `Δ = 1/128`, `u_j = j/128`; `k = 3`, `Λ_g = 10`,
`κ' = 1/2`, `ε = 4/5`; levels `(Γ, Λ, Φ) = (4, 3, 1)` with `Γ = N^{2/21}`; `D' = 6`, `D'' = 5`,
`D_Y = 1`, `D_t = -5`, `τ_K = 1/21`, `ε_q = 1`, `ε₀ = C + 12` with the abstract
`C = nqGood1C 3 3 10 (1/2) > 0`; `X0 = 4 B_0^3`; label `aFar`): every hypothesis is discharged
(`hlog`, `hR` by the explicit bounds above, `ha1`-`he4` for every `C > 0`); nothing is left open. -/
theorem budgetNonAltN_instance :
    assembledRHSNonAltN sz0 Einst sInst vg Kg 0 3 10 (1 / 2) (4 / 5) Γ4 Λ3 Φ1 6 5 1 (1 / 21) 1
        (4 * (sz0.Bctl 0 (sInst 0)) ^ 3) aFar ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (nqGood1C 3 3 10 (1 / 2) + 12) *
        (Λ3 0 ^ ((1 : ℝ) / 2) + Φ1 0 + Φ1 0 ^ 2) * (sz0.Bctl 0 (vg 0)) ^ 3 :=
  budgetNonAltN sz0 Einst sInst vg Kg 0 3 10 (1 / 2) (4 / 5) Γ4 Λ3 Φ1 6 5 1 (-5) (1 / 21) 1
    (nqGood1C 3 3 10 (1 / 2) + 12) (2 / 21) (4 * (sz0.Bctl 0 (sInst 0)) ^ 3) aFar
    (by norm_num) (by norm_num) (Einst_abs_lt 0) (by norm_num [sInst]) (by norm_num [sInst, vg])
    (by norm_num [vg]) (by norm_num [Kg]) eta_inv_le_N
    (by rw [step0]; linarith [eta_inv_le_v])
    (by rw [N_eps1]) (by norm_num [Λ3]) (by norm_num [Φ1])
    hlog_instance (by rw [N_eps1]) hR_instance
    (ha1_inst _ Cpos) (ha2_inst _ Cpos) (ha3_inst _ Cpos) (he1_inst _ Cpos) (he2_inst Cpos)
    (he3_inst _ Cpos) (he4_inst _ Cpos)

/-! ### (d) `nqBudget_merged_inputs` at the data of `GridEnvelopeNCheck` -/

section Merged

open RBM.Ind.GridEnvelopeNCheck

/-- **`nqBudget_merged_inputs` at the data of `GridEnvelopeNCheck`** (`d = 3`, `sz0`, `κ = 1`,
`τ' = τ_K = 1/2`, `C_K = 21`, `D_t = 1`, `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `K n = N_n^{21}`, `k = 3`):
every hypothesis is discharged (`sz0_tendsto`, `rangeCond_half`, `rpow_21_le_Kc`, `Kc_ne_zero`,
the four `C_K` inequalities); `hlog` and `hR` hold eventually. -/
theorem nqBudget_merged_inputs_instance :
    ∀ᶠ n : ℕ in atTop,
      (∑ j ∈ Finset.range (Kc n), gridStep (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n /
          etaT (E1 n) (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n j) ≤
        (mE (E1 n)).im⁻¹ * Real.log ((sz0.size n : ℕ) : ℝ)) ∧
      (∑ j ∈ Finset.range (Kc n),
          (1 + (1 - gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n (Kc n))⁻¹) ^ 3 *
          stepErrN 3 (sz0.L n) (sz0.W n) (E1 n) 3
            (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n j)
            (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n (j + 1))
            (gridStep (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n)
            (((sz0.size n : ℕ) : ℝ) ^ (1 / 2 : ℝ) *
              (etaT (E1 n) (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n
                (j + 1)))⁻¹ ^ 3) ≤
        ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) :=
  nqBudget_merged_inputs sz0 (κ := 1) (τ' := 1 / 2) (τK := 1 / 2) (C_K := 21) (D_t := 1)
    (E := E1) (s := fun _ => 0) (v := fun _ => 1 / 2) (K := Kc) 3 one_pos (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) sz0_tendsto (fun _ => by norm_num)
    (fun _ => le_rfl) (fun _ => by norm_num) (fun _ => by norm_num) Kc_ne_zero rangeCond_half
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Eventually.of_forall rpow_21_le_Kc)

/-- The `∃ n` consequence: there is an index `n` at which both `hlog` and `hR` of `budgetNonAltN`
hold at the data of `nqBudget_merged_inputs_instance`. -/
theorem nqBudget_merged_inputs_exists :
    ∃ n : ℕ,
      (∑ j ∈ Finset.range (Kc n), gridStep (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n /
          etaT (E1 n) (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n j) ≤
        (mE (E1 n)).im⁻¹ * Real.log ((sz0.size n : ℕ) : ℝ)) ∧
      (∑ j ∈ Finset.range (Kc n),
          (1 + (1 - gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n (Kc n))⁻¹) ^ 3 *
          stepErrN 3 (sz0.L n) (sz0.W n) (E1 n) 3
            (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n j)
            (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n (j + 1))
            (gridStep (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n)
            (((sz0.size n : ℕ) : ℝ) ^ (1 / 2 : ℝ) *
              (etaT (E1 n) (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n
                (j + 1)))⁻¹ ^ 3) ≤
        ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) :=
  nqBudget_merged_inputs_instance.exists

end Merged

end NQBudgetInst

end RBM.Ind

end

#print axioms RBM.Ind.assembledRHSNonAltN
#print axioms RBM.Ind.nqBudget_qvShape
#print axioms RBM.Ind.nqBudget_kapFar
#print axioms RBM.Ind.nqBudget_qvFar
#print axioms RBM.Ind.nqBudget_im_le_one
#print axioms RBM.Ind.nqBudget_inv_one_sub_le
#print axioms RBM.Ind.nqBudget_sum_succ_le
#print axioms RBM.Ind.nqBudget_sqrt_add_le
#print axioms RBM.Ind.nqBudget_kappa_le_kapFar
#print axioms RBM.Ind.tbInitN
#print axioms RBM.Ind.tbDriftN
#print axioms RBM.Ind.tbQvN
#print axioms RBM.Ind.qvBdNonAltN_eq_qvShape
#print axioms RBM.Ind.tbInitNonAltN
#print axioms RBM.Ind.tbDriftNonAltN
#print axioms RBM.Ind.tbQvNonAltN
#print axioms RBM.Ind.budgetNonAltN
#print axioms RBM.Ind.nqBudget_merged_inputs
#print axioms RBM.Ind.NQBudgetInst.tbInitN_instance
#print axioms RBM.Ind.NQBudgetInst.tbDriftN_instance
#print axioms RBM.Ind.NQBudgetInst.tbQvN_instance
#print axioms RBM.Ind.NQBudgetInst.hR_instance
#print axioms RBM.Ind.NQBudgetInst.hlog_instance
#print axioms RBM.Ind.NQBudgetInst.budgetNonAltN_instance
#print axioms RBM.Ind.NQBudgetInst.nqBudget_merged_inputs_instance
#print axioms RBM.Ind.NQBudgetInst.nqBudget_merged_inputs_exists
