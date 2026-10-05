/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.NQGood1
import RBM3D.Induction.ScaleFacts
import RBM3D.Induction.StepDecompN
import RBM3D.Induction.GridDuhamelN
import RBM3D.Induction.Step2Events
import RBM3D.Green.CondDom

/-!
# The non-alternating good-set inputs, second half (`d ≥ 3`): the class, the constants, the
# fields of `GridAssemblyHypN` and the quadratic-variation constant

Ticket T2167 (S3-10b, stochastic layer ST-3).  Port of RBM2D `Induction/NonAltGood.lean` §4 Classes
and Pathwise (`NAG:1117-1371`), §5 QVConst/QVGrid (`NAG:1385-1571`) and the items 3-4 instances of
§6 (`NAG:1883-2191`) at commit `c9a24cf`, re-derived for `d ≥ 3` on the merged S3-10a
(`Induction/NQGood1`): `hker_of_case1N` gives `W^{Cε} r^{k-1}` and `W^C` (no `cCase1 (1+log L)^k
K_w^{2(k-1)} ρ^k`, no `((1-u)/(1-w))^k`), `Bctl` replaces `scaleM⁻¹`, and
`nqGood1_qvFormN_le_of_bounds` replaces `ugenPairCase1Explicit`.  Paper: arXiv:2507.20274,
`paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`): `lem:STOeq_NQ` (`3_5:1136`, proof `3_5:1152`),
(5.93) (`3_5:1158`).  Not ported: RBM2D §3 (`zero_mem_goodSetN`: merged as `zero_mem_goodSetN_of_levels`),
`NonAltGood_cCase1_nonneg`, `NonAltGood_cPair1_nonneg` (the constant is `nqGood1C`),
`dDriftNonAlt_eq` (the `d ≥ 3` level is in closed form), the §6 item 1-2 instances (`NQGood1Inst`).

## What is here (namespace `RBM.Ind`)

* §1 the vocabulary: `nonAltClsN`, `kappaNonAltN`, `epsNonAltN`, `dDriftNonAltN`, `qvBdNonAltN`,
  `cQVNonAltN` (the six definitions of the ticket, verbatim).
* §2 (5.93) at `d ≥ 3`: `nqGood2_ratio_mul_Bctl_le` (`r_{u,t} B_u ≤ B_t`, an inequality: the
  `(L^d|1-t|)⁻¹` term of `Bparam` turns RBM2D's identity into `g²(t-u) ≥ 0`),
  `kappaNonAltN_mul_Bctl_pow_le`, `kappaNonAltN_succ_mul_Bctl_pow_le`.
* §3 the fields of `GridAssemblyHypN`: `nonAlt_hkerN`, `goodSetN_A0clsN`, `nonAlt_hA0clsN`,
  `nonAlt_hdriftN`, `goodSetN_driftClsN`, `nonAlt_hDclsN`, `nonAlt_hκ0N`, `nonAlt_hε0N`,
  `nonAlt_hdDrift0N`.
* §4 the quadratic-variation constant: `qvBdNonAltN_pos`, `qvFormN_le_of_goodSetN_shiftN`,
  `hQ_nonAltN`, `subGaussStop_nonAltN`, `cQVNonAltN_sum_pos`.
* §5 compiled nonempty instances at `d = 3` (namespace `NQGood2Inst`) on `sz0`, with the compiled
  bundle `GridAssemblyHypN` built from the theorems of §§3-4.

## Port map (RBM2D at `c9a24cf`; `NAG` = `NonAltGood.lean`)

`NonAltGood_rhoR_mul_scaleM_inv` `NAG:1143` → `nqGood2_ratio_mul_Bctl_le`; `nonAltCls` `:1168` →
`nonAltClsN`; `kappaNonAlt` `:1174` → `kappaNonAltN`; `epsNonAlt` `:1179` → `epsNonAltN`;
`dDriftNonAlt` `:1184` → `dDriftNonAltN`; `kappaNonAlt_mul_scale_pow_eq` `:1232` →
`kappaNonAltN_mul_Bctl_pow_le`; `kappaNonAlt_succ_mul_scale_pow_le` `:1250` →
`kappaNonAltN_succ_mul_Bctl_pow_le`; `nonAlt_hker` `:1272` → `nonAlt_hkerN`; `goodSetN_A0cls`
`:1283` → `goodSetN_A0clsN`; `goodSetN_driftCls` `:1297` → `goodSetN_driftClsN`; `nonAlt_hA0cls`
`:1317`, `nonAlt_hdrift` `:1329`, `nonAlt_hDcls` `:1341`, `nonAlt_hκ0` `:1356`,
`nonAlt_hε0` `:1361`, `nonAlt_hdDrift0` `:1366` → the `N` versions; `qvBdNonAlt` `:1385` → `qvBdNonAltN`;
`qvBdNonAlt_pos` `:1395` → `qvBdNonAltN_pos`; `qvFormN_le_of_goodSet_shiftN` `:1424` →
`qvFormN_le_of_goodSetN_shiftN`; `cQVNonAlt` `:1495` → `cQVNonAltN`; `hQ_nonAlt` `:1503` →
`hQ_nonAltN`; `subGaussStop_nonAlt` `:1532` → `subGaussStop_nonAltN`; `cQVNonAlt_sum_pos` `:1549` →
`cQVNonAltN_sum_pos`; §6 items 3-4 (`:1883-2191`) → §5 below.

Every unpinned helper is `private` or prefixed `nqGood2_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-! ## 1. The vocabulary (the six definitions of the ticket, verbatim) -/

/-- **The kernel class of the non-alternating case** (RBM2D `nonAltCls`, `NonAltGood:1168`):
`Cls i δ X :⇔ δ ≤ W^{-Dc}` and `‖X b‖ ≤ δ` when `ℓ_{u_i} W^{τ'} ≤ diam_∞ b` -- exactly the hypotheses
`hδD`, `hXcls` of `hker_of_case1N` at `s = u_i`, `D = Dc`; the radius is the `L^∞` one of `GoodSetN`. -/
def nonAltClsN (d L : ℕ) {k : ℕ} (g W τ' Dc : ℝ) (u : ℕ → ℝ) :
    ℕ → ℝ → ((Fin k → Zd d L) → ℂ) → Prop :=
  fun i δ X => δ ≤ W ^ (-Dc) ∧
    ∀ b : Fin k → Zd d L, ellT L g (u i) * W ^ τ' ≤ (STdiamInf b : ℝ) → ‖X b‖ ≤ δ

/-- **The kernel weight `κ_{i,m}`** (RBM2D `kappaNonAlt`, `NonAltGood:1174`): the coefficient of `M`
in `hker_of_case1N`, `W^{Cε} ((g²+|1-u_i|)/(g²+|1-u_m|))^{k-1}`, `C = nqGood1C d k Λg κ'`. -/
def kappaNonAltN (d k : ℕ) (Λg κ' g W ε : ℝ) (u : ℕ → ℝ) (i m : ℕ) : ℝ :=
  W ^ (nqGood1C d k Λg κ' * ε) * ((g ^ 2 + |1 - u i|) / (g ^ 2 + |1 - u m|)) ^ (k - 1)

/-- **The additive decay-error weight `ε_{i,m}`** (RBM2D `epsNonAlt`, `NonAltGood:1179`): the
coefficient of `δ` in `hker_of_case1N`, the constant `W^C`. -/
def epsNonAltN (d k : ℕ) (Λg κ' W : ℝ) (_i _m : ℕ) : ℝ :=
  W ^ nqGood1C d k Λg κ'

/-- **The drift level** (RBM2D `dDriftNonAlt`, `NonAltGood:1184`): the right side of
`driftTensorN_norm_le_of_goodSet`, `Γ(ΓΦ)(B_u^k/η_u)((k-1) + kΓΦ)`; no additive `W^{-D'}`. -/
def dDriftNonAltN {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (k : ℕ) (Γ Φ : ℝ) : ℝ :=
  Γ * (Γ * Φ) * ((sz.Bctl n u) ^ k / etaT E u) * (((k : ℝ) - 1) + (k : ℝ) * (Γ * Φ))

/-- **The variance majorant** (RBM2D `qvBdNonAlt`, `NonAltGood:1385`): the right side of
`nqGood1_qvFormN_le_of_bounds` at `(v, w) = (u, w)` with `M_ee = Γ(ΓΛ)B_u^{2k}/η_u + W^{-D''}` and
`δ = W^{-D''}`. -/
def qvBdNonAltN {d : ℕ} (sz : Sizes d) (n : ℕ) (E : ℝ) (k : ℕ)
    (Λg κ' ε Γ Λ D'' u w : ℝ) : ℝ :=
  (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
      ((sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - w|)) ^ (k - 1)) *
    ((((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
        ((sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - w|)) ^ (k - 1)) *
      (Γ * (Γ * Λ) * ((sz.Bctl n u) ^ (2 * k) / etaT E u) + ((sz.W n : ℕ) : ℝ) ^ (-D'')) +
      ((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' * ((sz.W n : ℕ) : ℝ) ^ (-D'')) +
    ((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' *
      (((sz.W n : ℕ) : ℝ) ^ k * ((sz.W n : ℕ) : ℝ) ^ (-D''))

/-- **The sub-Gaussian proxy of the `j`-th propagated increment towards `u_m`** (RBM2D `cQVNonAlt`,
`NonAltGood:1495`): `Δ · k · qvBdNonAltN(u_{j+1}, u_m)` (the label `a` does not enter). -/
def cQVNonAltN {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (Λg κ' ε : ℝ)
    (Γ Λ : ℕ → ℝ) (D'' : ℝ) (m : ℕ) (_a : Fin k → Zd d (sz.L n)) (j : ℕ) : ℝ≥0 :=
  (gridStep s v K n * ((k : ℝ) * qvBdNonAltN sz n (E n) k Λg κ' ε (Γ n) (Λ n) D''
    (gridTime s v K n (j + 1)) (gridTime s v K n m))).toNNReal

/-! ## 2. (5.93) at `d ≥ 3` -/

section Ratio

variable {d : ℕ} (sz : Sizes d)

/-- **(5.93) at `d ≥ 3`** (paper `3_5:1158`: "`(ilambda²+|1-u|)/(ilambda²+|1-t|) B_{u,0} ≤ B_{t,0}`";
RBM2D `NonAltGood_rhoR_mul_scaleM_inv`, `NonAltGood.lean:1143`, was the exact identity
`ρ_{s,t} M_s⁻¹ = M_t⁻¹`): for `u ≤ t < 1` and every real `g = sz.lam n`,
`((g²+|1-u|)/(g²+|1-t|)) · B_u ≤ B_t`, `B = W^{-d} B_{·,0}` (`sz.Bctl`).  The first term of `Bparam`,
`(g²+|1-u|)⁻¹`, gives equality; the second, `(L^d|1-u|)⁻¹`, gives the defect `g²(t-u) ≥ 0`. -/
theorem nqGood2_ratio_mul_Bctl_le (n : ℕ) {u t : ℝ} (hut : u ≤ t) (ht : t < 1) :
    ((sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - t|)) * sz.Bctl n u ≤ sz.Bctl n t := by
  have hu1 : u < 1 := hut.trans_lt ht
  have hxu : 0 < 1 - u := by linarith
  have hxt : 0 < 1 - t := by linarith
  have hg : 0 ≤ sz.lam n ^ 2 := sq_nonneg _
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  unfold Sizes.Bctl Bparam
  rw [abs_of_pos hxu, abs_of_pos hxt]
  simp only [Nat.cast_zero, zero_add, one_pow, inv_one, mul_one]
  set g2 : ℝ := sz.lam n ^ 2 with hg2
  set Lp : ℝ := ((sz.L n : ℕ) : ℝ) ^ d with hLp
  set Wp : ℝ := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ with hWp
  have hLp0 : 0 < Lp := by positivity
  have hWp0 : 0 < Wp := by positivity
  have ha : 0 < g2 + (1 - u) := by linarith
  have hb : 0 < g2 + (1 - t) := by linarith
  have e1 : (g2 + (1 - u)) / (g2 + (1 - t)) * (g2 + (1 - u))⁻¹ = (g2 + (1 - t))⁻¹ := by
    field_simp
  have e2 : (g2 + (1 - u)) / (g2 + (1 - t)) * (Lp * (1 - u))⁻¹ ≤ (Lp * (1 - t))⁻¹ := by
    rw [← sub_nonneg]
    have : (Lp * (1 - t))⁻¹ - (g2 + (1 - u)) / (g2 + (1 - t)) * (Lp * (1 - u))⁻¹ =
        g2 * (t - u) / (Lp * (1 - t) * (1 - u) * (g2 + (1 - t))) := by
      field_simp
      ring
    rw [this]
    exact div_nonneg (mul_nonneg hg (by linarith)) (by positivity)
  calc (g2 + (1 - u)) / (g2 + (1 - t)) * (Wp * ((g2 + (1 - u))⁻¹ + (Lp * (1 - u))⁻¹))
      = Wp * ((g2 + (1 - u)) / (g2 + (1 - t)) * (g2 + (1 - u))⁻¹ +
          (g2 + (1 - u)) / (g2 + (1 - t)) * (Lp * (1 - u))⁻¹) := by ring
    _ ≤ Wp * ((g2 + (1 - t))⁻¹ + (Lp * (1 - t))⁻¹) := by
        rw [e1]
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl e2) hWp0.le


private theorem nqGood2_kappaNonAltN_nonneg (d k : ℕ) (Λg κ' g W ε : ℝ) (hW : 0 ≤ W) (u : ℕ → ℝ) (i m : ℕ) :
    0 ≤ kappaNonAltN d k Λg κ' g W ε u i m := by
  unfold kappaNonAltN
  exact mul_nonneg (Real.rpow_nonneg hW _) (pow_nonneg (div_nonneg (by positivity) (by positivity)) _)

private theorem nqGood2_pow_aux {r a b : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a) (hab : a ≤ b)
    (hrb : r * a ≤ b) (k : ℕ) : r ^ (k - 1) * a ^ k ≤ b ^ k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    calc r ^ k' * a ^ (k' + 1) = (r * a) ^ k' * a := by ring
      _ ≤ b ^ k' * b := mul_le_mul (pow_le_pow_left₀ (mul_nonneg hr ha) hrb k') hab ha
          (pow_nonneg (ha.trans hab) _)
      _ = b ^ (k' + 1) := by ring

/-- **(5.93), the sharp kernel on the initial datum** (RBM2D `kappaNonAlt_mul_scale_pow_eq`,
`NonAltGood.lean:1232`, an identity there): for `u_i ≤ u_m < 1` and `0 ≤ W`,
`κ_{i,m} B_{u_i}^k ≤ W^{Cε} B_{u_m}^k` (`κ_{i,m} = W^{Cε} r_{i,m}^{k-1}`; `r^{k-1} B_u^k =
(r B_u)^{k-1} B_u ≤ B_t^{k-1} B_t`). -/
theorem kappaNonAltN_mul_Bctl_pow_le (n k : ℕ) (Λg κ' ε : ℝ) {W : ℝ} (hW : 0 ≤ W) (u : ℕ → ℝ)
    {i m : ℕ} (him : u i ≤ u m) (hm1 : u m < 1) :
    kappaNonAltN d k Λg κ' (sz.lam n) W ε u i m * (sz.Bctl n (u i)) ^ k ≤
      W ^ (nqGood1C d k Λg κ' * ε) * (sz.Bctl n (u m)) ^ k := by
  have hi1 : u i < 1 := him.trans_lt hm1
  have hBu : 0 < sz.Bctl n (u i) := Sizes.STBctl_pos sz n hi1
  have hBle : sz.Bctl n (u i) ≤ sz.Bctl n (u m) := Sizes.STBctl_mono sz n him hm1
  have hr0 : 0 ≤ (sz.lam n ^ 2 + |1 - u i|) / (sz.lam n ^ 2 + |1 - u m|) :=
    div_nonneg (by positivity) (by positivity)
  have hrB := nqGood2_ratio_mul_Bctl_le sz n him hm1
  have hWC : 0 ≤ W ^ (nqGood1C d k Λg κ' * ε) := Real.rpow_nonneg hW _
  unfold kappaNonAltN
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (nqGood2_pow_aux hr0 hBu.le hBle hrB k) hWC

/-- **(5.93), the sharp kernel on the drift** (RBM2D `kappaNonAlt_succ_mul_scale_pow_le`,
`NonAltGood.lean:1250`): for `u_j ≤ u_{j+1} ≤ u_m < 1`, `κ_{j+1,m} B_{u_j}^k ≤ W^{Cε} B_{u_m}^k`
(`B_{u_j} ≤ B_{u_{j+1}}`, `STBctl_mono`, then `kappaNonAltN_mul_Bctl_pow_le`). -/
theorem kappaNonAltN_succ_mul_Bctl_pow_le (n k : ℕ) (Λg κ' ε : ℝ) {W : ℝ} (hW : 0 ≤ W)
    (u : ℕ → ℝ) (j m : ℕ) (hjj : u j ≤ u (j + 1)) (hj1m : u (j + 1) ≤ u m) (hm1 : u m < 1) :
    kappaNonAltN d k Λg κ' (sz.lam n) W ε u (j + 1) m * (sz.Bctl n (u j)) ^ k ≤
      W ^ (nqGood1C d k Λg κ' * ε) * (sz.Bctl n (u m)) ^ k := by
  have hj1 : u (j + 1) < 1 := hj1m.trans_lt hm1
  have hBle : sz.Bctl n (u j) ≤ sz.Bctl n (u (j + 1)) := Sizes.STBctl_mono sz n hjj hj1
  have hBj : 0 < sz.Bctl n (u j) := Sizes.STBctl_pos sz n (hjj.trans_lt hj1)
  have hκ := nqGood2_kappaNonAltN_nonneg d k Λg κ' (sz.lam n) W ε hW u (j + 1) m
  calc kappaNonAltN d k Λg κ' (sz.lam n) W ε u (j + 1) m * (sz.Bctl n (u j)) ^ k
      ≤ kappaNonAltN d k Λg κ' (sz.lam n) W ε u (j + 1) m * (sz.Bctl n (u (j + 1))) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hBj.le hBle k) hκ
    _ ≤ _ := kappaNonAltN_mul_Bctl_pow_le sz n k Λg κ' ε hW u hj1m hm1

end Ratio

/-! ## 3. The fields of `GridAssemblyHypN` -/

section Fields

variable {d : ℕ} (sz : Sizes d)

/-- `u_j ≤ v_n` for `j ≤ K_n` on the grid `s_n ≤ v_n`. -/
private theorem nqGood2_gridTime_le {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hsv : s n ≤ v n) {j : ℕ}
    (hj : j ≤ K n) : gridTime s v K n j ≤ v n := by
  by_cases hK : K n = 0
  · have hj0 : j = 0 := by omega
    subst hj0
    rw [ST_gridTime_zero]
    exact hsv
  · exact (ST_gridTime_mono s v K n hsv hj).trans_eq (gridTime_last s v K n hK)

/-- `0 ≤ u_j` on the grid `0 ≤ s_n ≤ v_n`. -/
private theorem nqGood2_gridTime_nonneg {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hs0 : 0 ≤ s n)
    (hsv : s n ≤ v n) (j : ℕ) : 0 ≤ gridTime s v K n j := by
  have h := ST_gridTime_mono s v K n hsv (Nat.zero_le j)
  rw [ST_gridTime_zero] at h
  linarith

/-- **The field `hker` for non-alternating `σ`, `d ≥ 3`** (RBM2D `nonAlt_hker`,
`NonAltGood.lean:1272`; the merged `hker_of_case1N`, i.e. EK-6, in the shape of the field of
`GridAssemblyHypN`, `Cls = nonAltClsN`, `κ = kappaNonAltN`, `εK = epsNonAltN`): for `u` nonnegative and
monotone on `[0, K]`, `u_K ≤ 1 - g²/L²`, `W⁻¹ ≤ (1-u_K)/(1-u_0)` (so `W⁻¹ ≤ (1-u_m)/(1-u_i)` for
`i ≤ m ≤ K`), `|E| ≤ 2`, `κ' ≤ Im m(E)` and `σ` with `σ_i = σ_{i+1}` for some `i`:
`‖𝒰_{u_i,u_m} X‖ ≤ κ_{i,m} M + ε_{i,m} δ` for `‖X‖ ≤ M` and `X` in the class `nonAltClsN`
(`δ ≤ W^{-Dc}`, `‖X b‖ ≤ δ` beyond `ℓ_{u_i} W^{τ'}`).  Stated for general `L, g, W`, like
`hker_of_case1N`. -/
theorem nonAlt_hkerN {d k : ℕ} (Λg κ' : ℝ) (hd : 3 ≤ d) (hk : 2 ≤ k) (hΛ : 0 < Λg)
    (hκ' : 0 < κ') {L : ℕ} [NeZero L] (hL : 3 ≤ L) {g : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λg)
    {W ε τ' Dc : ℝ} (hW : 1 < W) (hε0 : 0 < ε) (hε1 : ε < 1) (hWε : 4 ≤ W ^ ε)
    (hdW : (d : ℝ) * W ^ τ' ≤ W ^ ε) (hDc : 1 < Dc)
    {K : ℕ} {u : ℕ → ℝ} (hu0 : ∀ i ≤ K, 0 ≤ u i)
    (hmono : ∀ i m, i ≤ m → m ≤ K → u i ≤ u m) (huK : u K ≤ 1 - g ^ 2 / (L : ℝ) ^ 2)
    (hWt : W⁻¹ ≤ (1 - u K) / (1 - u 0)) {E : ℝ} (hE : |E| ≤ 2) (hκm : κ' ≤ (mE E).im)
    {σ : Fin k → Bool} (hσ : ∃ i, σ i = σ (finRotate k i)) :
    ∀ i m, i ≤ m → m ≤ K → ∀ (X : (Fin k → Zd d L) → ℂ) (M δ : ℝ), 0 ≤ M → 0 ≤ δ →
      (∀ b, ‖X b‖ ≤ M) → nonAltClsN d L g W τ' Dc u i δ X →
      ∀ a : Fin k → Zd d L,
      ‖Ugen d L g E σ (u i) (u m) X a‖ ≤
        kappaNonAltN d k Λg κ' g W ε u i m * M + epsNonAltN d k Λg κ' W i m * δ := by
  intro i m him hmK X M δ hM hδ hXM hcls a
  obtain ⟨hδD, hXcls⟩ := hcls
  have hiK : i ≤ K := him.trans hmK
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hgL : 0 < g ^ 2 / (L : ℝ) ^ 2 := by positivity
  have hK1 : u K < 1 := by linarith
  have hmK' : u m ≤ u K := hmono m K hmK le_rfl
  have hi0 : u 0 ≤ u i := hmono 0 i (Nat.zero_le _) hiK
  have hwin : W⁻¹ ≤ (1 - u m) / (1 - u i) := by
    refine hWt.trans ?_
    exact div_le_div₀ (by linarith) (by linarith) (by linarith [hmono i K hiK le_rfl]) (by linarith)
  have h := hker_of_case1N Λg κ' hd hk hΛ hκ' hL hg hgΛ hW hε0 hε1 hWε hdW hDc (hu0 i hiK)
    (hmono i m him hmK) (hmK'.trans huK) hwin hE hκm hσ X hM hδ hδD hXM hXcls a
  exact h

/-- **The field `hA0cls`** (RBM1D `kerClass_A0`, `:1239`; RBM2D `goodSetN_A0cls`,
`NonAltGood.lean:1283`), matrix level: for `M ∈ GoodSetN … u_i`, `1 ≤ k` and `Dc ≤ D'`, the tensor
`a ↦ (𝓛-𝒦)_{u_i,σ,a}(M)` is in the class `nonAltClsN … i` with `δ = W^{-D'}` (clause (Dec) at
length `k ≤ 2k+2`; `W^{-D'} ≤ W^{-Dc}` as `1 ≤ W`). -/
theorem goodSetN_A0clsN {n k : ℕ} (hk : 1 ≤ k) {E Γ Λ Φ τ' D' Dc : ℝ} (hDc : Dc ≤ D')
    (hW : 1 ≤ ((sz.W n : ℕ) : ℝ)) {u : ℕ → ℝ} {i : ℕ}
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hM : M ∈ sz.GoodSetN n E (u i) k Γ Λ Φ τ' D') (σ : Fin k → Bool) :
    nonAltClsN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) τ' Dc u i (((sz.W n : ℕ) : ℝ) ^ (-D'))
      (fun a => sz.STLKM n E (u i) M σ a) := by
  refine ⟨Real.rpow_le_rpow_of_exponent_le hW (by linarith), fun b hfar => ?_⟩
  obtain ⟨-, -, hDec, -⟩ := hM
  have h := hDec k hk (by omega) σ b hfar
  have e : sz.STLKM n E (u i) M σ b =
      loopFine d (sz.L n) (sz.W n) M (zt E (u i)) σ b - STKloop sz n E (u i) σ b := rfl
  change ‖sz.STLKM n E (u i) M σ b‖ ≤ _
  rw [e]
  have h0 : 0 ≤ ‖loopFine d (sz.L n) (sz.W n) M (zt E (u i)) σ b‖ := norm_nonneg _
  linarith

/-- **The field `hA0cls` on the event `{H_0 ∈ GoodSetN(u_0)}`** (RBM2D `nonAlt_hA0cls`,
`NonAltGood.lean:1317`): on `{0 < τ}` the initial tensor `A_0 = (𝓛-𝒦)_{u_0}(H_0)` is in the class
`nonAltClsN` with radius `ℓ_{u_0} W^{τ'}` and `δ_0 = W^{-D'}`. -/
theorem nonAlt_hA0clsN {n k : ℕ} (hk : 1 ≤ k) (hW : 1 ≤ ((sz.W n : ℕ) : ℝ)) (σ : Fin k → Bool)
    (E s v : ℕ → ℝ) (K : ℕ → ℕ) (Γ Λ Φ : ℕ → ℝ) (τ' D' Dc : ℝ) (hDc : Dc ≤ D')
    (τ : PathΩ sz → ℕ)
    (hτG : ∀ ω j, j < τ ω → pathH sz s v K n j ω ∈ sz.GoodSetN n (E n) (gridTime s v K n j) k
      (Γ n) (Λ n) (Φ n) τ' D') :
    ∀ ω, 0 < τ ω → nonAltClsN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) τ' Dc (gridTime s v K n) 0
      (((sz.W n : ℕ) : ℝ) ^ (-D')) (AvecN sz E s v K n 0 σ ω) :=
  fun ω hω => goodSetN_A0clsN sz hk hDc hW (hτG ω 0 hω) σ

/-- **The field `hdrift` on the event `{H_j ∈ GoodSetN(u_j), j < τ}`** (RBM2D `nonAlt_hdrift`,
`NonAltGood.lean:1329`): the drift tensor `Dr_j = driftTensorN … (u_j) (H_j)` is bounded by
`dDriftNonAltN` (the triangle inequality of `driftTensorN_norm_le_of_goodSet`). -/
theorem nonAlt_hdriftN {n k : ℕ} (hk : 2 ≤ k) (σ : Fin k → Bool) (E s v : ℕ → ℝ) (K : ℕ → ℕ)
    (Γ Λ Φ : ℕ → ℝ) (τ' D' : ℝ) (τ : PathΩ sz → ℕ)
    (hτG : ∀ ω j, j < τ ω → pathH sz s v K n j ω ∈ sz.GoodSetN n (E n) (gridTime s v K n j) k
      (Γ n) (Λ n) (Φ n) τ' D') :
    ∀ ω j, j < K n → j < τ ω → ∀ b : Fin k → Zd d (sz.L n),
      ‖driftTensorN sz n (E n) (gridTime s v K n j) (pathH sz s v K n j ω) σ b‖ ≤
        dDriftNonAltN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ n) :=
  fun ω j _ hjτ b => driftTensorN_norm_le_of_goodSet sz hk (hτG ω j hjτ) σ b

/-- **The field `hDcls`** (RBM1D `kerClass_drift`, `:1265`; RBM2D `goodSetN_driftCls`,
`NonAltGood.lean:1297`), matrix level: the drift tensor at `u_i` of `M ∈ GoodSetN … u_i` is in the
class `nonAltClsN … i'` of radius `ℓ_{u_{i'}} W^{τ'}`, `δ = W^{-D'}`, for `u_i ≤ u_{i'} < 1` (clause
(Va) at `u_i`; the radius `ℓ_{u_i} W^{τ'} ≤ ℓ_{u_{i'}} W^{τ'}` only grows,
`nqGood1_ellT_mono`, for every real `g`). -/
theorem goodSetN_driftClsN {n k : ℕ} {E Γ Λ Φ τ' D' Dc : ℝ} (hDc : Dc ≤ D')
    (hW : 1 ≤ ((sz.W n : ℕ) : ℝ)) {u : ℕ → ℝ} {i i' : ℕ} (hii' : u i ≤ u i') (hi'1 : u i' < 1)
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hM : M ∈ sz.GoodSetN n E (u i) k Γ Λ Φ τ' D') (σ : Fin k → Bool) :
    nonAltClsN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) τ' Dc u i' (((sz.W n : ℕ) : ℝ) ^ (-D'))
      (driftTensorN sz n E (u i) M σ) := by
  refine ⟨Real.rpow_le_rpow_of_exponent_le hW (by linarith), fun b hfar => ?_⟩
  have hWτ : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ τ' := Real.rpow_nonneg (by linarith) _
  have hrad : ellT (sz.L n) (sz.lam n) (u i) ≤ ellT (sz.L n) (sz.lam n) (u i') :=
    nqGood1_ellT_mono _ _ hii' hi'1
  exact driftTensorN_far_of_goodSet sz hM σ b ((mul_le_mul_of_nonneg_right hrad hWτ).trans hfar)

/-- **The field `hDcls` on the event** (RBM2D `nonAlt_hDcls`, `NonAltGood.lean:1341`): the drift
tensor at `(u_j, H_j)` is in the class `nonAltClsN` at index `j + 1` (radius `ℓ_{u_{j+1}} W^{τ'}`) with
`δ_D = W^{-D'}`. -/
theorem nonAlt_hDclsN {n k : ℕ} (E s v : ℕ → ℝ) (K : ℕ → ℕ) (hsv : s n ≤ v n) (hv1 : v n < 1)
    (hW : 1 ≤ ((sz.W n : ℕ) : ℝ)) (σ : Fin k → Bool)
    (Γ Λ Φ : ℕ → ℝ) (τ' D' Dc : ℝ) (hDc : Dc ≤ D') (τ : PathΩ sz → ℕ)
    (hτG : ∀ ω j, j < τ ω → pathH sz s v K n j ω ∈ sz.GoodSetN n (E n) (gridTime s v K n j) k
      (Γ n) (Λ n) (Φ n) τ' D') :
    ∀ ω j, j < K n → j < τ ω →
      nonAltClsN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) τ' Dc (gridTime s v K n) (j + 1)
        (((sz.W n : ℕ) : ℝ) ^ (-D'))
        (driftTensorN sz n (E n) (gridTime s v K n j) (pathH sz s v K n j ω) σ) := by
  intro ω j hjK hjτ
  have hjj : gridTime s v K n j ≤ gridTime s v K n (j + 1) :=
    ST_gridTime_mono s v K n hsv (Nat.le_succ j)
  have hu1 : gridTime s v K n (j + 1) < 1 :=
    (nqGood2_gridTime_le hsv (show j + 1 ≤ K n by omega)).trans_lt hv1
  exact goodSetN_driftClsN sz hDc hW hjj hu1 (hτG ω j hjτ) σ

/-- The non-negativity field `hκ0` of `GridAssemblyHypN` (RBM2D `nonAlt_hκ0`, `NonAltGood.lean:1356`;
no condition on the grid but `0 ≤ W`: `κ_{i,m} = W^{Cε} r^{k-1}`, `r ≥ 0`). -/
theorem nonAlt_hκ0N (d k : ℕ) (Λg κ' g W ε : ℝ) (hW : 0 ≤ W) (K : ℕ) (u : ℕ → ℝ) :
    ∀ i m, i ≤ m → m ≤ K → 0 ≤ kappaNonAltN d k Λg κ' g W ε u i m :=
  fun i m _ _ => nqGood2_kappaNonAltN_nonneg d k Λg κ' g W ε hW u i m

/-- The non-negativity field `hε0` of `GridAssemblyHypN` (RBM2D `nonAlt_hε0`, `NonAltGood.lean:1361`):
`ε_{i,m} = W^C ≥ 0`. -/
theorem nonAlt_hε0N (d k : ℕ) (Λg κ' W : ℝ) (hW : 0 ≤ W) (K : ℕ) :
    ∀ i m, i ≤ m → m ≤ K → 0 ≤ epsNonAltN d k Λg κ' W i m :=
  fun i m _ _ => Real.rpow_nonneg hW _

/-- The non-negativity field `hdDrift0` of `GridAssemblyHypN` (RBM2D `nonAlt_hdDrift0`,
`NonAltGood.lean:1366`): `Γ(ΓΦ)(B_u^k/η_u)((k-1) + kΓΦ) ≥ 0` for `0 ≤ Γ`, `0 ≤ Φ`, `1 ≤ k`, `u_j < 1`. -/
theorem nonAlt_hdDrift0N {n k : ℕ} (E s v : ℕ → ℝ) (K : ℕ → ℕ) (hk : 1 ≤ k) (hE : |E n| < 2)
    (hsv : s n ≤ v n) (hv1 : v n < 1) (Γ Φ : ℕ → ℝ) (hΓ : 0 ≤ Γ n) (hΦ : 0 ≤ Φ n) :
    ∀ (_ : PathΩ sz) (j : ℕ), j < K n →
      0 ≤ dDriftNonAltN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ n) := by
  intro _ j hj
  have hu1 : gridTime s v K n j < 1 :=
    (nqGood2_gridTime_le hsv (show j ≤ K n by omega)).trans_lt hv1
  have hη := etaT_pos hE hu1
  have hB := Sizes.STBctl_pos sz n hu1
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold dDriftNonAltN
  have h1 : 0 ≤ (k : ℝ) - 1 + (k : ℝ) * (Γ n * Φ n) := by
    have : 0 ≤ (k : ℝ) * (Γ n * Φ n) := mul_nonneg (by linarith) (mul_nonneg hΓ hΦ)
    linarith
  exact mul_nonneg (mul_nonneg (mul_nonneg hΓ (mul_nonneg hΓ hΦ)) (div_nonneg (pow_nonneg hB.le _)
    hη.le)) h1

end Fields

/-! ## 4. The quadratic-variation constant -/

section QVConst

/-- `0 < qvBdNonAltN` (RBM2D `qvBdNonAlt_pos`, `NonAltGood.lean:1395`): the last term
`W^C W^k W^{-D''}` is positive and the others are nonnegative (`ratio ≥ 0`, `Γ(ΓΛ) = Γ²Λ ≥ 0`,
`η_u = (1-u) Im m(E) ≥ 0` for `u ≤ 1`, as `Im m(E) = √(4-E²)/2 ≥ 0` for every real `E`; `W > 0` is
`sz.W_pos`).  No energy condition is needed (paper-delta candidate `T2167e`). -/
theorem qvBdNonAltN_pos {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} {k : ℕ}
    {Λg κ' ε Γ Λ D'' u w : ℝ} (hΛ : 0 ≤ Λ) (hu1 : u ≤ 1) :
    0 < qvBdNonAltN sz n E k Λg κ' ε Γ Λ D'' u w := by
  have hWp : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hη : 0 ≤ etaT E u := by
    unfold etaT
    rw [mE_im]
    exact mul_nonneg (by linarith) (by positivity)
  have hG : 0 ≤ Γ * (Γ * Λ) := by
    have : Γ * (Γ * Λ) = Γ ^ 2 * Λ := by ring
    rw [this]
    exact mul_nonneg (sq_nonneg _) hΛ
  have hB2 : 0 ≤ (sz.Bctl n u) ^ (2 * k) := (even_two_mul k).pow_nonneg _
  have hmain := mul_nonneg hG (div_nonneg hB2 hη)
  have hWD : 0 < ((sz.W n : ℕ) : ℝ) ^ (-D'') := Real.rpow_pos_of_pos hWp _
  have hWC : 0 < ((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' := Real.rpow_pos_of_pos hWp _
  have hκ1 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
      ((sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - w|)) ^ (k - 1) :=
    mul_nonneg (Real.rpow_nonneg hWp.le _) (pow_nonneg (div_nonneg (by positivity) (by positivity)) _)
  unfold qvBdNonAltN
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg hκ1 (add_nonneg (mul_nonneg hκ1 (add_nonneg hmain hWD.le))
      (mul_nonneg hWC.le hWD.le)))
    (mul_pos hWC (mul_pos (pow_pos hWp k) hWD))

/-- **The variance majorant of `AzumaSubGN` after the spectral-time shift `u → u'`** (RBM1D
`hqv514`, `:1446`; RBM2D `qvFormN_le_of_goodSet_shiftN`, `NonAltGood.lean:1424`): for
`M ∈ GoodSetN(u)` (levels `Γ, Λ, Φ`, decay `τ', D'`), `0 ≤ u ≤ u' ≤ w ≤ 1 - g²/L²`,
`W⁻¹ ≤ (1-w)/(1-u')`, non-alternating `σ`, `k + 1 < D''` and the shift hypothesis
`W^{-D'} + eeShiftErrN(u, u') ≤ W^{-D''}`,
`qvFormN_{u',w}(M)(a) ≤ qvBdNonAltN(u', w)`.  Route: `nqGood1_qvFormN_le_of_bounds` at `v = u'` with
`M_ee = Γ(ΓΛ)B_{u'}^{2k}/η_{u'} + W^{-D''}` (from (D4) at `u`, `norm_STeeM_shiftN_le`, `STBctl_mono`,
`etaT_le_of_le`) and `δ = W^{-D''}` (from (Vb) at `u`, `nqGood1_ellT_mono` and the shift).  The
hypothesis `0 ≤ Γ` of the ticket is not used (`Γ(ΓΛ) = Γ²Λ`). -/
theorem qvFormN_le_of_goodSetN_shiftN {d k : ℕ} (Λg κ' : ℝ) (hd : 3 ≤ d) (hk : 2 ≤ k)
    (hΛg : 0 < Λg) (hκ' : 0 < κ') (sz : Sizes d) (n : ℕ) (hg : 0 < sz.lam n)
    (hgΛ : sz.lam n ≤ Λg) {ε τ' D' D'' : ℝ} (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hε0 : 0 < ε)
    (hε1 : ε < 1) (hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hD'' : (k : ℝ) + 1 < D'') {u u' w : ℝ} (hu0 : 0 ≤ u) (huu' : u ≤ u') (hu'w : u' ≤ w)
    (hwL : w ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - w) / (1 - u')) {E : ℝ} (hE : |E| < 2)
    (hκm : κ' ≤ (mE E).im) {σ : Fin k → Bool} (hσ : ∃ i, σ i = σ (finRotate k i))
    {Γ Λ Φ : ℝ} (hΓ : 0 ≤ Γ) (hΛ : 0 ≤ Λ)
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hM : M ∈ sz.GoodSetN n E u k Γ Λ Φ τ' D')
    (hδ : ((sz.W n : ℕ) : ℝ) ^ (-D') + eeShiftErrN d (sz.L n) (sz.W n) E k u u' ≤
      ((sz.W n : ℕ) : ℝ) ^ (-D''))
    (a : Fin k → Zd d (sz.L n)) :
    qvFormN sz n E u' w σ M a ≤ qvBdNonAltN sz n E k Λg κ' ε Γ Λ D'' u' w := by
  have hMh : M.IsHermitian := hM.1
  obtain ⟨-, -, -, -, -, -, hD4, -, hVb⟩ := hM
  have hL3 := sz.three_le_L n
  have hLpos : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < sz.L n)
  have hgL : 0 < sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := by positivity
  have hu'1 : u' < 1 := by linarith
  have hu1 : u < 1 := by linarith
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hWD' : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D') := Real.rpow_nonneg hW0.le _
  have hWD'' : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'') := Real.rpow_nonneg hW0.le _
  have hWτ : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ τ' := Real.rpow_nonneg hW0.le _
  have hee0 : 0 ≤ eeShiftErrN d (sz.L n) (sz.W n) E k u u' := by
    have h := norm_STeeM_shiftN_le sz n hE hMh huu' hu'1 (k := k) σ (fun _ => 0) (fun _ => 0)
    exact (norm_nonneg _).trans h
  have hηu := etaT_pos hE hu1
  have hηu' := etaT_pos hE hu'1
  have hηle : etaT E u' ≤ etaT E u := RBM.Green.etaT_le_of_le hE huu'
  have hBu : 0 < sz.Bctl n u := Sizes.STBctl_pos sz n hu1
  have hBu' : 0 < sz.Bctl n u' := Sizes.STBctl_pos sz n hu'1
  have hBle : sz.Bctl n u ≤ sz.Bctl n u' := Sizes.STBctl_mono sz n huu' hu'1
  have hG : 0 ≤ Γ * (Γ * Λ) := by
    have : Γ * (Γ * Λ) = Γ ^ 2 * Λ := by ring
    rw [this]
    exact mul_nonneg (sq_nonneg _) hΛ
  have hmono : Γ * (Γ * Λ) * ((sz.Bctl n u) ^ (2 * k) / etaT E u) ≤
      Γ * (Γ * Λ) * ((sz.Bctl n u') ^ (2 * k) / etaT E u') :=
    mul_le_mul_of_nonneg_left (div_le_div₀ (pow_nonneg hBu'.le _)
      (pow_le_pow_left₀ hBu.le hBle _) hηu' hηle) hG
  have hLK : ellT (sz.L n) (sz.lam n) u ≤ ellT (sz.L n) (sz.lam n) u' :=
    nqGood1_ellT_mono _ _ huu' hu'1
  have hshift := fun b b' => norm_STeeM_shiftN_le sz n hE hMh huu' hu'1 σ b b'
  have htri : ∀ b b' : Fin k → Zd d (sz.L n), ‖sz.STeeM n E u' M σ b b'‖ ≤
      ‖sz.STeeM n E u M σ b b'‖ + eeShiftErrN d (sz.L n) (sz.W n) E k u u' := by
    intro b b'
    have h3 : ‖sz.STeeM n E u' M σ b b'‖ ≤ ‖sz.STeeM n E u M σ b b'‖ +
        ‖sz.STeeM n E u' M σ b b' - sz.STeeM n E u M σ b b'‖ := by
      have := norm_add_le (sz.STeeM n E u M σ b b')
        (sz.STeeM n E u' M σ b b' - sz.STeeM n E u M σ b b')
      rwa [add_sub_cancel] at this
    linarith [hshift b b']
  have hT : ∀ b b' : Fin k → Zd d (sz.L n), ‖sz.STeeM n E u' M σ b b'‖ ≤
      Γ * (Γ * Λ) * ((sz.Bctl n u') ^ (2 * k) / etaT E u') + ((sz.W n : ℕ) : ℝ) ^ (-D'') := by
    intro b b'
    have h1 := hD4 σ b b'
    have h2 := htri b b'
    linarith
  have hTfar : ∀ b b' : Fin k → Zd d (sz.L n),
      ellT (sz.L n) (sz.lam n) u' * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf (Fin.append b b') : ℝ) →
        ‖sz.STeeM n E u' M σ b b'‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'') := by
    intro b b' hfar
    have hfar' : ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤
        (STdiamInf (Fin.append b b') : ℝ) := (mul_le_mul_of_nonneg_right hLK hWτ).trans hfar
    have h1 := hVb σ b b' hfar'
    have h2 := htri b b'
    linarith
  have key := nqGood1_qvFormN_le_of_bounds Λg κ' hd hk hΛg hκ' sz n hg hgΛ hW hε0 hε1 hWε hdW hD''
    (hu0.trans huu') hu'w hwL hWt hE.le hκm hσ M
    (Mee := Γ * (Γ * Λ) * ((sz.Bctl n u') ^ (2 * k) / etaT E u') + ((sz.W n : ℕ) : ℝ) ^ (-D''))
    (δ := ((sz.W n : ℕ) : ℝ) ^ (-D'')) hWD'' le_rfl hT hTfar a
  unfold qvBdNonAltN
  exact key

/-- **The majorant `hQ` of `azumaProxy_subG_goodExit` on the good set** (RBM2D `hQ_nonAlt`,
`NonAltGood.lean:1503`; RBM1D `hqv514`, `:1446`, the deterministic part): for `M ∈ GoodSetN(u_j)`
Hermitian, `Δ · (k · qvFormN_{u_{j+1},u_m}(M)) ≤ cQVNonAltN`, under the shift hypothesis
`W^{-D'} + eeShiftErrN(u_j, u_{j+1}) ≤ W^{-D''}`.  All hypotheses are at the fixed `n`; the window
`W⁻¹ ≤ (1-v_n)/(1-s_n)` and `v_n ≤ 1 - g²/L²` give those of the shifted majorant for every
`u_j ≤ u_{j+1} ≤ u_m` on the grid. -/
theorem hQ_nonAltN {d k : ℕ} (Λg κ' : ℝ) (hd : 3 ≤ d) (hk : 2 ≤ k) (hΛg : 0 < Λg)
    (hκ' : 0 < κ') (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hE : |E n| < 2)
    (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1)
    (hwL : v n ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - v n) / (1 - s n)) (hκm : κ' ≤ (mE (E n)).im)
    (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ Λg) {ε τ' D' D'' : ℝ}
    (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hD'' : (k : ℝ) + 1 < D'') {σ : Fin k → Bool} (hσ : ∃ i, σ i = σ (finRotate k i))
    (Γ Λ Φ : ℕ → ℝ) (hΓ : 0 ≤ Γ n) (hΛ : 0 ≤ Λ n) (m : ℕ) (hm : m ≤ K n)
    (a : Fin k → Zd d (sz.L n)) (j : ℕ) (hj : j < m)
    (hδ : ((sz.W n : ℕ) : ℝ) ^ (-D') + eeShiftErrN d (sz.L n) (sz.W n) (E n) k
      (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'')) :
    ∀ M ∈ sz.GoodSetN n (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D',
      M.IsHermitian → gridStep s v K n * ((k : ℝ) * qvFormN sz n (E n)
        (gridTime s v K n (j + 1)) (gridTime s v K n m) σ M a) ≤
        (cQVNonAltN sz E s v K n k Λg κ' ε Γ Λ D'' m a j : ℝ) := by
  intro M hM _
  have hΔ : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n hsv
  have hu0 : 0 ≤ gridTime s v K n j := nqGood2_gridTime_nonneg hs0 hsv j
  have hjj : gridTime s v K n j ≤ gridTime s v K n (j + 1) :=
    ST_gridTime_mono s v K n hsv (Nat.le_succ j)
  have hj1m : gridTime s v K n (j + 1) ≤ gridTime s v K n m :=
    ST_gridTime_mono s v K n hsv (by omega)
  have hmv : gridTime s v K n m ≤ v n := nqGood2_gridTime_le hsv hm
  have hs1 : s n ≤ gridTime s v K n (j + 1) := by
    have h := ST_gridTime_mono s v K n hsv (Nat.zero_le (j + 1))
    rwa [ST_gridTime_zero] at h
  have hj1v : gridTime s v K n (j + 1) ≤ v n := hj1m.trans hmv
  have hwin : (((sz.W n : ℕ) : ℝ))⁻¹ ≤
      (1 - gridTime s v K n m) / (1 - gridTime s v K n (j + 1)) := by
    refine hWt.trans ?_
    exact div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)
  have hq := qvFormN_le_of_goodSetN_shiftN Λg κ' hd hk hΛg hκ' sz n hg hgΛ hW hε0 hε1 hWε hdW
    hD'' hu0 hjj hj1m (hmv.trans hwL) hwin hE hκm hσ hΓ hΛ hM hδ a
  refine le_trans ?_ (Real.le_coe_toNNReal _)
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _)) hΔ

/-- **The `SubGaussStopN` input of `AssembledN` for non-alternating `σ`** (RBM2D
`subGaussStop_nonAlt`, `NonAltGood.lean:1532`): the merged `azumaSubGN` (ST2-34), the test class
`hermTestFunLoopN` and the exit time `goodExitTauN` give, for the stopped propagated first-chaos part
`ZvecN`, sub-Gaussianity with the explicit proxy `cQVNonAltN`.  The `∀ n` premises are those of
`azumaProxy_subG_goodExit`; the other hypotheses are at the fixed `n`; the only extra one is the
shift inequality `W^{-D'} + eeShiftErrN(u_j, u_{j+1}) ≤ W^{-D''}`. -/
theorem subGaussStop_nonAltN {d k : ℕ} (Λg κ' : ℝ) (hd : 3 ≤ d) (hk : 2 ≤ k) (hΛg : 0 < Λg)
    (hκ' : 0 < κ') (sz : Sizes d) {E s v : ℕ → ℝ} {K : ℕ → ℕ} (hE : ∀ n, |E n| < 2)
    (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1) (n : ℕ)
    (hwL : v n ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - v n) / (1 - s n)) (hκm : κ' ≤ (mE (E n)).im)
    (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ Λg) {ε τ' D' D'' : ℝ}
    (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hD'' : (k : ℝ) + 1 < D'') {σ : Fin k → Bool} (hσ : ∃ i, σ i = σ (finRotate k i))
    (Γ Λ Φ : ℕ → ℝ) (hΓ : 0 ≤ Γ n) (hΛ : 0 ≤ Λ n) (m : ℕ) (hm : m ≤ K n)
    (a : Fin k → Zd d (sz.L n)) (j : ℕ) (hj : j < m)
    (hδ : ((sz.W n : ℕ) : ℝ) ^ (-D') + eeShiftErrN d (sz.L n) (sz.W n) (E n) k
      (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'')) :
    SubGaussStopN sz (E n) σ (gridTime s v K n)
      (goodExitTauN sz E s v K k Γ Λ Φ τ' D' n) (fun j ω => ZvecN sz E s v K n j σ ω) m a j
      (cQVNonAltN sz E s v K n k Λg κ' ε Γ Λ D'' m a j) :=
  azumaProxy_subG_goodExit sz (azumaSubGN sz s v K) hE hs0 hsv hv1 n k hk σ Γ Λ Φ τ' D' m hm a j hj
    (cQVNonAltN sz E s v K n k Λg κ' ε Γ Λ D'' m a j)
    (hQ_nonAltN Λg κ' hd hk hΛg hκ' sz E s v K n (hE n) (hs0 n) (hsv n) (hv1 n) hwL hWt hκm hg hgΛ
      hW hε0 hε1 hWε hdW hD'' hσ Γ Λ Φ hΓ hΛ m hm a j hj hδ)

/-- **The field `hc_pos`** (RBM1D `cQV514_sum_pos`, `:1511`; RBM2D `cQVNonAlt_sum_pos`,
`NonAltGood.lean:1549`): `Σ_{j<m} c_j > 0` for `Δ > 0`, i.e. `s_n < v_n`, `K_n ≠ 0` (the field needs
the strict window; `AssembledN` gives only `0 ≤ Δ`). -/
theorem cQVNonAltN_sum_pos {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (Λg κ' ε : ℝ) (hk : 1 ≤ k) (hsv : s n < v n) (hv1 : v n < 1)
    (hK : K n ≠ 0) (Γ Λ : ℕ → ℝ) (hΛ : 0 ≤ Λ n) (D'' : ℝ) :
    ∀ m, 1 ≤ m → m ≤ K n → ∀ a : Fin k → Zd d (sz.L n),
      0 < ∑ j ∈ Finset.range m,
        (cQVNonAltN sz E s v K n k Λg κ' ε Γ Λ D'' m a j : ℝ) := by
  intro m hm1 hmK a
  have hΔ : 0 < gridStep s v K n :=
    div_pos (by linarith) (by exact_mod_cast Nat.pos_of_ne_zero hK)
  have hterm : ∀ j ∈ Finset.range m,
      0 ≤ (cQVNonAltN sz E s v K n k Λg κ' ε Γ Λ D'' m a j : ℝ) := fun j _ => NNReal.coe_nonneg _
  have h0 : (0 : ℕ) ∈ Finset.range m := Finset.mem_range.mpr (by omega)
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum hterm h0)
  have hu1 : gridTime s v K n (0 + 1) ≤ 1 :=
    ((nqGood2_gridTime_le hsv.le (show 0 + 1 ≤ K n by omega)).trans hv1.le)
  have hpos := qvBdNonAltN_pos sz n (E := E n) (k := k) (Λg := Λg) (κ' := κ') (ε := ε) (Γ := Γ n)
    (D'' := D'') (u := gridTime s v K n (0 + 1)) (w := gridTime s v K n m) hΛ hu1
  unfold cQVNonAltN
  rw [Real.coe_toNNReal _ (mul_pos hΔ (mul_pos (by exact_mod_cast hk) hpos)).le]
  exact mul_pos hΔ (mul_pos (by exact_mod_cast hk) hpos)

end QVConst

/-! ## 5. Compiled nonempty instances at `d = 3`

Data (the merged instance data of `GridGoodN` §7 and `AzumaProxyN` §6, and `NQGood1` §6): `sz0` (`n = 0`:
`L = 4`, `W = 32`, `lam = 1/64`), `E ≡ 1/2` (`Im m = √15/4 ≈ 0.968`), `s ≡ 0`, `v ≡ 1/32`, `K ≡ 4` (`Δ = 1/128`,
`u_j = j/128`), `k = 3`, `σ = (+,-,+)` (`σ_2 = σ_0` cyclically: non-alternating), levels `(Γ, Λ, Φ) =
(4, 3, 1)` (D366: `Γ²Λ = 48 ≥ 3(1+g²)^6`; `zero_mem_goodSetN_inst_grid`), `τ' = 1/5`, `ε = 4/5`
(`W^ε = 16`, `W^{τ'} = 2`, `d W^{τ'} = 6 ≤ 16`), `D' = Dc = 6`, `D'' = 5`, `Λ_g = 10`, `κ' = 1/2`; the
exit time is `τ = goodExitTauN … (1/5) 6 0` and the label vector of the far clauses is `aFar` (`diam_∞ = 2`).
The constant `C = nqGood1C 3 3 10 (1/2)` stays abstract (`Classical.choose` of EK-6; only `C > 0` is
known), so every instance holds for the actual `C`. -/

namespace NQGood2Inst

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.GridGoodNInst
  RBM.Ind.AzumaProxyNInst RBM.Ind.NQGood1Inst

private theorem W0 : ((sz0.W 0 : ℕ) : ℝ) = 32 := by rw [sz0_values.2.1]; norm_num

private theorem lam0 : sz0.lam 0 = 1 / 64 := sz0_values.2.2.2

private theorem L0 : sz0.L 0 = 4 := sz0_values.1

private theorem L0r : ((sz0.L 0 : ℕ) : ℝ) = 4 := by rw [L0]; norm_num

private theorem rpow32_fifth : (32 : ℝ) ^ ((1 : ℝ) / 5) = 2 := by
  have : (32 : ℝ) = 2 ^ (5 : ℝ) := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  rw [this, ← Real.rpow_mul (by norm_num)]; norm_num

private theorem rpow32_four_fifth : (32 : ℝ) ^ ((4 : ℝ) / 5) = 16 := by
  have : (32 : ℝ) = 2 ^ (5 : ℝ) := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  rw [this, ← Real.rpow_mul (by norm_num)]
  rw [show (5 : ℝ) * (4 / 5) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num

private theorem rpow32_neg (m : ℕ) : (32 : ℝ) ^ (-(m : ℝ)) = ((32 : ℝ) ^ m)⁻¹ := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]

private theorem abs_half : |(1 / 2 : ℝ)| < 2 := by norm_num [abs_of_pos]

private theorem im_mE_half : (1 / 2 : ℝ) ≤ (mE (1 / 2)).im := by
  have h := nqGood1_mE_im_ge (E := 1 / 2) (κ := 1 / 2) (by norm_num) (by norm_num [abs_of_pos])
  rwa [show min (1 / 2 : ℝ) (4 / 5) = 1 / 2 by norm_num] at h

private theorem im_mE_nine : (9 / 10 : ℝ) ≤ (mE (1 / 2)).im := by
  rw [mE_im]
  have : (9 / 5 : ℝ) ≤ Real.sqrt (4 - (1 / 2) ^ 2) := by
    calc (9 / 5 : ℝ) = Real.sqrt ((9 / 5) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by norm_num)
  linarith

private theorem hσ3 : ∃ i : Fin 3, sig3 i = sig3 (finRotate 3 i) := ⟨2, by decide⟩

private theorem hW1 : 1 < ((sz0.W 0 : ℕ) : ℝ) := by rw [W0]; norm_num

private theorem hW1' : (1 : ℝ) ≤ ((sz0.W 0 : ℕ) : ℝ) := hW1.le

private theorem hW0 : (0 : ℝ) ≤ ((sz0.W 0 : ℕ) : ℝ) := by rw [W0]; norm_num

private theorem hWε : 4 ≤ ((sz0.W 0 : ℕ) : ℝ) ^ (4 / 5 : ℝ) := by
  rw [W0, rpow32_four_fifth]; norm_num

private theorem hdW : ((3 : ℕ) : ℝ) * ((sz0.W 0 : ℕ) : ℝ) ^ (1 / 5 : ℝ) ≤
    ((sz0.W 0 : ℕ) : ℝ) ^ (4 / 5 : ℝ) := by
  rw [W0, rpow32_fifth, rpow32_four_fifth]; norm_num

/-- The grid times of the data: `u_j = j/128` (`s ≡ 0`, `Δ = 1/128`). -/
theorem gridTime_inst (j : ℕ) : gridTime sInst vg Kg 0 j = (j : ℝ) / 128 := by
  have h := grid_data.1
  simp only [gridTime, sInst, h]
  ring

private theorem u_le_of_le (j : ℕ) (hj : j ≤ 4) : gridTime sInst vg Kg 0 j ≤ 1 / 32 := by
  rw [gridTime_inst]
  have : (j : ℝ) ≤ 4 := by exact_mod_cast hj
  linarith

private theorem u_nonneg (j : ℕ) : 0 ≤ gridTime sInst vg Kg 0 j := by
  rw [gridTime_inst]; positivity

private theorem u_lt_one (j : ℕ) (hj : j ≤ 4) : gridTime sInst vg Kg 0 j < 1 :=
  (u_le_of_le j hj).trans_lt (by norm_num)

private theorem u_mono (i m : ℕ) (him : i ≤ m) :
    gridTime sInst vg Kg 0 i ≤ gridTime sInst vg Kg 0 m := by
  rw [gridTime_inst, gridTime_inst]
  have : (i : ℝ) ≤ m := by exact_mod_cast him
  linarith

private theorem hwL : gridTime sInst vg Kg 0 4 ≤
    1 - sz0.lam 0 ^ 2 / ((sz0.L 0 : ℕ) : ℝ) ^ 2 := by
  rw [grid_data.2.2.2, lam0, L0r]; norm_num

private theorem hvL : vg 0 ≤ 1 - sz0.lam 0 ^ 2 / ((sz0.L 0 : ℕ) : ℝ) ^ 2 := by
  have : vg 0 = 1 / 32 := rfl
  rw [this, lam0, L0r]; norm_num

private theorem hWt : (((sz0.W 0 : ℕ) : ℝ))⁻¹ ≤
    (1 - gridTime sInst vg Kg 0 4) / (1 - gridTime sInst vg Kg 0 0) := by
  rw [grid_data.2.2.2, grid_data.2.1, W0]; norm_num

/-! ### Target 2: (5.93) at `d ≥ 3` -/

/-- **Instance of `nqGood2_ratio_mul_Bctl_le`** at `(u_i, u_4)`, every `i ≤ 4` (in particular
`(u_0, u_4)` and `(u_1, u_4)`; `g = 1/64 > 0`, so the second term of `Bparam` has the strict defect
`g²(t-u) > 0` for `i < 4`). -/
theorem ratio_instance (i : ℕ) (hi : i ≤ 4) :
    ((sz0.lam 0 ^ 2 + |1 - gridTime sInst vg Kg 0 i|) /
        (sz0.lam 0 ^ 2 + |1 - gridTime sInst vg Kg 0 4|)) * sz0.Bctl 0 (gridTime sInst vg Kg 0 i) ≤
      sz0.Bctl 0 (gridTime sInst vg Kg 0 4) :=
  nqGood2_ratio_mul_Bctl_le sz0 0 (u_mono i 4 hi) (u_lt_one 4 le_rfl)

/-- **Instance of `kappaNonAltN_mul_Bctl_pow_le`** at `(u_i, u_4)`, `k = 3`, `ε = 4/5`, `W = 32`. -/
theorem kappa_Bctl_instance (i : ℕ) (hi : i ≤ 4) :
    kappaNonAltN 3 3 10 (1 / 2) (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (4 / 5) (gridTime sInst vg Kg 0) i 4 *
        (sz0.Bctl 0 (gridTime sInst vg Kg 0 i)) ^ 3 ≤
      ((sz0.W 0 : ℕ) : ℝ) ^ (nqGood1C 3 3 10 (1 / 2) * (4 / 5)) *
        (sz0.Bctl 0 (gridTime sInst vg Kg 0 4)) ^ 3 :=
  kappaNonAltN_mul_Bctl_pow_le sz0 0 3 10 (1 / 2) (4 / 5) hW0 (gridTime sInst vg Kg 0)
    (u_mono i 4 hi) (u_lt_one 4 le_rfl)

/-- **Instance of `kappaNonAltN_succ_mul_Bctl_pow_le`** at `(u_j, u_{j+1}, u_4)`, every `j < 4`. -/
theorem kappa_succ_instance (j : ℕ) (hj : j < 4) :
    kappaNonAltN 3 3 10 (1 / 2) (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (4 / 5) (gridTime sInst vg Kg 0)
        (j + 1) 4 * (sz0.Bctl 0 (gridTime sInst vg Kg 0 j)) ^ 3 ≤
      ((sz0.W 0 : ℕ) : ℝ) ^ (nqGood1C 3 3 10 (1 / 2) * (4 / 5)) *
        (sz0.Bctl 0 (gridTime sInst vg Kg 0 4)) ^ 3 :=
  kappaNonAltN_succ_mul_Bctl_pow_le sz0 0 3 10 (1 / 2) (4 / 5) hW0 (gridTime sInst vg Kg 0) j 4
    (u_mono j (j + 1) (Nat.le_succ j)) (u_mono (j + 1) 4 (by omega)) (u_lt_one 4 le_rfl)

/-! ### Target 3: the fields of `GridAssemblyHypN` -/

/-- The class radius at `u_0`: `ℓ_{u_0} W^{τ'} = 1 · 2 = 2`. -/
private theorem ell_u0 : ellT (sz0.L 0) (sz0.lam 0) (gridTime sInst vg Kg 0 0) = 1 := by
  rw [grid_data.2.1, lam0, L0]; norm_num [ellT]

/-- `ℓ_{u_1} = 1` (`g/√(1-u_1) = (1/64)/√(127/128) ≤ 1`, `L = 4`). -/
private theorem ell_u1 : ellT (sz0.L 0) (sz0.lam 0) (gridTime sInst vg Kg 0 1) = 1 := by
  rw [grid_data.2.2.1, lam0, L0]
  unfold ellT
  have h1 : (1 / 64 : ℝ) / Real.sqrt |1 - 1 / 128| ≤ 1 := by
    rw [div_le_one (Real.sqrt_pos.2 (by norm_num [abs_of_pos]))]
    exact Real.le_sqrt_of_sq_le (by norm_num [abs_of_pos])
  rw [max_eq_right h1]
  norm_num

/-- **Instance of `nonAlt_hkerN`** (the field `hker`) at `d = 3`, `k = 3`, `L = 4`, `g = 1/64`,
`W = 32`, `ε = 4/5`, `τ' = 1/5`, `Dc = 6`, the grid `u_j = j/128`, `K = 4`, `E = 1/2`,
`σ = (+,-,+)`, `Λ_g = 10`, `κ' = 1/2`. -/
theorem hker_field_instance :
    ∀ i m, i ≤ m → m ≤ Kg 0 → ∀ (X : (Fin 3 → Zd 3 (sz0.L 0)) → ℂ) (M δ : ℝ), 0 ≤ M → 0 ≤ δ →
      (∀ b, ‖X b‖ ≤ M) →
      nonAltClsN 3 (sz0.L 0) (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (1 / 5) 6 (gridTime sInst vg Kg 0)
        i δ X →
      ∀ a : Fin 3 → Zd 3 (sz0.L 0),
      ‖Ugen 3 (sz0.L 0) (sz0.lam 0) (Einst 0) sig3 (gridTime sInst vg Kg 0 i)
          (gridTime sInst vg Kg 0 m) X a‖ ≤
        kappaNonAltN 3 3 10 (1 / 2) (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (4 / 5)
            (gridTime sInst vg Kg 0) i m * M +
          epsNonAltN 3 3 10 (1 / 2) ((sz0.W 0 : ℕ) : ℝ) i m * δ :=
  nonAlt_hkerN (d := 3) (k := 3) 10 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sz0.three_le_L 0) (g := sz0.lam 0) (by rw [lam0]; norm_num)
    (by rw [lam0]; norm_num) hW1 (by norm_num) (by norm_num) hWε hdW (by norm_num)
    (K := Kg 0) (u := gridTime sInst vg Kg 0) (fun i _ => u_nonneg i)
    (fun i m him _ => u_mono i m him) hwL hWt (E := Einst 0) (abs_half.le) im_mE_half hσ3

/-- The tensor `Xinst` (`‖Xinst b‖ ≤ 1`, `Xinst_0 = 1`, zero beyond `diam_∞ ≥ 2`) is in the class
`nonAltClsN` at index `0` with `δ = W^{-6}`. -/
theorem Xinst_cls :
    nonAltClsN 3 (sz0.L 0) (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (1 / 5) 6 (gridTime sInst vg Kg 0) 0
      (((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ))) Xinst :=
  ⟨le_rfl, fun b hb => Xinst_far b (by rw [grid_data.2.1] at hb; exact hb)⟩

/-- **`nonAlt_hkerN` applied** to the nonzero tensor `Xinst` (`M = 1`, `δ = W^{-6}`), from `u_0` to `u_4`,
at the far label vector `aFar`: the bound `κ_{0,4} · 1 + ε_{0,4} · W^{-6}`. -/
theorem hker_applied :
    ‖Ugen 3 (sz0.L 0) (sz0.lam 0) (Einst 0) sig3 (gridTime sInst vg Kg 0 0)
        (gridTime sInst vg Kg 0 4) Xinst aFar‖ ≤
      kappaNonAltN 3 3 10 (1 / 2) (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (4 / 5)
          (gridTime sInst vg Kg 0) 0 4 * 1 +
        epsNonAltN 3 3 10 (1 / 2) ((sz0.W 0 : ℕ) : ℝ) 0 4 * ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ)) :=
  hker_field_instance 0 4 (Nat.zero_le _) le_rfl Xinst 1 (((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ)))
    zero_le_one (Real.rpow_nonneg hW0 _) Xinst_norm_le Xinst_cls aFar

/-- The exit time of the data: levels `(4, 3, 1)`, `k = 3`, `τ' = 1/5`, `D' = 6`. -/
def tau0 : PathΩ sz0 → ℕ := goodExitTauN sz0 Einst sInst vg Kg 3 Γ4 Λ3 Φ1 (1 / 5) 6 0

/-- The grid state is in `GoodSetN` strictly before the exit time. -/
theorem tau0_mem (ω : PathΩ sz0) (j : ℕ) (hj : j < tau0 ω) :
    pathH sz0 sInst vg Kg 0 j ω ∈ sz0.GoodSetN 0 (Einst 0) (gridTime sInst vg Kg 0 j) 3 (Γ4 0)
      (Λ3 0) (Φ1 0) (1 / 5) 6 :=
  mem_of_lt_gridExitTauN hj

/-- **The event `{0 < τ}` is everything** (nondegeneracy of `hA0cls`): `H_0 = 0` is a member of
`GoodSetN` at `u_0` (`zero_mem_goodSetN_inst_grid`, the levels `(4, 3, 1)` of D366). -/
theorem tau0_pos (ω : PathΩ sz0) : 0 < tau0 ω := by
  refine azumaProxy_pos_gridExitTauN sz0 (by norm_num [Kg]) ?_
  rw [azumaProxy_pathH_zero_of_s_zero sz0 sInst vg Kg 0 rfl ω]
  exact zero_mem_goodSetN_inst_grid

/-- **Instance of `goodSetN_A0clsN`**: `H_0 = 0 ∈ GoodSetN` at `u_0`, the initial tensor has the
class `nonAltClsN` at index `0` with `δ = W^{-6}`. -/
theorem A0cls_instance :
    nonAltClsN 3 (sz0.L 0) (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (1 / 5) 6 (gridTime sInst vg Kg 0) 0
      (((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ)))
      (fun a => sz0.STLKM 0 (Einst 0) (gridTime sInst vg Kg 0 0)
        (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) sig3 a) :=
  goodSetN_A0clsN sz0 (by norm_num) (le_refl _) hW1' zero_mem_goodSetN_inst_grid sig3

/-- **Instance of `goodSetN_driftClsN`**: the drift tensor of `H_0 = 0` at `u_0` is in the class of
index `1` (radius `ℓ_{u_1} W^{τ'}`), `δ = W^{-6}`. -/
theorem driftCls_instance :
    nonAltClsN 3 (sz0.L 0) (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (1 / 5) 6 (gridTime sInst vg Kg 0) 1
      (((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ)))
      (driftTensorN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 0)
        (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) sig3) :=
  goodSetN_driftClsN sz0 (le_refl _) hW1' (u_mono 0 1 (by norm_num)) (u_lt_one 1 (by norm_num))
    zero_mem_goodSetN_inst_grid sig3

/-- **Instance of `nonAlt_hA0clsN`** on `{0 < τ}` (every sample, `tau0_pos`). -/
theorem hA0cls_instance :
    ∀ ω, 0 < tau0 ω →
      nonAltClsN 3 (sz0.L 0) (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (1 / 5) 6 (gridTime sInst vg Kg 0) 0
        (((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ))) (AvecN sz0 Einst sInst vg Kg 0 0 sig3 ω) :=
  nonAlt_hA0clsN sz0 (n := 0) (k := 3) (by norm_num) hW1' sig3 Einst sInst vg Kg Γ4 Λ3 Φ1 (1 / 5)
    6 6 le_rfl tau0 (fun ω j hj => tau0_mem ω j hj)

/-- **The far clause of `hA0cls` at `aFar`** (`ℓ_{u_0} W^{1/5} = 2 ≤ diam_∞ aFar = 2`): on `{0 < τ}` the
initial tensor `A_0` is `≤ W^{-6}` at the label vector `aFar`. -/
theorem hA0cls_far_instance (ω : PathΩ sz0) :
    ‖AvecN sz0 Einst sInst vg Kg 0 0 sig3 ω aFar‖ ≤ ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ)) := by
  refine (hA0cls_instance ω (tau0_pos ω)).2 aFar ?_
  rw [ell_u0, W0, rpow32_fifth]
  have := diam_aFar
  exact_mod_cast (by omega : (1 : ℕ) * 2 ≤ STdiamInf aFar)

/-- **Instance of `nonAlt_hdriftN`**: `‖Dr_j(b)‖ ≤ dDriftNonAltN` on `{j < τ}`, `j < 4`. -/
theorem hdrift_instance :
    ∀ ω j, j < Kg 0 → j < tau0 ω → ∀ b : Fin 3 → Zd 3 (sz0.L 0),
      ‖driftTensorN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 j) (pathH sz0 sInst vg Kg 0 j ω) sig3 b‖ ≤
        dDriftNonAltN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 j) 3 (Γ4 0) (Φ1 0) :=
  nonAlt_hdriftN sz0 (n := 0) (k := 3) (by norm_num) sig3 Einst sInst vg Kg Γ4 Λ3 Φ1 (1 / 5) 6 tau0
    (fun ω j hj => tau0_mem ω j hj)

/-- **Instance of `nonAlt_hDclsN`**: the drift tensor at `(u_j, H_j)` is in the class of index
`j + 1` on `{j < τ}`. -/
theorem hDcls_instance :
    ∀ ω j, j < Kg 0 → j < tau0 ω →
      nonAltClsN 3 (sz0.L 0) (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (1 / 5) 6 (gridTime sInst vg Kg 0)
        (j + 1) (((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ)))
        (driftTensorN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 j) (pathH sz0 sInst vg Kg 0 j ω)
          sig3) :=
  nonAlt_hDclsN sz0 (n := 0) (k := 3) Einst sInst vg Kg (sInst_le_vg 0) (vg_lt_one 0) hW1' sig3
    Γ4 Λ3 Φ1 (1 / 5) 6 6 le_rfl tau0 (fun ω j hj => tau0_mem ω j hj)

/-- **The far clause of `hDcls` at `aFar`** (`ℓ_{u_1} W^{1/5} = 2 ≤ diam_∞ aFar = 2`): on `{0 < τ}`
the drift tensor `Dr_0` is `≤ W^{-6}` at the label vector `aFar` (the class is not vacuous there). -/
theorem hDcls_far_instance (ω : PathΩ sz0) :
    ‖driftTensorN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 0) (pathH sz0 sInst vg Kg 0 0 ω) sig3
        aFar‖ ≤ ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ)) := by
  refine (hDcls_instance ω 0 (by norm_num [Kg]) (tau0_pos ω)).2 aFar ?_
  rw [ell_u1, W0, rpow32_fifth]
  have := diam_aFar
  exact_mod_cast (by omega : (1 : ℕ) * 2 ≤ STdiamInf aFar)

/-- **Instance of `nonAlt_hκ0N`** and **`nonAlt_hε0N`**. -/
theorem hκ0_instance :
    ∀ i m, i ≤ m → m ≤ Kg 0 → 0 ≤ kappaNonAltN 3 3 10 (1 / 2) (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ)
      (4 / 5) (gridTime sInst vg Kg 0) i m :=
  nonAlt_hκ0N 3 3 10 (1 / 2) (sz0.lam 0) _ (4 / 5) hW0 (Kg 0) _

theorem hε0_instance :
    ∀ i m, i ≤ m → m ≤ Kg 0 → 0 ≤ epsNonAltN 3 3 10 (1 / 2) ((sz0.W 0 : ℕ) : ℝ) i m :=
  nonAlt_hε0N 3 3 10 (1 / 2) _ hW0 (Kg 0)

/-- **Instance of `nonAlt_hdDrift0N`** (`Γ = 4`, `Φ = 1`, `k = 3`, `|E| = 1/2 < 2`). -/
theorem hdDrift0_instance :
    ∀ (_ : PathΩ sz0) (j : ℕ), j < Kg 0 →
      0 ≤ dDriftNonAltN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 j) 3 (Γ4 0) (Φ1 0) :=
  nonAlt_hdDrift0N sz0 (n := 0) (k := 3) Einst sInst vg Kg (by norm_num) (Einst_abs_lt 0)
    (sInst_le_vg 0) (vg_lt_one 0) Γ4 Φ1 (by norm_num) (by norm_num)


/-! ### Target 4: the quadratic-variation constant -/

/-- `η_{u'} ≥ 4/5` for `0 ≤ u' ≤ 1/32` (`Im m(1/2) ≥ 9/10`). -/
private theorem etaT_ge (u : ℝ) (hu : u ≤ 1 / 32) : 4 / 5 ≤ etaT (1 / 2) u := by
  unfold etaT
  have := im_mE_nine
  nlinarith

/-- `eeShiftErrN` at the data is tiny: for `0 ≤ u ≤ u' ≤ 1/32`, `eeShiftErrN ≤ 10^{-20}`
(`W^d k L^d · ℓ η^{-(ℓ+1)} (W^{-d})^{ℓ-1} Δ` with `ℓ = 8`, `η ≥ 4/5`, `Δ ≤ 1/32`, `(W^{-3})^7 = 2^{-105}`). -/
theorem eeShiftErrN_inst_le {u u' : ℝ} (hu : 0 ≤ u) (huu' : u ≤ u') (hu' : u' ≤ 1 / 32) :
    eeShiftErrN 3 (sz0.L 0) (sz0.W 0) (1 / 2) 3 u u' ≤ 1 / 10 ^ 20 := by
  have hη := etaT_ge u' hu'
  have hη0 : 0 < etaT (1 / 2) u' := by linarith
  have hx : (etaT (1 / 2) u')⁻¹ ≤ 5 / 4 := by
    calc (etaT (1 / 2) u')⁻¹ ≤ ((4 : ℝ) / 5)⁻¹ := inv_anti₀ (by norm_num) hη
      _ = 5 / 4 := by norm_num
  have hx0 : 0 ≤ (etaT (1 / 2) u')⁻¹ := inv_nonneg.2 hη0.le
  have hΔ0 : 0 ≤ u' - u := by linarith
  have hΔ : u' - u ≤ 1 / 32 := by linarith
  have hle : loopShiftErrN 3 (sz0.W 0) (etaT (1 / 2) u') (2 * 3 + 2) (u' - u) ≤
      ((2 * 3 + 2 : ℕ) : ℝ) * (((5 : ℝ) / 4) ^ (2 * 3 + 2 + 1) *
        ((((32 : ℕ) : ℝ) ^ 3)⁻¹) ^ (2 * 3 + 2 - 1) * (1 / 32)) := by
    unfold loopShiftErrN
    rw [sz0_values.2.1]
    gcongr
  unfold eeShiftErrN
  rw [sz0_values.2.1, sz0_values.1]
  rw [sz0_values.2.1] at hle
  have h1 : (((32 : ℕ) : ℝ) ^ 3) * (((3 : ℕ) : ℝ) * ((((4 : ℕ) : ℝ) ^ 3) *
      loopShiftErrN 3 32 (etaT (1 / 2) u') (2 * 3 + 2) (u' - u))) ≤
      (((32 : ℕ) : ℝ) ^ 3) * (((3 : ℕ) : ℝ) * ((((4 : ℕ) : ℝ) ^ 3) *
        (((2 * 3 + 2 : ℕ) : ℝ) * (((5 : ℝ) / 4) ^ (2 * 3 + 2 + 1) *
          ((((32 : ℕ) : ℝ) ^ 3)⁻¹) ^ (2 * 3 + 2 - 1) * (1 / 32))))) := by
    gcongr
  refine h1.trans ?_
  norm_num

/-- **The shift hypothesis at the data** (`D' = 6`, `D'' = 5`): `W^{-6} + eeShiftErrN(u_j, u_{j+1}) ≤
W^{-5}` for every `j < 4` (`W^{-5} - W^{-6} = 2.89·10^{-8} ≥ 10^{-20}`). -/
theorem delta_shift_ok (j : ℕ) (hj : j < Kg 0) :
    ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ)) +
        eeShiftErrN 3 (sz0.L 0) (sz0.W 0) (Einst 0) 3 (gridTime sInst vg Kg 0 j)
          (gridTime sInst vg Kg 0 (j + 1)) ≤ ((sz0.W 0 : ℕ) : ℝ) ^ (-(5 : ℝ)) := by
  have hj4 : j < 4 := hj
  have h := eeShiftErrN_inst_le (u_nonneg j) (u_mono j (j + 1) (Nat.le_succ j))
    (u_le_of_le (j + 1) (by omega))
  have h6 : ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ)) = ((32 : ℝ) ^ 6)⁻¹ := by
    have := rpow32_neg 6
    simp only [Nat.cast_ofNat] at this
    rw [W0, this]
  have h5 : ((sz0.W 0 : ℕ) : ℝ) ^ (-(5 : ℝ)) = ((32 : ℝ) ^ 5)⁻¹ := by
    have := rpow32_neg 5
    simp only [Nat.cast_ofNat] at this
    rw [W0, this]
  rw [h6, h5]
  have h' : eeShiftErrN 3 (sz0.L 0) (sz0.W 0) (Einst 0) 3 (gridTime sInst vg Kg 0 j)
      (gridTime sInst vg Kg 0 (j + 1)) ≤ 1 / 10 ^ 20 := h
  refine (add_le_add le_rfl h').trans ?_
  norm_num

/-- **Instance of `qvBdNonAltN_pos`** at `(u_1, u_4)`. -/
theorem qvBd_pos_instance :
    0 < qvBdNonAltN sz0 0 (Einst 0) 3 10 (1 / 2) (4 / 5) (Γ4 0) (Λ3 0) 5
      (gridTime sInst vg Kg 0 1) (gridTime sInst vg Kg 0 4) :=
  qvBdNonAltN_pos sz0 0 (E := Einst 0) (by norm_num)
    (u_lt_one 1 (by norm_num)).le

/-- **Instance of `qvFormN_le_of_goodSetN_shiftN`**: `M = H_0 = 0 ∈ GoodSetN` at `u_0 = 0` (levels
`(4, 3, 1)`, `D' = 6`), the shifted time `u' = u_1`, the end time `w = u_4`, `D'' = 5`, the far label
vector `aFar`; the shift hypothesis is `delta_shift_ok 0`. -/
theorem qvFormN_shift_instance :
    qvFormN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 1) (gridTime sInst vg Kg 0 4) sig3
        (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) aFar ≤
      qvBdNonAltN sz0 0 (Einst 0) 3 10 (1 / 2) (4 / 5) (Γ4 0) (Λ3 0) 5
        (gridTime sInst vg Kg 0 1) (gridTime sInst vg Kg 0 4) := by
  have hδ := delta_shift_ok 0 (by norm_num [Kg])
  rw [grid_data.2.1] at hδ
  refine qvFormN_le_of_goodSetN_shiftN (d := 3) (k := 3) 10 (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) sz0 0 (by rw [lam0]; norm_num) (by rw [lam0]; norm_num) hW1
    (by norm_num) (by norm_num) hWε hdW (by norm_num) (u := 0) (u' := gridTime sInst vg Kg 0 1)
    (w := gridTime sInst vg Kg 0 4) le_rfl (by rw [← grid_data.2.1]; exact u_mono 0 1 (by norm_num))
    (u_mono 1 4 (by norm_num)) hwL ?_ (E := 1 / 2) abs_half im_mE_half hσ3 (Γ := 4) (Λ := 3) (Φ := 1)
    (by norm_num) (by norm_num) (τ' := 1 / 5) (D' := 6) ?_ hδ aFar
  · rw [grid_data.2.2.1, grid_data.2.2.2, W0]; norm_num
  · have := zero_mem_goodSetN_inst
    exact this

/-- **Instance of `hQ_nonAltN`** at `(j, m)`, `j < m ≤ 4`, every label vector `a`: the majorant of
`azumaProxy_subG_goodExit` on `GoodSetN … u_j` with value `cQVNonAltN`. -/
theorem hQ_instance (m : ℕ) (hm : m ≤ Kg 0) (j : ℕ) (hj : j < m) (a : Fin 3 → Zd 3 (sz0.L 0)) :
    ∀ M ∈ sz0.GoodSetN 0 (Einst 0) (gridTime sInst vg Kg 0 j) 3 (Γ4 0) (Λ3 0) (Φ1 0) (1 / 5) 6,
      M.IsHermitian → gridStep sInst vg Kg 0 * (((3 : ℕ) : ℝ) *
        qvFormN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 (j + 1)) (gridTime sInst vg Kg 0 m) sig3 M a) ≤
        (cQVNonAltN sz0 Einst sInst vg Kg 0 3 10 (1 / 2) (4 / 5) Γ4 Λ3 5 m a j : ℝ) :=
  hQ_nonAltN (d := 3) (k := 3) 10 (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    sz0 Einst sInst vg Kg 0 (Einst_abs_lt 0) (sInst_nonneg 0) (sInst_le_vg 0) (vg_lt_one 0) hvL
    (by rw [W0]; norm_num [sInst, vg]) im_mE_half (by rw [lam0]; norm_num) (by rw [lam0]; norm_num)
    hW1 (by norm_num) (by norm_num) hWε hdW (by norm_num) hσ3 Γ4 Λ3 Φ1 (by norm_num) (by norm_num) m hm
    a j hj (delta_shift_ok j (hj.trans_le hm))

/-- `hQ_instance` at the concrete member `M = H_0 = 0` (`m = 4`, `j = 0`, `a = aFar`). -/
theorem hQ_instance_zero :
    gridStep sInst vg Kg 0 * (((3 : ℕ) : ℝ) *
      qvFormN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 (0 + 1)) (gridTime sInst vg Kg 0 4) sig3
        (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) aFar) ≤
      (cQVNonAltN sz0 Einst sInst vg Kg 0 3 10 (1 / 2) (4 / 5) Γ4 Λ3 5 4 aFar 0 : ℝ) :=
  hQ_instance 4 le_rfl 0 (by norm_num) aFar 0 zero_mem_goodSetN_inst_grid Matrix.isHermitian_zero

/-- **Instance of `subGaussStop_nonAltN`**: the `SubGaussStopN` input of `AssembledN` at the
**same** exit time `τ = tau0` and the **same** proxy `c = cQVNonAltN` for every `m ≤ 4`, `j < m` and
every label vector `a`. -/
theorem subGaussStop_instance (m : ℕ) (hm : m ≤ Kg 0) (a : Fin 3 → Zd 3 (sz0.L 0)) (j : ℕ)
    (hj : j < m) :
    SubGaussStopN sz0 (Einst 0) sig3 (gridTime sInst vg Kg 0) tau0
      (fun j ω => ZvecN sz0 Einst sInst vg Kg 0 j sig3 ω) m a j
      (cQVNonAltN sz0 Einst sInst vg Kg 0 3 10 (1 / 2) (4 / 5) Γ4 Λ3 5 m a j) :=
  subGaussStop_nonAltN (d := 3) (k := 3) 10 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) sz0 (E := Einst) (s := sInst) (v := vg) (K := Kg) Einst_abs_lt sInst_nonneg
    sInst_le_vg vg_lt_one 0 hvL (by rw [W0]; norm_num [sInst, vg]) im_mE_half
    (by rw [lam0]; norm_num) (by rw [lam0]; norm_num) hW1 (by norm_num) (by norm_num) hWε hdW
    (by norm_num) hσ3 Γ4 Λ3 Φ1 (by norm_num) (by norm_num) m hm a j hj
    (delta_shift_ok j (hj.trans_le hm))

/-- **Instance of `cQVNonAltN_sum_pos`** (the field `hc_pos`): `Σ_{j<m} c_j > 0` for every
`1 ≤ m ≤ 4` (`Δ = 1/128 > 0`). -/
theorem hc_pos_instance :
    ∀ m, 1 ≤ m → m ≤ Kg 0 → ∀ a : Fin 3 → Zd 3 (sz0.L 0),
      0 < ∑ j ∈ Finset.range m,
        (cQVNonAltN sz0 Einst sInst vg Kg 0 3 10 (1 / 2) (4 / 5) Γ4 Λ3 5 m a j : ℝ) :=
  cQVNonAltN_sum_pos sz0 Einst sInst vg Kg 0 3 10 (1 / 2) (4 / 5) (by norm_num)
    (by norm_num [sInst, vg]) (vg_lt_one 0) (by norm_num [Kg]) Γ4 Λ3 (by norm_num) 5


/-! ### The bundle `GridAssemblyHypN` at the data, built from the theorems of §§3-4 -/

/-- The drift tensor along the walk. -/
def Dr0 (j : ℕ) (ω : PathΩ sz0) : (Fin 3 → Zd 3 (sz0.L 0)) → ℂ :=
  driftTensorN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 j) (pathH sz0 sInst vg Kg 0 j ω) sig3

/-- The initial tensor `A_0 = (𝓛-𝒦)_{u_0}(H_0)`. -/
def A0f (ω : PathΩ sz0) : (Fin 3 → Zd 3 (sz0.L 0)) → ℂ :=
  AvecN sz0 Einst sInst vg Kg 0 0 sig3 ω

/-- The drift-only frozen process `A_m = 𝒰_{u_0,u_m} A_0 + Σ_{j < m ∧ τ} 𝒰_{u_{j+1},u_m}(Δ Dr_j)`
(the martingale, second-order and remainder parts are `0`): it satisfies `hexp` of the bundle
exactly. -/
def Af (m : ℕ) (ω : PathΩ sz0) : (Fin 3 → Zd 3 (sz0.L 0)) → ℂ :=
  Ugen 3 (sz0.L 0) (sz0.lam 0) (Einst 0) sig3 (gridTime sInst vg Kg 0 0)
      (gridTime sInst vg Kg 0 m) (A0f ω) +
    ∑ j ∈ Finset.range (min m (tau0 ω)), Ugen 3 (sz0.L 0) (sz0.lam 0) (Einst 0) sig3
      (gridTime sInst vg Kg 0 (j + 1)) (gridTime sInst vg Kg 0 m)
      (((gridStep sInst vg Kg 0 : ℝ) : ℂ) • Dr0 j ω)

set_option linter.flexible false in
/-- **The bundle `GridAssemblyHypN` at the data**: the class `nonAltClsN`, the weights `κ = kappaNonAltN`,
`εK = epsNonAltN`, the drift level `dDriftNonAltN`, the constant `cQVNonAltN` and the fields `hker`,
`hA0cls`, `hdrift`, `hDcls`, `hc_pos`, `hκ0`, `hε0`, `hδ0`, `hdDrift0`, `hδD0` are the theorems of
§§3-4 (so their shapes are those of the structure); the process is the drift-only frozen process `Af`,
`Z = Y = R = 0`, `v = w = stepErr = 0`; the stopping time is `tau0 = goodExitTauN …` and the proxy is
the one of `subGaussStop_instance`. -/
theorem gridAssemblyHyp_instance :
    GridAssemblyHypN sz0 (n := 0) (k := 3) (Einst 0) sig3 (gridTime sInst vg Kg 0) tau0
      (gridStep sInst vg Kg 0) (Kg 0)
      (nonAltClsN 3 (sz0.L 0) (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (1 / 5) 6 (gridTime sInst vg Kg 0))
      A0f Af Dr0 (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
      (kappaNonAltN 3 3 10 (1 / 2) (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (4 / 5) (gridTime sInst vg Kg 0))
      (epsNonAltN 3 3 10 (1 / 2) ((sz0.W 0 : ℕ) : ℝ))
      (((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ)))
      (fun j _ => dDriftNonAltN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 j) 3 (Γ4 0) (Φ1 0))
      (fun _ _ => ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ)))
      (fun m a j => cQVNonAltN sz0 Einst sInst vg Kg 0 3 10 (1 / 2) (4 / 5) Γ4 Λ3 5 m a j)
      (fun _ => 0) (fun _ => 0) (fun _ => 0) where
  hE := (Einst_abs_lt 0).le
  hu0 := fun i _ => u_nonneg i
  hu1 := fun i hi => u_lt_one i hi
  hΔ0 := ST_gridStep_nonneg sInst vg Kg 0 (sInst_le_vg 0)
  hexp := fun m _ => Eventually.of_forall fun ω => by
    have hz : (fun _ : Fin 3 → Zd 3 (sz0.L 0) => (0 : ℂ)) = 0 := rfl
    simp only [Af, hz, add_zero]
  hκ0 := hκ0_instance
  hε0 := hε0_instance
  hker := hker_field_instance
  hδ0 := Real.rpow_nonneg hW0 _
  hA0cls := hA0cls_instance
  hdDrift0 := hdDrift0_instance
  hδD0 := fun _ _ _ => Real.rpow_nonneg hW0 _
  hdrift := hdrift_instance
  hDcls := hDcls_instance
  hc_pos := hc_pos_instance
  hv0 := fun _ _ => le_rfl
  hw0 := fun _ _ => le_rfl
  hY := by
    refine ⟨fun j => stronglyMeasurable_const, fun m _ b j _ => ?_⟩
    have h0 : ∀ ω, stoppedEdgeN sz0 (Einst 0) sig3 (gridTime sInst vg Kg 0)
        (gridTime sInst vg Kg 0 m) tau0 (fun _ _ _ => (0 : ℂ)) b j ω = 0 := by
      intro ω; simp [stoppedEdgeN, Ugen, UN]
    simp only [h0]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp
    all_goals first
      | exact Filter.Eventually.of_forall fun _ => rfl
      | exact Filter.Eventually.of_forall fun _ => le_rfl
  hstepErr0 := fun _ _ => le_rfl
  hR := Eventually.of_forall fun ω j _ _ b => by simp

/-- The fields of the bundle on the event `{0 < τ}` (everything, `tau0_pos`): `hker` applied through
the bundle to the nonzero tensor `Xinst`, and `hA0cls`, `hdrift`, `hDcls` at `j = 0`. -/
theorem bundle_fields_instance (ω : PathΩ sz0) :
    ‖Ugen 3 (sz0.L 0) (sz0.lam 0) (Einst 0) sig3 (gridTime sInst vg Kg 0 0)
        (gridTime sInst vg Kg 0 1) Xinst aFar‖ ≤
      kappaNonAltN 3 3 10 (1 / 2) (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (4 / 5) (gridTime sInst vg Kg 0) 0 1 *
          1 + epsNonAltN 3 3 10 (1 / 2) ((sz0.W 0 : ℕ) : ℝ) 0 1 *
            ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ)) ∧
    nonAltClsN 3 (sz0.L 0) (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (1 / 5) 6 (gridTime sInst vg Kg 0) 0
      (((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ))) (A0f ω) ∧
    (∀ b, ‖Dr0 0 ω b‖ ≤
      dDriftNonAltN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 0) 3 (Γ4 0) (Φ1 0)) ∧
    nonAltClsN 3 (sz0.L 0) (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (1 / 5) 6 (gridTime sInst vg Kg 0) (0 + 1)
      (((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ))) (Dr0 0 ω) :=
  ⟨gridAssemblyHyp_instance.hker 0 1 (Nat.zero_le 1) (by norm_num [Kg]) Xinst 1
      (((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ))) zero_le_one (Real.rpow_nonneg hW0 _) Xinst_norm_le Xinst_cls
      aFar,
    gridAssemblyHyp_instance.hA0cls ω (tau0_pos ω),
    fun b => gridAssemblyHyp_instance.hdrift ω 0 (by norm_num [Kg]) (tau0_pos ω) b,
    gridAssemblyHyp_instance.hDcls ω 0 (by norm_num [Kg]) (tau0_pos ω)⟩

end NQGood2Inst

end RBM.Ind

end

/-! ## 6. Axioms -/

#print axioms RBM.Ind.nonAltClsN
#print axioms RBM.Ind.kappaNonAltN
#print axioms RBM.Ind.epsNonAltN
#print axioms RBM.Ind.dDriftNonAltN
#print axioms RBM.Ind.qvBdNonAltN
#print axioms RBM.Ind.cQVNonAltN
#print axioms RBM.Ind.nqGood2_ratio_mul_Bctl_le
#print axioms RBM.Ind.kappaNonAltN_mul_Bctl_pow_le
#print axioms RBM.Ind.kappaNonAltN_succ_mul_Bctl_pow_le
#print axioms RBM.Ind.nonAlt_hkerN
#print axioms RBM.Ind.goodSetN_A0clsN
#print axioms RBM.Ind.nonAlt_hA0clsN
#print axioms RBM.Ind.nonAlt_hdriftN
#print axioms RBM.Ind.goodSetN_driftClsN
#print axioms RBM.Ind.nonAlt_hDclsN
#print axioms RBM.Ind.nonAlt_hκ0N
#print axioms RBM.Ind.nonAlt_hε0N
#print axioms RBM.Ind.nonAlt_hdDrift0N
#print axioms RBM.Ind.qvBdNonAltN_pos
#print axioms RBM.Ind.qvFormN_le_of_goodSetN_shiftN
#print axioms RBM.Ind.hQ_nonAltN
#print axioms RBM.Ind.subGaussStop_nonAltN
#print axioms RBM.Ind.cQVNonAltN_sum_pos
#print axioms RBM.Ind.NQGood2Inst.gridTime_inst
#print axioms RBM.Ind.NQGood2Inst.ratio_instance
#print axioms RBM.Ind.NQGood2Inst.kappa_Bctl_instance
#print axioms RBM.Ind.NQGood2Inst.kappa_succ_instance
#print axioms RBM.Ind.NQGood2Inst.hker_field_instance
#print axioms RBM.Ind.NQGood2Inst.Xinst_cls
#print axioms RBM.Ind.NQGood2Inst.hker_applied
#print axioms RBM.Ind.NQGood2Inst.tau0
#print axioms RBM.Ind.NQGood2Inst.tau0_mem
#print axioms RBM.Ind.NQGood2Inst.tau0_pos
#print axioms RBM.Ind.NQGood2Inst.A0cls_instance
#print axioms RBM.Ind.NQGood2Inst.driftCls_instance
#print axioms RBM.Ind.NQGood2Inst.hA0cls_instance
#print axioms RBM.Ind.NQGood2Inst.hA0cls_far_instance
#print axioms RBM.Ind.NQGood2Inst.hdrift_instance
#print axioms RBM.Ind.NQGood2Inst.hDcls_instance
#print axioms RBM.Ind.NQGood2Inst.hDcls_far_instance
#print axioms RBM.Ind.NQGood2Inst.hκ0_instance
#print axioms RBM.Ind.NQGood2Inst.hε0_instance
#print axioms RBM.Ind.NQGood2Inst.hdDrift0_instance
#print axioms RBM.Ind.NQGood2Inst.eeShiftErrN_inst_le
#print axioms RBM.Ind.NQGood2Inst.delta_shift_ok
#print axioms RBM.Ind.NQGood2Inst.qvBd_pos_instance
#print axioms RBM.Ind.NQGood2Inst.qvFormN_shift_instance
#print axioms RBM.Ind.NQGood2Inst.hQ_instance
#print axioms RBM.Ind.NQGood2Inst.hQ_instance_zero
#print axioms RBM.Ind.NQGood2Inst.subGaussStop_instance
#print axioms RBM.Ind.NQGood2Inst.hc_pos_instance
#print axioms RBM.Ind.NQGood2Inst.Dr0
#print axioms RBM.Ind.NQGood2Inst.A0f
#print axioms RBM.Ind.NQGood2Inst.Af
#print axioms RBM.Ind.NQGood2Inst.gridAssemblyHyp_instance
#print axioms RBM.Ind.NQGood2Inst.bundle_fields_instance
