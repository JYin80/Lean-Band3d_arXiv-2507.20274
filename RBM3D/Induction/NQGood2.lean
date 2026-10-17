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

/-! ### Target 2: (5.93) at `d ≥ 3` -/

/-! ### Target 3: the fields of `GridAssemblyHypN` -/

/-! ### Target 4: the quadratic-variation constant -/

/-! ### The bundle `GridAssemblyHypN` at the data, built from the theorems of §§3-4 -/

end RBM.Ind

end

/-! ## 6. Axioms -/
