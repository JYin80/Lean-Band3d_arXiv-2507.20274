/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.NQLin
import RBM3D.Induction.GridAssemblyN
import RBM3D.Induction.AzumaProxyN2
import RBM3D.Loop.KLFinal

/-!
# The non-alternating grid endpoint with the linear right side (`d ≥ 3`): `nqGridEndLinN`

Ticket T2199 (S3-12b, stochastic layer ST-3, second of three; S3-12a = `Induction/NQLin`).  Port of
RBM2D `Induction/NonAltEnd.lean` (`NonAltEnd:54-1276` at `c9a24cf`) on the `d ≥ 3` data of route (R)
(DECISIONS §62 (2)).  Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex`, `lem:STOeq_NQ`
(`3_5:1136`, proof `3_5:1152-1180`).

## What is here (namespace `RBM.Ind`)

* §0 asymptotic helpers `C (1 + log x)^j x^a ≤ x^b` (private; RBM2D `NonAltEnd:54-121`);
* §1 facts on the sizes, `W ≤ N` (crude), `W ≥ N^𝔠` for the negative powers of `W`;
* §2 the absorption lemmas of the seven numerical hypotheses of `budgetNonAltLinN` (`ha1`-`he4`),
  the regime facts (`hη`, the grid step, the shift hypothesis `hδ`), the exponent bookkeeping
  `nqEnd_arith`;
* §3 the assembly per sign vector at the exit time `nqLinExitTauN` (`nqEndLin_assembly`, private:
  its binder mentions `YMomentBoundsN`);
* §4 the collapsed window `v_n = s_n`, the union bound, the `Y`-moment constant;
* §5 **`nqGridEndLinN`** with exactly the statement `T2199_nqGridEndLinN` of
  `docs/tickets/checks/T2199-check.lean`: the `GoodSetN` at a free crude level `Φc`, the `GoodLinN`
  at the deterministic levels `Φ₁ Φ₂ Φ₃`, right side `N^{ε₀}(Λ^{1/2} + Φ₁ + Φ₂ + Φ₃) B_v^k`
  (degree 1 in the levels, no `Φ²`, no `Φc`); no `STKbound` premise (`stKbound_holds` gives it);
* §6 compiled nonempty instances at `d = 3` (namespace `RBM.Ind.NQEndLinInst`).

The good-event probability is not here (S3-12c, as in RBM2D `GridEndConcl`).  Every helper that the
ticket does not pin is `private` or prefixed `nqEnd_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-! ## 0. Asymptotic helpers (RBM2D `NonAltEnd.lean:54-121`, real variable `x`) -/

section Asymp

/-- `C · x^a ≤ x^b` for all large real `x` when `a < b` (RBM2D `NonAltEnd_ev_rpow_le`, `NonAltEnd:60`). -/
private theorem nqEnd_ev_rpow_le {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, C * x ^ a ≤ x ^ b := by
  have ht : Tendsto (fun x : ℝ => x ^ (b - a)) atTop atTop := tendsto_rpow_atTop (sub_pos.mpr hab)
  filter_upwards [ht.eventually_ge_atTop C, eventually_gt_atTop 0] with x hx hx0
  have h1 : x ^ b = x ^ (b - a) * x ^ a := by
    rw [← Real.rpow_add hx0]; ring_nf
  rw [h1]
  exact mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hx0.le _)

/-- `C · x^a (log x + 1) ≤ x^b` for all large real `x` when `a < b` (RBM2D `NonAltEnd:70`). -/
private theorem nqEnd_ev_rpow_log_le {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, C * x ^ a * (Real.log x + 1) ≤ x ^ b := by
  set δ := (b - a) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  filter_upwards [nqEnd_ev_rpow_le (a := a + δ) (b := b) (by rw [hδ]; linarith)
    (max C 0 * (1 / δ + 1)), eventually_ge_atTop 1] with x hN hx1
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlog : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div hx0.le hδ0
  have hNδ : 1 ≤ x ^ δ := Real.one_le_rpow hx1 hδ0.le
  have hl : Real.log x + 1 ≤ (1 / δ + 1) * x ^ δ := by
    have : x ^ δ / δ = 1 / δ * x ^ δ := by ring
    nlinarith
  have hCa : C * x ^ a ≤ max C 0 * x ^ a :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx0.le _)
  have hM0 : 0 ≤ max C 0 * x ^ a := mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hx0.le _)
  calc C * x ^ a * (Real.log x + 1)
      ≤ max C 0 * x ^ a * (Real.log x + 1) := mul_le_mul_of_nonneg_right hCa (by linarith)
    _ ≤ max C 0 * x ^ a * ((1 / δ + 1) * x ^ δ) := mul_le_mul_of_nonneg_left hl hM0
    _ = max C 0 * (1 / δ + 1) * x ^ (a + δ) := by
        rw [Real.rpow_add hx0]; ring
    _ ≤ x ^ b := hN

/-- **Polylog absorption**: `C (1 + log x)^j x^a ≤ x^b` for all large real `x` when `a < b`
(RBM2D `NonAltEnd_ev_polylog_le`, `NonAltEnd:94`). -/
private theorem nqEnd_ev_polylog_le (j : ℕ) :
    ∀ {a b : ℝ}, a < b → ∀ C : ℝ, ∀ᶠ x : ℝ in atTop, C * (1 + Real.log x) ^ j * x ^ a ≤ x ^ b := by
  induction j with
  | zero =>
    intro a b hab C
    filter_upwards [nqEnd_ev_rpow_le hab C] with x hx
    simpa using hx
  | succ j ih =>
    intro a b hab C
    set m := (a + b) / 2 with hm
    have ham : a < m := by rw [hm]; linarith
    have hmb : m < b := by rw [hm]; linarith
    filter_upwards [nqEnd_ev_rpow_log_le ham (max C 0), ih hmb 1, eventually_ge_atTop 1] with
      x h1 h2 hx1
    have hx0 : (0 : ℝ) < x := by linarith
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hL : 0 ≤ (1 + Real.log x) ^ j := by positivity
    have hxa : 0 ≤ x ^ a := Real.rpow_nonneg hx0.le _
    calc C * (1 + Real.log x) ^ (j + 1) * x ^ a
        ≤ max C 0 * (1 + Real.log x) ^ (j + 1) * x ^ a := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
            (by positivity)) hxa
      _ = (1 + Real.log x) ^ j * (max C 0 * x ^ a * (Real.log x + 1)) := by ring
      _ ≤ (1 + Real.log x) ^ j * x ^ m := mul_le_mul_of_nonneg_left h1 hL
      _ = 1 * (1 + Real.log x) ^ j * x ^ m := by ring
      _ ≤ x ^ b := h2

end Asymp

/-! ## 1. Elementary facts on the sizes -/

section Facts

variable {d : ℕ} (sz : Sizes d)

private theorem nqEnd_one_le_size (n : ℕ) : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  exact_mod_cast sz.one_le_size n

private theorem nqEnd_one_le_W (n : ℕ) : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by
  exact_mod_cast sz.W_pos n

/-- `W^d L^d = N` (the private `gridEnv_size_cast` of `GridEnvelopeN`). -/
private theorem nqEnd_size_cast (n : ℕ) :
    (sz.W n : ℝ) ^ d * (sz.L n : ℝ) ^ d = ((sz.size n : ℕ) : ℝ) := by
  have : ((sz.size n : ℕ) : ℝ) = (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) := rfl
  rw [this]
  push_cast
  ring

/-- **Crude `W ≤ N`** (`W ≤ W^d ≤ (W L)^d = N`, `d ≥ 1`): the bound for the positive powers of `W`. -/
private theorem nqEnd_W_le_size (hd : 1 ≤ d) (n : ℕ) :
    ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  have h1 : sz.W n ≤ (sz.W n) ^ d := Nat.le_self_pow (by omega) _
  have h2 : (sz.W n) ^ d ≤ sz.size n := by
    unfold Sizes.size
    exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by have := sz.three_le_L n; omega)) d
  exact_mod_cast h1.trans h2

end Facts

/-- `W^e ≤ N^{𝔠 e}` for `e ≤ 0` from `N^𝔠 ≤ W` (the negative powers of `W`; RBM2D
`NonAltEnd_Wneg_le`, `NonAltEnd:266`, with a general nonpositive exponent). -/
private theorem nqEnd_Wpow_le {W N c e : ℝ} (hN0 : 0 < N) (hcW : N ^ c ≤ W) (he : e ≤ 0) :
    W ^ e ≤ N ^ (c * e) := by
  have h1 : 0 < N ^ c := Real.rpow_pos_of_pos hN0 _
  have h := Real.rpow_le_rpow_of_nonpos h1 hcW he
  rwa [← Real.rpow_mul hN0.le] at h

/-! ## 2. The absorption lemmas (the seven numerical hypotheses of `budgetNonAltLinN`)

Each is stated for abstract exponents (`c = C ε` of `nqGood1C`, `ε₁`, `εq`, `ε₀`, `D'`, ...) in the exact
form of the corresponding hypothesis of `budgetNonAltLinN` (`NQLin.lean:966`), eventually in `n`.
Positive powers of `W` are bounded by `W ≤ N` (crude, `W^d L^d = N`), negative ones by `W ≥ N^𝔠`
(`Bandwidth`); the polylogarithm of `Ls = (Im m)⁻¹ log N ≤ κ'⁻¹ log N` is absorbed by
`nqEnd_ev_polylog_le`. -/

section Absorb

variable {d : ℕ} (sz : Sizes d)

/-- (ha1) `W^{Cε} N^{ε₁} ≤ N^{ε₀}/6` when `Cε + ε₁ < ε₀` (`budgetNonAltLinN.ha1`). -/
private theorem nqEnd_ev_ha1 (hd : 1 ≤ d) (hsize : sz.SizeTendsto) {c ε₁ ε₀ : ℝ} (hc : 0 ≤ c)
    (hε : c + ε₁ < ε₀) :
    ∀ᶠ n : ℕ in atTop, ((sz.W n : ℕ) : ℝ) ^ c * ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 := by
  filter_upwards [hsize.eventually (nqEnd_ev_rpow_le hε 6), hsize.eventually_ge_atTop 1] with n h hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have h1 : ((sz.W n : ℕ) : ℝ) ^ c ≤ ((sz.size n : ℕ) : ℝ) ^ c :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (nqEnd_W_le_size sz hd n) hc
  have hE1 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ := Real.rpow_nonneg hN0.le _
  rw [Real.rpow_add hN0] at h
  calc ((sz.W n : ℕ) : ℝ) ^ c * ((sz.size n : ℕ) : ℝ) ^ ε₁
      ≤ ((sz.size n : ℕ) : ℝ) ^ c * ((sz.size n : ℕ) : ℝ) ^ ε₁ :=
        mul_le_mul_of_nonneg_right h1 hE1
    _ ≤ _ := by linarith

/-- (ha2) `k W^{Cε} (N^{ε₁})² Ls ≤ N^{ε₀}/12` when `Cε + 2ε₁ < ε₀`, `Ls = (Im m)⁻¹ log N`
(`budgetNonAltLinN.ha2`; the polylog `log N` is absorbed). -/
private theorem nqEnd_ev_ha2 (hd : 1 ≤ d) (hsize : sz.SizeTendsto) (k : ℕ) {κ' : ℝ} (hκ' : 0 < κ')
    {E : ℕ → ℝ} (hκm : ∀ n, κ' ≤ (mE (E n)).im) {c ε₁ ε₀ : ℝ} (hc : 0 ≤ c)
    (hε : c + 2 * ε₁ < ε₀) :
    ∀ᶠ n : ℕ in atTop, (k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ c * (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 2 *
        ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 := by
  filter_upwards [hsize.eventually (nqEnd_ev_polylog_le 1 hε (12 * ((k : ℝ) * κ'⁻¹))),
    hsize.eventually_ge_atTop 1] with n h hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hIm : ((mE (E n)).im)⁻¹ ≤ κ'⁻¹ := inv_anti₀ hκ' (hκm n)
  have hW : ((sz.W n : ℕ) : ℝ) ^ c ≤ N ^ c :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (nqEnd_W_le_size sz hd n) hc
  have hsq : (N ^ ε₁) ^ 2 = N ^ (2 * ε₁) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; push_cast; ring_nf
  have hLs : (mE (E n)).im⁻¹ * Real.log N ≤ κ'⁻¹ * Real.log N :=
    mul_le_mul_of_nonneg_right hIm hlog0
  have hLs0 : 0 ≤ (mE (E n)).im⁻¹ * Real.log N := by
    have : 0 < (mE (E n)).im := lt_of_lt_of_le hκ' (hκm n)
    positivity
  have hN2 : 0 ≤ N ^ (2 * ε₁) := Real.rpow_nonneg hN0.le _
  have hrp : N ^ (c + 2 * ε₁) = N ^ c * N ^ (2 * ε₁) := Real.rpow_add hN0 _ _
  calc (k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ c * (N ^ ε₁) ^ 2 * ((mE (E n)).im⁻¹ * Real.log N)
      ≤ (k : ℝ) * N ^ c * N ^ (2 * ε₁) * (κ'⁻¹ * Real.log N) := by
        rw [hsq]
        refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW hk0) hN2) hLs hLs0
          (by positivity)
    _ = ((k : ℝ) * κ'⁻¹) * Real.log N * N ^ (c + 2 * ε₁) := by rw [hrp]; ring
    _ ≤ ((k : ℝ) * κ'⁻¹) * (1 + Real.log N) * N ^ (c + 2 * ε₁) := by
        have : 0 ≤ ((k : ℝ) * κ'⁻¹) * N ^ (c + 2 * ε₁) := by positivity
        nlinarith
    _ ≤ N ^ ε₀ / 12 := by
        have h' : 12 * ((k : ℝ) * κ'⁻¹) * (1 + Real.log N) ^ 1 * N ^ (c + 2 * ε₁) ≤ N ^ ε₀ := h
        rw [pow_one] at h'
        linarith

/-- (ha3) `N^{εq} W^{Cε} N^{ε₁} √(k (Ls + 1)) ≤ N^{ε₀}/12` when `εq + Cε + ε₁ < ε₀`
(`budgetNonAltLinN.ha3`; `√z ≤ z + 1`, the polylog is absorbed). -/
private theorem nqEnd_ev_ha3 (hd : 1 ≤ d) (hsize : sz.SizeTendsto) (k : ℕ) {κ' : ℝ} (hκ' : 0 < κ')
    {E : ℕ → ℝ} (hκm : ∀ n, κ' ≤ (mE (E n)).im) {c ε₁ εq ε₀ : ℝ} (hc : 0 ≤ c)
    (hε : εq + c + ε₁ < ε₀) :
    ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ c *
        ((sz.size n : ℕ) : ℝ) ^ ε₁ * Real.sqrt ((k : ℝ) * ((mE (E n)).im⁻¹ *
          Real.log ((sz.size n : ℕ) : ℝ) + 1))) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 := by
  filter_upwards [hsize.eventually (nqEnd_ev_polylog_le 1 hε
    (12 * ((k : ℝ) * κ'⁻¹ + k + 1))), hsize.eventually_ge_atTop 1] with n h hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have him0 : 0 < (mE (E n)).im := lt_of_lt_of_le hκ' (hκm n)
  have hIm : ((mE (E n)).im)⁻¹ ≤ κ'⁻¹ := inv_anti₀ hκ' (hκm n)
  have hW : ((sz.W n : ℕ) : ℝ) ^ c ≤ N ^ c :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (nqEnd_W_le_size sz hd n) hc
  have hLs : (mE (E n)).im⁻¹ * Real.log N ≤ κ'⁻¹ * Real.log N :=
    mul_le_mul_of_nonneg_right hIm hlog0
  have hLs0 : 0 ≤ (mE (E n)).im⁻¹ * Real.log N := by positivity
  set Z : ℝ := (k : ℝ) * ((mE (E n)).im⁻¹ * Real.log N + 1) with hZ
  have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
  have hsq : Real.sqrt Z ≤ Z + 1 := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hZle : Z + 1 ≤ ((k : ℝ) * κ'⁻¹ + k + 1) * (1 + Real.log N) := by
    have h1 : (k : ℝ) * ((mE (E n)).im⁻¹ * Real.log N) ≤ (k : ℝ) * (κ'⁻¹ * Real.log N) :=
      mul_le_mul_of_nonneg_left hLs hk0
    have h2 : 0 ≤ (k : ℝ) * κ'⁻¹ := by positivity
    have h3 : 0 ≤ ((k : ℝ) + 1) * Real.log N := by positivity
    rw [hZ]
    nlinarith
  have hrp : N ^ (εq + c + ε₁) = N ^ εq * N ^ c * N ^ ε₁ := by
    rw [Real.rpow_add hN0, Real.rpow_add hN0]
  have hNe : 0 ≤ N ^ εq := Real.rpow_nonneg hN0.le _
  have hN1' : 0 ≤ N ^ ε₁ := Real.rpow_nonneg hN0.le _
  have hNc : 0 ≤ N ^ c := Real.rpow_nonneg hN0.le _
  calc N ^ εq * (((sz.W n : ℕ) : ℝ) ^ c * N ^ ε₁ * Real.sqrt Z)
      ≤ N ^ εq * (N ^ c * N ^ ε₁ * (((k : ℝ) * κ'⁻¹ + k + 1) * (1 + Real.log N))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_right hW hN1')
          (hsq.trans hZle) (Real.sqrt_nonneg _) (by positivity)) hNe
    _ = ((k : ℝ) * κ'⁻¹ + k + 1) * (1 + Real.log N) * N ^ (εq + c + ε₁) := by rw [hrp]; ring
    _ ≤ N ^ ε₀ / 12 := by
        have h' : 12 * ((k : ℝ) * κ'⁻¹ + k + 1) * (1 + Real.log N) ^ 1 * N ^ (εq + c + ε₁) ≤
            N ^ ε₀ := h
        rw [pow_one] at h'
        linarith

/-- (he1) `N^k (W^C W^{-D'}) ≤ N^{ε₀}/12` when `C ≤ D'` and `k + 𝔠 (C - D') < ε₀`
(`budgetNonAltLinN.he1`; `W^C W^{-D'} = W^{C-D'} ≤ N^{𝔠(C-D')}`). -/
private theorem nqEnd_ev_he1 (hsize : sz.SizeTendsto) {𝔠 : ℝ} (hband : sz.Bandwidth 𝔠) {k : ℕ}
    {C D' ε₀ : ℝ} (hCD : C ≤ D') (hε : (k : ℝ) + 𝔠 * (C - D') < ε₀) :
    ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ k * (((sz.W n : ℕ) : ℝ) ^ C *
        ((sz.W n : ℕ) : ℝ) ^ (-D')) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 := by
  filter_upwards [hband, hsize.eventually (nqEnd_ev_rpow_le hε 12), hsize.eventually_ge_atTop 1] with
    n hW h hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hW
  have hmerge : ((sz.W n : ℕ) : ℝ) ^ C * ((sz.W n : ℕ) : ℝ) ^ (-D') =
      ((sz.W n : ℕ) : ℝ) ^ (C - D') := by
    rw [← Real.rpow_add hWpos]; ring_nf
  have hle := nqEnd_Wpow_le hN0 hW (show C - D' ≤ 0 by linarith)
  have hk : ((sz.size n : ℕ) : ℝ) ^ k = ((sz.size n : ℕ) : ℝ) ^ (k : ℝ) := (Real.rpow_natCast _ _).symm
  have hrp : ((sz.size n : ℕ) : ℝ) ^ ((k : ℝ) + 𝔠 * (C - D')) =
      ((sz.size n : ℕ) : ℝ) ^ (k : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (𝔠 * (C - D')) :=
    Real.rpow_add hN0 _ _
  rw [hrp] at h
  have hNk : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (k : ℝ) := Real.rpow_nonneg hN0.le _
  rw [hmerge, hk]
  calc ((sz.size n : ℕ) : ℝ) ^ (k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (C - D')
      ≤ ((sz.size n : ℕ) : ℝ) ^ (k : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (𝔠 * (C - D')) :=
        mul_le_mul_of_nonneg_left hle hNk
    _ ≤ _ := by linarith

/-- (he3, he4) `N^k N^{-D} ≤ N^{ε₀}/6` when `k - D < ε₀` (`budgetNonAltLinN.he3`, `he4` at
`D = D_Y`, `D = D_t`; RBM2D `NonAltEnd_ev_he4`, `NonAltEnd:573`). -/
private theorem nqEnd_ev_he4 (hsize : sz.SizeTendsto) (k : ℕ) {D ε₀ : ℝ}
    (hε : (k : ℝ) - D < ε₀) :
    ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-D) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 := by
  filter_upwards [hsize.eventually (nqEnd_ev_polylog_le 0 hε 6),
    hsize.eventually_ge_atTop 1] with n h hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  simp only [pow_zero, mul_one] at h
  rw [← Real.rpow_natCast, ← Real.rpow_add hN0]
  have e : (k : ℝ) + -D = (k : ℝ) - D := by ring
  rw [e]
  linarith

end Absorb

/-- The core bound of (he2), on plain reals: with `R ≤ P N^r`, the three exponents `e₁ = 2a - D`,
`e₂ = a + b - D`, `e₃ = b + k - D` all `≤ 0` (so that `W^{e} ≤ N^{𝔠 e}`) and
`2r + 𝔠 e₁, r + 𝔠 e₂, 𝔠 e₃ ≤ ξ`:
`(W^a R (W^a R + W^b) + W^b W^k) W^{-D} ≤ (P² + P + 1) N^ξ`.  Here `a = Cε`, `b = C`,
`R = ((1+g²)N)^{k-1}`, so the left side is `nqBudget_qvFar · W^{-D''}`: the positive powers of `W` are
combined with `W^{-D''}` before the bandwidth `W ≥ N^𝔠` is used. -/
private theorem nqEnd_he2_bound {x N R P a b D 𝔠 ξ r : ℝ} {k : ℕ} (hN1 : 1 ≤ N) (hx : N ^ 𝔠 ≤ x)
    (hR0 : 0 ≤ R) (hRP : R ≤ P * N ^ r) (hP : 0 ≤ P) (he1 : 2 * a - D ≤ 0) (he2 : a + b - D ≤ 0)
    (he3 : b + (k : ℝ) - D ≤ 0) (h1 : 2 * r + 𝔠 * (2 * a - D) ≤ ξ) (h2 : r + 𝔠 * (a + b - D) ≤ ξ)
    (h3 : 𝔠 * (b + (k : ℝ) - D) ≤ ξ) :
    ((x ^ a * R) * ((x ^ a * R) + x ^ b) + x ^ b * x ^ k) * x ^ (-D) ≤ (P ^ 2 + P + 1) * N ^ ξ := by
  have hN0 : 0 < N := by linarith
  have hx0 : 0 < x := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hx
  have e1 : x ^ a * x ^ a * x ^ (-D) = x ^ (2 * a - D) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; ring
  have e2 : x ^ a * x ^ b * x ^ (-D) = x ^ (a + b - D) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1
  have e3 : x ^ b * x ^ k * x ^ (-D) = x ^ (b + (k : ℝ) - D) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1
  have hexp : ((x ^ a * R) * ((x ^ a * R) + x ^ b) + x ^ b * x ^ k) * x ^ (-D) =
      R ^ 2 * x ^ (2 * a - D) + R * x ^ (a + b - D) + x ^ (b + (k : ℝ) - D) := by
    calc _ = R ^ 2 * (x ^ a * x ^ a * x ^ (-D)) + R * (x ^ a * x ^ b * x ^ (-D)) +
          x ^ b * x ^ k * x ^ (-D) := by ring
      _ = _ := by rw [e1, e2, e3]
  have hb1 : x ^ (2 * a - D) ≤ N ^ (𝔠 * (2 * a - D)) := nqEnd_Wpow_le hN0 hx he1
  have hb2 : x ^ (a + b - D) ≤ N ^ (𝔠 * (a + b - D)) := nqEnd_Wpow_le hN0 hx he2
  have hb3 : x ^ (b + (k : ℝ) - D) ≤ N ^ (𝔠 * (b + (k : ℝ) - D)) := nqEnd_Wpow_le hN0 hx he3
  have hNr : 0 ≤ N ^ r := Real.rpow_nonneg hN0.le _
  have hsq : (N ^ r) ^ 2 = N ^ (2 * r) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; push_cast; ring_nf
  have t1 : R ^ 2 * x ^ (2 * a - D) ≤ P ^ 2 * N ^ ξ := by
    calc R ^ 2 * x ^ (2 * a - D) ≤ (P * N ^ r) ^ 2 * N ^ (𝔠 * (2 * a - D)) :=
          mul_le_mul (pow_le_pow_left₀ hR0 hRP 2) hb1 (by positivity) (by positivity)
      _ = P ^ 2 * N ^ (2 * r + 𝔠 * (2 * a - D)) := by
          rw [mul_pow, hsq, Real.rpow_add hN0]; ring
      _ ≤ P ^ 2 * N ^ ξ :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 h1) (by positivity)
  have t2 : R * x ^ (a + b - D) ≤ P * N ^ ξ := by
    calc R * x ^ (a + b - D) ≤ (P * N ^ r) * N ^ (𝔠 * (a + b - D)) :=
          mul_le_mul hRP hb2 (by positivity) (by positivity)
      _ = P * N ^ (r + 𝔠 * (a + b - D)) := by rw [Real.rpow_add hN0]; ring
      _ ≤ P * N ^ ξ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 h2) hP
  have t3 : x ^ (b + (k : ℝ) - D) ≤ N ^ ξ :=
    hb3.trans (Real.rpow_le_rpow_of_exponent_le hN1 h3)
  rw [hexp]
  nlinarith [t1, t2, t3]

/-- The last step of (he2), on plain reals: `Y ≤ M N^ξ` and `12 √(k M) N^{εq + k + ξ/2} ≤ N^{ε₀}` give
`N^{εq} (N^k √(k Y)) ≤ N^{ε₀}/12`. -/
private theorem nqEnd_he2_final {N Y εq ε₀ ξ M : ℝ} {k : ℕ} (hN1 : 1 ≤ N) (hM : 0 ≤ M)
    (hY : Y ≤ M * N ^ ξ)
    (h : 12 * Real.sqrt ((k : ℝ) * M) * N ^ (εq + (k : ℝ) + ξ / 2) ≤ N ^ ε₀) :
    N ^ εq * (N ^ k * Real.sqrt ((k : ℝ) * Y)) ≤ N ^ ε₀ / 12 := by
  have hN0 : 0 < N := by linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hs1 : Real.sqrt ((k : ℝ) * Y) ≤ Real.sqrt ((k : ℝ) * (M * N ^ ξ)) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hY hk0)
  have hsN : Real.sqrt (N ^ ξ) = N ^ (ξ / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]; ring_nf
  have hs2 : Real.sqrt ((k : ℝ) * (M * N ^ ξ)) = Real.sqrt ((k : ℝ) * M) * N ^ (ξ / 2) := by
    rw [← mul_assoc, Real.sqrt_mul (by positivity), hsN]
  have hk : N ^ k = N ^ (k : ℝ) := (Real.rpow_natCast _ _).symm
  have hNe : 0 ≤ N ^ εq := Real.rpow_nonneg hN0.le _
  have hNk : 0 ≤ N ^ k := by positivity
  calc N ^ εq * (N ^ k * Real.sqrt ((k : ℝ) * Y))
      ≤ N ^ εq * (N ^ k * (Real.sqrt ((k : ℝ) * M) * N ^ (ξ / 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hs1.trans_eq hs2) hNk) hNe
    _ = Real.sqrt ((k : ℝ) * M) * N ^ (εq + (k : ℝ) + ξ / 2) := by
        rw [hk, Real.rpow_add hN0, Real.rpow_add hN0]; ring
    _ ≤ N ^ ε₀ / 12 := by linarith

section Absorb2

variable {d : ℕ} (sz : Sizes d)

/-- (he2) `N^{εq} (N^k √(k · qvFar · W^{-D''})) ≤ N^{ε₀}/12` (`budgetNonAltLinN.he2`;
`qvFar ≤ kapFar² + kapFar W^C + W^{C+k}`, `kapFar = W^{Cε}((1+g²)N)^{k-1}`, `g ≤ Λg`): with
`D'' ≥ C + k + 2Cε` every `W`-exponent is negative; `ξ` is a common exponent bound (`ξ = -2k-4` at
the chosen constants) with `εq + k + ξ/2 < ε₀`. -/
private theorem nqEnd_ev_he2 (hsize : sz.SizeTendsto) {𝔠 : ℝ} (hband : sz.Bandwidth 𝔠) {k : ℕ}
    (hk : 1 ≤ k) {Λg κ' ε : ℝ} (hlam : ∀ᶠ n : ℕ in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λg)
    {D'' εq ε₀ ξ : ℝ}
    (he1 : 2 * (nqGood1C d k Λg κ' * ε) - D'' ≤ 0)
    (he2 : nqGood1C d k Λg κ' * ε + nqGood1C d k Λg κ' - D'' ≤ 0)
    (he3 : nqGood1C d k Λg κ' + (k : ℝ) - D'' ≤ 0)
    (h1 : 2 * ((k : ℝ) - 1) + 𝔠 * (2 * (nqGood1C d k Λg κ' * ε) - D'') ≤ ξ)
    (h2 : ((k : ℝ) - 1) + 𝔠 * (nqGood1C d k Λg κ' * ε + nqGood1C d k Λg κ' - D'') ≤ ξ)
    (h3 : 𝔠 * (nqGood1C d k Λg κ' + (k : ℝ) - D'') ≤ ξ) (hξ : εq + (k : ℝ) + ξ / 2 < ε₀) :
    ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.size n : ℕ) : ℝ) ^ k *
        Real.sqrt ((k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε * ((sz.W n : ℕ) : ℝ) ^ (-D'')))) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 := by
  set P : ℝ := (1 + Λg ^ 2) ^ (k - 1) with hP
  have hP0 : 0 ≤ P := by positivity
  set M : ℝ := P ^ 2 + P + 1 with hM
  have hM0 : 0 ≤ M := by positivity
  filter_upwards [hband, hlam, hsize.eventually (nqEnd_ev_rpow_le hξ (12 * Real.sqrt ((k : ℝ) * M))),
    hsize.eventually_ge_atTop 1] with n hW hg h hN1
  obtain ⟨hg0, hgΛ⟩ := hg
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hR0 : 0 ≤ ((1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ)) ^ (k - 1) := by positivity
  have hR : ((1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ)) ^ (k - 1) ≤
      P * ((sz.size n : ℕ) : ℝ) ^ ((k : ℝ) - 1) := by
    rw [mul_pow]
    have h1' : (1 + sz.lam n ^ 2) ^ (k - 1) ≤ P :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) _
    have h2' : ((sz.size n : ℕ) : ℝ) ^ (k - 1) = ((sz.size n : ℕ) : ℝ) ^ ((k : ℝ) - 1) := by
      rw [← Real.rpow_natCast, Nat.cast_sub hk, Nat.cast_one]
    rw [h2']
    exact mul_le_mul_of_nonneg_right h1' (Real.rpow_nonneg hN0.le _)
  have hbound := nqEnd_he2_bound (x := ((sz.W n : ℕ) : ℝ)) (N := ((sz.size n : ℕ) : ℝ))
    (a := nqGood1C d k Λg κ' * ε) (b := nqGood1C d k Λg κ') (D := D'') (𝔠 := 𝔠) (ξ := ξ)
    (r := (k : ℝ) - 1) (k := k) hN1 hW hR0 hR hP0 he1 he2 he3 h1 h2 h3
  have hY : nqBudget_qvFar sz n k Λg κ' ε * ((sz.W n : ℕ) : ℝ) ^ (-D'') ≤
      M * ((sz.size n : ℕ) : ℝ) ^ ξ := by
    unfold nqBudget_qvFar nqBudget_kapFar
    exact hbound
  exact nqEnd_he2_final hN1 hM0 hY h

end Absorb2

/-! ## 2b. The regime facts: `W → ∞`, the grid step, `hη`, `hΔη`, the shift hypothesis `hδ` -/

section Regime

variable {d : ℕ} (sz : Sizes d)

/-- `X ≤ W^a` eventually for `a > 0` (`W ≥ N^𝔠 → ∞`): the source of `1 < W`, `4 ≤ W^ε`,
`d W^{τ'} ≤ W^ε`, `2 ≤ W`. -/
private theorem nqEnd_ev_W_rpow_ge (hsize : sz.SizeTendsto) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠)
    (hband : sz.Bandwidth 𝔠) {a : ℝ} (ha : 0 < a) (X : ℝ) :
    ∀ᶠ n : ℕ in atTop, X ≤ ((sz.W n : ℕ) : ℝ) ^ a := by
  have ht : Tendsto (fun x : ℝ => x ^ (𝔠 * a)) atTop atTop := tendsto_rpow_atTop (mul_pos h𝔠 ha)
  filter_upwards [hband, hsize.eventually (ht.eventually_ge_atTop X),
    hsize.eventually_ge_atTop 1] with n hW hX hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  calc X ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * a) := hX
    _ = (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ a := Real.rpow_mul hN0.le _ _
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ a := Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hW ha.le

/-- `Δ ≤ N^{-C_K}` on a grid with `N^{C_K} ≤ K n` and `v - s ≤ 1` (RBM2D `NonAltEnd_step_le`,
`NonAltEnd:652`). -/
private theorem nqEnd_step_le {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {C_K : ℝ}
    (hK : ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) (hvs : v n - s n ≤ 1) :
    gridStep s v K n ≤ ((sz.size n : ℕ) : ℝ) ^ (-C_K) := by
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := lt_of_lt_of_le one_pos (nqEnd_one_le_size sz n)
  have hpos : 0 < ((sz.size n : ℕ) : ℝ) ^ C_K := Real.rpow_pos_of_pos hN0 _
  have hK0 : (0 : ℝ) < K n := lt_of_lt_of_le hpos hK
  unfold gridStep
  rw [Real.rpow_neg hN0.le, div_le_iff₀ hK0]
  calc v n - s n ≤ 1 := hvs
    _ = (((sz.size n : ℕ) : ℝ) ^ C_K)⁻¹ * ((sz.size n : ℕ) : ℝ) ^ C_K :=
        (inv_mul_cancel₀ hpos.ne').symm
    _ ≤ (((sz.size n : ℕ) : ℝ) ^ C_K)⁻¹ * (K n : ℝ) :=
        mul_le_mul_of_nonneg_left hK (inv_nonneg.2 hpos.le)

/-- `K Δ = v - s ≤ 1`. -/
private theorem nqEnd_K_mul_step {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hK : K n ≠ 0)
    (hvs : v n - s n ≤ 1) : (K n : ℝ) * gridStep s v K n ≤ 1 := by
  have hK' : (K n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK
  unfold gridStep
  rw [mul_div_cancel₀ _ hK']
  exact hvs

/-- The one-step increment of the grid times is `Δ`. -/
private theorem nqEnd_gridTime_succ_sub (s v : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) :
    gridTime s v K n (j + 1) - gridTime s v K n j = gridStep s v K n := by
  unfold gridTime; push_cast; ring

/-- `η_u⁻¹ ≤ N^{1-τ}/κ'` for `u ≤ t`, `κ' ≤ Im m`, under the range condition
`N^{-1+τ} ≤ 1 - t` (RBM2D `NonAltEnd_etaT_inv_le`, `NonAltEnd:593`, with `κ'` for `c₀`). -/
private theorem nqEnd_etaT_inv_le {κ' E u t τR N : ℝ} (hκ' : 0 < κ') (hκm : κ' ≤ (mE E).im)
    (hut : u ≤ t) (hN0 : 0 < N) (hR : N ^ (-1 + τR) ≤ 1 - t) :
    (etaT E u)⁻¹ ≤ N ^ (1 - τR) / κ' := by
  have hpos : 0 < N ^ (-1 + τR) := Real.rpow_pos_of_pos hN0 _
  have h1 : N ^ (-1 + τR) ≤ 1 - u := by linarith
  have hη : N ^ (-1 + τR) * κ' ≤ etaT E u := by
    unfold etaT
    exact mul_le_mul h1 hκm hκ'.le (by linarith)
  calc (etaT E u)⁻¹ ≤ (N ^ (-1 + τR) * κ')⁻¹ := inv_anti₀ (mul_pos hpos hκ') hη
    _ = N ^ (1 - τR) / κ' := by
        rw [mul_inv, show (-1 + τR) = -(1 - τR) by ring, Real.rpow_neg hN0.le, inv_inv]
        exact (div_eq_mul_inv _ _).symm

/-- (`hη`) `η_v⁻¹ ≤ N` eventually, from `RangeCond τ_R v`, `κ' ≤ Im m` and `N^{τ_R} ≥ κ'⁻¹`
(RBM2D `NonAltEnd_ev_hη`, `NonAltEnd:634`). -/
private theorem nqEnd_ev_hη (hsize : sz.SizeTendsto) {κ' τR : ℝ} (hκ' : 0 < κ') {E v : ℕ → ℝ}
    (hκm : ∀ n, κ' ≤ (mE (E n)).im) (hτR : 0 < τR) (hrange : sz.RangeCond τR v) :
    ∀ᶠ n : ℕ in atTop, (etaT (E n) (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
  filter_upwards [hrange, hsize.eventually (nqEnd_ev_rpow_le (a := 0) hτR κ'⁻¹),
    hsize.eventually_ge_atTop 1] with n hR hbig hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have h := nqEnd_etaT_inv_le hκ' (hκm n) le_rfl hN0 hR
  rw [Real.rpow_zero, mul_one] at hbig
  calc (etaT (E n) (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (1 - τR) / κ' := h
    _ = ((sz.size n : ℕ) : ℝ) ^ (1 - τR) * κ'⁻¹ := div_eq_mul_inv _ _
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (1 - τR) * ((sz.size n : ℕ) : ℝ) ^ τR :=
        mul_le_mul_of_nonneg_left hbig (Real.rpow_nonneg hN0.le _)
    _ = ((sz.size n : ℕ) : ℝ) := by rw [← Real.rpow_add hN0]; simp

/-- (`hΔη`) `Δ η_v⁻¹ ≤ 1` for `C_K ≥ 1`, `η_v⁻¹ ≤ N` (RBM2D `NonAltEnd_hΔN`, `NonAltEnd:667`). -/
private theorem nqEnd_hΔη {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {C_K η : ℝ} (hC : 1 ≤ C_K)
    (hK : ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) (hvs : v n - s n ≤ 1) (hη0 : 0 ≤ η⁻¹)
    (hη : η⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) : gridStep s v K n * η⁻¹ ≤ 1 := by
  have hN1 := nqEnd_one_le_size sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := lt_of_lt_of_le one_pos hN1
  have h := nqEnd_step_le sz hK hvs
  calc gridStep s v K n * η⁻¹
      ≤ ((sz.size n : ℕ) : ℝ) ^ (-C_K) * ((sz.size n : ℕ) : ℝ) :=
        mul_le_mul h hη hη0 (Real.rpow_nonneg hN0.le _)
    _ = ((sz.size n : ℕ) : ℝ) ^ (1 - C_K) := by
        rw [show (1 - C_K) = 1 + (-C_K) by ring, Real.rpow_add hN0, Real.rpow_one]; ring
    _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)

/-- The shift error with `η_{u'}⁻¹ ≤ B`: `eeShiftErrN ≤ W^d k L^d (2k+2) B^{2k+3} (u' - u)`
(RBM2D `NonAltEnd_eeShiftErr_le`, `NonAltEnd:694`, with `W^d`, `L^d`). -/
private theorem nqEnd_eeShiftErrN_le {d L W : ℕ} (hW : 1 ≤ W) {E : ℝ} (k : ℕ) {u u' B : ℝ}
    (hη0 : 0 ≤ (etaT E u')⁻¹) (hB : (etaT E u')⁻¹ ≤ B) (hΔ : 0 ≤ u' - u) :
    eeShiftErrN d L W E k u u' ≤
      (W : ℝ) ^ d * ((k : ℝ) * ((L : ℝ) ^ d * (((2 * k + 2 : ℕ) : ℝ) *
        (B ^ (2 * k + 2 + 1) * (u' - u))))) := by
  unfold eeShiftErrN loopShiftErrN
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hWi : (((W : ℝ) ^ d)⁻¹) ^ (2 * k + 2 - 1) ≤ 1 :=
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ hW1))
  have hWi0 : 0 ≤ (((W : ℝ) ^ d)⁻¹) ^ (2 * k + 2 - 1) := by positivity
  have h1 : (etaT E u')⁻¹ ^ (2 * k + 2 + 1) ≤ B ^ (2 * k + 2 + 1) := pow_le_pow_left₀ hη0 hB _
  have h2 : (etaT E u')⁻¹ ^ (2 * k + 2 + 1) * (((W : ℝ) ^ d)⁻¹) ^ (2 * k + 2 - 1) * (u' - u) ≤
      B ^ (2 * k + 2 + 1) * (u' - u) := by
    calc _ ≤ (etaT E u')⁻¹ ^ (2 * k + 2 + 1) * 1 * (u' - u) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWi (by positivity)) hΔ
      _ ≤ _ := by rw [mul_one]; exact mul_le_mul_of_nonneg_right h1 hΔ
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hl0 : (0 : ℝ) ≤ ((2 * k + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  gcongr

/-- (`hδ`, the shift hypothesis of `subGaussStop_linN`) `W^{-(D''+1)} + eeShiftErrN(u_j, u_{j+1}) ≤
W^{-D''}` for every `j < K n`, eventually: `eeShiftErrN ≤ k(2k+2) N^{2k+4} Δ`
(`W^d L^d = N`, `η_{u_{j+1}}⁻¹ ≤ η_v⁻¹ ≤ N`, `(W^{-d})^{2k+1} ≤ 1`), `Δ ≤ N^{-C_K}`,
`C_K ≥ D'' + 2k + 5`, `W ≥ 2`, `N ≥ 2k(2k+2)`, `N^{-D''} ≤ W^{-D''}` (RBM2D `NonAltEnd_ev_hδ`,
`NonAltEnd:717`). -/
private theorem nqEnd_ev_hδ (hd : 1 ≤ d) (hsize : sz.SizeTendsto) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠)
    (hband : sz.Bandwidth 𝔠) (k : ℕ) {D'' C_K : ℝ} {E s v : ℕ → ℝ} {K : ℕ → ℕ}
    (hE : ∀ n, |E n| < 2) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1)
    (hK0 : ∀ n, K n ≠ 0)
    (hη : ∀ᶠ n : ℕ in atTop, (etaT (E n) (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) (hD'' : 0 ≤ D'')
    (hCK : D'' + 2 * (k : ℝ) + 5 ≤ C_K)
    (hKN : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) :
    ∀ᶠ n : ℕ in atTop, ∀ j < K n, ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1)) +
      eeShiftErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤
        ((sz.W n : ℕ) : ℝ) ^ (-D'') := by
  set A : ℝ := (k : ℝ) * ((2 * k + 2 : ℕ) : ℝ) with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  filter_upwards [hη, hKN, nqEnd_ev_W_rpow_ge sz hsize h𝔠 hband one_pos 2,
    hsize.eventually_ge_atTop (2 * A), hsize.eventually_ge_atTop 1] with n hηn hKNn hW2 hNA hN1
  intro j hj
  rw [Real.rpow_one] at hW2
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hWN : ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := nqEnd_W_le_size sz hd n
  have hvs : v n - s n ≤ 1 := by linarith [hv1 n, hs0 n]
  have hΔ : gridStep s v K n ≤ ((sz.size n : ℕ) : ℝ) ^ (-C_K) := nqEnd_step_le sz hKNn hvs
  have hΔ0 : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n (hsv n)
  have hu'v : gridTime s v K n (j + 1) ≤ v n := by
    have h := ST_gridTime_mono s v K n (hsv n) (show j + 1 ≤ K n by omega)
    rwa [gridTime_last s v K n (hK0 n)] at h
  have hdiff := nqEnd_gridTime_succ_sub s v K n j
  have hEn := hE n
  have hηv : 0 < etaT (E n) (v n) := etaT_pos hEn (hv1 n)
  have hη' : 0 < etaT (E n) (gridTime s v K n (j + 1)) := etaT_pos hEn (hu'v.trans_lt (hv1 n))
  have hηle : (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
    refine le_trans (inv_anti₀ hηv ?_) hηn
    unfold etaT
    exact mul_le_mul_of_nonneg_right (by linarith) (mE_im_pos hEn).le
  have hη0 : 0 ≤ (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ := inv_nonneg.2 hη'.le
  have hee := nqEnd_eeShiftErrN_le (d := d) (L := sz.L n) (W := sz.W n) (sz.W_pos n) k
    (E := E n) (u := gridTime s v K n j) (u' := gridTime s v K n (j + 1)) hη0 hηle
    (by rw [hdiff]; exact hΔ0)
  rw [hdiff] at hee
  have hsz := nqEnd_size_cast sz n
  have hpow : ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (2 * k + 2 + 1) *
      ((sz.size n : ℕ) : ℝ) ^ (-C_K) = ((sz.size n : ℕ) : ℝ) ^ ((2 * (k : ℝ) + 4) - C_K) := by
    have e1 : ((sz.size n : ℕ) : ℝ) ^ (2 * k + 2 + 1) =
        ((sz.size n : ℕ) : ℝ) ^ (2 * (k : ℝ) + 3) := by
      rw [← Real.rpow_natCast]; push_cast; ring_nf
    rw [e1]
    calc ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (2 * (k : ℝ) + 3) *
          ((sz.size n : ℕ) : ℝ) ^ (-C_K)
        = ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (2 * (k : ℝ) + 3) *
          ((sz.size n : ℕ) : ℝ) ^ (-C_K) := by rw [Real.rpow_one]
      _ = ((sz.size n : ℕ) : ℝ) ^ (1 + (2 * (k : ℝ) + 3) + (-C_K)) := by
          rw [Real.rpow_add hN0 (1 + (2 * (k : ℝ) + 3)) (-C_K), Real.rpow_add hN0 (1 : ℝ)]
      _ = _ := by congr 1; ring
  have hmain : eeShiftErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j)
      (gridTime s v K n (j + 1)) ≤ A * ((sz.size n : ℕ) : ℝ) ^ (-(D'' + 1)) := by
    refine hee.trans ?_
    have e : ((sz.W n : ℕ) : ℝ) ^ d * ((k : ℝ) * (((sz.L n : ℕ) : ℝ) ^ d *
        (((2 * k + 2 : ℕ) : ℝ) * (((sz.size n : ℕ) : ℝ) ^ (2 * k + 2 + 1) * gridStep s v K n)))) =
        (((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d) * A *
          (((sz.size n : ℕ) : ℝ) ^ (2 * k + 2 + 1) * gridStep s v K n) := by rw [hA]; ring
    rw [e, hsz]
    calc ((sz.size n : ℕ) : ℝ) * A * (((sz.size n : ℕ) : ℝ) ^ (2 * k + 2 + 1) * gridStep s v K n)
        ≤ ((sz.size n : ℕ) : ℝ) * A * (((sz.size n : ℕ) : ℝ) ^ (2 * k + 2 + 1) *
            ((sz.size n : ℕ) : ℝ) ^ (-C_K)) := by gcongr
      _ = A * (((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (2 * k + 2 + 1) *
            ((sz.size n : ℕ) : ℝ) ^ (-C_K)) := by ring
      _ = A * ((sz.size n : ℕ) : ℝ) ^ ((2 * (k : ℝ) + 4) - C_K) := by rw [hpow]
      _ ≤ A * ((sz.size n : ℕ) : ℝ) ^ (-(D'' + 1)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) hA0
  have hN2 : A * ((sz.size n : ℕ) : ℝ) ^ (-(D'' + 1)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-D'') / 2 := by
    rw [show (-(D'' + 1)) = -D'' + -1 by ring, Real.rpow_add hN0, Real.rpow_neg_one]
    have h0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-D'') := Real.rpow_nonneg hN0.le _
    have h2A : A * ((sz.size n : ℕ) : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hN0]; linarith
    calc A * (((sz.size n : ℕ) : ℝ) ^ (-D'') * ((sz.size n : ℕ) : ℝ)⁻¹)
        = ((sz.size n : ℕ) : ℝ) ^ (-D'') * (A * ((sz.size n : ℕ) : ℝ)⁻¹) := by ring
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D'') * (1 / 2) := mul_le_mul_of_nonneg_left h2A h0
      _ = ((sz.size n : ℕ) : ℝ) ^ (-D'') / 2 := by ring
  have hWD : ((sz.size n : ℕ) : ℝ) ^ (-D'') ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'') :=
    Real.rpow_le_rpow_of_nonpos hWpos hWN (by linarith)
  have hWm1 : ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'') / 2 := by
    rw [show (-(D'' + 1)) = -D'' + -1 by ring, Real.rpow_add hWpos, Real.rpow_neg_one]
    have hpos : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'') := Real.rpow_nonneg hWpos.le _
    have : ((sz.W n : ℕ) : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) hW2
    calc ((sz.W n : ℕ) : ℝ) ^ (-D'') * ((sz.W n : ℕ) : ℝ)⁻¹
        ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'') * (1 / 2) := mul_le_mul_of_nonneg_left this hpos
      _ = _ := by ring
  linarith

end Regime

/-! ## 2c. The exponent bookkeeping

The order of the constants of `nqGridEndLinN` is `(d, k, Λg, κ') → C = nqGood1C → ε₀' = min ε₀ 1 →
ε₁ = εq = ε₀'/8 → ε = min (ε₀'/(8C)) (1/2) → τ' = ε/2 → D'' = C + k + 2 + (4k+2)/𝔠 → D' = D'' + 1 →
C_P → C_K`.  `nqEnd_arith` packages every inequality between these numbers that the absorption
lemmas and the regime facts need (so the endpoint and the instances use the same bookkeeping). -/

/-- **The exponent bookkeeping** at `ε = min (e0/(8C)) (1/2)`, `D'' = C + k + 2 + (4k+2)/𝔠`, `ε₁ = εq = e0/8`,
`D' = D'' + 1`, `ξ = -(2k+4)`: `0 < ε < 1`, `Cε ≤ e0/8`, `k + 1 < D''`, the conditions of `ha1`, `ha2`, `ha3`
(`Cε + ε₁ < e0`, `Cε + 2ε₁ < e0`, `εq + Cε + ε₁ < e0`), of `he1` (`C ≤ D'`, `k + 𝔠(C - D') < e0`), of `he2`
(all `W`-exponents `2Cε - D''`, `Cε + C - D''`, `C + k - D''` nonpositive, their `N`-exponents `≤ ξ`,
`εq + k + ξ/2 < e0`) and of `he3`, `he4` (`k - (k+1) < e0`).  A private `Prop`-valued structure. -/
private structure NQEndArith (k : ℕ) (𝔠 C e0 ε D'' : ℝ) : Prop where
  hε0 : 0 < ε
  hε1 : ε < 1
  hCε0 : 0 ≤ C * ε
  hCε : C * ε ≤ e0 / 8
  hD''k : (k : ℝ) + 1 < D''
  hD''0 : 0 ≤ D''
  E1 : C * ε + e0 / 8 < e0
  E2 : C * ε + 2 * (e0 / 8) < e0
  E3 : e0 / 8 + C * ε + e0 / 8 < e0
  hCD' : C ≤ D'' + 1
  E4 : (k : ℝ) + 𝔠 * (C - (D'' + 1)) < e0
  F1 : 2 * (C * ε) - D'' ≤ 0
  F2 : C * ε + C - D'' ≤ 0
  F3 : C + (k : ℝ) - D'' ≤ 0
  G1 : 2 * ((k : ℝ) - 1) + 𝔠 * (2 * (C * ε) - D'') ≤ -(2 * (k : ℝ) + 4)
  G2 : ((k : ℝ) - 1) + 𝔠 * (C * ε + C - D'') ≤ -(2 * (k : ℝ) + 4)
  G3 : 𝔠 * (C + (k : ℝ) - D'') ≤ -(2 * (k : ℝ) + 4)
  H1 : e0 / 8 + (k : ℝ) + (-(2 * (k : ℝ) + 4)) / 2 < e0
  H2 : (k : ℝ) - ((k : ℝ) + 1) < e0

private theorem nqEnd_arith (k : ℕ) (hk : 2 ≤ k) {𝔠 C e0 : ℝ} (h𝔠 : 0 < 𝔠) (hC : 0 < C)
    (he0 : 0 < e0) (he01 : e0 ≤ 1) {ε D'' : ℝ} (hε : ε = min (e0 / (8 * C)) (1 / 2))
    (hD : D'' = C + k + 2 + (4 * k + 2) / 𝔠) : NQEndArith k 𝔠 C e0 ε D'' := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hεpos : 0 < ε := by rw [hε]; exact lt_min (by positivity) (by norm_num)
  have hεle1 : ε ≤ e0 / (8 * C) := by rw [hε]; exact min_le_left _ _
  have hεle2 : ε ≤ 1 / 2 := by rw [hε]; exact min_le_right _ _
  have hCε : C * ε ≤ e0 / 8 := by
    calc C * ε ≤ C * (e0 / (8 * C)) := mul_le_mul_of_nonneg_left hεle1 hC.le
      _ = e0 / 8 := by field_simp
  have hCε0 : 0 ≤ C * ε := by positivity
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = (4 * k + 2) / 𝔠 := ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hqdef]; positivity
  have hq : 𝔠 * q = 4 * k + 2 := by rw [hqdef]; field_simp
  rw [← hqdef] at hD
  subst hD
  have hx1 : 𝔠 * (C * ε) ≤ 𝔠 * (1 / 8) :=
    mul_le_mul_of_nonneg_left (by linarith) h𝔠.le
  have hx2 : 0 ≤ 𝔠 * C := by positivity
  have hx3 : 0 ≤ 𝔠 * (k : ℝ) := by positivity
  have hx4 : 0 ≤ 𝔠 * (C * ε) := by positivity
  refine ⟨hεpos, by linarith, hCε0, hCε, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, ?_, by linarith, by linarith, by linarith, ?_, ?_, ?_, by linarith,
    by linarith⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
/-! ## 3. The assembly at the exit time `nqLinExitTauN`, for one sign vector

RBM2D `NonAltEnd_assembly` (`NonAltEnd:853`) with three substitutions: the exit time is `nqLinExitTauN`
(exit from `GoodSetN ∩ GoodLinN`), the drift field is `nqLin_hdriftN` at the level `dDriftLinN`, and the
right side is `assembledRHSLinN`.  `GoodSetN` is used through its level-free clauses and (D4) only
(`nonAlt_hA0clsN`, `nonAlt_hDclsN`, `subGaussStop_linN`), so its crude level `Φ` never enters the bound. -/

section Assembly

variable {d : ℕ} (sz : Sizes d)

/-- `0 ≤ u_i` on the grid `0 ≤ s_n ≤ v_n`. -/
private theorem nqEnd_gridTime_nonneg {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hs0 : 0 ≤ s n)
    (hsv : s n ≤ v n) (i : ℕ) : 0 ≤ gridTime s v K n i := by
  have h := ST_gridTime_mono s v K n hsv (Nat.zero_le i)
  rw [ST_gridTime_zero] at h
  linarith

/-- `u_i ≤ v_n` for `i ≤ K_n`, `K_n ≠ 0`. -/
private theorem nqEnd_gridTime_le {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hsv : s n ≤ v n)
    (hK : K n ≠ 0) {i : ℕ} (hi : i ≤ K n) : gridTime s v K n i ≤ v n :=
  (ST_gridTime_mono s v K n hsv hi).trans_eq (gridTime_last s v K n hK)

/-- The step error of `gridDriftN` is nonnegative (RBM2D `NonAltEnd_stepErrN_nonneg`,
`NonAltEnd:817`, with `W^d` in place of `W²`). -/
private theorem nqEnd_stepErrN_nonneg {d L W : ℕ} {E u v Δ Bk : ℝ} {k : ℕ} (hE : |E| < 2)
    (hu1 : u < 1) (hv1 : v < 1) (hΔ : 0 ≤ Δ) (hBk : 0 ≤ Bk) : 0 ≤ stepErrN d L W E k u v Δ Bk := by
  have hη : 0 < etaT E v := etaT_pos hE hv1
  have hv : 0 < 1 - v := by linarith
  have hηi : 0 ≤ (etaT E v)⁻¹ := inv_nonneg.2 hη.le
  have h1 : 0 ≤ envConst d L W E k v * Δ ^ ((3 : ℝ) / 2) := by
    unfold envConst
    exact mul_nonneg (by positivity) (Real.rpow_nonneg hΔ _)
  have h2 : 0 ≤ kStepC d L W k Bk * Δ ^ 2 := by
    unfold kStepC; positivity
  have h3 : 0 ≤ uStepC k Δ v := by
    unfold uStepC
    have hx : 0 ≤ Δ * (1 - v)⁻¹ := mul_nonneg hΔ (inv_nonneg.2 hv.le)
    have hb : 1 + (k : ℝ) * (Δ * (1 - v)⁻¹) ≤ (1 + Δ * (1 - v)⁻¹) ^ k := by
      have := one_add_mul_le_pow (a := Δ * (1 - v)⁻¹) (by linarith : (-2 : ℝ) ≤ Δ * (1 - v)⁻¹) k
      simpa using this
    have hk : 0 ≤ (k : ℝ) * Δ ^ 2 * (1 - v)⁻¹ ^ 2 := by positivity
    nlinarith
  have h4 : 0 ≤ (etaT E u)⁻¹ ^ k * (((W : ℝ) ^ d)⁻¹) ^ (k - 1) + Bk := by
    have : 0 ≤ (etaT E u)⁻¹ := inv_nonneg.2 (etaT_pos hE hu1).le
    positivity
  unfold stepErrN
  have := mul_nonneg h3 h4
  linarith

/-- **The assembly at the exit time, for one sign vector** (the merged `assembledN` at
`τ = nqLinExitTauN`).  With the data of `NQGood2` (`nonAltClsN`, `kappaNonAltN`, `epsNonAltN`,
`cQVNonAltN`), the linear drift level `dDriftLinN`, the sub-Gaussian input `subGaussStop_linN`, the `Y`
moments (`hY`) and the envelope of the step error (`gridDriftN_envelope`, `hKb`), eventually in `n`, for
every non-alternating `σ` on a strict window `s_n < v_n`, there is an event `G`,
`P(Gᶜ) ≤ N^{-D₁}`, on which the terminal bound `‖A_K(a)‖ ≤ assembledRHSLinN` holds as soon as the grid walk
stays in `GoodSetN ∩ GoodLinN`.  The per-`n` regime facts of `subGaussStop_linN` and the shift
hypothesis `hδ` are eventual premises.  Private: its binder `hY` mentions `YMomentBoundsN`. -/
private theorem nqEndLin_assembly {κ : ℝ} {E s v : ℕ → ℝ} {K : ℕ → ℕ} (k : ℕ) (hd : 3 ≤ d)
    (hk : 2 ≤ k) (hκ : 0 < κ) (hE : ∀ n, |E n| ≤ 2 - κ) (hs0 : ∀ n, 0 ≤ s n)
    (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1) (hK0 : ∀ n, K n ≠ 0) (hsize : sz.SizeTendsto)
    (hKb : sz.STKbound E) (Γ Λ Φ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (hΓ : ∀ n, 0 ≤ Γ n) (hΛ : ∀ n, 0 ≤ Λ n)
    (hΦ₁ : ∀ n, 0 ≤ Φ₁ n) (hΦ₂ : ∀ n, 0 ≤ Φ₂ n) (hΦ₃ : ∀ n, 0 ≤ Φ₃ n)
    {Λg κ' ε τ' D' D'' D_Y τK εq D₁ C_P C_K : ℝ} (hΛg : 0 < Λg) (hκ' : 0 < κ')
    (hκm : ∀ n, κ' ≤ (mE (E n)).im) (hε0 : 0 < ε) (hε1 : ε < 1) (hD'' : (k : ℝ) + 1 < D'')
    (hD' : 1 < D') (hτK : 0 < τK) (hεq : 0 < εq) (hCK0 : 0 ≤ C_K)
    (hCK : D₁ + 4 * D_Y + (k : ℝ) + 2 * C_P + 8 ≤ C_K)
    (hKN : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ))
    (hKU : ∀ᶠ n : ℕ in atTop, K n ≤ ⌈((sz.size n : ℕ) : ℝ) ^ C_K⌉₊)
    (hY : ∀ σ : Fin k → Bool, ∀ᶠ n : ℕ in atTop, ∃ P : ℝ, 0 ≤ P ∧
      P ≤ ((sz.size n : ℕ) : ℝ) ^ C_P ∧
      ∀ τ : PathΩ sz → ℕ, (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
        YMomentBoundsN sz (E n) σ (gridTime s v K n) τ (K n)
          (fun j ω => YvecN sz E s v K n j σ ω)
          (fun _ => gridStep s v K n ^ 2 * P) (fun _ => gridStep s v K n ^ 4 * P ^ 2))
    (hwL : ∀ n, v n ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hWt : ∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - v n) / (1 - s n))
    (hlam : ∀ᶠ n : ℕ in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λg)
    (hW1 : ∀ᶠ n : ℕ in atTop, 1 < ((sz.W n : ℕ) : ℝ))
    (hWε : ∀ᶠ n : ℕ in atTop, 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hdW : ∀ᶠ n : ℕ in atTop, (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hδ : ∀ᶠ n : ℕ in atTop, ∀ j < K n, ((sz.W n : ℕ) : ℝ) ^ (-D') +
      eeShiftErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤
        ((sz.W n : ℕ) : ℝ) ^ (-D'')) :
    ∀ᶠ n : ℕ in atTop, ∀ σ : Fin k → Bool, (∃ i, σ i = σ (finRotate k i)) → s n < v n →
      ∃ G : Set (PathΩ sz), (pathP sz).real Gᶜ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) ∧
        ∀ ω ∈ G,
          (∀ j ≤ K n, pathH sz s v K n j ω ∈
            sz.GoodSetN n (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D' ∩
              GoodLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)) →
          ∀ a : Fin k → Zd d (sz.L n),
            ‖AvecN sz E s v K n (K n) σ ω a‖ ≤
              assembledRHSLinN sz E s v K n k Λg κ' ε Γ Λ Φ₁ Φ₂ Φ₃ D' D'' D_Y τK εq
                (Finset.univ.sup' Finset.univ_nonempty fun b => ‖AvecN sz E s v K n 0 σ ω b‖) a := by
  have hA := assembledN sz hsize k εq hεq D_Y D₁ C_P C_K hCK0 hCK
  have hEnv : ∀ σ : Fin k → Bool, ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂(pathP sz), ∀ j, j < K n →
      ∀ a : Fin k → Zd d (sz.L n),
      ‖predIncN sz E s v K n j σ ω a - (gridStep s v K n : ℂ) *
          (∑ l ∈ Finset.Icc 3 k, sz.STksimLKM n (E n) (gridTime s v K n j)
              (pathH sz s v K n j ω) l (loopOf σ a) +
            sz.STelklkM n (E n) (gridTime s v K n j) (pathH sz s v K n j ω) (loopOf σ a) +
            sz.STegtM n (E n) (gridTime s v K n j) (pathH sz s v K n j ω) (loopOf σ a))‖ ≤
        stepErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1))
          (gridStep s v K n)
          (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ k) :=
    fun σ => gridDriftN_envelope sz κ hκ k hk τK hτK hsize hKb hE hs0 hsv hv1 hK0 σ
  filter_upwards [hA, hKN, hKU, Filter.eventually_all.2 hY, Filter.eventually_all.2 hEnv, hWt,
    hlam, hW1, hWε, hdW, hδ] with
    n hAn hKNn hKUn hYn hEnvn hWtn hlamn hW1n hWεn hdWn hδn
  intro σ hσ hsvn
  obtain ⟨P, hP0, hPle, hYP⟩ := hYn σ
  obtain ⟨hg, hgΛ⟩ := hlamn
  have hEn2 : |E n| < 2 := by have := hE n; linarith [abs_nonneg (E n)]
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith [abs_nonneg (E n)]
  have hKn : K n ≠ 0 := hK0 n
  have hK1 : 1 ≤ K n := Nat.one_le_iff_ne_zero.2 hKn
  have hvs : v n - s n ≤ 1 := by linarith [hv1 n, hs0 n]
  have hΔ : gridStep s v K n ≤ ((sz.size n : ℕ) : ℝ) ^ (-C_K) := nqEnd_step_le sz hKNn hvs
  have hKΔ : (K n : ℝ) * gridStep s v K n ≤ 1 := nqEnd_K_mul_step hKn hvs
  have hΔ0 : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n (hsv n)
  have hu0 : ∀ i ≤ K n, 0 ≤ gridTime s v K n i := fun i _ =>
    nqEnd_gridTime_nonneg (hs0 n) (hsv n) i
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi =>
    (nqEnd_gridTime_le (hsv n) hKn hi).trans_lt (hv1 n)
  have hmono : ∀ i m, i ≤ m → m ≤ K n → gridTime s v K n i ≤ gridTime s v K n m :=
    fun i m him _ => ST_gridTime_mono s v K n (hsv n) him
  have hW0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hW1' : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := hW1n.le
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := nqEnd_one_le_size sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hτmeas : ∀ j, MeasurableSet[filt sz j]
      {ω | j < nqLinExitTauN sz E s v K k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D' n ω} :=
    nqLinExitMeasN sz E s v K n k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D'
  have hmemG : ∀ (ω : PathΩ sz) (j : ℕ), j < nqLinExitTauN sz E s v K k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D' n ω →
      pathH sz s v K n j ω ∈ sz.GoodSetN n (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D' :=
    fun ω j hj => (mem_of_lt_nqLinExitTauN hj).1
  have hmemL : ∀ (ω : PathΩ sz) (j : ℕ), j < nqLinExitTauN sz E s v K k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D' n ω →
      pathH sz s v K n j ω ∈
        GoodLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) :=
    fun ω j hj => (mem_of_lt_nqLinExitTauN hj).2
  -- the data of the assembly
  set u : ℕ → ℝ := gridTime s v K n with hu
  set Δ : ℝ := gridStep s v K n with hΔdef
  set τ : PathΩ sz → ℕ := nqLinExitTauN sz E s v K k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D' n with hτdef
  set A0 : PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ := fun ω => AvecN sz E s v K n 0 σ ω with hA0
  set Dr : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ := fun j ω =>
    driftTensorN sz n (E n) (u j) (pathH sz s v K n j ω) σ with hDr
  set Z : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ := fun j ω => ZvecN sz E s v K n j σ ω
    with hZ
  set Y : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ := fun j ω => YvecN sz E s v K n j σ ω
    with hY'
  set R : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ := fun j ω =>
    predIncN sz E s v K n j σ ω - ((Δ : ℝ) : ℂ) • Dr j ω with hR
  set Af : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ := fun m ω =>
    Ugen d (sz.L n) (sz.lam n) (E n) σ (u 0) (u m) (A0 ω) +
      ∑ j ∈ Finset.range (min m (τ ω)), Ugen d (sz.L n) (sz.lam n) (E n) σ (u (j + 1)) (u m)
        (((Δ : ℝ) : ℂ) • Dr j ω + Z j ω + Y j ω + R j ω) with hAf
  set stepE : ℕ → ℝ := fun j => stepErrN d (sz.L n) (sz.W n) (E n) k (u j) (u (j + 1)) Δ
    (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (u (j + 1)))⁻¹ ^ k) with hstepE
  have hZmeas : ∀ j, StronglyMeasurable[filt sz (j + 1)] (Z j) := fun j =>
    gridAsm_stronglyMeasurable_ZvecN sz E s v K n j σ
  have hsubG : ∀ m ≤ K n, ∀ (a : Fin k → Zd d (sz.L n)) (j : ℕ), j < m →
      SubGaussStopN sz (E n) σ u τ Z m a j (cQVNonAltN sz E s v K n k Λg κ' ε Γ Λ D'' m a j) :=
    fun m hm a j hj => subGaussStop_linN Λg κ' hd hk hΛg hκ' sz hE2 hs0 hsv hv1 n (hwL n) hWtn
      (hκm n) hg hgΛ hW1n hε0 hε1 hWεn hdWn hD'' hσ Γ Λ Φ Φ₁ Φ₂ Φ₃ (hΓ n) (hΛ n) m hm a j hj
      (hδn j (lt_of_lt_of_le hj hm))
  have hu0K : u (K n) = v n := gridTime_last s v K n hKn
  have hu00 : u 0 = s n := ST_gridTime_zero s v K n
  have hbundle : GridAssemblyHypN sz (n := n) (k := k) (E n) σ u τ Δ (K n)
      (nonAltClsN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) τ' D' u) A0 Af Dr Z Y R
      (kappaNonAltN d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε u) (epsNonAltN d k Λg κ' ((sz.W n : ℕ) : ℝ))
      (((sz.W n : ℕ) : ℝ) ^ (-D'))
      (fun j _ => dDriftLinN sz n (E n) (u j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n))
      (fun _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D'))
      (fun m a j => cQVNonAltN sz E s v K n k Λg κ' ε Γ Λ D'' m a j)
      (fun _ => Δ ^ 2 * P) (fun _ => Δ ^ 4 * P ^ 2) stepE := {
    hE := hEn2.le
    hu0 := hu0
    hu1 := hu1
    hΔ0 := hΔ0
    hexp := fun m _ => Eventually.of_forall fun ω => rfl
    hκ0 := nonAlt_hκ0N d k Λg κ' (sz.lam n) _ ε hW0 (K n) u
    hε0 := nonAlt_hε0N d k Λg κ' _ hW0 (K n)
    hker := nonAlt_hkerN Λg κ' hd hk hΛg hκ' (sz.three_le_L n) hg hgΛ hW1n hε0 hε1 hWεn hdWn hD'
      hu0 hmono (by rw [hu0K]; exact hwL n) (by rw [hu0K, hu00]; exact hWtn) hEn2.le (hκm n) hσ
    hδ0 := Real.rpow_nonneg hW0 _
    hA0cls := nonAlt_hA0clsN sz (n := n) (by omega) hW1' σ E s v K Γ Λ Φ τ' D' D' le_rfl τ hmemG
    hdDrift0 := fun ω j hj => by
      have hη := etaT_pos hEn2 (hu1 j hj.le)
      have hB := Sizes.STBctl_pos sz n (hu1 j hj.le)
      have hk2 : (0 : ℝ) ≤ (k : ℝ) - 2 := by
        have : (2 : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      unfold dDriftLinN
      have h1 := hΓ n
      have h2 := hΦ₁ n
      have h3 := hΦ₂ n
      have h4 := hΦ₃ n
      positivity
    hδD0 := fun _ _ _ => Real.rpow_nonneg hW0 _
    hdrift := nqLin_hdriftN sz hk σ E s v K Γ Φ₁ Φ₂ Φ₃ τ hmemL
    hDcls := nonAlt_hDclsN sz E s v K (hsv n) (hv1 n) hW1' σ Γ Λ Φ τ' D' D' le_rfl τ hmemG
    hc_pos := cQVNonAltN_sum_pos sz E s v K n k Λg κ' ε (by omega) hsvn (hv1 n) hKn Γ Λ (hΛ n) D''
    hv0 := fun _ _ => by positivity
    hw0 := fun _ _ => by positivity
    hY := hYP τ hτmeas
    hstepErr0 := fun j hj => nqEnd_stepErrN_nonneg hEn2 (hu1 j hj.le) (hu1 (j + 1) hj) hΔ0
      (by
        have := etaT_pos hEn2 (hu1 (j + 1) hj)
        positivity)
    hR := (hEnvn σ).mono fun ω hω j hj _ b => by
      have h := hω j hj b
      simp only [hR, hDr, hstepE, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, driftTensorN]
      exact h }
  obtain ⟨G, hG, hGb⟩ := hAn (K n) (E n) σ u τ Δ
    (nonAltClsN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) τ' D' u) A0 Af Dr Z Y R
    (kappaNonAltN d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε u)
    (epsNonAltN d k Λg κ' ((sz.W n : ℕ) : ℝ)) (((sz.W n : ℕ) : ℝ) ^ (-D'))
    (fun j _ => dDriftLinN sz n (E n) (u j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n))
    (fun _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D'))
    (fun m a j => cQVNonAltN sz E s v K n k Λg κ' ε Γ Λ D'' m a j)
    (fun _ => Δ ^ 2 * P) (fun _ => Δ ^ 4 * P ^ 2) stepE P hK1 hKUn hΔ hKΔ hP0 hPle
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) hτmeas hZmeas hsubG hbundle
  refine ⟨G, hG, fun ω hω hgood a => ?_⟩
  have hτeq : τ ω = K n := gridExitTauN_eq_of_forall_mem hgood
  have hτpos : 0 < τ ω := by rw [hτeq]; omega
  have hb := hGb ω hω hτpos (K n) le_rfl a
  have hex := stoppedDuhamelN_at sz E s v K n hEn2 (hs0 n) (hsv n) (hv1 n) hKn σ τ (K n) ω
    (min_le_left _ _)
  have hAeq : Af (K n) ω = AvecN sz E s v K n (K n) σ ω := by
    have hex' : AvecN sz E s v K n (K n) σ ω =
        Ugen d (sz.L n) (sz.lam n) (E n) σ (u 0) (u (K n)) (AvecN sz E s v K n 0 σ ω) +
          ∑ j ∈ Finset.range (K n), Ugen d (sz.L n) (sz.lam n) (E n) σ (u (j + 1)) (u (K n))
            (predIncN sz E s v K n j σ ω + martIncN sz E s v K n j σ ω) := by
      rw [hτeq, min_self] at hex
      exact hex
    have hinner : ∀ j, ((Δ : ℝ) : ℂ) • Dr j ω + Z j ω + Y j ω + R j ω =
        predIncN sz E s v K n j σ ω + martIncN sz E s v K n j σ ω := by
      intro j; funext b
      simp only [hR, hZ, hY', hDr, YvecN, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hex']
    simp only [hAf, hτeq, min_self, hinner, hA0]
  rw [hAeq] at hb
  exact hb

end Assembly

/-! ## 4. The collapsed window, the union bound, the `Y`-moment constant, the range condition -/

section Endpoint

variable {d : ℕ} (sz : Sizes d)

/-- If `v_n = s_n` the grid walk does not move: `Δ = 0` and every `H_j = H_0` (RBM2D
`NonAltEnd_pathH_collapse`, `NonAltEnd:1014`). -/
private theorem nqEnd_pathH_collapse {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hsv : s n = v n) (j : ℕ)
    (ω : PathΩ sz) : pathH sz s v K n j ω = pathH sz s v K n 0 ω := by
  have hΔ : gridStep s v K n = 0 := by unfold gridStep; rw [← hsv]; simp
  unfold pathH
  rw [hΔ]
  simp

/-- **The collapsed window** (the case `v_n = s_n` of the endpoint, where `hc_pos` of the assembly
fails): `H_K = H_0` and `u_K = s`, so the initial bound `‖(𝓛-𝒦)_s‖ ≤ N^{ε₁} B_s^k` with `ε₁ ≤ ε₀`, `N ≥ 1`,
`Λ ≥ 1`, `Φ_i ≥ 0` and `B_s^k ≥ 0` is the conclusion `‖(𝓛-𝒦)_v‖ ≤ N^{ε₀} (Λ^{1/2} + Φ₁ + Φ₂ + Φ₃) B_v^k`
(RBM2D `NonAltEnd_collapse`, `NonAltEnd:1025`). -/
private theorem nqEnd_collapse {E s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hv1 : v n < 1)
    (hsv : s n = v n) {k : ℕ} {ε₁ ε₀ Λ Φ₁ Φ₂ Φ₃ : ℝ} (hε : ε₁ ≤ ε₀) (hΛ : 1 ≤ Λ) (hΦ₁ : 0 ≤ Φ₁)
    (hΦ₂ : 0 ≤ Φ₂) (hΦ₃ : 0 ≤ Φ₃) (ω : PathΩ sz) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n))
    (hinit : ‖sz.STLKM n (E n) (s n) (pathH sz s v K n 0 ω) σ a‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ k) :
    ‖sz.STLKM n (E n) (v n) (pathH sz s v K n (K n) ω) σ a‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ ^ ((1 : ℝ) / 2) + Φ₁ + Φ₂ + Φ₃) * (sz.Bctl n (v n)) ^ k := by
  rw [nqEnd_pathH_collapse sz hsv (K n) ω, ← hsv]
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := nqEnd_one_le_size sz n
  have hs1 : s n < 1 := by rw [hsv]; exact hv1
  have hB : 0 ≤ (sz.Bctl n (s n)) ^ k := pow_nonneg (Sizes.STBctl_pos sz n hs1).le _
  have h1 : ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ :=
    Real.rpow_le_rpow_of_exponent_le hN1 hε
  have h2 : 1 ≤ Λ ^ ((1 : ℝ) / 2) + Φ₁ + Φ₂ + Φ₃ := by
    have := Real.one_le_rpow hΛ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith
  have h3 : ((sz.size n : ℕ) : ℝ) ^ ε₀ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ *
      (Λ ^ ((1 : ℝ) / 2) + Φ₁ + Φ₂ + Φ₃) :=
    le_mul_of_one_le_right (Real.rpow_nonneg (by linarith) _) h2
  exact hinit.trans (mul_le_mul_of_nonneg_right (h1.trans h3) hB)

/-- The range condition passes to a smaller exponent and an earlier time (RBM2D
`NonAltEnd_rangeCond_mono`, `NonAltEnd:1059`). -/
private theorem nqEnd_rangeCond_mono {τ τR : ℝ} {t v : ℕ → ℝ} (hτ : τR ≤ τ)
    (hvt : ∀ n, v n ≤ t n) (h : sz.RangeCond τ t) : sz.RangeCond τR v := by
  filter_upwards [h] with n hn
  calc ((sz.size n : ℕ) : ℝ) ^ (-1 + τR) ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 + τ) :=
        Real.rpow_le_rpow_of_exponent_le (nqEnd_one_le_size sz n) (by linarith)
    _ ≤ 1 - t n := hn
    _ ≤ 1 - v n := by linarith [hvt n]

/-- The union bound over the sign vectors: `2^k N^{-(D+1)} ≤ N^{-D}` eventually (RBM2D
`NonAltEnd_ev_union`, `NonAltEnd:1068`). -/
private theorem nqEnd_ev_union (hsize : sz.SizeTendsto) (k : ℕ) (D : ℝ) :
    ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-(D + 1)) ≤
      ((sz.size n : ℕ) : ℝ) ^ (-D) := by
  filter_upwards [hsize.eventually_ge_atTop ((2 : ℝ) ^ k), hsize.eventually_ge_atTop 1] with n hn hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  rw [show (-(D + 1)) = -D + -1 by ring, Real.rpow_add hN0, Real.rpow_neg_one]
  have h := Real.rpow_nonneg hN0.le (-D)
  calc (2 : ℝ) ^ k * (((sz.size n : ℕ) : ℝ) ^ (-D) * ((sz.size n : ℕ) : ℝ)⁻¹)
      = ((sz.size n : ℕ) : ℝ) ^ (-D) * ((2 : ℝ) ^ k / ((sz.size n : ℕ) : ℝ)) := by ring
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ h
        rw [div_le_one hN0]; exact hn
    _ = _ := mul_one _

/-- **The uniform `Y` moments for all signs with one `C_P`** (before the grid `K`): the maximum over the
`2^k` sign vectors of the constants of `yMomentsUnifN` serves every sign (`N ≥ 1`; RBM2D
`NonAltEnd_yMomentsMax`, `NonAltEnd:1092`). -/
private theorem nqEnd_yMomentsMax {κ τR : ℝ} {E s v : ℕ → ℝ} (hκ : 0 < κ)
    (hE : ∀ n, |E n| ≤ 2 - κ) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1)
    (hsize : sz.SizeTendsto) (hrange : sz.RangeCond τR v) (k : ℕ) :
    ∃ C_P : ℝ, 0 ≤ C_P ∧ ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → ∀ σ : Fin k → Bool,
      ∀ᶠ n : ℕ in atTop, ∃ P : ℝ, 0 ≤ P ∧ P ≤ ((sz.size n : ℕ) : ℝ) ^ C_P ∧
        ∀ τ : PathΩ sz → ℕ, (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
          YMomentBoundsN sz (E n) σ (gridTime s v K n) τ (K n)
            (fun j ω => YvecN sz E s v K n j σ ω)
            (fun _ => gridStep s v K n ^ 2 * P) (fun _ => gridStep s v K n ^ 4 * P ^ 2) := by
  choose CP hCP0 hCPev using fun σ : Fin k → Bool =>
    yMomentsUnifN sz κ τR E s v hκ hE hs0 hsv hv1 hsize hrange k σ
  refine ⟨Finset.univ.sup' Finset.univ_nonempty CP,
    (hCP0 (fun _ => true)).trans (Finset.le_sup' CP (Finset.mem_univ _)), fun K hK0 σ => ?_⟩
  filter_upwards [hCPev σ K hK0] with n hn
  obtain ⟨P, hP0, hPle, hτ⟩ := hn
  exact ⟨P, hP0, hPle.trans (Real.rpow_le_rpow_of_exponent_le (nqEnd_one_le_size sz n)
    (Finset.le_sup' CP (Finset.mem_univ σ))), hτ⟩

end Endpoint

/-! ## 5. The grid endpoint `nqGridEndLinN`

RBM2D `nonAltGridEnd` (`NonAltEnd:1116-1276`).  The statement is the pin `T2199_nqGridEndLinN` of
`docs/tickets/checks/T2199-check.lean`, copied verbatim (script diff in the report).  Exponents (fixed
order): `Λg = 𝔡⁻¹`, `κ' = min κ (4/5)`, `C = nqGood1C d k Λg κ'`, `ε₀' = min ε₀ 1`, `ε₁ = εq = ε₀'/8`,
`ε = min (ε₀'/(8C)) (1/2)`, `τ' = ε/2`, `D'' = C + k + 2 + (4k+2)/𝔠`, `D' = D'' + 1`, `τ_K = 1`,
`D_Y = D_t = k + 1`, `C_P^* = max_σ C_P(σ)` (`yMomentsUnifN`), `C_K = D₁ + 2 C_P^* + 6k + 20 + D''`. -/

/-- **`nqGridEndLinN`: the non-alternating grid endpoint with the linear right side** (`lem:STOeq_NQ`,
`3_5:1136`, proof `3_5:1152-1180`; RBM2D `nonAltGridEnd`, `NonAltEnd:1116` at `c9a24cf`).  For every length
`k ≥ 2`, deterministic levels `Λ ≥ 0` (`≥ 1` eventually), `Φ₁, Φ₂, Φ₃ ≥ 0`, end time `v ∈ [s,t]`, final loss
`ε₀ > 0` and failure exponent `D₁ > 0` there are exponents `ε₁, τ', D', C_K` such that, for every crude level
`Φc` of `GoodSetN` and every grid `N^{C_K} ≤ K_n ≤ ⌈N^{C_K}⌉`, eventually there is an event `G`,
`P(Gᶜ) ≤ N^{-D₁}`, on which: if the grid walk is in `GoodSetN(N^{ε₁}, Λ, Φc, τ', D') ∩
GoodLinN(N^{ε₁}, Φ₁, Φ₂, Φ₃)` at every `j ≤ K_n` and the initial loops satisfy
`|(𝓛-𝒦)_{s,σ,a}| ≤ N^{ε₁} B_s^k` for the non-alternating `σ`, then
`|(𝓛-𝒦)_{v,σ,a}(H_{K_n})| ≤ N^{ε₀}(Λ^{1/2} + Φ₁ + Φ₂ + Φ₃) B_v^k` for every non-alternating `σ` and label
`a`.  No `Φ²`, no `Φc` on the right side; no `STKbound` premise (`stKbound_holds` discharges it); the
good-event probability is S3-12c's. -/
theorem nqGridEndLinN :
  ∀ {d : ℕ} (sz : Sizes d) (κ 𝔠 τ 𝔡 : ℝ) (E s t : ℕ → ℝ),
    3 ≤ d → 0 < κ → 0 < 𝔠 → 0 < τ → 0 < 𝔡 →
    sz.SizeTendsto → sz.Bandwidth 𝔠 → sz.WO 𝔡 →
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    sz.STCaseI s t → sz.RangeCond τ t →
    (∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - t n) / (1 - s n)) →
    ∀ k : ℕ, 2 ≤ k →
    ∀ Λ Φ₁ Φ₂ Φ₃ : ℕ → ℝ, (∀ n, 0 ≤ Λ n) → (∀ᶠ n : ℕ in atTop, 1 ≤ Λ n) →
      (∀ n, 0 ≤ Φ₁ n) → (∀ n, 0 ≤ Φ₂ n) → (∀ n, 0 ≤ Φ₃ n) →
    ∀ v : ℕ → ℝ, (∀ n, s n ≤ v n) → (∀ n, v n ≤ t n) →
    ∀ ε₀ : ℝ, 0 < ε₀ → ∀ D₁ : ℝ, 0 < D₁ →
    ∃ ε₁ τ' D' C_K : ℝ, 0 < ε₁ ∧ 0 < τ' ∧ 0 < D' ∧ 0 ≤ C_K ∧
    ∀ (Φc : ℕ → ℝ) (K : ℕ → ℕ), (∀ n, K n ≠ 0) →
      (∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) →
      (∀ᶠ n : ℕ in atTop, K n ≤ ⌈((sz.size n : ℕ) : ℝ) ^ C_K⌉₊) →
      ∀ᶠ n : ℕ in atTop, ∃ G : Set (PathΩ sz),
        (pathP sz).real Gᶜ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) ∧
        ∀ ω ∈ G,
          (∀ j ≤ K n, pathH sz s v K n j ω ∈
            sz.GoodSetN n (E n) (gridTime s v K n j) k (((sz.size n : ℕ) : ℝ) ^ ε₁) (Λ n)
                (Φc n) τ' D' ∩
              GoodLinN sz n (E n) (gridTime s v K n j) k (((sz.size n : ℕ) : ℝ) ^ ε₁)
                (Φ₁ n) (Φ₂ n) (Φ₃ n)) →
          (∀ σ : Fin k → Bool, (∃ i, σ i = σ (finRotate k i)) → ∀ a : Fin k → Zd d (sz.L n),
            ‖sz.STLKM n (E n) (s n) (pathH sz s v K n 0 ω) σ a‖ ≤
              ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ k) →
          ∀ σ : Fin k → Bool, (∃ i, σ i = σ (finRotate k i)) → ∀ a : Fin k → Zd d (sz.L n),
            ‖sz.STLKM n (E n) (v n) (pathH sz s v K n (K n) ω) σ a‖ ≤
              ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n) *
                (sz.Bctl n (v n)) ^ k := by
  intro d sz κ 𝔠 τ 𝔡 E s t hd hκ h𝔠 hτ h𝔡 hsize hband hWO hE hs0 hst ht1 hcase hrange hWt k hk
    Λ Φ₁ Φ₂ Φ₃ hΛ0 hΛ1 hΦ₁ hΦ₂ hΦ₃ v hsv hvt ε₀ hε₀ D₁ hD₁
  classical
  have hd1 : 1 ≤ d := by omega
  have hv1 : ∀ n, v n < 1 := fun n => (hvt n).trans_lt (ht1 n)
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith [abs_nonneg (E n)]
  -- the energy gap `κ' = min κ (4/5) ≤ Im m(E n)` and the coupling window `0 < lam n ≤ Λg = 𝔡⁻¹`
  obtain ⟨κ', hκ'def⟩ : ∃ κ' : ℝ, κ' = min κ (4 / 5) := ⟨_, rfl⟩
  obtain ⟨Λg, hΛgdef⟩ : ∃ Λg : ℝ, Λg = 𝔡⁻¹ := ⟨_, rfl⟩
  have hκ' : 0 < κ' := by rw [hκ'def]; exact lt_min hκ (by norm_num)
  have hκm : ∀ n, κ' ≤ (mE (E n)).im := fun n => by
    rw [hκ'def]; exact nqGood1_mE_im_ge hκ (hE n)
  have hΛg : 0 < Λg := by rw [hΛgdef]; exact inv_pos.2 h𝔡
  have hlam : ∀ᶠ n : ℕ in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λg := by
    rw [hΛgdef]
    filter_upwards [hWO] with n hn
    have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) hn.1, hn.2⟩
  -- `STKbound` is not a premise: it follows from `3 ≤ d`, `N → ∞`, the bulk and the window of `lam`
  have hKb : sz.STKbound E := stKbound_holds sz hd hκ hΛg hsize (Eventually.of_forall hE) hlam
  -- the range exponent of the end time, the `Y`-moment constant (one for all signs, before the grid)
  have hτR : 0 < min τ 1 := lt_min hτ one_pos
  have hτR1 : min τ 1 ≤ 1 := min_le_right _ _
  have hrangeV : sz.RangeCond (min τ 1) v := nqEnd_rangeCond_mono sz (min_le_left _ _) hvt hrange
  obtain ⟨Cmax, hCmax0, hYmax⟩ := nqEnd_yMomentsMax sz hκ hE hs0 hsv hv1 hsize hrangeV k
  -- the numerical constants, in the fixed order `C → ε₀' → ε₁ → ε → D'' → D' → C_P → C_K`
  obtain ⟨e0, he0def⟩ : ∃ e0 : ℝ, e0 = min ε₀ 1 := ⟨_, rfl⟩
  have he0 : 0 < e0 := by rw [he0def]; exact lt_min hε₀ one_pos
  have he01 : e0 ≤ 1 := by rw [he0def]; exact min_le_right _ _
  have he0le : e0 ≤ ε₀ := by rw [he0def]; exact min_le_left _ _
  have hC : 0 < nqGood1C d k Λg κ' := nqGood1C_pos hd hk hΛg hκ'
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (e0 / (8 * nqGood1C d k Λg κ')) (1 / 2) := ⟨_, rfl⟩
  obtain ⟨D'', hD''def⟩ : ∃ D'' : ℝ, D'' = nqGood1C d k Λg κ' + k + 2 + (4 * k + 2) / 𝔠 :=
    ⟨_, rfl⟩
  obtain ⟨hε0, hε1, hCε0, hCε, hD''k, hD''0, E1, E2, E3, hCD', E4, F1, F2, F3, G1, G2, G3, H1,
    H2⟩ := nqEnd_arith k hk h𝔠 hC he0 he01 hεdef hD''def
  obtain ⟨C_K, hCKdef⟩ : ∃ C_K : ℝ, C_K = D₁ + 2 * Cmax + 6 * k + 20 + D'' := ⟨_, rfl⟩
  have hk0 : (0 : ℝ) < k := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hCK0 : 0 ≤ C_K := by rw [hCKdef]; linarith
  refine ⟨e0 / 8, ε / 2, D'' + 1, C_K, by linarith, by linarith, by linarith, hCK0, ?_⟩
  intro Φc K hK0 hKN hKU
  -- the exponent constraints on `C_K`
  have hθ1 : 1 - min τ 1 ≤ 1 := by linarith
  have hθk1 : (4 * (k : ℝ) + 8) * (1 - min τ 1) ≤ 4 * k + 8 :=
    mul_le_of_le_one_right (by positivity) hθ1
  have hθk2 : 5 * (k : ℝ) * (1 - min τ 1) ≤ 5 * k := mul_le_of_le_one_right (by positivity) hθ1
  have hθk3 : 2 * (k : ℝ) * (1 - min τ 1) ≤ 2 * k := mul_le_of_le_one_right (by positivity) hθ1
  have hC1 : (D₁ + 1) + 4 * ((k : ℝ) + 1) + (k : ℝ) + 2 * Cmax + 8 ≤ C_K := by
    rw [hCKdef]; linarith
  have hC2 : 8 + (4 * (k : ℝ) + 8) * (1 - min τ 1) + 2 * ((k : ℝ) + 1) < C_K := by
    rw [hCKdef]; linarith
  have hC3 : 3 + 4 * (1 : ℝ) + 5 * (k : ℝ) * (1 - min τ 1) + ((k : ℝ) + 1) < C_K := by
    rw [hCKdef]; linarith
  have hC4 : 2 * (1 - min τ 1) + 1 + 2 * (k : ℝ) * (1 - min τ 1) + ((k : ℝ) + 1) < C_K := by
    rw [hCKdef]; linarith
  have hC5 : 1 - min τ 1 < C_K := by rw [hCKdef]; linarith
  have hC6 : D'' + 2 * (k : ℝ) + 5 ≤ C_K := by rw [hCKdef]; linarith
  have hC7 : 1 ≤ C_K := by rw [hCKdef]; linarith
  -- the eventual regime facts
  have hη := nqEnd_ev_hη sz hsize hκ' hκm hτR hrangeV
  have hδ := nqEnd_ev_hδ sz hd1 hsize h𝔠 hband k hE2 hs0 hsv hv1 hK0 hη hD''0 hC6 hKN
  have hlogR := nqBudget_merged_inputs sz (κ := κ) (τ' := min τ 1) (τK := 1) (C_K := C_K)
    (D_t := (k : ℝ) + 1) (E := E) (s := s) (v := v) (K := K) k hκ hτR hτR1 one_pos
    (by linarith) hk hsize hE hs0 hsv hv1 hK0 hrangeV hC2 hC3 hC4 hC5 hKN
  have hWt' : ∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - v n) / (1 - s n) := by
    filter_upwards [hWt] with n hn
    refine hn.trans ?_
    have h1 : 0 < 1 - s n := by linarith [hst n, ht1 n]
    exact div_le_div_of_nonneg_right (by linarith [hvt n]) h1.le
  have hwL : ∀ n, v n ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := fun n => by
    have := hcase n
    linarith [hvt n]
  have hW1 : ∀ᶠ n : ℕ in atTop, 1 < ((sz.W n : ℕ) : ℝ) := by
    filter_upwards [nqEnd_ev_W_rpow_ge sz hsize h𝔠 hband one_pos 2] with n hn
    rw [Real.rpow_one] at hn
    linarith
  have hWε : ∀ᶠ n : ℕ in atTop, 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε :=
    nqEnd_ev_W_rpow_ge sz hsize h𝔠 hband hε0 4
  have hdW : ∀ᶠ n : ℕ in atTop,
      (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (ε / 2) ≤ ((sz.W n : ℕ) : ℝ) ^ ε := by
    filter_upwards [nqEnd_ev_W_rpow_ge sz hsize h𝔠 hband (show 0 < ε / 2 by linarith) (d : ℝ)]
      with n hn
    have hW0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
    calc (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (ε / 2)
        ≤ ((sz.W n : ℕ) : ℝ) ^ (ε / 2) * ((sz.W n : ℕ) : ℝ) ^ (ε / 2) :=
          mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hW0 _)
      _ = ((sz.W n : ℕ) : ℝ) ^ ε := by
          rw [← Real.rpow_add' hW0 (by linarith)]; congr 1; ring
  -- the seven absorption lemmas of `budgetNonAltLinN`
  have ha1 := nqEnd_ev_ha1 sz hd1 hsize hCε0 E1
  have ha2 := nqEnd_ev_ha2 sz hd1 hsize k hκ' hκm hCε0 E2
  have ha3 := nqEnd_ev_ha3 sz hd1 hsize k hκ' hκm hCε0 E3
  have he1 := nqEnd_ev_he1 sz hsize hband (k := k) hCD' E4
  have he2 := nqEnd_ev_he2 sz hsize hband (by omega) hlam F1 F2 F3 G1 G2 G3 H1
  have he3 := nqEnd_ev_he4 sz hsize k (D := (k : ℝ) + 1) H2
  have he4 := nqEnd_ev_he4 sz hsize k (D := (k : ℝ) + 1) H2
  have hun := nqEnd_ev_union sz hsize k D₁
  -- the assembly at the exit time `nqLinExitTauN` (per sign vector, `D₁ + 1`)
  have hΓ0 : ∀ n, 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (e0 / 8) := fun n =>
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hAsm := nqEndLin_assembly sz (κ := κ) (E := E) (s := s) (v := v) (K := K) k hd hk hκ hE
    hs0 hsv hv1 hK0 hsize hKb (fun n => ((sz.size n : ℕ) : ℝ) ^ (e0 / 8)) Λ Φc Φ₁ Φ₂ Φ₃ hΓ0 hΛ0
    hΦ₁ hΦ₂ hΦ₃ (Λg := Λg) (κ' := κ') (ε := ε) (τ' := ε / 2) (D' := D'' + 1) (D'' := D'')
    (D_Y := (k : ℝ) + 1) (τK := 1) (εq := e0 / 8) (D₁ := D₁ + 1) (C_P := Cmax) (C_K := C_K)
    hΛg hκ' hκm hε0 hε1 hD''k (by linarith) one_pos (by linarith) hCK0 hC1 hKN hKU
    (hYmax K hK0) hwL hWt' hlam hW1 hWε hdW hδ
  filter_upwards [hAsm, hη, hlogR, ha1, ha2, ha3, he1, he2, he3, he4, hΛ1, hun, hKN] with n hAsmn
    hηn hlogRn ha1n ha2n ha3n he1n he2n he3n he4n hΛ1n hunn hKNn
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := nqEnd_one_le_size sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  by_cases hsvn : s n = v n
  · -- the collapsed window `v_n = s_n`: `G = univ`
    refine ⟨Set.univ, ?_, fun ω _ _ hinit' σ hσ a => ?_⟩
    · rw [Set.compl_univ]
      simp only [measureReal_empty]
      exact Real.rpow_nonneg hN0.le _
    · exact nqEnd_collapse sz (hv1 n) hsvn (by linarith) hΛ1n (hΦ₁ n) (hΦ₂ n) (hΦ₃ n) ω σ a
        (hinit' σ hσ a)
  · have hlt : s n < v n := lt_of_le_of_ne (hsv n) hsvn
    have hK1 : 1 ≤ K n := Nat.one_le_iff_ne_zero.2 (hK0 n)
    have hvs : v n - s n ≤ 1 := by linarith [hv1 n, hs0 n]
    have hη0 : 0 ≤ (etaT (E n) (v n))⁻¹ := inv_nonneg.2 (etaT_pos (hE2 n) (hv1 n)).le
    have hΔη := nqEnd_hΔη sz (C_K := C_K) (η := etaT (E n) (v n)) hC7 hKNn hvs hη0 hηn
    -- the events, one per non-alternating sign vector
    have hAsmσ := fun σ : {σ : Fin k → Bool // ∃ i, σ i = σ (finRotate k i)} =>
      hAsmn σ.1 σ.2 hlt
    choose Gs hGsP hGsb using hAsmσ
    refine ⟨⋂ σ, Gs σ, ?_, ?_⟩
    · -- the union bound over the `≤ 2^k` sign vectors
      have hcompl : (⋂ σ, Gs σ)ᶜ = ⋃ σ, (Gs σ)ᶜ := by rw [Set.compl_iInter]
      rw [hcompl]
      calc (pathP sz).real (⋃ σ, (Gs σ)ᶜ) ≤ ∑ σ, (pathP sz).real (Gs σ)ᶜ :=
            measureReal_iUnion_fintype_le _
        _ ≤ ∑ _σ : {σ : Fin k → Bool // ∃ i, σ i = σ (finRotate k i)},
              ((sz.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) := Finset.sum_le_sum fun σ _ => hGsP σ
        _ = (Fintype.card {σ : Fin k → Bool // ∃ i, σ i = σ (finRotate k i)} : ℝ) *
              ((sz.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) := by simp
        _ ≤ (2 : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hN0.le _)
            have h1 := Fintype.card_subtype_le (fun σ : Fin k → Bool => ∃ i, σ i = σ (finRotate k i))
            have h2 : Fintype.card (Fin k → Bool) = 2 ^ k := by simp
            rw [h2] at h1
            exact_mod_cast h1
        _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) := hunn
    · intro ω hω hgood hinit' σ hσ a
      have hωσ : ω ∈ Gs ⟨σ, hσ⟩ := Set.mem_iInter.1 hω ⟨σ, hσ⟩
      have hb := hGsb ⟨σ, hσ⟩ ω hωσ hgood a
      have hX0 : (Finset.univ.sup' Finset.univ_nonempty fun b => ‖AvecN sz E s v K n 0 σ ω b‖) ≤
          ((sz.size n : ℕ) : ℝ) ^ (e0 / 8) * (sz.Bctl n (s n)) ^ k := by
        refine Finset.sup'_le _ _ fun b _ => ?_
        have h := hinit' σ hσ b
        have e : ‖AvecN sz E s v K n 0 σ ω b‖ =
            ‖sz.STLKM n (E n) (s n) (pathH sz s v K n 0 ω) σ b‖ := by
          simp only [AvecN, ST_gridTime_zero]
        rw [e]
        exact h
      have hbud := budgetNonAltLinN sz E s v K n k Λg κ' ε
        (fun n => ((sz.size n : ℕ) : ℝ) ^ (e0 / 8)) Λ Φ₁ Φ₂ Φ₃ (D'' + 1) D'' ((k : ℝ) + 1)
        ((k : ℝ) + 1) 1 (e0 / 8) e0 (e0 / 8)
        (Finset.univ.sup' Finset.univ_nonempty fun b => ‖AvecN sz E s v K n 0 σ ω b‖) a hk
        (by linarith) (hE2 n) (hs0 n) (hsv n) (hv1 n) (hK0 n) hηn hΔη rfl hΛ1n (hΦ₁ n) (hΦ₂ n)
        (hΦ₃ n) hlogRn.1 hX0 hlogRn.2 ha1n ha2n ha3n he1n he2n he3n he4n
      have hlk : ‖sz.STLKM n (E n) (v n) (pathH sz s v K n (K n) ω) σ a‖ =
          ‖AvecN sz E s v K n (K n) σ ω a‖ := by
        simp only [AvecN, gridTime_last s v K n (hK0 n)]
      rw [hlk]
      refine hb.trans (hbud.trans ?_)
      have hB : 0 ≤ (sz.Bctl n (v n)) ^ k := pow_nonneg (Sizes.STBctl_pos sz n (hv1 n)).le _
      have hS : 0 ≤ Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n := by
        have := Real.rpow_nonneg (hΛ0 n) ((1 : ℝ) / 2)
        have := hΦ₁ n
        have := hΦ₂ n
        have := hΦ₃ n
        linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hN1 he0le) hS) hB

/-! ## 6. Compiled nonempty instances at `d = 3`

Namespace `RBM.Ind.NQEndLinInst`.  Data (the merged instance data): `sz0` (`d = 3`, `L = 4(n+1)`,
`W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`, `N = (WL)^3`; `n = 0`: `L = 4`, `W = 32`, `N = 2^21`;
`sz0_tendsto`, `sz0_bandwidth` `𝔠 = 1/6`, `sz0_WO` `𝔡 = 1/10`), `E = Einst ≡ 1/2` (`Im m = √15/4 ≈ 0.968`),
`κ = 1` (`κ' = min κ (4/5) = 4/5`), `s = sInst ≡ 0`, `t = tInst ≡ 1/16`, `v = vg ≡ 1/32`, `τ = 1/2`
(`RangeCond (1/2) tInst` from the merged `rangeCond_half`), `STCaseI` = `sz0_caseI`, `W⁻¹ ≤ 15/16` from
`W_ge_32`; `k = 3`, `σ = sig3 = (+,-,+)`, `Λ = Λ3 ≡ 3`, `Φ₁ = Φ₃ = Φc = Φ1 ≡ 1`, `Φ₂ ≡ 12`, `ε₀ = 1/10`,
`D₁ = 1`.  The grid is `KC C_K n = max 1 ⌈N^{C_K}⌉` (so `N^{C_K} ≤ K_n ≤ ⌈N^{C_K}⌉`).  The constant
`C = nqGood1C 3 3 10 κ'` of EK-6 stays abstract (`Classical.choose`; only `C > 0` is known), so every
instance holds for the actual `C`.  Each eventual statement is unfolded at one size index
(`Filter.Eventually.exists`). -/

namespace NQEndLinInst

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.GridGoodNInst RBM.Gauss.Step34Inst
  RBM.Ind.AzumaProxyNInst

/-! ### The data -/

/-- The bulk gap constant `κ' = min κ (4/5)` at `κ = 1`. -/
abbrev κi : ℝ := min 1 (4 / 5)

/-- The constant `C = nqGood1C 3 3 10 κ'` of EK-6 at the data (`Λg = 𝔡⁻¹ = 10`): abstract, positive. -/
abbrev Ci : ℝ := nqGood1C 3 3 10 κi

theorem Ci_pos : 0 < Ci := nqGood1C_pos (by norm_num) (by norm_num) (by norm_num) (lt_min one_pos (by norm_num))

/-- `ε₀' = min ε₀ 1 = 1/10`, `ε = min (ε₀'/(8C)) (1/2)`, `D'' = C + k + 2 + (4k+2)/𝔠` at `k = 3`, `𝔠 = 1/6`. -/
abbrev e0i : ℝ := 1 / 10
abbrev epsi : ℝ := min (e0i / (8 * Ci)) (1 / 2)
abbrev Ddi : ℝ := Ci + ((3 : ℕ) : ℝ) + 2 + (4 * ((3 : ℕ) : ℝ) + 2) / (1 / 6)

private theorem arith_i : NQEndArith 3 (1 / 6) Ci e0i epsi Ddi :=
  nqEnd_arith 3 (by norm_num) (by norm_num) Ci_pos (by norm_num) (by norm_num) rfl rfl

theorem hE_i : ∀ n, |Einst n| ≤ 2 - 1 := fun n => by norm_num [Einst]

theorem hκm_i : ∀ n, κi ≤ (mE (Einst n)).im := fun n =>
  nqGood1_mE_im_ge one_pos (hE_i n)

theorem hlam_i : ∀ᶠ n : ℕ in atTop, 0 < sz0.lam n ∧ sz0.lam n ≤ 10 := by
  filter_upwards [sz0_WO] with n hn
  have hW : (0 : ℝ) < ((sz0.W n : ℕ) : ℝ) := by exact_mod_cast sz0.W_pos n
  exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) hn.1, hn.2.trans (by norm_num)⟩

theorem rangeCond_tInst : sz0.RangeCond (1 / 2) tInst :=
  RBM.Green.rangeCond_mono sz0 GridEnvelopeNCheck.rangeCond_half (fun n => by norm_num [tInst])

theorem rangeCond_vg : sz0.RangeCond (1 / 2) vg :=
  RBM.Green.rangeCond_mono sz0 GridEnvelopeNCheck.rangeCond_half (fun n => by norm_num [vg])

theorem vg_le_tInst : ∀ n, vg n ≤ tInst n := fun n => by norm_num [vg, tInst]

theorem sInst_le_tInst : ∀ n, sInst n ≤ tInst n := fun n => by norm_num [sInst, tInst]

/-- The window hypothesis `W⁻¹ ≤ (1-t)/(1-s) = 15/16` (`W ≥ 32`). -/
theorem WtInst : ∀ᶠ n : ℕ in atTop,
    (((sz0.W n : ℕ) : ℝ))⁻¹ ≤ (1 - tInst n) / (1 - sInst n) := Eventually.of_forall fun n => by
  have h := W_ge_32 n
  have : (((sz0.W n : ℕ) : ℝ))⁻¹ ≤ (32 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h
  refine this.trans ?_
  norm_num [tInst, sInst]

theorem hσ3_i : ∃ i : Fin 3, sig3 i = sig3 (finRotate 3 i) := ⟨2, by decide⟩

/-! ### The grid `KC C_K n = max 1 ⌈N^{C_K}⌉` -/

/-- The grid of the instances: `N^{C_K} ≤ K_n ≤ ⌈N^{C_K}⌉` (RBM2D `KC`, `NonAltEnd:1469`). -/
def KC (C_K : ℝ) (n : ℕ) : ℕ := max 1 ⌈((sz0.size n : ℕ) : ℝ) ^ C_K⌉₊

theorem KC_ne_zero (C_K : ℝ) (n : ℕ) : KC C_K n ≠ 0 := by
  unfold KC
  exact Nat.pos_iff_ne_zero.1 (lt_of_lt_of_le one_pos (le_max_left _ _))

theorem KC_low (C_K : ℝ) (n : ℕ) : ((sz0.size n : ℕ) : ℝ) ^ C_K ≤ (KC C_K n : ℝ) := by
  unfold KC
  have h : ((sz0.size n : ℕ) : ℝ) ^ C_K ≤ (⌈((sz0.size n : ℕ) : ℝ) ^ C_K⌉₊ : ℝ) := Nat.le_ceil _
  exact h.trans (by exact_mod_cast le_max_right _ _)

theorem KC_up (C_K : ℝ) (n : ℕ) : KC C_K n ≤ ⌈((sz0.size n : ℕ) : ℝ) ^ C_K⌉₊ := by
  unfold KC
  have hN : (0 : ℝ) < ((sz0.size n : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (by have := sz0.one_le_size n; omega)
  exact max_le (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hN _)) le_rfl

/-- The window of the instances is not collapsed: `s_n = 0 < 1/32 = v_n`, so the grid step
`Δ = (v_n - s_n)/K_n` is positive on every grid `KC C_K`. -/
theorem window_nondegenerate (C_K : ℝ) (n : ℕ) :
    sInst n < vg n ∧ 0 < gridStep sInst vg (KC C_K) n := by
  refine ⟨by norm_num [sInst, vg], ?_⟩
  have hK : (0 : ℝ) < (KC C_K n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero (KC_ne_zero _ n))
  exact div_pos (by norm_num [vg, sInst]) hK

/-! ### (1) The asymptotic helpers at concrete exponents -/

/-- `7 x^{1/10} ≤ x^{1/5}`, `5 (1 + log x)^3 x^{1/10} ≤ x^{1/5}` and `7 x^{1/10} (log x + 1) ≤ x^{1/5}`
for some real `x` (RBM2D `asymp_instance`, `NonAltEnd:1297`). -/
theorem asymp_instance : (∃ x : ℝ, 7 * x ^ (1 / 10 : ℝ) ≤ x ^ (1 / 5 : ℝ)) ∧
    (∃ x : ℝ, 5 * (1 + Real.log x) ^ 3 * x ^ (1 / 10 : ℝ) ≤ x ^ (1 / 5 : ℝ)) ∧
    (∃ x : ℝ, 7 * x ^ (1 / 10 : ℝ) * (Real.log x + 1) ≤ x ^ (1 / 5 : ℝ)) :=
  ⟨(nqEnd_ev_rpow_le (a := 1 / 10) (b := 1 / 5) (by norm_num) 7).exists,
    (nqEnd_ev_polylog_le 3 (a := 1 / 10) (b := 1 / 5) (by norm_num) 5).exists,
    (nqEnd_ev_rpow_log_le (a := 1 / 10) (b := 1 / 5) (by norm_num) 7).exists⟩

/-! ### (2) The absorption and regime lemmas at the exponents the endpoint chooses at the data

`ε₁ = εq = e0i/8 = 1/80`, `ε = epsi`, `τ' = epsi/2`, `D'' = Ddi`, `D' = Ddi + 1`, `D_Y = D_t = 4`,
`ε₀' = e0i = 1/10`, `Λg = 10`, `κ' = κi`; each statement is unfolded at one size index. -/

theorem union_instance : ∃ n : ℕ, (2 : ℝ) ^ 3 * ((sz0.size n : ℕ) : ℝ) ^ (-((1 : ℝ) + 1)) ≤
    ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) :=
  (nqEnd_ev_union sz0 sz0_tendsto 3 1).exists

theorem rangeCond_mono_instance : sz0.RangeCond (1 / 4) tInst :=
  nqEnd_rangeCond_mono sz0 (τ := 1 / 2) (by norm_num) (fun _ => le_rfl) rangeCond_tInst

/-- (ha1) at the data. -/
theorem ha1_instance : ∃ n : ℕ, ((sz0.W n : ℕ) : ℝ) ^ (Ci * epsi) * ((sz0.size n : ℕ) : ℝ) ^ (e0i / 8) ≤
    ((sz0.size n : ℕ) : ℝ) ^ e0i / 6 :=
  (nqEnd_ev_ha1 sz0 (by norm_num) sz0_tendsto arith_i.hCε0 arith_i.E1).exists

/-- (ha2) at the data. -/
theorem ha2_instance : ∃ n : ℕ, ((3 : ℕ) : ℝ) * ((sz0.W n : ℕ) : ℝ) ^ (Ci * epsi) *
    (((sz0.size n : ℕ) : ℝ) ^ (e0i / 8)) ^ 2 *
      ((mE (Einst n)).im⁻¹ * Real.log ((sz0.size n : ℕ) : ℝ)) ≤ ((sz0.size n : ℕ) : ℝ) ^ e0i / 12 :=
  (nqEnd_ev_ha2 sz0 (by norm_num) sz0_tendsto 3 (lt_min one_pos (by norm_num)) hκm_i arith_i.hCε0
    arith_i.E2).exists

/-- (ha3) at the data. -/
theorem ha3_instance : ∃ n : ℕ, ((sz0.size n : ℕ) : ℝ) ^ (e0i / 8) * (((sz0.W n : ℕ) : ℝ) ^ (Ci * epsi) *
    ((sz0.size n : ℕ) : ℝ) ^ (e0i / 8) * Real.sqrt (((3 : ℕ) : ℝ) * ((mE (Einst n)).im⁻¹ *
      Real.log ((sz0.size n : ℕ) : ℝ) + 1))) ≤ ((sz0.size n : ℕ) : ℝ) ^ e0i / 12 :=
  (nqEnd_ev_ha3 sz0 (by norm_num) sz0_tendsto 3 (lt_min one_pos (by norm_num)) hκm_i arith_i.hCε0
    arith_i.E3).exists

/-- (he1) at the data (`D' = D'' + 1`). -/
theorem he1_instance : ∃ n : ℕ, ((sz0.size n : ℕ) : ℝ) ^ 3 * (((sz0.W n : ℕ) : ℝ) ^ Ci *
    ((sz0.W n : ℕ) : ℝ) ^ (-(Ddi + 1))) ≤ ((sz0.size n : ℕ) : ℝ) ^ e0i / 12 :=
  (nqEnd_ev_he1 sz0 sz0_tendsto sz0_bandwidth (k := 3) arith_i.hCD' arith_i.E4).exists

/-- (he2) at the data. -/
theorem he2_instance : ∃ n : ℕ, ((sz0.size n : ℕ) : ℝ) ^ (e0i / 8) * (((sz0.size n : ℕ) : ℝ) ^ 3 *
    Real.sqrt (((3 : ℕ) : ℝ) * (nqBudget_qvFar sz0 n 3 10 κi epsi * ((sz0.W n : ℕ) : ℝ) ^ (-Ddi)))) ≤
      ((sz0.size n : ℕ) : ℝ) ^ e0i / 12 :=
  (nqEnd_ev_he2 sz0 sz0_tendsto sz0_bandwidth (by norm_num) hlam_i arith_i.F1 arith_i.F2 arith_i.F3
    arith_i.G1 arith_i.G2 arith_i.G3 arith_i.H1).exists

/-- (he3, he4) at the data (`D_Y = D_t = k + 1 = 4`). -/
theorem he34_instance : ∃ n : ℕ, ((sz0.size n : ℕ) : ℝ) ^ 3 * ((sz0.size n : ℕ) : ℝ) ^ (-((3 : ℝ) + 1)) ≤
    ((sz0.size n : ℕ) : ℝ) ^ e0i / 6 :=
  (nqEnd_ev_he4 sz0 sz0_tendsto 3 (D := (3 : ℝ) + 1) arith_i.H2).exists

/-- (`hη`) at the data. -/
theorem hη_instance : ∃ n : ℕ, (etaT (Einst n) (vg n))⁻¹ ≤ ((sz0.size n : ℕ) : ℝ) :=
  (nqEnd_ev_hη sz0 sz0_tendsto (lt_min one_pos (by norm_num)) hκm_i (τR := 1 / 2) (by norm_num)
    rangeCond_vg).exists

/-- (`hδ`, the shift hypothesis) at the data (`C_K = Ddi + 2k + 5`, grid `KC C_K`). -/
theorem hδ_instance : ∃ n : ℕ, ∀ j < KC (Ddi + 2 * ((3 : ℕ) : ℝ) + 5) n,
    ((sz0.W n : ℕ) : ℝ) ^ (-(Ddi + 1)) + eeShiftErrN 3 (sz0.L n) (sz0.W n) (Einst n) 3
      (gridTime sInst vg (KC (Ddi + 2 * ((3 : ℕ) : ℝ) + 5)) n j)
      (gridTime sInst vg (KC (Ddi + 2 * ((3 : ℕ) : ℝ) + 5)) n (j + 1)) ≤ ((sz0.W n : ℕ) : ℝ) ^ (-Ddi) :=
  (nqEnd_ev_hδ sz0 (by norm_num) sz0_tendsto (𝔠 := 1 / 6) (by norm_num) sz0_bandwidth 3
    (E := Einst) (s := sInst) (v := vg) (K := KC (Ddi + 2 * ((3 : ℕ) : ℝ) + 5)) Einst_abs_lt
    sInst_nonneg sInst_le_vg vg_lt_one (KC_ne_zero _)
    (nqEnd_ev_hη sz0 sz0_tendsto (lt_min one_pos (by norm_num)) hκm_i (τR := 1 / 2) (by norm_num)
      rangeCond_vg) arith_i.hD''0 le_rfl (Eventually.of_forall (KC_low _))).exists

/-- (`hΔη`) at the data (`C_K = Ddi + 2k + 5 ≥ 1`): `Δ η_v⁻¹ ≤ 1` at one size index. -/
theorem hΔη_instance : ∃ n : ℕ, gridStep sInst vg (KC (Ddi + 2 * ((3 : ℕ) : ℝ) + 5)) n *
    (etaT (Einst n) (vg n))⁻¹ ≤ 1 := by
  obtain ⟨n, hn⟩ := (nqEnd_ev_hη sz0 sz0_tendsto (lt_min one_pos (by norm_num)) hκm_i (τR := 1 / 2)
    (by norm_num) rangeCond_vg).exists
  refine ⟨n, nqEnd_hΔη sz0 (C_K := Ddi + 2 * ((3 : ℕ) : ℝ) + 5) ?_ (KC_low _ n) ?_
    (inv_nonneg.2 (etaT_pos (Einst_abs_lt n) (vg_lt_one n)).le) hn⟩
  · have := arith_i.hD''0
    push_cast
    linarith
  · norm_num [vg, sInst]

/-! ### (3) The assembly at the exit time at the data

The per-`n` regime facts of the assembly at the data (`ε = 1/2`, `τ' = 1/4`): `W ≥ 32`, `W → ∞`. -/

theorem hwL_i : ∀ n, vg n ≤ 1 - sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 := fun n => by
  have h := sz0_caseI n
  have := vg_le_tInst n
  linarith

theorem hWt_vg : ∀ᶠ n : ℕ in atTop,
    (((sz0.W n : ℕ) : ℝ))⁻¹ ≤ (1 - vg n) / (1 - sInst n) := Eventually.of_forall fun n => by
  have h := W_ge_32 n
  have : (((sz0.W n : ℕ) : ℝ))⁻¹ ≤ (32 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h
  refine this.trans ?_
  norm_num [vg, sInst]

theorem hW1_i : ∀ᶠ n : ℕ in atTop, 1 < ((sz0.W n : ℕ) : ℝ) :=
  Eventually.of_forall fun n => by have := W_ge_32 n; linarith

theorem hWε_i : ∀ᶠ n : ℕ in atTop, 4 ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ) :=
  nqEnd_ev_W_rpow_ge sz0 sz0_tendsto (𝔠 := 1 / 6) (by norm_num) sz0_bandwidth (a := 1 / 2)
    (by norm_num) 4

theorem hdW_i : ∀ᶠ n : ℕ in atTop,
    ((3 : ℕ) : ℝ) * ((sz0.W n : ℕ) : ℝ) ^ (1 / 4 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ) := by
  filter_upwards [nqEnd_ev_W_rpow_ge sz0 sz0_tendsto (𝔠 := 1 / 6) (by norm_num) sz0_bandwidth
    (a := 1 / 4) (by norm_num) ((3 : ℕ) : ℝ)] with n hn
  have hW0 : (0 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  calc ((3 : ℕ) : ℝ) * ((sz0.W n : ℕ) : ℝ) ^ (1 / 4 : ℝ)
      ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 4 : ℝ) * ((sz0.W n : ℕ) : ℝ) ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hW0 _)
    _ = ((sz0.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add' hW0 (by norm_num)]; norm_num

/-- **The assembly at the exit time `nqLinExitTauN`** at the data: `k = 3`, `σ = (+,-,+)`, levels
`(Γ, Λ, Φc, Φ₁, Φ₂, Φ₃) = (4, 3, 1, 1, 12, 1)`, `Λg = 10`, `κ' = κi`, `ε = 1/2`, `τ' = 1/4`, `D'' = 5`,
`D' = 5 + 1`, `D_Y = 4`, `τ_K = 1`, `ε_q = 1/10`, `D₁ = 2`, the `Y`-moment constant `C_P` of
`yMomentsUnifN`, `C_K = 100 + 2 C_P`, the grid `KC C_K`.  At one size index (from the eventual
statement; `STKbound` by `stKbound_holds`, the shift hypothesis `hδ` by `nqEnd_ev_hδ`), on the strict window
`Δ > 0`, there is an event of probability `≥ 1 - N^{-2}` on which the terminal bound
`‖A_K(a)‖ ≤ assembledRHSLinN` holds as soon as the walk stays in `GoodSetN ∩ GoodLinN`
(RBM2D `assembly_instance`, `NonAltEnd:1488`). -/
theorem assembly_instance :
    ∃ C_P : ℝ, 0 ≤ C_P ∧ ∃ n : ℕ, 0 < gridStep sInst vg (KC (100 + 2 * C_P)) n ∧
      ∃ G : Set (PathΩ sz0), (pathP sz0).real Gᶜ ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(2 : ℝ)) ∧
        ∀ ω ∈ G,
          (∀ j ≤ KC (100 + 2 * C_P) n,
            pathH sz0 sInst vg (KC (100 + 2 * C_P)) n j ω ∈
              sz0.GoodSetN n (Einst n) (gridTime sInst vg (KC (100 + 2 * C_P)) n j) 3 (Γ4 n)
                (Λ3 n) (Φ1 n) (1 / 4) (5 + 1) ∩
              GoodLinN sz0 n (Einst n) (gridTime sInst vg (KC (100 + 2 * C_P)) n j) 3 (Γ4 n)
                (Φ1 n) (12 : ℝ) (Φ1 n)) →
          ∀ a : Fin 3 → Zd 3 (sz0.L n),
            ‖AvecN sz0 Einst sInst vg (KC (100 + 2 * C_P)) n (KC (100 + 2 * C_P) n) sig3 ω a‖ ≤
              assembledRHSLinN sz0 Einst sInst vg (KC (100 + 2 * C_P)) n 3 10 κi (1 / 2) Γ4 Λ3 Φ1
                (fun _ => 12) Φ1 (5 + 1) 5 4 1 (1 / 10)
                (Finset.univ.sup' Finset.univ_nonempty fun b =>
                  ‖AvecN sz0 Einst sInst vg (KC (100 + 2 * C_P)) n 0 sig3 ω b‖) a := by
  obtain ⟨C_P, hCP0, hYm⟩ := nqEnd_yMomentsMax sz0 (κ := 1) (τR := 1 / 2) (E := Einst) (s := sInst)
    (v := vg) one_pos hE_i sInst_nonneg sInst_le_vg vg_lt_one sz0_tendsto rangeCond_vg 3
  refine ⟨C_P, hCP0, ?_⟩
  have hKN : ∀ᶠ n : ℕ in atTop, ((sz0.size n : ℕ) : ℝ) ^ (100 + 2 * C_P) ≤
      (KC (100 + 2 * C_P) n : ℝ) := Eventually.of_forall (KC_low _)
  have hKU : ∀ᶠ n : ℕ in atTop, KC (100 + 2 * C_P) n ≤
      ⌈((sz0.size n : ℕ) : ℝ) ^ (100 + 2 * C_P)⌉₊ := Eventually.of_forall (KC_up _)
  have hKb : sz0.STKbound Einst := stKbound_holds sz0 (by norm_num) one_pos
    (by norm_num : (0 : ℝ) < 10) sz0_tendsto (Eventually.of_forall hE_i) hlam_i
  have hη := nqEnd_ev_hη sz0 sz0_tendsto (lt_min one_pos (by norm_num)) hκm_i (τR := 1 / 2)
    (by norm_num) rangeCond_vg
  have hδ := nqEnd_ev_hδ sz0 (by norm_num) sz0_tendsto (𝔠 := 1 / 6) (by norm_num) sz0_bandwidth 3
    (D'' := 5) (C_K := 100 + 2 * C_P) (E := Einst) (s := sInst) (v := vg)
    (K := KC (100 + 2 * C_P)) Einst_abs_lt sInst_nonneg sInst_le_vg vg_lt_one (KC_ne_zero _) hη
    (by norm_num) (by push_cast; linarith) hKN
  have hAsm := nqEndLin_assembly sz0 (κ := 1) (E := Einst) (s := sInst) (v := vg)
    (K := KC (100 + 2 * C_P)) 3 (by norm_num) (by norm_num) one_pos hE_i sInst_nonneg sInst_le_vg
    vg_lt_one (KC_ne_zero _) sz0_tendsto hKb Γ4 Λ3 Φ1 Φ1 (fun _ => 12) Φ1 (fun _ => by norm_num)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
    (Λg := 10) (κ' := κi) (ε := 1 / 2) (τ' := 1 / 4) (D' := 5 + 1) (D'' := 5) (D_Y := 4) (τK := 1)
    (εq := 1 / 10) (D₁ := 2) (C_P := C_P) (C_K := 100 + 2 * C_P) (by norm_num)
    (lt_min one_pos (by norm_num)) hκm_i (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    one_pos (by norm_num) (by linarith) (by push_cast; linarith) hKN hKU
    (hYm _ (KC_ne_zero _)) hwL_i hWt_vg hlam_i hW1_i hWε_i hdW_i hδ
  obtain ⟨n, hn⟩ := hAsm.exists
  exact ⟨n, (window_nondegenerate (100 + 2 * C_P) n).2,
    hn sig3 hσ3_i (window_nondegenerate (100 + 2 * C_P) n).1⟩

/-! ### (4) `nqGridEndLinN` at the data, every premise discharged -/

/-- **`nqGridEndLinN` at the data** (`k ≥ 2` arbitrary, `σ` arbitrary non-alternating; no hypothesis
is left: `STKbound` is internal, the good-walk and initial hypotheses stay in the conclusion).  The
conclusion is unfolded to the eventual event statement at the grid `KC C_K` (`N^{C_K} ≤ K_n ≤ ⌈N^{C_K}⌉`)
for the exponents the theorem produces, at one size index.  Levels `Λ = 3`, `Φ₁ = Φ₃ = Φc = 1`,
`Φ₂ = 12`, `v = vg ≡ 1/32` (`Δ > 0`), `ε₀ = 1/10`, `D₁ = 1` (RBM2D `nonAltEnd_instance`,
`NonAltEnd:1535`). -/
theorem nqEndLin_instance (k : ℕ) (hk : 2 ≤ k) :
    ∃ ε₁ τ' D' C_K : ℝ, 0 < ε₁ ∧ 0 < τ' ∧ 0 < D' ∧ 0 ≤ C_K ∧
      ∃ n : ℕ, ∃ G : Set (PathΩ sz0), (pathP sz0).real Gᶜ ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ∧
        ∀ ω ∈ G,
          (∀ j ≤ KC C_K n, pathH sz0 sInst vg (KC C_K) n j ω ∈
            sz0.GoodSetN n (Einst n) (gridTime sInst vg (KC C_K) n j) k
                (((sz0.size n : ℕ) : ℝ) ^ ε₁) (Λ3 n) (Φ1 n) τ' D' ∩
              GoodLinN sz0 n (Einst n) (gridTime sInst vg (KC C_K) n j) k
                (((sz0.size n : ℕ) : ℝ) ^ ε₁) (Φ1 n) (12 : ℝ) (Φ1 n)) →
          (∀ σ : Fin k → Bool, (∃ i, σ i = σ (finRotate k i)) → ∀ a : Fin k → Zd 3 (sz0.L n),
            ‖sz0.STLKM n (Einst n) (sInst n) (pathH sz0 sInst vg (KC C_K) n 0 ω) σ a‖ ≤
              ((sz0.size n : ℕ) : ℝ) ^ ε₁ * (sz0.Bctl n (sInst n)) ^ k) →
          ∀ σ : Fin k → Bool, (∃ i, σ i = σ (finRotate k i)) → ∀ a : Fin k → Zd 3 (sz0.L n),
            ‖sz0.STLKM n (Einst n) (vg n) (pathH sz0 sInst vg (KC C_K) n (KC C_K n) ω) σ a‖ ≤
              ((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * (Λ3 n ^ ((1 : ℝ) / 2) + Φ1 n + 12 + Φ1 n) *
                (sz0.Bctl n (vg n)) ^ k := by
  obtain ⟨ε₁, τ', D', C_K, h1, h2, h3, h4, hend⟩ := nqGridEndLinN sz0 1 (1 / 6) (1 / 2) (1 / 10)
    Einst sInst tInst (by norm_num) one_pos (by norm_num) (by norm_num) (by norm_num) sz0_tendsto
    sz0_bandwidth sz0_WO hE_i sInst_nonneg sInst_le_tInst tInst_lt_one sz0_caseI rangeCond_tInst
    WtInst k hk Λ3 Φ1 (fun _ => 12) Φ1 (fun _ => by norm_num)
    (Eventually.of_forall fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => by norm_num) vg sInst_le_vg vg_le_tInst (1 / 10) (by norm_num) 1 one_pos
  refine ⟨ε₁, τ', D', C_K, h1, h2, h3, h4, ?_⟩
  obtain ⟨n, G, hG, hGb⟩ := (hend Φ1 (KC C_K) (KC_ne_zero C_K)
    (Eventually.of_forall (KC_low C_K)) (Eventually.of_forall (KC_up C_K))).exists
  exact ⟨n, G, hG, hGb⟩

/-- The instance at `k = 2` (no `l ∈ [3,k]`; the sign vectors `σ` of length `2` with `σ_0 = σ_1`). -/
example := nqEndLin_instance 2 le_rfl

/-- The instance at `k = 3`. -/
example := nqEndLin_instance 3 (by norm_num)

/-- The instance at `k = 4`. -/
example := nqEndLin_instance 4 (by norm_num)

end NQEndLinInst

end RBM.Ind

end
