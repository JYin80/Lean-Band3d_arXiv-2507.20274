/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.QtNonzero
import RBM3D.Induction.NQLin
import RBM3D.Induction.NQBudget
import RBM3D.Induction.GridEnvelopeN
import RBM3D.Induction.AzumaProxyN2
import RBM3D.Loop.KLFinal
import RBM3D.Induction.Step34Pins

/-!
# The case-(ii) grid endpoint of the zero-mode-removed loops (`d ≥ 3`): `nzGridEndN`

Ticket T2284 (S3-22a, stochastic layer ST-3, case (ii) `1 − s ≤ ilambda²/L²`; S3-21 =
`Induction/QtNonzero`).  Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex`
(`3_5:line`): `def;zero_mode_remove` (`:1444`), `lem: newPQ` (`:1482`), `(iisuwjyys)` (`:1545`),
`lem:STOeq_Qt_nonzero` (`:1561`), `lem:sum_decay_nonzero` (`:1666`), the proof `:1889-1928`.
No RBM1D/RBM2D source for the statement (the zero-mode regime does not exist for `d ≤ 2`);
the proof follows the format model `nqGridEndLinN` (`Induction/NQEndLin.lean:1067`).

## What is here (namespace `RBM.Ind`)

* §0 asymptotic helpers `C (1 + log x)^j x^a ≤ x^b` (private copies of `NQEndLin`);
* §1 facts on the sizes;
* §2 the absorption lemmas H1-H6 of `budgetNZN` (`QtNonzero.lean:872`);
* §3 the regime facts (`hη`, the grid step, the shift hypothesis `hδ`, the range condition, the
  collapsed window, the `4^k` union bound, the `Y`-moment constant);
* §4 the assembly per pair `(σ, A)`, `A ⊇ I_diff(σ)`, at the merged exit time `nqLinExitTauN`
  (`nzEnd_assembly`, private: its binder mentions `YMomentBoundsN`);
* §5 **`nzGridEndN`** with exactly the statement `T2284_nzGridEndN` of
  `docs/tickets/checks/T2284-check.lean`: kernel class "fixed points of `Q^{(A)}`" with `κ ≡ C`,
  `εK ≡ 0` (loss-free EK-5), `GoodSetN` at a free crude level `Φc` (only its `STeeM` clause is
  used), `GoodLinN` at the levels `Φ₁ Φ₂ Φ₃`, right side `N^{ε₀}(Λ^{1/2} + Φ₁ + Φ₂ + Φ₃) B_v^k`
  (degree 1 in the levels, no `Φ²`, no `Φc`); no `STKbound` premise (`stKbound_holds`); no
  `W⁻¹ ≤ (1−t)/(1−s)` window (EK-5 has none);
* §6 compiled nonempty instances at `d = 3` (namespace `RBM.Ind.QtNonzeroEndInst`).

The good-event probability and the initial event are S3-22b's (as in case (i): T2199 → T2246);
no conclusion pin is proved here.  Every helper that the ticket does not pin is `private` or
prefixed `nzEnd_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-! ## 0. Asymptotic helpers (copies of `NQEndLin.lean:57-117`) -/

section Asymp

/-- `C · x^a ≤ x^b` for all large real `x` when `a < b`. -/
private theorem nzEnd_ev_rpow_le {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, C * x ^ a ≤ x ^ b := by
  have ht : Tendsto (fun x : ℝ => x ^ (b - a)) atTop atTop := tendsto_rpow_atTop (sub_pos.mpr hab)
  filter_upwards [ht.eventually_ge_atTop C, eventually_gt_atTop 0] with x hx hx0
  have h1 : x ^ b = x ^ (b - a) * x ^ a := by
    rw [← Real.rpow_add hx0]; ring_nf
  rw [h1]
  exact mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hx0.le _)

/-- `C · x^a (log x + 1) ≤ x^b` for all large real `x` when `a < b`. -/
private theorem nzEnd_ev_rpow_log_le {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, C * x ^ a * (Real.log x + 1) ≤ x ^ b := by
  set δ := (b - a) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  filter_upwards [nzEnd_ev_rpow_le (a := a + δ) (b := b) (by rw [hδ]; linarith)
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

/-- **Polylog absorption**: `C (1 + log x)^j x^a ≤ x^b` for all large real `x` when `a < b`. -/
private theorem nzEnd_ev_polylog_le (j : ℕ) :
    ∀ {a b : ℝ}, a < b → ∀ C : ℝ, ∀ᶠ x : ℝ in atTop, C * (1 + Real.log x) ^ j * x ^ a ≤ x ^ b := by
  induction j with
  | zero =>
    intro a b hab C
    filter_upwards [nzEnd_ev_rpow_le hab C] with x hx
    simpa using hx
  | succ j ih =>
    intro a b hab C
    set m := (a + b) / 2 with hm
    have ham : a < m := by rw [hm]; linarith
    have hmb : m < b := by rw [hm]; linarith
    filter_upwards [nzEnd_ev_rpow_log_le ham (max C 0), ih hmb 1, eventually_ge_atTop 1] with
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

private theorem nzEnd_one_le_size (n : ℕ) : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  exact_mod_cast sz.one_le_size n

/-- `W^d L^d = N`. -/
private theorem nzEnd_size_cast (n : ℕ) :
    (sz.W n : ℝ) ^ d * (sz.L n : ℝ) ^ d = ((sz.size n : ℕ) : ℝ) := by
  have : ((sz.size n : ℕ) : ℝ) = (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) := rfl
  rw [this]
  push_cast
  ring

/-- **Crude `W ≤ N`** (`W ≤ W^d ≤ (W L)^d = N`, `d ≥ 1`): the bound for the positive powers of `W`. -/
private theorem nzEnd_W_le_size (hd : 1 ≤ d) (n : ℕ) :
    ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  have h1 : sz.W n ≤ (sz.W n) ^ d := Nat.le_self_pow (by omega) _
  have h2 : (sz.W n) ^ d ≤ sz.size n := by
    unfold Sizes.size
    exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by have := sz.three_le_L n; omega)) d
  exact_mod_cast h1.trans h2

end Facts

/-- `W^e ≤ N^{𝔠 e}` for `e ≤ 0` from `N^𝔠 ≤ W` (the negative powers of `W`). -/
private theorem nzEnd_Wpow_le {W N c e : ℝ} (hN0 : 0 < N) (hcW : N ^ c ≤ W) (he : e ≤ 0) :
    W ^ e ≤ N ^ (c * e) := by
  have h1 : 0 < N ^ c := Real.rpow_pos_of_pos hN0 _
  have h := Real.rpow_le_rpow_of_nonpos h1 hcW he
  rwa [← Real.rpow_mul hN0.le] at h

/-! ## 2. The absorption lemmas H1-H6 of `budgetNZN` (`QtNonzero.lean:872`)

Each is stated for abstract exponents in the exact form of the corresponding hypothesis of `budgetNZN`,
eventually in `n`.  Positive powers of `W` do not occur; the one negative power (H4) is bounded by
`W ≥ N^𝔠` (`Bandwidth`); the polylogarithm of `Ls = (Im m)⁻¹ log N ≤ κ'⁻¹ log N` is absorbed by
`nzEnd_ev_polylog_le`. -/

section Absorb

variable {d : ℕ} (sz : Sizes d)

/-- (H1) `C N^{ε₁} ≤ N^{ε₀}/6` when `ε₁ < ε₀`. -/
private theorem nzEnd_ev_H1 (hsize : sz.SizeTendsto) {C ε₁ ε₀ : ℝ} (hε : ε₁ < ε₀) :
    ∀ᶠ n : ℕ in atTop, C * ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 := by
  filter_upwards [hsize.eventually (nzEnd_ev_rpow_le hε (6 * C))] with n h
  linarith

/-- (H2) `C cA k (N^{ε₁})² Ls ≤ N^{ε₀}/6` when `2ε₁ < ε₀`, `Ls = (Im m)⁻¹ log N` (the polylog `log N` is
absorbed). -/
private theorem nzEnd_ev_H2 (hsize : sz.SizeTendsto) (k : ℕ) {κ' : ℝ} (hκ' : 0 < κ')
    {E : ℕ → ℝ} (hκm : ∀ n, κ' ≤ (mE (E n)).im) {C cA ε₁ ε₀ : ℝ} (hC : 0 ≤ C) (hcA : 0 ≤ cA)
    (hε : 2 * ε₁ < ε₀) :
    ∀ᶠ n : ℕ in atTop, C * cA * (k : ℝ) * (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 2 *
        ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 := by
  set M : ℝ := C * cA * (k : ℝ) with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  filter_upwards [hsize.eventually (nzEnd_ev_polylog_le 1 hε (6 * (M * κ'⁻¹))),
    hsize.eventually_ge_atTop 1] with n h hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hIm : ((mE (E n)).im)⁻¹ ≤ κ'⁻¹ := inv_anti₀ hκ' (hκm n)
  have hsq : (N ^ ε₁) ^ 2 = N ^ (2 * ε₁) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; push_cast; ring_nf
  have hLs : (mE (E n)).im⁻¹ * Real.log N ≤ κ'⁻¹ * Real.log N :=
    mul_le_mul_of_nonneg_right hIm hlog0
  have hLs0 : 0 ≤ (mE (E n)).im⁻¹ * Real.log N := by
    have : 0 < (mE (E n)).im := lt_of_lt_of_le hκ' (hκm n)
    positivity
  have hN2 : 0 ≤ N ^ (2 * ε₁) := Real.rpow_nonneg hN0.le _
  calc C * cA * (k : ℝ) * (N ^ ε₁) ^ 2 * ((mE (E n)).im⁻¹ * Real.log N)
      = M * N ^ (2 * ε₁) * ((mE (E n)).im⁻¹ * Real.log N) := by rw [hsq]
    _ ≤ M * N ^ (2 * ε₁) * (κ'⁻¹ * Real.log N) :=
        mul_le_mul_of_nonneg_left hLs (by positivity)
    _ = (M * κ'⁻¹) * Real.log N * N ^ (2 * ε₁) := by ring
    _ ≤ (M * κ'⁻¹) * (1 + Real.log N) * N ^ (2 * ε₁) := by
        have : 0 ≤ (M * κ'⁻¹) * N ^ (2 * ε₁) := by positivity
        nlinarith
    _ ≤ N ^ ε₀ / 6 := by
        have h' : 6 * (M * κ'⁻¹) * (1 + Real.log N) ^ 1 * N ^ (2 * ε₁) ≤ N ^ ε₀ := h
        rw [pow_one] at h'
        linarith

/-- (H3) `N^{εq} (C N^{ε₁} √(k Ls)) ≤ N^{ε₀}/12` when `εq + ε₁ < ε₀` (`√z ≤ z + 1`, the polylog is
absorbed). -/
private theorem nzEnd_ev_H3 (hsize : sz.SizeTendsto) (k : ℕ) {κ' : ℝ} (hκ' : 0 < κ')
    {E : ℕ → ℝ} (hκm : ∀ n, κ' ≤ (mE (E n)).im) {C εq ε₁ ε₀ : ℝ} (hC : 0 ≤ C)
    (hε : εq + ε₁ < ε₀) :
    ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ εq * (C * ((sz.size n : ℕ) : ℝ) ^ ε₁ *
        Real.sqrt ((k : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)))) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 := by
  filter_upwards [hsize.eventually (nzEnd_ev_polylog_le 1 hε
    (12 * (C * ((k : ℝ) * κ'⁻¹ + 1)))), hsize.eventually_ge_atTop 1] with n h hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have him0 : 0 < (mE (E n)).im := lt_of_lt_of_le hκ' (hκm n)
  have hIm : ((mE (E n)).im)⁻¹ ≤ κ'⁻¹ := inv_anti₀ hκ' (hκm n)
  have hLs : (mE (E n)).im⁻¹ * Real.log N ≤ κ'⁻¹ * Real.log N :=
    mul_le_mul_of_nonneg_right hIm hlog0
  have hLs0 : 0 ≤ (mE (E n)).im⁻¹ * Real.log N := by positivity
  set Z : ℝ := (k : ℝ) * ((mE (E n)).im⁻¹ * Real.log N) with hZ
  have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
  have hsq : Real.sqrt Z ≤ Z + 1 := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hZle : Z + 1 ≤ ((k : ℝ) * κ'⁻¹ + 1) * (1 + Real.log N) := by
    have h1 : (k : ℝ) * ((mE (E n)).im⁻¹ * Real.log N) ≤ (k : ℝ) * (κ'⁻¹ * Real.log N) :=
      mul_le_mul_of_nonneg_left hLs hk0
    have h2 : 0 ≤ (k : ℝ) * κ'⁻¹ := by positivity
    have h3 : 0 ≤ Real.log N := hlog0
    rw [hZ]
    nlinarith
  have hrp : N ^ (εq + ε₁) = N ^ εq * N ^ ε₁ := Real.rpow_add hN0 _ _
  have hNe : 0 ≤ N ^ εq := Real.rpow_nonneg hN0.le _
  have hN1' : 0 ≤ N ^ ε₁ := Real.rpow_nonneg hN0.le _
  calc N ^ εq * (C * N ^ ε₁ * Real.sqrt Z)
      ≤ N ^ εq * (C * N ^ ε₁ * (((k : ℝ) * κ'⁻¹ + 1) * (1 + Real.log N))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hsq.trans hZle)
          (by positivity)) hNe
    _ = (C * ((k : ℝ) * κ'⁻¹ + 1)) * (1 + Real.log N) * N ^ (εq + ε₁) := by rw [hrp]; ring
    _ ≤ N ^ ε₀ / 12 := by
        have h' : 12 * (C * ((k : ℝ) * κ'⁻¹ + 1)) * (1 + Real.log N) ^ 1 * N ^ (εq + ε₁) ≤
            N ^ ε₀ := h
        rw [pow_one] at h'
        linarith

/-- (H4) `N^{εq} (N^k (C √(k W^{-D''}))) ≤ N^{ε₀}/12` when `εq + k − 𝔠 D''/2 < ε₀`
(`W^{-D''} ≤ N^{-𝔠 D''}`, `W ≥ N^𝔠`). -/
private theorem nzEnd_ev_H4 (hsize : sz.SizeTendsto) {𝔠 : ℝ} (hband : sz.Bandwidth 𝔠) (k : ℕ)
    {C D'' εq ε₀ : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D'') (hε : εq + (k : ℝ) - 𝔠 * D'' / 2 < ε₀) :
    ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.size n : ℕ) : ℝ) ^ k *
        (C * Real.sqrt ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D'')))) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 := by
  filter_upwards [hband, hsize.eventually (nzEnd_ev_rpow_le hε (12 * (C * Real.sqrt (k : ℝ)))),
    hsize.eventually_ge_atTop 1] with n hW h hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hle : ((sz.W n : ℕ) : ℝ) ^ (-D'') ≤ N ^ (𝔠 * (-D'')) :=
    nzEnd_Wpow_le hN0 hW (by linarith)
  have hsN : Real.sqrt (N ^ (𝔠 * (-D''))) = N ^ (𝔠 * (-D'') / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]; ring_nf
  have hs : Real.sqrt ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D'')) ≤
      Real.sqrt (k : ℝ) * N ^ (𝔠 * (-D'') / 2) := by
    calc Real.sqrt ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D''))
        ≤ Real.sqrt ((k : ℝ) * N ^ (𝔠 * (-D''))) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hle hk0)
      _ = Real.sqrt (k : ℝ) * Real.sqrt (N ^ (𝔠 * (-D''))) := Real.sqrt_mul hk0 _
      _ = _ := by rw [hsN]
  have hk : N ^ k = N ^ (k : ℝ) := (Real.rpow_natCast _ _).symm
  have hNe : 0 ≤ N ^ εq := Real.rpow_nonneg hN0.le _
  have hNk : 0 ≤ N ^ k := by positivity
  have hrp : N ^ (εq + (k : ℝ) - 𝔠 * D'' / 2) =
      N ^ εq * N ^ (k : ℝ) * N ^ (𝔠 * (-D'') / 2) := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; congr 1; ring
  calc N ^ εq * (N ^ k * (C * Real.sqrt ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D''))))
      ≤ N ^ εq * (N ^ k * (C * (Real.sqrt (k : ℝ) * N ^ (𝔠 * (-D'') / 2)))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hs hC) hNk) hNe
    _ = (C * Real.sqrt (k : ℝ)) * N ^ (εq + (k : ℝ) - 𝔠 * D'' / 2) := by
        rw [hrp, hk]; ring
    _ ≤ N ^ ε₀ / 12 := by linarith

/-- (H5, H6) `c N^k N^{-D} ≤ N^{ε₀}/6` when `k - D < ε₀` (H5: `c = 1`, `D = D_Y`; H6: `c = cA`,
`D = D_t`). -/
private theorem nzEnd_ev_H56 (hsize : sz.SizeTendsto) (k : ℕ) (c : ℝ) {D ε₀ : ℝ}
    (hε : (k : ℝ) - D < ε₀) :
    ∀ᶠ n : ℕ in atTop, c * ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-D) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 := by
  filter_upwards [hsize.eventually (nzEnd_ev_rpow_le hε (6 * c)),
    hsize.eventually_ge_atTop 1] with n h hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have e : c * ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-D) =
      c * ((sz.size n : ℕ) : ℝ) ^ ((k : ℝ) - D) := by
    rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hN0, sub_eq_add_neg]
  rw [e]
  linarith

end Absorb

/-! ## 3. The regime facts: `W → ∞`, the grid step, `hη`, the shift hypothesis `hδ`, the range condition

Copies of the private helpers of `NQEndLin` (`NQEndLin.lean:446-646`, `:722-759`, `:965-1044`), with the prefix
`nzEnd_`; the only changes are the collapsed-window lemma (stated for the projected loops) and the union bound
(over `4^k` pairs `(σ, A)`). -/

section Regime

variable {d : ℕ} (sz : Sizes d)

/-- `X ≤ W^a` eventually for `a > 0` (`W ≥ N^𝔠 → ∞`): the source of `1 < W`, `4 ≤ W^ε`,
`d W^{τ'} ≤ W^ε`, `2 ≤ W`. -/
private theorem nzEnd_ev_W_rpow_ge (hsize : sz.SizeTendsto) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠)
    (hband : sz.Bandwidth 𝔠) {a : ℝ} (ha : 0 < a) (X : ℝ) :
    ∀ᶠ n : ℕ in atTop, X ≤ ((sz.W n : ℕ) : ℝ) ^ a := by
  have ht : Tendsto (fun x : ℝ => x ^ (𝔠 * a)) atTop atTop := tendsto_rpow_atTop (mul_pos h𝔠 ha)
  filter_upwards [hband, hsize.eventually (ht.eventually_ge_atTop X),
    hsize.eventually_ge_atTop 1] with n hW hX hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  calc X ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * a) := hX
    _ = (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ a := Real.rpow_mul hN0.le _ _
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ a := Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hW ha.le

/-- `Δ ≤ N^{-C_K}` on a grid with `N^{C_K} ≤ K n` and `v - s ≤ 1` (copy of `nqEnd_step_le`,
`NQEndLin.lean:459`). -/
private theorem nzEnd_step_le {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {C_K : ℝ}
    (hK : ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) (hvs : v n - s n ≤ 1) :
    gridStep s v K n ≤ ((sz.size n : ℕ) : ℝ) ^ (-C_K) := by
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := lt_of_lt_of_le one_pos (nzEnd_one_le_size sz n)
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
private theorem nzEnd_K_mul_step {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hK : K n ≠ 0)
    (hvs : v n - s n ≤ 1) : (K n : ℝ) * gridStep s v K n ≤ 1 := by
  have hK' : (K n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK
  unfold gridStep
  rw [mul_div_cancel₀ _ hK']
  exact hvs

/-- The one-step increment of the grid times is `Δ`. -/
private theorem nzEnd_gridTime_succ_sub (s v : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) :
    gridTime s v K n (j + 1) - gridTime s v K n j = gridStep s v K n := by
  unfold gridTime; push_cast; ring

/-- `η_u⁻¹ ≤ N^{1-τ}/κ'` for `u ≤ t`, `κ' ≤ Im m`, under the range condition
`N^{-1+τ} ≤ 1 - t` (copy of `nqEnd_etaT_inv_le`, `NQEndLin.lean:488`). -/
private theorem nzEnd_etaT_inv_le {κ' E u t τR N : ℝ} (hκ' : 0 < κ') (hκm : κ' ≤ (mE E).im)
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
(copy of `nqEnd_ev_hη`, `NQEndLin.lean:503`). -/
private theorem nzEnd_ev_hη (hsize : sz.SizeTendsto) {κ' τR : ℝ} (hκ' : 0 < κ') {E v : ℕ → ℝ}
    (hκm : ∀ n, κ' ≤ (mE (E n)).im) (hτR : 0 < τR) (hrange : sz.RangeCond τR v) :
    ∀ᶠ n : ℕ in atTop, (etaT (E n) (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
  filter_upwards [hrange, hsize.eventually (nzEnd_ev_rpow_le (a := 0) hτR κ'⁻¹),
    hsize.eventually_ge_atTop 1] with n hR hbig hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have h := nzEnd_etaT_inv_le hκ' (hκm n) le_rfl hN0 hR
  rw [Real.rpow_zero, mul_one] at hbig
  calc (etaT (E n) (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (1 - τR) / κ' := h
    _ = ((sz.size n : ℕ) : ℝ) ^ (1 - τR) * κ'⁻¹ := div_eq_mul_inv _ _
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (1 - τR) * ((sz.size n : ℕ) : ℝ) ^ τR :=
        mul_le_mul_of_nonneg_left hbig (Real.rpow_nonneg hN0.le _)
    _ = ((sz.size n : ℕ) : ℝ) := by rw [← Real.rpow_add hN0]; simp

/-- The shift error with `η_{u'}⁻¹ ≤ B`: `eeShiftErrN ≤ W^d k L^d (2k+2) B^{2k+3} (u' - u)`
(copy of `nqEnd_eeShiftErrN_le`, `NQEndLin.lean:533`). -/
private theorem nzEnd_eeShiftErrN_le {d L W : ℕ} (hW : 1 ≤ W) {E : ℝ} (k : ℕ) {u u' B : ℝ}
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
`C_K ≥ D'' + 2k + 5`, `W ≥ 2`, `N ≥ 2k(2k+2)`, `N^{-D''} ≤ W^{-D''}` (copy of `nqEnd_ev_hδ`,
`NQEndLin.lean:558`). -/
private theorem nzEnd_ev_hδ (hd : 1 ≤ d) (hsize : sz.SizeTendsto) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠)
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
  filter_upwards [hη, hKN, nzEnd_ev_W_rpow_ge sz hsize h𝔠 hband one_pos 2,
    hsize.eventually_ge_atTop (2 * A), hsize.eventually_ge_atTop 1] with n hηn hKNn hW2 hNA hN1
  intro j hj
  rw [Real.rpow_one] at hW2
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hWN : ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := nzEnd_W_le_size sz hd n
  have hvs : v n - s n ≤ 1 := by linarith [hv1 n, hs0 n]
  have hΔ : gridStep s v K n ≤ ((sz.size n : ℕ) : ℝ) ^ (-C_K) := nzEnd_step_le sz hKNn hvs
  have hΔ0 : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n (hsv n)
  have hu'v : gridTime s v K n (j + 1) ≤ v n := by
    have h := ST_gridTime_mono s v K n (hsv n) (show j + 1 ≤ K n by omega)
    rwa [gridTime_last s v K n (hK0 n)] at h
  have hdiff := nzEnd_gridTime_succ_sub s v K n j
  have hEn := hE n
  have hηv : 0 < etaT (E n) (v n) := etaT_pos hEn (hv1 n)
  have hη' : 0 < etaT (E n) (gridTime s v K n (j + 1)) := etaT_pos hEn (hu'v.trans_lt (hv1 n))
  have hηle : (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
    refine le_trans (inv_anti₀ hηv ?_) hηn
    unfold etaT
    exact mul_le_mul_of_nonneg_right (by linarith) (mE_im_pos hEn).le
  have hη0 : 0 ≤ (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ := inv_nonneg.2 hη'.le
  have hee := nzEnd_eeShiftErrN_le (d := d) (L := sz.L n) (W := sz.W n) (sz.W_pos n) k
    (E := E n) (u := gridTime s v K n j) (u' := gridTime s v K n (j + 1)) hη0 hηle
    (by rw [hdiff]; exact hΔ0)
  rw [hdiff] at hee
  have hsz := nzEnd_size_cast sz n
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
/-! ## 3b. Grid times, the step error, the collapsed window, the range condition, the `Y`-moment constant -/

section Grid

variable {d : ℕ} (sz : Sizes d)

/-- `0 ≤ u_i` on the grid `0 ≤ s_n ≤ v_n`. -/
private theorem nzEnd_gridTime_nonneg {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hs0 : 0 ≤ s n)
    (hsv : s n ≤ v n) (i : ℕ) : 0 ≤ gridTime s v K n i := by
  have h := ST_gridTime_mono s v K n hsv (Nat.zero_le i)
  rw [ST_gridTime_zero] at h
  linarith

/-- `u_i ≤ v_n` for `i ≤ K_n`, `K_n ≠ 0`. -/
private theorem nzEnd_gridTime_le {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hsv : s n ≤ v n)
    (hK : K n ≠ 0) {i : ℕ} (hi : i ≤ K n) : gridTime s v K n i ≤ v n :=
  (ST_gridTime_mono s v K n hsv hi).trans_eq (gridTime_last s v K n hK)

/-- The step error of `gridDriftN` is nonnegative (copy of `nqEnd_stepErrN_nonneg`,
`NQEndLin.lean:736`). -/
private theorem nzEnd_stepErrN_nonneg {d L W : ℕ} {E u v Δ Bk : ℝ} {k : ℕ} (hE : |E| < 2)
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

/-- If `v_n = s_n` the grid walk does not move: `Δ = 0` and every `H_j = H_0` (copy of
`nqEnd_pathH_collapse`, `NQEndLin.lean:967`). -/
private theorem nzEnd_pathH_collapse {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hsv : s n = v n) (j : ℕ)
    (ω : PathΩ sz) : pathH sz s v K n j ω = pathH sz s v K n 0 ω := by
  have hΔ : gridStep s v K n = 0 := by unfold gridStep; rw [← hsv]; simp
  unfold pathH
  rw [hΔ]
  simp

/-- **The collapsed window** (the case `v_n = s_n` of the endpoint, where `hc_pos` of the assembly fails):
`H_K = H_0` and `u_K = s`, so the projected initial bound
`‖(Q^{(A)}(𝓛-𝒦)_s)(a)‖ ≤ N^{ε₁} B_s^k` with `ε₁ ≤ ε₀`, `N ≥ 1`, `Λ ≥ 1`, `Φ_i ≥ 0` and `B_s^k ≥ 0` is the
conclusion `‖(Q^{(A)}(𝓛-𝒦)_v)(a)‖ ≤ N^{ε₀} (Λ^{1/2} + Φ₁ + Φ₂ + Φ₃) B_v^k` (copy of `nzEnd_collapse`,
`NQEndLin.lean:974`, for the projected loops). -/
private theorem nzEnd_collapse {E s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hv1 : v n < 1)
    (hsv : s n = v n) {k : ℕ} {ε₁ ε₀ Λ Φ₁ Φ₂ Φ₃ : ℝ} (hε : ε₁ ≤ ε₀) (hΛ : 1 ≤ Λ) (hΦ₁ : 0 ≤ Φ₁)
    (hΦ₂ : 0 ≤ Φ₂) (hΦ₃ : 0 ≤ Φ₃) (ω : PathΩ sz) (σ : Fin k → Bool) (A : Finset (Fin k))
    (a : Fin k → Zd d (sz.L n))
    (hinit : ‖zeroModeSet d (sz.L n) A
      (fun b : Fin k → Zd d (sz.L n) => sz.STLKM n (E n) (s n) (pathH sz s v K n 0 ω) σ b) a‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ k) :
    ‖zeroModeSet d (sz.L n) A
        (fun b : Fin k → Zd d (sz.L n) => sz.STLKM n (E n) (v n) (pathH sz s v K n (K n) ω) σ b) a‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ ^ ((1 : ℝ) / 2) + Φ₁ + Φ₂ + Φ₃) * (sz.Bctl n (v n)) ^ k := by
  rw [nzEnd_pathH_collapse sz hsv (K n) ω, ← hsv]
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := nzEnd_one_le_size sz n
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

/-- The range condition passes to a smaller exponent and an earlier time (copy of
`nqEnd_rangeCond_mono`, `NQEndLin.lean:1001`). -/
private theorem nzEnd_rangeCond_mono {τ τR : ℝ} {t v : ℕ → ℝ} (hτ : τR ≤ τ)
    (hvt : ∀ n, v n ≤ t n) (h : sz.RangeCond τ t) : sz.RangeCond τR v := by
  filter_upwards [h] with n hn
  calc ((sz.size n : ℕ) : ℝ) ^ (-1 + τR) ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 + τ) :=
        Real.rpow_le_rpow_of_exponent_le (nzEnd_one_le_size sz n) (by linarith)
    _ ≤ 1 - t n := hn
    _ ≤ 1 - v n := by linarith [hvt n]

/-- The union bound over the pairs `(σ, A)`: `c N^{-(D+1)} ≤ N^{-D}` eventually, for any constant `c`
(here `c = 4^k`; copy of `nzEnd_ev_union`, `NQEndLin.lean:1011`, with the constant a parameter). -/
private theorem nzEnd_ev_union (hsize : sz.SizeTendsto) (c D : ℝ) :
    ∀ᶠ n : ℕ in atTop, c * ((sz.size n : ℕ) : ℝ) ^ (-(D + 1)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-D) := by
  filter_upwards [hsize.eventually_ge_atTop c, hsize.eventually_ge_atTop 1] with n hn hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  rw [show (-(D + 1)) = -D + -1 by ring, Real.rpow_add hN0, Real.rpow_neg_one]
  have h := Real.rpow_nonneg hN0.le (-D)
  calc c * (((sz.size n : ℕ) : ℝ) ^ (-D) * ((sz.size n : ℕ) : ℝ)⁻¹)
      = ((sz.size n : ℕ) : ℝ) ^ (-D) * (c / ((sz.size n : ℕ) : ℝ)) := by ring
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ h
        rw [div_le_one hN0]; exact hn
    _ = _ := mul_one _

/-- **The uniform `Y` moments for all signs with one `C_P`** (before the grid `K`): the maximum over the
`2^k` sign vectors of the constants of `yMomentsUnifN` serves every sign (`N ≥ 1`; copy of
`nqEnd_yMomentsMax`, `NQEndLin.lean:1028`). -/
private theorem nzEnd_yMomentsMax {κ τR : ℝ} {E s v : ℕ → ℝ} (hκ : 0 < κ)
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
  exact ⟨P, hP0, hPle.trans (Real.rpow_le_rpow_of_exponent_le (nzEnd_one_le_size sz n)
    (Finset.le_sup' CP (Finset.mem_univ σ))), hτ⟩

end Grid

/-! ## 4. The assembly at the exit time `nqLinExitTauN` for one pair `(σ, A)`, `A ⊇ I_diff(σ)`

The merged `assembledN` (`GridAssemblyN.lean:1605`) at the exit time `nqLinExitTauN` of the walk from
`GoodSetN ∩ GoodLinN` (`NQLin.lean:716`), for the zero-mode-removed evolution: the kernel class is "fixed
points of `Q^{(A)}`" with `κ ≡ C`, `εK ≡ 0` (`nz_hker`, loss-free EK-5); every tensor is pushed through
`Q^{(A)}` (drift `nz_hdriftN`, Azuma `subGaussStop_nzN`, moments `yMomentBounds_nzN`, step error by
`(normQA2)` = `norm_zeroModeSet_le`); `A_{j∧τ} := 𝒰 Q^{(A)}A_0 + Σ 𝒰 (Δ Dr + Z + Y + R)` is defined by its
formula (`hexp` is `rfl`) and equals `Q^{(A)}A_K` on the good walk by `zeroModeCalc_duhamel_inside_at`.
`GoodSetN` is used through its `STeeM` clause only (inside `subGaussStop_nzN`): the crude level `Φ` never
enters the bound. -/

section Assembly

variable {d : ℕ} (sz : Sizes d)

/-- **The assembly at the exit time, for one pair `(σ, A)`** (the merged `assembledN` at
`τ = nqLinExitTauN`, the data of `QtNonzero`).  `hCop` is the conclusion of `nzUgen_holds` at `(d, k, Λg, κ')`
(operator bound and row sums of `Q^{(A)} ∘ 𝒰` with the constant `C`).  Eventually in `n`, for every `σ`, every
`A ⊇ I_diff(σ)`, on a strict window `s_n < v_n`, there is an event `G`, `P(Gᶜ) ≤ N^{-D₁}`, on which the terminal
bound `‖(Q^{(A)} A_K)(a)‖ ≤ assembledRHSNZN` holds as soon as the grid walk stays in `GoodSetN ∩ GoodLinN`.
Private: its binder `hY` mentions `YMomentBoundsN`. -/
private theorem nzEnd_assembly {κ : ℝ} {E s v : ℕ → ℝ} {K : ℕ → ℕ} (k : ℕ)
    (hk : 2 ≤ k) (hκ : 0 < κ) (hE : ∀ n, |E n| ≤ 2 - κ) (hs0 : ∀ n, 0 ≤ s n)
    (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1) (hK0 : ∀ n, K n ≠ 0) (hsize : sz.SizeTendsto)
    (hKb : sz.STKbound E) (hcase : ∀ n, 1 - s n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (Γ Λ Φ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (hΓ : ∀ n, 0 ≤ Γ n) (hΛ : ∀ n, 0 ≤ Λ n)
    (hΦ₁ : ∀ n, 0 ≤ Φ₁ n) (hΦ₂ : ∀ n, 0 ≤ Φ₂ n) (hΦ₃ : ∀ n, 0 ≤ Φ₃ n)
    {Λg κ' C τ' D' D'' D_Y τK εq D₁ C_P C_K : ℝ} (hκ' : 0 < κ')
    (hκm : ∀ n, κ' ≤ (mE (E n)).im) (hC : 0 < C)
    (hCop : ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g E : ℝ, 0 < g → g ≤ Λg → |E| < 2 → κ' ≤ (mE E).im →
      ∀ v w : ℝ, 0 ≤ v → 1 - g ^ 2 / (L : ℝ) ^ 2 ≤ v → v ≤ w → w < 1 →
      ∀ (σ : Fin k → Bool) (A : Finset (Fin k)), STIdiff σ ⊆ A →
        (∀ X : (Fin k → Zd d L) → ℂ, ‖zeroModeSet d L A (Ugen d L g E σ v w X)‖ ≤ C * ‖X‖) ∧
        ∀ a : Fin k → Zd d L, ∃ κ : (Fin k → Zd d L) → ℂ,
          (∀ X : (Fin k → Zd d L) → ℂ,
            zeroModeSet d L A (Ugen d L g E σ v w X) a = ∑ b, κ b * X b) ∧ ∑ b, ‖κ b‖ ≤ C)
    (hεq : 0 < εq) (hτK : 0 < τK) (hCK0 : 0 ≤ C_K)
    (hCK : D₁ + 4 * D_Y + (k : ℝ) + 2 * (C_P + 2 * (k : ℝ) + 2) + 8 ≤ C_K)
    (hKN : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ))
    (hKU : ∀ᶠ n : ℕ in atTop, K n ≤ ⌈((sz.size n : ℕ) : ℝ) ^ C_K⌉₊)
    (hY : ∀ σ : Fin k → Bool, ∀ᶠ n : ℕ in atTop, ∃ P : ℝ, 0 ≤ P ∧
      P ≤ ((sz.size n : ℕ) : ℝ) ^ C_P ∧
      ∀ τ : PathΩ sz → ℕ, (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
        YMomentBoundsN sz (E n) σ (gridTime s v K n) τ (K n)
          (fun j ω => YvecN sz E s v K n j σ ω)
          (fun _ => gridStep s v K n ^ 2 * P) (fun _ => gridStep s v K n ^ 4 * P ^ 2))
    (hlam : ∀ᶠ n : ℕ in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λg)
    (hδ : ∀ᶠ n : ℕ in atTop, ∀ j < K n, ((sz.W n : ℕ) : ℝ) ^ (-D') +
      eeShiftErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤
        ((sz.W n : ℕ) : ℝ) ^ (-D'')) :
    ∀ᶠ n : ℕ in atTop, ∀ σ : Fin k → Bool, ∀ A : Finset (Fin k), STIdiff σ ⊆ A → s n < v n →
      ∃ G : Set (PathΩ sz), (pathP sz).real Gᶜ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) ∧
        ∀ ω ∈ G,
          (∀ j ≤ K n, pathH sz s v K n j ω ∈
            sz.GoodSetN n (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D' ∩
              GoodLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)) →
          ∀ a : Fin k → Zd d (sz.L n),
            ‖zeroModeSet d (sz.L n) A (AvecN sz E s v K n (K n) σ ω) a‖ ≤
              assembledRHSNZN sz E s v K n k C (2 ^ k) Γ Λ Φ₁ Φ₂ Φ₃ D'' D_Y τK εq
                (Finset.univ.sup' Finset.univ_nonempty fun b =>
                  ‖zeroModeSet d (sz.L n) A (AvecN sz E s v K n 0 σ ω) b‖) := by
  have hA := assembledN sz hsize k εq hεq D_Y D₁ (C_P + 2 * (k : ℝ) + 2) C_K hCK0 hCK
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
  filter_upwards [hA, hKN, hKU, Filter.eventually_all.2 hY, Filter.eventually_all.2 hEnv, hlam, hδ,
    hsize.eventually_ge_atTop ((4 : ℝ) ^ (k + 1)), hsize.eventually_ge_atTop 1] with
    n hAn hKNn hKUn hYn hEnvn hlamn hδn h4n hN1
  intro σ A hσA hsvn
  obtain ⟨P, hP0, hPle, hYP⟩ := hYn σ
  obtain ⟨hg, hgΛ⟩ := hlamn
  have hEn2 : |E n| < 2 := by have := hE n; linarith [abs_nonneg (E n)]
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith [abs_nonneg (E n)]
  have hKn : K n ≠ 0 := hK0 n
  have hK1 : 1 ≤ K n := Nat.one_le_iff_ne_zero.2 hKn
  have hvs : v n - s n ≤ 1 := by linarith [hv1 n, hs0 n]
  have hΔ : gridStep s v K n ≤ ((sz.size n : ℕ) : ℝ) ^ (-C_K) := nzEnd_step_le sz hKNn hvs
  have hKΔ : (K n : ℝ) * gridStep s v K n ≤ 1 := nzEnd_K_mul_step hKn hvs
  have hΔ0 : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n (hsv n)
  have hu0 : ∀ i ≤ K n, 0 ≤ gridTime s v K n i := fun i _ =>
    nzEnd_gridTime_nonneg (hs0 n) (hsv n) i
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi =>
    (nzEnd_gridTime_le (hsv n) hKn hi).trans_lt (hv1 n)
  have hmono : ∀ i m, i ≤ m → m ≤ K n → gridTime s v K n i ≤ gridTime s v K n m :=
    fun i m him _ => ST_gridTime_mono s v K n (hsv n) him
  have hsu : ∀ i, s n ≤ gridTime s v K n i := fun i => by
    have h := ST_gridTime_mono s v K n (hsv n) (Nat.zero_le i)
    rwa [ST_gridTime_zero] at h
  have hcaseU : ∀ i, 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ gridTime s v K n i :=
    fun i => by linarith [hcase n, hsu i]
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hAk : (2 : ℝ) ^ A.card ≤ 2 ^ k :=
    pow_le_pow_right₀ (by norm_num) (by simpa using Finset.card_le_univ A)
  have h4A : (4 : ℝ) ^ (A.card + 1) ≤ 4 ^ (k + 1) :=
    pow_le_pow_right₀ (by norm_num) (Nat.succ_le_succ (by simpa using Finset.card_le_univ A))
  have h16A : (16 : ℝ) ^ (A.card + 1) ≤ 16 ^ (k + 1) :=
    pow_le_pow_right₀ (by norm_num) (Nat.succ_le_succ (by simpa using Finset.card_le_univ A))
  have h16 : (16 : ℝ) ^ (k + 1) = ((4 : ℝ) ^ (k + 1)) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hdD0 : ∀ j, j ≤ K n →
      0 ≤ dDriftLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) := by
    intro j hj
    have hη := etaT_pos hEn2 (hu1 j hj)
    have hB := Sizes.STBctl_pos sz n (hu1 j hj)
    have hk2 : (0 : ℝ) ≤ (k : ℝ) - 2 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    unfold dDriftLinN
    have h1 := hΓ n
    have h2 := hΦ₁ n
    have h3 := hΦ₂ n
    have h4 := hΦ₃ n
    positivity
  -- the data of the assembly
  set u : ℕ → ℝ := gridTime s v K n with hu
  set Δ : ℝ := gridStep s v K n with hΔdef
  set τ : PathΩ sz → ℕ := nqLinExitTauN sz E s v K k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D' n with hτdef
  set A0 : PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ := fun ω =>
    zeroModeSet d (sz.L n) A (AvecN sz E s v K n 0 σ ω) with hA0
  set Dr : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ := fun j ω =>
    zeroModeSet d (sz.L n) A (driftTensorN sz n (E n) (u j) (pathH sz s v K n j ω) σ) with hDr
  set Z : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ := fun j ω =>
    zeroModeSet d (sz.L n) A (ZvecN sz E s v K n j σ ω) with hZ
  set Y : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ := fun j ω =>
    zeroModeSet d (sz.L n) A (YvecN sz E s v K n j σ ω) with hY'
  set R : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ := fun j ω =>
    zeroModeSet d (sz.L n) A (predIncN sz E s v K n j σ ω -
      ((Δ : ℝ) : ℂ) • driftTensorN sz n (E n) (u j) (pathH sz s v K n j ω) σ) with hR
  set Af : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ := fun m ω =>
    Ugen d (sz.L n) (sz.lam n) (E n) σ (u 0) (u m) (A0 ω) +
      ∑ j ∈ Finset.range (min m (τ ω)), Ugen d (sz.L n) (sz.lam n) (E n) σ (u (j + 1)) (u m)
        (((Δ : ℝ) : ℂ) • Dr j ω + Z j ω + Y j ω + R j ω) with hAf
  set stepE : ℕ → ℝ := fun j => 2 ^ k * stepErrN d (sz.L n) (sz.W n) (E n) k (u j) (u (j + 1)) Δ
    (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (u (j + 1)))⁻¹ ^ k) with hstepE
  have hτmeas : ∀ j, MeasurableSet[filt sz j] {ω | j < τ ω} :=
    nqLinExitMeasN sz E s v K n k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D'
  have hmemG : ∀ (ω : PathΩ sz) (j : ℕ), j < τ ω →
      pathH sz s v K n j ω ∈ sz.GoodSetN n (E n) (u j) k (Γ n) (Λ n) (Φ n) τ' D' :=
    fun ω j hj => (mem_of_lt_nqLinExitTauN hj).1
  have hmemL : ∀ (ω : PathΩ sz) (j : ℕ), j < τ ω →
      pathH sz s v K n j ω ∈ GoodLinN sz n (E n) (u j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) :=
    fun ω j hj => (mem_of_lt_nqLinExitTauN hj).2
  have hop : ∀ i m, i ≤ m → m ≤ K n → ∀ X : (Fin k → Zd d (sz.L n)) → ℂ,
      ‖zeroModeSet d (sz.L n) A (Ugen d (sz.L n) (sz.lam n) (E n) σ (u i) (u m) X)‖ ≤ C * ‖X‖ :=
    fun i m him hmK =>
      (hCop (sz.L n) (sz.three_le_L n) (sz.lam n) (E n) hg hgΛ hEn2 (hκm n) (u i) (u m)
        (hu0 i (him.trans hmK)) (hcaseU i) (hmono i m him hmK) (hu1 m hmK) σ A hσA).1
  have hZmeas : ∀ j, StronglyMeasurable[filt sz (j + 1)] (Z j) := fun j =>
    (LinearMap.continuous_of_finiteDimensional
      (zeroModeSetLin (d := d) (L := sz.L n) A)).comp_stronglyMeasurable
      (gridAsm_stronglyMeasurable_ZvecN sz E s v K n j σ)
  have hsubG : ∀ m ≤ K n, ∀ (a : Fin k → Zd d (sz.L n)) (j : ℕ), j < m →
      SubGaussStopN sz (E n) σ u τ Z m a j (cQVNZN sz E s v K n k C (Γ n) (Λ n) D'' j) := by
    intro m hm a j hj
    have hrow := (hCop (sz.L n) (sz.three_le_L n) (sz.lam n) (E n) hg hgΛ hEn2 (hκm n)
      (u (j + 1)) (u m) (hu0 _ ((Nat.succ_le_of_lt hj).trans hm)) (hcaseU _)
      (hmono _ _ (Nat.succ_le_of_lt hj) hm) (hu1 m hm) σ A hσA).2 a
    exact subGaussStop_nzN sz E s v K n σ A C (Γ n) (Λ n) (Φ n) τ' D' D'' τ hk hE2 hs0 hsv hv1
      hC.le (hΓ n) (hΛ n) hτmeas hmemG m hm a j hj hrow (hδn j (lt_of_lt_of_le hj hm))
  have hu0K : u (K n) = v n := gridTime_last s v K n hKn
  have hu00 : u 0 = s n := ST_gridTime_zero s v K n
  have hP'0 : 0 ≤ (4 : ℝ) ^ (k + 1) * P := by positivity
  have hP'le : (4 : ℝ) ^ (k + 1) * P ≤ ((sz.size n : ℕ) : ℝ) ^ (C_P + 2 * (k : ℝ) + 2) := by
    have h2 : ((sz.size n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * (k : ℝ) + 2) := by
      calc ((sz.size n : ℕ) : ℝ) = ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1
          (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
    have h3 : (4 : ℝ) ^ (k + 1) ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * (k : ℝ) + 2) := h4n.trans h2
    calc (4 : ℝ) ^ (k + 1) * P
        ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * (k : ℝ) + 2) * ((sz.size n : ℕ) : ℝ) ^ C_P :=
          mul_le_mul h3 hPle hP0 (Real.rpow_nonneg hN0.le _)
      _ = ((sz.size n : ℕ) : ℝ) ^ (C_P + 2 * (k : ℝ) + 2) := by
          rw [← Real.rpow_add hN0]; congr 1; ring
  have hv : ∀ j < K n, 4 ^ (A.card + 1) * (Δ ^ 2 * P) ≤ Δ ^ 2 * ((4 : ℝ) ^ (k + 1) * P) := by
    intro j _
    calc (4 : ℝ) ^ (A.card + 1) * (Δ ^ 2 * P) ≤ 4 ^ (k + 1) * (Δ ^ 2 * P) :=
          mul_le_mul_of_nonneg_right h4A (by positivity)
      _ = Δ ^ 2 * ((4 : ℝ) ^ (k + 1) * P) := by ring
  have hw : ∀ j < K n, 16 ^ (A.card + 1) * (Δ ^ 4 * P ^ 2) ≤
      Δ ^ 4 * (((4 : ℝ) ^ (k + 1) * P) ^ 2) := by
    intro j _
    calc (16 : ℝ) ^ (A.card + 1) * (Δ ^ 4 * P ^ 2) ≤ 16 ^ (k + 1) * (Δ ^ 4 * P ^ 2) :=
          mul_le_mul_of_nonneg_right h16A (by positivity)
      _ = Δ ^ 4 * (((4 : ℝ) ^ (k + 1) * P) ^ 2) := by rw [h16]; ring
  have hbundle : GridAssemblyHypN sz (n := n) (k := k) (E n) σ u τ Δ (K n)
      (fun _ _ X => zeroModeSet d (sz.L n) A X = X) A0 Af Dr Z Y R (fun _ _ => C) (fun _ _ => 0) 0
      (fun j _ => 2 ^ k * dDriftLinN sz n (E n) (u j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n))
      (fun _ _ => 0) (fun m a j => cQVNZN sz E s v K n k C (Γ n) (Λ n) D'' j)
      (fun _ => 4 ^ (A.card + 1) * (Δ ^ 2 * P)) (fun _ => 16 ^ (A.card + 1) * (Δ ^ 4 * P ^ 2))
      stepE := {
    hE := hEn2.le
    hu0 := hu0
    hu1 := hu1
    hΔ0 := hΔ0
    hexp := fun m _ => Eventually.of_forall fun ω => rfl
    hκ0 := fun _ _ _ _ => hC.le
    hε0 := fun _ _ _ _ => le_rfl
    hker := nz_hker sz n (E n) σ A u (K n) C hC.le hEn2.le hu0 hu1 hop
    hδ0 := le_rfl
    hA0cls := fun ω _ => zeroModeSet_idem d (sz.L n) k A _
    hdDrift0 := fun ω j hj => mul_nonneg (by positivity) (hdD0 j hj.le)
    hδD0 := fun _ _ _ => le_rfl
    hdrift := fun ω j hjK hjτ b => by
      have h := nz_hdriftN sz hk σ A E s v K Γ Φ₁ Φ₂ Φ₃ τ hmemL ω j hjK hjτ b
      exact h.trans (mul_le_mul_of_nonneg_right hAk (hdD0 j hjK.le))
    hDcls := fun ω j _ _ => zeroModeSet_idem d (sz.L n) k A _
    hc_pos := fun m hm1 hmK a => by
      have hΔpos : 0 < Δ :=
        div_pos (by linarith) (by exact_mod_cast Nat.pos_of_ne_zero hKn)
      have hterm : ∀ j ∈ Finset.range m,
          0 < (cQVNZN sz E s v K n k C (Γ n) (Λ n) D'' j : ℝ) := by
        intro j hj
        have hjK : j ≤ K n := by have := Finset.mem_range.1 hj; omega
        have hη := etaT_pos hEn2 (hu1 j hjK)
        have hB := Sizes.STBctl_pos sz n (hu1 j hjK)
        have hk0 : (0 : ℝ) < k := by
          have : (2 : ℝ) ≤ k := by exact_mod_cast hk
          linarith
        have h1 := hΓ n
        have h2 := hΛ n
        have hWD : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ (-D'') := Real.rpow_pos_of_pos hW0 _
        have hpos : 0 < Δ * ((k : ℝ) * C ^ 2 * (Γ n * (Γ n * Λ n) *
            ((sz.Bctl n (u j)) ^ (2 * k) / etaT (E n) (u j)) + ((sz.W n : ℕ) : ℝ) ^ (-D''))) := by
          positivity
        unfold cQVNZN
        rw [NNReal.coe_pos, Real.toNNReal_pos]
        exact hpos
      exact Finset.sum_pos hterm ⟨0, Finset.mem_range.2 (by omega)⟩
    hv0 := fun _ _ => by positivity
    hw0 := fun _ _ => by positivity
    hY := yMomentBounds_nzN sz (E n) σ A u τ (K n) (fun j ω => YvecN sz E s v K n j σ ω)
      (fun _ => Δ ^ 2 * P) (fun _ => Δ ^ 4 * P ^ 2) hEn2.le hu0 hu1 (hYP τ hτmeas)
    hstepErr0 := fun j hj => mul_nonneg (by positivity)
      (nzEnd_stepErrN_nonneg hEn2 (hu1 j hj.le) (hu1 (j + 1) hj) hΔ0
        (by
          have := etaT_pos hEn2 (hu1 (j + 1) hj)
          positivity))
    hR := (hEnvn σ).mono fun ω hω j hj _ b => by
      have hse0 : 0 ≤ stepErrN d (sz.L n) (sz.W n) (E n) k (u j) (u (j + 1)) Δ
          (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (u (j + 1)))⁻¹ ^ k) :=
        nzEnd_stepErrN_nonneg hEn2 (hu1 j hj.le) (hu1 (j + 1) hj) hΔ0
          (by
            have := etaT_pos hEn2 (hu1 (j + 1) hj)
            positivity)
      have hnorm : ‖predIncN sz E s v K n j σ ω - ((Δ : ℝ) : ℂ) •
          driftTensorN sz n (E n) (u j) (pathH sz s v K n j ω) σ‖ ≤
          stepErrN d (sz.L n) (sz.W n) (E n) k (u j) (u (j + 1)) Δ
            (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (u (j + 1)))⁻¹ ^ k) := by
        refine (pi_norm_le_iff_of_nonneg hse0).2 fun a => ?_
        have h := hω j hj a
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, driftTensorN]
        exact h
      calc ‖R j ω b‖
          ≤ ‖R j ω‖ := norm_le_pi_norm _ b
        _ ≤ 2 ^ A.card * ‖predIncN sz E s v K n j σ ω - ((Δ : ℝ) : ℂ) •
              driftTensorN sz n (E n) (u j) (pathH sz s v K n j ω) σ‖ := norm_zeroModeSet_le A _
        _ ≤ 2 ^ k * stepErrN d (sz.L n) (sz.W n) (E n) k (u j) (u (j + 1)) Δ
              (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (u (j + 1)))⁻¹ ^ k) :=
            mul_le_mul hAk hnorm (norm_nonneg _) (by positivity) }
  obtain ⟨G, hG, hGb⟩ := hAn (K n) (E n) σ u τ Δ
    (fun _ _ X => zeroModeSet d (sz.L n) A X = X) A0 Af Dr Z Y R (fun _ _ => C) (fun _ _ => 0) 0
    (fun j _ => 2 ^ k * dDriftLinN sz n (E n) (u j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n))
    (fun _ _ => 0) (fun m a j => cQVNZN sz E s v K n k C (Γ n) (Λ n) D'' j)
    (fun _ => 4 ^ (A.card + 1) * (Δ ^ 2 * P)) (fun _ => 16 ^ (A.card + 1) * (Δ ^ 4 * P ^ 2))
    stepE ((4 : ℝ) ^ (k + 1) * P) hK1 hKUn hΔ hKΔ hP'0 hP'le hv hw hτmeas hZmeas hsubG hbundle
  refine ⟨G, hG, fun ω hω hgood a => ?_⟩
  have hτeq : τ ω = K n := gridExitTauN_eq_of_forall_mem hgood
  have hτpos : 0 < τ ω := by rw [hτeq]; omega
  have hb := hGb ω hω hτpos (K n) le_rfl a
  have hAeq : Af (K n) ω = zeroModeSet d (sz.L n) A (AvecN sz E s v K n (K n) σ ω) := by
    have hex := zeroModeCalc_duhamel_inside_at sz E s v K n hEn2 (hs0 n) (hsv n) (hv1 n) hKn σ A τ
      (K n) ω (min_le_left _ _)
    rw [hτeq, min_self] at hex
    have hinner : ∀ j, ((Δ : ℝ) : ℂ) • Dr j ω + Z j ω + Y j ω + R j ω =
        zeroModeSet d (sz.L n) A (predIncN sz E s v K n j σ ω) +
          zeroModeSet d (sz.L n) A (martIncN sz E s v K n j σ ω) := by
      intro j
      have hm : martIncN sz E s v K n j σ ω =
          ZvecN sz E s v K n j σ ω + YvecN sz E s v K n j σ ω := by
        funext b; simp only [YvecN, Pi.add_apply]; ring
      have e1 : zeroModeSet d (sz.L n) A (predIncN sz E s v K n j σ ω) =
          R j ω + ((Δ : ℝ) : ℂ) • Dr j ω := by
        simp only [hR, hDr]
        rw [← zeroModeSet_smul, ← zeroModeSet_add, sub_add_cancel]
      have e2 : zeroModeSet d (sz.L n) A (martIncN sz E s v K n j σ ω) = Z j ω + Y j ω := by
        rw [hm, zeroModeSet_add]
      rw [e1, e2]
      abel
    rw [hex]
    change Ugen d (sz.L n) (sz.lam n) (E n) σ (u 0) (u (K n)) (A0 ω) +
        ∑ j ∈ Finset.range (min (K n) (τ ω)), Ugen d (sz.L n) (sz.lam n) (E n) σ (u (j + 1))
          (u (K n)) (((Δ : ℝ) : ℂ) • Dr j ω + Z j ω + Y j ω + R j ω) = _
    rw [hτeq, min_self]
    simp only [hinner]
    simp only [GridDuhamelN_Ugen_add, Finset.sum_add_distrib]
    rw [add_assoc]
  rw [hAeq] at hb
  refine hb.trans_eq ?_
  unfold assembledRHSNZN
  simp only [zero_mul, add_zero]
  rfl

end Assembly

/-! ## 5. The grid endpoint `nzGridEndN`

The statement is the pin `T2284_nzGridEndN` of `docs/tickets/checks/T2284-check.lean`, copied verbatim (script
diff in the report).  Exponents (fixed order): `Λg = 𝔡⁻¹`, `κ' = min κ (4/5)`, `C` = the constant of
`nzUgen_holds d k hd hk Λg κ'`, `ε₀' = min ε₀ 1`, `ε₁ = εq = ε₀'/8`, `D'' = 2(k+2)/𝔠 + 1`, `D' = D'' + 1`,
`τ' = 1`, `τ_R = min τ 1`, `τK = 1`, `D_Y = D_t = k + 2`, `cA = 2^k`, `C_P^* = max_σ C_P(σ)`
(`yMomentsUnifN`), `C_P' = C_P^* + 2k + 2`, `D₁' = D₁ + 1`, `C_K = D₁ + 2 C_P' + D'' + 16k + 40`. -/

/-- **`nzGridEndN`: the case-(ii) grid endpoint of the zero-mode-removed loops** (`lem:STOeq_Qt_nonzero`,
`3_5:1561`, proof `3_5:1889-1928`: `(sahwNQ_smalleta)` `:1903`, `(sahwNQ2)` `:1910`, `(am;asoiuw_smalleta)`
`:1916`; `(iisuwjyys)` `3_5:1545`; shape of `nqGridEndLinN`, `NQEndLin.lean:1067`).  Setting: `3 ≤ d`,
constants `κ, 𝔠, τ, 𝔡 > 0`, `N → ∞`, `W ≥ N^𝔠`, `(eq:WO)`, `|E| ≤ 2 - κ`, `0 ≤ s ≤ t < 1`, case (ii)
`1 - s ≤ g²/L²`, `1 - t ≥ N^{-1+τ}` (no `W⁻¹ ≤ (1-t)/(1-s)`: EK-5 has no such window).  For every length `k ≥ 2`,
deterministic levels `Λ ≥ 0` (`≥ 1` eventually), `Φ₁, Φ₂, Φ₃ ≥ 0`, end time `v ∈ [s,t]`, final loss `ε₀ > 0` and
failure exponent `D₁ > 0` there are exponents `ε₁, τ', D', C_K` such that, for every crude level `Φc` of
`GoodSetN` and every grid `N^{C_K} ≤ K_n ≤ ⌈N^{C_K}⌉`, eventually there is an event `G`, `P(Gᶜ) ≤ N^{-D₁}`, on
which: if the grid walk is in `GoodSetN(N^{ε₁}, Λ, Φc, τ', D') ∩ GoodLinN(N^{ε₁}, Φ₁, Φ₂, Φ₃)` at every `j ≤ K_n`
and the initial zero-mode-removed loops satisfy `|(Q^{(A)}(𝓛-𝒦))_{s,σ,a}| ≤ N^{ε₁} B_s^k` for every `σ` and
`A ⊇ I_diff(σ)`, then `|(Q^{(A)}(𝓛-𝒦))_{v,σ,a}(H_{K_n})| ≤ N^{ε₀}(Λ^{1/2} + Φ₁ + Φ₂ + Φ₃) B_v^k` for every `σ`,
every `A ⊇ I_diff(σ)` and every label `a`.  No `Φ²`, no `Φc` on the right side; no `STKbound` premise
(`stKbound_holds` discharges it). -/
theorem nzGridEndN :
  ∀ {d : ℕ} (sz : Sizes d) (κ 𝔠 τ 𝔡 : ℝ) (E s t : ℕ → ℝ),
    3 ≤ d → 0 < κ → 0 < 𝔠 → 0 < τ → 0 < 𝔡 →
    sz.SizeTendsto → sz.Bandwidth 𝔠 → sz.WO 𝔡 →
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    sz.STCaseII s t → sz.RangeCond τ t →
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
          (∀ (σ : Fin k → Bool) (A : Finset (Fin k)), STIdiff σ ⊆ A →
            ∀ a : Fin k → Zd d (sz.L n),
              ‖zeroModeSet d (sz.L n) A
                  (fun b : Fin k → Zd d (sz.L n) =>
                    sz.STLKM n (E n) (s n) (pathH sz s v K n 0 ω) σ b) a‖ ≤
                ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ k) →
          ∀ (σ : Fin k → Bool) (A : Finset (Fin k)), STIdiff σ ⊆ A →
            ∀ a : Fin k → Zd d (sz.L n),
              ‖zeroModeSet d (sz.L n) A
                  (fun b : Fin k → Zd d (sz.L n) =>
                    sz.STLKM n (E n) (v n) (pathH sz s v K n (K n) ω) σ b) a‖ ≤
                ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n) *
                  (sz.Bctl n (v n)) ^ k := by
  intro d sz κ 𝔠 τ 𝔡 E s t hd hκ h𝔠 hτ h𝔡 hsize hband hWO hE hs0 hst ht1 hcase hrange k hk
    Λ Φ₁ Φ₂ Φ₃ hΛ0 hΛ1 hΦ₁ hΦ₂ hΦ₃ v hsv hvt ε₀ hε₀ D₁ hD₁
  classical
  have hd1 : 1 ≤ d := by omega
  have hv1 : ∀ n, v n < 1 := fun n => (hvt n).trans_lt (ht1 n)
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith [abs_nonneg (E n)]
  have hk0 : (0 : ℝ) < k := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
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
  -- the constant of `lem:sum_decay_nonzero` (EK-5, loss-free): the operator and row bounds of `Q^{(A)} ∘ 𝒰`
  obtain ⟨C, hC, hCop⟩ := nzUgen_holds d k hd hk Λg κ' hΛg hκ'
  -- the range exponent of the end time, the `Y`-moment constant (one for all signs, before the grid)
  have hτR : 0 < min τ 1 := lt_min hτ one_pos
  have hτR1 : min τ 1 ≤ 1 := min_le_right _ _
  have hrangeV : sz.RangeCond (min τ 1) v := nzEnd_rangeCond_mono sz (min_le_left _ _) hvt hrange
  obtain ⟨Cmax, hCmax0, hYmax⟩ := nzEnd_yMomentsMax sz hκ hE hs0 hsv hv1 hsize hrangeV k
  -- the numerical constants, in the fixed order `C → ε₀' → ε₁ → D'' → D' → τ' → C_P → C_K`
  obtain ⟨e0, he0def⟩ : ∃ e0 : ℝ, e0 = min ε₀ 1 := ⟨_, rfl⟩
  have he0 : 0 < e0 := by rw [he0def]; exact lt_min hε₀ one_pos
  have he01 : e0 ≤ 1 := by rw [he0def]; exact min_le_right _ _
  have he0le : e0 ≤ ε₀ := by rw [he0def]; exact min_le_left _ _
  obtain ⟨D'', hD''def⟩ : ∃ D'' : ℝ, D'' = 2 * ((k : ℝ) + 2) / 𝔠 + 1 := ⟨_, rfl⟩
  have hD''0 : 0 ≤ D'' := by rw [hD''def]; positivity
  have hD''c : 𝔠 * D'' / 2 = (k : ℝ) + 2 + 𝔠 / 2 := by
    rw [hD''def]; field_simp
  obtain ⟨C_K, hCKdef⟩ : ∃ C_K : ℝ,
      C_K = D₁ + 2 * (Cmax + 2 * (k : ℝ) + 2) + D'' + 16 * k + 40 := ⟨_, rfl⟩
  have hCK0 : 0 ≤ C_K := by rw [hCKdef]; linarith
  refine ⟨e0 / 8, 1, D'' + 1, C_K, by linarith, one_pos, by linarith, hCK0, ?_⟩
  intro Φc K hK0 hKN hKU
  -- the exponent constraints on `C_K`
  have hθ1 : 1 - min τ 1 ≤ 1 := by linarith
  have hθk1 : (4 * (k : ℝ) + 8) * (1 - min τ 1) ≤ 4 * k + 8 :=
    mul_le_of_le_one_right (by positivity) hθ1
  have hθk2 : 5 * (k : ℝ) * (1 - min τ 1) ≤ 5 * k := mul_le_of_le_one_right (by positivity) hθ1
  have hθk3 : 2 * (k : ℝ) * (1 - min τ 1) ≤ 2 * k := mul_le_of_le_one_right (by positivity) hθ1
  have hC1 : (D₁ + 1) + 4 * ((k : ℝ) + 2) + (k : ℝ) + 2 * (Cmax + 2 * (k : ℝ) + 2) + 8 ≤ C_K := by
    rw [hCKdef]; linarith
  have hC2 : 8 + (4 * (k : ℝ) + 8) * (1 - min τ 1) + 2 * ((k : ℝ) + 2) < C_K := by
    rw [hCKdef]; linarith
  have hC3 : 3 + 4 * (1 : ℝ) + 5 * (k : ℝ) * (1 - min τ 1) + ((k : ℝ) + 2) < C_K := by
    rw [hCKdef]; linarith
  have hC4 : 2 * (1 - min τ 1) + 1 + 2 * (k : ℝ) * (1 - min τ 1) + ((k : ℝ) + 2) < C_K := by
    rw [hCKdef]; linarith
  have hC5 : 1 - min τ 1 < C_K := by rw [hCKdef]; linarith
  have hC6 : D'' + 2 * (k : ℝ) + 5 ≤ C_K := by rw [hCKdef]; linarith
  -- the eventual regime facts
  have hη := nzEnd_ev_hη sz hsize hκ' hκm hτR hrangeV
  have hδ := nzEnd_ev_hδ sz hd1 hsize h𝔠 hband k hE2 hs0 hsv hv1 hK0 hη hD''0 hC6 hKN
  have hlogR := nqBudget_merged_inputs sz (κ := κ) (τ' := min τ 1) (τK := 1) (C_K := C_K)
    (D_t := (k : ℝ) + 2) (E := E) (s := s) (v := v) (K := K) k hκ hτR hτR1 one_pos
    (by linarith) hk hsize hE hs0 hsv hv1 hK0 hrangeV hC2 hC3 hC4 hC5 hKN
  -- the six absorption lemmas of `budgetNZN`
  have H1 := nzEnd_ev_H1 sz hsize (C := C) (ε₁ := e0 / 8) (ε₀ := e0) (by linarith)
  have H2 := nzEnd_ev_H2 sz hsize k hκ' hκm (C := C) (cA := (2 : ℝ) ^ k) (ε₁ := e0 / 8) (ε₀ := e0)
    hC.le (by positivity) (by linarith)
  have H3 := nzEnd_ev_H3 sz hsize k hκ' hκm (C := C) (εq := e0 / 8) (ε₁ := e0 / 8) (ε₀ := e0)
    hC.le (by linarith)
  have H4 := nzEnd_ev_H4 sz hsize hband k (C := C) (D'' := D'') (εq := e0 / 8) (ε₀ := e0) hC.le hD''0
    (by rw [hD''c]; linarith)
  have H5 : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-((k : ℝ) + 2)) ≤
      ((sz.size n : ℕ) : ℝ) ^ e0 / 6 := by
    filter_upwards [nzEnd_ev_H56 sz hsize k 1 (D := (k : ℝ) + 2) (ε₀ := e0) (by linarith)] with n h
    rw [one_mul] at h
    exact h
  have H6 := nzEnd_ev_H56 sz hsize k ((2 : ℝ) ^ k) (D := (k : ℝ) + 2) (ε₀ := e0) (by linarith)
  have hun := nzEnd_ev_union sz hsize ((4 : ℝ) ^ k) D₁
  -- the assembly at the exit time `nqLinExitTauN` (per pair `(σ, A)`, `D₁ + 1`)
  have hΓ0 : ∀ n, 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (e0 / 8) := fun n =>
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hAsm := nzEnd_assembly sz (κ := κ) (E := E) (s := s) (v := v) (K := K) k hk hκ hE hs0 hsv
    hv1 hK0 hsize hKb hcase (fun n => ((sz.size n : ℕ) : ℝ) ^ (e0 / 8)) Λ Φc Φ₁ Φ₂ Φ₃ hΓ0 hΛ0
    hΦ₁ hΦ₂ hΦ₃ (Λg := Λg) (κ' := κ') (C := C) (τ' := 1) (D' := D'' + 1) (D'' := D'')
    (D_Y := (k : ℝ) + 2) (τK := 1) (εq := e0 / 8) (D₁ := D₁ + 1) (C_P := Cmax) (C_K := C_K)
    hκ' hκm hC hCop (by linarith) one_pos hCK0 hC1 hKN hKU (hYmax K hK0) hlam hδ
  filter_upwards [hAsm, hlogR, H1, H2, H3, H4, H5, H6, hΛ1, hun, hKN] with n hAsmn hlogRn H1n H2n
    H3n H4n H5n H6n hΛ1n hunn hKNn
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := nzEnd_one_le_size sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  by_cases hsvn : s n = v n
  · -- the collapsed window `v_n = s_n`: `G = univ`
    refine ⟨Set.univ, ?_, fun ω _ _ hinit' σ A hσA a => ?_⟩
    · rw [Set.compl_univ]
      simp only [measureReal_empty]
      exact Real.rpow_nonneg hN0.le _
    · exact nzEnd_collapse sz (hv1 n) hsvn (by linarith) hΛ1n (hΦ₁ n) (hΦ₂ n) (hΦ₃ n) ω σ A a
        (hinit' σ A hσA a)
  · have hlt : s n < v n := lt_of_le_of_ne (hsv n) hsvn
    -- the events, one per pair `(σ, A)` with `I_diff(σ) ⊆ A`
    have hAsmP := fun p : {p : (Fin k → Bool) × Finset (Fin k) // STIdiff p.1 ⊆ p.2} =>
      hAsmn p.1.1 p.1.2 p.2 hlt
    choose Gs hGsP hGsb using hAsmP
    refine ⟨⋂ p, Gs p, ?_, ?_⟩
    · -- the union bound over the `≤ 4^k` pairs
      have hcompl : (⋂ p, Gs p)ᶜ = ⋃ p, (Gs p)ᶜ := by rw [Set.compl_iInter]
      have hcard : (Fintype.card {p : (Fin k → Bool) × Finset (Fin k) // STIdiff p.1 ⊆ p.2} : ℝ) ≤
          (4 : ℝ) ^ k := by
        have h1 := Fintype.card_subtype_le
          (fun p : (Fin k → Bool) × Finset (Fin k) => STIdiff p.1 ⊆ p.2)
        have h2 : Fintype.card ((Fin k → Bool) × Finset (Fin k)) = 2 ^ k * 2 ^ k := by
          simp [Fintype.card_prod, Fintype.card_finset]
        rw [h2] at h1
        have h3 : (4 : ℝ) ^ k = ((2 ^ k * 2 ^ k : ℕ) : ℝ) := by
          push_cast; rw [← mul_pow]; norm_num
        rw [h3]
        exact_mod_cast h1
      rw [hcompl]
      calc (pathP sz).real (⋃ p, (Gs p)ᶜ) ≤ ∑ p, (pathP sz).real (Gs p)ᶜ :=
            measureReal_iUnion_fintype_le _
        _ ≤ ∑ _p : {p : (Fin k → Bool) × Finset (Fin k) // STIdiff p.1 ⊆ p.2},
              ((sz.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) := Finset.sum_le_sum fun p _ => hGsP p
        _ = (Fintype.card {p : (Fin k → Bool) × Finset (Fin k) // STIdiff p.1 ⊆ p.2} : ℝ) *
              ((sz.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) := by simp
        _ ≤ (4 : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) :=
            mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hN0.le _)
        _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) := hunn
    · intro ω hω hgood hinit' σ A hσA a
      have hωp : ω ∈ Gs ⟨(σ, A), hσA⟩ := Set.mem_iInter.1 hω ⟨(σ, A), hσA⟩
      have hb := hGsb ⟨(σ, A), hσA⟩ ω hωp hgood a
      have hX0 : (Finset.univ.sup' Finset.univ_nonempty fun b =>
            ‖zeroModeSet d (sz.L n) A (AvecN sz E s v K n 0 σ ω) b‖) ≤
          ((sz.size n : ℕ) : ℝ) ^ (e0 / 8) * (sz.Bctl n (s n)) ^ k := by
        refine Finset.sup'_le _ _ fun b _ => ?_
        have h := hinit' σ A hσA b
        have e : AvecN sz E s v K n 0 σ ω =
            (fun b : Fin k → Zd d (sz.L n) =>
              sz.STLKM n (E n) (s n) (pathH sz s v K n 0 ω) σ b) := by
          funext b
          simp only [AvecN, ST_gridTime_zero]
        rw [e]
        exact h
      have hbud := budgetNZN sz E s v K n k C ((2 : ℝ) ^ k)
        (fun n => ((sz.size n : ℕ) : ℝ) ^ (e0 / 8)) Λ Φ₁ Φ₂ Φ₃ D'' ((k : ℝ) + 2) ((k : ℝ) + 2) 1
        (e0 / 8) e0 (e0 / 8)
        (Finset.univ.sup' Finset.univ_nonempty fun b =>
          ‖zeroModeSet d (sz.L n) A (AvecN sz E s v K n 0 σ ω) b‖) hk hC (by positivity)
        (by linarith) (hE2 n) (hs0 n) (hsv n) (hv1 n) (hK0 n) rfl hΛ1n (hΦ₁ n) (hΦ₂ n) (hΦ₃ n)
        hlogRn.1 hX0 hlogRn.2 H1n H2n H3n H4n H5n H6n
      have hlk : AvecN sz E s v K n (K n) σ ω =
          (fun b : Fin k → Zd d (sz.L n) =>
            sz.STLKM n (E n) (v n) (pathH sz s v K n (K n) ω) σ b) := by
        funext b
        simp only [AvecN, gridTime_last s v K n (hK0 n)]
      rw [← hlk]
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

Namespace `RBM.Ind.QtNonzeroEndInst`.  Data: `szB` (merged `Step34Inst`: `d = 3`, `L = 4`, `W = n + 4`,
`ilambda = 1`, `N = (4(n+4))^3`; `szB_tendsto`, `szB_bandwidth` `𝔠 = 1/6`, `szB_WO` `𝔡 = 1/10`), the case-(ii)
window `s ≡ 15/16`, `t ≡ 31/32` (`szB_caseII`: `1 - s = 1/16 = ilambda²/L²`), `v ≡ 31/32` (non-collapsed,
`s < v`) and `v ≡ 15/16` (collapsed, `v = s`), `E = Einst ≡ 1/2` (`Im m = √15/4 ≈ 0.968`), `κ = 1`
(`κ' = min κ (4/5) = 4/5`), `τ = 1/2` (`RangeCond (1/2) t`: `N^{-1/2} ≤ 1/64 ≤ 1/32`, from `szB_size_ge`),
`k = 3`, `σ = sig3 = (+,-,+)` (`I_diff(σ) = {0, 1}`), levels `Λ ≡ 1`, `Φ₁ = Φ₂ = Φ₃ = Φc ≡ 1`, `ε₀ = 1/10`,
`D₁ = 1`.  The grid is `KB C_K n = max 1 ⌈N^{C_K}⌉` (so `N^{C_K} ≤ K_n ≤ ⌈N^{C_K}⌉`).  The constant
`C` of `nzUgen_holds d k hd hk Λg κ'` stays abstract (`Classical.choose`; only `C > 0` and the bounds are
known), so every instance holds for the actual `C`.  Each eventual statement is unfolded at one size index
(`Filter.Eventually.exists`). -/

namespace QtNonzeroEndInst

open RBM.Gauss.Step34Inst RBM.Ind.AzumaProxyNInst

/-! ### The data -/

/-- The window of the instances: `s ≡ 15/16` (case (ii) at `szB`: `1 - s = 1/16 = ilambda²/L²`). -/
abbrev sB : ℕ → ℝ := fun _ => 15 / 16

/-- `t ≡ 31/32`. -/
abbrev tB : ℕ → ℝ := fun _ => 31 / 32

/-- The non-collapsed end time `v ≡ 31/32` (`s < v`). -/
abbrev vB : ℕ → ℝ := fun _ => 31 / 32

/-- The collapsed end time `v ≡ 15/16 = s`. -/
abbrev vC : ℕ → ℝ := fun _ => 15 / 16

/-- The levels `Λ = Φ₁ = Φ₂ = Φ₃ = Φc ≡ 1`. -/
abbrev oneL : ℕ → ℝ := fun _ => 1

/-- The bulk gap constant `κ' = min κ (4/5)` at `κ = 1`. -/
abbrev κz : ℝ := min 1 (4 / 5)

theorem κz_pos : 0 < κz := lt_min one_pos (by norm_num)

/-- The constant `C` of `nzUgen_holds 3 3 _ _ 10 κz` (`Λg = 𝔡⁻¹ = 10`): abstract, positive. -/
theorem Cz_ex : ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g E : ℝ, 0 < g → g ≤ 10 → |E| < 2 → κz ≤ (mE E).im →
      ∀ v w : ℝ, 0 ≤ v → 1 - g ^ 2 / (L : ℝ) ^ 2 ≤ v → v ≤ w → w < 1 →
      ∀ (σ : Fin 3 → Bool) (A : Finset (Fin 3)), STIdiff σ ⊆ A →
        (∀ X : (Fin 3 → Zd 3 L) → ℂ, ‖zeroModeSet 3 L A (Ugen 3 L g E σ v w X)‖ ≤ C * ‖X‖) ∧
        ∀ a : Fin 3 → Zd 3 L, ∃ κ : (Fin 3 → Zd 3 L) → ℂ,
          (∀ X : (Fin 3 → Zd 3 L) → ℂ,
            zeroModeSet 3 L A (Ugen 3 L g E σ v w X) a = ∑ b, κ b * X b) ∧ ∑ b, ‖κ b‖ ≤ C :=
  nzUgen_holds 3 3 (by norm_num) (by norm_num) 10 κz (by norm_num) κz_pos

/-- The abstract constant `C`. -/
abbrev Cz : ℝ := Classical.choose Cz_ex

theorem Cz_pos : 0 < Cz := (Classical.choose_spec Cz_ex).1

/-- `D'' = 2(k+2)/𝔠 + 1` at `k = 3`, `𝔠 = 1/6` (`= 61`). -/
abbrev Ddz : ℝ := 2 * (((3 : ℕ) : ℝ) + 2) / (1 / 6) + 1

theorem Ddz_eq : Ddz = 61 := by norm_num [Ddz]

theorem hE_B : ∀ n, |Einst n| ≤ 2 - 1 := fun n => by norm_num [Einst]

theorem hκm_B : ∀ n, κz ≤ (mE (Einst n)).im := fun n => nqGood1_mE_im_ge one_pos (hE_B n)

theorem hlam_B : ∀ᶠ n : ℕ in atTop, 0 < szB.lam n ∧ szB.lam n ≤ 10 :=
  Eventually.of_forall fun n => ⟨by norm_num [szB], by norm_num [szB]⟩

theorem sB_nonneg : ∀ n, 0 ≤ sB n := fun n => by norm_num [sB]

theorem sB_le_tB : ∀ n, sB n ≤ tB n := fun n => by norm_num [sB, tB]

theorem tB_lt_one : ∀ n, tB n < 1 := fun n => by norm_num [tB]

theorem sB_le_vB : ∀ n, sB n ≤ vB n := fun n => by norm_num [sB, vB]

theorem vB_le_tB : ∀ n, vB n ≤ tB n := fun n => by norm_num [vB, tB]

theorem vB_lt_one : ∀ n, vB n < 1 := fun n => by norm_num [vB]

theorem sB_le_vC : ∀ n, sB n ≤ vC n := fun n => by norm_num [sB, vC]

theorem vC_le_tB : ∀ n, vC n ≤ tB n := fun n => by norm_num [vC, tB]

theorem vC_lt_one : ∀ n, vC n < 1 := fun n => by norm_num [vC]

/-- **The range condition at the data** (new): `N^{-1+1/2} ≤ 1 - t = 1/32` (`N ≥ 4096`, so
`N^{-1/2} ≤ 1/64`). -/
theorem rangeCond_tB : szB.RangeCond (1 / 2) tB := by
  refine Eventually.of_forall fun n => ?_
  have hN : (4096 : ℝ) ≤ ((szB.size n : ℕ) : ℝ) := by exact_mod_cast szB_size_ge n
  change ((szB.size n : ℕ) : ℝ) ^ (-1 + 1 / 2 : ℝ) ≤ 1 - 31 / 32
  calc ((szB.size n : ℕ) : ℝ) ^ (-1 + 1 / 2 : ℝ) ≤ (4096 : ℝ) ^ (-1 + 1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hN (by norm_num)
    _ ≤ 1 - 31 / 32 := by
        have h1 : (64 : ℝ) ≤ (4096 : ℝ) ^ (1 / 2 : ℝ) := by
          rw [← Real.sqrt_eq_rpow, show (4096 : ℝ) = 64 ^ 2 by norm_num]
          exact (Real.sqrt_sq (by norm_num)).ge
        rw [show (-1 + 1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num, Real.rpow_neg (by norm_num)]
        calc ((4096 : ℝ) ^ (1 / 2 : ℝ))⁻¹ ≤ (64 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h1
          _ ≤ 1 - 31 / 32 := by norm_num

theorem σ3_idiff : STIdiff sig3 = {0, 1} := by decide

/-! ### The grid `KB C_K n = max 1 ⌈N^{C_K}⌉` -/

/-- The grid of the instances: `N^{C_K} ≤ K_n ≤ ⌈N^{C_K}⌉` (copy of `NQEndLinInst.KC`,
`NQEndLin.lean:1346`, for `szB`). -/
def KB (C_K : ℝ) (n : ℕ) : ℕ := max 1 ⌈((szB.size n : ℕ) : ℝ) ^ C_K⌉₊

theorem KB_ne_zero (C_K : ℝ) (n : ℕ) : KB C_K n ≠ 0 := by
  unfold KB
  exact Nat.pos_iff_ne_zero.1 (lt_of_lt_of_le one_pos (le_max_left _ _))

theorem KB_low (C_K : ℝ) (n : ℕ) : ((szB.size n : ℕ) : ℝ) ^ C_K ≤ (KB C_K n : ℝ) := by
  unfold KB
  have h : ((szB.size n : ℕ) : ℝ) ^ C_K ≤ (⌈((szB.size n : ℕ) : ℝ) ^ C_K⌉₊ : ℝ) := Nat.le_ceil _
  exact h.trans (by exact_mod_cast le_max_right _ _)

theorem KB_up (C_K : ℝ) (n : ℕ) : KB C_K n ≤ ⌈((szB.size n : ℕ) : ℝ) ^ C_K⌉₊ := by
  unfold KB
  have hN : (0 : ℝ) < ((szB.size n : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (by have := szB.one_le_size n; omega)
  exact max_le (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hN _)) le_rfl

/-- The window of the instances is not collapsed: `s_n = 15/16 < 31/32 = v_n`, so the grid step
`Δ = (v_n - s_n)/K_n` is positive on every grid `KB C_K`. -/
theorem window_nondegenerate (C_K : ℝ) (n : ℕ) :
    sB n < vB n ∧ 0 < gridStep sB vB (KB C_K) n := by
  refine ⟨by norm_num [sB, vB], ?_⟩
  have hK : (0 : ℝ) < (KB C_K n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero (KB_ne_zero _ n))
  exact div_pos (by norm_num [vB, sB]) hK

/-- The collapsed window is collapsed: `s_n = v_n`, `Δ = 0`. -/
theorem window_collapsed (C_K : ℝ) (n : ℕ) : sB n = vC n ∧ gridStep sB vC (KB C_K) n = 0 := by
  refine ⟨by norm_num [sB, vC], ?_⟩
  unfold gridStep
  norm_num [sB, vC]

/-! ### (1) The asymptotic helpers at concrete exponents -/

/-- `7 x^{1/10} ≤ x^{1/5}`, `5 (1 + log x)^3 x^{1/10} ≤ x^{1/5}` and `7 x^{1/10} (log x + 1) ≤ x^{1/5}`
for some real `x` (copy of `NQEndLinInst.asymp_instance`, `NQEndLin.lean:1375`). -/
theorem asymp_instance : (∃ x : ℝ, 7 * x ^ (1 / 10 : ℝ) ≤ x ^ (1 / 5 : ℝ)) ∧
    (∃ x : ℝ, 5 * (1 + Real.log x) ^ 3 * x ^ (1 / 10 : ℝ) ≤ x ^ (1 / 5 : ℝ)) ∧
    (∃ x : ℝ, 7 * x ^ (1 / 10 : ℝ) * (Real.log x + 1) ≤ x ^ (1 / 5 : ℝ)) :=
  ⟨(nzEnd_ev_rpow_le (a := 1 / 10) (b := 1 / 5) (by norm_num) 7).exists,
    (nzEnd_ev_polylog_le 3 (a := 1 / 10) (b := 1 / 5) (by norm_num) 5).exists,
    (nzEnd_ev_rpow_log_le (a := 1 / 10) (b := 1 / 5) (by norm_num) 7).exists⟩

/-! ### (2) The absorption and regime lemmas at the exponents the endpoint chooses at the data

`ε₀' = 1/10`, `ε₁ = εq = ε₀'/8 = 1/80`, `D'' = Ddz = 61`, `D' = D'' + 1`, `D_Y = D_t = k + 2 = 5`,
`cA = 2^k = 8`, `κ' = κz`, `τ_R = 1/2`; each statement is unfolded at one size index. -/

/-- (H1) at the data, for every `C`. -/
theorem H1_instance (C : ℝ) : ∃ n : ℕ, C * ((szB.size n : ℕ) : ℝ) ^ (1 / 80 : ℝ) ≤
    ((szB.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) / 6 :=
  (nzEnd_ev_H1 szB szB_tendsto (C := C) (ε₁ := 1 / 80) (ε₀ := 1 / 10) (by norm_num)).exists

/-- (H2) at the data (`cA = 2^3`). -/
theorem H2_instance : ∃ n : ℕ, Cz * (2 : ℝ) ^ 3 * ((3 : ℕ) : ℝ) *
    (((szB.size n : ℕ) : ℝ) ^ (1 / 80 : ℝ)) ^ 2 *
      ((mE (Einst n)).im⁻¹ * Real.log ((szB.size n : ℕ) : ℝ)) ≤
        ((szB.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) / 6 :=
  (nzEnd_ev_H2 szB szB_tendsto 3 κz_pos hκm_B (C := Cz) (cA := (2 : ℝ) ^ 3) (ε₁ := 1 / 80)
    (ε₀ := 1 / 10) Cz_pos.le (by norm_num) (by norm_num)).exists

/-- (H3) at the data. -/
theorem H3_instance : ∃ n : ℕ, ((szB.size n : ℕ) : ℝ) ^ (1 / 80 : ℝ) *
    (Cz * ((szB.size n : ℕ) : ℝ) ^ (1 / 80 : ℝ) *
      Real.sqrt (((3 : ℕ) : ℝ) * ((mE (Einst n)).im⁻¹ * Real.log ((szB.size n : ℕ) : ℝ)))) ≤
        ((szB.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) / 12 :=
  (nzEnd_ev_H3 szB szB_tendsto 3 κz_pos hκm_B (C := Cz) (εq := 1 / 80) (ε₁ := 1 / 80)
    (ε₀ := 1 / 10) Cz_pos.le (by norm_num)).exists

/-- (H4) at the data (`D'' = Ddz = 61`: `εq + k - 𝔠 D''/2 = 1/80 + 3 - 61/12 < 1/10`). -/
theorem H4_instance : ∃ n : ℕ, ((szB.size n : ℕ) : ℝ) ^ (1 / 80 : ℝ) *
    (((szB.size n : ℕ) : ℝ) ^ 3 * (Cz * Real.sqrt (((3 : ℕ) : ℝ) *
      ((szB.W n : ℕ) : ℝ) ^ (-Ddz)))) ≤ ((szB.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) / 12 :=
  (nzEnd_ev_H4 szB szB_tendsto szB_bandwidth 3 (C := Cz) (D'' := Ddz) (εq := 1 / 80)
    (ε₀ := 1 / 10) Cz_pos.le (by norm_num [Ddz]) (by norm_num [Ddz])).exists

/-- (H5) at the data (`D_Y = k + 2`: `k - D_Y = -2 < 1/10`). -/
theorem H5_instance : ∃ n : ℕ, 1 * ((szB.size n : ℕ) : ℝ) ^ 3 *
    ((szB.size n : ℕ) : ℝ) ^ (-(((3 : ℕ) : ℝ) + 2)) ≤ ((szB.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) / 6 :=
  (nzEnd_ev_H56 szB szB_tendsto 3 1 (D := ((3 : ℕ) : ℝ) + 2) (ε₀ := 1 / 10)
    (by norm_num)).exists

/-- (H6) at the data (`cA = 2^3`, `D_t = k + 2`). -/
theorem H6_instance : ∃ n : ℕ, (2 : ℝ) ^ 3 * ((szB.size n : ℕ) : ℝ) ^ 3 *
    ((szB.size n : ℕ) : ℝ) ^ (-(((3 : ℕ) : ℝ) + 2)) ≤ ((szB.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) / 6 :=
  (nzEnd_ev_H56 szB szB_tendsto 3 ((2 : ℝ) ^ 3) (D := ((3 : ℕ) : ℝ) + 2) (ε₀ := 1 / 10)
    (by norm_num)).exists

/-- The union bound over the `≤ 4^k` pairs `(σ, A)` at `k = 3`, `D₁ = 1`. -/
theorem union_instance : ∃ n : ℕ, (4 : ℝ) ^ 3 * ((szB.size n : ℕ) : ℝ) ^ (-((1 : ℝ) + 1)) ≤
    ((szB.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) :=
  (nzEnd_ev_union szB szB_tendsto ((4 : ℝ) ^ 3) 1).exists

/-- The range condition passes to a smaller exponent (`τ_R = 1/4 ≤ τ = 1/2`) and an earlier time
(`v = 15/16 ≤ t = 31/32`). -/
theorem rangeCond_mono_instance : szB.RangeCond (1 / 4) vC :=
  nzEnd_rangeCond_mono szB (τ := 1 / 2) (by norm_num) vC_le_tB rangeCond_tB

/-- (`hη`) at the data. -/
theorem hη_instance : ∃ n : ℕ, (etaT (Einst n) (vB n))⁻¹ ≤ ((szB.size n : ℕ) : ℝ) :=
  (nzEnd_ev_hη szB szB_tendsto κz_pos hκm_B (τR := 1 / 2) (by norm_num) rangeCond_tB).exists

/-- (`hδ`, the shift hypothesis) at the data (`D'' = Ddz`, `C_K = D'' + 2k + 5`, grid `KB C_K`). -/
theorem hδ_instance : ∃ n : ℕ, ∀ j < KB (Ddz + 2 * ((3 : ℕ) : ℝ) + 5) n,
    ((szB.W n : ℕ) : ℝ) ^ (-(Ddz + 1)) + eeShiftErrN 3 (szB.L n) (szB.W n) (Einst n) 3
      (gridTime sB vB (KB (Ddz + 2 * ((3 : ℕ) : ℝ) + 5)) n j)
      (gridTime sB vB (KB (Ddz + 2 * ((3 : ℕ) : ℝ) + 5)) n (j + 1)) ≤
        ((szB.W n : ℕ) : ℝ) ^ (-Ddz) :=
  (nzEnd_ev_hδ szB (by norm_num) szB_tendsto (𝔠 := 1 / 6) (by norm_num) szB_bandwidth 3
    (E := Einst) (s := sB) (v := vB) (K := KB (Ddz + 2 * ((3 : ℕ) : ℝ) + 5)) Einst_abs_lt
    sB_nonneg sB_le_vB vB_lt_one (KB_ne_zero _)
    (nzEnd_ev_hη szB szB_tendsto κz_pos hκm_B (τR := 1 / 2) (by norm_num) rangeCond_tB)
    (by norm_num [Ddz]) le_rfl (Eventually.of_forall (KB_low _))).exists

/-- The grid facts `Δ ≤ N^{-C_K}` and `KΔ ≤ 1` at the data (one size index, every `C_K`). -/
theorem grid_instance (C_K : ℝ) : ∃ n : ℕ, gridStep sB vB (KB C_K) n ≤
    ((szB.size n : ℕ) : ℝ) ^ (-C_K) ∧ (KB C_K n : ℝ) * gridStep sB vB (KB C_K) n ≤ 1 := by
  refine ⟨0, nzEnd_step_le szB (KB_low C_K 0) (by norm_num [vB, sB]),
    nzEnd_K_mul_step (KB_ne_zero C_K 0) (by norm_num [vB, sB])⟩

/-- The operator bound of `lem:sum_decay_nonzero` (`nzUgen_holds`) at every pair of grid times
`u_i ≤ u_m` of the case-(ii) window (`1 - g²/L² = 15/16 ≤ s ≤ u_i ≤ u_m < 1`), every `A ⊇ I_diff(σ)`:
the per-`n` hypotheses of `nzUgen_holds` of the endpoint, discharged at the data. -/
theorem hop_instance (C_K : ℝ) (n : ℕ) (A : Finset (Fin 3)) (hA : STIdiff sig3 ⊆ A) :
    ∀ i m, i ≤ m → m ≤ KB C_K n → ∀ X : (Fin 3 → Zd 3 (szB.L n)) → ℂ,
      ‖zeroModeSet 3 (szB.L n) A (Ugen 3 (szB.L n) (szB.lam n) (Einst n) sig3
        (gridTime sB vB (KB C_K) n i) (gridTime sB vB (KB C_K) n m) X)‖ ≤ Cz * ‖X‖ := by
  intro i m him hmK X
  have hsu : ∀ i, sB n ≤ gridTime sB vB (KB C_K) n i := fun i => by
    have h := ST_gridTime_mono sB vB (KB C_K) n (sB_le_vB n) (Nat.zero_le i)
    rwa [ST_gridTime_zero] at h
  have hu1 : gridTime sB vB (KB C_K) n m < 1 :=
    (nzEnd_gridTime_le (sB_le_vB n) (KB_ne_zero C_K n) hmK).trans_lt (vB_lt_one n)
  have hcase : 1 - sB n ≤ szB.lam n ^ 2 / ((szB.L n : ℕ) : ℝ) ^ 2 := szB_caseII n
  exact ((Classical.choose_spec Cz_ex).2 (szB.L n) (szB.three_le_L n) (szB.lam n) (Einst n)
    (by norm_num [szB]) (by norm_num [szB]) (Einst_abs_lt n) (hκm_B n) _ _
    (nzEnd_gridTime_nonneg (sB_nonneg n) (sB_le_vB n) i) ((sub_le_comm.1 hcase).trans (hsu i))
    (ST_gridTime_mono sB vB (KB C_K) n (sB_le_vB n) him) hu1 sig3 A hA).1 X

/-! ### (3) The assembly at the exit time at the data

`k = 3`, `σ = sig3`, `A ⊇ I_diff(σ) = {0, 1}` (`A = {0, 1}` and `A = univ` below), levels
`(Γ, Λ, Φc, Φ₁, Φ₂, Φ₃) = (N^{1/80}, 1, 1, 1, 1, 1)`, `Λg = 10`, `κ' = κz`, `τ' = 1`, `D'' = Ddz = 61`,
`D' = D'' + 1`, `D_Y = 5`, `τ_K = 1`, `ε_q = 1/80`, `D₁ = 2` (`= D₁ + 1` of the endpoint at `D₁ = 1`), the `Y`-moment
constant `C_P` of `yMomentsUnifN`, `C_K = 100 + 2 C_P`, the grid `KB C_K`. -/

/-- The loss level `Γ = N^{1/80}` of the instances. -/
abbrev Γz : ℕ → ℝ := fun n => ((szB.size n : ℕ) : ℝ) ^ (1 / 80 : ℝ)

/-- **The assembly at the exit time `nqLinExitTauN`** at the data: at one size index, on the strict window
`Δ > 0`, there is an event of probability `≥ 1 - N^{-2}` on which the terminal bound
`‖(Q^{(A)} A_K)(a)‖ ≤ assembledRHSNZN` holds as soon as the walk stays in `GoodSetN ∩ GoodLinN`
(`STKbound` by `stKbound_holds`, the shift hypothesis `hδ` by `nzEnd_ev_hδ`). -/
theorem assembly_instance (A : Finset (Fin 3)) (hA : STIdiff sig3 ⊆ A) :
    ∃ C_P : ℝ, 0 ≤ C_P ∧ ∃ n : ℕ, 0 < gridStep sB vB (KB (100 + 2 * C_P)) n ∧
      ∃ G : Set (PathΩ szB), (pathP szB).real Gᶜ ≤ ((szB.size n : ℕ) : ℝ) ^ (-(2 : ℝ)) ∧
        ∀ ω ∈ G,
          (∀ j ≤ KB (100 + 2 * C_P) n, pathH szB sB vB (KB (100 + 2 * C_P)) n j ω ∈
            szB.GoodSetN n (Einst n) (gridTime sB vB (KB (100 + 2 * C_P)) n j) 3 (Γz n) 1 1 1
                (Ddz + 1) ∩
              GoodLinN szB n (Einst n) (gridTime sB vB (KB (100 + 2 * C_P)) n j) 3 (Γz n) 1 1 1) →
          ∀ a : Fin 3 → Zd 3 (szB.L n),
            ‖zeroModeSet 3 (szB.L n) A (AvecN szB Einst sB vB (KB (100 + 2 * C_P)) n
                (KB (100 + 2 * C_P) n) sig3 ω) a‖ ≤
              assembledRHSNZN szB Einst sB vB (KB (100 + 2 * C_P)) n 3 Cz (2 ^ 3) Γz oneL oneL oneL
                oneL Ddz 5 1 (1 / 80)
                (Finset.univ.sup' Finset.univ_nonempty fun b =>
                  ‖zeroModeSet 3 (szB.L n) A (AvecN szB Einst sB vB (KB (100 + 2 * C_P)) n 0 sig3 ω)
                    b‖) := by
  obtain ⟨C_P, hCP0, hYm⟩ := nzEnd_yMomentsMax szB (κ := 1) (τR := 1 / 2) (E := Einst) (s := sB)
    (v := vB) one_pos hE_B sB_nonneg sB_le_vB vB_lt_one szB_tendsto rangeCond_tB 3
  refine ⟨C_P, hCP0, ?_⟩
  have hKN : ∀ᶠ n : ℕ in atTop, ((szB.size n : ℕ) : ℝ) ^ (100 + 2 * C_P) ≤
      (KB (100 + 2 * C_P) n : ℝ) := Eventually.of_forall (KB_low _)
  have hKU : ∀ᶠ n : ℕ in atTop, KB (100 + 2 * C_P) n ≤
      ⌈((szB.size n : ℕ) : ℝ) ^ (100 + 2 * C_P)⌉₊ := Eventually.of_forall (KB_up _)
  have hKb : szB.STKbound Einst := stKbound_holds szB (by norm_num) one_pos
    (by norm_num : (0 : ℝ) < 10) szB_tendsto (Eventually.of_forall hE_B) hlam_B
  have hη := nzEnd_ev_hη szB szB_tendsto κz_pos hκm_B (τR := 1 / 2) (by norm_num) rangeCond_tB
  have hδ := nzEnd_ev_hδ szB (by norm_num) szB_tendsto (𝔠 := 1 / 6) (by norm_num) szB_bandwidth 3
    (D'' := Ddz) (C_K := 100 + 2 * C_P) (E := Einst) (s := sB) (v := vB)
    (K := KB (100 + 2 * C_P)) Einst_abs_lt sB_nonneg sB_le_vB vB_lt_one (KB_ne_zero _) hη
    (by norm_num [Ddz]) (by norm_num [Ddz]; linarith) hKN
  have hAsm := nzEnd_assembly szB (κ := 1) (E := Einst) (s := sB) (v := vB)
    (K := KB (100 + 2 * C_P)) 3 (by norm_num) one_pos hE_B sB_nonneg sB_le_vB vB_lt_one
    (KB_ne_zero _) szB_tendsto hKb szB_caseII Γz oneL oneL oneL oneL oneL
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => by norm_num) (fun _ => by norm_num)
    (Λg := 10) (κ' := κz) (C := Cz) (τ' := 1) (D' := Ddz + 1) (D'' := Ddz) (D_Y := 5) (τK := 1)
    (εq := 1 / 80) (D₁ := 2) (C_P := C_P) (C_K := 100 + 2 * C_P) κz_pos hκm_B Cz_pos
    (Classical.choose_spec Cz_ex).2 (by norm_num) one_pos (by linarith)
    (by norm_num [Ddz]; linarith) hKN hKU (hYm _ (KB_ne_zero _)) hlam_B hδ
  obtain ⟨n, hn⟩ := hAsm.exists
  exact ⟨n, (window_nondegenerate (100 + 2 * C_P) n).2,
    hn sig3 A hA (window_nondegenerate (100 + 2 * C_P) n).1⟩

/-- The assembly at the data for `A = I_diff(σ) = {0, 1}`. -/
example := assembly_instance (STIdiff sig3) (Finset.Subset.refl _)

/-- The assembly at the data for `A = univ ⊇ I_diff(σ)`. -/
example := assembly_instance Finset.univ (Finset.subset_univ _)

/-! ### (4) `nzGridEndN` at the data, every premise discharged -/

/-- **`nzGridEndN` at the data, non-collapsed window** (`k ≥ 2` arbitrary; no hypothesis is left:
`STKbound` is internal, the good-walk and initial hypotheses stay in the conclusion).  The theorem is
applied at `sz = szB`, `κ = 1`, `𝔠 = 1/6`, `τ = 1/2`, `𝔡 = 1/10`, `E = Einst`, `(s, t) = (15/16, 31/32)`
(`szB_caseII`, `rangeCond_tB`), levels `Λ = 1`, `Φ₁ = Φ₂ = Φ₃ = Φc = 1`, `v = vB ≡ 31/32`
(`s = 15/16 < v`, `Δ > 0`: `window_nondegenerate`), `ε₀ = 1/10`, `D₁ = 1`; the conclusion is unfolded at the
grid `KB C_K` (`N^{C_K} ≤ K_n ≤ ⌈N^{C_K}⌉`) for the exponents the theorem produces, at one size index; every
`σ` and every `A ⊇ I_diff(σ)`. -/
theorem nzEnd_instance (k : ℕ) (hk : 2 ≤ k) :
    ∃ ε₁ τ' D' C_K : ℝ, 0 < ε₁ ∧ 0 < τ' ∧ 0 < D' ∧ 0 ≤ C_K ∧
      ∃ n : ℕ, ∃ G : Set (PathΩ szB), (pathP szB).real Gᶜ ≤ ((szB.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ∧
        ∀ ω ∈ G,
          (∀ j ≤ KB C_K n, pathH szB sB vB (KB C_K) n j ω ∈
            szB.GoodSetN n (Einst n) (gridTime sB vB (KB C_K) n j) k
                (((szB.size n : ℕ) : ℝ) ^ ε₁) 1 1 τ' D' ∩
              GoodLinN szB n (Einst n) (gridTime sB vB (KB C_K) n j) k
                (((szB.size n : ℕ) : ℝ) ^ ε₁) 1 1 1) →
          (∀ (σ : Fin k → Bool) (A : Finset (Fin k)), STIdiff σ ⊆ A →
            ∀ a : Fin k → Zd 3 (szB.L n),
              ‖zeroModeSet 3 (szB.L n) A
                  (fun b : Fin k → Zd 3 (szB.L n) =>
                    szB.STLKM n (Einst n) (sB n) (pathH szB sB vB (KB C_K) n 0 ω) σ b) a‖ ≤
                ((szB.size n : ℕ) : ℝ) ^ ε₁ * (szB.Bctl n (sB n)) ^ k) →
          ∀ (σ : Fin k → Bool) (A : Finset (Fin k)), STIdiff σ ⊆ A →
            ∀ a : Fin k → Zd 3 (szB.L n),
              ‖zeroModeSet 3 (szB.L n) A
                  (fun b : Fin k → Zd 3 (szB.L n) =>
                    szB.STLKM n (Einst n) (vB n) (pathH szB sB vB (KB C_K) n (KB C_K n) ω) σ b) a‖ ≤
                ((szB.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * ((1 : ℝ) ^ ((1 : ℝ) / 2) + 1 + 1 + 1) *
                  (szB.Bctl n (vB n)) ^ k := by
  obtain ⟨ε₁, τ', D', C_K, h1, h2, h3, h4, hend⟩ := nzGridEndN szB 1 (1 / 6) (1 / 2) (1 / 10)
    Einst sB tB (by norm_num) one_pos (by norm_num) (by norm_num) (by norm_num) szB_tendsto
    szB_bandwidth szB_WO hE_B sB_nonneg sB_le_tB tB_lt_one szB_caseII rangeCond_tB k hk
    oneL oneL oneL oneL (fun _ => by norm_num) (Eventually.of_forall fun _ => le_rfl)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) vB sB_le_vB vB_le_tB
    (1 / 10) (by norm_num) 1 one_pos
  refine ⟨ε₁, τ', D', C_K, h1, h2, h3, h4, ?_⟩
  obtain ⟨n, G, hG, hGb⟩ := (hend oneL (KB C_K) (KB_ne_zero C_K)
    (Eventually.of_forall (KB_low C_K)) (Eventually.of_forall (KB_up C_K))).exists
  exact ⟨n, G, hG, hGb⟩

/-- **`nzGridEndN` at the data, collapsed window** `v = s = 15/16` (`Δ = 0`: `window_collapsed`):
the same statement with `v = vC`; here `G = univ` and the conclusion is the initial bound. -/
theorem nzEnd_instance_collapsed (k : ℕ) (hk : 2 ≤ k) :
    ∃ ε₁ τ' D' C_K : ℝ, 0 < ε₁ ∧ 0 < τ' ∧ 0 < D' ∧ 0 ≤ C_K ∧
      ∃ n : ℕ, ∃ G : Set (PathΩ szB), (pathP szB).real Gᶜ ≤ ((szB.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ∧
        ∀ ω ∈ G,
          (∀ j ≤ KB C_K n, pathH szB sB vC (KB C_K) n j ω ∈
            szB.GoodSetN n (Einst n) (gridTime sB vC (KB C_K) n j) k
                (((szB.size n : ℕ) : ℝ) ^ ε₁) 1 1 τ' D' ∩
              GoodLinN szB n (Einst n) (gridTime sB vC (KB C_K) n j) k
                (((szB.size n : ℕ) : ℝ) ^ ε₁) 1 1 1) →
          (∀ (σ : Fin k → Bool) (A : Finset (Fin k)), STIdiff σ ⊆ A →
            ∀ a : Fin k → Zd 3 (szB.L n),
              ‖zeroModeSet 3 (szB.L n) A
                  (fun b : Fin k → Zd 3 (szB.L n) =>
                    szB.STLKM n (Einst n) (sB n) (pathH szB sB vC (KB C_K) n 0 ω) σ b) a‖ ≤
                ((szB.size n : ℕ) : ℝ) ^ ε₁ * (szB.Bctl n (sB n)) ^ k) →
          ∀ (σ : Fin k → Bool) (A : Finset (Fin k)), STIdiff σ ⊆ A →
            ∀ a : Fin k → Zd 3 (szB.L n),
              ‖zeroModeSet 3 (szB.L n) A
                  (fun b : Fin k → Zd 3 (szB.L n) =>
                    szB.STLKM n (Einst n) (vC n) (pathH szB sB vC (KB C_K) n (KB C_K n) ω) σ b) a‖ ≤
                ((szB.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * ((1 : ℝ) ^ ((1 : ℝ) / 2) + 1 + 1 + 1) *
                  (szB.Bctl n (vC n)) ^ k := by
  obtain ⟨ε₁, τ', D', C_K, h1, h2, h3, h4, hend⟩ := nzGridEndN szB 1 (1 / 6) (1 / 2) (1 / 10)
    Einst sB tB (by norm_num) one_pos (by norm_num) (by norm_num) (by norm_num) szB_tendsto
    szB_bandwidth szB_WO hE_B sB_nonneg sB_le_tB tB_lt_one szB_caseII rangeCond_tB k hk
    oneL oneL oneL oneL (fun _ => by norm_num) (Eventually.of_forall fun _ => le_rfl)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) vC sB_le_vC vC_le_tB
    (1 / 10) (by norm_num) 1 one_pos
  refine ⟨ε₁, τ', D', C_K, h1, h2, h3, h4, ?_⟩
  obtain ⟨n, G, hG, hGb⟩ := (hend oneL (KB C_K) (KB_ne_zero C_K)
    (Eventually.of_forall (KB_low C_K)) (Eventually.of_forall (KB_up C_K))).exists
  exact ⟨n, G, hG, hGb⟩

/-- The instance at `k = 2` (no `l ∈ [3,k]`; `A ⊆ Fin 2`). -/
example := nzEnd_instance 2 le_rfl

/-- The instance at `k = 3`. -/
example := nzEnd_instance 3 (by norm_num)

/-- The instance at `k = 4`. -/
example := nzEnd_instance 4 (by norm_num)

/-- The collapsed-window instance at `k = 3`. -/
example := nzEnd_instance_collapsed 3 (by norm_num)

end QtNonzeroEndInst
end RBM.Ind

end
