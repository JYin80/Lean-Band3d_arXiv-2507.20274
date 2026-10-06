/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.QEndA
import RBM3D.Induction.QBudgetB
import RBM3D.Induction.QGridB
import RBM3D.Induction.NQBudget
import RBM3D.Induction.GridAssemblyN
import RBM3D.Loop.KLFinal

/-!
# S3-18a2 (ticket T2302): the alternating grid endpoint `altGridEndQN`

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`): `lem:STOeq_Qt` `3_5:1362-1378`, the alternating case
`3_5:1676-1714` (`(y27kasdfg)`, `(A4)`, `(A5)` `3_5:1692-1706`), `(normQA)` `3_5:1284-1289`.  Composition, no new
mathematics (DECISIONS §62 (2)/(4), §83, §95 (3), §98 (1), §105 (1)): the merged `assembledN` at the alternating exit family
`altExitTauN` with the fields of `QEndA` (T2294), the bridge C1b and `budgetAltQN` at `ε₀/2`, the de-`𝒬` step `altEnd_unQ` at
`v`, the per-`n` level split, the `lam` patch for `yMomentsQUnifN`, the collapsed window and the union bound over the
alternating `σ`.  The statement is the pin `T2302_altGridEndQN` of `docs/tickets/checks/T2302-check.lean` (= `T2294_altGridEndQN_shape`),
unchanged.

## What is here (namespace `RBM.Ind`; every helper is `private` with the prefix `altGrid_`)

* §0-§1 copies of the private helpers of `NQEndLin` (`:56`, `:127-148`, `:446-646`, `:722-759`, `:967-1023`): the asymptotic
  absorption, `W ≤ N`, `W ≥ N^𝔠 → ∞`, `η_v⁻¹ ≤ N`, the grid step, the shift hypothesis `hδ`, the collapsed window, the range
  condition, the union bound;
* §2 the `lam` patch (paper-delta candidate `T2302c`): the family `altGrid_mol` (explicit mollifier if `0 < lam n`, else the delta
  family on constant labels), `STMollifierProps` at every `n`, and the `Y`-moment constant `altGrid_yMomentsMax` over all signs;
* §3 the level split (`T2302b`): the crude sup `‖(𝓛-𝒦)^{(k)}‖ ≤ N^{k+2}` on the good walk (`STmaxLKM_crudeN`, the `𝒦` envelope
  `M_K = N η_v^{-k}`), `B_u ≤ 2 N`, and on the small levels `𝔏 < N^{2k+2}` the quantities of the assembly `≤ N^{8k+7}`;
* §4 `altGrid_assembly` (per alternating `σ`): the bundle `GridAssemblyHypN` at `altExitTauN`, `assembledN`, the bridge C1b;
* §5 the exponent bookkeeping `AltGridArith` and helpers; §6 **`altGridEndQN`**;
* §7 compiled nonempty instances (namespace `RBM.Ind.QEndGridInst`).

Constants of the proof (fixed order): `Λg = 𝔡⁻¹`, `κ' = min κ (4/5)`, `KL = 1/𝔠`, `C₁ = (1 + 40 d(m+1)) 6^{d(m+1)}`, `C₄`, `C_n`,
`ε₀' = min ε₀ 1`, `e₂ = ε₀'/2` (the budget runs at `e₂`), `ε = min (e₂/(8 max(C₄,C_n))) (1/2)`, `ε' = ε/2`,
`τ' = min (ε/4) (e₂/(40 d m))`, `ε₁ = εq = e₂/40`, `τ_N = e₂/8`, `D'' = 2C_n + 2 + 2C₄ + k + (4k+1)/𝔠`, `D' = D'' + 2`,
`D_c = D'' + 1`, `D_Y = D_t = k + 1`, `C_K = D₁ + 2C_P^* + 8k + 20 + D''`, `C₀ = (8k+8)/𝔠` (`k = m + 2`); the `ν` of the
`hY` set is `N^{ε₁}` (`W^{τ'dm} ≤ N^{ε₁}`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-! ## 0. Asymptotic helper (copy of `NQEndLin.lean:56`) -/

/-- `C · x^a ≤ x^b` for all large real `x` when `a < b` (RBM2D `NonAltEnd_ev_rpow_le`, `NonAltEnd:60`). -/
private theorem altGrid_ev_rpow_le {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, C * x ^ a ≤ x ^ b := by
  have ht : Tendsto (fun x : ℝ => x ^ (b - a)) atTop atTop := tendsto_rpow_atTop (sub_pos.mpr hab)
  filter_upwards [ht.eventually_ge_atTop C, eventually_gt_atTop 0] with x hx hx0
  have h1 : x ^ b = x ^ (b - a) * x ^ a := by
    rw [← Real.rpow_add hx0]; ring_nf
  rw [h1]
  exact mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hx0.le _)

/-! ## 1. Elementary facts on the sizes and the grid (copies of `NQEndLin.lean:127-148`, `:446-646`, `:722-759`,
`:967-1023`) -/

section Facts

variable {d : ℕ} (sz : Sizes d)

private theorem altGrid_one_le_size (n : ℕ) : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  exact_mod_cast sz.one_le_size n

/-- `W^d L^d = N` (the private `gridEnv_size_cast` of `GridEnvelopeN`). -/
private theorem altGrid_size_cast (n : ℕ) :
    (sz.W n : ℝ) ^ d * (sz.L n : ℝ) ^ d = ((sz.size n : ℕ) : ℝ) := by
  have : ((sz.size n : ℕ) : ℝ) = (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) := rfl
  rw [this]
  push_cast
  ring

/-- **Crude `W ≤ N`** (`W ≤ W^d ≤ (W L)^d = N`, `d ≥ 1`): the bound for the positive powers of `W`. -/
private theorem altGrid_W_le_size (hd : 1 ≤ d) (n : ℕ) :
    ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  have h1 : sz.W n ≤ (sz.W n) ^ d := Nat.le_self_pow (by omega) _
  have h2 : (sz.W n) ^ d ≤ sz.size n := by
    unfold Sizes.size
    exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by have := sz.three_le_L n; omega)) d
  exact_mod_cast h1.trans h2

end Facts

section Regime

variable {d : ℕ} (sz : Sizes d)

/-- `X ≤ W^a` eventually for `a > 0` (`W ≥ N^𝔠 → ∞`): the source of `1 < W`, `4 ≤ W^ε`,
`d W^{τ'} ≤ W^ε`, `2 ≤ W`. -/
private theorem altGrid_ev_W_rpow_ge (hsize : sz.SizeTendsto) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠)
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
private theorem altGrid_step_le {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {C_K : ℝ}
    (hK : ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) (hvs : v n - s n ≤ 1) :
    gridStep s v K n ≤ ((sz.size n : ℕ) : ℝ) ^ (-C_K) := by
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := lt_of_lt_of_le one_pos (altGrid_one_le_size sz n)
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
private theorem altGrid_K_mul_step {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hK : K n ≠ 0)
    (hvs : v n - s n ≤ 1) : (K n : ℝ) * gridStep s v K n ≤ 1 := by
  have hK' : (K n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK
  unfold gridStep
  rw [mul_div_cancel₀ _ hK']
  exact hvs

/-- The one-step increment of the grid times is `Δ`. -/
private theorem altGrid_gridTime_succ_sub (s v : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) :
    gridTime s v K n (j + 1) - gridTime s v K n j = gridStep s v K n := by
  unfold gridTime; push_cast; ring

/-- `η_u⁻¹ ≤ N^{1-τ}/κ'` for `u ≤ t`, `κ' ≤ Im m`, under the range condition
`N^{-1+τ} ≤ 1 - t` (RBM2D `NonAltEnd_etaT_inv_le`, `NonAltEnd:593`, with `κ'` for `c₀`). -/
private theorem altGrid_etaT_inv_le {κ' E u t τR N : ℝ} (hκ' : 0 < κ') (hκm : κ' ≤ (mE E).im)
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
private theorem altGrid_ev_hη (hsize : sz.SizeTendsto) {κ' τR : ℝ} (hκ' : 0 < κ') {E v : ℕ → ℝ}
    (hκm : ∀ n, κ' ≤ (mE (E n)).im) (hτR : 0 < τR) (hrange : sz.RangeCond τR v) :
    ∀ᶠ n : ℕ in atTop, (etaT (E n) (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
  filter_upwards [hrange, hsize.eventually (altGrid_ev_rpow_le (a := 0) hτR κ'⁻¹),
    hsize.eventually_ge_atTop 1] with n hR hbig hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have h := altGrid_etaT_inv_le hκ' (hκm n) le_rfl hN0 hR
  rw [Real.rpow_zero, mul_one] at hbig
  calc (etaT (E n) (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (1 - τR) / κ' := h
    _ = ((sz.size n : ℕ) : ℝ) ^ (1 - τR) * κ'⁻¹ := div_eq_mul_inv _ _
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (1 - τR) * ((sz.size n : ℕ) : ℝ) ^ τR :=
        mul_le_mul_of_nonneg_left hbig (Real.rpow_nonneg hN0.le _)
    _ = ((sz.size n : ℕ) : ℝ) := by rw [← Real.rpow_add hN0]; simp

/-- (`hΔη`) `Δ η_v⁻¹ ≤ 1` for `C_K ≥ 1`, `η_v⁻¹ ≤ N` (RBM2D `NonAltEnd_hΔN`, `NonAltEnd:667`). -/
private theorem altGrid_hΔη {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {C_K η : ℝ} (hC : 1 ≤ C_K)
    (hK : ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) (hvs : v n - s n ≤ 1) (hη0 : 0 ≤ η⁻¹)
    (hη : η⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) : gridStep s v K n * η⁻¹ ≤ 1 := by
  have hN1 := altGrid_one_le_size sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := lt_of_lt_of_le one_pos hN1
  have h := altGrid_step_le sz hK hvs
  calc gridStep s v K n * η⁻¹
      ≤ ((sz.size n : ℕ) : ℝ) ^ (-C_K) * ((sz.size n : ℕ) : ℝ) :=
        mul_le_mul h hη hη0 (Real.rpow_nonneg hN0.le _)
    _ = ((sz.size n : ℕ) : ℝ) ^ (1 - C_K) := by
        rw [show (1 - C_K) = 1 + (-C_K) by ring, Real.rpow_add hN0, Real.rpow_one]; ring
    _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)

/-- The shift error with `η_{u'}⁻¹ ≤ B`: `eeShiftErrN ≤ W^d k L^d (2k+2) B^{2k+3} (u' - u)`
(RBM2D `NonAltEnd_eeShiftErr_le`, `NonAltEnd:694`, with `W^d`, `L^d`). -/
private theorem altGrid_eeShiftErrN_le {d L W : ℕ} (hW : 1 ≤ W) {E : ℝ} (k : ℕ) {u u' B : ℝ}
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
private theorem altGrid_ev_hδ (hd : 1 ≤ d) (hsize : sz.SizeTendsto) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠)
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
  filter_upwards [hη, hKN, altGrid_ev_W_rpow_ge sz hsize h𝔠 hband one_pos 2,
    hsize.eventually_ge_atTop (2 * A), hsize.eventually_ge_atTop 1] with n hηn hKNn hW2 hNA hN1
  intro j hj
  rw [Real.rpow_one] at hW2
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hWN : ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := altGrid_W_le_size sz hd n
  have hvs : v n - s n ≤ 1 := by linarith [hv1 n, hs0 n]
  have hΔ : gridStep s v K n ≤ ((sz.size n : ℕ) : ℝ) ^ (-C_K) := altGrid_step_le sz hKNn hvs
  have hΔ0 : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n (hsv n)
  have hu'v : gridTime s v K n (j + 1) ≤ v n := by
    have h := ST_gridTime_mono s v K n (hsv n) (show j + 1 ≤ K n by omega)
    rwa [gridTime_last s v K n (hK0 n)] at h
  have hdiff := altGrid_gridTime_succ_sub s v K n j
  have hEn := hE n
  have hηv : 0 < etaT (E n) (v n) := etaT_pos hEn (hv1 n)
  have hη' : 0 < etaT (E n) (gridTime s v K n (j + 1)) := etaT_pos hEn (hu'v.trans_lt (hv1 n))
  have hηle : (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
    refine le_trans (inv_anti₀ hηv ?_) hηn
    unfold etaT
    exact mul_le_mul_of_nonneg_right (by linarith) (mE_im_pos hEn).le
  have hη0 : 0 ≤ (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ := inv_nonneg.2 hη'.le
  have hee := altGrid_eeShiftErrN_le (d := d) (L := sz.L n) (W := sz.W n) (sz.W_pos n) k
    (E := E n) (u := gridTime s v K n j) (u' := gridTime s v K n (j + 1)) hη0 hηle
    (by rw [hdiff]; exact hΔ0)
  rw [hdiff] at hee
  have hsz := altGrid_size_cast sz n
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

section Grid

variable {d : ℕ} (sz : Sizes d)

/-- `0 ≤ u_i` on the grid `0 ≤ s_n ≤ v_n`. -/
private theorem altGrid_gridTime_nonneg {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hs0 : 0 ≤ s n)
    (hsv : s n ≤ v n) (i : ℕ) : 0 ≤ gridTime s v K n i := by
  have h := ST_gridTime_mono s v K n hsv (Nat.zero_le i)
  rw [ST_gridTime_zero] at h
  linarith

/-- `u_i ≤ v_n` for `i ≤ K_n`, `K_n ≠ 0`. -/
private theorem altGrid_gridTime_le {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hsv : s n ≤ v n)
    (hK : K n ≠ 0) {i : ℕ} (hi : i ≤ K n) : gridTime s v K n i ≤ v n :=
  (ST_gridTime_mono s v K n hsv hi).trans_eq (gridTime_last s v K n hK)

/-- The step error of `gridDriftN` is nonnegative (RBM2D `NonAltEnd_stepErrN_nonneg`,
`NonAltEnd:817`, with `W^d` in place of `W²`). -/
private theorem altGrid_stepErrN_nonneg {d L W : ℕ} {E u v Δ Bk : ℝ} {k : ℕ} (hE : |E| < 2)
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

/-- If `v_n = s_n` the grid walk does not move: `Δ = 0` and every `H_j = H_0` (RBM2D
`NonAltEnd_pathH_collapse`, `NonAltEnd:1014`). -/
private theorem altGrid_pathH_collapse {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hsv : s n = v n) (j : ℕ)
    (ω : PathΩ sz) : pathH sz s v K n j ω = pathH sz s v K n 0 ω := by
  have hΔ : gridStep s v K n = 0 := by unfold gridStep; rw [← hsv]; simp
  unfold pathH
  rw [hΔ]
  simp

/-- The range condition passes to a smaller exponent and an earlier time (RBM2D
`NonAltEnd_rangeCond_mono`, `NonAltEnd:1059`). -/
private theorem altGrid_rangeCond_mono {τ τR : ℝ} {t v : ℕ → ℝ} (hτ : τR ≤ τ)
    (hvt : ∀ n, v n ≤ t n) (h : sz.RangeCond τ t) : sz.RangeCond τR v := by
  filter_upwards [h] with n hn
  calc ((sz.size n : ℕ) : ℝ) ^ (-1 + τR) ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 + τ) :=
        Real.rpow_le_rpow_of_exponent_le (altGrid_one_le_size sz n) (by linarith)
    _ ≤ 1 - t n := hn
    _ ≤ 1 - v n := by linarith [hvt n]

/-- The union bound over the sign vectors: `2^k N^{-(D+1)} ≤ N^{-D}` eventually (RBM2D
`NonAltEnd_ev_union`, `NonAltEnd:1068`). -/
private theorem altGrid_ev_union (hsize : sz.SizeTendsto) (k : ℕ) (D : ℝ) :
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

end Grid
/-! ## 2. The `lam` patch (paper-delta candidate `T2302c`)

The merged `yMomentsQUnifN` asks `STMollifierProps (lam n) C c (ϑ n)` for **every** `n`, while the endpoint knows
`0 < lam n` only eventually (`WO`; `KLFinal_flowLam` gives only `∀ᶠ n, 0 < lam n`).  At `g ≤ 0` the window `ℓ_t` of
`(eq:ellt)` is `1` (`ellT L g t = min (max (g/√|1-t|) 1) L`), and the delta family on constant labels satisfies the
four clauses of `STMollifierProps` with `C ≥ 1`; the family `altGrid_mol` is the explicit mollifier when
`0 < lam n` and this delta family otherwise. -/

section Patch

/-- The delta family on constant labels: `1` on the labels `a₁ = ⋯ = a_{m+1}` and `0` elsewhere (constant in `t`). -/
private def altGrid_delta (d L m : ℕ) : ℝ → (Fin (m + 1) → Zd d L) → ℂ :=
  fun _ a => if ∀ i, a i = a 0 then 1 else 0

/-- The patched mollifier family (tensors of `m + 2` indices): `QopAlgebra_mollifier … (m+1)` if `0 < lam n`,
else the delta family. -/
private def altGrid_mol {d : ℕ} (sz : Sizes d) (m n : ℕ) :
    ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ :=
  if 0 < sz.lam n then QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)
  else altGrid_delta d (sz.L n) (m + 1)

/-- On the eventual set `0 < lam n` the patched family is the explicit mollifier. -/
private theorem altGrid_mol_eq {d : ℕ} (sz : Sizes d) (m n : ℕ) (h : 0 < sz.lam n) :
    altGrid_mol sz m n = QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n) := by
  unfold altGrid_mol
  rw [ite_eq_left h]

/-- `ℓ_t = 1` at a non-positive coupling (`g / √|1 - t| ≤ 0 < 1 ≤ L`). -/
private theorem altGrid_ellT_nonpos {L : ℕ} (hL : 1 ≤ L) {g : ℝ} (hg : g ≤ 0) (t : ℝ) :
    ellT L g t = 1 := by
  unfold ellT
  have h1 : g / Real.sqrt |1 - t| ≤ 0 := div_nonpos_of_nonpos_of_nonneg hg (Real.sqrt_nonneg _)
  rw [max_eq_right (by linarith)]
  exact min_eq_left (by exact_mod_cast hL)

/-- The four clauses of `STMollifierProps` for the delta family at a non-positive coupling, `1 ≤ C`, `0 ≤ c`:
(i) one constant label per `a₁`; (ii) `‖δ‖ = 1 ≤ C · 1 · e⁰` on constant labels and `0 ≤ RHS` elsewhere;
(iii) constant in `t`; (iv) the derivative is `0 ≤ RHS`. -/
private theorem altGrid_delta_props {d L : ℕ} [NeZero L] (hL : 1 ≤ L) (m : ℕ) {g C c : ℝ} (hg : g ≤ 0)
    (hC : 1 ≤ C) (hc : 0 ≤ c) : STMollifierProps (d := d) g C c (altGrid_delta d L m) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t a₁
    rw [Finset.sum_eq_single (fun _ => a₁)]
    · simp [altGrid_delta]
    · intro b hb hne
      have hb0 : b 0 = a₁ := (Finset.mem_filter.1 hb).2
      simp only [altGrid_delta]
      rw [ite_eq_right]
      intro hall
      apply hne
      funext i
      rw [hall i, hb0]
    · intro hn
      exfalso
      apply hn
      simp [Finset.mem_filter]
  · intro t _ _ a
    rw [altGrid_ellT_nonpos hL hg t]
    by_cases h : ∀ i, a i = a 0
    · have hS : ∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)), (zdistD d L (a i - a 0) : ℝ) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [h i, sub_self, zdistD_zero]
        simp
      simp only [altGrid_delta, ite_eq_left h, hS, one_pow, inv_one, div_one, mul_zero, Real.exp_zero,
        mul_one, norm_one]
      exact hC
    · simp only [altGrid_delta, ite_eq_right h, norm_zero]
      positivity
  · intro a
    exact differentiableOn_const _
  · intro t ht0 ht1 a
    have hd : deriv (fun τ => altGrid_delta d L m τ a) t = 0 := by
      have : (fun τ => altGrid_delta d L m τ a) = fun _ => (if ∀ i, a i = a 0 then (1 : ℂ) else 0) := rfl
      rw [this]
      exact deriv_const _ _
    rw [hd, norm_zero, altGrid_ellT_nonpos hL hg t]
    have h1t : 0 < 1 - t := by linarith
    have hC0 : 0 ≤ C := by linarith
    simp only [one_pow, inv_one]
    positivity

/-- `STMollifierProps` for the patched family at **every** `n` (`C₁ = (1 + 40 d(m+1)) 6^{d(m+1)} ≥ 1`, `c = 1/2`). -/
private theorem altGrid_mol_props {d : ℕ} (sz : Sizes d) (m n : ℕ) :
    STMollifierProps (d := d) (sz.lam n) ((1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1))) (1 / 2)
      (altGrid_mol sz m n) := by
  by_cases h : 0 < sz.lam n
  · rw [altGrid_mol_eq sz m n h]
    exact QopAlgebra_mollifier_props d (sz.L n) (m + 1) (sz.three_le_L n) h
  · unfold altGrid_mol
    rw [ite_eq_right h]
    refine altGrid_delta_props (by have := sz.three_le_L n; omega) (m + 1) (not_lt.1 h) ?_ (by norm_num)
    have h1 : (1 : ℝ) ≤ 1 + 40 * ((d * (m + 1) : ℕ) : ℝ) := by
      have : (0 : ℝ) ≤ ((d * (m + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    exact one_le_mul_of_one_le_of_one_le h1 (one_le_pow₀ (by norm_num))

/-- **The uniform `Y` moments for all signs with one `C_P`** (the patch): the maximum over the `2^k` sign vectors of
the constants of `yMomentsQUnifN` at the patched family serves every sign; the conclusion is for the explicit
mollifier on the eventual set `0 < lam n` (copy of `altEnd_yMomentsMax`, `QEndA.lean:926`). -/
private theorem altGrid_yMomentsMax {d : ℕ} (sz : Sizes d) {κ τR : ℝ} {E s v : ℕ → ℝ} (hκ : 0 < κ)
    (hE : ∀ n, |E n| ≤ 2 - κ) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1)
    (hsize : sz.SizeTendsto) (hrange : sz.RangeCond τR v) (m : ℕ) :
    ∃ C_P : ℝ, 0 ≤ C_P ∧ ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → ∀ σ : Fin (m + 1 + 1) → Bool,
      ∀ᶠ n : ℕ in atTop, 0 < sz.lam n → ∃ P : ℝ, 0 ≤ P ∧ P ≤ ((sz.size n : ℕ) : ℝ) ^ C_P ∧
        ∀ τ : PathΩ sz → ℕ, (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
          YMomentBoundsN sz (E n) σ (gridTime s v K n) τ (K n)
            (fun j ω => yVecQN sz E s v K n j (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ ω)
            (fun _ => gridStep s v K n ^ 2 * P) (fun _ => gridStep s v K n ^ 4 * P ^ 2) := by
  have hC0 : (0 : ℝ) < (1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1)) := by positivity
  choose CP hCP0 hCPev using fun σ : Fin (m + 1 + 1) → Bool =>
    yMomentsQUnifN sz κ τR E s v hκ hE hs0 hsv hv1 hsize hrange (m + 1)
      ((1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1))) (1 / 2)
      (fun n => altGrid_mol sz m n) hC0 (by norm_num) (fun n => altGrid_mol_props sz m n) σ
  refine ⟨Finset.univ.sup' Finset.univ_nonempty CP,
    (hCP0 (fun _ => true)).trans (Finset.le_sup' CP (Finset.mem_univ _)), fun K hK0 σ => ?_⟩
  filter_upwards [hCPev σ K hK0] with n hn hlam
  obtain ⟨P, hP0, hPle, hτ⟩ := hn
  refine ⟨P, hP0, hPle.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast sz.one_le_size n)
    (Finset.le_sup' CP (Finset.mem_univ σ))), fun τ hτm => ?_⟩
  have h := hτ τ hτm
  rw [altGrid_mol_eq sz m n hlam] at h
  exact h

end Patch

/-! ## 3. The level split (F1/`T2294c`/`T2294e`, F6): deterministic facts per `n`

The crude constants (in `N`-exponents): the crude sup of `(𝓛-𝒦)^{(k)}` on the good walk is `≤ N^{k+2}`
(`STmaxLKM_crudeN` with the `𝒦` envelope `M_K = N η_v^{-k}`), `C_big = 2k + 2`; on the small levels
`𝔏 < N^{2k+2}` the quantities of the assembly are `≤ N^{8k+7}`.  Everything is then moved to `W`-powers by
`W ≥ N^𝔠` (`C₀ = (8k+8)/𝔠`). -/

section Levels

variable {d : ℕ} (sz : Sizes d)

/-- `B_{w} ≤ 2 (1 - v)⁻¹` for `0 ≤ w ≤ v < 1` (copy of the private `gdn_Bctl_le`, `GridDriftN.lean:987`). -/
private theorem altGrid_Bctl_le (n : ℕ) {w v : ℝ} (hw0 : 0 ≤ w) (hwv : w ≤ v) (hv1 : v < 1) :
    sz.Bctl n w ≤ 2 * (1 - v)⁻¹ := by
  have hw1 : 0 < 1 - w := by linarith
  have hv : 0 < 1 - v := by linarith
  have hwv' : (1 - w)⁻¹ ≤ (1 - v)⁻¹ := inv_anti₀ hv (by linarith)
  have hWd : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.one_le_cast.2 (sz.W_pos n)
    exact one_le_pow₀ this
  have hLd : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := by
    have : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
      have := sz.three_le_L n
      exact_mod_cast (by omega : 1 ≤ sz.L n)
    exact one_le_pow₀ this
  have habs : |1 - w| = 1 - w := abs_of_pos hw1
  have hB : Bparam d (sz.L n) (sz.lam n) w 0 ≤ 2 * (1 - v)⁻¹ := by
    unfold Bparam
    rw [habs]
    have e1 : (sz.lam n ^ 2 + (1 - w))⁻¹ * ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ ≤ (1 - w)⁻¹ := by
      have : ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ = 1 := by simp
      rw [this, mul_one]
      exact inv_anti₀ hw1 (by nlinarith [sq_nonneg (sz.lam n)])
    have e2 : (((sz.L n : ℕ) : ℝ) ^ d * (1 - w))⁻¹ ≤ (1 - w)⁻¹ := by
      refine inv_anti₀ hw1 ?_
      nlinarith
    linarith
  have hB0 : 0 ≤ Bparam d (sz.L n) (sz.lam n) w 0 := by
    unfold Bparam
    rw [habs]
    positivity
  unfold Sizes.Bctl
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) w 0
      ≤ 1 * Bparam d (sz.L n) (sz.lam n) w 0 :=
        mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hWd) hB0
    _ ≤ 2 * (1 - v)⁻¹ := by rw [one_mul]; exact hB

/-- The per-`u` facts on `[0, v]`: `η_u⁻¹ ≤ η_v⁻¹ ≤ N`, `B_u ≤ 2 (1-v)⁻¹ ≤ 2 N`. -/
private theorem altGrid_u_facts (n : ℕ) {E v u : ℝ} (hE : |E| < 2) (hv1 : v < 1) (hu0 : 0 ≤ u) (huv : u ≤ v)
    (hη : (etaT E v)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) (hNv : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - v) :
    0 < etaT E u ∧ (etaT E u)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ∧ 0 < sz.Bctl n u ∧
      sz.Bctl n u ≤ 2 * ((sz.size n : ℕ) : ℝ) := by
  have hu1 : u < 1 := huv.trans_lt hv1
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  refine ⟨etaT_pos hE hu1, ?_, STBctl_pos sz n hu1, ?_⟩
  · exact (inv_anti₀ (etaT_pos hE hv1) (RBM.Green.etaT_le_of_le hE huv)).trans hη
  · have h1 := altGrid_Bctl_le sz n hu0 huv hv1
    have h2 : (1 - v)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
      have := inv_anti₀ (inv_pos.2 hN0) hNv
      rwa [inv_inv] at this
    linarith

/-- `N⁻¹ ≤ 1 - v` from `η_v⁻¹ ≤ N` and `Im m ≤ 1` (`η_v = (1 - v) Im m ≤ 1 - v`). -/
private theorem altGrid_Nv {E v N : ℝ} (hE : |E| < 2) (hv1 : v < 1) (hN0 : 0 < N) (hη : (etaT E v)⁻¹ ≤ N) :
    N⁻¹ ≤ 1 - v := by
  have h1v : 0 < 1 - v := by linarith
  have hle : etaT E v ≤ 1 - v := by
    unfold etaT
    exact mul_le_of_le_one_right h1v.le (nqBudget_im_le_one E)
  have h2 : (1 - v)⁻¹ ≤ N := (inv_anti₀ (etaT_pos hE hv1) hle).trans hη
  exact (inv_le_comm₀ h1v hN0).1 h2

/-- (`hMee` level, small `𝔏`) `Γ (Γ Λ) B^{2k}/η ≤ N^{8k+7}` for `Γ ≤ N`, `Λ ≤ N^{4k+4}`, `B ≤ 2N`, `η⁻¹ ≤ N`. -/
private theorem altGrid_hMee_bound {Γ Λ N B η : ℝ} (k : ℕ) (hN2 : 2 ≤ N) (hΓ0 : 0 ≤ Γ) (hΓN : Γ ≤ N)
    (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ N ^ (4 * k + 4)) (hB0 : 0 ≤ B) (hB : B ≤ 2 * N) (hη : 0 < η)
    (hηN : η⁻¹ ≤ N) : Γ * (Γ * Λ) * (B ^ (2 * k) / η) ≤ N ^ (8 * k + 7) := by
  have hN0 : 0 < N := by linarith
  have h1 : Γ * (Γ * Λ) ≤ N * (N * N ^ (4 * k + 4)) := by
    have : Γ * Λ ≤ N * N ^ (4 * k + 4) := mul_le_mul hΓN hΛ hΛ0 hN0.le
    exact mul_le_mul hΓN this (mul_nonneg hΓ0 hΛ0) hN0.le
  have h2 : B ^ (2 * k) ≤ (2 * N) ^ (2 * k) := pow_le_pow_left₀ hB0 hB _
  have h3 : B ^ (2 * k) / η ≤ (2 * N) ^ (2 * k) * N := by
    rw [div_eq_mul_inv]
    exact mul_le_mul h2 hηN (inv_nonneg.2 hη.le) (by positivity)
  have h4 : (2 * N) ^ (2 * k) = 4 ^ k * N ^ (2 * k) := by
    rw [mul_pow, pow_mul]; norm_num
  have h5 : (4 : ℝ) ^ k ≤ N ^ (2 * k) := by
    have h2k : (2 : ℝ) ^ k ≤ N ^ k := pow_le_pow_left₀ (by norm_num) hN2 k
    calc (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by rw [← pow_mul, mul_comm k 2, pow_mul]; norm_num
      _ ≤ (N ^ k) ^ 2 := pow_le_pow_left₀ (by positivity) h2k 2
      _ = N ^ (2 * k) := by rw [← pow_mul, mul_comm]
  calc Γ * (Γ * Λ) * (B ^ (2 * k) / η)
      ≤ (N * (N * N ^ (4 * k + 4))) * ((2 * N) ^ (2 * k) * N) :=
        mul_le_mul h1 h3 (by positivity) (by positivity)
    _ = 4 ^ k * N ^ (6 * k + 7) := by rw [h4]; ring
    _ ≤ N ^ (2 * k) * N ^ (6 * k + 7) := mul_le_mul_of_nonneg_right h5 (by positivity)
    _ = N ^ (8 * k + 7) := by rw [← pow_add]; ring_nf

/-- (`hDcr` level, small `𝔏`) `dDriftLinN ≤ N^{8k+7}` for `Γ ≤ N`, `Φ_i ≤ N^{2k+2}`, `B ≤ 2N`, `η⁻¹ ≤ N`. -/
private theorem altGrid_dDrift_bound {Γ Φ₁ Φ₂ Φ₃ N B η : ℝ} {k : ℕ} (hk : 2 ≤ k) (hN2 : 2 ≤ N)
    (hΓ0 : 0 ≤ Γ) (hΓN : Γ ≤ N) (hΦ₁ : 0 ≤ Φ₁) (hΦ₂ : 0 ≤ Φ₂) (hΦ₃ : 0 ≤ Φ₃)
    (h₁ : Φ₁ ≤ N ^ (2 * k + 2)) (h₂ : Φ₂ ≤ N ^ (2 * k + 2)) (h₃ : Φ₃ ≤ N ^ (2 * k + 2))
    (hB0 : 0 ≤ B) (hB : B ≤ 2 * N) (hη : 0 < η) (hηN : η⁻¹ ≤ N) :
    Γ * Γ * (B ^ k / η) * (((k : ℝ) - 2) * Φ₁ + Φ₂ + Φ₃) ≤ N ^ (8 * k + 7) := by
  have hN0 : 0 < N := by linarith
  have hk2 : (0 : ℝ) ≤ (k : ℝ) - 2 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hNk : (0 : ℝ) ≤ N ^ (2 * k + 2) := by positivity
  have hS0 : 0 ≤ ((k : ℝ) - 2) * Φ₁ + Φ₂ + Φ₃ :=
    add_nonneg (add_nonneg (mul_nonneg hk2 hΦ₁) hΦ₂) hΦ₃
  have hsum : ((k : ℝ) - 2) * Φ₁ + Φ₂ + Φ₃ ≤ (k : ℝ) * N ^ (2 * k + 2) := by
    have := mul_le_mul_of_nonneg_left h₁ hk2
    nlinarith
  have h1 : Γ * Γ ≤ N * N := mul_le_mul hΓN hΓN hΓ0 hN0.le
  have h2 : B ^ k ≤ (2 * N) ^ k := pow_le_pow_left₀ hB0 hB _
  have h3 : B ^ k / η ≤ (2 * N) ^ k * N := by
    rw [div_eq_mul_inv]
    exact mul_le_mul h2 hηN (inv_nonneg.2 hη.le) (by positivity)
  have h12 : Γ * Γ * (B ^ k / η) ≤ (N * N) * ((2 * N) ^ k * N) :=
    mul_le_mul h1 h3 (by positivity) (by positivity)
  have h123 : Γ * Γ * (B ^ k / η) * (((k : ℝ) - 2) * Φ₁ + Φ₂ + Φ₃) ≤
      ((N * N) * ((2 * N) ^ k * N)) * ((k : ℝ) * N ^ (2 * k + 2)) :=
    mul_le_mul h12 hsum hS0 (by positivity)
  have hkN : (k : ℝ) ≤ N ^ k := by
    have h2k : (k : ℝ) ≤ 2 ^ k := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
    exact h2k.trans (pow_le_pow_left₀ (by norm_num) hN2 k)
  have h2N : (2 : ℝ) ^ k ≤ N ^ k := pow_le_pow_left₀ (by norm_num) hN2 k
  calc Γ * Γ * (B ^ k / η) * (((k : ℝ) - 2) * Φ₁ + Φ₂ + Φ₃)
      ≤ ((N * N) * ((2 * N) ^ k * N)) * ((k : ℝ) * N ^ (2 * k + 2)) := h123
    _ = (2 : ℝ) ^ k * (k : ℝ) * N ^ (3 * k + 5) := by rw [mul_pow]; ring
    _ ≤ N ^ k * N ^ k * N ^ (3 * k + 5) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul h2N hkN (by positivity) (by positivity))
          (by positivity)
    _ = N ^ (5 * k + 5) := by rw [← pow_add, ← pow_add]; ring_nf
    _ ≤ N ^ (8 * k + 7) := pow_le_pow_right₀ (by linarith) (by omega)

/-- **The crude sup at length `k` on the good walk, in `N`-exponents** (F1/F6; deterministic, fixed `n`): for
Hermitian `H` and `u ∈ [0, v]`, `‖(𝓛-𝒦)^{(k)}_{u,σ}(H)‖_∞ ≤ N^{k+2}`, from `STmaxLKM_crudeN` with the `𝒦`
envelope `M_K = N η_v^{-k}` (`exists_norm_Kcal_le_win` at `τ = 1`), `η_u⁻¹ ≤ η_v⁻¹ ≤ N`, `N ≥ 2`
(pattern `crude_u`, `QEndA.lean:1093`). -/
private theorem altGrid_crude_N (n : ℕ) {E v : ℝ} (hE : |E| < 2) {k : ℕ} (hk : 2 ≤ k)
    (hKcal : ∀ w ∈ Set.Icc (0 : ℝ) v, ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ k →
      ‖KLK d (sz.L n) (sz.lam n) (sz.W n) E w J‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((etaT E v)⁻¹) ^ k)
    (hv1 : v < 1) (hη : (etaT E v)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) (hN2 : 2 ≤ ((sz.size n : ℕ) : ℝ))
    {u : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v)
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian)
    (σ : Fin k → Bool) :
    ‖fun b : Fin k → Zd d (sz.L n) => sz.STLKM n E u H σ b‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (k + 2) := by
  have hu1 : u < 1 := huv.trans_lt hv1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hηv := etaT_pos hE hv1
  have hηu : (etaT E u)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) :=
    (inv_anti₀ hηv (RBM.Green.etaT_le_of_le hE huv)).trans hη
  have hηv0 : 0 ≤ (etaT E v)⁻¹ := inv_nonneg.2 hηv.le
  have hηu0 : 0 ≤ (etaT E u)⁻¹ := inv_nonneg.2 (etaT_pos hE hu1).le
  have hK : ∀ (σ' : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖sz.STKloop n E u σ' a‖ ≤ ((sz.size n : ℕ) : ℝ) * ((etaT E v)⁻¹) ^ k := by
    intro σ' a
    have hJ : sz.STKloop n E u σ' a = KLK d (sz.L n) (sz.lam n) (sz.W n) E u (loopOf σ' a) := rfl
    rw [hJ]
    have h2 := hKcal u ⟨hu0, huv⟩ (loopOf σ' a) (by simp [LoopIdx.WF, loopOf])
      (by simpa [LoopIdx.length, loopOf] using hk) (by simp [LoopIdx.length, loopOf])
    rwa [Real.rpow_one] at h2
  have hmax := STmaxLKM_crudeN sz n hE hH hu0 hu1 (n' := k) (m := k) (by omega) le_rfl hK
  have hbd : (etaT E u)⁻¹ ^ k + ((sz.size n : ℕ) : ℝ) * ((etaT E v)⁻¹) ^ k ≤
      ((sz.size n : ℕ) : ℝ) ^ (k + 2) := by
    have h1 : (etaT E u)⁻¹ ^ k ≤ ((sz.size n : ℕ) : ℝ) ^ k := pow_le_pow_left₀ hηu0 hηu k
    have h2 : ((etaT E v)⁻¹) ^ k ≤ ((sz.size n : ℕ) : ℝ) ^ k := pow_le_pow_left₀ hηv0 hη k
    have h3 : ((sz.size n : ℕ) : ℝ) * ((etaT E v)⁻¹) ^ k ≤ ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ k :=
      mul_le_mul_of_nonneg_left h2 hN0.le
    have hNk : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ k := by positivity
    have h4 : (1 : ℝ) + ((sz.size n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ 2 := by nlinarith
    calc (etaT E u)⁻¹ ^ k + ((sz.size n : ℕ) : ℝ) * ((etaT E v)⁻¹) ^ k
        ≤ ((sz.size n : ℕ) : ℝ) ^ k + ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ k := by linarith
      _ = (1 + ((sz.size n : ℕ) : ℝ)) * ((sz.size n : ℕ) : ℝ) ^ k := by ring
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ 2 * ((sz.size n : ℕ) : ℝ) ^ k := mul_le_mul_of_nonneg_right h4 hNk
      _ = ((sz.size n : ℕ) : ℝ) ^ (k + 2) := by rw [← pow_add]; ring_nf
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun b => ?_
  refine le_trans ?_ (hmax.trans hbd)
  exact Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
    ‖loopFine d (sz.L n) (sz.W n) H (zt E u) p.1 p.2 - STKloop sz n E u p.1 p.2‖) (Finset.mem_univ (σ, b))

/-- **The big levels**: if `N^{2k+2} ≤ 𝔏` the crude bound `N^{k+2}` is at most `N^{ε₀} 𝔏 B^k` (`B ≥ N⁻¹`). -/
private theorem altGrid_big_case {N B 𝔏 ε₀ : ℝ} (k : ℕ) (hN1 : 1 ≤ N) (hε₀ : 0 ≤ ε₀) (hB : N⁻¹ ≤ B)
    (h𝔏 : N ^ (2 * k + 2) ≤ 𝔏) : N ^ (k + 2) ≤ N ^ ε₀ * 𝔏 * B ^ k := by
  have hN0 : 0 < N := by linarith
  have h1 : 1 ≤ N ^ ε₀ := Real.one_le_rpow hN1 hε₀
  have h2 : (N⁻¹) ^ k ≤ B ^ k := pow_le_pow_left₀ (inv_nonneg.2 hN0.le) hB k
  have h𝔏0 : 0 ≤ 𝔏 := le_trans (by positivity) h𝔏
  have hB0 : 0 ≤ B := le_trans (inv_nonneg.2 hN0.le) hB
  have e : N ^ (k + 2) = N ^ (2 * k + 2) * (N⁻¹) ^ k := by
    rw [inv_pow]
    field_simp
    ring
  calc N ^ (k + 2) = N ^ (2 * k + 2) * (N⁻¹) ^ k := e
    _ ≤ 𝔏 * B ^ k := mul_le_mul h𝔏 h2 (by positivity) h𝔏0
    _ ≤ N ^ ε₀ * 𝔏 * B ^ k := by
        have : 𝔏 ≤ N ^ ε₀ * 𝔏 := le_mul_of_one_le_left h𝔏0 h1
        exact mul_le_mul_of_nonneg_right this (by positivity)

/-- **`N^{-D_t}` absorbed** (`D_t = k + 1`, `B ≥ N⁻¹`, `𝔏 ≥ 1`, `N ≥ 2`): `N^{-(k+1)} ≤ N^e 𝔏 B^k / 2`. -/
private theorem altGrid_Dt_absorb {N B 𝔏 e : ℝ} (k : ℕ) (hN2 : 2 ≤ N) (he : 0 ≤ e) (hB : N⁻¹ ≤ B)
    (h𝔏 : 1 ≤ 𝔏) : N ^ (-((k : ℝ) + 1)) ≤ N ^ e * 𝔏 * B ^ k / 2 := by
  have hN0 : 0 < N := by linarith
  have hB0 : 0 ≤ B := le_trans (inv_nonneg.2 hN0.le) hB
  have h1 : 1 ≤ N ^ e := Real.one_le_rpow (by linarith) he
  have e1 : N ^ (-((k : ℝ) + 1)) = N⁻¹ * (N⁻¹) ^ k := by
    rw [Real.rpow_neg hN0.le, show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
      ← inv_pow, pow_succ']
  have h2 : N⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hN2
  have h3 : (N⁻¹) ^ k ≤ B ^ k := pow_le_pow_left₀ (inv_nonneg.2 hN0.le) hB k
  have h4 : N ^ (-((k : ℝ) + 1)) ≤ (1 / 2) * B ^ k := by
    rw [e1]
    have : N⁻¹ * (N⁻¹) ^ k ≤ (1 / 2) * (N⁻¹) ^ k :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    exact this.trans (mul_le_mul_of_nonneg_left h3 (by norm_num))
  have h5 : B ^ k ≤ N ^ e * 𝔏 * B ^ k := by
    have : (1 : ℝ) ≤ N ^ e * 𝔏 := by nlinarith
    exact le_mul_of_one_le_left (by positivity) this
  linarith

/-- The per-`σ` bookkeeping on plain reals (the final bound of the endpoint): `a ≤ Q + A (B_k X)` (de-`𝒬`),
`Q ≤ R + D_t` (the bridge), `R ≤ e₁ 𝔏 B_k` (the budget), `D_t ≤ e₁ 𝔏 B_k / 2`, `X ≤ 𝔏` and
`(3/2) e₁ + A ≤ e₀` give `a ≤ e₀ 𝔏 B_k`. -/
private theorem altGrid_final_arith {a Q R Dt A Bk X 𝔏 e1 e0 : ℝ} (hBk : 0 ≤ Bk) (hX : X ≤ 𝔏) (h𝔏0 : 0 ≤ 𝔏)
    (hA : 0 ≤ A) (hunQ : a ≤ Q + A * (Bk * X)) (hQ : Q ≤ R + Dt) (hR : R ≤ e1 * 𝔏 * Bk)
    (hDt : Dt ≤ e1 * 𝔏 * Bk / 2) (hfin : 3 / 2 * e1 + A ≤ e0) : a ≤ e0 * 𝔏 * Bk := by
  have h1 : A * (Bk * X) ≤ A * (Bk * 𝔏) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX hBk) hA
  have h2 : Bk * 𝔏 * (3 / 2 * e1 + A) ≤ Bk * 𝔏 * e0 :=
    mul_le_mul_of_nonneg_left hfin (mul_nonneg hBk h𝔏0)
  nlinarith

end Levels

/-! ## 4. The assembly at the alternating exit time, for one sign vector

The merged `assembledN` (`GridAssemblyN.lean:1605`) at the exit time `altExitTauN` of the walk from
`GoodSetN ∩ GoodLinN ∩ altYSetN` (levels `Γ = N^{ε₁}`, `Yl = N^{ε₁} X`), for the `𝒬`-process `aTrueQN` with the
kernel class `altClsQN` (`κ = kappaAltQN`, `εK = epsAltQN`, class exponent `ε'`, radius level `Dc`), the linear drift
level `dDriftAltLinQN`, the sub-Gaussian proxy `cQVAltQN` (`subGaussStop_altQN`), the `Y` moments of `yVecQN`
(`altGrid_yMomentsMax`) and the `qErrQN` remainder (`gridDriftQN_envelope`); then the bridge C1b
(`assembledRHSAltQN_qErr_le`) turns the remainder sum into `assembledRHSAltQN + N^{-D_t}`.  `GoodSetN` is used through
its level-free clauses only: its crude level `Φc` never enters the bound.  Private: its binders mention
`YMomentBoundsN`. -/

section Assembly

variable {d : ℕ} (sz : Sizes d)

/-- The sup constant `C₁ = (1 + 40 d (m+1)) 6^{d(m+1)}` of the mollifier `QopAlgebra_mollifier … (m+1)`. -/
private abbrev altGrid_C1 (d m : ℕ) : ℝ := (1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1))

/-- The Taylor constant `C₂ = 1000 (1 + d (m+1))²` of `gridDriftQN`. -/
private abbrev altGrid_C2 (d m : ℕ) : ℝ := 1000 * (1 + ((d * (m + 1) : ℕ) : ℝ)) ^ 2

/-- `uStepC ≥ 0` (the `𝒰`-remainder factor, copy of the block `h3` of `altEnd_stepErrN_nonneg`). -/
private theorem altGrid_uStepC_nonneg (k : ℕ) {Δ v : ℝ} (hΔ : 0 ≤ Δ) (hv1 : v < 1) :
    0 ≤ uStepC k Δ v := by
  have hv : 0 < 1 - v := by linarith
  unfold uStepC
  have hx : 0 ≤ Δ * (1 - v)⁻¹ := mul_nonneg hΔ (inv_nonneg.2 hv.le)
  have hb : 1 + (k : ℝ) * (Δ * (1 - v)⁻¹) ≤ (1 + Δ * (1 - v)⁻¹) ^ k := by
    have := one_add_mul_le_pow (a := Δ * (1 - v)⁻¹) (by linarith : (-2 : ℝ) ≤ Δ * (1 - v)⁻¹) k
    simpa using this
  have hk : 0 ≤ (k : ℝ) * Δ ^ 2 * (1 - v)⁻¹ ^ 2 := by positivity
  nlinarith

/-- **The `𝒬`-remainder `qErrQN` is nonnegative** (the field `hstepErr0`; new, ticket row `.hstepErr0`): every term of
`qStepErrN` is a product of nonnegative factors (`stepErrN ≥ 0`, `uStepC ≥ 0`, `lkEnvN`, `driftEnvN ≥ 0`,
`(1 - (u + Δ))⁻¹ ≥ 0`). -/
private theorem altGrid_qErrQN_nonneg (n j m : ℕ) {E s t : ℕ → ℝ} {K : ℕ → ℕ} {C C₂ Bk : ℝ}
    (hE : |E n| < 2) (hu : gridTime s t K n j < 1) (hu' : gridTime s t K n (j + 1) < 1)
    (hΔ : 0 ≤ gridStep s t K n) (hC : 0 ≤ C) (hC₂ : 0 ≤ C₂) (hBk : 0 ≤ Bk) :
    0 ≤ qErrQN sz E s t K n m C C₂ Bk j := by
  have hη : 0 < etaT (E n) (gridTime s t K n j) := etaT_pos hE hu
  have hη0 : 0 ≤ (etaT (E n) (gridTime s t K n j))⁻¹ := inv_nonneg.2 hη.le
  have hsucc : gridTime s t K n j + gridStep s t K n = gridTime s t K n (j + 1) := by
    unfold gridTime; push_cast; ring
  have hβ : 0 ≤ (1 - (gridTime s t K n j + gridStep s t K n))⁻¹ := by
    rw [hsucc]; exact inv_nonneg.2 (by linarith)
  have hS : 0 ≤ stepErrN d (sz.L n) (sz.W n) (E n) (m + 1) (gridTime s t K n j)
      (gridTime s t K n (j + 1)) (gridStep s t K n) Bk :=
    altGrid_stepErrN_nonneg hE hu hu' hΔ hBk
  have hUst : 0 ≤ uStepC (m + 1) (gridStep s t K n) (gridTime s t K n j + gridStep s t K n) := by
    refine altGrid_uStepC_nonneg _ hΔ ?_
    rw [hsucc]; exact hu'
  have hMk : 0 ≤ lkEnvN d (sz.W n) (E n) (m + 1) (gridTime s t K n j) Bk := by
    unfold lkEnvN; positivity
  have hDm : 0 ≤ driftEnvN d (sz.L n) (sz.W n) (E n) (m + 1) (gridTime s t K n j) Bk := by
    unfold driftEnvN; positivity
  unfold qErrQN qStepErrN
  positivity


/-- `kappaAltQN` is nonnegative (copy of the private `QBudgetA_kappa_nonneg`, `QBudgetA.lean:125`; F4). -/
private theorem altGrid_kappa_nonneg (d k : ℕ) (Λg κ' KL g W ε : ℝ) (hW : 0 ≤ W) (u : ℕ → ℝ)
    (i m : ℕ) : 0 ≤ kappaAltQN d k Λg κ' KL g W ε u i m := by
  unfold kappaAltQN
  exact mul_nonneg (Real.rpow_nonneg hW _)
    (pow_nonneg (div_nonneg (by positivity) (by positivity)) _)

/-- `epsAltQN` is nonnegative (copy of the private `QBudgetA_eps_nonneg`, `QBudgetA.lean:131`; F4). -/
private theorem altGrid_eps_nonneg (d k : ℕ) (Λg κ' KL W : ℝ) (hW : 0 ≤ W) (i m : ℕ) :
    0 ≤ epsAltQN d k Λg κ' KL W i m := by
  unfold epsAltQN
  exact Real.rpow_nonneg hW _


/-- **The assembly at the alternating exit time, for one sign vector** (the merged `assembledN` at `τ = altExitTauN`).
Eventually in `n`, on the small levels `S n` (the level split, `§3`), for every alternating `σ` on a strict window
`s_n < v_n`, there is an event `G`, `P(Gᶜ) ≤ N^{-D₁}`, on which the terminal bound
`‖𝒬_{v_n}(𝓛-𝒦)_{v_n}(H_{K n})(a)‖ ≤ assembledRHSAltQN + N^{-D_t}` holds as soon as the grid walk stays in
`GoodSetN ∩ GoodLinN ∩ altYSetN` at every `j ≤ K n`.  The levels are `Γ = N^{ε₁}` (also `ν`) and
`Yl = N^{ε₁} X`; every numerical row is an eventual hypothesis. -/
private theorem altGrid_assembly {κ : ℝ} {E s v : ℕ → ℝ} {K : ℕ → ℕ} (m : ℕ) (hd : 3 ≤ d) (hm : 1 ≤ m)
    (hκ : 0 < κ) (hE : ∀ n, |E n| ≤ 2 - κ) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n)
    (hv1 : ∀ n, v n < 1) (hK0 : ∀ n, K n ≠ 0) (hsize : sz.SizeTendsto) (hKb : sz.STKbound E)
    (Λ Φc Φ₁ Φ₂ Φ₃ X : ℕ → ℝ) (hΛ : ∀ n, 0 ≤ Λ n) (hΦ₁ : ∀ n, 0 ≤ Φ₁ n) (hΦ₂ : ∀ n, 0 ≤ Φ₂ n)
    (hΦ₃ : ∀ n, 0 ≤ Φ₃ n) (hX : ∀ n, 1 ≤ X n)
    {Λg κ' KL ε ε' τ' τN D' D'' Dc ε₁ εq τK D_Y D_t D₁ C_P C_K C₀ : ℝ}
    (hΛg : 0 < Λg) (hκ' : 0 < κ') (hKL : 0 < KL) (hκm : ∀ n, κ' ≤ (mE (E n)).im)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hε'0 : 0 < ε') (hε'1 : ε' < 1) (hε'ε : ε' ≤ ε) (hτ' : 0 ≤ τ') (hε₁0 : 0 ≤ ε₁)
    (hε₁1 : ε₁ ≤ 1) (hD'1 : 1 < D') (hDc : 1 < Dc) (hC₀ : 0 ≤ C₀) (hεq : 0 < εq) (hτK : 0 < τK)
    (hCK0 : 0 ≤ C_K) (hDt0 : 0 ≤ D_t)
    (hCK : D₁ + 4 * D_Y + ((m + 1 + 1 : ℕ) : ℝ) + 2 * C_P + 8 ≤ C_K)
    (hD : ((m + 1 : ℕ) : ℝ) + 2 + qProxyCQ d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2) < D'' + 1)
    (hKN : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ))
    (hKU : ∀ᶠ n : ℕ in atTop, K n ≤ ⌈((sz.size n : ℕ) : ℝ) ^ C_K⌉₊)
    (hY : ∀ σ : Fin (m + 1 + 1) → Bool, ∀ᶠ n : ℕ in atTop, 0 < sz.lam n → ∃ P : ℝ, 0 ≤ P ∧
      P ≤ ((sz.size n : ℕ) : ℝ) ^ C_P ∧
      ∀ τ : PathΩ sz → ℕ, (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
        YMomentBoundsN sz (E n) σ (gridTime s v K n) τ (K n)
          (fun j ω => yVecQN sz E s v K n j (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ ω)
          (fun _ => gridStep s v K n ^ 2 * P) (fun _ => gridStep s v K n ^ 4 * P ^ 2))
    (hwL : ∀ n, v n ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hWt : ∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - v n) / (1 - s n))
    (hlam : ∀ᶠ n : ℕ in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λg)
    (hW4 : ∀ᶠ n : ℕ in atTop, 4 ≤ ((sz.W n : ℕ) : ℝ))
    (hWε : ∀ᶠ n : ℕ in atTop, 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hWε' : ∀ᶠ n : ℕ in atTop, 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε')
    (hlog : ∀ᶠ n : ℕ in atTop, Real.log ((sz.L n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hNW : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ KL)
    (hdW1 : ∀ᶠ n : ℕ in atTop, (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε')
    (hdW2 : ∀ᶠ n : ℕ in atTop, (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ ε' ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hDD : ∀ᶠ n : ℕ in atTop, 4 * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dc))
    (hδ : ∀ᶠ n : ℕ in atTop, ∀ j < K n, ((sz.W n : ℕ) : ℝ) ^ (-D') +
      eeShiftErrN d (sz.L n) (sz.W n) (E n) (m + 1 + 1) (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤
        ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1)))
    (hW0a : ∀ᶠ n : ℕ in atTop,
      qProxyW0 d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2) C₀ ε (D'' + 1) ≤ ((sz.W n : ℕ) : ℝ))
    (hW0b : ∀ᶠ n : ℕ in atTop,
      QDriftA_W0 d (m + 1) KL (altGrid_C1 d m) (1 / 2) C₀ ε' D' ≤ ((sz.W n : ℕ) : ℝ))
    (hWbig : ∀ T : ℝ, ∀ᶠ n : ℕ in atTop, T ≤ ((sz.W n : ℕ) : ℝ))
    (hη : ∀ᶠ n : ℕ in atTop, (etaT (E n) (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ))
    (hνt : ∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ) ^ τ') ^ (d * m) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁)
    (hFv : ∀ᶠ n : ℕ in atTop, ((sz.W n : ℕ) : ℝ) ^ (-D') ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₁ * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹)
    (hMΛ : ∀ᶠ n : ℕ in atTop, (2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * (2 / Real.sqrt κ) * altGrid_C1 d m *
      (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τN)
    (S : ℕ → Prop)
    (hMee : ∀ᶠ n : ℕ in atTop, S n → ∀ u : ℝ, 0 ≤ u → u ≤ v n →
      ((sz.size n : ℕ) : ℝ) ^ ε₁ * (((sz.size n : ℕ) : ℝ) ^ ε₁ * Λ n) *
        ((sz.Bctl n u) ^ (2 * (m + 1 + 1)) / etaT (E n) u) + ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1)) ≤
      ((sz.W n : ℕ) : ℝ) ^ C₀)
    (hDr : ∀ᶠ n : ℕ in atTop, S n → ∀ u : ℝ, 0 ≤ u → u ≤ v n →
      dDriftLinN sz n (E n) u (m + 1 + 1) (((sz.size n : ℕ) : ℝ) ^ ε₁) (Φ₁ n) (Φ₂ n) (Φ₃ n) ≤
        ((sz.W n : ℕ) : ℝ) ^ C₀)
    (hCr : ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ v n →
      ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
        ∀ σ : Fin (m + 1 + 1) → Bool,
          ‖fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => sz.STLKM n (E n) u H σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀)
    (hsum : ∀ᶠ n : ℕ in atTop, ∀ p ≤ K n,
      ∑ j ∈ Finset.range p, (1 + (1 - gridTime s v K n p)⁻¹) ^ (m + 1 + 1) *
          qErrQN sz E s v K n (m + 1) (altGrid_C1 d m) (altGrid_C2 d m) (((sz.size n : ℕ) : ℝ) ^ τK *
            (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ (m + 1 + 1)) j ≤
        ((sz.size n : ℕ) : ℝ) ^ (-D_t)) :
    ∀ᶠ n : ℕ in atTop, S n → ∀ σ : Fin (m + 1 + 1) → Bool, σ (Fin.last (m + 1)) = !σ 0 → s n < v n →
      ∃ G : Set (PathΩ sz), (pathP sz).real Gᶜ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) ∧
        ∀ ω ∈ G,
          (∀ j ≤ K n, pathH sz s v K n j ω ∈
            sz.GoodSetN n (E n) (gridTime s v K n j) (m + 1 + 1) (((sz.size n : ℕ) : ℝ) ^ ε₁) (Λ n)
                (Φc n) τ' D' ∩
              GoodLinN sz n (E n) (gridTime s v K n j) (m + 1 + 1) (((sz.size n : ℕ) : ℝ) ^ ε₁)
                (Φ₁ n) (Φ₂ n) (Φ₃ n) ∩
              altYSetN sz n (E n) (gridTime s v K n j) (m + 1) (((sz.size n : ℕ) : ℝ) ^ ε₁ * X n)) →
          ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
            ‖aTrueQN sz E s v K n (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ (K n) ω a‖ ≤
              assembledRHSAltQN sz E s v K n m Λg κ' KL (altGrid_C1 d m) (1 / 2) ε
                (fun n => ((sz.size n : ℕ) : ℝ) ^ ε₁) Λ
                (fun j => dDriftAltLinQN sz n (E n) (gridTime s v K n j) m (((sz.size n : ℕ) : ℝ) ^ ε₁)
                  (Φ₁ n) (Φ₂ n) (Φ₃ n) (qProxyCn d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2)) ε' D' τN (X n))
                (2 * ((sz.W n : ℕ) : ℝ) ^ (-D')) (4 * ((sz.W n : ℕ) : ℝ) ^ (-D')) D'' D_Y τK εq
                (Finset.univ.sup' Finset.univ_nonempty fun b =>
                  ‖aTrueQN sz E s v K n (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ 0 ω b‖) a +
                ((sz.size n : ℕ) : ℝ) ^ (-D_t) := by
  classical
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith [abs_nonneg (E n)]
  have hC₁ : 0 < altGrid_C1 d m := by unfold altGrid_C1; positivity
  have hC₂0 : 0 ≤ altGrid_C2 d m := by unfold altGrid_C2; positivity
  have hlam0 : ∀ᶠ n : ℕ in atTop, 0 < sz.lam n := hlam.mono fun n h => h.1
  have hk2 : 2 ≤ m + 1 + 1 := by omega
  obtain ⟨W₀, hW₀1, HDcls⟩ := alt_hDclsGridQN d m Λg KL C₀ ε' D' hd hΛg hε'0
  have hA := assembledN sz hsize (m + 1 + 1) εq hεq D_Y D₁ C_P C_K hCK0 hCK
  have hEnv : ∀ σ : Fin (m + 1 + 1) → Bool, ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂(pathP sz), ∀ j, j < K n →
      ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
      ‖rGridQN sz E s v K n (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ j ω a‖ ≤
        qErrQN sz E s v K n (m + 1) (altGrid_C1 d m) (altGrid_C2 d m) (((sz.size n : ℕ) : ℝ) ^ τK *
          (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ (m + 1 + 1)) j :=
    fun σ => gridDriftQN_envelope sz κ hκ m hm τK hτK hsize hKb hE hs0 hsv hv1 hK0 hlam0 σ
  filter_upwards [hA, hKN, hKU, Filter.eventually_all.2 hY, Filter.eventually_all.2 hEnv, hlam, hWt, hW4,
    hWε, hWε', hlog, hNW, hdW1, hdW2, hDD, hδ, hW0a, hW0b, hWbig W₀, hη, hνt, hFv, hMΛ, hMee, hDr, hCr,
    hsum] with n hAn hKNn hKUn hYn hEnvn hlamn hWtn hW4n hWεn hWε'n hlogn hNWn hdW1n hdW2n hDDn hδn hW0an
    hW0bn hW₀n hηn hνtn hFvn hMΛn hMeen hDrn hCrn hsumn
  intro hSn σ hσ hsvn
  obtain ⟨hg, hgΛ⟩ := hlamn
  obtain ⟨P, hP0, hPle, hYP⟩ := hYn σ hg
  have hMeen := hMeen hSn
  have hDrn := hDrn hSn
  have hEn2 : |E n| < 2 := hE2 n
  have hKn : K n ≠ 0 := hK0 n
  have hK1 : 1 ≤ K n := Nat.one_le_iff_ne_zero.2 hKn
  have hvs : v n - s n ≤ 1 := by linarith [hv1 n, hs0 n]
  have hΔ : gridStep s v K n ≤ ((sz.size n : ℕ) : ℝ) ^ (-C_K) := altGrid_step_le sz hKNn hvs
  have hKΔ : (K n : ℝ) * gridStep s v K n ≤ 1 := altGrid_K_mul_step hKn hvs
  have hΔ0 : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n (hsv n)
  have hu0 : ∀ i ≤ K n, 0 ≤ gridTime s v K n i := fun i _ => altGrid_gridTime_nonneg (hs0 n) (hsv n) i
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi =>
    (altGrid_gridTime_le (hsv n) hKn hi).trans_lt (hv1 n)
  have huv : ∀ i ≤ K n, gridTime s v K n i ≤ v n := fun i hi => altGrid_gridTime_le (hsv n) hKn hi
  have hmono : ∀ i m', i ≤ m' → m' ≤ K n → gridTime s v K n i ≤ gridTime s v K n m' :=
    fun i m' him _ => ST_gridTime_mono s v K n (hsv n) him
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := altGrid_one_le_size sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hW1 : (1 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hW2 : (2 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by linarith
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hNvn : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - v n := altGrid_Nv hEn2 (hv1 n) hN0 hηn
  have hLKn : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ KL := by
    refine le_trans ?_ hNWn
    have h1 := altGrid_size_cast sz n
    have h2 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := one_le_pow₀ hW1.le
    have h3 : (0 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := by positivity
    calc ((sz.L n : ℕ) : ℝ) ^ d = 1 * ((sz.L n : ℕ) : ℝ) ^ d := (one_mul _).symm
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := mul_le_mul_of_nonneg_right h2 h3
      _ = ((sz.size n : ℕ) : ℝ) := h1
  have hKv : (1 - v n)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ KL := by
    refine le_trans ?_ hNWn
    have := inv_anti₀ (inv_pos.2 hN0) hNvn
    rwa [inv_inv] at this
  have hdW0 : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε :=
    hdW1n.trans (Real.rpow_le_rpow_of_exponent_le hW1.le hε'ε)
  have hDD2 : 2 * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dc) := by
    have := Real.rpow_nonneg hW0.le (-D')
    linarith
  have hν1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ := Real.one_le_rpow hN1 hε₁0
  have hνN : ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.size n : ℕ) : ℝ) := by
    calc ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 hε₁1
      _ = _ := Real.rpow_one _
  -- the data of the assembly
  set ϑ : ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ :=
    QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n) with hϑ
  set u : ℕ → ℝ := gridTime s v K n with hu
  set Δ : ℝ := gridStep s v K n with hΔdef
  set Γ : ℕ → ℝ := fun n => ((sz.size n : ℕ) : ℝ) ^ ε₁ with hΓ
  set Yl : ℕ → ℝ := fun n => ((sz.size n : ℕ) : ℝ) ^ ε₁ * X n with hYl
  set τ : PathΩ sz → ℕ := altExitTauN sz E s v K (m + 1 + 1) Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D' n with hτdef
  have hτmeas : ∀ j, MeasurableSet[filt sz j] {ω | j < τ ω} :=
    altExitMeasN sz E s v K n (m + 1 + 1) Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D'
  have hmem : ∀ (ω : PathΩ sz) (j : ℕ), j < τ ω → pathH sz s v K n j ω ∈
      sz.GoodSetN n (E n) (u j) (m + 1 + 1) (Γ n) (Λ n) (Φc n) τ' D' ∩
        GoodLinN sz n (E n) (u j) (m + 1 + 1) (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) ∩
          altYSetN sz n (E n) (u j) (m + 1 + 1 - 1) (Yl n) :=
    fun ω j hj => mem_of_lt_altExitTauN hj
  have hcrude : ∀ (ω : PathΩ sz) (j : ℕ), j < τ ω → j ≤ K n →
      ‖fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
        sz.STLKM n (E n) (u j) (pathH sz s v K n j ω) σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀ :=
    fun ω j hj hjK => hCrn (u j) (hu0 j hjK) (huv j hjK) _ (hmem ω j hj).1.1.1 σ
  have hAcr : ∀ (ω : PathΩ sz) (j : ℕ), j < K n → j < τ ω →
      ‖fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
        sz.STLKM n (E n) (gridTime s v K n j) (pathH sz s v K n j ω) σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀ :=
    fun ω j hjK hjτ => hcrude ω j hjτ hjK.le
  have hDcr : ∀ (ω : PathΩ sz) (j : ℕ), j < K n → j < τ ω →
      ‖fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
        driftTensorN sz n (E n) (gridTime s v K n j) (pathH sz s v K n j ω) σ b‖ ≤
          ((sz.W n : ℕ) : ℝ) ^ C₀ :=
    fun ω j hjK hjτ => altEnd_driftSup sz n hk2 (hmem ω j hjτ).1.2
      (hDrn (u j) (hu0 j hjK.le) (huv j hjK.le)) σ
  have hZmeas : ∀ j, StronglyMeasurable[filt sz (j + 1)] (fun ω => zVecQN sz E s v K n j ϑ σ ω) :=
    fun j => altEnd_stronglyMeasurable_zVecQN sz E s v K n j ϑ σ
  have hsubG : ∀ m' ≤ K n, ∀ (a : Fin (m + 1 + 1) → Zd d (sz.L n)) (j : ℕ), j < m' →
      SubGaussStopN sz (E n) σ u τ (fun j ω => zVecQN sz E s v K n j ϑ σ ω) m' a j
        (cQVAltQN sz E s v K n m Λg κ' KL (altGrid_C1 d m) (1 / 2) ε Γ Λ D'' m' a j) := by
    intro m' hm' a j hj
    have hj1 : j + 1 ≤ K n := by omega
    exact subGaussStop_altQN (m := m) Λg κ' KL hd hΛg hκ' hKL sz hE2 hs0 hsv hv1 n (hwL n) hWtn (hκm n) hg hgΛ
      (ε := ε) (τ' := τ') (C₀ := C₀) (D' := D') (D'' := D'') hW2 hε0 hε1 hWεn hlogn hLKn hdW0 hC₀ hD hW0an
      (σ := σ) Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl m' hm' a j hj (hMeen _ (hu0 _ hj1) (huv _ hj1)) (hδn j (by omega))
  have hbundle : GridAssemblyHypN sz (n := n) (k := m + 1 + 1) (E n) σ u τ Δ (K n)
      (altClsQN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) ε' Dc u)
      (fun ω => aTrueQN sz E s v K n ϑ σ 0 ω) (fun m' ω => aFrozQN sz E s v K n ϑ σ τ m' ω)
      (fun j ω => dGridQN sz E s v K n ϑ σ j ω) (fun j ω => zVecQN sz E s v K n j ϑ σ ω)
      (fun j ω => yVecQN sz E s v K n j ϑ σ ω) (fun j ω => rGridQN sz E s v K n ϑ σ j ω)
      (kappaAltQN d (m + 1 + 1) Λg κ' KL (sz.lam n) ((sz.W n : ℕ) : ℝ) ε u)
      (epsAltQN d (m + 1 + 1) Λg κ' KL ((sz.W n : ℕ) : ℝ)) (2 * ((sz.W n : ℕ) : ℝ) ^ (-D'))
      (fun j _ => dDriftAltLinQN sz n (E n) (u j) m (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)
        (qProxyCn d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2)) ε' D' τN (X n))
      (fun _ _ => 4 * ((sz.W n : ℕ) : ℝ) ^ (-D'))
      (fun m' a j => cQVAltQN sz E s v K n m Λg κ' KL (altGrid_C1 d m) (1 / 2) ε Γ Λ D'' m' a j)
      (fun _ => Δ ^ 2 * P) (fun _ => Δ ^ 4 * P ^ 2)
      (fun j => qErrQN sz E s v K n (m + 1) (altGrid_C1 d m) (altGrid_C2 d m) (((sz.size n : ℕ) : ℝ) ^ τK *
        (etaT (E n) (u (j + 1)))⁻¹ ^ (m + 1 + 1)) j) := {
    hE := hEn2.le
    hu0 := hu0
    hu1 := hu1
    hΔ0 := hΔ0
    hexp := altEnd_hexp sz E s v K n hEn2 (hs0 n) (hsv n) (hv1 n) hKn ϑ σ τ
    hκ0 := fun i m' _ _ => altGrid_kappa_nonneg d (m + 1 + 1) Λg κ' KL (sz.lam n) _ ε hW0.le u i m'
    hε0 := fun i m' _ _ => altGrid_eps_nonneg d (m + 1 + 1) Λg κ' KL _ hW0.le i m'
    hker := alt_hkerGridQN Λg κ' KL hd hΛg hκ' hKL sz E s v K n (hs0 n) (hsv n) hKn hEn2.le (hκm n) hg hgΛ
      hW1 hε0 hε1 hWεn hlogn hLKn hdW2n hDc (hwL n) hWtn σ
    hδ0 := by positivity
    hA0cls := alt_hA0clsGridQN sz hd m KL C₀ ε' D' hε'0 σ E s v K Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' Dc hW0bn hLKn hdW1n
      hDD2 hg (hs0 n) ((hsv n).trans_lt (hv1 n)) (fun ω hω => hcrude ω 0 hω (Nat.zero_le _))
    hdDrift0 := fun ω j hj => dDriftAltLinQN_nonneg sz n (E n) (u j) m (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) _ ε' D' τN
      (X n) hEn2 (hu1 j hj.le) (hΦ₁ n) (hΦ₂ n) (hΦ₃ n) (by linarith [hX n])
    hδD0 := fun _ _ _ => by positivity
    hdrift := fun ω j hjK hjτ b => alt_hdriftGridQN d m Λg KL hd hΛg hKL sz n σ E s v K Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl κ
      τ' ε' D' (((sz.size n : ℕ) : ℝ) ^ ε₁) (X n) τN hκ (hE n) hg hgΛ (hs0 n) (hsv n) (hv1 n) hNvn hW1 hτ'
      hε'0 hε'1 hD'1 hWε'n hLKn hdW1n hν1 (hX n) hνtn hνN hFvn hMΛn le_rfl hσ ω j hjK hjτ b
    hDcls := fun ω j hjK hjτ => HDcls sz n σ E s v K Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' Dc hEn2.le hg hgΛ hW₀n hLKn (hs0 n)
      (hsv n) (hv1 n) hKv hdW1n hDDn hAcr hDcr ω j hjK hjτ
    hc_pos := fun m' hm1 hmK a => by
      have hΔpos : 0 < Δ := div_pos (by linarith) (by exact_mod_cast Nat.pos_of_ne_zero hKn)
      have hterm : ∀ j ∈ Finset.range m',
          0 < (cQVAltQN sz E s v K n m Λg κ' KL (altGrid_C1 d m) (1 / 2) ε Γ Λ D'' m' a j : ℝ) := by
        intro j hj
        have hj1 : j + 1 ≤ K n := by have := Finset.mem_range.1 hj; omega
        have hη' := etaT_pos hEn2 (hu1 (j + 1) hj1)
        have hB' := STBctl_pos sz n (hu1 (j + 1) hj1)
        have hΛ' := hΛ n
        have hΓ' : 0 ≤ Γ n := Real.rpow_nonneg hN0.le _
        unfold cQVAltQN
        rw [NNReal.coe_pos, Real.toNNReal_pos]
        have hq : 0 < qvBdAltQN sz n (E n) m Λg κ' KL (altGrid_C1 d m) (1 / 2) ε (Γ n) (Λ n) D'' (u (j + 1))
            (u m') := by
          unfold qvBdAltQN
          positivity
        positivity
      exact Finset.sum_pos hterm ⟨0, Finset.mem_range.2 (by omega)⟩
    hv0 := fun _ _ => by positivity
    hw0 := fun _ _ => by positivity
    hY := hYP τ hτmeas
    hstepErr0 := fun j hj => altGrid_qErrQN_nonneg sz n j (m + 1) hEn2 (hu1 j hj.le) (hu1 (j + 1) hj) hΔ0
      hC₁.le hC₂0
      (by
        have := etaT_pos hEn2 (hu1 (j + 1) hj)
        positivity)
    hR := (hEnvn σ).mono fun ω hω j hj _ b => hω j hj b }
  obtain ⟨G, hG, hGb⟩ := hAn (K n) (E n) σ u τ Δ
    (altClsQN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) ε' Dc u)
    (fun ω => aTrueQN sz E s v K n ϑ σ 0 ω) (fun m' ω => aFrozQN sz E s v K n ϑ σ τ m' ω)
    (fun j ω => dGridQN sz E s v K n ϑ σ j ω) (fun j ω => zVecQN sz E s v K n j ϑ σ ω)
    (fun j ω => yVecQN sz E s v K n j ϑ σ ω) (fun j ω => rGridQN sz E s v K n ϑ σ j ω)
    (kappaAltQN d (m + 1 + 1) Λg κ' KL (sz.lam n) ((sz.W n : ℕ) : ℝ) ε u)
    (epsAltQN d (m + 1 + 1) Λg κ' KL ((sz.W n : ℕ) : ℝ)) (2 * ((sz.W n : ℕ) : ℝ) ^ (-D'))
    (fun j _ => dDriftAltLinQN sz n (E n) (u j) m (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)
      (qProxyCn d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2)) ε' D' τN (X n))
    (fun _ _ => 4 * ((sz.W n : ℕ) : ℝ) ^ (-D'))
    (fun m' a j => cQVAltQN sz E s v K n m Λg κ' KL (altGrid_C1 d m) (1 / 2) ε Γ Λ D'' m' a j)
    (fun _ => Δ ^ 2 * P) (fun _ => Δ ^ 4 * P ^ 2)
    (fun j => qErrQN sz E s v K n (m + 1) (altGrid_C1 d m) (altGrid_C2 d m) (((sz.size n : ℕ) : ℝ) ^ τK *
      (etaT (E n) (u (j + 1)))⁻¹ ^ (m + 1 + 1)) j) P hK1 hKUn hΔ hKΔ hP0 hPle (fun _ _ => le_rfl)
    (fun _ _ => le_rfl) hτmeas hZmeas hsubG hbundle
  refine ⟨G, hG, fun ω hω hgood a => ?_⟩
  have hτeq : τ ω = K n := gridExitTauN_eq_of_forall_mem hgood
  have hτpos : 0 < τ ω := by rw [hτeq]; omega
  have hb := hGb ω hω hτpos (K n) le_rfl a
  have hAeq : aFrozQN sz E s v K n ϑ σ τ (K n) ω = aTrueQN sz E s v K n ϑ σ (K n) ω :=
    altEnd_aFroz_eq_aTrue sz E s v K n hEn2.le (hs0 n) (hsv n) (hv1 n) hKn ϑ σ τ ω (by rw [hτeq])
  have hb' : ‖aFrozQN sz E s v K n ϑ σ τ (K n) ω a‖ ≤ _ := hb
  rw [hAeq] at hb'
  have hC1b := assembledRHSAltQN_qErr_le sz E s v K n m Λg κ' KL (altGrid_C1 d m) (1 / 2) ε Γ Λ
    (fun j => dDriftAltLinQN sz n (E n) (u j) m (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)
      (qProxyCn d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2)) ε' D' τN (X n))
    (2 * ((sz.W n : ℕ) : ℝ) ^ (-D')) (4 * ((sz.W n : ℕ) : ℝ) ^ (-D')) D'' D_Y τK εq
    (Finset.univ.sup' Finset.univ_nonempty fun b => ‖aTrueQN sz E s v K n ϑ σ 0 ω b‖)
    (Finset.univ.sup' Finset.univ_nonempty fun b => ‖aTrueQN sz E s v K n ϑ σ 0 ω b‖) D_t
    (altGrid_C1 d m) (altGrid_C2 d m) a hEn2 (hs0 n) (hsv n) (hv1 n) hKn hτK.le le_rfl (hsumn (K n) le_rfl)
  exact hb'.trans hC1b

end Assembly

/-! ## 5. Helpers of the endpoint: `W`-powers, the logarithm of `L`, the final absorption, the exponent bookkeeping -/

section EndHelpers

variable {d : ℕ} (sz : Sizes d)

/-- `W^e ≤ N^{𝔠 e}` for `e ≤ 0` from `N^𝔠 ≤ W` (copy of `nqEnd_Wpow_le`, `NQEndLin.lean:154`). -/
private theorem altGrid_Wpow_le {W N c e : ℝ} (hN0 : 0 < N) (hcW : N ^ c ≤ W) (he : e ≤ 0) :
    W ^ e ≤ N ^ (c * e) := by
  have h1 : 0 < N ^ c := Real.rpow_pos_of_pos hN0 _
  have h := Real.rpow_le_rpow_of_nonpos h1 hcW he
  rwa [← Real.rpow_mul hN0.le] at h

/-- `N^a ≤ W^{c/𝔠}` for `a ≤ c` from `N^𝔠 ≤ W`, `N ≥ 1` (the move from `N`-exponents to `W`-exponents). -/
private theorem altGrid_Npow_le_Wpow {N W 𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (hN1 : 1 ≤ N) (hband : N ^ 𝔠 ≤ W)
    {a c : ℕ} (hac : a ≤ c) : N ^ a ≤ W ^ ((c : ℝ) / 𝔠) := by
  have hN0 : 0 ≤ N := by linarith
  calc N ^ a ≤ N ^ c := pow_le_pow_right₀ hN1 hac
    _ = N ^ (c : ℝ) := (Real.rpow_natCast _ _).symm
    _ = (N ^ 𝔠) ^ ((c : ℝ) / 𝔠) := by
        rw [← Real.rpow_mul hN0]; congr 1; field_simp
    _ ≤ W ^ ((c : ℝ) / 𝔠) := Real.rpow_le_rpow (Real.rpow_nonneg hN0 _) hband (by positivity)

/-- (`hlog`) `log L ≤ W^ε` eventually (`L ≤ N`, `L^δ ≤ W^{ε/2}` for `δ = ε𝔠/2`, `log x ≤ x^δ/δ`, `W^{ε/2} ≥ 1/δ`). -/
private theorem altGrid_ev_hlog (hd : 1 ≤ d) (hsize : sz.SizeTendsto) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠)
    (hband : sz.Bandwidth 𝔠) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.log ((sz.L n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ ε := by
  have hδ0 : 0 < ε * 𝔠 / 2 := by positivity
  filter_upwards [hband, altGrid_ev_W_rpow_ge sz hsize h𝔠 hband (half_pos hε) (1 / (ε * 𝔠 / 2)),
    hsize.eventually_ge_atTop 1] with n hbn hWb hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hL0 : 0 ≤ ((sz.L n : ℕ) : ℝ) := by linarith
  have hLN : ((sz.L n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
    have h1 := altGrid_size_cast sz n
    have h2 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := one_le_pow₀ hW1
    have h3 : ((sz.L n : ℕ) : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := le_self_pow₀ hL1 (by omega)
    have h4 : (0 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := by positivity
    calc ((sz.L n : ℕ) : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := h3
      _ = 1 * ((sz.L n : ℕ) : ℝ) ^ d := (one_mul _).symm
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := mul_le_mul_of_nonneg_right h2 h4
      _ = ((sz.size n : ℕ) : ℝ) := h1
  have hlog := Real.log_le_rpow_div hL0 hδ0
  have h1 : ((sz.L n : ℕ) : ℝ) ^ (ε * 𝔠 / 2) ≤ ((sz.W n : ℕ) : ℝ) ^ (ε / 2) := by
    calc ((sz.L n : ℕ) : ℝ) ^ (ε * 𝔠 / 2) ≤ ((sz.size n : ℕ) : ℝ) ^ (ε * 𝔠 / 2) :=
          Real.rpow_le_rpow hL0 hLN hδ0.le
      _ = (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (ε / 2) := by
          rw [← Real.rpow_mul hN0.le]; congr 1; ring
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ (ε / 2) :=
          Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hbn (by positivity)
  calc Real.log ((sz.L n : ℕ) : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ (ε * 𝔠 / 2) / (ε * 𝔠 / 2) := hlog
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ (ε / 2) / (ε * 𝔠 / 2) := div_le_div_of_nonneg_right h1 hδ0.le
    _ = ((sz.W n : ℕ) : ℝ) ^ (ε / 2) * (1 / (ε * 𝔠 / 2)) := by ring
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ (ε / 2) * ((sz.W n : ℕ) : ℝ) ^ (ε / 2) :=
        mul_le_mul_of_nonneg_left hWb (Real.rpow_nonneg hW0.le _)
    _ = ((sz.W n : ℕ) : ℝ) ^ ε := by
        rw [← Real.rpow_add hW0]; congr 1; ring

end EndHelpers

/-- The final absorption `(3/2) N^{e₂} + N^{τ_N} ≤ N^{ε₀}` once `N^{ε₀ - e₂} ≥ 3` and `τ_N ≤ e₂`. -/
private theorem altGrid_fin_arith {N e2 τN ε₀ : ℝ} (hN1 : 1 ≤ N) (hτN : τN ≤ e2)
    (hbig : 3 ≤ N ^ (ε₀ - e2)) : 3 / 2 * N ^ e2 + N ^ τN ≤ N ^ ε₀ := by
  have hN0 : 0 < N := by linarith
  have h1 : N ^ τN ≤ N ^ e2 := Real.rpow_le_rpow_of_exponent_le hN1 hτN
  have h2 : N ^ ε₀ = N ^ (ε₀ - e2) * N ^ e2 := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have h3 : 0 ≤ N ^ e2 := Real.rpow_nonneg hN0.le _
  rw [h2]
  nlinarith [mul_le_mul_of_nonneg_right hbig h3]

/-- **The exponent bookkeeping** (private `Prop`-valued structure, pattern `NQEndArith`, `NQEndLin.lean:662`) at
`e₂ = ε₀''` (the budget exponent), `ε = min (e₂/(8 max(C₄, C_n))) (1/2)`, `ε' = ε/2`,
`τ' = min (ε/4) (e₂/(40 d m))`, `ε₁ = e₂/40`, `τ_N = e₂/8`, `D'' = 2C_n + 2 + 2C₄ + k + (4k+1)/𝔠`,
`D' = D'' + 2` (F2), `D_c = D'' + 1`, `C_K = D₁ + 2C_P + 8k + 20 + D''` (F5), `k = m + 2`, `D_Y = D_t = k + 1`. -/
private structure AltGridArith (d m : ℕ) (𝔠 C₄ Cn e2 D₁ Cmax ε ε' τ' ε₁ τN D'' D' Dc C_K : ℝ) : Prop where
  hε0 : 0 < ε
  hε1 : ε < 1
  hε'0 : 0 < ε'
  hε'1 : ε' < 1
  hε'ε : ε' ≤ ε
  hτ'0 : 0 < τ'
  hτ'ε : τ' ≤ ε / 4
  hτ'dm : τ' * ((d : ℝ) * m) ≤ ε₁
  hε₁0 : 0 < ε₁
  hε₁1 : ε₁ ≤ 1
  hε₁e2 : ε₁ ≤ e2
  hτNe2 : τN ≤ e2
  h2ε₁τN : 2 * ε₁ < τN
  hD''0 : 0 < D''
  hD'1 : 1 < D'
  hDc1 : 1 < Dc
  hCK0 : 0 ≤ C_K
  hCK1 : 1 ≤ C_K
  hCKa : (D₁ + 1) + 4 * (((m + 1 + 1 : ℕ) : ℝ) + 1) + ((m + 1 + 1 : ℕ) : ℝ) + 2 * Cmax + 8 ≤ C_K
  hCKb : (D'' + 1) + 2 * ((m + 1 + 1 : ℕ) : ℝ) + 5 ≤ C_K
  hCKθ : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
    8 + (4 * ((m + 1 + 1 : ℕ) : ℝ) + 8) * θ + 2 * (((m + 1 + 1 : ℕ) : ℝ) + 1) < C_K ∧
    3 + 4 * 1 + 5 * ((m + 1 + 1 : ℕ) : ℝ) * θ + (((m + 1 + 1 : ℕ) : ℝ) + 1) < C_K ∧
    2 * θ + 1 + 2 * ((m + 1 + 1 : ℕ) : ℝ) * θ + (((m + 1 + 1 : ℕ) : ℝ) + 1) < C_K ∧
    8 + (4 * (((m + 1 : ℕ) : ℝ) + 1) + 8) * θ +
      2 * ((((m + 1 + 1 : ℕ) : ℝ) + 1) + (((m + 1 : ℕ) : ℝ) + 1)) < C_K ∧
    3 + 4 * 1 + 5 * (((m + 1 : ℕ) : ℝ) + 1) * θ +
      ((((m + 1 + 1 : ℕ) : ℝ) + 1) + (((m + 1 : ℕ) : ℝ) + 1)) < C_K ∧
    2 * θ + 1 + 2 * (((m + 1 : ℕ) : ℝ) + 1) * θ +
      ((((m + 1 + 1 : ℕ) : ℝ) + 1) + (((m + 1 : ℕ) : ℝ) + 1)) < C_K
  hD : ((m + 1 : ℕ) : ℝ) + 2 + (2 * Cn + 2) < D'' + 1
  hFv : (2 * (m : ℝ) + 4) ≤ 𝔠 * D'
  hexp : altBudgetExpQN (m + 1 + 1) C₄ Cn 𝔠 ε ε' τN D' D'' (((m + 1 + 1 : ℕ) : ℝ) + 1)
    (((m + 1 + 1 : ℕ) : ℝ) + 1) ε₁ e2 ε₁ (-(2 * ((m + 1 + 1 : ℕ) : ℝ) + 1))

private theorem altGrid_arith (d m : ℕ) {𝔠 C₄ Cn e2 D₁ Cmax ε ε' τ' ε₁ τN D'' D' Dc C_K : ℝ}
    (hd : 3 ≤ d) (hm : 1 ≤ m) (h𝔠 : 0 < 𝔠) (hC₄ : 0 < C₄) (hCn : 0 < Cn) (he2 : 0 < e2) (he2le : e2 ≤ 1)
    (hD₁ : 0 < D₁) (hCmax : 0 ≤ Cmax)
    (hε : ε = min (e2 / (8 * max C₄ Cn)) (1 / 2)) (hε' : ε' = ε / 2)
    (hτ' : τ' = min (ε / 4) (e2 / (40 * ((d : ℝ) * m)))) (hε₁ : ε₁ = e2 / 40) (hτN : τN = e2 / 8)
    (hD'' : D'' = 2 * Cn + 2 + 2 * C₄ + ((m + 1 + 1 : ℕ) : ℝ) + (4 * ((m + 1 + 1 : ℕ) : ℝ) + 1) / 𝔠)
    (hD' : D' = D'' + 2) (hDc : Dc = D'' + 1)
    (hCK : C_K = D₁ + 2 * Cmax + 8 * ((m + 1 + 1 : ℕ) : ℝ) + 20 + D'') :
    AltGridArith d m 𝔠 C₄ Cn e2 D₁ Cmax ε ε' τ' ε₁ τN D'' D' Dc C_K := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hd0 : (0 : ℝ) < d := by linarith
  have hm0 : (0 : ℝ) < m := by linarith
  have hkd : ((m + 1 + 1 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
  have hk3 : (3 : ℝ) ≤ ((m + 1 + 1 : ℕ) : ℝ) := by rw [hkd]; linarith
  have hk0 : (0 : ℝ) < ((m + 1 + 1 : ℕ) : ℝ) := by linarith
  have hmk : ((m + 1 : ℕ) : ℝ) + 1 = ((m + 1 + 1 : ℕ) : ℝ) := by push_cast; ring
  have hMx : 0 < max C₄ Cn := lt_max_of_lt_left hC₄
  have hε0 : 0 < ε := by rw [hε]; exact lt_min (by positivity) (by norm_num)
  have hεhalf : ε ≤ 1 / 2 := by rw [hε]; exact min_le_right _ _
  have hεMx : ε ≤ e2 / (8 * max C₄ Cn) := by rw [hε]; exact min_le_left _ _
  have hCε : ∀ C : ℝ, 0 < C → C ≤ max C₄ Cn → C * ε ≤ e2 / 8 := by
    intro C hC hCM
    calc C * ε ≤ max C₄ Cn * ε := mul_le_mul_of_nonneg_right hCM hε0.le
      _ ≤ max C₄ Cn * (e2 / (8 * max C₄ Cn)) := mul_le_mul_of_nonneg_left hεMx hMx.le
      _ = e2 / 8 := by field_simp
  have hC₄ε : C₄ * ε ≤ e2 / 8 := hCε C₄ hC₄ (le_max_left _ _)
  have hCnε : Cn * ε ≤ e2 / 8 := hCε Cn hCn (le_max_right _ _)
  have hε'0 : 0 < ε' := by rw [hε']; positivity
  have hCnε' : Cn * ε' ≤ e2 / 8 := by
    rw [hε']
    have : Cn * (ε / 2) = Cn * ε / 2 := by ring
    rw [this]
    linarith
  have hτ'0 : 0 < τ' := by rw [hτ']; exact lt_min (by positivity) (by positivity)
  have hτ'dm : τ' * ((d : ℝ) * m) ≤ ε₁ := by
    have h1 : τ' ≤ e2 / (40 * ((d : ℝ) * m)) := by rw [hτ']; exact min_le_right _ _
    calc τ' * ((d : ℝ) * m) ≤ e2 / (40 * ((d : ℝ) * m)) * ((d : ℝ) * m) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = e2 / 40 := by field_simp
      _ = ε₁ := hε₁.symm
  have hε₁0 : 0 < ε₁ := by rw [hε₁]; positivity
  have hqpos : 0 < (4 * ((m + 1 + 1 : ℕ) : ℝ) + 1) / 𝔠 := by positivity
  have hq'le : (2 * ((m + 1 + 1 : ℕ) : ℝ) + 1) / 𝔠 ≤ (4 * ((m + 1 + 1 : ℕ) : ℝ) + 1) / 𝔠 :=
    div_le_div_of_nonneg_right (by linarith) h𝔠.le
  have hD''0 : 0 < D'' := by rw [hD'']; positivity
  have hCKa : (D₁ + 1) + 4 * (((m + 1 + 1 : ℕ) : ℝ) + 1) + ((m + 1 + 1 : ℕ) : ℝ) + 2 * Cmax + 8 ≤ C_K := by
    rw [hCK]; linarith
  refine ⟨hε0, by linarith, hε'0, by rw [hε']; linarith, by rw [hε']; linarith, hτ'0,
    by rw [hτ']; exact min_le_left _ _, hτ'dm, hε₁0, by rw [hε₁]; linarith, by rw [hε₁]; linarith,
    by rw [hτN]; linarith, by rw [hε₁, hτN]; linarith, hD''0, by rw [hD']; linarith,
    by rw [hDc]; linarith, by rw [hCK]; linarith, by rw [hCK]; linarith, hCKa,
    by rw [hCK]; linarith, ?_, ?_, ?_, ?_⟩
  · intro θ hθ0 hθ1
    have hq : ((m + 1 : ℕ) : ℝ) + 1 = ((m + 1 + 1 : ℕ) : ℝ) := hmk
    rw [hq]
    have h1 : (4 * ((m + 1 + 1 : ℕ) : ℝ) + 8) * θ ≤ 4 * ((m + 1 + 1 : ℕ) : ℝ) + 8 :=
      mul_le_of_le_one_right (by positivity) hθ1
    have h2 : 5 * ((m + 1 + 1 : ℕ) : ℝ) * θ ≤ 5 * ((m + 1 + 1 : ℕ) : ℝ) :=
      mul_le_of_le_one_right (by positivity) hθ1
    have h3 : 2 * ((m + 1 + 1 : ℕ) : ℝ) * θ ≤ 2 * ((m + 1 + 1 : ℕ) : ℝ) :=
      mul_le_of_le_one_right (by positivity) hθ1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hCK] <;> linarith
  · -- `hD`
    rw [hD'']
    have : ((m + 1 : ℕ) : ℝ) + 1 = ((m + 1 + 1 : ℕ) : ℝ) := hmk
    linarith
  · -- `hFv`: `𝔠 D' ≥ 𝔠 q = 4k + 1 ≥ 2m + 4`
    have hq : 𝔠 * ((4 * ((m + 1 + 1 : ℕ) : ℝ) + 1) / 𝔠) = 4 * ((m + 1 + 1 : ℕ) : ℝ) + 1 := by
      field_simp
    have h1 : (4 * ((m + 1 + 1 : ℕ) : ℝ) + 1) / 𝔠 ≤ D' := by rw [hD', hD'']; linarith
    have h2 := mul_le_mul_of_nonneg_left h1 h𝔠.le
    rw [hq] at h2
    rw [hkd] at h2
    linarith
  · -- `hexp`
    have hD'' : 2 * Cn + 2 + 2 * C₄ + ((m + 1 + 1 : ℕ) : ℝ) + (4 * ((m + 1 + 1 : ℕ) : ℝ) + 1) / 𝔠 ≤ D'' := by
      rw [hD'']
    exact altBudgetExpQN_of_choice (m + 1 + 1) C₄ Cn 𝔠 ε ε' τN D' D'' (((m + 1 + 1 : ℕ) : ℝ) + 1)
      (((m + 1 + 1 : ℕ) : ℝ) + 1) ε₁ e2 ε₁ hC₄ hCn h𝔠 he2 hε0 hεhalf hC₄ε hCnε hε'0.le hCnε'
      (by rw [hε₁]; linarith) (by rw [hε₁]; linarith) (by rw [hτN])
      (by rw [hD']; linarith) hD'' (by linarith) (by linarith)

/-! ## 6. The grid endpoint `altGridEndQN`

The statement is the pin `T2302_altGridEndQN` of `docs/tickets/checks/T2302-check.lean`, copied verbatim (script diff in the
report).  Exponents (fixed order): `Λg = 𝔡⁻¹`, `κ' = min κ (4/5)`, `KL = 1/𝔠`, `C₁ = (1 + 40 d(m+1)) 6^{d(m+1)}`,
`C₄ = qProxy4C d (m+2) Λg κ' KL`, `C_n = qProxyCn d (m+1) Λg KL C₁ (1/2)`, `ε₀' = min ε₀ 1`, `e₂ = ε₀'/2` (the budget runs at
`e₂`, C1b absorption), `ε = min (e₂/(8 max(C₄, C_n))) (1/2)`, `ε' = ε/2`, `τ' = min (ε/4) (e₂/(40 d m))`, `ε₁ = εq = e₂/40`,
`τ_N = e₂/8`, `D'' = 2C_n + 2 + 2C₄ + k + (4k+1)/𝔠`, `D' = D'' + 2`, `D_c = D'' + 1`, `τ_K = 1`, `D_Y = D_t = k + 1`,
`C_P^* = max_σ C_P(σ)`, `C_K = D₁ + 2C_P^* + 8k + 20 + D''`, `D₁' = D₁ + 1`, `C₀ = (8k+8)/𝔠` (`k = m + 2`). -/

/-- The small levels: `𝔏 = Λ^{1/2} + Φ₁ + Φ₂ + Φ₃ + X < N^{2k+2}` (`k = m + 2`; the level split of `§3`). -/
private def altGrid_small {d : ℕ} (sz : Sizes d) (Λ Φ₁ Φ₂ Φ₃ X : ℕ → ℝ) (m n : ℕ) : Prop :=
  Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n + X n < ((sz.size n : ℕ) : ℝ) ^ (2 * (m + 1 + 1) + 2)

/-- `N^p + 1 ≤ N^{p+1}` for `N ≥ 2`. -/
private theorem altGrid_pow_succ_le {N : ℝ} (hN2 : 2 ≤ N) (p : ℕ) : N ^ p + 1 ≤ N ^ (p + 1) := by
  have h1 : 1 ≤ N ^ p := one_le_pow₀ (by linarith)
  rw [pow_succ]
  nlinarith

theorem altGridEndQN :
  ∀ {d : ℕ} (sz : Sizes d) (κ 𝔠 τ 𝔡 : ℝ) (E s t : ℕ → ℝ),
    3 ≤ d → 0 < κ → 0 < 𝔠 → 0 < τ → 0 < 𝔡 →
    sz.SizeTendsto → sz.Bandwidth 𝔠 → sz.WO 𝔡 →
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    sz.STCaseI s t → sz.RangeCond τ t →
    (∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - t n) / (1 - s n)) →
    ∀ m : ℕ, 1 ≤ m →
    ∀ Λ Φ₁ Φ₂ Φ₃ X : ℕ → ℝ, (∀ n, 0 ≤ Λ n) → (∀ᶠ n : ℕ in atTop, 1 ≤ Λ n) →
      (∀ n, 0 ≤ Φ₁ n) → (∀ n, 0 ≤ Φ₂ n) → (∀ n, 0 ≤ Φ₃ n) → (∀ n, 1 ≤ X n) →
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
            sz.GoodSetN n (E n) (gridTime s v K n j) (m + 1 + 1) (((sz.size n : ℕ) : ℝ) ^ ε₁) (Λ n)
                (Φc n) τ' D' ∩
              GoodLinN sz n (E n) (gridTime s v K n j) (m + 1 + 1) (((sz.size n : ℕ) : ℝ) ^ ε₁)
                (Φ₁ n) (Φ₂ n) (Φ₃ n) ∩
              altYSetN sz n (E n) (gridTime s v K n j) (m + 1) (((sz.size n : ℕ) : ℝ) ^ ε₁ * X n)) →
          (∀ σ : Fin (m + 1 + 1) → Bool, σ (Fin.last (m + 1)) = !σ 0 →
            ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
              ‖STQop (d := d) (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) (s n)
                  (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
                    sz.STLKM n (E n) (s n) (pathH sz s v K n 0 ω) σ b) a‖ ≤
                ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ (m + 1 + 1)) →
          ∀ σ : Fin (m + 1 + 1) → Bool, σ (Fin.last (m + 1)) = !σ 0 →
            ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
              ‖sz.STLKM n (E n) (v n) (pathH sz s v K n (K n) ω) σ a‖ ≤
                ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n + X n) *
                  (sz.Bctl n (v n)) ^ (m + 1 + 1) := by
  intro d sz κ 𝔠 τ 𝔡 E s t hd hκ h𝔠 hτ h𝔡 hsize hband hWO hE hs0 hst ht1 hcase hrange hWt m hm
    Λ Φ₁ Φ₂ Φ₃ X hΛ0 hΛ1 hΦ₁ hΦ₂ hΦ₃ hX v hsv hvt ε₀ hε₀ D₁ hD₁
  classical
  have hd1 : 1 ≤ d := by omega
  have hv1 : ∀ n, v n < 1 := fun n => (hvt n).trans_lt (ht1 n)
  have hv0 : ∀ n, 0 ≤ v n := fun n => (hs0 n).trans (hsv n)
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith [abs_nonneg (E n)]
  have hk2 : 2 ≤ m + 1 + 1 := by omega
  -- the energy gap `κ' = min κ (4/5) ≤ Im m(E n)`, the window `0 < lam n ≤ Λg = 𝔡⁻¹`, `KL = 1/𝔠`
  obtain ⟨κ', hκ'def⟩ : ∃ κ' : ℝ, κ' = min κ (4 / 5) := ⟨_, rfl⟩
  obtain ⟨Λg, hΛgdef⟩ : ∃ Λg : ℝ, Λg = 𝔡⁻¹ := ⟨_, rfl⟩
  obtain ⟨KL, hKLdef⟩ : ∃ KL : ℝ, KL = 1 / 𝔠 := ⟨_, rfl⟩
  have hκ' : 0 < κ' := by rw [hκ'def]; exact lt_min hκ (by norm_num)
  have hκm : ∀ n, κ' ≤ (mE (E n)).im := fun n => by
    rw [hκ'def]; exact nqGood1_mE_im_ge hκ (hE n)
  have hΛg : 0 < Λg := by rw [hΛgdef]; exact inv_pos.2 h𝔡
  have hKL : 0 < KL := by rw [hKLdef]; positivity
  have hlam : ∀ᶠ n : ℕ in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λg := by
    rw [hΛgdef]
    filter_upwards [hWO] with n hn
    have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) hn.1, hn.2⟩
  have hKb : sz.STKbound E := stKbound_holds sz hd hκ hΛg hsize (Eventually.of_forall hE) hlam
  -- the range exponent of the end time, the `Y`-moment constant (one for all signs, before the grid)
  have hτR : 0 < min τ 1 := lt_min hτ one_pos
  have hτR1 : min τ 1 ≤ 1 := min_le_right _ _
  have hrangeV : sz.RangeCond (min τ 1) v := altGrid_rangeCond_mono sz (min_le_left _ _) hvt hrange
  obtain ⟨Cmax, hCmax0, hYmax⟩ := altGrid_yMomentsMax sz hκ hE hs0 hsv hv1 hsize hrangeV m
  -- the numerical constants, in the fixed order of the docstring
  have hC₁ : 0 < altGrid_C1 d m := by unfold altGrid_C1; positivity
  have hC₂0 : 0 ≤ altGrid_C2 d m := by unfold altGrid_C2; positivity
  have hC₄ : 0 < qProxy4C d (m + 1 + 1) Λg κ' KL := qProxy4C_pos hd hk2 hΛg hκ' hKL
  have hCn : 0 < qProxyCn d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2) :=
    qProxyCn_pos hd (m + 1) hΛg hKL hC₁ (by norm_num)
  obtain ⟨e0, he0def⟩ : ∃ e0 : ℝ, e0 = min ε₀ 1 := ⟨_, rfl⟩
  have he0 : 0 < e0 := by rw [he0def]; exact lt_min hε₀ one_pos
  have he01 : e0 ≤ 1 := by rw [he0def]; exact min_le_right _ _
  have he0le : e0 ≤ ε₀ := by rw [he0def]; exact min_le_left _ _
  obtain ⟨e2, he2def⟩ : ∃ e2 : ℝ, e2 = e0 / 2 := ⟨_, rfl⟩
  have he2 : 0 < e2 := by rw [he2def]; positivity
  have he2le : e2 ≤ 1 := by rw [he2def]; linarith
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (e2 / (8 * max (qProxy4C d (m + 1 + 1) Λg κ' KL)
      (qProxyCn d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2)))) (1 / 2) := ⟨_, rfl⟩
  obtain ⟨ε', hε'def⟩ : ∃ ε' : ℝ, ε' = ε / 2 := ⟨_, rfl⟩
  obtain ⟨τ', hτ'def⟩ : ∃ τ' : ℝ, τ' = min (ε / 4) (e2 / (40 * ((d : ℝ) * m))) := ⟨_, rfl⟩
  obtain ⟨ε₁, hε₁def⟩ : ∃ ε₁ : ℝ, ε₁ = e2 / 40 := ⟨_, rfl⟩
  obtain ⟨τN, hτNdef⟩ : ∃ τN : ℝ, τN = e2 / 8 := ⟨_, rfl⟩
  obtain ⟨D'', hD''def⟩ : ∃ D'' : ℝ, D'' = 2 * qProxyCn d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2) + 2 +
      2 * qProxy4C d (m + 1 + 1) Λg κ' KL + ((m + 1 + 1 : ℕ) : ℝ) +
        (4 * ((m + 1 + 1 : ℕ) : ℝ) + 1) / 𝔠 := ⟨_, rfl⟩
  obtain ⟨D', hD'def⟩ : ∃ D' : ℝ, D' = D'' + 2 := ⟨_, rfl⟩
  obtain ⟨Dc, hDcdef⟩ : ∃ Dc : ℝ, Dc = D'' + 1 := ⟨_, rfl⟩
  obtain ⟨C_K, hCKdef⟩ : ∃ C_K : ℝ, C_K = D₁ + 2 * Cmax + 8 * ((m + 1 + 1 : ℕ) : ℝ) + 20 + D'' :=
    ⟨_, rfl⟩
  have hA := altGrid_arith d m (C₄ := qProxy4C d (m + 1 + 1) Λg κ' KL)
    (Cn := qProxyCn d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2)) hd hm h𝔠 hC₄ hCn he2 he2le hD₁ hCmax0 hεdef
    hε'def hτ'def hε₁def hτNdef hD''def hD'def hDcdef hCKdef
  refine ⟨ε₁, τ', D', C_K, hA.hε₁0, hA.hτ'0, by linarith [hA.hD'1], hA.hCK0, ?_⟩
  intro Φc K hK0 hKN hKU
  -- the eventual regime facts
  have hη := altGrid_ev_hη sz hsize hκ' hκm hτR hrangeV
  have hN2ev : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hsize.eventually_ge_atTop 2
  have hWbig : ∀ T : ℝ, ∀ᶠ n : ℕ in atTop, T ≤ ((sz.W n : ℕ) : ℝ) := fun T => by
    filter_upwards [altGrid_ev_W_rpow_ge sz hsize h𝔠 hband one_pos T] with n hn
    rwa [Real.rpow_one] at hn
  have hWε : ∀ᶠ n : ℕ in atTop, 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε :=
    altGrid_ev_W_rpow_ge sz hsize h𝔠 hband hA.hε0 4
  have hWε' : ∀ᶠ n : ℕ in atTop, 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε' :=
    altGrid_ev_W_rpow_ge sz hsize h𝔠 hband hA.hε'0 4
  have hlog := altGrid_ev_hlog sz hd1 hsize h𝔠 hband hA.hε0
  have hNW : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ KL := by
    filter_upwards [hband] with n hn
    have := Sizes.size_rpow_le_W_rpow sz h𝔠 n hn (τ := 1) zero_le_one
    rwa [Real.rpow_one, ← hKLdef] at this
  have hdW1 : ∀ᶠ n : ℕ in atTop, (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε' := by
    filter_upwards [altGrid_ev_W_rpow_ge sz hsize h𝔠 hband (show 0 < ε / 4 by linarith [hA.hε0])
      (d : ℝ)] with n hn
    have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have hW0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by linarith
    calc (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (ε / 4) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hW1 hA.hτ'ε) (by positivity)
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ (ε / 4) * ((sz.W n : ℕ) : ℝ) ^ (ε / 4) :=
          mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hW0 _)
      _ = ((sz.W n : ℕ) : ℝ) ^ ε' := by
          rw [← Real.rpow_add' hW0 (by linarith [hA.hε0]), hε'def]; congr 1; ring
  have hdW2 : ∀ᶠ n : ℕ in atTop, (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ ε' ≤ ((sz.W n : ℕ) : ℝ) ^ ε := by
    filter_upwards [altGrid_ev_W_rpow_ge sz hsize h𝔠 hband (show 0 < ε / 2 by linarith [hA.hε0])
      (d : ℝ)] with n hn
    have hW0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
    calc (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ ε' = (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (ε / 2) := by rw [hε'def]
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ (ε / 2) * ((sz.W n : ℕ) : ℝ) ^ (ε / 2) :=
          mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hW0 _)
      _ = ((sz.W n : ℕ) : ℝ) ^ ε := by
          rw [← Real.rpow_add' hW0 (by linarith [hA.hε0])]; congr 1; ring
  have hDD : ∀ᶠ n : ℕ in atTop, 4 * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dc) := by
    filter_upwards [hWbig 4] with n hn
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
    have e : ((sz.W n : ℕ) : ℝ) ^ (-Dc) = ((sz.W n : ℕ) : ℝ) ^ (-D') * ((sz.W n : ℕ) : ℝ) := by
      rw [show -Dc = -D' + 1 by rw [hDcdef, hD'def]; ring, Real.rpow_add hW0, Real.rpow_one]
    rw [e]
    have : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D') := Real.rpow_nonneg hW0.le _
    nlinarith
  have hδ : ∀ᶠ n : ℕ in atTop, ∀ j < K n, ((sz.W n : ℕ) : ℝ) ^ (-D') +
      eeShiftErrN d (sz.L n) (sz.W n) (E n) (m + 1 + 1) (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤
        ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1)) := by
    filter_upwards [altGrid_ev_hδ sz hd1 hsize h𝔠 hband (m + 1 + 1) (D'' := D'' + 1) (C_K := C_K) hE2 hs0
      hsv hv1 hK0 hη (by linarith [hA.hD''0]) hA.hCKb hKN] with n hn j hj
    have h := hn j hj
    rwa [show -(D'' + 1 + 1) = -D' by rw [hD'def]; ring] at h
  have hνt : ∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ) ^ τ') ^ (d * m) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ := by
    refine Eventually.of_forall fun n => ?_
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := altGrid_one_le_size sz n
    have hW0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hWN : ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := altGrid_W_le_size sz hd1 n
    have hτ0 := hA.hτ'0.le
    calc (((sz.W n : ℕ) : ℝ) ^ τ') ^ (d * m)
        = ((sz.W n : ℕ) : ℝ) ^ (τ' * ((d : ℝ) * m)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hW0]; push_cast; ring_nf
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ' * ((d : ℝ) * m)) :=
          Real.rpow_le_rpow hW0 hWN (by positivity)
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ := Real.rpow_le_rpow_of_exponent_le hN1 hA.hτ'dm
  have hFv : ∀ᶠ n : ℕ in atTop, ((sz.W n : ℕ) : ℝ) ^ (-D') ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₁ * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹ := by
    filter_upwards [hband] with n hbn
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := altGrid_one_le_size sz n
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have h1 := altGrid_Wpow_le hN0 hbn (show -D' ≤ 0 by linarith [hA.hD'1])
    have h2 : ((sz.size n : ℕ) : ℝ) ^ (𝔠 * (-D')) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(2 * (m : ℝ) + 4)) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [hA.hFv])
    have h3 : ((sz.size n : ℕ) : ℝ) ^ (-(2 * (m : ℝ) + 4)) = (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹ := by
      rw [Real.rpow_neg hN0.le, show (2 * (m : ℝ) + 4) = ((2 * m + 4 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    have h4 : (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹ ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₁ * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹ :=
      le_mul_of_one_le_left (inv_nonneg.2 (by positivity)) (Real.one_le_rpow hN1 hA.hε₁0.le)
    exact h1.trans (h2.trans (h3.le.trans h4))
  have hMΛ : ∀ᶠ n : ℕ in atTop, (2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * (2 / Real.sqrt κ) *
      altGrid_C1 d m * (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τN := by
    filter_upwards [hsize.eventually (altGrid_ev_rpow_le (a := 2 * ε₁) (b := τN) hA.h2ε₁τN
      ((2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * (2 / Real.sqrt κ) * altGrid_C1 d m))),
      hsize.eventually_ge_atTop 1] with n hn hN1
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have e : (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 2 = ((sz.size n : ℕ) : ℝ) ^ (2 * ε₁) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; push_cast; ring_nf
    calc (2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * (2 / Real.sqrt κ) * altGrid_C1 d m *
          (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 2)
        = ((2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * (2 / Real.sqrt κ) * altGrid_C1 d m)) *
          ((sz.size n : ℕ) : ℝ) ^ (2 * ε₁) := by rw [e]; ring
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ τN := hn
  have hε₀e2 : 0 < ε₀ - e2 := by rw [he2def]; linarith
  have hfin : ∀ᶠ n : ℕ in atTop, 3 / 2 * ((sz.size n : ℕ) : ℝ) ^ e2 + ((sz.size n : ℕ) : ℝ) ^ τN ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ := by
    filter_upwards [hsize.eventually (altGrid_ev_rpow_le (a := 0) (b := ε₀ - e2) hε₀e2 3),
      hsize.eventually_ge_atTop 1] with n hn hN1
    rw [Real.rpow_zero, mul_one] at hn
    exact altGrid_fin_arith hN1 hA.hτNe2 hn
  have hun := altGrid_ev_union sz hsize (m + 1 + 1) D₁
  have hKcal := exists_norm_Kcal_le_win sz hsize E hKb hE2 v hv0 hv1 (m + 1 + 1) 1 one_pos
  have hθ0 : 0 ≤ 1 - min τ 1 := by linarith
  have hθ1 : 1 - min τ 1 ≤ 1 := by linarith
  obtain ⟨hC1, hC2, hC3, hC1', hC2', hC3'⟩ := hA.hCKθ (1 - min τ 1) hθ0 hθ1
  have hC4 : 1 - min τ 1 < C_K := by linarith [hA.hCK1]
  have hlogR := nqBudget_merged_inputs sz (κ := κ) (τ' := min τ 1) (τK := 1) (C_K := C_K)
    (D_t := ((m + 1 + 1 : ℕ) : ℝ) + 1) (E := E) (s := s) (v := v) (K := K) (m + 1 + 1) hκ hτR hτR1
    one_pos (by positivity) hk2 hsize hE hs0 hsv hv1 hK0 hrangeV hC1 hC2 hC3 hC4 hKN
  have hsumE := sum_weighted_qErrQN_le d sz (κ := κ) (τ' := min τ 1) (τK := 1) (C_K := C_K)
    (D_t := ((m + 1 + 1 : ℕ) : ℝ) + 1) (C := altGrid_C1 d m) (C₂ := altGrid_C2 d m) (E := E) (s := s)
    (t := v) (K := K) (m + 1) hC₁.le hC₂0 hκ hτR hτR1 one_pos (by positivity) (by omega) hsize hE hs0 hsv
    hv1 hK0 hrangeV hC1' hC2' hC3' hC4 hKN
  have hbudNum := altBudgetNumQN_eventually sz E m Λg κ' KL (altGrid_C1 d m) (1 / 2) 𝔠 ε ε' τN D' D''
    (((m + 1 + 1 : ℕ) : ℝ) + 1) (((m + 1 + 1 : ℕ) : ℝ) + 1) ε₁ e2 ε₁ (-(2 * ((m + 1 + 1 : ℕ) : ℝ) + 1))
    hd1 hsize hband hκ' (Eventually.of_forall hκm) hlam hA.hexp
  have hWt' : ∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - v n) / (1 - s n) := by
    filter_upwards [hWt] with n hn
    refine hn.trans ?_
    have h1 : 0 < 1 - s n := by linarith [hst n, ht1 n]
    exact div_le_div_of_nonneg_right (by linarith [hvt n]) h1.le
  have hwL : ∀ n, v n ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := fun n => by
    have := hcase n
    linarith [hvt n]
  -- the level split (`§3`): on the small levels the three quantities of the assembly are `≤ W^{C₀}`
  have hCr : ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ v n →
      ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
        ∀ σ : Fin (m + 1 + 1) → Bool,
          ‖fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => sz.STLKM n (E n) u H σ b‖ ≤
            ((sz.W n : ℕ) : ℝ) ^ (((8 * (m + 1 + 1) + 8 : ℕ) : ℝ) / 𝔠) := by
    filter_upwards [hη, hN2ev, hKcal, hband] with n hηn hN2n hKcaln hbn
    intro u hu0 huv H hH σ
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := altGrid_one_le_size sz n
    exact (altGrid_crude_N sz n (hE2 n) hk2 hKcaln (hv1 n) hηn hN2n hu0 huv hH σ).trans
      (altGrid_Npow_le_Wpow h𝔠 hN1 hbn (a := m + 1 + 1 + 2) (c := 8 * (m + 1 + 1) + 8) (by omega))
  have hMee : ∀ᶠ n : ℕ in atTop, altGrid_small sz Λ Φ₁ Φ₂ Φ₃ X m n → ∀ u : ℝ, 0 ≤ u → u ≤ v n →
      ((sz.size n : ℕ) : ℝ) ^ ε₁ * (((sz.size n : ℕ) : ℝ) ^ ε₁ * Λ n) *
        ((sz.Bctl n u) ^ (2 * (m + 1 + 1)) / etaT (E n) u) + ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1)) ≤
      ((sz.W n : ℕ) : ℝ) ^ (((8 * (m + 1 + 1) + 8 : ℕ) : ℝ) / 𝔠) := by
    filter_upwards [hη, hN2ev, hband, hWbig 1] with n hηn hN2n hbn hW1n
    intro hSn u hu0 huv
    unfold altGrid_small at hSn
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := altGrid_one_le_size sz n
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have hNvn := altGrid_Nv (hE2 n) (hv1 n) hN0 hηn
    obtain ⟨hηu0, hηu, hBu0, hBu⟩ := altGrid_u_facts sz n (hE2 n) (hv1 n) hu0 huv hηn hNvn
    have hΛh : 0 ≤ Λ n ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (hΛ0 n) _
    have hΛs : Λ n ^ ((1 : ℝ) / 2) < ((sz.size n : ℕ) : ℝ) ^ (2 * (m + 1 + 1) + 2) := by
      linarith only [hSn, hΦ₁ n, hΦ₂ n, hΦ₃ n, hX n]
    have hΛle : Λ n ≤ ((sz.size n : ℕ) : ℝ) ^ (4 * (m + 1 + 1) + 4) := by
      have e : Λ n = (Λ n ^ ((1 : ℝ) / 2)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (hΛ0 n)]; norm_num
      calc Λ n = (Λ n ^ ((1 : ℝ) / 2)) ^ 2 := e
        _ ≤ (((sz.size n : ℕ) : ℝ) ^ (2 * (m + 1 + 1) + 2)) ^ 2 := pow_le_pow_left₀ hΛh hΛs.le 2
        _ = ((sz.size n : ℕ) : ℝ) ^ (4 * (m + 1 + 1) + 4) := by rw [← pow_mul]; ring_nf
    have hΓ0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ := Real.rpow_nonneg hN0.le _
    have hΓN : ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.size n : ℕ) : ℝ) := by
      calc ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN1 hA.hε₁1
        _ = _ := Real.rpow_one _
    have h1 := altGrid_hMee_bound (m + 1 + 1) hN2n hΓ0 hΓN (hΛ0 n) hΛle hBu0.le hBu hηu0 hηu
    have h2 : ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hW1n (by linarith [hA.hD''0])
    have h3 := altGrid_pow_succ_le hN2n (8 * (m + 1 + 1) + 7)
    have h4 := altGrid_Npow_le_Wpow h𝔠 hN1 hbn (a := 8 * (m + 1 + 1) + 7 + 1) (c := 8 * (m + 1 + 1) + 8)
      le_rfl
    calc _ ≤ ((sz.size n : ℕ) : ℝ) ^ (8 * (m + 1 + 1) + 7) + 1 := by linarith only [h1, h2]
      _ ≤ _ := h3.trans h4
  have hDr : ∀ᶠ n : ℕ in atTop, altGrid_small sz Λ Φ₁ Φ₂ Φ₃ X m n → ∀ u : ℝ, 0 ≤ u → u ≤ v n →
      dDriftLinN sz n (E n) u (m + 1 + 1) (((sz.size n : ℕ) : ℝ) ^ ε₁) (Φ₁ n) (Φ₂ n) (Φ₃ n) ≤
        ((sz.W n : ℕ) : ℝ) ^ (((8 * (m + 1 + 1) + 8 : ℕ) : ℝ) / 𝔠) := by
    filter_upwards [hη, hN2ev, hband] with n hηn hN2n hbn
    intro hSn u hu0 huv
    unfold altGrid_small at hSn
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := altGrid_one_le_size sz n
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have hNvn := altGrid_Nv (hE2 n) (hv1 n) hN0 hηn
    obtain ⟨hηu0, hηu, hBu0, hBu⟩ := altGrid_u_facts sz n (hE2 n) (hv1 n) hu0 huv hηn hNvn
    have hΛh : 0 ≤ Λ n ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (hΛ0 n) _
    have hΓ0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ := Real.rpow_nonneg hN0.le _
    have hΓN : ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.size n : ℕ) : ℝ) := by
      calc ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN1 hA.hε₁1
        _ = _ := Real.rpow_one _
    have h1 := altGrid_dDrift_bound (k := m + 1 + 1) hk2 hN2n hΓ0 hΓN (hΦ₁ n) (hΦ₂ n) (hΦ₃ n)
      (by linarith only [hSn, hΛh, hΦ₂ n, hΦ₃ n, hX n]) (by linarith only [hSn, hΛh, hΦ₁ n, hΦ₃ n, hX n])
      (by linarith only [hSn, hΛh, hΦ₁ n, hΦ₂ n, hX n]) hBu0.le hBu hηu0 hηu
    have h4 := altGrid_Npow_le_Wpow h𝔠 hN1 hbn (a := 8 * (m + 1 + 1) + 7) (c := 8 * (m + 1 + 1) + 8)
      (by omega)
    exact h1.trans h4
  have hsum : ∀ᶠ n : ℕ in atTop, ∀ p ≤ K n,
      ∑ j ∈ Finset.range p, (1 + (1 - gridTime s v K n p)⁻¹) ^ (m + 1 + 1) *
          qErrQN sz E s v K n (m + 1) (altGrid_C1 d m) (altGrid_C2 d m) (((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) *
            (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ (m + 1 + 1)) j ≤
        ((sz.size n : ℕ) : ℝ) ^ (-(((m + 1 + 1 : ℕ) : ℝ) + 1)) := hsumE
  have hAsm := altGrid_assembly sz m hd hm hκ hE hs0 hsv hv1 hK0 hsize hKb Λ Φc Φ₁ Φ₂ Φ₃ X hΛ0 hΦ₁ hΦ₂
    hΦ₃ hX (Λg := Λg) (κ' := κ') (KL := KL) (ε := ε) (ε' := ε') (τ' := τ') (τN := τN) (D' := D')
    (D'' := D'') (Dc := Dc) (ε₁ := ε₁) (εq := ε₁) (τK := 1) (D_Y := ((m + 1 + 1 : ℕ) : ℝ) + 1)
    (D_t := ((m + 1 + 1 : ℕ) : ℝ) + 1) (D₁ := D₁ + 1) (C_P := Cmax) (C_K := C_K)
    (C₀ := ((8 * (m + 1 + 1) + 8 : ℕ) : ℝ) / 𝔠) hΛg hκ' hKL hκm hA.hε0 hA.hε1 hA.hε'0 hA.hε'1 hA.hε'ε
    hA.hτ'0.le hA.hε₁0.le hA.hε₁1 hA.hD'1 hA.hDc1 (by positivity) hA.hε₁0 one_pos hA.hCK0
    (by positivity) hA.hCKa hA.hD hKN hKU (hYmax K hK0) hwL hWt' hlam (hWbig 4) hWε hWε' hlog hNW hdW1 hdW2 hDD
    hδ (hWbig _) (hWbig _) hWbig hη hνt hFv hMΛ (altGrid_small sz Λ Φ₁ Φ₂ Φ₃ X m) hMee hDr hCr hsum
  filter_upwards [hAsm, hη, hlogR, hbudNum, hΛ1, hun, hKN, hKcal, hfin, hN2ev, hlam, hWbig 4, hνt, hFv, hMΛ]
    with n hAsmn hηn hlogRn hbudn hΛ1n hunn hKNn hKcaln hfinn hN2n hlamn hW4n hνtn hFvn hMΛn
  obtain ⟨hg, hgΛ⟩ := hlamn
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := altGrid_one_le_size sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hEn2 : |E n| < 2 := hE2 n
  have hKn : K n ≠ 0 := hK0 n
  have hvs : v n - s n ≤ 1 := by linarith [hv1 n, hs0 n]
  have hW1 : (1 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hNvn : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - v n := altGrid_Nv hEn2 (hv1 n) hN0 hηn
  have hBv : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ sz.Bctl n (v n) :=
    ContinuityNet.cont_inv_size_le_Bctl sz n (hv0 n) (hv1 n)
  have hBv0 : 0 < sz.Bctl n (v n) := STBctl_pos sz n (hv1 n)
  have hBk0 : 0 ≤ (sz.Bctl n (v n)) ^ (m + 1 + 1) := pow_nonneg hBv0.le _
  have hΛh1 : 1 ≤ Λ n ^ ((1 : ℝ) / 2) := Real.one_le_rpow hΛ1n (by norm_num)
  have h𝔏1 : 1 ≤ Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n + X n := by
    linarith only [hΛh1, hΦ₁ n, hΦ₂ n, hΦ₃ n, hX n]
  have h𝔏0 : 0 ≤ Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n + X n := by linarith only [h𝔏1]
  have hν1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ := Real.one_le_rpow hN1 hA.hε₁0.le
  have hνN : ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.size n : ℕ) : ℝ) := by
    calc ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 hA.hε₁1
      _ = _ := Real.rpow_one _
  have hϑ : STMollifierProps (d := d) (sz.lam n) (altGrid_C1 d m) (1 / 2)
      (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) :=
    QopAlgebra_mollifier_props d (sz.L n) (m + 1) (sz.three_le_L n) hg
  by_cases hbig : ((sz.size n : ℕ) : ℝ) ^ (2 * (m + 1 + 1) + 2) ≤
      Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n + X n
  · -- the big levels: the conclusion follows from the level-free crude bound
    refine ⟨Set.univ, ?_, fun ω _ hgood _ σ hσ a => ?_⟩
    · rw [Set.compl_univ]
      simp only [measureReal_empty]
      exact Real.rpow_nonneg hN0.le _
    · have hH : (pathH sz s v K n (K n) ω).IsHermitian := (hgood (K n) le_rfl).1.1.1
      have hcr := altGrid_crude_N sz n hEn2 hk2 hKcaln (hv1 n) hηn hN2n (hv0 n) le_rfl hH σ
      exact (norm_le_pi_norm (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
        sz.STLKM n (E n) (v n) (pathH sz s v K n (K n) ω) σ b) a).trans
        (hcr.trans (altGrid_big_case (m + 1 + 1) hN1 hε₀.le hBv hbig))
  · have hS : altGrid_small sz Λ Φ₁ Φ₂ Φ₃ X m n := not_le.1 hbig
    by_cases hsvn : s n = v n
    · -- the collapsed window `v_n = s_n`: `G = univ`; de-`𝒬` at `u = s_n = v_n`
      refine ⟨Set.univ, ?_, fun ω _ hgood hinit σ hσ a => ?_⟩
      · rw [Set.compl_univ]
        simp only [measureReal_empty]
        exact Real.rpow_nonneg hN0.le _
      · rw [altGrid_pathH_collapse sz hsvn (K n) ω, ← hsvn]
        have hg0 := hgood 0 (Nat.zero_le _)
        rw [ST_gridTime_zero s v K n] at hg0
        have hs1 : s n < 1 := by rw [hsvn]; exact hv1 n
        have hNs : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - s n := by rw [hsvn]; exact hNvn
        have hunQ := altEnd_unQ hd m sz n (E n) (s n) κ (((sz.size n : ℕ) : ℝ) ^ ε₁) (Λ n) (Φc n) τ' D'
          (((sz.size n : ℕ) : ℝ) ^ ε₁) (X n) τN (altGrid_C1 d m) (1 / 2)
          (pathH sz s v K n 0 ω) σ (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) hκ (hE n) (hs0 n)
          hs1 hg hNs hW1 hA.hτ'0.le hν1 (hX n) hνtn hνN hFvn hC₁ (by norm_num) hMΛn hϑ hg0.1.1 hg0.2 hσ a
        have hinit' := hinit σ hσ a
        have hBks0 : 0 ≤ (sz.Bctl n (s n)) ^ (m + 1 + 1) :=
          pow_nonneg (STBctl_pos sz n hs1).le _
        have hN12 : ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.size n : ℕ) : ℝ) ^ e2 :=
          Real.rpow_le_rpow_of_exponent_le hN1 hA.hε₁e2
        have hR : ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ (m + 1 + 1) ≤
            ((sz.size n : ℕ) : ℝ) ^ e2 * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n + X n) *
              (sz.Bctl n (s n)) ^ (m + 1 + 1) := by
          refine mul_le_mul_of_nonneg_right ?_ hBks0
          exact hN12.trans (le_mul_of_one_le_right (Real.rpow_nonneg hN0.le _) h𝔏1)
        have hDt0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ e2 * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n + X n) *
            (sz.Bctl n (s n)) ^ (m + 1 + 1) / 2 :=
          div_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hN0.le _) h𝔏0) hBks0) (by norm_num)
        refine altGrid_final_arith (Q := ‖STQop (d := d) (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n))
          (s n) (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
            sz.STLKM n (E n) (s n) (pathH sz s v K n 0 ω) σ b) a‖)
          (R := ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ (m + 1 + 1)) (Dt := 0)
          (A := ((sz.size n : ℕ) : ℝ) ^ τN) hBks0 (by linarith only [h𝔏1, hΛh1, hΦ₁ n, hΦ₂ n, hΦ₃ n])
          h𝔏0 (Real.rpow_nonneg hN0.le _) hunQ (by linarith only [hinit']) hR hDt0 hfinn
    · -- the non-collapsed window: one event per alternating sign vector
      have hlt : s n < v n := lt_of_le_of_ne (hsv n) hsvn
      have hAsmσ := fun σ : {σ : Fin (m + 1 + 1) → Bool // σ (Fin.last (m + 1)) = !σ 0} =>
        hAsmn hS σ.1 σ.2 hlt
      choose Gs hGsP hGsb using hAsmσ
      refine ⟨⋂ σ, Gs σ, ?_, ?_⟩
      · -- the union bound over the `≤ 2^k` sign vectors
        have hcompl : (⋂ σ, Gs σ)ᶜ = ⋃ σ, (Gs σ)ᶜ := by rw [Set.compl_iInter]
        rw [hcompl]
        calc (pathP sz).real (⋃ σ, (Gs σ)ᶜ) ≤ ∑ σ, (pathP sz).real (Gs σ)ᶜ :=
              measureReal_iUnion_fintype_le _
          _ ≤ ∑ _σ : {σ : Fin (m + 1 + 1) → Bool // σ (Fin.last (m + 1)) = !σ 0},
                ((sz.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) := Finset.sum_le_sum fun σ _ => hGsP σ
          _ = (Fintype.card {σ : Fin (m + 1 + 1) → Bool // σ (Fin.last (m + 1)) = !σ 0} : ℝ) *
                ((sz.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) := by simp
          _ ≤ (2 : ℝ) ^ (m + 1 + 1) * ((sz.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) := by
              refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hN0.le _)
              have h1 := Fintype.card_subtype_le
                (fun σ : Fin (m + 1 + 1) → Bool => σ (Fin.last (m + 1)) = !σ 0)
              have h2 : Fintype.card (Fin (m + 1 + 1) → Bool) = 2 ^ (m + 1 + 1) := by simp
              rw [h2] at h1
              exact_mod_cast h1
          _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) := hunn
      · intro ω hω hgood hinit σ hσ a
        have hωσ : ω ∈ Gs ⟨σ, hσ⟩ := Set.mem_iInter.1 hω ⟨σ, hσ⟩
        have hb := hGsb ⟨σ, hσ⟩ ω hωσ hgood a
        have hX0 : (Finset.univ.sup' Finset.univ_nonempty fun b =>
            ‖aTrueQN sz E s v K n (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ 0 ω b‖) ≤
            ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ (m + 1 + 1) := by
          refine Finset.sup'_le _ _ fun b _ => ?_
          have h := hinit σ hσ b
          have h0 : AvecN sz E s v K n 0 σ ω =
              fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
                sz.STLKM n (E n) (s n) (pathH sz s v K n 0 ω) σ b := by
            funext b
            simp only [AvecN, ST_gridTime_zero]
          have e : aTrueQN sz E s v K n (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ 0 ω b =
              STQop (d := d) (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) (s n)
                (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
                  sz.STLKM n (E n) (s n) (pathH sz s v K n 0 ω) σ b) b := by
            simp only [aTrueQN, ST_gridTime_zero, h0]
          rw [e]
          exact h
        obtain ⟨ha1, ha2, ha3, he0', he1, he2', he3, he4⟩ := hbudn
        have hη0 : 0 ≤ (etaT (E n) (v n))⁻¹ := inv_nonneg.2 (etaT_pos hEn2 (hv1 n)).le
        have hΔη := altGrid_hΔη sz (C_K := C_K) (η := etaT (E n) (v n)) hA.hCK1 hKNn hvs hη0 hηn
        have hdd : ∀ j < K n, dDriftAltLinQN sz n (E n) (gridTime s v K n j) m
            (((sz.size n : ℕ) : ℝ) ^ ε₁) (Φ₁ n) (Φ₂ n) (Φ₃ n)
            (qProxyCn d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2)) ε' D' τN (X n) ≤
            (((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2) * ε') *
              (((sz.size n : ℕ) : ℝ) ^ ε₁ * ((sz.size n : ℕ) : ℝ) ^ ε₁) * ((m + 1 + 1 : ℕ) : ℝ) +
                ((sz.size n : ℕ) : ℝ) ^ τN) * (Φ₁ n + Φ₂ n + Φ₃ n + X n) *
              ((sz.Bctl n (gridTime s v K n j)) ^ (m + 1 + 1) / etaT (E n) (gridTime s v K n j)) +
            ((sz.W n : ℕ) : ℝ) ^ (-D' + qProxyCn d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2)) := by
          intro j hj
          have hj1 : j ≤ K n := hj.le
          exact dDriftAltLinQN_le_shape sz n (E n) (gridTime s v K n j) m _ (Φ₁ n) (Φ₂ n) (Φ₃ n) _ ε' D' τN
            (X n) hEn2 ((altGrid_gridTime_le (hsv n) hKn hj1).trans_lt (hv1 n)) (hΦ₁ n) (hΦ₂ n) (hΦ₃ n)
            (by linarith only [hX n])
        have hbud := budgetAltQN sz E s v K n m Λg κ' KL (altGrid_C1 d m) (1 / 2) ε
          (fun n => ((sz.size n : ℕ) : ℝ) ^ ε₁) Λ
          (fun j => dDriftAltLinQN sz n (E n) (gridTime s v K n j) m (((sz.size n : ℕ) : ℝ) ^ ε₁)
            (Φ₁ n) (Φ₂ n) (Φ₃ n) (qProxyCn d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2)) ε' D' τN (X n))
          (((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2) * ε') *
              (((sz.size n : ℕ) : ℝ) ^ ε₁ * ((sz.size n : ℕ) : ℝ) ^ ε₁) * ((m + 1 + 1 : ℕ) : ℝ) +
                ((sz.size n : ℕ) : ℝ) ^ τN)
          (Φ₁ n + Φ₂ n + Φ₃ n + X n)
          (((sz.W n : ℕ) : ℝ) ^ (-D' + qProxyCn d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2)))
          (2 * ((sz.W n : ℕ) : ℝ) ^ (-D')) (4 * ((sz.W n : ℕ) : ℝ) ^ (-D')) D''
          (((m + 1 + 1 : ℕ) : ℝ) + 1) (((m + 1 + 1 : ℕ) : ℝ) + 1) 1 ε₁ e2 ε₁
          (Finset.univ.sup' Finset.univ_nonempty fun b =>
            ‖aTrueQN sz E s v K n (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ 0 ω b‖) a
          hA.hε₁0.le hEn2 (hs0 n) (hsv n) (hv1 n) hKn hηn hΔη rfl hΛ1n (by positivity)
          (by linarith only [hΦ₁ n, hΦ₂ n, hΦ₃ n, hX n]) (by positivity) (by positivity) (by positivity)
          hdd hlogRn.1 hX0 hlogRn.2 ha1 ha2 ha3 he0' he1 he2' he3 he4
        have hdt := altGrid_Dt_absorb (m + 1 + 1) hN2n he2.le hBv h𝔏1
        have hunQ := altEnd_unQ hd m sz n (E n) (v n) κ (((sz.size n : ℕ) : ℝ) ^ ε₁) (Λ n) (Φc n) τ' D'
          (((sz.size n : ℕ) : ℝ) ^ ε₁) (X n) τN (altGrid_C1 d m) (1 / 2)
          (pathH sz s v K n (K n) ω) σ (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) hκ (hE n)
          (hv0 n) (hv1 n) hg hNvn hW1 hA.hτ'0.le hν1 (hX n) hνtn hνN hFvn hC₁ (by norm_num) hMΛn hϑ
          (by have := (hgood (K n) le_rfl).1.1; rwa [gridTime_last s v K n hKn] at this)
          (by have := (hgood (K n) le_rfl).2; rwa [gridTime_last s v K n hKn] at this) hσ a
        have h0K : AvecN sz E s v K n (K n) σ ω =
            fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
              sz.STLKM n (E n) (v n) (pathH sz s v K n (K n) ω) σ b := by
          funext b
          simp only [AvecN, gridTime_last s v K n hKn]
        have e : aTrueQN sz E s v K n (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ (K n) ω a =
            STQop (d := d) (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) (v n)
              (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
                sz.STLKM n (E n) (v n) (pathH sz s v K n (K n) ω) σ b) a := by
          simp only [aTrueQN, gridTime_last s v K n hKn, h0K]
        rw [e] at hb
        have e𝔏 : Λ n ^ ((1 : ℝ) / 2) + (Φ₁ n + Φ₂ n + Φ₃ n + X n) =
            Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n + X n := by ring
        rw [e𝔏] at hbud
        refine altGrid_final_arith (Q := ‖STQop (d := d) (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n))
          (v n) (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
            sz.STLKM n (E n) (v n) (pathH sz s v K n (K n) ω) σ b) a‖) hBk0
          (by linarith only [h𝔏1, hΛh1, hΦ₁ n, hΦ₂ n, hΦ₃ n]) h𝔏0 (Real.rpow_nonneg hN0.le _) hunQ hb hbud
          ?_ hfinn
        exact hdt

/-! ## 7. Compiled nonempty instances (namespace `QEndGridInst`)

The merged admissible sequence `sz0` (`d = 3`; `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`; `sz0_tendsto`,
`sz0_bandwidth` `𝔠 = 1/6`, `sz0_WO` `𝔡 = 1/10`) at `E ≡ 0` (`κ = 1`), `s ≡ 0`, `t ≡ 1/2`, `τ = 1/2`
(`RangeCond (1/2) t` is `rangeCond_half`), the non-collapsed end time `v ≡ 1/2` and the collapsed one `v ≡ 0`, levels
`Λ ≡ Φ₁ ≡ Φ₂ ≡ Φ₃ ≡ X ≡ Φc ≡ 1`, `ε₀ = 1/10`, `D₁ = 1`, every `m ≥ 1`; the grid is `agK C_K n = max 1 ⌈N^{C_K}⌉`
(so `N^{C_K} ≤ K_n ≤ ⌈N^{C_K}⌉`).  The constants `C₄`, `C_n`, `C_P` stay abstract, so every instance holds for the actual
constants.  Items: (1) the `lam` patch (`sz0` and `sz0.withLam 0`); (2) the level split (`n = 4`: small levels, big levels, the
crude bound at an `n` of the `𝒦`-envelope); (3) `altGridEndQN` at the data, every structural premise discharged, unfolded at the
grid; (4) the collapsed window; (5) the pinned statement.  The good-walk and initial hypotheses stay in the conclusion
(made non-vacuous in S3-18b1). -/

namespace QEndGridInst

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Ind.GridEnvelopeNCheck

/-- `E ≡ 0`. -/
abbrev agE : ℕ → ℝ := fun _ => 0
/-- `s ≡ 0`. -/
abbrev agS : ℕ → ℝ := fun _ => 0
/-- `t ≡ 1/2`. -/
abbrev agT : ℕ → ℝ := fun _ => 1 / 2
/-- The non-collapsed end time `v ≡ 1/2` (`s < v`). -/
abbrev agV : ℕ → ℝ := fun _ => 1 / 2
/-- The collapsed end time `v ≡ 0 = s`. -/
abbrev agC : ℕ → ℝ := fun _ => 0
/-- The levels `Λ = Φ₁ = Φ₂ = Φ₃ = X = Φc ≡ 1`. -/
abbrev agOne : ℕ → ℝ := fun _ => 1

private theorem sz0_facts (n : ℕ) :
    ((sz0.W n : ℕ) : ℝ) = (2 * ((n : ℝ) + 1)) ^ 5 ∧ ((sz0.L n : ℕ) : ℝ) = 2 * (2 * ((n : ℝ) + 1)) ∧
      sz0.lam n = ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ := by
  refine ⟨?_, ?_, rfl⟩
  · simp [sz0]
  · simp [sz0]; ring

private theorem sz0_lam_pos (n : ℕ) : 0 < sz0.lam n := by
  change 0 < ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹
  positivity

private theorem sz0_lam_le_one (n : ℕ) : sz0.lam n ≤ 1 := by
  change ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ ≤ 1
  have hx1 : (1 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  exact inv_le_one_of_one_le₀ (one_le_pow₀ hx1)

private theorem sz0_L_ge_four (n : ℕ) : (4 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := by
  have h : (4 : ℕ) ≤ sz0.L n := by change 4 ≤ 4 * (n + 1); omega
  exact_mod_cast h

/-- Case (i) at the data: `lam²/L² ≤ 1/16 ≤ 1 - t = 1/2`. -/
theorem agCaseI : sz0.STCaseI agS agT := fun n => by
  have hl1 := sz0_lam_le_one n
  have hl0 := sz0_lam_pos n
  have hL4 := sz0_L_ge_four n
  have h : sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 ≤ 1 / 16 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  change sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 ≤ 1 - 1 / 2
  linarith

theorem agE_abs (n : ℕ) : |agE n| ≤ 2 - 1 := by norm_num [agE]

/-- The window hypothesis `W⁻¹ ≤ (1-t)/(1-s) = 1/2` (`W ≥ 32`). -/
theorem agWt : ∀ᶠ n : ℕ in atTop, (((sz0.W n : ℕ) : ℝ))⁻¹ ≤ (1 - agT n) / (1 - agS n) :=
  Eventually.of_forall fun n => by
    have h := W_ge_32 n
    have : (((sz0.W n : ℕ) : ℝ))⁻¹ ≤ (32 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h
    refine this.trans ?_
    norm_num [agT, agS]

theorem agS_nonneg : ∀ n, 0 ≤ agS n := fun n => by norm_num [agS]
theorem agS_le_agT : ∀ n, agS n ≤ agT n := fun n => by norm_num [agS, agT]
theorem agT_lt_one : ∀ n, agT n < 1 := fun n => by norm_num [agT]
theorem agS_le_agV : ∀ n, agS n ≤ agV n := fun n => by norm_num [agS, agV]
theorem agV_le_agT : ∀ n, agV n ≤ agT n := fun n => by norm_num [agV, agT]
theorem agS_le_agC : ∀ n, agS n ≤ agC n := fun n => by norm_num [agS, agC]
theorem agC_le_agT : ∀ n, agC n ≤ agT n := fun n => by norm_num [agC, agT]

/-- The grid of the instances: `N^{C_K} ≤ K_n ≤ ⌈N^{C_K}⌉` (copy of `NQEndLinInst.KC`, `NQEndLin.lean:1346`). -/
def agK (C_K : ℝ) (n : ℕ) : ℕ := max 1 ⌈((sz0.size n : ℕ) : ℝ) ^ C_K⌉₊

theorem agK_ne_zero (C_K : ℝ) (n : ℕ) : agK C_K n ≠ 0 := by
  unfold agK
  exact Nat.pos_iff_ne_zero.1 (lt_of_lt_of_le one_pos (le_max_left _ _))

theorem agK_low (C_K : ℝ) (n : ℕ) : ((sz0.size n : ℕ) : ℝ) ^ C_K ≤ (agK C_K n : ℝ) := by
  unfold agK
  have h : ((sz0.size n : ℕ) : ℝ) ^ C_K ≤ (⌈((sz0.size n : ℕ) : ℝ) ^ C_K⌉₊ : ℝ) := Nat.le_ceil _
  exact h.trans (by exact_mod_cast le_max_right _ _)

theorem agK_up (C_K : ℝ) (n : ℕ) : agK C_K n ≤ ⌈((sz0.size n : ℕ) : ℝ) ^ C_K⌉₊ := by
  unfold agK
  have hN : (0 : ℝ) < ((sz0.size n : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (by have := sz0.one_le_size n; omega)
  exact max_le (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hN _)) le_rfl

/-- The non-collapsed window is not collapsed: `s_n = 0 < 1/2 = v_n`, so `Δ = (v_n - s_n)/K_n > 0` on every grid. -/
theorem window_nondegenerate (C_K : ℝ) (n : ℕ) :
    agS n < agV n ∧ 0 < gridStep agS agV (agK C_K) n := by
  refine ⟨by norm_num [agS, agV], ?_⟩
  have hK : (0 : ℝ) < (agK C_K n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero (agK_ne_zero _ n))
  exact div_pos (by norm_num [agV, agS]) hK

/-- The collapsed window is collapsed: `s_n = v_n`, `Δ = 0`. -/
theorem window_collapsed (C_K : ℝ) (n : ℕ) : agS n = agC n ∧ gridStep agS agC (agK C_K) n = 0 := by
  refine ⟨by norm_num [agS, agC], ?_⟩
  unfold gridStep
  norm_num [agS, agC]

/-! ### (5) The pinned statement (copy of `docs/tickets/checks/T2302-check.lean` §2, `T2302_altGridEndQN`) -/

private def T2302_altGridEndQN : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (κ 𝔠 τ 𝔡 : ℝ) (E s t : ℕ → ℝ),
    3 ≤ d → 0 < κ → 0 < 𝔠 → 0 < τ → 0 < 𝔡 →
    sz.SizeTendsto → sz.Bandwidth 𝔠 → sz.WO 𝔡 →
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    sz.STCaseI s t → sz.RangeCond τ t →
    (∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - t n) / (1 - s n)) →
    ∀ m : ℕ, 1 ≤ m →
    ∀ Λ Φ₁ Φ₂ Φ₃ X : ℕ → ℝ, (∀ n, 0 ≤ Λ n) → (∀ᶠ n : ℕ in atTop, 1 ≤ Λ n) →
      (∀ n, 0 ≤ Φ₁ n) → (∀ n, 0 ≤ Φ₂ n) → (∀ n, 0 ≤ Φ₃ n) → (∀ n, 1 ≤ X n) →
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
            sz.GoodSetN n (E n) (gridTime s v K n j) (m + 1 + 1) (((sz.size n : ℕ) : ℝ) ^ ε₁) (Λ n)
                (Φc n) τ' D' ∩
              GoodLinN sz n (E n) (gridTime s v K n j) (m + 1 + 1) (((sz.size n : ℕ) : ℝ) ^ ε₁)
                (Φ₁ n) (Φ₂ n) (Φ₃ n) ∩
              altYSetN sz n (E n) (gridTime s v K n j) (m + 1) (((sz.size n : ℕ) : ℝ) ^ ε₁ * X n)) →
          (∀ σ : Fin (m + 1 + 1) → Bool, σ (Fin.last (m + 1)) = !σ 0 →
            ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
              ‖STQop (d := d) (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) (s n)
                  (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
                    sz.STLKM n (E n) (s n) (pathH sz s v K n 0 ω) σ b) a‖ ≤
                ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ (m + 1 + 1)) →
          ∀ σ : Fin (m + 1 + 1) → Bool, σ (Fin.last (m + 1)) = !σ 0 →
            ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
              ‖sz.STLKM n (E n) (v n) (pathH sz s v K n (K n) ω) σ a‖ ≤
                ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n + X n) *
                  (sz.Bctl n (v n)) ^ (m + 1 + 1)

/-- **Instance (5)**: the pinned statement is proved by `altGridEndQN`. -/
example : T2302_altGridEndQN := @altGridEndQN


/-! ### (3) `altGridEndQN` at the data, non-collapsed window; (4) the collapsed window -/

/-- **`altGridEndQN` at the data** (`m ≥ 1` arbitrary, so tensors of `m + 2 ≥ 3` indices; no hypothesis is left: `STKbound`
is internal, the good-walk and initial hypotheses stay in the conclusion).  The theorem is applied at `sz = sz0`,
`κ = 1`, `𝔠 = 1/6`, `τ = 1/2`, `𝔡 = 1/10`, `E = 0`, `(s, t) = (0, 1/2)` (`agCaseI`, `rangeCond_half`, `agWt`), levels
`Λ = Φ₁ = Φ₂ = Φ₃ = X = Φc = 1`, `v ≡ 1/2` (`s < v`, `Δ > 0`: `window_nondegenerate`), `ε₀ = 1/10`, `D₁ = 1`; the
conclusion is unfolded at the grid `agK C_K` (`N^{C_K} ≤ K_n ≤ ⌈N^{C_K}⌉`) for the exponents the theorem produces, at one
size index. -/
theorem altGrid_instance (m : ℕ) (hm : 1 ≤ m) :
    ∃ ε₁ τ' D' C_K : ℝ, 0 < ε₁ ∧ 0 < τ' ∧ 0 < D' ∧ 0 ≤ C_K ∧
      ∃ n : ℕ, ∃ G : Set (PathΩ sz0), (pathP sz0).real Gᶜ ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ∧
        ∀ ω ∈ G,
          (∀ j ≤ agK C_K n, pathH sz0 agS agV (agK C_K) n j ω ∈
            sz0.GoodSetN n (agE n) (gridTime agS agV (agK C_K) n j) (m + 1 + 1)
                (((sz0.size n : ℕ) : ℝ) ^ ε₁) 1 1 τ' D' ∩
              GoodLinN sz0 n (agE n) (gridTime agS agV (agK C_K) n j) (m + 1 + 1)
                (((sz0.size n : ℕ) : ℝ) ^ ε₁) 1 1 1 ∩
              altYSetN sz0 n (agE n) (gridTime agS agV (agK C_K) n j) (m + 1)
                (((sz0.size n : ℕ) : ℝ) ^ ε₁ * 1)) →
          (∀ σ : Fin (m + 1 + 1) → Bool, σ (Fin.last (m + 1)) = !σ 0 →
            ∀ a : Fin (m + 1 + 1) → Zd 3 (sz0.L n),
              ‖STQop (d := 3) (QopAlgebra_mollifier 3 (sz0.L n) (m + 1) (sz0.lam n)) (agS n)
                  (fun b : Fin (m + 1 + 1) → Zd 3 (sz0.L n) =>
                    sz0.STLKM n (agE n) (agS n) (pathH sz0 agS agV (agK C_K) n 0 ω) σ b) a‖ ≤
                ((sz0.size n : ℕ) : ℝ) ^ ε₁ * (sz0.Bctl n (agS n)) ^ (m + 1 + 1)) →
          ∀ σ : Fin (m + 1 + 1) → Bool, σ (Fin.last (m + 1)) = !σ 0 →
            ∀ a : Fin (m + 1 + 1) → Zd 3 (sz0.L n),
              ‖sz0.STLKM n (agE n) (agV n) (pathH sz0 agS agV (agK C_K) n (agK C_K n) ω) σ a‖ ≤
                ((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * ((1 : ℝ) ^ ((1 : ℝ) / 2) + 1 + 1 + 1 + 1) *
                  (sz0.Bctl n (agV n)) ^ (m + 1 + 1) := by
  obtain ⟨ε₁, τ', D', C_K, h1, h2, h3, h4, hend⟩ := altGridEndQN sz0 1 (1 / 6) (1 / 2) (1 / 10)
    agE agS agT (by norm_num) one_pos (by norm_num) (by norm_num) (by norm_num) sz0_tendsto
    sz0_bandwidth sz0_WO agE_abs agS_nonneg agS_le_agT agT_lt_one agCaseI rangeCond_half agWt m hm
    agOne agOne agOne agOne agOne (fun _ => by norm_num) (Eventually.of_forall fun _ => le_rfl)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => le_rfl) agV
    agS_le_agV agV_le_agT (1 / 10) (by norm_num) 1 one_pos
  refine ⟨ε₁, τ', D', C_K, h1, h2, h3, h4, ?_⟩
  obtain ⟨n, G, hG, hGb⟩ := (hend agOne (agK C_K) (agK_ne_zero C_K)
    (Eventually.of_forall (agK_low C_K)) (Eventually.of_forall (agK_up C_K))).exists
  exact ⟨n, G, hG, hGb⟩

/-- **`altGridEndQN` at the data, collapsed window** `v = s = 0` (`Δ = 0`: `window_collapsed`): the same statement with
`v = agC`; here the conclusion is the initial bound (`G = univ`). -/
theorem altGrid_instance_collapsed (m : ℕ) (hm : 1 ≤ m) :
    ∃ ε₁ τ' D' C_K : ℝ, 0 < ε₁ ∧ 0 < τ' ∧ 0 < D' ∧ 0 ≤ C_K ∧
      ∃ n : ℕ, ∃ G : Set (PathΩ sz0), (pathP sz0).real Gᶜ ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ∧
        ∀ ω ∈ G,
          (∀ j ≤ agK C_K n, pathH sz0 agS agC (agK C_K) n j ω ∈
            sz0.GoodSetN n (agE n) (gridTime agS agC (agK C_K) n j) (m + 1 + 1)
                (((sz0.size n : ℕ) : ℝ) ^ ε₁) 1 1 τ' D' ∩
              GoodLinN sz0 n (agE n) (gridTime agS agC (agK C_K) n j) (m + 1 + 1)
                (((sz0.size n : ℕ) : ℝ) ^ ε₁) 1 1 1 ∩
              altYSetN sz0 n (agE n) (gridTime agS agC (agK C_K) n j) (m + 1)
                (((sz0.size n : ℕ) : ℝ) ^ ε₁ * 1)) →
          (∀ σ : Fin (m + 1 + 1) → Bool, σ (Fin.last (m + 1)) = !σ 0 →
            ∀ a : Fin (m + 1 + 1) → Zd 3 (sz0.L n),
              ‖STQop (d := 3) (QopAlgebra_mollifier 3 (sz0.L n) (m + 1) (sz0.lam n)) (agS n)
                  (fun b : Fin (m + 1 + 1) → Zd 3 (sz0.L n) =>
                    sz0.STLKM n (agE n) (agS n) (pathH sz0 agS agC (agK C_K) n 0 ω) σ b) a‖ ≤
                ((sz0.size n : ℕ) : ℝ) ^ ε₁ * (sz0.Bctl n (agS n)) ^ (m + 1 + 1)) →
          ∀ σ : Fin (m + 1 + 1) → Bool, σ (Fin.last (m + 1)) = !σ 0 →
            ∀ a : Fin (m + 1 + 1) → Zd 3 (sz0.L n),
              ‖sz0.STLKM n (agE n) (agC n) (pathH sz0 agS agC (agK C_K) n (agK C_K n) ω) σ a‖ ≤
                ((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * ((1 : ℝ) ^ ((1 : ℝ) / 2) + 1 + 1 + 1 + 1) *
                  (sz0.Bctl n (agC n)) ^ (m + 1 + 1) := by
  obtain ⟨ε₁, τ', D', C_K, h1, h2, h3, h4, hend⟩ := altGridEndQN sz0 1 (1 / 6) (1 / 2) (1 / 10)
    agE agS agT (by norm_num) one_pos (by norm_num) (by norm_num) (by norm_num) sz0_tendsto
    sz0_bandwidth sz0_WO agE_abs agS_nonneg agS_le_agT agT_lt_one agCaseI rangeCond_half agWt m hm
    agOne agOne agOne agOne agOne (fun _ => by norm_num) (Eventually.of_forall fun _ => le_rfl)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => le_rfl) agC
    agS_le_agC agC_le_agT (1 / 10) (by norm_num) 1 one_pos
  refine ⟨ε₁, τ', D', C_K, h1, h2, h3, h4, ?_⟩
  obtain ⟨n, G, hG, hGb⟩ := (hend agOne (agK C_K) (agK_ne_zero C_K)
    (Eventually.of_forall (agK_low C_K)) (Eventually.of_forall (agK_up C_K))).exists
  exact ⟨n, G, hG, hGb⟩

/-- The instance at `m = 1` (tensors of `3` indices). -/
example := altGrid_instance 1 le_rfl

/-- The instance at `m = 2` (tensors of `4` indices). -/
example := altGrid_instance 2 (by norm_num)

/-- The instance at `m = 3` (tensors of `5` indices). -/
example := altGrid_instance 3 (by norm_num)

/-- The collapsed-window instance at `m = 2`. -/
example := altGrid_instance_collapsed 2 (by norm_num)


/-! ### (1) The `lam` patch at one size index -/

/-- **Instance (1)**: `STMollifierProps` for the patched family at the size index `n = 4`, in both branches: at `sz0`
(`lam > 0`: the explicit mollifier) and at `sz0.withLam 0` (`lam = 0 ≤ 0`: the delta family). -/
theorem lam_patch_instance (m : ℕ) :
    STMollifierProps (d := 3) (sz0.lam 4) (altGrid_C1 3 m) (1 / 2) (altGrid_mol sz0 m 4) ∧
    STMollifierProps (d := 3) ((sz0.withLam fun _ => (0 : ℝ)).lam 4) (altGrid_C1 3 m) (1 / 2)
      (altGrid_mol (sz0.withLam fun _ => (0 : ℝ)) m 4) :=
  ⟨altGrid_mol_props sz0 m 4, altGrid_mol_props (sz0.withLam fun _ => (0 : ℝ)) m 4⟩

/-- The patched family at `lam = 0` is not trivial: it is `1` on a constant label and `0` on a non-constant label
(`m = 1`, tensors of `3` indices, `n = 4`: `L = 20`); at `lam > 0` it is the explicit mollifier. -/
theorem lam_patch_values (t : ℝ) :
    altGrid_mol (sz0.withLam fun _ => (0 : ℝ)) 1 4 t (fun _ => 0) = 1 ∧
    altGrid_mol (sz0.withLam fun _ => (0 : ℝ)) 1 4 t (fun i => if i = 0 then 0 else 1) = 0 ∧
    altGrid_mol sz0 1 4 = QopAlgebra_mollifier 3 (sz0.L 4) (1 + 1) (sz0.lam 4) := by
  have hl : ¬ (0 : ℝ) < (sz0.withLam fun _ => (0 : ℝ)).lam 4 := by
    change ¬ (0 : ℝ) < 0
    exact lt_irrefl _
  refine ⟨?_, ?_, altGrid_mol_eq sz0 1 4 (sz0_lam_pos 4)⟩
  · unfold altGrid_mol
    rw [ite_eq_right hl]
    simp [altGrid_delta]
  · unfold altGrid_mol
    rw [ite_eq_right hl]
    simp only [altGrid_delta]
    rw [ite_eq_right]
    intro h
    have h1 := h 1
    simp only [Nat.reduceAdd, Fin.isValue, one_ne_zero, ↓reduceIte] at h1
    exact absurd h1 (by decide)

/-! ### (2) The level split at one size index (`n = 4`: `N = 8·10^{18}`, `W = 10^5`, `E = 0`, `u = v = 1/2`, `η = 1/2`) -/

private theorem N4 : ((sz0.size 4 : ℕ) : ℝ) = 8000000000000000000 := by
  have : sz0.size 4 = 8000000000000000000 := by norm_num [Sizes.size, sz0]
  exact_mod_cast this

private theorem mE_zero_im : (mE 0).im = 1 := by
  rw [mE_im]
  have : (4 : ℝ) - 0 ^ 2 = 2 ^ 2 := by norm_num
  rw [this, Real.sqrt_sq (by norm_num)]
  norm_num

private theorem etaT_zero_half : etaT 0 (1 / 2) = 1 / 2 := by
  unfold etaT
  rw [mE_zero_im]
  norm_num

/-- **Instance (2), small levels**: at `n = 4`, `k = m + 2 = 4`, `Γ = N^{1/10}`, `Λ = Φ₁ = Φ₂ = Φ₃ = 1`, `u = 1/2`: the two
quantities of the assembly that the level split bounds, `Γ(ΓΛ)B^{2k}/η` and `dDriftLinN`, are `≤ N^{8k+7}`
(`altGrid_hMee_bound`, `altGrid_dDrift_bound`, with `B ≤ 2N`, `η⁻¹ = 2 ≤ N` from `altGrid_u_facts`). -/
theorem levels_small_instance :
    ((sz0.size 4 : ℕ) : ℝ) ^ (1 / 10 : ℝ) * (((sz0.size 4 : ℕ) : ℝ) ^ (1 / 10 : ℝ) * 1) *
        ((sz0.Bctl 4 (1 / 2)) ^ (2 * (2 + 1 + 1)) / etaT 0 (1 / 2)) ≤
      ((sz0.size 4 : ℕ) : ℝ) ^ (8 * (2 + 1 + 1) + 7) ∧
    dDriftLinN sz0 4 0 (1 / 2) (2 + 1 + 1) (((sz0.size 4 : ℕ) : ℝ) ^ (1 / 10 : ℝ)) 1 1 1 ≤
      ((sz0.size 4 : ℕ) : ℝ) ^ (8 * (2 + 1 + 1) + 7) := by
  have hN1 : (1 : ℝ) ≤ ((sz0.size 4 : ℕ) : ℝ) := by rw [N4]; norm_num
  have hN2 : (2 : ℝ) ≤ ((sz0.size 4 : ℕ) : ℝ) := by rw [N4]; norm_num
  have hη : (etaT 0 (1 / 2))⁻¹ ≤ ((sz0.size 4 : ℕ) : ℝ) := by rw [etaT_zero_half, N4]; norm_num
  have hNv : (((sz0.size 4 : ℕ) : ℝ))⁻¹ ≤ 1 - 1 / 2 := by rw [N4]; norm_num
  obtain ⟨hηu0, hηu, hBu0, hBu⟩ := altGrid_u_facts sz0 4 (E := 0) (v := 1 / 2) (u := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) le_rfl hη hNv
  have hΓ0 : 0 ≤ ((sz0.size 4 : ℕ) : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hΓN : ((sz0.size 4 : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ ((sz0.size 4 : ℕ) : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (1 / 10 : ℝ) ≤ 1)).trans_eq (Real.rpow_one _)
  have hΛ : (1 : ℝ) ≤ ((sz0.size 4 : ℕ) : ℝ) ^ (4 * (2 + 1 + 1) + 4) := one_le_pow₀ hN1
  have hΦ : (1 : ℝ) ≤ ((sz0.size 4 : ℕ) : ℝ) ^ (2 * (2 + 1 + 1) + 2) := one_le_pow₀ hN1
  refine ⟨altGrid_hMee_bound (k := 2 + 1 + 1) hN2 hΓ0 hΓN (by norm_num) hΛ hBu0.le hBu hηu0 hηu, ?_⟩
  unfold dDriftLinN
  exact altGrid_dDrift_bound (k := 2 + 1 + 1) (by norm_num) hN2 hΓ0 hΓN (by norm_num) (by norm_num)
    (by norm_num) hΦ hΦ hΦ hBu0.le hBu hηu0 hηu

/-- **Instance (2), big levels**: at `n = 4`, `k = 4`, `ε₀ = 1/10`, `𝔏 = N^{2k+2}` (the boundary of the split) the crude bound
`N^{k+2}` is at most `N^{ε₀} 𝔏 B_v^k`, `B_v ≥ N⁻¹` (`cont_inv_size_le_Bctl`). -/
theorem levels_big_instance :
    ((sz0.size 4 : ℕ) : ℝ) ^ (2 + 1 + 1 + 2) ≤ ((sz0.size 4 : ℕ) : ℝ) ^ (1 / 10 : ℝ) *
      ((sz0.size 4 : ℕ) : ℝ) ^ (2 * (2 + 1 + 1) + 2) * (sz0.Bctl 4 (1 / 2)) ^ (2 + 1 + 1) :=
  altGrid_big_case (2 + 1 + 1) (by rw [N4]; norm_num) (by norm_num)
    (ContinuityNet.cont_inv_size_le_Bctl sz0 4 (by norm_num) (by norm_num)) le_rfl

/-- **Instance (2), the crude bound** `‖(𝓛-𝒦)^{(4)}_{u,σ}(H)‖ ≤ N^{k+2}` for the Hermitian `H = 0` at `u = 1/2 = v`, at a size
index `n` of the `𝒦` envelope (`exists_norm_Kcal_le_win`; `STKbound` by `stKbound_holds`), every `σ`. -/
theorem levels_crude_instance (σ : Fin (2 + 1 + 1) → Bool) :
    ∃ n : ℕ, ‖fun b : Fin (2 + 1 + 1) → Zd 3 (sz0.L n) =>
      sz0.STLKM n 0 (1 / 2) (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) σ b‖ ≤
        ((sz0.size n : ℕ) : ℝ) ^ (2 + 1 + 1 + 2) := by
  have hKb : sz0.STKbound agE := stKbound_holds sz0 (by norm_num) one_pos (by norm_num : (0 : ℝ) < 10)
    sz0_tendsto (Eventually.of_forall fun n => by norm_num [agE])
    (Eventually.of_forall fun n => ⟨sz0_lam_pos n, (sz0_lam_le_one n).trans (by norm_num)⟩)
  have hKev := exists_norm_Kcal_le_win sz0 sz0_tendsto agE hKb (fun _ => by norm_num [agE])
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun _ => by norm_num) (2 + 1 + 1) 1 one_pos
  obtain ⟨n, hn, -⟩ := (hKev.and (Filter.eventually_ge_atTop 0)).exists
  refine ⟨n, ?_⟩
  have hN4 : (4 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) := four_le_size n
  have hη : (etaT 0 (1 / 2))⁻¹ ≤ ((sz0.size n : ℕ) : ℝ) := by
    rw [etaT_zero_half, show ((1 / 2 : ℝ))⁻¹ = 2 by norm_num]; linarith
  exact altGrid_crude_N sz0 n (E := 0) (v := 1 / 2) (by norm_num) (k := 2 + 1 + 1) (by norm_num) hn
    (by norm_num) hη (by linarith) (by norm_num) le_rfl Matrix.isHermitian_zero σ


end QEndGridInst

end RBM.Ind

end

#print axioms RBM.Ind.altGridEndQN
#print axioms RBM.Ind.QEndGridInst.agCaseI
#print axioms RBM.Ind.QEndGridInst.agWt
#print axioms RBM.Ind.QEndGridInst.window_nondegenerate
#print axioms RBM.Ind.QEndGridInst.window_collapsed
#print axioms RBM.Ind.QEndGridInst.altGrid_instance
#print axioms RBM.Ind.QEndGridInst.altGrid_instance_collapsed
#print axioms RBM.Ind.QEndGridInst.lam_patch_instance
#print axioms RBM.Ind.QEndGridInst.lam_patch_values
#print axioms RBM.Ind.QEndGridInst.levels_small_instance
#print axioms RBM.Ind.QEndGridInst.levels_big_instance
#print axioms RBM.Ind.QEndGridInst.levels_crude_instance
