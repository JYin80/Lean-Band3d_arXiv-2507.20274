/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Defs
import RBM3D.Induction.PerTimeCalc

/-!
# The scale facts of the size sequence at `d ≥ 3`

The scales of arXiv:2507.20274: `ℓ_t` ((2.64) `eq:ellt`, `ellT`), `W^{-d} B_{t,0}` ((2.62)
`eq_B_param`, `Sizes.Bctl`), `η_t` (`RBM.Gauss.etaT`), and `N = (W L)^d = sz.size n`.  The
deterministic facts `STsize_pos`, `STBctl_pos`, `STBctl_mono`, `STBctl_xmono`, `STBctl_ge`,
`closure_scale` are proved in §1-§2; the proofs follow the two-dimensional formalization (RBM2D
`Induction/ScaleFacts`) with the scales of this paper.

## What changes from `d = 2`

The RBM2D scale `M_t = W² ℓ_t² η_t` (`scaleM`) has no `d ≥ 3` reading: `W^{-d} B_{t,0} ≍ M_t^{-1}`
only for `d = 2`, `ilambda = 1` (for `d ≥ 3` the zero-mode term `(L^d |1-t|)^{-1}` of `B` is not
`1/(ℓ² |1-t|)`).  The role of `M_t^{-1}` is played by `a_t := sz.Bctl n t = W^{-d} B_{t,0}`:

* `scaleFacts_R1`: `M_u ≥ Im m N^{c₀}` becomes `a_u ≤ 2 N^{-c₀}`, `c₀ = min(2 𝔠 𝔡, τ)`; it needs
  `(eq:WO)` (`sz.WO 𝔡`: `ilambda² W^d ≥ W^{2𝔡}`) because `ilambda` is a sequence and not `1`; the
  hypothesis is necessary (§7);
* `scaleFacts_R2_pt`: `M_s^{29/30} ≤ M_u` from `M_s^{-1} ≤ ((1-t)/(1-s))^{30}` becomes
  `a_u ≤ a_s^{1-c}` from `a_t^c ≤ (1-t)/(1-s)` ((2.83) `con_st_ind`, `c = 𝔠_d`); `c = 1/30`
  reproduces `29/30`;
* the ratio facts `ℓ_u/ℓ_s ≤ ((1-s)/(1-t))^{1/2}`, `(ℓ_t/ℓ_s)^4 ≤ (η_s/η_t)^2` keep their
  exponents (dimension free); `ellT` carries the coupling `g`, and `0 ≤ s` is not needed.

## Two-dimensional statements without a counterpart

`ChainStepCond`, `chainStepCond` (the `d = 2` grid `1 - s_k = (1 - t)^{k/n₀}`) have no `d ≥ 3`
form here: in the proof of the main results (after (2.84) `Eq:Gdecay+s<g`) the induction on `t`
runs in two phases and fixes no grid.  `scaleFacts_inv_sq_le_tailT` belongs to Step 5 of the
`d = 2` paper; `tailT`, `ellStar`, `scaleM` are not `d ≥ 3` objects.
-/

set_option linter.style.longLine false

noncomputable section

open Filter RBM RBM.Gauss

/-! ## 1. Deterministic scale facts of `W^{-d} B_{t,0}` -/

namespace RBM.Gauss.Sizes

variable {d : ℕ} (sz : Sizes d)

theorem STsize_pos (n : ℕ) : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by
  have h : 0 < sz.size n :=
    pow_pos (Nat.mul_pos (sz.W_pos n) (by have := sz.three_le_L n; omega)) _
  exact_mod_cast h

/-- `W^{-d} B_{t,0} > 0` for `t < 1`. -/
theorem STBctl_pos (n : ℕ) {t : ℝ} (ht : t < 1) : 0 < sz.Bctl n t := by
  unfold Sizes.Bctl Bparam
  have hx : 0 < 1 - t := by linarith
  rw [abs_of_pos hx]
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  positivity

/-- **Monotonicity**: `W^{-d} B_{s,0} ≤ W^{-d} B_{u,0}` for `s ≤ u < 1`: it is nondecreasing along the flow. -/
theorem STBctl_mono (n : ℕ) {s u : ℝ} (hsu : s ≤ u) (hu : u < 1) : sz.Bctl n s ≤ sz.Bctl n u := by
  unfold Sizes.Bctl Bparam
  have hxu : 0 < 1 - u := by linarith
  have hxs : 0 < 1 - s := by linarith
  rw [abs_of_pos hxu, abs_of_pos hxs]
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hg : (0 : ℝ) ≤ sz.lam n ^ 2 := sq_nonneg _
  have h1 : (sz.lam n ^ 2 + (1 - s))⁻¹ ≤ (sz.lam n ^ 2 + (1 - u))⁻¹ :=
    inv_anti₀ (by linarith) (by linarith)
  have h2 : (((sz.L n : ℕ) : ℝ) ^ d * (1 - s))⁻¹ ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ :=
    inv_anti₀ (by positivity) (by gcongr)
  have hK : 0 ≤ ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
  gcongr

/-- **Monotonicity, sharper form**: `(1-v) W^{-d} B_{v,0} ≤ (1-s) W^{-d} B_{s,0}` for `s ≤ v < 1`
(`x ↦ x B_{x,0} = x/(g²+x) + L^{-d}` is nondecreasing): the bound `(η_s/η_u) W^{-d} B_{s,0}` of
`lem_ConArg` can only improve if the starting time is moved later. -/
theorem STBctl_xmono (n : ℕ) {s v : ℝ} (hsv : s ≤ v) (hv : v < 1) :
    (1 - v) * sz.Bctl n v ≤ (1 - s) * sz.Bctl n s := by
  unfold Sizes.Bctl Bparam
  have hxv : 0 < 1 - v := by linarith
  have hxs : 0 < 1 - s := by linarith
  rw [abs_of_pos hxv, abs_of_pos hxs]
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hg : (0 : ℝ) ≤ sz.lam n ^ 2 := sq_nonneg _
  have hz : (((0 : ℕ) : ℝ) + 1) ^ (d - 2) = 1 := by norm_num
  simp only [hz, inv_one, mul_one]
  have h1 : (1 - v) * (sz.lam n ^ 2 + (1 - v))⁻¹ ≤ (1 - s) * (sz.lam n ^ 2 + (1 - s))⁻¹ := by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have h2 : (1 - v) * (((sz.L n : ℕ) : ℝ) ^ d * (1 - v))⁻¹ =
      (1 - s) * (((sz.L n : ℕ) : ℝ) ^ d * (1 - s))⁻¹ := by
    field_simp
  have key : (1 - v) * ((sz.lam n ^ 2 + (1 - v))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - v))⁻¹) ≤
      (1 - s) * ((sz.lam n ^ 2 + (1 - s))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - s))⁻¹) := by
    rw [mul_add, mul_add]; linarith
  have hW0 : 0 ≤ ((((sz.W n : ℕ) : ℝ) ^ d))⁻¹ := by positivity
  calc (1 - v) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
        ((sz.lam n ^ 2 + (1 - v))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - v))⁻¹))
      = ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) *
        ((1 - v) * ((sz.lam n ^ 2 + (1 - v))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - v))⁻¹)) := by ring
    _ ≤ ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) *
        ((1 - s) * ((sz.lam n ^ 2 + (1 - s))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - s))⁻¹)) :=
        mul_le_mul_of_nonneg_left key hW0
    _ = (1 - s) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
        ((sz.lam n ^ 2 + (1 - s))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - s))⁻¹)) := by ring

/-- `W^{-d} B_{s,0} ≥ W^{-d} (ilambda² + 1)⁻¹` for `0 ≤ s < 1`: at the early times it is
at least the volume factor (`x_s ≤ 1`). -/
theorem STBctl_ge (n : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ((((sz.W n : ℕ) : ℝ) ^ d))⁻¹ * (sz.lam n ^ 2 + 1)⁻¹ ≤ sz.Bctl n s := by
  unfold Sizes.Bctl Bparam
  have hxs : 0 < 1 - s := by linarith
  rw [abs_of_pos hxs]
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hg : (0 : ℝ) ≤ sz.lam n ^ 2 := sq_nonneg _
  have hz : (((0 : ℕ) : ℝ) + 1) ^ (d - 2) = 1 := by norm_num
  simp only [hz, inv_one, mul_one]
  have h1 : (sz.lam n ^ 2 + 1)⁻¹ ≤ (sz.lam n ^ 2 + (1 - s))⁻¹ :=
    inv_anti₀ (by linarith) (by linarith)
  have h2 : 0 ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - s))⁻¹ := by positivity
  have hW0 : 0 ≤ ((((sz.W n : ℕ) : ℝ) ^ d))⁻¹ := by positivity
  calc ((((sz.W n : ℕ) : ℝ) ^ d))⁻¹ * (sz.lam n ^ 2 + 1)⁻¹
      ≤ ((((sz.W n : ℕ) : ℝ) ^ d))⁻¹ * ((sz.lam n ^ 2 + (1 - s))⁻¹ +
          (((sz.L n : ℕ) : ℝ) ^ d * (1 - s))⁻¹) :=
        mul_le_mul_of_nonneg_left (by linarith) hW0
    _ = _ := rfl

end RBM.Gauss.Sizes

/-! ## 2. The closure of Step 1, pure real facts -/

namespace RBM.Ind

/-- **The closure of Step 1**: if `a_s ≤ a_t`, `a_t^c ≤ x_t/x_s` (`(con_st_ind)` with
`c = 𝔠_d`, `a = W^{-d}B_{·,0}`, `x = 1 - ·`) and `x_t ≤ x_u`, then `a_s x_s/x_u ≤ a_s^{1-c}`.
With `c ≤ 1/4`: `(a_s x_s/x_u)^{1/2} ≤ a_s^{3/8}`; the exponent `30` of RBM2D is `1/c` at `c = 1/30`, and the dimension enters only through `a`. -/
theorem closure_scale {as at_ xs xt xu c : ℝ} (hc : 0 < c) (has : 0 < as) (hat : as ≤ at_)
    (hxt : 0 < xt) (hxs : 0 < xs) (hxu : xt ≤ xu) (hcon : at_ ^ c ≤ xt / xs) :
    as * (xs / xu) ≤ as ^ (1 - c) := by
  have hat0 : 0 < at_ := lt_of_lt_of_le has hat
  have h1 : xs / xu ≤ xs / xt := div_le_div_of_nonneg_left hxs.le hxt hxu
  have h2 : xs / xt ≤ at_ ^ (-c) := by
    have h3 : (xt / xs)⁻¹ ≤ (at_ ^ c)⁻¹ := inv_anti₀ (Real.rpow_pos_of_pos hat0 c) hcon
    rw [inv_div] at h3
    rwa [← Real.rpow_neg hat0.le] at h3
  have h4 : at_ ^ (-c) ≤ as ^ (-c) := Real.rpow_le_rpow_of_nonpos has hat (by linarith)
  calc as * (xs / xu) ≤ as * as ^ (-c) := by gcongr; exact h1.trans (h2.trans h4)
    _ = as ^ (1 - c) := by rw [sub_eq_add_neg, Real.rpow_add has, Real.rpow_one]

end RBM.Ind

/-! ## 3. `scaleFacts_R1`: `W^{-d} B_{u,0} ≤ 2 N^{-c₀}` for `u ≤ t` -/

namespace RBM.Ind

variable {d : ℕ} (sz : Sizes d)

/-- `scaleFacts_R1` (the counterpart of RBM2D's `scaleFacts_R1`, `M_u ≥ Im m · N^{c₀}`):
under `Bandwidth 𝔠` (`W ≥ N^𝔠`), `(eq:WO)` and the range condition `N^{-1+τ} ≤ 1 - t`
(RBM2D `RangeCond`), eventually, for every `u ≤ t n`,
`W^{-d} B_{u,0} ≤ 2 N^{-min(2𝔠𝔡, τ)}`, `N = sz.size n = (W L)^d`.

Proof: `W^{-d}B_{u,0} = (W^d (g² + x_u))⁻¹ + (N x_u)⁻¹ ≤ (g² W^d)⁻¹ + (N N^{-1+τ})⁻¹
≤ W^{-2𝔡} + N^{-τ} ≤ N^{-2𝔠𝔡} + N^{-τ}` (`x_u ≥ x_t ≥ N^{-1+τ}`, `Sizes.lam_sq_mul_pow_ge`).
`(eq:WO)` is needed: for `ilambda ≡ 0`, `W = L = N^{1/(2d)}`, `x = N^{-1+τ}` the left side is
`≥ (W^d x)⁻¹ = N^{1/2 - τ} → ∞` for `τ < 1/2`.  The exponent
`2𝔠𝔡` replaces RBM2D's `2c`: `W^{-2𝔡}` is the `d = 2` bound `W^{-2}` with `ilambda = 1`. -/
theorem scaleFacts_R1 (𝔠 𝔡 τ : ℝ) (t : ℕ → ℝ) (h𝔡 : 0 < 𝔡)
    (hB : sz.Bandwidth 𝔠) (hWO : sz.WO 𝔡)
    (hR : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + τ) ≤ 1 - t n) :
    ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, u ≤ t n →
      sz.Bctl n u ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (-(min (2 * 𝔠 * 𝔡) τ)) := by
  filter_upwards [hB, hWO, hR] with n hBn hWOn hRn u hu
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  set L : ℝ := ((sz.L n : ℕ) : ℝ) with hLdef
  have hN1 : (1 : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast sz.one_le_size n
  have hN0 : 0 < N := by linarith
  have hW0 : 0 < W := by rw [hWdef]; exact_mod_cast sz.W_pos n
  have hL0 : 0 < L := by
    rw [hLdef]; exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hNWL : N = W ^ d * L ^ d := by
    rw [hNdef, hWdef, hLdef]; simp [Sizes.size, mul_pow]
  have hxrange : N ^ (-1 + τ) ≤ 1 - u := by linarith
  have hxpos : 0 < N ^ (-1 + τ) := Real.rpow_pos_of_pos hN0 _
  have hxu : 0 < 1 - u := lt_of_lt_of_le hxpos hxrange
  -- the two terms of `W^{-d} B_{u,0}`
  have hBctl : sz.Bctl n u =
      (W ^ d * (sz.lam n ^ 2 + (1 - u)))⁻¹ + (N * (1 - u))⁻¹ := by
    unfold Sizes.Bctl Bparam
    rw [abs_of_pos hxu, hNWL]
    have hz : (((0 : ℕ) : ℝ) + 1) ^ (d - 2) = 1 := by norm_num
    simp only [hz, inv_one, mul_one]
    rw [← hWdef, ← hLdef, mul_add, mul_inv, mul_inv, mul_inv, mul_inv]
    ring
  -- `ilambda² W^d ≥ W^{2𝔡}`
  have hlam : W ^ (2 * 𝔡) ≤ sz.lam n ^ 2 * W ^ d := Sizes.lam_sq_mul_pow_ge sz n hWOn.1
  have hWp : 0 < W ^ (2 * 𝔡) := Real.rpow_pos_of_pos hW0 _
  have hg2 : 0 < sz.lam n ^ 2 * W ^ d := lt_of_lt_of_le hWp hlam
  -- first term
  have hT1 : (W ^ d * (sz.lam n ^ 2 + (1 - u)))⁻¹ ≤ (W ^ (2 * 𝔡))⁻¹ := by
    refine le_trans (inv_anti₀ hg2 ?_) (inv_anti₀ hWp hlam)
    nlinarith [pow_pos hW0 d]
  have hT1' : (W ^ (2 * 𝔡))⁻¹ ≤ N ^ (-(2 * 𝔠 * 𝔡)) := by
    have hNc : 0 ≤ N ^ 𝔠 := Real.rpow_nonneg hN0.le _
    have hpos : 0 < (N ^ 𝔠) ^ (2 * 𝔡) := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hN0 _) _
    have h1 : (N ^ 𝔠) ^ (2 * 𝔡) ≤ W ^ (2 * 𝔡) :=
      Real.rpow_le_rpow hNc hBn (by linarith)
    have h2 : (N ^ 𝔠) ^ (2 * 𝔡) = N ^ (2 * 𝔠 * 𝔡) := by
      rw [← Real.rpow_mul hN0.le]; congr 1; ring
    calc (W ^ (2 * 𝔡))⁻¹ ≤ ((N ^ 𝔠) ^ (2 * 𝔡))⁻¹ := inv_anti₀ hpos h1
      _ = N ^ (-(2 * 𝔠 * 𝔡)) := by rw [h2, Real.rpow_neg hN0.le]
  -- second term
  have hT2 : (N * (1 - u))⁻¹ ≤ N ^ (-τ) := by
    have h1 : N * N ^ (-1 + τ) ≤ N * (1 - u) := mul_le_mul_of_nonneg_left hxrange hN0.le
    have h2 : N * N ^ (-1 + τ) = N ^ τ := by
      have h := Real.rpow_add hN0 1 (-1 + τ)
      rw [Real.rpow_one] at h
      rw [← h]; congr 1; ring
    calc (N * (1 - u))⁻¹ ≤ (N * N ^ (-1 + τ))⁻¹ := inv_anti₀ (by positivity) h1
      _ = N ^ (-τ) := by rw [h2, Real.rpow_neg hN0.le]
  have hm1 : N ^ (-(2 * 𝔠 * 𝔡)) ≤ N ^ (-(min (2 * 𝔠 * 𝔡) τ)) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [min_le_left (2 * 𝔠 * 𝔡) τ])
  have hm2 : N ^ (-τ) ≤ N ^ (-(min (2 * 𝔠 * 𝔡) τ)) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [min_le_right (2 * 𝔠 * 𝔡) τ])
  rw [hBctl]
  linarith

end RBM.Ind

/-! ## 4. `scaleFacts_R2`: `W^{-d} B_{u,0} ≤ (W^{-d} B_{s,0})^{1-𝔠_d}` for `u ∈ [s, t]` -/

namespace RBM.Ind

variable {d : ℕ} (sz : Sizes d)

/-- `scaleFacts_R2_pt`, pointwise (the counterpart of RBM2D's `scaleFacts_R2_pt`, `M_s^{29/30} ≤ M_u`
from `M_s⁻¹ ≤ ((1 - t)/(1 - s))^{30}`): from the step condition `(con_st_ind)`
`(W^{-d}B_{t,0})^c ≤ (1 - t)/(1 - s)` (`c = 𝔠_d`), for `s ≤ u ≤ t < 1`,
`W^{-d} B_{u,0} ≤ (W^{-d} B_{s,0})^{1-c}`.  `c = 1/30` is the exponent `29/30` of RBM2D.
Proof: `x_u a_u ≤ x_s a_s` (`STBctl_xmono`), `a_s ≤ a_t` (`STBctl_mono`) and `closure_scale`. -/
theorem scaleFacts_R2_pt (n : ℕ) {c s u t : ℝ} (hc : 0 < c) (hsu : s ≤ u) (hut : u ≤ t)
    (ht : t < 1) (hstep : (sz.Bctl n t) ^ c ≤ (1 - t) / (1 - s)) :
    sz.Bctl n u ≤ (sz.Bctl n s) ^ (1 - c) := by
  have hu1 : u < 1 := lt_of_le_of_lt hut ht
  have hs1 : s < 1 := lt_of_le_of_lt hsu hu1
  have hxt : 0 < 1 - t := by linarith
  have hxu : 0 < 1 - u := by linarith
  have hxs : 0 < 1 - s := by linarith
  have has : 0 < sz.Bctl n s := Sizes.STBctl_pos sz n hs1
  have hat : sz.Bctl n s ≤ sz.Bctl n t := Sizes.STBctl_mono sz n (hsu.trans hut) ht
  have hxm : (1 - u) * sz.Bctl n u ≤ (1 - s) * sz.Bctl n s := Sizes.STBctl_xmono sz n hsu hu1
  have h1 : sz.Bctl n u ≤ sz.Bctl n s * ((1 - s) / (1 - u)) := by
    rw [mul_div_assoc', le_div_iff₀ hxu]
    linarith
  exact h1.trans (closure_scale hc has hat hxt hxs (by linarith) hstep)

/-- `scaleFacts_R2`, sequence form (the counterpart of RBM2D's `scaleFacts_R2`, with `CondStInd`,
`RangeCond`): `STConStInd sz 𝔠d s t` and `t n < 1` eventually give, eventually, for every
`u ∈ [s n, t n]`, `W^{-d} B_{u,0} ≤ (W^{-d} B_{s n,0})^{1-𝔠_d}`.  `t n < 1` is needed because
`STConStInd` is vacuous at `s ≥ 1` (Lean `x/0 = 0`). -/
theorem scaleFacts_R2 {𝔠d : ℝ} (h𝔠d : 0 < 𝔠d) {s t : ℕ → ℝ} (hC : sz.STConStInd 𝔠d s t)
    (ht : ∀ᶠ n : ℕ in atTop, t n < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, s n ≤ u → u ≤ t n →
      sz.Bctl n u ≤ (sz.Bctl n (s n)) ^ (1 - 𝔠d) := by
  filter_upwards [hC, ht] with n hCn htn u hsu hut
  exact scaleFacts_R2_pt sz n h𝔠d hsu hut htn hCn.1

/-! ## 5. The ratio facts -/

/-- `η_s/η_t = (1 - s)/(1 - t)` for `|E| < 2`, `t < 1` (RBM2D's
`etaT_div_etaT`, for `etaT E t = (1 - t) Im m^{(E)}`). -/
theorem scaleFacts_etaT_div_etaT {E s t : ℝ} (hE : |E| < 2) :
    etaT E s / etaT E t = (1 - s) / (1 - t) :=
  mul_div_mul_right _ _ (mE_im_pos hE).ne'

end RBM.Ind


/-! ## 6. `scaleFacts_R1` feeds `forbidden_region` (the last hypothesis of the bootstrap)

Step 1 applies `forbidden_region` with `a = α = (W^{-d}B_{s,0})^{1/4}`, `b = 2α`,
`f = α^{3/2} = (W^{-d}B_{s,0})^{3/8}` (`PerTimeCalc.Unif.forbidden_region`); its hypothesis
`f ≤ N^{-ε} a` is `a_s^{1/8} ≤ N^{-ε}`, which follows from `scaleFacts_R1` (`a_s ≤ 2 N^{-c₀}`,
`c₀ = 1/30` at `𝔠 = 1/6`, `𝔡 = 1/10`, `τ = 1/10`) with `ε = 1/480` once `N ≥ 2^{60}`. -/

/-! ## 7. `scaleFacts_R1` is false without `(eq:WO)`

All other hypotheses of `scaleFacts_R1` hold for the size data below (`d = 3`, `ilambda ≡ 0`,
`W_n = L_n = n + 3`, so `N = W^6`, `Bandwidth (1/6)`, `N^{-1+τ} = 1 - t_n` with `τ = 1/10`), `(eq:WO)`
fails, and the conclusion fails at every `n` (at `u = t_n`): `W^{-3} B_{t_n,0} ≥ (W^3 N^{-9/10})^{-1}
≥ W^2 ≥ 9 > 2 ≥ 2 N^{-1/30}`.  This is why the `d ≥ 3` reading of RBM2D's `scaleFacts_R1` has the
extra hypothesis `sz.WO 𝔡`. -/
