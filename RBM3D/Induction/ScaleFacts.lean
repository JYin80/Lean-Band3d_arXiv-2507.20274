/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Defs
import RBM3D.Induction.PerTimeCalc

/-!
# The scale facts of the size sequence at `d ≥ 3` (ST-1, S1-08)

Ticket T2045.  Port of `RBM2D/Induction/ScaleFacts.lean` at `c9a24cf` (rows R1, R2, R3, R5 of the
T2006 report) to the scales of `arXiv:2507.20274`: `ℓ_t` (`(eq:ellt)`, `1_2:1121`, merged `ellT`),
`W^{-d} B_{t,0}` (`(eq_B_param)`, `1_2:1107-1108`, merged `Sizes.Bctl`), `η_t` (merged
`RBM.Gauss.etaT`), `N = (W L)^d = sz.size n`.  Probe sections 4.1 of the T2015 probe
(`RBM3D/Probe/T2015Pins.lean` at `752e027`, lines 938-1061, not merged): `STsize_pos`, `STBctl_pos`,
`STBctl_mono`, `STBctl_xmono`, `STBctl_ge`, `closure_scale`, `closure_sq_le`, copied here with their
proofs (the `open` lines name `RBM Filter`).

## What changes from `d = 2`

The RBM2D scale `M_t = W² ℓ_t² η_t` (`scaleM`) has no `d ≥ 3` reading: `W^{-d} B_{t,0} ≍ M_t^{-1}`
only for `d = 2`, `ilambda = 1` (for `d ≥ 3` the zero-mode term `(L^d |1-t|)^{-1}` of `B` is not
`1/(ℓ² |1-t|)`).  The role of `M_t^{-1}` is played by `a_t := sz.Bctl n t = W^{-d} B_{t,0}`:

* `scaleFacts_R1`: `M_u ≥ Im m N^{c₀}` becomes `a_u ≤ 2 N^{-c₀}`, `c₀ = min(2 𝔠 𝔡, τ)`; it needs
  `(eq:WO)` (`sz.WO 𝔡`: `ilambda² W^d ≥ W^{2𝔡}`) because `ilambda` is a sequence and not `1`
  (paper-delta candidate T2045a);
* `scaleFacts_R2_pt`: `M_s^{29/30} ≤ M_u` from `M_s^{-1} ≤ ((1-t)/(1-s))^{30}` becomes
  `a_u ≤ a_s^{1-c}` from `a_t^c ≤ (1-t)/(1-s)` (`(con_st_ind)`, `1_2:1296`, `c = 𝔠_d`); `c = 1/30`
  reproduces `29/30`;
* the ratio facts `ℓ_u/ℓ_s ≤ ((1-s)/(1-t))^{1/2}`, `(ℓ_t/ℓ_s)^4 ≤ (η_s/η_t)^2` keep their
  exponents (dimension free); the merged `ellT` carries the coupling `g`, and `0 ≤ s` is not needed
  (T2045a).

## Dropped from the RBM2D file

`ChainStepCond`, `chainStepCond` (the `d = 2` grid `1 - s_k = (1 - t)^{k/n₀}` of `1-2:989-996`; its
consumers at `c9a24cf` are `Induction/Chain` and `Induction/MainInd`, not ST-1; the `d ≥ 3` paper
(`1_2:1308-1312`) performs the induction on `t` in two phases and fixes no grid, so a `d ≥ 3` form
belongs to the chain induction, whose core is `scaleFacts_R1` with `STConStInd`), and
`scaleFacts_inv_sq_le_tailT` (Step 5 of the `d = 2` paper; consumer `Induction/Step45`; `tailT`,
`ellStar`, `scaleM` are not `d ≥ 3` objects) (paper-delta candidate T2045b).
-/

set_option linter.style.longLine false

noncomputable section

open Filter RBM RBM.Gauss

/-! ## 1. Deterministic scale facts of `W^{-d} B_{t,0}` (probe section 4.1, rows 10-12) -/

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

/-- **Row 10**: `W^{-d} B_{s,0} ≤ W^{-d} B_{u,0}` for `s ≤ u < 1`: the control grows along the flow. -/
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

/-- **Row 10, sharper form**: `(1-v) W^{-d} B_{v,0} ≤ (1-s) W^{-d} B_{s,0}` for `s ≤ v < 1`
(`x ↦ x B_{x,0} = x/(g²+x) + L^{-d}` is nondecreasing): the control `(η_s/η_u) W^{-d} B_{s,0}` of
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

/-- `W^{-d} B_{s,0} ≥ W^{-d} (ilambda² + 1)⁻¹` for `0 ≤ s < 1`: at the early times the control is
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

/-! ## 2. The closure of Step 1 (probe row 12), pure real facts -/

namespace RBM.Ind

/-- **Row 12, the closure of Step 1**: if `a_s ≤ a_t`, `a_t^c ≤ x_t/x_s` (`(con_st_ind)` with
`c = 𝔠_d`, `a = W^{-d}B_{·,0}`, `x = 1 - ·`) and `x_t ≤ x_u`, then `a_s x_s/x_u ≤ a_s^{1-c}`.
With `c ≤ 1/4`: `(a_s x_s/x_u)^{1/2} ≤ a_s^{3/8}`; the `d`-dependence of RBM2D's exponent `30`
(`Induction/ScaleFacts.lean:87`, `Induction/Step1.lean:157`) is only through `a`. -/
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

/-- `a^{1-c} ≤ (a^{3/8})²` for `0 < a ≤ 1`, `c ≤ 1/4` (so that `(a^{1-c})^{1/2} ≤ a^{3/8}`). -/
theorem closure_sq_le {a c : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hc : c ≤ 1 / 4) :
    a ^ (1 - c) ≤ (a ^ (3 / 8 : ℝ)) ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
  exact Real.rpow_le_rpow_of_exponent_ge ha ha1 (by push_cast; linarith)

end RBM.Ind

/-! ## 3. Row R1: `W^{-d} B_{u,0} ≤ 2 N^{-c₀}` for `u ≤ t` -/

namespace RBM.Ind

variable {d : ℕ} (sz : Sizes d)

/-- Row R1 (T2006 (a.4)/(b.4); RBM2D `scaleFacts_R1`, `ScaleFacts.lean:72`, `M_u ≥ Im m · N^{c₀}`):
under `Bandwidth 𝔠` (`W ≥ N^𝔠`), `(eq:WO)` and the range condition `N^{-1+τ} ≤ 1 - t`
(RBM2D `RangeCond`), eventually, for every `u ≤ t n`,
`W^{-d} B_{u,0} ≤ 2 N^{-min(2𝔠𝔡, τ)}`, `N = sz.size n = (W L)^d`.

Proof: `W^{-d}B_{u,0} = (W^d (g² + x_u))⁻¹ + (N x_u)⁻¹ ≤ (g² W^d)⁻¹ + (N N^{-1+τ})⁻¹
≤ W^{-2𝔡} + N^{-τ} ≤ N^{-2𝔠𝔡} + N^{-τ}` (`x_u ≥ x_t ≥ N^{-1+τ}`, `Sizes.lam_sq_mul_pow_ge`).
`(eq:WO)` is needed: for `ilambda ≡ 0`, `W = L = N^{1/(2d)}`, `x = N^{-1+τ}` the left side is
`≥ (W^d x)⁻¹ = N^{1/2 - τ} → ∞` for `τ < 1/2` (paper-delta candidate T2045a).  The exponent
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

/-! ## 4. Row R2: `W^{-d} B_{u,0} ≤ (W^{-d} B_{s,0})^{1-𝔠_d}` for `u ∈ [s, t]` -/

namespace RBM.Ind

variable {d : ℕ} (sz : Sizes d)

/-- Row R2, pointwise (RBM2D `scaleFacts_R2_pt`, `ScaleFacts.lean:87`, `M_s^{29/30} ≤ M_u`
from `M_s⁻¹ ≤ ((1 - t)/(1 - s))^{30}`): from the step condition `(con_st_ind)` (`1_2:1296`)
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

/-- Row R2, sequence form (RBM2D `scaleFacts_R2`, `ScaleFacts.lean:121`, with `CondStInd`,
`RangeCond`): `STConStInd sz 𝔠d s t` and `t n < 1` eventually give, eventually, for every
`u ∈ [s n, t n]`, `W^{-d} B_{u,0} ≤ (W^{-d} B_{s n,0})^{1-𝔠_d}`.  `t n < 1` is needed because
`STConStInd` is vacuous at `s ≥ 1` (Lean `x/0 = 0`). -/
theorem scaleFacts_R2 {𝔠d : ℝ} (h𝔠d : 0 < 𝔠d) {s t : ℕ → ℝ} (hC : sz.STConStInd 𝔠d s t)
    (ht : ∀ᶠ n : ℕ in atTop, t n < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, s n ≤ u → u ≤ t n →
      sz.Bctl n u ≤ (sz.Bctl n (s n)) ^ (1 - 𝔠d) := by
  filter_upwards [hC, ht] with n hCn htn u hsu hut
  exact scaleFacts_R2_pt sz n h𝔠d hsu hut htn hCn.1

/-! ## 5. The ratio facts behind R3 and R5 -/

/-- (F1) `ℓ_u/ℓ_s ≤ ((1 - s)/(1 - u))^{1/2}` for `s ≤ u < 1`: RBM2D `Path/Scales.lean:135`
(`ellT_mono_ratio`), for the merged `ellT L g` of `(eq:ellt)` (`ℓ_t = min(max(g |1-t|^{-1/2}, 1), L)`).
No sign condition on `g` or `s`: `max(a r, 1) ≤ r max(a, 1)` for `r ≥ 1`. -/
theorem scaleFacts_ellT_mono_ratio {L : ℕ} {g s u : ℝ} (hL : 1 ≤ L) (hsu : s ≤ u) (hu : u < 1) :
    ellT L g u / ellT L g s ≤ ((1 - s) / (1 - u)) ^ ((1 : ℝ) / 2) := by
  have hxu : 0 < 1 - u := by linarith
  have hxs : 0 < 1 - s := by linarith
  have hsqu : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.2 hxu
  have hsqs : 0 < Real.sqrt (1 - s) := Real.sqrt_pos.2 hxs
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hℓs : 0 < ellT L g s := ellT_pos hL'
  rw [← Real.sqrt_eq_rpow, div_le_iff₀ hℓs, Real.sqrt_div hxs.le]
  set r : ℝ := Real.sqrt (1 - s) / Real.sqrt (1 - u) with hr
  have hr1 : 1 ≤ r := (one_le_div hsqu).2 (Real.sqrt_le_sqrt (by linarith))
  set a : ℝ := g / Real.sqrt |1 - s| with ha
  have hgu : g / Real.sqrt |1 - u| = a * r := by
    rw [abs_of_pos hxu, ha, abs_of_pos hxs, hr]; field_simp
  have hmax : max (a * r) 1 ≤ r * max a 1 := by
    refine max_le ?_ ?_
    · nlinarith [le_max_left a 1, le_max_right a 1]
    · nlinarith [le_max_right a 1]
  have hL0 : (0 : ℝ) ≤ L := by linarith
  unfold ellT
  rw [hgu]
  rcases le_total (max a 1) (L : ℝ) with h | h
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans hmax
  · rw [min_eq_right h]
    calc min (max (a * r) 1) (L : ℝ) ≤ L := min_le_right _ _
      _ ≤ r * L := by nlinarith

/-- R3-form ratio fact (Step 1, `3_5:64-66`): `ℓ_u/ℓ_s ≤ ((1 - s)/(1 - t))^{1/2}` for
`s ≤ u ≤ t < 1`.  RBM2D `scaleFacts_ellT_ratio`, `ScaleFacts.lean:136`; the exponent `1/2` is
dimension free; the hypothesis `0 ≤ s` of RBM2D is not needed (T2045a). -/
theorem scaleFacts_ellT_ratio {L : ℕ} {g s u t : ℝ} (hL : 1 ≤ L) (hsu : s ≤ u) (hut : u ≤ t)
    (ht : t < 1) :
    ellT L g u / ellT L g s ≤ ((1 - s) / (1 - t)) ^ ((1 : ℝ) / 2) := by
  have hu1 : u < 1 := lt_of_le_of_lt hut ht
  have hxt : 0 < 1 - t := by linarith
  have hxs : 0 < 1 - s := by linarith
  refine le_trans (scaleFacts_ellT_mono_ratio hL hsu hu1) ?_
  refine Real.rpow_le_rpow (div_nonneg hxs.le (by linarith)) ?_ (by norm_num)
  exact div_le_div_of_nonneg_left hxs.le hxt (by linarith)

/-- `η_s/η_t = (1 - s)/(1 - t)` for `|E| < 2`, `t < 1` (RBM2D `Path/Scales.lean:92`
`etaT_div_etaT`, for the merged `etaT E t = (1 - t) Im m^{(E)}`). -/
theorem scaleFacts_etaT_div_etaT {E s t : ℝ} (hE : |E| < 2) :
    etaT E s / etaT E t = (1 - s) / (1 - t) :=
  mul_div_mul_right _ _ (mE_im_pos hE).ne'

/-- R5-form ratio fact (Step 3, `lem_ConArg` `3_5:52`): `(ℓ_t/ℓ_s)^4 ≤ (η_s/η_t)^2` for `|E| < 2`,
`s ≤ t < 1`.  RBM2D `scaleFacts_ellT_pow_four`, `ScaleFacts.lean:148`; the exponents `4`, `2` are
dimension free (`4 · 1/2 = 2`). -/
theorem scaleFacts_ellT_pow_four {L : ℕ} {g E s t : ℝ} (hL : 1 ≤ L) (hE : |E| < 2)
    (hst : s ≤ t) (ht : t < 1) :
    (ellT L g t / ellT L g s) ^ 4 ≤ (etaT E s / etaT E t) ^ 2 := by
  have hxt : 0 < 1 - t := by linarith
  have hxs : 0 < 1 - s := by linarith
  have hC := scaleFacts_ellT_ratio (g := g) hL hst le_rfl ht
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hpos : 0 < ellT L g t / ellT L g s := div_pos (ellT_pos hL') (ellT_pos hL')
  have hr0 : 0 ≤ (1 - s) / (1 - t) := div_nonneg hxs.le hxt.le
  have h4 : (ellT L g t / ellT L g s) ^ 4 ≤ (((1 - s) / (1 - t)) ^ ((1 : ℝ) / 2)) ^ 4 :=
    pow_le_pow_left₀ hpos.le hC 4
  have h5 : (((1 - s) / (1 - t)) ^ ((1 : ℝ) / 2)) ^ 4 = ((1 - s) / (1 - t)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr0, ← Real.rpow_natCast]; norm_num
  rw [scaleFacts_etaT_div_etaT hE]
  exact h4.trans_eq h5

end RBM.Ind

/-! ## 6. Instances at `d = 3`

The size data are the merged preflight sequence `RBM.Gauss.SizesInst.sz0` (`L_n = 4(n+1)`,
`W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6} → 0`, `N_n = (W_n L_n)^3`; `n = 0`: `L = 4`, `W = 32`,
`lam = 1/64`, `N = 2097152`), admissible at `𝔠 = 1/6`, `𝔡 = 1/10` (`sz0_admissible`), and the
times of `RBM.Gauss.InductionDefsInst`: `s ≡ 0`, `t ≡ 1/16` (window of positive length), with
`(con_st_ind)` for every `𝔠_d > 0` (`conStInd_inst`).  Every deterministic hypothesis is
discharged; the ratio facts are checked at the sharp point `s = 1 - 10^{-4}`, `t = 1 - 4^{-1} 10^{-4}`
(both in the regime `g²/L² ≤ 1 - t ≤ g²` of `ℓ`: `ℓ_s = 25/16`, `ℓ_t = 25/8`, ratio `2`). -/

namespace RBM.Ind.ScaleFactsInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst Filter

/-- **R1 at `sz0`**: `𝔠 = 1/6`, `𝔡 = 1/10`, `τ = 1/10`, `t ≡ 1/16`: eventually, for all
`u ≤ 1/16`, `W^{-3} B_{u,0} ≤ 2 N^{-1/30}`; `Bandwidth`, `(eq:WO)` and the range condition
`N^{-9/10} ≤ 15/16` are discharged. -/
theorem R1_sz0 : ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, u ≤ tInst n →
    sz0.Bctl n u ≤ 2 * ((sz0.size n : ℕ) : ℝ) ^ (-(min (2 * (1 / 6) * (1 / 10)) (1 / 10 : ℝ))) := by
  refine Ind.scaleFacts_R1 sz0 (1 / 6) (1 / 10) (1 / 10) tInst (by norm_num) sz0_bandwidth sz0_WO ?_
  filter_upwards [sz0_tendsto.eventually_ge_atTop 256] with n hn
  have hN1 : (1 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) := by linarith
  have h1 : ((sz0.size n : ℕ) : ℝ) ^ (-1 + 1 / 10 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have h2 : ((sz0.size n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt ((sz0.size n : ℕ) : ℝ))⁻¹ := by
    rw [Real.rpow_neg (by linarith), ← Real.sqrt_eq_rpow]
  have h3 : (16 : ℝ) ≤ Real.sqrt ((sz0.size n : ℕ) : ℝ) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have h4 : (Real.sqrt ((sz0.size n : ℕ) : ℝ))⁻¹ ≤ (16 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h3
  simp only [tInst]
  norm_num at h4 ⊢
  linarith

/-- **R1 at `sz0`, the bound is a bound**: `2 N^{-1/30} < 1` once `N ≥ 4^{30}`, so eventually
`W^{-3} B_{1/16,0} < 1`. -/
theorem R1_sz0_lt_one : ∀ᶠ n : ℕ in atTop, sz0.Bctl n (1 / 16) < 1 := by
  filter_upwards [R1_sz0, sz0_tendsto.eventually_ge_atTop ((4 : ℝ) ^ 30)] with n h hn
  have hN1 : (1 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ 4 ^ 30 := one_le_pow₀ (by norm_num)
    linarith
  have h1 := h (1 / 16) (by simp [tInst])
  have hmin : min (2 * (1 / 6) * (1 / 10)) (1 / 10 : ℝ) = 1 / 30 := by
    rw [min_eq_left] <;> norm_num
  have h5 : ((4 : ℝ) ^ 30) ^ (1 / 30 : ℝ) = 4 := by
    rw [show (1 / 30 : ℝ) = ((30 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
  have h6 : ((4 : ℝ) ^ 30) ^ (1 / 30 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) ^ (1 / 30 : ℝ) :=
    Real.rpow_le_rpow (by norm_num) hn (by norm_num)
  have h7 : (4 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) ^ (1 / 30 : ℝ) := h5 ▸ h6
  have h2 : ((sz0.size n : ℕ) : ℝ) ^ (-(min (2 * (1 / 6) * (1 / 10)) (1 / 10 : ℝ))) ≤ 1 / 4 := by
    rw [hmin, Real.rpow_neg (by linarith)]
    calc (((sz0.size n : ℕ) : ℝ) ^ (1 / 30 : ℝ))⁻¹ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h7
      _ = 1 / 4 := by norm_num
  linarith

/-- **R2 at `sz0`** (sequence form): `s ≡ 0`, `t ≡ 1/16`, `𝔠_d = 1/100` (`conStInd_inst`):
eventually, for all `u ∈ [0, 1/16]`, `W^{-3} B_{u,0} ≤ (W^{-3} B_{0,0})^{99/100}`. -/
theorem R2_sz0 : ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, sInst n ≤ u → u ≤ tInst n →
    sz0.Bctl n u ≤ (sz0.Bctl n (sInst n)) ^ (1 - 1 / 100 : ℝ) :=
  Ind.scaleFacts_R2 sz0 (by norm_num) (conStInd_inst (by norm_num))
    (Eventually.of_forall fun n => by simp only [tInst]; norm_num)

/-- **R2, pointwise, at `sz0`**: at a size index `n` where `(con_st_ind)` holds (it holds
eventually, so such an `n` exists), `W^{-3} B_{1/32,0} ≤ (W^{-3} B_{0,0})^{99/100}`. -/
theorem R2_pt_sz0 : ∃ n : ℕ, sz0.Bctl n (1 / 32) ≤ (sz0.Bctl n 0) ^ (1 - 1 / 100 : ℝ) := by
  obtain ⟨n, hn⟩ := (conStInd_inst (𝔠d := 1 / 100) (by norm_num)).exists
  refine ⟨n, Ind.scaleFacts_R2_pt sz0 n (c := 1 / 100) (s := 0) (u := 1 / 32) (t := 1 / 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_⟩
  simpa [sInst, tInst] using hn.1

/-- **`STsize_pos` and `closure_scale` at `sz0`**: `N_0 > 0`, and at a size index `n` where
`(con_st_ind)` holds with `𝔠_d = 1/100` (`s = 0`, `t = u = 1/16`): `a_0 x_0/x_u ≤ a_0^{99/100}`. -/
theorem closure_sz0 : 0 < ((sz0.size 0 : ℕ) : ℝ) ∧
    ∃ n : ℕ, sz0.Bctl n 0 * ((1 - 0) / (1 - 1 / 16)) ≤ (sz0.Bctl n 0) ^ (1 - 1 / 100 : ℝ) := by
  refine ⟨Sizes.STsize_pos sz0 0, ?_⟩
  obtain ⟨n, hn⟩ := (conStInd_inst (𝔠d := 1 / 100) (by norm_num)).exists
  have hn1 : (sz0.Bctl n (1 / 16)) ^ (1 / 100 : ℝ) ≤ (1 - 1 / 16) / (1 - 0) := by
    simpa [sInst, tInst] using hn.1
  exact ⟨n, Ind.closure_scale (as := sz0.Bctl n 0) (at_ := sz0.Bctl n (1 / 16)) (xs := 1 - 0)
    (xt := 1 - 1 / 16) (xu := 1 - 1 / 16) (c := 1 / 100) (by norm_num)
    (Sizes.STBctl_pos sz0 n (by norm_num)) (Sizes.STBctl_mono sz0 n (by norm_num) (by norm_num))
    (by norm_num) (by norm_num) le_rfl hn1⟩

/-- `ℓ` at `n = 0` (`L = 4`, `g = lam 0 = 1/64`): `ℓ_s = 25/16` at `1 - s = 10^{-4}` and
`ℓ_t = 25/8` at `1 - t = (4 · 10^4)^{-1}` (`g/√x = 100/64`, `200/64`, both `≤ L = 4`). -/
theorem ell_values :
    ellT (sz0.L 0) (sz0.lam 0) (1 - 1 / 10000) = 25 / 16 ∧
      ellT (sz0.L 0) (sz0.lam 0) (1 - 1 / 40000) = 25 / 8 := by
  have hL : sz0.L 0 = 4 := sz0_values.1
  have hg : sz0.lam 0 = 1 / 64 := sz0_values.2.2.2
  have e1 : Real.sqrt |1 - (1 - 1 / 10000 : ℝ)| = 1 / 100 := by
    rw [show |1 - (1 - 1 / 10000 : ℝ)| = (1 / 100) ^ 2 by norm_num [abs_of_pos]]
    exact Real.sqrt_sq (by norm_num)
  have e2 : Real.sqrt |1 - (1 - 1 / 40000 : ℝ)| = 1 / 200 := by
    rw [show |1 - (1 - 1 / 40000 : ℝ)| = (1 / 200) ^ 2 by norm_num [abs_of_pos]]
    exact Real.sqrt_sq (by norm_num)
  refine ⟨?_, ?_⟩
  · unfold ellT
    rw [hL, hg, e1]
    norm_num
  · unfold ellT
    rw [hL, hg, e2]
    norm_num

/-- **The ratio facts at the sharp point**: `s = 1 - 10^{-4}`, `u = t = 1 - (4·10^4)^{-1}`:
`ℓ_t/ℓ_s = 2 = ((1 - s)/(1 - t))^{1/2}` (equality), and `(ℓ_t/ℓ_s)^4 = 16 = (η_s/η_t)^2` at
`E = 1/2` (`|E| < 2`). -/
theorem ratio_sz0 :
    ellT (sz0.L 0) (sz0.lam 0) (1 - 1 / 40000) / ellT (sz0.L 0) (sz0.lam 0) (1 - 1 / 10000) ≤
        ((1 - (1 - 1 / 10000)) / (1 - (1 - 1 / 40000) : ℝ)) ^ ((1 : ℝ) / 2) ∧
      (ellT (sz0.L 0) (sz0.lam 0) (1 - 1 / 40000) / ellT (sz0.L 0) (sz0.lam 0) (1 - 1 / 10000)) ^ 4 ≤
        (etaT (1 / 2) (1 - 1 / 10000) / etaT (1 / 2) (1 - 1 / 40000)) ^ 2 := by
  have hL : 1 ≤ sz0.L 0 := by have := sz0.three_le_L 0; omega
  exact ⟨Ind.scaleFacts_ellT_ratio hL (by norm_num) (by norm_num) (by norm_num),
    Ind.scaleFacts_ellT_pow_four hL (by norm_num) (by norm_num) (by norm_num)⟩

/-- The ratio is not slack at this point: both sides equal `2`. -/
theorem ratio_sz0_sharp :
    ellT (sz0.L 0) (sz0.lam 0) (1 - 1 / 40000) / ellT (sz0.L 0) (sz0.lam 0) (1 - 1 / 10000) = 2 ∧
      ((1 - (1 - 1 / 10000)) / (1 - (1 - 1 / 40000) : ℝ)) ^ ((1 : ℝ) / 2) = 2 := by
  refine ⟨by rw [ell_values.1, ell_values.2]; norm_num, ?_⟩
  rw [← Real.sqrt_eq_rpow, show ((1 - (1 - 1 / 10000)) / (1 - (1 - 1 / 40000) : ℝ)) = 2 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- **The `W^{-d}B` facts at `sz0`, `n = 0`** (`W = 32`, `lam = 1/64`, `L = 4`): positivity,
monotonicity `s = 0 ≤ u = 1/2`, the sharper `x B` monotonicity, the lower bound and the closure
`a^{1-c} ≤ (a^{3/8})^2` at `c = 1/100`, `a = W^{-3}B_{0,0} ≤ 1`. -/
theorem Bctl_facts_sz0 :
    0 < sz0.Bctl 0 0 ∧ sz0.Bctl 0 0 ≤ sz0.Bctl 0 (1 / 2) ∧
      (1 - 1 / 2) * sz0.Bctl 0 (1 / 2) ≤ (1 - 0) * sz0.Bctl 0 0 ∧
      (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ * (sz0.lam 0 ^ 2 + 1)⁻¹ ≤ sz0.Bctl 0 0 ∧
      sz0.Bctl 0 0 ^ (1 - 1 / 100 : ℝ) ≤ (sz0.Bctl 0 0 ^ (3 / 8 : ℝ)) ^ 2 := by
  have hpos := Sizes.STBctl_pos sz0 0 (t := 0) (by norm_num)
  have hle1 : sz0.Bctl 0 0 ≤ 1 := by
    have h := Bctl_const_le 0 (c := 0) (by norm_num)
    have hW : (32 : ℝ) ≤ ((sz0.W 0 : ℕ) : ℝ) := W_ge_32 0
    have h3 : (1 : ℝ) ≤ ((sz0.W 0 : ℕ) : ℝ) ^ 3 := one_le_pow₀ (by linarith)
    have h4 : (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h3
    have h5 : (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ ≤ 1 / 32 := by
      have : (32 : ℝ) ≤ ((sz0.W 0 : ℕ) : ℝ) ^ 3 := hW.trans (le_self_pow₀ (by linarith) (by norm_num))
      calc (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ ≤ (32 : ℝ)⁻¹ := inv_anti₀ (by norm_num) this
        _ = 1 / 32 := by norm_num
    norm_num at h
    linarith
  exact ⟨hpos, Sizes.STBctl_mono sz0 0 (by norm_num) (by norm_num),
    Sizes.STBctl_xmono sz0 0 (by norm_num) (by norm_num),
    Sizes.STBctl_ge sz0 0 le_rfl (by norm_num),
    Ind.closure_sq_le hpos hle1 (by norm_num)⟩


/-! ## 7. `scaleFacts_R1` feeds `forbidden_region` (the last hypothesis of the bootstrap)

Step 1 applies `forbidden_region` with `a = α = (W^{-d}B_{s,0})^{1/4}`, `b = 2α`,
`f = α^{3/2} = (W^{-d}B_{s,0})^{3/8}` (`STForbidden`, `Induction/Defs.lean`); its hypothesis
`f ≤ N^{-ε} a` is `a_s^{1/8} ≤ N^{-ε}`, which follows from `scaleFacts_R1` (`a_s ≤ 2 N^{-c₀}`,
`c₀ = 1/30` at `𝔠 = 1/6`, `𝔡 = 1/10`, `τ = 1/10`) with `ε = 1/480` once `N ≥ 2^{60}`.  Here the
whole chain is run at `sz0`, `s ≡ 0`, window `[0, 1/16]` (`TimeIcc sInst tInst n`), with the random
family `x = a_s^{3/8} obs` (so that `1(x ≤ 2α) x ≺ f` is `prec_of_le`). -/

/-- The family `x_n(u, ω) = (W^{-3} B_{0,0})^{3/8} · obs_n(ω)` on the window `[0, 1/16]`. -/
def xB (n : ℕ) (_ : Path.TimeIcc sInst tInst n) (ω : SeqΩ sz0) : ℝ :=
  (sz0.Bctl n 0) ^ (3 / 8 : ℝ) * StochDomAtInst.obs n ω

theorem xB_le_fB (n : ℕ) (u : Path.TimeIcc sInst tInst n) (ω : SeqΩ sz0) :
    xB n u ω ≤ (sz0.Bctl n 0) ^ (3 / 8 : ℝ) := by
  unfold xB
  have h0 : 0 ≤ (sz0.Bctl n 0) ^ (3 / 8 : ℝ) :=
    Real.rpow_nonneg (Sizes.STBctl_pos sz0 n (by norm_num)).le _
  calc (sz0.Bctl n 0) ^ (3 / 8 : ℝ) * StochDomAtInst.obs n ω ≤ (sz0.Bctl n 0) ^ (3 / 8 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left (StochDomAtInst.obs_le_one n ω) h0
    _ = _ := mul_one _

/-- `a_s^{1/8} ≤ N^{-1/480}` eventually, from `R1_sz0` (`a_s = W^{-3} B_{0,0}`). -/
theorem Bctl_eighth_le : ∀ᶠ n : ℕ in atTop,
    (sz0.Bctl n 0) ^ (1 / 8 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(1 / 480 : ℝ)) := by
  filter_upwards [R1_sz0, sz0_tendsto.eventually_ge_atTop ((2 : ℝ) ^ 60)] with n h hn
  set N : ℝ := ((sz0.size n : ℕ) : ℝ) with hNdef
  have hN1 : (1 : ℝ) ≤ N := by
    have : (1 : ℝ) ≤ 2 ^ 60 := one_le_pow₀ (by norm_num)
    linarith
  have hN0 : 0 < N := by linarith
  have ha : 0 < sz0.Bctl n 0 := Sizes.STBctl_pos sz0 n (by norm_num)
  have hmin : min (2 * (1 / 6) * (1 / 10)) (1 / 10 : ℝ) = 1 / 30 := by
    rw [min_eq_left] <;> norm_num
  have h1 : sz0.Bctl n 0 ≤ 2 * N ^ (-(1 / 30 : ℝ)) := by
    have := h 0 (by simp [tInst])
    rwa [hmin] at this
  have h2 : (sz0.Bctl n 0) ^ (1 / 8 : ℝ) ≤ (2 * N ^ (-(1 / 30 : ℝ))) ^ (1 / 8 : ℝ) :=
    Real.rpow_le_rpow ha.le h1 (by norm_num)
  have h3 : (2 * N ^ (-(1 / 30 : ℝ))) ^ (1 / 8 : ℝ) = (2 : ℝ) ^ (1 / 8 : ℝ) * N ^ (-(1 / 240 : ℝ)) := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hN0.le _), ← Real.rpow_mul hN0.le]
    congr 2; norm_num
  have h4 : (2 : ℝ) ^ (1 / 8 : ℝ) ≤ N ^ (1 / 480 : ℝ) := by
    have h5 : ((2 : ℝ) ^ 60) ^ (1 / 480 : ℝ) = (2 : ℝ) ^ (1 / 8 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1; norm_num
    rw [← h5]
    exact Real.rpow_le_rpow (by norm_num) hn (by norm_num)
  calc (sz0.Bctl n 0) ^ (1 / 8 : ℝ) ≤ (2 : ℝ) ^ (1 / 8 : ℝ) * N ^ (-(1 / 240 : ℝ)) := h3 ▸ h2
    _ ≤ N ^ (1 / 480 : ℝ) * N ^ (-(1 / 240 : ℝ)) :=
        mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hN0.le _)
    _ = N ^ (-(1 / 480 : ℝ)) := by
        rw [← Real.rpow_add hN0]; congr 1; norm_num

/-- **`forbidden_region` at `sz0` with the actual scales** (`Unif`, the only variant): `a = α =
(W^{-3}B_{0,0})^{1/4}`, `b = 2α`, `f = α^{3/2}`, `ε = 1/480`; the hypothesis `f ≤ N^{-ε} a` is
discharged from `scaleFacts_R1` (`Bctl_eighth_le`), `1(x ≤ 2α) x ≺ f` from `prec_of_le`.  Conclusion:
w.h.p. `x` avoids `[α, 2α]` for all `u ∈ [0, 1/16]` simultaneously. -/
theorem forbidden_region_Bctl_sz0 :
    HighProbAt (seqP sz0) sz0.size
      (fun n => {ω | ∀ u : Path.TimeIcc sInst tInst n,
        xB n u ω < (sz0.Bctl n 0) ^ (1 / 4 : ℝ) ∨ 2 * (sz0.Bctl n 0) ^ (1 / 4 : ℝ) < xB n u ω}) := by
  refine PerTimeCalc.Unif.forbidden_region StochDomAtInst.tendsto_sz0_size
    (x := xB) (f := fun n _ => (sz0.Bctl n 0) ^ (3 / 8 : ℝ))
    (a := fun n _ => (sz0.Bctl n 0) ^ (1 / 4 : ℝ)) (b := fun n _ => 2 * (sz0.Bctl n 0) ^ (1 / 4 : ℝ))
    (fun n _ => Real.rpow_pos_of_pos (Sizes.STBctl_pos sz0 n (by norm_num)) _)
    (ε := 1 / 480) (by norm_num) ?_ ?_
  · filter_upwards [Bctl_eighth_le] with n hn u
    have ha : 0 < sz0.Bctl n 0 := Sizes.STBctl_pos sz0 n (by norm_num)
    have h8 : (sz0.Bctl n 0) ^ (3 / 8 : ℝ) =
        (sz0.Bctl n 0) ^ (1 / 8 : ℝ) * (sz0.Bctl n 0) ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add ha]; congr 1; norm_num
    rw [h8]
    exact mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg ha.le _)
  · refine Sizes.prec_of_le sz0 (ζ := fun n u _ => (sz0.Bctl n 0) ^ (3 / 8 : ℝ))
      (fun n u _ => Real.rpow_nonneg (Sizes.STBctl_pos sz0 n (by norm_num)).le _) fun n u ω => ?_
    by_cases hx : xB n u ω ≤ 2 * (sz0.Bctl n 0) ^ (1 / 4 : ℝ)
    · rw [Set.indicator_of_mem (show ω ∈ {ω | xB n u ω ≤ 2 * (sz0.Bctl n 0) ^ (1 / 4 : ℝ)} from hx)]
      exact xB_le_fB n u ω
    · rw [Set.indicator_of_notMem
        (show ω ∉ {ω | xB n u ω ≤ 2 * (sz0.Bctl n 0) ^ (1 / 4 : ℝ)} from hx)]
      exact Real.rpow_nonneg (Sizes.STBctl_pos sz0 n (by norm_num)).le _

end RBM.Ind.ScaleFactsInst

/-! ## 8. `scaleFacts_R1` is false without `(eq:WO)` (compiled negative statement)

All other hypotheses of `scaleFacts_R1` hold for the size data below (`d = 3`, `ilambda ≡ 0`,
`W_n = L_n = n + 3`, so `N = W^6`, `Bandwidth (1/6)`, `N^{-1+τ} = 1 - t_n` with `τ = 1/10`), `(eq:WO)`
fails, and the conclusion fails at every `n` (at `u = t_n`): `W^{-3} B_{t_n,0} ≥ (W^3 N^{-9/10})^{-1}
≥ W^2 ≥ 9 > 2 ≥ 2 N^{-1/30}`.  This is why the `d ≥ 3` reading of RBM2D's `scaleFacts_R1` has the
extra hypothesis `sz.WO 𝔡` (T2045a). -/

namespace RBM.Ind.ScaleFactsNeg

/-- Size data at `d = 3` with `ilambda ≡ 0` and `W_n = L_n = n + 3`: `N_n = (n+3)^6`, `W = N^{1/6}`. -/
def szNoWO : Sizes 3 where
  L := fun n => n + 3
  W := fun n => n + 3
  lam := fun _ => 0
  three_le_L := fun n => by omega
  W_pos := fun n => by omega

theorem szNoWO_size (n : ℕ) : ((szNoWO.size n : ℕ) : ℝ) = ((n : ℝ) + 3) ^ 6 := by
  simp only [Sizes.size, szNoWO]
  push_cast
  ring

/-- The times `t_n = 1 - N_n^{-9/10}` (`N^{-1+τ} = 1 - t`, `τ = 1/10`). -/
def tNoWO (n : ℕ) : ℝ := 1 - ((szNoWO.size n : ℕ) : ℝ) ^ (-(9 / 10 : ℝ))

theorem scaleFacts_R1_needs_WO :
    szNoWO.Bandwidth (1 / 6) ∧
      (∀ n, ((szNoWO.size n : ℕ) : ℝ) ^ (-1 + 1 / 10 : ℝ) ≤ 1 - tNoWO n) ∧
      (∀ n, 2 * ((szNoWO.size n : ℕ) : ℝ) ^ (-(min (2 * (1 / 6) * (1 / 10)) (1 / 10 : ℝ))) <
        szNoWO.Bctl n (tNoWO n)) ∧ ¬ szNoWO.WO (1 / 10) := by
  have hW : ∀ n : ℕ, (3 : ℝ) ≤ (n : ℝ) + 3 := fun n => by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Eventually.of_forall fun n => ?_
    rw [szNoWO_size, show (1 / 6 : ℝ) = ((6 : ℕ) : ℝ)⁻¹ by norm_num,
      Real.pow_rpow_inv_natCast (by linarith [hW n]) (by norm_num)]
    simp [szNoWO]
  · intro n
    unfold tNoWO
    refine le_of_eq ?_
    norm_num
  · intro n
    set N : ℝ := ((szNoWO.size n : ℕ) : ℝ) with hN
    have hw : (3 : ℝ) ≤ (n : ℝ) + 3 := hW n
    have hN6 : N = ((n : ℝ) + 3) ^ 6 := szNoWO_size n
    have hN1 : (1 : ℝ) ≤ N := by rw [hN6]; exact one_le_pow₀ (by linarith)
    have hN0 : 0 < N := by linarith
    have hx0 : 0 < N ^ (-(9 / 10 : ℝ)) := Real.rpow_pos_of_pos hN0 _
    have h2 : 2 * N ^ (-(min (2 * (1 / 6) * (1 / 10)) (1 / 10 : ℝ))) ≤ 2 := by
      have : N ^ (-(min (2 * (1 / 6) * (1 / 10)) (1 / 10 : ℝ))) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hN1 (by
          have : (0 : ℝ) ≤ min (2 * (1 / 6) * (1 / 10)) (1 / 10 : ℝ) := le_min (by norm_num) (by norm_num)
          linarith)
      linarith
    have hxx : |1 - (1 - N ^ (-(9 / 10 : ℝ)))| = N ^ (-(9 / 10 : ℝ)) := by
      rw [sub_sub_cancel, abs_of_pos hx0]
    have hB : szNoWO.Bctl n (tNoWO n) = (((n : ℝ) + 3) ^ 3)⁻¹ *
        ((N ^ (-(9 / 10 : ℝ)))⁻¹ + (((n : ℝ) + 3) ^ 3 * N ^ (-(9 / 10 : ℝ)))⁻¹) := by
      unfold Sizes.Bctl Bparam tNoWO
      rw [← hN, hxx]
      have hz : (((0 : ℕ) : ℝ) + 1) ^ (3 - 2) = 1 := by norm_num
      simp only [hz, inv_one, mul_one, szNoWO]
      push_cast
      ring
    have hb : (((n : ℝ) + 3) ^ 3)⁻¹ * (N ^ (-(9 / 10 : ℝ)))⁻¹ ≤ szNoWO.Bctl n (tNoWO n) := by
      rw [hB]
      have hL3 : 0 ≤ (((n : ℝ) + 3) ^ 3 * N ^ (-(9 / 10 : ℝ)))⁻¹ := by positivity
      have hW0 : 0 ≤ (((n : ℝ) + 3) ^ 3)⁻¹ := by positivity
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hL3) hW0
    -- `N^{9/10} ≥ N^{5/6} = (n+3)^5`
    have h5 : ((n : ℝ) + 3) ^ 5 ≤ N ^ (9 / 10 : ℝ) := by
      have h1 : N ^ (5 / 6 : ℝ) ≤ N ^ (9 / 10 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      have h2 : N ^ (5 / 6 : ℝ) = ((n : ℝ) + 3) ^ 5 := by
        rw [hN6, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
        have : ((6 : ℕ) : ℝ) * (5 / 6 : ℝ) = ((5 : ℕ) : ℝ) := by norm_num
        rw [this, Real.rpow_natCast]
      linarith
    have hinv : (N ^ (-(9 / 10 : ℝ)))⁻¹ = N ^ (9 / 10 : ℝ) := by
      rw [Real.rpow_neg hN0.le, inv_inv]
    rw [hinv] at hb
    have hw3 : (0 : ℝ) < ((n : ℝ) + 3) ^ 3 := by positivity
    have hge : (((n : ℝ) + 3) ^ 3)⁻¹ * ((n : ℝ) + 3) ^ 5 ≤ (((n : ℝ) + 3) ^ 3)⁻¹ * N ^ (9 / 10 : ℝ) :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    have hval : (((n : ℝ) + 3) ^ 3)⁻¹ * ((n : ℝ) + 3) ^ 5 = ((n : ℝ) + 3) ^ 2 := by
      field_simp
    have h9 : (9 : ℝ) ≤ ((n : ℝ) + 3) ^ 2 := by nlinarith
    linarith
  · intro h
    obtain ⟨n, hn⟩ := h.exists
    have h1 := hn.1
    have : (0 : ℝ) < ((szNoWO.W n : ℕ) : ℝ) ^ (-((3 : ℕ) : ℝ) / 2 + 1 / 10) :=
      Real.rpow_pos_of_pos (by exact_mod_cast szNoWO.W_pos n) _
    have h0 : szNoWO.lam n = 0 := rfl
    rw [h0] at h1
    linarith

end RBM.Ind.ScaleFactsNeg

