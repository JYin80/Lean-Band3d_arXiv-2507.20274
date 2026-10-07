/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.FlowPins
import RBM3D.BA.CombesThomas
import RBM3D.Defs.RadialSum

/-!
# `(prop:ThfadC_short)` for the block Anderson propagator (BA-P1)

Ticket T2308.  Proof of the merged owed pin `BAProp5s` (`RBM3D/BA/FlowPins.lean`):
`|Θ_t^{(σ,σ)}(0,a)| ≤ C (1_{a=0} + g² e^{-c|a|})` for `Θ_t^{(σ,σ)} = (1 - t M^{(σ,σ)})⁻¹` of the
block Anderson model, uniformly in `L ≥ 3`, `0 < g ≤ Λ`, `t ∈ [0, 1]`, both `σ`, at the real-axis
datum `BAReal`.  Paper `1_2:1146-1150` (`lem_propTH` (5s)), proof `A:23-41`, `(eq:off_diagM)`
`A:32-34`.

Route (differs from the Neumann series `(eq:expMLn)` of `A:26-41`, same statement): a weighted `ℓ^∞`
(Combes-Thomas) estimate for the row equation of `(1 - tQ)Θ = 1` (`BApropQ_decay`,
`BApropQ_offdiag`).  The row hypothesis is the weighted off-diagonal row sum
`t Σ_{x≠y} e^{μ|y-x|} |Q_yx| ≤ (1 - ε/2) |1 - tq|` (`BAp5s_row_weighted`), from `BAoffDiag_scalar`
(Ward, `Ward.lean`) for the unweighted part and from the Combes-Thomas entry bounds `BAMB_sq_off_le`
(`CombesThomas.lean`) plus `Σ_x e^{-c|x|} ≤ expC` (`RadialSum.lean`) for the weight.  The `(-,-)`
case runs through the same lemmas (only norms of entries enter; `|1 - t m̄²| = |1 - tm²|`).

Constants `C = BAp5s_C d Λ κ`, `c = BAp5s_rate d Λ κ` depend on `(d, Λ, κ)` only (§18; `1_2:1150`).
Premises not used: `t < 1` (the bound holds at `t = 1`), `3 ≤ d` beyond `2 ≤ d`.  No statement
mentions a law.
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false

noncomputable section

open Matrix

namespace RBM.BA

open RBM RBM.Gauss

/-! ## 1. The constants -/

/-- `A = 4 (C/c)²` (`C = BAct_C d κ`, `c = BAct_rate d Λ κ`): `|M_xy|² ≤ A g² e^{-2c|x-y|}` for `x ≠ y`. -/
def BAp5s_A (d : ℕ) (Λ κ : ℝ) : ℝ := 4 * (BAct_C d κ / BAct_rate d Λ κ) ^ 2

/-- `S = expC (d-2) c`: `Σ_x e^{-c|y-x|} ≤ S` on `Z_L^d`, uniformly in `L` (`RadialSum.lean:275`, `d = (d-2)+2`). -/
def BAp5s_S (d : ℕ) (Λ κ : ℝ) : ℝ := RBM.expC (d - 2) (BAct_rate d Λ κ)

/-- The rate `μ = min c (ε² c / (2 A Λ² S))`, `ε = κ²/4` (the `ε` of `BAoffDiag_scalar`). -/
def BAp5s_rate (d : ℕ) (Λ κ : ℝ) : ℝ :=
  min (BAct_rate d Λ κ) ((κ ^ 2 / 4) ^ 2 * BAct_rate d Λ κ / (2 * BAp5s_A d Λ κ * Λ ^ 2 * BAp5s_S d Λ κ))

/-- The constant `C₅ = 2/ε² + 2 A S/ε³`, `ε = κ²/4`. -/
def BAp5s_C (d : ℕ) (Λ κ : ℝ) : ℝ :=
  2 / (κ ^ 2 / 4) ^ 2 + 2 * BAp5s_A d Λ κ * BAp5s_S d Λ κ / (κ ^ 2 / 4) ^ 3

private theorem BP5_expC_pos (k : ℕ) {c : ℝ} (hc : 0 < c) : 0 < RBM.expC k c := by
  unfold RBM.expC
  positivity

private theorem BP5_A_pos (d : ℕ) (Λ κ : ℝ) (hd : 0 < d) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    0 < BAp5s_A d Λ κ := by
  have h1 := BAct_C_pos d κ hd hκ
  have h2 := BAct_rate_pos d Λ κ hd hΛ hκ
  unfold BAp5s_A
  positivity

private theorem BP5_S_pos (d : ℕ) (Λ κ : ℝ) (hd : 0 < d) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    0 < BAp5s_S d Λ κ :=
  BP5_expC_pos _ (BAct_rate_pos d Λ κ hd hΛ hκ)

theorem BAp5s_C_pos (d : ℕ) (Λ κ : ℝ) (hd : 0 < d) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    0 < BAp5s_C d Λ κ := by
  have h1 := BP5_A_pos d Λ κ hd hΛ hκ
  have h2 := BP5_S_pos d Λ κ hd hΛ hκ
  unfold BAp5s_C
  positivity

theorem BAp5s_rate_pos (d : ℕ) (Λ κ : ℝ) (hd : 0 < d) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    0 < BAp5s_rate d Λ κ := by
  have h1 := BP5_A_pos d Λ κ hd hΛ hκ
  have h2 := BP5_S_pos d Λ κ hd hΛ hκ
  have h3 := BAct_rate_pos d Λ κ hd hΛ hκ
  unfold BAp5s_rate
  exact lt_min h3 (by positivity)

/-! ## 2. The matrices `M^{(σ,σ)}`: entries, diagonal, row sums -/

section Entries

variable (d L : ℕ) [NeZero L]

/-- `|M^{(σ,σ)}_{xy}| = |M_xy|²` for both `σ` (any `z, m`). -/
theorem BAMss_ss_norm (g : ℝ) (z m : ℂ) (σ : Bool) (x y : Zd d L) :
    ‖BAMss d L (BAMB d L g z m) σ σ x y‖ = ‖BAMB d L g z m x y‖ ^ 2 := by
  have hs := BAMB_symm d L g z m y x
  cases σ
  · simp only [BAMss, BAMsigma, Matrix.of_apply, Bool.false_eq_true, ite_false,
      Matrix.conjTranspose_apply, norm_mul, Complex.norm_conj, Complex.star_def]
    rw [hs, sq]
  · simp only [BAMss, BAMsigma, Matrix.of_apply, ite_true, norm_mul]
    rw [hs, sq]

/-- The diagonal of `M^{(σ,σ)}` is `m(σ)²` at a solution of `(self_m)`. -/
theorem BAMss_ss_diag (g : ℝ) (z m : ℂ) (h : BASelf d L g z m) (σ : Bool) (y : Zd d L) :
    BAMss d L (BAMB d L g z m) σ σ y y = (if σ then m else star m) ^ 2 := by
  have hd := BAMB_diag_eq d L g z m h y
  cases σ
  · simp only [BAMss, BAMsigma, Matrix.of_apply, Bool.false_eq_true, ite_false,
      Matrix.conjTranspose_apply, hd]
    rw [sq]
  · simp only [BAMss, BAMsigma, Matrix.of_apply, ite_true, hd]
    rw [sq]

/-- Every row of `M'^{(σ,σ)}` (diagonal removed) sums to `1 - |m|²` (Ward, row `y`). -/
theorem BAMss_row_offdiag_sum (g E : ℝ) (m : ℂ) (h : BASelf d L g (E : ℂ) m) (σ : Bool) (y : Zd d L) :
    ∑ x ∈ Finset.univ.erase y, ‖BAMss d L (BAMB d L g (E : ℂ) m) σ σ y x‖ = 1 - ‖m‖ ^ 2 := by
  simp only [BAMss_ss_norm d L g (E : ℂ) m σ y]
  have h2 := Finset.add_sum_erase (Finset.univ : Finset (Zd d L))
    (fun a => ‖BAMB d L g (E : ℂ) m y a‖ ^ 2) (Finset.mem_univ y)
  rw [BAMB_row_sq_real d L g E m h y, BAMB_diag_eq d L g (E : ℂ) m h y] at h2
  linarith

end Entries

/-- `|1 - t m(σ)²| = |1 - t m²|` (`t` real). -/
theorem BAnorm_one_sub_tq_sigma (t : ℝ) (m : ℂ) (σ : Bool) :
    ‖1 - (t : ℂ) * (if σ then m else star m) ^ 2‖ = ‖1 - (t : ℂ) * m ^ 2‖ := by
  cases σ
  · have : (1 : ℂ) - (t : ℂ) * (star m) ^ 2 = star (1 - (t : ℂ) * m ^ 2) := by
      simp [star_sub, star_mul', star_pow, Complex.star_def]
    simp only [Bool.false_eq_true, ite_false]
    rw [this, Complex.star_def, Complex.norm_conj]
  · simp

/-! ## 3. Entry bound off the diagonal and the torus sum -/

section Bounds

variable (d L : ℕ) [NeZero L]

private theorem BP5_exp_neg_ge_quarter (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 / 4 ≤ Real.exp (-x) := by
  have h1 : 1 - x / 2 ≤ Real.exp (-(x / 2)) := by
    have := Real.add_one_le_exp (-(x / 2))
    linarith
  have h2 : Real.exp (-x) = Real.exp (-(x / 2)) ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  rw [h2]
  have h3 : (1 : ℝ) / 2 ≤ Real.exp (-(x / 2)) := by linarith
  nlinarith

/-- Off the diagonal, `|M_xy|² ≤ A g² e^{-2c|x-y|}` for every `0 < g ≤ Λ` (both branches of T2290). -/
theorem BAMB_sq_off_le (hL : 3 ≤ L) (hd : 0 < d) (Λ g κ E : ℝ) (m : ℂ) (hΛ : 0 < Λ) (hg : 0 < g)
    (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (x y : Zd d L) (hxy : x ≠ y) :
    ‖BAMB d L g (E : ℂ) m x y‖ ^ 2
      ≤ BAp5s_A d Λ κ * g ^ 2 * Real.exp (-(2 * BAct_rate d Λ κ * (zdistD d L (x - y) : ℝ))) := by
  set C₀ := BAct_C d κ with hC₀
  set c₀ := BAct_rate d Λ κ with hc₀
  have hC₀p : 0 < C₀ := BAct_C_pos d κ hd hκ
  have hc₀p : 0 < c₀ := BAct_rate_pos d Λ κ hd hΛ hκ
  have hκ1 : κ ≤ 1 := by
    have h1 := BAm_norm_le_one d L g (E : ℂ) m (by simp) hr.1
    have h2 := Complex.im_le_norm m
    linarith [hr.2]
  have hc₀h : c₀ ≤ 1 / 2 := by
    have : c₀ ≤ κ / 2 := min_le_right _ _
    linarith
  set r := zdistD d L (x - y) with hrdef
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exact absurd (sub_eq_zero.mp ((zdistD_eq_zero_iff d L).mp h0)) hxy
    · exact h0
  have hAg : BAp5s_A d Λ κ = 4 * (C₀ / c₀) ^ 2 := rfl
  rw [hAg]
  by_cases hsm : g < (2 * C₀)⁻¹
  · -- small coupling: `|M_xy| ≤ (C₀ g)^r`
    have hw : 1 / 4 ≤ Real.exp (-(2 * c₀)) :=
      BP5_exp_neg_ge_quarter (2 * c₀) (by positivity) (by linarith)
    have hexp : Real.exp (-(2 * c₀ * (r : ℝ))) = Real.exp (-(2 * c₀)) ^ r := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [hexp]
    set w := Real.exp (-(2 * c₀)) with hwdef
    have hw0 : 0 < w := Real.exp_pos _
    have h1 := BAMB_upper_small d L hL hd g κ E m hg hκ hr hsm x y
    rw [← hrdef] at h1
    have hu : (C₀ * g) ^ 2 ≤ 1 / 4 := by
      have h3 : g * (2 * C₀) < 1 := by
        have := mul_lt_mul_of_pos_right hsm (by positivity : 0 < 2 * C₀)
        rwa [inv_mul_cancel₀ (by positivity)] at this
      have h5 : C₀ * g < 1 / 2 := by linarith
      have h4 : 0 ≤ C₀ * g := by positivity
      nlinarith
    have hu0 : 0 ≤ (C₀ * g) ^ 2 := by positivity
    have h2 : ‖BAMB d L g (E : ℂ) m x y‖ ^ 2 ≤ ((C₀ * g) ^ 2) ^ r := by
      calc ‖BAMB d L g (E : ℂ) m x y‖ ^ 2 ≤ ((C₀ * g) ^ r) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ = ((C₀ * g) ^ 2) ^ r := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    obtain ⟨s, hs⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    have h3 : ((C₀ * g) ^ 2) ^ r ≤ 4 * (C₀ * g) ^ 2 * w ^ r := by
      rw [hs, pow_succ, pow_succ]
      have h5 : ((C₀ * g) ^ 2) ^ s ≤ w ^ s := pow_le_pow_left₀ hu0 (by linarith) s
      have h6 : 0 ≤ w ^ s := by positivity
      have h7 : w ^ s ≤ 4 * (w ^ s * w) := by nlinarith
      calc ((C₀ * g) ^ 2) ^ s * (C₀ * g) ^ 2 ≤ w ^ s * (C₀ * g) ^ 2 :=
            mul_le_mul_of_nonneg_right h5 hu0
        _ = (C₀ * g) ^ 2 * w ^ s := by ring
        _ ≤ (C₀ * g) ^ 2 * (4 * (w ^ s * w)) := mul_le_mul_of_nonneg_left h7 hu0
        _ = 4 * (C₀ * g) ^ 2 * (w ^ s * w) := by ring
    have h4 : 4 * (C₀ * g) ^ 2 ≤ 4 * (C₀ / c₀) ^ 2 * g ^ 2 := by
      have : C₀ ≤ C₀ / c₀ := by
        rw [le_div_iff₀ hc₀p]; nlinarith
      have h8 : (C₀ * g) ^ 2 ≤ (C₀ / c₀ * g) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right this hg.le) 2
      nlinarith [h8]
    calc ‖BAMB d L g (E : ℂ) m x y‖ ^ 2 ≤ 4 * (C₀ * g) ^ 2 * w ^ r := h2.trans h3
      _ ≤ 4 * (C₀ / c₀) ^ 2 * g ^ 2 * w ^ r :=
          mul_le_mul_of_nonneg_right h4 (by positivity)
  · -- large coupling: `|M_xy| ≤ c₀⁻¹ e^{-c₀ r}`
    have hge : (2 * C₀)⁻¹ ≤ g := not_lt.mp hsm
    have h1 := BAMB_decay_large d L hL hd Λ g κ E m hΛ hg hgΛ hκ hr x y
    rw [← hrdef] at h1
    have h2 : ‖BAMB d L g (E : ℂ) m x y‖ ^ 2 ≤ (c₀⁻¹ * Real.exp (-c₀ * (r : ℝ))) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : (c₀⁻¹ * Real.exp (-c₀ * (r : ℝ))) ^ 2
        = c₀⁻¹ ^ 2 * Real.exp (-(2 * c₀ * (r : ℝ))) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    have h4 : 1 ≤ 2 * C₀ * g := by
      have := mul_le_mul_of_nonneg_left hge (by positivity : 0 ≤ 2 * C₀)
      rwa [mul_inv_cancel₀ (by positivity)] at this
    have h5 : 4 * (C₀ / c₀) ^ 2 * g ^ 2 = c₀⁻¹ ^ 2 * (2 * C₀ * g) ^ 2 := by
      field_simp
      norm_num
    have h6 : c₀⁻¹ ^ 2 ≤ 4 * (C₀ / c₀) ^ 2 * g ^ 2 := by
      rw [h5]
      have : (1 : ℝ) ≤ (2 * C₀ * g) ^ 2 := by nlinarith
      have h7 : 0 ≤ c₀⁻¹ ^ 2 := by positivity
      nlinarith
    calc ‖BAMB d L g (E : ℂ) m x y‖ ^ 2 ≤ c₀⁻¹ ^ 2 * Real.exp (-(2 * c₀ * (r : ℝ))) := h2.trans h3.le
      _ ≤ 4 * (C₀ / c₀) ^ 2 * g ^ 2 * Real.exp (-(2 * c₀ * (r : ℝ))) :=
          mul_le_mul_of_nonneg_right h6 (Real.exp_pos _).le

/-- `Σ_x e^{-c|y-x|} ≤ expC (d-2) c` on `Z_L^d`, `d ≥ 2`, uniformly in `L` and `y`. -/
theorem BAsum_exp_decay_le (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) (y : Zd d L) :
    ∑ x : Zd d L, Real.exp (-(c * (zdistD d L (y - x) : ℝ))) ≤ RBM.expC (d - 2) c := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  rw [sum_shift (k + 2) y (fun r : ℕ => Real.exp (-(c * (r : ℝ))))]
  have := sum_radial_exp_decay_le (L := L) k hc
  simpa using this

end Bounds

/-! ## 4. The weighted `ℓ^∞` estimate for `Θ = (1 - tQ)⁻¹` -/

section Weighted

variable (d L : ℕ) [NeZero L]

/-- The row equation of `(1 - tQ)Θ = 1` at the entry `(y, a)`, with the diagonal `Q_yy = q` split off. -/
private theorem BP5_row_identity (Q : Matrix (Zd d L) (Zd d L) ℂ) (q : ℂ) (t : ℝ)
    (hQ : ∀ y, Q y y = q) (hU : IsUnit (1 - (t : ℂ) • Q)) (y a : Zd d L) :
    (1 - (t : ℂ) * q) * PropThetaQ Q t y a
      = (if y = a then (1 : ℂ) else 0)
        + (t : ℂ) * ∑ x ∈ Finset.univ.erase y, Q y x * PropThetaQ Q t x a := by
  have h := Ring.mul_inverse_cancel _ hU
  have h1 := congrFun (congrFun h y) a
  change ((1 - (t : ℂ) • Q) * PropThetaQ Q t) y a = (1 : Matrix (Zd d L) (Zd d L) ℂ) y a at h1
  rw [Matrix.mul_apply] at h1
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, sub_mul, Finset.sum_sub_distrib,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, smul_eq_mul] at h1
  have h2 := Finset.add_sum_erase (Finset.univ : Finset (Zd d L))
    (fun x => (t : ℂ) * Q y x * PropThetaQ Q t x a) (Finset.mem_univ y)
  simp only [hQ y] at h2
  have h3 : ∑ x ∈ Finset.univ.erase y, (t : ℂ) * Q y x * PropThetaQ Q t x a
      = (t : ℂ) * ∑ x ∈ Finset.univ.erase y, Q y x * PropThetaQ Q t x a := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [h3] at h2
  linear_combination h1 - h2

/-- The triangle inequality for the weight: `e^{μ|y-a|} ≤ e^{μ|y-x|} e^{μ|x-a|}`. -/
private theorem BP5_weight_tri (μ : ℝ) (hμ : 0 ≤ μ) (x y a : Zd d L) :
    Real.exp (μ * (zdistD d L (y - a) : ℝ))
      ≤ Real.exp (μ * (zdistD d L (y - x) : ℝ)) * Real.exp (μ * (zdistD d L (x - a) : ℝ)) := by
  rw [← Real.exp_add, ← mul_add]
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hμ
  have h := zdistD_add_le d L (y - x) (x - a)
  rw [show y - x + (x - a) = y - a by ring] at h
  exact_mod_cast h

/-- **The weighted `ℓ^∞` estimate** for `Θ = (1 - tQ)⁻¹` (`PropThetaQ`), `Q` with constant diagonal `q`,
gap `ε ≤ |1 - tq|` and weighted off-diagonal row sums `t Σ_{x≠y} e^{μ|y-x|}|Q_yx| ≤ (1 - ε/2)|1 - tq|`. -/
theorem BApropQ_decay (Q : Matrix (Zd d L) (Zd d L) ℂ) (q : ℂ) (t ε μ : ℝ)
    (hQ : ∀ y, Q y y = q) (hε : 0 < ε) (hεD : ε ≤ ‖1 - (t : ℂ) * q‖) (hμ : 0 ≤ μ) (ht : 0 ≤ t)
    (hrow : ∀ y, t * ∑ x ∈ Finset.univ.erase y, Real.exp (μ * (zdistD d L (y - x) : ℝ)) * ‖Q y x‖
        ≤ (1 - ε / 2) * ‖1 - (t : ℂ) * q‖)
    (y a : Zd d L) :
    ‖PropThetaQ Q t y a‖ ≤ 2 / ε ^ 2 * Real.exp (-(μ * (zdistD d L (y - a) : ℝ))) := by
  by_cases hU : IsUnit (1 - (t : ℂ) • Q)
  swap
  · have h0 : PropThetaQ Q t = 0 := Ring.inverse_non_unit _ hU
    rw [h0]
    simp only [Matrix.zero_apply, norm_zero]
    positivity
  set D : ℂ := 1 - (t : ℂ) * q with hD
  have hDpos : 0 < ‖D‖ := lt_of_lt_of_le hε hεD
  set v : Zd d L → ℝ := fun y => Real.exp (μ * (zdistD d L (y - a) : ℝ)) * ‖PropThetaQ Q t y a‖ with hv
  obtain ⟨y0, hy0⟩ := Finite.exists_max v
  have hv0 : ∀ y, 0 ≤ v y := fun y => by positivity
  have key : ∀ y, ‖D‖ * v y ≤ 1 + (1 - ε / 2) * ‖D‖ * v y0 := by
    intro y
    have hid := BP5_row_identity d L Q q t hQ hU y a
    have hn : ‖D‖ * ‖PropThetaQ Q t y a‖
        ≤ (if y = a then (1 : ℝ) else 0)
          + t * ∑ x ∈ Finset.univ.erase y, ‖Q y x‖ * ‖PropThetaQ Q t x a‖ := by
      calc ‖D‖ * ‖PropThetaQ Q t y a‖ = ‖D * PropThetaQ Q t y a‖ := (norm_mul _ _).symm
        _ = ‖(if y = a then (1 : ℂ) else 0)
              + (t : ℂ) * ∑ x ∈ Finset.univ.erase y, Q y x * PropThetaQ Q t x a‖ := by rw [hid]
        _ ≤ ‖(if y = a then (1 : ℂ) else 0)‖
              + ‖(t : ℂ) * ∑ x ∈ Finset.univ.erase y, Q y x * PropThetaQ Q t x a‖ := norm_add_le _ _
        _ ≤ (if y = a then (1 : ℝ) else 0)
              + t * ∑ x ∈ Finset.univ.erase y, ‖Q y x‖ * ‖PropThetaQ Q t x a‖ := by
            apply add_le_add
            · split_ifs <;> simp
            · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
              apply mul_le_mul_of_nonneg_left _ ht
              refine (norm_sum_le _ _).trans ?_
              exact Finset.sum_le_sum fun x _ => (norm_mul _ _).le
    have hey : 0 < Real.exp (μ * (zdistD d L (y - a) : ℝ)) := Real.exp_pos _
    have h1 : ‖D‖ * v y ≤ Real.exp (μ * (zdistD d L (y - a) : ℝ)) * (if y = a then (1 : ℝ) else 0)
        + t * ∑ x ∈ Finset.univ.erase y, Real.exp (μ * (zdistD d L (y - x) : ℝ)) * ‖Q y x‖ * v y0 := by
      have h2 : ‖D‖ * v y = Real.exp (μ * (zdistD d L (y - a) : ℝ)) * (‖D‖ * ‖PropThetaQ Q t y a‖) := by
        simp only [hv]; ring
      rw [h2]
      have h3 := mul_le_mul_of_nonneg_left hn hey.le
      refine h3.trans ?_
      rw [mul_add]
      apply add_le_add le_rfl
      rw [mul_left_comm, Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ ht
      apply Finset.sum_le_sum
      intro x _
      have h4 := BP5_weight_tri d L μ hμ x y a
      have h5 : v x ≤ v y0 := hy0 x
      calc Real.exp (μ * (zdistD d L (y - a) : ℝ)) * (‖Q y x‖ * ‖PropThetaQ Q t x a‖)
          = ‖Q y x‖ * (Real.exp (μ * (zdistD d L (y - a) : ℝ)) * ‖PropThetaQ Q t x a‖) := by ring
        _ ≤ ‖Q y x‖ * (Real.exp (μ * (zdistD d L (y - x) : ℝ)) * v x) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            calc Real.exp (μ * (zdistD d L (y - a) : ℝ)) * ‖PropThetaQ Q t x a‖
                ≤ (Real.exp (μ * (zdistD d L (y - x) : ℝ)) * Real.exp (μ * (zdistD d L (x - a) : ℝ)))
                    * ‖PropThetaQ Q t x a‖ := mul_le_mul_of_nonneg_right h4 (norm_nonneg _)
              _ = Real.exp (μ * (zdistD d L (y - x) : ℝ)) * v x := by simp only [hv]; ring
        _ ≤ ‖Q y x‖ * (Real.exp (μ * (zdistD d L (y - x) : ℝ)) * v y0) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            exact mul_le_mul_of_nonneg_left h5 (Real.exp_pos _).le
        _ = Real.exp (μ * (zdistD d L (y - x) : ℝ)) * ‖Q y x‖ * v y0 := by ring
    have h6 : Real.exp (μ * (zdistD d L (y - a) : ℝ)) * (if y = a then (1 : ℝ) else 0) ≤ 1 := by
      split_ifs with hya
      · subst hya
        simp
      · simp
    have h7 : t * ∑ x ∈ Finset.univ.erase y, Real.exp (μ * (zdistD d L (y - x) : ℝ)) * ‖Q y x‖ * v y0
        ≤ (1 - ε / 2) * ‖D‖ * v y0 := by
      rw [← Finset.sum_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hrow y) (hv0 y0)
    linarith
  have h8 := key y0
  have h9 : ε / 2 * (‖D‖ * v y0) ≤ 1 := by nlinarith
  have h10 : ‖D‖ * v y0 ≤ 2 / ε := by
    rw [le_div_iff₀ hε]; nlinarith
  have h11 : v y0 ≤ 2 / ε ^ 2 := by
    have h12 : ε * v y0 ≤ ‖D‖ * v y0 := mul_le_mul_of_nonneg_right hεD (hv0 y0)
    have h13 : ε * v y0 ≤ 2 / ε := h12.trans h10
    rw [le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ hε] at h13
    nlinarith
  have h14 := (hy0 y).trans h11
  have hey : 0 < Real.exp (μ * (zdistD d L (y - a) : ℝ)) := Real.exp_pos _
  have h15 : ‖PropThetaQ Q t y a‖
      = Real.exp (-(μ * (zdistD d L (y - a) : ℝ))) * v y := by
    simp only [hv]
    rw [← mul_assoc, ← Real.exp_add]
    simp
  rw [h15, mul_comm (2 / ε ^ 2)]
  exact mul_le_mul_of_nonneg_left h14 (Real.exp_pos _).le
/-- Off the diagonal the entry bound `|Q_yx| ≤ B e^{-2c|y-x|}` (`μ ≤ c`) gives the factor `B`. -/
theorem BApropQ_offdiag (Q : Matrix (Zd d L) (Zd d L) ℂ) (q : ℂ) (t ε μ B c S : ℝ)
    (hQ : ∀ y, Q y y = q) (hε : 0 < ε) (hεD : ε ≤ ‖1 - (t : ℂ) * q‖) (hμ : 0 ≤ μ) (ht : 0 ≤ t)
    (ht1 : t ≤ 1)
    (hrow : ∀ y, t * ∑ x ∈ Finset.univ.erase y, Real.exp (μ * (zdistD d L (y - x) : ℝ)) * ‖Q y x‖
        ≤ (1 - ε / 2) * ‖1 - (t : ℂ) * q‖)
    (hB : 0 ≤ B) (hμc : μ ≤ c)
    (hQB : ∀ y x : Zd d L, x ≠ y → ‖Q y x‖ ≤ B * Real.exp (-(2 * c * (zdistD d L (y - x) : ℝ))))
    (hS : ∀ y : Zd d L, ∑ x : Zd d L, Real.exp (-(c * (zdistD d L (y - x) : ℝ))) ≤ S)
    (y a : Zd d L) (hya : y ≠ a) :
    ‖PropThetaQ Q t y a‖ ≤ 2 * B * S / ε ^ 3 * Real.exp (-(μ * (zdistD d L (y - a) : ℝ))) := by
  have hS0 : 0 ≤ S :=
    (Finset.sum_nonneg fun x _ => (Real.exp_pos _).le).trans (hS y)
  have hpos : 0 ≤ 2 * B * S / ε ^ 3 * Real.exp (-(μ * (zdistD d L (y - a) : ℝ))) := by positivity
  by_cases hU : IsUnit (1 - (t : ℂ) • Q)
  swap
  · have h0 : PropThetaQ Q t = 0 := Ring.inverse_non_unit _ hU
    rw [h0]
    simpa only [Matrix.zero_apply, norm_zero] using hpos
  set D : ℂ := 1 - (t : ℂ) * q with hD
  have hDpos : 0 < ‖D‖ := lt_of_lt_of_le hε hεD
  have hid := BP5_row_identity d L Q q t hQ hU y a
  simp only [hya, ↓reduceIte, zero_add] at hid
  have hn : ‖D‖ * ‖PropThetaQ Q t y a‖
      ≤ t * ∑ x ∈ Finset.univ.erase y, ‖Q y x‖ * ‖PropThetaQ Q t x a‖ := by
    calc ‖D‖ * ‖PropThetaQ Q t y a‖ = ‖D * PropThetaQ Q t y a‖ := (norm_mul _ _).symm
      _ = ‖(t : ℂ) * ∑ x ∈ Finset.univ.erase y, Q y x * PropThetaQ Q t x a‖ := by rw [hid]
      _ ≤ t * ∑ x ∈ Finset.univ.erase y, ‖Q y x‖ * ‖PropThetaQ Q t x a‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
          apply mul_le_mul_of_nonneg_left _ ht
          refine (norm_sum_le _ _).trans ?_
          exact Finset.sum_le_sum fun x _ => (norm_mul _ _).le
  set K : ℝ := B * (2 / ε ^ 2) * Real.exp (-(μ * (zdistD d L (y - a) : ℝ))) with hK
  have hK0 : 0 ≤ K := by positivity
  have hterm : ∀ x ∈ Finset.univ.erase y, ‖Q y x‖ * ‖PropThetaQ Q t x a‖
      ≤ K * Real.exp (-(c * (zdistD d L (y - x) : ℝ))) := by
    intro x hx
    have hxy : x ≠ y := Finset.ne_of_mem_erase hx
    have h1 := hQB y x hxy
    have h2 := BApropQ_decay d L Q q t ε μ hQ hε hεD hμ ht hrow x a
    have h3 : Real.exp (-(2 * c * (zdistD d L (y - x) : ℝ))) * Real.exp (-(μ * (zdistD d L (x - a) : ℝ)))
        ≤ Real.exp (-(μ * (zdistD d L (y - a) : ℝ))) * Real.exp (-(c * (zdistD d L (y - x) : ℝ))) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h4 := zdistD_add_le d L (y - x) (x - a)
      rw [show y - x + (x - a) = y - a by ring] at h4
      have h5 : (zdistD d L (y - a) : ℝ) ≤ (zdistD d L (y - x) : ℝ) + (zdistD d L (x - a) : ℝ) := by
        exact_mod_cast h4
      have h6 : 0 ≤ (zdistD d L (y - x) : ℝ) := Nat.cast_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left h5 hμ, mul_le_mul_of_nonneg_right hμc h6]
    calc ‖Q y x‖ * ‖PropThetaQ Q t x a‖
        ≤ (B * Real.exp (-(2 * c * (zdistD d L (y - x) : ℝ))))
            * (2 / ε ^ 2 * Real.exp (-(μ * (zdistD d L (x - a) : ℝ)))) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = B * (2 / ε ^ 2) * (Real.exp (-(2 * c * (zdistD d L (y - x) : ℝ)))
            * Real.exp (-(μ * (zdistD d L (x - a) : ℝ)))) := by ring
      _ ≤ B * (2 / ε ^ 2) * (Real.exp (-(μ * (zdistD d L (y - a) : ℝ)))
            * Real.exp (-(c * (zdistD d L (y - x) : ℝ)))) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = K * Real.exp (-(c * (zdistD d L (y - x) : ℝ))) := by rw [hK]; ring
  have hsum : ∑ x ∈ Finset.univ.erase y, ‖Q y x‖ * ‖PropThetaQ Q t x a‖ ≤ K * S := by
    calc ∑ x ∈ Finset.univ.erase y, ‖Q y x‖ * ‖PropThetaQ Q t x a‖
        ≤ ∑ x ∈ Finset.univ.erase y, K * Real.exp (-(c * (zdistD d L (y - x) : ℝ))) :=
          Finset.sum_le_sum hterm
      _ = K * ∑ x ∈ Finset.univ.erase y, Real.exp (-(c * (zdistD d L (y - x) : ℝ))) := by
          rw [Finset.mul_sum]
      _ ≤ K * ∑ x : Zd d L, Real.exp (-(c * (zdistD d L (y - x) : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hK0
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun x _ _ => (Real.exp_pos _).le
      _ ≤ K * S := mul_le_mul_of_nonneg_left (hS y) hK0
  have h7 : ‖D‖ * ‖PropThetaQ Q t y a‖ ≤ K * S := by
    refine hn.trans ?_
    have : 0 ≤ ∑ x ∈ Finset.univ.erase y, ‖Q y x‖ * ‖PropThetaQ Q t x a‖ :=
      Finset.sum_nonneg fun x _ => by positivity
    nlinarith
  have h8 : ε * ‖PropThetaQ Q t y a‖ ≤ K * S :=
    (mul_le_mul_of_nonneg_right hεD (norm_nonneg _)).trans h7
  have h9 : ‖PropThetaQ Q t y a‖ ≤ K * S / ε := by
    rw [le_div_iff₀ hε]; linarith
  refine h9.trans (le_of_eq ?_)
  rw [hK]
  field_simp

end Weighted

/-! ## 5. The weighted row sum for `Q = M^{(σ,σ)}` and the pin -/

section Final

variable (d L : ℕ) [NeZero L]

/-- Convexity of `exp`: `e^{μr} - 1 ≤ (μ/c) e^{cr}` for `0 ≤ μ ≤ c`, `r ≥ 0`. -/
private theorem BP5_exp_sub_one_le (μ c r : ℝ) (hμ : 0 ≤ μ) (hμc : μ ≤ c) (hc : 0 < c) (hr : 0 ≤ r) :
    Real.exp (μ * r) - 1 ≤ μ / c * Real.exp (c * r) := by
  have hs0 : 0 ≤ μ / c := by positivity
  have hs1 : μ / c ≤ 1 := (div_le_one hc).mpr hμc
  have h := convexOn_exp.2 (Set.mem_univ (c * r)) (Set.mem_univ (0 : ℝ)) hs0 (sub_nonneg.mpr hs1)
    (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at h
  have h2 : μ / c * (c * r) = μ * r := by field_simp
  rw [h2] at h
  nlinarith

/-- The row hypothesis of `BApropQ_decay` for `Q = M^{(σ,σ)}` at a real-axis datum,
`μ = BAp5s_rate d Λ κ`, `ε = κ²/4`, every `t ∈ [0, 1]`. -/
theorem BAp5s_row_weighted (hL : 3 ≤ L) (hd : 2 ≤ d) (Λ g κ E : ℝ) (m : ℂ) (hΛ : 0 < Λ) (hg : 0 < g)
    (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (σ : Bool) (y : Zd d L) :
    t * ∑ x ∈ Finset.univ.erase y,
        Real.exp (BAp5s_rate d Λ κ * (zdistD d L (y - x) : ℝ))
          * ‖BAMss d L (BAMB d L g (E : ℂ) m) σ σ y x‖
      ≤ (1 - κ ^ 2 / 4 / 2) * ‖1 - (t : ℂ) * (if σ then m else star m) ^ 2‖ := by
  have hd0 : 0 < d := by omega
  have hc₀ : 0 < BAct_rate d Λ κ := BAct_rate_pos d Λ κ hd0 hΛ hκ
  have hA : 0 < BAp5s_A d Λ κ := BP5_A_pos d Λ κ hd0 hΛ hκ
  have hS : 0 < BAp5s_S d Λ κ := BP5_S_pos d Λ κ hd0 hΛ hκ
  have hμ0 : 0 < BAp5s_rate d Λ κ := BAp5s_rate_pos d Λ κ hd0 hΛ hκ
  have hμc : BAp5s_rate d Λ κ ≤ BAct_rate d Λ κ := min_le_left _ _
  have hμε : BAp5s_rate d Λ κ
      ≤ (κ ^ 2 / 4) ^ 2 * BAct_rate d Λ κ / (2 * BAp5s_A d Λ κ * Λ ^ 2 * BAp5s_S d Λ κ) :=
    min_le_right _ _
  have hn := BAm_norm_le_one d L g (E : ℂ) m (by simp) hr.1
  obtain ⟨hD1, hD2⟩ := BAoffDiag_scalar κ t m hκ hr.2 hn ht0 ht1
  rw [BAnorm_one_sub_tq_sigma]
  have hε : 0 < κ ^ 2 / 4 := by positivity
  -- the weighted part
  have hterm : ∀ x ∈ Finset.univ.erase y,
      (Real.exp (BAp5s_rate d Λ κ * (zdistD d L (y - x) : ℝ)) - 1)
          * ‖BAMss d L (BAMB d L g (E : ℂ) m) σ σ y x‖
        ≤ BAp5s_rate d Λ κ / BAct_rate d Λ κ * (BAp5s_A d Λ κ * g ^ 2)
          * Real.exp (-(BAct_rate d Λ κ * (zdistD d L (y - x) : ℝ))) := by
    intro x hx
    have hxy : x ≠ y := Finset.ne_of_mem_erase hx
    rw [BAMss_ss_norm]
    have h1 := BAMB_sq_off_le d L hL hd0 Λ g κ E m hΛ hg hgΛ hκ hr y x (Ne.symm hxy)
    have h2 := BP5_exp_sub_one_le (BAp5s_rate d Λ κ) (BAct_rate d Λ κ) (zdistD d L (y - x) : ℝ)
      hμ0.le hμc hc₀ (Nat.cast_nonneg _)
    have h3 : 0 ≤ BAp5s_rate d Λ κ / BAct_rate d Λ κ := by positivity
    have h4 : Real.exp (BAct_rate d Λ κ * (zdistD d L (y - x) : ℝ))
        * Real.exp (-(2 * BAct_rate d Λ κ * (zdistD d L (y - x) : ℝ)))
        = Real.exp (-(BAct_rate d Λ κ * (zdistD d L (y - x) : ℝ))) := by
      rw [← Real.exp_add]; congr 1; ring
    calc (Real.exp (BAp5s_rate d Λ κ * (zdistD d L (y - x) : ℝ)) - 1) * ‖BAMB d L g (E : ℂ) m y x‖ ^ 2
        ≤ (BAp5s_rate d Λ κ / BAct_rate d Λ κ * Real.exp (BAct_rate d Λ κ * (zdistD d L (y - x) : ℝ)))
            * (BAp5s_A d Λ κ * g ^ 2 * Real.exp (-(2 * BAct_rate d Λ κ * (zdistD d L (y - x) : ℝ)))) :=
          mul_le_mul h2 h1 (by positivity) (by positivity)
      _ = BAp5s_rate d Λ κ / BAct_rate d Λ κ * (BAp5s_A d Λ κ * g ^ 2)
            * (Real.exp (BAct_rate d Λ κ * (zdistD d L (y - x) : ℝ))
              * Real.exp (-(2 * BAct_rate d Λ κ * (zdistD d L (y - x) : ℝ)))) := by ring
      _ = _ := by rw [h4]
  have hsec : ∑ x ∈ Finset.univ.erase y,
      (Real.exp (BAp5s_rate d Λ κ * (zdistD d L (y - x) : ℝ)) - 1)
        * ‖BAMss d L (BAMB d L g (E : ℂ) m) σ σ y x‖ ≤ (κ ^ 2 / 4) ^ 2 / 2 := by
    have h1 : ∑ x ∈ Finset.univ.erase y,
        (Real.exp (BAp5s_rate d Λ κ * (zdistD d L (y - x) : ℝ)) - 1)
          * ‖BAMss d L (BAMB d L g (E : ℂ) m) σ σ y x‖
        ≤ BAp5s_rate d Λ κ / BAct_rate d Λ κ * (BAp5s_A d Λ κ * g ^ 2)
          * BAp5s_S d Λ κ := by
      calc _ ≤ ∑ x ∈ Finset.univ.erase y, BAp5s_rate d Λ κ / BAct_rate d Λ κ * (BAp5s_A d Λ κ * g ^ 2)
            * Real.exp (-(BAct_rate d Λ κ * (zdistD d L (y - x) : ℝ))) := Finset.sum_le_sum hterm
        _ = BAp5s_rate d Λ κ / BAct_rate d Λ κ * (BAp5s_A d Λ κ * g ^ 2)
            * ∑ x ∈ Finset.univ.erase y, Real.exp (-(BAct_rate d Λ κ * (zdistD d L (y - x) : ℝ))) := by
            rw [Finset.mul_sum]
        _ ≤ BAp5s_rate d Λ κ / BAct_rate d Λ κ * (BAp5s_A d Λ κ * g ^ 2)
            * ∑ x : Zd d L, Real.exp (-(BAct_rate d Λ κ * (zdistD d L (y - x) : ℝ))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              fun x _ _ => (Real.exp_pos _).le
        _ ≤ BAp5s_rate d Λ κ / BAct_rate d Λ κ * (BAp5s_A d Λ κ * g ^ 2) * BAp5s_S d Λ κ :=
            mul_le_mul_of_nonneg_left (BAsum_exp_decay_le d L hd _ hc₀ y) (by positivity)
    refine h1.trans ?_
    have h2 : BAp5s_rate d Λ κ / BAct_rate d Λ κ * (BAp5s_A d Λ κ * g ^ 2) * BAp5s_S d Λ κ
        ≤ BAp5s_rate d Λ κ / BAct_rate d Λ κ * (BAp5s_A d Λ κ * Λ ^ 2) * BAp5s_S d Λ κ := by
      have : g ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hg.le hgΛ 2
      have h5 : 0 ≤ BAp5s_rate d Λ κ / BAct_rate d Λ κ := by positivity
      have h6 : BAp5s_A d Λ κ * g ^ 2 ≤ BAp5s_A d Λ κ * Λ ^ 2 := mul_le_mul_of_nonneg_left this hA.le
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h6 h5) hS.le
    refine h2.trans ?_
    have h7 := (le_div_iff₀ (by positivity : 0 < 2 * BAp5s_A d Λ κ * Λ ^ 2 * BAp5s_S d Λ κ)).mp hμε
    have h8 : BAp5s_rate d Λ κ / BAct_rate d Λ κ * (BAp5s_A d Λ κ * Λ ^ 2) * BAp5s_S d Λ κ
        = BAp5s_rate d Λ κ * (BAp5s_A d Λ κ * Λ ^ 2 * BAp5s_S d Λ κ) / BAct_rate d Λ κ := by
      field_simp
    rw [h8, div_le_iff₀ hc₀]
    nlinarith
  have hsec0 : 0 ≤ ∑ x ∈ Finset.univ.erase y,
      (Real.exp (BAp5s_rate d Λ κ * (zdistD d L (y - x) : ℝ)) - 1)
        * ‖BAMss d L (BAMB d L g (E : ℂ) m) σ σ y x‖ :=
    Finset.sum_nonneg fun x _ =>
      mul_nonneg (sub_nonneg.mpr (Real.one_le_exp (by positivity))) (norm_nonneg _)
  have hsplit : ∑ x ∈ Finset.univ.erase y,
        Real.exp (BAp5s_rate d Λ κ * (zdistD d L (y - x) : ℝ))
          * ‖BAMss d L (BAMB d L g (E : ℂ) m) σ σ y x‖
      = ∑ x ∈ Finset.univ.erase y, ‖BAMss d L (BAMB d L g (E : ℂ) m) σ σ y x‖
        + ∑ x ∈ Finset.univ.erase y,
          (Real.exp (BAp5s_rate d Λ κ * (zdistD d L (y - x) : ℝ)) - 1)
            * ‖BAMss d L (BAMB d L g (E : ℂ) m) σ σ y x‖ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hsplit, BAMss_row_offdiag_sum d L g E m hr.1 σ y]
  have h1m : 0 ≤ 1 - ‖m‖ ^ 2 := by nlinarith [norm_nonneg m]
  have h2 : t * (1 - ‖m‖ ^ 2) ≤ 1 - ‖m‖ ^ 2 := mul_le_of_le_one_left h1m ht1
  have h3 : t * ∑ x ∈ Finset.univ.erase y,
      (Real.exp (BAp5s_rate d Λ κ * (zdistD d L (y - x) : ℝ)) - 1)
        * ‖BAMss d L (BAMB d L g (E : ℂ) m) σ σ y x‖ ≤ (κ ^ 2 / 4) ^ 2 / 2 :=
    (mul_le_of_le_one_left hsec0 ht1).trans hsec
  have h4 : (κ ^ 2 / 4) ^ 2 / 2 ≤ κ ^ 2 / 4 / 2 * ‖1 - (t : ℂ) * m ^ 2‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hD1 hε.le]
  rw [mul_add]
  nlinarith


/-- The body of `BAProp5s` at one datum with `C := BAp5s_C d Λ κ`, `c := BAp5s_rate d Λ κ`, for every
`t ∈ [0, 1]` (the pin asks `t < 1`). -/
theorem baProp5s_of_real (hL : 3 ≤ L) (hd : 2 ≤ d) (Λ g κ E : ℝ) (m : ℂ) (hΛ : 0 < Λ) (hg : 0 < g)
    (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (σ : Bool) (a : Zd d L) :
    ‖BATheta d L g E m t σ σ 0 a‖
      ≤ BAp5s_C d Λ κ * ((if a = 0 then (1 : ℝ) else 0)
          + g ^ 2 * Real.exp (-BAp5s_rate d Λ κ * (zdistD d L a : ℝ))) := by
  have hd0 : 0 < d := by omega
  have hc₀ : 0 < BAct_rate d Λ κ := BAct_rate_pos d Λ κ hd0 hΛ hκ
  have hA : 0 < BAp5s_A d Λ κ := BP5_A_pos d Λ κ hd0 hΛ hκ
  have hS : 0 < BAp5s_S d Λ κ := BP5_S_pos d Λ κ hd0 hΛ hκ
  have hμ0 : 0 < BAp5s_rate d Λ κ := BAp5s_rate_pos d Λ κ hd0 hΛ hκ
  have hn := BAm_norm_le_one d L g (E : ℂ) m (by simp) hr.1
  obtain ⟨hD1, _⟩ := BAoffDiag_scalar κ t m hκ hr.2 hn ht0 ht1
  have hε : 0 < κ ^ 2 / 4 := by positivity
  have hεD : κ ^ 2 / 4 ≤ ‖1 - (t : ℂ) * (if σ then m else star m) ^ 2‖ := by
    rw [BAnorm_one_sub_tq_sigma]; exact hD1
  have hQ : ∀ y, BAMss d L (BAMB d L g (E : ℂ) m) σ σ y y = (if σ then m else star m) ^ 2 :=
    fun y => BAMss_ss_diag d L g (E : ℂ) m hr.1 σ y
  have hrow := BAp5s_row_weighted d L hL hd Λ g κ E m hΛ hg hgΛ hκ hr t ht0 ht1 σ
  have hC : 0 < BAp5s_C d Λ κ := BAp5s_C_pos d Λ κ hd0 hΛ hκ
  have hCge : 2 / (κ ^ 2 / 4) ^ 2 ≤ BAp5s_C d Λ κ := by
    unfold BAp5s_C
    have : 0 ≤ 2 * BAp5s_A d Λ κ * BAp5s_S d Λ κ / (κ ^ 2 / 4) ^ 3 := by positivity
    linarith
  change ‖PropThetaQ (BAMss d L (BAMB d L g (E : ℂ) m) σ σ) t 0 a‖ ≤ _
  by_cases ha : a = 0
  · subst ha
    have h := BApropQ_decay d L _ _ t (κ ^ 2 / 4) (BAp5s_rate d Λ κ) hQ hε hεD hμ0.le ht0 hrow 0 0
    simp only [sub_self, zdistD_zero, Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at h
    simp only [ite_true]
    have h2 : 0 ≤ g ^ 2 * Real.exp (-BAp5s_rate d Λ κ * (zdistD d L (0 : Zd d L) : ℝ)) := by positivity
    calc _ ≤ 2 / (κ ^ 2 / 4) ^ 2 := h
      _ ≤ BAp5s_C d Λ κ := hCge
      _ ≤ _ := by nlinarith
  · have h := BApropQ_offdiag d L _ _ t (κ ^ 2 / 4) (BAp5s_rate d Λ κ) (BAp5s_A d Λ κ * g ^ 2)
      (BAct_rate d Λ κ) (BAp5s_S d Λ κ) hQ hε hεD hμ0.le ht0 ht1 hrow (by positivity)
      (min_le_left _ _)
      (fun y x hxy => by
        rw [BAMss_ss_norm]
        exact BAMB_sq_off_le d L hL hd0 Λ g κ E m hΛ hg hgΛ hκ hr y x (Ne.symm hxy))
      (fun y => BAsum_exp_decay_le d L hd _ hc₀ y) 0 a (Ne.symm ha)
    rw [zero_sub, zdistD_neg] at h
    simp only [ha, ite_false, zero_add]
    have h2 : 2 * (BAp5s_A d Λ κ * g ^ 2) * BAp5s_S d Λ κ / (κ ^ 2 / 4) ^ 3
          * Real.exp (-(BAp5s_rate d Λ κ * (zdistD d L a : ℝ)))
        = (2 * BAp5s_A d Λ κ * BAp5s_S d Λ κ / (κ ^ 2 / 4) ^ 3)
          * (g ^ 2 * Real.exp (-BAp5s_rate d Λ κ * (zdistD d L a : ℝ))) := by
      rw [neg_mul]; ring
    rw [h2] at h
    refine h.trans ?_
    have h3 : 2 * BAp5s_A d Λ κ * BAp5s_S d Λ κ / (κ ^ 2 / 4) ^ 3 ≤ BAp5s_C d Λ κ := by
      unfold BAp5s_C
      have : 0 ≤ 2 / (κ ^ 2 / 4) ^ 2 := by positivity
      linarith
    exact mul_le_mul_of_nonneg_right h3 (by positivity)

end Final

/-- **`BAProp5s` is proved** (`prop:ThfadC_short`, `1_2:1148`): `3 ≤ d` is used only as `2 ≤ d`, `t < 1` only as `t ≤ 1`. -/
theorem baProp5s_holds (d : ℕ) (Λ κ : ℝ) : BAProp5s d Λ κ := by
  intro hd hΛ hκ
  have hd0 : 0 < d := by omega
  refine ⟨BAp5s_C d Λ κ, BAp5s_C_pos d Λ κ hd0 hΛ hκ, BAp5s_rate d Λ κ,
    BAp5s_rate_pos d Λ κ hd0 hΛ hκ, ?_⟩
  intro L hL g hg hgΛ E m hr t ht0 ht1 σ a
  have : NeZero L := ⟨by omega⟩
  exact baProp5s_of_real d L hL (by omega) Λ g κ E m hΛ hg hgΛ hκ hr t ht0 ht1.le σ a


/-! ## 6. Compiled nonempty instances (`d = 3`, `L = 4`, `Λ = 10`)

`P : FlowPt 4 10` is the merged real-axis flow point (`MFixedPoint.lean`): `P.g0 ∈ (0, 10]`, a real energy
`P.E`, `P.m0` solving `(self_m)` with `κ = Im m₀ > 0` (`P.real : BAReal 3 4 P.g0 (Im m₀) P.E P.m0`);
`card (Zd 3 4) = 64`.  Every deterministic hypothesis is discharged; nothing is left open. -/

namespace Prop5sInst

open RBM RBM.Gauss RBM.BA RBM.BA.MFixedPointInst

/-- T6 at `(d, L, c, y) = (3, 4, 1/2, 0)`. -/
theorem inst_sum_exp_decay :
    ∑ x : Zd 3 4, Real.exp (-((1 / 2 : ℝ) * (zdistD 3 4 (0 - x) : ℝ))) ≤ RBM.expC (3 - 2) (1 / 2) :=
  BAsum_exp_decay_le 3 4 (by norm_num) (1 / 2) (by norm_num) 0

/-- T2 at `P`, `σ = -`, the entry `(0, (1,0,0))`. -/
theorem inst_ss_norm :
    ‖BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) false false 0 ![1, 0, 0]‖
      = ‖BAMB 3 4 P.g0 (P.E : ℂ) P.m0 0 ![1, 0, 0]‖ ^ 2 :=
  BAMss_ss_norm 3 4 P.g0 (P.E : ℂ) P.m0 false 0 ![1, 0, 0]

/-- T3 at `P`, `σ = -`. -/
theorem inst_ss_diag :
    BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) false false 0 0 = (if false then P.m0 else star P.m0) ^ 2 :=
  BAMss_ss_diag 3 4 P.g0 (P.E : ℂ) P.m0 P.real.1 false 0

/-- T3 (norm), `t = 1/2`, `σ = -`. -/
theorem inst_norm_sigma :
    ‖1 - (((1 / 2 : ℝ)) : ℂ) * (if false then P.m0 else star P.m0) ^ 2‖
      = ‖1 - (((1 / 2 : ℝ)) : ℂ) * P.m0 ^ 2‖ :=
  BAnorm_one_sub_tq_sigma (1 / 2) P.m0 false

/-- T4 at `P`, `σ = +`, row `0`. -/
theorem inst_row_offdiag_sum :
    ∑ x ∈ Finset.univ.erase (0 : Zd 3 4), ‖BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) true true 0 x‖
      = 1 - ‖P.m0‖ ^ 2 :=
  BAMss_row_offdiag_sum 3 4 P.g0 P.E P.m0 P.real.1 true 0

/-- T5 at `P`, the pair `(0, (1,0,0))` (both lie in `Z_4^3`, `|(1,0,0)| = 1`). -/
theorem inst_sq_off_le :
    ‖BAMB 3 4 P.g0 (P.E : ℂ) P.m0 0 ![1, 0, 0]‖ ^ 2
      ≤ BAp5s_A 3 10 P.m0.im * P.g0 ^ 2
        * Real.exp (-(2 * BAct_rate 3 10 P.m0.im * (zdistD 3 4 ((0 : Zd 3 4) - ![1, 0, 0]) : ℝ))) :=
  BAMB_sq_off_le 3 4 (by norm_num) (by norm_num) 10 P.g0 P.m0.im P.E P.m0 (by norm_num) P.g0_pos
    P.g0_le P.real.1.1 P.real 0 ![1, 0, 0] (by decide)

/-- T9 at `P`, `t = 1/2`, `σ = -`, row `0`. -/
theorem inst_row_weighted :
    (1 / 2 : ℝ) * ∑ x ∈ Finset.univ.erase (0 : Zd 3 4),
        Real.exp (BAp5s_rate 3 10 P.m0.im * (zdistD 3 4 (0 - x) : ℝ))
          * ‖BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) false false 0 x‖
      ≤ (1 - P.m0.im ^ 2 / 4 / 2) * ‖1 - (((1 / 2 : ℝ)) : ℂ) * (if false then P.m0 else star P.m0) ^ 2‖ :=
  BAp5s_row_weighted 3 4 (by norm_num) (by norm_num) 10 P.g0 P.m0.im P.E P.m0 (by norm_num) P.g0_pos
    P.g0_le P.real.1.1 P.real (1 / 2) (by norm_num) (by norm_num) false 0

private theorem BP5_hyp_row (σ : Bool) :
    ∀ y : Zd 3 4, (1 / 2 : ℝ) * ∑ x ∈ Finset.univ.erase y,
        Real.exp (BAp5s_rate 3 10 P.m0.im * (zdistD 3 4 (y - x) : ℝ))
          * ‖BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) σ σ y x‖
      ≤ (1 - P.m0.im ^ 2 / 4 / 2) * ‖1 - (((1 / 2 : ℝ)) : ℂ) * (if σ then P.m0 else star P.m0) ^ 2‖ :=
  fun y => BAp5s_row_weighted 3 4 (by norm_num) (by norm_num) 10 P.g0 P.m0.im P.E P.m0 (by norm_num)
    P.g0_pos P.g0_le P.real.1.1 P.real (1 / 2) (by norm_num) (by norm_num) σ y

private theorem BP5_gap (σ : Bool) :
    P.m0.im ^ 2 / 4 ≤ ‖1 - (((1 / 2 : ℝ)) : ℂ) * (if σ then P.m0 else star P.m0) ^ 2‖ := by
  have hn := BAm_norm_le_one 3 4 P.g0 (P.E : ℂ) P.m0 (by simp) P.real.1
  obtain ⟨hD1, _⟩ := BAoffDiag_scalar P.m0.im (1 / 2) P.m0 P.real.1.1 P.real.2 hn (by norm_num)
    (by norm_num)
  rw [BAnorm_one_sub_tq_sigma]
  exact hD1

/-- T7 at `Q = M^{(+,+)}` of `P`, `q = m₀²`, `t = 1/2`, `ε = (Im m₀)²/4`, `μ = BAp5s_rate 3 10 (Im m₀)`;
the hypotheses come from T3, T9 and `BAoffDiag_scalar`. -/
theorem inst_BApropQ_decay (y a : Zd 3 4) :
    ‖PropThetaQ (BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) true true) (1 / 2) y a‖
      ≤ 2 / (P.m0.im ^ 2 / 4) ^ 2
        * Real.exp (-(BAp5s_rate 3 10 P.m0.im * (zdistD 3 4 (y - a) : ℝ))) := by
  have hκ := P.real.1.1
  refine BApropQ_decay 3 4 _ (P.m0 ^ 2) (1 / 2) (P.m0.im ^ 2 / 4) (BAp5s_rate 3 10 P.m0.im)
    (fun y => ?_) (by positivity) (by simpa using BP5_gap true)
    (BAp5s_rate_pos 3 10 _ (by norm_num) (by norm_num) hκ).le (by norm_num)
    (by simpa using BP5_hyp_row true) y a
  simpa using BAMss_ss_diag 3 4 P.g0 (P.E : ℂ) P.m0 P.real.1 true y

/-- T8 at `Q = M^{(-,-)}` of `P`, `t = 1/2`, off the diagonal (`0 ≠ (1,0,0)`), `B = A g²`,
`c = BAct_rate`, `S = BAp5s_S`. -/
theorem inst_BApropQ_offdiag :
    ‖PropThetaQ (BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) false false) (1 / 2) 0 ![1, 0, 0]‖
      ≤ 2 * (BAp5s_A 3 10 P.m0.im * P.g0 ^ 2) * BAp5s_S 3 10 P.m0.im / (P.m0.im ^ 2 / 4) ^ 3
        * Real.exp (-(BAp5s_rate 3 10 P.m0.im * (zdistD 3 4 ((0 : Zd 3 4) - ![1, 0, 0]) : ℝ))) := by
  have hκ := P.real.1.1
  have hA := BP5_A_pos 3 10 P.m0.im (by norm_num) (by norm_num) hκ
  refine BApropQ_offdiag 3 4 _ ((star P.m0) ^ 2) (1 / 2) (P.m0.im ^ 2 / 4) (BAp5s_rate 3 10 P.m0.im)
    (BAp5s_A 3 10 P.m0.im * P.g0 ^ 2) (BAct_rate 3 10 P.m0.im) (BAp5s_S 3 10 P.m0.im)
    (fun y => ?_) (by positivity) (by simpa using BP5_gap false)
    (BAp5s_rate_pos 3 10 _ (by norm_num) (by norm_num) hκ).le (by norm_num) (by norm_num)
    (by simpa using BP5_hyp_row false) (by have := P.g0_pos; positivity) (min_le_left _ _)
    (fun y x hxy => ?_) (fun y => BAsum_exp_decay_le 3 4 (by norm_num) _
      (BAct_rate_pos 3 10 _ (by norm_num) (by norm_num) hκ) y) 0 ![1, 0, 0] (by decide)
  · simpa using BAMss_ss_diag 3 4 P.g0 (P.E : ℂ) P.m0 P.real.1 false y
  · rw [BAMss_ss_norm]
    exact BAMB_sq_off_le 3 4 (by norm_num) (by norm_num) 10 P.g0 P.m0.im P.E P.m0 (by norm_num)
      P.g0_pos P.g0_le hκ P.real y x (Ne.symm hxy)

/-- `baProp5s_of_real` at `P`, `t = 1/2`, `σ = +`, `a = (1,0,0)` (`|a| = 1`, `a ≠ 0`). -/
theorem inst_of_real_half :
    ‖BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true true 0 ![1, 0, 0]‖
      ≤ BAp5s_C 3 10 P.m0.im * ((if (![1, 0, 0] : Zd 3 4) = 0 then (1 : ℝ) else 0)
          + P.g0 ^ 2 * Real.exp (-BAp5s_rate 3 10 P.m0.im * (zdistD 3 4 (![1, 0, 0] : Zd 3 4) : ℝ))) :=
  baProp5s_of_real 3 4 (by norm_num) (by norm_num) 10 P.g0 P.m0.im P.E P.m0 (by norm_num) P.g0_pos
    P.g0_le P.real.1.1 P.real (1 / 2) (by norm_num) (by norm_num) true ![1, 0, 0]

/-- `baProp5s_of_real` at `P`, the endpoint `t = 1`, `σ = -`, `a = 0`. -/
theorem inst_of_real_one :
    ‖BATheta 3 4 P.g0 P.E P.m0 1 false false 0 0‖
      ≤ BAp5s_C 3 10 P.m0.im * ((if (0 : Zd 3 4) = 0 then (1 : ℝ) else 0)
          + P.g0 ^ 2 * Real.exp (-BAp5s_rate 3 10 P.m0.im * (zdistD 3 4 (0 : Zd 3 4) : ℝ))) :=
  baProp5s_of_real 3 4 (by norm_num) (by norm_num) 10 P.g0 P.m0.im P.E P.m0 (by norm_num) P.g0_pos
    P.g0_le P.real.1.1 P.real 1 (by norm_num) (by norm_num) false 0

/-- The merged instance `inst_BAProp5s` (`FlowPins.lean`) closed by `baProp5s_holds`: no hypothesis left. -/
theorem inst_BAProp5s_closed : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ‖BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true true 0 ![1, 0, 0]‖ ≤
      C * ((if (![1, 0, 0] : Zd 3 4) = 0 then (1 : ℝ) else 0) +
        P.g0 ^ 2 * Real.exp (-c * (zdistD 3 4 (![1, 0, 0] : Zd 3 4) : ℝ))) :=
  RBM.BA.FlowPinsInst.inst_BAProp5s (baProp5s_holds 3 10 P.m0.im)

/-- The constants at `(d, Λ, κ) = (3, 10, 1/2)`. -/
theorem inst_C_pos : 0 < BAp5s_C 3 10 (1 / 2) := BAp5s_C_pos 3 10 (1 / 2) (by norm_num) (by norm_num) (by norm_num)

theorem inst_rate_pos : 0 < BAp5s_rate 3 10 (1 / 2) :=
  BAp5s_rate_pos 3 10 (1 / 2) (by norm_num) (by norm_num) (by norm_num)

end Prop5sInst

end RBM.BA

end
