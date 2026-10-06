/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/

import RBM3D.BA.Ward
import RBM3D.BA.CouplingWindow
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Complex.Norm

/-!
# BA-D7 (T2291): the lower bound on `Im m(E + iη)`, `η ∈ (0, 1]`, in the bulk

Proves the merged pin `RBM.BA.BAImmLower` (`RBM3D/BA/MFixedPoint.lean`, "Owed: BA-D7")
unconditionally, for every `d`, `Λ`, `κ`, with `c = κ⁵/64`.
Paper: `paper/tex/7_8_light_weight.tex:1908` (`lem:propM`: "The bound `Im m ≳ 1` is a consequence
of [LeeSchSteYau2015, Lemma 3.5]"), `7_8:1864-1869` (`(eq:WardM)`), `1_2:624` (`ρ_N`).
The route is algebraic (finite sums over `Zd d L`, no spectral bound, no dimension): with
`v_i = BAspec d L g i`, `a_i = (v_i - (z + m))⁻¹`, `⟨f⟩ = N⁻¹ Σ_i f_i`, `N = L^d`:

* (M0) `Im a_i = Im (z + m) |a_i|²`, so `Im m = (Im z + Im m) ⟨|a|²⟩` (the averaged Ward identity
  in spectral form) and `⟨|a|²⟩ ≤ 1`.
* (M1) two solutions `(z, m)`, `(z', m')`: `a_i - b_i = a_i b_i ((z + m) - (z' + m'))`, so
  `(m - m')(1 - T) = (z - z') T`, `T = ⟨a b⟩`.
* (M2) `‖T‖ ≤ 1` (AM-GM) and `Re (1 - T) ≥ (Im m² + Im m'²)/2` (`⟨Re a²⟩ ≤ 1 - Im m²` by
  Jensen): target 1 `BASelf_sub_le`.
* (M3) target 2 `BAm_im_ge_half` (`0 < η ≤ κ³/4`), (M4) target 3 `BAm_im_ge_mul`
  (`η κ²/(η + 3)²`, every `η > 0`), (M5) target 4 `BAm_im_lower` (`c = κ⁵/64`), target 5
  `baImmLower_holds` (the pin), target 6 `BAm_im_lower_of_bulk` (the `ρ`-form).

Premises of the pin that the proof does not use (kept in the pin, not in the theorems):
`3 ≤ d`, `0 < Λ`, `0 < g`, `g ≤ Λ`; `3 ≤ L` only through `NeZero L`.
Answers supervisor 1102 O9 (b) (DECISIONS §95 (4)): the lower bound `Im m ≥ c` off the real axis
from `ρ_N ≥ κ`.  Consumers: BA-G1, BA-C2 (`BA/MReg`: target 1 is the modulus of `m` off the real
axis), BA-C3 (target 6), the T2161 glue skeletons (`baImmLower_holds`).  Nothing is registered.
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false

noncomputable section

namespace RBM.BA

open RBM RBM.Gauss

/-! ## 1. Generic finite-average lemmas (no lattice) -/

section Generic

variable {ι : Type*} [Fintype ι]

/-- `Im (v - w)⁻¹ = Im w · |(v - w)⁻¹|²` for `Im w > 0` and real `v`. -/
private theorem ImmLower_inv_im (v : ℝ) (w : ℂ) (hw : 0 < w.im) :
    (((v : ℂ) - w)⁻¹).im = w.im * ‖((v : ℂ) - w)⁻¹‖ ^ 2 := by
  have h1 : ((v : ℂ) - w).im = -w.im := by simp
  rw [Complex.inv_im, Complex.sq_norm, Complex.normSq_inv, h1]
  simp [div_eq_mul_inv]

private theorem ImmLower_inv_ne (v : ℝ) (w : ℂ) (hw : 0 < w.im) : ((v : ℂ) - w) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

/-- `Im w ≤ |v - w|` for `Im w > 0` and real `v`. -/
private theorem ImmLower_norm_ge (v : ℝ) (w : ℂ) (hw : 0 < w.im) : w.im ≤ ‖(v : ℂ) - w‖ := by
  have h1 : |((v : ℂ) - w).im| ≤ ‖(v : ℂ) - w‖ := Complex.abs_im_le_norm _
  have h2 : ((v : ℂ) - w).im = -w.im := by simp
  rw [h2, abs_neg, abs_of_pos hw] at h1
  exact h1

private theorem ImmLower_inv_norm_le (v : ℝ) (w : ℂ) (hw : 0 < w.im) : ‖((v : ℂ) - w)⁻¹‖ ≤ w.im⁻¹ := by
  rw [norm_inv]
  exact inv_anti₀ hw (ImmLower_norm_ge v w hw)

/-- Jensen and the Ward bound: `⟨Re a²⟩ ≤ 1 - Im m²` when `Im m = ⟨Im a⟩` and `⟨|a|²⟩ ≤ 1`. -/
private theorem ImmLower_re_sq_avg (N : ℝ) (hN : (Fintype.card ι : ℝ) = N) (hNpos : 0 < N) (a : ι → ℂ) (m : ℂ)
    (hma : m.im = N⁻¹ * ∑ i, (a i).im) (hA : N⁻¹ * ∑ i, ‖a i‖ ^ 2 ≤ 1) :
    N⁻¹ * ∑ i, (a i).re ^ 2 ≤ 1 - m.im ^ 2 := by
  have hjen : (∑ i, (a i).im) ^ 2 ≤ N * ∑ i, (a i).im ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun i => (a i).im)
    simpa [Finset.card_univ, hN] using this
  have hre : ∑ i, (a i).re ^ 2 = ∑ i, ‖a i‖ ^ 2 - ∑ i, (a i).im ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hS : ∑ i, (a i).im = m.im * N := by
    rw [hma]; field_simp
  rw [hS] at hjen
  have h1 : m.im ^ 2 * N ≤ ∑ i, (a i).im ^ 2 := by
    refine le_of_mul_le_mul_left ?_ hNpos
    nlinarith [hjen]
  have him2 : m.im ^ 2 ≤ N⁻¹ * ∑ i, (a i).im ^ 2 := by
    rw [← div_eq_inv_mul, le_div_iff₀ hNpos]; exact h1
  rw [hre, mul_sub]
  linarith

/-- (M2) The two-point bounds: `‖T‖ ≤ 1` and `Re (1 - T) ≥ (Im m² + Im m'²)/2`, `T = ⟨a b⟩`. -/
private theorem ImmLower_two_point (N : ℝ) (hN : (Fintype.card ι : ℝ) = N) (hNpos : 0 < N) (a b : ι → ℂ) (m m' : ℂ)
    (ha : ∀ i, 0 < (a i).im) (hb : ∀ i, 0 < (b i).im)
    (hma : m.im = N⁻¹ * ∑ i, (a i).im) (hmb : m'.im = N⁻¹ * ∑ i, (b i).im)
    (hA : N⁻¹ * ∑ i, ‖a i‖ ^ 2 ≤ 1) (hB : N⁻¹ * ∑ i, ‖b i‖ ^ 2 ≤ 1) :
    ‖((N⁻¹ : ℝ) : ℂ) * ∑ i, a i * b i‖ ≤ 1 ∧
      (m.im ^ 2 + m'.im ^ 2) / 2 ≤ (1 - ((N⁻¹ : ℝ) : ℂ) * ∑ i, a i * b i).re := by
  have hNinv : 0 ≤ N⁻¹ := inv_nonneg.mpr hNpos.le
  constructor
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hNinv]
    have h1 : ‖∑ i, a i * b i‖ ≤ ∑ i, (‖a i‖ ^ 2 + ‖b i‖ ^ 2) / 2 := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul]
      nlinarith [sq_nonneg (‖a i‖ - ‖b i‖)]
    have h2 : ∑ i, (‖a i‖ ^ 2 + ‖b i‖ ^ 2) / 2 = (∑ i, ‖a i‖ ^ 2 + ∑ i, ‖b i‖ ^ 2) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
    have h3 := mul_le_mul_of_nonneg_left h1 hNinv
    rw [h2] at h3
    linarith
  · have hre : (1 - ((N⁻¹ : ℝ) : ℂ) * ∑ i, a i * b i).re =
        1 - N⁻¹ * ∑ i, ((a i).re * (b i).re - (a i).im * (b i).im) := by
      rw [Complex.sub_re, Complex.one_re, Complex.re_ofReal_mul, Complex.re_sum]
      simp only [Complex.mul_re]
    have h1 : ∑ i, ((a i).re * (b i).re - (a i).im * (b i).im) ≤ ∑ i, (((a i).re ^ 2 + (b i).re ^ 2) / 2) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have := mul_pos (ha i) (hb i)
      nlinarith [sq_nonneg ((a i).re - (b i).re)]
    have h2 : ∑ i, (((a i).re ^ 2 + (b i).re ^ 2) / 2) = (∑ i, (a i).re ^ 2 + ∑ i, (b i).re ^ 2) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
    have h3 := ImmLower_re_sq_avg N hN hNpos a m hma hA
    have h4 := ImmLower_re_sq_avg N hN hNpos b m' hmb hB
    have h5 := mul_le_mul_of_nonneg_left h1 hNinv
    rw [h2] at h5
    rw [hre]
    linarith

/-- `‖w⁻¹‖ κ/(κ + δ) ≤ ‖w'⁻¹‖` when `κ ≤ ‖w‖`, `‖w' - w‖ ≤ δ`, `w' ≠ 0` (M4, pointwise). -/
private theorem ImmLower_b_ge (w w' : ℂ) (κ δ : ℝ) (hκ : 0 < κ) (hδ : 0 ≤ δ) (hw : κ ≤ ‖w‖) (hw' : w' ≠ 0)
    (hww : ‖w' - w‖ ≤ δ) : ‖w⁻¹‖ * (κ / (κ + δ)) ≤ ‖w'⁻¹‖ := by
  have hwpos : 0 < ‖w‖ := lt_of_lt_of_le hκ hw
  have hw'pos : 0 < ‖w'‖ := norm_pos_iff.mpr hw'
  have h1 : ‖w'‖ ≤ ‖w‖ + δ := by
    calc ‖w'‖ = ‖(w' - w) + w‖ := by rw [sub_add_cancel]
      _ ≤ ‖w' - w‖ + ‖w‖ := norm_add_le _ _
      _ ≤ ‖w‖ + δ := by linarith
  have h2 : κ * ‖w'‖ ≤ ‖w‖ * (κ + δ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hw) hδ, mul_le_mul_of_nonneg_left h1 hκ.le]
  rw [norm_inv, norm_inv]
  have hk : 0 < κ + δ := by linarith
  calc ‖w‖⁻¹ * (κ / (κ + δ)) = κ / (‖w‖ * (κ + δ)) := by field_simp
    _ ≤ 1 / ‖w'‖ := by
        rw [div_le_div_iff₀ (by positivity) hw'pos]; linarith
    _ = ‖w'‖⁻¹ := one_div _

end Generic

/-! ## 2. The spectral form of a solution of `(self_m)` -/

section Spectral

variable {d L : ℕ} [NeZero L]

/-- `a_i = (v_i - (z + m))⁻¹`, `v = BAspec d L g`. -/
private def ImmLower_a (d L : ℕ) [NeZero L] (g : ℝ) (z m : ℂ) (i : Zd d L) : ℂ :=
  ((BAspec d L g i : ℂ) - (z + m))⁻¹

private theorem ImmLower_zm_pos {g : ℝ} {z m : ℂ} (hz : 0 ≤ z.im) (h : BASelf d L g z m) : 0 < (z + m).im := by
  rw [Complex.add_im]; linarith [h.1]

private theorem ImmLower_N_pos (d L : ℕ) [NeZero L] : 0 < ((L ^ d : ℕ) : ℝ) := by
  have : 0 < L ^ d := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) d
  exact_mod_cast this

private theorem ImmLower_card (d L : ℕ) [NeZero L] : (Fintype.card (Zd d L) : ℝ) = ((L ^ d : ℕ) : ℝ) := by
  rw [BAcard_Zd]

/-- `m = ⟨a⟩` (`(self_m)` through `BAMB_trace_eq_sum`). -/
private theorem ImmLower_sum {g : ℝ} {z m : ℂ} (hz : 0 ≤ z.im) (h : BASelf d L g z m) :
    m = ((((L ^ d : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) * ∑ i, ImmLower_a d L g z m i := by
  have hzm : (z + m).im ≠ 0 := (ImmLower_zm_pos hz h).ne'
  have h1 : m = (((L ^ d : ℕ) : ℂ))⁻¹ * ∑ i, ((BAspec d L g i : ℂ) - (z + m))⁻¹ := by
    rw [← BAMB_trace_eq_sum d L g z m hzm]; exact h.2
  have hc : (((L ^ d : ℕ) : ℂ))⁻¹ = ((((L ^ d : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_inv, Complex.ofReal_natCast]
  refine h1.trans ?_
  rw [hc]
  rfl

private theorem ImmLower_a_im {g : ℝ} {z m : ℂ} (hz : 0 ≤ z.im) (h : BASelf d L g z m) (i : Zd d L) :
    (ImmLower_a d L g z m i).im = (z + m).im * ‖ImmLower_a d L g z m i‖ ^ 2 :=
  ImmLower_inv_im _ _ (ImmLower_zm_pos hz h)

private theorem ImmLower_a_ne {g : ℝ} {z m : ℂ} (hz : 0 ≤ z.im) (h : BASelf d L g z m) (i : Zd d L) :
    ImmLower_a d L g z m i ≠ 0 :=
  inv_ne_zero (ImmLower_inv_ne _ _ (ImmLower_zm_pos hz h))

private theorem ImmLower_a_im_pos {g : ℝ} {z m : ℂ} (hz : 0 ≤ z.im) (h : BASelf d L g z m) (i : Zd d L) :
    0 < (ImmLower_a d L g z m i).im := by
  rw [ImmLower_a_im hz h i]
  exact mul_pos (ImmLower_zm_pos hz h) (pow_pos (norm_pos_iff.mpr (ImmLower_a_ne hz h i)) 2)

/-- `Im m = ⟨Im a⟩`. -/
private theorem ImmLower_im_avg {g : ℝ} {z m : ℂ} (hz : 0 ≤ z.im) (h : BASelf d L g z m) :
    m.im = ((L ^ d : ℕ) : ℝ)⁻¹ * ∑ i, (ImmLower_a d L g z m i).im := by
  have him := congrArg Complex.im (ImmLower_sum hz h)
  rw [Complex.im_ofReal_mul, Complex.im_sum] at him
  exact him

/-- (M0) The averaged Ward identity in spectral form: `(Im z + Im m) ⟨|a|²⟩ = Im m`. -/
private theorem ImmLower_ward {g : ℝ} {z m : ℂ} (hz : 0 ≤ z.im) (h : BASelf d L g z m) :
    (z.im + m.im) * (((L ^ d : ℕ) : ℝ)⁻¹ * ∑ i, ‖ImmLower_a d L g z m i‖ ^ 2) = m.im := by
  have h1 := ImmLower_im_avg hz h
  have h2 : ∑ i, (ImmLower_a d L g z m i).im = (z + m).im * ∑ i, ‖ImmLower_a d L g z m i‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => ImmLower_a_im hz h i
  have h3 : (z + m).im = z.im + m.im := by simp [Complex.add_im]
  rw [h2, h3] at h1
  calc (z.im + m.im) * (((L ^ d : ℕ) : ℝ)⁻¹ * ∑ i, ‖ImmLower_a d L g z m i‖ ^ 2)
      = ((L ^ d : ℕ) : ℝ)⁻¹ * ((z.im + m.im) * ∑ i, ‖ImmLower_a d L g z m i‖ ^ 2) := by ring
    _ = m.im := h1.symm

/-- `⟨|a|²⟩ ≤ 1`. -/
private theorem ImmLower_A_le {g : ℝ} {z m : ℂ} (hz : 0 ≤ z.im) (h : BASelf d L g z m) :
    ((L ^ d : ℕ) : ℝ)⁻¹ * ∑ i, ‖ImmLower_a d L g z m i‖ ^ 2 ≤ 1 := by
  have h1 := ImmLower_ward hz h
  have hpos : 0 < z.im + m.im := by linarith [h.1]
  by_contra hc
  have hc := not_le.mp hc
  have := mul_lt_mul_of_pos_left hc hpos
  linarith [h.1]

/-- At real `z`, `⟨|a|²⟩ = 1`. -/
private theorem ImmLower_A_eq_real {g : ℝ} {z m : ℂ} (hz : z.im = 0) (h : BASelf d L g z m) :
    ((L ^ d : ℕ) : ℝ)⁻¹ * ∑ i, ‖ImmLower_a d L g z m i‖ ^ 2 = 1 := by
  have h1 := ImmLower_ward hz.ge h
  rw [hz, zero_add] at h1
  have hm := h.1
  have : m.im * (((L ^ d : ℕ) : ℝ)⁻¹ * ∑ i, ‖ImmLower_a d L g z m i‖ ^ 2 - 1) = 0 := by linarith
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd h0 hm.ne'
  · linarith

end Spectral

/-! ## 3. Target 1: the two-point stability estimate -/

/-- **Target 1 (M1-M2)**: for solutions `m`, `m'` of `(self_m)` at `z`, `z'` with `Im z, Im z' ≥ 0`,
`(Im m² + Im m'²) ‖m - m'‖ ≤ 2 ‖z - z'‖` (no dimension, no `L`, no `g` condition).  At `z = z'` real this is the stability gap
`BAgapReal` with constant 2 instead of 1; off the real axis it is the modulus of `m` (Lipschitz in `Re z`, uniformly in `Im z ≥ 0`
once `Im m ≥ κ`).  Paper: `7_8:1908` (the input for BA-C2). -/
theorem BASelf_sub_le (d L : ℕ) [NeZero L] (g : ℝ) (z z' m m' : ℂ) (hz : 0 ≤ z.im) (hz' : 0 ≤ z'.im)
    (h : BASelf d L g z m) (h' : BASelf d L g z' m') :
    (m.im ^ 2 + m'.im ^ 2) * ‖m - m'‖ ≤ 2 * ‖z - z'‖ := by
  set N : ℝ := ((L ^ d : ℕ) : ℝ) with hN
  have hNpos : 0 < N := ImmLower_N_pos d L
  have hcard : (Fintype.card (Zd d L) : ℝ) = N := ImmLower_card d L
  have hzm := ImmLower_zm_pos hz h
  have hzm' := ImmLower_zm_pos hz' h'
  obtain ⟨hT1, hT2⟩ := ImmLower_two_point N hcard hNpos (ImmLower_a d L g z m) (ImmLower_a d L g z' m') m m'
    (ImmLower_a_im_pos hz h) (ImmLower_a_im_pos hz' h') (ImmLower_im_avg hz h) (ImmLower_im_avg hz' h')
    (ImmLower_A_le hz h) (ImmLower_A_le hz' h')
  set T : ℂ := ((N⁻¹ : ℝ) : ℂ) * ∑ i, ImmLower_a d L g z m i * ImmLower_a d L g z' m' i with hT
  -- (M1)
  have hpt : ∀ i, ImmLower_a d L g z m i - ImmLower_a d L g z' m' i =
      ImmLower_a d L g z m i * ImmLower_a d L g z' m' i * ((z + m) - (z' + m')) := by
    intro i
    have h1 := ImmLower_inv_ne (BAspec d L g i) (z + m) hzm
    have h2 := ImmLower_inv_ne (BAspec d L g i) (z' + m') hzm'
    simp only [ImmLower_a]
    field_simp
    ring
  have e1 : ((N⁻¹ : ℝ) : ℂ) * ∑ i, ImmLower_a d L g z m i = m := (ImmLower_sum hz h).symm
  have e2 : ((N⁻¹ : ℝ) : ℂ) * ∑ i, ImmLower_a d L g z' m' i = m' := (ImmLower_sum hz' h').symm
  have hdiff : T * ((z + m) - (z' + m')) = m - m' := by
    calc T * ((z + m) - (z' + m'))
        = ((N⁻¹ : ℝ) : ℂ) * ∑ i, (ImmLower_a d L g z m i * ImmLower_a d L g z' m' i * ((z + m) - (z' + m'))) := by
          rw [hT, mul_assoc, Finset.sum_mul]
      _ = ((N⁻¹ : ℝ) : ℂ) * ∑ i, (ImmLower_a d L g z m i - ImmLower_a d L g z' m' i) := by
          rw [Finset.sum_congr rfl fun i _ => (hpt i).symm]
      _ = ((N⁻¹ : ℝ) : ℂ) * ∑ i, ImmLower_a d L g z m i - ((N⁻¹ : ℝ) : ℂ) * ∑ i, ImmLower_a d L g z' m' i := by
          rw [Finset.sum_sub_distrib, mul_sub]
      _ = m - m' := by rw [e1, e2]
  have hid : (m - m') * (1 - T) = (z - z') * T := by linear_combination (-1 : ℂ) * hdiff
  have hnorm : ‖m - m'‖ * ‖1 - T‖ = ‖z - z'‖ * ‖T‖ := by
    rw [← norm_mul, ← norm_mul, hid]
  have hre : (1 - T).re ≤ ‖1 - T‖ := Complex.re_le_norm _
  have hX : 0 ≤ ‖m - m'‖ := norm_nonneg _
  have hZ : 0 ≤ ‖z - z'‖ := norm_nonneg _
  have hP : m.im ^ 2 + m'.im ^ 2 ≤ 2 * ‖1 - T‖ := by linarith
  have h5 := mul_le_mul_of_nonneg_right hP hX
  have h6 := mul_le_mul_of_nonneg_left hT1 hZ
  nlinarith [h5, h6, hnorm]

/-! ## 4. Targets 2-6 -/

/-- `‖(η : ℂ) * I‖ = η` for `η > 0`. -/
private theorem ImmLower_norm_eta (η : ℝ) (hη : 0 < η) : ‖(η : ℂ) * Complex.I‖ = η := by
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]

/-- **Target 2 (M3)**: for `0 < η ≤ κ³/4` the bulk value at most halves: `κ/2 ≤ Im m(E + iη)`. -/
theorem BAm_im_ge_half (d L : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ) (hκ : 0 < κ) (h : BAReal d L g κ E m)
    (η : ℝ) (hη : 0 < η) (hη' : η ≤ κ ^ 3 / 4) :
    κ / 2 ≤ (BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im := by
  have hz' : 0 < ((E : ℂ) + (η : ℂ) * Complex.I).im := by simp [hη]
  have hs' := BAm_self d L g _ hz'
  set m' := BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I) with hm'
  have h1 := BASelf_sub_le d L g (E : ℂ) ((E : ℂ) + (η : ℂ) * Complex.I) m m' (by simp) hz'.le h.1 hs'
  have h2 : ‖(E : ℂ) - ((E : ℂ) + (η : ℂ) * Complex.I)‖ = η := by
    rw [sub_add_cancel_left, norm_neg, ImmLower_norm_eta η hη]
  rw [h2] at h1
  have hm : κ ≤ m.im := h.2
  have hX : 0 ≤ ‖m - m'‖ := norm_nonneg _
  have h3 : κ ^ 2 * ‖m - m'‖ ≤ 2 * η := by
    have : κ ^ 2 ≤ m.im ^ 2 + m'.im ^ 2 := by nlinarith [sq_nonneg m'.im]
    nlinarith [mul_le_mul_of_nonneg_right this hX]
  have h4 : ‖m - m'‖ ≤ κ / 2 := by
    by_contra hc
    have hc := not_le.mp hc
    have h5 : κ ^ 2 * (κ / 2) < κ ^ 2 * ‖m - m'‖ := mul_lt_mul_of_pos_left hc (by positivity)
    nlinarith
  have h5 : (m - m').im ≤ ‖m - m'‖ := Complex.im_le_norm _
  rw [Complex.sub_im] at h5
  linarith

/-- **Target 3 (M4)**: every `η > 0`, `Im m(E + iη) ≥ η κ²/(η + 3)²` (from `⟨|v - E - m|⁻²⟩ = 1`). -/
theorem BAm_im_ge_mul (d L : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ) (hκ : 0 < κ) (h : BAReal d L g κ E m)
    (η : ℝ) (hη : 0 < η) :
    η * κ ^ 2 / (η + 3) ^ 2 ≤ (BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im := by
  have hz : (E : ℂ).im = 0 := Complex.ofReal_im E
  have hz' : 0 < ((E : ℂ) + (η : ℂ) * Complex.I).im := by simp [hη]
  have hs' := BAm_self d L g _ hz'
  set z' : ℂ := (E : ℂ) + (η : ℂ) * Complex.I with hz'def
  set m' := BAm d L g z' with hm'
  have hm1 : ‖m‖ ≤ 1 := BAm_norm_le_one d L g (E : ℂ) m hz.ge h.1
  have hm'1 : ‖m'‖ ≤ 1 := BAm_norm_le_one d L g z' m' hz'.le hs'
  have hκ1 : κ ≤ 1 := h.2.trans ((Complex.im_le_norm m).trans hm1)
  have hz'im : z'.im = η := by simp [hz'def]
  set N : ℝ := ((L ^ d : ℕ) : ℝ) with hN
  have hNpos : 0 < N := ImmLower_N_pos d L
  have hNinv : 0 ≤ N⁻¹ := inv_nonneg.mpr hNpos.le
  have hzm := ImmLower_zm_pos hz.ge h.1
  have hzm' := ImmLower_zm_pos hz'.le hs'
  have hzmim : (E + m : ℂ).im = m.im := by simp
  have hAeq := ImmLower_A_eq_real hz h.1
  have hBw := ImmLower_ward hz'.le hs'
  have hBle := ImmLower_A_le hz'.le hs'
  set δ : ℝ := η + 2 with hδ
  have hδ0 : 0 ≤ δ := by linarith
  have hpt : ∀ i, ‖ImmLower_a d L g (E : ℂ) m i‖ ^ 2 * (κ / (κ + δ)) ^ 2 ≤ ‖ImmLower_a d L g z' m' i‖ ^ 2 := by
    intro i
    have hw : κ ≤ ‖(BAspec d L g i : ℂ) - ((E : ℂ) + m)‖ := by
      refine le_trans ?_ (ImmLower_norm_ge (BAspec d L g i) ((E : ℂ) + m) hzm)
      rw [hzmim]; exact h.2
    have hww : ‖((BAspec d L g i : ℂ) - (z' + m')) - ((BAspec d L g i : ℂ) - ((E : ℂ) + m))‖ ≤ δ := by
      have e : ((BAspec d L g i : ℂ) - (z' + m')) - ((BAspec d L g i : ℂ) - ((E : ℂ) + m)) =
          -((η : ℂ) * Complex.I) + m - m' := by simp only [hz'def]; ring
      rw [e]
      calc ‖-((η : ℂ) * Complex.I) + m - m'‖ ≤ ‖-((η : ℂ) * Complex.I) + m‖ + ‖m'‖ := norm_sub_le _ _
        _ ≤ (‖-((η : ℂ) * Complex.I)‖ + ‖m‖) + ‖m'‖ := by gcongr; exact norm_add_le _ _
        _ ≤ δ := by rw [norm_neg, ImmLower_norm_eta η hη]; linarith
    have hne : (BAspec d L g i : ℂ) - (z' + m') ≠ 0 := ImmLower_inv_ne _ _ hzm'
    have := ImmLower_b_ge _ _ κ δ hκ hδ0 hw hne hww
    have h0 : 0 ≤ ‖ImmLower_a d L g (E : ℂ) m i‖ * (κ / (κ + δ)) := by positivity
    calc ‖ImmLower_a d L g (E : ℂ) m i‖ ^ 2 * (κ / (κ + δ)) ^ 2
        = (‖ImmLower_a d L g (E : ℂ) m i‖ * (κ / (κ + δ))) ^ 2 := by ring
      _ ≤ ‖ImmLower_a d L g z' m' i‖ ^ 2 := pow_le_pow_left₀ h0 this 2
  have hBge : (κ / (κ + δ)) ^ 2 ≤ N⁻¹ * ∑ i, ‖ImmLower_a d L g z' m' i‖ ^ 2 := by
    have h1 : ∑ i, ‖ImmLower_a d L g (E : ℂ) m i‖ ^ 2 * (κ / (κ + δ)) ^ 2 ≤
        ∑ i, ‖ImmLower_a d L g z' m' i‖ ^ 2 := Finset.sum_le_sum fun i _ => hpt i
    rw [← Finset.sum_mul] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 hNinv
    calc (κ / (κ + δ)) ^ 2 = (N⁻¹ * ∑ i, ‖ImmLower_a d L g (E : ℂ) m i‖ ^ 2) * (κ / (κ + δ)) ^ 2 := by
          rw [hAeq, one_mul]
      _ = N⁻¹ * ((∑ i, ‖ImmLower_a d L g (E : ℂ) m i‖ ^ 2) * (κ / (κ + δ)) ^ 2) := by ring
      _ ≤ _ := h2
  have hkd : κ / (η + 3) ≤ κ / (κ + δ) := by
    refine div_le_div_of_nonneg_left hκ.le (by linarith) ?_
    linarith
  have hkd2 : (κ / (η + 3)) ^ 2 ≤ (κ / (κ + δ)) ^ 2 := pow_le_pow_left₀ (by positivity) hkd 2
  set B : ℝ := N⁻¹ * ∑ i, ‖ImmLower_a d L g z' m' i‖ ^ 2 with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hmpos : 0 < m'.im := hs'.1
  rw [hz'im] at hBw
  have hfin : η * B ≤ m'.im := by nlinarith [mul_nonneg hmpos.le hB0]
  calc η * κ ^ 2 / (η + 3) ^ 2 = η * (κ / (η + 3)) ^ 2 := by rw [div_pow]; ring
    _ ≤ η * B := mul_le_mul_of_nonneg_left (hkd2.trans hBge) hη.le
    _ ≤ m'.im := hfin

/-- **Target 4 (M5)**: the pin's conclusion at fixed `(L, g, E, m)`, with `c = κ⁵/64`. -/
theorem BAm_im_lower (d L : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ) (hκ : 0 < κ) (h : BAReal d L g κ E m)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    κ ^ 5 / 64 ≤ (BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im := by
  have hm1 : ‖m‖ ≤ 1 := BAm_norm_le_one d L g (E : ℂ) m (Complex.ofReal_im E).ge h.1
  have hκ1 : κ ≤ 1 := h.2.trans ((Complex.im_le_norm m).trans hm1)
  have h5 : κ ^ 5 ≤ κ := by
    calc κ ^ 5 = κ * κ ^ 4 := by ring
      _ ≤ κ * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hκ.le hκ1) hκ.le
      _ = κ := mul_one κ
  by_cases hc : η ≤ κ ^ 3 / 4
  · have := BAm_im_ge_half d L g κ E m hκ h η hη hc
    linarith
  · have hc := not_le.mp hc
    have h1 := BAm_im_ge_mul d L g κ E m hκ h η hη
    have h2 : η * κ ^ 2 / 16 ≤ η * κ ^ 2 / (η + 3) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
    have h3 : κ ^ 5 / 64 ≤ η * κ ^ 2 / 16 := by
      have : κ ^ 3 / 4 * κ ^ 2 ≤ η * κ ^ 2 := mul_le_mul_of_nonneg_right hc.le (by positivity)
      nlinarith
    linarith

/-- **Target 5**: the merged pin `BAImmLower` (`MFixedPoint.lean`, owed by BA-D7), proved at every `d`, `Λ`, `κ`, with
`c = κ⁵/64`.  The pin's premises `3 ≤ d`, `0 < Λ`, `0 < g`, `g ≤ Λ` are not used; `3 ≤ L` only for `NeZero L`. -/
theorem baImmLower_holds (d : ℕ) (Λ κ : ℝ) : BAImmLower d Λ κ := by
  intro _ _ hκ
  refine ⟨κ ^ 5 / 64, by positivity, ?_⟩
  intro L hL g _ _ E m
  have : NeZero L := ⟨by omega⟩
  intro h η hη hη1
  exact BAm_im_lower d L g κ E m hκ h η hη hη1

/-- **Target 6 (M6)**: the `ρ`-form (`BAbulk`, DECISIONS §51; supervisor 1102 O9 (b)): `ρ_N(E) ≥ κ` gives
`Im m(E + iη) ≥ (πκ)⁵/64` for `η ∈ (0, 1]`. -/
theorem BAm_im_lower_of_bulk (d L : ℕ) [NeZero L] (g κ E : ℝ) (hκ : 0 < κ) (hb : BAbulk d L g κ E)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    (Real.pi * κ) ^ 5 / 64 ≤ (BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im := by
  obtain ⟨m, hm, hmκ⟩ := (BAbulk_iff_exists d L g κ E hκ).mp hb
  exact BAm_im_lower d L g (Real.pi * κ) E m (by positivity) ⟨hm, hmκ⟩ η hη hη1

/-! ## 5. Compiled nonempty instances (`d = 3`, `L = 4`, the merged flow point of `(L, g) = (4, 10)`; no hypothesis left open) -/

end RBM.BA

namespace RBM.BA.ImmLowerInst

open RBM.BA RBM.BA.MFixedPointInst RBM.BA.CouplingWindowInst

/-- (I1) The pin `BAImmLower` itself, at `d = 3` and arbitrary `Λ`, `κ`. -/
example (Λ κ : ℝ) : BAImmLower 3 Λ κ := baImmLower_holds 3 Λ κ

/-- (I2) The pin's conclusion at the merged flow point: `c = (Im m_S)⁵/64`, `η ∈ (0, 1]`. -/
example : ∀ η : ℝ, 0 < η → η ≤ 1 →
    (mS 4 10).im ^ 5 / 64 ≤ (BAm 3 4 g0P ((EP : ℂ) + (η : ℂ) * Complex.I)).im :=
  fun η hη hη1 => BAm_im_lower 3 4 g0P (mS 4 10).im EP m0P (selfS 4 10).1 flowP_real η hη hη1

/-- (I3) Target 1 between the real point `(EP, m0P)` and `(EP + iη, m(EP + iη))`. -/
example : ∀ η : ℝ, 0 < η →
    (m0P.im ^ 2 + (BAm 3 4 g0P ((EP : ℂ) + (η : ℂ) * Complex.I)).im ^ 2) *
        ‖m0P - BAm 3 4 g0P ((EP : ℂ) + (η : ℂ) * Complex.I)‖
      ≤ 2 * ‖(EP : ℂ) - ((EP : ℂ) + (η : ℂ) * Complex.I)‖ := by
  intro η hη
  have hz' : 0 < ((EP : ℂ) + (η : ℂ) * Complex.I).im := by simp [hη]
  exact BASelf_sub_le 3 4 g0P (EP : ℂ) ((EP : ℂ) + (η : ℂ) * Complex.I) m0P _ (by simp) hz'.le
    flowP_data.2.2 (BAm_self 3 4 g0P _ hz')

/-- (I4) Target 6 at the `ρ`-bulk datum of the flow point: `ρ_4(EP) ≥ (Im m_S)/π`, `c = ((Im m_S))⁵/64`. -/
example : ∀ η : ℝ, 0 < η → η ≤ 1 →
    (Real.pi * ((mS 4 10).im / Real.pi)) ^ 5 / 64 ≤
      (BAm 3 4 g0P ((EP : ℂ) + (η : ℂ) * Complex.I)).im := by
  intro η hη hη1
  have hκ : 0 < (mS 4 10).im / Real.pi := div_pos (selfS 4 10).1 Real.pi_pos
  have hb : BAbulk 3 4 g0P ((mS 4 10).im / Real.pi) EP := by
    unfold BAbulk BArho
    rw [BAm_real_eq_of_self 3 4 g0P EP m0P flowP_real.1]
    exact div_le_div_of_nonneg_right flowP_real.2 Real.pi_pos.le
  exact BAm_im_lower_of_bulk 3 4 g0P _ EP hκ hb η hη hη1

/-- Target 2 at the flow point, `η = κ³/4` (the end of its range), `κ = Im m_S`. -/
example : (mS 4 10).im / 2 ≤
    (BAm 3 4 g0P ((EP : ℂ) + (((mS 4 10).im ^ 3 / 4 : ℝ) : ℂ) * Complex.I)).im :=
  BAm_im_ge_half 3 4 g0P (mS 4 10).im EP m0P (selfS 4 10).1 flowP_real ((mS 4 10).im ^ 3 / 4)
    (div_pos (pow_pos (selfS 4 10).1 3) (by norm_num)) le_rfl

/-- Target 3 at the flow point, `η = 1`. -/
example : (1 : ℝ) * (mS 4 10).im ^ 2 / (1 + 3) ^ 2 ≤
    (BAm 3 4 g0P ((EP : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)).im :=
  BAm_im_ge_mul 3 4 g0P (mS 4 10).im EP m0P (selfS 4 10).1 flowP_real 1 one_pos

end RBM.BA.ImmLowerInst
