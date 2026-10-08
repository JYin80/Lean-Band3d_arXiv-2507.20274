/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.KHeat

/-!
# Regime (i) `τ ≤ L²` of the heat kernel of `K = |M^{(B)}|²` (BA-P4b)

Ticket T2335 (BA stage P, row P4b; supervisor 2026-10-08-1048 C1 (i), C3).  Target `kBA_le`, the
twin of `Heat.kProd_le` (`HeatProduct.lean:439`) for the kernel `kBA τ = P_{τ/g²}(0, ·)` of `K`:
`kBA τ a ≤ C min(1, τ^{-d/2}) e^{-c min(|a|²/τ, |a|)}` for `τ ≤ L²`, `|a| = zdistD`.

Route.  The Chernoff step is done on the torus, with the test function `cosh(λ |x_j|_L)`; the
centered lift of `K` to `ℤ^d` is not constructed: the lift is only used through
`zdist(u ± v) ≤ |ε p ± δ q|`, `p = zdist u`, `q = zdist v`, `ε, δ = ±1` the signs of the
centered representatives (`KHeatTail_cosh_pair`).
(1) The coordinate pairing `cosh(λ|u+v|) + cosh(λ|u−v|) ≤ 2 cosh(λ|u|) cosh(λ|v|)` and the
symmetry `K(0,−c) = K(0,c)` give `Σ_b K(x,b) h(b) ≤ ρ_λ h(x)`, `h = cosh(λ |x_j|_L)`,
`ρ_λ = Σ_c K(0,c) cosh(λ|c_j|_L)`.  (2) Iterate along the Poisson series:
`Σ_b P_s(0,b) h(b) ≤ e^{s(ρ_λ−1)}`.  (3) `ρ_λ − 1 ≤ C g² λ²` for `λ ≤ c₀ = BAct_rate/2`, from
`BAK_exp_moment_le` (the diagonal `‖m‖²` cancels, `cosh 0 − 1 = 0`).  (4) Chernoff tail and union
over the coordinates.  (5) Semigroup splitting at `τ/2` and `kBA_diag_le`.

Nothing is ported from `../RBM1D` or `../RBM2D`.
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSectionVars false

noncomputable section

open Matrix

namespace RBM.BA

open RBM RBM.Gauss

/-! ## 1. One-dimensional facts on `ℤ_L` -/

section Zmod1

variable {L : ℕ} [NeZero L]

private theorem KHeatTail_zdist_natCast (k : ℕ) : zdist L (k : ZMod L) ≤ k := by
  unfold zdist
  rw [ZMod.val_natCast]
  exact (min_le_left _ _).trans (Nat.mod_le k L)

private theorem KHeatTail_zdist_intCast (n : ℤ) : (zdist L (n : ZMod L) : ℝ) ≤ |(n : ℝ)| := by
  have h : zdist L (n : ZMod L) ≤ n.natAbs := by
    rcases Int.natAbs_eq n with h | h
    · have h1 : (n : ZMod L) = ((n.natAbs : ℕ) : ZMod L) := by
        have := congrArg (Int.cast : ℤ → ZMod L) h
        simpa using this
      rw [h1]
      exact KHeatTail_zdist_natCast _
    · have h1 : (n : ZMod L) = -((n.natAbs : ℕ) : ZMod L) := by
        have := congrArg (Int.cast : ℤ → ZMod L) h
        simpa using this
      rw [h1, zdist_neg]
      exact KHeatTail_zdist_natCast _
  have h2 : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [← h2]
  exact_mod_cast h

private theorem KHeatTail_zdist_sign (u : ZMod L) :
    ∃ e : ℤ, (e = 1 ∨ e = -1) ∧ u = ((e * (zdist L u : ℕ) : ℤ) : ZMod L) := by
  have hv := ZMod.val_lt u
  by_cases h : u.val ≤ L - u.val
  · refine ⟨1, Or.inl rfl, ?_⟩
    have : zdist L u = u.val := by unfold zdist; exact min_eq_left h
    rw [this]
    simp
  · refine ⟨-1, Or.inr rfl, ?_⟩
    have : zdist L u = L - u.val := by unfold zdist; exact min_eq_right (by omega)
    rw [this]
    push_cast [Nat.cast_sub hv.le]
    simp

private theorem KHeatTail_cosh_pm (a b : ℝ) :
    Real.cosh (a + b) + Real.cosh (a - b) = 2 * Real.cosh a * Real.cosh b := by
  rw [Real.cosh_add, Real.cosh_sub]
  ring

private theorem KHeatTail_cosh_mono (lam z y : ℝ) (hz : 0 ≤ z) (hzy : z ≤ |y|) :
    Real.cosh (lam * z) ≤ Real.cosh (lam * y) := by
  rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_nonneg hz]
  exact mul_le_mul_of_nonneg_left hzy (abs_nonneg _)

private theorem KHeatTail_cosh_four (lam p q s t : ℝ) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    Real.cosh (lam * (s * p + t * q)) + Real.cosh (lam * (s * p - t * q))
      = 2 * Real.cosh (lam * p) * Real.cosh (lam * q) := by
  have key := KHeatTail_cosh_pm (lam * p) (lam * q)
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · rw [show lam * (1 * p + 1 * q) = lam * p + lam * q by ring,
      show lam * (1 * p - 1 * q) = lam * p - lam * q by ring]
    exact key
  · rw [show lam * (1 * p + -1 * q) = lam * p - lam * q by ring,
      show lam * (1 * p - -1 * q) = lam * p + lam * q by ring, add_comm]
    exact key
  · rw [show lam * (-1 * p + 1 * q) = -(lam * p - lam * q) by ring,
      show lam * (-1 * p - 1 * q) = -(lam * p + lam * q) by ring, Real.cosh_neg, Real.cosh_neg, add_comm]
    exact key
  · rw [show lam * (-1 * p + -1 * q) = -(lam * p + lam * q) by ring,
      show lam * (-1 * p - -1 * q) = -(lam * p - lam * q) by ring, Real.cosh_neg, Real.cosh_neg]
    exact key

/-- The coordinate pairing: `cosh(λ|u+v|) + cosh(λ|u−v|) ≤ 2 cosh(λ|u|) cosh(λ|v|)`. -/
private theorem KHeatTail_cosh_pair (lam : ℝ) (u v : ZMod L) :
    Real.cosh (lam * (zdist L (u + v) : ℝ)) + Real.cosh (lam * (zdist L (u - v) : ℝ))
      ≤ 2 * Real.cosh (lam * (zdist L u : ℝ)) * Real.cosh (lam * (zdist L v : ℝ)) := by
  obtain ⟨e, he, hu⟩ := KHeatTail_zdist_sign u
  obtain ⟨f, hf, hv⟩ := KHeatTail_zdist_sign v
  set p : ℕ := zdist L u with hp
  set q : ℕ := zdist L v with hq
  have h1 : u + v = ((e * p + f * q : ℤ) : ZMod L) := by
    calc u + v = ((e * p : ℤ) : ZMod L) + ((f * q : ℤ) : ZMod L) := by rw [← hu, ← hv]
      _ = _ := (Int.cast_add _ _).symm
  have h2 : u - v = ((e * p - f * q : ℤ) : ZMod L) := by
    calc u - v = ((e * p : ℤ) : ZMod L) - ((f * q : ℤ) : ZMod L) := by rw [← hu, ← hv]
      _ = _ := (Int.cast_sub _ _).symm
  have h1' := KHeatTail_zdist_intCast (L := L) (e * p + f * q)
  have h2' := KHeatTail_zdist_intCast (L := L) (e * p - f * q)
  rw [← h1] at h1'
  rw [← h2] at h2'
  have c1 := KHeatTail_cosh_mono lam _ _ (Nat.cast_nonneg _) h1'
  have c2 := KHeatTail_cosh_mono lam _ _ (Nat.cast_nonneg _) h2'
  refine (add_le_add c1 c2).trans (le_of_eq ?_)
  push_cast
  have he' : (e : ℝ) = 1 ∨ (e : ℝ) = -1 := by rcases he with rfl | rfl <;> simp
  have hf' : (f : ℝ) = 1 ∨ (f : ℝ) = -1 := by rcases hf with rfl | rfl <;> simp
  exact KHeatTail_cosh_four lam p q e f he' hf'

end Zmod1

/-! ## 2. The test function, one step of `K`, the Poisson series -/

section Step

variable (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ)

/-- The test function `h(x) = cosh(λ |x_j|_L)`. -/
private def KHeatTail_h (lam : ℝ) (j : Fin d) (x : Zd d L) : ℝ :=
  Real.cosh (lam * (zdist L (x j) : ℝ))

private theorem KHeatTail_h_pos (lam : ℝ) (j : Fin d) (x : Zd d L) : 0 < KHeatTail_h d L lam j x :=
  Real.cosh_pos _

private theorem KHeatTail_h_zero (lam : ℝ) (j : Fin d) : KHeatTail_h d L lam j 0 = 1 := by
  simp [KHeatTail_h]

/-- The mean of `h` under one step of `K` from `0`. -/
private def KHeatTail_rho (lam : ℝ) (j : Fin d) : ℝ :=
  ∑ c, BAK d L g E m 0 c * KHeatTail_h d L lam j c

private theorem KHeatTail_rho_nonneg (lam : ℝ) (j : Fin d) : 0 ≤ KHeatTail_rho d L g E m lam j :=
  Finset.sum_nonneg fun c _ => mul_nonneg (BAK_nonneg d L g E m 0 c) (KHeatTail_h_pos d L lam j c).le

/-- One step: `Σ_b K(x,b) h(b) ≤ ρ_λ h(x)` (pairing `c ↔ -c` and `K(0,-c) = K(0,c)`). -/
private theorem KHeatTail_step (lam : ℝ) (j : Fin d) (x : Zd d L) :
    ∑ b, BAK d L g E m x b * KHeatTail_h d L lam j b
      ≤ KHeatTail_rho d L g E m lam j * KHeatTail_h d L lam j x := by
  have h1 : ∑ b, BAK d L g E m x b * KHeatTail_h d L lam j b
      = ∑ c, BAK d L g E m 0 c * KHeatTail_h d L lam j (x + c) := by
    rw [← Equiv.sum_comp (Equiv.addLeft x)]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Equiv.coe_addLeft]
    have := BAK_shift d L g E m 0 c x
    rw [zero_add, add_comm c x] at this
    rw [this]
  have h2 : ∑ c, BAK d L g E m 0 c * KHeatTail_h d L lam j (x + c)
      = ∑ c, BAK d L g E m 0 c * KHeatTail_h d L lam j (x - c) := by
    rw [← Equiv.sum_comp (Equiv.neg (Zd d L))]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Equiv.neg_apply]
    rw [BAK_zero_neg, ← sub_eq_add_neg]
  have h3 : 2 * ∑ c, BAK d L g E m 0 c * KHeatTail_h d L lam j (x + c)
      ≤ 2 * (KHeatTail_rho d L g E m lam j * KHeatTail_h d L lam j x) := by
    calc 2 * ∑ c, BAK d L g E m 0 c * KHeatTail_h d L lam j (x + c)
        = ∑ c, BAK d L g E m 0 c * KHeatTail_h d L lam j (x + c)
            + ∑ c, BAK d L g E m 0 c * KHeatTail_h d L lam j (x - c) := by rw [two_mul, ← h2]
      _ = ∑ c, BAK d L g E m 0 c * (KHeatTail_h d L lam j (x + c) + KHeatTail_h d L lam j (x - c)) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun c _ => (mul_add _ _ _).symm
      _ ≤ ∑ c, BAK d L g E m 0 c * (2 * KHeatTail_h d L lam j x * KHeatTail_h d L lam j c) := by
          refine Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left ?_ (BAK_nonneg d L g E m 0 c)
          simp only [KHeatTail_h, Pi.add_apply, Pi.sub_apply]
          exact KHeatTail_cosh_pair lam (x j) (c j)
      _ = 2 * (KHeatTail_rho d L g E m lam j * KHeatTail_h d L lam j x) := by
          unfold KHeatTail_rho
          rw [Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ => by ring
  rw [h1]
  linarith

/-- The iterated step: `Σ_b (Kⁿ)(0,b) h(b) ≤ ρ_λⁿ`. -/
private theorem KHeatTail_pow (lam : ℝ) (j : Fin d) (n : ℕ) :
    ∑ b, (BAK d L g E m ^ n) 0 b * KHeatTail_h d L lam j b ≤ KHeatTail_rho d L g E m lam j ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp [KHeatTail_h_zero]
  | succ n ih =>
    have hr := KHeatTail_rho_nonneg d L g E m lam j
    calc ∑ b, (BAK d L g E m ^ (n + 1)) 0 b * KHeatTail_h d L lam j b
        = ∑ c, (BAK d L g E m ^ n) 0 c * ∑ b, BAK d L g E m c b * KHeatTail_h d L lam j b := by
          simp only [pow_succ, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by ring
      _ ≤ ∑ c, (BAK d L g E m ^ n) 0 c
            * (KHeatTail_rho d L g E m lam j * KHeatTail_h d L lam j c) :=
          Finset.sum_le_sum fun c _ =>
            mul_le_mul_of_nonneg_left (KHeatTail_step d L g E m lam j c) (BAK_pow_nonneg d L g E m n 0 c)
      _ = KHeatTail_rho d L g E m lam j * ∑ c, (BAK d L g E m ^ n) 0 c * KHeatTail_h d L lam j c := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ => by ring
      _ ≤ KHeatTail_rho d L g E m lam j * KHeatTail_rho d L g E m lam j ^ n :=
          mul_le_mul_of_nonneg_left ih hr
      _ = _ := by rw [pow_succ']

private theorem KHeatTail_pow_le_one (h : BASelf d L g (E : ℂ) m) (n : ℕ) (a b : Zd d L) :
    (BAK d L g E m ^ n) a b ≤ 1 := by
  calc (BAK d L g E m ^ n) a b ≤ ∑ c, (BAK d L g E m ^ n) a c :=
        Finset.single_le_sum (f := fun c => (BAK d L g E m ^ n) a c)
          (fun c _ => BAK_pow_nonneg d L g E m n a c) (Finset.mem_univ b)
    _ = 1 := BAK_pow_row_sum d L g E m h n a

private theorem KHeatTail_summable (h : BASelf d L g (E : ℂ) m) (s : ℝ) (a b : Zd d L) :
    Summable (fun n : ℕ => s ^ n / (n.factorial : ℝ) * (BAK d L g E m ^ n) a b) := by
  refine Summable.of_norm_bounded (Real.summable_pow_div_factorial |s|) (fun n => ?_)
  have h0 := BAK_pow_nonneg d L g E m n a b
  have h1 := KHeatTail_pow_le_one d L g E m h n a b
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast]
  calc |s| ^ n / (n.factorial : ℝ) * |(BAK d L g E m ^ n) a b|
      ≤ |s| ^ n / (n.factorial : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left (by rw [abs_of_nonneg h0]; exact h1) (by positivity)
    _ = _ := mul_one _

private theorem KHeatTail_tsum_exp (x : ℝ) :
    ∑' n : ℕ, x ^ n / (n.factorial : ℝ) = Real.exp x := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) x
  rw [Real.exp_eq_exp_ℝ]
  exact h.tsum_eq

/-- The Poisson series: `Σ_b P_s(0,b) h(b) ≤ e^{s(ρ_λ-1)}` for `s ≥ 0`. -/
private theorem KHeatTail_P_h (h : BASelf d L g (E : ℂ) m) (lam : ℝ) (j : Fin d) {s : ℝ} (hs : 0 ≤ s) :
    ∑ b, BAP d L g E m s 0 b * KHeatTail_h d L lam j b
      ≤ Real.exp (s * (KHeatTail_rho d L g E m lam j - 1)) := by
  set ρ := KHeatTail_rho d L g E m lam j with hρ
  have hsum : ∀ b : Zd d L, Summable (fun n : ℕ => s ^ n / (n.factorial : ℝ) * (BAK d L g E m ^ n) 0 b
      * KHeatTail_h d L lam j b) :=
    fun b => (KHeatTail_summable d L g E m h s 0 b).mul_right _
  calc ∑ b, BAP d L g E m s 0 b * KHeatTail_h d L lam j b
      = Real.exp (-s) * ∑' n : ℕ, ∑ b, s ^ n / (n.factorial : ℝ) * (BAK d L g E m ^ n) 0 b
          * KHeatTail_h d L lam j b := by
        rw [Summable.tsum_finsetSum (fun b _ => hsum b), Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        unfold BAP
        rw [tsum_mul_right, mul_assoc]
    _ ≤ Real.exp (-s) * ∑' n : ℕ, s ^ n / (n.factorial : ℝ) * ρ ^ n := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        refine Summable.tsum_le_tsum (fun n => ?_)
          (summable_sum fun b _ => hsum b) ?_
        · calc ∑ b, s ^ n / (n.factorial : ℝ) * (BAK d L g E m ^ n) 0 b * KHeatTail_h d L lam j b
              = s ^ n / (n.factorial : ℝ) * ∑ b, (BAK d L g E m ^ n) 0 b * KHeatTail_h d L lam j b := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun b _ => by ring
            _ ≤ s ^ n / (n.factorial : ℝ) * ρ ^ n :=
                mul_le_mul_of_nonneg_left (KHeatTail_pow d L g E m lam j n) (by positivity)
        · have := Real.summable_pow_div_factorial (s * ρ)
          refine this.congr fun n => ?_
          rw [mul_pow]
          ring
    _ = Real.exp (s * (ρ - 1)) := by
        have h2 : ∑' n : ℕ, s ^ n / (n.factorial : ℝ) * ρ ^ n = Real.exp (s * ρ) := by
          rw [← KHeatTail_tsum_exp]
          refine tsum_congr fun n => ?_
          rw [mul_pow]
          ring
        rw [h2, ← Real.exp_add]
        congr 1
        ring

end Step

/-! ## 3. The quadratic Chernoff constant -/

section Chernoff

variable (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ)

/-- `cosh y − 1 ≤ (y²/2) e^y` for `y ≥ 0`. -/
private theorem KHeatTail_cosh_sub_one_le {y : ℝ} (hy : 0 ≤ y) :
    Real.cosh y - 1 ≤ y ^ 2 / 2 * Real.exp y := by
  set X : ℝ := Real.exp y with hX
  set F : ℝ := Real.exp (-y) with hF
  have hXF : X * F = 1 := by rw [hX, hF, ← Real.exp_add]; simp
  have hX1 : 1 ≤ X := Real.one_le_exp hy
  have hF0 : 0 < F := Real.exp_pos _
  have h1 : 1 - y ≤ F := by have := Real.add_one_le_exp (-y); linarith
  have h2 : X - 1 ≤ y * X := by
    have := mul_le_mul_of_nonneg_left h1 (by linarith : 0 ≤ X)
    nlinarith
  have h3 : (X - 1) ^ 2 ≤ (y * X) ^ 2 := pow_le_pow_left₀ (by linarith) h2 2
  have h4 : Real.cosh y = (X + F) / 2 := by rw [Real.cosh_eq]
  have h5 : X + F - 2 = F * (X - 1) ^ 2 := by nlinarith
  have h6 : F * (X - 1) ^ 2 ≤ y ^ 2 * X := by
    calc F * (X - 1) ^ 2 ≤ F * (y * X) ^ 2 := mul_le_mul_of_nonneg_left h3 hF0.le
      _ = y ^ 2 * X * (X * F) := by ring
      _ = y ^ 2 * X := by rw [hXF, mul_one]
  rw [h4]
  linarith

/-- Constant of the Chernoff bound (depends on `(d, Λ, κ)` only). -/
private def KHeatTail_C (d : ℕ) (Λ κ : ℝ) : ℝ :=
  max 1 ((BAct_rate d Λ κ / 2)⁻¹ ^ 2 * (BAp5s_A d Λ κ * BAp5s_S d Λ κ))

private theorem KHeatTail_C_pos (d : ℕ) (Λ κ : ℝ) : 0 < KHeatTail_C d Λ κ :=
  lt_of_lt_of_le one_pos (le_max_left _ _)

/-- `Σ_c K(0,c)(cosh(λ|c_j|) − 1) ≤ C g² λ²` for `0 ≤ λ ≤ c₀ = BAct_rate/2`: the diagonal term
cancels (`cosh 0 − 1 = 0`) and the quadratic bound uses `BAK_exp_moment_le` at `μ = λ + c₀ ≤ BAct_rate`. -/
private theorem KHeatTail_cosh_sum (hL : 3 ≤ L) (hd : 2 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ)
    (hg : 0 < g) (hgΛ : g ≤ Λ) (hr : BAReal d L g κ E m) (j : Fin d) (lam : ℝ) (hl0 : 0 ≤ lam)
    (hlc : lam ≤ BAct_rate d Λ κ / 2) :
    ∑ c, BAK d L g E m 0 c * (Real.cosh (lam * (zdist L (c j) : ℝ)) - 1)
      ≤ KHeatTail_C d Λ κ * g ^ 2 * lam ^ 2 := by
  have hd0 : 0 < d := by omega
  have hc := BAct_rate_pos d Λ κ hd0 hΛ hκ
  set ε : ℝ := BAct_rate d Λ κ / 2 with hε
  have hε0 : 0 < ε := by positivity
  set μ : ℝ := lam + ε with hμ
  have hmom := BAK_exp_moment_le d L hL hd Λ g κ E m hΛ hg hgΛ hκ hr μ (by positivity)
    (by linarith [hμ, hε]) 0
  -- the pointwise bound
  have hterm : ∀ c : Zd d L, c ≠ 0 →
      BAK d L g E m 0 c * (Real.cosh (lam * (zdist L (c j) : ℝ)) - 1)
        ≤ lam ^ 2 / ε ^ 2 * (BAK d L g E m 0 c * Real.exp (μ * (zdistD d L (0 - c) : ℝ))) := by
    intro c _
    have hn : (zdistD d L (0 - c) : ℝ) = (zdistD d L c : ℝ) := by
      rw [zero_sub, zdistD_neg]
    rw [hn]
    set n : ℝ := (zdistD d L c : ℝ) with hn'
    have hn0 : 0 ≤ n := Nat.cast_nonneg _
    set r : ℝ := (zdist L (c j) : ℝ) with hr'
    have hr0 : 0 ≤ r := Nat.cast_nonneg _
    have hrn : r ≤ n := by
      rw [hr', hn']
      exact_mod_cast Finset.single_le_sum (f := fun i => zdist L (c i)) (fun i _ => Nat.zero_le _)
        (Finset.mem_univ j)
    have h1 := KHeatTail_cosh_sub_one_le (mul_nonneg hl0 hr0)
    have h2 : Real.exp (lam * r) ≤ Real.exp (lam * n) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hrn hl0)
    have h3 : (lam * r) ^ 2 ≤ (lam * n) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hl0 hr0) (mul_le_mul_of_nonneg_left hrn hl0) 2
    have h4 : n ^ 2 ≤ 2 / ε ^ 2 * Real.exp (ε * n) := by
      have := Real.quadratic_le_exp_of_nonneg (mul_nonneg hε0.le hn0)
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [Real.exp_pos (ε * n)]
    have h5 : Real.cosh (lam * r) - 1 ≤ lam ^ 2 / ε ^ 2 * Real.exp (μ * n) := by
      calc Real.cosh (lam * r) - 1 ≤ (lam * r) ^ 2 / 2 * Real.exp (lam * r) := h1
        _ ≤ (lam * n) ^ 2 / 2 * Real.exp (lam * n) := by
            gcongr
        _ = lam ^ 2 / 2 * n ^ 2 * Real.exp (lam * n) := by ring
        _ ≤ lam ^ 2 / 2 * (2 / ε ^ 2 * Real.exp (ε * n)) * Real.exp (lam * n) := by
            gcongr
        _ = lam ^ 2 / ε ^ 2 * (Real.exp (ε * n) * Real.exp (lam * n)) := by
            field_simp
        _ = lam ^ 2 / ε ^ 2 * Real.exp (μ * n) := by
            rw [← Real.exp_add, hμ]
            congr 2
            ring
    calc BAK d L g E m 0 c * (Real.cosh (lam * r) - 1)
        ≤ BAK d L g E m 0 c * (lam ^ 2 / ε ^ 2 * Real.exp (μ * n)) :=
          mul_le_mul_of_nonneg_left h5 (BAK_nonneg d L g E m 0 c)
      _ = _ := by ring
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : Zd d L))]
  have hz : BAK d L g E m 0 0 * (Real.cosh (lam * (zdist L ((0 : Zd d L) j) : ℝ)) - 1) = 0 := by
    simp
  rw [hz, zero_add]
  have hdiag : BAK d L g E m 0 0 * Real.exp (μ * (zdistD d L (0 - 0) : ℝ)) = ‖m‖ ^ 2 := by
    rw [sub_self, zdistD_zero, BAK_diag d L g E m hr.1 0]
    simp
  have hmom' := hmom
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : Zd d L)), hdiag] at hmom'
  have hAS : ∑ c ∈ Finset.univ.erase (0 : Zd d L),
      BAK d L g E m 0 c * Real.exp (μ * (zdistD d L (0 - c) : ℝ))
        ≤ BAp5s_A d Λ κ * g ^ 2 * BAp5s_S d Λ κ := by linarith
  calc ∑ c ∈ Finset.univ.erase (0 : Zd d L),
        BAK d L g E m 0 c * (Real.cosh (lam * (zdist L (c j) : ℝ)) - 1)
      ≤ ∑ c ∈ Finset.univ.erase (0 : Zd d L),
          lam ^ 2 / ε ^ 2 * (BAK d L g E m 0 c * Real.exp (μ * (zdistD d L (0 - c) : ℝ))) :=
        Finset.sum_le_sum fun c hc' => hterm c (Finset.ne_of_mem_erase hc')
    _ = lam ^ 2 / ε ^ 2 * ∑ c ∈ Finset.univ.erase (0 : Zd d L),
          BAK d L g E m 0 c * Real.exp (μ * (zdistD d L (0 - c) : ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ lam ^ 2 / ε ^ 2 * (BAp5s_A d Λ κ * g ^ 2 * BAp5s_S d Λ κ) :=
        mul_le_mul_of_nonneg_left hAS (by positivity)
    _ = (ε⁻¹ ^ 2 * (BAp5s_A d Λ κ * BAp5s_S d Λ κ)) * g ^ 2 * lam ^ 2 := by
        field_simp
    _ ≤ KHeatTail_C d Λ κ * g ^ 2 * lam ^ 2 := by
        have := le_max_right 1 (ε⁻¹ ^ 2 * (BAp5s_A d Λ κ * BAp5s_S d Λ κ))
        unfold KHeatTail_C
        have h7 : 0 ≤ g ^ 2 * lam ^ 2 := by positivity
        nlinarith

end Chernoff

/-! ## 4. The Chernoff tail -/

section Tail

variable (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ)

/-- The `cosh` moment of one coordinate: `Σ_b kBA τ b cosh(λ|b_j|) ≤ e^{C τ λ²}`, `0 ≤ λ ≤ c₀`. -/
private theorem KHeatTail_moment (hL : 3 ≤ L) (hd : 2 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ)
    (hg : 0 < g) (hgΛ : g ≤ Λ) (hr : BAReal d L g κ E m) (j : Fin d) (lam : ℝ) (hl0 : 0 ≤ lam)
    (hlc : lam ≤ BAct_rate d Λ κ / 2) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∑ b, kBA d L g E m τ b * Real.cosh (lam * (zdist L (b j) : ℝ))
      ≤ Real.exp (KHeatTail_C d Λ κ * τ * lam ^ 2) := by
  have hs : 0 ≤ τ / g ^ 2 := div_nonneg hτ (sq_nonneg g)
  have h1 := KHeatTail_P_h d L g E m hr.1 lam j hs
  have h2 : KHeatTail_rho d L g E m lam j - 1
      = ∑ c, BAK d L g E m 0 c * (Real.cosh (lam * (zdist L (c j) : ℝ)) - 1) := by
    simp only [mul_sub, Finset.sum_sub_distrib, mul_one, BAK_row_sum d L g E m hr.1 0]
    rfl
  have h3 := KHeatTail_cosh_sum d L g E m hL hd Λ κ hΛ hκ hg hgΛ hr j lam hl0 hlc
  rw [← h2] at h3
  have h4 : τ / g ^ 2 * (KHeatTail_rho d L g E m lam j - 1) ≤ KHeatTail_C d Λ κ * τ * lam ^ 2 := by
    calc τ / g ^ 2 * (KHeatTail_rho d L g E m lam j - 1)
        ≤ τ / g ^ 2 * (KHeatTail_C d Λ κ * g ^ 2 * lam ^ 2) := mul_le_mul_of_nonneg_left h3 hs
      _ = KHeatTail_C d Λ κ * τ * lam ^ 2 := by field_simp
  refine le_trans ?_ (Real.exp_le_exp.mpr h4)
  exact h1

/-- Chernoff tail of one coordinate. -/
private theorem KHeatTail_coord_tail (hL : 3 ≤ L) (hd : 2 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ)
    (hg : 0 < g) (hgΛ : g ≤ Λ) (hr : BAReal d L g κ E m) (j : Fin d) (lam : ℝ) (hl0 : 0 ≤ lam)
    (hlc : lam ≤ BAct_rate d Λ κ / 2) {τ : ℝ} (hτ : 0 ≤ τ) (R : ℝ) :
    ∑ b ∈ Finset.univ.filter (fun b : Zd d L => R ≤ (zdist L (b j) : ℝ)), kBA d L g E m τ b
      ≤ 2 * Real.exp (-(lam * R) + KHeatTail_C d Λ κ * τ * lam ^ 2) := by
  have hk := (kBA_basic d L g E m hg hr.1).1 τ hτ
  have hmom := KHeatTail_moment d L g E m hL hd Λ κ hΛ hκ hg hgΛ hr j lam hl0 hlc hτ
  have hw : ∀ b : Zd d L, R ≤ (zdist L (b j) : ℝ) →
      1 ≤ 2 * Real.exp (-(lam * R)) * Real.cosh (lam * (zdist L (b j) : ℝ)) := by
    intro b hb
    have h1 : Real.exp (lam * R) ≤ Real.exp (lam * (zdist L (b j) : ℝ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hb hl0)
    have h2 : Real.exp (lam * (zdist L (b j) : ℝ)) ≤ 2 * Real.cosh (lam * (zdist L (b j) : ℝ)) := by
      rw [Real.cosh_eq]
      have := Real.exp_pos (-(lam * (zdist L (b j) : ℝ)))
      linarith
    have h3 : Real.exp (-(lam * R)) * Real.exp (lam * R) = 1 := by
      rw [← Real.exp_add]; simp
    calc (1 : ℝ) = Real.exp (-(lam * R)) * Real.exp (lam * R) := h3.symm
      _ ≤ Real.exp (-(lam * R)) * (2 * Real.cosh (lam * (zdist L (b j) : ℝ))) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (Real.exp_pos _).le
      _ = _ := by ring
  calc ∑ b ∈ Finset.univ.filter (fun b : Zd d L => R ≤ (zdist L (b j) : ℝ)), kBA d L g E m τ b
      ≤ ∑ b ∈ Finset.univ.filter (fun b : Zd d L => R ≤ (zdist L (b j) : ℝ)),
          kBA d L g E m τ b * (2 * Real.exp (-(lam * R)) * Real.cosh (lam * (zdist L (b j) : ℝ))) := by
        refine Finset.sum_le_sum fun b hb => ?_
        have := hw b (Finset.mem_filter.mp hb).2
        nlinarith [hk b]
    _ ≤ ∑ b : Zd d L,
          kBA d L g E m τ b * (2 * Real.exp (-(lam * R)) * Real.cosh (lam * (zdist L (b j) : ℝ))) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun b _ _ => ?_
        have := Real.cosh_pos (lam * (zdist L (b j) : ℝ))
        have := Real.exp_pos (-(lam * R))
        have := hk b
        positivity
    _ = 2 * Real.exp (-(lam * R)) * ∑ b : Zd d L, kBA d L g E m τ b * Real.cosh (lam * (zdist L (b j) : ℝ)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
    _ ≤ 2 * Real.exp (-(lam * R)) * Real.exp (KHeatTail_C d Λ κ * τ * lam ^ 2) :=
        mul_le_mul_of_nonneg_left hmom (by positivity)
    _ = 2 * Real.exp (-(lam * R) + KHeatTail_C d Λ κ * τ * lam ^ 2) := by
        rw [Real.exp_add]; ring

/-- Choice of the tilt: `λ = min(R/(2Cτ), c₀)`. -/
private theorem KHeatTail_opt (C c₀ τ R : ℝ) (hC : 0 < C) (hc₀ : 0 < c₀) (hτ : 0 < τ) (hR : 0 ≤ R) :
    ∃ lam : ℝ, 0 ≤ lam ∧ lam ≤ c₀ ∧
      -(lam * R) + C * τ * lam ^ 2 ≤ -min (R ^ 2 / (4 * C * τ)) (c₀ * R / 2) := by
  have hCτ : 0 < C * τ := mul_pos hC hτ
  have h0 : 0 ≤ R / (2 * C * τ) := by positivity
  refine ⟨min (R / (2 * C * τ)) c₀, le_min h0 hc₀.le, min_le_right _ _, ?_⟩
  rcases le_total (R / (2 * C * τ)) c₀ with h | h
  · rw [min_eq_left h]
    have h1 : -(R / (2 * C * τ) * R) + C * τ * (R / (2 * C * τ)) ^ 2 = -(R ^ 2 / (4 * C * τ)) := by
      field_simp
      ring
    rw [h1]
    exact neg_le_neg (min_le_left _ _)
  · rw [min_eq_right h]
    have h2 : c₀ * (2 * C * τ) ≤ R := by
      have := (le_div_iff₀ (by positivity : 0 < 2 * C * τ)).mp h
      exact this
    have h3 : C * τ * c₀ ^ 2 ≤ c₀ * R / 2 := by nlinarith
    have h4 : -(c₀ * R) + C * τ * c₀ ^ 2 ≤ -(c₀ * R / 2) := by linarith
    exact h4.trans (neg_le_neg (min_le_right _ _))

end Tail

/-! ## 5. Target helper: the tail of the torus `ℓ¹` distance -/

/-- **Tail of the heat kernel** (public helper): `Σ_{|b| ≥ ρ} kBA τ b ≤ 2d e^{-c_T min(ρ²/τ, ρ)}`,
`|b| = zdistD d L b`, for every `τ > 0`, `ρ ≥ 0`; `c_T` depends on `(d, Λ, κ)` only. -/
theorem BAP_tail_le : ∀ d : ℕ, 2 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ cT : ℝ, 0 < cT ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ τ : ℝ, 0 < τ → ∀ ρ : ℝ, 0 ≤ ρ →
        ∑ b ∈ Finset.univ.filter (fun b : Zd d L => ρ ≤ (zdistD d L b : ℝ)), kBA d L g E m τ b
          ≤ 2 * d * Real.exp (-cT * min (ρ ^ 2 / τ) ρ) := by
  intro d hd Λ κ hΛ hκ
  have hd0 : 0 < d := by omega
  have hc := BAct_rate_pos d Λ κ hd0 hΛ hκ
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  set C : ℝ := KHeatTail_C d Λ κ with hC
  have hCpos : 0 < C := KHeatTail_C_pos d Λ κ
  set c₀ : ℝ := BAct_rate d Λ κ / 2 with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  set cT : ℝ := min (1 / (4 * (d : ℝ) ^ 2 * C)) (c₀ / (2 * d)) with hcT
  have hcT0 : 0 < cT := lt_min (by positivity) (by positivity)
  refine ⟨cT, hcT0, ?_⟩
  intro L _ hL g E m hg hgΛ hr τ hτ ρ hρ
  set R : ℝ := ρ / d with hR
  have hR0 : 0 ≤ R := by positivity
  obtain ⟨lam, hl0, hlc, hopt⟩ := KHeatTail_opt C c₀ τ R hCpos hc₀pos hτ hR0
  have hcoord : ∀ j : Fin d,
      ∑ b ∈ Finset.univ.filter (fun b : Zd d L => R ≤ (zdist L (b j) : ℝ)), kBA d L g E m τ b
        ≤ 2 * Real.exp (-(cT * min (ρ ^ 2 / τ) ρ)) := by
    intro j
    refine (KHeatTail_coord_tail d L g E m hL hd Λ κ hΛ hκ hg hgΛ hr j lam hl0 hlc hτ.le R).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hopt.trans (neg_le_neg ?_))) (by norm_num)
    have hq : 0 ≤ ρ ^ 2 / τ := by positivity
    have hm1 : min (ρ ^ 2 / τ) ρ ≤ ρ ^ 2 / τ := min_le_left _ _
    have hm2 : min (ρ ^ 2 / τ) ρ ≤ ρ := min_le_right _ _
    have hmn : 0 ≤ min (ρ ^ 2 / τ) ρ := le_min hq hρ
    refine le_min ?_ ?_
    · calc cT * min (ρ ^ 2 / τ) ρ ≤ (1 / (4 * (d : ℝ) ^ 2 * C)) * (ρ ^ 2 / τ) :=
            mul_le_mul (min_le_left _ _) hm1 hmn (by positivity)
        _ = R ^ 2 / (4 * C * τ) := by rw [hR]; field_simp
    · calc cT * min (ρ ^ 2 / τ) ρ ≤ (c₀ / (2 * (d : ℝ))) * ρ :=
            mul_le_mul (min_le_right _ _) hm2 hmn (by positivity)
        _ = c₀ * R / 2 := by rw [hR]; field_simp
  -- union over the coordinates
  have hunion : ∑ b ∈ Finset.univ.filter (fun b : Zd d L => ρ ≤ (zdistD d L b : ℝ)), kBA d L g E m τ b
      ≤ ∑ j : Fin d, ∑ b ∈ Finset.univ.filter (fun b : Zd d L => R ≤ (zdist L (b j) : ℝ)),
          kBA d L g E m τ b := by
    have hk := (kBA_basic d L g E m hg hr.1).1 τ hτ.le
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun b _ => ?_
    by_cases hb : ρ ≤ (zdistD d L b : ℝ)
    · simp only [hb, ↓reduceIte]
      have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, hd0⟩, Finset.mem_univ _⟩
      have hsum : ∑ _j : Fin d, R ≤ ∑ j : Fin d, (zdist L (b j) : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hR]
        have : (d : ℝ) * (ρ / d) = ρ := by field_simp
        rw [this]
        have h2 : (zdistD d L b : ℝ) = ∑ j : Fin d, (zdist L (b j) : ℝ) := by
          simp [zdistD]
        rw [← h2]
        exact hb
      obtain ⟨j, _, hj⟩ := Finset.exists_le_of_sum_le hne hsum
      calc kBA d L g E m τ b = (if R ≤ (zdist L (b j) : ℝ) then kBA d L g E m τ b else 0) := by
            simp only [hj, ↓reduceIte]
        _ ≤ ∑ j : Fin d, (if R ≤ (zdist L (b j) : ℝ) then kBA d L g E m τ b else 0) :=
            Finset.single_le_sum (f := fun j : Fin d => if R ≤ (zdist L (b j) : ℝ) then kBA d L g E m τ b else 0)
              (fun j _ => by split_ifs <;> simp [hk b]) (Finset.mem_univ j)
    · simp only [hb, ↓reduceIte]
      exact Finset.sum_nonneg fun j _ => by split_ifs <;> simp [hk b]
  calc ∑ b ∈ Finset.univ.filter (fun b : Zd d L => ρ ≤ (zdistD d L b : ℝ)), kBA d L g E m τ b
      ≤ ∑ j : Fin d, ∑ b ∈ Finset.univ.filter (fun b : Zd d L => R ≤ (zdist L (b j) : ℝ)),
          kBA d L g E m τ b := hunion
    _ ≤ ∑ _j : Fin d, 2 * Real.exp (-(cT * min (ρ ^ 2 / τ) ρ)) := Finset.sum_le_sum fun j _ => hcoord j
    _ = 2 * d * Real.exp (-cT * min (ρ ^ 2 / τ) ρ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, neg_mul]
        ring

/-! ## 6. Target: regime (i) `τ ≤ L²` -/

section Prefactor

private theorem KHeatTail_floor_le {L : ℕ} (hL : 1 ≤ L) (d : ℕ) {τ : ℝ} (hτ : 0 < τ)
    (hτL : τ ≤ (L : ℝ) ^ 2) :
    ((L : ℝ) ^ d)⁻¹ ≤ min 1 (τ ^ (-(d : ℝ) / 2)) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  refine le_min ?_ ?_
  · exact inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
  · have h1 : ((L : ℝ) ^ 2) ^ (-(d : ℝ) / 2) ≤ τ ^ (-(d : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos hτ hτL (by
        have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
        linarith [div_nonneg this (by norm_num : (0 : ℝ) ≤ 2)])
    have h2 : ((L : ℝ) ^ 2) ^ (-(d : ℝ) / 2) = ((L : ℝ) ^ d)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le, ← Real.rpow_natCast, ← Real.rpow_neg hL0.le]
      congr 1
      push_cast
      ring
    rw [← h2]
    exact h1

/-- `min(1, (τ/2)^{-d/2}) ≤ K₂ min(1, τ^{-d/2})` with `K₂ = 2^{d/2} ≥ 1`. -/
private theorem KHeatTail_half_le (d : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    min 1 ((τ / 2) ^ (-(d : ℝ) / 2))
      ≤ ((2 : ℝ) ^ (-(d : ℝ) / 2))⁻¹ * min 1 (τ ^ (-(d : ℝ) / 2)) := by
  set K2 : ℝ := ((2 : ℝ) ^ (-(d : ℝ) / 2))⁻¹ with hK2
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (-(d : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have h2le : (2 : ℝ) ^ (-(d : ℝ) / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by
      have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
      linarith [div_nonneg this (by norm_num : (0 : ℝ) ≤ 2)])
  have hK : 1 ≤ K2 := one_le_inv₀ h2pos |>.mpr h2le
  have hx : (τ / 2) ^ (-(d : ℝ) / 2) = K2 * τ ^ (-(d : ℝ) / 2) := by
    rw [Real.div_rpow hτ.le (by norm_num), hK2]
    ring
  rw [hx, mul_min_of_nonneg _ _ (by linarith : (0 : ℝ) ≤ K2)]
  exact min_le_min hK (le_refl _) |>.trans (by rw [mul_one])

end Prefactor

/-- **Regime (i) `τ ≤ L²`** (twin of `Heat.kProd_le`, `HeatProduct.lean:439`): no floor `L^{-d}`,
Gaussian-then-exponential decay in the torus `ℓ¹` distance. -/
theorem kBA_le : ∀ d : ℕ, 2 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 → ∀ a : Zd d L,
        kBA d L g E m τ a ≤ C * min 1 (τ ^ (-(d : ℝ) / 2))
          * Real.exp (-c * min ((zdistD d L a : ℝ) ^ 2 / τ) (zdistD d L a : ℝ)) := by
  intro d hd Λ κ hΛ hκ
  have hd0 : 0 < d := by omega
  obtain ⟨CD, hCD, hdiag⟩ := kBA_diag_le d hd0 Λ κ hΛ hκ
  obtain ⟨cT, hcT, htail⟩ := BAP_tail_le d hd Λ κ hΛ hκ
  set K2 : ℝ := ((2 : ℝ) ^ (-(d : ℝ) / 2))⁻¹ with hK2
  have hK2pos : 0 < K2 := inv_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  refine ⟨4 * d * (CD * (K2 + 1)), cT / 2, by positivity, by positivity, ?_⟩
  intro L _ hL g E m hg hgΛ hr τ hτ hτL a
  have hτ2 : 0 < τ / 2 := by positivity
  have hk := (kBA_basic d L g E m hg hr.1).1
  set M : ℝ := CD * (K2 + 1) * min 1 (τ ^ (-(d : ℝ) / 2)) with hM
  have hmin0 : 0 ≤ min 1 (τ ^ (-(d : ℝ) / 2)) := le_min zero_le_one (Real.rpow_nonneg hτ.le _)
  have hM0 : 0 ≤ M := by positivity
  -- the sup bound at time τ/2
  have hsup : ∀ b : Zd d L, kBA d L g E m (τ / 2) b ≤ M := by
    intro b
    have h1 := hdiag L hL g E m hg hgΛ hr (τ / 2) hτ2 b
    have h2 := KHeatTail_half_le d hτ
    have h3 := KHeatTail_floor_le (by omega : 1 ≤ L) d hτ hτL
    calc kBA d L g E m (τ / 2) b
        ≤ CD * (min 1 ((τ / 2) ^ (-(d : ℝ) / 2)) + ((L : ℝ) ^ d)⁻¹) := h1
      _ ≤ CD * (K2 * min 1 (τ ^ (-(d : ℝ) / 2)) + min 1 (τ ^ (-(d : ℝ) / 2))) :=
          mul_le_mul_of_nonneg_left (add_le_add h2 h3) hCD.le
      _ = M := by rw [hM]; ring
  -- the semigroup
  have hsg := (BAP_semigroup_shift d L g E m hr.1)
  have hconv : kBA d L g E m τ a
      = ∑ c, kBA d L g E m (τ / 2) c * kBA d L g E m (τ / 2) (a - c) := by
    have hs : (0 : ℝ) ≤ τ / 2 / g ^ 2 := by positivity
    have h1 : τ / g ^ 2 = τ / 2 / g ^ 2 + τ / 2 / g ^ 2 := by ring
    unfold kBA
    rw [h1, hsg.1 _ _ hs hs 0 a]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hsg.2 (τ / 2 / g ^ 2) c a]
  -- splitting
  set r : ℝ := (zdistD d L a : ℝ) with hrdef
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  have hsplit : ∀ c : Zd d L, kBA d L g E m (τ / 2) c * kBA d L g E m (τ / 2) (a - c)
      ≤ (if r / 2 ≤ (zdistD d L c : ℝ) then kBA d L g E m (τ / 2) c * kBA d L g E m (τ / 2) (a - c) else 0)
        + (if r / 2 ≤ (zdistD d L (a - c) : ℝ) then kBA d L g E m (τ / 2) c * kBA d L g E m (τ / 2) (a - c) else 0) := by
    intro c
    have hnn : 0 ≤ kBA d L g E m (τ / 2) c * kBA d L g E m (τ / 2) (a - c) :=
      mul_nonneg (hk _ hτ2.le _) (hk _ hτ2.le _)
    have htri : zdistD d L a ≤ zdistD d L c + zdistD d L (a - c) := by
      have := zdistD_add_le d L c (a - c)
      rwa [add_sub_cancel] at this
    have htri' : r ≤ (zdistD d L c : ℝ) + (zdistD d L (a - c) : ℝ) := by
      rw [hrdef]; exact_mod_cast htri
    by_cases h1 : r / 2 ≤ (zdistD d L c : ℝ)
    · simp only [h1, ↓reduceIte]
      split_ifs <;> linarith
    · have h2 : r / 2 ≤ (zdistD d L (a - c) : ℝ) := by linarith
      simp only [h1, h2, ↓reduceIte]
      linarith
  have hS1 : ∑ c ∈ Finset.univ.filter (fun c : Zd d L => r / 2 ≤ (zdistD d L c : ℝ)),
      kBA d L g E m (τ / 2) c * kBA d L g E m (τ / 2) (a - c)
        ≤ M * (2 * d * Real.exp (-cT * min ((r / 2) ^ 2 / (τ / 2)) (r / 2))) := by
    have ht := htail L hL g E m hg hgΛ hr (τ / 2) hτ2 (r / 2) (by positivity)
    calc ∑ c ∈ Finset.univ.filter (fun c : Zd d L => r / 2 ≤ (zdistD d L c : ℝ)),
          kBA d L g E m (τ / 2) c * kBA d L g E m (τ / 2) (a - c)
        ≤ ∑ c ∈ Finset.univ.filter (fun c : Zd d L => r / 2 ≤ (zdistD d L c : ℝ)),
            M * kBA d L g E m (τ / 2) c :=
          Finset.sum_le_sum fun c _ => by
            have := mul_le_mul_of_nonneg_left (hsup (a - c)) (hk _ hτ2.le c)
            linarith
      _ = M * ∑ c ∈ Finset.univ.filter (fun c : Zd d L => r / 2 ≤ (zdistD d L c : ℝ)),
            kBA d L g E m (τ / 2) c := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left ht hM0
  have hS2 : ∑ c ∈ Finset.univ.filter (fun c : Zd d L => r / 2 ≤ (zdistD d L (a - c) : ℝ)),
      kBA d L g E m (τ / 2) c * kBA d L g E m (τ / 2) (a - c)
        ≤ M * (2 * d * Real.exp (-cT * min ((r / 2) ^ 2 / (τ / 2)) (r / 2))) := by
    have ht := htail L hL g E m hg hgΛ hr (τ / 2) hτ2 (r / 2) (by positivity)
    have hre : ∑ c ∈ Finset.univ.filter (fun c : Zd d L => r / 2 ≤ (zdistD d L (a - c) : ℝ)),
        kBA d L g E m (τ / 2) (a - c)
          = ∑ c ∈ Finset.univ.filter (fun c : Zd d L => r / 2 ≤ (zdistD d L c : ℝ)),
              kBA d L g E m (τ / 2) c := by
      simp only [Finset.sum_filter]
      exact Equiv.sum_comp (Equiv.subLeft a)
        (fun c : Zd d L => if r / 2 ≤ (zdistD d L c : ℝ) then kBA d L g E m (τ / 2) c else 0)
    calc ∑ c ∈ Finset.univ.filter (fun c : Zd d L => r / 2 ≤ (zdistD d L (a - c) : ℝ)),
          kBA d L g E m (τ / 2) c * kBA d L g E m (τ / 2) (a - c)
        ≤ ∑ c ∈ Finset.univ.filter (fun c : Zd d L => r / 2 ≤ (zdistD d L (a - c) : ℝ)),
            M * kBA d L g E m (τ / 2) (a - c) :=
          Finset.sum_le_sum fun c _ => by
            have := mul_le_mul_of_nonneg_right (hsup c) (hk _ hτ2.le (a - c))
            linarith
      _ = M * ∑ c ∈ Finset.univ.filter (fun c : Zd d L => r / 2 ≤ (zdistD d L (a - c) : ℝ)),
            kBA d L g E m (τ / 2) (a - c) := (Finset.mul_sum _ _ _).symm
      _ = M * ∑ c ∈ Finset.univ.filter (fun c : Zd d L => r / 2 ≤ (zdistD d L c : ℝ)),
            kBA d L g E m (τ / 2) c := by rw [hre]
      _ ≤ _ := mul_le_mul_of_nonneg_left ht hM0
  have hexp : min ((r / 2) ^ 2 / (τ / 2)) (r / 2) = (1 / 2) * min (r ^ 2 / τ) r := by
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    congr 1
    · field_simp
    · ring
  calc kBA d L g E m τ a
      = ∑ c, kBA d L g E m (τ / 2) c * kBA d L g E m (τ / 2) (a - c) := hconv
    _ ≤ ∑ c, ((if r / 2 ≤ (zdistD d L c : ℝ) then kBA d L g E m (τ / 2) c * kBA d L g E m (τ / 2) (a - c) else 0)
        + (if r / 2 ≤ (zdistD d L (a - c) : ℝ) then kBA d L g E m (τ / 2) c * kBA d L g E m (τ / 2) (a - c) else 0)) :=
        Finset.sum_le_sum fun c _ => hsplit c
    _ = ∑ c ∈ Finset.univ.filter (fun c : Zd d L => r / 2 ≤ (zdistD d L c : ℝ)),
          kBA d L g E m (τ / 2) c * kBA d L g E m (τ / 2) (a - c)
        + ∑ c ∈ Finset.univ.filter (fun c : Zd d L => r / 2 ≤ (zdistD d L (a - c) : ℝ)),
          kBA d L g E m (τ / 2) c * kBA d L g E m (τ / 2) (a - c) := by
        rw [Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_filter]
    _ ≤ M * (2 * d * Real.exp (-cT * min ((r / 2) ^ 2 / (τ / 2)) (r / 2)))
        + M * (2 * d * Real.exp (-cT * min ((r / 2) ^ 2 / (τ / 2)) (r / 2))) := add_le_add hS1 hS2
    _ = 4 * d * (CD * (K2 + 1)) * min 1 (τ ^ (-(d : ℝ) / 2)) * Real.exp (-(cT / 2) * min (r ^ 2 / τ) r) := by
        rw [hexp, hM]
        have : -cT * (1 / 2 * min (r ^ 2 / τ) r) = -(cT / 2) * min (r ^ 2 / τ) r := by ring
        rw [this]
        ring

/-! ## 7. Compiled nonempty instances (`d = 3`, `L = 4`, `Λ = 10`, `κ = Im m₀`, flow point `P` of `KKernelInst`) -/

namespace KHeatTailInst

open RBM.BA.MFixedPointInst

/-- `zdistD 3 4 (1, 0, 2) = 3` (the point of the instance is at torus `ℓ¹` distance `3`). -/
theorem inst_zdistD : zdistD 3 4 (![1, 0, 2] : Zd 3 4) = 3 := by
  decide

/-- Target `kBA_le` at `τ = 1 ≤ L² = 16`, `a = (1, 0, 2)`, `Λ = 10`, `κ = Im m₀`. -/
theorem inst_kBA_le :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      kBA 3 4 P.g0 P.E P.m0 1 ![1, 0, 2] ≤ C * Real.exp (-c * 3) := by
  obtain ⟨C, c, hC, hc, h⟩ := kBA_le 3 (by norm_num) 10 P.m0.im (by norm_num) P.real.1.1
  refine ⟨C, c, hC, hc, ?_⟩
  have h1 := h 4 (by norm_num) P.g0 P.E P.m0 P.g0_pos P.g0_le P.real 1 one_pos (by norm_num) ![1, 0, 2]
  have h2 : min (((3 : ℕ) : ℝ) ^ 2 / 1) ((3 : ℕ) : ℝ) = 3 := by
    rw [min_eq_right (by norm_num)]
    norm_num
  rw [inst_zdistD, h2] at h1
  simpa using h1

/-- Target `BAP_tail_le` at `τ = 1`, `ρ = 2`: the mass at torus distance `≥ 2`. -/
theorem inst_tail_le :
    ∃ cT : ℝ, 0 < cT ∧
      ∑ b ∈ Finset.univ.filter (fun b : Zd 3 4 => (2 : ℝ) ≤ (zdistD 3 4 b : ℝ)), kBA 3 4 P.g0 P.E P.m0 1 b
        ≤ 2 * ((3 : ℕ) : ℝ) * Real.exp (-cT * min ((2 : ℝ) ^ 2 / 1) 2) := by
  obtain ⟨cT, hcT, h⟩ := BAP_tail_le 3 (by norm_num) 10 P.m0.im (by norm_num) P.real.1.1
  exact ⟨cT, hcT, h 4 (by norm_num) P.g0 P.E P.m0 P.g0_pos P.g0_le P.real 1 one_pos 2 (by norm_num)⟩

end KHeatTailInst

end RBM.BA

end
