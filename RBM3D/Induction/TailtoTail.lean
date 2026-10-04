/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step5Pins
import RBM3D.Kernel.Evolution
import RBM3D.Evolution.Pins
import RBM3D.Propagator.Props4

/-!
# S5-04 (ST-4): `TailtoTail`, `(neiwuj)` (`3_5:2344-2362`)

The deterministic lemma `STTailtoTail` (`Induction/Step5Pins.lean:121`) for `3 ≤ d`: for
`0 ≤ s ≤ t < 1`, `ilambda² ≤ 1 - t`, `|m| = 1`, every `σ ∈ {±}²` and every `A` with
`|A_b| ≤ T_{s,D}(|b₁-b₂|)`,
`|(𝒰^{(2)}_{s,t,σ} ∘ A)_a| ≤ C T_{t,D}(|a₁-a₂|) + ((1-s)/(1-t))² W^{-D}`,
with `C = (3 e^{(4d+1)/4})²`.

Route (arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex:2344-2362`, with the independent check
`docs/claude-team/fable/2026-10-04-tailtotail.md` §2; the Neumann step is done by a weighted
row-sum bound instead of the pointwise bound `(1-t)Θ_t(0,x) ≤ q^{|x|₁}`):

* `(1 - sμS) Θ_{tμ} = 1 + (t-s) μ S Θ_{tμ}` (`uKer_eq_one_add`), so by property 4
  (`norm_Theta_apply_le`) the entries of the one-index kernel are dominated by
  `1_{a=b} + (t-s) (S Θ_t)(a,b)`, with `Θ_t ≥ 0`;
* the weight `w(x) = e^{c|x|_∞}`, `c = 1/(4d+1)`: `Σ_x S(x) w(x) ≤ 1 + g²/2`
  (`e^c - 1 ≤ 1/(4d)`), the resolvent identity `Θ = 1 + t Θ S` and
  `w(a-b) ≤ w(a-y) w(y-b)` give `Σ_b Θ_t(a,b) w(a-b) ≤ 2/(1-t)` when `g² ≤ 1 - t`;
* so `Σ_b |K(a,b)| e^{√|a-b|} ≤ 3 e^{(4d+1)/4} ρ`, `ρ = (1-s)/(1-t)`
  (`√r ≤ c r + 1/(4c)`);
* `√|a₁-a₂| ≤ √|a₁-b₁| + √|b₁-b₂| + √|b₂-a₂|` splits the double sum, and
  `ρ² (W^d (1-s))^{-2} = (W^d (1-t))^{-2}` converts the amplitude.

Registry (DECISIONS §16, §20): `STTailtoTail` is proved here (`stTailtoTail_holds`).
-/

set_option linter.style.longLine false

namespace RBM.Gauss.Sizes

open RBM RBM.Gauss

/-! ### 1. The `L^∞` weight -/

section Weight

variable {d L : ℕ} [NeZero L]

private theorem tailtoTail_zdistInf_add_le (x y : Zd d L) :
    zdistInf d L (x + y) ≤ zdistInf d L x + zdistInf d L y := by
  unfold zdistInf
  refine Finset.sup_le fun i _ => ?_
  calc zdist L ((x + y) i) = zdist L (x i + y i) := rfl
    _ ≤ zdist L (x i) + zdist L (y i) := zdist_add_le L (x i) (y i)
    _ ≤ _ := Nat.add_le_add
        (Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i))
        (Finset.le_sup (f := fun j => zdist L (y j)) (Finset.mem_univ i))

omit [NeZero L] in
private theorem tailtoTail_zdistInf_zero : zdistInf d L (0 : Zd d L) = 0 := by
  unfold zdistInf
  simp

/-- three-point triangle inequality for `zdistInf` -/
private theorem tailtoTail_zdistInf_tri (a y b : Zd d L) :
    zdistInf d L (a - b) ≤ zdistInf d L (a - y) + zdistInf d L (y - b) := by
  have := tailtoTail_zdistInf_add_le (a - y) (y - b)
  rwa [sub_add_sub_cancel] at this

/-- the weight `w(x) = e^{c |x|_∞}` -/
private noncomputable def tailtoTail_wt (d L : ℕ) (c : ℝ) (x : Zd d L) : ℝ :=
  Real.exp (c * (zdistInf d L x : ℝ))

omit [NeZero L] in
private theorem tailtoTail_wt_pos (c : ℝ) (x : Zd d L) : 0 < tailtoTail_wt d L c x :=
  Real.exp_pos _

omit [NeZero L] in
private theorem tailtoTail_wt_zero (c : ℝ) : tailtoTail_wt d L c 0 = 1 := by
  simp [tailtoTail_wt, tailtoTail_zdistInf_zero]

private theorem tailtoTail_wt_sub_le {c : ℝ} (hc : 0 ≤ c) (a y b : Zd d L) :
    tailtoTail_wt d L c (a - b) ≤ tailtoTail_wt d L c (a - y) * tailtoTail_wt d L c (y - b) := by
  unfold tailtoTail_wt
  rw [← Real.exp_add, ← mul_add]
  refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ hc)
  exact_mod_cast tailtoTail_zdistInf_tri a y b

/-- `Σ_x S(x) w(x) ≤ 1 + g²/2` when `e^c - 1 ≤ 1/(4d)`: the `2d` neighbours have `|x|_∞ ≤ |x|₁ = 1`. -/
private theorem tailtoTail_sum_s_wt (hL : 3 ≤ L) (g : ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hec : (d : ℝ) * (Real.exp c - 1) ≤ 1 / 4) :
    ∑ x : Zd d L, sbKernelR d L g x * tailtoTail_wt d L c x ≤ 1 + g ^ 2 / 2 := by
  set a : ℝ := (1 + 2 * (d : ℝ) * g ^ 2)⁻¹ with ha
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hpos : 0 < 1 + 2 * (d : ℝ) * g ^ 2 := by positivity
  have ha0 : 0 < a := inv_pos.mpr hpos
  have ha1 : a ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg g])
  have hpt : ∀ x : Zd d L, sbKernelR d L g x * tailtoTail_wt d L c x ≤
      sbKernelR d L g x + (if zdistD d L x = 1 then g ^ 2 * a * (Real.exp c - 1) else 0) := by
    intro x
    by_cases h0 : x = 0
    · subst h0
      simp [sbKernelR, tailtoTail_wt_zero, ← ha]
    · by_cases h1 : zdistD d L x = 1
      · have hw : tailtoTail_wt d L c x ≤ Real.exp c := by
          unfold tailtoTail_wt
          refine Real.exp_le_exp.mpr ?_
          have : (zdistInf d L x : ℝ) ≤ 1 := by
            have := zdistInf_le_zdistD d L x
            rw [h1] at this
            exact_mod_cast this
          nlinarith
        simp only [sbKernelR, h0, h1, ite_true, ite_false, zero_add]
        have : 0 ≤ g ^ 2 * a := by positivity
        nlinarith
      · simp [sbKernelR, h0, h1]
  calc ∑ x : Zd d L, sbKernelR d L g x * tailtoTail_wt d L c x
      ≤ ∑ x : Zd d L, (sbKernelR d L g x +
          (if zdistD d L x = 1 then g ^ 2 * a * (Real.exp c - 1) else 0)) :=
        Finset.sum_le_sum fun x _ => hpt x
    _ = 1 + 2 * (d : ℝ) * (g ^ 2 * a * (Real.exp c - 1)) := by
        rw [Finset.sum_add_distrib, sum_sbKernelR d L g hL, ← Finset.sum_filter, Finset.sum_const,
          card_nbhd d L hL, nsmul_eq_mul]
        push_cast; ring
    _ ≤ 1 + g ^ 2 / 2 := by
        have h1 : 2 * (d : ℝ) * (g ^ 2 * a * (Real.exp c - 1))
            = 2 * (g ^ 2 * a) * ((d : ℝ) * (Real.exp c - 1)) := by ring
        have h2 : 2 * (g ^ 2 * a) * ((d : ℝ) * (Real.exp c - 1)) ≤ 2 * (g ^ 2 * a) * (1 / 4) :=
          mul_le_mul_of_nonneg_left hec (by positivity)
        have h3 : g ^ 2 * a ≤ g ^ 2 := by nlinarith [sq_nonneg g]
        nlinarith

end Weight

/-! ### 2. The resolvent identity and the weighted row sum of `Θ_t` -/

section Theta

variable {d L : ℕ} [NeZero L] {g : ℝ}

/-- `Θ_t = 1 + t Θ_t S` entrywise, for the (real, nonnegative) entries of `Θ_t^{(+,-)}`. -/
private theorem tailtoTail_theta_eq (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (a b : Zd d L) :
    (Theta d L g t a b).re = (if a = b then 1 else 0) +
      t * ∑ y, (Theta d L g t a y).re * sbKernelR d L g (y - b) := by
  have hξ : ‖(t : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_of_nonneg ht0]
  have h := congrFun (congrFun (Theta_mul_of_three_le (d := d) (L := L) (g := g) hL hξ) a) b
  simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, SB_apply,
    sbKernel_eq_ofReal, smul_eq_mul] at h
  have hr : ∀ y, Theta d L g (t : ℂ) a y = (((Theta d L g (t : ℂ) a y).re : ℝ) : ℂ) :=
    fun y => Theta_real_eq hL ht0 ht1 a y
  have h2 : (((∑ y, (Theta d L g (t : ℂ) a y).re *
        ((if y = b then 1 else 0) - t * sbKernelR d L g (y - b)) : ℝ)) : ℂ) =
      (((if a = b then 1 else 0 : ℝ)) : ℂ) := by
    have hc : (((if a = b then (1 : ℝ) else 0 : ℝ)) : ℂ) = if a = b then 1 else 0 := by
      split_ifs <;> simp
    rw [hc, ← h]
    push_cast
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← hr y]
    by_cases hy : y = b <;> simp [hy]
  have h3 := Complex.ofReal_injective h2
  simp only [mul_sub, Finset.sum_sub_distrib] at h3
  have h4 : ∑ y, (Theta d L g (t : ℂ) a y).re * (if y = b then (1 : ℝ) else 0)
      = (Theta d L g (t : ℂ) a b).re := by
    simp
  have h5 : ∑ y, (Theta d L g (t : ℂ) a y).re * (t * sbKernelR d L g (y - b))
      = t * ∑ y, (Theta d L g (t : ℂ) a y).re * sbKernelR d L g (y - b) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [h4, h5] at h3
  linarith

/-- `Σ_b Θ_t(a,b) w(a-b) ≤ 2/(1-t)` for `g² ≤ 1 - t`: from `Θ = 1 + tΘS`, `w(a-b) ≤ w(a-y) w(y-b)` and
`Σ_x S(x) w(x) ≤ 1 + g²/2`. -/
private theorem tailtoTail_theta_wt (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {c : ℝ} (hc : 0 ≤ c) (hec : (d : ℝ) * (Real.exp c - 1) ≤ 1 / 4) (hgt : g ^ 2 ≤ 1 - t)
    (a : Zd d L) :
    ∑ b, (Theta d L g t a b).re * tailtoTail_wt d L c (a - b) ≤ 2 / (1 - t) := by
  set F : ℝ := ∑ b, (Theta d L g t a b).re * tailtoTail_wt d L c (a - b) with hF
  have hθ0 : ∀ y, 0 ≤ (Theta d L g t a y).re := fun y => Theta_real_nonneg hL ht0 ht1 a y
  have hF0 : 0 ≤ F := Finset.sum_nonneg fun b _ =>
    mul_nonneg (hθ0 b) (tailtoTail_wt_pos c _).le
  have hlam := tailtoTail_sum_s_wt (d := d) (L := L) hL g hc hec
  have hconv : ∀ y : Zd d L, ∑ b, sbKernelR d L g (y - b) * tailtoTail_wt d L c (y - b) =
      ∑ x : Zd d L, sbKernelR d L g x * tailtoTail_wt d L c x := fun y =>
    Fintype.sum_equiv (Equiv.subLeft y) _ _ fun b => rfl
  have h1 : F ≤ 1 + t * ((1 + g ^ 2 / 2) * F) := by
    have e1 : F = 1 + t * ∑ b, ∑ y, (Theta d L g t a y).re * sbKernelR d L g (y - b) *
        tailtoTail_wt d L c (a - b) := by
      rw [hF]
      have : ∀ b : Zd d L, (Theta d L g t a b).re * tailtoTail_wt d L c (a - b) =
          (if a = b then tailtoTail_wt d L c (a - b) else 0) +
          t * ∑ y, (Theta d L g t a y).re * sbKernelR d L g (y - b) * tailtoTail_wt d L c (a - b) := by
        intro b
        rw [tailtoTail_theta_eq hL ht0 ht1 a b, add_mul, mul_assoc, Finset.sum_mul]
        by_cases hab : a = b <;> simp [hab, Finset.mul_sum]
      rw [Finset.sum_congr rfl fun b _ => this b, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [tailtoTail_wt_zero]
    have e2 : ∑ b, ∑ y, (Theta d L g t a y).re * sbKernelR d L g (y - b) *
        tailtoTail_wt d L c (a - b) ≤ (1 + g ^ 2 / 2) * F := by
      rw [Finset.sum_comm, hF, Finset.mul_sum]
      refine Finset.sum_le_sum fun y _ => ?_
      calc ∑ b, (Theta d L g t a y).re * sbKernelR d L g (y - b) * tailtoTail_wt d L c (a - b)
          ≤ ∑ b, (Theta d L g t a y).re * tailtoTail_wt d L c (a - y) *
              (sbKernelR d L g (y - b) * tailtoTail_wt d L c (y - b)) := by
            refine Finset.sum_le_sum fun b _ => ?_
            have hs := sbKernelR_nonneg d L g (y - b)
            have := tailtoTail_wt_sub_le hc a y b
            have h0 := hθ0 y
            calc (Theta d L g t a y).re * sbKernelR d L g (y - b) * tailtoTail_wt d L c (a - b)
                = (Theta d L g t a y).re * sbKernelR d L g (y - b) * tailtoTail_wt d L c (a - b) := rfl
              _ ≤ (Theta d L g t a y).re * sbKernelR d L g (y - b) *
                    (tailtoTail_wt d L c (a - y) * tailtoTail_wt d L c (y - b)) :=
                  mul_le_mul_of_nonneg_left this (mul_nonneg h0 hs)
              _ = _ := by ring
        _ = (Theta d L g t a y).re * tailtoTail_wt d L c (a - y) *
              ∑ b, sbKernelR d L g (y - b) * tailtoTail_wt d L c (y - b) := by
            rw [Finset.mul_sum]
        _ ≤ (Theta d L g t a y).re * tailtoTail_wt d L c (a - y) * (1 + g ^ 2 / 2) := by
            rw [hconv y]
            exact mul_le_mul_of_nonneg_left hlam
              (mul_nonneg (hθ0 y) (tailtoTail_wt_pos c _).le)
        _ = (1 + g ^ 2 / 2) * ((Theta d L g t a y).re * tailtoTail_wt d L c (a - y)) := by ring
    calc F = 1 + t * ∑ b, ∑ y, (Theta d L g t a y).re * sbKernelR d L g (y - b) *
          tailtoTail_wt d L c (a - b) := e1
      _ ≤ 1 + t * ((1 + g ^ 2 / 2) * F) := by
          have := mul_le_mul_of_nonneg_left e2 ht0
          linarith
  have h2 : (1 - t) / 2 * F ≤ 1 := by
    have : t * (g ^ 2 / 2) ≤ (1 - t) / 2 := by nlinarith [sq_nonneg g]
    nlinarith
  have h3 : 0 < 1 - t := by linarith
  rw [le_div_iff₀ h3]
  nlinarith

end Theta

/-! ### 3. The one-index kernel `(1 - sμS)Θ_{tμ}` -/

section Kernel

variable {d L : ℕ} [NeZero L] {g : ℝ}

/-- the entries of `(1 - sμS)Θ_{tμ} = 1 + (t-s)μ S Θ_{tμ}` are dominated by `1_{a=b} + (t-s)(SΘ_t)(a,b)`. -/
private theorem tailtoTail_ker_entry (hL : 3 ≤ L) {μ : ℂ} (hμ : ‖μ‖ = 1) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht1 : t < 1) (a b : Zd d L) :
    ‖uKer d L g μ s t a b‖ ≤ (if a = b then 1 else 0) +
      (t - s) * ∑ y, sbKernelR d L g (a - y) * (Theta d L g t y b).re := by
  have ht0 : 0 ≤ t := hs.trans hst
  have hξ : ‖(t : ℂ) * μ‖ < 1 := norm_t_mul_lt_one ht0 ht1 hμ
  rw [uKer_eq_one_add hL hξ]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.mul_apply, SB_apply,
    sbKernel_eq_ofReal, smul_eq_mul]
  refine (norm_add_le _ _).trans ?_
  refine add_le_add (by by_cases hab : a = b <;> simp [hab]) ?_
  rw [norm_mul]
  have hc : ‖((t : ℂ) - s) * μ‖ = t - s := by
    rw [norm_mul, hμ, mul_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  rw [hc]
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sbKernelR_nonneg d L g _)]
  exact mul_le_mul_of_nonneg_left (norm_Theta_apply_le hL ht0 ht1 hμ y b)
    (sbKernelR_nonneg d L g _)

/-- `Σ_b |K(a,b)| w(a-b) ≤ 3ρ` for the one-index kernel `K = (1 - sμS)Θ_{tμ}`, `ρ = (1-s)/(1-t)`. -/
private theorem tailtoTail_ker_wt (hL : 3 ≤ L) {μ : ℂ} (hμ : ‖μ‖ = 1) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht1 : t < 1) {c : ℝ} (hc : 0 ≤ c) (hec : (d : ℝ) * (Real.exp c - 1) ≤ 1 / 4)
    (hgt : g ^ 2 ≤ 1 - t) (a : Zd d L) :
    ∑ b, ‖uKer d L g μ s t a b‖ * tailtoTail_wt d L c (a - b) ≤ 3 * ((1 - s) / (1 - t)) := by
  have ht0 : 0 ≤ t := hs.trans hst
  have h3 : 0 < 1 - t := by linarith
  have hlam := tailtoTail_sum_s_wt (d := d) (L := L) hL g hc hec
  have hconv : ∑ y, sbKernelR d L g (a - y) * tailtoTail_wt d L c (a - y) =
      ∑ x : Zd d L, sbKernelR d L g x * tailtoTail_wt d L c x :=
    Fintype.sum_equiv (Equiv.subLeft a) _ _ fun b => rfl
  have hθ0 : ∀ y b, 0 ≤ (Theta d L g t y b).re := fun y b => Theta_real_nonneg hL ht0 ht1 y b
  -- the double sum
  have hdbl : ∑ b, ∑ y, sbKernelR d L g (a - y) * (Theta d L g t y b).re * tailtoTail_wt d L c (a - b)
      ≤ (1 + g ^ 2 / 2) * (2 / (1 - t)) := by
    rw [Finset.sum_comm]
    calc ∑ y, ∑ b, sbKernelR d L g (a - y) * (Theta d L g t y b).re * tailtoTail_wt d L c (a - b)
        ≤ ∑ y, sbKernelR d L g (a - y) * tailtoTail_wt d L c (a - y) * (2 / (1 - t)) := by
          refine Finset.sum_le_sum fun y _ => ?_
          calc ∑ b, sbKernelR d L g (a - y) * (Theta d L g t y b).re * tailtoTail_wt d L c (a - b)
              ≤ ∑ b, sbKernelR d L g (a - y) * tailtoTail_wt d L c (a - y) *
                  ((Theta d L g t y b).re * tailtoTail_wt d L c (y - b)) := by
                refine Finset.sum_le_sum fun b _ => ?_
                have hs0 := sbKernelR_nonneg d L g (a - y)
                have := tailtoTail_wt_sub_le hc a y b
                calc sbKernelR d L g (a - y) * (Theta d L g t y b).re * tailtoTail_wt d L c (a - b)
                    ≤ sbKernelR d L g (a - y) * (Theta d L g t y b).re *
                        (tailtoTail_wt d L c (a - y) * tailtoTail_wt d L c (y - b)) :=
                      mul_le_mul_of_nonneg_left this (mul_nonneg hs0 (hθ0 y b))
                  _ = _ := by ring
            _ = sbKernelR d L g (a - y) * tailtoTail_wt d L c (a - y) *
                  ∑ b, (Theta d L g t y b).re * tailtoTail_wt d L c (y - b) := by
                rw [Finset.mul_sum]
            _ ≤ sbKernelR d L g (a - y) * tailtoTail_wt d L c (a - y) * (2 / (1 - t)) :=
                mul_le_mul_of_nonneg_left
                  (tailtoTail_theta_wt hL ht0 ht1 hc hec hgt y)
                  (mul_nonneg (sbKernelR_nonneg d L g _) (tailtoTail_wt_pos c _).le)
      _ = (∑ y, sbKernelR d L g (a - y) * tailtoTail_wt d L c (a - y)) * (2 / (1 - t)) := by
          rw [Finset.sum_mul]
      _ ≤ (1 + g ^ 2 / 2) * (2 / (1 - t)) := by
          rw [hconv]
          exact mul_le_mul_of_nonneg_right hlam (by positivity)
  calc ∑ b, ‖uKer d L g μ s t a b‖ * tailtoTail_wt d L c (a - b)
      ≤ ∑ b, ((if a = b then tailtoTail_wt d L c (a - b) else 0) +
          (t - s) * ∑ y, sbKernelR d L g (a - y) * (Theta d L g t y b).re *
            tailtoTail_wt d L c (a - b)) := by
        refine Finset.sum_le_sum fun b _ => ?_
        have := mul_le_mul_of_nonneg_right (tailtoTail_ker_entry (g := g) hL hμ hs hst ht1 a b)
          (tailtoTail_wt_pos c (a - b)).le
        refine this.trans (le_of_eq ?_)
        rw [add_mul, mul_assoc, Finset.sum_mul]
        by_cases hab : a = b <;> simp [hab]
    _ = 1 + (t - s) * ∑ b, ∑ y, sbKernelR d L g (a - y) * (Theta d L g t y b).re *
          tailtoTail_wt d L c (a - b) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp [tailtoTail_wt_zero]
    _ ≤ 1 + (t - s) * ((1 + g ^ 2 / 2) * (2 / (1 - t))) := by
        have := mul_le_mul_of_nonneg_left hdbl (sub_nonneg.mpr hst)
        linarith
    _ ≤ 3 * ((1 - s) / (1 - t)) := by
        have hg1 : g ^ 2 / 2 ≤ 1 / 2 := by linarith
        have hts : 0 ≤ (t - s) / (1 - t) := div_nonneg (sub_nonneg.mpr hst) h3.le
        have e : 1 + (t - s) * ((1 + g ^ 2 / 2) * (2 / (1 - t)))
            = 1 + (1 + g ^ 2 / 2) * 2 * ((t - s) / (1 - t)) := by
          field_simp
        have e2 : 3 * ((1 - s) / (1 - t)) = 3 + 3 * ((t - s) / (1 - t)) := by
          field_simp; ring
        rw [e, e2]
        nlinarith

end Kernel

/-! ### 4. The weights `e^{√r}` -/

section Sqrt

variable {d L : ℕ} [NeZero L]

private theorem tailtoTail_hec (hd : 1 ≤ d) :
    (d : ℝ) * (Real.exp (1 / (4 * (d : ℝ) + 1)) - 1) ≤ 1 / 4 := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hK : (0 : ℝ) < 4 * d + 1 := by linarith
  set c : ℝ := 1 / (4 * (d : ℝ) + 1) with hc
  have hc1 : c < 1 := by
    rw [hc, div_lt_one hK]; linarith
  have h1 := Real.add_one_le_exp (-c)
  have h2 : Real.exp c * Real.exp (-c) = 1 := by rw [← Real.exp_add]; simp
  have h3 : Real.exp c * (1 - c) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos c).le
    nlinarith
  have h4 : (1 - c) = 4 * d / (4 * d + 1) := by
    rw [hc]; field_simp; ring
  rw [h4] at h3
  have h5 : Real.exp c * (4 * d) ≤ 4 * d + 1 := by
    have := mul_le_mul_of_nonneg_right h3 hK.le
    have e : Real.exp c * (4 * d / (4 * d + 1)) * (4 * d + 1) = Real.exp c * (4 * d) := by
      field_simp
    linarith
  nlinarith

private theorem tailtoTail_sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

omit [NeZero L] in
private theorem tailtoTail_exp_sqrt_le (hd : 1 ≤ d) (x : Zd d L) :
    Real.exp (Real.sqrt (zdistInf d L x : ℝ)) ≤
      Real.exp ((4 * (d : ℝ) + 1) / 4) * tailtoTail_wt d L (1 / (4 * (d : ℝ) + 1)) x := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hK : (0 : ℝ) < 4 * d + 1 := by linarith
  unfold tailtoTail_wt
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  set r : ℝ := (zdistInf d L x : ℝ) with hr
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  set u := Real.sqrt r with hu
  have hu2 : u ^ 2 = r := Real.sq_sqrt hr0
  have : (4 * (d : ℝ) + 1) / 4 + 1 / (4 * d + 1) * r - u = (u - (4 * d + 1) / 2) ^ 2 / (4 * d + 1) := by
    rw [← hu2]; field_simp; ring
  have h2 : 0 ≤ (u - (4 * (d : ℝ) + 1) / 2) ^ 2 / (4 * d + 1) := by positivity
  linarith

/-- `Σ_b |K(a,b)| e^{√|a-b|} ≤ 3 e^{(4d+1)/4} ρ` for the one-index kernel. -/
private theorem tailtoTail_ker_exp (hL : 3 ≤ L) (hd : 1 ≤ d) {g : ℝ} {μ : ℂ} (hμ : ‖μ‖ = 1)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht1 : t < 1) (hgt : g ^ 2 ≤ 1 - t) (a : Zd d L) :
    ∑ b, ‖uKer d L g μ s t a b‖ * Real.exp (Real.sqrt (zdistInf d L (a - b) : ℝ)) ≤
      3 * Real.exp ((4 * (d : ℝ) + 1) / 4) * ((1 - s) / (1 - t)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hK : (0 : ℝ) < 4 * d + 1 := by linarith
  have hc0 : (0 : ℝ) ≤ 1 / (4 * (d : ℝ) + 1) := by positivity
  have hw := tailtoTail_ker_wt (g := g) hL hμ hs hst ht1 hc0 (tailtoTail_hec hd) hgt a
  calc ∑ b, ‖uKer d L g μ s t a b‖ * Real.exp (Real.sqrt (zdistInf d L (a - b) : ℝ))
      ≤ ∑ b, Real.exp ((4 * (d : ℝ) + 1) / 4) *
          (‖uKer d L g μ s t a b‖ * tailtoTail_wt d L (1 / (4 * (d : ℝ) + 1)) (a - b)) := by
        refine Finset.sum_le_sum fun b _ => ?_
        have := mul_le_mul_of_nonneg_left (tailtoTail_exp_sqrt_le hd (a - b)) (norm_nonneg (uKer d L g μ s t a b))
        linarith
    _ = Real.exp ((4 * (d : ℝ) + 1) / 4) *
          ∑ b, ‖uKer d L g μ s t a b‖ * tailtoTail_wt d L (1 / (4 * (d : ℝ) + 1)) (a - b) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp ((4 * (d : ℝ) + 1) / 4) * (3 * ((1 - s) / (1 - t))) :=
        mul_le_mul_of_nonneg_left hw (Real.exp_pos _).le
    _ = 3 * Real.exp ((4 * (d : ℝ) + 1) / 4) * ((1 - s) / (1 - t)) := by ring

/-- the row sums of the one-index kernel: `Σ_b |K(a,b)| ≤ ρ` (`norm_uKer_le`). -/
private theorem tailtoTail_ker_row (hL : 3 ≤ L) {g : ℝ} {μ : ℂ} (hμ : ‖μ‖ = 1)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht1 : t < 1) (a : Zd d L) :
    ∑ b, ‖uKer d L g μ s t a b‖ ≤ (1 - s) / (1 - t) :=
  (sum_norm_row_le _ a).trans (norm_uKer_le hL hs hst ht1 hμ)

private theorem tailtoTail_zdistInf_neg (x : Zd d L) :
    zdistInf d L (-x) = zdistInf d L x := by
  unfold zdistInf
  exact Finset.sup_congr rfl fun i _ => by simp [zdist_neg]

/-- `√|a₀-a₁| ≤ √|a₀-b₀| + √|b₀-b₁| + √|b₁-a₁|`, in exponential form. -/
private theorem tailtoTail_exp_tri (a0 a1 b0 b1 : Zd d L) :
    Real.exp (-Real.sqrt (zdistInf d L (b0 - b1) : ℝ)) ≤
      Real.exp (-Real.sqrt (zdistInf d L (a0 - a1) : ℝ)) *
        (Real.exp (Real.sqrt (zdistInf d L (a0 - b0) : ℝ)) *
          Real.exp (Real.sqrt (zdistInf d L (a1 - b1) : ℝ))) := by
  rw [← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h1 : zdistInf d L (a0 - a1) ≤
      zdistInf d L (a0 - b0) + zdistInf d L (b0 - b1) + zdistInf d L (a1 - b1) := by
    have e1 := tailtoTail_zdistInf_tri a0 b0 a1
    have e2 := tailtoTail_zdistInf_tri b0 b1 a1
    have e3 : zdistInf d L (b1 - a1) = zdistInf d L (a1 - b1) := by
      rw [← neg_sub a1 b1]; exact tailtoTail_zdistInf_neg _
    omega
  have h2 : ((zdistInf d L (a0 - a1) : ℕ) : ℝ) ≤
      (zdistInf d L (a0 - b0) : ℝ) + (zdistInf d L (b0 - b1) : ℝ) + (zdistInf d L (a1 - b1) : ℝ) := by
    exact_mod_cast h1
  have h3 := Real.sqrt_le_sqrt h2
  have h4 := tailtoTail_sqrt_add_le (x := (zdistInf d L (a0 - b0) : ℝ) + (zdistInf d L (b0 - b1) : ℝ))
    (y := (zdistInf d L (a1 - b1) : ℝ)) (by positivity) (by positivity)
  have h5 := tailtoTail_sqrt_add_le (x := (zdistInf d L (a0 - b0) : ℝ)) (y := (zdistInf d L (b0 - b1) : ℝ))
    (by positivity) (by positivity)
  linarith

end Sqrt

/-! ### 5. `TailtoTail` -/

section Main

variable {d L : ℕ} [NeZero L]

/-- `(neiwuj)` at a fixed `a`, with the constant `(3 e^{(4d+1)/4})²`. -/
private theorem tailtoTail_main (hL : 3 ≤ L) (hd : 1 ≤ d) {g W D s t : ℝ} (hW : 0 < W) (hs : 0 ≤ s)
    (hst : s ≤ t) (ht1 : t < 1) (hgt : g ^ 2 ≤ 1 - t) {m : ℂ} (hm : ‖m‖ = 1) (σ : Fin 2 → Bool)
    (A : (Fin 2 → Zd d L) → ℂ)
    (hA : ∀ b, ‖A b‖ ≤ tailTD d W s D (zdistInf d L (b 0 - b 1) : ℝ)) (a : Fin 2 → Zd d L) :
    ‖UN d L g (EKsgn m σ) s t A a‖ ≤
      (3 * Real.exp ((4 * (d : ℝ) + 1) / 4)) ^ 2 * tailTD d W t D (zdistInf d L (a 0 - a 1) : ℝ) +
        ((1 - s) / (1 - t)) ^ 2 * W ^ (-D) := by
  have ht0 : 0 ≤ t := hs.trans hst
  have h1t : 0 < 1 - t := by linarith
  have h1s : 0 < 1 - s := by linarith
  have hμ : ∀ i, ‖cycProd (EKsgn m σ) i‖ = 1 := fun i =>
    norm_cycProd (fun j => ek_norm_spin hm (σ j)) i
  set ρ : ℝ := (1 - s) / (1 - t) with hρ
  set E : ℝ := Real.exp ((4 * (d : ℝ) + 1) / 4) with hE
  set K : Fin 2 → Matrix (Zd d L) (Zd d L) ℂ := fun i => uKer d L g (cycProd (EKsgn m σ) i) s t with hK
  set WD : ℝ := W ^ (-D) with hWD
  have hWD0 : 0 ≤ WD := Real.rpow_nonneg hW.le _
  set α : ℝ := ((W ^ d * |1 - s|)⁻¹) ^ 2 with hα
  set α' : ℝ := α * Real.exp (-Real.sqrt (zdistInf d L (a 0 - a 1) : ℝ)) with hα'
  have hα0 : 0 ≤ α := by positivity
  have hα'0 : 0 ≤ α' := by positivity
  -- row sums
  have hR : ∀ i, ∑ b, ‖K i (a i) b‖ ≤ ρ := fun i =>
    tailtoTail_ker_row hL (hμ i) hs hst ht1 (a i)
  have hX : ∀ i, ∑ b, ‖K i (a i) b‖ * Real.exp (Real.sqrt (zdistInf d L (a i - b) : ℝ)) ≤ 3 * E * ρ :=
    fun i => tailtoTail_ker_exp hL hd (hμ i) hs hst ht1 hgt (a i)
  -- reduction to a double sum
  have hsum2 : ∀ F : Zd d L → Zd d L → ℝ,
      ∑ b : Fin 2 → Zd d L, F (b 0) (b 1) = ∑ b0, ∑ b1, F b0 b1 := by
    intro F
    rw [← Fintype.sum_prod_type']
    exact Fintype.sum_equiv (piFinTwoEquiv fun _ => Zd d L) _ _ (fun b => rfl)
  set F : Zd d L → Zd d L → ℝ := fun b0 b1 =>
    ‖K 0 (a 0) b0‖ * ‖K 1 (a 1) b1‖ * tailTD d W s D (zdistInf d L (b0 - b1) : ℝ) with hF
  have hstep1 : ‖UN d L g (EKsgn m σ) s t A a‖ ≤ ∑ b : Fin 2 → Zd d L, F (b 0) (b 1) := by
    unfold UN
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [norm_mul, norm_prod, Fin.prod_univ_two]
    exact mul_le_mul_of_nonneg_left (hA b) (by positivity)
  have hpt : ∀ b0 b1, F b0 b1 ≤
      α' * ((‖K 0 (a 0) b0‖ * Real.exp (Real.sqrt (zdistInf d L (a 0 - b0) : ℝ))) *
        (‖K 1 (a 1) b1‖ * Real.exp (Real.sqrt (zdistInf d L (a 1 - b1) : ℝ)))) +
      WD * (‖K 0 (a 0) b0‖ * ‖K 1 (a 1) b1‖) := by
    intro b0 b1
    have hq0 := norm_nonneg (K 0 (a 0) b0)
    have hq1 := norm_nonneg (K 1 (a 1) b1)
    have htri := tailtoTail_exp_tri (a 0) (a 1) b0 b1
    have habs : |1 - s| = 1 - s := abs_of_pos h1s
    have hT : tailTD d W s D (zdistInf d L (b0 - b1) : ℝ) =
        α * Real.exp (-Real.sqrt (zdistInf d L (b0 - b1) : ℝ)) + WD := rfl
    simp only [hF]
    rw [hT]
    have h2 : α * Real.exp (-Real.sqrt (zdistInf d L (b0 - b1) : ℝ)) ≤
        α' * (Real.exp (Real.sqrt (zdistInf d L (a 0 - b0) : ℝ)) *
          Real.exp (Real.sqrt (zdistInf d L (a 1 - b1) : ℝ))) := by
      rw [hα', mul_assoc]
      exact mul_le_mul_of_nonneg_left htri hα0
    have h3 : 0 ≤ ‖K 0 (a 0) b0‖ * ‖K 1 (a 1) b1‖ := mul_nonneg hq0 hq1
    calc ‖K 0 (a 0) b0‖ * ‖K 1 (a 1) b1‖ *
          (α * Real.exp (-Real.sqrt (zdistInf d L (b0 - b1) : ℝ)) + WD)
        = (‖K 0 (a 0) b0‖ * ‖K 1 (a 1) b1‖) *
            (α * Real.exp (-Real.sqrt (zdistInf d L (b0 - b1) : ℝ))) +
          WD * (‖K 0 (a 0) b0‖ * ‖K 1 (a 1) b1‖) := by ring
      _ ≤ (‖K 0 (a 0) b0‖ * ‖K 1 (a 1) b1‖) *
            (α' * (Real.exp (Real.sqrt (zdistInf d L (a 0 - b0) : ℝ)) *
              Real.exp (Real.sqrt (zdistInf d L (a 1 - b1) : ℝ)))) +
          WD * (‖K 0 (a 0) b0‖ * ‖K 1 (a 1) b1‖) := by
          have := mul_le_mul_of_nonneg_left h2 h3
          linarith
      _ = _ := by ring
  have hstep2 : ∑ b0, ∑ b1, F b0 b1 ≤
      α' * ((∑ b0, ‖K 0 (a 0) b0‖ * Real.exp (Real.sqrt (zdistInf d L (a 0 - b0) : ℝ))) *
        (∑ b1, ‖K 1 (a 1) b1‖ * Real.exp (Real.sqrt (zdistInf d L (a 1 - b1) : ℝ)))) +
      WD * ((∑ b0, ‖K 0 (a 0) b0‖) * (∑ b1, ‖K 1 (a 1) b1‖)) := by
    calc ∑ b0, ∑ b1, F b0 b1
        ≤ ∑ b0, ∑ b1, (α' * ((‖K 0 (a 0) b0‖ * Real.exp (Real.sqrt (zdistInf d L (a 0 - b0) : ℝ))) *
              (‖K 1 (a 1) b1‖ * Real.exp (Real.sqrt (zdistInf d L (a 1 - b1) : ℝ)))) +
            WD * (‖K 0 (a 0) b0‖ * ‖K 1 (a 1) b1‖)) :=
          Finset.sum_le_sum fun b0 _ => Finset.sum_le_sum fun b1 _ => hpt b0 b1
      _ = _ := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_mul_sum]
  have hnn0 : 0 ≤ ∑ b0, ‖K 0 (a 0) b0‖ * Real.exp (Real.sqrt (zdistInf d L (a 0 - b0) : ℝ)) :=
    Finset.sum_nonneg fun b _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hnn1 : 0 ≤ ∑ b1, ‖K 1 (a 1) b1‖ * Real.exp (Real.sqrt (zdistInf d L (a 1 - b1) : ℝ)) :=
    Finset.sum_nonneg fun b _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hr0 : 0 ≤ ∑ b0, ‖K 0 (a 0) b0‖ := Finset.sum_nonneg fun b _ => norm_nonneg _
  have hr1 : 0 ≤ ∑ b1, ‖K 1 (a 1) b1‖ := Finset.sum_nonneg fun b _ => norm_nonneg _
  have hprodX : (∑ b0, ‖K 0 (a 0) b0‖ * Real.exp (Real.sqrt (zdistInf d L (a 0 - b0) : ℝ))) *
        (∑ b1, ‖K 1 (a 1) b1‖ * Real.exp (Real.sqrt (zdistInf d L (a 1 - b1) : ℝ)))
      ≤ (3 * E * ρ) * (3 * E * ρ) := mul_le_mul (hX 0) (hX 1) hnn1 (by positivity)
  have hprodR : (∑ b0, ‖K 0 (a 0) b0‖) * (∑ b1, ‖K 1 (a 1) b1‖) ≤ ρ * ρ :=
    mul_le_mul (hR 0) (hR 1) hr1 (by positivity)
  -- the amplitude identity
  have hamp : α * ρ ^ 2 = ((W ^ d * |1 - t|)⁻¹) ^ 2 := by
    rw [hα, hρ, abs_of_pos h1s, abs_of_pos h1t]
    have hWd : 0 < W ^ d := pow_pos hW d
    field_simp
  have hmain : α' * ((3 * E * ρ) * (3 * E * ρ)) ≤
      (3 * E) ^ 2 * tailTD d W t D (zdistInf d L (a 0 - a 1) : ℝ) := by
    have hT : tailTD d W t D (zdistInf d L (a 0 - a 1) : ℝ) =
        ((W ^ d * |1 - t|)⁻¹) ^ 2 * Real.exp (-Real.sqrt (zdistInf d L (a 0 - a 1) : ℝ)) + WD := rfl
    have hexp := Real.exp_pos (-Real.sqrt (zdistInf d L (a 0 - a 1) : ℝ))
    have e : α' * ((3 * E * ρ) * (3 * E * ρ)) =
        (3 * E) ^ 2 * (((W ^ d * |1 - t|)⁻¹) ^ 2 *
          Real.exp (-Real.sqrt (zdistInf d L (a 0 - a 1) : ℝ))) := by
      rw [hα', ← hamp]; ring
    rw [e, hT]
    have : 0 ≤ (3 * E) ^ 2 := by positivity
    nlinarith [mul_nonneg this hWD0]
  calc ‖UN d L g (EKsgn m σ) s t A a‖
      ≤ ∑ b : Fin 2 → Zd d L, F (b 0) (b 1) := hstep1
    _ = ∑ b0, ∑ b1, F b0 b1 := hsum2 F
    _ ≤ α' * ((3 * E * ρ) * (3 * E * ρ)) + WD * (ρ * ρ) := by
        refine hstep2.trans (add_le_add ?_ ?_)
        · exact mul_le_mul_of_nonneg_left hprodX hα'0
        · exact mul_le_mul_of_nonneg_left hprodR hWD0
    _ ≤ (3 * E) ^ 2 * tailTD d W t D (zdistInf d L (a 0 - a 1) : ℝ) + ρ ^ 2 * WD := by
        have := hmain
        nlinarith

end Main

/-- **`TailtoTail`**, `(neiwuj)` (`3_5:2344-2362`): the pin `STTailtoTail d`, for every `d` (the hypothesis `3 ≤ d`
is only used as `1 ≤ d`), with `C = (3 e^{(4d+1)/4})²`. -/
theorem stTailtoTail_holds (d : ℕ) : STTailtoTail d := by
  intro hd
  refine ⟨(3 * Real.exp ((4 * (d : ℝ) + 1) / 4)) ^ 2, by positivity, ?_⟩
  intro L hL g W D s t hg hW hs hst ht hgt m hm σ A hA
  have : NeZero L := ⟨by omega⟩
  intro a
  exact tailtoTail_main hL (by omega) hW hs hst ht hgt hm σ A hA a

/-! ### 6. Instances (CLAUDE.md §4 step 2) -/

/-- The pin at `d = 3`. -/
example : STTailtoTail 3 := stTailtoTail_holds 3

/-- **`TailtoTail`, instantiated** at `d = 3`, `L = 3`, `g = 1/2`, `W = 2`, `D = 2`, `s = 0`, `t = 1/2` (`g² = 1/4 ≤ 1/2 = 1 - t`;
`ρ = 2`), `m = i` (`|m| = 1`), `σ = (+,-)`, `A = 0` (`|A_b| = 0 ≤ T_{0,2}`), at `a = (0, e₁)`; the `27` points of `Z_3^3` are not collapsed. -/
theorem inst_tailtoTail_zero :
    ∃ C : ℝ, 0 < C ∧
      ‖UN 3 3 (1 / 2 : ℝ) (EKsgn Complex.I ![true, false]) (0 : ℝ) (1 / 2 : ℝ)
          (fun _ : Fin 2 → Zd 3 3 => (0 : ℂ)) ![0, ![1, 0, 0]]‖ ≤
        C * tailTD 3 2 (1 / 2 : ℝ) 2 (zdistInf 3 3 ((![0, ![1, 0, 0]] : Fin 2 → Zd 3 3) 0 -
            (![0, ![1, 0, 0]] : Fin 2 → Zd 3 3) 1) : ℕ) +
          ((1 - 0 : ℝ) / (1 - 1 / 2 : ℝ)) ^ 2 * (2 : ℝ) ^ (-(2 : ℝ)) := by
  obtain ⟨C, hC, H⟩ := stTailtoTail_holds 3 (by norm_num)
  refine ⟨C, hC, ?_⟩
  exact H 3 (by norm_num) (1 / 2) 2 2 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) Complex.I (by simp) ![true, false]
    (fun _ : Fin 2 → Zd 3 3 => (0 : ℂ))
    (fun b => by rw [norm_zero]; exact tailTD_nonneg (by norm_num)) ![0, ![1, 0, 0]]

/-- The same parameters with the extremal (nonzero) tensor `A_b = T_{s,D}(|b₁-b₂|)`. -/
theorem inst_tailtoTail_extremal :
    ∃ C : ℝ, 0 < C ∧
      ‖UN 3 3 (1 / 2 : ℝ) (EKsgn Complex.I ![true, false]) (0 : ℝ) (1 / 2 : ℝ)
          (fun b : Fin 2 → Zd 3 3 => ((tailTD 3 2 (0 : ℝ) 2 (zdistInf 3 3 (b 0 - b 1) : ℕ) : ℝ) : ℂ))
          ![0, ![1, 0, 0]]‖ ≤
        C * tailTD 3 2 (1 / 2 : ℝ) 2 (zdistInf 3 3 ((![0, ![1, 0, 0]] : Fin 2 → Zd 3 3) 0 -
            (![0, ![1, 0, 0]] : Fin 2 → Zd 3 3) 1) : ℕ) +
          ((1 - 0 : ℝ) / (1 - 1 / 2 : ℝ)) ^ 2 * (2 : ℝ) ^ (-(2 : ℝ)) := by
  obtain ⟨C, hC, H⟩ := stTailtoTail_holds 3 (by norm_num)
  refine ⟨C, hC, ?_⟩
  exact H 3 (by norm_num) (1 / 2) 2 2 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) Complex.I (by simp) ![true, false]
    (fun b : Fin 2 → Zd 3 3 => ((tailTD 3 2 (0 : ℝ) 2 (zdistInf 3 3 (b 0 - b 1) : ℕ) : ℝ) : ℂ))
    (fun b => by
      rw [Complex.norm_real, Real.norm_of_nonneg (tailTD_nonneg (by norm_num))]) ![0, ![1, 0, 0]]

end RBM.Gauss.Sizes
