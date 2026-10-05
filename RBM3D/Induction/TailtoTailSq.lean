/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.TailtoTail
import RBM3D.Induction.Step5Cases

/-!
# S5-10a (ST-4): the squared-profile `TailtoTail` for the quadratic variation of `lem:pf_step5`

The kernel bound for the merged `STeeUM` (`Induction/Step2Defs.lean:797`), the
quadratic-variation weight of `(alu9_STime)` (`3_5:232-240`, `(def_Ustz)`) and of `STGridRepNAt`
conjunct 4 (`Step2Defs.lean:839-851`), with the near/far split at `ℓ* = (log W)^{3/2}` (the
martingale term of `(int_K-L_ST)`, `3_5:2364-2383`; the paper uses Burkholder-Davis-Gundy with
`(res_deccalE_dif)` and states no kernel lemma: paper-delta candidates `T2215a`, `T2215b`).

For any four-index tensor `X` with

* (H1) `‖X(b,b')‖ ≤ p T_{v,D}(|b₀-b₁|)²` when `max_i |b_i-b'_i| ≤ ℓ*` (the shape of
  `lemDecCalEPrec_Bounds` conjunct 3, `Induction/LemDecCalEPrec.lean:847-852`),
* (H2) `‖X‖ ≤ Y` (`difRep2_norm_STeeM_le_N`, `Path/DifREP2.lean:1277`),
* (H3) `‖Θ_w(x,y)‖ ≤ W^{-D₂}` for `(1/8) ℓ* ℓ_w ≤ |x-y|` (`hkell` of `lemDecCalEPrec_goodDet`,
  `Induction/LemDecCalEPrec.lean:868-871`),

and `0 ≤ v ≤ w < 1`, `g² ≤ 1 - w`, `4 ≤ log W`, `|E| ≤ 2`, the bound
`‖Σ_{b,b'} Π_i K^σ_i(a_i,b_i) Π_i K^{σ̄}_i(a_i,b'_i) X(b,b')‖
  ≤ 18 e^{8d+2} p (T_{w,D}(|a₀-a₁|)² + ρ⁴ (W^{-D})²) + 4 Y L^d ρ³ W^{-D₂}`
holds, `ρ = (1-v)/(1-w)`, `K^σ_i = uKer (cycProd (m(σ)) i) v w`.

Route: the helpers of `Induction/TailtoTail.lean` (S5-04, copied with the prefix `tailtoTailSq_`)
give the row sums `Σ_b |K(a,b)| ≤ ρ` and the weighted row sums
`Σ_b |K(a,b)| e^{c|a-b|} ≤ 3ρ`, `c = 1/(4d+1)`; the squared profile uses
`e^{2√r} ≤ e^{4d+1} e^{c r}` and `T_v² ≤ 2 α_v² e^{-2√r} + 2 (W^{-D})²`; the far pairs
(`max_i |b_i-b'_i| > ℓ*`) lie in four events `|a_i-b_i| > ℓ*/2` or `|a_i-b'_i| > ℓ*/2`, each
bounded by the entry bound `‖K(a,b)‖ ≤ W^{-D₂}` from (H3) and `card (Z_L^d) = L^d`.

Registry (DECISIONS §16, §20): no `Prop` is defined or assumed; the targets are theorems.
-/

set_option linter.style.longLine false

namespace RBM.Gauss.Sizes

open RBM RBM.Gauss

/-! ### 1. The `L^∞` weight -/

section Weight

variable {d L : ℕ} [NeZero L]

-- copy of `TailtoTail.lean:50` (verbatim up to the prefix `tailtoTailSq_`).
private theorem tailtoTailSq_zdistInf_add_le (x y : Zd d L) :
    zdistInf d L (x + y) ≤ zdistInf d L x + zdistInf d L y := by
  unfold zdistInf
  refine Finset.sup_le fun i _ => ?_
  calc zdist L ((x + y) i) = zdist L (x i + y i) := rfl
    _ ≤ zdist L (x i) + zdist L (y i) := zdist_add_le L (x i) (y i)
    _ ≤ _ := Nat.add_le_add
        (Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i))
        (Finset.le_sup (f := fun j => zdist L (y j)) (Finset.mem_univ i))

-- copy of `TailtoTail.lean:61` (verbatim up to the prefix `tailtoTailSq_`).
omit [NeZero L] in
private theorem tailtoTailSq_zdistInf_zero : zdistInf d L (0 : Zd d L) = 0 := by
  unfold zdistInf
  simp

-- copy of `TailtoTail.lean:66` (verbatim up to the prefix `tailtoTailSq_`).
/-- three-point triangle inequality for `zdistInf` -/
private theorem tailtoTailSq_zdistInf_tri (a y b : Zd d L) :
    zdistInf d L (a - b) ≤ zdistInf d L (a - y) + zdistInf d L (y - b) := by
  have := tailtoTailSq_zdistInf_add_le (a - y) (y - b)
  rwa [sub_add_sub_cancel] at this

-- copy of `TailtoTail.lean:72` (verbatim up to the prefix `tailtoTailSq_`).
/-- the weight `w(x) = e^{c |x|_∞}` -/
private noncomputable def tailtoTailSq_wt (d L : ℕ) (c : ℝ) (x : Zd d L) : ℝ :=
  Real.exp (c * (zdistInf d L x : ℝ))

-- copy of `TailtoTail.lean:76` (verbatim up to the prefix `tailtoTailSq_`).
omit [NeZero L] in
private theorem tailtoTailSq_wt_pos (c : ℝ) (x : Zd d L) : 0 < tailtoTailSq_wt d L c x :=
  Real.exp_pos _

-- copy of `TailtoTail.lean:80` (verbatim up to the prefix `tailtoTailSq_`).
omit [NeZero L] in
private theorem tailtoTailSq_wt_zero (c : ℝ) : tailtoTailSq_wt d L c 0 = 1 := by
  simp [tailtoTailSq_wt, tailtoTailSq_zdistInf_zero]

-- copy of `TailtoTail.lean:83` (verbatim up to the prefix `tailtoTailSq_`).
private theorem tailtoTailSq_wt_sub_le {c : ℝ} (hc : 0 ≤ c) (a y b : Zd d L) :
    tailtoTailSq_wt d L c (a - b) ≤ tailtoTailSq_wt d L c (a - y) * tailtoTailSq_wt d L c (y - b) := by
  unfold tailtoTailSq_wt
  rw [← Real.exp_add, ← mul_add]
  refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ hc)
  exact_mod_cast tailtoTailSq_zdistInf_tri a y b

-- copy of `TailtoTail.lean:91` (verbatim up to the prefix `tailtoTailSq_`).
/-- `Σ_x S(x) w(x) ≤ 1 + g²/2` when `e^c - 1 ≤ 1/(4d)`: the `2d` neighbours have `|x|_∞ ≤ |x|₁ = 1`. -/
private theorem tailtoTailSq_sum_s_wt (hL : 3 ≤ L) (g : ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hec : (d : ℝ) * (Real.exp c - 1) ≤ 1 / 4) :
    ∑ x : Zd d L, sbKernelR d L g x * tailtoTailSq_wt d L c x ≤ 1 + g ^ 2 / 2 := by
  set a : ℝ := (1 + 2 * (d : ℝ) * g ^ 2)⁻¹ with ha
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hpos : 0 < 1 + 2 * (d : ℝ) * g ^ 2 := by positivity
  have ha0 : 0 < a := inv_pos.mpr hpos
  have ha1 : a ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg g])
  have hpt : ∀ x : Zd d L, sbKernelR d L g x * tailtoTailSq_wt d L c x ≤
      sbKernelR d L g x + (if zdistD d L x = 1 then g ^ 2 * a * (Real.exp c - 1) else 0) := by
    intro x
    by_cases h0 : x = 0
    · subst h0
      simp [sbKernelR, tailtoTailSq_wt_zero, ← ha]
    · by_cases h1 : zdistD d L x = 1
      · have hw : tailtoTailSq_wt d L c x ≤ Real.exp c := by
          unfold tailtoTailSq_wt
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
  calc ∑ x : Zd d L, sbKernelR d L g x * tailtoTailSq_wt d L c x
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

-- copy of `TailtoTail.lean:143` (verbatim up to the prefix `tailtoTailSq_`).
/-- `Θ_t = 1 + t Θ_t S` entrywise, for the (real, nonnegative) entries of `Θ_t^{(+,-)}`. -/
private theorem tailtoTailSq_theta_eq (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (a b : Zd d L) :
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

-- copy of `TailtoTail.lean:176` (verbatim up to the prefix `tailtoTailSq_`).
/-- `Σ_b Θ_t(a,b) w(a-b) ≤ 2/(1-t)` for `g² ≤ 1 - t`: from `Θ = 1 + tΘS`, `w(a-b) ≤ w(a-y) w(y-b)` and
`Σ_x S(x) w(x) ≤ 1 + g²/2`. -/
private theorem tailtoTailSq_theta_wt (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {c : ℝ} (hc : 0 ≤ c) (hec : (d : ℝ) * (Real.exp c - 1) ≤ 1 / 4) (hgt : g ^ 2 ≤ 1 - t)
    (a : Zd d L) :
    ∑ b, (Theta d L g t a b).re * tailtoTailSq_wt d L c (a - b) ≤ 2 / (1 - t) := by
  set F : ℝ := ∑ b, (Theta d L g t a b).re * tailtoTailSq_wt d L c (a - b) with hF
  have hθ0 : ∀ y, 0 ≤ (Theta d L g t a y).re := fun y => Theta_real_nonneg hL ht0 ht1 a y
  have hF0 : 0 ≤ F := Finset.sum_nonneg fun b _ =>
    mul_nonneg (hθ0 b) (tailtoTailSq_wt_pos c _).le
  have hlam := tailtoTailSq_sum_s_wt (d := d) (L := L) hL g hc hec
  have hconv : ∀ y : Zd d L, ∑ b, sbKernelR d L g (y - b) * tailtoTailSq_wt d L c (y - b) =
      ∑ x : Zd d L, sbKernelR d L g x * tailtoTailSq_wt d L c x := fun y =>
    Fintype.sum_equiv (Equiv.subLeft y) _ _ fun b => rfl
  have h1 : F ≤ 1 + t * ((1 + g ^ 2 / 2) * F) := by
    have e1 : F = 1 + t * ∑ b, ∑ y, (Theta d L g t a y).re * sbKernelR d L g (y - b) *
        tailtoTailSq_wt d L c (a - b) := by
      rw [hF]
      have : ∀ b : Zd d L, (Theta d L g t a b).re * tailtoTailSq_wt d L c (a - b) =
          (if a = b then tailtoTailSq_wt d L c (a - b) else 0) +
          t * ∑ y, (Theta d L g t a y).re * sbKernelR d L g (y - b) * tailtoTailSq_wt d L c (a - b) := by
        intro b
        rw [tailtoTailSq_theta_eq hL ht0 ht1 a b, add_mul, mul_assoc, Finset.sum_mul]
        by_cases hab : a = b <;> simp [hab, Finset.mul_sum]
      rw [Finset.sum_congr rfl fun b _ => this b, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [tailtoTailSq_wt_zero]
    have e2 : ∑ b, ∑ y, (Theta d L g t a y).re * sbKernelR d L g (y - b) *
        tailtoTailSq_wt d L c (a - b) ≤ (1 + g ^ 2 / 2) * F := by
      rw [Finset.sum_comm, hF, Finset.mul_sum]
      refine Finset.sum_le_sum fun y _ => ?_
      calc ∑ b, (Theta d L g t a y).re * sbKernelR d L g (y - b) * tailtoTailSq_wt d L c (a - b)
          ≤ ∑ b, (Theta d L g t a y).re * tailtoTailSq_wt d L c (a - y) *
              (sbKernelR d L g (y - b) * tailtoTailSq_wt d L c (y - b)) := by
            refine Finset.sum_le_sum fun b _ => ?_
            have hs := sbKernelR_nonneg d L g (y - b)
            have := tailtoTailSq_wt_sub_le hc a y b
            have h0 := hθ0 y
            calc (Theta d L g t a y).re * sbKernelR d L g (y - b) * tailtoTailSq_wt d L c (a - b)
                = (Theta d L g t a y).re * sbKernelR d L g (y - b) * tailtoTailSq_wt d L c (a - b) := rfl
              _ ≤ (Theta d L g t a y).re * sbKernelR d L g (y - b) *
                    (tailtoTailSq_wt d L c (a - y) * tailtoTailSq_wt d L c (y - b)) :=
                  mul_le_mul_of_nonneg_left this (mul_nonneg h0 hs)
              _ = _ := by ring
        _ = (Theta d L g t a y).re * tailtoTailSq_wt d L c (a - y) *
              ∑ b, sbKernelR d L g (y - b) * tailtoTailSq_wt d L c (y - b) := by
            rw [Finset.mul_sum]
        _ ≤ (Theta d L g t a y).re * tailtoTailSq_wt d L c (a - y) * (1 + g ^ 2 / 2) := by
            rw [hconv y]
            exact mul_le_mul_of_nonneg_left hlam
              (mul_nonneg (hθ0 y) (tailtoTailSq_wt_pos c _).le)
        _ = (1 + g ^ 2 / 2) * ((Theta d L g t a y).re * tailtoTailSq_wt d L c (a - y)) := by ring
    calc F = 1 + t * ∑ b, ∑ y, (Theta d L g t a y).re * sbKernelR d L g (y - b) *
          tailtoTailSq_wt d L c (a - b) := e1
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

-- copy of `TailtoTail.lean:246` (verbatim up to the prefix `tailtoTailSq_`).
/-- the entries of `(1 - sμS)Θ_{tμ} = 1 + (t-s)μ S Θ_{tμ}` are dominated by `1_{a=b} + (t-s)(SΘ_t)(a,b)`. -/
private theorem tailtoTailSq_ker_entry (hL : 3 ≤ L) {μ : ℂ} (hμ : ‖μ‖ = 1) {s t : ℝ} (hs : 0 ≤ s)
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

-- copy of `TailtoTail.lean:269` (verbatim up to the prefix `tailtoTailSq_`).
/-- `Σ_b |K(a,b)| w(a-b) ≤ 3ρ` for the one-index kernel `K = (1 - sμS)Θ_{tμ}`, `ρ = (1-s)/(1-t)`. -/
private theorem tailtoTailSq_ker_wt (hL : 3 ≤ L) {μ : ℂ} (hμ : ‖μ‖ = 1) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht1 : t < 1) {c : ℝ} (hc : 0 ≤ c) (hec : (d : ℝ) * (Real.exp c - 1) ≤ 1 / 4)
    (hgt : g ^ 2 ≤ 1 - t) (a : Zd d L) :
    ∑ b, ‖uKer d L g μ s t a b‖ * tailtoTailSq_wt d L c (a - b) ≤ 3 * ((1 - s) / (1 - t)) := by
  have ht0 : 0 ≤ t := hs.trans hst
  have h3 : 0 < 1 - t := by linarith
  have hlam := tailtoTailSq_sum_s_wt (d := d) (L := L) hL g hc hec
  have hconv : ∑ y, sbKernelR d L g (a - y) * tailtoTailSq_wt d L c (a - y) =
      ∑ x : Zd d L, sbKernelR d L g x * tailtoTailSq_wt d L c x :=
    Fintype.sum_equiv (Equiv.subLeft a) _ _ fun b => rfl
  have hθ0 : ∀ y b, 0 ≤ (Theta d L g t y b).re := fun y b => Theta_real_nonneg hL ht0 ht1 y b
  -- the double sum
  have hdbl : ∑ b, ∑ y, sbKernelR d L g (a - y) * (Theta d L g t y b).re * tailtoTailSq_wt d L c (a - b)
      ≤ (1 + g ^ 2 / 2) * (2 / (1 - t)) := by
    rw [Finset.sum_comm]
    calc ∑ y, ∑ b, sbKernelR d L g (a - y) * (Theta d L g t y b).re * tailtoTailSq_wt d L c (a - b)
        ≤ ∑ y, sbKernelR d L g (a - y) * tailtoTailSq_wt d L c (a - y) * (2 / (1 - t)) := by
          refine Finset.sum_le_sum fun y _ => ?_
          calc ∑ b, sbKernelR d L g (a - y) * (Theta d L g t y b).re * tailtoTailSq_wt d L c (a - b)
              ≤ ∑ b, sbKernelR d L g (a - y) * tailtoTailSq_wt d L c (a - y) *
                  ((Theta d L g t y b).re * tailtoTailSq_wt d L c (y - b)) := by
                refine Finset.sum_le_sum fun b _ => ?_
                have hs0 := sbKernelR_nonneg d L g (a - y)
                have := tailtoTailSq_wt_sub_le hc a y b
                calc sbKernelR d L g (a - y) * (Theta d L g t y b).re * tailtoTailSq_wt d L c (a - b)
                    ≤ sbKernelR d L g (a - y) * (Theta d L g t y b).re *
                        (tailtoTailSq_wt d L c (a - y) * tailtoTailSq_wt d L c (y - b)) :=
                      mul_le_mul_of_nonneg_left this (mul_nonneg hs0 (hθ0 y b))
                  _ = _ := by ring
            _ = sbKernelR d L g (a - y) * tailtoTailSq_wt d L c (a - y) *
                  ∑ b, (Theta d L g t y b).re * tailtoTailSq_wt d L c (y - b) := by
                rw [Finset.mul_sum]
            _ ≤ sbKernelR d L g (a - y) * tailtoTailSq_wt d L c (a - y) * (2 / (1 - t)) :=
                mul_le_mul_of_nonneg_left
                  (tailtoTailSq_theta_wt hL ht0 ht1 hc hec hgt y)
                  (mul_nonneg (sbKernelR_nonneg d L g _) (tailtoTailSq_wt_pos c _).le)
      _ = (∑ y, sbKernelR d L g (a - y) * tailtoTailSq_wt d L c (a - y)) * (2 / (1 - t)) := by
          rw [Finset.sum_mul]
      _ ≤ (1 + g ^ 2 / 2) * (2 / (1 - t)) := by
          rw [hconv]
          exact mul_le_mul_of_nonneg_right hlam (by positivity)
  calc ∑ b, ‖uKer d L g μ s t a b‖ * tailtoTailSq_wt d L c (a - b)
      ≤ ∑ b, ((if a = b then tailtoTailSq_wt d L c (a - b) else 0) +
          (t - s) * ∑ y, sbKernelR d L g (a - y) * (Theta d L g t y b).re *
            tailtoTailSq_wt d L c (a - b)) := by
        refine Finset.sum_le_sum fun b _ => ?_
        have := mul_le_mul_of_nonneg_right (tailtoTailSq_ker_entry (g := g) hL hμ hs hst ht1 a b)
          (tailtoTailSq_wt_pos c (a - b)).le
        refine this.trans (le_of_eq ?_)
        rw [add_mul, mul_assoc, Finset.sum_mul]
        by_cases hab : a = b <;> simp [hab]
    _ = 1 + (t - s) * ∑ b, ∑ y, sbKernelR d L g (a - y) * (Theta d L g t y b).re *
          tailtoTailSq_wt d L c (a - b) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp [tailtoTailSq_wt_zero]
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

/-! ### 4. The weights `e^{2√r}` and the far entry bound -/

section Sqrt

variable {d L : ℕ} [NeZero L]

-- copy of `TailtoTail.lean:346` (verbatim up to the prefix `tailtoTailSq_`).
private theorem tailtoTailSq_hec (hd : 1 ≤ d) :
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

-- copy of `TailtoTail.lean:368` (verbatim up to the prefix `tailtoTailSq_`).
private theorem tailtoTailSq_sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

-- copy of `TailtoTail.lean:414` (verbatim up to the prefix `tailtoTailSq_`).
/-- the row sums of the one-index kernel: `Σ_b |K(a,b)| ≤ ρ` (`norm_uKer_le`). -/
private theorem tailtoTailSq_ker_row (hL : 3 ≤ L) {g : ℝ} {μ : ℂ} (hμ : ‖μ‖ = 1)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht1 : t < 1) (a : Zd d L) :
    ∑ b, ‖uKer d L g μ s t a b‖ ≤ (1 - s) / (1 - t) :=
  (sum_norm_row_le _ a).trans (norm_uKer_le hL hs hst ht1 hμ)

-- copy of `TailtoTail.lean:419` (verbatim up to the prefix `tailtoTailSq_`).
private theorem tailtoTailSq_zdistInf_neg (x : Zd d L) :
    zdistInf d L (-x) = zdistInf d L x := by
  unfold zdistInf
  exact Finset.sup_congr rfl fun i _ => by simp [zdist_neg]

omit [NeZero L] in
/-- `e^{2√r} ≤ e^{4d+1} w_c(x)`, `c = 1/(4d+1)` (adapted from `TailtoTail.lean:374`, `√r` becomes `2√r`):
`K + c r - 2√r = (√r - K)²/K ≥ 0`, `K = 4d+1`. -/
private theorem tailtoTailSq_exp_sqrt_le (hd : 1 ≤ d) (x : Zd d L) :
    Real.exp (2 * Real.sqrt (zdistInf d L x : ℝ)) ≤
      Real.exp (4 * (d : ℝ) + 1) * tailtoTailSq_wt d L (1 / (4 * (d : ℝ) + 1)) x := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hK : (0 : ℝ) < 4 * d + 1 := by linarith
  unfold tailtoTailSq_wt
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  set r : ℝ := (zdistInf d L x : ℝ) with hr
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  set u := Real.sqrt r with hu
  have hu2 : u ^ 2 = r := Real.sq_sqrt hr0
  have : (4 * (d : ℝ) + 1) + 1 / (4 * d + 1) * r - 2 * u = (u - (4 * d + 1)) ^ 2 / (4 * d + 1) := by
    rw [← hu2]; field_simp; ring
  have h2 : 0 ≤ (u - (4 * (d : ℝ) + 1)) ^ 2 / (4 * d + 1) := by positivity
  linarith

/-- `Σ_b |K(a,b)| e^{2√|a-b|} ≤ 3 e^{4d+1} ρ` for the one-index kernel (adapted from `TailtoTail.lean:392`). -/
private theorem tailtoTailSq_ker_exp (hL : 3 ≤ L) (hd : 1 ≤ d) {g : ℝ} {μ : ℂ} (hμ : ‖μ‖ = 1)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht1 : t < 1) (hgt : g ^ 2 ≤ 1 - t) (a : Zd d L) :
    ∑ b, ‖uKer d L g μ s t a b‖ * Real.exp (2 * Real.sqrt (zdistInf d L (a - b) : ℝ)) ≤
      3 * Real.exp (4 * (d : ℝ) + 1) * ((1 - s) / (1 - t)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hK : (0 : ℝ) < 4 * d + 1 := by linarith
  have hc0 : (0 : ℝ) ≤ 1 / (4 * (d : ℝ) + 1) := by positivity
  have hw := tailtoTailSq_ker_wt (g := g) hL hμ hs hst ht1 hc0 (tailtoTailSq_hec hd) hgt a
  calc ∑ b, ‖uKer d L g μ s t a b‖ * Real.exp (2 * Real.sqrt (zdistInf d L (a - b) : ℝ))
      ≤ ∑ b, Real.exp (4 * (d : ℝ) + 1) *
          (‖uKer d L g μ s t a b‖ * tailtoTailSq_wt d L (1 / (4 * (d : ℝ) + 1)) (a - b)) := by
        refine Finset.sum_le_sum fun b _ => ?_
        have := mul_le_mul_of_nonneg_left (tailtoTailSq_exp_sqrt_le hd (a - b)) (norm_nonneg (uKer d L g μ s t a b))
        linarith
    _ = Real.exp (4 * (d : ℝ) + 1) *
          ∑ b, ‖uKer d L g μ s t a b‖ * tailtoTailSq_wt d L (1 / (4 * (d : ℝ) + 1)) (a - b) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (4 * (d : ℝ) + 1) * (3 * ((1 - s) / (1 - t))) :=
        mul_le_mul_of_nonneg_left hw (Real.exp_pos _).le
    _ = 3 * Real.exp (4 * (d : ℝ) + 1) * ((1 - s) / (1 - t)) := by ring

/-- `√|a₀-a₁| ≤ √|a₀-b₀| + √|b₀-b₁| + √|b₁-a₁|`, in doubled exponential form (adapted from `TailtoTail.lean:425`). -/
private theorem tailtoTailSq_exp_tri (a0 a1 b0 b1 : Zd d L) :
    Real.exp (-(2 * Real.sqrt (zdistInf d L (b0 - b1) : ℝ))) ≤
      Real.exp (-(2 * Real.sqrt (zdistInf d L (a0 - a1) : ℝ))) *
        (Real.exp (2 * Real.sqrt (zdistInf d L (a0 - b0) : ℝ)) *
          Real.exp (2 * Real.sqrt (zdistInf d L (a1 - b1) : ℝ))) := by
  rw [← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h1 : zdistInf d L (a0 - a1) ≤
      zdistInf d L (a0 - b0) + zdistInf d L (b0 - b1) + zdistInf d L (a1 - b1) := by
    have e1 := tailtoTailSq_zdistInf_tri a0 b0 a1
    have e2 := tailtoTailSq_zdistInf_tri b0 b1 a1
    have e3 : zdistInf d L (b1 - a1) = zdistInf d L (a1 - b1) := by
      rw [← neg_sub a1 b1]; exact tailtoTailSq_zdistInf_neg _
    omega
  have h2 : ((zdistInf d L (a0 - a1) : ℕ) : ℝ) ≤
      (zdistInf d L (a0 - b0) : ℝ) + (zdistInf d L (b0 - b1) : ℝ) + (zdistInf d L (a1 - b1) : ℝ) := by
    exact_mod_cast h1
  have h3 := Real.sqrt_le_sqrt h2
  have h4 := tailtoTailSq_sqrt_add_le (x := (zdistInf d L (a0 - b0) : ℝ) + (zdistInf d L (b0 - b1) : ℝ))
    (y := (zdistInf d L (a1 - b1) : ℝ)) (by positivity) (by positivity)
  have h5 := tailtoTailSq_sqrt_add_le (x := (zdistInf d L (a0 - b0) : ℝ)) (y := (zdistInf d L (b0 - b1) : ℝ))
    (by positivity) (by positivity)
  linarith

omit [NeZero L] in
/-- the support of the block kernel: `S(x) ≠ 0 → |x|_∞ ≤ 1` (`zdistInf_le_zdistD`). -/
private theorem tailtoTailSq_sb_support {g : ℝ} {x : Zd d L} (hx : sbKernelR d L g x ≠ 0) :
    zdistInf d L x ≤ 1 := by
  by_cases h0 : x = 0
  · subst h0; rw [tailtoTailSq_zdistInf_zero]; exact Nat.zero_le _
  · by_cases h1 : zdistD d L x = 1
    · exact (zdistInf_le_zdistD d L x).trans h1.le
    · exact absurd (by simp [sbKernelR, h0, h1]) hx

/-- the far entry bound: `|a-b| > ℓ/2`, `ℓ ≥ 8` and `‖Θ_t(x,y)‖ ≤ W^{-D₂}` for `|x-y| ≥ ℓ/8` give
`‖K(a,b)‖ ≤ (t-s) Σ_y S(a-y) Θ_t(y,b) ≤ W^{-D₂}` (`|y-b| ≥ |a-b| - |a-y| > ℓ/2 - 1 ≥ ℓ/8`). -/
private theorem tailtoTailSq_far_entry (hL : 3 ≤ L) {g : ℝ} {μ : ℂ} (hμ : ‖μ‖ = 1) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht1 : t < 1) {ℓ B : ℝ} (hℓ : 8 ≤ ℓ) (hB : 0 ≤ B)
    (hΘ : ∀ x y : Zd d L, ℓ / 8 ≤ (zdistInf d L (x - y) : ℝ) → ‖Theta d L g (t : ℂ) x y‖ ≤ B)
    (a b : Zd d L) (hab : ℓ / 2 < (zdistInf d L (a - b) : ℝ)) :
    ‖uKer d L g μ s t a b‖ ≤ B := by
  have hne : a ≠ b := by
    rintro rfl
    rw [sub_self, tailtoTailSq_zdistInf_zero] at hab
    norm_num at hab
    linarith
  have h1 := tailtoTailSq_ker_entry (g := g) hL hμ hs hst ht1 a b
  simp only [hne, ↓reduceIte, zero_add] at h1
  have hconv : ∑ y, sbKernelR d L g (a - y) = 1 :=
    (Fintype.sum_equiv (Equiv.subLeft a) _ (fun x => sbKernelR d L g x) fun y => rfl).trans
      (sum_sbKernelR d L g hL)
  have hsum : ∑ y, sbKernelR d L g (a - y) * (Theta d L g t y b).re ≤ B := by
    calc ∑ y, sbKernelR d L g (a - y) * (Theta d L g t y b).re
        ≤ ∑ y, sbKernelR d L g (a - y) * B := by
          refine Finset.sum_le_sum fun y _ => ?_
          by_cases hS : sbKernelR d L g (a - y) = 0
          · simp [hS]
          · refine mul_le_mul_of_nonneg_left ?_ (sbKernelR_nonneg d L g _)
            have hay := tailtoTailSq_sb_support hS
            have htri := tailtoTailSq_zdistInf_tri a y b
            have hay' : (zdistInf d L (a - y) : ℝ) ≤ 1 := by exact_mod_cast hay
            have htri' : (zdistInf d L (a - b) : ℝ) ≤
                (zdistInf d L (a - y) : ℝ) + (zdistInf d L (y - b) : ℝ) := by exact_mod_cast htri
            exact (Complex.re_le_norm _).trans (hΘ y b (by linarith))
      _ = B := by rw [← Finset.sum_mul, hconv, one_mul]
  refine h1.trans ?_
  have hts : 0 ≤ t - s := by linarith
  have hts1 : t - s ≤ 1 := by linarith
  have := mul_le_mul_of_nonneg_left hsum hts
  nlinarith [mul_nonneg (sub_nonneg.mpr hts1) hB]

/-- a far pair `|b-b'| > ℓ` has `|a-b| > ℓ/2` or `|a-b'| > ℓ/2`. -/
private theorem tailtoTailSq_far_split (a b b' : Zd d L) {ℓ : ℝ}
    (h : ℓ < (zdistInf d L (b - b') : ℝ)) :
    ℓ / 2 < (zdistInf d L (a - b) : ℝ) ∨ ℓ / 2 < (zdistInf d L (a - b') : ℝ) := by
  by_contra hcon
  push Not at hcon
  have h1 := tailtoTailSq_zdistInf_tri b a b'
  have e3 : zdistInf d L (b - a) = zdistInf d L (a - b) := by
    rw [← neg_sub a b]; exact tailtoTailSq_zdistInf_neg _
  have h1' : (zdistInf d L (b - b') : ℝ) ≤
      (zdistInf d L (a - b) : ℝ) + (zdistInf d L (a - b') : ℝ) := by
    rw [e3] at h1; exact_mod_cast h1
  linarith [hcon.1, hcon.2]

private theorem tailtoTailSq_card_Zd : Fintype.card (Zd d L) = L ^ d := by
  simp [Zd, ZMod.card]

end Sqrt

/-! ### 5. The squared-profile `TailtoTail` -/

section Main

variable {d L : ℕ} [NeZero L]

/-- `Σ_b F(b₀) G(b₁) = (Σ F)(Σ G)` over `b : Fin 2 → Z_L^d` (the factorisation of `TailtoTail.lean:485`). -/
private theorem tailtoTailSq_sum_pair (F G : Zd d L → ℝ) :
    ∑ b : Fin 2 → Zd d L, F (b 0) * G (b 1) = (∑ x, F x) * (∑ y, G y) := by
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (piFinTwoEquiv fun _ => Zd d L) _ _ (fun b => rfl)

private theorem tailtoTailSq_sum_split {ι : Type*} [Fintype ι] (F G R S : ι → ℝ) :
    ∑ b, ∑ b', F b * G b' * (R b + S b') =
      (∑ b, F b * R b) * (∑ b', G b') + (∑ b, F b) * (∑ b', G b' * S b') := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b' _ => ?_
  ring

private theorem tailtoTailSq_ell_ge (W : ℝ) (hlog : 4 ≤ Real.log W) :
    (8 : ℝ) ≤ Real.log W ^ (3 / 2 : ℝ) := by
  have h4 : (4 : ℝ) ^ (3 / 2 : ℝ) ≤ Real.log W ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (by norm_num) hlog (by norm_num)
  have h8 : (4 : ℝ) ^ (3 / 2 : ℝ) = 8 := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one,
      ← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 * 2 by norm_num, Real.sqrt_mul_self (by norm_num)]
    norm_num
  linarith

/-- the algebra of the near part: `18 K² α² x² + 2 ρ⁴ y² ≤ 18 K² ((α x + y)² + ρ⁴ y²)` for `K ≥ 1`. -/
private theorem tailtoTailSq_near_alg {K α x y ρ : ℝ} (hK : 1 ≤ K) (hα : 0 ≤ α) (hx : 0 ≤ x)
    (hy : 0 ≤ y) :
    18 * K ^ 2 * α ^ 2 * x ^ 2 + 2 * ρ ^ 4 * y ^ 2 ≤ 18 * K ^ 2 * ((α * x + y) ^ 2 + ρ ^ 4 * y ^ 2) := by
  have hK2 : 1 ≤ K ^ 2 := one_le_pow₀ hK
  have h1 : 0 ≤ 18 * K ^ 2 * (2 * α * x * y + y ^ 2) := by positivity
  have h2 : 0 ≤ (18 * K ^ 2 - 2) * (ρ ^ 4 * y ^ 2) := mul_nonneg (by linarith) (by positivity)
  nlinarith [h1, h2]

/-- the real-number bookkeeping of the final step: `A ρ² + ρ² B'` with `A = p S + Y(F₀R₁) + Y(R₀F₁)` and
`B' = Y(F₀'R₁') + Y(R₀'F₁')`, the row sums `R, R' ≤ ρ`, the far row sums `F, F' ≤ B`. -/
private theorem tailtoTailSq_final {p Y ρ Bd NN SNN R0 R1 R0' R1' F0 F1 F0' F1' : ℝ} (hp : 0 ≤ p) (hY : 0 ≤ Y)
    (hρ : 0 ≤ ρ) (hBd : 0 ≤ Bd) (hSNN0 : 0 ≤ SNN) (hSNN : SNN ≤ NN)
    (hR0 : 0 ≤ R0) (hR1 : 0 ≤ R1) (hR0' : 0 ≤ R0') (hR1' : 0 ≤ R1')
    (hF0 : 0 ≤ F0) (hF1 : 0 ≤ F1) (hF0' : 0 ≤ F0') (hF1' : 0 ≤ F1')
    (hR0ρ : R0 ≤ ρ) (hR1ρ : R1 ≤ ρ) (hR0'ρ : R0' ≤ ρ) (hR1'ρ : R1' ≤ ρ)
    (hF0B : F0 ≤ Bd) (hF1B : F1 ≤ Bd) (hF0'B : F0' ≤ Bd) (hF1'B : F1' ≤ Bd) :
    (p * SNN + Y * (F0 * R1) + Y * (R0 * F1)) * (R0' * R1') +
        (R0 * R1) * (Y * (F0' * R1') + Y * (R0' * F1')) ≤
      p * (NN * ρ ^ 2) + 4 * Y * Bd * ρ ^ 3 := by
  have hRR : R0 * R1 ≤ ρ * ρ := mul_le_mul hR0ρ hR1ρ hR1 hρ
  have hRR' : R0' * R1' ≤ ρ * ρ := mul_le_mul hR0'ρ hR1'ρ hR1' hρ
  have h1 : F0 * R1 ≤ Bd * ρ := mul_le_mul hF0B hR1ρ hR1 hBd
  have h2 : R0 * F1 ≤ ρ * Bd := mul_le_mul hR0ρ hF1B hF1 hρ
  have h1' : F0' * R1' ≤ Bd * ρ := mul_le_mul hF0'B hR1'ρ hR1' hBd
  have h2' : R0' * F1' ≤ ρ * Bd := mul_le_mul hR0'ρ hF1'B hF1' hρ
  have hA0 : 0 ≤ p * SNN + Y * (F0 * R1) + Y * (R0 * F1) :=
    add_nonneg (add_nonneg (mul_nonneg hp hSNN0) (mul_nonneg hY (mul_nonneg hF0 hR1)))
      (mul_nonneg hY (mul_nonneg hR0 hF1))
  have hB0 : 0 ≤ Y * (F0' * R1') + Y * (R0' * F1') :=
    add_nonneg (mul_nonneg hY (mul_nonneg hF0' hR1')) (mul_nonneg hY (mul_nonneg hR0' hF1'))
  have hA : p * SNN + Y * (F0 * R1) + Y * (R0 * F1) ≤ p * NN + Y * (Bd * ρ) + Y * (ρ * Bd) := by
    have := mul_le_mul_of_nonneg_left hSNN hp
    have := mul_le_mul_of_nonneg_left h1 hY
    have := mul_le_mul_of_nonneg_left h2 hY
    linarith
  have hB : Y * (F0' * R1') + Y * (R0' * F1') ≤ Y * (Bd * ρ) + Y * (ρ * Bd) := by
    have := mul_le_mul_of_nonneg_left h1' hY
    have := mul_le_mul_of_nonneg_left h2' hY
    linarith
  have hρρ : 0 ≤ ρ * ρ := mul_nonneg hρ hρ
  calc (p * SNN + Y * (F0 * R1) + Y * (R0 * F1)) * (R0' * R1') +
        (R0 * R1) * (Y * (F0' * R1') + Y * (R0' * F1'))
      ≤ (p * SNN + Y * (F0 * R1) + Y * (R0 * F1)) * (ρ * ρ) +
        (ρ * ρ) * (Y * (F0' * R1') + Y * (R0' * F1')) :=
        add_le_add (mul_le_mul_of_nonneg_left hRR' hA0) (mul_le_mul_of_nonneg_right hRR hB0)
    _ ≤ (p * NN + Y * (Bd * ρ) + Y * (ρ * Bd)) * (ρ * ρ) +
        (ρ * ρ) * (Y * (Bd * ρ) + Y * (ρ * Bd)) :=
        add_le_add (mul_le_mul_of_nonneg_right hA hρρ) (mul_le_mul_of_nonneg_left hB hρρ)
    _ = p * (NN * ρ ^ 2) + 4 * Y * Bd * ρ ^ 3 := by ring

/-- **Target 7g at a fixed `a`** (the kernel bound for an arbitrary tensor `X`). -/
private theorem tailtoTailSq_main (hL : 3 ≤ L) (hd : 1 ≤ d) {g W D D₂ E v w p Y : ℝ} (hW : 0 < W)
    (hE : |E| ≤ 2) (hv : 0 ≤ v) (hvw : v ≤ w) (hw1 : w < 1) (hgw : g ^ 2 ≤ 1 - w)
    (hlog : 4 ≤ Real.log W) (hp : 0 ≤ p) (hY : 0 ≤ Y) (σ : Fin 2 → Bool)
    (X : (Fin 2 → Zd d L) → (Fin 2 → Zd d L) → ℂ)
    (hH1 : ∀ b b' : Fin 2 → Zd d L,
      (∀ i : Fin 2, ((zdistInf d L (b i - b' i) : ℕ) : ℝ) ≤ Real.log W ^ (3 / 2 : ℝ)) →
      ‖X b b'‖ ≤ p * tailTD d W v D ((zdistInf d L (b 0 - b 1) : ℕ) : ℝ) ^ 2)
    (hH2 : ∀ b b' : Fin 2 → Zd d L, ‖X b b'‖ ≤ Y)
    (hH3 : ∀ x y : Zd d L,
      (1 / 8 : ℝ) * (Real.log W ^ ((3 : ℝ) / 2) * ellT L g w) ≤ (zdistInf d L (x - y) : ℝ) →
      ‖Theta d L g (w : ℂ) x y‖ ≤ W ^ (-D₂))
    (a : Fin 2 → Zd d L) :
    ‖∑ b : Fin 2 → Zd d L, ∑ b' : Fin 2 → Zd d L,
        (∏ i, uKer d L g (cycProd (fun i => mSigma E (σ i)) i) v w (a i) (b i)) *
          (∏ i, uKer d L g (cycProd (fun i => mSigma E (!σ i)) i) v w (a i) (b' i)) *
            X b b'‖ ≤
      18 * Real.exp (8 * (d : ℝ) + 2) * p *
          (tailTD d W w D ((zdistInf d L (a 0 - a 1) : ℕ) : ℝ) ^ 2 +
            ((1 - v) / (1 - w)) ^ 4 * (W ^ (-D)) ^ 2) +
        4 * Y * (L : ℝ) ^ d * ((1 - v) / (1 - w)) ^ 3 * W ^ (-D₂) := by
  have ht0 : 0 ≤ w := hv.trans hvw
  have h1w : 0 < 1 - w := by linarith
  have h1v : 0 < 1 - v := by linarith
  have hWD0 : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  have hWD20 : 0 ≤ W ^ (-D₂) := Real.rpow_nonneg hW.le _
  set ρ : ℝ := (1 - v) / (1 - w) with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg h1v.le h1w.le
  have hℓ8 := tailtoTailSq_ell_ge W hlog
  set ℓ : ℝ := Real.log W ^ (3 / 2 : ℝ) with hℓ
  have hellT : ellT L g w = 1 := st5_ellT_one (by exact_mod_cast (by omega : 1 ≤ L)) hgw
  have hΘ : ∀ x y : Zd d L, ℓ / 8 ≤ (zdistInf d L (x - y) : ℝ) →
      ‖Theta d L g (w : ℂ) x y‖ ≤ W ^ (-D₂) := by
    intro x y h
    refine hH3 x y ?_
    rw [hellT, mul_one]
    linarith
  -- the row data
  obtain ⟨k, hk⟩ : ∃ k : Fin 2 → Zd d L → ℝ, ∀ i x,
      k i x = ‖uKer d L g (cycProd (fun j => mSigma E (σ j)) i) v w (a i) x‖ := ⟨_, fun _ _ => rfl⟩
  obtain ⟨k', hk'⟩ : ∃ k' : Fin 2 → Zd d L → ℝ, ∀ i x,
      k' i x = ‖uKer d L g (cycProd (fun j => mSigma E (!σ j)) i) v w (a i) x‖ := ⟨_, fun _ _ => rfl⟩
  have hk0 : ∀ i x, 0 ≤ k i x := fun i x => by rw [hk]; exact norm_nonneg _
  have hk'0 : ∀ i x, 0 ≤ k' i x := fun i x => by rw [hk']; exact norm_nonneg _
  have hμ : ∀ i : Fin 2, ‖cycProd (fun j => mSigma E (σ j)) i‖ = 1 := fun i =>
    norm_cycProd (fun j => norm_mSigma hE (σ j)) i
  have hμ' : ∀ i : Fin 2, ‖cycProd (fun j => mSigma E (!σ j)) i‖ = 1 := fun i =>
    norm_cycProd (fun j => norm_mSigma hE (!σ j)) i
  have hkR : ∀ i, ∑ x, k i x ≤ ρ := fun i => by
    simp_rw [hk]; exact tailtoTailSq_ker_row hL (hμ i) hv hvw hw1 (a i)
  have hk'R : ∀ i, ∑ x, k' i x ≤ ρ := fun i => by
    simp_rw [hk']; exact tailtoTailSq_ker_row hL (hμ' i) hv hvw hw1 (a i)
  have hkX : ∀ i, ∑ x, k i x * Real.exp (2 * Real.sqrt (zdistInf d L (a i - x) : ℝ)) ≤
      3 * Real.exp (4 * (d : ℝ) + 1) * ρ := fun i => by
    simp_rw [hk]; exact tailtoTailSq_ker_exp hL hd (hμ i) hv hvw hw1 hgw (a i)
  have hSk0 : ∀ i, 0 ≤ ∑ x, k i x := fun i => Finset.sum_nonneg fun x _ => hk0 i x
  have hSk'0 : ∀ i, 0 ≤ ∑ x, k' i x := fun i => Finset.sum_nonneg fun x _ => hk'0 i x
  -- the far indicators
  obtain ⟨fe, hfe⟩ : ∃ fe : Fin 2 → Zd d L → ℝ, ∀ i x,
      fe i x = if ℓ / 2 < (zdistInf d L (a i - x) : ℝ) then 1 else 0 := ⟨_, fun _ _ => rfl⟩
  have hfe0 : ∀ i x, 0 ≤ fe i x := fun i x => by rw [hfe]; split_ifs <;> norm_num
  have hfe1 : ∀ i x, ℓ / 2 < (zdistInf d L (a i - x) : ℝ) → fe i x = 1 := fun i x h => by
    simp [hfe, h]
  have hfe2 : ∀ i x, ¬ ℓ / 2 < (zdistInf d L (a i - x) : ℝ) → fe i x = 0 := fun i x h => by
    simp [hfe, h]
  have hcard : ∑ _x : Zd d L, W ^ (-D₂) = (L : ℝ) ^ d * W ^ (-D₂) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, tailtoTailSq_card_Zd]; push_cast; ring
  have hkfe : ∀ i, ∑ x, k i x * fe i x ≤ (L : ℝ) ^ d * W ^ (-D₂) := fun i => by
    rw [← hcard]
    refine Finset.sum_le_sum fun x _ => ?_
    by_cases h : ℓ / 2 < (zdistInf d L (a i - x) : ℝ)
    · rw [hfe1 i x h, mul_one, hk]
      exact tailtoTailSq_far_entry hL (hμ i) hv hvw hw1 hℓ8 hWD20 hΘ (a i) x h
    · rw [hfe2 i x h, mul_zero]; exact hWD20
  have hk'fe : ∀ i, ∑ x, k' i x * fe i x ≤ (L : ℝ) ^ d * W ^ (-D₂) := fun i => by
    rw [← hcard]
    refine Finset.sum_le_sum fun x _ => ?_
    by_cases h : ℓ / 2 < (zdistInf d L (a i - x) : ℝ)
    · rw [hfe1 i x h, mul_one, hk']
      exact tailtoTailSq_far_entry hL (hμ' i) hv hvw hw1 hℓ8 hWD20 hΘ (a i) x h
    · rw [hfe2 i x h, mul_zero]; exact hWD20
  have hSkfe0 : ∀ i, 0 ≤ ∑ x, k i x * fe i x := fun i =>
    Finset.sum_nonneg fun x _ => mul_nonneg (hk0 i x) (hfe0 i x)
  have hSk'fe0 : ∀ i, 0 ≤ ∑ x, k' i x * fe i x := fun i =>
    Finset.sum_nonneg fun x _ => mul_nonneg (hk'0 i x) (hfe0 i x)
  -- the pointwise bound for `X`
  obtain ⟨T, hT⟩ : ∃ T : (Fin 2 → Zd d L) → ℝ, ∀ b,
      T b = tailTD d W v D ((zdistInf d L (b 0 - b 1) : ℕ) : ℝ) := ⟨_, fun _ => rfl⟩
  have hpt : ∀ b b' : Fin 2 → Zd d L, ‖X b b'‖ ≤
      (p * T b ^ 2 + Y * (fe 0 (b 0) + fe 1 (b 1))) + Y * (fe 0 (b' 0) + fe 1 (b' 1)) := by
    intro b b'
    have hb0 := hfe0 0 (b 0)
    have hb1 := hfe0 1 (b 1)
    have hc0 := hfe0 0 (b' 0)
    have hc1 := hfe0 1 (b' 1)
    have hT2 : 0 ≤ p * T b ^ 2 := mul_nonneg hp (sq_nonneg _)
    by_cases hn : ∀ i : Fin 2, ((zdistInf d L (b i - b' i) : ℕ) : ℝ) ≤ ℓ
    · have := hH1 b b' hn
      rw [← hT b] at this
      nlinarith [mul_nonneg hY (add_nonneg hb0 hb1), mul_nonneg hY (add_nonneg hc0 hc1)]
    · push Not at hn
      obtain ⟨i, hi⟩ := hn
      have h1 : 1 ≤ fe 0 (b 0) + fe 1 (b 1) + (fe 0 (b' 0) + fe 1 (b' 1)) := by
        have keyb : ∀ j : Fin 2, fe j (b j) ≤ fe 0 (b 0) + fe 1 (b 1) :=
          Fin.forall_fin_two.2 ⟨by linarith, by linarith⟩
        have keyc : ∀ j : Fin 2, fe j (b' j) ≤ fe 0 (b' 0) + fe 1 (b' 1) :=
          Fin.forall_fin_two.2 ⟨by linarith, by linarith⟩
        rcases tailtoTailSq_far_split (a i) (b i) (b' i) hi with h | h
        · have := keyb i
          rw [hfe1 i (b i) h] at this
          linarith
        · have := keyc i
          rw [hfe1 i (b' i) h] at this
          linarith
      have := hH2 b b'
      nlinarith [mul_le_mul_of_nonneg_left h1 hY]
  have hnorm : ∀ b b' : Fin 2 → Zd d L,
      ‖(∏ i, uKer d L g (cycProd (fun i => mSigma E (σ i)) i) v w (a i) (b i)) *
          (∏ i, uKer d L g (cycProd (fun i => mSigma E (!σ i)) i) v w (a i) (b' i)) * X b b'‖ =
        (k 0 (b 0) * k 1 (b 1)) * (k' 0 (b' 0) * k' 1 (b' 1)) * ‖X b b'‖ := by
    intro b b'
    simp only [norm_mul, Fin.prod_univ_two, hk, hk']
  refine le_trans ((norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun b' _ => (hnorm b b').le))) ?_
  have hstep : ∑ b : Fin 2 → Zd d L, ∑ b' : Fin 2 → Zd d L,
        (k 0 (b 0) * k 1 (b 1)) * (k' 0 (b' 0) * k' 1 (b' 1)) * ‖X b b'‖ ≤
      ∑ b : Fin 2 → Zd d L, ∑ b' : Fin 2 → Zd d L,
        (k 0 (b 0) * k 1 (b 1)) * (k' 0 (b' 0) * k' 1 (b' 1)) *
          ((p * T b ^ 2 + Y * (fe 0 (b 0) + fe 1 (b 1))) + Y * (fe 0 (b' 0) + fe 1 (b' 1))) :=
    Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun b' _ =>
      mul_le_mul_of_nonneg_left (hpt b b')
        (mul_nonneg (mul_nonneg (hk0 0 _) (hk0 1 _)) (mul_nonneg (hk'0 0 _) (hk'0 1 _)))
  refine hstep.trans ((tailtoTailSq_sum_split (fun b => k 0 (b 0) * k 1 (b 1))
    (fun b' => k' 0 (b' 0) * k' 1 (b' 1))
    (fun b => p * T b ^ 2 + Y * (fe 0 (b 0) + fe 1 (b 1)))
    (fun b' => Y * (fe 0 (b' 0) + fe 1 (b' 1)))).le.trans ?_)
  -- the four sums
  have hSP : ∑ b : Fin 2 → Zd d L, k 0 (b 0) * k 1 (b 1) = (∑ x, k 0 x) * ∑ x, k 1 x :=
    tailtoTailSq_sum_pair (k 0) (k 1)
  have hSQ : ∑ b' : Fin 2 → Zd d L, k' 0 (b' 0) * k' 1 (b' 1) = (∑ x, k' 0 x) * ∑ x, k' 1 x :=
    tailtoTailSq_sum_pair (k' 0) (k' 1)
  have hPR : ∑ b : Fin 2 → Zd d L, (k 0 (b 0) * k 1 (b 1)) *
        (p * T b ^ 2 + Y * (fe 0 (b 0) + fe 1 (b 1))) =
      p * ∑ b : Fin 2 → Zd d L, (k 0 (b 0) * k 1 (b 1)) * T b ^ 2 +
        Y * ((∑ x, k 0 x * fe 0 x) * ∑ x, k 1 x) + Y * ((∑ x, k 0 x) * ∑ x, k 1 x * fe 1 x) := by
    have e1 : ∀ b : Fin 2 → Zd d L, (k 0 (b 0) * k 1 (b 1)) *
        (p * T b ^ 2 + Y * (fe 0 (b 0) + fe 1 (b 1))) =
        p * ((k 0 (b 0) * k 1 (b 1)) * T b ^ 2) + Y * (k 0 (b 0) * fe 0 (b 0) * k 1 (b 1)) +
          Y * (k 0 (b 0) * (k 1 (b 1) * fe 1 (b 1))) := fun b => by ring
    have e2 : ∑ b : Fin 2 → Zd d L, k 0 (b 0) * fe 0 (b 0) * k 1 (b 1) =
        (∑ x, k 0 x * fe 0 x) * ∑ x, k 1 x :=
      tailtoTailSq_sum_pair (fun x => k 0 x * fe 0 x) (k 1)
    have e3 : ∑ b : Fin 2 → Zd d L, k 0 (b 0) * (k 1 (b 1) * fe 1 (b 1)) =
        (∑ x, k 0 x) * ∑ x, k 1 x * fe 1 x :=
      tailtoTailSq_sum_pair (k 0) (fun x => k 1 x * fe 1 x)
    rw [Finset.sum_congr rfl fun b _ => e1 b, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, e2, e3]
  have hQS : ∑ b' : Fin 2 → Zd d L, (k' 0 (b' 0) * k' 1 (b' 1)) *
        (Y * (fe 0 (b' 0) + fe 1 (b' 1))) =
      Y * ((∑ x, k' 0 x * fe 0 x) * ∑ x, k' 1 x) + Y * ((∑ x, k' 0 x) * ∑ x, k' 1 x * fe 1 x) := by
    have e1 : ∀ b : Fin 2 → Zd d L, (k' 0 (b 0) * k' 1 (b 1)) * (Y * (fe 0 (b 0) + fe 1 (b 1))) =
        Y * (k' 0 (b 0) * fe 0 (b 0) * k' 1 (b 1)) + Y * (k' 0 (b 0) * (k' 1 (b 1) * fe 1 (b 1))) :=
      fun b => by ring
    have e2 : ∑ b : Fin 2 → Zd d L, k' 0 (b 0) * fe 0 (b 0) * k' 1 (b 1) =
        (∑ x, k' 0 x * fe 0 x) * ∑ x, k' 1 x :=
      tailtoTailSq_sum_pair (fun x => k' 0 x * fe 0 x) (k' 1)
    have e3 : ∑ b : Fin 2 → Zd d L, k' 0 (b 0) * (k' 1 (b 1) * fe 1 (b 1)) =
        (∑ x, k' 0 x) * ∑ x, k' 1 x * fe 1 x :=
      tailtoTailSq_sum_pair (k' 0) (fun x => k' 1 x * fe 1 x)
    rw [Finset.sum_congr rfl fun b _ => e1 b, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, e2, e3]
  -- the near sum: amplitude and exponentials
  obtain ⟨αv, hαv⟩ : ∃ α : ℝ, α = ((W ^ d * |1 - v|)⁻¹) ^ 2 := ⟨_, rfl⟩
  obtain ⟨αw, hαw⟩ : ∃ α : ℝ, α = ((W ^ d * |1 - w|)⁻¹) ^ 2 := ⟨_, rfl⟩
  have hαv0 : 0 ≤ αv := by rw [hαv]; positivity
  have hαw0 : 0 ≤ αw := by rw [hαw]; positivity
  have hamp : αv * ρ ^ 2 = αw := by
    rw [hαv, hαw, hρ, abs_of_pos h1v, abs_of_pos h1w]
    have hWd : 0 < W ^ d := pow_pos hW d
    field_simp
  have hTb : ∀ b : Fin 2 → Zd d L, T b =
      αv * Real.exp (-Real.sqrt (zdistInf d L (b 0 - b 1) : ℝ)) + W ^ (-D) := fun b => by
    rw [hT, hαv]; rfl
  obtain ⟨eA, heA⟩ : ∃ eA : Fin 2 → Zd d L → ℝ, ∀ i x,
      eA i x = Real.exp (2 * Real.sqrt (zdistInf d L (a i - x) : ℝ)) := ⟨_, fun _ _ => rfl⟩
  have heA0 : ∀ i x, 0 ≤ eA i x := fun i x => by rw [heA]; exact (Real.exp_pos _).le
  have hkX' : ∀ i, ∑ x, k i x * eA i x ≤ 3 * Real.exp (4 * (d : ℝ) + 1) * ρ := fun i => by
    simp_rw [heA]; exact hkX i
  have hSkX0 : ∀ i, 0 ≤ ∑ x, k i x * eA i x := fun i =>
    Finset.sum_nonneg fun x _ => mul_nonneg (hk0 i x) (heA0 i x)
  have hNNpt : ∀ b : Fin 2 → Zd d L, (k 0 (b 0) * k 1 (b 1)) * T b ^ 2 ≤
      2 * αv ^ 2 * Real.exp (-(2 * Real.sqrt (zdistInf d L (a 0 - a 1) : ℝ))) *
          ((k 0 (b 0) * eA 0 (b 0)) * (k 1 (b 1) * eA 1 (b 1))) +
        2 * (W ^ (-D)) ^ 2 * (k 0 (b 0) * k 1 (b 1)) := by
    intro b
    have hkk : 0 ≤ k 0 (b 0) * k 1 (b 1) := mul_nonneg (hk0 0 _) (hk0 1 _)
    have htri : Real.exp (-(2 * Real.sqrt (zdistInf d L (b 0 - b 1) : ℝ))) ≤
        Real.exp (-(2 * Real.sqrt (zdistInf d L (a 0 - a 1) : ℝ))) * (eA 0 (b 0) * eA 1 (b 1)) := by
      rw [heA, heA]; exact tailtoTailSq_exp_tri (a 0) (a 1) (b 0) (b 1)
    have hsq : (Real.exp (-Real.sqrt (zdistInf d L (b 0 - b 1) : ℝ))) ^ 2 =
        Real.exp (-(2 * Real.sqrt (zdistInf d L (b 0 - b 1) : ℝ))) := by
      rw [sq, ← Real.exp_add]; ring_nf
    have hT2 : T b ^ 2 ≤ 2 * αv ^ 2 *
        Real.exp (-(2 * Real.sqrt (zdistInf d L (b 0 - b 1) : ℝ))) + 2 * (W ^ (-D)) ^ 2 := by
      rw [hTb, ← hsq]
      nlinarith [sq_nonneg (αv * Real.exp (-Real.sqrt (zdistInf d L (b 0 - b 1) : ℝ)) - W ^ (-D))]
    have h3 : 2 * αv ^ 2 * Real.exp (-(2 * Real.sqrt (zdistInf d L (b 0 - b 1) : ℝ))) ≤
        2 * αv ^ 2 * (Real.exp (-(2 * Real.sqrt (zdistInf d L (a 0 - a 1) : ℝ))) *
          (eA 0 (b 0) * eA 1 (b 1))) :=
      mul_le_mul_of_nonneg_left htri (by positivity)
    calc (k 0 (b 0) * k 1 (b 1)) * T b ^ 2
        ≤ (k 0 (b 0) * k 1 (b 1)) * (2 * αv ^ 2 * (Real.exp (-(2 * Real.sqrt
            (zdistInf d L (a 0 - a 1) : ℝ))) * (eA 0 (b 0) * eA 1 (b 1))) + 2 * (W ^ (-D)) ^ 2) :=
          mul_le_mul_of_nonneg_left (hT2.trans (by linarith)) hkk
      _ = _ := by ring
  have hNN : ∑ b : Fin 2 → Zd d L, (k 0 (b 0) * k 1 (b 1)) * T b ^ 2 ≤
      2 * αv ^ 2 * Real.exp (-(2 * Real.sqrt (zdistInf d L (a 0 - a 1) : ℝ))) *
          ((3 * Real.exp (4 * (d : ℝ) + 1) * ρ) * (3 * Real.exp (4 * (d : ℝ) + 1) * ρ)) +
        2 * (W ^ (-D)) ^ 2 * (ρ * ρ) := by
    have e2 : ∑ b : Fin 2 → Zd d L, (k 0 (b 0) * eA 0 (b 0)) * (k 1 (b 1) * eA 1 (b 1)) =
        (∑ x, k 0 x * eA 0 x) * ∑ x, k 1 x * eA 1 x :=
      tailtoTailSq_sum_pair (fun x => k 0 x * eA 0 x) (fun x => k 1 x * eA 1 x)
    calc _ ≤ ∑ b : Fin 2 → Zd d L,
          (2 * αv ^ 2 * Real.exp (-(2 * Real.sqrt (zdistInf d L (a 0 - a 1) : ℝ))) *
            ((k 0 (b 0) * eA 0 (b 0)) * (k 1 (b 1) * eA 1 (b 1))) +
          2 * (W ^ (-D)) ^ 2 * (k 0 (b 0) * k 1 (b 1))) := Finset.sum_le_sum fun b _ => hNNpt b
      _ = 2 * αv ^ 2 * Real.exp (-(2 * Real.sqrt (zdistInf d L (a 0 - a 1) : ℝ))) *
            ((∑ x, k 0 x * eA 0 x) * ∑ x, k 1 x * eA 1 x) +
          2 * (W ^ (-D)) ^ 2 * ((∑ x, k 0 x) * ∑ x, k 1 x) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, e2, hSP]
      _ ≤ _ := by
        have h1 := mul_le_mul (hkX' 0) (hkX' 1) (hSkX0 1) (by positivity)
        have h2 := mul_le_mul (hkR 0) (hkR 1) (hSk0 1) hρ0
        exact add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity))
          (mul_le_mul_of_nonneg_left h2 (by positivity))
  -- the final assembly
  have hnear : (2 * αv ^ 2 * Real.exp (-(2 * Real.sqrt (zdistInf d L (a 0 - a 1) : ℝ))) *
          ((3 * Real.exp (4 * (d : ℝ) + 1) * ρ) * (3 * Real.exp (4 * (d : ℝ) + 1) * ρ)) +
        2 * (W ^ (-D)) ^ 2 * (ρ * ρ)) * ρ ^ 2 ≤
      18 * Real.exp (8 * (d : ℝ) + 2) *
        (tailTD d W w D ((zdistInf d L (a 0 - a 1) : ℕ) : ℝ) ^ 2 + ρ ^ 4 * (W ^ (-D)) ^ 2) := by
    have hK2 : Real.exp (8 * (d : ℝ) + 2) = Real.exp (4 * (d : ℝ) + 1) ^ 2 := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    have hE0 : Real.exp (-(2 * Real.sqrt (zdistInf d L (a 0 - a 1) : ℝ))) =
        Real.exp (-Real.sqrt (zdistInf d L (a 0 - a 1) : ℝ)) ^ 2 := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    have hTw : tailTD d W w D ((zdistInf d L (a 0 - a 1) : ℕ) : ℝ) =
        αw * Real.exp (-Real.sqrt (zdistInf d L (a 0 - a 1) : ℝ)) + W ^ (-D) := by
      rw [hαw]; rfl
    have e1 : (2 * αv ^ 2 * Real.exp (-(2 * Real.sqrt (zdistInf d L (a 0 - a 1) : ℝ))) *
          ((3 * Real.exp (4 * (d : ℝ) + 1) * ρ) * (3 * Real.exp (4 * (d : ℝ) + 1) * ρ)) +
        2 * (W ^ (-D)) ^ 2 * (ρ * ρ)) * ρ ^ 2 =
        18 * Real.exp (4 * (d : ℝ) + 1) ^ 2 * (αv * ρ ^ 2) ^ 2 *
          Real.exp (-(2 * Real.sqrt (zdistInf d L (a 0 - a 1) : ℝ))) + 2 * ρ ^ 4 * (W ^ (-D)) ^ 2 := by
      ring
    rw [e1, hamp, hTw, hK2, hE0]
    exact tailtoTailSq_near_alg (Real.one_le_exp (by positivity)) hαw0 (Real.exp_pos _).le hWD0
  have hSNN0 : 0 ≤ ∑ b : Fin 2 → Zd d L, (k 0 (b 0) * k 1 (b 1)) * T b ^ 2 :=
    Finset.sum_nonneg fun b _ => mul_nonneg (mul_nonneg (hk0 0 _) (hk0 1 _)) (sq_nonneg _)
  have hBd0 : 0 ≤ (L : ℝ) ^ d * W ^ (-D₂) := by positivity
  rw [hPR, hQS, hSP, hSQ]
  have hfin := tailtoTailSq_final hp hY hρ0 hBd0 hSNN0 hNN (hSk0 0) (hSk0 1) (hSk'0 0) (hSk'0 1)
    (hSkfe0 0) (hSkfe0 1) (hSk'fe0 0) (hSk'fe0 1) (hkR 0) (hkR 1) (hk'R 0) (hk'R 1)
    (hkfe 0) (hkfe 1) (hk'fe 0) (hk'fe 1)
  calc _ ≤ _ := hfin
    _ ≤ p * (18 * Real.exp (8 * (d : ℝ) + 2) *
          (tailTD d W w D ((zdistInf d L (a 0 - a 1) : ℕ) : ℝ) ^ 2 + ρ ^ 4 * (W ^ (-D)) ^ 2)) +
        4 * Y * ((L : ℝ) ^ d * W ^ (-D₂)) * ρ ^ 3 :=
        add_le_add (mul_le_mul_of_nonneg_left hnear hp) le_rfl
    _ = _ := by ring

end Main

/-- `4 ≤ log 64` (`log 64 = 6 log 2`, `log 2 > 0.6931`). -/
private theorem tailtoTailSq_four_le_log64 : (4 : ℝ) ≤ Real.log 64 := by
  have h : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_gt_d9
  rw [h]; linarith

/-! ### 6. The targets -/

/-- **Target 7g** (`tailtoTailSq_kernelGen`): the squared-profile `TailtoTail` for an arbitrary 4-index tensor `X`,
near/far split at `ℓ* = (log W)^{3/2}`.  (H1) near bound `‖X(b,b')‖ ≤ p T_{v,D}(|b₀-b₁|)²` for `max_i |b_i - b'_i| ≤ ℓ*`,
(H2) crude bound `‖X‖ ≤ Y`, (H3) `‖Θ_w(x,y)‖ ≤ W^{-D₂}` for `|x-y| ≥ ℓ* ℓ_w / 8` (`hkell` of
`lemDecCalEPrec_goodDet` at `u = w`, `D = D₂`).  Conclusion with `ρ = (1-v)/(1-w)`, `C₇ = 18 e^{8d+2}`:
`‖Σ_{b,b'} Π_i K^σ_i(a_i,b_i) Π_i K^σ̄_i(a_i,b'_i) X(b,b')‖ ≤ C₇ p (T_{w,D}(|a₀-a₁|)² + ρ⁴ (W^{-D})²) + 4 Y L^d ρ³ W^{-D₂}`.
Paper-delta candidates `T2215a`, `T2215b`; a conditional adapter in `(H1)`-`(H3)`, not a statement of the paper. -/
theorem tailtoTailSq_kernelGen (d : ℕ) :
  3 ≤ d → ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g W D D₂ E v w p Y : ℝ), 0 < W → |E| ≤ 2 →
    0 ≤ v → v ≤ w → w < 1 → g ^ 2 ≤ 1 - w → 4 ≤ Real.log W → 0 ≤ p → 0 ≤ Y →
    ∀ (σ : Fin 2 → Bool) (X : (Fin 2 → Zd d L) → (Fin 2 → Zd d L) → ℂ),
      (∀ b b' : Fin 2 → Zd d L,
        (∀ i : Fin 2, ((zdistInf d L (b i - b' i) : ℕ) : ℝ) ≤ Real.log W ^ (3 / 2 : ℝ)) →
        ‖X b b'‖ ≤ p * tailTD d W v D ((zdistInf d L (b 0 - b 1) : ℕ) : ℝ) ^ 2) →
      (∀ b b' : Fin 2 → Zd d L, ‖X b b'‖ ≤ Y) →
      (∀ x y : Zd d L,
        (1 / 8 : ℝ) * (Real.log W ^ ((3 : ℝ) / 2) * ellT L g w) ≤ (zdistInf d L (x - y) : ℝ) →
        ‖Theta d L g (w : ℂ) x y‖ ≤ W ^ (-D₂)) →
      ∀ a : Fin 2 → Zd d L,
        ‖∑ b : Fin 2 → Zd d L, ∑ b' : Fin 2 → Zd d L,
            (∏ i, uKer d L g (cycProd (fun i => mSigma E (σ i)) i) v w (a i) (b i)) *
              (∏ i, uKer d L g (cycProd (fun i => mSigma E (!σ i)) i) v w (a i) (b' i)) *
                X b b'‖ ≤
          18 * Real.exp (8 * (d : ℝ) + 2) * p *
              (tailTD d W w D ((zdistInf d L (a 0 - a 1) : ℕ) : ℝ) ^ 2 +
                ((1 - v) / (1 - w)) ^ 4 * (W ^ (-D)) ^ 2) +
            4 * Y * (L : ℝ) ^ d * ((1 - v) / (1 - w)) ^ 3 * W ^ (-D₂) := by
  intro hd L _ hL g W D D₂ E v w p Y hW hE hv hvw hw1 hgw hlog hp hY σ X hH1 hH2 hH3 a
  exact tailtoTailSq_main hL (by omega) hW hE hv hvw hw1 hgw hlog hp hY σ X hH1 hH2 hH3 a

/-- **Target 7** (`tailtoTailSq_kernel`): target 7g at `L = L_n`, `g = lam_n`, `W = W_n`, `X = STeeM sz n E v H σ`
for every fine matrix `H`; the left side is the merged `STeeUM` (`Step2Defs.lean:797`, the quadratic-variation
weight of `STGridRepNAt` conjunct 4, `Step2Defs.lean:839-851`). -/
theorem tailtoTailSq_kernel {d : ℕ} (sz : Sizes d) :
  3 ≤ d → ∀ (n : ℕ) (E v w D D₂ p Y : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool),
    |E| ≤ 2 → 0 ≤ v → v ≤ w → w < 1 → sz.lam n ^ 2 ≤ 1 - w →
    4 ≤ Real.log ((sz.W n : ℕ) : ℝ) → 0 ≤ p → 0 ≤ Y →
    (∀ b b' : Fin 2 → Zd d (sz.L n),
      (∀ i : Fin 2, ((zdistInf d (sz.L n) (b i - b' i) : ℕ) : ℝ) ≤
        Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
      ‖STeeM sz n E v H σ b b'‖ ≤ p * STtailTD sz n v D b ^ 2) →
    (∀ b b' : Fin 2 → Zd d (sz.L n), ‖STeeM sz n E v H σ b b'‖ ≤ Y) →
    (∀ x y : Zd d (sz.L n),
      (1 / 8 : ℝ) * (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) * ellT (sz.L n) (sz.lam n) w) ≤
        (zdistInf d (sz.L n) (x - y) : ℝ) →
      ‖Theta d (sz.L n) (sz.lam n) (w : ℂ) x y‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D₂)) →
    ∀ a : Fin 2 → Zd d (sz.L n),
      ‖STeeUM sz n E v w H σ a‖ ≤
        18 * Real.exp (8 * (d : ℝ) + 2) * p *
            (STtailTD sz n w D a ^ 2 + ((1 - v) / (1 - w)) ^ 4 * (((sz.W n : ℕ) : ℝ) ^ (-D)) ^ 2) +
          4 * Y * ((sz.L n : ℕ) : ℝ) ^ d * ((1 - v) / (1 - w)) ^ 3 * ((sz.W n : ℕ) : ℝ) ^ (-D₂) := by
  intro hd n E v w D D₂ p Y H σ hE hv hvw hw1 hg hlog hp hY hH1 hH2 hH3 a
  exact tailtoTailSq_kernelGen d hd (sz.L n) (sz.three_le_L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) D D₂ E v w p Y
    (by exact_mod_cast sz.W_pos n) hE hv hvw hw1 hg hlog hp hY σ (STeeM sz n E v H σ) hH1 hH2 hH3 a

/-! ### 7. Instances (CLAUDE.md §4 step 2) -/

/-- The pin of target 7 at the size data `SizesInst.sz0` (`Defs/Sizes.lean:260`). -/
example := tailtoTailSq_kernel SizesInst.sz0

/-- **Instance (c) of target 7g**, at `d = 3`, `L = 20`, `g = 1/64`, `W = 64`, `D = 8`, `D₂ = 5`, `E = 0`, `v = 1/32`,
`w = 1/16`, `p = Y = 1`, with the concrete nonnegative worst tensor `X(b,b') = T_{v,D}(|b₀-b₁|)²` on near pairs and `1` on
far pairs (both kinds occur: `max zdist = 10 > ℓ* = 8.48`).  Discharged here: `3 ≤ 3`, `3 ≤ 20`, `0 < 64`, `|0| ≤ 2`,
`0 ≤ 1/32 ≤ 1/16 < 1`, `(1/64)² ≤ 15/16`, `4 ≤ log 64`, (H1) and (H2); (H3) (another gate's pin, `lemDecCalEPrec_kell`;
numerically `max_{|x|_∞ ≥ 2} Θ_w(x) = 2.8e-10 ≤ 64^{-5} = 9.3e-10`) stays the hypothesis. -/
theorem inst_tailtoTailSq_c :
  (∀ x y : Zd 3 20,
      (1 / 8 : ℝ) * (Real.log 64 ^ ((3 : ℝ) / 2) * ellT 20 (1 / 64) (1 / 16)) ≤ (zdistInf 3 20 (x - y) : ℝ) →
      ‖Theta 3 20 (1 / 64) ((1 / 16 : ℝ) : ℂ) x y‖ ≤ (64 : ℝ) ^ (-(5 : ℝ))) →
    ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 20),
      ‖∑ b : Fin 2 → Zd 3 20, ∑ b' : Fin 2 → Zd 3 20,
          (∏ i, uKer 3 20 (1 / 64) (cycProd (fun i => mSigma 0 (σ i)) i) (1 / 32) (1 / 16) (a i) (b i)) *
            (∏ i, uKer 3 20 (1 / 64) (cycProd (fun i => mSigma 0 (!σ i)) i) (1 / 32) (1 / 16) (a i) (b' i)) *
              (((if (∀ i : Fin 2, ((zdistInf 3 20 (b i - b' i) : ℕ) : ℝ) ≤ Real.log 64 ^ (3 / 2 : ℝ)) then
                  tailTD 3 64 (1 / 32) 8 ((zdistInf 3 20 (b 0 - b 1) : ℕ) : ℝ) ^ 2 else 1 : ℝ)) : ℂ)‖ ≤
        18 * Real.exp (8 * ((3 : ℕ) : ℝ) + 2) * 1 *
            (tailTD 3 64 (1 / 16) 8 ((zdistInf 3 20 (a 0 - a 1) : ℕ) : ℝ) ^ 2 +
              ((1 - 1 / 32) / (1 - 1 / 16)) ^ 4 * ((64 : ℝ) ^ (-(8 : ℝ))) ^ 2) +
          4 * 1 * ((20 : ℕ) : ℝ) ^ 3 * ((1 - 1 / 32) / (1 - 1 / 16)) ^ 3 * (64 : ℝ) ^ (-(5 : ℝ)) := by
  intro hΘ σ a
  have hlog := tailtoTailSq_four_le_log64
  have hT1 : ∀ r : ℝ, tailTD 3 64 (1 / 32) 8 r ^ 2 ≤ 1 := by
    intro r
    have hW : (64 : ℝ) ^ (-(8 : ℝ)) ≤ 1 / 2 := by
      rw [Real.rpow_neg (by norm_num)]
      norm_num [Real.rpow_ofNat]
    have hα : ((((64 : ℝ) ^ 3 * |1 - 1 / 32|)⁻¹) ^ 2) ≤ 1 / 2 := by
      norm_num [abs_of_pos]
    have he : Real.exp (-Real.sqrt r) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith [Real.sqrt_nonneg r])
    have hnn := tailTD_nonneg (d := 3) (W := 64) (u := 1 / 32) (D := 8) (r := r) (by norm_num)
    have hle : tailTD 3 64 (1 / 32) 8 r ≤ 1 := by
      unfold tailTD
      have : 0 ≤ ((((64 : ℝ) ^ 3 * |1 - 1 / 32|)⁻¹) ^ 2) := by positivity
      nlinarith [Real.exp_pos (-Real.sqrt r)]
    exact pow_le_one₀ hnn hle
  refine tailtoTailSq_kernelGen 3 le_rfl 20 (by norm_num) (1 / 64) 64 8 5 0 (1 / 32) (1 / 16) 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlog
    (by norm_num) (by norm_num) σ
    (fun b b' => (((if (∀ i : Fin 2, ((zdistInf 3 20 (b i - b' i) : ℕ) : ℝ) ≤ Real.log 64 ^ (3 / 2 : ℝ)) then
      tailTD 3 64 (1 / 32) 8 ((zdistInf 3 20 (b 0 - b 1) : ℕ) : ℝ) ^ 2 else 1 : ℝ)) : ℂ))
    ?_ ?_ hΘ a
  · intro b b' h
    simp only [eq_true h, ↓reduceIte]
    rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _), one_mul]
  · intro b b'
    by_cases h : ∀ i : Fin 2, ((zdistInf 3 20 (b i - b' i) : ℕ) : ℝ) ≤ Real.log 64 ^ (3 / 2 : ℝ)
    · simp only [eq_true h, ↓reduceIte]
      rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
      exact hT1 _
    · simp only [eq_false h, ↓reduceIte]
      simp

/-- **Target 7, instantiated** at `SizesInst.sz0` (`Defs/Sizes.lean:260`), `n = 1` (`L = 8`, `W = 1024`, `lam = 1/4096`,
`d = 3`), `E = 0`, `v = 1/32`, `w = 1/16`, `D = 8`, `D₂ = 5`, `p = Y = 1`, any fine matrix `H`, any `σ`, any `a`.  The
scalar premises are discharged (`|0| ≤ 2`, `0 ≤ 1/32 ≤ 1/16 < 1`, `lam² ≤ 15/16`, `4 ≤ log 1024`, `0 ≤ 1`); (H1), (H2), (H3)
are the statements of other gates' suppliers (`lemDecCalEPrec_Bounds` conjunct 3, `difRep2_norm_STeeM_le_N`,
`lemDecCalEPrec_kell`) and stay hypotheses. -/
example (H : Matrix (Idx 3 (SizesInst.sz0.L 1) (SizesInst.sz0.W 1))
      (Idx 3 (SizesInst.sz0.L 1) (SizesInst.sz0.W 1)) ℂ) (σ : Fin 2 → Bool)
    (hH1 : ∀ b b' : Fin 2 → Zd 3 (SizesInst.sz0.L 1),
      (∀ i : Fin 2, ((zdistInf 3 (SizesInst.sz0.L 1) (b i - b' i) : ℕ) : ℝ) ≤
        Real.log ((SizesInst.sz0.W 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
      ‖STeeM SizesInst.sz0 1 0 (1 / 32) H σ b b'‖ ≤ 1 * STtailTD SizesInst.sz0 1 (1 / 32) 8 b ^ 2)
    (hH2 : ∀ b b' : Fin 2 → Zd 3 (SizesInst.sz0.L 1), ‖STeeM SizesInst.sz0 1 0 (1 / 32) H σ b b'‖ ≤ 1)
    (hH3 : ∀ x y : Zd 3 (SizesInst.sz0.L 1),
      (1 / 8 : ℝ) * (Real.log ((SizesInst.sz0.W 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) *
        ellT (SizesInst.sz0.L 1) (SizesInst.sz0.lam 1) (1 / 16)) ≤
        (zdistInf 3 (SizesInst.sz0.L 1) (x - y) : ℝ) →
      ‖Theta 3 (SizesInst.sz0.L 1) (SizesInst.sz0.lam 1) ((1 / 16 : ℝ) : ℂ) x y‖ ≤
        ((SizesInst.sz0.W 1 : ℕ) : ℝ) ^ (-(5 : ℝ)))
    (a : Fin 2 → Zd 3 (SizesInst.sz0.L 1)) :
    ‖STeeUM SizesInst.sz0 1 0 (1 / 32) (1 / 16) H σ a‖ ≤
      18 * Real.exp (8 * ((3 : ℕ) : ℝ) + 2) * 1 *
          (STtailTD SizesInst.sz0 1 (1 / 16) 8 a ^ 2 +
            ((1 - 1 / 32) / (1 - 1 / 16)) ^ 4 * (((SizesInst.sz0.W 1 : ℕ) : ℝ) ^ (-(8 : ℝ))) ^ 2) +
        4 * 1 * ((SizesInst.sz0.L 1 : ℕ) : ℝ) ^ 3 * ((1 - 1 / 32) / (1 - 1 / 16)) ^ 3 *
          ((SizesInst.sz0.W 1 : ℕ) : ℝ) ^ (-(5 : ℝ)) := by
  refine tailtoTailSq_kernel SizesInst.sz0 le_rfl 1 0 (1 / 32) (1 / 16) 8 5 1 1 H σ (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [SizesInst.sz0]) ?_ (by norm_num)
    (by norm_num) hH1 hH2 hH3 a
  exact tailtoTailSq_four_le_log64.trans (Real.log_le_log (by norm_num) (by norm_num [SizesInst.sz0]))

end RBM.Gauss.Sizes
