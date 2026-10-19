/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.Step5IIIEdet

/-!
# The ℰ-bounds of BA case (iii) of Step 5 by Hilbert-Schmidt estimates, second half

Second half of `BA/Step5IIIEdet`.  Paper: Lemma 5.2 (`lem_dec_calE`), (5.45) `res_deccalE_dif`; the paper omits the proof
("a special case of [YY_25, Lemma 5.7]"; at BA, Section 8, "we therefore omit the details").  This file proves `res_deccalE_dif` and
assembles `lem_dec_calE`.

* `baStep5IIIE_sumTheta`: `S_θ = Σ_y e^{-(θ/2)√|y|_∞} ≤ (1 + 96/(θ/(2d))⁴)^d`,
  uniformly in `L`.
* `baStep5IIIE_dif`: `res_deccalE_dif`.  At `S = 1` (`baStep2Mat`), `STeeMg` at
  `m = 2` is `W^d Σ_c` of two six-loops with blocks `(a₀, a₁, c, a₁', a₀', c)` and
  `(a₁, a₀, c, a₀', a₁', c)` (`Step5IIIEdet2_STeeMg_eq`, from `STeeLoop` at `k = 1, 2`).  Each
  six-loop is bounded through its six legs by `Step5IIIEdet2_hs6`
  (the Hilbert-Schmidt bound at `k = 6`, from the Hilbert-Schmidt layer of `BA/Step5IIIEdet`; the glue forms `Step5IIIEdet2_glue5`, `Step5IIIEdet2_glue2` keep the two legs at `c` as
  one factor whose 4-loop is `≤ Λ τ³`).  Near regime `r ≤ 6ℓ*`: (A) `c` within `3ℓ*` of `a₀` or
  `a₁`: the six-loop is `≤ Λ τ⁵` by (v); (B) `c` farther: two short legs `≤ Λ τ`, four long legs by
  (vi) (`Step5IIIEdet2_leg_dec`), one decaying factor summed to `S_θ`.  Far regime `r > 6ℓ*`:
  (C) `c` within `3ℓ*`: the glue, four long legs `≤ 2 J e^{√6 Y} T(r)`; (D) `c` farther: six long
  legs, `LemDecCalE_sum_tail_tail`.  No entry-level bound of the resolvent, no energy bound, no
  `M = m·1`, no explicit band kernel, no 𝒦 bound at equal charges.
* `BAStep5IIIEdet`, `baStep5IIIEdet_holds`: the conjunction of `res_deccalE_lk`, `res_deccalE_wG` (`BA/Step5IIIEdet`)
  and `res_deccalE_dif`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open private lemDecCalE_zdistInf_sub_comm lemDecCalE_zdistInf_tri_real lemDecCalE_sum_zdist_le lemDecCalE_zdist_le_zdistInf from RBM3D.Path.LemDecCalE

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Matrix

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The lattice sum `S_θ` -/

/-- `S_θ ≤ (1 + 96/γ⁴)^d` with `γ = θ/(2d)` for one `L` (the proof of `LemDecCalE_sum_zd_le`, `Path/LemDecCalE`, at the rate
`θ/2` instead of `1/2`; the one-dimensional sum is `lemDecCalE_sum_zdist_le`, `open private`). -/
theorem Step5IIIEdet2_sum_theta_le (d L : ℕ) [NeZero L] (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 < θ) :
    ∑ z : Zd d L, Real.exp (-(θ / 2 * Real.sqrt (zdistInf d L z : ℝ))) ≤ (1 + 96 / (θ / (2 * d)) ^ 4) ^ d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set γ : ℝ := θ / (2 * d) with hγ
  have hγ0 : 0 < γ := by positivity
  set g : ZMod L → ℝ := fun y => Real.exp (-(γ * Real.sqrt (zdist L y : ℝ))) with hg
  have hpt : ∀ z : Zd d L, Real.exp (-(θ / 2 * Real.sqrt (zdistInf d L z : ℝ))) ≤ ∏ i, g (z i) := by
    intro z
    simp only [hg]
    rw [← Real.exp_sum]
    refine Real.exp_le_exp.2 ?_
    rw [Finset.sum_neg_distrib, neg_le_neg_iff, ← Finset.mul_sum]
    have hs : ∑ i : Fin d, Real.sqrt (zdist L (z i) : ℝ) ≤ d * Real.sqrt (zdistInf d L z : ℝ) := by
      calc ∑ i : Fin d, Real.sqrt (zdist L (z i) : ℝ)
          ≤ ∑ _i : Fin d, Real.sqrt (zdistInf d L z : ℝ) :=
            Finset.sum_le_sum fun i _ =>
              Real.sqrt_le_sqrt (by exact_mod_cast lemDecCalE_zdist_le_zdistInf d L z i)
        _ = d * Real.sqrt (zdistInf d L z : ℝ) := by simp
    calc γ * ∑ i : Fin d, Real.sqrt (zdist L (z i) : ℝ)
        ≤ γ * (d * Real.sqrt (zdistInf d L z : ℝ)) := mul_le_mul_of_nonneg_left hs hγ0.le
      _ = θ / 2 * Real.sqrt (zdistInf d L z : ℝ) := by rw [hγ]; field_simp
  have hprod : ∑ z : Zd d L, ∏ i, g (z i) = (∑ y : ZMod L, g y) ^ d := by
    have := Finset.prod_univ_sum (fun _ : Fin d => (Finset.univ : Finset (ZMod L)))
      (fun _ y => g y)
    rw [Fintype.piFinset_univ] at this
    rw [← this]
    simp
  have h1d := lemDecCalE_sum_zdist_le L hγ0
  calc ∑ z : Zd d L, Real.exp (-(θ / 2 * Real.sqrt (zdistInf d L z : ℝ)))
      ≤ ∑ z : Zd d L, ∏ i, g (z i) := Finset.sum_le_sum fun z _ => hpt z
    _ = (∑ y : ZMod L, g y) ^ d := hprod
    _ ≤ (1 + 96 / γ ^ 4) ^ d :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun y _ => (Real.exp_pos _).le) h1d d

/-- `baStep5IIIE_sumTheta`: `S_θ = Σ_y e^{-(θ/2)√|y|_∞} ≤ C(d, θ)` uniformly in `L`, `C(d, θ) = (1 + 96/(θ/(2d))⁴)^d
= (1 + 1536 d⁴/θ⁴)^d`. -/
theorem baStep5IIIE_sumTheta (d : ℕ) (hd : 1 ≤ d) (θ : ℝ) (hθ : 0 < θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sz : Sizes d) (n : ℕ),
      ∑ y : Zd d (sz.L n), Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) y : ℝ))) ≤ C := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨(1 + 96 / (θ / (2 * d)) ^ 4) ^ d, by positivity, fun sz n => ?_⟩
  exact Step5IIIEdet2_sum_theta_le d (sz.L n) hd hθ

/-! ## 2. Scalar facts: the shift by `6ℓ*`, the floors, the ball count, the exponent `e^{√6 Y}` -/

section Scalar2

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {u D Λ K₀ J : ℝ}

/-- The shift by `6ℓ*`: for `p ≥ r - 6ℓ*`, `T_{u,D}(p) ≤ e^{√6 Y} T_{u,D}(r)`, `Y = (log W)^{3/4}`. -/
theorem Step5IIIEdet2_shift6 (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) {r p : ℝ}
    (hp : r - 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ p) :
    tailTD d ((sz.W n : ℕ) : ℝ) u D p ≤
      Real.exp (Real.sqrt 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) * tailTD d ((sz.W n : ℕ) : ℝ) u D r := by
  have h1 := LemDecCalE_tailT_anti (d := d) (W := ((sz.W n : ℕ) : ℝ)) (u := u) (D := D) hp
  have h2 := LemDecCalE_e4c (d := d) (W := ((sz.W n : ℕ) : ℝ)) (u := u) (D := D) (C := 6)
    (Step5IIIEdet_W_gt_one hs).le (by norm_num) r
  exact h1.trans h2

/-- The near normalisation at `6ℓ*`: for `r ≤ 6ℓ*`, `τ² ≤ e^{√6 Y} T_{u,D}(r)`. -/
theorem Step5IIIEdet2_near_norm6 (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) {r : ℝ}
    (hr : r ≤ 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2)) :
    ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 ≤
      Real.exp (Real.sqrt 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) * tailTD d ((sz.W n : ℕ) : ℝ) u D r := by
  have hW0 := Step5IIIEdet_W_pos sz n
  have h := LemDecCalE_e4c (d := d) (W := ((sz.W n : ℕ) : ℝ)) (u := u) (D := D) (C := 6)
    (Step5IIIEdet_W_gt_one hs).le (by norm_num) r
  refine le_trans ?_ h
  have hneg : r - 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 0 := by linarith
  rw [Step5IIIEdet_tail_eq (Step5IIIEdet_u_lt_one hs), Real.sqrt_eq_zero_of_nonpos hneg, neg_zero, Real.exp_zero, mul_one]
  have : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  linarith

/-- `e^{√6 Y} ≥ 1` and `(e^{√6 Y})³ ≤ e^{8Y}` (`3√6 ≤ 8`). -/
theorem Step5IIIEdet2_E6_one_le (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) :
    1 ≤ Real.exp (Real.sqrt 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) :=
  Real.one_le_exp (mul_nonneg (Real.sqrt_nonneg _)
    (Real.rpow_nonneg (by linarith [Step5IIIEdet_log_ge_four hs]) _))

theorem Step5IIIEdet2_E6_cube (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) :
    (Real.exp (Real.sqrt 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4))) ^ 3 ≤
      Real.exp (8 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) := by
  have hY : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4) :=
    Real.rpow_nonneg (by linarith [Step5IIIEdet_log_ge_four hs]) _
  rw [← Real.exp_nat_mul]
  refine Real.exp_le_exp.2 ?_
  have h6 : Real.sqrt 6 ≤ 8 / 3 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  push_cast
  nlinarith

/-- The floor with the `L`-factor split off: `W^{-D} ≤ τ² ((L^d)⁻¹)²`. -/
theorem Step5IIIEdet2_floor_inv (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) :
    ((sz.W n : ℕ) : ℝ) ^ (-D) ≤ ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 * ((((sz.L n : ℕ) : ℝ) ^ d)⁻¹) ^ 2 := by
  have h := Step5IIIEdet_floor hs
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (sz.three_le_L n).trans_lt' (by norm_num)
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ (2 * d) := pow_pos hL0 _
  have e : ((((sz.L n : ℕ) : ℝ) ^ d)⁻¹) ^ 2 = (((sz.L n : ℕ) : ℝ) ^ (2 * d))⁻¹ := by
    rw [inv_pow, ← pow_mul, mul_comm]
  rw [e, ← div_eq_mul_inv, le_div_iff₀ hLd]
  exact h

/-- The ball count against the loss at the radius `3ℓ*`: `(2·3ℓ* + 1)^d ≤ (1 + log P)^{2d}`, `P = L^d W^{6d}`. -/
theorem Step5IIIEdet2_ball3_le (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) :
    (2 * (3 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2)) + 1) ^ d ≤
      (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d))) ^ (2 * d) := by
  have hlog := Step5IIIEdet_log_ge_four hs
  have hd3 := hs.1
  have hW0 := Step5IIIEdet_W_pos sz n
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (sz.three_le_L n).trans' (by norm_num)
  set x := Real.log ((sz.W n : ℕ) : ℝ) with hx
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have h1 : x ^ ((3 : ℝ) / 2) ≤ x ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le hx1 (show ((3 : ℝ) / 2) ≤ 2 by norm_num)
    simpa [Real.rpow_two] using this
  have h2 : 6 * (d : ℝ) * x ≤ Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) := by
    have hP : ((sz.W n : ℕ) : ℝ) ^ (6 * d) ≤ ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d) :=
      le_mul_of_one_le_left (pow_pos hW0 _).le (one_le_pow₀ hL1)
    have := Real.log_le_log (pow_pos hW0 _) hP
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hd3' : (3 : ℝ) ≤ d := by exact_mod_cast hd3
  have h3 : 18 * x ≤ 6 * (d : ℝ) * x := by nlinarith
  have h4 : 2 * (3 * x ^ ((3 : ℝ) / 2)) + 1 ≤ (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d))) ^ 2 := by
    have : (18 * x) ^ 2 ≤ (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d))) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    nlinarith
  calc (2 * (3 * x ^ ((3 : ℝ) / 2)) + 1) ^ d ≤ ((1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d))) ^ 2) ^ d :=
        pow_le_pow_left₀ (by positivity) h4 d
    _ = _ := by rw [← pow_mul]

end Scalar2

/-! ## 3. The legs of the six-loops of `res_deccalE_dif` -/

section Legs2

variable {d : ℕ} {sz : Sizes d} {lam0 E : ℕ → ℝ} {n : ℕ} {u D Λ K₀ J θ Cd : ℝ}
  {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- The `(+,-)` leg at distance `≥ ℓ*` through (vi) and (iii): `‖𝓛‖ ≤ ‖𝓛-𝒦‖ + ‖𝒦‖ ≤ W^{θd(Cd+1)} Λ τ² e^{-θ√r} + 2W^{-D}`. -/
theorem Step5IIIEdet2_leg_plus_dec (hm : BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ J θ Cd H) (x y : Zd d (sz.L n))
    (h : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (x - y) : ℝ)) :
    ‖(baStep2Mat sz lam0 E).LM n u H ![true, false] ![x, y]‖ ≤
      ((sz.W n : ℕ) : ℝ) ^ (θ * (d * (Cd + 1))) * Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 *
        Real.exp (-(θ * Real.sqrt (zdistInf d (sz.L n) (x - y) : ℝ))) + 2 * ((sz.W n : ℕ) : ℝ) ^ (-D) := by
  have e : (baStep2Mat sz lam0 E).LM n u H ![true, false] ![x, y] =
      STLKMg (baStep2Mat sz lam0 E) n u H ![true, false] ![x, y] + (baStep2Mat sz lam0 E).K n u ![true, false] ![x, y] := by
    simp [STLKMg, STLMg]
  rw [e]
  have h1 : ‖STLKMg (baStep2Mat sz lam0 E) n u H ![true, false] ![x, y]‖ ≤
      ((sz.W n : ℕ) : ℝ) ^ (θ * (d * (Cd + 1))) * Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 *
        Real.exp (-(θ * Real.sqrt (zdistInf d (sz.L n) (x - y) : ℝ))) + ((sz.W n : ℕ) : ℝ) ^ (-D) := by
    simpa using hm.2.2.2.2.2.2.2.2.2 ![true, false] ![x, y]
  have h2 := hm.2.2.2.1 x y h
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

/-- Every leg at distance `≥ ℓ*`, charge `(σ, !σ)` (swap for `(-,+)`):
`‖𝓛‖ ≤ W^{θd(Cd+1)} Λ τ² (e^{-(θ/2)√r} + 2 (L^d)⁻¹)²` (the floor `W^{-D} ≤ τ² ((L^d)⁻¹)²`, `W^{θd(Cd+1)} Λ ≥ 1`). -/
theorem Step5IIIEdet2_leg_dec (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) (hθ : 0 < θ) (hCd : 0 < Cd)
    (hm : BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ J θ Cd H) (σ : Bool) (x y : Zd d (sz.L n))
    (h : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (x - y) : ℝ)) :
    ‖(baStep2Mat sz lam0 E).LM n u H ![σ, !σ] ![x, y]‖ ≤
      (((sz.W n : ℕ) : ℝ) ^ (θ * (d * (Cd + 1))) * Λ) * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 *
        (Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) (x - y) : ℝ))) + 2 * (((sz.L n : ℕ) : ℝ) ^ d)⁻¹) ^ 2 := by
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := (Step5IIIEdet_W_gt_one hs).le
  have hΛ := Step5IIIEdet_one_le_Λ hs
  have ha2 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (θ * (d * (Cd + 1))) * Λ :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hW1 (by positivity)) hΛ
  have hfl := Step5IIIEdet2_floor_inv hs
  have key : ∀ x y : Zd d (sz.L n), Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (x - y) : ℝ) →
      ‖(baStep2Mat sz lam0 E).LM n u H ![true, false] ![x, y]‖ ≤
        (((sz.W n : ℕ) : ℝ) ^ (θ * (d * (Cd + 1))) * Λ) * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 *
          (Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) (x - y) : ℝ))) + 2 * (((sz.L n : ℕ) : ℝ) ^ d)⁻¹) ^ 2 := by
    intro x y h
    refine (Step5IIIEdet2_leg_plus_dec hm x y h).trans ?_
    set a2 := ((sz.W n : ℕ) : ℝ) ^ (θ * (d * (Cd + 1))) * Λ with ha2def
    set τ := (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ with hτ
    set e := Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) (x - y) : ℝ))) with he
    set lam := (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ with hlam
    have he0 : 0 ≤ e := (Real.exp_pos _).le
    have hl0 : 0 ≤ lam := by positivity
    have hee : Real.exp (-(θ * Real.sqrt (zdistInf d (sz.L n) (x - y) : ℝ))) = e ^ 2 := by
      rw [he, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hτ0 : 0 ≤ τ ^ 2 := sq_nonneg _
    have e1 : a2 * τ ^ 2 * Real.exp (-(θ * Real.sqrt (zdistInf d (sz.L n) (x - y) : ℝ))) = a2 * τ ^ 2 * e ^ 2 := by
      rw [hee]
    have e2 : (((sz.W n : ℕ) : ℝ) ^ (θ * (d * (Cd + 1))) * Λ * τ ^ 2 *
        Real.exp (-(θ * Real.sqrt (zdistInf d (sz.L n) (x - y) : ℝ)))) = a2 * τ ^ 2 * e ^ 2 := by
      rw [← ha2def]; exact e1
    rw [e2]
    have h3 : 2 * ((sz.W n : ℕ) : ℝ) ^ (-D) ≤ 2 * (τ ^ 2 * lam ^ 2) := by linarith
    have h4 : 2 * (τ ^ 2 * lam ^ 2) ≤ a2 * τ ^ 2 * (2 * lam ^ 2) := by
      have : 0 ≤ τ ^ 2 * (2 * lam ^ 2) := by positivity
      nlinarith
    have h5 : a2 * τ ^ 2 * e ^ 2 + a2 * τ ^ 2 * (2 * lam ^ 2) ≤ a2 * τ ^ 2 * (e + 2 * lam) ^ 2 := by
      have : 0 ≤ a2 * τ ^ 2 := by positivity
      have h6 : e ^ 2 + 2 * lam ^ 2 ≤ (e + 2 * lam) ^ 2 := by nlinarith [mul_nonneg he0 hl0, sq_nonneg lam]
      nlinarith
    linarith
  cases σ
  · simp only [Bool.not_false]
    rw [Step5IIIEdet_swap sz lam0 E n u H false true x y]
    have h' : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (y - x) : ℝ) := by
      rwa [lemDecCalE_zdistInf_sub_comm]
    have := key y x h'
    rwa [lemDecCalE_zdistInf_sub_comm] at this
  · simpa using key x y h

/-- A long leg with a shift: for `δ = |x-y| ≥ ℓ*` and `δ ≥ r - 6ℓ*`, `‖𝓛^{(2)}_{(σ,!σ),(x,y)}‖ ≤ 2 J e^{√6 Y} T_{u,D}(r)`. -/
theorem Step5IIIEdet2_leg_far (hs : BAStep5IIIEScalar sz n u D Λ K₀ J)
    (hm : BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ J θ Cd H) (σ : Bool) (x y : Zd d (sz.L n)) {r : ℝ}
    (hl : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (x - y) : ℝ))
    (hsh : r - 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ (zdistInf d (sz.L n) (x - y) : ℝ)) :
    ‖(baStep2Mat sz lam0 E).LM n u H ![σ, !σ] ![x, y]‖ ≤
      2 * J * (Real.exp (Real.sqrt 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) * tailTD d ((sz.W n : ℕ) : ℝ) u D r) := by
  have hJ := Step5IIIEdet_one_le_J hs
  exact (Step5IIIEdet_leg_long hs hm σ x y hl).trans
    (mul_le_mul_of_nonneg_left (Step5IIIEdet2_shift6 hs hsh) (by linarith : (0 : ℝ) ≤ 2 * J))

/-- The six legs of the `res_deccalE_dif` loop with blocks `(a₀, a₁, c, a₁', a₀', c)` (Hilbert-Schmidt bound at `k = 6`). -/
theorem Step5IIIEdet2_hs6 (hH : H.IsHermitian) (σ0 σ1 : Bool) (a0 a1 a0' a1' c : Zd d (sz.L n)) :
    ‖(baStep2Mat sz lam0 E).LM n u H ![σ0, σ1, σ0, !σ0, !σ1, !σ0] ![a0, a1, c, a1', a0', c]‖ ≤
      Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![σ0, !σ0] ![a0, c]‖ *
        Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![σ1, !σ1] ![a1, a0]‖ *
        Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![σ0, !σ0] ![c, a1]‖ *
        Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![!σ0, !(!σ0)] ![a1', c]‖ *
        Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![!σ1, !(!σ1)] ![a0', a1']‖ *
        Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![!σ0, !(!σ0)] ![c, a0']‖ := by
  have h := baStep5IIIE_loop_hs d sz lam0 E n u H hH 6 ![σ0, σ1, σ0, !σ0, !σ1, !σ0] ![a0, a1, c, a1', a0', c] (by norm_num)
  have e0 : (finRotate 6).symm 0 = 5 := by decide
  have e1 : (finRotate 6).symm 1 = 0 := by decide
  have e2 : (finRotate 6).symm 2 = 1 := by decide
  have e3 : (finRotate 6).symm 3 = 2 := by decide
  have e4 : (finRotate 6).symm 4 = 3 := by decide
  have e5 : (finRotate 6).symm 5 = 4 := by decide
  simpa [Fin.prod_univ_six, e0, e1, e2, e3, e4, e5] using h

end Legs2

section Glue2

variable {d : ℕ} {sz : Sizes d} {lam0 E : ℕ → ℝ} {n : ℕ} {u D Λ K₀ J θ Cd : ℝ}
  {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- The glue at the two legs meeting at `c` on the `a₀` side (positions `5, 0`): the 4-loop `Y` is bounded by (v) at `k = 4`. -/
theorem Step5IIIEdet2_glue5 (hm : BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ J θ Cd H) (σ0 σ1 : Bool)
    (a0 a1 a0' a1' c : Zd d (sz.L n)) :
    ‖(baStep2Mat sz lam0 E).LM n u H ![σ0, σ1, σ0, !σ0, !σ1, !σ0] ![a0, a1, c, a1', a0', c]‖ ≤
      Real.sqrt (Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 3) *
        (Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![σ1, !σ1] ![a1, a0]‖ *
          Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![σ0, !σ0] ![c, a1]‖ *
          Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![!σ0, !(!σ0)] ![a1', c]‖ *
          Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![!σ1, !(!σ1)] ![a0', a1']‖) := by
  have h := baStep5IIIE_loop_glue d sz lam0 E n u H hm.1 ![σ0, σ1, σ0, !σ0, !σ1, !σ0] ![a0, a1, c, a1', a0', c] 5
  have hY := hm.2.2.2.2.2.2.2.1 ![!σ0, σ0, !σ0, σ0] ![c, a0, c, a0']
  have e1 : ((5 : Fin 6) + 1) = 0 := by decide
  have e2 : ((5 : Fin 6) - 1) = 4 := by decide
  have e3 : ((5 : Fin 6) + 2) = 1 := by decide
  have e4 : ((5 : Fin 6) + 3) = 2 := by decide
  have e5 : ((5 : Fin 6) + 4) = 3 := by decide
  have e6 : ((5 : Fin 6) + 5) = 4 := by decide
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val, e1, Matrix.cons_val_zero, Bool.not_not,
    e2, Finset.mem_insert, Fin.reduceEq, Finset.mem_singleton, or_self, not_false_eq_true, Finset.prod_insert, e3,
    Matrix.cons_val_one, sub_self, e4, Fin.reduceSub, e5, Finset.prod_singleton, e6] at h
  simp only [Bool.not_not]
  calc _ ≤ _ := h
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hY)
      (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))))
    _ = _ := by ring

/-- The glue at the two legs meeting at `c` on the `a₁` side (positions `2, 3`). -/
theorem Step5IIIEdet2_glue2 (hm : BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ J θ Cd H) (σ0 σ1 : Bool)
    (a0 a1 a0' a1' c : Zd d (sz.L n)) :
    ‖(baStep2Mat sz lam0 E).LM n u H ![σ0, σ1, σ0, !σ0, !σ1, !σ0] ![a0, a1, c, a1', a0', c]‖ ≤
      Real.sqrt (Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 3) *
        (Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![!σ1, !(!σ1)] ![a0', a1']‖ *
          Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![!σ0, !(!σ0)] ![c, a0']‖ *
          Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![σ0, !σ0] ![a0, c]‖ *
          Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![σ1, !σ1] ![a1, a0]‖) := by
  have h := baStep5IIIE_loop_glue d sz lam0 E n u H hm.1 ![σ0, σ1, σ0, !σ0, !σ1, !σ0] ![a0, a1, c, a1', a0', c] 2
  have hY := hm.2.2.2.2.2.2.2.1 ![σ0, !σ0, σ0, !σ0] ![c, a1', c, a1]
  have e1 : ((2 : Fin 6) + 1) = 3 := by decide
  have e2 : ((2 : Fin 6) - 1) = 1 := by decide
  have e3 : ((2 : Fin 6) + 2) = 4 := by decide
  have e4 : ((2 : Fin 6) + 3) = 5 := by decide
  have e5 : ((2 : Fin 6) + 4) = 0 := by decide
  have e6 : ((2 : Fin 6) + 5) = 1 := by decide
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val, e1, Bool.not_not, e2, Matrix.cons_val_one,
    Matrix.cons_val_zero, Finset.mem_insert, Fin.reduceEq, Finset.mem_singleton, or_self, not_false_eq_true,
    Finset.prod_insert, e3, Fin.reduceSub, e4, e5, zero_sub, Finset.prod_singleton, e6, sub_self] at h
  simp only [Bool.not_not]
  calc _ ≤ _ := h
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hY)
      (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))))
    _ = _ := by ring

end Glue2

/-! ## 4. The bridge `STeeMg` to explicit six-loops, and the real-number combinators of the pointwise bounds -/

section Bridge

/-- `STeeMg` at `m = 2`, `S = 1`: `W^d Σ_c (𝓛^{(6)} + 𝓛^{(6)})` with the blocks `(a₀,a₁,c,a₁',a₀',c)` and `(a₁,a₀,c,a₀',a₁',c)` (`STeeLoop`, `Induction/Step34Pins`, at
`k = 1, 2`; `S` is the identity matrix, `baStep2Mat`). -/
theorem Step5IIIEdet2_STeeMg_eq {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)) :
    STeeMg (baStep2Mat sz lam0 E) n u H σ a a' = (((sz.W n : ℕ) : ℂ) ^ d) * ∑ c : Zd d (sz.L n),
      ((baStep2Mat sz lam0 E).LM n u H ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a 0, a 1, c, a' 1, a' 0, c] +
        (baStep2Mat sz lam0 E).LM n u H ![σ 1, σ 0, σ 1, !(σ 1), !(σ 0), !(σ 1)] ![a 1, a 0, c, a' 0, a' 1, c]) := by
  have key : ∀ {m : ℕ} (σ' : Fin m → Bool) (a' : Fin m → Zd d (sz.L n)),
      STLIMg (baStep2Mat sz lam0 E) n u H ⟨List.ofFn σ', List.ofFn a'⟩ = (baStep2Mat sz lam0 E).LM n u H σ' a' :=
    fun σ' a' => (loopM_eq_loopL _ _ _ _ _ _ _).symm
  have hS : (baStep2Mat sz lam0 E).S n = 1 := rfl
  have h12 : Finset.Icc 1 2 = {1, 2} := by decide
  have e1 : ∀ c : Zd d (sz.L n), STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') 1 c c =
      ⟨List.ofFn ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)], List.ofFn ![a 0, a 1, c, a' 1, a' 0, c]⟩ := fun c => by
    simp [STeeLoop, List.ofFn_succ]
  have e2 : ∀ c : Zd d (sz.L n), STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') 2 c c =
      ⟨List.ofFn ![σ 1, σ 0, σ 1, !(σ 1), !(σ 0), !(σ 1)], List.ofFn ![a 1, a 0, c, a' 0, a' 1, c]⟩ := fun c => by
    simp [STeeLoop, List.ofFn_succ]
  unfold STeeMg
  congr 1
  rw [Finset.sum_comm, h12]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_pair (by decide)]
  simp only [hS, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [e1, e2, key, key]

end Bridge

section RealPt

/-- `√g ≤ √a₂ · τ (e + 2λ)` from `g ≤ a₂ τ² (e + 2λ)²`. -/
theorem Step5IIIEdet2_sqrt_leg {g a2 τ e lam : ℝ} (ha2 : 0 ≤ a2) (hτ : 0 ≤ τ) (he : 0 ≤ e) (hl : 0 ≤ lam)
    (h : g ≤ a2 * τ ^ 2 * (e + 2 * lam) ^ 2) : Real.sqrt g ≤ Real.sqrt a2 * (τ * (e + 2 * lam)) := by
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt ha2]
  refine h.trans (le_of_eq ?_)
  ring

/-- Case B, pointwise: two short legs `≤ Λτ` and four long legs `≤ a₂ τ² (e + 2λ)²`; only the leg `0` keeps its decay. -/
theorem Step5IIIEdet2_pt_B {g0 g1 g2 g3 g4 g5 Λ τ a2 lam e0 e2 e3 e5 : ℝ} (hΛ : 1 ≤ Λ) (hτ : 0 < τ) (ha2 : 1 ≤ a2)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (he0 : 0 ≤ e0) (he2 : 0 ≤ e2) (he3 : 0 ≤ e3) (he5 : 0 ≤ e5)
    (he2' : e2 ≤ 1) (he3' : e3 ≤ 1) (he5' : e5 ≤ 1)
    (h0 : g0 ≤ a2 * τ ^ 2 * (e0 + 2 * lam) ^ 2) (h1 : g1 ≤ Λ * τ)
    (h2 : g2 ≤ a2 * τ ^ 2 * (e2 + 2 * lam) ^ 2) (h3 : g3 ≤ a2 * τ ^ 2 * (e3 + 2 * lam) ^ 2)
    (h4 : g4 ≤ Λ * τ) (h5 : g5 ≤ a2 * τ ^ 2 * (e5 + 2 * lam) ^ 2) :
    Real.sqrt g0 * Real.sqrt g1 * Real.sqrt g2 * Real.sqrt g3 * Real.sqrt g4 * Real.sqrt g5 ≤
      (Λ * τ) * (a2 ^ 2 * τ ^ 4 * (27 * (e0 + 2 * lam))) := by
  have ha20 : 0 ≤ a2 := by linarith
  have hΛτ : 0 ≤ Λ * τ := by nlinarith
  set s := Real.sqrt a2 with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = a2 := Real.sq_sqrt ha20
  have b0 := Step5IIIEdet2_sqrt_leg ha20 hτ.le he0 hlam h0
  have b2 := Step5IIIEdet2_sqrt_leg ha20 hτ.le he2 hlam h2
  have b3 := Step5IIIEdet2_sqrt_leg ha20 hτ.le he3 hlam h3
  have b5 := Step5IIIEdet2_sqrt_leg ha20 hτ.le he5 hlam h5
  have b14 : Real.sqrt g1 * Real.sqrt g4 ≤ Λ * τ := by
    calc Real.sqrt g1 * Real.sqrt g4 ≤ Real.sqrt (Λ * τ) * Real.sqrt (Λ * τ) :=
          mul_le_mul (Real.sqrt_le_sqrt h1) (Real.sqrt_le_sqrt h4) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Λ * τ := Real.mul_self_sqrt hΛτ
  have c2 : e2 + 2 * lam ≤ 3 := by linarith
  have c3 : e3 + 2 * lam ≤ 3 := by linarith
  have c5 : e5 + 2 * lam ≤ 3 := by linarith
  have n0 : 0 ≤ e0 + 2 * lam := by linarith
  have n2 : 0 ≤ e2 + 2 * lam := by linarith
  have n3 : 0 ≤ e3 + 2 * lam := by linarith
  have n5 : 0 ≤ e5 + 2 * lam := by linarith
  calc Real.sqrt g0 * Real.sqrt g1 * Real.sqrt g2 * Real.sqrt g3 * Real.sqrt g4 * Real.sqrt g5
      = (Real.sqrt g0 * Real.sqrt g2 * Real.sqrt g3 * Real.sqrt g5) * (Real.sqrt g1 * Real.sqrt g4) := by ring
    _ ≤ ((s * (τ * (e0 + 2 * lam))) * (s * (τ * (e2 + 2 * lam))) * (s * (τ * (e3 + 2 * lam))) *
          (s * (τ * (e5 + 2 * lam)))) * (Λ * τ) := by
        refine mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul b0 b2 (Real.sqrt_nonneg _) (by positivity)) b3
          (Real.sqrt_nonneg _) (by positivity)) b5 (Real.sqrt_nonneg _) (by positivity)) b14
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (by positivity)
    _ = (Λ * τ) * (s ^ 4 * τ ^ 4 * ((e0 + 2 * lam) * (e2 + 2 * lam) * (e3 + 2 * lam) * (e5 + 2 * lam))) := by ring
    _ ≤ (Λ * τ) * (a2 ^ 2 * τ ^ 4 * (27 * (e0 + 2 * lam))) := by
        refine mul_le_mul_of_nonneg_left ?_ hΛτ
        have h4s : s ^ 4 = a2 ^ 2 := by rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hss]
        rw [h4s]
        have hprod : (e2 + 2 * lam) * (e3 + 2 * lam) * (e5 + 2 * lam) ≤ 27 := by
          calc (e2 + 2 * lam) * (e3 + 2 * lam) * (e5 + 2 * lam) ≤ 3 * 3 * 3 :=
                mul_le_mul (mul_le_mul c2 c3 n3 (by norm_num)) c5 n5 (by norm_num)
            _ = 27 := by norm_num
        have h00 : 0 ≤ a2 ^ 2 * τ ^ 4 * (e0 + 2 * lam) := by positivity
        calc a2 ^ 2 * τ ^ 4 * ((e0 + 2 * lam) * (e2 + 2 * lam) * (e3 + 2 * lam) * (e5 + 2 * lam))
            = (a2 ^ 2 * τ ^ 4 * (e0 + 2 * lam)) * ((e2 + 2 * lam) * (e3 + 2 * lam) * (e5 + 2 * lam)) := by ring
          _ ≤ (a2 ^ 2 * τ ^ 4 * (e0 + 2 * lam)) * 27 := mul_le_mul_of_nonneg_left hprod h00
          _ = _ := by ring

/-- Case D, a pair of legs: `√g √g' ≤ 2 J E T` when `g ≤ 2 J T` and `g' ≤ 2 J (E T)`. -/
theorem Step5IIIEdet2_pt_pair {g g' T E J : ℝ} (hJ : 1 ≤ J) (hE : 1 ≤ E) (hT : 0 ≤ T)
    (h : g ≤ 2 * J * T) (h' : g' ≤ 2 * J * (E * T)) : Real.sqrt g * Real.sqrt g' ≤ 2 * J * E * T := by
  have hM : 0 ≤ 2 * J * T := by nlinarith
  calc Real.sqrt g * Real.sqrt g' ≤ Real.sqrt (2 * J * T) * Real.sqrt (2 * J * (E * T)) :=
        mul_le_mul (Real.sqrt_le_sqrt h) (Real.sqrt_le_sqrt h') (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt ((2 * J * T) * (2 * J * (E * T))) := (Real.sqrt_mul hM _).symm
    _ = Real.sqrt ((2 * J * T) ^ 2 * E) := by congr 1; ring
    _ = (2 * J * T) * Real.sqrt E := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hM]
    _ ≤ (2 * J * T) * E := mul_le_mul_of_nonneg_left (Step5IIIEdet_sqrt_le_self hE) hM
    _ = 2 * J * E * T := by ring

/-- Case D, the six legs, in three pairs `(0,5)`, `(2,3)`, `(1,4)`. -/
theorem Step5IIIEdet2_pt_D {g0 g1 g2 g3 g4 g5 T0 T2 Tr E J : ℝ} (hJ : 1 ≤ J) (hE : 1 ≤ E)
    (hT0 : 0 ≤ T0) (hT2 : 0 ≤ T2) (hTr : 0 ≤ Tr)
    (h0 : g0 ≤ 2 * J * T0) (h5 : g5 ≤ 2 * J * (E * T0)) (h2 : g2 ≤ 2 * J * T2) (h3 : g3 ≤ 2 * J * (E * T2))
    (h1 : g1 ≤ 2 * J * Tr) (h4 : g4 ≤ 2 * J * (E * Tr)) :
    Real.sqrt g0 * Real.sqrt g1 * Real.sqrt g2 * Real.sqrt g3 * Real.sqrt g4 * Real.sqrt g5 ≤
      ((2 * J * E) ^ 3 * Tr) * (T2 * T0) := by
  have p05 := Step5IIIEdet2_pt_pair hJ hE hT0 h0 h5
  have p23 := Step5IIIEdet2_pt_pair hJ hE hT2 h2 h3
  have p14 := Step5IIIEdet2_pt_pair hJ hE hTr h1 h4
  have hJE : 0 ≤ 2 * J * E := by nlinarith
  calc Real.sqrt g0 * Real.sqrt g1 * Real.sqrt g2 * Real.sqrt g3 * Real.sqrt g4 * Real.sqrt g5
      = (Real.sqrt g0 * Real.sqrt g5) * (Real.sqrt g2 * Real.sqrt g3) * (Real.sqrt g1 * Real.sqrt g4) := by ring
    _ ≤ (2 * J * E * T0) * (2 * J * E * T2) * (2 * J * E * Tr) :=
        mul_le_mul (mul_le_mul p05 p23 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (by positivity)) p14
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (by positivity)
    _ = ((2 * J * E) ^ 3 * Tr) * (T2 * T0) := by ring

/-- Case C, the four legs outside the glued pair: each `≤ M`, so the product of the square roots is `≤ M²`. -/
theorem Step5IIIEdet2_pt_four {g1 g2 g3 g4 M : ℝ} (hM : 0 ≤ M) (h1 : g1 ≤ M) (h2 : g2 ≤ M) (h3 : g3 ≤ M) (h4 : g4 ≤ M) :
    Real.sqrt g1 * Real.sqrt g2 * Real.sqrt g3 * Real.sqrt g4 ≤ M ^ 2 := by
  have hsq : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hM
  calc Real.sqrt g1 * Real.sqrt g2 * Real.sqrt g3 * Real.sqrt g4
      ≤ Real.sqrt M * Real.sqrt M * Real.sqrt M * Real.sqrt M := by
        refine mul_le_mul (mul_le_mul (mul_le_mul (Real.sqrt_le_sqrt h1) (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)) (Real.sqrt_le_sqrt h3) (Real.sqrt_nonneg _) (by positivity)) (Real.sqrt_le_sqrt h4)
          (Real.sqrt_nonneg _) (by positivity)
    _ = (Real.sqrt M * Real.sqrt M) * (Real.sqrt M * Real.sqrt M) := by ring
    _ = M ^ 2 := by rw [hsq]; ring

end RealPt

/-! ## 5. The pointwise bounds of the six-loop, cases (A)-(D) -/

section Pointwise

variable {d : ℕ} {sz : Sizes d} {lam0 E : ℕ → ℝ} {n : ℕ} {u D Λ K₀ J θ Cd : ℝ}
  {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- Case (A), any `c`: the six-loop is `≤ Λ τ⁵` (bundle (v), `k = 6`). -/
theorem Step5IIIEdet2_loop_A (hm : BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ J θ Cd H) (σ0 σ1 : Bool)
    (a0 a1 a0' a1' c : Zd d (sz.L n)) :
    ‖(baStep2Mat sz lam0 E).LM n u H ![σ0, σ1, σ0, !σ0, !σ1, !σ0] ![a0, a1, c, a1', a0', c]‖ ≤
      Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 5 :=
  hm.2.2.2.2.2.2.2.2.1 _ _

/-- Case (B), `c` at distance `> 3ℓ*` from `a₀` and `a₁`, near cut `2ℓ*`: two short legs and four long legs with (vi);
only the leg `(a₀, c)` keeps its decay. -/
theorem Step5IIIEdet2_loop_B (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) (hθ : 0 < θ) (hCd : 0 < Cd)
    (hm : BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ J θ Cd H) (σ0 σ1 : Bool) (a0 a1 a0' a1' c : Zd d (sz.L n))
    (hn0 : (zdistInf d (sz.L n) (a0 - a0') : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ))
    (hn1 : (zdistInf d (sz.L n) (a1 - a1') : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ))
    (hc0 : 3 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) < (zdistInf d (sz.L n) (a0 - c) : ℝ))
    (hc1 : 3 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) < (zdistInf d (sz.L n) (a1 - c) : ℝ)) :
    ‖(baStep2Mat sz lam0 E).LM n u H ![σ0, σ1, σ0, !σ0, !σ1, !σ0] ![a0, a1, c, a1', a0', c]‖ ≤
      (Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) *
        ((((sz.W n : ℕ) : ℝ) ^ (θ * (d * (Cd + 1))) * Λ) ^ 2 * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 4 *
          (27 * (Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) (a0 - c) : ℝ))) + 2 * (((sz.L n : ℕ) : ℝ) ^ d)⁻¹))) := by
  have hℓ0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg (by linarith [Step5IIIEdet_log_ge_four hs]) _
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := (Step5IIIEdet_W_gt_one hs).le
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (sz.three_le_L n).trans' (by norm_num)
  have hΛ := Step5IIIEdet_one_le_Λ hs
  obtain ⟨hτ0, -⟩ := Step5IIIEdet_tau_le_one hs
  have ha2 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (θ * (d * (Cd + 1))) * Λ :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hW1 (by positivity)) hΛ
  have hlam0 : 0 ≤ (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  have hlam1 : (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
  have sc : ∀ x y : Zd d (sz.L n), (zdistInf d (sz.L n) (x - y) : ℝ) = (zdistInf d (sz.L n) (y - x) : ℝ) :=
    fun x y => by rw [lemDecCalE_zdistInf_sub_comm]
  have t1 := lemDecCalE_zdistInf_tri_real d (sz.L n) a1 a1' c
  have t2 := lemDecCalE_zdistInf_tri_real d (sz.L n) a0 a0' c
  have d3 : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (a1' - c) : ℝ) := by linarith
  have d5 : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (c - a0') : ℝ) := by
    rw [sc c a0']; linarith
  have d2 : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (c - a1) : ℝ) := by
    rw [sc c a1]; linarith
  have d0 : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (a0 - c) : ℝ) := by linarith
  have eexp : ∀ x y : Zd d (sz.L n), 0 ≤ Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) (x - y) : ℝ))) ∧
      Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) (x - y) : ℝ))) ≤ 1 := fun x y =>
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (neg_nonpos.2 (by positivity))⟩
  refine (Step5IIIEdet2_hs6 hm.1 σ0 σ1 a0 a1 a0' a1' c).trans ?_
  exact Step5IIIEdet2_pt_B hΛ hτ0 ha2 hlam0 hlam1 (eexp a0 c).1 (eexp c a1).1 (eexp a1' c).1 (eexp c a0').1
    (eexp c a1).2 (eexp a1' c).2 (eexp c a0').2
    (Step5IIIEdet2_leg_dec hs hθ hCd hm σ0 a0 c d0) (Step5IIIEdet_leg_short hm σ1 a1 a0)
    (Step5IIIEdet2_leg_dec hs hθ hCd hm σ0 c a1 d2) (Step5IIIEdet2_leg_dec hs hθ hCd hm (!σ0) a1' c d3)
    (Step5IIIEdet_leg_short hm (!σ1) a0' a1') (Step5IIIEdet2_leg_dec hs hθ hCd hm (!σ0) c a0' d5)

end Pointwise

section Pointwise2

variable {d : ℕ} {sz : Sizes d} {lam0 E : ℕ → ℝ} {n : ℕ} {u D Λ K₀ J θ Cd : ℝ}
  {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- Case (C), `r > 6ℓ*`, `c` within `3ℓ*` of `a₀` or of `a₁`: glue the two legs at `c` (their 4-loop is `≤ Λ τ³` by (v), `k = 4`); the four
other legs are long, at distance `≥ r - 5ℓ*`, each `≤ 2 J e^{√6 Y} T(r)`. -/
theorem Step5IIIEdet2_loop_C (hs : BAStep5IIIEScalar sz n u D Λ K₀ J)
    (hm : BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ J θ Cd H) (σ0 σ1 : Bool) (a0 a1 a0' a1' c : Zd d (sz.L n))
    (hr : 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) < (zdistInf d (sz.L n) (a0 - a1) : ℝ))
    (hn0 : (zdistInf d (sz.L n) (a0 - a0') : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ))
    (hn1 : (zdistInf d (sz.L n) (a1 - a1') : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ))
    (hball : (zdistInf d (sz.L n) (a0 - c) : ℝ) ≤ 3 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ∨
      (zdistInf d (sz.L n) (a1 - c) : ℝ) ≤ 3 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) :
    ‖(baStep2Mat sz lam0 E).LM n u H ![σ0, σ1, σ0, !σ0, !σ1, !σ0] ![a0, a1, c, a1', a0', c]‖ ≤
      Real.sqrt (Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 3) *
        (2 * J * (Real.exp (Real.sqrt 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) *
          tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a0 - a1) : ℝ))) ^ 2 := by
  have hℓ0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg (by linarith [Step5IIIEdet_log_ge_four hs]) _
  have hJ := Step5IIIEdet_one_le_J hs
  have hE6 := Step5IIIEdet2_E6_one_le hs
  have hT : 0 ≤ tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a0 - a1) : ℝ) :=
    tailTD_nonneg (Step5IIIEdet_W_pos sz n).le
  have hM : 0 ≤ 2 * J * (Real.exp (Real.sqrt 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) *
      tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a0 - a1) : ℝ)) :=
    mul_nonneg (by linarith) (mul_nonneg (by linarith) hT)
  have sc : ∀ x y : Zd d (sz.L n), (zdistInf d (sz.L n) (x - y) : ℝ) = (zdistInf d (sz.L n) (y - x) : ℝ) :=
    fun x y => by rw [lemDecCalE_zdistInf_sub_comm]
  have f4 : (zdistInf d (sz.L n) (a0 - a1) : ℝ) - 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤
      (zdistInf d (sz.L n) (a0' - a1') : ℝ) ∧
      Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (a0' - a1') : ℝ) := by
    have t1 := lemDecCalE_zdistInf_tri_real d (sz.L n) a0 a0' a1
    have t2 := lemDecCalE_zdistInf_tri_real d (sz.L n) a0' a1' a1
    have s1 := sc a1' a1
    constructor <;> linarith
  have f1 : (zdistInf d (sz.L n) (a0 - a1) : ℝ) - 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤
      (zdistInf d (sz.L n) (a1 - a0) : ℝ) ∧
      Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (a1 - a0) : ℝ) := by
    have s1 := sc a1 a0
    constructor <;> linarith
  rcases hball with h | h
  · -- `c` within `3ℓ*` of `a₀`: glue the legs `5, 0`
    have t3 := lemDecCalE_zdistInf_tri_real d (sz.L n) a0 c a1
    have t4 := lemDecCalE_zdistInf_tri_real d (sz.L n) a1 a1' c
    have s2 := sc c a1
    have s3 := sc a1 c
    have f2 : (zdistInf d (sz.L n) (a0 - a1) : ℝ) - 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤
        (zdistInf d (sz.L n) (c - a1) : ℝ) ∧
        Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (c - a1) : ℝ) := by
        constructor <;> linarith
    have f3 : (zdistInf d (sz.L n) (a0 - a1) : ℝ) - 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤
        (zdistInf d (sz.L n) (a1' - c) : ℝ) ∧
        Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (a1' - c) : ℝ) := by
        constructor <;> linarith
    refine (Step5IIIEdet2_glue5 hm σ0 σ1 a0 a1 a0' a1' c).trans ?_
    refine mul_le_mul_of_nonneg_left (Step5IIIEdet2_pt_four hM ?_ ?_ ?_ ?_) (Real.sqrt_nonneg _)
    · exact Step5IIIEdet2_leg_far hs hm σ1 a1 a0 f1.2 f1.1
    · exact Step5IIIEdet2_leg_far hs hm σ0 c a1 f2.2 f2.1
    · exact Step5IIIEdet2_leg_far hs hm (!σ0) a1' c f3.2 f3.1
    · exact Step5IIIEdet2_leg_far hs hm (!σ1) a0' a1' f4.2 f4.1
  · -- `c` within `3ℓ*` of `a₁`: glue the legs `2, 3`
    have t3 := lemDecCalE_zdistInf_tri_real d (sz.L n) a0 c a1
    have t4 := lemDecCalE_zdistInf_tri_real d (sz.L n) a0 a0' c
    have s2 := sc c a0'
    have s3 := sc a1 c
    have f2 : (zdistInf d (sz.L n) (a0 - a1) : ℝ) - 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤
        (zdistInf d (sz.L n) (a0 - c) : ℝ) ∧
        Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (a0 - c) : ℝ) := by
        constructor <;> linarith
    have f3 : (zdistInf d (sz.L n) (a0 - a1) : ℝ) - 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤
        (zdistInf d (sz.L n) (c - a0') : ℝ) ∧
        Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (c - a0') : ℝ) := by
        constructor <;> linarith
    refine (Step5IIIEdet2_glue2 hm σ0 σ1 a0 a1 a0' a1' c).trans ?_
    refine mul_le_mul_of_nonneg_left (Step5IIIEdet2_pt_four hM ?_ ?_ ?_ ?_) (Real.sqrt_nonneg _)
    · exact Step5IIIEdet2_leg_far hs hm (!σ1) a0' a1' f4.2 f4.1
    · exact Step5IIIEdet2_leg_far hs hm (!σ0) c a0' f3.2 f3.1
    · exact Step5IIIEdet2_leg_far hs hm σ0 a0 c f2.2 f2.1
    · exact Step5IIIEdet2_leg_far hs hm σ1 a1 a0 f1.2 f1.1

end Pointwise2

section Pointwise3

variable {d : ℕ} {sz : Sizes d} {lam0 E : ℕ → ℝ} {n : ℕ} {u D Λ K₀ J θ Cd : ℝ}
  {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- Case (D), `r > 6ℓ*`, `c` farther than `3ℓ*` from `a₀` and `a₁`: all six legs are long; the pairs `(a₀,c), (c,a₀')`, `(c,a₁), (a₁',c)`,
`(a₁,a₀), (a₀',a₁')` give `(2 J e^{√6 Y})³ T(r) · T(|c-a₁|) T(|a₀-c|)`. -/
theorem Step5IIIEdet2_loop_D (hs : BAStep5IIIEScalar sz n u D Λ K₀ J)
    (hm : BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ J θ Cd H) (σ0 σ1 : Bool) (a0 a1 a0' a1' c : Zd d (sz.L n))
    (hr : 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) < (zdistInf d (sz.L n) (a0 - a1) : ℝ))
    (hn0 : (zdistInf d (sz.L n) (a0 - a0') : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ))
    (hn1 : (zdistInf d (sz.L n) (a1 - a1') : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ))
    (hc0 : 3 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) < (zdistInf d (sz.L n) (a0 - c) : ℝ))
    (hc1 : 3 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) < (zdistInf d (sz.L n) (a1 - c) : ℝ)) :
    ‖(baStep2Mat sz lam0 E).LM n u H ![σ0, σ1, σ0, !σ0, !σ1, !σ0] ![a0, a1, c, a1', a0', c]‖ ≤
      ((2 * J * Real.exp (Real.sqrt 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4))) ^ 3 *
          tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a0 - a1) : ℝ)) *
        (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (c - a1) : ℝ) *
          tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a0 - c) : ℝ)) := by
  have hℓ0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg (by linarith [Step5IIIEdet_log_ge_four hs]) _
  have hJ := Step5IIIEdet_one_le_J hs
  have hE6 := Step5IIIEdet2_E6_one_le hs
  have hW0 := (Step5IIIEdet_W_pos sz n).le
  have sc : ∀ x y : Zd d (sz.L n), (zdistInf d (sz.L n) (x - y) : ℝ) = (zdistInf d (sz.L n) (y - x) : ℝ) :=
    fun x y => by rw [lemDecCalE_zdistInf_sub_comm]
  have t1 := lemDecCalE_zdistInf_tri_real d (sz.L n) a0 a0' a1
  have t2 := lemDecCalE_zdistInf_tri_real d (sz.L n) a0' a1' a1
  have t3 := lemDecCalE_zdistInf_tri_real d (sz.L n) a0 a0' c
  have t4 := lemDecCalE_zdistInf_tri_real d (sz.L n) a1 a1' c
  have s1 := sc a1' a1
  have s2 := sc c a0'
  have s3 := sc c a1
  have s4 := sc a1 a0
  have d4 : (zdistInf d (sz.L n) (a0 - a1) : ℝ) - 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤
      (zdistInf d (sz.L n) (a0' - a1') : ℝ) := by linarith
  have l4 : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (a0' - a1') : ℝ) := by linarith
  have l0 : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (a0 - c) : ℝ) := by linarith
  have l2 : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (c - a1) : ℝ) := by linarith
  have l5 : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (c - a0') : ℝ) := by linarith
  have l3 : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (a1' - c) : ℝ) := by linarith
  have l1 : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (a0 - a1) : ℝ) := by linarith
  have d5 : (zdistInf d (sz.L n) (a0 - c) : ℝ) - 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤
      (zdistInf d (sz.L n) (c - a0') : ℝ) := by linarith
  have d3 : (zdistInf d (sz.L n) (c - a1) : ℝ) - 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤
      (zdistInf d (sz.L n) (a1' - c) : ℝ) := by linarith
  refine (Step5IIIEdet2_hs6 hm.1 σ0 σ1 a0 a1 a0' a1' c).trans ?_
  exact Step5IIIEdet2_pt_D hJ hE6 (tailTD_nonneg hW0) (tailTD_nonneg hW0) (tailTD_nonneg hW0)
    (Step5IIIEdet_leg_long hs hm σ0 a0 c l0) (Step5IIIEdet2_leg_far hs hm (!σ0) c a0' l5 d5)
    (Step5IIIEdet_leg_long hs hm σ0 c a1 l2) (Step5IIIEdet2_leg_far hs hm (!σ0) a1' c l3 d3)
    (Step5IIIEdet_leg_long' hs hm σ1 a1 a0 l1) (Step5IIIEdet2_leg_far hs hm (!σ1) a0' a1' l4 d4)

end Pointwise3

/-! ## 6. The sums over `c` of one six-loop -/

section Sums

variable {d : ℕ} {sz : Sizes d} {lam0 E : ℕ → ℝ} {n : ℕ} {u D Λ K₀ J θ Cd : ℝ}
  {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- The union of the two balls of radius `R` about `a₀` and `a₁` has at most `2 (2R+1)^d` points (`LemDecCalE_e10a`). -/
theorem Step5IIIEdet2_ball_card {L : ℕ} [NeZero L] (a0 a1 : Zd d L) {R : ℝ} (hR : 0 ≤ R) :
    ((Finset.univ.filter fun c : Zd d L => (zdistInf d L (a0 - c) : ℝ) ≤ R ∨ (zdistInf d L (a1 - c) : ℝ) ≤ R).card : ℝ) ≤
      2 * (2 * R + 1) ^ d := by
  classical
  set Bl : Finset (Zd d L) := Finset.univ.filter fun c : Zd d L => (zdistInf d L (a0 - c) : ℝ) ≤ R ∨ (zdistInf d L (a1 - c) : ℝ) ≤ R with hBl
  set B0 : Finset (Zd d L) := Finset.univ.filter fun c : Zd d L => (zdistInf d L (a0 - c) : ℝ) ≤ R with hB0
  set B1 : Finset (Zd d L) := Finset.univ.filter fun c : Zd d L => (zdistInf d L (a1 - c) : ℝ) ≤ R with hB1
  have hsub : Bl ⊆ B0 ∪ B1 := by
    intro x hx
    simp only [hBl, hB0, hB1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx
  have hcard : Bl.card ≤ B0.card + B1.card := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcard' : (Bl.card : ℝ) ≤ (B0.card : ℝ) + (B1.card : ℝ) := by exact_mod_cast hcard
  have h0 := LemDecCalE_e10a a0 R hR
  have h1 := LemDecCalE_e10a a1 R hR
  linarith

/-- The number of points of `Z_L^d`, times `(L^d)⁻¹`, is `1`. -/
theorem Step5IIIEdet2_card_inv (L : ℕ) [NeZero L] :
    ∑ _c : Zd d L, (((L : ℕ) : ℝ) ^ d)⁻¹ = 1 := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp [Zd, ZMod.card, hL]

/-- `|0|_∞ = 0`. -/
theorem Step5IIIEdet2_zdistInf_zero (d L : ℕ) : zdistInf d L (0 : Zd d L) = 0 := by
  unfold zdistInf
  exact Nat.eq_zero_of_le_zero (Finset.sup_le fun i _ => by simp)

/-- `S_θ ≥ 1` (the term `y = 0`). -/
theorem Step5IIIEdet2_sumTheta_ge_one (L : ℕ) [NeZero L] (θ : ℝ) :
    1 ≤ ∑ y : Zd d L, Real.exp (-(θ / 2 * Real.sqrt (zdistInf d L y : ℝ))) := by
  have h0 := Step5IIIEdet2_zdistInf_zero d L
  have := Finset.single_le_sum (f := fun y : Zd d L => Real.exp (-(θ / 2 * Real.sqrt (zdistInf d L y : ℝ))))
    (fun y _ => (Real.exp_pos _).le) (Finset.mem_univ (0 : Zd d L))
  simpa [h0] using this

/-- Near regime, one loop (cases (A), (B)): `Σ_c ‖𝓛^{(6)}‖ ≤ 2 (2·3ℓ*+1)^d Λ τ⁵ + Λ τ (a₂² τ⁴ 27) (S_θ + 2)`, `a₂ = W^{θd(Cd+1)} Λ`;
valid for every `r = |a₀ - a₁|`. -/
theorem Step5IIIEdet2_loop_sum_near (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) (hθ : 0 < θ) (hCd : 0 < Cd)
    (hm : BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ J θ Cd H) (σ0 σ1 : Bool) (a0 a1 a0' a1' : Zd d (sz.L n))
    (hn0 : (zdistInf d (sz.L n) (a0 - a0') : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ))
    (hn1 : (zdistInf d (sz.L n) (a1 - a1') : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) :
    ∑ c : Zd d (sz.L n), ‖(baStep2Mat sz lam0 E).LM n u H ![σ0, σ1, σ0, !σ0, !σ1, !σ0] ![a0, a1, c, a1', a0', c]‖ ≤
      2 * (2 * (3 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) + 1) ^ d * (Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 5) +
        (Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) *
          ((((sz.W n : ℕ) : ℝ) ^ (θ * (d * (Cd + 1))) * Λ) ^ 2 * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 4 * 27) *
          (∑ y : Zd d (sz.L n), Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) y : ℝ))) + 2) := by
  classical
  have hℓ0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg (by linarith [Step5IIIEdet_log_ge_four hs]) _
  have hΛ := Step5IIIEdet_one_le_Λ hs
  obtain ⟨hτ0, -⟩ := Step5IIIEdet_tau_le_one hs
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := (Step5IIIEdet_W_gt_one hs).le
  have ha2 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (θ * (d * (Cd + 1))) * Λ :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hW1 (by positivity)) hΛ
  set ℓ : ℝ := Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) with hℓ
  set τ : ℝ := (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ with hτ
  set a2 : ℝ := ((sz.W n : ℕ) : ℝ) ^ (θ * (d * (Cd + 1))) * Λ with ha2def
  set lam : ℝ := (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ with hlam
  set Bl : Finset (Zd d (sz.L n)) := Finset.univ.filter fun c : Zd d (sz.L n) =>
    (zdistInf d (sz.L n) (a0 - c) : ℝ) ≤ 3 * ℓ ∨ (zdistInf d (sz.L n) (a1 - c) : ℝ) ≤ 3 * ℓ with hBl
  have hmem : ∀ c, c ∈ Bl ↔ ((zdistInf d (sz.L n) (a0 - c) : ℝ) ≤ 3 * ℓ ∨ (zdistInf d (sz.L n) (a1 - c) : ℝ) ≤ 3 * ℓ) :=
    fun c => by simp [hBl]
  have hcard := Step5IIIEdet2_ball_card (d := d) a0 a1 (by positivity : (0 : ℝ) ≤ 3 * ℓ)
  have hpt : ∀ c : Zd d (sz.L n), ‖(baStep2Mat sz lam0 E).LM n u H ![σ0, σ1, σ0, !σ0, !σ1, !σ0] ![a0, a1, c, a1', a0', c]‖ ≤
      if c ∈ Bl then Λ * τ ^ 5 else
        ((Λ * τ) * (a2 ^ 2 * τ ^ 4 * 27)) *
          (Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) (a0 - c) : ℝ))) + 2 * lam) := by
    intro c
    by_cases hc : c ∈ Bl
    · simp only [hc, ↓reduceIte]
      exact Step5IIIEdet2_loop_A hm σ0 σ1 a0 a1 a0' a1' c
    · simp only [hc, ↓reduceIte]
      rw [hmem, not_or, not_le, not_le] at hc
      refine (Step5IIIEdet2_loop_B hs hθ hCd hm σ0 σ1 a0 a1 a0' a1' c hn0 hn1 hc.1 hc.2).trans (le_of_eq ?_)
      ring
  have hlam0 : 0 ≤ lam := by positivity
  have hsum := Step5IIIEdet_sum_split Bl
    (f := fun c => ‖(baStep2Mat sz lam0 E).LM n u H ![σ0, σ1, σ0, !σ0, !σ1, !σ0] ![a0, a1, c, a1', a0', c]‖)
    (g := fun c => Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) (a0 - c) : ℝ))) + 2 * lam)
    (β := Λ * τ ^ 5) (γ := (Λ * τ) * (a2 ^ 2 * τ ^ 4 * 27)) (by positivity) (by positivity)
    (fun c => by have := (Real.exp_pos (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) (a0 - c) : ℝ)))); positivity) hpt
  have hS : ∑ c : Zd d (sz.L n), Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) (a0 - c) : ℝ))) =
      ∑ y : Zd d (sz.L n), Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) y : ℝ))) :=
    Fintype.sum_equiv (Equiv.subLeft a0) _ _ fun x => rfl
  have hg : ∑ c : Zd d (sz.L n), (Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) (a0 - c) : ℝ))) + 2 * lam) =
      ∑ y : Zd d (sz.L n), Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) y : ℝ))) + 2 := by
    rw [Finset.sum_add_distrib, hS, ← Finset.mul_sum, Step5IIIEdet2_card_inv]
    ring
  rw [hg] at hsum
  have hcardle : (Bl.card : ℝ) * (Λ * τ ^ 5) ≤ 2 * (2 * (3 * ℓ) + 1) ^ d * (Λ * τ ^ 5) :=
    mul_le_mul_of_nonneg_right hcard (by positivity)
  linarith

/-- Far regime, one loop (cases (C), (D)), `r = |a₀ - a₁| > 6ℓ*`:
`Σ_c ‖𝓛^{(6)}‖ ≤ 2 (2·3ℓ*+1)^d √(Λτ³) (2 J e^{√6 Y} T(r))² + (2 J e^{√6 Y})³ T(r) (2 S_d + 1) τ² T(r)`. -/
theorem Step5IIIEdet2_loop_sum_far (hs : BAStep5IIIEScalar sz n u D Λ K₀ J)
    (hm : BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ J θ Cd H) (σ0 σ1 : Bool) (a0 a1 a0' a1' : Zd d (sz.L n))
    (hr : 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) < (zdistInf d (sz.L n) (a0 - a1) : ℝ))
    (hn0 : (zdistInf d (sz.L n) (a0 - a0') : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ))
    (hn1 : (zdistInf d (sz.L n) (a1 - a1') : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) :
    ∑ c : Zd d (sz.L n), ‖(baStep2Mat sz lam0 E).LM n u H ![σ0, σ1, σ0, !σ0, !σ1, !σ0] ![a0, a1, c, a1', a0', c]‖ ≤
      2 * (2 * (3 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) + 1) ^ d *
          (Real.sqrt (Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 3) *
            (2 * J * (Real.exp (Real.sqrt 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) *
              tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a0 - a1) : ℝ))) ^ 2) +
        ((2 * J * Real.exp (Real.sqrt 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4))) ^ 3 *
            tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a0 - a1) : ℝ)) *
          ((2 * (1 + 1536 * (d : ℝ) ^ 4) ^ d + 1) * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 *
            tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a0 - a1) : ℝ)) := by
  classical
  have hℓ0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg (by linarith [Step5IIIEdet_log_ge_four hs]) _
  have hJ := Step5IIIEdet_one_le_J hs
  have hE6 := Step5IIIEdet2_E6_one_le hs
  have hW0 := Step5IIIEdet_W_pos sz n
  have hu1 := Step5IIIEdet_u_lt_one hs
  obtain ⟨hτ0, -⟩ := Step5IIIEdet_tau_le_one hs
  have hd3 := hs.1
  have hTD : ∀ r : ℝ, tailTD d ((sz.W n : ℕ) : ℝ) u D r =
      ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 * Real.exp (-Real.sqrt r) + ((sz.W n : ℕ) : ℝ) ^ (-D) :=
    fun r => Step5IIIEdet_tail_eq hu1 r
  have hTnn : ∀ r : ℝ, 0 ≤ tailTD d ((sz.W n : ℕ) : ℝ) u D r := fun r => tailTD_nonneg hW0.le
  set ℓ : ℝ := Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) with hℓ
  set Tr : ℝ := tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a0 - a1) : ℝ) with hTr
  set E6 : ℝ := Real.exp (Real.sqrt 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) with hE6def
  set Bl : Finset (Zd d (sz.L n)) := Finset.univ.filter fun c : Zd d (sz.L n) =>
    (zdistInf d (sz.L n) (a0 - c) : ℝ) ≤ 3 * ℓ ∨ (zdistInf d (sz.L n) (a1 - c) : ℝ) ≤ 3 * ℓ with hBl
  have hmem : ∀ c, c ∈ Bl ↔ ((zdistInf d (sz.L n) (a0 - c) : ℝ) ≤ 3 * ℓ ∨ (zdistInf d (sz.L n) (a1 - c) : ℝ) ≤ 3 * ℓ) :=
    fun c => by simp [hBl]
  have hcard := Step5IIIEdet2_ball_card (d := d) a0 a1 (by positivity : (0 : ℝ) ≤ 3 * ℓ)
  have hTr0 : 0 ≤ Tr := hTnn _
  have hpt : ∀ c : Zd d (sz.L n), ‖(baStep2Mat sz lam0 E).LM n u H ![σ0, σ1, σ0, !σ0, !σ1, !σ0] ![a0, a1, c, a1', a0', c]‖ ≤
      if c ∈ Bl then Real.sqrt (Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 3) * (2 * J * (E6 * Tr)) ^ 2 else
        ((2 * J * E6) ^ 3 * Tr) *
          (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (c - a1) : ℝ) *
            tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a0 - c) : ℝ)) := by
    intro c
    by_cases hc : c ∈ Bl
    · simp only [hc, ↓reduceIte]
      exact Step5IIIEdet2_loop_C hs hm σ0 σ1 a0 a1 a0' a1' c hr hn0 hn1 ((hmem c).1 hc)
    · simp only [hc, ↓reduceIte]
      rw [hmem, not_or, not_le, not_le] at hc
      exact Step5IIIEdet2_loop_D hs hm σ0 σ1 a0 a1 a0' a1' c hr hn0 hn1 hc.1 hc.2
  have hβ : 0 ≤ Real.sqrt (Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 3) * (2 * J * (E6 * Tr)) ^ 2 :=
    mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)
  have hγ : 0 ≤ (2 * J * E6) ^ 3 * Tr := mul_nonneg (pow_nonneg (by nlinarith) 3) hTr0
  have hsum := Step5IIIEdet_sum_split Bl
    (f := fun c => ‖(baStep2Mat sz lam0 E).LM n u H ![σ0, σ1, σ0, !σ0, !σ1, !σ0] ![a0, a1, c, a1', a0', c]‖)
    (g := fun c => tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (c - a1) : ℝ) *
      tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a0 - c) : ℝ)) hβ hγ (fun c => mul_nonneg (hTnn _) (hTnn _)) hpt
  have hAnn : 0 ≤ ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 := sq_nonneg _
  have hwnn : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  have hconv := LemDecCalE_sum_tail_tail (d := d) (L := sz.L n) (by omega) hAnn hwnn (Step5IIIEdet_floor_one hs) a0 a1
  simp only [← hTD] at hconv
  have hcardle : (Bl.card : ℝ) * (Real.sqrt (Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 3) * (2 * J * (E6 * Tr)) ^ 2) ≤
      2 * (2 * (3 * ℓ) + 1) ^ d * (Real.sqrt (Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 3) * (2 * J * (E6 * Tr)) ^ 2) :=
    mul_le_mul_of_nonneg_right hcard hβ
  have := mul_le_mul_of_nonneg_left hconv hγ
  linarith

end Sums

/-! ## 7. The final comparisons and the loss budget for `res_deccalE_dif` -/

section Final

/-- The final comparison, near regime (`r ≤ 6ℓ*`, indicator `1`): with `Bw τ = Ω = (1-u)⁻¹`, `τ² ≤ E Tr`, the two loops give
`Bw · 2 [2 N₆ Λ τ⁵ + Λ τ (ω₀ Λ)² τ⁴ 27 (S + 2)] ≤ L₁ ω₀² S Ω (1 + Z) Tr²`. -/
theorem Step5IIIEdet2_final_near {Bw Λ τ ω0 N6 S Ω Tr E L1 Z : ℝ} (hΛ : 1 ≤ Λ) (hτ0 : 0 < τ) (hω0 : 1 ≤ ω0) (hS : 1 ≤ S)
    (hN6 : 1 ≤ N6) (hE : 1 ≤ E) (hTr : 0 ≤ Tr) (hΩ : 0 ≤ Ω) (hZ : 0 ≤ Z) (hB : Bw * τ = Ω) (hτE : τ ^ 2 ≤ E * Tr)
    (hL : 2 * E ^ 2 * Λ * (2 * N6 + 81 * Λ ^ 2) ≤ L1) :
    Bw * ((2 * N6 * (Λ * τ ^ 5) + (Λ * τ) * ((ω0 * Λ) ^ 2 * τ ^ 4 * 27) * (S + 2)) +
        (2 * N6 * (Λ * τ ^ 5) + (Λ * τ) * ((ω0 * Λ) ^ 2 * τ ^ 4 * 27) * (S + 2))) ≤
      L1 * (ω0 ^ 2 * S) * (Ω * (1 + Z) * Tr ^ 2) := by
  have hΛ0 : 0 ≤ Λ := by linarith
  have hE0 : 0 ≤ E := by linarith
  have hω2 : 1 ≤ ω0 ^ 2 * S := by nlinarith
  have h1 : Bw * τ ^ 5 = Ω * τ ^ 4 := by rw [← hB]; ring
  have hτ4 : τ ^ 4 ≤ E ^ 2 * Tr ^ 2 := by
    calc τ ^ 4 = (τ ^ 2) ^ 2 := by ring
      _ ≤ (E * Tr) ^ 2 := pow_le_pow_left₀ (by positivity) hτE 2
      _ = E ^ 2 * Tr ^ 2 := by ring
  have hbr : 2 * N6 + 27 * ω0 ^ 2 * Λ ^ 2 * (S + 2) ≤ ω0 ^ 2 * S * (2 * N6 + 81 * Λ ^ 2) := by
    have hq : 0 ≤ ω0 ^ 2 * Λ ^ 2 := by positivity
    nlinarith
  have hbr0 : 0 ≤ 2 * N6 + 27 * ω0 ^ 2 * Λ ^ 2 * (S + 2) := by positivity
  have hL0 : 0 ≤ L1 := le_trans (by positivity) hL
  calc _ = 2 * (Bw * τ ^ 5) * Λ * (2 * N6 + 27 * ω0 ^ 2 * Λ ^ 2 * (S + 2)) := by ring
    _ = 2 * (Ω * τ ^ 4) * Λ * (2 * N6 + 27 * ω0 ^ 2 * Λ ^ 2 * (S + 2)) := by rw [h1]
    _ ≤ 2 * (Ω * (E ^ 2 * Tr ^ 2)) * Λ * (2 * N6 + 27 * ω0 ^ 2 * Λ ^ 2 * (S + 2)) := by gcongr
    _ ≤ 2 * (Ω * (E ^ 2 * Tr ^ 2)) * Λ * (ω0 ^ 2 * S * (2 * N6 + 81 * Λ ^ 2)) := by gcongr
    _ = (2 * E ^ 2 * Λ * (2 * N6 + 81 * Λ ^ 2)) * (ω0 ^ 2 * S) * (Ω * Tr ^ 2) := by ring
    _ ≤ L1 * (ω0 ^ 2 * S) * (Ω * Tr ^ 2) := by gcongr
    _ ≤ L1 * (ω0 ^ 2 * S) * (Ω * (1 + Z) * Tr ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have : 0 ≤ Ω * Z * Tr ^ 2 := by positivity
        nlinarith

/-- The final comparison, far regime (`r > 6ℓ*`, indicator `0`): the glue and the six long legs. -/
theorem Step5IIIEdet2_final_far {Bw Λ τ ω0 N6 S Ω Tr E L1 J K2 : ℝ} (hΛ : 1 ≤ Λ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (hω0 : 1 ≤ ω0)
    (hS : 1 ≤ S) (hN6 : 1 ≤ N6) (hE : 1 ≤ E) (hJ : 1 ≤ J) (hK2 : 0 ≤ K2) (hTr : 0 ≤ Tr) (hΩ : 0 ≤ Ω) (hB : Bw * τ = Ω)
    (hL : 16 * E ^ 3 * (N6 * Λ + K2) ≤ L1) :
    Bw * ((2 * N6 * (Real.sqrt (Λ * τ ^ 3) * (2 * J * (E * Tr)) ^ 2) + ((2 * J * E) ^ 3 * Tr) * (K2 * τ ^ 2 * Tr)) +
        (2 * N6 * (Real.sqrt (Λ * τ ^ 3) * (2 * J * (E * Tr)) ^ 2) + ((2 * J * E) ^ 3 * Tr) * (K2 * τ ^ 2 * Tr))) ≤
      L1 * (ω0 ^ 2 * S) * (Ω * (0 + Real.sqrt τ * J ^ 3) * Tr ^ 2) := by
  have hΛ0 : 0 ≤ Λ := by linarith
  have hE0 : 0 ≤ E := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hω2 : 1 ≤ ω0 ^ 2 * S := by nlinarith
  have hsτ : 0 ≤ Real.sqrt τ := Real.sqrt_nonneg _
  have hτs : τ ≤ Real.sqrt τ := Real.le_sqrt_of_sq_le (by nlinarith)
  have hsΛ : Real.sqrt Λ ≤ Λ := Step5IIIEdet_sqrt_le_self hΛ
  have e3 : Real.sqrt (Λ * τ ^ 3) = Real.sqrt Λ * (τ * Real.sqrt τ) := by
    rw [Real.sqrt_mul hΛ0, show τ ^ 3 = τ ^ 2 * τ by ring, Real.sqrt_mul (sq_nonneg τ), Real.sqrt_sq hτ0.le]
  have hJ2 : J ^ 2 ≤ J ^ 3 := pow_le_pow_right₀ hJ (by norm_num)
  have hE2 : E ^ 2 ≤ E ^ 3 := pow_le_pow_right₀ hE (by norm_num)
  have hL0 : 0 ≤ L1 := le_trans (by positivity) hL
  -- the two terms
  have t1 : Bw * (2 * N6 * (Real.sqrt (Λ * τ ^ 3) * (2 * J * (E * Tr)) ^ 2)) =
      8 * N6 * Real.sqrt Λ * J ^ 2 * E ^ 2 * (Ω * Real.sqrt τ * Tr ^ 2) := by
    rw [e3, ← hB]; ring
  have t2 : Bw * (((2 * J * E) ^ 3 * Tr) * (K2 * τ ^ 2 * Tr)) = 8 * J ^ 3 * E ^ 3 * K2 * (Ω * τ * Tr ^ 2) := by
    rw [← hB]; ring
  have b1 : 8 * N6 * Real.sqrt Λ * J ^ 2 * E ^ 2 * (Ω * Real.sqrt τ * Tr ^ 2) ≤
      8 * N6 * Λ * J ^ 3 * E ^ 3 * (Ω * Real.sqrt τ * Tr ^ 2) := by
    have h0 : 0 ≤ Ω * Real.sqrt τ * Tr ^ 2 := by positivity
    refine mul_le_mul_of_nonneg_right ?_ h0
    gcongr
  have b2 : 8 * J ^ 3 * E ^ 3 * K2 * (Ω * τ * Tr ^ 2) ≤ 8 * J ^ 3 * E ^ 3 * K2 * (Ω * Real.sqrt τ * Tr ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have : 0 ≤ Ω * Tr ^ 2 := by positivity
    nlinarith
  have hZ : 0 ≤ Ω * (Real.sqrt τ * J ^ 3) * Tr ^ 2 := by positivity
  have key : Bw * ((2 * N6 * (Real.sqrt (Λ * τ ^ 3) * (2 * J * (E * Tr)) ^ 2) + ((2 * J * E) ^ 3 * Tr) * (K2 * τ ^ 2 * Tr)) +
        (2 * N6 * (Real.sqrt (Λ * τ ^ 3) * (2 * J * (E * Tr)) ^ 2) + ((2 * J * E) ^ 3 * Tr) * (K2 * τ ^ 2 * Tr))) ≤
      (16 * E ^ 3 * (N6 * Λ + K2)) * (Ω * (Real.sqrt τ * J ^ 3) * Tr ^ 2) := by
    calc _ = 2 * (Bw * (2 * N6 * (Real.sqrt (Λ * τ ^ 3) * (2 * J * (E * Tr)) ^ 2)) +
            Bw * (((2 * J * E) ^ 3 * Tr) * (K2 * τ ^ 2 * Tr))) := by ring
      _ ≤ 2 * (8 * N6 * Λ * J ^ 3 * E ^ 3 * (Ω * Real.sqrt τ * Tr ^ 2) +
            8 * J ^ 3 * E ^ 3 * K2 * (Ω * Real.sqrt τ * Tr ^ 2)) := by
          rw [t1, t2]; gcongr
      _ = _ := by ring
  calc _ ≤ (16 * E ^ 3 * (N6 * Λ + K2)) * (Ω * (Real.sqrt τ * J ^ 3) * Tr ^ 2) := key
    _ ≤ L1 * (Ω * (Real.sqrt τ * J ^ 3) * Tr ^ 2) := mul_le_mul_of_nonneg_right hL hZ
    _ ≤ L1 * (ω0 ^ 2 * S) * (Ω * (0 + Real.sqrt τ * J ^ 3) * Tr ^ 2) := by
        rw [zero_add]
        exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hL0 hω2) hZ

end Final

section LossBudget

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {u D Λ K₀ J : ℝ}

/-- The constants for `res_deccalE_dif`, near regime: `2 E² Λ (2 N₆ + 81 Λ²) ≤ lossE2wG`, `E = e^{√6 Y}`, `N₆ = (2·3ℓ*+1)^d`. -/
theorem Step5IIIEdet2_const_near (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) :
    2 * (Real.exp (Real.sqrt 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4))) ^ 2 * Λ *
        (2 * (2 * (3 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) + 1) ^ d + 81 * Λ ^ 2) ≤
      lossE2wG d (sz.L n) (sz.W n) Λ K₀ := by
  refine le_trans ?_ (Step5IIIEdet_loss_ge hs)
  have hball := Step5IIIEdet2_ball3_le hs
  have hE1 := Step5IIIEdet2_E6_one_le hs
  have hE3 := Step5IIIEdet2_E6_cube hs
  have hΛ1 := Step5IIIEdet_one_le_Λ hs
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by have := hs.1; omega : 1 ≤ d)
  have hd4 : (1 : ℝ) ≤ (d : ℝ) ^ 4 := one_le_pow₀ hd1
  have hlog := Step5IIIEdet_log_ge_four hs
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := (Step5IIIEdet_W_gt_one hs).le
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (sz.three_le_L n).trans' (by norm_num)
  have hP1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) (one_le_pow₀ hW1)
  set E6 := Real.exp (Real.sqrt 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) with hE6
  set G := (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d))) ^ (2 * d) with hG
  set N6 := (2 * (3 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) + 1) ^ d with hN6
  set c := (1600 * (d : ℝ) ^ 4 * 1000) ^ d with hc
  set X8 := Real.exp (8 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) with hX8
  have hG1 : (1 : ℝ) ≤ G := one_le_pow₀ (by linarith [Real.log_nonneg hP1])
  have hc1 : (1 : ℝ) ≤ c := one_le_pow₀ (by nlinarith)
  have hN60 : 0 ≤ N6 := by positivity
  have hX0 : 0 ≤ X8 := (Real.exp_pos _).le
  have hE2 : E6 ^ 2 ≤ E6 ^ 3 := pow_le_pow_right₀ hE1 (by norm_num)
  have hΛ3 : Λ ^ 3 ≤ Λ ^ 6 := pow_le_pow_right₀ hΛ1 (by norm_num)
  have hΛ0 : 0 ≤ Λ := by linarith
  have hΛ2 : Λ ^ 2 ≤ Λ ^ 3 := pow_le_pow_right₀ hΛ1 (by norm_num)
  have hΛ1' : Λ ≤ Λ ^ 3 := by nlinarith
  have h1 : Λ * (2 * N6 + 81 * Λ ^ 2) ≤ 83 * G * Λ ^ 6 := by
    have : Λ * (2 * N6 + 81 * Λ ^ 2) ≤ Λ ^ 3 * (2 * N6 + 81) := by nlinarith
    have h2 : 2 * N6 + 81 ≤ 83 * G := by nlinarith
    calc Λ * (2 * N6 + 81 * Λ ^ 2) ≤ Λ ^ 3 * (2 * N6 + 81) := this
      _ ≤ Λ ^ 3 * (83 * G) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ Λ ^ 6 * (83 * G) := mul_le_mul_of_nonneg_right hΛ3 (by positivity)
      _ = 83 * G * Λ ^ 6 := by ring
  calc 2 * E6 ^ 2 * Λ * (2 * N6 + 81 * Λ ^ 2) = 2 * E6 ^ 2 * (Λ * (2 * N6 + 81 * Λ ^ 2)) := by ring
    _ ≤ 2 * X8 * (83 * G * Λ ^ 6) := by
        have h3 : E6 ^ 2 ≤ X8 := hE2.trans hE3
        have h4 : 0 ≤ Λ * (2 * N6 + 81 * Λ ^ 2) := by positivity
        calc 2 * E6 ^ 2 * (Λ * (2 * N6 + 81 * Λ ^ 2)) ≤ 2 * X8 * (Λ * (2 * N6 + 81 * Λ ^ 2)) := by gcongr
          _ ≤ 2 * X8 * (83 * G * Λ ^ 6) := by gcongr
    _ ≤ 10 ^ 12 * c * Λ ^ 6 * X8 * G := by
        have : 0 ≤ X8 * G * Λ ^ 6 := by positivity
        nlinarith

/-- The constants for `res_deccalE_dif`, far regime: `16 E³ (N₆ Λ + 2 S_d + 1) ≤ lossE2wG`. -/
theorem Step5IIIEdet2_const_far (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) :
    16 * (Real.exp (Real.sqrt 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4))) ^ 3 *
        ((2 * (3 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) + 1) ^ d * Λ + (2 * (1 + 1536 * (d : ℝ) ^ 4) ^ d + 1)) ≤
      lossE2wG d (sz.L n) (sz.W n) Λ K₀ := by
  refine le_trans ?_ (Step5IIIEdet_loss_ge hs)
  have hball := Step5IIIEdet2_ball3_le hs
  have hE3 := Step5IIIEdet2_E6_cube hs
  have hΛ1 := Step5IIIEdet_one_le_Λ hs
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by have := hs.1; omega : 1 ≤ d)
  have hd4 : (1 : ℝ) ≤ (d : ℝ) ^ 4 := one_le_pow₀ hd1
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := (Step5IIIEdet_W_gt_one hs).le
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (sz.three_le_L n).trans' (by norm_num)
  have hP1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) (one_le_pow₀ hW1)
  set E6 := Real.exp (Real.sqrt 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) with hE6
  set G := (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d))) ^ (2 * d) with hG
  set N6 := (2 * (3 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) + 1) ^ d with hN6
  set c := (1600 * (d : ℝ) ^ 4 * 1000) ^ d with hc
  set X8 := Real.exp (8 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) with hX8
  have hG1 : (1 : ℝ) ≤ G := one_le_pow₀ (by linarith [Real.log_nonneg hP1])
  have hc1 : (1 : ℝ) ≤ c := one_le_pow₀ (by nlinarith)
  have hN60 : 0 ≤ N6 := by positivity
  have hX0 : 0 ≤ X8 := (Real.exp_pos _).le
  have hΛ0 : 0 ≤ Λ := by linarith
  have hΛ6 : (1 : ℝ) ≤ Λ ^ 6 := one_le_pow₀ hΛ1
  have hΛΛ : Λ ≤ Λ ^ 6 := by nlinarith [pow_le_pow_right₀ hΛ1 (show 1 ≤ 6 by norm_num)]
  have hS : (1 + 1536 * (d : ℝ) ^ 4) ^ d ≤ c := pow_le_pow_left₀ (by positivity) (by nlinarith) d
  have hS1 : (1 : ℝ) ≤ (1 + 1536 * (d : ℝ) ^ 4) ^ d := one_le_pow₀ (by nlinarith)
  have h1 : N6 * Λ + (2 * (1 + 1536 * (d : ℝ) ^ 4) ^ d + 1) ≤ 4 * c * G * Λ ^ 6 := by
    have a1 : N6 * Λ ≤ G * Λ ^ 6 := mul_le_mul hball hΛΛ hΛ0 (by positivity)
    have a2 : 2 * (1 + 1536 * (d : ℝ) ^ 4) ^ d + 1 ≤ 3 * c := by linarith
    have a3 : G * Λ ^ 6 ≤ c * G * Λ ^ 6 := by
      have : 0 ≤ G * Λ ^ 6 := by positivity
      nlinarith
    have a4 : 3 * c ≤ 3 * c * G * Λ ^ 6 := by
      have : 0 ≤ 3 * c := by positivity
      nlinarith [mul_le_mul hG1 hΛ6 (by norm_num) (by positivity)]
    nlinarith
  calc 16 * E6 ^ 3 * (N6 * Λ + (2 * (1 + 1536 * (d : ℝ) ^ 4) ^ d + 1)) ≤ 16 * X8 * (4 * c * G * Λ ^ 6) := by
        calc _ ≤ 16 * X8 * (N6 * Λ + (2 * (1 + 1536 * (d : ℝ) ^ 4) ^ d + 1)) := by
              have : 0 ≤ N6 * Λ + (2 * (1 + 1536 * (d : ℝ) ^ 4) ^ d + 1) := by positivity
              gcongr
          _ ≤ _ := by gcongr
    _ ≤ 10 ^ 12 * c * Λ ^ 6 * X8 * G := by
        have : 0 ≤ X8 * G * Λ ^ 6 * c := by positivity
        nlinarith

end LossBudget

/-! ## 8. `res_deccalE_dif` (5.45) -/

section Dif

/-- `res_deccalE_dif` (5.45) at BA, near cut `2ℓ*`, indicator at `6ℓ*`, factor `W^{2θd(Cd+1)} S_θ`.
Chain: `STeeMg` at `m = 2`, `S = 1` is `W^d Σ_c` of two six-loops with blocks `(a₀, a₁, c, a₁', a₀', c)`, `(a₁, a₀, c, a₀', a₁', c)`
(`Step5IIIEdet2_STeeMg_eq`); each loop is bounded through its legs (the Hilbert-Schmidt bound `Step5IIIEdet2_hs6`, glue forms): `r ≤ 6ℓ*`: (A) `c` within
`3ℓ*` of `a₀` or `a₁`, `Λ τ⁵` by (v), (B) `c` farther, two short legs and four long legs by (vi) (`Step5IIIEdet2_loop_sum_near`); `r > 6ℓ*`:
(C) `c` within `3ℓ*`, the glue, (D) `c` farther, six long legs, `LemDecCalE_sum_tail_tail` (`Step5IIIEdet2_loop_sum_far`); the comparisons
are `Step5IIIEdet2_final_near`, `Step5IIIEdet2_final_far` and the constants against `lossE2wG` are `Step5IIIEdet2_const_near`, `Step5IIIEdet2_const_far`. -/
theorem baStep5IIIE_dif (d : ℕ) (hd : 3 ≤ d) (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u D Λ K₀ J θ Cd : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hθ : 0 < θ) (hCd : 0 < Cd)
    (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) (hm : BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ J θ Cd H)
    (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n))
    (hnear : ∀ i : Fin 2, (zdistInf d (sz.L n) (a i - a' i) : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) :
    ‖STeeMg (baStep2Mat sz lam0 E) n u H σ a a'‖ ≤ lossE2wG d (sz.L n) (sz.W n) Λ K₀ *
        (((sz.W n : ℕ) : ℝ) ^ (2 * (θ * (d * (Cd + 1)))) *
          ∑ y : Zd d (sz.L n), Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) y : ℝ)))) * ((1 - u)⁻¹ *
        ((if (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) ≤ 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) +
          (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 : ℝ)) * STtailTD sz n u D a ^ 2) := by
  have hu1 := Step5IIIEdet_u_lt_one hs
  have hx : 0 < 1 - u := by linarith
  have hW0 := Step5IIIEdet_W_pos sz n
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := (Step5IIIEdet_W_gt_one hs).le
  have hJ1 := Step5IIIEdet_one_le_J hs
  have hΛ1 := Step5IIIEdet_one_le_Λ hs
  obtain ⟨hτ0, hτ1⟩ := Step5IIIEdet_tau_le_one hs
  have hlogn : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := by linarith [Step5IIIEdet_log_ge_four hs]
  have hℓ0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hlogn _
  have hE6 := Step5IIIEdet2_E6_one_le hs
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (sz.three_le_L n).trans' (by norm_num)
  have hS1 := Step5IIIEdet2_sumTheta_ge_one (d := d) (sz.L n) θ
  have hω0 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (θ * (d * (Cd + 1))) := Real.one_le_rpow hW1 (by positivity)
  have hN61 : (1 : ℝ) ≤ (2 * (3 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) + 1) ^ d :=
    one_le_pow₀ (by linarith)
  have hωeq : ((sz.W n : ℕ) : ℝ) ^ (2 * (θ * (d * (Cd + 1)))) = (((sz.W n : ℕ) : ℝ) ^ (θ * (d * (Cd + 1)))) ^ 2 := by
    rw [mul_comm, Real.rpow_mul hW0.le, Real.rpow_two]
  have hWd : ((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ = (1 - u)⁻¹ := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW0 d
    field_simp
  have hΩ : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 hx.le
  have hTr0 : 0 ≤ tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) := tailTD_nonneg hW0.le
  have hTrE : STtailTD sz n u D a = tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) := rfl
  -- the bridge and the norm
  have hnorm : ‖STeeMg (baStep2Mat sz lam0 E) n u H σ a a'‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d *
      (∑ c : Zd d (sz.L n), ‖(baStep2Mat sz lam0 E).LM n u H ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a 0, a 1, c, a' 1, a' 0, c]‖ +
        ∑ c : Zd d (sz.L n), ‖(baStep2Mat sz lam0 E).LM n u H ![σ 1, σ 0, σ 1, !(σ 1), !(σ 0), !(σ 1)] ![a 1, a 0, c, a' 0, a' 1, c]‖) := by
    rw [Step5IIIEdet2_STeeMg_eq, norm_mul]
    have hw : ‖(((sz.W n : ℕ) : ℂ) ^ d)‖ = ((sz.W n : ℕ) : ℝ) ^ d := by simp
    rw [hw]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hW0.le _)
    rw [← Finset.sum_add_distrib]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => norm_add_le _ _)
  rw [abs_of_pos hx, hωeq, hTrE]
  refine hnorm.trans ?_
  by_cases hr : (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) ≤ 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)
  · simp only [hr, ↓reduceIte]
    have L1 := Step5IIIEdet2_loop_sum_near hs hθ hCd hm (σ 0) (σ 1) (a 0) (a 1) (a' 0) (a' 1) (hnear 0) (hnear 1)
    have L2 := Step5IIIEdet2_loop_sum_near hs hθ hCd hm (σ 1) (σ 0) (a 1) (a 0) (a' 1) (a' 0) (hnear 1) (hnear 0)
    refine le_trans (mul_le_mul_of_nonneg_left (add_le_add L1 L2) (pow_nonneg hW0.le _)) ?_
    have hZ : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 : ℝ) :=
      mul_nonneg (Real.rpow_nonneg hτ0.le _) (Real.rpow_nonneg (by linarith) _)
    exact Step5IIIEdet2_final_near hΛ1 hτ0 hω0 hS1 hN61 hE6 hTr0 hΩ hZ hWd (Step5IIIEdet2_near_norm6 hs hr)
      (Step5IIIEdet2_const_near hs)
  · simp only [hr, ↓reduceIte]
    have hr' : 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) < (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) := not_le.1 hr
    have L1 := Step5IIIEdet2_loop_sum_far hs hm (σ 0) (σ 1) (a 0) (a 1) (a' 0) (a' 1) hr' (hnear 0) (hnear 1)
    have L2 := Step5IIIEdet2_loop_sum_far hs hm (σ 1) (σ 0) (a 1) (a 0) (a' 1) (a' 0)
      (by rw [lemDecCalE_zdistInf_sub_comm]; exact hr') (hnear 1) (hnear 0)
    rw [lemDecCalE_zdistInf_sub_comm d (sz.L n) (a 1) (a 0)] at L2
    refine le_trans (mul_le_mul_of_nonneg_left (add_le_add L1 L2) (pow_nonneg hW0.le _)) ?_
    have hτh : (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ^ (1 / 2 : ℝ) = Real.sqrt (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ :=
      (Real.sqrt_eq_rpow _).symm
    have hJ3 : J ^ (3 : ℝ) = J ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hτh, hJ3]
    exact Step5IIIEdet2_final_far hΛ1 hτ0 hτ1 hω0 hS1 hN61 hE6 hJ1 (by positivity) hTr0 hΩ hWd (Step5IIIEdet2_const_far hs)

end Dif

/-! ## 9. The assembly -/

/-- `BAStep5IIIEdet`: `lem_dec_calE` (Lemma 5.2) at BA, deterministic, one time `u`, `S = 1`; loss
`lossE2wG` (`Path/LemDecCalEwG`); indicators at `2ℓ*` (`res_deccalE_wG`) and `6ℓ*` (`res_deccalE_dif`), near cut `2ℓ*`; the `res_deccalE_dif` factor
`W^{2θd(Cd+1)} S_θ`.  The matrix part of the bundle is a hypothesis. -/
def BAStep5IIIEdet (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u D Λ K₀ J θ Cd : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), 0 < θ → 0 < Cd →
    BAStep5IIIEScalar sz n u D Λ K₀ J → BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ J θ Cd H →
    (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STELKLKMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤
        lossE2wG d (sz.L n) (sz.W n) Λ K₀ * ((1 - u)⁻¹ * ((((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ * J ^ 2)) * STtailTD sz n u D a) ∧
    (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STEGtMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤
        lossE2wG d (sz.L n) (sz.W n) Λ K₀ * ((1 - u)⁻¹ *
          ((if (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) +
            (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 / 2 : ℝ)) * STtailTD sz n u D a)) ∧
    (∀ (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)),
      (∀ i : Fin 2, (zdistInf d (sz.L n) (a i - a' i) : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
      ‖STeeMg (baStep2Mat sz lam0 E) n u H σ a a'‖ ≤ lossE2wG d (sz.L n) (sz.W n) Λ K₀ * (((sz.W n : ℕ) : ℝ) ^ (2 * (θ * (d * (Cd + 1)))) *
          ∑ y : Zd d (sz.L n), Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) y : ℝ)))) * ((1 - u)⁻¹ *
          ((if (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) ≤ 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) +
            (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 : ℝ)) * STtailTD sz n u D a ^ 2))

/-- `BAStep5IIIEdet d` holds for every `d` (the three conjuncts are `baStep5IIIE_lk`, `baStep5IIIE_wG`, `baStep5IIIE_dif`). -/
theorem baStep5IIIEdet_holds (d : ℕ) : BAStep5IIIEdet d := fun hd sz lam0 E n u D Λ K₀ J θ Cd H hθ hCd hs hm =>
  ⟨fun σ a => baStep5IIIE_lk d hd sz lam0 E n u D Λ K₀ J θ Cd H hθ hCd hs hm σ a,
   fun σ a => baStep5IIIE_wG d hd sz lam0 E n u D Λ K₀ J θ Cd H hθ hCd hs hm σ a,
   fun σ a a' hnear => baStep5IIIE_dif d hd sz lam0 E n u D Λ K₀ J θ Cd H hθ hCd hs hm σ a a' hnear⟩

end RBM.BA
end
