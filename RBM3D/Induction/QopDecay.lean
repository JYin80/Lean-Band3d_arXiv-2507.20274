/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.QopNorm
import RBM3D.Induction.B45
import RBM3D.Induction.Step2Iterate
import RBM3D.Propagator.Prop5Hold

/-!
# S6-09c (ticket T2249): decay of `∂_tϑ` and propagation of `(deccA0)` through `Θ^{(n)}`

Deterministic, public, generic in the tensor order.

* `QopAlgebra_mollifier_derivDecay`: `|∂_t ϑ_{t,a}| ≤ (1 + 40 d m) 6^{d m} (1-t)⁻¹ (ℓ_t^d)^{-m} e^{-S/(4ℓ_t)}`
  (paper `(eq:derv_Theta)` `3_5:1215` states the size only; `rmk:choosechi` `3_5:1250`).
* `QopDecay_deriv_fastDecay`: the `STExpQsrc` source `(𝒫f)_{a₁} ∂_tϑ_{t,a}` is `(t, ε', D')`-decaying.
* `QopDecay_thetaKer_decay`: the kernel `μ S^{(B)} Θ_{uμ}` of `Θ^{(n)}_u` decays at scale `ℓ_u`, prefactor `(1-u)⁻¹`.
* `QopDecay_ThetaN_fastDecay`: `Θ^{(n)}_u` maps `(u, ε, D)` to `(u, 2ε, D - (K+1))`.
* `QopDecay_STthetaOp_fastDecay`: the same for `STthetaOp`.

Section 1 is a verbatim copy (renamed `qa… ↦ qdec…`) of the private helpers of
`RBM3D/Induction/QopAlgebra.lean` (main `d822fd7`, last change `6b2494e`), lines 37-282, 331-340, 377-408, 438-458, 506-508; `qdec_growth` copies `qn_growth` (`QopNorm.lean:343`).
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Gauss.Sizes

open RBM Filter

/-! ## 1. One-dimensional sums over `ℤ_L` -/

/-- `Σ_{y ∈ ℤ_L} F(y.val) = Σ_{k < L} F k`. -/
private theorem qdec_sum_zmod_val {L : ℕ} [NeZero L] (F : ℕ → ℝ) :
    ∑ y : ZMod L, F y.val = ∑ k ∈ Finset.range L, F k :=
  Finset.sum_bij (fun y _ => y.val) (fun y _ => Finset.mem_range.2 (ZMod.val_lt y))
    (fun _ _ _ _ h => ZMod.val_injective L h)
    (fun k hk => ⟨(k : ZMod L), Finset.mem_univ _, ZMod.val_natCast_of_lt (Finset.mem_range.1 hk)⟩)
    (fun _ _ => rfl)

/-- `z(u) = Σ_{y ∈ ℤ_L} exp(-u |y|)`. -/
private def qdecZ1 (L : ℕ) [NeZero L] (u : ℝ) : ℝ :=
  ∑ y : ZMod L, Real.exp (-u * (zdist L y : ℝ))

/-- `z₂(u) = Σ_{y ∈ ℤ_L} |y| exp(-u |y|)` (minus the `u`-derivative of `z`). -/
private def qdecZ2 (L : ℕ) [NeZero L] (u : ℝ) : ℝ :=
  ∑ y : ZMod L, (zdist L y : ℝ) * Real.exp (-u * (zdist L y : ℝ))

private theorem qdecZ1_pos {L : ℕ} [NeZero L] (u : ℝ) : 0 < qdecZ1 L u :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

private theorem qdecZ1_eq_range {L : ℕ} [NeZero L] (u : ℝ) :
    qdecZ1 L u = ∑ k ∈ Finset.range L, Real.exp (-u * ((min k (L - k) : ℕ) : ℝ)) :=
  qdec_sum_zmod_val (fun k => Real.exp (-u * ((min k (L - k) : ℕ) : ℝ)))

private theorem qdecZ2_eq_range {L : ℕ} [NeZero L] (u : ℝ) :
    qdecZ2 L u = ∑ k ∈ Finset.range L,
      ((min k (L - k) : ℕ) : ℝ) * Real.exp (-u * ((min k (L - k) : ℕ) : ℝ)) :=
  qdec_sum_zmod_val (fun k => ((min k (L - k) : ℕ) : ℝ) * Real.exp (-u * ((min k (L - k) : ℕ) : ℝ)))

/-- Lower bound for the one-dimensional mass: `z(u) ≥ (e u)⁻¹` when `L⁻¹ < u`. -/
private theorem qdecZ1_ge {L : ℕ} [NeZero L] {u : ℝ} (hu : 0 < u) (huL : (L : ℝ)⁻¹ < u) :
    (Real.exp 1)⁻¹ * u⁻¹ ≤ qdecZ1 L u := by
  set k := ⌊u⁻¹⌋₊ with hk
  have hk1 : (k : ℝ) ≤ u⁻¹ := Nat.floor_le (by positivity)
  have hk2 : u⁻¹ < k + 1 := Nat.lt_floor_add_one _
  have hL0 : (0 : ℝ) < L := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))
  have hkL : k + 1 ≤ L := by
    have h1 : (k : ℝ) < L := lt_of_le_of_lt hk1 ((inv_lt_comm₀ hu hL0).2 huL)
    exact_mod_cast h1
  rw [qdecZ1_eq_range]
  calc (Real.exp 1)⁻¹ * u⁻¹ ≤ ((k : ℝ) + 1) * (Real.exp 1)⁻¹ := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_right hk2.le (inv_nonneg.2 (Real.exp_pos 1).le)
    _ = ∑ _j ∈ Finset.range (k + 1), (Real.exp 1)⁻¹ := by simp
    _ ≤ ∑ j ∈ Finset.range (k + 1), Real.exp (-u * ((min j (L - j) : ℕ) : ℝ)) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        have h1 : ((min j (L - j) : ℕ) : ℝ) ≤ k := by
          exact_mod_cast (min_le_left _ _).trans hj'
        have h2 : u * ((min j (L - j) : ℕ) : ℝ) ≤ 1 := by
          calc u * ((min j (L - j) : ℕ) : ℝ) ≤ u * u⁻¹ := mul_le_mul_of_nonneg_left (h1.trans hk1) hu.le
            _ = 1 := mul_inv_cancel₀ hu.ne'
        rw [← Real.exp_neg]
        exact Real.exp_le_exp.2 (by linarith)
    _ ≤ ∑ j ∈ Finset.range L, Real.exp (-u * ((min j (L - j) : ℕ) : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hkL)
          (fun _ _ _ => (Real.exp_pos _).le)

private theorem qdec_hasSum_f {u : ℝ} (hu : 0 < u) :
    HasSum (fun j : ℕ => (j : ℝ) * Real.exp (-u * j))
      (Real.exp (-u) / (1 - Real.exp (-u)) ^ 2) := by
  have hr : ‖Real.exp (-u)‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact Real.exp_lt_one_iff.2 (by linarith)
  have h := hasSum_coe_mul_geometric_of_norm_lt_one hr
  convert h using 2 with j
  rw [← Real.exp_nat_mul]; ring_nf

/-- Upper bound for the first moment of the one-dimensional mass:
`z₂(u) ≤ 2 e^{-u} / (1 - e^{-u})²`. -/
private theorem qdecZ2_le {L : ℕ} [NeZero L] {u : ℝ} (hu : 0 < u) :
    qdecZ2 L u ≤ 2 * (Real.exp (-u) / (1 - Real.exp (-u)) ^ 2) := by
  set f : ℕ → ℝ := fun j => (j : ℝ) * Real.exp (-u * j) with hf
  have hf0 : ∀ j, 0 ≤ f j := fun j => by simp only [hf]; positivity
  have hT : ∀ n, ∑ k ∈ Finset.range n, f k ≤ Real.exp (-u) / (1 - Real.exp (-u)) ^ 2 :=
    fun n => sum_le_hasSum _ (fun j _ => hf0 j) (qdec_hasSum_f hu)
  rw [qdecZ2_eq_range]
  have h1 : ∑ k ∈ Finset.range L, ((min k (L - k) : ℕ) : ℝ) * Real.exp (-u * ((min k (L - k) : ℕ) : ℝ))
      ≤ ∑ k ∈ Finset.range L, (f k + f (L - k)) := by
    refine Finset.sum_le_sum fun k _ => ?_
    change f (min k (L - k)) ≤ f k + f (L - k)
    rcases min_choice k (L - k) with h | h <;> rw [h]
    · linarith [hf0 (L - k)]
    · linarith [hf0 k]
  have h2 : ∑ k ∈ Finset.range L, f (L - k) = ∑ j ∈ Finset.range L, f (j + 1) := by
    rw [← Finset.sum_range_reflect (fun j => f (j + 1)) L]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    congr 1; omega
  have h3 : ∑ j ∈ Finset.range L, f (j + 1) ≤ Real.exp (-u) / (1 - Real.exp (-u)) ^ 2 := by
    have := Finset.sum_range_succ' f L
    have h0 : f 0 = 0 := by simp [hf]
    rw [h0, add_zero] at this
    rw [← this]; exact hT _
  rw [Finset.sum_add_distrib, h2] at h1
  linarith [hT L]

/-! ## 2. The smoothed scale `ℓ̃_t = 1 / u_t` -/

/-- `y_t = 1 + g (1 - t)^{-1/2}`. -/
private def qdecY (g t : ℝ) : ℝ := 1 + g / Real.sqrt (1 - t)

/-- `u_t = 1 / ℓ̃_t = y_t⁻¹ + L⁻¹`. -/
private def qdecU (L : ℕ) (g t : ℝ) : ℝ := (qdecY g t)⁻¹ + (L : ℝ)⁻¹

private theorem qdecY_gt {g t : ℝ} (hg : 0 < g) (ht : t < 1) : 1 < qdecY g t := by
  have h : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 (by linarith)
  unfold qdecY; have := div_pos hg h; linarith

private theorem qdecU_pos {L : ℕ} [NeZero L] {g t : ℝ} (hg : 0 < g) (ht : t < 1) : 0 < qdecU L g t := by
  have h1 : 0 < qdecY g t := lt_trans zero_lt_one (qdecY_gt hg ht)
  have h2 : (0 : ℝ) < L := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))
  unfold qdecU; positivity

private theorem qdecU_gt {L : ℕ} [NeZero L] {g t : ℝ} (hg : 0 < g) (ht : t < 1) :
    (L : ℝ)⁻¹ < qdecU L g t := by
  have h1 : 0 < qdecY g t := lt_trans zero_lt_one (qdecY_gt hg ht)
  unfold qdecU; have := inv_pos.2 h1; linarith

/-- `u_t ≤ 4/3` (as `y_t > 1` and `L ≥ 3`). -/
private theorem qdecU_le {L : ℕ} (hL : 3 ≤ L) {g t : ℝ} (hg : 0 < g) (ht : t < 1) :
    qdecU L g t ≤ 4 / 3 := by
  have h1 : (qdecY g t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (qdecY_gt hg ht).le
  have h3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have h2 : (L : ℝ)⁻¹ ≤ 1 / 3 := by
    rw [one_div]; exact inv_anti₀ (by norm_num) h3
  unfold qdecU; linarith

private theorem qdec_ellT_eq {L : ℕ} {g t : ℝ} (ht : t < 1) :
    ellT L g t = min (max (g / Real.sqrt (1 - t)) 1) L := by
  unfold ellT; rw [abs_of_pos (by linarith : 0 < 1 - t)]

/-- `u_t ≥ 1 / (2 ℓ_t)`. -/
private theorem qdecU_lb {L : ℕ} [NeZero L] {g t : ℝ} (hg : 0 < g) (ht : t < 1) :
    (2 * ellT L g t)⁻¹ ≤ qdecU L g t := by
  have hy : 0 < qdecY g t := lt_trans zero_lt_one (qdecY_gt hg ht)
  have hL0 : (0 : ℝ) < L := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))
  have hx : 0 < g / Real.sqrt (1 - t) := div_pos hg (Real.sqrt_pos.2 (by linarith))
  have hell1 : 1 ≤ ellT L g t := one_le_ellT (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  rw [qdec_ellT_eq ht] at hell1 ⊢
  unfold qdecU
  rcases min_choice (max (g / Real.sqrt (1 - t)) 1) (L : ℝ) with h | h
  · rw [h]
    have h2 : (2 * max (g / Real.sqrt (1 - t)) 1)⁻¹ ≤ (qdecY g t)⁻¹ := by
      refine inv_anti₀ hy ?_
      unfold qdecY
      rcases le_total (g / Real.sqrt (1 - t)) 1 with h' | h'
      · rw [max_eq_right h']; linarith
      · rw [max_eq_left h']; linarith
    have := inv_nonneg.2 hL0.le
    linarith
  · rw [h]
    have h2 : (2 * (L : ℝ))⁻¹ ≤ (L : ℝ)⁻¹ := inv_anti₀ hL0 (by linarith)
    have := inv_nonneg.2 hy.le
    linarith

/-- `ℓ_t u_t ≤ 2`. -/
private theorem qdecU_ub {L : ℕ} [NeZero L] {g t : ℝ} (hg : 0 < g) (ht : t < 1) :
    ellT L g t * qdecU L g t ≤ 2 := by
  have hy : 0 < qdecY g t := lt_trans zero_lt_one (qdecY_gt hg ht)
  have hL0 : (0 : ℝ) < L := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))
  have hx : 0 < g / Real.sqrt (1 - t) := div_pos hg (Real.sqrt_pos.2 (by linarith))
  have hell1 : ellT L g t ≤ qdecY g t := by
    rw [qdec_ellT_eq ht]; unfold qdecY
    refine (min_le_left _ _).trans (max_le (by linarith) (by linarith))
  have hell2 : ellT L g t ≤ L := ellT_le_L
  have e1 : ellT L g t * (qdecY g t)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hy]; exact hell1
  have e2 : ellT L g t * (L : ℝ)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hL0]; exact hell2
  unfold qdecU; rw [mul_add]; linarith

/-- The derivative of `u_t`, `|∂_t u_t| ≤ u_t / (2 (1 - t))`. -/
private theorem qdecU_deriv {L : ℕ} [NeZero L] {g t : ℝ} (hg : 0 < g) (ht : t < 1) :
    ∃ u' : ℝ, HasDerivAt (qdecU L g) u' t ∧ |u'| ≤ qdecU L g t / (2 * (1 - t)) := by
  have h1t : 0 < 1 - t := by linarith
  have hr : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 h1t
  have hy : 0 < qdecY g t := lt_trans zero_lt_one (qdecY_gt hg ht)
  have h1 : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub 1
  have h2 : HasDerivAt (fun s : ℝ => Real.sqrt (1 - s)) (-1 / (2 * Real.sqrt (1 - t))) t :=
    h1.sqrt h1t.ne'
  have h3 := (hasDerivAt_const t g).div h2 hr.ne'
  have h4 : HasDerivAt (qdecY g) ((0 * Real.sqrt (1 - t) - g * (-1 / (2 * Real.sqrt (1 - t)))) / Real.sqrt (1 - t) ^ 2) t :=
    h3.const_add 1
  have h5 := (h4.inv hy.ne').add_const ((L : ℝ)⁻¹)
  refine ⟨_, h5, ?_⟩
  set r := Real.sqrt (1 - t) with hrdef
  have hr2 : r ^ 2 = 1 - t := Real.sq_sqrt h1t.le
  set q := g / r with hq
  have hq0 : 0 < q := div_pos hg hr
  have hy' : qdecY g t = 1 + q := rfl
  have hder : (0 * r - g * (-1 / (2 * r))) / r ^ 2 = q / (2 * r ^ 2) := by
    rw [hq]; field_simp; ring
  rw [hder]
  have hq_le : q ≤ qdecY g t := by rw [hy']; linarith
  have habs : |-(q / (2 * r ^ 2)) / qdecY g t ^ 2| = (q / (2 * r ^ 2)) / qdecY g t ^ 2 := by
    rw [abs_div, abs_neg, abs_of_pos (by positivity), abs_of_pos (by positivity)]
  rw [habs, ← hr2]
  have hu : (qdecY g t)⁻¹ ≤ qdecU L g t := by
    unfold qdecU; have := inv_nonneg.2 (Nat.cast_nonneg (α := ℝ) L); linarith
  calc (q / (2 * r ^ 2)) / qdecY g t ^ 2 = (q / qdecY g t ^ 2) / (2 * r ^ 2) := by ring
    _ ≤ (qdecY g t)⁻¹ / (2 * r ^ 2) := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        rw [div_le_iff₀ (by positivity)]
        calc q ≤ qdecY g t := hq_le
          _ = (qdecY g t)⁻¹ * qdecY g t ^ 2 := by field_simp
    _ ≤ qdecU L g t / (2 * r ^ 2) := div_le_div_of_nonneg_right hu (by positivity)


/-- The derivative bound for the one-dimensional masses: `u z₂(u) ≤ 40 z(u)` for `L⁻¹ < u ≤ 4/3`. -/
private theorem qdec_u_Z2_le {L : ℕ} [NeZero L] {u : ℝ} (hu : 0 < u) (huL : (L : ℝ)⁻¹ < u)
    (hu4 : u ≤ 4 / 3) : u * qdecZ2 L u ≤ 40 * qdecZ1 L u := by
  set r := Real.exp (-u) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r ≤ (1 + u)⁻¹ := by
    rw [hr, Real.exp_neg]
    exact inv_anti₀ (by linarith) (by linarith [Real.add_one_le_exp u])
  have h1u : 0 < 1 + u := by linarith
  have hgap : u / (1 + u) ≤ 1 - r := by
    have : 1 - (1 + u)⁻¹ = u / (1 + u) := by field_simp; ring
    linarith
  have hgap0 : 0 < u / (1 + u) := by positivity
  have hr_le1 : r ≤ 1 := by
    have : (1 + u)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    linarith
  have h2 : r / (1 - r) ^ 2 ≤ (1 + u) ^ 2 / u ^ 2 := by
    have h3 : (u / (1 + u)) ^ 2 ≤ (1 - r) ^ 2 := pow_le_pow_left₀ hgap0.le hgap 2
    calc r / (1 - r) ^ 2 ≤ 1 / (1 - r) ^ 2 := div_le_div_of_nonneg_right hr_le1 (by positivity)
      _ ≤ 1 / (u / (1 + u)) ^ 2 := one_div_le_one_div_of_le (by positivity) h3
      _ = (1 + u) ^ 2 / u ^ 2 := by field_simp
  have hz2 : qdecZ2 L u ≤ 2 * ((1 + u) ^ 2 / u ^ 2) := (qdecZ2_le hu).trans (by linarith)
  have hz1 := qdecZ1_ge hu huL
  have he : Real.exp 1 < 2.72 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  -- `u z₂ ≤ 2 (1+u)²/u ≤ 40/(e u) ≤ 40 z`
  have h4 : u * qdecZ2 L u ≤ 2 * (1 + u) ^ 2 / u := by
    calc u * qdecZ2 L u ≤ u * (2 * ((1 + u) ^ 2 / u ^ 2)) := mul_le_mul_of_nonneg_left hz2 hu.le
      _ = 2 * (1 + u) ^ 2 / u := by field_simp
  have h5 : 2 * (1 + u) ^ 2 / u ≤ 40 * ((Real.exp 1)⁻¹ * u⁻¹) := by
    rw [show 40 * ((Real.exp 1)⁻¹ * u⁻¹) = 40 / (Real.exp 1 * u) by field_simp]
    rw [div_le_div_iff₀ hu (by positivity)]
    have h7 : (1 + u) ^ 2 ≤ 49 / 9 := by nlinarith
    have h6 : 2 * (1 + u) ^ 2 * Real.exp 1 ≤ 40 := by nlinarith [sq_nonneg (1 + u)]
    nlinarith [mul_le_mul_of_nonneg_right h6 hu.le]
  calc u * qdecZ2 L u ≤ 40 * ((Real.exp 1)⁻¹ * u⁻¹) := h4.trans h5
    _ ≤ 40 * qdecZ1 L u := mul_le_mul_of_nonneg_left hz1 (by norm_num)

/-- `S(a) = Σ_{i ≥ 2} |a_i - a₁|`. -/
private def qdecS {d L m : ℕ} [NeZero L] (a : Fin (m + 1) → Zd d L) : ℝ :=
  ∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)), (zdistD d L (a i - a 0) : ℝ)

private theorem qdecS_nonneg {d L m : ℕ} [NeZero L] (a : Fin (m + 1) → Zd d L) : 0 ≤ qdecS a :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- `Φ_a(u) = exp(-u S(a)) / z(u)^{d m}`. -/
private def qdecPhi (d L m : ℕ) [NeZero L] (a : Fin (m + 1) → Zd d L) (u : ℝ) : ℝ :=
  Real.exp (-u * qdecS a) / (qdecZ1 L u) ^ (d * m)

private theorem qdecZ1_hasDerivAt (L : ℕ) [NeZero L] (u : ℝ) : HasDerivAt (qdecZ1 L) (-qdecZ2 L u) u := by
  have h : ∀ y ∈ (Finset.univ : Finset (ZMod L)),
      HasDerivAt (fun v : ℝ => Real.exp (-v * (zdist L y : ℝ)))
        (-((zdist L y : ℝ) * Real.exp (-u * (zdist L y : ℝ)))) u := by
    intro y _
    have h1 : HasDerivAt (fun v : ℝ => -v * (zdist L y : ℝ)) (-(zdist L y : ℝ)) u := by
      simpa using ((hasDerivAt_id u).neg.mul_const (zdist L y : ℝ))
    have h2 := h1.exp
    convert h2 using 1; ring
  have h3 := HasDerivAt.fun_sum h
  unfold qdecZ1 qdecZ2
  rw [Finset.sum_neg_distrib] at h3
  exact h3

private theorem qdecPhi_hasDerivAt (L : ℕ) [NeZero L] (S : ℝ) (n : ℕ) (u : ℝ) :
    HasDerivAt (fun v : ℝ => Real.exp (-v * S) / (qdecZ1 L v) ^ n)
      (Real.exp (-u * S) / (qdecZ1 L u) ^ n * (-S + n * qdecZ2 L u / qdecZ1 L u)) u := by
  have hz : 0 < qdecZ1 L u := qdecZ1_pos u
  have h1 : HasDerivAt (fun v : ℝ => Real.exp (-v * S)) (Real.exp (-u * S) * (-S)) u := by
    have h0 : HasDerivAt (fun v : ℝ => -v * S) (-S) u := by
      simpa using ((hasDerivAt_id u).neg.mul_const S)
    exact h0.exp
  have h2 : HasDerivAt (fun v : ℝ => (qdecZ1 L v) ^ n)
      ((n : ℝ) * (qdecZ1 L u) ^ (n - 1) * (-qdecZ2 L u)) u := (qdecZ1_hasDerivAt L u).pow n
  have h3 := h1.div h2 (pow_pos hz n).ne'
  convert h3 using 1
  rcases n with _ | n
  · simp
  · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    field_simp
    ring

/-- `z(u_t)⁻¹ ≤ 6 / ℓ_t`. -/
private theorem qdec_Zinv_le {L : ℕ} [NeZero L] {g t : ℝ} (hg : 0 < g) (ht : t < 1) :
    (qdecZ1 L (qdecU L g t))⁻¹ ≤ 6 * (ellT L g t)⁻¹ := by
  have hu := qdecU_pos (L := L) hg ht
  have hz := qdecZ1_ge hu (qdecU_gt (L := L) hg ht)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hl : 0 < ellT L g t := ellT_pos hL1
  have hub := qdecU_ub (L := L) hg ht
  have he : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9.trans (by norm_num)).le
  have he0 := Real.exp_pos 1
  -- `ℓ/2 ≤ u⁻¹`
  have h1 : ellT L g t / 2 ≤ (qdecU L g t)⁻¹ := by
    rw [← one_div, le_div_iff₀ hu]; linarith
  have h2 : ((Real.exp 1)⁻¹ * (ellT L g t / 2)) ≤ qdecZ1 L (qdecU L g t) :=
    le_trans (mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 he0.le)) hz
  have h3 : 0 < (Real.exp 1)⁻¹ * (ellT L g t / 2) := by positivity
  calc (qdecZ1 L (qdecU L g t))⁻¹ ≤ ((Real.exp 1)⁻¹ * (ellT L g t / 2))⁻¹ := inv_anti₀ h3 h2
    _ = 2 * Real.exp 1 * (ellT L g t)⁻¹ := by field_simp
    _ ≤ 6 * (ellT L g t)⁻¹ := by
        refine mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 hl.le)

private theorem qdec_inv_pow_eq (d m : ℕ) (x : ℝ) : ((x ^ d)⁻¹) ^ m = (x⁻¹) ^ (d * m) := by
  rw [pow_mul, inv_pow x d]

/-- Growth: `C W^p ≤ exp (c W^{ε'} / 2)` for large `W` (copy of `qn_growth`, `QopNorm.lean:343`). -/
private theorem qdec_growth {C c ε' p : ℝ} (hC : 0 < C) (hc : 0 < c) (hε' : 0 < ε') :
    ∃ W₁ : ℝ, 1 < W₁ ∧ ∀ W : ℝ, W₁ ≤ W → C * W ^ p ≤ Real.exp (c * W ^ ε' / 2) := by
  set q := p / ε' with hq
  have hκ : 0 < (C * (2 / c) ^ q)⁻¹ := by positivity
  have hlo := (isLittleO_rpow_exp_atTop q).def hκ
  have hT : Tendsto (fun W : ℝ => c * W ^ ε' / 2) atTop atTop := by
    have := (tendsto_rpow_atTop hε').const_mul_atTop hc
    exact this.atTop_div_const (by norm_num : (0 : ℝ) < 2)
  have hev := hT.eventually hlo
  obtain ⟨W₁, hW₁⟩ := Filter.eventually_atTop.1 (hev.and (Filter.eventually_gt_atTop (1 : ℝ)))
  refine ⟨max W₁ 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro W hW
  have hW2 : 2 ≤ W := (le_max_right _ _).trans hW
  obtain ⟨h1, h2⟩ := hW₁ W ((le_max_left _ _).trans hW)
  have hW0 : 0 < W := by linarith
  set y := c * W ^ ε' / 2 with hy
  have hy0 : 0 < y := by positivity
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hy0.le _), Real.norm_of_nonneg (Real.exp_pos y).le] at h1
  -- `W^p = (2/c)^q y^q`
  have hWp : W ^ p = (2 / c) ^ q * y ^ q := by
    have h3 : W ^ p = (W ^ ε') ^ q := by
      rw [← Real.rpow_mul hW0.le, hq]; field_simp
    have h4 : W ^ ε' = 2 / c * y := by rw [hy]; field_simp
    rw [h3, h4, Real.mul_rpow (by positivity) hy0.le]
  rw [hWp]
  have hy1 : y ^ q ≤ (C * (2 / c) ^ q)⁻¹ * Real.exp y := h1
  have hpos : 0 < C * (2 / c) ^ q := by positivity
  calc C * ((2 / c) ^ q * y ^ q) = (C * (2 / c) ^ q) * y ^ q := by ring
    _ ≤ (C * (2 / c) ^ q) * ((C * (2 / c) ^ q)⁻¹ * Real.exp y) := by gcongr
    _ = Real.exp y := by field_simp

/-! ## 2. The derivative of the mollifier -/

/-- The explicit mollifier is `Φ_a(u_t)` (the private definitions of `QopAlgebra.lean` unfold to the copies). -/
private theorem qdec_mollifier_eq (d L m : ℕ) [NeZero L] (g t : ℝ) (a : Fin (m + 1) → Zd d L) :
    QopAlgebra_mollifier d L m g t a = ((qdecPhi d L m a (qdecU L g t) : ℝ) : ℂ) := rfl

/-- `|(-S + n z₂/z) Φ| u ≤ (1 + 40 n) e^{-uS/2} / z^n` given `u z₂ ≤ 40 z` (`u S e^{-uS} ≤ e^{-uS/2}`). -/
private theorem qdec_core {u S z z₂ : ℝ} (n : ℕ) (hu : 0 < u) (hS : 0 ≤ S) (hz : 0 < z) (hz₂ : 0 ≤ z₂)
    (h : u * z₂ ≤ 40 * z) :
    |Real.exp (-u * S) / z ^ n * (-S + n * z₂ / z)| * u ≤
      (1 + 40 * (n : ℝ)) * Real.exp (-u * S / 2) / z ^ n := by
  have he0 : 0 < Real.exp (-u * S) := Real.exp_pos _
  have hh0 : 0 < Real.exp (-u * S / 2) := Real.exp_pos _
  have he : Real.exp (-u * S) ≤ Real.exp (-u * S / 2) := Real.exp_le_exp.2 (by nlinarith)
  have hx : u * S * Real.exp (-u * S) ≤ Real.exp (-u * S / 2) := by
    set y := u * S / 2 with hy
    have hy0 : 0 ≤ y := by positivity
    have h1 : 2 * y ≤ Real.exp y := by nlinarith [Real.quadratic_le_exp_of_nonneg hy0, sq_nonneg (y - 1)]
    have e1 : Real.exp (-u * S) = Real.exp (-y) * Real.exp (-y) := by
      rw [← Real.exp_add]; congr 1; rw [hy]; ring
    have e2 : Real.exp (-u * S / 2) = Real.exp (-y) := by congr 1; rw [hy]; ring
    have e3 : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
    have e4 : u * S = 2 * y := by rw [hy]; ring
    rw [e1, e2, e4]
    calc 2 * y * (Real.exp (-y) * Real.exp (-y)) = (2 * y) * Real.exp (-y) * Real.exp (-y) := by ring
      _ ≤ Real.exp y * Real.exp (-y) * Real.exp (-y) := by gcongr
      _ = Real.exp (-y) := by rw [e3, one_mul]
  have hzn : 0 < z ^ n := pow_pos hz n
  have hnz : 0 ≤ (n : ℝ) * z₂ / z := div_nonneg (mul_nonneg n.cast_nonneg hz₂) hz.le
  have habs : |-S + n * z₂ / z| ≤ S + n * z₂ / z := by
    rw [abs_le]; constructor <;> linarith
  have huz : u * z₂ / z ≤ 40 := by rw [div_le_iff₀ hz]; exact h
  rw [abs_mul, abs_of_pos (div_pos he0 hzn)]
  calc Real.exp (-u * S) / z ^ n * |-S + n * z₂ / z| * u
      ≤ Real.exp (-u * S) / z ^ n * (S + n * z₂ / z) * u := by gcongr
    _ = (u * S * Real.exp (-u * S) + (n : ℝ) * (u * z₂ / z) * Real.exp (-u * S)) / z ^ n := by
        field_simp
    _ ≤ (1 + 40 * (n : ℝ)) * Real.exp (-u * S / 2) / z ^ n := by
        refine div_le_div_of_nonneg_right ?_ hzn.le
        have h1 : (n : ℝ) * (u * z₂ / z) * Real.exp (-u * S) ≤ (n : ℝ) * 40 * Real.exp (-u * S / 2) := by
          calc (n : ℝ) * (u * z₂ / z) * Real.exp (-u * S)
              ≤ (n : ℝ) * (u * z₂ / z) * Real.exp (-u * S / 2) :=
                mul_le_mul_of_nonneg_left he (mul_nonneg n.cast_nonneg (by positivity))
            _ ≤ (n : ℝ) * 40 * Real.exp (-u * S / 2) := by gcongr
        nlinarith

/-- The derivative of `t ↦ Φ_a(u_t)` and its decaying bound, for `t < 1`, `L ≥ 3`. -/
private theorem qdec_deriv_real (d L m : ℕ) [NeZero L] {g t : ℝ} (hg : 0 < g) (ht : t < 1)
    (hL : 3 ≤ L) (a : Fin (m + 1) → Zd d L) :
    ∃ x : ℝ, HasDerivAt (fun τ => qdecPhi d L m a (qdecU L g τ)) x t ∧
      |x| ≤ (1 + 40 * ((d * m : ℕ) : ℝ)) * 6 ^ (d * m) * (1 - t)⁻¹ * ((ellT L g t)⁻¹) ^ (d * m) *
        Real.exp (-(1 / 4) * qdecS a / ellT L g t) := by
  obtain ⟨u', hu', hu'b⟩ := qdecU_deriv (L := L) hg ht
  have hu := qdecU_pos (L := L) hg ht
  have huL := qdecU_gt (L := L) hg ht
  have hu4 := qdecU_le hL hg ht
  have hlb := qdecU_lb (L := L) hg ht
  set u := qdecU L g t with hudef
  have hΦ : HasDerivAt (qdecPhi d L m a)
      (Real.exp (-u * qdecS a) / (qdecZ1 L u) ^ (d * m) *
        (-qdecS a + ((d * m : ℕ) : ℝ) * qdecZ2 L u / qdecZ1 L u)) u :=
    qdecPhi_hasDerivAt L (qdecS a) (d * m) u
  have hc := hΦ.comp t hu'
  refine ⟨_, hc, ?_⟩
  have hz := qdecZ1_pos (L := L) u
  have h40 := qdec_u_Z2_le hu huL hu4
  have hz₂ : 0 ≤ qdecZ2 L u := Finset.sum_nonneg fun _ _ => by positivity
  have hcore := qdec_core (z := qdecZ1 L u) (d * m) hu (qdecS_nonneg a) hz hz₂ h40
  have h1t : 0 < 1 - t := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hl : 0 < ellT L g t := ellT_pos hL1
  have hS := qdecS_nonneg a
  set P := Real.exp (-u * qdecS a) / (qdecZ1 L u) ^ (d * m) *
    (-qdecS a + ((d * m : ℕ) : ℝ) * qdecZ2 L u / qdecZ1 L u) with hP
  have hzn : 0 < (qdecZ1 L u) ^ (d * m) := pow_pos hz _
  have hexp : Real.exp (-u * qdecS a / 2) ≤ Real.exp (-(1 / 4) * qdecS a / ellT L g t) := by
    refine Real.exp_le_exp.2 ?_
    have h2 : -(1 / 4 : ℝ) * qdecS a / ellT L g t = -(qdecS a * (2 * ellT L g t)⁻¹) / 2 := by
      field_simp; ring
    rw [h2]
    have := mul_le_mul_of_nonneg_left hlb hS
    linarith
  have h2 : |P * u'| ≤ (1 + 40 * ((d * m : ℕ) : ℝ)) * Real.exp (-u * qdecS a / 2) /
      (qdecZ1 L u) ^ (d * m) / (2 * (1 - t)) := by
    rw [abs_mul]
    calc |P| * |u'| ≤ |P| * (u / (2 * (1 - t))) := mul_le_mul_of_nonneg_left hu'b (abs_nonneg _)
      _ = (|P| * u) / (2 * (1 - t)) := by ring
      _ ≤ (1 + 40 * ((d * m : ℕ) : ℝ)) * Real.exp (-u * qdecS a / 2) /
          (qdecZ1 L u) ^ (d * m) / (2 * (1 - t)) :=
          div_le_div_of_nonneg_right hcore (by positivity)
  have hinv := qdec_Zinv_le (L := L) hg ht
  have h3 : 1 / (qdecZ1 L u) ^ (d * m) ≤ 6 ^ (d * m) * ((ellT L g t)⁻¹) ^ (d * m) := by
    rw [one_div, ← inv_pow, ← mul_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 hz.le) (by simpa [hudef] using hinv) _
  have hn : 0 ≤ 1 + 40 * ((d * m : ℕ) : ℝ) := by positivity
  have hℓinv : 0 ≤ (ellT L g t)⁻¹ := inv_nonneg.2 hl.le
  have hX : 0 ≤ (1 + 40 * ((d * m : ℕ) : ℝ)) * (6 ^ (d * m) * ((ellT L g t)⁻¹) ^ (d * m)) * (1 - t)⁻¹ *
      Real.exp (-(1 / 4) * qdecS a / ellT L g t) := by positivity
  change |P * u'| ≤ _
  calc |P * u'| ≤ (1 + 40 * ((d * m : ℕ) : ℝ)) * Real.exp (-u * qdecS a / 2) /
          (qdecZ1 L u) ^ (d * m) / (2 * (1 - t)) := h2
    _ = (1 + 40 * ((d * m : ℕ) : ℝ)) * (1 / (qdecZ1 L u) ^ (d * m)) * (1 - t)⁻¹ *
          Real.exp (-u * qdecS a / 2) / 2 := by field_simp
    _ ≤ (1 + 40 * ((d * m : ℕ) : ℝ)) * (6 ^ (d * m) * ((ellT L g t)⁻¹) ^ (d * m)) * (1 - t)⁻¹ *
          Real.exp (-(1 / 4) * qdecS a / ellT L g t) / 2 := by gcongr
    _ ≤ (1 + 40 * ((d * m : ℕ) : ℝ)) * 6 ^ (d * m) * (1 - t)⁻¹ * ((ellT L g t)⁻¹) ^ (d * m) *
          Real.exp (-(1 / 4) * qdecS a / ellT L g t) := by
        have e : (1 + 40 * ((d * m : ℕ) : ℝ)) * 6 ^ (d * m) * (1 - t)⁻¹ * ((ellT L g t)⁻¹) ^ (d * m) *
            Real.exp (-(1 / 4) * qdecS a / ellT L g t) =
            (1 + 40 * ((d * m : ℕ) : ℝ)) * (6 ^ (d * m) * ((ellT L g t)⁻¹) ^ (d * m)) * (1 - t)⁻¹ *
              Real.exp (-(1 / 4) * qdecS a / ellT L g t) := by ring
        rw [e]; linarith

/-- **Target 1.** The time derivative of the explicit mollifier decays like the mollifier itself: constants
`C = (1 + 40 d m) 6^{d m}` (that of `QopAlgebra_mollifier_props`), `c = 1/4`, factor `(1 - t)⁻¹` as in clause 4 of
`STMollifierProps` (`rmk:choosechi` `3_5:1250`; `(eq:derv_Theta)` `3_5:1215` states only the size). -/
theorem QopAlgebra_mollifier_derivDecay (d L m : ℕ) [NeZero L] (hL : 3 ≤ L) {g : ℝ} (hg : 0 < g)
    (t : ℝ) (_ht0 : 0 ≤ t) (ht : t < 1) (a : Fin (m + 1) → Zd d L) :
    ‖deriv (fun τ => QopAlgebra_mollifier d L m g τ a) t‖ ≤
      (1 + 40 * ((d * m : ℕ) : ℝ)) * 6 ^ (d * m) * (1 - t)⁻¹ * (((ellT L g t) ^ d)⁻¹) ^ m *
        Real.exp (-(1 / 4) * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)),
          (zdistD d L (a i - a 0) : ℝ)) / ellT L g t) := by
  obtain ⟨x, hx, hxb⟩ := qdec_deriv_real d L m hg ht hL a
  have hd : HasDerivAt (fun τ => QopAlgebra_mollifier d L m g τ a) (x : ℂ) t := hx.ofReal_comp
  rw [hd.deriv, Complex.norm_real, Real.norm_eq_abs, qdec_inv_pow_eq]
  unfold qdecS at hxb
  exact hxb

/-! ## 3. `EKFastDecay` of the source `(𝒫f)_{a₁} ∂_tϑ_{t,a}` -/

/-- **Target 2.** The `STExpQsrc` source `B(a₀) ∂_tϑ_{t,a}` is `(t, ε', D')`-decaying for every `ε', D'` once
`W ≥ W₀(d, m, K, C₀, ε', D')`, if `‖B‖ ≤ W^{C₀}` and `(1 - t)⁻¹ ≤ W^K` (pattern of `stQop_sub_fastDecay`;
no `L^d ≤ W^K` is needed). -/
theorem QopDecay_deriv_fastDecay (d m : ℕ) (K C₀ ε' D' : ℝ) (hε' : 0 < ε') :
    ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g →
      ∀ W : ℝ, W₀ ≤ W → ∀ t : ℝ, 0 ≤ t → t < 1 → (1 - t)⁻¹ ≤ W ^ K →
      ∀ B : Zd d L → ℂ, ‖B‖ ≤ W ^ C₀ →
        EKFastDecay g t W ε' D'
          (fun a : Fin (m + 1) → Zd d L => B (a 0) *
            deriv (fun τ => QopAlgebra_mollifier d L m g τ a) t) := by
  have hC : 0 < (1 + 40 * ((d * m : ℕ) : ℝ)) * 6 ^ (d * m) := by positivity
  obtain ⟨W₁, hW₁, hW₁'⟩ := qdec_growth (p := C₀ + K + D') hC (by norm_num : (0 : ℝ) < 1 / 4) hε'
  refine ⟨W₁, hW₁, ?_⟩
  intro L _ hL g hg W hW t ht0 ht1 hK B hB a ha
  set C := (1 + 40 * ((d * m : ℕ) : ℝ)) * 6 ^ (d * m) with hCdef
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hW1 : 1 < W := lt_of_lt_of_le hW₁ hW
  have hW0 : 0 < W := by linarith
  set ℓ := ellT L g t with hℓ
  have hℓ1 : 1 ≤ ℓ := one_le_ellT hL1
  obtain ⟨i, j, hij⟩ := ha
  have hR : 0 < W ^ ε' * ℓ := by positivity
  set S := ∑ k ∈ Finset.univ.erase (0 : Fin (m + 1)), (zdistD d L (a k - a 0) : ℝ) with hS
  have hSge : W ^ ε' * ℓ / 2 ≤ S := by
    have htri : (zdistD d L (a i - a j) : ℝ) ≤ (zdistD d L (a i - a 0) : ℝ) + (zdistD d L (a j - a 0) : ℝ) := by
      have : a i - a j = (a i - a 0) + -(a j - a 0) := by ring
      have h2 := zdistD_add_le d L (a i - a 0) (-(a j - a 0))
      rw [← this, zdistD_neg] at h2
      exact_mod_cast h2
    have hmem : ∀ k : Fin (m + 1), (zdistD d L (a k - a 0) : ℝ) ≤ S := by
      intro k
      by_cases hk : k = 0
      · subst hk
        simp only [sub_self, zdistD_zero, Nat.cast_zero]
        exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
      · exact Finset.single_le_sum (f := fun k => (zdistD d L (a k - a 0) : ℝ))
          (fun _ _ => Nat.cast_nonneg _) (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩)
    have hi' := hmem i
    have hj' := hmem j
    linarith
  set y := (1 / 4 : ℝ) * W ^ ε' / 2 with hy
  have hexp : Real.exp (-(1 / 4) * S / ℓ) ≤ Real.exp (-y) := by
    refine Real.exp_le_exp.2 ?_
    have : y ≤ (1 / 4 : ℝ) * S / ℓ := by
      rw [le_div_iff₀ (by linarith)]
      have := mul_le_mul_of_nonneg_left hSge (by norm_num : (0 : ℝ) ≤ 1 / 4)
      nlinarith
    have h2 : -(1 / 4 : ℝ) * S / ℓ = -((1 / 4 : ℝ) * S / ℓ) := by ring
    rw [h2]; linarith
  have hθ := QopAlgebra_mollifier_derivDecay d L m hL hg t ht0 ht1 a
  have hθ' : ‖deriv (fun τ => QopAlgebra_mollifier d L m g τ a) t‖ ≤ C * W ^ K * Real.exp (-y) := by
    have hinv : ((ℓ ^ d)⁻¹) ^ m ≤ 1 := by
      have : (ℓ ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hℓ1)
      exact pow_le_one₀ (by positivity) this
    refine hθ.trans ?_
    calc C * (1 - t)⁻¹ * ((ℓ ^ d)⁻¹) ^ m * Real.exp (-(1 / 4) * S / ℓ)
        ≤ C * W ^ K * 1 * Real.exp (-y) := by gcongr
      _ = _ := by ring
  rw [norm_mul]
  set E := W ^ (C₀ + K) with hE
  set G := W ^ D' with hG
  have hE0 : 0 < E := Real.rpow_pos_of_pos hW0 _
  have hG0 : 0 < G := Real.rpow_pos_of_pos hW0 _
  have hgr := hW₁' W hW
  have hp : W ^ (C₀ + K + D') = E * G := by rw [Real.rpow_add hW0]
  rw [hp] at hgr
  have hWD : W ^ (-D') = G⁻¹ := Real.rpow_neg hW0.le D'
  rw [hWD]
  have hBa : ‖B (a 0)‖ ≤ W ^ C₀ := (norm_le_pi_norm B (a 0)).trans hB
  have hmain : ‖B (a 0)‖ * ‖deriv (fun τ => QopAlgebra_mollifier d L m g τ a) t‖ ≤
      W ^ C₀ * (C * W ^ K * Real.exp (-y)) :=
    mul_le_mul hBa hθ' (norm_nonneg _) (Real.rpow_pos_of_pos hW0 _).le
  have hEe : W ^ C₀ * W ^ K = E := by rw [hE, Real.rpow_add hW0]
  refine hmain.trans ?_
  have h1 : W ^ C₀ * (C * W ^ K * Real.exp (-y)) * G ≤ 1 := by
    calc W ^ C₀ * (C * W ^ K * Real.exp (-y)) * G = (C * (E * G)) * Real.exp (-y) := by
          rw [← hEe]; ring
      _ ≤ Real.exp y * Real.exp (-y) := by gcongr
      _ = 1 := by rw [← Real.exp_add]; simp
  calc W ^ C₀ * (C * W ^ K * Real.exp (-y))
      = W ^ C₀ * (C * W ^ K * Real.exp (-y)) * G * G⁻¹ := by field_simp
    _ ≤ 1 * G⁻¹ := by gcongr
    _ = G⁻¹ := one_mul _

/-! ## 4. The one-index kernel of `Θ^{(n)}_u` -/

/-- A unit complex number has a unit square root. -/
private theorem qdec_sqrt_unit (μ : ℂ) (hμ : ‖μ‖ = 1) : ∃ m : ℂ, ‖m‖ = 1 ∧ m * m = μ := by
  obtain ⟨m, hm⟩ := IsAlgClosed.exists_pow_nat_eq μ (by norm_num : 0 < 2)
  refine ⟨m, ?_, by rw [← hm]; ring⟩
  have h : ‖m‖ ^ 2 = 1 := by rw [← norm_pow, hm, hμ]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h

/-- The nearest-neighbour kernel is supported on `|x - z| ≤ 1`. -/
private theorem qdec_sbKernel_support (d L : ℕ) (g : ℝ) (w : Zd d L)
    (h : sbKernel d L g w ≠ 0) : zdistD d L w ≤ 1 := by
  by_cases h0 : w = 0
  · subst h0; simp
  · by_cases h1 : zdistD d L w = 1
    · exact h1.le
    · exact absurd (by simp [sbKernel, h0, h1]) h

/-- `B_{u,K} ≤ 2 (1 - u)⁻¹`. -/
private theorem qdec_Bparam_le (d L : ℕ) (g u : ℝ) (hL : 1 ≤ L) (hu : u < 1) (K : ℕ) :
    Bparam d L g u K ≤ 2 * (1 - u)⁻¹ := by
  have h1u : 0 < 1 - u := by linarith
  have habs : |1 - u| = 1 - u := abs_of_pos h1u
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  unfold Bparam
  rw [habs]
  have a1 : (g ^ 2 + (1 - u))⁻¹ ≤ (1 - u)⁻¹ :=
    inv_anti₀ h1u (by nlinarith [sq_nonneg g])
  have a2 : (((K : ℝ) + 1) ^ (d - 2))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by have : (0 : ℝ) ≤ K := Nat.cast_nonneg K; linarith))
  have a3 : ((L : ℝ) ^ d * (1 - u))⁻¹ ≤ (1 - u)⁻¹ :=
    inv_anti₀ h1u (by nlinarith [one_le_pow₀ (n := d) hL1])
  have a4 : 0 ≤ (g ^ 2 + (1 - u))⁻¹ := inv_nonneg.2 (by nlinarith [sq_nonneg g])
  have a5 : 0 ≤ (((K : ℝ) + 1) ^ (d - 2))⁻¹ := inv_nonneg.2 (by positivity)
  calc (g ^ 2 + (1 - u))⁻¹ * (((K : ℝ) + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * (1 - u))⁻¹
      ≤ (1 - u)⁻¹ * 1 + (1 - u)⁻¹ := by gcongr
    _ = 2 * (1 - u)⁻¹ := by ring

/-- **Target 3.** The one-index kernel `μ S^{(B)} Θ_{uμ}` of `Θ^{(n)}_u` (`(def:op_thn)`, `3_5:112`) decays at the
scale `ℓ_u` with prefactor `(1 - u)⁻¹`, for every `|μ| = 1`: property 5 (`Prop5Decay`, at a square root
`m` of `μ`, signs `(+,+)`), `B_{u,K} ≤ 2 (1 - u)⁻¹`, and the nearest-neighbour convolution; constants `(d, Λ)`. -/
theorem QopDecay_thetaKer_decay (d : ℕ) (hd : 3 ≤ d) (Λ : ℝ) (hΛ : 0 < Λ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g → g ≤ Λ →
        ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ μ : ℂ, ‖μ‖ = 1 → ∀ x y : Zd d L,
          ‖thetaKer d L g μ u x y‖ ≤
            C * (1 - u)⁻¹ * Real.exp (-c * (zdistD d L (y - x) : ℝ) / ellT L g u) := by
  obtain ⟨C₅, hC₅, c₅, hc₅, h5⟩ := prop5Decay_holds d Λ hd hΛ
  refine ⟨2 * C₅ * Real.exp c₅, c₅, by positivity, hc₅, ?_⟩
  intro L _ hL g hg hgΛ u hu0 hu1 μ hμ x y
  obtain ⟨m, hm, hmm⟩ := qdec_sqrt_unit μ hμ
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hℓ1 : 1 ≤ ellT L g u := one_le_ellT hL1
  have hℓ0 : 0 < ellT L g u := lt_of_lt_of_le zero_lt_one hℓ1
  have hξ : ‖(u : ℂ) * μ‖ < 1 := by
    rw [norm_mul, hμ, mul_one, Complex.norm_real, Real.norm_of_nonneg hu0]; exact hu1
  have h1u : 0 < (1 - u)⁻¹ := inv_pos.2 (by linarith)
  set R := 2 * C₅ * Real.exp c₅ * (1 - u)⁻¹ * Real.exp (-c₅ * (zdistD d L (y - x) : ℝ) / ellT L g u)
    with hR
  have hz : ∀ z : Zd d L, ‖SB d L g x z‖ * ‖Theta d L g ((u : ℂ) * μ) z y‖ ≤ ‖SB d L g x z‖ * R := by
    intro z
    by_cases hSz : SB d L g x z = 0
    · simp [hSz]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hsup : zdistD d L (x - z) ≤ 1 := qdec_sbKernel_support d L g _ (by rwa [SB_apply] at hSz)
    have hT : Theta d L g ((u : ℂ) * μ) z y = Theta d L g ((u : ℂ) * μ) 0 (y - z) := by
      have := Theta_apply_add_right_of_three_le (d := d) (L := L) (g := g) hL hξ 0 (y - z) z
      simpa using this
    have hP := h5 L hL g hg hgΛ u hu0 hu1 m hm true true (y - z)
    have hpm : PropSpin m true * PropSpin m true = μ := by simpa [PropSpin] using hmm
    rw [hpm] at hP
    rw [hT]
    refine hP.trans ?_
    have hB := qdec_Bparam_le d L g u (by omega) hu1 (zdistD d L (y - z))
    have hdist : (zdistD d L (y - x) : ℝ) ≤ (zdistD d L (y - z) : ℝ) + 1 := by
      have h2 := zdistD_add_le d L (y - z) (z - x)
      have e : y - z + (z - x) = y - x := by ring
      rw [e] at h2
      have h3 : zdistD d L (z - x) = zdistD d L (x - z) := by
        rw [← zdistD_neg d L (z - x)]; congr 1; ring
      have : zdistD d L (y - x) ≤ zdistD d L (y - z) + 1 := by omega
      exact_mod_cast this
    have hexp : Real.exp (-c₅ * (zdistD d L (y - z) : ℝ) / ellT L g u) ≤
        Real.exp c₅ * Real.exp (-c₅ * (zdistD d L (y - x) : ℝ) / ellT L g u) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have h4 : c₅ * ((zdistD d L (y - x) : ℝ) - (zdistD d L (y - z) : ℝ)) / ellT L g u ≤ c₅ := by
        rw [div_le_iff₀ hℓ0]
        nlinarith [mul_le_mul_of_nonneg_left (by linarith : (zdistD d L (y - x) : ℝ) -
          (zdistD d L (y - z) : ℝ) ≤ 1) hc₅.le, mul_le_mul_of_nonneg_left hℓ1 hc₅.le]
      have e1 : -c₅ * (zdistD d L (y - z) : ℝ) / ellT L g u =
          -c₅ * (zdistD d L (y - x) : ℝ) / ellT L g u +
            c₅ * ((zdistD d L (y - x) : ℝ) - (zdistD d L (y - z) : ℝ)) / ellT L g u := by ring
      rw [e1]; linarith
    have hCB : 0 ≤ C₅ * Bparam d L g u (zdistD d L (y - z)) := by
      unfold Bparam
      have : 0 ≤ (g ^ 2 + |1 - u|)⁻¹ := inv_nonneg.2 (by positivity)
      positivity
    calc C₅ * Bparam d L g u (zdistD d L (y - z)) *
          Real.exp (-c₅ * (zdistD d L (y - z) : ℝ) / ellT L g u)
        ≤ (C₅ * (2 * (1 - u)⁻¹)) * (Real.exp c₅ * Real.exp (-c₅ * (zdistD d L (y - x) : ℝ) / ellT L g u)) := by
          gcongr
      _ = R := by rw [hR]; ring
  have hsum : thetaKer d L g μ u x y =
      ∑ z : Zd d L, μ * SB d L g x z * Theta d L g ((u : ℂ) * μ) z y := by
    unfold thetaKer
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul]
  rw [hsum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ z : Zd d L, ‖μ * SB d L g x z * Theta d L g ((u : ℂ) * μ) z y‖
      ≤ ∑ z : Zd d L, ‖SB d L g x z‖ * R := by
        refine Finset.sum_le_sum fun z _ => ?_
        rw [norm_mul, norm_mul, hμ, one_mul]
        exact hz z
    _ = R := by rw [← Finset.sum_mul, sum_norm_SB_row d L g hL x, one_mul]

/-! ## 5. Propagation of `(deccA0)` through `Θ^{(n)}_u` -/

/-- Far case of the near/far split: if every pair of `a^{(i)}(b)` is at distance `< r₁` and some pair
`(j, k)` of `a` is at distance `≥ r₂ ≥ 2 r₁`, then `|b - a_i| ≥ r₂ / 2` (necessarily `i ∈ {j, k}`). -/
private theorem qdec_far_dist {d L n : ℕ} [NeZero L] (a : Fin n → Zd d L) (b : Zd d L) (i j k : Fin n)
    {r₁ r₂ : ℝ} (hr : 2 * r₁ ≤ r₂)
    (hjk : r₂ ≤ (zdistD d L (a j - a k) : ℝ))
    (hfar : ∀ p q : Fin n,
      (zdistD d L (Function.update a i b p - Function.update a i b q) : ℝ) < r₁) :
    r₂ / 2 ≤ (zdistD d L (b - a i) : ℝ) := by
  by_cases hji : j = i
  · subst hji
    by_cases hki : k = j
    · subst hki
      simp at hjk
      linarith
    · have h1 := hfar j k
      rw [Function.update_self, Function.update_of_ne hki] at h1
      have h2 := zdistD_add_le d L (a j - b) (b - a k)
      have e : a j - b + (b - a k) = a j - a k := by ring
      rw [e] at h2
      have h3 : zdistD d L (a j - b) = zdistD d L (b - a j) := by
        rw [← zdistD_neg d L (a j - b)]; congr 1; ring
      have h4 : (zdistD d L (a j - a k) : ℝ) ≤ (zdistD d L (b - a j) : ℝ) + (zdistD d L (b - a k) : ℝ) := by
        exact_mod_cast (h3 ▸ h2)
      linarith
  · by_cases hki : k = i
    · subst hki
      have h1 := hfar j k
      rw [Function.update_self, Function.update_of_ne hji] at h1
      have h2 := zdistD_add_le d L (a j - b) (b - a k)
      have e : a j - b + (b - a k) = a j - a k := by ring
      rw [e] at h2
      have h4 : (zdistD d L (a j - a k) : ℝ) ≤ (zdistD d L (a j - b) : ℝ) + (zdistD d L (b - a k) : ℝ) := by
        exact_mod_cast h2
      have h3 : zdistD d L (a j - b) = zdistD d L (b - a j) := by
        rw [← zdistD_neg d L (a j - b)]; congr 1; ring
      have h5 := hfar j k
      rw [Function.update_of_ne hji, Function.update_self] at h5
      linarith
    · exfalso
      have h1 := hfar j k
      rw [Function.update_of_ne hji, Function.update_of_ne hki] at h1
      linarith

/-- **Target 4.** `Θ^{(n)}_u` maps a `(u, ε, D)`-decaying tensor of size `≤ W^{C₀}` to a `(u, 2ε, D - (K + 1))`-decaying
tensor for `W ≥ W₀(d, n, Λ, K, C₀, ε, D)`, `L^d ≤ W^K`, `(1 - u)⁻¹ ≤ W^K`; any tensor order `n`, any unit charges.
Near/far split of the sum over `b` in `(Θ^{(n)} A)_a = Σ_i Σ_b K_i(a_i, b) A(a^{(i)}(b))`: near terms by the row
sum `(1 - u)⁻¹` of `K_i` (`B45_row_thetaKer`) and the decay of `A`; far terms by the kernel decay (target 3). -/
theorem QopDecay_ThetaN_fastDecay (d n : ℕ) (hd : 3 ≤ d) (Λ K C₀ ε D : ℝ) (hΛ : 0 < Λ) (hε : 0 < ε) :
    ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g → g ≤ Λ →
      ∀ W : ℝ, W₀ ≤ W → (L : ℝ) ^ d ≤ W ^ K →
      ∀ u : ℝ, 0 ≤ u → u < 1 → (1 - u)⁻¹ ≤ W ^ K →
      ∀ μs : Fin n → ℂ, (∀ i, ‖μs i‖ = 1) →
      ∀ A : (Fin n → Zd d L) → ℂ, ‖A‖ ≤ W ^ C₀ → EKFastDecay g u W ε D A →
        EKFastDecay g u W (2 * ε) (D - (K + 1)) (ThetaN d L g μs u A) := by
  obtain ⟨C, c, hC, hc, hker⟩ := QopDecay_thetaKer_decay d hd Λ hΛ
  obtain ⟨W₁, hW₁, hgrow⟩ := qdec_growth (C := 2 * ((n : ℝ) + 1) * C) (c := c) (ε' := 2 * ε)
    (p := K + C₀ + D - 1) (by positivity) hc (by positivity)
  refine ⟨max W₁ (max ((2 : ℝ) ^ (1 / ε)) (2 * n)), lt_of_lt_of_le hW₁ (le_max_left _ _), ?_⟩
  intro L _ hL g hg hgΛ W hW hLW u hu0 hu1 hKu μs hμs A hA hAd a ⟨j, k, hjk⟩
  have hWW₁ : W₁ ≤ W := (le_max_left _ _).trans hW
  have hW2ε : (2 : ℝ) ^ (1 / ε) ≤ W := ((le_max_left _ _).trans (le_max_right _ _)).trans hW
  have hWn : 2 * (n : ℝ) ≤ W := ((le_max_right _ _).trans (le_max_right _ _)).trans hW
  have hW1 : 1 < W := lt_of_lt_of_le hW₁ hWW₁
  have hW0 : 0 < W := by linarith
  have hWε : 2 ≤ W ^ ε := by
    calc (2 : ℝ) = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
          rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), one_div, inv_mul_cancel₀ hε.ne', Real.rpow_one]
      _ ≤ W ^ ε := Real.rpow_le_rpow (by positivity) hW2ε hε.le
  have hWε2 : W ^ (2 * ε) = W ^ ε * W ^ ε := by rw [two_mul, Real.rpow_add hW0]
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  set ℓ := ellT L g u with hℓ
  have hℓ1 : 1 ≤ ℓ := one_le_ellT hL1
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le zero_lt_one hℓ1
  set x := c * W ^ (2 * ε) / 2 with hx
  have hr : 2 * (W ^ ε * ℓ) ≤ W ^ (2 * ε) * ℓ := by
    rw [hWε2]
    nlinarith [mul_nonneg (sub_nonneg.2 hWε) (mul_nonneg (by linarith : (0 : ℝ) ≤ W ^ ε) hℓ0.le)]
  have hpar : ∀ i : Fin n, ‖∑ b : Zd d L, thetaKer d L g (cycProd μs i) u (a i) b *
      A (Function.update a i b)‖ ≤
      W ^ K * W ^ (-D) + W ^ K * (C * W ^ K * W ^ C₀ * Real.exp (-x)) := by
    intro i
    have hconst : 0 ≤ C * W ^ K * W ^ C₀ * Real.exp (-x) := by positivity
    have hpt : ∀ b : Zd d L, ‖thetaKer d L g (cycProd μs i) u (a i) b * A (Function.update a i b)‖ ≤
        ‖thetaKer d L g (cycProd μs i) u (a i) b‖ * W ^ (-D) + C * W ^ K * W ^ C₀ * Real.exp (-x) := by
      intro b
      rw [norm_mul]
      by_cases hnear : ∃ p q : Fin n,
          W ^ ε * ℓ ≤ (zdistD d L (Function.update a i b p - Function.update a i b q) : ℝ)
      · have h1 : ‖A (Function.update a i b)‖ ≤ W ^ (-D) := hAd _ hnear
        have h2 := mul_le_mul_of_nonneg_left h1 (norm_nonneg (thetaKer d L g (cycProd μs i) u (a i) b))
        linarith
      · push Not at hnear
        have hdist := qdec_far_dist a b i j k hr hjk hnear
        have hKb := hker L hL g hg hgΛ u hu0 hu1 (cycProd μs i) (norm_cycProd hμs i) (a i) b
        have hexp : Real.exp (-c * (zdistD d L (b - a i) : ℝ) / ℓ) ≤ Real.exp (-x) := by
          refine Real.exp_le_exp.2 ?_
          have : x ≤ c * (zdistD d L (b - a i) : ℝ) / ℓ := by
            rw [le_div_iff₀ hℓ0, hx]
            nlinarith [mul_le_mul_of_nonneg_left hdist hc.le]
          have e : -c * (zdistD d L (b - a i) : ℝ) / ℓ = -(c * (zdistD d L (b - a i) : ℝ) / ℓ) := by ring
          rw [e]; linarith
        have hK1 : ‖thetaKer d L g (cycProd μs i) u (a i) b‖ ≤ C * W ^ K * Real.exp (-x) :=
          hKb.trans (by gcongr)
        have hA1 : ‖A (Function.update a i b)‖ ≤ W ^ C₀ := (norm_le_pi_norm A _).trans hA
        have h3 := mul_le_mul hK1 hA1 (norm_nonneg _) (by positivity)
        have h4 : 0 ≤ ‖thetaKer d L g (cycProd μs i) u (a i) b‖ * W ^ (-D) := by positivity
        calc _ ≤ C * W ^ K * Real.exp (-x) * W ^ C₀ := h3
          _ = C * W ^ K * W ^ C₀ * Real.exp (-x) := by ring
          _ ≤ _ := by linarith
    calc ‖∑ b : Zd d L, thetaKer d L g (cycProd μs i) u (a i) b * A (Function.update a i b)‖
        ≤ ∑ b : Zd d L, ‖thetaKer d L g (cycProd μs i) u (a i) b * A (Function.update a i b)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ b : Zd d L, (‖thetaKer d L g (cycProd μs i) u (a i) b‖ * W ^ (-D) +
            C * W ^ K * W ^ C₀ * Real.exp (-x)) := Finset.sum_le_sum fun b _ => hpt b
      _ = (∑ b : Zd d L, ‖thetaKer d L g (cycProd μs i) u (a i) b‖) * W ^ (-D) +
            (L : ℝ) ^ d * (C * W ^ K * W ^ C₀ * Real.exp (-x)) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, card_Zd,
            nsmul_eq_mul]
          push_cast; ring
      _ ≤ W ^ K * W ^ (-D) + W ^ K * (C * W ^ K * W ^ C₀ * Real.exp (-x)) := by
          have hrow := B45_row_thetaKer (d := d) (L := L) g hL (norm_cycProd hμs i) hu0 hu1 (a i)
          have : ∑ b : Zd d L, ‖thetaKer d L g (cycProd μs i) u (a i) b‖ ≤ W ^ K := hrow.trans hKu
          gcongr
  simp only [ThetaN]
  refine (norm_sum_le _ _).trans ?_
  have hQ0 : 0 ≤ W ^ K * W ^ (-D) := by positivity
  set Z := W ^ (-(D - (K + 1))) with hZ
  have hZ0 : 0 < Z := Real.rpow_pos_of_pos hW0 _
  have hZe : Z = W * (W ^ K * W ^ (-D)) := by
    rw [hZ, show -(D - (K + 1)) = 1 + K + -D by ring, Real.rpow_add hW0, Real.rpow_add hW0, Real.rpow_one]
    ring
  have hT1 : (n : ℝ) * (W ^ K * W ^ (-D)) ≤ Z / 2 := by
    rw [hZe]; linarith only [mul_le_mul_of_nonneg_right hWn hQ0]
  have hpow : W ^ K * W ^ K * W ^ C₀ = W ^ (K + C₀ + D - 1) * Z := by
    have h1 : W ^ K * W ^ K * W ^ C₀ = W ^ (K + K + C₀) := by rw [Real.rpow_add hW0, Real.rpow_add hW0]
    have h2 : W ^ (K + C₀ + D - 1) * Z = W ^ (K + C₀ + D - 1 + -(D - (K + 1))) := by
      rw [hZ, Real.rpow_add hW0]
    rw [h1, h2]; congr 1; ring
  have hg1 := hgrow W hWW₁
  set q := C * W ^ (K + C₀ + D - 1) * Real.exp (-x) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : 2 * ((n : ℝ) + 1) * q ≤ 1 := by
    calc 2 * ((n : ℝ) + 1) * q = (2 * ((n : ℝ) + 1) * C * W ^ (K + C₀ + D - 1)) * Real.exp (-x) := by
          rw [hq]; ring
      _ ≤ Real.exp x * Real.exp (-x) := by gcongr
      _ = 1 := by rw [← Real.exp_add]; simp
  have hT2 : (n : ℝ) * (W ^ K * (C * W ^ K * W ^ C₀ * Real.exp (-x))) ≤ Z / 2 := by
    have e : W ^ K * (C * W ^ K * W ^ C₀ * Real.exp (-x)) = Z * q := by
      calc W ^ K * (C * W ^ K * W ^ C₀ * Real.exp (-x)) = C * (W ^ K * W ^ K * W ^ C₀) * Real.exp (-x) := by ring
        _ = C * (W ^ (K + C₀ + D - 1) * Z) * Real.exp (-x) := by rw [hpow]
        _ = Z * q := by rw [hq]; ring
    rw [e]
    have hn1 : (n : ℝ) * q ≤ ((n : ℝ) + 1) * q := mul_le_mul_of_nonneg_right (by linarith) hq0
    have hnq : (n : ℝ) * q ≤ 1 / 2 := by linarith only [hn1, hq1]
    calc (n : ℝ) * (Z * q) = Z * ((n : ℝ) * q) := by ring
      _ ≤ Z * (1 / 2) := mul_le_mul_of_nonneg_left hnq hZ0.le
      _ = Z / 2 := by ring
  calc ∑ i : Fin n, ‖∑ b : Zd d L, thetaKer d L g (cycProd μs i) u (a i) b * A (Function.update a i b)‖
      ≤ ∑ _i : Fin n, (W ^ K * W ^ (-D) + W ^ K * (C * W ^ K * W ^ C₀ * Real.exp (-x))) :=
        Finset.sum_le_sum fun i _ => hpar i
    _ = (n : ℝ) * (W ^ K * W ^ (-D)) + (n : ℝ) * (W ^ K * (C * W ^ K * W ^ C₀ * Real.exp (-x))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    _ ≤ Z := by linarith

/-! ## 6. The operator `STthetaOp` -/

/-- **Target 5.** Target 4 for the Step 2/6 operator `STthetaOp` (`n = 2`, `STthetaOp_eq_ThetaN`, `norm_mSigma`):
`L = sz.L n`, `g = sz.lam n`, `W = sz.W n`; every sign pattern `σ`. -/
theorem QopDecay_STthetaOp_fastDecay {d : ℕ} (hd : 3 ≤ d) (Λ K C₀ ε D : ℝ) (hΛ : 0 < Λ) (hε : 0 < ε) :
    ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| ≤ 2 → 0 < sz.lam n → sz.lam n ≤ Λ →
      W₀ ≤ ((sz.W n : ℕ) : ℝ) → ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K →
      ∀ u : ℝ, 0 ≤ u → u < 1 → (1 - u)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ K →
      ∀ (σ : Fin 2 → Bool) (A : (Fin 2 → Zd d (sz.L n)) → ℂ), ‖A‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀ →
        EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) ε D A →
        EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) (2 * ε) (D - (K + 1)) (STthetaOp sz n E u σ A) := by
  obtain ⟨W₀, hW₀, h⟩ := QopDecay_ThetaN_fastDecay d 2 hd Λ K C₀ ε D hΛ hε
  refine ⟨W₀, hW₀, ?_⟩
  intro sz n E hE hlam hlamΛ hW hLW u hu0 hu1 hKu σ A hA hAd
  have key := h (sz.L n) (sz.three_le_L n) (sz.lam n) hlam hlamΛ _ hW hLW u hu0 hu1 hKu
    (fun i => mSigma E (σ i)) (fun i => norm_mSigma hE _) A hA hAd
  intro a ha
  rw [STthetaOp_eq_ThetaN]
  exact key a ha

/-! ## 7. Compiled nonempty instances (`d = 3`, `L = 5`, `g = 1`, `u = t = 1/2`) -/

/-- A nonzero tensor on `Zd 3 L` supported on the diagonal `b₀ = b₁` (copy of `qnA`, `QopNorm.lean:468`). -/
private def qdecA (L : ℕ) : (Fin 2 → Zd 3 L) → ℂ := fun b => if b 0 = b 1 then 1 else 0

private theorem qdecA_ne (L : ℕ) : qdecA L ≠ 0 := by
  intro h
  have := congrFun h (fun _ => 0)
  simp [qdecA] at this

private theorem qdecA_norm_le (L : ℕ) [NeZero L] : ‖qdecA L‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun b => ?_
  unfold qdecA
  split_ifs <;> simp

private theorem qdecA_fastDecay (L : ℕ) (hL : 1 ≤ L) (W ε D : ℝ) (hW : 0 < W) :
    EKFastDecay (d := 3) (L := L) (n := 2) 1 (1 / 2) W ε D (qdecA L) := by
  intro a ⟨i, j, hij⟩
  by_cases h : a 0 = a 1
  · exfalso
    have hz : zdistD 3 L (a i - a j) = 0 := by
      have : a i - a j = 0 := by
        fin_cases i <;> fin_cases j <;> simp [h]
      rw [this]; simp
    have hpos : 0 < W ^ ε * ellT L 1 (1 / 2) :=
      mul_pos (Real.rpow_pos_of_pos hW _)
        (lt_of_lt_of_le zero_lt_one (one_le_ellT (by exact_mod_cast hL)))
    rw [hz] at hij
    simp at hij
    linarith
  · simp [qdecA, h, Real.rpow_nonneg hW.le]

/-- `ℓ_{1/2}(L, g = 1) ≤ 2`. -/
private theorem qdec_ellT_le (L : ℕ) : ellT L 1 (1 / 2) ≤ 2 := by
  unfold ellT
  refine (min_le_left _ _).trans (max_le ?_ (by norm_num))
  have h1 : (1 / 2 : ℝ) ≤ Real.sqrt |1 - 1 / 2| := by
    rw [show |(1 : ℝ) - 1 / 2| = 1 / 2 by norm_num, Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- The window `W^{2ε} ℓ_{1/2}` at `W = L = N ≥ 9`, `ε = 1/4`, `g = 1` contains the pair
`a = ((⌊N/2⌋, ⌊N/2⌋, ⌊N/2⌋), 0)`. -/
private theorem qdec_window (N : ℕ) (hN : 9 ≤ N) :
    ∃ a : Fin 2 → Zd 3 N,
      (N : ℝ) ^ (2 * (1 / 4 : ℝ)) * ellT N 1 (1 / 2) ≤ (zdistD 3 N (a 0 - a 1) : ℝ) := by
  refine ⟨![fun _ => ((N / 2 : ℕ) : ZMod N), 0], ?_⟩
  have hz : zdist N ((N / 2 : ℕ) : ZMod N) = N / 2 := by
    unfold zdist
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    omega
  have hd : zdistD 3 N ((![fun _ => ((N / 2 : ℕ) : ZMod N), 0] : Fin 2 → Zd 3 N) 0 -
      (![fun _ => ((N / 2 : ℕ) : ZMod N), 0] : Fin 2 → Zd 3 N) 1) = 3 * (N / 2) := by
    simp [zdistD, hz]
  rw [hd]
  have h2 : (N : ℝ) ≤ 2 * ((N / 2 : ℕ) : ℝ) + 1 := by
    have : N ≤ 2 * (N / 2) + 1 := by omega
    exact_mod_cast this
  have hN9 : (9 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : (N : ℝ) ^ (2 * (1 / 4 : ℝ)) = Real.sqrt N := by
    rw [Real.sqrt_eq_rpow]; norm_num
  have hs3 : 3 ≤ Real.sqrt N := by
    rw [show (3 : ℝ) = Real.sqrt 9 by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hN9
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (by linarith)
  have hs0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have he := mul_le_mul_of_nonneg_left (qdec_ellT_le N) hs0
  rw [hs]
  push_cast
  nlinarith

/-- Instance of target 1 at `d = 3`, `m = 1`, `L = 5`, `g = 1`, `t = 1/2`, `a = (0, (1,1,1))`. -/
example : ‖deriv (fun τ => QopAlgebra_mollifier 3 5 1 1 τ ![0, fun _ => 1]) (1 / 2 : ℝ)‖ ≤
    (1 + 40 * ((3 * 1 : ℕ) : ℝ)) * 6 ^ (3 * 1) * (1 - (1 / 2 : ℝ))⁻¹ *
      (((ellT 5 1 (1 / 2 : ℝ)) ^ 3)⁻¹) ^ 1 *
      Real.exp (-(1 / 4) * (∑ i ∈ Finset.univ.erase (0 : Fin (1 + 1)),
        (zdistD 3 5 ((![0, fun _ => 1] : Fin 2 → Zd 3 5) i - (![0, fun _ => 1] : Fin 2 → Zd 3 5) 0) : ℝ)) /
          ellT 5 1 (1 / 2 : ℝ)) :=
  QopAlgebra_mollifier_derivDecay 3 5 1 (by norm_num) one_pos (1 / 2) (by norm_num) (by norm_num) _

/-- Instance of target 2 at `d = 3`, `m = 1`, `K = 1`, `C₀ = 0`, `ε' = D' = 1`, `L = 5`, `g = 1`, `t = 1/2`,
`B ≡ 1`: some `W` (any `W ≥ max W₀ 2`) satisfies all deterministic hypotheses; for `L = 5` the window is empty
for large `W` (diameter `6`), the content is in the proof. -/
example : ∃ W : ℝ, 2 ≤ W ∧
    EKFastDecay (d := 3) (L := 5) (n := 2) 1 (1 / 2) W 1 1
      (fun a : Fin (1 + 1) → Zd 3 5 => (fun _ : Zd 3 5 => (1 : ℂ)) (a 0) *
        deriv (fun τ => QopAlgebra_mollifier 3 5 1 1 τ a) (1 / 2 : ℝ)) := by
  obtain ⟨W₀, hW₀, h⟩ := QopDecay_deriv_fastDecay 3 1 1 0 1 1 one_pos
  have hW2 : (2 : ℝ) ≤ max W₀ 2 := le_max_right _ _
  refine ⟨max W₀ 2, hW2, ?_⟩
  refine h 5 (by norm_num) 1 one_pos (max W₀ 2) (le_max_left _ _) (1 / 2) (by norm_num) (by norm_num)
    ?_ (fun _ => 1) ?_
  · rw [Real.rpow_one]; norm_num
  · rw [Real.rpow_zero]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => by simp

/-- Instance of target 3 at `d = 3`, `Λ = 1`, `L = 5`, `g = 1`, `u = 1/2`, `μ = i`, `x = 0`, `y = (2,2,2)`. -/
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ‖thetaKer 3 5 1 Complex.I (1 / 2 : ℝ) 0 (fun _ => 2)‖ ≤
      C * (1 - (1 / 2 : ℝ))⁻¹ * Real.exp (-c * (zdistD 3 5 ((fun _ => 2 : Zd 3 5) - 0) : ℝ) / ellT 5 1 (1 / 2 : ℝ)) := by
  obtain ⟨C, c, hC, hc, h⟩ := QopDecay_thetaKer_decay 3 le_rfl 1 one_pos
  exact ⟨C, c, hC, hc, h 5 (by norm_num) 1 one_pos le_rfl (1 / 2) (by norm_num) (by norm_num) Complex.I
    (by simp) 0 _⟩

/-- Instance of target 4 at `d = 3`, `n = 2`, `Λ = 1`, `K = 4`, `C₀ = 0`, `ε = 1/4`, `D = 1`, `g = 1`, `u = 1/2`,
`μs = (1, i)`, `W = L = N := ⌈W₀⌉₊ + 9` (`L` is chosen after `W₀`), the nonzero tensor `qdecA N`:
`L^3 ≤ W^4`, `(1 - u)⁻¹ = 2 ≤ W^4`, `‖qdecA N‖ ≤ W^0`, `EKFastDecay` of `qdecA N`. The conclusion window
`W^{2ε} ℓ_u` (hence the hypothesis window `W^ε ℓ_u ≤ W^{2ε} ℓ_u`) contains a pair `a`. -/
example : ∃ (N : ℕ) (_ : NeZero N), 9 ≤ N ∧
    (∃ a : Fin 2 → Zd 3 N,
      (N : ℝ) ^ (2 * (1 / 4 : ℝ)) * ellT N 1 (1 / 2) ≤ (zdistD 3 N (a 0 - a 1) : ℝ)) ∧
    EKFastDecay (d := 3) (L := N) (n := 2) 1 (1 / 2) (N : ℝ) (2 * (1 / 4)) (1 - (4 + 1))
      (ThetaN 3 N 1 ![1, Complex.I] (1 / 2 : ℝ) (qdecA N)) := by
  obtain ⟨W₀, hW₀, h⟩ := QopDecay_ThetaN_fastDecay 3 2 le_rfl 1 4 0 (1 / 4) 1 one_pos (by norm_num)
  obtain ⟨N, hN9, hNW⟩ : ∃ N : ℕ, 9 ≤ N ∧ W₀ ≤ (N : ℝ) := by
    refine ⟨⌈W₀⌉₊ + 9, by omega, ?_⟩
    have := Nat.le_ceil W₀
    push_cast; linarith
  have : NeZero N := ⟨by omega⟩
  have hN9' : (9 : ℝ) ≤ N := by exact_mod_cast hN9
  have hr4 : (N : ℝ) ^ (4 : ℝ) = (N : ℝ) ^ 4 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hN34 : (N : ℝ) ^ 3 ≤ (N : ℝ) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hN14 : (N : ℝ) ^ 1 ≤ (N : ℝ) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  refine ⟨N, inferInstance, hN9, qdec_window N hN9, ?_⟩
  refine h N (by omega) 1 one_pos le_rfl (N : ℝ) hNW ?_ (1 / 2) (by norm_num) (by norm_num) ?_
    ![1, Complex.I] ?_ (qdecA N) ?_ (qdecA_fastDecay N (by omega) _ _ _ (by linarith))
  · rw [hr4]; exact hN34
  · have e : ((1 : ℝ) - 1 / 2)⁻¹ = 2 := by norm_num
    rw [e, hr4]; rw [pow_one] at hN14; linarith
  · intro i; fin_cases i <;> simp
  · rw [Real.rpow_zero]; exact qdecA_norm_le N

/-- Size data for the instance of target 5: `L ≡ N`, `W ≡ N`, `λ ≡ 1`. -/
private def qdecSz (N : ℕ) (hN : 9 ≤ N) : Sizes 3 where
  L := fun _ => N
  W := fun _ => N
  lam := fun _ => 1
  three_le_L := fun _ => by omega
  W_pos := fun _ => by omega

/-- Instance of target 5 at `d = 3`, `Λ = 1`, `K = 4`, `C₀ = 0`, `ε = 1/4`, `D = 1`, size index `n = 0`, `E = 0`,
`u = 1/2`, the size data `qdecSz N` (`L = W = N := ⌈W₀⌉₊ + 9`, `λ = 1`), `σ = (+, -)`, the tensor `qdecA N`.
The conclusion window `W^{2ε} ℓ_u` (hence the hypothesis window) contains a pair `a`. -/
example : ∃ (N : ℕ) (hN : 9 ≤ N),
    (∃ a : Fin 2 → Zd 3 ((qdecSz N hN).L 0),
      (((qdecSz N hN).W 0 : ℕ) : ℝ) ^ (2 * (1 / 4 : ℝ)) *
          ellT ((qdecSz N hN).L 0) ((qdecSz N hN).lam 0) (1 / 2) ≤
        (zdistD 3 ((qdecSz N hN).L 0) (a 0 - a 1) : ℝ)) ∧
    EKFastDecay (d := 3) (L := (qdecSz N hN).L 0) (n := 2) ((qdecSz N hN).lam 0) (1 / 2)
      (((qdecSz N hN).W 0 : ℕ) : ℝ) (2 * (1 / 4)) (1 - (4 + 1))
      (STthetaOp (qdecSz N hN) 0 0 (1 / 2) ![true, false] (qdecA N)) := by
  obtain ⟨W₀, hW₀, h⟩ := QopDecay_STthetaOp_fastDecay (d := 3) le_rfl 1 4 0 (1 / 4) 1 one_pos (by norm_num)
  obtain ⟨N, hN9, hNW⟩ : ∃ N : ℕ, 9 ≤ N ∧ W₀ ≤ (N : ℝ) := by
    refine ⟨⌈W₀⌉₊ + 9, by omega, ?_⟩
    have := Nat.le_ceil W₀
    push_cast; linarith
  have hN9' : (9 : ℝ) ≤ N := by exact_mod_cast hN9
  have hr4 : (N : ℝ) ^ (4 : ℝ) = (N : ℝ) ^ 4 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hN34 : (N : ℝ) ^ 3 ≤ (N : ℝ) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hN14 : (N : ℝ) ^ 1 ≤ (N : ℝ) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  refine ⟨N, hN9, qdec_window N hN9, ?_⟩
  refine h (qdecSz N hN9) 0 0 (by norm_num) (by norm_num [qdecSz]) (by norm_num [qdecSz]) hNW ?_ (1 / 2)
    (by norm_num) (by norm_num) ?_ ![true, false] (qdecA N) ?_
    (qdecA_fastDecay N (by omega) _ _ _ (by change (0 : ℝ) < N; linarith))
  · change (N : ℝ) ^ 3 ≤ (N : ℝ) ^ (4 : ℝ)
    rw [hr4]; exact hN34
  · change ((1 : ℝ) - 1 / 2)⁻¹ ≤ (N : ℝ) ^ (4 : ℝ)
    have e : ((1 : ℝ) - 1 / 2)⁻¹ = 2 := by norm_num
    rw [e, hr4]; rw [pow_one] at hN14; linarith
  · have : NeZero N := ⟨by omega⟩
    change ‖qdecA N‖ ≤ (N : ℝ) ^ (0 : ℝ)
    rw [Real.rpow_zero]; exact qdecA_norm_le N

end RBM.Gauss.Sizes

end
