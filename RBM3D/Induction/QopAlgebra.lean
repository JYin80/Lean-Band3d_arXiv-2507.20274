/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step34Pins
import RBM3D.Kernel.Evolution

/-!
# S3-04 (ticket T2055): the mollifier `ϑ` and the algebra of `𝒫`, `ϑ_t`, `𝒬_t`

Paper: `paper/tex/3_5_Loop_Hierarchy.tex:1204-1250` (`Def:QtPt`, `(eq:sumzero_op)`,
`(eq:suma1chi)`, `(eq:derv_Theta)`, `rmk:choosechi`).

**The mollifier** (`rmk:choosechi`, `3_5:1250`), at a smoothed scale (paper-delta candidate
`T2041b`): with `y_t = 1 + g (1 - t)^{-1/2}` and `u_t = 1/ℓ̃_t = y_t⁻¹ + L⁻¹`,
`ϑ_{t,a} = exp(-u_t Σ_{i ≥ 2} |a_i - a₁|) / z(u_t)^{d m}`, `z(u) = Σ_{y ∈ ℤ_L} exp(-u |y|)`.
The scale `ℓ̃_t = 1/u_t` is smooth in `t < 1`, `ℓ_t / 2 ≤ ℓ̃_t ≤ 2 ℓ_t` and
`|∂_t u_t| ≤ u_t / (2 (1 - t))`.  `z(u)^d` is the total mass `Σ_{x ∈ ℤ_L^d} exp(-u |x|)` (the `ℓ¹`
norm splits over the coordinates), so `Σ_{a₂..a_n} ϑ = 1`.  The RBM2D choice
`(1-t)^m Π Θ_t(a₁, a_i)` is not admissible at `d ≥ 3` (docstring of `STMollifierProps`).

**The algebra of the operators** (RBM2D `Induction/SumZeroQ.lean`, ported with `Z2 L ↦ Zd d L`,
`Fin k ↦ Fin (m+1)`, `Psum ↦ STPsum`, `Qop ↦ STQop`, `thetaSig ↦ ThetaN`): `𝒫 𝒬_t = 0`,
`𝒬_t = id` on sum-zero tensors, `Θ^{(m+1)}` and `U^{(m+1)}` preserve sum-zero, the commutator
formulas, `𝒫 ∂_tϑ = 0` and `∂_t(𝒬_t 𝒜_t) = 𝒬_t(∂_t 𝒜_t) - (𝒫 𝒜_t)_{a₁} ∂_tϑ_t`.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Gauss.Sizes

open RBM

/-! ## 1. One-dimensional sums over `ℤ_L` -/

/-- `Σ_{y ∈ ℤ_L} F(y.val) = Σ_{k < L} F k`. -/
private theorem qa_sum_zmod_val {L : ℕ} [NeZero L] (F : ℕ → ℝ) :
    ∑ y : ZMod L, F y.val = ∑ k ∈ Finset.range L, F k :=
  Finset.sum_bij (fun y _ => y.val) (fun y _ => Finset.mem_range.2 (ZMod.val_lt y))
    (fun _ _ _ _ h => ZMod.val_injective L h)
    (fun k hk => ⟨(k : ZMod L), Finset.mem_univ _, ZMod.val_natCast_of_lt (Finset.mem_range.1 hk)⟩)
    (fun _ _ => rfl)

/-- `z(u) = Σ_{y ∈ ℤ_L} exp(-u |y|)`. -/
private def qaZ1 (L : ℕ) [NeZero L] (u : ℝ) : ℝ :=
  ∑ y : ZMod L, Real.exp (-u * (zdist L y : ℝ))

/-- `z₂(u) = Σ_{y ∈ ℤ_L} |y| exp(-u |y|)` (minus the `u`-derivative of `z`). -/
private def qaZ2 (L : ℕ) [NeZero L] (u : ℝ) : ℝ :=
  ∑ y : ZMod L, (zdist L y : ℝ) * Real.exp (-u * (zdist L y : ℝ))

private theorem qaZ1_pos {L : ℕ} [NeZero L] (u : ℝ) : 0 < qaZ1 L u :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

private theorem qaZ1_eq_range {L : ℕ} [NeZero L] (u : ℝ) :
    qaZ1 L u = ∑ k ∈ Finset.range L, Real.exp (-u * ((min k (L - k) : ℕ) : ℝ)) :=
  qa_sum_zmod_val (fun k => Real.exp (-u * ((min k (L - k) : ℕ) : ℝ)))

private theorem qaZ2_eq_range {L : ℕ} [NeZero L] (u : ℝ) :
    qaZ2 L u = ∑ k ∈ Finset.range L,
      ((min k (L - k) : ℕ) : ℝ) * Real.exp (-u * ((min k (L - k) : ℕ) : ℝ)) :=
  qa_sum_zmod_val (fun k => ((min k (L - k) : ℕ) : ℝ) * Real.exp (-u * ((min k (L - k) : ℕ) : ℝ)))

/-- Lower bound for the one-dimensional mass: `z(u) ≥ (e u)⁻¹` when `L⁻¹ < u`. -/
private theorem qaZ1_ge {L : ℕ} [NeZero L] {u : ℝ} (hu : 0 < u) (huL : (L : ℝ)⁻¹ < u) :
    (Real.exp 1)⁻¹ * u⁻¹ ≤ qaZ1 L u := by
  set k := ⌊u⁻¹⌋₊ with hk
  have hk1 : (k : ℝ) ≤ u⁻¹ := Nat.floor_le (by positivity)
  have hk2 : u⁻¹ < k + 1 := Nat.lt_floor_add_one _
  have hL0 : (0 : ℝ) < L := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))
  have hkL : k + 1 ≤ L := by
    have h1 : (k : ℝ) < L := lt_of_le_of_lt hk1 ((inv_lt_comm₀ hu hL0).2 huL)
    exact_mod_cast h1
  rw [qaZ1_eq_range]
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

private theorem qa_hasSum_f {u : ℝ} (hu : 0 < u) :
    HasSum (fun j : ℕ => (j : ℝ) * Real.exp (-u * j))
      (Real.exp (-u) / (1 - Real.exp (-u)) ^ 2) := by
  have hr : ‖Real.exp (-u)‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact Real.exp_lt_one_iff.2 (by linarith)
  have h := hasSum_coe_mul_geometric_of_norm_lt_one hr
  convert h using 2 with j
  rw [← Real.exp_nat_mul]; ring_nf

/-- Upper bound for the first moment of the one-dimensional mass:
`z₂(u) ≤ 2 e^{-u} / (1 - e^{-u})²`. -/
private theorem qaZ2_le {L : ℕ} [NeZero L] {u : ℝ} (hu : 0 < u) :
    qaZ2 L u ≤ 2 * (Real.exp (-u) / (1 - Real.exp (-u)) ^ 2) := by
  set f : ℕ → ℝ := fun j => (j : ℝ) * Real.exp (-u * j) with hf
  have hf0 : ∀ j, 0 ≤ f j := fun j => by simp only [hf]; positivity
  have hT : ∀ n, ∑ k ∈ Finset.range n, f k ≤ Real.exp (-u) / (1 - Real.exp (-u)) ^ 2 :=
    fun n => sum_le_hasSum _ (fun j _ => hf0 j) (qa_hasSum_f hu)
  rw [qaZ2_eq_range]
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
private def qaY (g t : ℝ) : ℝ := 1 + g / Real.sqrt (1 - t)

/-- `u_t = 1 / ℓ̃_t = y_t⁻¹ + L⁻¹`. -/
private def qaU (L : ℕ) (g t : ℝ) : ℝ := (qaY g t)⁻¹ + (L : ℝ)⁻¹

private theorem qaY_gt {g t : ℝ} (hg : 0 < g) (ht : t < 1) : 1 < qaY g t := by
  have h : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 (by linarith)
  unfold qaY; have := div_pos hg h; linarith

private theorem qaU_pos {L : ℕ} [NeZero L] {g t : ℝ} (hg : 0 < g) (ht : t < 1) : 0 < qaU L g t := by
  have h1 : 0 < qaY g t := lt_trans zero_lt_one (qaY_gt hg ht)
  have h2 : (0 : ℝ) < L := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))
  unfold qaU; positivity

private theorem qaU_gt {L : ℕ} [NeZero L] {g t : ℝ} (hg : 0 < g) (ht : t < 1) :
    (L : ℝ)⁻¹ < qaU L g t := by
  have h1 : 0 < qaY g t := lt_trans zero_lt_one (qaY_gt hg ht)
  unfold qaU; have := inv_pos.2 h1; linarith

/-- `u_t ≤ 4/3` (as `y_t > 1` and `L ≥ 3`). -/
private theorem qaU_le {L : ℕ} (hL : 3 ≤ L) {g t : ℝ} (hg : 0 < g) (ht : t < 1) :
    qaU L g t ≤ 4 / 3 := by
  have h1 : (qaY g t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (qaY_gt hg ht).le
  have h3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have h2 : (L : ℝ)⁻¹ ≤ 1 / 3 := by
    rw [one_div]; exact inv_anti₀ (by norm_num) h3
  unfold qaU; linarith

private theorem qa_ellT_eq {L : ℕ} {g t : ℝ} (ht : t < 1) :
    ellT L g t = min (max (g / Real.sqrt (1 - t)) 1) L := by
  unfold ellT; rw [abs_of_pos (by linarith : 0 < 1 - t)]

/-- `u_t ≥ 1 / (2 ℓ_t)`. -/
private theorem qaU_lb {L : ℕ} [NeZero L] {g t : ℝ} (hg : 0 < g) (ht : t < 1) :
    (2 * ellT L g t)⁻¹ ≤ qaU L g t := by
  have hy : 0 < qaY g t := lt_trans zero_lt_one (qaY_gt hg ht)
  have hL0 : (0 : ℝ) < L := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))
  have hx : 0 < g / Real.sqrt (1 - t) := div_pos hg (Real.sqrt_pos.2 (by linarith))
  have hell1 : 1 ≤ ellT L g t := one_le_ellT (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  rw [qa_ellT_eq ht] at hell1 ⊢
  unfold qaU
  rcases min_choice (max (g / Real.sqrt (1 - t)) 1) (L : ℝ) with h | h
  · rw [h]
    have h2 : (2 * max (g / Real.sqrt (1 - t)) 1)⁻¹ ≤ (qaY g t)⁻¹ := by
      refine inv_anti₀ hy ?_
      unfold qaY
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
private theorem qaU_ub {L : ℕ} [NeZero L] {g t : ℝ} (hg : 0 < g) (ht : t < 1) :
    ellT L g t * qaU L g t ≤ 2 := by
  have hy : 0 < qaY g t := lt_trans zero_lt_one (qaY_gt hg ht)
  have hL0 : (0 : ℝ) < L := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))
  have hx : 0 < g / Real.sqrt (1 - t) := div_pos hg (Real.sqrt_pos.2 (by linarith))
  have hell1 : ellT L g t ≤ qaY g t := by
    rw [qa_ellT_eq ht]; unfold qaY
    refine (min_le_left _ _).trans (max_le (by linarith) (by linarith))
  have hell2 : ellT L g t ≤ L := ellT_le_L
  have e1 : ellT L g t * (qaY g t)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hy]; exact hell1
  have e2 : ellT L g t * (L : ℝ)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hL0]; exact hell2
  unfold qaU; rw [mul_add]; linarith

/-- The derivative of `u_t`, `|∂_t u_t| ≤ u_t / (2 (1 - t))`. -/
private theorem qaU_deriv {L : ℕ} [NeZero L] {g t : ℝ} (hg : 0 < g) (ht : t < 1) :
    ∃ u' : ℝ, HasDerivAt (qaU L g) u' t ∧ |u'| ≤ qaU L g t / (2 * (1 - t)) := by
  have h1t : 0 < 1 - t := by linarith
  have hr : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 h1t
  have hy : 0 < qaY g t := lt_trans zero_lt_one (qaY_gt hg ht)
  have h1 : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub 1
  have h2 : HasDerivAt (fun s : ℝ => Real.sqrt (1 - s)) (-1 / (2 * Real.sqrt (1 - t))) t :=
    h1.sqrt h1t.ne'
  have h3 := (hasDerivAt_const t g).div h2 hr.ne'
  have h4 : HasDerivAt (qaY g) ((0 * Real.sqrt (1 - t) - g * (-1 / (2 * Real.sqrt (1 - t)))) / Real.sqrt (1 - t) ^ 2) t :=
    h3.const_add 1
  have h5 := (h4.inv hy.ne').add_const ((L : ℝ)⁻¹)
  refine ⟨_, h5, ?_⟩
  set r := Real.sqrt (1 - t) with hrdef
  have hr2 : r ^ 2 = 1 - t := Real.sq_sqrt h1t.le
  set q := g / r with hq
  have hq0 : 0 < q := div_pos hg hr
  have hy' : qaY g t = 1 + q := rfl
  have hder : (0 * r - g * (-1 / (2 * r))) / r ^ 2 = q / (2 * r ^ 2) := by
    rw [hq]; field_simp; ring
  rw [hder]
  have hq_le : q ≤ qaY g t := by rw [hy']; linarith
  have habs : |-(q / (2 * r ^ 2)) / qaY g t ^ 2| = (q / (2 * r ^ 2)) / qaY g t ^ 2 := by
    rw [abs_div, abs_neg, abs_of_pos (by positivity), abs_of_pos (by positivity)]
  rw [habs, ← hr2]
  have hu : (qaY g t)⁻¹ ≤ qaU L g t := by
    unfold qaU; have := inv_nonneg.2 (Nat.cast_nonneg (α := ℝ) L); linarith
  calc (q / (2 * r ^ 2)) / qaY g t ^ 2 = (q / qaY g t ^ 2) / (2 * r ^ 2) := by ring
    _ ≤ (qaY g t)⁻¹ / (2 * r ^ 2) := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        rw [div_le_iff₀ (by positivity)]
        calc q ≤ qaY g t := hq_le
          _ = (qaY g t)⁻¹ * qaY g t ^ 2 := by field_simp
    _ ≤ qaU L g t / (2 * r ^ 2) := div_le_div_of_nonneg_right hu (by positivity)


/-- The derivative bound for the one-dimensional masses: `u z₂(u) ≤ 40 z(u)` for `L⁻¹ < u ≤ 4/3`. -/
private theorem qa_u_Z2_le {L : ℕ} [NeZero L] {u : ℝ} (hu : 0 < u) (huL : (L : ℝ)⁻¹ < u)
    (hu4 : u ≤ 4 / 3) : u * qaZ2 L u ≤ 40 * qaZ1 L u := by
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
  have hz2 : qaZ2 L u ≤ 2 * ((1 + u) ^ 2 / u ^ 2) := (qaZ2_le hu).trans (by linarith)
  have hz1 := qaZ1_ge hu huL
  have he : Real.exp 1 < 2.72 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  -- `u z₂ ≤ 2 (1+u)²/u ≤ 40/(e u) ≤ 40 z`
  have h4 : u * qaZ2 L u ≤ 2 * (1 + u) ^ 2 / u := by
    calc u * qaZ2 L u ≤ u * (2 * ((1 + u) ^ 2 / u ^ 2)) := mul_le_mul_of_nonneg_left hz2 hu.le
      _ = 2 * (1 + u) ^ 2 / u := by field_simp
  have h5 : 2 * (1 + u) ^ 2 / u ≤ 40 * ((Real.exp 1)⁻¹ * u⁻¹) := by
    rw [show 40 * ((Real.exp 1)⁻¹ * u⁻¹) = 40 / (Real.exp 1 * u) by field_simp]
    rw [div_le_div_iff₀ hu (by positivity)]
    have h7 : (1 + u) ^ 2 ≤ 49 / 9 := by nlinarith
    have h6 : 2 * (1 + u) ^ 2 * Real.exp 1 ≤ 40 := by nlinarith [sq_nonneg (1 + u)]
    nlinarith [mul_le_mul_of_nonneg_right h6 hu.le]
  calc u * qaZ2 L u ≤ 40 * ((Real.exp 1)⁻¹ * u⁻¹) := h4.trans h5
    _ ≤ 40 * qaZ1 L u := mul_le_mul_of_nonneg_left hz1 (by norm_num)

/-! ## 3. The mass `Σ_x exp(-u |x|) = z(u)^d` and the sum-one identity -/

/-- The `ℓ¹` norm splits over the coordinates: `Σ_{x ∈ ℤ_L^d} exp(-u |x|) = z(u)^d`. -/
private theorem qaZ1_pow (d L : ℕ) [NeZero L] (u : ℝ) :
    ∑ x : Zd d L, Real.exp (-u * (zdistD d L x : ℝ)) = (qaZ1 L u) ^ d := by
  calc ∑ x : Zd d L, Real.exp (-u * (zdistD d L x : ℝ))
      = ∑ x : Zd d L, ∏ j : Fin d, Real.exp (-u * (zdist L (x j) : ℝ)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Real.exp_sum, zdistD, Nat.cast_sum, Finset.mul_sum]
    _ = ∏ j : Fin d, ∑ y : ZMod L, Real.exp (-u * (zdist L y : ℝ)) :=
        (Fintype.prod_sum (fun (_ : Fin d) (y : ZMod L) => Real.exp (-u * (zdist L y : ℝ)))).symm
    _ = (qaZ1 L u) ^ d := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]; rfl

/-- **The factorisation** `Σ_{a : a₀ = a₁} Π_{i ≠ 0} g_i(a_i) = Π_{i ≠ 0} Σ_b g_i(b)`
(RBM2D `SumZeroQ.lean:53` `SumZeroQ_sum_filter_prod`, `c9a24cf`, with `Z2 L ↦ Zd d L`, `Fin k ↦ Fin (m+1)`). -/
private theorem qa_sum_filter_prod {d L m : ℕ} [NeZero L] {R : Type*} [CommSemiring R] (a₁ : Zd d L)
    (g : Fin (m + 1) → Zd d L → R) :
    ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁),
        ∏ i ∈ Finset.univ.erase (0 : Fin (m + 1)), g i (a i)
      = ∏ i ∈ Finset.univ.erase (0 : Fin (m + 1)), ∑ b : Zd d L, g i b := by
  classical
  set g' : Fin (m + 1) → Zd d L → R := fun i b => if i = 0 then (if b = a₁ then 1 else 0) else g i b
    with hg'
  have h1 : ∏ i, ∑ b, g' i b = ∑ a : Fin (m + 1) → Zd d L, ∏ i, g' i (a i) := Fintype.prod_sum g'
  have h2 : ∏ i, ∑ b, g' i b = ∏ i ∈ Finset.univ.erase (0 : Fin (m + 1)), ∑ b : Zd d L, g i b := by
    rw [← Finset.mul_prod_erase Finset.univ (fun i => ∑ b, g' i b) (Finset.mem_univ (0 : Fin (m + 1)))]
    have h0 : ∑ b, g' 0 b = 1 := by simp [hg']
    rw [h0, one_mul]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi0 : i ≠ 0 := Finset.ne_of_mem_erase hi
    simp [hg', hi0]
  have h3 : ∑ a : Fin (m + 1) → Zd d L, ∏ i, g' i (a i)
      = ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁),
          ∏ i ∈ Finset.univ.erase (0 : Fin (m + 1)), g i (a i) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.mul_prod_erase Finset.univ (fun i => g' i (a i)) (Finset.mem_univ (0 : Fin (m + 1)))]
    have h4 : ∏ i ∈ Finset.univ.erase (0 : Fin (m + 1)), g' i (a i)
        = ∏ i ∈ Finset.univ.erase (0 : Fin (m + 1)), g i (a i) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hi0 : i ≠ 0 := Finset.ne_of_mem_erase hi
      simp [hg', hi0]
    rw [h4]
    by_cases ha : a 0 = a₁ <;> simp [hg', ha]
  rw [← h2, h1, h3]

/-- `S(a) = Σ_{i ≥ 2} |a_i - a₁|`. -/
private def qaS {d L m : ℕ} [NeZero L] (a : Fin (m + 1) → Zd d L) : ℝ :=
  ∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)), (zdistD d L (a i - a 0) : ℝ)

private theorem qaS_nonneg {d L m : ℕ} [NeZero L] (a : Fin (m + 1) → Zd d L) : 0 ≤ qaS a :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- `Φ_a(u) = exp(-u S(a)) / z(u)^{d m}`. -/
private def qaPhi (d L m : ℕ) [NeZero L] (a : Fin (m + 1) → Zd d L) (u : ℝ) : ℝ :=
  Real.exp (-u * qaS a) / (qaZ1 L u) ^ (d * m)

/-- **The mollifier** `ϑ_{t,a} = exp(-u_t Σ_{i ≥ 2} |a_i - a₁|) / z(u_t)^{d m}` of `rmk:choosechi`
(`3_5:1250`) at the smoothed scale `ℓ̃_t = 1/u_t = (y_t⁻¹ + L⁻¹)⁻¹`, `y_t = 1 + g (1 - t)^{-1/2}` (`T2041b`);
tensors of `m + 1` indices. -/
def QopAlgebra_mollifier (d L m : ℕ) [NeZero L] (g : ℝ) (t : ℝ) (a : Fin (m + 1) → Zd d L) : ℂ :=
  ((qaPhi d L m a (qaU L g t) : ℝ) : ℂ)

/-- `(eq:suma1chi)`: `Σ_{a₂..a_n} ϑ_{t,a} = 1`, for every real `t`. -/
theorem QopAlgebra_mollifier_sum (d L m : ℕ) [NeZero L] (g t : ℝ) (a₁ : Zd d L) :
    ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁),
      QopAlgebra_mollifier d L m g t a = 1 := by
  set u := qaU L g t with hu
  have hz : qaZ1 L u ≠ 0 := (qaZ1_pos u).ne'
  unfold QopAlgebra_mollifier
  rw [← Complex.ofReal_sum, Complex.ofReal_eq_one]
  unfold qaPhi
  rw [← Finset.sum_div]
  have h1 : ∀ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁),
      Real.exp (-u * qaS a)
        = ∏ i ∈ Finset.univ.erase (0 : Fin (m + 1)), Real.exp (-u * (zdistD d L (a i - a₁) : ℝ)) := by
    intro a ha
    have ha0 : a 0 = a₁ := (Finset.mem_filter.1 ha).2
    rw [← Real.exp_sum, qaS, Finset.mul_sum]
    simp only [ha0]
  rw [Finset.sum_congr rfl h1,
    qa_sum_filter_prod (d := d) (L := L) (m := m) a₁
      (fun _ b => Real.exp (-u * (zdistD d L (b - a₁) : ℝ)))]
  have h2 : ∑ b : Zd d L, Real.exp (-u * (zdistD d L (b - a₁) : ℝ)) = (qaZ1 L u) ^ d := by
    rw [← qaZ1_pow]
    exact Fintype.sum_equiv (Equiv.subRight a₁) _ _ (fun b => rfl)
  simp only [h2, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, Nat.add_sub_cancel]
  rw [← pow_mul, div_self (pow_ne_zero _ hz)]

/-! ## 4. The four properties of `STMollifierProps` -/

private theorem qaZ1_hasDerivAt (L : ℕ) [NeZero L] (u : ℝ) : HasDerivAt (qaZ1 L) (-qaZ2 L u) u := by
  have h : ∀ y ∈ (Finset.univ : Finset (ZMod L)),
      HasDerivAt (fun v : ℝ => Real.exp (-v * (zdist L y : ℝ)))
        (-((zdist L y : ℝ) * Real.exp (-u * (zdist L y : ℝ)))) u := by
    intro y _
    have h1 : HasDerivAt (fun v : ℝ => -v * (zdist L y : ℝ)) (-(zdist L y : ℝ)) u := by
      simpa using ((hasDerivAt_id u).neg.mul_const (zdist L y : ℝ))
    have h2 := h1.exp
    convert h2 using 1; ring
  have h3 := HasDerivAt.fun_sum h
  unfold qaZ1 qaZ2
  rw [Finset.sum_neg_distrib] at h3
  exact h3

private theorem qaPhi_hasDerivAt (L : ℕ) [NeZero L] (S : ℝ) (n : ℕ) (u : ℝ) :
    HasDerivAt (fun v : ℝ => Real.exp (-v * S) / (qaZ1 L v) ^ n)
      (Real.exp (-u * S) / (qaZ1 L u) ^ n * (-S + n * qaZ2 L u / qaZ1 L u)) u := by
  have hz : 0 < qaZ1 L u := qaZ1_pos u
  have h1 : HasDerivAt (fun v : ℝ => Real.exp (-v * S)) (Real.exp (-u * S) * (-S)) u := by
    have h0 : HasDerivAt (fun v : ℝ => -v * S) (-S) u := by
      simpa using ((hasDerivAt_id u).neg.mul_const S)
    exact h0.exp
  have h2 : HasDerivAt (fun v : ℝ => (qaZ1 L v) ^ n)
      ((n : ℝ) * (qaZ1 L u) ^ (n - 1) * (-qaZ2 L u)) u := (qaZ1_hasDerivAt L u).pow n
  have h3 := h1.div h2 (pow_pos hz n).ne'
  convert h3 using 1
  rcases n with _ | n
  · simp
  · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    field_simp
    ring

/-- `|(-S + n z₂/z) Φ| u ≤ (1 + 40 n) / z^n` given `u z₂ ≤ 40 z`. -/
private theorem qa_core {u S z z₂ : ℝ} (n : ℕ) (hu : 0 < u) (hS : 0 ≤ S) (hz : 0 < z) (hz₂ : 0 ≤ z₂)
    (h : u * z₂ ≤ 40 * z) :
    |Real.exp (-u * S) / z ^ n * (-S + n * z₂ / z)| * u ≤ (1 + 40 * (n : ℝ)) / z ^ n := by
  have he0 : 0 < Real.exp (-u * S) := Real.exp_pos _
  have he : Real.exp (-u * S) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hx : u * S * Real.exp (-u * S) ≤ 1 := by
    have h1 : u * S ≤ Real.exp (u * S) := by linarith [Real.add_one_le_exp (u * S)]
    calc u * S * Real.exp (-u * S) ≤ Real.exp (u * S) * Real.exp (-u * S) :=
          mul_le_mul_of_nonneg_right h1 he0.le
      _ = 1 := by rw [← Real.exp_add]; simp
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
    _ ≤ (1 + 40 * (n : ℝ)) / z ^ n := by
        refine div_le_div_of_nonneg_right ?_ hzn.le
        have h1 : (n : ℝ) * (u * z₂ / z) * Real.exp (-u * S) ≤ (n : ℝ) * 40 := by
          calc (n : ℝ) * (u * z₂ / z) * Real.exp (-u * S) ≤ (n : ℝ) * (u * z₂ / z) * 1 :=
                mul_le_mul_of_nonneg_left he (mul_nonneg n.cast_nonneg (by positivity))
            _ ≤ (n : ℝ) * 40 := by rw [mul_one]; exact mul_le_mul_of_nonneg_left huz n.cast_nonneg
        linarith

/-- `z(u_t)⁻¹ ≤ 6 / ℓ_t`. -/
private theorem qa_Zinv_le {L : ℕ} [NeZero L] {g t : ℝ} (hg : 0 < g) (ht : t < 1) :
    (qaZ1 L (qaU L g t))⁻¹ ≤ 6 * (ellT L g t)⁻¹ := by
  have hu := qaU_pos (L := L) hg ht
  have hz := qaZ1_ge hu (qaU_gt (L := L) hg ht)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hl : 0 < ellT L g t := ellT_pos hL1
  have hub := qaU_ub (L := L) hg ht
  have he : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9.trans (by norm_num)).le
  have he0 := Real.exp_pos 1
  -- `ℓ/2 ≤ u⁻¹`
  have h1 : ellT L g t / 2 ≤ (qaU L g t)⁻¹ := by
    rw [← one_div, le_div_iff₀ hu]; linarith
  have h2 : ((Real.exp 1)⁻¹ * (ellT L g t / 2)) ≤ qaZ1 L (qaU L g t) :=
    le_trans (mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 he0.le)) hz
  have h3 : 0 < (Real.exp 1)⁻¹ * (ellT L g t / 2) := by positivity
  calc (qaZ1 L (qaU L g t))⁻¹ ≤ ((Real.exp 1)⁻¹ * (ellT L g t / 2))⁻¹ := inv_anti₀ h3 h2
    _ = 2 * Real.exp 1 * (ellT L g t)⁻¹ := by field_simp
    _ ≤ 6 * (ellT L g t)⁻¹ := by
        refine mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 hl.le)

/-- The derivative of `t ↦ Φ_a(u_t)` and its bound (`(eq:derv_Theta)`), for `0 ≤ t < 1`, `L ≥ 3`. -/
private theorem qa_deriv_real (d L m : ℕ) [NeZero L] {g t : ℝ} (hg : 0 < g) (ht : t < 1)
    (hL : 3 ≤ L) (a : Fin (m + 1) → Zd d L) :
    ∃ x : ℝ, HasDerivAt (fun τ => qaPhi d L m a (qaU L g τ)) x t ∧
      |x| ≤ (1 + 40 * ((d * m : ℕ) : ℝ)) * 6 ^ (d * m) * (1 - t)⁻¹ * ((ellT L g t)⁻¹) ^ (d * m) := by
  obtain ⟨u', hu', hu'b⟩ := qaU_deriv (L := L) hg ht
  have hu := qaU_pos (L := L) hg ht
  have huL := qaU_gt (L := L) hg ht
  have hu4 := qaU_le hL hg ht
  set u := qaU L g t with hudef
  have hΦ : HasDerivAt (qaPhi d L m a)
      (Real.exp (-u * qaS a) / (qaZ1 L u) ^ (d * m) *
        (-qaS a + ((d * m : ℕ) : ℝ) * qaZ2 L u / qaZ1 L u)) u := qaPhi_hasDerivAt L (qaS a) (d * m) u
  have hc := hΦ.comp t hu'
  refine ⟨_, hc, ?_⟩
  have hz := qaZ1_pos (L := L) u
  have h40 := qa_u_Z2_le hu huL hu4
  have hz₂ : 0 ≤ qaZ2 L u := Finset.sum_nonneg fun _ _ => by positivity
  have hcore := qa_core (z := qaZ1 L u) (d * m) hu (qaS_nonneg a) hz hz₂ h40
  have h1t : 0 < 1 - t := by linarith
  set P := Real.exp (-u * qaS a) / (qaZ1 L u) ^ (d * m) * (-qaS a + ((d * m : ℕ) : ℝ) * qaZ2 L u / qaZ1 L u)
    with hP
  have hzn : 0 < (qaZ1 L u) ^ (d * m) := pow_pos hz _
  -- `|P u'| ≤ |P| u / (2(1-t))`
  have h2 : |P * u'| ≤ (1 + 40 * ((d * m : ℕ) : ℝ)) / (qaZ1 L u) ^ (d * m) / (2 * (1 - t)) := by
    rw [abs_mul]
    calc |P| * |u'| ≤ |P| * (u / (2 * (1 - t))) := mul_le_mul_of_nonneg_left hu'b (abs_nonneg _)
      _ = (|P| * u) / (2 * (1 - t)) := by ring
      _ ≤ (1 + 40 * ((d * m : ℕ) : ℝ)) / (qaZ1 L u) ^ (d * m) / (2 * (1 - t)) :=
          div_le_div_of_nonneg_right hcore (by positivity)
  have hinv := qa_Zinv_le (L := L) hg ht
  have h3 : 1 / (qaZ1 L u) ^ (d * m) ≤ 6 ^ (d * m) * ((ellT L g t)⁻¹) ^ (d * m) := by
    rw [one_div, ← inv_pow, ← mul_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 hz.le) (by simpa [hudef] using hinv) _
  have hn : 0 ≤ 1 + 40 * ((d * m : ℕ) : ℝ) := by positivity
  change |P * u'| ≤ _
  calc |P * u'| ≤ (1 + 40 * ((d * m : ℕ) : ℝ)) / (qaZ1 L u) ^ (d * m) / (2 * (1 - t)) := h2
    _ = (1 + 40 * ((d * m : ℕ) : ℝ)) * (1 / (qaZ1 L u) ^ (d * m)) * (1 - t)⁻¹ / 2 := by
        field_simp
    _ ≤ (1 + 40 * ((d * m : ℕ) : ℝ)) * (6 ^ (d * m) * ((ellT L g t)⁻¹) ^ (d * m)) * (1 - t)⁻¹ / 2 := by
        gcongr
    _ ≤ (1 + 40 * ((d * m : ℕ) : ℝ)) * 6 ^ (d * m) * (1 - t)⁻¹ * ((ellT L g t)⁻¹) ^ (d * m) := by
        have : 0 ≤ (1 + 40 * ((d * m : ℕ) : ℝ)) * (6 ^ (d * m) * ((ellT L g t)⁻¹) ^ (d * m)) * (1 - t)⁻¹ := by
          have : 0 ≤ (ellT L g t)⁻¹ := inv_nonneg.2 (ellT_pos (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))).le
          positivity
        nlinarith

private theorem qa_inv_pow_eq (d m : ℕ) (x : ℝ) : ((x ^ d)⁻¹) ^ m = (x⁻¹) ^ (d * m) := by
  rw [pow_mul, inv_pow x d]

/-- **`STMollifierProps` for the mollifier**, constants `C = (1 + 40 d m) 6^{d m}`, `c = 1/2`
(independent of `g` and `L ≥ 3`). -/
theorem QopAlgebra_mollifier_props (d L m : ℕ) [NeZero L] (hL : 3 ≤ L) {g : ℝ} (hg : 0 < g) :
    STMollifierProps (d := d) g ((1 + 40 * ((d * m : ℕ) : ℝ)) * 6 ^ (d * m)) (1 / 2)
      (QopAlgebra_mollifier d L m g) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  refine ⟨fun t a₁ => QopAlgebra_mollifier_sum d L m g t a₁, ?_, ?_, ?_⟩
  · -- the sup bound
    intro t ht0 ht a
    have hl : 0 < ellT L g t := ellT_pos hL1
    have hz := qaZ1_pos (L := L) (qaU L g t)
    unfold QopAlgebra_mollifier
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hΦ0 : 0 ≤ qaPhi d L m a (qaU L g t) := by unfold qaPhi; positivity
    rw [abs_of_nonneg hΦ0, qa_inv_pow_eq]
    have hS := qaS_nonneg a
    have h1 : Real.exp (-qaU L g t * qaS a)
        ≤ Real.exp (-(1 / 2) * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)),
            (zdistD d L (a i - a 0) : ℝ)) / ellT L g t) := by
      refine Real.exp_le_exp.2 ?_
      have h2 : -(1 / 2 : ℝ) * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)), (zdistD d L (a i - a 0) : ℝ)) / ellT L g t
          = -(qaS a * (2 * ellT L g t)⁻¹) := by
        unfold qaS; field_simp
      rw [h2]
      have := mul_le_mul_of_nonneg_left (qaU_lb (L := L) hg ht) hS
      linarith
    have hinv := qa_Zinv_le (L := L) hg ht
    have h3 : 1 / (qaZ1 L (qaU L g t)) ^ (d * m) ≤ 6 ^ (d * m) * ((ellT L g t)⁻¹) ^ (d * m) := by
      rw [one_div, ← inv_pow, ← mul_pow]
      exact pow_le_pow_left₀ (inv_nonneg.2 hz.le) hinv _
    have h6 : (1 : ℝ) ≤ 1 + 40 * ((d * m : ℕ) : ℝ) := by
      have : (0 : ℝ) ≤ 40 * ((d * m : ℕ) : ℝ) := by positivity
      linarith
    have h7 : (0 : ℝ) ≤ 6 ^ (d * m) * ((ellT L g t)⁻¹) ^ (d * m) := by positivity
    have he0 := Real.exp_pos (-(1 / 2) * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)),
            (zdistD d L (a i - a 0) : ℝ)) / ellT L g t)
    unfold qaPhi
    calc Real.exp (-qaU L g t * qaS a) / (qaZ1 L (qaU L g t)) ^ (d * m)
        = Real.exp (-qaU L g t * qaS a) * (1 / (qaZ1 L (qaU L g t)) ^ (d * m)) := by ring
      _ ≤ Real.exp (-(1 / 2) * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)),
            (zdistD d L (a i - a 0) : ℝ)) / ellT L g t) * (6 ^ (d * m) * ((ellT L g t)⁻¹) ^ (d * m)) :=
          mul_le_mul h1 h3 (by positivity) he0.le
      _ ≤ ((1 + 40 * ((d * m : ℕ) : ℝ)) * 6 ^ (d * m)) * ((ellT L g t)⁻¹) ^ (d * m) *
          Real.exp (-(1 / 2) * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)),
            (zdistD d L (a i - a 0) : ℝ)) / ellT L g t) := by
          have h8 : 6 ^ (d * m) * ((ellT L g t)⁻¹) ^ (d * m)
              ≤ (1 + 40 * ((d * m : ℕ) : ℝ)) * 6 ^ (d * m) * ((ellT L g t)⁻¹) ^ (d * m) := by
            have := mul_le_mul_of_nonneg_right h6 (by positivity : (0 : ℝ) ≤ 6 ^ (d * m) * ((ellT L g t)⁻¹) ^ (d * m))
            linarith
          nlinarith
  · -- differentiability
    intro a t ht
    obtain ⟨x, hx, _⟩ := qa_deriv_real d L m hg ht.2 hL a
    exact (hx.ofReal_comp.differentiableAt).differentiableWithinAt
  · -- the derivative bound
    intro t ht0 ht a
    obtain ⟨x, hx, hxb⟩ := qa_deriv_real d L m hg ht hL a
    have hd : HasDerivAt (fun τ => QopAlgebra_mollifier d L m g τ a) (x : ℂ) t := hx.ofReal_comp
    rw [hd.deriv, Complex.norm_real, Real.norm_eq_abs, qa_inv_pow_eq]
    calc |x| ≤ _ := hxb
      _ = _ := by ring

/-- **Existence of the mollifier** (`rmk:choosechi`, `3_5:1250`): the pin `STMollifierEx` of
`Step34Pins.lean:518`.  The constants `C = (1 + 40 d m) 6^{d m}`, `c = 1/2` do not depend on `Λ`. -/
theorem stMollifierEx_holds (d : ℕ) : STMollifierEx d := by
  intro _ m Λ _
  refine ⟨(1 + 40 * ((d * m : ℕ) : ℝ)) * 6 ^ (d * m), 1 / 2, by positivity, by norm_num, ?_⟩
  intro L hL g hg _
  have : NeZero L := ⟨by omega⟩
  exact ⟨QopAlgebra_mollifier d L m g, QopAlgebra_mollifier_props d L m hL hg⟩

/-- `t ↦ ϑ_{t,a}` is differentiable at every `t < 1` (a two-sided derivative, also at `t = 0`). -/
theorem QopAlgebra_mollifier_differentiableAt (d L m : ℕ) [NeZero L] (hL : 3 ≤ L) {g t : ℝ} (hg : 0 < g)
    (ht : t < 1) (a : Fin (m + 1) → Zd d L) :
    DifferentiableAt ℝ (fun τ => QopAlgebra_mollifier d L m g τ a) t := by
  obtain ⟨x, hx, _⟩ := qa_deriv_real d L m hg ht hL a
  exact hx.ofReal_comp.differentiableAt

/-! ## 5. The algebra of `𝒫`, `𝒬_t`, `Θ`, `U` on sum-zero tensors

Ported from RBM2D `Induction/SumZeroQ.lean` at `c9a24cf` (`qa_sum_filter_prod` :53, `qa_slot_zero` :236,
`qa_slot_succ` :269; `QopAlgebra_Psum_Qop` :122, `QopAlgebra_Qop_of_sumZero`, `qa_SB_mul_Theta_symm` :216,
`qa_col_sum_SBTheta` :226, `QopAlgebra_ThetaN_sumZero` :324, `QopAlgebra_commutator_ThetaN` :359): `Z2 L ↦ Zd d L`, `Fin k ↦ Fin (m+1)`, `Psum ↦ STPsum`,
`Qop ↦ STQop`, `thetaSig ↦ ThetaN`, `thetaGenMat ↦ thetaKer`. -/

open scoped Matrix

section Algebra

variable {d L m : ℕ} [NeZero L]

/-- `𝒫 ∘ 𝒬_t = 0` (`Def:QtPt`), given `Σ_{a₂..a_n} ϑ_{t,a} = 1` at this `t` (clause 1 of `STMollifierProps`). -/
theorem QopAlgebra_Psum_Qop (ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ) {t : ℝ}
    (hϑ : ∀ a₁, ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁), ϑ t a = 1)
    (A : (Fin (m + 1) → Zd d L) → ℂ) (a₁ : Zd d L) :
    STPsum (d := d) (STQop (d := d) ϑ t A) a₁ = 0 := by
  unfold STPsum
  have h1 : ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁), STQop (d := d) ϑ t A a
      = ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁),
          (A a - STPsum (d := d) A a₁ * ϑ t a) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha0 : a 0 = a₁ := (Finset.mem_filter.mp ha).2
    simp only [STQop, ha0]
  rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum, hϑ a₁, mul_one]
  unfold STPsum
  exact sub_self _

/-- `𝒬_t = id` on sum-zero tensors. -/
theorem QopAlgebra_Qop_of_sumZero (ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ) (t : ℝ)
    {A : (Fin (m + 1) → Zd d L) → ℂ} (hA : ∀ a₁, STPsum (d := d) A a₁ = 0) :
    STQop (d := d) ϑ t A = A := by
  funext a
  simp only [STQop, hA (a 0), zero_mul, sub_zero]

/-- `Σ_{a₂..a_n} ϑ = 1` rewritten as `𝒫 ϑ_t = 1`. -/
theorem QopAlgebra_Psum_mollifier (g t : ℝ) (a₁ : Zd d L) :
    STPsum (d := d) (QopAlgebra_mollifier d L m g t) a₁ = 1 :=
  QopAlgebra_mollifier_sum d L m g t a₁

/-- `𝒫 ∂_tϑ = 0`: differentiate `𝒫ϑ_τ = 1` (valid for all `τ`, so the derivative is taken on a neighbourhood). -/
theorem QopAlgebra_Psum_deriv {ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ}
    (hsum : ∀ τ a₁, ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁), ϑ τ a = 1)
    {t : ℝ} {ϑ' : (Fin (m + 1) → Zd d L) → ℂ} (hd : ∀ a, HasDerivAt (fun τ => ϑ τ a) (ϑ' a) t)
    (a₁ : Zd d L) : STPsum (d := d) ϑ' a₁ = 0 := by
  have h : HasDerivAt (fun τ => ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁), ϑ τ a)
      (∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁), ϑ' a) t :=
    HasDerivAt.fun_sum fun a _ => hd a
  have h1 : (fun τ => ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁), ϑ τ a)
      = fun _ => (1 : ℂ) := funext fun τ => hsum τ a₁
  rw [h1] at h
  exact h.unique (hasDerivAt_const t (1 : ℂ))

/-- `[∂_t, 𝒬_t]` in terms of `∂_tϑ`: for a differentiable family of tensors `𝒜_τ`,
`∂_t(𝒬_t 𝒜_t)_a = (𝒬_t ∂_t𝒜_t)_a - (𝒫 𝒜_t)_{a₁} ∂_tϑ_{t,a}`. -/
theorem QopAlgebra_Qop_hasDerivAt {ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ}
    {A : ℝ → (Fin (m + 1) → Zd d L) → ℂ} {t : ℝ}
    {A' ϑ' : (Fin (m + 1) → Zd d L) → ℂ} (hA : ∀ a, HasDerivAt (fun τ => A τ a) (A' a) t)
    (hϑ : ∀ a, HasDerivAt (fun τ => ϑ τ a) (ϑ' a) t) (a : Fin (m + 1) → Zd d L) :
    HasDerivAt (fun τ => STQop (d := d) ϑ τ (A τ) a)
      (STQop (d := d) ϑ t A' a - STPsum (d := d) (A t) (a 0) * ϑ' a) t := by
  have hP : HasDerivAt (fun τ => STPsum (d := d) (A τ) (a 0)) (STPsum (d := d) A' (a 0)) t := by
    unfold STPsum
    exact HasDerivAt.fun_sum fun b _ => hA b
  have h := (hA a).sub (hP.mul (hϑ a))
  unfold STQop
  convert h using 1
  ring

/-- `∂_t(𝒬_t 𝒜) = -(𝒫𝒜)_{a₁} ∂_tϑ_t` for a `t`-independent tensor `𝒜`. -/
theorem QopAlgebra_Qop_hasDerivAt_const {ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ} {t : ℝ}
    {ϑ' : (Fin (m + 1) → Zd d L) → ℂ} (hϑ : ∀ a, HasDerivAt (fun τ => ϑ τ a) (ϑ' a) t)
    (A : (Fin (m + 1) → Zd d L) → ℂ) (a : Fin (m + 1) → Zd d L) :
    HasDerivAt (fun τ => STQop (d := d) ϑ τ A a) (-(STPsum (d := d) A (a 0) * ϑ' a)) t := by
  have h := QopAlgebra_Qop_hasDerivAt (A := fun _ => A) (A' := fun _ => 0) (t := t)
    (fun a => hasDerivAt_const t (A a)) hϑ a
  convert h using 1
  simp [STQop, STPsum]

/-! ### Column sums of the one-index kernels -/

/-- `S^{(B)} Θ_ζ` is symmetric. -/
private theorem qa_SB_mul_Theta_symm (g : ℝ) (hL : 3 ≤ L) {ζ : ℂ} (hζ : ‖ζ‖ < 1) (x y : Zd d L) :
    (SB d L g * Theta d L g ζ) x y = (SB d L g * Theta d L g ζ) y x := by
  have h : (SB d L g * Theta d L g ζ)ᵀ = SB d L g * Theta d L g ζ := by
    rw [Matrix.transpose_mul, SB_transpose, Theta_transpose_of_three_le hL hζ]
    exact (Theta_commute_SB_of_three_le hL hζ).eq
  have := congrFun (congrFun h y) x
  simpa [Matrix.transpose_apply] using this

/-- The column sums of `S Θ_ζ` are the constant `(1 - ζ)⁻¹`. -/
private theorem qa_col_sum_SBTheta (g : ℝ) (hL : 3 ≤ L) {ζ : ℂ} (hζ : ‖ζ‖ < 1) (y : Zd d L) :
    ∑ c : Zd d L, (SB d L g * Theta d L g ζ) c y = (1 - ζ)⁻¹ := by
  simp_rw [qa_SB_mul_Theta_symm g hL hζ _ y]
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, sum_Theta_row_of_three_le hL hζ]
  rw [← Finset.sum_mul, sum_SB_row d L g hL, one_mul]

/-- The column sums of `Θ_ζ` are the constant `(1 - ζ)⁻¹` (`Θ_ζ` is symmetric with row sums `(1 - ζ)⁻¹`). -/
private theorem qa_col_sum_Theta (g : ℝ) (hL : 3 ≤ L) {ζ : ℂ} (hζ : ‖ζ‖ < 1) (y : Zd d L) :
    ∑ c : Zd d L, Theta d L g ζ c y = (1 - ζ)⁻¹ := by
  have h : ∀ c, Theta d L g ζ c y = Theta d L g ζ y c := fun c => by
    have := congrFun (congrFun (Theta_transpose_of_three_le (d := d) (g := g) hL hζ) y) c
    simpa [Matrix.transpose_apply] using this
  simp_rw [h]
  exact sum_Theta_row_of_three_le hL hζ y

/-- `Σ_c thetaKer(μ, t)(c, y) = μ (1 - tμ)⁻¹`, constant in `y`. -/
theorem QopAlgebra_col_sum_thetaKer (g : ℝ) (hL : 3 ≤ L) {μ : ℂ} {t : ℝ} (h : ‖(t : ℂ) * μ‖ < 1)
    (y : Zd d L) :
    ∑ c : Zd d L, thetaKer d L g μ t c y = μ * (1 - (t : ℂ) * μ)⁻¹ := by
  simp only [thetaKer, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, qa_col_sum_SBTheta g hL h y]

/-- `Σ_c uKer(μ, s, t)(c, y) = (1 - sμ)(1 - tμ)⁻¹`, constant in `y`. -/
theorem QopAlgebra_col_sum_uKer (g : ℝ) (hL : 3 ≤ L) {μ : ℂ} {s t : ℝ} (h : ‖(t : ℂ) * μ‖ < 1)
    (y : Zd d L) :
    ∑ c : Zd d L, uKer d L g μ s t c y = (1 - (s : ℂ) * μ) * (1 - (t : ℂ) * μ)⁻¹ := by
  simp only [uKer, sub_mul, one_mul, Matrix.smul_mul, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, qa_col_sum_Theta g hL h y, qa_col_sum_SBTheta g hL h y]

/-! ### Slot-by-slot sums -/

/-- Slot `0`: `Σ_{a₀ = a₁} Σ_b G(a₀, b) A(a^{(0)}_b) = Σ_b G(a₁, b) (𝒫A)_b`
(RBM2D `SumZeroQ_slot_zero`, `SumZeroQ.lean:236` at `c9a24cf`). -/
private theorem qa_slot_zero (G : Zd d L → Zd d L → ℂ) (A : (Fin (m + 1) → Zd d L) → ℂ) (a₁ : Zd d L) :
    ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁),
        ∑ b : Zd d L, G (a 0) b * A (Function.update a 0 b)
      = ∑ b : Zd d L, G a₁ b * STPsum (d := d) A b := by
  have h1 : ∀ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁),
      ∑ b : Zd d L, G (a 0) b * A (Function.update a 0 b)
        = ∑ b : Zd d L, G a₁ b * A (Function.update a 0 b) := by
    intro a ha
    have ha0 : a 0 = a₁ := (Finset.mem_filter.mp ha).2
    simp only [ha0]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  unfold STPsum
  refine Finset.sum_nbij' (fun a => Function.update a 0 b) (fun a => Function.update a 0 a₁)
    ?_ ?_ ?_ ?_ ?_
  · intro a _
    simp
  · intro a ha
    have ha0 : a 0 = b := (Finset.mem_filter.mp ha).2
    simp
  · intro a ha
    have ha0 : a 0 = a₁ := (Finset.mem_filter.mp ha).2
    simp [ha0]
  · intro a ha
    have ha0 : a 0 = b := (Finset.mem_filter.mp ha).2
    simp [ha0]
  · intro a _
    rfl

/-- Slot `i ≠ 0`: the reindexing `(a, b) ↦ (a^{(i)}_b, a_i)` of `{a₀ = a₁} × ℤ_L^d`
(RBM2D `SumZeroQ_slot_succ`, `SumZeroQ.lean:269` at `c9a24cf`). -/
private theorem qa_slot_succ {i : Fin (m + 1)} (hi : i ≠ 0) (G : Zd d L → Zd d L → ℂ)
    (A : (Fin (m + 1) → Zd d L) → ℂ) (a₁ : Zd d L) :
    ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁),
        ∑ b : Zd d L, G (a i) b * A (Function.update a i b)
      = ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁),
          (∑ c : Zd d L, G c (a i)) * A a := by
  classical
  set F : Finset (Fin (m + 1) → Zd d L) :=
    Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁) with hF
  have h1 : ∑ a ∈ F, ∑ b : Zd d L, G (a i) b * A (Function.update a i b)
      = ∑ x ∈ F ×ˢ (Finset.univ : Finset (Zd d L)), G (x.1 i) x.2 * A (Function.update x.1 i x.2) :=
    (Finset.sum_product' F Finset.univ (fun a b => G (a i) b * A (Function.update a i b))).symm
  have h2 : ∑ x ∈ F ×ˢ (Finset.univ : Finset (Zd d L)), G (x.1 i) x.2 * A (Function.update x.1 i x.2)
      = ∑ x ∈ F ×ˢ (Finset.univ : Finset (Zd d L)), G x.2 (x.1 i) * A x.1 := by
    refine Finset.sum_nbij' (fun x => (Function.update x.1 i x.2, x.1 i))
      (fun x => (Function.update x.1 i x.2, x.1 i)) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      have hx0 : x.1 0 = a₁ := (Finset.mem_filter.mp (Finset.mem_product.mp hx).1).2
      simp [hF, Function.update_of_ne hi.symm, hx0]
    · intro x hx
      have hx0 : x.1 0 = a₁ := (Finset.mem_filter.mp (Finset.mem_product.mp hx).1).2
      simp [hF, Function.update_of_ne hi.symm, hx0]
    · intro x _
      refine Prod.ext ?_ ?_
      · simp
      · simp
    · intro x _
      refine Prod.ext ?_ ?_
      · simp
      · simp
    · intro x _
      simp
  rw [h1, h2, Finset.sum_product' F Finset.univ (fun a b => G b (a i) * A a)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]

/-- `Θ^{(m+1)}_{t,σ}` preserves sum-zero tensors: slot `0` gives `Σ_b K(a₁, b)(𝒫A)_b = 0`, every slot
`i ≥ 1` gives the constant column sum of `K_i` times `(𝒫A)_{a₁} = 0`. -/
theorem QopAlgebra_ThetaN_sumZero (g : ℝ) (hL : 3 ≤ L) {μs : Fin (m + 1) → ℂ} (hμ : ∀ i, ‖μs i‖ = 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {A : (Fin (m + 1) → Zd d L) → ℂ}
    (hA : ∀ a₁, STPsum (d := d) A a₁ = 0) (a₁ : Zd d L) :
    STPsum (d := d) (ThetaN d L g μs t A) a₁ = 0 := by
  unfold STPsum
  simp only [ThetaN]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i = 0
  · subst hi
    refine (qa_slot_zero (d := d) (fun x y => thetaKer d L g (cycProd μs 0) t x y) A a₁).trans ?_
    exact Finset.sum_eq_zero fun b _ => by rw [hA b, mul_zero]
  · refine (qa_slot_succ (d := d) hi (fun x y => thetaKer d L g (cycProd μs i) t x y) A a₁).trans ?_
    have hcol : ∀ y : Zd d L, ∑ c : Zd d L, thetaKer d L g (cycProd μs i) t c y
        = cycProd μs i * (1 - (t : ℂ) * cycProd μs i)⁻¹ :=
      fun y => QopAlgebra_col_sum_thetaKer g hL (norm_t_mul_lt_one ht0 ht1 (norm_cycProd hμ i)) y
    simp only [hcol]
    rw [← Finset.mul_sum]
    have h : ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁), A a = 0 := hA a₁
    rw [h, mul_zero]

/-- `Σ_b f(b₀) A(b) = Σ_{b₀} f(b₀) (𝒫A)_{b₀}`. -/
private theorem qa_sum_fiber0 (f : Zd d L → ℂ) (A : (Fin (m + 1) → Zd d L) → ℂ) :
    ∑ b : Fin (m + 1) → Zd d L, f (b 0) * A b = ∑ b₀ : Zd d L, f b₀ * STPsum (d := d) A b₀ := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun b : Fin (m + 1) → Zd d L => b 0)
    (fun b => f (b 0) * A b)]
  refine Finset.sum_congr rfl fun b₀ _ => ?_
  unfold STPsum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [(Finset.mem_filter.1 hb).2]

/-- `U^{(m+1)}_{s,t,σ}` preserves sum-zero tensors: summing over `a ∈ {a₀ = a₁}` the factors `i ≥ 1` give the
constant column sums `(1 - sμ_i)/(1 - tμ_i)`, and slot `0` leaves `Σ_{b₀} K₀(a₁, b₀) (𝒫A)_{b₀} = 0`. -/
theorem QopAlgebra_UN_sumZero (g : ℝ) (hL : 3 ≤ L) {μs : Fin (m + 1) → ℂ} (hμ : ∀ i, ‖μs i‖ = 1)
    {s t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {A : (Fin (m + 1) → Zd d L) → ℂ}
    (hA : ∀ a₁, STPsum (d := d) A a₁ = 0) (a₁ : Zd d L) :
    STPsum (d := d) (UN d L g μs s t A) a₁ = 0 := by
  set K : Fin (m + 1) → Matrix (Zd d L) (Zd d L) ℂ := fun i => uKer d L g (cycProd μs i) s t with hK
  set κ : Fin (m + 1) → ℂ := fun i => (1 - (s : ℂ) * cycProd μs i) * (1 - (t : ℂ) * cycProd μs i)⁻¹ with hκ
  have hcol : ∀ i (y : Zd d L), ∑ c : Zd d L, K i c y = κ i := fun i y =>
    QopAlgebra_col_sum_uKer g hL (norm_t_mul_lt_one ht0 ht1 (norm_cycProd hμ i)) y
  unfold STPsum
  simp only [UN]
  rw [Finset.sum_comm]
  -- for fixed `b`: `Σ_{a₀ = a₁} Π_i K_i(a_i, b_i) = K₀(a₁, b₀) Π_{i ≠ 0} κ_i`
  have h1 : ∀ b : Fin (m + 1) → Zd d L,
      ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁), (∏ i, K i (a i) (b i)) * A b
        = (K 0 a₁ (b 0) * ∏ i ∈ Finset.univ.erase (0 : Fin (m + 1)), κ i) * A b := by
    intro b
    rw [← Finset.sum_mul]
    congr 1
    have h2 : ∀ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁),
        ∏ i, K i (a i) (b i) = K 0 a₁ (b 0) * ∏ i ∈ Finset.univ.erase (0 : Fin (m + 1)), K i (a i) (b i) := by
      intro a ha
      have ha0 : a 0 = a₁ := (Finset.mem_filter.1 ha).2
      rw [← Finset.mul_prod_erase Finset.univ (fun i => K i (a i) (b i)) (Finset.mem_univ (0 : Fin (m + 1))), ha0]
    rw [Finset.sum_congr rfl h2, ← Finset.mul_sum,
      qa_sum_filter_prod (d := d) (L := L) (m := m) a₁ (fun i c => K i c (b i))]
    congr 1
    exact Finset.prod_congr rfl fun i _ => hcol i (b i)
  rw [Finset.sum_congr rfl fun b _ => h1 b]
  have h3 : ∀ b : Fin (m + 1) → Zd d L,
      (K 0 a₁ (b 0) * ∏ i ∈ Finset.univ.erase (0 : Fin (m + 1)), κ i) * A b
        = (∏ i ∈ Finset.univ.erase (0 : Fin (m + 1)), κ i) * (K 0 a₁ (b 0) * A b) := fun b => by ring
  rw [Finset.sum_congr rfl fun b _ => h3 b, ← Finset.mul_sum,
    qa_sum_fiber0 (d := d) (fun b₀ => K 0 a₁ b₀) A]
  have : ∑ b₀ : Zd d L, K 0 a₁ b₀ * STPsum (d := d) A b₀ = 0 :=
    Finset.sum_eq_zero fun b₀ _ => by rw [hA b₀, mul_zero]
  rw [this, mul_zero]

/-! ### The commutator formulas (pure linearity) -/

theorem QopAlgebra_ThetaN_sub (g : ℝ) (μs : Fin (m + 1) → ℂ) (u : ℝ) (A B : (Fin (m + 1) → Zd d L) → ℂ)
    (a : Fin (m + 1) → Zd d L) :
    ThetaN d L g μs u (fun b => A b - B b) a = ThetaN d L g μs u A a - ThetaN d L g μs u B a := by
  simp only [ThetaN, mul_sub, Finset.sum_sub_distrib]

theorem QopAlgebra_UN_sub (g : ℝ) (μs : Fin (m + 1) → ℂ) (s u : ℝ) (A B : (Fin (m + 1) → Zd d L) → ℂ)
    (a : Fin (m + 1) → Zd d L) :
    UN d L g μs s u (fun b => A b - B b) a = UN d L g μs s u A a - UN d L g μs s u B a := by
  simp only [UN, mul_sub, Finset.sum_sub_distrib]

/-- The commutator `[𝒬_t, Θ^{(m+1)}_{t,σ}]` (`pqthlk`): `𝒬_t Θ𝒜 - Θ 𝒬_t𝒜 = Θ((𝒫𝒜)_{b₁} ϑ_t) - (𝒫Θ𝒜)_{a₁} ϑ_t`. -/
theorem QopAlgebra_commutator_ThetaN (g : ℝ) (μs : Fin (m + 1) → ℂ) (ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ)
    (t : ℝ) (A : (Fin (m + 1) → Zd d L) → ℂ) (a : Fin (m + 1) → Zd d L) :
    STQop (d := d) ϑ t (ThetaN d L g μs t A) a - ThetaN d L g μs t (STQop (d := d) ϑ t A) a =
      ThetaN d L g μs t (fun b => STPsum (d := d) A (b 0) * ϑ t b) a -
        STPsum (d := d) (ThetaN d L g μs t A) (a 0) * ϑ t a := by
  have h : ThetaN d L g μs t (STQop (d := d) ϑ t A) a
      = ThetaN d L g μs t A a - ThetaN d L g μs t (fun b => STPsum (d := d) A (b 0) * ϑ t b) a :=
    QopAlgebra_ThetaN_sub g μs t A (fun b => STPsum (d := d) A (b 0) * ϑ t b) a
  rw [h]
  simp only [STQop]
  ring

/-- The same for `U^{(m+1)}_{s,t,σ}`. -/
theorem QopAlgebra_commutator_UN (g : ℝ) (μs : Fin (m + 1) → ℂ) (ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ)
    (s t : ℝ) (A : (Fin (m + 1) → Zd d L) → ℂ) (a : Fin (m + 1) → Zd d L) :
    STQop (d := d) ϑ t (UN d L g μs s t A) a - UN d L g μs s t (STQop (d := d) ϑ t A) a =
      UN d L g μs s t (fun b => STPsum (d := d) A (b 0) * ϑ t b) a -
        STPsum (d := d) (UN d L g μs s t A) (a 0) * ϑ t a := by
  have h : UN d L g μs s t (STQop (d := d) ϑ t A) a
      = UN d L g μs s t A a - UN d L g μs s t (fun b => STPsum (d := d) A (b 0) * ϑ t b) a :=
    QopAlgebra_UN_sub g μs s t A (fun b => STPsum (d := d) A (b 0) * ϑ t b) a
  rw [h]
  simp only [STQop]
  ring

end Algebra

/-! ## 6. Compiled nonempty instances -/

/-- `stMollifierEx_holds` at `d = 3`, `m = 1` (two indices), `Λ = 1`. -/
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L : ℕ) (_ : 3 ≤ L) (g : ℝ), 0 < g → g ≤ 1 →
    haveI : NeZero L := ⟨by omega⟩
    ∃ ϑ : ℝ → (Fin (1 + 1) → Zd 3 L) → ℂ, STMollifierProps (d := 3) g C c ϑ :=
  stMollifierEx_holds 3 (by norm_num) 1 1 one_pos

/-- `stMollifierEx_holds` at `d = 3`, `m = 2` (three indices), `Λ = 1`. -/
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L : ℕ) (_ : 3 ≤ L) (g : ℝ), 0 < g → g ≤ 1 →
    haveI : NeZero L := ⟨by omega⟩
    ∃ ϑ : ℝ → (Fin (2 + 1) → Zd 3 L) → ℂ, STMollifierProps (d := 3) g C c ϑ :=
  stMollifierEx_holds 3 (by norm_num) 2 1 one_pos

/-- The same, unpacked at the data `L = 5`, `g = 1`, `m = 2`: the constants and a mollifier. -/
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∃ ϑ : ℝ → (Fin (2 + 1) → Zd 3 5) → ℂ, STMollifierProps (d := 3) (1 : ℝ) C c ϑ := by
  obtain ⟨C, c, hC, hc, h⟩ := stMollifierEx_holds 3 (by norm_num) 2 1 one_pos
  exact ⟨C, c, hC, hc, h 5 (by norm_num) 1 one_pos le_rfl⟩

/-- The mollifier itself at `d = 3`, `L = 3`, `m = 1`, `g = 1`: the four properties of `STMollifierProps`
with the explicit constants `C = (1 + 40·3·1) 6^{3·1}`, `c = 1/2`. -/
example : STMollifierProps (d := 3) (L := 3) (m := 1) (1 : ℝ) ((1 + 40 * ((3 * 1 : ℕ) : ℝ)) * 6 ^ (3 * 1)) (1 / 2)
    (QopAlgebra_mollifier 3 3 1 1) :=
  QopAlgebra_mollifier_props 3 3 1 le_rfl one_pos

/-- Data of the algebra instances: `d = 3`, `L = 3`, two indices (`m = 1`), `g = 1`, the mollifier `ϑ`. -/
private abbrev qaTheta : ℝ → (Fin (1 + 1) → Zd 3 3) → ℂ := QopAlgebra_mollifier 3 3 1 1

private theorem qaTheta_sum (τ : ℝ) (a₁ : Zd 3 3) :
    ∑ a ∈ Finset.univ.filter (fun a : Fin (1 + 1) → Zd 3 3 => a 0 = a₁), qaTheta τ a = 1 :=
  QopAlgebra_mollifier_sum 3 3 1 1 τ a₁

/-- `𝒫 ∘ 𝒬_t = 0` at `d = 3`, `L = 3`, `t = 1/2`. -/
example (A : (Fin (1 + 1) → Zd 3 3) → ℂ) (a₁ : Zd 3 3) :
    STPsum (d := 3) (STQop (d := 3) qaTheta (1 / 2) A) a₁ = 0 :=
  QopAlgebra_Psum_Qop qaTheta (qaTheta_sum (1 / 2)) A a₁

/-- `𝒬_t = id` on the sum-zero tensor `𝒬_t 1`. -/
example : STQop (d := 3) qaTheta (1 / 2) (STQop (d := 3) qaTheta (1 / 2) (fun _ => (1 : ℂ)))
    = STQop (d := 3) qaTheta (1 / 2) (fun _ => (1 : ℂ)) :=
  QopAlgebra_Qop_of_sumZero qaTheta (1 / 2) fun a₁ => QopAlgebra_Psum_Qop qaTheta (qaTheta_sum (1 / 2)) _ a₁

/-- `Θ^{(2)}_{t,σ}` preserves sum-zero (`μ_i = 1`, `g = 1`, `t = 1/2`) on the sum-zero tensor `𝒬_t 1`. -/
example (a₁ : Zd 3 3) :
    STPsum (d := 3) (ThetaN 3 3 (1 : ℝ) (fun _ : Fin (1 + 1) => (1 : ℂ)) (1 / 2)
      (STQop (d := 3) qaTheta (1 / 2) (fun _ => (1 : ℂ)))) a₁ = 0 :=
  QopAlgebra_ThetaN_sumZero 1 (le_refl 3) (fun _ => norm_one) (by norm_num) (by norm_num)
    (fun a₁ => QopAlgebra_Psum_Qop qaTheta (qaTheta_sum (1 / 2)) _ a₁) a₁

/-- `U^{(2)}_{s,t,σ}` preserves sum-zero (`μ_i = 1`, `g = 1`, `s = 1/4`, `t = 1/2`). -/
example (a₁ : Zd 3 3) :
    STPsum (d := 3) (UN 3 3 (1 : ℝ) (fun _ : Fin (1 + 1) => (1 : ℂ)) (1 / 4) (1 / 2)
      (STQop (d := 3) qaTheta (1 / 2) (fun _ => (1 : ℂ)))) a₁ = 0 :=
  QopAlgebra_UN_sumZero 1 (le_refl 3) (fun _ => norm_one) (by norm_num) (by norm_num)
    (fun a₁ => QopAlgebra_Psum_Qop qaTheta (qaTheta_sum (1 / 2)) _ a₁) a₁

/-- The commutator `[𝒬_t, Θ^{(2)}_{t,σ}]` at the same data. -/
example (A : (Fin (1 + 1) → Zd 3 3) → ℂ) (a : Fin (1 + 1) → Zd 3 3) :
    STQop (d := 3) qaTheta (1 / 2) (ThetaN 3 3 (1 : ℝ) (fun _ : Fin (1 + 1) => (1 : ℂ)) (1 / 2) A) a
        - ThetaN 3 3 (1 : ℝ) (fun _ : Fin (1 + 1) => (1 : ℂ)) (1 / 2) (STQop (d := 3) qaTheta (1 / 2) A) a =
      ThetaN 3 3 (1 : ℝ) (fun _ : Fin (1 + 1) => (1 : ℂ)) (1 / 2)
          (fun b => STPsum (d := 3) A (b 0) * qaTheta (1 / 2) b) a -
        STPsum (d := 3) (ThetaN 3 3 (1 : ℝ) (fun _ : Fin (1 + 1) => (1 : ℂ)) (1 / 2) A) (a 0) * qaTheta (1 / 2) a :=
  QopAlgebra_commutator_ThetaN 1 _ qaTheta (1 / 2) A a

/-- `𝒫 ∂_tϑ = 0` at `t = 0` (two-sided derivative). -/
example (a₁ : Zd 3 3) : STPsum (d := 3) (fun a => deriv (fun τ => qaTheta τ a) 0) a₁ = 0 :=
  QopAlgebra_Psum_deriv qaTheta_sum
    (fun a => (QopAlgebra_mollifier_differentiableAt 3 3 1 le_rfl one_pos (by norm_num) a).hasDerivAt) a₁

/-- `∂_t(𝒬_t 𝒜) = -(𝒫𝒜)_{a₁} ∂_tϑ` at `t = 0`, `𝒜 = 1`. -/
example (a : Fin (1 + 1) → Zd 3 3) :
    HasDerivAt (fun τ => STQop (d := 3) qaTheta τ (fun _ => (1 : ℂ)) a)
      (-(STPsum (d := 3) (fun _ : Fin (1 + 1) → Zd 3 3 => (1 : ℂ)) (a 0) * deriv (fun τ => qaTheta τ a) 0)) 0 :=
  QopAlgebra_Qop_hasDerivAt_const
    (fun a => (QopAlgebra_mollifier_differentiableAt 3 3 1 le_rfl one_pos (by norm_num) a).hasDerivAt) _ a

/-- The commutator `[𝒬_t, U^{(2)}_{s,t,σ}]` at `μ_i = 1`, `g = 1`, `s = 1/4`, `t = 1/2`. -/
example (A : (Fin (1 + 1) → Zd 3 3) → ℂ) (a : Fin (1 + 1) → Zd 3 3) :
    STQop (d := 3) qaTheta (1 / 2) (UN 3 3 (1 : ℝ) (fun _ : Fin (1 + 1) => (1 : ℂ)) (1 / 4) (1 / 2) A) a
        - UN 3 3 (1 : ℝ) (fun _ : Fin (1 + 1) => (1 : ℂ)) (1 / 4) (1 / 2)
            (STQop (d := 3) qaTheta (1 / 2) A) a =
      UN 3 3 (1 : ℝ) (fun _ : Fin (1 + 1) => (1 : ℂ)) (1 / 4) (1 / 2)
          (fun b => STPsum (d := 3) A (b 0) * qaTheta (1 / 2) b) a -
        STPsum (d := 3) (UN 3 3 (1 : ℝ) (fun _ : Fin (1 + 1) => (1 : ℂ)) (1 / 4) (1 / 2) A) (a 0) *
          qaTheta (1 / 2) a :=
  QopAlgebra_commutator_UN 1 _ qaTheta (1 / 4) (1 / 2) A a

/-- The general `[∂_t, 𝒬_t]` identity at `t = 0` with the `t`-dependent tensor `𝒜_τ ≡ τ`, `∂_t𝒜 ≡ 1`. -/
example (a : Fin (1 + 1) → Zd 3 3) :
    HasDerivAt (fun τ : ℝ => STQop (d := 3) qaTheta τ (fun _ => (τ : ℂ)) a)
      (STQop (d := 3) qaTheta 0 (fun _ => (1 : ℂ)) a -
        STPsum (d := 3) (fun _ : Fin (1 + 1) → Zd 3 3 => ((0 : ℝ) : ℂ)) (a 0) *
          deriv (fun τ => qaTheta τ a) 0) 0 :=
  QopAlgebra_Qop_hasDerivAt (A := fun τ _ => (τ : ℂ)) (A' := fun _ => 1)
    (fun _ => by simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp)
    (fun a => (QopAlgebra_mollifier_differentiableAt 3 3 1 le_rfl one_pos (by norm_num) a).hasDerivAt) a

end RBM.Gauss.Sizes

end
