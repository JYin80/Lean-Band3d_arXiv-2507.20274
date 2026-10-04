/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step2K2
import RBM3D.Evolution.PropTInf
import RBM3D.Loop.KLWard
import RBM3D.Induction.ConArgDet

/-!
# ST2-07 (ticket T2099): `lem:newKLK`, the pin `STNewKLK` proved

`stNewKLK_holds (d : ℕ) : STNewKLK d` (`Induction/Step2Defs.lean:377`; paper `3_5:371-378`, proof
`3_5:610-654`): for `3 ≤ d`, with `δ₀ = κ/2` and a constant `C` depending on `(d, 𝔡)` only
(`nkl_at`), every Hermitian `H` with `‖G_u - M‖_max ≤ δ₀` has
`|Θ^{(2)} ∘ (𝓛-𝒦)^{(2)}| ≤ C/(1-u) Ĵ W^{-d} 𝒯̃` and
`|𝓔^{(𝓛-𝒦)×(𝓛-𝒦)}| ≤ C/(1-u) (Ĵ + Ĵ² 1_{ℓ≥1}) W^{-d} 𝒯̃` (`STNewKLKAt`).  Deterministic: the only
inputs are `Prop5Decay` (`prop5Decay_holds`), `(TTT2)` (`ekPropTInf_holds`) and the resolvent
identity; no stochastic premise.

Proof (all steps are merged facts or elementary).
* **A. Tail function.** Shift `𝒯_t(r') ≤ C_s 𝒯_t(r)` for `r ≤ r' + 1`, `C_s = 2^{d-2} e`
  (`nkl_tailT_shift`: `B_{t,r}` loses `2^{d-2}`, the zero mode is constant, `√(r/ℓ_t)` moves by at
  most `1` since `ℓ_t ≥ 1`).  *Near/far* (replaces the paper's cut `K` with `𝒯(K) = W^{-D}`, no
  intermediate value argument): `r` is near if `1 ≤ ℓ`, `r ≤ ℓ`, `W^{-D} ≤ 𝒯(r)`; then
  `𝒯̃(r) = 𝒯(r)` (`nkl_tailW_eq_of_near`); otherwise `𝒯̃(r) ≤ C_s 𝒯̃(r')` for every distance `r'`
  (`nkl_tailW_far`; for `ℓ < 1` the profile is constant up to `C_s` on distances).  The floor
  `W^{-D}` is never summed over `L^d` points (DECISIONS §29 (3)).
* **B. Propagator.** `|Θ_ξ(a,b)| ≤ C₁ 𝒯_u(|a-b|_∞)`, `C₁ = C₅ e^{1/(4c)}` (`nkl_theta_tail`, a
  copy of the private `k2d_theta_tail`; `stK2decay_holds` carries the floor and cannot be used);
  then
  `|(SΘ)(a,b)| ≤ C₁ C_s 𝒯_u(|a-b|)` (`S_{ab} ≠ 0 ⟹ |a-b|_∞ ≤ 1`) and `Σ_b |(SΘ)(a,b)| ≤ (1-u)⁻¹`
  (`sum_norm_Theta_row_le`, `sum_norm_SB_row`).
* **C. Convolutions.** `Σ_b |(SΘ)(a,b)| 𝒯̃(|b-a'|) ≤ (C₁ C_s C_T + C_s)/(1-u) 𝒯̃(|a-a'|)`
  (`nkl_conv_P`: near `b` by `(TTT2)`, far `b` by the row sum); both-near double sum
  (`nkl_conv_two`).
* **D. Ward for `𝓛^{(2)}`, entrywise** (no list-loop Ward needed).  For every sign pattern
  `‖𝓛_{σ,(a,b)}‖ ≤ W^{-2d} (Q_{ab} + Q_{ba})`, `Q_{ab} = Σ_{l∈[b], j∈[a]} |G_{lj}|²`; the row and
  column masses are `Σ_j |G_{lj}|² = Im G_{ll}/η` and `Σ_l |G_{lj}|² = Im G_{jj}/η`
  (`G G† = G† G = (G-G†)/(2iη)`, `Ind.Gres_mul_conjTranspose`).  With
  `Im G_{xx} ≤ Im m + κ/2 ≤ 2 Im m` (`Ind.half_le_mE_im`),
  both marginals of `‖𝓛^{(2)}‖` are `≤ 4 W^{-d}/(1-u)`, and those of `‖𝒦^{(2)}‖` are
  `≤ W^{-d}/(1-u)` (`Theta_transpose_of_three_le`): `nkl_ward_LKM`, total `5 W^{-d}/(1-u)`.
* **E. Bound 2** (`nkl_bound2`): pairs `(x,y)` with `y` far use `Σ_x |F(x,a₁)|`, with `y` near and
  `x` far use `Σ_y |F(a₀,y)|` (`S` symmetric), both near (only if `1 ≤ ℓ`) use `nkl_conv_two`.
* **Constants.** `C = 2(C₁ C_s C_T + C_s) + 10 C_s + C_s C_T`, `δ₀ = κ/2`.

Sources: no port from RBM1D/RBM2D.  Copies of RBM3D private lemmas: `nkl_sqrt_le`, `nkl_theta_tail`
(`Induction/Step2K2.lean:65`, `:78`, `0fc2597`), `nkl_gres_blockMat_true`, `nkl_Gres_false`
(`Green/Pins.lean:350`, `:367`, `64bdfd3`), `nkl_mE_zero` (`Induction/ConArgDet.lean:1371`,
`bbd22a5`), `nkl_zdistInf_add_le` (`Evolution/PropTInf.lean:43`).  Helpers are `private`.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Gauss

/-! ### A. The tail function: shift, floor and cut -/

section Tail

variable {d L : ℕ} {g t : ℝ}

/-- **Shift**: `𝒯_t(r') ≤ 2^{d-2} e 𝒯_t(r)` whenever `0 ≤ r`, `0 ≤ r'`, `r ≤ r' + 1`
(`B_{t,r}` loses the factor `2^{d-2}` in `(r+1)^{-(d-2)}`, the zero mode is constant, and the
exponent `√(r/ℓ_t)` moves by at most `1` because `ℓ_t ≥ 1`). -/
private theorem nkl_tailT_shift (hL : 1 ≤ (L : ℝ)) {r r' : ℝ} (hr : 0 ≤ r) (hr' : 0 ≤ r')
    (h : r ≤ r' + 1) :
    tailT d L g t r' ≤ (2 ^ (d - 2) * Real.exp 1) * tailT d L g t r := by
  have hℓ1 : 1 ≤ ellT L g t := one_le_ellT hL
  have hℓ : 0 < ellT L g t := lt_of_lt_of_le one_pos hℓ1
  have h2 : (1 : ℝ) ≤ 2 ^ (d - 2) := one_le_pow₀ (by norm_num)
  have hB : BparamR d L g t r' ≤ 2 ^ (d - 2) * BparamR d L g t r := by
    unfold BparamR
    have hA : 0 ≤ (g ^ 2 + |1 - t|)⁻¹ := inv_nonneg.mpr (by positivity)
    have hZ : 0 ≤ ((L : ℝ) ^ d * |1 - t|)⁻¹ := inv_nonneg.mpr (by positivity)
    have hp : (r + 1) ^ (d - 2) ≤ 2 ^ (d - 2) * (r' + 1) ^ (d - 2) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith) (by linarith) _
    have hq : ((r' + 1) ^ (d - 2))⁻¹ ≤ 2 ^ (d - 2) * ((r + 1) ^ (d - 2))⁻¹ := by
      have hrp : 0 < (r + 1) ^ (d - 2) := pow_pos (by linarith) _
      have hrp' : 0 < (r' + 1) ^ (d - 2) := pow_pos (by linarith) _
      rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hrp' hrp]
      linarith
    have h3 := mul_le_mul_of_nonneg_left hq hA
    nlinarith [mul_nonneg hA (inv_nonneg.mpr (pow_pos (by linarith : (0 : ℝ) < r + 1) (d - 2)).le)]
  have hsq : Real.sqrt (r / ellT L g t) ≤ Real.sqrt (r' / ellT L g t) + 1 := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    have h0 : 0 ≤ r' / ellT L g t := div_nonneg hr' hℓ.le
    have hr1 : r / ellT L g t ≤ r' / ellT L g t + 1 := by
      rw [div_le_iff₀ hℓ, add_mul, div_mul_cancel₀ _ hℓ.ne']
      nlinarith
    nlinarith [Real.sq_sqrt h0, Real.sqrt_nonneg (r' / ellT L g t)]
  have hE : Real.exp (-Real.sqrt (r' / ellT L g t)) ≤
      Real.exp 1 * Real.exp (-Real.sqrt (r / ellT L g t)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  unfold tailT
  calc BparamR d L g t r' * Real.exp (-Real.sqrt (r' / ellT L g t))
      ≤ (2 ^ (d - 2) * BparamR d L g t r) * (Real.exp 1 * Real.exp (-Real.sqrt (r / ellT L g t))) :=
        mul_le_mul hB hE (Real.exp_pos _).le (by
          have := BparamR_nonneg (d := d) (L := L) (g := g) (t := t) hr
          positivity)
    _ = _ := by ring

/-- The shift constant is at least `1`. -/
private theorem nkl_Cs_ge_one : (1 : ℝ) ≤ 2 ^ (d - 2) * Real.exp 1 :=
  one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (Real.one_le_exp (by norm_num))

variable {ℓ W D : ℝ}

/-- `𝒯_t(r) ≤ 𝒯̃(r)`. -/
private theorem nkl_tailT_le_tailW (hℓ : 0 ≤ ℓ) {r : ℝ} (hr : 0 ≤ r) :
    tailT d L g t r ≤ tailW d L g t ℓ W D r :=
  (tailT_antitone (le_min hr hℓ) (min_le_left r ℓ)).trans (le_max_left _ _)

/-- Near region: `𝒯̃(r) = 𝒯_t(r)` for `r ≤ ℓ` and `W^{-D} ≤ 𝒯_t(r)`. -/
private theorem nkl_tailW_eq_of_near {r : ℝ} (hrℓ : r ≤ ℓ) (hω : W ^ (-D) ≤ tailT d L g t r) :
    tailW d L g t ℓ W D r = tailT d L g t r := by
  unfold tailW
  rw [min_eq_left hrℓ]
  exact max_eq_left hω

/-- **Far region**: if `r` is not near (`1 ≤ ℓ`, `r ≤ ℓ`, `W^{-D} ≤ 𝒯_t(r)`), then
`𝒯̃(r) ≤ C_s 𝒯̃(r')` for every `r' ≥ 0` that is `0` or `≥ 1` (a distance). -/
private theorem nkl_tailW_far (hL : 1 ≤ (L : ℝ)) (hW : 0 < W) (hℓ : 0 ≤ ℓ) {r r' : ℝ} (hr : 0 ≤ r)
    (hr' : 0 ≤ r') (hr'1 : r' = 0 ∨ 1 ≤ r')
    (hnear : ¬ (1 ≤ ℓ ∧ r ≤ ℓ ∧ W ^ (-D) ≤ tailT d L g t r)) :
    tailW d L g t ℓ W D r ≤ (2 ^ (d - 2) * Real.exp 1) * tailW d L g t ℓ W D r' := by
  have hP0 : 0 ≤ tailW d L g t ℓ W D r' := (tailW_pos hW r').le
  have hCs := nkl_Cs_ge_one (d := d)
  have hω : 0 ≤ W ^ (-D) := (Real.rpow_pos_of_pos hW _).le
  by_cases h1 : 1 ≤ ℓ
  · have hle : tailW d L g t ℓ W D r ≤ tailW d L g t ℓ W D r' := by
      by_cases hrℓ : r ≤ ℓ
      · have hlt : tailT d L g t r < W ^ (-D) := by
          by_contra hc
          exact hnear ⟨h1, hrℓ, not_lt.1 hc⟩
        unfold tailW
        rw [min_eq_left hrℓ, max_eq_right hlt.le]
        exact le_max_right _ _
      · push Not at hrℓ
        unfold tailW
        rw [min_eq_right hrℓ.le]
        refine max_le ?_ (le_max_right _ _)
        exact (tailT_antitone (le_min hr' hℓ) (min_le_right r' ℓ)).trans (le_max_left _ _)
    nlinarith
  · push Not at h1
    have hPr : tailW d L g t ℓ W D r ≤ tailW d L g t ℓ W D 0 :=
      tailW_antitone hℓ le_rfl hr
    rcases hr'1 with h0 | h1'
    · subst h0
      nlinarith
    · have hsh : tailT d L g t 0 ≤ (2 ^ (d - 2) * Real.exp 1) * tailT d L g t ℓ :=
        nkl_tailT_shift hL hℓ le_rfl (by linarith)
      have hP0' : tailW d L g t ℓ W D 0 ≤ (2 ^ (d - 2) * Real.exp 1) * tailW d L g t ℓ W D r' := by
        unfold tailW
        rw [min_eq_left hℓ, min_eq_right (by linarith : ℓ ≤ r')]
        refine max_le ?_ ?_
        · exact hsh.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity))
        · exact (le_max_right _ _).trans (le_mul_of_one_le_left (le_max_right _ _ |>.trans' hω) hCs)
      exact hPr.trans hP0'

end Tail

/-! ### B. The `L^∞` distance and the block kernel -/

section Dist

variable {d L : ℕ} [NeZero L]

private theorem nkl_zdistInf_neg (x : Zd d L) : zdistInf d L (-x) = zdistInf d L x := by
  simp only [zdistInf, Pi.neg_apply, zdist_neg]

private theorem nkl_zdistInf_sub_comm (x y : Zd d L) : zdistInf d L (x - y) = zdistInf d L (y - x) := by
  rw [← nkl_zdistInf_neg (y - x), neg_sub]

private theorem nkl_zdistInf_add_le (x y : Zd d L) :
    zdistInf d L (x + y) ≤ zdistInf d L x + zdistInf d L y := by
  unfold zdistInf
  refine Finset.sup_le fun i _ => ?_
  calc zdist L ((x + y) i) = zdist L (x i + y i) := rfl
    _ ≤ zdist L (x i) + zdist L (y i) := zdist_add_le L (x i) (y i)
    _ ≤ _ := Nat.add_le_add
        (Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i))
        (Finset.le_sup (f := fun j => zdist L (y j)) (Finset.mem_univ i))

/-- Triangle inequality in the form `|a - c| ≤ |a - b| + |b - c|`. -/
private theorem nkl_zdistInf_tri (a b c : Zd d L) :
    zdistInf d L (a - c) ≤ zdistInf d L (a - b) + zdistInf d L (b - c) := by
  have := nkl_zdistInf_add_le (a - b) (b - c)
  rwa [sub_add_sub_cancel] at this

omit [NeZero L] in
/-- The support of `S^{(B)}`: `S_{ab} ≠ 0` forces `|a - b|_∞ ≤ 1`. -/
private theorem nkl_SB_support (g : ℝ) {a b : Zd d L} (h : SB d L g a b ≠ 0) :
    zdistInf d L (a - b) ≤ 1 := by
  rw [SB_apply] at h
  by_cases h0 : a - b = 0
  · rw [h0]
    simp [zdistInf, zdist]
  · by_cases h1 : zdistD d L (a - b) = 1
    · exact (zdistInf_le_zdistD d L _).trans h1.le
    · exact absurd (by simp [sbKernel, h0, h1]) h

/-- `√y ≤ c y + 1/(4c)` for `c > 0` (copy of the private `k2d_sqrt_le`, `Step2K2.lean:63`). -/
private theorem nkl_sqrt_le {c : ℝ} (hc : 0 < c) (y : ℝ) (hy : 0 ≤ y) :
    Real.sqrt y ≤ c * y + 1 / (4 * c) := by
  set s := Real.sqrt y with hs
  have hy' : y = s ^ 2 := (Real.sq_sqrt hy).symm
  rw [hy', ← sub_nonneg]
  have : c * s ^ 2 + 1 / (4 * c) - s = (2 * c * s - 1) ^ 2 / (4 * c) := by
    field_simp
    ring
  rw [this]
  positivity

/-- **The tail bound of one propagator entry** from the decay of `Θ_ξ(0, ·)` in the `ℓ¹` distance:
`‖Θ_ξ(a,b)‖ ≤ C₅ e^{1/(4c)} 𝒯_t(|a-b|_∞)` (copy of the private `k2d_theta_tail`,
`Step2K2.lean:78`; the floor `W^{-D}` of `stK2decay_holds` is not wanted here). -/
private theorem nkl_theta_tail {C₅ c : ℝ} (hC₅ : 0 < C₅) (hc : 0 < c) (hL : 3 ≤ L) {g t : ℝ} {ξ : ℂ}
    (hξ : ‖ξ‖ < 1)
    (H : ∀ x : Zd d L, ‖Theta d L g ξ 0 x‖ ≤
      C₅ * Bparam d L g t (zdistD d L x) * Real.exp (-c * (zdistD d L x : ℝ) / ellT L g t))
    (a b : Zd d L) :
    ‖Theta d L g ξ a b‖ ≤
      C₅ * Real.exp (1 / (4 * c)) * tailT d L g t ((zdistInf d L (a - b) : ℕ) : ℝ) := by
  have htr : Theta d L g ξ a b = Theta d L g ξ 0 (b - a) := by
    have h := Theta_apply_add_right_of_three_le (g := g) hL hξ 0 (b - a) a
    simpa using h
  rw [htr]
  refine (H (b - a)).trans ?_
  have hr : zdistInf d L (a - b) = zdistInf d L (b - a) := nkl_zdistInf_sub_comm a b
  rw [hr]
  set x := b - a with hx
  have hrρ : ((zdistInf d L x : ℕ) : ℝ) ≤ (zdistD d L x : ℝ) := by
    exact_mod_cast zdistInf_le_zdistD d L x
  have hr0 : (0 : ℝ) ≤ ((zdistInf d L x : ℕ) : ℝ) := Nat.cast_nonneg _
  have hℓ : 0 < ellT L g t := ellT_pos (by exact_mod_cast (by omega : 1 ≤ L))
  have hB : Bparam d L g t (zdistD d L x) ≤ BparamR d L g t ((zdistInf d L x : ℕ) : ℝ) := by
    rw [← BparamR_natCast]
    exact BparamR_antitone hr0 hrρ
  have hB0 : 0 ≤ Bparam d L g t (zdistD d L x) := by
    rw [← BparamR_natCast]
    exact BparamR_nonneg (Nat.cast_nonneg _)
  have hexp : Real.exp (-c * (zdistD d L x : ℝ) / ellT L g t) ≤
      Real.exp (1 / (4 * c)) *
        Real.exp (-Real.sqrt (((zdistInf d L x : ℕ) : ℝ) / ellT L g t)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 : ((zdistInf d L x : ℕ) : ℝ) / ellT L g t ≤ (zdistD d L x : ℝ) / ellT L g t :=
      div_le_div_of_nonneg_right hrρ hℓ.le
    have h2 := mul_le_mul_of_nonneg_left h1 hc.le
    have h3 := nkl_sqrt_le hc (((zdistInf d L x : ℕ) : ℝ) / ellT L g t)
      (div_nonneg hr0 hℓ.le)
    have e : -c * (zdistD d L x : ℝ) / ellT L g t = -(c * ((zdistD d L x : ℝ) / ellT L g t)) := by
      ring
    rw [e]
    linarith
  calc C₅ * Bparam d L g t (zdistD d L x) * Real.exp (-c * (zdistD d L x : ℝ) / ellT L g t)
      ≤ C₅ * BparamR d L g t ((zdistInf d L x : ℕ) : ℝ) *
          (Real.exp (1 / (4 * c)) *
            Real.exp (-Real.sqrt (((zdistInf d L x : ℕ) : ℝ) / ellT L g t))) := by
        have hBR0 : 0 ≤ BparamR d L g t ((zdistInf d L x : ℕ) : ℝ) := BparamR_nonneg hr0
        exact mul_le_mul (mul_le_mul_of_nonneg_left hB hC₅.le) hexp (Real.exp_pos _).le
          (mul_nonneg hC₅.le hBR0)
    _ = C₅ * Real.exp (1 / (4 * c)) * tailT d L g t ((zdistInf d L x : ℕ) : ℝ) := by
        unfold tailT
        ring

end Dist

/-! ### C. Convolution bounds for `S Θ` against the profiles -/

section Conv

variable {d L : ℕ} [NeZero L] {g t : ℝ}

/-- `|(SΘ)(a,b)| ≤ Q 𝒯_t(|a-b|_∞)` from `|Θ(x,b)| ≤ C₁ 𝒯_t(|x-b|_∞)`: `Q = C₁ C_s`. -/
private theorem nkl_SBTheta_tail (hL : 3 ≤ L) {ξ : ℂ} {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hΘ : ∀ a b : Zd d L, ‖Theta d L g ξ a b‖ ≤
      C₁ * tailT d L g t ((zdistInf d L (a - b) : ℕ) : ℝ)) (a b : Zd d L) :
    ‖(SB d L g * Theta d L g ξ) a b‖ ≤
      (C₁ * (2 ^ (d - 2) * Real.exp 1)) * tailT d L g t ((zdistInf d L (a - b) : ℕ) : ℝ) := by
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (by omega : 1 ≤ L)
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ x, ‖SB d L g a x * Theta d L g ξ x b‖
      ≤ ∑ x, ‖SB d L g a x‖ * ((C₁ * (2 ^ (d - 2) * Real.exp 1)) *
          tailT d L g t ((zdistInf d L (a - b) : ℕ) : ℝ)) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [norm_mul]
        by_cases hx : SB d L g a x = 0
        · simp [hx]
        · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have h1 : zdistInf d L (a - x) ≤ 1 := nkl_SB_support g hx
          have h2 := nkl_zdistInf_tri a x b
          have hsh := nkl_tailT_shift (d := d) (g := g) (t := t) hL1
            (Nat.cast_nonneg (zdistInf d L (a - b))) (Nat.cast_nonneg (zdistInf d L (x - b)))
            (by exact_mod_cast (by omega : zdistInf d L (a - b) ≤ zdistInf d L (x - b) + 1))
          calc ‖Theta d L g ξ x b‖ ≤ C₁ * tailT d L g t ((zdistInf d L (x - b) : ℕ) : ℝ) := hΘ x b
            _ ≤ C₁ * ((2 ^ (d - 2) * Real.exp 1) *
                tailT d L g t ((zdistInf d L (a - b) : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left hsh hC₁
            _ = _ := by ring
    _ = _ := by rw [← Finset.sum_mul, sum_norm_SB_row d L g hL, one_mul]

/-- Row sums of `|SΘ|`: `Σ_b |(SΘ)(a,b)| ≤ (1-u)⁻¹` from the same for `Θ`. -/
private theorem nkl_SBTheta_row (hL : 3 ≤ L) {ξ : ℂ} {c : ℝ}
    (hΘ : ∀ x : Zd d L, ∑ b, ‖Theta d L g ξ x b‖ ≤ c) (a : Zd d L) :
    ∑ b, ‖(SB d L g * Theta d L g ξ) a b‖ ≤ c := by
  have hc : 0 ≤ c := (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans
    (hΘ a)
  calc ∑ b, ‖(SB d L g * Theta d L g ξ) a b‖
      ≤ ∑ b, ∑ x, ‖SB d L g a x‖ * ‖Theta d L g ξ x b‖ := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [Matrix.mul_apply]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => (norm_mul _ _).le)
    _ = ∑ x, ‖SB d L g a x‖ * ∑ b, ‖Theta d L g ξ x b‖ := by
        rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
    _ ≤ ∑ x, ‖SB d L g a x‖ * c :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hΘ x) (norm_nonneg _)
    _ = c := by rw [← Finset.sum_mul, sum_norm_SB_row d L g hL, one_mul]

variable {ℓ W D : ℝ}

/-- **Bound 1 core**: `Σ_b |(SΘ)(a,b)| 𝒯̃(|b-a'|) ≤ (Q C_T + C_s)/(1-u) 𝒯̃(|a-a'|)`.
Near `b` use `|(SΘ)| ≤ Q 𝒯` and `(TTT2)`; far `b` use the row sum and `nkl_tailW_far`. -/
private theorem nkl_conv_P (hL : 3 ≤ L) (hW : 0 < W) (hℓ : 0 ≤ ℓ) {ξ : ℂ} {Q CT c : ℝ} (hQ : 0 ≤ Q) (hCT : 0 ≤ CT)
    (hTail : ∀ a b : Zd d L, ‖(SB d L g * Theta d L g ξ) a b‖ ≤
      Q * tailT d L g t ((zdistInf d L (a - b) : ℕ) : ℝ))
    (hRow : ∀ a : Zd d L, ∑ b, ‖(SB d L g * Theta d L g ξ) a b‖ ≤ c)
    (hTTT : ∀ a b : Zd d L, ∑ x : Zd d L, tailT d L g t ((zdistInf d L (a - x) : ℕ) : ℝ) *
        tailT d L g t ((zdistInf d L (x - b) : ℕ) : ℝ) ≤
      CT * tailT d L g t ((zdistInf d L (a - b) : ℕ) : ℝ)) (a a' : Zd d L) :
    ∑ b, ‖(SB d L g * Theta d L g ξ) a b‖ *
        tailW d L g t ℓ W D ((zdistInf d L (b - a') : ℕ) : ℝ) ≤
      (Q * CT + (2 ^ (d - 2) * Real.exp 1) * c) *
        tailW d L g t ℓ W D ((zdistInf d L (a - a') : ℕ) : ℝ) := by
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (by omega : 1 ≤ L)
  set P : ℝ → ℝ := tailW d L g t ℓ W D with hP
  have hdist : ∀ x : Zd d L, ((zdistInf d L x : ℕ) : ℝ) = 0 ∨ 1 ≤ ((zdistInf d L x : ℕ) : ℝ) := by
    intro x
    rcases Nat.eq_zero_or_pos (zdistInf d L x) with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  have hterm : ∀ b : Zd d L, ‖(SB d L g * Theta d L g ξ) a b‖ * P ((zdistInf d L (b - a') : ℕ) : ℝ) ≤
      Q * (tailT d L g t ((zdistInf d L (a - b) : ℕ) : ℝ) *
        tailT d L g t ((zdistInf d L (b - a') : ℕ) : ℝ)) +
      (2 ^ (d - 2) * Real.exp 1) * (‖(SB d L g * Theta d L g ξ) a b‖ *
        P ((zdistInf d L (a - a') : ℕ) : ℝ)) := by
    intro b
    set r : ℝ := ((zdistInf d L (b - a') : ℕ) : ℝ) with hr
    have hr0 : 0 ≤ r := Nat.cast_nonneg _
    have hCs := nkl_Cs_ge_one (d := d)
    have hnorm := norm_nonneg ((SB d L g * Theta d L g ξ) a b)
    by_cases hnear : 1 ≤ ℓ ∧ r ≤ ℓ ∧ W ^ (-D) ≤ tailT d L g t r
    · rw [hP, nkl_tailW_eq_of_near hnear.2.1 hnear.2.2]
      have h1 := mul_le_mul_of_nonneg_right (hTail a b) (tailT_nonneg (d := d) (L := L) (g := g)
        (t := t) hr0)
      have h2 : 0 ≤ (2 ^ (d - 2) * Real.exp 1) * (‖(SB d L g * Theta d L g ξ) a b‖ *
          P ((zdistInf d L (a - a') : ℕ) : ℝ)) := by
        have := (tailW_pos (d := d) (L := L) (g := g) (t := t) (ℓ := ℓ) (D := D) hW
          ((zdistInf d L (a - a') : ℕ) : ℝ)).le
        positivity
      nlinarith
    · have hfar := nkl_tailW_far (d := d) (L := L) (g := g) (t := t) hL1 hW hℓ hr0
        (Nat.cast_nonneg (zdistInf d L (a - a'))) (hdist _) hnear
      have h1 : 0 ≤ Q * (tailT d L g t ((zdistInf d L (a - b) : ℕ) : ℝ) *
          tailT d L g t ((zdistInf d L (b - a') : ℕ) : ℝ)) :=
        mul_nonneg hQ (mul_nonneg (tailT_nonneg (Nat.cast_nonneg _)) (tailT_nonneg (Nat.cast_nonneg _)))
      calc ‖(SB d L g * Theta d L g ξ) a b‖ * P r
          ≤ ‖(SB d L g * Theta d L g ξ) a b‖ *
            ((2 ^ (d - 2) * Real.exp 1) * P ((zdistInf d L (a - a') : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hfar hnorm
        _ = (2 ^ (d - 2) * Real.exp 1) * (‖(SB d L g * Theta d L g ξ) a b‖ *
            P ((zdistInf d L (a - a') : ℕ) : ℝ)) := by ring
        _ ≤ _ := le_add_of_nonneg_left h1
  have hT0 : tailT d L g t ((zdistInf d L (a - a') : ℕ) : ℝ) ≤ P ((zdistInf d L (a - a') : ℕ) : ℝ) :=
    nkl_tailT_le_tailW hℓ (Nat.cast_nonneg _)
  have hP0 : 0 ≤ P ((zdistInf d L (a - a') : ℕ) : ℝ) :=
    (tailW_pos (d := d) (L := L) (g := g) (t := t) (ℓ := ℓ) (D := D) hW _).le
  have hCs := nkl_Cs_ge_one (d := d)
  calc ∑ b, ‖(SB d L g * Theta d L g ξ) a b‖ * P ((zdistInf d L (b - a') : ℕ) : ℝ)
      ≤ ∑ b, (Q * (tailT d L g t ((zdistInf d L (a - b) : ℕ) : ℝ) *
        tailT d L g t ((zdistInf d L (b - a') : ℕ) : ℝ)) +
      (2 ^ (d - 2) * Real.exp 1) * (‖(SB d L g * Theta d L g ξ) a b‖ *
        P ((zdistInf d L (a - a') : ℕ) : ℝ))) := Finset.sum_le_sum fun b _ => hterm b
    _ = Q * ∑ b, (tailT d L g t ((zdistInf d L (a - b) : ℕ) : ℝ) *
        tailT d L g t ((zdistInf d L (b - a') : ℕ) : ℝ)) +
      (2 ^ (d - 2) * Real.exp 1) * ((∑ b, ‖(SB d L g * Theta d L g ξ) a b‖) *
        P ((zdistInf d L (a - a') : ℕ) : ℝ)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul]
    _ ≤ Q * (CT * tailT d L g t ((zdistInf d L (a - a') : ℕ) : ℝ)) +
      (2 ^ (d - 2) * Real.exp 1) * (c * P ((zdistInf d L (a - a') : ℕ) : ℝ)) := by
        refine add_le_add (mul_le_mul_of_nonneg_left (hTTT a a') hQ) ?_
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hRow a) hP0) (by positivity)
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hT0 (mul_nonneg hQ hCT)
        nlinarith

/-- **Bound 2 core, both factors near**: `Σ_{x,y} 𝒯(|x-a₁|) |S_{xy}| 𝒯(|a₀-y|) ≤ C_s C_T/(1-u) 𝒯(|a₀-a₁|)`
(`S_{xy} ≠ 0` forces `|x - y| ≤ 1`, hence `𝒯(|a₀-y|) ≤ C_s 𝒯(|a₀-x|)`, then `(TTT2)`). -/
private theorem nkl_conv_two (hL : 3 ≤ L) {CT : ℝ}
    (hTTT : ∀ a b : Zd d L, ∑ x : Zd d L, tailT d L g t ((zdistInf d L (a - x) : ℕ) : ℝ) *
        tailT d L g t ((zdistInf d L (x - b) : ℕ) : ℝ) ≤
      CT * tailT d L g t ((zdistInf d L (a - b) : ℕ) : ℝ)) (a₀ a₁ : Zd d L) :
    ∑ x : Zd d L, ∑ y : Zd d L, tailT d L g t ((zdistInf d L (x - a₁) : ℕ) : ℝ) *
        (‖SB d L g x y‖ * tailT d L g t ((zdistInf d L (a₀ - y) : ℕ) : ℝ)) ≤
      (2 ^ (d - 2) * Real.exp 1) * (CT * tailT d L g t ((zdistInf d L (a₀ - a₁) : ℕ) : ℝ)) := by
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (by omega : 1 ≤ L)
  have hterm : ∀ x y : Zd d L, tailT d L g t ((zdistInf d L (x - a₁) : ℕ) : ℝ) *
        (‖SB d L g x y‖ * tailT d L g t ((zdistInf d L (a₀ - y) : ℕ) : ℝ)) ≤
      (2 ^ (d - 2) * Real.exp 1) * (‖SB d L g x y‖ *
        (tailT d L g t ((zdistInf d L (a₀ - x) : ℕ) : ℝ) *
          tailT d L g t ((zdistInf d L (x - a₁) : ℕ) : ℝ))) := by
    intro x y
    by_cases hx : SB d L g x y = 0
    · simp [hx]
    · have h1 : zdistInf d L (x - y) ≤ 1 := nkl_SB_support g hx
      have h2 := nkl_zdistInf_tri a₀ y x
      rw [nkl_zdistInf_sub_comm y x] at h2
      have hsh := nkl_tailT_shift (d := d) (g := g) (t := t) hL1
        (Nat.cast_nonneg (zdistInf d L (a₀ - x))) (Nat.cast_nonneg (zdistInf d L (a₀ - y)))
        (by exact_mod_cast (by omega : zdistInf d L (a₀ - x) ≤ zdistInf d L (a₀ - y) + 1))
      have hT1 := tailT_nonneg (d := d) (L := L) (g := g) (t := t)
        (Nat.cast_nonneg (zdistInf d L (x - a₁)))
      have hn := norm_nonneg (SB d L g x y)
      calc tailT d L g t ((zdistInf d L (x - a₁) : ℕ) : ℝ) *
            (‖SB d L g x y‖ * tailT d L g t ((zdistInf d L (a₀ - y) : ℕ) : ℝ))
          ≤ tailT d L g t ((zdistInf d L (x - a₁) : ℕ) : ℝ) *
            (‖SB d L g x y‖ * ((2 ^ (d - 2) * Real.exp 1) *
              tailT d L g t ((zdistInf d L (a₀ - x) : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsh hn) hT1
        _ = _ := by ring
  calc ∑ x : Zd d L, ∑ y : Zd d L, tailT d L g t ((zdistInf d L (x - a₁) : ℕ) : ℝ) *
        (‖SB d L g x y‖ * tailT d L g t ((zdistInf d L (a₀ - y) : ℕ) : ℝ))
      ≤ ∑ x : Zd d L, ∑ y : Zd d L, (2 ^ (d - 2) * Real.exp 1) * (‖SB d L g x y‖ *
        (tailT d L g t ((zdistInf d L (a₀ - x) : ℕ) : ℝ) *
          tailT d L g t ((zdistInf d L (x - a₁) : ℕ) : ℝ))) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hterm x y
    _ = (2 ^ (d - 2) * Real.exp 1) * ∑ x : Zd d L, (tailT d L g t ((zdistInf d L (a₀ - x) : ℕ) : ℝ) *
          tailT d L g t ((zdistInf d L (x - a₁) : ℕ) : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.mul_sum, ← Finset.sum_mul, sum_norm_SB_row d L g hL, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hTTT a₀ a₁) (by positivity)

end Conv

/-! ### D. Ward's identity for the two-loops `𝓛^{(2)}` (entrywise) -/

section Ward

open scoped Matrix

variable {d L W : ℕ} [NeZero L]

/-- `Σ_{l ∈ [b]} Σ_{j ∈ [a]} ‖G_{lj}‖²` (block sums of squared entries). -/
private def nklQ (G : Matrix (Vtx d L W) (Vtx d L W) ℂ) (a b : Zd d L) : ℝ :=
  ∑ l : Vtx d L W, ∑ j : Vtx d L W, if l.1 = b then (if j.1 = a then ‖G l j‖ ^ 2 else 0) else 0

/-- The trace of a two-loop, entrywise: `⟨A E_a B E_b⟩ = Σ_{l,j} A_{lj} E_a(j) B_{jl} E_b(l)`. -/
private theorem nkl_trace2 (A B : Matrix (Vtx d L W) (Vtx d L W) ℂ) (a b : Zd d L) :
    Matrix.trace (A * Eblk d L W a * (B * Eblk d L W b)) =
      ∑ l : Vtx d L W, ∑ j : Vtx d L W,
        (A l j * (if j.1 = a then ((W : ℂ) ^ d)⁻¹ else 0)) *
          (B j l * (if l.1 = b then ((W : ℂ) ^ d)⁻¹ else 0)) := by
  unfold Matrix.trace
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Eblk, Matrix.mul_diagonal]

private theorem nkl_Gres_false {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (z : ℂ) : Gres H z false = (Gres H z true)ᴴ := by
  unfold Gres
  simp only [Bool.false_eq_true, ite_false, ite_true]
  rw [← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.conjTranspose_nonsing_inv]
  congr 1
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH.eq]
  rfl

/-- The product of two entries of `G(σ₁)`, `G(σ₂)` (in the order of a two-loop) is at most
`‖G_{lj}‖² + ‖G_{jl}‖²`, for every sign pattern. -/
private theorem nkl_entry_prod_le {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (z : ℂ) (s₀ s₁ : Bool) (l j : ι) :
    ‖Gres H z s₀ l j‖ * ‖Gres H z s₁ j l‖ ≤
      ‖Gres H z true l j‖ ^ 2 + ‖Gres H z true j l‖ ^ 2 := by
  have hx := norm_nonneg (Gres H z true l j)
  have hy := norm_nonneg (Gres H z true j l)
  have e1 : ‖Gres H z false l j‖ = ‖Gres H z true j l‖ := by
    rw [nkl_Gres_false hH, Matrix.conjTranspose_apply, norm_star]
  have e2 : ‖Gres H z false j l‖ = ‖Gres H z true l j‖ := by
    rw [nkl_Gres_false hH, Matrix.conjTranspose_apply, norm_star]
  cases s₀ <;> cases s₁ <;> (try simp only [e1, e2]) <;> nlinarith [sq_nonneg (‖Gres H z true l j‖ - ‖Gres H z true j l‖)]

/-- **`‖𝓛^{(2)}_{σ,(a,b)}‖ ≤ W^{-2d}(Q_{ab} + Q_{ba})`**, every sign pattern. -/
private theorem nkl_norm_loop2_le [NeZero W] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) (z : ℂ) (σ : Fin 2 → Bool) (a b : Zd d L) :
    ‖loopM d L W H z σ ![a, b]‖ ≤
      (((W : ℝ) ^ d)⁻¹) ^ 2 * (nklQ (Gres H z true) a b + nklQ (Gres H z true) b a) := by
  have hloop : loopM d L W H z σ ![a, b] =
      Matrix.trace (Gres H z (σ 0) * Eblk d L W a * (Gres H z (σ 1) * Eblk d L W b)) := by
    simp [loopM, List.ofFn_succ]
  rw [hloop, nkl_trace2]
  set G := Gres H z true with hG
  have hc : ‖((W : ℂ) ^ d)⁻¹‖ = ((W : ℝ) ^ d)⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_natCast]
  have hc0 : 0 ≤ ((W : ℝ) ^ d)⁻¹ := by positivity
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun l _ => norm_sum_le _ _).trans ?_)
  have hterm : ∀ l j : Vtx d L W,
      ‖(Gres H z (σ 0) l j * (if j.1 = a then ((W : ℂ) ^ d)⁻¹ else 0)) *
          (Gres H z (σ 1) j l * (if l.1 = b then ((W : ℂ) ^ d)⁻¹ else 0))‖ ≤
        (((W : ℝ) ^ d)⁻¹) ^ 2 *
          ((if l.1 = b then (if j.1 = a then ‖G l j‖ ^ 2 else 0) else 0) +
           (if l.1 = b then (if j.1 = a then ‖G j l‖ ^ 2 else 0) else 0)) := by
    intro l j
    by_cases hl : l.1 = b
    · by_cases hj : j.1 = a
      · simp only [hl, hj, ite_true]
        rw [norm_mul, norm_mul, norm_mul, hc]
        have := nkl_entry_prod_le hH z (σ 0) (σ 1) l j
        have h2 := mul_le_mul_of_nonneg_left this (sq_nonneg ((W : ℝ) ^ d)⁻¹)
        calc ‖Gres H z (σ 0) l j‖ * ((W ^ d : ℝ)⁻¹) * (‖Gres H z (σ 1) j l‖ * ((W ^ d : ℝ)⁻¹))
            = ((W ^ d : ℝ)⁻¹) ^ 2 * (‖Gres H z (σ 0) l j‖ * ‖Gres H z (σ 1) j l‖) := by ring
          _ ≤ _ := h2
      · simp [hj]
    · simp [hl]
  refine (Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun j _ => hterm l j).trans ?_
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, mul_add]
  have hswap : (∑ l : Vtx d L W, ∑ j : Vtx d L W,
      (if l.1 = b then (if j.1 = a then ‖G j l‖ ^ 2 else 0) else 0)) = nklQ G b a := by
    unfold nklQ
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h1 : j.1 = b <;> by_cases h2 : l.1 = a <;> simp [h1, h2]
  rw [hswap]
  rfl

private theorem nkl_sum_nklQ_snd (G : Matrix (Vtx d L W) (Vtx d L W) ℂ) (a : Zd d L) :
    ∑ b, nklQ G a b = ∑ l : Vtx d L W, ∑ j : Vtx d L W, if j.1 = a then ‖G l j‖ ^ 2 else 0 := by
  unfold nklQ
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j.1 = a <;> simp [hj]

private theorem nkl_sum_nklQ_fst (G : Matrix (Vtx d L W) (Vtx d L W) ℂ) (b : Zd d L) :
    ∑ a, nklQ G a b = ∑ l : Vtx d L W, ∑ j : Vtx d L W, if l.1 = b then ‖G l j‖ ^ 2 else 0 := by
  unfold nklQ
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hl : l.1 = b <;> simp [hl]

/-- `Σ_j ‖G_{lj}‖² = Im G_{ll}/η` (row mass; `G G† = (G - G†)/(2iη)`). -/
private theorem nkl_row_mass [NeZero W] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) (l : Vtx d L W) :
    ∑ j, ‖Gres H z true l j‖ ^ 2 = (Gres H z true l l).im / z.im := by
  have hu : IsUnit (H - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) :=
    Ind.isUnit_sub_smul_one_of_im_ne_zero hH hz.ne'
  have hu' : IsUnit (H - (starRingEnd ℂ) z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) :=
    Ind.isUnit_sub_smul_one_of_im_ne_zero hH (by simpa using hz.ne')
  have h := congrFun (congrFun (Ind.Gres_mul_conjTranspose hH hu hu' true) l) l
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sub_apply,
    smul_eq_mul, nkl_Gres_false hH z] at h
  have hsum : ∑ j, Gres H z true l j * star (Gres H z true l j) =
      ((∑ j, ‖Gres H z true l j‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; rfl
  rw [hsum, Complex.star_def, Complex.sub_conj] at h
  generalize (∑ j, ‖Gres H z true l j‖ ^ 2 : ℝ) = S at h ⊢
  have h2 := congrArg Complex.im h
  simp at h2
  rw [eq_div_iff hz.ne']
  linarith

/-- `Σ_l ‖G_{lj}‖² = Im G_{jj}/η` (column mass; `G† G = (G - G†)/(2iη)`). -/
private theorem nkl_col_mass [NeZero W] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) (j : Vtx d L W) :
    ∑ l, ‖Gres H z true l j‖ ^ 2 = (Gres H z true j j).im / z.im := by
  have hu : IsUnit (H - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) :=
    Ind.isUnit_sub_smul_one_of_im_ne_zero hH hz.ne'
  have hu' : IsUnit (H - (starRingEnd ℂ) z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) :=
    Ind.isUnit_sub_smul_one_of_im_ne_zero hH (by simpa using hz.ne')
  have h := congrFun (congrFun (Ind.Gres_mul_conjTranspose hH hu hu' false) j) j
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sub_apply,
    smul_eq_mul, nkl_Gres_false hH z, star_star] at h
  have hsum : ∑ l, star (Gres H z true l j) * Gres H z true l j =
      ((∑ l, ‖Gres H z true l j‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; rfl
  rw [hsum, Complex.star_def, Complex.sub_conj] at h
  generalize (∑ l, ‖Gres H z true l j‖ ^ 2 : ℝ) = S at h ⊢
  have h2 := congrArg Complex.im h
  simp at h2
  rw [eq_div_iff hz.ne']
  linarith

private theorem nkl_block_const (a : Zd d L) (B : ℝ) :
    ∑ j : Vtx d L W, (if j.1 = a then B else 0) = (W : ℝ) ^ d * B := by
  rw [Fintype.sum_prod_type]
  have hx : ∀ x : Zd d L, (∑ _y : Fin (W ^ d), if x = a then B else 0) =
      if x = a then (W : ℝ) ^ d * B else 0 := by
    intro x; by_cases h : x = a <;> simp [h]
  simp only [hx, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- **Ward bounds for `𝓛^{(2)}`** (every sign pattern `σ`): if `Im G_{xx} ≤ B₀` for all `x`, then
both marginals of `‖𝓛^{(2)}_{σ,(·,·)}‖` are at most `2 W^{-d} B₀/Im z`. -/
private theorem nkl_ward_L [NeZero W] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) {B0 : ℝ}
    (hdiag : ∀ x, (Gres H z true x x).im ≤ B0) (σ : Fin 2 → Bool) :
    (∀ a₁ : Zd d L, ∑ x, ‖loopM d L W H z σ ![x, a₁]‖ ≤
        2 * (((W : ℝ) ^ d)⁻¹ * (B0 / z.im))) ∧
      (∀ a₀ : Zd d L, ∑ y, ‖loopM d L W H z σ ![a₀, y]‖ ≤
        2 * (((W : ℝ) ^ d)⁻¹ * (B0 / z.im))) := by
  set G := Gres H z true with hG
  have hWd : (0 : ℝ) < (W : ℝ) ^ d := by
    have : (0 : ℝ) < (W : ℝ) := Nat.cast_pos.2 (NeZero.pos W)
    positivity
  have hRbound : ∀ a : Zd d L, ∑ l : Vtx d L W, ∑ j : Vtx d L W,
      (if l.1 = a then ‖G l j‖ ^ 2 else 0) ≤ (W : ℝ) ^ d * (B0 / z.im) := by
    intro a
    rw [← nkl_block_const (L := L) (W := W) a (B0 / z.im)]
    refine Finset.sum_le_sum fun l _ => ?_
    by_cases hl : l.1 = a
    · simp only [hl, ite_true]
      rw [nkl_row_mass hH hz l]
      exact div_le_div_of_nonneg_right (hdiag l) hz.le
    · simp [hl]
  have hCbound : ∀ a : Zd d L, ∑ l : Vtx d L W, ∑ j : Vtx d L W,
      (if j.1 = a then ‖G l j‖ ^ 2 else 0) ≤ (W : ℝ) ^ d * (B0 / z.im) := by
    intro a
    rw [Finset.sum_comm, ← nkl_block_const (L := L) (W := W) a (B0 / z.im)]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : j.1 = a
    · simp only [hj, ite_true]
      rw [nkl_col_mass hH hz j]
      exact div_le_div_of_nonneg_right (hdiag j) hz.le
    · simp [hj]
  have hc : (((W : ℝ) ^ d)⁻¹) ^ 2 * ((W : ℝ) ^ d * (B0 / z.im)) =
      ((W : ℝ) ^ d)⁻¹ * (B0 / z.im) := by
    field_simp
  constructor
  · intro a₁
    calc ∑ x, ‖loopM d L W H z σ ![x, a₁]‖
        ≤ ∑ x, (((W : ℝ) ^ d)⁻¹) ^ 2 * (nklQ G x a₁ + nklQ G a₁ x) :=
          Finset.sum_le_sum fun x _ => nkl_norm_loop2_le hH z σ x a₁
      _ = (((W : ℝ) ^ d)⁻¹) ^ 2 * (∑ x, nklQ G x a₁ + ∑ x, nklQ G a₁ x) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ (((W : ℝ) ^ d)⁻¹) ^ 2 * ((W : ℝ) ^ d * (B0 / z.im) + (W : ℝ) ^ d * (B0 / z.im)) := by
          rw [nkl_sum_nklQ_fst, nkl_sum_nklQ_snd]
          exact mul_le_mul_of_nonneg_left (add_le_add (hRbound a₁) (hCbound a₁)) (by positivity)
      _ = _ := by rw [← two_mul, ← mul_assoc, mul_comm _ (2 : ℝ), mul_assoc, hc]
  · intro a₀
    calc ∑ y, ‖loopM d L W H z σ ![a₀, y]‖
        ≤ ∑ y, (((W : ℝ) ^ d)⁻¹) ^ 2 * (nklQ G a₀ y + nklQ G y a₀) :=
          Finset.sum_le_sum fun y _ => nkl_norm_loop2_le hH z σ a₀ y
      _ = (((W : ℝ) ^ d)⁻¹) ^ 2 * (∑ y, nklQ G a₀ y + ∑ y, nklQ G y a₀) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ (((W : ℝ) ^ d)⁻¹) ^ 2 * ((W : ℝ) ^ d * (B0 / z.im) + (W : ℝ) ^ d * (B0 / z.im)) := by
          rw [nkl_sum_nklQ_fst, nkl_sum_nklQ_snd]
          exact mul_le_mul_of_nonneg_left (add_le_add (hCbound a₀) (hRbound a₀)) (by positivity)
      _ = _ := by rw [← two_mul, ← mul_assoc, mul_comm _ (2 : ℝ), mul_assoc, hc]

end Ward

/-! ### E. Ward bounds for `𝓛 - 𝒦` of the model (`STLKM`) -/

section WardLKM

open scoped Matrix

variable {d : ℕ} (sz : Sizes d)

/-- `𝒦^{(2)} = W^{-d} m₁ m₂ Θ_{u m₁ m₂}(a₁, a₂)` for the model's `STKloop` (the `n = 2` tree formula). -/
private theorem nkl_STKloop_eq (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STKloop sz n E u σ a =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (mSigma E (σ 0) * mSigma E (σ 1)) *
        Theta d (sz.L n) (sz.lam n) ((u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) (a 0) (a 1) := by
  have h2 : KLloopOf d (sz.L n) σ a = ⟨[σ 0, σ 1], [a 0, a 1]⟩ := by
    simp [KLloopOf, List.ofFn_succ]
  unfold STKloop
  rw [h2, KLK_two]

/-- `Σ` of `‖𝒦^{(2)}‖` in either argument is at most `W^{-d} (1-u)⁻¹`. -/
private theorem nkl_ward_K (n : ℕ) {E u : ℝ} (hE : |E| ≤ 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (σ : Fin 2 → Bool) :
    (∀ a₁ : Zd d (sz.L n), ∑ x, ‖STKloop sz n E u σ ![x, a₁]‖ ≤
        ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) * (1 - u)⁻¹) ∧
      (∀ a₀ : Zd d (sz.L n), ∑ y, ‖STKloop sz n E u σ ![a₀, y]‖ ≤
        ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) * (1 - u)⁻¹) := by
  have hL : 3 ≤ sz.L n := sz.three_le_L n
  have hm : ‖mSigma E (σ 0) * mSigma E (σ 1)‖ = 1 := by
    rw [norm_mul, norm_mSigma hE, norm_mSigma hE, mul_one]
  have hξ : ‖(u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))‖ < 1 :=
    norm_mul_mSigma_lt_one hE hu0 hu1 (σ 0) (σ 1)
  have hnorm : ∀ a : Fin 2 → Zd d (sz.L n), ‖STKloop sz n E u σ a‖ =
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ‖Theta d (sz.L n) (sz.lam n)
        ((u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) (a 0) (a 1)‖ := by
    intro a
    rw [nkl_STKloop_eq, norm_mul, norm_mul, hm, mul_one, norm_inv, norm_pow, Complex.norm_natCast]
  have hrow := fun a : Zd d (sz.L n) => sum_norm_Theta_row_le (d := d) (g := sz.lam n) hL hu0 hu1 hm a
  constructor
  · intro a₁
    calc ∑ x, ‖STKloop sz n E u σ ![x, a₁]‖
        = ∑ x, (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ‖Theta d (sz.L n) (sz.lam n)
            ((u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) a₁ x‖ := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [hnorm]
          have := Theta_transpose_of_three_le (d := d) (g := sz.lam n) hL hξ
          have h3 := congrFun (congrFun this a₁) x
          simp only [Matrix.transpose_apply] at h3
          simp [h3]
      _ = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ∑ x, ‖Theta d (sz.L n) (sz.lam n)
            ((u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) a₁ x‖ := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hrow a₁) (by positivity)
  · intro a₀
    calc ∑ y, ‖STKloop sz n E u σ ![a₀, y]‖
        = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ∑ y, ‖Theta d (sz.L n) (sz.lam n)
            ((u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) a₀ y‖ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [hnorm]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hrow a₀) (by positivity)

private theorem nkl_gres_blockMat_true {d L W : ℕ} [NeZero L] [NeZero W]
    (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) (x y : Vtx d L W) :
    Gres (blockMat d L W H) z true x y =
      Gres H z true ((splitEquiv d L W).symm x) ((splitEquiv d L W).symm y) := by
  unfold Gres blockMat
  simp only [ite_true]
  have e1 : H.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm -
        z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) =
      (H - z • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)).submatrix (splitEquiv d L W).symm
        (splitEquiv d L W).symm := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply]
  rw [e1, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.inv_submatrix_equiv]
  rfl

/-- **Ward bounds for `𝓛 - 𝒦`** (every `σ`): for Hermitian `H` with `‖G_u - M‖_max ≤ κ/2`
(`|E| ≤ 2 - κ`), both marginals of `‖(𝓛-𝒦)^{(2)}_{u,σ,(·,·)}‖` are at most
`5 W^{-d} (1-u)⁻¹`. -/
private theorem nkl_ward_LKM (n : ℕ) {E u κ : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (hu0 : 0 ≤ u)
    (hu1 : u < 1) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hH : H.IsHermitian) (hGM : ∀ x y, ‖STGMM sz n E u H x y‖ ≤ κ / 2) (σ : Fin 2 → Bool) :
    (∀ a₁ : Zd d (sz.L n), ∑ x, ‖STLKM sz n E u H σ ![x, a₁]‖ ≤
        5 * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 - u)⁻¹)) ∧
      (∀ a₀ : Zd d (sz.L n), ∑ y, ‖STLKM sz n E u H σ ![a₀, y]‖ ≤
        5 * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 - u)⁻¹)) := by
  have hE2 : |E| ≤ 2 := by linarith
  have hm := Ind.half_le_mE_im hκ.le hE
  have hmpos : 0 < (mE E).im := lt_of_lt_of_le (by linarith) hm
  have hv : 0 < 1 - u := by linarith
  have hz : 0 < (zt E u).im := by rw [zt_im]; positivity
  set Hb := blockMat d (sz.L n) (sz.W n) H with hHb
  have hHbH : Hb.IsHermitian := Matrix.IsHermitian.submatrix hH _
  have hdiag : ∀ x : Vtx d (sz.L n) (sz.W n),
      (Gres Hb (zt E u) true x x).im ≤ (mE E).im + κ / 2 := by
    intro x
    rw [hHb, nkl_gres_blockMat_true]
    have h1 := hGM ((splitEquiv d (sz.L n) (sz.W n)).symm x) ((splitEquiv d (sz.L n) (sz.W n)).symm x)
    have h2 : (STGMM sz n E u H ((splitEquiv d (sz.L n) (sz.W n)).symm x)
        ((splitEquiv d (sz.L n) (sz.W n)).symm x)).im =
        (Gres H (zt E u) true ((splitEquiv d (sz.L n) (sz.W n)).symm x)
          ((splitEquiv d (sz.L n) (sz.W n)).symm x)).im - (mE E).im := by
      simp [STGMM]
    have h3 := Complex.abs_im_le_norm (STGMM sz n E u H ((splitEquiv d (sz.L n) (sz.W n)).symm x)
        ((splitEquiv d (sz.L n) (sz.W n)).symm x))
    have h4 := le_abs_self (STGMM sz n E u H ((splitEquiv d (sz.L n) (sz.W n)).symm x)
        ((splitEquiv d (sz.L n) (sz.W n)).symm x)).im
    linarith
  obtain ⟨hLa, hLb⟩ := nkl_ward_L (W := sz.W n) (L := sz.L n) hHbH hz hdiag σ
  obtain ⟨hKa, hKb⟩ := nkl_ward_K sz n hE2 hu0 hu1 σ
  have hcore : 2 * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((mE E).im + κ / 2) / (zt E u).im)) ≤
      4 * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 - u)⁻¹) := by
    rw [zt_im]
    have : ((mE E).im + κ / 2) / ((1 - u) * (mE E).im) ≤ 2 * (1 - u)⁻¹ := by
      rw [div_le_iff₀ (by positivity)]
      have : 2 * (1 - u)⁻¹ * ((1 - u) * (mE E).im) = 2 * (mE E).im := by field_simp
      rw [this]; linarith
    have hW0 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
    nlinarith
  have hsplit : ∀ a : Fin 2 → Zd d (sz.L n), ‖STLKM sz n E u H σ a‖ ≤
      ‖loopM d (sz.L n) (sz.W n) Hb (zt E u) σ a‖ + ‖STKloop sz n E u σ a‖ :=
    fun a => norm_sub_le _ _
  constructor
  · intro a₁
    calc ∑ x, ‖STLKM sz n E u H σ ![x, a₁]‖
        ≤ ∑ x, (‖loopM d (sz.L n) (sz.W n) Hb (zt E u) σ ![x, a₁]‖ + ‖STKloop sz n E u σ ![x, a₁]‖) :=
          Finset.sum_le_sum fun x _ => hsplit _
      _ = _ := Finset.sum_add_distrib
      _ ≤ _ := by
          have := hLa a₁
          have := hKa a₁
          linarith
  · intro a₀
    calc ∑ y, ‖STLKM sz n E u H σ ![a₀, y]‖
        ≤ ∑ y, (‖loopM d (sz.L n) (sz.W n) Hb (zt E u) σ ![a₀, y]‖ + ‖STKloop sz n E u σ ![a₀, y]‖) :=
          Finset.sum_le_sum fun y _ => hsplit _
      _ = _ := Finset.sum_add_distrib
      _ ≤ _ := by
          have := hLb a₀
          have := hKb a₀
          linarith

end WardLKM

/-! ### F. The two bounds, abstractly -/

section Assembly

variable {d L : ℕ} [NeZero L] {g t : ℝ}

omit [NeZero L] in
private theorem nkl_dist_cases (x : Zd d L) :
    ((zdistInf d L x : ℕ) : ℝ) = 0 ∨ 1 ≤ ((zdistInf d L x : ℕ) : ℝ) := by
  rcases Nat.eq_zero_or_pos (zdistInf d L x) with h | h
  · left; exact_mod_cast h
  · right; exact_mod_cast h

/-- **Bound 2, abstractly** (`3_5:626-654`): with `A_x = |F(x,a₁)|`, `B_y = |F(a₀,y)|`,
`A_x ≤ J W^{-d} 𝒯̃(|x-a₁|)`, `B_y ≤ J W^{-d} 𝒯̃(|a₀-y|)` and the marginal sums bounded by `Σ̄`:
`Σ_{x,y} A_x |S_{xy}| B_y ≤ 2 J W^{-d} C_s 𝒯̃(|a₀-a₁|) Σ̄ + 1_{ℓ≥1} (J W^{-d})² C_s C_T' 𝒯(|a₀-a₁|)`. -/
private theorem nkl_bound2 (hL : 3 ≤ L) {ℓ Wr D CT J cW Sig : ℝ} (hW : 0 < Wr) (hℓ : 0 ≤ ℓ)
    (hJ : 0 ≤ J) (hcW : 0 ≤ cW) (A B : Zd d L → ℝ) (hA0 : ∀ x, 0 ≤ A x) (hB0 : ∀ y, 0 ≤ B y)
    (a₀ a₁ : Zd d L)
    (hA : ∀ x, A x ≤ J * (cW * tailW d L g t ℓ Wr D ((zdistInf d L (x - a₁) : ℕ) : ℝ)))
    (hB : ∀ y, B y ≤ J * (cW * tailW d L g t ℓ Wr D ((zdistInf d L (a₀ - y) : ℕ) : ℝ)))
    (hSumA : ∑ x, A x ≤ Sig) (hSumB : ∑ y, B y ≤ Sig)
    (hTTT : ∀ a b : Zd d L, ∑ x : Zd d L, tailT d L g t ((zdistInf d L (a - x) : ℕ) : ℝ) *
        tailT d L g t ((zdistInf d L (x - b) : ℕ) : ℝ) ≤
      CT * tailT d L g t ((zdistInf d L (a - b) : ℕ) : ℝ)) :
    ∑ x, ∑ y, A x * ‖SB d L g x y‖ * B y ≤
      2 * (J * cW * (2 ^ (d - 2) * Real.exp 1) *
          tailW d L g t ℓ Wr D ((zdistInf d L (a₀ - a₁) : ℕ) : ℝ)) * Sig +
        (if 1 ≤ ℓ then (J * cW) ^ 2 * ((2 ^ (d - 2) * Real.exp 1) *
          (CT * tailT d L g t ((zdistInf d L (a₀ - a₁) : ℕ) : ℝ))) else 0) := by
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (by omega : 1 ≤ L)
  have hCs := nkl_Cs_ge_one (d := d)
  set Cs : ℝ := 2 ^ (d - 2) * Real.exp 1 with hCsdef
  set P : ℝ → ℝ := tailW d L g t ℓ Wr D with hP
  set Ps : ℝ := P ((zdistInf d L (a₀ - a₁) : ℕ) : ℝ) with hPs
  have hP0 : ∀ r, 0 ≤ P r := fun r => (tailW_pos (d := d) (L := L) (g := g) (t := t) (ℓ := ℓ)
    (D := D) hW r).le
  have hPs0 : 0 ≤ Ps := hP0 _
  set K0 : ℝ := J * cW * Cs * Ps with hK0
  have hK0nn : 0 ≤ K0 := by positivity
  set T3 : Zd d L → Zd d L → ℝ := fun x y =>
    if 1 ≤ ℓ then (J * cW) ^ 2 * (tailT d L g t ((zdistInf d L (x - a₁) : ℕ) : ℝ) *
      (‖SB d L g x y‖ * tailT d L g t ((zdistInf d L (a₀ - y) : ℕ) : ℝ))) else 0 with hT3
  have hterm : ∀ x y : Zd d L, A x * ‖SB d L g x y‖ * B y ≤
      A x * ‖SB d L g x y‖ * K0 + K0 * ‖SB d L g x y‖ * B y + T3 x y := by
    intro x y
    have hn := norm_nonneg (SB d L g x y)
    have hT3nn : 0 ≤ T3 x y := by
      simp only [hT3]
      split_ifs
      · exact mul_nonneg (sq_nonneg _) (mul_nonneg (tailT_nonneg (Nat.cast_nonneg _))
          (mul_nonneg hn (tailT_nonneg (Nat.cast_nonneg _))))
      · exact le_rfl
    by_cases hNy : 1 ≤ ℓ ∧ ((zdistInf d L (a₀ - y) : ℕ) : ℝ) ≤ ℓ ∧
        Wr ^ (-D) ≤ tailT d L g t ((zdistInf d L (a₀ - y) : ℕ) : ℝ)
    · by_cases hNx : 1 ≤ ℓ ∧ ((zdistInf d L (x - a₁) : ℕ) : ℝ) ≤ ℓ ∧
          Wr ^ (-D) ≤ tailT d L g t ((zdistInf d L (x - a₁) : ℕ) : ℝ)
      · -- both near
        have hAx := hA x
        have hBy := hB y
        have eX : P ((zdistInf d L (x - a₁) : ℕ) : ℝ) =
            tailT d L g t ((zdistInf d L (x - a₁) : ℕ) : ℝ) := by
          rw [hP]; exact nkl_tailW_eq_of_near hNx.2.1 hNx.2.2
        have eY : P ((zdistInf d L (a₀ - y) : ℕ) : ℝ) =
            tailT d L g t ((zdistInf d L (a₀ - y) : ℕ) : ℝ) := by
          rw [hP]; exact nkl_tailW_eq_of_near hNy.2.1 hNy.2.2
        rw [eX] at hAx
        rw [eY] at hBy
        have h1 : A x * B y ≤ (J * cW) ^ 2 * (tailT d L g t ((zdistInf d L (x - a₁) : ℕ) : ℝ) *
            tailT d L g t ((zdistInf d L (a₀ - y) : ℕ) : ℝ)) := by
          have := mul_le_mul hAx hBy (hB0 y) (by
            have := tailT_nonneg (d := d) (L := L) (g := g) (t := t)
              (Nat.cast_nonneg (zdistInf d L (x - a₁)))
            positivity)
          calc A x * B y ≤ _ := this
            _ = _ := by ring
        have hT3eq : T3 x y = (J * cW) ^ 2 * (tailT d L g t ((zdistInf d L (x - a₁) : ℕ) : ℝ) *
            (‖SB d L g x y‖ * tailT d L g t ((zdistInf d L (a₀ - y) : ℕ) : ℝ))) := by
          simp only [hT3, hNx.1, ite_true]
        have h2 : 0 ≤ A x * ‖SB d L g x y‖ * K0 := by have := hA0 x; positivity
        have h3 : 0 ≤ K0 * ‖SB d L g x y‖ * B y := by have := hB0 y; positivity
        calc A x * ‖SB d L g x y‖ * B y = ‖SB d L g x y‖ * (A x * B y) := by ring
          _ ≤ ‖SB d L g x y‖ * ((J * cW) ^ 2 * (tailT d L g t ((zdistInf d L (x - a₁) : ℕ) : ℝ) *
            tailT d L g t ((zdistInf d L (a₀ - y) : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left h1 hn
          _ = T3 x y := by rw [hT3eq]; ring
          _ ≤ _ := by linarith
      · -- y near, x far
        have hfar := nkl_tailW_far (d := d) (L := L) (g := g) (t := t) (ℓ := ℓ) (W := Wr) (D := D)
          hL1 hW hℓ (Nat.cast_nonneg (zdistInf d L (x - a₁)))
          (Nat.cast_nonneg (zdistInf d L (a₀ - a₁))) (nkl_dist_cases _) hNx
        have hAx : A x ≤ K0 := by
          calc A x ≤ J * (cW * P ((zdistInf d L (x - a₁) : ℕ) : ℝ)) := hA x
            _ ≤ J * (cW * (Cs * Ps)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfar hcW) hJ
            _ = K0 := by rw [hK0]; ring
        have h2 : 0 ≤ A x * ‖SB d L g x y‖ * K0 := by have := hA0 x; positivity
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAx hn) (hB0 y)
        calc A x * ‖SB d L g x y‖ * B y ≤ K0 * ‖SB d L g x y‖ * B y := this
          _ ≤ _ := by linarith
    · -- y far
      have hfar := nkl_tailW_far (d := d) (L := L) (g := g) (t := t) (ℓ := ℓ) (W := Wr) (D := D)
        hL1 hW hℓ (Nat.cast_nonneg (zdistInf d L (a₀ - y)))
        (Nat.cast_nonneg (zdistInf d L (a₀ - a₁))) (nkl_dist_cases _) hNy
      have hBy : B y ≤ K0 := by
        calc B y ≤ J * (cW * P ((zdistInf d L (a₀ - y) : ℕ) : ℝ)) := hB y
          _ ≤ J * (cW * (Cs * Ps)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfar hcW) hJ
          _ = K0 := by rw [hK0]; ring
      have h3 : 0 ≤ K0 * ‖SB d L g x y‖ * B y := by have := hB0 y; positivity
      have := mul_le_mul_of_nonneg_left hBy (mul_nonneg (hA0 x) hn)
      calc A x * ‖SB d L g x y‖ * B y ≤ A x * ‖SB d L g x y‖ * K0 := by linarith
        _ ≤ _ := by linarith
  have hsum1 : ∑ x, ∑ y, A x * ‖SB d L g x y‖ * K0 ≤ K0 * Sig := by
    calc ∑ x, ∑ y, A x * ‖SB d L g x y‖ * K0 = K0 * ∑ x, A x := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          calc ∑ y, A x * ‖SB d L g x y‖ * K0 = A x * K0 * ∑ y, ‖SB d L g x y‖ := by
                rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
            _ = K0 * A x := by rw [sum_norm_SB_row d L g hL]; ring
      _ ≤ K0 * Sig := mul_le_mul_of_nonneg_left hSumA hK0nn
  have hsum2 : ∑ x, ∑ y, K0 * ‖SB d L g x y‖ * B y ≤ K0 * Sig := by
    calc ∑ x, ∑ y, K0 * ‖SB d L g x y‖ * B y = ∑ y, ∑ x, K0 * ‖SB d L g x y‖ * B y :=
          Finset.sum_comm
      _ = K0 * ∑ y, B y := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          have hsymm : ∀ x, ‖SB d L g x y‖ = ‖SB d L g y x‖ := fun x => by
            have h := congrFun (congrFun (SB_transpose d L g) x) y
            simp only [Matrix.transpose_apply] at h
            rw [h]
          calc ∑ x, K0 * ‖SB d L g x y‖ * B y = K0 * B y * ∑ x, ‖SB d L g y x‖ := by
                rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by rw [hsymm]; ring
            _ = K0 * B y := by rw [sum_norm_SB_row d L g hL]; ring
      _ ≤ K0 * Sig := mul_le_mul_of_nonneg_left hSumB hK0nn
  have hsum3 : ∑ x, ∑ y, T3 x y ≤ (if 1 ≤ ℓ then (J * cW) ^ 2 * (Cs *
      (CT * tailT d L g t ((zdistInf d L (a₀ - a₁) : ℕ) : ℝ))) else 0) := by
    by_cases h1 : 1 ≤ ℓ
    · have e : ∑ x, ∑ y, T3 x y = (J * cW) ^ 2 * ∑ x, ∑ y, (tailT d L g t
          ((zdistInf d L (x - a₁) : ℕ) : ℝ) * (‖SB d L g x y‖ *
            tailT d L g t ((zdistInf d L (a₀ - y) : ℕ) : ℝ))) := by
        simp only [hT3, ite_true, h1]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
      rw [e]
      simp only [h1, ite_true]
      exact mul_le_mul_of_nonneg_left (nkl_conv_two hL hTTT a₀ a₁) (sq_nonneg _)
    · simp [hT3, h1]
  calc ∑ x, ∑ y, A x * ‖SB d L g x y‖ * B y
      ≤ ∑ x, ∑ y, (A x * ‖SB d L g x y‖ * K0 + K0 * ‖SB d L g x y‖ * B y + T3 x y) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hterm x y
    _ = ∑ x, ∑ y, A x * ‖SB d L g x y‖ * K0 + ∑ x, ∑ y, K0 * ‖SB d L g x y‖ * B y +
          ∑ x, ∑ y, T3 x y := by
        simp only [Finset.sum_add_distrib]
    _ ≤ _ := by
        have : K0 * Sig + K0 * Sig = 2 * (J * cW * Cs * Ps) * Sig := by rw [hK0]; ring
        linarith

end Assembly

/-! ### G. The pin `STNewKLK` -/

private theorem nkl_STmsig_eq (E : ℝ) (s : Bool) : STmsig E s = mSigma E s := rfl

/-- `lem:newKLK` with the explicit `δ₀ = κ/2`.
Constants: `C = 2 (C₁ C_s C_T + C_s) + 10 C_s + C_s C_T`, with `C₁ = C₅ e^{1/(4c)}`
(`Prop5Decay d 𝔡⁻¹`), `C_s = 2^{d-2} e` (the shift of `𝒯`), `C_T` (`(TTT2)`, `ekPropTInf_holds`);
all depend only on `(d, 𝔡)`. -/
private theorem nkl_at (d : ℕ) (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) :
    ∃ C : ℝ, 0 < C ∧ STNewKLKAt d κ 𝔡 C (κ / 2) := by
  obtain ⟨C₅, hC₅, c, hc, H5⟩ := prop5Decay_holds d 𝔡⁻¹ hd (inv_pos.2 h𝔡)
  obtain ⟨CT, hCT, HT⟩ := ekPropTInf_holds d hd
  have hCs := nkl_Cs_ge_one (d := d)
  set C₁ : ℝ := C₅ * Real.exp (1 / (4 * c)) with hC₁
  set Cs : ℝ := 2 ^ (d - 2) * Real.exp 1 with hCsdef
  have hC₁0 : 0 < C₁ := by positivity
  refine ⟨2 * (C₁ * Cs * CT + Cs) + 10 * Cs + Cs * CT, by positivity, ?_⟩
  intro sz n E u D ℓ hlam hlam' hE hu0 hu1 hD hℓ0 hℓL H hH hGM σ a
  have hE2 : |E| ≤ 2 := by linarith
  have hL : 3 ≤ sz.L n := sz.three_le_L n
  have hv : 0 < 1 - u := by linarith
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := Nat.cast_pos.2 (sz.W_pos n)
  set Wr : ℝ := ((sz.W n : ℕ) : ℝ) with hWr
  set J : ℝ := STJhatM sz n E D ℓ u H with hJ
  set g : ℝ := sz.lam n with hg
  set P : ℝ → ℝ := tailW d (sz.L n) g u ℓ Wr D with hP
  have hP0 : ∀ r, 0 < P r := fun r => tailW_pos hWpos r
  have hprof : ∀ x y : Zd d (sz.L n), STprof sz n u D ℓ x y =
      (Wr ^ d)⁻¹ * P ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) := fun x y => rfl
  have hprof0 : ∀ x y : Zd d (sz.L n), 0 < STprof sz n u D ℓ x y := fun x y => by
    rw [hprof]; have := hP0 ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ); positivity
  have hF : ∀ (σ' : Fin 2 → Bool) (a' : Fin 2 → Zd d (sz.L n)),
      ‖STLKM sz n E u H σ' a'‖ ≤ J * STprof sz n u D ℓ (a' 0) (a' 1) := by
    intro σ' a'
    have h := Finset.le_sup' (fun p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) =>
      ‖STLKM sz n E u H p.1 p.2‖ / STprof sz n u D ℓ (p.2 0) (p.2 1)) (Finset.mem_univ (σ', a'))
    rw [div_le_iff₀ (hprof0 _ _)] at h
    exact h
  have hJ0 : 0 ≤ J := by
    have h := hF σ (fun _ => 0)
    have h1 := norm_nonneg (STLKM sz n E u H σ (fun _ => 0))
    have h2 := hprof0 (0 : Zd d (sz.L n)) 0
    by_contra hneg
    push Not at hneg
    nlinarith
  -- the propagator
  have hm : ‖mSigma E (σ 0) * mSigma E (σ 1)‖ = 1 := by
    rw [norm_mul, norm_mSigma hE2, norm_mSigma hE2, mul_one]
  have hξ : ‖(u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))‖ < 1 :=
    norm_mul_mSigma_lt_one hE2 hu0 hu1 (σ 0) (σ 1)
  have hΘ : ∀ x y : Zd d (sz.L n),
      ‖Theta d (sz.L n) g ((u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) x y‖ ≤
        C₁ * tailT d (sz.L n) g u ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) :=
    nkl_theta_tail hC₅ hc hL hξ
      (fun x => H5 (sz.L n) hL g hlam hlam' u hu0 hu1 (mE E) (norm_mE hE2) (σ 0) (σ 1) x)
  have hrowΘ : ∀ x : Zd d (sz.L n),
      ∑ b, ‖Theta d (sz.L n) g ((u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) x b‖ ≤ (1 - u)⁻¹ :=
    fun x => sum_norm_Theta_row_le hL hu0 hu1 hm x
  have hSΘ := nkl_SBTheta_tail (t := u) hL hC₁0.le hΘ
  have hrowSΘ := nkl_SBTheta_row hL hrowΘ
  have hTTT : ∀ x y : Zd d (sz.L n), ∑ z : Zd d (sz.L n),
      tailT d (sz.L n) g u ((zdistInf d (sz.L n) (x - z) : ℕ) : ℝ) *
        tailT d (sz.L n) g u ((zdistInf d (sz.L n) (z - y) : ℕ) : ℝ) ≤
      (CT / (1 - u)) * tailT d (sz.L n) g u ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) :=
    fun x y => HT (sz.L n) g u u hlam hu0 le_rfl hu1 (le_total _ _) x y
  have hCT' : 0 ≤ CT / (1 - u) := by positivity
  set SΘ : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ := SB d (sz.L n) g *
    Theta d (sz.L n) g ((u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) with hSΘdef
  -- Bound 1
  set K : ℝ := C₁ * Cs * (CT / (1 - u)) + Cs * (1 - u)⁻¹ with hKdef
  have hK1 : ∀ p q : Zd d (sz.L n), ∑ b, ‖SΘ p b‖ * P ((zdistInf d (sz.L n) (b - q) : ℕ) : ℝ) ≤
      K * P ((zdistInf d (sz.L n) (p - q) : ℕ) : ℝ) :=
    fun p q => nkl_conv_P (t := u) (ℓ := ℓ) (W := Wr) (D := D) hL hWpos hℓ0
      (Q := C₁ * Cs) (CT := CT / (1 - u)) (c := (1 - u)⁻¹) (by positivity) hCT' hSΘ hrowSΘ hTTT p q
  have hconv : ∀ p q : Zd d (sz.L n), ∑ b, ‖SΘ p b‖ *
        (J * ((Wr ^ d)⁻¹ * P ((zdistInf d (sz.L n) (b - q) : ℕ) : ℝ))) ≤
      K * J * ((Wr ^ d)⁻¹ * P ((zdistInf d (sz.L n) (p - q) : ℕ) : ℝ)) := by
    intro p q
    have h := mul_le_mul_of_nonneg_left (hK1 p q)
      (mul_nonneg hJ0 (by positivity : (0 : ℝ) ≤ (Wr ^ d)⁻¹))
    calc ∑ b, ‖SΘ p b‖ * (J * ((Wr ^ d)⁻¹ * P ((zdistInf d (sz.L n) (b - q) : ℕ) : ℝ)))
        = (J * (Wr ^ d)⁻¹) * ∑ b, ‖SΘ p b‖ * P ((zdistInf d (sz.L n) (b - q) : ℕ) : ℝ) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
      _ ≤ (J * (Wr ^ d)⁻¹) * (K * P ((zdistInf d (sz.L n) (p - q) : ℕ) : ℝ)) := h
      _ = _ := by ring
  have hC2 : 2 * K = 2 * (C₁ * Cs * CT + Cs) / (1 - u) := by rw [hKdef]; field_simp
  have hB1 : ‖STthetaOp sz n E u σ (STLKM sz n E u H σ) a‖ ≤
      (2 * (C₁ * Cs * CT + Cs)) / (1 - u) * J * STprof sz n u D ℓ (a 0) (a 1) := by
    unfold STthetaOp
    simp only [nkl_STmsig_eq]
    have hterm : ∀ i : Fin 2, ‖∑ b, (mSigma E (σ 0) * mSigma E (σ 1)) * (SΘ (a i) b) *
        STLKM sz n E u H σ (Function.update a i b)‖ ≤
        ∑ b, ‖SΘ (a i) b‖ *
          (J * STprof sz n u D ℓ ((Function.update a i b) 0) ((Function.update a i b) 1)) := by
      intro i
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      rw [norm_mul, norm_mul, hm, one_mul]
      exact mul_le_mul_of_nonneg_left (hF σ _) (norm_nonneg _)
    rw [Fin.sum_univ_two]
    refine (norm_add_le _ _).trans ((add_le_add (hterm 0) (hterm 1)).trans ?_)
    have e0 : ∀ b, (Function.update a 0 b) 0 = b := fun b => by simp
    have e0' : ∀ b, (Function.update a 0 b) 1 = a 1 := fun b => by simp
    have e1 : ∀ b, (Function.update a 1 b) 0 = a 0 := fun b => by simp
    have e1' : ∀ b, (Function.update a 1 b) 1 = b := fun b => by simp
    simp only [e0, e0', e1, e1', hprof]
    have t0 := hconv (a 0) (a 1)
    have t1 : ∑ b, ‖SΘ (a 1) b‖ * (J * ((Wr ^ d)⁻¹ *
        P ((zdistInf d (sz.L n) (a 0 - b) : ℕ) : ℝ))) ≤
        K * J * ((Wr ^ d)⁻¹ * P ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) := by
      have h := hconv (a 1) (a 0)
      rw [nkl_zdistInf_sub_comm (a 1) (a 0)] at h
      calc _ = ∑ b, ‖SΘ (a 1) b‖ * (J * ((Wr ^ d)⁻¹ *
              P ((zdistInf d (sz.L n) (b - a 0) : ℕ) : ℝ))) :=
            Finset.sum_congr rfl fun b _ => by rw [nkl_zdistInf_sub_comm (a 0) b]
        _ ≤ _ := h
    have hfin : K * J * ((Wr ^ d)⁻¹ * P ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) +
        K * J * ((Wr ^ d)⁻¹ * P ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) =
        2 * (C₁ * Cs * CT + Cs) / (1 - u) * J *
          ((Wr ^ d)⁻¹ * P ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) := by
      rw [← hC2]; ring
    linarith
  -- Bound 2
  have hWd : ‖(((sz.W n : ℕ) : ℂ) ^ d)‖ = Wr ^ d := by rw [norm_pow, Complex.norm_natCast]
  obtain ⟨hSumA, hSumB⟩ := nkl_ward_LKM sz n hκ hE hu0 hu1 H hH hGM σ
  have hA : ∀ x : Zd d (sz.L n), ‖STLKM sz n E u H σ ![x, a 1]‖ ≤
      J * ((Wr ^ d)⁻¹ * P ((zdistInf d (sz.L n) (x - a 1) : ℕ) : ℝ)) := by
    intro x
    have h := hF σ ![x, a 1]
    simpa [hprof] using h
  have hB : ∀ y : Zd d (sz.L n), ‖STLKM sz n E u H σ ![a 0, y]‖ ≤
      J * ((Wr ^ d)⁻¹ * P ((zdistInf d (sz.L n) (a 0 - y) : ℕ) : ℝ)) := by
    intro y
    have h := hF σ ![a 0, y]
    simpa [hprof] using h
  have key := nkl_bound2 (g := g) (t := u) (ℓ := ℓ) (D := D) (CT := CT / (1 - u)) hL hWpos hℓ0 hJ0
    (cW := (Wr ^ d)⁻¹) (by positivity) (fun x => ‖STLKM sz n E u H σ ![x, a 1]‖)
    (fun y => ‖STLKM sz n E u H σ ![a 0, y]‖) (fun x => norm_nonneg _) (fun y => norm_nonneg _)
    (a 0) (a 1) hA hB (hSumA (a 1)) (hSumB (a 0)) hTTT
  have hB2 : ‖STELKLKM sz n E u H σ a‖ ≤ Wr ^ d *
      (2 * (J * (Wr ^ d)⁻¹ * Cs * P ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) *
          (5 * ((Wr ^ d)⁻¹ * (1 - u)⁻¹)) +
        (if 1 ≤ ℓ then (J * (Wr ^ d)⁻¹) ^ 2 * (Cs * ((CT / (1 - u)) *
          tailT d (sz.L n) g u ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ))) else 0)) := by
    unfold STELKLKM
    rw [norm_mul, hWd]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun x _ => norm_sum_le _ _).trans ?_)
    refine le_trans (Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_) key
    rw [norm_mul, norm_mul]
  -- the constants
  have hCs0 : 0 < Cs := by linarith
  have hw : 0 < Wr ^ d := by positivity
  set Cc : ℝ := 2 * (C₁ * Cs * CT + Cs) + 10 * Cs + Cs * CT with hCc
  have hCc1 : 0 ≤ Cc - 2 * (C₁ * Cs * CT + Cs) := by
    rw [hCc]; have := mul_pos hCs0 hCT; linarith
  have hCc2 : 0 ≤ Cc - 10 * Cs := by
    rw [hCc]; have : 0 ≤ C₁ * Cs * CT + Cs := by positivity
    linarith [mul_nonneg hCs0.le hCT.le]
  have hCc3 : 0 ≤ Cc - Cs * CT := by
    rw [hCc]; have : 0 ≤ C₁ * Cs * CT + Cs := by positivity
    linarith
  set Ps : ℝ := P ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) with hPs
  set Ts : ℝ := tailT d (sz.L n) g u ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) with hTs
  have hTsP : Ts ≤ Ps := nkl_tailT_le_tailW hℓ0 (Nat.cast_nonneg _)
  have hTs0 : 0 ≤ Ts := tailT_nonneg (Nat.cast_nonneg _)
  have hPs0 : 0 < Ps := hP0 _
  have hpr : STprof sz n u D ℓ (a 0) (a 1) = (Wr ^ d)⁻¹ * Ps := hprof _ _
  have hpr0 : 0 < (Wr ^ d)⁻¹ * Ps := by positivity
  have e1 : Wr ^ d * (2 * (J * (Wr ^ d)⁻¹ * Cs * Ps) * (5 * ((Wr ^ d)⁻¹ * (1 - u)⁻¹))) =
      10 * Cs / (1 - u) * J * ((Wr ^ d)⁻¹ * Ps) := by
    field_simp
    ring
  have e2 : Wr ^ d * ((J * (Wr ^ d)⁻¹) ^ 2 * (Cs * (CT / (1 - u) * Ts))) =
      Cs * CT / (1 - u) * J ^ 2 * ((Wr ^ d)⁻¹ * Ts) := by
    field_simp
  refine ⟨?_, ?_⟩
  · rw [hpr] at hB1 ⊢
    refine hB1.trans ?_
    have h1 : 2 * (C₁ * Cs * CT + Cs) / (1 - u) ≤ Cc / (1 - u) :=
      div_le_div_of_nonneg_right (by linarith) hv.le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hJ0) hpr0.le
  · rw [hpr]
    refine hB2.trans ?_
    rw [mul_add, e1]
    have hX : 0 ≤ J * ((Wr ^ d)⁻¹ * Ps) / (1 - u) := by positivity
    by_cases h1 : 1 ≤ ℓ
    · simp only [h1, ite_true, mul_one]
      rw [e2]
      have hq : (Wr ^ d)⁻¹ * Ts ≤ (Wr ^ d)⁻¹ * Ps :=
        mul_le_mul_of_nonneg_left hTsP (by positivity)
      have hq2 : Cs * CT / (1 - u) * J ^ 2 * ((Wr ^ d)⁻¹ * Ts) ≤
          Cs * CT / (1 - u) * J ^ 2 * ((Wr ^ d)⁻¹ * Ps) :=
        mul_le_mul_of_nonneg_left hq (by positivity)
      have hdiff : Cc / (1 - u) * (J + J ^ 2) * ((Wr ^ d)⁻¹ * Ps) -
          (10 * Cs / (1 - u) * J * ((Wr ^ d)⁻¹ * Ps) +
            Cs * CT / (1 - u) * J ^ 2 * ((Wr ^ d)⁻¹ * Ps)) =
          (Cc - 10 * Cs) / (1 - u) * J * ((Wr ^ d)⁻¹ * Ps) +
            (Cc - Cs * CT) / (1 - u) * J ^ 2 * ((Wr ^ d)⁻¹ * Ps) := by ring
      have hn1 : 0 ≤ (Cc - 10 * Cs) / (1 - u) * J * ((Wr ^ d)⁻¹ * Ps) := by
        have := div_nonneg hCc2 hv.le; positivity
      have hn2 : 0 ≤ (Cc - Cs * CT) / (1 - u) * J ^ 2 * ((Wr ^ d)⁻¹ * Ps) := by
        have := div_nonneg hCc3 hv.le; positivity
      linarith
    · simp only [h1, ite_false, mul_zero, add_zero, mul_zero]
      have hdiff : Cc / (1 - u) * (J + J ^ 2 * 0) * ((Wr ^ d)⁻¹ * Ps) -
          10 * Cs / (1 - u) * J * ((Wr ^ d)⁻¹ * Ps) =
          (Cc - 10 * Cs) / (1 - u) * J * ((Wr ^ d)⁻¹ * Ps) := by ring
      have hn1 : 0 ≤ (Cc - 10 * Cs) / (1 - u) * J * ((Wr ^ d)⁻¹ * Ps) := by
        have := div_nonneg hCc2 hv.le; positivity
      linarith

/-- **`lem:newKLK`** (`3_5:371–378`, proof `3_5:610–654`): the pin `STNewKLK` holds, with
`δ₀ = κ/2` and `C` as in `nkl_at`. -/
theorem stNewKLK_holds (d : ℕ) : STNewKLK d := by
  intro hd κ 𝔡 hκ h𝔡
  obtain ⟨C, hC, h⟩ := nkl_at d hd κ 𝔡 hκ h𝔡
  exact ⟨C, κ / 2, hC, by positivity, h⟩

/-! ### Compiled nonempty instances (`d = 3`, the merged preflight sequence `sz0`)

`sz0` at `n = 0`: `L = 4`, `W = 32`, `lam = 1/64` (`sz0_values`); `κ = 𝔡 = 1/10` (`lam ≤ 𝔡⁻¹ = 10`),
`E = 0` (`|E| ≤ 2 - κ`, `m(0) = i`), `D = 1`, `ℓ = 2` (`1 ≤ ℓ ≤ L`, so the indicator `1_{ℓ≥1}` is
on), `u > 0`, and `H = 0` (Hermitian).  At `H = 0` the resolvent is `G_u = (-z_u)⁻¹ I` with
`z_u = (1-u) i`, so `G_u - M = i u/(1-u) I` is not `0` for `u > 0` and `‖G_u - M‖_max = u/(1-u)`
(`nkl_STGMM_zero`).  Every deterministic hypothesis of the pin is discharged. -/

private theorem nkl_mE_zero : mE 0 = Complex.I := by
  have hsqrt : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  simp [mE, hsqrt]

private theorem nkl_diag0 {u : ℝ} (hu1 : u < 1) :
    (-(((1 - u : ℝ) : ℂ) * Complex.I))⁻¹ - Complex.I = ((u / (1 - u) : ℝ) : ℂ) * Complex.I := by
  have hv : ((1 - u : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by linarith : (1 - u : ℝ) ≠ 0)
  have h1 : (-(((1 - u : ℝ) : ℂ) * Complex.I))⁻¹ = (((1 - u : ℝ) : ℂ))⁻¹ * Complex.I := by
    rw [inv_neg, mul_inv, Complex.inv_I]; ring
  have h2 : ((u / (1 - u) : ℝ) : ℂ) = (((1 - u : ℝ) : ℂ))⁻¹ - 1 := by
    rw [Complex.ofReal_div]
    field_simp
    push_cast
    ring
  rw [h1, h2]; ring

/-- At `H = 0`, `E = 0`: `‖(G_u - M)_{xy}‖ ≤ u/(1-u)` (equality on the diagonal). -/
private theorem nkl_STGMM_zero {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u < 1) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖STGMM sz n 0 u (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) x y‖ ≤
      u / (1 - u) := by
  have hv : 0 < 1 - u := by linarith
  have hz : zt 0 u = ((1 - u : ℝ) : ℂ) * Complex.I := by simp [zt, nkl_mE_zero]
  have hne : -(zt 0 u) ≠ 0 := by
    rw [hz]
    have : ((1 - u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
    exact neg_ne_zero.2 (mul_ne_zero this Complex.I_ne_zero)
  unfold STGMM Gres
  simp only [ite_true]
  rw [zero_sub, ← neg_smul, ring_inverse_smul_one hne, hz]
  by_cases hxy : x = y
  · subst hxy
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, ite_true, nkl_mE_zero]
    rw [nkl_diag0 hu1, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_of_nonneg (by positivity)]
  · simp only [Matrix.smul_apply, Matrix.one_apply_ne hxy, smul_zero, hxy, ite_false, sub_zero,
      norm_zero]
    positivity

open RBM.Gauss.SizesInst in
/-- **`stNewKLK_holds`, instantiated**: the constants `C, δ₀` of the pin (`κ = 𝔡 = 1/10`), then the
time `u = δ₀/(1+δ₀) ∈ (0,1)` (so that `‖G_u - M‖_max = u/(1-u) = δ₀`, `G_u ≠ M`), and the two
bounds of `(juwo2=klk)`, `(juwo=Lklk)` at `n = 0`, `E = 0`, `D = 1`, `ℓ = 2`, `H = 0`, for all
sign patterns `σ` and all `a ∈ (Z_4^3)²`. -/
example : ∃ C δ₀ u : ℝ, 0 < C ∧ 0 < δ₀ ∧ 0 < u ∧ u < 1 ∧
    ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L 0)),
      ‖STthetaOp sz0 0 0 u σ (STLKM sz0 0 0 u
          (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) σ) a‖ ≤
          C / (1 - u) * STJhatM sz0 0 0 1 2 u
            (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) *
            STprof sz0 0 u 1 2 (a 0) (a 1) ∧
        ‖STELKLKM sz0 0 0 u
            (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) σ a‖ ≤
          C / (1 - u) * (STJhatM sz0 0 0 1 2 u
            (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) +
            STJhatM sz0 0 0 1 2 u
              (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) ^ 2 *
              (if 1 ≤ (2 : ℝ) then 1 else 0)) * STprof sz0 0 u 1 2 (a 0) (a 1) := by
  obtain ⟨C, δ₀, hC, hδ, hAt⟩ := stNewKLK_holds 3 (by norm_num) (1 / 10) (1 / 10) (by norm_num)
    (by norm_num)
  have hlam : 0 < sz0.lam 0 := by simp [sz0]
  have hlam' : sz0.lam 0 ≤ ((1 : ℝ) / 10)⁻¹ := by
    have : sz0.lam 0 = 1 / 64 := by norm_num [sz0]
    rw [this]; norm_num
  have hL4 : (2 : ℝ) ≤ ((sz0.L 0 : ℕ) : ℝ) := by norm_num [sz0]
  have hu0 : 0 < δ₀ / (1 + δ₀) := by positivity
  have hu1 : δ₀ / (1 + δ₀) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have huδ : δ₀ / (1 + δ₀) / (1 - δ₀ / (1 + δ₀)) = δ₀ := by
    field_simp
    ring
  refine ⟨C, δ₀, δ₀ / (1 + δ₀), hC, hδ, hu0, hu1, fun σ a => ?_⟩
  exact hAt sz0 0 0 (δ₀ / (1 + δ₀)) 1 2 hlam hlam' (by norm_num) hu0.le hu1 zero_le_one
    (by norm_num) hL4 0 Matrix.isHermitian_zero
    (fun x y => (nkl_STGMM_zero sz0 0 hu0.le hu1 x y).trans huδ.le) σ a

open RBM.Gauss.SizesInst in
/-- The same with every number explicit (`δ₀ = κ/2 = 1/20` from `nkl_at`): `u = 1/32`,
`‖G_u - M‖_max = 1/31 ≤ 1/20`, `n = 0`, `E = 0`, `D = 1`, `ℓ = 2`, `H = 0`. -/
example : ∃ C : ℝ, 0 < C ∧ ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L 0)),
    ‖STthetaOp sz0 0 0 (1 / 32) σ (STLKM sz0 0 0 (1 / 32)
        (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) σ) a‖ ≤
        C / (1 - 1 / 32) * STJhatM sz0 0 0 1 2 (1 / 32)
          (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) *
          STprof sz0 0 (1 / 32) 1 2 (a 0) (a 1) ∧
      ‖STELKLKM sz0 0 0 (1 / 32)
          (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) σ a‖ ≤
        C / (1 - 1 / 32) * (STJhatM sz0 0 0 1 2 (1 / 32)
          (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) +
          STJhatM sz0 0 0 1 2 (1 / 32)
            (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) ^ 2 *
            (if 1 ≤ (2 : ℝ) then 1 else 0)) * STprof sz0 0 (1 / 32) 1 2 (a 0) (a 1) := by
  obtain ⟨C, hC, hAt⟩ := nkl_at 3 (by norm_num) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
  have hlam : 0 < sz0.lam 0 := by simp [sz0]
  have hlam' : sz0.lam 0 ≤ ((1 : ℝ) / 10)⁻¹ := by
    have : sz0.lam 0 = 1 / 64 := by norm_num [sz0]
    rw [this]; norm_num
  have hL4 : (2 : ℝ) ≤ ((sz0.L 0 : ℕ) : ℝ) := by norm_num [sz0]
  refine ⟨C, hC, fun σ a => ?_⟩
  exact hAt sz0 0 0 (1 / 32) 1 2 hlam hlam' (by norm_num) (by norm_num) (by norm_num)
    zero_le_one (by norm_num) hL4 0 Matrix.isHermitian_zero
    (fun x y => (nkl_STGMM_zero sz0 0 (by norm_num) (by norm_num) x y).trans (by norm_num)) σ a

end RBM.Gauss.Sizes
