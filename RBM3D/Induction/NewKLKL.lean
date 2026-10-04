/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.NewKLK
import RBM3D.Induction.Step5Pins

/-!
# S5-12 (ticket T2150): `lem:newKLK` at `ℓ = L`, sharp form; the pin `STNewKLKL` proved

`stNewKLKL_holds (d : ℕ) : STNewKLKL d` (`Induction/Step5Pins.lean:245`; paper `3_5:628-651` with `ℓ = L`,
paper-delta candidate `T2134a`): for `3 ≤ d`, with `δ₀ = κ/2` and a constant `C = 10 + C_s C_T` depending on `d`
only (`newKLKL_at`), every Hermitian `H` with `‖G_u - M‖_max ≤ δ₀` has
`|𝓔^{(𝓛-𝒦)×(𝓛-𝒦),(2)}_{u,σ,a}| ≤ C/(1-u) (Ĵ² W^{-d} 𝒯̃^L_{u,D}(|a₁-a₂|) + Ĵ W^{-d} W^{-D})`, `Ĵ = Ĵ^L_{u,D}`
(`STNewKLKLAt`).  Deterministic: the only external input is `(TTT2)` (`ekPropTInf_holds`) and the resolvent identity.

Route (the proof of `nkl_bound2`, `Induction/NewKLK.lean:840`, at `ℓ = L`).
* `W^{-d} 𝓔 = Σ_{x,y} F(x,a₂) S_{xy} F(a₁,y)`, `F = 𝓛-𝒦`.  At `ℓ = L` every `L^∞` distance is `≤ L = ℓ`
  (`zdist L u = min u.val (L - u.val) ≤ L`), so `1 ≤ ℓ` and, for `r = |·|_∞`,
  `𝒯̃^L(r) = max(𝒯(r), W^{-D})`: either `W^{-D} ≤ 𝒯(r)` (near, `𝒯̃ = 𝒯`) or `𝒯(r) < W^{-D}` (far, `𝒯̃ = W^{-D}` exactly).
  This pointwise split replaces the paper's case distinction on `𝒯_u(L) ≥ W^{-D}` (`3_5:612-616`).
* Pairs `(x,y)` with `y` far: `B_y = |F(a₁,y)| ≤ Ĵ W^{-d} W^{-D}` (no shift `C_s`, no profile at `|a₁-a₂|`), summed
  against `Σ_x A_x ≤ 5 W^{-d}/(1-u)` (Ward, `newKLKL_ward_LKM`); `y` near and `x` far: `A_x ≤ Ĵ W^{-d} W^{-D}`,
  `Σ_y B_y ≤ 5 W^{-d}/(1-u)` (`S` symmetric with row sums `1`); both near: `A_x ≤ Ĵ W^{-d} 𝒯(|x-a₂|)`,
  `B_y ≤ Ĵ W^{-d} 𝒯(|a₁-y|)`, so `(Ĵ W^{-d})² C_s C_T/(1-u) 𝒯(|a₁-a₂|)` by `S`-support and `(TTT2)`
  (`newKLKL_conv_two`).  Multiplying by `W^d`: `10 Ĵ W^{-d-D}/(1-u) + C_s C_T/(1-u) Ĵ² W^{-d} 𝒯(|a₁-a₂|)`;
  the first power of `Ĵ` multiplies only the floor, the second the profile, and `𝒯 ≤ 𝒯̃^L`.
* Constants: `C = 10 + C_s C_T`, `C_s = 2^{d-2} e` (shift of `𝒯`), `C_T` of `(TTT2)`; `δ₀ = κ/2`.

Sources: no port from RBM1D/RBM2D.  Private copies of the private helpers of `Induction/NewKLK.lean` (`b06ff9b`),
prefix `newKLKL_`: `nkl_tailT_shift`, `nkl_Cs_ge_one`, `nkl_tailT_le_tailW`, `nkl_tailW_eq_of_near`,
`nkl_zdistInf_{neg,sub_comm,add_le,tri}`, `nkl_SB_support`, `nkl_conv_two`, the Ward block (sections D, E:
`nklQ` ... `nkl_ward_LKM`), `nkl_mE_zero`, `nkl_diag0`, `nkl_STGMM_zero`.  New: `newKLKL_zdistInf_le_L`,
`newKLKL_tailW_of_far`, `newKLKL_bound2`, `newKLKL_at`, `stNewKLKL_holds`.
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
private theorem newKLKL_tailT_shift (hL : 1 ≤ (L : ℝ)) {r r' : ℝ} (hr : 0 ≤ r) (hr' : 0 ≤ r')
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
private theorem newKLKL_Cs_ge_one : (1 : ℝ) ≤ 2 ^ (d - 2) * Real.exp 1 :=
  one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (Real.one_le_exp (by norm_num))

variable {ℓ W D : ℝ}

/-- `𝒯_t(r) ≤ 𝒯̃(r)`. -/
private theorem newKLKL_tailT_le_tailW (hℓ : 0 ≤ ℓ) {r : ℝ} (hr : 0 ≤ r) :
    tailT d L g t r ≤ tailW d L g t ℓ W D r :=
  (tailT_antitone (le_min hr hℓ) (min_le_left r ℓ)).trans (le_max_left _ _)

/-- Near region: `𝒯̃(r) = 𝒯_t(r)` for `r ≤ ℓ` and `W^{-D} ≤ 𝒯_t(r)`. -/
private theorem newKLKL_tailW_eq_of_near {r : ℝ} (hrℓ : r ≤ ℓ) (hω : W ^ (-D) ≤ tailT d L g t r) :
    tailW d L g t ℓ W D r = tailT d L g t r := by
  unfold tailW
  rw [min_eq_left hrℓ]
  exact max_eq_left hω

end Tail

/-! ### B. The `L^∞` distance and the block kernel -/

section Dist

variable {d L : ℕ} [NeZero L]

private theorem newKLKL_zdistInf_neg (x : Zd d L) : zdistInf d L (-x) = zdistInf d L x := by
  simp only [zdistInf, Pi.neg_apply, zdist_neg]

private theorem newKLKL_zdistInf_sub_comm (x y : Zd d L) : zdistInf d L (x - y) = zdistInf d L (y - x) := by
  rw [← newKLKL_zdistInf_neg (y - x), neg_sub]

private theorem newKLKL_zdistInf_add_le (x y : Zd d L) :
    zdistInf d L (x + y) ≤ zdistInf d L x + zdistInf d L y := by
  unfold zdistInf
  refine Finset.sup_le fun i _ => ?_
  calc zdist L ((x + y) i) = zdist L (x i + y i) := rfl
    _ ≤ zdist L (x i) + zdist L (y i) := zdist_add_le L (x i) (y i)
    _ ≤ _ := Nat.add_le_add
        (Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i))
        (Finset.le_sup (f := fun j => zdist L (y j)) (Finset.mem_univ i))

/-- Triangle inequality in the form `|a - c| ≤ |a - b| + |b - c|`. -/
private theorem newKLKL_zdistInf_tri (a b c : Zd d L) :
    zdistInf d L (a - c) ≤ zdistInf d L (a - b) + zdistInf d L (b - c) := by
  have := newKLKL_zdistInf_add_le (a - b) (b - c)
  rwa [sub_add_sub_cancel] at this

omit [NeZero L] in
/-- The support of `S^{(B)}`: `S_{ab} ≠ 0` forces `|a - b|_∞ ≤ 1`. -/
private theorem newKLKL_SB_support (g : ℝ) {a b : Zd d L} (h : SB d L g a b ≠ 0) :
    zdistInf d L (a - b) ≤ 1 := by
  rw [SB_apply] at h
  by_cases h0 : a - b = 0
  · rw [h0]
    simp [zdistInf, zdist]
  · by_cases h1 : zdistD d L (a - b) = 1
    · exact (zdistInf_le_zdistD d L _).trans h1.le
    · exact absurd (by simp [sbKernel, h0, h1]) h

end Dist

/-! ### C. Convolution bound: both factors near -/

section Conv

variable {d L : ℕ} [NeZero L] {g t : ℝ}

/-- **Bound 2 core, both factors near**: `Σ_{x,y} 𝒯(|x-a₁|) |S_{xy}| 𝒯(|a₀-y|) ≤ C_s C_T/(1-u) 𝒯(|a₀-a₁|)`
(`S_{xy} ≠ 0` forces `|x - y| ≤ 1`, hence `𝒯(|a₀-y|) ≤ C_s 𝒯(|a₀-x|)`, then `(TTT2)`). -/
private theorem newKLKL_conv_two (hL : 3 ≤ L) {CT : ℝ}
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
    · have h1 : zdistInf d L (x - y) ≤ 1 := newKLKL_SB_support g hx
      have h2 := newKLKL_zdistInf_tri a₀ y x
      rw [newKLKL_zdistInf_sub_comm y x] at h2
      have hsh := newKLKL_tailT_shift (d := d) (g := g) (t := t) hL1
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
private def newKLKLQ (G : Matrix (Vtx d L W) (Vtx d L W) ℂ) (a b : Zd d L) : ℝ :=
  ∑ l : Vtx d L W, ∑ j : Vtx d L W, if l.1 = b then (if j.1 = a then ‖G l j‖ ^ 2 else 0) else 0

/-- The trace of a two-loop, entrywise: `⟨A E_a B E_b⟩ = Σ_{l,j} A_{lj} E_a(j) B_{jl} E_b(l)`. -/
private theorem newKLKL_trace2 (A B : Matrix (Vtx d L W) (Vtx d L W) ℂ) (a b : Zd d L) :
    Matrix.trace (A * Eblk d L W a * (B * Eblk d L W b)) =
      ∑ l : Vtx d L W, ∑ j : Vtx d L W,
        (A l j * (if j.1 = a then ((W : ℂ) ^ d)⁻¹ else 0)) *
          (B j l * (if l.1 = b then ((W : ℂ) ^ d)⁻¹ else 0)) := by
  unfold Matrix.trace
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Eblk, Matrix.mul_diagonal]

private theorem newKLKL_Gres_false {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
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
private theorem newKLKL_entry_prod_le {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (z : ℂ) (s₀ s₁ : Bool) (l j : ι) :
    ‖Gres H z s₀ l j‖ * ‖Gres H z s₁ j l‖ ≤
      ‖Gres H z true l j‖ ^ 2 + ‖Gres H z true j l‖ ^ 2 := by
  have hx := norm_nonneg (Gres H z true l j)
  have hy := norm_nonneg (Gres H z true j l)
  have e1 : ‖Gres H z false l j‖ = ‖Gres H z true j l‖ := by
    rw [newKLKL_Gres_false hH, Matrix.conjTranspose_apply, norm_star]
  have e2 : ‖Gres H z false j l‖ = ‖Gres H z true l j‖ := by
    rw [newKLKL_Gres_false hH, Matrix.conjTranspose_apply, norm_star]
  cases s₀ <;> cases s₁ <;> (try simp only [e1, e2]) <;> nlinarith [sq_nonneg (‖Gres H z true l j‖ - ‖Gres H z true j l‖)]

/-- **`‖𝓛^{(2)}_{σ,(a,b)}‖ ≤ W^{-2d}(Q_{ab} + Q_{ba})`**, every sign pattern. -/
private theorem newKLKL_norm_loop2_le [NeZero W] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) (z : ℂ) (σ : Fin 2 → Bool) (a b : Zd d L) :
    ‖loopM d L W H z σ ![a, b]‖ ≤
      (((W : ℝ) ^ d)⁻¹) ^ 2 * (newKLKLQ (Gres H z true) a b + newKLKLQ (Gres H z true) b a) := by
  have hloop : loopM d L W H z σ ![a, b] =
      Matrix.trace (Gres H z (σ 0) * Eblk d L W a * (Gres H z (σ 1) * Eblk d L W b)) := by
    simp [loopM, List.ofFn_succ]
  rw [hloop, newKLKL_trace2]
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
        have := newKLKL_entry_prod_le hH z (σ 0) (σ 1) l j
        have h2 := mul_le_mul_of_nonneg_left this (sq_nonneg ((W : ℝ) ^ d)⁻¹)
        calc ‖Gres H z (σ 0) l j‖ * ((W ^ d : ℝ)⁻¹) * (‖Gres H z (σ 1) j l‖ * ((W ^ d : ℝ)⁻¹))
            = ((W ^ d : ℝ)⁻¹) ^ 2 * (‖Gres H z (σ 0) l j‖ * ‖Gres H z (σ 1) j l‖) := by ring
          _ ≤ _ := h2
      · simp [hj]
    · simp [hl]
  refine (Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun j _ => hterm l j).trans ?_
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, mul_add]
  have hswap : (∑ l : Vtx d L W, ∑ j : Vtx d L W,
      (if l.1 = b then (if j.1 = a then ‖G j l‖ ^ 2 else 0) else 0)) = newKLKLQ G b a := by
    unfold newKLKLQ
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h1 : j.1 = b <;> by_cases h2 : l.1 = a <;> simp [h1, h2]
  rw [hswap]
  rfl

private theorem newKLKL_sum_newKLKLQ_snd (G : Matrix (Vtx d L W) (Vtx d L W) ℂ) (a : Zd d L) :
    ∑ b, newKLKLQ G a b = ∑ l : Vtx d L W, ∑ j : Vtx d L W, if j.1 = a then ‖G l j‖ ^ 2 else 0 := by
  unfold newKLKLQ
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j.1 = a <;> simp [hj]

private theorem newKLKL_sum_newKLKLQ_fst (G : Matrix (Vtx d L W) (Vtx d L W) ℂ) (b : Zd d L) :
    ∑ a, newKLKLQ G a b = ∑ l : Vtx d L W, ∑ j : Vtx d L W, if l.1 = b then ‖G l j‖ ^ 2 else 0 := by
  unfold newKLKLQ
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hl : l.1 = b <;> simp [hl]

/-- `Σ_j ‖G_{lj}‖² = Im G_{ll}/η` (row mass; `G G† = (G - G†)/(2iη)`). -/
private theorem newKLKL_row_mass [NeZero W] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) (l : Vtx d L W) :
    ∑ j, ‖Gres H z true l j‖ ^ 2 = (Gres H z true l l).im / z.im := by
  have hu : IsUnit (H - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) :=
    Ind.isUnit_sub_smul_one_of_im_ne_zero hH hz.ne'
  have hu' : IsUnit (H - (starRingEnd ℂ) z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) :=
    Ind.isUnit_sub_smul_one_of_im_ne_zero hH (by simpa using hz.ne')
  have h := congrFun (congrFun (Ind.Gres_mul_conjTranspose hH hu hu' true) l) l
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sub_apply,
    smul_eq_mul, newKLKL_Gres_false hH z] at h
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
private theorem newKLKL_col_mass [NeZero W] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) (j : Vtx d L W) :
    ∑ l, ‖Gres H z true l j‖ ^ 2 = (Gres H z true j j).im / z.im := by
  have hu : IsUnit (H - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) :=
    Ind.isUnit_sub_smul_one_of_im_ne_zero hH hz.ne'
  have hu' : IsUnit (H - (starRingEnd ℂ) z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) :=
    Ind.isUnit_sub_smul_one_of_im_ne_zero hH (by simpa using hz.ne')
  have h := congrFun (congrFun (Ind.Gres_mul_conjTranspose hH hu hu' false) j) j
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sub_apply,
    smul_eq_mul, newKLKL_Gres_false hH z, star_star] at h
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

private theorem newKLKL_block_const (a : Zd d L) (B : ℝ) :
    ∑ j : Vtx d L W, (if j.1 = a then B else 0) = (W : ℝ) ^ d * B := by
  rw [Fintype.sum_prod_type]
  have hx : ∀ x : Zd d L, (∑ _y : Fin (W ^ d), if x = a then B else 0) =
      if x = a then (W : ℝ) ^ d * B else 0 := by
    intro x; by_cases h : x = a <;> simp [h]
  simp only [hx, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- **Ward bounds for `𝓛^{(2)}`** (every sign pattern `σ`): if `Im G_{xx} ≤ B₀` for all `x`, then
both marginals of `‖𝓛^{(2)}_{σ,(·,·)}‖` are at most `2 W^{-d} B₀/Im z`. -/
private theorem newKLKL_ward_L [NeZero W] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
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
    rw [← newKLKL_block_const (L := L) (W := W) a (B0 / z.im)]
    refine Finset.sum_le_sum fun l _ => ?_
    by_cases hl : l.1 = a
    · simp only [hl, ite_true]
      rw [newKLKL_row_mass hH hz l]
      exact div_le_div_of_nonneg_right (hdiag l) hz.le
    · simp [hl]
  have hCbound : ∀ a : Zd d L, ∑ l : Vtx d L W, ∑ j : Vtx d L W,
      (if j.1 = a then ‖G l j‖ ^ 2 else 0) ≤ (W : ℝ) ^ d * (B0 / z.im) := by
    intro a
    rw [Finset.sum_comm, ← newKLKL_block_const (L := L) (W := W) a (B0 / z.im)]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : j.1 = a
    · simp only [hj, ite_true]
      rw [newKLKL_col_mass hH hz j]
      exact div_le_div_of_nonneg_right (hdiag j) hz.le
    · simp [hj]
  have hc : (((W : ℝ) ^ d)⁻¹) ^ 2 * ((W : ℝ) ^ d * (B0 / z.im)) =
      ((W : ℝ) ^ d)⁻¹ * (B0 / z.im) := by
    field_simp
  constructor
  · intro a₁
    calc ∑ x, ‖loopM d L W H z σ ![x, a₁]‖
        ≤ ∑ x, (((W : ℝ) ^ d)⁻¹) ^ 2 * (newKLKLQ G x a₁ + newKLKLQ G a₁ x) :=
          Finset.sum_le_sum fun x _ => newKLKL_norm_loop2_le hH z σ x a₁
      _ = (((W : ℝ) ^ d)⁻¹) ^ 2 * (∑ x, newKLKLQ G x a₁ + ∑ x, newKLKLQ G a₁ x) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ (((W : ℝ) ^ d)⁻¹) ^ 2 * ((W : ℝ) ^ d * (B0 / z.im) + (W : ℝ) ^ d * (B0 / z.im)) := by
          rw [newKLKL_sum_newKLKLQ_fst, newKLKL_sum_newKLKLQ_snd]
          exact mul_le_mul_of_nonneg_left (add_le_add (hRbound a₁) (hCbound a₁)) (by positivity)
      _ = _ := by rw [← two_mul, ← mul_assoc, mul_comm _ (2 : ℝ), mul_assoc, hc]
  · intro a₀
    calc ∑ y, ‖loopM d L W H z σ ![a₀, y]‖
        ≤ ∑ y, (((W : ℝ) ^ d)⁻¹) ^ 2 * (newKLKLQ G a₀ y + newKLKLQ G y a₀) :=
          Finset.sum_le_sum fun y _ => newKLKL_norm_loop2_le hH z σ a₀ y
      _ = (((W : ℝ) ^ d)⁻¹) ^ 2 * (∑ y, newKLKLQ G a₀ y + ∑ y, newKLKLQ G y a₀) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ (((W : ℝ) ^ d)⁻¹) ^ 2 * ((W : ℝ) ^ d * (B0 / z.im) + (W : ℝ) ^ d * (B0 / z.im)) := by
          rw [newKLKL_sum_newKLKLQ_fst, newKLKL_sum_newKLKLQ_snd]
          exact mul_le_mul_of_nonneg_left (add_le_add (hCbound a₀) (hRbound a₀)) (by positivity)
      _ = _ := by rw [← two_mul, ← mul_assoc, mul_comm _ (2 : ℝ), mul_assoc, hc]

end Ward

/-! ### E. Ward bounds for `𝓛 - 𝒦` of the model (`STLKM`) -/

section WardLKM

open scoped Matrix

variable {d : ℕ} (sz : Sizes d)

/-- `𝒦^{(2)} = W^{-d} m₁ m₂ Θ_{u m₁ m₂}(a₁, a₂)` for the model's `STKloop` (the `n = 2` tree formula). -/
private theorem newKLKL_STKloop_eq (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STKloop sz n E u σ a =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (mSigma E (σ 0) * mSigma E (σ 1)) *
        Theta d (sz.L n) (sz.lam n) ((u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) (a 0) (a 1) := by
  have h2 : KLloopOf d (sz.L n) σ a = ⟨[σ 0, σ 1], [a 0, a 1]⟩ := by
    simp [KLloopOf, List.ofFn_succ]
  unfold STKloop
  rw [h2, KLK_two]

/-- `Σ` of `‖𝒦^{(2)}‖` in either argument is at most `W^{-d} (1-u)⁻¹`. -/
private theorem newKLKL_ward_K (n : ℕ) {E u : ℝ} (hE : |E| ≤ 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
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
    rw [newKLKL_STKloop_eq, norm_mul, norm_mul, hm, mul_one, norm_inv, norm_pow, Complex.norm_natCast]
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

private theorem newKLKL_gres_blockMat_true {d L W : ℕ} [NeZero L] [NeZero W]
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
private theorem newKLKL_ward_LKM (n : ℕ) {E u κ : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (hu0 : 0 ≤ u)
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
    rw [hHb, newKLKL_gres_blockMat_true]
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
  obtain ⟨hLa, hLb⟩ := newKLKL_ward_L (W := sz.W n) (L := sz.L n) hHbH hz hdiag σ
  obtain ⟨hKa, hKb⟩ := newKLKL_ward_K sz n hE2 hu0 hu1 σ
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

/-! ### F. Bound 2 at `ℓ = L`, abstractly: the far pairs give the floor `W^{-D}` without the shift -/

section Assembly

variable {d L : ℕ} [NeZero L] {g t : ℝ}

omit [NeZero L] in
/-- The `L^∞` distance of the torus is at most `L` (`zdist L u = min (u.val) (L - u.val) ≤ L`). -/
private theorem newKLKL_zdistInf_le_L (x : Zd d L) : zdistInf d L x ≤ L := by
  unfold zdistInf
  refine Finset.sup_le fun i _ => ?_
  exact (min_le_right _ _).trans (Nat.sub_le _ _)

omit [NeZero L] in
/-- At `ℓ = L` every distance is `≤ ℓ`; a non-near `r` (`𝒯(r) < W^{-D}`) has `𝒯̃^L(r) = W^{-D}` exactly. -/
private theorem newKLKL_tailW_of_far {ℓ Wr D r : ℝ} (hrℓ : r ≤ ℓ) (hlt : tailT d L g t r < Wr ^ (-D)) :
    tailW d L g t ℓ Wr D r = Wr ^ (-D) := by
  unfold tailW
  rw [min_eq_left hrℓ]
  exact max_eq_right hlt.le

/-- **Bound 2 at `ℓ = L`, abstractly** (`3_5:626-654`, `3_5:640-646`): with `A_x = |F(x,a₁)|`, `B_y = |F(a₀,y)|`,
`A_x ≤ J W^{-d} 𝒯̃^L(|x-a₁|)`, `B_y ≤ J W^{-d} 𝒯̃^L(|a₀-y|)` and the marginal sums bounded by `Σ̄`:
`Σ_{x,y} A_x |S_{xy}| B_y ≤ 2 J W^{-d} W^{-D} Σ̄ + (J W^{-d})² C_s C_T' 𝒯(|a₀-a₁|)`.
A far factor (`𝒯(|·|) < W^{-D}`) is bounded by `J W^{-d} W^{-D}` exactly, with no shift and no profile at `|a₀-a₁|`
(this is where the linear term `Ĵ 𝒯̃(|a₀-a₁|)` of `nkl_bound2` disappears); both-near pairs use `(TTT2)`. -/
private theorem newKLKL_bound2 (hL : 3 ≤ L) {Wr D CT J cW Sig : ℝ} (hW : 0 < Wr)
    (hJ : 0 ≤ J) (hcW : 0 ≤ cW) (A B : Zd d L → ℝ) (hA0 : ∀ x, 0 ≤ A x) (hB0 : ∀ y, 0 ≤ B y)
    (a₀ a₁ : Zd d L)
    (hA : ∀ x, A x ≤ J * (cW * tailW d L g t (L : ℝ) Wr D ((zdistInf d L (x - a₁) : ℕ) : ℝ)))
    (hB : ∀ y, B y ≤ J * (cW * tailW d L g t (L : ℝ) Wr D ((zdistInf d L (a₀ - y) : ℕ) : ℝ)))
    (hSumA : ∑ x, A x ≤ Sig) (hSumB : ∑ y, B y ≤ Sig)
    (hTTT : ∀ a b : Zd d L, ∑ x : Zd d L, tailT d L g t ((zdistInf d L (a - x) : ℕ) : ℝ) *
        tailT d L g t ((zdistInf d L (x - b) : ℕ) : ℝ) ≤
      CT * tailT d L g t ((zdistInf d L (a - b) : ℕ) : ℝ)) :
    ∑ x, ∑ y, A x * ‖SB d L g x y‖ * B y ≤
      2 * (J * cW * Wr ^ (-D)) * Sig +
        (J * cW) ^ 2 * ((2 ^ (d - 2) * Real.exp 1) *
          (CT * tailT d L g t ((zdistInf d L (a₀ - a₁) : ℕ) : ℝ))) := by
  have hCs := newKLKL_Cs_ge_one (d := d)
  set Cs : ℝ := 2 ^ (d - 2) * Real.exp 1 with hCsdef
  have hω : 0 ≤ Wr ^ (-D) := (Real.rpow_pos_of_pos hW _).le
  set K0 : ℝ := J * cW * Wr ^ (-D) with hK0
  have hK0nn : 0 ≤ K0 := by positivity
  have hrL : ∀ x : Zd d L, ((zdistInf d L x : ℕ) : ℝ) ≤ (L : ℝ) := fun x => by
    exact_mod_cast newKLKL_zdistInf_le_L x
  set T3 : Zd d L → Zd d L → ℝ := fun x y =>
    (J * cW) ^ 2 * (tailT d L g t ((zdistInf d L (x - a₁) : ℕ) : ℝ) *
      (‖SB d L g x y‖ * tailT d L g t ((zdistInf d L (a₀ - y) : ℕ) : ℝ))) with hT3
  have hterm : ∀ x y : Zd d L, A x * ‖SB d L g x y‖ * B y ≤
      A x * ‖SB d L g x y‖ * K0 + K0 * ‖SB d L g x y‖ * B y + T3 x y := by
    intro x y
    have hn := norm_nonneg (SB d L g x y)
    have hT3nn : 0 ≤ T3 x y := by
      simp only [hT3]
      exact mul_nonneg (sq_nonneg _) (mul_nonneg (tailT_nonneg (Nat.cast_nonneg _))
          (mul_nonneg hn (tailT_nonneg (Nat.cast_nonneg _))))
    by_cases hNy : Wr ^ (-D) ≤ tailT d L g t ((zdistInf d L (a₀ - y) : ℕ) : ℝ)
    · by_cases hNx : Wr ^ (-D) ≤ tailT d L g t ((zdistInf d L (x - a₁) : ℕ) : ℝ)
      · -- both near
        have hAx := hA x
        have hBy := hB y
        have eX : tailW d L g t (L : ℝ) Wr D ((zdistInf d L (x - a₁) : ℕ) : ℝ) =
            tailT d L g t ((zdistInf d L (x - a₁) : ℕ) : ℝ) :=
          newKLKL_tailW_eq_of_near (hrL _) hNx
        have eY : tailW d L g t (L : ℝ) Wr D ((zdistInf d L (a₀ - y) : ℕ) : ℝ) =
            tailT d L g t ((zdistInf d L (a₀ - y) : ℕ) : ℝ) :=
          newKLKL_tailW_eq_of_near (hrL _) hNy
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
        have h2 : 0 ≤ A x * ‖SB d L g x y‖ * K0 := by have := hA0 x; positivity
        have h3 : 0 ≤ K0 * ‖SB d L g x y‖ * B y := by have := hB0 y; positivity
        calc A x * ‖SB d L g x y‖ * B y = ‖SB d L g x y‖ * (A x * B y) := by ring
          _ ≤ ‖SB d L g x y‖ * ((J * cW) ^ 2 * (tailT d L g t ((zdistInf d L (x - a₁) : ℕ) : ℝ) *
            tailT d L g t ((zdistInf d L (a₀ - y) : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left h1 hn
          _ = T3 x y := by simp only [hT3]; ring
          _ ≤ _ := by linarith
      · -- y near, x far: `A x ≤ J W^{-d} W^{-D}`
        push Not at hNx
        have hAx : A x ≤ K0 := by
          calc A x ≤ J * (cW * tailW d L g t (L : ℝ) Wr D ((zdistInf d L (x - a₁) : ℕ) : ℝ)) := hA x
            _ = K0 := by rw [newKLKL_tailW_of_far (hrL _) hNx, hK0]; ring
        have h2 : 0 ≤ A x * ‖SB d L g x y‖ * K0 := by have := hA0 x; positivity
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAx hn) (hB0 y)
        calc A x * ‖SB d L g x y‖ * B y ≤ K0 * ‖SB d L g x y‖ * B y := this
          _ ≤ _ := by linarith
    · -- y far: `B y ≤ J W^{-d} W^{-D}`
      push Not at hNy
      have hBy : B y ≤ K0 := by
        calc B y ≤ J * (cW * tailW d L g t (L : ℝ) Wr D ((zdistInf d L (a₀ - y) : ℕ) : ℝ)) := hB y
          _ = K0 := by rw [newKLKL_tailW_of_far (hrL _) hNy, hK0]; ring
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
  have hsum3 : ∑ x, ∑ y, T3 x y ≤ (J * cW) ^ 2 * (Cs *
      (CT * tailT d L g t ((zdistInf d L (a₀ - a₁) : ℕ) : ℝ))) := by
    have e : ∑ x, ∑ y, T3 x y = (J * cW) ^ 2 * ∑ x, ∑ y, (tailT d L g t
        ((zdistInf d L (x - a₁) : ℕ) : ℝ) * (‖SB d L g x y‖ *
          tailT d L g t ((zdistInf d L (a₀ - y) : ℕ) : ℝ))) := by
      simp only [hT3]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
    rw [e]
    exact mul_le_mul_of_nonneg_left (newKLKL_conv_two hL hTTT a₀ a₁) (sq_nonneg _)
  calc ∑ x, ∑ y, A x * ‖SB d L g x y‖ * B y
      ≤ ∑ x, ∑ y, (A x * ‖SB d L g x y‖ * K0 + K0 * ‖SB d L g x y‖ * B y + T3 x y) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hterm x y
    _ = ∑ x, ∑ y, A x * ‖SB d L g x y‖ * K0 + ∑ x, ∑ y, K0 * ‖SB d L g x y‖ * B y +
          ∑ x, ∑ y, T3 x y := by
        simp only [Finset.sum_add_distrib]
    _ ≤ _ := by
        have : K0 * Sig + K0 * Sig = 2 * (J * cW * Wr ^ (-D)) * Sig := by rw [hK0]; ring
        linarith

end Assembly

/-! ### G. The pin `STNewKLKL` -/

/-- `lem:newKLK` at `ℓ = L`, sharp, with `δ₀ = κ/2` and `C = 10 + C_s C_T` (`C_s = 2^{d-2} e`, `C_T` of `(TTT2)`). -/
private theorem newKLKL_at (d : ℕ) (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ STNewKLKLAt d κ 𝔡 C (κ / 2) := by
  obtain ⟨CT, hCT, HT⟩ := ekPropTInf_holds d hd
  have hCs := newKLKL_Cs_ge_one (d := d)
  set Cs : ℝ := 2 ^ (d - 2) * Real.exp 1 with hCsdef
  have hCs0 : 0 < Cs := by linarith
  refine ⟨10 + Cs * CT, by positivity, ?_⟩
  intro sz n E u D hlam hlam' hE hu0 hu1 hD H hH hGM σ a
  have hE2 : |E| ≤ 2 := by linarith
  have hL : 3 ≤ sz.L n := sz.three_le_L n
  have hv : 0 < 1 - u := by linarith
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := Nat.cast_pos.2 (sz.W_pos n)
  have hℓ0 : (0 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := Nat.cast_nonneg _
  set Wr : ℝ := ((sz.W n : ℕ) : ℝ) with hWr
  set ℓ : ℝ := ((sz.L n : ℕ) : ℝ) with hℓdef
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
  have hTTT : ∀ x y : Zd d (sz.L n), ∑ z : Zd d (sz.L n),
      tailT d (sz.L n) g u ((zdistInf d (sz.L n) (x - z) : ℕ) : ℝ) *
        tailT d (sz.L n) g u ((zdistInf d (sz.L n) (z - y) : ℕ) : ℝ) ≤
      (CT / (1 - u)) * tailT d (sz.L n) g u ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) :=
    fun x y => HT (sz.L n) g u u hlam hu0 le_rfl hu1 (le_total _ _) x y
  -- Bound 2 at `ℓ = L`
  have hWd : ‖(((sz.W n : ℕ) : ℂ) ^ d)‖ = Wr ^ d := by rw [norm_pow, Complex.norm_natCast]
  obtain ⟨hSumA, hSumB⟩ := newKLKL_ward_LKM sz n hκ hE hu0 hu1 H hH hGM σ
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
  have key := newKLKL_bound2 (g := g) (t := u) (D := D) (CT := CT / (1 - u)) hL hWpos hJ0
    (cW := (Wr ^ d)⁻¹) (by positivity) (fun x => ‖STLKM sz n E u H σ ![x, a 1]‖)
    (fun y => ‖STLKM sz n E u H σ ![a 0, y]‖) (fun x => norm_nonneg _) (fun y => norm_nonneg _)
    (a 0) (a 1) hA hB (hSumA (a 1)) (hSumB (a 0)) hTTT
  have hB2 : ‖STELKLKM sz n E u H σ a‖ ≤ Wr ^ d *
      (2 * (J * (Wr ^ d)⁻¹ * Wr ^ (-D)) * (5 * ((Wr ^ d)⁻¹ * (1 - u)⁻¹)) +
        (J * (Wr ^ d)⁻¹) ^ 2 * (Cs * ((CT / (1 - u)) *
          tailT d (sz.L n) g u ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)))) := by
    unfold STELKLKM
    rw [norm_mul, hWd]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun x _ => norm_sum_le _ _).trans ?_)
    refine le_trans (Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_) key
    rw [norm_mul, norm_mul]
  -- the constants
  have hw : 0 < Wr ^ d := by positivity
  set Ps : ℝ := P ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) with hPs
  set Ts : ℝ := tailT d (sz.L n) g u ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) with hTs
  have hTsP : Ts ≤ Ps := newKLKL_tailT_le_tailW hℓ0 (Nat.cast_nonneg _)
  have hTs0 : 0 ≤ Ts := tailT_nonneg (Nat.cast_nonneg _)
  have hPs0 : 0 < Ps := hP0 _
  have hω0 : 0 < Wr ^ (-D) := Real.rpow_pos_of_pos hWpos _
  have hpr : STprof sz n u D ℓ (a 0) (a 1) = (Wr ^ d)⁻¹ * Ps := hprof _ _
  have e1 : Wr ^ d * (2 * (J * (Wr ^ d)⁻¹ * Wr ^ (-D)) * (5 * ((Wr ^ d)⁻¹ * (1 - u)⁻¹))) =
      10 / (1 - u) * (J * (Wr ^ d)⁻¹ * Wr ^ (-D)) := by
    field_simp
    ring
  have e2 : Wr ^ d * ((J * (Wr ^ d)⁻¹) ^ 2 * (Cs * (CT / (1 - u) * Ts))) =
      Cs * CT / (1 - u) * (J ^ 2 * ((Wr ^ d)⁻¹ * Ts)) := by
    field_simp
  rw [hpr]
  refine hB2.trans ?_
  rw [mul_add, e1, e2]
  have hq : J ^ 2 * ((Wr ^ d)⁻¹ * Ts) ≤ J ^ 2 * ((Wr ^ d)⁻¹ * Ps) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hTsP (by positivity)) (sq_nonneg _)
  have h1 : Cs * CT / (1 - u) * (J ^ 2 * ((Wr ^ d)⁻¹ * Ts)) ≤
      Cs * CT / (1 - u) * (J ^ 2 * ((Wr ^ d)⁻¹ * Ps)) :=
    mul_le_mul_of_nonneg_left hq (by positivity)
  have hdiff : (10 + Cs * CT) / (1 - u) * (J ^ 2 * ((Wr ^ d)⁻¹ * Ps) + J * (Wr ^ d)⁻¹ * Wr ^ (-D)) -
      (10 / (1 - u) * (J * (Wr ^ d)⁻¹ * Wr ^ (-D)) +
        Cs * CT / (1 - u) * (J ^ 2 * ((Wr ^ d)⁻¹ * Ps))) =
      10 / (1 - u) * (J ^ 2 * ((Wr ^ d)⁻¹ * Ps)) +
        Cs * CT / (1 - u) * (J * (Wr ^ d)⁻¹ * Wr ^ (-D)) := by ring
  have hn1 : 0 ≤ 10 / (1 - u) * (J ^ 2 * ((Wr ^ d)⁻¹ * Ps)) := by positivity
  have hn2 : 0 ≤ Cs * CT / (1 - u) * (J * (Wr ^ d)⁻¹ * Wr ^ (-D)) := by positivity
  linarith

/-- **`lem:newKLK` at `ℓ = L`, sharp form** (`(i2kk2zgg)` `3_5:628-651` with `ℓ = L`; paper-delta candidate `T2134a`):
the pin `STNewKLKL` holds, with `δ₀ = κ/2` and `C = 10 + 2^{d-2} e C_T` (`newKLKL_at`). -/
theorem stNewKLKL_holds (d : ℕ) : STNewKLKL d := by
  intro hd κ 𝔡 hκ h𝔡
  obtain ⟨C, hC, h⟩ := newKLKL_at d hd κ 𝔡 hκ
  exact ⟨C, κ / 2, hC, by positivity, h⟩

/-! ### Compiled nonempty instances (`d = 3`)

The weak-law premise `‖G_u - M‖_max ≤ δ₀` is discharged at `H = 0`, `E = 0` (`m = i`) with the time
`u = δ₀/(1+δ₀) ∈ (0,1)`: `G_u - M = i u/(1-u) I` is not `0`, `‖G_u - M‖_max = u/(1-u) = δ₀` (`newKLKL_STGMM_zero`).
-/

private theorem newKLKL_mE_zero : mE 0 = Complex.I := by
  have hsqrt : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  simp [mE, hsqrt]

private theorem newKLKL_diag0 {u : ℝ} (hu1 : u < 1) :
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
private theorem newKLKL_STGMM_zero {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u < 1) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖STGMM sz n 0 u (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) x y‖ ≤
      u / (1 - u) := by
  have hv : 0 < 1 - u := by linarith
  have hz : zt 0 u = ((1 - u : ℝ) : ℂ) * Complex.I := by simp [zt, newKLKL_mE_zero]
  have hne : -(zt 0 u) ≠ 0 := by
    rw [hz]
    have : ((1 - u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
    exact neg_ne_zero.2 (mul_ne_zero this Complex.I_ne_zero)
  unfold STGMM Gres
  simp only [ite_true]
  rw [zero_sub, ← neg_smul, ring_inverse_smul_one hne, hz]
  by_cases hxy : x = y
  · subst hxy
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, ite_true, newKLKL_mE_zero]
    rw [newKLKL_diag0 hu1, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_of_nonneg (by positivity)]
  · simp only [Matrix.smul_apply, Matrix.one_apply_ne hxy, smul_zero, hxy, ite_false, sub_zero,
      norm_zero]
    positivity

open RBM.Gauss.SizesInst in
/-- **`stNewKLKL_holds`, instantiated at the merged preflight sequence `sz0`** (`n = 0`: `L = 4`, `W = 32`,
`lam = 1/64`, `sz0_values`): `κ = 𝔡 = 1/10`, `E = 0`, `D = 1`, `H = 0`, the constants `C, δ₀` of the pin, then the time
`u = δ₀/(1+δ₀) ∈ (0,1)` (`G_u ≠ M`), and the sharp bound at `ℓ = L` for all sign patterns `σ` and all `a ∈ (Z_4^3)²`. -/
example : ∃ C δ₀ u : ℝ, 0 < C ∧ 0 < δ₀ ∧ 0 < u ∧ u < 1 ∧
    ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L 0)),
      ‖STELKLKM sz0 0 0 u
          (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) σ a‖ ≤
        C / (1 - u) * (STJhatM sz0 0 0 1 ((sz0.L 0 : ℕ) : ℝ) u
              (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) ^ 2 *
            STprof sz0 0 u 1 ((sz0.L 0 : ℕ) : ℝ) (a 0) (a 1) +
          STJhatM sz0 0 0 1 ((sz0.L 0 : ℕ) : ℝ) u
              (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) *
            (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ * ((sz0.W 0 : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
  obtain ⟨C, δ₀, hC, hδ, hAt⟩ := stNewKLKL_holds 3 (by norm_num) (1 / 10) (1 / 10) (by norm_num)
    (by norm_num)
  have hlam : 0 < sz0.lam 0 := by simp [sz0]
  have hlam' : sz0.lam 0 ≤ ((1 : ℝ) / 10)⁻¹ := by
    have : sz0.lam 0 = 1 / 64 := by norm_num [sz0]
    rw [this]; norm_num
  have hu0 : 0 < δ₀ / (1 + δ₀) := by positivity
  have hu1 : δ₀ / (1 + δ₀) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have huδ : δ₀ / (1 + δ₀) / (1 - δ₀ / (1 + δ₀)) = δ₀ := by
    field_simp
    ring
  refine ⟨C, δ₀, δ₀ / (1 + δ₀), hC, hδ, hu0, hu1, fun σ a => ?_⟩
  exact hAt sz0 0 0 (δ₀ / (1 + δ₀)) 1 hlam hlam' (by norm_num) hu0.le hu1 zero_le_one
    0 Matrix.isHermitian_zero
    (fun x y => (newKLKL_STGMM_zero sz0 0 hu0.le hu1 x y).trans huδ.le) σ a

/-- The size data of the instance below: `d = 3`, `L = 3`, `W = 1` (`N = 27`), `lam = 1`. -/
private def newKLKLsz31 : Sizes 3 where
  L := fun _ => 3
  W := fun _ => 1
  lam := fun _ => 1
  three_le_L := fun _ => le_rfl
  W_pos := fun _ => one_pos

/-- **`stNewKLKL_holds`, instantiated at `d = 3`, `L = 3`, `W = 1`** (`newKLKLsz31`): `κ = 𝔡 = 1`
(`lam = 1 ≤ 𝔡⁻¹`), `E = 0`, `D = 1`, `H = 0`, the constants `C, δ₀` of the pin, then `u = δ₀/(1+δ₀) ∈ (0,1)`
(`G_u ≠ M`), and the sharp bound at `ℓ = L = 3` for all `σ` and all `a ∈ (Z_3^3)²`. -/
example : ∃ C δ₀ u : ℝ, 0 < C ∧ 0 < δ₀ ∧ 0 < u ∧ u < 1 ∧
    ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (newKLKLsz31.L 0)),
      ‖STELKLKM newKLKLsz31 0 0 u
          (0 : Matrix (Idx 3 (newKLKLsz31.L 0) (newKLKLsz31.W 0))
            (Idx 3 (newKLKLsz31.L 0) (newKLKLsz31.W 0)) ℂ) σ a‖ ≤
        C / (1 - u) * (STJhatM newKLKLsz31 0 0 1 ((newKLKLsz31.L 0 : ℕ) : ℝ) u
              (0 : Matrix (Idx 3 (newKLKLsz31.L 0) (newKLKLsz31.W 0))
                (Idx 3 (newKLKLsz31.L 0) (newKLKLsz31.W 0)) ℂ) ^ 2 *
            STprof newKLKLsz31 0 u 1 ((newKLKLsz31.L 0 : ℕ) : ℝ) (a 0) (a 1) +
          STJhatM newKLKLsz31 0 0 1 ((newKLKLsz31.L 0 : ℕ) : ℝ) u
              (0 : Matrix (Idx 3 (newKLKLsz31.L 0) (newKLKLsz31.W 0))
                (Idx 3 (newKLKLsz31.L 0) (newKLKLsz31.W 0)) ℂ) *
            (((newKLKLsz31.W 0 : ℕ) : ℝ) ^ 3)⁻¹ * ((newKLKLsz31.W 0 : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
  obtain ⟨C, δ₀, hC, hδ, hAt⟩ := stNewKLKL_holds 3 (by norm_num) 1 1 one_pos one_pos
  have hlam : 0 < newKLKLsz31.lam 0 := by simp [newKLKLsz31]
  have hlam' : newKLKLsz31.lam 0 ≤ (1 : ℝ)⁻¹ := by simp [newKLKLsz31]
  have hu0 : 0 < δ₀ / (1 + δ₀) := by positivity
  have hu1 : δ₀ / (1 + δ₀) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have huδ : δ₀ / (1 + δ₀) / (1 - δ₀ / (1 + δ₀)) = δ₀ := by
    field_simp
    ring
  refine ⟨C, δ₀, δ₀ / (1 + δ₀), hC, hδ, hu0, hu1, fun σ a => ?_⟩
  exact hAt newKLKLsz31 0 0 (δ₀ / (1 + δ₀)) 1 hlam hlam' (by norm_num) hu0.le hu1 zero_le_one
    0 Matrix.isHermitian_zero
    (fun x y => (newKLKL_STGMM_zero newKLKLsz31 0 hu0.le hu1 x y).trans huδ.le) σ a

end RBM.Gauss.Sizes
