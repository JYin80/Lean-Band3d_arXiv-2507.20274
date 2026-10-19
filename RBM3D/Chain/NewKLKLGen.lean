/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step5Gen
import RBM3D.Chain.NewKLKGen
import RBM3D.Induction.NewKLKL

/-!
# Bound 2 at `ℓ = L` for a generic kernel

The convolution estimate in the proof of the sharp form of Lemma 3.9 (`lem:newKLK`) at `ℓ = L`,
(3.57) `i2kk2zgg` (Subsection 3.4, `subsec:pf_lem:newKLK`).  `NewKLKLGen_bound2` is the argument of
`newKLKL_bound2` (`Induction/NewKLKL`) for a generic kernel `S` on `Zd d L` (support in
`|x-y|_∞ ≤ 1`, row sums `≤ 1`, `‖S_{xy}‖ = ‖S_{yx}‖`) in place of `SB`.  It is used in
`BA/Step5KerBA`.

Private lemmas are reached by `open private`: the tail helpers of `Induction/NewKLKL` and the generic
convolution and Ward bounds of `Chain/NewKLKGen` (`NewKLKGen_conv_two`, `NewKLKGen_ward_LKM`).
-/

set_option linter.style.longLine false

open private newKLKL_Cs_ge_one newKLKL_tailT_le_tailW newKLKL_tailW_eq_of_near newKLKL_tailW_of_far
  newKLKL_zdistInf_le_L from RBM3D.Induction.NewKLKL
open private NewKLKGen_conv_two NewKLKGen_ward_LKM from RBM3D.Chain.NewKLKGen

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Bound 2 at `ℓ = L` for a generic kernel `S` -/

section Assembly

variable {d L : ℕ} [NeZero L] {g t : ℝ}

/-- **Bound 2 at `ℓ = L`, abstractly** (the proof of (3.57) `i2kk2zgg`; the argument of `newKLKL_bound2`,
`Induction/NewKLKL`, with the kernel `SB` replaced by a kernel `S` with `|x-y|_∞ ≤ 1` on its support,
row sums `≤ 1` and `‖S_{xy}‖ = ‖S_{yx}‖`): with `A_x = |F(x,a₁)|`, `B_y = |F(a₀,y)|`,
`A_x ≤ J W^{-d} 𝒯̃^L(|x-a₁|)`, `B_y ≤ J W^{-d} 𝒯̃^L(|a₀-y|)` and the marginal sums bounded by `Σ̄`:
`Σ_{x,y} A_x |S_{xy}| B_y ≤ 2 J W^{-d} W^{-D} Σ̄ + (J W^{-d})² C_s C_T' 𝒯(|a₀-a₁|)`.
A far factor (`𝒯(|·|) < W^{-D}`) is bounded by `J W^{-d} W^{-D}` exactly. -/
private theorem NewKLKLGen_bound2 {S : Matrix (Zd d L) (Zd d L) ℂ}
    (hsupp : ∀ x y, S x y ≠ 0 → zdistInf d L (x - y) ≤ 1) (hrow : ∀ x, ∑ y, ‖S x y‖ ≤ 1)
    (hsym : ∀ x y, ‖S x y‖ = ‖S y x‖) {Wr D CT J cW Sig : ℝ} (hW : 0 < Wr)
    (hJ : 0 ≤ J) (hcW : 0 ≤ cW) (A B : Zd d L → ℝ) (hA0 : ∀ x, 0 ≤ A x) (hB0 : ∀ y, 0 ≤ B y)
    (a₀ a₁ : Zd d L)
    (hA : ∀ x, A x ≤ J * (cW * tailW d L g t (L : ℝ) Wr D ((zdistInf d L (x - a₁) : ℕ) : ℝ)))
    (hB : ∀ y, B y ≤ J * (cW * tailW d L g t (L : ℝ) Wr D ((zdistInf d L (a₀ - y) : ℕ) : ℝ)))
    (hSumA : ∑ x, A x ≤ Sig) (hSumB : ∑ y, B y ≤ Sig)
    (hTTT : ∀ a b : Zd d L, ∑ x : Zd d L, tailT d L g t ((zdistInf d L (a - x) : ℕ) : ℝ) *
        tailT d L g t ((zdistInf d L (x - b) : ℕ) : ℝ) ≤
      CT * tailT d L g t ((zdistInf d L (a - b) : ℕ) : ℝ)) :
    ∑ x, ∑ y, A x * ‖S x y‖ * B y ≤
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
      (‖S x y‖ * tailT d L g t ((zdistInf d L (a₀ - y) : ℕ) : ℝ))) with hT3
  have hterm : ∀ x y : Zd d L, A x * ‖S x y‖ * B y ≤
      A x * ‖S x y‖ * K0 + K0 * ‖S x y‖ * B y + T3 x y := by
    intro x y
    have hn := norm_nonneg (S x y)
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
        have h2 : 0 ≤ A x * ‖S x y‖ * K0 := by have := hA0 x; positivity
        have h3 : 0 ≤ K0 * ‖S x y‖ * B y := by have := hB0 y; positivity
        calc A x * ‖S x y‖ * B y = ‖S x y‖ * (A x * B y) := by ring
          _ ≤ ‖S x y‖ * ((J * cW) ^ 2 * (tailT d L g t ((zdistInf d L (x - a₁) : ℕ) : ℝ) *
            tailT d L g t ((zdistInf d L (a₀ - y) : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left h1 hn
          _ = T3 x y := by simp only [hT3]; ring
          _ ≤ _ := by linarith
      · -- y near, x far: `A x ≤ J W^{-d} W^{-D}`
        push Not at hNx
        have hAx : A x ≤ K0 := by
          calc A x ≤ J * (cW * tailW d L g t (L : ℝ) Wr D ((zdistInf d L (x - a₁) : ℕ) : ℝ)) := hA x
            _ = K0 := by rw [newKLKL_tailW_of_far (hrL _) hNx, hK0]; ring
        have h2 : 0 ≤ A x * ‖S x y‖ * K0 := by have := hA0 x; positivity
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAx hn) (hB0 y)
        calc A x * ‖S x y‖ * B y ≤ K0 * ‖S x y‖ * B y := this
          _ ≤ _ := by linarith
    · -- y far: `B y ≤ J W^{-d} W^{-D}`
      push Not at hNy
      have hBy : B y ≤ K0 := by
        calc B y ≤ J * (cW * tailW d L g t (L : ℝ) Wr D ((zdistInf d L (a₀ - y) : ℕ) : ℝ)) := hB y
          _ = K0 := by rw [newKLKL_tailW_of_far (hrL _) hNy, hK0]; ring
      have h3 : 0 ≤ K0 * ‖S x y‖ * B y := by have := hB0 y; positivity
      have := mul_le_mul_of_nonneg_left hBy (mul_nonneg (hA0 x) hn)
      calc A x * ‖S x y‖ * B y ≤ A x * ‖S x y‖ * K0 := by linarith
        _ ≤ _ := by linarith
  have hsum1 : ∑ x, ∑ y, A x * ‖S x y‖ * K0 ≤ K0 * Sig := by
    calc ∑ x, ∑ y, A x * ‖S x y‖ * K0 ≤ K0 * ∑ x, A x := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun x _ => ?_
          calc ∑ y, A x * ‖S x y‖ * K0 = A x * K0 * ∑ y, ‖S x y‖ := by
                rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
            _ ≤ A x * K0 * 1 := mul_le_mul_of_nonneg_left (hrow x) (mul_nonneg (hA0 x) hK0nn)
            _ = K0 * A x := by ring
      _ ≤ K0 * Sig := mul_le_mul_of_nonneg_left hSumA hK0nn
  have hsum2 : ∑ x, ∑ y, K0 * ‖S x y‖ * B y ≤ K0 * Sig := by
    calc ∑ x, ∑ y, K0 * ‖S x y‖ * B y = ∑ y, ∑ x, K0 * ‖S x y‖ * B y :=
          Finset.sum_comm
      _ ≤ K0 * ∑ y, B y := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun y _ => ?_
          calc ∑ x, K0 * ‖S x y‖ * B y = K0 * B y * ∑ x, ‖S y x‖ := by
                rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by rw [hsym]; ring
            _ ≤ K0 * B y * 1 := mul_le_mul_of_nonneg_left (hrow y) (mul_nonneg hK0nn (hB0 y))
            _ = K0 * B y := by ring
      _ ≤ K0 * Sig := mul_le_mul_of_nonneg_left hSumB hK0nn
  have hsum3 : ∑ x, ∑ y, T3 x y ≤ (J * cW) ^ 2 * (Cs *
      (CT * tailT d L g t ((zdistInf d L (a₀ - a₁) : ℕ) : ℝ))) := by
    have e : ∑ x, ∑ y, T3 x y = (J * cW) ^ 2 * ∑ x, ∑ y, (tailT d L g t
        ((zdistInf d L (x - a₁) : ℕ) : ℝ) * (‖S x y‖ *
          tailT d L g t ((zdistInf d L (a₀ - y) : ℕ) : ℝ))) := by
      simp only [hT3]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
    rw [e]
    exact mul_le_mul_of_nonneg_left (NewKLKGen_conv_two hsupp hrow hTTT a₀ a₁) (sq_nonneg _)
  calc ∑ x, ∑ y, A x * ‖S x y‖ * B y
      ≤ ∑ x, ∑ y, (A x * ‖S x y‖ * K0 + K0 * ‖S x y‖ * B y + T3 x y) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hterm x y
    _ = ∑ x, ∑ y, A x * ‖S x y‖ * K0 + ∑ x, ∑ y, K0 * ‖S x y‖ * B y +
          ∑ x, ∑ y, T3 x y := by
        simp only [Finset.sum_add_distrib]
    _ ≤ _ := by
        have : K0 * Sig + K0 * Sig = 2 * (J * cW * Wr ^ (-D)) * Sig := by rw [hK0]; ring
        linarith

end Assembly

end RBM.BA

end
