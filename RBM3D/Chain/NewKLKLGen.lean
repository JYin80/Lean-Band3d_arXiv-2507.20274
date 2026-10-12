/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step5Gen
import RBM3D.Chain.NewKLKGen
import RBM3D.Induction.NewKLKL

/-!
# `lem:newKLK` at `ℓ = L` over the carrier (T2462, U4s1b)

Additive restatement of `Induction/NewKLKL.lean` (not edited) over a family `mk` of matrix-level
carriers, in the pattern of `Chain/NewKLKGen.lean`: the sharp form of `lem:newKLK` at `ℓ = L`
(`(i2kk2zgg)`, `3_5:628-651`) holds for every family that satisfies the facts `NewKLKGenHyp`
(F5-F9; F6 and F7 are not read here).  Paper: arXiv:2507.20274.

* **Target 10.** `stNewKLKLAtgL'_of` (pointwise, `δ₀ = κ/2`, `C = 2 (4 + C_K) + C_s C_T` with
  `C_s = 2^{d-2} e`, `C_T` of `ekPropTInf_holds`) and `stNewKLKLgL'_of` (the pin `STNewKLKLgL'` of
  `Chain/Step5Gen.lean`), then the band result `stNewKLKLgL'_holds_band` from
  `newKLKGenHyp_band`; an `example` gets the same result through U6's route
  `stNewKLKLgL'_band d (stNewKLKL_holds d)`.
* The proof is that of `newKLKL_at` (`NewKLKL:732`): `bound2` at `ℓ = L` (copied below for a generic
  kernel `S`, with the support, row-sum and symmetry facts F5), the Ward marginals of
  `𝓛 - 𝒦` (`NewKLKGen_ward_LKM`, which reads F8 and F9), and `(TTT2)`.

Private lemmas are reached by `open private`: the model-free helpers of `Induction/NewKLKL.lean`
(tail floor and cut, `newKLKL_STGMM_zero` for the instance) and the generic convolution and Ward
bounds of `Chain/NewKLKGen.lean` (`NewKLKGen_conv_two`, `NewKLKGen_ward_LKM`).  Only
`NewKLKLGen_bound2` is copied (RBM3D, no RBM1D/RBM2D text).
-/

set_option linter.style.longLine false

open private newKLKL_Cs_ge_one newKLKL_tailT_le_tailW newKLKL_tailW_eq_of_near newKLKL_tailW_of_far
  newKLKL_zdistInf_le_L newKLKL_mE_zero newKLKL_STGMM_zero from RBM3D.Induction.NewKLKL
open private NewKLKGen_conv_two NewKLKGen_ward_LKM from RBM3D.Chain.NewKLKGen

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Bound 2 at `ℓ = L` for a generic kernel `S` -/

section Assembly

variable {d L : ℕ} [NeZero L] {g t : ℝ}

/-- **Bound 2 at `ℓ = L`, abstractly** (`3_5:626-654`, `3_5:640-646`; copy of `newKLKL_bound2`,
`Induction/NewKLKL.lean:606`, with the kernel `SB` replaced by a kernel `S` with `|x-y|_∞ ≤ 1` on its support,
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

/-! ## 2. Target 10: `lem:newKLK` at `ℓ = L` over the carrier -/

section Main

variable {d : ℕ}

/-- **Target 10, pointwise form** (`δ₀ = κ/2`; the proof of `newKLKL_at`, `NewKLKL:732`, with `S`, `m`, `K`, `LM`, `GMM` read
from the family `mk`): under `NewKLKGenHyp d κ 𝔡 mk` (constants `K_c, C_K`), `C = 2 (4 + C_K) + C_s C_T` works, with
`C_s = 2^{d-2} e` and `C_T` of `ekPropTInf_holds d`.  F5 gives the support, row sums and symmetry of `S`; F8 and F9 give the
Ward marginals `(4 + C_K) W^{-d} (1-u)⁻¹` of `𝓛 - 𝒦` (`NewKLKGen_ward_LKM`); F6 and F7 are not read. -/
theorem stNewKLKLAtgL'_of (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ)
    (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) (hyp : NewKLKGenHyp d κ 𝔡 mk) :
    ∃ C : ℝ, 0 < C ∧ STNewKLKLAtgL' d κ 𝔡 C (κ / 2) mk := by
  obtain ⟨K_c, C_K, hKc, hCK, hS, _, _, hK, hlink⟩ := hyp
  obtain ⟨CT, hCT, HT⟩ := ekPropTInf_holds d hd
  have hCs := newKLKL_Cs_ge_one (d := d)
  set Cs : ℝ := 2 ^ (d - 2) * Real.exp 1 with hCsdef
  have hCs0 : 0 < Cs := by linarith
  refine ⟨2 * (4 + C_K) + Cs * CT, by positivity, ?_⟩
  intro sz n E u D hlam hlam' hIm hu0 hu1 hD H hH hGM σ a
  set Cm := mk sz (fun _ => E) with hCm
  have hv : 0 < 1 - u := by linarith
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := Nat.cast_pos.2 (sz.W_pos n)
  have hℓ0 : (0 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := Nat.cast_nonneg _
  set Wr : ℝ := ((sz.W n : ℕ) : ℝ) with hWr
  set ℓ : ℝ := ((sz.L n : ℕ) : ℝ) with hℓdef
  set J : ℝ := STJhatMg Cm n D ℓ u H with hJ
  set g : ℝ := sz.lam n with hg
  set P : ℝ → ℝ := tailW d (sz.L n) g u ℓ Wr D with hP
  have hP0 : ∀ r, 0 < P r := fun r => tailW_pos hWpos r
  have hprof : ∀ x y : Zd d (sz.L n), STprof sz n u D ℓ x y =
      (Wr ^ d)⁻¹ * P ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) := fun x y => rfl
  have hprof0 : ∀ x y : Zd d (sz.L n), 0 < STprof sz n u D ℓ x y := fun x y => by
    rw [hprof]; have := hP0 ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ); positivity
  have hF : ∀ (σ' : Fin 2 → Bool) (a' : Fin 2 → Zd d (sz.L n)),
      ‖STLKMg Cm n u H σ' a'‖ ≤ J * STprof sz n u D ℓ (a' 0) (a' 1) := by
    intro σ' a'
    have h := Finset.le_sup' (fun p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) =>
      ‖STLKMg Cm n u H p.1 p.2‖ / STprof sz n u D ℓ (p.2 0) (p.2 1)) (Finset.mem_univ (σ', a'))
    rw [div_le_iff₀ (hprof0 _ _)] at h
    exact h
  have hJ0 : 0 ≤ J := by
    have h := hF σ (fun _ => 0)
    have h1 := norm_nonneg (STLKMg Cm n u H σ (fun _ => 0))
    have h2 := hprof0 (0 : Zd d (sz.L n)) 0
    by_contra hneg
    push Not at hneg
    nlinarith
  obtain ⟨hsupp, hrow, hsym⟩ := hS sz n E hlam hlam' hIm
  have hTTT : ∀ x y : Zd d (sz.L n), ∑ z : Zd d (sz.L n),
      tailT d (sz.L n) g u ((zdistInf d (sz.L n) (x - z) : ℕ) : ℝ) *
        tailT d (sz.L n) g u ((zdistInf d (sz.L n) (z - y) : ℕ) : ℝ) ≤
      (CT / (1 - u)) * tailT d (sz.L n) g u ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) :=
    fun x y => HT (sz.L n) g u u hlam hu0 le_rfl hu1 (le_total _ _) x y
  -- Bound 2 at `ℓ = L`
  have hWd : ‖(((sz.W n : ℕ) : ℂ) ^ d)‖ = Wr ^ d := by rw [norm_pow, Complex.norm_natCast]
  obtain ⟨ζ, hζ, hLM, hGMd⟩ := hlink sz n E u hlam hlam' hIm hu0 hu1
  obtain ⟨hKa, hKb⟩ := hK sz n E u hlam hlam' hIm hu0 hu1 σ
  obtain ⟨hSumA, hSumB⟩ := NewKLKGen_ward_LKM Cm n hκ hIm hu1 hζ hLM hGMd σ hKa hKb H hH hGM
  have hA : ∀ x : Zd d (sz.L n), ‖STLKMg Cm n u H σ ![x, a 1]‖ ≤
      J * ((Wr ^ d)⁻¹ * P ((zdistInf d (sz.L n) (x - a 1) : ℕ) : ℝ)) := by
    intro x
    have h := hF σ ![x, a 1]
    simpa [hprof] using h
  have hB : ∀ y : Zd d (sz.L n), ‖STLKMg Cm n u H σ ![a 0, y]‖ ≤
      J * ((Wr ^ d)⁻¹ * P ((zdistInf d (sz.L n) (a 0 - y) : ℕ) : ℝ)) := by
    intro y
    have h := hF σ ![a 0, y]
    simpa [hprof] using h
  have key := NewKLKLGen_bound2 hsupp hrow hsym (g := g) (t := u) (D := D) (CT := CT / (1 - u)) hWpos hJ0
    (cW := (Wr ^ d)⁻¹) (by positivity) (fun x => ‖STLKMg Cm n u H σ ![x, a 1]‖)
    (fun y => ‖STLKMg Cm n u H σ ![a 0, y]‖) (fun x => norm_nonneg _) (fun y => norm_nonneg _)
    (a 0) (a 1) hA hB (hSumA (a 1)) (hSumB (a 0)) hTTT
  have hB2 : ‖STELKLKMg Cm n u H σ a‖ ≤ Wr ^ d *
      (2 * (J * (Wr ^ d)⁻¹ * Wr ^ (-D)) * ((4 + C_K) * ((Wr ^ d)⁻¹ * (1 - u)⁻¹)) +
        (J * (Wr ^ d)⁻¹) ^ 2 * (Cs * ((CT / (1 - u)) *
          tailT d (sz.L n) g u ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)))) := by
    unfold STELKLKMg
    rw [norm_mul, hWd]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun x _ => norm_sum_le _ _).trans ?_)
    refine le_trans (Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_) key
    rw [norm_mul, norm_mul]
  -- the constants
  have hw : 0 < Wr ^ d := by positivity
  set Q : ℝ := 2 * (4 + C_K) with hQ
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  set Ps : ℝ := P ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) with hPs
  set Ts : ℝ := tailT d (sz.L n) g u ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) with hTs
  have hTsP : Ts ≤ Ps := newKLKL_tailT_le_tailW hℓ0 (Nat.cast_nonneg _)
  have hTs0 : 0 ≤ Ts := tailT_nonneg (Nat.cast_nonneg _)
  have hPs0 : 0 < Ps := hP0 _
  have hω0 : 0 < Wr ^ (-D) := Real.rpow_pos_of_pos hWpos _
  have hpr : STprof sz n u D ℓ (a 0) (a 1) = (Wr ^ d)⁻¹ * Ps := hprof _ _
  have e1 : Wr ^ d * (2 * (J * (Wr ^ d)⁻¹ * Wr ^ (-D)) * ((4 + C_K) * ((Wr ^ d)⁻¹ * (1 - u)⁻¹))) =
      Q / (1 - u) * (J * (Wr ^ d)⁻¹ * Wr ^ (-D)) := by
    rw [hQ]
    field_simp
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
  have hdiff : (Q + Cs * CT) / (1 - u) * (J ^ 2 * ((Wr ^ d)⁻¹ * Ps) + J * (Wr ^ d)⁻¹ * Wr ^ (-D)) -
      (Q / (1 - u) * (J * (Wr ^ d)⁻¹ * Wr ^ (-D)) +
        Cs * CT / (1 - u) * (J ^ 2 * ((Wr ^ d)⁻¹ * Ps))) =
      Q / (1 - u) * (J ^ 2 * ((Wr ^ d)⁻¹ * Ps)) +
        Cs * CT / (1 - u) * (J * (Wr ^ d)⁻¹ * Wr ^ (-D)) := by ring
  have hn1 : 0 ≤ Q / (1 - u) * (J ^ 2 * ((Wr ^ d)⁻¹ * Ps)) := by positivity
  have hn2 : 0 ≤ Cs * CT / (1 - u) * (J * (Wr ^ d)⁻¹ * Wr ^ (-D)) := by positivity
  linarith

/-- **Target 10**: `STNewKLKLgL' d mk` (`lem:newKLK` at `ℓ = L`, U6's primed pin) for every family whose facts F5-F9 hold,
quantified as the pin quantifies `κ 𝔡` (the constants `K_c, C_K` of `NewKLKGenHyp` may depend on `(κ, 𝔡)`); `δ₀ = κ/2`.
Band original `stNewKLKL_holds` (`NewKLKL:836`). -/
theorem stNewKLKLgL'_of (d : ℕ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) :
    (3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → NewKLKGenHyp d κ 𝔡 mk) → STNewKLKLgL' d mk := by
  intro h hd κ 𝔡 hκ h𝔡
  obtain ⟨C, hC, hAt⟩ := stNewKLKLAtgL'_of hd κ 𝔡 hκ mk (h hd κ 𝔡 hκ h𝔡)
  exact ⟨C, κ / 2, hC, by positivity, hAt⟩

end Main

/-! ## 3. The band family -/

/-- **Target 10, band result** (`d` arbitrary; U6's `STNewKLKLgL'` at `bandStep2Mat`): target 10 and `newKLKGenHyp_band`
(F5-F9 hold at the band for `3 ≤ d`, `κ, 𝔡 > 0`). -/
theorem stNewKLKLgL'_holds_band (d : ℕ) : STNewKLKLgL' d (fun sz E => bandStep2Mat sz E) :=
  stNewKLKLgL'_of d _ fun hd κ 𝔡 hκ h𝔡 => newKLKGenHyp_band hd κ 𝔡 hκ h𝔡

/-! ## 4. Compiled nonempty instances (`d = 3`)

The band family `fun sz E => bandStep2Mat sz E` satisfies F5-F9 for every `κ, 𝔡 > 0` (`newKLKGenHyp_band`), so target 10
holds at the band.  The pointwise instance is the merged preflight sequence `sz0` (`L = 4`, `W = 32`, `lam = 1/64`) at
`n = 0`, `E = 0` (`m = i`), `u = 1/32`, `D = 1`, `ℓ = L = 4` (so `1 ≤ ℓ`), `H = 0`: `‖G_u - M‖_max = u/(1-u) = 1/31 ≤ 1/20 =
δ₀` (`κ = 1/10`), so `G_u ≠ M`. -/

section Inst

open RBM.Gauss.SizesInst

/-- **Target 10 at the band, through the generic theorem** (every deterministic hypothesis of `stNewKLKLgL'_of` is
discharged by `newKLKGenHyp_band`). -/
example : STNewKLKLgL' 3 (fun sz E => bandStep2Mat sz E) :=
  stNewKLKLgL'_of 3 _ fun hd κ 𝔡 hκ h𝔡 => newKLKGenHyp_band hd κ 𝔡 hκ h𝔡

/-- **Target 10 at the band, through U6's route**: the merged band pin `stNewKLKL_holds` and `stNewKLKLgL'_band`; it
gives the same statement as `stNewKLKLgL'_holds_band`. -/
example (d : ℕ) : STNewKLKLgL' d (fun sz E => bandStep2Mat sz E) := stNewKLKLgL'_band d (stNewKLKL_holds d)

/-- **Target 10, pointwise, at the band**: `d = 3`, `κ = 𝔡 = 1/10`, `δ₀ = 1/20`. -/
example : ∃ C : ℝ, 0 < C ∧ STNewKLKLAtgL' 3 (1 / 10) (1 / 10) C (1 / 20) (fun sz E => bandStep2Mat sz E) := by
  obtain ⟨C, hC, h⟩ := stNewKLKLAtgL'_of (d := 3) (by norm_num) (1 / 10) (1 / 10) (by norm_num) _
    (newKLKGenHyp_band (d := 3) (by norm_num) (1 / 10) (1 / 10) (by norm_num) (by norm_num))
  refine ⟨C, hC, ?_⟩
  have e : (1 / 10 : ℝ) / 2 = 1 / 20 := by norm_num
  rw [e] at h
  exact h

/-- The band carrier at `sz0`, `E ≡ 0`. -/
private abbrev NewKLKLGen_cm0 : Step2Mat sz0 := bandStep2Mat sz0 (fun _ => 0)

/-- The matrix `H = 0` at `sz0`, `n = 0`. -/
private abbrev NewKLKLGen_H0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ := 0

/-- **Target 10, the bound itself, at `sz0`**: `stNewKLKLAtgL'_of` at `κ = 𝔡 = 1/10` (`lam = 1/64 ≤ 10`, `Im m(0) = 1 ≥ κ`),
`n = 0`, `E = 0`, `u = 1/32`, `D = 1`, `H = 0` (Hermitian, `‖G_u - M‖_max ≤ 1/31 ≤ 1/20`), all `σ` and `a`. -/
example : ∃ C : ℝ, 0 < C ∧ ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L 0)),
    ‖STELKLKMg NewKLKLGen_cm0 0 (1 / 32) NewKLKLGen_H0 σ a‖ ≤
      C / (1 - 1 / 32) * (STJhatMg NewKLKLGen_cm0 0 1 ((sz0.L 0 : ℕ) : ℝ) (1 / 32) NewKLKLGen_H0 ^ 2 *
          STprof sz0 0 (1 / 32) 1 ((sz0.L 0 : ℕ) : ℝ) (a 0) (a 1) +
        STJhatMg NewKLKLGen_cm0 0 1 ((sz0.L 0 : ℕ) : ℝ) (1 / 32) NewKLKLGen_H0 * (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ *
          ((sz0.W 0 : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
  obtain ⟨C, hC, h⟩ := stNewKLKLAtgL'_of (d := 3) (by norm_num) (1 / 10) (1 / 10) (by norm_num) _
    (newKLKGenHyp_band (d := 3) (by norm_num) (1 / 10) (1 / 10) (by norm_num) (by norm_num))
  have hlam : 0 < sz0.lam 0 := by simp [sz0]
  have hlam' : sz0.lam 0 ≤ ((1 : ℝ) / 10)⁻¹ := by
    have : sz0.lam 0 = 1 / 64 := by norm_num [sz0]
    rw [this]; norm_num
  have hIm : (1 / 10 : ℝ) ≤ ((bandStep2Mat sz0 fun _ => 0).m 0).im := by
    change (1 / 10 : ℝ) ≤ (mE 0).im
    rw [newKLKL_mE_zero]; norm_num
  refine ⟨C, hC, fun σ a => ?_⟩
  exact h sz0 0 0 (1 / 32) 1 hlam hlam' hIm (by norm_num) (by norm_num) zero_le_one 0
    Matrix.isHermitian_zero
    (fun x y => (newKLKL_STGMM_zero sz0 0 (by norm_num) (by norm_num) x y).trans (by norm_num)) σ a

end Inst

end RBM.BA

end
