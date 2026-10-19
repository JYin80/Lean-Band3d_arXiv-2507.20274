/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.NewKLK
import RBM3D.Chain.Step2Gen
import RBM3D.BA.FlowPins

/-!
# Convolution and Ward bounds for `lem:newKLK` over a carrier

Generic versions of the estimates in the proof of Lemma 3.9 (`lem:newKLK`, Subsection 3.4
`subsec:pf_lem:newKLK`), for a generic kernel `S` and a family `mk` of matrix-level carriers.  They are
the arguments of `nkl_conv_two`, `nkl_bound2`, `nkl_ward_LKM` of `Induction/NewKLK` with `S`, `Θ`, `m`,
`K`, `LM`, `GMM` read from the family:

* `NewKLKGen_conv_two`: the convolution of two near factors against `S`;
* `NewKLKGen_bound2`: bound 2 of the proof, abstractly;
* `NewKLKGen_ward_LKM`: the Ward bounds for `𝓛 - 𝒦` over the carrier;
* `NewKLKGenHyp`: the carrier hypotheses under which the generic proof runs (support, row sums and
  symmetry of `S`, `‖m‖ ≤ 1`, the convolution of the block kernel against `tailW`, the marginals of
  `𝒦^{(2)}`, and `LM`, `GMM` as the resolvent of `loopFine` at `ζ` with `Im ζ = (1-u) Im m`).

The private lemmas of `Induction/NewKLK` used here (tail shift/near/far lemmas, distance lemmas,
`nkl_ward_L`, `nkl_gres_blockMat_true`, `nkl_SB_support`, `nkl_theta_tail`, `nkl_SBTheta_tail`,
`nkl_SBTheta_row`, `nkl_conv_P`, `nkl_ward_K`) are reached by `open private`.
-/

set_option linter.style.longLine false

open private nkl_Cs_ge_one nkl_tailT_shift nkl_tailT_le_tailW nkl_tailW_eq_of_near nkl_tailW_far
  nkl_zdistInf_sub_comm nkl_zdistInf_tri nkl_dist_cases nkl_ward_L nkl_gres_blockMat_true
  nkl_SB_support nkl_theta_tail nkl_SBTheta_tail nkl_SBTheta_row nkl_conv_P nkl_ward_K
  from RBM3D.Induction.NewKLK

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The two convolution bounds over a generic kernel `S` -/

section Assembly

variable {d L : ℕ} [NeZero L] {g t : ℝ}

/-- **Bound 2 core, both factors near**, for a kernel `S` with `|x-y|_∞ ≤ 1` on its support and row sums `≤ 1`:
`Σ_{x,y} 𝒯(|x-a₁|) ‖S_{xy}‖ 𝒯(|a₀-y|) ≤ C_s C_T 𝒯(|a₀-a₁|)` (the argument of `nkl_conv_two`, `Induction/NewKLK`, for a generic kernel). -/
private theorem NewKLKGen_conv_two {S : Matrix (Zd d L) (Zd d L) ℂ}
    (hsupp : ∀ x y, S x y ≠ 0 → zdistInf d L (x - y) ≤ 1) (hrow : ∀ x, ∑ y, ‖S x y‖ ≤ 1) {CT : ℝ}
    (hTTT : ∀ a b : Zd d L, ∑ x : Zd d L, tailT d L g t ((zdistInf d L (a - x) : ℕ) : ℝ) *
        tailT d L g t ((zdistInf d L (x - b) : ℕ) : ℝ) ≤
      CT * tailT d L g t ((zdistInf d L (a - b) : ℕ) : ℝ)) (a₀ a₁ : Zd d L) :
    ∑ x : Zd d L, ∑ y : Zd d L, tailT d L g t ((zdistInf d L (x - a₁) : ℕ) : ℝ) *
        (‖S x y‖ * tailT d L g t ((zdistInf d L (a₀ - y) : ℕ) : ℝ)) ≤
      (2 ^ (d - 2) * Real.exp 1) * (CT * tailT d L g t ((zdistInf d L (a₀ - a₁) : ℕ) : ℝ)) := by
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (NeZero.one_le (n := L))
  have hterm : ∀ x y : Zd d L, tailT d L g t ((zdistInf d L (x - a₁) : ℕ) : ℝ) *
        (‖S x y‖ * tailT d L g t ((zdistInf d L (a₀ - y) : ℕ) : ℝ)) ≤
      (2 ^ (d - 2) * Real.exp 1) * (‖S x y‖ *
        (tailT d L g t ((zdistInf d L (a₀ - x) : ℕ) : ℝ) *
          tailT d L g t ((zdistInf d L (x - a₁) : ℕ) : ℝ))) := by
    intro x y
    by_cases hx : S x y = 0
    · simp [hx]
    · have h1 : zdistInf d L (x - y) ≤ 1 := hsupp x y hx
      have h2 := nkl_zdistInf_tri a₀ y x
      rw [nkl_zdistInf_sub_comm y x] at h2
      have hsh := nkl_tailT_shift (d := d) (g := g) (t := t) hL1
        (Nat.cast_nonneg (zdistInf d L (a₀ - x))) (Nat.cast_nonneg (zdistInf d L (a₀ - y)))
        (by exact_mod_cast (by omega : zdistInf d L (a₀ - x) ≤ zdistInf d L (a₀ - y) + 1))
      have hT1 := tailT_nonneg (d := d) (L := L) (g := g) (t := t)
        (Nat.cast_nonneg (zdistInf d L (x - a₁)))
      have hn := norm_nonneg (S x y)
      calc tailT d L g t ((zdistInf d L (x - a₁) : ℕ) : ℝ) *
            (‖S x y‖ * tailT d L g t ((zdistInf d L (a₀ - y) : ℕ) : ℝ))
          ≤ tailT d L g t ((zdistInf d L (x - a₁) : ℕ) : ℝ) *
            (‖S x y‖ * ((2 ^ (d - 2) * Real.exp 1) *
              tailT d L g t ((zdistInf d L (a₀ - x) : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsh hn) hT1
        _ = _ := by ring
  have hCs := nkl_Cs_ge_one (d := d)
  have hZ : ∀ x : Zd d L, 0 ≤ tailT d L g t ((zdistInf d L (a₀ - x) : ℕ) : ℝ) *
      tailT d L g t ((zdistInf d L (x - a₁) : ℕ) : ℝ) := fun x =>
    mul_nonneg (tailT_nonneg (Nat.cast_nonneg _)) (tailT_nonneg (Nat.cast_nonneg _))
  calc ∑ x : Zd d L, ∑ y : Zd d L, tailT d L g t ((zdistInf d L (x - a₁) : ℕ) : ℝ) *
        (‖S x y‖ * tailT d L g t ((zdistInf d L (a₀ - y) : ℕ) : ℝ))
      ≤ ∑ x : Zd d L, ∑ y : Zd d L, (2 ^ (d - 2) * Real.exp 1) * (‖S x y‖ *
        (tailT d L g t ((zdistInf d L (a₀ - x) : ℕ) : ℝ) *
          tailT d L g t ((zdistInf d L (x - a₁) : ℕ) : ℝ))) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hterm x y
    _ ≤ ∑ x : Zd d L, (2 ^ (d - 2) * Real.exp 1) * (tailT d L g t ((zdistInf d L (a₀ - x) : ℕ) : ℝ) *
          tailT d L g t ((zdistInf d L (x - a₁) : ℕ) : ℝ)) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [← Finset.mul_sum, ← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (hZ x) (hrow x)) (by positivity)
    _ = (2 ^ (d - 2) * Real.exp 1) * ∑ x : Zd d L, (tailT d L g t ((zdistInf d L (a₀ - x) : ℕ) : ℝ) *
          tailT d L g t ((zdistInf d L (x - a₁) : ℕ) : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hTTT a₀ a₁) (by positivity)


/-- **Bound 2, abstractly** (in the proof of Lemma 3.9 `lem:newKLK`, after (3.56) `eq;facts`): with `A_x = |F(x,a₁)|`, `B_y = |F(a₀,y)|`,
`A_x ≤ J W^{-d} 𝒯̃(|x-a₁|)`, `B_y ≤ J W^{-d} 𝒯̃(|a₀-y|)` and the marginal sums bounded by `Σ̄`:
`Σ_{x,y} A_x |S_{xy}| B_y ≤ 2 J W^{-d} C_s 𝒯̃(|a₀-a₁|) Σ̄ + 1_{ℓ≥1} (J W^{-d})² C_s C_T' 𝒯(|a₀-a₁|)`. -/
private theorem NewKLKGen_bound2 {S : Matrix (Zd d L) (Zd d L) ℂ}
    (hsupp : ∀ x y, S x y ≠ 0 → zdistInf d L (x - y) ≤ 1) (hrow : ∀ x, ∑ y, ‖S x y‖ ≤ 1)
    (hsym : ∀ x y, ‖S x y‖ = ‖S y x‖) {ℓ Wr D CT J cW Sig : ℝ} (hW : 0 < Wr) (hℓ : 0 ≤ ℓ)
    (hJ : 0 ≤ J) (hcW : 0 ≤ cW) (A B : Zd d L → ℝ) (hA0 : ∀ x, 0 ≤ A x) (hB0 : ∀ y, 0 ≤ B y)
    (a₀ a₁ : Zd d L)
    (hA : ∀ x, A x ≤ J * (cW * tailW d L g t ℓ Wr D ((zdistInf d L (x - a₁) : ℕ) : ℝ)))
    (hB : ∀ y, B y ≤ J * (cW * tailW d L g t ℓ Wr D ((zdistInf d L (a₀ - y) : ℕ) : ℝ)))
    (hSumA : ∑ x, A x ≤ Sig) (hSumB : ∑ y, B y ≤ Sig)
    (hTTT : ∀ a b : Zd d L, ∑ x : Zd d L, tailT d L g t ((zdistInf d L (a - x) : ℕ) : ℝ) *
        tailT d L g t ((zdistInf d L (x - b) : ℕ) : ℝ) ≤
      CT * tailT d L g t ((zdistInf d L (a - b) : ℕ) : ℝ)) :
    ∑ x, ∑ y, A x * ‖S x y‖ * B y ≤
      2 * (J * cW * (2 ^ (d - 2) * Real.exp 1) *
          tailW d L g t ℓ Wr D ((zdistInf d L (a₀ - a₁) : ℕ) : ℝ)) * Sig +
        (if 1 ≤ ℓ then (J * cW) ^ 2 * ((2 ^ (d - 2) * Real.exp 1) *
          (CT * tailT d L g t ((zdistInf d L (a₀ - a₁) : ℕ) : ℝ))) else 0) := by
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (NeZero.one_le (n := L))
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
      (‖S x y‖ * tailT d L g t ((zdistInf d L (a₀ - y) : ℕ) : ℝ))) else 0 with hT3
  have hterm : ∀ x y : Zd d L, A x * ‖S x y‖ * B y ≤
      A x * ‖S x y‖ * K0 + K0 * ‖S x y‖ * B y + T3 x y := by
    intro x y
    have hn := norm_nonneg (S x y)
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
            (‖S x y‖ * tailT d L g t ((zdistInf d L (a₀ - y) : ℕ) : ℝ))) := by
          simp only [hT3, hNx.1, ite_true]
        have h2 : 0 ≤ A x * ‖S x y‖ * K0 := by have := hA0 x; positivity
        have h3 : 0 ≤ K0 * ‖S x y‖ * B y := by have := hB0 y; positivity
        calc A x * ‖S x y‖ * B y = ‖S x y‖ * (A x * B y) := by ring
          _ ≤ ‖S x y‖ * ((J * cW) ^ 2 * (tailT d L g t ((zdistInf d L (x - a₁) : ℕ) : ℝ) *
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
        have h2 : 0 ≤ A x * ‖S x y‖ * K0 := by have := hA0 x; positivity
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAx hn) (hB0 y)
        calc A x * ‖S x y‖ * B y ≤ K0 * ‖S x y‖ * B y := this
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
  have hsum3 : ∑ x, ∑ y, T3 x y ≤ (if 1 ≤ ℓ then (J * cW) ^ 2 * (Cs *
      (CT * tailT d L g t ((zdistInf d L (a₀ - a₁) : ℕ) : ℝ))) else 0) := by
    by_cases h1 : 1 ≤ ℓ
    · have e : ∑ x, ∑ y, T3 x y = (J * cW) ^ 2 * ∑ x, ∑ y, (tailT d L g t
          ((zdistInf d L (x - a₁) : ℕ) : ℝ) * (‖S x y‖ *
            tailT d L g t ((zdistInf d L (a₀ - y) : ℕ) : ℝ))) := by
        simp only [hT3, ite_true, h1]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
      rw [e]
      simp only [h1, ite_true]
      exact mul_le_mul_of_nonneg_left (NewKLKGen_conv_two hsupp hrow hTTT a₀ a₁) (sq_nonneg _)
    · simp [hT3, h1]
  calc ∑ x, ∑ y, A x * ‖S x y‖ * B y
      ≤ ∑ x, ∑ y, (A x * ‖S x y‖ * K0 + K0 * ‖S x y‖ * B y + T3 x y) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hterm x y
    _ = ∑ x, ∑ y, A x * ‖S x y‖ * K0 + ∑ x, ∑ y, K0 * ‖S x y‖ * B y +
          ∑ x, ∑ y, T3 x y := by
        simp only [Finset.sum_add_distrib]
    _ ≤ _ := by
        have : K0 * Sig + K0 * Sig = 2 * (J * cW * Cs * Ps) * Sig := by rw [hK0]; ring
        linarith


end Assembly

/-! ## 2. Ward marginals of `𝓛 - 𝒦` over the carrier -/

section Ward

open scoped Matrix

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz)

/-- **Ward bounds for `𝓛 - 𝒦` over the carrier** (every `σ`; the argument of `nkl_ward_LKM`, `Induction/NewKLK`): for Hermitian `H` with
`‖G_u - M‖_max ≤ κ/2`, `κ ≤ Im m`, both marginals of `‖(𝓛-𝒦)^{(2)}_{u,σ,(·,·)}‖` are at most `(4 + C_K) W^{-d} (1-u)⁻¹`,
given the marginals of `𝒦^{(2)}` (`C_K W^{-d} (1-u)⁻¹`) and the link of `LM`, `GMM` to the resolvent at `ζ`. -/
private theorem NewKLKGen_ward_LKM (n : ℕ) {u κ C_K : ℝ} (hκ : 0 < κ) (hIm : κ ≤ (Cm.m n).im) (hu1 : u < 1)
    {ζ : ℂ} (hζ : ζ.im = (1 - u) * (Cm.m n).im)
    (hLM : ∀ (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool)
      (a : Fin 2 → Zd d (sz.L n)), Cm.LM n u H σ a = loopFine d (sz.L n) (sz.W n) H ζ σ a)
    (hGMd : ∀ (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (x : Idx d (sz.L n) (sz.W n)),
      Cm.GMM n u H x x = Gres H ζ true x x - Cm.m n)
    (σ : Fin 2 → Bool)
    (hKa : ∀ a₁ : Zd d (sz.L n), ∑ x, ‖Cm.K n u σ ![x, a₁]‖ ≤
      C_K * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 - u)⁻¹))
    (hKb : ∀ a₀ : Zd d (sz.L n), ∑ y, ‖Cm.K n u σ ![a₀, y]‖ ≤
      C_K * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 - u)⁻¹))
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hH : H.IsHermitian) (hGM : ∀ x y, ‖Cm.GMM n u H x y‖ ≤ κ / 2) :
    (∀ a₁ : Zd d (sz.L n), ∑ x, ‖STLKMg Cm n u H σ ![x, a₁]‖ ≤
        (4 + C_K) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 - u)⁻¹)) ∧
      (∀ a₀ : Zd d (sz.L n), ∑ y, ‖STLKMg Cm n u H σ ![a₀, y]‖ ≤
        (4 + C_K) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 - u)⁻¹)) := by
  have hv : 0 < 1 - u := by linarith
  have hmpos : 0 < (Cm.m n).im := lt_of_lt_of_le hκ hIm
  have hz : 0 < ζ.im := by rw [hζ]; positivity
  set Hb := blockMat d (sz.L n) (sz.W n) H with hHb
  have hHbH : Hb.IsHermitian := Matrix.IsHermitian.submatrix hH _
  have hdiag : ∀ x : Vtx d (sz.L n) (sz.W n),
      (Gres Hb ζ true x x).im ≤ (Cm.m n).im + κ / 2 := by
    intro x
    rw [hHb, nkl_gres_blockMat_true]
    set s := (splitEquiv d (sz.L n) (sz.W n)).symm x with hs
    have h1 := hGM s s
    have h2 : (Cm.GMM n u H s s).im = (Gres H ζ true s s).im - (Cm.m n).im := by
      rw [hGMd]; simp
    have h3 := Complex.abs_im_le_norm (Cm.GMM n u H s s)
    have h4 := le_abs_self (Cm.GMM n u H s s).im
    linarith
  obtain ⟨hLa, hLb⟩ := nkl_ward_L (W := sz.W n) (L := sz.L n) hHbH hz hdiag σ
  have hcore : 2 * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((Cm.m n).im + κ / 2) / ζ.im)) ≤
      4 * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 - u)⁻¹) := by
    rw [hζ]
    have : ((Cm.m n).im + κ / 2) / ((1 - u) * (Cm.m n).im) ≤ 2 * (1 - u)⁻¹ := by
      rw [div_le_iff₀ (by positivity)]
      have : 2 * (1 - u)⁻¹ * ((1 - u) * (Cm.m n).im) = 2 * (Cm.m n).im := by field_simp
      rw [this]; linarith
    have hW0 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
    nlinarith
  have hsplit : ∀ a : Fin 2 → Zd d (sz.L n), ‖STLKMg Cm n u H σ a‖ ≤
      ‖loopM d (sz.L n) (sz.W n) Hb ζ σ a‖ + ‖Cm.K n u σ a‖ := fun a => by
    change ‖Cm.LM n u H σ a - Cm.K n u σ a‖ ≤ _
    rw [hLM]
    exact norm_sub_le _ _
  constructor
  · intro a₁
    calc ∑ x, ‖STLKMg Cm n u H σ ![x, a₁]‖
        ≤ ∑ x, (‖loopM d (sz.L n) (sz.W n) Hb ζ σ ![x, a₁]‖ + ‖Cm.K n u σ ![x, a₁]‖) :=
          Finset.sum_le_sum fun x _ => hsplit _
      _ = _ := Finset.sum_add_distrib
      _ ≤ _ := by
          have := hLa a₁
          have := hKa a₁
          linarith
  · intro a₀
    calc ∑ y, ‖STLKMg Cm n u H σ ![a₀, y]‖
        ≤ ∑ y, (‖loopM d (sz.L n) (sz.W n) Hb ζ σ ![a₀, y]‖ + ‖Cm.K n u σ ![a₀, y]‖) :=
          Finset.sum_le_sum fun y _ => hsplit _
      _ = _ := Finset.sum_add_distrib
      _ ≤ _ := by
          have := hLb a₀
          have := hKb a₀
          linarith

end Ward

/-! ## 3. The carrier hypotheses -/

section Main

variable {d : ℕ}

/-- **The carrier hypotheses of Lemma 3.9 (`lem:newKLK`)**, each through the family `mk` on the domain
(`0 < lam ≤ 𝔡⁻¹`, `κ ≤ Im m`, and `0 ≤ u < 1` where `u` occurs), with some constants `K_c, C_K ≥ 0`:
* the support of `S` is in `|x-y|_∞ ≤ 1`, the row sums of `‖S‖` are `≤ 1`, `‖S_{xy}‖ = ‖S_{yx}‖`;
* `‖m‖ ≤ 1`;
* the `Θ`-convolution over the block kernel: for every charge pair `(s, s')`,
  `Σ_b ‖thetaKer C n s s' u (a,b)‖ 𝒯̃(|b-a'|_∞) ≤ K_c/(1-u) 𝒯̃(|a-a'|_∞)` for every `ℓ', D' ≥ 0`, where
  `thetaKer = Step2Gen_thetaKer` (`X Θ_u(X)`, `X = M^{(ss')} S`, `C = mk sz (fun _ => E)`);
* the marginals of `𝒦^{(2)}`: `Σ_x ‖K_{(x,a₁)}‖ ≤ C_K W^{-d} (1-u)⁻¹` and the same in the second slot;
* the link: `LM` and the diagonal of `GMM` are the resolvent loop `loopFine` and `Gres - m` at some `ζ`,
  `Im ζ = (1-u) Im m`. -/
def NewKLKGenHyp (d : ℕ) (κ 𝔡 : ℝ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) : Prop :=
  ∃ K_c C_K : ℝ, 0 ≤ K_c ∧ 0 ≤ C_K ∧
  (∀ (sz : Sizes d) (n : ℕ) (E : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
      κ ≤ ((mk sz (fun _ => E)).m n).im →
      (∀ x y, (mk sz (fun _ => E)).S n x y ≠ 0 → zdistInf d (sz.L n) (x - y) ≤ 1) ∧
        (∀ x, ∑ y, ‖(mk sz (fun _ => E)).S n x y‖ ≤ 1) ∧
        (∀ x y, ‖(mk sz (fun _ => E)).S n x y‖ = ‖(mk sz (fun _ => E)).S n y x‖)) ∧
  (∀ (sz : Sizes d) (n : ℕ) (E : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
      κ ≤ ((mk sz (fun _ => E)).m n).im → ‖(mk sz (fun _ => E)).m n‖ ≤ 1) ∧
  (∀ (sz : Sizes d) (n : ℕ) (E u : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
      κ ≤ ((mk sz (fun _ => E)).m n).im → 0 ≤ u → u < 1 → ∀ (s s' : Bool) (ℓ' D' : ℝ), 0 ≤ ℓ' → 0 ≤ D' →
      ∀ a a' : Zd d (sz.L n),
        ∑ b, ‖Step2Gen_thetaKer (mk sz (fun _ => E)).toFlowFM n s s' u a b‖ *
          tailW d (sz.L n) (sz.lam n) u ℓ' ((sz.W n : ℕ) : ℝ) D' ((zdistInf d (sz.L n) (b - a') : ℕ) : ℝ) ≤
        K_c / (1 - u) *
          tailW d (sz.L n) (sz.lam n) u ℓ' ((sz.W n : ℕ) : ℝ) D' ((zdistInf d (sz.L n) (a - a') : ℕ) : ℝ)) ∧
  (∀ (sz : Sizes d) (n : ℕ) (E u : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
      κ ≤ ((mk sz (fun _ => E)).m n).im → 0 ≤ u → u < 1 → ∀ σ : Fin 2 → Bool,
      (∀ a₁ : Zd d (sz.L n), ∑ x, ‖(mk sz (fun _ => E)).K n u σ ![x, a₁]‖ ≤
        C_K * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 - u)⁻¹)) ∧
      (∀ a₀ : Zd d (sz.L n), ∑ y, ‖(mk sz (fun _ => E)).K n u σ ![a₀, y]‖ ≤
        C_K * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 - u)⁻¹))) ∧
  (∀ (sz : Sizes d) (n : ℕ) (E u : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
      κ ≤ ((mk sz (fun _ => E)).m n).im → 0 ≤ u → u < 1 →
      ∃ ζ : ℂ, ζ.im = (1 - u) * ((mk sz (fun _ => E)).m n).im ∧
        (∀ (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool)
          (a : Fin 2 → Zd d (sz.L n)), (mk sz (fun _ => E)).LM n u H σ a = loopFine d (sz.L n) (sz.W n) H ζ σ a) ∧
        (∀ (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (x : Idx d (sz.L n) (sz.W n)),
          (mk sz (fun _ => E)).GMM n u H x x = Gres H ζ true x x - (mk sz (fun _ => E)).m n))

end Main

end RBM.BA
