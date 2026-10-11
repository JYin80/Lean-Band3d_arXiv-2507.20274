/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.NewKLK
import RBM3D.Chain.Step2Gen
import RBM3D.BA.FlowPins

/-!
# `lem:newKLK` over the carrier (BA-T row T3, ticket T2405, Amend 1)

Design `docs/reports/T2379-design.md` §2 (row T3), §3; layout (A) (Amend 1 D1): a new file,
`Induction/NewKLK.lean` and `Induction/Step2K2.lean` are **not** edited, nothing imports this file.

* **Primed pins** `STNewKLKAtgL'`, `STNewKLKgL'`: `STNewKLKAtgL` / `STNewKLKgL`
  (`Chain/Step2Gen.lean:889-904`) with the single premise `|E| ≤ 2 - κ` replaced by the carrier
  datum `κ ≤ Im m` (the `m` of the family at `E`; the form the BA data carry).
* **Generic theorems** `stNewKLKAtgL'_of`, `stNewKLKgL'_of` (`δ₀ = κ/2`): the proof of `nkl_at`
  (`NewKLK.lean:993`) with `S`, `Θ`, `m`, `K`, `LM`, `GMM` read from the family `mk`.  The
  hypotheses are `NewKLKGenHyp` (F5-F9, all through `mk`): `S` support, row sum and symmetry
  (F5), `‖m‖ ≤ 1` (F6), the `SΘ`-convolution against `tailW` (F7), the marginals of `𝒦^{(2)}`
  (F8), and `LM`, `GMM` as the resolvent of `loopFine` at `ζ`, `Im ζ = (1-u) Im m` (F9).
* **Unprimed corollaries** `stNewKLKAtgL_of_primed`, `stNewKLKgL_of_primed` (Amend 1 D1′): at
  `κ' = κ/2` with the domain fact `|E| ≤ 2 - κ → κ/2 ≤ Im m`.
* **Band**: F5-F9 hold at `bandStep2Mat` (`NewKLKGen_band_hyp`), so the band pin `STNewKLK d` is
  re-derived through the generic theorem and `bandStep2_STNewKLK` (compiled `example`s, `d = 3`).

Opened private names of `Induction/NewKLK.lean` (`open private`, precedent `DuhamelII.lean:42`):
the tail shift/near/far lemmas, the distance lemmas, `nkl_ward_L`, `nkl_gres_blockMat_true`
(generic proof), and `nkl_SB_support`, `nkl_theta_tail`, `nkl_SBTheta_tail`, `nkl_SBTheta_row`,
`nkl_conv_P`, `nkl_ward_K`, `nkl_mE_zero`, `nkl_STGMM_zero` (band discharge and instances).
Copies of `nkl_conv_two` (:409), `nkl_bound2` (:840), `nkl_ward_LKM` (:759), `nkl_at` (:993),
adapted to a generic kernel and family (RBM3D `Induction/NewKLK.lean`, last commit b06ff9b;
no RBM1D/RBM2D text).
-/

set_option linter.style.longLine false

open private nkl_Cs_ge_one nkl_tailT_shift nkl_tailT_le_tailW nkl_tailW_eq_of_near nkl_tailW_far
  nkl_zdistInf_sub_comm nkl_zdistInf_tri nkl_dist_cases nkl_ward_L nkl_gres_blockMat_true
  nkl_SB_support nkl_theta_tail nkl_SBTheta_tail nkl_SBTheta_row nkl_conv_P nkl_ward_K nkl_mE_zero
  nkl_STGMM_zero from RBM3D.Induction.NewKLK

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The primed pins -/

/-- `STNewKLKAtgL'`: `STNewKLKAtgL` (`Chain/Step2Gen.lean:889`) with the premise `|E| ≤ 2 - κ` replaced by `κ ≤ Im m`, `m` the
one-loop value of the family at the constant sequence `fun _ => E` (the datum `BAReal` carries, `BA/MFixedPoint.lean:432`). -/
def STNewKLKAtgL' (d : ℕ) (κ 𝔡 C δ₀ : ℝ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E u D ℓ : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → κ ≤ ((mk sz (fun _ => E)).m n).im →
    0 ≤ u → u < 1 → 0 ≤ D → 0 ≤ ℓ → ℓ ≤ ((sz.L n : ℕ) : ℝ) →
    ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
      (∀ x y, ‖STGMMg (mk sz (fun _ => E)) n u H x y‖ ≤ δ₀) →
      ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖STthetaOpg (mk sz (fun _ => E)) n u σ (STLKMg (mk sz (fun _ => E)) n u H σ) a‖ ≤
            C / (1 - u) * STJhatMg (mk sz (fun _ => E)) n D ℓ u H * STprof sz n u D ℓ (a 0) (a 1) ∧
        ‖STELKLKMg (mk sz (fun _ => E)) n u H σ a‖ ≤
            C / (1 - u) * (STJhatMg (mk sz (fun _ => E)) n D ℓ u H +
              STJhatMg (mk sz (fun _ => E)) n D ℓ u H ^ 2 * (if 1 ≤ ℓ then 1 else 0)) *
              STprof sz n u D ℓ (a 0) (a 1)

/-- `STNewKLKgL'`: `∃ C δ₀` with `STNewKLKAtgL'` (the shape of `STNewKLKgL`, `Chain/Step2Gen.lean:903`). -/
def STNewKLKgL' (d : ℕ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ STNewKLKAtgL' d κ 𝔡 C δ₀ mk

/-! ## 2. The two convolution bounds over a generic kernel `S` -/

section Assembly

variable {d L : ℕ} [NeZero L] {g t : ℝ}

/-- **Bound 2 core, both factors near**, for a kernel `S` with `|x-y|_∞ ≤ 1` on its support and row sums `≤ 1`:
`Σ_{x,y} 𝒯(|x-a₁|) ‖S_{xy}‖ 𝒯(|a₀-y|) ≤ C_s C_T 𝒯(|a₀-a₁|)` (copy of `nkl_conv_two`, `NewKLK.lean:409`). -/
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


/-- **Bound 2, abstractly** (`3_5:626-654`): with `A_x = |F(x,a₁)|`, `B_y = |F(a₀,y)|`,
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

/-! ## 3. Ward marginals of `𝓛 - 𝒦` over the carrier -/

section Ward

open scoped Matrix

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz)

/-- **Ward bounds for `𝓛 - 𝒦` over the carrier** (every `σ`; copy of `nkl_ward_LKM`, `NewKLK.lean:759`): for Hermitian `H` with
`‖G_u - M‖_max ≤ κ/2`, `κ ≤ Im m`, both marginals of `‖(𝓛-𝒦)^{(2)}_{u,σ,(·,·)}‖` are at most `(4 + C_K) W^{-d} (1-u)⁻¹`,
given the marginals of `𝒦^{(2)}` (`C_K W^{-d} (1-u)⁻¹`) and the link F9 of `LM`, `GMM` to the resolvent at `ζ`. -/
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

/-! ## 4. The generic theorems -/

section Main

variable {d : ℕ}

/-- **The carrier facts F5-F9 of `lem:newKLK`** (the hypothesis of the generic theorems), each through the family `mk` on the
domain of the primed pin (`0 < lam ≤ 𝔡⁻¹`, `κ ≤ Im m`, and `0 ≤ u < 1` where `u` occurs), with some constants `K_c, C_K ≥ 0`:
* F5: the support of `S` is in `|x-y|_∞ ≤ 1`, the row sums of `‖S‖` are `≤ 1`, `‖S_{xy}‖ = ‖S_{yx}‖`;
* F6: `‖m‖ ≤ 1`;
* F7 (the `Θ`-convolution): `Σ_b ‖(SΘ_σ)(a,b)‖ 𝒯̃(|b-a'|_∞) ≤ K_c/(1-u) 𝒯̃(|a-a'|_∞)` for every `ℓ', D' ≥ 0`, where
  `Θ_σ = Step2Gen_Theta S (u m_{σ₀} m_{σ₁})`;
* F8 (marginals of `𝒦^{(2)}`): `Σ_x ‖K_{(x,a₁)}‖ ≤ C_K W^{-d} (1-u)⁻¹` and the same in the second slot;
* F9 (link): `LM` and the diagonal of `GMM` are the resolvent loop `loopFine` and `Gres - m` at some `ζ`,
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
      κ ≤ ((mk sz (fun _ => E)).m n).im → 0 ≤ u → u < 1 → ∀ (σ : Fin 2 → Bool) (ℓ' D' : ℝ), 0 ≤ ℓ' → 0 ≤ D' →
      ∀ a a' : Zd d (sz.L n),
        ∑ b, ‖((mk sz (fun _ => E)).S n * Step2Gen_Theta ((mk sz (fun _ => E)).S n)
            ((u : ℂ) * (STmsigg (mk sz (fun _ => E)) n (σ 0) * STmsigg (mk sz (fun _ => E)) n (σ 1)))) a b‖ *
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

/-- **`lem:newKLK` over the carrier at `δ₀ = κ/2`** (target 1; the proof of `nkl_at`, `NewKLK.lean:993`, with `S`, `Θ`, `m`,
`K`, `LM`, `GMM` read from the family `mk`): under `NewKLKGenHyp d κ 𝔡 mk` (constants `K_c, C_K`),
`C = 2 K_c + 2 C_s (4 + C_K) + C_s C_T` with `C_s = 2^{d-2} e` and `C_T` of `ekPropTInf_holds d` works. -/
theorem stNewKLKAtgL'_of (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ)
    (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) (hyp : NewKLKGenHyp d κ 𝔡 mk) :
    ∃ C : ℝ, 0 < C ∧ STNewKLKAtgL' d κ 𝔡 C (κ / 2) mk := by
  obtain ⟨K_c, C_K, hKc, hCK, hS, hm, hconv, hK, hlink⟩ := hyp
  obtain ⟨CT, hCT, HT⟩ := ekPropTInf_holds d hd
  have hCs := nkl_Cs_ge_one (d := d)
  set Cs : ℝ := 2 ^ (d - 2) * Real.exp 1 with hCsdef
  have hCs0 : 0 < Cs := by linarith
  refine ⟨2 * K_c + 2 * Cs * (4 + C_K) + Cs * CT, by positivity, ?_⟩
  intro sz n E u D ℓ hlam hlam' hIm hu0 hu1 hD hℓ0 hℓL H hH hGM σ a
  set Cm := mk sz (fun _ => E) with hCm
  have hL : 3 ≤ sz.L n := sz.three_le_L n
  have hv : 0 < 1 - u := by linarith
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := Nat.cast_pos.2 (sz.W_pos n)
  set Wr : ℝ := ((sz.W n : ℕ) : ℝ) with hWr
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
  -- the data of `mk`
  obtain ⟨hsupp, hrow, hsym⟩ := hS sz n E hlam hlam' hIm
  have hmn : ‖Cm.m n‖ ≤ 1 := hm sz n E hlam hlam' hIm
  have hms : ∀ s : Bool, ‖STmsigg Cm n s‖ ≤ 1 := fun s => by
    cases s <;> simpa [STmsigg] using hmn
  have hmσ : ‖STmsigg Cm n (σ 0) * STmsigg Cm n (σ 1)‖ ≤ 1 := by
    rw [norm_mul]
    calc ‖STmsigg Cm n (σ 0)‖ * ‖STmsigg Cm n (σ 1)‖ ≤ 1 * 1 :=
          mul_le_mul (hms _) (hms _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hTTT : ∀ x y : Zd d (sz.L n), ∑ z : Zd d (sz.L n),
      tailT d (sz.L n) g u ((zdistInf d (sz.L n) (x - z) : ℕ) : ℝ) *
        tailT d (sz.L n) g u ((zdistInf d (sz.L n) (z - y) : ℕ) : ℝ) ≤
      (CT / (1 - u)) * tailT d (sz.L n) g u ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) :=
    fun x y => HT (sz.L n) g u u hlam hu0 le_rfl hu1 (le_total _ _) x y
  have hCT' : 0 ≤ CT / (1 - u) := by positivity
  set SΘ : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ := Cm.S n *
    Step2Gen_Theta (Cm.S n) ((u : ℂ) * (STmsigg Cm n (σ 0) * STmsigg Cm n (σ 1))) with hSΘdef
  -- Bound 1
  set K : ℝ := K_c / (1 - u) with hKdef
  have hK1 : ∀ p q : Zd d (sz.L n), ∑ b, ‖SΘ p b‖ * P ((zdistInf d (sz.L n) (b - q) : ℕ) : ℝ) ≤
      K * P ((zdistInf d (sz.L n) (p - q) : ℕ) : ℝ) :=
    fun p q => hconv sz n E u hlam hlam' hIm hu0 hu1 σ ℓ D hℓ0 hD p q
  have hK0 : 0 ≤ K := by positivity
  have hconvJ : ∀ p q : Zd d (sz.L n), ∑ b, ‖SΘ p b‖ *
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
  have hC2 : 2 * K = 2 * K_c / (1 - u) := by rw [hKdef]; field_simp
  have hB1 : ‖STthetaOpg Cm n u σ (STLKMg Cm n u H σ) a‖ ≤
      (2 * K_c) / (1 - u) * J * STprof sz n u D ℓ (a 0) (a 1) := by
    unfold STthetaOpg
    have hterm : ∀ i : Fin 2, ‖∑ b, (STmsigg Cm n (σ 0) * STmsigg Cm n (σ 1)) * (SΘ (a i) b) *
        STLKMg Cm n u H σ (Function.update a i b)‖ ≤
        ∑ b, ‖SΘ (a i) b‖ *
          (J * STprof sz n u D ℓ ((Function.update a i b) 0) ((Function.update a i b) 1)) := by
      intro i
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      rw [norm_mul, norm_mul]
      calc ‖STmsigg Cm n (σ 0) * STmsigg Cm n (σ 1)‖ * ‖SΘ (a i) b‖ *
            ‖STLKMg Cm n u H σ (Function.update a i b)‖
          ≤ 1 * ‖SΘ (a i) b‖ * ‖STLKMg Cm n u H σ (Function.update a i b)‖ := by
            gcongr
        _ = ‖SΘ (a i) b‖ * ‖STLKMg Cm n u H σ (Function.update a i b)‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hF σ _) (norm_nonneg _)
    rw [Fin.sum_univ_two]
    refine (norm_add_le _ _).trans ((add_le_add (hterm 0) (hterm 1)).trans ?_)
    have e0 : ∀ b, (Function.update a 0 b) 0 = b := fun b => by simp
    have e0' : ∀ b, (Function.update a 0 b) 1 = a 1 := fun b => by simp
    have e1 : ∀ b, (Function.update a 1 b) 0 = a 0 := fun b => by simp
    have e1' : ∀ b, (Function.update a 1 b) 1 = b := fun b => by simp
    simp only [e0, e0', e1, e1', hprof]
    have t0 := hconvJ (a 0) (a 1)
    have t1 : ∑ b, ‖SΘ (a 1) b‖ * (J * ((Wr ^ d)⁻¹ *
        P ((zdistInf d (sz.L n) (a 0 - b) : ℕ) : ℝ))) ≤
        K * J * ((Wr ^ d)⁻¹ * P ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) := by
      have h := hconvJ (a 1) (a 0)
      rw [nkl_zdistInf_sub_comm (a 1) (a 0)] at h
      calc _ = ∑ b, ‖SΘ (a 1) b‖ * (J * ((Wr ^ d)⁻¹ *
              P ((zdistInf d (sz.L n) (b - a 0) : ℕ) : ℝ))) :=
            Finset.sum_congr rfl fun b _ => by rw [nkl_zdistInf_sub_comm (a 0) b]
        _ ≤ _ := h
    have hfin : K * J * ((Wr ^ d)⁻¹ * P ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) +
        K * J * ((Wr ^ d)⁻¹ * P ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) =
        2 * K_c / (1 - u) * J *
          ((Wr ^ d)⁻¹ * P ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) := by
      rw [← hC2]; ring
    linarith
  -- Bound 2
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
  have key := NewKLKGen_bound2 hsupp hrow hsym (g := g) (t := u) (ℓ := ℓ) (D := D) (CT := CT / (1 - u))
    hWpos hℓ0 hJ0 (cW := (Wr ^ d)⁻¹) (by positivity) (fun x => ‖STLKMg Cm n u H σ ![x, a 1]‖)
    (fun y => ‖STLKMg Cm n u H σ ![a 0, y]‖) (fun x => norm_nonneg _) (fun y => norm_nonneg _)
    (a 0) (a 1) hA hB (hSumA (a 1)) (hSumB (a 0)) hTTT
  have hB2 : ‖STELKLKMg Cm n u H σ a‖ ≤ Wr ^ d *
      (2 * (J * (Wr ^ d)⁻¹ * Cs * P ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) *
          ((4 + C_K) * ((Wr ^ d)⁻¹ * (1 - u)⁻¹)) +
        (if 1 ≤ ℓ then (J * (Wr ^ d)⁻¹) ^ 2 * (Cs * ((CT / (1 - u)) *
          tailT d (sz.L n) g u ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ))) else 0)) := by
    unfold STELKLKMg
    rw [norm_mul, hWd]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun x _ => norm_sum_le _ _).trans ?_)
    refine le_trans (Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_) key
    rw [norm_mul, norm_mul]
  -- the constants
  have hw : 0 < Wr ^ d := by positivity
  set Q2 : ℝ := 2 * Cs * (4 + C_K) with hQ2
  set Cc : ℝ := 2 * K_c + Q2 + Cs * CT with hCc
  have hQ20 : 0 ≤ Q2 := by rw [hQ2]; positivity
  have hCc1 : 0 ≤ Cc - 2 * K_c := by
    rw [hCc]; have := mul_pos hCs0 hCT; linarith
  have hCc2 : 0 ≤ Cc - Q2 := by
    rw [hCc]; linarith [mul_nonneg hCs0.le hCT.le]
  have hCc3 : 0 ≤ Cc - Cs * CT := by
    rw [hCc]; linarith
  set Ps : ℝ := P ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) with hPs
  set Ts : ℝ := tailT d (sz.L n) g u ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) with hTs
  have hTsP : Ts ≤ Ps := nkl_tailT_le_tailW hℓ0 (Nat.cast_nonneg _)
  have hTs0 : 0 ≤ Ts := tailT_nonneg (Nat.cast_nonneg _)
  have hPs0 : 0 < Ps := hP0 _
  have hpr : STprof sz n u D ℓ (a 0) (a 1) = (Wr ^ d)⁻¹ * Ps := hprof _ _
  have hpr0 : 0 < (Wr ^ d)⁻¹ * Ps := by positivity
  have e1 : Wr ^ d * (2 * (J * (Wr ^ d)⁻¹ * Cs * Ps) * ((4 + C_K) * ((Wr ^ d)⁻¹ * (1 - u)⁻¹))) =
      Q2 / (1 - u) * J * ((Wr ^ d)⁻¹ * Ps) := by
    rw [hQ2]
    field_simp
  have e2 : Wr ^ d * ((J * (Wr ^ d)⁻¹) ^ 2 * (Cs * (CT / (1 - u) * Ts))) =
      Cs * CT / (1 - u) * J ^ 2 * ((Wr ^ d)⁻¹ * Ts) := by
    field_simp
  refine ⟨?_, ?_⟩
  · rw [hpr] at hB1 ⊢
    refine hB1.trans ?_
    have h1 : 2 * K_c / (1 - u) ≤ Cc / (1 - u) :=
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
          (Q2 / (1 - u) * J * ((Wr ^ d)⁻¹ * Ps) +
            Cs * CT / (1 - u) * J ^ 2 * ((Wr ^ d)⁻¹ * Ps)) =
          (Cc - Q2) / (1 - u) * J * ((Wr ^ d)⁻¹ * Ps) +
            (Cc - Cs * CT) / (1 - u) * J ^ 2 * ((Wr ^ d)⁻¹ * Ps) := by ring
      have hn1 : 0 ≤ (Cc - Q2) / (1 - u) * J * ((Wr ^ d)⁻¹ * Ps) := by
        have := div_nonneg hCc2 hv.le; positivity
      have hn2 : 0 ≤ (Cc - Cs * CT) / (1 - u) * J ^ 2 * ((Wr ^ d)⁻¹ * Ps) := by
        have := div_nonneg hCc3 hv.le; positivity
      linarith
    · simp only [h1, ite_false, mul_zero, add_zero, mul_zero]
      have hdiff : Cc / (1 - u) * (J + J ^ 2 * 0) * ((Wr ^ d)⁻¹ * Ps) -
          Q2 / (1 - u) * J * ((Wr ^ d)⁻¹ * Ps) =
          (Cc - Q2) / (1 - u) * J * ((Wr ^ d)⁻¹ * Ps) := by ring
      have hn1 : 0 ≤ (Cc - Q2) / (1 - u) * J * ((Wr ^ d)⁻¹ * Ps) := by
        have := div_nonneg hCc2 hv.le; positivity
      linarith

/-- **Target 1, pointwise form**: `STNewKLKAtgL'` at the constant that `stNewKLKAtgL'_of` chooses (the shape of
`stNewKLKAt_holds`, the conclusion the registry scan of `Test/Axioms.lean` looks for). -/
theorem stNewKLKAtgL'_holds (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ)
    (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) (hyp : NewKLKGenHyp d κ 𝔡 mk) :
    STNewKLKAtgL' d κ 𝔡 (stNewKLKAtgL'_of hd κ 𝔡 hκ mk hyp).choose (κ / 2) mk :=
  (stNewKLKAtgL'_of hd κ 𝔡 hκ mk hyp).choose_spec.2

/-- **Target 2**: `STNewKLKgL' d mk` from the facts, quantified as the pin quantifies `κ 𝔡` (the constants `K_c, C_K` of
`NewKLKGenHyp` may depend on `(κ, 𝔡)`); `δ₀ = κ/2`. -/
theorem stNewKLKgL'_of (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz)
    (h : 3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → NewKLKGenHyp d κ 𝔡 mk) :
    STNewKLKgL' d mk := by
  intro hd κ 𝔡 hκ h𝔡
  obtain ⟨C, hC, hAt⟩ := stNewKLKAtgL'_of hd κ 𝔡 hκ mk (h hd κ 𝔡 hκ h𝔡)
  exact ⟨C, κ / 2, hC, by positivity, hAt⟩

/-! ## 5. The unprimed pins as corollaries (Amend 1 D1′) -/

/-- **`STNewKLKAtgL` from `STNewKLKAtgL'` at `κ/2`**: given the domain fact `|E| ≤ 2 - κ → κ/2 ≤ Im m`. -/
theorem stNewKLKAtgL_of_primed {κ 𝔡 C δ₀ : ℝ} {mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz}
    (h : STNewKLKAtgL' d (κ / 2) 𝔡 C δ₀ mk)
    (hdom : ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → |E| ≤ 2 - κ →
      κ / 2 ≤ ((mk sz (fun _ => E)).m n).im) :
    STNewKLKAtgL d κ 𝔡 C δ₀ mk :=
  fun sz n E u D ℓ hlam hlam' hE hu0 hu1 hD hℓ0 hℓL H hH hGM σ a =>
    h sz n E u D ℓ hlam hlam' (hdom sz n E hlam hlam' hE) hu0 hu1 hD hℓ0 hℓL H hH hGM σ a

/-- **`STNewKLKgL` from `STNewKLKgL'`**: apply the primed pin at `κ' = κ/2` (so `δ₀ = κ/4` for `stNewKLKgL'_of`), given the
domain fact `|E| ≤ 2 - κ → κ/2 ≤ Im m` for every `κ, 𝔡 > 0`. -/
theorem stNewKLKgL_of_primed {mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz} (h : STNewKLKgL' d mk)
    (hdom : ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
      |E| ≤ 2 - κ → κ / 2 ≤ ((mk sz (fun _ => E)).m n).im) :
    STNewKLKgL d mk := by
  intro hd κ 𝔡 hκ h𝔡
  obtain ⟨C, δ₀, hC, hδ, hAt⟩ := h hd (κ / 2) 𝔡 (half_pos hκ) h𝔡
  exact ⟨C, δ₀, hC, hδ, stNewKLKAtgL_of_primed hAt (hdom κ 𝔡 hκ h𝔡)⟩

end Main

/-! ## 6. The band family: F5-F9 hold at `bandStep2Mat` -/

section Band

variable {d : ℕ}

/-- **F5-F9 at the band family** `fun sz E => bandStep2Mat sz E`, for `3 ≤ d`, `κ > 0`: the facts are the merged band lemmas
(`nkl_SB_support`, `sum_norm_SB_row`, `SB_transpose`; `norm_mE`; `prop5Decay_holds` with `nkl_theta_tail`, `nkl_SBTheta_*`,
`nkl_conv_P`, `ekPropTInf_holds`; `nkl_ward_K`; `zt_im`), with `K_c = C₁ C_s C_T + C_s`, `C_K = 1`.  This is a
proof at the band only; at BA the facts are owed to T3-BA. -/
theorem newKLKGenHyp_band (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) :
    NewKLKGenHyp d κ 𝔡 (fun sz E => bandStep2Mat sz E) := by
  obtain ⟨C₅, hC₅, c, hc, H5⟩ := prop5Decay_holds d 𝔡⁻¹ hd (inv_pos.2 h𝔡)
  obtain ⟨CT, hCT, HT⟩ := ekPropTInf_holds d hd
  have hCs := nkl_Cs_ge_one (d := d)
  set C₁ : ℝ := C₅ * Real.exp (1 / (4 * c)) with hC₁
  set Cs : ℝ := 2 ^ (d - 2) * Real.exp 1 with hCsdef
  have hC₁0 : 0 < C₁ := by positivity
  have hCs0 : 0 < Cs := by linarith
  have hE2 : ∀ E : ℝ, κ ≤ (mE E).im → |E| ≤ 2 := by
    intro E h
    rw [mE_im] at h
    have h0 : 0 < Real.sqrt (4 - E ^ 2) := by linarith
    have h1 : 0 < 4 - E ^ 2 := Real.sqrt_pos.1 h0
    exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
  unfold NewKLKGenHyp
  refine ⟨C₁ * Cs * CT + Cs, 1, by positivity, zero_le_one, ?_, ?_, ?_, ?_, ?_⟩
  · -- F5
    intro sz n E hlam hlam' hIm
    refine ⟨fun x y h => nkl_SB_support _ h, fun x => (sum_norm_SB_row d _ _ (sz.three_le_L n) x).le,
      fun x y => ?_⟩
    have h := congrFun (congrFun (SB_transpose d (sz.L n) (sz.lam n)) x) y
    simp only [Matrix.transpose_apply] at h
    exact congrArg norm h.symm
  · -- F6
    intro sz n E hlam hlam' hIm
    exact (norm_mE (hE2 E hIm)).le
  · -- F7
    intro sz n E u hlam hlam' hIm hu0 hu1 σ ℓ' D' hℓ' hD' a a'
    have hE := hE2 E hIm
    have hL : 3 ≤ sz.L n := sz.three_le_L n
    have hv : 0 < 1 - u := by linarith
    have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := Nat.cast_pos.2 (sz.W_pos n)
    have hm : ‖mSigma E (σ 0) * mSigma E (σ 1)‖ = 1 := by
      rw [norm_mul, norm_mSigma hE, norm_mSigma hE, mul_one]
    have hξ : ‖(u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))‖ < 1 :=
      norm_mul_mSigma_lt_one hE hu0 hu1 (σ 0) (σ 1)
    have hΘ : ∀ x y : Zd d (sz.L n),
        ‖Theta d (sz.L n) (sz.lam n) ((u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) x y‖ ≤
          C₁ * tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) :=
      nkl_theta_tail hC₅ hc hL hξ
        (fun x => H5 (sz.L n) hL (sz.lam n) hlam hlam' u hu0 hu1 (mE E) (norm_mE hE) (σ 0) (σ 1) x)
    have hrowΘ : ∀ x : Zd d (sz.L n),
        ∑ b, ‖Theta d (sz.L n) (sz.lam n) ((u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) x b‖ ≤ (1 - u)⁻¹ :=
      fun x => sum_norm_Theta_row_le hL hu0 hu1 hm x
    have hTTT : ∀ x y : Zd d (sz.L n), ∑ z : Zd d (sz.L n),
        tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (x - z) : ℕ) : ℝ) *
          tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (z - y) : ℕ) : ℝ) ≤
        (CT / (1 - u)) * tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) :=
      fun x y => HT (sz.L n) (sz.lam n) u u hlam hu0 le_rfl hu1 (le_total _ _) x y
    have hconv := nkl_conv_P (t := u) (ℓ := ℓ') (W := ((sz.W n : ℕ) : ℝ)) (D := D') hL hWpos hℓ'
      (Q := C₁ * Cs) (CT := CT / (1 - u)) (c := (1 - u)⁻¹) (by positivity) (by positivity)
      (nkl_SBTheta_tail (t := u) hL hC₁0.le hΘ) (nkl_SBTheta_row hL hrowΘ) hTTT a a'
    have e : C₁ * Cs * (CT / (1 - u)) + Cs * (1 - u)⁻¹ = (C₁ * Cs * CT + Cs) / (1 - u) := by
      field_simp
    rw [e] at hconv
    exact hconv
  · -- F8
    intro sz n E u hlam hlam' hIm hu0 hu1 σ
    obtain ⟨ha, hb⟩ := nkl_ward_K sz n (hE2 E hIm) hu0 hu1 σ
    exact ⟨fun a₁ => by rw [one_mul]; exact ha a₁, fun a₀ => by rw [one_mul]; exact hb a₀⟩
  · -- F9
    intro sz n E u hlam hlam' hIm hu0 hu1
    refine ⟨zt E u, zt_im E u, fun H σ a => rfl, fun H x => ?_⟩
    change STGMM sz n E u H x x = _
    unfold STGMM
    simp
    rfl

end Band

/-! ## 7. Compiled nonempty instances (`d = 3`)

The band family `fun sz E => bandStep2Mat sz E` satisfies F5-F9 for every `κ, 𝔡 > 0` (§6), so target 2 holds at the band;
target 1 is applied at `κ = 𝔡 = 1/10`; the band pin `STNewKLK d` is re-derived through the generic theorem, the corollary of
§5 (`κ' = κ/2`, domain fact `Ind.half_le_mE_im`) and `bandStep2_STNewKLK`.  The pointwise instance is the merged preflight
sequence `sz0` (`L = 4`, `W = 32`, `lam = 1/64`) at `n = 0`, `E = 0` (`m = i`), `u = 1/32`, `D = 1`, `ℓ = 2` (the indicator
`1_{ℓ≥1}` is on), `H = 0`: `‖G_u - M‖_max = u/(1-u) = 1/31 ≤ 1/20 = δ₀`, so `G_u ≠ M`. -/

section Inst

/-- **Target 2 at the band**: every deterministic hypothesis of `stNewKLKgL'_of` is discharged (`d = 3`). -/
example : STNewKLKgL' 3 (fun sz E => bandStep2Mat sz E) :=
  stNewKLKgL'_of _ fun hd κ 𝔡 hκ h𝔡 => newKLKGenHyp_band hd κ 𝔡 hκ h𝔡

/-- **Target 1 at the band**: `d = 3`, `κ = 𝔡 = 1/10`, `δ₀ = 1/20`. -/
example : ∃ C : ℝ, 0 < C ∧ STNewKLKAtgL' 3 (1 / 10) (1 / 10) C (1 / 20) (fun sz E => bandStep2Mat sz E) := by
  obtain ⟨C, hC, h⟩ := stNewKLKAtgL'_of (d := 3) (by norm_num) (1 / 10) (1 / 10) (by norm_num) _
    (newKLKGenHyp_band (d := 3) (by norm_num) (1 / 10) (1 / 10) (by norm_num) (by norm_num))
  refine ⟨C, hC, ?_⟩
  have e : (1 / 10 : ℝ) / 2 = 1 / 20 := by norm_num
  rw [e] at h
  exact h

/-- **The band pin through the generic theorem** (target 6): `STNewKLK d` from target 2, the corollary and the bridge
`bandStep2_STNewKLK`; the domain fact is `Ind.half_le_mE_im`. -/
example (d : ℕ) : STNewKLK d :=
  (bandStep2_STNewKLK d).mpr (stNewKLKgL_of_primed
    (stNewKLKgL'_of _ fun hd κ 𝔡 hκ h𝔡 => newKLKGenHyp_band hd κ 𝔡 hκ h𝔡)
    fun _ _ hκ _ _ _ _ _ _ hE => Ind.half_le_mE_im hκ.le hE)

open RBM.Gauss.SizesInst in
/-- The band carrier at `sz0`, `E ≡ 0`. -/
private abbrev NewKLKGen_cm0 : Step2Mat sz0 := bandStep2Mat sz0 (fun _ => 0)

open RBM.Gauss.SizesInst in
/-- The matrix `H = 0` at `sz0`, `n = 0`. -/
private abbrev NewKLKGen_H0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ := 0

open RBM.Gauss.SizesInst in
/-- **Target 1, pointwise**: the two bounds at `sz0`, `n = 0`, `E = 0`, `u = 1/32`, `D = 1`, `ℓ = 2`, `H = 0`, all `σ`, `a`. -/
example : ∃ C : ℝ, 0 < C ∧ ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L 0)),
    ‖STthetaOpg NewKLKGen_cm0 0 (1 / 32) σ (STLKMg NewKLKGen_cm0 0 (1 / 32) NewKLKGen_H0 σ) a‖ ≤
        C / (1 - 1 / 32) * STJhatMg NewKLKGen_cm0 0 1 2 (1 / 32) NewKLKGen_H0 *
          STprof sz0 0 (1 / 32) 1 2 (a 0) (a 1) ∧
      ‖STELKLKMg NewKLKGen_cm0 0 (1 / 32) NewKLKGen_H0 σ a‖ ≤
        C / (1 - 1 / 32) * (STJhatMg NewKLKGen_cm0 0 1 2 (1 / 32) NewKLKGen_H0 +
          STJhatMg NewKLKGen_cm0 0 1 2 (1 / 32) NewKLKGen_H0 ^ 2 * (if 1 ≤ (2 : ℝ) then 1 else 0)) *
          STprof sz0 0 (1 / 32) 1 2 (a 0) (a 1) := by
  obtain ⟨C, hC, h⟩ := stNewKLKAtgL'_of (d := 3) (by norm_num) (1 / 10) (1 / 10) (by norm_num) _
    (newKLKGenHyp_band (d := 3) (by norm_num) (1 / 10) (1 / 10) (by norm_num) (by norm_num))
  have hlam : 0 < sz0.lam 0 := by simp [sz0]
  have hlam' : sz0.lam 0 ≤ ((1 : ℝ) / 10)⁻¹ := by
    have : sz0.lam 0 = 1 / 64 := by norm_num [sz0]
    rw [this]; norm_num
  have hL4 : (2 : ℝ) ≤ ((sz0.L 0 : ℕ) : ℝ) := by norm_num [sz0]
  have hIm : (1 / 10 : ℝ) ≤ ((bandStep2Mat sz0 fun _ => 0).m 0).im := by
    change (1 / 10 : ℝ) ≤ (mE 0).im
    rw [nkl_mE_zero]; norm_num
  refine ⟨C, hC, fun σ a => ?_⟩
  exact h sz0 0 0 (1 / 32) 1 2 hlam hlam' hIm (by norm_num) (by norm_num) zero_le_one (by norm_num) hL4 0
    Matrix.isHermitian_zero
    (fun x y => (nkl_STGMM_zero sz0 0 (by norm_num) (by norm_num) x y).trans (by norm_num)) σ a

/-- A statement-level block Anderson family over `baFM sz sz.lam E` (`S = 1`, `m = BAmF`): `LM` is the resolvent loop at
`ztOf (BAmF ..)`, `GMM = Gres - M`; the fields `LIM`, `KI`, `Pp`, `Hpath` are inert.  No BA fact is proved here (T3-BA). -/
private def NewKLKGen_baMk {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) : Step2Mat sz where
  toFlowFM := baFM sz sz.lam E
  LM := fun n u {_k} H σ a => loopFine d (sz.L n) (sz.W n) H (ztOf (BAmF sz sz.lam E n) (E n) u) σ a
  GMM := fun n u H x y => Gres H (ztOf (BAmF sz sz.lam E n) (E n) u) true x y - BAMfine sz sz.lam E n x y
  LIM := fun _ _ _ _ => 0
  KI := fun _ _ _ => 0
  Pp := 0
  Hpath := fun _ _ _ _ _ _ => 0

/-- **Target 1 elaborates at a BA family** (statement level): the BA facts F5-F9 are the hypothesis `hyp` (owed to T3-BA). -/
example (κ 𝔡 : ℝ) (hκ : 0 < κ) (hyp : NewKLKGenHyp 3 κ 𝔡 (fun sz E => NewKLKGen_baMk sz E)) :
    ∃ C : ℝ, 0 < C ∧ STNewKLKAtgL' 3 κ 𝔡 C (κ / 2) (fun sz E => NewKLKGen_baMk sz E) :=
  stNewKLKAtgL'_of (by norm_num) κ 𝔡 hκ _ hyp

end Inst

end RBM.BA
