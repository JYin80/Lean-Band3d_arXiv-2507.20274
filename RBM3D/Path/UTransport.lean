/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Path.UBounds
import RBM3D.Defs.Sizes

/-!
# Transport by the `𝒰` kernel: local-maximum bounds

Ticket T2097 (ST2-25, part 2).  Port of `RBM2D/Path/UTransport.lean` at commit `c9a24cf` (cited
`UTransport:<line>`): the pinned definitions `UkerFar`, `UopLocalMax`, `UopPairLocalMax`
(`UTransport:46`, `:51`, `:61`) and their proofs (`:170`, `:235`).  Paper: arXiv:2507.20274,
`3_5_Loop_Hierarchy.tex:2357` (`neiwuj`, which is proved from `lem:sum_Ndecay` (`:1620`), `prop:ThfadC`
and calculus, `:2364`).  The statements here are the deterministic near/far splitting behind that
proof; the paper has no label for them (RBM2D's `res_deccalE_0`, `res_deccalE_3` do not exist in
this paper).

`tailtoTail` (`UTransport:422`) and its lemmas `uT_scalar` (`:364`), `uT_zdist_neg`, `uT_near_far`
(`:336`, `:348`) are **not ported** (ticket `T2097.md` Amend 1, DECISIONS §33): the d = 2 statement is
false at `d ≥ 3` (the preflight, `docs/reports/T2097-prove.md` (a) part C, shows the ratio
`≈ ρ_η = (1-s)/(1-t)`, and growth with `L` at `ℓ_t = L`).

Renaming (`docs/tickets/ST1-COMMON.md` item 2, 3): `Z2 L` becomes `Zd d L`; `zdist2` becomes the
`L^∞` distance `zdistInf d L` (stochastic and endpoint statements); `ukerMat L`, `Uop L` become
`ukerMat d L g`, `Uop d L g` with `g` an explicit coupling.  The one `d = 2` count is the number of
far sites: `card (Zd d L) = L^d` replaces `card (Z2 L) = L²` (`UTransport:147`); the near-label
weight `((1-u)/(1-v))^k` is dimension free (row sums, `ukerRowSum`).
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Path

open RBM RBM.Gauss

/-! ## Pinned definitions (probe text) -/

/-- The far-kernel condition: `(Θ_u^{-1}Θ_v)_{ab} ≤ W^{-D'}` for `|a - b|_L ≥ R`
(supplied by `KellStarEv`). -/
def UkerFar (d L W : ℕ) [NeZero L] (g u v R D' : ℝ) : Prop :=
  ∀ a b : Zd d L, R ≤ (zdistInf d L (a - b) : ℝ) → ‖ukerMat d L g 1 u v a b‖ ≤ (W : ℝ) ^ (-D')

/-- **Pin E.5f (transport by the local maximum)**, 5-6:400–406: near labels carry the weight
`((1-u)/(1-v))²`, far labels cost `2 L² W^{-D'} (1-u)/(1-v) ‖A‖_max`. -/
def UopLocalMax (d : ℕ) (g : ℝ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ u v R D' : ℝ, 0 ≤ u → u ≤ v → v < 1 →
    UkerFar d L W g u v R D' → ∀ (A : Zd d L × Zd d L → ℂ) (α β : ℝ) (a : Zd d L × Zd d L), 0 ≤ β →
      (∀ b, ‖A b‖ ≤ α) →
      (∀ b : Zd d L × Zd d L, (zdistInf d L (a.1 - b.1) : ℝ) < R → (zdistInf d L (a.2 - b.2) : ℝ) < R →
        ‖A b‖ ≤ β) →
      ‖Uop d L g 1 u v A a‖ ≤
        ((1 - u) / (1 - v)) ^ 2 * β + 2 * (L : ℝ) ^ d * (W : ℝ) ^ (-D') * ((1 - u) / (1 - v)) * α

/-- **Pin E.5g (the same for `𝒰 ⊗ 𝒰̄`)**, used by the QV (`res_deccalE_3`, 5-6:433). -/
def UopPairLocalMax (d : ℕ) (g : ℝ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ u v R D' : ℝ, 0 ≤ u → u ≤ v → v < 1 →
    UkerFar d L W g u v R D' →
    ∀ (A : Zd d L × Zd d L → Zd d L × Zd d L → ℂ) (α β : ℝ) (a : Zd d L × Zd d L), 0 ≤ β →
      (∀ b b', ‖A b b'‖ ≤ α) →
      (∀ b b' : Zd d L × Zd d L, (zdistInf d L (a.1 - b.1) : ℝ) < R → (zdistInf d L (a.2 - b.2) : ℝ) < R →
        (zdistInf d L (a.1 - b'.1) : ℝ) < R → (zdistInf d L (a.2 - b'.2) : ℝ) < R → ‖A b b'‖ ≤ β) →
      ‖∑ b : Zd d L × Zd d L, ∑ b' : Zd d L × Zd d L,
          ukerMat d L g 1 u v a.1 b.1 * ukerMat d L g 1 u v a.2 b.2 *
            (starRingEnd ℂ) (ukerMat d L g 1 u v a.1 b'.1 * ukerMat d L g 1 u v a.2 b'.2) * A b b'‖ ≤
        ((1 - u) / (1 - v)) ^ 4 * β +
          4 * (L : ℝ) ^ d * (W : ℝ) ^ (-D') * ((1 - u) / (1 - v)) ^ 3 * α

/-! ## Private helpers -/

section Helpers

variable (d L : ℕ) [NeZero L] (g : ℝ)

/-- `‖z‖ = re z` for `im z = 0`, `0 ≤ re z`. -/
private theorem uT_norm_eq_re_of {z : ℂ} (him : z.im = 0) (hre : 0 ≤ z.re) : ‖z‖ = z.re := by
  have hz : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using him)
  calc ‖z‖ = ‖(z.re : ℂ)‖ := congrArg norm hz
    _ = z.re := Complex.norm_of_nonneg hre

/-- The row `ℓ¹` norm of `ukerMat d L g 1 u v` is the row sum `(1 - u)/(1 - v)` (`ukerNonneg`,
`ukerRowSum` at `ξ = 1`). -/
private theorem uT_row_sum (hL : 3 ≤ L) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v < 1)
    (x : Zd d L) : ∑ c : Zd d L, ‖ukerMat d L g 1 u v x c‖ = (1 - u) / (1 - v) := by
  have hvξ : v * (1 : ℝ) < 1 := by rw [mul_one]; exact hv
  have hn : ∀ c : Zd d L, ‖ukerMat d L g 1 u v x c‖ = (ukerMat d L g 1 u v x c).re := by
    intro c
    have h := ukerNonneg d g L hL 1 u v zero_le_one hu huv hvξ x c
    rw [Complex.ofReal_one] at h
    exact uT_norm_eq_re_of h.1 h.2
  simp_rw [hn]
  have hs := ukerRowSum d g L hL 1 u v zero_le_one (hu.trans huv) hvξ x
  rw [Complex.ofReal_one] at hs
  have hre := congrArg Complex.re hs
  rw [Complex.re_sum, Complex.ofReal_re] at hre
  simpa only [mul_one] using hre

/-- The far indicator `1[R ≤ |a - c|_L]` as a real number. -/
private def uTF (a : Zd d L) (R : ℝ) (c : Zd d L) : ℝ :=
  if R ≤ (zdistInf d L (a - c) : ℝ) then 1 else 0

omit [NeZero L] in
private theorem uTF_nonneg (a : Zd d L) (R : ℝ) (c : Zd d L) : 0 ≤ uTF d L a R c := by
  unfold uTF; split_ifs <;> norm_num

omit [NeZero L] in
private theorem uTF_eq_one {a : Zd d L} {R : ℝ} {c : Zd d L} (h : R ≤ (zdistInf d L (a - c) : ℝ)) :
    uTF d L a R c = 1 := by
  unfold uTF; simp [h]

omit [NeZero L] in
private theorem uTF_eq_zero {a : Zd d L} {R : ℝ} {c : Zd d L} (h : (zdistInf d L (a - c) : ℝ) < R) :
    uTF d L a R c = 0 := by
  unfold uTF; simp [not_le.2 h]

/-- The far part of a nonnegative weight with pointwise far bound `δ` costs at most `L² δ`
(only `card (Zd d L) = L²` is used). -/
private theorem uT_far_sum_le (a : Zd d L) (R δ : ℝ) (hδ : 0 ≤ δ) (k : Zd d L → ℝ)
    (hk : ∀ c, R ≤ (zdistInf d L (a - c) : ℝ) → k c ≤ δ) :
    ∑ c : Zd d L, k c * uTF d L a R c ≤ (L : ℝ) ^ d * δ := by
  have hterm : ∀ c : Zd d L, k c * uTF d L a R c ≤ δ := by
    intro c
    by_cases h : R ≤ (zdistInf d L (a - c) : ℝ)
    · rw [uTF_eq_one d L h, mul_one]; exact hk c h
    · rw [uTF_eq_zero d L (not_le.1 h), mul_zero]; exact hδ
  calc ∑ c : Zd d L, k c * uTF d L a R c ≤ ∑ _c : Zd d L, δ := Finset.sum_le_sum fun c _ => hterm c
    _ = (L : ℝ) ^ d * δ := by
        rw [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
        push_cast; ring

/-- The two-slot sum over `Zd d L × Zd d L` of a product is the product of the sums. -/
private theorem uT_sum2 (p q : Zd d L → ℝ) :
    ∑ b : Zd d L × Zd d L, p b.1 * q b.2 = (∑ x, p x) * ∑ y, q y := by
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

/-- The four-slot double sum of a product is the product of the four sums. -/
private theorem uT_sum4 (p q r s : Zd d L → ℝ) :
    ∑ b : Zd d L × Zd d L, ∑ b' : Zd d L × Zd d L, p b.1 * q b.2 * (r b'.1 * s b'.2) =
      ((∑ x, p x) * ∑ y, q y) * ((∑ x, r x) * ∑ y, s y) := by
  have h : ∀ b : Zd d L × Zd d L, ∑ b' : Zd d L × Zd d L, p b.1 * q b.2 * (r b'.1 * s b'.2) =
      p b.1 * q b.2 * ∑ b' : Zd d L × Zd d L, r b'.1 * s b'.2 :=
    fun b => (Finset.mul_sum _ _ _).symm
  rw [Finset.sum_congr rfl fun b _ => h b, ← Finset.sum_mul, uT_sum2 d L p q, uT_sum2 d L r s]

end Helpers

/-! ## The theorems -/

/-- **Pin E.5f (`res_deccalE_0`, 5-6:400–406)**: nonnegativity and row sums of `ukerMat` give the
near labels the weight `((1-u)/(1-v))²`; the far labels cost `L² W^{-D'}` per coordinate. -/
theorem uopLocalMax (d : ℕ) (g : ℝ) : UopLocalMax d g := by
  intro L W _ _ hL u v R D' hu huv hv hFar A α β a hβ hα hnear
  have hr0 : 0 ≤ (1 - u) / (1 - v) := div_nonneg (by linarith) (by linarith)
  have hα0 : 0 ≤ α := (norm_nonneg _).trans (hα a)
  have hδ : 0 ≤ (W : ℝ) ^ (-D') := Real.rpow_nonneg (Nat.cast_nonneg W) _
  obtain ⟨k₁, hk₁⟩ : ∃ k : Zd d L → ℝ, ∀ c, k c = ‖ukerMat d L g 1 u v a.1 c‖ := ⟨_, fun _ => rfl⟩
  obtain ⟨k₂, hk₂⟩ : ∃ k : Zd d L → ℝ, ∀ c, k c = ‖ukerMat d L g 1 u v a.2 c‖ := ⟨_, fun _ => rfl⟩
  have hk₁0 : ∀ c, 0 ≤ k₁ c := fun c => by rw [hk₁]; exact norm_nonneg _
  have hk₂0 : ∀ c, 0 ≤ k₂ c := fun c => by rw [hk₂]; exact norm_nonneg _
  have hs₁ : ∑ c, k₁ c = (1 - u) / (1 - v) := by
    simp_rw [hk₁]; exact uT_row_sum d L g hL hu huv hv a.1
  have hs₂ : ∑ c, k₂ c = (1 - u) / (1 - v) := by
    simp_rw [hk₂]; exact uT_row_sum d L g hL hu huv hv a.2
  have hg₁ : ∑ c, k₁ c * uTF d L a.1 R c ≤ (L : ℝ) ^ d * (W : ℝ) ^ (-D') :=
    uT_far_sum_le d L a.1 R _ hδ k₁ fun c hc => by rw [hk₁]; exact hFar a.1 c hc
  have hg₂ : ∑ c, k₂ c * uTF d L a.2 R c ≤ (L : ℝ) ^ d * (W : ℝ) ^ (-D') :=
    uT_far_sum_le d L a.2 R _ hδ k₂ fun c hc => by rw [hk₂]; exact hFar a.2 c hc
  have hpt : ∀ b : Zd d L × Zd d L, ‖A b‖ ≤ β + α * (uTF d L a.1 R b.1 + uTF d L a.2 R b.2) := by
    intro b
    by_cases h1 : (zdistInf d L (a.1 - b.1) : ℝ) < R
    · by_cases h2 : (zdistInf d L (a.2 - b.2) : ℝ) < R
      · rw [uTF_eq_zero d L h1, uTF_eq_zero d L h2]
        simpa using hnear b h1 h2
      · have hF := uTF_eq_one d L (not_lt.1 h2)
        have hF1 := uTF_nonneg d L a.1 R b.1
        have := mul_le_mul_of_nonneg_left (show 1 ≤ uTF d L a.1 R b.1 + uTF d L a.2 R b.2 by
          rw [hF]; linarith) hα0
        nlinarith [hα b]
    · have hF := uTF_eq_one d L (not_lt.1 h1)
      have hF2 := uTF_nonneg d L a.2 R b.2
      have := mul_le_mul_of_nonneg_left (show 1 ≤ uTF d L a.1 R b.1 + uTF d L a.2 R b.2 by
        rw [hF]; linarith) hα0
      nlinarith [hα b]
  have hsplit : ∑ b : Zd d L × Zd d L, k₁ b.1 * k₂ b.2 * (β + α * (uTF d L a.1 R b.1 + uTF d L a.2 R b.2)) =
      β * ∑ b : Zd d L × Zd d L, k₁ b.1 * k₂ b.2 +
        α * ∑ b : Zd d L × Zd d L, (k₁ b.1 * uTF d L a.1 R b.1) * k₂ b.2 +
        α * ∑ b : Zd d L × Zd d L, k₁ b.1 * (k₂ b.2 * uTF d L a.2 R b.2) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  have e1 : ∑ b : Zd d L × Zd d L, k₁ b.1 * k₂ b.2 = (∑ x, k₁ x) * ∑ y, k₂ y := uT_sum2 d L k₁ k₂
  have e2 : ∑ b : Zd d L × Zd d L, (k₁ b.1 * uTF d L a.1 R b.1) * k₂ b.2 =
      (∑ x, k₁ x * uTF d L a.1 R x) * ∑ y, k₂ y := uT_sum2 d L (fun x => k₁ x * uTF d L a.1 R x) k₂
  have e3 : ∑ b : Zd d L × Zd d L, k₁ b.1 * (k₂ b.2 * uTF d L a.2 R b.2) =
      (∑ x, k₁ x) * ∑ y, k₂ y * uTF d L a.2 R y := uT_sum2 d L k₁ (fun y => k₂ y * uTF d L a.2 R y)
  have hnorm : ‖Uop d L g 1 u v A a‖ ≤
      ∑ b : Zd d L × Zd d L, k₁ b.1 * k₂ b.2 * (β + α * (uTF d L a.1 R b.1 + uTF d L a.2 R b.2)) := by
    unfold Uop
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [norm_mul, norm_mul, ← hk₁, ← hk₂]
    exact mul_le_mul_of_nonneg_left (hpt b) (mul_nonneg (hk₁0 _) (hk₂0 _))
  rw [hsplit, e1, e2, e3, hs₁, hs₂] at hnorm
  set r := (1 - u) / (1 - v) with hr
  set Δ := (L : ℝ) ^ d * (W : ℝ) ^ (-D') with hΔ
  have m1 : α * ((∑ x, k₁ x * uTF d L a.1 R x) * r) ≤ α * (Δ * r) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hg₁ hr0) hα0
  have m2 : α * (r * ∑ y, k₂ y * uTF d L a.2 R y) ≤ α * (r * Δ) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg₂ hr0) hα0
  calc ‖Uop d L g 1 u v A a‖ ≤ _ := hnorm
    _ ≤ r ^ 2 * β + 2 * (L : ℝ) ^ d * (W : ℝ) ^ (-D') * r * α := by
        rw [hΔ] at m1 m2
        nlinarith [m1, m2]

/-- **Pin E.5g (`res_deccalE_3`, 5-6:433)**: the same for the four-factor sum of `𝒰 ⊗ 𝒰̄`;
`‖conj z‖ = ‖z‖`, so only the row `ℓ¹` norms enter. -/
theorem uopPairLocalMax (d : ℕ) (g : ℝ) : UopPairLocalMax d g := by
  intro L W _ _ hL u v R D' hu huv hv hFar A α β a hβ hα hnear
  have hr0 : 0 ≤ (1 - u) / (1 - v) := div_nonneg (by linarith) (by linarith)
  have hα0 : 0 ≤ α := (norm_nonneg _).trans (hα a a)
  have hδ : 0 ≤ (W : ℝ) ^ (-D') := Real.rpow_nonneg (Nat.cast_nonneg W) _
  obtain ⟨k₁, hk₁⟩ : ∃ k : Zd d L → ℝ, ∀ c, k c = ‖ukerMat d L g 1 u v a.1 c‖ := ⟨_, fun _ => rfl⟩
  obtain ⟨k₂, hk₂⟩ : ∃ k : Zd d L → ℝ, ∀ c, k c = ‖ukerMat d L g 1 u v a.2 c‖ := ⟨_, fun _ => rfl⟩
  have hk₁0 : ∀ c, 0 ≤ k₁ c := fun c => by rw [hk₁]; exact norm_nonneg _
  have hk₂0 : ∀ c, 0 ≤ k₂ c := fun c => by rw [hk₂]; exact norm_nonneg _
  have hs₁ : ∑ c, k₁ c = (1 - u) / (1 - v) := by
    simp_rw [hk₁]; exact uT_row_sum d L g hL hu huv hv a.1
  have hs₂ : ∑ c, k₂ c = (1 - u) / (1 - v) := by
    simp_rw [hk₂]; exact uT_row_sum d L g hL hu huv hv a.2
  have hg₁ : ∑ c, k₁ c * uTF d L a.1 R c ≤ (L : ℝ) ^ d * (W : ℝ) ^ (-D') :=
    uT_far_sum_le d L a.1 R _ hδ k₁ fun c hc => by rw [hk₁]; exact hFar a.1 c hc
  have hg₂ : ∑ c, k₂ c * uTF d L a.2 R c ≤ (L : ℝ) ^ d * (W : ℝ) ^ (-D') :=
    uT_far_sum_le d L a.2 R _ hδ k₂ fun c hc => by rw [hk₂]; exact hFar a.2 c hc
  have hpt : ∀ b b' : Zd d L × Zd d L, ‖A b b'‖ ≤
      β + α * (uTF d L a.1 R b.1 + uTF d L a.2 R b.2 + uTF d L a.1 R b'.1 + uTF d L a.2 R b'.2) := by
    intro b b'
    have n1 := uTF_nonneg d L a.1 R b.1
    have n2 := uTF_nonneg d L a.2 R b.2
    have n3 := uTF_nonneg d L a.1 R b'.1
    have n4 := uTF_nonneg d L a.2 R b'.2
    by_cases h : (zdistInf d L (a.1 - b.1) : ℝ) < R ∧ (zdistInf d L (a.2 - b.2) : ℝ) < R ∧
        (zdistInf d L (a.1 - b'.1) : ℝ) < R ∧ (zdistInf d L (a.2 - b'.2) : ℝ) < R
    · obtain ⟨h1, h2, h3, h4⟩ := h
      rw [uTF_eq_zero d L h1, uTF_eq_zero d L h2, uTF_eq_zero d L h3, uTF_eq_zero d L h4]
      simpa using hnear b b' h1 h2 h3 h4
    · have hge : 1 ≤ uTF d L a.1 R b.1 + uTF d L a.2 R b.2 + uTF d L a.1 R b'.1 +
          uTF d L a.2 R b'.2 := by
        by_cases h1 : (zdistInf d L (a.1 - b.1) : ℝ) < R
        · by_cases h2 : (zdistInf d L (a.2 - b.2) : ℝ) < R
          · by_cases h3 : (zdistInf d L (a.1 - b'.1) : ℝ) < R
            · by_cases h4 : (zdistInf d L (a.2 - b'.2) : ℝ) < R
              · exact absurd ⟨h1, h2, h3, h4⟩ h
              · rw [uTF_eq_one d L (not_lt.1 h4)]; linarith
            · rw [uTF_eq_one d L (not_lt.1 h3)]; linarith
          · rw [uTF_eq_one d L (not_lt.1 h2)]; linarith
        · rw [uTF_eq_one d L (not_lt.1 h1)]; linarith
      have := mul_le_mul_of_nonneg_left hge hα0
      nlinarith [hα b b']
  have hsplit : ∑ b : Zd d L × Zd d L, ∑ b' : Zd d L × Zd d L,
        k₁ b.1 * k₂ b.2 * (k₁ b'.1 * k₂ b'.2) *
          (β + α * (uTF d L a.1 R b.1 + uTF d L a.2 R b.2 + uTF d L a.1 R b'.1 + uTF d L a.2 R b'.2)) =
      β * ∑ b : Zd d L × Zd d L, ∑ b' : Zd d L × Zd d L, k₁ b.1 * k₂ b.2 * (k₁ b'.1 * k₂ b'.2) +
        α * ∑ b : Zd d L × Zd d L, ∑ b' : Zd d L × Zd d L,
          (k₁ b.1 * uTF d L a.1 R b.1) * k₂ b.2 * (k₁ b'.1 * k₂ b'.2) +
        α * ∑ b : Zd d L × Zd d L, ∑ b' : Zd d L × Zd d L,
          k₁ b.1 * (k₂ b.2 * uTF d L a.2 R b.2) * (k₁ b'.1 * k₂ b'.2) +
        α * ∑ b : Zd d L × Zd d L, ∑ b' : Zd d L × Zd d L,
          k₁ b.1 * k₂ b.2 * ((k₁ b'.1 * uTF d L a.1 R b'.1) * k₂ b'.2) +
        α * ∑ b : Zd d L × Zd d L, ∑ b' : Zd d L × Zd d L,
          k₁ b.1 * k₂ b.2 * (k₁ b'.1 * (k₂ b'.2 * uTF d L a.2 R b'.2)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    ring
  have e1 := uT_sum4 d L k₁ k₂ k₁ k₂
  have e2 := uT_sum4 d L (fun x => k₁ x * uTF d L a.1 R x) k₂ k₁ k₂
  have e3 := uT_sum4 d L k₁ (fun y => k₂ y * uTF d L a.2 R y) k₁ k₂
  have e4 := uT_sum4 d L k₁ k₂ (fun x => k₁ x * uTF d L a.1 R x) k₂
  have e5 := uT_sum4 d L k₁ k₂ k₁ (fun y => k₂ y * uTF d L a.2 R y)
  have hnorm : ‖∑ b : Zd d L × Zd d L, ∑ b' : Zd d L × Zd d L,
      ukerMat d L g 1 u v a.1 b.1 * ukerMat d L g 1 u v a.2 b.2 *
        (starRingEnd ℂ) (ukerMat d L g 1 u v a.1 b'.1 * ukerMat d L g 1 u v a.2 b'.2) * A b b'‖ ≤
      ∑ b : Zd d L × Zd d L, ∑ b' : Zd d L × Zd d L,
        k₁ b.1 * k₂ b.2 * (k₁ b'.1 * k₂ b'.2) *
          (β + α * (uTF d L a.1 R b.1 + uTF d L a.2 R b.2 + uTF d L a.1 R b'.1 +
            uTF d L a.2 R b'.2)) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b' _ => ?_)
    simp only [norm_mul, Complex.norm_conj, ← hk₁, ← hk₂]
    exact mul_le_mul_of_nonneg_left (hpt b b')
      (mul_nonneg (mul_nonneg (hk₁0 _) (hk₂0 _)) (mul_nonneg (hk₁0 _) (hk₂0 _)))
  rw [hsplit, e1, e2, e3, e4, e5, hs₁, hs₂] at hnorm
  set r := (1 - u) / (1 - v) with hr
  set Δ := (L : ℝ) ^ d * (W : ℝ) ^ (-D') with hΔ
  have hrr : 0 ≤ r * r * (r * r) := by positivity
  have m1 : α * (((∑ x, k₁ x * uTF d L a.1 R x) * r) * (r * r)) ≤ α * ((Δ * r) * (r * r)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hg₁ hr0) (by positivity)) hα0
  have m2 : α * ((r * ∑ y, k₂ y * uTF d L a.2 R y) * (r * r)) ≤ α * ((r * Δ) * (r * r)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hg₂ hr0) (by positivity)) hα0
  have m3 : α * ((r * r) * ((∑ x, k₁ x * uTF d L a.1 R x) * r)) ≤ α * ((r * r) * (Δ * r)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hg₁ hr0) (by positivity)) hα0
  have m4 : α * ((r * r) * (r * ∑ y, k₂ y * uTF d L a.2 R y)) ≤ α * ((r * r) * (r * Δ)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hg₂ hr0) (by positivity)) hα0
  calc _ ≤ _ := hnorm
    _ ≤ r ^ 4 * β + 4 * (L : ℝ) ^ d * (W : ℝ) ^ (-D') * r ^ 3 * α := by
        rw [hΔ] at m1 m2 m3 m4
        nlinarith [m1, m2, m3, m4]


/-! ## Compiled nonempty instances (`d = 3`, `L = 3`, `W = 2`, `g = 1/2`)

Data: `u = 1/2`, `v = 3/4` (`(1-u)/(1-v) = 2`), `R = 1` (so the near set is `{a}` and the far set
is `{b ≠ a}`, nonempty), `D' = -1` (`W^{-D'} = 2`; `UkerFar` holds because each entry is at most
the row sum `2`).  The tensor takes the value `1/2` at `a` (the near set; `β = 1/2`) and `1`
elsewhere (`α = 1`), so `β ≠ α`. -/

section Instances

private theorem uT_zdistInf_eq_zero {d L : ℕ} [NeZero L] {x : Zd d L} (h : zdistInf d L x = 0) :
    x = 0 := by
  funext i
  have h1 : zdist L (x i) ≤ zdistInf d L x :=
    Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i)
  exact (zdist_eq_zero_iff L).1 (by omega)

/-- `zdistInf d L (a - b) < 1` forces `b = a`. -/
private theorem uT_eq_of_lt_one {d L : ℕ} [NeZero L] {a b : Zd d L}
    (h : (zdistInf d L (a - b) : ℝ) < 1) : b = a := by
  have h0 : zdistInf d L (a - b) = 0 := by exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast h)
  exact (sub_eq_zero.mp (uT_zdistInf_eq_zero h0)).symm

/-- `UkerFar` at the instance data: each entry is at most the row sum `2 = W^{-D'}`. -/
private theorem uT_inst_far : UkerFar 3 3 2 (1 / 2) (1 / 2) (3 / 4) 1 (-1) := by
  intro a b _
  calc ‖ukerMat 3 3 (1 / 2) 1 (1 / 2) (3 / 4) a b‖
      ≤ ∑ c : Zd 3 3, ‖ukerMat 3 3 (1 / 2) 1 (1 / 2) (3 / 4) a c‖ :=
        Finset.single_le_sum (f := fun c : Zd 3 3 => ‖ukerMat 3 3 (1 / 2) 1 (1 / 2) (3 / 4) a c‖)
          (fun c _ => norm_nonneg _) (Finset.mem_univ b)
    _ = (1 - 1 / 2) / (1 - 3 / 4) := uT_row_sum 3 3 (1 / 2) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) a
    _ ≤ ((2 : ℕ) : ℝ) ^ (-(-1 : ℝ)) := by norm_num

/-- Check of `uopLocalMax` at every `a`: `‖𝒰_{1/2,3/4} A (a)‖ ≤ 2² · (1/2) + 2 · 27 · 2 · 2 · 1`. -/
example (a : Zd 3 3 × Zd 3 3) :
    ‖Uop 3 3 (1 / 2) 1 (1 / 2) (3 / 4) (fun b : Zd 3 3 × Zd 3 3 => if b = a then (1 / 2 : ℂ) else 1)
        a‖ ≤
      ((1 - 1 / 2) / (1 - 3 / 4)) ^ 2 * (1 / 2) +
        2 * ((3 : ℕ) : ℝ) ^ 3 * ((2 : ℕ) : ℝ) ^ (-(-1 : ℝ)) * ((1 - 1 / 2) / (1 - 3 / 4)) * 1 := by
  refine uopLocalMax 3 (1 / 2) 3 2 le_rfl (1 / 2) (3 / 4) 1 (-1) (by norm_num) (by norm_num)
    (by norm_num) uT_inst_far _ 1 (1 / 2) a (by norm_num) ?_ ?_
  · intro b
    by_cases h : b = a
    · simp [h]; norm_num
    · simp [h]
  · intro b h1 h2
    have hb : b = a := Prod.ext (uT_eq_of_lt_one h1) (uT_eq_of_lt_one h2)
    simp [hb]

/-- Check of `uopPairLocalMax` at every `a`, tensor `A b b' = 1/2` at `b = b' = a`, else `1`. -/
example (a : Zd 3 3 × Zd 3 3) :
    ‖∑ b : Zd 3 3 × Zd 3 3, ∑ b' : Zd 3 3 × Zd 3 3,
        ukerMat 3 3 (1 / 2) 1 (1 / 2) (3 / 4) a.1 b.1 * ukerMat 3 3 (1 / 2) 1 (1 / 2) (3 / 4) a.2 b.2 *
          (starRingEnd ℂ) (ukerMat 3 3 (1 / 2) 1 (1 / 2) (3 / 4) a.1 b'.1 *
            ukerMat 3 3 (1 / 2) 1 (1 / 2) (3 / 4) a.2 b'.2) *
          (fun b b' : Zd 3 3 × Zd 3 3 => if b = a ∧ b' = a then (1 / 2 : ℂ) else 1) b b'‖ ≤
      ((1 - 1 / 2) / (1 - 3 / 4)) ^ 4 * (1 / 2) +
        4 * ((3 : ℕ) : ℝ) ^ 3 * ((2 : ℕ) : ℝ) ^ (-(-1 : ℝ)) * ((1 - 1 / 2) / (1 - 3 / 4)) ^ 3 * 1 := by
  refine uopPairLocalMax 3 (1 / 2) 3 2 le_rfl (1 / 2) (3 / 4) 1 (-1) (by norm_num) (by norm_num)
    (by norm_num) uT_inst_far _ 1 (1 / 2) a (by norm_num) ?_ ?_
  · intro b b'
    by_cases h : b = a ∧ b' = a
    · simp [h]; norm_num
    · simp [h]
  · intro b b' h1 h2 h3 h4
    have hb : b = a := Prod.ext (uT_eq_of_lt_one h1) (uT_eq_of_lt_one h2)
    have hb' : b' = a := Prod.ext (uT_eq_of_lt_one h3) (uT_eq_of_lt_one h4)
    simp [hb, hb']

/-- Boundary of the window `0 ≤ u ≤ v < 1` (DECISIONS §29): `u = v = 0` (`𝒰 = id`, row sum `1`),
`R = 1`, `D' = 0` (`UkerFar`: each entry is at most the row sum `1 = W^0`). -/
example (a : Zd 3 3 × Zd 3 3) :
    ‖Uop 3 3 (1 / 2) 1 0 0 (fun b : Zd 3 3 × Zd 3 3 => if b = a then (1 / 2 : ℂ) else 1) a‖ ≤
      ((1 - 0) / (1 - 0)) ^ 2 * (1 / 2) +
        2 * ((3 : ℕ) : ℝ) ^ 3 * ((2 : ℕ) : ℝ) ^ (-(0 : ℝ)) * ((1 - 0) / (1 - 0)) * 1 := by
  have hFar : UkerFar 3 3 2 (1 / 2) 0 0 1 0 := by
    intro x y _
    calc ‖ukerMat 3 3 (1 / 2) 1 0 0 x y‖
        ≤ ∑ c : Zd 3 3, ‖ukerMat 3 3 (1 / 2) 1 0 0 x c‖ :=
          Finset.single_le_sum (f := fun c : Zd 3 3 => ‖ukerMat 3 3 (1 / 2) 1 0 0 x c‖)
            (fun c _ => norm_nonneg _) (Finset.mem_univ y)
      _ = (1 - 0) / (1 - 0) := uT_row_sum 3 3 (1 / 2) (by norm_num) le_rfl le_rfl (by norm_num) x
      _ ≤ ((2 : ℕ) : ℝ) ^ (-(0 : ℝ)) := by norm_num
  refine uopLocalMax 3 (1 / 2) 3 2 le_rfl 0 0 1 0 le_rfl le_rfl (by norm_num) hFar _ 1 (1 / 2) a
    (by norm_num) ?_ ?_
  · intro b
    by_cases h : b = a
    · simp [h]; norm_num
    · simp [h]
  · intro b h1 h2
    have hb : b = a := Prod.ext (uT_eq_of_lt_one h1) (uT_eq_of_lt_one h2)
    simp [hb]

end Instances

end RBM.Path

end
