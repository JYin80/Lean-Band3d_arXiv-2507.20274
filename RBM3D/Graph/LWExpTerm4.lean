/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWExpTerm2
import RBM3D.Loop.PureLoop
import RBM3D.Defs.RadialSum
import RBM3D.Loop.KLUnique
import RBM3D.Induction.Step34Pins
import RBM3D.Induction.ScaleFacts

/-!
# LW-14d (T2254): `lem:LWterm_EXP`, part d: the term bounds with a decaying first kernel

Paper: arXiv:2507.20274, `paper/tex/6_Step6_two_loop.tex:83-88` (`lem:LWterm_EXP`), proof
`paper/tex/B_graphical_lemmas.tex:7-121` (`B:line`): the terms `I₁+J₁` (`(eq:termI1)`, `B:37-41`),
`I₂+J₂`, `I₃+J₃` (`(eq:termI2)`, `B:43-49`), `I₄₁+J₄₁` (`(eq:termI41)`, `B:57-70`), where `I_i + J_i` is one term
with the kernel `K = S^{(B)}(m + m³K⁺)` (`B:34`).  No port (RBM2D has no light-weight layer).

## What is proved

`lwExpI1K_holds`, `lwExpI23K_holds`, `lwExpI41K_holds`: the merged pins `LWExpI1K`, `LWExpI23K`, `LWExpI41K`
(`LWExpTerm2.lean:81,96,115`) as stated, for every `LWExpKer` kernel and both charges `s`; then
`lwCutExp_of_G5' : LWExpG5' d → LWCutExp d` (`lwCutExp_of_terms` with the three proved terms).

## Targets 1-5 (the new estimates)

* `lwExpTerm4_kerSum`: `Σ_a ‖K_{ab}‖, Σ_a ‖K_{ba}‖ ≤ C` uniformly in `n, L`, every `d` (padding to `d + 2` coordinates and
  `sum_radial_exp_decay_le`; `|x|_1 ≤ d |x|_∞`).
* `lwExpTerm4_ward2`: `W^d Σ_b ‖𝓛^{(2)}_{(s,+),(a,b)}‖ ≤ η⁻¹ ‖𝓛^{(1)}_{+,a}‖`, both `s`; pathwise.  Fine-level Ward
  `Σ_y |G_{yx}|² = Im G_{xx}/η`; `s = +`: `|𝓛_{(+,+),(a,b)}| ≤ ½(P(a,b) + P(b,a))` entrywise (AM-GM).
* `lwExpTerm4_kward`: `W^d Σ_a ‖𝒦^{(2)}_{(s,+),(a,b)}‖ ≺ η⁻¹` (`STKward` after `KLK_rotate`).
* `lwExpTerm4_diag`: `max_x |G_{xx}| ≺ 1` (`STLocalEntry` at `(x, x)`).
* `lwExpTerm4_L3`: `W^d Σ_a ‖𝓛^{(3)}_{(+,+,σ),(a,b,c)}‖ ≤ η⁻¹ A (max 𝓛^{(2)}_{(-,+)})^{1/2}`; pathwise.

Sections: §1 target 1, §2 fine Ward, §3 weights and targets 2, 5, §4 copies of the private machinery of
`LWExpTerm.lean` (T2236), §5 targets 3, 4, §6 target 6, §7 sums with `K`, §8 target 7, §9 target 8, target 9, §10 instances.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ## 1. Target 1: the column and row sums of a decaying kernel -/

/-- Padding by two zero coordinates: `Z_L^d ↪ Z_L^{d+2}`, preserving `zdistD`. -/
private def lwExpTerm4_pad {d L : ℕ} (x : Zd d L) : Zd (d + 2) L := Fin.append x (0 : Fin 2 → ZMod L)

private theorem lwExpTerm4_pad_inj {d L : ℕ} : Function.Injective (lwExpTerm4_pad (d := d) (L := L)) := by
  intro x y h
  funext i
  have := congrFun h (Fin.castAdd 2 i)
  simpa [lwExpTerm4_pad, Fin.append_left] using this

private theorem lwExpTerm4_zdistD_pad {d L : ℕ} (x : Zd d L) :
    zdistD (d + 2) L (lwExpTerm4_pad x) = zdistD d L x := by
  unfold zdistD lwExpTerm4_pad
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-- `Σ_{x ∈ Z_L^d} e^{-c|x|_∞} ≤ expC d (c/(d+1))`, uniformly in `L` and for every `d` (padding to `d + 2`
coordinates; `|x|_1 ≤ d |x|_∞ ≤ (d+1) |x|_∞`). -/
private theorem lwExpTerm4_sum_decay (d L : ℕ) [NeZero L] {c : ℝ} (hc : 0 < c) :
    ∑ x : Zd d L, Real.exp (-(c * (zdistInf d L x : ℝ))) ≤ expC d (c / ((d : ℝ) + 1)) := by
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hc' : 0 < c / ((d : ℝ) + 1) := div_pos hc hd1
  have hpt : ∀ x : Zd d L, Real.exp (-(c * (zdistInf d L x : ℝ))) ≤
      Real.exp (-(c / ((d : ℝ) + 1) * (zdistD (d + 2) L (lwExpTerm4_pad x) : ℝ))) := by
    intro x
    apply Real.exp_le_exp.2
    rw [lwExpTerm4_zdistD_pad]
    have h1 : (zdistD d L x : ℝ) ≤ (d : ℝ) * (zdistInf d L x : ℝ) := by
      exact_mod_cast zdistD_le_mul_zdistInf d L x
    have h2 : (0 : ℝ) ≤ (zdistInf d L x : ℝ) := Nat.cast_nonneg _
    have h3 : c / ((d : ℝ) + 1) * (zdistD d L x : ℝ) ≤ c * (zdistInf d L x : ℝ) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hd1]
      nlinarith [mul_nonneg hc.le h2, mul_le_mul_of_nonneg_left h1 hc.le]
    linarith
  calc ∑ x : Zd d L, Real.exp (-(c * (zdistInf d L x : ℝ)))
      ≤ ∑ x : Zd d L, Real.exp (-(c / ((d : ℝ) + 1) * (zdistD (d + 2) L (lwExpTerm4_pad x) : ℝ))) :=
        Finset.sum_le_sum fun x _ => hpt x
    _ = ∑ y ∈ Finset.univ.image (lwExpTerm4_pad (d := d) (L := L)),
          Real.exp (-(c / ((d : ℝ) + 1) * (zdistD (d + 2) L y : ℝ))) := by
        rw [Finset.sum_image (fun x _ y _ h => lwExpTerm4_pad_inj h)]
    _ ≤ ∑ y : Zd (d + 2) L, Real.exp (-(c / ((d : ℝ) + 1) * (zdistD (d + 2) L y : ℝ))) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun y _ _ => (Real.exp_pos _).le
    _ ≤ expC d (c / ((d : ℝ) + 1)) := sum_radial_exp_decay_le d hc'

/-- **Target 1** (`LwExpTerm4KerSumPin`): a kernel with `LWExpKer` has column and row sums bounded uniformly
in `n` (and `L`): `C = C_K · expC d (c_K/(d+1))`.  The row sum reindexes `a ↦ b - a`, the column sum
`a ↦ a - b`; no `|-x| = |x|` is used. -/
theorem lwExpTerm4_kerSum (d : ℕ) (sz : Sizes d) (K : ∀ n, Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ)
    (hK : LWExpKer sz K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (b : Zd d (sz.L n)),
      ∑ a : Zd d (sz.L n), ‖K n a b‖ ≤ C ∧ ∑ a : Zd d (sz.L n), ‖K n b a‖ ≤ C := by
  obtain ⟨C₀, c, hC₀, hc, h⟩ := hK
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hE : 0 < expC d (c / ((d : ℝ) + 1)) := by
    unfold expC
    have hc' : 0 < c / ((d : ℝ) + 1) := div_pos hc hd1
    positivity
  refine ⟨C₀ * expC d (c / ((d : ℝ) + 1)), mul_pos hC₀ hE, fun n b => ⟨?_, ?_⟩⟩
  · have : NeZero (sz.L n) := ⟨by have := sz.three_le_L n; omega⟩
    calc ∑ a, ‖K n a b‖ ≤ ∑ a, C₀ * Real.exp (-(c * (zdistInf d (sz.L n) (a - b) : ℝ))) :=
          Finset.sum_le_sum fun a _ => h n a b
      _ = C₀ * ∑ x : Zd d (sz.L n), Real.exp (-(c * (zdistInf d (sz.L n) x : ℝ))) := by
          rw [← Finset.mul_sum]
          congr 1
          exact Fintype.sum_equiv (Equiv.subRight b) _ _ fun a => rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left (lwExpTerm4_sum_decay d (sz.L n) hc) hC₀.le
  · have : NeZero (sz.L n) := ⟨by have := sz.three_le_L n; omega⟩
    calc ∑ a, ‖K n b a‖ ≤ ∑ a, C₀ * Real.exp (-(c * (zdistInf d (sz.L n) (b - a) : ℝ))) :=
          Finset.sum_le_sum fun a _ => h n b a
      _ = C₀ * ∑ x : Zd d (sz.L n), Real.exp (-(c * (zdistInf d (sz.L n) x : ℝ))) := by
          rw [← Finset.mul_sum]
          congr 1
          exact Fintype.sum_equiv (Equiv.subLeft b) _ _ fun a => rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left (lwExpTerm4_sum_decay d (sz.L n) hc) hC₀.le


/-! ## 2. The fine-level Ward identity `Σ_y |G_{yx}|² = Im G_{xx}/η` (and the row form) -/

section FineWard

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem lwExpTerm4_green_conj {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (z : ℂ) :
    (green H z)ᴴ = green H ((starRingEnd ℂ) z) := by
  have hH' : Hᴴ = H := hH
  simp only [green, Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH', Complex.star_def]

/-- `G - G^* = 2iη G^* G = 2iη G G^*` (`Gres H z true = green H z`), at one entry. -/
private theorem lwExpTerm4_ward_gram {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    (green H z - (green H z)ᴴ = (2 * Complex.I * (z.im : ℂ)) • ((green H z)ᴴ * green H z)) ∧
    (green H z - (green H z)ᴴ = (2 * Complex.I * (z.im : ℂ)) • (green H z * (green H z)ᴴ)) := by
  have hu := RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero hH hz
  have hu' := RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero hH (z := (starRingEnd ℂ) z) (by simpa using hz)
  rw [lwExpTerm4_green_conj hH]
  refine ⟨green_sub_green_conj' hu hu', ?_⟩
  rw [green_sub_green hu hu', Complex.sub_conj]
  congr 1
  push_cast
  ring

private theorem lwExpTerm4_ward_row {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (x : ι) :
    z.im * ∑ y, ‖green H z x y‖ ^ 2 = (green H z x x).im := by
  have h := congrFun (congrFun (lwExpTerm4_ward_gram hH hz).2 x) x
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    smul_eq_mul, Complex.star_def] at h
  have h1 : ∑ y, green H z x y * (starRingEnd ℂ) (green H z x y) = ((∑ y, ‖green H z x y‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Complex.mul_conj', ← Complex.ofReal_pow]
  rw [h1, Complex.sub_conj] at h
  have hI : (2 * Complex.I) ≠ 0 := by simp
  generalize (∑ y, ‖green H z x y‖ ^ 2 : ℝ) = S at h ⊢
  have h3 : ((z.im * S : ℝ) : ℂ) = ((green H z x x).im : ℂ) := by
    apply mul_left_cancel₀ hI
    push_cast at h ⊢
    linear_combination (-1 : ℂ) * h
  exact_mod_cast h3

private theorem lwExpTerm4_ward_col {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (x : ι) :
    z.im * ∑ y, ‖green H z y x‖ ^ 2 = (green H z x x).im := by
  have h := congrFun (congrFun (lwExpTerm4_ward_gram hH hz).1 x) x
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    smul_eq_mul, Complex.star_def] at h
  have h1 : ∑ y, (starRingEnd ℂ) (green H z y x) * green H z y x = ((∑ y, ‖green H z y x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [mul_comm, Complex.mul_conj', ← Complex.ofReal_pow]
  rw [h1, Complex.sub_conj] at h
  have hI : (2 * Complex.I) ≠ 0 := by simp
  generalize (∑ y, ‖green H z y x‖ ^ 2 : ℝ) = S at h ⊢
  have h3 : ((z.im * S : ℝ) : ℂ) = ((green H z x x).im : ℂ) := by
    apply mul_left_cancel₀ hI
    push_cast at h ⊢
    linear_combination (-1 : ℂ) * h
  exact_mod_cast h3

end FineWard


/-! ## 3. Block weights; the pathwise bounds of targets 2 and 5 -/

section Weights

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

/-- The real block weight `W^{-d} 1[x ∈ [a]]`. -/
private def lwExpTerm4_rho (a : Zd d (sz.L n)) (x : Idx d (sz.L n) (sz.W n)) : ℝ :=
  if lwExpTerm2_bl d (sz.L n) (sz.W n) x = a then (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ else 0

private theorem lwExpTerm4_w_eq (a : Zd d (sz.L n)) (x : Idx d (sz.L n) (sz.W n)) :
    lwExpTerm2_w sz n a x = ((lwExpTerm4_rho sz n a x : ℝ) : ℂ) := by
  unfold lwExpTerm2_w lwExpTerm2_dw lwExpTerm4_rho
  split_ifs <;> simp

private theorem lwExpTerm4_rho_nonneg (a : Zd d (sz.L n)) (x : Idx d (sz.L n) (sz.W n)) :
    0 ≤ lwExpTerm4_rho sz n a x := by
  unfold lwExpTerm4_rho
  split_ifs
  · positivity
  · exact le_rfl

private theorem lwExpTerm4_rho_sum_pts (a : Zd d (sz.L n)) : ∑ x, lwExpTerm4_rho sz n a x = 1 := by
  have h : ∑ x, lwExpTerm2_w sz n a x = 1 :=
    lwExpTerm2_dw_sum (lwExpTerm2_bl d (sz.L n) (sz.W n)) ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) (lwExpTerm2_hc sz n) a
  simp only [lwExpTerm4_w_eq] at h
  exact_mod_cast h

private theorem lwExpTerm4_rho_sum_blocks (x : Idx d (sz.L n) (sz.W n)) :
    ∑ a, lwExpTerm4_rho sz n a x = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
  unfold lwExpTerm4_rho
  simp [Finset.sum_ite_eq]

private theorem lwExpTerm4_Wd_pos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
  have := sz.W_pos n
  positivity

private theorem lwExpTerm4_Gt_true_green (E t : ℝ) (ω : sz.SeqΩ) :
    Gt sz n E t true ω = green (seqHflow sz n t ω) (zt E t) :=
  RBM.Ind.Gres_eq_green_zSig _ _ true

private theorem lwExpTerm4_Gt_ward_row {E t : ℝ} (hE : |E| < 2) (ht : t < 1) (ω : sz.SeqΩ)
    (x : Idx d (sz.L n) (sz.W n)) :
    etaT E t * ∑ y, ‖Gt sz n E t true ω x y‖ ^ 2 = (Gt sz n E t true ω x x).im := by
  have hz : (zt E t).im ≠ 0 := by rw [← etaT_eq_zt_im]; exact (etaT_pos hE ht).ne'
  have h := lwExpTerm4_ward_row (seqHflow_isHermitian sz n t ω) hz x
  rw [← etaT_eq_zt_im] at h
  simpa only [lwExpTerm4_Gt_true_green] using h

private theorem lwExpTerm4_Gt_ward_col {E t : ℝ} (hE : |E| < 2) (ht : t < 1) (ω : sz.SeqΩ)
    (x : Idx d (sz.L n) (sz.W n)) :
    etaT E t * ∑ y, ‖Gt sz n E t true ω y x‖ ^ 2 = (Gt sz n E t true ω x x).im := by
  have hz : (zt E t).im ≠ 0 := by rw [← etaT_eq_zt_im]; exact (etaT_pos hE ht).ne'
  have h := lwExpTerm4_ward_col (seqHflow_isHermitian sz n t ω) hz x
  rw [← etaT_eq_zt_im] at h
  simpa only [lwExpTerm4_Gt_true_green] using h

/-- `Σ_x ρ_a(x) |G_{yx}|²`-type double sum: `P(a,b) = Σ_{x,y} |G_{yx}|² ρ_a(y) ρ_b(x)` (`= 𝓛^{(2)}_{(-,+),(a,b)}`). -/
private def lwExpTerm4_Pm (E t : ℝ) (ω : sz.SeqΩ) (a b : Zd d (sz.L n)) : ℝ :=
  ∑ x, ∑ y, ‖Gt sz n E t true ω y x‖ ^ 2 * (lwExpTerm4_rho sz n a y * lwExpTerm4_rho sz n b x)

private theorem lwExpTerm4_Pm_nonneg (E t : ℝ) (ω : sz.SeqΩ) (a b : Zd d (sz.L n)) :
    0 ≤ lwExpTerm4_Pm sz n E t ω a b :=
  Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (sq_nonneg _) (mul_nonneg (lwExpTerm4_rho_nonneg sz n a y) (lwExpTerm4_rho_nonneg sz n b x))

/-- `𝓛^{(2)}_{(-,+),(a,b)} = P(a,b)`. -/
private theorem lwExpTerm4_Lloop_ft (E t : ℝ) (a b : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    Lloop sz n E t ![false, true] ![a, b] ω = ((lwExpTerm4_Pm sz n E t ω a b : ℝ) : ℂ) := by
  rw [lwExpTerm2_Lloop2]
  unfold lwExpTerm2_L2 lwExpTerm4_Pm
  push_cast
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have h1 : Gt sz n E t false ω x y = (starRingEnd ℂ) (Gt sz n E t true ω y x) :=
    (lwExpTerm2_conj_Gt sz n E t true ω y x).symm
  rw [h1, lwExpTerm4_w_eq, lwExpTerm4_w_eq]
  have h2 : (starRingEnd ℂ) (Gt sz n E t true ω y x) * Gt sz n E t true ω y x =
      ((‖Gt sz n E t true ω y x‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.conj_mul']
  rw [show (starRingEnd ℂ) (Gt sz n E t true ω y x) * ((lwExpTerm4_rho sz n a y : ℝ) : ℂ) *
      (Gt sz n E t true ω y x * ((lwExpTerm4_rho sz n b x : ℝ) : ℂ)) =
    ((starRingEnd ℂ) (Gt sz n E t true ω y x) * Gt sz n E t true ω y x) *
      (((lwExpTerm4_rho sz n a y : ℝ) : ℂ) * ((lwExpTerm4_rho sz n b x : ℝ) : ℂ)) by ring, h2]

private theorem lwExpTerm4_norm_Lloop_ft (E t : ℝ) (a b : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    ‖Lloop sz n E t ![false, true] ![a, b] ω‖ = lwExpTerm4_Pm sz n E t ω a b := by
  rw [lwExpTerm4_Lloop_ft, Complex.norm_real, Real.norm_of_nonneg (lwExpTerm4_Pm_nonneg sz n E t ω a b)]

/-- `‖𝓛^{(2)}_{(+,+),(a,b)}‖ ≤ ½ (P(a,b) + P(b,a))` (AM-GM entrywise: `|G_{xy}||G_{yx}| ≤ ½(|G_{xy}|² + |G_{yx}|²)`). -/
private theorem lwExpTerm4_norm_Lloop_tt (E t : ℝ) (a b : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    ‖Lloop sz n E t ![true, true] ![a, b] ω‖ ≤
      (lwExpTerm4_Pm sz n E t ω a b + lwExpTerm4_Pm sz n E t ω b a) / 2 := by
  rw [lwExpTerm2_Lloop2]
  unfold lwExpTerm2_L2
  set G := Gt sz n E t true ω with hG
  have hn : ∀ x y : Idx d (sz.L n) (sz.W n), ‖G x y * lwExpTerm2_w sz n a y * (G y x * lwExpTerm2_w sz n b x)‖ ≤
      (‖G x y‖ ^ 2 + ‖G y x‖ ^ 2) / 2 * (lwExpTerm4_rho sz n a y * lwExpTerm4_rho sz n b x) := by
    intro x y
    rw [lwExpTerm4_w_eq, lwExpTerm4_w_eq]
    have hr : ‖G x y * ((lwExpTerm4_rho sz n a y : ℝ) : ℂ) * (G y x * ((lwExpTerm4_rho sz n b x : ℝ) : ℂ))‖ =
        ‖G x y‖ * ‖G y x‖ * (lwExpTerm4_rho sz n a y * lwExpTerm4_rho sz n b x) := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (lwExpTerm4_rho_nonneg sz n a y), Real.norm_of_nonneg (lwExpTerm4_rho_nonneg sz n b x)]
      ring
    rw [hr]
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (lwExpTerm4_rho_nonneg sz n a y) (lwExpTerm4_rho_nonneg sz n b x))
    nlinarith [sq_nonneg (‖G x y‖ - ‖G y x‖)]
  calc ‖∑ x, ∑ y, G x y * lwExpTerm2_w sz n a y * (G y x * lwExpTerm2_w sz n b x)‖
      ≤ ∑ x, ∑ y, ‖G x y * lwExpTerm2_w sz n a y * (G y x * lwExpTerm2_w sz n b x)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => norm_sum_le _ _)
    _ ≤ ∑ x, ∑ y, (‖G x y‖ ^ 2 + ‖G y x‖ ^ 2) / 2 * (lwExpTerm4_rho sz n a y * lwExpTerm4_rho sz n b x) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hn x y
    _ = (lwExpTerm4_Pm sz n E t ω a b + lwExpTerm4_Pm sz n E t ω b a) / 2 := by
        have e : ∑ x, ∑ y, ‖G x y‖ ^ 2 * (lwExpTerm4_rho sz n a y * lwExpTerm4_rho sz n b x) =
            lwExpTerm4_Pm sz n E t ω b a := by
          unfold lwExpTerm4_Pm
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          rw [hG, mul_comm (lwExpTerm4_rho sz n b y)]
        unfold lwExpTerm4_Pm at e ⊢
        rw [← e, ← hG, ← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun y _ => ?_
        ring


private theorem lwExpTerm4_sumPm_left (E t : ℝ) (ω : sz.SeqΩ) (a : Zd d (sz.L n)) :
    (((sz.W n : ℕ) : ℝ) ^ d) * ∑ b, lwExpTerm4_Pm sz n E t ω a b =
      ∑ y, lwExpTerm4_rho sz n a y * ∑ x, ‖Gt sz n E t true ω y x‖ ^ 2 := by
  have hW := (lwExpTerm4_Wd_pos sz n (d := d)).ne'
  unfold lwExpTerm4_Pm
  have e1 : ∑ b, ∑ x, ∑ y, ‖Gt sz n E t true ω y x‖ ^ 2 * (lwExpTerm4_rho sz n a y * lwExpTerm4_rho sz n b x) =
      ∑ x, ∑ y, ‖Gt sz n E t true ω y x‖ ^ 2 * (lwExpTerm4_rho sz n a y * ∑ b, lwExpTerm4_rho sz n b x) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
  rw [e1]
  simp_rw [lwExpTerm4_rho_sum_blocks]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  field_simp

private theorem lwExpTerm4_sumPm_right (E t : ℝ) (ω : sz.SeqΩ) (a : Zd d (sz.L n)) :
    (((sz.W n : ℕ) : ℝ) ^ d) * ∑ b, lwExpTerm4_Pm sz n E t ω b a =
      ∑ x, lwExpTerm4_rho sz n a x * ∑ y, ‖Gt sz n E t true ω y x‖ ^ 2 := by
  have hW := (lwExpTerm4_Wd_pos sz n (d := d)).ne'
  unfold lwExpTerm4_Pm
  have e1 : ∑ b, ∑ x, ∑ y, ‖Gt sz n E t true ω y x‖ ^ 2 * (lwExpTerm4_rho sz n b y * lwExpTerm4_rho sz n a x) =
      ∑ x, ∑ y, ‖Gt sz n E t true ω y x‖ ^ 2 * ((∑ b, lwExpTerm4_rho sz n b y) * lwExpTerm4_rho sz n a x) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
  rw [e1]
  simp_rw [lwExpTerm4_rho_sum_blocks]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  field_simp

private theorem lwExpTerm4_L1_im (E t : ℝ) (a : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    (Lloop sz n E t ![true] ![a] ω).im = ∑ x, (Gt sz n E t true ω x x).im * lwExpTerm4_rho sz n a x := by
  rw [lwExpTerm2_Lloop1, Complex.im_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [lwExpTerm4_w_eq, Complex.im_mul_ofReal]

/-- `W^d Σ_b P(a,b) = W^d Σ_b P(b,a) = η⁻¹ Im 𝓛^{(1)}_{+,a}` (the fine-level Ward identity). -/
private theorem lwExpTerm4_sumPm_eq {E t : ℝ} (hE : |E| < 2) (ht : t < 1) (ω : sz.SeqΩ) (a : Zd d (sz.L n)) :
    (((sz.W n : ℕ) : ℝ) ^ d) * ∑ b, lwExpTerm4_Pm sz n E t ω a b =
        (etaT E t)⁻¹ * (Lloop sz n E t ![true] ![a] ω).im ∧
      (((sz.W n : ℕ) : ℝ) ^ d) * ∑ b, lwExpTerm4_Pm sz n E t ω b a =
        (etaT E t)⁻¹ * (Lloop sz n E t ![true] ![a] ω).im := by
  have hη := etaT_pos hE ht
  have hrow : ∀ y, ∑ x, ‖Gt sz n E t true ω y x‖ ^ 2 = (etaT E t)⁻¹ * (Gt sz n E t true ω y y).im := by
    intro y
    rw [← lwExpTerm4_Gt_ward_row sz n hE ht ω y]
    field_simp
  have hcol : ∀ x, ∑ y, ‖Gt sz n E t true ω y x‖ ^ 2 = (etaT E t)⁻¹ * (Gt sz n E t true ω x x).im := by
    intro x
    rw [← lwExpTerm4_Gt_ward_col sz n hE ht ω x]
    field_simp
  rw [lwExpTerm4_L1_im, lwExpTerm4_sumPm_left, lwExpTerm4_sumPm_right, Finset.mul_sum]
  constructor
  · refine Finset.sum_congr rfl fun y _ => ?_
    rw [hrow]; ring
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [hcol]; ring

/-- **Target 2** (`LwExpTerm4WardPin`), pathwise: `W^d Σ_b ‖𝓛^{(2)}_{(s,+),(a,b)}‖ ≤ η_t⁻¹ ‖𝓛^{(1)}_{+,a}‖`, both
charges `s`.  `s = false`: `𝓛^{(2)}_{(-,+),(a,b)} = P(a,b) ≥ 0` and the Ward identity; `s = true`:
`|𝓛^{(2)}_{(+,+),(a,b)}| ≤ ½ (P(a,b) + P(b,a))`, then Ward for each. -/
theorem lwExpTerm4_ward2 (d : ℕ) (sz : Sizes d) (n : ℕ) (E t : ℝ) (hE : |E| < 2) (ht : t < 1)
    (s : Bool) (a : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    (((sz.W n : ℕ) : ℝ) ^ d) * ∑ b : Zd d (sz.L n), ‖Lloop sz n E t ![s, true] ![a, b] ω‖ ≤
      (etaT E t)⁻¹ * ‖Lloop sz n E t ![true] ![a] ω‖ := by
  have hWd := (lwExpTerm4_Wd_pos sz n (d := d)).le
  obtain ⟨h1, h2⟩ := lwExpTerm4_sumPm_eq sz n hE ht ω a
  have hη : 0 ≤ (etaT E t)⁻¹ := (inv_pos.2 (etaT_pos hE ht)).le
  have him : (etaT E t)⁻¹ * (Lloop sz n E t ![true] ![a] ω).im ≤
      (etaT E t)⁻¹ * ‖Lloop sz n E t ![true] ![a] ω‖ :=
    mul_le_mul_of_nonneg_left (Complex.im_le_norm _) hη
  cases s
  · simp only [lwExpTerm4_norm_Lloop_ft]
    rw [h1]
    exact him
  · calc (((sz.W n : ℕ) : ℝ) ^ d) * ∑ b, ‖Lloop sz n E t ![true, true] ![a, b] ω‖
        ≤ (((sz.W n : ℕ) : ℝ) ^ d) * ∑ b, (lwExpTerm4_Pm sz n E t ω a b + lwExpTerm4_Pm sz n E t ω b a) / 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => lwExpTerm4_norm_Lloop_tt sz n E t a b ω) hWd
      _ = ((((sz.W n : ℕ) : ℝ) ^ d) * ∑ b, lwExpTerm4_Pm sz n E t ω a b +
            (((sz.W n : ℕ) : ℝ) ^ d) * ∑ b, lwExpTerm4_Pm sz n E t ω b a) / 2 := by
          rw [← Finset.sum_div, Finset.sum_add_distrib]; ring
      _ ≤ _ := by rw [h1, h2]; linarith


/-- Weighted Cauchy-Schwarz: `(Σ p u)² ≤ (Σ p)(Σ p u²)` for `p ≥ 0`. -/
private theorem lwExpTerm4_cs_weighted {α : Type*} [Fintype α] (p u : α → ℝ) (hp : ∀ i, 0 ≤ p i) :
    (∑ i, p i * u i) ^ 2 ≤ (∑ i, p i) * ∑ i, p i * u i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => Real.sqrt (p i))
    (fun i => Real.sqrt (p i) * u i)
  have e1 : ∀ i, Real.sqrt (p i) * (Real.sqrt (p i) * u i) = p i * u i := fun i => by
    rw [← mul_assoc, Real.mul_self_sqrt (hp i)]
  have e2 : ∀ i, Real.sqrt (p i) ^ 2 = p i := fun i => Real.sq_sqrt (hp i)
  have e3 : ∀ i, (Real.sqrt (p i) * u i) ^ 2 = p i * u i ^ 2 := fun i => by
    rw [mul_pow, e2]
  simp only [e1, e2, e3] at h
  exact h

/-- The vertex bound: `Σ_y |G_{xy}||G_{yz}| ≤ A/η` from `Σ_y |G_{xy}|² = Im G_{xx}/η`,
`Σ_y |G_{yz}|² = Im G_{zz}/η` and Cauchy-Schwarz over `y`. -/
private theorem lwExpTerm4_vertex {E t : ℝ} (hE : |E| < 2) (ht : t < 1) (ω : sz.SeqΩ) {A : ℝ}
    (hA : ∀ x : Idx d (sz.L n) (sz.W n), ‖Gt sz n E t true ω x x‖ ≤ A) (x z : Idx d (sz.L n) (sz.W n)) :
    ∑ y, ‖Gt sz n E t true ω x y‖ * ‖Gt sz n E t true ω y z‖ ≤ A * (etaT E t)⁻¹ := by
  have hη := etaT_pos hE ht
  set G := Gt sz n E t true ω with hG
  have h1 := lwExpTerm4_Gt_ward_row sz n hE ht ω x
  have h2 := lwExpTerm4_Gt_ward_col sz n hE ht ω z
  rw [← hG] at h1 h2
  have hS1 : 0 ≤ ∑ y, ‖G x y‖ ^ 2 := Finset.sum_nonneg fun y _ => sq_nonneg _
  have hS2 : 0 ≤ ∑ y, ‖G y z‖ ^ 2 := Finset.sum_nonneg fun y _ => sq_nonneg _
  have hIm1 : (G x x).im ≤ A := (Complex.im_le_norm _).trans (hA x)
  have hIm2 : (G z z).im ≤ A := (Complex.im_le_norm _).trans (hA z)
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA x)
  have hs1 : ∑ y, ‖G x y‖ ^ 2 ≤ A * (etaT E t)⁻¹ := by
    rw [le_mul_inv_iff₀ hη]
    nlinarith
  have hs2 : ∑ y, ‖G y z‖ ^ 2 ≤ A * (etaT E t)⁻¹ := by
    rw [le_mul_inv_iff₀ hη]
    nlinarith
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun y => ‖G x y‖) (fun y => ‖G y z‖)
  have h3 : (∑ y, ‖G x y‖ * ‖G y z‖) ^ 2 ≤ (A * (etaT E t)⁻¹) ^ 2 := by
    refine hcs.trans ?_
    rw [sq]
    exact mul_le_mul hs1 hs2 hS2 (by positivity)
  exact (sq_le_sq₀ (Finset.sum_nonneg fun y _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (by positivity)).1 h3


private theorem lwExpTerm4_norm_w (a : Zd d (sz.L n)) (x : Idx d (sz.L n) (sz.W n)) :
    ‖lwExpTerm2_w sz n a x‖ = lwExpTerm4_rho sz n a x := by
  rw [lwExpTerm4_w_eq, Complex.norm_real, Real.norm_of_nonneg (lwExpTerm4_rho_nonneg sz n a x)]

/-- `Σ_x Σ_z |Ĝ_{zx}|² ρ_b(z) ρ_c(x) ≤ max_{u,v} 𝓛^{(2)}_{(-,+),(u,v)}` for both charges of `Ĝ`
(`σ = +`: `P(b,c)`; `σ = -`: `P(c,b)`). -/
private theorem lwExpTerm4_Q_le (E t : ℝ) (σ : Bool) (b c : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    ∑ x, ∑ z, ‖Gt sz n E t σ ω z x‖ ^ 2 * (lwExpTerm4_rho sz n b z * lwExpTerm4_rho sz n c x) ≤
      STmaxLoop2 sz n E t ω := by
  have hle : ∀ u v, lwExpTerm4_Pm sz n E t ω u v ≤ STmaxLoop2 sz n E t ω := fun u v => by
    rw [← lwExpTerm4_norm_Lloop_ft]
    exact Finset.le_sup' (fun p : Zd d (sz.L n) × Zd d (sz.L n) =>
      ‖Lloop sz n E t ![false, true] ![p.1, p.2] ω‖) (Finset.mem_univ (u, v))
  cases σ
  · have e : ∑ x, ∑ z, ‖Gt sz n E t false ω z x‖ ^ 2 * (lwExpTerm4_rho sz n b z * lwExpTerm4_rho sz n c x) =
        lwExpTerm4_Pm sz n E t ω c b := by
      unfold lwExpTerm4_Pm
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      have h1 : Gt sz n E t false ω x y = (starRingEnd ℂ) (Gt sz n E t true ω y x) :=
        (lwExpTerm2_conj_Gt sz n E t true ω y x).symm
      rw [h1, Complex.norm_conj, mul_comm (lwExpTerm4_rho sz n b x)]
    rw [e]
    exact hle c b
  · exact hle b c

/-- **Target 5** (`LwExpTerm4L3Pin`), pathwise: the 3-loop sum of `I₂`, `I₃`,
`W^d Σ_a ‖𝓛^{(3)}_{(+,+,σ),(a,b,c)}‖ ≤ η_t⁻¹ A (max 𝓛^{(2)}_{(-,+)})^{1/2}` for `A ≥ max_x |G_{xx}|`.
`𝓛^{(3)} = Σ_{x,y,z} G_{xy} w_a(y) G_{yz} w_b(z) Ĝ_{zx} w_c(x)`; `Σ_a w_a = W^{-d}`;
`Σ_y |G_{xy}||G_{yz}| ≤ A/η` (vertex Ward identity, `lwExpTerm4_vertex`); then weighted Cauchy-Schwarz over
the pairs `(z, x)`, whose weights `ρ_b(z) ρ_c(x)` sum to `1`. -/
theorem lwExpTerm4_L3 (d : ℕ) (sz : Sizes d) (n : ℕ) (E t : ℝ) (hE : |E| < 2) (ht : t < 1)
    (σ : Bool) (b c : Zd d (sz.L n)) (ω : sz.SeqΩ) (A : ℝ)
    (hA : ∀ x : Idx d (sz.L n) (sz.W n), ‖Gt sz n E t true ω x x‖ ≤ A) :
    (((sz.W n : ℕ) : ℝ) ^ d) * ∑ a : Zd d (sz.L n), ‖Lloop sz n E t ![true, true, σ] ![a, b, c] ω‖ ≤
      (etaT E t)⁻¹ * A * Real.sqrt (STmaxLoop2 sz n E t ω) := by
  have hη := etaT_pos hE ht
  have hWd := lwExpTerm4_Wd_pos sz n (d := d)
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA (0 : Idx d (sz.L n) (sz.W n)))
  set G := Gt sz n E t true ω with hG
  set Gs := Gt sz n E t σ ω with hGs
  set ρ := lwExpTerm4_rho sz n with hρ
  -- the pointwise bound of one 3-loop
  have hpt : ∀ a : Zd d (sz.L n), ‖Lloop sz n E t ![true, true, σ] ![a, b, c] ω‖ ≤
      ∑ x, ∑ y, ∑ z, ‖G x y‖ * ‖G y z‖ * ‖Gs z x‖ * (ρ b z * ρ c x) * ρ a y := by
    intro a
    rw [lwExpTerm2_Lloop3]
    unfold lwExpTerm2_L3
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun y _ => norm_sum_le _ _)).trans ?_)
    refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun z _ => ?_
    simp only [norm_mul, lwExpTerm4_norm_w]
    exact le_of_eq (by ring)
  have hsum : (((sz.W n : ℕ) : ℝ) ^ d) * ∑ a, ‖Lloop sz n E t ![true, true, σ] ![a, b, c] ω‖ ≤
      ∑ x, ∑ y, ∑ z, ‖G x y‖ * ‖G y z‖ * ‖Gs z x‖ * (ρ b z * ρ c x) := by
    refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => hpt a) hWd.le).trans (le_of_eq ?_)
    have e : ∑ a, ∑ x, ∑ y, ∑ z, ‖G x y‖ * ‖G y z‖ * ‖Gs z x‖ * (ρ b z * ρ c x) * ρ a y =
        ∑ x, ∑ y, ∑ z, ‖G x y‖ * ‖G y z‖ * ‖Gs z x‖ * (ρ b z * ρ c x) * ∑ a, ρ a y := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.mul_sum]
    rw [e]
    simp_rw [hρ, lwExpTerm4_rho_sum_blocks]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    field_simp
  -- sum over y first
  have hy : ∑ x, ∑ y, ∑ z, ‖G x y‖ * ‖G y z‖ * ‖Gs z x‖ * (ρ b z * ρ c x) ≤
      (A * (etaT E t)⁻¹) * ∑ x, ∑ z, (ρ b z * ρ c x) * ‖Gs z x‖ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [Finset.mul_sum]
    calc ∑ y, ∑ z, ‖G x y‖ * ‖G y z‖ * ‖Gs z x‖ * (ρ b z * ρ c x)
        = ∑ z, ∑ y, ‖G x y‖ * ‖G y z‖ * ‖Gs z x‖ * (ρ b z * ρ c x) := Finset.sum_comm
      _ ≤ ∑ z, (A * (etaT E t)⁻¹) * ((ρ b z * ρ c x) * ‖Gs z x‖) := by
          refine Finset.sum_le_sum fun z _ => ?_
          have h := lwExpTerm4_vertex sz n hE ht ω hA x z
          have hp : 0 ≤ (ρ b z * ρ c x) * ‖Gs z x‖ :=
            mul_nonneg (mul_nonneg (lwExpTerm4_rho_nonneg sz n b z) (lwExpTerm4_rho_nonneg sz n c x))
              (norm_nonneg _)
          calc ∑ y, ‖G x y‖ * ‖G y z‖ * ‖Gs z x‖ * (ρ b z * ρ c x)
              = (∑ y, ‖G x y‖ * ‖G y z‖) * ((ρ b z * ρ c x) * ‖Gs z x‖) := by
                rw [Finset.sum_mul]
                refine Finset.sum_congr rfl fun y _ => ?_
                ring
            _ ≤ _ := mul_le_mul_of_nonneg_right h hp
  -- weighted Cauchy-Schwarz over the pairs
  have hcs := lwExpTerm4_cs_weighted (fun q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) => ρ b q.2 * ρ c q.1)
    (fun q => ‖Gs q.2 q.1‖) (fun q => mul_nonneg (lwExpTerm4_rho_nonneg sz n b q.2) (lwExpTerm4_rho_nonneg sz n c q.1))
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type] at hcs
  have hone : ∑ x : Idx d (sz.L n) (sz.W n), ∑ z : Idx d (sz.L n) (sz.W n), ρ b z * ρ c x = 1 := by
    have : ∀ x, ∑ z, ρ b z * ρ c x = ρ c x := fun x => by
      rw [← Finset.sum_mul, hρ, lwExpTerm4_rho_sum_pts, one_mul]
    simp_rw [this]
    exact lwExpTerm4_rho_sum_pts sz n c
  simp only [hone, one_mul] at hcs
  have hQ := lwExpTerm4_Q_le sz n E t σ b c ω
  have hQ' : ∑ x, ∑ z, ρ b z * ρ c x * ‖Gs z x‖ ^ 2 ≤ STmaxLoop2 sz n E t ω := by
    refine le_trans (le_of_eq ?_) hQ
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => ?_
    ring
  have hU : ∑ x, ∑ z, ρ b z * ρ c x * ‖Gs z x‖ ≤ Real.sqrt (STmaxLoop2 sz n E t ω) := by
    have hU0 : 0 ≤ ∑ x, ∑ z, ρ b z * ρ c x * ‖Gs z x‖ :=
      Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun z _ =>
        mul_nonneg (mul_nonneg (lwExpTerm4_rho_nonneg sz n b z) (lwExpTerm4_rho_nonneg sz n c x)) (norm_nonneg _)
    exact Real.le_sqrt_of_sq_le (hcs.trans hQ')
  calc _ ≤ _ := hsum
    _ ≤ _ := hy
    _ ≤ (A * (etaT E t)⁻¹) * Real.sqrt (STmaxLoop2 sz n E t ω) := mul_le_mul_of_nonneg_left hU (by positivity)
    _ = _ := by ring

/-- `|G_{xx}| ≤ η⁻¹`: `|G_{xx}|² ≤ Σ_y |G_{xy}|² = Im G_{xx}/η ≤ |G_{xx}|/η` (the row Ward identity). -/
private theorem lwExpTerm4_Gt_entry_le {E t : ℝ} (hE : |E| < 2) (ht : t < 1) (ω : sz.SeqΩ)
    (x : Idx d (sz.L n) (sz.W n)) : ‖Gt sz n E t true ω x x‖ ≤ (etaT E t)⁻¹ := by
  have hη := etaT_pos hE ht
  have h := lwExpTerm4_Gt_ward_row sz n hE ht ω x
  have h1 : ‖Gt sz n E t true ω x x‖ ^ 2 ≤ ∑ y, ‖Gt sz n E t true ω x y‖ ^ 2 :=
    Finset.single_le_sum (f := fun y => ‖Gt sz n E t true ω x y‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ x)
  have h2 : (Gt sz n E t true ω x x).im ≤ ‖Gt sz n E t true ω x x‖ := Complex.im_le_norm _
  set g : ℝ := ‖Gt sz n E t true ω x x‖ with hg
  have hg0 : 0 ≤ g := norm_nonneg _
  have h3 : etaT E t * g ^ 2 ≤ g := by
    calc etaT E t * g ^ 2 ≤ etaT E t * ∑ y, ‖Gt sz n E t true ω x y‖ ^ 2 := mul_le_mul_of_nonneg_left h1 hη.le
      _ = _ := h
      _ ≤ g := h2
  by_contra hcon
  push Not at hcon
  have h4 : 1 < etaT E t * g := by
    have := mul_lt_mul_of_pos_left hcon hη
    rwa [mul_inv_cancel₀ hη.ne'] at this
  nlinarith

end Weights


/-! ## 4. Copies of the private machinery of `LWExpTerm.lean` (T2236, `LWExpTerm.lean:196-203, 336-457`, private there) -/

private theorem lwExpTerm4_prec_congr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}
    {U : ℕ → Type*} {ξ ξ' ζ ζ' : ∀ l, U l → Ω → ℝ} (hξ : ∀ l u ω, ξ l u ω = ξ' l u ω)
    (hζ : ∀ l u ω, ζ l u ω = ζ' l u ω) (h : StochDomAt P size ξ ζ) : StochDomAt P size ξ' ζ' := by
  have e1 : ξ = ξ' := by funext l u ω; exact hξ l u ω
  have e2 : ζ = ζ' := by funext l u ω; exact hζ l u ω
  subst e1 e2
  exact h


section Common

variable {d : ℕ} (sz : Sizes d)

private theorem lwExpTerm4_vec1 {α : Type*} (x : α) : (![x] : Fin 1 → α) = fun _ => x := by
  funext i
  fin_cases i
  rfl

/-- `tr(Ǧ E_a)` against `𝒦^{(1)} = m` (`ST_Kloop_one`) in the `![·]` notation of the pins. -/
private theorem lwExpTerm4_Kloop_one (n : ℕ) (E u : ℝ) (σ : Bool) (a : Zd d (sz.L n)) :
    STKloop sz n E u ![σ] ![a] = mSigma E σ := by
  rw [lwExpTerm4_vec1, lwExpTerm4_vec1]
  exact ST_Kloop_one sz n E u σ a

/-- The eventual facts along the flow at the time sequence `t`: `η_t⁻¹ ≤ N`, `W^{-d}B_{t,0} ≤ 1`,
`N⁻¹ ≤ W^{-d}B_{t,0}`, `4 ≤ N`, and `|𝒦^{(2)}| ≤ N` for every `(σ, a)`. -/
private theorem lwExpTerm4_facts (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) {z : ℕ → ℂ}
    (hz : STFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n) (htz : ∀ n, t n ≤ lemT (z n)) :
    ∀ᶠ n in atTop, (etaT (STflowE z n) (t n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ∧
      sz.Bctl n (t n) ≤ 1 ∧ ((sz.size n : ℕ) : ℝ)⁻¹ ≤ sz.Bctl n (t n) ∧
      (4 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ∧
      ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖STKloop sz n (STflowE z n) (t n) σ a‖ ≤ ((sz.size n : ℕ) : ℝ) := by
  have hsz : sz.SizeTendsto := hz.1.2.2.1
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hz htz
  have hK := (st6_prec_det_iff sz hsz _ _).1 (stKbound_of_flow sz hd hκ hz t ht0 ht1 2 (by norm_num)) 1
    one_pos
  filter_upwards [expAvg_eta_inv_le sz hκ hε hz, st5_Bctl_le_one sz hκ hε hz htz, hK,
    hsz.eventually (eventually_ge_atTop 4)] with n hη hB1 hKn hN4
  refine ⟨hη (t n) (htz n), hB1 (t n) le_rfl, expAvg_Bctl_ge sz n (ht0 n) (ht1 n), hN4, ?_⟩
  intro σ a
  have h := hKn (σ, a)
  have hB := hB1 (t n) le_rfl
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  simp only [Nat.reduceSub, pow_one, Real.rpow_one] at h
  calc _ ≤ ((sz.size n : ℕ) : ℝ) * sz.Bctl n (t n) := h
    _ ≤ ((sz.size n : ℕ) : ℝ) * 1 := mul_le_mul_of_nonneg_left hB hNpos.le
    _ = _ := mul_one _

/-- `‖𝓛^{(1)} - m‖ ≤ 2N` (`‖𝓛^{(1)}‖ ≤ η⁻¹ ≤ N`, `‖m‖ = 1`). -/
private theorem lwExpTerm4_env_X (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht : t < 1) {N : ℝ}
    (hη : (etaT E t)⁻¹ ≤ N) (hN : 1 ≤ N) (σ : Bool) (a : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    ‖Lloop sz n E t ![σ] ![a] ω - mSigma E σ‖ ≤ 2 * N := by
  have h1 : ‖Lloop sz n E t ![σ] ![a] ω‖ ≤ (etaT E t)⁻¹ ^ 1 :=
    norm_Lloop_le sz n hE ht (k := 0) ![σ] ![a] ω
  rw [pow_one] at h1
  calc _ ≤ ‖Lloop sz n E t ![σ] ![a] ω‖ + ‖mSigma E σ‖ := norm_sub_le _ _
    _ ≤ N + 1 := by rw [norm_mSigma hE.le]; linarith
    _ ≤ 2 * N := by linarith

/-- `‖𝓛^{(2)}‖ ≤ N²`. -/
private theorem lwExpTerm4_env_L2 (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht : t < 1) {N : ℝ}
    (hη : (etaT E t)⁻¹ ≤ N) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    ‖Lloop sz n E t σ a ω‖ ≤ N ^ 2 := by
  have h1 := norm_Lloop_le sz n hE ht (k := 1) σ a ω
  have h0 : 0 ≤ (etaT E t)⁻¹ := (inv_pos.2 (etaT_pos hE ht)).le
  exact h1.trans (pow_le_pow_left₀ h0 hη 2)

/-- `‖𝓛^{(2)} - 𝒦^{(2)}‖ ≤ 2N²` given `‖𝒦^{(2)}‖ ≤ N`, `1 ≤ N`. -/
private theorem lwExpTerm4_env_D (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht : t < 1) {N : ℝ}
    (hη : (etaT E t)⁻¹ ≤ N) (hN : 1 ≤ N) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (hK : ‖STKloop sz n E t σ a‖ ≤ N) (ω : sz.SeqΩ) :
    ‖Lloop sz n E t σ a ω - STKloop sz n E t σ a‖ ≤ 2 * N ^ 2 := by
  calc _ ≤ ‖Lloop sz n E t σ a ω‖ + ‖STKloop sz n E t σ a‖ := norm_sub_le _ _
    _ ≤ N ^ 2 + N := add_le_add (lwExpTerm4_env_L2 sz n hE ht hη σ a ω) hK
    _ ≤ 2 * N ^ 2 := by nlinarith

/-- `N^{-3} ≤ B³` from `N⁻¹ ≤ B`. -/
private theorem lwExpTerm4_floor3 {N B : ℝ} (hN : 0 < N) (hB : N⁻¹ ≤ B) : N ^ (-(3 : ℝ)) ≤ B ^ 3 := by
  have h : N ^ (-(3 : ℝ)) = (N⁻¹) ^ 3 := by
    rw [Real.rpow_neg hN.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow]
  rw [h]
  exact pow_le_pow_left₀ (inv_nonneg.2 hN.le) hB 3

/-- **`𝔼[(𝓛^{(1)} - m)(𝓛 - 𝒦)^{(2)}] ≺ B³`**, all charges, uniformly in `(σ₁, σ, a, a₁)`: the product
`‖X‖‖D‖ ≺ B · B²` (`STLK` at `k = 1, 2`, `ST_Kloop_one`; `StochDomAt.mul`), then `≺ → 𝔼` with the
envelope `4N³ ≤ N⁴` and the floor `N⁻³ ≤ B³` (`lwExpTerm_prec_integral`). -/
private theorem lwExpTerm4_XD (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) {z : ℕ → ℂ}
    (hz : STFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n) (htz : ∀ n, t n ≤ lemT (z n))
    (hLK : STLK sz (STflowE z) t) :
    sz.Prec (U := fun n => (Bool × (Fin 2 → Bool)) × (Fin 2 → Zd d (sz.L n)) × Zd d (sz.L n))
      (fun n p _ => ‖∫ ω, (Lloop sz n (STflowE z n) (t n) ![p.1.1] ![p.2.2] ω - mSigma (STflowE z n) p.1.1) *
          (Lloop sz n (STflowE z n) (t n) p.1.2 p.2.1 ω - STKloop sz n (STflowE z n) (t n) p.1.2 p.2.1)
            ∂(sz.seqP)‖)
      (fun n _ _ => (sz.Bctl n (t n)) ^ 3) := by
  have hsz : sz.SizeTendsto := hz.1.2.2.1
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hz htz
  have hE2 : ∀ n, |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hz
  have hfac := lwExpTerm4_facts sz hd hκ hε hz ht0 htz
  refine lwExpTerm_prec_integral sz (V := fun n => (Bool × (Fin 2 → Bool)) × (Fin 2 → Zd d (sz.L n)) × Zd d (sz.L n))
    (fun n p ω => (Lloop sz n (STflowE z n) (t n) ![p.1.1] ![p.2.2] ω - mSigma (STflowE z n) p.1.1) *
      (Lloop sz n (STflowE z n) (t n) p.1.2 p.2.1 ω - STKloop sz n (STflowE z n) (t n) p.1.2 p.2.1))
    (fun n _ => (sz.Bctl n (t n)) ^ 3) (Kenv := 4) (Kf := 3) hsz ?_ ?_ ?_
  · filter_upwards [hfac] with n hn
    obtain ⟨hη, hB1, hBN, hN4, hK⟩ := hn
    intro p ω
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
    have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have h1 := lwExpTerm4_env_X sz n (hE2 n) (ht1 n) hη hN1 p.1.1 p.2.2 ω
    have h2 := lwExpTerm4_env_D sz n (hE2 n) (ht1 n) hη hN1 p.1.2 p.2.1 (hK _ _) ω
    set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
    rw [norm_mul]
    calc _ ≤ (2 * N) * (2 * N ^ 2) := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = 4 * N ^ 3 := by ring
      _ ≤ N ^ (4 : ℝ) := by
          have h4 : N ^ (4 : ℝ) = N ^ 4 := by rw [← Real.rpow_natCast]; norm_num
          rw [h4]
          nlinarith [pow_pos hNpos 3]
  · filter_upwards [hfac] with n hn
    obtain ⟨hη, hB1, hBN, hN4, hK⟩ := hn
    intro p
    have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    exact lwExpTerm4_floor3 hNpos hBN
  · have h₁ := StochDomAt.precomp_param (hLK 1 le_rfl)
      (fun n (p : (Bool × (Fin 2 → Bool)) × (Fin 2 → Zd d (sz.L n)) × Zd d (sz.L n)) =>
        ((![p.1.1], ![p.2.2]) : (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n))))
    have h₂ := StochDomAt.precomp_param (hLK 2 (by norm_num))
      (fun n (p : (Bool × (Fin 2 → Bool)) × (Fin 2 → Zd d (sz.L n)) × Zd d (sz.L n)) =>
        ((p.1.2, p.2.1) : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))))
    have hm := StochDomAt.mul (P := sz.seqP) (size := sz.size) (tendsto_size sz hsz)
      (fun n p ω => norm_nonneg _) (fun n p ω => pow_nonneg (STBctl_pos sz n (ht1 n)).le _) h₁ h₂
    refine lwExpTerm4_prec_congr (fun n p ω => ?_) (fun n p ω => ?_) hm
    · simp only [Pi.mul_apply, norm_mul, lwExpTerm4_Kloop_one]
    · simp only [Pi.mul_apply]; ring


end Common


/-! ## 5. Targets 3 and 4: `(WI_calK)` for the charges `(s,+)` and the diagonal entries -/

/-- **Target 3** (`LwExpTerm4KwardPin`): `(WI_calK)` for `𝒦^{(2)}_{(s,+)}`, both `s`, the FIRST label summed:
`W^d Σ_a ‖𝒦^{(2)}_{(s,+),(a,b)}‖ ≺ η_t⁻¹`.  `STKward` (`k = 2`, charge `![true, s]`, `stKward_of_flow`) sums the
last label of `(+, s)`; `𝒦^{(2)}_{(s,+),(x,b)} = 𝒦^{(2)}_{(+,s),(b,x)}` by `KLK_rotate` (`σ = [true]`). -/
theorem lwExpTerm4_kward (d : ℕ) : 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        Prec sz (U := fun n => Bool × Zd d (sz.L n))
          (fun n p _ => (((sz.W n : ℕ) : ℝ) ^ d) * ∑ a : Zd d (sz.L n),
              ‖STKloop sz n (STflowE z n) (t n) ![p.1, true] ![a, p.2]‖)
          (fun n _ _ => (etaT (STflowE z n) (t n))⁻¹) := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz t ht0 htz
  have hsz : sz.SizeTendsto := hz.1.2.2.1
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hz htz
  have hE2 : ∀ n, |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hz
  have hKw := (st6_prec_det_iff sz hsz _ _).1 (stKward_of_flow sz hd hκ hz t ht0 ht1 2 le_rfl)
  refine (st6_prec_det_iff sz hsz _ _).2 fun τ hτ => ?_
  filter_upwards [hKw τ hτ] with n hn
  rintro ⟨s, b⟩
  have h := hn (![true, s], ![b])
  have hrot : ∀ x : Zd d (sz.L n),
      STKI sz n (STflowE z n) (t n) ⟨List.ofFn ![true, s], List.ofFn ![b] ++ [x]⟩ =
        STKloop sz n (STflowE z n) (t n) ![s, true] ![x, b] := by
    intro x
    have hr := KLK_rotate d (sz.L n) (sz.W n) (sz.lam n) (STflowE z n) (sz.three_le_L n) (sz.W_pos n)
      (hE2 n) (t n) ⟨ht0 n, ht1 n⟩ s x [true] [b] rfl
    simp only [STKI, STKloop, KLloopOf, List.ofFn_succ, List.ofFn_zero]
    simpa using hr.symm
  simp only [hrot] at h
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := lwExpTerm4_Wd_pos sz n
  have hη := etaT_pos (hE2 n) (ht1 n)
  simp only [Nat.sub_self, pow_zero, mul_one] at h
  calc _ ≤ ((sz.W n : ℕ) : ℝ) ^ d * (((sz.size n : ℕ) : ℝ) ^ τ * ((((sz.W n : ℕ) : ℝ) ^ d *
        etaT (STflowE z n) (t n))⁻¹)) := mul_le_mul_of_nonneg_left h hWd.le
    _ = _ := by field_simp

/-- **Target 4** (`LwExpTerm4DiagPin`): `max_x |(G_t)_{xx}| ≺ 1` from `STLocalEntry` at `(x, x)`:
`STblk x - STblk x = 0`, `zdistInf 0 = 0`, `STWB sz n τ 0 = sz.Bctl n τ ≤ 1` (`st5_Bctl_le_one`), `‖m‖ = 1`
(`norm_mE`); the failure event of `‖G_xx‖ > N^τ` is inside that of `‖G_xx - m‖² > N^τ B`. -/
theorem lwExpTerm4_diag (d : ℕ) : 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        STLocalEntry sz (STflowE z) t →
        Prec sz (U := fun n => Idx d (sz.L n) (sz.W n))
          (fun n x ω => ‖Gt sz n (STflowE z n) (t n) true ω x x‖)
          (fun _ _ _ => 1) := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz t ht0 htz hLE
  have hsz : sz.SizeTendsto := hz.1.2.2.1
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hz htz
  have hE2 : ∀ n, |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hz
  unfold STLocalEntry Prec at hLE
  unfold Prec
  intro τ hτ D hD
  filter_upwards [hLE τ hτ D hD, st5_Bctl_le_one sz hκ hε hz htz,
    ((tendsto_rpow_atTop hτ).comp hsz).eventually (eventually_ge_atTop 4)] with n hn hB hN4
  refine le_trans (measure_mono ?_) hn
  intro ω hω
  obtain ⟨x, hx⟩ := hω
  refine ⟨(x, x), ?_⟩
  set u : ℝ := ((sz.size n : ℕ) : ℝ) ^ τ with hu
  have hu4 : (4 : ℝ) ≤ u := hN4
  have hB1 : sz.Bctl n (t n) ≤ 1 := hB (t n) le_rfl
  have hB0 : 0 < sz.Bctl n (t n) := STBctl_pos sz n (ht1 n)
  have hzero : STWB sz n (t n) (zdistInf d (sz.L n) (STblk sz n x - STblk sz n x)) = sz.Bctl n (t n) := by
    rw [sub_self]
    have : zdistInf d (sz.L n) (0 : Zd d (sz.L n)) = 0 := by simp [zdistInf]
    rw [this]
    rfl
  change u * sz.STWB n (t n) (zdistInf d (sz.L n) (STblk sz n x - STblk sz n x)) <
    ‖STGM sz n (STflowE z n) (t n) ω x x‖ ^ 2
  rw [hzero]
  have hm : ‖mE (STflowE z n)‖ = 1 := norm_mE (hE2 n).le
  have hGM : ‖STGM sz n (STflowE z n) (t n) ω x x‖ = ‖Gt sz n (STflowE z n) (t n) true ω x x - mE (STflowE z n)‖ := by
    simp [STGM]
  have hnorm : ‖Gt sz n (STflowE z n) (t n) true ω x x‖ ≤ ‖STGM sz n (STflowE z n) (t n) ω x x‖ + 1 := by
    rw [hGM, ← hm]
    calc _ = ‖(Gt sz n (STflowE z n) (t n) true ω x x - mE (STflowE z n)) + mE (STflowE z n)‖ := by
          rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have h1 : u < ‖Gt sz n (STflowE z n) (t n) true ω x x‖ := by simpa using hx
  have h2 : u - 1 < ‖STGM sz n (STflowE z n) (t n) ω x x‖ := by linarith
  have h3 : (u - 1) ^ 2 < ‖STGM sz n (STflowE z n) (t n) ω x x‖ ^ 2 :=
    pow_lt_pow_left₀ h2 (by linarith) two_ne_zero
  nlinarith


/-! ## 6. Target 6: `lwExpI1K_holds` (`(eq:termI1)`, `B:37-41`) -/

section I1

variable {d : ℕ} (sz : Sizes d)

/-- `𝔼 (𝓛^{(1)} - m) = 𝔼 𝓛^{(1)} - m` (a probability space, `𝓛^{(1)}` bounded). -/
private theorem lwExpTerm4_int_X (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht : t < 1) (σ : Bool)
    (a : Zd d (sz.L n)) :
    ∫ ω, (Lloop sz n E t ![σ] ![a] ω - mSigma E σ) ∂(sz.seqP) =
      (∫ ω, Lloop sz n E t (fun _ : Fin 1 => σ) (fun _ => a) ω ∂(sz.seqP)) - mSigma E σ := by
  rw [integral_sub (lwExpTerm2_BM_integrable (lwExpTerm2_BM_Lloop sz n hE ht (k := 0) _ _))
    (integrable_const _), integral_const]
  simp [lwExpTerm4_vec1]

/-- `𝔼[X 𝓛^{(2)}] = (𝔼 X) 𝒦^{(2)} + 𝔼[X (𝓛 - 𝒦)^{(2)}]`, `X = 𝓛^{(1)} - m`. -/
private theorem lwExpTerm4_int_XL (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht : t < 1) (σ₁ : Bool)
    (a₁ : Zd d (sz.L n)) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ∫ ω, (Lloop sz n E t ![σ₁] ![a₁] ω - mSigma E σ₁) * Lloop sz n E t σ a ω ∂(sz.seqP) =
      (∫ ω, (Lloop sz n E t ![σ₁] ![a₁] ω - mSigma E σ₁) ∂(sz.seqP)) * STKloop sz n E t σ a +
        ∫ ω, (Lloop sz n E t ![σ₁] ![a₁] ω - mSigma E σ₁) *
          (Lloop sz n E t σ a ω - STKloop sz n E t σ a) ∂(sz.seqP) := by
  have hX := lwExpTerm2_BM_X sz n hE ht σ₁ a₁
  have h1 : lwExpTerm2_BM (fun ω : sz.SeqΩ => (Lloop sz n E t ![σ₁] ![a₁] ω - mSigma E σ₁) *
      STKloop sz n E t σ a) := lwExpTerm2_BM_mul hX (lwExpTerm2_BM_const _)
  have h2 : lwExpTerm2_BM (fun ω : sz.SeqΩ => (Lloop sz n E t ![σ₁] ![a₁] ω - mSigma E σ₁) *
      (Lloop sz n E t σ a ω - STKloop sz n E t σ a)) :=
    lwExpTerm2_BM_mul hX (lwExpTerm2_BM_sub (lwExpTerm2_BM_Lloop sz n hE ht (k := 1) _ _)
      (lwExpTerm2_BM_const _))
  have hpt : ∀ ω : sz.SeqΩ, (Lloop sz n E t ![σ₁] ![a₁] ω - mSigma E σ₁) * Lloop sz n E t σ a ω =
      (Lloop sz n E t ![σ₁] ![a₁] ω - mSigma E σ₁) * STKloop sz n E t σ a +
        (Lloop sz n E t ![σ₁] ![a₁] ω - mSigma E σ₁) *
          (Lloop sz n E t σ a ω - STKloop sz n E t σ a) := fun ω => by ring
  simp_rw [hpt]
  rw [integral_add (lwExpTerm2_BM_integrable h1) (lwExpTerm2_BM_integrable h2), integral_mul_const]


/-- **`I₁K`, one size** (`(eq:termI1)`): `‖Σ_{a₁} K_{a₁b} 𝔼[X_{a₁} 𝓛^{(2)}]‖ ≤ C (x k + y)` when the column sums of
`‖K‖` are `≤ C` (target 1; `Σ_{a₁} ‖S^{(B)}_{a₁b}‖ = 1` in `lwExpTerm_I1_n`), `‖𝔼 X_{a₁}‖ ≤ x`, `‖𝒦^{(2)}‖ ≤ k`,
`‖𝔼[X_{a₁} (𝓛-𝒦)^{(2)}]‖ ≤ y`. -/
private theorem lwExpTerm4_I1K_n (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht : t < 1) (σ₁ : Bool)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (K : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) {C : ℝ}
    (hC : ∑ a₁, ‖K a₁ (a 1)‖ ≤ C) {x k y : ℝ}
    (hX : ∀ a₁ : Zd d (sz.L n), ‖∫ ω, (Lloop sz n E t ![σ₁] ![a₁] ω - mSigma E σ₁) ∂(sz.seqP)‖ ≤ x)
    (hK : ‖STKloop sz n E t σ a‖ ≤ k)
    (hXD : ∀ a₁ : Zd d (sz.L n), ‖∫ ω, (Lloop sz n E t ![σ₁] ![a₁] ω - mSigma E σ₁) *
      (Lloop sz n E t σ a ω - STKloop sz n E t σ a) ∂(sz.seqP)‖ ≤ y) :
    ‖∑ a₁, K a₁ (a 1) *
        ∫ ω, (Lloop sz n E t ![σ₁] ![a₁] ω - mSigma E σ₁) * Lloop sz n E t σ a ω ∂(sz.seqP)‖ ≤
      C * (x * k + y) := by
  have hx0 : 0 ≤ x := (norm_nonneg _).trans (hX 0)
  have hterm : ∀ a₁ : Zd d (sz.L n), ‖∫ ω, (Lloop sz n E t ![σ₁] ![a₁] ω - mSigma E σ₁) *
      Lloop sz n E t σ a ω ∂(sz.seqP)‖ ≤ x * k + y := by
    intro a₁
    rw [lwExpTerm4_int_XL sz n hE ht σ₁ a₁ σ a]
    refine (norm_add_le _ _).trans (add_le_add ?_ (hXD a₁))
    rw [norm_mul]
    exact mul_le_mul (hX a₁) hK (norm_nonneg _) hx0
  have hxky : 0 ≤ x * k + y := (norm_nonneg _).trans (hterm 0)
  calc _ ≤ ∑ a₁, ‖K a₁ (a 1) *
        ∫ ω, (Lloop sz n E t ![σ₁] ![a₁] ω - mSigma E σ₁) * Lloop sz n E t σ a ω ∂(sz.seqP)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ a₁, ‖K a₁ (a 1)‖ * (x * k + y) := by
        refine Finset.sum_le_sum fun a₁ _ => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hterm a₁) (norm_nonneg _)
    _ = (∑ a₁, ‖K a₁ (a 1)‖) * (x * k + y) := by rw [← Finset.sum_mul]
    _ ≤ C * (x * k + y) := mul_le_mul_of_nonneg_right hC hxky

end I1

/-- **Target 6** (`lwExpI1K_holds`): `I₁ + J₁ ≺ B³` for every decaying first kernel `K`.  The route of
`lwExpI1_holds` (`LWExpTerm.lean:535`): `𝓛^{(2)} = 𝒦^{(2)} + (𝓛-𝒦)^{(2)}`, `‖𝔼 X_{a₁}‖ ≺ B²` (`STExpAvgAt`),
`‖𝒦^{(2)}‖ ≺ B` (`STKbound`), `‖𝔼[X (𝓛-𝒦)^{(2)}]‖ ≺ B³` (`lwExpTerm4_XD`); the column sums of `K` are `≤ C`
(target 1) and the constant `C` is absorbed by `N^{τ/3} ≥ 2C + 2`. -/
theorem lwExpI1K_holds (d : ℕ) : LWExpI1K d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz t ht0 htz K hK hLW hLK
  have hsz : sz.SizeTendsto := hz.1.2.2.1
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hz htz
  have hE2 : ∀ n, |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hz
  obtain ⟨C, hC0, hCsum⟩ := lwExpTerm4_kerSum d sz K hK
  have hEX := (st6_prec_det_iff sz hsz _ _).1 (STExpAvgAt_of_LWAvgLaw sz hd hκ hε hz t ht0 htz hLW)
  have hKb := (st6_prec_det_iff sz hsz _ _).1
    (stKbound_of_flow sz hd hκ hz t ht0 ht1 2 (by norm_num))
  have hXD := (st6_prec_det_iff sz hsz _ _).1 (lwExpTerm4_XD sz hd hκ hε hz ht0 htz hLK)
  refine (st6_prec_det_iff sz hsz _ _).2 ?_
  intro τ hτ
  have hτ3 : 0 < τ / 3 := by positivity
  filter_upwards [hEX (τ / 3) hτ3, hKb (τ / 3) hτ3, hXD (τ / 3) hτ3,
    ((tendsto_rpow_atTop hτ3).comp hsz).eventually (eventually_ge_atTop (2 * C + 2))] with n hEXn hKn hXDn hN2
  rintro ⟨⟨σ₁, σ⟩, a⟩
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := Nat.cast_pos.mpr (by have := sz.one_le_size n; omega)
  set B : ℝ := sz.Bctl n (t n) with hBdef
  have hB : 0 < B := STBctl_pos sz n (ht1 n)
  have key := lwExpTerm4_I1K_n sz n (hE2 n) (ht1 n) σ₁ σ a (K n) (hCsum n (a 1)).1 (x := N ^ (τ / 3) * B ^ 2)
    (k := N ^ (τ / 3) * B) (y := N ^ (τ / 3) * B ^ 3)
    (fun a₁ => by rw [lwExpTerm4_int_X sz n (hE2 n) (ht1 n)]; exact hEXn (σ₁, a₁))
    (by simpa using hKn (σ, a)) (fun a₁ => hXDn ((σ₁, σ), (a, a₁)))
  refine key.trans ?_
  have hu3 : N ^ τ = (N ^ (τ / 3)) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; congr 1; push_cast; ring
  rw [hu3]
  have hN2' : 2 * C + 2 ≤ N ^ (τ / 3) := hN2
  set u : ℝ := N ^ (τ / 3) with hu
  have hB3 : 0 < B ^ 3 := by positivity
  have h1 : 0 ≤ u ^ 2 - C * u - C := by nlinarith
  have h2 : 0 ≤ u * (u ^ 2 - C * u - C) * B ^ 3 :=
    mul_nonneg (mul_nonneg (by linarith) h1) hB3.le
  nlinarith [h2]


/-! ## 7. Sums with a decaying first kernel: `Σ_{a₁} |K_{a₁a₂}| ≤ C` replaces `Σ_{a₁} |S^{(B)}_{a₁a₂}| = 1` -/

section KSums

variable {d : ℕ} (L : ℕ) [NeZero L] (g : ℝ) (hL : 3 ≤ L)

include hL in
/-- `Σ_{a₁,a₂,a₃} ‖K_{a₁a₂}‖ ‖S_{a₂a₃}‖ h(a₂) ≤ C Σ_{a₂} h(a₂)`, `h ≥ 0`, column sums of `K` `≤ C`. -/
private theorem lwExpTerm4_wsum2K (K : Matrix (Zd d L) (Zd d L) ℂ) {C : ℝ} (hC : ∀ b, ∑ a, ‖K a b‖ ≤ C)
    (h : Zd d L → ℝ) (h0 : ∀ a, 0 ≤ h a) :
    ∑ a₁, ∑ a₂, ∑ a₃, ‖K a₁ a₂‖ * ‖SB d L g a₂ a₃‖ * h a₂ ≤ C * ∑ a₂, h a₂ := by
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a₂ _ => ?_
  have e : ∀ a₁, ∑ a₃, ‖K a₁ a₂‖ * ‖SB d L g a₂ a₃‖ * h a₂ = ‖K a₁ a₂‖ * h a₂ := by
    intro a₁
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_norm_SB_row d L g hL, mul_one]
  simp_rw [e]
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (hC a₂) (h0 a₂)

include hL in
/-- `Σ_{a₁,a₂,a₃} ‖K_{a₁a₂}‖ ‖S_{a₂a₃}‖ h(a₃) ≤ C Σ_{a₃} h(a₃)`, `h ≥ 0`. -/
private theorem lwExpTerm4_wsum3K (K : Matrix (Zd d L) (Zd d L) ℂ) {C : ℝ} (hC : ∀ b, ∑ a, ‖K a b‖ ≤ C)
    (h : Zd d L → ℝ) (h0 : ∀ a, 0 ≤ h a) :
    ∑ a₁, ∑ a₂, ∑ a₃, ‖K a₁ a₂‖ * ‖SB d L g a₂ a₃‖ * h a₃ ≤ C * ∑ a₃, h a₃ := by
  have hS0 : ∀ a b, 0 ≤ ‖SB d L g a b‖ := fun _ _ => norm_nonneg _
  have e1 : ∑ a₁, ∑ a₂, ∑ a₃, ‖K a₁ a₂‖ * ‖SB d L g a₂ a₃‖ * h a₃ =
      ∑ a₂, (∑ a₁, ‖K a₁ a₂‖) * ∑ a₃, ‖SB d L g a₂ a₃‖ * h a₃ := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a₂ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a₃ _ => ?_
    ring
  rw [e1]
  calc ∑ a₂, (∑ a₁, ‖K a₁ a₂‖) * ∑ a₃, ‖SB d L g a₂ a₃‖ * h a₃
      ≤ ∑ a₂, C * ∑ a₃, ‖SB d L g a₂ a₃‖ * h a₃ :=
        Finset.sum_le_sum fun a₂ _ => mul_le_mul_of_nonneg_right (hC a₂)
          (Finset.sum_nonneg fun a₃ _ => mul_nonneg (hS0 _ _) (h0 _))
    _ = C * ∑ a₃, (∑ a₂, ‖SB d L g a₂ a₃‖) * h a₃ := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun a₃ _ => ?_
        rw [Finset.sum_mul]
    _ = C * ∑ a₃, h a₃ := by
        congr 1
        refine Finset.sum_congr rfl fun a₃ _ => ?_
        have h1 : ∑ a₂, ‖SB d L g a₂ a₃‖ = 1 := by
          have := sum_norm_SB_row d L g hL a₃
          rw [← this]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [(SB_isSymm d L g).apply]
        rw [h1, one_mul]

end KSums


section SumsN

variable {d : ℕ} (sz : Sizes d)

private theorem lwExpTerm4_norm_sum3_le {ι : Type*} [Fintype ι] (f : ι → ι → ι → ℂ) :
    ‖∑ a₁, ∑ a₂, ∑ a₃, f a₁ a₂ a₃‖ ≤ ∑ a₁, ∑ a₂, ∑ a₃, ‖f a₁ a₂ a₃‖ :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun _ _ => norm_sum_le _ _))

private theorem lwExpTerm4_norm_Wd (n : ℕ) : ‖(((sz.W n : ℕ) : ℂ) ^ d)‖ = ((sz.W n : ℕ) : ℝ) ^ d := by
  rw [norm_pow, Complex.norm_natCast]

/-- **The `I₂`/`I₃`-type bound** (`B:43-49`): if `‖x_{a₁}‖ ‖y_{a'}‖ ≤ c`, then
`‖W^d Σ K_{a₁a₂} S_{a₂a₃} x_{a₁} y_{a'} ℓ_{a''}‖ ≤ C c W^d Σ_a ‖ℓ_a‖`, `(a', a'') = (a₃, a₂)` (`sel`) or `(a₂, a₃)`;
`Σ_{a₁} ‖K_{a₁b}‖ ≤ C`, `Σ_{a₃} ‖S_{a₂a₃}‖ = 1` (`sel`), `Σ_{a₂} ‖S_{a₂a₃}‖ = 1` (not `sel`). -/
private theorem lwExpTerm4_T23_n (n : ℕ) (K : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) {C : ℝ}
    (hC : ∀ b, ∑ a, ‖K a b‖ ≤ C) (sel : Bool) (x y ℓ : Zd d (sz.L n) → ℂ) {c : ℝ}
    (hc : ∀ a₁ a', ‖x a₁‖ * ‖y a'‖ ≤ c) :
    ‖(((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃, K a₁ a₂ * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
        (x a₁ * y (if sel then a₃ else a₂) * ℓ (if sel then a₂ else a₃))‖ ≤
      C * c * ((((sz.W n : ℕ) : ℝ) ^ d) * ∑ a, ‖ℓ a‖) := by
  rw [norm_mul, lwExpTerm4_norm_Wd]
  have hWd : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have h1 := lwExpTerm4_norm_sum3_le (fun a₁ a₂ a₃ => K a₁ a₂ * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
        (x a₁ * y (if sel then a₃ else a₂) * ℓ (if sel then a₂ else a₃)))
  have hc0 : 0 ≤ c := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans (hc 0 0)
  have h2 : ∑ a₁, ∑ a₂, ∑ a₃, ‖K a₁ a₂ * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
        (x a₁ * y (if sel then a₃ else a₂) * ℓ (if sel then a₂ else a₃))‖ ≤
      ∑ a₁, ∑ a₂, ∑ a₃, ‖K a₁ a₂‖ * ‖SB d (sz.L n) (sz.lam n) a₂ a₃‖ *
        (c * ‖ℓ (if sel then a₂ else a₃)‖) := by
    refine Finset.sum_le_sum fun a₁ _ => Finset.sum_le_sum fun a₂ _ => Finset.sum_le_sum fun a₃ _ => ?_
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    have hS : 0 ≤ ‖K a₁ a₂‖ * ‖SB d (sz.L n) (sz.lam n) a₂ a₃‖ := by positivity
    calc _ = ‖K a₁ a₂‖ * ‖SB d (sz.L n) (sz.lam n) a₂ a₃‖ *
          (‖x a₁‖ * ‖y (if sel then a₃ else a₂)‖ * ‖ℓ (if sel then a₂ else a₃)‖) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hc _ _) (norm_nonneg _)) hS
  have h3 : ∑ a₁, ∑ a₂, ∑ a₃, ‖K a₁ a₂‖ * ‖SB d (sz.L n) (sz.lam n) a₂ a₃‖ *
        (c * ‖ℓ (if sel then a₂ else a₃)‖) ≤ C * ∑ a, c * ‖ℓ a‖ := by
    cases sel
    · exact lwExpTerm4_wsum3K (sz.L n) (sz.lam n) (sz.three_le_L n) K hC (fun a => c * ‖ℓ a‖)
        (fun a => mul_nonneg hc0 (norm_nonneg _))
    · exact lwExpTerm4_wsum2K (sz.L n) (sz.lam n) (sz.three_le_L n) K hC (fun a => c * ‖ℓ a‖)
        (fun a => mul_nonneg hc0 (norm_nonneg _))
  rw [← Finset.mul_sum] at h3
  calc _ ≤ ((sz.W n : ℕ) : ℝ) ^ d * (C * (c * ∑ a, ‖ℓ a‖)) :=
        mul_le_mul_of_nonneg_left (h1.trans (h2.trans h3)) hWd
    _ = _ := by ring

/-- **The `T_a`-type bound** (`B:66-72`): `‖x_{a₁}‖ ‖y_{a₃}‖ ≤ c` gives
`‖W^d Σ K_{a₁a₂} S_{a₂a₃} x_{a₁} A_{a₂} y_{a₃}‖ ≤ C c W^d Σ_{a₂} ‖A_{a₂}‖`. -/
private theorem lwExpTerm4_Ta_n (n : ℕ) (K : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) {C : ℝ}
    (hC : ∀ b, ∑ a, ‖K a b‖ ≤ C) (x A y : Zd d (sz.L n) → ℂ) {c : ℝ}
    (hc : ∀ a₁ a₃, ‖x a₁‖ * ‖y a₃‖ ≤ c) :
    ‖(((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃, K a₁ a₂ * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
        (x a₁ * A a₂ * y a₃)‖ ≤
      C * c * ((((sz.W n : ℕ) : ℝ) ^ d) * ∑ a₂, ‖A a₂‖) := by
  rw [norm_mul, lwExpTerm4_norm_Wd]
  have hWd : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have h1 := lwExpTerm4_norm_sum3_le (fun a₁ a₂ a₃ => K a₁ a₂ * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
        (x a₁ * A a₂ * y a₃))
  have hc0 : 0 ≤ c := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans (hc 0 0)
  have h2 : ∑ a₁, ∑ a₂, ∑ a₃, ‖K a₁ a₂ * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) * (x a₁ * A a₂ * y a₃)‖ ≤
      ∑ a₁, ∑ a₂, ∑ a₃, ‖K a₁ a₂‖ * ‖SB d (sz.L n) (sz.lam n) a₂ a₃‖ * (c * ‖A a₂‖) := by
    refine Finset.sum_le_sum fun a₁ _ => Finset.sum_le_sum fun a₂ _ => Finset.sum_le_sum fun a₃ _ => ?_
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    have hS : 0 ≤ ‖K a₁ a₂‖ * ‖SB d (sz.L n) (sz.lam n) a₂ a₃‖ := by positivity
    calc _ = ‖K a₁ a₂‖ * ‖SB d (sz.L n) (sz.lam n) a₂ a₃‖ * (‖x a₁‖ * ‖y a₃‖ * ‖A a₂‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hc a₁ a₃) (norm_nonneg _)) hS
  have h3 := lwExpTerm4_wsum2K (sz.L n) (sz.lam n) (sz.three_le_L n) K hC (fun a => c * ‖A a‖)
    (fun a => mul_nonneg hc0 (norm_nonneg _))
  rw [← Finset.mul_sum] at h3
  calc _ ≤ ((sz.W n : ℕ) : ℝ) ^ d * (C * (c * ∑ a₂, ‖A a₂‖)) :=
        mul_le_mul_of_nonneg_left (h1.trans (h2.trans h3)) hWd
    _ = _ := by ring

/-- **The `T_b`-type bound** (`B:66-72`): `‖u_{a₁a₂}‖ ≤ c` gives
`‖W^d Σ K_{a₁a₂} S_{a₂a₃} u_{a₁a₂} k_{a₃}‖ ≤ C c W^d Σ_{a₃} ‖k_{a₃}‖`. -/
private theorem lwExpTerm4_Tb_n (n : ℕ) (K : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) {C : ℝ}
    (hC : ∀ b, ∑ a, ‖K a b‖ ≤ C) (u : Zd d (sz.L n) → Zd d (sz.L n) → ℂ) (k : Zd d (sz.L n) → ℂ)
    {c : ℝ} (hu : ∀ a₁ a₂, ‖u a₁ a₂‖ ≤ c) :
    ‖(((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃, K a₁ a₂ * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
        (u a₁ a₂ * k a₃)‖ ≤
      C * c * ((((sz.W n : ℕ) : ℝ) ^ d) * ∑ a₃, ‖k a₃‖) := by
  rw [norm_mul, lwExpTerm4_norm_Wd]
  have hWd : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have h1 := lwExpTerm4_norm_sum3_le (fun a₁ a₂ a₃ => K a₁ a₂ * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
        (u a₁ a₂ * k a₃))
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hu 0 0)
  have h2 : ∑ a₁, ∑ a₂, ∑ a₃, ‖K a₁ a₂ * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) * (u a₁ a₂ * k a₃)‖ ≤
      ∑ a₁, ∑ a₂, ∑ a₃, ‖K a₁ a₂‖ * ‖SB d (sz.L n) (sz.lam n) a₂ a₃‖ * (c * ‖k a₃‖) := by
    refine Finset.sum_le_sum fun a₁ _ => Finset.sum_le_sum fun a₂ _ => Finset.sum_le_sum fun a₃ _ => ?_
    rw [norm_mul, norm_mul, norm_mul]
    have hS : 0 ≤ ‖K a₁ a₂‖ * ‖SB d (sz.L n) (sz.lam n) a₂ a₃‖ := by positivity
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hu a₁ a₂) (norm_nonneg _)) hS
  have h3 := lwExpTerm4_wsum3K (sz.L n) (sz.lam n) (sz.three_le_L n) K hC (fun a => c * ‖k a‖)
    (fun a => mul_nonneg hc0 (norm_nonneg _))
  rw [← Finset.mul_sum] at h3
  calc _ ≤ ((sz.W n : ℕ) : ℝ) ^ d * (C * (c * ∑ a₃, ‖k a₃‖)) :=
        mul_le_mul_of_nonneg_left (h1.trans (h2.trans h3)) hWd
    _ = _ := by ring

end SumsN


/-! ## 8. Target 7: `lwExpI23K_holds` (`(eq:termI2)`, `B:43-49`) -/

/-- `3 N^{-(D+1)} ≤ N^{-D}` for `N ≥ 3`. -/
private theorem lwExpTerm4_three_mul_rpow_le (D : ℝ) :
    ∀ᶠ N : ℕ in atTop, 3 * (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) := by
  filter_upwards [eventually_ge_atTop 3] with N hN
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  rw [neg_add, Real.rpow_add hN0, Real.rpow_neg_one]
  have h := Real.rpow_nonneg hN0.le (-D)
  calc 3 * ((N : ℝ) ^ (-D) * (N : ℝ)⁻¹) = (N : ℝ) ^ (-D) * (3 / N) := by ring
    _ ≤ (N : ℝ) ^ (-D) * 1 := by
        gcongr; rw [div_le_one hN0]; exact hN3
    _ = _ := mul_one _

/-- A failure event eventually contained in the union of three failure events (copy of
`StochDomAt.of_subset_union`, `Defs/StochDomAt.lean:355`, with three events). -/
private theorem lwExpTerm4_prec_union3 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}
    (hsize : Tendsto size atTop atTop) {U U₁ U₂ U₃ : ℕ → Type*} {ξ ζ : ∀ l, U l → Ω → ℝ}
    {f₁ g₁ : ∀ l, U₁ l → Ω → ℝ} {f₂ g₂ : ∀ l, U₂ l → Ω → ℝ} {f₃ g₃ : ∀ l, U₃ l → Ω → ℝ}
    (h₁ : StochDomAt P size f₁ g₁) (h₂ : StochDomAt P size f₂ g₂) (h₃ : StochDomAt P size f₃ g₃)
    (hsub : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop,
      badSetAt size ξ ζ τ l ⊆ badSetAt size f₁ g₁ τ' l ∪ badSetAt size f₂ g₂ τ' l ∪ badSetAt size f₃ g₃ τ' l) :
    StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hs⟩ := hsub τ hτ
  filter_upwards [hs, h₁ τ' hτ' (D + 1) (by linarith), h₂ τ' hτ' (D + 1) (by linarith),
    h₃ τ' hτ' (D + 1) (by linarith), hsize.eventually (lwExpTerm4_three_mul_rpow_le D)] with l h0 h1 h2 h3 h4
  have hp : (0 : ℝ) ≤ (size l : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc P (badSetAt size ξ ζ τ l) ≤ P (badSetAt size f₁ g₁ τ' l ∪ badSetAt size f₂ g₂ τ' l ∪ badSetAt size f₃ g₃ τ' l) :=
        measure_mono h0
    _ ≤ P (badSetAt size f₁ g₁ τ' l ∪ badSetAt size f₂ g₂ τ' l) + P (badSetAt size f₃ g₃ τ' l) :=
        measure_union_le _ _
    _ ≤ P (badSetAt size f₁ g₁ τ' l) + P (badSetAt size f₂ g₂ τ' l) + P (badSetAt size f₃ g₃ τ' l) :=
        add_le_add (measure_union_le _ _) le_rfl
    _ ≤ ENNReal.ofReal ((size l : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((size l : ℝ) ^ (-(D + 1))) +
          ENNReal.ofReal ((size l : ℝ) ^ (-(D + 1))) := add_le_add (add_le_add h1 h2) h3
    _ = ENNReal.ofReal (3 * (size l : ℝ) ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add hp hp, ← ENNReal.ofReal_add (add_nonneg hp hp) hp]; ring_nf
    _ ≤ ENNReal.ofReal ((size l : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal h4

/-- `B^{5/2} = B² √B`. -/
private theorem lwExpTerm4_rpow52 {B : ℝ} (hB : 0 < B) : B ^ (5 / 2 : ℝ) = B ^ 2 * Real.sqrt B := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hB]
  norm_num

/-- `∫ c₀ Σ_{a₁a₂a₃} c f = c₀ Σ c ∫ f` for integrable `f` (copy of `lwExpTerm_int_sum3`, `LWExpTerm.lean:864`). -/
private theorem lwExpTerm4_int_sum3 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ι : Type*} [Fintype ι]
    (c₀ : ℂ) (c : ι → ι → ι → ℂ)
    (f : ι → ι → ι → Ω → ℂ) (hf : ∀ a₁ a₂ a₃, Integrable (f a₁ a₂ a₃) P) :
    ∫ ω, c₀ * ∑ a₁, ∑ a₂, ∑ a₃, c a₁ a₂ a₃ * f a₁ a₂ a₃ ω ∂P =
      c₀ * ∑ a₁, ∑ a₂, ∑ a₃, c a₁ a₂ a₃ * ∫ ω, f a₁ a₂ a₃ ω ∂P := by
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum _ (fun a₁ _ => integrable_finsetSum _ fun a₂ _ =>
    integrable_finsetSum _ fun a₃ _ => (hf a₁ a₂ a₃).const_mul _)]
  refine Finset.sum_congr rfl fun a₁ _ => ?_
  rw [integral_finsetSum _ (fun a₂ _ => integrable_finsetSum _ fun a₃ _ => (hf a₁ a₂ a₃).const_mul _)]
  refine Finset.sum_congr rfl fun a₂ _ => ?_
  rw [integral_finsetSum _ (fun a₃ _ => (hf a₁ a₂ a₃).const_mul _)]
  refine Finset.sum_congr rfl fun a₃ _ => ?_
  rw [integral_const_mul]

section I23

variable {d : ℕ} (sz : Sizes d)

/-- The random variable of `I₂` (`sel = true`), `I₃` (`sel = false`) under the integral. -/
private def lwExpTerm4_R23 (n : ℕ) (K : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) (E t : ℝ) (sel σ : Bool)
    (ac ao : Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃, K a₁ a₂ * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
    ((Lloop sz n E t ![true] ![a₁] ω - mSigma E true) *
      (Lloop sz n E t ![true] ![if sel then a₃ else a₂] ω - mSigma E true) *
      Lloop sz n E t ![true, true, σ] ![if sel then a₂ else a₃, ac, ao] ω)

private theorem lwExpTerm4_int_R23 (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht : t < 1)
    (K : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) (sel σ : Bool) (ac ao : Zd d (sz.L n)) :
    (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃, K a₁ a₂ * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
      ∫ ω, (Lloop sz n E t ![true] ![a₁] ω - mSigma E true) *
        (Lloop sz n E t ![true] ![if sel then a₃ else a₂] ω - mSigma E true) *
        Lloop sz n E t ![true, true, σ] ![if sel then a₂ else a₃, ac, ao] ω ∂(sz.seqP) =
      ∫ ω, lwExpTerm4_R23 sz n K E t sel σ ac ao ω ∂(sz.seqP) := by
  have hint : ∀ a₁ a₂ a₃ : Zd d (sz.L n), Integrable (fun ω => (Lloop sz n E t ![true] ![a₁] ω - mSigma E true) *
        (Lloop sz n E t ![true] ![if sel then a₃ else a₂] ω - mSigma E true) *
        Lloop sz n E t ![true, true, σ] ![if sel then a₂ else a₃, ac, ao] ω) (sz.seqP) := fun a₁ a₂ a₃ =>
    lwExpTerm2_BM_integrable (lwExpTerm2_BM_mul (lwExpTerm2_BM_mul (lwExpTerm2_BM_X sz n hE ht true a₁)
      (lwExpTerm2_BM_X sz n hE ht true _)) (lwExpTerm2_BM_Lloop sz n hE ht (k := 2) _ _))
  exact (lwExpTerm4_int_sum3 (P := sz.seqP) (((sz.W n : ℕ) : ℂ) ^ d)
    (fun a₁ a₂ a₃ => K a₁ a₂ * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ))
    (fun a₁ a₂ a₃ ω => (Lloop sz n E t ![true] ![a₁] ω - mSigma E true) *
        (Lloop sz n E t ![true] ![if sel then a₃ else a₂] ω - mSigma E true) *
        Lloop sz n E t ![true, true, σ] ![if sel then a₂ else a₃, ac, ao] ω) hint).symm

/-- **The deterministic bound of `R`** (`B:43-49`): `‖R‖ ≤ C M² · η⁻¹ A √(max 𝓛^{(2)})` for `M ≥ max_a |X_a|`,
`A ≥ max_x |G_{xx}|`: `lwExpTerm4_T23_n` and the 3-loop sum `lwExpTerm4_L3`. -/
private theorem lwExpTerm4_R23_le (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht : t < 1)
    (K : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) {C : ℝ} (hC : ∀ b, ∑ a, ‖K a b‖ ≤ C) (sel σ : Bool)
    (ac ao : Zd d (sz.L n)) (ω : sz.SeqΩ) {M A : ℝ}
    (hM : ∀ a, ‖Lloop sz n E t ![true] ![a] ω - mSigma E true‖ ≤ M)
    (hA : ∀ x : Idx d (sz.L n) (sz.W n), ‖Gt sz n E t true ω x x‖ ≤ A) :
    ‖lwExpTerm4_R23 sz n K E t sel σ ac ao ω‖ ≤
      C * (M * M) * ((etaT E t)⁻¹ * A * Real.sqrt (STmaxLoop2 sz n E t ω)) := by
  have hC0 : 0 ≤ C := (Finset.sum_nonneg fun a _ => norm_nonneg (K a 0)).trans (hC 0)
  have h1 := lwExpTerm4_T23_n sz n K hC sel
    (fun a => Lloop sz n E t ![true] ![a] ω - mSigma E true)
    (fun a => Lloop sz n E t ![true] ![a] ω - mSigma E true)
    (fun a => Lloop sz n E t ![true, true, σ] ![a, ac, ao] ω) (c := M * M)
    (fun a₁ a' => mul_le_mul (hM a₁) (hM a') (norm_nonneg _) ((norm_nonneg _).trans (hM a₁)))
  have h2 := lwExpTerm4_L3 d sz n E t hE ht σ ac ao ω A hA
  refine h1.trans ?_
  have hM0 : 0 ≤ M * M := mul_self_nonneg M
  calc C * (M * M) * ((((sz.W n : ℕ) : ℝ) ^ d) * ∑ a, ‖Lloop sz n E t ![true, true, σ] ![a, ac, ao] ω‖)
      ≤ C * (M * M) * ((etaT E t)⁻¹ * A * Real.sqrt (STmaxLoop2 sz n E t ω)) :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg hC0 hM0)

end I23


section I23prec

variable {d : ℕ} (sz : Sizes d)

/-- **`‖R‖ ≺ η⁻¹ B^{5/2}`** (`B:43-49`): on the complement of the failure events of `STLK` (`k = 1`: `|X_a| ≤ N^{τ/5}B`),
target 4 (`|G_{xx}| ≤ N^{τ/5}`) and `STLmax` (`k = 2`: `max 𝓛^{(2)} ≤ N^{τ/5}B`), `lwExpTerm4_R23_le` gives
`‖R‖ ≤ C (N^{τ/5}B)² η⁻¹ N^{τ/5} (N^{τ/5}B)^{1/2} ≤ N^τ η⁻¹ B² B^{1/2}` (exponent `2 + 1/2 = 5/2`). -/
private theorem lwExpTerm4_R23_prec (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    {z : ℕ → ℂ} (hz : STFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n) (htz : ∀ n, t n ≤ lemT (z n))
    (K : ∀ n, Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) {C : ℝ} (hC : ∀ n b, ∑ a, ‖K n a b‖ ≤ C)
    (hLE : STLocalEntry sz (STflowE z) t) (hLmax : STLmax sz (STflowE z) t) (hLK : STLK sz (STflowE z) t) :
    sz.Prec (U := fun n => (Bool × Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n v ω => ‖lwExpTerm4_R23 sz n (K n) (STflowE z n) (t n) v.1.1 v.1.2 (v.2 0) (v.2 1) ω‖)
      (fun n _ _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) := by
  have hsz : sz.SizeTendsto := hz.1.2.2.1
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hz htz
  have hE2 : ∀ n, |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hz
  have hC0 : 0 ≤ C := (Finset.sum_nonneg fun a _ => norm_nonneg (K 0 a 0)).trans (hC 0 0)
  have hX : StochDomAt sz.seqP sz.size (U := fun n => Zd d (sz.L n))
      (fun n a ω => ‖Lloop sz n (STflowE z n) (t n) ![true] ![a] ω - mSigma (STflowE z n) true‖)
      (fun n _ _ => sz.Bctl n (t n)) := by
    have h := StochDomAt.precomp_param (hLK 1 le_rfl)
      (fun n (a : Zd d (sz.L n)) => ((![true], ![a]) : (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n))))
    refine lwExpTerm4_prec_congr (fun n a ω => ?_) (fun n a ω => ?_) h
    · simp only [lwExpTerm4_Kloop_one]
    · simp
  have hG := lwExpTerm4_diag d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz t ht0 htz hLE
  have hS := hLmax 2 (by norm_num)
  unfold Prec at hG hS ⊢
  refine lwExpTerm4_prec_union3 (tendsto_size sz hsz) hX hG hS ?_
  intro τ hτ
  have hτ5 : 0 < τ / 5 := by positivity
  refine ⟨τ / 5, hτ5, ?_⟩
  filter_upwards [((tendsto_rpow_atTop hτ5).comp hsz).eventually (eventually_ge_atTop (C + 1))] with n hu
  intro ω hω
  obtain ⟨v, hv⟩ := hω
  by_contra hno
  simp only [Set.mem_union, badSetAt, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hno
  obtain ⟨⟨h1, h2⟩, h3⟩ := hno
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := Nat.cast_pos.mpr (by have := sz.one_le_size n; omega)
  set B : ℝ := sz.Bctl n (t n) with hBdef
  have hB : 0 < B := STBctl_pos sz n (ht1 n)
  set e : ℝ := (etaT (STflowE z n) (t n))⁻¹ with hedef
  have he : 0 ≤ e := (inv_pos.2 (etaT_pos (hE2 n) (ht1 n))).le
  have hu' : C + 1 ≤ N ^ (τ / 5) := hu
  set u : ℝ := N ^ (τ / 5) with hudef
  have hu1 : 1 ≤ u := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hSmax : STmaxLoop2 sz n (STflowE z n) (t n) ω ≤ u * B := by
    refine Finset.sup'_le _ _ fun p _ => ?_
    simpa using h3 (![false, true], ![p.1, p.2])
  obtain ⟨⟨sel, σ⟩, ab⟩ := v
  have hR := lwExpTerm4_R23_le sz n (hE2 n) (ht1 n) (K n) (hC n) sel σ (ab 0) (ab 1) ω (M := u * B) (A := u * 1)
    h1 h2
  have hsq : Real.sqrt (u * B) ≤ u * Real.sqrt B := by
    rw [Real.sqrt_mul hu0]
    refine mul_le_mul_of_nonneg_right (Real.sqrt_le_iff.2 ⟨hu0, by nlinarith⟩) (Real.sqrt_nonneg _)
  have hsqS : Real.sqrt (STmaxLoop2 sz n (STflowE z n) (t n) ω) ≤ u * Real.sqrt B :=
    (Real.sqrt_le_sqrt hSmax).trans hsq
  have hCu : C ≤ u := by linarith
  have hfin : ‖lwExpTerm4_R23 sz n (K n) (STflowE z n) (t n) sel σ (ab 0) (ab 1) ω‖ ≤
      u ^ 5 * (e * (B ^ 2 * Real.sqrt B)) := by
    refine hR.trans ?_
    have hsB : 0 ≤ Real.sqrt B := Real.sqrt_nonneg _
    calc C * ((u * B) * (u * B)) * (e * (u * 1) * Real.sqrt (STmaxLoop2 sz n (STflowE z n) (t n) ω))
        ≤ u * ((u * B) * (u * B)) * (e * (u * 1) * (u * Real.sqrt B)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right hCu (by positivity)) ?_ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hsqS (by positivity)
      _ = _ := by ring
  have hNτ : N ^ τ = u ^ 5 := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; congr 1; push_cast; ring
  have hv' : N ^ τ * (e * B ^ (5 / 2 : ℝ)) < ‖lwExpTerm4_R23 sz n (K n) (STflowE z n) (t n) sel σ (ab 0) (ab 1) ω‖ := hv
  rw [hNτ, lwExpTerm4_rpow52 hB] at hv'
  exact absurd hfin (not_le.2 hv')

end I23prec


/-- `η_t ≤ 1` for `0 ≤ t < 1`, `|E| < 2` (copy of `lwExpTerm_eta_le_one`, `LWExpTerm.lean:996`, private there). -/
private theorem lwExpTerm4_eta_le_one {E t : ℝ} (hE : |E| < 2) (ht0 : 0 ≤ t) :
    etaT E t ≤ 1 := by
  have h1 : (mE E).im ≤ 1 := by
    have := Complex.im_le_norm (mE E)
    rwa [norm_mE hE.le] at this
  unfold etaT
  have him : 0 ≤ (mE E).im := (mE_im_pos hE).le
  nlinarith

/-- **Target 7** (`lwExpI23K_holds`): `I₂ + J₂` (`sel = true`) and `I₃ + J₃` (`sel = false`), `≺ η⁻¹ B^{5/2}`, for every
decaying first kernel `K`, both charges `σ_o`.  `∫` is moved through the sums (`lwExpTerm4_int_R23`),
`‖R‖ ≺ η⁻¹ B^{5/2}` is `lwExpTerm4_R23_prec` (the bound `lwExpTerm4_R23_le` on the good event of `STLK` (`k = 1`),
target 4 (`STLocalEntry`) and `STLmax` (`k = 2`)), then `≺ → 𝔼` (`lwExpTerm_prec_integral`) with the envelope
`‖R‖ ≤ 4C N⁶ ≤ N⁷` and the floor `η⁻¹ B^{5/2} ≥ N^{-5/2}`. -/
theorem lwExpI23K_holds (d : ℕ) : LWExpI23K d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz t ht0 htz K hK hLE hLW hLmax hLK hDec
  have hsz : sz.SizeTendsto := hz.1.2.2.1
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hz htz
  have hE2 : ∀ n, |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hz
  obtain ⟨C, hC0, hCsum⟩ := lwExpTerm4_kerSum d sz K hK
  have hC : ∀ n b, ∑ a, ‖K n a b‖ ≤ C := fun n b => (hCsum n b).1
  have hfac := lwExpTerm4_facts sz hd hκ hε hz ht0 htz
  have hprec := lwExpTerm4_R23_prec sz hd hκ hε h𝔡 hz ht0 htz K hC hLE hLmax hLK
  have hint := lwExpTerm_prec_integral sz (V := fun n => (Bool × Bool) × (Fin 2 → Zd d (sz.L n)))
    (fun n v ω => lwExpTerm4_R23 sz n (K n) (STflowE z n) (t n) v.1.1 v.1.2 (v.2 0) (v.2 1) ω)
    (fun n _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) (Kenv := 7) (Kf := 5 / 2) hsz
    ?_ ?_ hprec
  · refine lwExpTerm4_prec_congr (fun n p ω => ?_) (fun n p ω => rfl) hint
    obtain ⟨⟨sel, σ⟩, ab⟩ := p
    exact (congrArg norm (lwExpTerm4_int_R23 sz n (hE2 n) (ht1 n) (K n) sel σ (ab 0) (ab 1))).symm
  · -- the envelope
    filter_upwards [hfac, hsz.eventually (eventually_ge_atTop (4 * C))] with n hn hN4C
    obtain ⟨hη, hB1, hBN, hN4, hK2⟩ := hn
    intro v ω
    obtain ⟨⟨sel, σ⟩, ab⟩ := v
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
    have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
    have hη0 : 0 ≤ (etaT (STflowE z n) (t n))⁻¹ := (inv_pos.2 (etaT_pos (hE2 n) (ht1 n))).le
    have hX1 : ∀ a : Zd d (sz.L n),
        ‖Lloop sz n (STflowE z n) (t n) ![true] ![a] ω - mSigma (STflowE z n) true‖ ≤ 2 * N :=
      fun a => lwExpTerm4_env_X sz n (hE2 n) (ht1 n) hη hN1 true a ω
    have hT := lwExpTerm4_T23_n sz n (K n) (hC n) sel
      (fun a => Lloop sz n (STflowE z n) (t n) ![true] ![a] ω - mSigma (STflowE z n) true)
      (fun a => Lloop sz n (STflowE z n) (t n) ![true] ![a] ω - mSigma (STflowE z n) true)
      (fun a => Lloop sz n (STflowE z n) (t n) ![true, true, σ] ![a, ab 0, ab 1] ω) (c := (2 * N) * (2 * N))
      (fun a₁ a' => mul_le_mul (hX1 a₁) (hX1 a') (norm_nonneg _) (by positivity))
    have hL3 : ∀ a : Zd d (sz.L n),
        ‖Lloop sz n (STflowE z n) (t n) ![true, true, σ] ![a, ab 0, ab 1] ω‖ ≤ N ^ 3 := fun a =>
      (norm_Lloop_le sz n (hE2 n) (ht1 n) (k := 2) ![true, true, σ] ![a, ab 0, ab 1] ω).trans
        (pow_le_pow_left₀ hη0 hη 3)
    have hcard : (((sz.W n : ℕ) : ℝ) ^ d) * ∑ a : Zd d (sz.L n),
        ‖Lloop sz n (STflowE z n) (t n) ![true, true, σ] ![a, ab 0, ab 1] ω‖ ≤ N * N ^ 3 := by
      have h1 : ∑ a : Zd d (sz.L n), ‖Lloop sz n (STflowE z n) (t n) ![true, true, σ] ![a, ab 0, ab 1] ω‖ ≤
          (((sz.L n : ℕ) : ℝ) ^ d) * N ^ 3 := by
        calc _ ≤ ∑ _a : Zd d (sz.L n), N ^ 3 := Finset.sum_le_sum fun a _ => hL3 a
          _ = (((sz.L n : ℕ) : ℝ) ^ d) * N ^ 3 := by
              rw [Finset.sum_const, nsmul_eq_mul]
              congr 1
              simp [Zd, ZMod.card]
      have hNW : N = (((sz.W n : ℕ) : ℝ) ^ d) * (((sz.L n : ℕ) : ℝ) ^ d) := by
        rw [hNdef]
        simp [Sizes.size, mul_pow]
      calc _ ≤ (((sz.W n : ℕ) : ℝ) ^ d) * ((((sz.L n : ℕ) : ℝ) ^ d) * N ^ 3) :=
            mul_le_mul_of_nonneg_left h1 (lwExpTerm4_Wd_pos sz n).le
        _ = N * N ^ 3 := by rw [← mul_assoc, ← hNW]
    have hC0' : 0 ≤ C := hC0.le
    have h7 : N ^ (7 : ℝ) = N ^ 7 := by rw [← Real.rpow_natCast]; norm_num
    change ‖lwExpTerm4_R23 sz n (K n) (STflowE z n) (t n) sel σ (ab 0) (ab 1) ω‖ ≤ N ^ (7 : ℝ)
    rw [h7]
    calc _ ≤ C * ((2 * N) * (2 * N)) * (((sz.W n : ℕ) : ℝ) ^ d * ∑ a : Zd d (sz.L n),
          ‖Lloop sz n (STflowE z n) (t n) ![true, true, σ] ![a, ab 0, ab 1] ω‖) := hT
      _ ≤ C * ((2 * N) * (2 * N)) * (N * N ^ 3) := mul_le_mul_of_nonneg_left hcard (by positivity)
      _ = (4 * C) * N ^ 6 := by ring
      _ ≤ N * N ^ 6 := mul_le_mul_of_nonneg_right hN4C (by positivity)
      _ = N ^ 7 := by ring
  · -- the floor
    filter_upwards [hfac] with n hn
    obtain ⟨hη, hB1, hBN, hN4, hK2⟩ := hn
    intro v
    have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have h1 : 1 ≤ (etaT (STflowE z n) (t n))⁻¹ :=
      (one_le_inv₀ (etaT_pos (hE2 n) (ht1 n))).2 (lwExpTerm4_eta_le_one (hE2 n) (ht0 n))
    have h2 : ((sz.size n : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) ≤ (sz.Bctl n (t n)) ^ (5 / 2 : ℝ) := by
      rw [Real.rpow_neg hNpos.le, ← Real.inv_rpow hNpos.le]
      exact Real.rpow_le_rpow (inv_nonneg.2 hNpos.le) hBN (by norm_num)
    have hB52 : 0 ≤ (sz.Bctl n (t n)) ^ (5 / 2 : ℝ) := Real.rpow_nonneg (STBctl_pos sz n (ht1 n)).le _
    calc _ ≤ (sz.Bctl n (t n)) ^ (5 / 2 : ℝ) := h2
      _ = 1 * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 hB52


/-! ## 9. Target 8: `lwExpI41K_holds` (`(eq:termI41)`, `B:57-70`), both charges `s` -/

section Split4

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- `𝔼[X A A'] = 𝔼[X A (A' - K')] + (𝔼 X) K K' + 𝔼[X (A - K)] K'` (`A = K + (A - K)`, `A' = K' + (A' - K')`). -/
private theorem lwExpTerm4_int_split3 {X A A' : Ω → ℂ} (K K' : ℂ) (hX : lwExpTerm2_BM X)
    (hA : lwExpTerm2_BM A) (hA' : lwExpTerm2_BM A') :
    ∫ ω, X ω * A ω * A' ω ∂P = ∫ ω, X ω * A ω * (A' ω - K') ∂P + (∫ ω, X ω ∂P) * K * K' +
      (∫ ω, X ω * (A ω - K) ∂P) * K' := by
  have h1 : lwExpTerm2_BM (fun ω => X ω * A ω * (A' ω - K')) :=
    lwExpTerm2_BM_mul (lwExpTerm2_BM_mul hX hA) (lwExpTerm2_BM_sub hA' (lwExpTerm2_BM_const _))
  have h2 : lwExpTerm2_BM (fun ω => X ω * K * K') :=
    lwExpTerm2_BM_mul (lwExpTerm2_BM_mul hX (lwExpTerm2_BM_const _)) (lwExpTerm2_BM_const _)
  have h3 : lwExpTerm2_BM (fun ω => X ω * (A ω - K) * K') :=
    lwExpTerm2_BM_mul (lwExpTerm2_BM_mul hX (lwExpTerm2_BM_sub hA (lwExpTerm2_BM_const _)))
      (lwExpTerm2_BM_const _)
  have hpt : ∀ ω, X ω * A ω * A' ω =
      X ω * A ω * (A' ω - K') + X ω * K * K' + X ω * (A ω - K) * K' := fun ω => by ring
  simp_rw [hpt]
  rw [integral_add (lwExpTerm2_BM_integrable (lwExpTerm2_BM_add h1 h2)) (lwExpTerm2_BM_integrable h3),
    integral_add (lwExpTerm2_BM_integrable h1) (lwExpTerm2_BM_integrable h2), integral_mul_const,
    integral_mul_const, integral_mul_const]


/-- **The `I₄₁K` split** (`B:66-72`): `W^d Σ (K S) 𝔼[X A A'] = 𝔼[W^d Σ (K S) X A (A' - K')]
+ W^d Σ (K S) ((𝔼 X) K) K' + W^d Σ (K S) (𝔼[X (A - K)]) K'` (the kernels `K_{a₁a₂}`, `S_{a₂a₃}`). -/
private theorem lwExpTerm4_I41K_split {ι : Type*} [Fintype ι] (c₀ : ℂ) (Kk S : ι → ι → ℂ)
    (X A A' : ι → Ω → ℂ) (K K' : ι → ℂ) (hX : ∀ i, lwExpTerm2_BM (X i)) (hA : ∀ i, lwExpTerm2_BM (A i))
    (hA' : ∀ i, lwExpTerm2_BM (A' i)) :
    c₀ * ∑ a₁, ∑ a₂, ∑ a₃, Kk a₁ a₂ * S a₂ a₃ * ∫ ω, X a₁ ω * A a₂ ω * A' a₃ ω ∂P =
      (∫ ω, c₀ * ∑ a₁, ∑ a₂, ∑ a₃, Kk a₁ a₂ * S a₂ a₃ * (X a₁ ω * A a₂ ω * (A' a₃ ω - K' a₃)) ∂P) +
        c₀ * ∑ a₁, ∑ a₂, ∑ a₃, Kk a₁ a₂ * S a₂ a₃ * (((∫ ω, X a₁ ω ∂P) * K a₂) * K' a₃) +
        c₀ * ∑ a₁, ∑ a₂, ∑ a₃, Kk a₁ a₂ * S a₂ a₃ * ((∫ ω, X a₁ ω * (A a₂ ω - K a₂) ∂P) * K' a₃) := by
  have hint : ∀ a₁ a₂ a₃, Integrable (fun ω => X a₁ ω * A a₂ ω * (A' a₃ ω - K' a₃)) P := fun a₁ a₂ a₃ =>
    lwExpTerm2_BM_integrable (lwExpTerm2_BM_mul (lwExpTerm2_BM_mul (hX a₁) (hA a₂))
      (lwExpTerm2_BM_sub (hA' a₃) (lwExpTerm2_BM_const _)))
  rw [lwExpTerm4_int_sum3 c₀ (fun a₁ a₂ a₃ => Kk a₁ a₂ * S a₂ a₃)
    (fun a₁ a₂ a₃ ω => X a₁ ω * A a₂ ω * (A' a₃ ω - K' a₃)) hint]
  have e : ∀ a₁ a₂ a₃, (∫ ω, X a₁ ω * A a₂ ω * A' a₃ ω ∂P) =
      (∫ ω, X a₁ ω * A a₂ ω * (A' a₃ ω - K' a₃) ∂P) + ((∫ ω, X a₁ ω ∂P) * K a₂) * K' a₃ +
        (∫ ω, X a₁ ω * (A a₂ ω - K a₂) ∂P) * K' a₃ := fun a₁ a₂ a₃ =>
    lwExpTerm4_int_split3 (K a₂) (K' a₃) (hX a₁) (hA a₂) (hA' a₃)
  simp_rw [e, mul_add, Finset.sum_add_distrib]
  ring

end Split4


section Ta4

variable {d : ℕ} (sz : Sizes d)

/-- `R_a = W^d Σ K_{a₁a₂} S_{a₂a₃} X_{a₁} 𝓛^{(2)}_{(s,+),(a,a₂)} (𝓛 - 𝒦)^{(2)}_{(s,+),(a₃,b)}`, `((σ₁, s), (a, b))` the index. -/
private def lwExpTerm4_Ra (n : ℕ) (K : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) (E t : ℝ) (σ₁ s : Bool)
    (ab : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃, K a₁ a₂ * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
    ((Lloop sz n E t ![σ₁] ![a₁] ω - mSigma E σ₁) * Lloop sz n E t ![s, true] ![ab 0, a₂] ω *
      (Lloop sz n E t ![s, true] ![a₃, ab 1] ω - STKloop sz n E t ![s, true] ![a₃, ab 1]))

/-- `‖R_a‖ ≺ η_t⁻¹ B³` as a random variable: on the complement of the failure events of `STLK` (`k = 1, 2`) and
`STLmax` (`k = 1`), `‖X_{a₁}‖ ‖D'_{a₃}‖ ≤ N^{τ/3} B³`, `‖𝓛^{(1)}_{+,a}‖ ≤ N^{τ/3}`, and `Ta_n` with the Ward bound
`lwExpTerm4_ward2` (charge `s`) give `‖R_a‖ ≤ C N^{2τ/3} η⁻¹ B³ ≤ N^τ η⁻¹ B³`. -/
private theorem lwExpTerm4_Ra_prec {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ}
    (hz : STFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (htz : ∀ n, t n ≤ lemT (z n))
    (K : ∀ n, Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) {C : ℝ} (hC : ∀ n b, ∑ a, ‖K n a b‖ ≤ C)
    (hLmax : STLmax sz (STflowE z) t) (hLK : STLK sz (STflowE z) t) :
    sz.Prec (U := fun n => (Bool × Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n v ω => ‖lwExpTerm4_Ra sz n (K n) (STflowE z n) (t n) v.1.1 v.1.2 v.2 ω‖)
      (fun n _ _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ 3) := by
  have hsz : sz.SizeTendsto := hz.1.2.2.1
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hz htz
  have hE2 : ∀ n, |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hz
  have hB0 : ∀ n, 0 < sz.Bctl n (t n) := fun n => STBctl_pos sz n (ht1 n)
  have hC0 : 0 ≤ C := (Finset.sum_nonneg fun a _ => norm_nonneg (K 0 a 0)).trans (hC 0 0)
  have h₁ := StochDomAt.precomp_param (hLK 1 le_rfl)
    (fun n (p : (Bool × Bool) × (Fin 2 → Zd d (sz.L n)) × Zd d (sz.L n) × Zd d (sz.L n)) =>
      ((![p.1.1], ![p.2.2.1]) : (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n))))
  have h₂ := StochDomAt.precomp_param (hLK 2 (by norm_num))
    (fun n (p : (Bool × Bool) × (Fin 2 → Zd d (sz.L n)) × Zd d (sz.L n) × Zd d (sz.L n)) =>
      ((![p.1.2, true], ![p.2.2.2, p.2.1 1]) : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))))
  have hm := StochDomAt.mul (P := sz.seqP) (size := sz.size) (tendsto_size sz hsz)
    (fun n p ω => norm_nonneg _) (fun n p ω => pow_nonneg (hB0 n).le _) h₁ h₂
  have hF1 : StochDomAt sz.seqP sz.size
      (U := fun n => (Bool × Bool) × (Fin 2 → Zd d (sz.L n)) × Zd d (sz.L n) × Zd d (sz.L n))
      (fun n p ω => ‖Lloop sz n (STflowE z n) (t n) ![p.1.1] ![p.2.2.1] ω - mSigma (STflowE z n) p.1.1‖ *
        ‖Lloop sz n (STflowE z n) (t n) ![p.1.2, true] ![p.2.2.2, p.2.1 1] ω -
          STKloop sz n (STflowE z n) (t n) ![p.1.2, true] ![p.2.2.2, p.2.1 1]‖)
      (fun n _ _ => (sz.Bctl n (t n)) ^ 3) := by
    refine lwExpTerm4_prec_congr (fun n p ω => ?_) (fun n p ω => ?_) hm
    · simp only [Pi.mul_apply, lwExpTerm4_Kloop_one]
    · simp only [Pi.mul_apply]; ring
  have hF2 : StochDomAt sz.seqP sz.size (U := fun n => (Bool × Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n v ω => ‖Lloop sz n (STflowE z n) (t n) ![true] ![v.2 0] ω‖) (fun n _ _ => (1 : ℝ)) := by
    have := StochDomAt.precomp_param (hLmax 1 le_rfl)
      (fun n (p : (Bool × Bool) × (Fin 2 → Zd d (sz.L n))) =>
        ((![true], ![p.2 0]) : (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n))))
    refine lwExpTerm4_prec_congr (fun n p ω => rfl) (fun n p ω => ?_) this
    simp
  refine StochDomAt.of_subset_union (tendsto_size sz hsz) hF1 hF2 ?_
  intro τ hτ
  have hτ3 : 0 < τ / 3 := by positivity
  refine ⟨τ / 3, hτ3, ?_⟩
  filter_upwards [((tendsto_rpow_atTop hτ3).comp hsz).eventually (eventually_ge_atTop C)] with n hu ω hω
  by_contra hno
  simp only [Set.mem_union, badSetAt, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hno
  obtain ⟨v, hv⟩ := hω
  obtain ⟨h1, h2⟩ := hno
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := Nat.cast_pos.mpr (by have := sz.one_le_size n; omega)
  set B : ℝ := sz.Bctl n (t n) with hBdef
  have hB : 0 < B := hB0 n
  set η : ℝ := (etaT (STflowE z n) (t n))⁻¹ with hηdef
  have hη0 : 0 ≤ η := (inv_pos.2 (etaT_pos (hE2 n) (ht1 n))).le
  have hu' : C ≤ N ^ (τ / 3) := hu
  set u : ℝ := N ^ (τ / 3) with hudef
  have hu0 : 0 ≤ u := Real.rpow_nonneg hNpos.le _
  obtain ⟨⟨σ₁, s⟩, ab⟩ := v
  have hc : ∀ a₁ a₃ : Zd d (sz.L n),
      ‖Lloop sz n (STflowE z n) (t n) ![σ₁] ![a₁] ω - mSigma (STflowE z n) σ₁‖ *
        ‖Lloop sz n (STflowE z n) (t n) ![s, true] ![a₃, ab 1] ω -
          STKloop sz n (STflowE z n) (t n) ![s, true] ![a₃, ab 1]‖ ≤ u * B ^ 3 :=
    fun a₁ a₃ => h1 ((σ₁, s), ab, a₁, a₃)
  have hΛ : ‖Lloop sz n (STflowE z n) (t n) ![true] ![ab 0] ω‖ ≤ u := by
    have := h2 ((σ₁, s), ab); simpa using this
  have hTa := lwExpTerm4_Ta_n sz n (K n) (hC n)
    (fun a₁ => Lloop sz n (STflowE z n) (t n) ![σ₁] ![a₁] ω - mSigma (STflowE z n) σ₁)
    (fun a₂ => Lloop sz n (STflowE z n) (t n) ![s, true] ![ab 0, a₂] ω)
    (fun a₃ => Lloop sz n (STflowE z n) (t n) ![s, true] ![a₃, ab 1] ω -
      STKloop sz n (STflowE z n) (t n) ![s, true] ![a₃, ab 1]) hc
  have hW := lwExpTerm4_ward2 d sz n (STflowE z n) (t n) (hE2 n) (ht1 n) s (ab 0) ω
  have hWd : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hfin : ‖lwExpTerm4_Ra sz n (K n) (STflowE z n) (t n) σ₁ s ab ω‖ ≤ C * (u * B ^ 3) * (η * u) := by
    refine hTa.trans (mul_le_mul_of_nonneg_left (hW.trans ?_) (by positivity))
    exact mul_le_mul_of_nonneg_left hΛ hη0
  have hNτ : N ^ τ = u ^ 3 := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; congr 1; push_cast; ring
  have hle : C * (u * B ^ 3) * (η * u) ≤ u ^ 3 * (η * B ^ 3) := by
    have h3 : 0 ≤ (u - C) * (u ^ 2 * (η * B ^ 3)) := mul_nonneg (by linarith) (by positivity)
    nlinarith [h3]
  have hv' : N ^ τ * (η * B ^ 3) < ‖lwExpTerm4_Ra sz n (K n) (STflowE z n) (t n) σ₁ s ab ω‖ := hv
  rw [hNτ] at hv'
  exact absurd (hfin.trans hle) (not_le.2 hv')


/-- **`𝔼 R_a ≺ η_t⁻¹ B³`** (deterministic): `lwExpTerm4_Ra_prec` then `≺ → 𝔼` with the envelope
`‖R_a‖ ≤ 4C N³ · η⁻¹‖𝓛^{(1)}‖ ≤ 4C N⁵ ≤ N⁶` (`Ta_n`, `lwExpTerm4_ward2`) and the floor `η⁻¹ B³ ≥ N⁻³`. -/
private theorem lwExpTerm4_Ta_det (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) {z : ℕ → ℂ}
    (hz : STFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n) (htz : ∀ n, t n ≤ lemT (z n))
    (K : ∀ n, Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) {C : ℝ} (hC : ∀ n b, ∑ a, ‖K n a b‖ ≤ C)
    (hLmax : STLmax sz (STflowE z) t) (hLK : STLK sz (STflowE z) t) :
    sz.Prec (U := fun n => (Bool × Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n v _ => ‖∫ ω, lwExpTerm4_Ra sz n (K n) (STflowE z n) (t n) v.1.1 v.1.2 v.2 ω ∂(sz.seqP)‖)
      (fun n _ _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ 3) := by
  have hsz : sz.SizeTendsto := hz.1.2.2.1
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hz htz
  have hE2 : ∀ n, |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hz
  have hfac := lwExpTerm4_facts sz hd hκ hε hz ht0 htz
  have hC0 : 0 ≤ C := (Finset.sum_nonneg fun a _ => norm_nonneg (K 0 a 0)).trans (hC 0 0)
  refine lwExpTerm_prec_integral sz (V := fun n => (Bool × Bool) × (Fin 2 → Zd d (sz.L n)))
    (fun n v ω => lwExpTerm4_Ra sz n (K n) (STflowE z n) (t n) v.1.1 v.1.2 v.2 ω)
    (fun n _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ 3) (Kenv := 6) (Kf := 3) hsz ?_ ?_
    (lwExpTerm4_Ra_prec sz hκ hz htz K hC hLmax hLK)
  · filter_upwards [hfac, hsz.eventually (eventually_ge_atTop (4 * C))] with n hn hN4C
    obtain ⟨hη, hB1, hBN, hN4, hK⟩ := hn
    intro v ω
    obtain ⟨⟨σ₁, s⟩, ab⟩ := v
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
    have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
    have hη0 : 0 ≤ (etaT (STflowE z n) (t n))⁻¹ := (inv_pos.2 (etaT_pos (hE2 n) (ht1 n))).le
    have hX1 : ∀ a₁ : Zd d (sz.L n),
        ‖Lloop sz n (STflowE z n) (t n) ![σ₁] ![a₁] ω - mSigma (STflowE z n) σ₁‖ ≤ 2 * N :=
      fun a₁ => lwExpTerm4_env_X sz n (hE2 n) (ht1 n) hη hN1 σ₁ a₁ ω
    have hD1 : ∀ a₃ : Zd d (sz.L n),
        ‖Lloop sz n (STflowE z n) (t n) ![s, true] ![a₃, ab 1] ω -
          STKloop sz n (STflowE z n) (t n) ![s, true] ![a₃, ab 1]‖ ≤ 2 * N ^ 2 :=
      fun a₃ => lwExpTerm4_env_D sz n (hE2 n) (ht1 n) hη hN1 ![s, true] ![a₃, ab 1] (hK _ _) ω
    have hc : ∀ a₁ a₃ : Zd d (sz.L n),
        ‖Lloop sz n (STflowE z n) (t n) ![σ₁] ![a₁] ω - mSigma (STflowE z n) σ₁‖ *
          ‖Lloop sz n (STflowE z n) (t n) ![s, true] ![a₃, ab 1] ω -
            STKloop sz n (STflowE z n) (t n) ![s, true] ![a₃, ab 1]‖ ≤ (2 * N) * (2 * N ^ 2) :=
      fun a₁ a₃ => mul_le_mul (hX1 a₁) (hD1 a₃) (norm_nonneg _) (by positivity)
    have hTa := lwExpTerm4_Ta_n sz n (K n) (hC n)
      (fun a₁ => Lloop sz n (STflowE z n) (t n) ![σ₁] ![a₁] ω - mSigma (STflowE z n) σ₁)
      (fun a₂ => Lloop sz n (STflowE z n) (t n) ![s, true] ![ab 0, a₂] ω)
      (fun a₃ => Lloop sz n (STflowE z n) (t n) ![s, true] ![a₃, ab 1] ω -
        STKloop sz n (STflowE z n) (t n) ![s, true] ![a₃, ab 1]) hc
    have hW := lwExpTerm4_ward2 d sz n (STflowE z n) (t n) (hE2 n) (ht1 n) s (ab 0) ω
    have hL1 : ‖Lloop sz n (STflowE z n) (t n) ![true] ![ab 0] ω‖ ≤ N := by
      have h1 : ‖Lloop sz n (STflowE z n) (t n) ![true] ![ab 0] ω‖ ≤ (etaT (STflowE z n) (t n))⁻¹ ^ 1 :=
        norm_Lloop_le sz n (hE2 n) (ht1 n) (k := 0) ![true] ![ab 0] ω
      rw [pow_one] at h1
      exact h1.trans hη
    have hW2 : ((sz.W n : ℕ) : ℝ) ^ d * ∑ a₂, ‖Lloop sz n (STflowE z n) (t n) ![s, true] ![ab 0, a₂] ω‖ ≤
        N * N := hW.trans (mul_le_mul hη hL1 (norm_nonneg _) hNpos.le)
    have h6 : N ^ (6 : ℝ) = N ^ 6 := by rw [← Real.rpow_natCast]; norm_num
    change ‖lwExpTerm4_Ra sz n (K n) (STflowE z n) (t n) σ₁ s ab ω‖ ≤ N ^ (6 : ℝ)
    rw [h6]
    calc _ ≤ C * ((2 * N) * (2 * N ^ 2)) * (((sz.W n : ℕ) : ℝ) ^ d *
          ∑ a₂, ‖Lloop sz n (STflowE z n) (t n) ![s, true] ![ab 0, a₂] ω‖) := hTa
      _ ≤ C * ((2 * N) * (2 * N ^ 2)) * (N * N) := mul_le_mul_of_nonneg_left hW2 (by positivity)
      _ = (4 * C) * N ^ 5 := by ring
      _ ≤ N * N ^ 5 := mul_le_mul_of_nonneg_right hN4C (by positivity)
      _ = N ^ 6 := by ring
  · filter_upwards [hfac] with n hn
    obtain ⟨hη, hB1, hBN, hN4, hK⟩ := hn
    intro v
    have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have h1 : 1 ≤ (etaT (STflowE z n) (t n))⁻¹ :=
      (one_le_inv₀ (etaT_pos (hE2 n) (ht1 n))).2 (lwExpTerm4_eta_le_one (hE2 n) (ht0 n))
    have h3 := lwExpTerm4_floor3 hNpos hBN
    have hB3 : 0 ≤ (sz.Bctl n (t n)) ^ 3 := pow_nonneg (STBctl_pos sz n (ht1 n)).le _
    calc _ ≤ (sz.Bctl n (t n)) ^ 3 := h3
      _ = 1 * (sz.Bctl n (t n)) ^ 3 := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 hB3

end Ta4

/-- **Target 8** (`lwExpI41K_holds`): `I₄₁ + J₄₁ ≺ η⁻¹ B³` for every decaying first kernel `K` and both charges `s`
(`σ_o = ±`).  The route of `lwExpI41_holds` (`LWExpTerm.lean:1119`): `A' = 𝒦' + (A' - 𝒦')`, `T_a = 𝔼 R_a`
(`lwExpTerm4_Ta_det`: Ward `(s,+)` by target 2), `T_{b1}`, `T_{b2}` by `lwExpTerm4_Tb_n` with `STExpAvgAt`,
`STKbound`, `lwExpTerm4_XD` and the `𝒦`-Ward of target 3; the column sums of `K` are `≤ C` (target 1). -/
theorem lwExpI41K_holds (d : ℕ) : LWExpI41K d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz t ht0 htz K hK hLW hLmax hLK
  have hsz : sz.SizeTendsto := hz.1.2.2.1
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hz htz
  have hE2 : ∀ n, |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hz
  obtain ⟨C, hC0, hCsum⟩ := lwExpTerm4_kerSum d sz K hK
  have hC : ∀ n b, ∑ a, ‖K n a b‖ ≤ C := fun n b => (hCsum n b).1
  have hEX := (st6_prec_det_iff sz hsz _ _).1 (STExpAvgAt_of_LWAvgLaw sz hd hκ hε hz t ht0 htz hLW)
  have hKb := (st6_prec_det_iff sz hsz _ _).1
    (stKbound_of_flow sz hd hκ hz t ht0 ht1 2 (by norm_num))
  have hXD := (st6_prec_det_iff sz hsz _ _).1 (lwExpTerm4_XD sz hd hκ hε hz ht0 htz hLK)
  have hTa := (st6_prec_det_iff sz hsz _ _).1 (lwExpTerm4_Ta_det sz hd hκ hε hz ht0 htz K hC hLmax hLK)
  have hKw := (st6_prec_det_iff sz hsz _ _).1 (lwExpTerm4_kward d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz t ht0 htz)
  refine (st6_prec_det_iff sz hsz _ _).2 ?_
  intro τ hτ
  have hτ4 : 0 < τ / 4 := by positivity
  filter_upwards [hEX (τ / 4) hτ4, hKb (τ / 4) hτ4, hXD (τ / 4) hτ4, hTa (τ / 4) hτ4, hKw (τ / 4) hτ4,
    ((tendsto_rpow_atTop hτ4).comp hsz).eventually (eventually_ge_atTop (C + 2))] with
    n hEXn hKn hXDn hTan hKwn hN2
  rintro ⟨⟨σ₁, s⟩, ab⟩
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := Nat.cast_pos.mpr (by have := sz.one_le_size n; omega)
  set B : ℝ := sz.Bctl n (t n) with hBdef
  have hB : 0 < B := STBctl_pos sz n (ht1 n)
  set e : ℝ := (etaT (STflowE z n) (t n))⁻¹ with hedef
  have he : 0 < e := inv_pos.2 (etaT_pos (hE2 n) (ht1 n))
  have hN2' : C + 2 ≤ N ^ (τ / 4) := hN2
  set u : ℝ := N ^ (τ / 4) with hu
  have hu0 : 0 ≤ u := by linarith
  have hsplit := lwExpTerm4_I41K_split (P := sz.seqP) (((sz.W n : ℕ) : ℂ) ^ d)
    (K n) (fun a₂ a₃ => SB d (sz.L n) (sz.lam n) a₂ a₃)
    (fun a₁ ω => Lloop sz n (STflowE z n) (t n) ![σ₁] ![a₁] ω - mSigma (STflowE z n) σ₁)
    (fun a₂ ω => Lloop sz n (STflowE z n) (t n) ![s, true] ![ab 0, a₂] ω)
    (fun a₃ ω => Lloop sz n (STflowE z n) (t n) ![s, true] ![a₃, ab 1] ω)
    (fun a₂ => STKloop sz n (STflowE z n) (t n) ![s, true] ![ab 0, a₂])
    (fun a₃ => STKloop sz n (STflowE z n) (t n) ![s, true] ![a₃, ab 1])
    (fun a₁ => lwExpTerm2_BM_X sz n (hE2 n) (ht1 n) σ₁ a₁)
    (fun a₂ => lwExpTerm2_BM_Lloop sz n (hE2 n) (ht1 n) (k := 1) _ _)
    (fun a₃ => lwExpTerm2_BM_Lloop sz n (hE2 n) (ht1 n) (k := 1) _ _)
  -- the three bounds
  have hx : ∀ a₁ : Zd d (sz.L n), ‖∫ ω, (Lloop sz n (STflowE z n) (t n) ![σ₁] ![a₁] ω -
      mSigma (STflowE z n) σ₁) ∂(sz.seqP)‖ ≤ u * B ^ 2 := fun a₁ => by
    rw [lwExpTerm4_int_X sz n (hE2 n) (ht1 n)]; exact hEXn (σ₁, a₁)
  have hk : ∀ a₂ : Zd d (sz.L n),
      ‖STKloop sz n (STflowE z n) (t n) ![s, true] ![ab 0, a₂]‖ ≤ u * B := fun a₂ => by
    simpa using hKn (![s, true], ![ab 0, a₂])
  have hxd : ∀ a₁ a₂ : Zd d (sz.L n), ‖∫ ω, (Lloop sz n (STflowE z n) (t n) ![σ₁] ![a₁] ω -
      mSigma (STflowE z n) σ₁) * (Lloop sz n (STflowE z n) (t n) ![s, true] ![ab 0, a₂] ω -
        STKloop sz n (STflowE z n) (t n) ![s, true] ![ab 0, a₂]) ∂(sz.seqP)‖ ≤ u * B ^ 3 :=
    fun a₁ a₂ => hXDn ((σ₁, ![s, true]), (![ab 0, a₂], a₁))
  have hkw : ((sz.W n : ℕ) : ℝ) ^ d * ∑ a₃,
      ‖STKloop sz n (STflowE z n) (t n) ![s, true] ![a₃, ab 1]‖ ≤ u * e := hKwn (s, ab 1)
  have hT1 := lwExpTerm4_Tb_n sz n (K n) (hC n)
    (fun a₁ a₂ => (∫ ω, (Lloop sz n (STflowE z n) (t n) ![σ₁] ![a₁] ω -
      mSigma (STflowE z n) σ₁) ∂(sz.seqP)) * STKloop sz n (STflowE z n) (t n) ![s, true] ![ab 0, a₂])
    (fun a₃ => STKloop sz n (STflowE z n) (t n) ![s, true] ![a₃, ab 1]) (c := (u * B ^ 2) * (u * B))
    (fun a₁ a₂ => by
      rw [norm_mul]
      exact mul_le_mul (hx a₁) (hk a₂) (norm_nonneg _) (by positivity))
  have hT2 := lwExpTerm4_Tb_n sz n (K n) (hC n)
    (fun a₁ a₂ => ∫ ω, (Lloop sz n (STflowE z n) (t n) ![σ₁] ![a₁] ω - mSigma (STflowE z n) σ₁) *
      (Lloop sz n (STflowE z n) (t n) ![s, true] ![ab 0, a₂] ω -
        STKloop sz n (STflowE z n) (t n) ![s, true] ![ab 0, a₂]) ∂(sz.seqP))
    (fun a₃ => STKloop sz n (STflowE z n) (t n) ![s, true] ![a₃, ab 1]) (c := u * B ^ 3) hxd
  have hTa' := hTan ((σ₁, s), ab)
  refine (congrArg norm hsplit).le.trans ?_
  have hW0 : 0 ≤ u * e := by positivity
  have hb1 : 0 ≤ C * ((u * B ^ 2) * (u * B)) := by positivity
  have hb2 : 0 ≤ C * (u * B ^ 3) := by positivity
  calc _ ≤ ‖∫ ω, lwExpTerm4_Ra sz n (K n) (STflowE z n) (t n) σ₁ s ab ω ∂(sz.seqP)‖ +
        ‖(((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃, K n a₁ a₂ * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
          (((∫ ω, (Lloop sz n (STflowE z n) (t n) ![σ₁] ![a₁] ω -
            mSigma (STflowE z n) σ₁) ∂(sz.seqP)) * STKloop sz n (STflowE z n) (t n) ![s, true]
              ![ab 0, a₂]) * STKloop sz n (STflowE z n) (t n) ![s, true] ![a₃, ab 1])‖ +
        ‖(((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃, K n a₁ a₂ * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
          ((∫ ω, (Lloop sz n (STflowE z n) (t n) ![σ₁] ![a₁] ω -
            mSigma (STflowE z n) σ₁) * (Lloop sz n (STflowE z n) (t n) ![s, true] ![ab 0, a₂] ω -
              STKloop sz n (STflowE z n) (t n) ![s, true] ![ab 0, a₂]) ∂(sz.seqP)) *
                STKloop sz n (STflowE z n) (t n) ![s, true] ![a₃, ab 1])‖ :=
        (norm_add₃_le).trans (le_of_eq rfl)
    _ ≤ u * (e * B ^ 3) + (C * ((u * B ^ 2) * (u * B))) * (u * e) + (C * (u * B ^ 3)) * (u * e) := by
        refine add_le_add (add_le_add hTa' ?_) ?_
        · exact hT1.trans (mul_le_mul_of_nonneg_left hkw hb1)
        · exact hT2.trans (mul_le_mul_of_nonneg_left hkw hb2)
    _ ≤ N ^ τ * (e * B ^ 3) := by
        have hu4 : N ^ τ = u ^ 4 := by
          rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; congr 1; push_cast; ring
        rw [hu4]
        have hCu : C ≤ u - 2 := by linarith
        have hu2 : 2 ≤ u := by linarith
        have a1 : 2 * u ^ 2 ≤ u ^ 2 * (u - C) := by nlinarith [sq_nonneg u]
        have a2 : C * u ≤ (u - 2) * u := by nlinarith
        have h1 : 0 ≤ u ^ 3 - C * u ^ 2 - C * u - 1 := by nlinarith
        have h2 : 0 ≤ u * (u ^ 3 - C * u ^ 2 - C * u - 1) * (e * B ^ 3) :=
          mul_nonneg (mul_nonneg hu0 h1) (by positivity)
        nlinarith [h2]


/-- **Target 9** (`lwCutExp_of_G5'`): with LW-14d, `LWCutExp` needs only `LWExpG5'` (LW-14c). -/
theorem lwCutExp_of_G5' (d : ℕ) : LWExpG5' d → LWCutExp d :=
  lwCutExp_of_terms d (lwExpI1K_holds d) (lwExpI23K_holds d) (lwExpI41K_holds d)

end RBM.Gauss.Sizes

/-! ## 10. Compiled nonempty instances (`d = 3`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, the merged data `sz0`, `z0`, `tInst` of
`RBM.Gauss.LWInst`, `n = 0`): every deterministic hypothesis is discharged (`3 ≤ 3`, `0 < 1/10`, `flow_z0`, `0 ≤ tInst`,
`tInst ≤ lemT z0`, `|E| < 2`, `t < 1`); the local laws (`LWAvgLaw`, `STLK`, `STLmax`, `STLocalEntry`, `STDecay`) and `LWExpG5'`
(LW-14c) are other gates' pins and stay hypotheses -/

namespace RBM.Gauss.LWInst

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst Filter

/-- **Instance of `lwCutExp_of_G5'`**: `LWExpG5' 3` and the five local laws give `lem:LWterm_EXP` at the preflight data,
through the merged `inst_LWtermEXP`. -/
theorem lwExpTerm4_inst_cut (h5 : LWExpG5' 3) (h1 : STLocalEntry sz0 (STflowE z0) tInst)
    (h2 : LWAvgLaw sz0 (STflowE z0) tInst) (h3 : STLmax sz0 (STflowE z0) tInst)
    (h4 : STLK sz0 (STflowE z0) tInst) (h5' : STDecay sz0 (STflowE z0) tInst) :
    Prec sz0 (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)) //
        sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - tInst n})
      (fun n p _ => ‖∫ ω, LWE sz0 n (STflowE z0 n) (tInst n) p.1.1 p.1.2 ω ∂(sz0.seqP)‖)
      (fun n _ _ => (1 - tInst n)⁻¹ * (sz0.Bctl n (tInst n)) ^ (5 / 2 : ℝ)) :=
  inst_LWtermEXP (lwTermEXP_of_cut 3 (lwCutExp_of_G5' 3 h5)) h1 h2 h3 h4 h5'

/-- **Instance of target 6** at the kernel `K = lwExpTerm2_KK` of the expansion. -/
theorem lwExpTerm4_inst_I1K (hLW : LWAvgLaw sz0 (STflowE z0) tInst) (hLK : STLK sz0 (STflowE z0) tInst) :
    Prec sz0 (U := fun n => (Bool × (Fin 2 → Bool)) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p _ => ‖∑ a₁, lwExpTerm2_KK sz0 n (STflowE z0 n) (tInst n) a₁ (p.2 1) *
          ∫ ω, (Lloop sz0 n (STflowE z0 n) (tInst n) ![p.1.1] ![a₁] ω - mSigma (STflowE z0 n) p.1.1) *
            Lloop sz0 n (STflowE z0 n) (tInst n) p.1.2 p.2 ω ∂(sz0.seqP)‖)
      (fun n _ _ => (sz0.Bctl n (tInst n)) ^ 3) :=
  lwExpI1K_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2 (fun n => lwExpTerm2_KK sz0 n (STflowE z0 n) (tInst n))
    lwExpTerm2_inst_ker_KK hLW hLK

/-- **Instance of target 7** at `K = lwExpTerm2_KK`. -/
theorem lwExpTerm4_inst_I23K (hLE : STLocalEntry sz0 (STflowE z0) tInst) (hLW : LWAvgLaw sz0 (STflowE z0) tInst)
    (hLmax : STLmax sz0 (STflowE z0) tInst) (hLK : STLK sz0 (STflowE z0) tInst)
    (hDec : STDecay sz0 (STflowE z0) tInst) :
    Prec sz0 (U := fun n => (Bool × Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p _ => ‖(((sz0.W n : ℕ) : ℂ) ^ 3) * ∑ a₁, ∑ a₂, ∑ a₃,
          lwExpTerm2_KK sz0 n (STflowE z0 n) (tInst n) a₁ a₂ * (SB 3 (sz0.L n) (sz0.lam n) a₂ a₃ : ℂ) *
          ∫ ω, (Lloop sz0 n (STflowE z0 n) (tInst n) ![true] ![a₁] ω - mSigma (STflowE z0 n) true) *
            (Lloop sz0 n (STflowE z0 n) (tInst n) ![true] ![if p.1.1 then a₃ else a₂] ω -
              mSigma (STflowE z0 n) true) *
            Lloop sz0 n (STflowE z0 n) (tInst n) ![true, true, p.1.2]
              ![if p.1.1 then a₂ else a₃, p.2 0, p.2 1] ω ∂(sz0.seqP)‖)
      (fun n _ _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * (sz0.Bctl n (tInst n)) ^ (5 / 2 : ℝ)) :=
  lwExpI23K_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2 (fun n => lwExpTerm2_KK sz0 n (STflowE z0 n) (tInst n))
    lwExpTerm2_inst_ker_KK hLE hLW hLmax hLK hDec

/-- **Instance of target 8** at `K = lwExpTerm2_KK`, both charges `s`. -/
theorem lwExpTerm4_inst_I41K (hLW : LWAvgLaw sz0 (STflowE z0) tInst) (hLmax : STLmax sz0 (STflowE z0) tInst)
    (hLK : STLK sz0 (STflowE z0) tInst) :
    Prec sz0 (U := fun n => (Bool × Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p _ => ‖(((sz0.W n : ℕ) : ℂ) ^ 3) * ∑ a₁, ∑ a₂, ∑ a₃,
          lwExpTerm2_KK sz0 n (STflowE z0 n) (tInst n) a₁ a₂ * (SB 3 (sz0.L n) (sz0.lam n) a₂ a₃ : ℂ) *
          ∫ ω, (Lloop sz0 n (STflowE z0 n) (tInst n) ![p.1.1] ![a₁] ω - mSigma (STflowE z0 n) p.1.1) *
            Lloop sz0 n (STflowE z0 n) (tInst n) ![p.1.2, true] ![p.2 0, a₂] ω *
            Lloop sz0 n (STflowE z0 n) (tInst n) ![p.1.2, true] ![a₃, p.2 1] ω ∂(sz0.seqP)‖)
      (fun n _ _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * (sz0.Bctl n (tInst n)) ^ 3) :=
  lwExpI41K_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2 (fun n => lwExpTerm2_KK sz0 n (STflowE z0 n) (tInst n))
    lwExpTerm2_inst_ker_KK hLW hLmax hLK

/-- **Instance of target 1** at `K = lwExpTerm2_KK` (`LWExpKer`: `lwExpTerm2_inst_ker_KK`). -/
theorem lwExpTerm4_inst_kerSum :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (b : Zd 3 (sz0.L n)),
      ∑ a : Zd 3 (sz0.L n), ‖lwExpTerm2_KK sz0 n (STflowE z0 n) (tInst n) a b‖ ≤ C ∧
        ∑ a : Zd 3 (sz0.L n), ‖lwExpTerm2_KK sz0 n (STflowE z0 n) (tInst n) b a‖ ≤ C :=
  lwExpTerm4_kerSum 3 sz0 (fun n => lwExpTerm2_KK sz0 n (STflowE z0 n) (tInst n)) lwExpTerm2_inst_ker_KK

/-- **Instance of target 2** at `n = 0` (`L = 4`, `W = 32`), `E = STflowE z0 0`, `t = tInst 0 = 1/16`, both charges
`s`, every block `a` and every sample `ω`: `|E| < 2`, `t < 1` are discharged. -/
theorem lwExpTerm4_inst_ward2 (s : Bool) (a : Zd 3 (sz0.L 0)) (ω : sz0.SeqΩ) :
    (((sz0.W 0 : ℕ) : ℝ) ^ 3) * ∑ b : Zd 3 (sz0.L 0),
        ‖Lloop sz0 0 (STflowE z0 0) (tInst 0) ![s, true] ![a, b] ω‖ ≤
      (etaT (STflowE z0 0) (tInst 0))⁻¹ * ‖Lloop sz0 0 (STflowE z0 0) (tInst 0) ![true] ![a] ω‖ :=
  lwExpTerm4_ward2 3 sz0 0 (STflowE z0 0) (tInst 0)
    (st6_flowE_lt_two sz0 (by norm_num : (0 : ℝ) < 1 / 10) flow_z0 0) (st5_t_lt_one sz0 flow_z0 tInst_range.2 0)
    s a ω

/-- **Instance of target 5** at `n = 0`, `E = STflowE z0 0`, `t = tInst 0`: both charges `σ`, every pair of blocks
`(b, c)`, every sample, every `A ≥ max_x |G_{xx}|`. -/
theorem lwExpTerm4_inst_L3 (σ : Bool) (b c : Zd 3 (sz0.L 0)) (ω : sz0.SeqΩ) (A : ℝ)
    (hA : ∀ x : Idx 3 (sz0.L 0) (sz0.W 0), ‖Gt sz0 0 (STflowE z0 0) (tInst 0) true ω x x‖ ≤ A) :
    (((sz0.W 0 : ℕ) : ℝ) ^ 3) * ∑ a : Zd 3 (sz0.L 0),
        ‖Lloop sz0 0 (STflowE z0 0) (tInst 0) ![true, true, σ] ![a, b, c] ω‖ ≤
      (etaT (STflowE z0 0) (tInst 0))⁻¹ * A * Real.sqrt (STmaxLoop2 sz0 0 (STflowE z0 0) (tInst 0) ω) :=
  lwExpTerm4_L3 3 sz0 0 (STflowE z0 0) (tInst 0)
    (st6_flowE_lt_two sz0 (by norm_num : (0 : ℝ) < 1 / 10) flow_z0 0) (st5_t_lt_one sz0 flow_z0 tInst_range.2 0)
    σ b c ω A hA

/-- **Instance of target 5 with every hypothesis discharged**: `A = η⁻¹ ≥ max_x |G_{xx}|` (`lwExpTerm4_Gt_entry_le`). -/
theorem lwExpTerm4_inst_L3_full (σ : Bool) (b c : Zd 3 (sz0.L 0)) (ω : sz0.SeqΩ) :
    (((sz0.W 0 : ℕ) : ℝ) ^ 3) * ∑ a : Zd 3 (sz0.L 0),
        ‖Lloop sz0 0 (STflowE z0 0) (tInst 0) ![true, true, σ] ![a, b, c] ω‖ ≤
      (etaT (STflowE z0 0) (tInst 0))⁻¹ * (etaT (STflowE z0 0) (tInst 0))⁻¹ *
        Real.sqrt (STmaxLoop2 sz0 0 (STflowE z0 0) (tInst 0) ω) :=
  lwExpTerm4_inst_L3 σ b c ω _ fun x =>
    lwExpTerm4_Gt_entry_le sz0 0 (st6_flowE_lt_two sz0 (by norm_num : (0 : ℝ) < 1 / 10) flow_z0 0)
      (st5_t_lt_one sz0 flow_z0 tInst_range.2 0) ω x

/-- **Instance of target 3** at `(sz0, z0, tInst)`: no hypothesis left (`stKward_of_flow`). -/
theorem lwExpTerm4_inst_kward :
    Prec sz0 (U := fun n => Bool × Zd 3 (sz0.L n))
      (fun n p _ => (((sz0.W n : ℕ) : ℝ) ^ 3) * ∑ a : Zd 3 (sz0.L n),
          ‖STKloop sz0 n (STflowE z0 n) (tInst n) ![p.1, true] ![a, p.2]‖)
      (fun n _ _ => (etaT (STflowE z0 n) (tInst n))⁻¹) :=
  lwExpTerm4_kward 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2

/-- **Instance of target 4** at `(sz0, z0, tInst)`: `STLocalEntry` (the local law of `lem_GbEXP`) is the hypothesis. -/
theorem lwExpTerm4_inst_diag (hLE : STLocalEntry sz0 (STflowE z0) tInst) :
    Prec sz0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n))
      (fun n x ω => ‖Gt sz0 n (STflowE z0 n) (tInst n) true ω x x‖) (fun _ _ _ => 1) :=
  lwExpTerm4_diag 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2 hLE

end RBM.Gauss.LWInst
