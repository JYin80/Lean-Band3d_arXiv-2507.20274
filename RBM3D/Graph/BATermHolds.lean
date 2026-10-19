/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAMomentGenB
import RBM3D.Graph.BAMomentExpGenB
import RBM3D.Graph.BAAnpLift
import RBM3D.Graph.BAExp14bB
import RBM3D.Graph.BAAuxGraph2B
import RBM3D.Graph.BAExp14dB
import RBM3D.Graph.LWTermHolds
import RBM3D.Graph.LWTermExpN
import RBM3D.BA.LWPinsBA

/-!
# `lem:LWterm` at BA and the regime `1 - t ≤ λ²/L²` of `lem: EWGn2_N` (file A)

Paper: Lemma 3.10 (`lem:LWterm`) and Lemma 3.11 (`lem: EWGn2_N`) through Section 7 ((7.1) `eq:EGC`
to (7.12), Lemma 7.1 and Lemma 7.2); Subappendix B.3 ("analogously", the proof of Lemma B.7); (B.1)
`eq:ELW_term`.  This is the BA counterpart of `Graph/LWTermHolds.lean` (Sections 1-4) and of the
regime `lwtermExpN_of_LWterm` of `Graph/LWTermExpN.lean`.

## Contents (namespace `RBM.BA`; helpers carry the stem `BATermHolds_`)

1. The algebra of `LWcutg` through `f_{xy}` (`BAExp14b_cut_true`, `baExp14b_cut_conj`): the
   pointwise bound of one term of (7.1) `eq:EGC`, the offset count, the averaging step and the
   pathwise bound `BATermHolds_LWE_le` of `LWEg` from entry bounds.  **The `M`-part**: at BA the
   closing edge is `G_{yx} = (G - M)_{yx} + M_{yx}` with `M_{yx} = 0` unless the offsets of `x`, `y`
   agree (`BAMomentGen_decay`); exactly `W^d` of the `W^{2d}` pairs of two blocks have equal
   offsets, so the `M`-part enters with the weight `W^{-d}` (`BATermHolds_card_off`).
2. The Markov step at the BA carrier (`BATermHolds_fB`, from `baLWMoment_closed` through
   `LWTermHolds_prec_of_moments`), (7.2) `eq:directG1` at BA (`BATermHolds_GM_B`:
   `baGbyZeta_holds` at `R = 0`, `ρ = (log W)^{3/2}`, `baZetaClaim_holds`), the entry law, the
   averaged local law (`BAMomentGen_avg_whp`), the `M`-part facts, the arithmetic, and
   **`baLWterm_holds : ∀ d, BALWterm d`**.
3. The regime `1 - t ≤ λ²/L²` of `lem: EWGn2_N`: the statement def `BALWtermExpN` and
   **`baLWtermExpN_holds : ∀ d, BALWtermExpN d`**, from `baLWterm_holds` at the B class `LWPhiB`
   (`lwN_prec_mono`, `lwN_tailW_le`, `lwN_B_le_tail`, `lwN_size_rpow_neg_le`, `lwN_Wneg_le`;
   `BAExp14d_Bctl_small` in the place of `lwN_Bctl_le`).

**Public names**: `baLWterm_holds`, `BALWtermExpN`, `baLWtermExpN_holds`; every helper is private
(file B reads them by `open private`).  The public theorems have the binder `d : ℕ` only (the
hypotheses `LWAssmgL`, `LWAssmExpgL` occur inside the statements `BALWterm` and `BALWtermExpN`);
the private lemmas that take the hypotheses of `LWAssmgL` take them unfolded (as in
`Graph/BAMomentGen.lean` Section 6).  The other regime and the union are in
`Graph/BATermHoldsB.lean`.
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false

open MeasureTheory Filter Matrix

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-! ## 1. The algebra of `LWcutg` through `f_{xy}`, with the `M`-part -/

section Alg

variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} (n : ℕ) (t : ℝ) (ω : sz.SeqΩ)

private theorem BATermHolds_zdistInf_zero (L : ℕ) : zdistInf d L (0 : Zd d L) = 0 := by
  unfold zdistInf
  exact Nat.eq_zero_of_le_zero (Finset.sup_le fun i _ => by simp)

private theorem BATermHolds_zdistInf_sub_comm (L : ℕ) [NeZero L] (x y : Zd d L) :
    zdistInf d L (x - y) = zdistInf d L (y - x) := by
  rw [← neg_sub, BAAuxGraph2_zdistInf_neg]

/-- `f_{xy} = Σ_{α ∉ {x,y}} X_{[α]} G_{xα} G_{αy}` (`Σ_β W^{-d} S_{[α][β]} Ǧ_{ββ} = X_{[α]}`). -/
private theorem BATermHolds_f_eq (x y : Idx d (sz.L n) (sz.W n)) :
    LWfg (baFMz sz z) n t ω x y = ∑ α, if α = x ∨ α = y then (0 : ℂ) else
      BAExp14a_X sz z n t ω (STblk sz n α) * (baFMz sz z).G n t ω x α * (baFMz sz z).G n t ω α y := by
  unfold LWfg
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs
  · rfl
  · rw [← BAMomentGen_sumS (z := z) n t ω α, Finset.sum_mul, Finset.sum_mul]

/-- The split `Σ_α X_{[α]} G_{xα} G_{αy} = f_{xy} + f̃_{xy}`, `f̃` the contribution of `α ∈ {x, y}` ((7.4) `fxyG_sum`). -/
private theorem BATermHolds_F_split (x y : Idx d (sz.L n) (sz.W n)) :
    ∑ α, BAExp14a_X sz z n t ω (STblk sz n α) * ((baFMz sz z).G n t ω x α * (baFMz sz z).G n t ω α y) =
      LWfg (baFMz sz z) n t ω x y + ∑ α ∈ ({x, y} : Finset (Idx d (sz.L n) (sz.W n))),
        BAExp14a_X sz z n t ω (STblk sz n α) * ((baFMz sz z).G n t ω x α * (baFMz sz z).G n t ω α y) := by
  classical
  have hs : ({x, y} : Finset (Idx d (sz.L n) (sz.W n))) = Finset.univ.filter (fun α => α = x ∨ α = y) := by
    ext α; simp
  rw [BATermHolds_f_eq, hs, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs <;> simp [mul_assoc]

/-- **The pointwise bound of one term of (7.1) `eq:EGC`**: with `‖X_c‖ ≤ μ`, `‖G_{xx}‖ ≤ A`, `‖G_{xy}‖, ‖G_{yx}‖ ≤ γ` (`x ≠ y`),
`A ≤ γ` if `x = y`, `‖f_{xy}‖ ≤ φ`:  `‖G(σ)_{yx} Σ_α X_{[α]} G_{xα} G_{αy}‖ ≤ γ (φ + 2 μ A γ)`. -/
private theorem BATermHolds_pointwise (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)) {A γ φ μ : ℝ}
    (hμ0 : 0 ≤ μ) (hA0 : 0 ≤ A) (hγ0 : 0 ≤ γ) (hX : ∀ c, ‖BAExp14a_X sz z n t ω c‖ ≤ μ)
    (hA : ∀ v, ‖(baFMz sz z).G n t ω v v‖ ≤ A)
    (hγ : x ≠ y → ‖(baFMz sz z).G n t ω x y‖ ≤ γ ∧ ‖(baFMz sz z).G n t ω y x‖ ≤ γ) (hAγ : x = y → A ≤ γ)
    (hφ : ‖LWfg (baFMz sz z) n t ω x y‖ ≤ φ) :
    ‖BAExp14a_tail sz z n t ω σ x y * ∑ α, BAExp14a_X sz z n t ω (STblk sz n α) *
      ((baFMz sz z).G n t ω x α * (baFMz sz z).G n t ω α y)‖ ≤ γ * (φ + 2 * μ * A * γ) := by
  classical
  rw [norm_mul, BATermHolds_F_split]
  have htail : ‖BAExp14a_tail sz z n t ω σ x y‖ ≤ γ := by
    unfold BAExp14a_tail
    by_cases hxy : x = y
    · subst hxy
      have h1 := hA x
      have h2 := hAγ rfl
      cases σ <;> simp only [Bool.false_eq_true, ↓reduceIte, norm_star] <;> linarith
    · obtain ⟨h1, h2⟩ := hγ hxy
      cases σ <;> simp only [Bool.false_eq_true, ↓reduceIte, norm_star] <;> assumption
  have hterm : ∀ α, ‖BAExp14a_X sz z n t ω (STblk sz n α) * ((baFMz sz z).G n t ω x α * (baFMz sz z).G n t ω α y)‖ ≤
      μ * (‖(baFMz sz z).G n t ω x α‖ * ‖(baFMz sz z).G n t ω α y‖) := fun α => by
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right (hX _) (by positivity)
  have hsum : ‖LWfg (baFMz sz z) n t ω x y + ∑ α ∈ ({x, y} : Finset (Idx d (sz.L n) (sz.W n))),
      BAExp14a_X sz z n t ω (STblk sz n α) * ((baFMz sz z).G n t ω x α * (baFMz sz z).G n t ω α y)‖ ≤
      φ + 2 * μ * A * γ := by
    refine (norm_add_le _ _).trans (add_le_add hφ ?_)
    by_cases hxy : x = y
    · subst hxy
      simp only [Finset.mem_singleton, Finset.insert_eq_of_mem, Finset.pair_eq_singleton, Finset.sum_singleton]
      refine (hterm x).trans ?_
      have h1 := hA x
      have h2 := hAγ rfl
      have h3 : ‖(baFMz sz z).G n t ω x x‖ * ‖(baFMz sz z).G n t ω x x‖ ≤ A * A :=
        mul_le_mul h1 h1 (norm_nonneg _) hA0
      nlinarith [mul_le_mul_of_nonneg_left h3 hμ0, mul_nonneg hμ0 hA0, mul_le_mul_of_nonneg_left h2 (mul_nonneg hμ0 hA0)]
    · rw [Finset.sum_pair hxy]
      refine (norm_add_le _ _).trans ?_
      obtain ⟨h1, h2⟩ := hγ hxy
      have e1 := (hterm x).trans (mul_le_mul_of_nonneg_left (mul_le_mul (hA x) h1 (norm_nonneg _) hA0) hμ0)
      have e2 := (hterm y).trans (mul_le_mul_of_nonneg_left (mul_le_mul h1 (hA y) (norm_nonneg _) hγ0) hμ0)
      nlinarith [e1, e2]
  exact mul_le_mul htail hsum (norm_nonneg _) hγ0

/-- The offset count: for fixed blocks, exactly `W^d` of the `W^{2d}` pairs `(x, y) ∈ [a_o] × [a_c]` have the same offset
(`split` is a bijection onto `Z_L^d × Fin (W^d)`). -/
private theorem BATermHolds_card_off (ao ac : Zd d (sz.L n)) :
    ∑ x ∈ Iblk d (sz.L n) (sz.W n) ao, ∑ y ∈ Iblk d (sz.L n) (sz.W n) ac,
      (if (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) y).2 then (1 : ℝ) else 0) =
      ((sz.W n : ℕ) : ℝ) ^ d := by
  classical
  have h1 : ∀ x : Idx d (sz.L n) (sz.W n), ∑ y ∈ Iblk d (sz.L n) (sz.W n) ac,
      (if (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) y).2 then (1 : ℝ) else 0) = 1 := by
    intro x
    rw [Finset.sum_boole]
    have : (Iblk d (sz.L n) (sz.W n) ac).filter
        (fun y => (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) y).2) =
        {(splitEquiv d (sz.L n) (sz.W n)).symm (ac, (split d (sz.L n) (sz.W n) x).2)} := by
      ext y
      simp only [Iblk, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [Equiv.eq_symm_apply]
      simp only [splitEquiv, Equiv.ofBijective_apply, Prod.ext_iff]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩
    rw [this]; simp
  simp only [h1, Finset.sum_const, card_Iblk, nsmul_eq_mul, mul_one]
  push_cast; rfl


/-- **The averaging step** ((7.7) `eq:recoltermwt`): if every pair `(x, y) ∈ [a_o] × [a_c]` has
`‖G(σ)_{yx} Σ_α X_{[α]} G_{xα} G_{αy}‖ ≤ b₀ + 1[off x = off y] b₁`, then `‖LWcutg(+, σ, a_c, a_o)‖ ≤ b₀ + W^{-d} b₁`
(exactly `W^d` of the `W^{2d}` pairs have the same offset, `BATermHolds_card_off`). -/
private theorem BATermHolds_cut_true_le
    (hSelf : BASelf d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) ((baFMz sz z).m n))
    (σo : Bool) (ac ao : Zd d (sz.L n)) {b0 b1 : ℝ} (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1)
    (hpair : ∀ x ∈ Iblk d (sz.L n) (sz.W n) ao, ∀ y ∈ Iblk d (sz.L n) (sz.W n) ac,
      ‖BAExp14a_tail sz z n t ω σo x y * ∑ α, BAExp14a_X sz z n t ω (STblk sz n α) *
        ((baFMz sz z).G n t ω x α * (baFMz sz z).G n t ω α y)‖ ≤
      b0 + (if (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) y).2 then b1 else 0)) :
    ‖LWcutg (baFMz sz z) n t true σo ac ao ω‖ ≤ b0 + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * b1 := by
  classical
  rw [BAExp14b_cut_true n t hSelf σo ac ao ω]
  unfold BAExp14b_fr
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos (by exact_mod_cast sz.W_pos n) d
  have hJ : ∀ x y : Idx d (sz.L n) (sz.W n), ∑ α, BAExp14a_tail sz z n t ω σo x y * (BAExp14a_X sz z n t ω (STblk sz n α) *
      ((baFMz sz z).G n t ω x α * (baFMz sz z).G n t ω α y)) = BAExp14a_tail sz z n t ω σo x y *
      ∑ α, BAExp14a_X sz z n t ω (STblk sz n α) * ((baFMz sz z).G n t ω x α * (baFMz sz z).G n t ω α y) :=
    fun x y => (Finset.mul_sum _ _ _).symm
  simp only [hJ]
  rw [norm_mul, norm_pow, norm_inv, norm_pow, Complex.norm_natCast]
  have h1 := (norm_sum_le _ _).trans (Finset.sum_le_sum fun x hx =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun y hy => hpair x hx y hy))
  have h2 : ∑ x ∈ Iblk d (sz.L n) (sz.W n) ao, ∑ y ∈ Iblk d (sz.L n) (sz.W n) ac,
      (b0 + (if (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) y).2 then b1 else 0)) =
      ((sz.W n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ d * b0 + ((sz.W n : ℕ) : ℝ) ^ d * b1 := by
    have e1 : ∀ x y : Idx d (sz.L n) (sz.W n), (b0 + (if (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) y).2 then b1 else 0)) =
        b0 + b1 * (if (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) y).2 then (1 : ℝ) else 0) :=
      fun x y => by split_ifs <;> ring
    simp only [e1, Finset.sum_add_distrib, ← Finset.mul_sum, BATermHolds_card_off, Finset.sum_const, card_Iblk, nsmul_eq_mul]
    push_cast; ring
  rw [h2] at h1
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ 2 * ‖∑ x ∈ Iblk d (sz.L n) (sz.W n) ao, ∑ y ∈ Iblk d (sz.L n) (sz.W n) ac,
        BAExp14a_tail sz z n t ω σo x y * ∑ α, BAExp14a_X sz z n t ω (STblk sz n α) *
          ((baFMz sz z).G n t ω x α * (baFMz sz z).G n t ω α y)‖
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ 2 * (((sz.W n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ d * b0 + ((sz.W n : ℕ) : ℝ) ^ d * b1) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = b0 + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * b1 := by field_simp


/-- **The pathwise bound of `LWEg`** ((7.7) `eq:recoltermwt`, both charges `σ_c`) at the block Anderson carrier: from the entry
bounds `‖G_{xx}‖ ≤ A`, `‖(G - M)_{xy}‖ ≤ γ(|[x]-[y]|)`, the off-diagonal support and decay of `M` (`M_{xy} = 0` unless the offsets agree,
`‖M_{xy}‖ ≤ Mb(|[x]-[y]|)`, `A ≤ Mb(0)`), `‖f_{xy}‖ ≤ φ(|[x]-[y]|)` and the block averages `‖𝓛^{(1)}_b - m‖ ≤ μ`:
`‖LWEg‖ ≤ 2 (γ(φ + 2μAγ) + W^{-d} (γ + Mb)(φ + 2μA(γ + Mb)))`, `r = |a₀ - a₁|`.  The second summand is the `M`-part of the closing edge
`G_{yx} = (G - M)_{yx} + M_{yx}`: only the `W^{-d}` fraction of the pairs `(x, y) ∈ [a_o] × [a_c]` with equal offsets carries it. -/
private theorem BATermHolds_LWE_le
    (hSelf : BASelf d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) ((baFMz sz z).m n))
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) {A μ : ℝ} {γ φ Mb : ℕ → ℝ}
    (hμ0 : 0 ≤ μ) (hA0 : 0 ≤ A) (hγ0 : ∀ r, 0 ≤ γ r) (hφ0 : ∀ r, 0 ≤ φ r) (hMb0 : ∀ r, 0 ≤ Mb r) (hAM : A ≤ Mb 0)
    (hμ : ∀ b : Zd d (sz.L n), ‖(baFMz sz z).L n t (fun _ : Fin 1 => true) (fun _ => b) ω - (baFMz sz z).m n‖ ≤ μ)
    (hA : ∀ v, ‖(baFMz sz z).G n t ω v v‖ ≤ A)
    (hγ : ∀ x y, ‖(baFMz sz z).GM n t ω x y‖ ≤ γ (zdistInf d (sz.L n) (STblk sz n x - STblk sz n y)))
    (hM0 : ∀ x y, (split d (sz.L n) (sz.W n) x).2 ≠ (split d (sz.L n) (sz.W n) y).2 → (baFMz sz z).M n x y = 0)
    (hM : ∀ x y, ‖(baFMz sz z).M n x y‖ ≤ Mb (zdistInf d (sz.L n) (STblk sz n x - STblk sz n y)))
    (hφ : ∀ x y, ‖LWfg (baFMz sz z) n t ω x y‖ ≤ φ (zdistInf d (sz.L n) (STblk sz n x - STblk sz n y))) :
    ‖LWEg (baFMz sz z) n t σ a ω‖ ≤ 2 * (γ (zdistInf d (sz.L n) (a 0 - a 1)) *
        (φ (zdistInf d (sz.L n) (a 0 - a 1)) + 2 * μ * A * γ (zdistInf d (sz.L n) (a 0 - a 1))) +
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((γ (zdistInf d (sz.L n) (a 0 - a 1)) + Mb (zdistInf d (sz.L n) (a 0 - a 1))) *
        (φ (zdistInf d (sz.L n) (a 0 - a 1)) + 2 * μ * A *
          (γ (zdistInf d (sz.L n) (a 0 - a 1)) + Mb (zdistInf d (sz.L n) (a 0 - a 1)))))) := by
  classical
  have hX : ∀ c, ‖BAExp14a_X sz z n t ω c‖ ≤ μ := fun c => by
    rw [BAExp14a_X_eq n t ω hSelf c]; exact hμ c
  have hG : ∀ u v, (baFMz sz z).G n t ω u v = (baFMz sz z).GM n t ω u v + (baFMz sz z).M n u v :=
    fun u v => by unfold FlowFM.GM; ring
  -- the cut at `σ_c = +` for every pair of blocks
  have key : ∀ (σo : Bool) (ac ao : Zd d (sz.L n)), ‖LWcutg (baFMz sz z) n t true σo ac ao ω‖ ≤
      γ (zdistInf d (sz.L n) (ao - ac)) * (φ (zdistInf d (sz.L n) (ao - ac)) +
        2 * μ * A * γ (zdistInf d (sz.L n) (ao - ac))) +
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((γ (zdistInf d (sz.L n) (ao - ac)) + Mb (zdistInf d (sz.L n) (ao - ac))) *
        (φ (zdistInf d (sz.L n) (ao - ac)) + 2 * μ * A *
          (γ (zdistInf d (sz.L n) (ao - ac)) + Mb (zdistInf d (sz.L n) (ao - ac))))) := by
    intro σo ac ao
    set R : ℕ := zdistInf d (sz.L n) (ao - ac) with hR
    have hg0 := hγ0 R
    have hf0 := hφ0 R
    have hm0 := hMb0 R
    have hb0 : 0 ≤ γ R * (φ R + 2 * μ * A * γ R) := by positivity
    have hb1 : 0 ≤ (γ R + Mb R) * (φ R + 2 * μ * A * (γ R + Mb R)) := by positivity
    refine BATermHolds_cut_true_le n t ω hSelf σo ac ao hb0 hb1 ?_
    intro x hx y hy
    have hxa : STblk sz n x = ao := (Finset.mem_filter.1 hx).2
    have hya : STblk sz n y = ac := (Finset.mem_filter.1 hy).2
    have hr1 : zdistInf d (sz.L n) (STblk sz n x - STblk sz n y) = R := by rw [hxa, hya]
    have hr2 : zdistInf d (sz.L n) (STblk sz n y - STblk sz n x) = R := by
      rw [BATermHolds_zdistInf_sub_comm, hr1]
    have hγ1 := hγ x y
    have hγ2 := hγ y x
    have hφ1 := hφ x y
    have hM1 := hM x y
    have hM2 := hM y x
    rw [hr1] at hγ1 hφ1 hM1
    rw [hr2] at hγ2 hM2
    by_cases hoff : (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) y).2
    · simp only [hoff, ite_true]
      refine (BATermHolds_pointwise n t ω σo x y (A := A) (γ := γ R + Mb R) (φ := φ R) (μ := μ) hμ0 hA0 (by positivity) hX hA
        (fun _ => ⟨?_, ?_⟩) (fun hxy => ?_) hφ1).trans (le_add_of_nonneg_left hb0)
      · rw [hG]; exact (norm_add_le _ _).trans (add_le_add hγ1 hM1)
      · rw [hG]; exact (norm_add_le _ _).trans (add_le_add hγ2 hM2)
      · subst hxy
        have h0 : R = 0 := by rw [← hr1, sub_self]; exact BATermHolds_zdistInf_zero _
        rw [h0] at hm0 ⊢
        linarith [hγ0 0]
    · simp only [hoff, ite_false, add_zero]
      have hne : x ≠ y := fun h => hoff (by rw [h])
      refine BATermHolds_pointwise n t ω σo x y (A := A) (γ := γ R) (φ := φ R) (μ := μ) hμ0 hA0 hg0 hX hA
        (fun _ => ⟨?_, ?_⟩) (fun h => absurd h hne) hφ1
      · rw [hG, hM0 x y hoff, add_zero]; exact hγ1
      · rw [hG, hM0 y x (Ne.symm hoff), add_zero]; exact hγ2
  -- both charges
  have cutAll : ∀ (σc σo : Bool) (ac ao : Zd d (sz.L n)), ‖LWcutg (baFMz sz z) n t σc σo ac ao ω‖ ≤
      γ (zdistInf d (sz.L n) (ao - ac)) * (φ (zdistInf d (sz.L n) (ao - ac)) +
        2 * μ * A * γ (zdistInf d (sz.L n) (ao - ac))) +
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((γ (zdistInf d (sz.L n) (ao - ac)) + Mb (zdistInf d (sz.L n) (ao - ac))) *
        (φ (zdistInf d (sz.L n) (ao - ac)) + 2 * μ * A *
          (γ (zdistInf d (sz.L n) (ao - ac)) + Mb (zdistInf d (sz.L n) (ao - ac))))) := by
    intro σc σo ac ao
    cases σc
    · have h := key (!σo) ao ac
      rw [baExp14b_cut_conj sz z n t σo ac ao ω, norm_star]
      rw [BATermHolds_zdistInf_sub_comm (sz.L n) ac ao] at h
      exact h
    · exact key σo ac ao
  unfold LWEg
  have h1 := cutAll (σ 1) (σ 0) (a 1) (a 0)
  have h2 := cutAll (σ 0) (σ 1) (a 0) (a 1)
  rw [BATermHolds_zdistInf_sub_comm (sz.L n) (a 1) (a 0)] at h2
  linarith [norm_add_le (LWcutg (baFMz sz z) n t (σ 1) (σ 0) (a 1) (a 0) ω) (LWcutg (baFMz sz z) n t (σ 0) (σ 1) (a 0) (a 1) ω)]

end Alg

/-- The arithmetic of the `B` side. -/
private theorem BATermHolds_arithB {X I P0 Pr Wd μ m c3 c3' Kz : ℝ} (hX : 1 ≤ X) (hI : 1 ≤ I) (hP0 : 0 < P0)
    (hP01 : P0 ≤ 1) (hPr : 0 < Pr) (hWd0 : 0 ≤ Wd) (hWd : Wd ≤ c3 * P0 ^ 2) (hc3 : 0 ≤ c3)
    (hc3' : 0 ≤ c3') (hμ0 : 0 ≤ μ) (hμ : μ ≤ X * (c3' * P0 ^ 2)) (hm : 0 ≤ m) (hKz : 0 ≤ Kz)
    (hmP : P0 * m ≤ Kz * Pr) :
    2 * (X * Pr * (X * (I * P0 * Pr) + 2 * μ * 2 * (X * Pr)) +
      Wd * ((X * Pr + m) * (X * (I * P0 * Pr) + 2 * μ * 2 * (X * Pr + m)))) ≤
      (2 * ((1 + 4 * c3') + c3 * (1 + Kz) + 8 * c3 * c3' * (1 + Kz ^ 2))) * (X ^ 3 * (I * P0 * Pr ^ 2)) := by
  have hX0 : 0 < X := by linarith
  have hI0 : 0 < I := by linarith
  set T : ℝ := X ^ 3 * (I * P0 * Pr ^ 2) with hT
  have hT0 : 0 ≤ T := by positivity
  have hP0sq : P0 ^ 2 ≤ I * P0 := by nlinarith
  have hP0sq1 : P0 ^ 2 ≤ 1 := by nlinarith
  have hX2 : X ^ 2 ≤ X ^ 3 := by nlinarith [pow_pos hX0 2]
  have hX1 : X ≤ X ^ 3 := by nlinarith [pow_pos hX0 2]
  -- the `X`-multiples of `I P0 Pr²` are bounded by `T`
  have hA1 : X ^ 2 * (I * P0 * Pr ^ 2) ≤ T := mul_le_mul_of_nonneg_right hX2 (by positivity)
  have hA2 : X * (I * P0 * Pr ^ 2) ≤ T := mul_le_mul_of_nonneg_right hX1 (by positivity)
  -- `μ ≤ X c3' I P0`
  have hμ' : μ ≤ X * (c3' * (I * P0)) := hμ.trans (by gcongr)
  -- off-diagonal part
  have hb0 : X * Pr * (X * (I * P0 * Pr) + 2 * μ * 2 * (X * Pr)) ≤ (1 + 4 * c3') * T := by
    have e : X * Pr * (X * (I * P0 * Pr) + 2 * μ * 2 * (X * Pr)) =
        X ^ 2 * (I * P0 * Pr ^ 2) + 4 * μ * (X ^ 2 * Pr ^ 2) := by ring
    have h1 : 4 * μ * (X ^ 2 * Pr ^ 2) ≤ 4 * c3' * T := by
      have := mul_le_mul_of_nonneg_right hμ' (by positivity : (0 : ℝ) ≤ 4 * X ^ 2 * Pr ^ 2)
      calc 4 * μ * (X ^ 2 * Pr ^ 2) = μ * (4 * X ^ 2 * Pr ^ 2) := by ring
        _ ≤ X * (c3' * (I * P0)) * (4 * X ^ 2 * Pr ^ 2) := this
        _ = 4 * c3' * T := by rw [hT]; ring
    rw [e]; nlinarith
  -- the terms with weight `W^{-d}`
  have hu : Wd * (X * Pr * (X * (I * P0 * Pr))) ≤ c3 * T := by
    have e : Wd * (X * Pr * (X * (I * P0 * Pr))) = Wd * (X ^ 2 * (I * P0 * Pr ^ 2)) := by ring
    rw [e]
    calc Wd * (X ^ 2 * (I * P0 * Pr ^ 2)) ≤ (c3 * P0 ^ 2) * (X ^ 2 * (I * P0 * Pr ^ 2)) :=
          mul_le_mul_of_nonneg_right hWd (by positivity)
      _ ≤ c3 * 1 * (X ^ 2 * (I * P0 * Pr ^ 2)) := by
          have : c3 * P0 ^ 2 ≤ c3 * 1 := mul_le_mul_of_nonneg_left hP0sq1 hc3
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ ≤ c3 * T := by nlinarith
  have hm1 : Wd * m ≤ c3 * Kz * Pr := by
    calc Wd * m ≤ (c3 * P0 ^ 2) * m := mul_le_mul_of_nonneg_right hWd hm
      _ = c3 * P0 * (P0 * m) := by ring
      _ ≤ c3 * 1 * (Kz * Pr) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hP01 hc3) hmP (by positivity) (by positivity)
      _ = c3 * Kz * Pr := by ring
  have hmF : Wd * (m * (X * (I * P0 * Pr))) ≤ c3 * Kz * T := by
    have e : Wd * (m * (X * (I * P0 * Pr))) = (Wd * m) * (X * (I * P0 * Pr)) := by ring
    rw [e]
    calc (Wd * m) * (X * (I * P0 * Pr)) ≤ (c3 * Kz * Pr) * (X * (I * P0 * Pr)) :=
          mul_le_mul_of_nonneg_right hm1 (by positivity)
      _ = c3 * Kz * (X * (I * P0 * Pr ^ 2)) := by ring
      _ ≤ c3 * Kz * T := mul_le_mul_of_nonneg_left hA2 (by positivity)
  have hμu : Wd * (μ * (X * Pr) ^ 2) ≤ c3 * c3' * T := by
    have h1 : Wd * μ ≤ (c3 * P0 ^ 2) * (X * (c3' * P0 ^ 2)) :=
      mul_le_mul hWd hμ hμ0 (by positivity)
    calc Wd * (μ * (X * Pr) ^ 2) = (Wd * μ) * (X * Pr) ^ 2 := by ring
      _ ≤ ((c3 * P0 ^ 2) * (X * (c3' * P0 ^ 2))) * (X * Pr) ^ 2 := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = c3 * c3' * (P0 ^ 3 * (X ^ 3 * (P0 * Pr ^ 2))) := by ring
      _ ≤ c3 * c3' * (1 * (X ^ 3 * (I * P0 * Pr ^ 2))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hp3 : P0 ^ 3 ≤ 1 := pow_le_one₀ hP0.le hP01
          have : P0 * Pr ^ 2 ≤ I * P0 * Pr ^ 2 := mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hP0.le hI) (sq_nonneg Pr)
          exact mul_le_mul hp3 (mul_le_mul_of_nonneg_left this (by positivity)) (by positivity) zero_le_one
      _ = c3 * c3' * T := by rw [hT]; ring
  have hμm : Wd * (μ * m ^ 2) ≤ c3 * c3' * Kz ^ 2 * T := by
    have h1 : Wd * μ ≤ (c3 * P0 ^ 2) * (X * (c3' * P0 ^ 2)) :=
      mul_le_mul hWd hμ hμ0 (by positivity)
    have h2 : (P0 * m) ^ 2 ≤ (Kz * Pr) ^ 2 := pow_le_pow_left₀ (by positivity) hmP 2
    calc Wd * (μ * m ^ 2) = (Wd * μ) * m ^ 2 := by ring
      _ ≤ ((c3 * P0 ^ 2) * (X * (c3' * P0 ^ 2))) * m ^ 2 := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = c3 * c3' * (X * P0 ^ 2) * (P0 * m) ^ 2 := by ring
      _ ≤ c3 * c3' * (X * P0 ^ 2) * (Kz * Pr) ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = c3 * c3' * Kz ^ 2 * (X * P0 ^ 2 * Pr ^ 2) := by ring
      _ ≤ c3 * c3' * Kz ^ 2 * (X * (I * P0) * Pr ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP0sq hX0.le) (by positivity)
      _ ≤ c3 * c3' * Kz ^ 2 * T := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc X * (I * P0) * Pr ^ 2 = X * (I * P0 * Pr ^ 2) := by ring
            _ ≤ T := hA2
  have hb1 : Wd * ((X * Pr + m) * (X * (I * P0 * Pr) + 2 * μ * 2 * (X * Pr + m))) ≤
      (c3 * (1 + Kz) + 8 * c3 * c3' * (1 + Kz ^ 2)) * T := by
    have e : Wd * ((X * Pr + m) * (X * (I * P0 * Pr) + 2 * μ * 2 * (X * Pr + m))) =
        Wd * (X * Pr * (X * (I * P0 * Pr))) + Wd * (m * (X * (I * P0 * Pr))) +
          4 * (Wd * (μ * (X * Pr) ^ 2)) + 8 * (Wd * (μ * (X * Pr) * m)) + 4 * (Wd * (μ * m ^ 2)) := by ring
    have hcross : Wd * (μ * (X * Pr) * m) ≤ (1 / 2) * (Wd * (μ * (X * Pr) ^ 2)) + (1 / 2) * (Wd * (μ * m ^ 2)) := by
      have : μ * (X * Pr) * m ≤ (1 / 2) * (μ * (X * Pr) ^ 2) + (1 / 2) * (μ * m ^ 2) := by
        nlinarith [mul_nonneg hμ0 (sq_nonneg (X * Pr - m))]
      calc Wd * (μ * (X * Pr) * m) ≤ Wd * ((1 / 2) * (μ * (X * Pr) ^ 2) + (1 / 2) * (μ * m ^ 2)) :=
            mul_le_mul_of_nonneg_left this hWd0
        _ = _ := by ring
    rw [e]
    nlinarith [hu, hmF, hμu, hμm, hcross]
  have hfin : 2 * (X * Pr * (X * (I * P0 * Pr) + 2 * μ * 2 * (X * Pr)) +
      Wd * ((X * Pr + m) * (X * (I * P0 * Pr) + 2 * μ * 2 * (X * Pr + m)))) ≤
      2 * ((1 + 4 * c3') * T + (c3 * (1 + Kz) + 8 * c3 * c3' * (1 + Kz ^ 2)) * T) := by
    linarith [hb0, hb1]
  calc _ ≤ _ := hfin
    _ = _ := by ring

/-- `(max 1 r)^{C₂} e^{-c r}` is bounded on `r ≥ 0` (`r e^{-s r} ≤ 1/s`, `s = c / C₂`). -/
private theorem BATermHolds_poly_exp {C₂ c : ℝ} (hC₂ : 0 < C₂) (hc : 0 < c) :
    ∃ E : ℝ, 0 < E ∧ ∀ r : ℝ, 0 ≤ r → (max 1 r) ^ C₂ * Real.exp (-(c * r)) ≤ E := by
  refine ⟨max 1 ((C₂ / c) ^ C₂), lt_max_of_lt_left one_pos, fun r hr => ?_⟩
  by_cases hr1 : r ≤ 1
  · rw [max_eq_left hr1, Real.one_rpow, one_mul]
    exact (Real.exp_le_one_iff.2 (by nlinarith)).trans (le_max_left _ _)
  · push Not at hr1
    rw [max_eq_right hr1.le]
    have hs : 0 < c / C₂ := by positivity
    have h1 : r * Real.exp (-(c / C₂ * r)) ≤ C₂ / c := by
      have h2 := Real.add_one_le_exp (c / C₂ * r)
      have h3 : c / C₂ * r * Real.exp (-(c / C₂ * r)) ≤ 1 := by
        have h4 : c / C₂ * r ≤ Real.exp (c / C₂ * r) := by linarith
        calc c / C₂ * r * Real.exp (-(c / C₂ * r)) ≤ Real.exp (c / C₂ * r) * Real.exp (-(c / C₂ * r)) :=
              mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
          _ = 1 := by rw [← Real.exp_add]; simp
      have h5 : r * Real.exp (-(c / C₂ * r)) = (C₂ / c) * (c / C₂ * r * Real.exp (-(c / C₂ * r))) := by
        field_simp
      rw [h5]
      calc C₂ / c * (c / C₂ * r * Real.exp (-(c / C₂ * r))) ≤ C₂ / c * 1 :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = C₂ / c := mul_one _
    calc r ^ C₂ * Real.exp (-(c * r)) = (r * Real.exp (-(c / C₂ * r))) ^ C₂ := by
          rw [Real.mul_rpow (by linarith) (Real.exp_pos _).le, ← Real.exp_mul]
          congr 2; field_simp
      _ ≤ (C₂ / c) ^ C₂ := Real.rpow_le_rpow (by positivity) h1 hC₂.le
      _ ≤ _ := le_max_right _ _


/-- `W → ∞` (`W ≥ N^𝔠`, `N → ∞`). -/
private theorem BATermHolds_W_tendsto {d : ℕ} {sz : Sizes d} {𝔠 𝔡 : ℝ} (hadm : sz.Admissible 𝔠 𝔡) :
    Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := by
  obtain ⟨h𝔠, -, hsz, hband, -⟩ := hadm
  exact tendsto_atTop_mono' atTop hband ((tendsto_rpow_atTop h𝔠).comp hsz)

/-- `log W → ∞`. -/
private theorem BATermHolds_logW_tendsto {d : ℕ} {sz : Sizes d} {𝔠 𝔡 : ℝ} (hadm : sz.Admissible 𝔠 𝔡) :
    Tendsto (fun n => Real.log ((sz.W n : ℕ) : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp (BATermHolds_W_tendsto hadm)

section BSide

variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔡 𝔠 : ℝ} {t : ℕ → ℝ} {ε₀ C₁ C₂ C₃ : ℝ} {Cc : ℝ → ℝ} {Ψ : ℕ → ℝ}
  {Φ : ℕ → ℝ → ℝ}
  (hd : 3 ≤ d) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : ∀ n, 0 ≤ t n)
  (ht1 : ∀ n, t n ≤ BAflowT0 sz z n)
  (hassm : 0 < ε₀ ∧ LWWindow sz ε₀ Ψ ∧ STInitialGT2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ ∧
    LWClass sz ε₀ C₃ Φ ∧ LWPsiRel C₁ C₂ Cc Φ ∧
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Bool × Zd d (sz.L n) × Zd d (sz.L n))
      (fun n p ω => ‖(baFMz sz z).L n (t n) ![p.1, !p.1] ![p.2.1, p.2.2] ω‖)
      (fun n p _ => Φ n ((zdistInf d (sz.L n) (p.2.1 - p.2.2) : ℕ) : ℝ) ^ 2))
include hd hκ hε h𝔡 hflow ht0 ht1 hassm

/-- **The Markov step at the BA carrier** ((7.11) `eq:LW_moment_exp`, proof of Lemma 7.2; as `LWTermHolds_fB` in `Graph/LWTermHolds.lean`): `f_{xy} ≺ η_t⁻¹ Φ(0) Φ(|a-b|)`
from the moment bound `baLWMoment_closed` (`p = 2 p₀`, `p₀ = ⌈(D+2)/τ₀⌉ + 1`), the integrability of `|f_{xy}|^p` (`BAMomentExp_integrable` at
`Dm = univ`, `LWfgD_univ`), `Φ(c r) ≲ Φ(r)` (`LWPsiAll.shift`) and the union bound over the `N²` pairs (`LWTermHolds_prec_of_moments`). -/
private theorem BATermHolds_fB :
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n q ω => ‖LWfg (baFMz sz z) n (t n) ω q.1 q.2‖)
      (fun n q _ => ((baFMz sz z).eta n (t n))⁻¹ * Φ n 0 *
        Φ n ((zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2) : ℕ) : ℝ)) := by
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  refine LWTermHolds_prec_of_moments (sz.withLam 0) hsz
    (V := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n q ω => ‖LWfg (baFMz sz z) n (t n) ω q.1 q.2‖)
    (fun n q => ((baFMz sz z).eta n (t n))⁻¹ * Φ n 0 *
      Φ n ((zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2) : ℕ) : ℝ)) (C := 2) ?_
    (fun n q ω => norm_nonneg _) (fun p n q => ?_) ?_ ?_
  · refine Eventually.of_forall fun n => ?_
    rw [Fintype.card_prod, Sizes.card_Idx, Real.rpow_two]
    push_cast; ring_nf; exact le_rfl
  · have h2 : Integrable (fun ω => ‖LWfg (baFMz sz z) n (t n) ω q.1 q.2‖ ^ p) (BAExp14a_μ sz) := by
      simpa only [LWfgD_univ] using BAMomentExp_integrable hκ hflow n (ht0 n) (ht1 n) p Finset.univ q.1 q.2
    exact h2
  · filter_upwards [hassm.2.2.2.1.1] with n hcl q
    have h1 := (hcl 0 le_rfl).1
    have h2 := (hcl _ (Nat.cast_nonneg (zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2)))).1
    have h3 : 0 < ((baFMz sz z).eta n (t n))⁻¹ := inv_pos.2 (BAExp14a_eta_pos hκ hflow n (ht0 n) (ht1 n))
    positivity
  · intro τ₀ hτ₀ D hD
    set p₀ : ℕ := ⌈(D + 2) / τ₀⌉₊ + 1 with hp₀
    have hp2 : 2 ∣ 2 * p₀ := dvd_mul_right _ _
    obtain ⟨c, hc, H⟩ := baLWMoment_closed d hd κ ε 𝔡 hκ hε h𝔡 (2 * p₀) hp2 ε₀ C₁ C₂ C₃ Cc
    have hH := H 𝔠 sz z hflow t ht0 ht1 Ψ Φ hassm
    obtain ⟨K, hK, hshift⟩ := LWPsiAll.shift sz (BAMomentGen_psiAll hd hκ hε h𝔡 hflow ht0 ht1 hassm) hc
    refine ⟨2 * p₀, by omega, ?_, K, hK, ?_⟩
    · have h1 : (D + 2) / τ₀ ≤ (⌈(D + 2) / τ₀⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : D + 2 ≤ τ₀ * (⌈(D + 2) / τ₀⌉₊ : ℝ) := by
        have := mul_le_mul_of_nonneg_left h1 hτ₀.le
        rwa [mul_div_cancel₀ _ hτ₀.ne'] at this
      have hp : ((2 * p₀ : ℕ) : ℝ) = 2 * ((⌈(D + 2) / τ₀⌉₊ : ℝ) + 1) := by rw [hp₀]; push_cast; ring
      rw [hp]
      nlinarith [h2, hτ₀]
    · have h1 := (BAExp14a_det_iff (P := BAExp14a_μ sz) (Sizes.tendsto_size sz hsz) _ _).1 hH 1 one_pos
      filter_upwards [h1, hshift, hassm.2.2.2.1.1] with n hn hs hcl q
      refine (hn q).trans ?_
      rw [Real.rpow_one]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      have hη : 0 < ((baFMz sz z).eta n (t n))⁻¹ := inv_pos.2 (BAExp14a_eta_pos hκ hflow n (ht0 n) (ht1 n))
      have h0 := (hcl 0 le_rfl).1
      have hr : (0 : ℝ) ≤ ((zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2) : ℕ) : ℝ) := Nat.cast_nonneg _
      have hcr : 0 < Φ n (c * ((zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2) : ℕ) : ℝ)) :=
        (hcl _ (by positivity)).1
      refine pow_le_pow_left₀ (by positivity) ?_ _
      calc ((baFMz sz z).eta n (t n))⁻¹ * Φ n 0 * Φ n (c * ((zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2) : ℕ) : ℝ))
          ≤ ((baFMz sz z).eta n (t n))⁻¹ * Φ n 0 * (K * Φ n ((zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2) : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left (hs _ hr) (by positivity)
        _ = _ := by ring


/-- **(7.2) `eq:directG1` at BA** ((B.22) `eq:Gbyxi2_BA`; as `LWTermHolds_Gij_B`): `‖(G_t - M)_{xy}‖ ≺ Φ(|[x]-[y]|)` for all `x, y`
(`baGbyZeta_holds` at `R = 0`, `ρ = (log W)^{3/2}`, then the claim (7.34) `eq:Gbyxi2` = `baZetaClaim_holds`). -/
private theorem BATermHolds_GM_B :
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n q ω => ‖(baFMz sz z).GM n (t n) ω q.1 q.2‖)
      (fun n q _ => Φ n ((zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2) : ℕ) : ℝ)) := by
  have hadm := hflow.1
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have hent := hassm.2.2.1.1
  set ρ : ℕ → ℝ := fun n => Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) with hρ
  have hW1 : ∀ n, (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := fun n => Nat.one_le_cast.2 (sz.W_pos n)
  have hρ0 : ∀ n, 0 ≤ ρ n := fun n => Real.rpow_nonneg (Real.log_nonneg (hW1 n)) _
  have hρrad : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ρ n + 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := fun τ hτ => by
    filter_upwards [lwXiRad_holds sz hsz 1 0 (3 / 2) zero_le_one le_rfl (by norm_num) τ hτ] with n hn
    simpa [hρ] using hn
  have hsep : ∀ K : ℝ, ∀ᶠ n in atTop, K * Real.log ((sz.W n : ℕ) : ℝ) ≤ ρ n - 2 * (fun _ : ℕ => (0 : ℝ)) n := fun K => by
    filter_upwards [(BATermHolds_logW_tendsto hadm).eventually_ge_atTop (K ^ 2),
      (BATermHolds_logW_tendsto hadm).eventually_ge_atTop 1] with n h1 h2
    have e : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) =
        Real.log ((sz.W n : ℕ) : ℝ) * Real.sqrt (Real.log ((sz.W n : ℕ) : ℝ)) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one, Real.sqrt_eq_rpow]
    simp only [hρ, mul_zero, sub_zero, e]
    calc K * Real.log ((sz.W n : ℕ) : ℝ) ≤ |K| * Real.log ((sz.W n : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right (le_abs_self K) (by linarith)
      _ ≤ Real.sqrt (Real.log ((sz.W n : ℕ) : ℝ)) * Real.log ((sz.W n : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right (Real.abs_le_sqrt h1) (by linarith)
      _ = _ := mul_comm _ _
  set D₁ : ℝ := max ((d : ℝ) + 2 * C₂ / (𝔠 * d) + 1) (1 / 𝔠) with hD₁
  have h1 := baGbyZeta_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 ht1 ε₀ hassm.1 hent ρ (fun _ => 0) D₁
    (fun _ => le_rfl) hsep
  have h2 := (baZetaClaim_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 ht1 ε₀ C₁ C₂ C₃ Cc Φ
    (BAMomentGen_psiAll hd hκ hε h𝔡 hflow ht0 ht1 hassm) hassm.2.2.2.2.2 ε₀ hassm.1 hent ρ hρ0 hρrad D₁ le_rfl).2.1
  have p1 := StochDomAt.precomp_param h1
    (fun n (v : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) =>
      (⟨((v.1, v.2), (STblk sz n v.1, STblk sz n v.2)), by simp [STblk], by simp [STblk]⟩ :
        BAGbyZetaU sz (fun _ => (0 : ℝ)) n))
  have p2 := StochDomAt.precomp_param h2
    (fun n (v : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) => (STblk sz n v.1, STblk sz n v.2))
  exact StochDomAt.trans (Sizes.tendsto_size sz hsz) p1 p2


/-- **The `M`-part of the closing edge** (the support and decay of `M` from `BAMomentGen_decay`, `BAMomentGen_consts`): constants `C' ≥ 2`, `c > 0`
(of `(d, 𝔡, κ)`) such that eventually `M_{xy} = 0` unless the offsets of `x`, `y` agree, and `‖M_{xy}‖ ≤ C' e^{-c |[x]-[y]|}` (`|·|` the `ℓ^∞` block distance,
`zdistInf ≤ zdistD = lwBdist`). -/
private theorem BATermHolds_Mpart : ∃ C' c : ℝ, 2 ≤ C' ∧ 0 < c ∧ ∀ᶠ n in atTop,
    (∀ x y : Idx d (sz.L n) (sz.W n), (split d (sz.L n) (sz.W n) x).2 ≠ (split d (sz.L n) (sz.W n) y).2 →
      (baFMz sz z).M n x y = 0) ∧
    ∀ x y : Idx d (sz.L n) (sz.W n), ‖(baFMz sz z).M n x y‖ ≤
      C' * Real.exp (-(c * ((zdistInf d (sz.L n) (STblk sz n x - STblk sz n y) : ℕ) : ℝ))) := by
  obtain ⟨C, c, Kd, hC1, hc, hKd, hdecay⟩ := BAMomentGen_decay hd hκ hε h𝔡 hflow ht0 ht1 hassm
  refine ⟨max C 2, c, le_max_right _ _, hc, ?_⟩
  filter_upwards [hdecay] with n hdec
  obtain ⟨-, -, hMP, hoff, -⟩ := hdec (fun _ => 0)
  refine ⟨fun x y h => (hoff x y h).1, fun x y => ?_⟩
  refine (hMP x y).1.trans ?_
  have hle : ((zdistInf d (sz.L n) (STblk sz n x - STblk sz n y) : ℕ) : ℝ) ≤ (lwBdist d (sz.L n) (sz.W n) x y : ℝ) := by
    exact_mod_cast zdistInf_le_zdistD d (sz.L n) (STblk sz n x - STblk sz n y)
  refine mul_le_mul (le_max_left _ _) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (le_trans (by norm_num) (le_max_right _ _))
  have := mul_le_mul_of_nonneg_left hle hc.le
  linarith

/-- **`lem:LWterm` reduces to the moment bound** (as `lwReduceB_holds` in `Graph/LWTermHolds.lean`): from
`f_{xy} ≺ η_t⁻¹ Φ(0) Φ(|a-b|)` (`BATermHolds_fB`), (7.2) `eq:directG1` (`BATermHolds_GM_B`), `‖G_{xx}‖ ≤ 2` (`baEntryPsi_holds`), the averaged
local law (`BAMomentGen_avg_whp`) and the pathwise bound `BATermHolds_LWE_le` with the `M`-part of the closing edge
(`BAMomentGen_decay`, `M_{xy} = 0` off equal offsets, `|M_{xy}| ≤ C e^{-c|[x]-[y]|}`). -/
private theorem BATermHolds_reduceB :
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖LWEg (baFMz sz z) n (t n) p.1 p.2 ω‖)
      (fun n p _ => ((baFMz sz z).eta n (t n))⁻¹ * Φ n 0 *
        Φ n ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ^ 2) := by
  classical
  have hadm := hflow.1
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have hsize := Sizes.tendsto_size sz hsz
  have h𝔠 : 0 < 𝔠 := hadm.1
  have hε₀ := hassm.1
  have hcls := hassm.2.2.2.1
  have hrel := hassm.2.2.2.2.1
  have hC₂ : 1 < C₂ := hrel.2.2.1
  have hC₁ : 1 < C₁ := hrel.2.1
  obtain ⟨C', c, hC'2, hc, hMpart⟩ := BATermHolds_Mpart hd hκ hε h𝔡 hflow ht0 ht1 hassm
  obtain ⟨Ee, hEe, hpoly⟩ := BATermHolds_poly_exp (C₂ := C₂) (c := c) (by linarith) hc
  refine BAMomentGen_prec_of_whp sz fun τ hτ => ?_
  have hτ4 : 0 < τ / 4 := by positivity
  set τ₁ : ℝ := min (τ / 4) (𝔠 * ε₀ / 4) with hτ₁def
  have hτ₁ : 0 < τ₁ := lt_min hτ4 (by positivity)
  have hτ₁a : τ₁ ≤ τ / 4 := min_le_left _ _
  have E1 := BAMomentGen_whp_of_prec sz (BATermHolds_fB hd hκ hε h𝔡 hflow ht0 ht1 hassm) hτ4
  have E2 := BAMomentGen_whp_of_prec sz (BATermHolds_GM_B hd hκ hε h𝔡 hflow ht0 ht1 hassm) hτ4
  have E3 := BAMomentGen_entry_whp hd hκ hε h𝔡 hflow ht0 ht1 hassm hτ₁
  have E4 := BAMomentGen_avg_whp hd hκ hε h𝔡 hflow ht0 ht1 hassm hτ₁
  refine ⟨_, HighProbAt.inter hsize (HighProbAt.inter hsize (HighProbAt.inter hsize E1 E2) E3) E4, ?_⟩
  set M : ℝ := max 1 C₃ with hMdef
  set c3 : ℝ := C₃ ^ 2 with hc3def
  set c3' : ℝ := M ^ 2 with hc3'def
  set Kz : ℝ := C' * (Cc 2 * C₁) * Ee with hKzdef
  set K0 : ℝ := (1 + 4 * c3') + c3 * (1 + Kz) + 8 * c3 * c3' * (1 + Kz ^ 2) with hK0def
  have hK : ∀ᶠ n in atTop, 2 * K0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 4) :=
    ((tendsto_rpow_atTop hτ4).comp hsz).eventually_ge_atTop _
  filter_upwards [hcls.1, lwMoment_phi_facts hcls hrel, BAMomentGen_Psi'_facts hd hκ hε h𝔡 hflow ht0 ht1 hassm,
    BAMomentGen_Psi_facts hd hκ hε h𝔡 hflow ht0 ht1 hassm hτ₁.le (min_le_right _ _), hMpart, hcls.2.2, hK,
    hsize.eventually (eventually_ge_atTop 1)] with n hcl1 hph hPs' hPsi hMp hwin hKn hN1
  intro ω hω u
  obtain ⟨⟨⟨hf, hgm⟩, hent⟩, havg⟩ := hω
  have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  set X : ℝ := ((sz.size n : ℕ) : ℝ) ^ (τ / 4) with hXdef
  have hX1 : 1 ≤ X := Real.one_le_rpow hN1' hτ4.le
  obtain ⟨hη0, hη1, -⟩ := BAMomentGen_eta_facts hd hκ hε h𝔡 hflow ht0 ht1 hassm n
  have hI : 1 ≤ ((baFMz sz z).eta n (t n))⁻¹ := one_le_inv_iff₀.2 ⟨hη0, hη1⟩
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.one_le_cast.2 (sz.W_pos n)
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hP0 : 0 < Φ n 0 := (hcl1 0 le_rfl).1
  have hP01 : Φ n 0 ≤ 1 :=
    (hcl1 0 le_rfl).2.trans (Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith))
  obtain ⟨hCc, hP, hcmp, -⟩ := hph
  have hΦnn : ∀ r : ℕ, 0 < Φ n (r : ℝ) := fun r => hP r (Nat.cast_nonneg _)
  have hWd : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ c3 * Φ n 0 ^ 2 := by
    have e : (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) ^ 2 = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hWpos.le, show -(d : ℝ) / 2 * ((2 : ℕ) : ℝ) = -(d : ℝ) by push_cast; ring,
        Real.rpow_neg hWpos.le, Real.rpow_natCast]
    rw [← e]
    calc _ ≤ (C₃ * Φ n 0) ^ 2 := pow_le_pow_left₀ (Real.rpow_nonneg hWpos.le _) hwin 2
      _ = _ := by rw [hc3def]; ring
  obtain ⟨-, hPsiW, -, hPsiC⟩ := hPs'
  have hΨ0 : 0 ≤ BAMomentGen_Psi' sz Φ n := (Real.rpow_nonneg hWpos.le _).trans hPsiW
  have hΨ2 : BAMomentGen_Psi' sz Φ n ^ 2 ≤ c3' * Φ n 0 ^ 2 := by
    rw [hc3'def, ← mul_pow]; exact pow_le_pow_left₀ hΨ0 hPsiC 2
  -- the diagonal
  obtain ⟨-, -, hPsi3⟩ := hPsi
  have hΨ1 : M * ((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0 ≤ 1 :=
    hPsi3.trans (Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith [hε₀]))
  obtain ⟨-, -, -, -, -, hMle⟩ := ba_G_data hκ sz hflow n (ht0 n) (ht1 n)
  have hGA : ∀ v, ‖(baFMz sz z).G n (t n) ω v v‖ ≤ 2 := by
    intro v
    have h1 : ‖(baFMz sz z).GM n (t n) ω v v‖ ≤ 1 := by
      refine (hent (v, v)).trans ?_
      calc ((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0 = 1 * (((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0) := (one_mul _).symm
        _ ≤ M * (((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ = M * ((sz.size n : ℕ) : ℝ) ^ τ₁ * Φ n 0 := by ring
        _ ≤ 1 := hΨ1
    have h3 : (baFMz sz z).G n (t n) ω v v = (baFMz sz z).GM n (t n) ω v v + (baFMz sz z).M n v v := by
      unfold FlowFM.GM; ring
    rw [h3]
    exact (norm_add_le _ _).trans (by have := hMle v v; change ‖(baFMz sz z).M n v v‖ ≤ 1 at this; linarith)
  -- the averages
  have hXτ : ((sz.size n : ℕ) : ℝ) ^ τ₁ ≤ X := Real.rpow_le_rpow_of_exponent_le hN1' hτ₁a
  have hμ : ∀ b : Zd d (sz.L n), ‖(baFMz sz z).L n (t n) (fun _ : Fin 1 => true) (fun _ => b) ω - (baFMz sz z).m n‖ ≤
      X * BAMomentGen_Psi' sz Φ n ^ 2 := fun b =>
    (havg b).trans (mul_le_mul_of_nonneg_right hXτ (sq_nonneg _))
  -- the `M`-part
  obtain ⟨hM0, hM⟩ := hMp
  set Mb : ℕ → ℝ := fun r => C' * Real.exp (-(c * (r : ℝ))) with hMbdef
  have hMb0 : ∀ r, 0 ≤ Mb r := fun r => by positivity
  have hAM : (2 : ℝ) ≤ Mb 0 := by simpa [hMbdef] using hC'2
  have hKz0 : 0 ≤ Kz := by rw [hKzdef]; have := hC₁; positivity
  have hKzP : ∀ r : ℕ, Φ n 0 * Mb r ≤ Kz * Φ n (r : ℝ) := by
    intro r
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
    have h1 := hcmp r hr0
    have h2 := hpoly r hr0
    have hPr := hΦnn r
    calc Φ n 0 * Mb r ≤ (Cc 2 * C₁ * (max 1 (r : ℝ)) ^ C₂ * Φ n r) * (C' * Real.exp (-(c * (r : ℝ)))) :=
          mul_le_mul_of_nonneg_right h1 (hMb0 r)
      _ = (C' * (Cc 2 * C₁) * Φ n r) * ((max 1 (r : ℝ)) ^ C₂ * Real.exp (-(c * (r : ℝ)))) := by ring
      _ ≤ (C' * (Cc 2 * C₁) * Φ n r) * Ee := mul_le_mul_of_nonneg_left h2 (by have := hC₁; positivity)
      _ = Kz * Φ n r := by rw [hKzdef]; ring
  -- the pathwise bound
  have hSelf := (BAflow_real κ ε 𝔠 𝔡 sz z hflow n).1
  have hLWE := BATermHolds_LWE_le n (t n) ω hSelf u.1 u.2 (A := 2) (μ := X * BAMomentGen_Psi' sz Φ n ^ 2)
    (γ := fun r : ℕ => X * Φ n (r : ℝ)) (φ := fun r : ℕ => X * (((baFMz sz z).eta n (t n))⁻¹ * Φ n 0 * Φ n (r : ℝ)))
    (Mb := Mb) (by positivity) (by norm_num) (fun r => by have := hΦnn r; positivity)
    (fun r => by have := hΦnn r; positivity) hMb0 hAM hμ hGA (fun x y => hgm (x, y)) hM0 hM (fun x y => hf (x, y))
  set r : ℕ := zdistInf d (sz.L n) (u.2 0 - u.2 1) with hr
  have hbd := BATermHolds_arithB (X := X) (I := ((baFMz sz z).eta n (t n))⁻¹) (P0 := Φ n 0) (Pr := Φ n (r : ℝ))
    (Wd := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) (μ := X * BAMomentGen_Psi' sz Φ n ^ 2) (m := Mb r) (c3 := c3) (c3' := c3')
    (Kz := Kz) hX1 hI hP0 hP01 (hΦnn r) (by positivity) hWd (by positivity) (by positivity) (by positivity)
    (mul_le_mul_of_nonneg_left hΨ2 (by linarith)) (hMb0 r) hKz0 (hKzP r)
  have hN : ((sz.size n : ℕ) : ℝ) ^ τ = X ^ 3 * X := by
    rw [hXdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
    congr 1; push_cast; ring
  have hζ : 0 ≤ ((baFMz sz z).eta n (t n))⁻¹ * Φ n 0 * Φ n (r : ℝ) ^ 2 := by
    have := hΦnn r; positivity
  calc ‖LWEg (baFMz sz z) n (t n) u.1 u.2 ω‖ ≤ _ := hLWE
    _ ≤ (2 * K0) * (X ^ 3 * (((baFMz sz z).eta n (t n))⁻¹ * Φ n 0 * Φ n (r : ℝ) ^ 2)) := hbd
    _ ≤ X * (X ^ 3 * (((baFMz sz z).eta n (t n))⁻¹ * Φ n 0 * Φ n (r : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_right hKn (by positivity)
    _ = _ := by rw [hN]; ring

end BSide


/-- **`lem:LWterm` at the block Anderson data** (Lemma 3.10; Section 7): `BATermHolds_reduceB` with its hypothesis `LWAssmgL`
unfolded, for every `d` and no hypothesis on the model. -/
theorem baLWterm_holds : ∀ d : ℕ, BALWterm d := by
  intro d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 ht1 ε₀ C₁ C₂ C₃ Cc Ψ Φ hassm
  exact BATermHolds_reduceB hd hκ hε h𝔡 hflow ht0 ht1 hassm

/-! ## 3. The regime `1 - t ≤ λ²/L²` of `lem: EWGn2_N` -/

/-- **`lem: EWGn2_N` on the sizes where `1 - t ≤ λ²/L²`** (Lemma 3.11, (7.1) `eq:EGC`; `LWtermExpN`, `Graph/LWPins.lean`) at the block Anderson data: the same
conclusion as `BALWtermExp` (`BA/LWPinsBA.lean`) on the index set of the regime.  The statement def; the union with the other regime
is `baLWtermExp_holds`. -/
def BALWtermExpN (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExpgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ ℓ →
          ∀ D : ℝ, 0 < D →
            PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) //
                1 - t n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2})
              (fun n p ω => ‖LWEg (baFMz sz z) n (t n) p.1.1 p.1.2 ω‖)
              (fun n p _ => ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
                ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n)
                  ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ)))

/-- `W^{-d}` as the rpow of `LWPhiB` equals the natural-power inverse of `Bctl` (as the private `lwN_wneg` in `Graph/LWTermExpN.lean`). -/
private theorem BATermHolds_wneg (W : ℝ) (hW : 0 ≤ W) (d : ℕ) : W ^ (-(d : ℝ)) = (W ^ d)⁻¹ := by
  rw [Real.rpow_neg hW, Real.rpow_natCast]

/-- `Φ_n(0) = Bctl^{1/2}` for the B class with `c₀ = d` (as the private `lwN_phi_zero` in `Graph/LWTermExpN.lean`). -/
private theorem BATermHolds_phi_zero {d : ℕ} (sz : Sizes d) (K : ℕ → ℕ) (t : ℕ → ℝ) (n : ℕ) :
    LWPhiB sz (d : ℝ) K t n 0 = (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) := by
  unfold LWPhiB Sizes.Bctl
  rw [BATermHolds_wneg _ (Nat.cast_nonneg _)]
  simp

/-- `Φ_n(r)² = W^{-d} B_{t, r∧K}` for the B class with `c₀ = d`, `r ∈ ℕ` (as the private `lwN_phi_sq` in `Graph/LWTermExpN.lean`). -/
private theorem BATermHolds_phi_sq {d : ℕ} (sz : Sizes d) (K : ℕ → ℕ) (t : ℕ → ℝ) (n r : ℕ) :
    LWPhiB sz (d : ℝ) K t n (r : ℝ) ^ 2 =
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) (t n) (min r (K n)) := by
  unfold LWPhiB
  rw [BATermHolds_wneg _ (Nat.cast_nonneg _), Nat.floor_natCast, ← Real.sqrt_eq_rpow, Real.sq_sqrt]
  refine mul_nonneg (inv_nonneg.mpr (by positivity)) ?_
  unfold Bparam
  positivity

private theorem BATermHolds_zdistInf_le (L : ℕ) [NeZero L] (x : Zd d L) : zdistInf d L x ≤ L := by
  refine Finset.sup_le fun i _ => ?_
  unfold zdist
  exact (min_le_left _ _).trans (ZMod.val_lt _).le

/-- **`lem: EWGn2_N`, second regime (`1 - t ≤ λ²/L²`), from `lem:LWterm`** (Lemma 3.11; as `lwtermExpN_of_LWterm` in `Graph/LWTermExpN.lean`): `baLWterm_holds` is applied to the B class `Φ = LWPhiB sz d K t`, `K n = ⌊ℓ_n⌋ ∧ L_n`, at the window
`ε₁ = min(ε₀, d c₀/4)` with `c₀` of `BAExp14d_Bctl_small` (`Bctl ≤ 2 N^{-c₀}`); `LWLoop2gL` for `Φ` is (3.31) `eq:LW_assm_exp` at `D' = 1/𝔠`
(`wT ≤ B_{r∧K}`, `W^{-D'} ≤ L^{-d}`); the conclusion is compared with `tailW` on the regime with the constant `e · 2^{d-2}` (`ℓ_t = L`). -/
theorem baLWtermExpN_holds : ∀ d : ℕ, BALWtermExpN d := by
  intro d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ Ψ ℓ hA D hD
  obtain ⟨hε₀, hwin, hinit, hℓ0, hℓt, hloop⟩ := hA
  have hd2 : 2 ≤ d := by omega
  have hadm := hflow.1
  have h𝔠 : 0 < 𝔠 := hadm.1
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have hband : sz.Bandwidth 𝔠 := hadm.2.2.2.1
  have hWO : sz.WO 𝔡 := hadm.2.2.2.2
  have hsize := Sizes.tendsto_size sz hsz
  have ht1 : ∀ n, t n < 1 := fun n => (ba_G_data hκ sz hflow n (ht0 n) (htT n)).1
  obtain ⟨c₀, hc₀, hBs⟩ := BAExp14d_Bctl_small d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨ε₁, hε₁def⟩ : ∃ ε₁ : ℝ, ε₁ = min ε₀ ((d : ℝ) * c₀ / 4) := ⟨_, rfl⟩
  have hε₁pos : 0 < ε₁ := by rw [hε₁def]; exact lt_min hε₀ (by positivity)
  have hε₁a : ε₁ ≤ ε₀ := by rw [hε₁def]; exact min_le_left _ _
  have hε₁b : 2 * ε₁ ≤ (d : ℝ) * c₀ / 2 := by
    have : ε₁ ≤ (d : ℝ) * c₀ / 4 := by rw [hε₁def]; exact min_le_right _ _
    linarith
  have hW1 : ∀ n, (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := fun n => Nat.one_le_cast.2 (sz.W_pos n)
  have hWpos : ∀ n, (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := fun n => lt_of_lt_of_le one_pos (hW1 n)
  have hL1 : ∀ n, (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := fun n =>
    Nat.one_le_cast.2 (by have := sz.three_le_L n; omega)
  -- data conditions of `LWPhiB_psiAll`
  have hg : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
    filter_upwards [hWO] with n hn
    exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos (hWpos n) _) hn.1, hn.2⟩
  have ht : ∀ᶠ n in atTop, 0 ≤ t n ∧ t n ≤ 1 := Eventually.of_forall fun n => ⟨ht0 n, (ht1 n).le⟩
  have hup : ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ)) * Bparam d (sz.L n) (sz.lam n) (t n) 0 ≤
      ((sz.W n : ℕ) : ℝ) ^ (-2 * ε₁) := by
    filter_upwards [hBs t ht0 htT, (BATermHolds_W_tendsto hadm).eventually
      ((tendsto_rpow_atTop (by positivity : 0 < (d : ℝ) * c₀ / 2)).eventually_ge_atTop 2)] with n hn hW2
    have h1 : sz.Bctl n (t n) ≤ 2 * ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c₀)) :=
      hn.trans (mul_le_mul_of_nonneg_left (Sizes.lwN_size_rpow_neg_le sz n hc₀.le) zero_le_two)
    set a : ℝ := ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c₀ / 2)) with ha
    have ha0 : 0 < a := Real.rpow_pos_of_pos (hWpos n) _
    have haa : ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c₀)) = a * a := by
      rw [ha, ← Real.rpow_add (hWpos n)]; congr 1; ring
    have ha2 : 2 * a ≤ 1 := by
      have : a * ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) * c₀ / 2) = 1 := by
        rw [ha, ← Real.rpow_add (hWpos n)]; simp
      nlinarith
    have h3 : a ≤ ((sz.W n : ℕ) : ℝ) ^ (-2 * ε₁) :=
      Real.rpow_le_rpow_of_exponent_le (hW1 n) (by linarith)
    rw [BATermHolds_wneg _ (Nat.cast_nonneg _)]
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) (t n) 0 = sz.Bctl n (t n) := rfl
      _ ≤ 2 * (a * a) := by rw [← haa]; exact h1
      _ ≤ 1 * a := by nlinarith
      _ ≤ _ := by rw [one_mul]; exact h3
  set K : ℕ → ℕ := fun n => min ⌊ℓ n⌋₊ (sz.L n) with hKdef
  obtain ⟨-, hcls, hrel⟩ := LWPhiB_psiAll sz hd2 (ε₀ := ε₁) (c₀ := (d : ℝ)) K t hε₁pos le_rfl hg ht hup
  -- the window and `(initialGT2)` at `ε₁ ≤ ε₀`
  have hwin' : LWWindow sz ε₁ Ψ := by
    filter_upwards [hwin] with n hn
    exact ⟨hn.1, hn.2.trans (Real.rpow_le_rpow_of_exponent_le (hW1 n) (by linarith))⟩
  have hinit' : STInitialGT2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₁ Ψ := by
    refine ⟨?_, hinit.2⟩
    refine lwN_prec_mono hsize (c := 1) ?_ hinit.1
    exact Eventually.of_forall fun n u ω => ⟨Real.rpow_nonneg (Nat.cast_nonneg _) _,
      by rw [one_mul]; exact Real.rpow_le_rpow_of_exponent_le (hW1 n) (by linarith)⟩
  -- `LWLoop2gL` for the B class from `(LW_assm_exp)` at `D' = 1/𝔠`
  have hD' : 0 < 1 / 𝔠 := by positivity
  have hL2 : LWLoop2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t (LWPhiB sz (d : ℝ) K t) := by
    refine lwN_prec_mono hsize (c := 1) ?_ (hloop (1 / 𝔠) hD')
    filter_upwards [Sizes.lwN_Wneg_le sz h𝔠 hband] with n hn
    rintro ⟨σ, a, b⟩ ω
    simp only
    have hLn : (zdistInf d (sz.L n) (a - b) : ℕ) ≤ sz.L n := BATermHolds_zdistInf_le _ _
    rw [BATermHolds_phi_sq, one_mul]
    refine ⟨mul_nonneg (inv_nonneg.mpr (by positivity)) ?_, ?_⟩
    · unfold Bparam; positivity
    · refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (by positivity))
      exact lwN_tailW_le (L := sz.L n) _ hLn (by have := sz.three_le_L n; omega) rfl (hℓ0 n) (ht0 n) (ht1 n) hn
  have hmain := baLWterm_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₁ _ _ _ _ Ψ (LWPhiB sz (d : ℝ) K t)
    ⟨hε₁pos, hwin', hinit', hcls, hrel, hL2⟩
  -- restrict to the regime subtype and compare
  have h1 := StochDomAt.precomp_param hmain
    (fun n (v : {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) //
      1 - t n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2}) => v.1)
  refine lwN_prec_mono hsize (c := Real.exp 1 * 2 ^ (d - 2)) ?_ h1
  filter_upwards [hg] with n hgn
  rintro ⟨⟨σ, a⟩, hreg⟩ ω
  simp only
  have hLn : (zdistInf d (sz.L n) (a 0 - a 1) : ℕ) ≤ sz.L n := BATermHolds_zdistInf_le _ _
  have hη : 0 ≤ ((baFMz sz z).eta n (t n))⁻¹ :=
    inv_nonneg.mpr (BAExp14a_eta_pos hκ hflow n (ht0 n) (htT n)).le
  have hS : 0 ≤ (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by
    unfold Sizes.Bctl Bparam; positivity) _
  have hTW : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n)
      ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) :=
    mul_nonneg (inv_nonneg.mpr (by positivity)) (tailW_pos (hWpos n) _).le
  refine ⟨mul_nonneg (mul_nonneg hη hS) hTW, ?_⟩
  rw [BATermHolds_phi_zero, BATermHolds_phi_sq]
  have hB := lwN_B_le_tail (d := d) (L := sz.L n) (W := ((sz.W n : ℕ) : ℝ)) (D := D)
    (zdistInf d (sz.L n) (a 0 - a 1)) hLn rfl (hℓ0 n) hgn.1.le (ht1 n) (hL1 n) hreg
  calc ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
        ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) (t n)
          (min (zdistInf d (sz.L n) (a 0 - a 1)) (K n)))
      ≤ ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
        ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((Real.exp 1 * 2 ^ (d - 2)) *
          tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) D
            ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB (inv_nonneg.mpr (by positivity)))
          (mul_nonneg hη hS)
    _ = (Real.exp 1 * 2 ^ (d - 2)) * (((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
        ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n)
          ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ))) := by ring


end RBM.BA

end
