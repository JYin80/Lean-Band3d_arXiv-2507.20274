/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.TwistGrid2
import RBM3D.BA.GreenCond2
import RBM3D.BA.EMn2BA
import RBM3D.Path.DifREP2
import RBM3D.Induction.StepDecompN
import RBM3D.Path.QVIdentity
import RBM3D.Kernel.Evolution

/-!
# BA stage TL, row TL2a4 (T2439), part 1: the `Ũ`-weighted martingale tail (clause (iv) of 4 (b))

Ticket `docs/tickets/T2439.md`; paper arXiv:2507.20274; proofs `docs/tickets/T2398-TL-proofs.md` (D.5).  Twin of
`Path/DifREP3.lean` (`gridRepWTailN_holds`, route `:20-45`) with the one-slot kernel `Ũ = twU = BAuKer` in place of
`UN`/`uKerQ` and no zero-mode projection.  This file: the kernel facts of `Ũ` (conjugation `Ũ^{(σ̄)} = conj Ũ^{(σ)}`,
row sums, transfer), the entrywise algebra of the gradient `twDerM` (crude bound, shift in `u`), the twisted observable
`Φ_b(M) = L̃_u(g₀Ψ + M)` as a Hermitian test function with the second-derivative bound `6 η⁻⁴`, its directional
derivative `Σ_{xy} twDerM_{xy} X_{xy}`, the variance identity `Σ_c gvar_c |⟨∂Φ, X_c⟩|² = Σ_{xy} S_{xy} |∂_{xy}Φ|²`, the
frozen conditional mgf, and the weighted Doob tail of the second-order part.  The second part is
`RBM3D/BA/TwistGridWTail2.lean`.

Every statement is for every `d` (no `3 ≤ d`).  Every helper is `private` or carries the stem `TwistGridWTail_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-! ## 1. The kernel `Ũ`: conjugation, row sums, transfer -/

section Kernel

variable {d L : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ}

/-- `M^{(σ̄)} = conj M^{(σ)}` entrywise (`BAMB` symmetric: `M(−) = (M^{(B)})^*`). -/
private theorem TwistGridWTail_BAMss_conj (σ₁ σ₂ : Bool) (a b : Zd d L) :
    BAMss d L (BAMB d L g (E : ℂ) m) (!σ₁) (!σ₂) a b = starRingEnd ℂ (BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ a b) := by
  have h : ∀ x y, BAMB d L g (E : ℂ) m x y = BAMB d L g (E : ℂ) m y x := fun x y => BAMB_symm d L g (E : ℂ) m x y
  cases σ₁ <;> cases σ₂ <;> simp [BAMss, BAMsigma, Matrix.conjTranspose_apply, h a b, map_mul]

/-- A left inverse of a unit is its `Ring.inverse` (twin of the private `BAKBase_eq_inverse`, `BA/KBase.lean:176`). -/
private theorem TwistGridWTail_eq_inverse {x y : Matrix (Zd d L) (Zd d L) ℂ} (hx : IsUnit x) (h : y * x = 1) :
    y = Ring.inverse x := by
  calc y = y * (x * Ring.inverse x) := by rw [Ring.mul_inverse_cancel x hx, mul_one]
    _ = (y * x) * Ring.inverse x := (mul_assoc _ _ _).symm
    _ = Ring.inverse x := by rw [h, one_mul]

/-- `Θ^{(σ̄)}_t = conj Θ^{(σ)}_t` as matrices, `0 ≤ t < 1` (`Θ = (1 − tM)⁻¹`, `M^{(σ̄)} = conj M^{(σ)}`). -/
private theorem TwistGridWTail_BATheta_conj (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (σ₁ σ₂ : Bool) :
    BATheta d L g E m t (!σ₁) (!σ₂) = (starRingEnd ℂ).mapMatrix (BATheta d L g E m t σ₁ σ₂) := by
  set φ : Matrix (Zd d L) (Zd d L) ℂ →+* Matrix (Zd d L) (Zd d L) ℂ := (starRingEnd ℂ).mapMatrix with hφ
  have hx : 1 - (t : ℂ) • BAMss d L (BAMB d L g (E : ℂ) m) (!σ₁) (!σ₂) =
      φ (1 - (t : ℂ) • BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) := by
    ext i j
    simp only [hφ, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, map_sub, map_mul, Complex.conj_ofReal, TwistGridWTail_BAMss_conj]
    split_ifs <;> simp
  have hu := BATheta_isUnit d L g κ E m hr t ht0 ht1 σ₁ σ₂
  have hmul : BATheta d L g E m t σ₁ σ₂ * (1 - (t : ℂ) • BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) = 1 :=
    Ring.inverse_mul_cancel _ hu
  unfold BATheta PropThetaQ
  rw [hx]
  have hu' := hu.map φ
  have h1 : φ (BATheta d L g E m t σ₁ σ₂) * φ (1 - (t : ℂ) • BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) = 1 := by
    rw [← map_mul, hmul, map_one]
  exact (TwistGridWTail_eq_inverse hu' h1).symm

/-- **Conjugation of the kernel**: `Ũ^{(σ̄)}_{v,w} = conj Ũ^{(σ)}_{v,w}` entrywise, `0 ≤ w < 1` (`BAReal`; `Ũ = (1 − vM)Θ_w`). -/
theorem TwistGridWTail_twU_conj {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) {κ : ℝ}
    (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (σ : Fin 2 → Bool) (v : ℝ) {w : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w < 1) (a b : Zd d (sz.L n)) :
    twU sz lam0 E n (fun i => !σ i) v w a b = starRingEnd ℂ (twU sz lam0 E n σ v w a b) := by
  have hΘ := TwistGridWTail_BATheta_conj hr hw0 hw1 (σ 0) (σ 1)
  have hX : (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) - (v : ℂ) • BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (!σ 0) (!σ 1) =
      (starRingEnd ℂ).mapMatrix (1 - (v : ℂ) • BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) (σ 1)) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, map_sub, map_mul, Complex.conj_ofReal, TwistGridWTail_BAMss_conj]
    split_ifs <;> simp
  have : twU sz lam0 E n (fun i => !σ i) v w =
      (starRingEnd ℂ).mapMatrix (twU sz lam0 E n σ v w) := by
    unfold twU BAuKer
    show (1 - (v : ℂ) • BAMss _ _ _ (!σ 0) (!σ 1)) * BATheta _ _ _ _ _ _ (!σ 0) (!σ 1) = _
    rw [hX, hΘ, map_mul]
  have := congrFun (congrFun this a) b
  simpa using this

open scoped Matrix.Norms.Operator in
/-- Row sums of `Ũ_{v,w}`: `Σ_b |Ũ_{v,w}(a,b)| ≤ (1 − v)/(1 − w)` for `0 ≤ v ≤ w < 1` (`EKPins_norm_uKer_le`). -/
theorem TwistGridWTail_sum_norm_twU_le {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) {κ : ℝ}
    (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (σ : Fin 2 → Bool) {v w : ℝ}
    (hv : 0 ≤ v) (hvw : v ≤ w) (hw : w < 1) (a : Zd d (sz.L n)) :
    ∑ b, ‖twU sz lam0 E n σ v w a b‖ ≤ (1 - v) / (1 - w) :=
  (sum_norm_row_le _ a).trans (EKPins_norm_uKer_le hr hv hvw hw (σ 0) (σ 1))

open scoped Matrix.Norms.Operator in
/-- `‖Ũ_{w,v} − 1‖ ≤ |v − w| (1 − v)⁻¹` for `0 ≤ v < 1` (`BAuKer_eq_one_add`, `EKPins_norm_Q_le`, `EKPins_norm_Theta_le`); no order between `v` and `w`. -/
theorem TwistGridWTail_norm_twU_sub_one_le {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) {κ : ℝ}
    (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (σ : Fin 2 → Bool) (w : ℝ) {v : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) :
    ‖twU sz lam0 E n σ w v - 1‖ ≤ |v - w| * (1 - v)⁻¹ := by
  have h := BAuKer_eq_one_add hr (s := w) hv0 hv1 (σ 0) (σ 1)
  have e : twU sz lam0 E n σ w v - 1 = ((v : ℂ) - w) • (BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) (σ 1) *
      BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) v (σ 0) (σ 1)) := by
    unfold twU; rw [h]; abel
  rw [e]
  have hc : ‖((v : ℂ) - w)‖ = |v - w| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  refine (norm_smul_le _ _).trans ?_
  rw [hc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine (norm_mul_le _ _).trans ?_
  have h1 := EKPins_norm_Q_le hr (σ 0) (σ 1)
  have h2 := EKPins_norm_Theta_le hr hv0 hv1 (σ 0) (σ 1)
  calc _ ≤ 1 * (1 - v)⁻¹ := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

end Kernel


/-! ## 2. The gradient `twDerM` at the entry level: crude bound and the shift in `u` -/

section Entry

variable {d : ℕ} {sz : Sizes d} (n : ℕ)

/-- `∂_{xy} L̃_b` of (D.2) as a function of the two charged resolvent entry arrays `G₁ = G(σ₁)`, `G₂ = G(σ₂)`
(`twDerM` is this at `twChg (twGM ..)`, by `rfl`: `TwistGridWTail_twDerM_eq`). -/
def TwistGridWTail_der (G₁ G₂ : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) (b c₁ c₂ : Zd d (sz.L n))
    (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  -((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * (∑ z ∈ twBlk n b, ∑ w ∈ twBlk n c₁, G₁ y z * G₂ z w * G₁ (twShift n c₂ w) x +
    ∑ w ∈ twBlk n c₁, ∑ z ∈ twBlk n b, G₂ y w * G₁ (twShift n c₂ w) z * G₂ z x)

theorem TwistGridWTail_twDerM_eq (lam0 E : ℕ → ℝ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (b c₁ c₂ : Zd d (sz.L n)) (x y : Idx d (sz.L n) (sz.W n)) :
    twDerM sz lam0 E n u H σ b c₁ c₂ x y =
      TwistGridWTail_der n (twChg (twGM sz lam0 E n u H) (σ 0)) (twChg (twGM sz lam0 E n u H) (σ 1)) b c₁ c₂ x y := rfl

private theorem TwistGridWTail_card_blk (a : Zd d (sz.L n)) : ((twBlk n a).card : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d := by
  have : (twBlk n a).card = (sz.W n) ^ d := card_Iblk d (sz.L n) (sz.W n) a
  rw [this]; push_cast; rfl

private theorem TwistGridWTail_norm_sum_sum_le {α β : Type*} (s : Finset α) (t : Finset β) (f : α → β → ℂ) {M : ℝ}
    (h : ∀ z ∈ s, ∀ w ∈ t, ‖f z w‖ ≤ M) : ‖∑ z ∈ s, ∑ w ∈ t, f z w‖ ≤ (s.card : ℝ) * (t.card : ℝ) * M := by
  calc ‖∑ z ∈ s, ∑ w ∈ t, f z w‖ ≤ ∑ z ∈ s, ‖∑ w ∈ t, f z w‖ := norm_sum_le _ _
    _ ≤ ∑ z ∈ s, (t.card : ℝ) * M := Finset.sum_le_sum fun z hz =>
        (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul t _ M (h z hz)).trans (by rw [nsmul_eq_mul]))
    _ = (s.card : ℝ) * (t.card : ℝ) * M := by rw [Finset.sum_const, nsmul_eq_mul]; ring

private theorem TwistGridWTail_tri {a b c a' b' c' : ℂ} {R δ : ℝ} (hR : 0 ≤ R) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) (hc : ‖c‖ ≤ R)
    (ha' : ‖a'‖ ≤ R) (hb' : ‖b'‖ ≤ R) (hc' : ‖c'‖ ≤ R) (hda : ‖a - a'‖ ≤ δ) (hdb : ‖b - b'‖ ≤ δ) (hdc : ‖c - c'‖ ≤ δ) :
    ‖a * b * c - a' * b' * c'‖ ≤ 3 * R ^ 2 * δ := by
  have e : a * b * c - a' * b' * c' = (a - a') * b * c + a' * (b - b') * c + a' * b' * (c - c') := by ring
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hda
  rw [e]
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  simp only [norm_mul]
  have h1 : ‖a - a'‖ * ‖b‖ * ‖c‖ ≤ δ * R * R := by gcongr
  have h2 : ‖a'‖ * ‖b - b'‖ * ‖c‖ ≤ R * δ * R := by gcongr
  have h3 : ‖a'‖ * ‖b'‖ * ‖c - c'‖ ≤ R * R * δ := by gcongr
  nlinarith

private theorem TwistGridWTail_wd_sq (n : ℕ) :
    ‖((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2‖ * (((sz.W n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ d) = 1 := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  rw [norm_pow, norm_inv, norm_pow, Complex.norm_natCast]
  field_simp

/-- **Crude bound of the gradient**: entries of `G₁`, `G₂` at most `R` give `|∂_{xy} L̃| ≤ 2 R³`
(`W^{-2d}` against the `W^{2d}` terms of each sum). -/
theorem TwistGridWTail_der_norm_le {G₁ G₂ : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (h₁ : ∀ x y, ‖G₁ x y‖ ≤ R) (h₂ : ∀ x y, ‖G₂ x y‖ ≤ R) (b c₁ c₂ : Zd d (sz.L n)) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖TwistGridWTail_der n G₁ G₂ b c₁ c₂ x y‖ ≤ 2 * R ^ 3 := by
  unfold TwistGridWTail_der
  rw [norm_mul, norm_neg]
  have hS1 : ‖∑ z ∈ twBlk n b, ∑ w ∈ twBlk n c₁, G₁ y z * G₂ z w * G₁ (twShift n c₂ w) x‖ ≤
      ((twBlk n b).card : ℝ) * ((twBlk n c₁).card : ℝ) * R ^ 3 :=
    TwistGridWTail_norm_sum_sum_le _ _ _ fun z _ w _ => by
      rw [norm_mul, norm_mul]
      calc ‖G₁ y z‖ * ‖G₂ z w‖ * ‖G₁ (twShift n c₂ w) x‖ ≤ R * R * R := by
            gcongr
            · exact h₁ _ _
            · exact h₂ _ _
            · exact h₁ _ _
        _ = R ^ 3 := by ring
  have hS2 : ‖∑ w ∈ twBlk n c₁, ∑ z ∈ twBlk n b, G₂ y w * G₁ (twShift n c₂ w) z * G₂ z x‖ ≤
      ((twBlk n c₁).card : ℝ) * ((twBlk n b).card : ℝ) * R ^ 3 :=
    TwistGridWTail_norm_sum_sum_le _ _ _ fun w _ z _ => by
      rw [norm_mul, norm_mul]
      calc ‖G₂ y w‖ * ‖G₁ (twShift n c₂ w) z‖ * ‖G₂ z x‖ ≤ R * R * R := by
            gcongr
            · exact h₂ _ _
            · exact h₁ _ _
            · exact h₂ _ _
        _ = R ^ 3 := by ring
  rw [TwistGridWTail_card_blk, TwistGridWTail_card_blk] at hS1 hS2
  have hwd := TwistGridWTail_wd_sq (sz := sz) (d := d) n
  calc ‖((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2‖ * ‖_ + _‖ ≤ ‖((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2‖ *
        (((sz.W n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ d * R ^ 3 + ((sz.W n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ d * R ^ 3) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hS1 hS2)) (norm_nonneg _)
    _ = 2 * R ^ 3 := by
        have : ‖((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2‖ * (((sz.W n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ d) * (2 * R ^ 3) = 2 * R ^ 3 := by
          rw [hwd, one_mul]
        linarith [this]

/-- **The shift of the gradient**: entries of `G_i, G'_i` at most `R` and `|G_i − G'_i| ≤ δ` entrywise give
`|∂_{xy}L̃[G] − ∂_{xy}L̃[G']| ≤ 6 R² δ`. -/
theorem TwistGridWTail_der_sub_le {G₁ G₂ G₁' G₂' : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ} {R δ : ℝ} (hR : 0 ≤ R)
    (h₁ : ∀ x y, ‖G₁ x y‖ ≤ R) (h₂ : ∀ x y, ‖G₂ x y‖ ≤ R) (h₁' : ∀ x y, ‖G₁' x y‖ ≤ R) (h₂' : ∀ x y, ‖G₂' x y‖ ≤ R)
    (d₁ : ∀ x y, ‖G₁ x y - G₁' x y‖ ≤ δ) (d₂ : ∀ x y, ‖G₂ x y - G₂' x y‖ ≤ δ) (b c₁ c₂ : Zd d (sz.L n))
    (x y : Idx d (sz.L n) (sz.W n)) :
    ‖TwistGridWTail_der n G₁ G₂ b c₁ c₂ x y - TwistGridWTail_der n G₁' G₂' b c₁ c₂ x y‖ ≤ 6 * R ^ 2 * δ := by
  unfold TwistGridWTail_der
  rw [← mul_sub, norm_mul, norm_neg]
  have hS1 : ‖∑ z ∈ twBlk n b, ∑ w ∈ twBlk n c₁, G₁ y z * G₂ z w * G₁ (twShift n c₂ w) x -
      ∑ z ∈ twBlk n b, ∑ w ∈ twBlk n c₁, G₁' y z * G₂' z w * G₁' (twShift n c₂ w) x‖ ≤
      ((twBlk n b).card : ℝ) * ((twBlk n c₁).card : ℝ) * (3 * R ^ 2 * δ) := by
    rw [← Finset.sum_sub_distrib]
    simp only [← Finset.sum_sub_distrib]
    exact TwistGridWTail_norm_sum_sum_le _ _ _ fun z _ w _ =>
      TwistGridWTail_tri hR (h₁ _ _) (h₂ _ _) (h₁ _ _) (h₁' _ _) (h₂' _ _) (h₁' _ _) (d₁ _ _) (d₂ _ _) (d₁ _ _)
  have hS2 : ‖∑ w ∈ twBlk n c₁, ∑ z ∈ twBlk n b, G₂ y w * G₁ (twShift n c₂ w) z * G₂ z x -
      ∑ w ∈ twBlk n c₁, ∑ z ∈ twBlk n b, G₂' y w * G₁' (twShift n c₂ w) z * G₂' z x‖ ≤
      ((twBlk n c₁).card : ℝ) * ((twBlk n b).card : ℝ) * (3 * R ^ 2 * δ) := by
    rw [← Finset.sum_sub_distrib]
    simp only [← Finset.sum_sub_distrib]
    exact TwistGridWTail_norm_sum_sum_le _ _ _ fun w _ z _ =>
      TwistGridWTail_tri hR (h₂ _ _) (h₁ _ _) (h₂ _ _) (h₂' _ _) (h₁' _ _) (h₂' _ _) (d₂ _ _) (d₁ _ _) (d₂ _ _)
  rw [TwistGridWTail_card_blk, TwistGridWTail_card_blk] at hS1 hS2
  have hwd := TwistGridWTail_wd_sq (sz := sz) (d := d) n
  have hsplit : ∀ (A B A' B' : ℂ), (A + B) - (A' + B') = (A - A') + (B - B') := fun A B A' B' => by ring
  rw [hsplit]
  calc ‖((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2‖ * ‖_ + _‖ ≤ ‖((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2‖ *
        (((sz.W n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ d * (3 * R ^ 2 * δ) + ((sz.W n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ d * (3 * R ^ 2 * δ)) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hS1 hS2)) (norm_nonneg _)
    _ = 6 * R ^ 2 * δ := by
        have : ‖((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2‖ * (((sz.W n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ d) * (6 * R ^ 2 * δ) = 6 * R ^ 2 * δ := by
          rw [hwd, one_mul]
        linarith [this]

end Entry

/-! ## 3. Resolvent entries and the quadratic variation `twEEM`: crude bound and shift -/

section Resolvent

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Matrix.Norms.L2Operator in
/-- Entries of the charged resolvent are at most `η⁻¹` (`‖G‖ ≤ η⁻¹`, `|G_{xy}| ≤ ‖G‖`; the charge `−` is `conj G_{yx}`). -/
theorem TwistGridWTail_norm_chg_le {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|)
    (σ : Bool) (x y : ι) : ‖twChg (fun x y => Gres H z true x y) σ x y‖ ≤ η⁻¹ := by
  have h := norm_Gsig_le_inv_eta hH hη hz true
  have h1 := norm_matrix_entry_le_opNorm (Gres H z true)
  cases σ
  · simp only [twChg, Bool.false_eq_true, ite_false, Complex.norm_conj]
    exact (h1 y x).trans h
  · simp only [twChg, ite_true]
    exact (h1 x y).trans h

/-- The resolvent identity `G(z') − G(z) = (z' − z) G(z') G(z)` for non-real spectral parameters. -/
theorem TwistGridWTail_resolvent_identity {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z z' : ℂ} (hz : z.im ≠ 0) (hz' : z'.im ≠ 0) :
    Gres H z' true - Gres H z true = (z' - z) • (Gres H z' true * Gres H z true) := by
  have hA := isUnit_sub_smul_of_isHermitian hH hz
  have hB := isUnit_sub_smul_of_isHermitian hH hz'
  have e1 : Gres H z true * (H - z • (1 : Matrix ι ι ℂ)) = 1 := by
    simp only [Gres, ↓reduceIte]; exact Ring.inverse_mul_cancel _ hA
  have e2 : (H - z' • (1 : Matrix ι ι ℂ)) * Gres H z' true = 1 := by
    simp only [Gres, ↓reduceIte]; exact Ring.mul_inverse_cancel _ hB
  have e3 : (H - z • (1 : Matrix ι ι ℂ)) * Gres H z true = 1 := by
    simp only [Gres, ↓reduceIte]; exact Ring.mul_inverse_cancel _ hA
  have e4 : Gres H z' true * (H - z' • (1 : Matrix ι ι ℂ)) = 1 := by
    simp only [Gres, ↓reduceIte]; exact Ring.inverse_mul_cancel _ hB
  calc Gres H z' true - Gres H z true
      = Gres H z' true * ((H - z • (1 : Matrix ι ι ℂ)) - (H - z' • (1 : Matrix ι ι ℂ))) * Gres H z true := by
        rw [mul_sub, sub_mul, mul_assoc, e3, mul_one, mul_assoc, ← mul_assoc _ (H - z' • (1 : Matrix ι ι ℂ)), e4, one_mul]
    _ = (z' - z) • (Gres H z' true * Gres H z true) := by
        have : (H - z • (1 : Matrix ι ι ℂ)) - (H - z' • (1 : Matrix ι ι ℂ)) = (z' - z) • (1 : Matrix ι ι ℂ) := by
          rw [sub_smul]; abel
        rw [this, Matrix.mul_smul, Matrix.smul_mul, mul_one]

open scoped Matrix.Norms.L2Operator in
/-- Entries of the charged resolvents at two spectral parameters differ by at most `|z' − z| η⁻²`. -/
theorem TwistGridWTail_chg_sub_le {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z z' : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|)
    (hz' : η ≤ |z'.im|) (σ : Bool) (x y : ι) :
    ‖twChg (fun x y => Gres H z' true x y) σ x y - twChg (fun x y => Gres H z true x y) σ x y‖ ≤ ‖z' - z‖ * η⁻¹ ^ 2 := by
  have hz0 : z.im ≠ 0 := fun h => absurd hz (by rw [h]; simpa using hη)
  have hz0' : z'.im ≠ 0 := fun h => absurd hz' (by rw [h]; simpa using hη)
  have hid := TwistGridWTail_resolvent_identity hH hz0 hz0'
  have hG := norm_Gsig_le_inv_eta hH hη hz true
  have hG' := norm_Gsig_le_inv_eta hH hη hz' true
  have hnorm : ‖Gres H z' true - Gres H z true‖ ≤ ‖z' - z‖ * η⁻¹ ^ 2 := by
    rw [hid]
    refine (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans ?_) (norm_nonneg _))
    calc ‖Gres H z' true‖ * ‖Gres H z true‖ ≤ η⁻¹ * η⁻¹ := mul_le_mul hG' hG (norm_nonneg _) (inv_nonneg.2 hη.le)
      _ = η⁻¹ ^ 2 := by ring
  have h1 := norm_matrix_entry_le_opNorm (Gres H z' true - Gres H z true)
  cases σ
  · simp only [twChg, Bool.false_eq_true, ite_false]
    rw [← map_sub, Complex.norm_conj]
    exact ((h1 y x).trans hnorm).trans' (le_of_eq (by simp))
  · simp only [twChg, ite_true]
    exact ((h1 x y).trans hnorm).trans' (le_of_eq (by simp))

end Resolvent

section EE

variable {d : ℕ} {sz : Sizes d} (lam0 E : ℕ → ℝ) (n : ℕ)

/-- The variance weight `W^{-d} S^{(B)}_{[x][y]}` of `twEEM` (`S^{(B)} = 1` at the carrier `baFM`). -/
def TwistGridWTail_wS (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFM sz lam0 E).S n (split d (sz.L n) (sz.W n) x).1 (split d (sz.L n) (sz.W n) y).1

theorem TwistGridWTail_twEEM_eq (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool)
    (b b' c₁ c₂ : Zd d (sz.L n)) :
    twEEM sz lam0 E n u H σ b b' c₁ c₂ = ∑ x, ∑ y, TwistGridWTail_wS lam0 E n x y *
      (twDerM sz lam0 E n u H σ b c₁ c₂ x y * (starRingEnd ℂ) (twDerM sz lam0 E n u H σ b' c₁ c₂ x y)) := rfl

/-- `Σ_{x,y} |W^{-d} S^{(B)}_{[x][y]}| = N` (`S^{(B)} = 1`: `W^d` points per block, `L^d` blocks). -/
theorem TwistGridWTail_sum_wS : ∑ x, ∑ y, ‖TwistGridWTail_wS (sz := sz) lam0 E n x y‖ = ((sz.size n : ℕ) : ℝ) := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hrow : ∀ x : Idx d (sz.L n) (sz.W n), ∑ y, ‖TwistGridWTail_wS (sz := sz) lam0 E n x y‖ = 1 := by
    intro x
    have h1 : ∀ y : Idx d (sz.L n) (sz.W n), ‖TwistGridWTail_wS (sz := sz) lam0 E n x y‖ =
        (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (if (split d (sz.L n) (sz.W n) y).1 = (split d (sz.L n) (sz.W n) x).1 then 1 else 0) := by
      intro y
      unfold TwistGridWTail_wS
      simp only [baFM, Matrix.one_apply, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
      by_cases h : (split d (sz.L n) (sz.W n) x).1 = (split d (sz.L n) (sz.W n) y).1
      · simp [h]
      · have h' : ¬ (split d (sz.L n) (sz.W n) y).1 = (split d (sz.L n) (sz.W n) x).1 := fun h2 => h h2.symm
        simp [h, h']
    simp only [h1, ← Finset.mul_sum, Finset.sum_boole]
    have : (Finset.univ.filter fun y : Idx d (sz.L n) (sz.W n) => (split d (sz.L n) (sz.W n) y).1 = (split d (sz.L n) (sz.W n) x).1) =
        twBlk n (split d (sz.L n) (sz.W n) x).1 := rfl
    rw [this, TwistGridWTail_card_blk]
    field_simp
  simp only [hrow, Finset.sum_const, Finset.card_univ, Sizes.card_Idx, nsmul_eq_mul, mul_one]

private theorem TwistGridWTail_norm_sum_wS_mul_le {f : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ} {M : ℝ}
    (hf : ∀ x y, ‖f x y‖ ≤ M) :
    ‖∑ x, ∑ y, TwistGridWTail_wS (sz := sz) lam0 E n x y * f x y‖ ≤ ((sz.size n : ℕ) : ℝ) * M := by
  calc ‖∑ x, ∑ y, TwistGridWTail_wS (sz := sz) lam0 E n x y * f x y‖
      ≤ ∑ x, ∑ y, ‖TwistGridWTail_wS (sz := sz) lam0 E n x y‖ * M := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_))
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hf x y) (norm_nonneg _)
    _ = ((sz.size n : ℕ) : ℝ) * M := by
        rw [← TwistGridWTail_sum_wS lam0 E n, Finset.sum_mul]
        exact Finset.sum_congr rfl fun x _ => by rw [Finset.sum_mul]

/-- `η ≤ |Im z_u|` from `η ≤ η_u = (1 − u) Im m` (`Im z_u = η_u`, `ztOf_im`). -/
theorem TwistGridWTail_abs_im {m : ℂ} (Eu u : ℝ) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ etaOf m u) : η ≤ |(ztOf m Eu u).im| := by
  rw [ztOf_im, abs_of_pos (hη0.trans_le hη)]; exact hη

/-- **Crude bound of the gradient at a Hermitian matrix**: `|∂_{xy} L̃| ≤ 2 η⁻³` when `η ≤ η_u`. -/
theorem TwistGridWTail_twDerM_norm_le (u : ℝ) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hH : H.IsHermitian) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ etaOf (BAmF sz lam0 E n) u) (σ : Fin 2 → Bool)
    (b c₁ c₂ : Zd d (sz.L n)) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖twDerM sz lam0 E n u H σ b c₁ c₂ x y‖ ≤ 2 * (η⁻¹) ^ 3 := by
  have hz := TwistGridWTail_abs_im (E n) u hη0 hη
  exact TwistGridWTail_der_norm_le n (inv_nonneg.2 hη0.le) (fun x y => TwistGridWTail_norm_chg_le hH hη0 hz _ x y)
    (fun x y => TwistGridWTail_norm_chg_le hH hη0 hz _ x y) b c₁ c₂ x y

/-- **Crude bound of the quadratic variation** `|(Ẽ⊗Ẽ)(b,b')| ≤ N (2 η⁻³)²` (`Σ_{xy} |W^{-d} S_{xy}| = N`). -/
theorem TwistGridWTail_twEEM_norm_le (u : ℝ) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hH : H.IsHermitian) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ etaOf (BAmF sz lam0 E n) u) (σ : Fin 2 → Bool)
    (b b' c₁ c₂ : Zd d (sz.L n)) :
    ‖twEEM sz lam0 E n u H σ b b' c₁ c₂‖ ≤ ((sz.size n : ℕ) : ℝ) * (2 * (η⁻¹) ^ 3 * (2 * (η⁻¹) ^ 3)) := by
  rw [TwistGridWTail_twEEM_eq]
  refine TwistGridWTail_norm_sum_wS_mul_le lam0 E n fun x y => ?_
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (TwistGridWTail_twDerM_norm_le lam0 E n u hH hη0 hη σ b c₁ c₂ x y)
    (TwistGridWTail_twDerM_norm_le lam0 E n u hH hη0 hη σ b' c₁ c₂ x y) (norm_nonneg _) (by positivity)

/-- **The shift of the quadratic variation in `u`**: for `η ≤ η_u, η_{u'}`,
`|(Ẽ⊗Ẽ)_{u'}(H) − (Ẽ⊗Ẽ)_u(H)| ≤ 24 N η⁻⁷ |z_{u'} − z_u|` (the gradient moves by `6 η⁻⁴ |z' − z|`, the resolvent identity). -/
theorem TwistGridWTail_twEEM_sub_le (u u' : ℝ) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hH : H.IsHermitian) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ etaOf (BAmF sz lam0 E n) u)
    (hη' : η ≤ etaOf (BAmF sz lam0 E n) u') (σ : Fin 2 → Bool) (b b' c₁ c₂ : Zd d (sz.L n)) :
    ‖twEEM sz lam0 E n u' H σ b b' c₁ c₂ - twEEM sz lam0 E n u H σ b b' c₁ c₂‖ ≤
      ((sz.size n : ℕ) : ℝ) * (24 * (η⁻¹) ^ 7 * ‖ztOf (BAmF sz lam0 E n) (E n) u' - ztOf (BAmF sz lam0 E n) (E n) u‖) := by
  rw [TwistGridWTail_twEEM_eq, TwistGridWTail_twEEM_eq, ← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib, ← mul_sub]
  set Δz := ‖ztOf (BAmF sz lam0 E n) (E n) u' - ztOf (BAmF sz lam0 E n) (E n) u‖ with hΔz
  have hz := TwistGridWTail_abs_im (E n) u hη0 hη
  have hz' := TwistGridWTail_abs_im (E n) u' hη0 hη'
  have hR0 : 0 ≤ η⁻¹ := inv_nonneg.2 hη0.le
  have hδ : ∀ σ' : Bool, ∀ x y : Idx d (sz.L n) (sz.W n),
      ‖twChg (twGM sz lam0 E n u' H) σ' x y - twChg (twGM sz lam0 E n u H) σ' x y‖ ≤ Δz * η⁻¹ ^ 2 := fun σ' x y =>
    TwistGridWTail_chg_sub_le hH hη0 hz hz' σ' x y
  have hdS : ∀ b'' : Zd d (sz.L n), ∀ x y : Idx d (sz.L n) (sz.W n),
      ‖twDerM sz lam0 E n u' H σ b'' c₁ c₂ x y - twDerM sz lam0 E n u H σ b'' c₁ c₂ x y‖ ≤ 6 * (η⁻¹) ^ 2 * (Δz * η⁻¹ ^ 2) := by
    intro b'' x y
    exact TwistGridWTail_der_sub_le n hR0 (fun x y => TwistGridWTail_norm_chg_le hH hη0 hz' _ x y)
      (fun x y => TwistGridWTail_norm_chg_le hH hη0 hz' _ x y) (fun x y => TwistGridWTail_norm_chg_le hH hη0 hz _ x y)
      (fun x y => TwistGridWTail_norm_chg_le hH hη0 hz _ x y) (fun x y => hδ _ x y) (fun x y => hδ _ x y) b'' c₁ c₂ x y
  have hΔ0 : 0 ≤ Δz := norm_nonneg _
  refine (TwistGridWTail_norm_sum_wS_mul_le lam0 E n (M := 2 * (2 * (η⁻¹) ^ 3) * (6 * (η⁻¹) ^ 2 * (Δz * η⁻¹ ^ 2))) fun x y => ?_).trans ?_
  · have e : ∀ (f f' e e' : ℂ), f * (starRingEnd ℂ) f' - e * (starRingEnd ℂ) e' =
        (f - e) * (starRingEnd ℂ) f' + e * (starRingEnd ℂ) (f' - e') := fun f f' e e' => by rw [map_sub]; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
    have h1 := TwistGridWTail_twDerM_norm_le lam0 E n u' hH hη0 hη' σ b' c₁ c₂ x y
    have h2 := TwistGridWTail_twDerM_norm_le lam0 E n u hH hη0 hη σ b c₁ c₂ x y
    have h3 := hdS b x y
    have h4 := hdS b' x y
    have hA : ‖twDerM sz lam0 E n u' H σ b c₁ c₂ x y - twDerM sz lam0 E n u H σ b c₁ c₂ x y‖ * ‖twDerM sz lam0 E n u' H σ b' c₁ c₂ x y‖ ≤
        6 * (η⁻¹) ^ 2 * (Δz * η⁻¹ ^ 2) * (2 * (η⁻¹) ^ 3) := mul_le_mul h3 h1 (norm_nonneg _) (by positivity)
    have hB : ‖twDerM sz lam0 E n u H σ b c₁ c₂ x y‖ * ‖twDerM sz lam0 E n u' H σ b' c₁ c₂ x y - twDerM sz lam0 E n u H σ b' c₁ c₂ x y‖ ≤
        2 * (η⁻¹) ^ 3 * (6 * (η⁻¹) ^ 2 * (Δz * η⁻¹ ^ 2)) := mul_le_mul h2 h4 (norm_nonneg _) (by positivity)
    nlinarith
  · apply le_of_eq
    ring

end EE

/-! ## 4. The twisted observable `Φ_b(M) = L̃_u(g₀Ψ + M)`: jets along Hermitian lines, `HermTestFun`, the second-derivative bound

Copies (stem `TwistGridWTail_`) of the private `LoopC2N_hasDerivAt_line`, `_isHermitian_add_realSmul`, `_hasDerivAt_Gres`,
`_fderiv_of_line`, `_fderiv2_of_line` (`Induction/LoopC2N.lean:238-305`, `691566a` lineage); the Leibniz count is that of
`LoopC2N_word_jets` for two entries: `|p''| ≤ 6 K⁴ ‖D‖²`. -/

section Jets

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Matrix.Norms.L2Operator

private theorem TwistGridWTail_hasDerivAt_line (M A : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => M + (s : ℂ) • A) A t := by
  have h : HasDerivAt (fun s : ℝ => (s : ℂ) • A) A t := by
    simpa using (hasDerivAt_id t).smul_const A
  simpa using h.const_add M

omit [Fintype ι] [DecidableEq ι] in
private theorem TwistGridWTail_isHermitian_add_realSmul {M A : Matrix ι ι ℂ} (hM : M.IsHermitian) (hA : A.IsHermitian) (s : ℝ) :
    (M + (s : ℂ) • A).IsHermitian := by
  refine hM.add ?_
  change Matrix.conjTranspose ((s : ℂ) • A) = (s : ℂ) • A
  rw [Matrix.conjTranspose_smul, hA, Complex.star_def, Complex.conj_ofReal]

private theorem TwistGridWTail_hasDerivAt_Gres {H D : Matrix ι ι ℂ} (hH : H.IsHermitian) (hD : D.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) (σ : Bool) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Gres (H + (s : ℂ) • D) z σ)
      (-(Gres (H + (t : ℂ) • D) z σ * D * Gres (H + (t : ℂ) • D) z σ)) t := by
  have hline := TwistGridWTail_hasDerivAt_line H D t
  have hherm := TwistGridWTail_isHermitian_add_realSmul hH hD t
  cases σ with
  | true =>
    have h := hasDerivAt_green_moving (z := fun _ => z) hline (hasDerivAt_const t z) hherm hz
    simpa using h
  | false =>
    have h := hasDerivAt_green_moving (z := fun _ => (starRingEnd ℂ) z) hline
      (hasDerivAt_const t ((starRingEnd ℂ) z)) hherm (by simpa using hz)
    simpa [Gres] using h

private theorem TwistGridWTail_fderiv2_of_line {Φ : Matrix ι ι ℂ → ℂ}
    (hΦ : ∀ M, M.IsHermitian → ContDiffAt ℝ 2 Φ M) {M y : Matrix ι ι ℂ} (hM : M.IsHermitian) (hy : y.IsHermitian)
    {φ₁ φ₂ : ℝ → ℂ} (h₀ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Φ (M + (s : ℂ) • y)) (φ₁ t) t)
    (h₁ : ∀ t : ℝ, HasDerivAt φ₁ (φ₂ t) t) :
    fderiv ℝ (fderiv ℝ Φ) M y y = φ₂ 0 := by
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => M + (s : ℂ) • y) y t := fun t => TwistGridWTail_hasDerivAt_line M y t
  have hφ₁ : ∀ t : ℝ, φ₁ t = fderiv ℝ Φ (M + (t : ℂ) • y) y := by
    intro t
    have hdiff : DifferentiableAt ℝ Φ (M + (t : ℂ) • y) :=
      ((hΦ _ (TwistGridWTail_isHermitian_add_realSmul hM hy t)).differentiableAt (by norm_num))
    have h := hdiff.hasFDerivAt.comp_hasDerivAt t (hline t)
    exact (h₀ t).unique h
  have hfd : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) M) M :=
    (((hΦ M hM).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hpt : M + ((0 : ℝ) : ℂ) • y = M := by simp
  have hΘ : HasFDerivAt (fun N : Matrix ι ι ℂ => fderiv ℝ Φ N y)
      ((ContinuousLinearMap.apply ℝ ℂ y).comp (fderiv ℝ (fderiv ℝ Φ) M)) M :=
    (ContinuousLinearMap.apply ℝ ℂ y).hasFDerivAt.comp M hfd
  have hev := hΘ.comp_hasDerivAt_of_eq (0 : ℝ) (hline 0) hpt.symm
  have hfun : (fun t : ℝ => fderiv ℝ Φ (M + (t : ℂ) • y) y) = φ₁ := by
    funext t; exact (hφ₁ t).symm
  have hev' : HasDerivAt φ₁ (fderiv ℝ (fderiv ℝ Φ) M y y) 0 := by
    rw [← hfun]
    exact hev
  exact hev'.unique (h₁ 0)

/-- **Jets of a product of two resolvent entries** along a Hermitian line: with `R_i' = −R_i D R_i`, `‖R_i‖ ≤ K`, the product
`R₂(x,w) R₁(v,y)` has the explicit first derivative `p₁` and a second derivative `p₂` with `|p₂| ≤ 6 K⁴ ‖D‖²`
(`a'' b + 2 a' b' + a b''` with `|a| ≤ K`, `|a'| ≤ K²‖D‖`, `|a''| ≤ 2 K³ ‖D‖²`). -/
private theorem TwistGridWTail_entry_jets {R₁ R₂ : ℝ → Matrix ι ι ℂ} {D : Matrix ι ι ℂ} {K : ℝ}
    (h₁ : ∀ t, HasDerivAt R₁ (-(R₁ t * D * R₁ t)) t) (h₂ : ∀ t, HasDerivAt R₂ (-(R₂ t * D * R₂ t)) t)
    (hK₁ : ∀ t, ‖R₁ t‖ ≤ K) (hK₂ : ∀ t, ‖R₂ t‖ ≤ K) (x w v y : ι) :
    ∃ p₂ : ℝ → ℂ,
      (∀ t, HasDerivAt (fun s => R₂ s x w * R₁ s v y)
        (-(R₂ t * D * R₂ t) x w * R₁ t v y + R₂ t x w * -(R₁ t * D * R₁ t) v y) t) ∧
      (∀ t, HasDerivAt (fun t => -(R₂ t * D * R₂ t) x w * R₁ t v y + R₂ t x w * -(R₁ t * D * R₁ t) v y) (p₂ t) t) ∧
      (∀ t, ‖p₂ t‖ ≤ 6 * K ^ 4 * ‖D‖ ^ 2) := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK₁ 0)
  -- the derivative of an entry of a matrix function
  have hent : ∀ {F : ℝ → Matrix ι ι ℂ} {F' : Matrix ι ι ℂ} {t : ℝ}, HasDerivAt F F' t → ∀ i j, HasDerivAt (fun s => F s i j) (F' i j) t :=
    fun {F F' t} h i j => (hasDerivAt_pi.1 (hasDerivAt_pi.1 h i) j)
  have hRDR : ∀ (R : ℝ → Matrix ι ι ℂ), (∀ t, HasDerivAt R (-(R t * D * R t)) t) → ∀ t,
      HasDerivAt (fun s => R s * D * R s) (-(R t * D * R t) * D * R t + R t * D * (-(R t * D * R t))) t := fun R hR t =>
    ((hR t).mul_const D).mul (hR t)
  have hnorm1 : ∀ (R : ℝ → Matrix ι ι ℂ), (∀ t, ‖R t‖ ≤ K) → ∀ t i j, ‖(R t * D * R t) i j‖ ≤ K ^ 2 * ‖D‖ := by
    intro R hK t i j
    refine (norm_matrix_entry_le_opNorm _ i j).trans ?_
    calc ‖R t * D * R t‖ ≤ ‖R t‖ * ‖D‖ * ‖R t‖ := (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ K * ‖D‖ * K := by gcongr; exact hK t; exact hK t
      _ = K ^ 2 * ‖D‖ := by ring
  have hnorm2 : ∀ (R : ℝ → Matrix ι ι ℂ), (∀ t, ‖R t‖ ≤ K) → ∀ t i j,
      ‖((R t * D * R t) * D * R t + R t * D * (R t * D * R t)) i j‖ ≤ 2 * K ^ 3 * ‖D‖ ^ 2 := by
    intro R hK t i j
    refine (norm_matrix_entry_le_opNorm _ i j).trans ?_
    have hX : ‖R t * D * R t‖ ≤ K * ‖D‖ * K :=
      (norm_mul_le _ _).trans (mul_le_mul (((norm_mul_le _ _).trans (mul_le_mul (hK t) le_rfl (norm_nonneg _) hK0))) (hK t) (norm_nonneg _) (by positivity))
    have h1 : ‖(R t * D * R t) * D * R t‖ ≤ K * ‖D‖ * K * ‖D‖ * K :=
      (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul hX le_rfl (norm_nonneg _) (by positivity))) (hK t) (norm_nonneg _) (by positivity))
    have h2 : ‖R t * D * (R t * D * R t)‖ ≤ K * ‖D‖ * (K * ‖D‖ * K) :=
      (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul (hK t) le_rfl (norm_nonneg _) hK0)) hX (norm_nonneg _) (by positivity))
    calc _ ≤ ‖(R t * D * R t) * D * R t‖ + ‖R t * D * (R t * D * R t)‖ := norm_add_le _ _
      _ ≤ K * ‖D‖ * K * ‖D‖ * K + K * ‖D‖ * (K * ‖D‖ * K) := add_le_add h1 h2
      _ = 2 * K ^ 3 * ‖D‖ ^ 2 := by ring
  refine ⟨fun t =>
    ((R₂ t * D * R₂ t) * D * R₂ t + R₂ t * D * (R₂ t * D * R₂ t)) x w * R₁ t v y +
      2 * (-(R₂ t * D * R₂ t) x w * -(R₁ t * D * R₁ t) v y) +
      R₂ t x w * ((R₁ t * D * R₁ t) * D * R₁ t + R₁ t * D * (R₁ t * D * R₁ t)) v y, ?_, ?_, ?_⟩
  · intro t
    exact ((hent (h₂ t) x w).mul (hent (h₁ t) v y)).congr_deriv (by simp only [Matrix.neg_apply])
  · intro t
    have hA : HasDerivAt (fun s => -(R₂ s * D * R₂ s) x w)
        (((R₂ t * D * R₂ t) * D * R₂ t + R₂ t * D * (R₂ t * D * R₂ t)) x w) t := by
      have h := (hent (hRDR R₂ h₂ t) x w).neg
      refine h.congr_deriv ?_
      simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.mul_neg, Matrix.neg_mul]
      ring
    have hB : HasDerivAt (fun s => -(R₁ s * D * R₁ s) v y)
        (((R₁ t * D * R₁ t) * D * R₁ t + R₁ t * D * (R₁ t * D * R₁ t)) v y) t := by
      have h := (hent (hRDR R₁ h₁ t) v y).neg
      refine h.congr_deriv ?_
      simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.mul_neg, Matrix.neg_mul]
      ring
    exact ((hA.mul (hent (h₁ t) v y)).add ((hent (h₂ t) x w).mul hB)).congr_deriv (by simp only [Matrix.neg_apply]; ring)
  · intro t
    have a0 : ‖R₂ t x w‖ ≤ K := (norm_matrix_entry_le_opNorm _ x w).trans (hK₂ t)
    have b0 : ‖R₁ t v y‖ ≤ K := (norm_matrix_entry_le_opNorm _ v y).trans (hK₁ t)
    have a1 := hnorm1 R₂ hK₂ t x w
    have b1 := hnorm1 R₁ hK₁ t v y
    have a2 := hnorm2 R₂ hK₂ t x w
    have b2 := hnorm2 R₁ hK₁ t v y
    have hD0 : 0 ≤ ‖D‖ := norm_nonneg _
    simp only [neg_mul_neg]
    refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    simp only [Complex.norm_ofNat]
    have e1 : ‖((R₂ t * D * R₂ t) * D * R₂ t + R₂ t * D * (R₂ t * D * R₂ t)) x w‖ * ‖R₁ t v y‖ ≤ 2 * K ^ 3 * ‖D‖ ^ 2 * K :=
      mul_le_mul a2 b0 (norm_nonneg _) (by positivity)
    have e2 : ‖(R₂ t * D * R₂ t) x w‖ * ‖(R₁ t * D * R₁ t) v y‖ ≤ K ^ 2 * ‖D‖ * (K ^ 2 * ‖D‖) :=
      mul_le_mul a1 b1 (norm_nonneg _) (by positivity)
    have e3 : ‖R₂ t x w‖ * ‖((R₁ t * D * R₁ t) * D * R₁ t + R₁ t * D * (R₁ t * D * R₁ t)) v y‖ ≤ K * (2 * K ^ 3 * ‖D‖ ^ 2) :=
      mul_le_mul a0 b2 (norm_nonneg _) (by positivity)
    nlinarith

omit [Fintype ι] [DecidableEq ι] in
private theorem TwistGridWTail_sum_comm4 (B C : Finset ι) [Fintype ι] (f : ι → ι → ι → ι → ℂ) :
    ∑ x ∈ B, ∑ w ∈ C, ∑ q, ∑ p, f x w q p = ∑ p, ∑ q, ∑ w ∈ C, ∑ x ∈ B, f x w q p := by
  calc ∑ x ∈ B, ∑ w ∈ C, ∑ q, ∑ p, f x w q p = ∑ x ∈ B, ∑ w ∈ C, ∑ p, ∑ q, f x w q p :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun w _ => Finset.sum_comm
    _ = ∑ x ∈ B, ∑ p, ∑ w ∈ C, ∑ q, f x w q p := Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ p, ∑ x ∈ B, ∑ w ∈ C, ∑ q, f x w q p := Finset.sum_comm
    _ = ∑ p, ∑ x ∈ B, ∑ q, ∑ w ∈ C, f x w q p :=
        Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ p, ∑ q, ∑ x ∈ B, ∑ w ∈ C, f x w q p := Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ p, ∑ q, ∑ w ∈ C, ∑ x ∈ B, f x w q p :=
        Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => Finset.sum_comm

omit [Fintype ι] [DecidableEq ι] in
private theorem TwistGridWTail_sum_comm4' (B C : Finset ι) [Fintype ι] (f : ι → ι → ι → ι → ℂ) :
    ∑ x ∈ B, ∑ w ∈ C, ∑ q, ∑ p, f x w q p = ∑ p, ∑ q, ∑ x ∈ B, ∑ w ∈ C, f x w q p := by
  rw [TwistGridWTail_sum_comm4]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => Finset.sum_comm

end Jets

section DerivIdentity

variable {d : ℕ} {sz : Sizes d} (n : ℕ)

/-- **The directional derivative of `L̃` is the pairing with the gradient**: the first derivative of `Tr(R₁ E_b R₂ P)` along `X`
(`R_i' = −R_i X R_i`) equals `Σ_{p,q} ∂_{pq} L̃ · X_{pq}` with `∂_{pq} L̃ = TwistGridWTail_der` (D.2): a rearrangement of four finite sums. -/
theorem TwistGridWTail_deriv_identity (R₁ R₂ X : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (b c₁ c₂ : Zd d (sz.L n)) :
    ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n b, ∑ w ∈ twBlk n c₁,
      (-(R₂ * X * R₂) x w * R₁ (twShift n c₂ w) x + R₂ x w * -(R₁ * X * R₁) (twShift n c₂ w) x) =
    ∑ p, ∑ q, TwistGridWTail_der n (fun x y => R₁ x y) (fun x y => R₂ x y) b c₁ c₂ p q * X p q := by
  have I1 : ∑ x ∈ twBlk n b, ∑ w ∈ twBlk n c₁, (R₂ * X * R₂) x w * R₁ (twShift n c₂ w) x =
      ∑ p, ∑ q, (∑ w ∈ twBlk n c₁, ∑ z ∈ twBlk n b, R₂ q w * R₁ (twShift n c₂ w) z * R₂ z p) * X p q := by
    have h := TwistGridWTail_sum_comm4 (twBlk n b) (twBlk n c₁)
      (fun x w q p => R₂ x p * X p q * R₂ q w * R₁ (twShift n c₂ w) x)
    simp only [Matrix.mul_apply, Finset.sum_mul]
    refine h.trans (Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_)
    exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun x _ => by ring
  have I2 : ∑ x ∈ twBlk n b, ∑ w ∈ twBlk n c₁, R₂ x w * (R₁ * X * R₁) (twShift n c₂ w) x =
      ∑ p, ∑ q, (∑ z ∈ twBlk n b, ∑ w ∈ twBlk n c₁, R₁ q z * R₂ z w * R₁ (twShift n c₂ w) p) * X p q := by
    have h := TwistGridWTail_sum_comm4' (twBlk n b) (twBlk n c₁)
      (fun x w q p => R₂ x w * (R₁ (twShift n c₂ w) p * X p q * R₁ q x))
    simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    refine h.trans (Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_)
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun w _ => by ring
  have hL : ∑ x ∈ twBlk n b, ∑ w ∈ twBlk n c₁,
      (-(R₂ * X * R₂) x w * R₁ (twShift n c₂ w) x + R₂ x w * -(R₁ * X * R₁) (twShift n c₂ w) x) =
      -(∑ x ∈ twBlk n b, ∑ w ∈ twBlk n c₁, (R₂ * X * R₂) x w * R₁ (twShift n c₂ w) x) -
        ∑ x ∈ twBlk n b, ∑ w ∈ twBlk n c₁, R₂ x w * (R₁ * X * R₁) (twShift n c₂ w) x := by
    simp only [neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    ring
  rw [hL, I1, I2]
  unfold TwistGridWTail_der
  set wd : ℂ := ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 with hwd
  have hpt : ∀ p q : Idx d (sz.L n) (sz.W n),
      -wd * ((∑ z ∈ twBlk n b, ∑ w ∈ twBlk n c₁, R₁ q z * R₂ z w * R₁ (twShift n c₂ w) p) +
        ∑ w ∈ twBlk n c₁, ∑ z ∈ twBlk n b, R₂ q w * R₁ (twShift n c₂ w) z * R₂ z p) * X p q =
      -wd * ((∑ z ∈ twBlk n b, ∑ w ∈ twBlk n c₁, R₁ q z * R₂ z w * R₁ (twShift n c₂ w) p) * X p q) +
        -wd * ((∑ w ∈ twBlk n c₁, ∑ z ∈ twBlk n b, R₂ q w * R₁ (twShift n c₂ w) z * R₂ z p) * X p q) := fun p q => by ring
  simp only [hpt, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end DerivIdentity

/-! ### The observable and its derivatives along Hermitian lines -/

section Obs

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)

open scoped Matrix.Norms.L2Operator

/-- The flow matrix `H = g₀ Ψ + M` of the carrier `baStep2Mat` (`Hpath = g₀ Ψ + pathH`). -/
def TwistGridWTail_Hm (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  ((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + M

/-- **The observable `Φ_b(M) = L̃_{u,σ,(b;c₁,c₂)}(g₀Ψ + M)`** (the label family of `stepDecompCN`, `Φ_b ∘ pathH = twAk + K̃`). -/
def TwistGridWTail_Phi (u : ℝ) (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)) (b : Zd d (sz.L n)) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ :=
  fun M => twL2M sz lam0 E n u (TwistGridWTail_Hm sz lam0 n M) σ b c₁ c₂

theorem TwistGridWTail_Hm_herm {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian) :
    (TwistGridWTail_Hm sz lam0 n M).IsHermitian := by
  unfold TwistGridWTail_Hm
  refine Matrix.IsHermitian.add ?_ hM
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, (PsiI_isHermitian d _ _).eq, show star ((lam0 n : ℝ) : ℂ) = ((lam0 n : ℝ) : ℂ) from Complex.conj_ofReal _]

theorem TwistGridWTail_Hm_add (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (s : ℝ) :
    TwistGridWTail_Hm sz lam0 n (M + (s : ℂ) • y) = TwistGridWTail_Hm sz lam0 n M + (s : ℂ) • y := by
  unfold TwistGridWTail_Hm; rw [add_assoc]

private theorem TwistGridWTail_chg_eq_Gres {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (z : ℂ)
    (σ : Bool) (x y : ι) : twChg (fun x y => Gres H z true x y) σ x y = Gres H z σ x y := by
  cases σ
  · have hH' : Hᴴ = H := hH
    have : (Gres H z true)ᴴ = Gres H z false := by
      simp only [Gres, ↓reduceIte, Bool.false_eq_true, ← Matrix.nonsing_inv_eq_ringInverse,
        Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
        Matrix.conjTranspose_one, hH', Complex.star_def]
    simp only [twChg, Bool.false_eq_true, ite_false]
    rw [← this]; rfl
  · rfl

/-- The observable along a Hermitian line is `W^{-2d} Σ_{x ∈ [b]} Σ_{w ∈ [c₁]} R₂(s)_{xw} R₁(s)_{σ(w) x}` with `R_i(s) = G_{σ_i}(H + sD)`. -/
theorem TwistGridWTail_Phi_line (u : ℝ) (σ : Fin 2 → Bool) (c₁ c₂ b : Zd d (sz.L n))
    {M D : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian) (hD : D.IsHermitian) (s : ℝ) :
    TwistGridWTail_Phi sz lam0 E n u σ c₁ c₂ b (M + (s : ℂ) • D) =
      ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n b, ∑ w ∈ twBlk n c₁,
        Gres (TwistGridWTail_Hm sz lam0 n M + (s : ℂ) • D) (ztOf (BAmF sz lam0 E n) (E n) u) (σ 1) x w *
          Gres (TwistGridWTail_Hm sz lam0 n M + (s : ℂ) • D) (ztOf (BAmF sz lam0 E n) (E n) u) (σ 0) (twShift n c₂ w) x := by
  have hH := TwistGridWTail_isHermitian_add_realSmul (TwistGridWTail_Hm_herm sz lam0 n hM) hD s
  unfold TwistGridWTail_Phi twL2M twLoopX
  rw [TwistGridWTail_Hm_add]
  refine congrArg _ (Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun w _ => ?_)
  have h1 : ∀ (σ' : Bool) (x' y' : Idx d (sz.L n) (sz.W n)), twChg (twGM sz lam0 E n u (TwistGridWTail_Hm sz lam0 n M + (s : ℂ) • D)) σ' x' y' =
      Gres (TwistGridWTail_Hm sz lam0 n M + (s : ℂ) • D) (ztOf (BAmF sz lam0 E n) (E n) u) σ' x' y' :=
    fun σ' x' y' => TwistGridWTail_chg_eq_Gres hH _ σ' x' y'
  rw [h1, h1]

/-- **Jets of the observable along a Hermitian line** `s ↦ M + sD` (`η ≤ η_u`): the first derivative `φ₁` with
`φ₁(0) = Σ_{p,q} ∂_{pq} L̃ · D_{pq}` (`twDerM` at `g₀Ψ + M`), a second derivative `φ₂` with `|φ₂| ≤ 6 η⁻⁴ ‖D‖²`. -/
theorem TwistGridWTail_Phi_jets (u : ℝ) (σ : Fin 2 → Bool) (c₁ c₂ b : Zd d (sz.L n))
    {M D : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian) (hD : D.IsHermitian)
    {η : ℝ} (hη0 : 0 < η) (hη : η ≤ etaOf (BAmF sz lam0 E n) u) :
    ∃ φ₁ φ₂ : ℝ → ℂ,
      (∀ t : ℝ, HasDerivAt (fun s : ℝ => TwistGridWTail_Phi sz lam0 E n u σ c₁ c₂ b (M + (s : ℂ) • D)) (φ₁ t) t) ∧
      (∀ t : ℝ, HasDerivAt φ₁ (φ₂ t) t) ∧ (∀ t : ℝ, ‖φ₂ t‖ ≤ 6 * η⁻¹ ^ 4 * ‖D‖ ^ 2) ∧
      φ₁ 0 = ∑ p, ∑ q, twDerM sz lam0 E n u (TwistGridWTail_Hm sz lam0 n M) σ b c₁ c₂ p q * D p q := by
  set z : ℂ := ztOf (BAmF sz lam0 E n) (E n) u with hz
  have hzabs : η ≤ |z.im| := TwistGridWTail_abs_im (E n) u hη0 hη
  have hz0 : z.im ≠ 0 := fun h => absurd hzabs (by rw [h]; simpa using hη0)
  have hHm := TwistGridWTail_Hm_herm sz lam0 n hM
  set R : Fin 2 → ℝ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
    fun i s => Gres (TwistGridWTail_Hm sz lam0 n M + (s : ℂ) • D) z (σ i) with hR
  have hd : ∀ i t, HasDerivAt (R i) (-(R i t * D * R i t)) t := fun i t =>
    TwistGridWTail_hasDerivAt_Gres hHm hD hz0 (σ i) t
  have hK : ∀ i t, ‖R i t‖ ≤ η⁻¹ := fun i t =>
    norm_Gsig_le_inv_eta (TwistGridWTail_isHermitian_add_realSmul hHm hD t) hη0 hzabs (σ i)
  have hjets := fun (x w : Idx d (sz.L n) (sz.W n)) => TwistGridWTail_entry_jets (R₁ := R 0) (R₂ := R 1) (D := D) (K := η⁻¹)
    (hd 0) (hd 1) (hK 0) (hK 1) x w (twShift n c₂ w) x
  choose p₂ hp₁ hp₂ hpb using hjets
  set wd : ℂ := ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 with hwd
  refine ⟨fun t => wd * ∑ x ∈ twBlk n b, ∑ w ∈ twBlk n c₁,
      (-(R 1 t * D * R 1 t) x w * R 0 t (twShift n c₂ w) x + R 1 t x w * -(R 0 t * D * R 0 t) (twShift n c₂ w) x),
    fun t => wd * ∑ x ∈ twBlk n b, ∑ w ∈ twBlk n c₁, p₂ x w t, ?_, ?_, ?_, ?_⟩
  · intro t
    have hfun : (fun s : ℝ => TwistGridWTail_Phi sz lam0 E n u σ c₁ c₂ b (M + (s : ℂ) • D)) =
        fun s => wd * ∑ x ∈ twBlk n b, ∑ w ∈ twBlk n c₁, R 1 s x w * R 0 s (twShift n c₂ w) x :=
      funext fun s => TwistGridWTail_Phi_line sz lam0 E n u σ c₁ c₂ b hM hD s
    rw [hfun]
    refine HasDerivAt.const_mul _ ?_
    exact HasDerivAt.fun_sum fun x _ => HasDerivAt.fun_sum fun w _ => hp₁ x w t
  · intro t
    refine HasDerivAt.const_mul _ ?_
    exact HasDerivAt.fun_sum fun x _ => HasDerivAt.fun_sum fun w _ => hp₂ x w t
  · intro t
    have hwd1 := TwistGridWTail_wd_sq (sz := sz) (d := d) n
    rw [norm_mul]
    have hS : ‖∑ x ∈ twBlk n b, ∑ w ∈ twBlk n c₁, p₂ x w t‖ ≤
        ((twBlk n b).card : ℝ) * ((twBlk n c₁).card : ℝ) * (6 * η⁻¹ ^ 4 * ‖D‖ ^ 2) :=
      TwistGridWTail_norm_sum_sum_le _ _ _ fun x _ w _ => hpb x w t
    rw [TwistGridWTail_card_blk, TwistGridWTail_card_blk] at hS
    calc ‖wd‖ * ‖∑ x ∈ twBlk n b, ∑ w ∈ twBlk n c₁, p₂ x w t‖
        ≤ ‖wd‖ * (((sz.W n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ d * (6 * η⁻¹ ^ 4 * ‖D‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hS (norm_nonneg _)
      _ = 6 * η⁻¹ ^ 4 * ‖D‖ ^ 2 := by
          have : ‖wd‖ * (((sz.W n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ d) * (6 * η⁻¹ ^ 4 * ‖D‖ ^ 2) = 6 * η⁻¹ ^ 4 * ‖D‖ ^ 2 := by
            rw [hwd1, one_mul]
          linarith [this]
  · have h0 : ∀ i, R i 0 = Gres (TwistGridWTail_Hm sz lam0 n M) z (σ i) := fun i => by simp [hR]
    simp only [h0]
    have hid := TwistGridWTail_deriv_identity n (Gres (TwistGridWTail_Hm sz lam0 n M) z (σ 0))
      (Gres (TwistGridWTail_Hm sz lam0 n M) z (σ 1)) D b c₁ c₂
    rw [hid]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [TwistGridWTail_twDerM_eq]
    congr 1
    have h1 : ∀ (σ' : Bool) (x' y' : Idx d (sz.L n) (sz.W n)), twChg (twGM sz lam0 E n u (TwistGridWTail_Hm sz lam0 n M)) σ' x' y' =
        Gres (TwistGridWTail_Hm sz lam0 n M) z σ' x' y' := fun σ' x' y' => TwistGridWTail_chg_eq_Gres hHm _ σ' x' y'
    unfold TwistGridWTail_der
    simp only [h1]

/-- Entry `(x, y)` as a continuous real-linear map. -/
private def TwistGridWTail_entryCLM {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : ι) : Matrix ι ι ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M x y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- `M ↦ G(g₀Ψ + M)` is `C²` at every Hermitian `M` (`Ring.inverse` at the unit `g₀Ψ + M − z`). -/
private theorem TwistGridWTail_contDiffAt_Gres {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hM : M.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    ContDiffAt ℝ 2 (fun M' : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      Gres (TwistGridWTail_Hm sz lam0 n M') z true) M := by
  have hu : IsUnit (TwistGridWTail_Hm sz lam0 n M - z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) :=
    isUnit_sub_smul_of_isHermitian (TwistGridWTail_Hm_herm sz lam0 n hM) hz
  have hA : ContDiff ℝ 2 (fun M' : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      TwistGridWTail_Hm sz lam0 n M' - z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) := by
    unfold TwistGridWTail_Hm
    exact (contDiff_const.add contDiff_id).sub contDiff_const
  have hinv : ContDiffAt ℝ 2 (Ring.inverse (M₀ := Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))
      (TwistGridWTail_Hm sz lam0 n M - z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) := by
    obtain ⟨u, hu'⟩ := hu
    rw [← hu']
    exact contDiffAt_ringInverse ℝ u
  have h := hinv.comp M hA.contDiffAt
  have hfun : (fun M' : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => Gres (TwistGridWTail_Hm sz lam0 n M') z true) =
      Ring.inverse ∘ (fun M' : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
        TwistGridWTail_Hm sz lam0 n M' - z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) := by
    funext M'; simp [Gres]
  rw [hfun]
  exact h

/-- **(H1)**: `Φ_b` is `C²` at every Hermitian `M`. -/
theorem TwistGridWTail_Phi_contDiffAt (u : ℝ) (σ : Fin 2 → Bool) (c₁ c₂ b : Zd d (sz.L n))
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ etaOf (BAmF sz lam0 E n) u) :
    ContDiffAt ℝ 2 (TwistGridWTail_Phi sz lam0 E n u σ c₁ c₂ b) M := by
  have hzabs : η ≤ |(ztOf (BAmF sz lam0 E n) (E n) u).im| := TwistGridWTail_abs_im (E n) u hη0 hη
  have hz0 : (ztOf (BAmF sz lam0 E n) (E n) u).im ≠ 0 := fun h => absurd hzabs (by rw [h]; simpa using hη0)
  have hG := TwistGridWTail_contDiffAt_Gres sz lam0 n hM hz0
  have hent : ∀ (σ' : Bool) (x y : Idx d (sz.L n) (sz.W n)), ContDiffAt ℝ 2 (fun M' : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      twChg (twGM sz lam0 E n u (TwistGridWTail_Hm sz lam0 n M')) σ' x y) M := by
    intro σ' x y
    cases σ'
    · simp only [twChg, twGM, Bool.false_eq_true, ite_false]
      exact (Complex.conjCLE.contDiff.contDiffAt).comp M ((TwistGridWTail_entryCLM y x).contDiff.contDiffAt.comp M hG)
    · simp only [twChg, twGM, ite_true]
      exact (TwistGridWTail_entryCLM x y).contDiff.contDiffAt.comp M hG
  unfold TwistGridWTail_Phi twL2M twLoopX
  refine ContDiffAt.mul contDiffAt_const ?_
  exact ContDiffAt.sum fun x _ => ContDiffAt.sum fun w _ => (hent _ _ _).mul (hent _ _ _)

/-- **(H2)**: `|Φ_b(M)| ≤ η⁻²` at Hermitian `M` (`W^{-2d}` against `W^{2d}` products of two entries `≤ η⁻¹`). -/
theorem TwistGridWTail_Phi_norm_le (u : ℝ) (σ : Fin 2 → Bool) (c₁ c₂ b : Zd d (sz.L n))
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ etaOf (BAmF sz lam0 E n) u) :
    ‖TwistGridWTail_Phi sz lam0 E n u σ c₁ c₂ b M‖ ≤ η⁻¹ ^ 2 := by
  have hzabs : η ≤ |(ztOf (BAmF sz lam0 E n) (E n) u).im| := TwistGridWTail_abs_im (E n) u hη0 hη
  have hHm := TwistGridWTail_Hm_herm sz lam0 n hM
  unfold TwistGridWTail_Phi twL2M twLoopX
  rw [norm_mul]
  have hS : ‖∑ x ∈ twBlk n b, ∑ w ∈ twBlk n c₁,
      twChg (twGM sz lam0 E n u (TwistGridWTail_Hm sz lam0 n M)) (σ 1) x w *
        twChg (twGM sz lam0 E n u (TwistGridWTail_Hm sz lam0 n M)) (σ 0) (twShift n c₂ w) x‖ ≤
      ((twBlk n b).card : ℝ) * ((twBlk n c₁).card : ℝ) * (η⁻¹ ^ 2) :=
    TwistGridWTail_norm_sum_sum_le _ _ _ fun x _ w _ => by
      rw [norm_mul, sq]
      exact mul_le_mul (TwistGridWTail_norm_chg_le hHm hη0 hzabs _ _ _) (TwistGridWTail_norm_chg_le hHm hη0 hzabs _ _ _)
        (norm_nonneg _) (inv_nonneg.2 hη0.le)
  rw [TwistGridWTail_card_blk, TwistGridWTail_card_blk] at hS
  have hwd1 := TwistGridWTail_wd_sq (sz := sz) (d := d) n
  calc _ ≤ ‖((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2‖ * (((sz.W n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ d * η⁻¹ ^ 2) :=
        mul_le_mul_of_nonneg_left hS (norm_nonneg _)
    _ = η⁻¹ ^ 2 := by
        have : ‖((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2‖ * (((sz.W n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ d) * η⁻¹ ^ 2 = η⁻¹ ^ 2 := by
          rw [hwd1, one_mul]
        linarith [this]

/-- **(H3)**: `‖∂²Φ_b(M)[y, y]‖ ≤ 6 η⁻⁴ ‖y‖²` at Hermitian `M, y`. -/
theorem TwistGridWTail_Phi_second (u : ℝ) (σ : Fin 2 → Bool) (c₁ c₂ b : Zd d (sz.L n)) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ etaOf (BAmF sz lam0 E n) u) {M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hM : M.IsHermitian) (hy : y.IsHermitian) :
    ‖fderiv ℝ (fderiv ℝ (TwistGridWTail_Phi sz lam0 E n u σ c₁ c₂ b)) M y y‖ ≤ 6 * η⁻¹ ^ 4 * ‖y‖ ^ 2 := by
  obtain ⟨φ₁, φ₂, h₀, h₁, hb, -⟩ := TwistGridWTail_Phi_jets sz lam0 E n u σ c₁ c₂ b hM hy hη0 hη
  rw [TwistGridWTail_fderiv2_of_line (fun M' hM' => TwistGridWTail_Phi_contDiffAt sz lam0 E n u σ c₁ c₂ b hM' hη0 hη) hM hy h₀ h₁]
  exact hb 0

/-- The observable is in the Hermitian test class of `Path/StepDecomp.lean` (the grid walk is that of `sz.withLam 0`). -/
theorem TwistGridWTail_hermTestFun (u : ℝ) (σ : Fin 2 → Bool) (c₁ c₂ b : Zd d (sz.L n)) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ etaOf (BAmF sz lam0 E n) u) :
    HermTestFun (sz.withLam 0) n (TwistGridWTail_Phi sz lam0 E n u σ c₁ c₂ b) :=
  ⟨fun M hM => TwistGridWTail_Phi_contDiffAt sz lam0 E n u σ c₁ c₂ b hM hη0 hη,
    ⟨η⁻¹ ^ 2, fun M hM => TwistGridWTail_Phi_norm_le sz lam0 E n u σ c₁ c₂ b hM hη0 hη⟩⟩

end Obs


end RBM.BA
