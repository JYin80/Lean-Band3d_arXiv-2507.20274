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
open RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph RBM.Ind

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
    change (1 - (v : ℂ) • BAMss _ _ _ (!σ 0) (!σ 1)) * BATheta _ _ _ _ _ _ (!σ 0) (!σ 1) = _
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
      _ ≤ K * ‖D‖ * K := by gcongr <;> exact hK t
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



/-! ### The coordinate algebra of the Gaussian increment (copy of the private `QVIdentity_cm_*`, `_gvar_*`, `_pair*`, `_sum_tri`, `_coord_sum`,
`Path/QVIdentity.lean:430-585`, `691566a` lineage): `Σ_c gvar_c ⟨X_c, f⟩ conj ⟨X_c, f'⟩ = Σ_{kl} svar_{kl} f_{lk} conj f'_{lk}` -/

section CoordAlgebra

variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W]

private theorem TwistGridWTail_cm_apply (c : CoordF d L W) (k l : Idx d L W) :
    coordinateMatrix d L W c k l = Xentry d L W (Pi.single c 1) k l := rfl

private theorem TwistGridWTail_cm_lt {i j : Idx d L W} (h : idxKey d L W i < idxKey d L W j)
    (b : Bool) :
    coordinateMatrix d L W (i, j, b) =
      Matrix.single i j (if b then (1 : ℂ) else Complex.I) +
        Matrix.single j i (if b then (1 : ℂ) else -Complex.I) := by
  have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
  ext k l
  simp only [TwistGridWTail_cm_apply, Xentry, Matrix.add_apply, Matrix.single_apply,
    Pi.single_apply, Prod.mk.injEq]
  cases b <;> split_ifs <;> (try push_cast) <;>
    (try simp only [zero_add, add_zero, mul_zero, mul_one, sub_zero, zero_sub]) <;> grind

private theorem TwistGridWTail_cm_diag_true (i : Idx d L W) :
    coordinateMatrix d L W (i, i, true) = Matrix.single i i (1 : ℂ) := by
  ext k l
  simp only [TwistGridWTail_cm_apply, Xentry, Matrix.single_apply, Pi.single_apply, Prod.mk.injEq]
  split_ifs <;> (try push_cast) <;>
    (try simp only [zero_add, add_zero, mul_zero, mul_one, sub_zero, zero_sub]) <;> grind

private theorem TwistGridWTail_cm_diag_false (i : Idx d L W) :
    coordinateMatrix d L W (i, i, false) = 0 := by
  ext k l
  simp only [TwistGridWTail_cm_apply, Xentry, Matrix.zero_apply, Pi.single_apply, Prod.mk.injEq]
  split_ifs <;> (try push_cast) <;>
    (try simp only [zero_add, add_zero, mul_zero, mul_one, sub_zero, zero_sub]) <;> grind

private theorem TwistGridWTail_cm_gt {i j : Idx d L W} (h : idxKey d L W j < idxKey d L W i)
    (b : Bool) :
    coordinateMatrix d L W (i, j, b) = 0 := by
  have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
  ext k l
  simp only [TwistGridWTail_cm_apply, Xentry, Matrix.zero_apply, Pi.single_apply, Prod.mk.injEq]
  cases b <;> split_ifs <;> (try push_cast) <;>
    (try simp only [zero_add, add_zero, mul_zero, mul_one, sub_zero, zero_sub]) <;> grind

/-- The diagonal coordinate variance is `S_ii` (the private `fineModel_gvarF_diag` of
`Gauss/FineModel.lean:233`, re-proved). -/
private theorem TwistGridWTail_gvar_diag (g : ℝ) (i : Idx d L W) (b : Bool) :
    (gvarF d L W g (i, i, b) : ℝ) = svarF d L W g i i := by
  change (if i = i then svarF d L W g i i else svarF d L W g i i / 2) = _
  simp

/-- The off-diagonal coordinate variance is `S_ij / 2` (the private `fineModel_gvarF_offDiag` of
`Gauss/FineModel.lean:241`, re-proved). -/
private theorem TwistGridWTail_gvar_offDiag (g : ℝ) (i j : Idx d L W) (b : Bool) (hij : i ≠ j) :
    (gvarF d L W g (i, j, b) : ℝ) = svarF d L W g i j / 2 := by
  change (if i = j then svarF d L W g i j else svarF d L W g i j / 2) = _
  simp [hij]

/-- The pairing `Σ_{k,l} X_{kl} f_{lk}` (the trace `tr(X F)` with `F_{lk} = f l k`). -/
private def TwistGridWTail_pair (X : Matrix (Idx d L W) (Idx d L W) ℂ)
    (f : Idx d L W → Idx d L W → ℂ) : ℂ :=
  ∑ k, ∑ l, X k l * f l k

private theorem TwistGridWTail_pair_single (i j : Idx d L W) (x : ℂ)
    (f : Idx d L W → Idx d L W → ℂ) :
    TwistGridWTail_pair (Matrix.single i j x) f = x * f j i := by
  simp only [TwistGridWTail_pair, Matrix.single_apply]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro l _ hl; simp [Ne.symm hl]
    · simp
  · intro k _ hk; simp [Ne.symm hk]
  · simp

private theorem TwistGridWTail_pair_add (X Y : Matrix (Idx d L W) (Idx d L W) ℂ)
    (f : Idx d L W → Idx d L W → ℂ) :
    TwistGridWTail_pair (X + Y) f = TwistGridWTail_pair X f + TwistGridWTail_pair Y f := by
  simp only [TwistGridWTail_pair, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

private theorem TwistGridWTail_pair_zero (f : Idx d L W → Idx d L W → ℂ) :
    TwistGridWTail_pair (0 : Matrix (Idx d L W) (Idx d L W) ℂ) f = 0 := by
  simp [TwistGridWTail_pair]

/-- Sum of an ordered-pair function over the three cases of `idxKey`. -/
private theorem TwistGridWTail_sum_tri (T : Idx d L W → Idx d L W → ℂ) :
    (∑ i, ∑ j, if idxKey d L W i < idxKey d L W j then T i j + T j i
      else if i = j then T i i else 0) = ∑ i, ∑ j, T i j := by
  have hpt : ∀ i j, (if idxKey d L W i < idxKey d L W j then T i j + T j i
      else if i = j then T i i else 0) =
      ((if idxKey d L W i < idxKey d L W j then T i j else 0) +
        (if idxKey d L W i < idxKey d L W j then T j i else 0)) +
        (if i = j then T i j else 0) := by
    intro i j
    rcases idxKey_lt_or_eq_or_lt d L W i j with h | h | h
    · have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
      simp [h, hij]
    · subst h; simp
    · have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
      simp [not_lt.mpr h.le, hij]
  have hswap : (∑ i, ∑ j, if idxKey d L W i < idxKey d L W j then T j i else 0) =
      ∑ i, ∑ j, if idxKey d L W j < idxKey d L W i then T i j else 0 := Finset.sum_comm
  calc (∑ i, ∑ j, if idxKey d L W i < idxKey d L W j then T i j + T j i
        else if i = j then T i i else 0)
      = (∑ i, ∑ j, if idxKey d L W i < idxKey d L W j then T i j else 0) +
          (∑ i, ∑ j, if idxKey d L W i < idxKey d L W j then T j i else 0) +
          ∑ i, ∑ j, (if i = j then T i j else 0) := by
        simp only [hpt, Finset.sum_add_distrib]
    _ = (∑ i, ∑ j, if idxKey d L W i < idxKey d L W j then T i j else 0) +
          (∑ i, ∑ j, if idxKey d L W j < idxKey d L W i then T i j else 0) +
          ∑ i, ∑ j, (if i = j then T i j else 0) := by rw [hswap]
    _ = ∑ i, ∑ j, (((if idxKey d L W i < idxKey d L W j then T i j else 0) +
          (if idxKey d L W j < idxKey d L W i then T i j else 0)) +
          (if i = j then T i j else 0)) := by simp only [Finset.sum_add_distrib]
    _ = ∑ i, ∑ j, T i j := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rcases idxKey_lt_or_eq_or_lt d L W i j with h | h | h
        · have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
          simp [h, hij, not_lt.mpr h.le]
        · subst h; simp
        · have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
          simp [h, hij, not_lt.mpr h.le]

/-- **Coordinate sum of a sesquilinear pairing.**  For every pair of kernels `f, f'`,
`Σ_c gvar_c ⟨X_c, f⟩ conj ⟨X_c, f'⟩ = Σ_{k,l} svar_{kl} f_{lk} conj f'_{lk}`. -/
private theorem TwistGridWTail_coord_sum (g : ℝ) (f f' : Idx d L W → Idx d L W → ℂ) :
    ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
        (TwistGridWTail_pair (coordinateMatrix d L W c) f *
          (starRingEnd ℂ) (TwistGridWTail_pair (coordinateMatrix d L W c) f')) =
      ∑ k, ∑ l, (svarF d L W g k l : ℂ) * (f l k * (starRingEnd ℂ) (f' l k)) := by
  have hc : ∀ F : CoordF d L W → ℂ,
      ∑ c : CoordF d L W, F c =
        ∑ i : Idx d L W, ∑ j : Idx d L W, (F (i, j, true) + F (i, j, false)) := by
    intro F
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun j _ => Fintype.sum_bool _
  rw [← TwistGridWTail_sum_tri, hc]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rcases idxKey_lt_or_eq_or_lt d L W i j with h | h | h
  · have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
    rw [ite_eq_left h, TwistGridWTail_cm_lt h, TwistGridWTail_cm_lt h,
      TwistGridWTail_gvar_offDiag g i j true hij,
      TwistGridWTail_gvar_offDiag g i j false hij, svarF_comm d L W g j i]
    simp only [TwistGridWTail_pair_add, TwistGridWTail_pair_single, ite_true, Bool.false_eq_true,
      ite_false, map_add, map_mul, map_neg, map_one, Complex.conj_I]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  · subst h
    rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl, TwistGridWTail_cm_diag_true,
      TwistGridWTail_cm_diag_false, TwistGridWTail_gvar_diag, TwistGridWTail_gvar_diag]
    simp [TwistGridWTail_pair_single, TwistGridWTail_pair_zero]
  · have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
    rw [ite_eq_right (not_lt.mpr h.le), ite_eq_right hij, TwistGridWTail_cm_gt h, TwistGridWTail_cm_gt h]
    simp [TwistGridWTail_pair_zero]

end CoordAlgebra

/-! ## 5. The variance of the frozen linear functional: `linTrVar (Σ_b κ_b ∇Φ_b) ≤ Re Σ κ κ̄ twEEM`

Copies (stem `TwistGridWTail_`) of the private helpers of `Path/DifREP2.lean:805-917` (`difRepTail_hasDerivAt_dir`,
`_linTr_neg_I_smul`, `_seqXmat_single`, `_linTrVar_eq`, `_sq_re_le`, `_sq_im_le`, `_linTrVar_le`, `_trace_eq`), then the identity
`Σ_c gvar_c |Σ_{pq} f_{pq} (X_c)_{pq}|² = Σ_{kl} S_{kl} |f_{kl}|²` with `S = W^{-d}·1[[k]=[l]]` (coupling `0`). -/

section QV

open scoped Matrix.Norms.L2Operator

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)

private theorem TwistGridWTail_hasDerivAt_dir {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ψ : Matrix ι ι ℂ → ℂ} {M : Matrix ι ι ℂ} (X : Matrix ι ι ℂ) (hd : DifferentiableAt ℝ Ψ M) :
    HasDerivAt (fun y : ℝ => Ψ (M + (y : ℂ) • X)) (fderiv ℝ Ψ M X) 0 := by
  have hadd : HasDerivAt (fun t' : ℝ => M + t' • X) X 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add M
  have hp0 : HasDerivAt (fun t' : ℝ => Ψ (M + t' • X)) (fderiv ℝ Ψ M X) 0 := by
    have h1 : HasFDerivAt Ψ (fderiv ℝ Ψ (M + (0 : ℝ) • X)) (M + (0 : ℝ) • X) := by
      simpa using hd.hasFDerivAt
    have h2 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) h1 hadd
    simp only [zero_smul, add_zero, Function.comp_def] at h2
    exact h2
  simpa only [Complex.coe_smul] using hp0

private theorem TwistGridWTail_linTr_neg_I_smul (szz : Sizes d)
    (A X : Matrix (Idx d (szz.L n) (szz.W n)) (Idx d (szz.L n) (szz.W n)) ℂ) :
    linTr n ((-Complex.I) • A) X = (Matrix.trace (A * X)).im := by
  unfold linTr
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  ring

private theorem TwistGridWTail_seqXmat_single (szz : Sizes d) (c : CoordF d (szz.L n) (szz.W n)) :
    Sizes.seqXmat szz n (Pi.single (⟨n, c⟩ : Sizes.SeqCoord szz) 1) = coordinateMatrix d (szz.L n) (szz.W n) c := by
  have hs : Sizes.slice szz n (Pi.single (⟨n, c⟩ : Sizes.SeqCoord szz) 1) = Pi.single c 1 := by
    funext c'
    change (Pi.single (⟨n, c⟩ : Sizes.SeqCoord szz) (1 : ℝ) : Sizes.SeqCoord szz → ℝ) ⟨n, c'⟩ =
      (Pi.single c (1 : ℝ) : CoordF d (szz.L n) (szz.W n) → ℝ) c'
    by_cases h : c' = c
    · subst h; simp
    · have h' : (⟨n, c'⟩ : Sizes.SeqCoord szz) ≠ ⟨n, c⟩ := fun he => h (eq_of_heq (Sigma.mk.inj he).2)
      rw [Pi.single_eq_of_ne h', Pi.single_eq_of_ne h]
  unfold Sizes.seqXmat coordinateMatrix
  rw [hs]

private theorem TwistGridWTail_linTrVar_eq (szz : Sizes d) (A : Matrix (Idx d (szz.L n) (szz.W n)) (Idx d (szz.L n) (szz.W n)) ℂ) :
    linTrVar n A = ∑ c : CoordF d (szz.L n) (szz.W n), (gvarF d (szz.L n) (szz.W n) (szz.lam n) c : ℝ) *
      (linTr n A (coordinateMatrix d (szz.L n) (szz.W n) c)) ^ 2 := by
  classical
  rw [← vB_self (sz := szz)]
  unfold vB coordFinset
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Function.Embedding.sigmaMk_apply, TwistGridWTail_seqXmat_single]
  change (gvarF d (szz.L n) (szz.W n) (szz.lam n) c : ℝ) * _ * _ = _
  ring

private theorem TwistGridWTail_sq_re_le (z : ℂ) : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
  calc z.re ^ 2 = |z.re| ^ 2 := (sq_abs _).symm
    _ ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm z) 2

private theorem TwistGridWTail_sq_im_le (z : ℂ) : z.im ^ 2 ≤ ‖z‖ ^ 2 := by
  calc z.im ^ 2 = |z.im| ^ 2 := (sq_abs _).symm
    _ ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm z) 2

private theorem TwistGridWTail_linTrVar_le (szz : Sizes d)
    (A : Matrix (Idx d (szz.L n) (szz.W n)) (Idx d (szz.L n) (szz.W n)) ℂ) (D : CoordF d (szz.L n) (szz.W n) → ℂ)
    (hD : ∀ c, Matrix.trace (A * coordinateMatrix d (szz.L n) (szz.W n) c) = D c) :
    linTrVar n A ≤ ∑ c : CoordF d (szz.L n) (szz.W n), (gvarF d (szz.L n) (szz.W n) (szz.lam n) c : ℝ) * ‖D c‖ ^ 2 ∧
    linTrVar n ((-Complex.I) • A) ≤
      ∑ c : CoordF d (szz.L n) (szz.W n), (gvarF d (szz.L n) (szz.W n) (szz.lam n) c : ℝ) * ‖D c‖ ^ 2 := by
  constructor
  · rw [TwistGridWTail_linTrVar_eq]
    refine Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left ?_ (gvarF d (szz.L n) (szz.W n) (szz.lam n) c).2
    have : linTr n A (coordinateMatrix d (szz.L n) (szz.W n) c) = (D c).re := by rw [← hD c]; rfl
    rw [this]
    exact TwistGridWTail_sq_re_le _
  · rw [TwistGridWTail_linTrVar_eq]
    refine Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left ?_ (gvarF d (szz.L n) (szz.W n) (szz.lam n) c).2
    rw [TwistGridWTail_linTr_neg_I_smul, hD c]
    exact TwistGridWTail_sq_im_le _

/-- The directional derivative of `Φ_b` at Hermitian `M` along Hermitian `X` is the pairing with the gradient `twDerM`. -/
theorem TwistGridWTail_fderiv_eq (u : ℝ) (σ : Fin 2 → Bool) (c₁ c₂ b : Zd d (sz.L n)) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ etaOf (BAmF sz lam0 E n) u) {M X : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hM : M.IsHermitian) (hX : X.IsHermitian) :
    fderiv ℝ (TwistGridWTail_Phi sz lam0 E n u σ c₁ c₂ b) M X =
      ∑ p, ∑ q, twDerM sz lam0 E n u (TwistGridWTail_Hm sz lam0 n M) σ b c₁ c₂ p q * X p q := by
  obtain ⟨φ₁, φ₂, h₀, -, -, h0⟩ := TwistGridWTail_Phi_jets sz lam0 E n u σ c₁ c₂ b hM hX hη0 hη
  have hd : DifferentiableAt ℝ (TwistGridWTail_Phi sz lam0 E n u σ c₁ c₂ b) M :=
    (TwistGridWTail_Phi_contDiffAt sz lam0 E n u σ c₁ c₂ b hM hη0 hη).differentiableAt (by norm_num)
  have h1 := TwistGridWTail_hasDerivAt_dir X hd
  rw [← h0]
  exact h1.unique (h₀ 0)

/-- `svar` of the coupling-`0` fine model is the weight `W^{-d} S^{(B)}_{[k][l]}` of `twEEM`. -/
theorem TwistGridWTail_svarF_zero (x y : Idx d (sz.L n) (sz.W n)) :
    ((svarF d (sz.L n) (sz.W n) ((sz.withLam 0).lam n) x y : ℝ) : ℂ) = TwistGridWTail_wS (sz := sz) lam0 E n x y := by
  unfold svarF TwistGridWTail_wS
  have h0 : (sz.withLam 0).lam n = 0 := rfl
  rw [h0]
  by_cases h : (split d (sz.L n) (sz.W n) x).1 = (split d (sz.L n) (sz.W n) y).1
  · simp [baFM, SBR, sbKernelR, h]
  · simp [baFM, SBR, sbKernelR, h, sub_eq_zero]

/-- **The variance identity**: `Σ_c gvar_c |Σ_{pq} f_{pq} (X_c)_{pq}|² = Re Σ_{kl} W^{-d} S_{kl} f_{kl} conj f_{kl}`. -/
theorem TwistGridWTail_coord_sum_eq (f : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) :
    ∑ c : CoordF d (sz.L n) (sz.W n), (gvarF d (sz.L n) (sz.W n) ((sz.withLam 0).lam n) c : ℝ) *
      ‖∑ p, ∑ q, f p q * coordinateMatrix d (sz.L n) (sz.W n) c p q‖ ^ 2 =
    (∑ k, ∑ l, TwistGridWTail_wS (sz := sz) lam0 E n k l * (f k l * (starRingEnd ℂ) (f k l))).re := by
  have h := TwistGridWTail_coord_sum (d := d) (L := sz.L n) (W := sz.W n) ((sz.withLam 0).lam n)
    (fun l k => f k l) (fun l k => f k l)
  have hpair : ∀ c : CoordF d (sz.L n) (sz.W n), TwistGridWTail_pair (coordinateMatrix d (sz.L n) (sz.W n) c) (fun l k => f k l) =
      ∑ p, ∑ q, f p q * coordinateMatrix d (sz.L n) (sz.W n) c p q := fun c => by
    unfold TwistGridWTail_pair
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  simp only [hpair] at h
  have hre := congrArg Complex.re h
  rw [Complex.re_sum] at hre
  have hL : ∀ c : CoordF d (sz.L n) (sz.W n), (((gvarF d (sz.L n) (sz.W n) ((sz.withLam 0).lam n) c : ℝ) : ℂ) *
      ((∑ p, ∑ q, f p q * coordinateMatrix d (sz.L n) (sz.W n) c p q) *
        (starRingEnd ℂ) (∑ p, ∑ q, f p q * coordinateMatrix d (sz.L n) (sz.W n) c p q))).re =
      (gvarF d (sz.L n) (sz.W n) ((sz.withLam 0).lam n) c : ℝ) *
        ‖∑ p, ∑ q, f p q * coordinateMatrix d (sz.L n) (sz.W n) c p q‖ ^ 2 := by
    intro c
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.ofReal_re]
  simp only [hL] at hre
  rw [hre]
  congr 1
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [TwistGridWTail_svarF_zero]

private theorem TwistGridWTail_sum4_swap {α β : Type*} [Fintype α] [Fintype β] (F : α → α → β → β → ℂ) :
    ∑ a, ∑ a', ∑ k, ∑ l, F a a' k l = ∑ k, ∑ l, ∑ a, ∑ a', F a a' k l := by
  calc ∑ a, ∑ a', ∑ k, ∑ l, F a a' k l = ∑ a, ∑ k, ∑ a', ∑ l, F a a' k l :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ a', ∑ l, F a a' k l := Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ l, ∑ a', F a a' k l := Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ a, ∑ a', F a a' k l := Finset.sum_congr rfl fun k _ => Finset.sum_comm

/-- **The variance proxy of the frozen gradient** (`c = 1`, one slot): for the weights `κ`, `linTrVar` of `Σ_b κ_b ∇Φ_b(M)` and of
`(-I)` times it are at most `Re Σ_{b,b'} κ_b conj(κ_{b'}) (Ẽ⊗Ẽ)_u(g₀Ψ + M)(b,b')` (twin of `difRepTail_linTrVar_le_QV`, `Path/DifREP2.lean:1007`,
without the loop factor `k`: the two terms of (D.2) sit inside `twDerM`). -/
theorem TwistGridWTail_linTrVar_le_QV (u : ℝ) (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ etaOf (BAmF sz lam0 E n) u) (κ : Zd d (sz.L n) → ℂ)
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian) :
    linTrVar (sz := sz.withLam 0) n (∑ b, κ b • gradMat (TwistGridWTail_Phi sz lam0 E n u σ c₁ c₂ b) M) ≤
      (∑ b, ∑ b', κ b * (starRingEnd ℂ) (κ b') * twEEM sz lam0 E n u (TwistGridWTail_Hm sz lam0 n M) σ b b' c₁ c₂).re ∧
    linTrVar (sz := sz.withLam 0) n ((-Complex.I) • ∑ b, κ b • gradMat (TwistGridWTail_Phi sz lam0 E n u σ c₁ c₂ b) M) ≤
      (∑ b, ∑ b', κ b * (starRingEnd ℂ) (κ b') * twEEM sz lam0 E n u (TwistGridWTail_Hm sz lam0 n M) σ b b' c₁ c₂).re := by
  set f : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ := fun p q =>
    ∑ b, κ b * twDerM sz lam0 E n u (TwistGridWTail_Hm sz lam0 n M) σ b c₁ c₂ p q with hf
  set D : CoordF d (sz.L n) (sz.W n) → ℂ := fun c => ∑ b, κ b *
    fderiv ℝ (TwistGridWTail_Phi sz lam0 E n u σ c₁ c₂ b) M (coordinateMatrix d (sz.L n) (sz.W n) c) with hD
  have hDtr : ∀ c, Matrix.trace ((∑ b, κ b • gradMat (TwistGridWTail_Phi sz lam0 E n u σ c₁ c₂ b) M) *
      coordinateMatrix d (sz.L n) (sz.W n) c) = D c := by
    intro c
    rw [Matrix.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ← fderiv_eq_trace_gradMat M (coordinateMatrix_isHermitian _ _ _ c)]
  obtain ⟨h1, h2⟩ := TwistGridWTail_linTrVar_le n (sz.withLam 0) _ D hDtr
  have hDf : ∀ c, D c = ∑ p, ∑ q, f p q * coordinateMatrix d (sz.L n) (sz.W n) c p q := by
    intro c
    simp only [hD, hf, TwistGridWTail_fderiv_eq sz lam0 E n u σ c₁ c₂ _ hη0 hη hM (coordinateMatrix_isHermitian _ _ _ c)]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun b _ => by ring
  have hS : ∑ c : CoordF d (sz.L n) (sz.W n), (gvarF d (sz.L n) (sz.W n) ((sz.withLam 0).lam n) c : ℝ) * ‖D c‖ ^ 2 =
      (∑ b, ∑ b', κ b * (starRingEnd ℂ) (κ b') * twEEM sz lam0 E n u (TwistGridWTail_Hm sz lam0 n M) σ b b' c₁ c₂).re := by
    simp only [hDf]
    rw [TwistGridWTail_coord_sum_eq sz lam0 E n f]
    congr 1
    simp only [TwistGridWTail_twEEM_eq, Finset.mul_sum]
    rw [TwistGridWTail_sum4_swap]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [hf, map_sum]
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b' _ => ?_
    simp only [map_mul]
    ring
  exact ⟨h1.trans_eq hS, h2.trans_eq hS⟩

end QV


/-! ### The conditional exponential moment of a frozen linear functional (copies of `Path/DifREP2.lean:1051-1187`, `76b840e`) -/

section Frozen

variable {d : ℕ} {sz : Sizes d}

private theorem TwistGridWTail_measurable_seqXmat (n : ℕ) : Measurable (Sizes.seqXmat sz n) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j =>
    (measurable_Xentry d (sz.L n) (sz.W n) i j).comp (Sizes.measurable_slice sz n)

private theorem TwistGridWTail_linTr_eq_sum (n : ℕ)
    (A X : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    linTr n A X = ∑ i : Idx d (sz.L n) (sz.W n), ∑ k : Idx d (sz.L n) (sz.W n),
      (A i k * X k i).re := by
  unfold linTr
  rw [Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]

private theorem TwistGridWTail_measurable_linTr_uncurry (n : ℕ) :
    Measurable (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ × Sizes.SeqΩ sz =>
      linTr n p.1 (Sizes.seqXmat sz n p.2)) := by
  have heq : (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ × Sizes.SeqΩ sz =>
      linTr n p.1 (Sizes.seqXmat sz n p.2))
      = fun p => ∑ i : Idx d (sz.L n) (sz.W n), ∑ k : Idx d (sz.L n) (sz.W n),
          (p.1 i k * Sizes.seqXmat sz n p.2 k i).re :=
    funext fun p => TwistGridWTail_linTr_eq_sum n p.1 (Sizes.seqXmat sz n p.2)
  rw [heq]
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ => ?_
  have hM : Measurable
      (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ × Sizes.SeqΩ sz => p.1 i k) :=
    Measurable.eval_matrix (i := i) (j := k) measurable_fst
  have hX : Measurable
      (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ × Sizes.SeqΩ sz =>
        Sizes.seqXmat sz n p.2 k i) :=
    Measurable.eval_matrix (i := k) (j := i) ((TwistGridWTail_measurable_seqXmat n).comp measurable_snd)
  exact Complex.measurable_re.comp (hM.mul hX)

private theorem TwistGridWTail_measurable_linTr_seqXmat (n : ℕ)
    (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    Measurable (fun x : Sizes.SeqΩ sz => linTr n A (Sizes.seqXmat sz n x)) := by
  have heq : (fun x : Sizes.SeqΩ sz => linTr n A (Sizes.seqXmat sz n x))
      = fun x => ∑ i : Idx d (sz.L n) (sz.W n), ∑ k : Idx d (sz.L n) (sz.W n),
          (A i k * Sizes.seqXmat sz n x k i).re :=
    funext fun x => TwistGridWTail_linTr_eq_sum n A (Sizes.seqXmat sz n x)
  rw [heq]
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ => ?_
  exact Complex.measurable_re.comp
    (measurable_const.mul (Measurable.eval_matrix (i := k) (j := i) (TwistGridWTail_measurable_seqXmat n)))

private theorem TwistGridWTail_mgf_linTr_seqXmat (n : ℕ)
    (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (r : ℝ) :
    mgf (fun x => linTr n A (Sizes.seqXmat sz n x)) (Sizes.seqP sz) r
      = Real.exp (linTrVar n A * r ^ 2 / 2) := by
  have hmeas : Measurable (fun x : Sizes.SeqΩ sz => linTr n A (Sizes.seqXmat sz n x)) :=
    TwistGridWTail_measurable_linTr_seqXmat n A
  have hlaw : HasLaw (fun x => linTr n A (Sizes.seqXmat sz n x))
      (gaussianReal 0 (NNReal.mk (linTrVar n A) (linTrVar_nonneg n A))) (Sizes.seqP sz) :=
    ⟨hmeas.aemeasurable, map_linTr_seqXmat n A⟩
  rw [mgf_gaussianReal hlaw]
  congr 1
  push_cast [NNReal.coe_mk]
  ring

private instance TwistGridWTail_standardBorelMatrix (n : ℕ) :
    StandardBorelSpace (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
  inferInstanceAs (StandardBorelSpace (Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ))

/-- **The conditional exponential moment of the frozen linear functional**, with the random
variance: for a `filt sz j`-measurable direction `A`, a.e. `𝔼[exp (r √Δ linTr (A) X_{j+1}) | F_j]
= exp (linTrVar (A ω) (r √Δ)² / 2)`; `condExp_freeze` and the Gaussian mgf (the first half of the
merged `condMGF_le`, `Path/Markov.lean:572-604`). -/
private theorem TwistGridWTail_condExp_exp {n j : ℕ}
    {A : PathΩ sz → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hA : Measurable[filt sz j] A) (Δ r : ℝ)
    (hInt : Integrable (fun ω : PathΩ sz => Real.exp (r * (Real.sqrt Δ *
      linTr n (A ω) (Sizes.seqXmat sz n (ω (j + 1)))))) (pathP sz)) :
    (pathP sz)[fun ω : PathΩ sz => Real.exp (r * (Real.sqrt Δ *
        linTr n (A ω) (Sizes.seqXmat sz n (ω (j + 1))))) | filt sz j]
      =ᵐ[pathP sz] fun ω => Real.exp (linTrVar n (A ω) * (r * Real.sqrt Δ) ^ 2 / 2) := by
  set Gr : PathΩ sz → ℝ := fun ρ => Real.exp (r * (Real.sqrt Δ *
    linTr n (A ρ) (Sizes.seqXmat sz n (ρ (j + 1))))) with hGrdef
  set Fr : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → Sizes.SeqΩ sz → ℝ :=
    fun y x => Real.exp (r * (Real.sqrt Δ * linTr n y (Sizes.seqXmat sz n x))) with hFrdef
  have hFrmeas : Measurable
      (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ × Sizes.SeqΩ sz =>
        Fr p.1 p.2) := by
    have h1 : Measurable
        (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ × Sizes.SeqΩ sz =>
          linTr n p.1 (Sizes.seqXmat sz n p.2)) := TwistGridWTail_measurable_linTr_uncurry n
    exact Real.measurable_exp.comp ((h1.const_mul _).const_mul _)
  have hGreq : (fun ρ : PathΩ sz => Fr (A ρ) (ρ (j + 1))) = Gr := by
    funext ρ; rw [hFrdef, hGrdef]
  have hfreeze := condExp_freeze j hA hFrmeas (hGreq ▸ hInt)
  have hRHS : (fun ρ : PathΩ sz => ∫ x, Fr (A ρ) x ∂ (Sizes.seqP sz))
      = fun ρ => Real.exp (linTrVar n (A ρ) * (r * Real.sqrt Δ) ^ 2 / 2) := by
    funext ρ
    have hmgf := TwistGridWTail_mgf_linTr_seqXmat n (A ρ) (r * Real.sqrt Δ)
    rw [mgf] at hmgf
    rw [← hmgf]
    have hpt : ∀ x, Fr (A ρ) x
        = Real.exp ((r * Real.sqrt Δ) * linTr n (A ρ) (Sizes.seqXmat sz n x)) := by
      intro x; rw [hFrdef]; ring_nf
    simp_rw [hpt]
  rw [hRHS] at hfreeze
  rw [hGreq] at hfreeze
  exact hfreeze

end Frozen

/-! ## 6. The conditional exponential moment of the first-chaos increment `stepZCN` with a random variance proxy -/

section ZGeneric

open scoped Matrix.Norms.L2Operator

variable {d : ℕ} {sz : Sizes d}

/-- **The conditional mgf of `Re ζ` and `Im ζ`**, `ζ = stepZCN` of any label family in the Hermitian test class with the kernel `U`
(twin of the second half of `difRepTail_condMGF_Z`, `Path/DifREP2.lean:1476-1537`; the loop-specific part is the hypotheses
`hRe`, `hIm`, `hv` on a variance proxy `v`): if `linTrVar` of the frozen gradient direction (and of `(-I)` times it) is at most `v ω`, and
`Δ v ≤ c0`, then both parts are exponentially integrable and have conditional mgf at most `exp (r² Δ v / 2)` given `F_j`. -/
theorem TwistGridWTail_condMGF_generic (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type} [Fintype ι]
    {Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ} (hΦ : ∀ a, HermTestFun sz n (Φ a)) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), M.IsHermitian → y.IsHermitian →
      ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n) (U : ι → ι → ℂ) (b₀ : ι) {c0 : ℝ} (hc0 : 0 ≤ c0) (v : PathΩ sz → ℝ)
    (hRe : ∀ ω, linTrVar n (AbCN sz s t K n j Φ U b₀ ω) ≤ v ω)
    (hIm : ∀ ω, linTrVar n ((-Complex.I) • AbCN sz s t K n j Φ U b₀ ω) ≤ v ω)
    (hv : ∀ ω, gridStep s t K n * v ω ≤ c0) (r : ℝ) :
    Integrable (fun ω => Real.exp (r * stepZCN_re sz s t K n j Φ U b₀ ω)) (pathP sz) ∧
    Integrable (fun ω => Real.exp (r * stepZCN_im sz s t K n j Φ U b₀ ω)) (pathP sz) ∧
    (pathP sz)[fun ω => Real.exp (r * stepZCN_re sz s t K n j Φ U b₀ ω) | filt sz j] ≤ᵐ[pathP sz]
      (fun ω => Real.exp (r ^ 2 * (gridStep s t K n * v ω) / 2)) ∧
    (pathP sz)[fun ω => Real.exp (r * stepZCN_im sz s t K n j Φ U b₀ ω) | filt sz j] ≤ᵐ[pathP sz]
      (fun ω => Real.exp (r ^ 2 * (gridStep s t K n * v ω) / 2)) := by
  have hIntRe := integrable_stepZCN_re_of_hermTestFun sz s t K n j hΦ hC₂ hΔ U b₀
  have hIntIm := integrable_stepZCN_im_of_hermTestFun sz s t K n j hΦ hC₂ hΔ U b₀
  obtain ⟨-, hAm, -, -⟩ := stepDecompCN sz s t K n j hΦ hC₂ hΔ U b₀ hIntRe hIntIm
  have hZ := stepDecompCN_Z_subG sz s t K n j hΦ U b₀ Set.univ MeasurableSet.univ c0 hc0
    (fun ω _ => (mul_le_mul_of_nonneg_left (hRe ω) hΔ).trans (hv ω))
    (fun ω _ => (mul_le_mul_of_nonneg_left (hIm ω) hΔ).trans (hv ω))
  have hIre : Integrable (fun ω : PathΩ sz => Real.exp (r * (Real.sqrt (gridStep s t K n) *
      linTr n (AbCN sz s t K n j Φ U b₀ ω) (Sizes.seqXmat sz n (ω (j + 1)))))) (pathP sz) := by
    have := hZ.1.integrable_exp_mul r
    simpa [Set.indicator_univ, stepZCN_re] using this
  have hIim : Integrable (fun ω : PathΩ sz => Real.exp (r * (Real.sqrt (gridStep s t K n) *
      linTr n ((-Complex.I) • AbCN sz s t K n j Φ U b₀ ω) (Sizes.seqXmat sz n (ω (j + 1)))))) (pathP sz) := by
    have := hZ.2.integrable_exp_mul r
    simpa [Set.indicator_univ, stepZCN_im] using this
  have hAm' : Measurable[filt sz j] (fun ω => (-Complex.I) • AbCN sz s t K n j Φ U b₀ ω) := hAm.const_smul (-Complex.I)
  have hce_re := TwistGridWTail_condExp_exp hAm (gridStep s t K n) r hIre
  have hce_im := TwistGridWTail_condExp_exp hAm' (gridStep s t K n) r hIim
  have hsq : (r * Real.sqrt (gridStep s t K n)) ^ 2 = r ^ 2 * gridStep s t K n := by
    rw [mul_pow, Real.sq_sqrt hΔ]
  have hrr : 0 ≤ r ^ 2 * gridStep s t K n := by positivity
  refine ⟨hIre, hIim, ?_, ?_⟩
  · refine hce_re.le.trans (Eventually.of_forall fun ω => ?_)
    refine Real.exp_le_exp.2 ?_
    rw [hsq]
    nlinarith [mul_le_mul_of_nonneg_right (hRe ω) hrr]
  · refine hce_im.le.trans (Eventually.of_forall fun ω => ?_)
    refine Real.exp_le_exp.2 ?_
    rw [hsq]
    nlinarith [mul_le_mul_of_nonneg_right (hIm ω) hrr]

end ZGeneric

/-! ## 7. The second-order part: moment fields of the weighted `Y` increments

Twin of `AzumaProxyN_YfieldsW` (`Induction/AzumaProxyN2.lean:1025`, loops only) for an arbitrary label family, through `stepDecompCN`: the increment
`y = ξ − ζ` (`ξ` a.e. the `stepXiCN` of the kernel `(·, a) ↦ κ_a`, `ζ = stepZCN`) is `filt (j+1)`-measurable, has conditional mean zero and
`E ‖y‖² ≤ 4 ((Σ|κ|) C₂/2)² Δ² · 768 N⁸` (`stepDecompCN_Y_sq`, `integral_normPow4_incr_le`). -/

section YGeneric

open scoped Matrix.Norms.L2Operator

variable {d : ℕ} {sz : Sizes d}

/-- The draw `ω l` is `filt sz k`-measurable for `l ≤ k` (copy of the private `gridAsm_measurable_coord`, `Induction/GridAssemblyN.lean:872`). -/
private theorem TwistGridWTail_measurable_coord {k l : ℕ} (hl : l ≤ k) : Measurable[filt sz k] (fun ω : PathΩ sz => ω l) := by
  have : (fun ω : PathΩ sz => ω l) = (fun g : Set.Iic k → Sizes.SeqΩ sz => g ⟨l, hl⟩) ∘
      (Preorder.restrictLe (π := fun _ : ℕ => Sizes.SeqΩ sz) k) := rfl
  rw [this]
  exact (measurable_pi_apply (⟨l, hl⟩ : Set.Iic k)).comp (comap_measurable (Preorder.restrictLe (π := fun _ : ℕ => Sizes.SeqΩ sz) k))

/-- `stepZCN` is `filt (j+1)`-measurable (`A_j` is `filt j`-measurable, `X_{j+1}` is `filt (j+1)`-measurable, `linTr` is jointly measurable). -/
theorem TwistGridWTail_measurable_stepZCN (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*} [Fintype ι]
    (Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ) (U : ι → ι → ℂ) (b₀ : ι)
    (hAm : Measurable[filt sz j] (fun ω => AbCN sz s t K n j Φ U b₀ ω)) :
    Measurable[filt sz (j + 1)] (fun ω => stepZCN sz s t K n j Φ U b₀ ω) := by
  have hA : Measurable[filt sz (j + 1)] (fun ω => AbCN sz s t K n j Φ U b₀ ω) := hAm.mono ((filt sz).mono (Nat.le_succ j)) le_rfl
  have hX : Measurable[filt sz (j + 1)] (fun ω : PathΩ sz => ω (j + 1)) := TwistGridWTail_measurable_coord le_rfl
  have hpair : Measurable[filt sz (j + 1)] (fun ω : PathΩ sz => (AbCN sz s t K n j Φ U b₀ ω, ω (j + 1))) := hA.prodMk hX
  have hlin := TwistGridWTail_measurable_linTr_uncurry (sz := sz) n
  have hre : Measurable[filt sz (j + 1)] (fun ω => stepZCN_re sz s t K n j Φ U b₀ ω) := by
    unfold stepZCN_re
    exact (hlin.comp hpair).const_mul _
  have him : Measurable[filt sz (j + 1)] (fun ω => stepZCN_im sz s t K n j Φ U b₀ ω) := by
    unfold stepZCN_im
    have h2 : Measurable[filt sz (j + 1)] (fun ω : PathΩ sz => ((-Complex.I) • AbCN sz s t K n j Φ U b₀ ω, ω (j + 1))) :=
      (hA.const_smul (-Complex.I)).prodMk hX
    exact (hlin.comp h2).const_mul _
  unfold stepZCN
  exact (Complex.measurable_ofReal.comp hre).add (measurable_const.mul (Complex.measurable_ofReal.comp him))

/-- **The moment fields of the weighted second-order increment** `y = ξ − stepZCN` (see the section header). -/
theorem TwistGridWTail_Y_fields (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type} [Fintype ι]
    {Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ} (hΦ : ∀ a, HermTestFun sz n (Φ a)) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), M.IsHermitian → y.IsHermitian →
      ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n) (κ : ι → ℂ) (b₀ : ι) (ξ : PathΩ sz → ℂ)
    (hξ : ξ =ᵐ[pathP sz] stepXiCN sz s t K n j Φ (fun _ a => κ a) b₀) (hξm : Measurable[filt sz (j + 1)] ξ) :
    Measurable[filt sz (j + 1)] (fun ω => ξ ω - stepZCN sz s t K n j Φ (fun _ a => κ a) b₀ ω) ∧
    (pathP sz)[fun ω => (ξ ω - stepZCN sz s t K n j Φ (fun _ a => κ a) b₀ ω).re | filt sz j] =ᵐ[pathP sz] 0 ∧
    (pathP sz)[fun ω => (ξ ω - stepZCN sz s t K n j Φ (fun _ a => κ a) b₀ ω).im | filt sz j] =ᵐ[pathP sz] 0 ∧
    MemLp (fun ω => (ξ ω - stepZCN sz s t K n j Φ (fun _ a => κ a) b₀ ω).re) 2 (pathP sz) ∧
    MemLp (fun ω => (ξ ω - stepZCN sz s t K n j Φ (fun _ a => κ a) b₀ ω).im) 2 (pathP sz) ∧
    ∫ ω, (ξ ω - stepZCN sz s t K n j Φ (fun _ a => κ a) b₀ ω).re ^ 2 ∂(pathP sz) ≤
      4 * ((∑ a, ‖κ a‖) * (C₂ / 2)) ^ 2 * gridStep s t K n ^ 2 * (768 * ((sz.size n : ℕ) : ℝ) ^ 8) ∧
    ∫ ω, (ξ ω - stepZCN sz s t K n j Φ (fun _ a => κ a) b₀ ω).im ^ 2 ∂(pathP sz) ≤
      4 * ((∑ a, ‖κ a‖) * (C₂ / 2)) ^ 2 * gridStep s t K n ^ 2 * (768 * ((sz.size n : ℕ) : ℝ) ^ 8) := by
  set U : ι → ι → ℂ := fun _ a => κ a with hU
  have hIntRe := integrable_stepZCN_re_of_hermTestFun sz s t K n j hΦ hC₂ hΔ U b₀
  have hIntIm := integrable_stepZCN_im_of_hermTestFun sz s t K n j hΦ hC₂ hΔ U b₀
  obtain ⟨-, hAm, hbound, hmeanY⟩ := stepDecompCN sz s t K n j hΦ hC₂ hΔ U b₀ hIntRe hIntIm
  have hZm := TwistGridWTail_measurable_stepZCN s t K n j Φ U b₀ hAm
  set y : PathΩ sz → ℂ := fun ω => ξ ω - stepZCN sz s t K n j Φ U b₀ ω with hy
  have hym : Measurable[filt sz (j + 1)] y := hξm.sub hZm
  have hyae : y =ᵐ[pathP sz] stepYCN sz s t K n j Φ U b₀ := by
    filter_upwards [hξ] with ω h
    simp only [hy, stepYCN, h]
  have hym' : Measurable y := hym.mono ((filt sz).le (j + 1)) le_rfl
  -- `L²` membership of `stepYCN` from the pathwise domination
  set g : PathΩ sz → ℝ := fun ω => (∑ a, ‖U b₀ a‖) * ((C₂ / 2) * gridStep s t K n) * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 with hg
  have hXmeas : Measurable fun ω : PathΩ sz => ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 :=
    ((((continuous_Xmat d (sz.L n) (sz.W n)).measurable.comp (Sizes.measurable_slice sz n)).comp (measurable_pi_apply (j + 1))).norm).pow_const 2
  have hg2 : Integrable (fun ω => (g ω) ^ 2) (pathP sz) := by
    have : (fun ω => (g ω) ^ 2) = fun ω => (((∑ a, ‖U b₀ a‖) * ((C₂ / 2) * gridStep s t K n)) ^ 2) *
        ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 4 := by funext ω; rw [hg]; ring
    rw [this]
    exact (integrable_normPow4_incr sz n j).const_mul _
  have hgL2 : MemLp g 2 (pathP sz) := (memLp_two_iff_integrable_sq (hXmeas.const_mul _).aestronglyMeasurable).2 hg2
  have hcL2 : MemLp ((pathP sz)[g | filt sz j]) 2 (pathP sz) := hgL2.condExp (by norm_num)
  have hYL2 : MemLp (stepYCN sz s t K n j Φ U b₀) 2 (pathP sz) := by
    refine (hgL2.add hcL2).mono' (hym'.aestronglyMeasurable.congr hyae) ?_
    filter_upwards [hbound] with ω h
    exact h
  have hyL2 : MemLp y 2 (pathP sz) := hYL2.ae_eq hyae.symm
  have hyint : Integrable y (pathP sz) := hyL2.integrable (by norm_num)
  have hmean : (pathP sz)[y | filt sz j] =ᵐ[pathP sz] fun _ => (0 : ℂ) := (condExp_congr_ae hyae).trans hmeanY
  have hq := stepDecompCN_Y_sq sz s t K n j hΦ hC₂ hΔ U b₀
  have hB4 := integral_normPow4_incr_le sz n j
  have hqbound : ∫ ω, ‖stepYCN sz s t K n j Φ U b₀ ω‖ ^ 2 ∂(pathP sz) ≤
      4 * ((∑ a, ‖κ a‖) * (C₂ / 2)) ^ 2 * gridStep s t K n ^ 2 * (768 * ((sz.size n : ℕ) : ℝ) ^ 8) := by
    refine hq.trans ?_
    have h0 : 0 ≤ 4 * ((∑ a, ‖κ a‖) * (C₂ / 2)) ^ 2 * gridStep s t K n ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left hB4 h0
  have hyn : ∫ ω, ‖y ω‖ ^ 2 ∂(pathP sz) = ∫ ω, ‖stepYCN sz s t K n j Φ U b₀ ω‖ ^ 2 ∂(pathP sz) :=
    integral_congr_ae (by filter_upwards [hyae] with ω h; rw [h])
  have hysq : Integrable (fun ω => ‖y ω‖ ^ 2) (pathP sz) := (memLp_two_iff_integrable_sq_norm hym'.aestronglyMeasurable).1 hyL2
  refine ⟨hym, ?_, ?_, hyL2.re, hyL2.im, ?_, ?_⟩
  · have hc := (ContinuousLinearMap.comp_condExp_comm (m := filt sz j) hyint Complex.reCLM).symm
    have hc' : (pathP sz)[fun ω => (y ω).re | filt sz j] =ᵐ[pathP sz] fun ω => ((pathP sz)[y | filt sz j] ω).re := by
      simpa [Function.comp_def] using hc
    filter_upwards [hc', hmean] with ω h1 h2
    rw [h1, h2]; simp
  · have hc := (ContinuousLinearMap.comp_condExp_comm (m := filt sz j) hyint Complex.imCLM).symm
    have hc' : (pathP sz)[fun ω => (y ω).im | filt sz j] =ᵐ[pathP sz] fun ω => ((pathP sz)[y | filt sz j] ω).im := by
      simpa [Function.comp_def] using hc
    filter_upwards [hc', hmean] with ω h1 h2
    rw [h1, h2]; simp
  · refine le_trans (integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _) hysq
      (Eventually.of_forall fun ω => TwistGridWTail_sq_re_le (y ω))) ?_
    rw [hyn]; exact hqbound
  · refine le_trans (integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _) hysq
      (Eventually.of_forall fun ω => TwistGridWTail_sq_im_le (y ω))) ?_
    rw [hyn]; exact hqbound

end YGeneric

/-! ## 8. The twisted martingale increment as a `stepXiCN`: measurability and the a.e. identification -/

section Mart

open scoped Matrix.Norms.L2Operator

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

theorem TwistGridWTail_Hm_measurable : Measurable (TwistGridWTail_Hm sz lam0 n) := by
  unfold TwistGridWTail_Hm; exact measurable_const.add measurable_id

/-- `Φ_b` is Borel measurable in the matrix (entries of the resolvent, `walk_measurable_Gres_apply`). -/
theorem TwistGridWTail_Phi_measurable (u : ℝ) (σ : Fin 2 → Bool) (c₁ c₂ b : Zd d (sz.L n)) :
    Measurable (TwistGridWTail_Phi sz lam0 E n u σ c₁ c₂ b) := by
  have hHm := TwistGridWTail_Hm_measurable sz lam0 n
  have hent : ∀ (σ' : Bool) (x y : Idx d (sz.L n) (sz.W n)), Measurable (fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      twChg (twGM sz lam0 E n u (TwistGridWTail_Hm sz lam0 n M)) σ' x y) := by
    intro σ' x y
    cases σ'
    · simp only [twChg, twGM, Bool.false_eq_true, ite_false]
      exact Complex.continuous_conj.measurable.comp ((walk_measurable_Gres_apply _ true y x).comp hHm)
    · simp only [twChg, twGM, ite_true]
      exact (walk_measurable_Gres_apply _ true x y).comp hHm
  unfold TwistGridWTail_Phi twL2M twLoopX
  exact measurable_const.mul (Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun w _ => (hent _ _ _).mul (hent _ _ _))

/-- The label family of step `j`: `Φ_b` at the spectral time `u_{j+1}`. -/
def TwistGridWTail_fam (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)) (j : ℕ) :
    Zd d (sz.L n) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ :=
  fun b => TwistGridWTail_Phi sz lam0 E n (gridTime s t K n (j + 1)) σ c₁ c₂ b

/-- The twisted martingale increment of step `j`, weighted by `κ`: `Σ_b κ_b ξ_{j+1}(b)` is a.e. `stepXiCN` of the family `TwistGridWTail_fam`
with the kernel `(·, a) ↦ κ_a` (linearity of the conditional expectation; `K̃` cancels), and `filt (j+1)`-measurable. -/
theorem TwistGridWTail_xi_ae (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)) (j : ℕ) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ etaOf (BAmF sz lam0 E n) (gridTime s t K n (j + 1))) (κ : Zd d (sz.L n) → ℂ) :
    (fun ω : PathΩ (sz.withLam 0) => ∑ b, κ b * twMartInc sz lam0 E s t K n σ c₁ c₂ j ω b) =ᵐ[pathP (sz.withLam 0)]
      stepXiCN (sz.withLam 0) s t K n j (TwistGridWTail_fam sz lam0 E s t K n σ c₁ c₂ j) (fun _ a => κ a) 0 ∧
    Measurable[filt (sz.withLam 0) (j + 1)] (fun ω : PathΩ (sz.withLam 0) => ∑ b, κ b * twMartInc sz lam0 E s t K n σ c₁ c₂ j ω b) := by
  set szz : Sizes d := sz.withLam 0 with hszz
  set Ξ : Zd d (sz.L n) → PathΩ szz → ℂ := fun b ω =>
    TwistGridWTail_Phi sz lam0 E n (gridTime s t K n (j + 1)) σ c₁ c₂ b (pathH szz s t K n (j + 1) ω) with hΞ
  set Kc : Zd d (sz.L n) → ℂ := fun b => twK (baFM sz lam0 E) n (gridTime s t K n (j + 1)) σ b c₁ c₂ with hKc
  have hΞm : ∀ b, Measurable[filt szz (j + 1)] (Ξ b) := fun b =>
    (TwistGridWTail_Phi_measurable sz lam0 E n _ σ c₁ c₂ b).comp (pathH_measurable_filt szz s t K n (j + 1))
  have hΞint : ∀ b, Integrable (Ξ b) (pathP szz) := by
    intro b
    have hm : Measurable (Ξ b) := (hΞm b).mono ((filt szz).le (j + 1)) le_rfl
    exact (memLp_top_of_bound hm.aestronglyMeasurable (η⁻¹ ^ 2) (Eventually.of_forall fun ω =>
      TwistGridWTail_Phi_norm_le sz lam0 E n _ σ c₁ c₂ b (pathH_isHermitian szz s t K n (j + 1) ω) hη0 hη)).integrable le_top
  -- pointwise: `twMartInc = (Ξ - K) - E[Ξ - K | F]`
  have hmart : ∀ ω b, twMartInc sz lam0 E s t K n σ c₁ c₂ j ω b =
      (Ξ b ω - Kc b) - (pathP szz)[fun ω' => Ξ b ω' - Kc b | filt szz j] ω := fun ω b => rfl
  have hce : ∀ b, (pathP szz)[fun ω' => Ξ b ω' - Kc b | filt szz j] =ᵐ[pathP szz] fun ω => (pathP szz)[Ξ b | filt szz j] ω - Kc b := by
    intro b
    have h := condExp_sub (hΞint b) (integrable_const (Kc b)) (filt szz j)
    have hc : (pathP szz)[fun _ : PathΩ szz => Kc b | filt szz j] = fun _ => Kc b := condExp_const ((filt szz).le j) _
    filter_upwards [h] with ω hω
    simp only [Pi.sub_apply] at hω ⊢
    rw [show (fun ω' => Ξ b ω' - Kc b) = Ξ b - fun _ => Kc b from rfl, hω, hc]
  have hlin : (pathP szz)[fun ω' => ∑ a, κ a * Ξ a ω' | filt szz j] =ᵐ[pathP szz] fun ω => ∑ a, κ a * (pathP szz)[Ξ a | filt szz j] ω := by
    have h1 := condExp_finsetSum (μ := pathP szz) (s := Finset.univ) (f := fun a ω' => κ a * Ξ a ω') (fun a _ => (hΞint a).const_mul (κ a)) (filt szz j)
    have h2 : ∀ a, (pathP szz)[fun ω' => κ a * Ξ a ω' | filt szz j] =ᵐ[pathP szz] fun ω => κ a * (pathP szz)[Ξ a | filt szz j] ω :=
      fun a => condExp_smul (κ a) (Ξ a) (filt szz j)
    have h3 : ∀ᵐ ω ∂(pathP szz), ∀ a, (pathP szz)[fun ω' => κ a * Ξ a ω' | filt szz j] ω = κ a * (pathP szz)[Ξ a | filt szz j] ω :=
      ae_all_iff.2 h2
    filter_upwards [h1, h3] with ω hω1 hω2
    have : (fun ω' => ∑ a, κ a * Ξ a ω') = ∑ a, fun ω' => κ a * Ξ a ω' := by funext ω'; simp [Finset.sum_apply]
    rw [this, hω1]
    simp only [Finset.sum_apply, hω2]
  have hce' : ∀ᵐ ω ∂(pathP szz), ∀ b, (pathP szz)[fun ω' => Ξ b ω' - Kc b | filt szz j] ω = (pathP szz)[Ξ b | filt szz j] ω - Kc b :=
    ae_all_iff.2 hce
  refine ⟨?_, ?_⟩
  · filter_upwards [hlin, hce'] with ω h1 h2
    have hL : ∑ b, κ b * twMartInc sz lam0 E s t K n σ c₁ c₂ j ω b =
        ∑ b, κ b * (Ξ b ω - (pathP szz)[Ξ b | filt szz j] ω) :=
      Finset.sum_congr rfl fun b _ => by rw [show twMartInc sz lam0 E s t K n σ c₁ c₂ j ω b = _ from hmart ω b, h2 b]; ring
    rw [hL]
    change _ = (∑ a, κ a * Ξ a ω) - (pathP szz)[fun ω' => ∑ a, κ a * Ξ a ω' | filt szz j] ω
    rw [h1, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  · change Measurable[filt szz (j + 1)] (fun ω : PathΩ szz => ∑ b, κ b * ((Ξ b ω - Kc b) - (pathP szz)[fun ω' => Ξ b ω' - Kc b | filt szz j] ω))
    refine Finset.measurable_sum _ fun b _ => measurable_const.mul ?_
    exact ((hΞm b).sub measurable_const).sub ((stronglyMeasurable_condExp.measurable).mono ((filt szz).mono (Nat.le_succ j)) le_rfl)

end Mart


/-! ## 9. Doob's `L²` maximal tail for the second-order part (copy of the private `difRep3_doob_tail`, `Path/DifREP3.lean:857`) -/

section Doob

/-- **Doob's `L²` tail for martingale differences**: `F_j` is `ℱ_{j+1}`-measurable, square-integrable,
conditionally centred, with `𝔼 F_j² ≤ q`; then `μ(∃ k ≤ K, x ≤ |Σ_{j<k} F_j|) ≤ K q / x²`. -/
private theorem TwistGridWTail_doob_tail {Ω' : Type} {mΩ' : MeasurableSpace Ω'} (μ : Measure Ω')
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ') (F : ℕ → Ω' → ℝ) (K : ℕ) (q x : ℝ)
    (hF : ∀ j < K, StronglyMeasurable[ℱ (j + 1)] (F j))
    (hL2 : ∀ j < K, MemLp (F j) 2 μ)
    (hmean : ∀ j < K, μ[F j | ℱ j] =ᵐ[μ] 0)
    (hq : ∀ j < K, ∫ ω, (F j ω) ^ 2 ∂μ ≤ q) (hx : 0 < x) :
    μ.real {ω | ∃ k, k ≤ K ∧ x ≤ |∑ j ∈ Finset.range k, F j ω|} ≤ K * q / x ^ 2 := by
  classical
  set F' : ℕ → Ω' → ℝ := fun j ω => if j < K then F j ω else 0 with hF'
  set M : ℕ → Ω' → ℝ := fun k ω => ∑ j ∈ Finset.range k, F' j ω with hM
  have hF'm : ∀ j, StronglyMeasurable[ℱ (j + 1)] (F' j) := fun j => by
    by_cases h : j < K
    · simpa only [hF', h, ↓reduceIte] using hF j h
    · simp only [hF', h, ↓reduceIte]
      exact stronglyMeasurable_const
  have hF'L2 : ∀ j, MemLp (F' j) 2 μ := fun j => by
    by_cases h : j < K
    · simpa only [hF', h, ↓reduceIte] using hL2 j h
    · simp only [hF', h, ↓reduceIte]
      exact MemLp.zero'
  have hMad : StronglyAdapted ℱ M := fun k =>
    Finset.stronglyMeasurable_fun_sum _ fun j hj =>
      (hF'm j).mono (ℱ.mono (Nat.succ_le_of_lt (Finset.mem_range.1 hj)))
  have hML2 : ∀ k, MemLp (M k) 2 μ := fun k =>
    memLp_finsetSum _ fun j _ => hF'L2 j
  have hMint : ∀ k, Integrable (M k) μ := fun k => (memLp_one_iff_integrable.1
    ((hML2 k).mono_exponent (by norm_num)))
  have hMsub : ∀ k, M (k + 1) - M k = F' k := fun k => by
    funext ω
    simp only [hM, Pi.sub_apply, Finset.sum_range_succ]
    ring
  have hmart : Martingale M ℱ μ := by
    refine martingale_of_condExp_sub_eq_zero_nat hMad hMint fun k => ?_
    rw [hMsub]
    by_cases h : k < K
    · have : F' k = F k := funext fun ω => by simp only [hF', h, ↓reduceIte]
      rw [this]
      exact hmean k h
    · have : F' k = 0 := funext fun ω => by simp only [hF', h, ↓reduceIte, Pi.zero_apply]
      rw [this]
      exact (condExp_zero).eventuallyEq
  have hM0 : M 0 = 0 := by funext ω; simp [hM]
  have hdoob := doob_L2_max hmart hM0 hML2 K hx
  have hset : {ω | ∃ k, k ≤ K ∧ x ≤ |∑ j ∈ Finset.range k, F j ω|} =
      {ω | x ≤ (Finset.range (K + 1)).sup' Finset.nonempty_range_add_one fun k => |M k ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Finset.le_sup'_iff, Finset.mem_range, Nat.lt_succ_iff]
    constructor
    · rintro ⟨k, hk, hxk⟩
      refine ⟨k, hk, ?_⟩
      have : M k ω = ∑ j ∈ Finset.range k, F j ω :=
        Finset.sum_congr rfl fun j hj => by
          simp only [hF', lt_of_lt_of_le (Finset.mem_range.1 hj) hk, ↓reduceIte]
      rw [this]; exact hxk
    · rintro ⟨k, hk, hxk⟩
      refine ⟨k, hk, ?_⟩
      have : M k ω = ∑ j ∈ Finset.range k, F j ω :=
        Finset.sum_congr rfl fun j hj => by
          simp only [hF', lt_of_lt_of_le (Finset.mem_range.1 hj) hk, ↓reduceIte]
      rw [← this]; exact hxk
  rw [hset]
  refine hdoob.trans ?_
  gcongr
  rw [martingale_sq_eq_sum hmart hM0 hML2 K]
  calc ∑ k ∈ Finset.range K, ∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ
      ≤ ∑ k ∈ Finset.range K, q := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' : k < K := Finset.mem_range.1 hk
        have : (fun ω => (M (k + 1) ω - M k ω) ^ 2) = fun ω => (F k ω) ^ 2 := by
          funext ω
          have := congrFun (hMsub k) ω
          simp only [Pi.sub_apply, hF', hk', ↓reduceIte] at this
          rw [this]
        rw [this]
        exact hq k hk'
    _ = K * q := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Doob

/-! ## 10. Grid arithmetic (copies of `Path/DifREP3.lean:726-757`, public with the stem for `TwistGridWTail2`) and the difference of two kernels -/

section Grid

theorem TwistGridWTail_gridTime_nonneg {s t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (j : ℕ) :
    0 ≤ gridTime s t K n j := by
  have hΔ := ST_gridStep_nonneg s t K n hst
  unfold gridTime
  have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg this hΔ]

theorem TwistGridWTail_gridTime_le {s t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hst : s n ≤ t n) (hK0 : K n ≠ 0) {j : ℕ} (hj : j ≤ K n) :
    gridTime s t K n j ≤ t n := by
  have hΔ := ST_gridStep_nonneg s t K n hst
  have hj' : (j : ℝ) ≤ (K n : ℝ) := by exact_mod_cast hj
  have h := mul_le_mul_of_nonneg_right hj' hΔ
  have hlast := gridTime_last s t K n hK0
  unfold gridTime at hlast ⊢
  nlinarith

theorem TwistGridWTail_gridTime_succ (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) :
    gridTime s t K n (j + 1) = gridTime s t K n j + gridStep s t K n := by
  unfold gridTime; push_cast; ring

theorem TwistGridWTail_gridTime_mono {s t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hst : s n ≤ t n) {i j : ℕ} (hij : i ≤ j) :
    gridTime s t K n i ≤ gridTime s t K n j := by
  have hΔ := ST_gridStep_nonneg s t K n hst
  unfold gridTime
  have : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.2 hij
  nlinarith

theorem TwistGridWTail_K_mul_step (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hK : K n ≠ 0) :
    (K n : ℝ) * gridStep s t K n = t n - s n := by
  have hK' : (K n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK
  unfold gridStep
  field_simp

end Grid

section KernelDiff

open scoped Matrix.Norms.Operator in
/-- `‖Ũ_{u,w₂} − Ũ_{u,w₁}‖ ≤ (w₂ − w₁)(1 − w₂)⁻¹ (1 − u)/(1 − w₁)` for `0 ≤ u ≤ w₁ ≤ w₂ < 1`: `Ũ_{u,w₂} − Ũ_{u,w₁} = (Ũ_{w₁,w₂} − 1) Ũ_{u,w₁}`
(`BAuKer_comp`, `norm_twU_sub_one_le`, `EKPins_norm_uKer_le`). -/
theorem TwistGridWTail_norm_twU_sub_le {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) {κ : ℝ}
    (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (σ : Fin 2 → Bool) {u w₁ w₂ : ℝ} (hu : 0 ≤ u) (huw : u ≤ w₁)
    (hw : w₁ ≤ w₂) (hw2 : w₂ < 1) :
    ‖twU sz lam0 E n σ u w₂ - twU sz lam0 E n σ u w₁‖ ≤ (w₂ - w₁) * (1 - w₂)⁻¹ * ((1 - u) / (1 - w₁)) := by
  have hw10 : 0 ≤ w₁ := hu.trans huw
  have hw1 : w₁ < 1 := hw.trans_lt hw2
  have hcomp : twU sz lam0 E n σ w₁ w₂ * twU sz lam0 E n σ u w₁ = twU sz lam0 E n σ u w₂ :=
    BAuKer_comp hr hw10 hw1 (hw10.trans hw) hw2 (σ 0) (σ 1)
  have e : twU sz lam0 E n σ u w₂ - twU sz lam0 E n σ u w₁ = (twU sz lam0 E n σ w₁ w₂ - 1) * twU sz lam0 E n σ u w₁ := by
    rw [sub_mul, hcomp, one_mul]
  rw [e]
  refine (norm_mul_le _ _).trans (mul_le_mul ?_ (EKPins_norm_uKer_le hr hu huw hw1 (σ 0) (σ 1)) (norm_nonneg _) (by positivity))
  have h := TwistGridWTail_norm_twU_sub_one_le sz lam0 E n hr σ w₁ (hw10.trans hw) hw2
  rwa [abs_of_nonneg (by linarith)] at h

end KernelDiff

/-! ## 11. The weighted `Y` tail (twin of `difRep3_Y_tail`, `Path/DifREP3.lean:959`) -/

section YTail

open scoped Matrix.Norms.L2Operator

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

/-- The second-order increment `y_j = Σ_b κ_{j,b} ξ_{j+1}(b) − ζ_j`, with `ζ_j = stepZCN` of the family at the kernel `(·, a) ↦ κ_{j,a}`. -/
def TwistGridWTail_yinc (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)) (κ : ℕ → Zd d (sz.L n) → ℂ) (j : ℕ)
    (ω : PathΩ (sz.withLam 0)) : ℂ :=
  (∑ b, κ j b * twMartInc sz lam0 E s t K n σ c₁ c₂ j ω b) -
    stepZCN (sz.withLam 0) s t K n j (TwistGridWTail_fam sz lam0 E s t K n σ c₁ c₂ j) (fun _ a => κ j a) 0 ω

/-- **The `Y` part of the tail, weighted**: for deterministic `j`-dependent weights `κ_j` with `Σ_b |κ_j(b)| ≤ S`, `η ≤ η_u` for `u ≤ t`, and
`P ≥ 768 (S · 6 η⁻⁴)² N⁸`, `μ (∃ k ≤ K, x ≤ |Σ_{j<k} y_j|) ≤ 4 K Δ² P / x²` (`TwistGridWTail_Y_fields` at every step, Doob for `Re` and `Im`). -/
theorem TwistGridWTail_Y_tail (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) {η : ℝ} (hη0 : 0 < η)
    (hη : ∀ u : ℝ, u ≤ t n → η ≤ etaOf (BAmF sz lam0 E n) u) (κ : ℕ → Zd d (sz.L n) → ℂ) {S : ℝ} (hS0 : 0 ≤ S)
    (hrow : ∀ j, ∑ b, ‖κ j b‖ ≤ S) {P : ℝ} (hP : 768 * (S * (6 * η⁻¹ ^ 4)) ^ 2 * ((sz.size n : ℕ) : ℝ) ^ 8 ≤ P) {x : ℝ} (hx : 0 < x) :
    (pathP (sz.withLam 0)).real {ω | ∃ k, k ≤ K n ∧
        x ≤ ‖∑ j ∈ Finset.range k, TwistGridWTail_yinc sz lam0 E s t K n σ c₁ c₂ κ j ω‖} ≤
      4 * ((K n : ℝ) * (gridStep s t K n ^ 2 * P)) / x ^ 2 := by
  set szz : Sizes d := sz.withLam 0 with hszz
  have hΔ := ST_gridStep_nonneg s t K n hst
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hfields : ∀ j < K n,
      Measurable[filt szz (j + 1)] (fun ω => TwistGridWTail_yinc sz lam0 E s t K n σ c₁ c₂ κ j ω) ∧
      (pathP szz)[fun ω => (TwistGridWTail_yinc sz lam0 E s t K n σ c₁ c₂ κ j ω).re | filt szz j] =ᵐ[pathP szz] 0 ∧
      (pathP szz)[fun ω => (TwistGridWTail_yinc sz lam0 E s t K n σ c₁ c₂ κ j ω).im | filt szz j] =ᵐ[pathP szz] 0 ∧
      MemLp (fun ω => (TwistGridWTail_yinc sz lam0 E s t K n σ c₁ c₂ κ j ω).re) 2 (pathP szz) ∧
      MemLp (fun ω => (TwistGridWTail_yinc sz lam0 E s t K n σ c₁ c₂ κ j ω).im) 2 (pathP szz) ∧
      ∫ ω, (TwistGridWTail_yinc sz lam0 E s t K n σ c₁ c₂ κ j ω).re ^ 2 ∂(pathP szz) ≤ gridStep s t K n ^ 2 * P ∧
      ∫ ω, (TwistGridWTail_yinc sz lam0 E s t K n σ c₁ c₂ κ j ω).im ^ 2 ∂(pathP szz) ≤ gridStep s t K n ^ 2 * P := by
    intro j hj
    have hj' : j + 1 ≤ K n := hj
    have hK : K n ≠ 0 := by omega
    have hu : gridTime s t K n (j + 1) ≤ t n := TwistGridWTail_gridTime_le hst hK hj'
    have hηj := hη _ hu
    have hΦ : ∀ b, HermTestFun szz n (TwistGridWTail_fam sz lam0 E s t K n σ c₁ c₂ j b) := fun b =>
      TwistGridWTail_hermTestFun sz lam0 E n _ σ c₁ c₂ b hη0 hηj
    have hC₂ : ∀ b (M y : Matrix (Idx d (szz.L n) (szz.W n)) (Idx d (szz.L n) (szz.W n)) ℂ), M.IsHermitian → y.IsHermitian →
        ‖fderiv ℝ (fderiv ℝ (TwistGridWTail_fam sz lam0 E s t K n σ c₁ c₂ j b)) M y y‖ ≤ (6 * η⁻¹ ^ 4) * ‖y‖ ^ 2 :=
      fun b M y hM hy => TwistGridWTail_Phi_second sz lam0 E n _ σ c₁ c₂ b hη0 hηj hM hy
    obtain ⟨hξae, hξm⟩ := TwistGridWTail_xi_ae sz lam0 E s t K n σ c₁ c₂ j hη0 hηj (κ j)
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := TwistGridWTail_Y_fields (sz := szz) s t K n j hΦ hC₂ hΔ (κ j) 0
      (fun ω => ∑ b, κ j b * twMartInc sz lam0 E s t K n σ c₁ c₂ j ω b) hξae hξm
    have hq : 4 * ((∑ a, ‖κ j a‖) * (6 * η⁻¹ ^ 4 / 2)) ^ 2 * gridStep s t K n ^ 2 * (768 * N ^ 8) ≤ gridStep s t K n ^ 2 * P := by
      have hA : ∑ a, ‖κ j a‖ ≤ S := hrow j
      have hA0 : 0 ≤ ∑ a, ‖κ j a‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
      have hC0 : 0 ≤ 6 * η⁻¹ ^ 4 := by positivity
      have h0 : (∑ a, ‖κ j a‖) * (6 * η⁻¹ ^ 4) ≤ S * (6 * η⁻¹ ^ 4) := mul_le_mul_of_nonneg_right hA hC0
      have h00 : 0 ≤ (∑ a, ‖κ j a‖) * (6 * η⁻¹ ^ 4) := mul_nonneg hA0 hC0
      have h1' : ((∑ a, ‖κ j a‖) * (6 * η⁻¹ ^ 4)) ^ 2 ≤ (S * (6 * η⁻¹ ^ 4)) ^ 2 := pow_le_pow_left₀ h00 h0 2
      calc 4 * ((∑ a, ‖κ j a‖) * (6 * η⁻¹ ^ 4 / 2)) ^ 2 * gridStep s t K n ^ 2 * (768 * N ^ 8)
          = gridStep s t K n ^ 2 * (768 * ((∑ a, ‖κ j a‖) * (6 * η⁻¹ ^ 4)) ^ 2 * N ^ 8) := by ring
        _ ≤ gridStep s t K n ^ 2 * (768 * (S * (6 * η⁻¹ ^ 4)) ^ 2 * N ^ 8) := by gcongr
        _ ≤ gridStep s t K n ^ 2 * P := by gcongr
    exact ⟨h1, h2, h3, h4, h5, h6.trans hq, h7.trans hq⟩
  have hxs : 0 < x / Real.sqrt 2 := div_pos hx (Real.sqrt_pos.2 (by norm_num))
  have hRe := TwistGridWTail_doob_tail (pathP szz) (filt szz) (fun j ω => (TwistGridWTail_yinc sz lam0 E s t K n σ c₁ c₂ κ j ω).re)
    (K n) (gridStep s t K n ^ 2 * P) (x / Real.sqrt 2)
    (fun j hj => (Complex.measurable_re.comp (hfields j hj).1).stronglyMeasurable)
    (fun j hj => (hfields j hj).2.2.2.1) (fun j hj => (hfields j hj).2.1) (fun j hj => (hfields j hj).2.2.2.2.2.1) hxs
  have hIm := TwistGridWTail_doob_tail (pathP szz) (filt szz) (fun j ω => (TwistGridWTail_yinc sz lam0 E s t K n σ c₁ c₂ κ j ω).im)
    (K n) (gridStep s t K n ^ 2 * P) (x / Real.sqrt 2)
    (fun j hj => (Complex.measurable_im.comp (hfields j hj).1).stronglyMeasurable)
    (fun j hj => (hfields j hj).2.2.2.2.1) (fun j hj => (hfields j hj).2.2.1) (fun j hj => (hfields j hj).2.2.2.2.2.2) hxs
  have hsub : {ω | ∃ k, k ≤ K n ∧ x ≤ ‖∑ j ∈ Finset.range k, TwistGridWTail_yinc sz lam0 E s t K n σ c₁ c₂ κ j ω‖} ⊆
      {ω | ∃ k, k ≤ K n ∧ x / Real.sqrt 2 ≤ |∑ j ∈ Finset.range k, (TwistGridWTail_yinc sz lam0 E s t K n σ c₁ c₂ κ j ω).re|} ∪
      {ω | ∃ k, k ≤ K n ∧ x / Real.sqrt 2 ≤ |∑ j ∈ Finset.range k, (TwistGridWTail_yinc sz lam0 E s t K n σ c₁ c₂ κ j ω).im|} := by
    intro ω hω
    obtain ⟨k, hk, hxk⟩ := hω
    have h1 := Complex.norm_le_sqrt_two_mul_max (∑ j ∈ Finset.range k, TwistGridWTail_yinc sz lam0 E s t K n σ c₁ c₂ κ j ω)
    have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have h2 : x / Real.sqrt 2 ≤ max |(∑ j ∈ Finset.range k, TwistGridWTail_yinc sz lam0 E s t K n σ c₁ c₂ κ j ω).re|
        |(∑ j ∈ Finset.range k, TwistGridWTail_yinc sz lam0 E s t K n σ c₁ c₂ κ j ω).im| := by
      rw [div_le_iff₀ hs2]
      linarith
    rw [Complex.re_sum, Complex.im_sum] at h2
    rcases le_max_iff.1 h2 with h | h
    · exact Or.inl ⟨k, hk, h⟩
    · exact Or.inr ⟨k, hk, h⟩
  calc (pathP szz).real {ω | ∃ k, k ≤ K n ∧ x ≤ ‖∑ j ∈ Finset.range k, TwistGridWTail_yinc sz lam0 E s t K n σ c₁ c₂ κ j ω‖}
      ≤ (pathP szz).real ({ω | ∃ k, k ≤ K n ∧ x / Real.sqrt 2 ≤ |∑ j ∈ Finset.range k, (TwistGridWTail_yinc sz lam0 E s t K n σ c₁ c₂ κ j ω).re|} ∪
        {ω | ∃ k, k ≤ K n ∧ x / Real.sqrt 2 ≤ |∑ j ∈ Finset.range k, (TwistGridWTail_yinc sz lam0 E s t K n σ c₁ c₂ κ j ω).im|}) :=
        measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ (K n : ℝ) * (gridStep s t K n ^ 2 * P) / (x / Real.sqrt 2) ^ 2 + (K n : ℝ) * (gridStep s t K n ^ 2 * P) / (x / Real.sqrt 2) ^ 2 :=
        add_le_add hRe hIm
    _ = 4 * ((K n : ℝ) * (gridStep s t K n ^ 2 * P)) / x ^ 2 := by
        rw [div_pow, Real.sq_sqrt (by norm_num)]
        field_simp
        ring

end YTail

end RBM.BA
