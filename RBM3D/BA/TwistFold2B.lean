/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.TwistFold2
import RBM3D.Graph.BAExp14aB

/-!
# BA-L L4d2a (T2445), part B: the `≺` row of the two-insertion fold

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:118`; design
`docs/claude-team/fable/2026-10-12-s3-fold-A.md` §2.2, §4, §5 (route (A')), supervisor
`2026-10-12-0851.md` Q2, S3A-C1 to S3A-C3.  Part A is `BA/TwistFold2.lean`.

Contents:
* the fine-trace form of the `3`-loop at the carrier (`TwistFold2_loop3`, `TwistFold2_L3_carrier`);
* the deterministic bounds of the two marginals of the fold, `S_A` and `S_C`
  (`TwistFold2_SA`, `TwistFold2_SC`; S3A-C1 in the BA form, no band formula);
* `twFold2Prec`, `twFold2PrecDet` and their `_holds` theorems: for a deterministic weight `ρ` with
  `r₁, r₂ ≤ Cρ` and a random factor `X` with `‖X‖ ≺ W^d Bctl`,
  `‖twLoop2X Ǧ Ǧ (Ǧ E_b Ǧ(σ)) (ρ X) a‖ ≺ (1 - t)⁻¹ Bctl^{5/2}` from `STLocalEntrygL` and `STLmaxgL`.

Proof map (S3A-C1 in the BA form, supervisor 0851 `:51-60`; no band formula
`E_c M E_{c'} = δ W^{-d} m E_c`).  With `φ_x = E_b Ǧ(σ) e_x`, the column `C e_x = Ǧ φ_x` of
`C = Ǧ E_b Ǧ(σ)` is bounded by `twVec_holds` (`‖Ǧφ‖² ≤ 2 η⁻¹ Im⟨φ, Gφ⟩ + 2 ‖Mφ‖²`, with
`‖Mφ‖² ≤ ‖φ‖²` by `twMblk_le_holds`).  The vector is split as `φ = φ^G - φ^M` (the `G(σ)` and
`M(σ)` parts of the leg `Ǧ(σ)`) and `Im⟨φ, Gφ⟩ = η ‖Gφ‖²` gives
`Im Q(φ) ≤ 2 Im Q(φ^G) + 2 Im Q(φ^M)` (`TwistFold2_imQ_sub`).  Then
`Σ_x Q(φ^G_x) = W^d 𝓛^{(3)}_{(σ̄,+,σ),(b,b,a)}` (`TwistFold2_L3_carrier`, the pin `STLmaxgL`,
`k = 3`), and `φ^M_x` is supported at the single point `(b, o(x))` because
`M_{uv} = 1[o(u) = o(v)] M^{(B)}_{[u][v]}` (`BAMfine_eq`), so `Σ_x Im Q(φ^M_x) ≤ W^{-d} ℓ₁`
(`k = 1`).  The rows `S_A = Σ_{x∈[a]} ‖Ǧ^* e_x‖²` use the Ward identity and `twMrow_le_holds`.
The inputs `b = max|Ǧ_{xy}|` (`STLocalEntrygL`), `ℓ₁`, `ℓ₃` (`STLmaxgL`), `Y = max|X|`, and the
deterministic `W^d Bctl ≥ c₀`, `η_t ≥ κ(1 - t)` combine in `TwistFold2_arith`; the `≺` calculus of
one-index variables closes the row.  Premises used: `STLocalEntrygL`, `STLmaxgL` at `k = 1, 3`
(no `k = 2`, `STLKgL`, `BATwist*`).

All private helpers carry the stem `TwistFold2_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.style.setOption false
set_option linter.flexible false

open MeasureTheory Filter
open scoped Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-! ## 1. The fine-trace form of the `3`-loop -/

private theorem TwistFold2_ind_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (I : Finset ι) (c : ℂ) (f : ι → ℂ) :
    ∑ x, (if x ∈ I then c else 0) * f x = c * ∑ x ∈ I, f x := by
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]

/-- The indicator-weighted triple sum of a 3-loop is the sum over the three blocks. -/
private theorem TwistFold2_tri {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℂ) (I0 I1 I2 : Finset ι) (G0 G1 G2 : ι → ι → ℂ) :
    ∑ x, ∑ x1, (G0 x x1 * if x1 ∈ I0 then c else 0) *
      ∑ x2, (G1 x1 x2 * if x2 ∈ I1 then c else 0) * (G2 x2 x * if x ∈ I2 then c else 0) =
    c ^ 3 * ∑ x ∈ I2, ∑ y ∈ I0, ∑ w ∈ I1, G0 x y * G1 y w * G2 w x := by
  have h1 : ∀ x x1, (G0 x x1 * if x1 ∈ I0 then c else 0) *
      ∑ x2, (G1 x1 x2 * if x2 ∈ I1 then c else 0) * (G2 x2 x * if x ∈ I2 then c else 0) =
      (if x ∈ I2 then c else 0) * ((if x1 ∈ I0 then c else 0) * (c * (G0 x x1 * ∑ x2 ∈ I1, G1 x1 x2 * G2 x2 x))) := by
    intro x x1
    have : ∑ x2, (G1 x1 x2 * if x2 ∈ I1 then c else 0) * (G2 x2 x * if x ∈ I2 then c else 0) =
        (if x ∈ I2 then c else 0) * ∑ x2, (if x2 ∈ I1 then c else 0) * (G1 x1 x2 * G2 x2 x) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x2 _ => by ring
    rw [this, TwistFold2_ind_sum I1 c (fun x2 => G1 x1 x2 * G2 x2 x)]; ring
  have h2 : ∀ x, ∑ x1, (if x ∈ I2 then c else 0) * ((if x1 ∈ I0 then c else 0) * (c * (G0 x x1 * ∑ x2 ∈ I1, G1 x1 x2 * G2 x2 x))) =
      (if x ∈ I2 then c else 0) * (c * (c * ∑ x1 ∈ I0, G0 x x1 * ∑ x2 ∈ I1, G1 x1 x2 * G2 x2 x)) := by
    intro x
    have h := TwistFold2_ind_sum I0 c (fun x1 => G0 x x1 * ∑ x2 ∈ I1, G1 x1 x2 * G2 x2 x)
    calc ∑ x1, (if x ∈ I2 then c else 0) * ((if x1 ∈ I0 then c else 0) * (c * (G0 x x1 * ∑ x2 ∈ I1, G1 x1 x2 * G2 x2 x)))
        = (if x ∈ I2 then c else 0) * (c * ∑ x1, (if x1 ∈ I0 then c else 0) * (G0 x x1 * ∑ x2 ∈ I1, G1 x1 x2 * G2 x2 x)) := by
          rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun x1 _ => by ring
      _ = _ := by rw [h]
  simp only [h1, h2]
  have h3 := TwistFold2_ind_sum I2 c (fun x => c * (c * ∑ x1 ∈ I0, G0 x x1 * ∑ x2 ∈ I1, G1 x1 x2 * G2 x2 x))
  rw [h3]
  have e1 : ∀ x, c * (c * ∑ x1 ∈ I0, G0 x x1 * ∑ x2 ∈ I1, G1 x1 x2 * G2 x2 x) =
      c ^ 2 * ∑ x1 ∈ I0, ∑ x2 ∈ I1, G0 x x1 * G1 x1 x2 * G2 x2 x := by
    intro x
    have : ∑ x1 ∈ I0, G0 x x1 * ∑ x2 ∈ I1, G1 x1 x2 * G2 x2 x = ∑ x1 ∈ I0, ∑ x2 ∈ I1, G0 x x1 * G1 x1 x2 * G2 x2 x :=
      Finset.sum_congr rfl fun x1 _ => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x2 _ => by ring
    rw [this]; ring
  simp only [e1]
  rw [← Finset.mul_sum, ← mul_assoc, ← pow_succ']

theorem TwistFold2_loop3 {d L W : ℕ} [NeZero L] [NeZero W] (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ)
    (σ : Fin 3 → Bool) (a : Fin 3 → Zd d L) :
    loopFine d L W H z σ a = (((W : ℂ) ^ d)⁻¹) ^ 3 * ∑ x ∈ Iblk d L W (a 2), ∑ y ∈ Iblk d L W (a 0), ∑ w ∈ Iblk d L W (a 1),
      Gres H z (σ 0) x y * Gres H z (σ 1) y w * Gres H z (σ 2) w x := by
  have hP : ∀ (A : Matrix (Vtx d L W) (Vtx d L W) ℂ) (b : Zd d L),
      A * Eblk d L W b = Matrix.of fun i j => A i j * (if j.1 = b then ((W : ℂ) ^ d)⁻¹ else 0) := by
    intro A b; ext i j; simp [Eblk, Matrix.mul_diagonal]
  have hmem : ∀ (x : Idx d L W) (b : Zd d L), ((splitEquiv d L W) x).1 = b ↔ x ∈ Iblk d L W b := by
    intro x b; simp [Iblk, splitEquiv, Equiv.ofBijective_apply]
  unfold loopFine loopM
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, BAExp14a_Gres_blockMat, hP]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.submatrix_apply]
  simp only [← Equiv.sum_comp (splitEquiv d L W), Equiv.symm_apply_apply, hmem]
  classical
  exact TwistFold2_tri _ (Iblk d L W (a 0)) (Iblk d L W (a 1)) (Iblk d L W (a 2)) (fun x y => Gres H z (σ 0) x y)
    (fun x y => Gres H z (σ 1) x y) (fun x y => Gres H z (σ 2) x y)


section Carrier
variable {d : ℕ} {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}

theorem TwistFold2_Gres_false (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) :
    Gres (sz.seqHflowBA (BAflowLam0 sz z) n t ω) (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t) false x y =
      twChg ((baFMz sz z).G n t ω) false x y := by
  have hH := BAExpand_Hm_isHermitian sz n (BAflowLam0 sz z n) t ω
  have h1 : Gres (sz.seqHflowBA (BAflowLam0 sz z) n t ω) (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t) false =
      green (BAExpand_Hm sz n (BAflowLam0 sz z n) t ω) ((starRingEnd ℂ) (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t)) := by
    simp only [Gres, green, Matrix.nonsing_inv_eq_ringInverse]
    rfl
  have h2 := TwistFold2_green_conj hH (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t)
  rw [h1, ← h2]
  have h3 := BAExp14a_G_green (sz := sz) (z := z) n t ω
  simp only [twChg, Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply, h3]
  rfl

theorem TwistFold2_Gres_eq (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (s : Bool) (x y : Idx d (sz.L n) (sz.W n)) :
    Gres (sz.seqHflowBA (BAflowLam0 sz z) n t ω) (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t) s x y =
      twChg ((baFMz sz z).G n t ω) s x y := by
  cases s
  · exact TwistFold2_Gres_false n t ω x y
  · rfl

/-- **The fine-trace form of `𝓛^{(3)}` at the carrier**: `𝓛^{(3)}_{σ,a} = W^{-3d} Σ_{x∈[a₂]} Σ_{y∈[a₀]} Σ_{w∈[a₁]} G(σ₀)_{xy} G(σ₁)_{yw} G(σ₂)_{wx}`. -/
theorem TwistFold2_L3_carrier (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (σ : Fin 3 → Bool) (a : Fin 3 → Zd d (sz.L n)) :
    (baFMz sz z).L n t σ a ω = (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ ^ 3 *
      ∑ x ∈ twBlk n (a 2), ∑ y ∈ twBlk n (a 0), ∑ w ∈ twBlk n (a 1),
        twChg ((baFMz sz z).G n t ω) (σ 0) x y * twChg ((baFMz sz z).G n t ω) (σ 1) y w *
          twChg ((baFMz sz z).G n t ω) (σ 2) w x := by
  change loopFine d (sz.L n) (sz.W n) (sz.seqHflowBA (BAflowLam0 sz z) n t ω)
      (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t) σ a = _
  rw [TwistFold2_loop3]
  simp only [TwistFold2_Gres_eq]
  rfl

end Carrier

/-! ## 2. The marginals of the fold: `S_A` and `S_C` -/

theorem TwistFold2_twChg_sub {ι : Type*} (A B : ι → ι → ℂ) (σ : Bool) (x y : ι) :
    twChg (fun u v => A u v - B u v) σ x y = twChg A σ x y - twChg B σ x y := by
  unfold twChg; split_ifs <;> simp

theorem TwistFold2_star_twChg {ι : Type*} (A : ι → ι → ℂ) (σ : Bool) (x y : ι) :
    star (twChg A σ y x) = twChg A (!σ) x y := by
  cases σ <;> simp [twChg]

theorem TwistFold2_norm_twChg_le {ι : Type*} (A : ι → ι → ℂ) (σ : Bool) (x y : ι) (b : ℝ)
    (h : ∀ u v, ‖A u v‖ ≤ b) : ‖twChg A σ x y‖ ≤ b := by
  cases σ
  · simpa [twChg] using h y x
  · simpa [twChg] using h x y

/-- The quadratic form `Q(φ) = ⟨φ, Gφ⟩`. -/
def TwistFold2_Q {ι : Type*} [Fintype ι] (G : Matrix ι ι ℂ) (φ : ι → ℂ) : ℂ := ∑ u, star (φ u) * ∑ v, G u v * φ v

/-- `Im Q(φ₁ - φ₂) ≤ 2 Im Q(φ₁) + 2 Im Q(φ₂)` for the resolvent quadratic form. -/
theorem TwistFold2_imQ_sub {ι : Type} [Fintype ι] (G : Matrix ι ι ℂ) (η : ℝ) (hη : 0 ≤ η)
    (hG : G - G.conjTranspose = (2 * (η : ℂ) * Complex.I) • (G.conjTranspose * G)) (φ₁ φ₂ : ι → ℂ) :
    (TwistFold2_Q G (fun y => φ₁ y - φ₂ y)).im ≤ 2 * (TwistFold2_Q G φ₁).im + 2 * (TwistFold2_Q G φ₂).im := by
  unfold TwistFold2_Q
  rw [TwistFold2_imQ G η hG, TwistFold2_imQ G η hG φ₁, TwistFold2_imQ G η hG φ₂]
  have h2 : ∀ u, ‖∑ v, G u v * (φ₁ v - φ₂ v)‖ ^ 2 ≤ 2 * ‖∑ v, G u v * φ₁ v‖ ^ 2 + 2 * ‖∑ v, G u v * φ₂ v‖ ^ 2 := by
    intro u
    have e : ∑ v, G u v * (φ₁ v - φ₂ v) = ∑ v, G u v * φ₁ v - ∑ v, G u v * φ₂ v := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    rw [e]
    have h1 := norm_sub_le (∑ v, G u v * φ₁ v) (∑ v, G u v * φ₂ v)
    have h0 := norm_nonneg (∑ v, G u v * φ₁ v - ∑ v, G u v * φ₂ v)
    nlinarith [norm_nonneg (∑ v, G u v * φ₁ v), norm_nonneg (∑ v, G u v * φ₂ v),
      sq_nonneg (‖∑ v, G u v * φ₁ v‖ - ‖∑ v, G u v * φ₂ v‖)]
  have := Finset.sum_le_sum (fun u (_ : u ∈ Finset.univ) => h2 u)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at this
  nlinarith

/-- The quadratic form of an indicator-supported vector. -/
theorem TwistFold2_Q_ind {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ) (S : Finset ι) (w : ι → ℂ) :
    TwistFold2_Q G (fun y => if y ∈ S then w y else 0) = ∑ u ∈ S, star (w u) * ∑ v ∈ S, G u v * w v := by
  unfold TwistFold2_Q
  have h1 : ∀ u, (∑ v, G u v * (if v ∈ S then w v else 0)) = ∑ v ∈ S, G u v * w v := by
    intro u
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  simp only [h1]
  have h2 : ∀ u, star (if u ∈ S then w u else 0) * ∑ v ∈ S, G u v * w v =
      if u ∈ S then star (w u) * ∑ v ∈ S, G u v * w v else 0 := by
    intro u; split_ifs <;> simp
  simp only [h2]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

section Abstract
variable {d : ℕ} {sz : Sizes d}

theorem TwistFold2_u_pos (n : ℕ) : 0 < ((sz.W n : ℕ) : ℝ) ^ d := by
  have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  positivity

/-- **The row bound** `S_A = Σ_{x∈[a]} ‖Ǧ^* e_x‖² ≤ 2 η⁻¹ W^d (𝓛¹ + 1)` (Ward identity, `‖M^* e_x‖² ≤ 1`). -/
theorem TwistFold2_SA (n : ℕ) (G M : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (η l1 : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hward : ∀ x, η * ∑ y, ‖G x y‖ ^ 2 = (G x x).im)
    (hMrow : ∀ x, ∑ v, ‖M x v‖ ^ 2 ≤ 1) (a : Zd d (sz.L n))
    (hl1 : ∑ x ∈ twBlk n a, (G x x).im ≤ ((sz.W n : ℕ) : ℝ) ^ d * l1) :
    ∑ x ∈ twBlk n a, ∑ v, ‖G x v - M x v‖ ^ 2 ≤ 2 * η⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d) * (l1 + 1) := by
  set u : ℝ := ((sz.W n : ℕ) : ℝ) ^ d with hu
  have hu0 : 0 < u := TwistFold2_u_pos n
  have h1 : ∀ x v, ‖G x v - M x v‖ ^ 2 ≤ 2 * ‖G x v‖ ^ 2 + 2 * ‖M x v‖ ^ 2 := by
    intro x v
    have h := norm_sub_le (G x v) (M x v)
    nlinarith [norm_nonneg (G x v - M x v), norm_nonneg (G x v), norm_nonneg (M x v),
      sq_nonneg (‖G x v‖ - ‖M x v‖)]
  have h2 : ∀ x, ∑ v, ‖G x v - M x v‖ ^ 2 ≤ 2 * η⁻¹ * (G x x).im + 2 := by
    intro x
    calc ∑ v, ‖G x v - M x v‖ ^ 2 ≤ ∑ v, (2 * ‖G x v‖ ^ 2 + 2 * ‖M x v‖ ^ 2) :=
          Finset.sum_le_sum fun v _ => h1 x v
      _ = 2 * ∑ v, ‖G x v‖ ^ 2 + 2 * ∑ v, ‖M x v‖ ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 2 * η⁻¹ * (G x x).im + 2 := by
          have : ∑ v, ‖G x v‖ ^ 2 = η⁻¹ * (G x x).im := by
            rw [← hward x]; field_simp
          rw [this]; linarith [hMrow x]
  have hone : 1 ≤ η⁻¹ := (one_le_inv₀ hη).mpr hη1
  calc ∑ x ∈ twBlk n a, ∑ v, ‖G x v - M x v‖ ^ 2 ≤ ∑ x ∈ twBlk n a, (2 * η⁻¹ * (G x x).im + 2) :=
        Finset.sum_le_sum fun x _ => h2 x
    _ = 2 * η⁻¹ * ∑ x ∈ twBlk n a, (G x x).im + 2 * u := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, TwistFold2_card_blk]; ring
    _ ≤ 2 * η⁻¹ * (u * l1) + 2 * u := by
        have : 0 ≤ 2 * η⁻¹ := by positivity
        nlinarith
    _ ≤ 2 * η⁻¹ * u * (l1 + 1) := by nlinarith

/-- **The column bound** `S_C = Σ_{x∈[a]} ‖(Ǧ E_b Ǧ(σ)) e_x‖² ≤ 4 η⁻¹ W^d ℓ₃ + 4 η⁻¹ W^{-d} ℓ₁ + 2 b²` (S3A-C1: `φ_x = E_b Ǧ(σ) e_x`
is split as `φ^G_x - φ^M_x`; the `M`-part is supported at the one point `(b, o(x))` by `BAMfine_eq`, the `G`-part is the 3-loop
`Tr(E_a G(σ̄) E_b G E_b G(σ))`; no band formula `E_c M E_{c'} = δ W^{-d} m E_c`). -/
theorem TwistFold2_SC (n : ℕ) (G M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (η b l1 l3 : ℝ)
    (hη : 0 < η) (hG : G - G.conjTranspose = (2 * (η : ℂ) * Complex.I) • (G.conjTranspose * G))
    (hMtie : ∀ x y, (split d (sz.L n) (sz.W n) x).2 ≠ (split d (sz.L n) (sz.W n) y).2 → M x y = 0)
    (hMle : ∀ x y, ‖M x y‖ ≤ 1)
    (hMblk : ∀ (c : Zd d (sz.L n)) (φ : Idx d (sz.L n) (sz.W n) → ℂ), (∀ v, v ∉ twBlk n c → φ v = 0) →
      ∑ u, ‖∑ v, M u v * φ v‖ ^ 2 ≤ ∑ v, ‖φ v‖ ^ 2)
    (hImG : ∀ x, 0 ≤ (G x x).im) (hb : ∀ x y, ‖G x y - M x y‖ ≤ b)
    (σ : Bool) (a bb : Zd d (sz.L n))
    (hl1 : ∑ y ∈ twBlk n bb, (G y y).im ≤ ((sz.W n : ℕ) : ℝ) ^ d * l1)
    (hl3 : ‖∑ x ∈ twBlk n a, ∑ y ∈ twBlk n bb, ∑ w ∈ twBlk n bb,
        twChg G (!σ) x y * twChg G true y w * twChg G σ w x‖ ≤ (((sz.W n : ℕ) : ℝ) ^ d) ^ 3 * l3) :
    ∑ x ∈ twBlk n a, ∑ v, ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ y ∈ twBlk n bb, (G v y - M v y) *
        twChg (fun p q => G p q - M p q) σ y x‖ ^ 2 ≤
      4 * η⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d) * l3 + 4 * η⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * l1 + 2 * b ^ 2 := by
  classical
  set u : ℝ := ((sz.W n : ℕ) : ℝ) ^ d with hu
  have hu0 : 0 < u := TwistFold2_u_pos n
  set wC : ℂ := (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ with hwC
  have hwCn : ‖wC‖ = u⁻¹ := by rw [hwC, hu]; simp
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0 0)
  set S : Finset (Idx d (sz.L n) (sz.W n)) := twBlk n bb with hS
  -- the three vectors
  let φ : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ := fun x y =>
    if y ∈ S then wC * twChg (fun p q => G p q - M p q) σ y x else 0
  let φG : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ := fun x y => if y ∈ S then wC * twChg G σ y x else 0
  let φM : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ := fun x y => if y ∈ S then wC * twChg M σ y x else 0
  have hφ : ∀ x y, φ x y = φG x y - φM x y := by
    intro x y
    simp only [φ, φG, φM]
    split_ifs
    · rw [TwistFold2_twChg_sub (ι := Idx d (sz.L n) (sz.W n)) G M σ y x]; ring
    · simp
  have hwCs : star wC = wC := by
    rw [hwC]; simp
  set K : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ := twChg (fun p q => G p q - M p q) σ with hK
  have hKb : ∀ y x, ‖K y x‖ ≤ b := fun y x =>
    TwistFold2_norm_twChg_le (fun p q => G p q - M p q) σ y x b hb
  have hKGb : True := trivial
  -- (P1)
  have hP1 : ∀ x v, wC * ∑ y ∈ S, (G v y - M v y) * K y x = ∑ y, (G v y - M v y) * φ x y := by
    intro x v
    simp only [φ, mul_ite, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  -- (P2)
  have hvec : ∀ x, ∑ v, ‖wC * ∑ y ∈ S, (G v y - M v y) * K y x‖ ^ 2 ≤
      2 * η⁻¹ * (TwistFold2_Q G (φ x)).im + 2 * ∑ v, ‖∑ y, M v y * φ x y‖ ^ 2 := by
    intro x
    have h := twVec_holds G M η hη.ne' hG (φ x)
    unfold TwistFold2_Q
    simpa only [hP1 x] using h
  -- (P3), (P4)
  have hsupp : ∀ x v, v ∉ S → φ x v = 0 := by
    intro x v hv; simp [φ, hv]
  have hMphi : ∀ x, ∑ v, ‖∑ y, M v y * φ x y‖ ^ 2 ≤ u⁻¹ * b ^ 2 := by
    intro x
    refine (hMblk bb (φ x) (hsupp x)).trans ?_
    have h1 : ∑ y, ‖φ x y‖ ^ 2 = ∑ y ∈ S, ‖wC * K y x‖ ^ 2 := by
      have : ∀ y, ‖φ x y‖ ^ 2 = if y ∈ S then ‖wC * K y x‖ ^ 2 else 0 := by
        intro y; simp only [φ]; split_ifs with h
        · rfl
        · simp
      simp only [this]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [h1]
    calc ∑ y ∈ S, ‖wC * K y x‖ ^ 2 ≤ ∑ y ∈ S, (u⁻¹ * b) ^ 2 := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [norm_mul, hwCn]
          exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (hKb y x) (by positivity)) 2
      _ = u⁻¹ * b ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, hS, TwistFold2_card_blk, ← hu]
          field_simp
  -- (P5)
  have hQsplit : ∀ x, (TwistFold2_Q G (φ x)).im ≤ 2 * (TwistFold2_Q G (φG x)).im + 2 * (TwistFold2_Q G (φM x)).im := by
    intro x
    have h := TwistFold2_imQ_sub G η hη.le hG (φG x) (φM x)
    have e : φ x = fun y => φG x y - φM x y := funext (hφ x)
    rw [e]; exact h
  -- (P6) the `G`-part is the 3-loop
  have hQG : ∀ x, TwistFold2_Q G (φG x) =
      wC ^ 2 * ∑ y ∈ S, ∑ y' ∈ S, twChg G (!σ) x y * twChg G true y y' * twChg G σ y' x := by
    intro x
    have e : φG x = fun y => if y ∈ S then wC * twChg G σ y x else 0 := rfl
    rw [e, TwistFold2_Q_ind, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y' _ => ?_
    have htrue : twChg G true y y' = G y y' := by simp [twChg]
    rw [star_mul', hwCs, TwistFold2_star_twChg G σ x y, htrue]
    ring
  have hP6 : ∑ x ∈ twBlk n a, (TwistFold2_Q G (φG x)).im ≤ u * l3 := by
    have e : ∑ x ∈ twBlk n a, TwistFold2_Q G (φG x) = wC ^ 2 * ∑ x ∈ twBlk n a, ∑ y ∈ S, ∑ w ∈ S,
        twChg G (!σ) x y * twChg G true y w * twChg G σ w x := by
      simp only [hQG, ← Finset.mul_sum]
    calc ∑ x ∈ twBlk n a, (TwistFold2_Q G (φG x)).im = (∑ x ∈ twBlk n a, TwistFold2_Q G (φG x)).im :=
          (Complex.im_sum _ _).symm
      _ ≤ ‖∑ x ∈ twBlk n a, TwistFold2_Q G (φG x)‖ := Complex.im_le_norm _
      _ = u⁻¹ ^ 2 * ‖∑ x ∈ twBlk n a, ∑ y ∈ S, ∑ w ∈ S, twChg G (!σ) x y * twChg G true y w * twChg G σ w x‖ := by
          rw [e, norm_mul, norm_pow, hwCn]
      _ ≤ u⁻¹ ^ 2 * (u ^ 3 * l3) := by gcongr
      _ = u * l3 := by field_simp
  -- (P7) the `M`-part is supported at the one point `(b, o(x))`
  have hQM : ∀ x, (TwistFold2_Q G (φM x)).im ≤ u⁻¹ ^ 2 * (G (twShift n bb x) (twShift n bb x)).im := by
    intro x
    set s := twShift n bb x with hs
    have hsS : s ∈ S := TwistFold2_shift_mem n bb x
    have hKM0 : ∀ y ∈ S, y ≠ s → twChg M σ y x = 0 := by
      intro y hy hne
      have hne2 : (split d (sz.L n) (sz.W n) y).2 ≠ (split d (sz.L n) (sz.W n) x).2 := by
        intro heq
        apply hne
        apply split_injective d (sz.L n) (sz.W n)
        rw [hs, TwistFold2_split_shift]
        exact Prod.ext ((TwistFold2_mem_blk n).1 hy) heq
      cases σ
      · simp [twChg, hMtie x y (Ne.symm hne2)]
      · simp [twChg, hMtie y x hne2]
    have e : φM x = fun y => if y ∈ S then wC * twChg M σ y x else 0 := rfl
    have hinner : ∑ v ∈ S, G s v * (wC * twChg M σ v x) = G s s * (wC * twChg M σ s x) := by
      rw [Finset.sum_eq_single s]
      · intro y hy hne; rw [hKM0 y hy hne]; simp
      · intro h; exact absurd hsS h
    have houter : ∑ u ∈ S, star (wC * twChg M σ u x) * ∑ v ∈ S, G u v * (wC * twChg M σ v x) =
        star (wC * twChg M σ s x) * ∑ v ∈ S, G s v * (wC * twChg M σ v x) := by
      rw [Finset.sum_eq_single s]
      · intro y hy hne; rw [hKM0 y hy hne]; simp
      · intro h; exact absurd hsS h
    rw [e, TwistFold2_Q_ind, houter, hinner]
    set c : ℂ := wC * twChg M σ s x with hc
    have hcn : ‖c‖ ≤ u⁻¹ := by
      rw [hc, norm_mul, hwCn]
      calc u⁻¹ * ‖twChg M σ s x‖ ≤ u⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left (TwistFold2_norm_twChg_le M σ s x 1 hMle) (by positivity)
        _ = u⁻¹ := mul_one _
    have e2 : star c * (G s s * c) = G s s * ((‖c‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def]
      push_cast
      rw [← Complex.conj_mul' c]
      ring
    rw [e2, Complex.im_mul_ofReal]
    calc (G s s).im * ‖c‖ ^ 2 ≤ (G s s).im * (u⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hcn 2) (hImG s)
      _ = u⁻¹ ^ 2 * (G s s).im := by ring
  have hP7 : ∑ x ∈ twBlk n a, (TwistFold2_Q G (φM x)).im ≤ u⁻¹ * l1 := by
    calc ∑ x ∈ twBlk n a, (TwistFold2_Q G (φM x)).im
        ≤ ∑ x ∈ twBlk n a, u⁻¹ ^ 2 * (G (twShift n bb x) (twShift n bb x)).im := Finset.sum_le_sum fun x _ => hQM x
      _ = u⁻¹ ^ 2 * ∑ y ∈ S, (G y y).im := by
          rw [← Finset.mul_sum, TwistFold2_sum_shift n a bb (fun y => (G y y).im)]
      _ ≤ u⁻¹ ^ 2 * (u * l1) := by gcongr
      _ = u⁻¹ * l1 := by field_simp
  -- (P8) the sum over `x ∈ [a]`
  have hη' : 0 ≤ η⁻¹ := by positivity
  have hfin : ∀ x, ∑ v, ‖wC * ∑ y ∈ S, (G v y - M v y) * K y x‖ ^ 2 ≤
      4 * η⁻¹ * (TwistFold2_Q G (φG x)).im + 4 * η⁻¹ * (TwistFold2_Q G (φM x)).im + 2 * (u⁻¹ * b ^ 2) := by
    intro x
    have h1 := hvec x
    have h2 := hMphi x
    have h3 := hQsplit x
    nlinarith
  calc ∑ x ∈ twBlk n a, ∑ v, ‖wC * ∑ y ∈ S, (G v y - M v y) * K y x‖ ^ 2
      ≤ ∑ x ∈ twBlk n a, (4 * η⁻¹ * (TwistFold2_Q G (φG x)).im + 4 * η⁻¹ * (TwistFold2_Q G (φM x)).im +
          2 * (u⁻¹ * b ^ 2)) := Finset.sum_le_sum fun x _ => hfin x
    _ = 4 * η⁻¹ * ∑ x ∈ twBlk n a, (TwistFold2_Q G (φG x)).im + 4 * η⁻¹ * ∑ x ∈ twBlk n a, (TwistFold2_Q G (φM x)).im +
          2 * b ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
          nsmul_eq_mul, TwistFold2_card_blk, ← hu]
        field_simp
    _ ≤ 4 * η⁻¹ * (u * l3) + 4 * η⁻¹ * (u⁻¹ * l1) + 2 * b ^ 2 := by
        have := mul_le_mul_of_nonneg_left hP6 (by positivity : 0 ≤ 4 * η⁻¹)
        have := mul_le_mul_of_nonneg_left hP7 (by positivity : 0 ≤ 4 * η⁻¹)
        linarith
    _ = 4 * η⁻¹ * u * l3 + 4 * η⁻¹ * u⁻¹ * l1 + 2 * b ^ 2 := by ring

end Abstract


/-! ## 3. The marginals at the carrier -/

section PathwiseCarrier
variable {d : ℕ} {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}

/-- `η_t ≤ 1` along the flow (`Im m_F ≤ ‖m_F‖ ≤ 1`, `0 ≤ 1 - t ≤ 1`). -/
theorem TwistFold2_eta_le_one (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ BAflowT0 sz z n) : (baFMz sz z).eta n t ≤ 1 := by
  obtain ⟨ht1, hr, hmi, -, -⟩ := ba_G_data hκ sz hflow n ht0 ht
  have hnorm : ‖BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n‖ ≤ 1 :=
    BAm_norm_le_one d (sz.L n) _ _ _ (by simp) hr.1
  have hm : (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im ≤ 1 := (Complex.im_le_norm _).trans hnorm
  have e : (baFMz sz z).eta n t = (1 - t) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := rfl
  rw [e]
  calc (1 - t) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im ≤ 1 * 1 :=
        mul_le_mul (by linarith) hm hmi.le zero_le_one
    _ = 1 := one_mul 1

/-- `G_t` of the carrier as a matrix on the fine lattice. -/
def TwistFold2_Gm (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ := (baFMz sz z).G n t ω

/-- The resolvent identity `G - G^* = 2iη G^*G` at the carrier. -/
theorem TwistFold2_gram (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ BAflowT0 sz z n) (ω : sz.SeqΩ) :
    TwistFold2_Gm sz z n t ω - (TwistFold2_Gm sz z n t ω)ᴴ =
      (2 * (((baFMz sz z).eta n t : ℝ) : ℂ) * Complex.I) •
        ((TwistFold2_Gm sz z n t ω)ᴴ * TwistFold2_Gm sz z n t ω) := by
  obtain ⟨-, -, -, hzi, -⟩ := ba_G_data hκ sz hflow n ht0 ht
  have hH := BAExpand_Hm_isHermitian sz n (BAflowLam0 sz z n) t ω
  have e : (baFMz sz z).eta n t = (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t).im := by
    rw [ztOf_im]; rfl
  unfold TwistFold2_Gm
  rw [BAExp14a_G_green, e]
  exact TwistFold2_gram_green hH hzi.ne'

/-- `Σ_{x∈[c]} Im G_{xx} = W^d Im 𝓛^{(1)}_{+,c}`. -/
theorem TwistFold2_L1_im (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (c : Zd d (sz.L n)) :
    ∑ x ∈ twBlk n c, ((baFMz sz z).G n t ω x x).im =
      ((sz.W n : ℕ) : ℝ) ^ d * ((baFMz sz z).L n t (fun _ : Fin 1 => true) (fun _ => c) ω).im := by
  have hW : (((sz.W n : ℕ) : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (sz.W_pos n).ne')
  have h1 := BAExp14a_L1_eq (sz := sz) (z := z) n t ω c
  have h2 : ((sz.W n : ℕ) : ℂ) ^ d * (baFMz sz z).L n t (fun _ : Fin 1 => true) (fun _ => c) ω =
      ∑ x ∈ twBlk n c, (baFMz sz z).G n t ω x x := by
    rw [h1]
    change _ = ∑ x ∈ Iblk d (sz.L n) (sz.W n) c, _
    rw [← mul_assoc, mul_inv_cancel₀ hW, one_mul]
  have h3 := congrArg Complex.im h2
  have hc : ((sz.W n : ℕ) : ℂ) ^ d = ((((sz.W n : ℕ) : ℝ) ^ d : ℝ) : ℂ) := by push_cast; rfl
  rw [hc, Complex.im_ofReal_mul, Complex.im_sum] at h3
  exact h3.symm

/-- The `S_A` marginal at the carrier. -/
theorem TwistFold2_SA_carrier (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ BAflowT0 sz z n) (ω : sz.SeqΩ) (l1 : ℝ)
    (hl1 : ∀ c, ‖(baFMz sz z).L n t (fun _ : Fin 1 => true) (fun _ => c) ω‖ ≤ l1) (a : Zd d (sz.L n)) :
    ∑ x ∈ twBlk n a, ∑ v, ‖(baFMz sz z).GM n t ω x v‖ ^ 2 ≤
      2 * ((baFMz sz z).eta n t)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d) * (l1 + 1) := by
  obtain ⟨-, hr, hmi, -, -⟩ := ba_G_data hκ sz hflow n ht0 ht
  have hη := BAExp14a_eta_pos hκ hflow n ht0 ht
  refine TwistFold2_SA n ((baFMz sz z).G n t ω) ((baFMz sz z).M n) _ l1 hη (TwistFold2_eta_le_one hκ hflow n ht0 ht)
    (fun x => (BAExp14a_G_ward hκ hflow n ht0 ht ω x).1) (fun x => twMrow_le_holds sz _ _ n hr.1 x) a ?_
  rw [TwistFold2_L1_im]
  exact mul_le_mul_of_nonneg_left ((Complex.im_le_norm _).trans (hl1 a)) (TwistFold2_u_pos n).le

/-- The `S_C` marginal at the carrier (S3A-C1: the BA expansion of the circled legs). -/
theorem TwistFold2_SC_carrier (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ BAflowT0 sz z n) (ω : sz.SeqΩ) (b l1 l3 : ℝ)
    (hb : ∀ x y, ‖(baFMz sz z).GM n t ω x y‖ ≤ b)
    (hl1 : ∀ c, ‖(baFMz sz z).L n t (fun _ : Fin 1 => true) (fun _ => c) ω‖ ≤ l1)
    (hl3 : ∀ (σ : Fin 3 → Bool) (a : Fin 3 → Zd d (sz.L n)), ‖(baFMz sz z).L n t σ a ω‖ ≤ l3)
    (σ : Bool) (a bb : Zd d (sz.L n)) :
    ∑ x ∈ twBlk n a, ∑ v, ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ y ∈ twBlk n bb, (baFMz sz z).GM n t ω v y *
        twChg ((baFMz sz z).GM n t ω) σ y x‖ ^ 2 ≤
      4 * ((baFMz sz z).eta n t)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d) * l3 +
        4 * ((baFMz sz z).eta n t)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * l1 + 2 * b ^ 2 := by
  obtain ⟨-, hr, hmi, -, -, hMle⟩ := ba_G_data hκ sz hflow n ht0 ht
  have hη := BAExp14a_eta_pos hκ hflow n ht0 ht
  have hu0 := TwistFold2_u_pos (sz := sz) n
  refine TwistFold2_SC n (TwistFold2_Gm sz z n t ω) ((baFMz sz z).M n) _ b l1 l3 hη (TwistFold2_gram hκ hflow n ht0 ht ω)
    ?_ hMle (fun c φ hφ => twMblk_le_holds sz _ _ n hr.1 c φ hφ) ?_ hb σ a bb ?_ ?_
  · intro x y hxy
    change BAMfine sz (BAflowLam0 sz z) (BAflowEs sz z) n x y = 0
    rw [BAMfine_eq sz _ _ n hmi x y]
    simp [hxy]
  · intro x
    change 0 ≤ ((baFMz sz z).G n t ω x x).im
    have := (BAExp14a_G_ward hκ hflow n ht0 ht ω x).1
    nlinarith [Finset.sum_nonneg (fun y (_ : y ∈ Finset.univ) => sq_nonneg ‖(baFMz sz z).G n t ω x y‖)]
  · change ∑ y ∈ twBlk n bb, ((baFMz sz z).G n t ω y y).im ≤ _
    rw [TwistFold2_L1_im]
    exact mul_le_mul_of_nonneg_left ((Complex.im_le_norm _).trans (hl1 bb)) hu0.le
  · have h3 := TwistFold2_L3_carrier (sz := sz) (z := z) n t ω ![!σ, true, σ] ![bb, bb, a]
    have h4 := hl3 ![!σ, true, σ] ![bb, bb, a]
    rw [h3] at h4
    have hwn : ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹‖ = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := TwistFold2_norm_inv_pow n
    rw [norm_mul, norm_pow, hwn] at h4
    change ‖∑ x ∈ twBlk n a, ∑ y ∈ twBlk n bb, ∑ w ∈ twBlk n bb, twChg ((baFMz sz z).G n t ω) (!σ) x y *
        twChg ((baFMz sz z).G n t ω) true y w * twChg ((baFMz sz z).G n t ω) σ w x‖ ≤ _
    set S3 := ‖∑ x ∈ twBlk n a, ∑ y ∈ twBlk n bb, ∑ w ∈ twBlk n bb, twChg ((baFMz sz z).G n t ω) (!σ) x y *
        twChg ((baFMz sz z).G n t ω) true y w * twChg ((baFMz sz z).G n t ω) σ w x‖ with hS3
    have h5 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ 3 * S3 ≤ l3 := h4
    have hpos : 0 < (((sz.W n : ℕ) : ℝ) ^ d) ^ 3 := pow_pos hu0 3
    calc S3 = (((sz.W n : ℕ) : ℝ) ^ d) ^ 3 * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ 3 * S3) := by
          field_simp
      _ ≤ (((sz.W n : ℕ) : ℝ) ^ d) ^ 3 * l3 := mul_le_mul_of_nonneg_left h5 hpos.le

/-- **The pathwise bound of the node** at a fixed sample: `|twLoop2X|² ≤ W^{-5d} (β r₁ r₂) S_A S_C` with `β = W^d b²`,
`r₁ = r₂ = Cρ Y`, and the marginals `S_A`, `S_C` of `TwistFold2_SA_carrier`, `TwistFold2_SC_carrier`. -/
theorem TwistFold2_pathwise (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ BAflowT0 sz z n) (ω : sz.SeqΩ) (b l1 l3 Y Cρ : ℝ)
    (hb : ∀ x y, ‖(baFMz sz z).GM n t ω x y‖ ≤ b)
    (hl1 : ∀ c, ‖(baFMz sz z).L n t (fun _ : Fin 1 => true) (fun _ => c) ω‖ ≤ l1)
    (hl3 : ∀ (σ : Fin 3 → Bool) (a : Fin 3 → Zd d (sz.L n)), ‖(baFMz sz z).L n t σ a ω‖ ≤ l3)
    (σ : Bool) (a bb : Zd d (sz.L n))
    (ρ X : Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → ℂ)
    (hρ1 : ∀ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖ ≤ Cρ) (hρ2 : ∀ c₄, ∑ c₁, ∑ c₂, ∑ c₃, ‖ρ c₁ c₂ c₃ c₄‖ ≤ Cρ)
    (hY : ∀ c₁ c₂ c₃ c₄, ‖X c₁ c₂ c₃ c₄‖ ≤ Y) :
    ‖twLoop2X n ((baFMz sz z).GM n t ω) ((baFMz sz z).GM n t ω)
        (fun (u x : Idx d (sz.L n) (sz.W n)) => (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ y ∈ twBlk n bb,
          (baFMz sz z).GM n t ω u y * twChg ((baFMz sz z).GM n t ω) σ y x)
        (fun c₁ c₂ c₃ c₄ => ρ c₁ c₂ c₃ c₄ * X c₁ c₂ c₃ c₄) a‖ ^ 2 ≤
      ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 5 * ((((sz.W n : ℕ) : ℝ) ^ d * b ^ 2) * (Cρ * Y) * (Cρ * Y)) *
        (2 * ((baFMz sz z).eta n t)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d) * (l1 + 1)) *
        (4 * ((baFMz sz z).eta n t)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d) * l3 +
          4 * ((baFMz sz z).eta n t)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * l1 + 2 * b ^ 2) := by
  set u : ℝ := ((sz.W n : ℕ) : ℝ) ^ d with hu
  have hu0 : 0 < u := TwistFold2_u_pos n
  have hη := BAExp14a_eta_pos hκ hflow n ht0 ht
  set η : ℝ := (baFMz sz z).eta n t with hηdef
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0 0)
  have hY0 : 0 ≤ Y := (norm_nonneg _).trans (hY a a a a)
  have hl10 : 0 ≤ l1 := (norm_nonneg _).trans (hl1 a)
  have hCρ0 : 0 ≤ Cρ := (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    norm_nonneg _).trans (hρ1 a)
  have hβ : ∀ (v : Idx d (sz.L n) (sz.W n)) (c : Zd d (sz.L n)),
      ∑ w ∈ twBlk n c, ‖(baFMz sz z).GM n t ω v w‖ ^ 2 ≤ u * b ^ 2 := by
    intro v c
    calc ∑ w ∈ twBlk n c, ‖(baFMz sz z).GM n t ω v w‖ ^ 2 ≤ ∑ w ∈ twBlk n c, b ^ 2 :=
          Finset.sum_le_sum fun w _ => pow_le_pow_left₀ (norm_nonneg _) (hb v w) 2
      _ = u * b ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul, TwistFold2_card_blk]
  have hr1 : ∀ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄ * X c₁ c₂ c₃ c₄‖ ≤ Cρ * Y := by
    intro c₁
    calc ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄ * X c₁ c₂ c₃ c₄‖ ≤ ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖ * Y :=
          Finset.sum_le_sum fun c₂ _ => Finset.sum_le_sum fun c₃ _ => Finset.sum_le_sum fun c₄ _ => by
            rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hY c₁ c₂ c₃ c₄) (norm_nonneg _)
      _ = (∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖) * Y := by simp only [Finset.sum_mul]
      _ ≤ Cρ * Y := mul_le_mul_of_nonneg_right (hρ1 c₁) hY0
  have hr2 : ∀ c₄, ∑ c₁, ∑ c₂, ∑ c₃, ‖ρ c₁ c₂ c₃ c₄ * X c₁ c₂ c₃ c₄‖ ≤ Cρ * Y := by
    intro c₄
    calc ∑ c₁, ∑ c₂, ∑ c₃, ‖ρ c₁ c₂ c₃ c₄ * X c₁ c₂ c₃ c₄‖ ≤ ∑ c₁, ∑ c₂, ∑ c₃, ‖ρ c₁ c₂ c₃ c₄‖ * Y :=
          Finset.sum_le_sum fun c₁ _ => Finset.sum_le_sum fun c₂ _ => Finset.sum_le_sum fun c₃ _ => by
            rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hY c₁ c₂ c₃ c₄) (norm_nonneg _)
      _ = (∑ c₁, ∑ c₂, ∑ c₃, ‖ρ c₁ c₂ c₃ c₄‖) * Y := by simp only [Finset.sum_mul]
      _ ≤ Cρ * Y := mul_le_mul_of_nonneg_right (hρ2 c₄) hY0
  have h := twFold2_bound_holds d sz n ((baFMz sz z).GM n t ω) ((baFMz sz z).GM n t ω)
    (fun (v x : Idx d (sz.L n) (sz.W n)) => (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ y ∈ twBlk n bb,
      (baFMz sz z).GM n t ω v y * twChg ((baFMz sz z).GM n t ω) σ y x)
    (fun c₁ c₂ c₃ c₄ => ρ c₁ c₂ c₃ c₄ * X c₁ c₂ c₃ c₄) a (u * b ^ 2) (Cρ * Y) (Cρ * Y) hβ hr1 hr2
  have hSA := TwistFold2_SA_carrier hκ hflow n ht0 ht ω l1 hl1 a
  have hSC := TwistFold2_SC_carrier hκ hflow n ht0 ht ω b l1 l3 hb hl1 hl3 σ a bb
  refine h.trans ?_
  have hA0 : 0 ≤ ∑ x ∈ twBlk n a, ∑ v, ‖(baFMz sz z).GM n t ω x v‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hC0 : 0 ≤ ∑ x ∈ twBlk n a, ∑ v, ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ y ∈ twBlk n bb,
      (baFMz sz z).GM n t ω v y * twChg ((baFMz sz z).GM n t ω) σ y x‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hP0 : 0 ≤ (u⁻¹) ^ 5 * ((u * b ^ 2) * (Cρ * Y) * (Cρ * Y)) := by positivity
  have hη0 : 0 ≤ η⁻¹ := by positivity
  refine mul_le_mul (mul_le_mul_of_nonneg_left hSA hP0) hSC hC0 ?_
  positivity

end PathwiseCarrier

/-! ## 4. The arithmetic of the exponent table -/

/-- The arithmetic of the `≺` row (exponent table, rows 9-10 of the 1a). -/
theorem TwistFold2_arith (u B η c0 Cρ b l1 l3 Y Z : ℝ) (hu : 0 < u) (hB : 0 < B) (hη : 0 < η) (hη1 : η ≤ 1)
    (hc0 : 0 < c0) (hBc : c0 ≤ u * B) (hCρ : 0 ≤ Cρ) (hb : 0 ≤ b) (hl1 : 0 ≤ l1) (hl3 : 0 ≤ l3) (hY : 0 ≤ Y)
    (hZ : 1 ≤ Z) (hb2 : b ^ 2 ≤ B * Z) (hl1Z : l1 ≤ Z) (hl3Z : l3 ≤ B ^ 2 * Z) (hYZ : Y ≤ u * B * Z) :
    (u⁻¹) ^ 5 * ((u * b ^ 2) * (Cρ * Y) * (Cρ * Y)) * (2 * η⁻¹ * u * (l1 + 1)) *
        (4 * η⁻¹ * u * l3 + 4 * η⁻¹ * u⁻¹ * l1 + 2 * b ^ 2) ≤
      (16 + 16 * c0⁻¹ ^ 2 + 8 * c0⁻¹) * Cρ ^ 2 * η⁻¹ ^ 2 * B ^ 5 * Z ^ 5 := by
  have hZ0 : 0 < Z := by linarith
  have hηi : 1 ≤ η⁻¹ := (one_le_inv₀ hη).mpr hη1
  have hηi0 : 0 < η⁻¹ := by positivity
  have hui : u⁻¹ ≤ c0⁻¹ * B := by
    rw [inv_le_iff_one_le_mul₀ hu]
    have : 1 ≤ c0⁻¹ * B * u := by
      have : c0⁻¹ * (u * B) ≥ 1 := by
        rw [ge_iff_le, ← div_eq_inv_mul, le_div_iff₀ hc0]; linarith
      nlinarith
    linarith
  have hui0 : 0 < u⁻¹ := by positivity
  -- step 1: monotonicity in the four random quantities
  have h1 : (u⁻¹) ^ 5 * ((u * b ^ 2) * (Cρ * Y) * (Cρ * Y)) ≤ (u⁻¹) ^ 5 * ((u * (B * Z)) * (Cρ * (u * B * Z)) * (Cρ * (u * B * Z))) := by
    gcongr
  have h2 : 2 * η⁻¹ * u * (l1 + 1) ≤ 2 * η⁻¹ * u * (Z + Z) := by gcongr
  have h3 : 4 * η⁻¹ * u * l3 + 4 * η⁻¹ * u⁻¹ * l1 + 2 * b ^ 2 ≤
      4 * η⁻¹ * u * (B ^ 2 * Z) + 4 * η⁻¹ * u⁻¹ * Z + 2 * (B * Z) := by gcongr
  have hP0 : 0 ≤ (u⁻¹) ^ 5 * ((u * b ^ 2) * (Cρ * Y) * (Cρ * Y)) := by positivity
  have hQ0 : 0 ≤ 2 * η⁻¹ * u * (l1 + 1) := by positivity
  calc (u⁻¹) ^ 5 * ((u * b ^ 2) * (Cρ * Y) * (Cρ * Y)) * (2 * η⁻¹ * u * (l1 + 1)) *
        (4 * η⁻¹ * u * l3 + 4 * η⁻¹ * u⁻¹ * l1 + 2 * b ^ 2)
      ≤ (u⁻¹) ^ 5 * ((u * (B * Z)) * (Cρ * (u * B * Z)) * (Cρ * (u * B * Z))) * (2 * η⁻¹ * u * (Z + Z)) *
        (4 * η⁻¹ * u * (B ^ 2 * Z) + 4 * η⁻¹ * u⁻¹ * Z + 2 * (B * Z)) := by
        refine mul_le_mul (mul_le_mul h1 h2 hQ0 (by positivity)) h3 (by positivity) (by positivity)
    _ = 4 * Cρ ^ 2 * η⁻¹ * Z ^ 5 * B ^ 3 * (4 * η⁻¹ * B ^ 2 + 4 * η⁻¹ * u⁻¹ ^ 2 + 2 * u⁻¹ * B) := by
        field_simp
        ring
    _ ≤ 4 * Cρ ^ 2 * η⁻¹ * Z ^ 5 * B ^ 3 * (η⁻¹ * B ^ 2 * (4 + 4 * c0⁻¹ ^ 2 + 2 * c0⁻¹)) := by
        have e1 : u⁻¹ ^ 2 ≤ c0⁻¹ ^ 2 * B ^ 2 := by
          calc u⁻¹ ^ 2 ≤ (c0⁻¹ * B) ^ 2 := pow_le_pow_left₀ hui0.le hui 2
            _ = c0⁻¹ ^ 2 * B ^ 2 := by ring
        have e2 : u⁻¹ * B ≤ c0⁻¹ * B ^ 2 := by
          calc u⁻¹ * B ≤ (c0⁻¹ * B) * B := mul_le_mul_of_nonneg_right hui hB.le
            _ = c0⁻¹ * B ^ 2 := by ring
        have e3 : 4 * η⁻¹ * B ^ 2 + 4 * η⁻¹ * u⁻¹ ^ 2 + 2 * u⁻¹ * B ≤ η⁻¹ * B ^ 2 * (4 + 4 * c0⁻¹ ^ 2 + 2 * c0⁻¹) := by
          have hc : 0 < c0⁻¹ := by positivity
          nlinarith [mul_le_mul_of_nonneg_left e1 (by positivity : 0 ≤ 4 * η⁻¹),
            mul_le_mul_of_nonneg_left e2 (by positivity : (0 : ℝ) ≤ 2), mul_le_mul_of_nonneg_right hηi (by positivity : 0 ≤ 2 * c0⁻¹ * B ^ 2)]
        gcongr
    _ = (16 + 16 * c0⁻¹ ^ 2 + 8 * c0⁻¹) * Cρ ^ 2 * η⁻¹ ^ 2 * B ^ 5 * Z ^ 5 := by ring


/-! ## 5. `≺` of one-index random variables: normalisation, suprema, powers, square roots -/

section DomLemmas
variable {d : ℕ} {sz : Sizes d} {μ : Measure sz.SeqΩ}

/-- `f ≺ g` with `g > 0` gives `f / g ≺ 1`. -/
theorem TwistFold2_dom_div {f : ℕ → sz.SeqΩ → ℝ} {g : ℕ → ℝ} (hg : ∀ n, 0 < g n) (h : BAExp14a_Dom sz μ f g) :
    BAExp14a_Dom sz μ (fun n ω => f n ω / g n) (fun _ => 1) := by
  unfold BAExp14a_Dom PrecL at h ⊢
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun n ω hω => ?_⟩
  obtain ⟨⟨⟩, hu⟩ := hω
  refine ⟨(), ?_⟩
  change ((sz.size n : ℕ) : ℝ) ^ τ * 1 < f n ω / g n at hu
  change ((sz.size n : ℕ) : ℝ) ^ τ * g n < f n ω
  rw [mul_one, lt_div_iff₀ (hg n)] at hu
  exact hu

/-- A supremum over a finite index type is dominated as soon as the family is (the union over the index is inside `P`). -/
theorem TwistFold2_dom_sup {V : ℕ → Type} [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    (f : ∀ n, V n → sz.SeqΩ → ℝ) (g : ℕ → ℝ) (h : PrecL sz μ f (fun n _ _ => g n)) :
    BAExp14a_Dom sz μ (fun n ω => Finset.univ.sup' Finset.univ_nonempty (fun v => f n v ω)) g := by
  unfold PrecL at h
  unfold BAExp14a_Dom PrecL
  refine BAExp14a_prec_of_bad h fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun n ω hω => ?_⟩
  obtain ⟨⟨⟩, hu⟩ := hω
  obtain ⟨v, -, hv⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := V n)) (fun v => f n v ω)
  refine ⟨v, ?_⟩
  change ((sz.size n : ℕ) : ℝ) ^ τ * g n < Finset.univ.sup' Finset.univ_nonempty (fun v => f n v ω) at hu
  change ((sz.size n : ℕ) : ℝ) ^ τ * g n < f n v ω
  rw [hv] at hu
  exact hu

/-- Powers of a `≺ 1` variable. -/
theorem TwistFold2_dom_pow (hsz : Tendsto sz.size atTop atTop) {Z : ℕ → sz.SeqΩ → ℝ} (hZ0 : ∀ n ω, 0 ≤ Z n ω)
    (h : BAExp14a_Dom sz μ Z (fun _ => 1)) (k : ℕ) : BAExp14a_Dom sz μ (fun n ω => Z n ω ^ k) (fun _ => 1) := by
  induction k with
  | zero => simpa using BAExp14a_Dom.refl (μ := μ) hsz (g := fun _ => (1 : ℝ)) (fun _ => zero_le_one)
  | succ k ih =>
    have h1 := BAExp14a_Dom.mul hsz (fun n ω => hZ0 n ω) (fun _ => zero_le_one) ih h
    have h2 := BAExp14a_Dom.mono hsz (K := 1) one_pos (fun _ => zero_le_one)
      (Eventually.of_forall fun n => by norm_num) h1
    exact BAExp14a_Dom.of_le hsz (fun n ω => by rw [pow_succ]) h2

/-- `f² ≺ g²` gives `f ≺ g` for non-negative families. -/
theorem TwistFold2_prec_sqrt {U : ℕ → Type*} {f g : ∀ n, U n → sz.SeqΩ → ℝ} (hf : ∀ n u ω, 0 ≤ f n u ω)
    (hg : ∀ n u ω, 0 ≤ g n u ω) (h : PrecL sz μ (fun n u ω => f n u ω ^ 2) (fun n u ω => g n u ω ^ 2)) :
    PrecL sz μ f g := by
  unfold PrecL at h ⊢
  refine StochDomAt.of_subset h fun τ hτ => ⟨2 * τ, by positivity, Eventually.of_forall fun n ω hω => ?_⟩
  obtain ⟨u, hu⟩ := hω
  refine ⟨u, ?_⟩
  have hN : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ * g n u ω := mul_nonneg (Real.rpow_nonneg hN _) (hg n u ω)
  have h2 : (((sz.size n : ℕ) : ℝ) ^ τ * g n u ω) ^ 2 < f n u ω ^ 2 := pow_lt_pow_left₀ hu h1 two_ne_zero
  have h3 : (((sz.size n : ℕ) : ℝ) ^ τ) ^ 2 = ((sz.size n : ℕ) : ℝ) ^ (2 * τ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN, mul_comm]; norm_num
  rw [mul_pow, h3] at h2
  exact h2

end DomLemmas

/-! ## 6. The maxima of the random inputs -/

section Maxima
variable {d : ℕ} {sz : Sizes d}

/-- `max_{σ,a} ‖𝓛^{(k)}_{t,σ,a}‖` at a sample (the supremum over the finite index of `STLmaxgL`). -/
def TwistFold2_lmax (sz : Sizes d) (z : ℕ → ℂ) (t : ℕ → ℝ) (k n : ℕ) (ω : sz.SeqΩ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
    ‖(baFMz sz z).L n (t n) p.1 p.2 ω‖)

theorem TwistFold2_le_lmax (z : ℕ → ℂ) (t : ℕ → ℝ) (k n : ℕ) (ω : sz.SeqΩ) (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) : ‖(baFMz sz z).L n (t n) σ a ω‖ ≤ TwistFold2_lmax sz z t k n ω :=
  Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) => ‖(baFMz sz z).L n (t n) p.1 p.2 ω‖)
    (Finset.mem_univ (σ, a))

theorem TwistFold2_lmax_nonneg (z : ℕ → ℂ) (t : ℕ → ℝ) (k n : ℕ) (ω : sz.SeqΩ) :
    0 ≤ TwistFold2_lmax sz z t k n ω :=
  (norm_nonneg _).trans (TwistFold2_le_lmax z t k n ω (fun _ => true) (fun _ => 0))

theorem TwistFold2_dom_lmax {μ : Measure sz.SeqΩ} {z : ℕ → ℂ} {t : ℕ → ℝ} {k : ℕ} {g : ℕ → ℝ}
    (h : PrecL sz μ (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖(baFMz sz z).L n (t n) p.1 p.2 ω‖) (fun n _ _ => g n)) :
    BAExp14a_Dom sz μ (fun n ω => TwistFold2_lmax sz z t k n ω) g :=
  TwistFold2_dom_sup _ _ h

/-- `max_{q} ‖X(q)‖` at a sample, `q = (p, c₁, c₂, c₃, c₄)`. -/
def TwistFold2_Xmax (X : ∀ n, Bool × Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) →
    Zd d (sz.L n) → sz.SeqΩ → ℂ) (n : ℕ) (ω : sz.SeqΩ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun q : (Bool × Zd d (sz.L n) × Zd d (sz.L n)) × Zd d (sz.L n) × Zd d (sz.L n) ×
    Zd d (sz.L n) × Zd d (sz.L n) => ‖X n q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 ω‖)

theorem TwistFold2_le_Xmax (X : ∀ n, Bool × Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) →
    Zd d (sz.L n) → sz.SeqΩ → ℂ) (n : ℕ) (ω : sz.SeqΩ) (p : Bool × Zd d (sz.L n) × Zd d (sz.L n))
    (c₁ c₂ c₃ c₄ : Zd d (sz.L n)) : ‖X n p c₁ c₂ c₃ c₄ ω‖ ≤ TwistFold2_Xmax X n ω :=
  Finset.le_sup' (fun q : (Bool × Zd d (sz.L n) × Zd d (sz.L n)) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n) ×
    Zd d (sz.L n) => ‖X n q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 ω‖) (Finset.mem_univ (p, c₁, c₂, c₃, c₄))

theorem TwistFold2_Xmax_nonneg (X : ∀ n, Bool × Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) →
    Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℂ) (n : ℕ) (ω : sz.SeqΩ) : 0 ≤ TwistFold2_Xmax X n ω :=
  (norm_nonneg _).trans (TwistFold2_le_Xmax X n ω (true, 0, 0) 0 0 0 0)

theorem TwistFold2_dom_Xmax {μ : Measure sz.SeqΩ}
    {X : ∀ n, Bool × Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) →
      Zd d (sz.L n) → sz.SeqΩ → ℂ} {g : ℕ → ℝ}
    (h : PrecL sz μ (U := fun n => (Bool × Zd d (sz.L n) × Zd d (sz.L n)) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n) ×
      Zd d (sz.L n)) (fun n q ω => ‖X n q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 ω‖) (fun n _ _ => g n)) :
    BAExp14a_Dom sz μ (fun n ω => TwistFold2_Xmax X n ω) g :=
  TwistFold2_dom_sup _ _ h

/-- The normalised sum `Z = 1 + b²/B + ℓ₁ + ℓ₃/B² + Y/(W^d B)` and its four consequences. -/
theorem TwistFold2_Z_facts (u B b l1 l3 Y : ℝ) (hu : 0 < u) (hB : 0 < B) (hb : 0 ≤ b) (hl1 : 0 ≤ l1) (hl3 : 0 ≤ l3)
    (hY : 0 ≤ Y) :
    1 ≤ 1 + b ^ 2 / B + l1 + l3 / B ^ 2 + Y / (u * B) ∧ b ^ 2 ≤ B * (1 + b ^ 2 / B + l1 + l3 / B ^ 2 + Y / (u * B)) ∧
      l1 ≤ 1 + b ^ 2 / B + l1 + l3 / B ^ 2 + Y / (u * B) ∧
      l3 ≤ B ^ 2 * (1 + b ^ 2 / B + l1 + l3 / B ^ 2 + Y / (u * B)) ∧
      Y ≤ u * B * (1 + b ^ 2 / B + l1 + l3 / B ^ 2 + Y / (u * B)) := by
  have h1 : 0 ≤ b ^ 2 / B := by positivity
  have h2 : 0 ≤ l3 / B ^ 2 := by positivity
  have h3 : 0 ≤ Y / (u * B) := by positivity
  refine ⟨by linarith, ?_, by linarith, ?_, ?_⟩
  · have e : b ^ 2 = B * (b ^ 2 / B) := by field_simp
    nlinarith
  · have e : l3 = B ^ 2 * (l3 / B ^ 2) := by field_simp
    nlinarith [sq_nonneg B]
  · have e : Y = u * B * (Y / (u * B)) := by field_simp
    have : 0 < u * B := mul_pos hu hB
    nlinarith

/-- The normalised sum `Z = 1 + b²/B + ℓ₁ + ℓ₃/B² + Y/(W^d B)` of the four random inputs. -/
def TwistFold2_Z (sz : Sizes d) (z : ℕ → ℂ) (t : ℕ → ℝ)
    (X : ∀ n, Bool × Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) →
      Zd d (sz.L n) → sz.SeqΩ → ℂ) (n : ℕ) (ω : sz.SeqΩ) : ℝ :=
  1 + BAExp14a_b sz z n (t n) ω ^ 2 / sz.Bctl n (t n) + TwistFold2_lmax sz z t 1 n ω +
    TwistFold2_lmax sz z t 3 n ω / sz.Bctl n (t n) ^ 2 +
    TwistFold2_Xmax X n ω / (((sz.W n : ℕ) : ℝ) ^ d * sz.Bctl n (t n))

end Maxima

/-! ## 7. The row at a fixed sample -/

section Row
variable {d : ℕ} {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}

/-- **The pathwise form of the row**: `|twLoop2X|² ≤ K Cρ² κ⁻² ((1 - t)⁻¹ Bctl^{5/2})² Z⁵` with `Z` the normalised sum of the four
random inputs `b = max|Ǧ|`, `ℓ₁`, `ℓ₃`, `Y` and `K = 16 + 16 c₀⁻² + 8 c₀⁻¹`, `c₀ = (𝔡⁻² + 1)⁻¹` (S3A-C2: `c₀ ≤ W^d Bctl`;
S3A-C3: `η⁻¹ ≤ κ⁻¹ (1 - t)⁻¹`). -/
theorem TwistFold2_row (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (t : ℕ → ℝ) (ht0 : ∀ n, 0 ≤ t n)
    (htT : ∀ n, t n ≤ BAflowT0 sz z n) (n : ℕ) (ω : sz.SeqΩ) (c0 Cρ : ℝ) (hc0 : 0 < c0)
    (hn6 : c0 ≤ ((sz.W n : ℕ) : ℝ) ^ d * sz.Bctl n (t n)) (hCρ : 0 ≤ Cρ)
    (ρ : Bool × Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → ℂ)
    (hρ : ∀ p, (∀ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ p c₁ c₂ c₃ c₄‖ ≤ Cρ) ∧ (∀ c₄, ∑ c₁, ∑ c₂, ∑ c₃, ‖ρ p c₁ c₂ c₃ c₄‖ ≤ Cρ))
    (X : ∀ n, Bool × Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) →
      Zd d (sz.L n) → sz.SeqΩ → ℂ) (p : Bool × Zd d (sz.L n) × Zd d (sz.L n)) :
    ‖twLoop2X n ((baFMz sz z).GM n (t n) ω) ((baFMz sz z).GM n (t n) ω)
        (fun (u x : Idx d (sz.L n) (sz.W n)) => (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ y ∈ twBlk n p.2.2,
          (baFMz sz z).GM n (t n) ω u y * twChg ((baFMz sz z).GM n (t n) ω) p.1 y x)
        (fun c₁ c₂ c₃ c₄ => ρ p c₁ c₂ c₃ c₄ * X n p c₁ c₂ c₃ c₄ ω) p.2.1‖ ^ 2 ≤
      (16 + 16 * c0⁻¹ ^ 2 + 8 * c0⁻¹) * Cρ ^ 2 * κ⁻¹ ^ 2 *
        (((1 - t n)⁻¹ * sz.Bctl n (t n) ^ (5 / 2 : ℝ)) ^ 2 * TwistFold2_Z sz z t X n ω ^ 5) := by
  have hB : 0 < sz.Bctl n (t n) := STBctl_pos sz n (ba_G_data hκ sz hflow n (ht0 n) (htT n)).1
  have ht1 : t n < 1 := (ba_G_data hκ sz hflow n (ht0 n) (htT n)).1
  have hu : 0 < ((sz.W n : ℕ) : ℝ) ^ d := TwistFold2_u_pos n
  have hη := BAExp14a_eta_pos hκ hflow n (ht0 n) (htT n)
  have hη1 := TwistFold2_eta_le_one hκ hflow n (ht0 n) (htT n)
  set B : ℝ := sz.Bctl n (t n) with hBdef
  set u : ℝ := ((sz.W n : ℕ) : ℝ) ^ d with hudef
  set η : ℝ := (baFMz sz z).eta n (t n) with hηdef
  set b : ℝ := BAExp14a_b sz z n (t n) ω with hbdef
  set l1 : ℝ := TwistFold2_lmax sz z t 1 n ω with hl1def
  set l3 : ℝ := TwistFold2_lmax sz z t 3 n ω with hl3def
  set Y : ℝ := TwistFold2_Xmax X n ω with hYdef
  have hb0 : 0 ≤ b := BAExp14a_b_nonneg n (t n) ω
  have hl10 : 0 ≤ l1 := TwistFold2_lmax_nonneg z t 1 n ω
  have hl30 : 0 ≤ l3 := TwistFold2_lmax_nonneg z t 3 n ω
  have hY0 : 0 ≤ Y := TwistFold2_Xmax_nonneg X n ω
  obtain ⟨hZ1, hb2, hl1Z, hl3Z, hYZ⟩ := TwistFold2_Z_facts u B b l1 l3 Y hu hB hb0 hl10 hl30 hY0
  have hp := TwistFold2_pathwise hκ hflow n (ht0 n) (htT n) ω b l1 l3 Y Cρ (BAExp14a_le_b n (t n) ω)
    (fun c => TwistFold2_le_lmax z t 1 n ω (fun _ => true) (fun _ => c))
    (fun σ a => TwistFold2_le_lmax z t 3 n ω σ a) p.1 p.2.1 p.2.2 (ρ p) (fun c₁ c₂ c₃ c₄ => X n p c₁ c₂ c₃ c₄ ω)
    (hρ p).1 (hρ p).2 (fun c₁ c₂ c₃ c₄ => TwistFold2_le_Xmax X n ω p c₁ c₂ c₃ c₄)
  have ha := TwistFold2_arith u B η c0 Cρ b l1 l3 Y (TwistFold2_Z sz z t X n ω) hu hB hη hη1 hc0 hn6 hCρ hb0 hl10 hl30 hY0
    hZ1 hb2 hl1Z hl3Z hYZ
  refine hp.trans (ha.trans ?_)
  -- `η⁻¹ ≤ κ⁻¹ (1 - t)⁻¹`
  have h1t : 0 < 1 - t n := by linarith
  have hηlow : κ * (1 - t n) ≤ η := twEta_ge_holds κ ε 𝔠 𝔡 sz z hflow n (t n) ht1.le
  have hηinv : η⁻¹ ≤ κ⁻¹ * (1 - t n)⁻¹ := by
    rw [← mul_inv]
    exact inv_anti₀ (mul_pos hκ h1t) hηlow
  have hηinv2 : η⁻¹ ^ 2 ≤ (κ⁻¹ * (1 - t n)⁻¹) ^ 2 := pow_le_pow_left₀ (by positivity) hηinv 2
  have hB5 : (B ^ (5 / 2 : ℝ)) ^ 2 = B ^ 5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hB.le]
    norm_num
  have hZ0 : 0 ≤ TwistFold2_Z sz z t X n ω ^ 5 := pow_nonneg (le_trans zero_le_one hZ1) 5
  have hK0 : 0 ≤ (16 + 16 * c0⁻¹ ^ 2 + 8 * c0⁻¹) * Cρ ^ 2 := by positivity
  calc (16 + 16 * c0⁻¹ ^ 2 + 8 * c0⁻¹) * Cρ ^ 2 * η⁻¹ ^ 2 * B ^ 5 * TwistFold2_Z sz z t X n ω ^ 5
      ≤ (16 + 16 * c0⁻¹ ^ 2 + 8 * c0⁻¹) * Cρ ^ 2 * (κ⁻¹ * (1 - t n)⁻¹) ^ 2 * B ^ 5 * TwistFold2_Z sz z t X n ω ^ 5 := by
        gcongr
    _ = (16 + 16 * c0⁻¹ ^ 2 + 8 * c0⁻¹) * Cρ ^ 2 * κ⁻¹ ^ 2 *
        (((1 - t n)⁻¹ * B ^ (5 / 2 : ℝ)) ^ 2 * TwistFold2_Z sz z t X n ω ^ 5) := by
        rw [mul_pow κ⁻¹ (1 - t n)⁻¹ 2, mul_pow (1 - t n)⁻¹ (B ^ (5 / 2 : ℝ)) 2, hB5]; ring

end Row

/-! ## 8. A bounded random factor is `≺ W^d Bctl` -/

section OneFactor
variable {d : ℕ} {sz : Sizes d}

/-- A pathwise bounded factor, `‖X‖ ≤ 1`, is `≺ W^d Bctl`: `W^d Bctl ≥ c₀ = (𝔡⁻² + 1)⁻¹` eventually (target 6a), and `N^τ → ∞`. -/
theorem TwistFold2_one_prec (hsz : Tendsto sz.size atTop atTop) (μ : Measure sz.SeqΩ) (𝔡 : ℝ) (hWO : sz.WO 𝔡)
    (t : ℕ → ℝ) (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n ≤ 1)
    (X : ∀ n, Bool × Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) →
      Zd d (sz.L n) → sz.SeqΩ → ℂ)
    (hX : ∀ n p c₁ c₂ c₃ c₄ ω, ‖X n p c₁ c₂ c₃ c₄ ω‖ ≤ 1) :
    PrecL sz μ (U := fun n => (Bool × Zd d (sz.L n) × Zd d (sz.L n)) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n) ×
        Zd d (sz.L n))
      (fun n q ω => ‖X n q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 ω‖)
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ d * sz.Bctl n (t n)) := by
  have h6a := twB0_ge_holds sz 𝔡 hWO t ht0 ht1
  set c0 : ℝ := (𝔡⁻¹ ^ 2 + 1)⁻¹ with hc0def
  have hc0 : 0 < c0 := by positivity
  refine StochDomAt.of_eventually_empty fun τ hτ => ?_
  have hN : ∀ᶠ n in atTop, c0⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ τ :=
    ((tendsto_rpow_atTop hτ).comp (tendsto_natCast_atTop_iff.2 hsz)).eventually (eventually_ge_atTop c0⁻¹)
  filter_upwards [h6a, hN] with n h6n hNn
  ext ω
  simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
  intro q
  refine (hX n q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 ω).trans ?_
  calc (1 : ℝ) = c0⁻¹ * c0 := (inv_mul_cancel₀ hc0.ne').symm
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (((sz.W n : ℕ) : ℝ) ^ d * sz.Bctl n (t n)) :=
        mul_le_mul hNn h6n hc0.le (le_trans (inv_nonneg.2 hc0.le) hNn)

end OneFactor

/-! ## 9. Targets 7 and 7′: the `≺` row -/

/-- **Target 7** (the `≺` row, 0851 Q2 `:125`; Fable §5 "Pin instantiation"), frame of `BAExp14aS1` without its `U`-subtype:
from `STLocalEntrygL`, `STLmaxgL`, a deterministic weight `ρ` with `r₁, r₂ ≤ Cρ` (eventually, uniformly in `(σ, a, b)`) and a
random factor `X` with `‖X‖ ≺ W^d·Bctl` (#17, #47), pathwise over `(σ, a, b)`:
`‖Σ_c ρ(c) X(c) Tr(E_a Ǧ P_{c₁c₂} Ǧ P_{c₃c₄} Ǧ E_b Ǧ(σ))‖ ≺ (1 - t)⁻¹ (W^{-d} B_{t,0})^{5/2}` (the `[a]×[b]`-averaged node, Fable §1;
`σ` the tail charge, `Ǧ(σ)` by `twChg`, the closing edge circled as `BAExp14a_tailG`). -/
def twFold2Prec (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      STLocalEntrygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t → STLmaxgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t →
      ∀ (Cρ : ℝ) (ρ : ∀ n, Bool × Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) →
          Zd d (sz.L n) → ℂ),
        (∀ᶠ n in atTop, ∀ p, (∀ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ n p c₁ c₂ c₃ c₄‖ ≤ Cρ) ∧
          (∀ c₄, ∑ c₁, ∑ c₂, ∑ c₃, ‖ρ n p c₁ c₂ c₃ c₄‖ ≤ Cρ)) →
      ∀ X : ∀ n, Bool × Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) →
          sz.SeqΩ → ℂ,
        PrecL sz (Sizes.seqP (sz.withLam 0))
          (U := fun n => (Bool × Zd d (sz.L n) × Zd d (sz.L n)) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
          (fun n q ω => ‖X n q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 ω‖)
          (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ d * sz.Bctl n (t n)) →
        PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Bool × Zd d (sz.L n) × Zd d (sz.L n))
          (fun n p ω => ‖twLoop2X n ((baFMz sz z).GM n (t n) ω) ((baFMz sz z).GM n (t n) ω)
            (fun (u x : Idx d (sz.L n) (sz.W n)) => (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
              ∑ y ∈ twBlk n p.2.2, (baFMz sz z).GM n (t n) ω u y * twChg ((baFMz sz z).GM n (t n) ω) p.1 y x)
            (fun c₁ c₂ c₃ c₄ => ρ n p c₁ c₂ c₃ c₄ * X n p c₁ c₂ c₃ c₄ ω) p.2.1‖)
          (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))

/-- **Target 7′** (`twFold2PrecDet`): the deterministic weight, `X ≡ 1` (the twelve nodes other than #17, #47); from 7 and 6a. -/
def twFold2PrecDet (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      STLocalEntrygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t → STLmaxgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t →
      ∀ (Cρ : ℝ) (ρ : ∀ n, Bool × Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) →
          Zd d (sz.L n) → ℂ),
        (∀ᶠ n in atTop, ∀ p, (∀ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ n p c₁ c₂ c₃ c₄‖ ≤ Cρ) ∧
          (∀ c₄, ∑ c₁, ∑ c₂, ∑ c₃, ‖ρ n p c₁ c₂ c₃ c₄‖ ≤ Cρ)) →
      PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Bool × Zd d (sz.L n) × Zd d (sz.L n))
        (fun n p ω => ‖twLoop2X n ((baFMz sz z).GM n (t n) ω) ((baFMz sz z).GM n (t n) ω)
          (fun (u x : Idx d (sz.L n) (sz.W n)) => (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
            ∑ y ∈ twBlk n p.2.2, (baFMz sz z).GM n (t n) ω u y * twChg ((baFMz sz z).GM n (t n) ω) p.1 y x)
          (ρ n p) p.2.1‖)
        (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))

theorem twFold2Prec_holds (d : ℕ) : twFold2Prec d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT hE hLmax Cρ ρ hρ X hX
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hflow.1.2.2.1
  have ht1 : ∀ n, t n < 1 := fun n => (ba_G_data hκ sz hflow n (ht0 n) (htT n)).1
  have hBpos : ∀ n, 0 < sz.Bctl n (t n) := fun n => STBctl_pos sz n (ht1 n)
  have hu : ∀ n, 0 < ((sz.W n : ℕ) : ℝ) ^ d := fun n => TwistFold2_u_pos n
  have h6a := twB0_ge_holds sz 𝔡 hflow.1.2.2.2.2 t ht0 (fun n => (ht1 n).le)
  set c0 : ℝ := (𝔡⁻¹ ^ 2 + 1)⁻¹ with hc0def
  have hc0 : 0 < c0 := by positivity
  set μ : Measure sz.SeqΩ := Sizes.seqP (sz.withLam 0) with hμ
  -- the four random inputs are `≺ 1` after normalisation
  have domb : BAExp14a_Dom sz μ (fun n ω => BAExp14a_b sz z n (t n) ω) (fun n => sz.Bctl n (t n) ^ (1 / 2 : ℝ)) :=
    BAExp14a_Dom_b (κ := κ) (ε := ε) (𝔠 := 𝔠) (𝔡 := 𝔡) μ t ht1 hE
  have domb2 : BAExp14a_Dom sz μ (fun n ω => BAExp14a_b sz z n (t n) ω ^ 2 / sz.Bctl n (t n)) (fun _ => 1) := by
    refine TwistFold2_dom_div hBpos ?_
    have h1 := BAExp14a_Dom.mul hsz (fun n ω => BAExp14a_b_nonneg n (t n) ω)
      (fun n => Real.rpow_nonneg (hBpos n).le _) domb domb
    have h2 := BAExp14a_Dom.mono hsz (K := 1) one_pos (fun n => (hBpos n).le)
      (Eventually.of_forall fun n => by
        show sz.Bctl n (t n) ^ (1 / 2 : ℝ) * sz.Bctl n (t n) ^ (1 / 2 : ℝ) ≤ 1 * sz.Bctl n (t n)
        rw [one_mul, ← Real.rpow_add (hBpos n)]; norm_num) h1
    exact BAExp14a_Dom.of_le hsz (fun n ω => (sq _).le) h2
  have dom1 : BAExp14a_Dom sz μ (fun n ω => TwistFold2_lmax sz z t 1 n ω) (fun _ => 1) := by
    have h := TwistFold2_dom_lmax (μ := μ) (z := z) (t := t) (hLmax 1 le_rfl)
    exact BAExp14a_Dom.mono hsz (K := 1) one_pos (fun _ => zero_le_one) (Eventually.of_forall fun n => by simp) h
  have dom3 : BAExp14a_Dom sz μ (fun n ω => TwistFold2_lmax sz z t 3 n ω / sz.Bctl n (t n) ^ 2) (fun _ => 1) :=
    TwistFold2_dom_div (fun n => pow_pos (hBpos n) 2) (TwistFold2_dom_lmax (μ := μ) (z := z) (t := t) (hLmax 3 (by norm_num)))
  have domY : BAExp14a_Dom sz μ (fun n ω => TwistFold2_Xmax X n ω / (((sz.W n : ℕ) : ℝ) ^ d * sz.Bctl n (t n)))
      (fun _ => 1) :=
    TwistFold2_dom_div (fun n => mul_pos (hu n) (hBpos n)) (TwistFold2_dom_Xmax hX)
  have domZ : BAExp14a_Dom sz μ (fun n ω => TwistFold2_Z sz z t X n ω) (fun _ => 1) := by
    have h1 : BAExp14a_Dom sz μ (fun _ _ => (1 : ℝ)) (fun _ => 1) := BAExp14a_Dom.refl hsz (fun _ => zero_le_one)
    have h := BAExp14a_Dom.add hsz (BAExp14a_Dom.add hsz (BAExp14a_Dom.add hsz (BAExp14a_Dom.add hsz h1 domb2) dom1) dom3) domY
    exact BAExp14a_Dom.mono hsz (K := 5) (by norm_num) (fun _ => zero_le_one) (Eventually.of_forall fun n => by norm_num) h
  have hZ0 : ∀ n ω, 0 ≤ TwistFold2_Z sz z t X n ω := fun n ω =>
    le_trans zero_le_one (TwistFold2_Z_facts _ _ _ _ _ _ (hu n) (hBpos n) (BAExp14a_b_nonneg n (t n) ω)
      (TwistFold2_lmax_nonneg z t 1 n ω) (TwistFold2_lmax_nonneg z t 3 n ω) (TwistFold2_Xmax_nonneg X n ω)).1
  have domZ5 := TwistFold2_dom_pow hsz hZ0 domZ 5
  set R : ℕ → ℝ := fun n => (1 - t n)⁻¹ * sz.Bctl n (t n) ^ (5 / 2 : ℝ) with hR
  have hR0 : ∀ n, 0 ≤ R n := fun n =>
    mul_nonneg (inv_nonneg.2 (by linarith [ht1 n])) (Real.rpow_nonneg (hBpos n).le _)
  set Kc : ℝ := (16 + 16 * c0⁻¹ ^ 2 + 8 * c0⁻¹) * Cρ ^ 2 * κ⁻¹ ^ 2 with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  have domR := BAExp14a_Dom.mul hsz (fun n ω => pow_nonneg (hZ0 n ω) 5) (fun n => sq_nonneg (R n))
    (BAExp14a_Dom.refl hsz (fun n => sq_nonneg (R n))) domZ5
  have domK := BAExp14a_Dom.const_mul hsz hKc0 (fun n => by positivity) domR
  have hpr := BAExp14a_Dom.index hsz (V := fun n => Bool × Zd d (sz.L n) × Zd d (sz.L n)) domK
  refine TwistFold2_prec_sqrt (fun n p ω => norm_nonneg _) (fun n p ω => hR0 n) ?_
  refine BAExp14a_prec_congr (fun _ _ _ => rfl) (fun _ _ _ => mul_one _) (BAExp14a_prec_of_le_ev ?_ hpr)
  filter_upwards [hρ, h6a] with n hρn h6n
  intro p ω
  have hCρ : 0 ≤ Cρ := (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    norm_nonneg _).trans ((hρn (true, 0, 0)).1 0)
  exact TwistFold2_row hκ hflow t ht0 htT n ω c0 Cρ hc0 h6n hCρ (ρ n) hρn X p

theorem twFold2PrecDet_holds (d : ℕ) : twFold2PrecDet d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT hE hLmax Cρ ρ hρ
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hflow.1.2.2.1
  have ht1 : ∀ n, t n < 1 := fun n => (ba_G_data hκ sz hflow n (ht0 n) (htT n)).1
  -- the constant random factor `X ≡ 1` is `≺ W^d Bctl` (S3A-C2)
  have hX1 := TwistFold2_one_prec hsz (Sizes.seqP (sz.withLam 0)) 𝔡 hflow.1.2.2.2.2 t ht0 (fun n => (ht1 n).le)
    (fun n _ _ _ _ _ _ => (1 : ℂ)) (fun n p c₁ c₂ c₃ c₄ ω => by simp)
  have h := twFold2Prec_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT hE hLmax Cρ ρ hρ
    (fun n _ _ _ _ _ _ => 1) hX1
  simpa only [mul_one] using h

/-! ## 10. Compiled nonempty instances of targets 7 and 7′ (`d = 3`, `sz0`, `zSeq`, `t ≡ 1/2`) -/

section Inst
open RBM.Gauss.SizesInst RBM.BA.FlowPinsInst

/-- The weight of root term #2 of `T3C-tr_0` at `t ≡ 1/2`: `ρ₀(c) = t² 1[c₃ = c₁ ∧ c₄ = c₂] (M^{(B)}_{c₁c₂})²` (Fable §1, §5). -/
def TwistFold2_rho2 (n : ℕ) :
    Bool × Zd 3 (sz0.L n) × Zd 3 (sz0.L n) → Zd 3 (sz0.L n) → Zd 3 (sz0.L n) → Zd 3 (sz0.L n) → Zd 3 (sz0.L n) → ℂ :=
  fun _ c₁ c₂ c₃ c₄ => if c₃ = c₁ ∧ c₄ = c₂ then (1 / 2 : ℂ) ^ 2 * twMB (baFMz sz0 zSeq) n c₁ c₂ ^ 2 else 0

/-- `r₁ = r₂ = 1/4` for `ρ₀`, from the `M`-Ward identity `Σ_b |M^{(B)}_{ab}|² = 1` and the symmetry of `M^{(B)}`. -/
theorem TwistFold2_rho2_bounds (n : ℕ) (p : Bool × Zd 3 (sz0.L n) × Zd 3 (sz0.L n)) :
    (∀ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖TwistFold2_rho2 n p c₁ c₂ c₃ c₄‖ ≤ 1 / 4) ∧
      (∀ c₄, ∑ c₁, ∑ c₂, ∑ c₃, ‖TwistFold2_rho2 n p c₁ c₂ c₃ c₄‖ ≤ 1 / 4) := by
  have hr := BAflow_real _ _ _ _ sz0 zSeq flow_sz0 n
  have hmB := twMB_ba (sz := sz0) zSeq n hr.1.1
  have hrow : ∀ a : Zd 3 (sz0.L n), ∑ b, ‖twMB (baFMz sz0 zSeq) n a b‖ ^ 2 = 1 := by
    intro a; rw [hmB]
    exact BAMB_row_sq_real 3 (sz0.L n) _ _ _ hr.1 a
  have hcol : ∀ b : Zd 3 (sz0.L n), ∑ a, ‖twMB (baFMz sz0 zSeq) n a b‖ ^ 2 = 1 := by
    intro b; rw [← hrow b]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hmB, BAMB_symm]
  have hnorm : ∀ c₁ c₂ : Zd 3 (sz0.L n), ‖(1 / 2 : ℂ) ^ 2 * twMB (baFMz sz0 zSeq) n c₁ c₂ ^ 2‖ =
      1 / 4 * ‖twMB (baFMz sz0 zSeq) n c₁ c₂‖ ^ 2 := by
    intro c₁ c₂; rw [norm_mul, norm_pow, norm_pow]; norm_num
  refine ⟨fun c₁ => ?_, fun c₄ => ?_⟩
  · unfold TwistFold2_rho2
    simp only [ite_and, apply_ite (fun z : ℂ => ‖z‖), norm_zero, hnorm]
    simp [Finset.sum_ite_eq', ← Finset.mul_sum, hrow c₁]
  · unfold TwistFold2_rho2
    simp only [ite_and, apply_ite (fun z : ℂ => ‖z‖), norm_zero, hnorm]
    simp [Finset.sum_ite_eq', ← Finset.mul_sum, hcol c₄]

-- Target 7′ (`twFold2PrecDet`) at `d = 3`, `sz0`, `zSeq`, `t ≡ 1/2` for the root-#2 weight `ρ₀`; the two stochastic premises
-- `STLocalEntrygL`, `STLmaxgL` stay hypotheses, every deterministic hypothesis is discharged (`r₁, r₂ = 1/4` by the `M`-Ward identity)
example (hE : STLocalEntrygL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2))
    (hL : STLmaxgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2)) :
    PrecL sz0 (Sizes.seqP (sz0.withLam 0)) (U := fun n => Bool × Zd 3 (sz0.L n) × Zd 3 (sz0.L n))
      (fun n p ω => ‖twLoop2X n ((baFMz sz0 zSeq).GM n (1 / 2) ω) ((baFMz sz0 zSeq).GM n (1 / 2) ω)
        (fun (u x : Idx 3 (sz0.L n) (sz0.W n)) => (((sz0.W n : ℕ) : ℂ) ^ 3)⁻¹ *
          ∑ y ∈ twBlk n p.2.2, (baFMz sz0 zSeq).GM n (1 / 2) ω u y * twChg ((baFMz sz0 zSeq).GM n (1 / 2) ω) p.1 y x)
        (fun c₁ c₂ c₃ c₄ => if c₃ = c₁ ∧ c₄ = c₂ then (1 / 2 : ℂ) ^ 2 * twMB (baFMz sz0 zSeq) n c₁ c₂ ^ 2 else 0) p.2.1‖)
      (fun n _ _ => (1 - (1 / 2 : ℝ))⁻¹ * (sz0.Bctl n (1 / 2)) ^ (5 / 2 : ℝ)) :=
  twFold2PrecDet_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq
    flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) hE hL (1 / 4) TwistFold2_rho2
    (Eventually.of_forall fun n p => TwistFold2_rho2_bounds n p)

-- Target 7 (`twFold2Prec`) at the same data with the random factor `X ≡ 1` (`‖1‖ ≺ W^d Bctl` by `TwistFold2_one_prec`, target 6a)
example (hE : STLocalEntrygL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2))
    (hL : STLmaxgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2)) :
    PrecL sz0 (Sizes.seqP (sz0.withLam 0)) (U := fun n => Bool × Zd 3 (sz0.L n) × Zd 3 (sz0.L n))
      (fun n p ω => ‖twLoop2X n ((baFMz sz0 zSeq).GM n (1 / 2) ω) ((baFMz sz0 zSeq).GM n (1 / 2) ω)
        (fun (u x : Idx 3 (sz0.L n) (sz0.W n)) => (((sz0.W n : ℕ) : ℂ) ^ 3)⁻¹ *
          ∑ y ∈ twBlk n p.2.2, (baFMz sz0 zSeq).GM n (1 / 2) ω u y * twChg ((baFMz sz0 zSeq).GM n (1 / 2) ω) p.1 y x)
        (fun c₁ c₂ c₃ c₄ => TwistFold2_rho2 n p c₁ c₂ c₃ c₄ * (fun (_ : ℕ) (_ : Bool × Zd 3 (sz0.L n) × Zd 3 (sz0.L n))
          (_ _ _ _ : Zd 3 (sz0.L n)) (_ : sz0.SeqΩ) => (1 : ℂ)) n p c₁ c₂ c₃ c₄ ω) p.2.1‖)
      (fun n _ _ => (1 - (1 / 2 : ℝ))⁻¹ * (sz0.Bctl n (1 / 2)) ^ (5 / 2 : ℝ)) :=
  twFold2Prec_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq
    flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) hE hL (1 / 4) TwistFold2_rho2
    (Eventually.of_forall fun n p => TwistFold2_rho2_bounds n p) (fun n _ _ _ _ _ _ => 1)
    (TwistFold2_one_prec (Sizes.tendsto_size sz0 sz0_tendsto) _ (1 / 10) flow_sz0.1.2.2.2.2 (fun _ => 1 / 2)
      (fun _ => by norm_num) (fun _ => by norm_num) _ (fun _ _ _ _ _ _ _ => (norm_one (α := ℂ)).le))

end Inst

end RBM.BA

end
