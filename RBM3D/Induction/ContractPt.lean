/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step2Defs
import RBM3D.Induction.ConArgDet

/-!
# ST2-08 (ticket T2094): the pointwise contraction inequality `STContractPt`

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`), Lemma `ygdhmsgq0`
(`3_5:751-797`): `(eq_sym_loop_bound)` `3_5:754`, the quadratic form `(eq_6loop_quadform)`
`3_5:776`, `(eq:L4loop)` `3_5:780`, `(eq_sym_loop_bound_old)` `3_5:788`, the neighbour count and
Ward's identity `3_5:791-795`.  New at `d ≥ 3`: no
RBM2D source (the technique is that of `RBM3D/Induction/Contract.lean`, `stContract_holds`,
`3_5:918-1000`, whose helper lemmas are private there and are re-proved here in the form needed).

The proof is deterministic: a Hermitian `H` on the fine lattice, `Im z = η > 0`, `E_a = W^{-d} P_a`
with `P_a` the diagonal projection onto the block `a`.  With `G₁ = G(σ₁)`, `G₂ = G(σ₂)`,
`Ḡ_i = G(-σ_i) = G_i^*` and
`Ψ_c = P_c G₁ P_a G₂ P_b`, `A_{c'} = P_b G₁ P_{c'} Ḡ₁ P_b`:

* `𝓛^{(6)}_{(σ⊗σ̄)^{(1)},(a,b,c',b,a,c)} = W^{-6d} tr(Ψ_c A_{c'} Ψ_c^*)`;
* `|tr(Ψ A Ψ^*)| ≤ ‖A‖_HS ‖Ψ‖²_HS` (Cauchy-Schwarz on the pair of indices of `A`);
* `A_{c'}` is Hermitian and `𝓛^{(4)}_{alt,(c',b,c',b)} = W^{-4d} tr(A_{c'}²)
  = W^{-4d} ‖A_{c'}‖²_HS`;
* `Σ_c ‖Ψ_c‖²_HS = tr(G₁ P_a G₂ P_b Ḡ₂ P_a Ḡ₁)` (`Σ_c P_c = 1`), and Ward's identity
  `Ḡ₁ G₁ = (2 i η)⁻¹ (G(+) - G(-))` turns it into
  `W^{3d} (2 i η)⁻¹ (𝓛^{(3)}_{(+,σ₂,-σ₂),(a,b,a)} - 𝓛^{(3)}_{(-,σ₂,-σ₂),(a,b,a)})`
  for both signs of `σ₁` (`3_5:795`; the identity `G(-σ) G(σ) = (2 i η)⁻¹ (G(+) - G(-))` holds
  for either `σ`, so the case `σ₁ = -` needs no separate treatment);
* each `c` has at most `3^d` neighbours `c'` (`zdist L u ≤ 1 ⇔ u.val ∈ {0, 1, L - 1}`).

Constants are exact: `3^d / (W^d η)`, no loss; `3 ≤ d`, `3 ≤ L` are not used.
* §1 the Hilbert-Schmidt norm `hs` and `|tr(Ψ A Ψ^*)| ≤ √(hs A) hs Ψ`;
* §2 the adjoint `G(σ)^* = G(-σ)` and Ward's identity;
* §3 block projections `Pm`;
* §4 the matrix identities: the six-loop, the alternating four-loop, the sum over `c`;
* §5 the neighbour count and the pin `stContractPt_holds`; §6 compiled instances at `d = 3`.
-/

noncomputable section

open Matrix Finset

namespace RBM.Gauss.Sizes

open RBM.Gauss

/-! ## 1. Hilbert-Schmidt Cauchy-Schwarz -/

section Generic

variable {ι : Type*} [Fintype ι]

/-- `‖A‖_{HS}² = Σ_{ij} |A_{ij}|²`.  `RBM3D/Induction/Contract.lean:52` (private there). -/
private def hs (A : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

private lemma hs_nonneg (A : Matrix ι ι ℂ) : 0 ≤ hs A := by
  unfold hs; positivity

/-- `tr(A A^*) = ‖A‖_HS²`.  `RBM3D/Induction/Contract.lean:57` (private there). -/
private lemma trace_mul_conjTranspose_eq (A : Matrix ι ι ℂ) :
    (A * Aᴴ).trace = (hs A : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, hs]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj']

/-- Cauchy-Schwarz over the pair of indices:
`Σ_{ij} |A_{ij}| v_i v_j ≤ ‖A‖_HS Σ_i v_i²`. -/
private lemma sum_pair_le (A : Matrix ι ι ℂ) (v : ι → ℝ) :
    ∑ i, ∑ j, ‖A i j‖ * (v i * v j) ≤ √(hs A) * ∑ i, v i ^ 2 := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (ι × ι))
    (fun p => ‖A p.1 p.2‖) (fun p => v p.1 * v p.2)
  simp only [Fintype.sum_prod_type] at h
  have h2 : ∑ i, ∑ j, (v i * v j) ^ 2 = (∑ i, v i ^ 2) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h2, Real.sqrt_sq (Finset.sum_nonneg fun i _ => sq_nonneg (v i))] at h
  exact h

/-- **The quadratic-form Cauchy-Schwarz bound** `|tr(Ψ A Ψ^*)| ≤ ‖A‖_HS ‖Ψ‖²_HS`
(`(eq_6loop_quadform)`, `3_5:776`, with `‖A‖_op ≤ ‖A‖_HS`, `3_5:779`). -/
private lemma norm_trace_mul_mul_conjTranspose_le (Ψ A : Matrix ι ι ℂ) :
    ‖(Ψ * A * Ψᴴ).trace‖ ≤ √(hs A) * hs Ψ := by
  have h1 : ‖(Ψ * A * Ψᴴ).trace‖ ≤
      ∑ x, ∑ i, ∑ j, ‖A i j‖ * (‖Ψ x i‖ * ‖Ψ x j‖) := by
    calc ‖(Ψ * A * Ψᴴ).trace‖
        = ‖∑ x, ∑ j, (∑ i, Ψ x i * A i j) * star (Ψ x j)‖ := by
          simp [Matrix.trace, Matrix.mul_apply]
      _ ≤ ∑ x, ‖∑ j, (∑ i, Ψ x i * A i j) * star (Ψ x j)‖ := norm_sum_le _ _
      _ ≤ ∑ x, ∑ j, ‖(∑ i, Ψ x i * A i j) * star (Ψ x j)‖ :=
          Finset.sum_le_sum fun x _ => norm_sum_le _ _
      _ ≤ ∑ x, ∑ j, ∑ i, ‖Ψ x i * A i j * star (Ψ x j)‖ := by
          refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul, norm_star]
          calc ‖∑ i, Ψ x i * A i j‖ * ‖Ψ x j‖ ≤ (∑ i, ‖Ψ x i * A i j‖) * ‖Ψ x j‖ :=
                mul_le_mul_of_nonneg_right (norm_sum_le _ _) (norm_nonneg _)
            _ = ∑ i, ‖Ψ x i * A i j‖ * ‖Ψ x j‖ := Finset.sum_mul _ _ _
            _ = _ := by simp
      _ = ∑ x, ∑ i, ∑ j, ‖A i j‖ * (‖Ψ x i‖ * ‖Ψ x j‖) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [norm_mul, norm_mul, norm_star]
          ring
  refine h1.trans ?_
  calc ∑ x, ∑ i, ∑ j, ‖A i j‖ * (‖Ψ x i‖ * ‖Ψ x j‖)
      ≤ ∑ x, √(hs A) * ∑ i, ‖Ψ x i‖ ^ 2 :=
        Finset.sum_le_sum fun x _ => sum_pair_le A (fun i => ‖Ψ x i‖)
    _ = √(hs A) * hs Ψ := by rw [← Finset.mul_sum]; rfl

end Generic

/-! ## 2. The resolvent: adjoint and Ward's identity -/

section Resolvent

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `G(σ)^* = G(-σ)` for Hermitian `H`.  `RBM3D/Induction/Contract.lean:224` (private there). -/
private lemma Gres_conjTranspose {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (z : ℂ) (σ : Bool) :
    (Gres H z σ)ᴴ = Gres H z (!σ) := by
  have hH' : Hᴴ = H := hH
  cases σ with
  | true =>
    simp only [Gres, ↓reduceIte, Bool.not_true, Bool.false_eq_true,
      ← Matrix.nonsing_inv_eq_ringInverse, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH',
      Complex.star_def]
  | false =>
    simp only [Gres, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      ← Matrix.nonsing_inv_eq_ringInverse, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH',
      Complex.star_def, Complex.conj_conj]

/-- `G(+) - G(-) = (z - z̄) G(+) G(-) = (z - z̄) G(-) G(+)` (`(eq_Ward0)`, `1_2:1018`; `Im z ≠ 0`).
`RBM3D/Induction/Contract.lean:237` (private there). -/
private lemma Gres_sub {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    Gres H z true - Gres H z false = (z - (starRingEnd ℂ) z) • (Gres H z true * Gres H z false) ∧
    Gres H z true - Gres H z false =
      (z - (starRingEnd ℂ) z) • (Gres H z false * Gres H z true) := by
  have hA : IsUnit (H - z • (1 : Matrix ι ι ℂ)) := isUnit_sub_smul_of_isHermitian hH hz
  have hB : IsUnit (H - (starRingEnd ℂ) z • (1 : Matrix ι ι ℂ)) :=
    isUnit_sub_smul_of_isHermitian hH (by simpa using hz)
  have hAd : IsUnit (H - z • (1 : Matrix ι ι ℂ)).det := (Matrix.isUnit_iff_isUnit_det _).mp hA
  have hBd : IsUnit (H - (starRingEnd ℂ) z • (1 : Matrix ι ι ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hB
  simp only [Gres, ↓reduceIte, Bool.false_eq_true, ← Matrix.nonsing_inv_eq_ringInverse]
  set A : Matrix ι ι ℂ := H - z • (1 : Matrix ι ι ℂ) with hAdef
  set B : Matrix ι ι ℂ := H - (starRingEnd ℂ) z • (1 : Matrix ι ι ℂ) with hBdef
  have hBA : B - A = (z - (starRingEnd ℂ) z) • (1 : Matrix ι ι ℂ) := by
    rw [hAdef, hBdef, sub_sub_sub_cancel_left, ← sub_smul]
  have hAinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hAd
  have hAinv' : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hAd
  have hBinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hBd
  have hBinv' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hBd
  constructor
  · have : A⁻¹ * (B - A) * B⁻¹ = A⁻¹ - B⁻¹ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hBinv', Matrix.mul_one,
        hAinv, Matrix.one_mul]
    rw [← this, hBA]
    simp
  · have : B⁻¹ * (B - A) * A⁻¹ = A⁻¹ - B⁻¹ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hBinv, Matrix.one_mul, Matrix.mul_assoc, hAinv',
        Matrix.mul_one]
    rw [← this, hBA]
    simp

/-- `z - z̄ = 2 i Im z`. -/
private lemma sub_conj_eq (z : ℂ) : z - (starRingEnd ℂ) z = 2 * Complex.I * (z.im : ℂ) := by
  rw [Complex.sub_conj]; push_cast; ring

/-- **Ward's identity** `G(-σ) G(σ) = (2 i η)⁻¹ (G(+) - G(-))` for either charge `σ`
(`(eq_Ward0)`, `1_2:1018`, behind `(WI_calL)`, `1_2:1036`; used at `3_5:795`).
`RBM3D/Induction/Contract.lean:276` (private there). -/
private lemma Gres_ward_left {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (σ : Bool) :
    Gres H z (!σ) * Gres H z σ =
      (2 * Complex.I * (z.im : ℂ))⁻¹ • (Gres H z true - Gres H z false) := by
  have hk : (2 * Complex.I * (z.im : ℂ)) ≠ 0 := by
    have : (z.im : ℂ) ≠ 0 := by exact_mod_cast hz
    simp [this]
  obtain ⟨h1, h2⟩ := Gres_sub hH hz
  rw [sub_conj_eq] at h1 h2
  cases σ with
  | true =>
    simp only [Bool.not_true]
    rw [h2, smul_smul, inv_mul_cancel₀ hk, one_smul]
  | false =>
    simp only [Bool.not_false]
    rw [h1, smul_smul, inv_mul_cancel₀ hk, one_smul]

end Resolvent

/-! ## 3. The block projections `P_a = W^d E_a` -/

section Proj

variable (d L W : ℕ) [NeZero L]

/-- The block projection `P_a = W^d E_a`: the diagonal matrix of the indicator of the block `a`.
`RBM3D/Induction/Contract.lean:706` (private there). -/
private def Pm (a : Zd d L) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  Matrix.diagonal fun x => if x.1 = a then 1 else 0

variable {d L W}

omit [NeZero L] in
/-- `RBM3D/Induction/Contract.lean:711`. -/
private lemma Eblk_eq_smul_Pm (a : Zd d L) :
    Eblk d L W a = ((W : ℂ) ^ d)⁻¹ • Pm d L W a := by
  ext x y
  by_cases hxy : x = y
  · subst hxy
    by_cases hx : x.1 = a <;> simp [Eblk, Pm, hx]
  · simp [Eblk, Pm, hxy]

omit [NeZero L] in
/-- `RBM3D/Induction/Contract.lean:724`. -/
private lemma Pm_conjTranspose (a : Zd d L) : (Pm d L W a)ᴴ = Pm d L W a := by
  refine (Matrix.isHermitian_diagonal_iff.mpr fun x => ?_).eq
  by_cases h : x.1 = a <;> simp [h, IsSelfAdjoint]

/-- `RBM3D/Induction/Contract.lean:728`. -/
private lemma Pm_mul_self (a : Zd d L) : Pm d L W a * Pm d L W a = Pm d L W a := by
  simp only [Pm, Matrix.diagonal_mul_diagonal]
  congr 1
  ext x
  by_cases h : x.1 = a <;> simp [h]

private lemma Pm_mul_Pm_mul (a : Zd d L) (X : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    Pm d L W a * (Pm d L W a * X) = Pm d L W a * X := by
  rw [← Matrix.mul_assoc, Pm_mul_self]

/-- `RBM3D/Induction/Contract.lean:734`. -/
private lemma sum_Pm : ∑ a : Zd d L, Pm d L W a = 1 := by
  ext x y
  simp only [Pm, Matrix.sum_apply, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy
    simp
  · simp [hxy]

end Proj

/-! ## 4. Matrix identities -/

section Core

variable {d L W : ℕ} [NeZero L]
variable (G : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ)

/-- `Ψ_c = P_c G(σ₁) P_a G(σ₂) P_b` (the matrix of the vectors `ψ^z`, `z ∈ [c]`, of
`3_5:764-773`). -/
private def Psi (s0 s1 : Bool) (a b c : Zd d L) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  Pm d L W c * G s0 * Pm d L W a * G s1 * Pm d L W b

/-- `A_{c'} = P_b G(σ₁) P_{c'} G(-σ₁) P_b` (`A^{(c')}` of `3_5:764-773`). -/
private def Amat (s0 : Bool) (b c' : Zd d L) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  Pm d L W b * G s0 * Pm d L W c' * G (!s0) * Pm d L W b

/-- `(G₁ P_a G₂ P_b Ḡ₂ P_a Ḡ₁)`: the matrix whose trace is `Σ_c ‖Ψ_c‖²_HS`. -/
private def Kmat (s0 s1 : Bool) (a b : Zd d L) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  G s0 * Pm d L W a * G s1 * Pm d L W b * G (!s1) * Pm d L W a * G (!s0)

variable {G}

private lemma trace_Pm_sandwich (c : Zd d L) (X : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    (Pm d L W c * X * Pm d L W c).trace = (X * Pm d L W c).trace := by
  rw [Matrix.trace_mul_comm, Pm_mul_Pm_mul, Matrix.trace_mul_comm]

private lemma Psi_conjTranspose (hG : ∀ s, (G s)ᴴ = G (!s)) (s0 s1 : Bool) (a b c : Zd d L) :
    (Psi G s0 s1 a b c : Matrix (Vtx d L W) (Vtx d L W) ℂ)ᴴ =
      Pm d L W b * G (!s1) * Pm d L W a * G (!s0) * Pm d L W c := by
  simp only [Psi, Matrix.conjTranspose_mul, Pm_conjTranspose, hG, Matrix.mul_assoc]

private lemma Amat_conjTranspose (hG : ∀ s, (G s)ᴴ = G (!s)) (s0 : Bool) (b c' : Zd d L) :
    (Amat G s0 b c' : Matrix (Vtx d L W) (Vtx d L W) ℂ)ᴴ = Amat G s0 b c' := by
  simp only [Amat, Matrix.conjTranspose_mul, Pm_conjTranspose, hG, Bool.not_not, Matrix.mul_assoc]

/-- `Ψ_c A_{c'} Ψ_c^* = P_c (G₁ P_a G₂ P_b G₁ P_{c'} Ḡ₁ P_b Ḡ₂ P_a Ḡ₁) P_c`, from
`P_b P_b = P_b`. -/
private lemma Psi_mul_Amat_mul_conj (hG : ∀ s, (G s)ᴴ = G (!s)) (s0 s1 : Bool)
    (a b c c' : Zd d L) :
    Psi G s0 s1 a b c * Amat G s0 b c' * (Psi G s0 s1 a b c)ᴴ =
      Pm d L W c * (G s0 * Pm d L W a * G s1 * Pm d L W b * G s0 * Pm d L W c' * G (!s0) *
        Pm d L W b * G (!s1) * Pm d L W a * G (!s0)) * Pm d L W c := by
  rw [Psi_conjTranspose hG]
  simp only [Psi, Amat, Matrix.mul_assoc, Pm_mul_Pm_mul]

/-- `A_{c'} A_{c'} = P_b (G₁ P_{c'} Ḡ₁ P_b G₁ P_{c'} Ḡ₁) P_b`. -/
private lemma Amat_mul_Amat (s0 : Bool) (b c' : Zd d L) :
    Amat G s0 b c' * Amat G s0 b c' =
      Pm d L W b * (G s0 * Pm d L W c' * G (!s0) * Pm d L W b * G s0 * Pm d L W c' *
        G (!s0)) * Pm d L W b := by
  simp only [Amat, Matrix.mul_assoc, Pm_mul_Pm_mul]

/-- `Ψ_c Ψ_c^* = P_c K P_c`. -/
private lemma Psi_mul_conj (hG : ∀ s, (G s)ᴴ = G (!s)) (s0 s1 : Bool) (a b c : Zd d L) :
    Psi G s0 s1 a b c * (Psi G s0 s1 a b c)ᴴ = Pm d L W c * Kmat G s0 s1 a b * Pm d L W c := by
  rw [Psi_conjTranspose hG]
  simp only [Psi, Kmat, Matrix.mul_assoc, Pm_mul_Pm_mul]

/-- `‖A_{c'}‖²_HS = tr(A_{c'}²)`: `A_{c'}` is Hermitian. -/
private lemma hs_Amat (hG : ∀ s, (G s)ᴴ = G (!s)) (s0 : Bool) (b c' : Zd d L) :
    (hs (Amat G s0 b c' : Matrix (Vtx d L W) (Vtx d L W) ℂ) : ℂ) =
      (Amat G s0 b c' * Amat G s0 b c').trace := by
  rw [← trace_mul_conjTranspose_eq, Amat_conjTranspose hG]

/-- `‖Ψ_c‖²_HS = tr(K P_c)`. -/
private lemma hs_Psi (hG : ∀ s, (G s)ᴴ = G (!s)) (s0 s1 : Bool) (a b c : Zd d L) :
    (hs (Psi G s0 s1 a b c : Matrix (Vtx d L W) (Vtx d L W) ℂ) : ℂ) =
      (Kmat G s0 s1 a b * Pm d L W c).trace := by
  rw [← trace_mul_conjTranspose_eq, Psi_mul_conj hG, trace_Pm_sandwich]

/-- `Σ_c ‖Ψ_c‖²_HS = tr K` (`Σ_c P_c = 1`). -/
private lemma sum_hs_Psi (hG : ∀ s, (G s)ᴴ = G (!s)) (s0 s1 : Bool) (a b : Zd d L) :
    ∑ c : Zd d L, (hs (Psi G s0 s1 a b c : Matrix (Vtx d L W) (Vtx d L W) ℂ) : ℂ) =
      (Kmat G s0 s1 a b : Matrix (Vtx d L W) (Vtx d L W) ℂ).trace := by
  simp only [hs_Psi hG]
  rw [← Matrix.trace_sum, ← Finset.mul_sum, sum_Pm, Matrix.mul_one]


/-- Ward's identity for the sum over `c`: `tr K = (2iη)⁻¹ (tr(G(+) Y) - tr(G(-) Y))` with
`Y = P_a G₂ P_b Ḡ₂ P_a`, given `Ḡ₁ G₁ = (2iη)⁻¹ (G(+) - G(-))`. -/
private lemma trace_Kmat {s0 : Bool} (s1 : Bool) (a b : Zd d L) {c : ℂ}
    (hW : G (!s0) * G s0 = c • (G true - G false)) :
    (Kmat G s0 s1 a b : Matrix (Vtx d L W) (Vtx d L W) ℂ).trace =
      c * ((G true * (Pm d L W a * G s1 * Pm d L W b * G (!s1) * Pm d L W a)).trace -
        (G false * (Pm d L W a * G s1 * Pm d L W b * G (!s1) * Pm d L W a)).trace) := by
  have h : (Kmat G s0 s1 a b : Matrix (Vtx d L W) (Vtx d L W) ℂ) =
      (G s0 * (Pm d L W a * G s1 * Pm d L W b * G (!s1) * Pm d L W a)) * G (!s0) := by
    simp only [Kmat, Matrix.mul_assoc]
  rw [h, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hW, Matrix.smul_mul, Matrix.trace_smul,
    Matrix.sub_mul, Matrix.trace_sub, smul_eq_mul]

end Core

/-! ### The loops as traces of `P`-words -/

section LoopTraces

variable {d L W : ℕ} [NeZero L] [NeZero W] (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ)

/-- The six-loop of the pin: `𝓛^{(6)} = W^{-6d} tr(Ψ_c A_{c'} Ψ_c^*)`. -/
private lemma loop6_eq
    (hG : ∀ s, (Gres (blockMat d L W H) z s)ᴴ = Gres (blockMat d L W H) z (!s))
    (s0 s1 : Bool) (a b c c' : Zd d L) :
    loopFine d L W H z ![s0, s1, s0, !s0, !s1, !s0] ![a, b, c', b, a, c] =
      (((W : ℂ) ^ d)⁻¹) ^ 6 *
        (Psi (Gres (blockMat d L W H) z) s0 s1 a b c * Amat (Gres (blockMat d L W H) z) s0 b c' *
          (Psi (Gres (blockMat d L W H) z) s0 s1 a b c)ᴴ).trace := by
  rw [Psi_mul_Amat_mul_conj hG, trace_Pm_sandwich]
  conv_lhs => simp [loopFine, loopM, List.ofFn_succ]
  simp only [Eblk_eq_smul_Pm, Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.trace_smul,
    smul_eq_mul, Matrix.mul_assoc]
  ring

/-- The alternating four-loop of the pin: `𝓛^{(4)}_{alt} = W^{-4d} tr(A_{c'}²)` (`(eq:L4loop)`,
`3_5:780`). -/
private lemma loop4_eq (s0 : Bool) (b c' : Zd d L) :
    loopFine d L W H z ![s0, !s0, s0, !s0] ![c', b, c', b] =
      (((W : ℂ) ^ d)⁻¹) ^ 4 *
        (Amat (Gres (blockMat d L W H) z) s0 b c' *
          Amat (Gres (blockMat d L W H) z) s0 b c').trace := by
  rw [Amat_mul_Amat, trace_Pm_sandwich]
  conv_lhs => simp [loopFine, loopM, List.ofFn_succ]
  simp only [Eblk_eq_smul_Pm, Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.trace_smul,
    smul_eq_mul, Matrix.mul_assoc]
  ring

/-- The three-loop of the pin: `𝓛^{(3)}_{(s,σ₂,-σ₂),(a,b,a)} = W^{-3d} tr(G(s) Y)`,
`Y = P_a G₂ P_b Ḡ₂ P_a`. -/
private lemma loop3_eq (s s1 : Bool) (a b : Zd d L) :
    loopFine d L W H z ![s, s1, !s1] ![a, b, a] =
      (((W : ℂ) ^ d)⁻¹) ^ 3 *
        (Gres (blockMat d L W H) z s * (Pm d L W a * Gres (blockMat d L W H) z s1 * Pm d L W b *
          Gres (blockMat d L W H) z (!s1) * Pm d L W a)).trace := by
  conv_lhs => simp [loopFine, loopM, List.ofFn_succ]
  simp only [Eblk_eq_smul_Pm, Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.trace_smul,
    smul_eq_mul, Matrix.mul_assoc]
  ring

end LoopTraces

/-! ## 5. The neighbour count and the pin -/

section Neighbours

/-- `zdist L x ≤ 1` forces `x ∈ {0, 1, -1}`. -/
private lemma zdist_le_one {L : ℕ} [NeZero L] {x : ZMod L} (h : zdist L x ≤ 1) :
    x = 0 ∨ x = 1 ∨ x = -1 := by
  have hx : x.val < L := ZMod.val_lt x
  have hx' : (x.val : ZMod L) = x := ZMod.natCast_zmod_val x
  unfold zdist at h
  rcases (by omega : x.val = 0 ∨ x.val = 1 ∨ x.val + 1 = L) with h0 | h1 | h2
  · left; rw [← hx', h0]; simp
  · right; left; rw [← hx', h1]; simp
  · right; right
    have : x + 1 = 0 := by
      calc x + 1 = ((x.val + 1 : ℕ) : ZMod L) := by rw [Nat.cast_add, hx', Nat.cast_one]
        _ = 0 := by rw [h2]; exact ZMod.natCast_self L
    exact eq_neg_of_add_eq_zero_left this

/-- The ball `{u : |u|_∞ ≤ 1}` of `Z_L^d` has at most `3^d` points (`= 3^d` for `L ≥ 3`). -/
private lemma card_ball_le (d L : ℕ) [NeZero L] :
    (Finset.univ.filter fun u : Zd d L => zdistInf d L u ≤ 1).card ≤ 3 ^ d := by
  set T : Finset (ZMod L) := Finset.univ.filter fun x => zdist L x ≤ 1 with hT
  have hT3 : T.card ≤ 3 := by
    refine le_trans (Finset.card_le_card (t := ({0, 1, -1} : Finset (ZMod L))) ?_)
      Finset.card_le_three
    intro x hx
    have := zdist_le_one (Finset.mem_filter.mp hx).2
    simpa [or_assoc] using this
  have hsub : (Finset.univ.filter fun u : Zd d L => zdistInf d L u ≤ 1) ⊆
      Fintype.piFinset (fun _ : Fin d => T) := by
    intro u hu
    rw [Fintype.mem_piFinset]
    intro i
    have hu' : zdistInf d L u ≤ 1 := (Finset.mem_filter.mp hu).2
    have : zdist L (u i) ≤ 1 :=
      le_trans (Finset.le_sup (f := fun i => zdist L (u i)) (Finset.mem_univ i)) hu'
    simp [hT, this]
  calc _ ≤ (Fintype.piFinset (fun _ : Fin d => T)).card := Finset.card_le_card hsub
    _ = T.card ^ d := by simp [Fintype.card_piFinset]
    _ ≤ 3 ^ d := Nat.pow_le_pow_left hT3 d

/-- Each `c` has at most `3^d` neighbours `c'`:
`Σ_{c'∈𝒜} Σ_{c ∼ c'} q(c) ≤ 3^d Σ_c q(c)` for `q ≥ 0`. -/
private lemma sum_neighbours_le (d L : ℕ) [NeZero L] (𝒜 : Finset (Zd d L)) (q : Zd d L → ℝ)
    (hq : ∀ c, 0 ≤ q c) :
    ∑ c' ∈ 𝒜, ∑ c ∈ Finset.univ.filter (fun c : Zd d L => zdistInf d L (c - c') ≤ 1), q c ≤
      3 ^ d * ∑ c, q c := by
  have h1 : ∑ c' ∈ 𝒜, ∑ c ∈ Finset.univ.filter (fun c : Zd d L => zdistInf d L (c - c') ≤ 1), q c =
      ∑ c, ∑ c' ∈ 𝒜.filter (fun c' => zdistInf d L (c - c') ≤ 1), q c := by
    simp only [Finset.sum_filter]
    exact Finset.sum_comm
  rw [h1, Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((𝒜.filter (fun c' => zdistInf d L (c - c') ≤ 1)).card : ℝ) ≤ 3 ^ d := by
    have : (𝒜.filter (fun c' => zdistInf d L (c - c') ≤ 1)).card ≤ 3 ^ d := by
      refine le_trans (Finset.card_le_card_of_injOn (fun c' => c - c') ?_ ?_) (card_ball_le d L)
      · intro c' hc'
        simpa using (Finset.mem_filter.mp hc').2
      · intro x _ y _ hxy
        simpa using hxy
    exact_mod_cast this
  exact mul_le_mul_of_nonneg_right hcard (hq c)

end Neighbours

section Pin

/-- **`STContractPt`** (`ygdhmsgq0`, `(eq_sym_loop_bound)`, `3_5:751-797`): the pointwise
contraction inequality of Step 2 holds for every `d`, `L`, `W`, every Hermitian `H` on the fine
lattice and every `z` with `Im z > 0`: deterministic, no hypothesis beyond those of the pin; the
constant `3^d / (W^d Im z)` is exact. -/
theorem stContractPt_holds (d : ℕ) : STContractPt d := by
  intro L W _ _ H z hH hz σ a b 𝒜 M hM0 hM
  have hHb : (blockMat d L W H).IsHermitian := hH.submatrix _
  have hη : z.im ≠ 0 := hz.ne'
  set G : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ := Gres (blockMat d L W H) z with hGdef
  have hG : ∀ s, (G s)ᴴ = G (!s) := Gres_conjTranspose hHb z
  set w : ℝ := ((W : ℕ) : ℝ) ^ d with hwdef
  have hWpos : (0 : ℝ) < ((W : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hw : 0 < w := pow_pos hWpos d
  have hκ : ‖((W : ℂ) ^ d)⁻¹‖ = w⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_natCast]
  set q : Zd d L → ℝ := fun c => hs (Psi G (σ 0) (σ 1) a b c) with hqdef
  have hq0 : ∀ c, 0 ≤ q c := fun c => hs_nonneg _
  -- the pointwise bound `(eq_sym_loop_bound_old)`
  have hpt : ∀ c' ∈ 𝒜, ∀ c : Zd d L,
      ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖ ≤
        w⁻¹ ^ 4 * M * q c := by
    intro c' hc' c
    -- `√(hs A) ≤ w² M`
    have hL4 : loopFine d L W H z ![σ 0, !(σ 0), σ 0, !(σ 0)] ![c', b, c', b] =
        (((W : ℂ) ^ d)⁻¹) ^ 4 * (hs (Amat G (σ 0) b c') : ℂ) := by
      rw [loop4_eq, hs_Amat hG]
    have hn4 : ‖loopFine d L W H z ![σ 0, !(σ 0), σ 0, !(σ 0)] ![c', b, c', b]‖ =
        w⁻¹ ^ 4 * hs (Amat G (σ 0) b c') := by
      rw [hL4, norm_mul, norm_pow, hκ, Complex.norm_real, Real.norm_of_nonneg (hs_nonneg _)]
    have hsqrt : √(hs (Amat G (σ 0) b c')) ≤ w ^ 2 * M := by
      have h1 := hM c' hc'
      rw [← Real.sqrt_eq_rpow] at h1
      have h2 := (Real.sqrt_le_iff.mp h1).2
      rw [hn4] at h2
      rw [Real.sqrt_le_left (by positivity)]
      have hwi : w⁻¹ ^ 4 * w ^ 4 = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hw.ne', one_pow]
      calc hs (Amat G (σ 0) b c') = w ^ 4 * (w⁻¹ ^ 4 * hs (Amat G (σ 0) b c')) := by
            rw [← mul_assoc, mul_comm (w ^ 4), hwi, one_mul]
        _ ≤ w ^ 4 * M ^ 2 := by gcongr
        _ = (w ^ 2 * M) ^ 2 := by ring
    rw [loop6_eq H z hG, norm_mul, norm_pow, hκ]
    calc w⁻¹ ^ 6 * ‖(Psi G (σ 0) (σ 1) a b c * Amat G (σ 0) b c' *
            (Psi G (σ 0) (σ 1) a b c)ᴴ).trace‖
        ≤ w⁻¹ ^ 6 * (√(hs (Amat G (σ 0) b c')) * hs (Psi G (σ 0) (σ 1) a b c)) := by
          gcongr
          exact norm_trace_mul_mul_conjTranspose_le _ _
      _ ≤ w⁻¹ ^ 6 * ((w ^ 2 * M) * q c) := by
          gcongr
          exact hq0 c
      _ = w⁻¹ ^ 4 * M * q c := by
          field_simp
  -- Ward's identity for the sum over `c`
  set mx : ℝ := max ‖loopFine d L W H z ![true, σ 1, !(σ 1)] ![a, b, a]‖
    ‖loopFine d L W H z ![false, σ 1, !(σ 1)] ![a, b, a]‖ with hmx
  set Y : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
    Pm d L W a * G (σ 1) * Pm d L W b * G (!(σ 1)) * Pm d L W a with hYdef
  have hY : ∀ s : Bool, ‖(G s * Y).trace‖ =
      w ^ 3 * ‖loopFine d L W H z ![s, σ 1, !(σ 1)] ![a, b, a]‖ := by
    intro s
    rw [loop3_eq H z s (σ 1) a b, norm_mul, norm_pow, hκ, ← mul_assoc (w ^ 3)]
    have : w ^ 3 * w⁻¹ ^ 3 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hw.ne', one_pow]
    rw [this, one_mul]
  have hsum : ∑ c, q c ≤ w ^ 3 * mx / z.im := by
    have hW := Gres_ward_left hHb hη (σ 0)
    have hK := trace_Kmat (G := G) (s0 := σ 0) (σ 1) a b hW
    have h1 : ((∑ c, q c : ℝ) : ℂ) = (Kmat G (σ 0) (σ 1) a b).trace := by
      rw [Complex.ofReal_sum]; exact sum_hs_Psi hG _ _ a b
    have hnorm : ∑ c, q c = ‖(Kmat G (σ 0) (σ 1) a b).trace‖ := by
      rw [← h1, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun c _ => hq0 c)]
    have hc : ‖(2 * Complex.I * (z.im : ℂ))⁻¹‖ = (2 * z.im)⁻¹ := by
      rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
        Real.norm_of_nonneg hz.le]
      simp
    have hdiff : ‖(G true * Y).trace - (G false * Y).trace‖ ≤ 2 * (w ^ 3 * mx) := by
      refine (norm_sub_le _ _).trans ?_
      rw [hY true, hY false]
      have h1' : ‖loopFine d L W H z ![true, σ 1, !(σ 1)] ![a, b, a]‖ ≤ mx := le_max_left _ _
      have h2' : ‖loopFine d L W H z ![false, σ 1, !(σ 1)] ![a, b, a]‖ ≤ mx := le_max_right _ _
      have hw3 : 0 ≤ w ^ 3 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h1' hw3, mul_le_mul_of_nonneg_left h2' hw3]
    rw [hnorm, hK, norm_mul, hc]
    calc (2 * z.im)⁻¹ * ‖(G true * Y).trace - (G false * Y).trace‖
        ≤ (2 * z.im)⁻¹ * (2 * (w ^ 3 * mx)) :=
          mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = w ^ 3 * mx / z.im := by field_simp
  have hmx0 : 0 ≤ mx := (norm_nonneg _).trans (le_max_left _ _)
  -- assemble
  calc ∑ c' ∈ 𝒜, ∑ c ∈ Finset.univ.filter (fun c : Zd d L => zdistInf d L (c - c') ≤ 1),
        ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
      ≤ ∑ c' ∈ 𝒜, ∑ c ∈ Finset.univ.filter (fun c : Zd d L => zdistInf d L (c - c') ≤ 1),
          (w⁻¹ ^ 4 * M) * q c := by
        refine Finset.sum_le_sum fun c' hc' => Finset.sum_le_sum fun c _ => ?_
        exact hpt c' hc' c
    _ = (w⁻¹ ^ 4 * M) * ∑ c' ∈ 𝒜, ∑ c ∈ Finset.univ.filter
          (fun c : Zd d L => zdistInf d L (c - c') ≤ 1), q c := by
        simp only [← Finset.mul_sum]
    _ ≤ (w⁻¹ ^ 4 * M) * (3 ^ d * ∑ c, q c) :=
        mul_le_mul_of_nonneg_left (sum_neighbours_le d L 𝒜 q hq0) (by positivity)
    _ ≤ (w⁻¹ ^ 4 * M) * (3 ^ d * (w ^ 3 * mx / z.im)) := by
        gcongr
    _ = 3 ^ d / (w * z.im) * M * mx := by
        field_simp

end Pin

/-! ## 6. Compiled instances at `d = 3`, `L = 3`, `W = 2`

`N = (W L)^d = 216` sites, `W^d = 8` sites per block, `L^d = 27` block labels, each block with
`3^d = 27` neighbours.  The matrix is the real symmetric `H_{ij} = (i)_0 + (j)_0` (coordinate `0`
of the two sites, as natural numbers): Hermitian, not block diagonal and not a multiple of the
identity, so the loops do not vanish.  The spectral parameter is `z = 1/2 + i/4` (`η = 1/4 > 0`).
`M` is the sum over `𝒜` of the square roots `‖𝓛^{(4)}‖^{1/2}`, which dominates each term, so the
hypothesis on `M` holds by construction.  Every deterministic hypothesis of the pin is discharged
(Hermitian, `Im z > 0`, `0 ≤ M`, the bound on `M`); there is no other hypothesis.  The two instances
use both orders of the signs `σ = (+,-)` and `σ = (-,+)` (the Ward identity for first sign `-`), the
sets `𝒜 = {0, b}` and `𝒜 = Z_L^d` (27 blocks), `a = 0`, `b = (1,1,1)`. -/

section Instances

private noncomputable def ptH : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ :=
  Matrix.of fun i j => (((i 0).val + (j 0).val : ℕ) : ℂ)

private theorem ptH_herm : ptH.IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, ptH, Matrix.of_apply]
  rw [add_comm (j 0).val, star_natCast]

private def ptZ : ℂ := ⟨1 / 2, 1 / 4⟩

private theorem ptZ_im : 0 < ptZ.im := by
  change (0 : ℝ) < 1 / 4
  norm_num

private def ptB : Zd 3 3 := fun _ => 1

private noncomputable def ptM (σ0 : Bool) (𝒜 : Finset (Zd 3 3)) : ℝ :=
  ∑ c' ∈ 𝒜, ‖loopFine 3 3 2 ptH ptZ ![σ0, !σ0, σ0, !σ0] ![c', ptB, c', ptB]‖ ^ (1 / 2 : ℝ)

private theorem ptM_nonneg (σ0 : Bool) (𝒜 : Finset (Zd 3 3)) : 0 ≤ ptM σ0 𝒜 :=
  Finset.sum_nonneg fun _ _ => by positivity

private theorem ptM_bound (σ0 : Bool) (𝒜 : Finset (Zd 3 3)) :
    ∀ c' ∈ 𝒜, ‖loopFine 3 3 2 ptH ptZ ![σ0, !σ0, σ0, !σ0] ![c', ptB, c', ptB]‖ ^ (1 / 2 : ℝ) ≤
      ptM σ0 𝒜 := fun c' hc' =>
  Finset.single_le_sum (f := fun c' => ‖loopFine 3 3 2 ptH ptZ ![σ0, !σ0, σ0, !σ0]
    ![c', ptB, c', ptB]‖ ^ (1 / 2 : ℝ)) (fun _ _ => by positivity) hc'

/-- The instance matrix has `N = 216` sites. -/
example : Fintype.card (Idx 3 3 2) = 216 := by
  rw [RBM.Gauss.card_Idx]; norm_num

/-- `stContractPt_holds` at `d = 3`, `L = 3`, `W = 2`, `σ = (+,-)`, `a = 0`, `b = (1,1,1)`,
`𝒜 = {0, b}`, `z = 1/2 + i/4`. -/
example :
    ∑ c' ∈ ({0, ptB} : Finset (Zd 3 3)),
        ∑ c ∈ Finset.univ.filter (fun c : Zd 3 3 => zdistInf 3 3 (c - c') ≤ 1),
          ‖loopFine 3 3 2 ptH ptZ ![true, false, true, false, true, false]
            ![0, ptB, c', ptB, 0, c]‖ ≤
      3 ^ 3 / ((((2 : ℕ) : ℝ)) ^ 3 * ptZ.im) * ptM true {0, ptB} *
        max ‖loopFine 3 3 2 ptH ptZ ![true, false, true] ![0, ptB, 0]‖
          ‖loopFine 3 3 2 ptH ptZ ![false, false, true] ![0, ptB, 0]‖ :=
  stContractPt_holds 3 3 2 ptH ptZ ptH_herm ptZ_im ![true, false] 0 ptB {0, ptB}
    (ptM true {0, ptB}) (ptM_nonneg _ _) (ptM_bound true {0, ptB})

/-- `stContractPt_holds` at the same data with `σ = (-,+)` (first sign `-`) and `𝒜 = Z_L^d`. -/
example :
    ∑ c' ∈ (Finset.univ : Finset (Zd 3 3)),
        ∑ c ∈ Finset.univ.filter (fun c : Zd 3 3 => zdistInf 3 3 (c - c') ≤ 1),
          ‖loopFine 3 3 2 ptH ptZ ![false, true, false, true, false, true]
            ![0, ptB, c', ptB, 0, c]‖ ≤
      3 ^ 3 / ((((2 : ℕ) : ℝ)) ^ 3 * ptZ.im) * ptM false Finset.univ *
        max ‖loopFine 3 3 2 ptH ptZ ![true, true, false] ![0, ptB, 0]‖
          ‖loopFine 3 3 2 ptH ptZ ![false, true, false] ![0, ptB, 0]‖ :=
  stContractPt_holds 3 3 2 ptH ptZ ptH_herm ptZ_im ![false, true] 0 ptB Finset.univ
    (ptM false Finset.univ) (ptM_nonneg _ _) (ptM_bound false Finset.univ)

end Instances

end RBM.Gauss.Sizes
