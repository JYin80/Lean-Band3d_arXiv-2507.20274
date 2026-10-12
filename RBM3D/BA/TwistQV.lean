/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.TwistPins
import RBM3D.BA.EMn2BA
import RBM3D.Induction.Contract

/-!
# BA stage TL, row TL2c (T2430): the quadratic variation of the twisted 2-loop, `BATwistSrc3` (draft header)
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false
set_option linter.unusedDecidableInType false

open MeasureTheory Filter
open scoped Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-! ## 1. Tools copied from `Induction/Contract.lean` (private there) -/

section Tools
open Matrix Finset
open scoped ComplexOrder

/-! ### 1.1 The power-trace bound (`Induction/Contract.lean:81-193`, private there) -/

section PsdTools

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- real inequality -/
private lemma TwistQV_sum_mul_pow_le (lam w : ι → ℝ) (hl : ∀ i, 0 ≤ lam i) (hw : ∀ i, 0 ≤ w i) {p : ℕ}
    (hp : 1 ≤ p) :
    (∑ i, lam i * w i) ^ p ≤ (∑ i, w i) ^ p * ∑ i, lam i ^ p := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Nat.pos_iff_ne_zero.mp hp, zero_pow]
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ lam Finset.univ_nonempty
  have h1 : ∑ i, lam i * w i ≤ lam i₀ * ∑ i, w i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hi₀ i (Finset.mem_univ _)) (hw i)
  have h2 : lam i₀ ^ p ≤ ∑ i, lam i ^ p :=
    Finset.single_le_sum (f := fun i => lam i ^ p) (fun i _ => pow_nonneg (hl i) p)
      (Finset.mem_univ i₀)
  calc (∑ i, lam i * w i) ^ p ≤ (lam i₀ * ∑ i, w i) ^ p :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => mul_nonneg (hl i) (hw i)) h1 p
    _ = (∑ i, w i) ^ p * lam i₀ ^ p := by rw [mul_pow, mul_comm]
    _ ≤ (∑ i, w i) ^ p * ∑ i, lam i ^ p :=
        mul_le_mul_of_nonneg_left h2 (pow_nonneg (Finset.sum_nonneg fun i _ => hw i) p)

private lemma TwistQV_psd_quad_pow_le {B : Matrix ι ι ℂ} (hB : B.PosSemidef) (v : ι → ℂ) {p : ℕ}
    (hp : 1 ≤ p) :
    ((star v ⬝ᵥ (B *ᵥ v)).re) ^ p ≤ (∑ i, ‖v i‖ ^ 2) ^ p * (B ^ p).trace.re := by
  classical
  have hH := hB.isHermitian
  set U : Matrix ι ι ℂ := (hH.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  set lam : ι → ℝ := hH.eigenvalues with hlam
  have hl0 : ∀ i, 0 ≤ lam i := fun i => hB.eigenvalues_nonneg i
  have hUU : star U * U = 1 := by
    simp [hU]
  have hUU' : U * star U = 1 := by
    simp [hU]
  have hspec : B = U * diagonal (fun i => (lam i : ℂ)) * star U := by
    have := hH.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, hU, hlam, Function.comp_def] using this
  set D : Matrix ι ι ℂ := diagonal (fun i => (lam i : ℂ)) with hD
  set y : ι → ℂ := (star U) *ᵥ v with hy
  have hv : v = U *ᵥ y := by
    rw [hy, Matrix.mulVec_mulVec, hUU', Matrix.one_mulVec]
  have hstar : star y = star v ᵥ* U := by
    rw [hy, Matrix.star_mulVec]
    simp [Matrix.star_eq_conjTranspose]
  have hnorm : ∀ w : ι → ℂ, star w ⬝ᵥ w = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
    intro w
    simp only [dotProduct, Pi.star_apply, Complex.star_def]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.conj_mul']
  have hq : star v ⬝ᵥ (B *ᵥ v) = ((∑ i, lam i * ‖y i‖ ^ 2 : ℝ) : ℂ) := by
    have h1 : B *ᵥ v = U *ᵥ (D *ᵥ y) := by
      rw [hspec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hy]
    rw [h1, Matrix.dotProduct_mulVec, ← hstar]
    simp only [dotProduct, Pi.star_apply, hD, Matrix.mulVec_diagonal, Complex.star_def]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, mul_comm (starRingEnd ℂ (y i)) (lam i : ℂ), mul_assoc, Complex.conj_mul']
  have hvv : ∑ i, ‖v i‖ ^ 2 = ∑ i, ‖y i‖ ^ 2 := by
    have h2 : star v ⬝ᵥ v = star y ⬝ᵥ y := by
      rw [hstar, ← Matrix.dotProduct_mulVec, ← hv]
    have := h2
    rw [hnorm, hnorm] at this
    exact_mod_cast this
  have htr : (B ^ p).trace = ((∑ i, lam i ^ p : ℝ) : ℂ) := by
    have h3 : ∀ q : ℕ, B ^ q = U * D ^ q * star U := by
      intro q
      induction q with
      | zero => simp [hUU']
      | succ q ih =>
        rw [pow_succ, ih, hspec]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul, pow_succ, Matrix.mul_assoc]
    rw [h3 p, Matrix.trace_mul_cycle, hUU, Matrix.one_mul, hD, Matrix.diagonal_pow,
      Matrix.trace_diagonal]
    push_cast
    rfl
  rw [hq, htr, hvv]
  simp only [Complex.ofReal_re]
  exact TwistQV_sum_mul_pow_le lam (fun i => ‖y i‖ ^ 2) hl0 (fun i => by positivity) hp

/-- `Σ_t |Σ_s ρ_s A_{st}|² = ⟨v, A Aᴴ v⟩` with `v = conj ρ`. -/
private lemma TwistQV_sum_norm_sq_vecMul (A : Matrix ι ι ℂ) (ρ : ι → ℂ) :
    ∑ t, ‖∑ s, ρ s * A s t‖ ^ 2 = (star (star ρ) ⬝ᵥ ((A * Aᴴ) *ᵥ star ρ)).re := by
  set v : ι → ℂ := star ρ with hv
  have h1 : Aᴴ *ᵥ v = fun t => star (∑ s, ρ s * A s t) := by
    funext t
    simp [Matrix.mulVec, dotProduct, hv, Matrix.conjTranspose_apply, mul_comm, star_sum]
  have h2 : star v ⬝ᵥ ((A * Aᴴ) *ᵥ v) = star (Aᴴ *ᵥ v) ⬝ᵥ (Aᴴ *ᵥ v) := by
    rw [← Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec, 
      Matrix.conjTranspose_conjTranspose]
  rw [h2, h1]
  simp only [dotProduct, Pi.star_apply, Complex.star_def]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Complex.conj_conj, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- the quadratic-form bound of  from the power trace -/
private lemma TwistQV_rowbound_of_pow (A : Matrix ι ι ℂ) {p : ℕ} (hp : 1 ≤ p) {T : ℝ} (hT0 : 0 ≤ T)
    (hT : (((A * Aᴴ) ^ p).trace).re ≤ T) (ρ : ι → ℂ) :
    ∑ t, ‖∑ s, ρ s * A s t‖ ^ 2 ≤ T ^ ((p : ℝ)⁻¹) * ∑ s, ‖ρ s‖ ^ 2 := by
  have hpos := Matrix.posSemidef_self_mul_conjTranspose A
  have hb := TwistQV_psd_quad_pow_le hpos (star ρ) hp
  rw [← TwistQV_sum_norm_sq_vecMul] at hb
  have hn : ∑ i, ‖(star ρ) i‖ ^ 2 = ∑ s, ‖ρ s‖ ^ 2 := by simp
  rw [hn] at hb
  have ha0 : 0 ≤ ∑ t, ‖∑ s, ρ s * A s t‖ ^ 2 := by positivity
  have hn0 : 0 ≤ ∑ s, ‖ρ s‖ ^ 2 := by positivity
  have hp0 : p ≠ 0 := by omega
  refine le_of_pow_le_pow_left₀ hp0 (by positivity) ?_
  rw [mul_pow, Real.rpow_inv_natCast_pow hT0 hp0]
  calc _ ≤ _ := hb
    _ ≤ _ := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hT (pow_nonneg hn0 p)

end PsdTools

/-! ### 1.2 The resolvent: adjoint and Ward identity (`Induction/Contract.lean:224-291`, private there) -/

section ResolventTools

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `G(σ)^* = G(-σ)` for Hermitian `H` (`Gres`, `GLoopFlow.lean:74`). -/
private lemma TwistQV_Gres_conjTranspose {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (z : ℂ) (σ : Bool) :
    (Gres H z σ)ᴴ = Gres H z (!σ) := by
  have hH' : Hᴴ = H := hH
  cases σ with
  | true =>
    simp only [Gres, ↓reduceIte, Bool.not_true, Bool.false_eq_true, ← Matrix.nonsing_inv_eq_ringInverse,
      Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, hH', Complex.star_def]
  | false =>
    simp only [Gres, Bool.false_eq_true, ↓reduceIte, Bool.not_false, ← Matrix.nonsing_inv_eq_ringInverse,
      Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, hH', Complex.star_def, Complex.conj_conj]

/-- **Ward's identity** in the form `G(+) - G(-) = (z - z̄) G(+) G(-) = (z - z̄) G(-) G(+)`
(`(eq_Ward0)`, `1_2:1018`; `Im z ≠ 0`). -/
private lemma TwistQV_Gres_sub {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    Gres H z true - Gres H z false = (z - (starRingEnd ℂ) z) • (Gres H z true * Gres H z false) ∧
    Gres H z true - Gres H z false = (z - (starRingEnd ℂ) z) • (Gres H z false * Gres H z true) := by
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
private lemma TwistQV_sub_conj_eq (z : ℂ) : z - (starRingEnd ℂ) z = 2 * Complex.I * (z.im : ℂ) := by
  rw [Complex.sub_conj]; push_cast; ring

/-- `G(-σ) G(σ) = (2 i η)⁻¹ (G(+) - G(-))`: the Ward identity used for the two ends of a loop
(the algebraic identity `(eq_Ward0)`, `1_2:1018`, behind `(WI_calL)`, `1_2:1036`, used at
`3_5:954`). -/
private lemma TwistQV_Gres_ward_left {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (σ : Bool) :
    Gres H z (!σ) * Gres H z σ = (2 * Complex.I * (z.im : ℂ))⁻¹ • (Gres H z true - Gres H z false) := by
  have hk : (2 * Complex.I * (z.im : ℂ)) ≠ 0 := by
    have : (z.im : ℂ) ≠ 0 := by exact_mod_cast hz
    simp [this]
  obtain ⟨h1, h2⟩ := TwistQV_Gres_sub hH hz
  rw [TwistQV_sub_conj_eq] at h1 h2
  cases σ with
  | true =>
    simp only [Bool.not_true]
    rw [h2, smul_smul, inv_mul_cancel₀ hk, one_smul]
  | false =>
    simp only [Bool.not_false]
    rw [h1, smul_smul, inv_mul_cancel₀ hk, one_smul]

end ResolventTools

/-! ### 1.3 Words (`Induction/Contract.lean:309-320, 409-418`, private there) -/

section WordTools

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] (G : Bool → Matrix ι ι ℂ) (E : κ → Matrix ι ι ℂ)

/-- The product `G(σ_1) E_{a_1} ⋯ G(σ_n) E_{a_n}` of a list of pairs `(σ_i, a_i)`. -/
private def TwistQV_wd (l : List (Bool × κ)) : Matrix ι ι ℂ := (l.map fun p => G p.1 * E p.2).prod

@[simp] private lemma TwistQV_wd_nil : TwistQV_wd G E [] = 1 := by simp [TwistQV_wd]

@[simp] private lemma TwistQV_wd_cons (p : Bool × κ) (l : List (Bool × κ)) :
    TwistQV_wd G E (p :: l) = (G p.1 * E p.2) * TwistQV_wd G E l := by simp [TwistQV_wd]

private lemma TwistQV_wd_append (l₁ l₂ : List (Bool × κ)) :
    TwistQV_wd G E (l₁ ++ l₂) = TwistQV_wd G E l₁ * TwistQV_wd G E l₂ := by simp [TwistQV_wd]

@[simp] private lemma TwistQV_wd_singleton (p : Bool × κ) : TwistQV_wd G E [p] = G p.1 * E p.2 := by simp [TwistQV_wd]

/-- `(TwistQV_wd l)^p` is the word of `p` copies of `l`: the loop of length `p |l|` in `eq:Apsipsi1`. -/
private lemma TwistQV_wd_pow (l : List (Bool × κ)) (p : ℕ) :
    (TwistQV_wd G E l) ^ p = TwistQV_wd G E ((List.replicate p l).flatten) := by
  induction p with
  | zero => simp
  | succ p ih => rw [pow_succ', ih, List.replicate_succ, List.flatten_cons, TwistQV_wd_append]

private lemma TwistQV_length_replicate_flatten {α : Type*} (l : List α) (p : ℕ) :
    ((List.replicate p l).flatten).length = p * l.length := by
  simp [List.length_flatten, List.map_replicate, List.sum_replicate]

end WordTools

/-! ### 1.4 `tr((P D P)^p) = tr((D P)^p)` (`Induction/Contract.lean:485-503`, private there) -/

/-- `tr((P D P)^p) = tr((D P)^p)` for an idempotent `P` and `p ≥ 1`. -/
private lemma TwistQV_trace_pow_proj {ι : Type*} [Fintype ι] [DecidableEq ι] (P D : Matrix ι ι ℂ)
    (hP : P * P = P) {p : ℕ} (hp : 1 ≤ p) :
    ((P * D * P) ^ p).trace = ((D * P) ^ p).trace := by
  have hDP : ∀ q : ℕ, (D * P) ^ (q + 1) * P = (D * P) ^ (q + 1) := by
    intro q
    rw [pow_succ, Matrix.mul_assoc, Matrix.mul_assoc, hP, ← Matrix.mul_assoc]
  have key : ∀ q : ℕ, (P * D * P) ^ (q + 1) = P * (D * P) ^ (q + 1) := by
    intro q
    induction q with
    | zero => simp [Matrix.mul_assoc]
    | succ q ih =>
      rw [pow_succ, ih, pow_succ (D * P) (q + 1)]
      calc P * (D * P) ^ (q + 1) * (P * D * P)
          = P * ((D * P) ^ (q + 1) * P) * D * P := by simp only [Matrix.mul_assoc]
        _ = P * ((D * P) ^ (q + 1) * (D * P)) := by rw [hDP]; simp only [Matrix.mul_assoc]
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [key, Matrix.trace_mul_comm, hDP]

/-! ### 1.5 The block projection `P_a = W^d E_a` on `Vtx` (`Induction/Contract.lean:706-733`, private there) -/

section PmTools

variable (d L W : ℕ) [NeZero L]

/-- The block projection `P_a = W^d E_a`: the diagonal matrix of the indicator of the block `a`. -/
private def TwistQV_Pm (a : Zd d L) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  Matrix.diagonal fun x => if x.1 = a then 1 else 0

variable {d L W}

private lemma TwistQV_Eblk_eq_smul_Pm (a : Zd d L) :
    Eblk d L W a = ((W : ℂ) ^ d)⁻¹ • TwistQV_Pm d L W a := by
  ext x y
  by_cases hxy : x = y
  · subst hxy
    by_cases hx : x.1 = a <;> simp [Eblk, TwistQV_Pm, hx]
  · simp [Eblk, TwistQV_Pm, hxy]

private lemma TwistQV_Pm_eq_smul_Eblk [NeZero W] (a : Zd d L) :
    TwistQV_Pm d L W a = ((W : ℂ) ^ d) • Eblk d L W a := by
  have hW : ((W : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne W))
  rw [TwistQV_Eblk_eq_smul_Pm, smul_smul, mul_inv_cancel₀ hW, one_smul]

private lemma TwistQV_Pm_conjTranspose (a : Zd d L) : (TwistQV_Pm d L W a)ᴴ = TwistQV_Pm d L W a := by
  refine (Matrix.isHermitian_diagonal_iff.mpr fun x => ?_).eq
  by_cases h : x.1 = a <;> simp [h, IsSelfAdjoint]

private lemma TwistQV_Pm_mul_self (a : Zd d L) : TwistQV_Pm d L W a * TwistQV_Pm d L W a = TwistQV_Pm d L W a := by
  simp only [TwistQV_Pm, Matrix.diagonal_mul_diagonal]
  congr 1
  ext x
  by_cases h : x.1 = a <;> simp [h]

end PmTools

/-! ### 1.6 The Ward constant (`Induction/Contract.lean:743-756`, private there) -/

/-- `Σ_a ‖c‖`-type bound: `|c (t₁ - t₂)| ≤ M / η` for `‖c‖ = (2η)⁻¹`, `|t_i| ≤ M`. -/
private lemma TwistQV_norm_ward_trace_le {c t₁ t₂ : ℂ} {η M : ℝ} (hη : 0 < η) (hc : ‖c‖ = (2 * η)⁻¹)
    (h₁ : ‖t₁‖ ≤ M) (h₂ : ‖t₂‖ ≤ M) : ‖c * (t₁ - t₂)‖ ≤ M / η := by
  rw [norm_mul, hc]
  have : ‖t₁ - t₂‖ ≤ 2 * M := (norm_sub_le _ _).trans (by linarith)
  calc (2 * η)⁻¹ * ‖t₁ - t₂‖ ≤ (2 * η)⁻¹ * (2 * M) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = M / η := by field_simp

private lemma TwistQV_norm_Ward_const {z : ℂ} (hz : 0 < z.im) :
    ‖(2 * Complex.I * (z.im : ℂ))⁻¹‖ = (2 * z.im)⁻¹ := by
  rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hz.le]
  simp


/-! ### 1.7 Words are loops (`Induction/Contract.lean:1029-1065`, private there) -/

section LoopTools

private lemma TwistQV_foldr_eq_wd {ι κ : Type*} [Fintype ι] [DecidableEq ι] (G : Bool → Matrix ι ι ℂ)
    (E : κ → Matrix ι ι ℂ) (l : List (Bool × κ)) :
    l.foldr (fun p M => G p.1 * E p.2 * M) 1 = TwistQV_wd G E l := by
  induction l with
  | nil => simp
  | cons p l ih => simp [ih]

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- Every word is a loop: `|tr ∏ G E| ≤ max_{σ,a} |𝓛^{(n)}|` with `n` its length. -/
private lemma TwistQV_norm_trace_wd_le (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ)
    (Lst : List (Bool × Zd d L)) :
    ‖(TwistQV_wd (Gres (blockMat d L W H) z) (Eblk d L W) Lst).trace‖ ≤
      Contract_maxLoopM d L W H z Lst.length := by
  unfold Contract_maxLoopM
  refine le_trans (le_of_eq ?_)
    (Finset.le_sup' (fun p : (Fin Lst.length → Bool) × (Fin Lst.length → Zd d L) =>
      ‖loopFine d L W H z p.1 p.2‖)
      (Finset.mem_univ ((fun i => (Lst.get i).1), (fun i => (Lst.get i).2))))
  unfold loopFine loopM TwistQV_wd
  have hmap : ∀ f : Bool × Zd d L → Matrix (Vtx d L W) (Vtx d L W) ℂ,
      Lst.map f = List.ofFn (fun i : Fin Lst.length => f (Lst.get i)) := fun f =>
    List.ext_getElem (by simp) fun i h1 h2 => by simp
  dsimp only
  rw [hmap]

private lemma TwistQV_maxLoopM_nonneg (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) (k : ℕ) :
    0 ≤ Contract_maxLoopM d L W H z k :=
  (norm_nonneg _).trans (Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Zd d L) =>
    ‖loopFine d L W H z p.1 p.2‖) (Finset.mem_univ ((fun _ => true), (fun _ => 0))))

end LoopTools

end Tools

/-! ## 2. The offset form of the Schatten row bound -/

section Core
open Matrix Finset

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The entries of `P_{a₁} G P_{a₂}`. -/
private lemma TwistQV_PGP_apply (G : Matrix (Vtx d L W) (Vtx d L W) ℂ) (a₁ a₂ : Zd d L) (s t : Vtx d L W) :
    (TwistQV_Pm d L W a₁ * G * TwistQV_Pm d L W a₂) s t =
      (if s.1 = a₁ then 1 else 0) * G s t * (if t.1 = a₂ then 1 else 0) := by
  rw [TwistQV_Pm, TwistQV_Pm, Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- **The Schatten row bound in offset form**: for `T ≥ tr[(A A^*)^p]`, `A = P_{a₁} G P_{a₂}`,
`Σ_{o'} |Σ_o r_o G_{(a₁,o),(a₂,o')}|² ≤ T^{1/p} Σ_o |r_o|²` (`TwistQV_rowbound_of_pow` with `ρ = 1_{[a₁]} r`). -/
private lemma TwistQV_rowbound_off (G : Matrix (Vtx d L W) (Vtx d L W) ℂ) (a₁ a₂ : Zd d L) {p : ℕ}
    (hp : 1 ≤ p) {T : ℝ} (hT0 : 0 ≤ T)
    (hT : ((((TwistQV_Pm d L W a₁ * G * TwistQV_Pm d L W a₂) *
      (TwistQV_Pm d L W a₁ * G * TwistQV_Pm d L W a₂)ᴴ) ^ p).trace).re ≤ T)
    (r : Fin (W ^ d) → ℂ) :
    ∑ o' : Fin (W ^ d), ‖∑ o : Fin (W ^ d), r o * G (a₁, o) (a₂, o')‖ ^ 2 ≤
      T ^ ((p : ℝ)⁻¹) * ∑ o, ‖r o‖ ^ 2 := by
  have h := TwistQV_rowbound_of_pow (TwistQV_Pm d L W a₁ * G * TwistQV_Pm d L W a₂) hp hT0 hT
    (fun s => if s.1 = a₁ then r s.2 else 0)
  have hrow : ∀ t : Vtx d L W, ∑ s : Vtx d L W, (if s.1 = a₁ then r s.2 else 0) *
      (TwistQV_Pm d L W a₁ * G * TwistQV_Pm d L W a₂) s t =
        (if t.1 = a₂ then 1 else 0) * ∑ o : Fin (W ^ d), r o * G (a₁, o) t := by
    intro t
    simp only [TwistQV_PGP_apply]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single a₁]
    · simp only [ite_true, one_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun o _ => ?_
      ring
    · intro a _ ha
      simp [ha]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp only [hrow] at h
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a₂] at h
  · simp only [ite_true, one_mul] at h
    have hs : ∑ s : Vtx d L W, ‖if s.1 = a₁ then r s.2 else 0‖ ^ 2 = ∑ o, ‖r o‖ ^ 2 := by
      rw [Fintype.sum_prod_type, Finset.sum_eq_single a₁]
      · simp
      · intro a _ ha; simp [ha]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hs] at h
    exact h
  · intro b _ hb
    simp [hb]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The Schatten trace is a loop**: `tr[((P_{a₁} G(s) P_{a₂})(P_{a₁} G(s) P_{a₂})^*)^p]` is `(W^d)^{2p}` times the
trace of the word `(G(s) E_{a₂} G(-s) E_{a₁})^p` of length `2p` (the proof of `hTb` in `part2_matrix`,
`Induction/Contract.lean:927-950`, for the word of length `2`). -/
private lemma TwistQV_Tbound {Hb : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ} (hH : Hb.IsHermitian) (Mx : ℕ → ℝ)
    (hM : ∀ Lst : List (Bool × Zd d L), ‖(TwistQV_wd (Gres Hb z) (Eblk d L W) Lst).trace‖ ≤ Mx Lst.length)
    (s : Bool) (a₁ a₂ : Zd d L) {p : ℕ} (hp : 1 ≤ p) :
    ((((TwistQV_Pm d L W a₁ * Gres Hb z s * TwistQV_Pm d L W a₂) *
      (TwistQV_Pm d L W a₁ * Gres Hb z s * TwistQV_Pm d L W a₂)ᴴ) ^ p).trace).re ≤
        ((W : ℝ) ^ d) ^ (2 * p) * Mx (2 * p) := by
  set G := Gres Hb z with hGdef
  set E := Eblk d L W with hEdef
  have hG : ∀ σ, (G σ)ᴴ = G (!σ) := TwistQV_Gres_conjTranspose hH z
  have hPE : ∀ a, TwistQV_Pm d L W a = ((W : ℂ) ^ d) • E a := fun a => TwistQV_Pm_eq_smul_Eblk a
  have h1 : (TwistQV_Pm d L W a₁ * G s * TwistQV_Pm d L W a₂) * (TwistQV_Pm d L W a₁ * G s * TwistQV_Pm d L W a₂)ᴴ =
      TwistQV_Pm d L W a₁ * (G s * TwistQV_Pm d L W a₂ * (G s)ᴴ) * TwistQV_Pm d L W a₁ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, TwistQV_Pm_conjTranspose, TwistQV_Pm_conjTranspose]
    calc TwistQV_Pm d L W a₁ * G s * TwistQV_Pm d L W a₂ * (TwistQV_Pm d L W a₂ * ((G s)ᴴ * TwistQV_Pm d L W a₁))
        = TwistQV_Pm d L W a₁ * G s * (TwistQV_Pm d L W a₂ * TwistQV_Pm d L W a₂) * ((G s)ᴴ * TwistQV_Pm d L W a₁) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [TwistQV_Pm_mul_self]; simp only [Matrix.mul_assoc]
  have h2 : G s * TwistQV_Pm d L W a₂ * (G s)ᴴ * TwistQV_Pm d L W a₁ =
      (((W : ℂ) ^ d) * ((W : ℂ) ^ d)) • TwistQV_wd G E [(s, a₂), (!s, a₁)] := by
    rw [hPE a₂, hPE a₁, hG]
    simp only [TwistQV_wd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [h1, TwistQV_trace_pow_proj _ _ (TwistQV_Pm_mul_self a₁) hp, h2, smul_pow, Matrix.trace_smul, TwistQV_wd_pow]
  refine (Complex.re_le_norm _).trans ?_
  rw [smul_eq_mul, norm_mul, norm_pow]
  have hn : ‖((W : ℂ) ^ d) * ((W : ℂ) ^ d)‖ = ((W : ℝ) ^ d) * ((W : ℝ) ^ d) := by simp
  rw [hn]
  have hM' := hM ((List.replicate p [(s, a₂), (!s, a₁)]).flatten)
  rw [TwistQV_length_replicate_flatten, List.length_cons, List.length_cons, List.length_nil,
    show p * (0 + 1 + 1) = 2 * p by ring] at hM'
  calc ((W : ℝ) ^ d * (W : ℝ) ^ d) ^ p * ‖(TwistQV_wd G E (List.replicate p [(s, a₂), (!s, a₁)]).flatten).trace‖
      ≤ ((W : ℝ) ^ d * (W : ℝ) ^ d) ^ p * Mx (2 * p) :=
        mul_le_mul_of_nonneg_left hM' (by positivity)
    _ = ((W : ℝ) ^ d) ^ (2 * p) * Mx (2 * p) := by rw [← mul_pow, ← pow_two, ← pow_mul]; ring_nf


/-! ### 2.1 Ward on the diagonal and the Frobenius norms of the blocks -/

/-- `Σ_y |G(s)_{yu}|² = η⁻¹ Im G(+)_{uu}`: Ward's identity `G(-s) G(s) = (2iη)⁻¹ (G(+) - G(-))`, entry `(u, u)`. -/
private lemma TwistQV_ward_diag {Hb : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ} (hH : Hb.IsHermitian)
    (hz : 0 < z.im) (s : Bool) (u : Vtx d L W) :
    ∑ y, ‖Gres Hb z s y u‖ ^ 2 = (z.im)⁻¹ * (Gres Hb z true u u).im := by
  have hw := TwistQV_Gres_ward_left hH hz.ne' s
  have hG : ∀ σ, (Gres Hb z σ)ᴴ = Gres Hb z (!σ) := TwistQV_Gres_conjTranspose hH z
  have e1 : (Gres Hb z (!s) * Gres Hb z s) u u = ((∑ y, ‖Gres Hb z s y u‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.mul_apply]
    push_cast
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← hG s, Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_mul']
  have e2 : (Gres Hb z true - Gres Hb z false) u u = 2 * Complex.I * ((Gres Hb z true u u).im : ℂ) := by
    have h0 : Gres Hb z false = (Gres Hb z true)ᴴ := by simpa using (hG true).symm
    rw [h0, Matrix.sub_apply, Matrix.conjTranspose_apply, Complex.star_def]
    exact TwistQV_sub_conj_eq _
  rw [hw, Matrix.smul_apply, e2, smul_eq_mul] at e1
  have hη : (z.im : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
  have e3 : (2 * Complex.I * (z.im : ℂ))⁻¹ * (2 * Complex.I * ((Gres Hb z true u u).im : ℂ)) =
      (((z.im)⁻¹ * (Gres Hb z true u u).im : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [e3] at e1
  exact_mod_cast e1.symm


/-- The sum over `Vtx` of a block-supported function is the sum over the offsets. -/
private lemma TwistQV_sum_ite {β : Type*} [AddCommMonoid β] (a : Zd d L) (f : Vtx d L W → β) :
    ∑ v : Vtx d L W, (if v.1 = a then f v else 0) = ∑ o : Fin (W ^ d), f (a, o) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp
  · intro a' _ ha'; simp [ha']
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `Σ_o G_{(b,o),(b,o)} = W^d tr(G E_b)`. -/
private lemma TwistQV_diag_blk (G : Matrix (Vtx d L W) (Vtx d L W) ℂ) (b : Zd d L) :
    ∑ o : Fin (W ^ d), G (b, o) (b, o) = ((W : ℂ) ^ d) * (G * Eblk d L W b).trace := by
  have h1 : (G * TwistQV_Pm d L W b).trace = ∑ o : Fin (W ^ d), G (b, o) (b, o) := by
    rw [TwistQV_Pm, Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_diagonal]
    rw [← TwistQV_sum_ite b (fun v => G v v)]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> simp
  rw [← h1, TwistQV_Pm_eq_smul_Eblk, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

/-- `Σ_y Σ_o |G(s)_{y,(b,o)}|² ≤ η⁻¹ W^d M_1` (Ward on the diagonal, then the `1`-loop). -/
private lemma TwistQV_ward_sum {Hb : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ} (hH : Hb.IsHermitian)
    (hz : 0 < z.im) (Mx : ℕ → ℝ)
    (hM : ∀ Lst : List (Bool × Zd d L), ‖(TwistQV_wd (Gres Hb z) (Eblk d L W) Lst).trace‖ ≤ Mx Lst.length)
    (s : Bool) (b : Zd d L) :
    ∑ y, ∑ o : Fin (W ^ d), ‖Gres Hb z s y (b, o)‖ ^ 2 ≤ (z.im)⁻¹ * (((W : ℝ) ^ d) * Mx 1) := by
  rw [Finset.sum_comm]
  simp_rw [TwistQV_ward_diag hH hz s]
  rw [← Finset.mul_sum, ← Complex.im_sum, TwistQV_diag_blk]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hz.le)
  refine (Complex.im_le_norm _).trans ?_
  rw [norm_mul]
  have hW : ‖((W : ℂ) ^ d)‖ = (W : ℝ) ^ d := by simp
  rw [hW]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have := hM [(true, b)]
  simpa [TwistQV_wd_singleton] using this


/-- `Σ_{o,o'} |X_{(a,o),(a,o')}|² = Re tr(P_a X P_a X^*)`. -/
private lemma TwistQV_hsblk (X : Matrix (Vtx d L W) (Vtx d L W) ℂ) (a : Zd d L) :
    ∑ o : Fin (W ^ d), ∑ o' : Fin (W ^ d), ‖X (a, o) (a, o')‖ ^ 2 =
      ((TwistQV_Pm d L W a * X * TwistQV_Pm d L W a * Xᴴ).trace).re := by
  have hY := TwistQV_PGP_apply X a a
  have h0 : ∀ i, (TwistQV_Pm d L W a * X * TwistQV_Pm d L W a * Xᴴ) i i =
      ∑ j, (if i.1 = a then (1 : ℂ) else 0) * X i j * (if j.1 = a then 1 else 0) * star (X i j) := by
    intro i
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hY, Matrix.conjTranspose_apply]
  have h1 : ∀ i j : Vtx d L W, (if i.1 = a then (1 : ℂ) else 0) * X i j * (if j.1 = a then 1 else 0) * star (X i j) =
      if i.1 = a then (if j.1 = a then ((‖X i j‖ ^ 2 : ℝ) : ℂ) else 0) else 0 := by
    intro i j
    by_cases hi : i.1 = a <;> by_cases hj : j.1 = a <;> simp [hi, hj]
    exact Complex.mul_conj' _
  have h : (TwistQV_Pm d L W a * X * TwistQV_Pm d L W a * Xᴴ).trace =
      ((∑ o : Fin (W ^ d), ∑ o' : Fin (W ^ d), ‖X (a, o) (a, o')‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, h0, h1]
    have h2 : ∀ i : Vtx d L W, ∑ j : Vtx d L W, (if i.1 = a then (if j.1 = a then ((‖X i j‖ ^ 2 : ℝ) : ℂ) else 0) else 0) =
        if i.1 = a then ∑ o' : Fin (W ^ d), ((‖X i (a, o')‖ ^ 2 : ℝ) : ℂ) else 0 := by
      intro i
      by_cases hi : i.1 = a
      · simp only [hi, ite_true]
        exact TwistQV_sum_ite a (fun j => ((‖X i j‖ ^ 2 : ℝ) : ℂ))
      · simp [hi]
    simp only [h2]
    rw [TwistQV_sum_ite a (fun i => ∑ o' : Fin (W ^ d), ((‖X i (a, o')‖ ^ 2 : ℝ) : ℂ))]
    push_cast
    rfl
  rw [h, Complex.ofReal_re]


/-- `Σ_{o,o'} |G(s)_{(c,o),(c,o')}|² ≤ (W^d)² M_2` (the `2`-loop `tr(G(s) E_c G(-s) E_c)`). -/
private lemma TwistQV_hsG {Hb : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ} (hH : Hb.IsHermitian) (Mx : ℕ → ℝ)
    (hM : ∀ Lst : List (Bool × Zd d L), ‖(TwistQV_wd (Gres Hb z) (Eblk d L W) Lst).trace‖ ≤ Mx Lst.length)
    (s : Bool) (c : Zd d L) :
    ∑ o : Fin (W ^ d), ∑ o' : Fin (W ^ d), ‖Gres Hb z s (c, o) (c, o')‖ ^ 2 ≤ ((W : ℝ) ^ d) ^ 2 * Mx 2 := by
  rw [TwistQV_hsblk]
  have hG := TwistQV_Gres_conjTranspose hH z
  have hPE : ∀ a, TwistQV_Pm d L W a = ((W : ℂ) ^ d) • Eblk d L W a := fun a => TwistQV_Pm_eq_smul_Eblk a
  have h1 : TwistQV_Pm d L W c * Gres Hb z s * TwistQV_Pm d L W c * (Gres Hb z s)ᴴ =
      (((W : ℂ) ^ d) * ((W : ℂ) ^ d)) • (Eblk d L W c * (Gres Hb z s * Eblk d L W c * Gres Hb z (!s))) := by
    rw [hPE c, hG s]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  have e : (Gres Hb z s * Eblk d L W c * Gres Hb z (!s)) * Eblk d L W c =
      TwistQV_wd (Gres Hb z) (Eblk d L W) [(s, c), (!s, c)] := by
    simp only [TwistQV_wd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Matrix.mul_one,
      Matrix.mul_assoc]
  rw [h1, Matrix.trace_smul, Matrix.trace_mul_comm, e, smul_eq_mul]
  refine (Complex.re_le_norm _).trans ?_
  rw [norm_mul]
  have hn : ‖((W : ℂ) ^ d) * ((W : ℂ) ^ d)‖ = ((W : ℝ) ^ d) * ((W : ℝ) ^ d) := by simp
  rw [hn, ← pow_two]
  exact mul_le_mul_of_nonneg_left (by simpa using hM [(s, c), (!s, c)]) (by positivity)

/-- `Σ_{o,o'} |X_{(c,o),(c,o')}|² ≤ (W^d)⁴ M_4` for `X = G(s) P_b G(s)^*` (the `4`-loop `tr[(G(s) E_b G(-s) E_c)²]`). -/
private lemma TwistQV_hsX {Hb : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ} (hH : Hb.IsHermitian) (Mx : ℕ → ℝ)
    (hM : ∀ Lst : List (Bool × Zd d L), ‖(TwistQV_wd (Gres Hb z) (Eblk d L W) Lst).trace‖ ≤ Mx Lst.length)
    (s : Bool) (b c : Zd d L) :
    ∑ o : Fin (W ^ d), ∑ o' : Fin (W ^ d),
      ‖(Gres Hb z s * TwistQV_Pm d L W b * (Gres Hb z s)ᴴ) (c, o) (c, o')‖ ^ 2 ≤ ((W : ℝ) ^ d) ^ 4 * Mx 4 := by
  rw [TwistQV_hsblk]
  have hG := TwistQV_Gres_conjTranspose hH z
  have hPE : ∀ a, TwistQV_Pm d L W a = ((W : ℂ) ^ d) • Eblk d L W a := fun a => TwistQV_Pm_eq_smul_Eblk a
  have hX : (Gres Hb z s * TwistQV_Pm d L W b * (Gres Hb z s)ᴴ)ᴴ = Gres Hb z s * TwistQV_Pm d L W b * (Gres Hb z s)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, TwistQV_Pm_conjTranspose,
      Matrix.mul_assoc]
  rw [hX]
  have h1 : TwistQV_Pm d L W c * (Gres Hb z s * TwistQV_Pm d L W b * (Gres Hb z s)ᴴ) * TwistQV_Pm d L W c *
      (Gres Hb z s * TwistQV_Pm d L W b * (Gres Hb z s)ᴴ) =
      ((((W : ℂ) ^ d) * ((W : ℂ) ^ d)) * (((W : ℂ) ^ d) * ((W : ℂ) ^ d))) •
        (Eblk d L W c * (Gres Hb z s * Eblk d L W b * Gres Hb z (!s)) * Eblk d L W c *
          (Gres Hb z s * Eblk d L W b * Gres Hb z (!s))) := by
    rw [hPE c, hPE b, hG s]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
    congr 1; ring
  have e : ((Gres Hb z s * Eblk d L W b * Gres Hb z (!s)) * Eblk d L W c) *
      ((Gres Hb z s * Eblk d L W b * Gres Hb z (!s)) * Eblk d L W c) =
      TwistQV_wd (Gres Hb z) (Eblk d L W) (List.replicate 2 [(s, b), (!s, c)]).flatten := by
    rw [← TwistQV_wd_pow]
    simp only [TwistQV_wd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Matrix.mul_one, pow_two,
      Matrix.mul_assoc]
  have e2 : (Eblk d L W c * (Gres Hb z s * Eblk d L W b * Gres Hb z (!s)) * Eblk d L W c *
        (Gres Hb z s * Eblk d L W b * Gres Hb z (!s))).trace =
      (((Gres Hb z s * Eblk d L W b * Gres Hb z (!s)) * Eblk d L W c) *
        ((Gres Hb z s * Eblk d L W b * Gres Hb z (!s)) * Eblk d L W c)).trace := by
    generalize Gres Hb z s * Eblk d L W b * Gres Hb z (!s) = Z
    generalize Eblk d L W c = Ec
    rw [show Ec * Z * Ec * Z = Ec * (Z * Ec * Z) by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [h1, Matrix.trace_smul, e2, e, smul_eq_mul]
  refine (Complex.re_le_norm _).trans ?_
  rw [norm_mul]
  have hn : ‖(((W : ℂ) ^ d) * ((W : ℂ) ^ d)) * (((W : ℂ) ^ d) * ((W : ℂ) ^ d))‖ = ((W : ℝ) ^ d) ^ 4 := by
    simp; ring
  rw [hn]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have := hM (List.replicate 2 [(s, b), (!s, c)]).flatten
  rwa [TwistQV_length_replicate_flatten, List.length_cons, List.length_cons, List.length_nil] at this


/-- Cauchy-Schwarz for a double sum. -/
private lemma TwistQV_cs2 {O : Type*} [Fintype O] (f g : O → O → ℂ) :
    ‖∑ o, ∑ o', f o o' * g o o'‖ ≤ √(∑ o, ∑ o', ‖f o o'‖ ^ 2) * √(∑ o, ∑ o', ‖g o o'‖ ^ 2) := by
  have h1 : ‖∑ o, ∑ o', f o o' * g o o'‖ ≤ ∑ p : O × O, ‖f p.1 p.2‖ * ‖g p.1 p.2‖ := by
    rw [Fintype.sum_prod_type]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun o _ =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun o' _ => (norm_mul _ _).le))
  refine h1.trans ?_
  refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans_eq ?_
  simp only [Fintype.sum_prod_type]

/-- The expansion of `Σ_{y,p} |Σ_o A_{yo} B_{op}|²` along the middle index. -/
private lemma TwistQV_sq_expand {Y O P : Type*} [Fintype Y] [Fintype O] [Fintype P] (A : Y → O → ℂ) (B : O → P → ℂ) :
    ((∑ y, ∑ p, ‖∑ o, A y o * B o p‖ ^ 2 : ℝ) : ℂ) =
      ∑ o, ∑ o', (∑ y, A y o * (starRingEnd ℂ) (A y o')) * (∑ p, B o p * (starRingEnd ℂ) (B o' p)) := by
  push_cast
  have h1 : ∀ y p, ((‖∑ o, A y o * B o p‖ : ℝ) : ℂ) ^ 2 =
      ∑ o, ∑ o', (A y o * B o p) * ((starRingEnd ℂ) (A y o') * (starRingEnd ℂ) (B o' p)) := by
    intro y p
    rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    simp only [map_mul]
  simp only [h1]
  have h2 : ∀ o o', (∑ y, A y o * (starRingEnd ℂ) (A y o')) * (∑ p, B o p * (starRingEnd ℂ) (B o' p)) =
      ∑ y, ∑ p, (A y o * B o p) * ((starRingEnd ℂ) (A y o') * (starRingEnd ℂ) (B o' p)) := by
    intro o o'
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun p _ => ?_
    ring
  simp only [h2]
  calc ∑ y, ∑ p, ∑ o, ∑ o', (A y o * B o p) * ((starRingEnd ℂ) (A y o') * (starRingEnd ℂ) (B o' p))
      = ∑ y, ∑ o, ∑ p, ∑ o', (A y o * B o p) * ((starRingEnd ℂ) (A y o') * (starRingEnd ℂ) (B o' p)) :=
        Finset.sum_congr rfl fun y _ => Finset.sum_comm
    _ = ∑ o, ∑ y, ∑ p, ∑ o', (A y o * B o p) * ((starRingEnd ℂ) (A y o') * (starRingEnd ℂ) (B o' p)) :=
        Finset.sum_comm
    _ = ∑ o, ∑ y, ∑ o', ∑ p, (A y o * B o p) * ((starRingEnd ℂ) (A y o') * (starRingEnd ℂ) (B o' p)) :=
        Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun y _ => Finset.sum_comm
    _ = ∑ o, ∑ o', ∑ y, ∑ p, (A y o * B o p) * ((starRingEnd ℂ) (A y o') * (starRingEnd ℂ) (B o' p)) :=
        Finset.sum_congr rfl fun o _ => Finset.sum_comm


/-- `(G P_b G^*)_{uu'} = Σ_p G_{u,(b,p)} \overline{G_{u',(b,p)}}`. -/
private lemma TwistQV_GPG_apply (G : Matrix (Vtx d L W) (Vtx d L W) ℂ) (b : Zd d L) (u u' : Vtx d L W) :
    (G * TwistQV_Pm d L W b * Gᴴ) u u' = ∑ p : Fin (W ^ d), G u (b, p) * (starRingEnd ℂ) (G u' (b, p)) := by
  rw [Matrix.mul_apply]
  have h : ∀ v : Vtx d L W, (G * TwistQV_Pm d L W b) u v * Gᴴ v u' =
      if v.1 = b then G u v * (starRingEnd ℂ) (G u' v) else 0 := by
    intro v
    rw [TwistQV_Pm, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.star_def]
    by_cases hv : v.1 = b <;> simp [hv]
  simp only [h]
  exact TwistQV_sum_ite b (fun v => G u v * (starRingEnd ℂ) (G u' v))

/-- **The Ward sum of the second chain**:
`Σ_y Σ_o |Σ_{o'} G₂(y,(c₁,o')) G₁((c₂,o'),(b,o))|² ≤ η⁻¹ (W^d)³ (M₂ M₄)^{1/2}`
(Ward `G₂^* G₂ = (2iη)⁻¹ (G(+) - G(-))`, then Cauchy-Schwarz over the pair of offsets, `TwistQV_hsG`, `TwistQV_hsX`). -/
private lemma TwistQV_R2 {Hb : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ} (hH : Hb.IsHermitian) (hz : 0 < z.im)
    (Mx : ℕ → ℝ) (hM0 : ∀ n, 0 ≤ Mx n)
    (hM : ∀ Lst : List (Bool × Zd d L), ‖(TwistQV_wd (Gres Hb z) (Eblk d L W) Lst).trace‖ ≤ Mx Lst.length)
    (s₁ s₂ : Bool) (b c₁ c₂ : Zd d L) :
    ∑ y, ∑ o₁ : Fin (W ^ d), ‖∑ o₂ : Fin (W ^ d), Gres Hb z s₂ y (c₁, o₂) * Gres Hb z s₁ (c₂, o₂) (b, o₁)‖ ^ 2 ≤
      (z.im)⁻¹ * (((W : ℝ) ^ d) ^ 3 * √(Mx 2 * Mx 4)) := by
  have hexp := TwistQV_sq_expand (fun (y : Vtx d L W) (o : Fin (W ^ d)) => Gres Hb z s₂ y (c₁, o))
    (fun (o : Fin (W ^ d)) (p : Fin (W ^ d)) => Gres Hb z s₁ (c₂, o) (b, p))
  have hw := TwistQV_Gres_ward_left hH hz.ne' s₂
  have hG := TwistQV_Gres_conjTranspose hH z
  set c : ℂ := (2 * Complex.I * (z.im : ℂ))⁻¹ with hc
  have hA : ∀ o o' : Fin (W ^ d), ∑ y, Gres Hb z s₂ y (c₁, o) * (starRingEnd ℂ) (Gres Hb z s₂ y (c₁, o')) =
      c * (Gres Hb z true (c₁, o') (c₁, o) - Gres Hb z false (c₁, o') (c₁, o)) := by
    intro o o'
    have h1 := congrFun (congrFun hw (c₁, o')) (c₁, o)
    rw [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Matrix.mul_apply] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← hG s₂, Matrix.conjTranspose_apply, Complex.star_def, mul_comm]
  have hB : ∀ o o' : Fin (W ^ d), ∑ p : Fin (W ^ d), Gres Hb z s₁ (c₂, o) (b, p) * (starRingEnd ℂ) (Gres Hb z s₁ (c₂, o') (b, p)) =
      (Gres Hb z s₁ * TwistQV_Pm d L W b * (Gres Hb z s₁)ᴴ) (c₂, o) (c₂, o') := fun o o' =>
    (TwistQV_GPG_apply _ b _ _).symm
  simp only [hA, hB] at hexp
  set X : Fin (W ^ d) → Fin (W ^ d) → ℂ := fun o o' => (Gres Hb z s₁ * TwistQV_Pm d L W b * (Gres Hb z s₁)ᴴ) (c₂, o) (c₂, o')
    with hXdef
  have hsplit : ∑ o : Fin (W ^ d), ∑ o' : Fin (W ^ d),
      c * (Gres Hb z true (c₁, o') (c₁, o) - Gres Hb z false (c₁, o') (c₁, o)) * X o o' =
        c * ((∑ o, ∑ o', Gres Hb z true (c₁, o') (c₁, o) * X o o') - ∑ o, ∑ o', Gres Hb z false (c₁, o') (c₁, o) * X o o') := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun o' _ => ?_
    ring
  -- the two Cauchy-Schwarz bounds
  have hU : ∀ s : Bool, ∑ o : Fin (W ^ d), ∑ o' : Fin (W ^ d), ‖Gres Hb z s (c₁, o') (c₁, o)‖ ^ 2 ≤ ((W : ℝ) ^ d) ^ 2 * Mx 2 := by
    intro s
    rw [Finset.sum_comm]
    exact TwistQV_hsG hH Mx hM s c₁
  have hV : ∑ o : Fin (W ^ d), ∑ o' : Fin (W ^ d), ‖X o o'‖ ^ 2 ≤ ((W : ℝ) ^ d) ^ 4 * Mx 4 :=
    TwistQV_hsX hH Mx hM s₁ b c₂
  set D : ℝ := (W : ℝ) ^ d with hD
  have hD0 : 0 ≤ D := by positivity
  have hcs : ∀ s : Bool, ‖∑ o, ∑ o', Gres Hb z s (c₁, o') (c₁, o) * X o o'‖ ≤ D ^ 3 * √(Mx 2 * Mx 4) := by
    intro s
    refine (TwistQV_cs2 (fun o o' => Gres Hb z s (c₁, o') (c₁, o)) X).trans ?_
    have h1 : √(∑ o : Fin (W ^ d), ∑ o' : Fin (W ^ d), ‖Gres Hb z s (c₁, o') (c₁, o)‖ ^ 2) ≤ √(D ^ 2 * Mx 2) :=
      Real.sqrt_le_sqrt (hU s)
    have h2 : √(∑ o : Fin (W ^ d), ∑ o' : Fin (W ^ d), ‖X o o'‖ ^ 2) ≤ √(D ^ 4 * Mx 4) := Real.sqrt_le_sqrt hV
    calc _ ≤ √(D ^ 2 * Mx 2) * √(D ^ 4 * Mx 4) := mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = D ^ 3 * √(Mx 2 * Mx 4) := by
          rw [← Real.sqrt_mul (by have := hM0 2; positivity),
            show D ^ 2 * Mx 2 * (D ^ 4 * Mx 4) = (D ^ 3) ^ 2 * (Mx 2 * Mx 4) by ring,
            Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hnc : ‖c‖ = (2 * z.im)⁻¹ := TwistQV_norm_Ward_const hz
  have hfin := TwistQV_norm_ward_trace_le hz hnc (hcs true) (hcs false)
  rw [hsplit] at hexp
  have hR0 : 0 ≤ ∑ y : Vtx d L W, ∑ o₁ : Fin (W ^ d), ‖∑ o₂ : Fin (W ^ d), Gres Hb z s₂ y (c₁, o₂) * Gres Hb z s₁ (c₂, o₂) (b, o₁)‖ ^ 2 :=
    by positivity
  have hnorm := congrArg norm hexp
  rw [Complex.norm_real, Real.norm_of_nonneg hR0] at hnorm
  rw [hnorm]
  exact hfin.trans (le_of_eq (by rw [div_eq_inv_mul]))


/-! ### 2.2 The two chains -/

/-- `W^{2d} (G₁ E_b G₂ P_{c₁c₂} G₁)_{yx}`: the first chain `C₁` of `T.11 (iii)` (`Σ_{z∈[b]} Σ_{w∈[c₁]} G₁(y,z) G₂(z,w) G₁(τw,x)`
in offsets: `w = (c₁,o₂)`, `τw = (c₂,o₂)`). -/
private def TwistQV_CC1 (G₁ G₂ : Matrix (Vtx d L W) (Vtx d L W) ℂ) (b c₁ c₂ : Zd d L) (y x : Vtx d L W) : ℂ :=
  ∑ o₁ : Fin (W ^ d), ∑ o₂ : Fin (W ^ d), G₁ y (b, o₁) * G₂ (b, o₁) (c₁, o₂) * G₁ (c₂, o₂) x

/-- `W^{2d} (G₂ P_{c₁c₂} G₁ E_b G₂)_{yx}`: the second chain `C₂` of `T.11 (iii)`. -/
private def TwistQV_CC2 (G₁ G₂ : Matrix (Vtx d L W) (Vtx d L W) ℂ) (b c₁ c₂ : Zd d L) (y x : Vtx d L W) : ℂ :=
  ∑ o₂ : Fin (W ^ d), ∑ o₁ : Fin (W ^ d), G₂ y (c₁, o₂) * G₁ (c₂, o₂) (b, o₁) * G₂ (b, o₁) x

/-- **The first chain, one row** (`T.11 (iii)`, `C₁`: Cauchy-Schwarz with `‖𝒜_{bb}‖`, the monotonicity `P^*𝒲P ≤ ‖𝒲_{c₁c₁}‖ E_{c₂}`,
then the Schatten bounds `L^{(2q)}`, `L^{(4p)}`): two applications of `TwistQV_rowbound_off`. -/
private lemma TwistQV_chain1_row {Hb : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ} (hH : Hb.IsHermitian) (Mx : ℕ → ℝ)
    (hM : ∀ Lst : List (Bool × Zd d L), ‖(TwistQV_wd (Gres Hb z) (Eblk d L W) Lst).trace‖ ≤ Mx Lst.length)
    (s₁ s₂ : Bool) (b c₁ c₂ : Zd d L) {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hT₁ : 0 ≤ ((W : ℝ) ^ d) ^ (2 * q) * Mx (2 * q))
    (hT₂ : 0 ≤ ((W : ℝ) ^ d) ^ (2 * (2 * p)) * Mx (2 * (2 * p))) (y : Vtx d L W) :
    ∑ o' : Fin (W ^ d), ‖TwistQV_CC1 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y (y.1, o')‖ ^ 2 ≤
      (((W : ℝ) ^ d) ^ (2 * (2 * p)) * Mx (2 * (2 * p))) ^ (((2 * p : ℕ) : ℝ)⁻¹) *
        ((((W : ℝ) ^ d) ^ (2 * q) * Mx (2 * q)) ^ ((q : ℝ)⁻¹) * ∑ o₁ : Fin (W ^ d), ‖Gres Hb z s₁ y (b, o₁)‖ ^ 2) := by
  set R : Fin (W ^ d) → ℂ := fun o₂ => ∑ o₁ : Fin (W ^ d), Gres Hb z s₁ y (b, o₁) * Gres Hb z s₂ (b, o₁) (c₁, o₂) with hR
  have h1 : ∀ o' : Fin (W ^ d), TwistQV_CC1 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y (y.1, o') =
      ∑ o₂ : Fin (W ^ d), R o₂ * Gres Hb z s₁ (c₂, o₂) (y.1, o') := by
    intro o'
    unfold TwistQV_CC1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun o₂ _ => ?_
    rw [hR, Finset.sum_mul]
  simp only [h1]
  have hA := TwistQV_rowbound_off (Gres Hb z s₁) c₂ y.1 (p := 2 * p) (by omega) hT₂ (TwistQV_Tbound hH Mx hM s₁ c₂ y.1 (by omega)) R
  have hB := TwistQV_rowbound_off (Gres Hb z s₂) b c₁ (p := q) hq hT₁ (TwistQV_Tbound hH Mx hM s₂ b c₁ hq)
    (fun o₁ => Gres Hb z s₁ y (b, o₁))
  refine hA.trans ?_
  refine mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg hT₂ _)


/-- **The second chain, one row** (`T.11 (iii)`, `C₂`: the outer chains `G₂ P G₁`, the middle block `(G₂ E_c G₂^*)_{bb}`
bounded by the Schatten norm `L^{(4p)}`): one application of `TwistQV_rowbound_off`. -/
private lemma TwistQV_chain2_row {Hb : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ} (hH : Hb.IsHermitian) (Mx : ℕ → ℝ)
    (hM : ∀ Lst : List (Bool × Zd d L), ‖(TwistQV_wd (Gres Hb z) (Eblk d L W) Lst).trace‖ ≤ Mx Lst.length)
    (s₁ s₂ : Bool) (b c₁ c₂ : Zd d L) {p : ℕ} (hp : 1 ≤ p)
    (hT : 0 ≤ ((W : ℝ) ^ d) ^ (2 * (2 * p)) * Mx (2 * (2 * p))) (y : Vtx d L W) :
    ∑ o' : Fin (W ^ d), ‖TwistQV_CC2 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y (y.1, o')‖ ^ 2 ≤
      (((W : ℝ) ^ d) ^ (2 * (2 * p)) * Mx (2 * (2 * p))) ^ (((2 * p : ℕ) : ℝ)⁻¹) *
        ∑ o₁ : Fin (W ^ d), ‖∑ o₂ : Fin (W ^ d), Gres Hb z s₂ y (c₁, o₂) * Gres Hb z s₁ (c₂, o₂) (b, o₁)‖ ^ 2 := by
  set u : Fin (W ^ d) → ℂ := fun o₁ => ∑ o₂ : Fin (W ^ d), Gres Hb z s₂ y (c₁, o₂) * Gres Hb z s₁ (c₂, o₂) (b, o₁) with hu
  have h1 : ∀ o' : Fin (W ^ d), TwistQV_CC2 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y (y.1, o') =
      ∑ o₁ : Fin (W ^ d), u o₁ * Gres Hb z s₂ (b, o₁) (y.1, o') := by
    intro o'
    unfold TwistQV_CC2
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun o₁ _ => ?_
    rw [hu, Finset.sum_mul]
  simp only [h1]
  exact TwistQV_rowbound_off (Gres Hb z s₂) b y.1 (p := 2 * p) (by omega) hT
    (TwistQV_Tbound hH Mx hM s₂ b y.1 (by omega)) u


/-- `(D^{2k} M)^{1/k} = D² M^{1/k}`. -/
private lemma TwistQV_rpow_conv {D M : ℝ} (hD : 0 ≤ D) (hM : 0 ≤ M) {k : ℕ} (hk : 1 ≤ k) :
    (D ^ (2 * k) * M) ^ ((k : ℝ)⁻¹) = D ^ 2 * M ^ ((k : ℝ)⁻¹) := by
  rw [Real.mul_rpow (by positivity) hM]
  congr 1
  rw [pow_mul D 2 k]
  exact Real.pow_rpow_inv_natCast (by positivity) (by omega)

/-- **The deterministic core of `T.11 (iii)`** (`Q ≤ 2 W^d Σ_c [tr(E_c C₁ E_c C₁^*) + tr(E_c C₂ E_c C₂^*)]`, then `C₁`, `C₂` as in
`TwistQV_chain1_row`, `TwistQV_chain2_row`, the Ward sums `TwistQV_ward_sum`, `TwistQV_R2`): for a Hermitian `Hb` and `Im z = η > 0`,
`Σ_y Σ_{x∈[y]} |C₁(y,x) + C₂(y,x)|² ≤ 2 (W^d)⁵ η⁻¹ [M₁ M_{2q}^{1/q} M_{4p}^{1/(2p)} + M_{4p}^{1/(2p)} (M₂ M₄)^{1/2}]`,
`M_k` any bound of the traces of the words of length `k`. -/
private theorem TwistQV_core {Hb : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ} (hH : Hb.IsHermitian) (hz : 0 < z.im)
    (Mx : ℕ → ℝ) (hM0 : ∀ n, 0 ≤ Mx n)
    (hM : ∀ Lst : List (Bool × Zd d L), ‖(TwistQV_wd (Gres Hb z) (Eblk d L W) Lst).trace‖ ≤ Mx Lst.length)
    (s₁ s₂ : Bool) (b c₁ c₂ : Zd d L) {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ∑ y : Vtx d L W, ∑ x : Vtx d L W,
        (if x.1 = y.1 then ‖TwistQV_CC1 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y x +
          TwistQV_CC2 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y x‖ ^ 2 else 0) ≤
      2 * (((W : ℝ) ^ d) ^ 5 * (z.im)⁻¹ * (Mx 1 * Mx (2 * q) ^ ((q : ℝ)⁻¹) * Mx (4 * p) ^ (1 / (2 * (p : ℝ))) +
        Mx (4 * p) ^ (1 / (2 * (p : ℝ))) * √(Mx 2 * Mx 4))) := by
  set D : ℝ := (W : ℝ) ^ d with hD
  have hD0 : 0 ≤ D := by positivity
  have hT₁ : 0 ≤ D ^ (2 * q) * Mx (2 * q) := mul_nonneg (by positivity) (hM0 _)
  have hT₂ : 0 ≤ D ^ (2 * (2 * p)) * Mx (2 * (2 * p)) := mul_nonneg (by positivity) (hM0 _)
  have hμ₁ : (D ^ (2 * q) * Mx (2 * q)) ^ ((q : ℝ)⁻¹) = D ^ 2 * Mx (2 * q) ^ ((q : ℝ)⁻¹) :=
    TwistQV_rpow_conv hD0 (hM0 _) hq
  have hexp : (((2 * p : ℕ) : ℝ)⁻¹) = 1 / (2 * (p : ℝ)) := by push_cast; rw [one_div]
  have hμ₂ : (D ^ (2 * (2 * p)) * Mx (2 * (2 * p))) ^ (((2 * p : ℕ) : ℝ)⁻¹) =
      D ^ 2 * Mx (4 * p) ^ (1 / (2 * (p : ℝ))) := by
    rw [TwistQV_rpow_conv hD0 (hM0 _) (k := 2 * p) (by omega), hexp, show 2 * (2 * p) = 4 * p by ring]
  set μ₁ : ℝ := D ^ 2 * Mx (2 * q) ^ ((q : ℝ)⁻¹) with hμ₁d
  set μ₂ : ℝ := D ^ 2 * Mx (4 * p) ^ (1 / (2 * (p : ℝ))) with hμ₂d
  have hμ₁0 : 0 ≤ μ₁ := mul_nonneg (by positivity) (Real.rpow_nonneg (hM0 _) _)
  have hμ₂0 : 0 ≤ μ₂ := mul_nonneg (by positivity) (Real.rpow_nonneg (hM0 _) _)
  -- the pointwise splitting
  have hsplit : ∀ y x : Vtx d L W,
      ‖TwistQV_CC1 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y x + TwistQV_CC2 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y x‖ ^ 2 ≤
        2 * ‖TwistQV_CC1 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y x‖ ^ 2 +
          2 * ‖TwistQV_CC2 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y x‖ ^ 2 := by
    intro y x
    have h := norm_add_le (TwistQV_CC1 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y x)
      (TwistQV_CC2 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y x)
    nlinarith [norm_nonneg (TwistQV_CC1 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y x),
      norm_nonneg (TwistQV_CC2 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y x),
      norm_nonneg (TwistQV_CC1 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y x +
        TwistQV_CC2 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y x),
      sq_nonneg (‖TwistQV_CC1 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y x‖ -
        ‖TwistQV_CC2 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y x‖)]
  -- the sums over `x` in the block of `y`
  have hrow : ∀ f : Vtx d L W → ℝ, ∀ y : Vtx d L W,
      ∑ x : Vtx d L W, (if x.1 = y.1 then f x else 0) = ∑ o : Fin (W ^ d), f (y.1, o) :=
    fun f y => TwistQV_sum_ite y.1 f
  -- chain 1
  have hN₁ : ∑ y : Vtx d L W, ∑ o : Fin (W ^ d), ‖TwistQV_CC1 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y (y.1, o)‖ ^ 2 ≤
      D ^ 5 * (z.im)⁻¹ * (Mx 1 * Mx (2 * q) ^ ((q : ℝ)⁻¹) * Mx (4 * p) ^ (1 / (2 * (p : ℝ)))) := by
    calc ∑ y : Vtx d L W, ∑ o : Fin (W ^ d), ‖TwistQV_CC1 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y (y.1, o)‖ ^ 2
        ≤ ∑ y : Vtx d L W, (μ₂ * (μ₁ * ∑ o₁ : Fin (W ^ d), ‖Gres Hb z s₁ y (b, o₁)‖ ^ 2)) := by
          refine Finset.sum_le_sum fun y _ => ?_
          have := TwistQV_chain1_row hH Mx hM s₁ s₂ b c₁ c₂ hp hq hT₁ hT₂ y
          rwa [hμ₁, hμ₂] at this
      _ = μ₂ * (μ₁ * ∑ y : Vtx d L W, ∑ o₁ : Fin (W ^ d), ‖Gres Hb z s₁ y (b, o₁)‖ ^ 2) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ μ₂ * (μ₁ * ((z.im)⁻¹ * (D * Mx 1))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (TwistQV_ward_sum hH hz Mx hM s₁ b) hμ₁0) hμ₂0
      _ = D ^ 5 * (z.im)⁻¹ * (Mx 1 * Mx (2 * q) ^ ((q : ℝ)⁻¹) * Mx (4 * p) ^ (1 / (2 * (p : ℝ)))) := by
          rw [hμ₁d, hμ₂d]; ring
  -- chain 2
  have hN₂ : ∑ y : Vtx d L W, ∑ o : Fin (W ^ d), ‖TwistQV_CC2 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y (y.1, o)‖ ^ 2 ≤
      D ^ 5 * (z.im)⁻¹ * (Mx (4 * p) ^ (1 / (2 * (p : ℝ))) * √(Mx 2 * Mx 4)) := by
    calc ∑ y : Vtx d L W, ∑ o : Fin (W ^ d), ‖TwistQV_CC2 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y (y.1, o)‖ ^ 2
        ≤ ∑ y : Vtx d L W, (μ₂ * ∑ o₁ : Fin (W ^ d),
            ‖∑ o₂ : Fin (W ^ d), Gres Hb z s₂ y (c₁, o₂) * Gres Hb z s₁ (c₂, o₂) (b, o₁)‖ ^ 2) := by
          refine Finset.sum_le_sum fun y _ => ?_
          have := TwistQV_chain2_row hH Mx hM s₁ s₂ b c₁ c₂ hp hT₂ y
          rwa [hμ₂] at this
      _ = μ₂ * ∑ y : Vtx d L W, ∑ o₁ : Fin (W ^ d),
            ‖∑ o₂ : Fin (W ^ d), Gres Hb z s₂ y (c₁, o₂) * Gres Hb z s₁ (c₂, o₂) (b, o₁)‖ ^ 2 := by
          rw [← Finset.mul_sum]
      _ ≤ μ₂ * ((z.im)⁻¹ * (D ^ 3 * √(Mx 2 * Mx 4))) :=
          mul_le_mul_of_nonneg_left (TwistQV_R2 hH hz Mx hM0 hM s₁ s₂ b c₁ c₂) hμ₂0
      _ = D ^ 5 * (z.im)⁻¹ * (Mx (4 * p) ^ (1 / (2 * (p : ℝ))) * √(Mx 2 * Mx 4)) := by
          rw [hμ₂d]; ring
  calc ∑ y : Vtx d L W, ∑ x : Vtx d L W,
        (if x.1 = y.1 then ‖TwistQV_CC1 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y x +
          TwistQV_CC2 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y x‖ ^ 2 else 0)
      ≤ ∑ y : Vtx d L W, ∑ x : Vtx d L W,
        (if x.1 = y.1 then 2 * ‖TwistQV_CC1 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y x‖ ^ 2 +
          2 * ‖TwistQV_CC2 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y x‖ ^ 2 else 0) := by
        refine Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun x _ => ?_
        split_ifs
        · exact hsplit y x
        · exact le_rfl
    _ = ∑ y : Vtx d L W, (2 * ∑ o : Fin (W ^ d), ‖TwistQV_CC1 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y (y.1, o)‖ ^ 2 +
          2 * ∑ o : Fin (W ^ d), ‖TwistQV_CC2 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y (y.1, o)‖ ^ 2) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [hrow (fun x => 2 * ‖TwistQV_CC1 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y x‖ ^ 2 +
          2 * ‖TwistQV_CC2 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y x‖ ^ 2) y]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = 2 * ∑ y : Vtx d L W, ∑ o : Fin (W ^ d), ‖TwistQV_CC1 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y (y.1, o)‖ ^ 2 +
          2 * ∑ y : Vtx d L W, ∑ o : Fin (W ^ d), ‖TwistQV_CC2 (Gres Hb z s₁) (Gres Hb z s₂) b c₁ c₂ y (y.1, o)‖ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (D ^ 5 * (z.im)⁻¹ * (Mx 1 * Mx (2 * q) ^ ((q : ℝ)⁻¹) * Mx (4 * p) ^ (1 / (2 * (p : ℝ))))) +
          2 * (D ^ 5 * (z.im)⁻¹ * (Mx (4 * p) ^ (1 / (2 * (p : ℝ))) * √(Mx 2 * Mx 4))) := by
        gcongr
    _ = _ := by ring


end Core

/-! ## 3. The bridge from the carrier: `twDer`, `twEE` in the offsets of `Vtx` -/

section Bridge

variable {d : ℕ} {sz : Sizes d}

/-- The sum over the block `[b]` of the fine lattice is the sum over the offsets. -/
private lemma TwistQV_sum_blk {β : Type*} [AddCommMonoid β] (n : ℕ) (b : Zd d (sz.L n))
    (F : Idx d (sz.L n) (sz.W n) → β) :
    ∑ z ∈ twBlk n b, F z = ∑ o : Fin ((sz.W n) ^ d), F ((splitEquiv d (sz.L n) (sz.W n)).symm (b, o)) := by
  unfold twBlk
  rw [Finset.sum_filter, ← (Equiv.sum_comp (splitEquiv d (sz.L n) (sz.W n)).symm
    (fun x => if (split d (sz.L n) (sz.W n) x).1 = b then F x else 0))]
  have h : ∀ u : Vtx d (sz.L n) (sz.W n), split d (sz.L n) (sz.W n) ((splitEquiv d (sz.L n) (sz.W n)).symm u) = u :=
    fun u => (splitEquiv d (sz.L n) (sz.W n)).apply_symm_apply u
  simp only [h]
  exact TwistQV_sum_ite b (fun u => F ((splitEquiv d (sz.L n) (sz.W n)).symm u))

/-- `τ_{c}(c', o) = (c, o)` through `splitEquiv`. -/
private lemma TwistQV_shift_symm (n : ℕ) (c a : Zd d (sz.L n)) (o : Fin ((sz.W n) ^ d)) :
    twShift n c ((splitEquiv d (sz.L n) (sz.W n)).symm (a, o)) = (splitEquiv d (sz.L n) (sz.W n)).symm (c, o) := by
  unfold twShift
  have h : split d (sz.L n) (sz.W n) ((splitEquiv d (sz.L n) (sz.W n)).symm (a, o)) = (a, o) :=
    (splitEquiv d (sz.L n) (sz.W n)).apply_symm_apply (a, o)
  rw [h]

/-- `Gres (blockMat M) z σ` read through `splitEquiv.symm` (`Path/LemDecCalEdif.lean:444`, private there). -/
private lemma TwistQV_Gres_blockMat (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (z : ℂ) (s : Bool) :
    Gres (blockMat d (sz.L n) (sz.W n) M) z s =
      (Gres M z s).submatrix (splitEquiv d (sz.L n) (sz.W n)).symm (splitEquiv d (sz.L n) (sz.W n)).symm := by
  unfold Gres
  generalize (if s then z else (starRingEnd ℂ) z) = w
  have h : blockMat d (sz.L n) (sz.W n) M - w • (1 : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ) =
      (M - w • 1).submatrix (splitEquiv d (sz.L n) (sz.W n)).symm (splitEquiv d (sz.L n) (sz.W n)).symm := by
    simp [blockMat, Matrix.submatrix_sub, Matrix.submatrix_smul]
  rw [h, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse, Matrix.inv_submatrix_equiv]


/-- `twChg` of the carrier matrix `G = Gres Hf z true` is `Gres Hf z σ`, read through `splitEquiv` (`Hf` Hermitian). -/
private lemma TwistQV_twChg_vtx {n : ℕ} (C : FlowFM sz) (v : ℝ) (ω : sz.SeqΩ)
    (Hf : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (z : ℂ) (hH : Hf.IsHermitian)
    (hG : ∀ x y, C.G n v ω x y = Gres Hf z true x y) (σ : Bool) (x' y' : Vtx d (sz.L n) (sz.W n)) :
    twChg (C.G n v ω) σ ((splitEquiv d (sz.L n) (sz.W n)).symm x') ((splitEquiv d (sz.L n) (sz.W n)).symm y') =
      Gres (blockMat d (sz.L n) (sz.W n) Hf) z σ x' y' := by
  rw [TwistQV_Gres_blockMat]
  simp only [Matrix.submatrix_apply]
  cases σ
  · simp only [twChg, Bool.false_eq_true, ite_false, hG]
    have h0 : Gres Hf z false = (Gres Hf z true)ᴴ := by
      simpa using (TwistQV_Gres_conjTranspose hH z true).symm
    rw [h0, Matrix.conjTranspose_apply, Complex.star_def]
  · simp [twChg, hG]

/-- **`twDer` in the offsets**: `twDer x y = -(W^{-d})² (C₁(y,x) + C₂(y,x))`, `C₁, C₂ = TwistQV_CC1, TwistQV_CC2` of
`G(σ₁) = Gres (blockMat Hf) z (σ 0)`, `G(σ₂) = Gres (blockMat Hf) z (σ 1)`. -/
private lemma TwistQV_twDer_vtx {n : ℕ} (C : FlowFM sz) (v : ℝ) (ω : sz.SeqΩ)
    (Hf : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (z : ℂ) (hH : Hf.IsHermitian)
    (hG : ∀ x y, C.G n v ω x y = Gres Hf z true x y) (σ : Fin 2 → Bool) (b c₁ c₂ : Zd d (sz.L n))
    (x' y' : Vtx d (sz.L n) (sz.W n)) :
    twDer C n v ω σ b c₁ c₂ ((splitEquiv d (sz.L n) (sz.W n)).symm x') ((splitEquiv d (sz.L n) (sz.W n)).symm y') =
      -((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 *
        (TwistQV_CC1 (Gres (blockMat d (sz.L n) (sz.W n) Hf) z (σ 0)) (Gres (blockMat d (sz.L n) (sz.W n) Hf) z (σ 1)) b c₁ c₂ y' x' +
          TwistQV_CC2 (Gres (blockMat d (sz.L n) (sz.W n) Hf) z (σ 0)) (Gres (blockMat d (sz.L n) (sz.W n) Hf) z (σ 1)) b c₁ c₂ y' x') := by
  unfold twDer TwistQV_CC1 TwistQV_CC2
  simp only [TwistQV_sum_blk, TwistQV_shift_symm, TwistQV_twChg_vtx C v ω Hf z hH hG]


/-- The arithmetic of one term of `twEE`: `w · 1_c · (D conj D)`, `D = -w² Q`, `w = (W^d)⁻¹`. -/
private lemma TwistQV_term (W : ℕ) (d : ℕ) (c : Prop) [Decidable c] (Q : ℂ) :
    ((((W : ℕ) : ℂ) ^ d)⁻¹ * (if c then 1 else 0) *
        ((-((((W : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * Q) * (starRingEnd ℂ) (-((((W : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * Q))) =
      (((((W : ℕ) : ℝ) ^ d)⁻¹ ^ 5 * (if c then ‖Q‖ ^ 2 else 0) : ℝ) : ℂ) := by
  by_cases hc : c
  · simp only [hc, ite_true, mul_one]
    rw [Complex.mul_conj']
    rw [norm_mul, norm_neg, norm_pow, norm_inv, norm_pow, Complex.norm_natCast]
    push_cast
    ring
  · simp [hc]

/-- **`‖twEE b b‖` in the offsets** (`S = 1` at the carrier): `Q(b) = (W^d)⁻⁵ Σ_y Σ_{x ∈ [y]} |C₁(y,x) + C₂(y,x)|²`. -/
private lemma TwistQV_twEE_diag {n : ℕ} (C : FlowFM sz) (v : ℝ) (ω : sz.SeqΩ)
    (Hf : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (z : ℂ) (hH : Hf.IsHermitian)
    (hG : ∀ x y, C.G n v ω x y = Gres Hf z true x y) (hS : C.S n = 1) (σ : Fin 2 → Bool) (b c₁ c₂ : Zd d (sz.L n)) :
    ‖twEE C n v ω σ b b c₁ c₂‖ =
      ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 5 * ∑ y : Vtx d (sz.L n) (sz.W n), ∑ x : Vtx d (sz.L n) (sz.W n),
        (if x.1 = y.1 then ‖TwistQV_CC1 (Gres (blockMat d (sz.L n) (sz.W n) Hf) z (σ 0)) (Gres (blockMat d (sz.L n) (sz.W n) Hf) z (σ 1))
          b c₁ c₂ y x + TwistQV_CC2 (Gres (blockMat d (sz.L n) (sz.W n) Hf) z (σ 0)) (Gres (blockMat d (sz.L n) (sz.W n) Hf) z (σ 1))
            b c₁ c₂ y x‖ ^ 2 else 0) := by
  have hS1 : ∀ a a' : Zd d (sz.L n), C.S n a a' = if a = a' then 1 else 0 := fun a a' => by rw [hS, Matrix.one_apply]
  have hsplit : ∀ u : Vtx d (sz.L n) (sz.W n), split d (sz.L n) (sz.W n) ((splitEquiv d (sz.L n) (sz.W n)).symm u) = u :=
    fun u => (splitEquiv d (sz.L n) (sz.W n)).apply_symm_apply u
  have hconv2 : ∀ F : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ,
      ∑ x, ∑ y, F x y = ∑ x', ∑ y', F ((splitEquiv d (sz.L n) (sz.W n)).symm x') ((splitEquiv d (sz.L n) (sz.W n)).symm y') := by
    intro F
    rw [← Equiv.sum_comp (splitEquiv d (sz.L n) (sz.W n)).symm]
    exact Finset.sum_congr rfl fun x' _ => (Equiv.sum_comp (splitEquiv d (sz.L n) (sz.W n)).symm _).symm
  have hmain : twEE C n v ω σ b b c₁ c₂ = ((((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 5 * ∑ x : Vtx d (sz.L n) (sz.W n),
      ∑ y : Vtx d (sz.L n) (sz.W n),
        (if x.1 = y.1 then ‖TwistQV_CC1 (Gres (blockMat d (sz.L n) (sz.W n) Hf) z (σ 0)) (Gres (blockMat d (sz.L n) (sz.W n) Hf) z (σ 1))
          b c₁ c₂ y x + TwistQV_CC2 (Gres (blockMat d (sz.L n) (sz.W n) Hf) z (σ 0)) (Gres (blockMat d (sz.L n) (sz.W n) Hf) z (σ 1))
            b c₁ c₂ y x‖ ^ 2 else 0) : ℝ) : ℂ) := by
    unfold twEE
    rw [hconv2]
    simp only [hsplit, hS1, TwistQV_twDer_vtx C v ω Hf z hH hG, TwistQV_term]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
  rw [hmain, Complex.norm_real]
  have hR : 0 ≤ ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 5 * ∑ x : Vtx d (sz.L n) (sz.W n), ∑ y : Vtx d (sz.L n) (sz.W n),
      (if x.1 = y.1 then ‖TwistQV_CC1 (Gres (blockMat d (sz.L n) (sz.W n) Hf) z (σ 0)) (Gres (blockMat d (sz.L n) (sz.W n) Hf) z (σ 1))
        b c₁ c₂ y x + TwistQV_CC2 (Gres (blockMat d (sz.L n) (sz.W n) Hf) z (σ 0)) (Gres (blockMat d (sz.L n) (sz.W n) Hf) z (σ 1))
          b c₁ c₂ y x‖ ^ 2 else 0) := by
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_)
    split_ifs <;> positivity
  rw [Real.norm_of_nonneg hR, Finset.sum_comm]

end Bridge

end RBM.BA
