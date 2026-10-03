/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step34Pins
import RBM3D.Hierarchy.ContractionBasic
import RBM3D.Gauss.FlowCalculus

/-!
# S3-02 (ticket T2054): the contraction inequality `STContract`

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`), Lemma `ygdhmsgq`
(`3_5:918-1000`): `(yi2oslxj2)`, `(u2jzooi-2)`; `eq:CS1` `3_5:936`, `eq;genWard0/1`
`3_5:950-955`, `defC=GEG` `3_5:970`, `eq:Apsipsi1` `3_5:985`.  New at `d ≥ 3`: no RBM2D source.

The proof is deterministic: it uses only a Hermitian `H`, `Im z = η > 0`, and `E_a = W^{-d} P_a`
with `P_a` the diagonal projection onto the block `a`.  The statement is independent of `d`, `L`
and `W` except through `W^d`; `3 ≤ d` is not used.

* §1 the Hilbert-Schmidt norm `hs`, the Cauchy-Schwarz bound `|tr(A B)| ≤ ‖A‖_HS ‖B‖_HS`, and the
  quadratic-form bound `⟨v, B v⟩^p ≤ ‖v‖^{2p} tr(B^p)` for `B ⪰ 0` (spectral theorem), which gives
  `|Σ_{s,t} ρ_s A_{st} τ_t| ≤ ‖ρ‖ ‖τ‖ tr[(A A^*)^p]^{1/(2p)}` (`eq:Apsipsi1`);
* §2 the adjoint `G(σ)^* = G(-σ)` and Ward's identity `G(-σ) G(σ) = (2 i η)⁻¹ (G(+) - G(-))`;
* §3 words `wd l = ∏ G(σ_i) E_{a_i}`, their reflections `Ref`, and the Ward reductions of
  `X E X^*` and `E Y Y^*` to two words of length `2k - 1` resp. `2m - 2k - 1` (`eq;genWard1`);
* §4 projections: `Σ_x ‖P_x X P_q‖²_HS = tr(X P_q X^*)`, and the matrix forms of the two parts
  of the pin (`eq:CS1`, `eq;genWard0`, `eq:Apsipsi`);
* §5 splitting the list of a loop at `a_k`, `a_l`, `a_n`;
* §6 the loop matrices on `Vtx d L W`: `P_a = W^d E_a`, and parts (1) and (2) at the matrix level;
* §7 `STLI`, `STmaxL` as words, and `stContract_holds`; §8 compiled instances at `d = 3`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace RBM.Gauss.Sizes

/-! ## 1. Hilbert-Schmidt Cauchy-Schwarz and the power-trace bound -/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `‖A‖_{HS}² = Σ_{ij} |A_{ij}|²`. -/
private def hs (A : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

private lemma hs_nonneg (A : Matrix ι ι ℂ) : 0 ≤ hs A := by
  unfold hs; positivity

private lemma trace_mul_conjTranspose_eq (A : Matrix ι ι ℂ) :
    (A * Aᴴ).trace = (hs A : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, hs]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj']

private lemma norm_trace_mul_le (A B : Matrix ι ι ℂ) :
    ‖(A * B).trace‖ ≤ √(hs A) * √(hs B) := by
  have h1 : ‖(A * B).trace‖ ≤ ∑ p : ι × ι, ‖A p.1 p.2‖ * ‖B p.2 p.1‖ := by
    rw [Fintype.sum_prod_type]
    calc ‖(A * B).trace‖ = ‖∑ i, ∑ j, A i j * B j i‖ := by
          simp [Matrix.trace, Matrix.mul_apply]
      _ ≤ ∑ i, ‖∑ j, A i j * B j i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ∑ j, ‖A i j * B j i‖ := Finset.sum_le_sum fun i _ => norm_sum_le _ _
      _ = _ := by simp
  refine h1.trans ?_
  refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans_eq ?_
  congr 2
  · unfold hs; rw [Fintype.sum_prod_type]
  · unfold hs; rw [Fintype.sum_prod_type, Finset.sum_comm]


/-- real inequality -/
private lemma sum_mul_pow_le (lam w : ι → ℝ) (hl : ∀ i, 0 ≤ lam i) (hw : ∀ i, 0 ≤ w i) {p : ℕ}
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


private lemma psd_quad_pow_le {B : Matrix ι ι ℂ} (hB : B.PosSemidef) (v : ι → ℂ) {p : ℕ}
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
  exact sum_mul_pow_le lam (fun i => ‖y i‖ ^ 2) hl0 (fun i => by positivity) hp

/-- `Σ_t |Σ_s ρ_s A_{st}|² = ⟨v, A Aᴴ v⟩` with `v = conj ρ`. -/
private lemma sum_norm_sq_vecMul (A : Matrix ι ι ℂ) (ρ : ι → ℂ) :
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
private lemma rowbound_of_pow (A : Matrix ι ι ℂ) {p : ℕ} (hp : 1 ≤ p) {T : ℝ} (hT0 : 0 ≤ T)
    (hT : (((A * Aᴴ) ^ p).trace).re ≤ T) (ρ : ι → ℂ) :
    ∑ t, ‖∑ s, ρ s * A s t‖ ^ 2 ≤ T ^ ((p : ℝ)⁻¹) * ∑ s, ‖ρ s‖ ^ 2 := by
  have hpos := Matrix.posSemidef_self_mul_conjTranspose A
  have hb := psd_quad_pow_le hpos (star ρ) hp
  rw [← sum_norm_sq_vecMul] at hb
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

/-- `hs (S A) ≤ μ hs S` when `μ` bounds the quadratic form `ρ ↦ ‖ρᵀ A‖²`. -/
private lemma hs_mul_le {A : Matrix ι ι ℂ} {μ : ℝ}
    (hμ : ∀ ρ : ι → ℂ, ∑ t, ‖∑ s, ρ s * A s t‖ ^ 2 ≤ μ * ∑ s, ‖ρ s‖ ^ 2) (S : Matrix ι ι ℂ) :
    hs (S * A) ≤ μ * hs S := by
  unfold hs
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun u _ => ?_
  have := hμ (fun s => S u s)
  simpa [Matrix.mul_apply] using this

/-- **The bilinear Cauchy-Schwarz bound** `|tr(S₁ A S₂)| ≤ √μ ‖S₁‖_{HS} ‖S₂‖_{HS}`
(`eq:Apsipsi`, `3_5:980`, with `μ` the squared operator norm of `A`). -/
private lemma norm_trace_mul_mul_le {A : Matrix ι ι ℂ} {μ : ℝ} (hμ0 : 0 ≤ μ)
    (hμ : ∀ ρ : ι → ℂ, ∑ t, ‖∑ s, ρ s * A s t‖ ^ 2 ≤ μ * ∑ s, ‖ρ s‖ ^ 2) (S₁ S₂ : Matrix ι ι ℂ) :
    ‖(S₁ * A * S₂).trace‖ ≤ √μ * √(hs S₁) * √(hs S₂) := by
  refine (norm_trace_mul_le (S₁ * A) S₂).trans ?_
  have h := hs_mul_le hμ S₁
  calc √(hs (S₁ * A)) * √(hs S₂) ≤ √(μ * hs S₁) * √(hs S₂) := by gcongr
    _ = _ := by rw [Real.sqrt_mul hμ0]

end Generic


/-! ## 2. The resolvent: adjoint and Ward identity -/

section Resolvent

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `G(σ)^* = G(-σ)` for Hermitian `H` (`Gres`, `GLoopFlow.lean:74`). -/
private lemma Gres_conjTranspose {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (z : ℂ) (σ : Bool) :
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
private lemma Gres_sub {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
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
private lemma sub_conj_eq (z : ℂ) : z - (starRingEnd ℂ) z = 2 * Complex.I * (z.im : ℂ) := by
  rw [Complex.sub_conj]; push_cast; ring

/-- `G(-σ) G(σ) = (2 i η)⁻¹ (G(+) - G(-))`: the Ward identity used for the two ends of a loop
(the algebraic identity `(eq_Ward0)`, `1_2:1018`, behind `(WI_calL)`, `1_2:1036`, used at
`3_5:954`). -/
private lemma Gres_ward_left {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (σ : Bool) :
    Gres H z (!σ) * Gres H z σ = (2 * Complex.I * (z.im : ℂ))⁻¹ • (Gres H z true - Gres H z false) := by
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

/-- `G(σ) G(-σ) = (2 i η)⁻¹ (G(+) - G(-))` (both orders agree: `G(+)` and `G(-)` commute). -/
private lemma Gres_ward_right {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (σ : Bool) :
    Gres H z σ * Gres H z (!σ) = (2 * Complex.I * (z.im : ℂ))⁻¹ • (Gres H z true - Gres H z false) := by
  have := Gres_ward_left hH hz (!σ)
  simpa using this

end Resolvent


/-! ## 3. Words `∏ G(σ_i) E_{a_i}` and their reflections (`eq:CS1`, `eq;genWard1`) -/

section Words

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] (G : Bool → Matrix ι ι ℂ) (E : κ → Matrix ι ι ℂ)

/-- The product `G(σ_1) E_{a_1} ⋯ G(σ_n) E_{a_n}` of a list of pairs `(σ_i, a_i)`. -/
private def wd (l : List (Bool × κ)) : Matrix ι ι ℂ := (l.map fun p => G p.1 * E p.2).prod

@[simp] private lemma wd_nil : wd G E [] = 1 := by simp [wd]

@[simp] private lemma wd_cons (p : Bool × κ) (l : List (Bool × κ)) :
    wd G E (p :: l) = (G p.1 * E p.2) * wd G E l := by simp [wd]

private lemma wd_append (l₁ l₂ : List (Bool × κ)) :
    wd G E (l₁ ++ l₂) = wd G E l₁ * wd G E l₂ := by simp [wd]

@[simp] private lemma wd_singleton (p : Bool × κ) : wd G E [p] = G p.1 * E p.2 := by simp [wd]

/-- The reflected list, `Ref c [] e = c e` and `Ref c (p :: ls) e = (p :: Ref c ls a_p) ++ [(-σ_p, e)]`:
each pair `p = (σ_p, a_p)` goes round the core `c` and returns as `(-σ_p, ·)`, the label of the
return being the label of the pair outside it (`e` for the outermost one); these are the lists
`𝐚'_1`, `𝛔_1^±` and `𝐚'_2`, `𝛔_2^±` of `eq;genWard1`. -/
private def Ref (c : κ → List (Bool × κ)) : List (Bool × κ) → κ → List (Bool × κ)
  | [], e => c e
  | p :: ls, e => (p :: Ref c ls p.2) ++ [(!p.1, e)]

private lemma Ref_length (c : κ → List (Bool × κ)) (n₀ : ℕ) (hc : ∀ e, (c e).length = n₀) :
    ∀ (ls : List (Bool × κ)) (e : κ), (Ref c ls e).length = 2 * ls.length + n₀ := by
  intro ls
  induction ls with
  | nil => intro e; simpa [Ref] using hc e
  | cons p ls ih => intro e; simp [Ref, ih]; omega

/-- `wd (Ref c ls e) = wd ls · K · (wd ls)^* · E_e` when `wd (c e) = K E_e`. -/
private lemma wd_Ref (hG : ∀ σ, (G σ)ᴴ = G (!σ)) (hE : ∀ a, (E a)ᴴ = E a)
    (c : κ → List (Bool × κ)) (K : Matrix ι ι ℂ) (hc : ∀ e, wd G E (c e) = K * E e) :
    ∀ (ls : List (Bool × κ)) (e : κ),
      wd G E (Ref c ls e) = wd G E ls * K * (wd G E ls)ᴴ * E e := by
  intro ls
  induction ls with
  | nil => intro e; simp [Ref, hc]
  | cons p ls ih =>
    intro e
    rw [Ref, wd_append, wd_cons, ih p.2, wd_singleton, wd_cons, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hE, hG]
    simp only [Matrix.mul_assoc]

/-- **Ward reduction of `X E_k X^*`** (`eq;genWard1`, first identity): for `X = wd l · G(σ_k)`,
`tr(X E_{a_k} X^*) = c (tr 𝓛^{(2k-1)}_{+} - tr 𝓛^{(2k-1)}_{-})`, `c = (2 i η)⁻¹`, with two words of
length `2 |l| + 1 = 2k - 1`. -/
private lemma trace_reflect_X (hG : ∀ σ, (G σ)ᴴ = G (!σ)) (hE : ∀ a, (E a)ᴴ = E a) (c : ℂ)
    (hw : ∀ σ, G (!σ) * G σ = c • (G true - G false)) (l : List (Bool × κ)) (q : Bool × κ) :
    ∃ L₁ L₂ : List (Bool × κ), L₁.length = 2 * l.length + 1 ∧ L₂.length = 2 * l.length + 1 ∧
      (wd G E l * (G q.1 * E q.2 * G (!q.1)) * (wd G E l)ᴴ).trace =
        c * ((wd G E L₁).trace - (wd G E L₂).trace) := by
  cases l with
  | nil =>
    refine ⟨[(true, q.2)], [(false, q.2)], by simp, by simp, ?_⟩
    have h1 : (G q.1 * E q.2 * G (!q.1)).trace = (G (!q.1) * (G q.1 * E q.2)).trace :=
      Matrix.trace_mul_comm _ _
    simp only [wd_nil, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one, h1,
      ← Matrix.mul_assoc, hw, wd_singleton, Matrix.smul_mul, Matrix.sub_mul, Matrix.trace_smul,
      Matrix.trace_sub, smul_eq_mul]
  | cons p l₂ =>
    set cc : κ → List (Bool × κ) := fun e => [q, (!q.1, e)] with hcc
    have hc : ∀ e, wd G E (cc e) = (G q.1 * E q.2 * G (!q.1)) * E e := by
      intro e; simp [hcc, wd, Matrix.mul_assoc]
    have hR := wd_Ref G E hG hE cc _ hc l₂
    have hlen : ∀ e, (Ref cc l₂ e).length = 2 * l₂.length + 2 := fun e =>
      Ref_length cc 2 (fun e => by simp [hcc]) l₂ e
    refine ⟨(true, p.2) :: Ref cc l₂ p.2, (false, p.2) :: Ref cc l₂ p.2, by simp [hlen]; omega,
      by simp [hlen]; omega, ?_⟩
    set S : Matrix ι ι ℂ := wd G E l₂ * (G q.1 * E q.2 * G (!q.1)) * (wd G E l₂)ᴴ with hS
    have hlhs : wd G E (p :: l₂) * (G q.1 * E q.2 * G (!q.1)) * (wd G E (p :: l₂))ᴴ =
        G p.1 * (E p.2 * S * E p.2) * G (!p.1) := by
      rw [wd_cons, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hE, hG, hS]
      simp only [Matrix.mul_assoc]
    have hb : ∀ b : Bool, (wd G E ((b, p.2) :: Ref cc l₂ p.2)).trace =
        (G b * (E p.2 * S * E p.2)).trace := by
      intro b
      rw [wd_cons, hR p.2, hS]
      simp only [Matrix.mul_assoc]
    rw [hlhs, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hw, hb, hb]
    simp only [Matrix.smul_mul, Matrix.sub_mul, Matrix.trace_smul, Matrix.trace_sub, smul_eq_mul]

/-- **Ward reduction of `E_e Y Y^*`** (`eq;genWard1`, second identity): for `Y = wd r · G(s)`,
`tr(E_e Y Y^*) = c (tr 𝓛^{(2m-2k-1)}_{+} - tr 𝓛^{(2m-2k-1)}_{-})` with two words of length
`2 |r| + 1`. -/
private lemma trace_reflect_Y (hG : ∀ σ, (G σ)ᴴ = G (!σ)) (hE : ∀ a, (E a)ᴴ = E a) (c : ℂ)
    (hw : ∀ σ, G σ * G (!σ) = c • (G true - G false)) (r : List (Bool × κ)) (s : Bool) (e : κ) :
    ∃ L₁ L₂ : List (Bool × κ), L₁.length = 2 * r.length + 1 ∧ L₂.length = 2 * r.length + 1 ∧
      (E e * (wd G E r * (G s * G (!s)) * (wd G E r)ᴴ)).trace =
        c * ((wd G E L₁).trace - (wd G E L₂).trace) := by
  set cb : Bool → κ → List (Bool × κ) := fun b e => [(b, e)] with hcb
  have hc : ∀ b e, wd G E (cb b e) = G b * E e := by intro b e; simp [hcb]
  have hR : ∀ b, wd G E (Ref (cb b) r e) = wd G E r * G b * (wd G E r)ᴴ * E e :=
    fun b => wd_Ref G E hG hE (cb b) (G b) (hc b) r e
  have hlen : ∀ b, (Ref (cb b) r e).length = 2 * r.length + 1 := fun b =>
    Ref_length (cb b) 1 (fun e => by simp [hcb]) r e
  refine ⟨Ref (cb true) r e, Ref (cb false) r e, hlen true, hlen false, ?_⟩
  rw [hR, hR, ← Matrix.trace_sub, show ∀ x : ℂ, c * x = c • x from fun x => rfl,
    ← Matrix.trace_smul, Matrix.trace_mul_comm, hw s]
  congr 1
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, smul_sub]

/-- `(wd l)^p` is the word of `p` copies of `l`: the loop of length `p |l|` in `eq:Apsipsi1`. -/
private lemma wd_pow (l : List (Bool × κ)) (p : ℕ) :
    (wd G E l) ^ p = wd G E ((List.replicate p l).flatten) := by
  induction p with
  | zero => simp
  | succ p ih => rw [pow_succ', ih, List.replicate_succ, List.flatten_cons, wd_append]

private lemma length_replicate_flatten {α : Type*} (l : List α) (p : ℕ) :
    ((List.replicate p l).flatten).length = p * l.length := by
  simp [List.length_flatten, List.map_replicate, List.sum_replicate]

end Words

/-! ## 4. Block projections and the Cauchy-Schwarz sums over the endpoint label -/

section Projections

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] (P : κ → Matrix ι ι ℂ)
  (hPh : ∀ a, (P a)ᴴ = P a) (hPP : ∀ a, P a * P a = P a) (hP1 : ∑ a, P a = 1)

include hPh hPP

omit [Fintype κ] in
/-- `‖P_a X P_b‖²_{HS} = tr(P_a X P_b X^*)`. -/
private lemma hs_proj (a b : κ) (X : Matrix ι ι ℂ) :
    (hs (P a * X * P b) : ℂ) = (P a * X * P b * Xᴴ).trace := by
  rw [← trace_mul_conjTranspose_eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hPh, hPh]
  have h1 : P a * X * P b * (P b * (Xᴴ * P a)) = P a * X * P b * Xᴴ * P a := by
    calc P a * X * P b * (P b * (Xᴴ * P a)) = P a * X * (P b * P b) * (Xᴴ * P a) := by
          simp only [Matrix.mul_assoc]
      _ = P a * X * P b * (Xᴴ * P a) := by rw [hPP]
      _ = _ := by simp only [Matrix.mul_assoc]
  have h2 : P a * (P a * X * P b) = P a * X * P b := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP]
  rw [h1, Matrix.trace_mul_comm (P a * X * P b * Xᴴ) (P a), ← Matrix.mul_assoc, h2]

include hP1 in
/-- `Σ_a ‖P_a X P_b‖²_{HS} = tr(X P_b X^*)` (`Σ_a P_a = 1`; the sum over `a_n` of `eq;genWard0`). -/
private lemma sum_hs_proj_left (b : κ) (X : Matrix ι ι ℂ) :
    ∑ a, hs (P a * X * P b) = ((X * P b * Xᴴ).trace).re := by
  have h : ((∑ a, hs (P a * X * P b) : ℝ) : ℂ) = (X * P b * Xᴴ).trace := by
    push_cast
    simp only [hs_proj P hPh hPP]
    rw [← Matrix.trace_sum]
    congr 1
    simp only [← Finset.sum_mul]
    rw [hP1, Matrix.one_mul]
  rw [← h, Complex.ofReal_re]

include hP1 in
/-- `Σ_b ‖P_a Y P_b‖²_{HS} = tr(P_a Y Y^*)`. -/
private lemma sum_hs_proj_right (a : κ) (Y : Matrix ι ι ℂ) :
    ∑ b, hs (P a * Y * P b) = ((P a * (Y * Yᴴ)).trace).re := by
  have h : ((∑ b, hs (P a * Y * P b) : ℝ) : ℂ) = (P a * (Y * Yᴴ)).trace := by
    push_cast
    simp only [hs_proj P hPh hPP]
    rw [← Matrix.trace_sum]
    congr 1
    have : ∀ b, P a * Y * P b * Yᴴ = P a * Y * (P b * Yᴴ) := fun b => by
      simp only [Matrix.mul_assoc]
    simp only [this, ← Finset.mul_sum]
    rw [← Finset.sum_mul, hP1, Matrix.one_mul, Matrix.mul_assoc]
  rw [← h, Complex.ofReal_re]

end Projections

section Core

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] (P : κ → Matrix ι ι ℂ)
  (hPh : ∀ a, (P a)ᴴ = P a) (hPP : ∀ a, P a * P a = P a) (hP1 : ∑ a, P a = 1)

omit [Fintype κ] in
private lemma trace_proj_sandwich (hPP : ∀ a, P a * P a = P a) (a : κ) (M : Matrix ι ι ℂ) :
    (P a * M * P a).trace = (P a * M).trace := by
  rw [Matrix.trace_mul_comm (P a * M) (P a), ← Matrix.mul_assoc, hPP]

omit [Fintype κ] in
/-- `tr((P D P)^p) = tr((D P)^p)` for an idempotent `P` and `p ≥ 1`. -/
private lemma trace_pow_proj {ι : Type*} [Fintype ι] [DecidableEq ι] (P D : Matrix ι ι ℂ)
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

include hPh hPP hP1

/-- **Part (1), matrix form** (`eq:CS1`, `eq;genWard0`): `Σ_x |tr(P_x X P_q Y)| ≤
(‖tr X P_q X^*‖ ‖tr P_q Y Y^*‖)^{1/2}`. -/
private lemma core1 (X Y : Matrix ι ι ℂ) (q : κ) {Mα Mβ : ℝ}
    (hα : ‖(X * P q * Xᴴ).trace‖ ≤ Mα) (hβ : ‖(P q * (Y * Yᴴ)).trace‖ ≤ Mβ) :
    ∑ x, ‖(P x * X * P q * Y).trace‖ ≤ √Mα * √Mβ := by
  have h1 : ∀ x, ‖(P x * X * P q * Y).trace‖ ≤ √(hs (P x * X * P q)) * √(hs (P q * Y * P x)) := by
    intro x
    have h : (P x * X * P q) * (P q * Y * P x) = P x * (X * P q * Y) * P x := by
      calc (P x * X * P q) * (P q * Y * P x) = P x * X * (P q * P q) * Y * P x := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hPP]; simp only [Matrix.mul_assoc]
    have h' : (P x * X * P q * Y).trace = ((P x * X * P q) * (P q * Y * P x)).trace := by
      rw [h, trace_proj_sandwich P hPP]
      simp only [Matrix.mul_assoc]
    rw [h']
    exact norm_trace_mul_le _ _
  calc ∑ x, ‖(P x * X * P q * Y).trace‖
      ≤ ∑ x, √(hs (P x * X * P q)) * √(hs (P q * Y * P x)) := Finset.sum_le_sum fun x _ => h1 x
    _ ≤ √(∑ x, hs (P x * X * P q)) * √(∑ x, hs (P q * Y * P x)) :=
        Real.sum_sqrt_mul_sqrt_le _ (fun x => hs_nonneg _) (fun x => hs_nonneg _)
    _ ≤ √Mα * √Mβ := by
        rw [sum_hs_proj_left P hPh hPP hP1, sum_hs_proj_right P hPh hPP hP1]
        gcongr
        · exact (Complex.re_le_norm _).trans hα
        · exact (Complex.re_le_norm _).trans hβ

/-- **Part (2), matrix form** (`eq:Apsipsi`, then Cauchy-Schwarz over `(a_n, x_n)`):
`Σ_x Σ_{y ∈ 𝒜(x)} |tr(P_x X₁ P_q X₂(y) P_{q₂} X₃)| ≤ C √μ (Mα Mβ)^{1/2}`, where `μ` bounds the
quadratic form of `A_y A_y^*`, `A_y = P_q X₂(y) P_{q₂}`. -/
private lemma core2 (X₁ X₃ : Matrix ι ι ℂ) (X₂ : κ → Matrix ι ι ℂ) (q q₂ : κ) {μ Mα Mβ : ℝ}
    (hμ0 : 0 ≤ μ)
    (hμ : ∀ (y : κ) (ρ : ι → ℂ), ∑ t, ‖∑ s, ρ s * (P q * X₂ y * P q₂) s t‖ ^ 2 ≤
      μ * ∑ s, ‖ρ s‖ ^ 2)
    (hα : ‖(X₁ * P q * X₁ᴴ).trace‖ ≤ Mα) (hβ : ‖(P q₂ * (X₃ * X₃ᴴ)).trace‖ ≤ Mβ)
    {C : ℝ} (hC : 0 ≤ C) (𝒜 : κ → Finset κ) (hcard : ∀ x, ((𝒜 x).card : ℝ) ≤ C) :
    ∑ x, ∑ y ∈ 𝒜 x, ‖(P x * X₁ * P q * X₂ y * P q₂ * X₃).trace‖ ≤
      C * (√μ * (√Mα * √Mβ)) := by
  set φ : κ → ℝ := fun x => √μ * (√(hs (P x * X₁ * P q)) * √(hs (P q₂ * X₃ * P x))) with hφ
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => by positivity
  have h1 : ∀ x y, ‖(P x * X₁ * P q * X₂ y * P q₂ * X₃).trace‖ ≤ φ x := by
    intro x y
    have h := norm_trace_mul_mul_le hμ0 (hμ y) (P x * X₁ * P q) (P q₂ * X₃ * P x)
    have h2 : (P x * X₁ * P q) * (P q * X₂ y * P q₂) * (P q₂ * X₃ * P x) =
        P x * (X₁ * P q * X₂ y * P q₂ * X₃) * P x := by
      calc (P x * X₁ * P q) * (P q * X₂ y * P q₂) * (P q₂ * X₃ * P x)
          = P x * X₁ * (P q * P q) * X₂ y * (P q₂ * P q₂) * X₃ * P x := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hPP, hPP]; simp only [Matrix.mul_assoc]
    have h3 : (P x * X₁ * P q * X₂ y * P q₂ * X₃).trace =
        ((P x * X₁ * P q) * (P q * X₂ y * P q₂) * (P q₂ * X₃ * P x)).trace := by
      rw [h2, trace_proj_sandwich P hPP]
      simp only [Matrix.mul_assoc]
    rw [h3]
    calc _ ≤ _ := h
      _ = φ x := by rw [hφ]; ring
  calc ∑ x, ∑ y ∈ 𝒜 x, ‖(P x * X₁ * P q * X₂ y * P q₂ * X₃).trace‖
      ≤ ∑ x, ∑ y ∈ 𝒜 x, φ x := Finset.sum_le_sum fun x _ =>
        Finset.sum_le_sum fun y _ => h1 x y
    _ = ∑ x, ((𝒜 x).card : ℝ) * φ x := by simp
    _ ≤ ∑ x, C * φ x := Finset.sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_right (hcard x) (hφ0 x)
    _ = C * ∑ x, φ x := by rw [Finset.mul_sum]
    _ ≤ C * (√μ * (√Mα * √Mβ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        rw [hφ, ← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        refine (Real.sum_sqrt_mul_sqrt_le _ (fun x => hs_nonneg _) (fun x => hs_nonneg _)).trans ?_
        rw [sum_hs_proj_left P hPh hPP hP1, sum_hs_proj_right P hPh hPP hP1]
        gcongr
        · exact (Complex.re_le_norm _).trans hα
        · exact (Complex.re_le_norm _).trans hβ

end Core


/-! ## 5. Splitting the list of a loop at `a_k`, `a_l`, `a_n` -/

section Lists

/-- Part (1): `σ.zip (a ++ [x]) = l ++ [q] ++ r ++ [(s, x)]`, the pieces independent of `x`
(the split of the loop at `a_k` and at the endpoint `a_n`). -/
private lemma list_split1 {α : Type*} {m k : ℕ} (hk : 1 ≤ k) (hkm : k + 1 ≤ m) (σl : List Bool)
    (hσ : σl.length = m) (al : List α) (ha : al.length = m - 1) :
    ∃ (l : List (Bool × α)) (q : Bool × α) (r : List (Bool × α)) (s : Bool),
      l.length = k - 1 ∧ r.length = m - k - 1 ∧
      ∀ x : α, σl.zip (al ++ [x]) = l ++ [q] ++ r ++ [(s, x)] := by
  have hne : σl ≠ [] := by
    intro h; subst h; simp at hσ; omega
  set σ' := σl.dropLast with hσ'
  set s := σl.getLast hne with hs
  have hσl : σl = σ' ++ [s] := (List.dropLast_append_getLast hne).symm
  have hlen' : σ'.length = al.length := by simp [hσ', List.length_dropLast, hσ, ha]
  set Z := σ'.zip al with hZ
  have hZlen : Z.length = m - 1 := by simp [hZ, hlen', ha]
  have hx : ∀ x : α, σl.zip (al ++ [x]) = Z ++ [(s, x)] := by
    intro x; rw [hσl, List.zip_append hlen']; simp [hZ]
  obtain ⟨l, q, hlq⟩ : ∃ l q, Z.take k = l ++ [q] := by
    rcases List.eq_nil_or_concat' (Z.take k) with h | ⟨L, b, h⟩
    · exfalso
      have := congrArg List.length h
      simp [hZlen] at this; omega
    · exact ⟨L, b, h⟩
  have hl : l.length = k - 1 := by
    have := congrArg List.length hlq
    simp [hZlen] at this; omega
  refine ⟨l, q, Z.drop k, s, hl, by simp [hZlen]; omega, ?_⟩
  intro x
  rw [hx, ← hlq, List.take_append_drop]

/-- One varying entry: `Z₀.set j z` splits at `k ≤ j < l'` into pieces not depending on `z`. -/
private lemma split_set {β : Type*} (Z₀ : List β) {j k l' : ℕ} (hk : 1 ≤ k) (hkj : k ≤ j)
    (hjl : j < l') (hl' : l' < Z₀.length) :
    ∃ (l₁ : List β) (q : β) (pre₂ post₁ : List β) (q₂ : β) (r₃ : List β),
      l₁.length = k - 1 ∧ pre₂.length = j - k ∧ post₁.length = l' - j - 1 ∧
      r₃.length = Z₀.length - l' - 1 ∧
      ∀ z : β, Z₀.set j z = l₁ ++ [q] ++ pre₂ ++ [z] ++ post₁ ++ [q₂] ++ r₃ := by
  have hj : j < Z₀.length := by omega
  set pre := Z₀.take j with hpre
  set post := Z₀.drop (j + 1) with hpost
  have hprelen : pre.length = j := by simp [hpre]; omega
  have hpostlen : post.length = Z₀.length - j - 1 := by simp [hpost]; omega
  obtain ⟨l₁, q, hlq⟩ : ∃ l q, pre.take k = l ++ [q] := by
    rcases List.eq_nil_or_concat' (pre.take k) with h | ⟨L, b, h⟩
    · exfalso
      have := congrArg List.length h
      simp [hprelen] at this; omega
    · exact ⟨L, b, h⟩
  have hl₁ : l₁.length = k - 1 := by
    have := congrArg List.length hlq
    simp [hprelen] at this; omega
  have hq₂ : l' - j - 1 < post.length := by omega
  refine ⟨l₁, q, pre.drop k, post.take (l' - j - 1), post[l' - j - 1], post.drop (l' - j - 1 + 1),
    hl₁, by simp [hprelen], by simp [hpostlen]; omega, by simp [hpostlen]; omega, ?_⟩
  intro z
  rw [List.set_eq_take_append_cons_drop]
  simp only [hj, ↓reduceIte]
  have h1 : post = post.take (l' - j - 1) ++ (post[l' - j - 1] :: post.drop (l' - j - 1 + 1)) := by
    rw [← List.drop_eq_getElem_cons hq₂, List.take_append_drop]
  have h2 : pre = (l₁ ++ [q]) ++ pre.drop k := by rw [← hlq, List.take_append_drop]
  rw [← hpre, ← hpost]
  conv_lhs => rw [h2, h1]
  simp [List.append_assoc]

private lemma ofFn_update_eq_set {α : Type*} {n : ℕ} (a : Fin n → α) (j : Fin n) (y : α) :
    List.ofFn (Function.update a j y) = (List.ofFn a).set j.val y := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.getElem_ofFn, List.getElem_set, Function.update_apply]
  by_cases h : j.val = i
  · have : (⟨i, by simpa using h1⟩ : Fin n) = j := Fin.ext h.symm
    simp [h, this]
  · have : ¬ ((⟨i, by simpa using h1⟩ : Fin n) = j) := fun h' => h (by rw [← h'])
    simp [h, this]

private lemma zip_set_right {α β : Type*} (σ' : List α) (a : List β) (j : ℕ) (y : β)
    (hj : j < σ'.length) (hlen : σ'.length = a.length) :
    σ'.zip (a.set j y) = (σ'.zip a).set j (σ'[j], y) := by
  refine List.ext_getElem (by simp [hlen]) fun i h1 h2 => ?_
  simp only [List.getElem_zip, List.getElem_set]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

/-- Part (2): the split at `a_k`, `a_l`, `a_n`, with the varying entry `a_j` (`k < j < l`) inside the middle
segment `r₂ y`, which has the length `l - k - 1`, independent of `y`. -/
private lemma list_split2 {α : Type*} {m k l : ℕ} (σl : List Bool) (hσ : σl.length = m)
    (a : List α) (ha : a.length = m - 1) {j : ℕ} (hj : j < m - 1) (hk : 1 ≤ k) (hkj : k ≤ j)
    (hjl : j + 2 ≤ l) (hlm : l + 1 ≤ m) :
    ∃ (l₁ : List (Bool × α)) (q : Bool × α) (r₃ : List (Bool × α)) (q₂ : Bool × α) (s : Bool)
      (r₂ : α → List (Bool × α)),
      l₁.length = k - 1 ∧ r₃.length = m - l - 1 ∧ (∀ y, (r₂ y).length = l - k - 1) ∧
      ∀ x y : α, σl.zip (a.set j y ++ [x]) = l₁ ++ [q] ++ r₂ y ++ [q₂] ++ r₃ ++ [(s, x)] := by
  have hne : σl ≠ [] := by
    intro h; subst h; simp at hσ; omega
  set σ' := σl.dropLast with hσ'
  set s := σl.getLast hne with hs
  have hσl : σl = σ' ++ [s] := (List.dropLast_append_getLast hne).symm
  have hlen' : σ'.length = a.length := by simp [hσ', List.length_dropLast, hσ, ha]
  have hjσ : j < σ'.length := by omega
  set Z₀ := σ'.zip a with hZ₀
  have hZlen : Z₀.length = m - 1 := by simp [hZ₀, hlen', ha]
  obtain ⟨l₁, q, pre₂, post₁, q₂, r₃, h1, h2, h3, h4, hset⟩ :=
    split_set Z₀ (j := j) (k := k) (l' := l - 1) hk hkj (by omega) (by omega)
  refine ⟨l₁, q, r₃, q₂, s, fun y => pre₂ ++ [(σ'[j], y)] ++ post₁, h1, by omega,
    fun y => by simp; omega, ?_⟩
  intro x y
  rw [hσl, List.zip_append (by simpa using hlen'), zip_set_right σ' a j y hjσ hlen', hset]
  simp [List.append_assoc]

end Lists


/-! ## 6. The loop matrices `Gres H z`, `Eblk` on the block-product index -/

section LoopMatrix

open RBM.Gauss

variable (d L W : ℕ) [NeZero L]

/-- The block projection `P_a = W^d E_a`: the diagonal matrix of the indicator of the block `a`. -/
private def Pm (a : Zd d L) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  Matrix.diagonal fun x => if x.1 = a then 1 else 0

variable {d L W}

private lemma Eblk_eq_smul_Pm (a : Zd d L) :
    Eblk d L W a = ((W : ℂ) ^ d)⁻¹ • Pm d L W a := by
  ext x y
  by_cases hxy : x = y
  · subst hxy
    by_cases hx : x.1 = a <;> simp [Eblk, Pm, hx]
  · simp [Eblk, Pm, hxy]

private lemma Pm_eq_smul_Eblk [NeZero W] (a : Zd d L) :
    Pm d L W a = ((W : ℂ) ^ d) • Eblk d L W a := by
  have hW : ((W : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne W))
  rw [Eblk_eq_smul_Pm, smul_smul, mul_inv_cancel₀ hW, one_smul]

private lemma Pm_conjTranspose (a : Zd d L) : (Pm d L W a)ᴴ = Pm d L W a := by
  refine (Matrix.isHermitian_diagonal_iff.mpr fun x => ?_).eq
  by_cases h : x.1 = a <;> simp [h, IsSelfAdjoint]

private lemma Pm_mul_self (a : Zd d L) : Pm d L W a * Pm d L W a = Pm d L W a := by
  simp only [Pm, Matrix.diagonal_mul_diagonal]
  congr 1
  ext x
  by_cases h : x.1 = a <;> simp [h]

private lemma sum_Pm : ∑ a : Zd d L, Pm d L W a = 1 := by
  ext x y
  simp only [Pm, Matrix.sum_apply, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy
    simp
  · simp [hxy]

/-- `Σ_a ‖c‖`-type bound: `|c (t₁ - t₂)| ≤ M / η` for `‖c‖ = (2η)⁻¹`, `|t_i| ≤ M`. -/
private lemma norm_ward_trace_le {c t₁ t₂ : ℂ} {η M : ℝ} (hη : 0 < η) (hc : ‖c‖ = (2 * η)⁻¹)
    (h₁ : ‖t₁‖ ≤ M) (h₂ : ‖t₂‖ ≤ M) : ‖c * (t₁ - t₂)‖ ≤ M / η := by
  rw [norm_mul, hc]
  have : ‖t₁ - t₂‖ ≤ 2 * M := (norm_sub_le _ _).trans (by linarith)
  calc (2 * η)⁻¹ * ‖t₁ - t₂‖ ≤ (2 * η)⁻¹ * (2 * M) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = M / η := by field_simp

private lemma norm_Ward_const {z : ℂ} (hz : 0 < z.im) :
    ‖(2 * Complex.I * (z.im : ℂ))⁻¹‖ = (2 * z.im)⁻¹ := by
  rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hz.le]
  simp

section Bounds

variable [NeZero W] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ}

/-- `‖tr(X P_q X^*)‖ ≤ W^d M_{2k-1}/η` for `X = wd l · G(σ_k)` (`eq;genWard1`, first identity). -/
private lemma alpha_bound (hH : H.IsHermitian) (hz : 0 < z.im) (Mx : ℕ → ℝ)
    (hM : ∀ Lst : List (Bool × Zd d L),
      ‖(wd (Gres H z) (Eblk d L W) Lst).trace‖ ≤ Mx Lst.length)
    (l : List (Bool × Zd d L)) (q : Bool × Zd d L) :
    ‖((wd (Gres H z) (Eblk d L W) l * Gres H z q.1) * Pm d L W q.2 *
        (wd (Gres H z) (Eblk d L W) l * Gres H z q.1)ᴴ).trace‖ ≤
      ((W : ℝ) ^ d) * Mx (2 * l.length + 1) / z.im := by
  have hG : ∀ σ, (Gres H z σ)ᴴ = Gres H z (!σ) := Gres_conjTranspose hH z
  have hE : ∀ a, (Eblk d L W a)ᴴ = Eblk d L W a := fun a => (Eblk_isHermitian a).eq
  obtain ⟨L₁, L₂, h1, h2, htr⟩ := trace_reflect_X (Gres H z) (Eblk d L W) hG hE
    (2 * Complex.I * (z.im : ℂ))⁻¹ (Gres_ward_left hH hz.ne') l q
  have hmat : (wd (Gres H z) (Eblk d L W) l * Gres H z q.1) * Pm d L W q.2 *
        (wd (Gres H z) (Eblk d L W) l * Gres H z q.1)ᴴ =
      ((W : ℂ) ^ d) • (wd (Gres H z) (Eblk d L W) l *
        (Gres H z q.1 * Eblk d L W q.2 * Gres H z (!q.1)) *
        (wd (Gres H z) (Eblk d L W) l)ᴴ) := by
    rw [Pm_eq_smul_Eblk, Matrix.conjTranspose_mul, hG]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [hmat, Matrix.trace_smul, htr, smul_eq_mul, norm_mul]
  have hD : ‖((W : ℂ) ^ d)‖ = (W : ℝ) ^ d := by simp
  have hw := norm_ward_trace_le hz (norm_Ward_const hz)
    (t₁ := (wd (Gres H z) (Eblk d L W) L₁).trace) (t₂ := (wd (Gres H z) (Eblk d L W) L₂).trace)
    (M := Mx (2 * l.length + 1)) (by simpa [h1] using hM L₁) (by simpa [h2] using hM L₂)
  rw [hD]
  calc (W : ℝ) ^ d * ‖(2 * Complex.I * (z.im : ℂ))⁻¹ * _‖
      ≤ (W : ℝ) ^ d * (Mx (2 * l.length + 1) / z.im) := mul_le_mul_of_nonneg_left hw (by positivity)
    _ = _ := by ring

/-- `‖tr(P_e Y Y^*)‖ ≤ W^d M_{2m-2k-1}/η` for `Y = wd r · G(s)` (`eq;genWard1`, second identity). -/
private lemma beta_bound (hH : H.IsHermitian) (hz : 0 < z.im) (Mx : ℕ → ℝ)
    (hM : ∀ Lst : List (Bool × Zd d L),
      ‖(wd (Gres H z) (Eblk d L W) Lst).trace‖ ≤ Mx Lst.length)
    (r : List (Bool × Zd d L)) (s : Bool) (e : Zd d L) :
    ‖(Pm d L W e * ((wd (Gres H z) (Eblk d L W) r * Gres H z s) *
        (wd (Gres H z) (Eblk d L W) r * Gres H z s)ᴴ)).trace‖ ≤
      ((W : ℝ) ^ d) * Mx (2 * r.length + 1) / z.im := by
  have hG : ∀ σ, (Gres H z σ)ᴴ = Gres H z (!σ) := Gres_conjTranspose hH z
  have hE : ∀ a, (Eblk d L W a)ᴴ = Eblk d L W a := fun a => (Eblk_isHermitian a).eq
  obtain ⟨L₁, L₂, h1, h2, htr⟩ := trace_reflect_Y (Gres H z) (Eblk d L W) hG hE
    (2 * Complex.I * (z.im : ℂ))⁻¹ (Gres_ward_right hH hz.ne') r s e
  have hmat : Pm d L W e * ((wd (Gres H z) (Eblk d L W) r * Gres H z s) *
        (wd (Gres H z) (Eblk d L W) r * Gres H z s)ᴴ) =
      ((W : ℂ) ^ d) • (Eblk d L W e * (wd (Gres H z) (Eblk d L W) r *
        (Gres H z s * Gres H z (!s)) * (wd (Gres H z) (Eblk d L W) r)ᴴ)) := by
    rw [Pm_eq_smul_Eblk, Matrix.conjTranspose_mul, hG]
    simp only [Matrix.smul_mul, Matrix.mul_assoc]
  rw [hmat, Matrix.trace_smul, htr, smul_eq_mul, norm_mul]
  have hD : ‖((W : ℂ) ^ d)‖ = (W : ℝ) ^ d := by simp
  have hw := norm_ward_trace_le hz (norm_Ward_const hz)
    (t₁ := (wd (Gres H z) (Eblk d L W) L₁).trace) (t₂ := (wd (Gres H z) (Eblk d L W) L₂).trace)
    (M := Mx (2 * r.length + 1)) (by simpa [h1] using hM L₁) (by simpa [h2] using hM L₂)
  rw [hD]
  calc (W : ℝ) ^ d * ‖(2 * Complex.I * (z.im : ℂ))⁻¹ * _‖
      ≤ (W : ℝ) ^ d * (Mx (2 * r.length + 1) / z.im) := mul_le_mul_of_nonneg_left hw (by positivity)
    _ = _ := by ring

/-- `√(D M₁/η) √(D M₂/η) = (D/η) √(M₁ M₂)`. -/
private lemma sqrt_mul_sqrt_eq {D η M₁ M₂ : ℝ} (hD : 0 < D) (hη : 0 < η) (h₁ : 0 ≤ M₁) :
    √(D * M₁ / η) * √(D * M₂ / η) = (D / η) * √(M₁ * M₂) := by
  rw [← Real.sqrt_mul (by positivity)]
  have : D * M₁ / η * (D * M₂ / η) = (D / η) ^ 2 * (M₁ * M₂) := by ring
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

/-- The arithmetic of the two `W^d`'s of part (1): `(W^d)⁻² √(D M₁/η) √(D M₂/η) = (W^d η)⁻¹ √(M₁ M₂)`. -/
private lemma arith_part1 {D η M₁ M₂ : ℝ} (hD : 0 < D) (hη : 0 < η) (h₁ : 0 ≤ M₁) :
    (D⁻¹) ^ 2 * (√(D * M₁ / η) * √(D * M₂ / η)) = (D * η)⁻¹ * √(M₁ * M₂) := by
  rw [sqrt_mul_sqrt_eq hD hη h₁]
  field_simp

/-- `√((D^{2p} M)^{1/p}) = D M^{1/(2p)}`. -/
private lemma arith_sqrt_rpow {D M : ℝ} (hD : 0 ≤ D) (hM : 0 ≤ M) {p : ℕ} (hp : 1 ≤ p) :
    √((D ^ (2 * p) * M) ^ ((p : ℝ)⁻¹)) = D * M ^ (1 / (2 * (p : ℝ))) := by
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp2 : (2 * p : ℕ) ≠ 0 := by omega
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  have : (p : ℝ)⁻¹ * (1 / 2) = 1 / (2 * (p : ℝ)) := by field_simp
  rw [this, Real.mul_rpow (by positivity) hM]
  congr 1
  have h := Real.pow_rpow_inv_natCast hD hp2
  push_cast at h
  rw [show (1 / (2 * (p : ℝ))) = (2 * (p : ℝ))⁻¹ by simp]
  exact h

/-- **Part (1) at the matrix level**: `Σ_x |tr ∏ G E (… x)| ≤ (W^d η)⁻¹ (M_{2k-1} M_{2m-2k-1})^{1/2}`
for words `l ++ [q] ++ r ++ [(s, x)]` (`l` has `k - 1` pairs, `r` has `m - k - 1`), `Mx n` any
bound of the traces of words of length `n`. -/
private lemma part1_matrix (hH : H.IsHermitian) (hz : 0 < z.im) (Mx : ℕ → ℝ)
    (hM0 : ∀ n, 0 ≤ Mx n)
    (hM : ∀ Lst : List (Bool × Zd d L),
      ‖(wd (Gres H z) (Eblk d L W) Lst).trace‖ ≤ Mx Lst.length)
    (l r : List (Bool × Zd d L)) (q : Bool × Zd d L) (s : Bool) :
    ∑ x : Zd d L, ‖(wd (Gres H z) (Eblk d L W) (l ++ [q] ++ r ++ [(s, x)])).trace‖ ≤
      (((W : ℝ) ^ d) * z.im)⁻¹ * √(Mx (2 * l.length + 1) * Mx (2 * r.length + 1)) := by
  set G := Gres H z with hGdef
  set E := Eblk d L W with hEdef
  set X : Matrix (Vtx d L W) (Vtx d L W) ℂ := wd G E l * G q.1 with hX
  set Y : Matrix (Vtx d L W) (Vtx d L W) ℂ := wd G E r * G s with hY
  set w : ℂ := ((W : ℂ) ^ d)⁻¹ with hw
  have hEw : ∀ a, E a = w • Pm d L W a := fun a => Eblk_eq_smul_Pm a
  have hwn : ‖w‖ = (((W : ℝ) ^ d))⁻¹ := by simp [hw]
  have hx : ∀ x : Zd d L, ‖(wd G E (l ++ [q] ++ r ++ [(s, x)])).trace‖ =
      ‖w‖ ^ 2 * ‖(Pm d L W x * X * Pm d L W q.2 * Y).trace‖ := by
    intro x
    have hdec : wd G E (l ++ [q] ++ r ++ [(s, x)]) = X * E q.2 * Y * E x := by
      simp only [wd_append, wd_singleton, hX, hY, Matrix.mul_assoc]
    have h2 : E x * (X * E q.2 * Y) = (w * w) • (Pm d L W x * X * Pm d L W q.2 * Y) := by
      rw [hEw x, hEw q.2]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
    rw [hdec, Matrix.trace_mul_comm, h2, Matrix.trace_smul, smul_eq_mul, norm_mul, norm_mul, sq]
  have hD : (0 : ℝ) < (W : ℝ) ^ d := by
    have : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
    positivity
  have hα := alpha_bound hH hz Mx hM l q
  have hβ := beta_bound hH hz Mx hM r s q.2
  have hc1 := core1 (Pm d L W) Pm_conjTranspose Pm_mul_self sum_Pm X Y q.2 hα hβ
  calc ∑ x : Zd d L, ‖(wd G E (l ++ [q] ++ r ++ [(s, x)])).trace‖
      = ‖w‖ ^ 2 * ∑ x : Zd d L, ‖(Pm d L W x * X * Pm d L W q.2 * Y).trace‖ := by
        simp_rw [hx]; rw [Finset.mul_sum]
    _ ≤ ‖w‖ ^ 2 * (√(((W : ℝ) ^ d) * Mx (2 * l.length + 1) / z.im) *
          √(((W : ℝ) ^ d) * Mx (2 * r.length + 1) / z.im)) := by gcongr
    _ = _ := by rw [hwn]; exact arith_part1 hD hz (hM0 _)

/-- **Part (2) at the matrix level** (`eq:Apsipsi`, `eq:Apsipsi1`): for the words
`l ++ [q] ++ r₂ y ++ [q₂] ++ r₃ ++ [(s, x)]` (the middle segment `r₂ y` has `n₂` pairs and carries the
summed label `a_j`), `Σ_x Σ_{y ∈ 𝒜 x} |tr ∏ G E| ≤ C (W^d η)⁻¹ (M_{2k-1} M_{2m-2l-1})^{1/2}
M_{2(n₂+1)p}^{1/(2p)}`. -/
private lemma part2_matrix (hH : H.IsHermitian) (hz : 0 < z.im) (Mx : ℕ → ℝ)
    (hM0 : ∀ n, 0 ≤ Mx n)
    (hM : ∀ Lst : List (Bool × Zd d L),
      ‖(wd (Gres H z) (Eblk d L W) Lst).trace‖ ≤ Mx Lst.length)
    {p : ℕ} (hp : 1 ≤ p) {C : ℝ} (hC : 0 ≤ C) (𝒜 : Zd d L → Finset (Zd d L))
    (hcard : ∀ x, ((𝒜 x).card : ℝ) ≤ C)
    (l r₃ : List (Bool × Zd d L)) (q q₂ : Bool × Zd d L) (s : Bool)
    (r₂ : Zd d L → List (Bool × Zd d L)) (n₂ : ℕ) (hr₂ : ∀ y, (r₂ y).length = n₂) :
    ∑ x : Zd d L, ∑ y ∈ 𝒜 x,
        ‖(wd (Gres H z) (Eblk d L W) (l ++ [q] ++ r₂ y ++ [q₂] ++ r₃ ++ [(s, x)])).trace‖ ≤
      C * ((((W : ℝ) ^ d) * z.im)⁻¹ * √(Mx (2 * l.length + 1) * Mx (2 * r₃.length + 1)) *
        Mx (2 * (n₂ + 1) * p) ^ (1 / (2 * (p : ℝ)))) := by
  set G := Gres H z with hGdef
  set E := Eblk d L W with hEdef
  have hG : ∀ σ, (G σ)ᴴ = G (!σ) := Gres_conjTranspose hH z
  have hE : ∀ a, (E a)ᴴ = E a := fun a => (Eblk_isHermitian a).eq
  set X₁ : Matrix (Vtx d L W) (Vtx d L W) ℂ := wd G E l * G q.1 with hX₁
  set X₃ : Matrix (Vtx d L W) (Vtx d L W) ℂ := wd G E r₃ * G s with hX₃
  set X₂ : Zd d L → Matrix (Vtx d L W) (Vtx d L W) ℂ := fun y => wd G E (r₂ y) * G q₂.1 with hX₂
  set w : ℂ := ((W : ℂ) ^ d)⁻¹ with hw
  have hEw : ∀ a, E a = w • Pm d L W a := fun a => Eblk_eq_smul_Pm a
  have hPE : ∀ a, Pm d L W a = ((W : ℂ) ^ d) • E a := fun a => Pm_eq_smul_Eblk a
  have hwn : ‖w‖ = (((W : ℝ) ^ d))⁻¹ := by simp [hw]
  have hD : (0 : ℝ) < (W : ℝ) ^ d := by
    have : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
    positivity
  have hx : ∀ (x y : Zd d L),
      ‖(wd G E (l ++ [q] ++ r₂ y ++ [q₂] ++ r₃ ++ [(s, x)])).trace‖ =
        ‖w‖ ^ 3 * ‖(Pm d L W x * X₁ * Pm d L W q.2 * X₂ y * Pm d L W q₂.2 * X₃).trace‖ := by
    intro x y
    have hdec : wd G E (l ++ [q] ++ r₂ y ++ [q₂] ++ r₃ ++ [(s, x)]) =
        X₁ * E q.2 * X₂ y * E q₂.2 * X₃ * E x := by
      simp only [wd_append, wd_singleton, hX₁, hX₂, hX₃, Matrix.mul_assoc]
    have h2 : E x * (X₁ * E q.2 * X₂ y * E q₂.2 * X₃) =
        (w * w * w) • (Pm d L W x * X₁ * Pm d L W q.2 * X₂ y * Pm d L W q₂.2 * X₃) := by
      rw [hEw x, hEw q.2, hEw q₂.2]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
    rw [hdec, Matrix.trace_mul_comm, h2, Matrix.trace_smul, smul_eq_mul, norm_mul, norm_mul,
      norm_mul]
    ring
  -- the power-trace bound of the middle block
  set Mp : ℝ := Mx (2 * (n₂ + 1) * p) with hMp
  set T : ℝ := ((W : ℝ) ^ d) ^ (2 * p) * Mp with hT
  have hT0 : 0 ≤ T := mul_nonneg (pow_nonneg hD.le _) (hM0 _)
  have hTb : ∀ y : Zd d L,
      ((((Pm d L W q.2 * X₂ y * Pm d L W q₂.2) * (Pm d L W q.2 * X₂ y * Pm d L W q₂.2)ᴴ) ^ p).trace).re
        ≤ T := by
    intro y
    set cc : Zd d L → List (Bool × Zd d L) := fun e => [q₂, (!q₂.1, e)] with hcc
    have hc : ∀ e, wd G E (cc e) = (G q₂.1 * E q₂.2 * G (!q₂.1)) * E e := by
      intro e; simp [hcc, wd, Matrix.mul_assoc]
    have hR := wd_Ref G E hG hE cc _ hc (r₂ y)
    set Lc : List (Bool × Zd d L) := Ref cc (r₂ y) q.2 with hLc
    have hLclen : Lc.length = 2 * n₂ + 2 := by
      rw [hLc, Ref_length cc 2 (fun e => by simp [hcc]), hr₂ y]
    have h1 : (Pm d L W q.2 * X₂ y * Pm d L W q₂.2) * (Pm d L W q.2 * X₂ y * Pm d L W q₂.2)ᴴ =
        Pm d L W q.2 * (X₂ y * Pm d L W q₂.2 * (X₂ y)ᴴ) * Pm d L W q.2 := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Pm_conjTranspose, Pm_conjTranspose]
      calc Pm d L W q.2 * X₂ y * Pm d L W q₂.2 * (Pm d L W q₂.2 * ((X₂ y)ᴴ * Pm d L W q.2))
          = Pm d L W q.2 * X₂ y * (Pm d L W q₂.2 * Pm d L W q₂.2) * ((X₂ y)ᴴ * Pm d L W q.2) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [Pm_mul_self]; simp only [Matrix.mul_assoc]
    have h2 : X₂ y * Pm d L W q₂.2 * (X₂ y)ᴴ * Pm d L W q.2 =
        (((W : ℂ) ^ d) * ((W : ℂ) ^ d)) • wd G E Lc := by
      rw [hLc, hR, hPE q₂.2, hPE q.2, hX₂]
      simp only [Matrix.conjTranspose_mul, hG]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
    rw [h1, trace_pow_proj _ _ (Pm_mul_self q.2) hp, h2, smul_pow, Matrix.trace_smul, wd_pow]
    refine (Complex.re_le_norm _).trans ?_
    rw [smul_eq_mul, norm_mul, norm_pow]
    have hn : ‖((W : ℂ) ^ d) * ((W : ℂ) ^ d)‖ = ((W : ℝ) ^ d) * ((W : ℝ) ^ d) := by simp
    rw [hn]
    have hM' := hM ((List.replicate p Lc).flatten)
    rw [length_replicate_flatten, hLclen,
      show p * (2 * n₂ + 2) = 2 * (n₂ + 1) * p by ring] at hM'
    calc ((W : ℝ) ^ d * (W : ℝ) ^ d) ^ p * ‖(wd G E (List.replicate p Lc).flatten).trace‖
        ≤ ((W : ℝ) ^ d * (W : ℝ) ^ d) ^ p * Mp :=
          mul_le_mul_of_nonneg_left hM' (by positivity)
      _ = T := by rw [hT, ← mul_pow, ← pow_two, ← pow_mul]; ring_nf
  have hμ0 : 0 ≤ T ^ ((p : ℝ)⁻¹) := Real.rpow_nonneg hT0 _
  have hμ : ∀ (y : Zd d L) (ρ : Vtx d L W → ℂ),
      ∑ t, ‖∑ s', ρ s' * (Pm d L W q.2 * X₂ y * Pm d L W q₂.2) s' t‖ ^ 2 ≤
        T ^ ((p : ℝ)⁻¹) * ∑ s', ‖ρ s'‖ ^ 2 :=
    fun y ρ => rowbound_of_pow _ hp hT0 (hTb y) ρ
  have hα := alpha_bound hH hz Mx hM l q
  have hβ := beta_bound hH hz Mx hM r₃ s q₂.2
  have hc2 := core2 (Pm d L W) Pm_conjTranspose Pm_mul_self sum_Pm X₁ X₃ X₂ q.2 q₂.2 hμ0 hμ hα hβ
    hC 𝒜 hcard
  have hsq : √(T ^ ((p : ℝ)⁻¹)) = (W : ℝ) ^ d * Mp ^ (1 / (2 * (p : ℝ))) :=
    arith_sqrt_rpow hD.le (hM0 _) hp
  calc ∑ x : Zd d L, ∑ y ∈ 𝒜 x,
        ‖(wd G E (l ++ [q] ++ r₂ y ++ [q₂] ++ r₃ ++ [(s, x)])).trace‖
      = ‖w‖ ^ 3 * ∑ x : Zd d L, ∑ y ∈ 𝒜 x,
          ‖(Pm d L W x * X₁ * Pm d L W q.2 * X₂ y * Pm d L W q₂.2 * X₃).trace‖ := by
        simp_rw [hx]; simp_rw [← Finset.mul_sum]
    _ ≤ ‖w‖ ^ 3 * (C * (√(T ^ ((p : ℝ)⁻¹)) *
          (√(((W : ℝ) ^ d) * Mx (2 * l.length + 1) / z.im) *
            √(((W : ℝ) ^ d) * Mx (2 * r₃.length + 1) / z.im)))) := by gcongr
    _ = _ := by
        rw [hsq, sqrt_mul_sqrt_eq hD hz (hM0 _), hwn]
        field_simp

end Bounds

end LoopMatrix


/-! ## 7. The pins: `STLI` and `STmaxL` as words, and `stContract_holds` -/

section Pin

open RBM.Gauss RBM.Loop

variable {d : ℕ} (sz : Sizes d)

/-- The block flow matrix `H_τ` on the block-product index is Hermitian. -/
private lemma blockMat_flow_isHermitian (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ) :
    (blockMat d (sz.L n) (sz.W n) (seqHflow sz n τ ω)).IsHermitian :=
  (seqHflow_isHermitian sz n τ ω).submatrix _

private lemma foldr_eq_wd {ι κ : Type*} [Fintype ι] [DecidableEq ι] (G : Bool → Matrix ι ι ℂ)
    (E : κ → Matrix ι ι ℂ) (l : List (Bool × κ)) :
    l.foldr (fun p M => G p.1 * E p.2 * M) 1 = wd G E l := by
  induction l with
  | nil => simp
  | cons p l ih => simp [ih]

/-- `𝓛_I` of the pin (`STLI`) is the trace of the word of its pairs. -/
private lemma STLI_eq_trace_wd (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) (I : LoopIdx (Zd d (sz.L n))) :
    STLI sz n E τ ω I =
      (wd (Gres (blockMat d (sz.L n) (sz.W n) (seqHflow sz n τ ω)) (zt E τ))
        (Eblk d (sz.L n) (sz.W n)) (I.σ.zip I.a)).trace := by
  unfold STLI loopL
  rw [foldr_eq_wd]

/-- Every word is a loop of the pins: `|tr ∏ G E| ≤ max_{σ,a} |𝓛^{(n)}|` with `n` its length. -/
private lemma norm_trace_wd_le_STmaxL (n : ℕ) (E t : ℝ) (ω : sz.SeqΩ)
    (Lst : List (Bool × Zd d (sz.L n))) :
    ‖(wd (Gres (blockMat d (sz.L n) (sz.W n) (seqHflow sz n t ω)) (zt E t))
        (Eblk d (sz.L n) (sz.W n)) Lst).trace‖ ≤ STmaxL sz n E t Lst.length ω := by
  unfold STmaxL
  refine le_trans (le_of_eq ?_)
    (Finset.le_sup' (fun p : (Fin Lst.length → Bool) × (Fin Lst.length → Zd d (sz.L n)) =>
      ‖Lloop sz n E t p.1 p.2 ω‖)
      (Finset.mem_univ ((fun i => (Lst.get i).1), (fun i => (Lst.get i).2))))
  unfold Lloop loopFine loopM wd
  have hmap : ∀ f : Bool × Zd d (sz.L n) → Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ,
      Lst.map f = List.ofFn (fun i : Fin Lst.length => f (Lst.get i)) := fun f =>
    List.ext_getElem (by simp) fun i h1 h2 => by simp
  dsimp only
  rw [hmap]

private lemma STmaxL_nonneg (n : ℕ) (E t : ℝ) (k : ℕ) (ω : sz.SeqΩ) : 0 ≤ STmaxL sz n E t k ω :=
  (norm_nonneg _).trans (Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
    ‖Lloop sz n E t p.1 p.2 ω‖) (Finset.mem_univ ((fun _ => true), (fun _ => 0))))

/-- **`STContract`** (`ygdhmsgq`, `(yi2oslxj2)`, `(u2jzooi-2)`, `3_5:918-1000`): the contraction
inequality holds for every `d`, every size sequence, every sample and every flow time
`τ ∈ [0, 1)`, `|E| < 2`: no hypothesis beyond those of the pin. -/
theorem stContract_holds (d : ℕ) : STContract d := by
  intro sz n E τ hE h0 h1 ω
  have hη : 0 < etaT E τ := etaT_pos hE h1
  have hzim : (zt E τ).im = etaT E τ := (etaT_eq_zt_im).symm
  have hz : 0 < (zt E τ).im := by rw [hzim]; exact hη
  have hH := blockMat_flow_isHermitian sz n τ ω
  have hM0 : ∀ k, 0 ≤ (fun k => STmaxL sz n E τ k ω) k := fun k => STmaxL_nonneg sz n E τ k ω
  have hM := norm_trace_wd_le_STmaxL sz n E τ ω
  constructor
  · intro m k hk hkm σ a
    obtain ⟨l, q, r, s, hl, hr, hsplit⟩ :=
      list_split1 hk hkm (List.ofFn σ) (by simp) (List.ofFn a) (by simp)
    have hpart := part1_matrix hH hz (fun k => STmaxL sz n E τ k ω) hM0 hM l r q s
    have e1 : 2 * l.length + 1 = 2 * k - 1 := by omega
    have e2 : 2 * r.length + 1 = 2 * m - 2 * k - 1 := by omega
    calc ∑ x : Zd d (sz.L n), ‖STLI sz n E τ ω ⟨List.ofFn σ, List.ofFn a ++ [x]⟩‖
        = ∑ x : Zd d (sz.L n), ‖(wd (Gres (blockMat d (sz.L n) (sz.W n) (seqHflow sz n τ ω))
            (zt E τ)) (Eblk d (sz.L n) (sz.W n)) (l ++ [q] ++ r ++ [(s, x)])).trace‖ := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [STLI_eq_trace_wd sz n E τ ω ⟨List.ofFn σ, List.ofFn a ++ [x]⟩]
          change ‖(wd _ _ ((List.ofFn σ).zip (List.ofFn a ++ [x]))).trace‖ = _
          rw [hsplit x]
      _ ≤ _ := hpart
      _ = _ := by
          simp only [e1, e2, hzim, Real.sqrt_eq_rpow]
  · intro m k l p j C hm hp hk hkj hjl hlm hC 𝒜 hcard σ a
    obtain ⟨l₁, q, r₃, q₂, s, r₂, hl₁, hr₃, hr₂, hsplit⟩ :=
      list_split2 (m := m) (k := k) (l := l) (List.ofFn σ) (by simp) (List.ofFn a) (by simp)
        (j := j.val) j.2 hk (by omega) (by omega) hlm
    have hpart := part2_matrix hH hz (fun k => STmaxL sz n E τ k ω) hM0 hM hp hC 𝒜 hcard
      l₁ r₃ q q₂ s r₂ (l - k - 1) hr₂
    have e1 : 2 * l₁.length + 1 = 2 * k - 1 := by omega
    have e2 : 2 * r₃.length + 1 = 2 * m - 2 * l - 1 := by omega
    have e3 : 2 * (l - k - 1 + 1) * p = 2 * (l - k) * p := by
      have : l - k - 1 + 1 = l - k := by omega
      rw [this]
    calc ∑ x : Zd d (sz.L n), ∑ y ∈ 𝒜 x,
          ‖STLI sz n E τ ω ⟨List.ofFn σ, List.ofFn (Function.update a j y) ++ [x]⟩‖
        = ∑ x : Zd d (sz.L n), ∑ y ∈ 𝒜 x,
            ‖(wd (Gres (blockMat d (sz.L n) (sz.W n) (seqHflow sz n τ ω)) (zt E τ))
              (Eblk d (sz.L n) (sz.W n)) (l₁ ++ [q] ++ r₂ y ++ [q₂] ++ r₃ ++ [(s, x)])).trace‖ := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          rw [STLI_eq_trace_wd sz n E τ ω ⟨List.ofFn σ, List.ofFn (Function.update a j y) ++ [x]⟩]
          change ‖(wd _ _ ((List.ofFn σ).zip (List.ofFn (Function.update a j y) ++ [x]))).trace‖ = _
          rw [ofFn_update_eq_set, hsplit x y]
      _ ≤ _ := hpart
      _ = _ := by
          simp only [e1, e2, e3, hzim, Real.sqrt_eq_rpow]
          ring

end Pin


/-! ## 8. Compiled instances at `d = 3`, `sz0`, `n = 0`, `E = 0`, `τ = 1/2`, `ω = 0`

`sz0 0`: `L = 4`, `W = 32` (`W^3 = 32768`, 64 blocks), `η_{1/2} = 1/2`; `stContract_holds 3` is applied
with every deterministic hypothesis (`|E| < 2`, `0 ≤ τ < 1`, the index chain, `0 ≤ C`,
`|𝒜 x| ≤ C`) discharged. -/

section Instances

open RBM.Gauss.SizesInst

/-- `η_{1/2}(E = 0) = 1/2 > 0`: the data of the instances are in the bulk, away from `η = 0`. -/
example : etaT 0 (1 / 2) = 1 / 2 := by
  unfold etaT
  rw [mE_im, show (4 - (0 : ℝ) ^ 2) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- `(yi2oslxj2)` for `m = 2`, `k = 1`, `σ = (+,-)`, `a_1 = 0`. -/
example :
    (∑ x : Zd 3 (sz0.L 0), ‖STLI sz0 0 0 (1 / 2) (0 : sz0.SeqΩ)
        ⟨List.ofFn (![true, false] : Fin 2 → Bool),
          List.ofFn (![0] : Fin 1 → Zd 3 (sz0.L 0)) ++ [x]⟩‖) ≤
      (((sz0.W 0 : ℕ) : ℝ) ^ 3 * etaT 0 (1 / 2))⁻¹ *
        (STmaxL sz0 0 0 (1 / 2) (2 * 1 - 1) (0 : sz0.SeqΩ) *
          STmaxL sz0 0 0 (1 / 2) (2 * 2 - 2 * 1 - 1) (0 : sz0.SeqΩ)) ^ (1 / 2 : ℝ) :=
  (stContract_holds 3 sz0 0 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num) 0).1 2 1
    (by norm_num) (by norm_num) ![true, false] ![0]

/-- `(u2jzooi-2)` for `m = 4`, `k = 1`, `l = 3`, `p = 1`, `j = 2` (`a_2`, `1 < 2 < 3`), `C = 1`,
`𝒜 x = {x}`, `σ = (+,-,+,-)`. -/
example :
    (∑ x : Zd 3 (sz0.L 0), ∑ y ∈ ({x} : Finset (Zd 3 (sz0.L 0))),
        ‖STLI sz0 0 0 (1 / 2) (0 : sz0.SeqΩ) ⟨List.ofFn (![true, false, true, false] : Fin 4 → Bool),
          List.ofFn (Function.update (![0, 0, 0] : Fin 3 → Zd 3 (sz0.L 0)) (1 : Fin 3) y) ++ [x]⟩‖) ≤
      1 * (((sz0.W 0 : ℕ) : ℝ) ^ 3 * etaT 0 (1 / 2))⁻¹ *
        (STmaxL sz0 0 0 (1 / 2) (2 * 1 - 1) (0 : sz0.SeqΩ) *
          STmaxL sz0 0 0 (1 / 2) (2 * 4 - 2 * 3 - 1) (0 : sz0.SeqΩ)) ^ (1 / 2 : ℝ) *
          STmaxL sz0 0 0 (1 / 2) (2 * (3 - 1) * 1) (0 : sz0.SeqΩ) ^ (1 / (2 * ((1 : ℕ) : ℝ))) :=
  (stContract_holds 3 sz0 0 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num) 0).2 4 1 3 1
    ⟨1, by norm_num⟩ 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (fun x => {x}) (fun x => by simp) ![true, false, true, false]
    ![0, 0, 0]

end Instances

end RBM.Gauss.Sizes
