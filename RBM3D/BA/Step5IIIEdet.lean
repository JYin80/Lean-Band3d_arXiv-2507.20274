/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step2Gen
import RBM3D.BA.Step2BA
import RBM3D.Loop.GLoopFlow
import RBM3D.Induction.Step5Pins
import RBM3D.Path.LemDecCalE
import RBM3D.Path.LemDecCalEwG
import RBM3D.Graph.BAAuxGraph2

/-!
# The ℰ-bounds of BA case (iii) of Step 5 by Hilbert-Schmidt estimates, first half

Paper: Lemma 5.2 (`lem_dec_calE`), (5.43) `res_deccalE_lk`, (5.44) `res_deccalE_wG`; the paper omits the proof ("a special case of
[YY_25, Lemma 5.7]"; at BA, Section 8, "we therefore omit the details").  This file proves `res_deccalE_lk` and `res_deccalE_wG` at BA; the second half
(`res_deccalE_dif` (5.45), `S_θ`, the assembly) is `BA/Step5IIIEdet2`.

* Hilbert-Schmidt layer (no entry bound of `G`): `|tr(AB)| ≤ ‖A‖_F‖B‖_F`,
  `|tr(X₁⋯X_k)| ≤ ∏‖X_i‖_F` (`k ≥ 2`); with `X_i = E_{a_{i-1}}^{1/2} G(σ_i) E_{a_i}^{1/2}`,
  `𝓛^{(k)}_{σ,a} = tr(X₀⋯X_{k-1})` and (`H` Hermitian)
  `‖X_i‖_F² = 𝓛^{(2)}_{(σ_i,!σ_i),(a_i,a_{i-1})}`, so
  `‖𝓛^{(k)}_{σ,a}‖ ≤ ∏_i √‖𝓛^{(2)}_{(σ_i,!σ_i),(a_i,a_{i-1})}‖` at `(baStep2Mat sz lam0 E).LM`;
  the list form (for `STLIMg`) and the glue form (six-loop with two adjacent legs kept as one
  factor).
* The premise bundle `BAStep5IIIEScalar`, `BAStep5IIIEMatrix` (the BA version of the
  band bundle of `Path/LemDecCalE`, without its entry-level conjuncts and
  its energy bound; the matrix part is a hypothesis of the theorems).
* `baStep5IIIE_lk`, `baStep5IIIE_wG`: `res_deccalE_lk`, `res_deccalE_wG` as inequality chains from the bundle,
  `S = 1` (`baStep2Mat`), the band's lattice lemmas and the loss `lossE2wG`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open private lemDecCalE_zdistInf_sub_comm lemDecCalE_zdistInf_tri_real from RBM3D.Path.LemDecCalE

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Matrix

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The Hilbert-Schmidt layer -/

section HS
open scoped Matrix.Norms.Frobenius

/-- Cauchy-Schwarz for the trace in the Frobenius (= Hilbert-Schmidt) norm. -/
theorem baStep5IIIE_trace_mul_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ) :
    ‖(A * B).trace‖ ≤ ‖A‖ * ‖B‖ := by
  have hA : ‖A‖ = Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := by rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]; norm_num
  have hB : ‖B‖ = Real.sqrt (∑ i, ∑ j, ‖B i j‖ ^ 2) := by rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]; norm_num
  rw [hA, hB]
  have h1 : ‖(A * B).trace‖ ≤ ∑ i, ∑ j, ‖A i j‖ * ‖B j i‖ := by
    rw [Matrix.trace]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [Matrix.diag_apply, Matrix.mul_apply]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => by rw [norm_mul])
  refine h1.trans ?_
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)]
  apply Real.le_sqrt_of_sq_le
  have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × ι)) (fun p => ‖A p.1 p.2‖) (fun p => ‖B p.2 p.1‖)
  simp only [Fintype.sum_prod_type] at this
  rwa [show ∑ x, ∑ y, ‖B y x‖ ^ 2 = ∑ i, ∑ j, ‖B i j‖ ^ 2 from Finset.sum_comm] at this

/-- `|tr(X₁⋯X_k)| ≤ ∏ ‖X_i‖_F`, `k ≥ 2` (false at `k = 1`: `|tr X| ≤ √N ‖X‖_F`). -/
theorem baStep5IIIE_trace_prod_le {ι : Type*} [Fintype ι] [DecidableEq ι] (l : List (Matrix ι ι ℂ)) (hl : 2 ≤ l.length) :
    ‖l.prod.trace‖ ≤ (l.map fun A => ‖A‖).prod := by
  obtain ⟨A, t, rfl⟩ : ∃ A t, l = A :: t := by cases l <;> simp_all
  have ht : t ≠ [] := by rintro rfl; simp at hl
  simp only [List.prod_cons, List.map_cons]
  exact (baStep5IIIE_trace_mul_le _ _).trans (mul_le_mul_of_nonneg_left (List.norm_prod_le' ht) (norm_nonneg _))

/-- `‖X‖_F² = tr(X Xᴴ)`. -/
private theorem Step5IIIEdet_frob_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) :
    (((‖X‖ ^ 2 : ℝ)) : ℂ) = (X * Xᴴ).trace := by
  have hA : ‖X‖ = Real.sqrt (∑ i, ∑ j, ‖X i j‖ ^ 2) := by rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]; norm_num
  rw [hA, Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)]
  push_cast
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast; ring

/-- The trace is invariant under rotation of a list of matrices. -/
private theorem Step5IIIEdet_trace_rotate {ι : Type*} [Fintype ι] [DecidableEq ι] (l : List (Matrix ι ι ℂ)) (j : ℕ) :
    (l.rotate j).prod.trace = l.prod.trace := by
  rw [List.rotate_eq_drop_append_take_mod, List.prod_append, Matrix.trace_mul_comm, ← List.prod_append,
    List.take_append_drop]

/-- Telescoping of the half-edges: `∏_i G_i (S_i S_i) = G_0 S_0 · ∏_{i<n} (S_i G_{i+1} S_{i+1}) · S_n`. -/
private theorem Step5IIIEdet_tele {M : Type*} [Monoid M] : ∀ (n : ℕ) (G S : Fin (n + 1) → M),
    (List.ofFn fun i => G i * (S i * S i)).prod =
      G 0 * S 0 * (List.ofFn fun i : Fin n => S i.castSucc * G i.succ * S i.succ).prod * S (Fin.last n) := by
  intro n
  induction n with
  | zero => intro G S; simp [mul_assoc]
  | succ n ih =>
    intro G S
    rw [List.ofFn_succ' (fun i => G i * (S i * S i)),
      List.ofFn_succ' (fun i : Fin (n + 1) => S i.castSucc * G i.succ * S i.succ)]
    simp only [List.concat_eq_append, List.prod_append, List.prod_singleton]
    have := ih (fun i => G i.castSucc) (fun i => S i.castSucc)
    simp only [Fin.castSucc_zero] at this
    rw [this]
    simp [Fin.succ_last, mul_assoc]

/-- Cyclic rotation of the half-edges: `tr ∏ G_i (S_i S_i) = tr ∏ S_{i-1} G_i S_i`. -/
private theorem Step5IIIEdet_trace_rot {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (G S : Fin (n + 1) → Matrix ι ι ℂ) :
    (List.ofFn fun i => G i * (S i * S i)).prod.trace =
      (List.ofFn fun i : Fin (n + 1) => S ((finRotate (n + 1)).symm i) * G i * S i).prod.trace := by
  rw [Step5IIIEdet_tele, List.ofFn_succ (f := fun i : Fin (n + 1) => S ((finRotate (n + 1)).symm i) * G i * S i), List.prod_cons]
  have h0 : (finRotate (n + 1)).symm 0 = Fin.last n := by rw [Equiv.symm_apply_eq]; exact finRotate_last.symm
  have h1 : ∀ i : Fin n, (finRotate (n + 1)).symm i.succ = i.castSucc := by
    intro i; rw [Equiv.symm_apply_eq, finRotate_apply]; exact Fin.coeSucc_eq_succ.symm
  simp only [h0, h1]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

section Legs
variable {d L W : ℕ} [NeZero L]

/-- `E_a^{1/2} = s · 1_{[a]}` for a real `s` with `s * s = W^{-d}`, so `E_a^{1/2} E_a^{1/2} = E_a` (`Eblk`, `Loop/GLoop`). -/
private def Step5IIIEdet_Es (d L W : ℕ) (s : ℝ) (a : Zd d L) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  Matrix.diagonal fun x => if x.1 = a then (s : ℂ) else 0

private theorem Step5IIIEdet_Es_herm (s : ℝ) (a : Zd d L) : (Step5IIIEdet_Es d L W s a)ᴴ = Step5IIIEdet_Es d L W s a := by
  rw [Step5IIIEdet_Es, Matrix.diagonal_conjTranspose]
  congr 1; funext x; by_cases h : x.1 = a <;> simp [h]

private theorem Step5IIIEdet_Es_mul_self (s : ℝ) (hs : s * s = ((W : ℝ) ^ d)⁻¹) (a : Zd d L) :
    Step5IIIEdet_Es d L W s a * Step5IIIEdet_Es d L W s a = Eblk d L W a := by
  simp only [Step5IIIEdet_Es, Eblk, Matrix.diagonal_mul_diagonal]
  congr 1; funext x; split_ifs
  · rw [← Complex.ofReal_mul, hs]; push_cast; rfl
  · simp

/-- Copy of `lwWx_Gres_conjTranspose` (`Graph/LWWeightExp`): `G(σ)ᴴ = G(!σ)` for Hermitian `H`. -/
private theorem Step5IIIEdet_Gres_conj {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (z : ℂ) (σ : Bool) : (Gres H z σ)ᴴ = Gres H z (!σ) := by
  have hH' : Hᴴ = H := hH
  have h : (Gres H z true)ᴴ = Gres H z false := by
    simp only [Gres, ↓reduceIte, Bool.false_eq_true, ← Matrix.nonsing_inv_eq_ringInverse,
      Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, hH', Complex.star_def]
  cases σ
  · rw [Bool.not_false, ← h, Matrix.conjTranspose_conjTranspose]
  · simpa using h

/-- `‖E_b^{1/2} M E_a^{1/2}‖_F² = tr(M E_a Mᴴ E_b)`. -/
private theorem Step5IIIEdet_sandwich (s : ℝ) (hs : s * s = ((W : ℝ) ^ d)⁻¹) (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) (a b : Zd d L) :
    (((‖Step5IIIEdet_Es d L W s b * M * Step5IIIEdet_Es d L W s a‖ ^ 2 : ℝ)) : ℂ) = (M * Eblk d L W a * Mᴴ * Eblk d L W b).trace := by
  rw [Step5IIIEdet_frob_sq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Step5IIIEdet_Es_herm, Step5IIIEdet_Es_herm,
    ← Step5IIIEdet_Es_mul_self s hs a, ← Step5IIIEdet_Es_mul_self s hs b]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (Step5IIIEdet_Es d L W s b)]
  simp only [Matrix.mul_assoc]

/-- The leg identity: `‖E_b^{1/2} G(σ) E_a^{1/2}‖_F² = 𝓛^{(2)}_{(σ,!σ),(a,b)}` for Hermitian `H`. -/
theorem Step5IIIEdet_leg_identity (s : ℝ) (hs : s * s = ((W : ℝ) ^ d)⁻¹) {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) (z : ℂ) (σ : Bool) (a b : Zd d L) :
    loopM d L W H z ![σ, !σ] ![a, b] =
      (((‖Step5IIIEdet_Es d L W s b * Gres H z σ * Step5IIIEdet_Es d L W s a‖ ^ 2 : ℝ)) : ℂ) := by
  rw [Step5IIIEdet_sandwich s hs, Step5IIIEdet_Gres_conj hH]
  simp [loopM, List.ofFn_succ, Matrix.mul_assoc]

/-- The glue identity: `‖X_p X_{p+1}‖_F² = 𝓛^{(4)}_{(σ₁,σ₂,!σ₂,!σ₁),(a₁,a₂,a₁,a₀)}` for `X_p = E_{a₀}^{1/2} G(σ₁) E_{a₁}^{1/2}`,
`X_{p+1} = E_{a₁}^{1/2} G(σ₂) E_{a₂}^{1/2}`. -/
theorem Step5IIIEdet_glue_identity (s : ℝ) (hs : s * s = ((W : ℝ) ^ d)⁻¹) {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) (z : ℂ) (σ₁ σ₂ : Bool) (a₀ a₁ a₂ : Zd d L) :
    loopM d L W H z ![σ₁, σ₂, !σ₂, !σ₁] ![a₁, a₂, a₁, a₀] =
      (((‖(Step5IIIEdet_Es d L W s a₀ * Gres H z σ₁ * Step5IIIEdet_Es d L W s a₁) *
        (Step5IIIEdet_Es d L W s a₁ * Gres H z σ₂ * Step5IIIEdet_Es d L W s a₂)‖ ^ 2 : ℝ)) : ℂ) := by
  have h : (Step5IIIEdet_Es d L W s a₀ * Gres H z σ₁ * Step5IIIEdet_Es d L W s a₁) *
      (Step5IIIEdet_Es d L W s a₁ * Gres H z σ₂ * Step5IIIEdet_Es d L W s a₂) =
      Step5IIIEdet_Es d L W s a₀ * (Gres H z σ₁ * Eblk d L W a₁ * Gres H z σ₂) * Step5IIIEdet_Es d L W s a₂ := by
    rw [← Step5IIIEdet_Es_mul_self s hs a₁]; simp only [Matrix.mul_assoc]
  rw [h, Step5IIIEdet_sandwich s hs]
  simp only [Matrix.conjTranspose_mul, (Eblk_isHermitian a₁).eq, Step5IIIEdet_Gres_conj hH]
  simp [loopM, List.ofFn_succ, Matrix.mul_assoc]

/-- The loop bound at the block-product index: `‖𝓛^{(k)}_{σ,a}‖ ≤ ∏_i ‖X_i‖_F = ∏_i √‖𝓛^{(2)}_{(σ_i,!σ_i),(a_i,a_{i-1})}‖`,
`H` Hermitian, `k ≥ 2`. -/
theorem Step5IIIEdet_loopM_hs {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian) (z : ℂ)
    {k : ℕ} (hk : 2 ≤ k) (σ : Fin k → Bool) (a : Fin k → Zd d L) :
    ‖loopM d L W H z σ a‖ ≤
      ∏ i : Fin k, Real.sqrt ‖loopM d L W H z ![σ i, !(σ i)] ![a i, a ((finRotate k).symm i)]‖ := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s * s = ((W : ℝ) ^ d)⁻¹ := ⟨Real.sqrt _, Real.mul_self_sqrt (by positivity)⟩
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have h1 := Step5IIIEdet_trace_rot (fun i => Gres H z (σ i)) (fun i => Step5IIIEdet_Es d L W s (a i))
  simp only [Step5IIIEdet_Es_mul_self s hs] at h1
  have h2 : loopM d L W H z σ a = _ := h1
  rw [h2]
  refine (baStep5IIIE_trace_prod_le _ (by simpa using hk)).trans (le_of_eq ?_)
  rw [List.map_ofFn, List.prod_ofFn]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Function.comp_apply, Step5IIIEdet_leg_identity s hs hH, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]

/-- The glue form at the block-product index: `‖𝓛^{(6)}_{σ,a}‖ ≤ ‖X_p X_{p+1}‖_F ∏_{j=2}^{5} ‖X_{p+j}‖_F`. -/
theorem Step5IIIEdet_loopM_glue {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian) (z : ℂ)
    (σ : Fin 6 → Bool) (a : Fin 6 → Zd d L) (p : Fin 6) :
    ‖loopM d L W H z σ a‖ ≤
      Real.sqrt ‖loopM d L W H z ![σ p, σ (p + 1), !(σ (p + 1)), !(σ p)] ![a p, a (p + 1), a p, a (p - 1)]‖ *
        ∏ j ∈ ({2, 3, 4, 5} : Finset (Fin 6)),
          Real.sqrt ‖loopM d L W H z ![σ (p + j), !(σ (p + j))] ![a (p + j), a (p + j - 1)]‖ := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s * s = ((W : ℝ) ^ d)⁻¹ := ⟨Real.sqrt _, Real.mul_self_sqrt (by positivity)⟩
  set X : Fin 6 → Matrix (Vtx d L W) (Vtx d L W) ℂ :=
    fun i => Step5IIIEdet_Es d L W s (a (i - 1)) * Gres H z (σ i) * Step5IIIEdet_Es d L W s (a i) with hX
  have h1 := Step5IIIEdet_trace_rot (n := 5) (fun i => Gres H z (σ i)) (fun i => Step5IIIEdet_Es d L W s (a i))
  simp only [Step5IIIEdet_Es_mul_self s hs, finRotate_symm_apply] at h1
  have h2 : loopM d L W H z σ a = (List.ofFn X).prod.trace := h1
  have h3 : (List.ofFn X).rotate p.val = [X p, X (p + 1), X (p + 2), X (p + 3), X (p + 4), X (p + 5)] := by
    fin_cases p <;> rfl
  have h4 : (List.ofFn X).prod.trace = [X p * X (p + 1), X (p + 2), X (p + 3), X (p + 4), X (p + 5)].prod.trace := by
    rw [← Step5IIIEdet_trace_rotate (List.ofFn X) p.val, h3]; simp [mul_assoc]
  have hleg : ∀ i, Real.sqrt ‖loopM d L W H z ![σ i, !(σ i)] ![a i, a (i - 1)]‖ = ‖X i‖ := fun i => by
    rw [Step5IIIEdet_leg_identity s hs hH, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  have hY : Real.sqrt ‖loopM d L W H z ![σ p, σ (p + 1), !(σ (p + 1)), !(σ p)] ![a p, a (p + 1), a p, a (p - 1)]‖ =
      ‖X p * X (p + 1)‖ := by
    rw [Step5IIIEdet_glue_identity s hs hH, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    simp [hX]
  rw [h2, h4, hY]
  refine (baStep5IIIE_trace_prod_le _ (by simp)).trans (le_of_eq ?_)
  simp [Finset.prod_insert, hleg]

end Legs

end HS

/-! ### The loops of the BA carrier: the loop bound, its list and glue forms, the swap -/

/-- The loop bound at the BA carrier.  `(baStep2Mat ..).LM` is `loopM` of `blockMat H` by unfolding,
and `blockMat H` is Hermitian (`Matrix.IsHermitian.submatrix`). -/
theorem baStep5IIIE_loop_hs (d : ℕ) (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hH : H.IsHermitian)
    (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) (hk : 2 ≤ k) :
    ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤
      ∏ i : Fin k, Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![σ i, !(σ i)] ![a i, a ((finRotate k).symm i)]‖ :=
  Step5IIIEdet_loopM_hs (hH.submatrix _) _ hk σ a

/-- The glue form of the loop bound: two adjacent legs `p, p+1` are kept as one factor, the 4-loop
`‖X_p X_{p+1}‖_F² = 𝓛^{(4)}_{(σ_p,σ_{p+1},!σ_{p+1},!σ_p),(a_p,a_{p+1},a_p,a_{p-1})}`; the other four legs are `p+2, ..., p+5`. -/
theorem baStep5IIIE_loop_glue (d : ℕ) (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hH : H.IsHermitian)
    (σ : Fin 6 → Bool) (a : Fin 6 → Zd d (sz.L n)) (p : Fin 6) :
    ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤
      Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![σ p, σ (p + 1), !(σ (p + 1)), !(σ p)] ![a p, a (p + 1), a p, a (p - 1)]‖ *
        ∏ j ∈ ({2, 3, 4, 5} : Finset (Fin 6)),
          Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![σ (p + j), !(σ (p + j))] ![a (p + j), a (p + j - 1)]‖ :=
  Step5IIIEdet_loopM_glue (hH.submatrix _) _ σ a p

/-- The swap (cyclicity of the 2-loop): `𝓛^{(2)}_{(σ,τ),(a,b)} = 𝓛^{(2)}_{(τ,σ),(b,a)}`; at `τ = !σ` every leg is a `(+,-)` loop. -/
theorem Step5IIIEdet_swap {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ τ : Bool) (a b : Zd d (sz.L n)) :
    (baStep2Mat sz lam0 E).LM n u H ![σ, τ] ![a, b] = (baStep2Mat sz lam0 E).LM n u H ![τ, σ] ![b, a] := by
  simp only [baStep2Mat, loopFine, loopM, List.ofFn_succ, Matrix.cons_val_zero, Matrix.cons_val_one, List.ofFn_zero, List.prod_cons,
    List.prod_nil, Matrix.mul_one, Fin.succ_zero_eq_one]
  exact Matrix.trace_mul_comm _ _

/-! ## 2. The premise bundle -/

/-- The scalar part of the bundle: the band
bundle of `Path/LemDecCalE` without its entry-level conjuncts and the energy bound; `J ≤ W^{1/2}`. -/
def BAStep5IIIEScalar {d : ℕ} (sz : Sizes d) (n : ℕ) (u D Λ K₀ J : ℝ) : Prop :=
  3 ≤ d ∧ 0 ≤ u ∧ u < 1 ∧ 0 < sz.lam n ∧ sz.lam n ^ 2 ≤ 1 - u ∧ 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d ∧ 1 ≤ Λ ∧ 1 ≤ K₀ ∧
    4 ≤ Real.log ((sz.W n : ℕ) : ℝ) ∧ (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D ∧
    1 ≤ J ∧ J ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ)

/-- The matrix part of the bundle at `baStep2Mat`:
`H` Hermitian; (i) the stopped control; (ii) `‖𝒦^{(2)}_{(+,-)}‖ ≤ K₀ M_u⁻¹`; (iii) its far field at `ℓ* = (log W)^{3/2}`;
(iv) `STavgMg`; (v) `𝓛^{(k)}`, `k = 2, 3, 4, 6`; (vi) the `J`-free decay of `(𝓛-𝒦)^{(2)}`. -/
def BAStep5IIIEMatrix {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u D Λ K₀ J θ Cd : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : Prop :=
  H.IsHermitian ∧ (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STLKMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤ J * STtailTD sz n u D a) ∧
  (∀ a b : Zd d (sz.L n), ‖(baStep2Mat sz lam0 E).K n u ![true, false] ![a, b]‖ ≤ K₀ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ∧
  (∀ a b : Zd d (sz.L n), Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (a - b) : ℝ) →
    ‖(baStep2Mat sz lam0 E).K n u ![true, false] ![a, b]‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D)) ∧
  (∀ (σ : Bool) (a : Zd d (sz.L n)), ‖STavgMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤ Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ∧
  (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤ Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ∧
  (∀ (σ : Fin 3 → Bool) (a : Fin 3 → Zd d (sz.L n)), ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2) ∧
  (∀ (σ : Fin 4 → Bool) (a : Fin 4 → Zd d (sz.L n)), ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 3) ∧
  (∀ (σ : Fin 6 → Bool) (a : Fin 6 → Zd d (sz.L n)), ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 5) ∧
  (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STLKMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (θ * (d * (Cd + 1))) * Λ *
    ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 * Real.exp (-(θ * Real.sqrt (zdistInf d (sz.L n) (a 0 - a 1) : ℝ))) + ((sz.W n : ℕ) : ℝ) ^ (-D))

/-! ## 3. The scalar facts under `BAStep5IIIEScalar` and the tail `T_{u,D}` -/

section Scalar

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {u D Λ K₀ J : ℝ}

theorem Step5IIIEdet_W_pos (sz : Sizes d) (n : ℕ) : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by
  exact_mod_cast sz.W_pos n

/-- `W > 1` from `4 ≤ log W`. -/
theorem Step5IIIEdet_W_gt_one (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) : (1 : ℝ) < ((sz.W n : ℕ) : ℝ) := by
  obtain ⟨-, -, -, -, -, -, -, -, hlog, -⟩ := hs
  by_contra hcon
  have := Real.log_nonpos (Step5IIIEdet_W_pos sz n).le (not_lt.1 hcon)
  linarith

/-- `1 ≤ M_u ≤ W^d` for `M_u = W^d (1-u)`. -/
theorem Step5IIIEdet_Mu (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) :
    1 ≤ ((sz.W n : ℕ) : ℝ) ^ d * (1 - u) ∧ ((sz.W n : ℕ) : ℝ) ^ d * (1 - u) ≤ ((sz.W n : ℕ) : ℝ) ^ d := by
  obtain ⟨-, hu0, hu1, hlam, hlamu, hlamW, -⟩ := hs
  have hWd : 0 < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos (Step5IIIEdet_W_pos sz n) d
  refine ⟨?_, ?_⟩
  · calc (1 : ℝ) ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d := hlamW
      _ ≤ (1 - u) * ((sz.W n : ℕ) : ℝ) ^ d := mul_le_mul_of_nonneg_right hlamu hWd.le
      _ = ((sz.W n : ℕ) : ℝ) ^ d * (1 - u) := by ring
  · nlinarith

/-- `0 < τ ≤ 1` for `τ = M_u⁻¹ = (W^d (1-u))⁻¹`. -/
theorem Step5IIIEdet_tau_le_one (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) :
    0 < (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ∧ (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ≤ 1 := by
  have h := (Step5IIIEdet_Mu hs).1
  exact ⟨inv_pos.2 (by linarith), inv_le_one_of_one_le₀ h⟩

/-- The floor: `W^{-D} L^{2d} ≤ τ²` (from `(L^d W^{6d})² ≤ W^D`; it gives the floors of `LemDecCalE_sum_tail_tail` and of
`LemDecCalEwG_sum_sqrt_tail`). -/
theorem Step5IIIEdet_floor (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) :
    ((sz.W n : ℕ) : ℝ) ^ (-D) * ((sz.L n : ℕ) : ℝ) ^ (2 * d) ≤ ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 := by
  have h2 := Step5IIIEdet_Mu hs
  have hW0 := Step5IIIEdet_W_pos sz n
  obtain ⟨hd3, hu0, hu1, hlam, hlamu, hlamW, hΛ, hK, hlog, hfloor, -⟩ := hs
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (sz.three_le_L n).trans_lt' (by norm_num)
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by
    by_contra hcon
    have := Real.log_nonpos hW0.le (not_le.1 hcon).le
    linarith
  have hMu : 0 < ((sz.W n : ℕ) : ℝ) ^ d * (1 - u) := by linarith [h2.1]
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := pow_pos hL0 d
  have hW6 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ (6 * d) := pow_pos hW0 _
  have hWD : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ D := Real.rpow_pos_of_pos hW0 _
  have h1 : ((sz.W n : ℕ) : ℝ) ^ (-D) ≤ ((((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hW0.le]
    exact inv_anti₀ (by positivity) hfloor
  have h3 : ((((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2)⁻¹ * ((sz.L n : ℕ) : ℝ) ^ (2 * d) =
      (((sz.W n : ℕ) : ℝ) ^ (12 * d))⁻¹ := by
    field_simp
    ring
  have h4 : (((sz.W n : ℕ) : ℝ) ^ (12 * d))⁻¹ ≤ (((sz.W n : ℕ) : ℝ) ^ (2 * d))⁻¹ :=
    inv_anti₀ (pow_pos hW0 _) (pow_le_pow_right₀ hW1 (by omega))
  have h5 : (((sz.W n : ℕ) : ℝ) ^ (2 * d))⁻¹ ≤ ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 := by
    rw [pow_mul', ← inv_pow]
    exact pow_le_pow_left₀ (by positivity) (inv_anti₀ hMu h2.2) 2
  calc ((sz.W n : ℕ) : ℝ) ^ (-D) * ((sz.L n : ℕ) : ℝ) ^ (2 * d)
      ≤ ((((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2)⁻¹ * ((sz.L n : ℕ) : ℝ) ^ (2 * d) :=
        mul_le_mul_of_nonneg_right h1 (pow_pos hL0 _).le
    _ = (((sz.W n : ℕ) : ℝ) ^ (12 * d))⁻¹ := h3
    _ ≤ _ := h4.trans h5

/-- The floor of `LemDecCalE_sum_tail_tail`: `W^{-D} L^d ≤ τ²`. -/
theorem Step5IIIEdet_floor_one (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) :
    ((sz.W n : ℕ) : ℝ) ^ (-D) * ((sz.L n : ℕ) : ℝ) ^ d ≤ ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 := by
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (sz.three_le_L n).trans' (by norm_num)
  have hwn : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg (Step5IIIEdet_W_pos sz n).le _
  refine le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 (by omega)) hwn) (Step5IIIEdet_floor hs)

/-- `T_{u,D}(r) = τ² e^{-√r} + W^{-D}` for `u < 1`. -/
theorem Step5IIIEdet_tail_eq {W u D : ℝ} (hu : u < 1) (r : ℝ) :
    tailTD d W u D r = ((W ^ d * (1 - u))⁻¹) ^ 2 * Real.exp (-Real.sqrt r) + W ^ (-D) := by
  unfold tailTD
  rw [abs_of_pos (by linarith)]

/-- `W^{-D} ≤ T_{u,D}(r)` and `τ² e^{-√r} ≤ T_{u,D}(r)`. -/
theorem Step5IIIEdet_tail_ge {W u D : ℝ} (hW : 0 ≤ W) (hu : u < 1) (r : ℝ) :
    W ^ (-D) ≤ tailTD d W u D r ∧ ((W ^ d * (1 - u))⁻¹) ^ 2 * Real.exp (-Real.sqrt r) ≤ tailTD d W u D r := by
  have h0 := Real.rpow_nonneg hW (-D)
  have h1 : 0 ≤ ((W ^ d * (1 - u))⁻¹) ^ 2 * Real.exp (-Real.sqrt r) := by positivity
  rw [Step5IIIEdet_tail_eq hu]
  exact ⟨by linarith, by linarith⟩

theorem Step5IIIEdet_u_lt_one (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) : u < 1 := hs.2.2.1
theorem Step5IIIEdet_one_le_Λ (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) : 1 ≤ Λ := hs.2.2.2.2.2.2.1
theorem Step5IIIEdet_one_le_K₀ (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) : 1 ≤ K₀ := hs.2.2.2.2.2.2.2.1
theorem Step5IIIEdet_log_ge_four (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) : 4 ≤ Real.log ((sz.W n : ℕ) : ℝ) :=
  hs.2.2.2.2.2.2.2.2.1
theorem Step5IIIEdet_one_le_J (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) : 1 ≤ J := hs.2.2.2.2.2.2.2.2.2.2.1

/-- The loss budget: `lossE2wG` dominates `10¹² (1.6·10⁶ d⁴)^d Λ⁶ e^{8Y} (1 + log P)^{2d}` with `P = L^d W^{6d}`,
`Y = (log W)^{3/4}` (the other factors `K₀²`, `(1 + log(L^d W^{2d}))⁴`, `(1 + log W)³` of `lossE2` are `≥ 1`). -/
theorem Step5IIIEdet_loss_ge (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) :
    10 ^ 12 * (1600 * (d : ℝ) ^ 4 * 1000) ^ d * Λ ^ 6 * Real.exp (8 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) *
        (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d))) ^ (2 * d) ≤
      lossE2wG d (sz.L n) (sz.W n) Λ K₀ := by
  have hK := Step5IIIEdet_one_le_K₀ hs
  have hlog := Step5IIIEdet_log_ge_four hs
  have hW0 := Step5IIIEdet_W_pos sz n
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := (Step5IIIEdet_W_gt_one hs).le
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (sz.three_le_L n).trans' (by norm_num)
  have hbase : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) (one_le_pow₀ hW1)
  have hQ : (1 : ℝ) ≤ (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d))) ^ 4 :=
    one_le_pow₀ (by linarith [Real.log_nonneg hbase])
  have hCw : (1 : ℝ) ≤ (1 + Real.log ((sz.W n : ℕ) : ℝ)) ^ 3 := one_le_pow₀ (by linarith)
  have hK2 : (1 : ℝ) ≤ K₀ ^ 2 := one_le_pow₀ hK
  have hprod : (1 : ℝ) ≤ K₀ ^ 2 * (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d))) ^ 4 *
      (1 + Real.log ((sz.W n : ℕ) : ℝ)) ^ 3 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK2 hQ) hCw
  have hΛ0 : (0 : ℝ) ≤ Λ := by linarith [Step5IIIEdet_one_le_Λ hs]
  unfold lossE2wG lossE2
  rw [mul_pow]
  set X := Real.exp (8 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4))
  set G := (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d))) ^ (2 * d)
  set Pr := K₀ ^ 2 * (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d))) ^ 4 *
      (1 + Real.log ((sz.W n : ℕ) : ℝ)) ^ 3
  have hX : 0 ≤ X := (Real.exp_pos _).le
  have hP1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) (one_le_pow₀ hW1)
  have hG : 0 ≤ G := pow_nonneg (by linarith [Real.log_nonneg hP1]) _
  have hpos : 0 ≤ 10 ^ 12 * ((1600 * (d : ℝ) ^ 4) ^ d * 1000 ^ d) * Λ ^ 6 * X * G := by positivity
  calc 10 ^ 12 * ((1600 * (d : ℝ) ^ 4) ^ d * 1000 ^ d) * Λ ^ 6 * X * G
      = 10 ^ 12 * ((1600 * (d : ℝ) ^ 4) ^ d * 1000 ^ d) * Λ ^ 6 * X * G * 1 := (mul_one _).symm
    _ ≤ 10 ^ 12 * ((1600 * (d : ℝ) ^ 4) ^ d * 1000 ^ d) * Λ ^ 6 * X * G * Pr := mul_le_mul_of_nonneg_left hprod hpos
    _ = _ := by ring

end Scalar

/-! ## 4. The legs: `‖𝓛^{(2)}_{(σ,!σ),(a,b)}‖` from the matrix bundle -/

section LegBounds

variable {d : ℕ} {sz : Sizes d} {lam0 E : ℕ → ℝ} {n : ℕ} {u D Λ K₀ J θ Cd : ℝ}
  {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- Every leg is at most `Λ τ` (bundle (v), `k = 2`). -/
theorem Step5IIIEdet_leg_short (hm : BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ J θ Cd H) (σ : Bool) (a b : Zd d (sz.L n)) :
    ‖(baStep2Mat sz lam0 E).LM n u H ![σ, !σ] ![a, b]‖ ≤ Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ :=
  hm.2.2.2.2.2.1 ![σ, !σ] ![a, b]

/-- The `(+,-)` leg at distance `≥ ℓ*`: `‖𝓛‖ ≤ ‖𝓛 - 𝒦‖ + ‖𝒦‖ ≤ J T(|a-b|) + W^{-D}` (bundle (i), (iii)). -/
theorem Step5IIIEdet_leg_plus (hm : BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ J θ Cd H) (a b : Zd d (sz.L n))
    (h : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (a - b) : ℝ)) :
    ‖(baStep2Mat sz lam0 E).LM n u H ![true, false] ![a, b]‖ ≤
      J * tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a - b) : ℝ) + ((sz.W n : ℕ) : ℝ) ^ (-D) := by
  have e : (baStep2Mat sz lam0 E).LM n u H ![true, false] ![a, b] =
      STLKMg (baStep2Mat sz lam0 E) n u H ![true, false] ![a, b] + (baStep2Mat sz lam0 E).K n u ![true, false] ![a, b] := by
    simp [STLKMg, STLMg]
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ (hm.2.2.2.1 a b h))
  have := hm.2.1 ![true, false] ![a, b]
  simpa [STtailTD] using this

/-- Every leg at distance `≥ ℓ*` is at most `2 J T_{u,D}(|a-b|)`: the charge `(-,+)` is the swap of `(+,-)`
(`Step5IIIEdet_swap`), so the bundle's `(+,-)` conjuncts (i), (iii) cover every leg; `W^{-D} ≤ T ≤ J T`. -/
theorem Step5IIIEdet_leg_long (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) (hm : BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ J θ Cd H)
    (σ : Bool) (a b : Zd d (sz.L n)) (h : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (a - b) : ℝ)) :
    ‖(baStep2Mat sz lam0 E).LM n u H ![σ, !σ] ![a, b]‖ ≤
      2 * J * tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a - b) : ℝ) := by
  have hJ1 := Step5IIIEdet_one_le_J hs
  have key : ∀ a b : Zd d (sz.L n), Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (a - b) : ℝ) →
      ‖(baStep2Mat sz lam0 E).LM n u H ![true, false] ![a, b]‖ ≤
        2 * J * tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a - b) : ℝ) := by
    intro a b h
    refine (Step5IIIEdet_leg_plus hm a b h).trans ?_
    have hT := (Step5IIIEdet_tail_ge (d := d) (D := D) (Step5IIIEdet_W_pos sz n).le (Step5IIIEdet_u_lt_one hs)
      (zdistInf d (sz.L n) (a - b) : ℝ)).1
    have hT0 : 0 ≤ tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a - b) : ℝ) := hT.trans' (Real.rpow_nonneg (Step5IIIEdet_W_pos sz n).le _)
    nlinarith
  cases σ
  · simp only [Bool.not_false]
    rw [Step5IIIEdet_swap sz lam0 E n u H false true a b]
    have h' : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (b - a) : ℝ) := by
      rwa [lemDecCalE_zdistInf_sub_comm]
    have := key b a h'
    rwa [lemDecCalE_zdistInf_sub_comm] at this
  · simpa using key a b h

/-- The loop bound for `k = 3` through the three legs (the loop bound at `k = 3`; `(finRotate 3).symm` is `0 ↦ 2, 1 ↦ 0, 2 ↦ 1`). -/
theorem Step5IIIEdet_loop3_legs (hH : H.IsHermitian) (σ : Fin 3 → Bool) (b : Fin 3 → Zd d (sz.L n)) :
    ‖(baStep2Mat sz lam0 E).LM n u H σ b‖ ≤
      Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![σ 0, !(σ 0)] ![b 0, b 2]‖ *
        Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![σ 1, !(σ 1)] ![b 1, b 0]‖ *
          Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![σ 2, !(σ 2)] ![b 2, b 1]‖ := by
  have h := baStep5IIIE_loop_hs d sz lam0 E n u H hH 3 σ b (by norm_num)
  have e0 : (finRotate 3).symm 0 = 2 := by decide
  have e1 : (finRotate 3).symm 1 = 0 := by decide
  have e2 : (finRotate 3).symm 2 = 1 := by decide
  have e3 : (-1 : Fin 3) = 2 := by decide
  simpa [Fin.prod_univ_three, e0, e1, e2, e3] using h

end LegBounds

/-! ## 5. `res_deccalE_lk` (5.43) -/

section LK

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {u D Λ K₀ J : ℝ}

/-- The convolution constant of `res_deccalE_lk` (5.43) against the loss: `2 S_d + 1 ≤ lossE2wG`, `S_d = (1 + 1536 d⁴)^d`. -/
theorem Step5IIIEdet_lk_const (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) :
    2 * (1 + 1536 * (d : ℝ) ^ 4) ^ d + 1 ≤ lossE2wG d (sz.L n) (sz.W n) Λ K₀ := by
  have h := Step5IIIEdet_loss_ge hs
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by have := hs.1; omega : 1 ≤ d)
  have hd4 : (1 : ℝ) ≤ (d : ℝ) ^ 4 := one_le_pow₀ hd1
  have hΛ6 : (1 : ℝ) ≤ Λ ^ 6 := one_le_pow₀ (Step5IIIEdet_one_le_Λ hs)
  have hlog := Step5IIIEdet_log_ge_four hs
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := (Step5IIIEdet_W_gt_one hs).le
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (sz.three_le_L n).trans' (by norm_num)
  have hX : (1 : ℝ) ≤ Real.exp (8 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) :=
    Real.one_le_exp (by have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ)) ((3 : ℝ) / 4); linarith)
  have hP1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) (one_le_pow₀ hW1)
  have hG : (1 : ℝ) ≤ (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d))) ^ (2 * d) :=
    one_le_pow₀ (by linarith [Real.log_nonneg hP1])
  have hS : (1 + 1536 * (d : ℝ) ^ 4) ^ d ≤ (1600 * (d : ℝ) ^ 4 * 1000) ^ d :=
    pow_le_pow_left₀ (by positivity) (by nlinarith) d
  have hS1 : (1 : ℝ) ≤ (1 + 1536 * (d : ℝ) ^ 4) ^ d := one_le_pow₀ (by nlinarith)
  have hc : (0 : ℝ) ≤ 10 ^ 12 * (1600 * (d : ℝ) ^ 4 * 1000) ^ d := by positivity
  refine le_trans ?_ h
  have h1 : 10 ^ 12 * (1600 * (d : ℝ) ^ 4 * 1000) ^ d ≤ 10 ^ 12 * (1600 * (d : ℝ) ^ 4 * 1000) ^ d * Λ ^ 6 *
      Real.exp (8 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) *
        (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d))) ^ (2 * d) := by
    calc _ = 10 ^ 12 * (1600 * (d : ℝ) ^ 4 * 1000) ^ d * 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  refine le_trans ?_ h1
  nlinarith

/-- `res_deccalE_lk` (5.43) at BA.  Chain: `S = 1` collapses `ℰ^{(𝓛-𝒦)×(𝓛-𝒦)}` to `W^d Σ_x LK_{(x,a₂)} LK_{(a₁,x)}`; (i) bounds
both factors by `J T`; `LemDecCalE_sum_tail_tail` (`A = τ²`, floor `W^{-D} L^d ≤ τ²`) gives `(2 S_d + 1) τ² T(|a₁-a₂|)`;
`W^d τ² = (1-u)⁻¹ τ` (`LemDecCalE_e1`); `2 S_d + 1 ≤ lossE2wG`. -/
theorem baStep5IIIE_lk (d : ℕ) (hd : 3 ≤ d) (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u D Λ K₀ J θ Cd : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hθ : 0 < θ) (hCd : 0 < Cd)
    (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) (hm : BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ J θ Cd H)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ‖STELKLKMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤
      lossE2wG d (sz.L n) (sz.W n) Λ K₀ * ((1 - u)⁻¹ * ((((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ * J ^ 2)) * STtailTD sz n u D a := by
  have hu1 := Step5IIIEdet_u_lt_one hs
  have hx : 0 < 1 - u := by linarith
  have hW0 := Step5IIIEdet_W_pos sz n
  have hJ1 := Step5IIIEdet_one_le_J hs
  have hS : (baStep2Mat sz lam0 E).S n = 1 := rfl
  have hTD : ∀ r : ℝ, tailTD d ((sz.W n : ℕ) : ℝ) u D r =
      ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 * Real.exp (-Real.sqrt r) + ((sz.W n : ℕ) : ℝ) ^ (-D) :=
    fun r => Step5IIIEdet_tail_eq hu1 r
  have hTnn : ∀ r : ℝ, 0 ≤ tailTD d ((sz.W n : ℕ) : ℝ) u D r := fun r => tailTD_nonneg hW0.le
  --   -- step 1: `S = 1` collapses the double sum
  have hred : STELKLKMg (baStep2Mat sz lam0 E) n u H σ a = (((sz.W n : ℕ) : ℂ) ^ d) * ∑ x : Zd d (sz.L n),
      STLKMg (baStep2Mat sz lam0 E) n u H σ ![x, a 1] * STLKMg (baStep2Mat sz lam0 E) n u H σ ![a 0, x] := by
    unfold STELKLKMg
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [hS, Matrix.one_apply]
  have hnorm : ‖STELKLKMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d * ∑ x : Zd d (sz.L n),
      ‖STLKMg (baStep2Mat sz lam0 E) n u H σ ![x, a 1]‖ * ‖STLKMg (baStep2Mat sz lam0 E) n u H σ ![a 0, x]‖ := by
    rw [hred, norm_mul]
    have hw : ‖(((sz.W n : ℕ) : ℂ) ^ d)‖ = ((sz.W n : ℕ) : ℝ) ^ d := by simp
    rw [hw]
    gcongr
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [norm_mul]
  --   -- step 2: the bundle (i) at both factors
  have hlk : ∀ b₀ b₁ : Zd d (sz.L n), ‖STLKMg (baStep2Mat sz lam0 E) n u H σ ![b₀, b₁]‖ ≤
      J * tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (b₀ - b₁) : ℝ) := by
    intro b₀ b₁
    have := hm.2.1 σ ![b₀, b₁]
    simpa [STtailTD] using this
  have hsum : ∑ x : Zd d (sz.L n), ‖STLKMg (baStep2Mat sz lam0 E) n u H σ ![x, a 1]‖ *
        ‖STLKMg (baStep2Mat sz lam0 E) n u H σ ![a 0, x]‖ ≤
      J ^ 2 * ∑ x : Zd d (sz.L n), tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (x - a 1) : ℝ) *
        tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - x) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    have h1 := hlk x (a 1)
    have h2 := hlk (a 0) x
    have hJ0 : 0 ≤ J := by linarith
    calc _ ≤ (J * tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (x - a 1) : ℝ)) *
          (J * tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - x) : ℝ)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hJ0 (hTnn _))
      _ = _ := by ring
  --   -- step 3: the convolution of two tails
  have hAnn : 0 ≤ ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 := sq_nonneg _
  have hwnn : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  have hconv := LemDecCalE_sum_tail_tail (d := d) (L := sz.L n) (by omega) hAnn hwnn (Step5IIIEdet_floor_one hs) (a 0) (a 1)
  simp only [← hTD] at hconv
  --   -- step 4: assemble
  have hcoef : ((sz.W n : ℕ) : ℝ) ^ d * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 =
      (1 - u)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ := by
    have := LemDecCalE_e1 d hW0 hu1
    rw [abs_of_pos hx] at this ⊢
    exact this
  have hTr : STtailTD sz n u D a = tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) := rfl
  set Tr := tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) with hTrdef
  set Aq := ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 with hAq
  set S := 2 * (1 + 1536 * (d : ℝ) ^ 4) ^ d + 1 with hSdef
  have hWd : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hmain : ‖STELKLKMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤ S * (((sz.W n : ℕ) : ℝ) ^ d * Aq * J ^ 2 * Tr) := by
    calc _ ≤ ((sz.W n : ℕ) : ℝ) ^ d * (J ^ 2 * (S * Aq * Tr)) := by
          refine hnorm.trans ?_
          gcongr
          exact hsum.trans (mul_le_mul_of_nonneg_left hconv (sq_nonneg J))
      _ = _ := by ring
  have hpos : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ d * Aq * J ^ 2 * Tr := by
    have := hTnn (zdistInf d (sz.L n) (a 0 - a 1) : ℝ)
    positivity
  refine hmain.trans ?_
  rw [hTr]
  calc S * (((sz.W n : ℕ) : ℝ) ^ d * Aq * J ^ 2 * Tr)
      ≤ lossE2wG d (sz.L n) (sz.W n) Λ K₀ * (((sz.W n : ℕ) : ℝ) ^ d * Aq * J ^ 2 * Tr) :=
        mul_le_mul_of_nonneg_right (Step5IIIEdet_lk_const hs) hpos
    _ = _ := by
      have : ((sz.W n : ℕ) : ℝ) ^ d * Aq * J ^ 2 * Tr =
          ((1 - u)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ * J ^ 2) * Tr := by rw [hcoef]
      rw [this]; ring

end LK

/-! ## 6. `res_deccalE_wG` (5.44) -/

section WGReal

/-! ### 6.1 Real-number lemmas for the pointwise bounds of the three-loops -/

/-- Two long legs (the `x`-legs, both at distance `≥ ℓ*`) and one arbitrary leg (`≤ A`):
`√Γp √Γq √Γr ≤ 2J √A √Tp √Tq` (`J`-power `1`). -/
theorem Step5IIIEdet_pt_far2 {Γp Γq Γr Tp Tq A J : ℝ} (hJ : 1 ≤ J)
    (hp : Γp ≤ 2 * J * Tp) (hq : Γq ≤ 2 * J * Tq) (hr : Γr ≤ A) :
    Real.sqrt Γp * Real.sqrt Γq * Real.sqrt Γr ≤ (2 * J * Real.sqrt A) * (Real.sqrt Tp * Real.sqrt Tq) := by
  have h2J : 0 ≤ 2 * J := by linarith
  have hp' : Real.sqrt Γp ≤ Real.sqrt (2 * J) * Real.sqrt Tp := by
    rw [← Real.sqrt_mul h2J]; exact Real.sqrt_le_sqrt hp
  have hq' : Real.sqrt Γq ≤ Real.sqrt (2 * J) * Real.sqrt Tq := by
    rw [← Real.sqrt_mul h2J]; exact Real.sqrt_le_sqrt hq
  have hr' : Real.sqrt Γr ≤ Real.sqrt A := Real.sqrt_le_sqrt hr
  have hsq : Real.sqrt (2 * J) * Real.sqrt (2 * J) = 2 * J := Real.mul_self_sqrt h2J
  calc Real.sqrt Γp * Real.sqrt Γq * Real.sqrt Γr
      ≤ (Real.sqrt (2 * J) * Real.sqrt Tp) * (Real.sqrt (2 * J) * Real.sqrt Tq) * Real.sqrt A := by gcongr
    _ = (Real.sqrt (2 * J) * Real.sqrt (2 * J)) * Real.sqrt A * (Real.sqrt Tp * Real.sqrt Tq) := by ring
    _ = _ := by rw [hsq]

/-- Three long legs: `√Γp √Γq √Γr ≤ 2J √(2J) √Tr √Tp √Tq` (`J`-power `3/2`). -/
theorem Step5IIIEdet_pt_far3 {Γp Γq Γr Tp Tq Tr J : ℝ} (hJ : 1 ≤ J)
    (hp : Γp ≤ 2 * J * Tp) (hq : Γq ≤ 2 * J * Tq) (hr : Γr ≤ 2 * J * Tr) :
    Real.sqrt Γp * Real.sqrt Γq * Real.sqrt Γr ≤
      (2 * J * Real.sqrt (2 * J)) * Real.sqrt Tr * (Real.sqrt Tp * Real.sqrt Tq) := by
  have h2J : 0 ≤ 2 * J := by linarith
  have hp' : Real.sqrt Γp ≤ Real.sqrt (2 * J) * Real.sqrt Tp := by
    rw [← Real.sqrt_mul h2J]; exact Real.sqrt_le_sqrt hp
  have hq' : Real.sqrt Γq ≤ Real.sqrt (2 * J) * Real.sqrt Tq := by
    rw [← Real.sqrt_mul h2J]; exact Real.sqrt_le_sqrt hq
  have hr' : Real.sqrt Γr ≤ Real.sqrt (2 * J) * Real.sqrt Tr := by
    rw [← Real.sqrt_mul h2J]; exact Real.sqrt_le_sqrt hr
  have hsq : Real.sqrt (2 * J) * Real.sqrt (2 * J) = 2 * J := Real.mul_self_sqrt h2J
  calc Real.sqrt Γp * Real.sqrt Γq * Real.sqrt Γr
      ≤ (Real.sqrt (2 * J) * Real.sqrt Tp) * (Real.sqrt (2 * J) * Real.sqrt Tq) * (Real.sqrt (2 * J) * Real.sqrt Tr) := by gcongr
    _ = (Real.sqrt (2 * J) * Real.sqrt (2 * J)) * Real.sqrt (2 * J) * Real.sqrt Tr * (Real.sqrt Tp * Real.sqrt Tq) := by ring
    _ = _ := by rw [hsq]

/-- The ball case, `r > 2ℓ`, one `x`-leg short (`a ≤ ℓ`): the other `x`-leg is at distance `b ≥ r - ℓ > ℓ`
(`T(b) ≤ T(r - ℓ) ≤ E₁ T(r)`), the `r`-leg is long; `√Γa √Γb √Γr ≤ √A · 2 J E₁ T(r)`. -/
theorem Step5IIIEdet_pt_ball_core {Γa Γb Γr a b r ℓ A J E1 Tb Tr : ℝ} (hJ : 1 ≤ J) (hℓ : 0 ≤ ℓ) (hE1 : 1 ≤ E1)
    (hTr : 0 ≤ Tr) (hΓa : Γa ≤ A) (hΓb : ℓ ≤ b → Γb ≤ 2 * J * Tb) (hΓr : ℓ ≤ r → Γr ≤ 2 * J * Tr)
    (hTb : r - ℓ ≤ b → Tb ≤ E1 * Tr) (hab : r ≤ a + b) (ha : a ≤ ℓ) (hr : 2 * ℓ < r) :
    Real.sqrt Γa * Real.sqrt Γb * Real.sqrt Γr ≤ Real.sqrt A * (2 * J * E1 * Tr) := by
  have hb1 : r - ℓ ≤ b := by linarith
  have hb2 : ℓ ≤ b := by linarith
  have h2J : 0 ≤ 2 * J := by linarith
  have hΓb' : Γb ≤ 2 * J * E1 * Tr := by
    calc Γb ≤ 2 * J * Tb := hΓb hb2
      _ ≤ 2 * J * (E1 * Tr) := mul_le_mul_of_nonneg_left (hTb hb1) h2J
      _ = _ := by ring
  have hΓr' : Γr ≤ 2 * J * Tr := hΓr (by linarith)
  have hX : 0 ≤ 2 * J * Tr := by positivity
  have key : Real.sqrt (2 * J * E1 * Tr) * Real.sqrt (2 * J * Tr) ≤ 2 * J * E1 * Tr := by
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    have h1 : 2 * J * Tr ≤ 2 * J * E1 * Tr := by
      have : 1 * (2 * J * Tr) ≤ E1 * (2 * J * Tr) := mul_le_mul_of_nonneg_right hE1 hX
      linarith
    have h0 : 0 ≤ 2 * J * E1 * Tr := by positivity
    nlinarith
  calc Real.sqrt Γa * Real.sqrt Γb * Real.sqrt Γr
      ≤ Real.sqrt A * Real.sqrt (2 * J * E1 * Tr) * Real.sqrt (2 * J * Tr) := by
        gcongr
    _ = Real.sqrt A * (Real.sqrt (2 * J * E1 * Tr) * Real.sqrt (2 * J * Tr)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left key (Real.sqrt_nonneg _)

/-- The ball case, `r > 2ℓ`: one of the two `x`-legs is short (`p ≤ ℓ` or `q ≤ ℓ`), the other is far. -/
theorem Step5IIIEdet_pt_ball {Γp Γq Γr p q r ℓ A J E1 Tp Tq Tr : ℝ} (hJ : 1 ≤ J) (hℓ : 0 ≤ ℓ) (hE1 : 1 ≤ E1)
    (hTr : 0 ≤ Tr) (hΓp : Γp ≤ A) (hΓq : Γq ≤ A) (hlp : ℓ ≤ p → Γp ≤ 2 * J * Tp) (hlq : ℓ ≤ q → Γq ≤ 2 * J * Tq)
    (hΓr : ℓ ≤ r → Γr ≤ 2 * J * Tr) (hTp : r - ℓ ≤ p → Tp ≤ E1 * Tr) (hTq : r - ℓ ≤ q → Tq ≤ E1 * Tr)
    (hpq : r ≤ p + q) (hball : p ≤ ℓ ∨ q ≤ ℓ) (hr : 2 * ℓ < r) :
    Real.sqrt Γp * Real.sqrt Γq * Real.sqrt Γr ≤ Real.sqrt A * (2 * J * E1 * Tr) := by
  rcases hball with h | h
  · exact Step5IIIEdet_pt_ball_core hJ hℓ hE1 hTr hΓp hlq hΓr hTq hpq h hr
  · have := Step5IIIEdet_pt_ball_core (Γa := Γq) (Γb := Γp) (a := q) (b := p) hJ hℓ hE1 hTr hΓq hlp hΓr hTp
      (by linarith) h hr
    calc _ = Real.sqrt Γq * Real.sqrt Γp * Real.sqrt Γr := by ring
      _ ≤ _ := this

end WGReal

section WGScale

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {u D Λ K₀ J : ℝ}

/-- The ball count against the loss: `(2ℓ* + 1)^d ≤ (1 + log P)^{2d}`, `P = L^d W^{6d}`, `ℓ* = (log W)^{3/2}`
(`log P ≥ 6 d log W ≥ 18 log W`, `ℓ* ≤ (log W)²`). -/
theorem Step5IIIEdet_ball_le (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) :
    (2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) + 1) ^ d ≤
      (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d))) ^ (2 * d) := by
  have hlog := Step5IIIEdet_log_ge_four hs
  have hd3 := hs.1
  have hW0 := Step5IIIEdet_W_pos sz n
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (sz.three_le_L n).trans' (by norm_num)
  set x := Real.log ((sz.W n : ℕ) : ℝ) with hx
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have h1 : x ^ ((3 : ℝ) / 2) ≤ x ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le hx1 (show ((3 : ℝ) / 2) ≤ 2 by norm_num)
    simpa [Real.rpow_two] using this
  have h2 : 6 * (d : ℝ) * x ≤ Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) := by
    have hP : ((sz.W n : ℕ) : ℝ) ^ (6 * d) ≤ ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d) :=
      le_mul_of_one_le_left (pow_pos hW0 _).le (one_le_pow₀ hL1)
    have := Real.log_le_log (pow_pos hW0 _) hP
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hd3' : (3 : ℝ) ≤ d := by exact_mod_cast hd3
  have h3 : 18 * x ≤ 6 * (d : ℝ) * x := by nlinarith
  have h4 : 2 * x ^ ((3 : ℝ) / 2) + 1 ≤ (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d))) ^ 2 := by
    have : (18 * x) ^ 2 ≤ (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d))) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    nlinarith
  calc (2 * x ^ ((3 : ℝ) / 2) + 1) ^ d ≤ ((1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d))) ^ 2) ^ d :=
        pow_le_pow_left₀ (by positivity) h4 d
    _ = _ := by rw [← pow_mul]

/-- The near normalisation: for `r ≤ 2ℓ*`, `τ² ≤ e^{√2 Y} T_{u,D}(r)` with `Y = (log W)^{3/4}`
(`T(r - 2ℓ*) ≥ τ²` as the square root of a non-positive number is `0`, then `LemDecCalE_e4c`). -/
theorem Step5IIIEdet_near_norm (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) {r : ℝ}
    (hr : r ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2)) :
    ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 ≤
      Real.exp (Real.sqrt 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) * tailTD d ((sz.W n : ℕ) : ℝ) u D r := by
  have hW0 := Step5IIIEdet_W_pos sz n
  have h := LemDecCalE_e4c (d := d) (W := ((sz.W n : ℕ) : ℝ)) (u := u) (D := D) (C := 2)
    (Step5IIIEdet_W_gt_one hs).le (by norm_num) r
  refine le_trans ?_ h
  have hneg : r - 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 0 := by linarith
  rw [Step5IIIEdet_tail_eq (Step5IIIEdet_u_lt_one hs), Real.sqrt_eq_zero_of_nonpos hneg, neg_zero, Real.exp_zero, mul_one]
  have : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  linarith

/-- The far shift: for `p ≥ r - ℓ*`, `T_{u,D}(p) ≤ e^{Y} T_{u,D}(r)` (`T` non-increasing, then `LemDecCalE_e4c` at `C = 1`). -/
theorem Step5IIIEdet_shift_one (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) {r p : ℝ}
    (hp : r - Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ p) :
    tailTD d ((sz.W n : ℕ) : ℝ) u D p ≤
      Real.exp (Real.sqrt 1 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) * tailTD d ((sz.W n : ℕ) : ℝ) u D r := by
  have h1 := LemDecCalE_tailT_anti (d := d) (W := ((sz.W n : ℕ) : ℝ)) (u := u) (D := D) hp
  have h2 := LemDecCalE_e4c (d := d) (W := ((sz.W n : ℕ) : ℝ)) (u := u) (D := D) (C := 1)
    (Step5IIIEdet_W_gt_one hs).le (by norm_num) r
  rw [one_mul] at h2
  exact h1.trans h2

/-- The constants for `res_deccalE_wG` (5.44): the constant `(8 (2ℓ*+1)^d + 6 C_sq) Λ² e^{√2 Y}` is at most `lossE2wG`
(`(2ℓ*+1)^d ≤ (1+log P)^{2d}`, `C_sq = 5 (1 + 24576 d⁴)^d ≤ 5 (1.6·10⁶ d⁴)^d`, `Λ² ≤ Λ⁶`, `√2 ≤ 8`). -/
theorem Step5IIIEdet_wG_const (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) :
    (8 * (2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) + 1) ^ d + 6 * (5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d)) * Λ ^ 2 *
        Real.exp (Real.sqrt 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) ≤
      lossE2wG d (sz.L n) (sz.W n) Λ K₀ := by
  refine le_trans ?_ (Step5IIIEdet_loss_ge hs)
  have hball := Step5IIIEdet_ball_le hs
  have hlog := Step5IIIEdet_log_ge_four hs
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by have := hs.1; omega : 1 ≤ d)
  have hd4 : (1 : ℝ) ≤ (d : ℝ) ^ 4 := one_le_pow₀ hd1
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := (Step5IIIEdet_W_gt_one hs).le
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (sz.three_le_L n).trans' (by norm_num)
  have hΛ1 := Step5IIIEdet_one_le_Λ hs
  have hY : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4) :=
    Real.rpow_nonneg (by linarith) _
  have hP1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) (one_le_pow₀ hW1)
  set G := (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d))) ^ (2 * d) with hG
  set c := (1600 * (d : ℝ) ^ 4 * 1000) ^ d with hc
  set Bd := (2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) + 1) ^ d with hBd
  have hG1 : (1 : ℝ) ≤ G := one_le_pow₀ (by linarith [Real.log_nonneg hP1])
  have hc1 : (1 : ℝ) ≤ c := one_le_pow₀ (by nlinarith)
  have hS : (1 + 24576 * (d : ℝ) ^ 4) ^ d ≤ c := pow_le_pow_left₀ (by positivity) (by nlinarith) d
  have hEsh : Real.exp (Real.sqrt 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) ≤
      Real.exp (8 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) := by
    refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ?_ hY)
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 8)]
    norm_num
  have hΛ2 : Λ ^ 2 ≤ Λ ^ 6 := pow_le_pow_right₀ hΛ1 (by norm_num)
  have hX1 : (0 : ℝ) ≤ Real.exp (Real.sqrt 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) := (Real.exp_pos _).le
  have hX8 : (0 : ℝ) ≤ Real.exp (8 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) := (Real.exp_pos _).le
  have hK : 8 * Bd + 6 * (5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d) ≤ 10 ^ 12 * c * G := by
    have h1 : G ≤ c * G := by nlinarith
    have h2 : c ≤ c * G := by nlinarith
    nlinarith
  calc (8 * Bd + 6 * (5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d)) * Λ ^ 2 *
        Real.exp (Real.sqrt 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4))
      ≤ (10 ^ 12 * c * G) * Λ ^ 6 * Real.exp (8 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) := by
        gcongr
    _ = _ := by ring

end WGScale

section WGLoops

variable {d : ℕ} {sz : Sizes d} {lam0 E : ℕ → ℝ} {n : ℕ} {u D Λ K₀ J θ Cd : ℝ}
  {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- The leg bound `Step5IIIEdet_leg_long` with the distance in the other orientation. -/
theorem Step5IIIEdet_leg_long' (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) (hm : BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ J θ Cd H)
    (σ : Bool) (a b : Zd d (sz.L n)) (h : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (b - a) : ℝ)) :
    ‖(baStep2Mat sz lam0 E).LM n u H ![σ, !σ] ![a, b]‖ ≤
      2 * J * tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (b - a) : ℝ) := by
  have e : zdistInf d (sz.L n) (b - a) = zdistInf d (sz.L n) (a - b) := lemDecCalE_zdistInf_sub_comm d (sz.L n) b a
  rw [e] at h ⊢
  exact Step5IIIEdet_leg_long hs hm σ a b h

/-- The first three-loop of `ℰ^{G̃}`: `𝓛^{(3)}_{(σ₀,σ₀,σ₁),(x,a₀,a₁)}` through its legs `(x,a₁)`, `(a₀,x)`, `(a₁,a₀)`. -/
theorem Step5IIIEdet_loopA_legs (hH : H.IsHermitian) (σ0 σ1 : Bool) (a0 a1 x : Zd d (sz.L n)) :
    ‖(baStep2Mat sz lam0 E).LM n u H ![σ0, σ0, σ1] ![x, a0, a1]‖ ≤
      Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![σ0, !σ0] ![x, a1]‖ *
        Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![σ0, !σ0] ![a0, x]‖ *
          Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![σ1, !σ1] ![a1, a0]‖ := by
  simpa using Step5IIIEdet_loop3_legs (lam0 := lam0) (E := E) (u := u) hH ![σ0, σ0, σ1] ![x, a0, a1]

/-- The second three-loop of `ℰ^{G̃}`: `𝓛^{(3)}_{(σ₀,σ₁,σ₁),(a₀,x,a₁)}` through its legs `(a₀,a₁)`, `(x,a₀)`, `(a₁,x)`. -/
theorem Step5IIIEdet_loopB_legs (hH : H.IsHermitian) (σ0 σ1 : Bool) (a0 a1 x : Zd d (sz.L n)) :
    ‖(baStep2Mat sz lam0 E).LM n u H ![σ0, σ1, σ1] ![a0, x, a1]‖ ≤
      Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![σ0, !σ0] ![a0, a1]‖ *
        Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![σ1, !σ1] ![x, a0]‖ *
          Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![σ1, !σ1] ![a1, x]‖ := by
  simpa using Step5IIIEdet_loop3_legs (lam0 := lam0) (E := E) (u := u) hH ![σ0, σ1, σ1] ![a0, x, a1]

/-- Both three-loops, the `x`-legs both far (`≥ ℓ*`), the `r`-leg arbitrary:
`‖𝓛^{(3)}‖ ≤ 2 J √(Λτ) √T(p) √T(q)` (`p = |x - a₁|`, `q = |a₀ - x|`). -/
theorem Step5IIIEdet_wG_far2 (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) (hm : BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ J θ Cd H)
    (σ0 σ1 : Bool) (a0 a1 x : Zd d (sz.L n))
    (hp : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (x - a1) : ℝ))
    (hq : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (a0 - x) : ℝ)) :
    ‖(baStep2Mat sz lam0 E).LM n u H ![σ0, σ0, σ1] ![x, a0, a1]‖ ≤
        (2 * J * Real.sqrt (Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹)) *
          (Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (x - a1) : ℝ)) *
            Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a0 - x) : ℝ))) ∧
    ‖(baStep2Mat sz lam0 E).LM n u H ![σ0, σ1, σ1] ![a0, x, a1]‖ ≤
        (2 * J * Real.sqrt (Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹)) *
          (Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (x - a1) : ℝ)) *
            Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a0 - x) : ℝ))) := by
  have hJ := Step5IIIEdet_one_le_J hs
  have hH := hm.1
  refine ⟨(Step5IIIEdet_loopA_legs hH σ0 σ1 a0 a1 x).trans
    (Step5IIIEdet_pt_far2 hJ (Step5IIIEdet_leg_long hs hm σ0 x a1 hp) (Step5IIIEdet_leg_long hs hm σ0 a0 x hq)
      (Step5IIIEdet_leg_short hm σ1 a1 a0)), ?_⟩
  refine (Step5IIIEdet_loopB_legs hH σ0 σ1 a0 a1 x).trans ?_
  have := Step5IIIEdet_pt_far2 hJ (Step5IIIEdet_leg_long' hs hm σ1 a1 x hp) (Step5IIIEdet_leg_long' hs hm σ1 x a0 hq)
    (Step5IIIEdet_leg_short hm σ0 a0 a1)
  linarith

/-- Both three-loops, all three legs far: `‖𝓛^{(3)}‖ ≤ 2 J √(2J) √T(r) √T(p) √T(q)` (`r = |a₀ - a₁|`). -/
theorem Step5IIIEdet_wG_far3 (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) (hm : BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ J θ Cd H)
    (σ0 σ1 : Bool) (a0 a1 x : Zd d (sz.L n))
    (hp : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (x - a1) : ℝ))
    (hq : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (a0 - x) : ℝ))
    (hr : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (a0 - a1) : ℝ)) :
    ‖(baStep2Mat sz lam0 E).LM n u H ![σ0, σ0, σ1] ![x, a0, a1]‖ ≤
        (2 * J * Real.sqrt (2 * J)) * Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a0 - a1) : ℝ)) *
          (Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (x - a1) : ℝ)) *
            Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a0 - x) : ℝ))) ∧
    ‖(baStep2Mat sz lam0 E).LM n u H ![σ0, σ1, σ1] ![a0, x, a1]‖ ≤
        (2 * J * Real.sqrt (2 * J)) * Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a0 - a1) : ℝ)) *
          (Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (x - a1) : ℝ)) *
            Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a0 - x) : ℝ))) := by
  have hJ := Step5IIIEdet_one_le_J hs
  have hH := hm.1
  refine ⟨(Step5IIIEdet_loopA_legs hH σ0 σ1 a0 a1 x).trans
    (Step5IIIEdet_pt_far3 hJ (Step5IIIEdet_leg_long hs hm σ0 x a1 hp) (Step5IIIEdet_leg_long hs hm σ0 a0 x hq)
      (Step5IIIEdet_leg_long' hs hm σ1 a1 a0 hr)), ?_⟩
  refine (Step5IIIEdet_loopB_legs hH σ0 σ1 a0 a1 x).trans ?_
  have := Step5IIIEdet_pt_far3 hJ (Step5IIIEdet_leg_long' hs hm σ1 a1 x hp) (Step5IIIEdet_leg_long' hs hm σ1 x a0 hq)
    (Step5IIIEdet_leg_long hs hm σ0 a0 a1 hr)
  linarith

/-- Both three-loops, `r > 2ℓ*` and `x` in the ball (`p ≤ ℓ*` or `q ≤ ℓ*`): `‖𝓛^{(3)}‖ ≤ √(Λτ) · 2 J e^{Y} T(r)`. -/
theorem Step5IIIEdet_wG_ball (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) (hm : BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ J θ Cd H)
    (σ0 σ1 : Bool) (a0 a1 x : Zd d (sz.L n))
    (hball : (zdistInf d (sz.L n) (x - a1) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ∨
      (zdistInf d (sz.L n) (a0 - x) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ))
    (hr : 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) < (zdistInf d (sz.L n) (a0 - a1) : ℝ)) :
    ‖(baStep2Mat sz lam0 E).LM n u H ![σ0, σ0, σ1] ![x, a0, a1]‖ ≤
        Real.sqrt (Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) *
          (2 * J * Real.exp (Real.sqrt 1 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) *
            tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a0 - a1) : ℝ)) ∧
    ‖(baStep2Mat sz lam0 E).LM n u H ![σ0, σ1, σ1] ![a0, x, a1]‖ ≤
        Real.sqrt (Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) *
          (2 * J * Real.exp (Real.sqrt 1 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) *
            tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a0 - a1) : ℝ)) := by
  have hJ := Step5IIIEdet_one_le_J hs
  have hH := hm.1
  have hW0 := Step5IIIEdet_W_pos sz n
  have hlogn : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := by linarith [Step5IIIEdet_log_ge_four hs]
  have hℓ : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hlogn _
  have hE1 : 1 ≤ Real.exp (Real.sqrt 1 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) :=
    Real.one_le_exp (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hlogn _))
  have hTr : 0 ≤ tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a0 - a1) : ℝ) := tailTD_nonneg hW0.le
  have htri : (zdistInf d (sz.L n) (a0 - a1) : ℝ) ≤ (zdistInf d (sz.L n) (x - a1) : ℝ) + (zdistInf d (sz.L n) (a0 - x) : ℝ) := by
    have := lemDecCalE_zdistInf_tri_real d (sz.L n) a0 x a1
    linarith
  have hsh : ∀ p : ℝ, (zdistInf d (sz.L n) (a0 - a1) : ℝ) - Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ p →
      tailTD d ((sz.W n : ℕ) : ℝ) u D p ≤ Real.exp (Real.sqrt 1 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) *
        tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a0 - a1) : ℝ) := fun p hp => Step5IIIEdet_shift_one hs hp
  refine ⟨(Step5IIIEdet_loopA_legs hH σ0 σ1 a0 a1 x).trans
    (Step5IIIEdet_pt_ball hJ hℓ hE1 hTr (Step5IIIEdet_leg_short hm σ0 x a1) (Step5IIIEdet_leg_short hm σ0 a0 x)
      (Step5IIIEdet_leg_long hs hm σ0 x a1) (Step5IIIEdet_leg_long hs hm σ0 a0 x) (Step5IIIEdet_leg_long' hs hm σ1 a1 a0)
      (fun h => hsh _ h) (fun h => hsh _ h) htri hball hr), ?_⟩
  refine (Step5IIIEdet_loopB_legs hH σ0 σ1 a0 a1 x).trans ?_
  have := Step5IIIEdet_pt_ball hJ hℓ hE1 hTr (Step5IIIEdet_leg_short hm σ1 a1 x) (Step5IIIEdet_leg_short hm σ1 x a0)
    (fun h => Step5IIIEdet_leg_long' hs hm σ1 a1 x h) (fun h => Step5IIIEdet_leg_long' hs hm σ1 x a0 h)
    (Step5IIIEdet_leg_long hs hm σ0 a0 a1) (fun h => hsh _ h) (fun h => hsh _ h) htri hball hr
  linarith

end WGLoops

section WGAlg

/-! ### 6.2 The sum over `x` and the final real-number comparison -/

/-- `√x ≤ x` for `x ≥ 1`. -/
theorem Step5IIIEdet_sqrt_le_self {x : ℝ} (hx : 1 ≤ x) : Real.sqrt x ≤ x :=
  Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩

/-- `1 ≤ √x` for `x ≥ 1`. -/
theorem Step5IIIEdet_one_le_sqrt {x : ℝ} (hx : 1 ≤ x) : 1 ≤ Real.sqrt x := by
  have := Real.sqrt_le_sqrt hx
  rwa [Real.sqrt_one] at this

/-- `J^{3/2} = J √J` for `J > 0`. -/
theorem Step5IIIEdet_rpow_three_halves {J : ℝ} (hJ : 0 < J) : J ^ (3 / 2 : ℝ) = J * Real.sqrt J := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hJ, Real.rpow_one, Real.sqrt_eq_rpow]

/-- The ball/complement split of a sum: if `f x ≤ β` on the ball `Bl` and `f x ≤ γ g x` off it (`g ≥ 0`), then
`Σ f ≤ #Bl β + γ Σ g`. -/
theorem Step5IIIEdet_sum_split {ι : Type*} [Fintype ι] [DecidableEq ι] (Bl : Finset ι) {f g : ι → ℝ} {β γ : ℝ}
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hg : ∀ x, 0 ≤ g x) (h : ∀ x, f x ≤ if x ∈ Bl then β else γ * g x) :
    ∑ x, f x ≤ Bl.card * β + γ * ∑ x, g x := by
  have h1 : ∀ x, f x ≤ (if x ∈ Bl then β else 0) + γ * g x := by
    intro x
    have := h x
    by_cases hx : x ∈ Bl
    · simp only [hx, ite_true] at this ⊢
      have : 0 ≤ γ * g x := mul_nonneg hγ (hg x)
      linarith
    · simp only [hx, ite_false] at this ⊢
      linarith
  calc ∑ x, f x ≤ ∑ x, ((if x ∈ Bl then β else 0) + γ * g x) := Finset.sum_le_sum fun x _ => h1 x
    _ = Bl.card * β + γ * ∑ x, g x := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

/-- The final comparison, `r ≤ 2ℓ*` (indicator `1`): with `Wd τ = Ω = (1-u)⁻¹`, `τ² ≤ E T(r)` (near normalisation),
`#Bl ≤ 2 Bd`, `Bd = (2ℓ*+1)^d`, `C_sq`: `W^d Λτ (2 Λτ² #Bl + 2·2J√(Λτ)·C_sq τ √T(r)) ≤ (8 Bd + 6 C_sq) Λ² E Ω (1 + √τ J√J) T(r)`. -/
theorem Step5IIIEdet_wG_final_near {Wd Λ τ J Esh Tr Ω Csq Bd Nb : ℝ} (hΛ : 1 ≤ Λ) (hJ : 1 ≤ J) (hτ0 : 0 < τ)
    (hEsh : 1 ≤ Esh) (hCsq : 0 ≤ Csq) (hTr : 0 ≤ Tr) (hΩ : 0 ≤ Ω) (hBd : 0 ≤ Bd) (hNb0 : 0 ≤ Nb)
    (hWdτ : Wd * τ = Ω) (hτ2 : τ ^ 2 ≤ Esh * Tr) (hNb : Nb ≤ 2 * Bd) :
    Wd * (Λ * τ) * (2 * (Λ * τ ^ 2) * Nb + 2 * (2 * J * Real.sqrt (Λ * τ)) * (Csq * τ * Real.sqrt Tr)) ≤
      (8 * Bd + 6 * Csq) * Λ ^ 2 * Esh * (Ω * (1 + Real.sqrt τ * (J * Real.sqrt J)) * Tr) := by
  have hΛ0 : 0 ≤ Λ := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hs0 : 0 ≤ Real.sqrt τ := Real.sqrt_nonneg _
  have ht0 : 0 ≤ Real.sqrt Tr := Real.sqrt_nonneg _
  have hq1 : 1 ≤ Real.sqrt J := Step5IIIEdet_one_le_sqrt hJ
  have hE0 : 0 ≤ Esh := by linarith
  have hZ : 0 ≤ Real.sqrt τ * (J * Real.sqrt J) := by positivity
  -- `√(Λτ) ≤ Λ √τ`
  have h2 : Real.sqrt (Λ * τ) ≤ Λ * Real.sqrt τ := by
    rw [Real.sqrt_mul hΛ0]
    exact mul_le_mul_of_nonneg_right (Step5IIIEdet_sqrt_le_self hΛ) hs0
  -- `τ √Tr ≤ E Tr`
  have h1 : τ * Real.sqrt Tr ≤ Esh * Tr := by
    have hτs : τ ≤ Real.sqrt Esh * Real.sqrt Tr := by
      rw [← Real.sqrt_mul hE0]
      exact Real.le_sqrt_of_sq_le hτ2
    calc τ * Real.sqrt Tr ≤ (Real.sqrt Esh * Real.sqrt Tr) * Real.sqrt Tr := mul_le_mul_of_nonneg_right hτs ht0
      _ = Real.sqrt Esh * Tr := by rw [mul_assoc, Real.mul_self_sqrt hTr]
      _ ≤ Esh * Tr := mul_le_mul_of_nonneg_right (Step5IIIEdet_sqrt_le_self hEsh) hTr
  have e1 : Wd * (Λ * τ) * (2 * (Λ * τ ^ 2) * Nb) = 2 * Λ ^ 2 * Ω * τ ^ 2 * Nb := by rw [← hWdτ]; ring
  have e2 : Wd * (Λ * τ) * (2 * (2 * J * Real.sqrt (Λ * τ)) * (Csq * τ * Real.sqrt Tr)) =
      4 * Λ * Ω * J * Real.sqrt (Λ * τ) * Csq * (τ * Real.sqrt Tr) := by rw [← hWdτ]; ring
  have b1 : 2 * Λ ^ 2 * Ω * τ ^ 2 * Nb ≤ 4 * Bd * Λ ^ 2 * Esh * (Ω * Tr) := by
    have : 0 ≤ 2 * Λ ^ 2 * Ω * Nb := by positivity
    calc 2 * Λ ^ 2 * Ω * τ ^ 2 * Nb = (2 * Λ ^ 2 * Ω * Nb) * τ ^ 2 := by ring
      _ ≤ (2 * Λ ^ 2 * Ω * Nb) * (Esh * Tr) := mul_le_mul_of_nonneg_left hτ2 this
      _ ≤ (2 * Λ ^ 2 * Ω * (2 * Bd)) * (Esh * Tr) := by
          have : 0 ≤ Esh * Tr := by positivity
          exact mul_le_mul_of_nonneg_right (by gcongr) this
      _ = _ := by ring
  have b2 : 4 * Λ * Ω * J * Real.sqrt (Λ * τ) * Csq * (τ * Real.sqrt Tr) ≤
      4 * Csq * Λ ^ 2 * Esh * (Ω * Tr * (Real.sqrt τ * (J * Real.sqrt J))) := by
    have hqJ : J ≤ J * Real.sqrt J := by nlinarith
    calc 4 * Λ * Ω * J * Real.sqrt (Λ * τ) * Csq * (τ * Real.sqrt Tr)
        ≤ 4 * Λ * Ω * J * (Λ * Real.sqrt τ) * Csq * (Esh * Tr) := by
          have h0 : 0 ≤ 4 * Λ * Ω * J := by positivity
          have h3 : 0 ≤ Csq := hCsq
          gcongr
      _ = 4 * Csq * Λ ^ 2 * Esh * (Ω * Tr * (Real.sqrt τ * J)) := by ring
      _ ≤ 4 * Csq * Λ ^ 2 * Esh * (Ω * Tr * (Real.sqrt τ * (J * Real.sqrt J))) := by
          have h0 : 0 ≤ 4 * Csq * Λ ^ 2 * Esh * (Ω * Tr) := by positivity
          calc _ = (4 * Csq * Λ ^ 2 * Esh * (Ω * Tr)) * (Real.sqrt τ * J) := by ring
            _ ≤ (4 * Csq * Λ ^ 2 * Esh * (Ω * Tr)) * (Real.sqrt τ * (J * Real.sqrt J)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hqJ hs0) h0
            _ = _ := by ring
  rw [mul_add, e1, e2]
  set Z := Real.sqrt τ * (J * Real.sqrt J) with hZdef
  have hrest : 0 ≤ Λ ^ 2 * Esh * (Ω * Tr) * (4 * Bd + 8 * Bd * Z + 6 * Csq + 2 * Csq * Z) := by positivity
  nlinarith [b1, b2, hrest]

/-- The final comparison, `r > 2ℓ*` (indicator `0`): `W^d Λτ (2 √(Λτ) 2 J E₁ T(r) #Bl + 2·2J√(2J) √T(r)·C_sq τ √T(r))
≤ (8 Bd + 6 C_sq) Λ² E Ω (√τ J√J) T(r)` (`E₁ ≤ E`, `J ≤ J √J`, `τ ≤ √τ`, `√2 ≤ 3/2`). -/
theorem Step5IIIEdet_wG_final_far {Wd Λ τ J Esh E1 Tr Ω Csq Bd Nb : ℝ} (hΛ : 1 ≤ Λ) (hJ : 1 ≤ J) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (hE1 : 1 ≤ E1) (hE1E : E1 ≤ Esh) (hCsq : 0 ≤ Csq) (hTr : 0 ≤ Tr) (hΩ : 0 ≤ Ω) (hBd : 0 ≤ Bd) (hNb0 : 0 ≤ Nb)
    (hWdτ : Wd * τ = Ω) (hNb : Nb ≤ 2 * Bd) :
    Wd * (Λ * τ) * (2 * (Real.sqrt (Λ * τ) * (2 * J * E1 * Tr)) * Nb +
        2 * ((2 * J * Real.sqrt (2 * J)) * Real.sqrt Tr) * (Csq * τ * Real.sqrt Tr)) ≤
      (8 * Bd + 6 * Csq) * Λ ^ 2 * Esh * (Ω * (0 + Real.sqrt τ * (J * Real.sqrt J)) * Tr) := by
  have hΛ0 : 0 ≤ Λ := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hs0 : 0 ≤ Real.sqrt τ := Real.sqrt_nonneg _
  have hq1 : 1 ≤ Real.sqrt J := Step5IIIEdet_one_le_sqrt hJ
  have hE0 : 0 ≤ Esh := by linarith
  have hZ : 0 ≤ Real.sqrt τ * (J * Real.sqrt J) := by positivity
  have h2 : Real.sqrt (Λ * τ) ≤ Λ * Real.sqrt τ := by
    rw [Real.sqrt_mul hΛ0]
    exact mul_le_mul_of_nonneg_right (Step5IIIEdet_sqrt_le_self hΛ) hs0
  have hτs : τ ≤ Real.sqrt τ := Real.le_sqrt_of_sq_le (by nlinarith)
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have hs2' : Real.sqrt (2 * J) = Real.sqrt 2 * Real.sqrt J := Real.sqrt_mul (by norm_num) J
  have hqJ : J ≤ J * Real.sqrt J := by nlinarith
  have hTT : Real.sqrt Tr * Real.sqrt Tr = Tr := Real.mul_self_sqrt hTr
  have e1 : Wd * (Λ * τ) * (2 * (Real.sqrt (Λ * τ) * (2 * J * E1 * Tr)) * Nb) =
      4 * Λ * Ω * J * E1 * Tr * Real.sqrt (Λ * τ) * Nb := by rw [← hWdτ]; ring
  have e2 : Wd * (Λ * τ) * (2 * ((2 * J * Real.sqrt (2 * J)) * Real.sqrt Tr) * (Csq * τ * Real.sqrt Tr)) =
      4 * Λ * Ω * J * Real.sqrt (2 * J) * Csq * τ * Tr := by
    rw [← hWdτ]
    calc _ = 4 * Λ * (Wd * τ) * J * Real.sqrt (2 * J) * Csq * τ * (Real.sqrt Tr * Real.sqrt Tr) := by ring
      _ = _ := by rw [hTT, hWdτ]
  have b1 : 4 * Λ * Ω * J * E1 * Tr * Real.sqrt (Λ * τ) * Nb ≤
      8 * Bd * Λ ^ 2 * Esh * (Ω * Tr * (Real.sqrt τ * (J * Real.sqrt J))) := by
    have h0 : 0 ≤ 4 * Λ * Ω * Tr := by positivity
    calc 4 * Λ * Ω * J * E1 * Tr * Real.sqrt (Λ * τ) * Nb
        = (4 * Λ * Ω * Tr) * (J * E1 * Real.sqrt (Λ * τ) * Nb) := by ring
      _ ≤ (4 * Λ * Ω * Tr) * (J * Esh * (Λ * Real.sqrt τ) * (2 * Bd)) := by
          refine mul_le_mul_of_nonneg_left ?_ h0
          gcongr
      _ = (8 * Bd * Λ ^ 2 * Esh * (Ω * Tr)) * (Real.sqrt τ * J) := by ring
      _ ≤ (8 * Bd * Λ ^ 2 * Esh * (Ω * Tr)) * (Real.sqrt τ * (J * Real.sqrt J)) := by
          have h00 : 0 ≤ 8 * Bd * Λ ^ 2 * Esh * (Ω * Tr) := by positivity
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hqJ hs0) h00
      _ = _ := by ring
  have b2 : 4 * Λ * Ω * J * Real.sqrt (2 * J) * Csq * τ * Tr ≤
      6 * Csq * Λ ^ 2 * Esh * (Ω * Tr * (Real.sqrt τ * (J * Real.sqrt J))) := by
    have hΛΛ : Λ ≤ Λ ^ 2 := by nlinarith
    have hEsh1 : 1 ≤ Esh := hE1.trans hE1E
    have h0 : 0 ≤ Ω * Tr := mul_nonneg hΩ hTr
    calc 4 * Λ * Ω * J * Real.sqrt (2 * J) * Csq * τ * Tr
        ≤ 4 * Λ * Ω * J * (Real.sqrt 2 * Real.sqrt J) * Csq * Real.sqrt τ * Tr := by
          rw [hs2']
          have h00 : 0 ≤ 4 * Λ * Ω * J * (Real.sqrt 2 * Real.sqrt J) * Csq * Tr := by positivity
          calc _ = (4 * Λ * Ω * J * (Real.sqrt 2 * Real.sqrt J) * Csq * Tr) * τ := by ring
            _ ≤ (4 * Λ * Ω * J * (Real.sqrt 2 * Real.sqrt J) * Csq * Tr) * Real.sqrt τ := mul_le_mul_of_nonneg_left hτs h00
            _ = _ := by ring
      _ ≤ 4 * Λ * Ω * J * ((3 / 2) * Real.sqrt J) * Csq * Real.sqrt τ * Tr := by
          have h00 : 0 ≤ 4 * Λ * Ω * J * Real.sqrt J * Csq * Real.sqrt τ * Tr := by positivity
          calc _ = (4 * Λ * Ω * J * Real.sqrt J * Csq * Real.sqrt τ * Tr) * Real.sqrt 2 := by ring
            _ ≤ (4 * Λ * Ω * J * Real.sqrt J * Csq * Real.sqrt τ * Tr) * (3 / 2) := mul_le_mul_of_nonneg_left hs2 h00
            _ = _ := by ring
      _ = 6 * Λ * Csq * (Ω * Tr * (Real.sqrt τ * (J * Real.sqrt J))) := by ring
      _ ≤ 6 * Λ ^ 2 * Csq * (Ω * Tr * (Real.sqrt τ * (J * Real.sqrt J))) := by
          have h00 : 0 ≤ 6 * Csq * (Ω * Tr * (Real.sqrt τ * (J * Real.sqrt J))) := by positivity
          calc _ = Λ * (6 * Csq * (Ω * Tr * (Real.sqrt τ * (J * Real.sqrt J)))) := by ring
            _ ≤ Λ ^ 2 * (6 * Csq * (Ω * Tr * (Real.sqrt τ * (J * Real.sqrt J)))) := mul_le_mul_of_nonneg_right hΛΛ h00
            _ = _ := by ring
      _ ≤ 6 * Csq * Λ ^ 2 * Esh * (Ω * Tr * (Real.sqrt τ * (J * Real.sqrt J))) := by
          have h00 : 0 ≤ 6 * Csq * Λ ^ 2 * (Ω * Tr * (Real.sqrt τ * (J * Real.sqrt J))) := by positivity
          calc _ = (6 * Csq * Λ ^ 2 * (Ω * Tr * (Real.sqrt τ * (J * Real.sqrt J)))) * 1 := by ring
            _ ≤ (6 * Csq * Λ ^ 2 * (Ω * Tr * (Real.sqrt τ * (J * Real.sqrt J)))) * Esh := mul_le_mul_of_nonneg_left hEsh1 h00
            _ = _ := by ring
  rw [mul_add, e1, e2]
  set Z := Real.sqrt τ * (J * Real.sqrt J) with hZdef
  have hfin : 8 * Bd * Λ ^ 2 * Esh * (Ω * Tr * Z) + 6 * Csq * Λ ^ 2 * Esh * (Ω * Tr * Z) =
      (8 * Bd + 6 * Csq) * Λ ^ 2 * Esh * (Ω * (0 + Z) * Tr) := by ring
  linarith [b1, b2, hfin]

end WGAlg

section WG

/-- `res_deccalE_wG` (5.44) at BA, indicator at `2ℓ*`.  Chain: `S = 1` collapses `ℰ^{G̃,(2)}` to
`W^d Σ_x (⟨G̃(σ₁)E_x⟩ 𝓛^{(3)}_{(x,a₀,a₁)} + ⟨G̃(σ₂)E_x⟩ 𝓛^{(3)}_{(a₀,x,a₁)})`; (iv) bounds the averages by `Λτ`; on the ball
`B = {|x-a₀| ≤ ℓ*} ∪ {|x-a₁| ≤ ℓ*}` (`#B ≤ 2(2ℓ*+1)^d`, `LemDecCalE_e10a`) and `r = |a₀-a₁| ≤ 2ℓ*` the three-loop is `≤ Λτ²` (v);
elsewhere `‖𝓛^{(3)}‖` is at most the product of the square roots of the norms of its three legs (the loop bound), with legs `≤ Λτ` (v) or `≤ 2 J T` (i), (iii), swap
(`Step5IIIEdet_wG_far2`, `Step5IIIEdet_wG_far3`, `Step5IIIEdet_wG_ball`); the sum over `x` of `√T√T` is `LemDecCalEwG_sum_sqrt_tail`; `Wd τ = (1-u)⁻¹`;
`Step5IIIEdet_wG_final_near`, `Step5IIIEdet_wG_final_far`; the constants against `lossE2wG` are `Step5IIIEdet_wG_const`. -/
theorem baStep5IIIE_wG (d : ℕ) (hd : 3 ≤ d) (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u D Λ K₀ J θ Cd : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hθ : 0 < θ) (hCd : 0 < Cd)
    (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) (hm : BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ J θ Cd H)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ‖STEGtMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤
      lossE2wG d (sz.L n) (sz.W n) Λ K₀ * ((1 - u)⁻¹ *
        ((if (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) +
          (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 / 2 : ℝ)) * STtailTD sz n u D a) := by
  have hu1 := Step5IIIEdet_u_lt_one hs
  have hx : 0 < 1 - u := by linarith
  have hW0 := Step5IIIEdet_W_pos sz n
  have hJ1 := Step5IIIEdet_one_le_J hs
  have hΛ1 := Step5IIIEdet_one_le_Λ hs
  obtain ⟨hτ0, hτ1⟩ := Step5IIIEdet_tau_le_one hs
  have hlog := Step5IIIEdet_log_ge_four hs
  have hlogn : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := by linarith
  have hℓ0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hlogn _
  have hY0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hlogn _
  have hS : (baStep2Mat sz lam0 E).S n = 1 := rfl
  have hTD : ∀ r : ℝ, tailTD d ((sz.W n : ℕ) : ℝ) u D r =
      ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 * Real.exp (-Real.sqrt r) + ((sz.W n : ℕ) : ℝ) ^ (-D) :=
    fun r => Step5IIIEdet_tail_eq hu1 r
  have hTnn : ∀ r : ℝ, 0 ≤ tailTD d ((sz.W n : ℕ) : ℝ) u D r := fun r => tailTD_nonneg hW0.le
  rw [abs_of_pos hx]
  --   -- step 1: `S = 1` collapses the double sum
  have hred : STEGtMg (baStep2Mat sz lam0 E) n u H σ a = (((sz.W n : ℕ) : ℂ) ^ d) * ∑ x : Zd d (sz.L n),
      (STavgMg (baStep2Mat sz lam0 E) n u H (σ 0) x * (baStep2Mat sz lam0 E).LM n u H ![σ 0, σ 0, σ 1] ![x, a 0, a 1] +
        STavgMg (baStep2Mat sz lam0 E) n u H (σ 1) x * (baStep2Mat sz lam0 E).LM n u H ![σ 0, σ 1, σ 1] ![a 0, x, a 1]) := by
    unfold STEGtMg
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [hS, Matrix.one_apply, Finset.sum_add_distrib, STLMg]
  --   -- step 2: the norm
  have hnorm : ‖STEGtMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d *
      (Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) * ∑ x : Zd d (sz.L n),
        (‖(baStep2Mat sz lam0 E).LM n u H ![σ 0, σ 0, σ 1] ![x, a 0, a 1]‖ +
          ‖(baStep2Mat sz lam0 E).LM n u H ![σ 0, σ 1, σ 1] ![a 0, x, a 1]‖) := by
    rw [hred, norm_mul]
    have hw : ‖(((sz.W n : ℕ) : ℂ) ^ d)‖ = ((sz.W n : ℕ) : ℝ) ^ d := by simp
    rw [hw, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hW0.le _)
    calc _ ≤ ∑ x : Zd d (sz.L n), ‖STavgMg (baStep2Mat sz lam0 E) n u H (σ 0) x *
            (baStep2Mat sz lam0 E).LM n u H ![σ 0, σ 0, σ 1] ![x, a 0, a 1] +
          STavgMg (baStep2Mat sz lam0 E) n u H (σ 1) x * (baStep2Mat sz lam0 E).LM n u H ![σ 0, σ 1, σ 1] ![a 0, x, a 1]‖ :=
          norm_sum_le _ _
      _ ≤ ∑ x : Zd d (sz.L n), ((Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) *
          (‖(baStep2Mat sz lam0 E).LM n u H ![σ 0, σ 0, σ 1] ![x, a 0, a 1]‖ +
            ‖(baStep2Mat sz lam0 E).LM n u H ![σ 0, σ 1, σ 1] ![a 0, x, a 1]‖)) := by
          refine Finset.sum_le_sum fun x _ => ?_
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
          calc _ ≤ (Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) * ‖(baStep2Mat sz lam0 E).LM n u H ![σ 0, σ 0, σ 1] ![x, a 0, a 1]‖ +
                (Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) * ‖(baStep2Mat sz lam0 E).LM n u H ![σ 0, σ 1, σ 1] ![a 0, x, a 1]‖ :=
                add_le_add (mul_le_mul_of_nonneg_right (hm.2.2.2.2.1 (σ 0) x) (norm_nonneg _))
                  (mul_le_mul_of_nonneg_right (hm.2.2.2.2.1 (σ 1) x) (norm_nonneg _))
            _ = _ := by ring
      _ = _ := by rw [Finset.mul_sum]
  --   -- step 3: the ball `B` and its count
  set ℓ : ℝ := Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) with hℓdef
  classical
  set Bl : Finset (Zd d (sz.L n)) := Finset.univ.filter fun x : Zd d (sz.L n) =>
    (zdistInf d (sz.L n) (a 0 - x) : ℝ) ≤ ℓ ∨ (zdistInf d (sz.L n) (a 1 - x) : ℝ) ≤ ℓ with hBldef
  have hmem : ∀ x : Zd d (sz.L n), x ∈ Bl ↔
      ((zdistInf d (sz.L n) (a 0 - x) : ℝ) ≤ ℓ ∨ (zdistInf d (sz.L n) (a 1 - x) : ℝ) ≤ ℓ) := fun x => by
    simp [hBldef]
  have hBl : (Bl.card : ℝ) ≤ 2 * (2 * ℓ + 1) ^ d := by
    set B0 : Finset (Zd d (sz.L n)) := Finset.univ.filter fun x : Zd d (sz.L n) =>
      (zdistInf d (sz.L n) (a 0 - x) : ℝ) ≤ ℓ with hB0
    set B1 : Finset (Zd d (sz.L n)) := Finset.univ.filter fun x : Zd d (sz.L n) =>
      (zdistInf d (sz.L n) (a 1 - x) : ℝ) ≤ ℓ with hB1
    have hsub : Bl ⊆ B0 ∪ B1 := by
      intro x hx
      rw [hmem] at hx
      simp only [hB0, hB1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hx
    have hcard : Bl.card ≤ B0.card + B1.card := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hcard' : (Bl.card : ℝ) ≤ (B0.card : ℝ) + (B1.card : ℝ) := by exact_mod_cast hcard
    have h0 := LemDecCalE_e10a (a 0) ℓ hℓ0
    have h1 := LemDecCalE_e10a (a 1) ℓ hℓ0
    linarith
  --   -- step 4: the sum of `√T √T` (square-root convolution)
  have hAnn : 0 ≤ ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 := sq_nonneg _
  have hwnn : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  have hconv := LemDecCalEwG_sum_sqrt_tail (d := d) (L := sz.L n) (by omega) hAnn hwnn (Step5IIIEdet_floor hs) (a 0) (a 1)
  simp only [← hTD] at hconv
  rw [Real.sqrt_sq hτ0.le] at hconv
  --   -- constants and bookkeeping
  have hΛ0 : 0 ≤ Λ := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hWd : ((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ = (1 - u)⁻¹ := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW0 d
    field_simp
  have hΩ : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 hx.le
  have hCsq : 0 ≤ 5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d := by positivity
  have hBd : 0 ≤ (2 * ℓ + 1) ^ d := by positivity
  have hNb0 : (0 : ℝ) ≤ Bl.card := Nat.cast_nonneg _
  have hEsh1 : 1 ≤ Real.exp (Real.sqrt 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) :=
    Real.one_le_exp (mul_nonneg (Real.sqrt_nonneg _) hY0)
  have hE1 : 1 ≤ Real.exp (Real.sqrt 1 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) :=
    Real.one_le_exp (mul_nonneg (Real.sqrt_nonneg _) hY0)
  have hE1Esh : Real.exp (Real.sqrt 1 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) ≤
      Real.exp (Real.sqrt 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by norm_num)) hY0)
  have hTr0 := hTnn (zdistInf d (sz.L n) (a 0 - a 1) : ℝ)
  have hTrE : STtailTD sz n u D a = tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) := rfl
  have hτhalf : (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ^ (1 / 2 : ℝ) = Real.sqrt (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ :=
    (Real.sqrt_eq_rpow _).symm
  rw [hτhalf, Step5IIIEdet_rpow_three_halves (by linarith), hTrE]
  have hconst := Step5IIIEdet_wG_const hs
  -- the two cases of `r = |a₀ - a₁|`
  by_cases hr : (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) ≤ 2 * ℓ
  · simp only [hr, ↓reduceIte]
    have hpt : ∀ x : Zd d (sz.L n),
        ‖(baStep2Mat sz lam0 E).LM n u H ![σ 0, σ 0, σ 1] ![x, a 0, a 1]‖ +
            ‖(baStep2Mat sz lam0 E).LM n u H ![σ 0, σ 1, σ 1] ![a 0, x, a 1]‖ ≤
          if x ∈ Bl then 2 * (Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2) else
            (2 * (2 * J * Real.sqrt (Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹))) *
              (Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (x - a 1) : ℝ)) *
                Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - x) : ℝ))) := by
      intro x
      by_cases hxB : x ∈ Bl
      · simp only [hxB, ↓reduceIte]
        have h1 := hm.2.2.2.2.2.2.1 ![σ 0, σ 0, σ 1] ![x, a 0, a 1]
        have h2 := hm.2.2.2.2.2.2.1 ![σ 0, σ 1, σ 1] ![a 0, x, a 1]
        linarith
      · simp only [hxB, ↓reduceIte]
        rw [hmem, not_or, not_le, not_le] at hxB
        have hp : ℓ ≤ (zdistInf d (sz.L n) (x - a 1) : ℝ) := by
          rw [lemDecCalE_zdistInf_sub_comm]; exact hxB.2.le
        obtain ⟨hA, hB⟩ := Step5IIIEdet_wG_far2 hs hm (σ 0) (σ 1) (a 0) (a 1) x hp hxB.1.le
        linarith
    have hsum := Step5IIIEdet_sum_split Bl
      (f := fun x => ‖(baStep2Mat sz lam0 E).LM n u H ![σ 0, σ 0, σ 1] ![x, a 0, a 1]‖ +
        ‖(baStep2Mat sz lam0 E).LM n u H ![σ 0, σ 1, σ 1] ![a 0, x, a 1]‖)
      (g := fun x => Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (x - a 1) : ℝ)) *
        Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - x) : ℝ)))
      (β := 2 * (Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2))
      (γ := 2 * (2 * J * Real.sqrt (Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹)))
      (by positivity) (by positivity) (fun x => by positivity) hpt
    have hτ2 := Step5IIIEdet_near_norm hs hr
    have hfin := Step5IIIEdet_wG_final_near (Wd := ((sz.W n : ℕ) : ℝ) ^ d) (Λ := Λ)
      (τ := (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) (J := J)
      (Esh := Real.exp (Real.sqrt 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)))
      (Tr := tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - a 1) : ℝ)) (Ω := (1 - u)⁻¹)
      (Csq := 5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d) (Bd := (2 * ℓ + 1) ^ d) (Nb := (Bl.card : ℝ))
      hΛ1 hJ1 hτ0 hEsh1 hCsq hTr0 hΩ hBd hNb0 hWd hτ2 (by linarith)
    refine hnorm.trans ?_
    calc _ ≤ ((sz.W n : ℕ) : ℝ) ^ d * (Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) *
          (2 * (Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2) * (Bl.card : ℝ) +
            2 * (2 * J * Real.sqrt (Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹)) *
              (5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ *
                Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - a 1) : ℝ)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine hsum.trans ?_
          have hγ : 0 ≤ 2 * (2 * J * Real.sqrt (Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹)) := by positivity
          have := mul_le_mul_of_nonneg_left hconv hγ
          linarith
      _ ≤ _ := hfin
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right hconst ?_
          positivity
  · simp only [hr, ↓reduceIte]
    have hr' : 2 * ℓ < (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) := not_le.1 hr
    have hpt : ∀ x : Zd d (sz.L n),
        ‖(baStep2Mat sz lam0 E).LM n u H ![σ 0, σ 0, σ 1] ![x, a 0, a 1]‖ +
            ‖(baStep2Mat sz lam0 E).LM n u H ![σ 0, σ 1, σ 1] ![a 0, x, a 1]‖ ≤
          if x ∈ Bl then 2 * (Real.sqrt (Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) *
              (2 * J * Real.exp (Real.sqrt 1 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) *
                tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - a 1) : ℝ))) else
            (2 * ((2 * J * Real.sqrt (2 * J)) *
                Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - a 1) : ℝ)))) *
              (Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (x - a 1) : ℝ)) *
                Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - x) : ℝ))) := by
      intro x
      by_cases hxB : x ∈ Bl
      · simp only [hxB, ↓reduceIte]
        rw [hmem] at hxB
        have hball : (zdistInf d (sz.L n) (x - a 1) : ℝ) ≤ ℓ ∨ (zdistInf d (sz.L n) (a 0 - x) : ℝ) ≤ ℓ := by
          rcases hxB with h | h
          · exact Or.inr h
          · left; rw [lemDecCalE_zdistInf_sub_comm]; exact h
        obtain ⟨hA, hB⟩ := Step5IIIEdet_wG_ball hs hm (σ 0) (σ 1) (a 0) (a 1) x hball hr'
        linarith
      · simp only [hxB, ↓reduceIte]
        rw [hmem, not_or, not_le, not_le] at hxB
        have hp : ℓ ≤ (zdistInf d (sz.L n) (x - a 1) : ℝ) := by
          rw [lemDecCalE_zdistInf_sub_comm]; exact hxB.2.le
        obtain ⟨hA, hB⟩ := Step5IIIEdet_wG_far3 hs hm (σ 0) (σ 1) (a 0) (a 1) x hp hxB.1.le (by linarith)
        linarith
    have hsum := Step5IIIEdet_sum_split Bl
      (f := fun x => ‖(baStep2Mat sz lam0 E).LM n u H ![σ 0, σ 0, σ 1] ![x, a 0, a 1]‖ +
        ‖(baStep2Mat sz lam0 E).LM n u H ![σ 0, σ 1, σ 1] ![a 0, x, a 1]‖)
      (g := fun x => Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (x - a 1) : ℝ)) *
        Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - x) : ℝ)))
      (β := 2 * (Real.sqrt (Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) *
              (2 * J * Real.exp (Real.sqrt 1 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) *
                tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - a 1) : ℝ))))
      (γ := 2 * ((2 * J * Real.sqrt (2 * J)) *
                Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - a 1) : ℝ))))
      (by positivity) (by positivity) (fun x => by positivity) hpt
    have hfin := Step5IIIEdet_wG_final_far (Wd := ((sz.W n : ℕ) : ℝ) ^ d) (Λ := Λ)
      (τ := (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) (J := J)
      (Esh := Real.exp (Real.sqrt 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)))
      (E1 := Real.exp (Real.sqrt 1 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)))
      (Tr := tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - a 1) : ℝ)) (Ω := (1 - u)⁻¹)
      (Csq := 5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d) (Bd := (2 * ℓ + 1) ^ d) (Nb := (Bl.card : ℝ))
      hΛ1 hJ1 hτ0 hτ1 hE1 hE1Esh hCsq hTr0 hΩ hBd hNb0 hWd (by linarith)
    refine hnorm.trans ?_
    calc _ ≤ ((sz.W n : ℕ) : ℝ) ^ d * (Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) *
          (2 * (Real.sqrt (Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) *
              (2 * J * Real.exp (Real.sqrt 1 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) *
                tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - a 1) : ℝ))) * (Bl.card : ℝ) +
            2 * ((2 * J * Real.sqrt (2 * J)) *
                Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - a 1) : ℝ))) *
              (5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ *
                Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - a 1) : ℝ)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine hsum.trans ?_
          have hγ : 0 ≤ 2 * ((2 * J * Real.sqrt (2 * J)) *
                Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - a 1) : ℝ))) := by positivity
          have := mul_le_mul_of_nonneg_left hconv hγ
          linarith
      _ ≤ _ := hfin
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right hconst ?_
          positivity

end WG

end RBM.BA
end
