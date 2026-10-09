/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.OUInterfaceK
import RBM3D.Main.QUEFromQDiff

/-!
# UN-52a: the weak QUE for `𝐇_t`, model-generic (`g2bRowk`, `g2bRow`; T2355)

Paper: arXiv:2507.20274, `paper/tex/1_2_Intro_model_result.tex` (cited `1_2:line`), the outline of the proof
of Theorem 2.3 (`MR:QUE`, `1_2:406-420`) applied to `𝐇_t` (GUE phase, §7.2).  Route: RBM2D
`Universality/QUEFlow.lean:887` (`g2bRow`, "the argument of `QUE_of_QDiff` on `ouMat`"); in RBM3D the argument
exists in pieces, `queFixed` (`Main/QUEFromQDiff.lean:285`, one `(sz, n, E)`, Markov on `X_c`) and `queChain`
(`:463`, the `d ≥ 3` exponent count), both stated for `Sizes.seqP sz` and `sz.Gn`.

* `g2bRowk : ∀ K P, UNG2bRowk K P` (`OUInterfaceK.lean:109`): for every kind `K` and profile `P`, from the
  row differences `UNOUProfRowk (K d) (P d)` (constant `C`) and `UNOUEq747k (K d) (P d) sz 𝔡 τ_U`, the
  `queBadMat` bound of `UNOUQUEk`, at `ε₀ = 𝔡/3`, `c = 𝔡/6` (`ouEtaQ sz 𝔡 n` is `etaQ sz n (𝔡/3)` by
  unfolding), for every `t ∈ [0, ouTStar sz τ_U n]` and every `E` in the bulk of `K`.  There is no
  `τ_U ≤ ouTauMax` (supervisor 0956 O2): `t ≤ ouTStar` enters only through `UNOUEq747k`.
* `g2bRow : UNG2bRow` is the band corollary (`unG2bRow_of_k`, `OUInterfaceK.lean:404`).
* Private generic copy (`QUEFlow_` prefix; no edit of `QUEFromQDiff.lean`, `QUECore.lean`): the merged
  `queX_core`, `queBad_sub` and `queFixed` are stated for `Sizes.seqP sz`, `sz.Gn`, `sz.seqXmat`, and their
  helpers are file-private, so the spectral lemmas, the trace algebra, the observable `B_c`, the integrability
  of the block averages, `QUEFlow_core` (`E X_c ≤ 4 (K + ε)`), `QUEFlow_queBad_sub` and `QUEFlow_queFixed`
  are copied here with a probability measure `P` on a type `Ω` and a Hermitian-valued measurable
  `Hm : Ω → Matrix` in place of `Sizes.seqP sz` and `sz.seqXmat n` (`QUECore.lean:197-1010`, the used parts; only the
  `queBadMat` half, `UNOUQUEk` has no `que2BadMat`).  `normSq_le_trace`, `queMarkov`, `queDomain`, `queChain`
  are the merged public statements.
* Instances (CLAUDE.md §4 step 2): `QUEFlowInst`, `d = 3`, `sz0`, `UNKind.band 3`, `UNOUProfile.band 3`.
  `UNOUEq747k` (UN-51's pin) stays a hypothesis of the examples.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Univ

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints
open scoped NNReal ENNReal ComplexConjugate

/-! ## 1. Spectral lemmas, trace algebra, the observable (the used parts of `QUECore.lean:197-657`, copied, private) -/

section Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {H : Matrix ι ι ℂ} {μ : ι → ℝ} {ψ : ι → ι → ℂ}

/-- The matrix of eigenvector columns. -/
private def QUEFlow_U (ψ : ι → ι → ℂ) : Matrix ι ι ℂ := Matrix.of fun y l => ψ l y

private theorem QUEFlow_UU (hψ : IsOrthoEigenbasis H μ ψ) :
    star (QUEFlow_U ψ) * QUEFlow_U ψ = 1 := by
  ext k k'
  have h := hψ.1 k k'
  simp only [dotProduct, Pi.star_apply] at h
  simp only [Matrix.mul_apply, Matrix.star_apply, QUEFlow_U, Matrix.of_apply,
    Matrix.one_apply]
  exact h

private theorem QUEFlow_green_eq (hψ : IsOrthoEigenbasis H μ ψ) {z : ℂ}
    (hz : ∀ l, (μ l : ℂ) ≠ z) :
    green H z = QUEFlow_U ψ * diagonal (fun l => ((μ l : ℂ) - z)⁻¹) *
      star (QUEFlow_U ψ) := by
  set U := QUEFlow_U ψ with hU
  have hUU : star U * U = 1 := QUEFlow_UU hψ
  have hUU' : U * star U = 1 := mul_eq_one_comm.mp hUU
  have hHU : H * U = U * diagonal (fun l => (μ l : ℂ)) := by
    ext y l
    have h := congrFun (hψ.2 l) y
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    rw [mul_diagonal, Matrix.mul_apply]
    simp only [hU, QUEFlow_U, Matrix.of_apply]
    rw [h, mul_comm]
  have hsub : (H - z • 1) * U = U * diagonal (fun l => (μ l : ℂ) - z) := by
    rw [Matrix.sub_mul, hHU, Matrix.smul_mul, Matrix.one_mul, ← diagonal_sub,
      Matrix.mul_sub, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  apply Matrix.inv_eq_right_inv
  calc (H - z • 1) * (U * diagonal (fun l => ((μ l : ℂ) - z)⁻¹) * star U)
      = ((H - z • 1) * U) * diagonal (fun l => ((μ l : ℂ) - z)⁻¹) * star U := by
        simp only [Matrix.mul_assoc]
    _ = U * (diagonal (fun l => (μ l : ℂ) - z)
          * diagonal (fun l => ((μ l : ℂ) - z)⁻¹)) * star U := by
        rw [hsub]; simp only [Matrix.mul_assoc]
    _ = 1 := by
        have hd : (fun l => ((μ l : ℂ) - z) * ((μ l : ℂ) - z)⁻¹) = fun _ => (1 : ℂ) :=
          funext fun l => mul_inv_cancel₀ (sub_ne_zero.mpr (hz l))
        rw [diagonal_mul_diagonal, hd, diagonal_one, Matrix.mul_one, hUU']

/-- The resolvent weight `w_l = η / ((μ_l - E)² + η²)`. -/
private noncomputable def QUEFlow_w (μ : ι → ℝ) (E η : ℝ) (l : ι) : ℝ :=
  η / ((μ l - E) ^ 2 + η ^ 2)

/-- `Im G(E + iη) = U diag(w) U*` for any orthonormal eigenbasis. -/
private theorem QUEFlow_imG_eq (hψ : IsOrthoEigenbasis H μ ψ) (E : ℝ) {η : ℝ}
    (hη : η ≠ 0) :
    queImG H (E + η * Complex.I) = QUEFlow_U ψ *
      diagonal (fun l => ((QUEFlow_w μ E η l : ℝ) : ℂ)) * star (QUEFlow_U ψ) := by
  set z : ℂ := E + η * Complex.I with hzdef
  have hz : ∀ l, (μ l : ℂ) ≠ z := by
    intro l h
    have := congrArg Complex.im h
    simp [hzdef] at this
    exact hη this.symm
  set U := QUEFlow_U ψ with hU
  set d : ι → ℂ := fun l => ((μ l : ℂ) - z)⁻¹ with hd
  have hG := QUEFlow_green_eq hψ hz
  rw [← hd] at hG
  have hGH : (green H z)ᴴ = U * diagonal (star d) * star U := by
    rw [hG, conjTranspose_mul, conjTranspose_mul, diagonal_conjTranspose,
      Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hdiag : diagonal (fun l => ((QUEFlow_w μ E η l : ℝ) : ℂ)) =
      ((2 : ℂ) * Complex.I)⁻¹ • (diagonal d - diagonal (star d)) := by
    rw [diagonal_sub, ← diagonal_smul]
    congr 1
    funext l
    simp only [Pi.smul_apply, Pi.star_apply, smul_eq_mul, RCLike.star_def]
    rw [Complex.sub_conj]
    have hn : Complex.normSq ((μ l : ℂ) - z) = (μ l - E) ^ 2 + η ^ 2 := by
      rw [Complex.normSq_apply]
      simp [hzdef]
      ring
    have him : ((μ l : ℂ) - z).im = -η := by simp [hzdef]
    have hdim : (d l).im = QUEFlow_w μ E η l := by
      simp only [hd, Complex.inv_im, hn, him, QUEFlow_w]
      ring
    rw [hdim]
    have hI : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
    field_simp
    push_cast
    ring
  unfold queImG
  rw [hGH, hG, hdiag, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]

omit [DecidableEq ι] in
/-- The entry `(U* B U)_{lm} = ψ_l^* B ψ_m`. -/
private theorem QUEFlow_C_apply (B : Matrix ι ι ℂ) (l m : ι) :
    (star (QUEFlow_U ψ) * B * QUEFlow_U ψ) l m = star (ψ l) ⬝ᵥ (B *ᵥ ψ m) := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, dotProduct, mulVec, QUEFlow_U,
    Matrix.star_apply, Matrix.of_apply, Pi.star_apply]

/-- For Hermitian `B`: `tr(Im G B Im G B) = ∑_{l,m} w_l w_m |ψ_l^* B ψ_m|²`. -/
private theorem QUEFlow_trace_eq (hψ : IsOrthoEigenbasis H μ ψ) (E : ℝ) {η : ℝ}
    (hη : η ≠ 0) (B : Matrix ι ι ℂ) (hB : Bᴴ = B) :
    trace (queImG H (E + η * Complex.I) * B *
        queImG H (E + η * Complex.I) * B) =
      ∑ l, ∑ m, ((QUEFlow_w μ E η l * QUEFlow_w μ E η m *
        Complex.normSq (star (ψ l) ⬝ᵥ (B *ᵥ ψ m)) : ℝ) : ℂ) := by
  rw [QUEFlow_imG_eq hψ E hη]
  set U := QUEFlow_U ψ with hU
  set D : Matrix ι ι ℂ := diagonal (fun l => ((QUEFlow_w μ E η l : ℝ) : ℂ)) with hD
  set C : Matrix ι ι ℂ := star U * B * U with hC
  have hCH : Cᴴ = C := by
    rw [hC, conjTranspose_mul, conjTranspose_mul, hB, Matrix.star_eq_conjTranspose,
      conjTranspose_conjTranspose, Matrix.mul_assoc]
  have htr : trace (U * D * star U * B * (U * D * star U) * B) = trace (D * C * D * C) := by
    have h1 : U * D * star U * B * (U * D * star U) * B =
        U * (D * star U * B * U * D * star U * B) := by simp only [Matrix.mul_assoc]
    rw [h1, trace_mul_comm, hC]
    simp only [Matrix.mul_assoc]
  rw [htr, trace]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [diag_apply, mul_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hml : C m l = star (C l m) := by
    have h := congrFun (congrFun hCH m) l
    rw [conjTranspose_apply] at h
    exact h.symm
  rw [hml, hD, mul_diagonal, diagonal_mul, ← QUEFlow_C_apply B l m]
  rw [RCLike.star_def]
  have := Complex.mul_conj (C l m)
  push_cast
  linear_combination (((QUEFlow_w μ E η l : ℝ) : ℂ) *
    ((QUEFlow_w μ E η m : ℝ) : ℂ)) * this

private theorem QUEFlow_re_trace_eq (hψ : IsOrthoEigenbasis H μ ψ) (E : ℝ) {η : ℝ}
    (hη : η ≠ 0) (B : Matrix ι ι ℂ) (hB : Bᴴ = B) :
    (trace (queImG H (E + η * Complex.I) * B *
        queImG H (E + η * Complex.I) * B)).re =
      ∑ l, ∑ m, QUEFlow_w μ E η l * QUEFlow_w μ E η m *
        Complex.normSq (star (ψ l) ⬝ᵥ (B *ᵥ ψ m)) := by
  rw [QUEFlow_trace_eq hψ E hη B hB, Complex.re_sum]
  simp only [Complex.re_sum, Complex.ofReal_re]

omit [Fintype ι] [DecidableEq ι] in
private theorem QUEFlow_w_nonneg (μ : ι → ℝ) (E : ℝ) {η : ℝ} (hη : 0 ≤ η) (l : ι) :
    0 ≤ QUEFlow_w μ E η l := by
  unfold QUEFlow_w
  positivity

/-- `Re tr(Im G B Im G B) ≥ 0` for Hermitian `B`. -/
private theorem QUEFlow_re_trace_nonneg (hψ : IsOrthoEigenbasis H μ ψ) (E : ℝ) {η : ℝ}
    (hη : 0 < η) (B : Matrix ι ι ℂ) (hB : Bᴴ = B) :
    0 ≤ (trace (queImG H (E + η * Complex.I) * B *
        queImG H (E + η * Complex.I) * B)).re := by
  rw [QUEFlow_re_trace_eq hψ E hη.ne' B hB]
  refine Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun m _ => ?_
  have := QUEFlow_w_nonneg μ E hη.le l
  have := QUEFlow_w_nonneg μ E hη.le m
  have := Complex.normSq_nonneg (star (ψ l) ⬝ᵥ (B *ᵥ ψ m))
  positivity

/-- Every Hermitian matrix has an orthonormal eigenbasis in the sense of
`IsOrthoEigenbasis` (Mathlib's `eigenvectorBasis`). -/
private theorem QUEFlow_exists_basis (hH : H.IsHermitian) :
    ∃ (μ : ι → ℝ) (ψ : ι → ι → ℂ), IsOrthoEigenbasis H μ ψ := by
  refine ⟨hH.eigenvalues, fun k => ⇑(hH.eigenvectorBasis k), ?_, fun k => ?_⟩
  · intro k k'
    have h := orthonormal_iff_ite.mp hH.eigenvectorBasis.orthonormal k k'
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
    exact h
  · rw [hH.mulVec_eigenvectorBasis k]
    ext x
    simp [RCLike.real_smul_eq_coe_smul (K := ℂ)]

end Spectral

section TraceAlgebra

variable {ι : Type*} [Fintype ι]

/-- `tr(Im G E_u Im G E_v) = -¼ (tr(G E_u G E_v) + conj tr(G E_u G E_v) - tr(G E_u G† E_v)
- tr(G E_v G† E_u))` for Hermitian `E_u, E_v`. -/
private theorem QUEFlow_trace_imG (G Eu Ev : Matrix ι ι ℂ) (hEu : Euᴴ = Eu)
    (hEv : Evᴴ = Ev) :
    trace ((((2 : ℂ) * Complex.I)⁻¹ • (G - Gᴴ)) * Eu * (((2 : ℂ) * Complex.I)⁻¹ • (G - Gᴴ)) *
        Ev) =
      -(1 / 4 : ℂ) * (trace (G * Eu * G * Ev) + conj (trace (G * Eu * G * Ev)) -
        trace (G * Eu * Gᴴ * Ev) - trace (G * Ev * Gᴴ * Eu)) := by
  have h1 : trace (Gᴴ * Eu * G * Ev) = trace (G * Ev * Gᴴ * Eu) := by
    have : Gᴴ * Eu * G * Ev = (Gᴴ * Eu) * (G * Ev) := by simp only [Matrix.mul_assoc]
    rw [this, trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have h2 : trace (Gᴴ * Eu * Gᴴ * Ev) = conj (trace (G * Eu * G * Ev)) := by
    rw [← RCLike.star_def, ← trace_conjTranspose]
    simp only [conjTranspose_mul, hEu, hEv]
    have : Gᴴ * Eu * Gᴴ * Ev = (Gᴴ * Eu * Gᴴ) * Ev := rfl
    rw [this, trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hc : ((2 : ℂ) * Complex.I)⁻¹ * ((2 : ℂ) * Complex.I)⁻¹ = -(1 / 4 : ℂ) := by
    rw [← mul_inv, show (2 : ℂ) * Complex.I * (2 * Complex.I) = -4 by
      ring_nf; rw [Complex.I_sq]; ring]
    norm_num
  simp only [Matrix.smul_mul, Matrix.mul_smul, trace_smul, Matrix.sub_mul,
    Matrix.mul_sub, trace_sub, smul_eq_mul]
  rw [h1, h2]
  linear_combination (trace (G * Eu * G * Ev) - trace (G * Ev * Gᴴ * Eu) -
    trace (G * Eu * Gᴴ * Ev) + conj (trace (G * Eu * G * Ev))) * hc

/-- Bilinear expansion of `tr(M B M B')` for `B = ∑ β_u E_u`, `B' = ∑ β'_v E_v`. -/
private theorem QUEFlow_trace_sum {κ : Type*} [Fintype κ] (M : Matrix ι ι ℂ)
    (E : κ → Matrix ι ι ℂ) (β : κ → ℂ) :
    trace (M * (∑ u, β u • E u) * M * (∑ v, β v • E v)) =
      ∑ u, ∑ v, β u * β v * trace (M * E u * M * E v) := by
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, trace_sum,
    trace_smul, smul_eq_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  ring

/-- `|∑_{u,v} β_u β_v g_{uv}| ≤ (∑|β|)² M` when `|g_{uv}| ≤ M`. -/
private theorem QUEFlow_norm_dbl_le {κ : Type*} [Fintype κ] (β : κ → ℝ)
    (g : κ → κ → ℂ) {M : ℝ} (hg : ∀ u v, ‖g u v‖ ≤ M) :
    ‖∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * g u v‖ ≤ (∑ u, |β u|) ^ 2 * M := by
  calc ‖∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * g u v‖
      ≤ ∑ u, ∑ v, ‖((β u : ℂ) * (β v : ℂ)) * g u v‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => norm_sum_le _ _)
    _ ≤ ∑ u, ∑ v, |β u| * |β v| * M := by
        refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hg u v) (by positivity)
    _ = (∑ u, |β u|) ^ 2 * M := by
        rw [sq, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]

/-- `|∑_{u,v} β_u β_v h_{uv}| ≤ (∑|β|)² (ε + K)` when `∑ β = 0`, `|h_{uv} - P_{uv}| ≤ ε` and the
profile `P` varies along each row by at most `K` (row differences `P(u,v) - P(u,u)`). -/
private theorem QUEFlow_norm_double_sum_le {κ : Type*} [Fintype κ] (β : κ → ℝ)
    (hβ0 : ∑ u, β u = 0) (h P : κ → κ → ℂ) {ε K : ℝ}
    (hε : ∀ u v, ‖h u v - P u v‖ ≤ ε) (hK : ∀ u v v', ‖P u v - P u v'‖ ≤ K) :
    ‖∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * h u v‖ ≤ (∑ u, |β u|) ^ 2 * (ε + K) := by
  have hz : ∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * P u u = 0 := by
    have h0 : (∑ v, (β v : ℂ)) = 0 := by exact_mod_cast hβ0
    have e : ∀ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * P u u = (β u : ℂ) * P u u * ∑ v, (β v : ℂ) := by
      intro u
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => by ring
    simp only [e, h0, mul_zero, Finset.sum_const_zero]
  have hsplit : ∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * h u v =
      ∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * (h u v - P u v) +
      ∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * (P u v - P u u) := by
    simp only [mul_sub, Finset.sum_sub_distrib, hz]
    ring
  rw [hsplit]
  calc _ ≤ ‖∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * (h u v - P u v)‖ +
        ‖∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * (P u v - P u u)‖ := norm_add_le _ _
    _ ≤ (∑ u, |β u|) ^ 2 * ε + (∑ u, |β u|) ^ 2 * K :=
        add_le_add (QUEFlow_norm_dbl_le β _ hε) (QUEFlow_norm_dbl_le β _ fun u v => hK u v u)
    _ = _ := by ring

end TraceAlgebra

section Observable

variable (d L W : ℕ) [NeZero L] [NeZero W]

private theorem QUEFlow_blk_conjTranspose (a : Zd d L) : (queBlk d L W a)ᴴ = queBlk d L W a := by
  unfold queBlk
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext x
  by_cases h : x ∈ Iblk d L W a <;> simp [h]

private theorem QUEFlow_sum_blk :
    ∑ u, queBlk d L W u = ((W : ℂ) ^ d)⁻¹ • (1 : Matrix (Idx d L W) (Idx d L W) ℂ) := by
  ext x y
  simp only [queBlk, Matrix.sum_apply, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy
    simp only [↓reduceIte, Iblk, Finset.mem_filter, Finset.mem_univ, true_and, smul_eq_mul, mul_one]
    rw [Finset.sum_ite_eq]
    simp
  · simp [hxy]

private theorem QUEFlow_obs_herm (c : Zd d L → ℝ) : (queObs d L W c)ᴴ = queObs d L W c := by
  unfold queObs
  rw [conjTranspose_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [conjTranspose_smul, QUEFlow_blk_conjTranspose, RCLike.star_def, Complex.conj_ofReal]

private theorem QUEFlow_obs_eq (c : Zd d L → ℝ) :
    queObs d L W c = ∑ u, ((c u : ℝ) : ℂ) • queBlk d L W u -
      ((((W * L) ^ d : ℕ) : ℂ))⁻¹ • (1 : Matrix (Idx d L W) (Idx d L W) ℂ) := by
  unfold queObs
  simp only [Complex.ofReal_sub, sub_smul, Finset.sum_sub_distrib]
  congr 1
  rw [← Finset.smul_sum, QUEFlow_sum_blk, smul_smul]
  congr 1
  have hL : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  push_cast
  field_simp
  ring

private theorem QUEFlow_card : (Fintype.card (Zd d L) : ℝ) = (L : ℝ) ^ d := by
  simp [Zd, ZMod.card]

private theorem QUEFlow_sum_beta (c : Zd d L → ℝ) (hc1 : ∑ u, c u = 1) :
    ∑ u, (c u - ((L : ℝ) ^ d)⁻¹) = 0 := by
  rw [Finset.sum_sub_distrib, hc1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    QUEFlow_card]
  have hL : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  field_simp
  ring

private theorem QUEFlow_sum_abs_beta (c : Zd d L → ℝ) (hc0 : ∀ u, 0 ≤ c u)
    (hc1 : ∑ u, c u = 1) :
    ∑ u, |c u - ((L : ℝ) ^ d)⁻¹| ≤ 2 := by
  have hL : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  calc ∑ u, |c u - ((L : ℝ) ^ d)⁻¹| ≤ ∑ u, (c u + ((L : ℝ) ^ d)⁻¹) := by
        refine Finset.sum_le_sum fun u _ => ?_
        rw [abs_le]
        have := hc0 u
        have : 0 ≤ ((L : ℝ) ^ d)⁻¹ := by positivity
        constructor <;> linarith
    _ = 2 := by
        rw [Finset.sum_add_distrib, hc1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          QUEFlow_card]
        field_simp
        ring

end Observable

section TraceBlk

variable {d : ℕ}

private theorem QUEFlow_trace_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (G H : Matrix ι ι ℂ)
    (e f : ι → ℂ) :
    Matrix.trace (G * Matrix.diagonal e * H * Matrix.diagonal f) =
      ∑ i, ∑ j, G i j * e j * H j i * f i := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_diagonal]

/-- `tr(G E_u H E_v) = W^{-2d} ∑_{i∈[v], j∈[u]} G_{ij} H_{ji}`. -/
private theorem QUEFlow_trace_blk (L W : ℕ) [NeZero L] [NeZero W]
    (G H : Matrix (Idx d L W) (Idx d L W) ℂ) (u v : Zd d L) :
    Matrix.trace (G * queBlk d L W u * H * queBlk d L W v) =
      ∑ i ∈ Iblk d L W v, ∑ j ∈ Iblk d L W u,
        ((W : ℂ) ^ d)⁻¹ * ((W : ℂ) ^ d)⁻¹ * (G i j * H j i) := by
  unfold queBlk
  rw [QUEFlow_trace_diag]
  have key : ∀ i, ∑ j, G i j * (if j ∈ Iblk d L W u then ((W : ℂ) ^ d)⁻¹ else 0) * H j i *
      (if i ∈ Iblk d L W v then ((W : ℂ) ^ d)⁻¹ else 0) =
      if i ∈ Iblk d L W v then ∑ j ∈ Iblk d L W u,
        ((W : ℂ) ^ d)⁻¹ * ((W : ℂ) ^ d)⁻¹ * (G i j * H j i) else 0 := by
    intro i
    by_cases hi : i ∈ Iblk d L W v
    · simp only [hi, ↓reduceIte]
      calc _ = ∑ j, (if j ∈ Iblk d L W u then
            ((W : ℂ) ^ d)⁻¹ * ((W : ℂ) ^ d)⁻¹ * (G i j * H j i) else 0) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            by_cases hj : j ∈ Iblk d L W u
            · simp only [hj, ↓reduceIte]; ring
            · simp [hj]
        _ = _ := by rw [Finset.sum_ite_mem, Finset.univ_inter]
    · simp [hi]
  simp only [key]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- `tr(G E_u G E_v) = W^{-2d} ∑_{x∈[u], y∈[v]} G_{xy} G_{yx}`. -/
private theorem QUEFlow_trace_GG (L W : ℕ) [NeZero L] [NeZero W]
    (G : Matrix (Idx d L W) (Idx d L W) ℂ) (u v : Zd d L) :
    Matrix.trace (G * queBlk d L W u * G * queBlk d L W v) =
      ((((W : ℂ) ^ d) ^ 2)⁻¹) * ∑ x ∈ Iblk d L W u, ∑ y ∈ Iblk d L W v, G x y * G y x := by
  rw [QUEFlow_trace_blk, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- `tr(G E_u G† E_v) = W^{-2d} ∑_{x∈[v], y∈[u]} |G_{xy}|²`. -/
private theorem QUEFlow_trace_GGstar (L W : ℕ) [NeZero L] [NeZero W]
    (G : Matrix (Idx d L W) (Idx d L W) ℂ) (u v : Zd d L) :
    Matrix.trace (G * queBlk d L W u * Gᴴ * queBlk d L W v) =
      ((((W : ℂ) ^ d) ^ 2)⁻¹) * ∑ x ∈ Iblk d L W v, ∑ y ∈ Iblk d L W u,
        ((‖G x y‖ ^ 2 : ℝ) : ℂ) := by
  rw [QUEFlow_trace_blk, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  have h1 : G x y * star (G x y) = ((‖G x y‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [Matrix.conjTranspose_apply, ← h1]
  ring

end TraceBlk

/-! ## 2. The generic core: any probability measure, any Hermitian-valued measurable matrix -/

section Core

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {Ω : Type} [MeasurableSpace Ω]

private theorem QUEFlow_norm_avg2_le (F : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    {C : ℝ} (hF : ∀ x y, ‖F x y‖ ≤ C) (a b : Zd d (sz.L n)) : ‖avg2 sz n F a b‖ ≤ C := by
  unfold avg2
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  rw [norm_mul, norm_inv, norm_pow, norm_pow, Complex.norm_natCast]
  have hS : ‖∑ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ y ∈ Iblk d (sz.L n) (sz.W n) b, F x y‖ ≤
      ((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * C) := by
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ x ∈ Iblk d (sz.L n) (sz.W n) a,
        ‖∑ y ∈ Iblk d (sz.L n) (sz.W n) b, F x y‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d * C := by
      intro x _
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ C fun y _ => hF x y).trans ?_
      rw [card_Iblk, nsmul_eq_mul]
      push_cast
      rfl
    refine (Finset.sum_le_card_nsmul _ _ _ h1).trans ?_
    rw [card_Iblk, nsmul_eq_mul]
    push_cast
    rfl
  calc ((((sz.W n : ℕ) : ℝ) ^ d) ^ 2)⁻¹ * ‖∑ x ∈ Iblk d (sz.L n) (sz.W n) a,
        ∑ y ∈ Iblk d (sz.L n) (sz.W n) b, F x y‖
      ≤ ((((sz.W n : ℕ) : ℝ) ^ d) ^ 2)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * C)) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = C := by field_simp

private theorem QUEFlow_meas_avg2
    (F : Ω → Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (hF : ∀ x y, Measurable fun ω => F ω x y) (a b : Zd d (sz.L n)) :
    Measurable fun ω => avg2 sz n (F ω) a b := by
  unfold avg2
  exact (Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun y _ => hF x y).const_mul _

/-- The resolvent entries of a measurable matrix-valued map are measurable. -/
private theorem QUEFlow_meas_G
    {Hm : Ω → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hHm : Measurable Hm)
    (z : ℂ) (x y : Idx d (sz.L n) (sz.W n)) : Measurable fun ω => Gres (Hm ω) z true x y :=
  (walk_measurable_Gres_apply z true x y).comp hHm

open scoped Matrix.Norms.L2Operator in
private theorem QUEFlow_norm_G_le
    {Hm : Ω → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hH : ∀ ω, (Hm ω).IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (ω : Ω)
    (x y : Idx d (sz.L n) (sz.W n)) : ‖Gres (Hm ω) z true x y‖ ≤ |z.im|⁻¹ :=
  (RBM.Ind.norm_apply_le_l2_opNorm _ x y).trans
    (norm_Gsig_le_inv_eta (hH ω) (abs_pos.mpr hz) le_rfl true)

variable {P : Measure Ω} {Hm : Ω → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

private theorem QUEFlow_Tp_integrable [IsProbabilityMeasure P] (hHm : Measurable Hm)
    (hH : ∀ ω, (Hm ω).IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (a b : Zd d (sz.L n)) :
    Integrable (fun ω => avg2 sz n (fun x y => Gres (Hm ω) z true x y * Gres (Hm ω) z true y x) a b)
      P := by
  refine Integrable.of_bound (C := (|z.im|⁻¹) * (|z.im|⁻¹)) ?_ (ae_of_all _ fun ω => ?_)
  · exact (QUEFlow_meas_avg2 (sz := sz) (n := n)
      (fun ω x y => Gres (Hm ω) z true x y * Gres (Hm ω) z true y x)
      (fun x y => (QUEFlow_meas_G hHm z x y).mul (QUEFlow_meas_G hHm z y x)) a b).aestronglyMeasurable
  · refine QUEFlow_norm_avg2_le _ (fun x y => ?_) a b
    rw [norm_mul]
    exact mul_le_mul (QUEFlow_norm_G_le hH hz ω x y) (QUEFlow_norm_G_le hH hz ω y x)
      (norm_nonneg _) (by positivity)

private theorem QUEFlow_Tm_integrable [IsProbabilityMeasure P] (hHm : Measurable Hm)
    (hH : ∀ ω, (Hm ω).IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (a b : Zd d (sz.L n)) :
    Integrable (fun ω => avg2 sz n (fun x y => ((‖Gres (Hm ω) z true x y‖ ^ 2 : ℝ) : ℂ)) a b) P := by
  refine Integrable.of_bound (C := (|z.im|⁻¹) ^ 2) ?_ (ae_of_all _ fun ω => ?_)
  · exact (QUEFlow_meas_avg2 (sz := sz) (n := n)
      (fun ω x y => ((‖Gres (Hm ω) z true x y‖ ^ 2 : ℝ) : ℂ))
      (fun x y => Complex.measurable_ofReal.comp
        ((QUEFlow_meas_G hHm z x y).norm.pow_const 2)) a b).aestronglyMeasurable
  · refine QUEFlow_norm_avg2_le _ (fun x y => ?_) a b
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (QUEFlow_norm_G_le hH hz ω x y) 2

/-- The complex four-term combination of the two block averages `T₊`, `T₋` (copy of `queCore_F`). -/
private noncomputable def QUEFlow_F (Hm : Ω → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (z : ℂ) (ω : Ω) (u v : Zd d (sz.L n)) : ℂ :=
  -(1 / 4 : ℂ) * (avg2 sz n (fun x y => Gres (Hm ω) z true x y * Gres (Hm ω) z true y x) u v +
    conj (avg2 sz n (fun x y => Gres (Hm ω) z true x y * Gres (Hm ω) z true y x) u v) -
    avg2 sz n (fun x y => ((‖Gres (Hm ω) z true x y‖ ^ 2 : ℝ) : ℂ)) v u -
    avg2 sz n (fun x y => ((‖Gres (Hm ω) z true x y‖ ^ 2 : ℝ) : ℂ)) u v)

/-- `X_c(ω) = Re tr(Im G B_c Im G B_c)` at `H = Hm ω` (copy of `queX` on a generic carrier). -/
private noncomputable def QUEFlow_X
    (Hm : Ω → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (z : ℂ) (c : Zd d (sz.L n) → ℝ) (ω : Ω) : ℝ :=
  (Matrix.trace (queImG (Hm ω) z * queObs d (sz.L n) (sz.W n) c *
    queImG (Hm ω) z * queObs d (sz.L n) (sz.W n) c)).re

private theorem QUEFlow_trace_eq_sum (z : ℂ) (c : Zd d (sz.L n) → ℝ) (ω : Ω) :
    Matrix.trace (queImG (Hm ω) z * queObs d (sz.L n) (sz.W n) c *
      queImG (Hm ω) z * queObs d (sz.L n) (sz.W n) c) =
      ∑ u, ∑ v, ((((c u - ((sz.L n : ℝ) ^ d)⁻¹ : ℝ)) : ℂ) *
        (((c v - ((sz.L n : ℝ) ^ d)⁻¹ : ℝ)) : ℂ)) * QUEFlow_F Hm z ω u v := by
  unfold queObs
  rw [QUEFlow_trace_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  unfold queImG
  rw [QUEFlow_trace_imG _ _ _ (QUEFlow_blk_conjTranspose _ _ _ u) (QUEFlow_blk_conjTranspose _ _ _ v)]
  have hG : RBM.green (Hm ω) z = Gres (Hm ω) z true :=
    (RBM.Ind.ContinuityNet.cont_Gres_true_eq_green _ _).symm
  rw [hG]
  simp only [QUEFlow_trace_GG, QUEFlow_trace_GGstar]
  rfl

private theorem QUEFlow_F_integrable [IsProbabilityMeasure P] (hHm : Measurable Hm)
    (hH : ∀ ω, (Hm ω).IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (u v : Zd d (sz.L n)) :
    Integrable (fun ω => QUEFlow_F Hm z ω u v) P := by
  have hT := QUEFlow_Tp_integrable (P := P) hHm hH hz u v
  have hF := QUEFlow_Tm_integrable (P := P) hHm hH hz u v
  have hF' := QUEFlow_Tm_integrable (P := P) hHm hH hz v u
  have hTc : Integrable (fun ω => conj (avg2 sz n (fun x y => Gres (Hm ω) z true x y *
      Gres (Hm ω) z true y x) u v)) P := by
    have := (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.integrable_comp hT
    simpa using this
  exact (((hT.add hTc).sub hF').sub hF).const_mul _

private theorem QUEFlow_integral_F [IsProbabilityMeasure P] (hHm : Measurable Hm)
    (hH : ∀ ω, (Hm ω).IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (u v : Zd d (sz.L n)) :
    ∫ ω, QUEFlow_F Hm z ω u v ∂P =
      -(1 / 4 : ℂ) * ((∫ ω, avg2 sz n (fun x y => Gres (Hm ω) z true x y * Gres (Hm ω) z true y x) u v ∂P) +
        conj (∫ ω, avg2 sz n (fun x y => Gres (Hm ω) z true x y * Gres (Hm ω) z true y x) u v ∂P) -
        (∫ ω, avg2 sz n (fun x y => ((‖Gres (Hm ω) z true x y‖ ^ 2 : ℝ) : ℂ)) v u ∂P) -
        (∫ ω, avg2 sz n (fun x y => ((‖Gres (Hm ω) z true x y‖ ^ 2 : ℝ) : ℂ)) u v ∂P)) := by
  have hT := QUEFlow_Tp_integrable (P := P) hHm hH hz u v
  have hF := QUEFlow_Tm_integrable (P := P) hHm hH hz u v
  have hF' := QUEFlow_Tm_integrable (P := P) hHm hH hz v u
  have hTc : Integrable (fun ω => conj (avg2 sz n (fun x y => Gres (Hm ω) z true x y *
      Gres (Hm ω) z true y x) u v)) P := by
    have := (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.integrable_comp hT
    simpa using this
  have h0 : Integrable (fun ω => avg2 sz n (fun x y => Gres (Hm ω) z true x y *
      Gres (Hm ω) z true y x) u v + conj (avg2 sz n (fun x y => Gres (Hm ω) z true x y *
      Gres (Hm ω) z true y x) u v)) P := hT.add hTc
  have h1 : Integrable (fun ω => avg2 sz n (fun x y => Gres (Hm ω) z true x y *
      Gres (Hm ω) z true y x) u v + conj (avg2 sz n (fun x y => Gres (Hm ω) z true x y *
      Gres (Hm ω) z true y x) u v) -
      avg2 sz n (fun x y => ((‖Gres (Hm ω) z true x y‖ ^ 2 : ℝ) : ℂ)) v u) P := h0.sub hF'
  unfold QUEFlow_F
  rw [integral_const_mul, integral_sub h1 hF, integral_sub h0 hF', integral_add hT hTc,
    integral_conj]

private theorem QUEFlow_four_sum {κ : Type*} [Fintype κ] (b : κ → ℂ) (A B C D : κ → κ → ℂ) :
    ∑ u, ∑ v, (b u * b v) * (-(1 / 4 : ℂ) * (A u v + B u v - C u v - D u v)) =
      -(1 / 4 : ℂ) * ((∑ u, ∑ v, (b u * b v) * A u v) + (∑ u, ∑ v, (b u * b v) * B u v) -
        (∑ u, ∑ v, (b u * b v) * C u v) - (∑ u, ∑ v, (b u * b v) * D u v)) := by
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring

/-- **The core** (copy of `queX_core`, `QUECore.lean:805`, on a generic probability space and with the
profiles `PM`, `PP` as arbitrary data): if the expectation half of `QDiff` holds at `z` with error `ε` and
`PM`, `PP` vary along rows by at most `K`, then for every probability vector `c`, `X_c ≥ 0`, `X_c` is
integrable and `E X_c ≤ 4 (K + ε)`. -/
private theorem QUEFlow_core [IsProbabilityMeasure P] (hHm : Measurable Hm)
    (hH : ∀ ω, (Hm ω).IsHermitian) (z : ℂ) (hz0 : 0 < z.im) (ε K : ℝ)
    (PM PP : Zd d (sz.L n) → Zd d (sz.L n) → ℂ)
    (hQ : ∀ a b : Zd d (sz.L n),
      ‖(∫ ω, avg2 sz n (fun x y => ((‖Gres (Hm ω) z true x y‖ ^ 2 : ℝ) : ℂ)) a b ∂P) - PM a b‖ ≤ ε ∧
      ‖(∫ ω, avg2 sz n (fun x y => Gres (Hm ω) z true x y * Gres (Hm ω) z true y x) a b ∂P) -
          PP a b‖ ≤ ε)
    (hK : ∀ a b b' : Zd d (sz.L n),
      ‖PM a b - PM a b'‖ ≤ K ∧ ‖PP a b - PP a b'‖ ≤ K)
    (c : Zd d (sz.L n) → ℝ) (hc0 : ∀ u, 0 ≤ c u) (hc1 : ∑ u, c u = 1) :
    Integrable (QUEFlow_X Hm z c) P ∧ (∀ ω, 0 ≤ QUEFlow_X Hm z c ω) ∧
      ∫ ω, QUEFlow_X Hm z c ω ∂P ≤ 4 * (K + ε) := by
  have hz : z.im ≠ 0 := hz0.ne'
  set β : Zd d (sz.L n) → ℝ := fun u => c u - ((sz.L n : ℝ) ^ d)⁻¹ with hβ
  set Xc : Ω → ℂ := fun ω =>
    Matrix.trace (queImG (Hm ω) z * queObs d (sz.L n) (sz.W n) c *
      queImG (Hm ω) z * queObs d (sz.L n) (sz.W n) c) with hXc
  have hXc_eq : Xc = fun ω => ∑ u, ∑ v, (((β u : ℝ) : ℂ) * ((β v : ℝ) : ℂ)) *
      QUEFlow_F Hm z ω u v :=
    funext fun ω => QUEFlow_trace_eq_sum z c ω
  have hXc_int : Integrable Xc P := by
    rw [hXc_eq]
    refine integrable_finsetSum _ fun u _ => integrable_finsetSum _ fun v _ => ?_
    exact (QUEFlow_F_integrable hHm hH hz u v).const_mul _
  have hX : QUEFlow_X Hm z c = fun ω => (Xc ω).re := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hX]; exact hXc_int.re
  · intro ω
    obtain ⟨μ, ψ, hψ⟩ := QUEFlow_exists_basis (hH ω)
    have hzeq : z = ((z.re : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * Complex.I := (Complex.re_add_im z).symm
    have h := QUEFlow_re_trace_nonneg hψ z.re hz0 (queObs d (sz.L n) (sz.W n) c)
      (QUEFlow_obs_herm _ _ _ c)
    rw [← hzeq] at h
    exact h
  · have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) (hQ 0 0).1
    have hint : ∫ ω, Xc ω ∂P = ∑ u, ∑ v, (((β u : ℝ) : ℂ) * ((β v : ℝ) : ℂ)) *
        ∫ ω, QUEFlow_F Hm z ω u v ∂P := by
      rw [hXc_eq, integral_finsetSum _ fun u _ => integrable_finsetSum _ fun v _ =>
        (QUEFlow_F_integrable hHm hH hz u v).const_mul _]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [integral_finsetSum _ fun v _ => (QUEFlow_F_integrable hHm hH hz u v).const_mul _]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [integral_const_mul]
    set Ip : Zd d (sz.L n) → Zd d (sz.L n) → ℂ := fun u v =>
      ∫ ω, avg2 sz n (fun x y => Gres (Hm ω) z true x y * Gres (Hm ω) z true y x) u v ∂P with hIp
    set Im' : Zd d (sz.L n) → Zd d (sz.L n) → ℂ := fun u v =>
      ∫ ω, avg2 sz n (fun x y => ((‖Gres (Hm ω) z true x y‖ ^ 2 : ℝ) : ℂ)) u v ∂P with hIm
    have hβ0 : ∑ u, β u = 0 := QUEFlow_sum_beta d (sz.L n) c hc1
    have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0 0 0).1
    have hSp : ‖∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Ip u v‖ ≤ (∑ u, |β u|) ^ 2 * (ε + K) :=
      QUEFlow_norm_double_sum_le β hβ0 Ip PP (fun u v => (hQ u v).2)
        (fun u v v' => (hK u v v').2)
    have hSm : ‖∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Im' u v‖ ≤ (∑ u, |β u|) ^ 2 * (ε + K) :=
      QUEFlow_norm_double_sum_le β hβ0 Im' PM (fun u v => (hQ u v).1)
        (fun u v v' => (hK u v v').1)
    have hsum2 : (∑ u, |β u|) ^ 2 ≤ 4 := by
      have h := QUEFlow_sum_abs_beta d (sz.L n) c hc0 hc1
      have h0 : 0 ≤ ∑ u, |β u| := Finset.sum_nonneg fun u _ => abs_nonneg _
      nlinarith
    -- the swap `u ↔ v` of the second block average
    have hswap : ∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Im' v u =
        ∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Im' u v := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => by ring
    have hconj : ∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * conj (Ip u v) =
        conj (∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Ip u v) := by
      simp only [map_sum, map_mul, Complex.conj_ofReal]
    have hmain : ∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * ∫ ω, QUEFlow_F Hm z ω u v ∂P =
        -(1 / 4 : ℂ) * ((∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Ip u v) +
          conj (∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Ip u v) -
          (∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Im' u v) -
          (∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Im' u v)) := by
      have h1 : ∀ u v, ∫ ω, QUEFlow_F Hm z ω u v ∂P =
          -(1 / 4 : ℂ) * (Ip u v + conj (Ip u v) - Im' v u - Im' u v) :=
        fun u v => QUEFlow_integral_F hHm hH hz u v
      simp only [h1]
      rw [QUEFlow_four_sum (fun u => (β u : ℂ)) Ip (fun u v => conj (Ip u v)) (fun u v => Im' v u)
        Im', hconj, hswap]
    rw [hX]
    have hre : (∫ ω, (Xc ω).re ∂P) = (∫ ω, Xc ω ∂P).re :=
      integral_re hXc_int
    change (∫ ω, (Xc ω).re ∂P) ≤ _
    rw [hre]
    calc (∫ ω, Xc ω ∂P).re ≤ ‖∫ ω, Xc ω ∂P‖ := Complex.re_le_norm _
      _ = ‖-(1 / 4 : ℂ) * ((∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Ip u v) +
          conj (∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Ip u v) -
          (∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Im' u v) -
          (∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Im' u v))‖ := by rw [hint, hmain]
      _ ≤ (1 / 4) * (‖∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Ip u v‖ +
          ‖∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Ip u v‖ +
          ‖∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Im' u v‖ +
          ‖∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Im' u v‖) := by
        rw [norm_mul]
        have h4 : ‖-(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
        rw [h4]
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine (norm_sub_le _ _).trans ?_
        refine add_le_add ((norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add le_rfl ?_)) le_rfl)) le_rfl
        rw [RCLike.norm_conj]
      _ ≤ (1 / 4) * (4 * ((∑ u, |β u|) ^ 2 * (ε + K))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        linarith
      _ ≤ 4 * (K + ε) := by
        have : (∑ u, |β u|) ^ 2 * (ε + K) ≤ 4 * (ε + K) :=
          mul_le_mul_of_nonneg_right hsum2 (by linarith)
        nlinarith

end Core

/-! ## 3. The event `queBadMat` and the Markov step at one `(n, t, E)` -/

section Events

private theorem QUEFlow_blk_cross (d L W : ℕ) [NeZero L] [NeZero W] (ψ φ : Idx d L W → ℂ)
    (u : Zd d L) :
    star ψ ⬝ᵥ (queBlk d L W u *ᵥ φ) =
      ((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W u, star (ψ x) * φ x := by
  unfold queBlk
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
  have key : ∀ x, star (ψ x) * ((if x ∈ Iblk d L W u then ((W : ℂ) ^ d)⁻¹ else 0) * φ x) =
      if x ∈ Iblk d L W u then ((W : ℂ) ^ d)⁻¹ * (star (ψ x) * φ x) else 0 := by
    intro x
    by_cases h : x ∈ Iblk d L W u
    · simp only [h, ↓reduceIte]; ring
    · simp [h]
  simp only [key]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
private theorem QUEFlow_sub_of_normSq {W N η X c : ℝ} (hW : 0 < W) (hN : 0 < N) (Z : ℂ)
    (hZ : (W ^ c)⁻¹ / N ≤ ‖Z‖) (hdom : Complex.normSq Z ≤ 4 * η ^ 2 * X) :
    W ^ (-(2 * c)) ≤ 4 * N ^ 2 * η ^ 2 * X := by
  have hWc : 0 < W ^ c := Real.rpow_pos_of_pos hW c
  have h1 : W ^ (-(2 * c)) = ((W ^ c)⁻¹) ^ 2 := by
    rw [Real.rpow_neg hW.le, show 2 * c = c * 2 by ring, Real.rpow_mul hW.le, Real.rpow_two,
      inv_pow]
  have h2 : (W ^ c)⁻¹ ≤ ‖Z‖ * N := (div_le_iff₀ hN).1 hZ
  have h3 : ((W ^ c)⁻¹) ^ 2 ≤ (‖Z‖ * N) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
  rw [h1]
  calc ((W ^ c)⁻¹) ^ 2 ≤ (‖Z‖ * N) ^ 2 := h3
    _ = N ^ 2 * Complex.normSq Z := by rw [mul_pow, Complex.sq_norm]; ring
    _ ≤ N ^ 2 * (4 * η ^ 2 * X) := mul_le_mul_of_nonneg_left hdom (by positivity)
    _ = _ := by ring

private theorem QUEFlow_rpow_sub {W : ℝ} (hW : 0 < W) (d : ℕ) (c : ℝ) :
    W ^ ((d : ℝ) - c) = W ^ d * (W ^ c)⁻¹ := by
  rw [Real.rpow_sub hW, Real.rpow_natCast, div_eq_mul_inv]

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-- `(Meq:QUE)` event `⊆ {W^{-2c} ≤ 4N²η² X_{δ_a}}` (copy of `queBad_sub`, `QUECore.lean:966`, with the
matrix `Hm ω` in place of `sz.seqXmat n ω`), when the window `𝓘_E(ε₀)` lies in `[E - η, E + η]`. -/
private theorem QUEFlow_queBad_sub
    (Hm : Ω → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (ε₀ c E η : ℝ) (hη : 0 < η)
    (hwin : ∀ x : ℝ, queWindow d (sz.L n) (sz.W n) (sz.lam n) ε₀ E x → |x - E| ≤ η)
    (a : Zd d (sz.L n)) :
    {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E a (Hm ω)} ⊆
      {ω | ((sz.W n : ℕ) : ℝ) ^ (-(2 * c)) ≤
        4 * Nsz sz n ^ 2 * η ^ 2 *
          QUEFlow_X Hm ((E : ℂ) + (η : ℂ) * Complex.I) (fun u => if u = a then 1 else 0) ω} := by
  intro ω hω
  obtain ⟨μ, ψ, hψ, i, j, hi, hj, hbad⟩ := hω
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hN : (0 : ℝ) < Nsz sz n := Nsz_pos sz n
  have hNeq : ((((sz.W n * sz.L n) ^ d : ℕ) : ℝ)) = Nsz sz n := rfl
  have hBeq : queObs d (sz.L n) (sz.W n) (fun u => if u = a then 1 else 0) =
      queBlk d (sz.L n) (sz.W n) a -
        ((((sz.W n * sz.L n) ^ d : ℕ) : ℂ))⁻¹ • (1 : Matrix (Idx d (sz.L n) (sz.W n))
          (Idx d (sz.L n) (sz.W n)) ℂ) := by
    rw [QUEFlow_obs_eq]
    congr 1
    simp only [apply_ite (fun r : ℝ => (r : ℂ)), Complex.ofReal_one, Complex.ofReal_zero,
      ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hdom := normSq_le_trace (Hm ω) μ ψ hψ E η hη
    (queObs d (sz.L n) (sz.W n) (fun u => if u = a then 1 else 0)) (QUEFlow_obs_herm _ _ _ _) i j
    (hwin _ hi) (hwin _ hj)
  have hWc : ((sz.W n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hW.ne'
  have hNc : ((((sz.W n * sz.L n) ^ d : ℕ) : ℂ)) ≠ 0 := by
    have : ((((sz.W n * sz.L n) ^ d : ℕ) : ℝ)) ≠ 0 := by rw [hNeq]; exact hN.ne'
    exact_mod_cast this
  have hZ : star (ψ i) ⬝ᵥ (queObs d (sz.L n) (sz.W n) (fun u => if u = a then 1 else 0) *ᵥ ψ j) =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ((∑ x ∈ Iblk d (sz.L n) (sz.W n) a, star (ψ i x) * ψ j x) -
        (((sz.W n : ℕ) : ℂ) ^ d / (((sz.W n * sz.L n) ^ d : ℕ) : ℂ)) *
          (if i = j then 1 else 0)) := by
    rw [hBeq, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
      dotProduct_smul, QUEFlow_blk_cross, hψ.1 i j, smul_eq_mul]
    field_simp
  have hnorm : (((sz.W n : ℕ) : ℝ) ^ c)⁻¹ / Nsz sz n ≤
      ‖star (ψ i) ⬝ᵥ (queObs d (sz.L n) (sz.W n) (fun u => if u = a then 1 else 0) *ᵥ ψ j)‖ := by
    rw [hZ, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    have h1 := hbad
    rw [QUEFlow_rpow_sub hW, hNeq] at h1
    calc (((sz.W n : ℕ) : ℝ) ^ c)⁻¹ / Nsz sz n
        = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
          (((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ c)⁻¹ / Nsz sz n) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
  exact QUEFlow_sub_of_normSq hW hN _ hnorm hdom

/-- **QUE at one `(n, t, E)` on a generic carrier** (copy of `queFixed`, `QUEFromQDiff.lean:285`, first
conjunct: `UNOUQUEk` has only the `queBadMat` event): any probability measure `P`, any Hermitian-valued
measurable `Hm`, profiles `PM`, `PP` at `z = E + iη_Q`; `queX_core` at `c = δ_a`, `queBad_sub`, `queMarkov`
with `s = W^{-2c}`, `f = 4N²η_Q² X_c`, `T = 4N²η_Q² · 4(K + ε)`. -/
private theorem QUEFlow_queFixed (P : Measure Ω) [IsProbabilityMeasure P]
    (Hm : Ω → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hHm : Measurable Hm)
    (hH : ∀ ω, (Hm ω).IsHermitian) (ε₀ c E ε K : ℝ) (z : ℂ)
    (PM PP : Zd d (sz.L n) → Zd d (sz.L n) → ℂ)
    (hz : z = (E : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I) (hη : 0 < etaQ sz n ε₀)
    (hQ : ∀ a b : Zd d (sz.L n),
      ‖(∫ ω, avg2 sz n (fun x y => ((‖Gres (Hm ω) z true x y‖ ^ 2 : ℝ) : ℂ)) a b ∂P) - PM a b‖ ≤ ε ∧
      ‖(∫ ω, avg2 sz n (fun x y => Gres (Hm ω) z true x y * Gres (Hm ω) z true y x) a b ∂P) -
          PP a b‖ ≤ ε)
    (hK : ∀ a b b' : Zd d (sz.L n),
      ‖PM a b - PM a b'‖ ≤ K ∧ ‖PP a b - PP a b'‖ ≤ K) (a : Zd d (sz.L n)) :
    P {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E a (Hm ω)} ≤
      ENNReal.ofReal (4 * Nsz sz n ^ 2 * etaQ sz n ε₀ ^ 2 * (4 * (K + ε)) /
        ((sz.W n : ℕ) : ℝ) ^ (-(2 * c))) := by
  have hz0 : 0 < z.im := by rw [hz]; simpa using hη
  have hwin : ∀ x : ℝ, queWindow d (sz.L n) (sz.W n) (sz.lam n) ε₀ E x → |x - E| ≤ etaQ sz n ε₀ :=
    fun x hx => hx
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hs : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ (-(2 * c)) := Real.rpow_pos_of_pos hW _
  obtain ⟨hint, hnn, hI⟩ := QUEFlow_core (P := P) hHm hH z hz0 ε K PM PP hQ hK
    (fun u => if u = a then 1 else 0) (fun u => by split_ifs <;> norm_num) (by simp)
  have hN := Nsz_pos sz n
  have hsub := QUEFlow_queBad_sub Hm ε₀ c E _ hη hwin a
  rw [← hz] at hsub
  refine queMarkov P
    (fun ω => 4 * Nsz sz n ^ 2 * etaQ sz n ε₀ ^ 2 *
      QUEFlow_X Hm z (fun u => if u = a then 1 else 0) ω)
    (hint.const_mul _) (fun ω => mul_nonneg (by positivity) (hnn ω)) hs ?_ _ hsub
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hI (by positivity)

end Events

/-! ## 4. Uniformization over `(t, E)` -/

/-- Uniformization over admissible parameter sequences (copy of the private
`ZeroModeProfile_eventually_forall_mem_of_forall_seq'`, `ZeroModeProfile.lean:547`; pure filter combinatorics). -/
private theorem QUEFlow_eventually_forall_mem_of_forall_seq {α : Type*} {T : ℕ → Set α}
    (hT : ∀ n, (T n).Nonempty) {P : ℕ → α → Prop}
    (h : ∀ s : ℕ → α, (∀ n, s n ∈ T n) → ∀ᶠ n in atTop, P n (s n)) :
    ∀ᶠ n in atTop, ∀ a ∈ T n, P n a := by
  classical
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hcon' : ∃ᶠ n in atTop, ∃ a, a ∈ T n ∧ ¬ P n a := by
    refine hcon.mono ?_
    intro n hn
    push Not at hn
    exact hn
  set g : ℕ → α := fun n =>
    if hn : ∃ a, a ∈ T n ∧ ¬ P n a then hn.choose else (hT n).choose with hg
  have hgmem : ∀ n, g n ∈ T n := by
    intro n
    by_cases hn : ∃ a, a ∈ T n ∧ ¬ P n a
    · simp only [hg, hn, dite_true]
      exact hn.choose_spec.1
    · simp only [hg, hn, dite_false]
      exact (hT n).choose_spec
  have hbad : ∀ n, (∃ a, a ∈ T n ∧ ¬ P n a) → ¬ P n (g n) := by
    intro n hn
    have hgn : g n = hn.choose := by simp only [hg, hn, dite_true]
    rw [hgn]
    exact hn.choose_spec.2
  have heven : ∀ᶠ n in atTop, P n (g n) := h g hgmem
  obtain ⟨n, hn1, hn2⟩ := (hcon'.and_eventually heven).exists
  exact hbad n hn1 hn2

/-- `ω ↦ ouMatC M n t ω` is measurable (copy of the private `OUInterfaceK_measurable_ouMatC`,
`OUInterfaceK.lean:160`). -/
private theorem QUEFlow_measurable_ouMatC {d : ℕ} {sz : Sizes d} (M : UNModelC sz) (n : ℕ) (t : ℝ) :
    Measurable (ouMatC M n t) := by
  have h : ouMatC M n t =
      fun ω => ouMat M.toUNModel n t ω + (1 - Real.exp (-t / 2)) • M.mean n :=
    funext (ouMatC_eq_ouMat_add M n t)
  rw [h]
  exact (measurable_ouMat M.toUNModel n t).add_const _

/-! ## 5. The targets -/

/-- **`g2bRowk`** (UN-52a, class P): `UNOUQUEk` from `UNOUEq747k` and the row differences of the profile, for
every kind `K` and profile `P`; `(ε₀, c) = (𝔡/3, 𝔡/6)`, `η_Q = ouEtaQ sz 𝔡 n`, `ε = qdBoundExp sz n (τ_Q/2) η_Q`,
`K_row = C ilambda^{-2} W^{-d}`; the exponent count is `queChain` at `(𝔡/3, 𝔡/6, τ_Q, C)`.  The bulk of the kind
is inside `∀ᶠ n` of `UNOUEq747k` and a hypothesis of the row differences (it is only passed on). -/
theorem g2bRowk : ∀ (K : ∀ d, UNKind d) (P : ∀ d, UNOUProfile (K d)), UNG2bRowk K P := by
  intro K P d hd hprof 𝔠 𝔡 sz hA τU hτU hEq κ τQ hκ hτQ
  have h𝔠 : 0 < 𝔠 := hA.1
  have h𝔡 : 0 < 𝔡 := hA.2.1
  obtain ⟨C, hC, hrow⟩ := hprof 𝔡 κ h𝔡 hκ
  -- (2) uniformization of `UNOUEq747k` over `T n = {(t, E) | 0 ≤ t ≤ ouTStar}`
  have hT : ∀ n, ({a : ℝ × ℝ | 0 ≤ a.1 ∧ a.1 ≤ ouTStar sz τU n}).Nonempty := by
    intro n
    exact ⟨(0, 0), le_rfl, Real.rpow_nonneg (Nat.cast_nonneg _) _⟩
  have key := QUEFlow_eventually_forall_mem_of_forall_seq
    (P := fun n (a : ℝ × ℝ) => (K d).bulk sz κ a.2 n → ∀ x y : Zd d (sz.L n),
      ‖(∫ ω, avg2 sz n (fun x y => ((‖Gres (ouMatC ((K d).M sz) n a.1 ω)
            ((a.2 : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) true x y‖ ^ 2 : ℝ) : ℂ)) x y
          ∂(ouP ((K d).M sz).toUNModel n)) -
        (P d).pm sz n (ouZeta a.1) ((a.2 : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) x y‖ ≤
          qdBoundExp sz n (τQ / 2) (ouEtaQ sz 𝔡 n) ∧
      ‖(∫ ω, avg2 sz n (fun x y =>
            Gres (ouMatC ((K d).M sz) n a.1 ω)
              ((a.2 : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) true x y *
            Gres (ouMatC ((K d).M sz) n a.1 ω)
              ((a.2 : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) true y x) x y
          ∂(ouP ((K d).M sz).toUNModel n)) -
        (P d).pp sz n (ouZeta a.1) ((a.2 : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) x y‖ ≤
          qdBoundExp sz n (τQ / 2) (ouEtaQ sz 𝔡 n)) hT
    (fun s hs => hEq κ hκ (fun n => (s n).2) (fun n => (s n).1)
      (fun n => ⟨(hs n).1, (hs n).2⟩) (τQ / 2) (half_pos hτQ))
  -- (1), (3): the scale `η_Q`, the exponent count
  have hdom := queDomain sz hA (κ := 1) (ε₀ := 𝔡 / 3) (by linarith) (by linarith)
  have hch := queChain hd sz hA (𝔡 / 3) (𝔡 / 6) τQ C (by linarith) (by linarith) hτQ hC
  filter_upwards [key, hdom, hch, hA.2.2.2.2] with n hkey hD hchn hWO t ht0 htT E hE a
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hD0 := hD 0 (by norm_num)
  have hz0 := locDomain_im_pos hD0
  have hz1 := hD0.2.2
  have him : (((0 : ℝ) : ℂ) + (etaQ sz n (𝔡 / 3) : ℂ) * Complex.I).im = etaQ sz n (𝔡 / 3) := by simp
  rw [him] at hz0 hz1
  have hlam : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) hWO.1
  have hzim : (((E : ℝ) : ℂ) + (etaQ sz n (𝔡 / 3) : ℂ) * Complex.I).im = etaQ sz n (𝔡 / 3) := by simp
  have hzre : (((E : ℝ) : ℂ) + (etaQ sz n (𝔡 / 3) : ℂ) * Complex.I).re = E := by simp
  have hK := hrow sz n hlam hWO.2 (((E : ℝ) : ℂ) + (etaQ sz n (𝔡 / 3) : ℂ) * Complex.I)
    (by rw [hzim]; exact hz0) (by rw [hzim]; exact hz1) (by rw [hzre]; exact hE)
    (ouZeta t) (ZeroModeProfile_ouZeta_nonneg ht0) (ZeroModeProfile_ouZeta_le_one t)
  have hQn := hkey (t, E) ⟨ht0, htT⟩ hE
  have h := QUEFlow_queFixed (ouP ((K d).M sz).toUNModel n) (ouMatC ((K d).M sz) n t)
    (QUEFlow_measurable_ouMatC ((K d).M sz) n t) (ouMatC_isHermitian ((K d).M sz) n t)
    (𝔡 / 3) (𝔡 / 6) E (qdBoundExp sz n (τQ / 2) (etaQ sz n (𝔡 / 3)))
    (C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d)
    (((E : ℝ) : ℂ) + (etaQ sz n (𝔡 / 3) : ℂ) * Complex.I)
    ((P d).pm sz n (ouZeta t) (((E : ℝ) : ℂ) + (etaQ sz n (𝔡 / 3) : ℂ) * Complex.I))
    ((P d).pp sz n (ouZeta t) (((E : ℝ) : ℂ) + (etaQ sz n (𝔡 / 3) : ℂ) * Complex.I))
    rfl hz0 (fun x y => hQn x y) (fun x y y' => hK x y y') a
  exact h.trans (ENNReal.ofReal_le_ofReal hchn)

/-- **`g2bRow`** (UN-52a, the band corollary): `g2bRowk` at `UNKind.band`, `UNOUProfile.band`
(`unG2bRow_of_k`). -/
theorem g2bRow : UNG2bRow :=
  unG2bRow_of_k (g2bRowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d))

/-! ## 6. Compiled instances (`d = 3`, `sz0`, band kind; the owed pin `UNOUEq747k` stays a hypothesis) -/

namespace QUEFlowInst

open RBM.Gauss.SizesInst

/-- `g2bRowk` at `UNKind.band 3`, `UNOUProfile.band 3`, applied at `sz0` (admissible at `𝔠 = 1/6`,
`𝔡 = 1/10`) and `τ_U = 1/1000`: `UNOUQUEk` from `UNOUEq747k` (UN-51's pin, a hypothesis) and the row
differences `UNOUProfRowk` (`unOUProfRowk_band`, discharged); no bound `τ_U ≤ ouTauMax` is used.  An anonymous
`example`, not a named theorem: `UNOUEq747k` is in no list of `RBM.Audit` (`Test/Axioms.lean`), and the registry
scan fails on a named theorem that carries an unlisted premise. -/
example
    (hE : UNOUEq747k (UNKind.band 3) (UNOUProfile.band 3) sz0 (1 / 10) (1 / 1000)) :
    UNOUQUEk (UNKind.band 3) sz0 (1 / 10) (1 / 1000) :=
  g2bRowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d) 3 le_rfl
    (unOUProfRowk_band le_rfl) (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 1000) (by norm_num) hE

/-- `g2bRow` (the band corollary) at `sz0`, `τ_U = 1/1000 ≤ ouTauMax = 1/720` (an `example`, as above). -/
example (hE : UNOUEq747 sz0 (1 / 10) (1 / 1000)) :
    UNOUQUE sz0 (1 / 10) (1 / 1000) :=
  g2bRow 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 1000) (by norm_num)
    (by rw [show ouTauMax (1 / 6) (1 / 10) = 1 / 720 by unfold ouTauMax; norm_num [min_def]]
        norm_num) hE

/-- The scale of `UNOUEq747k` is the scale of `queFixed` at `ε₀ = 𝔡/3`: `ouEtaQ sz 𝔡 n = etaQ sz n (𝔡/3)`
(unfolding both definitions; used in `g2bRowk` where `hQn` is applied at `etaQ sz n (𝔡/3)`). -/
theorem inst_ouEtaQ {d : ℕ} (sz : Sizes d) (𝔡 : ℝ) (n : ℕ) :
    ouEtaQ sz 𝔡 n = etaQ sz n (𝔡 / 3) := rfl

/-- The exponent identity of `queChain` at `(ε₀, c) = (𝔡/3, 𝔡/6)`, `𝔡 = 1/10`:
`-(min (2𝔡/3) (2𝔡/5)) + 𝔡/3 + τ = -𝔡/15 + τ` (`2 ε₀ = 2𝔡/3 > 2𝔡/5`, so the minimum is `2𝔡/5`). -/
theorem inst_exponent (τ : ℝ) :
    -(min (2 * ((1 / 10 : ℝ) / 3)) (2 * (1 / 10 : ℝ) / 5)) + 2 * ((1 / 10 : ℝ) / 6) + τ =
      -((1 / 10 : ℝ) / 15) + τ := by
  norm_num [min_def]

/-- The bound of `UNOUQUEk` at `𝔡 = 1/10`: `queBound W 𝔡 (𝔡/3) (𝔡/6) τ = W^{-𝔡/15 + τ}`. -/
theorem inst_queBound (W : ℕ) (τ : ℝ) :
    queBound W (1 / 10) ((1 / 10) / 3) ((1 / 10) / 6) τ =
      ENNReal.ofReal ((W : ℝ) ^ (-((1 / 10 : ℝ) / 15) + τ)) := by
  unfold queBound
  rw [inst_exponent]

end QUEFlowInst

end RBM.Univ

end
