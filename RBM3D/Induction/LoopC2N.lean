/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.CStarAlgebra.Hom
import RBM3D.Path.StepDecomp
import RBM3D.Path.StepDecompLoop
import RBM3D.Gauss.FlowCalculus
import RBM3D.Loop.GLoopFlow
import RBM3D.Defs.Sizes

/-!
# The general-length `C²` bound of the loop observables (`d ≥ 3`)

Ticket T2111 (ST2-29, first file).  Port of `RBM2D/Induction/LoopC2N.lean` at commit `c9a24cf`
(cited `LC2N:<line>`; 580 lines there).  The pin `HermTestFunLoopN` (RBM2D
`Induction/GridGoodN.lean:365`, section `TestClass`; `GridGoodN` is ST2-32 and is not imported) is
defined here and proved: for every loop length `k`, every `n`, `|E| < 2`, `0 ≤ u < 1`, every sign
vector `σ : Fin k → Bool` and label vector `b : Fin k → Z_L^d`, the observable

  `Φ(M) = loopL d L W (blockMat M) (zt E u) (loopOf σ b) = tr ∏_{i=1}^k (G_{σ_i}(z_u) E_{b_i})`

is in the Hermitian test class `HermTestFun` of `Path/StepDecomp.lean`, and at Hermitian `M, y`

  `‖∂²Φ(M)[y, y]‖ ≤ k (k + 1) · N · η_u^{-(k+2)} · ‖y‖²`,   `N = (W L)^d`, `η_u = (1 - u) Im m`.

## Main result (namespace `RBM.Ind`)

* `HermTestFunLoopN sz` : the pin, with the vocabulary of the merged files (`Sizes d`, `Zd d L`,
  `Idx d L W`, `loopL`, `blockMat d L W`, `zt`, `etaT`, `Sizes.size = (W L)^d`).
* `hermTestFunLoopN sz : HermTestFunLoopN sz`.  Compiled nonempty instances: section 6.

## Route (CLAUDE.md §5.2)

Generalisation of the merged `k = 2`, `σ = (+,-)` proof `hermTestFun_loopPM`
(`Path/StepDecompLoop.lean:603`), whose private jets (`StepDecompLoop_blockCLM`, `_norm_blockMat`,
`_trCLM`, `_hasDerivAt_Gres`, `_fderiv(2)_of_line`, `_contDiffAt_Gres`) are copied here as private
`LoopC2N_` helpers; the two-resolvent `word_jets` is replaced by an induction on the word
(`LoopC2N_word_jets`).  Along the Hermitian line `s ↦ M + s y`, with `H = blockMat M`,
`D = blockMat y`, `R_i(s) = G_{σ_i}(H + s D)`, `R_i' = -R_i D R_i`:

  `P_l = ∏_{i ∈ l} (R_i E_i)`,   `‖R_i‖ ≤ K = η⁻¹`,   `‖E_b‖ ≤ 1`,
  `‖P_l‖ ≤ K^m`,  `‖P_l'‖ ≤ m K^{m+1} ‖D‖`,  `‖P_l''‖ ≤ m (m + 1) K^{m+2} ‖D‖²`  (`m = |l|`),

by the Leibniz rule `(R E Q)'' = R'' E Q + 2 R' E Q' + R E Q''`, `R'' = 2 R D R D R`, which gives
`m (m + 1) + 2 m + 2 = (m + 1) (m + 2)`.  Only the trace cost carries the dimension:
`‖tr A‖ ≤ card · ‖A‖` with `card (Vtx d L W) = (L W)^d = size n` (`card_BlockIndex`); the Leibniz
count is dimension-free.  `‖blockMat y‖ = ‖y‖`; `‖E_b‖ ≤ (W^d)⁻¹ ≤ 1` (the factor `W^{-dk}` is
dropped, as in the pin).  The `HermTestFun` fields come from `ContDiffAt` of the resolvent
product at `Im z_u ≠ 0` and the crude envelope `norm_gloop_le_crude`.

Vocabulary changes (DECISIONS §29, D204; as T2104): `HermTestFunLoopN` drops RBM2D's `[NeZero k]`
(the proof does not use it, so the statement is stronger).  Every helper is `private` and carries
the prefix `LoopC2N_`.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Ind

open Matrix RBM RBM.Loop RBM.Gauss RBM.Path
open scoped Matrix.Norms.L2Operator

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-! ### 1. Block coordinates (copied from `Path/StepDecompLoop.lean`, section 1) -/

section BlockCoordinates

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem LoopC2N_blockMat_add_smul (A C : Matrix (Idx d L W) (Idx d L W) ℂ) (y : ℂ) :
    blockMat d L W (A + y • C) = blockMat d L W A + y • blockMat d L W C := by
  ext p q
  simp [blockMat]

/-- `blockMat` as a continuous real-linear map (`LC2N:82`). -/
private def LoopC2N_blockCLM (d L W : ℕ) [NeZero L] [NeZero W] :
    Matrix (Idx d L W) (Idx d L W) ℂ →L[ℝ] Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := blockMat d L W
      map_add' := fun A C => by ext p q; simp [blockMat]
      map_smul' := fun r A => by ext p q; simp [blockMat] }

/-- Reindexing by an equivalence is a star algebra homomorphism of matrix algebras. -/
private def LoopC2N_reindexHom {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m]
    [DecidableEq k] (e : k ≃ m) : Matrix m m ℂ →⋆ₙₐ[ℂ] Matrix k k ℂ where
  toFun A := A.submatrix e e
  map_smul' c A := rfl
  map_zero' := rfl
  map_add' A B := rfl
  map_mul' A B := by
    exact (Matrix.submatrix_mul_equiv A B e e e).symm
  map_star' A := by
    exact (Matrix.conjTranspose_submatrix A e e).symm

/-- `blockMat` preserves the operator norm. -/
private theorem LoopC2N_norm_blockMat (A : Matrix (Idx d L W) (Idx d L W) ℂ) :
    ‖blockMat d L W A‖ = ‖A‖ := by
  have hinj : Function.Injective (LoopC2N_reindexHom (splitEquiv d L W).symm) := by
    intro A B h
    ext i j
    have := congrFun (congrFun h ((splitEquiv d L W) i)) ((splitEquiv d L W) j)
    change A ((splitEquiv d L W).symm ((splitEquiv d L W) i))
      ((splitEquiv d L W).symm ((splitEquiv d L W) j)) =
        B ((splitEquiv d L W).symm ((splitEquiv d L W) i))
          ((splitEquiv d L W).symm ((splitEquiv d L W) j)) at this
    simpa using this
  exact NonUnitalStarAlgHom.norm_map _ hinj A

private theorem LoopC2N_isHermitian_blockMat {A : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hA : A.IsHermitian) : (blockMat d L W A).IsHermitian :=
  hA.submatrix _

end BlockCoordinates

/-! ### 2. Jets of a word of resolvents and block insertions along a line -/

section Words

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace as a continuous real-linear map. -/
private def LoopC2N_trCLM (n : Type*) [Fintype n] [DecidableEq n] :
    Matrix n n ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap n ℝ ℂ)

private theorem LoopC2N_trCLM_apply (A : Matrix n n ℂ) :
    LoopC2N_trCLM n A = Matrix.trace A := rfl

private theorem LoopC2N_trace_hasDerivAt {P : ℝ → Matrix n n ℂ} {P' : Matrix n n ℂ}
    {t : ℝ} (h : HasDerivAt P P' t) :
    HasDerivAt (fun s => Matrix.trace (P s)) (Matrix.trace P') t := by
  exact (LoopC2N_trCLM n).hasFDerivAt.comp_hasDerivAt t h

private theorem LoopC2N_nmul {A B : Matrix n n ℂ} {a b : ℝ} (hA : ‖A‖ ≤ a)
    (hB : ‖B‖ ≤ b) : ‖A * B‖ ≤ a * b :=
  (norm_mul_le _ _).trans (mul_le_mul hA hB (norm_nonneg _) ((norm_nonneg _).trans hA))

private theorem LoopC2N_nadd {A B : Matrix n n ℂ} {a b : ℝ} (hA : ‖A‖ ≤ a)
    (hB : ‖B‖ ≤ b) : ‖A + B‖ ≤ a + b :=
  (norm_add_le _ _).trans (add_le_add hA hB)

/-- The word `∏_{a ∈ l} (R a s * E a)` as a function of the line parameter `s`. -/
private def LoopC2N_word {α : Type*} (R : α → ℝ → Matrix n n ℂ) (E : α → Matrix n n ℂ)
    (l : List α) (s : ℝ) : Matrix n n ℂ :=
  l.foldr (fun a M => R a s * E a * M) 1

/-- **The Leibniz induction over the word** (`LC2N:144`).  Let `R a s` be resolvent-type matrices
with `(R a)' = -R a D R a` and `‖R a s‖ ≤ K`, and `E a` matrices with `‖E a‖ ≤ 1`.  Then the word
`P_l(s) = ∏_{a ∈ l} (R a s * E a)` has two derivatives along `s`, with
`‖P_l‖ ≤ K^m`, `‖P_l'‖ ≤ m K^{m+1} ‖D‖`, `‖P_l''‖ ≤ m (m + 1) K^{m+2} ‖D‖²`, `m = l.length`. -/
private theorem LoopC2N_word_jets [Nonempty n] {α : Type*}
    {R : α → ℝ → Matrix n n ℂ} {E : α → Matrix n n ℂ} {D : Matrix n n ℂ}
    (hR : ∀ a t, HasDerivAt (R a) (-(R a t * D * R a t)) t) {K : ℝ}
    (hK : ∀ a t, ‖R a t‖ ≤ K) (hE : ∀ a, ‖E a‖ ≤ 1) (l : List α) :
    ∃ P1 P2 : ℝ → Matrix n n ℂ,
      (∀ t, HasDerivAt (LoopC2N_word R E l) (P1 t) t) ∧
      (∀ t, HasDerivAt P1 (P2 t) t) ∧
      (∀ t, ‖LoopC2N_word R E l t‖ ≤ K ^ l.length) ∧
      (∀ t, ‖P1 t‖ ≤ (l.length : ℝ) * K ^ (l.length + 1) * ‖D‖) ∧
      (∀ t, ‖P2 t‖ ≤
        (l.length : ℝ) * ((l.length : ℝ) + 1) * K ^ (l.length + 2) * ‖D‖ ^ 2) := by
  induction l with
  | nil =>
    refine ⟨fun _ => 0, fun _ => 0, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_,
      fun t => ?_⟩
    · exact hasDerivAt_const t (1 : Matrix n n ℂ)
    · exact hasDerivAt_const t (0 : Matrix n n ℂ)
    · simp [LoopC2N_word]
    · simp
    · simp
  | cons a l ih =>
    obtain ⟨Q1, Q2, hQ1, hQ2, hb0, hb1, hb2⟩ := ih
    have hRDR : ∀ t, HasDerivAt (fun s => R a s * D * R a s)
        (-(R a t * D * R a t) * D * R a t + R a t * D * (-(R a t * D * R a t))) t := fun t =>
      ((hR a t).mul_const D).mul (hR a t)
    refine ⟨fun t => -(R a t * D * R a t) * E a * LoopC2N_word R E l t + R a t * E a * Q1 t,
      fun t => ((R a t * D * R a t) * D * R a t + R a t * D * (R a t * D * R a t))
          * E a * LoopC2N_word R E l t
        + (-(R a t * D * R a t) * E a * Q1 t
          + (-(R a t * D * R a t) * E a * Q1 t + R a t * E a * Q2 t)),
      fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩
    · exact ((hR a t).mul_const (E a)).mul (hQ1 t)
    · have hT1 := (((hRDR t).neg).mul_const (E a)).mul (hQ1 t)
      have hT2 := ((hR a t).mul_const (E a)).mul (hQ2 t)
      have h := hT1.add hT2
      refine h.congr_deriv ?_
      simp only [Pi.neg_apply]
      noncomm_ring
    · have hr := hK a t
      have h := LoopC2N_nmul (LoopC2N_nmul hr (hE a)) (hb0 t)
      refine h.trans (le_of_eq ?_)
      simp only [List.length_cons]
      ring
    · have hr := hK a t
      have hX : ‖R a t * D * R a t‖ ≤ K * ‖D‖ * K :=
        LoopC2N_nmul (LoopC2N_nmul hr le_rfl) hr
      have hXn : ‖-(R a t * D * R a t)‖ ≤ K * ‖D‖ * K := by rwa [norm_neg]
      have w1 := LoopC2N_nmul (LoopC2N_nmul hXn (hE a)) (hb0 t)
      have w2 := LoopC2N_nmul (LoopC2N_nmul hr (hE a)) (hb1 t)
      have h := LoopC2N_nadd w1 w2
      refine h.trans (le_of_eq ?_)
      simp only [List.length_cons]
      push_cast
      ring
    · have hr := hK a t
      have hX : ‖R a t * D * R a t‖ ≤ K * ‖D‖ * K :=
        LoopC2N_nmul (LoopC2N_nmul hr le_rfl) hr
      have hXn : ‖-(R a t * D * R a t)‖ ≤ K * ‖D‖ * K := by rwa [norm_neg]
      have hXDR : ‖(R a t * D * R a t) * D * R a t‖ ≤ K * ‖D‖ * K * ‖D‖ * K :=
        LoopC2N_nmul (LoopC2N_nmul hX le_rfl) hr
      have hRDX : ‖R a t * D * (R a t * D * R a t)‖ ≤ K * ‖D‖ * (K * ‖D‖ * K) :=
        LoopC2N_nmul (LoopC2N_nmul hr le_rfl) hX
      have w1 := LoopC2N_nmul (LoopC2N_nmul (LoopC2N_nadd hXDR hRDX) (hE a)) (hb0 t)
      have w2 := LoopC2N_nmul (LoopC2N_nmul hXn (hE a)) (hb1 t)
      have w4 := LoopC2N_nmul (LoopC2N_nmul hr (hE a)) (hb2 t)
      have h := LoopC2N_nadd w1 (LoopC2N_nadd w2 (LoopC2N_nadd w2 w4))
      refine h.trans (le_of_eq ?_)
      simp only [List.length_cons]
      push_cast
      ring

end Words

/-! ### 3. Lines through Hermitian points (copied from `Path/StepDecompLoop.lean`, section 3) -/

section Lines

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The affine line `s ↦ M + s • A` has derivative `A`. -/
private theorem LoopC2N_hasDerivAt_line (M A : Matrix n n ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => M + (s : ℂ) • A) A t := by
  have h : HasDerivAt (fun s : ℝ => (s : ℂ) • A) A t := by
    simpa using (hasDerivAt_id t).smul_const A
  simpa using h.const_add M

omit [Fintype n] [DecidableEq n] in
/-- A real multiple of a Hermitian matrix added to a Hermitian matrix is Hermitian. -/
private theorem LoopC2N_isHermitian_add_realSmul {M A : Matrix n n ℂ}
    (hM : M.IsHermitian) (hA : A.IsHermitian) (s : ℝ) : (M + (s : ℂ) • A).IsHermitian := by
  refine hM.add ?_
  change Matrix.conjTranspose ((s : ℂ) • A) = (s : ℂ) • A
  rw [Matrix.conjTranspose_smul, hA, Complex.star_def, Complex.conj_ofReal]

/-- The signed resolvent `Gres` along a Hermitian line has derivative `-G D G`. -/
private theorem LoopC2N_hasDerivAt_Gres {H D : Matrix n n ℂ} (hH : H.IsHermitian)
    (hD : D.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (σ : Bool) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Gres (H + (s : ℂ) • D) z σ)
      (-(Gres (H + (t : ℂ) • D) z σ * D * Gres (H + (t : ℂ) • D) z σ)) t := by
  have hline := LoopC2N_hasDerivAt_line H D t
  have hherm := LoopC2N_isHermitian_add_realSmul hH hD t
  cases σ with
  | true =>
    have h := hasDerivAt_green_moving (z := fun _ => z) hline (hasDerivAt_const t z) hherm hz
    simpa using h
  | false =>
    have h := hasDerivAt_green_moving (z := fun _ => (starRingEnd ℂ) z) hline
      (hasDerivAt_const t ((starRingEnd ℂ) z)) hherm (by simpa using hz)
    simpa [Gres] using h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If `Φ` is `C²` at Hermitian points and its derivative along a Hermitian line
`s ↦ M + s y` is `φ₁`, then `fderiv ℝ Φ (M + t y) y = φ₁ t`. -/
private theorem LoopC2N_fderiv_of_line {Φ : Matrix ι ι ℂ → ℂ}
    (hΦ : ∀ M, M.IsHermitian → ContDiffAt ℝ 2 Φ M) {M y : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (hy : y.IsHermitian) {φ₁ : ℝ → ℂ}
    (h₀ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Φ (M + (s : ℂ) • y)) (φ₁ t) t) (t : ℝ) :
    φ₁ t = fderiv ℝ Φ (M + (t : ℂ) • y) y := by
  have hdiff : DifferentiableAt ℝ Φ (M + (t : ℂ) • y) :=
    ((hΦ _ (LoopC2N_isHermitian_add_realSmul hM hy t)).differentiableAt (by norm_num))
  have h := hdiff.hasFDerivAt.comp_hasDerivAt t (LoopC2N_hasDerivAt_line M y t)
  exact (h₀ t).unique h

/-- If `Φ` is `C²` at Hermitian points and its first two derivatives along a Hermitian line
`s ↦ M + s y` are `φ₁`, `φ₂`, then `fderiv ℝ (fderiv ℝ Φ) M y y = φ₂ 0`. -/
private theorem LoopC2N_fderiv2_of_line {Φ : Matrix ι ι ℂ → ℂ}
    (hΦ : ∀ M, M.IsHermitian → ContDiffAt ℝ 2 Φ M) {M y : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (hy : y.IsHermitian) {φ₁ φ₂ : ℝ → ℂ}
    (h₀ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Φ (M + (s : ℂ) • y)) (φ₁ t) t)
    (h₁ : ∀ t : ℝ, HasDerivAt φ₁ (φ₂ t) t) :
    fderiv ℝ (fderiv ℝ Φ) M y y = φ₂ 0 := by
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => M + (s : ℂ) • y) y t := fun t =>
    LoopC2N_hasDerivAt_line M y t
  have hφ₁ := LoopC2N_fderiv_of_line hΦ hM hy h₀
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

end Lines

/-! ### 4. The observable: smoothness, second derivative along a line -/

section Observable

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The resolvent of `blockMat M` is `C²` at every `M` for which `blockMat M - w` is invertible
(`LC2N:313`). -/
private theorem LoopC2N_contDiffAt_Gres {w : ℂ} {M : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hu : IsUnit (blockMat d L W M - w • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ))) :
    ContDiffAt ℝ 2 (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ => Gres (blockMat d L W M') w true)
      M := by
  have hA : ContDiff ℝ 2 (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ =>
      blockMat d L W M' - w • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) :=
    ((LoopC2N_blockCLM d L W).contDiff).sub contDiff_const
  have hinv : ContDiffAt ℝ 2 (Ring.inverse (M₀ := Matrix (Vtx d L W) (Vtx d L W) ℂ))
      (blockMat d L W M - w • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) := by
    obtain ⟨u, hu'⟩ := hu
    rw [← hu']
    exact contDiffAt_ringInverse ℝ u
  have h := hinv.comp M hA.contDiffAt
  have hfun : (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ => Gres (blockMat d L W M') w true)
      = Ring.inverse ∘ (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ =>
        blockMat d L W M' - w • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) := by
    funext M'
    simp [Gres]
  rw [hfun]
  exact h

/-- The signed resolvent factor `G_σ(blockMat M')` is `C²` at Hermitian `M`. -/
private theorem LoopC2N_contDiffAt_Gsig {z : ℂ} (hz : z.im ≠ 0) (σ : Bool)
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) :
    ContDiffAt ℝ 2 (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ => Gres (blockMat d L W M') z σ)
      M := by
  have hMb : (blockMat d L W M).IsHermitian := LoopC2N_isHermitian_blockMat hM
  cases σ with
  | true => exact LoopC2N_contDiffAt_Gres (isUnit_sub_smul_of_isHermitian hMb hz)
  | false =>
    have hz' : ((starRingEnd ℂ) z).im ≠ 0 := by simpa using hz
    have h := LoopC2N_contDiffAt_Gres (d := d) (L := L) (W := W) (w := (starRingEnd ℂ) z)
      (isUnit_sub_smul_of_isHermitian hMb hz')
    simpa [Gres] using h

/-- The resolvent word is `C²` at every Hermitian point (as a function of `M`). -/
private theorem LoopC2N_contDiffAt_word {z : ℂ} (hz : z.im ≠ 0) (l : List (Bool × Zd d L))
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) :
    ContDiffAt ℝ 2 (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ =>
      l.foldr (fun p X => Gres (blockMat d L W M') z p.1 * Eblk d L W p.2 * X) 1) M := by
  induction l with
  | nil => exact contDiffAt_const
  | cons p l ih =>
    have hEp : ContDiffAt ℝ 2 (fun _ : Matrix (Idx d L W) (Idx d L W) ℂ => Eblk d L W p.2) M :=
      contDiffAt_const
    exact ((LoopC2N_contDiffAt_Gsig hz p.1 hM).mul hEp).mul ih

/-- (H1) for the `k`-loop observable: `C²` at every Hermitian point. -/
private theorem LoopC2N_contDiffAt_loop {z : ℂ} (hz : z.im ≠ 0) {k : ℕ} (σ : Fin k → Bool)
    (b : Fin k → Zd d L) {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) :
    ContDiffAt ℝ 2
      (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ =>
        loopL d L W (blockMat d L W M') z (loopOf σ b)) M := by
  have h := (LoopC2N_trCLM (Vtx d L W)).contDiff.contDiffAt.comp M
    (LoopC2N_contDiffAt_word hz ((List.ofFn σ).zip (List.ofFn b)) hM)
  exact h

/-- The first two derivatives of the `k`-loop observable along a Hermitian line, with the bound
`|φ₂| ≤ N · k (k + 1) η⁻⁽ᵏ⁺²⁾ ‖y‖²`, `N = (L W)^d` (`LC2N:366`). -/
private theorem LoopC2N_line_jets {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|) {k : ℕ}
    (σ : Fin k → Bool) (b : Fin k → Zd d L) {M y : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hM : M.IsHermitian) (hy : y.IsHermitian) :
    ∃ φ₁ φ₂ : ℝ → ℂ,
      (∀ t : ℝ, HasDerivAt (fun s : ℝ =>
        loopL d L W (blockMat d L W (M + (s : ℂ) • y)) z (loopOf σ b)) (φ₁ t) t) ∧
      (∀ t : ℝ, HasDerivAt φ₁ (φ₂ t) t) ∧
      (∀ t : ℝ, ‖φ₂ t‖ ≤
        (((L * W) ^ d : ℕ) : ℝ) * ((k : ℝ) * ((k : ℝ) + 1) * η⁻¹ ^ (k + 2) * ‖y‖ ^ 2)) := by
  have hz0 : z.im ≠ 0 := fun h => absurd hz (by rw [h]; simpa using hη)
  have hMb : (blockMat d L W M).IsHermitian := LoopC2N_isHermitian_blockMat hM
  have hyb : (blockMat d L W y).IsHermitian := LoopC2N_isHermitian_blockMat hy
  have hE1 : ∀ p : Bool × Zd d L, ‖Eblk d L W p.2‖ ≤ 1 := fun p => by
    refine (norm_Eblk_le_inv_W_sq d L W p.2).trans ?_
    have hW1 : (1 : ℝ) ≤ (W : ℝ) := Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne W))
    have hW2 : (1 : ℝ) ≤ (W : ℝ) ^ d := one_le_pow₀ hW1
    exact inv_le_one_of_one_le₀ hW2
  obtain ⟨P1, P2, hd1, hd2, -, -, hb2⟩ := LoopC2N_word_jets
    (R := fun (p : Bool × Zd d L) (s : ℝ) =>
      Gres (blockMat d L W M + (s : ℂ) • blockMat d L W y) z p.1)
    (E := fun p : Bool × Zd d L => Eblk d L W p.2) (D := blockMat d L W y) (K := η⁻¹)
    (fun p t => LoopC2N_hasDerivAt_Gres hMb hyb hz0 p.1 t)
    (fun p t => norm_Gsig_le_inv_eta (LoopC2N_isHermitian_add_realSmul hMb hyb t) hη hz p.1)
    hE1 ((List.ofFn σ).zip (List.ofFn b))
  refine ⟨fun t => Matrix.trace (P1 t), fun t => Matrix.trace (P2 t), ?_, ?_, ?_⟩
  · intro t
    have hfun : (fun s : ℝ => loopL d L W (blockMat d L W (M + (s : ℂ) • y)) z (loopOf σ b))
        = fun s : ℝ => Matrix.trace (LoopC2N_word
          (fun (p : Bool × Zd d L) (s : ℝ) =>
            Gres (blockMat d L W M + (s : ℂ) • blockMat d L W y) z p.1)
          (fun p : Bool × Zd d L => Eblk d L W p.2) ((List.ofFn σ).zip (List.ofFn b)) s) := by
      funext s
      rw [LoopC2N_blockMat_add_smul]
      rfl
    rw [hfun]
    exact LoopC2N_trace_hasDerivAt (hd1 t)
  · intro t
    exact LoopC2N_trace_hasDerivAt (hd2 t)
  · intro t
    refine (norm_matrix_trace_le_card_mul _).trans ?_
    rw [card_BlockIndex]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hlen : ((List.ofFn σ).zip (List.ofFn b)).length = k := by simp
    have h2 := hb2 t
    rw [hlen, LoopC2N_norm_blockMat] at h2
    exact h2

/-- (H3): the second derivative of the `k`-loop observable in a Hermitian direction. -/
private theorem LoopC2N_second_deriv_bound {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|)
    {k : ℕ} (σ : Fin k → Bool) (b : Fin k → Zd d L) {M y : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hM : M.IsHermitian) (hy : y.IsHermitian) :
    ‖fderiv ℝ (fderiv ℝ
        (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ =>
          loopL d L W (blockMat d L W M') z (loopOf σ b))) M y y‖
      ≤ (((L * W) ^ d : ℕ) : ℝ) * ((k : ℝ) * ((k : ℝ) + 1) * η⁻¹ ^ (k + 2) * ‖y‖ ^ 2) := by
  have hz0 : z.im ≠ 0 := fun h => absurd hz (by rw [h]; simpa using hη)
  obtain ⟨φ₁, φ₂, h₀, hd2, hb⟩ := LoopC2N_line_jets (d := d) (L := L) (W := W) hη hz σ b hM hy
  rw [LoopC2N_fderiv2_of_line
    (fun M' hM' => LoopC2N_contDiffAt_loop (d := d) (L := L) (W := W) hz0 σ b hM') hM hy h₀ hd2]
  exact hb 0

end Observable

/-! ### 5. The target -/

section Target

variable {d : ℕ} (sz : Sizes d)

/-- **Pin `HermTestFunLoopN`** (RBM2D `Induction/GridGoodN.lean:365`, section `TestClass`, with
`N = (W L)^d`): every `k`-loop observable `M ↦ 𝓛_{z_u,σ,b}(M)` (any length `k`, any signs,
complex-valued) is in the Hermitian test class and has the Hermitian second-derivative bound
`‖∂²𝓛(M)[y,y]‖ ≤ k(k+1) N η_u^{-(k+2)} ‖y‖²`, `z = z_u`, `η_u = (1 - u) Im m`
(`∂²` of a product of `k` resolvents has `2k + k(k−1)` terms).  It is the input `hΦ` of
`azumaSubG_ugen` and of `YMomentsN` (`C₂` in `stepDecompN`).  Differences from RBM2D: `Z2 → Zd d`,
`gloop → loopL`, `spectralZ → zt`, `W² → W^d` through `Sizes.size`; RBM2D's `[NeZero k]` is
dropped (the proof does not use it; T2111a). -/
def HermTestFunLoopN : Prop :=
  ∀ (k : ℕ) (n : ℕ) (E u : ℝ), |E| < 2 → 0 ≤ u → u < 1 →
    ∀ (σ : Fin k → Bool) (b : Fin k → Zd d (sz.L n)),
      HermTestFun sz n (fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
        loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) (zt E u) (loopOf σ b)) ∧
      ∀ M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian →
        y.IsHermitian →
        ‖fderiv ℝ (fderiv ℝ (fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
            loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) (zt E u)
              (loopOf σ b))) M y y‖ ≤
          ((k * (k + 1) : ℕ) : ℝ) * (Sizes.size sz n : ℝ) * (etaT E u)⁻¹ ^ (k + 2) * ‖y‖ ^ 2

/-- **`HermTestFunLoopN`, the general-length `C²` bound of the loop observables** (`LC2N:441`).
The merged pin with no added hypothesis; `0 ≤ u` is not used (as in the merged `k = 2` case).
The proof uses `‖E_b‖ ≤ (W^d)⁻¹ ≤ 1` (dropping the factor `W^{-dk}`), so the constant is the
count `k (k + 1)` of the Leibniz terms. -/
theorem hermTestFunLoopN : HermTestFunLoopN sz := by
  intro k n E u hE _hu0 hu1 σ b
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hpos : 0 < (1 - u) * (mE E).im := mul_pos (by linarith) (mE_im_pos hE)
  have hz : etaT E u ≤ |(zt E u).im| := by
    rw [zt_im, abs_of_pos hpos]
    exact le_of_eq rfl
  have hz0 : (zt E u).im ≠ 0 := by
    rw [zt_im]; exact hpos.ne'
  have hwf : (loopOf σ b).WF := by
    simp [Loop.LoopIdx.WF, loopOf]
  refine ⟨⟨fun M hM => LoopC2N_contDiffAt_loop hz0 σ b hM,
    ⟨_, fun M hM => norm_gloop_le_crude d (sz.L n) (sz.W n)
      (LoopC2N_isHermitian_blockMat hM) hη hz (loopOf σ b) hwf⟩⟩, ?_⟩
  intro M y hM hy
  have h := LoopC2N_second_deriv_bound (d := d) (L := sz.L n) (W := sz.W n) hη hz σ b hM hy
  refine h.trans (le_of_eq ?_)
  have hN : (((sz.L n * sz.W n) ^ d : ℕ) : ℝ) = (Sizes.size sz n : ℝ) := by
    rw [Sizes.size, mul_comm]
  rw [hN]
  push_cast
  ring

end Target

/-! ### 6. Compiled nonempty instances of `hermTestFunLoopN`

Data: the merged admissible sequence `sz0` (`RBM3D/Defs/Sizes.lean`, `d = 3`, `n = 0`: `L = 4`,
`W = 32`, `N = size 0 = 2097152`), energy `E = 0` (`|E| < 2`), `u = 1/2` (`0 ≤ u < 1`, so
`η_u = (1/2) Im m > 0`).  The signs and labels are given in each statement; the bound is evaluated
at the Hermitian pair `M = 0`, `y = 1`.  Every hypothesis of the theorem is discharged; there is no
external pin. -/

namespace LoopC2NCheck

open RBM.Gauss.SizesInst

/-- The data are nondegenerate: `N = 2097152` and `η_u > 0`. -/
theorem instance_data : Sizes.size sz0 0 = 2097152 ∧ 0 < etaT (0 : ℝ) (1 / 2) :=
  ⟨sz0_values.2.2.1, etaT_pos (by norm_num) (by norm_num)⟩

/-- **`hermTestFunLoopN` at `k = 3`**, `σ = (+,-,+)`, `b = ![0, 1, 2]` (three distinct blocks):
both conjuncts, the bound at the Hermitian pair `M = 0`, `y = 1`. -/
theorem hermTestFunLoopN_k3_instance :
    HermTestFun sz0 0
        (fun M : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ =>
          loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0) M) (zt 0 (1 / 2))
            (loopOf ![true, false, true] ![0, 1, 2])) ∧
      ‖fderiv ℝ (fderiv ℝ
          (fun M : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ =>
            loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0) M) (zt 0 (1 / 2))
              (loopOf ![true, false, true] ![0, 1, 2]))) 0 1 1‖ ≤
        ((3 * (3 + 1) : ℕ) : ℝ) * (Sizes.size sz0 0 : ℝ) * (etaT (0 : ℝ) (1 / 2))⁻¹ ^ (3 + 2) *
          ‖(1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)‖ ^ 2 := by
  have h := hermTestFunLoopN sz0 3 0 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    ![true, false, true] ![0, 1, 2]
  exact ⟨h.1, h.2 0 1 Matrix.isHermitian_zero Matrix.isHermitian_one⟩

/-- **`hermTestFunLoopN` at `k = 3`, `σ = (+,-,+)`, `b = ![0, 0, 0]`** (one block repeated):
both conjuncts, the bound at `M = 0`, `y = 1`.  (For distinct blocks `E_{b₁} E_{b₂} = 0`, so along
`s ↦ s • 1`, where the resolvents are scalars, the observable of the previous instance vanishes;
a repeated block does not have this property.) -/
theorem hermTestFunLoopN_k3_same_instance :
    HermTestFun sz0 0
        (fun M : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ =>
          loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0) M) (zt 0 (1 / 2))
            (loopOf ![true, false, true] ![0, 0, 0])) ∧
      ‖fderiv ℝ (fderiv ℝ
          (fun M : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ =>
            loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0) M) (zt 0 (1 / 2))
              (loopOf ![true, false, true] ![0, 0, 0]))) 0 1 1‖ ≤
        ((3 * (3 + 1) : ℕ) : ℝ) * (Sizes.size sz0 0 : ℝ) * (etaT (0 : ℝ) (1 / 2))⁻¹ ^ (3 + 2) *
          ‖(1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)‖ ^ 2 := by
  have h := hermTestFunLoopN sz0 3 0 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    ![true, false, true] ![0, 0, 0]
  exact ⟨h.1, h.2 0 1 Matrix.isHermitian_zero Matrix.isHermitian_one⟩

/-- **`hermTestFunLoopN` at `k = 1`**, `σ = (+)`, `b = ![0]`: both conjuncts, the bound
(`k (k + 1) = 2`, exponent `k + 2 = 3`) at `M = 0`, `y = 1`. -/
theorem hermTestFunLoopN_k1_instance :
    HermTestFun sz0 0
        (fun M : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ =>
          loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0) M) (zt 0 (1 / 2))
            (loopOf ![true] ![0])) ∧
      ‖fderiv ℝ (fderiv ℝ
          (fun M : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ =>
            loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0) M) (zt 0 (1 / 2))
              (loopOf ![true] ![0]))) 0 1 1‖ ≤
        ((1 * (1 + 1) : ℕ) : ℝ) * (Sizes.size sz0 0 : ℝ) * (etaT (0 : ℝ) (1 / 2))⁻¹ ^ (1 + 2) *
          ‖(1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)‖ ^ 2 := by
  have h := hermTestFunLoopN sz0 1 0 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    ![true] ![0]
  exact ⟨h.1, h.2 0 1 Matrix.isHermitian_zero Matrix.isHermitian_one⟩

end LoopC2NCheck

end RBM.Ind

end

#print axioms RBM.Ind.hermTestFunLoopN
#print axioms RBM.Ind.LoopC2NCheck.instance_data
#print axioms RBM.Ind.LoopC2NCheck.hermTestFunLoopN_k3_instance
#print axioms RBM.Ind.LoopC2NCheck.hermTestFunLoopN_k3_same_instance
#print axioms RBM.Ind.LoopC2NCheck.hermTestFunLoopN_k1_instance
