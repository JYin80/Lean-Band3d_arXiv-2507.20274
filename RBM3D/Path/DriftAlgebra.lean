/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Path.OneStep
import RBM3D.Induction.Step2Defs
import RBM3D.Hierarchy.ContractionBasic
import RBM3D.Propagator.Props4
import RBM3D.Propagator.Deriv
import RBM3D.Loop.KLTree

/-!
# The `n = 2` loop hierarchy at matrix level (ST2-21, part 2)

Ticket T2083 (ST2-21).  Port of `RBM2D/Path/DriftAlgebra.lean` at commit `c9a24cf` (cited
`DriftAlgebra:<line>`; RBM2D ticket T2079, row E.1 of the T2049 design).  Renaming rules R1-R4 of
`docs/tickets/ST1-COMMON.md`, `W^2 → W^d`, `Z2 L → Zd d L`, and the merged vocabulary:

* RBM2D's `Kpm`, `loopPM`, `lkMat`, `LLpair`, `EGt`, `ELKLK`, `loop3`, `thetaGen` of
  `Path/Step2Vocab` and `Path/UBounds` are the merged `STKloop`, `STLM`, `STLKM`, `STEGtM`,
  `STELKLKM`, `STthetaOp` of `RBM3D/Induction/Step2Defs.lean` / `Induction/Defs.lean` (at the
  signs `σ = (+,-)`); the pair `(L, W, g)` of the matrix is `(sz.L n, sz.W n, sz.lam n)`.
* The three pinned `Prop`s `KpmODE`, `LoopGenN2`, `HierarchyN2` quantify over `sz : Sizes d` and
  `n` (so `3 ≤ L` is `sz.three_le_L n`), and are proved: `kpmODE`, `loopGenN2`, `hierarchyN2`.
* `Kpm = W^{-d} Θ_u` (`|m|² = 1`) is the merged `kTwo` (`KLK_two_eq_kTwo`); its ODE is
  `hasDerivAt_kTwo` (`RBM3D/Loop/Primitive.lean`); the coordinate contraction is `sum_allCoords_trace_blocks`.

Paper: arXiv:2507.20274, (`pro_dyncalK`) and (`Kn2sol`) (`1_2`), (`eq:mainStoflow`) and
(`def_EwtG`) (`1_2`), (`def_ELKLK`), (`DefTHUST`), (`LK_SDE`) (`3_5`).

Every other helper is `private` or prefixed `DriftAlgebra_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Loop
open scoped NNReal ENNReal

/-! ## Pins (E.1) -/

/-- **Pin E.1a (`𝒦` ODE at `n = 2`)**, (`pro_dyncalK`) with (`Kn2sol`):
`∂_u 𝒦_{(+,-),(a,b)} = W^d Σ_{c,e} 𝒦_{(a,c)} S^{(B)}_{ce} 𝒦_{(e,b)}`.
(`DriftAlgebra:55`, `KpmODE`; `Kpm` is `STKloop` at `σ = (+,-)`.) -/
def KpmODE (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
    ∀ a b : Zd d (sz.L n),
      HasDerivAt (fun v : ℝ => sz.STKloop n E v ![true, false] ![a, b])
        ((((sz.W n : ℕ) : ℂ) ^ d) * ∑ c : Zd d (sz.L n), ∑ e : Zd d (sz.L n),
          sz.STKloop n E u ![true, false] ![a, c] * SB d (sz.L n) (sz.lam n) c e *
            sz.STKloop n E u ![true, false] ![e, b]) u

/-- **Pin E.1b (loop generator at `n = 2`)**, (`eq:mainStoflow`) drift part at `σ = (+,-)`:
`genMat(𝓛_{(a₁,a₂)}) = W^d Σ_{b₁,b₂} 𝓛_{(a₁,b₁)} S_{b₁b₂} 𝓛_{(b₂,a₂)} + 𝓔^{(G̃)}`, for Hermitian
`M` (`DriftAlgebra:62`, `LoopGenN2`; the first term is `LLpair`, the second `STEGtM`). -/
def LoopGenN2 (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian →
      ∀ a₁ a₂ : Zd d (sz.L n),
        genMat d (sz.L n) (sz.W n) (sz.lam n) E u M ⟨[true, false], [a₁, a₂]⟩ =
          (((sz.W n : ℕ) : ℂ) ^ d) * ∑ b₁ : Zd d (sz.L n), ∑ b₂ : Zd d (sz.L n),
              sz.STLM n E u M ![true, false] ![a₁, b₁] * SB d (sz.L n) (sz.lam n) b₁ b₂ *
                sz.STLM n E u M ![true, false] ![b₂, a₂] +
            sz.STEGtM n E u M ![true, false] ![a₁, a₂]

/-- **Pin E.1c (the `(𝓛 - 𝒦)` hierarchy at `n = 2`)**, (`LK_SDE`) drift part with the generator
`ξ S Θ` in each slot: `genMat(𝓛) - ∂_u 𝒦 = Θ^{(2)}∘(𝓛-𝒦) + 𝓔^{LK×LK} + 𝓔^{(G̃)}`, at `σ = (+,-)`
(`DriftAlgebra:69`, `HierarchyN2`; `thetaGen` is `STthetaOp`). -/
def HierarchyN2 (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian →
      ∀ a₁ a₂ : Zd d (sz.L n),
        genMat d (sz.L n) (sz.W n) (sz.lam n) E u M ⟨[true, false], [a₁, a₂]⟩ -
            deriv (fun v : ℝ => sz.STKloop n E v ![true, false] ![a₁, a₂]) u =
          sz.STthetaOp n E u ![true, false] (sz.STLKM n E u M ![true, false]) ![a₁, a₂] +
            sz.STELKLKM n E u M ![true, false] ![a₁, a₂] +
            sz.STEGtM n E u M ![true, false] ![a₁, a₂]

/-! ## 1. The `𝒦` ODE at `n = 2` -/

section KODE

variable {d L : ℕ} [NeZero L] {W : ℕ} {g : ℝ}

/-- `m(+) m(-) = |m|² = 1` for `|E| < 2` (`DriftAlgebra:84`, `DriftAlgebra_normSq_one`). -/
private theorem DriftAlgebra_mSigma_mul {E : ℝ} (hE : |E| < 2) :
    mSigma E true * mSigma E false = 1 := by
  simp only [mSigma, ite_true, Bool.false_eq_true, ite_false]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mE hE.le]
  simp

/-- `STKloop` at `σ = (+,-)` is `kTwo` (`DriftAlgebra:89`, `Kpm = W^{-d} Θ_u`). -/
private theorem DriftAlgebra_STKloop_eq (sz : Sizes d) (n : ℕ) (E v : ℝ) (x y : Zd d (sz.L n)) :
    sz.STKloop n E v ![true, false] ![x, y] =
      kTwo d (sz.L n) (sz.W n) (sz.lam n) (mSigma E) v true false x y := by
  have hI : KLloopOf d (sz.L n) ![true, false] ![x, y] = ⟨[true, false], [x, y]⟩ := by
    simp [KLloopOf]
  unfold Sizes.STKloop
  rw [hI]
  exact KLK_two_eq_kTwo d (sz.L n) (sz.lam n) (sz.W n) E v true false x y

end KODE

/-- **`KpmODE`** (pin E.1a). -/
theorem kpmODE (d : ℕ) : KpmODE d := by
  intro sz n E hE u hu0 hu1 a b
  have hu : ‖(u : ℂ) * (mSigma E true * mSigma E false)‖ < 1 := by
    rw [DriftAlgebra_mSigma_mul hE, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hu0]
    exact hu1
  have hW : ((sz.W n : ℕ) : ℂ) ^ d ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne (sz.W n)))
  have h := hasDerivAt_kTwo (norm_SB d (sz.L n) (sz.lam n) (sz.three_le_L n)) hW (mSigma E) true
    false hu a b
  simp only [DriftAlgebra_STKloop_eq]
  exact h

/-! ## 2. Derivatives of the two-loop word -/

section Word

open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Trace commutes with the derivative (as `OneStep_hasDerivAt_trace`, which is private;
`DriftAlgebra:132`). -/
private theorem DriftAlgebra_hasDerivAt_trace {f : ℝ → Matrix n n ℂ} {f' : Matrix n n ℂ} {t : ℝ}
    (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => Matrix.trace (f s)) (Matrix.trace f') t := by
  set T : Matrix n n ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap ((Matrix.traceLinearMap n ℂ ℂ).restrictScalars ℝ)
  have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
  have := T.hasFDerivAt.comp_hasDerivAt t h
  simpa only [hT, Function.comp_def] using this

/-- A signed resolvent along a moving Hermitian matrix and spectral parameter
(as `OneStep_hasDerivAt_Gsig`, which is private; `DriftAlgebra:143`). -/
private theorem DriftAlgebra_hasDerivAt_Gres {H : ℝ → Matrix n n ℂ} {zf : ℝ → ℂ}
    {H' : Matrix n n ℂ} {z' : ℂ} {t : ℝ}
    (hH : HasDerivAt H H' t) (hz : HasDerivAt zf z' t) (hherm : (H t).IsHermitian)
    (him : (zf t).im ≠ 0) (σ : Bool) :
    HasDerivAt (fun s => Gres (H s) (zf s) σ)
      (-(Gres (H t) (zf t) σ *
        (H' - (if σ then z' else (starRingEnd ℂ) z') • (1 : Matrix n n ℂ)) *
        Gres (H t) (zf t) σ)) t := by
  cases σ with
  | true => exact hasDerivAt_green_moving hH hz hherm him
  | false =>
      have hz' : HasDerivAt (fun s => (starRingEnd ℂ) (zf s)) ((starRingEnd ℂ) z') t := hz.star
      have him' : ((starRingEnd ℂ) (zf t)).im ≠ 0 := by simpa using him
      exact hasDerivAt_green_moving hH hz' hherm him'

set_option linter.unusedFintypeInType false in
/-- The affine line `s ↦ M + s • A` has derivative `A`. -/
private theorem DriftAlgebra_hasDerivAt_line (M A : Matrix n n ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => M + (s : ℂ) • A) A t := by
  have h : HasDerivAt (fun s : ℝ => (s : ℂ) • A) A t := by
    simpa using (hasDerivAt_id t).smul_const A
  simpa using h.const_add M

omit [Fintype n] [DecidableEq n] in
/-- A real multiple of a Hermitian matrix added to a Hermitian matrix is Hermitian. -/
private theorem DriftAlgebra_isHermitian_add_realSmul {M A : Matrix n n ℂ} (hM : M.IsHermitian)
    (hA : A.IsHermitian) (s : ℝ) : (M + (s : ℂ) • A).IsHermitian := by
  refine hM.add ?_
  change Matrix.conjTranspose ((s : ℂ) • A) = (s : ℂ) • A
  rw [Matrix.conjTranspose_smul, hA, Complex.star_def, Complex.conj_ofReal]

variable {R : ℝ → Bool → Matrix n n ℂ} {D : Bool → Matrix n n ℂ} {t : ℝ}

/-- First derivative of `R₊ A R₋ B` when `R_σ' = -R_σ D_σ R_σ` (`DriftAlgebra:161`). -/
private theorem DriftAlgebra_hasDerivAt_word1
    (hR : ∀ σ, HasDerivAt (fun s => R s σ) (-(R t σ * D σ * R t σ)) t) (A B : Matrix n n ℂ) :
    HasDerivAt (fun s => R s true * A * R s false * B)
      (-(R t true * D true * R t true * A * R t false * B) -
        R t true * A * R t false * D false * R t false * B) t := by
  have h := (((hR true).mul_const A).mul (hR false)).mul_const B
  refine h.congr_deriv ?_
  noncomm_ring

/-- Second derivative of `R₊ A R₋ B` when `R_σ' = -R_σ D_σ R_σ` (`DriftAlgebra:171`). -/
private theorem DriftAlgebra_hasDerivAt_word2
    (hR : ∀ σ, HasDerivAt (fun s => R s σ) (-(R t σ * D σ * R t σ)) t) (A B : Matrix n n ℂ) :
    HasDerivAt (fun s => -(R s true * D true * R s true * A * R s false * B) -
        R s true * A * R s false * D false * R s false * B)
      (R t true * D true * R t true * D true * R t true * A * R t false * B +
        R t true * D true * R t true * D true * R t true * A * R t false * B +
        (R t true * D true * R t true * A * R t false * D false * R t false * B +
          R t true * D true * R t true * A * R t false * D false * R t false * B) +
        (R t true * A * R t false * D false * R t false * D false * R t false * B +
          R t true * A * R t false * D false * R t false * D false * R t false * B)) t := by
  have h1 := (((((hR true).mul_const (D true)).mul (hR true)).mul_const A).mul
    (hR false)).mul_const B
  have h2 := (((((hR true).mul_const A).mul (hR false)).mul_const (D false)).mul
    (hR false)).mul_const B
  refine (h1.neg.sub h2).congr_deriv ?_
  simp only [Pi.mul_apply]
  noncomm_ring

end Word

/-! ## 3. The two-loop at a block matrix: space and spectral derivatives -/

section Loop

open scoped Matrix.Norms.L2Operator

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The `(+,-)` two-loop as one trace (`DriftAlgebra:200`). -/
private theorem DriftAlgebra_loopL_pm (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (a b : Zd d L) :
    loopL d L W H z ⟨[true, false], [a, b]⟩ =
      Matrix.trace (Gres H z true * Eblk d L W a * Gres H z false * Eblk d L W b) := by
  simp [loopL, Matrix.mul_assoc]

/-- A fine-lattice loop of length two (`STLM` at `σ = (+,-)`) as one trace. -/
private theorem DriftAlgebra_loopFine_pm (M : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ)
    (a b : Zd d L) :
    loopFine d L W M z ![true, false] ![a, b] =
      Matrix.trace (Gres (blockMat d L W M) z true * Eblk d L W a *
        Gres (blockMat d L W M) z false * Eblk d L W b) := by
  simp [loopFine, loopM, Matrix.mul_assoc]

/-- A fine-lattice loop of length three as one trace (`DriftAlgebra:207`). -/
private theorem DriftAlgebra_loopFine_three (M : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ)
    (s₁ s₂ s₃ : Bool) (x y w : Zd d L) :
    loopFine d L W M z ![s₁, s₂, s₃] ![x, y, w] =
      Matrix.trace (Gres (blockMat d L W M) z s₁ * Eblk d L W x * Gres (blockMat d L W M) z s₂ *
        Eblk d L W y * Gres (blockMat d L W M) z s₃ * Eblk d L W w) := by
  simp [loopFine, loopM, List.ofFn_succ, Matrix.mul_assoc]

/-- A fine-lattice loop of length one as one trace. -/
private theorem DriftAlgebra_loopFine_one (M : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ)
    (σ : Bool) (a : Zd d L) :
    loopFine d L W M z (fun _ : Fin 1 => σ) (fun _ => a) =
      Matrix.trace (Gres (blockMat d L W M) z σ * Eblk d L W a) := by
  simp [loopFine, loopM]

/-- `blockMat` is real-affine along a line (`DriftAlgebra:215`). -/
private theorem DriftAlgebra_blockMat_add_smul (M C : Matrix (Idx d L W) (Idx d L W) ℂ) (y : ℂ) :
    blockMat d L W (M + y • C) = blockMat d L W M + y • blockMat d L W C := by
  ext i j
  simp [blockMat]

/-- The second derivative of the two-loop along a Hermitian line, at `0`: two same-edge cuts and
one pair cut, each counted twice (`DriftAlgebra:222`). -/
private theorem DriftAlgebra_deriv2_line {H B : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) (hB : B.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (a b : Zd d L) :
    deriv (deriv (fun y : ℝ => loopL d L W (H + (y : ℂ) • B) z ⟨[true, false], [a, b]⟩)) 0 =
      2 * (Matrix.trace (Gres H z true * B * Gres H z true * B * Gres H z true * Eblk d L W a *
            Gres H z false * Eblk d L W b) +
          Matrix.trace (Gres H z true * B * Gres H z true * Eblk d L W a * Gres H z false * B *
            Gres H z false * Eblk d L W b) +
          Matrix.trace (Gres H z true * Eblk d L W a * Gres H z false * B * Gres H z false * B *
            Gres H z false * Eblk d L W b)) := by
  set R : ℝ → Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ :=
    fun s σ => Gres (H + (s : ℂ) • B) z σ with hRdef
  have hR : ∀ y : ℝ, ∀ σ, HasDerivAt (fun s => R s σ) (-(R y σ * (fun _ => B) σ * R y σ)) y := by
    intro y σ
    have := DriftAlgebra_hasDerivAt_Gres (DriftAlgebra_hasDerivAt_line H B y)
      (hasDerivAt_const y z) (DriftAlgebra_isHermitian_add_realSmul hH hB y) hz σ
    simpa [hRdef] using this
  have h1 : deriv (fun y : ℝ => loopL d L W (H + (y : ℂ) • B) z ⟨[true, false], [a, b]⟩) =
      fun y => Matrix.trace (-(R y true * B * R y true * Eblk d L W a * R y false * Eblk d L W b) -
        R y true * Eblk d L W a * R y false * B * R y false * Eblk d L W b) := by
    funext y
    simp only [DriftAlgebra_loopL_pm]
    exact (DriftAlgebra_hasDerivAt_trace
      (DriftAlgebra_hasDerivAt_word1 (hR y) (Eblk d L W a) (Eblk d L W b))).deriv
  rw [h1]
  have h2 := (DriftAlgebra_hasDerivAt_trace
    (DriftAlgebra_hasDerivAt_word2 (D := fun _ => B) (hR 0) (Eblk d L W a) (Eblk d L W b))).deriv
  rw [h2]
  simp only [hRdef, Complex.ofReal_zero, zero_smul, add_zero, Matrix.trace_add]
  ring

/-- The spectral derivative of the two-loop at a Hermitian block matrix (`DriftAlgebra:253`). -/
private theorem DriftAlgebra_deriv_spec {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) {E u : ℝ} (hE : |E| < 2) (hu : u < 1) (a b : Zd d L) :
    deriv (fun v : ℝ => loopL d L W H (zt E v) ⟨[true, false], [a, b]⟩) u =
      -(mE E * Matrix.trace (Gres H (zt E u) true * Gres H (zt E u) true *
          Eblk d L W a * Gres H (zt E u) false * Eblk d L W b)) -
        (starRingEnd ℂ) (mE E) * Matrix.trace (Gres H (zt E u) true * Eblk d L W a *
          Gres H (zt E u) false * Gres H (zt E u) false * Eblk d L W b) := by
  have him : (zt E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  set R : ℝ → Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ :=
    fun s σ => Gres H (zt E s) σ with hRdef
  set D : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ :=
    fun σ => (if σ then mE E else (starRingEnd ℂ) (mE E)) •
      (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) with hDdef
  have hR : ∀ σ, HasDerivAt (fun s => R s σ) (-(R u σ * D σ * R u σ)) u := by
    intro σ
    have := DriftAlgebra_hasDerivAt_Gres (hasDerivAt_const u H) (hasDerivAt_spectralZ E u) hH
      him σ
    refine this.congr_deriv ?_
    cases σ <;> simp [hDdef, hRdef]
  have h := (DriftAlgebra_hasDerivAt_trace
    (DriftAlgebra_hasDerivAt_word1 hR (Eblk d L W a) (Eblk d L W b))).deriv
  simp only [DriftAlgebra_loopL_pm]
  rw [h]
  simp only [hRdef, hDdef, ite_true, Bool.false_eq_true, ite_false, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.trace_sub, Matrix.trace_neg, Matrix.trace_smul, smul_eq_mul]

/-- The coordinate contraction at block level (`Gauss.sum_allCoords_trace_blocks`;
`DriftAlgebra:282`, coefficient `W^d`, `S^{(B)}(g)`). -/
private theorem DriftAlgebra_cov (g : ℝ) (X Y : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
        Matrix.trace (X * blockMat d L W (coordinateMatrix d L W c) * Y *
          blockMat d L W (coordinateMatrix d L W c)) =
      (W : ℂ) ^ d * ∑ p : Zd d L, ∑ q : Zd d L,
        Matrix.trace (X * Eblk d L W p) * SB d L g p q * Matrix.trace (Y * Eblk d L W q) := by
  have key := sum_allCoords_trace_blocks d L W g (X.submatrix (split d L W) (split d L W))
    (Y.submatrix (split d L W) (split d L W))
  rw [blockRelabel_submatrix_split, blockRelabel_submatrix_split] at key
  rw [← key]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  have hX := blockRelabel_submatrix_split d L W X
  have hY := blockRelabel_submatrix_split d L W Y
  have hmul : ∀ P Q : Matrix (Idx d L W) (Idx d L W) ℂ,
      blockRelabel d L W (P * Q) = blockRelabel d L W P * blockRelabel d L W Q :=
    fun P Q => (Matrix.submatrix_mul_equiv P Q
      (splitEquiv d L W).symm (splitEquiv d L W).symm (splitEquiv d L W).symm).symm
  have htr : ∀ P : Matrix (Idx d L W) (Idx d L W) ℂ,
      Matrix.trace (blockRelabel d L W P) = Matrix.trace P := by
    intro P
    simp only [Matrix.trace, Matrix.diag, blockRelabel]
    exact Equiv.sum_comp (splitEquiv d L W).symm (fun i => P i i)
  have hC : blockMat d L W (coordinateMatrix d L W c) =
      blockRelabel d L W (coordinateMatrix d L W c) := rfl
  conv_lhs => rw [← hX, ← hY, hC, ← hmul, ← hmul, ← hmul, htr]

end Loop

/-! ## 4. The loop generator at `n = 2` -/

section Gen

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The blocks partition the identity with factor `W^{-d}` (RBM2D `Defs/Model.lean:83`,
`sum_Eblk`). -/
private theorem DriftAlgebra_sum_Eblk :
    ∑ a : Zd d L, Eblk d L W a = (((W : ℂ) ^ d)⁻¹) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) := by
  ext p q
  simp only [Matrix.sum_apply, Eblk, Matrix.diagonal_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  split_ifs with h
  · simp [Finset.sum_ite_eq]
  · simp

/-- Inserting `1 = W^d Σ_p E_p` in a trace (`DriftAlgebra:318`). -/
private theorem DriftAlgebra_trace_insert (X Y : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    Matrix.trace (X * Y) = (W : ℂ) ^ d * ∑ p : Zd d L, Matrix.trace (X * Eblk d L W p * Y) := by
  have hW : (W : ℂ) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne W))
  have h : ∑ p : Zd d L, Matrix.trace (X * Eblk d L W p * Y) =
      Matrix.trace (X * (∑ p : Zd d L, Eblk d L W p) * Y) := by
    rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]
  rw [h, DriftAlgebra_sum_Eblk, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
    Matrix.mul_one, smul_eq_mul, ← mul_assoc]
  field_simp

/-- Column sums of `S^{(B)}` are `1` (`DriftAlgebra:329`). -/
private theorem DriftAlgebra_sum_SB_col (g : ℝ) (hL : 3 ≤ L) (b : Zd d L) :
    ∑ a : Zd d L, SB d L g a b = 1 := by
  rw [← sum_SB_row d L g hL b]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact congrFun (congrFun (SB_transpose d L g) b) a

/-- The final finite-sum algebra of `loopGenN2` (`DriftAlgebra:335`). -/
private theorem DriftAlgebra_sum_algebra (g : ℝ) (hL : 3 ≤ L) (w m m' : ℂ)
    (f₁ f₂ g₁ g₂ : Zd d L → ℂ) (P : Zd d L → Zd d L → ℂ) (a b : Zd d L) :
    w * ∑ p : Zd d L, ∑ q : Zd d L, f₁ p * SB d L g p q * g₁ q +
        w * ∑ p : Zd d L, ∑ q : Zd d L, P p b * SB d L g p q * P a q +
        w * ∑ p : Zd d L, ∑ q : Zd d L, f₂ p * SB d L g p q * g₂ q +
      (-(m * (w * ∑ p : Zd d L, f₁ p)) - m' * (w * ∑ p : Zd d L, f₂ p)) =
    w * ∑ b₁ : Zd d L, ∑ b₂ : Zd d L, P a b₁ * SB d L g b₁ b₂ * P b₂ b +
      w * ∑ a' : Zd d L, ∑ b' : Zd d L,
        ((g₁ a' - m) * SB d L g a' b' * f₁ b' + (g₂ a' - m') * SB d L g a' b' * f₂ b') := by
  have hS : ∀ p q : Zd d L, SB d L g p q = SB d L g q p := fun p q =>
    congrFun (congrFun (SB_transpose d L g) q) p
  have hP : ∑ p : Zd d L, ∑ q : Zd d L, P p b * SB d L g p q * P a q =
      ∑ b₁ : Zd d L, ∑ b₂ : Zd d L, P a b₁ * SB d L g b₁ b₂ * P b₂ b := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
    rw [hS p q]
    ring
  have hG : ∀ (f g' : Zd d L → ℂ) (m : ℂ),
      ∑ a' : Zd d L, ∑ b' : Zd d L, (g' a' - m) * SB d L g a' b' * f b' =
        ∑ p : Zd d L, ∑ q : Zd d L, f p * SB d L g p q * g' q - m * ∑ p : Zd d L, f p := by
    intro f g' m
    have h1 : ∑ a' : Zd d L, ∑ b' : Zd d L, g' a' * SB d L g a' b' * f b' =
        ∑ p : Zd d L, ∑ q : Zd d L, f p * SB d L g p q * g' q := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      rw [hS q p]
      ring
    have h2 : ∑ a' : Zd d L, ∑ b' : Zd d L, m * SB d L g a' b' * f b' = m * ∑ p : Zd d L, f p := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← Finset.sum_mul, ← Finset.mul_sum, DriftAlgebra_sum_SB_col g hL, mul_one]
    rw [← h1, ← h2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b' _ => ?_
    ring
  rw [Finset.sum_congr rfl fun a' _ => Finset.sum_add_distrib, Finset.sum_add_distrib, hG, hG, hP]
  ring

end Gen

/-- Rotation of a trace (`DriftAlgebra:389`). -/
private theorem DriftAlgebra_rot {n : Type*} [Fintype n] [DecidableEq n]
    (X Y : Matrix n n ℂ) : Matrix.trace (X * Y) = Matrix.trace (Y * X) :=
  Matrix.trace_mul_comm X Y

/-- **The matrix-level core of `loopGenN2`** (the body of `DriftAlgebra:396-524`, at `d`, `L`, `W`,
`g`), with `loopFine` in place of `STLM` and `mSigma` in place of `STmsig`. -/
private theorem DriftAlgebra_loopGen_core {d L W : ℕ} [NeZero L] [NeZero W] (g : ℝ) (hL : 3 ≤ L)
    {E u : ℝ} (hE : |E| < 2) (hu1 : u < 1) {M : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hM : M.IsHermitian) (a₁ a₂ : Zd d L) :
    genMat d L W g E u M ⟨[true, false], [a₁, a₂]⟩ =
      (W : ℂ) ^ d * ∑ b₁ : Zd d L, ∑ b₂ : Zd d L,
          loopFine d L W M (zt E u) ![true, false] ![a₁, b₁] * SB d L g b₁ b₂ *
            loopFine d L W M (zt E u) ![true, false] ![b₂, a₂] +
        (W : ℂ) ^ d * ∑ x : Zd d L, ∑ y : Zd d L,
          ((loopFine d L W M (zt E u) (fun _ : Fin 1 => true) (fun _ => x) - mSigma E true) *
              SB d L g x y *
              loopFine d L W M (zt E u) ![true, true, false] ![y, a₁, a₂] +
            (loopFine d L W M (zt E u) (fun _ : Fin 1 => false) (fun _ => x) - mSigma E false) *
              SB d L g x y *
              loopFine d L W M (zt E u) ![true, false, false] ![a₁, y, a₂]) := by
  have hz : (zt E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  have hH : (blockMat d L W M).IsHermitian := hM.submatrix _
  set H := blockMat d L W M with hHdef
  set z := zt E u with hzdef
  set Rp := Gres H z true with hRp
  set Rm := Gres H z false with hRm
  set Ea := Eblk d L W a₁ with hEa
  set Eb := Eblk d L W a₂ with hEb
  set Cb : CoordF d L W → Matrix (Vtx d L W) (Vtx d L W) ℂ :=
    fun c => blockMat d L W (coordinateMatrix d L W c) with hCb
  -- the space part, coordinate by coordinate
  have hspace : ∀ c : CoordF d L W, deriv (deriv (fun y : ℝ =>
        loopL d L W (blockMat d L W (M + (y : ℂ) • coordinateMatrix d L W c)) z
          ⟨[true, false], [a₁, a₂]⟩)) 0 =
      2 * (Matrix.trace ((Rp * Ea * Rm * Eb * Rp) * Cb c * Rp * Cb c) +
        Matrix.trace ((Rm * Eb * Rp) * Cb c * (Rp * Ea * Rm) * Cb c) +
        Matrix.trace ((Rm * Eb * Rp * Ea * Rm) * Cb c * Rm * Cb c)) := by
    intro c
    simp only [DriftAlgebra_blockMat_add_smul]
    rw [← hHdef, DriftAlgebra_deriv2_line (B := blockMat d L W (coordinateMatrix d L W c)) hH
      ((coordinateMatrix_isHermitian d L W c).submatrix _) hz]
    have h1 := DriftAlgebra_rot (Rp * Cb c * Rp * Cb c) (Rp * Ea * Rm * Eb)
    have h2 := DriftAlgebra_rot (Rp * Cb c * Rp * Ea * Rm * Cb c) (Rm * Eb)
    have h3 := DriftAlgebra_rot (Rp * Ea * Rm * Cb c * Rm * Cb c) (Rm * Eb)
    simp only [Matrix.mul_assoc] at h1 h2 h3 ⊢
    rw [h1, h2, h3]
  -- the spectral part
  have hspec := DriftAlgebra_deriv_spec (d := d) (L := L) (W := W) hH hE hu1 a₁ a₂
  -- the six trace identifications
  have e1 : ∀ p : Zd d L, Matrix.trace ((Rp * Ea * Rm * Eb * Rp) * Eblk d L W p) =
      loopFine d L W M z ![true, true, false] ![p, a₁, a₂] := by
    intro p
    rw [DriftAlgebra_loopFine_three]
    have h := DriftAlgebra_rot (Rp * Ea * Rm * Eb) (Rp * Eblk d L W p)
    simp only [Matrix.mul_assoc] at h ⊢
    exact h
  have e2 : ∀ p : Zd d L, Matrix.trace ((Rm * Eb * Rp) * Eblk d L W p) =
      loopFine d L W M z ![true, false] ![p, a₂] := by
    intro p
    rw [DriftAlgebra_loopFine_pm]
    have h := DriftAlgebra_rot (Rm * Eb) (Rp * Eblk d L W p)
    simp only [Matrix.mul_assoc] at h ⊢
    exact h
  have e3 : ∀ q : Zd d L, Matrix.trace ((Rp * Ea * Rm) * Eblk d L W q) =
      loopFine d L W M z ![true, false] ![a₁, q] := by
    intro q
    rw [DriftAlgebra_loopFine_pm]
  have e4 : ∀ p : Zd d L, Matrix.trace ((Rm * Eb * Rp * Ea * Rm) * Eblk d L W p) =
      loopFine d L W M z ![true, false, false] ![a₁, p, a₂] := by
    intro p
    rw [DriftAlgebra_loopFine_three]
    have h := DriftAlgebra_rot (Rm * Eb) (Rp * Ea * Rm * Eblk d L W p)
    simp only [Matrix.mul_assoc] at h ⊢
    exact h
  have e5 : Matrix.trace (Rp * Rp * Ea * Rm * Eb) =
      (W : ℂ) ^ d * ∑ p : Zd d L, loopFine d L W M z ![true, true, false] ![p, a₁, a₂] := by
    rw [show Rp * Rp * Ea * Rm * Eb = Rp * (Rp * Ea * Rm * Eb) by simp only [Matrix.mul_assoc],
      DriftAlgebra_trace_insert]
    refine congrArg _ (Finset.sum_congr rfl fun p _ => ?_)
    rw [DriftAlgebra_loopFine_three]
    simp only [Matrix.mul_assoc]
    rfl
  have e6 : Matrix.trace (Rp * Ea * Rm * Rm * Eb) =
      (W : ℂ) ^ d * ∑ p : Zd d L, loopFine d L W M z ![true, false, false] ![a₁, p, a₂] := by
    rw [show Rp * Ea * Rm * Rm * Eb = (Rp * Ea * Rm) * (Rm * Eb) by simp only [Matrix.mul_assoc],
      DriftAlgebra_trace_insert]
    refine congrArg _ (Finset.sum_congr rfl fun p _ => ?_)
    rw [DriftAlgebra_loopFine_three]
    simp only [Matrix.mul_assoc]
    rfl
  -- the left side
  have hlhs : genMat d L W g E u M ⟨[true, false], [a₁, a₂]⟩ =
      (W : ℂ) ^ d * ∑ p : Zd d L, ∑ q : Zd d L,
          loopFine d L W M z ![true, true, false] ![p, a₁, a₂] * SB d L g p q *
            Matrix.trace (Rp * Eblk d L W q) +
        (W : ℂ) ^ d * ∑ p : Zd d L, ∑ q : Zd d L,
          loopFine d L W M z ![true, false] ![p, a₂] * SB d L g p q *
            loopFine d L W M z ![true, false] ![a₁, q] +
        (W : ℂ) ^ d * ∑ p : Zd d L, ∑ q : Zd d L,
          loopFine d L W M z ![true, false, false] ![a₁, p, a₂] * SB d L g p q *
            Matrix.trace (Rm * Eblk d L W q) +
      (-(mE E * ((W : ℂ) ^ d * ∑ p : Zd d L,
          loopFine d L W M z ![true, true, false] ![p, a₁, a₂])) -
        (starRingEnd ℂ) (mE E) * ((W : ℂ) ^ d * ∑ p : Zd d L,
          loopFine d L W M z ![true, false, false] ![a₁, p, a₂])) := by
    rw [genMat, Finset.sum_congr rfl fun c _ => by rw [hspace c], hspec, ← e5, ← e6]
    have hsplit : (1 / 2 : ℂ) * ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
        (2 * (Matrix.trace ((Rp * Ea * Rm * Eb * Rp) * Cb c * Rp * Cb c) +
          Matrix.trace ((Rm * Eb * Rp) * Cb c * (Rp * Ea * Rm) * Cb c) +
          Matrix.trace ((Rm * Eb * Rp * Ea * Rm) * Cb c * Rm * Cb c))) =
        ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
            Matrix.trace ((Rp * Ea * Rm * Eb * Rp) * Cb c * Rp * Cb c) +
          ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
            Matrix.trace ((Rm * Eb * Rp) * Cb c * (Rp * Ea * Rm) * Cb c) +
          ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
            Matrix.trace ((Rm * Eb * Rp * Ea * Rm) * Cb c * Rm * Cb c) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    rw [hsplit]
    simp only [hCb]
    rw [DriftAlgebra_cov g, DriftAlgebra_cov g, DriftAlgebra_cov g]
    simp only [e1, e2, e3, e4]
    rfl
  -- the right side
  have hrhs : (W : ℂ) ^ d * ∑ b₁ : Zd d L, ∑ b₂ : Zd d L,
          loopFine d L W M z ![true, false] ![a₁, b₁] * SB d L g b₁ b₂ *
            loopFine d L W M z ![true, false] ![b₂, a₂] +
        (W : ℂ) ^ d * ∑ x : Zd d L, ∑ y : Zd d L,
          ((loopFine d L W M z (fun _ : Fin 1 => true) (fun _ => x) - mSigma E true) *
              SB d L g x y * loopFine d L W M z ![true, true, false] ![y, a₁, a₂] +
            (loopFine d L W M z (fun _ : Fin 1 => false) (fun _ => x) - mSigma E false) *
              SB d L g x y * loopFine d L W M z ![true, false, false] ![a₁, y, a₂]) =
      (W : ℂ) ^ d * ∑ b₁ : Zd d L, ∑ b₂ : Zd d L,
          loopFine d L W M z ![true, false] ![a₁, b₁] * SB d L g b₁ b₂ *
            loopFine d L W M z ![true, false] ![b₂, a₂] +
        (W : ℂ) ^ d * ∑ a' : Zd d L, ∑ b' : Zd d L,
          ((Matrix.trace (Rp * Eblk d L W a') - mE E) * SB d L g a' b' *
              loopFine d L W M z ![true, true, false] ![b', a₁, a₂] +
            (Matrix.trace (Rm * Eblk d L W a') - (starRingEnd ℂ) (mE E)) * SB d L g a' b' *
              loopFine d L W M z ![true, false, false] ![a₁, b', a₂]) := by
    simp only [DriftAlgebra_loopFine_one, mSigma, ite_true, Bool.false_eq_true, ite_false]
    rfl
  rw [hlhs, hrhs]
  exact DriftAlgebra_sum_algebra g hL ((W : ℂ) ^ d) (mE E) ((starRingEnd ℂ) (mE E))
    (fun p => loopFine d L W M z ![true, true, false] ![p, a₁, a₂])
    (fun p => loopFine d L W M z ![true, false, false] ![a₁, p, a₂])
    (fun q => Matrix.trace (Rp * Eblk d L W q)) (fun q => Matrix.trace (Rm * Eblk d L W q))
    (fun x y => loopFine d L W M z ![true, false] ![x, y]) a₁ a₂

/-- **`LoopGenN2`** (pin E.1b). -/
theorem loopGenN2 (d : ℕ) : LoopGenN2 d := by
  intro sz n E hE u hu0 hu1 M hM a₁ a₂
  exact DriftAlgebra_loopGen_core (sz.lam n) (sz.three_le_L n) hE hu1 hM a₁ a₂

/-! ## 5. The `(𝓛 - 𝒦)` hierarchy at `n = 2` -/

section Hier

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix form of `𝓛S𝓛 - 𝒦S𝒦 = STD + DST + DSD` with `𝓛 = D + 𝒦`, `𝒦 = c T`, `wc = 1`,
`TS = ST` (the structure of RBM1D `loopDrift_sub_K_deriv`; `DriftAlgebra:526`). -/
private theorem DriftAlgebra_matrix_identity (S T D : Matrix n n ℂ) (w c : ℂ) (hwc : w * c = 1)
    (hTS : T * S = S * T) :
    w • ((D + c • T) * S * (D + c • T)) - w • ((c • T) * S * (c • T)) =
      S * T * D + D * (S * T) + w • (D * S * D) := by
  have e1 : w • ((D + c • T) * S * (D + c • T)) =
      w • (D * S * D) + (w * c) • (D * S * T) + (w * c) • (T * S * D) +
        (w * c * c) • (T * S * T) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add,
      smul_smul]
    rw [mul_comm c c, ← mul_assoc]
    abel
  have e2 : w • ((c • T) * S * (c • T)) = (w * c * c) • (T * S * T) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [mul_comm c c, ← mul_assoc]
  rw [e1, e2, hwc, one_smul, one_smul, hTS, Matrix.mul_assoc D S T]
  abel

/-- The `(a, b)` entry of `A S B` as a double sum (`DriftAlgebra:94`). -/
private theorem DriftAlgebra_TST_apply {m : Type*} [Fintype m] (A S B : Matrix m m ℂ) (a b : m) :
    (A * S * B) a b = ∑ c : m, ∑ e : m, A a c * S c e * B e b := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

end Hier

/-- **`HierarchyN2`** (pin E.1c). -/
theorem hierarchyN2 (d : ℕ) : HierarchyN2 d := by
  intro sz n E hE u hu0 hu1 M hM a₁ a₂
  have hu : ‖(u : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
    exact hu1
  have hL : 3 ≤ sz.L n := sz.three_le_L n
  rw [loopGenN2 d sz n E hE u hu0 hu1 M hM a₁ a₂,
    (kpmODE d sz n E hE u hu0 hu1 a₁ a₂).deriv]
  set T := Theta d (sz.L n) (sz.lam n) (u : ℂ) with hT
  set S := SB d (sz.L n) (sz.lam n) with hS
  set c : ℂ := ((((sz.W n : ℕ) : ℂ) ^ d))⁻¹ with hc
  set w : ℂ := ((sz.W n : ℕ) : ℂ) ^ d with hw
  have hwc : w * c = 1 := by
    have hW : w ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne (sz.W n)))
    rw [hc]
    exact mul_inv_cancel₀ hW
  set D : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ :=
    Matrix.of fun x y => sz.STLKM n E u M ![true, false] ![x, y] with hD
  have hK : ∀ x y : Zd d (sz.L n),
      sz.STKloop n E u ![true, false] ![x, y] = (c • T) x y := by
    intro x y
    rw [DriftAlgebra_STKloop_eq, Matrix.smul_apply, smul_eq_mul, kTwo,
      DriftAlgebra_mSigma_mul hE, mul_one, mul_one]
  have hL' : ∀ x y : Zd d (sz.L n),
      sz.STLM n E u M ![true, false] ![x, y] = (D + c • T) x y := by
    intro x y
    rw [Matrix.add_apply, ← hK, hD, Matrix.of_apply, Sizes.STLKM, sub_add_cancel]
  have hTS : T * S = S * T := (Theta_commute_SB_of_three_le hL hu).eq
  have hsym : ∀ x y : Zd d (sz.L n), (S * T) x y = (S * T) y x := by
    intro x y
    have h : (S * T)ᵀ = S * T := by
      rw [Matrix.transpose_mul, Theta_transpose_of_three_le hL hu, hS, SB_transpose, ← hS, hTS]
    rw [← h, Matrix.transpose_apply, h]
  have hLL : w * ∑ b₁ : Zd d (sz.L n), ∑ b₂ : Zd d (sz.L n),
        sz.STLM n E u M ![true, false] ![a₁, b₁] * S b₁ b₂ *
          sz.STLM n E u M ![true, false] ![b₂, a₂] =
      w * ((D + c • T) * S * (D + c • T)) a₁ a₂ := by
    rw [DriftAlgebra_TST_apply]
    simp only [hL']
  have hKK : w * ∑ c' : Zd d (sz.L n), ∑ e : Zd d (sz.L n),
        sz.STKloop n E u ![true, false] ![a₁, c'] * S c' e *
          sz.STKloop n E u ![true, false] ![e, a₂] =
      w * ((c • T) * S * (c • T)) a₁ a₂ := by
    rw [DriftAlgebra_TST_apply]
    simp only [hK]
  have hSxy : ∀ x y : Zd d (sz.L n), S x y = S y x := fun x y =>
    congrFun (congrFun (SB_transpose d (sz.L n) (sz.lam n)) y) x
  have hLK : sz.STELKLKM n E u M ![true, false] ![a₁, a₂] = w * (D * S * D) a₁ a₂ := by
    have h : (D * S * D) a₁ a₂ = ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
        sz.STLKM n E u M ![true, false] ![x, a₂] * S x y *
          sz.STLKM n E u M ![true, false] ![a₁, y] := by
      rw [DriftAlgebra_TST_apply, Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      simp only [hD, Matrix.of_apply]
      rw [hSxy y x]
      ring
    rw [h]
    rfl
  have h0 : ∀ b : Zd d (sz.L n), Function.update (![a₁, a₂] : Fin 2 → Zd d (sz.L n)) 0 b = ![b, a₂] := by
    intro b; ext i; fin_cases i <;> simp
  have h1 : ∀ b : Zd d (sz.L n), Function.update (![a₁, a₂] : Fin 2 → Zd d (sz.L n)) 1 b = ![a₁, b] := by
    intro b; ext i; fin_cases i <;> simp
  have hmm : sz.STthetaOp n E u ![true, false] (sz.STLKM n E u M ![true, false]) ![a₁, a₂] =
      (S * T * D) a₁ a₂ + (D * (S * T)) a₁ a₂ := by
    have hm : Sizes.STmsig E true * Sizes.STmsig E false = 1 := DriftAlgebra_mSigma_mul hE
    unfold Sizes.STthetaOp
    rw [Fin.sum_univ_two]
    simp only [h0, h1, Matrix.cons_val_zero, Matrix.cons_val_one, hm, mul_one, one_mul]
    refine congrArg₂ (· + ·) ?_ ?_
    · rw [Matrix.mul_apply]
      rfl
    · rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hsym x a₂]
      exact mul_comm _ _
  have key := congrFun (congrFun (DriftAlgebra_matrix_identity S T D w c hwc hTS) a₁) a₂
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at key
  rw [hLL, hKK, hLK, hmm]
  linear_combination key

/-! ## 6. Compiled nonempty instances at the admissible sequence `sz0`

`RBM.Gauss.SizesInst.sz0` (`RBM3D/Defs/Sizes.lean`): `d = 3`, `L_0 = 4`, `W_0 = 32`,
`lam_0 = 1/64`.  Size index `n = 0`, energy `E = 0` (`|E| < 2`), time `u = 1/2` (`0 ≤ u < 1`),
the Hermitian matrix `M = 1` and the labels `a₁ = 0 ≠ 1 = a₂`.  Every deterministic hypothesis is
discharged; nothing is assumed. -/

section Instances

open RBM.Gauss.SizesInst

/-- The two labels of the instances differ (`0 ≠ 1` in `Z_4^3`). -/
theorem DriftAlgebra_check_labels_sz0 : (0 : Zd 3 (sz0.L 0)) ≠ 1 := fun h => by
  have h0 := congrFun h 0
  revert h0
  decide

/-- **`kpmODE` at `sz0`**: `∂_u 𝒦_{(+,-),(0,1)} = W^d Σ 𝒦 S 𝒦` at `u = 1/2`. -/
theorem DriftAlgebra_check_kpmODE_sz0 :
    HasDerivAt (fun v : ℝ => sz0.STKloop 0 0 v ![true, false] ![(0 : Zd 3 (sz0.L 0)), 1])
      ((((sz0.W 0 : ℕ) : ℂ) ^ 3) * ∑ c : Zd 3 (sz0.L 0), ∑ e : Zd 3 (sz0.L 0),
        sz0.STKloop 0 0 (1 / 2) ![true, false] ![(0 : Zd 3 (sz0.L 0)), c] *
          SB 3 (sz0.L 0) (sz0.lam 0) c e *
          sz0.STKloop 0 0 (1 / 2) ![true, false] ![e, 1]) (1 / 2) :=
  kpmODE 3 sz0 0 0 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 0 1

/-- **`loopGenN2` at `sz0`**: the generator of the `(+,-)` two-loop at `M = 1` is
`LLpair + 𝓔^{(G̃)}`. -/
theorem DriftAlgebra_check_loopGenN2_sz0 :
    genMat 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) 0 (1 / 2)
        (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
        ⟨[true, false], [(0 : Zd 3 (sz0.L 0)), 1]⟩ =
      (((sz0.W 0 : ℕ) : ℂ) ^ 3) * ∑ b₁ : Zd 3 (sz0.L 0), ∑ b₂ : Zd 3 (sz0.L 0),
          sz0.STLM 0 0 (1 / 2) (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
              ![true, false] ![(0 : Zd 3 (sz0.L 0)), b₁] *
            SB 3 (sz0.L 0) (sz0.lam 0) b₁ b₂ *
            sz0.STLM 0 0 (1 / 2) (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
              ![true, false] ![b₂, 1] +
        sz0.STEGtM 0 0 (1 / 2)
          (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
          ![true, false] ![(0 : Zd 3 (sz0.L 0)), 1] :=
  loopGenN2 3 sz0 0 0 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 1
    Matrix.isHermitian_one 0 1

/-- **`hierarchyN2` at `sz0`**: `genMat(𝓛) - ∂_u 𝒦 = Θ∘(𝓛-𝒦) + 𝓔^{LK×LK} + 𝓔^{(G̃)}`. -/
theorem DriftAlgebra_check_hierarchyN2_sz0 :
    genMat 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) 0 (1 / 2)
        (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
        ⟨[true, false], [(0 : Zd 3 (sz0.L 0)), 1]⟩ -
        deriv (fun v : ℝ => sz0.STKloop 0 0 v ![true, false] ![(0 : Zd 3 (sz0.L 0)), 1]) (1 / 2) =
      sz0.STthetaOp 0 0 (1 / 2) ![true, false]
          (sz0.STLKM 0 0 (1 / 2)
            (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) ![true, false])
          ![(0 : Zd 3 (sz0.L 0)), 1] +
        sz0.STELKLKM 0 0 (1 / 2)
          (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
          ![true, false] ![(0 : Zd 3 (sz0.L 0)), 1] +
        sz0.STEGtM 0 0 (1 / 2)
          (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
          ![true, false] ![(0 : Zd 3 (sz0.L 0)), 1] :=
  hierarchyN2 3 sz0 0 0 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 1
    Matrix.isHermitian_one 0 1

/-- The three pins hold as `Prop`s at `d = 3` (not only their instances). -/
example : KpmODE 3 ∧ LoopGenN2 3 ∧ HierarchyN2 3 := ⟨kpmODE 3, loopGenN2 3, hierarchyN2 3⟩

end Instances

end RBM.Path

end
