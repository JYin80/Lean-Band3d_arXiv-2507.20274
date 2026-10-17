/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.GridDuhamelGen
import RBM3D.Induction.StepDecompN

/-!
# The per-step layer over the carrier (BA-T row T5s2a, ticket T2474, targets 1-5)

Additive generic forms of `Induction/LoopC2N.lean`, `Induction/QVN.lean` and
`Induction/StepDecompN.lean` (not edited) over a carrier `Cm : Step2Mat sz`.  The band hypotheses
`|E| < 2`, `zt E`, `etaT E`, `pathP sz`, `pathH sz` become the two classes of target 1:

* `StepDecompGen_LoopForm Cm E`: the loops of the carrier are the loops at `ztOf (Cm.m n) (E n) u`,
  `0 < Im (Cm.m n)`, `Cm.eta n u = etaOf (Cm.m n) u`;
* `StepDecompGen_WalkForm Cm lam' Ψ`: the walk of the carrier is `Ψ n + pathH (sz.withLam lam')`.

Band discharges: `stepDecompGen_loopForm_band` (`m = mE E`), `stepDecompGen_walkForm_band`
(`lam' = sz.lam`, `Ψ = 0`).  Model-free band names (`AbCN`, `stepZCN`, `stepXiCN`, `stepYCN`,
`stepDecompCN`, `dirDerivN`, ...) are used by name at `sz.withLam lam'`.

Private band helpers are reused by `open private` (precedent `Chain/DecayGen.lean`); the QV words of
`Induction/QVN.lean`, which read `greenBlk d L W E u M` / `zt E u`, are copied at a spectral value
`z` under the stem `StepDecompGen_`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open private LoopC2N_contDiffAt_loop LoopC2N_second_deriv_bound LoopC2N_isHermitian_blockMat
  from RBM3D.Induction.LoopC2N

open private QVN_Gres_conjTranspose QVN_Eblk_conjTranspose QVN_hasDerivAt_line QVN_rflip QVN_rflip_eq_zip
  QVN_rot_zip QVN_flip_zip QVN_eeLoop_zip QVN_hasDerivAt_trace QVN_SB_swap QVN_cut_pair QVN_sum_Icc_fin
  QVN_norm_sum_sq_le QVN_mul_conj QVN_coord_sum QVN_svar_sum QVN_trace_blockMat_mul
  from RBM3D.Induction.QVN

open private StepDecompN_gridTime_lt_one StepDecompN_sum_fderiv_eq_stepZCN StepDecompN_sum_delta
  StepDecompN_integrable_phi StepDecompN_stepXiCN_eq_sum_delta_ae StepDecompN_stepYCN_eq_sum_delta_ae
  StepDecompN_hasDerivAt_dir from RBM3D.Induction.StepDecompN

noncomputable section

namespace RBM.BA

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal ENNReal Matrix.Norms.L2Operator
open RBM.Ind (stepZCN stepXiCN stepYCN AbCN)

/-! ### 1. The carrier classes (target 1) -/

/-- **Target 1, `StepDecompGen_LoopForm`**: the loops of the carrier are the loops at the spectral
parameter `ztOf (Cm.m n) (E n) u` (`Loop/GLoopFlow.lean:55`), with `η = etaOf (Cm.m n) u` and
`0 < Im m`.  It replaces `|E| < 2`, `zt E`, `etaT E` of the six band files. -/
def StepDecompGen_LoopForm {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (E : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 0 < (Cm.m n).im ∧
    (∀ (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (k : ℕ)
        (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Cm.LM n u H σ a = loopFine d (sz.L n) (sz.W n) H (ztOf (Cm.m n) (E n) u) σ a) ∧
    (∀ (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
        (I : LoopIdx (Zd d (sz.L n))),
      Cm.LIM n u H I =
        loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) H) (ztOf (Cm.m n) (E n) u) I) ∧
    (∀ u : ℝ, Cm.eta n u = etaOf (Cm.m n) u)

/-- **Target 1, `StepDecompGen_WalkForm`**: the walk of the carrier is the band walk of the model at
the coupling `lam'` shifted by a Hermitian `Ψ n`. -/
def StepDecompGen_WalkForm {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (lam' : ℕ → ℝ)
    (Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : Prop :=
  (∀ n, (Ψ n).IsHermitian) ∧
    Cm.Pp = (show Measure (PathΩ sz) from pathP (sz.withLam lam')) ∧
    ∀ (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz),
      Cm.Hpath s t K n k ω = Ψ n +
        (show Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ from
          pathH (sz.withLam lam') s t K n k ω)

/-! ### 2. The `C²` bound of the loops at a spectral value (target 2) -/

/-- **Target 2, the pin `HermTestFunLoopNOf`**: the pin `HermTestFunLoopN` (`LoopC2N.lean:453`) with `ztOf m E u`,
`etaOf m u` and `0 < m.im` in place of `zt E u`, `etaT E u` and `|E| < 2` (`0 ≤ u` dropped: unused, `LoopC2N:470`). -/
def HermTestFunLoopNOf : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (k n : ℕ) (m : ℂ) (E u : ℝ), 0 < m.im → u < 1 →
    ∀ (σ : Fin k → Bool) (b : Fin k → Zd d (sz.L n)),
      HermTestFun sz n (fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
        loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) (ztOf m E u) (loopOf σ b)) ∧
      ∀ M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian →
        y.IsHermitian →
        ‖fderiv ℝ (fderiv ℝ (fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
            loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) (ztOf m E u)
              (loopOf σ b))) M y y‖ ≤
          ((k * (k + 1) : ℕ) : ℝ) * (Sizes.size sz n : ℝ) * (etaOf m u)⁻¹ ^ (k + 2) * ‖y‖ ^ 2

/-- **Target 2, `hermTestFunLoopNOf`**: the general-length `C²` bound of the loop observables at an arbitrary spectral
value `z = E + (1 - u) m`, `Im m > 0` (route `LoopC2N:469-488`, the privates `LoopC2N_contDiffAt_loop`,
`LoopC2N_second_deriv_bound` being `z`-generic). -/
theorem hermTestFunLoopNOf : HermTestFunLoopNOf := by
  intro d sz k n m E u hm hu1 σ b
  have hη : 0 < etaOf m u := mul_pos (by linarith) hm
  have hz : etaOf m u ≤ |(ztOf m E u).im| := by rw [ztOf_im, abs_of_pos hη]
  have hz0 : (ztOf m E u).im ≠ 0 := by rw [ztOf_im]; exact hη.ne'
  have hwf : (loopOf σ b).WF := by simp [Loop.LoopIdx.WF, loopOf]
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

/-! ### 3. Translation by a Hermitian shift -/

section Shift

variable {d : ℕ} {sz : Sizes d} {n : ℕ}

/-- A test function composed with a Hermitian translation is a test function. -/
theorem StepDecompGen_hermTestFun_shift
    {f : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (hf : HermTestFun sz n f) {Ψ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hΨ : Ψ.IsHermitian) : HermTestFun sz n (fun M => f (Ψ + M)) where
  contDiffAt M hM :=
    (hf.contDiffAt (Ψ + M) (hΨ.add hM)).comp M (contDiffAt_const.add contDiffAt_id)
  bdd₀ := by
    obtain ⟨C, hC⟩ := hf.bdd₀
    exact ⟨C, fun M hM => hC _ (hΨ.add hM)⟩

/-- The second derivative of a translate is the translate of the second derivative. -/
theorem StepDecompGen_fderiv2_shift
    (f : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ)
    (Ψ M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    fderiv ℝ (fderiv ℝ (fun M' => f (Ψ + M'))) M y y = fderiv ℝ (fderiv ℝ f) (Ψ + M) y y := by
  have h1 : fderiv ℝ (fun M' => f (Ψ + M')) = fun M' => fderiv ℝ f (Ψ + M') :=
    funext fun M' => fderiv_comp_add_left Ψ
  rw [h1, fderiv_comp_add_left Ψ]

end Shift

/-! ### 4. The quadratic variation over the carrier (target 3)

The z-free coordinate algebra, the reversal of chains and the cut-pair identity of `Induction/QVN.lean` are reused by
`open private` (see the header of this file); the words, Leibniz rule and cut decomposition, which read
`greenBlk d L W E u M = Gres (blockMat M) (zt E u)`, are copied at a spectral value `z` under the stem
`StepDecompGen_` (`QVN:378-424`, `:500-650`, `:677-695`, `:716-797`). -/

section QV

variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W]

/-- The derivative of `𝓛_{z,σ,b}(M)` along a direction `X` at a spectral value `z`: `loopDerivN` (`QVN:62`) with
`zt E u` replaced by `z`. -/
def StepDecompGen_loopDerivZ (d L W : ℕ) [NeZero L] [NeZero W] (z : ℂ)
    (M X : Matrix (Idx d L W) (Idx d L W) ℂ) {k : ℕ} (σ : Fin k → Bool) (b : Fin k → Zd d L) : ℂ :=
  deriv (fun y : ℝ => loopL d L W (blockMat d L W (M + (y : ℂ) • X)) z (loopOf σ b)) 0

/-- `(𝓔⊗𝓔)_{z,σ,a,a'}` of a fine matrix at a spectral value `z` (`QVN_eeN`, `QVN:68`, with `zt E u` replaced by `z`). -/
def StepDecompGen_eeN (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) (z : ℂ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) {m : ℕ} (σ : Fin m → Bool)
    (a a' : Fin m → Zd d L) : ℂ :=
  (W : ℂ) ^ d * ∑ k ∈ Finset.Icc 1 m, ∑ b : Zd d L, ∑ b' : Zd d L,
    SB d L g b b' *
      loopL d L W (blockMat d L W M) z (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b')

/-- The word `∏_{p ∈ l} G_{p.1} E_{p.2}` of a list of `(sign, label)` pairs at `(E, u, M)`. -/
private def StepDecompGen_wd (z : ℂ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (l : List (Bool × Zd d L)) :
    Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  l.foldr (fun p Z => Gres (blockMat d L W M) z p.1 * Eblk d L W p.2 * Z) 1

private theorem StepDecompGen_wd_nil (z : ℂ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) :
    StepDecompGen_wd z M ([] : List (Bool × Zd d L)) =
      (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) := rfl

private theorem StepDecompGen_wd_cons (z : ℂ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (p : Bool × Zd d L)
    (l : List (Bool × Zd d L)) :
    StepDecompGen_wd z M (p :: l) = Gres (blockMat d L W M) z p.1 * Eblk d L W p.2 * StepDecompGen_wd z M l := rfl

private theorem StepDecompGen_wd_append (z : ℂ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (l₁ l₂ : List (Bool × Zd d L)) :
    StepDecompGen_wd z M (l₁ ++ l₂) = StepDecompGen_wd z M l₁ * StepDecompGen_wd z M l₂ := by
  induction l₁ with
  | nil => simp [StepDecompGen_wd_nil]
  | cons p l ih => simp [StepDecompGen_wd_cons, ih, Matrix.mul_assoc]

private theorem StepDecompGen_green_conjTranspose (z : ℂ) {M : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hM : M.IsHermitian) (σ : Bool) :
    (Gres (blockMat d L W M) z σ)ᴴ = Gres (blockMat d L W M) z (!σ) :=
  QVN_Gres_conjTranspose (hM.submatrix _) _ σ

/-- **The conjugate-transposed chain is a chain again** (RBM1D
`Gsig_mul_conjTranspose_prodList_mul`, `RBM1D/Hierarchy/EEBridge.lean:195`, commit `c06b103`):
`G(t) · (∏ G E)ᴴ · E_c` is the word of `QVN_rflip t l c`, for Hermitian `M`. -/
private theorem StepDecompGen_wd_rflip (z : ℂ) {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian)
    (t : Bool) (l : List (Bool × Zd d L)) (c : Zd d L) :
    Gres (blockMat d L W M) z t * (StepDecompGen_wd z M l)ᴴ * Eblk d L W c = StepDecompGen_wd z M (QVN_rflip t l c) := by
  induction l generalizing c with
  | nil => simp [QVN_rflip, StepDecompGen_wd_nil, StepDecompGen_wd_cons]
  | cons p l ih =>
    rw [QVN_rflip, StepDecompGen_wd_append, ← ih p.2, StepDecompGen_wd_cons, StepDecompGen_wd_cons,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, QVN_Eblk_conjTranspose,
      StepDecompGen_green_conjTranspose z hM]
    simp [Matrix.mul_assoc, StepDecompGen_wd_nil]

/-- `∂_y G^σ(M + yX)|_{y=0} = -G^σ X̂ G^σ` (the resolvent derivative, as in the proof of
`QVIdentity_loopDeriv_eq` of `Path/QVIdentity.lean`, for either sign). -/
private theorem StepDecompGen_hasDerivAt_green {z : ℂ} (hz : z.im ≠ 0)
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian)
    (X : Matrix (Idx d L W) (Idx d L W) ℂ) (σ : Bool) :
    HasDerivAt (fun y : ℝ => Gres (blockMat d L W (M + (y : ℂ) • X)) z σ)
      (-(Gres (blockMat d L W M) z σ * blockMat d L W X * Gres (blockMat d L W M) z σ)) 0 := by
  have hH : (blockMat d L W M).IsHermitian := hM.submatrix _
  set Hy : ℝ → Matrix (Vtx d L W) (Vtx d L W) ℂ :=
    fun y => blockMat d L W M + (y : ℂ) • blockMat d L W X with hHy
  have hH0 : Hy 0 = blockMat d L W M := by simp [hHy]
  have hline : HasDerivAt Hy (blockMat d L W X) 0 := QVN_hasDerivAt_line _ _ 0
  have hfun : (fun y : ℝ => Gres (blockMat d L W (M + (y : ℂ) • X)) z σ) =
      fun y => Gres (Hy y) z σ := by
    funext y
    simp only [hHy]
    rfl
  rw [hfun]
  cases σ with
  | true =>
      have h := hasDerivAt_green_moving hline (hasDerivAt_const (0 : ℝ) z)
        (by rw [hH0]; exact hH) hz
      simpa [hH0] using h
  | false =>
      have hz' : ((starRingEnd ℂ) z).im ≠ 0 := by simpa using hz
      have h := hasDerivAt_green_moving hline
        (hasDerivAt_const (0 : ℝ) ((starRingEnd ℂ) z)) (by rw [hH0]; exact hH) hz'
      simpa [hH0, Gres] using h

/-- Differentiate the first factor of the word `m`: `head (p :: m') = (-(G X̂ G) E_p) · wd m'`. -/
private def StepDecompGen_head (z : ℂ) (M X : Matrix (Idx d L W) (Idx d L W) ℂ) :
    List (Bool × Zd d L) → Matrix (Vtx d L W) (Vtx d L W) ℂ
  | [] => 0
  | p :: m => (-(Gres (blockMat d L W M) z p.1 * blockMat d L W X * Gres (blockMat d L W M) z p.1) *
      Eblk d L W p.2) * StepDecompGen_wd z M m

/-- The Leibniz sum of a word: differentiate the `q`-th factor, `q < |l|`. -/
private def StepDecompGen_wordDeriv (z : ℂ) (M X : Matrix (Idx d L W) (Idx d L W) ℂ)
    (l : List (Bool × Zd d L)) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  ∑ q ∈ Finset.range l.length, StepDecompGen_wd z M (l.take q) * StepDecompGen_head z M X (l.drop q)

private theorem StepDecompGen_wordDeriv_cons (z : ℂ) (M X : Matrix (Idx d L W) (Idx d L W) ℂ)
    (p : Bool × Zd d L) (l : List (Bool × Zd d L)) :
    StepDecompGen_wordDeriv z M X (p :: l) = StepDecompGen_head z M X (p :: l) +
      Gres (blockMat d L W M) z p.1 * Eblk d L W p.2 * StepDecompGen_wordDeriv z M X l := by
  unfold StepDecompGen_wordDeriv
  rw [List.length_cons, Finset.sum_range_succ']
  simp only [List.take_succ_cons, List.drop_succ_cons, StepDecompGen_wd_cons, List.take_zero,
    List.drop_zero, StepDecompGen_wd_nil, Matrix.one_mul, Finset.mul_sum, Matrix.mul_assoc]
  rw [add_comm]

/-- **Leibniz rule for a word** in the direction `X`. -/
private theorem StepDecompGen_hasDerivAt_wd {z : ℂ} (hz : z.im ≠ 0)
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) (X : Matrix (Idx d L W) (Idx d L W) ℂ)
    (l : List (Bool × Zd d L)) :
    HasDerivAt (fun y : ℝ => StepDecompGen_wd z (M + (y : ℂ) • X) l) (StepDecompGen_wordDeriv z M X l) 0 := by
  induction l with
  | nil =>
      have h0 : StepDecompGen_wordDeriv z M X ([] : List (Bool × Zd d L)) = 0 := by
        simp [StepDecompGen_wordDeriv]
      rw [h0]
      simpa only [StepDecompGen_wd_nil] using
        hasDerivAt_const (0 : ℝ) (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)
  | cons p l ih =>
      have hhead := (StepDecompGen_hasDerivAt_green hz hM X p.1).mul_const (Eblk d L W p.2)
      have h := hhead.mul ih
      rw [StepDecompGen_wordDeriv_cons]
      have hfun : (fun y : ℝ => StepDecompGen_wd z (M + (y : ℂ) • X) (p :: l)) =
          fun y : ℝ => Gres (blockMat d L W (M + (y : ℂ) • X)) z p.1 * Eblk d L W p.2 *
            StepDecompGen_wd z (M + (y : ℂ) • X) l := rfl
      rw [hfun]
      convert h using 1
      simp [StepDecompGen_head]

/-- The `q`-th Leibniz term as a pairing against the cut chain:
`tr(wd(l[:q]) · ∂_q) = -tr(X̂ · wd(l[q:] ++ l[:q]) · G^{l_q})` (cyclicity of the trace). -/
private theorem StepDecompGen_trace_term (z : ℂ) (M X : Matrix (Idx d L W) (Idx d L W) ℂ)
    (l : List (Bool × Zd d L)) {q : ℕ} (hq : q < l.length) :
    Matrix.trace (StepDecompGen_wd z M (l.take q) * StepDecompGen_head z M X (l.drop q)) =
      -Matrix.trace (blockMat d L W X * (StepDecompGen_wd z M (l.drop q ++ l.take q) *
        Gres (blockMat d L W M) z l[q].1)) := by
  rw [List.drop_eq_getElem_cons hq, StepDecompGen_head, StepDecompGen_wd_append, StepDecompGen_wd_cons]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.trace_neg]
  congr 1
  rw [show StepDecompGen_wd z M (l.take q) * (Gres (blockMat d L W M) z l[q].1 * blockMat d L W X *
        Gres (blockMat d L W M) z l[q].1 * Eblk d L W l[q].2 * StepDecompGen_wd z M (l.drop (q + 1))) =
      (StepDecompGen_wd z M (l.take q) * Gres (blockMat d L W M) z l[q].1) *
        (blockMat d L W X * (Gres (blockMat d L W M) z l[q].1 * Eblk d L W l[q].2 *
          StepDecompGen_wd z M (l.drop (q + 1)))) by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- The cut chain of edge `j`: `A_j(b) = wd(rot_j(σ, b)) · G^{σ_j}`, where `rot_j` starts the
chain at the `j`-th factor. -/
private def StepDecompGen_cut (z : ℂ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) {k : ℕ} (σ : Fin k → Bool)
    (b : Fin k → Zd d L) (j : Fin k) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  StepDecompGen_wd z M (((List.ofFn σ).zip (List.ofFn b)).drop j ++
      ((List.ofFn σ).zip (List.ofFn b)).take j) * Gres (blockMat d L W M) z (σ j)

/-- **Leibniz decomposition of the loop derivative** (RBM1D `gradMat_loopObs`,
`RBM1D/Gauss/EETensorBound.lean:267`, commit `c06b103`, read through `loopCut_eq` of
`Hierarchy/EEBridge.lean:256`): `∂_X 𝓛_{σ,b} = -Σ_j tr(X̂ · A_j(b))`. -/
private theorem StepDecompGen_loopDerivN_eq {z : ℂ} (hz : z.im ≠ 0)
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) (X : Matrix (Idx d L W) (Idx d L W) ℂ)
    {k : ℕ} (σ : Fin k → Bool) (b : Fin k → Zd d L) :
    StepDecompGen_loopDerivZ d L W z M X σ b =
      ∑ j : Fin k, -Matrix.trace (blockMat d L W X * StepDecompGen_cut z M σ b j) := by
  set l : List (Bool × Zd d L) := (List.ofFn σ).zip (List.ofFn b) with hl
  have hlen : l.length = k := by simp [hl]
  have hfun : (fun y : ℝ => loopL d L W (blockMat d L W (M + (y : ℂ) • X)) z
      (loopOf σ b)) = fun y : ℝ => Matrix.trace (StepDecompGen_wd z (M + (y : ℂ) • X) l) := rfl
  have hD := QVN_hasDerivAt_trace (StepDecompGen_hasDerivAt_wd hz hM X l)
  rw [StepDecompGen_loopDerivZ, hfun, hD.deriv, StepDecompGen_wordDeriv, Matrix.trace_sum, hlen, Finset.sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [StepDecompGen_trace_term z M X l (by omega : (j : ℕ) < l.length)]
  simp [StepDecompGen_cut, hl]

/-- **The glued `(2k+2)`-loop of the cut `j` is `tr(A_j(a) E_{β'} A_j(a')ᴴ E_β)`** (RBM1D
`glueLoop_prodList`, `RBM1D/Hierarchy/EEBridge.lean:208`, commit `c06b103`; the layout is
`eeLoop` of `Induction/HierVocab.lean`). -/
private theorem StepDecompGen_eeLoop_gloop (z : ℂ) {M : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hM : M.IsHermitian) {k : ℕ} (σ : Fin k → Bool) (a a' : Fin k → Zd d L) (j : Fin k)
    (β β' : Zd d L) :
    loopL d L W (blockMat d L W M) z (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') ((j : ℕ) + 1) β β') =
      Matrix.trace (StepDecompGen_cut z M σ a j * Eblk d L W β' * (StepDecompGen_cut z M σ a' j)ᴴ *
        Eblk d L W β) := by
  have hq : (j : ℕ) < (List.ofFn σ).length := by simp
  have hz := QVN_eeLoop_zip (L := L) (List.ofFn σ) (List.ofFn a) (List.ofFn a') (by simp)
    (by simp) hq β β'
  have hs : (List.ofFn σ)[(j : ℕ)] = σ j := by simp
  rw [hs] at hz
  have hL : loopL d L W (blockMat d L W M) z (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') ((j : ℕ) + 1) β β') =
      Matrix.trace (StepDecompGen_wd z M ((STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a')
        ((j : ℕ) + 1) β β').σ.zip (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a')
        ((j : ℕ) + 1) β β').a)) := rfl
  rw [hL, hz, StepDecompGen_wd_append, StepDecompGen_wd_append, ← StepDecompGen_wd_rflip z hM]
  simp only [StepDecompGen_cut, Matrix.conjTranspose_mul, StepDecompGen_green_conjTranspose z hM,
    StepDecompGen_wd_cons, StepDecompGen_wd_nil, Matrix.mul_one, Matrix.mul_assoc]

/-- The `j`-th cut of `𝓔⊗𝓔`: `W² Σ_{x,y} S^B_{xy} tr(A_j(b) E_x A_j(b')ᴴ E_y)`. -/
private def StepDecompGen_Ecut (g : ℝ) (z : ℂ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) {k : ℕ} (σ : Fin k → Bool)
    (j : Fin k) (b b' : Fin k → Zd d L) : ℂ :=
  (W : ℂ) ^ d * ∑ x : Zd d L, ∑ y : Zd d L, SB d L g x y *
    Matrix.trace (StepDecompGen_cut z M σ b j * Eblk d L W x * (StepDecompGen_cut z M σ b' j)ᴴ * Eblk d L W y)

/-- **`𝓔⊗𝓔` is the sum of its `k` cuts.** -/
private theorem StepDecompGen_eeN_eq (z : ℂ) {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian)
    {k : ℕ} (σ : Fin k → Bool) (b b' : Fin k → Zd d L) :
    StepDecompGen_eeN d L W g z M σ b b' = ∑ j : Fin k, StepDecompGen_Ecut g z M σ j b b' := by
  rw [StepDecompGen_eeN, QVN_sum_Icc_fin, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [StepDecompGen_Ecut]
  congr 1
  simp only [StepDecompGen_eeLoop_gloop z hM]
  exact QVN_SB_swap (fun x y => Matrix.trace (StepDecompGen_cut z M σ b j * Eblk d L W x *
    (StepDecompGen_cut z M σ b' j)ᴴ * Eblk d L W y))

/-- The variance proxy at general `(d, L, W, g)`: Cauchy–Schwarz over the `k` cuts, the per-cut
identity `QVN_cut_pair` and the glued loop `StepDecompGen_eeLoop_gloop`. -/
private theorem StepDecompGen_core (z : ℂ) (hz : z.im ≠ 0)
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) {k : ℕ}
    (σ : Fin k → Bool) (κ : (Fin k → Zd d L) → ℂ) :
    ∑ c : CoordF d L W, (gvarF d L W g c : ℝ) *
        ‖∑ b : Fin k → Zd d L, κ b * StepDecompGen_loopDerivZ d L W z M (coordinateMatrix d L W c) σ b‖ ^ 2 ≤
      (k : ℝ) * (∑ b : Fin k → Zd d L, ∑ b' : Fin k → Zd d L,
        κ b * (starRingEnd ℂ) (κ b') * StepDecompGen_eeN d L W g z M σ b b').re := by
  -- the `j`-th cut of the propagated increment
  set P : Fin k → CoordF d L W → ℂ := fun j c =>
    ∑ b : Fin k → Zd d L, κ b *
      (-Matrix.trace (blockMat d L W (coordinateMatrix d L W c) * StepDecompGen_cut z M σ b j)) with hP
  have hsplit : ∀ c : CoordF d L W,
      ∑ b : Fin k → Zd d L, κ b * StepDecompGen_loopDerivZ d L W z M (coordinateMatrix d L W c) σ b =
        ∑ j : Fin k, P j c := by
    intro c
    simp only [hP, StepDecompGen_loopDerivN_eq hz hM, Finset.mul_sum]
    exact Finset.sum_comm
  -- the per-cut variance identity
  have hcut : ∀ j : Fin k, ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
        (P j c * (starRingEnd ℂ) (P j c)) =
      ∑ b : Fin k → Zd d L, ∑ b' : Fin k → Zd d L,
        κ b * (starRingEnd ℂ) (κ b') * StepDecompGen_Ecut g z M σ j b b' := by
    intro j
    have hPP : ∀ c : CoordF d L W, P j c * (starRingEnd ℂ) (P j c) =
        ∑ b : Fin k → Zd d L, ∑ b' : Fin k → Zd d L, κ b * (starRingEnd ℂ) (κ b') *
          (-Matrix.trace (blockMat d L W (coordinateMatrix d L W c) * StepDecompGen_cut z M σ b j) *
            (starRingEnd ℂ) (-Matrix.trace (blockMat d L W (coordinateMatrix d L W c) *
              StepDecompGen_cut z M σ b' j))) := by
      intro c
      simp only [hP, map_sum, map_mul, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
      ring
    simp only [hPP, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [StepDecompGen_Ecut, ← QVN_cut_pair (StepDecompGen_cut z M σ b j) (StepDecompGen_cut z M σ b' j), Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have hre : ∀ j : Fin k, ∑ c : CoordF d L W, (gvarF d L W g c : ℝ) * ‖P j c‖ ^ 2 =
      (∑ b : Fin k → Zd d L, ∑ b' : Fin k → Zd d L,
        κ b * (starRingEnd ℂ) (κ b') * StepDecompGen_Ecut g z M σ j b b').re := by
    intro j
    rw [← hcut j, Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [QVN_mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re]
  simp only [hsplit]
  calc ∑ c : CoordF d L W, (gvarF d L W g c : ℝ) * ‖∑ j : Fin k, P j c‖ ^ 2
      ≤ ∑ c : CoordF d L W, (gvarF d L W g c : ℝ) * ((k : ℝ) * ∑ j : Fin k, ‖P j c‖ ^ 2) := by
        refine Finset.sum_le_sum fun c _ => ?_
        exact mul_le_mul_of_nonneg_left (QVN_norm_sum_sq_le _) (gvarF d L W g c).2
    _ = (k : ℝ) * ∑ j : Fin k, ∑ c : CoordF d L W, (gvarF d L W g c : ℝ) * ‖P j c‖ ^ 2 := by
        have h1 : ∀ c : CoordF d L W, (gvarF d L W g c : ℝ) * ((k : ℝ) * ∑ j : Fin k, ‖P j c‖ ^ 2) =
            (k : ℝ) * ∑ j : Fin k, (gvarF d L W g c : ℝ) * ‖P j c‖ ^ 2 := by
          intro c
          rw [← Finset.mul_sum]
          ring
        rw [Finset.sum_congr rfl fun c _ => h1 c, ← Finset.mul_sum, Finset.sum_comm]
    _ = (k : ℝ) * ∑ j : Fin k, (∑ b : Fin k → Zd d L, ∑ b' : Fin k → Zd d L,
          κ b * (starRingEnd ℂ) (κ b') * StepDecompGen_Ecut g z M σ j b b').re := by
        simp only [hre]
    _ = (k : ℝ) * (∑ b : Fin k → Zd d L, ∑ b' : Fin k → Zd d L,
          κ b * (starRingEnd ℂ) (κ b') * StepDecompGen_eeN d L W g z M σ b b').re := by
        congr 1
        rw [← Complex.re_sum]
        congr 1
        simp only [StepDecompGen_eeN_eq z hM, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]

end QV

/-! ### 5. Band discharges of the classes (target 1) -/

section BandClasses

variable {d : ℕ}

/-- **Band discharge of `StepDecompGen_LoopForm`**: at `m = mE E` every field is definitional (`zt_eq_ztOf`,
`etaT_eq_etaOf`), `0 < Im mE` is `mE_im_pos`. -/
theorem stepDecompGen_loopForm_band (sz : Sizes d) (E : ℕ → ℝ) (hE : ∀ n, |E n| < 2) :
    StepDecompGen_LoopForm (bandStep2Mat sz E) E :=
  fun n => ⟨mE_im_pos (hE n), fun _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩

/-- **Band discharge of `StepDecompGen_WalkForm`**: `lam' = sz.lam`, `Ψ = 0`; `sz.withLam sz.lam = sz` is structure
eta (precedent `Chain/CltGen.lean:177`). -/
theorem stepDecompGen_walkForm_band (sz : Sizes d) (E : ℕ → ℝ) :
    StepDecompGen_WalkForm (bandStep2Mat sz E) sz.lam (fun _ => 0) :=
  ⟨fun _ => Matrix.isHermitian_zero, rfl, fun s t K n k ω => (zero_add _).symm⟩

end BandClasses

/-! ### 6. The variance proxy over the carrier (target 3) -/

section QVTarget

variable {d : ℕ} {sz : Sizes d}

/-- **Target 3, `QVPropagatedNg`**: the pin `QVPropagatedN` (`QVN.lean:799`) over the carrier: the loop derivative is
`dirDerivN` of `Cm.LM`, the proxy is `STeeMg`, the coordinate variance is `gvarF` at the walk coupling `g n`. -/
def QVPropagatedNg (Cm : Step2Mat sz) (g : ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (u : ℝ), 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian →
      ∀ (k : ℕ), 2 ≤ k → ∀ (σ : Fin k → Bool) (κ : (Fin k → Zd d (sz.L n)) → ℂ),
        ∑ c : CoordF d (sz.L n) (sz.W n), (gvarF d (sz.L n) (sz.W n) (g n) c : ℝ) *
            ‖∑ b : Fin k → Zd d (sz.L n), κ b *
              RBM.Ind.dirDerivN (fun H => Cm.LM n u H σ b) M (coordinateMatrix d (sz.L n) (sz.W n) c)‖ ^ 2 ≤
          (k : ℝ) * (∑ b : Fin k → Zd d (sz.L n), ∑ b' : Fin k → Zd d (sz.L n),
            κ b * (starRingEnd ℂ) (κ b') * STeeMg Cm n u M σ b b').re

/-- Under `LoopForm`, `dirDerivN` of the carrier loop is the loop derivative at the spectral value. -/
theorem StepDecompGen_dirDerivN_LM {Cm : Step2Mat sz} {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E) (n : ℕ)
    (u : ℝ) (M X : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {k : ℕ} (σ : Fin k → Bool)
    (b : Fin k → Zd d (sz.L n)) :
    RBM.Ind.dirDerivN (fun H => Cm.LM n u H σ b) M X =
      StepDecompGen_loopDerivZ d (sz.L n) (sz.W n) (ztOf (Cm.m n) (E n) u) M X σ b := by
  unfold RBM.Ind.dirDerivN StepDecompGen_loopDerivZ
  congr 1
  funext y
  change Cm.LM n u (M + (y : ℂ) • X) σ b = _
  rw [(hL n).2.1 u _ k σ b]
  unfold loopFine
  rw [loopM_eq_loopL]

/-- **Target 3, `qvPropagatedNg`**: the variance proxy of a propagated increment over the carrier, under `LoopForm`
and the walk's variance law `Cm.S n = SB d (sz.L n) (g n)` (`QVN_core` at `z = ztOf (Cm.m n) (E n) u`). -/
theorem qvPropagatedNg (Cm : Step2Mat sz) (E g : ℕ → ℝ) (hL : StepDecompGen_LoopForm Cm E)
    (hS : ∀ n, Cm.S n = SB d (sz.L n) (g n)) : QVPropagatedNg Cm g := by
  intro n u _ hu M hM k _ σ κ
  have hz : (ztOf (Cm.m n) (E n) u).im ≠ 0 := by
    rw [ztOf_im]; exact (mul_pos (by linarith) (hL n).1).ne'
  have hee : ∀ b b' : Fin k → Zd d (sz.L n), STeeMg Cm n u M σ b b' =
      StepDecompGen_eeN d (sz.L n) (sz.W n) (g n) (ztOf (Cm.m n) (E n) u) M σ b b' := by
    intro b b'
    simp only [STeeMg, STLIMg, StepDecompGen_eeN, (hL n).2.2.1, hS n]
  simp only [StepDecompGen_dirDerivN_LM hL, hee]
  exact StepDecompGen_core (g := g n) _ hz hM σ κ

end QVTarget

/-! ### 7. The vocabulary over `Step2Mat` (target 4) -/

section Vocab

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz)

/-- **`loopFamNg`**: the loop family `b ↦ (M ↦ Cm.LM n u_{j+1} M σ b)` at the spectral time of the step `j → j+1`
(`loopFamN`, `StepDecompN:150`). -/
def loopFamNg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool) :
    (Fin k → Zd d (sz.L n)) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ :=
  fun a M => Cm.LM n (gridTime s t K n (j + 1)) M σ a

/-- **`ZfamNg`**: the first-chaos part of a family `Φ` on the grid step `j → j+1`: the directional derivative of
`Φ_b` at `H_j` along `H_{j+1} - H_j` (`ZfamN`, `StepDecompN:176`, where the direction is `√Δ X_{j+1}`). -/
def ZfamNg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*}
    (Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ) (ω : PathΩ sz) : ι → ℂ :=
  fun b => RBM.Ind.dirDerivN (Φ b) (Cm.Hpath s t K n j ω) (Cm.Hpath s t K n (j + 1) ω - Cm.Hpath s t K n j ω)

/-- **`ZvecNg`**: the first-chaos part of `martIncNg` (`ZvecN`, `StepDecompN:185`). -/
def ZvecNg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool) (ω : PathΩ sz) :
    (Fin k → Zd d (sz.L n)) → ℂ :=
  fun b => RBM.Ind.dirDerivN (loopFamNg Cm s t K n j σ b) (Cm.Hpath s t K n j ω)
    (Cm.Hpath s t K n (j + 1) ω - Cm.Hpath s t K n j ω)

/-- **`YvecNg`**: the quadratic remainder `martIncNg - ZvecNg` (`YvecN`, `StepDecompN:192`). -/
def YvecNg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool) (ω : PathΩ sz) :
    (Fin k → Zd d (sz.L n)) → ℂ :=
  fun b => martIncNg Cm s t K n j σ ω b - ZvecNg Cm s t K n j σ ω b

/-- **`stoppedEdgeNg`**: the stopped, propagated increment `1_{j<τ} (𝒰_{u_{j+1},t'} Y_j)_b`, the kernel being
`Step2Gen_UN` (`stoppedEdgeN`, `StepDecompN:198`). -/
def stoppedEdgeNg {n k : ℕ} (σ : Fin k → Bool) (u : ℕ → ℝ) (t' : ℝ)
    (τ : PathΩ sz → ℕ) (Y : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ)
    (b : Fin k → Zd d (sz.L n)) (j : ℕ) (ω : PathΩ sz) : ℂ :=
  {ω' | j < τ ω'}.indicator
    (fun ω' => Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) t' (Y j ω') b) ω

/-- **Target 4, `SubGaussFormNg`**: `SubGaussFormN` (`StepDecompN.lean:206`) with `Cm.Pp` for `pathP sz`. -/
def SubGaussFormNg [IsProbabilityMeasure Cm.Pp] (j : ℕ) (τ : PathΩ sz → ℕ) (F : PathΩ sz → ℂ) (c : ℝ≥0) :
    Prop :=
  HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
    (fun ω => ({ω' | j < τ ω'}.indicator F ω).re) c Cm.Pp ∧
  HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
    (fun ω => ({ω' | j < τ ω'}.indicator F ω).im) c Cm.Pp

/-- **Target 4, `SubGaussStopNg`**: `SubGaussStopN` (`StepDecompN.lean:215`) with `Step2Gen_UN` for `Ugen` (U-C4). -/
def SubGaussStopNg [IsProbabilityMeasure Cm.Pp] {n k : ℕ}
    (σ : Fin k → Bool) (u : ℕ → ℝ) (τ : PathΩ sz → ℕ) (Z : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ) (m : ℕ)
    (a : Fin k → Zd d (sz.L n)) (j : ℕ) (c : ℝ≥0) : Prop :=
  SubGaussFormNg Cm j τ (fun ω' => Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m) (Z j ω') a) c

end Vocab

/-! ### 8. Band bridges of the vocabulary (target 4) -/

section VocabBridge

variable {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ)

/-- The band carrier's law is a probability measure (the instance for `SubGaussFormNg`, `SubGaussStopNg`). -/
instance bandStep2Mat_isProbabilityMeasure_Pp : IsProbabilityMeasure (bandStep2Mat sz E).Pp :=
  isProbabilityMeasure_pathP sz

/-- Scaling of the directional derivative by a real factor (no differentiability needed). -/
theorem StepDecompGen_dirDerivN_smul {d L W : ℕ} [NeZero L] [NeZero W]
    (Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ) (M X : Matrix (Idx d L W) (Idx d L W) ℂ) (c : ℝ) :
    RBM.Ind.dirDerivN Φ M ((c : ℂ) • X) = (c : ℂ) * RBM.Ind.dirDerivN Φ M X := by
  unfold RBM.Ind.dirDerivN
  have h : (fun y : ℝ => Φ (M + (y : ℂ) • ((c : ℂ) • X))) =
      (fun y' : ℝ => Φ (M + (y' : ℂ) • X)) ∘ (fun y : ℝ => c * y) := by
    funext y
    simp only [Function.comp_apply, smul_smul, Complex.ofReal_mul]
    rw [mul_comm]
  rw [h]
  have h2 := deriv_comp_mul_left (c := c) (f := fun y' : ℝ => Φ (M + (y' : ℂ) • X)) (x := 0)
  rw [Function.comp_def]
  rw [h2, mul_zero, Complex.real_smul]

/-- The increment of the band walk: `H_{j+1} - H_j = √Δ X_{j+1}` (`pathH_succ`). -/
theorem StepDecompGen_band_incr (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (ω : PathΩ sz) :
    (bandStep2Mat sz E).Hpath s t K n (j + 1) ω - (bandStep2Mat sz E).Hpath s t K n j ω =
      (Real.sqrt (gridStep s t K n) : ℂ) • Sizes.seqXmat sz n (ω (j + 1)) := by
  change pathH sz s t K n (j + 1) ω - pathH sz s t K n j ω = _
  rw [pathH_succ]; abel

/-- `loopFamN` is `loopFamNg` at `bandStep2Mat` (`loopM_eq_loopL`). -/
theorem bandStep2_loopFamN (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool) :
    RBM.Ind.loopFamN sz E s t K n j σ = loopFamNg (bandStep2Mat sz E) s t K n j σ := by
  funext a M
  exact (loopM_eq_loopL _ _ _ _ _ σ a).symm

/-- `ZvecN` is `ZvecNg` at `bandStep2Mat` (`pathH_succ` and scaling of `deriv`). -/
theorem bandStep2_ZvecN (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool) (ω : PathΩ sz) :
    RBM.Ind.ZvecN sz E s t K n j σ ω = ZvecNg (bandStep2Mat sz E) s t K n j σ ω := by
  funext b
  unfold RBM.Ind.ZvecN ZvecNg RBM.Ind.loopDerivN
  rw [StepDecompGen_band_incr, StepDecompGen_dirDerivN_smul, ← bandStep2_loopFamN]
  rfl

/-- `YvecN` is `YvecNg` at `bandStep2Mat`. -/
theorem bandStep2_YvecN (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool) (ω : PathΩ sz) :
    RBM.Ind.YvecN sz E s t K n j σ ω = YvecNg (bandStep2Mat sz E) s t K n j σ ω := by
  funext b
  unfold RBM.Ind.YvecN YvecNg
  rw [bandStep2_ZvecN]
  rfl

/-- `stoppedEdgeN` is `stoppedEdgeNg` at `bandStep2Mat` (`bandStep2_Ugen`). -/
theorem bandStep2_stoppedEdgeN {n k : ℕ} (σ : Fin k → Bool) (u : ℕ → ℝ) (t' : ℝ) (τ : PathΩ sz → ℕ)
    (Y : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ) (b : Fin k → Zd d (sz.L n)) (j : ℕ) (ω : PathΩ sz) :
    RBM.Ind.stoppedEdgeN sz (E n) σ u t' τ Y b j ω = stoppedEdgeNg (bandStep2Mat sz E) σ u t' τ Y b j ω := by
  unfold RBM.Ind.stoppedEdgeN stoppedEdgeNg
  simp only [bandStep2_Ugen]
  rfl

/-- `SubGaussStopN` is `SubGaussStopNg` at `bandStep2Mat` (`bandStep2_Ugen`). -/
theorem bandStep2_SubGaussStopN {n k : ℕ} (σ : Fin k → Bool) (u : ℕ → ℝ) (τ : PathΩ sz → ℕ)
    (Z : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ) (m : ℕ) (a : Fin k → Zd d (sz.L n)) (j : ℕ) (c : ℝ≥0) :
    RBM.Ind.SubGaussStopN sz (E n) σ u τ Z m a j c ↔ SubGaussStopNg (bandStep2Mat sz E) σ u τ Z m a j c := by
  unfold RBM.Ind.SubGaussStopN SubGaussStopNg
  simp only [bandStep2_Ugen]
  exact Iff.rfl

end VocabBridge

/-! ### 9. The shifted loop family and the identifications (targets 2 and 5) -/

section Ident

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz)

/-- **The loop family seen from the shifted walk**: `Φ_b(M) = Cm.LM n u_{j+1} (Ψ n + M) σ b`, the observable of the
band walk `pathH (sz.withLam lam')` when the carrier walk is `Ψ n + pathH (sz.withLam lam')`. -/
def loopFamNgShift (Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool) :
    (Fin k → Zd d (sz.L n)) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ :=
  fun a M => Cm.LM n (gridTime s t K n (j + 1)) (Ψ n + M) σ a

variable {Cm} {E lam' : ℕ → ℝ}
  {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- Under `LoopForm`, the carrier loop of a fine matrix is the loop at the spectral value. -/
theorem StepDecompGen_LM_eq (hL : StepDecompGen_LoopForm Cm E) (n : ℕ) (u : ℝ) {k : ℕ} (σ : Fin k → Bool)
    (b : Fin k → Zd d (sz.L n)) :
    (fun H => Cm.LM n u H σ b) = fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) H) (ztOf (Cm.m n) (E n) u) (loopOf σ b) := by
  funext H
  rw [(hL n).2.1 u H k σ b]
  unfold loopFine
  rw [loopM_eq_loopL]

/-- **The carrier corollary of target 2**: under `LoopForm` and `WalkForm`, the loop family seen from the shifted
walk is in `HermTestFun`, with the Hermitian second-derivative bound `k (k + 1) N η^{-(k+2)}` in `Cm.eta n u`. -/
theorem StepDecompGen_hermLoop (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ)
    (n : ℕ) (u : ℝ) (hu : u < 1) {k : ℕ} (σ : Fin k → Bool) (b : Fin k → Zd d (sz.L n)) :
    HermTestFun sz n (fun H => Cm.LM n u (Ψ n + H) σ b) ∧
      ∀ M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian → y.IsHermitian →
        ‖fderiv ℝ (fderiv ℝ (fun H => Cm.LM n u (Ψ n + H) σ b)) M y y‖ ≤
          ((k * (k + 1) : ℕ) : ℝ) * (Sizes.size sz n : ℝ) * (Cm.eta n u)⁻¹ ^ (k + 2) * ‖y‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := hermTestFunLoopNOf sz k n (Cm.m n) (E n) u (hL n).1 hu σ b
  set f : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ := fun H =>
    loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) H) (ztOf (Cm.m n) (E n) u) (loopOf σ b) with hf
  have hfun : (fun H => Cm.LM n u (Ψ n + H) σ b) = fun M => f (Ψ n + M) := by
    funext M
    exact congrFun (StepDecompGen_LM_eq hL n u σ b) (Ψ n + M)
  rw [hfun]
  refine ⟨StepDecompGen_hermTestFun_shift h1 (hW.1 n), fun M y hM hy => ?_⟩
  rw [StepDecompGen_fderiv2_shift f (Ψ n) M y, (hL n).2.2.2 u]
  exact h2 (Ψ n + M) y ((hW.1 n).add hM) hy

/-- The family of `loopFamNgShift` is in `HermTestFun` at the grid times of a window. -/
theorem StepDecompGen_loopFamShift_hermTestFun (hL : StepDecompGen_LoopForm Cm E)
    (hW : StepDecompGen_WalkForm Cm lam' Ψ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hst : s n ≤ t n)
    (ht1 : t n < 1) (hj : j + 1 ≤ K n) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    HermTestFun sz n (loopFamNgShift Cm Ψ s t K n j σ a) ∧
      ∀ M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian → y.IsHermitian →
        ‖fderiv ℝ (fderiv ℝ (loopFamNgShift Cm Ψ s t K n j σ a)) M y y‖ ≤
          (((k * (k + 1) : ℕ) : ℝ) * (Sizes.size sz n : ℝ) *
            (Cm.eta n (gridTime s t K n (j + 1)))⁻¹ ^ (k + 2)) * ‖y‖ ^ 2 := by
  have hu1 := StepDecompN_gridTime_lt_one s t K n hst hj ht1
  obtain ⟨h1, h2⟩ := StepDecompGen_hermLoop hL hW n _ hu1 σ a
  exact ⟨h1, fun M y hM hy => h2 M y hM hy⟩

end Ident

/-! ### 10. Identifications under `LoopForm` and `WalkForm` (target 5) -/

section Ident2

variable {d : ℕ} {sz : Sizes d} {Cm : Step2Mat sz} {E lam' : ℕ → ℝ}
  {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- The band walk of the model at the coupling `lam'`, read as a matrix of `sz` (`(sz.withLam lam').L n = sz.L n`). -/
abbrev StepDecompGen_pathH (sz : Sizes d) (lam' : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  pathH (sz.withLam lam') s t K n k ω

/-- `HermTestFun` does not see the coupling of the sizes. -/
theorem StepDecompGen_hermTestFun_withLam {n : ℕ} (g : ℕ → ℝ)
    {f : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ} (h : HermTestFun sz n f) :
    HermTestFun (sz.withLam g) n f := ⟨h.contDiffAt, h.bdd₀⟩

/-- The Hpath of a `WalkForm` carrier. -/
theorem StepDecompGen_Hpath_eq (hW : StepDecompGen_WalkForm Cm lam' Ψ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (ω : PathΩ sz) : Cm.Hpath s t K n k ω = Ψ n + StepDecompGen_pathH sz lam' s t K n k ω :=
  hW.2.2 s t K n k ω

/-- The family `loopFamNgShift` is a label family of `HermTestFun`s for the walk `sz.withLam lam'`. -/
theorem StepDecompGen_hΦ (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ)
    (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n) {k : ℕ}
    (σ : Fin k → Bool) :
    ∀ a, HermTestFun (sz.withLam lam') n (loopFamNgShift Cm Ψ s t K n j σ a) :=
  fun a => StepDecompGen_hermTestFun_withLam lam' (StepDecompGen_loopFamShift_hermTestFun hL hW s t K n j hst ht1 hj σ a).1

/-- `ZvecNg` is the directional derivative of the shifted family along the Gaussian increment. -/
theorem StepDecompGen_ZvecNg_eq (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ)
    (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n) {k : ℕ}
    (σ : Fin k → Bool) (ω : PathΩ sz) (b : Fin k → Zd d (sz.L n)) :
    ZvecNg Cm s t K n j σ ω b =
      (Real.sqrt (gridStep s t K n) : ℂ) *
        fderiv ℝ (loopFamNgShift Cm Ψ s t K n j σ b) (pathH (sz.withLam lam') s t K n j ω)
          (Sizes.seqXmat (sz.withLam lam') n (ω (j + 1))) := by
  have hu1 := StepDecompN_gridTime_lt_one s t K n hst hj ht1
  have hT := (StepDecompGen_hermLoop hL hW n _ hu1 σ b).1
  have hH : (StepDecompGen_pathH sz lam' s t K n j ω).IsHermitian := pathH_isHermitian (sz.withLam lam') s t K n j ω
  have hdiff : DifferentiableAt ℝ (fun H => Cm.LM n (gridTime s t K n (j + 1)) H σ b)
      (Ψ n + StepDecompGen_pathH sz lam' s t K n j ω) := by
    have hT0 : HermTestFun sz n (fun H => Cm.LM n (gridTime s t K n (j + 1)) H σ b) := by
      rw [StepDecompGen_LM_eq hL]
      exact (hermTestFunLoopNOf sz k n (Cm.m n) (E n) _ (hL n).1 hu1 σ b).1
    exact (hT0.contDiffAt _ ((hW.1 n).add hH)).differentiableAt (by norm_num)
  have hinc : Cm.Hpath s t K n (j + 1) ω - Cm.Hpath s t K n j ω =
      (Real.sqrt (gridStep s t K n) : ℂ) • Sizes.seqXmat sz n (ω (j + 1)) := by
    rw [StepDecompGen_Hpath_eq hW, StepDecompGen_Hpath_eq hW]
    rw [show StepDecompGen_pathH sz lam' s t K n (j + 1) ω = _ from pathH_succ (sz.withLam lam') s t K n j ω]
    abel
  unfold ZvecNg loopFamNg
  rw [hinc, StepDecompGen_dirDerivN_smul, StepDecompGen_Hpath_eq hW]
  congr 1
  refine (StepDecompN_hasDerivAt_dir _ hdiff).deriv.trans ?_
  exact (congrArg (fun L => L (Sizes.seqXmat sz n (ω (j + 1))))
    (fderiv_comp_add_left (𝕜 := ℝ) (f := fun H => Cm.LM n (gridTime s t K n (j + 1)) H σ b) (Ψ n)
      (x := StepDecompGen_pathH sz lam' s t K n j ω))).symm

/-- `stepZCN` of the shifted family with a kernel `U` is `Σ_a U(b,a) ZvecNg_a`. -/
theorem StepDecompGen_stepZCN_eq_sum (hL : StepDecompGen_LoopForm Cm E)
    (hW : StepDecompGen_WalkForm Cm lam' Ψ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hst : s n ≤ t n)
    (ht1 : t n < 1) (hj : j + 1 ≤ K n) {k : ℕ} (σ : Fin k → Bool)
    (U : (Fin k → Zd d (sz.L n)) → (Fin k → Zd d (sz.L n)) → ℂ) (b : Fin k → Zd d (sz.L n))
    (ω : PathΩ sz) :
    stepZCN (sz.withLam lam') s t K n j (loopFamNgShift Cm Ψ s t K n j σ) U b ω =
      ∑ a, U b a * ZvecNg Cm s t K n j σ ω a := by
  rw [← StepDecompN_sum_fderiv_eq_stepZCN (sz.withLam lam') s t K n j
    (Φ := loopFamNgShift Cm Ψ s t K n j σ) U b ω, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [StepDecompGen_ZvecNg_eq hL hW s t K n j hst ht1 hj σ ω a]
  exact mul_left_comm _ _ _

/-- **Target 5, `ZvecNg_eq_stepZCN`** (`ZvecN_eq_stepZCN`, `StepDecompN:1126`): the first-chaos part is `stepZCN`
of the shifted loop family with the identity kernel, at the walk `sz.withLam lam'`. -/
theorem ZvecNg_eq_stepZCN (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ)
    (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n) {k : ℕ}
    (σ : Fin k → Bool) (b : Fin k → Zd d (sz.L n)) (ω : PathΩ sz) :
    ZvecNg Cm s t K n j σ ω b =
      stepZCN (sz.withLam lam') s t K n j (loopFamNgShift Cm Ψ s t K n j σ)
        (fun a a' => if a = a' then 1 else 0) b ω := by
  rw [StepDecompGen_stepZCN_eq_sum hL hW s t K n j hst ht1 hj σ _ b ω, StepDecompN_sum_delta]

/-- `stepXiCN` with the identity kernel (in the world of one `Sizes`). -/
theorem StepDecompGen_stepXiCN_delta (P : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (Φ : ι → Matrix (Idx d (P.L n) (P.W n)) (Idx d (P.L n) (P.W n)) ℂ → ℂ) (b : ι) (ω : PathΩ P) :
    stepXiCN P s t K n j Φ (fun a a' => if a = a' then 1 else 0) b ω =
      Φ b (pathH P s t K n (j + 1) ω) -
        (pathP P)[fun ω' => Φ b (pathH P s t K n (j + 1) ω') | filt P j] ω := by
  have e1 : (∑ a, (if b = a then (1 : ℂ) else 0) * Φ a (pathH P s t K n (j + 1) ω)) =
      Φ b (pathH P s t K n (j + 1) ω) := StepDecompN_sum_delta _ b
  have e2 : (fun ω' : PathΩ P => ∑ a, (if b = a then (1 : ℂ) else 0) * Φ a (pathH P s t K n (j + 1) ω')) =
      fun ω' => Φ b (pathH P s t K n (j + 1) ω') :=
    funext fun ω' => StepDecompN_sum_delta _ b
  unfold stepXiCN
  beta_reduce
  rw [e1, e2]

/-- **Target 5, `martIncNg_eq_stepXiCN`** (`martIncN_eq_stepXiCN`, `StepDecompN:1269`): a.e., simultaneously for all
labels, the martingale increment is `stepXiCN` of the shifted loop family with the identity kernel; the deterministic
`Cm.K` part of `AvecNg` cancels in the conditional mean. -/
theorem martIncNg_eq_stepXiCN (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ)
    (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n) {k : ℕ}
    (σ : Fin k → Bool) :
    ∀ᵐ ω ∂(Cm.Pp), ∀ b : Fin k → Zd d (sz.L n),
      martIncNg Cm s t K n j σ ω b =
        stepXiCN (sz.withLam lam') s t K n j (loopFamNgShift Cm Ψ s t K n j σ)
          (fun a a' => if a = a' then 1 else 0) b ω := by
  have hΦ := StepDecompGen_hΦ hL hW s t K n j hst ht1 hj σ
  have hPp : Cm.Pp = pathP (sz.withLam lam') := hW.2.1
  have : IsProbabilityMeasure Cm.Pp := by rw [hPp]; exact isProbabilityMeasure_pathP _
  refine ae_all_iff.mpr fun b => ?_
  have hint : Integrable (fun ω' : PathΩ sz => loopFamNgShift Cm Ψ s t K n j σ b
      (StepDecompGen_pathH sz lam' s t K n (j + 1) ω')) Cm.Pp := by
    rw [hPp]
    exact StepDecompN_integrable_phi (sz.withLam lam') s t K n (hΦ b) (j + 1)
  have hsub := condExp_sub hint
    (integrable_const (Cm.K n (gridTime s t K n (j + 1)) σ b)) (filt sz j)
  have hconst := condExp_const (μ := Cm.Pp) ((filt sz).le j)
    (Cm.K n (gridTime s t K n (j + 1)) σ b)
  have hAvec : (fun ω' : PathΩ sz => AvecNg Cm s t K n (j + 1) σ ω' b)
      = (fun ω' : PathΩ sz => loopFamNgShift Cm Ψ s t K n j σ b
          (StepDecompGen_pathH sz lam' s t K n (j + 1) ω'))
        - fun _ => Cm.K n (gridTime s t K n (j + 1)) σ b := by
    funext ω'
    simp only [AvecNg, STLKMg, STLMg, Pi.sub_apply, loopFamNgShift]
    rw [StepDecompGen_Hpath_eq hW]
  have hA0 : ∀ ω : PathΩ sz, AvecNg Cm s t K n (j + 1) σ ω b
      = loopFamNgShift Cm Ψ s t K n j σ b (StepDecompGen_pathH sz lam' s t K n (j + 1) ω)
        - Cm.K n (gridTime s t K n (j + 1)) σ b := fun ω => congrFun hAvec ω
  filter_upwards [hsub] with ω hω
  have hmain : martIncNg Cm s t K n j σ ω b =
      loopFamNgShift Cm Ψ s t K n j σ b (StepDecompGen_pathH sz lam' s t K n (j + 1) ω) -
        MeasureTheory.condExp (filt sz j) Cm.Pp (fun ω' => loopFamNgShift Cm Ψ s t K n j σ b
          (StepDecompGen_pathH sz lam' s t K n (j + 1) ω')) ω := by
    unfold martIncNg
    rw [hA0 ω, hAvec, hω]
    simp only [Pi.sub_apply, hconst]
    ring
  have hcond : ∀ (f : PathΩ sz → ℂ) (ω' : PathΩ sz), MeasureTheory.condExp (filt sz j) Cm.Pp f ω' =
      (pathP (sz.withLam lam'))[f | filt (sz.withLam lam') j] ω' := fun f ω' => by rw [hPp]; rfl
  rw [hmain]
  refine Eq.trans ?_ (StepDecompGen_stepXiCN_delta (sz.withLam lam') s t K n j
    (loopFamNgShift Cm Ψ s t K n j σ) b ω).symm
  exact congrArg (HSub.hSub _) (hcond _ ω)

/-- **Target 5, `YvecNg_eq_stepYCN`** (`YvecN_eq_stepYCN`): a.e., for all labels, `YvecNg` is `stepYCN` of the shifted
loop family with the identity kernel. -/
theorem YvecNg_eq_stepYCN (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ)
    (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n) {k : ℕ}
    (σ : Fin k → Bool) :
    ∀ᵐ ω ∂(Cm.Pp), ∀ b : Fin k → Zd d (sz.L n),
      YvecNg Cm s t K n j σ ω b =
        stepYCN (sz.withLam lam') s t K n j (loopFamNgShift Cm Ψ s t K n j σ)
          (fun a a' => if a = a' then 1 else 0) b ω := by
  filter_upwards [martIncNg_eq_stepXiCN hL hW s t K n j hst ht1 hj σ] with ω hω b
  unfold YvecNg stepYCN
  rw [hω b, ZvecNg_eq_stepZCN hL hW s t K n j hst ht1 hj σ b ω]

/-- Conditional sub-Gaussianity for the walk `sz.withLam lam'` is conditional sub-Gaussianity for any measure equal to
`pathP (sz.withLam lam')` (the filtrations agree by definition). -/
theorem StepDecompGen_hcsg_of_withLam {d : ℕ} {sz : Sizes d} (lam' : ℕ → ℝ) {μ : Measure (PathΩ sz)}
    [IsProbabilityMeasure μ] (hμ : μ = pathP (sz.withLam lam')) {j : ℕ} {X : PathΩ sz → ℝ} {c : ℝ≥0}
    (hX : HasCondSubgaussianMGF (filt (sz.withLam lam') j) ((filt (sz.withLam lam')).le j) X c
      (pathP (sz.withLam lam'))) :
    HasCondSubgaussianMGF (filt sz j) ((filt sz).le j) X c μ := by
  subst hμ
  exact hX

end Ident2

/-! ### 11. Band re-derivations of target 5 -/

/-! ### 12. Compiled nonempty instances (`d = 3`, `sz0`; targets 1-5)

Data: the merged admissible sequence `sz0` (`d = 3`, `L_0 = 4`, `W_0 = 32`, `lam_0 = 1/64`, `N = 2097152`), the band carrier
`bandStep2Mat sz0 (fun _ => 0)` (`E = 0`, `m = i`) with `Ψ = 0`, `lam' = sz0.lam`, the window `s ≡ 0`, `t ≡ 1/2`, `K ≡ 4`
(`Δ = 1/8`, `u_1 = 1/8`, `u_2 = 1/4`), size index `0`, loops of length `3`, `σ = (+,-,+)`, label `(0,0,0)`.  Step `j = 0`
has `H_0 = 0` (deterministic), step `j = 1` a random `H_1`.  Every deterministic premise is discharged. -/

end RBM.BA

end
