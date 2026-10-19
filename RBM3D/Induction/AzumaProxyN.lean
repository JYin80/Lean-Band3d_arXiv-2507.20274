/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.GridAssemblyN
import RBM3D.Induction.GridGoodN
import RBM3D.Induction.StepDecompN
import RBM3D.Induction.LoopC2N
import RBM3D.Path.Markov
import RBM3D.Gauss.LoopGenerator
import RBM3D.Loop.KLTreeDeriv

/-!
# The sub-Gaussian proxy of the first-chaos increments (`d ≥ 3`)

The martingale term of (3.13) `int_K-L_ST` (Lemma 3.4, `Sol_CalL`) and of (3.18) `alu9_STime`
(Lemma 3.6, `lem:DIfREP`) is estimated by the Azuma-Hoeffding inequality, with the
quadratic-variation proxy; the good set is the one of Lemma 4.3 (`lem:SEforLn`).

## Contents (namespace `RBM.Ind`)

* **`azumaSubGN : AzumaSubGN sz s t K`** (the statement `AzumaSubGN` is in `GridAssemblyN.lean`):
  for a finite family `Φ` in the Hermitian test class `HermTestFun`, weights `κ`, a stopping family
  `{j < τ} ∈ F_j` on which `H_j ∈ G j`, and `Q` majorising
  `Δ Σ_c gvar_c ‖Σ_b κ_b ∂_c Φ_b(M)‖²` on the Hermitian matrices of `G j`, the stopped
  `1_{j<τ} Σ_b κ_b Z_b` is conditionally sub-Gaussian with proxy `Q` (real and imaginary parts).
  Proof: `Σ_b κ_b Z_b = stepZCN` of the family `Φ` with the kernel `(b, a) ↦ κ_a`;
  `linTrVar (AbCN) ≤ Σ_c gvar_c ‖Σ_b κ_b ∂_c Φ_b‖²` (and for `(-I) • AbCN`); then
  `stepDecompCN_Z_subG`, i.e. `hasCondSubgaussianMGF_linear`.
* The loops at the initial grid state: `𝓛_0 = 𝒦_0` at `H_0 = 0` (`azumaProxy_loopL_zero_eq_KLK`,
  `azumaProxy_loopFine_sub_STKloop`).
* The composition `azumaProxy_subG_ugen` (`SubGaussStopN` for `ZvecN` from `azumaSubGN`,
  `hermTestFunLoopN`, `qvPropagatedN`).

Conventions: `sz : Sizes d`, labels in `Zd d (sz.L n)`, coordinates `CoordF d L W` with variances
`gvarF d L W (sz.lam n)`, matrix indices `Idx d L W`.  The identity
`linTrVar n A = Σ_c gvarF_c (linTr n A X_c)²` goes through `vB_self`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Loop RBM.Gauss RBM.Path RBM.Ind
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-! ## 1. The sub-Gaussian proxy `azumaSubGN` -/

section Azuma

variable {d : ℕ} (sz : Sizes d)

/-- The directional derivative along the real line `y ↦ M + y X` at `0` is `fderiv ℝ Ψ M X`, for
`Ψ` differentiable at `M`. -/
private theorem azumaProxy_hasDerivAt_dir {ι : Type*} [Fintype ι] [DecidableEq ι]
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

/-- `dirDerivN` is `fderiv ℝ` where the observable is differentiable. -/
private theorem azumaProxy_dirDerivN_eq {L W : ℕ} [NeZero L] [NeZero W]
    {Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ} {M : Matrix (Idx d L W) (Idx d L W) ℂ}
    (X : Matrix (Idx d L W) (Idx d L W) ℂ) (hd : DifferentiableAt ℝ Φ M) :
    dirDerivN Φ M X = fderiv ℝ Φ M X :=
  (azumaProxy_hasDerivAt_dir X hd).deriv

/-- `linTr` at the direction `(-I) • A` reads the imaginary part of `trace (A * X)`. -/
private theorem azumaProxy_linTr_neg_I_smul (n : ℕ)
    (A X : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    linTr n ((-Complex.I) • A) X = (Matrix.trace (A * X)).im := by
  unfold linTr
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  ring

/-- The coordinate matrix of the slice is the coordinate matrix of the coordinate. -/
private theorem azumaProxy_seqXmat_single (n : ℕ) (c : CoordF d (sz.L n) (sz.W n)) :
    Sizes.seqXmat sz n (Pi.single (⟨n, c⟩ : Sizes.SeqCoord sz) 1)
      = coordinateMatrix d (sz.L n) (sz.W n) c := by
  have hs : Sizes.slice sz n (Pi.single (⟨n, c⟩ : Sizes.SeqCoord sz) 1)
      = Pi.single c 1 := by
    funext c'
    change (Pi.single (⟨n, c⟩ : Sizes.SeqCoord sz) (1 : ℝ) : Sizes.SeqCoord sz → ℝ) ⟨n, c'⟩
      = (Pi.single c (1 : ℝ) : CoordF d (sz.L n) (sz.W n) → ℝ) c'
    by_cases h : c' = c
    · subst h; simp
    · have h' : (⟨n, c'⟩ : Sizes.SeqCoord sz) ≠ ⟨n, c⟩ := fun he =>
        h (eq_of_heq (Sigma.mk.inj he).2)
      rw [Pi.single_eq_of_ne h', Pi.single_eq_of_ne h]
  unfold Sizes.seqXmat coordinateMatrix
  rw [hs]

/-- `linTrVar` as the sum over the coordinates of one size. -/
private theorem azumaProxy_linTrVar_eq (n : ℕ)
    (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    linTrVar n A = ∑ c : CoordF d (sz.L n) (sz.W n),
      (gvarF d (sz.L n) (sz.W n) (sz.lam n) c : ℝ) *
      (linTr n A (coordinateMatrix d (sz.L n) (sz.W n) c)) ^ 2 := by
  classical
  rw [← vB_self (sz := sz)]
  unfold vB coordFinset
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Function.Embedding.sigmaMk_apply, azumaProxy_seqXmat_single]
  change (gvarF d (sz.L n) (sz.W n) (sz.lam n) c : ℝ) * _ * _ = _
  ring

private theorem azumaProxy_sq_re_le (z : ℂ) : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
  calc z.re ^ 2 = |z.re| ^ 2 := (sq_abs _).symm
    _ ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm z) 2

private theorem azumaProxy_sq_im_le (z : ℂ) : z.im ^ 2 ≤ ‖z‖ ^ 2 := by
  calc z.im ^ 2 = |z.im| ^ 2 := (sq_abs _).symm
    _ ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm z) 2

/-- **The variance identity**: for `A` with `tr (A X_c) = D_c`, `linTrVar A` and
`linTrVar ((-I) • A)` are `Σ_c gvar_c (Re D_c)²` and `Σ_c gvar_c (Im D_c)²`, hence at most
`Σ_c gvar_c ‖D_c‖²`. -/
private theorem azumaProxy_linTrVar_le (n : ℕ)
    (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (D : CoordF d (sz.L n) (sz.W n) → ℂ)
    (hD : ∀ c, Matrix.trace (A * coordinateMatrix d (sz.L n) (sz.W n) c) = D c) :
    linTrVar n A ≤ ∑ c : CoordF d (sz.L n) (sz.W n),
        (gvarF d (sz.L n) (sz.W n) (sz.lam n) c : ℝ) * ‖D c‖ ^ 2 ∧
    linTrVar n ((-Complex.I) • A) ≤
      ∑ c : CoordF d (sz.L n) (sz.W n), (gvarF d (sz.L n) (sz.W n) (sz.lam n) c : ℝ) * ‖D c‖ ^ 2 := by
  constructor
  · rw [azumaProxy_linTrVar_eq]
    refine Finset.sum_le_sum fun c _ =>
      mul_le_mul_of_nonneg_left ?_ (gvarF d (sz.L n) (sz.W n) (sz.lam n) c).2
    have : linTr n A (coordinateMatrix d (sz.L n) (sz.W n) c) = (D c).re := by
      rw [← hD c]; rfl
    rw [this]
    exact azumaProxy_sq_re_le _
  · rw [azumaProxy_linTrVar_eq]
    refine Finset.sum_le_sum fun c _ =>
      mul_le_mul_of_nonneg_left ?_ (gvarF d (sz.L n) (sz.W n) (sz.lam n) c).2
    rw [azumaProxy_linTr_neg_I_smul, hD c]
    exact azumaProxy_sq_im_le _

/-- `tr (A X)` for `A = Σ_a κ_a gradMat Φ_a M` at a Hermitian direction `X` is the `κ`-weighted sum
of the directional derivatives. -/
private theorem azumaProxy_trace_eq {ι : Type*} [Fintype ι] {n : ℕ}
    {Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (hΦ : ∀ b, HermTestFun sz n (Φ b)) (κ : ι → ℂ)
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian)
    {X : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hX : X.IsHermitian) :
    Matrix.trace ((∑ a, κ a • gradMat (Φ a) M) * X) = ∑ a, κ a * dirDerivN (Φ a) M X := by
  rw [Matrix.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hd : DifferentiableAt ℝ (Φ a) M := ((hΦ a).contDiffAt M hM).differentiableAt (by norm_num)
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ← fderiv_eq_trace_gradMat M hX,
    azumaProxy_dirDerivN_eq X hd]

/-- The zero function is conditionally sub-Gaussian with every proxy. -/
private theorem azumaProxy_subG_zero (j : ℕ) (c : ℝ≥0) :
    HasCondSubgaussianMGF (filt sz j) ((filt sz).le j) (fun _ => (0 : ℝ)) c (pathP sz) := by
  unfold HasCondSubgaussianMGF
  refine ⟨by simp, ?_⟩
  filter_upwards with ω t
  simp only [mgf, mul_zero, Real.exp_zero, integral_const, smul_eq_mul, mul_one]
  have h1 : (condExpKernel (pathP sz) (filt sz j) ω).real Set.univ = 1 := by simp
  rw [h1]
  exact Real.one_le_exp (by positivity)

/-- **`azumaSubGN`** (the statement `AzumaSubGN` of `Induction/GridAssemblyN.lean`): for a finite
family `Φ` in the Hermitian test class, weights `κ`, a stopping family
`{j < τ} ∈ F_j` on which the grid state lies in `G j`, and `Q` majorising
`Δ Σ_c gvar_c ‖Σ_b κ_b ∂_c Φ_b(M)‖²` on the Hermitian matrices of `G j`, the stopped combination
`1_{j<τ} Σ_b κ_b Z_b` of the first-chaos parts is conditionally sub-Gaussian with proxy `Q` (real
and imaginary parts).  Proof: for a nonempty label set `Σ_b κ_b Z_b = stepZCN` of the family `Φ`
with the kernel `(b, a) ↦ κ_a`, the variance identity
`linTrVar (AbCN) ≤ Σ_c gvar_c ‖Σ_b κ_b ∂_c Φ_b‖²` (and the same for `(-I) • AbCN`) and
`stepDecompCN_Z_subG` (`hasCondSubgaussianMGF_linear`); for an
empty label set the increment is `0`. -/
theorem azumaSubGN (s t : ℕ → ℝ) (K : ℕ → ℕ) : AzumaSubGN sz s t K := by
  intro n ι _ Φ hΦ κ τ G hτ hG j Q hQ
  classical
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨b₀⟩⟩
  · -- empty label set: the combination is `0`
    have hz : ∀ ω : PathΩ sz, ({ω' | j < τ ω'}.indicator
        (fun ω => ∑ b, κ b * ZfamN sz s t K n j Φ ω b) ω) = 0 := by
      intro ω
      simp [Finset.univ_eq_empty]
    unfold SubGaussFormN
    simp only [hz, Complex.zero_re, Complex.zero_im]
    exact ⟨azumaProxy_subG_zero sz j Q, azumaProxy_subG_zero sz j Q⟩
  · set U : ι → ι → ℂ := fun _ a => κ a with hU
    -- the combination is `stepZCN`
    have hFeq : ∀ ω : PathΩ sz,
        ∑ b, κ b * ZfamN sz s t K n j Φ ω b = stepZCN sz s t K n j Φ U b₀ ω := by
      intro ω
      have hH := pathH_isHermitian sz s t K n j ω
      have hX := Sizes.seqXmat_isHermitian sz n (ω (j + 1))
      have htr := azumaProxy_trace_eq sz hΦ κ hH hX
      have hA : AbCN sz s t K n j Φ U b₀ ω = ∑ a, κ a • gradMat (Φ a) (pathH sz s t K n j ω) := rfl
      set w := Matrix.trace (AbCN sz s t K n j Φ U b₀ ω * Sizes.seqXmat sz n (ω (j + 1))) with hw
      have hre : linTr n (AbCN sz s t K n j Φ U b₀ ω) (Sizes.seqXmat sz n (ω (j + 1))) = w.re := rfl
      have him : linTr n ((-Complex.I) • AbCN sz s t K n j Φ U b₀ ω)
          (Sizes.seqXmat sz n (ω (j + 1))) = w.im := azumaProxy_linTr_neg_I_smul sz n _ _
      have hw' : w = ∑ a, κ a * dirDerivN (Φ a) (pathH sz s t K n j ω)
          (Sizes.seqXmat sz n (ω (j + 1))) := by rw [hw, hA]; exact htr
      have hsum : ∑ b, κ b * ZfamN sz s t K n j Φ ω b = (Real.sqrt (gridStep s t K n) : ℂ) * w := by
        rw [hw', Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        unfold ZfamN; ring
      rw [hsum]
      unfold stepZCN stepZCN_re stepZCN_im
      rw [hre, him]
      have hreim := Complex.re_add_im w
      push_cast
      linear_combination (Real.sqrt (gridStep s t K n) : ℂ) * hreim.symm
    -- the variance bound on `{j < τ}`
    have hbound : ∀ ω ∈ {ω : PathΩ sz | j < τ ω},
        (gridStep s t K n * linTrVar n (AbCN sz s t K n j Φ U b₀ ω) ≤ (Q : ℝ)) ∧
        (gridStep s t K n * linTrVar n ((-Complex.I) • AbCN sz s t K n j Φ U b₀ ω) ≤ (Q : ℝ)) := by
      intro ω hω
      have hmem : pathH sz s t K n j ω ∈ G j := hG ω j hω
      have hH := pathH_isHermitian sz s t K n j ω
      have hq := hQ _ hmem hH
      set D : CoordF d (sz.L n) (sz.W n) → ℂ := fun c => ∑ b, κ b * dirDerivN (Φ b)
        (pathH sz s t K n j ω) (coordinateMatrix d (sz.L n) (sz.W n) c) with hD
      have hDeq : ∀ c, Matrix.trace (AbCN sz s t K n j Φ U b₀ ω *
          coordinateMatrix d (sz.L n) (sz.W n) c) = D c :=
        fun c => azumaProxy_trace_eq sz hΦ κ hH (coordinateMatrix_isHermitian _ _ _ c)
      obtain ⟨h1, h2⟩ := azumaProxy_linTrVar_le sz n _ D hDeq
      have hv1 := linTrVar_nonneg n (AbCN sz s t K n j Φ U b₀ ω)
      have hv2 := linTrVar_nonneg n ((-Complex.I) • AbCN sz s t K n j Φ U b₀ ω)
      rcases le_or_gt 0 (gridStep s t K n) with hΔ | hΔ
      · exact ⟨(mul_le_mul_of_nonneg_left h1 hΔ).trans hq,
          (mul_le_mul_of_nonneg_left h2 hΔ).trans hq⟩
      · exact ⟨(mul_nonpos_of_nonpos_of_nonneg hΔ.le hv1).trans Q.2,
          (mul_nonpos_of_nonpos_of_nonneg hΔ.le hv2).trans Q.2⟩
    have hZ := stepDecompCN_Z_subG sz s t K n j hΦ U b₀ {ω | j < τ ω} (hτ j) (Q : ℝ) Q.2
      (fun ω hω => (hbound ω hω).1) (fun ω hω => (hbound ω hω).2)
    have hFfun : (fun ω : PathΩ sz => ∑ b, κ b * ZfamN sz s t K n j Φ ω b)
        = stepZCN sz s t K n j Φ U b₀ := funext hFeq
    have hre : (fun ω : PathΩ sz => ({ω' | j < τ ω'}.indicator
          (stepZCN sz s t K n j Φ U b₀) ω).re)
        = fun ω => {ω' | j < τ ω'}.indicator (fun ω' => stepZCN_re sz s t K n j Φ U b₀ ω') ω := by
      funext ω
      by_cases h : ω ∈ {ω' | j < τ ω'}
      · simp only [Set.indicator_of_mem h]
        simp [stepZCN]
      · simp [Set.indicator_of_notMem h]
    have him : (fun ω : PathΩ sz => ({ω' | j < τ ω'}.indicator
          (stepZCN sz s t K n j Φ U b₀) ω).im)
        = fun ω => {ω' | j < τ ω'}.indicator (fun ω' => stepZCN_im sz s t K n j Φ U b₀ ω') ω := by
      funext ω
      by_cases h : ω ∈ {ω' | j < τ ω'}
      · simp only [Set.indicator_of_mem h]
        simp [stepZCN]
      · simp [Set.indicator_of_notMem h]
    unfold SubGaussFormN
    rw [hFfun]
    exact ⟨by rw [hre]; exact hZ.1, by rw [him]; exact hZ.2⟩

end Azuma

/-! ## 2. The loops at the initial grid state `H_0 = 0`

At `u = 0` the flow value is `z_0 = E + m`, the grid state is `H = 0`, and `G_0 = M`: the loops are
the initial loops, `𝓛_{0,I}(0) = W^{-d(|I|-1)} ∏ m(σ_i) 1(all labels equal)`, which is the `M`-loop
and ((2.52) `eq:initial_K`) `𝒦_{0,I}` for every well-formed `I` of length `≥ 1`. -/

section Member

variable {d : ℕ}

/-- The scalar of a signed Green factor at `z_0` is `m(σ)` (`mSigma`, `mE_mul`). -/
private theorem azumaProxy_initialGreenScalar {E : ℝ} (hE : |E| ≤ 2) (s : Bool) :
    initialGreenScalar E s = mSigma E s := by
  have hm := mE_mul hE
  have h1 : -((E : ℂ) + mE E) * mE E = 1 := by linear_combination -hm
  cases s
  · have h2 : -((starRingEnd ℂ) ((E : ℂ) + mE E)) * (starRingEnd ℂ) (mE E) = 1 := by
      have := congrArg (starRingEnd ℂ) h1
      simpa [map_mul, map_neg] using this
    simp only [initialGreenScalar, mSigma, Bool.false_eq_true, ite_false]
    exact inv_eq_of_mul_eq_one_right h2
  · simp only [initialGreenScalar, mSigma, ite_true]
    exact inv_eq_of_mul_eq_one_right h1

/-- A label word that is not constant has an unequal adjacent pair. -/
private theorem azumaProxy_adjacentMismatch {L : ℕ} (a : Zd d L) (as : List (Zd d L))
    (h : ¬ ∀ b ∈ as, b = a) : AdjacentMismatch d L (a :: as) := by
  induction as generalizing a with
  | nil => simp at h
  | cons b bs ih =>
      change a ≠ b ∨ AdjacentMismatch d L (b :: bs)
      by_cases hab : a = b
      · subst hab
        right
        refine ih a fun hall => h ?_
        intro c hc
        rcases List.mem_cons.1 hc with rfl | hc
        · rfl
        · exact hall c hc
      · exact Or.inl hab

/-- `adjacentBlockWeight` in the form of the `M`-loop:
`(W^{-d})^{|as|} 1(a₁ = ⋯ = aₙ)`. -/
private theorem azumaProxy_adjacentBlockWeight (L W : ℕ) (a : Zd d L) (as : List (Zd d L)) :
    adjacentBlockWeight d L W (a :: as) =
      ((W : ℂ)⁻¹ ^ d) ^ as.length *
        (if ∀ x ∈ a :: as, ∀ y ∈ a :: as, x = y then 1 else 0) := by
  by_cases hsame : ∀ b ∈ as, b = a
  · have hc : ∀ x ∈ a :: as, ∀ y ∈ a :: as, x = y := by
      intro x hx y hy
      have hx' : x = a := by
        rcases List.mem_cons.1 hx with rfl | hx
        · rfl
        · exact hsame x hx
      have hy' : y = a := by
        rcases List.mem_cons.1 hy with rfl | hy
        · rfl
        · exact hsame y hy
      rw [hx', hy']
    rw [adjacentBlockWeight_all_same d L W a as hsame]
    simp only [eq_true hc, ↓reduceIte, mul_one]
  · have hc : ¬ ∀ x ∈ a :: as, ∀ y ∈ a :: as, x = y := fun hall =>
      hsame fun b hb => hall b (List.mem_cons_of_mem a hb) a List.mem_cons_self
    rw [adjacentBlockWeight_zero_of_mismatch d L W (a :: as)
      (azumaProxy_adjacentMismatch a as hsame)]
    simp only [eq_false hc, ↓reduceIte, mul_zero]

/-- The value of a loop at `H = 0`, `u = 0`: `(∏ m(σ_i)) · adjacentBlockWeight`
(`initialLoopValue_nonempty`). -/
private theorem azumaProxy_loopL_zero_eq (L W : ℕ) [NeZero L] [NeZero W] {E : ℝ} (hE : |E| < 2)
    (I : LoopIdx (Zd d L)) (hI : I.WF) (a : Zd d L) (as : List (Zd d L)) (ha : I.a = a :: as) :
    loopL d L W (blockMat d L W (0 : Matrix (Idx d L W) (Idx d L W) ℂ)) (zt E 0) I =
      ((I.σ.zip I.a).map fun p => initialGreenScalar E p.1).prod *
        adjacentBlockWeight d L W (a :: as) := by
  have hb := blockMat_zero d L W
  have hg : loopL d L W 0 (zt E 0) I = initialLoopValue d L W E I := by
    simp [initialLoopValue, zt]
  rw [hb, hg, initialLoopValue_nonempty d L W hE I hI a as ha]

/-- **`𝓛_0 = 𝒦_0`** at `H_0 = 0` ((2.52) `eq:initial_K`):
every well-formed loop of length `≥ 1` at `z_0 = E + m` equals `𝒦_{0,I}` (`KLK_isKLoop` and
`KLK_one`). -/
private theorem azumaProxy_loopL_zero_eq_KLK (L W : ℕ) [NeZero L] [NeZero W] (hL : 3 ≤ L)
    (hW : 1 ≤ W) (g : ℝ) {E : ℝ} (hE : |E| < 2) (I : LoopIdx (Zd d L)) (hI : I.WF)
    (h1 : 1 ≤ I.length) :
    loopL d L W (blockMat d L W (0 : Matrix (Idx d L W) (Idx d L W) ℂ)) (zt E 0) I =
      KLK d L g W E 0 I := by
  obtain ⟨σ, as0⟩ := I
  cases as0 with
  | nil => simp [LoopIdx.length] at h1
  | cons a as =>
    by_cases h2 : 2 ≤ LoopIdx.length (⟨σ, a :: as⟩ : LoopIdx (Zd d L))
    · have hK : KLK d L g W E 0 ⟨σ, a :: as⟩ = MLoop d L W (mSigma E) ⟨σ, a :: as⟩ :=
        (KLK_isKLoop d L W g E hL hW hE).2.1 _ hI h2
      rw [hK, azumaProxy_loopL_zero_eq L W hE ⟨σ, a :: as⟩ hI a as rfl]
      have hσ : σ.length = (a :: as).length := hI
      have hmap : (σ.zip (a :: as)).map (fun p => initialGreenScalar E p.1) =
          σ.map (mSigma E) := by
        have hfun : (fun p : Bool × Zd d L => initialGreenScalar E p.1) =
            mSigma E ∘ Prod.fst :=
          funext fun p => azumaProxy_initialGreenScalar hE.le p.1
        rw [hfun, ← List.map_map, List.map_fst_zip hσ.le]
      have hlen : (⟨σ, a :: as⟩ : LoopIdx (Zd d L)).length - 1 = as.length := by
        simp [LoopIdx.length]
      simp only [MLoop, hlen]
      change (List.map (fun p => initialGreenScalar E p.1) (σ.zip (a :: as))).prod *
        adjacentBlockWeight d L W (a :: as) = _
      rw [hmap, azumaProxy_adjacentBlockWeight, inv_pow]
      by_cases hc : ∀ x ∈ a :: as, ∀ y ∈ a :: as, x = y
      · simp only [eq_true hc, ↓reduceIte]; ring
      · simp only [eq_false hc, ↓reduceIte]; ring
    · have has : as = [] := by
        simp only [LoopIdx.length, List.length_cons] at h2
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst has
      have hσ : σ.length = 1 := by simpa [LoopIdx.WF] using hI
      obtain ⟨s, rfl⟩ : ∃ s, σ = [s] := List.length_eq_one_iff.1 hσ
      have hg : loopL d L W 0 (zt E 0) ⟨[s], [a]⟩ = initialLoopValue d L W E ⟨[s], [a]⟩ := by
        simp [initialLoopValue, zt]
      rw [blockMat_zero, hg, initialLoopValue_one_edge d L W hE, KLK_one,
        azumaProxy_initialGreenScalar hE.le]

/-! ### The clauses of `GoodSetN` at `H = 0`, `u = 0` -/

section MemberSz

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

/-- `loopFine - 𝒦 = 0` at `H = 0`, `u = 0`, for loops of length `m ≥ 1`. -/
theorem azumaProxy_loopFine_sub_STKloop {E : ℝ} (hE : |E| < 2) {m : ℕ} (hm : 1 ≤ m)
    (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) :
    loopFine d (sz.L n) (sz.W n)
        (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (zt E 0) σ a
      - sz.STKloop n E 0 σ a = 0 := by
  unfold loopFine Sizes.STKloop
  rw [loopM_eq_loopL]
  exact sub_eq_zero.2 (azumaProxy_loopL_zero_eq_KLK (sz.L n) (sz.W n) (sz.three_le_L n)
    (sz.W_pos n) (sz.lam n) hE (loopOf σ a) (by simp [loopOf, LoopIdx.WF])
    (by simpa [loopOf, LoopIdx.length] using hm))

end MemberSz

end Member

/-! ## 3. The composition of `AzumaSubGN` with the loop observables

For `d ≥ 3`, from the proved `azumaSubGN`, the test class `hermTestFunLoopN` and the variance proxy
`qvPropagatedN`. -/

section Compose

variable {d : ℕ} (sz : Sizes d)

private theorem azumaProxy_gridStep_nonneg {s t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hst : s n ≤ t n) :
    0 ≤ gridStep s t K n :=
  div_nonneg (sub_nonneg.2 hst) (Nat.cast_nonneg _)

private theorem azumaProxy_gridTime_nonneg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hs0 : 0 ≤ s n)
    (hst : s n ≤ t n) (j : ℕ) : 0 ≤ gridTime s t K n j := by
  have hΔ : 0 ≤ gridStep s t K n := azumaProxy_gridStep_nonneg hst
  unfold gridTime
  have : (0 : ℝ) ≤ (j : ℝ) * gridStep s t K n := mul_nonneg (Nat.cast_nonneg _) hΔ
  linarith

/-- `u_{j+1} ≤ t n < 1` for `j + 1 ≤ K n`. -/
private theorem azumaProxy_gridTime_lt_one (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hst : s n ≤ t n)
    {j : ℕ} (hj : j + 1 ≤ K n) (ht1 : t n < 1) : gridTime s t K n (j + 1) < 1 := by
  have hK : K n ≠ 0 := by omega
  have hΔ : 0 ≤ gridStep s t K n := azumaProxy_gridStep_nonneg hst
  have hlast := gridTime_last s t K n hK
  have hle : gridTime s t K n (j + 1) ≤ gridTime s t K n (K n) := by
    unfold gridTime
    have : ((j + 1 : ℕ) : ℝ) ≤ (K n : ℝ) := Nat.cast_le.2 hj
    nlinarith
  linarith

/-- **`SubGaussStopN` for `ZvecN` from `AzumaSubGN`**: for the loop family `Φ_b = 𝓛_{u_{j+1},σ,b}`
(`loopFamN`, in the test class by `hermTestFunLoopN`), the propagator weights
`κ_b = Π_i (𝒰-slot)(a_i, b_i)` and the variance identity `qvPropagatedN`
(`Σ_c gvar_c ‖Σ_b κ_b ∂_c 𝓛_b‖² ≤ k · Re Σ κ κ̄' 𝓔⊗𝓔 = k · qvFormN`).  What remains for a consumer is
the deterministic majorant `hQ` of `Δ · k · qvFormN` on `G j`. -/
theorem azumaProxy_subG_ugen {E s t : ℕ → ℝ} {K : ℕ → ℕ} (h : AzumaSubGN sz s t K)
    (hE : ∀ n, |E n| < 2) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
    (n k : ℕ) (hk : 2 ≤ k) (σ : Fin k → Bool)
    (τ : PathΩ sz → ℕ) (G : ℕ → Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))
    (hτ : ∀ j, MeasurableSet[filt sz j] {ω | j < τ ω})
    (hG : ∀ ω j, j < τ ω → pathH sz s t K n j ω ∈ G j) (m : ℕ) (hm : m ≤ K n)
    (a : Fin k → Zd d (sz.L n)) (j : ℕ) (hj : j < m) (Q : ℝ≥0)
    (hQ : ∀ M ∈ G j, M.IsHermitian →
      gridStep s t K n * ((k : ℝ) * qvFormN sz n (E n) (gridTime s t K n (j + 1))
        (gridTime s t K n m) σ M a) ≤ (Q : ℝ)) :
    SubGaussStopN sz (E n) σ (gridTime s t K n) τ (fun j ω => ZvecN sz E s t K n j σ ω) m a j Q := by
  have hu0 : 0 ≤ gridTime s t K n (j + 1) :=
    azumaProxy_gridTime_nonneg s t K n (hs0 n) (hst n) (j + 1)
  have hu1 : gridTime s t K n (j + 1) < 1 :=
    azumaProxy_gridTime_lt_one s t K n (hst n) (show j + 1 ≤ K n by omega) (ht1 n)
  have hΔ : 0 ≤ gridStep s t K n := azumaProxy_gridStep_nonneg (hst n)
  have hΦ : ∀ b, HermTestFun sz n (loopFamN sz E s t K n j σ b) := fun b =>
    (hermTestFunLoopN sz k n (E n) (gridTime s t K n (j + 1)) (hE n) hu0 hu1 σ b).1
  have key := h n (loopFamN sz E s t K n j σ) hΦ
    (fun b => ∏ i : Fin k, uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma (E n) (σ i)) i)
      (gridTime s t K n (j + 1)) (gridTime s t K n m) (a i) (b i)) τ G hτ hG j Q
    (fun M hMG hMH => (mul_le_mul_of_nonneg_left
      (qvPropagatedN d sz n (E n) (hE n) (gridTime s t K n (j + 1)) hu0 hu1 M hMH k hk σ _) hΔ).trans (hQ M hMG hMH))
  exact key

end Compose

end RBM.Ind

end
