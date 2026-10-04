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
# The sub-Gaussian proxy of the first-chaos increments, and `0 ∈ GoodSetN` at `u = 0` (`d ≥ 3`)

Ticket T2159 (ST2-34, stochastic layer ST-2).  Port of RBM2D `Induction/AzumaProxyN.lean` §1, §2,
§8, §8c and of `Induction/NonAltGood.lean:561-1100` (`zero_mem_goodSetN`),
`Induction/GridGoodN.lean` (`azumaSubG_ugen`, `azumaSubG_goodExit`, `pathH_zero_of_s_zero`) at
commit `c9a24cf`, rewritten for `d ≥ 3` (cited `AzumaProxyN:<line>`, `NonAltGood:<line>`,
`GridGoodN:<line>`).  Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex`: the martingale
term of `int_K-L_ST` (`3_5:134`) and `alu9_STime` (`3_5:218-240`), with BDG replaced by
Azuma-Hoeffding (DECISIONS §10); the good set `lem:SEforLn` (`3_5:1017-1065`).

## What is here (namespace `RBM.Ind`)

* §1 `testFun_const_smul`, `testFun_linComb` (`AzumaProxyN:110, 133`): the Hermitian test class
  `HermTestFun` is closed under scalar multiples and finite linear combinations.
* §2 **`azumaSubGN : AzumaSubGN sz s t K`** (`AzumaProxyN:279`), the merged pin of
  `GridAssemblyN.lean:122`, unchanged and with no added hypothesis: for a finite family `Φ` in the
  test class, weights `κ`, a stopping family `{j < τ} ∈ F_j` on which `H_j ∈ G j`, and `Q`
  majorising `Δ Σ_c gvar_c ‖Σ_b κ_b ∂_c Φ_b(M)‖²` on the Hermitian matrices of `G j`, the stopped
  `1_{j<τ} Σ_b κ_b Z_b` is conditionally sub-Gaussian with proxy `Q` (real and imaginary parts).
  Route: `Σ_b κ_b Z_b = stepZCN` of the family `Φ` with the kernel `(b, a) ↦ κ_a`;
  `linTrVar (AbCN) ≤ Σ_c gvar_c ‖Σ_b κ_b ∂_c Φ_b‖²` (and for `(-I) • AbCN`); the merged
  `stepDecompCN_Z_subG`, i.e. `hasCondSubgaussianMGF_linear` (`Path/Markov.lean:636`).
* §3 **`zero_mem_goodSetN`** (new, DECISIONS §45; RBM2D `NonAltGood:996`):
  `0 ∈ GoodSetN … u = 0` for the initial state `H_0 = 0`, under deterministic level hypotheses
  `0 ≤ Γ`, `1 ≤ Γ Φ` and the (D4) level `k S_{cc} η_0 ≤ Γ² Λ b^{2k}`;
  `zero_mem_goodSetN_of_levels` has the sufficient condition `Γ² Λ ≥ k (1 + g²)^{2k}`.
* §4 the compositions `azumaProxy_subG_ugen`, `azumaProxy_subG_goodExit` (`SubGaussStopN` for
  `ZvecN` from the proved `azumaSubGN`, `hermTestFunLoopN`, `qvPropagatedN`),
  `azumaProxy_pathH_zero_of_s_zero`, `azumaProxy_pos_gridExitTauN`.
* §5-6 the scalar three-loop `W^{-2d} (y - z)⁻² (y - z̄)⁻¹` and the compiled nonempty instances at
  `d = 3` on the merged `sz0` and the grid `(sInst, vg, Kg)` (namespace `AzumaProxyNInst`), with the
  nondegeneracy of the proxy (`qProxy3_pos`).

## Dictionary and `d`-dependent changes (CLAUDE.md §5.2)

`d : Sizes` becomes `sz : Sizes d`; `Z2 (d.L n)` becomes `Zd d (sz.L n)`; `Coord`, `gvar`,
`coordinateMatrix`, `Idx` become `CoordF d L W`, `gvarF d L W (sz.lam n)`, `coordinateMatrix d L W`,
`Idx d L W`; `[NeZero k]` is dropped (as in the merged pin).  The identity
`linTrVar n A = Σ_c gvarF_c (linTr n A X_c)²` goes through the merged `vB_self`
(`Path/QVIdentity.lean:92`).  For `zero_mem_goodSetN` the changes are:

* the merged `GoodSetN` (`GridGoodN.lean:124`) has no (G1), (G3), (G4) (paper-delta `T2146a`), so
  only (G2), (Dec), (D1)-(D4), (Va), (Vb) are checked;
* `𝓛_0 = 𝒦_0` at `H_0 = 0` is the merged `KLK_isKLoop` (`(eq:initial_K)`) with
  `initialLoopValue_nonempty` (`Gauss/LoopGenerator.lean:572`) instead of RBM2D's `Kcal`;
* the pair form at equal labels carries `S_{cc} = (1 + 2 d g²)⁻¹` (the diagonal of
  `S^{(B)}(g)`, `sbKernel`) in place of RBM2D's `1/5`, and the scale is `B_{0,0} W^{-d}`
  (`sz.Bctl`) in place of `scaleM⁻¹`; the (D4) level `k S_{cc} η_0 ≤ Γ² Λ b^{2k}` depends on `g`, so
  RBM2D's condition `k/5 ≤ Γ² Λ` becomes this `g`-dependent one, which the unit levels
  `Γ = Λ = Φ = 1` need not satisfy (paper-delta candidate `T2159a`);
* `ellT L g 0 ≥ 1` (`one_le_ellT`) replaces `ellT L 0 = 1`, the far condition
  `ℓ_0 W^{τ'} ≤ diam_∞ a` forces two distinct labels (`STdiamInf`, `zdistInf`).

Every helper that the ticket does not pin is `private` or carries the prefix `azumaProxy_`.
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

/-! ## 1. Ports -/

section Ports

variable {d : ℕ} {sz : Sizes d} {n : ℕ}

theorem testFun_const_smul
    {Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (h : HermTestFun sz n Φ) (q : ℂ) : HermTestFun sz n (fun M => q • Φ M) := by
  refine ⟨fun M hM => (h.contDiffAt M hM).const_smul q, ?_⟩
  obtain ⟨C, hC⟩ := h.bdd₀
  exact ⟨‖q‖ * C, fun M hM => by
    rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hC M hM) (norm_nonneg _)⟩

private theorem azumaProxy_testFun_sum {ι : Type*} (s : Finset ι)
    {Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (h : ∀ i ∈ s, HermTestFun sz n (Φ i)) :
    HermTestFun sz n (fun M => ∑ i ∈ s, Φ i M) := by
  refine ⟨fun M hM => ContDiffAt.sum fun i hi => (h i hi).contDiffAt M hM, ?_⟩
  choose! C hC using fun i (hi : i ∈ s) => (h i hi).bdd₀
  refine ⟨∑ i ∈ s, C i, fun M hM => ?_⟩
  refine le_trans (norm_sum_le _ _) ?_
  exact Finset.sum_le_sum fun i hi => hC i hi M hM

theorem testFun_linComb {ι : Type*} [Fintype ι] (q : ι → ℂ)
    {Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (h : ∀ i, HermTestFun sz n (Φ i)) :
    HermTestFun sz n (fun M => ∑ i : ι, q i * Φ i M) :=
  azumaProxy_testFun_sum Finset.univ (Φ := fun i M => q i • Φ i M) fun i _ => testFun_const_smul (h i) (q i)

end Ports

/-! ## 2. Target: `azumaSubGN` -/

section Azuma

variable {d : ℕ} (sz : Sizes d)

/-- The directional derivative along the real line `y ↦ M + y X` at `0` is `fderiv ℝ Ψ M X`, for
`Ψ` differentiable at `M` (copy of the private `StepDecompN_hasDerivAt_dir`). -/
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

/-- `linTr` at the direction `(-I) • A` reads the imaginary part of `trace (A * X)` (copy of the
private `StepDecompN_linTr_neg_I_smul`). -/
private theorem azumaProxy_linTr_neg_I_smul (n : ℕ)
    (A X : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    linTr n ((-Complex.I) • A) X = (Matrix.trace (A * X)).im := by
  unfold linTr
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  ring

/-- The coordinate matrix of the slice is the coordinate matrix of the coordinate (copy of the
private `QVForm_seqXmat_single`, `Path/QVIdentity.lean:264`). -/
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

/-- The zero function is conditionally sub-Gaussian with every proxy (the check-section
`GridGoodNCheck.subG_zero` of RBM2D, for a general `sz`). -/
private theorem azumaProxy_subG_zero (j : ℕ) (c : ℝ≥0) :
    HasCondSubgaussianMGF (filt sz j) ((filt sz).le j) (fun _ => (0 : ℝ)) c (pathP sz) := by
  unfold HasCondSubgaussianMGF
  refine ⟨by simp, ?_⟩
  filter_upwards with ω t
  simp only [mgf, mul_zero, Real.exp_zero, integral_const, smul_eq_mul, mul_one]
  have h1 : (condExpKernel (pathP sz) (filt sz j) ω).real Set.univ = 1 := by simp
  rw [h1]
  exact Real.one_le_exp (by positivity)

/-- **Target `azumaSubGN`** (the merged pin `AzumaSubGN`, `Induction/GridAssemblyN.lean:122`,
unchanged): for a finite family `Φ` in the Hermitian test class, weights `κ`, a stopping family
`{j < τ} ∈ F_j` on which the grid state lies in `G j`, and `Q` majorising
`Δ Σ_c gvar_c ‖Σ_b κ_b ∂_c Φ_b(M)‖²` on the Hermitian matrices of `G j`, the stopped combination
`1_{j<τ} Σ_b κ_b Z_b` of the first-chaos parts is conditionally sub-Gaussian with proxy `Q` (real
and imaginary parts).  Route: for a nonempty label set `Σ_b κ_b Z_b = stepZCN` of the family `Φ`
with the kernel `(b, a) ↦ κ_a`, the variance identity
`linTrVar (AbCN) ≤ Σ_c gvar_c ‖Σ_b κ_b ∂_c Φ_b‖²` (and the same for `(-I) • AbCN`) and
`stepDecompCN_Z_subG` (merged, `hasCondSubgaussianMGF_linear`, `Path/Markov.lean:636`); for an
empty label set the increment is `0`.  Port of RBM2D `azumaSubGN` (`AzumaProxyN.lean:279` at
`c9a24cf`); RBM1D `hqv_of_vC` (`Gauss/GridAssembly.lean:201`). -/
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

/-! ## 3. Target: `0 ∈ GoodSetN` at `u = 0` (the initial grid state `H_0 = 0`)

At `u = 0` the flow value is `z_0 = E + m`, the grid state is `H = 0`, and `G_0 = M`: the loops are
the initial loops, `𝓛_{0,I}(0) = W^{-d(|I|-1)} ∏ m(σ_i) 1(all labels equal)`, which is the `M`-loop
and (`KLK_isKLoop`, `(eq:initial_K)`) `𝒦_{0,I}` for every well-formed `I` of length `≥ 1`.  Hence
every clause of `GoodSetN` that contains `𝓛 - 𝒦` holds with value `0`; the clauses with `𝓛`
alone vanish at two distinct labels; the pair form `𝓔⊗𝓔` has one term per cut. -/

section Member

variable {d : ℕ}

/-- The scalar of a signed Green factor at `z_0` is `m(σ)` (RBM2D `NonAltGood_initialGreenScalar`,
`Induction/NonAltGood.lean:575` at `c9a24cf`, with the merged `mSigma`, `mE_mul`). -/
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

/-- A label word that is not constant has an unequal adjacent pair (RBM2D
`NonAltGood_adjacentMismatch`, `:591`). -/
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

/-- `adjacentBlockWeight` in the form of the `M`-loop (RBM2D `NonAltGood_adjacentBlockWeight`, `:611`):
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

/-- `‖adjacentBlockWeight‖ ≤ ((W^{-1})^d)^{|as| - 1}` (RBM2D `NonAltGood_norm_adjacentBlockWeight_le`,
`:637`). -/
private theorem azumaProxy_norm_adjacentBlockWeight_le (L W : ℕ) (as : List (Zd d L)) :
    ‖adjacentBlockWeight d L W as‖ ≤ (((W : ℝ)⁻¹) ^ d) ^ (as.length - 1) := by
  induction as with
  | nil => simp [adjacentBlockWeight]
  | cons a as ih =>
      cases as with
      | nil => simp [adjacentBlockWeight]
      | cons b bs =>
          have h1 : ‖(if a = b then (W : ℂ)⁻¹ ^ d else 0)‖ ≤ ((W : ℝ)⁻¹) ^ d := by
            split_ifs
            · simp
            · simp only [norm_zero]; positivity
          simp only [adjacentBlockWeight, norm_mul, List.length_cons] at ih ⊢
          calc ‖(if a = b then (W : ℂ)⁻¹ ^ d else 0)‖ * ‖adjacentBlockWeight d L W (b :: bs)‖
              ≤ ((W : ℝ)⁻¹) ^ d * (((W : ℝ)⁻¹) ^ d) ^ (bs.length + 1 - 1) :=
                mul_le_mul h1 (by simpa using ih) (norm_nonneg _) (by positivity)
            _ = _ := by
                have : bs.length + 1 + 1 - 1 = (bs.length + 1 - 1) + 1 := by omega
                rw [this, pow_succ]; ring

private theorem azumaProxy_norm_prod_le_one {ι : Type*} (l : List ι) (f : ι → ℂ)
    (h : ∀ p ∈ l, ‖f p‖ ≤ 1) : ‖(l.map f).prod‖ ≤ 1 := by
  induction l with
  | nil => simp
  | cons p l ih =>
      simp only [List.map_cons, List.prod_cons, norm_mul]
      calc ‖f p‖ * ‖(l.map f).prod‖ ≤ 1 * 1 :=
            mul_le_mul (h p (by simp)) (ih fun q hq => h q (by simp [hq])) (norm_nonneg _)
              zero_le_one
        _ = 1 := one_mul 1

/-- The value of a loop at `H = 0`, `u = 0`: `(∏ m(σ_i)) · adjacentBlockWeight` (merged
`initialLoopValue_nonempty`, `Gauss/LoopGenerator.lean:572`; RBM2D `NonAltGood_gloop_zero_eq`). -/
private theorem azumaProxy_loopL_zero_eq (L W : ℕ) [NeZero L] [NeZero W] {E : ℝ} (hE : |E| < 2)
    (I : LoopIdx (Zd d L)) (hI : I.WF) (a : Zd d L) (as : List (Zd d L)) (ha : I.a = a :: as) :
    loopL d L W (blockMat d L W (0 : Matrix (Idx d L W) (Idx d L W) ℂ)) (zt E 0) I =
      ((I.σ.zip I.a).map fun p => initialGreenScalar E p.1).prod *
        adjacentBlockWeight d L W (a :: as) := by
  have hb := blockMat_zero d L W
  have hg : loopL d L W 0 (zt E 0) I = initialLoopValue d L W E I := by
    simp [initialLoopValue, zt]
  rw [hb, hg, initialLoopValue_nonempty d L W hE I hI a as ha]

/-- At `H = 0`, `u = 0`: `|𝓛_I| ≤ ((W^{-1})^d)^{|I|-1}` (`|m| = 1`). -/
private theorem azumaProxy_norm_loopL_zero_le (L W : ℕ) [NeZero L] [NeZero W] {E : ℝ} (hE : |E| < 2)
    (I : LoopIdx (Zd d L)) (hI : I.WF) (h1 : 1 ≤ I.length) :
    ‖loopL d L W (blockMat d L W (0 : Matrix (Idx d L W) (Idx d L W) ℂ)) (zt E 0) I‖ ≤
      (((W : ℝ)⁻¹) ^ d) ^ (I.length - 1) := by
  obtain ⟨σ, as0⟩ := I
  cases as0 with
  | nil => simp [LoopIdx.length] at h1
  | cons a as =>
    rw [azumaProxy_loopL_zero_eq L W hE ⟨σ, a :: as⟩ hI a as rfl, norm_mul]
    have hprod : ‖((σ.zip (a :: as)).map fun p => initialGreenScalar E p.1).prod‖ ≤ 1 :=
      azumaProxy_norm_prod_le_one _ _ (fun p _ => by
        rw [azumaProxy_initialGreenScalar hE.le, norm_mSigma hE.le])
    have habw := azumaProxy_norm_adjacentBlockWeight_le (d := d) L W (a :: as)
    calc _ ≤ 1 * (((W : ℝ)⁻¹) ^ d) ^ ((a :: as).length - 1) :=
          mul_le_mul hprod habw (norm_nonneg _) zero_le_one
      _ = _ := by simp [LoopIdx.length]

/-- At `H = 0`, `u = 0`: a loop with two distinct labels vanishes (`E_a E_b = 0`, `a ≠ b`). -/
private theorem azumaProxy_loopL_zero_of_ne (L W : ℕ) [NeZero L] [NeZero W] {E : ℝ} (hE : |E| < 2)
    (I : LoopIdx (Zd d L)) (hI : I.WF) {x y : Zd d L} (hx : x ∈ I.a) (hy : y ∈ I.a)
    (hxy : x ≠ y) :
    loopL d L W (blockMat d L W (0 : Matrix (Idx d L W) (Idx d L W) ℂ)) (zt E 0) I = 0 := by
  obtain ⟨σ, as0⟩ := I
  cases as0 with
  | nil => simp at hx
  | cons a as =>
    rw [azumaProxy_loopL_zero_eq L W hE ⟨σ, a :: as⟩ hI a as rfl,
      azumaProxy_adjacentBlockWeight]
    have hc : ¬ ∀ x ∈ a :: as, ∀ y ∈ a :: as, x = y := fun h => hxy (h x hx y hy)
    simp only [eq_false hc, ↓reduceIte, mul_zero]

/-- **`𝓛_0 = 𝒦_0`** at `H_0 = 0` (`(eq:initial_K)`, `3_5`; RBM2D `NonAltGood_gloop_zero`, `:671`):
every well-formed loop of length `≥ 1` at `z_0 = E + m` equals `𝒦_{0,I}` (merged `KLK_isKLoop`,
`Loop/KLTreeDeriv.lean:1049`, and `KLK_one`). -/
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

/-- `(𝓛 - 𝒦)_{0,I}(0) = 0` for every well-formed loop of length `≥ 1` (RBM2D `NonAltGood_LKf_zero`,
`:752`). -/
private theorem azumaProxy_STLKIM_zero {E : ℝ} (hE : |E| < 2) (I : LoopIdx (Zd d (sz.L n)))
    (hI : I.WF) (h1 : 1 ≤ I.length) :
    sz.STLKIM n E 0 (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) I = 0 := by
  unfold Sizes.STLKIM Sizes.STLIM
  rw [azumaProxy_loopL_zero_eq_KLK (sz.L n) (sz.W n) (sz.three_le_L n) (sz.W_pos n) (sz.lam n) hE I
    hI h1, sub_self]

/-- `tr (G̃_0(σ) E_a) = 0` at `H = 0`, `u = 0` (RBM2D `NonAltGood_avgErr_zero`, `:778`). -/
private theorem azumaProxy_STavgErrM_zero {E : ℝ} (hE : |E| < 2) (σ : Bool) (a : Zd d (sz.L n)) :
    sz.STavgErrM n E 0 (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) σ a
      = 0 := by
  have h := azumaProxy_STLKIM_zero sz n hE ⟨[σ], [a]⟩ (by simp [LoopIdx.WF])
    (by simp [LoopIdx.length])
  unfold Sizes.STLKIM at h
  rw [KLK_one, sub_eq_zero] at h
  unfold Sizes.STavgErrM
  rw [h, sub_self]

/-- `STksimLKM = 0` at `H = 0`, `u = 0`: every summand has the factor `(𝓛-𝒦)_0 = 0` (RBM2D
`NonAltGood_ksimLK_zero`, `:784`). -/
private theorem azumaProxy_STksimLKM_zero {E : ℝ} (hE : |E| < 2) (l : ℕ)
    (I : LoopIdx (Zd d (sz.L n))) (hI : I.WF) :
    sz.STksimLKM n E 0 (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) l I
      = 0 := by
  unfold Sizes.STksimLKM
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun l' hl' =>
    Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_)
  simp only [Finset.mem_Icc, Finset.mem_Ioc] at hk hl'
  have hLa := azumaProxy_STLKIM_zero sz n hE (I.cutGlueL k l' a)
    (LoopIdx.wf_cutGlueL I a hI hk.1 hl'.1 hl'.2) (by
      rw [LoopIdx.length_cutGlueL I a hk.1 hl'.1 hl'.2]; omega)
  have hRb := azumaProxy_STLKIM_zero sz n hE (I.cutGlueR k l' b)
    (LoopIdx.wf_cutGlueR I b hI hk.1 hl'.1 hl'.2) (by
      rw [LoopIdx.length_cutGlueR I b hk.1 hl'.1 hl'.2]; omega)
  simp [hLa, hRb]

private theorem azumaProxy_STelklkM_zero {E : ℝ} (hE : |E| < 2) (I : LoopIdx (Zd d (sz.L n)))
    (hI : I.WF) :
    sz.STelklkM n E 0 (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) I
      = 0 := by
  unfold Sizes.STelklkM
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun l' hl' =>
    Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_)
  simp only [Finset.mem_Icc, Finset.mem_Ioc] at hk hl'
  have hLa := azumaProxy_STLKIM_zero sz n hE (I.cutGlueL k l' a)
    (LoopIdx.wf_cutGlueL I a hI hk.1 hl'.1 hl'.2) (by
      rw [LoopIdx.length_cutGlueL I a hk.1 hl'.1 hl'.2]; omega)
  simp [hLa]

private theorem azumaProxy_STegtM_zero {E : ℝ} (hE : |E| < 2) (I : LoopIdx (Zd d (sz.L n))) :
    sz.STegtM n E 0 (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) I = 0 := by
  unfold Sizes.STegtM
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun a _ =>
    Finset.sum_eq_zero fun b _ => ?_)
  simp [azumaProxy_STavgErrM_zero sz n hE]

/-- `loopFine - 𝒦 = 0` at `H = 0`, `u = 0`, for loops of length `m ≥ 1`. -/
private theorem azumaProxy_loopFine_sub_STKloop {E : ℝ} (hE : |E| < 2) {m : ℕ} (hm : 1 ≤ m)
    (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) :
    loopFine d (sz.L n) (sz.W n)
        (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (zt E 0) σ a
      - sz.STKloop n E 0 σ a = 0 := by
  unfold loopFine Sizes.STKloop
  rw [loopM_eq_loopL]
  exact sub_eq_zero.2 (azumaProxy_loopL_zero_eq_KLK (sz.L n) (sz.W n) (sz.three_le_L n)
    (sz.W_pos n) (sz.lam n) hE (loopOf σ a) (by simp [loopOf, LoopIdx.WF])
    (by simpa [loopOf, LoopIdx.length] using hm))

/-- `Ξ̂^{(𝓛-𝒦)}_m(0; u = 0) = 1` for `m ≥ 1`: the maximum of `|𝓛 - 𝒦|` is `0`. -/
private theorem azumaProxy_STXiLKM_zero {E : ℝ} (hE : |E| < 2) {m : ℕ} (hm : 1 ≤ m) :
    sz.STXiLKM n E 0 m
      (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) = 1 := by
  have hmax : sz.STmaxLKM n E 0 m
      (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) = 0 := by
    unfold Sizes.STmaxLKM
    refine le_antisymm (Finset.sup'_le _ _ fun p _ => ?_) ?_
    · rw [azumaProxy_loopFine_sub_STKloop sz n hE hm, norm_zero]
    · exact Finset.le_sup'_of_le _ (Finset.mem_univ ((fun _ => true), fun _ => (0 : Zd d (sz.L n))))
        (norm_nonneg _)
  unfold Sizes.STXiLKM
  rw [hmax, zero_div, add_zero]

/-- `|0|_∞ = 0`. -/
private theorem azumaProxy_zdistInf_zero (L : ℕ) : zdistInf d L (0 : Zd d L) = 0 := by
  unfold zdistInf
  simp

/-- A positive spread means two different labels (the contrapositive: a constant label vector has
`diam_∞ = 0`). -/
private theorem azumaProxy_exists_ne {L k : ℕ} (a : Fin k → Zd d L)
    (h : 0 < Sizes.STdiamInf a) : ∃ i j : Fin k, a i ≠ a j := by
  by_contra hcon
  push Not at hcon
  have h0 : Sizes.STdiamInf a = 0 := by
    unfold Sizes.STdiamInf
    refine Nat.eq_zero_of_le_zero (Finset.sup_le fun p _ => ?_)
    rw [hcon p.1 p.2, sub_self]
    exact le_of_eq (azumaProxy_zdistInf_zero L)
  omega

/-- The far condition `ℓ_0 W^{τ'} ≤ diam_∞ a` forces two different labels (`ℓ_0 ≥ 1`, `W ≥ 1`). -/
private theorem azumaProxy_far_exists_ne {L k : ℕ} (hL : 1 ≤ L) (g τ' : ℝ) {W : ℕ} (hW : 0 < W)
    (a : Fin k → Zd d L) (hfar : ellT L g 0 * (W : ℝ) ^ τ' ≤ (Sizes.STdiamInf a : ℝ)) :
    ∃ i j : Fin k, a i ≠ a j := by
  have hL' : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hpos : 0 < ellT L g 0 * (W : ℝ) ^ τ' :=
    mul_pos (ellT_pos hL') (Real.rpow_pos_of_pos (by exact_mod_cast hW) _)
  have h0 : (0 : ℝ) < (Sizes.STdiamInf a : ℝ) := lt_of_lt_of_le hpos hfar
  exact azumaProxy_exists_ne a (by exact_mod_cast h0)

/-- Every label of `a` and of `a'` is a label of the `(2m+2)`-loop at every cut (RBM2D
`NonAltGood_mem_eeLoop`, `:866`; merged `mem_eeLoop_left/right`, `Induction/DecayLoopB.lean:475`). -/
private theorem azumaProxy_mem_eeLoop {L m : ℕ} (σ : Fin m → Bool) (a a' : Fin m → Zd d L) (k : ℕ)
    (b b' : Zd d L) (i : Fin (m + m)) :
    Fin.append a a' i ∈ (Sizes.STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b').a := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [Fin.append_left]
    exact mem_eeLoop_left _ _ _ _ _ _ (List.mem_ofFn.2 ⟨i, rfl⟩)
  · rw [Fin.append_right]
    exact mem_eeLoop_right _ _ _ _ _ _ (List.mem_ofFn.2 ⟨i, rfl⟩)

/-- `‖S^{(B)}_{cc}‖ = (1 + 2 d g²)⁻¹`. -/
private theorem azumaProxy_norm_SB_self (L : ℕ) [NeZero L] (g : ℝ) (c : Zd d L) :
    ‖SB d L g c c‖ = (1 + 2 * (d : ℝ) * g ^ 2)⁻¹ := by
  rw [SB_apply, sub_self]
  simp only [sbKernel, ↓reduceIte]
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]

/-- The pair form vanishes at `H = 0`, `u = 0` as soon as two of the labels of `a, a'` differ: every
`(2k+2)`-loop of `𝓔⊗𝓔` contains all of them. -/
private theorem azumaProxy_STeeM_zero_of_far {E : ℝ} (hE : |E| < 2) {k : ℕ} (σ : Fin k → Bool)
    (a a' : Fin k → Zd d (sz.L n)) {i j : Fin (k + k)}
    (hij : Fin.append a a' i ≠ Fin.append a a' j) :
    sz.STeeM n E 0 (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) σ a a'
      = 0 := by
  unfold Sizes.STeeM
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun k' hk' => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun b' _ => ?_)
  simp only [Finset.mem_Icc] at hk'
  have hwf := eeLoop_WF (List.ofFn σ) (List.ofFn a) (List.ofFn a') hk'.1
    (by simpa using hk'.2) (by simp) (by simp) b b'
  have h0 := azumaProxy_loopL_zero_of_ne (sz.L n) (sz.W n) hE _ hwf
    (azumaProxy_mem_eeLoop σ a a' k' b b' i) (azumaProxy_mem_eeLoop σ a a' k' b b' j) hij
  unfold Sizes.STLIM
  rw [h0, mul_zero]

/-- The pair form at `H = 0`, `u = 0`: the loop of `𝓔⊗𝓔` is nonzero only if `b = b' =` a label of
`a`, so each cut contributes one term `|S_{cc}| |𝓛_{2k+2}| ≤ S_{cc} ((W^{-1})^d)^{2k+1}` (RBM2D
`NonAltGood_norm_eeN_zero_le`, `:885`, with `S_{cc} = (1 + 2 d g²)⁻¹` in place of `1/5`). -/
private theorem azumaProxy_norm_STeeM_zero_le {E : ℝ} (hE : |E| < 2) {k : ℕ} (hk : 1 ≤ k)
    (σ : Fin k → Bool) (a a' : Fin k → Zd d (sz.L n)) :
    ‖sz.STeeM n E 0 (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) σ a a'‖ ≤
      ((sz.W n : ℕ) : ℝ) ^ d * ((k : ℝ) * ((1 + 2 * (d : ℝ) * (sz.lam n) ^ 2)⁻¹ *
        ((((sz.W n : ℕ) : ℝ)⁻¹ ^ d) ^ (2 * k + 1)))) := by
  have hW2 : ‖(((sz.W n : ℕ) : ℂ)) ^ d‖ = ((sz.W n : ℕ) : ℝ) ^ d := by simp
  unfold Sizes.STeeM
  rw [norm_mul, hW2]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans ?_
  set c : Zd d (sz.L n) := a ⟨0, by omega⟩ with hc
  have hB : ∀ k' ∈ Finset.Icc 1 k, ‖∑ b : Zd d (sz.L n), ∑ b' : Zd d (sz.L n),
      SB d (sz.L n) (sz.lam n) b b' *
      sz.STLIM n E 0 (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
        (Sizes.STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k' b b')‖ ≤
      (1 + 2 * (d : ℝ) * (sz.lam n) ^ 2)⁻¹ * ((((sz.W n : ℕ) : ℝ)⁻¹ ^ d) ^ (2 * k + 1)) := by
    intro k' hk'
    simp only [Finset.mem_Icc] at hk'
    have hwf : ∀ b b' : Zd d (sz.L n),
        (Sizes.STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k' b b').WF := fun b b' =>
      eeLoop_WF (List.ofFn σ) (List.ofFn a) (List.ofFn a') hk'.1 (by simpa using hk'.2)
        (by simp) (by simp) b b'
    have hlenE : ∀ b b' : Zd d (sz.L n),
        (Sizes.STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k' b b').length = 2 * k + 2 :=
      fun b b' => by
        have := length_eeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') (k := k')
          (by simp; omega) (by simp) b b'
        rw [List.length_ofFn] at this
        exact this
    have hval : ∀ b b' : Zd d (sz.L n), ‖sz.STLIM n E 0
        (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
        (Sizes.STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k' b b')‖ ≤
        (((sz.W n : ℕ) : ℝ)⁻¹ ^ d) ^ (2 * k + 1) := fun b b' => by
      have h1 := azumaProxy_norm_loopL_zero_le (sz.L n) (sz.W n) hE
        (Sizes.STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k' b b') (hwf b b')
        (by rw [hlenE]; omega)
      rw [hlenE] at h1
      unfold Sizes.STLIM
      have e : 2 * k + 2 - 1 = 2 * k + 1 := by omega
      rw [e] at h1
      exact h1
    have hmemb : ∀ b b' : Zd d (sz.L n),
        b ∈ (Sizes.STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k' b b').a :=
      fun b b' => by simp [Sizes.STeeLoop]
    have hmemb' : ∀ b b' : Zd d (sz.L n),
        b' ∈ (Sizes.STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k' b b').a :=
      fun b b' => by simp [Sizes.STeeLoop]
    have hmemc : ∀ b b' : Zd d (sz.L n),
        c ∈ (Sizes.STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k' b b').a :=
      fun b b' => mem_eeLoop_left _ _ _ _ _ _ (List.mem_ofFn.2 ⟨⟨0, by omega⟩, rfl⟩)
    have hzero : ∀ b b' : Zd d (sz.L n), ¬ (b = c ∧ b' = c) →
        sz.STLIM n E 0 (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
          (Sizes.STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k' b b') = 0 := by
      intro b b' hne
      unfold Sizes.STLIM
      by_cases hb : b = c
      · exact azumaProxy_loopL_zero_of_ne (sz.L n) (sz.W n) hE _ (hwf b b') (hmemb' b b')
          (hmemc b b') (fun h => hne ⟨hb, h⟩)
      · exact azumaProxy_loopL_zero_of_ne (sz.L n) (sz.W n) hE _ (hwf b b') (hmemb b b')
          (hmemc b b') hb
    have hsum : ∑ b : Zd d (sz.L n), ∑ b' : Zd d (sz.L n),
        SB d (sz.L n) (sz.lam n) b b' *
        sz.STLIM n E 0 (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
          (Sizes.STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k' b b') =
        SB d (sz.L n) (sz.lam n) c c *
        sz.STLIM n E 0 (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
          (Sizes.STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k' c c) := by
      rw [Finset.sum_eq_single c]
      · rw [Finset.sum_eq_single c]
        · intro b' _ hb'
          rw [hzero c b' (fun h => hb' h.2), mul_zero]
        · intro h; exact absurd (Finset.mem_univ c) h
      · intro b _ hb
        refine Finset.sum_eq_zero fun b' _ => ?_
        rw [hzero b b' (fun h => hb h.1), mul_zero]
      · intro h; exact absurd (Finset.mem_univ c) h
    rw [hsum, norm_mul, azumaProxy_norm_SB_self]
    exact mul_le_mul_of_nonneg_left (hval c c) (by positivity)
  calc ∑ k' ∈ Finset.Icc 1 k, ‖∑ b : Zd d (sz.L n), ∑ b' : Zd d (sz.L n),
        SB d (sz.L n) (sz.lam n) b b' *
        sz.STLIM n E 0 (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
          (Sizes.STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k' b b')‖
      ≤ ∑ k' ∈ Finset.Icc 1 k, (1 + 2 * (d : ℝ) * (sz.lam n) ^ 2)⁻¹ *
          ((((sz.W n : ℕ) : ℝ)⁻¹ ^ d) ^ (2 * k + 1)) := Finset.sum_le_sum hB
    _ = (k : ℝ) * ((1 + 2 * (d : ℝ) * (sz.lam n) ^ 2)⁻¹ *
          ((((sz.W n : ℕ) : ℝ)⁻¹ ^ d) ^ (2 * k + 1))) := by
        simp [Finset.sum_const, Nat.card_Icc]

/-- `0 ≤ W^{-d} B_{0,0}`: the control `Bctl` is nonnegative at `u = 0`. -/
private theorem azumaProxy_Bctl_nonneg : 0 ≤ sz.Bctl n 0 := by
  unfold Sizes.Bctl Bparam
  positivity

/-- **`0 ∈ GoodSetN` at `u = 0`** (supervisor 19:48 O3 (2), DECISIONS §45; RBM2D
`zero_mem_goodSetN`, `Induction/NonAltGood.lean:996` at `c9a24cf`, rewritten for `GoodSetN` of
`d ≥ 3`, `GridGoodN.lean:124`): the initial grid state `H_0 = 0` at the spectral time `u_0 = 0`
(`G_0 = M`), for every size index `n`, `|E| < 2`, `k ≥ 1`, every `Φ τ' D'`, and levels `Γ Λ` with

* `0 ≤ Γ`, `1 ≤ Γ Φ` (the clause (G2): `Ξ̂^{(𝓛-𝒦)}_m(0) = 1`, `1 ≤ m < k`; the `ℰ`-levels
  (D1)-(D3) have the value `0`), and
* the pair-form level (D4): `k · S_{cc} · η_0 ≤ Γ² Λ · b^{2k}`, where
  `S_{cc} = (1 + 2 d g²)⁻¹` (the diagonal of `S^{(B)}`), `η_0 = Im m` and
  `b = (g² + 1)⁻¹ + L^{-d}` is `Bparam d L g 0 0` (`W^{-d} b` is `Bctl n 0`; the power `W^{-2kd}`
  cancels).  Sufficient: `Γ² Λ ≥ k (1 + g²)^{2k}` (`zero_mem_goodSetN_of_levels`).

At `u = 0` the loops of `M = 0` are the initial loops: `𝓛_0 = 𝒦_0` for well-formed loops of length
`≥ 1` (`(eq:initial_K)`, merged `KLK_isKLoop`), so every clause with `𝓛 - 𝒦` has value `0`; the
clauses with `𝓛` and the pair form vanish at two distinct labels (`E_a E_b = 0`); at equal labels
`𝓔⊗𝓔` has one term per cut.  RBM2D's condition `k/5 ≤ Γ² Λ` becomes the `g`-dependent (D4)
level above, which the unit levels `Γ = Λ = Φ = 1` need not satisfy (at `sz0`, `n = 0`, `E = 1/2`,
`k = 3` the threshold `k S_{cc} η_0 / b^{2k}` is `≈ 2.65 > 1`; paper-delta candidate `T2159a`).
Deterministic; no hypothesis of another gate. -/
theorem zero_mem_goodSetN {E : ℝ} (hE : |E| < 2) {k : ℕ} (hk : 1 ≤ k)
    {Γ Λ Φ τ' D' : ℝ} (hΓ : 0 ≤ Γ) (hΓΦ : 1 ≤ Γ * Φ)
    (hee : (k : ℝ) * ((1 + 2 * (d : ℝ) * (sz.lam n) ^ 2)⁻¹ * etaT E 0) ≤
      Γ * (Γ * Λ) * (Bparam d (sz.L n) (sz.lam n) 0 0) ^ (2 * k)) :
    (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) ∈
      sz.GoodSetN n E 0 k Γ Λ Φ τ' D' := by
  have hL3 := sz.three_le_L n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hη : 0 < etaT E 0 := etaT_pos hE (by norm_num)
  have hΦ0 : 0 ≤ Γ * Φ := by linarith
  have hD0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D') := Real.rpow_nonneg hW0.le _
  have hB0 : 0 ≤ sz.Bctl n 0 := azumaProxy_Bctl_nonneg sz n
  have hRHS : 0 ≤ (sz.Bctl n 0) ^ k / etaT E 0 := div_nonneg (pow_nonneg hB0 _) hη.le
  have hwfo : ∀ {m : ℕ} (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)), (loopOf σ a).WF :=
    fun σ a => by simp [loopOf, LoopIdx.WF]
  refine ⟨Matrix.isHermitian_zero, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (G2)
    intro m hm1 hmk
    rw [azumaProxy_STXiLKM_zero sz n hE hm1]
    exact hΓΦ
  · -- (Dec)
    intro j hj1 hj2 σ a hfar
    obtain ⟨i, i', hne⟩ := azumaProxy_far_exists_ne (by omega) (sz.lam n) τ' (sz.W_pos n) a hfar
    have hz : loopFine d (sz.L n) (sz.W n)
        (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (zt E 0) σ a = 0 := by
      unfold loopFine
      rw [loopM_eq_loopL]
      exact azumaProxy_loopL_zero_of_ne (sz.L n) (sz.W n) hE (loopOf σ a) (hwfo σ a)
        (x := a i) (y := a i') (by simp [loopOf]) (by simp [loopOf]) hne
    rw [azumaProxy_loopFine_sub_STKloop sz n hE hj1, hz, norm_zero, add_zero]
    exact hD0
  · -- (D1)
    intro l hl3 hlk σ a
    rw [azumaProxy_STksimLKM_zero sz n hE l (loopOf σ a) (hwfo σ a), norm_zero]
    exact mul_nonneg (mul_nonneg hΓ hΦ0) hRHS
  · -- (D2)
    intro σ a
    rw [azumaProxy_STelklkM_zero sz n hE (loopOf σ a) (hwfo σ a), norm_zero]
    exact mul_nonneg (mul_nonneg hΓ (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))) hRHS
  · -- (D3)
    intro σ a
    rw [azumaProxy_STegtM_zero sz n hE (loopOf σ a), norm_zero]
    exact mul_nonneg (mul_nonneg hΓ hΦ0) hRHS
  · -- (D4)
    intro σ a a'
    refine (azumaProxy_norm_STeeM_zero_le sz n hE hk σ a a').trans ?_
    unfold Sizes.Bctl
    set x : ℝ := ((sz.W n : ℕ) : ℝ) ^ d with hx
    set S : ℝ := (1 + 2 * (d : ℝ) * (sz.lam n) ^ 2)⁻¹ with hS
    set b : ℝ := Bparam d (sz.L n) (sz.lam n) 0 0 with hb
    set η : ℝ := etaT E 0 with hηdef
    have hx0 : 0 < x := by positivity
    have hxi : ((sz.W n : ℕ) : ℝ)⁻¹ ^ d = x⁻¹ := by rw [hx, inv_pow]
    rw [hxi]
    set P : ℝ := (x⁻¹) ^ (2 * k) with hP
    have hP0 : 0 < P := by positivity
    have e1 : x * ((k : ℝ) * (S * (x⁻¹) ^ (2 * k + 1))) = (k : ℝ) * S * P := by
      have hxx : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0.ne'
      calc _ = (k : ℝ) * S * P * (x * x⁻¹) := by rw [hP]; ring
        _ = _ := by rw [hxx, mul_one]
    have e2 : (x⁻¹ * b) ^ (2 * k) = P * b ^ (2 * k) := by rw [mul_pow]
    rw [e1, e2, ← mul_div_assoc, le_div_iff₀ hη]
    have h3 := mul_le_mul_of_nonneg_right hee hP0.le
    nlinarith [h3]
  · -- (Va)
    intro σ a hfar
    rw [azumaProxy_STelklkM_zero sz n hE (loopOf σ a) (hwfo σ a),
      azumaProxy_STegtM_zero sz n hE (loopOf σ a)]
    have : ∑ l ∈ Finset.Icc 3 k, sz.STksimLKM n E 0
        (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) l (loopOf σ a) = 0 :=
      Finset.sum_eq_zero fun l _ => azumaProxy_STksimLKM_zero sz n hE l (loopOf σ a) (hwfo σ a)
    rw [this]
    simpa using hD0
  · -- (Vb)
    intro σ a a' hfar
    obtain ⟨i, j, hne⟩ := azumaProxy_far_exists_ne (by omega) (sz.lam n) τ' (sz.W_pos n)
      (Fin.append a a') hfar
    rw [azumaProxy_STeeM_zero_of_far sz n hE σ a a' hne, norm_zero]
    exact hD0

/-- **The (D4) level from `Γ² Λ ≥ k (1 + g²)^{2k}`**: `η_0 ≤ 1`, `S_{cc} ≤ 1`, `b ≥ (1 + g²)⁻¹`. -/
theorem azumaProxy_hee_of_levels {E : ℝ} (hE : |E| < 2) {k : ℕ} {Γ Λ : ℝ}
    (hΓΛ : (k : ℝ) * (1 + (sz.lam n) ^ 2) ^ (2 * k) ≤ Γ * (Γ * Λ)) :
    (k : ℝ) * ((1 + 2 * (d : ℝ) * (sz.lam n) ^ 2)⁻¹ * etaT E 0) ≤
      Γ * (Γ * Λ) * (Bparam d (sz.L n) (sz.lam n) 0 0) ^ (2 * k) := by
  set q : ℝ := 1 + (sz.lam n) ^ 2 with hq
  have hq0 : 0 < q := by positivity
  have hη0 : 0 < etaT E 0 := etaT_pos hE (by norm_num)
  have hη1 : etaT E 0 ≤ 1 := by
    have h := Complex.abs_im_le_norm (mE E)
    rw [norm_mE hE.le] at h
    unfold etaT
    simpa using (le_abs_self _).trans h
  have hS0 : 0 ≤ (1 + 2 * (d : ℝ) * (sz.lam n) ^ 2)⁻¹ := by positivity
  have hS1 : (1 + 2 * (d : ℝ) * (sz.lam n) ^ 2)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (sz.lam n), (Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
  have hb : Bparam d (sz.L n) (sz.lam n) 0 0 = (q)⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ := by
    unfold Bparam
    simp [hq, add_comm]
  have hbq : q⁻¹ ≤ Bparam d (sz.L n) (sz.lam n) 0 0 := by
    rw [hb]; exact le_add_of_nonneg_right (by positivity)
  have hbk : (q⁻¹) ^ (2 * k) ≤ (Bparam d (sz.L n) (sz.lam n) 0 0) ^ (2 * k) :=
    pow_le_pow_left₀ (by positivity) hbq _
  have hqk : (q ^ (2 * k)) * (q⁻¹) ^ (2 * k) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hq0.ne', one_pow]
  have hG0 : 0 ≤ Γ * (Γ * Λ) := le_trans (by positivity) hΓΛ
  have h1 : (k : ℝ) * ((1 + 2 * (d : ℝ) * (sz.lam n) ^ 2)⁻¹ * etaT E 0) ≤ (k : ℝ) := by
    have : (1 + 2 * (d : ℝ) * (sz.lam n) ^ 2)⁻¹ * etaT E 0 ≤ 1 := by
      calc _ ≤ 1 * 1 := mul_le_mul hS1 hη1 hη0.le zero_le_one
        _ = 1 := one_mul 1
    calc _ ≤ (k : ℝ) * 1 := mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
      _ = _ := mul_one _
  have h2 : (k : ℝ) ≤ Γ * (Γ * Λ) * (q⁻¹) ^ (2 * k) := by
    have := mul_le_mul_of_nonneg_right hΓΛ (by positivity : (0 : ℝ) ≤ (q⁻¹) ^ (2 * k))
    calc (k : ℝ) = (k : ℝ) * ((q ^ (2 * k)) * (q⁻¹) ^ (2 * k)) := by rw [hqk, mul_one]
      _ = (k : ℝ) * q ^ (2 * k) * (q⁻¹) ^ (2 * k) := by ring
      _ ≤ _ := this
  calc _ ≤ (k : ℝ) := h1
    _ ≤ Γ * (Γ * Λ) * (q⁻¹) ^ (2 * k) := h2
    _ ≤ _ := mul_le_mul_of_nonneg_left hbk hG0

/-- **A sufficient level condition** for `zero_mem_goodSetN`: `Γ² Λ ≥ k (1 + g²)^{2k}` (used at the
levels `Γ = 4`, `Λ = 3`, `Φ = 1` in `AzumaProxyNInst.zero_mem_goodSetN_instance`). -/
theorem zero_mem_goodSetN_of_levels {E : ℝ} (hE : |E| < 2) {k : ℕ} (hk : 1 ≤ k)
    {Γ Λ Φ τ' D' : ℝ} (hΓ : 0 ≤ Γ) (hΓΦ : 1 ≤ Γ * Φ)
    (hΓΛ : (k : ℝ) * (1 + (sz.lam n) ^ 2) ^ (2 * k) ≤ Γ * (Γ * Λ)) :
    (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) ∈
      sz.GoodSetN n E 0 k Γ Λ Φ τ' D' :=
  zero_mem_goodSetN sz n hE hk hΓ hΓΦ (azumaProxy_hee_of_levels sz n hE hΓΛ)

end MemberSz

end Member

/-! ## 4. The composition `AzumaSubGN ∘ loops ∘ GoodSetN ∘ goodExitTauN`

The two compositions of RBM2D `Induction/GridGoodN.lean:1104, 1134` (`azumaSubG_ugen`,
`azumaSubG_goodExit`, not in the merged `GridGoodN`), re-derived for `d ≥ 3` from the proved
`azumaSubGN`, the merged `hermTestFunLoopN` (test class) and `qvPropagatedN` (variance proxy). -/

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

/-- At `s n = 0` the grid walk starts at `H_0 = 0` (`H_{u_0} = √s X_0 = 0`; RBM2D
`pathH_zero_of_s_zero`, `Induction/GridGoodN.lean:1383`, not in the merged `GridGoodN`). -/
theorem azumaProxy_pathH_zero_of_s_zero (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hs : s n = 0)
    (ω : PathΩ sz) : pathH sz s t K n 0 ω = 0 := by
  simp [pathH, hs]

/-- **`SubGaussStopN` for `ZvecN` from the pin `AzumaSubGN`** (RBM2D `azumaSubG_ugen`,
`Induction/GridGoodN.lean:1104` at `c9a24cf`): for the loop family `Φ_b = 𝓛_{u_{j+1},σ,b}`
(`loopFamN`, in the test class by the merged `hermTestFunLoopN`), the propagator weights
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

/-- **(`AzumaSubGN` ∘ `GoodSetN` ∘ `goodExitTauN`)** (RBM2D `azumaSubG_goodExit`,
`Induction/GridGoodN.lean:1134` at `c9a24cf`): with `G j = GoodSetN …` and `τ = goodExitTauN`, the
membership hypothesis of `azumaProxy_subG_ugen` is `mem_of_lt_gridExitTauN` and its measurability
hypothesis is the merged `goodExitMeasN`; what remains is the deterministic majorant `hQ` on
`GoodSetN`. -/
theorem azumaProxy_subG_goodExit {E s v : ℕ → ℝ} {K : ℕ → ℕ} (h : AzumaSubGN sz s v K)
    (hE : ∀ n, |E n| < 2) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1)
    (n k : ℕ) (hk : 2 ≤ k) (σ : Fin k → Bool) (Γ Λ Φ : ℕ → ℝ) (τ' D' : ℝ) (m : ℕ)
    (hm : m ≤ K n) (a : Fin k → Zd d (sz.L n)) (j : ℕ) (hj : j < m) (Q : ℝ≥0)
    (hQ : ∀ M ∈ sz.GoodSetN n (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D',
      M.IsHermitian → gridStep s v K n * ((k : ℝ) * qvFormN sz n (E n)
        (gridTime s v K n (j + 1)) (gridTime s v K n m) σ M a) ≤ (Q : ℝ)) :
    SubGaussStopN sz (E n) σ (gridTime s v K n) (goodExitTauN sz E s v K k Γ Λ Φ τ' D' n)
      (fun j ω => ZvecN sz E s v K n j σ ω) m a j Q :=
  azumaProxy_subG_ugen sz h hE hs0 hsv hv1 n k hk σ (goodExitTauN sz E s v K k Γ Λ Φ τ' D' n)
    (fun j => sz.GoodSetN n (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D')
    (goodExitMeasN sz E s v K n k Γ Λ Φ τ' D') (fun ω j hj => mem_of_lt_gridExitTauN hj) m hm a j
    hj Q hQ

/-- The exit time of the grid walk from `G` is positive when `H_0 ∈ G 0` and the grid has a step
(`K n > 0`): with `0 ∈ GoodSetN … u_0` (`zero_mem_goodSetN`) and `s n = 0` the stopping time
`goodExitTauN` is `≥ 1` at every sample, so `{0 < τ}` is the whole space. -/
theorem azumaProxy_pos_gridExitTauN {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ}
    {G : ℕ → Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)}
    {ω : PathΩ sz} (hK : 0 < K n) (h0 : pathH sz s v K n 0 ω ∈ G 0) :
    0 < gridExitTauN sz s v K n G ω := by
  unfold gridExitTauN firstHit
  by_contra hle
  have hle' := Nat.le_of_not_lt hle
  obtain ⟨j, hj, hmem⟩ := (MeasureTheory.hittingBtwn_le_iff_of_lt (i := 0) hK).1 hle'
  have hj0 : j = 0 := by simpa using hj
  subst hj0
  have hnot : pathH sz s v K n 0 ω ∉ (G 0)ᶜ := fun h => h h0
  rw [Set.indicator_of_notMem hnot] at hmem
  norm_num at hmem

end Compose

/-! ## 5. The three-loop observable at a scalar matrix

Used for the nondegeneracy of the instance (section 6): at `M = y · 1` the Green functions are
scalar, `𝓛_{(+,-,+),(a,a,a)}(y 1) = W^{-2d} (y - z)⁻² (y - z̄)⁻¹`. -/

section ScalarLoop

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem azumaProxy_blockMat_scalar (c : ℂ) :
    blockMat d L W (c • (1 : Matrix (Idx d L W) (Idx d L W) ℂ))
      = c • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) := by
  ext i j
  simp [blockMat, Matrix.one_apply, (splitEquiv d L W).symm.injective.eq_iff]

private theorem azumaProxy_Gres_scalar_true (y z : ℂ) (h : y - z ≠ 0) :
    Gres (y • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) z true
      = (y - z)⁻¹ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) := by
  unfold Gres
  simp only [↓reduceIte]
  rw [← sub_smul, ring_inverse_smul_one h]

private theorem azumaProxy_Gres_scalar_false (y z : ℂ) (h : y - (starRingEnd ℂ) z ≠ 0) :
    Gres (y • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) z false
      = (y - (starRingEnd ℂ) z)⁻¹ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) := by
  unfold Gres
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [← sub_smul, ring_inverse_smul_one h]

/-- `𝓛_{(+,-,+),(a,a,a)}(y 1) = W^{-2d} (y - z)⁻² (y - z̄)⁻¹` (the trace of three block projectors is
`adjacentBlockWeight [a,a,a] = (W^{-d})²`). -/
theorem azumaProxy_loop3_scalar (y z : ℂ) (h1 : y - z ≠ 0)
    (h2 : y - (starRingEnd ℂ) z ≠ 0) (a : Zd d L) :
    loopL d L W (blockMat d L W (y • (1 : Matrix (Idx d L W) (Idx d L W) ℂ))) z
        ⟨[true, false, true], [a, a, a]⟩
      = ((W : ℂ)⁻¹ ^ d) ^ 2 * (y - z)⁻¹ ^ 2 * (y - (starRingEnd ℂ) z)⁻¹ := by
  unfold loopL
  rw [azumaProxy_blockMat_scalar]
  simp only [List.zip_cons_cons, List.zip_nil_right, List.foldr_cons, List.foldr_nil,
    azumaProxy_Gres_scalar_true y z h1, azumaProxy_Gres_scalar_false y z h2]
  simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]
  rw [Matrix.trace_smul]
  have hw : Matrix.trace (Eblk d L W a * (Eblk d L W a * Eblk d L W a)) = ((W : ℂ)⁻¹ ^ d) ^ 2 := by
    have := trace_blockProjectorWord_cons d L W a [a, a]
    simp only [blockProjectorWord, List.foldr_cons, List.foldr_nil, Matrix.mul_one] at this
    rw [this, adjacentBlockWeight_three]
    simp
  rw [hw, smul_eq_mul]
  ring

/-- The point of the sample space whose matrix is `μ 1`: the diagonal real coordinates are `μ`. -/
def azumaProxy_xmu (d L W : ℕ) (μ : ℝ) : CoordF d L W → ℝ :=
  fun c => if c.1 = c.2.1 ∧ c.2.2 = true then μ else 0

theorem azumaProxy_xmu_Xmat (μ : ℝ) :
    Xmat d L W (azumaProxy_xmu d L W μ) = (μ : ℂ) • (1 : Matrix (Idx d L W) (Idx d L W) ℂ) := by
  ext i j
  change Xentry d L W (azumaProxy_xmu d L W μ) i j = ((μ : ℂ) • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)) i j
  simp only [Xentry, Matrix.smul_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp [azumaProxy_xmu]
  · simp [azumaProxy_xmu, hij, Ne.symm hij]

end ScalarLoop


/-! ## 6. Compiled nonempty instances (`d = 3`)

Data (merged `GridGoodNInst`, `Induction/GridGoodN.lean` §7): `sz0` (`n = 0`: `L = 4`, `W = 32`,
`lam = 1/64`, `N = 2097152`), the window `s ≡ 0`, `v ≡ 1/32` (`vg`), the grid `K ≡ 4` (`Kg`;
`Δ = 1/128`, `u_j = j/128`: `grid_data`), the energy `E ≡ 1/2` (`η_0 ≈ 0.968`), loop length
`k = 3`, signs `σ = (+,-,+)`, step `j = 0`.  No hypothesis of `azumaSubGN`, `zero_mem_goodSetN`,
`testFun_*` is left open; the only hypothesis of `azumaSubGN_goodExit_instance` is the deterministic
majorant `hQ` of `Δ · k · qvFormN` on `GoodSetN` (the output of the Step 3 tickets S3-10/S3-14, not
proved here). -/

namespace AzumaProxyNInst

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.GridGoodNInst

/-- The energy `E ≡ 1/2`. -/
abbrev Einst : ℕ → ℝ := fun _ => 1 / 2

/-- The signs `(+,-,+)`. -/
abbrev sig3 : Fin 3 → Bool := ![true, false, true]

theorem Einst_abs_lt : ∀ n, |Einst n| < 2 := fun n => by norm_num [Einst]

theorem sInst_nonneg : ∀ n, 0 ≤ sInst n := fun n => by norm_num [sInst]

theorem sInst_le_vg : ∀ n, sInst n ≤ vg n := fun n => by norm_num [sInst, vg]

theorem vg_lt_one : ∀ n, vg n < 1 := fun n => by norm_num [vg]

/-- The loop family `b ↦ (M ↦ 𝓛_{u_1,σ,b}(M))` of the step `0 → 1` at `n = 0`. -/
abbrev phi3 : (Fin 3 → Zd 3 (sz0.L 0)) →
    Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ → ℂ :=
  loopFamN sz0 Einst sInst vg Kg 0 0 sig3

/-- The `Ugen` weights `b ↦ Π_i uKer(a_i, b_i)` from the spectral time `u_1` to `u_m`. -/
abbrev kap3 (m : ℕ) (a : Fin 3 → Zd 3 (sz0.L 0)) : (Fin 3 → Zd 3 (sz0.L 0)) → ℂ :=
  fun b => ∏ i : Fin 3, uKer 3 (sz0.L 0) (sz0.lam 0) (cycProd (fun i => mSigma (Einst 0) (sig3 i)) i)
    (gridTime sInst vg Kg 0 1) (gridTime sInst vg Kg 0 m) (a i) (b i)

/-- The proxy of the instance: the exact variance form `Δ Σ_c gvar_c ‖Σ_b κ_b ∂_c Φ_b(0)‖²` at
`M = 0` (the value of the grid state `H_0 = 0`, `s ≡ 0`). -/
def qProxy3 (m : ℕ) (a : Fin 3 → Zd 3 (sz0.L 0)) : ℝ≥0 :=
  Real.toNNReal (gridStep sInst vg Kg 0 *
    ∑ c : CoordF 3 (sz0.L 0) (sz0.W 0), (gvarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) c : ℝ) *
      ‖∑ b, kap3 m a b * dirDerivN (phi3 b) 0 (coordinateMatrix 3 (sz0.L 0) (sz0.W 0) c)‖ ^ 2)

/-- The three-loop observables of the step `0 → 1` are in the Hermitian test class (merged
`hermTestFunLoopN`, `k = 3`, `n = 0`, `u = u_1 = 1/128 ∈ [0, 1)`). -/
theorem phi3_hermTestFun (b : Fin 3 → Zd 3 (sz0.L 0)) : HermTestFun sz0 0 (phi3 b) := by
  have hu : gridTime sInst vg Kg 0 1 = 1 / 128 := grid_data.2.2.1
  exact (hermTestFunLoopN sz0 3 0 (Einst 0) (gridTime sInst vg Kg 0 1) (Einst_abs_lt 0)
    (by rw [hu]; norm_num) (by rw [hu]; norm_num) sig3 b).1

/-- **Instance of `azumaSubGN`** at the data above, `n = 0`, `j = 0`, for every target time `m` and
label `a`: the family `Φ_b = 𝓛_{u_1,(+,-,+),b}` (in the test class by `hermTestFunLoopN`), the
`Ugen` weights `κ`, the stopping time `τ ≡ K 0 = 4` (`{j < τ}` is the whole space at `j = 0`), the
sets `G 0 = {0}` (`H_0 = 0`, `s ≡ 0`) and `G j = {Hermitian}`, and `Q` the exact variance form at
`M = 0`.  Every hypothesis of the theorem is discharged; the window `(0, 1/32)` is not collapsed
(`grid_data`: `Δ = 1/128`). -/
theorem azumaSubGN_instance (m : ℕ) (a : Fin 3 → Zd 3 (sz0.L 0)) :
    SubGaussFormN sz0 0 (fun _ => Kg 0)
      (fun ω => ∑ b, kap3 m a b * ZfamN sz0 sInst vg Kg 0 0 phi3 ω b) (qProxy3 m a) := by
  refine azumaSubGN sz0 sInst vg Kg 0 phi3 phi3_hermTestFun (kap3 m a) (fun _ => Kg 0)
    (fun j M => M.IsHermitian ∧ (j = 0 → M = 0)) (fun j => MeasurableSet.const _)
    (fun ω j hj => ⟨pathH_isHermitian sz0 sInst vg Kg 0 j ω, fun hj0 => by
      subst hj0
      exact azumaProxy_pathH_zero_of_s_zero sz0 sInst vg Kg 0 rfl ω⟩) 0 (qProxy3 m a)
    (fun M hM _ => ?_)
  rw [hM.2 rfl]
  exact Real.le_coe_toNNReal _

/-- The levels `Γ = 4`, `Λ = 3`, `Φ = 1` (constant in `n`). -/
abbrev Γ4 : ℕ → ℝ := fun _ => 4
abbrev Λ3 : ℕ → ℝ := fun _ => 3
abbrev Φ1 : ℕ → ℝ := fun _ => 1

/-- **Instance of `zero_mem_goodSetN`** (target 2) at `sz0`, `n = 0`, `E = 1/2`, `k = 3`,
`Γ = 4`, `Λ = 3`, `Φ = 1`, `τ' = 1/2`, `D' = 1`: `0 ∈ GoodSetN` at `u = 0`.  The (D4) level of the
theorem is discharged from `Γ² Λ = 48 ≥ k (1 + g²)^{2k} = 3 (1 + 1/4096)^6`
(`azumaProxy_hee_of_levels`). -/
theorem zero_mem_goodSetN_instance :
    (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) ∈
      sz0.GoodSetN 0 (1 / 2) 0 3 4 3 1 (1 / 2) 1 := by
  have hl : sz0.lam 0 = 1 / 64 := sz0_values.2.2.2
  refine zero_mem_goodSetN sz0 0 (E := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (azumaProxy_hee_of_levels sz0 0 (E := 1 / 2) (by norm_num) ?_)
  rw [hl]
  norm_num

/-- **Instance of `zero_mem_goodSetN_of_levels`** at the same data: the sufficient condition
`Γ² Λ = 48 ≥ 3 (1 + (1/64)²)^6` and `0 ≤ Γ`, `1 ≤ Γ Φ` are discharged by `norm_num`. -/
theorem zero_mem_goodSetN_of_levels_instance :
    (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) ∈
      sz0.GoodSetN 0 (1 / 2) 0 3 4 3 1 (1 / 2) 1 := by
  have hl : sz0.lam 0 = 1 / 64 := sz0_values.2.2.2
  refine zero_mem_goodSetN_of_levels sz0 0 (E := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ?_
  rw [hl]
  norm_num

/-- The same at the `GoodSetN` of the grid time `u_0 = 0` (`gridTime … 0 = 0`). -/
theorem zero_mem_goodSetN_instance_grid :
    (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) ∈
      sz0.GoodSetN 0 (Einst 0) (gridTime sInst vg Kg 0 0) 3 (Γ4 0) (Λ3 0) (Φ1 0) (1 / 2) 1 := by
  rw [grid_data.2.1]
  exact zero_mem_goodSetN_instance

/-- **Instance of `azumaSubGN` at `τ = goodExitTauN`**, for every choice of the levels `Γ Λ Φ` and
the decay exponents `τ' D'`: `G j` is `GoodSetN …` intersected with `{0}` at `j = 0` (`H_0 = 0`), so
`hG` is `mem_of_lt_gridExitTauN` and the measurability of `{j < τ}` is the merged `goodExitMeasN`;
`Q` is the exact variance form at `M = 0`. -/
theorem azumaSubGN_goodExit_zero_instance (Γ Λ Φ : ℕ → ℝ) (τ' D' : ℝ) (m : ℕ)
    (a : Fin 3 → Zd 3 (sz0.L 0)) :
    SubGaussFormN sz0 0 (goodExitTauN sz0 Einst sInst vg Kg 3 Γ Λ Φ τ' D' 0)
      (fun ω => ∑ b, kap3 m a b * ZfamN sz0 sInst vg Kg 0 0 phi3 ω b) (qProxy3 m a) := by
  refine azumaSubGN sz0 sInst vg Kg 0 phi3 phi3_hermTestFun (kap3 m a)
    (goodExitTauN sz0 Einst sInst vg Kg 3 Γ Λ Φ τ' D' 0)
    (fun j => {M | M ∈ sz0.GoodSetN 0 (Einst 0) (gridTime sInst vg Kg 0 j) 3 (Γ 0) (Λ 0) (Φ 0) τ' D' ∧
      (j = 0 → M = 0)})
    (goodExitMeasN sz0 Einst sInst vg Kg 0 3 Γ Λ Φ τ' D')
    (fun ω j hj => ⟨mem_of_lt_gridExitTauN hj, fun hj0 => by
      subst hj0
      exact azumaProxy_pathH_zero_of_s_zero sz0 sInst vg Kg 0 rfl ω⟩) 0 (qProxy3 m a)
    (fun M hM _ => ?_)
  rw [hM.2 rfl]
  exact Real.le_coe_toNNReal _

/-- **Non-vacuity of the previous instance** (item 2 of the ticket): at the levels `Γ = 4`,
`Λ = 3`, `Φ = 1` the initial state `H_0 = 0` is in `GoodSetN` at `u_0 = 0`
(`zero_mem_goodSetN_instance_grid`), so the exit time `goodExitTauN` is `≥ 1` at every sample
(the stopping set `{0 < τ}` is the whole space) and `G_0 = GoodSetN ∩ {0}` is nonempty. -/
theorem goodExitTauN_pos_instance (ω : PathΩ sz0) :
    0 < goodExitTauN sz0 Einst sInst vg Kg 3 Γ4 Λ3 Φ1 (1 / 2) 1 0 ω := by
  refine azumaProxy_pos_gridExitTauN sz0 (by norm_num [Kg]) ?_
  rw [azumaProxy_pathH_zero_of_s_zero sz0 sInst vg Kg 0 rfl ω]
  exact zero_mem_goodSetN_instance_grid

/-- **Instance of the composition** `azumaProxy_subG_goodExit` with the proved `azumaSubGN` in place
of the pin: with `τ = goodExitTauN` and `G j = GoodSetN …`, the only remaining hypothesis is the
deterministic majorant `hQ` of `Δ · k · qvFormN` on `GoodSetN` (the work of the Step 3 tickets; it
needs the time shift `u_j → u_{j+1}`, and stays a hypothesis here as in RBM2D
`azumaSubGN_goodExit_instance`). -/
theorem azumaSubGN_goodExit_instance (Γ Λ Φ : ℕ → ℝ) (τ' D' : ℝ) (m : ℕ) (hm : m ≤ Kg 0)
    (a : Fin 3 → Zd 3 (sz0.L 0)) (j : ℕ) (hj : j < m) (Q : ℝ≥0)
    (hQ : ∀ M ∈ sz0.GoodSetN 0 (Einst 0) (gridTime sInst vg Kg 0 j) 3 (Γ 0) (Λ 0) (Φ 0) τ' D',
      M.IsHermitian → gridStep sInst vg Kg 0 * ((3 : ℕ) * qvFormN sz0 0 (Einst 0)
        (gridTime sInst vg Kg 0 (j + 1)) (gridTime sInst vg Kg 0 m) sig3 M a) ≤ (Q : ℝ)) :
    SubGaussStopN sz0 (Einst 0) sig3 (gridTime sInst vg Kg 0)
      (goodExitTauN sz0 Einst sInst vg Kg 3 Γ Λ Φ τ' D' 0)
      (fun j ω => ZvecN sz0 Einst sInst vg Kg 0 j sig3 ω) m a j Q :=
  azumaProxy_subG_goodExit sz0 (azumaSubGN sz0 sInst vg Kg) Einst_abs_lt sInst_nonneg sInst_le_vg
    vg_lt_one 0 3 (by norm_num) sig3 Γ Λ Φ τ' D' m hm a j hj Q hQ

/-- **Instance of `testFun_linComb`**: the `Ugen`-weighted combination of the three-loop
observables is in the Hermitian test class. -/
theorem testFun_linComb_instance (m : ℕ) (a : Fin 3 → Zd 3 (sz0.L 0)) :
    HermTestFun sz0 0 (fun M => ∑ b, kap3 m a b * phi3 b M) :=
  testFun_linComb (kap3 m a) phi3_hermTestFun

/-- **Instance of `testFun_const_smul`**: `M ↦ I · 𝓛_{u_1,(+,-,+),b}(M)` is in the class. -/
theorem testFun_const_smul_instance (b : Fin 3 → Zd 3 (sz0.L 0)) :
    HermTestFun sz0 0 (fun M => Complex.I • phi3 b M) :=
  testFun_const_smul (phi3_hermTestFun b) Complex.I

/-! ### The instance is not degenerate: `Q > 0` (`m = 1`, `a = (0,0,0)`)

For `m = 1` the `Ugen` weights are the identity (`GridDuhamelN_Ugen_self`), so
`Σ_b κ_b Z_b = Z_a`.  At the label `a = (0,0,0)` the proxy `Q = Δ Σ_c gvar_c ‖∂_c Φ(0)‖²` is positive:
the derivative of `Φ` at `0` in the direction `1 = Σ_i E_ii` is `f'(0)` for the explicit profile `f`
of `azumaProxy_loop3_scalar`, and `f'(0) = -W^{-2d} z⁻³ z̄⁻² (2 z̄ + z) ≠ 0` because
`Im (2 z̄ + z) = -Im z ≠ 0`; a nonzero derivative in the direction `1` gives a diagonal coordinate
`c` (variance `svarF_diag > 0`) with `∂_c Φ(0) ≠ 0`.  (RBM2D `AzumaProxyN` §8c, `:1811-1958`.) -/

/-- The label `b = (0,0,0)` (all three insertions in block `0`). -/
abbrev b0 : Fin 3 → Zd 3 (sz0.L 0) := fun _ => 0

/-- The flow value at the step `u_1`: `z_1 = z_{u_1}`. -/
abbrev z1 : ℂ := zt (Einst 0) (gridTime sInst vg Kg 0 1)

theorem z1_im_pos : 0 < z1.im := by
  have hu : gridTime sInst vg Kg 0 1 = 1 / 128 := grid_data.2.2.1
  unfold z1
  rw [zt_im, hu]
  exact mul_pos (by norm_num) (mE_im_pos (Einst_abs_lt 0))

theorem z1_ne_zero : z1 ≠ 0 := fun h => by
  have := z1_im_pos
  rw [h] at this
  simp at this

theorem z1_sub_ne (y : ℝ) : (y : ℂ) - z1 ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  have h2 := z1_im_pos
  simp at this
  linarith

theorem z1_sub_conj_ne (y : ℝ) : (y : ℂ) - (starRingEnd ℂ) z1 ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  have h2 := z1_im_pos
  simp at this
  linarith

/-- The explicit scalar profile `f(y) = W^{-2d} (y - z)⁻² (y - z̄)⁻¹`. -/
noncomputable def fsc (y : ℝ) : ℂ :=
  (((sz0.W 0 : ℕ) : ℂ)⁻¹ ^ 3) ^ 2 * ((y : ℂ) - z1)⁻¹ ^ 2 * ((y : ℂ) - (starRingEnd ℂ) z1)⁻¹

/-- The observable `𝓛_{u_1,(+,-,+),(0,0,0)}` at a scalar matrix `y 1` is `f(y)`. -/
theorem phi3_scalar (y : ℝ) :
    phi3 b0 ((y : ℂ) • (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ))
      = fsc y := by
  have hl : loopOf sig3 b0 = (⟨[true, false, true], [0, 0, 0]⟩ : LoopIdx (Zd 3 (sz0.L 0))) := by
    simp [loopOf, List.ofFn_succ, sig3, b0]
  unfold phi3 loopFamN
  rw [hl]
  exact azumaProxy_loop3_scalar (y : ℂ) z1 (z1_sub_ne y) (z1_sub_conj_ne y) 0

theorem fsc_hasDerivAt :
    HasDerivAt fsc (-((((sz0.W 0 : ℕ) : ℂ)⁻¹ ^ 3) ^ 2 * z1⁻¹ ^ 3
      * ((starRingEnd ℂ) z1)⁻¹ ^ 2 * (2 * (starRingEnd ℂ) z1 + z1))) 0 := by
  have hz := z1_ne_zero
  have hzb : (starRingEnd ℂ) z1 ≠ 0 := by simpa using hz
  have hA : HasDerivAt (fun z : ℂ => z - z1) 1 ((0 : ℝ) : ℂ) :=
    (hasDerivAt_id ((0 : ℝ) : ℂ)).sub_const z1
  have hB : HasDerivAt (fun z : ℂ => z - (starRingEnd ℂ) z1) 1 ((0 : ℝ) : ℂ) :=
    (hasDerivAt_id ((0 : ℝ) : ℂ)).sub_const ((starRingEnd ℂ) z1)
  have h1 : HasDerivAt (fun y : ℝ => ((y : ℂ) - z1)⁻¹) (-(1 : ℂ) / ((0 : ℂ) - z1) ^ 2) 0 := by
    have := (hA.inv (by simpa using hz)).comp_ofReal
    simpa using this
  have h2 : HasDerivAt (fun y : ℝ => ((y : ℂ) - (starRingEnd ℂ) z1)⁻¹)
      (-(1 : ℂ) / ((0 : ℂ) - (starRingEnd ℂ) z1) ^ 2) 0 := by
    have := (hB.inv (by simpa using hzb)).comp_ofReal
    simpa using this
  have h3 := (h1.mul (h1.mul h2)).const_mul ((((sz0.W 0 : ℕ) : ℂ)⁻¹ ^ 3) ^ 2)
  have hfun : fsc = fun y : ℝ => (((sz0.W 0 : ℕ) : ℂ)⁻¹ ^ 3) ^ 2 *
      (((y : ℂ) - z1)⁻¹ * (((y : ℂ) - z1)⁻¹ * ((y : ℂ) - (starRingEnd ℂ) z1)⁻¹)) := by
    funext y; unfold fsc; ring
  rw [hfun]
  refine h3.congr_deriv ?_
  simp only [Pi.mul_apply, zero_sub, Complex.ofReal_zero]
  field_simp
  ring

theorem fsc_deriv_ne : deriv fsc 0 ≠ 0 := by
  rw [fsc_hasDerivAt.deriv]
  have hz := z1_ne_zero
  have hzb : (starRingEnd ℂ) z1 ≠ 0 := by simpa using hz
  have hW : (((sz0.W 0 : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne _)
  have h2 : 2 * (starRingEnd ℂ) z1 + z1 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    have h3 := z1_im_pos
    simp at this
    linarith
  simp [hz, hzb, hW, h2]

theorem fderiv_one_ne :
    fderiv ℝ (phi3 b0) 0
      (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) ≠ 0 := by
  have hdiff : DifferentiableAt ℝ (phi3 b0) 0 :=
    ((phi3_hermTestFun b0).contDiffAt 0 Matrix.isHermitian_zero).differentiableAt (by norm_num)
  have h := azumaProxy_dirDerivN_eq
    (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) hdiff
  rw [← h]
  have : dirDerivN (phi3 b0) 0
      (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) = deriv fsc 0 := by
    have hfun : (fun y : ℝ => phi3 b0 ((0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0))
        (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) + (y : ℂ) • (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0))
        (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ))) = fsc :=
      funext fun y => by rw [zero_add, phi3_scalar]
    exact congrArg (fun f : ℝ → ℂ => deriv f 0) hfun
  rw [this]
  exact fsc_deriv_ne

/-- A diagonal coordinate with positive variance along which `Φ` has a nonzero derivative at `0`. -/
theorem exists_coord_deriv_ne :
    ∃ c : CoordF 3 (sz0.L 0) (sz0.W 0),
      0 < (gvarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) c : ℝ) ∧
      fderiv ℝ (phi3 b0) 0 (coordinateMatrix 3 (sz0.L 0) (sz0.W 0) c) ≠ 0 := by
  by_contra hne
  simp only [not_exists, not_and, not_not] at hne
  have hsum : (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
      = ∑ c : CoordF 3 (sz0.L 0) (sz0.W 0), (azumaProxy_xmu 3 (sz0.L 0) (sz0.W 0) 1 c) •
          coordinateMatrix 3 (sz0.L 0) (sz0.W 0) c := by
    have h := Xmat_eq_sum_coordinates 3 (sz0.L 0) (sz0.W 0)
      (azumaProxy_xmu 3 (sz0.L 0) (sz0.W 0) 1)
    rw [azumaProxy_xmu_Xmat] at h
    simpa using h
  apply fderiv_one_ne
  rw [hsum, map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [map_smul]
  by_cases hc : azumaProxy_xmu 3 (sz0.L 0) (sz0.W 0) 1 c = 0
  · rw [hc, zero_smul]
  · have hdiag : c.1 = c.2.1 ∧ c.2.2 = true := by
      by_contra hnc
      exact hc (by simp [azumaProxy_xmu, hnc])
    obtain ⟨i, j, b⟩ := c
    obtain ⟨h1, h2⟩ := hdiag
    simp only at h1 h2
    subst h1; subst h2
    have hpos : 0 < (gvarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (i, i, true) : ℝ) := by
      have : (gvarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (i, i, true) : ℝ)
          = svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) i i := by
        unfold gvarF
        simp only [↓reduceIte]
        rfl
      rw [this, svarF_diag]
      have hW : (0 : ℝ) < ((sz0.W 0 : ℕ) : ℝ) := by exact_mod_cast sz0.W_pos 0
      positivity
    rw [hne _ hpos, smul_zero]

/-- At `m = 1` the `Ugen` weights are the identity: `Σ_b κ_b X_b = X_a`. -/
theorem kap3_one_sum (a : Fin 3 → Zd 3 (sz0.L 0)) (X : (Fin 3 → Zd 3 (sz0.L 0)) → ℂ) :
    ∑ b, kap3 1 a b * X b = X a := by
  have hu : gridTime sInst vg Kg 0 1 = 1 / 128 := grid_data.2.2.1
  have h : Ugen 3 (sz0.L 0) (sz0.lam 0) (Einst 0) sig3 (gridTime sInst vg Kg 0 1)
      (gridTime sInst vg Kg 0 1) X = X :=
    GridDuhamelN_Ugen_self (sz0.three_le_L 0) (by norm_num) sig3 (by rw [hu]; norm_num)
      (by rw [hu]; norm_num) X
  exact congrFun h a

theorem sum_pos_aux {L W : ℕ} [NeZero L] [NeZero W]
    (F : Matrix (Idx 3 L W) (Idx 3 L W) ℂ → ℂ) (g : ℝ) (c : CoordF 3 L W)
    (hc : 0 < (gvarF 3 L W g c : ℝ)) (hne : F (coordinateMatrix 3 L W c) ≠ 0) :
    0 < ∑ c' : CoordF 3 L W, (gvarF 3 L W g c' : ℝ) * ‖F (coordinateMatrix 3 L W c')‖ ^ 2 :=
  Finset.sum_pos' (fun c' _ => mul_nonneg (gvarF 3 L W g c').2 (sq_nonneg _))
    ⟨c, Finset.mem_univ c, mul_pos hc (pow_pos (norm_pos_iff.2 hne) 2)⟩

/-- **The proxy of the `azumaSubGN` instance is positive** (`m = 1`, `a = (0,0,0)`, `n = 0`): the
first-chaos increment `Z_0` of the instance is genuinely random, not conditionally `0`. -/
theorem qProxy3_pos : 0 < qProxy3 1 b0 := by
  unfold qProxy3
  rw [Real.toNNReal_pos]
  obtain ⟨c, hc, hne⟩ := exists_coord_deriv_ne
  have hΔ : 0 < gridStep sInst vg Kg 0 := by rw [grid_data.1]; norm_num
  refine mul_pos hΔ ?_
  have hdiff : DifferentiableAt ℝ (phi3 b0) 0 :=
    ((phi3_hermTestFun b0).contDiffAt 0 Matrix.isHermitian_zero).differentiableAt (by norm_num)
  have hsum : ∀ c' : CoordF 3 (sz0.L 0) (sz0.W 0),
      ∑ b, kap3 1 b0 b * dirDerivN (phi3 b) 0 (coordinateMatrix 3 (sz0.L 0) (sz0.W 0) c')
        = fderiv ℝ (phi3 b0) 0 (coordinateMatrix 3 (sz0.L 0) (sz0.W 0) c') := by
    intro c'
    rw [kap3_one_sum b0 (fun b => dirDerivN (phi3 b) 0 (coordinateMatrix 3 (sz0.L 0) (sz0.W 0) c'))]
    exact azumaProxy_dirDerivN_eq _ hdiff
  simp only [hsum]
  exact sum_pos_aux (fderiv ℝ (phi3 b0) 0) (sz0.lam 0) c hc hne

end AzumaProxyNInst

/-! ## 7. Statement checks -/

section StatementChecks

example {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) : AzumaSubGN sz s t K :=
  azumaSubGN sz s t K

end StatementChecks

end RBM.Ind

end

#print axioms RBM.Ind.testFun_const_smul
#print axioms RBM.Ind.testFun_linComb
#print axioms RBM.Ind.azumaSubGN
#print axioms RBM.Ind.zero_mem_goodSetN
#print axioms RBM.Ind.azumaProxy_hee_of_levels
#print axioms RBM.Ind.zero_mem_goodSetN_of_levels
#print axioms RBM.Ind.azumaProxy_pathH_zero_of_s_zero
#print axioms RBM.Ind.azumaProxy_subG_ugen
#print axioms RBM.Ind.azumaProxy_subG_goodExit
#print axioms RBM.Ind.azumaProxy_pos_gridExitTauN
#print axioms RBM.Ind.azumaProxy_loop3_scalar
#print axioms RBM.Ind.AzumaProxyNInst.azumaSubGN_instance
#print axioms RBM.Ind.AzumaProxyNInst.zero_mem_goodSetN_instance
#print axioms RBM.Ind.AzumaProxyNInst.zero_mem_goodSetN_of_levels_instance
#print axioms RBM.Ind.AzumaProxyNInst.zero_mem_goodSetN_instance_grid
#print axioms RBM.Ind.AzumaProxyNInst.azumaSubGN_goodExit_zero_instance
#print axioms RBM.Ind.AzumaProxyNInst.goodExitTauN_pos_instance
#print axioms RBM.Ind.AzumaProxyNInst.azumaSubGN_goodExit_instance
#print axioms RBM.Ind.AzumaProxyNInst.testFun_linComb_instance
#print axioms RBM.Ind.AzumaProxyNInst.testFun_const_smul_instance
#print axioms RBM.Ind.AzumaProxyNInst.qProxy3_pos
