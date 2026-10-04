/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.LoopC2N
import RBM3D.Induction.GridDuhamelN
import RBM3D.Induction.QVN
import RBM3D.Path.LoopStep
import RBM3D.Path.StepDecomp

/-!
# The general-`n` one-step decomposition `ξ = Z + Y` of the loop observables (`d ≥ 3`)

Ticket T2121 (ST2-30).  Port of RBM2D `Induction/StepDecompN.lean` at commit `c9a24cf` (cited
`StepDecompN:<line>`; 1550 lines there; the RBM2D file is a port of RBM1D
`Gauss/GridStepDecompC.lean` at `c06b103` on the structure of the merged real
`Path/StepDecomp.lean`).
Paper: arXiv:2507.20274, the martingale term of `int_K-L_ST` (`3_5:134`) and `alu9_STime`
(`3_5:218-240`); the split `ξ = Z + Y` is a Lean device (BDG replaced by Azuma, DECISIONS §10).

For a label-indexed family `Φ_a` of complex observables in the Hermitian test class `HermTestFun`
(`Path/StepDecomp.lean`) and a complex kernel `U`, one grid step `H_j ↦ H_{j+1} = H_j + √Δ X_{j+1}`
splits `ξ_b = Σ_a U(b,a) (Φ_a(H_{j+1}) - E[Φ_a(H_{j+1}) | F_j]) = Z_b + Y_b`, with
`Z_b = √Δ tr(A_b X_{j+1})` exactly linear in the Gaussian increment (`A_b = Σ_a U(b,a) ∇Φ_a(H_j)`
is `F_j`-measurable; real part `stepZCN_re`, imaginary part `stepZCN_im`) and `Y_b` a Taylor
remainder with `E[Y_b | F_j] = 0` and `‖Y_b‖ ≤ g + E[g | F_j]`,
`g = (Σ_a ‖U(b,a)‖) (C₂/2) Δ ‖X_{j+1}‖²`.

## Main declarations (namespace `RBM.Ind`)

* Pinned definitions: `AbCN`, `stepZCN_re`, `stepZCN_im`, `stepZCN`, `stepXiCN`, `stepYCN`,
  `StepDecompCN_Stmt`, `loopFamN` (`a ↦ (M ↦ 𝓛_{u_{j+1},σ,a}(M))`, with the merged `loopL`, `zt`).
* The seven vocabulary declarations of RBM2D `GridGoodN:241-290` (class c; ST2-32 imports them from
  here): `dirDerivN`, `ZfamN`, `ZvecN`, `YvecN`, `stoppedEdgeN`, `SubGaussFormN`, `SubGaussStopN`
  (`d`-dimensional, no `[NeZero k]`; `dirDerivN` by Amend 1).
* `stepDecompCN : StepDecompCN_Stmt sz`, `stepDecompCN_Z_subG`,
  `integrable_stepZCN_re/im_of_hermTestFun`,
  `stepDecompCN_Y_sq`: `∫ ‖Y‖² ≤ 4 ((Σ_a ‖U(b,a)‖) C₂/2)² Δ² ∫ ‖X_{j+1}‖⁴`.
* Identification for the loop family: `ZvecN_eq_stepZCN` (pointwise), `martIncN_eq_stepXiCN`,
  `YvecN_eq_stepYCN` (a.e., all labels), `Ugen_stepZCN`, `Ugen_stepYCN`,
  `StepDecompN_subGaussStopN_zvecN`.
* Section 8: compiled nonempty instances at `sz0` (`d = 3`, `L_0 = 4`, `W_0 = 32`, `N = 2097152`).

## Renaming and `d ≥ 3` changes (`docs/tickets/ST1-COMMON.md` items 2-3)

`d : Sizes` becomes `sz : Sizes d`; `Z2 (d.L n)` becomes `Zd d (sz.L n)`, `Idx L W` becomes
`Idx d L W`; `Sizes.size` is `N = (W L)^d`.  The statements of the stepDecompCN family are
`ι`-generic: the only dimension entering is `C₂` through the hypothesis `hC₂`, which for the loop
family is `k (k + 1) N η_{u_{j+1}}^{-(k+2)}` with `N = (W L)^d` (merged `hermTestFunLoopN`).
`gloop`, `spectralZ` become `loopL`, `zt`; RBM2D's `Ugen` (no coupling, `i + 1`) is the merged
`Ugen d L g` (`= UN`, kernel `uKer d L g (cycProd m i)`, `finRotate`) at `g = sz.lam n`, and RBM2D's
`KLoop.Kcal` is `sz.STKloop`.  `[NeZero k]` is dropped from `stoppedEdgeN`, `SubGaussStopN`,
`Ugen_stepZCN`, `Ugen_stepYCN`, `StepDecompN_subGaussStopN_zvecN` (D204, T2111b): strictly stronger.
The test-class step for `k = 0` needs no case split (the merged `hermTestFunLoopN` has all `k`).
The grid-time arithmetic of RBM2D `Path/GoodEvent` (import cut) is copied as private
`StepDecompN_gridTime_*`.

Reduction at `k = 2` to the merged `Path/StepDecomp` (`stepDecomp`, `stepDecomp_Z_subG`): see the
prove report (section (a), row 13).  Every helper is `private` or carries the prefix `StepDecompN_`.
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

/-! ## 1. The pinned definitions -/

section PinnedDefs

variable {d : ℕ} (sz : Sizes d)

/-- **`AbCN`**: the `filt sz j`-measurable direction of a label-indexed complex family `Φ` with a
complex kernel `U` and target label `b`: `Σ_a U(b,a) • gradMat (Φ a) (H_j)` (RBM1D `AbC`,
`Gauss/GridStepDecompC.lean:87`; merged real version `Ab`, `Path/StepDecomp.lean:702`). -/
def AbCN (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*} [Fintype ι]
    (Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ) (U : ι → ι → ℂ) (b : ι)
    (ω : PathΩ sz) : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  ∑ a, U b a • gradMat (Φ a) (pathH sz s t K n j ω)

/-- Real part of the linear term: `√Δ · linTr (AbCN) X_{j+1}` (RBM1D `stepZC_re`, `:94`). -/
def stepZCN_re (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*} [Fintype ι]
    (Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ) (U : ι → ι → ℂ) (b : ι)
    (ω : PathΩ sz) : ℝ :=
  Real.sqrt (gridStep s t K n) *
    linTr n (AbCN sz s t K n j Φ U b ω) (Sizes.seqXmat sz n (ω (j + 1)))

/-- Imaginary part of the linear term: `√Δ · linTr ((−I) • AbCN) X_{j+1}` (RBM1D `stepZC_im`,
`:102`). -/
def stepZCN_im (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*} [Fintype ι]
    (Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ) (U : ι → ι → ℂ) (b : ι)
    (ω : PathΩ sz) : ℝ :=
  Real.sqrt (gridStep s t K n) *
    linTr n ((-Complex.I) • AbCN sz s t K n j Φ U b ω) (Sizes.seqXmat sz n (ω (j + 1)))

/-- **`stepZCN`**: the exactly linear part of one grid step, complex (RBM1D `stepZC`, `:112`). -/
def stepZCN (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*} [Fintype ι]
    (Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ) (U : ι → ι → ℂ) (b : ι)
    (ω : PathΩ sz) : ℂ :=
  (stepZCN_re sz s t K n j Φ U b ω : ℂ) + Complex.I * (stepZCN_im sz s t K n j Φ U b ω : ℂ)

/-- **`stepXiCN`**: the propagated observable minus its `filt sz j`-conditional mean (RBM1D
`stepXiC`, `:118`). -/
def stepXiCN (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*} [Fintype ι]
    (Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ) (U : ι → ι → ℂ) (b : ι)
    (ω : PathΩ sz) : ℂ :=
  (∑ a, U b a * Φ a (pathH sz s t K n (j + 1) ω))
    - (pathP sz)[fun ω' => ∑ a, U b a * Φ a (pathH sz s t K n (j + 1) ω') | filt sz j] ω

/-- **`stepYCN`**: the remainder `ξ − Z` (RBM1D `stepYC`, `:126`). -/
def stepYCN (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*} [Fintype ι]
    (Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ) (U : ι → ι → ℂ) (b : ι)
    (ω : PathΩ sz) : ℂ :=
  stepXiCN sz s t K n j Φ U b ω - stepZCN sz s t K n j Φ U b ω

/-- **Statement of `stepDecompCN`** (RBM1D `stepDecompC`, `:455`, with the class `HermTestFun`
and the Hermitian-direction bound `hC₂` of the merged `stepDecomp`, `Path/StepDecomp.lean:1160`;
no reality hypothesis): (i) `ξ = Z + Y` pointwise; (ii) `AbCN` is `filt sz j`-measurable; (iii) a.e.
`‖Y‖ ≤ g + E[g | F_j]`, `g = (Σ_a ‖U(b,a)‖)(C₂/2)Δ‖X_{j+1}‖²`; (iv) `E[Y | F_j] = 0`. -/
def StepDecompCN_Stmt : Prop :=
  ∀ (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type} [Fintype ι]
    {Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ},
    (∀ a, HermTestFun sz n (Φ a)) → ∀ {C₂ : ℝ},
    (∀ a (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2) →
    0 ≤ gridStep s t K n → ∀ (U : ι → ι → ℂ) (b : ι),
    Integrable (stepZCN_re sz s t K n j Φ U b) (pathP sz) →
    Integrable (stepZCN_im sz s t K n j Φ U b) (pathP sz) →
    (∀ ω, stepXiCN sz s t K n j Φ U b ω
        = stepZCN sz s t K n j Φ U b ω + stepYCN sz s t K n j Φ U b ω)
      ∧ Measurable[filt sz j] (fun ω => AbCN sz s t K n j Φ U b ω)
      ∧ (∀ᵐ ω ∂(pathP sz), ‖stepYCN sz s t K n j Φ U b ω‖
          ≤ (∑ a, ‖U b a‖) * ((C₂ / 2) * gridStep s t K n) * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2
            + (pathP sz)[fun ω' => (∑ a, ‖U b a‖) * ((C₂ / 2) * gridStep s t K n)
                * ‖Sizes.seqXmat sz n (ω' (j + 1))‖ ^ 2 | filt sz j] ω)
      ∧ (pathP sz)[stepYCN sz s t K n j Φ U b | filt sz j] =ᵐ[pathP sz] fun _ => (0 : ℂ)

/-- **`loopFamN`** (pinned): the loop family `a ↦ (M ↦ 𝓛_{u_{j+1},σ,a}(M))` at the spectral time
of the step `j → j+1`; with the identity kernel it turns `stepXiCN`, `stepZCN`, `stepYCN` into
`martIncN`, `ZvecN`, `YvecN` (targets 3). -/
def loopFamN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool) :
    (Fin k → Zd d (sz.L n)) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ :=
  fun a M => loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M)
    (zt (E n) (gridTime s t K n (j + 1))) (loopOf σ a)

end PinnedDefs

/-! ## 1b. The vocabulary of `GridGoodN` (RBM2D `Induction/GridGoodN.lean:241-290`)

The seven declarations `dirDerivN`, `ZfamN`, `ZvecN`, `YvecN`, `stoppedEdgeN`, `SubGaussFormN`,
`SubGaussStopN` are defined here, `d`-dimensional and without `[NeZero k]` (D204, T2111b); ST2-32
(`GridGoodN`) imports them from this file.  `dirDerivN` is the seventh declaration authorized by
Amend 1 of the ticket. -/

section Vocab

/-- The directional derivative of an observable `Φ` at `M` along `X` (real parameter):
`d/dy Φ(M + yX)` at `y = 0` (RBM2D `dirDerivN`, `GridGoodN:241`). -/
def dirDerivN {d L W : ℕ} [NeZero L] [NeZero W]
    (Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ) (M X : Matrix (Idx d L W) (Idx d L W) ℂ) : ℂ :=
  deriv (fun y : ℝ => Φ (M + (y : ℂ) • X)) 0

variable {d : ℕ} (sz : Sizes d)

/-- **`ZfamN`**: the first-chaos part of a family `Φ` of observables on the grid step
`j → j+1`: `Z_b = √Δ · ∂_{X_{j+1}} Φ_b (H_j)` (RBM2D `ZfamN`, `GridGoodN:249`). -/
def ZfamN (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*}
    (Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ)
    (ω : PathΩ sz) : ι → ℂ :=
  fun b => ((Real.sqrt (gridStep s t K n) : ℝ) : ℂ) *
    dirDerivN (Φ b) (pathH sz s t K n j ω) (Sizes.seqXmat sz n (ω (j + 1)))

/-- **`ZvecN`**: the first-chaos part of `martIncN` (the step `j → j+1`): `√Δ` times the
directional derivative of `𝓛_{u_{j+1},σ,b}` at `H_j` along the Gaussian increment `X_{j+1}`
(RBM2D `ZvecN`, `GridGoodN:258`). -/
def ZvecN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool)
    (ω : PathΩ sz) : (Fin k → Zd d (sz.L n)) → ℂ :=
  fun b => ((Real.sqrt (gridStep s t K n) : ℝ) : ℂ) *
    loopDerivN d (sz.L n) (sz.W n) (E n) (gridTime s t K n (j + 1)) (pathH sz s t K n j ω)
      (Sizes.seqXmat sz n (ω (j + 1))) σ b

/-- **`YvecN`**: the quadratic remainder `martIncN - ZvecN` (RBM2D `YvecN`, `GridGoodN:266`). -/
def YvecN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool)
    (ω : PathΩ sz) : (Fin k → Zd d (sz.L n)) → ℂ :=
  fun b => martIncN sz E s t K n j σ ω b - ZvecN sz E s t K n j σ ω b

/-- The stopped, propagated increment `1_{j<τ} (𝒰_{u_{j+1},t'} Y_j)_b` (RBM2D `stoppedEdgeN`,
`GridGoodN:271`; no `[NeZero k]`; `Ugen` at the coupling `sz.lam n`). -/
def stoppedEdgeN {n k : ℕ} (E : ℝ) (σ : Fin k → Bool) (u : ℕ → ℝ) (t' : ℝ)
    (τ : PathΩ sz → ℕ) (Y : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ)
    (b : Fin k → Zd d (sz.L n)) (j : ℕ) (ω : PathΩ sz) : ℂ :=
  {ω' | j < τ ω'}.indicator
    (fun ω' => Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) t' (Y j ω') b) ω

/-- Conditional sub-Gaussianity (real and imaginary part, common proxy `c`) of the stopped
complex increment `1_{j<τ} F` given `F_j` (RBM2D `SubGaussFormN`, `GridGoodN:279`). -/
def SubGaussFormN (j : ℕ) (τ : PathΩ sz → ℕ) (F : PathΩ sz → ℂ) (c : ℝ≥0) : Prop :=
  HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
    (fun ω => ({ω' | j < τ ω'}.indicator F ω).re) c (pathP sz) ∧
  HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
    (fun ω => ({ω' | j < τ ω'}.indicator F ω).im) c (pathP sz)

/-- The `hsubG` hypothesis of the assembled bound: the stopped, propagated increment
`1_{j<τ} (𝒰_{u_{j+1},u_m} Z_j)_a` is conditionally sub-Gaussian with proxy `c` (RBM2D
`SubGaussStopN`, `GridGoodN:287`; no `[NeZero k]`). -/
def SubGaussStopN {n k : ℕ} (E : ℝ) (σ : Fin k → Bool) (u : ℕ → ℝ) (τ : PathΩ sz → ℕ)
    (Z : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ) (m : ℕ) (a : Fin k → Zd d (sz.L n))
    (j : ℕ) (c : ℝ≥0) : Prop :=
  SubGaussFormN sz j τ (fun ω' => Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m) (Z j ω') a) c

end Vocab

/-! ## 2. Private helpers copied from the merged `Path/StepDecomp.lean` (private there)

The Hermitian projection, the `C²` composition, `gradMat` along the projection and the pathwise
second-order Taylor bound along a Hermitian line (merged `Path/StepDecomp.lean:186-365`, namespace
`RBM.Path`, all `private`); copied with the prefix `StepDecompN_`. -/

section Herm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Hermitian projection `M ↦ ½ (M + Mᴴ)` as a continuous `ℝ`-linear map (the pattern of
RBM1D `hermCLM`, `Gauss/Generator.lean:1397`, commit `86573b9`). -/
private def StepDecompN_hermCLM (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Matrix ι ι ℂ →L[ℝ] Matrix ι ι ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (2⁻¹ : ℝ) • (M + Matrix.conjTranspose M)
      map_add' := by
        intro M M'
        rw [Matrix.conjTranspose_add]
        module
      map_smul' := by
        intro r M
        rw [RingHom.id_apply, Matrix.conjTranspose_smul, star_trivial]
        module }

private theorem StepDecompN_hermCLM_apply (M : Matrix ι ι ℂ) :
    StepDecompN_hermCLM ι M = (2⁻¹ : ℝ) • (M + Matrix.conjTranspose M) := rfl

private theorem StepDecompN_isHermitian_hermCLM (M : Matrix ι ι ℂ) :
    (StepDecompN_hermCLM ι M).IsHermitian := by
  change Matrix.conjTranspose ((2⁻¹ : ℝ) • (M + Matrix.conjTranspose M))
      = (2⁻¹ : ℝ) • (M + Matrix.conjTranspose M)
  rw [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose, add_comm]

private theorem StepDecompN_hermCLM_of_isHermitian {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    StepDecompN_hermCLM ι M = M := by
  rw [StepDecompN_hermCLM_apply, hM]
  module

omit [Fintype ι] in
private theorem StepDecompN_isHermitian_single_diag (i : ι) :
    (Matrix.single i i (1 : ℂ)).IsHermitian := by
  simp [Matrix.IsHermitian, Matrix.conjTranspose_single]

omit [Fintype ι] in
private theorem StepDecompN_isHermitian_S (i j : ι) :
    (Matrix.single i j (1 : ℂ) + Matrix.single j i 1).IsHermitian := by
  simp [Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_single, add_comm]

omit [Fintype ι] in
private theorem StepDecompN_isHermitian_T (i j : ι) :
    (Matrix.single i j Complex.I - Matrix.single j i Complex.I).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_single, Matrix.conjTranspose_single]
  simp only [Complex.star_def, Complex.conj_I, ← Matrix.single_neg]
  abel

/-- `Φ ∘ P` is `C²` everywhere when `Φ` is `C²` at every Hermitian point. -/
private theorem StepDecompN_contDiff_comp {Φ : Matrix ι ι ℂ → ℂ}
    (h : ∀ M, M.IsHermitian → ContDiffAt ℝ 2 Φ M) :
    ContDiff ℝ 2 (fun M => Φ (StepDecompN_hermCLM ι M)) :=
  contDiff_iff_contDiffAt.2 fun M =>
    (h _ (StepDecompN_isHermitian_hermCLM M)).comp M (StepDecompN_hermCLM ι).contDiff.contDiffAt

/-- The first derivative of `Φ ∘ P` at a Hermitian point, along a Hermitian direction, is that of
`Φ`. -/
private theorem StepDecompN_fderiv_comp {Φ : Matrix ι ι ℂ → ℂ} {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (hΦ : DifferentiableAt ℝ Φ M) {B : Matrix ι ι ℂ} (hB : B.IsHermitian) :
    fderiv ℝ (fun M' => Φ (StepDecompN_hermCLM ι M')) M B = fderiv ℝ Φ M B := by
  have hPM := StepDecompN_hermCLM_of_isHermitian hM
  have hf : DifferentiableAt ℝ Φ (StepDecompN_hermCLM ι M) := by rw [hPM]; exact hΦ
  have h : HasFDerivAt (fun M' => Φ (StepDecompN_hermCLM ι M'))
      ((fderiv ℝ Φ (StepDecompN_hermCLM ι M)).comp (StepDecompN_hermCLM ι)) M :=
    hf.hasFDerivAt.comp M (StepDecompN_hermCLM ι).hasFDerivAt
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, hPM, StepDecompN_hermCLM_of_isHermitian hB]

/-- The gradient matrix of `Φ ∘ P` at a Hermitian point is that of `Φ`: `gradMat` reads `Φ`
only along Hermitian directions. -/
private theorem StepDecompN_gradMat_comp {Φ : Matrix ι ι ℂ → ℂ} {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (hΦ : DifferentiableAt ℝ Φ M) :
    gradMat (fun M' => Φ (StepDecompN_hermCLM ι M')) M = gradMat Φ M := by
  ext i j
  simp only [gradMat, Matrix.of_apply]
  rw [StepDecompN_fderiv_comp hM hΦ (StepDecompN_isHermitian_single_diag i),
    StepDecompN_fderiv_comp hM hΦ (StepDecompN_isHermitian_S i j),
    StepDecompN_fderiv_comp hM hΦ (StepDecompN_isHermitian_T i j)]

private theorem StepDecompN_continuous_gradMat {Ψ : Matrix ι ι ℂ → ℂ} (h : ContDiff ℝ 2 Ψ) :
    Continuous (gradMat Ψ) := by
  have hc : ∀ B : Matrix ι ι ℂ, Continuous fun M => fderiv ℝ Ψ M B :=
    fun B => (h.continuous_fderiv (by norm_num)).clm_apply continuous_const
  refine continuous_matrix fun i j => ?_
  simp only [gradMat, Matrix.of_apply]
  split_ifs
  · exact hc _
  · exact continuous_const.mul ((hc _).add (continuous_const.mul (hc _)))

end Herm

section Taylor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- (RBM1D `hasDerivAt_add_smul`, `Gauss/GridStepDecomp.lean:331`.) -/
private theorem StepDecompN_hasDerivAt_add_smul (M y : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (fun t' : ℝ => M + t' • y) y t := by
  simpa using ((hasDerivAt_id t).smul_const y).const_add M

private theorem StepDecompN_isHermitian_add_smul {M y : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (hy : y.IsHermitian) (t : ℝ) : (M + t • y).IsHermitian := by
  have hcast : M + t • y = M + (t : ℂ) • y := by rw [Complex.coe_smul]
  rw [hcast]
  exact hM.add (hy.smul (Complex.conj_ofReal t))

/-- `RBM1D` `hasFDerivAt_fderiv_apply'` (`Gauss/TestFunHerm.lean:104`, commit `86573b9`). -/
private theorem StepDecompN_hasFDerivAt_fderiv_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℂ} {M : E} (h : DifferentiableAt ℝ (fderiv ℝ f) M) (A : E) :
    HasFDerivAt (fun M' => fderiv ℝ f M' A) ((fderiv ℝ (fderiv ℝ f) M).flip A) M := by
  have hc := (h.hasFDerivAt).clm_apply (hasFDerivAt_const (𝕜 := ℝ) A M)
  simpa using hc

/-- **The pathwise second-order Taylor remainder bound along a Hermitian line** (RBM1D
`norm_taylor_remainder_le`, `Gauss/GridStepDecomp.lean:342`, commit `86573b9`).  Only (H1) at
Hermitian points and the Hermitian-direction bound (H3) are used; every point of the segment
`M + t y` is Hermitian. -/
private theorem StepDecompN_taylor {Φ : Matrix ι ι ℂ → ℂ}
    (h : ∀ M, M.IsHermitian → ContDiffAt ℝ 2 Φ M) {C₂ : ℝ}
    (hC₂ : ∀ M y : Matrix ι ι ℂ, M.IsHermitian → y.IsHermitian →
      ‖fderiv ℝ (fderiv ℝ Φ) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    {M y : Matrix ι ι ℂ} (hM : M.IsHermitian) (hy : y.IsHermitian) {s : ℝ} (hs : 0 ≤ s) :
    ‖Φ (M + s • y) - Φ M - s • fderiv ℝ Φ M y‖ ≤ (C₂ / 2) * s ^ 2 * ‖y‖ ^ 2 := by
  have hH := StepDecompN_isHermitian_add_smul hM hy
  have hdiff : ∀ t : ℝ, DifferentiableAt ℝ Φ (M + t • y) :=
    fun t => (h _ (hH t)).differentiableAt (by norm_num)
  have hdiff2 : ∀ t : ℝ, DifferentiableAt ℝ (fderiv ℝ Φ) (M + t • y) := fun t =>
    ((h _ (hH t)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hp : ∀ t : ℝ, HasDerivAt (fun t' : ℝ => Φ (M + t' • y)) (fderiv ℝ Φ (M + t • y) y) t :=
    fun t => ((hdiff t).hasFDerivAt).comp_hasDerivAt t (StepDecompN_hasDerivAt_add_smul M y t)
  have hk : ∀ t : ℝ, HasDerivAt (fun t' : ℝ => fderiv ℝ Φ (M + t' • y) y)
      (fderiv ℝ (fderiv ℝ Φ) (M + t • y) y y) t := by
    intro t
    have h1 := (StepDecompN_hasFDerivAt_fderiv_apply (hdiff2 t) y).comp_hasDerivAt t
      (StepDecompN_hasDerivAt_add_smul M y t)
    simp only [ContinuousLinearMap.flip_apply] at h1
    exact h1
  set k : ℝ → ℂ := fun t => fderiv ℝ Φ (M + t • y) y with hk_def
  have hkCont : Continuous k := continuous_iff_continuousAt.2 fun t => (hk t).continuousAt
  have hlevel1 : ∀ t ∈ Set.Icc (0 : ℝ) s, ‖k t - k 0‖ ≤ C₂ * ‖y‖ ^ 2 * (t - 0) :=
    norm_image_sub_le_of_norm_deriv_right_le_segment
      hkCont.continuousOn (fun t _ => (hk t).hasDerivWithinAt)
      (fun t _ => by simpa using hC₂ (M + t • y) y (hH t) hy)
  have hg : ∀ t : ℝ, HasDerivAt (fun t' : ℝ => Φ (M + t' • y) - Φ M - t' • fderiv ℝ Φ M y)
      (k t - k 0) t := by
    intro t
    have h1 := (hp t).sub_const (Φ M)
    have h2 : HasDerivAt (fun t' : ℝ => t' • fderiv ℝ Φ M y) (fderiv ℝ Φ M y) t := by
      simpa using (hasDerivAt_id t).smul_const (fderiv ℝ Φ M y)
    have h3 := h1.sub h2
    have hk0 : k 0 = fderiv ℝ Φ M y := by simp [hk_def]
    rw [hk0]
    exact h3
  set g : ℝ → ℂ := fun t' => Φ (M + t' • y) - Φ M - t' • fderiv ℝ Φ M y with hg_def
  have hgCont : Continuous g := continuous_iff_continuousAt.2 fun t => (hg t).continuousAt
  set B : ℝ → ℝ := fun t => (C₂ / 2) * ‖y‖ ^ 2 * t ^ 2 with hB_def
  have hB : ∀ t : ℝ, HasDerivAt B (C₂ * ‖y‖ ^ 2 * t) t := by
    intro t
    have h1 : HasDerivAt (fun t' : ℝ => t' ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h2 := h1.const_mul (C₂ / 2 * ‖y‖ ^ 2)
    have heq : C₂ / 2 * ‖y‖ ^ 2 * (2 * t) = C₂ * ‖y‖ ^ 2 * t := by ring
    rw [heq] at h2
    exact h2
  have ha0 : ‖g 0‖ ≤ B 0 := by simp [hg_def, hB_def]
  have hfinal := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    hgCont.continuousOn (fun t _ => (hg t).hasDerivWithinAt) ha0 hB
    (fun t ht => by simpa using hlevel1 t ⟨ht.1, ht.2.le⟩)
  have hgs := hfinal (Set.right_mem_Icc.2 hs)
  simp only [hg_def, hB_def] at hgs
  have heq : C₂ / 2 * ‖y‖ ^ 2 * s ^ 2 = C₂ / 2 * s ^ 2 * ‖y‖ ^ 2 := by ring
  linarith [hgs, heq]

end Taylor

/-! ## 3. The per-step lemmas (complex kernel, general label type) -/

section PerStep

variable {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*} [Fintype ι]
  {Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}

/-- The grid walk is measurable as a matrix-valued map. -/
private theorem StepDecompN_measurable_pathH (k : ℕ) :
    Measurable fun ω : PathΩ sz => pathH sz s t K n k ω :=
  (pathH_measurable_filt sz s t K n k).mono ((filt sz).le k) le_rfl

private theorem StepDecompN_measurable_seqXmat (i : ℕ) :
    Measurable fun ω : PathΩ sz => Sizes.seqXmat sz n (ω i) :=
  ((continuous_Xmat d (sz.L n) (sz.W n)).measurable.comp (Sizes.measurable_slice sz n)).comp
    (measurable_pi_apply i)

/-- The grid recursion `H_{k+1} = H_k + √Δ X_{k+1}` with the real scalar (merged `pathH_succ`,
`Path/LoopStep.lean:48`, has the complex scalar). -/
private theorem StepDecompN_pathH_succ (k : ℕ) (ω : PathΩ sz) :
    pathH sz s t K n (k + 1) ω
      = pathH sz s t K n k ω + Real.sqrt (gridStep s t K n) • Sizes.seqXmat sz n (ω (k + 1)) := by
  rw [pathH_succ, Complex.coe_smul]

/-- `Ψ` along the walk is `filt sz k`-measurable (merged `StepDecomp_measurable_phi_filt`). -/
private theorem StepDecompN_measurable_phi_filt
    {Ψ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (hΨ : HermTestFun sz n Ψ) (k : ℕ) :
    Measurable[filt sz k] fun ω : PathΩ sz => Ψ (pathH sz s t K n k ω) := by
  have hcont := (StepDecompN_contDiff_comp hΨ.contDiffAt).continuous
  have heq : (fun ω : PathΩ sz => Ψ (pathH sz s t K n k ω))
      = fun ω => Ψ (StepDecompN_hermCLM _ (pathH sz s t K n k ω)) := funext fun ω => by
    rw [StepDecompN_hermCLM_of_isHermitian (pathH_isHermitian sz s t K n k ω)]
  rw [heq]
  exact hcont.measurable.comp (pathH_measurable_filt sz s t K n k)

/-- `Ψ` along the walk is integrable: measurable and bounded by (H2) (merged
`StepDecomp_integrable_phi`). -/
private theorem StepDecompN_integrable_phi
    {Ψ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (hΨ : HermTestFun sz n Ψ) (k : ℕ) :
    Integrable (fun ω : PathΩ sz => Ψ (pathH sz s t K n k ω)) (pathP sz) := by
  obtain ⟨C, hC⟩ := hΨ.bdd₀
  have hm : Measurable fun ω : PathΩ sz => Ψ (pathH sz s t K n k ω) :=
    (StepDecompN_measurable_phi_filt sz s t K n hΨ k).mono ((filt sz).le k) le_rfl
  exact (memLp_top_of_bound hm.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => hC _ (pathH_isHermitian sz s t K n k ω))).integrable le_top

/-- `AbCN` is `filt sz j`-measurable (RBM1D `measurable_AbC`, `Gauss/GridStepDecompC.lean:143`;
merged `StepDecomp_measurable_Ab`): `gradMat` of a member of the Hermitian class is a continuous
function of the Hermitian walk, through the Hermitian projection. -/
private theorem StepDecompN_measurable_AbCN (hΦ : ∀ a, HermTestFun sz n (Φ a)) (U : ι → ι → ℂ)
    (b : ι) : Measurable[filt sz j] (fun ω : PathΩ sz => AbCN sz s t K n j Φ U b ω) := by
  have hgrad : ∀ a, Measurable[filt sz j]
      (fun ω : PathΩ sz => gradMat (Φ a) (pathH sz s t K n j ω)) := by
    intro a
    have hcont := StepDecompN_continuous_gradMat (StepDecompN_contDiff_comp (hΦ a).contDiffAt)
    have heq : (fun ω : PathΩ sz => gradMat (Φ a) (pathH sz s t K n j ω))
        = fun ω => gradMat (fun M' => Φ a (StepDecompN_hermCLM _ M')) (pathH sz s t K n j ω) :=
      funext fun ω => (StepDecompN_gradMat_comp (pathH_isHermitian sz s t K n j ω)
        (((hΦ a).contDiffAt _ (pathH_isHermitian sz s t K n j ω)).differentiableAt
          (by norm_num))).symm
    rw [heq]
    exact hcont.measurable.comp (pathH_measurable_filt sz s t K n j)
  exact Finset.measurable_sum _ fun a _ => (hgrad a).const_smul (U b a)

/-- **`Rlabel`**: the per-label Taylor remainder of one grid step,
`Φ(H_{j+1}) - Φ(H_j) - √Δ · fderiv ℝ Φ (H_j) X_{j+1}` (RBM1D `Rlabel`,
`Gauss/GridStepDecomp.lean:559`; merged `StepDecomp_Rlabel`). -/
private def StepDecompN_Rlabel
    (Ψ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ) (ω : PathΩ sz) : ℂ :=
  Ψ (pathH sz s t K n (j + 1) ω) - Ψ (pathH sz s t K n j ω)
    - Real.sqrt (gridStep s t K n) •
      fderiv ℝ Ψ (pathH sz s t K n j ω) (Sizes.seqXmat sz n (ω (j + 1)))

/-- The pathwise Taylor remainder bound, from (H1) and the Hermitian-direction bound (H3). -/
private theorem StepDecompN_norm_Rlabel_le
    {Ψ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ} (hΨ : HermTestFun sz n Ψ)
    {C₂ : ℝ} (hC₂ : ∀ M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ Ψ) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n) (ω : PathΩ sz) :
    ‖StepDecompN_Rlabel sz s t K n j Ψ ω‖
      ≤ (C₂ / 2) * gridStep s t K n * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 := by
  unfold StepDecompN_Rlabel
  rw [StepDecompN_pathH_succ]
  have hkey := StepDecompN_taylor hΨ.contDiffAt hC₂ (pathH_isHermitian sz s t K n j ω)
    (Sizes.seqXmat_isHermitian sz n (ω (j + 1))) (Real.sqrt_nonneg (gridStep s t K n))
  rwa [Real.sq_sqrt hΔ] at hkey

private theorem StepDecompN_measurable_Rlabel
    {Ψ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ} (hΨ : HermTestFun sz n Ψ) :
    Measurable (StepDecompN_Rlabel sz s t K n j Ψ) := by
  have h1 := (StepDecompN_measurable_phi_filt sz s t K n hΨ (j + 1)).mono
    ((filt sz).le (j + 1)) le_rfl
  have h2 := (StepDecompN_measurable_phi_filt sz s t K n hΨ j).mono ((filt sz).le j) le_rfl
  have hcont : Continuous fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ
      × Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      fderiv ℝ (fun M' => Ψ (StepDecompN_hermCLM _ M')) p.1 p.2 :=
    (((StepDecompN_contDiff_comp hΨ.contDiffAt).continuous_fderiv (by norm_num)).comp
      continuous_fst).clm_apply continuous_snd
  have h3 : Measurable fun ω : PathΩ sz =>
      fderiv ℝ Ψ (pathH sz s t K n j ω) (Sizes.seqXmat sz n (ω (j + 1))) := by
    have heq : (fun ω : PathΩ sz =>
        fderiv ℝ Ψ (pathH sz s t K n j ω) (Sizes.seqXmat sz n (ω (j + 1))))
        = fun ω => fderiv ℝ (fun M' => Ψ (StepDecompN_hermCLM _ M')) (pathH sz s t K n j ω)
            (Sizes.seqXmat sz n (ω (j + 1))) := funext fun ω =>
      (StepDecompN_fderiv_comp (pathH_isHermitian sz s t K n j ω)
        ((hΨ.contDiffAt _ (pathH_isHermitian sz s t K n j ω)).differentiableAt (by norm_num))
        (Sizes.seqXmat_isHermitian sz n (ω (j + 1)))).symm
    rw [heq]
    exact hcont.measurable.comp
      ((StepDecompN_measurable_pathH sz s t K n j).prodMk
        (StepDecompN_measurable_seqXmat sz n (j + 1)))
  unfold StepDecompN_Rlabel
  simp only [Complex.real_smul]
  exact (h1.sub h2).sub (h3.const_mul _)

/-- **The pathwise bound on the `U`-weighted sum of Taylor remainders**, complex `U`: `O(Δ)` in
`‖X_{j+1}‖²` with the constant `(Σ_a ‖U(b,a)‖)(C₂/2)` (RBM1D `norm_RlabelC_sum_le`, `:238`). -/
private theorem StepDecompN_norm_Rlabel_sum_le (hΦ : ∀ a, HermTestFun sz n (Φ a)) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n) (U : ι → ι → ℂ) (b : ι) (ω : PathΩ sz) :
    ‖∑ a, U b a * StepDecompN_Rlabel sz s t K n j (Φ a) ω‖
      ≤ (∑ a, ‖U b a‖) * ((C₂ / 2) * gridStep s t K n) * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 := by
  calc ‖∑ a, U b a * StepDecompN_Rlabel sz s t K n j (Φ a) ω‖
      ≤ ∑ a, ‖U b a * StepDecompN_Rlabel sz s t K n j (Φ a) ω‖ := norm_sum_le _ _
    _ = ∑ a, ‖U b a‖ * ‖StepDecompN_Rlabel sz s t K n j (Φ a) ω‖ :=
        Finset.sum_congr rfl fun a _ => norm_mul _ _
    _ ≤ ∑ a, ‖U b a‖ * ((C₂ / 2) * gridStep s t K n
          * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2) := by
        refine Finset.sum_le_sum fun a _ => ?_
        exact mul_le_mul_of_nonneg_left
          (StepDecompN_norm_Rlabel_le sz s t K n j (hΦ a) (hC₂ a) hΔ ω) (norm_nonneg _)
    _ = (∑ a, ‖U b a‖) * ((C₂ / 2) * gridStep s t K n)
          * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by ring

/-- The `U`-weighted sum of Taylor remainders is integrable (RBM1D `integrable_RlabelC_sum`,
`:260`): measurable and dominated by a multiple of the integrable `‖X_{j+1}‖²`. -/
private theorem StepDecompN_integrable_Rlabel_sum (hΦ : ∀ a, HermTestFun sz n (Φ a)) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n) (U : ι → ι → ℂ) (b : ι) :
    Integrable (fun ω : PathΩ sz => ∑ a, U b a * StepDecompN_Rlabel sz s t K n j (Φ a) ω)
      (pathP sz) := by
  have hmeas : Measurable fun ω : PathΩ sz =>
      ∑ a, U b a * StepDecompN_Rlabel sz s t K n j (Φ a) ω :=
    Finset.measurable_sum _ fun a _ =>
      (StepDecompN_measurable_Rlabel sz s t K n j (hΦ a)).const_mul _
  have hgint : Integrable (fun ω : PathΩ sz =>
      (∑ a, ‖U b a‖) * ((C₂ / 2) * gridStep s t K n)
        * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2) (pathP sz) :=
    (integrable_normSq_incr sz n j).const_mul _
  exact hgint.mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω =>
      StepDecompN_norm_Rlabel_sum_le sz s t K n j hΦ hC₂ hΔ U b ω)

end PerStep

/-! ## 4. The linear part `stepZCN`: the algebraic bridge and its conditional mean -/

section LinearPart

variable {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*} [Fintype ι]
  {Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}

/-- **The key algebraic fact**: `linTr` at the direction `(-I) • A` reads the imaginary part of
`trace (A * X)` (RBM1D `lin_neg_I_smul_eq_im`, `Gauss/GridStepDecompC.lean:135`).  Together with
`linTr n A X = (trace (A * X)).re` (its definition) this is why `stepZCN` is the whole complex
first-order term, with no reality hypothesis. -/
private theorem StepDecompN_linTr_neg_I_smul
    (A X : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    linTr n ((-Complex.I) • A) X = (Matrix.trace (A * X)).im := by
  unfold linTr
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  ring

/-- **The complex algebraic bridge** (RBM1D `sum_fderivC_eq_stepZC`, `:165`): the `U`-weighted sum
of directional derivatives is `stepZCN`, unconditionally (no reality of `Φ` or `U`). -/
private theorem StepDecompN_sum_fderiv_eq_stepZCN (U : ι → ι → ℂ) (b : ι) (ω : PathΩ sz) :
    (Real.sqrt (gridStep s t K n) : ℂ) *
      (∑ a, U b a * fderiv ℝ (Φ a) (pathH sz s t K n j ω) (Sizes.seqXmat sz n (ω (j + 1))))
      = stepZCN sz s t K n j Φ U b ω := by
  have hXherm := Sizes.seqXmat_isHermitian sz n (ω (j + 1))
  have hcomb : (∑ a, U b a * fderiv ℝ (Φ a) (pathH sz s t K n j ω)
        (Sizes.seqXmat sz n (ω (j + 1))))
      = Matrix.trace (AbCN sz s t K n j Φ U b ω * Sizes.seqXmat sz n (ω (j + 1))) := by
    unfold AbCN
    rw [Matrix.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, fderiv_eq_trace_gradMat _ hXherm]
  rw [hcomb]
  set w := Matrix.trace (AbCN sz s t K n j Φ U b ω * Sizes.seqXmat sz n (ω (j + 1))) with hw
  have hre : linTr n (AbCN sz s t K n j Φ U b ω) (Sizes.seqXmat sz n (ω (j + 1))) = w.re := rfl
  have him : linTr n ((-Complex.I) • AbCN sz s t K n j Φ U b ω)
      (Sizes.seqXmat sz n (ω (j + 1))) = w.im := StepDecompN_linTr_neg_I_smul sz n _ _
  unfold stepZCN stepZCN_re stepZCN_im
  rw [hre, him]
  have hreim := Complex.re_add_im w
  push_cast
  linear_combination (Real.sqrt (gridStep s t K n) : ℂ) * hreim.symm

/-- **The pointwise identity** (RBM1D `g_eq_pointwiseC`, `:193`): `Σ_a U(b,a) Φ_a(H_{j+1})` splits
into the `F_j`-measurable term, `stepZCN`, and the `U`-weighted Taylor remainder. -/
private theorem StepDecompN_g_eq_pointwise (U : ι → ι → ℂ) (b : ι) (ω : PathΩ sz) :
    (∑ a, U b a * Φ a (pathH sz s t K n (j + 1) ω))
      = (∑ a, U b a * Φ a (pathH sz s t K n j ω))
        + stepZCN sz s t K n j Φ U b ω
        + ∑ a, U b a * StepDecompN_Rlabel sz s t K n j (Φ a) ω := by
  have hZ := StepDecompN_sum_fderiv_eq_stepZCN sz s t K n j (Φ := Φ) U b ω
  have hexpand : ∀ a,
      U b a * Φ a (pathH sz s t K n (j + 1) ω)
        = U b a * Φ a (pathH sz s t K n j ω)
          + (Real.sqrt (gridStep s t K n) : ℂ) *
              (U b a * fderiv ℝ (Φ a) (pathH sz s t K n j ω) (Sizes.seqXmat sz n (ω (j + 1))))
          + U b a * StepDecompN_Rlabel sz s t K n j (Φ a) ω := by
    intro a
    have hR : StepDecompN_Rlabel sz s t K n j (Φ a) ω
        = Φ a (pathH sz s t K n (j + 1) ω) - Φ a (pathH sz s t K n j ω)
          - (Real.sqrt (gridStep s t K n) : ℂ) *
            fderiv ℝ (Φ a) (pathH sz s t K n j ω) (Sizes.seqXmat sz n (ω (j + 1))) := by
      unfold StepDecompN_Rlabel; rw [Complex.real_smul]
    rw [hR]; ring
  rw [Finset.sum_congr rfl fun a _ => hexpand a, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hZ]

/-- `h0 := Σ_a U(b,a)·Φ_a(H_j ω)` is `filt sz j`-measurable (RBM1D `measurable_h0C`, `:218`). -/
private theorem StepDecompN_measurable_h0 (hΦ : ∀ a, HermTestFun sz n (Φ a)) (U : ι → ι → ℂ)
    (b : ι) :
    Measurable[filt sz j] (fun ω : PathΩ sz => ∑ a, U b a * Φ a (pathH sz s t K n j ω)) :=
  Finset.measurable_sum _ fun a _ =>
    (StepDecompN_measurable_phi_filt sz s t K n (hΦ a) j).const_mul (U b a)

/-- `h0` is integrable: a finite sum of bounded functions (RBM1D `integrable_h0C`, `:229`). -/
private theorem StepDecompN_integrable_h0 (hΦ : ∀ a, HermTestFun sz n (Φ a)) (U : ι → ι → ℂ)
    (b : ι) :
    Integrable (fun ω : PathΩ sz => ∑ a, U b a * Φ a (pathH sz s t K n j ω)) (pathP sz) :=
  integrable_finsetSum _ fun a _ =>
    (StepDecompN_integrable_phi sz s t K n (hΦ a) j).const_mul (U b a)

/-- `stepZCN`, as a complex-valued function, is integrable given integrability of its real and
imaginary parts (RBM1D `integrable_stepZC`, `:279`). -/
private theorem StepDecompN_integrable_stepZCN (U : ι → ι → ℂ) (b : ι)
    (hIntRe : Integrable (stepZCN_re sz s t K n j Φ U b) (pathP sz))
    (hIntIm : Integrable (stepZCN_im sz s t K n j Φ U b) (pathP sz)) :
    Integrable (stepZCN sz s t K n j Φ U b) (pathP sz) := by
  have h1 : Integrable (fun ω => (stepZCN_re sz s t K n j Φ U b ω : ℂ)) (pathP sz) := hIntRe.ofReal
  have h2 : Integrable (fun ω => (stepZCN_im sz s t K n j Φ U b ω : ℂ)) (pathP sz) := hIntIm.ofReal
  have h3 : Integrable (fun ω => Complex.I * (stepZCN_im sz s t K n j Φ U b ω : ℂ)) (pathP sz) :=
    h2.const_mul Complex.I
  have heq : stepZCN sz s t K n j Φ U b
      = (fun ω => (stepZCN_re sz s t K n j Φ U b ω : ℂ))
        + (fun ω => Complex.I * (stepZCN_im sz s t K n j Φ U b ω : ℂ)) := by
    funext ω; rfl
  rw [heq]; exact h1.add h3

/-- **`stepZCN` has conditional mean zero** (RBM1D `condExp_stepZC_eq_zero`, `:297`): the merged
`condExp_linear_eq_zero` applied to the real direction `AbCN` and to `(-I) • AbCN`, recombined via
`condExp_add`/`condExp_smul`. -/
private theorem StepDecompN_condExp_stepZCN_eq_zero (hΦ : ∀ a, HermTestFun sz n (Φ a))
    (U : ι → ι → ℂ) (b : ι)
    (hIntRe : Integrable (stepZCN_re sz s t K n j Φ U b) (pathP sz))
    (hIntIm : Integrable (stepZCN_im sz s t K n j Φ U b) (pathP sz)) :
    (pathP sz)[stepZCN sz s t K n j Φ U b | filt sz j] =ᵐ[pathP sz] fun _ => (0 : ℂ) := by
  have hAmeas := StepDecompN_measurable_AbCN sz s t K n j hΦ U b
  have hAmeas' : Measurable[filt sz j]
      (fun ω => (-Complex.I) • AbCN sz s t K n j Φ U b ω) := hAmeas.const_smul (-Complex.I)
  have hrealRe : (pathP sz)[stepZCN_re sz s t K n j Φ U b | filt sz j]
      =ᵐ[pathP sz] fun _ => (0 : ℝ) := by
    have h := condExp_linear_eq_zero s t K n j hAmeas Set.univ MeasurableSet.univ
      (show Integrable (fun ω => Real.sqrt (gridStep s t K n)
        * linTr n (AbCN sz s t K n j Φ U b ω) (Sizes.seqXmat sz n (ω (j + 1)))) (pathP sz)
        from hIntRe)
    rwa [Set.indicator_univ] at h
  have hrealIm : (pathP sz)[stepZCN_im sz s t K n j Φ U b | filt sz j]
      =ᵐ[pathP sz] fun _ => (0 : ℝ) := by
    have h := condExp_linear_eq_zero s t K n j hAmeas' Set.univ MeasurableSet.univ
      (show Integrable (fun ω => Real.sqrt (gridStep s t K n)
        * linTr n ((-Complex.I) • AbCN sz s t K n j Φ U b ω)
          (Sizes.seqXmat sz n (ω (j + 1)))) (pathP sz) from hIntIm)
    rwa [Set.indicator_univ] at h
  have hliftRe := ContinuousLinearMap.comp_condExp_comm (μ := pathP sz) (m := filt sz j)
    hIntRe Complex.ofRealCLM
  have hliftRe' : (fun ω => (((pathP sz)[stepZCN_re sz s t K n j Φ U b | filt sz j] ω : ℝ) : ℂ))
      =ᵐ[pathP sz] (pathP sz)[fun ω => (stepZCN_re sz s t K n j Φ U b ω : ℂ) | filt sz j] := by
    simpa [Function.comp_def] using hliftRe
  have hliftIm := ContinuousLinearMap.comp_condExp_comm (μ := pathP sz) (m := filt sz j)
    hIntIm Complex.ofRealCLM
  have hliftIm' : (fun ω => (((pathP sz)[stepZCN_im sz s t K n j Φ U b | filt sz j] ω : ℝ) : ℂ))
      =ᵐ[pathP sz] (pathP sz)[fun ω => (stepZCN_im sz s t K n j Φ U b ω : ℂ) | filt sz j] := by
    simpa [Function.comp_def] using hliftIm
  have hReC : (pathP sz)[fun ω => (stepZCN_re sz s t K n j Φ U b ω : ℂ) | filt sz j]
      =ᵐ[pathP sz] fun _ => (0 : ℂ) := by
    refine hliftRe'.symm.trans ?_
    filter_upwards [hrealRe] with ω hω
    simp [hω]
  have hImC : (pathP sz)[fun ω => (stepZCN_im sz s t K n j Φ U b ω : ℂ) | filt sz j]
      =ᵐ[pathP sz] fun _ => (0 : ℂ) := by
    refine hliftIm'.symm.trans ?_
    filter_upwards [hrealIm] with ω hω
    simp [hω]
  have heq : stepZCN sz s t K n j Φ U b
      = (fun ω => (stepZCN_re sz s t K n j Φ U b ω : ℂ))
        + Complex.I • (fun ω => (stepZCN_im sz s t K n j Φ U b ω : ℂ)) := by
    funext ω; rfl
  rw [heq]
  have hIntImC : Integrable (fun ω => (stepZCN_im sz s t K n j Φ U b ω : ℂ)) (pathP sz) :=
    hIntIm.ofReal
  have hIntReC : Integrable (fun ω => (stepZCN_re sz s t K n j Φ U b ω : ℂ)) (pathP sz) :=
    hIntRe.ofReal
  have hIntSmul :
      Integrable (Complex.I • (fun ω => (stepZCN_im sz s t K n j Φ U b ω : ℂ))) (pathP sz) :=
    hIntImC.smul Complex.I
  have hAddCond := condExp_add hIntReC hIntSmul (filt sz j)
  have hSmulCond := condExp_smul (μ := pathP sz) Complex.I
    (fun ω => (stepZCN_im sz s t K n j Φ U b ω : ℂ)) (filt sz j)
  refine hAddCond.trans ?_
  filter_upwards [hReC, hSmulCond, hImC] with ω h1 h2 h3
  simp only [Pi.add_apply]
  rw [h1, h2]
  simp [h3]

end LinearPart

/-! ## 5. The decomposition `ξ = Z + Y` of one grid step -/

section Decomposition

variable {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*} [Fintype ι]
  {Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}

/-- **The a.e. identity behind `stepDecompCN`** (RBM1D `stepXiC_eq_ae`, `:358`): `ξ` agrees a.e. with
`Z` plus the `U`-weighted Taylor-remainder martingale difference. -/
private theorem StepDecompN_stepXiCN_eq_ae (hΦ : ∀ a, HermTestFun sz n (Φ a)) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n) (U : ι → ι → ℂ) (b : ι)
    (hIntRe : Integrable (stepZCN_re sz s t K n j Φ U b) (pathP sz))
    (hIntIm : Integrable (stepZCN_im sz s t K n j Φ U b) (pathP sz)) :
    stepXiCN sz s t K n j Φ U b
      =ᵐ[pathP sz] fun ω => stepZCN sz s t K n j Φ U b ω
        + ((∑ a, U b a * StepDecompN_Rlabel sz s t K n j (Φ a) ω)
          - (pathP sz)[fun ω' => ∑ a, U b a * StepDecompN_Rlabel sz s t K n j (Φ a) ω'
              | filt sz j] ω) := by
  set h0 : PathΩ sz → ℂ := fun ω => ∑ a, U b a * Φ a (pathH sz s t K n j ω) with hh0def
  set R : PathΩ sz → ℂ :=
    fun ω => ∑ a, U b a * StepDecompN_Rlabel sz s t K n j (Φ a) ω with hRdef
  set Zc : PathΩ sz → ℂ := stepZCN sz s t K n j Φ U b with hZcdef
  set g : PathΩ sz → ℂ := fun ω => ∑ a, U b a * Φ a (pathH sz s t K n (j + 1) ω) with hgdef
  have hgeq : g = h0 + Zc + R :=
    funext fun ω => StepDecompN_g_eq_pointwise sz s t K n j (Φ := Φ) U b ω
  have hh0meas := StepDecompN_measurable_h0 sz s t K n j hΦ U b
  have hh0int := StepDecompN_integrable_h0 sz s t K n j hΦ U b
  have hZcint := StepDecompN_integrable_stepZCN sz s t K n j U b hIntRe hIntIm
  have hRint := StepDecompN_integrable_Rlabel_sum sz s t K n j hΦ hC₂ hΔ U b
  have hcondg : (pathP sz)[g | filt sz j]
      =ᵐ[pathP sz] (pathP sz)[h0 | filt sz j] + (pathP sz)[Zc | filt sz j]
        + (pathP sz)[R | filt sz j] := by
    rw [hgeq]
    exact (condExp_add (hh0int.add hZcint) hRint (filt sz j)).trans
      ((condExp_add hh0int hZcint (filt sz j)).add (EventuallyEq.refl _ _))
  have hh0cond : (pathP sz)[h0 | filt sz j] =ᵐ[pathP sz] h0 := by
    rw [condExp_of_stronglyMeasurable ((filt sz).le j) hh0meas.stronglyMeasurable hh0int]
  have hZccond : (pathP sz)[Zc | filt sz j] =ᵐ[pathP sz] fun _ => (0 : ℂ) :=
    StepDecompN_condExp_stepZCN_eq_zero sz s t K n j hΦ U b hIntRe hIntIm
  have hstepXi : stepXiCN sz s t K n j Φ U b = fun ω => g ω - (pathP sz)[g | filt sz j] ω := rfl
  rw [hstepXi]
  filter_upwards [hcondg, hh0cond, hZccond] with ω hω1 hω2 hω3
  have hω1' : (pathP sz)[g | filt sz j] ω = h0 ω + (pathP sz)[R | filt sz j] ω := by
    rw [hω1]; simp only [Pi.add_apply, hω2, hω3, add_zero]
  rw [hω1']
  have hgω : g ω = h0 ω + Zc ω + R ω := by rw [hgeq]; rfl
  rw [hgω]
  ring

/-- **`stepYCN` a.e. equals the `U`-weighted Taylor remainder minus its own conditional mean**
(RBM1D `stepYC_eq_ae`, `:400`). -/
private theorem StepDecompN_stepYCN_eq_ae (hΦ : ∀ a, HermTestFun sz n (Φ a)) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n) (U : ι → ι → ℂ) (b : ι)
    (hIntRe : Integrable (stepZCN_re sz s t K n j Φ U b) (pathP sz))
    (hIntIm : Integrable (stepZCN_im sz s t K n j Φ U b) (pathP sz)) :
    stepYCN sz s t K n j Φ U b
      =ᵐ[pathP sz] fun ω => (∑ a, U b a * StepDecompN_Rlabel sz s t K n j (Φ a) ω)
        - (pathP sz)[fun ω' => ∑ a, U b a * StepDecompN_Rlabel sz s t K n j (Φ a) ω'
            | filt sz j] ω := by
  have hXi := StepDecompN_stepXiCN_eq_ae sz s t K n j hΦ hC₂ hΔ U b hIntRe hIntIm
  filter_upwards [hXi] with ω hω
  change stepXiCN sz s t K n j Φ U b ω - stepZCN sz s t K n j Φ U b ω = _
  rw [hω]; ring

/-- **The pathwise bound on `Y`, a.e.** (RBM1D `stepYC_norm_le_ae`, `:419`):
`‖Y b ω‖ ≤ g + E[g | F_j]`, `g = (Σ_a ‖U(b,a)‖)(C₂/2)Δ‖X_{j+1}‖²`. -/
private theorem StepDecompN_stepYCN_norm_le_ae (hΦ : ∀ a, HermTestFun sz n (Φ a)) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n) (U : ι → ι → ℂ) (b : ι)
    (hIntRe : Integrable (stepZCN_re sz s t K n j Φ U b) (pathP sz))
    (hIntIm : Integrable (stepZCN_im sz s t K n j Φ U b) (pathP sz)) :
    ∀ᵐ ω ∂(pathP sz), ‖stepYCN sz s t K n j Φ U b ω‖
      ≤ (∑ a, ‖U b a‖) * ((C₂ / 2) * gridStep s t K n) * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2
        + (pathP sz)[fun ω' => (∑ a, ‖U b a‖) * ((C₂ / 2) * gridStep s t K n)
            * ‖Sizes.seqXmat sz n (ω' (j + 1))‖ ^ 2 | filt sz j] ω := by
  have hY := StepDecompN_stepYCN_eq_ae sz s t K n j hΦ hC₂ hΔ U b hIntRe hIntIm
  set R : PathΩ sz → ℂ :=
    fun ω => ∑ a, U b a * StepDecompN_Rlabel sz s t K n j (Φ a) ω with hRdef
  set g : PathΩ sz → ℝ := fun ω => (∑ a, ‖U b a‖) * ((C₂ / 2) * gridStep s t K n)
      * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 with hgdef
  have hRnorm : ∀ ω, ‖R ω‖ ≤ g ω :=
    fun ω => StepDecompN_norm_Rlabel_sum_le sz s t K n j hΦ hC₂ hΔ U b ω
  have hgint : Integrable g (pathP sz) := (integrable_normSq_incr sz n j).const_mul _
  have hRint : Integrable R (pathP sz) :=
    StepDecompN_integrable_Rlabel_sum sz s t K n j hΦ hC₂ hΔ U b
  have hcondRmono : (pathP sz)[fun ω => ‖R ω‖ | filt sz j] ≤ᵐ[pathP sz] (pathP sz)[g | filt sz j] :=
    condExp_mono hRint.norm hgint (Filter.Eventually.of_forall hRnorm)
  have hnormcond : (fun x => ‖(pathP sz)[R | filt sz j] x‖)
      ≤ᵐ[pathP sz] (pathP sz)[fun x => ‖R x‖ | filt sz j] :=
    _root_.norm_condExp_le R
  filter_upwards [hY, hcondRmono, hnormcond] with ω hω h2 h3
  rw [hω]
  calc ‖R ω - (pathP sz)[R | filt sz j] ω‖
      ≤ ‖R ω‖ + ‖(pathP sz)[R | filt sz j] ω‖ := norm_sub_le _ _
    _ ≤ g ω + (pathP sz)[g | filt sz j] ω := add_le_add (hRnorm ω) (le_trans h3 h2)

end Decomposition

/-- **`stepDecompCN`: the complex one-step decomposition of a loop observable** (RBM1D
`stepDecompC`, `Gauss/GridStepDecompC.lean:455`, at `c06b103`; the class change is `HermTestFun`
and the Hermitian-direction bound `hC₂`, as in the merged real `stepDecomp`,
`Path/StepDecomp.lean:1160`).  (i) `ξ_b = Z_b + Y_b` pointwise; (ii) `AbCN` is
`filt sz j`-measurable; (iii) a.e., `‖Y_b‖ ≤ g + E[g | F_j]` with
`g = (Σ_a ‖U(b,a)‖) ((C₂/2) Δ) ‖X_{j+1}‖²`; (iv) `E[Y_b | F_j] = 0`.  No reality hypothesis on
`Φ` or `U`: the imaginary part of the first-order term is `stepZCN_im`. -/
theorem stepDecompCN {d : ℕ} (sz : Sizes d) : StepDecompCN_Stmt sz := by
  intro s t K n j ι _ Φ hΦ C₂ hC₂ hΔ U b hIntRe hIntIm
  refine ⟨fun ω => by unfold stepYCN; ring, StepDecompN_measurable_AbCN sz s t K n j hΦ U b,
    StepDecompN_stepYCN_norm_le_ae sz s t K n j hΦ hC₂ hΔ U b hIntRe hIntIm, ?_⟩
  have hY := StepDecompN_stepYCN_eq_ae sz s t K n j hΦ hC₂ hΔ U b hIntRe hIntIm
  have hRint := StepDecompN_integrable_Rlabel_sum sz s t K n j hΦ hC₂ hΔ U b
  have hcond : (pathP sz)[fun ω => ∑ a, U b a * StepDecompN_Rlabel sz s t K n j (Φ a) ω
        - (pathP sz)[fun ω' => ∑ a, U b a * StepDecompN_Rlabel sz s t K n j (Φ a) ω'
            | filt sz j] ω | filt sz j]
      =ᵐ[pathP sz] fun _ => (0 : ℂ) := by
    set R : PathΩ sz → ℂ :=
      fun ω => ∑ a, U b a * StepDecompN_Rlabel sz s t K n j (Φ a) ω with hRdef
    have hsub := condExp_sub hRint (integrable_condExp (f := R) (m := filt sz j)) (filt sz j)
    have hidem : (pathP sz)[(pathP sz)[R | filt sz j] | filt sz j]
        =ᵐ[pathP sz] (pathP sz)[R | filt sz j] :=
      condExp_condExp_of_le (le_refl (filt sz j)) ((filt sz).le j)
    have hfe : (fun ω => ∑ a, U b a * StepDecompN_Rlabel sz s t K n j (Φ a) ω
        - (pathP sz)[R | filt sz j] ω) = R - (pathP sz)[R | filt sz j] := by
      funext ω
      change R ω - (pathP sz)[R | filt sz j] ω = (R - (pathP sz)[R | filt sz j]) ω
      rw [Pi.sub_apply]
    rw [hfe]
    filter_upwards [hsub, hidem] with ω hω1 hω2
    rw [hω1]
    simp only [Pi.sub_apply]
    rw [hω2]
    ring
  exact (condExp_congr_ae hY).trans hcond

/-! ## 6. Sub-Gaussianity of `Z`, integrability, and the `L²` bound on `Y` -/

/-- **`stepDecompCN_Z_subG`: the real and imaginary parts of `Z` are conditionally sub-Gaussian**
(RBM1D `stepDecompC_ZC_subG`, `Gauss/GridStepDecompC.lean:502`; merged
`stepDecomp_Z_subG`, `Path/StepDecomp.lean:1273`, with `hasCondSubgaussianMGF_linear`,
`Path/Markov.lean:628`, `linTrVar` in place of RBM1D `v`): on a `filt sz j`-measurable set `E` where
`Δ · linTrVar (AbCN ω) ≤ c` and `Δ · linTrVar ((-I) • AbCN ω) ≤ c`, both `E.indicator stepZCN_re`
and `E.indicator stepZCN_im` are conditionally sub-Gaussian with the same parameter `c`. -/
theorem stepDecompCN_Z_subG {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*}
    [Fintype ι]
    {Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (hΦ : ∀ a, HermTestFun sz n (Φ a)) (U : ι → ι → ℂ) (b : ι)
    (E : Set (PathΩ sz)) (hE : MeasurableSet[filt sz j] E) (c : ℝ) (hc : 0 ≤ c)
    (hboundRe : ∀ ω ∈ E, gridStep s t K n * linTrVar n (AbCN sz s t K n j Φ U b ω) ≤ c)
    (hboundIm : ∀ ω ∈ E,
      gridStep s t K n * linTrVar n ((-Complex.I) • AbCN sz s t K n j Φ U b ω) ≤ c) :
    HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
      (fun ω => E.indicator (fun ω => stepZCN_re sz s t K n j Φ U b ω) ω) ⟨c, hc⟩ (pathP sz)
    ∧ HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
      (fun ω => E.indicator (fun ω => stepZCN_im sz s t K n j Φ U b ω) ω) ⟨c, hc⟩ (pathP sz) := by
  refine ⟨?_, ?_⟩
  · have h := hasCondSubgaussianMGF_linear (sz := sz) s t K n j
      (StepDecompN_measurable_AbCN sz s t K n j hΦ U b) E hE c hc hboundRe
    simpa only [stepZCN_re] using h
  · have hAmeas' : Measurable[filt sz j] (fun ω => (-Complex.I) • AbCN sz s t K n j Φ U b ω) :=
      (StepDecompN_measurable_AbCN sz s t K n j hΦ U b).const_smul (-Complex.I)
    have h := hasCondSubgaussianMGF_linear (sz := sz) s t K n j hAmeas' E hE c hc hboundIm
    simpa only [stepZCN_im] using h

/-- **`stepZCN` is integrable, unconditionally** (RBM1D `integrable_stepZC_of_testFun`, `:524`):
`stepZCN = Σ_a U Φ_a(H_{j+1}) - Σ_a U Φ_a(H_j) - Σ_a U R_a` (`StepDecompN_g_eq_pointwise`) with
all three terms integrable. -/
private theorem StepDecompN_integrable_stepZCN_of_hermTestFun {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ)
    (K : ℕ → ℕ) (n j : ℕ) {ι : Type*} [Fintype ι]
    {Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (hΦ : ∀ a, HermTestFun sz n (Φ a)) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n) (U : ι → ι → ℂ) (b : ι) :
    Integrable (stepZCN sz s t K n j Φ U b) (pathP sz) := by
  have hg : Integrable (fun ω : PathΩ sz => ∑ a, U b a * Φ a (pathH sz s t K n (j + 1) ω))
      (pathP sz) :=
    integrable_finsetSum _ fun a _ =>
      (StepDecompN_integrable_phi sz s t K n (hΦ a) (j + 1)).const_mul (U b a)
  have h0 := StepDecompN_integrable_h0 sz s t K n j hΦ U b
  have hR := StepDecompN_integrable_Rlabel_sum sz s t K n j hΦ hC₂ hΔ U b
  have heq : stepZCN sz s t K n j Φ U b
      = fun ω => (∑ a, U b a * Φ a (pathH sz s t K n (j + 1) ω))
        - (∑ a, U b a * Φ a (pathH sz s t K n j ω))
        - ∑ a, U b a * StepDecompN_Rlabel sz s t K n j (Φ a) ω := by
    funext ω
    rw [StepDecompN_g_eq_pointwise sz s t K n j (Φ := Φ) U b ω]
    ring
  rw [heq]
  exact (hg.sub h0).sub hR

/-- **`stepZCN_re` is integrable, unconditionally** (RBM1D `integrable_stepZC_re_of_testFun`,
`:546`): discharges the hypothesis `hIntRe` of `stepDecompCN`. -/
theorem integrable_stepZCN_re_of_hermTestFun {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    {ι : Type*} [Fintype ι]
    {Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (hΦ : ∀ a, HermTestFun sz n (Φ a)) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n) (U : ι → ι → ℂ) (b : ι) :
    Integrable (stepZCN_re sz s t K n j Φ U b) (pathP sz) := by
  have h := Complex.reCLM.integrable_comp
    (StepDecompN_integrable_stepZCN_of_hermTestFun sz s t K n j hΦ hC₂ hΔ U b)
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp [stepZCN]

/-- **`stepZCN_im` is integrable, unconditionally** (RBM1D `integrable_stepZC_im_of_testFun`,
`:557`): discharges the hypothesis `hIntIm` of `stepDecompCN`. -/
theorem integrable_stepZCN_im_of_hermTestFun {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    {ι : Type*} [Fintype ι]
    {Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (hΦ : ∀ a, HermTestFun sz n (Φ a)) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n) (U : ι → ι → ℂ) (b : ι) :
    Integrable (stepZCN_im sz s t K n j Φ U b) (pathP sz) := by
  have h := Complex.imCLM.integrable_comp
    (StepDecompN_integrable_stepZCN_of_hermTestFun sz s t K n j hΦ hC₂ hΔ U b)
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp [stepZCN]

/-- **`stepDecompCN_Y_sq`: the `L²` bound on `Y`** (merged `stepDecomp_Y_sq`,
`Path/StepDecomp.lean:1209`, with `Σ_a ‖U(b,a)‖`): `∫ ‖Y_b‖² ≤ 4 ((Σ_a ‖U(b,a)‖) C₂/2)² Δ²
∫ ‖X_{j+1}‖⁴`.  From (iii) of `stepDecompCN`, `(x+y)² ≤ 2x²+2y²`, conditional Jensen at
`x ↦ x²` (`ConvexOn.map_condExp_le_univ`) and the tower property (`integral_condExp`); the
integrability hypotheses of `stepDecompCN` are discharged by
`integrable_stepZCN_re_of_hermTestFun`, `integrable_stepZCN_im_of_hermTestFun`. -/
theorem stepDecompCN_Y_sq {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*}
    [Fintype ι]
    {Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (hΦ : ∀ a, HermTestFun sz n (Φ a)) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n) (U : ι → ι → ℂ) (b : ι) :
    ∫ ω, ‖stepYCN sz s t K n j Φ U b ω‖ ^ 2 ∂(pathP sz)
      ≤ 4 * ((∑ a, ‖U b a‖) * (C₂ / 2)) ^ 2 * (gridStep s t K n) ^ 2
          * ∫ ω, ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 4 ∂(pathP sz) := by
  have hIntRe := integrable_stepZCN_re_of_hermTestFun sz s t K n j hΦ hC₂ hΔ U b
  have hIntIm := integrable_stepZCN_im_of_hermTestFun sz s t K n j hΦ hC₂ hΔ U b
  have hYbound := StepDecompN_stepYCN_norm_le_ae sz s t K n j hΦ hC₂ hΔ U b hIntRe hIntIm
  set g : PathΩ sz → ℝ := fun ω => (∑ a, ‖U b a‖) * ((C₂ / 2) * gridStep s t K n)
      * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 with hgdef
  -- the key algebraic identity behind `g²`, in the exact grouping the target constant needs
  have heqg2 : (fun ω => (g ω) ^ 2)
      = fun ω => (((∑ a, ‖U b a‖) * (C₂ / 2)) ^ 2 * (gridStep s t K n) ^ 2)
        * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 4 := by
    rw [hgdef]; funext ω; ring
  have hgint : Integrable g (pathP sz) := by
    rw [hgdef]
    exact (integrable_normSq_incr sz n j).const_mul
      ((∑ a, ‖U b a‖) * ((C₂ / 2) * gridStep s t K n))
  have hg2int : Integrable (fun ω => (g ω) ^ 2) (pathP sz) := by
    rw [heqg2]
    exact (integrable_normPow4_incr sz n j).const_mul
      (((∑ a, ‖U b a‖) * (C₂ / 2)) ^ 2 * (gridStep s t K n) ^ 2)
  have hg2eq : ∫ ω, (g ω) ^ 2 ∂(pathP sz)
      = ((∑ a, ‖U b a‖) * (C₂ / 2)) ^ 2 * (gridStep s t K n) ^ 2
          * ∫ ω, ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 4 ∂(pathP sz) := by
    rw [heqg2, integral_const_mul]
  -- the conditional Jensen inequality at the convex map `x ↦ x²`
  have hcvx : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) := Even.convexOn_pow even_two
  have hcont : LowerSemicontinuous (fun x : ℝ => x ^ 2) := (continuous_pow 2).lowerSemicontinuous
  have hJensen : (fun ω => ((pathP sz)[g | filt sz j] ω) ^ 2)
      ≤ᵐ[pathP sz] (pathP sz)[fun ω => (g ω) ^ 2 | filt sz j] :=
    hcvx.map_condExp_le_univ ((filt sz).le j) hcont hgint hg2int
  -- combine the pathwise bound with `(x+y)² ≤ 2x²+2y²` and the Jensen bound
  have hcomb : ∀ᵐ ω ∂(pathP sz), ‖stepYCN sz s t K n j Φ U b ω‖ ^ 2
      ≤ 2 * (g ω) ^ 2 + 2 * (pathP sz)[fun ω' => (g ω') ^ 2 | filt sz j] ω := by
    filter_upwards [hYbound, hJensen] with ω h1 h2
    have hsq : ‖stepYCN sz s t K n j Φ U b ω‖ ^ 2
        ≤ (g ω + (pathP sz)[g | filt sz j] ω) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [hsq, h2, sq_nonneg (g ω - (pathP sz)[g | filt sz j] ω)]
  have hRHSint : Integrable (fun ω => 2 * (g ω) ^ 2
      + 2 * (pathP sz)[fun ω' => (g ω') ^ 2 | filt sz j] ω) (pathP sz) :=
    (hg2int.const_mul 2).add (Integrable.const_mul integrable_condExp 2)
  have hmono := integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
    hRHSint hcomb
  rw [integral_add (hg2int.const_mul 2) (Integrable.const_mul integrable_condExp 2),
    integral_const_mul, integral_const_mul, integral_condExp ((filt sz).le j), hg2eq] at hmono
  have hgoal : (2 : ℝ) * (((∑ a, ‖U b a‖) * (C₂ / 2)) ^ 2
        * (gridStep s t K n) ^ 2 * ∫ ω, ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 4 ∂(pathP sz))
      + 2 * (((∑ a, ‖U b a‖) * (C₂ / 2)) ^ 2
        * (gridStep s t K n) ^ 2 * ∫ ω, ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 4 ∂(pathP sz))
      = 4 * ((∑ a, ‖U b a‖) * (C₂ / 2)) ^ 2 * (gridStep s t K n) ^ 2
        * ∫ ω, ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 4 ∂(pathP sz) := by ring
  linarith [hmono, hgoal]

/-! ## 7. Identification with the merged `martIncN`: `ZvecN`, `YvecN`, `Ugen`

The loop family `loopFamN` at the spectral time `u_{j+1}` is in the Hermitian test class for
`j + 1 ≤ K n`, `|E n| < 2`, `0 ≤ s n ≤ t n`, `t n < 1`: the argument of `hΦ_of_hermTestFunLoopN`
stated per `n`, with the merged theorem `hermTestFunLoopN` (T2111) in place of the pin
`HermTestFunLoopN`, so no test-class hypothesis appears below. -/

section Identification

/-- Grid-time arithmetic (the merged versions in `GridDuhamelN` are private): `0 ≤ u_j`. -/
private theorem StepDecompN_gridTime_nonneg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hs0 : 0 ≤ s n)
    (hst : s n ≤ t n) (j : ℕ) : 0 ≤ gridTime s t K n j := by
  have hΔ : 0 ≤ gridStep s t K n := div_nonneg (sub_nonneg.2 hst) (Nat.cast_nonneg _)
  unfold gridTime
  have : (0 : ℝ) ≤ (j : ℝ) * gridStep s t K n := mul_nonneg (Nat.cast_nonneg _) hΔ
  linarith

/-- `u_{j+1} ≤ t n < 1` for `j + 1 ≤ K n`. -/
private theorem StepDecompN_gridTime_lt_one (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hst : s n ≤ t n)
    {j : ℕ} (hj : j + 1 ≤ K n) (ht1 : t n < 1) : gridTime s t K n (j + 1) < 1 := by
  have hK : K n ≠ 0 := by omega
  have hΔ : 0 ≤ gridStep s t K n := div_nonneg (sub_nonneg.2 hst) (Nat.cast_nonneg _)
  have hlast := gridTime_last s t K n hK
  have hle : gridTime s t K n (j + 1) ≤ gridTime s t K n (K n) := by
    unfold gridTime
    have : ((j + 1 : ℕ) : ℝ) ≤ (K n : ℝ) := Nat.cast_le.2 hj
    nlinarith
  linarith

/-- The loop family is in the Hermitian test class at the spectral time `u_{j+1}` (the per-`n`
form of `hΦ_of_hermTestFunLoopN`, with the merged theorem `hermTestFunLoopN` for the pin).  For
`k = 0` (not covered by the pin) the loop is empty and the observable is the constant `tr 1`. -/
private theorem StepDecompN_loopFam_hermTestFun {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ)
    (n j : ℕ) (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1)
    (hj : j + 1 ≤ K n) {k : ℕ} (σ : Fin k → Bool) (b : Fin k → Zd d (sz.L n)) :
    HermTestFun sz n (loopFamN sz E s t K n j σ b) := by
  have hu0 : 0 ≤ gridTime s t K n (j + 1) := StepDecompN_gridTime_nonneg s t K n hs0 hst (j + 1)
  have hu1 : gridTime s t K n (j + 1) < 1 := StepDecompN_gridTime_lt_one s t K n hst hj ht1
  exact (hermTestFunLoopN sz k n (E n) (gridTime s t K n (j + 1)) hE hu0 hu1 σ b).1

/-- The Hermitian second-derivative bound of the pin `HermTestFunLoopN` for the loop family:
`‖∂²Φ_a(M)[y,y]‖ ≤ k (k + 1) N η_{u_{j+1}}^{-(k+2)} ‖y‖²` at Hermitian `M`, `y` (the hypothesis
`hC₂` of `stepDecompCN` for `loopFamN`, with `C₂ = k (k + 1) N η^{-(k+2)}` uniform in the label). -/
private theorem StepDecompN_loopFam_hC₂ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n)
    {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n))
    (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hM : M.IsHermitian)
    (hy : y.IsHermitian) :
    ‖fderiv ℝ (fderiv ℝ (loopFamN sz E s t K n j σ a)) M y y‖ ≤
      (((k * (k + 1) : ℕ) : ℝ) * (Sizes.size sz n : ℝ)
        * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ (k + 2)) * ‖y‖ ^ 2 := by
  have hu0 : 0 ≤ gridTime s t K n (j + 1) := StepDecompN_gridTime_nonneg s t K n hs0 hst (j + 1)
  have hu1 : gridTime s t K n (j + 1) < 1 := StepDecompN_gridTime_lt_one s t K n hst hj ht1
  exact (hermTestFunLoopN sz k n (E n) (gridTime s t K n (j + 1)) hE hu0 hu1 σ a).2 M y hM hy

/-- The directional derivative along the real line `y ↦ M + y X` at `0` is `fderiv ℝ Ψ M X`, for
`Ψ` differentiable at `M` (merged `StepDecomp_fderiv_im_eq_zero`, first half). -/
private theorem StepDecompN_hasDerivAt_dir {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ψ : Matrix ι ι ℂ → ℂ} {M : Matrix ι ι ℂ} (X : Matrix ι ι ℂ) (hd : DifferentiableAt ℝ Ψ M) :
    HasDerivAt (fun y : ℝ => Ψ (M + (y : ℂ) • X)) (fderiv ℝ Ψ M X) 0 := by
  have hp0 : HasDerivAt (fun t' : ℝ => Ψ (M + t' • X)) (fderiv ℝ Ψ M X) 0 := by
    have h1 : HasFDerivAt Ψ (fderiv ℝ Ψ (M + (0 : ℝ) • X)) (M + (0 : ℝ) • X) := by
      simpa using hd.hasFDerivAt
    have h2 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) h1 (StepDecompN_hasDerivAt_add_smul M X 0)
    simp only [zero_smul, add_zero, Function.comp_def] at h2
    exact h2
  simpa only [Complex.coe_smul] using hp0

/-- `loopDerivN` is `fderiv ℝ` of the loop family, where the loop family is differentiable. -/
private theorem StepDecompN_loopDerivN_eq_fderiv {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ)
    (n j : ℕ) {k : ℕ} (σ : Fin k → Bool) (b : Fin k → Zd d (sz.L n))
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (X : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hd : DifferentiableAt ℝ (loopFamN sz E s t K n j σ b) M) :
    loopDerivN d (sz.L n) (sz.W n) (E n) (gridTime s t K n (j + 1)) M X σ b
      = fderiv ℝ (loopFamN sz E s t K n j σ b) M X :=
  (StepDecompN_hasDerivAt_dir X hd).deriv

/-- The identity kernel collapses a sum over labels. -/
private theorem StepDecompN_sum_delta {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℂ)
    (a : ι) : ∑ c, (if a = c then (1 : ℂ) else 0) * f c = f a := by
  simp [ite_mul]

/-- **`stepZCN` is linear in the complex kernel `U`**, pointwise in `ω` (RBM1D
`stepZC_eq_sum_gridDeltaC`, `:605`): `Z^U_b = Σ_a U(b,a) Z^δ_a`. -/
private theorem StepDecompN_stepZCN_eq_sum_delta {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ)
    (n j : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (U : ι → ι → ℂ) (b : ι) (ω : PathΩ sz) :
    stepZCN sz s t K n j Φ U b ω
      = ∑ a, U b a * stepZCN sz s t K n j Φ (fun a a' => if a = a' then 1 else 0) a ω := by
  rw [← StepDecompN_sum_fderiv_eq_stepZCN sz s t K n j (Φ := Φ) U b ω, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← StepDecompN_sum_fderiv_eq_stepZCN sz s t K n j (Φ := Φ)
    (fun a a' => if a = a' then 1 else 0) a ω]
  rw [StepDecompN_sum_delta (fun c => fderiv ℝ (Φ c) (pathH sz s t K n j ω)
    (Sizes.seqXmat sz n (ω (j + 1)))) a]
  ring

/-- `stepZCN` for the loop family and a general kernel is `Σ_a U(b,a) ZvecN_a`. -/
private theorem StepDecompN_stepZCN_eq_sum_zvecN {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ)
    (n j : ℕ) (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1)
    (hj : j + 1 ≤ K n) {k : ℕ} (σ : Fin k → Bool)
    (U : (Fin k → Zd d (sz.L n)) → (Fin k → Zd d (sz.L n)) → ℂ) (b : Fin k → Zd d (sz.L n))
    (ω : PathΩ sz) :
    stepZCN sz s t K n j (loopFamN sz E s t K n j σ) U b ω
      = ∑ a, U b a * ZvecN sz E s t K n j σ ω a := by
  rw [← StepDecompN_sum_fderiv_eq_stepZCN sz s t K n j (Φ := loopFamN sz E s t K n j σ) U b ω,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hd : DifferentiableAt ℝ (loopFamN sz E s t K n j σ a) (pathH sz s t K n j ω) :=
    ((StepDecompN_loopFam_hermTestFun sz E s t K n j hE hs0 hst ht1 hj σ a).contDiffAt _
      (pathH_isHermitian sz s t K n j ω)).differentiableAt (by norm_num)
  have h := StepDecompN_loopDerivN_eq_fderiv sz E s t K n j σ a
    (M := pathH sz s t K n j ω) (Sizes.seqXmat sz n (ω (j + 1))) hd
  unfold ZvecN
  rw [h]
  ring

/-- **`ZvecN = stepZCN`** (identity kernel; RBM1D `stepZC_gridDeltaC`, `:591`): the first-chaos
part `√Δ · ∂_{X_{j+1}} 𝓛_{u_{j+1},σ,b}(H_j)` of the merged vocabulary is `stepZCN` of the loop family with the
identity kernel, at every sample point.  The derivative `loopDerivN` is `fderiv ℝ` because the loop
observable is differentiable at the Hermitian `H_j` (`HermTestFun.contDiffAt`), and `fderiv` along a
Hermitian direction is `trace (gradMat · X)` (`fderiv_eq_trace_gradMat`). -/
theorem ZvecN_eq_stepZCN {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n)
    {k : ℕ} (σ : Fin k → Bool) (b : Fin k → Zd d (sz.L n)) (ω : PathΩ sz) :
    ZvecN sz E s t K n j σ ω b =
      stepZCN sz s t K n j (loopFamN sz E s t K n j σ) (fun a a' => if a = a' then 1 else 0) b ω := by
  rw [StepDecompN_stepZCN_eq_sum_zvecN sz E s t K n j hE hs0 hst ht1 hj σ _ b ω,
    StepDecompN_sum_delta]

/-- **`Ugen ∘ ZvecN = stepZCN` with the propagator kernel** (RBM1D `stepZC_ukerMatC_eq_Uker`,
`:619`): `(𝒰_{u_{j+1},u_m,σ} Z)_a = stepZCN` of the loop family with the kernel
`U(a,b) = Π_i ukerMat(m_i m_{i+1}; u_{j+1}, u_m)(a_i, b_i)` of `Ugen`, so that the
sub-Gaussianity of `(𝒰 Z)_a` (`SubGaussStopN` for `ZvecN`) reduces to `stepDecompCN_Z_subG`. -/
theorem Ugen_stepZCN {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n)
    {k : ℕ} (σ : Fin k → Bool) (m : ℕ) (a : Fin k → Zd d (sz.L n)) (ω : PathΩ sz) :
    Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (j + 1)) (gridTime s t K n m)
        (ZvecN sz E s t K n j σ ω) a =
      stepZCN sz s t K n j (loopFamN sz E s t K n j σ)
        (fun a b => ∏ i : Fin k, uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma (E n) (σ i)) i)
          (gridTime s t K n (j + 1)) (gridTime s t K n m) (a i) (b i)) a ω := by
  rw [StepDecompN_stepZCN_eq_sum_zvecN sz E s t K n j hE hs0 hst ht1 hj σ _ a ω]
  rfl

/-- **`stepXiCN` is linear in the complex kernel `U`**, a.e., simultaneously for all labels `b`
(RBM1D `stepXiC_eq_sum_gridDeltaC_ae`, `:628`): `ξ^U_b = Σ_a U(b,a) ξ^δ_a`. -/
private theorem StepDecompN_stepXiCN_eq_sum_delta_ae {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ)
    (n j : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (hΦ : ∀ a, HermTestFun sz n (Φ a)) (U : ι → ι → ℂ) :
    ∀ᵐ ω ∂(pathP sz), ∀ b : ι,
      stepXiCN sz s t K n j Φ U b ω
        = ∑ a, U b a * stepXiCN sz s t K n j Φ (fun a a' => if a = a' then 1 else 0) a ω := by
  have hfun : ∀ a : ι,
      (fun ω' => ∑ c, (if a = c then (1 : ℂ) else 0) * Φ c (pathH sz s t K n (j + 1) ω'))
        = fun ω' => Φ a (pathH sz s t K n (j + 1) ω') := by
    intro a; funext ω'
    exact StepDecompN_sum_delta (fun c => Φ c (pathH sz s t K n (j + 1) ω')) a
  have hδ : ∀ a (ω : PathΩ sz),
      stepXiCN sz s t K n j Φ (fun a a' => if a = a' then 1 else 0) a ω
        = Φ a (pathH sz s t K n (j + 1) ω)
          - (pathP sz)[fun ω' => Φ a (pathH sz s t K n (j + 1) ω') | filt sz j] ω := by
    intro a ω
    have h1 := congrFun (hfun a) ω
    unfold stepXiCN
    rw [h1, hfun a]
  refine ae_all_iff.mpr fun b => ?_
  have hint_a : ∀ a ∈ (Finset.univ : Finset ι),
      Integrable (fun ω => U b a * Φ a (pathH sz s t K n (j + 1) ω)) (pathP sz) :=
    fun a _ => (StepDecompN_integrable_phi sz s t K n (hΦ a) (j + 1)).const_mul (U b a)
  have hcondsum := condExp_finsetSum hint_a (filt sz j)
  have hsmul_ae : ∀ᵐ ω ∂(pathP sz), ∀ a : ι,
      (pathP sz)[fun ω' => U b a * Φ a (pathH sz s t K n (j + 1) ω') | filt sz j] ω
        = U b a * (pathP sz)[fun ω' => Φ a (pathH sz s t K n (j + 1) ω') | filt sz j] ω :=
    ae_all_iff.mpr fun a =>
      condExp_smul (U b a) (fun ω' => Φ a (pathH sz s t K n (j + 1) ω')) (filt sz j)
  have hsum_fn : (∑ a : ι, fun ω' => U b a * Φ a (pathH sz s t K n (j + 1) ω'))
      = (fun ω' => ∑ a : ι, U b a * Φ a (pathH sz s t K n (j + 1) ω')) := by
    funext ω'; simp only [Finset.sum_apply]
  rw [hsum_fn] at hcondsum
  filter_upwards [hcondsum, hsmul_ae] with ω hω1 hω2
  simp_rw [hδ]
  unfold stepXiCN
  rw [hω1]
  simp only [Finset.sum_apply]
  rw [Finset.sum_congr rfl fun a _ => hω2 a]
  simp only [mul_sub, Finset.sum_sub_distrib]

/-- **`stepYCN` is linear in the complex kernel `U`**, a.e., simultaneously for all labels `b`
(RBM1D `stepYC_eq_sum_gridDeltaC_ae`, `:674`). -/
private theorem StepDecompN_stepYCN_eq_sum_delta_ae {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ)
    (n j : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (hΦ : ∀ a, HermTestFun sz n (Φ a)) (U : ι → ι → ℂ) :
    ∀ᵐ ω ∂(pathP sz), ∀ b : ι,
      stepYCN sz s t K n j Φ U b ω
        = ∑ a, U b a * stepYCN sz s t K n j Φ (fun a a' => if a = a' then 1 else 0) a ω := by
  filter_upwards [StepDecompN_stepXiCN_eq_sum_delta_ae sz s t K n j hΦ U] with ω hω b
  unfold stepYCN
  rw [hω b, StepDecompN_stepZCN_eq_sum_delta sz s t K n j (Φ := Φ) U b ω]
  simp only [mul_sub, Finset.sum_sub_distrib]

/-- **`martIncN = stepXiCN`** (identity kernel; RBM1D `KernelC`, `:571-:698`): a.e., simultaneously
for all labels `b`, the martingale increment `ξ_{j+1} = A_{j+1} - E[A_{j+1} | F_j]` of the merged vocabulary is
`stepXiCN` of the loop family with the identity kernel.  The deterministic `𝒦` part of `AvecN`
(`A = 𝓛 - 𝒦`) cancels: `E[𝓛 - 𝒦 | F_j] = E[𝓛 | F_j] - 𝒦`, the loop observable being bounded and
measurable along the Hermitian walk (`HermTestFun`). -/
theorem martIncN_eq_stepXiCN {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n)
    {k : ℕ} (σ : Fin k → Bool) :
    ∀ᵐ ω ∂(pathP sz), ∀ b : Fin k → Zd d (sz.L n),
      martIncN sz E s t K n j σ ω b =
        stepXiCN sz s t K n j (loopFamN sz E s t K n j σ) (fun a a' => if a = a' then 1 else 0)
          b ω := by
  have hΦ := StepDecompN_loopFam_hermTestFun sz E s t K n j hE hs0 hst ht1 hj σ
  refine ae_all_iff.mpr fun b => ?_
  have hint : Integrable (fun ω' : PathΩ sz => loopFamN sz E s t K n j σ b (pathH sz s t K n (j + 1) ω'))
      (pathP sz) := StepDecompN_integrable_phi sz s t K n (hΦ b) (j + 1)
  have hsub := condExp_sub hint
    (integrable_const (sz.STKloop n (E n) (gridTime s t K n (j + 1)) σ b))
    (filt sz j)
  have hconst := condExp_const (μ := pathP sz) ((filt sz).le j)
    (sz.STKloop n (E n) (gridTime s t K n (j + 1)) σ b)
  have hfun : (fun ω' : PathΩ sz => ∑ a, (if b = a then (1 : ℂ) else 0) *
        loopFamN sz E s t K n j σ a (pathH sz s t K n (j + 1) ω'))
      = fun ω' => loopFamN sz E s t K n j σ b (pathH sz s t K n (j + 1) ω') := by
    funext ω'
    exact StepDecompN_sum_delta (fun c => loopFamN sz E s t K n j σ c (pathH sz s t K n (j + 1) ω')) b
  have hAvec : (fun ω' : PathΩ sz => AvecN sz E s t K n (j + 1) σ ω' b)
      = (fun ω' : PathΩ sz => loopFamN sz E s t K n j σ b (pathH sz s t K n (j + 1) ω'))
        - fun _ => sz.STKloop n (E n) (gridTime s t K n (j + 1)) σ b := by
    funext ω'
    simp only [AvecN, Sizes.STLKM, Sizes.STLM, loopFine, Pi.sub_apply, loopFamN]
    rw [loopM_eq_loopL]
  have hA0 : ∀ ω : PathΩ sz, AvecN sz E s t K n (j + 1) σ ω b
      = loopFamN sz E s t K n j σ b (pathH sz s t K n (j + 1) ω)
        - sz.STKloop n (E n) (gridTime s t K n (j + 1)) σ b := fun ω => congrFun hAvec ω
  filter_upwards [hsub] with ω hω
  unfold martIncN stepXiCN
  rw [hA0 ω, hAvec, hω, hfun]
  simp only [Pi.sub_apply, hconst]
  have hb : (∑ a, (if b = a then (1 : ℂ) else 0) *
      loopFamN sz E s t K n j σ a (pathH sz s t K n (j + 1) ω))
      = loopFamN sz E s t K n j σ b (pathH sz s t K n (j + 1) ω) :=
    StepDecompN_sum_delta (fun c => loopFamN sz E s t K n j σ c (pathH sz s t K n (j + 1) ω)) b
  rw [hb]
  change (loopFamN sz E s t K n j σ b (pathH sz s t K n (j + 1) ω) - _) - _ = _
  ring

/-- **`YvecN = stepYCN`** (identity kernel): a.e., simultaneously for all labels `b`, the remainder
`martIncN - ZvecN` of the merged vocabulary is `stepYCN` of the loop family with the identity kernel. -/
theorem YvecN_eq_stepYCN {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n)
    {k : ℕ} (σ : Fin k → Bool) :
    ∀ᵐ ω ∂(pathP sz), ∀ b : Fin k → Zd d (sz.L n),
      YvecN sz E s t K n j σ ω b =
        stepYCN sz s t K n j (loopFamN sz E s t K n j σ) (fun a a' => if a = a' then 1 else 0)
          b ω := by
  filter_upwards [martIncN_eq_stepXiCN sz E s t K n j hE hs0 hst ht1 hj σ] with ω hω b
  unfold YvecN stepYCN
  rw [hω b, ZvecN_eq_stepZCN sz E s t K n j hE hs0 hst ht1 hj σ b ω]

/-- **`Ugen ∘ YvecN = stepYCN` with the propagator kernel** (RBM1D `stepYC_ukerMatC_eq_Uker_ae`,
`:688`): a.e., for every label `a`, `(𝒰_{u_{j+1},u_m,σ} Y)_a` is `stepYCN` of the loop family with
the kernel of `Ugen`. -/
theorem Ugen_stepYCN {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n)
    {k : ℕ} (σ : Fin k → Bool) (m : ℕ) :
    ∀ᵐ ω ∂(pathP sz), ∀ a : Fin k → Zd d (sz.L n),
      Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (j + 1)) (gridTime s t K n m)
          (YvecN sz E s t K n j σ ω) a =
        stepYCN sz s t K n j (loopFamN sz E s t K n j σ)
          (fun a b => ∏ i : Fin k, uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma (E n) (σ i)) i)
          (gridTime s t K n (j + 1)) (gridTime s t K n m) (a i) (b i)) a ω := by
  have hΦ := StepDecompN_loopFam_hermTestFun sz E s t K n j hE hs0 hst ht1 hj σ
  filter_upwards [YvecN_eq_stepYCN sz E s t K n j hE hs0 hst ht1 hj σ,
    StepDecompN_stepYCN_eq_sum_delta_ae sz s t K n j hΦ
      (fun a b => ∏ i : Fin k, uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma (E n) (σ i)) i)
          (gridTime s t K n (j + 1)) (gridTime s t K n m) (a i) (b i))] with ω h1 h2 a
  rw [h2 a]
  unfold Ugen
  exact Finset.sum_congr rfl fun b _ => by rw [h1 b]

/-- **`SubGaussStopN` for `ZvecN` reduces to `stepDecompCN_Z_subG`** (the purpose of
`Ugen_stepZCN`): with the stopping family `{j < τ} ∈ F_j` as the set `E`, the stopped propagated
increment `1_{j<τ} (𝒰_{u_{j+1},u_m,σ} Z_j)_a` is conditionally sub-Gaussian, real and imaginary
part, with the proxy `c` whenever `Δ · linTrVar` of `AbCN` and of `(-I) • AbCN` (the loop family
with the `Ugen` kernel) is at most `c` on `{j < τ}`. -/
theorem StepDecompN_subGaussStopN_zvecN {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n)
    {k : ℕ} (σ : Fin k → Bool) (τ : PathΩ sz → ℕ)
    (hτ : MeasurableSet[filt sz j] {ω | j < τ ω}) (m : ℕ) (a : Fin k → Zd d (sz.L n))
    (c : ℝ) (hc : 0 ≤ c)
    (hboundRe : ∀ ω, j < τ ω → gridStep s t K n * linTrVar n
      (AbCN sz s t K n j (loopFamN sz E s t K n j σ)
        (fun a b => ∏ i : Fin k, uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma (E n) (σ i)) i)
          (gridTime s t K n (j + 1)) (gridTime s t K n m) (a i) (b i)) a ω) ≤ c)
    (hboundIm : ∀ ω, j < τ ω → gridStep s t K n * linTrVar n
      ((-Complex.I) • AbCN sz s t K n j (loopFamN sz E s t K n j σ)
        (fun a b => ∏ i : Fin k, uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma (E n) (σ i)) i)
          (gridTime s t K n (j + 1)) (gridTime s t K n m) (a i) (b i)) a ω) ≤ c) :
    SubGaussStopN sz (E n) σ (gridTime s t K n) τ (fun j ω => ZvecN sz E s t K n j σ ω) m a j
      ⟨c, hc⟩ := by
  have hΦ := StepDecompN_loopFam_hermTestFun sz E s t K n j hE hs0 hst ht1 hj σ
  have hZ := stepDecompCN_Z_subG sz s t K n j hΦ
    (fun a b => ∏ i : Fin k, uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma (E n) (σ i)) i)
          (gridTime s t K n (j + 1)) (gridTime s t K n m) (a i) (b i)) a {ω | j < τ ω} hτ c hc hboundRe hboundIm
  have hU := fun ω' => Ugen_stepZCN sz E s t K n j hE hs0 hst ht1 hj σ m a ω'
  have hre : (fun ω => ({ω' | j < τ ω'}.indicator (fun ω' => Ugen d (sz.L n) (sz.lam n) (E n) σ
        (gridTime s t K n (j + 1)) (gridTime s t K n m) (ZvecN sz E s t K n j σ ω') a) ω).re)
      = fun ω => {ω' | j < τ ω'}.indicator (fun ω' => stepZCN_re sz s t K n j
        (loopFamN sz E s t K n j σ) (fun a b => ∏ i : Fin k, uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma (E n) (σ i)) i)
          (gridTime s t K n (j + 1)) (gridTime s t K n m) (a i) (b i)) a ω') ω := by
    funext ω
    by_cases h : ω ∈ {ω' | j < τ ω'}
    · simp only [Set.indicator_of_mem h, hU]
      simp [stepZCN]
    · simp [Set.indicator_of_notMem h]
  have him : (fun ω => ({ω' | j < τ ω'}.indicator (fun ω' => Ugen d (sz.L n) (sz.lam n) (E n) σ
        (gridTime s t K n (j + 1)) (gridTime s t K n m) (ZvecN sz E s t K n j σ ω') a) ω).im)
      = fun ω => {ω' | j < τ ω'}.indicator (fun ω' => stepZCN_im sz s t K n j
        (loopFamN sz E s t K n j σ) (fun a b => ∏ i : Fin k, uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma (E n) (σ i)) i)
          (gridTime s t K n (j + 1)) (gridTime s t K n m) (a i) (b i)) a ω') ω := by
    funext ω
    by_cases h : ω ∈ {ω' | j < τ ω'}
    · simp only [Set.indicator_of_mem h, hU]
      simp [stepZCN]
    · simp [Set.indicator_of_notMem h]
  unfold SubGaussStopN SubGaussFormN
  exact ⟨by rw [hre]; exact hZ.1, by rw [him]; exact hZ.2⟩

end Identification

/-! ## 8. Compiled nonempty instances

Data: the merged `RBM.Gauss.SizesInst.sz0` (`d = 3`, `L_0 = 4`, `W_0 = 32`, `lam_0 = 1/64`,
`N = 2097152`), energy `E ≡ 0`, `s ≡ 0`, `t ≡ 1/2`, `K ≡ 4` (`Δ = 1/8`, `u_1 = 1/8`, `u_2 = 1/4`),
size index `n = 0`, loop length `k = 3`, `σ = (+,-,+)`, label `b = (0, 0, 0)` (all three insertions in
one block; for three distinct blocks `E_{b_1} E_{b_2} = 0` kills the gradient at `H_0 = 0`).
Step `j = 0`: `H_0 = 0` (`s 0 = 0`) is deterministic, so `AbCN` does not depend on `ω`; step
`j = 1`: `H_1 = √Δ X_1` is random.  The test class and the Hermitian bound
`C₂ = k (k + 1) N η^{-(k+2)}` come from the merged theorem `hermTestFunLoopN`, so every
hypothesis is discharged (no external hypothesis occurs). -/

section Instances

namespace StepDecompNCheck

open RBM.Gauss.SizesInst

private abbrev E0 : ℕ → ℝ := fun _ => 0
private abbrev s0 : ℕ → ℝ := fun _ => 0
private abbrev t0 : ℕ → ℝ := fun _ => 1 / 2
private abbrev K0 : ℕ → ℕ := fun _ => 4

/-- `σ = (+,-,+)`. -/
private abbrev σ3 : Fin 3 → Bool := ![true, false, true]

/-- The label `(0, 0, 0)`: all three insertions in the same block. -/
private abbrev b3 : Fin 3 → Zd 3 (sz0.L 0) := ![0, 0, 0]

/-- The identity kernel `δ`. -/
private abbrev δ3 : (Fin 3 → Zd 3 (sz0.L 0)) → (Fin 3 → Zd 3 (sz0.L 0)) → ℂ :=
  fun a a' => if a = a' then 1 else 0

/-- The propagator kernel of `Ugen` at `σ3` and the times `u_{j+1} → u_m`. -/
private abbrev U3 (j m : ℕ) : (Fin 3 → Zd 3 (sz0.L 0)) → (Fin 3 → Zd 3 (sz0.L 0)) → ℂ :=
  fun a b => ∏ i : Fin 3, uKer 3 (sz0.L 0) (sz0.lam 0)
    (cycProd (fun i => mSigma (E0 0) (σ3 i)) i)
    (gridTime s0 t0 K0 0 (j + 1)) (gridTime s0 t0 K0 0 m) (a i) (b i)

private theorem hE0 : |E0 0| < 2 := by norm_num
private theorem hs00 : 0 ≤ s0 0 := le_rfl
private theorem hst0 : s0 0 ≤ t0 0 := by norm_num
private theorem ht10 : t0 0 < 1 := by norm_num
private theorem hj0 : 0 + 1 ≤ K0 0 := by norm_num
private theorem hj1 : 1 + 1 ≤ K0 0 := by norm_num

private theorem hΔ : 0 ≤ gridStep s0 t0 K0 0 := by norm_num [gridStep]

/-- The grid data are nondegenerate: `Δ = 1/8`, `u_1 = 1/8`, `u_2 = 1/4`. -/
private theorem data : gridStep s0 t0 K0 0 = 1 / 8 ∧ gridTime s0 t0 K0 0 1 = 1 / 8 ∧
    gridTime s0 t0 K0 0 2 = 1 / 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [gridStep, gridTime]

/-- The loop family at the data is in the Hermitian test class (`k = 3`). -/
private theorem hΦ3 (j : ℕ) (hj : j + 1 ≤ K0 0) (a : Fin 3 → Zd 3 (sz0.L 0)) :
    HermTestFun sz0 0 (loopFamN sz0 E0 s0 t0 K0 0 j σ3 a) :=
  StepDecompN_loopFam_hermTestFun sz0 E0 s0 t0 K0 0 j hE0 hs00 hst0 ht10 hj σ3 a

/-- The Hermitian second-derivative constant `C₂ = k (k + 1) N η_{u_{j+1}}^{-(k+2)}` at the data. -/
private def C₂3 (j : ℕ) : ℝ :=
  ((3 * (3 + 1) : ℕ) : ℝ) * (Sizes.size sz0 0 : ℝ)
    * (etaT (E0 0) (gridTime s0 t0 K0 0 (j + 1)))⁻¹ ^ (3 + 2)

private theorem hC₂3 (j : ℕ) (hj : j + 1 ≤ K0 0) (a : Fin 3 → Zd 3 (sz0.L 0))
    (M y : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) :
    M.IsHermitian → y.IsHermitian →
      ‖fderiv ℝ (fderiv ℝ (loopFamN sz0 E0 s0 t0 K0 0 j σ3 a)) M y y‖ ≤ C₂3 j * ‖y‖ ^ 2 :=
  fun hM hy => StepDecompN_loopFam_hC₂ sz0 E0 s0 t0 K0 0 j hE0 hs00 hst0 ht10 hj σ3 a M y hM hy

/-- `C₂ > 0` (the bound is not a vacuous `≤ 0`): `12 · 2097152 · η^{-5} > 0`. -/
private theorem C₂3_pos (j : ℕ) (hj : j + 1 ≤ K0 0) : 0 < C₂3 j := by
  have hη : 0 < etaT (E0 0) (gridTime s0 t0 K0 0 (j + 1)) :=
    etaT_pos hE0 (StepDecompN_gridTime_lt_one s0 t0 K0 0 hst0 hj ht10)
  have hN : 0 < (Sizes.size sz0 0 : ℝ) := by
    rw [sz0_values.2.2.1]; norm_num
  unfold C₂3
  positivity

/-! ### Step `j = 0` (`H_0 = 0`) -/

/-- **Instance of `stepDecompCN`** (identity kernel): the loop family at the data, with the
integrability hypotheses discharged by `integrable_stepZCN_re_of_hermTestFun` and
`integrable_stepZCN_im_of_hermTestFun`. -/
example :=
  stepDecompCN sz0 s0 t0 K0 0 0 (hΦ3 0 hj0) (hC₂3 0 hj0) hΔ δ3 b3
    (integrable_stepZCN_re_of_hermTestFun sz0 s0 t0 K0 0 0 (hΦ3 0 hj0) (hC₂3 0 hj0) hΔ δ3 b3)
    (integrable_stepZCN_im_of_hermTestFun sz0 s0 t0 K0 0 0 (hΦ3 0 hj0) (hC₂3 0 hj0) hΔ δ3 b3)

/-- **Instance of `stepDecompCN`** with the genuinely complex propagator kernel `U3 0 1`. -/
example :=
  stepDecompCN sz0 s0 t0 K0 0 0 (hΦ3 0 hj0) (hC₂3 0 hj0) hΔ (U3 0 1) b3
    (integrable_stepZCN_re_of_hermTestFun sz0 s0 t0 K0 0 0 (hΦ3 0 hj0) (hC₂3 0 hj0) hΔ
      (U3 0 1) b3)
    (integrable_stepZCN_im_of_hermTestFun sz0 s0 t0 K0 0 0 (hΦ3 0 hj0) (hC₂3 0 hj0) hΔ
      (U3 0 1) b3)

/-- **Instances of the integrability theorems** (identity and propagator kernels). -/
example :=
  integrable_stepZCN_re_of_hermTestFun sz0 s0 t0 K0 0 0 (hΦ3 0 hj0) (hC₂3 0 hj0) hΔ δ3 b3

example :=
  integrable_stepZCN_im_of_hermTestFun sz0 s0 t0 K0 0 0 (hΦ3 0 hj0) (hC₂3 0 hj0) hΔ δ3 b3

example :=
  integrable_stepZCN_re_of_hermTestFun sz0 s0 t0 K0 0 0 (hΦ3 0 hj0) (hC₂3 0 hj0) hΔ (U3 0 1) b3

example :=
  integrable_stepZCN_im_of_hermTestFun sz0 s0 t0 K0 0 0 (hΦ3 0 hj0) (hC₂3 0 hj0) hΔ (U3 0 1) b3

/-- **Instances of `stepDecompCN_Y_sq`** (identity and propagator kernels). -/
example := stepDecompCN_Y_sq sz0 s0 t0 K0 0 0 (hΦ3 0 hj0) (hC₂3 0 hj0) hΔ δ3 b3

example := stepDecompCN_Y_sq sz0 s0 t0 K0 0 0 (hΦ3 0 hj0) (hC₂3 0 hj0) hΔ (U3 0 1) b3

/-- `H_0 = 0` at the data (`s 0 = 0`, `j = 0`): the walk is deterministic, so `AbCN` does not
depend on `ω`. -/
private theorem pathH_zero (ω : PathΩ sz0) : pathH sz0 s0 t0 K0 0 0 ω = 0 := by
  simp [pathH, s0]

/-- The (deterministic) direction `AbCN` of the loop family with the kernel `U3 0 1` at `H_0 = 0`. -/
private def A₀3 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ :=
  AbCN sz0 s0 t0 K0 0 0 (loopFamN sz0 E0 s0 t0 K0 0 0 σ3) (U3 0 1) b3 (fun _ => 0)

private theorem AbCN_eq (ω : PathΩ sz0) :
    AbCN sz0 s0 t0 K0 0 0 (loopFamN sz0 E0 s0 t0 K0 0 0 σ3) (U3 0 1) b3 ω = A₀3 := by
  simp only [A₀3, AbCN, pathH_zero]

/-- The sub-Gaussian proxy: the larger of `Δ · linTrVar A₀` and `Δ · linTrVar ((-I) • A₀)`. -/
private def c3 : ℝ :=
  max (gridStep s0 t0 K0 0 * linTrVar 0 A₀3)
    (gridStep s0 t0 K0 0 * linTrVar 0 ((-Complex.I) • A₀3))

private theorem c3_nonneg : 0 ≤ c3 :=
  le_max_of_le_left (mul_nonneg hΔ (linTrVar_nonneg 0 _))

private theorem boundRe3 (ω : PathΩ sz0) :
    gridStep s0 t0 K0 0 * linTrVar 0
      (AbCN sz0 s0 t0 K0 0 0 (loopFamN sz0 E0 s0 t0 K0 0 0 σ3) (U3 0 1) b3 ω) ≤ c3 := by
  rw [AbCN_eq]; exact le_max_left _ _

private theorem boundIm3 (ω : PathΩ sz0) :
    gridStep s0 t0 K0 0 * linTrVar 0 ((-Complex.I) •
      AbCN sz0 s0 t0 K0 0 0 (loopFamN sz0 E0 s0 t0 K0 0 0 σ3) (U3 0 1) b3 ω) ≤ c3 := by
  rw [AbCN_eq]; exact le_max_right _ _

/-- **Instance of `stepDecompCN_Z_subG`** (kernel `U3 0 1`, `E = univ`, `c = c3`). -/
example :=
  stepDecompCN_Z_subG sz0 s0 t0 K0 0 0 (hΦ3 0 hj0) (U3 0 1) b3 Set.univ
    MeasurableSet.univ c3 c3_nonneg (fun ω _ => boundRe3 ω) (fun ω _ => boundIm3 ω)

/-- **Instance of `StepDecompN_subGaussStopN_zvecN`**: the stopping family `τ ≡ K 0` (`{0 < τ}` is
the whole space since `K 0 ≥ 1`), `m = 1`. -/
example : SubGaussStopN sz0 (E0 0) σ3 (gridTime s0 t0 K0 0) (fun _ => K0 0)
    (fun j ω => ZvecN sz0 E0 s0 t0 K0 0 j σ3 ω) 1 b3 0 ⟨c3, c3_nonneg⟩ := by
  have hτ : MeasurableSet[filt sz0 0]
      {ω : PathΩ sz0 | 0 < (fun _ : PathΩ sz0 => K0 0) ω} := by
    have : {ω : PathΩ sz0 | 0 < (fun _ : PathΩ sz0 => K0 0) ω} = Set.univ :=
      Set.eq_univ_of_forall fun _ => by norm_num
    rw [this]; exact MeasurableSet.univ
  exact StepDecompN_subGaussStopN_zvecN sz0 E0 s0 t0 K0 0 0 hE0 hs00 hst0 ht10 hj0 σ3
    (fun _ => K0 0) hτ 1 b3 c3 c3_nonneg (fun ω _ => boundRe3 ω) (fun ω _ => boundIm3 ω)

/-- **Instances of the identification theorems** at the data. -/
example (ω : PathΩ sz0) (b : Fin 3 → Zd 3 (sz0.L 0)) :=
  ZvecN_eq_stepZCN sz0 E0 s0 t0 K0 0 0 hE0 hs00 hst0 ht10 hj0 σ3 b ω

example := martIncN_eq_stepXiCN sz0 E0 s0 t0 K0 0 0 hE0 hs00 hst0 ht10 hj0 σ3

example := YvecN_eq_stepYCN sz0 E0 s0 t0 K0 0 0 hE0 hs00 hst0 ht10 hj0 σ3

/-- **Instances of `Ugen_stepZCN`, `Ugen_stepYCN`** (`u_m = u_1`, `m = 1`). -/
example (a : Fin 3 → Zd 3 (sz0.L 0)) (ω : PathΩ sz0) :=
  Ugen_stepZCN sz0 E0 s0 t0 K0 0 0 hE0 hs00 hst0 ht10 hj0 σ3 1 a ω

example := Ugen_stepYCN sz0 E0 s0 t0 K0 0 0 hE0 hs00 hst0 ht10 hj0 σ3 1

/-! ### Step `j = 1` (`H_1 = √Δ X_1` random; `u_2 = 1/4`, `m = 2`) -/

/-- **Instance of `stepDecompCN`** at `j = 1`, propagator kernel `U3 1 2`: the direction `AbCN`
depends on `ω`. -/
example :=
  stepDecompCN sz0 s0 t0 K0 0 1 (hΦ3 1 hj1) (hC₂3 1 hj1) hΔ (U3 1 2) b3
    (integrable_stepZCN_re_of_hermTestFun sz0 s0 t0 K0 0 1 (hΦ3 1 hj1) (hC₂3 1 hj1) hΔ
      (U3 1 2) b3)
    (integrable_stepZCN_im_of_hermTestFun sz0 s0 t0 K0 0 1 (hΦ3 1 hj1) (hC₂3 1 hj1) hΔ
      (U3 1 2) b3)

example := stepDecompCN_Y_sq sz0 s0 t0 K0 0 1 (hΦ3 1 hj1) (hC₂3 1 hj1) hΔ (U3 1 2) b3

example (ω : PathΩ sz0) (b : Fin 3 → Zd 3 (sz0.L 0)) :=
  ZvecN_eq_stepZCN sz0 E0 s0 t0 K0 0 1 hE0 hs00 hst0 ht10 hj1 σ3 b ω

example := martIncN_eq_stepXiCN sz0 E0 s0 t0 K0 0 1 hE0 hs00 hst0 ht10 hj1 σ3

example := YvecN_eq_stepYCN sz0 E0 s0 t0 K0 0 1 hE0 hs00 hst0 ht10 hj1 σ3

example (a : Fin 3 → Zd 3 (sz0.L 0)) (ω : PathΩ sz0) :=
  Ugen_stepZCN sz0 E0 s0 t0 K0 0 1 hE0 hs00 hst0 ht10 hj1 σ3 2 a ω

example := Ugen_stepYCN sz0 E0 s0 t0 K0 0 1 hE0 hs00 hst0 ht10 hj1 σ3 2

end StepDecompNCheck

end Instances

end RBM.Ind

end

#print axioms RBM.Ind.loopFamN
#print axioms RBM.Ind.dirDerivN
#print axioms RBM.Ind.ZfamN
#print axioms RBM.Ind.ZvecN
#print axioms RBM.Ind.YvecN
#print axioms RBM.Ind.stoppedEdgeN
#print axioms RBM.Ind.SubGaussFormN
#print axioms RBM.Ind.SubGaussStopN
#print axioms RBM.Ind.stepDecompCN
#print axioms RBM.Ind.stepDecompCN_Z_subG
#print axioms RBM.Ind.integrable_stepZCN_re_of_hermTestFun
#print axioms RBM.Ind.integrable_stepZCN_im_of_hermTestFun
#print axioms RBM.Ind.stepDecompCN_Y_sq
#print axioms RBM.Ind.ZvecN_eq_stepZCN
#print axioms RBM.Ind.Ugen_stepZCN
#print axioms RBM.Ind.martIncN_eq_stepXiCN
#print axioms RBM.Ind.YvecN_eq_stepYCN
#print axioms RBM.Ind.Ugen_stepYCN
#print axioms RBM.Ind.StepDecompN_subGaussStopN_zvecN
