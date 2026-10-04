/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.AzumaProxyN
import Mathlib.Probability.ConditionalExpectation

/-!
# The moments of the stopped second-order remainders `Y`: `yMomentsN`, `YMomentsUnifN` (`d ≥ 3`)

Ticket T2160 (ST2-35, stochastic layer ST-2).  Port of RBM2D `Induction/AzumaProxyN.lean` §3-§7,
§10, §11, §8 and §8b at commit `c9a24cf` (cited `AzumaProxyN:<line>`), rewritten for `d ≥ 3`.
Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex`: the martingale term of `int_K-L_ST`
(label at `3_5:136`) and the BDG lemma around `alu9_STime` (`3_5:216-229`); the Lean grid walk
replaces the continuous-time martingale by `ξ = Z + Y` with the first-chaos part `Z`
(Azuma-Hoeffding, T2159) and the quadratic
remainder `Y` of the second-order Taylor expansion, whose moments are bounded here (DECISIONS §10).

## What is here (namespace `RBM.Ind`)

* §1-§2 **`AzumaProxyN_integrable_normPow8_incr`, `AzumaProxyN_integral_normPow8_incr_le`**: the
  eighth moment of one increment, `E ‖X_{j+1}‖⁸ ≤ 6881280 N¹⁶`, `N = (W L)^d` (the analogue of the
  merged `integral_normPow4_incr_le`, `Path/StepDecomp.lean:708`): `‖X‖ ≤ 2 Σ_c |ω_c|`, power mean
  over the `2 N²` coordinates (`#CoordF = 2 N²`), `E ω_c⁸ = 105 v⁴ ≤ 105` (Stein recursion),
  `gvarF ≤ 1`.
* §3 the stopped-`Y` moment lemmas (private): `Y` dominated by `ρ (‖X_{j+1}‖² + E ‖X‖²)` gives
  `E[W² | F_j] ≤ 2ρ² (E ‖X‖⁴ + m²)` and `E W⁴ ≤ 8ρ⁴ (E ‖X‖⁸ + m⁴)` (`condExp_indep_eq`,
  `indep_incr`).
* §4 the row sums of the `Ugen` kernel, `Σ_b ‖Π_i uKer (a_i, b_i)‖ ≤ (1 + (1 - w)⁻¹)^k`.
* §5 the eight moment fields of the merged pin `YMomentBoundsN` for one step and label (private).
* §6 **the pin `YMomentsUnifN`** (`C_P` chosen before the grid `K`, DECISIONS §45),
  **`yMomentsUnifN`** with the explicit witness `C_P = 11 + (4 k + 4) · max 0 (1 - τ')`,
  **`yMomentsN_of_unif`**, and **`yMomentsN : YMomentsN sz κ τ' E s t K`** (the merged pin of
  `GridAssemblyN.lean:173`, unchanged and with no added hypothesis), obtained from the uniform form.
* §7 **`AzumaProxyN_stopW`, `AzumaProxyN_YfieldsW`**: the eight moment fields for the stopped
  weighted increment `1_{j<τ} Σ_c κ_c Y_c` of an arbitrary weight vector, and the public helpers
  `AzumaProxyN_{c0_pos, inv_one_sub_le, etaT_inv_le, P_le, rowsum_Ugen}_pub`.
* §8-§9 compiled nonempty instances at `d = 3` on the merged `sz0`, `E ≡ 1/2`,
  `(s, t, K) = (0, 1/32, 4)` (namespace `AzumaProxyN2Inst`), and `yvecN_not_ae_zero` (`YvecN` is
  not a.e. zero, every `n`).

## Dictionary and `d`-dependent changes (CLAUDE.md §5.2)

`d : Sizes` becomes `sz : Sizes d`; `Z2 (d.L n)` becomes `Zd d (sz.L n)`; `Coord`, `gvar`, `P`,
`Xmat`, `Xentry`, `Ω` become `CoordF d L W`, `gvarF d L W g`, `PF d L W g`, `Xmat d L W`,
`Xentry d L W`, `Ω d L W`; `Sizes.size d n` becomes `sz.size n` (`N = (W L)^d`);
`ukerMat L ξ`, `KLoop.mSig` become `uKer d L g (cycProd (fun i => mSigma E (σ i)) i)`;
`spectralM` becomes `mE`; `[NeZero k]` is dropped (as in the merged pin).
`GoodEvent_gridTime_{nonneg,le}`, `GoodEvent_gridStep_nonneg` do not exist in RBM3D: in-file copies
`azumaProxy2_gridTime_*`.  `stronglyMeasurable_YvecN` is the merged public
`gridAsm_stronglyMeasurable_YvecN`.  The Gaussian-moment, norm and counting helpers are private
copies of the private lemmas of `Path/StepDecomp.lean` §4 (`StepDecomp_norm_Xmat_le`,
`StepDecomp_card_Coord`, `StepDecomp_gvar_le_one`, …) and of `Induction/GridAssemblyN.lean` §4
(`gridAsm_norm_uKer_le`).

* **`gvarF ≤ 1` needs `3 ≤ L`** (`azumaProxy2_gvarF_le_one`): `svarF = W^{-d} S^(B)(g)` and the
  rows of `S^(B)` sum to `1` (`sum_sbKernelR`); RBM2D's five-point profile needs no such
  hypothesis.  Used with `sz.three_le_L n`.
* **`C_P` does not change**: `E ‖X‖² ≤ 16 N⁴`, `E ‖X‖⁴ ≤ 768 N⁸`, `E ‖X‖⁸ ≤ 6881280 N¹⁶` are
  the same polynomials in `N` as for `d = 2` (only `#CoordF = 2 N²` and `gvarF ≤ 1` enter), the
  Hermitian second-derivative bound of the loops is `C₂ = k (k + 1) N η_u^{-(k+2)}` (merged
  `hermTestFunLoopN`), `η_u⁻¹ ≤ N^{1-τ'} / c₀` from `RangeCond`, the row sums of `Ugen` are at
  most `(2 Θ)^k`, `Θ = N^{max 0 (1-τ')}`; so `P = 2000 (S C₂)² N⁸ ≤ N^{11 + (4k+4) max 0 (1-τ')}`
  once `N ≥ max 1 (2000 (2^k k (k + 1) c₀^{-(k+2)})²)`.
* `yMomentsN` is derived from `yMomentsUnifN` by `yMomentsN_of_unif` (RBM2D proves the two
  separately with the same body); the statements are unchanged.

Every helper that the ticket does not pin is `private` or carries the prefix `azumaProxy2_`; the
public names `AzumaProxyN_*` are the RBM2D names (consumed by `AltProxyQ`).
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

/-! ## 1. Gaussian moments up to order 8 -/

section GaussMoments

private theorem azumaProxy2_integrable_pow_gaussianReal (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 v) := by
  have hmem : MemLp (id : ℝ → ℝ) (k : ℝ≥0∞) (gaussianReal 0 v) :=
    memLp_id_gaussianReal' _ (by simp)
  have h := hmem.integrable_norm_pow' (p := k)
  refine h.mono (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  simp

private theorem azumaProxy2_integrable_mul_gaussianPDFReal {v : ℝ≥0} (hv : v ≠ 0) {g : ℝ → ℝ}
    (hg : Integrable g (gaussianReal 0 v)) :
    Integrable fun x : ℝ => g x * gaussianPDFReal 0 v x := by
  rw [gaussianReal_of_var_ne_zero _ hv,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
      (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)] at hg
  simpa [gaussianPDF_def, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 v _),
    mul_comm] using hg

private theorem azumaProxy2_integral_pow_gaussianReal_succ (v : ℝ≥0) (p : ℕ) :
    ∫ x : ℝ, x ^ (2 * p + 2) ∂(gaussianReal 0 v)
      = (2 * p + 1) * (v : ℝ) * ∫ x : ℝ, x ^ (2 * p) ∂(gaussianReal 0 v) := by
  by_cases hv : v = 0
  · subst hv
    rw [gaussianReal_zero_var, integral_dirac, integral_dirac]
    simp
  have hf : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y ^ (2 * p + 1))
      ((2 * p + 1 : ℕ) * x ^ (2 * p)) x := by
    intro x
    simpa using hasDerivAt_pow (2 * p + 1) x
  have h1 : Integrable fun x : ℝ =>
      x ^ (2 * p + 1) * (-(x / (v : ℝ)) * gaussianPDFReal 0 v x) := by
    have := azumaProxy2_integrable_mul_gaussianPDFReal hv
      (g := fun x : ℝ => -((v : ℝ)⁻¹) * x ^ (2 * p + 2))
      (((azumaProxy2_integrable_pow_gaussianReal v (2 * p + 2)).const_mul _))
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    field_simp
    ring
  have h2 : Integrable fun x : ℝ =>
      ((2 * p + 1 : ℕ) : ℝ) * x ^ (2 * p) * gaussianPDFReal 0 v x :=
    azumaProxy2_integrable_mul_gaussianPDFReal hv
      ((azumaProxy2_integrable_pow_gaussianReal v (2 * p)).const_mul _)
  have h3 : Integrable fun x : ℝ => x ^ (2 * p + 1) * gaussianPDFReal 0 v x :=
    azumaProxy2_integrable_mul_gaussianPDFReal hv
      (azumaProxy2_integrable_pow_gaussianReal v (2 * p + 1))
  have h := integral_mul_gaussianReal hv hf h1 h2 h3
  rw [show (fun x : ℝ => x * x ^ (2 * p + 1)) = fun x : ℝ => x ^ (2 * p + 2) from by
    funext x; ring] at h
  rw [h, integral_const_mul]
  push_cast
  ring

/-- `E x⁸ = 105 v⁴` for `x ~ N(0, v)`, kept as the bound `≤ 105` for `v ≤ 1`. -/
private theorem azumaProxy2_integral_pow8_gaussian_le {v : ℝ≥0} (hv1 : (v : ℝ) ≤ 1) :
    ∫ x : ℝ, x ^ 8 ∂(gaussianReal 0 v) ≤ 105 := by
  have h0 : ∫ x : ℝ, x ^ (2 * 0) ∂(gaussianReal 0 v) = 1 := by simp
  have h1 := azumaProxy2_integral_pow_gaussianReal_succ v 0
  have h2 := azumaProxy2_integral_pow_gaussianReal_succ v 1
  have h3 := azumaProxy2_integral_pow_gaussianReal_succ v 2
  have h4 := azumaProxy2_integral_pow_gaussianReal_succ v 3
  norm_num at h1 h2 h3 h4
  rw [h4, h3, h2, h1]
  have hv0 : (0 : ℝ) ≤ v := v.2
  have : (v : ℝ) * (v : ℝ) ≤ 1 := by nlinarith
  nlinarith [mul_nonneg hv0 hv0, pow_nonneg hv0 3, pow_nonneg hv0 4, pow_le_one₀ hv0 hv1 (n := 4)]

end GaussMoments

/-! ## 2. The eighth moment of one increment: `E ‖X‖⁸ ≤ 6881280 N¹⁶`, `N = (W L)^d` -/

section MomentsBound8

private theorem azumaProxy2_norm_single_le {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι)
    (a : ℂ) : ‖(Matrix.single i j a : Matrix ι ι ℂ)‖ ≤ ‖a‖ := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) fun v => ?_
  have h : Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (Matrix.single i j a) v
      = EuclideanSpace.single i (a * v j) := by
    ext k
    simp [Matrix.ofLp_toEuclideanCLM, Matrix.single_mulVec, Function.update_apply]
  rw [h, EuclideanSpace.single, PiLp.norm_single, norm_mul]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le v j) (norm_nonneg _)

/-- The `ℓ²` operator norm is at most the sum of the moduli of the entries. -/
private theorem azumaProxy2_norm_le_sum_entries {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : ‖A‖ ≤ ∑ i, ∑ j, ‖A i j‖ := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => azumaProxy2_norm_single_le i j _))

variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W]

private theorem azumaProxy2_norm_Xentry_le (ω : Ω d L W) (i j : Idx d L W) :
    ‖Xentry d L W ω i j‖ ≤
      (|ω (i, j, true)| + |ω (i, j, false)|) + (|ω (j, i, true)| + |ω (j, i, false)|) := by
  have h1 := abs_nonneg (ω (i, j, true))
  have h2 := abs_nonneg (ω (i, j, false))
  have h3 := abs_nonneg (ω (j, i, true))
  have h4 := abs_nonneg (ω (j, i, false))
  unfold Xentry
  split_ifs
  · refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    linarith
  · refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    linarith
  · rw [Complex.norm_real, Real.norm_eq_abs]
    linarith

private theorem azumaProxy2_sum_coord (f : CoordF d L W → ℝ) :
    ∑ c : CoordF d L W, f c = ∑ i : Idx d L W, ∑ j : Idx d L W, (f (i, j, true) + f (i, j, false)) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]

/-- `‖X‖ ≤ 2 Σ_c |ω_c|` (copy of the private `StepDecomp_norm_Xmat_le`, `Path/StepDecomp.lean:429`). -/
private theorem azumaProxy2_norm_Xmat_le (ω : Ω d L W) :
    ‖Xmat d L W ω‖ ≤ 2 * ∑ c : CoordF d L W, |ω c| := by
  refine (azumaProxy2_norm_le_sum_entries _).trans ?_
  rw [azumaProxy2_sum_coord]
  have hswap : ∑ i : Idx d L W, ∑ j : Idx d L W, (|ω (j, i, true)| + |ω (j, i, false)|)
      = ∑ i : Idx d L W, ∑ j : Idx d L W, (|ω (i, j, true)| + |ω (i, j, false)|) :=
    Finset.sum_comm
  calc ∑ i : Idx d L W, ∑ j : Idx d L W, ‖Xmat d L W ω i j‖
      ≤ ∑ i : Idx d L W, ∑ j : Idx d L W, ((|ω (i, j, true)| + |ω (i, j, false)|)
          + (|ω (j, i, true)| + |ω (j, i, false)|)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => azumaProxy2_norm_Xentry_le ω i j
    _ = 2 * ∑ i : Idx d L W, ∑ j : Idx d L W, (|ω (i, j, true)| + |ω (i, j, false)|) := by
        simp only [Finset.sum_add_distrib] at hswap ⊢
        linarith [hswap]

/-- **`gvarF ≤ 1`** (copy of the private `StepDecomp_gvar_le_one`, `Path/StepDecomp.lean:448`):
`svarF = W^{-d} S^(B)(g)`, and `S^(B)(g)` has non-negative entries with row sum `1`
(`sum_sbKernelR`, which needs `3 ≤ L`). -/
private theorem azumaProxy2_gvarF_le_one (hL : 3 ≤ L) (c : CoordF d L W) :
    (gvarF d L W g c : ℝ) ≤ 1 := by
  have hW : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have h1 : ((W : ℝ) ^ d)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ hW)
  have hk : ∀ i j : Idx d L W, svarF d L W g i j ≤ 1 := by
    intro i j
    have h2 : SBR d L g (split d L W i).1 (split d L W j).1 ≤ 1 := by
      simp only [SBR, Matrix.of_apply]
      calc sbKernelR d L g ((split d L W i).1 - (split d L W j).1)
          ≤ ∑ x, sbKernelR d L g x :=
            Finset.single_le_sum (f := sbKernelR d L g) (fun x _ => sbKernelR_nonneg d L g x)
              (Finset.mem_univ _)
        _ = 1 := sum_sbKernelR d L g hL
    have h3 : 0 ≤ SBR d L g (split d L W i).1 (split d L W j).1 := by
      simpa [SBR] using sbKernelR_nonneg d L g _
    unfold svarF
    calc ((W : ℝ) ^ d)⁻¹ * SBR d L g (split d L W i).1 (split d L W j).1
        ≤ 1 * 1 := mul_le_mul h1 h2 h3 zero_le_one
      _ = 1 := one_mul 1
  have h0 := svarF_nonneg d L W g c.1 c.2.1
  have hs := hk c.1 c.2.1
  change (if c.1 = c.2.1 then svarF d L W g c.1 c.2.1 else svarF d L W g c.1 c.2.1 / 2) ≤ 1
  split_ifs <;> linarith

/-- `#CoordF = 2 N²`, `N = (W L)^d` (copy of the private `StepDecomp_card_Coord`). -/
private theorem azumaProxy2_card_Coord :
    (Fintype.card (CoordF d L W) : ℝ) = 2 * (((W * L) ^ d : ℕ) : ℝ) ^ 2 := by
  have : Fintype.card (CoordF d L W) = 2 * (Fintype.card (Idx d L W)) ^ 2 := by
    simp [CoordF, Fintype.card_prod, Fintype.card_bool]
    ring
  rw [this]
  push_cast
  have h2 : (Fintype.card (Idx d L W) : ℝ) = (((W * L) ^ d : ℕ) : ℝ) := by
    rw [card_Idx]
  rw [h2]
  push_cast
  ring

private theorem azumaProxy2_integrable_pow8_coord (c : CoordF d L W) :
    Integrable (fun ω : Ω d L W => (ω c) ^ 8) (PF d L W g) := by
  have hf : AEMeasurable (fun ω : Ω d L W => ω c) (PF d L W g) := (measurable_pi_apply c).aemeasurable
  have hg : Integrable (fun x : ℝ => x ^ 8) ((PF d L W g).map fun ω => ω c) := by
    rw [P_map_eval]
    exact azumaProxy2_integrable_pow_gaussianReal _ 8
  exact (integrable_map_measure hg.aestronglyMeasurable hf).1 hg

private theorem azumaProxy2_integral_pow8_coord_le (hL : 3 ≤ L) (c : CoordF d L W) :
    ∫ ω : Ω d L W, (ω c) ^ 8 ∂(PF d L W g) ≤ 105 := by
  have hf : AEMeasurable (fun ω : Ω d L W => ω c) (PF d L W g) := (measurable_pi_apply c).aemeasurable
  have hg : AEStronglyMeasurable (fun x : ℝ => x ^ 8) ((PF d L W g).map fun ω => ω c) := by
    fun_prop
  rw [← integral_map hf hg, P_map_eval]
  exact azumaProxy2_integral_pow8_gaussian_le (azumaProxy2_gvarF_le_one hL c)

private theorem azumaProxy2_norm_pow8_le (ω : Ω d L W) :
    ‖Xmat d L W ω‖ ^ 8 ≤ 256 * (Fintype.card (CoordF d L W) : ℝ) ^ 7 * ∑ c : CoordF d L W, (ω c) ^ 8 := by
  have h := azumaProxy2_norm_Xmat_le ω
  have h0 := norm_nonneg (Xmat d L W ω)
  have hS0 : ∀ c ∈ (Finset.univ : Finset (CoordF d L W)), 0 ≤ |ω c| := fun c _ => abs_nonneg _
  have hpm := pow_sum_le_card_mul_sum_pow hS0 7
  simp only [Finset.card_univ] at hpm
  have habs : ∀ c : CoordF d L W, |ω c| ^ (7 + 1) = (ω c) ^ 8 := fun c => Even.pow_abs (by decide) _
  simp only [habs] at hpm
  calc ‖Xmat d L W ω‖ ^ 8 ≤ (2 * ∑ c : CoordF d L W, |ω c|) ^ 8 := pow_le_pow_left₀ h0 h 8
    _ = 256 * (∑ c : CoordF d L W, |ω c|) ^ 8 := by ring
    _ ≤ 256 * ((Fintype.card (CoordF d L W) : ℝ) ^ 7 * ∑ c : CoordF d L W, (ω c) ^ 8) := by
        gcongr
    _ = _ := by ring

private theorem azumaProxy2_integrable_normPow8 :
    Integrable (fun ω : Ω d L W => ‖Xmat d L W ω‖ ^ 8) (PF d L W g) := by
  have hint : Integrable (fun ω : Ω d L W =>
      256 * (Fintype.card (CoordF d L W) : ℝ) ^ 7 * ∑ c : CoordF d L W, (ω c) ^ 8) (PF d L W g) :=
    (integrable_finsetSum _ fun c _ => azumaProxy2_integrable_pow8_coord c).const_mul _
  refine hint.mono' ((continuous_norm.comp (continuous_Xmat d L W)).pow 8).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact azumaProxy2_norm_pow8_le ω

private theorem azumaProxy2_integral_normPow8_le (hL : 3 ≤ L) :
    ∫ ω : Ω d L W, ‖Xmat d L W ω‖ ^ 8 ∂(PF d L W g) ≤ 6881280 * (((W * L) ^ d : ℕ) : ℝ) ^ 16 := by
  have hcard := azumaProxy2_card_Coord (d := d) (L := L) (W := W)
  calc ∫ ω : Ω d L W, ‖Xmat d L W ω‖ ^ 8 ∂(PF d L W g)
      ≤ ∫ ω : Ω d L W, 256 * (Fintype.card (CoordF d L W) : ℝ) ^ 7 * ∑ c : CoordF d L W, (ω c) ^ 8
          ∂(PF d L W g) :=
        integral_mono azumaProxy2_integrable_normPow8
          ((integrable_finsetSum _ fun c _ => azumaProxy2_integrable_pow8_coord c).const_mul _)
          fun ω => azumaProxy2_norm_pow8_le ω
    _ = 256 * (Fintype.card (CoordF d L W) : ℝ) ^ 7
          * ∑ c : CoordF d L W, ∫ ω : Ω d L W, (ω c) ^ 8 ∂(PF d L W g) := by
        rw [integral_const_mul, integral_finsetSum _ fun c _ => azumaProxy2_integrable_pow8_coord c]
    _ ≤ 256 * (Fintype.card (CoordF d L W) : ℝ) ^ 7 * ∑ _c : CoordF d L W, (105 : ℝ) := by
        gcongr with c
        exact azumaProxy2_integral_pow8_coord_le hL c
    _ = 6881280 * (((W * L) ^ d : ℕ) : ℝ) ^ 16 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
        ring

end MomentsBound8

section MomentsPath8

variable {d : ℕ} (sz : Sizes d)

private theorem azumaProxy2_map_incr_slice (n j : ℕ) :
    (pathP sz).map (fun ω : PathΩ sz => Sizes.slice sz n (ω (j + 1)))
      = PF d (sz.L n) (sz.W n) (sz.lam n) := by
  have h := Measure.map_map (μ := pathP sz) (Sizes.measurable_slice sz n)
    (measurable_pi_apply (j + 1) : Measurable fun ω : PathΩ sz => ω (j + 1))
  rw [map_incr, Sizes.seqP_map_slice] at h
  exact h.symm

private theorem azumaProxy2_transfer (n j : ℕ) {f : Ω d (sz.L n) (sz.W n) → ℝ}
    (hf : Integrable f (PF d (sz.L n) (sz.W n) (sz.lam n))) :
    Integrable (fun ω : PathΩ sz => f (Sizes.slice sz n (ω (j + 1)))) (pathP sz) ∧
      ∫ ω : PathΩ sz, f (Sizes.slice sz n (ω (j + 1))) ∂(pathP sz)
        = ∫ x, f x ∂(PF d (sz.L n) (sz.W n) (sz.lam n)) := by
  have hmap := azumaProxy2_map_incr_slice sz n j
  have hgm : AEStronglyMeasurable f
      ((pathP sz).map fun ω : PathΩ sz => Sizes.slice sz n (ω (j + 1))) := by
    rw [hmap]; exact hf.aestronglyMeasurable
  have hm : AEMeasurable (fun ω : PathΩ sz => Sizes.slice sz n (ω (j + 1))) (pathP sz) :=
    ((Sizes.measurable_slice sz n).comp (measurable_pi_apply (j + 1))).aemeasurable
  refine ⟨(integrable_map_measure hgm hm).1 (by rw [hmap]; exact hf), ?_⟩
  have h := integral_map hm hgm
  rw [hmap] at h
  exact h.symm

/-- **The eighth moment of one increment is integrable**: `‖X_{j+1}‖⁸`.  The eighth-moment
analogue of the merged `integrable_normPow4_incr` (`Path/StepDecomp.lean:693`). -/
theorem AzumaProxyN_integrable_normPow8_incr (n j : ℕ) :
    Integrable (fun ω : PathΩ sz => ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 8) (pathP sz) :=
  (azumaProxy2_transfer sz n j
    (f := fun x => ‖Xmat d (sz.L n) (sz.W n) x‖ ^ 8) azumaProxy2_integrable_normPow8).1

/-- **The eighth moment of one increment**: `E ‖X_{j+1}‖⁸ ≤ 6881280 N¹⁶`, `N = (W L)^d`
(`‖X‖ ≤ 2 Σ_c |ω_c|`, power mean over the `2 N²` coordinates, `E ω_c⁸ = 105 v⁴ ≤ 105`, `gvarF ≤ 1`
by `3 ≤ L`); the eighth-moment analogue of the merged `integral_normPow4_incr_le`
(`Path/StepDecomp.lean:708`). -/
theorem AzumaProxyN_integral_normPow8_incr_le (n j : ℕ) :
    ∫ ω : PathΩ sz, ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 8 ∂(pathP sz)
      ≤ 6881280 * (sz.size n : ℝ) ^ 16 :=
  le_of_eq_of_le (azumaProxy2_transfer sz n j
    (f := fun x => ‖Xmat d (sz.L n) (sz.W n) x‖ ^ 8) azumaProxy2_integrable_normPow8).2
    (azumaProxy2_integral_normPow8_le (d := d) (L := sz.L n) (W := sz.W n) (g := sz.lam n)
      (sz.three_le_L n))

end MomentsPath8

/-! ## 3. The stopped `Y` increments: moments from domination by `ρ (‖X_{j+1}‖² + m)`

RBM1D `moments_of_dom_incr`, `condExp_incr_comp`, `condExp_indicator_stepYC_reim`
(`Gauss/Lemma514NonAlt.lean:1554, 1721, 1640`, `c06b103`), adapted as in RBM2D `AzumaProxyN:643-804`:
the conditional expectation of a function of the increment is `condExp_indep_eq` for `indep_incr`,
and the dominating function is squared and raised to the fourth power with the crude
`(x + y)^2 ≤ 2 (x² + y²)`, `(x + y)^4 ≤ 8 (x^4 + y^4)`, so that only `E ‖X‖⁴`, `E ‖X‖⁸` enter. -/

section YMoments

variable {d : ℕ} (sz : Sizes d)

private theorem azumaProxy2_measurable_normX (n : ℕ) :
    Measurable fun x : Sizes.SeqΩ sz => ‖Sizes.seqXmat sz n x‖ :=
  ((continuous_Xmat d (sz.L n) (sz.W n)).measurable.comp (Sizes.measurable_slice sz n)).norm

/-- `E[φ(X_{j+1}) | F_j] = E φ(X_{j+1})` for a measurable `φ` of the increment: the increment
`ω (j + 1)` is independent of `filt sz j` (`indep_incr`). -/
private theorem azumaProxy2_condExp_incr (j : ℕ) {φ : Sizes.SeqΩ sz → ℝ} (hφ : Measurable φ) :
    (pathP sz)[fun ω => φ (ω (j + 1)) | filt sz j] =ᵐ[pathP sz]
      fun _ => ∫ ω, φ (ω (j + 1)) ∂(pathP sz) := by
  have hle₁ : MeasurableSpace.comap (fun ω : PathΩ sz => ω (j + 1)) inferInstance ≤
      (inferInstance : MeasurableSpace (PathΩ sz)) := (measurable_pi_apply (j + 1)).comap_le
  have hf : StronglyMeasurable[MeasurableSpace.comap (fun ω : PathΩ sz => ω (j + 1)) inferInstance]
      (fun ω : PathΩ sz => φ (ω (j + 1))) :=
    (hφ.comp (comap_measurable (fun ω : PathΩ sz => ω (j + 1)))).stronglyMeasurable
  exact condExp_indep_eq hle₁ ((filt sz).le j) hf (indep_incr sz j)

private theorem azumaProxy2_pow4_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by
  have h := mul_nonneg (sq_nonneg (x - y)) (show 0 ≤ 7 * x ^ 2 + 10 * x * y + 7 * y ^ 2 by positivity)
  nlinarith [h]

/-- **Moments of a real process dominated by `c (‖X_{j+1}‖² + m)`** (RBM1D `moments_of_dom_incr`,
`Gauss/Lemma514NonAlt.lean:1721`): the fourth power is integrable, the conditional second moment is
at most `2 c² (B₄ + m²)` and the fourth moment at most `8 c⁴ (B₈ + m⁴)`, where `B₄`, `B₈` bound
`E ‖X‖⁴`, `E ‖X‖⁸`. -/
private theorem azumaProxy2_moments_of_dom (n j : ℕ) {W : PathΩ sz → ℝ} (hWm : Measurable W)
    {c m B4 B8 : ℝ} (hc : 0 ≤ c) (hm : 0 ≤ m)
    (hB4 : ∫ ω, ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 4 ∂(pathP sz) ≤ B4)
    (hB8 : ∫ ω, ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 8 ∂(pathP sz) ≤ B8)
    (hdom : ∀ᵐ ω ∂(pathP sz), |W ω| ≤ c * (‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 + m)) :
    Integrable (fun ω => W ω ^ 4) (pathP sz)
      ∧ (pathP sz)[fun ω => W ω ^ 2 | filt sz j] ≤ᵐ[pathP sz] (fun _ => 2 * c ^ 2 * (B4 + m ^ 2))
      ∧ (∫ ω, W ω ^ 4 ∂(pathP sz)) ≤ 8 * c ^ 4 * (B8 + m ^ 4) := by
  set f2 : Sizes.SeqΩ sz → ℝ := fun x => 2 * c ^ 2 * (‖Sizes.seqXmat sz n x‖ ^ 4 + m ^ 2) with hf2
  set f4 : Sizes.SeqΩ sz → ℝ := fun x => 8 * c ^ 4 * (‖Sizes.seqXmat sz n x‖ ^ 8 + m ^ 4) with hf4
  have hnX := azumaProxy2_measurable_normX sz n
  have hf2m : Measurable f2 := ((hnX.pow_const 4).add_const _).const_mul _
  have hf4m : Measurable f4 := ((hnX.pow_const 8).add_const _).const_mul _
  have hg2i : Integrable (fun ω : PathΩ sz => f2 (ω (j + 1))) (pathP sz) :=
    ((integrable_normPow4_incr sz n j).add (integrable_const (m ^ 2))).const_mul _
  have hg4i : Integrable (fun ω : PathΩ sz => f4 (ω (j + 1))) (pathP sz) :=
    ((AzumaProxyN_integrable_normPow8_incr sz n j).add (integrable_const (m ^ 4))).const_mul _
  have hW2 : ∀ᵐ ω ∂(pathP sz), W ω ^ 2 ≤ f2 (ω (j + 1)) := by
    filter_upwards [hdom] with ω hω
    set a := ‖Sizes.seqXmat sz n (ω (j + 1))‖ with ha
    have ha0 : 0 ≤ a := norm_nonneg _
    have h1 := pow_le_pow_left₀ (abs_nonneg _) hω 2
    rw [sq_abs] at h1
    have h2 := mul_nonneg (sq_nonneg c) (sq_nonneg (a ^ 2 - m))
    simp only [hf2]
    nlinarith [h1, h2]
  have hW4 : ∀ᵐ ω ∂(pathP sz), W ω ^ 4 ≤ f4 (ω (j + 1)) := by
    filter_upwards [hdom] with ω hω
    set a := ‖Sizes.seqXmat sz n (ω (j + 1))‖ with ha
    have ha0 : 0 ≤ a := norm_nonneg _
    have h0 : 0 ≤ c * (a ^ 2 + m) := by positivity
    have h1 := pow_le_pow_left₀ (abs_nonneg _) hω 4
    rw [show |W ω| ^ 4 = W ω ^ 4 by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]] at h1
    have h2 := azumaProxy2_pow4_le (a ^ 2) m (by positivity) hm
    have h3 : (c * (a ^ 2 + m)) ^ 4 = c ^ 4 * (a ^ 2 + m) ^ 4 := by ring
    have h4 : 0 ≤ c ^ 4 := by positivity
    simp only [hf4]
    calc W ω ^ 4 ≤ (c * (a ^ 2 + m)) ^ 4 := h1
      _ = c ^ 4 * (a ^ 2 + m) ^ 4 := h3
      _ ≤ c ^ 4 * (8 * ((a ^ 2) ^ 4 + m ^ 4)) := mul_le_mul_of_nonneg_left h2 h4
      _ = 8 * c ^ 4 * (a ^ 8 + m ^ 4) := by ring
  have hW2i : Integrable (fun ω => W ω ^ 2) (pathP sz) :=
    hg2i.mono' (hWm.pow_const 2).aestronglyMeasurable (by
      filter_upwards [hW2] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hω)
  have hW4i : Integrable (fun ω => W ω ^ 4) (pathP sz) :=
    hg4i.mono' (hWm.pow_const 4).aestronglyMeasurable (by
      filter_upwards [hW4] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hω)
  refine ⟨hW4i, ?_, ?_⟩
  · have hmono := condExp_mono (m := filt sz j) hW2i hg2i hW2
    have hfr := azumaProxy2_condExp_incr sz j hf2m
    filter_upwards [hmono, hfr] with ω h1 h2
    rw [h2] at h1
    refine h1.trans ?_
    have hI : ∫ ω, f2 (ω (j + 1)) ∂(pathP sz)
        = 2 * c ^ 2 * (∫ ω, ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 4 ∂(pathP sz) + m ^ 2) := by
      simp only [hf2]
      rw [integral_const_mul, integral_add (integrable_normPow4_incr sz n j)
        (integrable_const (m ^ 2))]
      simp
    rw [hI]
    have : 0 ≤ 2 * c ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) this
  · have hmono := integral_mono_ae hW4i hg4i hW4
    refine hmono.trans ?_
    have hI : ∫ ω, f4 (ω (j + 1)) ∂(pathP sz)
        = 8 * c ^ 4 * (∫ ω, ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 8 ∂(pathP sz) + m ^ 4) := by
      simp only [hf4]
      rw [integral_const_mul, integral_add (AzumaProxyN_integrable_normPow8_incr sz n j)
        (integrable_const (m ^ 4))]
      simp
    rw [hI]
    have : 0 ≤ 8 * c ^ 4 := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) this

/-- Real and imaginary parts of a stopped process with conditional mean zero have conditional mean
zero (`S ∈ F_j`; RBM1D `condExp_indicator_stepYC_reim`, `Gauss/Lemma514NonAlt.lean:1640`). -/
private theorem azumaProxy2_condExp_stopped_reim (j : ℕ) {S : Set (PathΩ sz)}
    (hS : MeasurableSet[filt sz j] S) {Vf : PathΩ sz → ℂ} (hVint : Integrable Vf (pathP sz))
    (hmean : (pathP sz)[Vf | filt sz j] =ᵐ[pathP sz] fun _ => (0 : ℂ)) :
    (pathP sz)[fun ω => (S.indicator Vf ω).re | filt sz j] =ᵐ[pathP sz] 0 ∧
      (pathP sz)[fun ω => (S.indicator Vf ω).im | filt sz j] =ᵐ[pathP sz] 0 := by
  constructor
  · have hfun : (fun ω => (S.indicator Vf ω).re) = S.indicator (fun ω => (Vf ω).re) := by
      funext ω; by_cases h : ω ∈ S
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h]
    rw [hfun]
    have h1 := condExp_indicator (m := filt sz j) (f := fun ω => (Vf ω).re) hVint.re hS
    have h2 : (pathP sz)[fun ω => (Vf ω).re | filt sz j] =ᵐ[pathP sz] 0 := by
      have hc := (ContinuousLinearMap.comp_condExp_comm (m := filt sz j) hVint
        Complex.reCLM).symm
      have hc' : (pathP sz)[fun ω => (Vf ω).re | filt sz j]
          =ᵐ[pathP sz] fun ω => ((pathP sz)[Vf | filt sz j] ω).re := by
        simpa [Function.comp_def] using hc
      filter_upwards [hc', hmean] with ω h1 h2
      rw [h1, h2]; simp
    filter_upwards [h1, h2] with ω hω1 hω2
    rw [hω1]
    by_cases h : ω ∈ S
    · rw [Set.indicator_of_mem h, hω2]
    · rw [Set.indicator_of_notMem h]; rfl
  · have hfun : (fun ω => (S.indicator Vf ω).im) = S.indicator (fun ω => (Vf ω).im) := by
      funext ω; by_cases h : ω ∈ S
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h]
    rw [hfun]
    have h1 := condExp_indicator (m := filt sz j) (f := fun ω => (Vf ω).im) hVint.im hS
    have h2 : (pathP sz)[fun ω => (Vf ω).im | filt sz j] =ᵐ[pathP sz] 0 := by
      have hc := (ContinuousLinearMap.comp_condExp_comm (m := filt sz j) hVint
        Complex.imCLM).symm
      have hc' : (pathP sz)[fun ω => (Vf ω).im | filt sz j]
          =ᵐ[pathP sz] fun ω => ((pathP sz)[Vf | filt sz j] ω).im := by
        simpa [Function.comp_def] using hc
      filter_upwards [hc', hmean] with ω h1 h2
      rw [h1, h2]; simp
    filter_upwards [h1, h2] with ω hω1 hω2
    rw [hω1]
    by_cases h : ω ∈ S
    · rw [Set.indicator_of_mem h, hω2]
    · rw [Set.indicator_of_notMem h]; rfl

end YMoments

/-! ## 4. The kernel row sums of `Ugen` (copied from the private helper `gridAsm_norm_uKer_le` of
the merged `Induction/GridAssemblyN.lean`, section `UgenBounds`; RBM1D `sum_norm_ukerMatC_le`,
`Gauss/Lemma514NonAlt.lean:1772`) -/

section KernelRows

variable {d L : ℕ} [NeZero L] {g : ℝ}

open scoped Matrix.Norms.Operator in
/-- The `ℓ^∞` operator norm of the one-slot kernel: `‖uKer μ v w‖ ≤ 1 + (1 - w)⁻¹` for
`0 ≤ v, w < 1`, `‖μ‖ = 1` (copy of the private `gridAsm_norm_uKer_le`,
`Induction/GridAssemblyN.lean:586`). -/
private theorem azumaProxy2_norm_uKer_le (hL : 3 ≤ L) {μ : ℂ}
    (hμ : ‖μ‖ = 1) {v w : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (hw0 : 0 ≤ w) (hw1 : w < 1) :
    ‖uKer d L g μ v w‖ ≤ 1 + (1 - w)⁻¹ := by
  have hξ : ‖(w : ℂ) * μ‖ < 1 := norm_t_mul_lt_one hw0 hw1 hμ
  rw [uKer_eq_one_add hL hξ]
  have hc : ‖((w : ℂ) - v) * μ‖ ≤ 1 := by
    rw [norm_mul, hμ, mul_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_le]
    constructor <;> linarith
  have hΘ := norm_Theta_le (d := d) (g := g) hL hw0 hw1 hμ
  calc ‖(1 : Matrix (Zd d L) (Zd d L) ℂ)
        + (((w : ℂ) - v) * μ) • (SB d L g * Theta d L g ((w : ℂ) * μ))‖
      ≤ ‖(1 : Matrix (Zd d L) (Zd d L) ℂ)‖
        + ‖(((w : ℂ) - v) * μ) • (SB d L g * Theta d L g ((w : ℂ) * μ))‖ := norm_add_le _ _
    _ ≤ 1 + 1 * (1 - w)⁻¹ := by
        rw [norm_one]
        refine add_le_add le_rfl ?_
        calc ‖(((w : ℂ) - v) * μ) • (SB d L g * Theta d L g ((w : ℂ) * μ))‖
            ≤ ‖((w : ℂ) - v) * μ‖ * (‖SB d L g‖ * ‖Theta d L g ((w : ℂ) * μ)‖) :=
              (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _)
                (norm_nonneg _))
          _ ≤ 1 * (1 * (1 - w)⁻¹) := by
              rw [norm_SB d L g hL]
              exact mul_le_mul_of_nonneg' hc (by rw [one_mul, one_mul]; exact hΘ) (by positivity) zero_le_one
          _ = 1 * (1 - w)⁻¹ := by ring
    _ = 1 + (1 - w)⁻¹ := by rw [one_mul]

/-- **The row sums of the `Ugen` kernel**: for `|E| ≤ 2`, `3 ≤ L`, `0 ≤ v, w < 1`, the kernel
`(a, b) ↦ Π_i uKer (m_i m_{i+1}) v w (a_i, b_i)` of `Ugen` has row sums
`Σ_b ‖κ(a, b)‖ ≤ (1 + (1 - w)⁻¹)^k` (each of the `k` slots has row sum at most `1 + (1 - w)⁻¹`,
`|m_i m_{i+1}| = 1`).  RBM2D `AzumaProxyN_rowsum_Ugen` (`AzumaProxyN:891`) with `[NeZero k]`
dropped. -/
private theorem azumaProxy2_rowsum_Ugen (hL : 3 ≤ L) {E : ℝ}
    (hE : |E| ≤ 2) {k : ℕ} (σ : Fin k → Bool) {v w : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1)
    (hw0 : 0 ≤ w) (hw1 : w < 1) (a : Fin k → Zd d L) :
    ∑ b : Fin k → Zd d L, ‖∏ i : Fin k,
      uKer d L g (cycProd (fun i => mSigma E (σ i)) i) v w (a i) (b i)‖ ≤
      (1 + (1 - w)⁻¹) ^ k := by
  have hrow : ∀ (i : Fin k),
      ∑ c : Zd d L, ‖uKer d L g (cycProd (fun i => mSigma E (σ i)) i) v w (a i) c‖ ≤
        1 + (1 - w)⁻¹ := fun i =>
    (sum_norm_row_le _ (a i)).trans
      (azumaProxy2_norm_uKer_le hL (norm_cycProd (fun i => norm_mSigma hE (σ i)) i)
        hv0 hv1 hw0 hw1)
  simp_rw [norm_prod]
  rw [← Fintype.prod_sum (fun (i : Fin k) (c : Zd d L) =>
    ‖uKer d L g (cycProd (fun i => mSigma E (σ i)) i) v w (a i) c‖)]
  calc ∏ i : Fin k, ∑ c : Zd d L,
        ‖uKer d L g (cycProd (fun i => mSigma E (σ i)) i) v w (a i) c‖
      ≤ ∏ _i : Fin k, (1 + (1 - w)⁻¹) :=
        Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun c _ => norm_nonneg _)
          (fun i _ => hrow i)
    _ = (1 + (1 - w)⁻¹) ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end KernelRows

/-! ## 5. One step, one label: the eight moment fields of `YMomentBoundsN`

Fix `n`, the step `j < m ≤ K n` and the label `b`.  With the loop family `Φ = loopFamN` and the
kernel `Ukern (a, b') = Π_i uKer (a_i, b'_i)` of `Ugen`, the stopped propagated increment is
a.e. `1_{j<τ} stepYCN Φ Ukern b` (`Ugen_stepYCN`); `stepDecompCN` gives `E[Y | F_j] = 0` and
`‖Y‖ ≤ g + E[g | F_j]`, `g = (Σ_a ‖Ukern b a‖) (C₂/2) Δ ‖X_{j+1}‖²`; the independence of `X_{j+1}`
and `F_j` turns this into `‖Y‖ ≤ ρ (‖X_{j+1}‖² + E ‖X‖²)` a.e. -/

section GridArith

private theorem azumaProxy2_gridStep_nonneg {s t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hst : s n ≤ t n) :
    0 ≤ gridStep s t K n :=
  div_nonneg (sub_nonneg.2 hst) (Nat.cast_nonneg _)

private theorem azumaProxy2_gridTime_nonneg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hs0 : 0 ≤ s n)
    (hst : s n ≤ t n) (j : ℕ) : 0 ≤ gridTime s t K n j := by
  have hΔ : 0 ≤ gridStep s t K n := azumaProxy2_gridStep_nonneg hst
  unfold gridTime
  have : (0 : ℝ) ≤ (j : ℝ) * gridStep s t K n := mul_nonneg (Nat.cast_nonneg _) hΔ
  linarith

/-- `u_j ≤ t n` for `j ≤ K n` (`K n ≠ 0`). -/
private theorem azumaProxy2_gridTime_le (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hst : s n ≤ t n)
    {j : ℕ} (hj : j ≤ K n) (hK : K n ≠ 0) : gridTime s t K n j ≤ t n := by
  have hΔ : 0 ≤ gridStep s t K n := azumaProxy2_gridStep_nonneg hst
  have hlast := gridTime_last s t K n hK
  have hle : gridTime s t K n j ≤ gridTime s t K n (K n) := by
    unfold gridTime
    have : (j : ℝ) ≤ (K n : ℝ) := Nat.cast_le.2 hj
    nlinarith
  linarith

end GridArith

section YFields

variable {d : ℕ} (sz : Sizes d)

/-- **The eight moment fields of `YMomentBoundsN` for one step and one label**, with the loop
family, given the deterministic constants `S` (row sum of the `Ugen` kernel), `C₂` (Hermitian
second-derivative bound of the loops) and `P ≥ 2000 (S C₂)² N⁸`: the real and imaginary parts of the
stopped propagated increment `1_{j<τ} (𝒰_{u_{j+1},u_m} Y_j)_b` have conditional mean zero, integrable
fourth power, conditional second moment `≤ Δ² P` and fourth moment `≤ Δ⁴ P²`. -/
private theorem azumaProxy2_Yfields (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j m : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hjm : j < m)
    (hm : m ≤ K n) {k : ℕ} (σ : Fin k → Bool) (b : Fin k → Zd d (sz.L n))
    {Smax C2 P : ℝ} (hS0 : 0 ≤ Smax) (hC20 : 0 ≤ C2)
    (hrow : ∑ b' : Fin k → Zd d (sz.L n), ‖∏ i : Fin k, uKer d (sz.L n) (sz.lam n)
      (cycProd (fun i => mSigma (E n) (σ i)) i) (gridTime s t K n (j + 1))
      (gridTime s t K n m) (b i) (b' i)‖ ≤ Smax)
    (hC2 : ∀ (a : Fin k → Zd d (sz.L n))
      (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), M.IsHermitian →
      y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (loopFamN sz E s t K n j σ a)) M y y‖ ≤ C2 * ‖y‖ ^ 2)
    (hP : 2000 * (Smax * C2) ^ 2 * (sz.size n : ℝ) ^ 8 ≤ P)
    (τ : PathΩ sz → ℕ) (hτ : ∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) :
    (pathP sz)[fun ω => (stoppedEdgeN sz (E n) σ (gridTime s t K n) (gridTime s t K n m) τ
        (fun j ω => YvecN sz E s t K n j σ ω) b j ω).re | filt sz j] =ᵐ[pathP sz] 0 ∧
    (pathP sz)[fun ω => (stoppedEdgeN sz (E n) σ (gridTime s t K n) (gridTime s t K n m) τ
        (fun j ω => YvecN sz E s t K n j σ ω) b j ω).im | filt sz j] =ᵐ[pathP sz] 0 ∧
    Integrable (fun ω => (stoppedEdgeN sz (E n) σ (gridTime s t K n) (gridTime s t K n m) τ
        (fun j ω => YvecN sz E s t K n j σ ω) b j ω).re ^ 4) (pathP sz) ∧
    Integrable (fun ω => (stoppedEdgeN sz (E n) σ (gridTime s t K n) (gridTime s t K n m) τ
        (fun j ω => YvecN sz E s t K n j σ ω) b j ω).im ^ 4) (pathP sz) ∧
    (pathP sz)[fun ω => (stoppedEdgeN sz (E n) σ (gridTime s t K n) (gridTime s t K n m) τ
        (fun j ω => YvecN sz E s t K n j σ ω) b j ω).re ^ 2 | filt sz j]
      ≤ᵐ[pathP sz] (fun _ => gridStep s t K n ^ 2 * P) ∧
    (pathP sz)[fun ω => (stoppedEdgeN sz (E n) σ (gridTime s t K n) (gridTime s t K n m) τ
        (fun j ω => YvecN sz E s t K n j σ ω) b j ω).im ^ 2 | filt sz j]
      ≤ᵐ[pathP sz] (fun _ => gridStep s t K n ^ 2 * P) ∧
    ∫ ω, (stoppedEdgeN sz (E n) σ (gridTime s t K n) (gridTime s t K n m) τ
        (fun j ω => YvecN sz E s t K n j σ ω) b j ω).re ^ 4 ∂(pathP sz)
      ≤ gridStep s t K n ^ 4 * P ^ 2 ∧
    ∫ ω, (stoppedEdgeN sz (E n) σ (gridTime s t K n) (gridTime s t K n m) τ
        (fun j ω => YvecN sz E s t K n j σ ω) b j ω).im ^ 4 ∂(pathP sz)
      ≤ gridStep s t K n ^ 4 * P ^ 2 := by
  have hj : j + 1 ≤ K n := by omega
  have hK : K n ≠ 0 := by omega
  have hΔ : 0 ≤ gridStep s t K n := azumaProxy2_gridStep_nonneg hst
  have hu0 : 0 ≤ gridTime s t K n (j + 1) := azumaProxy2_gridTime_nonneg s t K n hs0 hst (j + 1)
  have hu1 : gridTime s t K n (j + 1) < 1 :=
    (azumaProxy2_gridTime_le s t K n hst hj hK).trans_lt ht1
  set Δ := gridStep s t K n with hΔdef
  set N : ℝ := (sz.size n : ℝ) with hNdef
  set Ukern : (Fin k → Zd d (sz.L n)) → (Fin k → Zd d (sz.L n)) → ℂ := fun a b' => ∏ i : Fin k,
    uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma (E n) (σ i)) i)
      (gridTime s t K n (j + 1)) (gridTime s t K n m) (a i) (b' i) with hU
  have hΦ : ∀ a, HermTestFun sz n (loopFamN sz E s t K n j σ a) := fun a =>
    (hermTestFunLoopN sz k n (E n) (gridTime s t K n (j + 1)) hE hu0 hu1 σ a).1
  have hIntRe := integrable_stepZCN_re_of_hermTestFun sz s t K n j hΦ hC2 hΔ Ukern b
  have hIntIm := integrable_stepZCN_im_of_hermTestFun sz s t K n j hΦ hC2 hΔ Ukern b
  obtain ⟨-, -, hbound, hmeanY⟩ :=
    stepDecompCN sz s t K n j hΦ hC2 hΔ Ukern b hIntRe hIntIm
  -- the increment moments
  set m2 : ℝ := ∫ ω, ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 ∂(pathP sz) with hm2
  have hm20 : 0 ≤ m2 := integral_nonneg fun _ => by positivity
  have hm2le : m2 ≤ 16 * N ^ 4 := integral_normSq_incr_le sz n j
  set R0 : ℝ := (∑ a, ‖Ukern b a‖) * ((C2 / 2) * Δ) with hR0
  set ρ : ℝ := Smax * ((C2 / 2) * Δ) with hρ
  have hcΔ : 0 ≤ (C2 / 2) * Δ := by positivity
  have hR0ρ : R0 ≤ ρ := mul_le_mul_of_nonneg_right hrow hcΔ
  have hρ0 : 0 ≤ ρ := by positivity
  have hcond : (pathP sz)[fun ω' => (∑ a, ‖Ukern b a‖) * ((C2 / 2) * Δ)
        * ‖Sizes.seqXmat sz n (ω' (j + 1))‖ ^ 2 | filt sz j]
      =ᵐ[pathP sz] fun _ => R0 * m2 := by
    have h := azumaProxy2_condExp_incr sz j (φ := fun x => R0 * ‖Sizes.seqXmat sz n x‖ ^ 2)
      (((azumaProxy2_measurable_normX sz n).pow_const 2).const_mul _)
    have hint : ∫ ω, R0 * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 ∂(pathP sz) = R0 * m2 :=
      integral_const_mul _ _
    rw [hint] at h
    exact h
  -- the loop-side representation of the stopped increment
  set Vfull : PathΩ sz → ℂ := fun ω => Ugen d (sz.L n) (sz.lam n) (E n) σ
    (gridTime s t K n (j + 1)) (gridTime s t K n m) (YvecN sz E s t K n j σ ω) b with hVfull
  have hVae : ∀ᵐ ω ∂(pathP sz),
      Vfull ω = stepYCN sz s t K n j (loopFamN sz E s t K n j σ) Ukern b ω := by
    filter_upwards [Ugen_stepYCN sz E s t K n j hE hs0 hst ht1 hj σ m] with ω hω
    exact hω b
  have hYm : Measurable fun ω : PathΩ sz => YvecN sz E s t K n j σ ω :=
    (gridAsm_stronglyMeasurable_YvecN sz E s t K n j σ).measurable.mono ((filt sz).le (j + 1)) le_rfl
  have hVm : Measurable Vfull := by
    change Measurable fun ω : PathΩ sz => ∑ b' : Fin k → Zd d (sz.L n), (∏ i : Fin k,
      uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma (E n) (σ i)) i)
        (gridTime s t K n (j + 1)) (gridTime s t K n m) (b i) (b' i)) * YvecN sz E s t K n j σ ω b'
    exact Finset.measurable_sum _ fun b' _ => ((measurable_pi_apply b').comp hYm).const_mul _
  have hdom : ∀ᵐ ω ∂(pathP sz), ‖Vfull ω‖ ≤ ρ * (‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 + m2) := by
    filter_upwards [hVae, hbound, hcond] with ω h1 h2 h3
    rw [h1]
    rw [h3] at h2
    have hX0 : 0 ≤ ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 + m2 := by positivity
    calc ‖stepYCN sz s t K n j (loopFamN sz E s t K n j σ) Ukern b ω‖
        ≤ R0 * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 + R0 * m2 := h2
      _ = R0 * (‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 + m2) := by ring
      _ ≤ ρ * (‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 + m2) := mul_le_mul_of_nonneg_right hR0ρ hX0
  have hmean : (pathP sz)[Vfull | filt sz j] =ᵐ[pathP sz] fun _ => (0 : ℂ) :=
    (condExp_congr_ae hVae).trans hmeanY
  have hS : MeasurableSet[filt sz j] {ω | j < τ ω} := hτ j
  have hB4 := integral_normPow4_incr_le sz n j
  have hB8 := AzumaProxyN_integral_normPow8_incr_le sz n j
  -- the stopped moments
  have hVint : Integrable Vfull (pathP sz) :=
    (((integrable_normSq_incr sz n j).add (integrable_const m2)).const_mul ρ).mono'
      hVm.aestronglyMeasurable hdom
  have hSm : MeasurableSet {ω | j < τ ω} := (filt sz).le j _ hS
  have hVind : Measurable ({ω | j < τ ω}.indicator Vfull) := hVm.indicator hSm
  have hdomS : ∀ᵐ ω ∂(pathP sz), ‖{ω | j < τ ω}.indicator Vfull ω‖
      ≤ ρ * (‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 + m2) := by
    filter_upwards [hdom] with ω hω
    exact (norm_indicator_le_norm_self _ _).trans hω
  have hdomRe : ∀ᵐ ω ∂(pathP sz), |({ω | j < τ ω}.indicator Vfull ω).re|
      ≤ ρ * (‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 + m2) := by
    filter_upwards [hdomS] with ω h
    exact (Complex.abs_re_le_norm _).trans h
  have hdomIm : ∀ᵐ ω ∂(pathP sz), |({ω | j < τ ω}.indicator Vfull ω).im|
      ≤ ρ * (‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 + m2) := by
    filter_upwards [hdomS] with ω h
    exact (Complex.abs_im_le_norm _).trans h
  obtain ⟨hRe4, hRe2, hRe4'⟩ := azumaProxy2_moments_of_dom sz n j
    (Complex.measurable_re.comp hVind) hρ0 hm20 hB4 hB8 hdomRe
  obtain ⟨hIm4, hIm2, hIm4'⟩ := azumaProxy2_moments_of_dom sz n j
    (Complex.measurable_im.comp hVind) hρ0 hm20 hB4 hB8 hdomIm
  obtain ⟨hmRe, hmIm⟩ := azumaProxy2_condExp_stopped_reim sz j hS hVint hmean
  -- the numerical bounds
  have hq0 : 0 ≤ Smax * C2 := mul_nonneg hS0 hC20
  have hN0 : 0 ≤ N := by positivity
  have hρq : ρ = (Smax * C2) * Δ / 2 := by simp only [hρ]; ring
  have hv : 2 * ρ ^ 2 * (768 * N ^ 8 + m2 ^ 2) ≤ Δ ^ 2 * P := by
    have hm2sq : m2 ^ 2 ≤ 256 * N ^ 8 := by
      calc m2 ^ 2 ≤ (16 * N ^ 4) ^ 2 := pow_le_pow_left₀ hm20 hm2le 2
        _ = 256 * N ^ 8 := by ring
    have hpos : 0 ≤ (Smax * C2) ^ 2 * Δ ^ 2 * N ^ 8 := by positivity
    calc 2 * ρ ^ 2 * (768 * N ^ 8 + m2 ^ 2)
        ≤ 2 * ρ ^ 2 * (768 * N ^ 8 + 256 * N ^ 8) := by gcongr
      _ = 512 * ((Smax * C2) ^ 2 * Δ ^ 2 * N ^ 8) := by rw [hρq]; ring
      _ ≤ 2000 * ((Smax * C2) ^ 2 * Δ ^ 2 * N ^ 8) := by nlinarith
      _ = Δ ^ 2 * (2000 * (Smax * C2) ^ 2 * N ^ 8) := by ring
      _ ≤ Δ ^ 2 * P := by gcongr
  have hw : 8 * ρ ^ 4 * (6881280 * N ^ 16 + m2 ^ 4) ≤ Δ ^ 4 * P ^ 2 := by
    have hm2q : m2 ^ 4 ≤ 65536 * N ^ 16 := by
      calc m2 ^ 4 ≤ (16 * N ^ 4) ^ 4 := pow_le_pow_left₀ hm20 hm2le 4
        _ = 65536 * N ^ 16 := by ring
    have hpos : 0 ≤ (Smax * C2) ^ 4 * Δ ^ 4 * N ^ 16 := by positivity
    have hP0 : 0 ≤ 2000 * (Smax * C2) ^ 2 * N ^ 8 := by positivity
    calc 8 * ρ ^ 4 * (6881280 * N ^ 16 + m2 ^ 4)
        ≤ 8 * ρ ^ 4 * (6881280 * N ^ 16 + 65536 * N ^ 16) := by gcongr
      _ = 3473408 * ((Smax * C2) ^ 4 * Δ ^ 4 * N ^ 16) := by rw [hρq]; ring
      _ ≤ 4000000 * ((Smax * C2) ^ 4 * Δ ^ 4 * N ^ 16) := by nlinarith
      _ = Δ ^ 4 * (2000 * (Smax * C2) ^ 2 * N ^ 8) ^ 2 := by ring
      _ ≤ Δ ^ 4 * P ^ 2 := by gcongr
  refine ⟨hmRe, hmIm, hRe4, hIm4, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hRe2] with ω h
    exact h.trans hv
  · filter_upwards [hIm2] with ω h
    exact h.trans hv
  · exact hRe4'.trans hw
  · exact hIm4'.trans hw

end YFields

/-! ## 6. Target: `yMomentsN`

The explicit witness: `C_P = 11 + (4 k + 4) · max 0 (1 - τ')`, with, for every `n` with `N = size n`
large and the range condition, `Θ = N^{max 0 (1-τ')}`, `c₀ = √(κ (4 - κ)) / 2`,
`S = (2 Θ)^k` (row sums of `Ugen`), `C₂ = k (k + 1) N (Θ / c₀)^{k+2}` (the second-derivative bound
of the loops) and `P = 2000 (S C₂)² N⁸`.  The exponent count is that of RBM2D (`N` enters only as
a symbol: `#CoordF = 2 N²`, `gvarF ≤ 1`, `C₂ ∝ N`), so `C_P` does not change for `N = (W L)^d`. -/

section YMomentsFinal

variable {d : ℕ} (sz : Sizes d)

/-- `Im m^{(E)} ≥ √(κ (4 - κ)) / 2` in the bulk `|E| ≤ 2 - κ` (copy of the private
`spectralM_im_ge` of `Loop/KBoundInner.lean`, with `mE`). -/
private theorem azumaProxy2_im_ge {κ E : ℝ} (hE : |E| ≤ 2 - κ) :
    Real.sqrt (κ * (4 - κ)) / 2 ≤ (mE E).im := by
  rw [mE_im]
  have hE0 : 0 ≤ |E| := abs_nonneg E
  have hsq : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ hE0 hE 2
  have : κ * (4 - κ) ≤ 4 - E ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt this
  linarith

private theorem azumaProxy2_c0_pos {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) :
    0 < Real.sqrt (κ * (4 - κ)) / 2 := by
  have hκ2 : κ ≤ 2 := by have := abs_nonneg E; linarith
  have : 0 < κ * (4 - κ) := mul_pos hκ (by linarith)
  positivity

/-- `(1 - u)⁻¹ ≤ N^{1-τ'}` for `u ≤ t` and the range condition `N^{-1+τ'} ≤ 1 - t`. -/
private theorem azumaProxy2_inv_one_sub_le {u t τ' N : ℝ} (hut : u ≤ t) (hN0 : 0 < N)
    (hR : N ^ (-1 + τ') ≤ 1 - t) : (1 - u)⁻¹ ≤ N ^ (1 - τ') := by
  have hpos : 0 < N ^ (-1 + τ') := Real.rpow_pos_of_pos hN0 _
  have h1 : N ^ (-1 + τ') ≤ 1 - u := by linarith
  calc (1 - u)⁻¹ ≤ (N ^ (-1 + τ'))⁻¹ := inv_anti₀ hpos h1
    _ = N ^ (1 - τ') := by
        rw [show (-1 + τ') = -(1 - τ') by ring, Real.rpow_neg hN0.le, inv_inv]

/-- `η_u⁻¹ ≤ N^{1-τ'} / c₀` for `u ≤ t`, in the bulk, under the range condition. -/
private theorem azumaProxy2_etaT_inv_le {κ E u t τ' N : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (hut : u ≤ t) (hN0 : 0 < N) (hR : N ^ (-1 + τ') ≤ 1 - t) :
    (etaT E u)⁻¹ ≤ N ^ (1 - τ') / (Real.sqrt (κ * (4 - κ)) / 2) := by
  have hc0 := azumaProxy2_c0_pos hκ hE
  have hm := azumaProxy2_im_ge hE
  have hpos : 0 < N ^ (-1 + τ') := Real.rpow_pos_of_pos hN0 _
  have h1 : N ^ (-1 + τ') ≤ 1 - u := by linarith
  have hη : N ^ (-1 + τ') * (Real.sqrt (κ * (4 - κ)) / 2) ≤ etaT E u := by
    unfold etaT
    exact mul_le_mul h1 hm hc0.le (by linarith)
  calc (etaT E u)⁻¹ ≤ (N ^ (-1 + τ') * (Real.sqrt (κ * (4 - κ)) / 2))⁻¹ :=
        inv_anti₀ (mul_pos hpos hc0) hη
    _ = N ^ (1 - τ') / (Real.sqrt (κ * (4 - κ)) / 2) := by
        rw [mul_inv, show (-1 + τ') = -(1 - τ') by ring, Real.rpow_neg hN0.le, inv_inv]
        exact (div_eq_mul_inv _ _).symm

/-- The final size bound `P ≤ N^{C_P}`. -/
private theorem azumaProxy2_P_le (k : ℕ) {c0 θ N : ℝ} (hc0 : 0 < c0) (hθ : 0 ≤ θ) (hN1 : 1 ≤ N)
    (hbig : 2000 * (2 ^ k * ((k * (k + 1) : ℕ) : ℝ) * (c0⁻¹) ^ (k + 2)) ^ 2 ≤ N) :
    2000 * ((2 * N ^ θ) ^ k * (((k * (k + 1) : ℕ) : ℝ) * N * (N ^ θ / c0) ^ (k + 2))) ^ 2 * N ^ 8
      ≤ N ^ (11 + (4 * k + 4) * θ) := by
  have hN0 : 0 < N := by linarith
  set A : ℝ := 2 ^ k * ((k * (k + 1) : ℕ) : ℝ) * (c0⁻¹) ^ (k + 2) with hA
  set Θ : ℝ := N ^ θ with hΘ
  have hid : 2000 * ((2 * Θ) ^ k * (((k * (k + 1) : ℕ) : ℝ) * N * (Θ / c0) ^ (k + 2))) ^ 2 * N ^ 8
      = (2000 * A ^ 2) * (Θ ^ (4 * k + 4) * N ^ 10) := by
    rw [hA, div_eq_mul_inv]
    ring
  have hΘpow : Θ ^ (4 * k + 4) = N ^ ((4 * k + 4 : ℝ) * θ) := by
    rw [hΘ, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    push_cast
    ring_nf
  have hN10 : N ^ 10 = N ^ (10 : ℝ) := by rw [← Real.rpow_natCast]; norm_num
  have hsplit : N ^ (11 + (4 * k + 4) * θ) = N * (N ^ ((4 * k + 4 : ℝ) * θ) * N ^ (10 : ℝ)) := by
    rw [show (11 + (4 * k + 4) * θ : ℝ) = 1 + (((4 * k + 4 : ℝ) * θ) + 10) by ring,
      Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_one]
  rw [hid, hΘpow, hN10, hsplit]
  have hpos : 0 ≤ N ^ ((4 * k + 4 : ℝ) * θ) * N ^ (10 : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_right hbig hpos

/-- **Pin `YMomentsUnifN`: the primed successor of the merged `YMomentsN`** (RBM2D `YMomentsUnifN`,
`Induction/AzumaProxyN.lean:2042` at `c9a24cf`; DECISIONS §45, supervisor 2026-10-04 19:48 O3 (1)):
the constant `C_P` is taken **before** the grid `K`, so that a consumer can choose
`C_K ≥ D₁ + 4D + k + 2C_P + 8` after `C_P` (`AssembledN`).  In `YMomentsN` the `∃ C_P` sits inside the
`K` binder (`YMomentsConclN`), so `C_P` may depend on `K`, and `K = ⌈N^{C_K}⌉` depends on `C_P`;
`YMomentsUnifN` implies `YMomentsN` (`yMomentsN_of_unif`).  True: `P` is a moment of the Gaussian
increments and of `η_t⁻¹`, independent of `K` (RBM1D `PPP`, `ev_moments`,
`Gauss/PPInduction.lean:2538,2590`).  `[NeZero k]` is dropped, as in the merged `YMomentsN`. -/
def YMomentsUnifN (κ τ' : ℝ) (E s t : ℕ → ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
  sz.SizeTendsto → sz.RangeCond τ' t →
  ∀ (k : ℕ) (σ : Fin k → Bool), ∃ C_P : ℝ, 0 ≤ C_P ∧ ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) →
    ∀ᶠ n : ℕ in atTop, ∃ P : ℝ, 0 ≤ P ∧ P ≤ ((sz.size n : ℕ) : ℝ) ^ C_P ∧
      ∀ τ : PathΩ sz → ℕ, (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
        YMomentBoundsN sz (E n) σ (gridTime s t K n) τ (K n)
          (fun j ω => YvecN sz E s t K n j σ ω)
          (fun _ => gridStep s t K n ^ 2 * P) (fun _ => gridStep s t K n ^ 4 * P ^ 2)

/-- **Target `yMomentsUnifN`**: the uniform `Y` moments.  **Explicit witness**
`C_P = 11 + (4 k + 4) · max 0 (1 - τ')` (the same as RBM2D's: `N = (W L)^d` enters only as the
symbol `N`), chosen before the grid `K`; the eventual threshold
`N ≥ max 1 (2000 (2^k k (k + 1) c₀^{-(k+2)})²)`, `c₀ = √(κ (4 - κ)) / 2`, and
`P = 2000 (S C₂)² N⁸` with `S = (2 Θ)^k`, `C₂ = k (k + 1) N (Θ / c₀)^{k+2}`, `Θ = N^{max 0 (1-τ')}`
depend on `k, κ, τ'` (and `sz, t`) only.  Route (RBM1D `Y_fields514`,
`Gauss/Lemma514NonAlt.lean:1857`): `YvecN = stepYCN` a.e. (`Ugen_stepYCN`), the pathwise bound and the
conditional mean zero of `stepDecompCN`, the constant `C₂` of `hermTestFunLoopN`,
`η^{-1} ≤ N^{1-τ'} / c₀` from `RangeCond` and `|E| ≤ 2 - κ`, the row sums of the `Ugen` kernel, and the
Gaussian moments of `‖X_{j+1}‖` of order 2, 4 and 8.  RBM2D `yMomentsUnifN`
(`AzumaProxyN:2064`, with `yMomentsN` `:1174` proved separately; here `yMomentsN` is derived from this). -/
theorem yMomentsUnifN (κ τ' : ℝ) (E s t : ℕ → ℝ) : YMomentsUnifN sz κ τ' E s t := by
  intro hκ hE hs0 hst ht1 hsize hrange k σ
  have hc0 : 0 < Real.sqrt (κ * (4 - κ)) / 2 := azumaProxy2_c0_pos hκ (hE 0)
  set c0 : ℝ := Real.sqrt (κ * (4 - κ)) / 2 with hc0def
  set θ : ℝ := max 0 (1 - τ') with hθdef
  have hθ0 : 0 ≤ θ := le_max_left _ _
  refine ⟨11 + (4 * k + 4) * θ, by positivity, ?_⟩
  intro K hK
  have hbig := hsize.eventually (eventually_ge_atTop
    (max 1 (2000 * (2 ^ k * ((k * (k + 1) : ℕ) : ℝ) * (c0⁻¹) ^ (k + 2)) ^ 2)))
  filter_upwards [hrange, hbig] with n hR hN
  have hN1 : 1 ≤ ((sz.size n : ℕ) : ℝ) := (le_max_left _ _).trans hN
  have hN0 : 0 < ((sz.size n : ℕ) : ℝ) := by linarith
  have hΘ1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ θ := Real.one_le_rpow hN1 hθ0
  have hΘ0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ θ := by positivity
  set Smax : ℝ := (2 * ((sz.size n : ℕ) : ℝ) ^ θ) ^ k with hSmax
  set C2 : ℝ := ((k * (k + 1) : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ)
    * (((sz.size n : ℕ) : ℝ) ^ θ / c0) ^ (k + 2) with hC2def
  have hS0 : 0 ≤ Smax := by positivity
  have hC20 : 0 ≤ C2 := by positivity
  refine ⟨2000 * (Smax * C2) ^ 2 * ((sz.size n : ℕ) : ℝ) ^ 8, by positivity, ?_, ?_⟩
  · exact azumaProxy2_P_le k hc0 hθ0 hN1 ((le_max_right _ _).trans hN)
  · intro τ hτ
    refine ⟨fun j => gridAsm_stronglyMeasurable_YvecN sz E s t K n j σ, ?_⟩
    intro m hm b j hjm
    have hj : j + 1 ≤ K n := by omega
    have hKn : K n ≠ 0 := hK n
    have hEn : |E n| < 2 := by have := hE n; linarith
    have hv0 : 0 ≤ gridTime s t K n (j + 1) := azumaProxy2_gridTime_nonneg s t K n (hs0 n) (hst n) (j + 1)
    have hvt : gridTime s t K n (j + 1) ≤ t n := azumaProxy2_gridTime_le s t K n (hst n) hj hKn
    have hv1 : gridTime s t K n (j + 1) < 1 := hvt.trans_lt (ht1 n)
    have hw0 : 0 ≤ gridTime s t K n m := azumaProxy2_gridTime_nonneg s t K n (hs0 n) (hst n) m
    have hwt : gridTime s t K n m ≤ t n := azumaProxy2_gridTime_le s t K n (hst n) hm hKn
    have hw1 : gridTime s t K n m < 1 := hwt.trans_lt (ht1 n)
    refine azumaProxy2_Yfields sz E s t K n j m hEn (hs0 n) (hst n) (ht1 n) hjm hm σ b hS0 hC20
      ?_ ?_ le_rfl τ hτ
    · refine (azumaProxy2_rowsum_Ugen (sz.three_le_L n) hEn.le σ hv0 hv1 hw0 hw1 b).trans ?_
      have h1 : (1 - gridTime s t K n m)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (1 - τ') :=
        azumaProxy2_inv_one_sub_le hwt hN0 hR
      have h2 : ((sz.size n : ℕ) : ℝ) ^ (1 - τ') ≤ ((sz.size n : ℕ) : ℝ) ^ θ :=
        Real.rpow_le_rpow_of_exponent_le hN1 (le_max_right _ _)
      exact pow_le_pow_left₀ (by positivity) (by linarith) k
    · intro a M y hM hy
      have hη := azumaProxy2_etaT_inv_le (κ := κ) (E := E n) (u := gridTime s t K n (j + 1))
        (t := t n) (τ' := τ') (N := ((sz.size n : ℕ) : ℝ)) hκ (hE n) hvt hN0 hR
      have hη' : (etaT (E n) (gridTime s t K n (j + 1)))⁻¹
          ≤ ((sz.size n : ℕ) : ℝ) ^ θ / c0 :=
        hη.trans (by
          gcongr
          exact le_max_right _ _)
      have h := (hermTestFunLoopN sz k n (E n) (gridTime s t K n (j + 1)) hEn hv0 hv1 σ a).2 M y hM hy
      refine h.trans ?_
      have hle : ((k * (k + 1) : ℕ) : ℝ) * (Sizes.size sz n : ℝ)
          * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ (k + 2) ≤ C2 := by
        rw [hC2def]
        have hη0 : 0 ≤ (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ := by
          have := etaT_pos hEn hv1
          positivity
        have := pow_le_pow_left₀ hη0 hη' (k + 2)
        have hpos : 0 ≤ ((k * (k + 1) : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left this hpos |>.trans (le_of_eq (by ring))
      exact mul_le_mul_of_nonneg_right hle (by positivity)

/-- `YMomentsUnifN` implies the merged `YMomentsN` (the `C_P` of the uniform statement serves every
`K`).  RBM2D `yMomentsN_of_unif`, `AzumaProxyN:2053`. -/
theorem yMomentsN_of_unif {κ τ' : ℝ} {E s t : ℕ → ℝ} (h : YMomentsUnifN sz κ τ' E s t)
    (K : ℕ → ℕ) : YMomentsN sz κ τ' E s t K := by
  intro hκ hE hs hst ht hK hsize hrange k σ
  obtain ⟨C_P, hC, hev⟩ := h hκ hE hs hst ht hsize hrange k σ
  exact ⟨C_P, hC, hev K hK⟩

/-- **Target `yMomentsN`** (the merged pin `YMomentsN`, `Induction/GridAssemblyN.lean:173`, exactly):
for every loop length `k` and signs `σ`, the moment inputs of the assembled bound hold for the
remainder `YvecN` of the grid step, with the deterministic levels `v_j = Δ² P`, `w_j = Δ⁴ P²`,
`P ≤ N^{C_P}`, for every stopping family `{j < τ} ∈ F_j`; explicit witness
`C_P = 11 + (4 k + 4) · max 0 (1 - τ')`.  Obtained from `yMomentsUnifN` by `yMomentsN_of_unif`
(RBM2D `yMomentsN`, `AzumaProxyN:1174`, has the same proof body). -/
theorem yMomentsN (κ τ' : ℝ) (E s t : ℕ → ℝ) (K : ℕ → ℕ) : YMomentsN sz κ τ' E s t K :=
  yMomentsN_of_unif sz (yMomentsUnifN sz κ τ' E s t) K

end YMomentsFinal

/-! ## 7. The weighted `Y` fields (RBM2D `AzumaProxyN` §11, `:2188-2457`)

The eight moment fields of the private `azumaProxy2_Yfields` for the stopped increment
`1_{j<τ} Σ_c κ_c Y_c` of an arbitrary weight vector `κ` with `Σ_c ‖κ_c‖ ≤ S` in place of the `Ugen`
row: the consumer is RBM2D `Induction/AltProxyQ.lean` (`yMomentsQUnifN`), where
`κ = Σ_b κ^{Ugen}_b Qmat_u(b, ·)` is the transposed `𝒬`-weight vector.  Each `Y_c` has conditional mean
zero and the pathwise domination `‖Y_c‖ ≤ (C₂/2) Δ (‖X_{j+1}‖² + E‖X‖²)` (merged `stepDecompCN` at the
identity kernel and `YvecN_eq_stepYCN`), so the combination is dominated by
`S (C₂/2) Δ (‖X_{j+1}‖² + E‖X‖²)`, and the moment bounds of `azumaProxy2_moments_of_dom` apply as in
`azumaProxy2_Yfields`.  The five numerical helpers of sections 4 and 6 are re-exported as the public
theorems `AzumaProxyN_c0_pos_pub`, `AzumaProxyN_inv_one_sub_le_pub`, `AzumaProxyN_etaT_inv_le_pub`,
`AzumaProxyN_P_le_pub`, `AzumaProxyN_rowsum_Ugen_pub`. -/

section YFieldsW

variable {d : ℕ} (sz : Sizes d)

/-- The stopped weighted increment `1_{j<τ} Σ_c κ_c Y_c` of the step `j → j+1` (RBM2D
`AzumaProxyN_stopW`, `AzumaProxyN:2214`). -/
def AzumaProxyN_stopW (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool)
    (κ : (Fin k → Zd d (sz.L n)) → ℂ) (τ : PathΩ sz → ℕ) (ω : PathΩ sz) : ℂ :=
  {ω' | j < τ ω'}.indicator (fun ω' => ∑ c, κ c * YvecN sz E s t K n j σ ω' c) ω

/-- **The eight moment fields for an arbitrary weight vector** (the weighted analogue of the private
`azumaProxy2_Yfields`; RBM2D `AzumaProxyN_YfieldsW`, `AzumaProxyN:2223`): for `Σ_c ‖κ_c‖ ≤ S`, the
Hermitian second-derivative bound `C₂` of the loop family and `P ≥ 2000 (S C₂)² N⁸`, the real and
imaginary parts of `1_{j<τ} Σ_c κ_c (Y_j)_c` have conditional mean zero, integrable fourth power,
conditional second moment `≤ Δ² P` and fourth moment `≤ Δ⁴ P²`.  `[NeZero k]` is dropped. -/
theorem AzumaProxyN_YfieldsW (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n)
    {k : ℕ} (σ : Fin k → Bool) (κ : (Fin k → Zd d (sz.L n)) → ℂ)
    {Smax C2 P : ℝ} (hS0 : 0 ≤ Smax) (hC20 : 0 ≤ C2) (hrow : ∑ c, ‖κ c‖ ≤ Smax)
    (hC2 : ∀ (a : Fin k → Zd d (sz.L n))
      (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), M.IsHermitian →
      y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (loopFamN sz E s t K n j σ a)) M y y‖ ≤ C2 * ‖y‖ ^ 2)
    (hP : 2000 * (Smax * C2) ^ 2 * (sz.size n : ℝ) ^ 8 ≤ P)
    (τ : PathΩ sz → ℕ) (hτ : ∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) :
    (pathP sz)[fun ω => (AzumaProxyN_stopW sz E s t K n j σ κ τ ω).re | filt sz j] =ᵐ[pathP sz] 0 ∧
    (pathP sz)[fun ω => (AzumaProxyN_stopW sz E s t K n j σ κ τ ω).im | filt sz j] =ᵐ[pathP sz] 0 ∧
    Integrable (fun ω => (AzumaProxyN_stopW sz E s t K n j σ κ τ ω).re ^ 4) (pathP sz) ∧
    Integrable (fun ω => (AzumaProxyN_stopW sz E s t K n j σ κ τ ω).im ^ 4) (pathP sz) ∧
    (pathP sz)[fun ω => (AzumaProxyN_stopW sz E s t K n j σ κ τ ω).re ^ 2 | filt sz j]
      ≤ᵐ[pathP sz] (fun _ => gridStep s t K n ^ 2 * P) ∧
    (pathP sz)[fun ω => (AzumaProxyN_stopW sz E s t K n j σ κ τ ω).im ^ 2 | filt sz j]
      ≤ᵐ[pathP sz] (fun _ => gridStep s t K n ^ 2 * P) ∧
    ∫ ω, (AzumaProxyN_stopW sz E s t K n j σ κ τ ω).re ^ 4 ∂(pathP sz)
      ≤ gridStep s t K n ^ 4 * P ^ 2 ∧
    ∫ ω, (AzumaProxyN_stopW sz E s t K n j σ κ τ ω).im ^ 4 ∂(pathP sz)
      ≤ gridStep s t K n ^ 4 * P ^ 2 := by
  have hK : K n ≠ 0 := by omega
  have hΔ : 0 ≤ gridStep s t K n := azumaProxy2_gridStep_nonneg hst
  have hu0 : 0 ≤ gridTime s t K n (j + 1) := azumaProxy2_gridTime_nonneg s t K n hs0 hst (j + 1)
  have hu1 : gridTime s t K n (j + 1) < 1 :=
    (azumaProxy2_gridTime_le s t K n hst hj hK).trans_lt ht1
  set Δ := gridStep s t K n with hΔdef
  set N : ℝ := (sz.size n : ℝ) with hNdef
  set δ : (Fin k → Zd d (sz.L n)) → (Fin k → Zd d (sz.L n)) → ℂ := fun a a' => if a = a' then 1 else 0
    with hδ
  have hΦ : ∀ a, HermTestFun sz n (loopFamN sz E s t K n j σ a) := fun a =>
    (hermTestFunLoopN sz k n (E n) (gridTime s t K n (j + 1)) hE hu0 hu1 σ a).1
  have hδrow : ∀ c : Fin k → Zd d (sz.L n), ∑ a, ‖δ c a‖ = 1 := by
    intro c
    have h1 : ∀ x, ‖δ c x‖ = if c = x then (1 : ℝ) else 0 := by
      intro x
      by_cases h : c = x <;> simp [hδ, h]
    simp only [h1, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- the identity kernel, label by label
  have hDec : ∀ c : Fin k → Zd d (sz.L n),
      (∀ᵐ ω ∂(pathP sz), ‖stepYCN sz s t K n j (loopFamN sz E s t K n j σ) δ c ω‖ ≤
          (∑ a, ‖δ c a‖) * ((C2 / 2) * Δ) * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 +
            (pathP sz)[fun ω' => (∑ a, ‖δ c a‖) * ((C2 / 2) * Δ) *
              ‖Sizes.seqXmat sz n (ω' (j + 1))‖ ^ 2 | filt sz j] ω) ∧
      (pathP sz)[stepYCN sz s t K n j (loopFamN sz E s t K n j σ) δ c | filt sz j] =ᵐ[pathP sz]
        fun _ => (0 : ℂ) := by
    intro c
    have hIntRe := integrable_stepZCN_re_of_hermTestFun sz s t K n j hΦ hC2 hΔ δ c
    have hIntIm := integrable_stepZCN_im_of_hermTestFun sz s t K n j hΦ hC2 hΔ δ c
    obtain ⟨-, -, hbound, hmeanY⟩ := stepDecompCN sz s t K n j hΦ hC2 hΔ δ c hIntRe hIntIm
    exact ⟨hbound, hmeanY⟩
  -- the increment moments
  set m2 : ℝ := ∫ ω, ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 ∂(pathP sz) with hm2
  have hm20 : 0 ≤ m2 := integral_nonneg fun _ => by positivity
  have hm2le : m2 ≤ 16 * N ^ 4 := integral_normSq_incr_le sz n j
  set R1 : ℝ := (C2 / 2) * Δ with hR1
  set ρ : ℝ := Smax * R1 with hρ
  have hR10 : 0 ≤ R1 := by positivity
  have hρ0 : 0 ≤ ρ := by positivity
  have hcond : (pathP sz)[fun ω' => R1 * ‖Sizes.seqXmat sz n (ω' (j + 1))‖ ^ 2 | filt sz j]
      =ᵐ[pathP sz] fun _ => R1 * m2 := by
    have h := azumaProxy2_condExp_incr sz j (φ := fun x => R1 * ‖Sizes.seqXmat sz n x‖ ^ 2)
      (((azumaProxy2_measurable_normX sz n).pow_const 2).const_mul _)
    have hint : ∫ ω, R1 * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 ∂(pathP sz) = R1 * m2 :=
      integral_const_mul _ _
    rw [hint] at h
    exact h
  -- `Y_c` a.e. equals `stepYCN` of the identity kernel
  have hYall := YvecN_eq_stepYCN sz E s t K n j hE hs0 hst ht1 hj σ
  have hdomc : ∀ᵐ ω ∂(pathP sz), ∀ c : Fin k → Zd d (sz.L n),
      ‖YvecN sz E s t K n j σ ω c‖ ≤ R1 * (‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 + m2) := by
    have h1 : ∀ᵐ ω ∂(pathP sz), ∀ c : Fin k → Zd d (sz.L n),
        ‖stepYCN sz s t K n j (loopFamN sz E s t K n j σ) δ c ω‖ ≤
          (∑ a, ‖δ c a‖) * ((C2 / 2) * Δ) * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 +
            (pathP sz)[fun ω' => (∑ a, ‖δ c a‖) * ((C2 / 2) * Δ) *
              ‖Sizes.seqXmat sz n (ω' (j + 1))‖ ^ 2 | filt sz j] ω :=
      ae_all_iff.mpr fun c => (hDec c).1
    simp only [hδrow, one_mul] at h1
    filter_upwards [hYall, h1, hcond] with ω hY hb hcd c
    rw [hY c]
    refine (hb c).trans ?_
    rw [hcd]
    nlinarith
  have hYm : Measurable fun ω : PathΩ sz => YvecN sz E s t K n j σ ω :=
    (gridAsm_stronglyMeasurable_YvecN sz E s t K n j σ).measurable.mono ((filt sz).le (j + 1)) le_rfl
  have hYcm : ∀ c : Fin k → Zd d (sz.L n), Measurable fun ω : PathΩ sz => YvecN sz E s t K n j σ ω c :=
    fun c => (measurable_pi_apply c).comp hYm
  have hYcint : ∀ c : Fin k → Zd d (sz.L n),
      Integrable (fun ω : PathΩ sz => YvecN sz E s t K n j σ ω c) (pathP sz) := fun c =>
    (((integrable_normSq_incr sz n j).add (integrable_const m2)).const_mul R1).mono'
      (hYcm c).aestronglyMeasurable (by filter_upwards [hdomc] with ω h using h c)
  have hYcmean : ∀ c : Fin k → Zd d (sz.L n),
      (pathP sz)[fun ω => YvecN sz E s t K n j σ ω c | filt sz j] =ᵐ[pathP sz] fun _ => (0 : ℂ) :=
    fun c => by
      have hae : (fun ω => YvecN sz E s t K n j σ ω c) =ᵐ[pathP sz]
          stepYCN sz s t K n j (loopFamN sz E s t K n j σ) δ c := by
        filter_upwards [hYall] with ω h using h c
      exact (condExp_congr_ae hae).trans (hDec c).2
  -- the weighted combination
  set Vfull : PathΩ sz → ℂ := fun ω => ∑ c, κ c * YvecN sz E s t K n j σ ω c with hVfull
  have hVm : Measurable Vfull :=
    Finset.measurable_sum _ fun c _ => (hYcm c).const_mul _
  have hdom : ∀ᵐ ω ∂(pathP sz), ‖Vfull ω‖ ≤
      ρ * (‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 + m2) := by
    filter_upwards [hdomc] with ω h
    have hX0 : 0 ≤ ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 + m2 := by positivity
    calc ‖Vfull ω‖ ≤ ∑ c, ‖κ c * YvecN sz E s t K n j σ ω c‖ := norm_sum_le _ _
      _ = ∑ c, ‖κ c‖ * ‖YvecN sz E s t K n j σ ω c‖ := by simp only [norm_mul]
      _ ≤ ∑ c, ‖κ c‖ * (R1 * (‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 + m2)) :=
          Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (h c) (norm_nonneg _)
      _ = (∑ c, ‖κ c‖) * (R1 * (‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 + m2)) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ Smax * (R1 * (‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 + m2)) :=
          mul_le_mul_of_nonneg_right hrow (by positivity)
      _ = ρ * (‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 + m2) := by rw [hρ]; ring
  have hmean : (pathP sz)[Vfull | filt sz j] =ᵐ[pathP sz] fun _ => (0 : ℂ) := by
    have hint : ∀ c ∈ (Finset.univ : Finset (Fin k → Zd d (sz.L n))),
        Integrable (fun ω => κ c * YvecN sz E s t K n j σ ω c) (pathP sz) :=
      fun c _ => (hYcint c).const_mul (κ c)
    have hcs := condExp_finsetSum hint (filt sz j)
    have hsm : ∀ᵐ ω ∂(pathP sz), ∀ c : Fin k → Zd d (sz.L n),
        (pathP sz)[fun ω' => κ c * YvecN sz E s t K n j σ ω' c | filt sz j] ω =
          κ c * (pathP sz)[fun ω' => YvecN sz E s t K n j σ ω' c | filt sz j] ω :=
      ae_all_iff.mpr fun c =>
        condExp_smul (κ c) (fun ω' => YvecN sz E s t K n j σ ω' c) (filt sz j)
    have hz : ∀ᵐ ω ∂(pathP sz), ∀ c : Fin k → Zd d (sz.L n),
        (pathP sz)[fun ω' => YvecN sz E s t K n j σ ω' c | filt sz j] ω = 0 :=
      ae_all_iff.mpr fun c => hYcmean c
    have hsumfn : (∑ c : Fin k → Zd d (sz.L n), fun ω' => κ c * YvecN sz E s t K n j σ ω' c) =
        Vfull := by
      funext ω'
      simp only [hVfull, Finset.sum_apply]
    rw [hsumfn] at hcs
    filter_upwards [hcs, hsm, hz] with ω h1 h2 h3
    rw [h1]
    simp only [Finset.sum_apply, h2, h3, mul_zero, Finset.sum_const_zero]
  have hS : MeasurableSet[filt sz j] {ω | j < τ ω} := hτ j
  have hB4 := integral_normPow4_incr_le sz n j
  have hB8 := AzumaProxyN_integral_normPow8_incr_le sz n j
  -- the stopped moments
  have hVint : Integrable Vfull (pathP sz) :=
    (((integrable_normSq_incr sz n j).add (integrable_const m2)).const_mul ρ).mono'
      hVm.aestronglyMeasurable hdom
  have hSm : MeasurableSet {ω | j < τ ω} := (filt sz).le j _ hS
  have hVind : Measurable ({ω | j < τ ω}.indicator Vfull) := hVm.indicator hSm
  have hdomS : ∀ᵐ ω ∂(pathP sz), ‖{ω | j < τ ω}.indicator Vfull ω‖
      ≤ ρ * (‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 + m2) := by
    filter_upwards [hdom] with ω hω
    exact (norm_indicator_le_norm_self _ _).trans hω
  have hdomRe : ∀ᵐ ω ∂(pathP sz), |({ω | j < τ ω}.indicator Vfull ω).re|
      ≤ ρ * (‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 + m2) := by
    filter_upwards [hdomS] with ω h
    exact (Complex.abs_re_le_norm _).trans h
  have hdomIm : ∀ᵐ ω ∂(pathP sz), |({ω | j < τ ω}.indicator Vfull ω).im|
      ≤ ρ * (‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 + m2) := by
    filter_upwards [hdomS] with ω h
    exact (Complex.abs_im_le_norm _).trans h
  obtain ⟨hRe4, hRe2, hRe4'⟩ := azumaProxy2_moments_of_dom sz n j
    (Complex.measurable_re.comp hVind) hρ0 hm20 hB4 hB8 hdomRe
  obtain ⟨hIm4, hIm2, hIm4'⟩ := azumaProxy2_moments_of_dom sz n j
    (Complex.measurable_im.comp hVind) hρ0 hm20 hB4 hB8 hdomIm
  obtain ⟨hmRe, hmIm⟩ := azumaProxy2_condExp_stopped_reim sz j hS hVint hmean
  -- the numerical bounds
  have hq0 : 0 ≤ Smax * C2 := mul_nonneg hS0 hC20
  have hN0 : 0 ≤ N := by positivity
  have hρq : ρ = (Smax * C2) * Δ / 2 := by simp only [hρ, hR1]; ring
  have hv : 2 * ρ ^ 2 * (768 * N ^ 8 + m2 ^ 2) ≤ Δ ^ 2 * P := by
    have hm2sq : m2 ^ 2 ≤ 256 * N ^ 8 := by
      calc m2 ^ 2 ≤ (16 * N ^ 4) ^ 2 := pow_le_pow_left₀ hm20 hm2le 2
        _ = 256 * N ^ 8 := by ring
    have hpos : 0 ≤ (Smax * C2) ^ 2 * Δ ^ 2 * N ^ 8 := by positivity
    calc 2 * ρ ^ 2 * (768 * N ^ 8 + m2 ^ 2)
        ≤ 2 * ρ ^ 2 * (768 * N ^ 8 + 256 * N ^ 8) := by gcongr
      _ = 512 * ((Smax * C2) ^ 2 * Δ ^ 2 * N ^ 8) := by rw [hρq]; ring
      _ ≤ 2000 * ((Smax * C2) ^ 2 * Δ ^ 2 * N ^ 8) := by nlinarith
      _ = Δ ^ 2 * (2000 * (Smax * C2) ^ 2 * N ^ 8) := by ring
      _ ≤ Δ ^ 2 * P := by gcongr
  have hw : 8 * ρ ^ 4 * (6881280 * N ^ 16 + m2 ^ 4) ≤ Δ ^ 4 * P ^ 2 := by
    have hm2q : m2 ^ 4 ≤ 65536 * N ^ 16 := by
      calc m2 ^ 4 ≤ (16 * N ^ 4) ^ 4 := pow_le_pow_left₀ hm20 hm2le 4
        _ = 65536 * N ^ 16 := by ring
    have hpos : 0 ≤ (Smax * C2) ^ 4 * Δ ^ 4 * N ^ 16 := by positivity
    have hP0 : 0 ≤ 2000 * (Smax * C2) ^ 2 * N ^ 8 := by positivity
    calc 8 * ρ ^ 4 * (6881280 * N ^ 16 + m2 ^ 4)
        ≤ 8 * ρ ^ 4 * (6881280 * N ^ 16 + 65536 * N ^ 16) := by gcongr
      _ = 3473408 * ((Smax * C2) ^ 4 * Δ ^ 4 * N ^ 16) := by rw [hρq]; ring
      _ ≤ 4000000 * ((Smax * C2) ^ 4 * Δ ^ 4 * N ^ 16) := by nlinarith
      _ = Δ ^ 4 * (2000 * (Smax * C2) ^ 2 * N ^ 8) ^ 2 := by ring
      _ ≤ Δ ^ 4 * P ^ 2 := by gcongr
  have hEq : ∀ ω, AzumaProxyN_stopW sz E s t K n j σ κ τ ω = {ω | j < τ ω}.indicator Vfull ω :=
    fun ω => rfl
  simp only [hEq]
  refine ⟨hmRe, hmIm, hRe4, hIm4, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hRe2] with ω h
    exact h.trans hv
  · filter_upwards [hIm2] with ω h
    exact h.trans hv
  · exact hRe4'.trans hw
  · exact hIm4'.trans hw

end YFieldsW

section PublicAliases

/-- Public re-export of the private `azumaProxy2_c0_pos` (`c₀ = √(κ (4 - κ)) / 2 > 0`; RBM2D
`AzumaProxyN_c0_pos_pub`, `AzumaProxyN:2426`). -/
theorem AzumaProxyN_c0_pos_pub {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) :
    0 < Real.sqrt (κ * (4 - κ)) / 2 :=
  azumaProxy2_c0_pos hκ hE

/-- Public re-export of the private `azumaProxy2_inv_one_sub_le` (RBM2D
`AzumaProxyN_inv_one_sub_le_pub`, `AzumaProxyN:2431`). -/
theorem AzumaProxyN_inv_one_sub_le_pub {u t τ' N : ℝ} (hut : u ≤ t) (hN0 : 0 < N)
    (hR : N ^ (-1 + τ') ≤ 1 - t) : (1 - u)⁻¹ ≤ N ^ (1 - τ') :=
  azumaProxy2_inv_one_sub_le hut hN0 hR

/-- Public re-export of the private `azumaProxy2_etaT_inv_le` (RBM2D
`AzumaProxyN_etaT_inv_le_pub`, `AzumaProxyN:2436`). -/
theorem AzumaProxyN_etaT_inv_le_pub {κ E u t τ' N : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (hut : u ≤ t) (hN0 : 0 < N) (hR : N ^ (-1 + τ') ≤ 1 - t) :
    (etaT E u)⁻¹ ≤ N ^ (1 - τ') / (Real.sqrt (κ * (4 - κ)) / 2) :=
  azumaProxy2_etaT_inv_le hκ hE hut hN0 hR

/-- Public re-export of the private `azumaProxy2_P_le` (`P ≤ N^{C_P}`, `C_P = 11 + (4k+4)θ`; RBM2D
`AzumaProxyN_P_le_pub`, `AzumaProxyN:2442`). -/
theorem AzumaProxyN_P_le_pub (k : ℕ) {c0 θ N : ℝ} (hc0 : 0 < c0) (hθ : 0 ≤ θ) (hN1 : 1 ≤ N)
    (hbig : 2000 * (2 ^ k * ((k * (k + 1) : ℕ) : ℝ) * (c0⁻¹) ^ (k + 2)) ^ 2 ≤ N) :
    2000 * ((2 * N ^ θ) ^ k * (((k * (k + 1) : ℕ) : ℝ) * N * (N ^ θ / c0) ^ (k + 2))) ^ 2 * N ^ 8
      ≤ N ^ (11 + (4 * k + 4) * θ) :=
  azumaProxy2_P_le k hc0 hθ hN1 hbig

/-- Public re-export of the private `azumaProxy2_rowsum_Ugen` (row sums of the `Ugen` kernel;
RBM2D `AzumaProxyN_rowsum_Ugen_pub`, `AzumaProxyN:2449`). -/
theorem AzumaProxyN_rowsum_Ugen_pub {d L : ℕ} [NeZero L] {g : ℝ} (hL : 3 ≤ L) {E : ℝ}
    (hE : |E| ≤ 2) {k : ℕ} (σ : Fin k → Bool) {v w : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1)
    (hw0 : 0 ≤ w) (hw1 : w < 1) (a : Fin k → Zd d L) :
    ∑ b : Fin k → Zd d L, ‖∏ i : Fin k,
      uKer d L g (cycProd (fun i => mSigma E (σ i)) i) v w (a i) (b i)‖ ≤
      (1 + (1 - w)⁻¹) ^ k :=
  azumaProxy2_rowsum_Ugen hL hE σ hv0 hv1 hw0 hw1 a

end PublicAliases

/-! ## 8. Compiled nonempty instances (`d = 3`)

Data (merged `GridGoodNInst`, `Induction/GridGoodN.lean` §7, and `AzumaProxyNInst`, T2159): `sz0`
(`L_n = 4 (n+1)`, `W_n = (2 (n+1))^5`, `lam_n = (2 (n+1))^{-6}`; at `n = 0`: `L = 4`, `W = 32`,
`N = 2097152`), the energy `E ≡ 1/2` (`Einst`, `|E| ≤ 2 - κ` for `κ = 1`), `τ' = 1/2`, the window
`s ≡ 0` (`sInst`), `t ≡ 1/32` (`vg`), the grid `K ≡ 4` (`Kg`; `Δ = 1/128`, `u_j = j/128`), the loop
length `k = 3` and the signs `σ`.  No hypothesis of `yMomentsN`, `yMomentsUnifN`, `yMomentsN_of_unif`
is left open: `SizeTendsto` is `sz0_tendsto`, `RangeCond (1/2) vg` is proved below (`N^{-1/2} ≤ 31/32`
for `N ≥ 4`), the rest is arithmetic at the data.  The eventual statements are applied at an `n` taken
from the filter (`Filter.Eventually.exists`; the eventual threshold `N ≥ 2000 A²` is not met at `n = 0`,
see the report, (a)). -/

namespace AzumaProxyN2Inst

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.GridGoodNInst
  RBM.Ind.AzumaProxyNInst

/-- `RangeCond` at the instance: `N^{-1+1/2} ≤ 1 - 1/32` for `N ≥ 4`. -/
private theorem azumaProxy2_rangeCond_vg : sz0.RangeCond (1 / 2) vg := by
  filter_upwards [sz0_tendsto.eventually_ge_atTop (4 : ℝ)] with n hn
  have h4 : (0 : ℝ) < 4 := by norm_num
  have h := Real.rpow_le_rpow_of_nonpos h4 hn (show (-1 + (1 / 2 : ℝ)) ≤ 0 by norm_num)
  have h2 : (4 : ℝ) ^ (-1 + (1 / 2 : ℝ)) = 1 / 2 := by
    rw [show (-1 + (1 / 2 : ℝ)) = -(1 / 2) by norm_num, Real.rpow_neg (by norm_num)]
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h3 : (1 : ℝ) - vg n = 31 / 32 := by norm_num [vg]
  rw [h3]
  linarith

private theorem azumaProxy2_Kg_ne_zero : ∀ n, Kg n ≠ 0 := fun n => by simp [Kg]

private theorem azumaProxy2_gridStep_pos (n : ℕ) : 0 < gridStep sInst vg Kg n := by
  unfold gridStep
  exact div_pos (by norm_num [vg, sInst]) (Nat.cast_pos.2 (Nat.pos_of_ne_zero (azumaProxy2_Kg_ne_zero n)))

/-- **Instance of `AzumaProxyN_integrable_normPow8_incr`, `AzumaProxyN_integral_normPow8_incr_le`** at
`n = 0`, `j = 0` (`N = 2097152`). -/
theorem normPow8_instance :
    Integrable (fun ω : PathΩ sz0 => ‖Sizes.seqXmat sz0 0 (ω (0 + 1))‖ ^ 8) (pathP sz0) ∧
      ∫ ω, ‖Sizes.seqXmat sz0 0 (ω (0 + 1))‖ ^ 8 ∂(pathP sz0)
        ≤ 6881280 * (sz0.size 0 : ℝ) ^ 16 :=
  ⟨AzumaProxyN_integrable_normPow8_incr sz0 0 0, AzumaProxyN_integral_normPow8_incr_le sz0 0 0⟩

/-- **Instance of `yMomentsUnifN`** at the data above (`k = 3`, every `σ`): all seven hypotheses are
discharged; `C_P` is obtained before the grid `Kg`, and the conclusion is applied at `K = Kg` at a
concrete `n` (from the eventual filter) with the stopping time `τ ≡ K n` and the window `Δ > 0`. -/
theorem yMomentsUnifN_instance (σ : Fin 3 → Bool) :
    ∃ C_P : ℝ, 0 ≤ C_P ∧ ∃ n : ℕ, ∃ P : ℝ, 0 ≤ P ∧ P ≤ ((sz0.size n : ℕ) : ℝ) ^ C_P ∧
      0 < gridStep sInst vg Kg n ∧
      YMomentBoundsN sz0 (Einst n) σ (gridTime sInst vg Kg n) (fun _ => Kg n) (Kg n)
        (fun j ω => YvecN sz0 Einst sInst vg Kg n j σ ω)
        (fun _ => gridStep sInst vg Kg n ^ 2 * P) (fun _ => gridStep sInst vg Kg n ^ 4 * P ^ 2) := by
  obtain ⟨C_P, hC, hev⟩ := yMomentsUnifN sz0 1 (1 / 2) Einst sInst vg one_pos
    (fun n => by norm_num [Einst]) sInst_nonneg sInst_le_vg vg_lt_one sz0_tendsto azumaProxy2_rangeCond_vg 3 σ
  obtain ⟨n, P, hP0, hPN, hτ⟩ := (hev Kg azumaProxy2_Kg_ne_zero).exists
  exact ⟨C_P, hC, n, P, hP0, hPN, azumaProxy2_gridStep_pos n, hτ (fun _ => Kg n) (fun j => MeasurableSet.const _)⟩

/-- **Instance of `yMomentsN_of_unif`** at the data above: the merged `YMomentsN` at the grid `Kg`,
obtained from `yMomentsUnifN` through `yMomentsN_of_unif`, applied at a concrete `n` (from the
eventual filter) with the stopping time `τ ≡ K n` and the window `Δ > 0`. -/
theorem yMomentsN_of_unif_instance (σ : Fin 3 → Bool) :
    ∃ C_P : ℝ, 0 ≤ C_P ∧ ∃ n : ℕ, ∃ P : ℝ, 0 ≤ P ∧ P ≤ ((sz0.size n : ℕ) : ℝ) ^ C_P ∧
      0 < gridStep sInst vg Kg n ∧
      YMomentBoundsN sz0 (Einst n) σ (gridTime sInst vg Kg n) (fun _ => Kg n) (Kg n)
        (fun j ω => YvecN sz0 Einst sInst vg Kg n j σ ω)
        (fun _ => gridStep sInst vg Kg n ^ 2 * P) (fun _ => gridStep sInst vg Kg n ^ 4 * P ^ 2) := by
  obtain ⟨C_P, hC, hev⟩ := yMomentsN_of_unif sz0 (yMomentsUnifN sz0 1 (1 / 2) Einst sInst vg) Kg
    one_pos (fun n => by norm_num [Einst]) sInst_nonneg sInst_le_vg vg_lt_one azumaProxy2_Kg_ne_zero
    sz0_tendsto azumaProxy2_rangeCond_vg 3 σ
  obtain ⟨n, P, hP0, hPN, hτ⟩ := hev.exists
  exact ⟨C_P, hC, n, P, hP0, hPN, azumaProxy2_gridStep_pos n, hτ (fun _ => Kg n) (fun j => MeasurableSet.const _)⟩

/-- **Instance of `yMomentsN`** at the data above (`k = 3`, every `σ`): all eight hypotheses are
discharged; applied at a concrete `n` (from the eventual filter) with the stopping time `τ ≡ K n`:
the `Y` moment inputs hold for `YvecN`, and at `j = 0`, `m = 1` (and every label `b`) the real and
imaginary parts of the stopped propagated increment have fourth moment at most `Δ⁴ P²`. -/
theorem yMomentsN_instance (σ : Fin 3 → Bool) :
    ∃ n : ℕ, ∃ P : ℝ, 0 ≤ P ∧ 0 < gridStep sInst vg Kg n ∧
      YMomentBoundsN sz0 (Einst n) σ (gridTime sInst vg Kg n) (fun _ => Kg n) (Kg n)
        (fun j ω => YvecN sz0 Einst sInst vg Kg n j σ ω)
        (fun _ => gridStep sInst vg Kg n ^ 2 * P) (fun _ => gridStep sInst vg Kg n ^ 4 * P ^ 2) ∧
      ∀ b : Fin 3 → Zd 3 (sz0.L n),
        ∫ ω, (stoppedEdgeN sz0 (Einst n) σ (gridTime sInst vg Kg n)
            (gridTime sInst vg Kg n 1) (fun _ => Kg n)
            (fun j ω => YvecN sz0 Einst sInst vg Kg n j σ ω) b 0 ω).re ^ 4 ∂(pathP sz0)
          ≤ gridStep sInst vg Kg n ^ 4 * P ^ 2 ∧
        ∫ ω, (stoppedEdgeN sz0 (Einst n) σ (gridTime sInst vg Kg n)
            (gridTime sInst vg Kg n 1) (fun _ => Kg n)
            (fun j ω => YvecN sz0 Einst sInst vg Kg n j σ ω) b 0 ω).im ^ 4 ∂(pathP sz0)
          ≤ gridStep sInst vg Kg n ^ 4 * P ^ 2 := by
  obtain ⟨C_P, hC, hev⟩ := yMomentsN sz0 1 (1 / 2) Einst sInst vg Kg one_pos
    (fun n => by norm_num [Einst]) sInst_nonneg sInst_le_vg vg_lt_one azumaProxy2_Kg_ne_zero sz0_tendsto
    azumaProxy2_rangeCond_vg 3 σ
  obtain ⟨n, P, hP0, -, hτ⟩ := hev.exists
  have hY := hτ (fun _ => Kg n) (fun j => MeasurableSet.const _)
  have hK1 : 1 ≤ Kg n := Nat.one_le_iff_ne_zero.2 (azumaProxy2_Kg_ne_zero n)
  refine ⟨n, P, hP0, azumaProxy2_gridStep_pos n, hY, fun b => ?_⟩
  have h := hY.2 1 hK1 b 0 Nat.zero_lt_one
  exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

/-- **Instance of `AzumaProxyN_YfieldsW`** at `n = 0`, `j = 0` (`j + 1 = 1 ≤ Kg 0 = 4`), `E ≡ 1/2`,
`k = 3`, `σ = (+,-,+)`, for every weight vector `κ` (with `S = Σ_c ‖κ_c‖`), the stopping time
`τ ≡ Kg 0` and the constants `C₂ = k (k + 1) N η^{-(k+2)}` (the Hermitian second-derivative bound of the
merged `hermTestFunLoopN`) and `P = 2000 (S C₂)² N⁸`: every hypothesis is discharged (`|E| < 2`,
`0 ≤ s ≤ t < 1`, the bound `hC2`, `hrow`, `hP`); the data is not degenerate (`Δ = 1/128 > 0`,
`N = 2097152`). -/
theorem yfieldsW_instance (κ : (Fin 3 → Zd 3 (sz0.L 0)) → ℂ) :
    let C2 : ℝ := ((3 * (3 + 1) : ℕ) : ℝ) * (sz0.size 0 : ℝ) *
      (etaT (Einst 0) (gridTime sInst vg Kg 0 1))⁻¹ ^ (3 + 2)
    let P : ℝ := 2000 * ((∑ c, ‖κ c‖) * C2) ^ 2 * (sz0.size 0 : ℝ) ^ 8
    (pathP sz0)[fun ω => (AzumaProxyN_stopW sz0 Einst sInst vg Kg 0 0 sig3 κ (fun _ => Kg 0) ω).re
        | filt sz0 0] =ᵐ[pathP sz0] 0 ∧
    (pathP sz0)[fun ω => (AzumaProxyN_stopW sz0 Einst sInst vg Kg 0 0 sig3 κ (fun _ => Kg 0) ω).im
        | filt sz0 0] =ᵐ[pathP sz0] 0 ∧
    Integrable (fun ω => (AzumaProxyN_stopW sz0 Einst sInst vg Kg 0 0 sig3 κ (fun _ => Kg 0) ω).re ^ 4)
      (pathP sz0) ∧
    Integrable (fun ω => (AzumaProxyN_stopW sz0 Einst sInst vg Kg 0 0 sig3 κ (fun _ => Kg 0) ω).im ^ 4)
      (pathP sz0) ∧
    (pathP sz0)[fun ω => (AzumaProxyN_stopW sz0 Einst sInst vg Kg 0 0 sig3 κ (fun _ => Kg 0) ω).re ^ 2
        | filt sz0 0] ≤ᵐ[pathP sz0] (fun _ => gridStep sInst vg Kg 0 ^ 2 * P) ∧
    (pathP sz0)[fun ω => (AzumaProxyN_stopW sz0 Einst sInst vg Kg 0 0 sig3 κ (fun _ => Kg 0) ω).im ^ 2
        | filt sz0 0] ≤ᵐ[pathP sz0] (fun _ => gridStep sInst vg Kg 0 ^ 2 * P) ∧
    ∫ ω, (AzumaProxyN_stopW sz0 Einst sInst vg Kg 0 0 sig3 κ (fun _ => Kg 0) ω).re ^ 4 ∂(pathP sz0)
      ≤ gridStep sInst vg Kg 0 ^ 4 * P ^ 2 ∧
    ∫ ω, (AzumaProxyN_stopW sz0 Einst sInst vg Kg 0 0 sig3 κ (fun _ => Kg 0) ω).im ^ 4 ∂(pathP sz0)
      ≤ gridStep sInst vg Kg 0 ^ 4 * P ^ 2 := by
  intro C2 P
  have hu : gridTime sInst vg Kg 0 1 = 1 / 128 := grid_data.2.2.1
  have hu0 : 0 ≤ gridTime sInst vg Kg 0 1 := by rw [hu]; norm_num
  have hu1 : gridTime sInst vg Kg 0 1 < 1 := by rw [hu]; norm_num
  have hη := etaT_pos (Einst_abs_lt 0) hu1
  refine AzumaProxyN_YfieldsW sz0 Einst sInst vg Kg 0 0 (Einst_abs_lt 0) (sInst_nonneg 0)
    (sInst_le_vg 0) (vg_lt_one 0) (by simp [Kg]) sig3 κ (Smax := ∑ c, ‖κ c‖) (C2 := C2) (P := P)
    (Finset.sum_nonneg fun c _ => norm_nonneg _) (by positivity) le_rfl
    (fun a M y hM hy => ?_) le_rfl (fun _ => Kg 0) (fun j => MeasurableSet.const _)
  exact (hermTestFunLoopN sz0 3 0 (Einst 0) (gridTime sInst vg Kg 0 1) (Einst_abs_lt 0) hu0 hu1
    sig3 a).2 M y hM hy

end AzumaProxyN2Inst

section PublicInstances

/-- Instance of `AzumaProxyN_c0_pos_pub` (`κ = 1`, `E = 1/2`): `c₀ = √3 / 2 > 0`. -/
example : 0 < Real.sqrt (1 * (4 - 1)) / 2 :=
  AzumaProxyN_c0_pos_pub (κ := 1) (E := 1 / 2) one_pos (by norm_num [abs_of_pos])

/-- Instance of `AzumaProxyN_inv_one_sub_le_pub` (`u = 1/4 ≤ t = 1/2`, `N = 4`, `τ' = 1/2`:
`N^{-1/2} = 1/2 ≤ 1 - t`). -/
example : (1 - (1 / 4 : ℝ))⁻¹ ≤ (4 : ℝ) ^ (1 - (1 / 2 : ℝ)) :=
  AzumaProxyN_inv_one_sub_le_pub (u := 1 / 4) (t := 1 / 2) (τ' := 1 / 2) (N := 4) (by norm_num)
    (by norm_num) (by
      rw [show (-1 + (1 / 2 : ℝ)) = -(1 / 2) by norm_num, Real.rpow_neg (by norm_num),
        show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num)

/-- Instance of `AzumaProxyN_etaT_inv_le_pub` (`κ = 1`, `E = 1/2`, `u = 1/4 ≤ t = 1/2`, `N = 4`,
`τ' = 1/2`). -/
example : (etaT (1 / 2) (1 / 4))⁻¹ ≤ (4 : ℝ) ^ (1 - (1 / 2 : ℝ)) / (Real.sqrt (1 * (4 - 1)) / 2) :=
  AzumaProxyN_etaT_inv_le_pub (κ := 1) (E := 1 / 2) (u := 1 / 4) (t := 1 / 2) (τ' := 1 / 2)
    (N := 4) one_pos (by norm_num [abs_of_pos]) (by norm_num) (by norm_num) (by
      rw [show (-1 + (1 / 2 : ℝ)) = -(1 / 2) by norm_num, Real.rpow_neg (by norm_num),
        show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num)

/-- Instance of `AzumaProxyN_P_le_pub` (`k = 1`, `c₀ = 1`, `θ = 0`, `N = 32000 = 2000 A²`,
`A = 2^1 · 1·2 · 1 = 4`). -/
example : 2000 * ((2 * (32000 : ℝ) ^ (0 : ℝ)) ^ 1 *
      (((1 * (1 + 1) : ℕ) : ℝ) * 32000 * ((32000 : ℝ) ^ (0 : ℝ) / 1) ^ (1 + 2))) ^ 2 * 32000 ^ 8
    ≤ (32000 : ℝ) ^ (11 + (4 * (1 : ℕ) + 4) * (0 : ℝ)) :=
  AzumaProxyN_P_le_pub 1 (c0 := 1) (θ := 0) (N := 32000) one_pos le_rfl (by norm_num)
    (by norm_num)

/-- Instance of `AzumaProxyN_rowsum_Ugen_pub` at `d = 3`, `L = 4`, `g = 1/64`, `E = 1/2`, `k = 3`,
`σ = (+,-,+)`, `v = 1/128`, `w = 1/32`, `a = 0`. -/
example : ∑ b : Fin 3 → Zd 3 4, ‖∏ i : Fin 3,
      uKer 3 4 (1 / 64) (cycProd (fun i => mSigma (1 / 2) (AzumaProxyNInst.sig3 i)) i)
        (1 / 128) (1 / 32) ((fun _ => (0 : Zd 3 4)) i) (b i)‖ ≤ (1 + (1 - (1 / 32 : ℝ))⁻¹) ^ 3 :=
  AzumaProxyN_rowsum_Ugen_pub (d := 3) (L := 4) (g := 1 / 64) (by norm_num) (E := 1 / 2)
    (by norm_num [abs_of_pos]) AzumaProxyNInst.sig3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (fun _ => 0)

end PublicInstances

/-! ## 9. `YvecN` is not a.e. zero at the instance data (RBM2D `AzumaProxyN` §8b, `:1388-1800`)

At the instance data (`s ≡ 0`, `t ≡ 1/32`, `E ≡ 1/2`, `K ≡ 4`, `sz0`), for every size index `n`, the
step `j = 0`, `σ = (+,-,+)` and `b = (0,0,0)`, the remainder `YvecN` is not `0` a.e.
(`yvecN_not_ae_zero`).  Since `s ≡ 0`, `H_0 = 0` and `H_1 = √Δ X_1` is independent of `F_0`, so a.e.
`Y_0 = T(X_1) - c` with `T(x) = Φ(√Δ X(x)) - √Δ ∂Φ(0)[X(x)]` (`Φ = 𝓛_{u_1,σ,b}`, `azumaProxy2_yvecN_ae_eq`) and a
constant `c` (the deterministic `𝒦` part of `AvecN` and the conditional mean).  If `Y_0 = 0` a.e., then
`T = c` at every point of the support of the Gaussian law of `X_1` at which `T` is continuous
(`azumaProxy2_eq_of_ae_eq_of_ball_pos`, `azumaProxy2_PF_ball_pos`), in particular at the scalar
matrices `μ 1`, where `Φ` is the
explicit rational function `f(y) = W^{-2d} (y - z)⁻² (y - z̄)⁻¹` (`azumaProxy2_phiN_scalar`, from the merged
`azumaProxy_loop3_scalar`).  Then `f(y) = f(0) + y D` for all real `y`, so `f(y) + f(-y) = 2 f(0)`;
letting `y → ∞` gives `f(0) = 0`, which is false (`z ≠ 0`).  Only `Im z_{u_1} > 0` is used, not the
value of `∂Φ(0)`.  `d = 3`: `W^{-2d}` replaces RBM2D's `W⁻⁴`, and `svarF_diag > 0` for every `g`
replaces `svar_diag_pos`. -/

section YNonzero

/-- The directional derivative along the real line `y ↦ M + y X` at `0` is `fderiv ℝ Ψ M X`, for
`Ψ` differentiable at `M` (copy of the private `azumaProxy_hasDerivAt_dir` of T2159). -/
private theorem azumaProxy2_hasDerivAt_dir {ι : Type*} [Fintype ι] [DecidableEq ι]
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

private theorem azumaProxy2_dirDerivN_eq {d L W : ℕ} [NeZero L] [NeZero W]
    {Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ} {M : Matrix (Idx d L W) (Idx d L W) ℂ}
    (X : Matrix (Idx d L W) (Idx d L W) ℂ) (hd : DifferentiableAt ℝ Φ M) :
    dirDerivN Φ M X = fderiv ℝ Φ M X :=
  (azumaProxy2_hasDerivAt_dir X hd).deriv

/-- A diagonal coordinate has positive variance (`svarF_diag`). -/
private theorem azumaProxy2_gvarF_diag_pos {d L W : ℕ} [NeZero W] (g : ℝ) (i : Idx d L W) :
    0 < (gvarF d L W g (i, i, true) : ℝ) := by
  have : (gvarF d L W g (i, i, true) : ℝ) = svarF d L W g i i := by
    unfold gvarF
    simp only [↓reduceIte]
    rfl
  rw [this, svarF_diag]
  have hW : (0 : ℝ) < (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  positivity

/-- Every ball around the scalar point `μ 1` has positive Gaussian measure (the diagonal coordinates
have positive variance; the other coordinates of `azumaProxy_xmu μ` are `0`, in the support of the
Gaussian or of the Dirac mass). -/
private theorem azumaProxy2_PF_ball_pos {d L W : ℕ} [NeZero L] [NeZero W] (g : ℝ) (μ : ℝ) {ε : ℝ}
    (hε : 0 < ε) : 0 < PF d L W g (Metric.ball (azumaProxy_xmu d L W μ) ε) := by
  unfold PF
  rw [Measure.infinitePi_eq_pi, ball_pi _ hε, Measure.pi_pi]
  rw [pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro c _
  by_cases hv : gvarF d L W g c = 0
  · have hx : azumaProxy_xmu d L W μ c = 0 := by
      by_contra hne
      have hc : c.1 = c.2.1 ∧ c.2.2 = true := by
        by_contra hnc
        exact hne (by simp [azumaProxy_xmu, hnc])
      obtain ⟨i, j, b⟩ := c
      obtain ⟨h1, h2⟩ := hc
      simp only at h1 h2
      subst h1; subst h2
      have := azumaProxy2_gvarF_diag_pos (d := d) (L := L) (W := W) g i
      exact absurd hv (ne_of_gt (by exact_mod_cast this))
    rw [hv, gaussianReal_zero_var, Measure.dirac_apply' _ Metric.isOpen_ball.measurableSet]
    rw [Set.indicator_of_mem (by rw [hx]; exact Metric.mem_ball_self hε)]
    simp
  · have : (gaussianReal 0 (gvarF d L W g c)).IsOpenPosMeasure :=
      (gaussianReal_absolutelyContinuous' 0 hv).isOpenPosMeasure
    exact (Metric.isOpen_ball.measure_pos _ (Metric.nonempty_ball.2 hε)).ne'

/-- A function continuous at `x` and a.e. equal to `c` equals `c` at `x` if every ball around `x`
has positive measure. -/
private theorem azumaProxy2_eq_of_ae_eq_of_ball_pos {α : Type*} [MetricSpace α] [MeasurableSpace α]
    {P : Measure α} {T : α → ℂ} {c : ℂ} {x : α} (hT : ContinuousAt T x) (hae : ∀ᵐ y ∂P, T y = c)
    (hball : ∀ ε > 0, 0 < P (Metric.ball x ε)) : T x = c := by
  by_contra hne
  have hev : ∀ᶠ y in nhds x, T y ≠ c := hT.eventually_ne hne
  obtain ⟨ε, hε, hsub⟩ := Metric.eventually_nhds_iff.1 hev
  have h0 : P {y | ¬ T y = c} = 0 := ae_iff.1 hae
  have h1 : P (Metric.ball x ε) = 0 :=
    measure_mono_null (fun y hy => hsub (Metric.mem_ball.1 hy)) h0
  exact (hball ε hε).ne' h1

namespace AzumaProxyN2Inst

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.GridGoodNInst
  RBM.Ind.AzumaProxyNInst
open scoped Topology

variable (n : ℕ)

private theorem azumaProxy2_gridTime_one : gridTime sInst vg Kg n 1 = 1 / 128 := by
  norm_num [gridTime, gridStep, sInst, vg, Kg]

/-- The loop family `b ↦ (M ↦ 𝓛_{u_1,(+,-,+),b}(M))` of the step `0 → 1` at size `n`. -/
private abbrev azumaProxy2_phiN : (Fin 3 → Zd 3 (sz0.L n)) →
    Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ → ℂ :=
  loopFamN sz0 Einst sInst vg Kg n 0 sig3

/-- The three-loop observables of the step `0 → 1` are in the Hermitian test class at every size. -/
private theorem azumaProxy2_phiN_hermTestFun (b : Fin 3 → Zd 3 (sz0.L n)) : HermTestFun sz0 n (azumaProxy2_phiN n b) := by
  have hu : gridTime sInst vg Kg n 1 = 1 / 128 := azumaProxy2_gridTime_one n
  exact (hermTestFunLoopN sz0 3 n (Einst n) (gridTime sInst vg Kg n 1) (Einst_abs_lt n)
    (by rw [hu]; norm_num) (by rw [hu]; norm_num) sig3 b).1

/-- The label `b = (0,0,0)` (all three insertions in block `0`). -/
abbrev b0n : Fin 3 → Zd 3 (sz0.L n) := fun _ => 0

/-- The spectral parameter `z_1 = z_{u_1}` at size `n`. -/
private abbrev azumaProxy2_z1n : ℂ := zt (Einst n) (gridTime sInst vg Kg n 1)

private theorem azumaProxy2_z1n_im_pos : 0 < (azumaProxy2_z1n n).im := by
  have hu : gridTime sInst vg Kg n 1 = 1 / 128 := azumaProxy2_gridTime_one n
  unfold azumaProxy2_z1n
  rw [zt_im, hu]
  exact mul_pos (by norm_num) (mE_im_pos (Einst_abs_lt n))

private theorem azumaProxy2_z1n_ne_zero : azumaProxy2_z1n n ≠ 0 := fun h => by
  have := azumaProxy2_z1n_im_pos n
  rw [h] at this
  simp at this

private theorem azumaProxy2_z1n_sub_ne (y : ℝ) : (y : ℂ) - azumaProxy2_z1n n ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  have h2 := azumaProxy2_z1n_im_pos n
  simp at this
  linarith

private theorem azumaProxy2_z1n_sub_conj_ne (y : ℝ) : (y : ℂ) - (starRingEnd ℂ) (azumaProxy2_z1n n) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  have h2 := azumaProxy2_z1n_im_pos n
  simp at this
  linarith

/-- The explicit scalar profile `f(y) = W^{-2d} (y - z)⁻² (y - z̄)⁻¹` (`d = 3`). -/
private noncomputable def azumaProxy2_fscn (y : ℝ) : ℂ :=
  (((sz0.W n : ℕ) : ℂ)⁻¹ ^ 3) ^ 2 * ((y : ℂ) - azumaProxy2_z1n n)⁻¹ ^ 2 *
    ((y : ℂ) - (starRingEnd ℂ) (azumaProxy2_z1n n))⁻¹

/-- The observable `𝓛_{u_1,(+,-,+),(0,0,0)}` at a scalar matrix `y 1` is `f(y)`. -/
private theorem azumaProxy2_phiN_scalar (y : ℝ) :
    azumaProxy2_phiN n (b0n n) ((y : ℂ) • (1 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ))
      = azumaProxy2_fscn n y := by
  have hl : loopOf sig3 (b0n n) = (⟨[true, false, true], [0, 0, 0]⟩ : LoopIdx (Zd 3 (sz0.L n))) := by
    simp [loopOf, List.ofFn_succ, sig3, b0n]
  unfold azumaProxy2_phiN loopFamN
  rw [hl]
  exact azumaProxy_loop3_scalar (y : ℂ) (azumaProxy2_z1n n) (azumaProxy2_z1n_sub_ne n y)
    (azumaProxy2_z1n_sub_conj_ne n y) 0

/-- The observable `Φ = 𝓛_{u_1,(+,-,+),(0,0,0)}`. -/
private abbrev azumaProxy2_Φ0n : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ → ℂ :=
  azumaProxy2_phiN n (b0n n)

private theorem azumaProxy2_Φ0n_scalar (y : ℝ) :
    azumaProxy2_Φ0n n ((y : ℂ) • (1 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ))
      = azumaProxy2_fscn n y := azumaProxy2_phiN_scalar n y

private theorem azumaProxy2_Φ0n_measurable : Measurable (azumaProxy2_Φ0n n) :=
  (walk_measurable_loopL 3 (sz0.L n) (sz0.W n) (azumaProxy2_z1n n) (loopOf sig3 (b0n n))).comp
    (walk_measurable_blockMat 3 (sz0.L n) (sz0.W n))

/-- `T(x) = Φ(√Δ X(x)) - √Δ ∂Φ(0)[X(x)]`. -/
private noncomputable def azumaProxy2_Tfun (x : Ω 3 (sz0.L n) (sz0.W n)) : ℂ :=
  azumaProxy2_Φ0n n (((Real.sqrt (gridStep sInst vg Kg n) : ℝ) : ℂ) • Xmat 3 (sz0.L n) (sz0.W n) x)
    - ((Real.sqrt (gridStep sInst vg Kg n) : ℝ) : ℂ) *
      dirDerivN (azumaProxy2_Φ0n n) 0 (Xmat 3 (sz0.L n) (sz0.W n) x)

/-- The deterministic constant `𝒦_{u_1,σ,b}` cancelled by the conditional expectation. -/
private noncomputable abbrev azumaProxy2_Kc0 : ℂ :=
  sz0.STKloop n (Einst n) (gridTime sInst vg Kg n 1) sig3 (b0n n)

private noncomputable def azumaProxy2_psi0 (x : Sizes.SeqΩ sz0) : ℂ :=
  azumaProxy2_Φ0n n (((Real.sqrt (gridStep sInst vg Kg n) : ℝ) : ℂ) • Sizes.seqXmat sz0 n x) - azumaProxy2_Kc0 n

private theorem azumaProxy2_psi0_measurable : Measurable (azumaProxy2_psi0 n) := by
  have hX : Measurable fun x : Sizes.SeqΩ sz0 => Sizes.seqXmat sz0 n x :=
    (continuous_Xmat 3 (sz0.L n) (sz0.W n)).measurable.comp (Sizes.measurable_slice sz0 n)
  have h1 : Measurable fun x : Sizes.SeqΩ sz0 =>
      ((Real.sqrt (gridStep sInst vg Kg n) : ℝ) : ℂ) • Sizes.seqXmat sz0 n x :=
    (measurable_const_smul ((Real.sqrt (gridStep sInst vg Kg n) : ℝ) : ℂ)).comp hX
  exact ((azumaProxy2_Φ0n_measurable n).comp h1).sub_const (azumaProxy2_Kc0 n)

private theorem azumaProxy2_pathH_one (ω : PathΩ sz0) :
    pathH sz0 sInst vg Kg n 1 ω
      = ((Real.sqrt (gridStep sInst vg Kg n) : ℝ) : ℂ) • Sizes.seqXmat sz0 n (ω 1) := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, pathH_succ,
    azumaProxy_pathH_zero_of_s_zero sz0 sInst vg Kg n rfl ω, zero_add]

private theorem azumaProxy2_avecN_one (ω : PathΩ sz0) :
    AvecN sz0 Einst sInst vg Kg n 1 sig3 ω (b0n n) = azumaProxy2_psi0 n (ω 1) := by
  unfold AvecN
  rw [azumaProxy2_pathH_one n ω]
  simp only [Sizes.STLKM, Sizes.STLM, loopFine, loopM_eq_loopL, azumaProxy2_psi0]
  rfl

private theorem azumaProxy2_condExp_avecN_one :
    (pathP sz0)[fun ω' => AvecN sz0 Einst sInst vg Kg n 1 sig3 ω' (b0n n) | filt sz0 0]
      =ᵐ[pathP sz0] fun _ => ∫ ω, azumaProxy2_psi0 n (ω 1) ∂(pathP sz0) := by
  have hle₁ : MeasurableSpace.comap (fun ω : PathΩ sz0 => ω (0 + 1)) inferInstance ≤
      (inferInstance : MeasurableSpace (PathΩ sz0)) := (measurable_pi_apply (0 + 1)).comap_le
  have hf : StronglyMeasurable[MeasurableSpace.comap (fun ω : PathΩ sz0 => ω (0 + 1))
      inferInstance] (fun ω : PathΩ sz0 => azumaProxy2_psi0 n (ω (0 + 1))) :=
    ((azumaProxy2_psi0_measurable n).comp
      (comap_measurable (fun ω : PathΩ sz0 => ω (0 + 1)))).stronglyMeasurable
  have h := condExp_indep_eq hle₁ ((filt sz0).le 0) hf (indep_incr sz0 0)
  have hfun : (fun ω' : PathΩ sz0 => AvecN sz0 Einst sInst vg Kg n 1 sig3 ω' (b0n n))
      = fun ω' => azumaProxy2_psi0 n (ω' (0 + 1)) := funext (azumaProxy2_avecN_one n)
  rw [hfun]
  exact h

private theorem azumaProxy2_yvecN_ae_eq :
    ∃ c : ℂ, ∀ᵐ ω ∂(pathP sz0),
      YvecN sz0 Einst sInst vg Kg n 0 sig3 ω (b0n n)
        = azumaProxy2_Tfun n (Sizes.slice sz0 n (ω 1)) - c := by
  refine ⟨azumaProxy2_Kc0 n + ∫ ω, azumaProxy2_psi0 n (ω 1) ∂(pathP sz0), ?_⟩
  filter_upwards [azumaProxy2_condExp_avecN_one n] with ω hω
  unfold YvecN martIncN ZvecN
  have h1 : AvecN sz0 Einst sInst vg Kg n (0 + 1) sig3 ω (b0n n) = azumaProxy2_psi0 n (ω 1) :=
    azumaProxy2_avecN_one n ω
  have hω' : (pathP sz0)[fun ω' => AvecN sz0 Einst sInst vg Kg n (0 + 1) sig3 ω' (b0n n)
      | filt sz0 0] ω = ∫ ω, azumaProxy2_psi0 n (ω 1) ∂(pathP sz0) := hω
  have h0 : pathH sz0 sInst vg Kg n 0 ω = 0 :=
    azumaProxy_pathH_zero_of_s_zero sz0 sInst vg Kg n rfl ω
  have hD : loopDerivN 3 (sz0.L n) (sz0.W n) (Einst n) (gridTime sInst vg Kg n (0 + 1))
      (pathH sz0 sInst vg Kg n 0 ω) (Sizes.seqXmat sz0 n (ω (0 + 1))) sig3 (b0n n)
      = dirDerivN (azumaProxy2_Φ0n n) 0 (Xmat 3 (sz0.L n) (sz0.W n) (Sizes.slice sz0 n (ω 1))) := by
    rw [h0]; rfl
  rw [h1, hω', hD]
  unfold azumaProxy2_Tfun azumaProxy2_psi0
  have hX : Sizes.seqXmat sz0 n (ω 1)
      = Xmat 3 (sz0.L n) (sz0.W n) (Sizes.slice sz0 n (ω 1)) := rfl
  rw [hX]
  ring

private theorem azumaProxy2_Φ0n_differentiableAt : DifferentiableAt ℝ (azumaProxy2_Φ0n n) 0 :=
  ((azumaProxy2_phiN_hermTestFun n (b0n n)).contDiffAt 0 Matrix.isHermitian_zero).differentiableAt
    (by norm_num)

private theorem azumaProxy2_Tfun_eq (x : Ω 3 (sz0.L n) (sz0.W n)) :
    azumaProxy2_Tfun n x = azumaProxy2_Φ0n n (((Real.sqrt (gridStep sInst vg Kg n) : ℝ) : ℂ) • Xmat 3 (sz0.L n) (sz0.W n) x)
      - ((Real.sqrt (gridStep sInst vg Kg n) : ℝ) : ℂ) *
        fderiv ℝ (azumaProxy2_Φ0n n) 0 (Xmat 3 (sz0.L n) (sz0.W n) x) := by
  unfold azumaProxy2_Tfun
  rw [azumaProxy2_dirDerivN_eq _ (azumaProxy2_Φ0n_differentiableAt n)]

private theorem azumaProxy2_Tfun_measurable : Measurable (azumaProxy2_Tfun n) := by
  have hXc := continuous_Xmat 3 (sz0.L n) (sz0.W n)
  have h1 : Measurable fun x : Ω 3 (sz0.L n) (sz0.W n) =>
      ((Real.sqrt (gridStep sInst vg Kg n) : ℝ) : ℂ) • Xmat 3 (sz0.L n) (sz0.W n) x :=
    (hXc.const_smul ((Real.sqrt (gridStep sInst vg Kg n) : ℝ) : ℂ)).measurable
  have h2 : Continuous fun x : Ω 3 (sz0.L n) (sz0.W n) =>
      ((Real.sqrt (gridStep sInst vg Kg n) : ℝ) : ℂ) *
        fderiv ℝ (azumaProxy2_Φ0n n) 0 (Xmat 3 (sz0.L n) (sz0.W n) x) :=
    continuous_const.mul ((fderiv ℝ (azumaProxy2_Φ0n n) 0).continuous.comp hXc)
  have : azumaProxy2_Tfun n = fun x => azumaProxy2_Φ0n n (((Real.sqrt (gridStep sInst vg Kg n) : ℝ) : ℂ) •
      Xmat 3 (sz0.L n) (sz0.W n) x) - ((Real.sqrt (gridStep sInst vg Kg n) : ℝ) : ℂ) *
        fderiv ℝ (azumaProxy2_Φ0n n) 0 (Xmat 3 (sz0.L n) (sz0.W n) x) :=
    funext (azumaProxy2_Tfun_eq n)
  rw [this]
  exact ((azumaProxy2_Φ0n_measurable n).comp h1).sub h2.measurable

private theorem azumaProxy2_Tfun_continuousAt (μ : ℝ) :
    ContinuousAt (azumaProxy2_Tfun n) (azumaProxy_xmu 3 (sz0.L n) (sz0.W n) μ) := by
  have hXc := continuous_Xmat 3 (sz0.L n) (sz0.W n)
  have hherm : (((Real.sqrt (gridStep sInst vg Kg n) : ℝ) : ℂ) •
      Xmat 3 (sz0.L n) (sz0.W n) (azumaProxy_xmu 3 (sz0.L n) (sz0.W n) μ)).IsHermitian :=
    (Xmat_isHermitian _ _ _ _).smul (Complex.conj_ofReal _)
  have hΦc : ContinuousAt (azumaProxy2_Φ0n n) (((Real.sqrt (gridStep sInst vg Kg n) : ℝ) : ℂ) •
      Xmat 3 (sz0.L n) (sz0.W n) (azumaProxy_xmu 3 (sz0.L n) (sz0.W n) μ)) :=
    ((azumaProxy2_phiN_hermTestFun n (b0n n)).contDiffAt _ hherm).continuousAt
  have hf : Continuous fun x : Ω 3 (sz0.L n) (sz0.W n) =>
      ((Real.sqrt (gridStep sInst vg Kg n) : ℝ) : ℂ) • Xmat 3 (sz0.L n) (sz0.W n) x :=
    hXc.const_smul ((Real.sqrt (gridStep sInst vg Kg n) : ℝ) : ℂ)
  have h1 : ContinuousAt (fun x : Ω 3 (sz0.L n) (sz0.W n) =>
      azumaProxy2_Φ0n n (((Real.sqrt (gridStep sInst vg Kg n) : ℝ) : ℂ) • Xmat 3 (sz0.L n) (sz0.W n) x))
      (azumaProxy_xmu 3 (sz0.L n) (sz0.W n) μ) :=
    ContinuousAt.comp (g := azumaProxy2_Φ0n n)
      (f := fun x : Ω 3 (sz0.L n) (sz0.W n) =>
        ((Real.sqrt (gridStep sInst vg Kg n) : ℝ) : ℂ) • Xmat 3 (sz0.L n) (sz0.W n) x)
      hΦc hf.continuousAt
  have h2 : Continuous fun x : Ω 3 (sz0.L n) (sz0.W n) =>
      ((Real.sqrt (gridStep sInst vg Kg n) : ℝ) : ℂ) *
        fderiv ℝ (azumaProxy2_Φ0n n) 0 (Xmat 3 (sz0.L n) (sz0.W n) x) :=
    continuous_const.mul ((fderiv ℝ (azumaProxy2_Φ0n n) 0).continuous.comp hXc)
  have : azumaProxy2_Tfun n = fun x => azumaProxy2_Φ0n n (((Real.sqrt (gridStep sInst vg Kg n) : ℝ) : ℂ) •
      Xmat 3 (sz0.L n) (sz0.W n) x) - ((Real.sqrt (gridStep sInst vg Kg n) : ℝ) : ℂ) *
        fderiv ℝ (azumaProxy2_Φ0n n) 0 (Xmat 3 (sz0.L n) (sz0.W n) x) :=
    funext (azumaProxy2_Tfun_eq n)
  rw [this]
  exact h1.sub h2.continuousAt

private theorem azumaProxy2_fscn_zero_ne : azumaProxy2_fscn n 0 ≠ 0 := by
  have hz := azumaProxy2_z1n_ne_zero n
  have hW : (((sz0.W n : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne _)
  unfold azumaProxy2_fscn
  simp [hz, hW]

private theorem azumaProxy2_inv_sub_tendsto (w : ℂ) (s : ℝ) (hs : |s| = 1) :
    Tendsto (fun y : ℝ => (((s * y : ℝ) : ℂ) - w)⁻¹) atTop (𝓝 0) := by
  have h : Tendsto (fun y : ℝ => ‖((s * y : ℝ) : ℂ) - w‖) atTop atTop := by
    refine tendsto_atTop_mono (fun y => ?_)
      (tendsto_atTop_add_const_right atTop (-‖w‖) tendsto_id)
    have h1 : ‖((s * y : ℝ) : ℂ)‖ - ‖w‖ ≤ ‖((s * y : ℝ) : ℂ) - w‖ := norm_sub_norm_le _ _
    have h2 : ‖((s * y : ℝ) : ℂ)‖ = |s| * |y| := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    rw [hs, one_mul] at h2
    simp only [id]
    linarith [le_abs_self y]
  exact (Filter.tendsto_inv₀_cobounded).comp (tendsto_norm_atTop_iff_cobounded.1 h)

private theorem azumaProxy2_fscn_tendsto (s : ℝ) (hs : |s| = 1) :
    Tendsto (fun y : ℝ => azumaProxy2_fscn n (s * y)) atTop (𝓝 0) := by
  have h1 := azumaProxy2_inv_sub_tendsto (azumaProxy2_z1n n) s hs
  have h2 := azumaProxy2_inv_sub_tendsto ((starRingEnd ℂ) (azumaProxy2_z1n n)) s hs
  have := (tendsto_const_nhds (x := (((sz0.W n : ℕ) : ℂ)⁻¹ ^ 3) ^ 2)).mul ((h1.pow 2).mul h2)
  simpa [azumaProxy2_fscn, mul_assoc] using this

/-- `T` at a scalar direction. -/
private theorem azumaProxy2_Tfun_xmu (μ : ℝ) :
    azumaProxy2_Tfun n (azumaProxy_xmu 3 (sz0.L n) (sz0.W n) μ)
      = azumaProxy2_fscn n (Real.sqrt (gridStep sInst vg Kg n) * μ)
        - ((Real.sqrt (gridStep sInst vg Kg n) : ℝ) : ℂ) * (μ : ℂ) * fderiv ℝ (azumaProxy2_Φ0n n) 0 1 := by
  rw [azumaProxy2_Tfun_eq, azumaProxy_xmu_Xmat, smul_smul]
  have h1 : (((Real.sqrt (gridStep sInst vg Kg n) : ℝ) : ℂ) * (μ : ℂ))
      = ((Real.sqrt (gridStep sInst vg Kg n) * μ : ℝ) : ℂ) := by
    push_cast; ring
  rw [h1, azumaProxy2_Φ0n_scalar]
  have h2 : fderiv ℝ (azumaProxy2_Φ0n n) 0 ((μ : ℂ) • (1 : Matrix (Idx 3 (sz0.L n) (sz0.W n))
      (Idx 3 (sz0.L n) (sz0.W n)) ℂ)) = (μ : ℂ) * fderiv ℝ (azumaProxy2_Φ0n n) 0 1 := by
    rw [Complex.coe_smul, map_smul, Complex.real_smul]
  rw [h2]
  push_cast
  ring

/-- **`YvecN` is not a.e. zero** at the instance data, for every size index `n`, the step `j = 0`,
`σ = (+,-,+)` and `b = (0,0,0)`: the second-order remainder of the step is genuinely random.  (RBM2D
`yvecN_not_ae_zero`, `AzumaProxyN:1748`.) -/
theorem yvecN_not_ae_zero :
    ¬ (∀ᵐ ω ∂(pathP sz0), YvecN sz0 Einst sInst vg Kg n 0 sig3 ω (b0n n) = 0) := by
  intro h0
  obtain ⟨c, hc⟩ := azumaProxy2_yvecN_ae_eq n
  have h1 : ∀ᵐ ω ∂(pathP sz0), azumaProxy2_Tfun n (Sizes.slice sz0 n (ω (0 + 1))) = c := by
    filter_upwards [h0, hc] with ω h0ω hcω
    rw [h0ω] at hcω
    exact (sub_eq_zero.1 hcω.symm)
  have hmeas : Measurable (fun ω : PathΩ sz0 => Sizes.slice sz0 n (ω (0 + 1))) :=
    (Sizes.measurable_slice sz0 n).comp (measurable_pi_apply (0 + 1))
  have h2 : ∀ᵐ x ∂(PF 3 (sz0.L n) (sz0.W n) (sz0.lam n)), azumaProxy2_Tfun n x = c := by
    rw [← azumaProxy2_map_incr_slice sz0 n 0,
      ae_map_iff hmeas.aemeasurable (measurableSet_eq_fun (azumaProxy2_Tfun_measurable n)
        measurable_const)]
    exact h1
  have hT : ∀ μ : ℝ, azumaProxy2_Tfun n (azumaProxy_xmu 3 (sz0.L n) (sz0.W n) μ) = c := fun μ =>
    azumaProxy2_eq_of_ae_eq_of_ball_pos (azumaProxy2_Tfun_continuousAt n μ) h2
      (fun ε hε => azumaProxy2_PF_ball_pos (sz0.lam n) μ hε)
  set D : ℂ := fderiv ℝ (azumaProxy2_Φ0n n) 0 1 with hD
  have hΔ : 0 < Real.sqrt (gridStep sInst vg Kg n) := Real.sqrt_pos.2 (azumaProxy2_gridStep_pos n)
  -- `f (y) = f 0 + y D` for every real `y`
  have hf0 : azumaProxy2_fscn n 0 = c := by
    have := hT 0
    rw [azumaProxy2_Tfun_xmu] at this
    simpa using this
  have hlin : ∀ y : ℝ, azumaProxy2_fscn n y = azumaProxy2_fscn n 0 + (y : ℂ) * D := by
    intro y
    have hT' := hT (y / Real.sqrt (gridStep sInst vg Kg n))
    have hy : Real.sqrt (gridStep sInst vg Kg n) * (y / Real.sqrt (gridStep sInst vg Kg n)) = y := by
      field_simp
    rw [azumaProxy2_Tfun_xmu, hy, ← hf0] at hT'
    have hy' : ((Real.sqrt (gridStep sInst vg Kg n) : ℝ) : ℂ) *
        ((y / Real.sqrt (gridStep sInst vg Kg n) : ℝ) : ℂ) = (y : ℂ) := by
      rw [← Complex.ofReal_mul, hy]
    rw [hy'] at hT'
    linear_combination hT'
  have hsum : ∀ y : ℝ, azumaProxy2_fscn n y + azumaProxy2_fscn n (-y) = 2 * azumaProxy2_fscn n 0 := by
    intro y
    have h1 := hlin y
    have h2 := hlin (-y)
    push_cast at h2
    linear_combination h1 + h2
  have hT1 : Tendsto (fun y : ℝ => azumaProxy2_fscn n (1 * y)) atTop (𝓝 0) :=
    azumaProxy2_fscn_tendsto n 1 (by norm_num)
  have hT2 : Tendsto (fun y : ℝ => azumaProxy2_fscn n ((-1) * y)) atTop (𝓝 0) :=
    azumaProxy2_fscn_tendsto n (-1) (by norm_num)
  have hT3 := hT1.add hT2
  have hconst : (fun y : ℝ => azumaProxy2_fscn n (1 * y) + azumaProxy2_fscn n ((-1) * y)) = fun _ => 2 * azumaProxy2_fscn n 0 := by
    funext y
    simp only [one_mul, neg_mul]
    exact hsum y
  rw [hconst, add_zero] at hT3
  have h4 : 2 * azumaProxy2_fscn n 0 = 0 := tendsto_nhds_unique tendsto_const_nhds hT3
  exact azumaProxy2_fscn_zero_ne n (by simpa using h4)

/-- **Instance of `yMomentsUnifN` with `YvecN` not a.e. zero**: at the data of section 8
(`k = 3`, `σ = (+,-,+)`), for the `n` given by the eventual filter and its constant `P`, the `Y` moment
inputs hold for `YvecN` with `Δ > 0`, and at this same `n` the remainder `YvecN` at the step `j = 0` and
the label `b = (0,0,0)` is not a.e. zero (`yvecN_not_ae_zero`), so the moment bounds are not satisfied
merely because `Y ≡ 0`.  (RBM2D `yMomentsN_instance_nonzero`, `AzumaProxyN:1969`, for `yMomentsUnifN`.) -/
theorem yMomentsUnifN_instance_nonzero :
    ∃ C_P : ℝ, 0 ≤ C_P ∧ ∃ n : ℕ, ∃ P : ℝ, 0 ≤ P ∧ P ≤ ((sz0.size n : ℕ) : ℝ) ^ C_P ∧
      0 < gridStep sInst vg Kg n ∧
      YMomentBoundsN sz0 (Einst n) sig3 (gridTime sInst vg Kg n) (fun _ => Kg n) (Kg n)
        (fun j ω => YvecN sz0 Einst sInst vg Kg n j sig3 ω)
        (fun _ => gridStep sInst vg Kg n ^ 2 * P) (fun _ => gridStep sInst vg Kg n ^ 4 * P ^ 2) ∧
      ¬ (∀ᵐ ω ∂(pathP sz0), YvecN sz0 Einst sInst vg Kg n 0 sig3 ω (b0n n) = 0) := by
  obtain ⟨C_P, hC, n, P, hP0, hPN, hΔ, hY⟩ := yMomentsUnifN_instance sig3
  exact ⟨C_P, hC, n, P, hP0, hPN, hΔ, hY, yvecN_not_ae_zero n⟩

end AzumaProxyN2Inst

end YNonzero

/-! ## 10. Statement checks -/

section StatementChecks

/-! The target statements against the pins (`GridAssemblyN.lean:173`; the check file
`docs/tickets/checks/T2160-check.lean`): these anonymous `example`s compile only if the theorems have
exactly the types `YMomentsN sz κ τ' E s t K` and `YMomentsUnifN sz κ τ' E s t`. -/

example {d : ℕ} (sz : Sizes d) (κ τ' : ℝ) (E s t : ℕ → ℝ) (K : ℕ → ℕ) :
    YMomentsN sz κ τ' E s t K := yMomentsN sz κ τ' E s t K

example {d : ℕ} (sz : Sizes d) (κ τ' : ℝ) (E s t : ℕ → ℝ) : YMomentsUnifN sz κ τ' E s t :=
  yMomentsUnifN sz κ τ' E s t

end StatementChecks

end RBM.Ind

#print axioms RBM.Ind.AzumaProxyN_integrable_normPow8_incr
#print axioms RBM.Ind.AzumaProxyN_integral_normPow8_incr_le
#print axioms RBM.Ind.yMomentsUnifN
#print axioms RBM.Ind.yMomentsN_of_unif
#print axioms RBM.Ind.yMomentsN
#print axioms RBM.Ind.AzumaProxyN_stopW
#print axioms RBM.Ind.AzumaProxyN_YfieldsW
#print axioms RBM.Ind.AzumaProxyN_c0_pos_pub
#print axioms RBM.Ind.AzumaProxyN_inv_one_sub_le_pub
#print axioms RBM.Ind.AzumaProxyN_etaT_inv_le_pub
#print axioms RBM.Ind.AzumaProxyN_P_le_pub
#print axioms RBM.Ind.AzumaProxyN_rowsum_Ugen_pub
#print axioms RBM.Ind.AzumaProxyN2Inst.normPow8_instance
#print axioms RBM.Ind.AzumaProxyN2Inst.yMomentsUnifN_instance
#print axioms RBM.Ind.AzumaProxyN2Inst.yMomentsN_of_unif_instance
#print axioms RBM.Ind.AzumaProxyN2Inst.yMomentsN_instance
#print axioms RBM.Ind.AzumaProxyN2Inst.yfieldsW_instance
#print axioms RBM.Ind.AzumaProxyN2Inst.yvecN_not_ae_zero
#print axioms RBM.Ind.AzumaProxyN2Inst.yMomentsUnifN_instance_nonzero

end
