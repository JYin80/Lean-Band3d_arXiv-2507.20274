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

/-- Public re-export of the private `azumaProxy2_inv_one_sub_le` (RBM2D
`AzumaProxyN_inv_one_sub_le_pub`, `AzumaProxyN:2431`). -/
theorem AzumaProxyN_inv_one_sub_le_pub {u t τ' N : ℝ} (hut : u ≤ t) (hN0 : 0 < N)
    (hR : N ^ (-1 + τ') ≤ 1 - t) : (1 - u)⁻¹ ≤ N ^ (1 - τ') :=
  azumaProxy2_inv_one_sub_le hut hN0 hR

/-- Public re-export of the private `azumaProxy2_P_le` (`P ≤ N^{C_P}`, `C_P = 11 + (4k+4)θ`; RBM2D
`AzumaProxyN_P_le_pub`, `AzumaProxyN:2442`). -/
theorem AzumaProxyN_P_le_pub (k : ℕ) {c0 θ N : ℝ} (hc0 : 0 < c0) (hθ : 0 ≤ θ) (hN1 : 1 ≤ N)
    (hbig : 2000 * (2 ^ k * ((k * (k + 1) : ℕ) : ℝ) * (c0⁻¹) ^ (k + 2)) ^ 2 ≤ N) :
    2000 * ((2 * N ^ θ) ^ k * (((k * (k + 1) : ℕ) : ℝ) * N * (N ^ θ / c0) ^ (k + 2))) ^ 2 * N ^ 8
      ≤ N ^ (11 + (4 * k + 4) * θ) :=
  azumaProxy2_P_le k hc0 hθ hN1 hbig

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

/-! ## 10. Statement checks -/

/-! The target statements against the pins (`GridAssemblyN.lean:173`; the check file
`docs/tickets/checks/T2160-check.lean`): these anonymous `example`s compile only if the theorems have
exactly the types `YMomentsN sz κ τ' E s t K` and `YMomentsUnifN sz κ τ' E s t`. -/

end RBM.Ind

end
