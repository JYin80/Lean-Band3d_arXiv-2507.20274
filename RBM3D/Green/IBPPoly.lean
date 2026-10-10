/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Green.LDEQuadT
import RBM3D.Green.LDE
import RBM3D.Green.RowIndep
import RBM3D.Green.EntryDom

/-!
# Gaussian integration by parts with polynomial moments, and the instantiated quadratic LDE

Port of `RBM2D/Green/IBPPoly.lean` (392 lines) and `RBM2D/Green/LDEQuadInst.lean` (701 lines) of
RBM2D at commit `c9a24cf` (T2088, portmap P.7 row S1-19) to the `d`-dimensional sequence model of
`RBM3D/Gauss/FineModel.lean`.  The paper (arXiv:2507.20274) does not state either file as a lemma:
the first is abstract Gaussian calculus on independent centred coordinates; the second proves, for
the Gaussian flow, the quadratic large deviation input `hLquad` of `diag_bound_stochDom`
(`Green/EntryDom.lean`), which the paper takes from [YY_25] (Lemma 4.2 there).

## Main statements

* `RBM.Green.gaussIBP` : `GaussIBP sz` for every `sz : Sizes d` (the registry line of
  `RBM.Green.GaussIBP` in `RBM3D/Test/Axioms.lean` is then superfluous; the cleanup ticket
  removes it), with `RBM.Green.integrable_polyW_pow` (`polyInt`) and the complex Stein identity
  `RBM.Green.integral_mul_gaussianReal_complex_int` (no restriction on the variance, so the
  zero-variance coordinates of `svarF` are covered).
* `RBM.Green.minorRes`, `modelChaos`, `modelChaosEps`, `hwConst`, `mom_modelChaosEps_le`,
  `meas_lt_normSq_chaos_le`: the row chaos of the model at row `i`, its `ε`-normalised version and
  the tail bound with the random control.
* `RBM.Green.stochDom_ldeQuad` : `sz.PrecPT (ldeQuadLHS …) (ldeQuadRHS …)`, the literal text of the
  hypothesis `hLquad` of `diag_bound_stochDom`, for every size sequence with `sz.SizeTendsto`.

* T2389 (BA-G2): the minor resolvent, the chaos instance and the tail bounds carry a deterministic Hermitian shift
  `D` (`minorRes sz n D u z i ω` is the resolvent of the minor of `D + X`); `IBPPoly_stochDom_ldeQuad_shift` is the
  quadratic input for `D + X`, and `stochDom_ldeQuad` is its corollary at `D = 0`.

## Differences from RBM2D (residual, after the renaming of `docs/tickets/ST1-COMMON.md`)

* `d : Sizes` becomes `sz : Sizes d`; `Idx L W` becomes `Idx d L W`; `PerTimeDomAt (seqP d) d.size`
  becomes `sz.PrecPT`; `Ind.SizeTendsto d` becomes `sz.SizeTendsto`; `spectralZ` becomes `zt`;
  `BlockIndex L W` becomes `Vtx d L W`; `Sblk2 L W` becomes `svar d L W (sz.lam n)` (the
  `d`-dimensional variance profile `W^{-d} SBR`, D129-D130); the fine-lattice profile of the chaos
  is `svarF d L W (sz.lam n)`; RBM2D's `update`, `update_self`, `update_of_ne`, `measurable_update`
  are `upd`, `upd_self`, `upd_of_ne`, `measurable_upd` of `Gauss/SteinMatrix.lean`.
* `norm_green_le` of RBM2D is re-derived from `norm_Gsig_le_inv_eta` and
  `norm_matrix_entry_le_opNorm` (private `LDEQuadInst_norm_green_apply_le`).
* No exponent of `d`, `W`, `L` occurs in either file; `d` enters only through `N = (W L)^d → ∞`
  (`SizeTendsto`), and `hwConst q = ((2q+1)(4q+2))^{q+1}` does not depend on it.
* Instances: `RBM.Green.IBPInst`, at the end of the file (`sz0`, `d = 3`).
-/

namespace RBM.Green

open MeasureTheory ProbabilityTheory Filter Finset RBM.Gauss

open scoped NNReal

variable {d : ℕ} {sz : Sizes d}

/-! ### Two Gaussian-moment helpers (private copies of RBM1D `Gauss/Moments.lean`; the same two helpers are
also private in `Green/RowIndep.lean` and `Green/LDE.lean`) -/

section Moments

open scoped ENNReal

/-- Every polynomial is integrable against a real Gaussian. -/
private theorem integrable_pow_gaussianReal (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 v) := by
  have hmem : MemLp (id : ℝ → ℝ) (k : ℝ≥0∞) (gaussianReal 0 v) :=
    memLp_id_gaussianReal' _ (by simp)
  have h := hmem.integrable_norm_pow' (p := k)
  refine h.mono (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  simp

/-- Transfer integrability from the Gaussian measure to the density form used by
`RBM.integral_mul_gaussianReal`. -/
private theorem integrable_mul_gaussianPDFReal {v : ℝ≥0} (hv : v ≠ 0) {g : ℝ → ℝ}
    (hg : Integrable g (gaussianReal 0 v)) :
    Integrable fun x : ℝ => g x * gaussianPDFReal 0 v x := by
  rw [gaussianReal_of_var_ne_zero _ hv,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
      (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)] at hg
  simpa [gaussianPDF_def, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 v _),
    mul_comm] using hg

end Moments

/-! ### Resampling one coordinate (RBM1D `P_map_update`, here `GaussianProduct.map_update`) -/

/-- Replacing the `c`-th coordinate of `Sizes.seqP sz` by an independent copy of its own law
leaves `Sizes.seqP sz` unchanged.  `Sizes.seqP sz` is by definition
`GaussianProduct.law (Sizes.seqGvar sz)`. -/
private theorem P_map_update (sz : Sizes d) (c : Sizes.SeqCoord sz) :
    ((Sizes.seqP sz).prod (gaussianReal 0 (Sizes.seqGvar sz c))).map
      (upd c) = Sizes.seqP sz :=
  GaussianProduct.map_update (Sizes.seqGvar sz) c

/-! ### An elementary inequality -/

/-- `(a+b)^n ≤ 2^n (a^n + b^n)` for `a, b ≥ 0`. -/
theorem add_pow_le_two_pow_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    (a + b) ^ n ≤ 2 ^ n * (a ^ n + b ^ n) := by
  have h0 : 0 ≤ max a b := le_max_of_le_left ha
  have hmax : a + b ≤ 2 * max a b := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  calc (a + b) ^ n ≤ (2 * max a b) ^ n := pow_le_pow_left₀ (by linarith) hmax n
    _ = 2 ^ n * max a b ^ n := by rw [mul_pow]
    _ ≤ 2 ^ n * (a ^ n + b ^ n) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rcases le_total a b with h | h
        · rw [max_eq_right h]
          have : (0 : ℝ) ≤ a ^ n := pow_nonneg ha n
          linarith
        · rw [max_eq_left h]
          have : (0 : ℝ) ≤ b ^ n := pow_nonneg hb n
          linarith

/-! ### All polynomial moments are finite -/

/-- `|ω_c|^n` is integrable. -/
theorem integrable_abs_pow_coord (sz : Sizes d) (c : Sizes.SeqCoord sz) (n : ℕ) :
    Integrable (fun ω : Sizes.SeqΩ sz => |ω c| ^ n) (Sizes.seqP sz) := by
  have h := (integrable_pow_coord sz c n).abs
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  change |ω c ^ n| = |ω c| ^ n
  rw [abs_pow]

theorem continuous_polyW (I : Finset (Sizes.SeqCoord sz)) :
    Continuous fun ω : Sizes.SeqΩ sz => polyW I ω := by
  refine continuous_const.add ?_
  exact continuous_finsetSum _ fun c _ => (continuous_apply c).abs

/-- **`polyInt`**: every polynomial moment of `Sizes.seqP sz` is finite.  Induction on the finite
set of coordinates, using `(a+b)^n ≤ 2^n(a^n+b^n)` and the one-coordinate moments. -/
theorem integrable_polyW_pow (sz : Sizes d) (I : Finset (Sizes.SeqCoord sz)) (n : ℕ) :
    Integrable (fun ω : Sizes.SeqΩ sz => polyW I ω ^ n) (Sizes.seqP sz) := by
  classical
  induction I using Finset.induction generalizing n with
  | empty =>
      have h : ∀ ω : Sizes.SeqΩ sz, polyW (∅ : Finset (Sizes.SeqCoord sz)) ω ^ n = 1 := by
        intro ω; simp [polyW]
      simp only [h]
      exact integrable_const 1
  | insert c I hc ih =>
      have hsplit : ∀ ω : Sizes.SeqΩ sz, polyW (insert c I) ω = polyW I ω + |ω c| := by
        intro ω
        change 1 + ∑ x ∈ insert c I, |ω x| = (1 + ∑ x ∈ I, |ω x|) + |ω c|
        rw [Finset.sum_insert hc]
        ring
      have hmaj : Integrable
          (fun ω : Sizes.SeqΩ sz => 2 ^ n * (polyW I ω ^ n + |ω c| ^ n)) (Sizes.seqP sz) :=
        ((ih n).add (integrable_abs_pow_coord sz c n)).const_mul _
      refine Integrable.mono' hmaj
        (((continuous_polyW (insert c I)).pow n).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun ω => ?_)
      have hp : (0 : ℝ) ≤ polyW I ω := (polyW_nonneg I ω)
      have hq : (0 : ℝ) ≤ |ω c| := abs_nonneg _
      have hb := add_pow_le_two_pow_mul hp hq n
      rw [Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (polyW_nonneg (insert c I) ω) n), hsplit ω]
      exact hb

/-! ### One-dimensional Stein, with integrability instead of boundedness

`RBM.integral_mul_gaussianReal` already takes integrability hypotheses, but stated against the
density.  These are the same statements with the hypotheses against the measure, which is the
form the fibrewise argument produces. -/

/-- The real one-dimensional Stein identity, hypotheses stated against the Gaussian measure. -/
theorem integral_mul_gaussianReal_int {var : ℝ≥0} (hv : var ≠ 0) {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hfi : Integrable f (gaussianReal 0 var))
    (hxfi : Integrable (fun x : ℝ => x * f x) (gaussianReal 0 var))
    (hf'i : Integrable f' (gaussianReal 0 var)) :
    ∫ x : ℝ, x * f x ∂(gaussianReal 0 var)
      = (var : ℝ) * ∫ x : ℝ, f' x ∂(gaussianReal 0 var) := by
  refine integral_mul_gaussianReal hv hf ?_ (integrable_mul_gaussianPDFReal hv hf'i)
    (integrable_mul_gaussianPDFReal hv hfi)
  have hv' : (var : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have h := integrable_mul_gaussianPDFReal hv (hxfi.const_mul (-(1 / (var : ℝ))))
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  change -(1 / (var : ℝ)) * (x * f x) * gaussianPDFReal 0 var x
    = f x * (-(x / (var : ℝ)) * gaussianPDFReal 0 var x)
  field_simp

/-- The complex one-dimensional Stein identity, hypotheses stated against the Gaussian measure
and with no restriction on the variance. -/
theorem integral_mul_gaussianReal_complex_int {var : ℝ≥0} {f f' : ℝ → ℂ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hfi : Integrable f (gaussianReal 0 var))
    (hxfi : Integrable (fun x : ℝ => (x : ℂ) * f x) (gaussianReal 0 var))
    (hf'i : Integrable f' (gaussianReal 0 var)) :
    ∫ x : ℝ, (x : ℂ) * f x ∂(gaussianReal 0 var)
      = ((var : ℝ) : ℂ) * ∫ x : ℝ, f' x ∂(gaussianReal 0 var) := by
  by_cases hv : var = 0
  · subst hv
    simp [gaussianReal_zero_var]
  -- real and imaginary parts
  have hre : ∀ x, HasDerivAt (fun y : ℝ => (f y).re) ((f' x).re) x := by
    intro x
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hf x)
    simpa only [Function.comp_def, Complex.reCLM_apply] using h
  have him : ∀ x, HasDerivAt (fun y : ℝ => (f y).im) ((f' x).im) x := by
    intro x
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hf x)
    simpa only [Function.comp_def, Complex.imCLM_apply] using h
  have hxre : Integrable (fun x : ℝ => x * (f x).re) (gaussianReal 0 var) := by
    refine hxfi.re.congr (Filter.Eventually.of_forall fun x => ?_)
    change ((x : ℂ) * f x).re = x * (f x).re
    simp [Complex.mul_re]
  have hxim : Integrable (fun x : ℝ => x * (f x).im) (gaussianReal 0 var) := by
    refine hxfi.im.congr (Filter.Eventually.of_forall fun x => ?_)
    change ((x : ℂ) * f x).im = x * (f x).im
    simp [Complex.mul_im]
  have hR := integral_mul_gaussianReal_int hv hre hfi.re hxre hf'i.re
  have hI := integral_mul_gaussianReal_int hv him hfi.im hxim hf'i.im
  -- assemble
  have hIl : Integrable (fun x : ℝ => (x : ℂ) * f x) (gaussianReal 0 var) := hxfi
  have hlre : (∫ x : ℝ, (x : ℂ) * f x ∂(gaussianReal 0 var)).re
      = ∫ x : ℝ, x * (f x).re ∂(gaussianReal 0 var) := by
    have h := (Complex.reCLM.integral_comp_comm hIl).symm
    simp only [Complex.reCLM_apply] at h
    rw [h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [Complex.mul_re])
  have hlim : (∫ x : ℝ, (x : ℂ) * f x ∂(gaussianReal 0 var)).im
      = ∫ x : ℝ, x * (f x).im ∂(gaussianReal 0 var) := by
    have h := (Complex.imCLM.integral_comp_comm hIl).symm
    simp only [Complex.imCLM_apply] at h
    rw [h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [Complex.mul_im])
  have hrre : (∫ x : ℝ, f' x ∂(gaussianReal 0 var)).re
      = ∫ x : ℝ, (f' x).re ∂(gaussianReal 0 var) := by
    have h := (Complex.reCLM.integral_comp_comm hf'i).symm
    simpa only [Complex.reCLM_apply] using h
  have hrim : (∫ x : ℝ, f' x ∂(gaussianReal 0 var)).im
      = ∫ x : ℝ, (f' x).im ∂(gaussianReal 0 var) := by
    have h := (Complex.imCLM.integral_comp_comm hf'i).symm
    simpa only [Complex.imCLM_apply] using h
  refine Complex.ext ?_ ?_
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      hlre, hrre]
    exact hR
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      hlim, hrim]
    exact hI

/-! ### The fibrewise argument -/

/-- `|x|^k` is integrable for a centred Gaussian. -/
theorem integrable_abs_pow_gaussianReal (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => |x| ^ k) (gaussianReal 0 v) := by
  have h := (integrable_pow_gaussianReal v k).abs
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  change |x ^ k| = |x| ^ k
  rw [abs_pow]

/-- Updating one coordinate increases the polynomial weight by at most `|t|`. -/
theorem polyW_upd_le (sz : Sizes d) (c : Sizes.SeqCoord sz) (I : Finset (Sizes.SeqCoord sz))
    (p : Sizes.SeqΩ sz × ℝ) :
    polyW I (upd c p) ≤ polyW I p.1 + |p.2| := by
  classical
  have hterm : ∀ x ∈ I, |(upd c p) x|
      ≤ |p.1 x| + (if x = c then |p.2| else 0) := by
    intro x _
    by_cases hx : x = c
    · subst hx
      rw [upd_self]
      simp
    · rw [upd_of_ne c p hx, ite_eq_right hx]
      simp
  have hsum : ∑ x ∈ I, |(upd c p) x|
      ≤ ∑ x ∈ I, (|p.1 x| + (if x = c then |p.2| else 0)) :=
    Finset.sum_le_sum hterm
  have hsplit : ∑ x ∈ I, (|p.1 x| + (if x = c then |p.2| else 0))
      = (∑ x ∈ I, |p.1 x|) + ∑ x ∈ I, (if x = c then |p.2| else 0) :=
    Finset.sum_add_distrib
  have hlast : (∑ x ∈ I, (if x = c then |p.2| else 0)) ≤ |p.2| := by
    by_cases hc : c ∈ I
    · rw [Finset.sum_ite_eq' I c fun _ => |p.2|, ite_eq_left hc]
    · rw [Finset.sum_ite_eq' I c fun _ => |p.2|, ite_eq_right hc]
      exact abs_nonneg _
  change 1 + ∑ x ∈ I, |(upd c p) x| ≤ (1 + ∑ x ∈ I, |p.1 x|) + |p.2|
  rw [hsplit] at hsum
  linarith

/-- The majorant used for the product integrability. -/
theorem norm_le_of_tame_upd (sz : Sizes d) (c : Sizes.SeqCoord sz) {f : Sizes.SeqΩ sz → ℂ}
    {I : Finset (Sizes.SeqCoord sz)}
    {n : ℕ} {C : ℝ} (hb : ∀ ω, ‖f ω‖ ≤ C * polyW I ω ^ n) (hC : 0 ≤ C) (p : Sizes.SeqΩ sz × ℝ) :
    ‖f (upd c p)‖ ≤ C * 2 ^ n * (polyW I p.1 ^ n + |p.2| ^ n) := by
  refine (hb _).trans ?_
  have h1 : polyW I (upd c p) ^ n ≤ (polyW I p.1 + |p.2|) ^ n :=
    pow_le_pow_left₀ (polyW_nonneg _ _) (polyW_upd_le sz c I p) n
  have h2 : (polyW I p.1 + |p.2|) ^ n ≤ 2 ^ n * (polyW I p.1 ^ n + |p.2| ^ n) :=
    add_pow_le_two_pow_mul (polyW_nonneg _ _) (abs_nonneg _) n
  calc C * polyW I (upd c p) ^ n ≤ C * ((polyW I p.1 + |p.2|) ^ n) :=
        mul_le_mul_of_nonneg_left h1 hC
    _ ≤ C * (2 ^ n * (polyW I p.1 ^ n + |p.2| ^ n)) := mul_le_mul_of_nonneg_left h2 hC
    _ = C * 2 ^ n * (polyW I p.1 ^ n + |p.2| ^ n) := by ring

/-- **`GaussIBP`, discharged.**  The same fibrewise argument as
`RBM.Gauss.GaussianProduct.stein`, with
"globally bounded" replaced by "polynomially bounded"; no smooth cutoff is needed, because the
one-dimensional identity only ever wanted integrability. -/
theorem gaussIBP (sz : Sizes d) : GaussIBP sz := by
  refine ⟨fun c g g' hg hg' hderiv => ?_, integrable_polyW_pow sz⟩
  classical
  obtain ⟨Ig, ng, Cg, hgb0⟩ := hg.poly
  obtain ⟨Ig', ng', Cg', hg'b0⟩ := hg'.poly
  -- the constants may be taken nonnegative
  have hCg : (0 : ℝ) ≤ max Cg 0 := le_max_right _ _
  have hCg' : (0 : ℝ) ≤ max Cg' 0 := le_max_right _ _
  have hgb : ∀ ω, ‖g ω‖ ≤ max Cg 0 * polyW Ig ω ^ ng := fun ω =>
    (hgb0 ω).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (pow_nonneg (polyW_nonneg _ _) _))
  have hg'b : ∀ ω, ‖g' ω‖ ≤ max Cg' 0 * polyW Ig' ω ^ ng' := fun ω =>
    (hg'b0 ω).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (pow_nonneg (polyW_nonneg _ _) _))
  have hUm : Measurable (upd c) :=
    measurable_upd c
  have hgm : Measurable g := hg.cont.measurable
  have hg'm : Measurable g' := hg'.cont.measurable
  have hfib : ∀ (ω : Sizes.SeqΩ sz) (t : ℝ),
      HasDerivAt (fun s : ℝ => g (Function.update ω c s)) (g' (Function.update ω c t)) t := by
    intro ω t
    simpa only [Function.update_idem, Function.update_self] using
      hderiv (Function.update ω c t)
  -- the three integrability facts on the product
  have hprodg : Integrable (fun p : Sizes.SeqΩ sz × ℝ => g (upd c p))
      ((Sizes.seqP sz).prod (gaussianReal 0 (Sizes.seqGvar sz c))) := by
    refine Integrable.mono'
      ((((integrable_polyW_pow sz Ig ng).comp_fst _).add
        ((integrable_abs_pow_gaussianReal (Sizes.seqGvar sz c) ng).comp_snd _)).const_mul
          (max Cg 0 * 2 ^ ng))
      ((hgm.comp hUm).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => ?_)
    simpa using norm_le_of_tame_upd sz c hgb hCg p
  have hprodg' : Integrable (fun p : Sizes.SeqΩ sz × ℝ => g' (upd c p))
      ((Sizes.seqP sz).prod (gaussianReal 0 (Sizes.seqGvar sz c))) := by
    refine Integrable.mono'
      ((((integrable_polyW_pow sz Ig' ng').comp_fst _).add
        ((integrable_abs_pow_gaussianReal (Sizes.seqGvar sz c) ng').comp_snd _)).const_mul
          (max Cg' 0 * 2 ^ ng'))
      ((hg'm.comp hUm).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => ?_)
    simpa using norm_le_of_tame_upd sz c hg'b hCg' p
  have hprodx : Integrable
      (fun p : Sizes.SeqΩ sz × ℝ => (p.2 : ℂ) * g (upd c p))
      ((Sizes.seqP sz).prod (gaussianReal 0 (Sizes.seqGvar sz c))) := by
    have hmaj : Integrable
        (fun p : Sizes.SeqΩ sz × ℝ => max Cg 0 * 2 ^ ng *
          (polyW Ig p.1 ^ ng * |p.2| + 1 * |p.2| ^ (ng + 1)))
        ((Sizes.seqP sz).prod (gaussianReal 0 (Sizes.seqGvar sz c))) := by
      refine Integrable.const_mul ?_ _
      refine Integrable.add ?_ ?_
      · exact (integrable_polyW_pow sz Ig ng).mul_prod
          (by simpa using integrable_abs_pow_gaussianReal (Sizes.seqGvar sz c) 1)
      · exact (integrable_const (1 : ℝ)).mul_prod
          (integrable_abs_pow_gaussianReal (Sizes.seqGvar sz c) (ng + 1))
    refine Integrable.mono' hmaj
      (((Complex.continuous_ofReal.measurable.comp measurable_snd).mul
        (hgm.comp hUm)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => ?_)
    have hb := norm_le_of_tame_upd sz c hgb hCg p
    have habs : (0 : ℝ) ≤ |p.2| := abs_nonneg _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |p.2| * ‖g (upd c p)‖
        ≤ |p.2| * (max Cg 0 * 2 ^ ng * (polyW Ig p.1 ^ ng + |p.2| ^ ng)) :=
          mul_le_mul_of_nonneg_left hb habs
      _ = max Cg 0 * 2 ^ ng * (polyW Ig p.1 ^ ng * |p.2| + 1 * |p.2| ^ (ng + 1)) := by
          rw [pow_succ]; ring
  -- both sides through the resampling map
  have hL : ∫ ω, (ω c : ℂ) * g ω ∂(Sizes.seqP sz)
      = ∫ p : Sizes.SeqΩ sz × ℝ, (p.2 : ℂ) * g (upd c p)
          ∂((Sizes.seqP sz).prod (gaussianReal 0 (Sizes.seqGvar sz c))) := by
    conv_lhs => rw [← P_map_update sz c]
    rw [integral_map hUm.aemeasurable (by
      rw [P_map_update sz c]
      exact ((Complex.continuous_ofReal.measurable.comp
        (measurable_pi_apply c)).mul hgm).aestronglyMeasurable)]
    simp only [upd_self]
  have hR : ∫ ω, g' ω ∂(Sizes.seqP sz)
      = ∫ p : Sizes.SeqΩ sz × ℝ, g' (upd c p)
          ∂((Sizes.seqP sz).prod (gaussianReal 0 (Sizes.seqGvar sz c))) := by
    conv_lhs => rw [← P_map_update sz c]
    rw [integral_map hUm.aemeasurable (by
      rw [P_map_update sz c]
      exact hg'm.aestronglyMeasurable)]
  rw [hL, hR, integral_prod _ hprodx, integral_prod _ hprodg', ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hprodx.prod_right_ae, hprodg.prod_right_ae, hprodg'.prod_right_ae]
    with ω h1 h2 h3
  exact integral_mul_gaussianReal_complex_int (hfib ω) h2 h1 h3



/-! ## The row chaos of the Gaussian model, and the input `hLquad` -/
/-! ### An entry is bounded by the operator norm -/

section OpNorm

open scoped Matrix.Norms.L2Operator

variable {ν : Type*} [Fintype ν] [DecidableEq ν]

/-- The merged `Gres H z true` (a `Ring.inverse`) is `RBM.green H z = (H - z)⁻¹`. -/
private theorem LDEQuadInst_Gres_true (H : Matrix ν ν ℂ) (z : ℂ) : Gres H z true = green H z := by
  simp only [green, Gres, ↓reduceIte, Matrix.nonsing_inv_eq_ringInverse]

/-- An entry of the resolvent of a Hermitian matrix is at most `|Im z|⁻¹`
(RBM2D `norm_green_le` through `norm_Gsig_le_inv_eta` and `norm_matrix_entry_le_opNorm`). -/
private theorem LDEQuadInst_norm_green_apply_le {H : Matrix ν ν ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) (p q : ν) : ‖green H z p q‖ ≤ |z.im|⁻¹ := by
  have h := norm_Gsig_le_inv_eta hH (abs_pos.2 hz) le_rfl true
  rw [LDEQuadInst_Gres_true] at h
  exact (norm_matrix_entry_le_opNorm _ p q).trans h

end OpNorm

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {u : ℝ} {z : ℂ}

-- The deterministic Hermitian shift `D` of the flow `D + X` (`D = 0` is the band; `D = g₀ Ψ` is the block Anderson
-- model): an implicit argument of every statement about the minors of `D + X` below.
variable {D : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

private theorem LDEQuadInst_seqHflow_zero (sz : Sizes d) (n : ℕ) (ω : Sizes.SeqΩ sz) :
    Sizes.seqHflow sz n 0 ω = 0 := by
  rw [Sizes.seqHflow_eq_smul]
  simp

/-- The size-`n` flow is continuous on the common sample space. -/
private theorem LDEQuadInst_continuous_seqHflow (sz : Sizes d) (n : ℕ) (u : ℝ) :
    Continuous fun ω : Sizes.SeqΩ sz => Sizes.seqHflow sz n u ω :=
  (continuous_Hflow d (sz.L n) (sz.W n) u).comp
    (continuous_pi fun c => continuous_apply (⟨n, c⟩ : Sizes.SeqCoord sz))

/-! ### The minor resolvent as the matrix of the chaos -/

/-- `((D + H)^{(i)} - z)^{-1}`, the resolvent of the minor of `D + H`. -/
noncomputable def minorRes (sz : Sizes d) (n : ℕ)
    (D : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (u : ℝ) (z : ℂ)
    (i : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    Matrix {a : Idx d (sz.L n) (sz.W n) // a ≠ i} {a : Idx d (sz.L n) (sz.W n) // a ≠ i} ℂ :=
  green ((D + Sizes.seqHflow sz n u ω).submatrix
    (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → Idx d (sz.L n) (sz.W n))
    (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → Idx d (sz.L n) (sz.W n))) z

theorem isHermitian_Hflow_submatrix (sz : Sizes d) (n : ℕ)
    (D : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hD : D.IsHermitian) (u : ℝ) (ω : Sizes.SeqΩ sz)
    (i : Idx d (sz.L n) (sz.W n)) :
    ((D + Sizes.seqHflow sz n u ω).submatrix
      (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → Idx d (sz.L n) (sz.W n))
      (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → Idx d (sz.L n) (sz.W n))).IsHermitian :=
  (hD.add (Sizes.seqHflow_isHermitian sz n u ω)).submatrix _

/-- **The minor resolvent is bounded by `|Im z|⁻¹`, for every `ω`.** -/
theorem norm_minorRes_le (hD : D.IsHermitian) (hz : z.im ≠ 0) (i : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz)
    (k l : {a : Idx d (sz.L n) (sz.W n) // a ≠ i}) : ‖minorRes sz n D u z i ω k l‖ ≤ |z.im|⁻¹ := by
  exact LDEQuadInst_norm_green_apply_le (isHermitian_Hflow_submatrix sz n D hD u ω i) hz k l

theorem continuous_minorRes (hD : D.IsHermitian) (hz : z.im ≠ 0) (i : Idx d (sz.L n) (sz.W n))
    (k l : {a : Idx d (sz.L n) (sz.W n) // a ≠ i}) :
    Continuous fun ω : Sizes.SeqΩ sz => minorRes sz n D u z i ω k l := by
  refine Continuous.matrix_elem ?_ k l
  have h := continuous_green_of_isHermitian
    ((show Continuous fun ω : Sizes.SeqΩ sz => D + Sizes.seqHflow sz n u ω from
      continuous_const.add (LDEQuadInst_continuous_seqHflow sz n u)).matrix_submatrix
      (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → _)
      (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → _))
    (fun ω => isHermitian_Hflow_submatrix sz n D hD u ω i) hz
  unfold minorRes
  simpa only [LDEQuadInst_Gres_true] using h

/-- The minor resolvent reads only the off-row block. -/
theorem minorRes_congr (i : Idx d (sz.L n) (sz.W n)) {ω ω' : Sizes.SeqΩ sz}
    (h : ∀ c ∈ offRowCoord sz n i, ω c = ω' c) :
    minorRes sz n D u z i ω = minorRes sz n D u z i ω' := by
  unfold minorRes
  rw [RowIndep_submatrix_shift_congr D u h]

/-! ### The instance -/

/-- **The row chaos of the Gaussian model at row `i`.**  The row is `h_k = (H_u)_{ik}`, the
matrix is the minor resolvent `((D + H)^{(i)} - z)^{-1}`, and the scale is `r = √u`. -/
noncomputable def modelChaos (sz : Sizes d) (n : ℕ) (D : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hD : D.IsHermitian) (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (i : Idx d (sz.L n) (sz.W n)) : RowChaos sz {a : Idx d (sz.L n) (sz.W n) // a ≠ i} where
  co k b := rowCoord sz n i k.1 b
  co_inj := by
    rintro ⟨⟨k, hk⟩, b⟩ ⟨⟨l, hl⟩, c⟩ h
    obtain ⟨h1, h2⟩ := rowCoord_injOn hk hl h
    subst h1; subst h2; rfl
  gvar_tag k := by rw [gvar_rowCoord k.2, gvar_rowCoord k.2]
  eps k := rowSign sz n i k.1
  eps_sq k := by unfold rowSign; split_ifs <;> norm_num
  r := Real.sqrt u
  B ω k l := minorRes sz n D u z i ω k l
  B_cont k l := continuous_minorRes hD hz i k l
  Bbd := |z.im|⁻¹
  B_bdd ω k l := norm_minorRes_le hD hz i ω k l
  Ifree := offRowCoord sz n i
  Ifree_free k b := by
    intro hmem
    exact (Finset.mem_sdiff.1 hmem).2 (rowCoord_mem_rowSet i k.1 b)
  B_free ω ω' h := by
    funext k l
    rw [minorRes_congr (D := D) (u := u) (z := z) i h]

/-! ### What the instance is -/

section Instance

variable (hD : D.IsHermitian) (hz : z.im ≠ 0) (i : Idx d (sz.L n) (sz.W n))

@[simp] theorem modelChaos_B (ω : Sizes.SeqΩ sz) (k l : {a : Idx d (sz.L n) (sz.W n) // a ≠ i}) :
    (modelChaos sz n D hD u hz i).B ω k l = minorRes sz n D u z i ω k l := rfl

/-- **The row of the chaos is the `i`-th row of `H_u`.** -/
theorem modelChaos_h (ω : Sizes.SeqΩ sz) (k : {a : Idx d (sz.L n) (sz.W n) // a ≠ i}) :
    (modelChaos sz n D hD u hz i).h ω k = Sizes.seqHflow sz n u ω i k.1 := by
  change (Real.sqrt u : ℂ) * ((ω (rowCoord sz n i k.1 true) : ℂ)
      + ((rowSign sz n i k.1 : ℂ) * Complex.I) * (ω (rowCoord sz n i k.1 false) : ℂ))
    = (Real.sqrt u : ℂ) * Xentry d (sz.L n) (sz.W n) (Sizes.slice sz n ω) i k.1
  rw [Xentry_eq_rowCoord (Ne.symm k.2) ω]

/-- **The variance of the row is `σ_k = u S_{ik}`** (`S = svarF`, the fine-lattice profile of `Defs`/`Gauss/FineModel`). -/
theorem modelChaos_sg (hu : 0 ≤ u) (k : {a : Idx d (sz.L n) (sz.W n) // a ≠ i}) :
    (modelChaos sz n D hD u hz i).sg k = u * svarF d (sz.L n) (sz.W n) (sz.lam n) i k.1 := by
  change 2 * Real.sqrt u ^ 2 * (Sizes.seqGvar sz (rowCoord sz n i k.1 true) : ℝ) = _
  rw [gvar_rowCoord k.2, Real.sq_sqrt hu]
  ring

/-- **The matrix of the chaos is `G^{(i)}`, for every `ω`.**  The two side conditions of
`RBM.Green.inv_minor_resolvent` hold unconditionally off the real axis. -/
theorem modelChaos_B_eq (ω : Sizes.SeqΩ sz) (k l : {a : Idx d (sz.L n) (sz.W n) // a ≠ i}) :
    (modelChaos sz n D hD u hz i).B ω k l
      = greenMinor (green (D + Sizes.seqHflow sz n u ω) z) i k.1 l.1 := by
  change minorRes sz n D u z i ω k l = _
  unfold minorRes
  have hH : (D + Sizes.seqHflow sz n u ω).IsHermitian := hD.add (Sizes.seqHflow_isHermitian sz n u ω)
  rw [show green ((D + Sizes.seqHflow sz n u ω).submatrix
      (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → Idx d (sz.L n) (sz.W n))
      (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → Idx d (sz.L n) (sz.W n))) z
      = ((D + Sizes.seqHflow sz n u ω).submatrix Subtype.val Subtype.val
        - z • (1 : Matrix {a : Idx d (sz.L n) (sz.W n) // a ≠ i} _ ℂ))⁻¹ from rfl,
    inv_minor_resolvent ((Matrix.isUnit_iff_isUnit_det _).1 (RBM.isUnit_sub_smul_of_isHermitian hH hz)) i
      (green_diag_ne_zero hH hz i)]
  rfl

/-! ### The two sides of (4.7), in the paper's notation -/

/-- **The chaos of the instance is `ldeQuadLHS`.** -/
theorem modelChaos_normSq_chaos (hu : 0 ≤ u) (ω : Sizes.SeqΩ sz) :
    ‖(modelChaos sz n D hD u hz i).chaos ω‖ ^ 2
      = ldeQuadLHS (Sizes.seqHflow sz n u ω) (green (D + Sizes.seqHflow sz n u ω) z)
          (svarF d (sz.L n) (sz.W n) (sz.lam n)) u i :=
  RowChaos.norm_chaos_sq_eq_ldeQuadLHS (modelChaos sz n D hD u hz i) ω
    (Sizes.seqHflow sz n u ω) (green (D + Sizes.seqHflow sz n u ω) z) (svarF d (sz.L n) (sz.W n) (sz.lam n)) u
    (fun k => modelChaos_h hD hz i ω k)
    (fun k => by
      rw [modelChaos_h hD hz i ω k]
      exact (Sizes.seqHflow_isHermitian sz n u ω).apply k.1 i)
    (fun k l => modelChaos_B_eq hD hz i ω k l)
    (fun k => modelChaos_sg hD hz i hu k)

/-- **The control of the instance is `u² · ldeQuadRHS`.**  The factor `u²` comes from
`E|H_{ik}|² = u S_{ik}` while `ldeQuadRHS` is written with `S`; the column form `hsg'` of
`RowChaos.Vq_eq_ldeQuadRHS` is `modelChaos_sg` with `svar_comm`. -/
theorem modelChaos_Vq (hu : 0 ≤ u) (ω : Sizes.SeqΩ sz) :
    (modelChaos sz n D hD u hz i).Vq ω
      = u ^ 2 * ldeQuadRHS (svarF d (sz.L n) (sz.W n) (sz.lam n)) (green (D + Sizes.seqHflow sz n u ω) z) i :=
  RowChaos.Vq_eq_ldeQuadRHS (modelChaos sz n D hD u hz i) ω
    (green (D + Sizes.seqHflow sz n u ω) z) (svarF d (sz.L n) (sz.W n) (sz.lam n)) u
    (fun k l => modelChaos_B_eq hD hz i ω k l)
    (fun k => modelChaos_sg hD hz i hu k)
    (fun k => by rw [modelChaos_sg hD hz i hu k, svarF_comm d (sz.L n) (sz.W n) (sz.lam n) i k.1])

end Instance

/-! ### The control of the model instance, as a function of `ω` -/

/-- `V_q` of the model instance, written out: `∑_{k,l} (uS_{ik})‖G^{(i)}_{kl}‖²(uS_{il})`. -/
noncomputable def vqM (sz : Sizes d) (n : ℕ)
    (D : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (u : ℝ) (z : ℂ)
    (i : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) : ℝ :=
  ∑ k : {a : Idx d (sz.L n) (sz.W n) // a ≠ i}, ∑ l : {a : Idx d (sz.L n) (sz.W n) // a ≠ i},
    (u * svarF d (sz.L n) (sz.W n) (sz.lam n) i k.1) * ‖minorRes sz n D u z i ω k l‖ ^ 2 *
      (u * svarF d (sz.L n) (sz.W n) (sz.lam n) i l.1)

theorem vqM_nonneg (hu : 0 ≤ u) (i : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    0 ≤ vqM sz n D u z i ω :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (mul_nonneg (mul_nonneg hu (svarF_nonneg d (sz.L n) (sz.W n) (sz.lam n) _ _)) (by positivity))
      (mul_nonneg hu (svarF_nonneg d (sz.L n) (sz.W n) (sz.lam n) _ _))

theorem continuous_vqM (hD : D.IsHermitian) (hz : z.im ≠ 0) (i : Idx d (sz.L n) (sz.W n)) :
    Continuous fun ω : Sizes.SeqΩ sz => vqM sz n D u z i ω := by
  refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ => ?_
  exact ((continuous_const.mul (((continuous_minorRes hD hz i k l).norm).pow 2)).mul
    continuous_const)

theorem vqM_congr (i : Idx d (sz.L n) (sz.W n)) {ω ω' : Sizes.SeqΩ sz}
    (h : ∀ c ∈ offRowCoord sz n i, ω c = ω' c) :
    vqM sz n D u z i ω = vqM sz n D u z i ω' := by
  unfold vqM
  rw [minorRes_congr (D := D) (u := u) (z := z) i h]

theorem vqM_eq (hD : D.IsHermitian) (hz : z.im ≠ 0) (hu : 0 ≤ u) (i : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    (modelChaos sz n D hD u hz i).Vq ω = vqM sz n D u z i ω := by
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [modelChaos_sg hD hz i hu k, modelChaos_sg hD hz i hu l]
  rfl

/-! ### The `ε`-normalised instance -/

/-- The normalising factor `(V_q + ε)^{1/2}`. -/
noncomputable def sqVq (sz : Sizes d) (n : ℕ)
    (D : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (u : ℝ) (z : ℂ)
    (i : Idx d (sz.L n) (sz.W n)) (ε : ℝ) (ω : Sizes.SeqΩ sz) : ℝ :=
  Real.sqrt (vqM sz n D u z i ω + ε)

theorem sqVq_pos (hu : 0 ≤ u) {ε : ℝ} (hε : 0 < ε) (i : Idx d (sz.L n) (sz.W n))
    (ω : Sizes.SeqΩ sz) : 0 < sqVq sz n D u z i ε ω :=
  Real.sqrt_pos.2 (by linarith [vqM_nonneg (D := D) (z := z) hu i ω])

theorem sq_sqVq (hu : 0 ≤ u) {ε : ℝ} (hε : 0 < ε) (i : Idx d (sz.L n) (sz.W n))
    (ω : Sizes.SeqΩ sz) : sqVq sz n D u z i ε ω ^ 2 = vqM sz n D u z i ω + ε :=
  Real.sq_sqrt (by linarith [vqM_nonneg (D := D) (z := z) hu i ω])

theorem sqVq_ge (hu : 0 ≤ u) {ε : ℝ} (_hε : 0 < ε) (i : Idx d (sz.L n) (sz.W n))
    (ω : Sizes.SeqΩ sz) : Real.sqrt ε ≤ sqVq sz n D u z i ε ω :=
  Real.sqrt_le_sqrt (by linarith [vqM_nonneg (D := D) (z := z) hu i ω])

/-- **The `ε`-normalised row chaos**: the same row, with the matrix divided by
`(V_q + ε)^{1/2}`.  The factor does not depend on `(k, l)`, so the chaos is divided by it too,
and it reads only the off-row block, so `B_free` survives. -/
noncomputable def modelChaosEps (sz : Sizes d) (n : ℕ)
    (D : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hD : D.IsHermitian) (u : ℝ) {z : ℂ}
    (hz : z.im ≠ 0)
    (hu : 0 ≤ u) (i : Idx d (sz.L n) (sz.W n)) (ε : ℝ) (hε : 0 < ε) :
    RowChaos sz {a : Idx d (sz.L n) (sz.W n) // a ≠ i} :=
  { modelChaos sz n D hD u hz i with
    B := fun ω k l => minorRes sz n D u z i ω k l / ((sqVq sz n D u z i ε ω : ℝ) : ℂ)
    B_cont := fun k l => by
      refine (continuous_minorRes hD hz i k l).div ?_ ?_
      · exact Complex.continuous_ofReal.comp
          ((continuous_vqM (D := D) (u := u) hD hz i).add continuous_const).sqrt
      · intro ω
        exact_mod_cast (sqVq_pos (D := D) (z := z) hu hε i ω).ne'
    Bbd := |z.im|⁻¹ / Real.sqrt ε
    B_bdd := fun ω k l => by
      have hpos := sqVq_pos (D := D) (z := z) hu hε i ω
      have hge := sqVq_ge (D := D) (z := z) hu hε i ω
      have hεp : (0 : ℝ) < Real.sqrt ε := Real.sqrt_pos.2 hε
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos.le]
      exact div_le_div₀ (by positivity) (norm_minorRes_le hD hz i ω k l) hεp hge
    B_free := fun ω ω' h => by
      have hs : sqVq sz n D u z i ε ω = sqVq sz n D u z i ε ω' := by
        unfold sqVq
        rw [vqM_congr (D := D) (u := u) (z := z) i h]
      funext k l
      rw [minorRes_congr (D := D) (u := u) (z := z) i h, hs] }

/-- **The normalised chaos is the chaos, divided by `(V_q+ε)^{1/2}`.** -/
theorem chaos_modelChaosEps (hD : D.IsHermitian) (hz : z.im ≠ 0) (hu : 0 ≤ u) (i : Idx d (sz.L n) (sz.W n)) {ε : ℝ}
    (hε : 0 < ε) (ω : Sizes.SeqΩ sz) :
    (modelChaosEps sz n D hD u hz hu i ε hε).chaos ω
      = (modelChaos sz n D hD u hz i).chaos ω / ((sqVq sz n D u z i ε ω : ℝ) : ℂ) := by
  unfold RowChaos.chaos RowChaos.cen
  rw [sub_div]
  congr 1
  · rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun l _ => ?_
    change (modelChaos sz n D hD u hz i).h ω k *
        (minorRes sz n D u z i ω k l / ((sqVq sz n D u z i ε ω : ℝ) : ℂ)) *
        (starRingEnd ℂ) ((modelChaos sz n D hD u hz i).h ω l)
      = (modelChaos sz n D hD u hz i).h ω k * minorRes sz n D u z i ω k l *
        (starRingEnd ℂ) ((modelChaos sz n D hD u hz i).h ω l) / ((sqVq sz n D u z i ε ω : ℝ) : ℂ)
    ring
  · rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    change (((modelChaos sz n D hD u hz i).sg k : ℝ) : ℂ) *
        (minorRes sz n D u z i ω k k / ((sqVq sz n D u z i ε ω : ℝ) : ℂ))
      = (((modelChaos sz n D hD u hz i).sg k : ℝ) : ℂ) * minorRes sz n D u z i ω k k /
        ((sqVq sz n D u z i ε ω : ℝ) : ℂ)
    ring

/-- **The normalised control is `V_q/(V_q+ε)`.** -/
theorem Vq_modelChaosEps (hD : D.IsHermitian) (hz : z.im ≠ 0) (hu : 0 ≤ u) (i : Idx d (sz.L n) (sz.W n)) {ε : ℝ}
    (hε : 0 < ε) (ω : Sizes.SeqΩ sz) :
    (modelChaosEps sz n D hD u hz hu i ε hε).Vq ω
      = vqM sz n D u z i ω / (vqM sz n D u z i ω + ε) := by
  have hpos := sqVq_pos (D := D) (z := z) hu hε i ω
  have hsq := sq_sqVq (D := D) (z := z) hu hε i ω
  have hpt : ∀ k l : {a : Idx d (sz.L n) (sz.W n) // a ≠ i},
      (modelChaosEps sz n D hD u hz hu i ε hε).sg k *
          ‖(modelChaosEps sz n D hD u hz hu i ε hε).B ω k l‖ ^ 2 *
          (modelChaosEps sz n D hD u hz hu i ε hε).sg l
        = ((modelChaos sz n D hD u hz i).sg k * ‖(modelChaos sz n D hD u hz i).B ω k l‖ ^ 2 *
            (modelChaos sz n D hD u hz i).sg l) / (vqM sz n D u z i ω + ε) := by
    intro k l
    change (modelChaos sz n D hD u hz i).sg k *
        ‖minorRes sz n D u z i ω k l / ((sqVq sz n D u z i ε ω : ℝ) : ℂ)‖ ^ 2 *
        (modelChaos sz n D hD u hz i).sg l = _
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos.le, div_pow, hsq]
    change _ = ((modelChaos sz n D hD u hz i).sg k * ‖minorRes sz n D u z i ω k l‖ ^ 2 *
      (modelChaos sz n D hD u hz i).sg l) / (vqM sz n D u z i ω + ε)
    ring
  have hd : ∀ (A : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → ℝ)
      (c : ℝ), (∑ k, ∑ l, A k l / c) = (∑ k, ∑ l, A k l) / c := by
    intro A c
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => (Finset.sum_div _ _ _).symm
  unfold RowChaos.Vq
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => hpt k l,
    hd (fun k l => (modelChaos sz n D hD u hz i).sg k * ‖(modelChaos sz n D hD u hz i).B ω k l‖ ^ 2 *
      (modelChaos sz n D hD u hz i).sg l) (vqM sz n D u z i ω + ε),
    show (∑ k, ∑ l, (modelChaos sz n D hD u hz i).sg k *
        ‖(modelChaos sz n D hD u hz i).B ω k l‖ ^ 2 * (modelChaos sz n D hD u hz i).sg l)
      = vqM sz n D u z i ω from vqM_eq hD hz hu i ω]

theorem Vq_modelChaosEps_le_one (hD : D.IsHermitian) (hz : z.im ≠ 0) (hu : 0 ≤ u) (i : Idx d (sz.L n) (sz.W n))
    {ε : ℝ} (hε : 0 < ε) (ω : Sizes.SeqΩ sz) : (modelChaosEps sz n D hD u hz hu i ε hε).Vq ω ≤ 1 := by
  rw [Vq_modelChaosEps hD hz hu i hε ω]
  have h0 := vqM_nonneg (D := D) (z := z) hu i ω
  rw [div_le_one (by linarith)]
  linarith

/-! ### The moment bound for the normalised chaos -/

/-- The constant of `RowChaos.mom_le_momVpow` at `p = q+1`. -/
noncomputable def hwConst (q : ℕ) : ℝ := ((2 * (q : ℝ) + 1) * (4 * (q : ℝ) + 2)) ^ (q + 1)

theorem hwConst_pos (q : ℕ) : 0 < hwConst q := by unfold hwConst; positivity

/-- **`E[(|Q|²/(V_q+ε))^{q+1}] ≤ A_{q+1}`, uniformly in `ε`.** -/
theorem mom_modelChaosEps_le (hD : D.IsHermitian) (hz : z.im ≠ 0) (hu : 0 ≤ u) (i : Idx d (sz.L n) (sz.W n))
    {ε : ℝ} (hε : 0 < ε) (q : ℕ) :
    (modelChaosEps sz n D hD u hz hu i ε hε).mom (q + 1) ≤ hwConst q := by
  have h := (modelChaosEps sz n D hD u hz hu i ε hε).mom_le_momVpow (gaussIBP sz) q
  have hV : (modelChaosEps sz n D hD u hz hu i ε hε).momVpow (q + 1) ≤ 1 := by
    change (∫ ω, (modelChaosEps sz n D hD u hz hu i ε hε).Vq ω ^ (q + 1) ∂(Sizes.seqP sz)) ≤ 1
    calc ∫ ω, (modelChaosEps sz n D hD u hz hu i ε hε).Vq ω ^ (q + 1) ∂(Sizes.seqP sz)
        ≤ ∫ _ω : Sizes.SeqΩ sz, (1 : ℝ) ∂(Sizes.seqP sz) :=
          MeasureTheory.integral_mono
            ((modelChaosEps sz n D hD u hz hu i ε hε).integrable_Vq_pow (gaussIBP sz) (q + 1))
            (MeasureTheory.integrable_const 1)
            (fun ω => pow_le_one₀ (RowChaos.Vq_nonneg ω)
              (Vq_modelChaosEps_le_one hD hz hu i hε ω))
      _ = 1 := by simp
  have hc : (0 : ℝ) ≤ hwConst q := (hwConst_pos q).le
  refine h.trans ?_
  calc hwConst q * (modelChaosEps sz n D hD u hz hu i ε hε).momVpow (q + 1)
      ≤ hwConst q * 1 := mul_le_mul_of_nonneg_left hV hc
    _ = hwConst q := mul_one _

/-! ### The tail bound, at fixed `ε` and then in the limit -/

theorem norm_chaos_modelChaosEps (hD : D.IsHermitian) (hz : z.im ≠ 0) (hu : 0 ≤ u) (i : Idx d (sz.L n) (sz.W n))
    {ε : ℝ} (hε : 0 < ε) (ω : Sizes.SeqΩ sz) :
    ‖(modelChaosEps sz n D hD u hz hu i ε hε).chaos ω‖
      = ‖(modelChaos sz n D hD u hz i).chaos ω‖ / sqVq sz n D u z i ε ω := by
  rw [chaos_modelChaosEps hD hz hu i hε ω, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sqVq_pos (D := D) (z := z) hu hε i ω).le]

/-- **Markov at fixed `ε`.** -/
theorem meas_lt_normSq_chaos_le_eps (hD : D.IsHermitian) (hz : z.im ≠ 0) (hu : 0 ≤ u)
    (i : Idx d (sz.L n) (sz.W n)) {lam : ℝ} (hlam : 0 < lam) (q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (Sizes.seqP sz)
        {ω | lam * (vqM sz n D u z i ω + ε) < ‖(modelChaos sz n D hD u hz i).chaos ω‖ ^ 2}
      ≤ ENNReal.ofReal (hwConst q / lam ^ (q + 1)) := by
  set C' := modelChaosEps sz n D hD u hz hu i ε hε with hC'
  set Y : Sizes.SeqΩ sz → ℝ := fun ω => ‖C'.chaos ω‖ with hY
  have hYnn : ∀ ω, 0 ≤ Y ω := fun ω => norm_nonneg _
  have habs : ∀ ω, |Y ω| ^ (2 * (q + 1)) = ‖C'.chaos ω‖ ^ (2 * (q + 1)) := fun ω => by
    rw [hY, abs_of_nonneg (hYnn ω)]
  have hint : Integrable (fun ω => |Y ω| ^ (2 * (q + 1))) (Sizes.seqP sz) := by
    simpa only [habs] using C'.integrable_norm_pow (gaussIBP sz) (q + 1)
  have hmom0 : (∫ ω, ‖C'.chaos ω‖ ^ (2 * (q + 1)) ∂(Sizes.seqP sz)) ≤ hwConst q :=
    mom_modelChaosEps_le hD hz hu i hε q
  have hmom : ∫ ω, |Y ω| ^ (2 * (q + 1)) ∂(Sizes.seqP sz) ≤ hwConst q := by
    simpa only [habs] using hmom0
  have ht : (0 : ℝ) < Real.sqrt lam := Real.sqrt_pos.2 hlam
  have hmark := meas_gt_le_of_moment (P := Sizes.seqP sz) (Y := Y) ht hint hmom
  have hset : {ω | lam * (vqM sz n D u z i ω + ε) < ‖(modelChaos sz n D hD u hz i).chaos ω‖ ^ 2}
      = {ω | Real.sqrt lam < Y ω} := by
    ext ω
    have hs := sqVq_pos (D := D) (z := z) hu hε i ω
    have hsq := sq_sqVq (D := D) (z := z) hu hε i ω
    have hYv : Y ω = ‖(modelChaos sz n D hD u hz i).chaos ω‖ / sqVq sz n D u z i ε ω := by
      rw [hY, hC']; exact norm_chaos_modelChaosEps hD hz hu i hε ω
    have hc : (0 : ℝ) ≤ ‖(modelChaos sz n D hD u hz i).chaos ω‖ := norm_nonneg _
    have hsl : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlam.le
    have hsln : (0 : ℝ) ≤ Real.sqrt lam := Real.sqrt_nonneg lam
    simp only [Set.mem_ofPred_eq, hYv]
    rw [lt_div_iff₀ hs, ← hsq]
    constructor
    · intro h
      nlinarith [h, hs, hc, hsl, hsln,
        sq_nonneg (Real.sqrt lam * sqVq sz n D u z i ε ω - ‖(modelChaos sz n D hD u hz i).chaos ω‖),
        sq_nonneg (Real.sqrt lam * sqVq sz n D u z i ε ω + ‖(modelChaos sz n D hD u hz i).chaos ω‖)]
    · intro h
      have hms := mul_self_lt_mul_self (mul_nonneg hsln hs.le) h
      nlinarith [hms, hsl, hs]
  rw [hset]
  refine hmark.trans (ENNReal.ofReal_le_ofReal ?_)
  have hpow : Real.sqrt lam ^ (2 * (q + 1)) = lam ^ (q + 1) := by
    rw [pow_mul, Real.sq_sqrt hlam.le]
  rw [hpow]

/-- **The tail bound with the true control.**  `{λV_q < |Q|²} = ⋃_m {λ(V_q + 1/(m+1)) < |Q|²}`
is an increasing union, so continuity of the measure from below removes `ε`: no integral limit
theorem, and no separate treatment of `{V_q = 0}`. -/
theorem meas_lt_normSq_chaos_le (hD : D.IsHermitian) (hz : z.im ≠ 0) (hu : 0 ≤ u) (i : Idx d (sz.L n) (sz.W n))
    {lam : ℝ} (hlam : 0 < lam) (q : ℕ) :
    (Sizes.seqP sz) {ω | lam * vqM sz n D u z i ω < ‖(modelChaos sz n D hD u hz i).chaos ω‖ ^ 2}
      ≤ ENNReal.ofReal (hwConst q / lam ^ (q + 1)) := by
  set S : ℕ → Set (Sizes.SeqΩ sz) := fun m =>
    {ω | lam * (vqM sz n D u z i ω + 1 / ((m : ℝ) + 1))
      < ‖(modelChaos sz n D hD u hz i).chaos ω‖ ^ 2} with hS
  have hmono : Monotone S := by
    intro m m' hmm ω hω
    simp only [hS, Set.mem_ofPred_eq] at hω ⊢
    have h1 : (1 : ℝ) / ((m' : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have hmm' : ((m : ℝ) + 1) ≤ ((m' : ℝ) + 1) := by
        have : (m : ℝ) ≤ (m' : ℝ) := by exact_mod_cast hmm
        linarith
      exact one_div_le_one_div_of_le hm hmm'
    nlinarith [hω, h1, hlam]
  have hunion : (⋃ m, S m)
      = {ω | lam * vqM sz n D u z i ω < ‖(modelChaos sz n D hD u hz i).chaos ω‖ ^ 2} := by
    ext ω
    simp only [Set.mem_iUnion, hS, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨m, hm⟩
      have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      nlinarith [hm, hlam, hpos]
    · intro h
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt
        (show (0 : ℝ) < (‖(modelChaos sz n D hD u hz i).chaos ω‖ ^ 2
          - lam * vqM sz n D u z i ω) / lam by
          apply div_pos _ hlam; linarith)
      refine ⟨m, ?_⟩
      rw [lt_div_iff₀ hlam] at hm
      nlinarith [hm]
  rw [← hunion]
  refine le_of_tendsto (tendsto_measure_iUnion_atTop (μ := Sizes.seqP sz) hmono)
    (Filter.Eventually.of_forall fun m => ?_)
  exact meas_lt_normSq_chaos_le_eps hD hz hu i hlam q (by positivity)

/-- With `u = 0` the flow is the zero matrix, so the chaos vanishes. -/
theorem chaos_modelChaos_zero (hD : D.IsHermitian) (hz : z.im ≠ 0) (i : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    (modelChaos sz n D hD 0 hz i).chaos ω = 0 := by
  have hh : ∀ k : {a : Idx d (sz.L n) (sz.W n) // a ≠ i}, (modelChaos sz n D hD 0 hz i).h ω k = 0 := by
    intro k
    rw [modelChaos_h hD hz i ω k, LDEQuadInst_seqHflow_zero]
    rfl
  have hsg : ∀ k : {a : Idx d (sz.L n) (sz.W n) // a ≠ i}, (modelChaos sz n D hD 0 hz i).sg k = 0 := by
    intro k
    rw [modelChaos_sg hD hz i le_rfl k]
    ring
  change (∑ k, ∑ l, _) - (∑ k, _) = 0
  rw [show (∑ k : {a : Idx d (sz.L n) (sz.W n) // a ≠ i}, ∑ l : {a : Idx d (sz.L n) (sz.W n) // a ≠ i},
        (modelChaos sz n D hD 0 hz i).h ω k * (modelChaos sz n D hD 0 hz i).B ω k l *
          (starRingEnd ℂ) ((modelChaos sz n D hD 0 hz i).h ω l)) = 0 from by
      refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
      rw [hh k]; ring,
    show (∑ k : {a : Idx d (sz.L n) (sz.W n) // a ≠ i},
        (((modelChaos sz n D hD 0 hz i).sg k : ℝ) : ℂ) * (modelChaos sz n D hD 0 hz i).B ω k k) = 0 from by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [hsg k]; simp]
  ring

/-! ### Relabelling the quadratic LDE from `Idx` to `Vtx`

The pin `hLquad` of `diag_bound_stochDom` (`Green/EntryDom.lean`) is stated on `Vtx d L W` through
`blockMat`, `greenBlk`, `svar`; the model lives on `Idx d L W`.  These are the
`ldeQuadLHS`/`ldeQuadRHS` analogues of the private relabelling lemmas of `Green/LDE.lean`
(RBM2D `LDEQuadInst.lean:441-505`, with `Sblk2 L W` replaced by `svar d L W g`). -/

section Relabel

variable {m ν : Type*} [Fintype m] [Fintype ν] [DecidableEq m] [DecidableEq ν]

omit [Fintype m] [Fintype ν] [DecidableEq m] [DecidableEq ν] in
private theorem LDEQuadInst_greenMinor_submatrix (e : m ≃ ν) (G : Matrix ν ν ℂ) (a k l : m) :
    greenMinor (G.submatrix e e) a k l = greenMinor G (e a) (e k) (e l) := by
  simp [greenMinor]

private theorem LDEQuadInst_ldeQuadLHS_submatrix (e : m ≃ ν) (H G : Matrix ν ν ℂ)
    (S : ν → ν → ℝ) (t : ℝ) (a : m) :
    ldeQuadLHS (H.submatrix e e) (G.submatrix e e) (fun p q => S (e p) (e q)) t a
      = ldeQuadLHS H G S t (e a) := by
  have h1 : ∑ k ∈ univ.erase a, ∑ l ∈ univ.erase a,
        H.submatrix e e a k * greenMinor (G.submatrix e e) a k l * H.submatrix e e l a
      = ∑ k ∈ univ.erase (e a), ∑ l ∈ univ.erase (e a),
        H (e a) k * greenMinor G (e a) k l * H l (e a) := by
    refine Finset.sum_equiv e (fun k => by simp [Finset.mem_erase]) (fun k _ => ?_)
    refine Finset.sum_equiv e (fun l => by simp [Finset.mem_erase]) (fun l _ => ?_)
    simp [LDEQuadInst_greenMinor_submatrix]
  have h2 : ∑ k ∈ univ.erase a, ((S (e a) (e k) : ℝ) : ℂ) * greenMinor (G.submatrix e e) a k k
      = ∑ k ∈ univ.erase (e a), ((S (e a) k : ℝ) : ℂ) * greenMinor G (e a) k k := by
    refine Finset.sum_equiv e (fun k => by simp [Finset.mem_erase]) (fun k _ => ?_)
    simp [LDEQuadInst_greenMinor_submatrix]
  unfold ldeQuadLHS
  rw [h1, h2]

private theorem LDEQuadInst_ldeQuadRHS_submatrix (e : m ≃ ν) (S : ν → ν → ℝ)
    (G : Matrix ν ν ℂ) (a : m) :
    ldeQuadRHS (fun p q => S (e p) (e q)) (G.submatrix e e) a = ldeQuadRHS S G (e a) := by
  unfold ldeQuadRHS
  refine Finset.sum_equiv e (fun k => by simp [Finset.mem_erase]) (fun k _ => ?_)
  refine Finset.sum_equiv e (fun l => by simp [Finset.mem_erase]) (fun l _ => ?_)
  simp [LDEQuadInst_greenMinor_submatrix]

end Relabel

section RelabelBlock

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The block resolvent is the fine-lattice resolvent, relabelled by `splitEquiv`. -/
private theorem LDEQuadInst_greenBlk_true (E t : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) :
    greenBlk d L W E t M true
      = (green M (zt E t)).submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm := by
  have h0 : greenBlk d L W E t M true = green (blockMat d L W M) (zt E t) := by
    simp only [greenBlk, Gres, green, ite_true]
    exact (Matrix.nonsing_inv_eq_ringInverse _).symm
  rw [h0]
  unfold green blockMat
  have h : (M - zt E t • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)).submatrix
      (splitEquiv d L W).symm (splitEquiv d L W).symm
      = M.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm
        - zt E t • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply, (splitEquiv d L W).symm.injective.eq_iff]
  rw [← h, Matrix.inv_submatrix_equiv]

/-- The block profile `svar` is the fine-lattice profile `svarF` read through `splitEquiv`
(RBM2D `Sblk2_eq_svar`; the merged `svarF_eq_svar`). -/
private theorem LDEQuadInst_svar_funext (g : ℝ) :
    svar d L W g
      = fun p q => svarF d L W g ((splitEquiv d L W).symm p) ((splitEquiv d L W).symm q) := by
  funext p q
  rw [svarF_eq_svar]
  have h1 : split d L W ((splitEquiv d L W).symm p) = p :=
    (splitEquiv d L W).apply_symm_apply p
  have h2 : split d L W ((splitEquiv d L W).symm q) = q :=
    (splitEquiv d L W).apply_symm_apply q
  rw [h1, h2]

private theorem LDEQuadInst_blk_quadLHS (M G : Matrix (Idx d L W) (Idx d L W) ℂ) (t g : ℝ)
    (a : Vtx d L W) :
    ldeQuadLHS (blockMat d L W M) (blockMat d L W G) (svar d L W g) t a
      = ldeQuadLHS M G (svarF d L W g) t ((splitEquiv d L W).symm a) := by
  rw [LDEQuadInst_svar_funext g]
  exact LDEQuadInst_ldeQuadLHS_submatrix (splitEquiv d L W).symm M G (svarF d L W g) t a

private theorem LDEQuadInst_blk_quadRHS (G : Matrix (Idx d L W) (Idx d L W) ℂ) (g : ℝ)
    (a : Vtx d L W) :
    ldeQuadRHS (svar d L W g) (blockMat d L W G) a
      = ldeQuadRHS (svarF d L W g) G ((splitEquiv d L W).symm a) := by
  rw [LDEQuadInst_svar_funext g]
  exact LDEQuadInst_ldeQuadRHS_submatrix (splitEquiv d L W).symm (svarF d L W g) G a

end RelabelBlock

/-! ### The hypothesis `hLquad` of `diag_bound_stochDom` -/

/-- The tail bound at one size and one index, with a deterministic threshold `s > 0` and
`0 ≤ u ≤ 1`, on the fine lattice. -/
private theorem LDEQuadInst_meas_le (hD : D.IsHermitian) (hz : z.im ≠ 0) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (i : Idx d (sz.L n) (sz.W n)) {s : ℝ} (hs : 0 < s) (q : ℕ) :
    (Sizes.seqP sz) {ω | s * ldeQuadRHS (svarF d (sz.L n) (sz.W n) (sz.lam n))
          (green (D + Sizes.seqHflow sz n u ω) z) i
        < ldeQuadLHS (Sizes.seqHflow sz n u ω) (green (D + Sizes.seqHflow sz n u ω) z)
          (svarF d (sz.L n) (sz.W n) (sz.lam n)) u i}
      ≤ ENNReal.ofReal (hwConst q / s ^ (q + 1)) := by
  have hrhs : ∀ ω : Sizes.SeqΩ sz,
      0 ≤ ldeQuadRHS (svarF d (sz.L n) (sz.W n) (sz.lam n)) (green (D + Sizes.seqHflow sz n u ω) z) i := fun ω =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      mul_nonneg (mul_nonneg (svarF_nonneg d (sz.L n) (sz.W n) (sz.lam n) _ _) (by positivity)) (svarF_nonneg d (sz.L n) (sz.W n) (sz.lam n) _ _)
  rcases eq_or_lt_of_le hu0 with hu | hupos
  · -- `u = 0`: the chaos vanishes, so the failure event is empty
    subst hu
    have hempty : {ω : Sizes.SeqΩ sz | s * ldeQuadRHS (svarF d (sz.L n) (sz.W n) (sz.lam n))
          (green (D + Sizes.seqHflow sz n 0 ω) z) i
        < ldeQuadLHS (Sizes.seqHflow sz n 0 ω) (green (D + Sizes.seqHflow sz n 0 ω) z)
          (svarF d (sz.L n) (sz.W n) (sz.lam n)) 0 i} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      rw [← modelChaos_normSq_chaos hD hz i le_rfl ω, chaos_modelChaos_zero hD hz i ω, norm_zero]
      have := hrhs ω
      have : (0 : ℝ) ^ 2 = 0 := by norm_num
      nlinarith
    rw [hempty, measure_empty]
    exact zero_le
  · set lam : ℝ := s / u ^ 2 with hlamdef
    have hlam : 0 < lam := by rw [hlamdef]; positivity
    have hu2 : u ^ 2 ≤ 1 := by nlinarith [hupos, hu1]
    have hlamge : s ≤ lam := by
      rw [hlamdef, le_div_iff₀ (by positivity)]
      nlinarith [hs, hu2]
    have hset : {ω : Sizes.SeqΩ sz | s * ldeQuadRHS (svarF d (sz.L n) (sz.W n) (sz.lam n))
          (green (D + Sizes.seqHflow sz n u ω) z) i
        < ldeQuadLHS (Sizes.seqHflow sz n u ω) (green (D + Sizes.seqHflow sz n u ω) z)
          (svarF d (sz.L n) (sz.W n) (sz.lam n)) u i}
        = {ω | lam * vqM sz n D u z i ω < ‖(modelChaos sz n D hD u hz i).chaos ω‖ ^ 2} := by
      ext ω
      have hL := modelChaos_normSq_chaos hD hz i hu0 ω
      have hV : vqM sz n D u z i ω
          = u ^ 2 * ldeQuadRHS (svarF d (sz.L n) (sz.W n) (sz.lam n)) (green (D + Sizes.seqHflow sz n u ω) z) i := by
        rw [← vqM_eq hD hz hu0 i ω]; exact modelChaos_Vq hD hz i hu0 ω
      have hune : u ≠ 0 := ne_of_gt hupos
      simp only [Set.mem_ofPred_eq, ← hL, hV, hlamdef]
      rw [show s / u ^ 2 * (u ^ 2 *
          ldeQuadRHS (svarF d (sz.L n) (sz.W n) (sz.lam n)) (green (D + Sizes.seqHflow sz n u ω) z) i)
          = s * ldeQuadRHS (svarF d (sz.L n) (sz.W n) (sz.lam n)) (green (D + Sizes.seqHflow sz n u ω) z) i from by
        field_simp]
    rw [hset]
    refine (meas_lt_normSq_chaos_le hD hz hu0 i hlam q).trans (ENNReal.ofReal_le_ofReal ?_)
    have hden : s ^ (q + 1) ≤ lam ^ (q + 1) := pow_le_pow_left₀ hs.le hlamge (q + 1)
    exact div_le_div_of_nonneg_left (hwConst_pos q).le (by positivity) hden

/-- **The quadratic large deviation input `hLquad`, for the flow `D + X` with a deterministic Hermitian shift**
(`D n` Hermitian, `Im z n ≠ 0`, `0 ≤ t n ≤ 1`; the random matrix `X` is the flow of `sz`, the row of the quadratic
form, and the resolvent `G = (D + X - z)⁻¹` supplies its minors).  The proof is that of the band
`stochDom_ldeQuad`: `D` is a constant of the minor, so only `D + X` Hermitian and `Im z ≠ 0` are used.
`D = 0`, `z = z_t` is the band; `D = g₀ Ψ` and `sz.withLam 0` is the block Anderson model (`BA/GreenLDE.lean`). -/
theorem IBPPoly_stochDom_ldeQuad_shift (sz : Sizes d) (hsz : sz.SizeTendsto)
    (D : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hD : ∀ n, (D n).IsHermitian) {z : ℕ → ℂ} (hz : ∀ n, (z n).im ≠ 0)
    {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n ≤ 1) :
    sz.PrecPT (U := fun n => Vtx d (sz.L n) (sz.W n))
      (fun n i ω => ldeQuadLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω))
        (blockMat d (sz.L n) (sz.W n) (green (D n + sz.seqHflow n (t n) ω) (z n)))
        (svar d (sz.L n) (sz.W n) (sz.lam n)) (t n) i)
      (fun n i ω => ldeQuadRHS (svar d (sz.L n) (sz.W n) (sz.lam n))
        (blockMat d (sz.L n) (sz.W n) (green (D n + sz.seqHflow n (t n) ω) (z n))) i) := by
  have hsz' : Filter.Tendsto sz.size Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_iff.mp hsz
  intro τ hτ K hK
  obtain ⟨q, hq⟩ := exists_nat_ge ((K + 1) / τ)
  have hKq : K + 1 ≤ τ * (q : ℝ) := by rw [div_le_iff₀ hτ] at hq; linarith
  have hexp : 0 < τ * ((q : ℝ) + 1) - K := by nlinarith
  filter_upwards [hsz'.eventually (eventually_le_rpow (hwConst q) hexp),
    hsz'.eventually_ge_atTop 1] with n hCN hn1 i
  have hN0 : (0 : ℝ) < (sz.size n : ℝ) := by exact_mod_cast hn1
  have hNτ : (0 : ℝ) < (sz.size n : ℝ) ^ τ := Real.rpow_pos_of_pos hN0 τ
  have hset : {ω : Sizes.SeqΩ sz | (sz.size n : ℝ) ^ τ *
        ldeQuadRHS (svar d (sz.L n) (sz.W n) (sz.lam n))
          (blockMat d (sz.L n) (sz.W n) (green (D n + sz.seqHflow n (t n) ω) (z n))) i
      < ldeQuadLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω))
        (blockMat d (sz.L n) (sz.W n) (green (D n + sz.seqHflow n (t n) ω) (z n)))
        (svar d (sz.L n) (sz.W n) (sz.lam n)) (t n) i}
      = {ω : Sizes.SeqΩ sz | (sz.size n : ℝ) ^ τ *
          ldeQuadRHS (svarF d (sz.L n) (sz.W n) (sz.lam n))
            (green (D n + sz.seqHflow n (t n) ω) (z n))
            ((splitEquiv d (sz.L n) (sz.W n)).symm i)
        < ldeQuadLHS (sz.seqHflow n (t n) ω)
          (green (D n + sz.seqHflow n (t n) ω) (z n))
          (svarF d (sz.L n) (sz.W n) (sz.lam n)) (t n)
          ((splitEquiv d (sz.L n) (sz.W n)).symm i)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, LDEQuadInst_blk_quadLHS, LDEQuadInst_blk_quadRHS]
  change (Sizes.seqP sz) {ω : Sizes.SeqΩ sz | (sz.size n : ℝ) ^ τ *
        ldeQuadRHS (svar d (sz.L n) (sz.W n) (sz.lam n))
          (blockMat d (sz.L n) (sz.W n) (green (D n + sz.seqHflow n (t n) ω) (z n))) i
      < ldeQuadLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω))
        (blockMat d (sz.L n) (sz.W n) (green (D n + sz.seqHflow n (t n) ω) (z n)))
        (svar d (sz.L n) (sz.W n) (sz.lam n)) (t n) i} ≤ _
  rw [hset]
  refine (LDEQuadInst_meas_le (hD n) (hz n) (ht0 n) (ht1 n) _ hNτ q).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hpow : (sz.size n : ℝ) ^ (τ * ((q : ℝ) + 1)) = ((sz.size n : ℝ) ^ τ) ^ (q + 1) := by
    rw [← Real.rpow_natCast ((sz.size n : ℝ) ^ τ) (q + 1), ← Real.rpow_mul hN0.le]
    push_cast
    ring_nf
  calc hwConst q / ((sz.size n : ℝ) ^ τ) ^ (q + 1)
      = hwConst q / (sz.size n : ℝ) ^ (τ * ((q : ℝ) + 1)) := by rw [hpow]
    _ ≤ (sz.size n : ℝ) ^ (τ * ((q : ℝ) + 1) - K) / (sz.size n : ℝ) ^ (τ * ((q : ℝ) + 1)) := by
        gcongr
    _ = (sz.size n : ℝ) ^ (-K) := by
        rw [← Real.rpow_sub hN0]
        congr 1
        ring

/-- **The quadratic large deviation input `hLquad` of `diag_bound_stochDom`,** for the Gaussian
flow `H_{t_n}`:
`|∑_{k,l≠i} H_{ik}G^{(i)}_{kl}H_{li} − t_n∑_{k≠i}S_{ik}G^{(i)}_{kk}|²
  ≺ ∑_{k,l≠i}S_{ik}|G^{(i)}_{kl}|²S_{li}`,
uniformly in `i`, per time `t n` (the conclusion is the text of `hLquad`; RBM2D
`Green/LDEQuadInst.lean:641`, RBM1D `stochDom_ldeQuad`, `86573b9:Gauss/LDEQuadDom.lean:356`, in the
per-time form, so without the union bound).  The band statement is the corollary of
`IBPPoly_stochDom_ldeQuad_shift` at `D = 0`, `z = z_t`. -/
theorem stochDom_ldeQuad (sz : Sizes d) {κ : ℝ} (hκ : 0 < κ) (hsz : sz.SizeTendsto)
    {E t : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n < 1) :
    sz.PrecPT (U := fun n => Vtx d (sz.L n) (sz.W n))
      (fun n i ω => ldeQuadLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true)
        (svar d (sz.L n) (sz.W n) (sz.lam n)) (t n) i)
      (fun n i ω => ldeQuadRHS (svar d (sz.L n) (sz.W n) (sz.lam n))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) i) := by
  have h := IBPPoly_stochDom_ldeQuad_shift sz hsz (fun _ => 0) (fun _ => Matrix.isHermitian_zero)
    (z := fun n => zt (E n) (t n)) (fun n => zt_im_ne_zero hκ (hE n) (ht1 n)) ht0 fun n => (ht1 n).le
  simpa only [zero_add, LDEQuadInst_greenBlk_true, blockMat] using h

/-! ### Compiled nonempty instances (`RBM.Green.IBPInst`)

At the preflight sequence `sz0` (`RBM3D/Defs/Sizes.lean:260`, `d = 3`; at `n = 0`: `L = 4`, `W = 32`,
`lam = 1/64`, `N = (W L)^3 = 2097152`), `E ≡ 0`, `t ≡ 1/2`, `κ = 1`.  The only external hypothesis is
`SizeTendsto` (`sz0_tendsto`, computed at `sz0`); all other hypotheses are deterministic and
discharged. -/

namespace IBPInst

open RBM.Gauss.SizesInst RBM.Green.LDEInst

/-- A diagonal coordinate of size `0`: its variance is `S_xx = W^{-d} (1 + 2 d g²)⁻¹ > 0`. -/
private noncomputable def c0 : Sizes.SeqCoord sz0 := ⟨0, (0, 0, true)⟩

/-- A diagonal coordinate of size `1`. -/
private noncomputable def c1 : Sizes.SeqCoord sz0 := ⟨1, (0, 0, false)⟩

/-- **Instance of `gaussIBP` (`polyInt`)**, at the two-coordinate set `{c₀, c₁}` of two different
sizes and the exponent `2`. -/
theorem gaussIBP_sz0_polyInt :
    Integrable (fun ω : Sizes.SeqΩ sz0 =>
      polyW ({c0, c1} : Finset (Sizes.SeqCoord sz0)) ω ^ 2) (Sizes.seqP sz0) :=
  (gaussIBP sz0).polyInt _ 2

/-- The variance of `c₀` is `S_xx = 32⁻³ (1 + 6/4096)⁻¹`, positive. -/
theorem seqGvar_sz0_c0 :
    (Sizes.seqGvar sz0 c0 : ℝ) = ((32 : ℝ) ^ 3)⁻¹ * (1 + 2 * (3 : ℝ) * (1 / 64) ^ 2)⁻¹ := by
  change (if (0 : Idx 3 (sz0.L 0) (sz0.W 0)) = 0 then
      svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) 0 0
      else svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) 0 0 / 2) = _
  simp only [↓reduceIte, svarF_diag]
  have hW : (sz0.W 0 : ℝ) = 32 := by exact_mod_cast sz0_values.2.1
  have hl : sz0.lam 0 = 1 / 64 := sz0_values.2.2.2
  rw [hW, hl]
  norm_num

theorem seqGvar_sz0_c0_pos : 0 < (Sizes.seqGvar sz0 c0 : ℝ) := by
  rw [seqGvar_sz0_c0]
  norm_num

/-- **Instance of `gaussIBP` (`stein`)** at the nonlinear, unbounded test function `g = ω_{c₀}³`,
`g' = 3 ω_{c₀}²`: `E[ω_{c₀}⁴] = S_xx · E[3 ω_{c₀}²]`, at a coordinate of positive variance. -/
theorem gaussIBP_sz0_stein_cubic :
    ∫ ω, (ω c0 : ℂ) * (ω c0 : ℂ) ^ 3 ∂(Sizes.seqP sz0)
      = (Sizes.seqGvar sz0 c0 : ℝ) * ∫ ω, (3 : ℂ) * (ω c0 : ℂ) ^ 2 ∂(Sizes.seqP sz0) :=
  (gaussIBP sz0).stein c0 (fun ω => (ω c0 : ℂ) ^ 3) (fun ω => 3 * (ω c0 : ℂ) ^ 2)
    ((Tame.coord c0).pow 3) ((Tame.const 3).mul ((Tame.coord c0).pow 2)) (fun ω => by
      have h := (RowChaos.hasDerivAt_ofReal_id (ω c0)).fun_pow 3
      simpa only [Function.update_self, Nat.cast_ofNat, mul_one] using h)

/-- **Instance of `stochDom_ldeQuad`** (the hypothesis `hLquad` of `diag_bound_stochDom`) at `sz0`,
`E ≡ 0`, `κ = 1`, `t ≡ 1/2`: only `SizeTendsto` (computed at `sz0`) and `0 ≤ t < 1`. -/
theorem stochDom_ldeQuad_sz0 :
    sz0.PrecPT (U := fun n => Vtx 3 (sz0.L n) (sz0.W n))
      (fun n i ω => ldeQuadLHS (blockMat 3 (sz0.L n) (sz0.W n) (sz0.seqHflow n (1 / 2) ω))
        (greenBlk 3 (sz0.L n) (sz0.W n) 0 (1 / 2) (sz0.seqHflow n (1 / 2) ω) true)
        (svar 3 (sz0.L n) (sz0.W n) (sz0.lam n)) (1 / 2) i)
      (fun n i ω => ldeQuadRHS (svar 3 (sz0.L n) (sz0.W n) (sz0.lam n))
        (greenBlk 3 (sz0.L n) (sz0.W n) 0 (1 / 2) (sz0.seqHflow n (1 / 2) ω) true) i) :=
  stochDom_ldeQuad sz0 (κ := 1) one_pos sz0_tendsto (E := fun _ => 0) (t := fun _ => 1 / 2)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)

/-- **Instance of `IBPPoly_stochDom_ldeQuad_shift`** at `sz0`, `t ≡ 1/2`, `z ≡ z_{1/2}` and the nonzero shift
`D = (1/2) I` (`LDE_shiftD_sz0`): only `SizeTendsto` (computed at `sz0`), `D` Hermitian, `Im z ≠ 0`, `0 ≤ t ≤ 1`. -/
example := IBPPoly_stochDom_ldeQuad_shift sz0 sz0_tendsto LDE_shiftD_sz0 LDE_shiftD_sz0_isHermitian
  (z := fun _ => zt 0 (1 / 2)) (fun _ => zt_im_ne_zero (κ := 1) one_pos (by norm_num) (by norm_num))
  (t := fun _ => 1 / 2)
  (fun _ => by norm_num) (fun _ => by norm_num)

/-- **`(GiiGEX)`, `3_5:21`, with no large deviation hypothesis left**: `GiiOmegaSeq` at `sz0`,
`E ≡ 0`, `t ≡ 1/2`, `κ = 1`, `𝔠 = 1/6`, `𝔡 = 1/10`, `c = 1`, from the four proved inputs
(`stochDom_ldeRow`, `stochDom_ldeCol`, `stochDom_ldeQuad`, `stochDom_normSq_Hflow_diag`). -/
example : GiiOmegaSeq sz0 (fun _ => 0) (fun _ => 1 / 2) 1 :=
  diag_bound_stochDom sz0 (κ := 1) (𝔠 := 1 / 6) (𝔡 := 1 / 10) (by norm_num) one_pos
    sz0_admissible (E := fun _ => 0) (t := fun _ => 1 / 2) (fun _ => by norm_num)
    (fun _ => by norm_num) (fun _ => by norm_num) one_pos stochDom_ldeRow_sz0
    stochDom_ldeCol_sz0 stochDom_ldeQuad_sz0 stochDom_normSq_Hflow_diag_sz0

/-- The constant at `q = 2` (the preflight table): `hwConst 2 = 125000`. -/
theorem hwConst_two : hwConst 2 = 125000 := by
  unfold hwConst
  norm_num

end IBPInst

end RBM.Green
