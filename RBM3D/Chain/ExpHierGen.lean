/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step6KitGen
import RBM3D.Induction.ExpHier
import RBM3D.Chain.HierDriftGen
import RBM3D.Chain.StepDecompGen
import RBM3D.Chain.CltGen

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The expected hierarchy at `n = 2` over the carrier

Restatement of `Induction/ExpHier` at one size index `n`, over a carrier `Cm : Step2Mat sz` whose loops
are those of the Hermitian matrix `H₀ n + √u X` at the spectral value `ztOf (Cm.m n) (E n) u`
(`CltRepg`, `StepDecompGen_LoopForm`).  Paper: (3.8) `eq_L-Keee` at `n = 2` after taking expectations,
Section 6 (`Sec:Step6`), (6.7) `eq:ExpLWn=2`.  The band hypotheses `|E| < 2`, `zt E`, `H₀ = 0` become
`0 < Im m`, `ztOf`, a Hermitian `H₀ n` (`H₀ ≠ 0` is the case of Lemma 6.1 (`lem:improve_exp_aver`),
"the same as [YY_25]").

* **The regularity class and the generator at `H₀ + seqHflow`**: the class `expHier_Good` of the band
  file is reused by name; its member `ExpHierGen_Good_loopL` is the loop at the generic flow; the
  generator `genMatOf` is the sum of the line Hessians and the spectral derivative
  (`ExpHierGen_genMat_eq_cuts`, the line-Hessian form of the cut expression);
  `ExpHierGen_hasDerivAt_integral` is `∂_u 𝔼 𝓛 = 𝔼 genMatOf` at `H₀ + √u X`, by one dominated
  differentiation in `u` (resolvent chain rule with `H` and `z` moving together:
  `OneStep_hasDerivAt_Gsig`) and the Stein identity `OneStep_stein_coord` at `M = H₀ n`, `x = √u` (the
  factors `u⁻¹` of the band `expHier_second_deriv` do not occur).
* **The `𝒦` ODE and the hierarchy at `k = 2`, per index**: `ExpHierGen_Kloop_hasDerivAt` (from
  `HierDriftGen_KLoop`, `HierDriftGen_KLink` at `n`), `ExpHierGen_hierarchy_two`.
* **The statement `STExpHierAtgL`**: `stExpHiergL_at` (at `n`) and `stExpHiergL_ev` (`∀ᶠ n` under the
  family hypotheses).
-/

open private expHier_Good expHier_Good.mk expHier_Good.cont_ω expHier_Good.cont_u expHier_Good.bdd expHier_Good_add expHier_Good_sub expHier_Good_mul expHier_Good_coef expHier_Good_const
  expHier_Good_sum expHier_Good_integrable expHier_Good_continuousOn_integral expHier_Good_congr
  expHier_continuousOn_Ico expHier_loopOf_wf from RBM3D.Induction.ExpHier

open private expHier_integral_slice from RBM3D.Induction.ExpHier

open private OneStep_Hs OneStep_Hs_eq OneStep_Hs_herm OneStep_continuous_Hs OneStep_stein_coord
  OneStep_integrable_normX OneStep_integrable_coord_mul OneStep_J1_Xmat OneStep_hasDerivAt_Gsig
  OneStep_hasDerivAt_w0 OneStep_w1_add OneStep_w1_smul OneStep_hasDerivAt_trace OneStep_blockMat_add_smul
  OneStep_continuous_gloop OneStep_continuous_J1 OneStep_continuous_J2 from RBM3D.Path.OneStep

noncomputable section

namespace RBM.BA

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-! ## 1. The loop at the generic flow `H₀ + √u X`, `z = ztOf m E u`: continuity, regularity class -/

section Flow

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem ExpHierGen_zim {m : ℂ} (hm : 0 < m.im) (E : ℝ) {u : ℝ} (hu : u < 1) : 0 < (ztOf m E u).im := by
  rw [ztOf_im, etaOf]
  exact mul_pos (by linarith) hm

private theorem ExpHierGen_continuous_Gsig {V : Type*} [TopologicalSpace V] {f : V → Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hf : Continuous f) (hherm : ∀ v, (f v).IsHermitian) {z : V → ℂ} (hz : Continuous z)
    (hzim : ∀ v, (z v).im ≠ 0) (σ : Bool) : Continuous fun v => Gres (f v) (z v) σ := by
  cases σ with
  | true => exact continuous_green_of_isHermitian_moving hf hherm hz hzim
  | false =>
      have h := continuous_green_of_isHermitian_moving hf hherm (Complex.continuous_conj.comp hz)
        (fun v => by simpa using hzim v)
      simpa [Gres] using h

private theorem ExpHierGen_continuous_loopL {V : Type*} [TopologicalSpace V] {f : V → Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hf : Continuous f) (hherm : ∀ v, (f v).IsHermitian) {z : V → ℂ} (hz : Continuous z)
    (hzim : ∀ v, (z v).im ≠ 0) (I : LoopIdx (Zd d L)) : Continuous fun v => loopL d L W (f v) (z v) I := by
  unfold loopL
  refine (continuous_matrixTrace d L W).comp ?_
  generalize I.σ.zip I.a = l
  induction l with
  | nil => exact continuous_const
  | cons p l ih =>
      exact ((ExpHierGen_continuous_Gsig hf hherm hz hzim p.1).mul continuous_const).mul ih

private theorem ExpHierGen_continuous_Hs_time (M₀ : Matrix (Idx d L W) (Idx d L W) ℂ) (ω : Ω d L W) :
    Continuous fun u : ℝ => OneStep_Hs M₀ (Real.sqrt u) ω := by
  simp only [OneStep_Hs_eq]
  exact continuous_const.add ((Complex.continuous_ofReal.comp Real.continuous_sqrt).smul continuous_const)

private theorem ExpHierGen_continuous_ztOf (m : ℂ) (E : ℝ) : Continuous fun u : ℝ => ztOf m E u := by
  unfold ztOf
  exact continuous_const.add ((continuous_const.sub Complex.continuous_ofReal).mul continuous_const)

/-- **The class**: the loop at `H₀ + √u X`, `z = ztOf m E u` is regular on `[0, b]`, `b < 1` (band `expHier_Good_loopL`,
at `H₀ = 0`, `zt E`; bound `card (Vtx) (η⁻¹ W^{-d})^k`). -/
private theorem ExpHierGen_Good_loopL {M₀ : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M₀.IsHermitian) {m : ℂ}
    (hm : 0 < m.im) (E : ℝ) {b : ℝ} (hb0 : 0 ≤ b) (hb : b < 1) {I : LoopIdx (Zd d L)} (hI : I.WF) :
    expHier_Good d L W b (fun u ω => loopL d L W (OneStep_Hs M₀ (Real.sqrt u) ω) (ztOf m E u) I) := by
  have hη : 0 < (1 - b) * m.im := mul_pos (by linarith) hm
  have hlow : ∀ u ∈ Set.Icc (0 : ℝ) b, (1 - b) * m.im ≤ |(ztOf m E u).im| := by
    intro u hu
    rw [abs_of_pos (ExpHierGen_zim hm E (lt_of_le_of_lt hu.2 hb)), ztOf_im, etaOf]
    exact mul_le_mul_of_nonneg_right (by linarith [hu.2]) hm.le
  have hzim : ∀ u ∈ Set.Icc (0 : ℝ) b, (ztOf m E u).im ≠ 0 := fun u hu =>
    (ExpHierGen_zim hm E (lt_of_le_of_lt hu.2 hb)).ne'
  refine expHier_Good.mk (fun u hu => OneStep_continuous_gloop (OneStep_continuous_Hs M₀ _) (OneStep_Hs_herm hM _) (hzim u hu) I)
    (fun ω => ?_) ⟨ (((L * W) ^ d : ℕ) : ℝ) * (((1 - b) * m.im)⁻¹ * ((W : ℝ) ^ d)⁻¹) ^ I.a.length,
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (mul_nonneg (inv_nonneg.2 hη.le) (inv_nonneg.2 (by positivity))) _),
    fun u hu ω => ?_⟩
  · have hc : Continuous fun u : ℝ =>
        loopL d L W (OneStep_Hs M₀ (Real.sqrt u) ω) (ztOf m E (min u b)) I :=
      ExpHierGen_continuous_loopL (ExpHierGen_continuous_Hs_time M₀ ω) (fun u => OneStep_Hs_herm hM _ ω)
        ((ExpHierGen_continuous_ztOf m E).comp (continuous_id.min continuous_const))
        (fun u => (ExpHierGen_zim hm E (lt_of_le_of_lt (min_le_right _ _) hb)).ne') I
    exact hc.continuousOn.congr fun u hu => by simp only [min_eq_left hu.2]
  · exact norm_gloop_le_crude d L W (OneStep_Hs_herm hM _ ω) hη (hlow u hu) I hI

end Flow

/-! ## 2. The `u`-derivative of the expected loop at `H₀ + √u X`: chain rule, domination, Stein -/

section Deriv

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem ExpHierGen_hasDerivAt_ztOf (m : ℂ) (E u : ℝ) : HasDerivAt (fun v : ℝ => ztOf m E v) (-m) u := by
  have h : HasDerivAt (fun v : ℝ => v • (-m : ℂ)) (-m) u := by
    simpa using (hasDerivAt_id u).smul_const (-m : ℂ)
  have hsum := h.const_add ((E : ℂ) + m)
  have hfun : (fun v : ℝ => ztOf m E v) = fun v : ℝ => ((E : ℂ) + m) + v • (-m : ℂ) := by
    funext v
    simp only [ztOf, Complex.real_smul]
    ring
  rw [hfun]
  exact hsum

/-- The resolvent chain rule with the matrix and the spectral value moving together: the loop along `(Hf v, ztOf m E v)` has the first jet
in the direction `H' + m_σ` (`z' = -m`; band `OneStep_hasDerivAt_spec0` is the case `Hf` constant, `m = mE E`). -/
private theorem ExpHierGen_hasDerivAt_loopL {m : ℂ} (E : ℝ) {Hf : ℝ → Matrix (Vtx d L W) (Vtx d L W) ℂ}
    {H' : Matrix (Vtx d L W) (Vtx d L W) ℂ} {u : ℝ} (hH : HasDerivAt Hf H' u) (hherm : (Hf u).IsHermitian)
    (hz : (ztOf m E u).im ≠ 0) (I : LoopIdx (Zd d L)) :
    HasDerivAt (fun v => loopL d L W (Hf v) (ztOf m E v) I)
      (OneStep_J1 (Hf u) (ztOf m E u) (fun σ => H' + PropSpin m σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) I) u := by
  have hR : ∀ σ, HasDerivAt (fun s => Gres (Hf s) (ztOf m E s) σ)
      (-(Gres (Hf u) (ztOf m E u) σ * (H' + PropSpin m σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) *
        Gres (Hf u) (ztOf m E u) σ)) u := by
    intro σ
    refine (OneStep_hasDerivAt_Gsig hH (ExpHierGen_hasDerivAt_ztOf m E u) hherm hz σ).congr_deriv ?_
    cases σ <;> simp [PropSpin, sub_neg_eq_add]
  exact OneStep_hasDerivAt_trace (OneStep_hasDerivAt_w0 (Rt := fun s σ => Gres (Hf s) (ztOf m E s) σ)
    (D := fun σ => H' + PropSpin m σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) (Ei := Eblk d L W) hR (I.σ.zip I.a))

private theorem ExpHierGen_J1_add (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (D₁ D₂ : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ) (I : LoopIdx (Zd d L)) :
    OneStep_J1 H z (fun σ => D₁ σ + D₂ σ) I = OneStep_J1 H z D₁ I + OneStep_J1 H z D₂ I := by
  unfold OneStep_J1
  have h := OneStep_w1_add (R := fun σ => Gres H z σ) (Ei := Eblk d L W) D₁ D₂ (I.σ.zip I.a)
  rw [← Matrix.trace_add, ← h]
  rfl

private theorem ExpHierGen_J1_smul (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (c : ℝ)
    (B : Matrix (Vtx d L W) (Vtx d L W) ℂ) (I : LoopIdx (Zd d L)) :
    OneStep_J1 H z (fun _ => c • B) I = (c : ℂ) * OneStep_J1 H z (fun _ => B) I := by
  unfold OneStep_J1
  have h := OneStep_w1_smul (R := fun σ => Gres H z σ) (Ei := Eblk d L W) c (fun _ : Bool => B) (I.σ.zip I.a)
  have e : (fun _ : Bool => c • B) = c • (fun _ : Bool => B) := rfl
  rw [e, h, Matrix.trace_smul, Complex.real_smul]

/-- The pointwise `u`-derivative of the loop at `H₀ + √u X_ω`, `z = ztOf m E u`, `u > 0`: `(2√u)⁻¹ J1(·, X) + J1(·, m_σ)`. -/
private theorem ExpHierGen_hasDerivAt_F_pt {M₀ : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M₀.IsHermitian) {m : ℂ}
    (E : ℝ) (ω : Ω d L W) {u : ℝ} (hu0 : 0 < u) (hz : (ztOf m E u).im ≠ 0) (I : LoopIdx (Zd d L)) :
    HasDerivAt (fun v : ℝ => loopL d L W (OneStep_Hs M₀ (Real.sqrt v) ω) (ztOf m E v) I)
      (((1 / (2 * Real.sqrt u) : ℝ) : ℂ) *
          OneStep_J1 (OneStep_Hs M₀ (Real.sqrt u) ω) (ztOf m E u) (fun _ => blockMat d L W (Xmat d L W ω)) I +
        OneStep_J1 (OneStep_Hs M₀ (Real.sqrt u) ω) (ztOf m E u)
          (fun σ => PropSpin m σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) I) u := by
  have hsq : HasDerivAt (fun v : ℝ => Real.sqrt v) (1 / (2 * Real.sqrt u)) u := Real.hasDerivAt_sqrt hu0.ne'
  have hH : HasDerivAt (fun v : ℝ => OneStep_Hs M₀ (Real.sqrt v) ω)
      ((1 / (2 * Real.sqrt u)) • blockMat d L W (Xmat d L W ω)) u := by
    have h := (hsq.smul_const (blockMat d L W (Xmat d L W ω))).const_add (blockMat d L W M₀)
    have hfun : (fun v : ℝ => OneStep_Hs M₀ (Real.sqrt v) ω) =
        fun v : ℝ => blockMat d L W M₀ + (Real.sqrt v) • blockMat d L W (Xmat d L W ω) := by
      funext v
      rw [OneStep_Hs_eq, Complex.coe_smul]
    rw [hfun]
    exact h
  have h2 := ExpHierGen_hasDerivAt_loopL (m := m) E hH (OneStep_Hs_herm hM _ ω) hz I
  refine h2.congr_deriv ?_
  rw [ExpHierGen_J1_add (D₁ := fun _ => (1 / (2 * Real.sqrt u)) • blockMat d L W (Xmat d L W ω))
    (D₂ := fun σ => PropSpin m σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)), ExpHierGen_J1_smul]

/-- **The generator**: `genMatOf` (the line Hessians along the coordinates and the spectral derivative) at a Hermitian `M` is
`½ Σ_c gvar_c J2(·, E_c) + J1(·, m_σ)` (band `expHier_genMat_eq_cuts`, whose cut form is not needed: the two parts below are the
quantities that `ExpHierGen_hasDerivAt_integral` produces). -/
private theorem ExpHierGen_genMat_eq_cuts (g : ℝ) {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) {m : ℂ}
    (E : ℝ) {u : ℝ} (hz : (ztOf m E u).im ≠ 0) (I : LoopIdx (Zd d L)) :
    RBM.Ind.genMatOf d L W g m E u M I =
      (1 / 2 : ℂ) * ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
          OneStep_J2 (blockMat d L W M) (ztOf m E u) (fun _ => blockMat d L W (coordinateMatrix d L W c)) I +
        OneStep_J1 (blockMat d L W M) (ztOf m E u) (fun σ => PropSpin m σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) I := by
  unfold RBM.Ind.genMatOf
  have hMb : (blockMat d L W M).IsHermitian := hM.submatrix _
  have h1 : ∀ c : CoordF d L W, deriv (deriv (fun y : ℝ =>
      loopL d L W (blockMat d L W (M + (y : ℂ) • coordinateMatrix d L W c)) (ztOf m E u) I)) 0 =
      OneStep_J2 (blockMat d L W M) (ztOf m E u) (fun _ => blockMat d L W (coordinateMatrix d L W c)) I := by
    intro c
    have hCb : (blockMat d L W (coordinateMatrix d L W c)).IsHermitian :=
      (coordinateMatrix_isHermitian d L W c).submatrix _
    have e : (fun y : ℝ => loopL d L W (blockMat d L W (M + (y : ℂ) • coordinateMatrix d L W c)) (ztOf m E u) I) =
        fun y : ℝ => loopL d L W (blockMat d L W M + (y : ℂ) • blockMat d L W (coordinateMatrix d L W c))
          (ztOf m E u) I := by
      funext y
      rw [OneStep_blockMat_add_smul]
    have hd : deriv (fun y : ℝ => loopL d L W (blockMat d L W M + (y : ℂ) • blockMat d L W (coordinateMatrix d L W c))
          (ztOf m E u) I) =
        fun y : ℝ => OneStep_J1 (blockMat d L W M + (y : ℂ) • blockMat d L W (coordinateMatrix d L W c)) (ztOf m E u)
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) I :=
      funext fun y => (OneStep_hasDerivAt_line0 hMb hCb hz I y).deriv
    rw [e, hd, (OneStep_hasDerivAt_line1 hMb hCb hz I 0).deriv]
    simp
  have h2 : deriv (fun v : ℝ => loopL d L W (blockMat d L W M) (ztOf m E v) I) u =
      OneStep_J1 (blockMat d L W M) (ztOf m E u) (fun σ => PropSpin m σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) I := by
    have h := ExpHierGen_hasDerivAt_loopL (m := m) E (hasDerivAt_const u (blockMat d L W M)) hMb hz I
    rw [h.deriv]
    simp
  rw [h2]
  simp only [h1]

end Deriv

section Integral

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- **The expected derivative**: for a Hermitian `M₀`, `0 < Im m`, `0 < u < 1` and a well-formed loop `I`, the `u`-derivative of
`𝔼 𝓛_I(H₀ + √u X; ztOf m E u)` over the Gaussian law `PF d L W g` is `½ Σ_c gvar_c 𝔼 J2(·, E_c) + 𝔼 J1(·, m_σ)` (the two parts of `genMatOf`,
`ExpHierGen_genMat_eq_cuts`): one dominated differentiation under the integral (bound `K₀ (c₀ ‖X‖ + ‖m‖)`), then Stein at `x = √u`
(`OneStep_stein_coord`; the factor `(2√u)⁻¹` cancels `√u`).  Band: `hasDerivAt_integral_gloop_HflowBlock_spectralZ` and
`deriv_integral_gloop_eq_integral_samplewiseLoopGeneratorCuts` (`H₀ = 0`, `zt E`). -/
private theorem ExpHierGen_hasDerivAt_integral (g : ℝ) {M₀ : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M₀.IsHermitian)
    {m : ℂ} (hm : 0 < m.im) (E : ℝ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) {I : LoopIdx (Zd d L)} (hI : I.WF) :
    HasDerivAt (fun v : ℝ => ∫ ω : Ω d L W, loopL d L W (OneStep_Hs M₀ (Real.sqrt v) ω) (ztOf m E v) I ∂(PF d L W g))
      (∫ ω : Ω d L W, RBM.Ind.genMatOf d L W g m E u (M₀ + ((Real.sqrt u : ℝ) : ℂ) • Xmat d L W ω) I ∂(PF d L W g)) u := by
  classical
  have hzu : (ztOf m E u).im ≠ 0 := (ExpHierGen_zim hm E hu1).ne'
  have hηu : 0 < |(ztOf m E u).im| := abs_pos.mpr hzu
  have hs : Set.Ioo (u / 2) ((1 + u) / 2) ∈ nhds u := Ioo_mem_nhds (by linarith) (by linarith)
  have hu_s : u ∈ Set.Ioo (u / 2) ((1 + u) / 2) := ⟨by linarith, by linarith⟩
  have hη : 0 < ((1 - u) / 2) * m.im := mul_pos (by linarith) hm
  have hlow : ∀ v ∈ Set.Ioo (u / 2) ((1 + u) / 2), ((1 - u) / 2) * m.im ≤ |(ztOf m E v).im| := fun v hv => by
    rw [abs_of_pos (ExpHierGen_zim hm E (by linarith [hv.2])), ztOf_im, etaOf]
    exact mul_le_mul_of_nonneg_right (by linarith [hv.2]) hm.le
  have hzv : ∀ v ∈ Set.Ioo (u / 2) ((1 + u) / 2), (ztOf m E v).im ≠ 0 := fun v hv =>
    (ExpHierGen_zim hm E (by linarith [hv.2])).ne'
  have hvpos : ∀ v ∈ Set.Ioo (u / 2) ((1 + u) / 2), 0 < v := fun v hv => by linarith [hv.1]
  have hcontF : ∀ v : ℝ, v < 1 → Continuous fun ω : Ω d L W =>
      loopL d L W (OneStep_Hs M₀ (Real.sqrt v) ω) (ztOf m E v) I := fun v hv =>
    OneStep_continuous_gloop (OneStep_continuous_Hs M₀ _) (OneStep_Hs_herm hM _) (ExpHierGen_zim hm E hv).ne' I
  have hJc : ∀ v : ℝ, v < 1 → ∀ c : CoordF d L W, Continuous fun ω : Ω d L W =>
      OneStep_J1 (OneStep_Hs M₀ (Real.sqrt v) ω) (ztOf m E v)
        (fun _ => blockMat d L W (coordinateMatrix d L W c)) I := fun v hv c =>
    OneStep_continuous_J1 (OneStep_continuous_Hs M₀ _) (OneStep_Hs_herm hM _) (ExpHierGen_zim hm E hv).ne' I _
  have hJXc : ∀ v : ℝ, v < 1 → Continuous fun ω : Ω d L W =>
      OneStep_J1 (OneStep_Hs M₀ (Real.sqrt v) ω) (ztOf m E v) (fun _ => blockMat d L W (Xmat d L W ω)) I := by
    intro v hv
    simp only [OneStep_J1_Xmat]
    exact continuous_finsetSum _ fun c _ => (Complex.continuous_ofReal.comp (continuous_apply c)).mul (hJc v hv c)
  have hJDc : ∀ v : ℝ, v < 1 → Continuous fun ω : Ω d L W =>
      OneStep_J1 (OneStep_Hs M₀ (Real.sqrt v) ω) (ztOf m E v)
        (fun σ => PropSpin m σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) I := fun v hv =>
    OneStep_continuous_J1 (OneStep_continuous_Hs M₀ _) (OneStep_Hs_herm hM _) (ExpHierGen_zim hm E hv).ne' I _
  set K0 : ℝ := (Fintype.card (Vtx d L W) : ℝ) * ((I.length : ℝ) * (((1 - u) / 2) * m.im)⁻¹ ^ (I.length + 1)) with hK0
  have hK0nn : 0 ≤ K0 :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (inv_nonneg.2 hη.le) _))
  have hbX : ∀ v ∈ Set.Ioo (u / 2) ((1 + u) / 2), ∀ ω : Ω d L W,
      ‖OneStep_J1 (OneStep_Hs M₀ (Real.sqrt v) ω) (ztOf m E v) (fun _ => blockMat d L W (Xmat d L W ω)) I‖ ≤
        K0 * ‖blockMat d L W (Xmat d L W ω)‖ := fun v hv ω => by
    have h := OneStep_norm_J1_le (OneStep_Hs_herm hM (Real.sqrt v) ω) hη (hlow v hv)
      (D := fun _ => blockMat d L W (Xmat d L W ω)) (norm_nonneg _) (fun _ => le_rfl) hI
    refine h.trans (le_of_eq ?_)
    rw [hK0]
    ring
  have hbD : ∀ v ∈ Set.Ioo (u / 2) ((1 + u) / 2), ∀ ω : Ω d L W,
      ‖OneStep_J1 (OneStep_Hs M₀ (Real.sqrt v) ω) (ztOf m E v)
        (fun σ => PropSpin m σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) I‖ ≤ K0 * ‖m‖ := fun v hv ω => by
    have h := OneStep_norm_J1_le (OneStep_Hs_herm hM (Real.sqrt v) ω) hη (hlow v hv)
      (D := fun σ => PropSpin m σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) (norm_nonneg m)
      (fun σ => by
        rw [norm_smul]
        have h1 : ‖PropSpin m σ‖ = ‖m‖ := by cases σ <;> simp [PropSpin]
        rw [h1]
        calc ‖m‖ * ‖(1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)‖ ≤ ‖m‖ * 1 :=
              mul_le_mul_of_nonneg_left OneStep_norm_one_le (norm_nonneg m)
          _ = ‖m‖ := mul_one _) hI
    refine h.trans (le_of_eq ?_)
    rw [hK0]
    ring
  set c0 : ℝ := 1 / (2 * Real.sqrt (u / 2)) with hc0
  have hsq0 : 0 < Real.sqrt (u / 2) := Real.sqrt_pos.2 (by linarith)
  have hcv : ∀ v ∈ Set.Ioo (u / 2) ((1 + u) / 2), 1 / (2 * Real.sqrt v) ≤ c0 := fun v hv => by
    rw [hc0]
    exact one_div_le_one_div_of_le (by positivity) (by
      have := Real.sqrt_le_sqrt (le_of_lt hv.1)
      linarith)
  have hboundint : Integrable (fun ω : Ω d L W => c0 * (K0 * ‖blockMat d L W (Xmat d L W ω)‖) + K0 * ‖m‖)
      (PF d L W g) :=
    (((OneStep_integrable_normX g).const_mul K0).const_mul c0).add (integrable_const _)
  obtain ⟨-, hD⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := PF d L W g) (x₀ := u)
    (s := Set.Ioo (u / 2) ((1 + u) / 2))
    (F := fun v ω => loopL d L W (OneStep_Hs M₀ (Real.sqrt v) ω) (ztOf m E v) I)
    (F' := fun v ω => ((1 / (2 * Real.sqrt v) : ℝ) : ℂ) *
          OneStep_J1 (OneStep_Hs M₀ (Real.sqrt v) ω) (ztOf m E v) (fun _ => blockMat d L W (Xmat d L W ω)) I +
        OneStep_J1 (OneStep_Hs M₀ (Real.sqrt v) ω) (ztOf m E v)
          (fun σ => PropSpin m σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) I)
    hs (by filter_upwards [Iio_mem_nhds hu1] with v hv using (hcontF v hv).aestronglyMeasurable)
    (Integrable.of_bound (hcontF u hu1).aestronglyMeasurable _ (Filter.Eventually.of_forall fun ω =>
      norm_gloop_le_crude d L W (OneStep_Hs_herm hM _ ω) hηu le_rfl I hI))
    (((Complex.continuous_ofReal.comp continuous_const).mul (hJXc u hu1)).add (hJDc u hu1)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω v hv => by
      refine (norm_add_le _ _).trans ?_
      have h1 : ‖((1 / (2 * Real.sqrt v) : ℝ) : ℂ) *
          OneStep_J1 (OneStep_Hs M₀ (Real.sqrt v) ω) (ztOf m E v) (fun _ => blockMat d L W (Xmat d L W ω)) I‖ ≤
          c0 * (K0 * ‖blockMat d L W (Xmat d L W ω)‖) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by
          have := Real.sqrt_pos.2 (hvpos v hv)
          positivity)]
        exact mul_le_mul (hcv v hv) (hbX v hv ω) (norm_nonneg _) (by rw [hc0]; positivity)
      exact add_le_add h1 (hbD v hv ω))
    hboundint
    (Filter.Eventually.of_forall fun ω v hv => ExpHierGen_hasDerivAt_F_pt hM E ω (hvpos v hv) (hzv v hv) I)
  refine hD.congr_deriv ?_
  have hJXint : Integrable (fun ω : Ω d L W =>
      OneStep_J1 (OneStep_Hs M₀ (Real.sqrt u) ω) (ztOf m E u) (fun _ => blockMat d L W (Xmat d L W ω)) I) (PF d L W g) :=
    Integrable.mono' ((OneStep_integrable_normX g).const_mul K0) (hJXc u hu1).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => hbX u hu_s ω)
  have hJDint : Integrable (fun ω : Ω d L W => OneStep_J1 (OneStep_Hs M₀ (Real.sqrt u) ω) (ztOf m E u)
      (fun σ => PropSpin m σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) I) (PF d L W g) :=
    Integrable.of_bound (hJDc u hu1).aestronglyMeasurable (K0 * ‖m‖)
      (Filter.Eventually.of_forall fun ω => hbD u hu_s ω)
  rw [integral_add (hJXint.const_mul _) hJDint, integral_const_mul]
  have hJXeq : ∫ ω : Ω d L W, OneStep_J1 (OneStep_Hs M₀ (Real.sqrt u) ω) (ztOf m E u)
      (fun _ => blockMat d L W (Xmat d L W ω)) I ∂(PF d L W g) =
      (Real.sqrt u : ℂ) * ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
        ∫ ω : Ω d L W, OneStep_J2 (OneStep_Hs M₀ (Real.sqrt u) ω) (ztOf m E u)
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) I ∂(PF d L W g) := by
    simp only [OneStep_J1_Xmat]
    rw [integral_finsetSum _ fun c _ => OneStep_integrable_coord_mul g c (hJc u hu1 c)
      (fun ω => OneStep_norm_J1_le (OneStep_Hs_herm hM _ ω) hηu le_rfl (norm_nonneg _) (fun _ => le_rfl) hI)]
    simp_rw [OneStep_stein_coord g hM hzu hI (Real.sqrt u)]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hJXeq]
  have hs0 : (Real.sqrt u : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hu0).ne'
  have hJ2int : ∀ c : CoordF d L W, Integrable (fun ω : Ω d L W => OneStep_J2 (OneStep_Hs M₀ (Real.sqrt u) ω)
      (ztOf m E u) (fun _ => blockMat d L W (coordinateMatrix d L W c)) I) (PF d L W g) := fun c =>
    Integrable.of_bound (OneStep_continuous_J2 (OneStep_continuous_Hs M₀ _) (OneStep_Hs_herm hM _) hzu I _).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun ω =>
        OneStep_norm_J2_le (OneStep_Hs_herm hM _ ω) hηu le_rfl (norm_nonneg _) (fun _ => le_rfl) hI)
  have hpt : ∀ ω : Ω d L W, RBM.Ind.genMatOf d L W g m E u (M₀ + ((Real.sqrt u : ℝ) : ℂ) • Xmat d L W ω) I =
      (1 / 2 : ℂ) * ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
          OneStep_J2 (OneStep_Hs M₀ (Real.sqrt u) ω) (ztOf m E u)
            (fun _ => blockMat d L W (coordinateMatrix d L W c)) I +
        OneStep_J1 (OneStep_Hs M₀ (Real.sqrt u) ω) (ztOf m E u)
          (fun σ => PropSpin m σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) I := fun ω =>
    ExpHierGen_genMat_eq_cuts g (OneStep_isHermitian_add_realSmul hM (Xmat_isHermitian d L W ω) _) E hzu I
  simp_rw [hpt]
  rw [integral_add ((integrable_finsetSum _ fun c _ => (hJ2int c).const_mul _).const_mul _) hJDint,
    integral_const_mul, integral_finsetSum _ fun c _ => (hJ2int c).const_mul _]
  simp_rw [integral_const_mul]
  congr 1
  push_cast
  field_simp

end Integral

/-! ## 3. The `𝒦` ODE and the hierarchy at `k = 2`, per index -/

section Two

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (n : ℕ)

private theorem ExpHierGen_length_two (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    (KLloopOf d (sz.L n) σ a).length = 2 := by
  change (List.ofFn a).length = 2
  simp

private theorem ExpHierGen_kloop_wf (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    (KLloopOf d (sz.L n) σ a).WF := expHier_loopOf_wf sz n σ a

/-- **The `𝒦` ODE at `n = 2`** (band `expHier_Kloop_hasDerivAt`, from `hasDerivAt_kTwo`; here from `HierDriftGen_KLoop`
and the link `KI = K` on `[0,1)`): for every `σ` and `0 < u < 1`, `∂_u 𝒦^{(2)}_{u,σ,a} = W^d Σ_{c,e} 𝒦 S 𝒦` (`treeEqRhsS` at `k = 2`). -/
theorem ExpHierGen_Kloop_hasDerivAt (hK : HierDriftGen_KLoop Cm n) (hLink : HierDriftGen_KLink Cm n) {u : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    HasDerivAt (fun v : ℝ => Cm.K n v σ a)
      (treeEqRhsS d (sz.L n) (sz.W n) (Cm.S n) (Cm.KI n u) (KLloopOf d (sz.L n) σ a)) u := by
  obtain ⟨M0, hder, -, -⟩ := hK
  have h := hder u ⟨hu0.le, hu1⟩ (KLloopOf d (sz.L n) σ a) (ExpHierGen_kloop_wf n σ a)
    (by rw [ExpHierGen_length_two n σ a])
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hu0 hu1] with v hv
  exact (hLink v ⟨hv.1.le, hv.2⟩ 2 σ a).symm

/-- `𝒦^{(2)}` is continuous on `[0,1)`, including `u = 0` (the ODE holds there for `KI`; `K = KI` on `[0,1)`). -/
theorem ExpHierGen_continuousOn_K (hK : HierDriftGen_KLoop Cm n) (hLink : HierDriftGen_KLink Cm n)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ContinuousOn (fun v : ℝ => Cm.K n v σ a) (Set.Ico 0 1) := by
  obtain ⟨M0, hder, -, -⟩ := hK
  have hc : ContinuousOn (fun v : ℝ => Cm.KI n v (KLloopOf d (sz.L n) σ a)) (Set.Ico 0 1) := fun t ht =>
    (hder t ht (KLloopOf d (sz.L n) σ a) (ExpHierGen_kloop_wf n σ a)
      (by rw [ExpHierGen_length_two n σ a])).continuousAt.continuousWithinAt
  exact hc.congr fun v hv => (hLink v hv 2 σ a).symm

/-- **The hierarchy at one index** (the hierarchy identity with hypotheses at one index `n` only). -/
private theorem ExpHierGen_hierarchyNg_at (E g : ℕ → ℝ) (hL : StepDecompGen_LoopForm Cm E)
    (hS : Cm.S n = SB d (sz.L n) (g n)) (hK : HierDriftGen_KLoop Cm n) (hT : HierDriftGen_KTwo Cm n) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hM : M.IsHermitian) (k : ℕ) (hk : 2 ≤ k) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    RBM.Ind.genMatOf d (sz.L n) (sz.W n) (g n) (Cm.m n) (E n) u M (KLloopOf d (sz.L n) σ a) -
        deriv (fun v : ℝ => Cm.KI n v (KLloopOf d (sz.L n) σ a)) u =
      Step2Gen_ThetaN Cm.toFlowFM n σ u (fun b => STLKIMg Cm n u M (KLloopOf d (sz.L n) σ b)) a +
        ∑ l ∈ Finset.Icc 3 k, STksimLKMg Cm n u M l (KLloopOf d (sz.L n) σ a) +
        STelklkMg Cm n u M (KLloopOf d (sz.L n) σ a) + STegtMg Cm n u M (KLloopOf d (sz.L n) σ a) := by
  have hgen := RBM.Ind.loopGenNOf d (sz.L n) (sz.W n) (g n) (Cm.m n) (E n) (sz.three_le_L n) (hL n).1 u hu1 M hM σ a
  have hpair : RBM.Ind.genMatOf d (sz.L n) (sz.W n) (g n) (Cm.m n) (E n) u M (KLloopOf d (sz.L n) σ a) =
      treeEqRhsS d (sz.L n) (sz.W n) (Cm.S n) (STLIMg Cm n u M) (KLloopOf d (sz.L n) σ a) +
        STegtMg Cm n u M (KLloopOf d (sz.L n) σ a) := by
    refine hgen.trans ?_
    simp only [treeEqRhsS, STegtMg, STavgErrMg, STmsigg, STLIMg, (hL n).2.2.1 u M, hS, PropSpin]
    rfl
  rw [hpair]
  exact loopDrift_sub_K_deriv_ng Cm n hK hT u ⟨hu0, hu1⟩ M k hk σ a

/-- The list-indexed loop of the carrier is its `Fin k`-indexed loop (`StepDecompGen_LoopForm`, `loopM_eq_loopL`). -/
private theorem ExpHierGen_LIM_eq (E : ℕ → ℝ) (hL : StepDecompGen_LoopForm Cm E) (u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    Cm.LIM n u H (KLloopOf d (sz.L n) σ a) = Cm.LM n u H σ a := by
  rw [(hL n).2.2.1 u H, (hL n).2.1 u H k σ a]
  exact (loopM_eq_loopL d (sz.L n) (sz.W n) _ _ σ a).symm

private theorem ExpHierGen_STLKIM_eq (E : ℕ → ℝ) (hL : StepDecompGen_LoopForm Cm E) (hLink : HierDriftGen_KLink Cm n)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {k : ℕ}
    (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    STLKIMg Cm n u H (KLloopOf d (sz.L n) σ a) = STLKMg Cm n u H σ a := by
  unfold STLKIMg STLKMg STLIMg STLMg
  rw [ExpHierGen_LIM_eq Cm n E hL u H σ a, hLink u ⟨hu0, hu1⟩ k σ a]

private theorem ExpHierGen_elklk_two (E : ℕ → ℝ) (hL : StepDecompGen_LoopForm Cm E) (hLink : HierDriftGen_KLink Cm n)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STelklkMg Cm n u H (KLloopOf d (sz.L n) σ a) = STELKLKMg Cm n u H σ a := by
  unfold STelklkMg STELKLKMg
  rw [ExpHierGen_length_two n σ a]
  have h1 : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := by decide
  have h2 : (Finset.Ioc 1 2 : Finset ℕ) = {2} := by decide
  have h3 : (Finset.Ioc 2 2 : Finset ℕ) = ∅ := by decide
  rw [h1, Finset.sum_pair (by decide), h2, h3]
  simp only [Finset.sum_singleton, Finset.sum_empty, add_zero]
  congr 1
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have e1 : (KLloopOf d (sz.L n) σ a).cutGlueL 1 2 x = KLloopOf d (sz.L n) σ ![x, a 1] := by
    simp [KLloopOf, LoopIdx.cutGlueL, List.ofFn_succ]
  have e2 : (KLloopOf d (sz.L n) σ a).cutGlueR 1 2 y = KLloopOf d (sz.L n) σ ![a 0, y] := by
    simp [KLloopOf, LoopIdx.cutGlueR, List.ofFn_succ]
  rw [e1, e2, ExpHierGen_STLKIM_eq Cm n E hL hLink hu0 hu1, ExpHierGen_STLKIM_eq Cm n E hL hLink hu0 hu1]

private theorem ExpHierGen_egt_two (E : ℕ → ℝ) (hL : StepDecompGen_LoopForm Cm E)
    (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STegtMg Cm n u H (KLloopOf d (sz.L n) σ a) = STEGtMg Cm n u H σ a := by
  unfold STegtMg STEGtMg
  rw [ExpHierGen_length_two n σ a]
  have h1 : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := by decide
  rw [h1, Finset.sum_pair (by decide)]
  congr 1
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have e1 : (KLloopOf d (sz.L n) σ a).cutGlue 1 y = KLloopOf d (sz.L n) ![σ 0, σ 0, σ 1] ![y, a 0, a 1] := by
    simp [KLloopOf, LoopIdx.cutGlue, List.ofFn_succ]
  have e2 : (KLloopOf d (sz.L n) σ a).cutGlue 2 y = KLloopOf d (sz.L n) ![σ 0, σ 1, σ 1] ![a 0, y, a 1] := by
    simp [KLloopOf, LoopIdx.cutGlue, List.ofFn_succ]
  have g1 : (KLloopOf d (sz.L n) σ a).σ.getD (1 - 1) false = σ 0 := by simp [KLloopOf, List.ofFn_succ]
  have g2 : (KLloopOf d (sz.L n) σ a).σ.getD (2 - 1) false = σ 1 := by simp [KLloopOf, List.ofFn_succ]
  have av : ∀ (b : Bool) (z : Zd d (sz.L n)), STavgErrMg Cm n u H b z = STavgMg Cm n u H b z := fun b z => by
    unfold STavgErrMg STavgMg STLIMg STLMg
    have : (⟨[b], [z]⟩ : LoopIdx (Zd d (sz.L n))) = KLloopOf d (sz.L n) (fun _ : Fin 1 => b) (fun _ => z) := by
      simp [KLloopOf]
    rw [this, ExpHierGen_LIM_eq Cm n E hL]
  rw [e1, e2, g1, g2, av, av]
  unfold STLIMg STLMg
  rw [ExpHierGen_LIM_eq Cm n E hL, ExpHierGen_LIM_eq Cm n E hL]

/-- **The hierarchy at `k = 2`, per index** (band `expHier_hierarchy_two`; from `ExpHierGen_hierarchyNg_at` and the
`k = 2` reductions of §3 of `Induction/ExpHier`, written for the carrier): for `0 < u < 1`, every Hermitian `M` and every `σ`,
`genMatOf(𝓛_{σ,a}) - ∂_u 𝒦^{(2)} = Θ^{(2)}_{u,σ}(𝓛-𝒦) + ℰ^{LK×LK} + ℰ^{G̃}` (the sum over `l ∈ [3,2]` is empty). -/
theorem ExpHierGen_hierarchy_two (E g : ℕ → ℝ) (hL : StepDecompGen_LoopForm Cm E)
    (hS : Cm.S n = SB d (sz.L n) (g n)) (hK : HierDriftGen_KLoop Cm n) (hT : HierDriftGen_KTwo Cm n)
    (hLink : HierDriftGen_KLink Cm n) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hM : M.IsHermitian)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    RBM.Ind.genMatOf d (sz.L n) (sz.W n) (g n) (Cm.m n) (E n) u M (KLloopOf d (sz.L n) σ a) -
        deriv (fun v : ℝ => Cm.K n v σ a) u =
      Step2Gen_ThetaN Cm.toFlowFM n σ u (STLKMg Cm n u M σ) a + STELKLKMg Cm n u M σ a + STEGtMg Cm n u M σ a := by
  have h := ExpHierGen_hierarchyNg_at Cm n E g hL hS hK hT u hu0.le hu1 M hM 2 le_rfl σ a
  rw [Finset.Icc_eq_empty (by norm_num), Finset.sum_empty, add_zero,
    ExpHierGen_elklk_two Cm n E hL hLink hu0.le hu1, ExpHierGen_egt_two Cm n E hL] at h
  have hKd : deriv (fun v : ℝ => Cm.K n v σ a) u = deriv (fun v : ℝ => Cm.KI n v (KLloopOf d (sz.L n) σ a)) u := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [Ioo_mem_nhds hu0 hu1] with v hv
    exact (hLink v ⟨hv.1.le, hv.2⟩ 2 σ a).symm
  have hfun : (fun b : Fin 2 → Zd d (sz.L n) => STLKIMg Cm n u M (KLloopOf d (sz.L n) σ b)) = STLKMg Cm n u M σ :=
    funext fun b => ExpHierGen_STLKIM_eq Cm n E hL hLink hu0.le hu1 M σ b
  rw [hKd]
  rw [hfun] at h
  exact h

end Two

/-! ## 4. The expected hierarchy at a fixed size, over the Gaussian law `PF d L W (g n)`

`Mu u ω = H₀ n + √u X_ω` is a family of fine matrices (hypothesis `hMu`; the carrier theorem instantiates it by `rfl`); every integrand below is a
function of `Mu u ω`. -/

section Fixed

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (n : ℕ) {E g : ℕ → ℝ}
  {M₀ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
  {Mu : ℝ → Ω d (sz.L n) (sz.W n) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

private theorem ExpHierGen_Mu_herm (hM₀ : M₀.IsHermitian) (hMu : ∀ u ω, Mu u ω = M₀ + ((Real.sqrt u : ℝ) : ℂ) • Xmat d (sz.L n) (sz.W n) ω)
    (u : ℝ) (ω : Ω d (sz.L n) (sz.W n)) : (Mu u ω).IsHermitian := by
  rw [hMu]
  exact OneStep_isHermitian_add_realSmul hM₀ (Xmat_isHermitian d (sz.L n) (sz.W n) ω) _

private theorem ExpHierGen_STLM_eq (hL : StepDecompGen_LoopForm Cm E)
    (hMu : ∀ u ω, Mu u ω = M₀ + ((Real.sqrt u : ℝ) : ℂ) • Xmat d (sz.L n) (sz.W n) ω) (u : ℝ)
    (ω : Ω d (sz.L n) (sz.W n)) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    STLMg Cm n u (Mu u ω) σ a =
      loopL d (sz.L n) (sz.W n) (OneStep_Hs M₀ (Real.sqrt u) ω) (ztOf (Cm.m n) (E n) u) (loopOf σ a) := by
  unfold STLMg
  rw [(hL n).2.1 u (Mu u ω) k σ a, loopFine, loopM_eq_loopL, hMu]
  rfl

private theorem ExpHierGen_Good_STLM (hM₀ : M₀.IsHermitian) (hL : StepDecompGen_LoopForm Cm E)
    (hMu : ∀ u ω, Mu u ω = M₀ + ((Real.sqrt u : ℝ) : ℂ) • Xmat d (sz.L n) (sz.W n) ω) {b : ℝ} (hb0 : 0 ≤ b) (hb : b < 1)
    {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    expHier_Good d (sz.L n) (sz.W n) b (fun u ω => STLMg Cm n u (Mu u ω) σ a) :=
  expHier_Good_congr (ExpHierGen_Good_loopL hM₀ (hL n).1 (E n) hb0 hb (expHier_loopOf_wf sz n σ a))
    fun u ω => (ExpHierGen_STLM_eq Cm n hL hMu u ω σ a).symm

private theorem ExpHierGen_Good_STLKM (hM₀ : M₀.IsHermitian) (hL : StepDecompGen_LoopForm Cm E)
    (hMu : ∀ u ω, Mu u ω = M₀ + ((Real.sqrt u : ℝ) : ℂ) • Xmat d (sz.L n) (sz.W n) ω) (hK : HierDriftGen_KLoop Cm n)
    (hLink : HierDriftGen_KLink Cm n) {b : ℝ} (hb0 : 0 ≤ b) (hb : b < 1) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) :
    expHier_Good d (sz.L n) (sz.W n) b (fun u ω => STLKMg Cm n u (Mu u ω) σ a) :=
  expHier_Good_sub (ExpHierGen_Good_STLM Cm n hM₀ hL hMu hb0 hb σ a)
    (expHier_Good_coef _ ((ExpHierGen_continuousOn_K Cm n hK hLink σ a).mono
      (fun u hu => ⟨hu.1, lt_of_le_of_lt hu.2 hb⟩)))

private theorem ExpHierGen_Good_STELKLKM (hM₀ : M₀.IsHermitian) (hL : StepDecompGen_LoopForm Cm E)
    (hMu : ∀ u ω, Mu u ω = M₀ + ((Real.sqrt u : ℝ) : ℂ) • Xmat d (sz.L n) (sz.W n) ω) (hK : HierDriftGen_KLoop Cm n)
    (hLink : HierDriftGen_KLink Cm n) {b : ℝ} (hb0 : 0 ≤ b) (hb : b < 1) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) :
    expHier_Good d (sz.L n) (sz.W n) b (fun u ω => STELKLKMg Cm n u (Mu u ω) σ a) := by
  have hlk : ∀ a' : Fin 2 → Zd d (sz.L n), expHier_Good d (sz.L n) (sz.W n) b
      (fun u ω => STLKMg Cm n u (Mu u ω) σ a') := fun a' =>
    ExpHierGen_Good_STLKM Cm n hM₀ hL hMu hK hLink hb0 hb σ a'
  exact expHier_Good_mul expHier_Good_const
    (expHier_Good_sum _ _ fun x _ => expHier_Good_sum _ _ fun y _ =>
      expHier_Good_mul (expHier_Good_mul (hlk _) expHier_Good_const) (hlk _))

private theorem ExpHierGen_Good_STEGtM (hM₀ : M₀.IsHermitian) (hL : StepDecompGen_LoopForm Cm E)
    (hMu : ∀ u ω, Mu u ω = M₀ + ((Real.sqrt u : ℝ) : ℂ) • Xmat d (sz.L n) (sz.W n) ω) {b : ℝ} (hb0 : 0 ≤ b) (hb : b < 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    expHier_Good d (sz.L n) (sz.W n) b (fun u ω => STEGtMg Cm n u (Mu u ω) σ a) := by
  have havg : ∀ (s : Bool) (x : Zd d (sz.L n)), expHier_Good d (sz.L n) (sz.W n) b
      (fun u ω => STavgMg Cm n u (Mu u ω) s x) := fun s x =>
    expHier_Good_sub (ExpHierGen_Good_STLM Cm n hM₀ hL hMu hb0 hb (fun _ : Fin 1 => s) (fun _ => x)) expHier_Good_const
  exact expHier_Good_mul expHier_Good_const
    (expHier_Good_sum _ _ fun x _ => expHier_Good_sum _ _ fun y _ =>
      expHier_Good_add
        (expHier_Good_mul (expHier_Good_mul (havg _ _) expHier_Good_const)
          (ExpHierGen_Good_STLM Cm n hM₀ hL hMu hb0 hb _ _))
        (expHier_Good_mul (expHier_Good_mul (havg _ _) expHier_Good_const)
          (ExpHierGen_Good_STLM Cm n hM₀ hL hMu hb0 hb _ _)))

/-- The expectation of `Θ^{(2)}_{u,σ}` of a family of integrable tensors is `Θ^{(2)}_{u,σ}` of the expectation (band `expHier_integral_thetaOp`,
for the carrier kernel `Step2Gen_ThetaN`). -/
private theorem ExpHierGen_integral_ThetaN {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') (C : FlowFM sz) {k : ℕ}
    (σ : Fin k → Bool) (u : ℝ) (Φ : Ω' → (Fin k → Zd d (sz.L n)) → ℂ) (hΦ : ∀ b, Integrable (fun ω => Φ ω b) P)
    (a : Fin k → Zd d (sz.L n)) :
    ∫ ω, Step2Gen_ThetaN C n σ u (Φ ω) a ∂P = Step2Gen_ThetaN C n σ u (fun b => ∫ ω, Φ ω b ∂P) a := by
  unfold Step2Gen_ThetaN
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun b _ => (hΦ _).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun b _ => (hΦ _).const_mul _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul]

end Fixed

section FixedDeriv

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (n : ℕ) {E g : ℕ → ℝ}
  {M₀ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
  {Mu : ℝ → Ω d (sz.L n) (sz.W n) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- **The expected hierarchy at a fixed size** (band `expHier_hasDerivAt_fixed`): on `(0,1)`,
`∂_u (𝔼 𝓛^{(2)} - 𝒦^{(2)}) = Θ^{(2)}_{u,σ}(𝔼 𝓛^{(2)} - 𝒦^{(2)}) + (𝔼 ℰ^{LK×LK} + 𝔼 ℰ^{G̃})` over the law `PF d L W (g n)` of the Hermitian
matrix `Mu u ω = H₀ n + √u X_ω` (the carrier loops are those of `Mu u ω`, `StepDecompGen_LoopForm`). -/
private theorem ExpHierGen_hasDerivAt_fixed (hM₀ : M₀.IsHermitian) (hL : StepDecompGen_LoopForm Cm E)
    (hMu : ∀ u ω, Mu u ω = M₀ + ((Real.sqrt u : ℝ) : ℂ) • Xmat d (sz.L n) (sz.W n) ω)
    (hS : Cm.S n = SB d (sz.L n) (g n)) (hK : HierDriftGen_KLoop Cm n) (hT : HierDriftGen_KTwo Cm n)
    (hLink : HierDriftGen_KLink Cm n) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) :
    HasDerivAt (fun v : ℝ => (∫ ω, STLMg Cm n v (Mu v ω) σ a ∂(PF d (sz.L n) (sz.W n) (g n))) - Cm.K n v σ a)
      (Step2Gen_ThetaN Cm.toFlowFM n σ u
          (fun b => (∫ ω, STLMg Cm n u (Mu u ω) σ b ∂(PF d (sz.L n) (sz.W n) (g n))) - Cm.K n u σ b) a +
        ((∫ ω, STELKLKMg Cm n u (Mu u ω) σ a ∂(PF d (sz.L n) (sz.W n) (g n))) +
          ∫ ω, STEGtMg Cm n u (Mu u ω) σ a ∂(PF d (sz.L n) (sz.W n) (g n)))) u := by
  set P := PF d (sz.L n) (sz.W n) (g n) with hP
  have hder1 := ExpHierGen_hasDerivAt_integral (g n) hM₀ (hL n).1 (E n) hu0 hu1 (I := loopOf σ a)
    (expHier_loopOf_wf sz n σ a)
  have hfun : (fun v : ℝ => ∫ ω, STLMg Cm n v (Mu v ω) σ a ∂P) =
      fun v : ℝ => ∫ ω, loopL d (sz.L n) (sz.W n) (OneStep_Hs M₀ (Real.sqrt v) ω) (ztOf (Cm.m n) (E n) v)
        (loopOf σ a) ∂P := by
    funext v
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => ExpHierGen_STLM_eq Cm n hL hMu v ω σ a)
  have hder1' : HasDerivAt (fun v : ℝ => ∫ ω, STLMg Cm n v (Mu v ω) σ a ∂P)
      (∫ ω : Ω d (sz.L n) (sz.W n), RBM.Ind.genMatOf d (sz.L n) (sz.W n) (g n) (Cm.m n) (E n) u
        (M₀ + ((Real.sqrt u : ℝ) : ℂ) • Xmat d (sz.L n) (sz.W n) ω) (loopOf σ a) ∂P) u := by
    rw [hfun]
    exact hder1
  have hderK := ExpHierGen_Kloop_hasDerivAt Cm n hK hLink hu0 hu1 σ a
  refine (hder1'.sub hderK).congr_deriv ?_
  set Kp := treeEqRhsS d (sz.L n) (sz.W n) (Cm.S n) (Cm.KI n u) (KLloopOf d (sz.L n) σ a) with hKp
  have hpt : ∀ ω : Ω d (sz.L n) (sz.W n),
      RBM.Ind.genMatOf d (sz.L n) (sz.W n) (g n) (Cm.m n) (E n) u (M₀ + ((Real.sqrt u : ℝ) : ℂ) • Xmat d (sz.L n) (sz.W n) ω)
        (loopOf σ a) =
      Step2Gen_ThetaN Cm.toFlowFM n σ u (STLKMg Cm n u (Mu u ω) σ) a + STELKLKMg Cm n u (Mu u ω) σ a +
        STEGtMg Cm n u (Mu u ω) σ a + Kp := fun ω => by
    have h : RBM.Ind.genMatOf d (sz.L n) (sz.W n) (g n) (Cm.m n) (E n) u (Mu u ω) (loopOf σ a) -
        deriv (fun v : ℝ => Cm.K n v σ a) u =
        Step2Gen_ThetaN Cm.toFlowFM n σ u (STLKMg Cm n u (Mu u ω) σ) a + STELKLKMg Cm n u (Mu u ω) σ a +
          STEGtMg Cm n u (Mu u ω) σ a :=
      ExpHierGen_hierarchy_two Cm n E g hL hS hK hT hLink hu0 hu1 (Mu u ω) (ExpHierGen_Mu_herm n hM₀ hMu u ω) σ a
    rw [hderK.deriv] at h
    rw [← hMu u ω]
    linear_combination h
  have hub : u ∈ Set.Icc (0 : ℝ) u := ⟨hu0.le, le_rfl⟩
  have hiL : ∀ {k : ℕ} (σ' : Fin k → Bool) (a' : Fin k → Zd d (sz.L n)),
      Integrable (fun ω => STLMg Cm n u (Mu u ω) σ' a') P := fun σ' a' =>
    expHier_Good_integrable (g n) (ExpHierGen_Good_STLM Cm n hM₀ hL hMu hu0.le hu1 σ' a') hub
  have hiLK : ∀ b : Fin 2 → Zd d (sz.L n), Integrable (fun ω => STLKMg Cm n u (Mu u ω) σ b) P := fun b =>
    expHier_Good_integrable (g n) (ExpHierGen_Good_STLKM Cm n hM₀ hL hMu hK hLink hu0.le hu1 σ b) hub
  have hiΘ : Integrable (fun ω => Step2Gen_ThetaN Cm.toFlowFM n σ u (STLKMg Cm n u (Mu u ω) σ) a) P := by
    unfold Step2Gen_ThetaN
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun b _ => (hiLK _).const_mul _
  have hiE1 : Integrable (fun ω => STELKLKMg Cm n u (Mu u ω) σ a) P :=
    expHier_Good_integrable (g n) (ExpHierGen_Good_STELKLKM Cm n hM₀ hL hMu hK hLink hu0.le hu1 σ a) hub
  have hiE2 : Integrable (fun ω => STEGtMg Cm n u (Mu u ω) σ a) P :=
    expHier_Good_integrable (g n) (ExpHierGen_Good_STEGtM Cm n hM₀ hL hMu hu0.le hu1 σ a) hub
  have hLK : (fun b : Fin 2 → Zd d (sz.L n) => ∫ ω, STLKMg Cm n u (Mu u ω) σ b ∂P) =
      fun b => (∫ ω, STLMg Cm n u (Mu u ω) σ b ∂P) - Cm.K n u σ b := by
    funext b
    change ∫ ω, (STLMg Cm n u (Mu u ω) σ b - Cm.K n u σ b) ∂P = _
    rw [integral_sub (hiL σ b) (integrable_const _), integral_const, probReal_univ, one_smul]
  have hΘ := ExpHierGen_integral_ThetaN n P Cm.toFlowFM σ u (fun ω b => STLKMg Cm n u (Mu u ω) σ b) hiLK a
  rw [hLK] at hΘ
  have hi12 : Integrable (fun ω => Step2Gen_ThetaN Cm.toFlowFM n σ u (STLKMg Cm n u (Mu u ω) σ) a +
      STELKLKMg Cm n u (Mu u ω) σ a) P := hiΘ.add hiE1
  have hi123 : Integrable (fun ω => Step2Gen_ThetaN Cm.toFlowFM n σ u (STLKMg Cm n u (Mu u ω) σ) a +
      STELKLKMg Cm n u (Mu u ω) σ a + STEGtMg Cm n u (Mu u ω) σ a) P := hi12.add hiE2
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hi123 (integrable_const _),
    integral_add hi12 hiE2, integral_add hiΘ hiE1, hΘ, integral_const, probReal_univ, one_smul]
  ring

end FixedDeriv

section FixedCont

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (n : ℕ) {E g : ℕ → ℝ}
  {M₀ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
  {Mu : ℝ → Ω d (sz.L n) (sz.W n) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- `𝔼 𝓛^{(k)}` is continuous on `[0,1)` (band `expHier_continuousOn_integral_loopL`, at `H₀ n`, `ztOf`). -/
private theorem ExpHierGen_continuousOn_STLM (hM₀ : M₀.IsHermitian) (hL : StepDecompGen_LoopForm Cm E)
    (hMu : ∀ u ω, Mu u ω = M₀ + ((Real.sqrt u : ℝ) : ℂ) • Xmat d (sz.L n) (sz.W n) ω) {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) :
    ContinuousOn (fun u : ℝ => ∫ ω, STLMg Cm n u (Mu u ω) σ a ∂(PF d (sz.L n) (sz.W n) (g n))) (Set.Ico 0 1) :=
  expHier_continuousOn_Ico fun b hb0 hb1 =>
    expHier_Good_continuousOn_integral (g n) (ExpHierGen_Good_STLM Cm n hM₀ hL hMu hb0 hb1 σ a)

/-- The drift `𝔼 ℰ^{LK×LK} + 𝔼 ℰ^{G̃}` is continuous on `[0,1)` (band `expHier_continuousOn_drift`). -/
private theorem ExpHierGen_continuousOn_drift (hM₀ : M₀.IsHermitian) (hL : StepDecompGen_LoopForm Cm E)
    (hMu : ∀ u ω, Mu u ω = M₀ + ((Real.sqrt u : ℝ) : ℂ) • Xmat d (sz.L n) (sz.W n) ω) (hK : HierDriftGen_KLoop Cm n)
    (hLink : HierDriftGen_KLink Cm n) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ContinuousOn (fun u : ℝ => (∫ ω, STELKLKMg Cm n u (Mu u ω) σ a ∂(PF d (sz.L n) (sz.W n) (g n))) +
      ∫ ω, STEGtMg Cm n u (Mu u ω) σ a ∂(PF d (sz.L n) (sz.W n) (g n))) (Set.Ico 0 1) :=
  (expHier_continuousOn_Ico fun b hb0 hb1 =>
      expHier_Good_continuousOn_integral (g n) (ExpHierGen_Good_STELKLKM Cm n hM₀ hL hMu hK hLink hb0 hb1 σ a)).add
    (expHier_continuousOn_Ico fun b hb0 hb1 =>
      expHier_Good_continuousOn_integral (g n) (ExpHierGen_Good_STEGtM Cm n hM₀ hL hMu hb0 hb1 σ a))

end FixedCont

/-! ## 5. The statement `STExpHierAtgL`, per index and eventually -/

section Target

/-- **`stExpHiergL_at`**: over a carrier `Cm` that represents `H₀ n + √u X` of the law `seqP (sz.withLam g')` at `ztOf (Cm.m n) (E n) u`
(`CltRepg`, `StepDecompGen_LoopForm`, variance law `S n = SB d (L n) (g' n)`) and has the `𝒦` classes `HierDriftGen_KLoop`, `HierDriftGen_KTwo`, `HierDriftGen_KLink` at the index `n`,
the expected loop `f_u = 𝔼 𝓛^{(2)}_u - 𝒦^{(2)}_u` and the drift `D_u = 𝔼 ℰ^{LK×LK}_u + 𝔼 ℰ^{G̃}_u` are continuous on `[0,1)` and
`∂_u f_u = Θ^{(2)}_{u,σ} f_u + D_u` on `(0,1)` (`Θ^{(2)}` the carrier generator `Step2Gen_ThetaN`).  No `|E| < 2`, `M = mI`, `H₀ = 0`. -/
theorem stExpHiergL_at {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ)
    (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (g' E : ℕ → ℝ) (n : ℕ) :
    CltRepg Cm.toFlowFM μ H₀ g' E → StepDecompGen_LoopForm Cm E → Cm.S n = SB d (sz.L n) (g' n) →
      HierDriftGen_KLoop Cm n → HierDriftGen_KTwo Cm n → HierDriftGen_KLink Cm n →
        STExpHierAtgL Cm.toFlowFM μ n := by
  rintro ⟨hμ, hH₀, hrep⟩ hL hS hK hT hLink
  obtain ⟨Mu, hMu⟩ : ∃ Mu : ℝ → Ω d (sz.L n) (sz.W n) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
      ∀ u ω, Mu u ω = H₀ n + ((Real.sqrt u : ℝ) : ℂ) • Xmat d (sz.L n) (sz.W n) ω := ⟨fun u ω => _, fun _ _ => rfl⟩
  -- the carrier loops are the loops of the flow matrix
  have hLrep : ∀ (u : ℝ) (ω : sz.SeqΩ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Cm.toFlowFM.L n u σ a ω = STLMg Cm n u (Mu u ((sz.withLam g').slice n ω)) σ a := by
    intro u ω k σ a
    have h1 := (hrep n u ω).2 k σ a
    have h2 := (hL n).2.1 u (H₀ n + ((Real.sqrt u : ℝ) : ℂ) • Xmat d (sz.L n) (sz.W n) ((sz.withLam g').slice n ω)) k σ a
    have h3 := hMu u ((sz.withLam g').slice n ω)
    calc Cm.toFlowFM.L n u σ a ω
        = loopFine d (sz.L n) (sz.W n) (H₀ n + ((Real.sqrt u : ℝ) : ℂ) • Xmat d (sz.L n) (sz.W n) ((sz.withLam g').slice n ω))
            (ztOf (Cm.m n) (E n) u) σ a := h1
      _ = Cm.LM n u (H₀ n + ((Real.sqrt u : ℝ) : ℂ) • Xmat d (sz.L n) (sz.W n) ((sz.withLam g').slice n ω)) σ a := h2.symm
      _ = STLMg Cm n u (Mu u ((sz.withLam g').slice n ω)) σ a := congrArg (fun H => Cm.LM n u H σ a) h3.symm
  have hslice : ∀ G : Ω d (sz.L n) (sz.W n) → ℂ, AEStronglyMeasurable G (PF d (sz.L n) (sz.W n) (g' n)) →
      ∫ ω : sz.SeqΩ, G ((sz.withLam g').slice n ω) ∂μ = ∫ ω, G ω ∂(PF d (sz.L n) (sz.W n) (g' n)) := by
    intro G hG
    rw [hμ]
    exact expHier_integral_slice (sz.withLam g') n G hG
  have hI1 : ∀ v : ℝ, 0 ≤ v → v < 1 → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      ∫ ω : sz.SeqΩ, Cm.toFlowFM.L n v σ a ω ∂μ =
        ∫ ω, STLMg Cm n v (Mu v ω) σ a ∂(PF d (sz.L n) (sz.W n) (g' n)) := by
    intro v hv0 hv1 σ a
    rw [integral_congr_ae (Filter.Eventually.of_forall fun ω => hLrep v ω σ a)]
    exact hslice (fun ω' => STLMg Cm n v (Mu v ω') σ a)
      (expHier_Good.cont_ω (ExpHierGen_Good_STLM Cm n (hH₀ n) hL hMu hv0 hv1 σ a) v ⟨hv0, le_rfl⟩).aestronglyMeasurable
  have hI2 : ∀ v : ℝ, 0 ≤ v → v < 1 → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      ∫ ω : sz.SeqΩ, STELKLKg Cm.toFlowFM n v σ a ω ∂μ =
        ∫ ω, STELKLKMg Cm n v (Mu v ω) σ a ∂(PF d (sz.L n) (sz.W n) (g' n)) := by
    intro v hv0 hv1 σ a
    have hpt : ∀ ω, STELKLKg Cm.toFlowFM n v σ a ω =
        STELKLKMg Cm n v (Mu v ((sz.withLam g').slice n ω)) σ a := fun ω => by
      unfold STELKLKg STELKLKMg STLKMg
      simp only [hLrep]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact hslice (fun ω' => STELKLKMg Cm n v (Mu v ω') σ a)
      (expHier_Good.cont_ω (ExpHierGen_Good_STELKLKM Cm n (hH₀ n) hL hMu hK hLink hv0 hv1 σ a) v
        ⟨hv0, le_rfl⟩).aestronglyMeasurable
  have hI3 : ∀ v : ℝ, 0 ≤ v → v < 1 → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      ∫ ω : sz.SeqΩ, STEGtg Cm.toFlowFM n v σ a ω ∂μ =
        ∫ ω, STEGtMg Cm n v (Mu v ω) σ a ∂(PF d (sz.L n) (sz.W n) (g' n)) := by
    intro v hv0 hv1 σ a
    have hpt : ∀ ω, STEGtg Cm.toFlowFM n v σ a ω =
        STEGtMg Cm n v (Mu v ((sz.withLam g').slice n ω)) σ a := fun ω => by
      unfold STEGtg STEGtMg STavgMg STmsigg
      simp only [hLrep]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact hslice (fun ω' => STEGtMg Cm n v (Mu v ω') σ a)
      (expHier_Good.cont_ω (ExpHierGen_Good_STEGtM Cm n (hH₀ n) hL hMu hv0 hv1 σ a) v
        ⟨hv0, le_rfl⟩).aestronglyMeasurable
  intro σ a
  refine ⟨?_, ?_, ?_⟩
  · exact ((ExpHierGen_continuousOn_STLM (g := g') Cm n (hH₀ n) hL hMu σ a).sub
      (ExpHierGen_continuousOn_K Cm n hK hLink σ a)).congr fun v hv => by
      rw [hI1 v hv.1 hv.2]
      try rfl
  · exact (ExpHierGen_continuousOn_drift (g := g') Cm n (hH₀ n) hL hMu hK hLink σ a).congr fun v hv => by
      rw [hI2 v hv.1 hv.2, hI3 v hv.1 hv.2]
      try rfl
  · intro u hu
    have h := ExpHierGen_hasDerivAt_fixed (g := g') Cm n (hH₀ n) hL hMu hS hK hT hLink hu.1 hu.2 σ a
    have hev : (fun v : ℝ => (∫ ω : sz.SeqΩ, Cm.toFlowFM.L n v σ a ω ∂μ) - Cm.toFlowFM.K n v σ a) =ᶠ[nhds u]
        (fun v : ℝ => (∫ ω, STLMg Cm n v (Mu v ω) σ a ∂(PF d (sz.L n) (sz.W n) (g' n))) - Cm.K n v σ a) := by
      filter_upwards [Ioo_mem_nhds hu.1 hu.2] with v hv
      rw [hI1 v hv.1.le hv.2]
    refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
    simp only [hI1 u hu.1.le hu.2, hI2 u hu.1.le hu.2, hI3 u hu.1.le hu.2]

/-- **`stExpHiergL_ev`** (= `STExpHierAtgL` for all large `n` along every flow of a family; hypotheses inline): the
guarded representation data `(H₀, g', E)` with `CltRepg`, the carrier `StepDecompGen_LoopForm` and the variance law, and, eventually in `n`, the
classes `HierDriftGen_KLoop`, `HierDriftGen_KTwo`, `HierDriftGen_KLink` (block Anderson: `baHierDrift_classes`; `HierDriftGen_KLoop`, `HierDriftGen_KTwo` hold only eventually).  No `∀ n` hierarchy or drift hypothesis. -/
theorem stExpHiergL_ev {d : ℕ} (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) (hmk : ∀ (sz : Sizes d) (z : ℕ → ℂ), (mkM sz z).toFlowFM = mk sz z)
    (hrep : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∃ (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (g' E : ℕ → ℝ),
        CltRepg (mk sz z) (law sz) H₀ g' E ∧ StepDecompGen_LoopForm (mkM sz z) E ∧
          ∀ n, (mkM sz z).S n = SB d (sz.L n) (g' n))
    (hcls : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n in atTop, HierDriftGen_KLoop (mkM sz z) n ∧ HierDriftGen_KTwo (mkM sz z) n ∧
        HierDriftGen_KLink (mkM sz z) n) :
    ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n in atTop, STExpHierAtgL (mk sz z) (law sz) n := by
  intro sz κ ε 𝔠 𝔡 z hκ hf
  obtain ⟨H₀, g', E, hClt, hL, hS⟩ := hrep sz κ ε 𝔠 𝔡 z hκ hf
  filter_upwards [hcls sz κ ε 𝔠 𝔡 z hκ hf] with n hn
  obtain ⟨hK, hT, hLink⟩ := hn
  have h := stExpHiergL_at (mkM sz z) (law sz) H₀ g' E n (by rw [hmk]; exact hClt) hL (hS n) hK hT hLink
  rwa [hmk] at h

end Target

end RBM.BA
