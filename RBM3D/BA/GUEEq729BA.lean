/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GUEOneLoop
import RBM3D.Universality.GUEPhase.Eq729A

/-!
# The GUE drift and the eq729 recursion on the block Anderson grid

`gueHBA` is the BA grid path `g Ψ_I + H_k` (see `BA/GUEOneLoop`), with
`H_k` of the model `sz.withLam 0` (`S^{(B)}(0) = 1`).  Band counterparts (read from
`Universality/GUEPhase`): `Drift.lean` (`oneStepEnvelopeGUE`, `condExp_loop_step_gue`,
`condExp_loop_drift_gue`) and `Eq729A.lean` (`eq729_eG2`, `eq729_duhamel`,
`eq729_one_step`).  Paper: the matrix Brownian motion (2.36) `MBM` (`H_0 =
ilambda Ψ` for block Anderson), the spectral parameter flow (2.37) `eq:zt` and `η_t` (2.38) `eta`.

Every statement is at the flow datum `(g, E, m)` (profile level): `m` is free with `0 < Im m`
and `‖m‖ ≤ 1` (for block Anderson `m = m(E, ilambda₀)`, `BAReal`); the flow is `ztOf m E`,
`etaOf m`, and the band hypothesis on `E` is replaced by these two.  The band flow is the case
`m = m_sc(E)`.

* §1-§2 `oneStepEnvelopeGUEOf`: the one-step expansion with its envelope for one GUE
  increment along `ztOf m E`.  The space step is the band `Drift_space_step` (generic in the
  spectral parameter); the time step is redone along `ztOf m E` (`GUEEq729BA_time_step`, `d_u
  ztOf m E u = -m`).
* §3 `condExp_loop_step_gueBA`, `condExp_loop_drift_gueBA`: the
  freezing lemma for `A + H_k` (`A = g Ψ_I`), and the conditional drift bounded by the envelope.
* §4-§5 `eq729FBA`, `eq729eBA`, `eq729_eG2BA`
  (`mSigOf`), `eq729_duhamelBA`, `eq729_one_stepBA` (used by the block Anderson version of
  `gueGrid_eq729`).

## Reuse of the band pieces

The private pieces of `Drift`, `Eq729A`, `Generator` and `OneStep` are used through `open private …
from` (the space step, the closure of the envelope constant, the Taylor lemma, the freezing
lemma, the bounded-measurable calculus `Eq729A_BM`, the quadratic and pair bounds, the
derivatives of words of resolvent factors).  The discrete recursion `eq729_Kdisc` is used by name (it is
generic in the primitive `Kf`).  Every helper is `private` with the prefix GUEEq729BA_.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false

noncomputable section

open private Drift_space_step Drift_closure Drift_taylor2 Drift_deriv_deriv Drift_g Drift_Hs Drift_Hs_eq Drift_Hs_herm
  Drift_continuous_Hs Drift_continuous_gloop Drift_integrable_normX Drift_integral_normX_le Drift_card_Block
  Drift_condExp_freezeC Drift_Phi Drift_continuous_Phi Drift_norm_Phi_le Drift_herm_of_isHermitian
  Drift_isHermitian_add_smul Drift_scaledSlice Drift_measurable_scaledSlice Drift_map_scaledSlice
  Drift_gueH_succ'
  from RBM3D.Universality.GUEPhase.Drift
open private Eq729A_BM Eq729A_BM_const Eq729A_BM.add Eq729A_BM.sub Eq729A_BM.mul Eq729A_BM.sum Eq729A_BM.integrable
  Eq729A_norm_integral_Wsum_le' Eq729A_integral_primBil_left Eq729A_integral_primBil_right Eq729A_quad
  Eq729A_pair Eq729A_time_succ Eq729A_loopL_one_false
  from RBM3D.Universality.GUEPhase.Eq729A
open private Generator_hasDerivAt_Gsig_spec from RBM3D.Universality.GUEPhase.Generator
open private OneStep_hasDerivAt_w0 OneStep_hasDerivAt_w1 OneStep_hasDerivAt_trace from RBM3D.Path.OneStep

namespace RBM.BA

open MeasureTheory ProbabilityTheory Filter Matrix Finset RBM RBM.Gauss RBM.Path RBM.Loop RBM.Univ
  RBM.Univ.GUEPhase
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-! ## 1. The jets of the loop functional along `ztOf m E` -/

section Jets

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The spectral direction of the factor `G(σ)` along `ztOf m E`: `m_σ · 1`. -/
private def GUEEq729BA_Dsp (d L W : ℕ) (m : ℂ) : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  fun σ => mSigOf m σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)

private theorem GUEEq729BA_hasDerivAt_spec0 {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian)
    {m : ℂ} (hm : 0 < m.im) {E v : ℝ} (hv : v < 1) (I : Loop.LoopIdx (Zd d L)) :
    HasDerivAt (fun s : ℝ => loopL d L W H (ztOf m E s) I)
      (OneStep_J1 H (ztOf m E v) (GUEEq729BA_Dsp d L W m) I) v :=
  OneStep_hasDerivAt_trace
    (OneStep_hasDerivAt_w0 (Rt := fun s σ => Gres H (ztOf m E s) σ)
      (D := GUEEq729BA_Dsp d L W m) (Ei := Eblk d L W)
      (fun σ => Generator_hasDerivAt_Gsig_spec hH hm hv σ) (I.σ.zip I.a))

private theorem GUEEq729BA_hasDerivAt_spec1 {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian)
    {m : ℂ} (hm : 0 < m.im) {E v : ℝ} (hv : v < 1) (I : Loop.LoopIdx (Zd d L)) :
    HasDerivAt (fun s : ℝ => OneStep_J1 H (ztOf m E s) (GUEEq729BA_Dsp d L W m) I)
      (OneStep_J2 H (ztOf m E v) (GUEEq729BA_Dsp d L W m) I) v :=
  OneStep_hasDerivAt_trace
    (OneStep_hasDerivAt_w1 (Rt := fun s σ => Gres H (ztOf m E s) σ)
      (D := GUEEq729BA_Dsp d L W m) (Ei := Eblk d L W)
      (fun σ => Generator_hasDerivAt_Gsig_spec hH hm hv σ) (I.σ.zip I.a))

end Jets

/-! ## 2. The time step and the envelope -/

section TimeStep

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem GUEEq729BA_norm_Dsp_le {m : ℂ} (hm1 : ‖m‖ ≤ 1) (σ : Bool) :
    ‖GUEEq729BA_Dsp d L W m σ‖ ≤ 1 := by
  have hm : ‖mSigOf m σ‖ ≤ 1 := by cases σ <;> simpa [mSigOf] using hm1
  unfold GUEEq729BA_Dsp
  rw [norm_smul]
  calc ‖mSigOf m σ‖ * ‖(1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)‖ ≤ 1 * 1 :=
        mul_le_mul hm OneStep_norm_one_le (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

private theorem GUEEq729BA_eta_pos {m : ℂ} (hm : 0 < m.im) {u : ℝ} (hu : u < 1) : 0 < etaOf m u :=
  mul_pos (by linarith) hm

private theorem GUEEq729BA_eta_le {m : ℂ} (hm : 0 < m.im) {u t : ℝ} (hut : u ≤ t) :
    etaOf m t ≤ etaOf m u := by
  unfold etaOf
  exact mul_le_mul_of_nonneg_right (by linarith) hm.le

/-- **The time step** along `ztOf m E`: Taylor expansion of `v ↦ f_v(A)` at fixed `A` (the band `Drift_time_step`,
redone for the generic flow; the spectral direction is `GUEEq729BA_Dsp`, `d_u ztOf m E u = -m`). -/
private theorem GUEEq729BA_time_step {A : Matrix (Idx d L W) (Idx d L W) ℂ} (hA : A.IsHermitian)
    {m : ℂ} (hm : 0 < m.im) (hm1 : ‖m‖ ≤ 1) {E u Δ : ℝ} (hΔ : 0 ≤ Δ) (hu1 : u + Δ < 1)
    {I : Loop.LoopIdx (Zd d L)} (hwf : I.WF) :
    ‖loopL d L W (blockMat d L W A) (ztOf m E (u + Δ)) I - loopL d L W (blockMat d L W A) (ztOf m E u) I
        - (Δ : ℂ) * OneStep_J1 (blockMat d L W A) (ztOf m E u) (GUEEq729BA_Dsp d L W m) I‖
      ≤ ((Fintype.card (Vtx d L W) : ℝ) * ((I.length : ℝ) * (I.length + 1) *
          (etaOf m (u + Δ))⁻¹ ^ (I.length + 2))) * Δ ^ 2 / 2 := by
  have hAb : (blockMat d L W A).IsHermitian := hA.submatrix _
  have hη := GUEEq729BA_eta_pos hm hu1
  have hvη : ∀ v ∈ Set.Icc u (u + Δ), etaOf m (u + Δ) ≤ |(ztOf m E v).im| := fun v hv => by
    rw [ztOf_im, abs_of_pos (GUEEq729BA_eta_pos hm (by linarith [hv.2]))]
    exact GUEEq729BA_eta_le hm hv.2
  have h := Drift_taylor2 (f := fun v => loopL d L W (blockMat d L W A) (ztOf m E v) I)
    (f₁ := fun v => OneStep_J1 (blockMat d L W A) (ztOf m E v) (GUEEq729BA_Dsp d L W m) I)
    (f₂ := fun v => OneStep_J2 (blockMat d L W A) (ztOf m E v) (GUEEq729BA_Dsp d L W m) I)
    (a := u) (b := u + Δ)
    (B := (Fintype.card (Vtx d L W) : ℝ) * ((I.length : ℝ) * (I.length + 1) *
      (etaOf m (u + Δ))⁻¹ ^ (I.length + 2))) (by linarith)
    (fun v hv' => GUEEq729BA_hasDerivAt_spec0 hAb hm (by linarith [hv'.2]) I)
    (fun v hv' => GUEEq729BA_hasDerivAt_spec1 hAb hm (by linarith [hv'.2]) I)
    (fun v hv' => by
      have := OneStep_norm_J2_le hAb hη (hvη v hv') zero_le_one (D := GUEEq729BA_Dsp d L W m)
        (GUEEq729BA_norm_Dsp_le hm1) hwf
      simpa using this)
  simpa using h

end TimeStep

section Assembly

/-- **The one-step expansion with its envelope for one GUE increment along the generic flow `ztOf m E`**
(the analogue of `oneStepEnvelopeGUE`, with the generator `genMatGUEOf`, the hypothesis `0 < Im m ∧ ‖m‖ ≤ 1` in
place of the band one on `E`, and the envelope constant written out with `etaOf m`): for Hermitian `M`,
`0 ≤ u`, `0 ≤ Δ`, `u + Δ < 1`, a well-formed loop of length `ℓ` and `X ~ gueP d L W`,
`‖E Φ_{u+Δ}(M + √Δ X) - Φ_u(M) - Δ · genMatGUEOf‖ ≤ 16 (ℓ+3)⁴ N⁴ (1 + η_{u+Δ}⁻¹)^{ℓ+4} Δ^{3/2}`, `N = (W L)^d`. -/
theorem oneStepEnvelopeGUEOf :
    ∀ (d L W : ℕ) [NeZero L] [NeZero W] (m : ℂ) (E : ℝ), 0 < m.im → ‖m‖ ≤ 1 →
      ∀ (I : Loop.LoopIdx (Zd d L)), I.WF →
      ∀ (u Δ : ℝ), 0 ≤ u → 0 ≤ Δ → u + Δ < 1 →
        ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian →
          ‖(∫ ω', loopL d L W (blockMat d L W (M + (Real.sqrt Δ : ℂ) • Xmat d L W ω'))
                (ztOf m E (u + Δ)) I ∂(gueP d L W)) -
              loopL d L W (blockMat d L W M) (ztOf m E u) I -
              (Δ : ℂ) * genMatGUEOf d L W m E u M I‖ ≤
            16 * ((I.length : ℝ) + 3) ^ 4 * (((W * L) ^ d : ℕ) : ℝ) ^ 4 *
              (1 + (etaOf m (u + Δ))⁻¹) ^ (I.length + 4) * Δ ^ ((3 : ℝ) / 2) := by
  intro d L W _ _ m E hm hm1 I hwf u Δ hu hΔ hu1 M hM
  have hΔ1 : Δ < 1 := by linarith
  set τ : ℝ := Real.sqrt Δ with hτ
  have hτ0 : 0 ≤ τ := Real.sqrt_nonneg Δ
  have hτ2 : τ ^ 2 = Δ := Real.sq_sqrt hΔ
  have hτΔ : Δ ≤ τ := by nlinarith
  have hτ3 : Δ ^ ((3 : ℝ) / 2) = τ ^ 3 := by
    rw [hτ, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hΔ]
    norm_num
  have hη : 0 < etaOf m (u + Δ) := GUEEq729BA_eta_pos hm hu1
  have hzu : (ztOf m E u).im ≠ 0 := by
    rw [ztOf_im]
    exact (GUEEq729BA_eta_pos hm (by linarith)).ne'
  have hηu : etaOf m (u + Δ) ≤ |(ztOf m E u).im| := by
    rw [ztOf_im, abs_of_pos (GUEEq729BA_eta_pos hm (by linarith))]
    exact GUEEq729BA_eta_le hm (by linarith)
  have hηv : etaOf m (u + Δ) ≤ |(ztOf m E (u + Δ)).im| := by
    rw [ztOf_im, abs_of_pos hη]
  have hzv : (ztOf m E (u + Δ)).im ≠ 0 := by
    rw [ztOf_im]
    exact hη.ne'
  have hMb : (blockMat d L W M).IsHermitian := hM.submatrix _
  set c₁ : ℝ := (Fintype.card (Vtx d L W) : ℝ) * ((I.length : ℝ) * (I.length + 1) *
    (etaOf m (u + Δ))⁻¹ ^ (I.length + 2)) with hc₁
  -- the generator, in the jets
  have hgen : genMatGUEOf d L W m E u M I = Drift_g (ztOf m E u) I M
      + OneStep_J1 (blockMat d L W M) (ztOf m E u) (GUEEq729BA_Dsp d L W m) I := by
    unfold genMatGUEOf Drift_g
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Drift_deriv_deriv hM (coordinateMatrix_isHermitian d L W c) hzu I]
    · exact (GUEEq729BA_hasDerivAt_spec0 hMb hm (by linarith) I).deriv
  -- integrability of the sample functionals
  have hint : ∀ v : ℝ, (ztOf m E v).im ≠ 0 → Integrable
      (fun ω : Ω d L W => loopL d L W (Drift_Hs M τ ω) (ztOf m E v) I) (gueP d L W) := fun v hv => by
    have hv' : 0 < |(ztOf m E v).im| := abs_pos.mpr hv
    exact Integrable.of_bound (Drift_continuous_gloop (Drift_continuous_Hs M τ)
      (Drift_Hs_herm hM τ) hv I).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun ω =>
        norm_gloop_le_crude d L W (Drift_Hs_herm hM τ ω) hv' le_rfl I hwf)
  -- the space step
  have hT2 := Drift_space_step hM hzu hη hηu hwf hτ0
  -- the time step, integrated
  have hT1 : ‖(∫ ω : Ω d L W, loopL d L W (Drift_Hs M τ ω) (ztOf m E (u + Δ)) I ∂(gueP d L W))
      - (∫ ω : Ω d L W, loopL d L W (Drift_Hs M τ ω) (ztOf m E u) I ∂(gueP d L W))
      - (Δ : ℂ) * OneStep_J1 (blockMat d L W M) (ztOf m E u) (GUEEq729BA_Dsp d L W m) I‖
      ≤ c₁ * τ ^ 3 * (1 / 2 + 4 * (Fintype.card (Idx d L W) : ℝ) ^ 2) := by
    have hpt : ∀ ω : Ω d L W, ‖loopL d L W (Drift_Hs M τ ω) (ztOf m E (u + Δ)) I
        - loopL d L W (Drift_Hs M τ ω) (ztOf m E u) I
        - (Δ : ℂ) * OneStep_J1 (blockMat d L W M) (ztOf m E u) (GUEEq729BA_Dsp d L W m) I‖
        ≤ c₁ * Δ ^ 2 / 2 + (c₁ * Δ * τ) * ‖blockMat d L W (Xmat d L W ω)‖ := by
      intro ω
      have hA : (M + (τ : ℂ) • Xmat d L W ω).IsHermitian :=
        OneStep_isHermitian_add_realSmul hM (Xmat_isHermitian d L W ω) τ
      have h1 := GUEEq729BA_time_step (E := E) hA hm hm1 hΔ hu1 hwf
      have h2 := OneStep_norm_J1_sub_le (Drift_Hs_herm hM τ ω) hMb hη hηu zero_le_one
        (D := GUEEq729BA_Dsp d L W m) (GUEEq729BA_norm_Dsp_le hm1) hwf
      have hd : ‖Drift_Hs M τ ω - blockMat d L W M‖ = τ * ‖blockMat d L W (Xmat d L W ω)‖ := by
        rw [Drift_Hs_eq, add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hτ0]
      rw [hd] at h2
      have hsplit : loopL d L W (Drift_Hs M τ ω) (ztOf m E (u + Δ)) I
          - loopL d L W (Drift_Hs M τ ω) (ztOf m E u) I
          - (Δ : ℂ) * OneStep_J1 (blockMat d L W M) (ztOf m E u) (GUEEq729BA_Dsp d L W m) I
          = (loopL d L W (blockMat d L W (M + (τ : ℂ) • Xmat d L W ω)) (ztOf m E (u + Δ)) I
            - loopL d L W (blockMat d L W (M + (τ : ℂ) • Xmat d L W ω)) (ztOf m E u) I
            - (Δ : ℂ) * OneStep_J1 (blockMat d L W (M + (τ : ℂ) • Xmat d L W ω)) (ztOf m E u)
              (GUEEq729BA_Dsp d L W m) I)
            + (Δ : ℂ) * (OneStep_J1 (Drift_Hs M τ ω) (ztOf m E u) (GUEEq729BA_Dsp d L W m) I
              - OneStep_J1 (blockMat d L W M) (ztOf m E u) (GUEEq729BA_Dsp d L W m) I) := by
        simp only [Drift_Hs]
        ring
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      have h3 : ‖(Δ : ℂ) * (OneStep_J1 (Drift_Hs M τ ω) (ztOf m E u) (GUEEq729BA_Dsp d L W m) I
          - OneStep_J1 (blockMat d L W M) (ztOf m E u) (GUEEq729BA_Dsp d L W m) I)‖
          ≤ Δ * (c₁ * (τ * ‖blockMat d L W (Xmat d L W ω)‖)) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΔ]
        refine mul_le_mul_of_nonneg_left ?_ hΔ
        refine h2.trans (le_of_eq ?_)
        rw [hc₁]
        ring
      have h1' : ‖loopL d L W (blockMat d L W (M + (τ : ℂ) • Xmat d L W ω)) (ztOf m E (u + Δ)) I
            - loopL d L W (blockMat d L W (M + (τ : ℂ) • Xmat d L W ω)) (ztOf m E u) I
            - (Δ : ℂ) * OneStep_J1 (blockMat d L W (M + (τ : ℂ) • Xmat d L W ω)) (ztOf m E u)
              (GUEEq729BA_Dsp d L W m) I‖ ≤ c₁ * Δ ^ 2 / 2 := h1
      calc _ ≤ c₁ * Δ ^ 2 / 2 + Δ * (c₁ * (τ * ‖blockMat d L W (Xmat d L W ω)‖)) := add_le_add h1' h3
        _ = _ := by ring
    have hsub : (∫ ω : Ω d L W, loopL d L W (Drift_Hs M τ ω) (ztOf m E (u + Δ)) I ∂(gueP d L W))
        - (∫ ω : Ω d L W, loopL d L W (Drift_Hs M τ ω) (ztOf m E u) I ∂(gueP d L W))
        - (Δ : ℂ) * OneStep_J1 (blockMat d L W M) (ztOf m E u) (GUEEq729BA_Dsp d L W m) I
        = ∫ ω : Ω d L W, (loopL d L W (Drift_Hs M τ ω) (ztOf m E (u + Δ)) I
          - loopL d L W (Drift_Hs M τ ω) (ztOf m E u) I
          - (Δ : ℂ) * OneStep_J1 (blockMat d L W M) (ztOf m E u) (GUEEq729BA_Dsp d L W m) I)
            ∂(gueP d L W) := by
      have i12 : Integrable (fun ω : Ω d L W => loopL d L W (Drift_Hs M τ ω) (ztOf m E (u + Δ)) I
          - loopL d L W (Drift_Hs M τ ω) (ztOf m E u) I) (gueP d L W) :=
        (hint _ hzv).sub (hint _ hzu)
      rw [integral_sub i12 (integrable_const _), integral_sub (hint _ hzv) (hint _ hzu)]
      simp
    rw [hsub]
    have ib : Integrable (fun ω : Ω d L W => c₁ * Δ ^ 2 / 2
        + (c₁ * Δ * τ) * ‖blockMat d L W (Xmat d L W ω)‖) (gueP d L W) :=
      (integrable_const _).add (Drift_integrable_normX.const_mul (c₁ * Δ * τ))
    refine (norm_integral_le_of_norm_le ib (Filter.Eventually.of_forall hpt)).trans ?_
    rw [integral_add (integrable_const _) (Drift_integrable_normX.const_mul _),
      integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have hν := Drift_integral_normX_le (d := d) (L := L) (W := W)
    rw [← OneStep_card_Idx] at hν
    have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
    have hΔ2 : Δ ^ 2 ≤ Δ * τ := by nlinarith
    calc c₁ * Δ ^ 2 / 2 + c₁ * Δ * τ * ∫ ω : Ω d L W, ‖blockMat d L W (Xmat d L W ω)‖ ∂(gueP d L W)
        ≤ c₁ * Δ ^ 2 / 2 + c₁ * Δ * τ * (4 * (Fintype.card (Idx d L W) : ℝ) ^ 2) := by
          gcongr
      _ ≤ c₁ * (Δ * τ) / 2 + c₁ * Δ * τ * (4 * (Fintype.card (Idx d L W) : ℝ) ^ 2) := by
          gcongr
      _ = c₁ * τ ^ 3 * (1 / 2 + 4 * (Fintype.card (Idx d L W) : ℝ) ^ 2) := by
          rw [← hτ2]
          ring
  -- assembly
  have hLHS : (∫ ω : Ω d L W, loopL d L W (blockMat d L W (M + (Real.sqrt Δ : ℂ) • Xmat d L W ω))
        (ztOf m E (u + Δ)) I ∂(gueP d L W)) - loopL d L W (blockMat d L W M) (ztOf m E u) I
        - (Δ : ℂ) * genMatGUEOf d L W m E u M I
      = ((∫ ω : Ω d L W, loopL d L W (Drift_Hs M τ ω) (ztOf m E u) I ∂(gueP d L W))
          - loopL d L W (blockMat d L W M) (ztOf m E u) I
          - ((τ ^ 2 : ℝ) : ℂ) * Drift_g (ztOf m E u) I M)
        + ((∫ ω : Ω d L W, loopL d L W (Drift_Hs M τ ω) (ztOf m E (u + Δ)) I ∂(gueP d L W))
          - (∫ ω : Ω d L W, loopL d L W (Drift_Hs M τ ω) (ztOf m E u) I ∂(gueP d L W))
          - (Δ : ℂ) * OneStep_J1 (blockMat d L W M) (ztOf m E u) (GUEEq729BA_Dsp d L W m) I) := by
    rw [hgen, hτ2]
    simp only [Drift_Hs]
    ring
  rw [hLHS]
  refine (norm_add_le _ _).trans ((add_le_add hT2 hT1).trans ?_)
  rw [hτ3, OneStep_card_Idx, Drift_card_Block]
  have hN : (1 : ℝ) ≤ (((W * L) ^ d : ℕ) : ℝ) := by
    have : 1 ≤ (W * L) ^ d :=
      Nat.one_le_pow _ _ (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne W))
        (Nat.pos_of_ne_zero (NeZero.ne L)))
    exact_mod_cast this
  have hcl := Drift_closure I.length hN (inv_nonneg.mpr hη.le)
  have hτ3' : 0 ≤ τ ^ 3 := by positivity
  rw [hc₁, Drift_card_Block]
  calc _ = (32 * (((W * L) ^ d : ℕ) : ℝ) ^ 3 * (((W * L) ^ d : ℕ) : ℝ) *
            ((I.length : ℝ) * (I.length + 1) * (I.length + 2) * (etaOf m (u + Δ))⁻¹ ^ (I.length + 3))
            / 3
          + ((((W * L) ^ d : ℕ) : ℝ) * ((I.length : ℝ) * (I.length + 1) *
            (etaOf m (u + Δ))⁻¹ ^ (I.length + 2))) * (1 / 2 + 4 * (((W * L) ^ d : ℕ) : ℝ) ^ 2))
          * τ ^ 3 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcl hτ3'

end Assembly

/-! ## 3. The conditional step and the conditional drift on the BA grid path -/

section LoopStepBA

variable {d : ℕ} (sz : Sizes d)

/-- The shifted grid path `A + H_k` is `filt sz k`-measurable as a matrix-valued map. -/
private theorem GUEEq729BA_measurable_shift_filt (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    Measurable[filt sz k] (fun ω : PathΩ sz => A + gueH sz t1 t0 K n k ω) :=
  @measurable_pi_iff _ _ _ (filt sz k) _ _ |>.mpr fun i =>
    @measurable_pi_iff _ _ _ (filt sz k) _ _ |>.mpr fun j =>
      ((gueH_adapted sz t1 t0 K n k i j).measurable).const_add (A i j)

/-- **The one-step conditional expectation at a Hermitian shift `A`** (`condExp_loop_step_gue`, for
the path `A + H_k`): the freezing lemma applied to `A + H_{k+1} = (A + H_k) + √Δ X_{k+1}`. -/
private theorem GUEEq729BA_condExp_step (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) {z : ℂ} (hz : z.im ≠ 0)
    (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hA : A.IsHermitian)
    {I : Loop.LoopIdx (Zd d (sz.L n))} (hwf : I.WF) :
    (Pgue sz)[fun ω : PathΩ sz =>
        loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (A + gueH sz t1 t0 K n (k + 1) ω))
          z I | filt sz k]
      =ᵐ[Pgue sz] fun ω =>
        ∫ x, loopL d (sz.L n) (sz.W n)
          (blockMat d (sz.L n) (sz.W n) (A + gueH sz t1 t0 K n k ω
            + (Real.sqrt (gridStep t1 t0 K n) : ℂ) • Xmat d (sz.L n) (sz.W n) x))
          z I ∂(gueP d (sz.L n) (sz.W n)) := by
  classical
  set Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ :=
    Drift_Phi d (sz.L n) (sz.W n) z I with hΦdef
  have hΦcont : Continuous Φ := Drift_continuous_Phi hz I
  set F : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → Sizes.SeqΩ sz → ℂ :=
    fun p x => Φ (p + (Real.sqrt (gridStep t1 t0 K n) : ℂ) •
      Xmat d (sz.L n) (sz.W n) (Drift_scaledSlice sz n x)) with hFdef
  have hXmeas : Measurable (fun x : Sizes.SeqΩ sz =>
      Xmat d (sz.L n) (sz.W n) (Drift_scaledSlice sz n x)) :=
    (continuous_Xmat d (sz.L n) (sz.W n)).measurable.comp (Drift_measurable_scaledSlice n)
  have hFmeas : Measurable (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ ×
      Sizes.SeqΩ sz => F p.1 p.2) := by
    have h2 : Measurable fun x : Sizes.SeqΩ sz =>
        (Real.sqrt (gridStep t1 t0 K n) : ℂ) •
          Xmat d (sz.L n) (sz.W n) (Drift_scaledSlice sz n x) :=
      hXmeas.const_smul (Real.sqrt (gridStep t1 t0 K n) : ℂ)
    have h3 : Measurable fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ ×
        Sizes.SeqΩ sz => p.1 + (Real.sqrt (gridStep t1 t0 K n) : ℂ) •
          Xmat d (sz.L n) (sz.W n) (Drift_scaledSlice sz n p.2) :=
      measurable_fst.add (h2.comp measurable_snd)
    have h4 := hΦcont.measurable.comp h3
    exact h4
  have hFbdd : ∀ p x, ‖F p x‖ ≤ (((sz.L n * sz.W n) ^ d : ℕ) : ℝ) *
      (|z.im|⁻¹ * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹)) ^ I.a.length :=
    fun p x => Drift_norm_Phi_le hz hwf _
  have hYmeas : Measurable[filt sz k] (fun ω : PathΩ sz => A + gueH sz t1 t0 K n k ω) :=
    GUEEq729BA_measurable_shift_filt sz t1 t0 K n k A
  have hYmeas' : Measurable (fun ω : PathΩ sz => A + gueH sz t1 t0 K n k ω) :=
    hYmeas.mono ((filt sz).le k) le_rfl
  have hFInt : ∀ p, Integrable (F p) (gueUnit sz) := by
    intro p
    have hpair : Measurable (fun x : Sizes.SeqΩ sz => (p, x)) :=
      measurable_const.prodMk measurable_id
    have hm : Measurable (fun x : Sizes.SeqΩ sz => F p x) := by
      have h := hFmeas.comp hpair
      exact h
    exact (memLp_top_of_bound hm.aestronglyMeasurable _
      (Eventually.of_forall fun x => hFbdd p x)).integrable le_top
  have hIntTarget : Integrable (fun ω : PathΩ sz => F (A + gueH sz t1 t0 K n k ω) (ω (k + 1)))
      (Pgue sz) := by
    have hm : Measurable (fun ω : PathΩ sz => F (A + gueH sz t1 t0 K n k ω) (ω (k + 1))) := by
      have h := hFmeas.comp (hYmeas'.prodMk (measurable_pi_apply (k + 1)))
      exact h
    exact (memLp_top_of_bound hm.aestronglyMeasurable _
      (Eventually.of_forall fun ω => hFbdd _ _)).integrable le_top
  have hEq : (fun ω : PathΩ sz =>
      loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (A + gueH sz t1 t0 K n (k + 1) ω)) z I)
      = fun ω => F (A + gueH sz t1 t0 K n k ω) (ω (k + 1)) := by
    funext ω
    have hH : (A + gueH sz t1 t0 K n (k + 1) ω).IsHermitian :=
      hA.add (gueH_isHermitian sz t1 t0 K n (k + 1) ω)
    have hsucc : (A + gueH sz t1 t0 K n k ω) + (Real.sqrt (gridStep t1 t0 K n) : ℂ) •
        Xmat d (sz.L n) (sz.W n) (Drift_scaledSlice sz n (ω (k + 1)))
        = A + gueH sz t1 t0 K n (k + 1) ω := by
      rw [Drift_gueH_succ' (sz := sz) t1 t0 K n k ω]
      abel
    change _ = Drift_Phi d (sz.L n) (sz.W n) z I _
    rw [hsucc]
    unfold Drift_Phi
    rw [Drift_herm_of_isHermitian hH]
  rw [hEq]
  filter_upwards [Drift_condExp_freezeC k hYmeas hFmeas hFInt hIntTarget] with ω hω
  rw [hω]
  have hp : (A + gueH sz t1 t0 K n k ω).IsHermitian := hA.add (gueH_isHermitian sz t1 t0 K n k ω)
  set f : Ω d (sz.L n) (sz.W n) → ℂ := fun y =>
    loopL d (sz.L n) (sz.W n)
      (blockMat d (sz.L n) (sz.W n) (A + gueH sz t1 t0 K n k ω
        + (Real.sqrt (gridStep t1 t0 K n) : ℂ) • Xmat d (sz.L n) (sz.W n) y)) z I with hfdef
  have hfeq : f = fun y => Φ (A + gueH sz t1 t0 K n k ω
      + (Real.sqrt (gridStep t1 t0 K n) : ℂ) • Xmat d (sz.L n) (sz.W n) y) := by
    funext y
    have hh := Drift_isHermitian_add_smul hp (Xmat_isHermitian d (sz.L n) (sz.W n) y)
      (Real.sqrt (gridStep t1 t0 K n))
    simp only [hΦdef, Drift_Phi, Drift_herm_of_isHermitian hh, hfdef]
  have hfcont : Continuous f := by
    rw [hfeq]
    have h2 : Continuous fun y : Ω d (sz.L n) (sz.W n) =>
        (Real.sqrt (gridStep t1 t0 K n) : ℂ) • Xmat d (sz.L n) (sz.W n) y :=
      (continuous_Xmat d (sz.L n) (sz.W n)).const_smul (Real.sqrt (gridStep t1 t0 K n) : ℂ)
    exact hΦcont.comp (continuous_const.add h2)
  have hFf : ∀ x, F (A + gueH sz t1 t0 K n k ω) x = f (Drift_scaledSlice sz n x) := by
    intro x
    have hh := Drift_isHermitian_add_smul hp
      (Xmat_isHermitian d (sz.L n) (sz.W n) (Drift_scaledSlice sz n x))
      (Real.sqrt (gridStep t1 t0 K n))
    simp only [hFdef, hΦdef, Drift_Phi, Drift_herm_of_isHermitian hh, hfdef]
  calc ∫ x, F (A + gueH sz t1 t0 K n k ω) x ∂(gueUnit sz)
      = ∫ x, f (Drift_scaledSlice sz n x) ∂(gueUnit sz) := by simp only [hFf]
    _ = ∫ y, f y ∂((gueUnit sz).map (Drift_scaledSlice sz n)) :=
        (integral_map (Drift_measurable_scaledSlice n).aemeasurable
          hfcont.aestronglyMeasurable).symm
    _ = ∫ y, f y ∂(gueP d (sz.L n) (sz.W n)) := by rw [Drift_map_scaledSlice]

/-- The shift `g Ψ_I` of the BA grid path is Hermitian (as in `gueHBA_isHermitian`). -/
private theorem GUEEq729BA_shift_isHermitian {d : ℕ} (sz : Sizes d) (g : ℕ → ℝ) (n : ℕ) :
    (((g n : ℝ) : ℂ) • PsiI d ((sz.withLam 0).L n) ((sz.withLam 0).W n)).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_smul, (PsiI_isHermitian d _ _).eq,
    show star ((g n : ℝ) : ℂ) = ((g n : ℝ) : ℂ) from Complex.conj_ofReal _]

/-- **The one-step conditional expectation of the BA grid path** (`condExp_loop_step_gue`): given `filt (sz.withLam 0) k`, the observable at the next grid time is the integral over one
GUE increment `√Δ X`, `X ~ gueP`, added to `gueHBA … k ω`, at the flow value `ztOf m E`. -/
theorem condExp_loop_step_gueBA {d : ℕ} (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (E : ℝ) (m : ℂ) (hm : 0 < m.im) {I : Loop.LoopIdx (Zd d (sz.L n))} (hwf : I.WF)
    (hu1 : gridTime t1 t0 K n (k + 1) < 1) :
    (Pgue (sz.withLam 0))[fun ω : PathΩ (sz.withLam 0) =>
        loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n (k + 1) ω))
          (ztOf m E (gridTime t1 t0 K n (k + 1))) I | filt (sz.withLam 0) k]
      =ᵐ[Pgue (sz.withLam 0)] fun ω =>
        ∫ x, loopL d (sz.L n) (sz.W n)
          (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k ω
            + (Real.sqrt (gridStep t1 t0 K n) : ℂ) • Xmat d (sz.L n) (sz.W n) x))
          (ztOf m E (gridTime t1 t0 K n (k + 1))) I ∂(gueP d (sz.L n) (sz.W n)) :=
  GUEEq729BA_condExp_step (sz.withLam 0) t1 t0 K n k
    (z := ztOf m E (gridTime t1 t0 K n (k + 1)))
    (by rw [ztOf_im]; exact (GUEEq729BA_eta_pos hm hu1).ne')
    (((g n : ℝ) : ℂ) • PsiI d ((sz.withLam 0).L n) ((sz.withLam 0).W n))
    (GUEEq729BA_shift_isHermitian sz g n) hwf

/-- **The conditional drift at `ztOf` on the BA grid path** (the analogue of `condExp_loop_drift_gue`,
with `0 < Im m`, `‖m‖ ≤ 1` and the envelope constant written out with `etaOf`): the one-step envelope
`oneStepEnvelopeGUEOf` applied pointwise at `M = gueHBA … k ω` (Hermitian).  The hypotheses `K n ≠ 0`,
`k < K n` are not used by the proof (as in the band). -/
theorem condExp_loop_drift_gueBA :
    ∀ {d : ℕ} (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (E : ℝ) (m : ℂ), 0 < m.im → ‖m‖ ≤ 1 →
    ∀ {I : LoopIdx (Zd d (sz.L n))}, I.WF → 0 ≤ t1 n → t1 n ≤ t0 n → K n ≠ 0 → k < K n →
      gridTime t1 t0 K n (k + 1) < 1 →
      ∀ᵐ ω ∂(Pgue (sz.withLam 0)),
        ‖(Pgue (sz.withLam 0))[fun ω' : PathΩ (sz.withLam 0) =>
              loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n)
                (gueHBA sz g t1 t0 K n (k + 1) ω'))
                (ztOf m E (gridTime t1 t0 K n (k + 1))) I | filt (sz.withLam 0) k] ω
          - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k ω))
              (ztOf m E (gridTime t1 t0 K n k)) I
          - (gridStep t1 t0 K n : ℂ) * genMatGUEOf d (sz.L n) (sz.W n) m E (gridTime t1 t0 K n k)
              (gueHBA sz g t1 t0 K n k ω) I‖
        ≤ 16 * ((I.length : ℝ) + 3) ^ 4 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) ^ 4 *
            (1 + (etaOf m (gridTime t1 t0 K n (k + 1)))⁻¹) ^ (I.length + 4) *
              gridStep t1 t0 K n ^ ((3 : ℝ) / 2) := by
  intro d sz g t1 t0 K n k E m hm hm1 I hwf ht1 ht10 _hK _hk hu1
  filter_upwards [condExp_loop_step_gueBA sz g t1 t0 K n k E m hm hwf hu1] with ω hω
  rw [hω]
  have hΔ : 0 ≤ gridStep t1 t0 K n := div_nonneg (sub_nonneg.2 ht10) (Nat.cast_nonneg _)
  have hu : gridTime t1 t0 K n (k + 1) = gridTime t1 t0 K n k + gridStep t1 t0 K n := by
    unfold gridTime
    push_cast
    ring
  have hu0 : 0 ≤ gridTime t1 t0 K n k := by
    unfold gridTime
    positivity
  have key := oneStepEnvelopeGUEOf d (sz.L n) (sz.W n) m E hm hm1 I hwf (gridTime t1 t0 K n k)
    (gridStep t1 t0 K n) hu0 hΔ (hu ▸ hu1) (gueHBA sz g t1 t0 K n k ω)
    (gueHBA_isHermitian sz g t1 t0 K n k ω)
  rw [← hu] at key
  exact key

end LoopStepBA

/-! ## 4. The loops of the BA grid path, the 2-loop algebra and Duhamel in expectation -/

section Eq729BA

variable {d : ℕ} (sz : Sizes d)

/-- The loop `L_{u_k}` of the BA grid path at grid step `k` (the analogue of `eq729F`, along
`ztOf (m n) (E n)` on `gueHBA`). -/
def eq729FBA (g t1 t0 E : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ (sz.withLam 0))
    (I : LoopIdx (Zd d (sz.L n))) : ℂ :=
  loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k ω))
    (ztOf (m n) (E n) (gridTime t1 t0 K n k)) I

/-- `e_k(I) = E L_{u_k}(I) - K̃_{u_k}(I)` at the BA grid path (the analogue of `eq729e`). -/
def eq729eBA (g t1 t0 E : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ)
    (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) (n k : ℕ) (I : LoopIdx (Zd d (sz.L n))) : ℂ :=
  (∫ ω, eq729FBA sz g t1 t0 E m K n k ω I ∂(Pgue (sz.withLam 0))) - Kt n (gridTime t1 t0 K n k) I

/-- The BA grid path is a measurable matrix-valued map. -/
private theorem GUEEq729BA_measurable_gueHBA (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) :
    Measurable (gueHBA sz g t1 t0 K n k) :=
  (GUEEq729BA_measurable_shift_filt (sz.withLam 0) t1 t0 K n k
    (((g n : ℝ) : ℂ) • PsiI d ((sz.withLam 0).L n) ((sz.withLam 0).W n))).mono
    ((filt (sz.withLam 0)).le k) le_rfl

/-- The loop at step `k` is a.e. strongly measurable (`Eq729A_loop_aesm`). -/
private theorem GUEEq729BA_loop_aesm (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (z : ℂ)
    (I : LoopIdx (Zd d (sz.L n))) :
    AEStronglyMeasurable
      (fun ω : PathΩ (sz.withLam 0) => loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n)
        (gueHBA sz g t1 t0 K n k ω)) z I) (Pgue (sz.withLam 0)) :=
  ((walk_measurable_loopL d (sz.L n) (sz.W n) z I).comp
    ((walk_measurable_blockMat d (sz.L n) (sz.W n)).comp
      (GUEEq729BA_measurable_gueHBA sz g t1 t0 K n k))).aestronglyMeasurable

/-- The crude bound on a well-formed loop of any length (`Eq729A_loop_bound_crude`). -/
private theorem GUEEq729BA_loop_bound_crude {g t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n k : ℕ} {z : ℂ}
    (hz : z.im ≠ 0) {I : LoopIdx (Zd d (sz.L n))} (hwf : I.WF) (ω : PathΩ (sz.withLam 0)) :
    ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k ω)) z I‖ ≤
      (((sz.L n * sz.W n) ^ d : ℕ) : ℝ) * (|z.im|⁻¹ * (((sz.W n : ℝ) ^ d)⁻¹)) ^ I.a.length :=
  norm_gloop_le_crude d (sz.L n) (sz.W n) ((gueHBA_isHermitian sz g t1 t0 K n k ω).submatrix _)
    (abs_pos.2 hz) le_rfl I hwf

/-- `‖𝓛_I‖ ≤ |Im z|^{-ℓ}` for a loop of length `ℓ ≥ 1` (`Eq729A_loop_bound`). -/
private theorem GUEEq729BA_loop_bound {g t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n k : ℕ} {z : ℂ}
    (hz : z.im ≠ 0) {I : LoopIdx (Zd d (sz.L n))} (hwf : I.WF) (hn : 1 ≤ I.a.length)
    (ω : PathΩ (sz.withLam 0)) :
    ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k ω)) z I‖ ≤
      (|z.im|)⁻¹ ^ I.a.length := by
  have hH : (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k ω)).IsHermitian :=
    (gueHBA_isHermitian sz g t1 t0 K n k ω).submatrix _
  have h := RBM.Ind.norm_gloop_le_of_le_abs_im (L := sz.L n) (W := sz.W n) hH (abs_pos.2 hz)
    le_rfl I hwf hn
  refine h.trans ?_
  have hW : ((sz.W n : ℝ) ^ d)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast sz.W_pos n))
  have hW0 : 0 ≤ ((sz.W n : ℝ) ^ d)⁻¹ := by positivity
  calc |z.im|⁻¹ ^ I.a.length * (((sz.W n : ℝ) ^ d)⁻¹) ^ (I.a.length - 1)
      ≤ |z.im|⁻¹ ^ I.a.length * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hW0 hW) (by positivity)
    _ = _ := mul_one _

/-- The loop at step `k` is bounded and measurable (any well-formed loop) (`Eq729A_loop_BM`). -/
private theorem GUEEq729BA_loop_BM {g t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n k : ℕ} {z : ℂ} (hz : z.im ≠ 0)
    {I : LoopIdx (Zd d (sz.L n))} (hwf : I.WF) :
    Eq729A_BM (Pgue (sz.withLam 0)) (fun ω : PathΩ (sz.withLam 0) =>
      loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k ω)) z I) :=
  ⟨GUEEq729BA_loop_aesm sz g t1 t0 K n k z I, _, GUEEq729BA_loop_bound_crude sz hz hwf⟩

end Eq729BA

section Eq729BA2

/-- **The `𝓔^{(G̃)}` term on a 2-loop**, written with 1-loops and 3-loops (the analogue of `eq729_eG2`,
for `egtNGUEOf`: the Green sign value is `mSigOf m`, the flow `ztOf m E`). -/
theorem eq729_eG2BA (d L W : ℕ) [NeZero L] [NeZero W] (m : ℂ) (E u : ℝ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (s1 s2 : Bool) (a1 a2 : Zd d L) :
    egtNGUEOf d L W m E u M ⟨[s1, s2], [a1, a2]⟩ =
      (W : ℂ) ^ d * ∑ a : Zd d L, ∑ b : Zd d L,
        ((loopL d L W (blockMat d L W M) (ztOf m E u) ⟨[s1], [a]⟩ - mSigOf m s1) * SBgue d L a b *
            loopL d L W (blockMat d L W M) (ztOf m E u) ⟨[s1, s1, s2], [b, a1, a2]⟩ +
          (loopL d L W (blockMat d L W M) (ztOf m E u) ⟨[s2], [a]⟩ - mSigOf m s2) * SBgue d L a b *
            loopL d L W (blockMat d L W M) (ztOf m E u) ⟨[s1, s2, s2], [a1, b, a2]⟩) := by
  unfold egtNGUEOf
  have h1 : Finset.Icc 1 (LoopIdx.length (⟨[s1, s2], [a1, a2]⟩ : LoopIdx (Zd d L))) = {1, 2} := by
    rfl
  rw [h1, Finset.sum_insert (by decide), Finset.sum_singleton]
  have e1 : (⟨[s1, s2], [a1, a2]⟩ : LoopIdx (Zd d L)).σ.getD (1 - 1) false = s1 := rfl
  have e2 : (⟨[s1, s2], [a1, a2]⟩ : LoopIdx (Zd d L)).σ.getD (2 - 1) false = s2 := rfl
  have c1 : ∀ b : Zd d L, (⟨[s1, s2], [a1, a2]⟩ : LoopIdx (Zd d L)).cutGlue 1 b
      = ⟨[s1, s1, s2], [b, a1, a2]⟩ := fun b => rfl
  have c2 : ∀ b : Zd d L, (⟨[s1, s2], [a1, a2]⟩ : LoopIdx (Zd d L)).cutGlue 2 b
      = ⟨[s1, s2, s2], [a1, b, a2]⟩ := fun b => rfl
  have tr : ∀ (σ : Bool) (a : Zd d L), Matrix.trace (Gres (blockMat d L W M) (ztOf m E u) σ *
      Eblk d L W a) = loopL d L W (blockMat d L W M) (ztOf m E u) ⟨[σ], [a]⟩ := fun σ a => by
    simp [loopL]
  simp only [e1, e2, c1, c2, tr]
  rw [← Finset.sum_add_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
  rw [← Finset.sum_add_distrib]

/-- The generator on a 2-loop (`loopGenGUEOf` at `k = 2`, in list form; `Eq729A_genMat_two`). -/
private theorem GUEEq729BA_genMat_two (d L W : ℕ) [NeZero L] [NeZero W] {m : ℂ} (hm : 0 < m.im) {E u : ℝ}
    (hu1 : u < 1) {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) (s1 s2 : Bool)
    (a1 a2 : Zd d L) :
    genMatGUEOf d L W m E u M ⟨[s1, s2], [a1, a2]⟩ =
      primRhsGUE d L W (loopL d L W (blockMat d L W M) (ztOf m E u)) ⟨[s1, s2], [a1, a2]⟩ +
        egtNGUEOf d L W m E u M ⟨[s1, s2], [a1, a2]⟩ :=
  loopGenGUEOf d L W m hm E u hu1 M hM 2 ![s1, s2] ![a1, a2]

end Eq729BA2

section Eq729BA3

variable {d : ℕ} (sz : Sizes d)

/-- **Duhamel in expectation** (the analogue of `eq729_duhamel`; `condExp_loop_drift_gueBA` integrated): the
martingale part has mean `0`; the loops are deterministically bounded, so every term is integrable. -/
theorem eq729_duhamelBA {g t1 t0 : ℕ → ℝ} (K : ℕ → ℕ) {E : ℕ → ℝ} {m : ℕ → ℂ} {n : ℕ}
    (hm : 0 < (m n).im) (hm1 : ‖m n‖ ≤ 1) (ht1 : 0 ≤ t1 n) (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1) {k : ℕ}
    (hk : k < K n) {J : LoopIdx (Zd d (sz.L n))} (hwf : J.WF)
    (hdrift : Integrable (fun ω => genMatGUEOf d (sz.L n) (sz.W n) (m n) (E n) (gridTime t1 t0 K n k)
      (gueHBA sz g t1 t0 K n k ω) J) (Pgue (sz.withLam 0))) :
    ‖(∫ ω, eq729FBA sz g t1 t0 E m K n (k + 1) ω J ∂(Pgue (sz.withLam 0))) -
        (∫ ω, eq729FBA sz g t1 t0 E m K n k ω J ∂(Pgue (sz.withLam 0))) -
        (gridStep t1 t0 K n : ℂ) * ∫ ω, genMatGUEOf d (sz.L n) (sz.W n) (m n) (E n)
          (gridTime t1 t0 K n k) (gueHBA sz g t1 t0 K n k ω) J ∂(Pgue (sz.withLam 0))‖
      ≤ 16 * ((J.length : ℝ) + 3) ^ 4 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) ^ 4 *
          (1 + (etaOf (m n) (gridTime t1 t0 K n (k + 1)))⁻¹) ^ (J.length + 4) *
            gridStep t1 t0 K n ^ ((3 : ℝ) / 2) := by
  have hKn : K n ≠ 0 := by omega
  have hu : ∀ j, j ≤ K n → gridTime t1 t0 K n j < 1 := fun j hj =>
    lt_of_le_of_lt (eq729_time_mem ht10 hKn hj).2 ht0
  have hz : ∀ j, j ≤ K n → (ztOf (m n) (E n) (gridTime t1 t0 K n j)).im ≠ 0 := fun j hj => by
    rw [ztOf_im]; exact (GUEEq729BA_eta_pos hm (hu j hj)).ne'
  have h := condExp_loop_drift_gueBA sz g t1 t0 K n k (E n) (m n) hm hm1 hwf ht1 ht10 hKn hk
    (hu (k + 1) hk)
  set f' : PathΩ (sz.withLam 0) → ℂ := fun ω' => eq729FBA sz g t1 t0 E m K n (k + 1) ω' J with hf'
  set f : PathΩ (sz.withLam 0) → ℂ := fun ω' => eq729FBA sz g t1 t0 E m K n k ω' J with hf
  have hf'i : Integrable f' (Pgue (sz.withLam 0)) := Eq729A_BM.integrable (GUEEq729BA_loop_BM sz (hz (k + 1) hk) hwf)
  have hfi : Integrable f (Pgue (sz.withLam 0)) := Eq729A_BM.integrable (GUEEq729BA_loop_BM sz (hz k hk.le) hwf)
  have hbound := norm_integral_le_of_norm_le_const h
  rw [probReal_univ, mul_one] at hbound
  set ce : PathΩ (sz.withLam 0) → ℂ := (Pgue (sz.withLam 0))[f' | filt (sz.withLam 0) k] with hce_def
  have hce : Integrable ce (Pgue (sz.withLam 0)) := integrable_condExp
  have hid : (∫ x, (ce x - f x - (gridStep t1 t0 K n : ℂ) *
        genMatGUEOf d (sz.L n) (sz.W n) (m n) (E n) (gridTime t1 t0 K n k) (gueHBA sz g t1 t0 K n k x) J)
        ∂(Pgue (sz.withLam 0)))
      = (∫ x, f' x ∂(Pgue (sz.withLam 0))) - (∫ x, f x ∂(Pgue (sz.withLam 0))) -
        (gridStep t1 t0 K n : ℂ) *
        ∫ ω, genMatGUEOf d (sz.L n) (sz.W n) (m n) (E n) (gridTime t1 t0 K n k)
          (gueHBA sz g t1 t0 K n k ω) J ∂(Pgue (sz.withLam 0)) := by
    rw [integral_sub, integral_sub, integral_const_mul, hce_def,
      integral_condExp ((filt (sz.withLam 0)).le k)]
    · exact hce
    · exact hfi
    · exact hce.sub hfi
    · exact hdrift.const_mul _
  refine (le_of_eq ?_).trans hbound
  exact congrArg norm hid.symm

/-- The `𝓔^{(G̃)}` part of the drift of a 2-loop is bounded and measurable (`Eq729A_BM_eG`). -/
private theorem GUEEq729BA_BM_eG {g t1 t0 : ℕ → ℝ} {E : ℕ → ℝ} {m : ℕ → ℂ} (K : ℕ → ℕ) {n k : ℕ}
    (hz : (ztOf (m n) (E n) (gridTime t1 t0 K n k)).im ≠ 0) (s1 s2 : Bool) (a1 a2 : Zd d (sz.L n)) :
    Eq729A_BM (Pgue (sz.withLam 0)) (fun ω => egtNGUEOf d (sz.L n) (sz.W n) (m n) (E n)
      (gridTime t1 t0 K n k) (gueHBA sz g t1 t0 K n k ω) ⟨[s1, s2], [a1, a2]⟩) := by
  have hFBM : ∀ I : LoopIdx (Zd d (sz.L n)), I.WF →
      Eq729A_BM (Pgue (sz.withLam 0)) (fun ω => eq729FBA sz g t1 t0 E m K n k ω I) :=
    fun I h => GUEEq729BA_loop_BM sz hz h
  simp_rw [eq729_eG2BA]
  refine Eq729A_BM.mul (Eq729A_BM_const _) (Eq729A_BM.sum _ fun a _ => Eq729A_BM.sum _ fun b _ => ?_)
  exact Eq729A_BM.add
    (Eq729A_BM.mul (Eq729A_BM.mul (Eq729A_BM.sub (hFBM ⟨[s1], [a]⟩ rfl) (Eq729A_BM_const _))
      (Eq729A_BM_const _)) (hFBM ⟨[s1, s1, s2], [b, a1, a2]⟩ rfl))
    (Eq729A_BM.mul (Eq729A_BM.mul (Eq729A_BM.sub (hFBM ⟨[s2], [a]⟩ rfl) (Eq729A_BM_const _))
      (Eq729A_BM_const _)) (hFBM ⟨[s1, s2, s2], [a1, b, a2]⟩ rfl))

/-- The `primRhsGUE` part of the drift of a 2-loop is bounded and measurable (`Eq729A_BM_prim`). -/
private theorem GUEEq729BA_BM_prim {g t1 t0 : ℕ → ℝ} {E : ℕ → ℝ} {m : ℕ → ℂ} (K : ℕ → ℕ) {n k : ℕ}
    (hz : (ztOf (m n) (E n) (gridTime t1 t0 K n k)).im ≠ 0) (s1 s2 : Bool) (a1 a2 : Zd d (sz.L n)) :
    Eq729A_BM (Pgue (sz.withLam 0)) (fun ω => primRhsGUE d (sz.L n) (sz.W n)
      (eq729FBA sz g t1 t0 E m K n k ω) ⟨[s1, s2], [a1, a2]⟩) := by
  have hFBM : ∀ I : LoopIdx (Zd d (sz.L n)), I.WF →
      Eq729A_BM (Pgue (sz.withLam 0)) (fun ω => eq729FBA sz g t1 t0 E m K n k ω I) :=
    fun I h => GUEEq729BA_loop_BM sz hz h
  simp_rw [primRhsGUE, eq729_primBil2]
  exact Eq729A_BM.mul (Eq729A_BM_const _) (Eq729A_BM.sum _ fun a _ => Eq729A_BM.sum _ fun b _ =>
    Eq729A_BM.mul (Eq729A_BM.mul (hFBM ⟨[s1, s2], [a, a2]⟩ rfl) (Eq729A_BM_const _))
      (hFBM ⟨[s1, s2], [a1, b]⟩ rfl))

end Eq729BA3

/-! ## 5. One step of the recursion for `e_k` -/

section Eq729BA4

/-- **One step of the recursion for `e_k = E L_{u_k} - K̃_{u_k}` on 2-loops at the BA grid path** (the analogue of
`eq729_one_step`: the flow `ztOf (m n) (E n)`, `etaOf`, the
value `m n`, the sign value `mSigOf`, the hypothesis `0 < Im (m n)`, `‖m n‖ ≤ 1`, the path `gueHBA sz g`, the
carrier `PathΩ (sz.withLam 0)`).  The `let` bodies `F`, `e` of the statement are written out; they are
`eq729FBA`, `eq729eBA` (`rfl`); `N = sz.size n = (W L)^d`.  The hypotheses
`hX`, `hB`, `hg1`–`hg3`, `hBk` are the stochastic inputs of the second half (the one-loop expectation along the grid and the
block Anderson version of `gueGrid_eq729`); `Kt` stays a parameter. -/
theorem eq729_one_stepBA :
    ∀ {d : ℕ} (sz : Sizes d) (g t1 t0 E : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ) (n : ℕ)
      (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ),
      let F : ℕ → PathΩ (sz.withLam 0) → LoopIdx (Zd d (sz.L n)) → ℂ := fun k ω I =>
        loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k ω))
          (ztOf (m n) (E n) (gridTime t1 t0 K n k)) I
      let e : ℕ → LoopIdx (Zd d (sz.L n)) → ℂ := fun k I =>
        (∫ ω, F k ω I ∂(Pgue (sz.withLam 0))) - Kt n (gridTime t1 t0 K n k) I
      0 < (m n).im → ‖m n‖ ≤ 1 → 0 ≤ t1 n → t1 n ≤ t0 n → t0 n < 1 →
      ∀ {Λ ρ p Bk : ℝ}, Λ = (((sz.size n : ℕ) : ℝ) * etaOf (m n) (t0 n))⁻¹ → Λ ≤ 1 → 0 ≤ ρ →
      ρ * Λ ≤ 1 → 0 ≤ p →
      ((sz.size n : ℕ) : ℝ) * gridStep t1 t0 K n ≤ 1 →
      (∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 x y, ‖Kt n s ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ) →
      (∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 s3 x y w, ‖Kt n s ⟨[s1, s2, s3], [x, y, w]⟩‖ ≤ ρ * Λ ^ 2) →
      (∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 x y, HasDerivWithinAt (fun s => Kt n s ⟨[s1, s2], [x, y]⟩)
        (primRhsGUE d (sz.L n) (sz.W n) (Kt n s) ⟨[s1, s2], [x, y]⟩) (Set.Icc (t1 n) (t0 n)) s) →
      ∀ {k : ℕ}, k < K n →
      (∀ a, ‖(∫ ω, F k ω ⟨[true], [a]⟩ ∂(Pgue (sz.withLam 0))) - m n‖ ≤ ρ * Λ ^ 2) →
      ∀ {B : Set (PathΩ (sz.withLam 0))}, Pgue (sz.withLam 0) B ≤ ENNReal.ofReal p →
      (∀ ω ∉ B, ∀ σ a, ‖F k ω ⟨[σ], [a]⟩ - mSigOf (m n) σ‖ ≤ ρ * Λ) →
      (∀ ω ∉ B, ∀ s1 s2 x y,
        ‖F k ω ⟨[s1, s2], [x, y]⟩ - Kt n (gridTime t1 t0 K n k) ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ ^ 2) →
      (∀ ω ∉ B, ∀ s1 s2 s3 x y w,
        ‖F k ω ⟨[s1, s2, s3], [x, y, w]⟩ - Kt n (gridTime t1 t0 K n k) ⟨[s1, s2, s3], [x, y, w]⟩‖ ≤
          ρ * Λ ^ 3) →
      (∀ s1 s2 x y, ‖e k ⟨[s1, s2], [x, y]⟩‖ ≤ Bk) →
      ∀ (s1 s2 : Bool) (a1 a2 : Zd d (sz.L n)),
        ‖e (k + 1) ⟨[s1, s2], [a1, a2]⟩‖ ≤
          (1 + gridStep t1 t0 K n * (2 * ((sz.size n : ℕ) : ℝ) * (ρ * Λ))) * Bk +
            eq729c ((sz.size n : ℕ) : ℝ) ρ Λ p (gridStep t1 t0 K n) := by
  intro d sz g t1 t0 E m K n Kt F0 e0 hm hm1 ht1 ht10 ht0 Λ ρ p Bk hΛ hΛ1 hρ0 hρΛ hp0 hMΔ hK2b hK3b hKd k hk
    hX B hB hg1 hg2 hg3 hBk s1 s2 a1 a2
  have hF0 : F0 = eq729FBA sz g t1 t0 E m K n := rfl
  have he0 : e0 = eq729eBA sz g t1 t0 E m K Kt n := rfl
  clear_value F0 e0
  subst hF0 he0
  classical
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  set Δ : ℝ := gridStep t1 t0 K n with hΔ
  set u : ℝ := gridTime t1 t0 K n k with hu_def
  set z : ℂ := ztOf (m n) (E n) u with hz_def
  set J : LoopIdx (Zd d (sz.L n)) := ⟨[s1, s2], [a1, a2]⟩ with hJ
  have hKN : K n ≠ 0 := by omega
  have hΔ0 : 0 ≤ Δ := eq729_step_nonneg ht10
  have hu : u ∈ Set.Icc (t1 n) (t0 n) := eq729_time_mem ht10 hKN hk.le
  have hu' : u + Δ ∈ Set.Icc (t1 n) (t0 n) := by
    rw [hu_def, hΔ, ← Eq729A_time_succ]; exact eq729_time_mem ht10 hKN hk
  have hM1 : 1 ≤ N := by
    have hpos : 0 < sz.size n := by
      unfold Sizes.size
      exact pow_pos (Nat.mul_pos (sz.W_pos n) (by have := sz.three_le_L n; omega)) d
    rw [hN]; exact_mod_cast hpos
  have hM0 : 0 ≤ N := by linarith
  -- the scale: `η_u⁻¹ ≤ N` on `[t₁, t₀]`
  have hη0 : 0 < etaOf (m n) (t0 n) := GUEEq729BA_eta_pos hm ht0
  have hΛpos : 0 < Λ := by rw [hΛ]; positivity
  have hΛ0 : 0 ≤ Λ := hΛpos.le
  have hηM : ∀ r ∈ Set.Icc (t1 n) (t0 n), |(ztOf (m n) (E n) r).im|⁻¹ ≤ N := by
    intro r hr
    rw [ztOf_im]
    have hr1 : etaOf (m n) (t0 n) ≤ etaOf (m n) r := GUEEq729BA_eta_le hm hr.2
    rw [abs_of_pos (hη0.trans_le hr1)]
    have hMη : 1 ≤ N * etaOf (m n) (t0 n) := by
      have : (N * etaOf (m n) (t0 n))⁻¹ ≤ 1 := by rw [← hΛ]; exact hΛ1
      have hpos : 0 < N * etaOf (m n) (t0 n) := by positivity
      rwa [inv_le_one₀ hpos] at this
    rw [inv_le_iff_one_le_mul₀ (hη0.trans_le hr1)]
    nlinarith
  have hzne : z.im ≠ 0 := by
    rw [hz_def, ztOf_im]; exact (GUEEq729BA_eta_pos hm (lt_of_le_of_lt hu.2 ht0)).ne'
  have hηz : |z.im|⁻¹ ≤ N := hηM u hu
  -- loops at step `k`: bounded and measurable
  have hFBM : ∀ I : LoopIdx (Zd d (sz.L n)), I.WF →
      Eq729A_BM (Pgue (sz.withLam 0)) (fun ω => eq729FBA sz g t1 t0 E m K n k ω I) := fun I h1 =>
    GUEEq729BA_loop_BM sz hzne h1
  have hFb : ∀ I : LoopIdx (Zd d (sz.L n)), I.WF → 1 ≤ I.a.length → ∀ ω,
      ‖eq729FBA sz g t1 t0 E m K n k ω I‖ ≤ N ^ I.a.length := fun I h1 h2 ω =>
    (GUEEq729BA_loop_bound sz hzne h1 h2 ω).trans (pow_le_pow_left₀ (by positivity) hηz _)
  have hFBM1 : ∀ σ a, Eq729A_BM (Pgue (sz.withLam 0))
      (fun ω => eq729FBA sz g t1 t0 E m K n k ω ⟨[σ], [a]⟩) := fun σ a => hFBM _ rfl
  have hFBM2 : ∀ σ₁ σ₂ x y, Eq729A_BM (Pgue (sz.withLam 0))
      (fun ω => eq729FBA sz g t1 t0 E m K n k ω ⟨[σ₁, σ₂], [x, y]⟩) :=
    fun σ₁ σ₂ x y => hFBM _ rfl
  have hFBM3 : ∀ σ₁ σ₂ σ₃ x y w, Eq729A_BM (Pgue (sz.withLam 0))
      (fun ω => eq729FBA sz g t1 t0 E m K n k ω ⟨[σ₁, σ₂, σ₃], [x, y, w]⟩) :=
    fun σ₁ σ₂ σ₃ x y w => hFBM _ rfl
  set Kk : LoopIdx (Zd d (sz.L n)) → ℂ := Kt n u with hKk
  set F : PathΩ (sz.withLam 0) → LoopIdx (Zd d (sz.L n)) → ℂ :=
    fun ω I => eq729FBA sz g t1 t0 E m K n k ω I with hF
  set e : LoopIdx (Zd d (sz.L n)) → ℂ := eq729eBA sz g t1 t0 E m K Kt n k with he
  -- the drift, pointwise
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 ht0
  have hdrift_eq : ∀ ω, genMatGUEOf d (sz.L n) (sz.W n) (m n) (E n) u (gueHBA sz g t1 t0 K n k ω) J
      = primRhsGUE d (sz.L n) (sz.W n) (F ω) J
        + egtNGUEOf d (sz.L n) (sz.W n) (m n) (E n) u (gueHBA sz g t1 t0 K n k ω) J := fun ω =>
    GUEEq729BA_genMat_two d (sz.L n) (sz.W n) hm hu1 (gueHBA_isHermitian sz g t1 t0 K n k ω)
      s1 s2 a1 a2
  have heG_eq : ∀ ω, egtNGUEOf d (sz.L n) (sz.W n) (m n) (E n) u (gueHBA sz g t1 t0 K n k ω) J
      = (sz.W n : ℂ) ^ d * ∑ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n),
        ((F ω ⟨[s1], [a]⟩ - mSigOf (m n) s1) * SBgue d (sz.L n) a b *
            F ω ⟨[s1, s1, s2], [b, a1, a2]⟩ +
          (F ω ⟨[s2], [a]⟩ - mSigOf (m n) s2) * SBgue d (sz.L n) a b *
            F ω ⟨[s1, s2, s2], [a1, b, a2]⟩) := fun ω =>
    eq729_eG2BA d (sz.L n) (sz.W n) (m n) (E n) u (gueHBA sz g t1 t0 K n k ω) s1 s2 a1 a2
  have hBMeG : Eq729A_BM (Pgue (sz.withLam 0))
      (fun ω => egtNGUEOf d (sz.L n) (sz.W n) (m n) (E n) u (gueHBA sz g t1 t0 K n k ω) J) :=
    GUEEq729BA_BM_eG sz K hzne s1 s2 a1 a2
  have hBMprim : Eq729A_BM (Pgue (sz.withLam 0)) (fun ω => primRhsGUE d (sz.L n) (sz.W n) (F ω) J) :=
    GUEEq729BA_BM_prim sz K hzne s1 s2 a1 a2
  have hdrift_int : Integrable (fun ω => genMatGUEOf d (sz.L n) (sz.W n) (m n) (E n) u
      (gueHBA sz g t1 t0 K n k ω) J) (Pgue (sz.withLam 0)) := by
    simp_rw [hdrift_eq]; exact Eq729A_BM.integrable (Eq729A_BM.add hBMprim hBMeG)
  -- Duhamel in expectation
  have hR1 := eq729_duhamelBA sz K hm hm1 ht1 ht10 ht0 hk (J := J) rfl hdrift_int
  -- the primitive side
  have hR2 := eq729_Kdisc (d := d) (L := sz.L n) (W := sz.W n) (Kt n) hu hu' hΔ0 hρΛ hMΔ hK2b hKd
    s1 s2 a1 a2
  have htime : gridTime t1 t0 K n (k + 1) = u + Δ := Eq729A_time_succ t1 t0 K n k
  -- split of the drift in expectation
  set D : PathΩ (sz.withLam 0) → LoopIdx (Zd d (sz.L n)) → ℂ := fun ω => F ω - Kk with hD
  have hDBM2 : ∀ x y, Eq729A_BM (Pgue (sz.withLam 0)) (fun ω => D ω ⟨[s1, s2], [x, y]⟩) := fun x y =>
    Eq729A_BM.sub (hFBM2 s1 s2 x y) (Eq729A_BM_const _)
  have hDint : ∀ x y, ∫ ω, D ω ⟨[s1, s2], [x, y]⟩ ∂(Pgue (sz.withLam 0)) = e ⟨[s1, s2], [x, y]⟩ := by
    intro x y
    simp only [hD, Pi.sub_apply]
    rw [integral_sub (Eq729A_BM.integrable (hFBM2 s1 s2 x y)) (integrable_const _), integral_const,
      probReal_univ, one_smul]
    rfl
  have hprim_split : ∀ ω, primRhsGUE d (sz.L n) (sz.W n) (F ω) J
      = primRhsGUE d (sz.L n) (sz.W n) Kk J
        + primBilGUE d (sz.L n) (sz.W n) Kk (D ω) J
        + primBilGUE d (sz.L n) (sz.W n) (D ω) Kk J
        + primBilGUE d (sz.L n) (sz.W n) (D ω) (D ω) J := by
    intro ω
    have := primRhsGUE_sub d (sz.L n) (sz.W n) (F ω) Kk J
    simp only [hD]
    linear_combination this
  have hBMbilL : Eq729A_BM (Pgue (sz.withLam 0))
      (fun ω => primBilGUE d (sz.L n) (sz.W n) Kk (D ω) J) := by
    simp_rw [hJ, eq729_primBil2]
    exact Eq729A_BM.mul (Eq729A_BM_const _) (Eq729A_BM.sum _ fun a _ => Eq729A_BM.sum _ fun b _ =>
      Eq729A_BM.mul (Eq729A_BM.mul (Eq729A_BM_const _) (Eq729A_BM_const _)) (hDBM2 a1 b))
  have hBMbilR : Eq729A_BM (Pgue (sz.withLam 0))
      (fun ω => primBilGUE d (sz.L n) (sz.W n) (D ω) Kk J) := by
    simp_rw [hJ, eq729_primBil2]
    exact Eq729A_BM.mul (Eq729A_BM_const _) (Eq729A_BM.sum _ fun a _ => Eq729A_BM.sum _ fun b _ =>
      Eq729A_BM.mul (Eq729A_BM.mul (hDBM2 a a2) (Eq729A_BM_const _)) (Eq729A_BM_const _))
  have hBMbilQ : Eq729A_BM (Pgue (sz.withLam 0))
      (fun ω => primBilGUE d (sz.L n) (sz.W n) (D ω) (D ω) J) := by
    simp_rw [hJ, eq729_primBil2]
    exact Eq729A_BM.mul (Eq729A_BM_const _) (Eq729A_BM.sum _ fun a _ => Eq729A_BM.sum _ fun b _ =>
      Eq729A_BM.mul (Eq729A_BM.mul (hDBM2 a a2) (Eq729A_BM_const _)) (hDBM2 a1 b))
  have hprim_int : ∫ ω, primRhsGUE d (sz.L n) (sz.W n) (F ω) J ∂(Pgue (sz.withLam 0))
      = primRhsGUE d (sz.L n) (sz.W n) Kk J
        + primBilGUE d (sz.L n) (sz.W n) Kk e J
        + primBilGUE d (sz.L n) (sz.W n) e Kk J
        + ∫ ω, primBilGUE d (sz.L n) (sz.W n) (D ω) (D ω) J ∂(Pgue (sz.withLam 0)) := by
    simp_rw [hprim_split]
    have i1 : Integrable (fun ω => primRhsGUE d (sz.L n) (sz.W n) Kk J
        + primBilGUE d (sz.L n) (sz.W n) Kk (D ω) J) (Pgue (sz.withLam 0)) :=
      (integrable_const _).add (Eq729A_BM.integrable hBMbilL)
    have i2 : Integrable (fun ω => primRhsGUE d (sz.L n) (sz.W n) Kk J
        + primBilGUE d (sz.L n) (sz.W n) Kk (D ω) J
        + primBilGUE d (sz.L n) (sz.W n) (D ω) Kk J) (Pgue (sz.withLam 0)) :=
      i1.add (Eq729A_BM.integrable hBMbilR)
    rw [integral_add i2 (Eq729A_BM.integrable hBMbilQ), integral_add i1 (Eq729A_BM.integrable hBMbilR),
      integral_add (integrable_const _) (Eq729A_BM.integrable hBMbilL), integral_const, probReal_univ,
      one_smul,
      Eq729A_integral_primBil_left (d := d) (sz.W n) Kk D e s1 s2 a1 a2
        (fun y => Eq729A_BM.integrable (hDBM2 a1 y)) (fun y => hDint a1 y),
      Eq729A_integral_primBil_right (d := d) (sz.W n) Kk D e s1 s2 a1 a2
        (fun x => Eq729A_BM.integrable (hDBM2 x a2)) (fun x => hDint x a2)]
  have hdrift_int_eq : ∫ ω, genMatGUEOf d (sz.L n) (sz.W n) (m n) (E n) u
        (gueHBA sz g t1 t0 K n k ω) J ∂(Pgue (sz.withLam 0))
      = (∫ ω, primRhsGUE d (sz.L n) (sz.W n) (F ω) J ∂(Pgue (sz.withLam 0)))
        + ∫ ω, egtNGUEOf d (sz.L n) (sz.W n) (m n) (E n) u (gueHBA sz g t1 t0 K n k ω) J
          ∂(Pgue (sz.withLam 0)) := by
    simp_rw [hdrift_eq]
    exact integral_add (Eq729A_BM.integrable hBMprim) (Eq729A_BM.integrable hBMeG)
  -- the exact identity
  set R1 : ℂ := (∫ ω, eq729FBA sz g t1 t0 E m K n (k + 1) ω J ∂(Pgue (sz.withLam 0)))
      - (∫ ω, eq729FBA sz g t1 t0 E m K n k ω J ∂(Pgue (sz.withLam 0)))
      - (Δ : ℂ) * ∫ ω, genMatGUEOf d (sz.L n) (sz.W n) (m n) (E n) u (gueHBA sz g t1 t0 K n k ω) J
        ∂(Pgue (sz.withLam 0))
    with hR1def
  set R2 : ℂ := Kk J + (Δ : ℂ) * primRhsGUE d (sz.L n) (sz.W n) Kk J - Kt n (u + Δ) J
    with hR2def
  set IeG : ℂ := ∫ ω, egtNGUEOf d (sz.L n) (sz.W n) (m n) (E n) u (gueHBA sz g t1 t0 K n k ω) J
    ∂(Pgue (sz.withLam 0)) with hIeG
  set IQ : ℂ := ∫ ω, primBilGUE d (sz.L n) (sz.W n) (D ω) (D ω) J ∂(Pgue (sz.withLam 0)) with hIQ
  set lin : ℂ := primBilGUE d (sz.L n) (sz.W n) Kk e J
    + primBilGUE d (sz.L n) (sz.W n) e Kk J with hlin
  have hident : eq729eBA sz g t1 t0 E m K Kt n (k + 1) J
      = (e J + (Δ : ℂ) * lin) + (Δ : ℂ) * IQ + (Δ : ℂ) * IeG + R1 + R2 := by
    have h1 : eq729eBA sz g t1 t0 E m K Kt n (k + 1) J
        = (∫ ω, eq729FBA sz g t1 t0 E m K n (k + 1) ω J ∂(Pgue (sz.withLam 0))) - Kt n (u + Δ) J := by
      rw [eq729eBA, htime]
    have h2 : e J = (∫ ω, eq729FBA sz g t1 t0 E m K n k ω J ∂(Pgue (sz.withLam 0))) - Kk J := rfl
    rw [h1, h2, hR1def, hR2def, hdrift_int_eq, hprim_int]
    ring
  -- bounds
  have hΔn : ‖(Δ : ℂ)‖ = Δ := by rw [Complex.norm_real, Real.norm_of_nonneg hΔ0]
  have hlinb : ‖lin‖ ≤ 2 * N * (ρ * Λ) * Bk := by
    have e1 := eq729_norm_primBil2_le d (sz.L n) (sz.W n) Kk e s1 s2 a1 a2
      (fun x => hK2b u hu s1 s2 x a2) (fun y => hBk s1 s2 a1 y)
    have e2 := eq729_norm_primBil2_le d (sz.L n) (sz.W n) e Kk s1 s2 a1 a2
      (fun x => hBk s1 s2 x a2) (fun y => hK2b u hu s1 s2 a1 y)
    calc ‖lin‖ ≤ _ + _ := norm_add_le _ _
      _ ≤ N * (ρ * Λ) * Bk + N * Bk * (ρ * Λ) := add_le_add e1 e2
      _ = 2 * N * (ρ * Λ) * Bk := by ring
  have hBk0 : 0 ≤ Bk := (norm_nonneg _).trans (hBk s1 s2 a1 a2)
  have hlead : ‖e J + (Δ : ℂ) * lin‖ ≤ (1 + Δ * (2 * N * (ρ * Λ))) * Bk := by
    calc ‖e J + (Δ : ℂ) * lin‖ ≤ ‖e J‖ + Δ * ‖lin‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul, hΔn]
      _ ≤ Bk + Δ * (2 * N * (ρ * Λ) * Bk) :=
          add_le_add (hBk s1 s2 a1 a2) (mul_le_mul_of_nonneg_left hlinb hΔ0)
      _ = (1 + Δ * (2 * N * (ρ * Λ))) * Bk := by ring
  -- the quadratic term
  have hρΛ2 : ρ * Λ ^ 2 ≤ 1 := by
    calc ρ * Λ ^ 2 = (ρ * Λ) * Λ := by ring
      _ ≤ 1 * 1 := mul_le_mul hρΛ hΛ1 hΛ0 zero_le_one
      _ = 1 := by ring
  have hQ : ‖IQ‖ ≤ N * ((ρ * Λ ^ 2) * (ρ * Λ ^ 2) + (2 * N ^ 2) * (2 * N ^ 2) * p) := by
    have := Eq729A_quad (μ := Pgue (sz.withLam 0)) (sz.W n) D s1 s2 a1 a2 hDBM2 (g := ρ * Λ ^ 2)
      (C := 2 * N ^ 2) (by positivity) (by positivity) hB hp0
      (fun ω hω x y => hg2 ω hω s1 s2 x y)
      (fun ω x y => by
        simp only [hD, Pi.sub_apply]
        refine (norm_sub_le _ _).trans ?_
        have h1 : ‖F ω ⟨[s1, s2], [x, y]⟩‖ ≤ N ^ 2 := hFb ⟨[s1, s2], [x, y]⟩ rfl (by simp) ω
        have h2 : ‖Kk ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ := hK2b u hu s1 s2 x y
        have : N ^ 2 ≥ 1 := one_le_pow₀ hM1
        nlinarith)
    exact this
  -- the 1-loop input
  have hXall : ∀ σ a, ‖∫ ω, (F ω ⟨[σ], [a]⟩ - mSigOf (m n) σ) ∂(Pgue (sz.withLam 0))‖ ≤ ρ * Λ ^ 2 := by
    intro σ a
    have htrue : ∫ ω, (F ω ⟨[true], [a]⟩ - mSigOf (m n) true) ∂(Pgue (sz.withLam 0))
        = (∫ ω, eq729FBA sz g t1 t0 E m K n k ω ⟨[true], [a]⟩ ∂(Pgue (sz.withLam 0))) - m n := by
      rw [integral_sub (Eq729A_BM.integrable (hFBM1 true a)) (integrable_const _), integral_const,
        probReal_univ, one_smul]
      rfl
    cases σ with
    | true => rw [htrue]; exact hX a
    | false =>
      have hconj : (fun ω => F ω ⟨[false], [a]⟩ - mSigOf (m n) false)
          = fun ω => (starRingEnd ℂ) (F ω ⟨[true], [a]⟩ - mSigOf (m n) true) := by
        funext ω
        simp only [hF, eq729FBA, mSigOf, map_sub, ite_true, Bool.false_eq_true, ite_false]
        have hH : (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k ω)).IsHermitian :=
          (gueHBA_isHermitian sz g t1 t0 K n k ω).submatrix _
        rw [Eq729A_loopL_one_false hH]
      rw [hconj, integral_conj, RCLike.norm_conj, htrue]
      exact hX a
  have hSBn : ∀ a b : Zd d (sz.L n), ‖SBgue d (sz.L n) a b‖ = ((sz.L n : ℝ) ^ d)⁻¹ := by
    intro a b; rw [SBgue_apply, norm_inv, norm_pow, Complex.norm_natCast]
  have hXb : ∀ σ a ω, ‖F ω ⟨[σ], [a]⟩ - mSigOf (m n) σ‖ ≤ 2 * N := by
    intro σ a ω
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖F ω ⟨[σ], [a]⟩‖ ≤ N ^ 1 := hFb ⟨[σ], [a]⟩ rfl (by simp) ω
    rw [pow_one] at h1
    have h2 : ‖mSigOf (m n) σ‖ ≤ 1 := by cases σ <;> simpa [mSigOf] using hm1
    linarith
  have hTb : ∀ σ₁ σ₂ σ₃ x y w ω, ‖F ω ⟨[σ₁, σ₂, σ₃], [x, y, w]⟩ - Kk ⟨[σ₁, σ₂, σ₃], [x, y, w]⟩‖
      ≤ 2 * N ^ 3 := by
    intro σ₁ σ₂ σ₃ x y w ω
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖F ω ⟨[σ₁, σ₂, σ₃], [x, y, w]⟩‖ ≤ N ^ 3 :=
      hFb ⟨[σ₁, σ₂, σ₃], [x, y, w]⟩ rfl (by simp) ω
    have h2 : ‖Kk ⟨[σ₁, σ₂, σ₃], [x, y, w]⟩‖ ≤ ρ * Λ ^ 2 := hK3b u hu σ₁ σ₂ σ₃ x y w
    have : N ^ 3 ≥ 1 := one_le_pow₀ hM1
    nlinarith
  have hpair : ∀ (σ : Bool) (a : Zd d (sz.L n)) (T : PathΩ (sz.withLam 0) → ℂ) (κ : ℂ) (c : ℂ),
      Eq729A_BM (Pgue (sz.withLam 0)) T → ‖κ‖ ≤ ρ * Λ ^ 2 → ‖c‖ = ((sz.L n : ℝ) ^ d)⁻¹ →
      (∀ ω ∉ B, ‖T ω - κ‖ ≤ ρ * Λ ^ 3) → (∀ ω, ‖T ω - κ‖ ≤ 2 * N ^ 3) →
      ‖∫ ω, (F ω ⟨[σ], [a]⟩ - mSigOf (m n) σ) * c * T ω ∂(Pgue (sz.withLam 0))‖
        ≤ ((ρ * Λ ^ 2) * (ρ * Λ ^ 2) + ((ρ * Λ) * (ρ * Λ ^ 3) + (2 * N) * (2 * N ^ 3) * p))
          * ((sz.L n : ℝ) ^ d)⁻¹ := by
    intro σ a T κ c hT hκ hc hTg hTa
    have := Eq729A_pair (μ := Pgue (sz.withLam 0)) (fun ω => F ω ⟨[σ], [a]⟩ - mSigOf (m n) σ) T κ c
      (Eq729A_BM.sub (hFBM1 σ a) (Eq729A_BM_const _)) hT (hXall σ a) hκ (by positivity)
      (by positivity) (by positivity) (by positivity) (norm_nonneg _) hB hp0
      (fun ω hω => ⟨hg1 ω hω σ a, hTg ω hω⟩) (fun ω => ⟨hXb σ a ω, hTa ω⟩)
    rwa [hc] at this
  have heG : ‖IeG‖ ≤ N * (2 * ((ρ * Λ ^ 2) * (ρ * Λ ^ 2)
      + ((ρ * Λ) * (ρ * Λ ^ 3) + (2 * N) * (2 * N ^ 3) * p))) := by
    rw [hIeG]
    simp_rw [heG_eq]
    have hint : ∀ a b, Integrable (fun ω =>
        (F ω ⟨[s1], [a]⟩ - mSigOf (m n) s1) * SBgue d (sz.L n) a b *
            F ω ⟨[s1, s1, s2], [b, a1, a2]⟩ +
          (F ω ⟨[s2], [a]⟩ - mSigOf (m n) s2) * SBgue d (sz.L n) a b *
            F ω ⟨[s1, s2, s2], [a1, b, a2]⟩) (Pgue (sz.withLam 0)) := fun a b =>
      Eq729A_BM.integrable (Eq729A_BM.add
        (Eq729A_BM.mul (Eq729A_BM.mul (Eq729A_BM.sub (hFBM1 s1 a) (Eq729A_BM_const _))
          (Eq729A_BM_const _)) (hFBM3 s1 s1 s2 b a1 a2))
        (Eq729A_BM.mul (Eq729A_BM.mul (Eq729A_BM.sub (hFBM1 s2 a) (Eq729A_BM_const _))
          (Eq729A_BM_const _)) (hFBM3 s1 s2 s2 a1 b a2)))
    refine Eq729A_norm_integral_Wsum_le' (sz.W n) _ hint fun a b => ?_
    have hi1 : Integrable (fun ω => (F ω ⟨[s1], [a]⟩ - mSigOf (m n) s1) *
        SBgue d (sz.L n) a b * F ω ⟨[s1, s1, s2], [b, a1, a2]⟩) (Pgue (sz.withLam 0)) :=
      Eq729A_BM.integrable (Eq729A_BM.mul (Eq729A_BM.mul
        (Eq729A_BM.sub (hFBM1 s1 a) (Eq729A_BM_const _)) (Eq729A_BM_const _))
        (hFBM3 s1 s1 s2 b a1 a2))
    have hi2 : Integrable (fun ω => (F ω ⟨[s2], [a]⟩ - mSigOf (m n) s2) *
        SBgue d (sz.L n) a b * F ω ⟨[s1, s2, s2], [a1, b, a2]⟩) (Pgue (sz.withLam 0)) :=
      Eq729A_BM.integrable (Eq729A_BM.mul (Eq729A_BM.mul
        (Eq729A_BM.sub (hFBM1 s2 a) (Eq729A_BM_const _)) (Eq729A_BM_const _))
        (hFBM3 s1 s2 s2 a1 b a2))
    rw [integral_add hi1 hi2]
    have p1 := hpair s1 a (fun ω => F ω ⟨[s1, s1, s2], [b, a1, a2]⟩)
      (Kk ⟨[s1, s1, s2], [b, a1, a2]⟩) (SBgue d (sz.L n) a b) (hFBM3 s1 s1 s2 b a1 a2)
      (hK3b u hu s1 s1 s2 b a1 a2) (hSBn a b) (fun ω hω => hg3 ω hω s1 s1 s2 b a1 a2)
      (fun ω => hTb s1 s1 s2 b a1 a2 ω)
    have p2 := hpair s2 a (fun ω => F ω ⟨[s1, s2, s2], [a1, b, a2]⟩)
      (Kk ⟨[s1, s2, s2], [a1, b, a2]⟩) (SBgue d (sz.L n) a b) (hFBM3 s1 s2 s2 a1 b a2)
      (hK3b u hu s1 s2 s2 a1 b a2) (hSBn a b) (fun ω hω => hg3 ω hω s1 s2 s2 a1 b a2)
      (fun ω => hTb s1 s2 s2 a1 b a2 ω)
    refine (norm_add_le _ _).trans ?_
    linarith
  -- assembly
  have hR1b : ‖R1‖ ≤ 10000 * N ^ 4 * (1 + N) ^ 6 * Δ ^ ((3 : ℝ) / 2) := by
    refine hR1.trans ?_
    have hlen : J.length = 2 := rfl
    rw [hlen, htime]
    have hu2 : u + Δ ∈ Set.Icc (t1 n) (t0 n) := hu'
    have hηk1 : (etaOf (m n) (u + Δ))⁻¹ ≤ N := by
      have := hηM _ hu2
      rwa [ztOf_im, abs_of_pos (GUEEq729BA_eta_pos hm (lt_of_le_of_lt hu2.2 ht0))] at this
    have hpos : 0 ≤ (etaOf (m n) (u + Δ))⁻¹ :=
      (inv_pos.2 (GUEEq729BA_eta_pos hm (lt_of_le_of_lt hu2.2 ht0))).le
    have hΔr : 0 ≤ Δ ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hΔ0 _
    have h6 : (1 + (etaOf (m n) (u + Δ))⁻¹) ^ (2 + 4) ≤ (1 + N) ^ 6 :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have hEnv : 16 * (((2 : ℕ) : ℝ) + 3) ^ 4 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) ^ 4 *
        (1 + (etaOf (m n) (u + Δ))⁻¹) ^ (2 + 4)
        = 10000 * N ^ 4 * (1 + (etaOf (m n) (u + Δ))⁻¹) ^ (2 + 4) := by
      have hNeq : (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) = N := rfl
      rw [hNeq]
      norm_num
    rw [hEnv]
    gcongr
  have hR2b : ‖R2‖ ≤ 3 * N ^ 2 * Δ ^ 2 := hR2
  rw [hident]
  have hQn : ‖(Δ : ℂ) * IQ‖
      ≤ Δ * (N * ((ρ * Λ ^ 2) * (ρ * Λ ^ 2) + (2 * N ^ 2) * (2 * N ^ 2) * p)) := by
    rw [norm_mul, hΔn]; exact mul_le_mul_of_nonneg_left hQ hΔ0
  have hGn : ‖(Δ : ℂ) * IeG‖ ≤ Δ * (N * (2 * ((ρ * Λ ^ 2) * (ρ * Λ ^ 2)
      + ((ρ * Λ) * (ρ * Λ ^ 3) + (2 * N) * (2 * N ^ 3) * p)))) := by
    rw [norm_mul, hΔn]; exact mul_le_mul_of_nonneg_left heG hΔ0
  have htri : ‖(e J + (Δ : ℂ) * lin) + (Δ : ℂ) * IQ + (Δ : ℂ) * IeG + R1 + R2‖
      ≤ ‖e J + (Δ : ℂ) * lin‖ + ‖(Δ : ℂ) * IQ‖ + ‖(Δ : ℂ) * IeG‖ + ‖R1‖ + ‖R2‖ := by
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl)
  refine htri.trans ?_
  unfold eq729c
  linarith

end Eq729BA4

end RBM.BA


end
