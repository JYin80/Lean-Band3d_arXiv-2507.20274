/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GUEEq729BA
import RBM3D.Universality.GUEPhase.DuhamelC
import RBM3D.Chain.StepDecompGen

/-!
# BA-C5 row b: the loop Duhamel tail of the GUE phase on the block Anderson grid

Ticket T2519 (row b; DECISIONS §344, §346, §348; Amends 1-3).  New BA leaf: no merged file is
edited.  Band twins (RBM3D, `Universality/GUEPhase`): `DuhamelA2.lean:1008`
(`Duhamel_drift_remainder_ae`), `DuhamelB.lean` (the processes, the Azuma tails,
`Duhamel_bddC2C_Phi`, `Duhamel_step_decomp:739`, `Duhamel_grid_facts`), `DuhamelC.lean:1485`
(`gueGrid_loop_duhamel`, in `BA/GUEDuhamelBA2`).  Paper: the GUE phase of Thm 2.4 is "essentially
identical to [YY_25, Theorem 2.6]" (`paper/tex/1_2_Intro_model_result.tex:566-570`), `d ≥ 3`, block
Anderson `S^{(B)}(0) = 1`.

The grid path is `gueHBA sz g t1 t0 K n k ω = g Ψ_I + H_k` (C4 a, `BA/GUEOneLoop:58`), `H_k` the
band path of the model `sz.withLam 0`; the flow is `ztOf m E u = E + (1 - u) m`,
`etaOf m u = (1 - u) Im m`, and the generator is `genMatGUEOf` (the band `zt`, `etaT`, `mE` are the
case `m = mE E`).  The band hypothesis `|E| < 2` becomes `0 < Im m` and `‖m‖ ≤ 1` (block Anderson:
`BAReal`, `BAm_norm_le_one`).

* §1-§4 (private): the development at a generic model `sz` and a Hermitian shift `A n` of the path,
  which is `A n + gueH sz …`: the observable and the processes of the step `j → j+1`
  (`GUEDuhamelBA_gPhi`, `_gVp`, `_gZinc`, `_gZst`, `_gYst`, `_gr`), Azuma for the stopped linear
  part and for the recentred truncated remainder, the `C²` class of the loop observable
  (`hermTestFunLoopNOf`, `Chain/StepDecompGen:101`), the pathwise decomposition of one step, the
  grid facts (`‖z_{j+1} - z_j‖ ≤ Δ ‖m‖`: the band has `= Δ`, as `‖mE E‖ = 1`).  The generic band
  lemmas (`DuhamelA2`: truncation, Taylor layer; `Duhamel_Vp_le`, `Duhamel_qv_le_crude`,
  `Duhamel_exists_level`; the conditional sub-Gaussian lemmas of `Markov`) are read by name, the
  band privates by `open private … from` (no third copies).
* §5 (target 6, public) the BA-form processes `GUEDuhamelBA_Phi`, `_Zinc`, `_Yst`, `_r`, `_Vp`,
  `_Zst` (twins of `DuhamelPhi`, `DuhamelZinc`, `DuhamelYst`, `Duhamelr`, `DuhamelVp`, `DuhamelZst`;
  the specialisations `sz := sz.withLam 0`, `A n := g Ψ_I` of the private ones, by `rfl`),
  `Duhamel_step_decompBA`, `Duhamel_azuma_ZBA`, `Duhamel_azuma_YBA` (the Azuma tails) and
  `Duhamel_drift_remainder_aeBA` (reads `condExp_loop_drift_gueBA`, C4 b, through the freezing
  lemma).
* §6 (target 8) compiled nonempty instances of §5 (`RBM.BA.GUEDuhamelBAInst`); the instance of the
  main theorem of `BA/GUEDuhamelBA2` is in that file.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false

open private DuhamelB_measurable_gradMat DuhamelB_measurable_vGue DuhamelB_sm_indicator_lin DuhamelB_FY
  DuhamelB_measurable_FY DuhamelB_condSubG_frozen DuhamelB_loopOf_eq from RBM3D.Universality.GUEPhase.DuhamelB
open private DuhamelA2_condExp_freezeC DuhamelA2_herm_of_isHermitian DuhamelA2_continuous_Phi
  DuhamelA2_norm_Phi_le DuhamelA2_Phi DuhamelA2_measurable_seqHflow from RBM3D.Universality.GUEPhase.DuhamelA2

noncomputable section

namespace RBM.BA

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.LinearForm RBM.Path RBM.Loop RBM.Univ
  RBM.Univ.GUEPhase
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-! ## 1. The shifted grid path and the processes of one step (private, generic in the Hermitian shift) -/

section Defs

variable {d : ℕ} (sz : Sizes d) (A : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
  (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (e : ℝ) (μ : ℂ) (I : LoopIdx (Zd d (sz.L n)))

/-- The shifted GUE-phase grid path `A n + H_k` (for `sz := sz.withLam 0`, `A n := g Ψ_I` it is `gueHBA`). -/
private abbrev GUEDuhamelBA_gH (k : ℕ) (ω : PathΩ sz) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  A n + gueH sz t1 t0 K n k ω

/-- The observable of the step `j → j+1` (at the spectral parameter of time `u_{j+1}` along `ztOf μ e`). -/
private def GUEDuhamelBA_gPhi (j : ℕ) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ :=
  fun M => loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) (ztOf μ e (gridTime t1 t0 K n (j + 1))) I

/-- The conditional variance proxy of the linear part. -/
private def GUEDuhamelBA_gVp (j : ℕ) (ω : PathΩ sz) : ℝ :=
  Duhamelv sz t1 t0 K n * max
    (vGue sz n (gradMat (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j) (GUEDuhamelBA_gH sz A t1 t0 K n j ω)) : ℝ)
    (vGue sz n (-Complex.I • gradMat (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j)
      (GUEDuhamelBA_gH sz A t1 t0 K n j ω)) : ℝ)

/-- The linear part of the step `j → j+1`. -/
private def GUEDuhamelBA_gZinc (j : ℕ) (ω : PathΩ sz) : ℂ :=
  DuhamelZ sz n (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j) (Duhamelv sz t1 t0 K n)
    (GUEDuhamelBA_gH sz A t1 t0 K n j ω) (ω (j + 1))

/-- The linear part, stopped at the dyadic level `lam` (index `0` carries `0`). -/
private def GUEDuhamelBA_gZst (lam : ℝ) : ℕ → PathΩ sz → ℂ
  | 0 => fun _ => 0
  | j + 1 => {ω | j < firstHit (GUEDuhamelBA_gVp sz A t1 t0 K n e μ I) lam (K n) ω}.indicator
      (GUEDuhamelBA_gZinc sz A t1 t0 K n e μ I j)

/-- The martingale increments `Ỹ` (cut off after the grid horizon): `T - ∫ T`. -/
private def GUEDuhamelBA_gYst : ℕ → PathΩ sz → ℂ
  | 0 => fun _ => 0
  | j + 1 => fun ω => if j < K n then
      DuhamelT sz n (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j) (Duhamelv sz t1 t0 K n)
        (GUEDuhamelBA_gH sz A t1 t0 K n j ω) (ω (j + 1))
        - ∫ y, DuhamelT sz n (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j) (Duhamelv sz t1 t0 K n)
          (GUEDuhamelBA_gH sz A t1 t0 K n j ω) y ∂(gueUnit sz)
      else 0

/-- The remainder of the step `j → j+1`. -/
private def GUEDuhamelBA_gr (j : ℕ) (ω : PathΩ sz) : ℂ :=
  (∫ y, GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j
      (GUEDuhamelBA_gH sz A t1 t0 K n j ω + Sizes.seqHflow sz n (Duhamelv sz t1 t0 K n) y) ∂(gueUnit sz))
    - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (GUEDuhamelBA_gH sz A t1 t0 K n j ω))
        (ztOf μ e (gridTime t1 t0 K n j)) I
    - (gridStep t1 t0 K n : ℂ) * genMatGUEOf d (sz.L n) (sz.W n) μ e (gridTime t1 t0 K n j)
        (GUEDuhamelBA_gH sz A t1 t0 K n j ω) I

end Defs

section ShiftedPath

variable {d : ℕ} {sz : Sizes d} (A : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)

private theorem GUEDuhamelBA_gH_isHermitian (hA : ∀ n, (A n).IsHermitian) (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (ω : PathΩ sz) : (GUEDuhamelBA_gH sz A t1 t0 K n k ω).IsHermitian :=
  (hA n).add (gueH_isHermitian sz t1 t0 K n k ω)

private theorem GUEDuhamelBA_gH_measurable (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) :
    Measurable[filt sz k] (GUEDuhamelBA_gH sz A t1 t0 K n k) :=
  @measurable_pi_iff _ _ _ (filt sz k) _ _ |>.mpr fun i =>
    @measurable_pi_iff _ _ _ (filt sz k) _ _ |>.mpr fun j =>
      ((gueH_adapted sz t1 t0 K n k i j).measurable).const_add (A n i j)

private theorem GUEDuhamelBA_gH_succ (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz) :
    GUEDuhamelBA_gH sz A t1 t0 K n (k + 1) ω
      = GUEDuhamelBA_gH sz A t1 t0 K n k ω
        + Sizes.seqHflow sz n (Duhamelv sz t1 t0 K n) (ω (k + 1)) := by
  unfold GUEDuhamelBA_gH
  rw [gueH_succ sz t1 t0 K n k ω, ← add_assoc]
  rfl

end ShiftedPath

/-! ## 2. The linear part: dyadic stopping levels and Azuma -/

section AzumaZ

variable {d : ℕ} {sz : Sizes d} {A : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
  {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {e : ℝ} {μ : ℂ} {I : LoopIdx (Zd d (sz.L n))}

private theorem GUEDuhamelBA_measurable_A (j : ℕ) :
    Measurable[filt sz j] (fun ω : PathΩ sz =>
      gradMat (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j) (GUEDuhamelBA_gH sz A t1 t0 K n j ω)) :=
  (DuhamelB_measurable_gradMat _).comp (GUEDuhamelBA_gH_measurable A t1 t0 K n j)

private theorem GUEDuhamelBA_measurable_A' (j : ℕ) :
    Measurable[filt sz j] (fun ω : PathΩ sz =>
      -Complex.I • gradMat (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j) (GUEDuhamelBA_gH sz A t1 t0 K n j ω)) := by
  have hA := GUEDuhamelBA_measurable_A (A := A) (t1 := t1) (t0 := t0) (K := K) (n := n) (e := e) (μ := μ)
    (I := I) j
  change Measurable[filt sz j] ((-Complex.I) • (fun ω : PathΩ sz =>
    gradMat (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j) (GUEDuhamelBA_gH sz A t1 t0 K n j ω)))
  exact hA.const_smul _

private theorem GUEDuhamelBA_adapted_Vp :
    Adapted (filt sz) (GUEDuhamelBA_gVp sz A t1 t0 K n e μ I) := by
  intro j
  exact measurable_const.mul (((DuhamelB_measurable_vGue n).comp
    (GUEDuhamelBA_measurable_A (e := e) (μ := μ) (I := I) j)).max ((DuhamelB_measurable_vGue n).comp
    (GUEDuhamelBA_measurable_A' (e := e) (μ := μ) (I := I) j)))

private theorem GUEDuhamelBA_Zst_re_im (lam : ℝ) (j : ℕ) (ω : PathΩ sz) :
    (GUEDuhamelBA_gZst sz A t1 t0 K n e μ I lam (j + 1) ω).re
        = {ω | j < firstHit (GUEDuhamelBA_gVp sz A t1 t0 K n e μ I) lam (K n) ω}.indicator
          (fun ω => Real.sqrt (Duhamelv sz t1 t0 K n) * linTr n
            (gradMat (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j) (GUEDuhamelBA_gH sz A t1 t0 K n j ω))
            (Sizes.seqXmat sz n (ω (j + 1)))) ω ∧
      (GUEDuhamelBA_gZst sz A t1 t0 K n e μ I lam (j + 1) ω).im
        = {ω | j < firstHit (GUEDuhamelBA_gVp sz A t1 t0 K n e μ I) lam (K n) ω}.indicator
          (fun ω => Real.sqrt (Duhamelv sz t1 t0 K n) * linTr n
            (-Complex.I • gradMat (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j) (GUEDuhamelBA_gH sz A t1 t0 K n j ω))
            (Sizes.seqXmat sz n (ω (j + 1)))) ω := by
  simp only [GUEDuhamelBA_gZst, Set.indicator]
  split_ifs
  · exact Duhamel_Z_re_im _ _ _
  · simp

private theorem GUEDuhamelBA_stronglyAdapted_Zst (lam : ℝ) :
    StronglyAdapted (filt sz) (fun i ω => (GUEDuhamelBA_gZst sz A t1 t0 K n e μ I lam i ω).re) ∧
      StronglyAdapted (filt sz) (fun i ω => (GUEDuhamelBA_gZst sz A t1 t0 K n e μ I lam i ω).im) := by
  have hE : ∀ j, MeasurableSet[filt sz j]
      {ω | j < firstHit (GUEDuhamelBA_gVp sz A t1 t0 K n e μ I) lam (K n) ω} :=
    fun j => lt_firstHit_measurableSet _ lam (K n) GUEDuhamelBA_adapted_Vp j
  constructor
  · intro i
    rcases i with _ | j
    · exact stronglyMeasurable_const
    · have heq : (fun ω => (GUEDuhamelBA_gZst sz A t1 t0 K n e μ I lam (j + 1) ω).re)
          = {ω | j < firstHit (GUEDuhamelBA_gVp sz A t1 t0 K n e μ I) lam (K n) ω}.indicator
            (fun ω => Real.sqrt (Duhamelv sz t1 t0 K n) * linTr n
              (gradMat (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j) (GUEDuhamelBA_gH sz A t1 t0 K n j ω))
              (Sizes.seqXmat sz n (ω (j + 1)))) :=
        funext fun ω => (GUEDuhamelBA_Zst_re_im lam j ω).1
      change StronglyMeasurable[filt sz (j + 1)]
        (fun ω => (GUEDuhamelBA_gZst sz A t1 t0 K n e μ I lam (j + 1) ω).re)
      rw [heq]
      exact DuhamelB_sm_indicator_lin (hE j) (GUEDuhamelBA_measurable_A j) _
  · intro i
    rcases i with _ | j
    · exact stronglyMeasurable_const
    · have heq : (fun ω => (GUEDuhamelBA_gZst sz A t1 t0 K n e μ I lam (j + 1) ω).im)
          = {ω | j < firstHit (GUEDuhamelBA_gVp sz A t1 t0 K n e μ I) lam (K n) ω}.indicator
            (fun ω => Real.sqrt (Duhamelv sz t1 t0 K n) * linTr n
              (-Complex.I • gradMat (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j)
                (GUEDuhamelBA_gH sz A t1 t0 K n j ω))
              (Sizes.seqXmat sz n (ω (j + 1)))) :=
        funext fun ω => (GUEDuhamelBA_Zst_re_im lam j ω).2
      change StronglyMeasurable[filt sz (j + 1)]
        (fun ω => (GUEDuhamelBA_gZst sz A t1 t0 K n e μ I lam (j + 1) ω).im)
      rw [heq]
      exact DuhamelB_sm_indicator_lin (hE j) (GUEDuhamelBA_measurable_A' j) _

private theorem GUEDuhamelBA_condSubG_Zst {lam : ℝ} (hlam : 0 ≤ lam)
    (hv : 0 ≤ Duhamelv sz t1 t0 K n) (j : ℕ) :
    HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
        (fun ω => (GUEDuhamelBA_gZst sz A t1 t0 K n e μ I lam (j + 1) ω).re) ⟨lam, hlam⟩ (Pgue sz) ∧
      HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
        (fun ω => (GUEDuhamelBA_gZst sz A t1 t0 K n e μ I lam (j + 1) ω).im) ⟨lam, hlam⟩ (Pgue sz) := by
  have hE : MeasurableSet[filt sz j]
      {ω | j < firstHit (GUEDuhamelBA_gVp sz A t1 t0 K n e μ I) lam (K n) ω} :=
    lt_firstHit_measurableSet _ lam (K n) GUEDuhamelBA_adapted_Vp j
  have hsq : Real.sqrt (Duhamelv sz t1 t0 K n) ^ 2 = Duhamelv sz t1 t0 K n := Real.sq_sqrt hv
  have hb1 : ∀ ω ∈ {ω | j < firstHit (GUEDuhamelBA_gVp sz A t1 t0 K n e μ I) lam (K n) ω},
      Real.sqrt (Duhamelv sz t1 t0 K n) ^ 2 * (vGue sz n
        (gradMat (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j) (GUEDuhamelBA_gH sz A t1 t0 K n j ω)) : ℝ)
        ≤ ((⟨lam, hlam⟩ : ℝ≥0) : ℝ) := by
    intro ω hω
    have h := lt_firstHit_imp (GUEDuhamelBA_gVp sz A t1 t0 K n e μ I) lam (K n) hω
    rw [hsq]
    refine le_trans ?_ h.le
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) hv
  have hb2 : ∀ ω ∈ {ω | j < firstHit (GUEDuhamelBA_gVp sz A t1 t0 K n e μ I) lam (K n) ω},
      Real.sqrt (Duhamelv sz t1 t0 K n) ^ 2 * (vGue sz n
        (-Complex.I • gradMat (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j)
          (GUEDuhamelBA_gH sz A t1 t0 K n j ω)) : ℝ)
        ≤ ((⟨lam, hlam⟩ : ℝ≥0) : ℝ) := by
    intro ω hω
    have h := lt_firstHit_imp (GUEDuhamelBA_gVp sz A t1 t0 K n e μ I) lam (K n) hω
    rw [hsq]
    refine le_trans ?_ h.le
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) hv
  have h1 := gueHasCondSubgaussianMGF_linear sz n j (Real.sqrt (Duhamelv sz t1 t0 K n))
    (GUEDuhamelBA_measurable_A (A := A) (e := e) (μ := μ) (I := I) j) _ hE _ hb1
  have h2 := gueHasCondSubgaussianMGF_linear sz n j (Real.sqrt (Duhamelv sz t1 t0 K n))
    (GUEDuhamelBA_measurable_A' (A := A) (e := e) (μ := μ) (I := I) j) _ hE _ hb2
  constructor
  · have heq : (fun ω => (GUEDuhamelBA_gZst sz A t1 t0 K n e μ I lam (j + 1) ω).re)
        = fun ω => {ω | j < firstHit (GUEDuhamelBA_gVp sz A t1 t0 K n e μ I) lam (K n) ω}.indicator
            (fun ω => Real.sqrt (Duhamelv sz t1 t0 K n) * linTr n
              (gradMat (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j) (GUEDuhamelBA_gH sz A t1 t0 K n j ω))
              (Sizes.seqXmat sz n (ω (j + 1)))) ω :=
      funext fun ω => (GUEDuhamelBA_Zst_re_im lam j ω).1
    rw [heq]; exact h1
  · have heq : (fun ω => (GUEDuhamelBA_gZst sz A t1 t0 K n e μ I lam (j + 1) ω).im)
        = fun ω => {ω | j < firstHit (GUEDuhamelBA_gVp sz A t1 t0 K n e μ I) lam (K n) ω}.indicator
            (fun ω => Real.sqrt (Duhamelv sz t1 t0 K n) * linTr n
              (-Complex.I • gradMat (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j)
                (GUEDuhamelBA_gH sz A t1 t0 K n j ω))
              (Sizes.seqXmat sz n (ω (j + 1)))) ω :=
      funext fun ω => (GUEDuhamelBA_Zst_re_im lam j ω).2
    rw [heq]; exact h2

/-- **Azuma at one dyadic level** (`Duhamel_azuma_Z`, `DuhamelB:341`): the linear part stopped at
`firstHit (GUEDuhamelBA_gVp …) lam (K n)` has the complex Azuma tail with proxy `lam` per step. -/
private theorem GUEDuhamelBA_azuma_Z {lam : ℝ} (hlam : 0 < lam) (hv : 0 ≤ Duhamelv sz t1 t0 K n) (k : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Pgue sz).real {ω | ε ≤ ‖∑ j ∈ Finset.range k, GUEDuhamelBA_gZst sz A t1 t0 K n e μ I lam (j + 1) ω‖}
      ≤ 4 * Real.exp (-ε ^ 2 / (4 * (k * lam))) := by
  set c : ℕ → ℝ≥0 := fun i => if i = 0 then 0 else ⟨lam, hlam.le⟩ with hc
  obtain ⟨hR, hI⟩ := GUEDuhamelBA_stronglyAdapted_Zst (sz := sz) (A := A) (t1 := t1) (t0 := t0) (K := K)
    (n := n) (e := e) (μ := μ) (I := I) lam
  have h0 : HasSubgaussianMGF (fun ω => (GUEDuhamelBA_gZst sz A t1 t0 K n e μ I lam 0 ω).re) (c 0)
      (Pgue sz) := by
    simp only [hc, GUEDuhamelBA_gZst, Complex.zero_re]
    exact HasSubgaussianMGF.zero
  have h0' : HasSubgaussianMGF (fun ω => (GUEDuhamelBA_gZst sz A t1 t0 K n e μ I lam 0 ω).im) (c 0)
      (Pgue sz) := by
    simp only [hc, GUEDuhamelBA_gZst, Complex.zero_im]
    exact HasSubgaussianMGF.zero
  have hCR : ∀ i < (k + 1) - 1, HasCondSubgaussianMGF (filt sz i) ((filt sz).le i)
      (fun ω => (GUEDuhamelBA_gZst sz A t1 t0 K n e μ I lam (i + 1) ω).re) (c (i + 1)) (Pgue sz) := by
    intro i _
    simp only [hc, Nat.succ_ne_zero]
    exact (GUEDuhamelBA_condSubG_Zst hlam.le hv i).1
  have hCI : ∀ i < (k + 1) - 1, HasCondSubgaussianMGF (filt sz i) ((filt sz).le i)
      (fun ω => (GUEDuhamelBA_gZst sz A t1 t0 K n e μ I lam (i + 1) ω).im) (c (i + 1)) (Pgue sz) := by
    intro i _
    simp only [hc, Nat.succ_ne_zero]
    exact (GUEDuhamelBA_condSubG_Zst hlam.le hv i).2
  have haz := azuma_complex (μ := Pgue sz) (ℱ := filt sz)
    (Z := GUEDuhamelBA_gZst sz A t1 t0 K n e μ I lam) (c := c) hR hI (k + 1) h0 h0' hCR hCI hε
  have hsumZ : ∀ ω, ∑ i ∈ Finset.range (k + 1), GUEDuhamelBA_gZst sz A t1 t0 K n e μ I lam i ω
      = ∑ j ∈ Finset.range k, GUEDuhamelBA_gZst sz A t1 t0 K n e μ I lam (j + 1) ω := by
    intro ω
    rw [Finset.sum_range_succ']
    simp [GUEDuhamelBA_gZst]
  have hsumc : ((∑ i ∈ Finset.range (k + 1), c i : ℝ≥0) : ℝ) = k * lam := by
    rw [NNReal.coe_sum, Finset.sum_range_succ']
    have : ∀ i ∈ Finset.range k, (c (i + 1) : ℝ) = lam := fun i _ => by simp [hc]; rfl
    rw [Finset.sum_congr rfl this]
    simp [hc]
  simp only [hsumZ, hsumc] at haz
  exact haz

end AzumaZ

/-! ## 3. The remainder part: adapted truncation and conditional Hoeffding -/

section AzumaY

variable {d : ℕ} {sz : Sizes d} {A : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
  {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {e : ℝ} {μ : ℂ} {I : LoopIdx (Zd d (sz.L n))}

private theorem GUEDuhamelBA_measurable_Phi (j : ℕ) :
    Measurable (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j) :=
  Duhamel_measurable_loop _ _

private theorem GUEDuhamelBA_Yst_succ {j : ℕ} (hj : j < K n) (ω : PathΩ sz) :
    GUEDuhamelBA_gYst sz A t1 t0 K n e μ I (j + 1) ω
      = DuhamelB_FY (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j) (Duhamelv sz t1 t0 K n)
          (GUEDuhamelBA_gH sz A t1 t0 K n j ω) (ω (j + 1)) := by
  simp [GUEDuhamelBA_gYst, hj, DuhamelB_FY]

private theorem GUEDuhamelBA_condSubG_Yst (hA : ∀ n, (A n).IsHermitian) {j : ℕ} (hj : j < K n) {b : ℝ}
    (hb0 : 0 ≤ b)
    (hb : ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian → ∀ y,
      ‖DuhamelT sz n (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j) (Duhamelv sz t1 t0 K n) M y‖ ≤ b) :
    HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
        (fun ω => (GUEDuhamelBA_gYst sz A t1 t0 K n e μ I (j + 1) ω).re) ((‖2 * b - -(2 * b)‖₊ / 2) ^ 2)
        (Pgue sz) ∧
      HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
        (fun ω => (GUEDuhamelBA_gYst sz A t1 t0 K n e μ I (j + 1) ω).im) ((‖2 * b - -(2 * b)‖₊ / 2) ^ 2)
        (Pgue sz) := by
  have h := DuhamelB_condSubG_frozen (sz := sz) (n := n) (j := j) (GUEDuhamelBA_measurable_Phi (e := e) (μ := μ)
    (I := I) j) (GUEDuhamelBA_gH_measurable A t1 t0 K n j)
    (fun ω => GUEDuhamelBA_gH_isHermitian A hA t1 t0 K n j ω) hb0 hb
  have heq1 : (fun ω => (GUEDuhamelBA_gYst sz A t1 t0 K n e μ I (j + 1) ω).re)
      = fun ω => (DuhamelB_FY (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j) (Duhamelv sz t1 t0 K n)
          (GUEDuhamelBA_gH sz A t1 t0 K n j ω) (ω (j + 1))).re := by
    funext ω; rw [GUEDuhamelBA_Yst_succ hj]
  have heq2 : (fun ω => (GUEDuhamelBA_gYst sz A t1 t0 K n e μ I (j + 1) ω).im)
      = fun ω => (DuhamelB_FY (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j) (Duhamelv sz t1 t0 K n)
          (GUEDuhamelBA_gH sz A t1 t0 K n j ω) (ω (j + 1))).im := by
    funext ω; rw [GUEDuhamelBA_Yst_succ hj]
  rw [heq1, heq2]
  exact h

private theorem GUEDuhamelBA_stronglyAdapted_Yst :
    StronglyAdapted (filt sz) (fun i ω => (GUEDuhamelBA_gYst sz A t1 t0 K n e μ I i ω).re) ∧
      StronglyAdapted (filt sz) (fun i ω => (GUEDuhamelBA_gYst sz A t1 t0 K n e μ I i ω).im) := by
  have key : ∀ j, Measurable[filt sz (j + 1)] (GUEDuhamelBA_gYst sz A t1 t0 K n e μ I (j + 1)) := by
    intro j
    by_cases hj : j < K n
    · have hF := DuhamelB_measurable_FY (sz := sz) (n := n)
        (GUEDuhamelBA_measurable_Phi (t1 := t1) (t0 := t0) (K := K) (e := e) (μ := μ) (I := I) j)
        (Duhamelv sz t1 t0 K n)
      have hle : filt sz j ≤ filt sz (j + 1) := (filt sz).mono (Nat.le_succ j)
      have hY : Measurable[filt sz (j + 1)] (GUEDuhamelBA_gH sz A t1 t0 K n j) :=
        (GUEDuhamelBA_gH_measurable A t1 t0 K n j).mono hle le_rfl
      have hc : Measurable[filt sz (j + 1)] (fun ω : PathΩ sz => ω (j + 1)) :=
        Duhamel_measurable_coord sz le_rfl
      have hp := hY.prodMk hc
      have hcomp := hF.comp hp
      have heq : GUEDuhamelBA_gYst sz A t1 t0 K n e μ I (j + 1)
          = fun ω => DuhamelB_FY (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j) (Duhamelv sz t1 t0 K n)
              (GUEDuhamelBA_gH sz A t1 t0 K n j ω) (ω (j + 1)) :=
        funext fun ω => GUEDuhamelBA_Yst_succ hj ω
      rw [heq]; exact hcomp
    · have heq : GUEDuhamelBA_gYst sz A t1 t0 K n e μ I (j + 1) = fun _ => 0 := by
        funext ω; simp [GUEDuhamelBA_gYst, hj]
      rw [heq]; exact measurable_const
  constructor
  · intro i
    rcases i with _ | j
    · exact stronglyMeasurable_const
    · exact (Complex.measurable_re.comp (key j)).stronglyMeasurable
  · intro i
    rcases i with _ | j
    · exact stronglyMeasurable_const
    · exact (Complex.measurable_im.comp (key j)).stronglyMeasurable

/-- **Azuma for `Ỹ`** (`Duhamel_azuma_Y`, `DuhamelB:620`): the recentred, truncated remainders `T - ∫ T` have the
complex Azuma tail with proxy `4 b²` per step, `b` a bound of `DuhamelT` at Hermitian base points. -/
private theorem GUEDuhamelBA_azuma_Y (hA : ∀ n, (A n).IsHermitian) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ j < K n, ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
      M.IsHermitian → ∀ y,
      ‖DuhamelT sz n (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j) (Duhamelv sz t1 t0 K n) M y‖ ≤ b)
    {k : ℕ} (hk : k ≤ K n) {ε : ℝ} (hε : 0 ≤ ε) :
    (Pgue sz).real {ω | ε ≤ ‖∑ j ∈ Finset.range k, GUEDuhamelBA_gYst sz A t1 t0 K n e μ I (j + 1) ω‖}
      ≤ 4 * Real.exp (-ε ^ 2 / (4 * (k * (4 * b ^ 2)))) := by
  set P : ℝ≥0 := (‖2 * b - -(2 * b)‖₊ / 2) ^ 2 with hP
  have hPval : (P : ℝ) = 4 * b ^ 2 := by
    rw [hP]
    push_cast
    rw [Real.norm_eq_abs, show 2 * b - -(2 * b) = 4 * b by ring,
      abs_of_nonneg (by linarith)]
    ring
  set c : ℕ → ℝ≥0 := fun i => if i = 0 then 0 else P with hc
  obtain ⟨hR, hI⟩ := GUEDuhamelBA_stronglyAdapted_Yst (sz := sz) (A := A) (t1 := t1) (t0 := t0) (K := K)
    (n := n) (e := e) (μ := μ) (I := I)
  have h0 : HasSubgaussianMGF (fun ω => (GUEDuhamelBA_gYst sz A t1 t0 K n e μ I 0 ω).re) (c 0) (Pgue sz) := by
    simp only [hc, GUEDuhamelBA_gYst, Complex.zero_re]
    exact HasSubgaussianMGF.zero
  have h0' : HasSubgaussianMGF (fun ω => (GUEDuhamelBA_gYst sz A t1 t0 K n e μ I 0 ω).im) (c 0)
      (Pgue sz) := by
    simp only [hc, GUEDuhamelBA_gYst, Complex.zero_im]
    exact HasSubgaussianMGF.zero
  have hsub : ∀ i < (k + 1) - 1,
      HasCondSubgaussianMGF (filt sz i) ((filt sz).le i)
        (fun ω => (GUEDuhamelBA_gYst sz A t1 t0 K n e μ I (i + 1) ω).re) (c (i + 1)) (Pgue sz) ∧
      HasCondSubgaussianMGF (filt sz i) ((filt sz).le i)
        (fun ω => (GUEDuhamelBA_gYst sz A t1 t0 K n e μ I (i + 1) ω).im) (c (i + 1)) (Pgue sz) := by
    intro i hi
    have hiK : i < K n := by omega
    simp only [hc, Nat.succ_ne_zero]
    exact GUEDuhamelBA_condSubG_Yst hA hiK hb0 (hb i hiK)
  have haz := azuma_complex (μ := Pgue sz) (ℱ := filt sz)
    (Z := GUEDuhamelBA_gYst sz A t1 t0 K n e μ I) (c := c) hR hI (k + 1) h0 h0'
    (fun i hi => (hsub i hi).1) (fun i hi => (hsub i hi).2) hε
  have hsumZ : ∀ ω, ∑ i ∈ Finset.range (k + 1), GUEDuhamelBA_gYst sz A t1 t0 K n e μ I i ω
      = ∑ j ∈ Finset.range k, GUEDuhamelBA_gYst sz A t1 t0 K n e μ I (j + 1) ω := by
    intro ω
    rw [Finset.sum_range_succ']
    simp [GUEDuhamelBA_gYst]
  have hsumc : ((∑ i ∈ Finset.range (k + 1), c i : ℝ≥0) : ℝ) = k * (4 * b ^ 2) := by
    rw [NNReal.coe_sum, Finset.sum_range_succ']
    have : ∀ i ∈ Finset.range k, (c (i + 1) : ℝ) = 4 * b ^ 2 := fun i _ => by
      simp only [hc, Nat.succ_ne_zero, ite_false]; exact hPval
    rw [Finset.sum_congr rfl this]
    simp [hc]
  simp only [hsumZ, hsumc] at haz
  exact haz

end AzumaY

/-! ## 4. The pathwise decomposition of one step, the grid facts -/

section Decomp

variable {d : ℕ} {sz : Sizes d} {A : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
  {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {e : ℝ} {μ : ℂ} {I : LoopIdx (Zd d (sz.L n))}

/-- **The loop observable before the horizon is `C²` with explicit constants** (`Duhamel_bddC2C_Phi`,
`DuhamelB:687`; `hermTestFunLoopNOf`, `Chain/StepDecompGen:101`, at `ztOf μ e` and `0 < Im μ`). -/
private theorem GUEDuhamelBA_bddC2C_Phi (hμ : 0 < μ.im) (hwf : I.WF) (hst : t1 n ≤ t0 n) (ht0 : t0 n < 1)
    {j : ℕ} (hj : j < K n) :
    (ztOf μ e (gridTime t1 t0 K n (j + 1))).im ≠ 0 ∧
      HermTestFun sz n (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j) ∧
      ∀ M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
        M.IsHermitian → y.IsHermitian →
        ‖fderiv ℝ (fderiv ℝ (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j)) M y y‖
          ≤ ((I.length * (I.length + 1) : ℕ) : ℝ) * (sz.size n : ℝ)
            * (etaOf μ (gridTime t1 t0 K n (j + 1)))⁻¹ ^ (I.length + 2) * ‖y‖ ^ 2 := by
  have hKpos : (0 : ℝ) < (K n : ℝ) := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le j) hj)
  have hk1 : (j : ℝ) + 1 ≤ (K n : ℝ) := by exact_mod_cast hj
  have hΔ0 : 0 ≤ gridStep t1 t0 K n := by
    unfold gridStep; exact div_nonneg (by linarith) hKpos.le
  have hKΔ : (K n : ℝ) * gridStep t1 t0 K n = t0 n - t1 n := by
    unfold gridStep; field_simp
  have h : gridTime t1 t0 K n (j + 1) = t1 n + ((j : ℝ) + 1) * gridStep t1 t0 K n := by
    unfold gridTime; push_cast; ring
  have hu1lt : gridTime t1 t0 K n (j + 1) < 1 := by
    rw [h]; nlinarith
  have hpos : 0 < (1 - gridTime t1 t0 K n (j + 1)) * μ.im :=
    mul_pos (by linarith) hμ
  have hz : (ztOf μ e (gridTime t1 t0 K n (j + 1))).im ≠ 0 := by
    rw [ztOf_im]; exact hpos.ne'
  have h1 := hermTestFunLoopNOf sz I.a.length n μ e _ hμ hu1lt
    (fun i : Fin I.a.length => I.σ[i.1]'(by rw [hwf]; exact i.2))
    (fun i : Fin I.a.length => I.a[i.1])
  rw [DuhamelB_loopOf_eq I hwf] at h1
  exact ⟨hz, h1.1, h1.2⟩

/-- **One step, pathwise**, on the truncation set of the new increment (`Duhamel_step_decomp`, `DuhamelB:739`):
`𝓛_{u_{j+1}}(H_{j+1}) - 𝓛_{u_j}(H_j) - Δ · gen = Z + Ỹ - B + r`. -/
private theorem GUEDuhamelBA_step_decomp (hA : ∀ n, (A n).IsHermitian) (hμ : 0 < μ.im) (hwf : I.WF)
    (hst : t1 n ≤ t0 n) (ht0 : t0 n < 1) {j : ℕ} (hj : j < K n) (ω : PathΩ sz)
    (hgood : ω (j + 1) ∈ DuhamelGood sz n) :
    loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (GUEDuhamelBA_gH sz A t1 t0 K n (j + 1) ω))
        (ztOf μ e (gridTime t1 t0 K n (j + 1))) I
        - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (GUEDuhamelBA_gH sz A t1 t0 K n j ω))
            (ztOf μ e (gridTime t1 t0 K n j)) I
        - (gridStep t1 t0 K n : ℂ) * genMatGUEOf d (sz.L n) (sz.W n) μ e (gridTime t1 t0 K n j)
            (GUEDuhamelBA_gH sz A t1 t0 K n j ω) I
      = GUEDuhamelBA_gZinc sz A t1 t0 K n e μ I j ω + GUEDuhamelBA_gYst sz A t1 t0 K n e μ I (j + 1) ω
        - DuhamelB sz n (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j) (Duhamelv sz t1 t0 K n)
            (GUEDuhamelBA_gH sz A t1 t0 K n j ω)
        + GUEDuhamelBA_gr sz A t1 t0 K n e μ I j ω := by
  obtain ⟨_, hΦ, hC₂⟩ := GUEDuhamelBA_bddC2C_Phi (sz := sz) (t1 := t1) (t0 := t0) (K := K) (n := n)
    (e := e) (μ := μ) (I := I) hμ hwf hst ht0 hj
  set Φ := GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j with hΦdef
  set v := Duhamelv sz t1 t0 K n with hvdef
  set M := GUEDuhamelBA_gH sz A t1 t0 K n j ω with hMdef
  set X := ω (j + 1) with hXdef
  have hM : M.IsHermitian := GUEDuhamelBA_gH_isHermitian A hA t1 t0 K n j ω
  have hsucc : GUEDuhamelBA_gH sz A t1 t0 K n (j + 1) ω = M + Sizes.seqHflow sz n v X :=
    GUEDuhamelBA_gH_succ A t1 t0 K n j ω
  have hL1 : loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (GUEDuhamelBA_gH sz A t1 t0 K n (j + 1) ω))
      (ztOf μ e (gridTime t1 t0 K n (j + 1))) I = Φ (M + Sizes.seqHflow sz n v X) := by
    rw [hΦdef, hsucc]; rfl
  have hint := Duhamel_integral_step hΦ hC₂ v hM
  have hRdef : Φ (M + Sizes.seqHflow sz n v X)
      = Φ M + DuhamelZ sz n Φ v M X + DuhamelR sz n Φ v M X := by
    unfold DuhamelR; ring
  have hT : DuhamelT sz n Φ v M X = DuhamelR sz n Φ v M X := by
    unfold DuhamelT; rw [Set.indicator_of_mem hgood]
  have hY : GUEDuhamelBA_gYst sz A t1 t0 K n e μ I (j + 1) ω
      = DuhamelT sz n Φ v M X - ∫ y, DuhamelT sz n Φ v M y ∂(gueUnit sz) := by
    simp only [GUEDuhamelBA_gYst, hj, ite_true]
    rfl
  have hZ : GUEDuhamelBA_gZinc sz A t1 t0 K n e μ I j ω = DuhamelZ sz n Φ v M X := rfl
  have hr : GUEDuhamelBA_gr sz A t1 t0 K n e μ I j ω
      = (∫ y, Φ (M + Sizes.seqHflow sz n v y) ∂(gueUnit sz))
        - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) (ztOf μ e (gridTime t1 t0 K n j)) I
        - (gridStep t1 t0 K n : ℂ) * genMatGUEOf d (sz.L n) (sz.W n) μ e (gridTime t1 t0 K n j) M I := rfl
  rw [hL1, hY, hZ, hr, hint, hRdef, hT]
  ring

/-- **The grid facts** (`Duhamel_grid_facts`, `DuhamelB:976`) along `ztOf μ e`: `Δ ≥ 0`, `K Δ ≤ 1`, `x⁻¹ ≤ Im z_j ≤ 1`
for `j ≤ K`, `‖z_{j+1} - z_j‖ ≤ Δ` (`= Δ ‖μ‖`; the band has equality, `‖mE E‖ = 1`), `Im z_{j+1} ≤ Im z_j ≤
Im z_{j+1} + Δ` and `u_k - t₁ = k Δ`. -/
private theorem GUEDuhamelBA_grid_facts (hμ : 0 < μ.im) (hμ1 : ‖μ‖ ≤ 1)
    (ht1 : 0 ≤ t1 n) (hst : t1 n ≤ t0 n) (ht0 : t0 n < 1) (hK : 0 < K n)
    {x : ℝ} (heta : x⁻¹ ≤ etaOf μ (t0 n)) :
    0 ≤ gridStep t1 t0 K n ∧ (K n : ℝ) * gridStep t1 t0 K n ≤ 1 ∧
      (∀ j ≤ K n, x⁻¹ ≤ (ztOf μ e (gridTime t1 t0 K n j)).im ∧
        (ztOf μ e (gridTime t1 t0 K n j)).im ≤ 1) ∧
      (∀ j, ‖ztOf μ e (gridTime t1 t0 K n (j + 1)) - ztOf μ e (gridTime t1 t0 K n j)‖
        ≤ gridStep t1 t0 K n) ∧
      (∀ j, (ztOf μ e (gridTime t1 t0 K n (j + 1))).im
            ≤ (ztOf μ e (gridTime t1 t0 K n j)).im ∧
        (ztOf μ e (gridTime t1 t0 K n j)).im
          ≤ (ztOf μ e (gridTime t1 t0 K n (j + 1))).im + gridStep t1 t0 K n) ∧
      (∀ k, gridTime t1 t0 K n k - t1 n = k * gridStep t1 t0 K n) := by
  have hKpos : (0 : ℝ) < (K n : ℝ) := by exact_mod_cast hK
  set Δ := gridStep t1 t0 K n with hΔdef
  have hΔ0 : 0 ≤ Δ := by rw [hΔdef]; unfold gridStep; exact div_nonneg (by linarith) hKpos.le
  have hKΔ : (K n : ℝ) * Δ = t0 n - t1 n := by rw [hΔdef]; unfold gridStep; field_simp
  have htime : ∀ j, gridTime t1 t0 K n j = t1 n + j * Δ := fun j => by
    rw [hΔdef]; rfl
  have hm0 : 0 < μ.im := hμ
  have hm1 : μ.im ≤ 1 := (Complex.im_le_norm _).trans hμ1
  refine ⟨hΔ0, by linarith, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have hj' : (j : ℝ) ≤ (K n : ℝ) := by exact_mod_cast hj
    have hle : gridTime t1 t0 K n j ≤ t0 n := by
      rw [htime]; nlinarith
    have hge : t1 n ≤ gridTime t1 t0 K n j := by
      rw [htime]; have : (0 : ℝ) ≤ j * Δ := by positivity
      linarith
    rw [ztOf_im]
    constructor
    · refine heta.trans ?_
      unfold etaOf
      exact mul_le_mul_of_nonneg_right (by linarith) hm0.le
    · unfold etaOf
      have h1 : 1 - gridTime t1 t0 K n j ≤ 1 := by linarith
      have h0 : 0 ≤ 1 - gridTime t1 t0 K n j := by linarith
      nlinarith
  · intro j
    have key : ztOf μ e (gridTime t1 t0 K n (j + 1)) - ztOf μ e (gridTime t1 t0 K n j)
        = -((Δ : ℂ) * μ) := by
      unfold ztOf
      rw [htime, htime]
      push_cast
      ring
    rw [key, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hΔ0]
    calc Δ * ‖μ‖ ≤ Δ * 1 := mul_le_mul_of_nonneg_left hμ1 hΔ0
      _ = Δ := mul_one _
  · intro j
    rw [ztOf_im, ztOf_im]
    unfold etaOf
    rw [htime, htime]
    push_cast
    constructor
    · nlinarith [mul_nonneg hΔ0 hm0.le]
    · nlinarith [mul_nonneg hΔ0 (sub_nonneg.2 hm1)]
  · intro k; rw [htime]; ring

end Decomp

/-! ## 5. Target 6, public: the BA processes of one step, the pathwise decomposition, the drift remainder

The processes below are the BA twins of `DuhamelPhi`, `DuhamelZinc`, `DuhamelYst`, `Duhamelr` (`DuhamelB:173, 186, 536,
726`) on the BA grid path `gueHBA` along `ztOf m E`; they are the `rfl`-specialisations of the private generic
development above to `sz := sz.withLam 0`, `A n := g Ψ_I`. -/

section BAForm

variable {d : ℕ}

/-- The BA shift `g Ψ_I` of the grid path (`gueHBA` is `g Ψ_I + gueH (sz.withLam 0) …`). -/
private abbrev GUEDuhamelBA_Ash (sz : Sizes d) (g : ℕ → ℝ) (n : ℕ) :
    Matrix (Idx d ((sz.withLam 0).L n) ((sz.withLam 0).W n)) (Idx d ((sz.withLam 0).L n) ((sz.withLam 0).W n)) ℂ :=
  ((g n : ℝ) : ℂ) • PsiI d ((sz.withLam 0).L n) ((sz.withLam 0).W n)

private theorem GUEDuhamelBA_Ash_isHermitian (sz : Sizes d) (g : ℕ → ℝ) (n : ℕ) :
    (GUEDuhamelBA_Ash sz g n).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_smul, (PsiI_isHermitian d _ _).eq,
    show star ((g n : ℝ) : ℂ) = ((g n : ℝ) : ℂ) from Complex.conj_ofReal _]

/-- The Hermitian increment `√v X_y` of the model `sz.withLam 0` (`Sizes.seqHflow`), read as a matrix of the sizes of `sz`
(they agree by `rfl`), so that sums with `gueHBA` have one matrix type. -/
abbrev GUEDuhamelBA_hflow (sz : Sizes d) (n : ℕ) (v : ℝ) (y : Sizes.SeqΩ (sz.withLam 0)) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  Sizes.seqHflow (sz.withLam 0) n v y

/-- **The observable of the step `j → j+1` on the BA grid** (twin of `DuhamelPhi`, `DuhamelB:173`): the loop
`𝓛_{u_{j+1}, I}` at the spectral parameter `ztOf m E u_{j+1}`. -/
def GUEDuhamelBA_Phi (sz : Sizes d) (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (E : ℝ) (m : ℂ)
    (I : LoopIdx (Zd d (sz.L n))) (j : ℕ) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ :=
  fun M => loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) (ztOf m E (gridTime t1 t0 K n (j + 1))) I

/-- **The linear part of the step `j → j+1` on the BA grid path** (twin of `DuhamelZinc`, `DuhamelB:186`). -/
def GUEDuhamelBA_Zinc (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (E : ℝ) (m : ℂ)
    (I : LoopIdx (Zd d (sz.L n))) (j : ℕ) (ω : PathΩ (sz.withLam 0)) : ℂ :=
  DuhamelZ (sz.withLam 0) n (GUEDuhamelBA_Phi sz t1 t0 K n E m I j) (Duhamelv (sz.withLam 0) t1 t0 K n)
    (gueHBA sz g t1 t0 K n j ω) (ω (j + 1))

/-- **The recentred truncated remainders on the BA grid path** (twin of `DuhamelYst`, `DuhamelB:536`; cut off after the
grid horizon). -/
def GUEDuhamelBA_Yst (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (E : ℝ) (m : ℂ)
    (I : LoopIdx (Zd d (sz.L n))) : ℕ → PathΩ (sz.withLam 0) → ℂ
  | 0 => fun _ => 0
  | j + 1 => fun ω => if j < K n then
      DuhamelT (sz.withLam 0) n (GUEDuhamelBA_Phi sz t1 t0 K n E m I j) (Duhamelv (sz.withLam 0) t1 t0 K n)
        (gueHBA sz g t1 t0 K n j ω) (ω (j + 1))
        - ∫ y, DuhamelT (sz.withLam 0) n (GUEDuhamelBA_Phi sz t1 t0 K n E m I j) (Duhamelv (sz.withLam 0) t1 t0 K n)
          (gueHBA sz g t1 t0 K n j ω) y ∂(gueUnit (sz.withLam 0))
      else 0

/-- **The remainder of the step `j → j+1` on the BA grid path** (twin of `Duhamelr`, `DuhamelB:726`): the conditional mean
of the next loop minus the loop and its drift. -/
def GUEDuhamelBA_r (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (E : ℝ) (m : ℂ)
    (I : LoopIdx (Zd d (sz.L n))) (j : ℕ) (ω : PathΩ (sz.withLam 0)) : ℂ :=
  (∫ y, GUEDuhamelBA_Phi sz t1 t0 K n E m I j
      (gueHBA sz g t1 t0 K n j ω + GUEDuhamelBA_hflow sz n (Duhamelv (sz.withLam 0) t1 t0 K n) y)
      ∂(gueUnit (sz.withLam 0)))
    - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω))
        (ztOf m E (gridTime t1 t0 K n j)) I
    - (gridStep t1 t0 K n : ℂ) * genMatGUEOf d (sz.L n) (sz.W n) m E (gridTime t1 t0 K n j)
        (gueHBA sz g t1 t0 K n j ω) I

/-- **Target 6, `Duhamel_step_decompBA`: one step, pathwise** (twin of `Duhamel_step_decomp`, `DuhamelB:739`), on the
truncation set of the new increment: `𝓛_{u_{j+1}}(H_{j+1}) - 𝓛_{u_j}(H_j) - Δ · genMatGUEOf = Z + Ỹ - B + r` at the BA grid
path `H_k = g Ψ_I + …` (`gueHBA`) along `ztOf m E`, `0 < Im m`. -/
theorem Duhamel_step_decompBA (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (E : ℝ) (m : ℂ)
    {I : LoopIdx (Zd d (sz.L n))} (hm : 0 < m.im) (hwf : I.WF) (hst : t1 n ≤ t0 n) (ht0 : t0 n < 1)
    {j : ℕ} (hj : j < K n) (ω : PathΩ (sz.withLam 0)) (hgood : ω (j + 1) ∈ DuhamelGood (sz.withLam 0) n) :
    loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n (j + 1) ω))
        (ztOf m E (gridTime t1 t0 K n (j + 1))) I
        - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω))
            (ztOf m E (gridTime t1 t0 K n j)) I
        - (gridStep t1 t0 K n : ℂ) * genMatGUEOf d (sz.L n) (sz.W n) m E (gridTime t1 t0 K n j)
            (gueHBA sz g t1 t0 K n j ω) I
      = GUEDuhamelBA_Zinc sz g t1 t0 K n E m I j ω + GUEDuhamelBA_Yst sz g t1 t0 K n E m I (j + 1) ω
        - DuhamelB (sz.withLam 0) n (GUEDuhamelBA_Phi sz t1 t0 K n E m I j) (Duhamelv (sz.withLam 0) t1 t0 K n)
            (gueHBA sz g t1 t0 K n j ω)
        + GUEDuhamelBA_r sz g t1 t0 K n E m I j ω :=
  GUEDuhamelBA_step_decomp (sz := sz.withLam 0) (A := GUEDuhamelBA_Ash sz g) (t1 := t1) (t0 := t0) (K := K)
    (n := n) (e := E) (μ := m) (I := I) (GUEDuhamelBA_Ash_isHermitian sz g) hm hwf hst ht0 hj ω hgood

/-- **Target 6, `Duhamel_drift_remainder_aeBA`: the drift remainder** (twin of `Duhamel_drift_remainder_ae`,
`DuhamelA2:1008`): the conditional mean of the next loop (the integral over one unit GUE increment
`seqHflow (Δ/N) y`, `y ~ gueUnit`) minus the loop and its drift `Δ · genMatGUEOf` is bounded, almost surely, by the
envelope of `condExp_loop_drift_gueBA` (C4 b), `16 (ℓ+3)⁴ N⁴ (1 + η_{u_{k+1}}⁻¹)^{ℓ+4} Δ^{3/2}`. -/
theorem Duhamel_drift_remainder_aeBA (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (E : ℝ) (m : ℂ)
    (hm : 0 < m.im) (hm1 : ‖m‖ ≤ 1) {I : LoopIdx (Zd d (sz.L n))} (hwf : I.WF)
    (ht1 : 0 ≤ t1 n) (hst : t1 n ≤ t0 n) (ht0 : t0 n < 1) (hk : k < K n) :
    ∀ᵐ ω ∂(Pgue (sz.withLam 0)),
      ‖(∫ y, loopL d (sz.L n) (sz.W n)
            (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k ω
              + GUEDuhamelBA_hflow sz n (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) y))
            (ztOf m E (gridTime t1 t0 K n (k + 1))) I ∂(gueUnit (sz.withLam 0)))
          - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k ω))
              (ztOf m E (gridTime t1 t0 K n k)) I
          - (gridStep t1 t0 K n : ℂ) * genMatGUEOf d (sz.L n) (sz.W n) m E (gridTime t1 t0 K n k)
              (gueHBA sz g t1 t0 K n k ω) I‖
        ≤ 16 * ((I.length : ℝ) + 3) ^ 4 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) ^ 4 *
            (1 + (etaOf m (gridTime t1 t0 K n (k + 1)))⁻¹) ^ (I.length + 4) *
              gridStep t1 t0 K n ^ ((3 : ℝ) / 2) := by
  have hu1lt : gridTime t1 t0 K n (k + 1) < 1 := by
    have hKpos : (0 : ℝ) < (K n : ℝ) := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le k) hk)
    have hk1 : (k : ℝ) + 1 ≤ (K n : ℝ) := by exact_mod_cast hk
    have hΔ0 : 0 ≤ gridStep t1 t0 K n := by
      unfold gridStep; exact div_nonneg (by linarith) hKpos.le
    have hKΔ : (K n : ℝ) * gridStep t1 t0 K n = t0 n - t1 n := by unfold gridStep; field_simp
    have h : gridTime t1 t0 K n (k + 1) = t1 n + ((k : ℝ) + 1) * gridStep t1 t0 K n := by
      unfold gridTime; push_cast; ring
    rw [h]; nlinarith
  have hz1ne : (ztOf m E (gridTime t1 t0 K n (k + 1))).im ≠ 0 := by
    rw [ztOf_im]
    exact (mul_pos (sub_pos.2 hu1lt) hm).ne'
  set z1 := ztOf m E (gridTime t1 t0 K n (k + 1)) with hz1
  set v := gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ) with hv
  set F : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ →
      Sizes.SeqΩ (sz.withLam 0) → ℂ :=
    fun p y => DuhamelA2_Phi d (sz.L n) (sz.W n) z1 I (p + GUEDuhamelBA_hflow sz n v y) with hF
  have hΦcont := DuhamelA2_continuous_Phi (d := d) (L := sz.L n) (W := sz.W n) hz1ne I
  have hFmeas : Measurable (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ ×
      Sizes.SeqΩ (sz.withLam 0) => F p.1 p.2) :=
    hΦcont.measurable.comp (measurable_fst.add
      ((DuhamelA2_measurable_seqHflow (sz := sz.withLam 0) (n := n) v).comp measurable_snd))
  have hFbdd : ∀ p y, ‖F p y‖ ≤ (((sz.L n * sz.W n) ^ d : ℕ) : ℝ) *
      (|z1.im|⁻¹ * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹)) ^ I.a.length :=
    fun p y => DuhamelA2_norm_Phi_le hz1ne hwf _
  have hFInt : ∀ p, Integrable (F p) (gueUnit (sz.withLam 0)) := by
    intro p
    have hm' : Measurable (fun y : Sizes.SeqΩ (sz.withLam 0) => F p y) := by
      have h := hFmeas.comp (measurable_const.prodMk measurable_id :
        Measurable fun y : Sizes.SeqΩ (sz.withLam 0) => (p, y))
      exact h
    exact (memLp_top_of_bound hm'.aestronglyMeasurable _
      (Eventually.of_forall fun y => hFbdd p y)).integrable le_top
  have hYmeas : Measurable[filt (sz.withLam 0) k] (gueHBA sz g t1 t0 K n k) :=
    GUEDuhamelBA_gH_measurable (sz := sz.withLam 0) (GUEDuhamelBA_Ash sz g) t1 t0 K n k
  have hYmeas' : Measurable (gueHBA sz g t1 t0 K n k) := hYmeas.mono ((filt (sz.withLam 0)).le k) le_rfl
  have hIntTarget : Integrable (fun ω : PathΩ (sz.withLam 0) => F (gueHBA sz g t1 t0 K n k ω) (ω (k + 1)))
      (Pgue (sz.withLam 0)) := by
    have hm' : Measurable (fun ω : PathΩ (sz.withLam 0) => F (gueHBA sz g t1 t0 K n k ω) (ω (k + 1))) := by
      have h := hFmeas.comp (hYmeas'.prodMk (measurable_pi_apply (k + 1)))
      exact h
    exact (memLp_top_of_bound hm'.aestronglyMeasurable _
      (Eventually.of_forall fun ω => hFbdd _ _)).integrable le_top
  have hfreeze := DuhamelA2_condExp_freezeC (sz := sz.withLam 0) k hYmeas hFmeas hFInt hIntTarget
  have hsucc : ∀ ω : PathΩ (sz.withLam 0), gueHBA sz g t1 t0 K n (k + 1) ω
      = gueHBA sz g t1 t0 K n k ω + GUEDuhamelBA_hflow sz n v (ω (k + 1)) :=
    fun ω => gueHBA_succ sz g t1 t0 K n k ω
  have hEq : (fun ω' : PathΩ (sz.withLam 0) =>
        loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n (k + 1) ω'))
          z1 I)
      = fun ω => F (gueHBA sz g t1 t0 K n k ω) (ω (k + 1)) := by
    funext ω
    have hH : (gueHBA sz g t1 t0 K n (k + 1) ω).IsHermitian := gueHBA_isHermitian sz g t1 t0 K n (k + 1) ω
    simp only [hF, DuhamelA2_Phi]
    rw [← hsucc ω, DuhamelA2_herm_of_isHermitian hH]
  have hD3 := condExp_loop_drift_gueBA sz g t1 t0 K n k E m hm hm1 hwf ht1 hst
    (by omega) hk hu1lt
  rw [hEq] at hD3
  filter_upwards [hD3, hfreeze] with ω h1 h2
  rw [h2] at h1
  have hFeq : ∀ y, F (gueHBA sz g t1 t0 K n k ω) y = loopL d (sz.L n) (sz.W n)
      (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k ω + GUEDuhamelBA_hflow sz n v y)) z1 I := by
    intro y
    have hh : (gueHBA sz g t1 t0 K n k ω + GUEDuhamelBA_hflow sz n v y).IsHermitian :=
      (gueHBA_isHermitian sz g t1 t0 K n k ω).add (Sizes.seqHflow_isHermitian (sz.withLam 0) n v y)
    simp only [hF, DuhamelA2_Phi]
    rw [DuhamelA2_herm_of_isHermitian hh]
  simp only [hFeq] at h1
  exact h1

/-- **The conditional variance proxy of the linear part on the BA grid path** (twin of `DuhamelVp`, `DuhamelB:180`). -/
def GUEDuhamelBA_Vp (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (E : ℝ) (m : ℂ)
    (I : LoopIdx (Zd d (sz.L n))) (j : ℕ) (ω : PathΩ (sz.withLam 0)) : ℝ :=
  Duhamelv (sz.withLam 0) t1 t0 K n * max
    (vGue (sz.withLam 0) n (gradMat (GUEDuhamelBA_Phi sz t1 t0 K n E m I j) (gueHBA sz g t1 t0 K n j ω)) : ℝ)
    (vGue (sz.withLam 0) n (-Complex.I • gradMat (GUEDuhamelBA_Phi sz t1 t0 K n E m I j)
      (gueHBA sz g t1 t0 K n j ω)) : ℝ)

/-- **The linear part on the BA grid path, stopped at the dyadic level `lam`** (twin of `DuhamelZst`, `DuhamelB:191`; the
index `0` carries `0`). -/
def GUEDuhamelBA_Zst (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (E : ℝ) (m : ℂ)
    (I : LoopIdx (Zd d (sz.L n))) (lam : ℝ) : ℕ → PathΩ (sz.withLam 0) → ℂ
  | 0 => fun _ => 0
  | j + 1 => {ω | j < firstHit (GUEDuhamelBA_Vp sz g t1 t0 K n E m I) lam (K n) ω}.indicator
      (GUEDuhamelBA_Zinc sz g t1 t0 K n E m I j)

/-- **Target 6, `Duhamel_azuma_ZBA`: Azuma at one dyadic level** (twin of `Duhamel_azuma_Z`, `DuhamelB:341`): the linear part
of the BA grid path, stopped at `firstHit (GUEDuhamelBA_Vp …) lam (K n)`, has the complex Azuma tail with proxy `lam` per
step.  No loop or grid hypothesis is needed. -/
theorem Duhamel_azuma_ZBA (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (E : ℝ) (m : ℂ)
    {I : LoopIdx (Zd d (sz.L n))} {lam : ℝ} (hlam : 0 < lam) (hv : 0 ≤ Duhamelv (sz.withLam 0) t1 t0 K n) (k : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Pgue (sz.withLam 0)).real
        {ω | ε ≤ ‖∑ j ∈ Finset.range k, GUEDuhamelBA_Zst sz g t1 t0 K n E m I lam (j + 1) ω‖}
      ≤ 4 * Real.exp (-ε ^ 2 / (4 * (k * lam))) :=
  GUEDuhamelBA_azuma_Z (sz := sz.withLam 0) (A := GUEDuhamelBA_Ash sz g) (t1 := t1) (t0 := t0) (K := K)
    (n := n) (e := E) (μ := m) (I := I) hlam hv k hε

/-- **Target 6, `Duhamel_azuma_YBA`: Azuma for `Ỹ`** (twin of `Duhamel_azuma_Y`, `DuhamelB:620`): the recentred, truncated
remainders `T - ∫ T` along the BA grid path have the complex Azuma tail with proxy `4 b²` per step, `b` a bound of
`DuhamelT` at Hermitian base points. -/
theorem Duhamel_azuma_YBA (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (E : ℝ) (m : ℂ)
    {I : LoopIdx (Zd d (sz.L n))} {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ j < K n, ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
      M.IsHermitian → ∀ y,
      ‖DuhamelT (sz.withLam 0) n (GUEDuhamelBA_Phi sz t1 t0 K n E m I j) (Duhamelv (sz.withLam 0) t1 t0 K n) M y‖ ≤ b)
    {k : ℕ} (hk : k ≤ K n) {ε : ℝ} (hε : 0 ≤ ε) :
    (Pgue (sz.withLam 0)).real
        {ω | ε ≤ ‖∑ j ∈ Finset.range k, GUEDuhamelBA_Yst sz g t1 t0 K n E m I (j + 1) ω‖}
      ≤ 4 * Real.exp (-ε ^ 2 / (4 * (k * (4 * b ^ 2)))) :=
  GUEDuhamelBA_azuma_Y (sz := sz.withLam 0) (A := GUEDuhamelBA_Ash sz g) (t1 := t1) (t0 := t0) (K := K)
    (n := n) (e := E) (μ := m) (I := I) (GUEDuhamelBA_Ash_isHermitian sz g) hb0 hb hk hε

end BAForm

end RBM.BA

/-! ## 6. Compiled nonempty instances (target 8) of the public theorems of this file

Namespace `RBM.BA.GUEDuhamelBAInst`.  Data: `d = 3`, `sz0` (`L_0 = 4`, `W_0 = 32`, `N_0 = 2097152`, `Defs/Sizes.lean`), the BA flow
datum `(g_n, E_n, m_n)` of `sz0` at every `n` (`BAReal` at `κ = 1/2`: `0 < Im m_n`, `‖m_n‖ ≤ 1`), `t₁ = 17/20`, `t₀ = 9/10`,
`K = 131072` (`Δ = 1/(20 · 131072) > 0`), size index `n = 0`, grid step `k = 0`, the 2-loop `(+,-; 0, 1)` (`0 ≠ 1` in `Z_4^3`),
the zero path `ω = 0`, which lies in the truncation set (`DuhamelA2Inst.zero_mem_good`); every deterministic hypothesis is
discharged. -/

namespace RBM.BA.GUEDuhamelBAInst

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Loop RBM.Univ RBM.Univ.GUEPhase
  RBM.Gauss.SizesInst RBM.BA.FlowPinsInst
open scoped NNReal ENNReal

/-- The flow datum of `sz0` (`BAflowLam0`, `BAflowEs`, `BAmF`): the coupling `g_n`, the energy `E_n`, the profile `m_n`. -/
abbrev gI : ℕ → ℝ := BAflowLam0 sz0 zSeq
abbrev EI : ℕ → ℝ := BAflowEs sz0 zSeq
abbrev mI : ℕ → ℂ := BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)
abbrev t1I : ℕ → ℝ := fun _ => 17 / 20
abbrev t0I : ℕ → ℝ := fun _ => 9 / 10
abbrev KI : ℕ → ℕ := fun _ => 131072

theorem real_I (n : ℕ) : BAReal 3 (sz0.L n) (gI n) (1 / 2) (EI n) (mI n) :=
  BAflow_real (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq flow_sz0 n

theorem im_pos_I (n : ℕ) : 0 < (mI n).im := by linarith [(real_I n).2]

theorem norm_le_I (n : ℕ) : ‖mI n‖ ≤ 1 :=
  BAm_norm_le_one 3 (sz0.L n) (gI n) (EI n : ℂ) (mI n) (by simp) (real_I n).1

/-- The two-loop `(+,-; a₁, a₂)` of the instances, and its well-formedness. -/
def loop2 (L : ℕ) (a₁ a₂ : Zd 3 L) : LoopIdx (Zd 3 L) := ⟨[true, false], [a₁, a₂]⟩

theorem loop2_wf (L : ℕ) (a₁ a₂ : Zd 3 L) : (loop2 L a₁ a₂).WF := rfl

/-- `Duhamel_step_decompBA` at the flow datum of `sz0` (`n = 0`, `j = 0`, the 2-loop `(+,-; 0, 1)`, `ω = 0`). -/
theorem Duhamel_step_decompBA_check :
    loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0)
          (gueHBA sz0 gI t1I t0I KI 0 (0 + 1) (0 : PathΩ (sz0.withLam 0))))
        (ztOf (mI 0) (EI 0) (gridTime t1I t0I KI 0 (0 + 1))) (loop2 (sz0.L 0) 0 1)
      - loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0)
          (gueHBA sz0 gI t1I t0I KI 0 0 (0 : PathΩ (sz0.withLam 0))))
        (ztOf (mI 0) (EI 0) (gridTime t1I t0I KI 0 0)) (loop2 (sz0.L 0) 0 1)
      - (gridStep t1I t0I KI 0 : ℂ) * genMatGUEOf 3 (sz0.L 0) (sz0.W 0) (mI 0) (EI 0) (gridTime t1I t0I KI 0 0)
          (gueHBA sz0 gI t1I t0I KI 0 0 (0 : PathΩ (sz0.withLam 0))) (loop2 (sz0.L 0) 0 1)
    = GUEDuhamelBA_Zinc sz0 gI t1I t0I KI 0 (EI 0) (mI 0) (loop2 (sz0.L 0) 0 1) 0 (0 : PathΩ (sz0.withLam 0))
      + GUEDuhamelBA_Yst sz0 gI t1I t0I KI 0 (EI 0) (mI 0) (loop2 (sz0.L 0) 0 1) (0 + 1) (0 : PathΩ (sz0.withLam 0))
      - DuhamelB (sz0.withLam 0) 0 (GUEDuhamelBA_Phi sz0 t1I t0I KI 0 (EI 0) (mI 0) (loop2 (sz0.L 0) 0 1) 0)
          (Duhamelv (sz0.withLam 0) t1I t0I KI 0) (gueHBA sz0 gI t1I t0I KI 0 0 (0 : PathΩ (sz0.withLam 0)))
      + GUEDuhamelBA_r sz0 gI t1I t0I KI 0 (EI 0) (mI 0) (loop2 (sz0.L 0) 0 1) 0 (0 : PathΩ (sz0.withLam 0)) :=
  Duhamel_step_decompBA sz0 gI t1I t0I KI 0 (EI 0) (mI 0) (I := loop2 (sz0.L 0) 0 1) (im_pos_I 0)
    (loop2_wf _ 0 1) (by norm_num) (by norm_num) (j := 0) (by norm_num) (0 : PathΩ (sz0.withLam 0))
    DuhamelA2Inst.zero_mem_good

/-- `Duhamel_drift_remainder_aeBA` at the flow datum of `sz0` (`n = 0`, `k = 0`, the 2-loop `(+,-; 0, 1)`). -/
theorem Duhamel_drift_remainder_aeBA_check :
    ∀ᵐ ω ∂(Pgue (sz0.withLam 0)),
      ‖(∫ y, loopL 3 (sz0.L 0) (sz0.W 0)
            (blockMat 3 (sz0.L 0) (sz0.W 0) (gueHBA sz0 gI t1I t0I KI 0 0 ω
              + GUEDuhamelBA_hflow sz0 0 (gridStep t1I t0I KI 0 / ((sz0.size 0 : ℕ) : ℝ)) y))
            (ztOf (mI 0) (EI 0) (gridTime t1I t0I KI 0 (0 + 1))) (loop2 (sz0.L 0) 0 1)
            ∂(gueUnit (sz0.withLam 0)))
          - loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0) (gueHBA sz0 gI t1I t0I KI 0 0 ω))
              (ztOf (mI 0) (EI 0) (gridTime t1I t0I KI 0 0)) (loop2 (sz0.L 0) 0 1)
          - (gridStep t1I t0I KI 0 : ℂ) * genMatGUEOf 3 (sz0.L 0) (sz0.W 0) (mI 0) (EI 0)
              (gridTime t1I t0I KI 0 0) (gueHBA sz0 gI t1I t0I KI 0 0 ω) (loop2 (sz0.L 0) 0 1)‖
        ≤ 16 * (((loop2 (sz0.L 0) 0 1).length : ℝ) + 3) ^ 4 * (((sz0.W 0 * sz0.L 0) ^ 3 : ℕ) : ℝ) ^ 4 *
            (1 + (etaOf (mI 0) (gridTime t1I t0I KI 0 (0 + 1)))⁻¹) ^ ((loop2 (sz0.L 0) 0 1).length + 4) *
              gridStep t1I t0I KI 0 ^ ((3 : ℝ) / 2) :=
  Duhamel_drift_remainder_aeBA sz0 gI t1I t0I KI 0 0 (EI 0) (mI 0) (im_pos_I 0) (norm_le_I 0)
    (I := loop2 (sz0.L 0) 0 1) (loop2_wf _ 0 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The grid of the `Ỹ` instance: one step, `K = 1` (`Δ = t₀ - t₁ = 1/20`, `u_1 = t₀`). -/
abbrev KI1 : ℕ → ℕ := fun _ => 1

theorem hv_I : 0 ≤ Duhamelv (sz0.withLam 0) t1I t0I KI 0 := by
  unfold Duhamelv gridStep
  exact div_nonneg (div_nonneg (by norm_num) (by norm_num)) (Nat.cast_nonneg _)

theorem hv_I1 : 0 ≤ Duhamelv (sz0.withLam 0) t1I t0I KI1 0 := by
  unfold Duhamelv gridStep
  exact div_nonneg (div_nonneg (by norm_num) (by norm_num)) (Nat.cast_nonneg _)

/-- `Duhamel_azuma_ZBA` at the flow datum of `sz0` (`n = 0`, the 2-loop `(+,-; 0, 1)`, level `lam = 1`, `k = 3` steps,
`ε = 1`). -/
theorem Duhamel_azuma_ZBA_check :
    (Pgue (sz0.withLam 0)).real
        {ω | (1 : ℝ) ≤ ‖∑ j ∈ Finset.range 3,
          GUEDuhamelBA_Zst sz0 gI t1I t0I KI 0 (EI 0) (mI 0) (loop2 (sz0.L 0) 0 1) 1 (j + 1) ω‖}
      ≤ 4 * Real.exp (-(1 : ℝ) ^ 2 / (4 * (((3 : ℕ) : ℝ) * 1))) :=
  Duhamel_azuma_ZBA sz0 gI t1I t0I KI 0 (EI 0) (mI 0) (I := loop2 (sz0.L 0) 0 1) one_pos hv_I 3 zero_le_one

/-- The `C²`-constant bound `b = C₂/2 · v · N⁴` of `DuhamelT` at the one grid step (`j = 0`) of the `Ỹ` instance, `C₂ = ℓ (ℓ+1) N
η_{u_1}^{-(ℓ+2)}`, `ℓ = 2` (`GUEDuhamelBA_bddC2C_Phi`, `Duhamel_norm_T_le`). -/
abbrev bI : ℝ :=
  (((loop2 (sz0.L 0) 0 1).length * ((loop2 (sz0.L 0) 0 1).length + 1) : ℕ) : ℝ) * (sz0.size 0 : ℝ)
    * (etaOf (mI 0) (gridTime t1I t0I KI1 0 (0 + 1)))⁻¹ ^ ((loop2 (sz0.L 0) 0 1).length + 2) / 2
    * Duhamelv (sz0.withLam 0) t1I t0I KI1 0 * ((sz0.size 0 : ℕ) : ℝ) ^ 4

theorem eta_pos_I1 : 0 < etaOf (mI 0) (gridTime t1I t0I KI1 0 (0 + 1)) := by
  unfold etaOf gridTime gridStep
  have := im_pos_I 0
  norm_num
  positivity

theorem bI_nonneg : 0 ≤ bI := by
  have h1 := eta_pos_I1
  have h2 := hv_I1
  have h3 : (0 : ℝ) ≤ ((sz0.size 0 : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold bI
  positivity

theorem hb_I :
    ∀ j < KI1 0, ∀ M : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ, M.IsHermitian → ∀ y,
      ‖DuhamelT (sz0.withLam 0) 0 (GUEDuhamelBA_Phi sz0 t1I t0I KI1 0 (EI 0) (mI 0) (loop2 (sz0.L 0) 0 1) j)
        (Duhamelv (sz0.withLam 0) t1I t0I KI1 0) M y‖ ≤ bI := by
  intro j hj M hM y
  have hj0 : j = 0 := Nat.lt_one_iff.mp hj
  subst hj0
  obtain ⟨_, hΦ, hC₂⟩ := GUEDuhamelBA_bddC2C_Phi (sz := sz0) (t1 := t1I) (t0 := t0I) (K := KI1) (n := 0)
    (e := EI 0) (μ := mI 0) (I := loop2 (sz0.L 0) 0 1) (im_pos_I 0) (loop2_wf _ 0 1) (by norm_num)
    (by norm_num) hj
  exact Duhamel_norm_T_le hΦ hC₂ hv_I1 hM y

/-- `Duhamel_azuma_YBA` at the flow datum of `sz0` (`n = 0`, the 2-loop `(+,-; 0, 1)`, one grid step `K = 1`, `k = 1`, `ε = 1`,
`b = bI`): `hb` is discharged by the `C²` bound of the loop observable. -/
theorem Duhamel_azuma_YBA_check :
    (Pgue (sz0.withLam 0)).real
        {ω | (1 : ℝ) ≤ ‖∑ j ∈ Finset.range 1,
          GUEDuhamelBA_Yst sz0 gI t1I t0I KI1 0 (EI 0) (mI 0) (loop2 (sz0.L 0) 0 1) (j + 1) ω‖}
      ≤ 4 * Real.exp (-(1 : ℝ) ^ 2 / (4 * (((1 : ℕ) : ℝ) * (4 * bI ^ 2)))) :=
  Duhamel_azuma_YBA sz0 gI t1I t0I KI1 0 (EI 0) (mI 0) (I := loop2 (sz0.L 0) 0 1) (b := bI) bI_nonneg hb_I
    (k := 1) le_rfl (ε := 1) zero_le_one

end RBM.BA.GUEDuhamelBAInst

end
