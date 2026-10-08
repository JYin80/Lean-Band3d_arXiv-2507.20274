/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.GUEPhase.DuhamelA1
import RBM3D.Universality.GUEPhase.DuhamelA2
import RBM3D.Universality.GUEPhase.Markov
import RBM3D.Path.Azuma
import RBM3D.Path.Stop
import RBM3D.Induction.LoopC2N

/-!
# The loop Duhamel tail of the GUE phase, part II (`d ≥ 3`)

Ticket T2349 (UN-38).  Port of RBM2D `Universality/GUEPhase/DuhamelB.lean` (1020 lines, RBM2D
commit `9e0f275`; cited `DB:<line>`): the linear part with dyadic stopping levels and Azuma, the
Taylor remainder with adapted truncation and conditional Hoeffding, the pathwise decomposition of
one step with the dyadic level choice, the deterministic bounds on the variance proxy, and the grid
bookkeeping.  Part III is written against the public declarations below and those of `DuhamelA1`
(T2345) and `DuhamelA2` (T2346).

## Contents

* the observable and the processes: `DuhamelPhi`, `Duhamelv`, `DuhamelVp`, `DuhamelZinc`,
  `DuhamelZst`, `DuhamelYst`, `Duhamelr`;
* `Duhamel_azuma_Z`, `Duhamel_azuma_Y`: Azuma tails for the stopped linear part and for the
  recentred truncated remainders;
* `Duhamel_bddC2C_Phi`, `Duhamel_step_decomp`, `Duhamel_exists_level`: the loop observable is
  `C²` with explicit constants, the pathwise decomposition of one step, the dyadic level;
* `Duhamel_Vp_le`, `Duhamel_qv_le_crude`, `Duhamel_grid_facts`: the bounds on the variance proxy
  and the grid facts.

## Renaming (as T2330, T2343, T2345, T2346)

`d : Sizes` is `sz : Sizes d`; `d.L n`, `d.W n`, `d.size n` are `sz.L n`, `sz.W n`, `sz.size n`
(`= (W L)^d`); `Idx L W` is `Idx d L W`; `Z2 L` is `Zd d L`; `BlockIndex L W` is `Vtx d L W`;
`gloop L W (blockMat M)` is `loopL d L W (blockMat d L W M)`; `spectralZ`, `spectralM` are `zt`,
`mE`; `RBM.Path.etaT` is `RBM.Gauss.etaT`; `RBM.Ind.loopMax L W` is `RBM.Ind.loopMax d L W`;
`gueUnit d`, `Pgue d`, `filt d`, `PathΩ d`, `gueH d`, `vGue d` are the same with `sz`;
`Duhamel_gueH_succ` is the merged `gueH_succ` (`Drift.lean`) read through
`Sizes.seqHflow sz n v y = (√v : ℂ) • seqXmat` (`Sizes.seqHflow_eq_smul`).  RBM2D `norm_green_le`
(`Gauss/Envelope.lean`) is re-derived as the private `DuhamelB_norm_green_le` from the merged
`norm_Gsig_le_inv_eta`.  `Duhamel_Z_re_im`, `Duhamel_measurable_R`, `Duhamel_integral_step`,
`Duhamel_norm_T_le`, `Duhamel_measurable_loop`, `Duhamel_measurable_coord`,
`Duhamel_gueH_measurable_filt` are `DuhamelA2`'s; `Duhamel_vGue_gradMat_le`,
`Duhamel_loopMax_le_crude`, `Duhamel_loopMax_shift_le` are `DuhamelA1`'s.

## Conventions and `d`-dependent lines

* The observable is a `HermTestFun sz n Φ` plus the second-derivative bound at Hermitian points
  (`hermTestFunLoopN`: `C₂ = m (m + 1) s η_{j+1}^{-(m+2)}`, `s = sz.size n = (W L)^d`).  The bound
  `hb` of `Duhamel_azuma_Y` is asked at Hermitian base points only (it is what `Duhamel_norm_T_le`
  gives); the family of `gueHasCondSubgaussianMGF_of_frozen` is cut off by `if M.IsHermitian`.
* `Duhamel_bddC2C_Phi` and `Duhamel_step_decomp` assume `0 ≤ t1 n`, as in the source.
* The Taylor constant is `C₂ = m (m + 1) s η^{-(m+2)}`, `s = sz.size n = (W L)^d`; the loop part
  of the variance proxy cancels the factor `s = ((L:ℝ) W)^d` of `Duhamel_loopMax_shift_le` against
  `Δ / s` (`DuhamelB_size_eq`, `Duhamel_Vp_le`, `Duhamel_qv_le_crude`).  The constants `32`, `4`,
  `m²` contain no `d`.  No statement uses `3 ≤ d`.

The measurability of `linTr`, `vGue`, `seqXmat`, of `gradMat` (`measurable_fderiv_apply_const`),
the `StandardBorelSpace` instance on matrices, and the loop-from-entries rewriting `loopOf σ b = I`
are re-proved here with the prefix `DuhamelB_`.  Compiled nonempty instances: namespace
`RBM.Univ.GUEPhase.DuhamelBInst` (last section).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.LinearForm RBM.Path
  RBM.Loop
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-! ### 0. Private measurability plumbing -/

section Prelim

variable {d : ℕ} {sz : Sizes d}

private theorem DuhamelB_measurable_seqXmat (n : ℕ) : Measurable (Sizes.seqXmat sz n) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j =>
    (measurable_Xentry d (sz.L n) (sz.W n) i j).comp (Sizes.measurable_slice sz n)

private theorem DuhamelB_linTr_eq_sum (n : ℕ)
    (A X : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    linTr n A X = ∑ i : Idx d (sz.L n) (sz.W n), ∑ k : Idx d (sz.L n) (sz.W n), (A i k * X k i).re := by
  unfold linTr
  rw [Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]

private theorem DuhamelB_measurable_linTr_uncurry (n : ℕ) :
    Measurable (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ × Sizes.SeqΩ sz =>
      linTr n p.1 (Sizes.seqXmat sz n p.2)) := by
  have heq : (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ × Sizes.SeqΩ sz =>
      linTr n p.1 (Sizes.seqXmat sz n p.2))
      = fun p => ∑ i : Idx d (sz.L n) (sz.W n), ∑ k : Idx d (sz.L n) (sz.W n),
          (p.1 i k * Sizes.seqXmat sz n p.2 k i).re :=
    funext fun p => DuhamelB_linTr_eq_sum n p.1 (Sizes.seqXmat sz n p.2)
  rw [heq]
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ => ?_
  have hM : Measurable
      (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ × Sizes.SeqΩ sz => p.1 i k) :=
    Measurable.eval_matrix (i := i) (j := k) measurable_fst
  have hX : Measurable
      (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ × Sizes.SeqΩ sz =>
        Sizes.seqXmat sz n p.2 k i) :=
    Measurable.eval_matrix (i := k) (j := i) ((DuhamelB_measurable_seqXmat n).comp measurable_snd)
  exact Complex.measurable_re.comp (hM.mul hX)

private theorem DuhamelB_measurable_linTr_left (n : ℕ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    Measurable (fun A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => linTr n A M) := by
  have heq : (fun A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => linTr n A M)
      = fun A => ∑ i : Idx d (sz.L n) (sz.W n), ∑ k : Idx d (sz.L n) (sz.W n), (A i k * M k i).re :=
    funext fun A => DuhamelB_linTr_eq_sum n A M
  rw [heq]
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ => ?_
  exact Complex.measurable_re.comp
    ((Matrix.measurable_apply (i := i) (j := k)).mul measurable_const)

private theorem DuhamelB_vGue_eq_sum (n : ℕ)
    (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    (vGue sz n A : ℝ) = ∑ c ∈ coordFinset n,
      (linTr n A (Sizes.seqXmat sz n (Pi.single c 1))) ^ 2 * (gueUnitVar sz c : ℝ) := by
  unfold vGue linVar
  push_cast [NNReal.coe_mk]
  rfl

private theorem DuhamelB_measurable_vGue (n : ℕ) :
    Measurable (fun A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      (vGue sz n A : ℝ)) := by
  have heq : (fun A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      (vGue sz n A : ℝ))
      = fun A => ∑ c ∈ coordFinset n,
          (linTr n A (Sizes.seqXmat sz n (Pi.single c 1))) ^ 2 * (gueUnitVar sz c : ℝ) :=
    funext (DuhamelB_vGue_eq_sum n)
  rw [heq]
  exact Finset.measurable_sum _ fun c _ =>
    ((DuhamelB_measurable_linTr_left n _).pow_const 2).mul_const _

/-- The gradient matrix of an arbitrary function is a Borel function of the base point (the entries
are finite combinations of the Borel maps `M ↦ (fderiv ℝ Φ M) y`). -/
private theorem DuhamelB_measurable_gradMat {n : ℕ}
    (Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ) :
    Measurable (gradMat Φ) := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [gradMat, Matrix.of_apply]
  split_ifs
  · exact measurable_fderiv_apply_const ℝ Φ _
  · exact measurable_const.mul (((measurable_fderiv_apply_const ℝ Φ _)).add
      (measurable_const.mul (measurable_fderiv_apply_const ℝ Φ _)))

private instance DuhamelB_standardBorelMatrix (n : ℕ) :
    StandardBorelSpace (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
  inferInstanceAs (StandardBorelSpace (Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ))

end Prelim

/-! ### 1. The linear part: dyadic stopping levels and Azuma  -/

section AzumaZ

variable {d : ℕ} (sz : Sizes d) (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (e : ℝ) (I : LoopIdx (Zd d (sz.L n)))

/-- The observable of the step `j → j+1` (at the spectral parameter of time `u_{j+1}`). -/
def DuhamelPhi (j : ℕ) : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ :=
  fun M => loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) (zt e (gridTime t1 t0 K n (j + 1))) I

/-- The variance `Δ/s` of one GUE increment. -/
def Duhamelv : ℝ := gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)

/-- The conditional variance proxy of the linear part. -/
def DuhamelVp (j : ℕ) (ω : PathΩ sz) : ℝ :=
  Duhamelv sz t1 t0 K n * max
    (vGue sz n (gradMat (DuhamelPhi sz t1 t0 K n e I j) (gueH sz t1 t0 K n j ω)) : ℝ)
    (vGue sz n (-Complex.I • gradMat (DuhamelPhi sz t1 t0 K n e I j) (gueH sz t1 t0 K n j ω)) : ℝ)

/-- The linear part of the step `j → j+1`. -/
def DuhamelZinc (j : ℕ) (ω : PathΩ sz) : ℂ :=
  DuhamelZ sz n (DuhamelPhi sz t1 t0 K n e I j) (Duhamelv sz t1 t0 K n) (gueH sz t1 t0 K n j ω)
    (ω (j + 1))

/-- The linear part, stopped at the dyadic level `lam` (index `0` carries `0`). -/
def DuhamelZst (lam : ℝ) : ℕ → PathΩ sz → ℂ
  | 0 => fun _ => 0
  | j + 1 => {ω | j < firstHit (DuhamelVp sz t1 t0 K n e I) lam (K n) ω}.indicator
      (DuhamelZinc sz t1 t0 K n e I j)

variable {sz t1 t0 K n e I}

private theorem DuhamelB_measurable_A (j : ℕ) :
    Measurable[filt sz j] (fun ω : PathΩ sz =>
      gradMat (DuhamelPhi sz t1 t0 K n e I j) (gueH sz t1 t0 K n j ω)) :=
  (DuhamelB_measurable_gradMat _).comp (Duhamel_gueH_measurable_filt sz t1 t0 K n j)

private theorem DuhamelB_measurable_A' (j : ℕ) :
    Measurable[filt sz j] (fun ω : PathΩ sz =>
      -Complex.I • gradMat (DuhamelPhi sz t1 t0 K n e I j) (gueH sz t1 t0 K n j ω)) := by
  have hA := DuhamelB_measurable_A (sz := sz) (t1 := t1) (t0 := t0) (K := K) (n := n) (e := e)
    (I := I) j
  change Measurable[filt sz j] ((-Complex.I) • (fun ω : PathΩ sz =>
    gradMat (DuhamelPhi sz t1 t0 K n e I j) (gueH sz t1 t0 K n j ω)))
  exact hA.const_smul _

private theorem DuhamelB_adapted_Vp :
    Adapted (filt sz) (DuhamelVp sz t1 t0 K n e I) := by
  intro j
  exact measurable_const.mul (((DuhamelB_measurable_vGue n).comp
    (DuhamelB_measurable_A (e := e) (I := I) j)).max ((DuhamelB_measurable_vGue n).comp
    (DuhamelB_measurable_A' (e := e) (I := I) j)))

private theorem DuhamelB_Zst_re_im (lam : ℝ) (j : ℕ) (ω : PathΩ sz) :
    (DuhamelZst sz t1 t0 K n e I lam (j + 1) ω).re
        = {ω | j < firstHit (DuhamelVp sz t1 t0 K n e I) lam (K n) ω}.indicator
          (fun ω => Real.sqrt (Duhamelv sz t1 t0 K n) * linTr n
            (gradMat (DuhamelPhi sz t1 t0 K n e I j) (gueH sz t1 t0 K n j ω))
            (Sizes.seqXmat sz n (ω (j + 1)))) ω ∧
      (DuhamelZst sz t1 t0 K n e I lam (j + 1) ω).im
        = {ω | j < firstHit (DuhamelVp sz t1 t0 K n e I) lam (K n) ω}.indicator
          (fun ω => Real.sqrt (Duhamelv sz t1 t0 K n) * linTr n
            (-Complex.I • gradMat (DuhamelPhi sz t1 t0 K n e I j) (gueH sz t1 t0 K n j ω))
            (Sizes.seqXmat sz n (ω (j + 1)))) ω := by
  simp only [DuhamelZst, Set.indicator]
  split_ifs
  · exact Duhamel_Z_re_im _ _ _
  · simp

/-- A stopped linear increment is `F_{j+1}`-measurable. -/
private theorem DuhamelB_sm_indicator_lin {j : ℕ} {E : Set (PathΩ sz)}
    (hE : MeasurableSet[filt sz j] E)
    {A : PathΩ sz → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hA : Measurable[filt sz j] A) (s : ℝ) :
    StronglyMeasurable[filt sz (j + 1)]
      (E.indicator (fun ω => s * linTr n (A ω) (Sizes.seqXmat sz n (ω (j + 1))))) := by
  have hle : filt sz j ≤ filt sz (j + 1) := (filt sz).mono (Nat.le_succ j)
  have hX : Measurable[filt sz (j + 1)] (fun ω : PathΩ sz => ω (j + 1)) :=
    Duhamel_measurable_coord sz le_rfl
  have hA1 : Measurable[filt sz (j + 1)] A := hA.mono hle le_rfl
  have hp := hA1.prodMk hX
  have hl := (DuhamelB_measurable_linTr_uncurry (sz := sz) n).comp hp
  have hm : Measurable[filt sz (j + 1)]
      (fun ω : PathΩ sz => s * linTr n (A ω) (Sizes.seqXmat sz n (ω (j + 1)))) :=
    measurable_const.mul hl
  have hE1 : MeasurableSet[filt sz (j + 1)] E := hle _ hE
  exact (hm.indicator hE1).stronglyMeasurable

private theorem DuhamelB_stronglyAdapted_Zst (lam : ℝ) :
    StronglyAdapted (filt sz) (fun i ω => (DuhamelZst sz t1 t0 K n e I lam i ω).re) ∧
      StronglyAdapted (filt sz) (fun i ω => (DuhamelZst sz t1 t0 K n e I lam i ω).im) := by
  have hE : ∀ j, MeasurableSet[filt sz j]
      {ω | j < firstHit (DuhamelVp sz t1 t0 K n e I) lam (K n) ω} :=
    fun j => lt_firstHit_measurableSet _ lam (K n) DuhamelB_adapted_Vp j
  constructor
  · intro i
    rcases i with _ | j
    · exact stronglyMeasurable_const
    · have heq : (fun ω => (DuhamelZst sz t1 t0 K n e I lam (j + 1) ω).re)
          = {ω | j < firstHit (DuhamelVp sz t1 t0 K n e I) lam (K n) ω}.indicator
            (fun ω => Real.sqrt (Duhamelv sz t1 t0 K n) * linTr n
              (gradMat (DuhamelPhi sz t1 t0 K n e I j) (gueH sz t1 t0 K n j ω))
              (Sizes.seqXmat sz n (ω (j + 1)))) :=
        funext fun ω => (DuhamelB_Zst_re_im lam j ω).1
      change StronglyMeasurable[filt sz (j + 1)]
        (fun ω => (DuhamelZst sz t1 t0 K n e I lam (j + 1) ω).re)
      rw [heq]
      exact DuhamelB_sm_indicator_lin (hE j) (DuhamelB_measurable_A j) _
  · intro i
    rcases i with _ | j
    · exact stronglyMeasurable_const
    · have heq : (fun ω => (DuhamelZst sz t1 t0 K n e I lam (j + 1) ω).im)
          = {ω | j < firstHit (DuhamelVp sz t1 t0 K n e I) lam (K n) ω}.indicator
            (fun ω => Real.sqrt (Duhamelv sz t1 t0 K n) * linTr n
              (-Complex.I • gradMat (DuhamelPhi sz t1 t0 K n e I j) (gueH sz t1 t0 K n j ω))
              (Sizes.seqXmat sz n (ω (j + 1)))) :=
        funext fun ω => (DuhamelB_Zst_re_im lam j ω).2
      change StronglyMeasurable[filt sz (j + 1)]
        (fun ω => (DuhamelZst sz t1 t0 K n e I lam (j + 1) ω).im)
      rw [heq]
      exact DuhamelB_sm_indicator_lin (hE j) (DuhamelB_measurable_A' j) _

private theorem DuhamelB_condSubG_Zst {lam : ℝ} (hlam : 0 ≤ lam)
    (hv : 0 ≤ Duhamelv sz t1 t0 K n) (j : ℕ) :
    HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
        (fun ω => (DuhamelZst sz t1 t0 K n e I lam (j + 1) ω).re) ⟨lam, hlam⟩ (Pgue sz) ∧
      HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
        (fun ω => (DuhamelZst sz t1 t0 K n e I lam (j + 1) ω).im) ⟨lam, hlam⟩ (Pgue sz) := by
  have hE : MeasurableSet[filt sz j]
      {ω | j < firstHit (DuhamelVp sz t1 t0 K n e I) lam (K n) ω} :=
    lt_firstHit_measurableSet _ lam (K n) DuhamelB_adapted_Vp j
  have hsq : Real.sqrt (Duhamelv sz t1 t0 K n) ^ 2 = Duhamelv sz t1 t0 K n := Real.sq_sqrt hv
  have hb1 : ∀ ω ∈ {ω | j < firstHit (DuhamelVp sz t1 t0 K n e I) lam (K n) ω},
      Real.sqrt (Duhamelv sz t1 t0 K n) ^ 2 * (vGue sz n
        (gradMat (DuhamelPhi sz t1 t0 K n e I j) (gueH sz t1 t0 K n j ω)) : ℝ)
        ≤ ((⟨lam, hlam⟩ : ℝ≥0) : ℝ) := by
    intro ω hω
    have h := lt_firstHit_imp (DuhamelVp sz t1 t0 K n e I) lam (K n) hω
    rw [hsq]
    refine le_trans ?_ h.le
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) hv
  have hb2 : ∀ ω ∈ {ω | j < firstHit (DuhamelVp sz t1 t0 K n e I) lam (K n) ω},
      Real.sqrt (Duhamelv sz t1 t0 K n) ^ 2 * (vGue sz n
        (-Complex.I • gradMat (DuhamelPhi sz t1 t0 K n e I j) (gueH sz t1 t0 K n j ω)) : ℝ)
        ≤ ((⟨lam, hlam⟩ : ℝ≥0) : ℝ) := by
    intro ω hω
    have h := lt_firstHit_imp (DuhamelVp sz t1 t0 K n e I) lam (K n) hω
    rw [hsq]
    refine le_trans ?_ h.le
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) hv
  have h1 := gueHasCondSubgaussianMGF_linear sz n j (Real.sqrt (Duhamelv sz t1 t0 K n))
    (DuhamelB_measurable_A (e := e) (I := I) j) _ hE _ hb1
  have h2 := gueHasCondSubgaussianMGF_linear sz n j (Real.sqrt (Duhamelv sz t1 t0 K n))
    (DuhamelB_measurable_A' (e := e) (I := I) j) _ hE _ hb2
  constructor
  · have heq : (fun ω => (DuhamelZst sz t1 t0 K n e I lam (j + 1) ω).re)
        = fun ω => {ω | j < firstHit (DuhamelVp sz t1 t0 K n e I) lam (K n) ω}.indicator
            (fun ω => Real.sqrt (Duhamelv sz t1 t0 K n) * linTr n
              (gradMat (DuhamelPhi sz t1 t0 K n e I j) (gueH sz t1 t0 K n j ω))
              (Sizes.seqXmat sz n (ω (j + 1)))) ω :=
      funext fun ω => (DuhamelB_Zst_re_im lam j ω).1
    rw [heq]; exact h1
  · have heq : (fun ω => (DuhamelZst sz t1 t0 K n e I lam (j + 1) ω).im)
        = fun ω => {ω | j < firstHit (DuhamelVp sz t1 t0 K n e I) lam (K n) ω}.indicator
            (fun ω => Real.sqrt (Duhamelv sz t1 t0 K n) * linTr n
              (-Complex.I • gradMat (DuhamelPhi sz t1 t0 K n e I j) (gueH sz t1 t0 K n j ω))
              (Sizes.seqXmat sz n (ω (j + 1)))) ω :=
      funext fun ω => (DuhamelB_Zst_re_im lam j ω).2
    rw [heq]; exact h2

end AzumaZ

/-- **Azuma at one dyadic level**: the linear part stopped
at `firstHit (DuhamelVp …) lam (K n)` has the complex Azuma tail with proxy `lam` per step.  No
loop or grid hypothesis is needed: only `gueHasCondSubgaussianMGF_linear` and `azuma_complex`. -/
theorem Duhamel_azuma_Z {d : ℕ} {sz : Sizes d} {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {e : ℝ}
    {I : LoopIdx (Zd d (sz.L n))} {lam : ℝ} (hlam : 0 < lam) (hv : 0 ≤ Duhamelv sz t1 t0 K n) (k : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Pgue sz).real {ω | ε ≤ ‖∑ j ∈ Finset.range k, DuhamelZst sz t1 t0 K n e I lam (j + 1) ω‖}
      ≤ 4 * Real.exp (-ε ^ 2 / (4 * (k * lam))) := by
  set c : ℕ → ℝ≥0 := fun i => if i = 0 then 0 else ⟨lam, hlam.le⟩ with hc
  obtain ⟨hR, hI⟩ := DuhamelB_stronglyAdapted_Zst (sz := sz) (t1 := t1) (t0 := t0) (K := K)
    (n := n) (e := e) (I := I) lam
  have h0 : HasSubgaussianMGF (fun ω => (DuhamelZst sz t1 t0 K n e I lam 0 ω).re) (c 0)
      (Pgue sz) := by
    simp only [hc, DuhamelZst, Complex.zero_re]
    exact HasSubgaussianMGF.zero
  have h0' : HasSubgaussianMGF (fun ω => (DuhamelZst sz t1 t0 K n e I lam 0 ω).im) (c 0)
      (Pgue sz) := by
    simp only [hc, DuhamelZst, Complex.zero_im]
    exact HasSubgaussianMGF.zero
  have hCR : ∀ i < (k + 1) - 1, HasCondSubgaussianMGF (filt sz i) ((filt sz).le i)
      (fun ω => (DuhamelZst sz t1 t0 K n e I lam (i + 1) ω).re) (c (i + 1)) (Pgue sz) := by
    intro i _
    simp only [hc, Nat.succ_ne_zero]
    exact (DuhamelB_condSubG_Zst hlam.le hv i).1
  have hCI : ∀ i < (k + 1) - 1, HasCondSubgaussianMGF (filt sz i) ((filt sz).le i)
      (fun ω => (DuhamelZst sz t1 t0 K n e I lam (i + 1) ω).im) (c (i + 1)) (Pgue sz) := by
    intro i _
    simp only [hc, Nat.succ_ne_zero]
    exact (DuhamelB_condSubG_Zst hlam.le hv i).2
  have haz := azuma_complex (μ := Pgue sz) (ℱ := filt sz)
    (Z := DuhamelZst sz t1 t0 K n e I lam) (c := c) hR hI (k + 1) h0 h0' hCR hCI hε
  have hsumZ : ∀ ω, ∑ i ∈ Finset.range (k + 1), DuhamelZst sz t1 t0 K n e I lam i ω
      = ∑ j ∈ Finset.range k, DuhamelZst sz t1 t0 K n e I lam (j + 1) ω := by
    intro ω
    rw [Finset.sum_range_succ']
    simp [DuhamelZst]
  have hsumc : ((∑ i ∈ Finset.range (k + 1), c i : ℝ≥0) : ℝ) = k * lam := by
    rw [NNReal.coe_sum, Finset.sum_range_succ']
    have : ∀ i ∈ Finset.range k, (c (i + 1) : ℝ) = lam := fun i _ => by simp [hc]; rfl
    rw [Finset.sum_congr rfl this]
    simp [hc]
  simp only [hsumZ, hsumc] at haz
  exact haz

/-! ### 2. The remainder part: adapted truncation and conditional Hoeffding -/

section AzumaY

variable {d : ℕ} {sz : Sizes d}

/-- The recentred, truncated remainder `T − ∫ T` of one step. -/
private def DuhamelB_FY {n : ℕ}
    (Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ) (v : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (y : Sizes.SeqΩ sz) : ℂ :=
  DuhamelT sz n Φ v M y - ∫ y', DuhamelT sz n Φ v M y' ∂(gueUnit sz)

private theorem DuhamelB_measurable_FY {n : ℕ}
    {Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ} (hΦm : Measurable Φ)
    (v : ℝ) :
    Measurable (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ × Sizes.SeqΩ sz =>
      DuhamelB_FY Φ v p.1 p.2) := by
  have hR := Duhamel_measurable_R (sz := sz) (n := n) hΦm v
  have hTeq : (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ × Sizes.SeqΩ sz =>
        DuhamelT sz n Φ v p.1 p.2)
      = (Set.univ ×ˢ DuhamelGood sz n).indicator (fun p => DuhamelR sz n Φ v p.1 p.2) := by
    funext p
    by_cases h : p.2 ∈ DuhamelGood sz n
    · have h' : p ∈ (Set.univ : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))
          ×ˢ DuhamelGood sz n := Set.mk_mem_prod (Set.mem_univ _) h
      simp only [DuhamelT, Set.indicator_of_mem h, Set.indicator_of_mem h']
    · have h' : p ∉ (Set.univ : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))
          ×ˢ DuhamelGood sz n := fun hp => h (Set.mem_prod.1 hp).2
      simp only [DuhamelT, Set.indicator_of_notMem h, Set.indicator_of_notMem h']
  have hT : Measurable (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ ×
      Sizes.SeqΩ sz => DuhamelT sz n Φ v p.1 p.2) := by
    rw [hTeq]
    exact hR.indicator (MeasurableSet.univ.prod Duhamel_measurableSet_good)
  have hInt : StronglyMeasurable (fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      ∫ y', DuhamelT sz n Φ v M y' ∂(gueUnit sz)) :=
    hT.stronglyMeasurable.integral_prod_right'
  exact hT.sub (hInt.measurable.comp measurable_fst)

private theorem DuhamelB_bound_FY {n : ℕ}
    {Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ} (hΦm : Measurable Φ)
    {v b : ℝ} (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hb : ∀ y, ‖DuhamelT sz n Φ v M y‖ ≤ b) :
    (∀ y, ‖DuhamelB_FY Φ v M y‖ ≤ 2 * b) ∧
      ∫ y, DuhamelB_FY Φ v M y ∂(gueUnit sz) = 0 ∧
      Integrable (DuhamelT sz n Φ v M) (gueUnit sz) := by
  have hTm : Measurable (DuhamelT sz n Φ v M) := by
    have hR := (Duhamel_measurable_R (sz := sz) (n := n) hΦm v).comp
      (measurable_const.prodMk measurable_id : Measurable fun y : Sizes.SeqΩ sz => (M, y))
    exact hR.indicator Duhamel_measurableSet_good
  have hTint : Integrable (DuhamelT sz n Φ v M) (gueUnit sz) :=
    (memLp_top_of_bound hTm.aestronglyMeasurable b
      (Eventually.of_forall fun y => hb y)).integrable le_top
  have hI : ‖∫ y', DuhamelT sz n Φ v M y' ∂(gueUnit sz)‖ ≤ b := by
    have h := norm_integral_le_of_norm_le_const (μ := gueUnit sz)
      (Eventually.of_forall fun y => hb y)
    simpa using h
  refine ⟨fun y => ?_, ?_, hTint⟩
  · unfold DuhamelB_FY
    refine (norm_sub_le _ _).trans ?_
    linarith [hb y]
  · unfold DuhamelB_FY
    rw [integral_sub hTint (integrable_const _), integral_const]
    simp

/-- **Conditional Hoeffding for the recentred remainder**, at a `filt sz j`-measurable Hermitian
base point `Y`.  The family is cut off by
`if M.IsHermitian` (the bound `hb` is only available at Hermitian points), which is harmless since
`Y ω` is Hermitian. -/
private theorem DuhamelB_condSubG_frozen {n j : ℕ}
    {Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ} (hΦm : Measurable Φ)
    {Y : PathΩ sz → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hY : Measurable[filt sz j] Y) (hYh : ∀ ω, (Y ω).IsHermitian) {v b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian →
      ∀ y, ‖DuhamelT sz n Φ v M y‖ ≤ b) :
    HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
        (fun ω => (DuhamelB_FY Φ v (Y ω) (ω (j + 1))).re) ((‖2 * b - -(2 * b)‖₊ / 2) ^ 2)
        (Pgue sz) ∧
      HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
        (fun ω => (DuhamelB_FY Φ v (Y ω) (ω (j + 1))).im) ((‖2 * b - -(2 * b)‖₊ / 2) ^ 2)
        (Pgue sz) := by
  classical
  have hF := DuhamelB_measurable_FY (sz := sz) (n := n) hΦm v
  have hHerm : MeasurableSet {p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ ×
      Sizes.SeqΩ sz | p.1.IsHermitian} := by
    have hcl : IsClosed {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ |
        M.IsHermitian} := isClosed_eq continuous_id.matrix_conjTranspose continuous_id
    exact measurable_fst hcl.measurableSet
  have hsubG : ∀ (g : ℂ → ℝ), Continuous g → (∀ w : ℂ, |g w| ≤ ‖w‖) →
      (∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian →
        ∫ y, g (DuhamelB_FY Φ v M y) ∂(gueUnit sz) = 0) →
      ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
        HasSubgaussianMGF (fun y => if M.IsHermitian then g (DuhamelB_FY Φ v M y) else 0)
          ((‖2 * b - -(2 * b)‖₊ / 2) ^ 2) (gueUnit sz) := by
    intro g hg hgb h0 M
    by_cases hM : M.IsHermitian
    · simp only [hM, ite_true]
      obtain ⟨hB, _, _⟩ := DuhamelB_bound_FY hΦm M (hb M hM)
      refine hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero ?_ ?_ (h0 M hM)
      · exact (hg.measurable.comp (hF.comp (measurable_const.prodMk measurable_id))).aemeasurable
      · refine Eventually.of_forall fun y => ?_
        have h1 := (hgb _).trans (hB y)
        exact ⟨by linarith [neg_abs_le (g (DuhamelB_FY Φ v M y))],
          by linarith [le_abs_self (g (DuhamelB_FY Φ v M y))]⟩
    · simp only [hM, ite_false]
      exact hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero aemeasurable_const
        (Eventually.of_forall fun y => ⟨by linarith, by linarith⟩) (by simp)
  have hre0 : ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian →
      ∫ y, (DuhamelB_FY Φ v M y).re ∂(gueUnit sz) = 0 := by
    intro M hM
    obtain ⟨_, hint0, hTint⟩ := DuhamelB_bound_FY hΦm M (hb M hM)
    have hFint : Integrable (DuhamelB_FY Φ v M) (gueUnit sz) :=
      hTint.sub (integrable_const _)
    have := integral_re hFint
    rw [hint0] at this
    simpa using this
  have him0 : ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian →
      ∫ y, (DuhamelB_FY Φ v M y).im ∂(gueUnit sz) = 0 := by
    intro M hM
    obtain ⟨_, hint0, hTint⟩ := DuhamelB_bound_FY hΦm M (hb M hM)
    have hFint : Integrable (DuhamelB_FY Φ v M) (gueUnit sz) :=
      hTint.sub (integrable_const _)
    have := integral_im hFint
    rw [hint0] at this
    simpa using this
  have hsre := hsubG Complex.re Complex.continuous_re Complex.abs_re_le_norm hre0
  have hsim := hsubG Complex.im Complex.continuous_im Complex.abs_im_le_norm him0
  have hFre : Measurable (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ ×
      Sizes.SeqΩ sz => if p.1.IsHermitian then (DuhamelB_FY Φ v p.1 p.2).re else 0) :=
    Measurable.ite hHerm (Complex.measurable_re.comp hF) measurable_const
  have hFim : Measurable (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ ×
      Sizes.SeqΩ sz => if p.1.IsHermitian then (DuhamelB_FY Φ v p.1 p.2).im else 0) :=
    Measurable.ite hHerm (Complex.measurable_im.comp hF) measurable_const
  have h1 := gueHasCondSubgaussianMGF_of_frozen sz j hY hFre hsre
  have h2 := gueHasCondSubgaussianMGF_of_frozen sz j hY hFim hsim
  have heq1 : (fun ω : PathΩ sz => (DuhamelB_FY Φ v (Y ω) (ω (j + 1))).re)
      = fun ω => (fun (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
          (y : Sizes.SeqΩ sz) => if M.IsHermitian then (DuhamelB_FY Φ v M y).re else 0)
        (Y ω) (ω (j + 1)) := by
    funext ω
    simp only [hYh ω, ite_true]
  have heq2 : (fun ω : PathΩ sz => (DuhamelB_FY Φ v (Y ω) (ω (j + 1))).im)
      = fun ω => (fun (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
          (y : Sizes.SeqΩ sz) => if M.IsHermitian then (DuhamelB_FY Φ v M y).im else 0)
        (Y ω) (ω (j + 1)) := by
    funext ω
    simp only [hYh ω, ite_true]
  rw [heq1, heq2]
  exact ⟨h1, h2⟩

section Defs

variable {d : ℕ} (sz : Sizes d) (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (e : ℝ) (I : LoopIdx (Zd d (sz.L n)))

/-- The martingale increments `Ỹ` (cut off after the grid horizon): `T − ∫ T` for `T = DuhamelT`. -/
def DuhamelYst : ℕ → PathΩ sz → ℂ
  | 0 => fun _ => 0
  | j + 1 => fun ω => if j < K n then
      DuhamelT sz n (DuhamelPhi sz t1 t0 K n e I j) (Duhamelv sz t1 t0 K n)
        (gueH sz t1 t0 K n j ω) (ω (j + 1))
        - ∫ y, DuhamelT sz n (DuhamelPhi sz t1 t0 K n e I j) (Duhamelv sz t1 t0 K n)
          (gueH sz t1 t0 K n j ω) y ∂(gueUnit sz)
      else 0

end Defs

variable {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {e : ℝ} {I : LoopIdx (Zd d (sz.L n))}

private theorem DuhamelB_measurable_Phi (j : ℕ) :
    Measurable (DuhamelPhi sz t1 t0 K n e I j) :=
  Duhamel_measurable_loop _ _

private theorem DuhamelB_Yst_succ {j : ℕ} (hj : j < K n) (ω : PathΩ sz) :
    DuhamelYst sz t1 t0 K n e I (j + 1) ω
      = DuhamelB_FY (DuhamelPhi sz t1 t0 K n e I j) (Duhamelv sz t1 t0 K n)
          (gueH sz t1 t0 K n j ω) (ω (j + 1)) := by
  simp [DuhamelYst, hj, DuhamelB_FY]

private theorem DuhamelB_condSubG_Yst {j : ℕ} (hj : j < K n) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian → ∀ y,
      ‖DuhamelT sz n (DuhamelPhi sz t1 t0 K n e I j) (Duhamelv sz t1 t0 K n) M y‖ ≤ b) :
    HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
        (fun ω => (DuhamelYst sz t1 t0 K n e I (j + 1) ω).re) ((‖2 * b - -(2 * b)‖₊ / 2) ^ 2)
        (Pgue sz) ∧
      HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
        (fun ω => (DuhamelYst sz t1 t0 K n e I (j + 1) ω).im) ((‖2 * b - -(2 * b)‖₊ / 2) ^ 2)
        (Pgue sz) := by
  have h := DuhamelB_condSubG_frozen (sz := sz) (n := n) (j := j) (DuhamelB_measurable_Phi j)
    (Duhamel_gueH_measurable_filt sz t1 t0 K n j) (fun ω => gueH_isHermitian sz t1 t0 K n j ω)
    hb0 hb
  have heq1 : (fun ω => (DuhamelYst sz t1 t0 K n e I (j + 1) ω).re)
      = fun ω => (DuhamelB_FY (DuhamelPhi sz t1 t0 K n e I j) (Duhamelv sz t1 t0 K n)
          (gueH sz t1 t0 K n j ω) (ω (j + 1))).re := by
    funext ω; rw [DuhamelB_Yst_succ hj]
  have heq2 : (fun ω => (DuhamelYst sz t1 t0 K n e I (j + 1) ω).im)
      = fun ω => (DuhamelB_FY (DuhamelPhi sz t1 t0 K n e I j) (Duhamelv sz t1 t0 K n)
          (gueH sz t1 t0 K n j ω) (ω (j + 1))).im := by
    funext ω; rw [DuhamelB_Yst_succ hj]
  rw [heq1, heq2]
  exact h

private theorem DuhamelB_stronglyAdapted_Yst :
    StronglyAdapted (filt sz) (fun i ω => (DuhamelYst sz t1 t0 K n e I i ω).re) ∧
      StronglyAdapted (filt sz) (fun i ω => (DuhamelYst sz t1 t0 K n e I i ω).im) := by
  have key : ∀ j, Measurable[filt sz (j + 1)] (DuhamelYst sz t1 t0 K n e I (j + 1)) := by
    intro j
    by_cases hj : j < K n
    · have hF := DuhamelB_measurable_FY (sz := sz) (n := n)
        (DuhamelB_measurable_Phi (t1 := t1) (t0 := t0) (K := K) (e := e) (I := I) j)
        (Duhamelv sz t1 t0 K n)
      have hle : filt sz j ≤ filt sz (j + 1) := (filt sz).mono (Nat.le_succ j)
      have hY : Measurable[filt sz (j + 1)] (gueH sz t1 t0 K n j) :=
        (Duhamel_gueH_measurable_filt sz t1 t0 K n j).mono hle le_rfl
      have hc : Measurable[filt sz (j + 1)] (fun ω : PathΩ sz => ω (j + 1)) :=
        Duhamel_measurable_coord sz le_rfl
      have hp := hY.prodMk hc
      have hcomp := hF.comp hp
      have heq : DuhamelYst sz t1 t0 K n e I (j + 1)
          = fun ω => DuhamelB_FY (DuhamelPhi sz t1 t0 K n e I j) (Duhamelv sz t1 t0 K n)
              (gueH sz t1 t0 K n j ω) (ω (j + 1)) :=
        funext fun ω => DuhamelB_Yst_succ hj ω
      rw [heq]; exact hcomp
    · have heq : DuhamelYst sz t1 t0 K n e I (j + 1) = fun _ => 0 := by
        funext ω; simp [DuhamelYst, hj]
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

end AzumaY

/-- **Azuma for `Ỹ`**: the recentred, truncated remainders `T − ∫ T` have the complex
Azuma tail with proxy `4 b²` per step, `b` a bound of `‖DuhamelT‖` at Hermitian base points. -/
theorem Duhamel_azuma_Y {d : ℕ} {sz : Sizes d} {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {e : ℝ}
    {I : LoopIdx (Zd d (sz.L n))} {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ j < K n, ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
      M.IsHermitian → ∀ y,
      ‖DuhamelT sz n (DuhamelPhi sz t1 t0 K n e I j) (Duhamelv sz t1 t0 K n) M y‖ ≤ b)
    {k : ℕ} (hk : k ≤ K n) {ε : ℝ} (hε : 0 ≤ ε) :
    (Pgue sz).real {ω | ε ≤ ‖∑ j ∈ Finset.range k, DuhamelYst sz t1 t0 K n e I (j + 1) ω‖}
      ≤ 4 * Real.exp (-ε ^ 2 / (4 * (k * (4 * b ^ 2)))) := by
  set P : ℝ≥0 := (‖2 * b - -(2 * b)‖₊ / 2) ^ 2 with hP
  have hPval : (P : ℝ) = 4 * b ^ 2 := by
    rw [hP]
    push_cast
    rw [Real.norm_eq_abs, show 2 * b - -(2 * b) = 4 * b by ring,
      abs_of_nonneg (by linarith)]
    ring
  set c : ℕ → ℝ≥0 := fun i => if i = 0 then 0 else P with hc
  obtain ⟨hR, hI⟩ := DuhamelB_stronglyAdapted_Yst (sz := sz) (t1 := t1) (t0 := t0) (K := K)
    (n := n) (e := e) (I := I)
  have h0 : HasSubgaussianMGF (fun ω => (DuhamelYst sz t1 t0 K n e I 0 ω).re) (c 0) (Pgue sz) := by
    simp only [hc, DuhamelYst, Complex.zero_re]
    exact HasSubgaussianMGF.zero
  have h0' : HasSubgaussianMGF (fun ω => (DuhamelYst sz t1 t0 K n e I 0 ω).im) (c 0)
      (Pgue sz) := by
    simp only [hc, DuhamelYst, Complex.zero_im]
    exact HasSubgaussianMGF.zero
  have hsub : ∀ i < (k + 1) - 1,
      HasCondSubgaussianMGF (filt sz i) ((filt sz).le i)
        (fun ω => (DuhamelYst sz t1 t0 K n e I (i + 1) ω).re) (c (i + 1)) (Pgue sz) ∧
      HasCondSubgaussianMGF (filt sz i) ((filt sz).le i)
        (fun ω => (DuhamelYst sz t1 t0 K n e I (i + 1) ω).im) (c (i + 1)) (Pgue sz) := by
    intro i hi
    have hiK : i < K n := by omega
    simp only [hc, Nat.succ_ne_zero]
    exact DuhamelB_condSubG_Yst hiK hb0 (hb i hiK)
  have haz := azuma_complex (μ := Pgue sz) (ℱ := filt sz)
    (Z := DuhamelYst sz t1 t0 K n e I) (c := c) hR hI (k + 1) h0 h0'
    (fun i hi => (hsub i hi).1) (fun i hi => (hsub i hi).2) hε
  have hsumZ : ∀ ω, ∑ i ∈ Finset.range (k + 1), DuhamelYst sz t1 t0 K n e I i ω
      = ∑ j ∈ Finset.range k, DuhamelYst sz t1 t0 K n e I (j + 1) ω := by
    intro ω
    rw [Finset.sum_range_succ']
    simp [DuhamelYst]
  have hsumc : ((∑ i ∈ Finset.range (k + 1), c i : ℝ≥0) : ℝ) = k * (4 * b ^ 2) := by
    rw [NNReal.coe_sum, Finset.sum_range_succ']
    have : ∀ i ∈ Finset.range k, (c (i + 1) : ℝ) = 4 * b ^ 2 := fun i _ => by
      simp only [hc, Nat.succ_ne_zero, ite_false]; exact hPval
    rw [Finset.sum_congr rfl this]
    simp [hc]
  simp only [hsumZ, hsumc] at haz
  exact haz

/-! ### 3. The pathwise decomposition of one step, and the dyadic level choice -/

section Decomp

/-- A well-formed loop is `loopOf` of its entries. -/
private theorem DuhamelB_loopOf_eq {d L : ℕ} (J : LoopIdx (Zd d L)) (h : J.WF) :
    loopOf (fun i : Fin J.a.length => J.σ[i.1]'(by rw [h]; exact i.2))
      (fun i : Fin J.a.length => J.a[i.1]) = J := by
  obtain ⟨σ, a⟩ := J
  simp only [LoopIdx.WF] at h
  simp only [loopOf, LoopIdx.mk.injEq]
  refine ⟨?_, List.ofFn_getElem⟩
  exact List.ext_getElem (by simp [h]) (fun i h1 h2 => by simp)

/-- **The loop observable before the horizon is `C²` with explicit constants**.  `ht1 : 0 ≤ t1 n`
is needed because `hermTestFunLoopN` asks `0 ≤ u`. -/
theorem Duhamel_bddC2C_Phi {d : ℕ} {sz : Sizes d} {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {e : ℝ}
    {I : LoopIdx (Zd d (sz.L n))} (he : |e| < 2) (hwf : I.WF) (ht1 : 0 ≤ t1 n)
    (hst : t1 n ≤ t0 n) (ht0 : t0 n < 1) {j : ℕ} (hj : j < K n) :
    (zt e (gridTime t1 t0 K n (j + 1))).im ≠ 0 ∧
      HermTestFun sz n (DuhamelPhi sz t1 t0 K n e I j) ∧
      ∀ M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
        M.IsHermitian → y.IsHermitian →
        ‖fderiv ℝ (fderiv ℝ (DuhamelPhi sz t1 t0 K n e I j)) M y y‖
          ≤ ((I.length * (I.length + 1) : ℕ) : ℝ) * (sz.size n : ℝ)
            * (RBM.Gauss.etaT e (gridTime t1 t0 K n (j + 1)))⁻¹ ^ (I.length + 2) * ‖y‖ ^ 2 := by
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
  have hu0 : 0 ≤ gridTime t1 t0 K n (j + 1) := by
    rw [h]
    have : (0 : ℝ) ≤ ((j : ℝ) + 1) * gridStep t1 t0 K n := by positivity
    linarith
  have hpos : 0 < (1 - gridTime t1 t0 K n (j + 1)) * (mE e).im :=
    mul_pos (by linarith) (mE_im_pos he)
  have hz : (zt e (gridTime t1 t0 K n (j + 1))).im ≠ 0 := by
    rw [zt_im]; exact hpos.ne'
  have h1 := RBM.Ind.hermTestFunLoopN sz I.a.length n e _ he hu0 hu1lt
    (fun i : Fin I.a.length => I.σ[i.1]'(by rw [hwf]; exact i.2))
    (fun i : Fin I.a.length => I.a[i.1])
  rw [DuhamelB_loopOf_eq I hwf] at h1
  exact ⟨hz, h1.1, h1.2⟩

section Defs

variable {d : ℕ} (sz : Sizes d) (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (e : ℝ) (I : LoopIdx (Zd d (sz.L n)))

/-- The remainder of the step `j → j+1`. -/
def Duhamelr (j : ℕ) (ω : PathΩ sz) : ℂ :=
  (∫ y, DuhamelPhi sz t1 t0 K n e I j
      (gueH sz t1 t0 K n j ω + Sizes.seqHflow sz n (Duhamelv sz t1 t0 K n) y) ∂(gueUnit sz))
    - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω))
        (zt e (gridTime t1 t0 K n j)) I
    - (gridStep t1 t0 K n : ℂ) * genMatGUE d (sz.L n) (sz.W n) e (gridTime t1 t0 K n j)
        (gueH sz t1 t0 K n j ω) I

end Defs

/-- **One step, pathwise**, on the truncation set of the new increment:
`𝓛_{u_{j+1}}(H_{j+1}) − 𝓛_{u_j}(H_j) − Δ · gen = Z + Ỹ − B + r`.  `ht1 : 0 ≤ t1 n` is needed as in
`Duhamel_bddC2C_Phi`. -/
theorem Duhamel_step_decomp {d : ℕ} {sz : Sizes d} {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {e : ℝ}
    {I : LoopIdx (Zd d (sz.L n))} (he : |e| < 2) (hwf : I.WF) (ht1 : 0 ≤ t1 n)
    (hst : t1 n ≤ t0 n) (ht0 : t0 n < 1) {j : ℕ} (hj : j < K n) (ω : PathΩ sz)
    (hgood : ω (j + 1) ∈ DuhamelGood sz n) :
    loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n (j + 1) ω))
        (zt e (gridTime t1 t0 K n (j + 1))) I
        - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω))
            (zt e (gridTime t1 t0 K n j)) I
        - (gridStep t1 t0 K n : ℂ) * genMatGUE d (sz.L n) (sz.W n) e (gridTime t1 t0 K n j)
            (gueH sz t1 t0 K n j ω) I
      = DuhamelZinc sz t1 t0 K n e I j ω + DuhamelYst sz t1 t0 K n e I (j + 1) ω
        - DuhamelB sz n (DuhamelPhi sz t1 t0 K n e I j) (Duhamelv sz t1 t0 K n)
            (gueH sz t1 t0 K n j ω)
        + Duhamelr sz t1 t0 K n e I j ω := by
  obtain ⟨_, hΦ, hC₂⟩ := Duhamel_bddC2C_Phi (sz := sz) (t1 := t1) (t0 := t0) (K := K) (n := n)
    (e := e) (I := I) he hwf ht1 hst ht0 hj
  set Φ := DuhamelPhi sz t1 t0 K n e I j with hΦdef
  set v := Duhamelv sz t1 t0 K n with hvdef
  set M := gueH sz t1 t0 K n j ω with hMdef
  set X := ω (j + 1) with hXdef
  have hM : M.IsHermitian := gueH_isHermitian sz t1 t0 K n j ω
  have hsucc : gueH sz t1 t0 K n (j + 1) ω = M + Sizes.seqHflow sz n v X :=
    gueH_succ sz t1 t0 K n j ω
  have hL1 : loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n (j + 1) ω))
      (zt e (gridTime t1 t0 K n (j + 1))) I = Φ (M + Sizes.seqHflow sz n v X) := by
    rw [hΦdef, hsucc]; rfl
  have hint := Duhamel_integral_step hΦ hC₂ v hM
  have hRdef : Φ (M + Sizes.seqHflow sz n v X)
      = Φ M + DuhamelZ sz n Φ v M X + DuhamelR sz n Φ v M X := by
    unfold DuhamelR; ring
  have hT : DuhamelT sz n Φ v M X = DuhamelR sz n Φ v M X := by
    unfold DuhamelT; rw [Set.indicator_of_mem hgood]
  have hY : DuhamelYst sz t1 t0 K n e I (j + 1) ω
      = DuhamelT sz n Φ v M X - ∫ y, DuhamelT sz n Φ v M y ∂(gueUnit sz) := by
    simp only [DuhamelYst, hj, ite_true]
    rfl
  have hZ : DuhamelZinc sz t1 t0 K n e I j ω = DuhamelZ sz n Φ v M X := rfl
  have hr : Duhamelr sz t1 t0 K n e I j ω
      = (∫ y, Φ (M + Sizes.seqHflow sz n v y) ∂(gueUnit sz))
        - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) (zt e (gridTime t1 t0 K n j)) I
        - (gridStep t1 t0 K n : ℂ) * genMatGUE d (sz.L n) (sz.W n) e (gridTime t1 t0 K n j) M I := rfl
  rw [hL1, hY, hZ, hr, hint, hRdef, hT]
  ring

/-- `firstHit` has not stopped before `k` if the process stays below the threshold. -/
private theorem DuhamelB_le_firstHit {Ω' : Type*} {J : ℕ → Ω' → ℝ} {θ : ℝ} {K' k : ℕ} {ω : Ω'}
    (hk : k ≤ K') (h : ∀ j < k, J j ω < θ) : k ≤ firstHit J θ K' ω := by
  by_contra hlt
  push Not at hlt
  have := (MeasureTheory.hittingBtwn_lt_iff (u := J) (s := Set.Ici θ) (n := 0) (ω := ω) k hk).1 hlt
  obtain ⟨j, hj, hjs⟩ := this
  exact absurd (h j hj.2) (not_lt.2 hjs)

/-- **The dyadic level**: some `ℓ ≤ L₀` has
`σ_ℓ ≥ k` and `λ_ℓ ≤ λ₀ + 2Q`. -/
theorem Duhamel_exists_level {Ω' : Type*} {J : ℕ → Ω' → ℝ} {K' k L₀ : ℕ} {ω : Ω'}
    {lam0 Q : ℝ} (hlam0 : 0 < lam0) (hQ : 0 ≤ Q) (hQL : Q < 2 ^ L₀ * lam0) (hk : k ≤ K')
    (hJ : ∀ j < k, J j ω ≤ Q) :
    ∃ ℓ : ℕ, ℓ ≤ L₀ ∧ k ≤ firstHit J (2 ^ ℓ * lam0) K' ω ∧ 2 ^ ℓ * lam0 ≤ lam0 + 2 * Q := by
  classical
  have hex : ∃ ℓ : ℕ, Q < 2 ^ ℓ * lam0 := ⟨L₀, hQL⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hQL, ?_, ?_⟩
  · exact DuhamelB_le_firstHit hk fun j hj => (hJ j hj).trans_lt (Nat.find_spec hex)
  · rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]; simp; linarith
    · have hmin := Nat.find_min hex (Nat.sub_lt hpos one_pos)
      push Not at hmin
      have e : (2 : ℝ) ^ Nat.find hex = 2 * 2 ^ (Nat.find hex - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [e]
      nlinarith

end Decomp

/-! ### 4. Deterministic bounds on the variance proxy  -/

section ProxyBounds

private theorem DuhamelB_size_pos {d : ℕ} (sz : Sizes d) (n : ℕ) : 0 < sz.size n := by
  unfold Sizes.size
  exact pow_pos (Nat.mul_pos (sz.W_pos n) (by have := sz.three_le_L n; omega)) d

/-- `((L : ℝ) W)^d = N`, the `d`-line of the size cancellation (`DB:817`, source `((L : ℝ) W)^2`). -/
private theorem DuhamelB_size_eq {d : ℕ} (sz : Sizes d) (n : ℕ) :
    ((sz.L n : ℝ) * (sz.W n : ℝ)) ^ d = ((sz.size n : ℕ) : ℝ) := by
  unfold Sizes.size; push_cast; ring

/-- `‖(H - z)⁻¹‖ ≤ η⁻¹` for Hermitian `H` and `0 < η ≤ |Im z|` (RBM2D `RBM.Gauss.norm_green_le`,
`Gauss/Envelope.lean`, rebuilt from the merged `norm_Gsig_le_inv_eta`). -/
private theorem DuhamelB_norm_green_le {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|) :
    ‖green H z‖ ≤ η⁻¹ := by
  have h := norm_Gsig_le_inv_eta hH hη hz true
  have e : Gres H z true = green H z := by
    simp only [green, Gres, ↓reduceIte, Matrix.nonsing_inv_eq_ringInverse]
  rwa [e] at h

/-- **The variance proxy of the step `j → j+1`** is controlled by the quadratic variation proxy
at time `u_j`.  The size scale: the matrix dimension is `s = sz.size n` and
`card (Vtx d L W) = (L W)^d = s`; the factor `s` cancels (the `d`-line: source `(L W)²`). -/
theorem Duhamel_Vp_le {d : ℕ} {sz : Sizes d} {n : ℕ}
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian) {z z' : ℂ}
    (hz'pos : 0 < z'.im) (hzz' : z'.im ≤ z.im) (hz2 : z.im ≤ 2 * z'.im) (hz'1 : z'.im ≤ 1)
    {Δ : ℝ} (hΔ : 0 ≤ Δ) (hzd : ‖z' - z‖ ≤ Δ) {I : LoopIdx (Zd d (sz.L n))} (hwf : I.WF) :
    Δ / ((sz.size n : ℕ) : ℝ) * max
        (vGue sz n (gradMat (fun M' : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
          loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M') z' I) M) : ℝ)
        (vGue sz n (-Complex.I • gradMat (fun M' : Matrix (Idx d (sz.L n) (sz.W n))
          (Idx d (sz.L n) (sz.W n)) ℂ => loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M') z' I) M) : ℝ)
      ≤ 32 * (I.length : ℝ) ^ 2 * Δ * (((sz.size n : ℕ) : ℝ)⁻¹ * (z.im)⁻¹ ^ 2
          * RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) z (2 * I.length)
          + 2 * I.length * (z'.im)⁻¹ ^ (2 * I.length + 4) * Δ) := by
  set S : ℝ := ((sz.size n : ℕ) : ℝ) with hS
  set m : ℕ := I.length with hm
  have hzpos : 0 < z.im := lt_of_lt_of_le hz'pos hzz'
  have hS0 : 0 < S := by rw [hS]; exact_mod_cast DuhamelB_size_pos sz n
  have hS1 : 1 ≤ S := by
    rw [hS]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (DuhamelB_size_pos sz n).ne'
  set K' : ℝ := (z'.im)⁻¹ with hK'
  have hK'1 : 1 ≤ K' := by rw [hK']; exact one_le_inv₀ hz'pos |>.2 hz'1
  have hK'0 : 0 ≤ K' := by linarith
  have hzinv : (z.im)⁻¹ ≤ K' := inv_anti₀ hz'pos hzz'
  have hz'ne : z'.im ≠ 0 := hz'pos.ne'
  have hzne : z.im ≠ 0 := hzpos.ne'
  have hMb : (blockMat d (sz.L n) (sz.W n) M).IsHermitian := hM.submatrix _
  -- the variance bound at `z'`
  have hv := Duhamel_vGue_gradMat_le (sz := sz) (n := n) hz'ne hwf hM
  rw [abs_of_pos hz'pos] at hv
  -- the shift of `loopMax`
  have hG : ‖green (blockMat d (sz.L n) (sz.W n) M) z‖ ≤ K' :=
    (DuhamelB_norm_green_le hMb hzpos (by rw [abs_of_pos hzpos])).trans hzinv
  have hG' : ‖green (blockMat d (sz.L n) (sz.W n) M) z'‖ ≤ K' :=
    (DuhamelB_norm_green_le hMb hz'pos (by rw [abs_of_pos hz'pos])).trans (le_of_eq rfl)
  have hsh := Duhamel_loopMax_shift_le (L := sz.L n) (W := sz.W n) hMb hzne hz'ne hK'1 hG hG'
    (2 * m)
  rw [DuhamelB_size_eq] at hsh
  have hsh' : RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) z' (2 * m)
      ≤ RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) z (2 * m)
        + S * (2 * m) * K' ^ (2 * m) * (Δ * K' ^ 2) := by
    refine hsh.trans (add_le_add le_rfl ?_)
    have : (0 : ℝ) ≤ S * ((2 * m : ℕ) : ℝ) * K' ^ (2 * m) := by positivity
    have h2 : ‖z' - z‖ * K' ^ 2 ≤ Δ * K' ^ 2 := mul_le_mul_of_nonneg_right hzd (by positivity)
    calc S * ((2 * m : ℕ) : ℝ) * K' ^ (2 * m) * (‖z' - z‖ * K' ^ 2)
        ≤ S * ((2 * m : ℕ) : ℝ) * K' ^ (2 * m) * (Δ * K' ^ 2) :=
          mul_le_mul_of_nonneg_left h2 this
      _ = _ := by push_cast; ring
  have hratio : K' ^ 2 ≤ 4 * (z.im)⁻¹ ^ 2 := by
    rw [hK']
    have : (z'.im)⁻¹ ≤ 2 * (z.im)⁻¹ := by
      rw [inv_le_iff_one_le_mul₀ hz'pos]
      have : z.im * (z.im)⁻¹ = 1 := mul_inv_cancel₀ hzne
      nlinarith [inv_pos.2 hzpos]
    have h0 : 0 ≤ (z'.im)⁻¹ := by positivity
    nlinarith
  have hLM0 : 0 ≤ RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) z (2 * m) :=
    RBM.Ind.loopMax_nonneg _
  have hLM'0 : 0 ≤ RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) z' (2 * m) :=
    RBM.Ind.loopMax_nonneg _
  have hzinv2 : (z.im)⁻¹ ^ 2 ≤ K' ^ 2 := pow_le_pow_left₀ (by positivity) hzinv 2
  set LM := RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) z (2 * m) with hLM
  set LM' := RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) z' (2 * m) with hLM'
  set V := max (vGue sz n (gradMat (fun M' : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
          loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M') z' I) M) : ℝ)
        (vGue sz n (-Complex.I • gradMat (fun M' : Matrix (Idx d (sz.L n) (sz.W n))
          (Idx d (sz.L n) (sz.W n)) ℂ => loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M') z' I) M) : ℝ)
    with hVdef
  set a := (z.im)⁻¹ with ha
  have ha0 : 0 ≤ a := by positivity
  have hn0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hE0 : 0 ≤ S * (2 * m) * K' ^ (2 * m) * (Δ * K' ^ 2) := by positivity
  have step1 : V ≤ 8 * ((m : ℝ) ^ 2 * (4 * a ^ 2)
      * (LM + S * (2 * m) * K' ^ (2 * m) * (Δ * K' ^ 2))) := by
    refine hv.trans ?_
    have h1 : (m : ℝ) ^ 2 * K' ^ 2 ≤ (m : ℝ) ^ 2 * (4 * a ^ 2) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    have h2 : (m : ℝ) ^ 2 * K' ^ 2 * LM' ≤ (m : ℝ) ^ 2 * (4 * a ^ 2)
        * (LM + S * (2 * m) * K' ^ (2 * m) * (Δ * K' ^ 2)) :=
      mul_le_mul h1 hsh' hLM'0 (by positivity)
    linarith
  have hΔS : 0 ≤ Δ / S := div_nonneg hΔ hS0.le
  have step2 : Δ / S * V ≤ Δ / S * (8 * ((m : ℝ) ^ 2 * (4 * a ^ 2)
      * (LM + S * (2 * m) * K' ^ (2 * m) * (Δ * K' ^ 2)))) :=
    mul_le_mul_of_nonneg_left step1 hΔS
  have step3 : Δ / S * (8 * ((m : ℝ) ^ 2 * (4 * a ^ 2)
      * (LM + S * (2 * m) * K' ^ (2 * m) * (Δ * K' ^ 2))))
      = 32 * (m : ℝ) ^ 2 * Δ * (S⁻¹ * a ^ 2 * LM + 2 * m * (a ^ 2 * K' ^ (2 * m + 2)) * Δ) := by
    have hSne : S ≠ 0 := hS0.ne'
    rw [div_eq_mul_inv]
    have e1 : K' ^ (2 * m) * K' ^ 2 = K' ^ (2 * m + 2) := by rw [← pow_add]
    calc Δ * S⁻¹ * (8 * ((m : ℝ) ^ 2 * (4 * a ^ 2)
          * (LM + S * (2 * m) * K' ^ (2 * m) * (Δ * K' ^ 2))))
        = 32 * (m : ℝ) ^ 2 * Δ * (S⁻¹ * a ^ 2 * LM
            + 2 * m * (a ^ 2 * (K' ^ (2 * m) * K' ^ 2)) * Δ * (S⁻¹ * S)) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hSne, e1, mul_one]
  have h4 : a ^ 2 * K' ^ (2 * m + 2) ≤ K' ^ (2 * m + 4) := by
    calc a ^ 2 * K' ^ (2 * m + 2) ≤ K' ^ 2 * K' ^ (2 * m + 2) :=
          mul_le_mul_of_nonneg_right hzinv2 (by positivity)
      _ = K' ^ (2 * m + 4) := by rw [← pow_add]; congr 1; ring
  have step4 : 32 * (m : ℝ) ^ 2 * Δ * (S⁻¹ * a ^ 2 * LM + 2 * m * (a ^ 2 * K' ^ (2 * m + 2)) * Δ)
      ≤ 32 * (m : ℝ) ^ 2 * Δ * (S⁻¹ * a ^ 2 * LM + 2 * m * K' ^ (2 * m + 4) * Δ) := by
    have h5 : 2 * m * (a ^ 2 * K' ^ (2 * m + 2)) * Δ ≤ 2 * m * K' ^ (2 * m + 4) * Δ := by
      have := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 2 * m)
      exact mul_le_mul_of_nonneg_right this hΔ
    have h6 : 0 ≤ 32 * (m : ℝ) ^ 2 * Δ := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) h6
  calc Δ / S * V ≤ _ := step2
    _ = _ := step3
    _ ≤ _ := step4

/-- **Crude bound**: `s⁻¹ η⁻² L^{(m)} ≤ η^{-(m+2)}`. -/
theorem Duhamel_qv_le_crude {d : ℕ} {sz : Sizes d} {n : ℕ}
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (m : ℕ) :
    ((sz.size n : ℕ) : ℝ)⁻¹ * (z.im)⁻¹ ^ 2
        * RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) z m
      ≤ (z.im)⁻¹ ^ (m + 2) := by
  have hMb : (blockMat d (sz.L n) (sz.W n) M).IsHermitian := hM.submatrix _
  have h := Duhamel_loopMax_le_crude (L := sz.L n) (W := sz.W n) hMb hz.ne' m
  rw [abs_of_pos hz, DuhamelB_size_eq] at h
  have hS : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast DuhamelB_size_pos sz n
  calc ((sz.size n : ℕ) : ℝ)⁻¹ * (z.im)⁻¹ ^ 2
        * RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) z m
      ≤ ((sz.size n : ℕ) : ℝ)⁻¹ * (z.im)⁻¹ ^ 2
          * (((sz.size n : ℕ) : ℝ) * (z.im)⁻¹ ^ m) := by gcongr
    _ = ((((sz.size n : ℕ) : ℝ))⁻¹ * ((sz.size n : ℕ) : ℝ))
          * ((z.im)⁻¹ ^ 2 * (z.im)⁻¹ ^ m) := by ring
    _ = (z.im)⁻¹ ^ (m + 2) := by rw [inv_mul_cancel₀ hS.ne', one_mul, ← pow_add, add_comm]

end ProxyBounds

/-! ### 5. Grid bookkeeping -/

section GridFacts

/-- **The grid facts**: `Δ ≥ 0`, `K Δ ≤ 1`, `x⁻¹ ≤ Im z_j ≤ 1`
for `j ≤ K`, `‖z_{j+1} − z_j‖ = Δ`, `Im z_{j+1} ≤ Im z_j ≤ Im z_{j+1} + Δ` and `u_k − t₁ = k Δ`,
with `z_j = zt e u_j` (RBM2D `spectralZ`, `spectralM` are `zt`, `mE`). -/
theorem Duhamel_grid_facts {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {e : ℝ} (he : |e| < 2)
    (ht1 : 0 ≤ t1 n) (hst : t1 n ≤ t0 n) (ht0 : t0 n < 1) (hK : 0 < K n)
    {x : ℝ} (heta : x⁻¹ ≤ RBM.Gauss.etaT e (t0 n)) :
    0 ≤ gridStep t1 t0 K n ∧ (K n : ℝ) * gridStep t1 t0 K n ≤ 1 ∧
      (∀ j ≤ K n, x⁻¹ ≤ (zt e (gridTime t1 t0 K n j)).im ∧
        (zt e (gridTime t1 t0 K n j)).im ≤ 1) ∧
      (∀ j, ‖zt e (gridTime t1 t0 K n (j + 1)) - zt e (gridTime t1 t0 K n j)‖
        = gridStep t1 t0 K n) ∧
      (∀ j, (zt e (gridTime t1 t0 K n (j + 1))).im
            ≤ (zt e (gridTime t1 t0 K n j)).im ∧
        (zt e (gridTime t1 t0 K n j)).im
          ≤ (zt e (gridTime t1 t0 K n (j + 1))).im + gridStep t1 t0 K n) ∧
      (∀ k, gridTime t1 t0 K n k - t1 n = k * gridStep t1 t0 K n) := by
  have hKpos : (0 : ℝ) < (K n : ℝ) := by exact_mod_cast hK
  set Δ := gridStep t1 t0 K n with hΔdef
  have hΔ0 : 0 ≤ Δ := by rw [hΔdef]; unfold gridStep; exact div_nonneg (by linarith) hKpos.le
  have hKΔ : (K n : ℝ) * Δ = t0 n - t1 n := by rw [hΔdef]; unfold gridStep; field_simp
  have htime : ∀ j, gridTime t1 t0 K n j = t1 n + j * Δ := fun j => by
    rw [hΔdef]; rfl
  have hm0 : 0 < (mE e).im := mE_im_pos he
  have hm1 : (mE e).im ≤ 1 :=
    le_of_abs_le ((Complex.abs_im_le_norm _).trans (norm_mE he.le).le)
  have hmn : ‖mE e‖ = 1 := norm_mE he.le
  refine ⟨hΔ0, by linarith, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have hj' : (j : ℝ) ≤ (K n : ℝ) := by exact_mod_cast hj
    have hle : gridTime t1 t0 K n j ≤ t0 n := by
      rw [htime]; nlinarith
    have hge : t1 n ≤ gridTime t1 t0 K n j := by
      rw [htime]; have : (0 : ℝ) ≤ j * Δ := by positivity
      linarith
    rw [zt_im]
    constructor
    · refine heta.trans ?_
      unfold RBM.Gauss.etaT
      exact mul_le_mul_of_nonneg_right (by linarith) hm0.le
    · have h1 : 1 - gridTime t1 t0 K n j ≤ 1 := by linarith
      have h0 : 0 ≤ 1 - gridTime t1 t0 K n j := by linarith
      nlinarith
  · intro j
    have key : zt e (gridTime t1 t0 K n (j + 1)) - zt e (gridTime t1 t0 K n j)
        = -((Δ : ℂ) * mE e) := by
      unfold zt
      rw [htime, htime]
      push_cast
      ring
    rw [key, norm_neg, norm_mul, hmn, mul_one, Complex.norm_real, Real.norm_of_nonneg hΔ0]
  · intro j
    rw [zt_im, zt_im, htime, htime]
    push_cast
    constructor
    · nlinarith [mul_nonneg hΔ0 hm0.le]
    · nlinarith [mul_nonneg hΔ0 (sub_nonneg.2 hm1)]
  · intro k; rw [htime]; ring

end GridFacts

end RBM.Univ.GUEPhase

/-! ### 6. Compiled nonempty instances

Namespace `RBM.Univ.GUEPhase.DuhamelBInst`.  Data: the merged `sz0` of `RBM3D/Defs/Sizes.lean`
(`d = 3`, `L_0 = 4`, `W_0 = 32`, `N = (W L)^d = 2097152`), size index `n = 0`, energy `e = 0`
(`|e| < 2`, `mE 0 = I`), the `Grid.lean` §`GridCheck` grid `t₀ = 9/10`, `t₁ = e^{-1/20} t₀`,
`K = 4`, and the two-loop `(+,-; 0, 1)` (`m = 2`, `I.WF`).  Every deterministic hypothesis of every
target is discharged: `0 ≤ t₁ ≤ t₀ < 1`, `0 < K`, `j < K`, `x⁻¹ = η_{t₀} = 1/10` (`x = 10`),
`0 < Im z' ≤ Im z ≤ 2 Im z'`, `Im z' ≤ 1`, `‖z' - z‖ = Δ`, `ω (j+1) ∈ DuhamelGood` (`ω = 0`),
`0 < λ₀`, `0 ≤ Q < 2^{L₀} λ₀`, `0 ≤ b`.  There is no external hypothesis. -/


namespace RBM.Univ.GUEPhase.DuhamelBInst

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Univ
  RBM.Gauss.SizesInst RBM.Univ.GUEPhase RBM.Loop
open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev DuhamelBInst_t1 : ℕ → ℝ := fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)
private abbrev DuhamelBInst_t0 : ℕ → ℝ := fun _ => 9 / 10
private abbrev DuhamelBInst_K : ℕ → ℕ := fun _ => 4
private abbrev DuhamelBInst_loop : LoopIdx (Zd 3 (sz0.L 0)) := ⟨[true, false], [0, 1]⟩

private theorem DuhamelBInst_t1_nonneg : 0 ≤ DuhamelBInst_t1 0 := by
  unfold DuhamelBInst_t1 ouZeta
  have := Real.exp_pos (-(1 / 20 : ℝ))
  nlinarith

private theorem DuhamelBInst_t1_le_t0 : DuhamelBInst_t1 0 ≤ DuhamelBInst_t0 0 := by
  unfold DuhamelBInst_t1 DuhamelBInst_t0 ouZeta
  have : Real.exp (-(1 / 20 : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  nlinarith

private abbrev DuhamelBInst_Δ : ℝ := gridStep DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0

private abbrev DuhamelBInst_z (j : ℕ) : ℂ :=
  zt 0 (gridTime DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 j)

private theorem DuhamelBInst_mE_im : (mE 0).im = 1 := by
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp [mE, h4]

private theorem DuhamelBInst_eta : (10 : ℝ)⁻¹ ≤ RBM.Gauss.etaT 0 (DuhamelBInst_t0 0) := by
  unfold RBM.Gauss.etaT DuhamelBInst_t0
  rw [DuhamelBInst_mE_im]
  norm_num

/-- `Duhamel_grid_facts` at the `GridCheck` data (`t₀ = 9/10`, `t₁ = e^{-1/20} t₀`, `K = 4`),
`n = 0`, `e = 0`, `x = 10` (`x⁻¹ = η_{t₀} = 1/10`). -/
theorem grid_facts_check :
    0 ≤ DuhamelBInst_Δ ∧ (DuhamelBInst_K 0 : ℝ) * DuhamelBInst_Δ ≤ 1 ∧
      (∀ j ≤ DuhamelBInst_K 0, (10 : ℝ)⁻¹ ≤ (DuhamelBInst_z j).im ∧ (DuhamelBInst_z j).im ≤ 1) ∧
      (∀ j, ‖DuhamelBInst_z (j + 1) - DuhamelBInst_z j‖ = DuhamelBInst_Δ) ∧
      (∀ j, (DuhamelBInst_z (j + 1)).im ≤ (DuhamelBInst_z j).im ∧
        (DuhamelBInst_z j).im ≤ (DuhamelBInst_z (j + 1)).im + DuhamelBInst_Δ) ∧
      (∀ k, gridTime DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 k - DuhamelBInst_t1 0
        = k * DuhamelBInst_Δ) :=
  Duhamel_grid_facts (t1 := DuhamelBInst_t1) (t0 := DuhamelBInst_t0) (K := DuhamelBInst_K)
    (n := 0) (e := 0) (by norm_num) DuhamelBInst_t1_nonneg DuhamelBInst_t1_le_t0 (by norm_num)
    (by norm_num) DuhamelBInst_eta

/-- `Δ ≤ 1/80` (`1 - e^{-1/20} ≤ 1/20`). -/
private theorem DuhamelBInst_Δ_le : DuhamelBInst_Δ ≤ 1 / 80 := by
  unfold DuhamelBInst_Δ gridStep DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K ouZeta
  have h := Real.add_one_le_exp (-(1 / 20 : ℝ))
  norm_num
  nlinarith

private theorem DuhamelBInst_Δ_nonneg : 0 ≤ DuhamelBInst_Δ := grid_facts_check.1

private theorem DuhamelBInst_im_ge (j : ℕ) (hj : j ≤ 4) : (10 : ℝ)⁻¹ ≤ (DuhamelBInst_z j).im :=
  (grid_facts_check.2.2.1 j hj).1

private theorem DuhamelBInst_v_nonneg :
    0 ≤ Duhamelv sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 :=
  div_nonneg DuhamelBInst_Δ_nonneg (Nat.cast_nonneg _)

/-! #### `Duhamel_bddC2C_Phi`, `Duhamel_step_decomp` -/

theorem bddC2C_Phi_check (j : ℕ) (hj : j < 4) :
    (DuhamelBInst_z (j + 1)).im ≠ 0 ∧
      HermTestFun sz0 0 (DuhamelPhi sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 0
        DuhamelBInst_loop j) ∧
      ∀ M y : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ,
        M.IsHermitian → y.IsHermitian →
        ‖fderiv ℝ (fderiv ℝ (DuhamelPhi sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 0
            DuhamelBInst_loop j)) M y y‖
          ≤ ((DuhamelBInst_loop.length * (DuhamelBInst_loop.length + 1) : ℕ) : ℝ)
            * (sz0.size 0 : ℝ) * (RBM.Gauss.etaT 0 (gridTime DuhamelBInst_t1 DuhamelBInst_t0
              DuhamelBInst_K 0 (j + 1)))⁻¹ ^ (DuhamelBInst_loop.length + 2) * ‖y‖ ^ 2 :=
  Duhamel_bddC2C_Phi (sz := sz0) (t1 := DuhamelBInst_t1) (t0 := DuhamelBInst_t0)
    (K := DuhamelBInst_K) (n := 0) (e := 0) (I := DuhamelBInst_loop) (by norm_num) rfl
    DuhamelBInst_t1_nonneg DuhamelBInst_t1_le_t0 (by norm_num) hj

theorem step_decomp_check (j : ℕ) (hj : j < 4) :
    loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0)
        (gueH sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 (j + 1) 0))
        (DuhamelBInst_z (j + 1)) DuhamelBInst_loop
      - loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0)
          (gueH sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 j 0))
          (DuhamelBInst_z j) DuhamelBInst_loop
      - (DuhamelBInst_Δ : ℂ) * genMatGUE 3 (sz0.L 0) (sz0.W 0) 0
          (gridTime DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 j)
          (gueH sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 j 0) DuhamelBInst_loop
    = DuhamelZinc sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 0 DuhamelBInst_loop j 0
        + DuhamelYst sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 0 DuhamelBInst_loop
          (j + 1) 0
        - DuhamelB sz0 0 (DuhamelPhi sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 0
            DuhamelBInst_loop j) (Duhamelv sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0)
            (gueH sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 j 0)
        + Duhamelr sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 0 DuhamelBInst_loop j 0 :=
  Duhamel_step_decomp (sz := sz0) (t1 := DuhamelBInst_t1) (t0 := DuhamelBInst_t0)
    (K := DuhamelBInst_K) (n := 0) (e := 0) (I := DuhamelBInst_loop) (by norm_num) rfl
    DuhamelBInst_t1_nonneg DuhamelBInst_t1_le_t0 (by norm_num) hj 0
    DuhamelA2Inst.zero_mem_good

/-! #### `Duhamel_Vp_le`, `Duhamel_qv_le_crude` -/

/-- `Duhamel_Vp_le` at every grid step `j < 4` and every path `ω`: the variance proxy
`DuhamelVp` of the step against the loop quantity at `u_j`. -/
theorem Vp_le_check (j : ℕ) (hj : j < 4) (ω : PathΩ sz0) :
    DuhamelVp sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 0 DuhamelBInst_loop j ω
      ≤ 32 * (DuhamelBInst_loop.length : ℝ) ^ 2 * DuhamelBInst_Δ
        * (((sz0.size 0 : ℕ) : ℝ)⁻¹ * (DuhamelBInst_z j).im⁻¹ ^ 2
            * RBM.Ind.loopMax 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0)
              (gueH sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 j ω))
              (DuhamelBInst_z j) (2 * DuhamelBInst_loop.length)
          + 2 * DuhamelBInst_loop.length
            * (DuhamelBInst_z (j + 1)).im⁻¹ ^ (2 * DuhamelBInst_loop.length + 4)
            * DuhamelBInst_Δ) := by
  have h1 := DuhamelBInst_im_ge (j + 1) (by omega)
  have hz'pos : 0 < (DuhamelBInst_z (j + 1)).im := lt_of_lt_of_le (by norm_num) h1
  have hfac := grid_facts_check.2.2.2.2.1 j
  have hle1 := (grid_facts_check.2.2.1 (j + 1) (Nat.succ_le_of_lt hj)).2
  have hΔ := DuhamelBInst_Δ_le
  exact Duhamel_Vp_le (sz := sz0) (M := gueH sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 j ω)
    (gueH_isHermitian sz0 _ _ _ 0 j ω) (z := DuhamelBInst_z j) (z' := DuhamelBInst_z (j + 1))
    hz'pos hfac.1 (by linarith [hfac.2]) hle1 DuhamelBInst_Δ_nonneg
    (grid_facts_check.2.2.2.1 j).le (I := DuhamelBInst_loop) rfl

/-- `Duhamel_qv_le_crude` at the grid point `u_0`, the loop length `m = 2`, and every `ω`. -/
theorem qv_le_crude_check (ω : PathΩ sz0) :
    ((sz0.size 0 : ℕ) : ℝ)⁻¹ * (DuhamelBInst_z 0).im⁻¹ ^ 2
        * RBM.Ind.loopMax 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0)
          (gueH sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 0 ω)) (DuhamelBInst_z 0) 2
      ≤ (DuhamelBInst_z 0).im⁻¹ ^ (2 + 2) :=
  Duhamel_qv_le_crude (sz := sz0) (gueH_isHermitian sz0 _ _ _ 0 0 ω)
    (lt_of_lt_of_le (by norm_num) (DuhamelBInst_im_ge 0 (by norm_num))) 2

/-! #### `Duhamel_exists_level` -/

/-- `Duhamel_exists_level` on the path space of `sz0`, the constant process `J ≡ 1/4`
(`Q = 1/2`), `λ₀ = 1/100`, `L₀ = 6` (`Q < 2^6 λ₀ = 0.64`), `k = K' = 4`. -/
theorem exists_level_check :
    ∃ ℓ : ℕ, ℓ ≤ 6 ∧
      4 ≤ firstHit (fun (_ : ℕ) (_ : PathΩ sz0) => (1 / 4 : ℝ)) (2 ^ ℓ * (1 / 100)) 4
        (0 : PathΩ sz0) ∧ (2 : ℝ) ^ ℓ * (1 / 100) ≤ 1 / 100 + 2 * (1 / 2) :=
  Duhamel_exists_level (J := fun (_ : ℕ) (_ : PathΩ sz0) => (1 / 4 : ℝ)) (K' := 4) (k := 4)
    (L₀ := 6) (ω := (0 : PathΩ sz0)) (lam0 := 1 / 100) (Q := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num) le_rfl (fun _ _ => by norm_num)

/-! #### `Duhamel_azuma_Z`, `Duhamel_azuma_Y` -/

/-- `Duhamel_azuma_Z` at `λ = 1/100`, `k = 4`, `ε = 1`. -/
theorem azuma_Z_check :
    (Pgue sz0).real {ω | 1 ≤ ‖∑ j ∈ Finset.range 4,
        DuhamelZst sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 0 DuhamelBInst_loop
          (1 / 100) (j + 1) ω‖}
      ≤ 4 * Real.exp (-1 ^ 2 / (4 * (((4 : ℕ) : ℝ) * (1 / 100)))) :=
  Duhamel_azuma_Z (sz := sz0) (t1 := DuhamelBInst_t1) (t0 := DuhamelBInst_t0)
    (K := DuhamelBInst_K) (n := 0) (e := 0) (I := DuhamelBInst_loop) (lam := 1 / 100)
    (by norm_num) DuhamelBInst_v_nonneg 4 (ε := 1) (by norm_num)

/-- The uniform bound `b = 3 · 10⁴ · v · N⁵` of `‖DuhamelT‖` at Hermitian base points
(`C₂ ≤ 6 N 10⁴` since `η_{u_{j+1}} ≥ 1/10`, `‖T‖ ≤ (C₂/2) v N⁴`). -/
private abbrev DuhamelBInst_b : ℝ :=
  3 * 10 ^ 4 * Duhamelv sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0
    * ((sz0.size 0 : ℕ) : ℝ) ^ 5

private theorem DuhamelBInst_hb :
    ∀ j < DuhamelBInst_K 0, ∀ M : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ,
      M.IsHermitian → ∀ y,
      ‖DuhamelT sz0 0 (DuhamelPhi sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 0
          DuhamelBInst_loop j) (Duhamelv sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0) M y‖
        ≤ DuhamelBInst_b := by
  intro j hj M hM y
  have hj4 : j < 4 := hj
  obtain ⟨_, hΦ, hC₂⟩ := bddC2C_Phi_check j hj4
  have hT := Duhamel_norm_T_le hΦ hC₂ DuhamelBInst_v_nonneg hM y
  refine hT.trans ?_
  have h1 := DuhamelBInst_im_ge (j + 1) (by omega)
  have hη : (RBM.Gauss.etaT 0 (gridTime DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0
      (j + 1)))⁻¹ ≤ 10 := by
    rw [etaT_eq_zt_im]
    calc ((DuhamelBInst_z (j + 1)).im)⁻¹ ≤ ((10 : ℝ)⁻¹)⁻¹ := inv_anti₀ (by norm_num) h1
      _ = 10 := by norm_num
  have hη0 : 0 ≤ (RBM.Gauss.etaT 0 (gridTime DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0
      (j + 1)))⁻¹ := inv_nonneg.2 (by
    rw [etaT_eq_zt_im]
    exact le_trans (by norm_num) h1)
  have hs0 : (0 : ℝ) ≤ ((sz0.size 0 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hC : ((DuhamelBInst_loop.length * (DuhamelBInst_loop.length + 1) : ℕ) : ℝ)
      * (sz0.size 0 : ℝ) * (RBM.Gauss.etaT 0 (gridTime DuhamelBInst_t1 DuhamelBInst_t0
        DuhamelBInst_K 0 (j + 1)))⁻¹ ^ (DuhamelBInst_loop.length + 2)
      ≤ 6 * ((sz0.size 0 : ℕ) : ℝ) * 10 ^ 4 := by
    have hlen : DuhamelBInst_loop.length = 2 := rfl
    rw [hlen]
    have hp := pow_le_pow_left₀ hη0 hη (2 + 2)
    norm_num at hp ⊢
    nlinarith [hp, hs0]
  have hv := DuhamelBInst_v_nonneg
  have hs4 : (0 : ℝ) ≤ ((sz0.size 0 : ℕ) : ℝ) ^ 4 := by positivity
  have hvs : 0 ≤ Duhamelv sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0
      * ((sz0.size 0 : ℕ) : ℝ) ^ 4 := mul_nonneg hv hs4
  calc _ ≤ (6 * ((sz0.size 0 : ℕ) : ℝ) * 10 ^ 4) / 2
        * Duhamelv sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0
        * ((sz0.size 0 : ℕ) : ℝ) ^ 4 := by
        have := div_le_div_of_nonneg_right hC (by norm_num : (0 : ℝ) ≤ 2)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hv) hs4
    _ = DuhamelBInst_b := by ring

/-- `Duhamel_azuma_Y` at `b = 3 · 10⁴ · v · N⁵`, `k = 4`, `ε = 1`: the hypothesis `hb` is
discharged by `Duhamel_bddC2C_Phi` and `Duhamel_norm_T_le`.  (The tail bound is numerically weak
at this `b` since `N⁵ ≈ 10³²`; the point is the hypothesis check.) -/
theorem azuma_Y_check :
    (Pgue sz0).real {ω | 1 ≤ ‖∑ j ∈ Finset.range 4,
        DuhamelYst sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 0 DuhamelBInst_loop
          (j + 1) ω‖}
      ≤ 4 * Real.exp (-1 ^ 2 / (4 * (((4 : ℕ) : ℝ) * (4 * DuhamelBInst_b ^ 2)))) :=
  Duhamel_azuma_Y (sz := sz0) (t1 := DuhamelBInst_t1) (t0 := DuhamelBInst_t0)
    (K := DuhamelBInst_K) (n := 0) (e := 0) (I := DuhamelBInst_loop) (b := DuhamelBInst_b)
    (by unfold DuhamelBInst_b; have := DuhamelBInst_v_nonneg; positivity) DuhamelBInst_hb
    (k := 4) (by norm_num) (ε := 1) (by norm_num)

end RBM.Univ.GUEPhase.DuhamelBInst

end
