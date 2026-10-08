/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.GUEPhase.Grid
import RBM3D.Path.Markov
import Mathlib.Probability.Moments.SubGaussian

/-!
# The `Pgue` Markov toolkit, `d ≥ 3`

Ticket T2327 (UN-32).  Port of `RBM2D/Universality/GUEPhase/Markov.lean` (`:1-912`; RBM2D HEAD
`9e0f275`, last commit touching the file `81fca44`).  Paper: arXiv:2507.20274, proof of Thm
`B_Univ` (`paper/tex/1_2_Intro_model_result.tex:566-570`: "essentially identical to ... [YY_25,
Theorem 2.6]"); no statement of the paper is involved beyond independence of the coordinates of
`Measure.infinitePi` and the Gaussian tail.

The freezing / conditional sub-Gaussianity toolkit for the GUE-phase grid measure `Pgue sz` on the
path carrier `PathΩ sz` (`Universality/GUEPhase/Grid.lean`), the analogue of what
`Path/Markov.lean` provides for the band grid measure `pathP sz`: the freezing lemma
`gueCondExp_freeze`, a general freezing-based conditional sub-Gaussianity lemma
(`gueHasCondSubgaussianMGF_of_frozen`), the law of a linear functional (`vGue`,
`gueMap_lin_Xmat`), the linear case (`gueHasCondSubgaussianMGF_linear`), and the entrywise
truncation event of the unit GUE increments (`gue_highProb_incr_le`).

What changes from `d = 2` (rule R1, as in `Grid.lean`): `d : Sizes` becomes `sz : Sizes d`;
`Idx (d.L n) (d.W n)` becomes `Idx d (sz.L n) (sz.W n)`; `Coord L W`/`Ω L W`/`Xentry L W` carry `d`
(`CoordF d L W`, `Ω d L W`, `Xentry d L W`).  The file is dimension-free except the cardinality
count `Fintype.card (Idx d (sz.L n) (sz.W n)) = sz.size n` (`(W L)^d`, merged `Sizes.card_Idx`; the
source proved it by `simp [Idx, Z2, ZMod.card, pow_two]`), and
`gueGridK sz n0 n = (sz.size n + 1)^(32 n₀ + 64)`; the polynomial-beats-exponential count is
unchanged.  `RBM2D`'s `Xmat_apply` has no RBM3D declaration: it is `rfl` (`Markov_Xmat_apply`).
`RBM.Path.hfun` (`Path/TailSums.lean:130` in RBM2D) is not used by the source (its `hfun` is a
local `have`).  The private freezing plumbing of `Path/Markov.lean` (`measurable_linTr_uncurry`,
`instStandardBorelSpace…`, `mgf_linTr_seqXmat`) is reproduced here under the prefix `Markov_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.LinearForm RBM.Path
open scoped NNReal ENNReal MeasureTheory

variable {d : ℕ} (sz : Sizes d)


/-! ### Private helpers: the `Pgue`-analogues of `Path/Markov.lean`'s freezing plumbing -/

section Freeze

/-- `PathΩ sz` is standard Borel (a countable product of countable products of `ℝ`); the instance
search does not find it by itself at a generic `sz` (as in `Path/Markov.lean`). -/
private instance Markov_standardBorelPathΩ {sz : Sizes d} : StandardBorelSpace (PathΩ sz) :=
  haveI : StandardBorelSpace (Sizes.SeqΩ sz) := inferInstance
  StandardBorelSpace.pi_countable (α := fun _ : ℕ => Sizes.SeqΩ sz)

private theorem Markov_indep_incr (k : ℕ) :
    Indep (MeasurableSpace.comap (fun ω : PathΩ sz => ω (k + 1)) inferInstance) (filt sz k)
      (Pgue sz) := by
  have hI : iIndepFun (fun i : ℕ => (fun ω : PathΩ sz => ω i)) (Pgue sz) :=
    iIndepFun_infinitePi (X := fun _ : ℕ => (id : Sizes.SeqΩ sz → Sizes.SeqΩ sz))
      (mX := fun _ => measurable_id)
  have hIndep : iIndep
      (fun n : ℕ => MeasurableSpace.comap (fun ω : PathΩ sz => ω n) inferInstance)
      (Pgue sz) := (iIndepFun_iff_iIndep
        (fun _ : ℕ => (inferInstance : MeasurableSpace (Sizes.SeqΩ sz)))
        (fun i ω => ω i) (Pgue sz)).mp hI
  have hle : ∀ n : ℕ, MeasurableSpace.comap (fun ω : PathΩ sz => ω n) inferInstance
      ≤ (inferInstance : MeasurableSpace (PathΩ sz)) :=
    fun n => le_iSup (fun n => MeasurableSpace.comap (fun ω : PathΩ sz => ω n) inferInstance) n
  have hsplit := indep_biSup_compl hle hIndep (Set.Iic k)
  have hfilt : filt sz k
      = ⨆ n ∈ Set.Iic k, MeasurableSpace.comap (fun ω : PathΩ sz => ω n) inferInstance := by
    have hshow : filt sz k =
        (inferInstance : MeasurableSpace (↥(Set.Iic k) → Sizes.SeqΩ sz)).comap
          (Preorder.restrictLe (π := fun _ : ℕ => Sizes.SeqΩ sz) k) := rfl
    have hpi : (inferInstance : MeasurableSpace (↥(Set.Iic k) → Sizes.SeqΩ sz))
        = ⨆ a : ↥(Set.Iic k),
            MeasurableSpace.comap (fun g : ↥(Set.Iic k) → Sizes.SeqΩ sz => g a) inferInstance :=
      rfl
    rw [hshow, hpi, MeasurableSpace.comap_iSup, iSup_subtype]
    simp only [MeasurableSpace.comap_comp]
    apply iSup_congr
    intro i
    apply iSup_congr
    intro _
    rfl
  rw [hfilt]
  have hmono : MeasurableSpace.comap (fun ω : PathΩ sz => ω (k + 1)) inferInstance
      ≤ ⨆ n ∈ (Set.Iic k)ᶜ, MeasurableSpace.comap (fun ω : PathΩ sz => ω n) inferInstance := by
    have hmem : (k + 1) ∈ (Set.Iic k)ᶜ := by simp
    exact le_biSup (fun n => MeasurableSpace.comap (fun ω : PathΩ sz => ω n) inferInstance) hmem
  exact indep_of_indep_of_le_left hsplit.symm hmono

private theorem Markov_map_incr (k : ℕ) :
    (Pgue sz).map (fun ω : PathΩ sz => ω (k + 1)) = gueUnit sz :=
  Measure.infinitePi_map_eval _ (k + 1)

/-- **The freezing lemma for `Pgue`**.  For
`k`, a `filt sz k`-measurable `Y : PathΩ sz → β` and a jointly measurable
`F : β → Sizes.SeqΩ sz → ℝ` with `F (Y ·) (· (k+1))` integrable, conditioning on `filt sz k`
freezes `Y` and averages the independent next draw `ω (k+1)` against its own law `gueUnit sz`
(the step law at every step `k + 1 ≥ 1` under `Pgue sz`). -/
theorem gueCondExp_freeze {β : Type*} [MeasurableSpace β] [StandardBorelSpace β]
    (k : ℕ) {Y : PathΩ sz → β} (hY : Measurable[filt sz k] Y)
    {F : β → Sizes.SeqΩ sz → ℝ} (hF : Measurable (fun p : β × Sizes.SeqΩ sz => F p.1 p.2))
    (hInt : Integrable (fun ω => F (Y ω) (ω (k + 1))) (Pgue sz)) :
    (Pgue sz)[fun ω => F (Y ω) (ω (k + 1)) | filt sz k]
      =ᵐ[Pgue sz] fun ω => ∫ x, F (Y ω) x ∂(gueUnit sz) := by
  classical
  set μ : Measure (PathΩ sz) := Pgue sz with hμdef
  set Z : PathΩ sz → Sizes.SeqΩ sz := fun ω => ω (k + 1) with hZdef
  set Φ : PathΩ sz → β × Sizes.SeqΩ sz := fun ω => (Y ω, Z ω) with hΦdef
  set ν : Measure (Sizes.SeqΩ sz) := gueUnit sz with hνdef
  set G : β → ℝ := fun y => ∫ x, F y x ∂ν with hGdef
  have hYmeas : Measurable Y := hY.mono ((filt sz).le k) le_rfl
  have hZmeas : Measurable Z := measurable_pi_apply (k + 1)
  have hΦmeas : Measurable Φ := hYmeas.prodMk hZmeas
  have hFsm : StronglyMeasurable (fun p : β × Sizes.SeqΩ sz => F p.1 p.2) := hF.stronglyMeasurable
  have hνmap : μ.map Z = ν := Markov_map_incr sz k
  have hindYZ : IndepFun Y Z μ := by
    have hcle : MeasurableSpace.comap Y inferInstance ≤ filt sz k := hY.comap_le
    exact (indep_of_indep_of_le_right (Markov_indep_incr sz k) hcle).symm
  have hIntΦ : Integrable (fun p : β × Sizes.SeqΩ sz => F p.1 p.2) (μ.map Φ) := by
    rw [integrable_map_measure hFsm.aestronglyMeasurable hΦmeas.aemeasurable]
    exact hInt
  have hprodglobal : μ.map Φ = (μ.map Y).prod ν := by
    rw [← hνmap]
    exact hindYZ.map_prod_eq_prod_map_map hYmeas.aemeasurable hZmeas.aemeasurable
  have hGmeas : StronglyMeasurable G := hFsm.integral_prod_right'
  have hkey : ∀ A : Set (PathΩ sz), MeasurableSet[filt sz k] A →
      ∫ ω in A, F (Y ω) (Z ω) ∂μ = ∫ ω in A, G (Y ω) ∂μ := by
    intro A hA
    have hprodA : (μ.restrict A).map Φ = ((μ.restrict A).map Y).prod ν := by
      refine (Measure.prod_eq ?_).symm
      intro s t hs ht
      have hpre : Φ ⁻¹' (s ×ˢ t) = Y ⁻¹' s ∩ Z ⁻¹' t := by
        ext ω; simp [Φ, Set.mem_prod]
      rw [Measure.map_apply hΦmeas (hs.prod ht), Measure.map_apply hYmeas hs,
        Measure.restrict_apply (hΦmeas (hs.prod ht)), Measure.restrict_apply (hYmeas hs), hpre]
      have hrearrange : Y ⁻¹' s ∩ Z ⁻¹' t ∩ A = Z ⁻¹' t ∩ (A ∩ Y ⁻¹' s) := by
        ext ω; simp only [Set.mem_inter_iff]; tauto
      rw [hrearrange]
      have hASmem : MeasurableSet[filt sz k] (A ∩ Y ⁻¹' s) := hA.inter (hY hs)
      have hZTmem : MeasurableSet[MeasurableSpace.comap Z inferInstance] (Z ⁻¹' t) :=
        ⟨t, ht, rfl⟩
      have hindep := (Indep_iff (MeasurableSpace.comap Z inferInstance) (filt sz k) μ).1
        (Markov_indep_incr sz k) (Z ⁻¹' t) (A ∩ Y ⁻¹' s) hZTmem hASmem
      rw [hindep, ← Measure.map_apply hZmeas ht, hνmap, Set.inter_comm (Y ⁻¹' s) A]
      ring
    have hIntΦA : Integrable (fun p : β × Sizes.SeqΩ sz => F p.1 p.2) ((μ.restrict A).map Φ) :=
      hIntΦ.mono_measure (Measure.map_mono Measure.restrict_le_self hΦmeas)
    calc
      ∫ ω in A, F (Y ω) (Z ω) ∂μ
          = ∫ p, F p.1 p.2 ∂((μ.restrict A).map Φ) :=
            (integral_map hΦmeas.aemeasurable hFsm.aestronglyMeasurable).symm
      _ = ∫ p, F p.1 p.2 ∂(((μ.restrict A).map Y).prod ν) := by rw [hprodA]
      _ = ∫ y, G y ∂((μ.restrict A).map Y) := integral_prod _ (hprodA ▸ hIntΦA)
      _ = ∫ ω in A, G (Y ω) ∂μ := integral_map hYmeas.aemeasurable hGmeas.aestronglyMeasurable
  have hIntG : Integrable G (μ.map Y) := by
    have hIntΦY : Integrable (fun p : β × Sizes.SeqΩ sz => F p.1 p.2) ((μ.map Y).prod ν) :=
      hprodglobal ▸ hIntΦ
    exact hIntΦY.integral_prod_left
  have hGYint : Integrable (fun ω => G (Y ω)) μ :=
    (integrable_map_measure hGmeas.aestronglyMeasurable hYmeas.aemeasurable).mp hIntG
  have hGYmeas : StronglyMeasurable[filt sz k] (fun ω => G (Y ω)) := hGmeas.comp_measurable hY
  exact (ae_eq_condExp_of_forall_setIntegral_eq ((filt sz).le k) hInt
    (fun s _ _ => hGYint.integrableOn) (fun s hs _ => (hkey s hs).symm)
    hGYmeas.aestronglyMeasurable).symm

end Freeze

/-! ### `gueHasCondSubgaussianMGF_of_frozen`: conditional sub-Gaussianity from a uniform-in-`y`
unconditional bound on the family. -/

section OfFrozen

/-- **Conditional sub-Gaussianity of a family**. -/
theorem gueHasCondSubgaussianMGF_of_frozen {β : Type*} [MeasurableSpace β]
    [StandardBorelSpace β] (k : ℕ) {Y : PathΩ sz → β} (hY : Measurable[filt sz k] Y)
    {F : β → Sizes.SeqΩ sz → ℝ} (hF : Measurable (fun p : β × Sizes.SeqΩ sz => F p.1 p.2))
    {c : ℝ≥0} (hsub : ∀ y, HasSubgaussianMGF (F y) c (gueUnit sz)) :
    HasCondSubgaussianMGF (filt sz k) ((filt sz).le k)
      (fun ω => F (Y ω) (ω (k + 1))) c (Pgue sz) := by
  classical
  set hm := (filt sz).le k
  have hYmeas : Measurable Y := hY.mono hm le_rfl
  have hUmeas : Measurable (fun ω : PathΩ sz => ω (k + 1)) := measurable_pi_apply (k + 1)
  have hindep : IndepFun (fun ω : PathΩ sz => ω (k + 1)) Y (Pgue sz) := by
    have hcle : MeasurableSpace.comap Y inferInstance ≤ filt sz k := hY.comap_le
    exact indep_of_indep_of_le_right (Markov_indep_incr sz k) hcle
  have hintegrable : ∀ t : ℝ,
      Integrable (fun ω : PathΩ sz => Real.exp (t * F (Y ω) (ω (k + 1)))) (Pgue sz) := by
    intro t
    set Fe : Sizes.SeqΩ sz × β → ℝ≥0∞ :=
      fun p => ENNReal.ofReal (Real.exp (t * F p.2 p.1)) with hFedef
    have hFe : Measurable Fe := by
      have h0 : Measurable (fun p : Sizes.SeqΩ sz × β => F p.2 p.1) := hF.comp measurable_swap
      exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (h0.const_mul t))
    have hbound : ∀ y : β,
        (∫⁻ x, Fe (x, y) ∂(Pgue sz).map (fun ω : PathΩ sz => ω (k + 1)))
          ≤ ENNReal.ofReal (Real.exp ((c : ℝ) * t ^ 2 / 2)) := by
      intro y
      rw [Markov_map_incr sz k]
      have hintY : Integrable (fun x => Real.exp (t * F y x)) (gueUnit sz) :=
        (hsub y).integrable_exp_mul t
      have hofreal := ofReal_integral_eq_lintegral_ofReal hintY
        (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
      have : (∫ x, Real.exp (t * F y x) ∂(gueUnit sz)) = mgf (F y) (gueUnit sz) t := rfl
      rw [hFedef]
      dsimp only
      rw [← hofreal, this]
      exact ENNReal.ofReal_le_ofReal ((hsub y).mgf_le t)
    have hlt := lintegral_indep_pair_le hUmeas hYmeas hindep hFe hbound
    refine ⟨?_, ?_⟩
    · have h1 : Measurable (fun ω : PathΩ sz => F (Y ω) (ω (k + 1))) := by
        have heq : (fun ω : PathΩ sz => F (Y ω) (ω (k + 1)))
            = (fun p : β × Sizes.SeqΩ sz => F p.1 p.2) ∘ (fun ω => (Y ω, ω (k + 1))) := rfl
        rw [heq]
        exact hF.comp (hYmeas.prodMk hUmeas)
      exact (Real.measurable_exp.comp (h1.const_mul t)).aestronglyMeasurable
    · rw [hasFiniteIntegral_def]
      have heq : ∀ ω, ‖Real.exp (t * F (Y ω) (ω (k + 1)))‖ₑ = Fe (ω (k + 1), Y ω) := by
        intro ω
        rw [Real.enorm_eq_ofReal (Real.exp_pos _).le, hFedef]
      simp_rw [heq]
      exact lt_of_le_of_lt hlt ENNReal.ofReal_lt_top
  refine Kernel.HasSubgaussianMGF.of_rat ?_ ?_
  · intro t
    rw [condExpKernel_comp_trim hm]
    exact hintegrable t
  · intro q
    set t : ℝ := (q : ℝ) with htdef
    set X : PathΩ sz → ℝ := fun ω => F (Y ω) (ω (k + 1)) with hXdef
    set Gr : PathΩ sz → ℝ := fun ω => Real.exp (t * X ω) with hGrdef
    set Fr : β → Sizes.SeqΩ sz → ℝ := fun y x => Real.exp (t * F y x) with hFrdef
    have hFrmeas : Measurable (fun p : β × Sizes.SeqΩ sz => Fr p.1 p.2) :=
      Real.measurable_exp.comp (hF.const_mul t)
    have hGreq : (fun ω : PathΩ sz => Fr (Y ω) (ω (k + 1))) = Gr := by
      funext ω; rw [hFrdef, hGrdef, hXdef]
    have hIntGr : Integrable Gr (Pgue sz) := hintegrable t
    have hfreeze := gueCondExp_freeze sz k hY hFrmeas (hGreq ▸ hIntGr)
    have hRHS : (fun ω : PathΩ sz => ∫ x, Fr (Y ω) x ∂(gueUnit sz))
        = fun ω => mgf (F (Y ω)) (gueUnit sz) t := rfl
    rw [hRHS, hGreq] at hfreeze
    have hsm1 : StronglyMeasurable[filt sz k] ((Pgue sz)[Gr | filt sz k]) :=
      stronglyMeasurable_condExp
    have hsm2 : StronglyMeasurable[filt sz k] (fun ω => mgf (F (Y ω)) (gueUnit sz) t) := by
      have hFrsm : StronglyMeasurable (fun p : β × Sizes.SeqΩ sz => Fr p.1 p.2) :=
        hFrmeas.stronglyMeasurable
      have hGmeas : StronglyMeasurable (fun y => ∫ x, Fr y x ∂(gueUnit sz)) :=
        hFrsm.integral_prod_right'
      exact hGmeas.comp_measurable hY
    have htrim := StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm hsm1 hsm2 hfreeze
    have hbridge := condExp_ae_eq_trim_integral_condExpKernel hm hIntGr
    have hcomb : ∀ᵐ ρ ∂(Pgue sz).trim hm,
        (∫ σ, Gr σ ∂condExpKernel (Pgue sz) (filt sz k) ρ) = mgf (F (Y ρ)) (gueUnit sz) t := by
      filter_upwards [hbridge, htrim] with ρ h1 h2
      rw [← h1, h2]
    filter_upwards [hcomb] with ρ hρ
    change (∫ σ, Gr σ ∂condExpKernel (Pgue sz) (filt sz k) ρ) ≤ Real.exp ((c : ℝ) * t ^ 2 / 2)
    rw [hρ, htdef]
    exact (hsub (Y ρ)).mgf_le _

end OfFrozen

/-! ### `vGue`, `gueMap_lin_Xmat`: the law of a linear functional under `gueUnit sz`.
The deterministic plumbing (`linTr`, `coordFinset`, `linTr_seqXmat_eq_sum`) is that of
`Path/Markov.lean`; only the two facts tying `gueUnit sz` to the coordinates (independence,
per-coordinate law) are specific to the GUE increments. -/

section LinearVariance

private theorem Markov_unitMapEval (c : Sizes.SeqCoord sz) :
    (gueUnit sz).map (fun ω : Sizes.SeqΩ sz => ω c) = gaussianReal 0 (gueUnitVar sz c) :=
  Measure.infinitePi_map_eval _ c

private theorem Markov_unitIIndepFun :
    iIndepFun (fun (c : Sizes.SeqCoord sz) (ω : Sizes.SeqΩ sz) => ω c) (gueUnit sz) := by
  have := iIndepFun_infinitePi (P := fun c : Sizes.SeqCoord sz => gaussianReal 0 (gueUnitVar sz c))
    (X := fun _ x => x) (fun _ => measurable_id)
  simpa [gueUnit] using this

/-- **`vGue`**: the conditional variance of a linear functional under `gueUnit sz`, in the
direction `A`. -/
def vGue (n : ℕ) (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℝ≥0 :=
  linVar (gueUnitVar sz)
    (fun c => linTr n A (Sizes.seqXmat sz n (Pi.single c 1))) (coordFinset n)

/-- **The law of a linear functional**: under `gueUnit sz`, `y ↦ Re tr (A · seqXmat sz n y)` is the
centred
Gaussian of variance `vGue sz n A`. -/
theorem gueMap_lin_Xmat (n : ℕ) (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    (gueUnit sz).map (fun y => linTr n A (Sizes.seqXmat sz n y)) =
      gaussianReal 0 (vGue sz n A) := by
  classical
  have hfun : (fun y : Sizes.SeqΩ sz => linTr n A (Sizes.seqXmat sz n y))
      = fun y => ∑ c ∈ coordFinset n,
          (linTr n A (Sizes.seqXmat sz n (Pi.single c 1))) * y c := by
    funext y
    rw [linTr_seqXmat_eq_sum]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  rw [hfun]
  have hsum := map_sum_const_mul_of_indep (P := gueUnit sz)
    (X := fun (c : Sizes.SeqCoord sz) (ω : Sizes.SeqΩ sz) => ω c) (v := gueUnitVar sz)
    (fun c => measurable_pi_apply c) (Markov_unitMapEval sz) (Markov_unitIIndepFun sz)
    (fun c => linTr n A (Sizes.seqXmat sz n (Pi.single c 1))) (coordFinset n)
  rw [hsum]
  rfl

end LinearVariance

/-! ### `gueHasCondSubgaussianMGF_linear`: the `Pgue`-analogue of `Path/Markov.lean`'s
`hasCondSubgaussianMGF_linear`

(Pointwise-bound argument: the private lemmas `measurable_linTr_uncurry`, `mgf_linTr_seqXmat`,
`integrable_exp_mul_X`, `condMGF_le` of `Path/Markov.lean` are reproduced here; the changes are
`pathP d ↦ Pgue sz`, `Sizes.seqP d ↦ gueUnit sz`, `Sizes.seqGvar d ↦ gueUnitVar sz`,
`linTrVar ↦ vGue`, and `√(gridStep) ↦ s`.) -/

section LinearMGF

variable {sz}

private theorem Markov_measurable_seqXmat (n : ℕ) : Measurable (Sizes.seqXmat sz n) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j =>
    (measurable_Xentry d (sz.L n) (sz.W n) i j).comp (Sizes.measurable_slice sz n)

private theorem Markov_linTr_eq_sum (n : ℕ)
    (A X : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    linTr n A X = ∑ i : Idx d (sz.L n) (sz.W n), ∑ k : Idx d (sz.L n) (sz.W n), (A i k * X k i).re := by
  unfold linTr
  rw [Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]

private theorem Markov_measurable_linTr_uncurry (n : ℕ) :
    Measurable (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ × Sizes.SeqΩ sz =>
      linTr n p.1 (Sizes.seqXmat sz n p.2)) := by
  have heq : (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ × Sizes.SeqΩ sz =>
      linTr n p.1 (Sizes.seqXmat sz n p.2))
      = fun p => ∑ i : Idx d (sz.L n) (sz.W n), ∑ k : Idx d (sz.L n) (sz.W n),
          (p.1 i k * Sizes.seqXmat sz n p.2 k i).re :=
    funext fun p => Markov_linTr_eq_sum n p.1 (Sizes.seqXmat sz n p.2)
  rw [heq]
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ => ?_
  have hM : Measurable
      (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ × Sizes.SeqΩ sz => p.1 i k) :=
    Measurable.eval_matrix (i := i) (j := k) measurable_fst
  have hX : Measurable
      (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ × Sizes.SeqΩ sz =>
        Sizes.seqXmat sz n p.2 k i) :=
    Measurable.eval_matrix (i := k) (j := i) ((Markov_measurable_seqXmat n).comp measurable_snd)
  exact Complex.measurable_re.comp (hM.mul hX)

private theorem Markov_measurable_linTr_left (n : ℕ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    Measurable (fun A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => linTr n A M) := by
  have heq : (fun A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => linTr n A M)
      = fun A => ∑ i : Idx d (sz.L n) (sz.W n), ∑ k : Idx d (sz.L n) (sz.W n), (A i k * M k i).re :=
    funext fun A => Markov_linTr_eq_sum n A M
  rw [heq]
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ => ?_
  exact Complex.measurable_re.comp
    ((Matrix.measurable_apply (i := i) (j := k)).mul measurable_const)

private theorem Markov_measurable_linTr_seqXmat (n : ℕ)
    (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    Measurable (fun x : Sizes.SeqΩ sz => linTr n A (Sizes.seqXmat sz n x)) := by
  have heq : (fun x : Sizes.SeqΩ sz => linTr n A (Sizes.seqXmat sz n x))
      = fun x => ∑ i : Idx d (sz.L n) (sz.W n), ∑ k : Idx d (sz.L n) (sz.W n),
          (A i k * Sizes.seqXmat sz n x k i).re :=
    funext fun x => Markov_linTr_eq_sum n A (Sizes.seqXmat sz n x)
  rw [heq]
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ => ?_
  exact Complex.measurable_re.comp
    (measurable_const.mul (Measurable.eval_matrix (i := k) (j := i) (Markov_measurable_seqXmat n)))

private theorem Markov_vGue_eq_sum (n : ℕ)
    (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    (vGue sz n A : ℝ) = ∑ c ∈ coordFinset n,
      (linTr n A (Sizes.seqXmat sz n (Pi.single c 1))) ^ 2 * (gueUnitVar sz c : ℝ) := by
  unfold vGue linVar
  push_cast [NNReal.coe_mk]
  rfl

private theorem Markov_measurable_vGue (n : ℕ) :
    Measurable (fun A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      (vGue sz n A : ℝ)) := by
  have heq : (fun A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      (vGue sz n A : ℝ))
      = fun A => ∑ c ∈ coordFinset n,
          (linTr n A (Sizes.seqXmat sz n (Pi.single c 1))) ^ 2 * (gueUnitVar sz c : ℝ) :=
    funext (Markov_vGue_eq_sum n)
  rw [heq]
  exact Finset.measurable_sum _ fun c _ => ((Markov_measurable_linTr_left n _).pow_const 2).mul_const _

private theorem Markov_mgf_lin_Xmat (n : ℕ)
    (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (r : ℝ) :
    mgf (fun x => linTr n A (Sizes.seqXmat sz n x)) (gueUnit sz) r
      = Real.exp ((vGue sz n A : ℝ) * r ^ 2 / 2) := by
  have hlaw : HasLaw (fun x => linTr n A (Sizes.seqXmat sz n x))
      (gaussianReal 0 (vGue sz n A)) (gueUnit sz) :=
    ⟨(Markov_measurable_linTr_seqXmat n A).aemeasurable, gueMap_lin_Xmat sz n A⟩
  rw [mgf_gaussianReal hlaw]
  congr 1
  ring

private theorem Markov_integrable_exp_lin_Xmat (n : ℕ)
    (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (r : ℝ) :
    Integrable (fun x => Real.exp (r * linTr n A (Sizes.seqXmat sz n x))) (gueUnit sz) := by
  have h : Integrable (fun x : ℝ => Real.exp (r * x))
      ((gueUnit sz).map (fun x => linTr n A (Sizes.seqXmat sz n x))) := by
    rw [gueMap_lin_Xmat sz n A]; exact integrable_exp_mul_gaussianReal r
  exact (integrable_map_measure h.aestronglyMeasurable
    (Markov_measurable_linTr_seqXmat n A).aemeasurable).1 h

private theorem Markov_linTr_zero (n : ℕ)
    (X : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    linTr n 0 X = 0 := by
  unfold linTr; simp

private theorem Markov_vGue_zero (n : ℕ) :
    vGue sz n (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) = 0 := by
  unfold vGue linVar; simp [Markov_linTr_zero]

private instance Markov_standardBorelMatrix (n : ℕ) :
    StandardBorelSpace (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
  inferInstanceAs (StandardBorelSpace (Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ))

section MGFBound

variable {n k : ℕ} {A : PathΩ sz → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

private theorem Markov_integrable_exp_mul_X (hA : Measurable[filt sz k] A) {s c : ℝ} (_hc : 0 ≤ c)
    (hAs : ∀ ω, s ^ 2 * (vGue sz n (A ω) : ℝ) ≤ c) (r : ℝ) :
    Integrable (fun ω : PathΩ sz =>
      Real.exp (r * (s * linTr n (A ω) (Sizes.seqXmat sz n (ω (k + 1)))))) (Pgue sz) := by
  classical
  set U : PathΩ sz → Sizes.SeqΩ sz := fun ω => ω (k + 1) with hUdef
  set F : Sizes.SeqΩ sz × Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (Real.exp ((r * s) * linTr n p.2 (Sizes.seqXmat sz n p.1))) with hFdef
  have hUmeas : Measurable U := measurable_pi_apply (k + 1)
  have hAmeas : Measurable A := hA.mono ((filt sz).le k) le_rfl
  have hindep : IndepFun U A (Pgue sz) := by
    have hcle : MeasurableSpace.comap A inferInstance ≤ filt sz k := hA.comap_le
    exact indep_of_indep_of_le_right (Markov_indep_incr sz k) hcle
  have hFmeas : Measurable F := by
    have h0 : Measurable
        (fun p : Sizes.SeqΩ sz × Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
          linTr n p.2 (Sizes.seqXmat sz n p.1)) := by
      have heq : (fun p : Sizes.SeqΩ sz × Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
          linTr n p.2 (Sizes.seqXmat sz n p.1))
          = fun p => ∑ i : Idx d (sz.L n) (sz.W n), ∑ k' : Idx d (sz.L n) (sz.W n),
              (p.2 i k' * Sizes.seqXmat sz n p.1 k' i).re :=
        funext fun p => Markov_linTr_eq_sum n p.2 (Sizes.seqXmat sz n p.1)
      rw [heq]
      refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k' _ => ?_
      have hM : Measurable
          (fun p : Sizes.SeqΩ sz × Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
            p.2 i k') :=
        Measurable.eval_matrix (i := i) (j := k') measurable_snd
      have hX : Measurable
          (fun p : Sizes.SeqΩ sz × Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
            Sizes.seqXmat sz n p.1 k' i) :=
        Measurable.eval_matrix (i := k') (j := i)
          ((Markov_measurable_seqXmat n).comp measurable_fst)
      exact Complex.measurable_re.comp (hM.mul hX)
    have h1 : Measurable
        (fun p : Sizes.SeqΩ sz × Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
          (r * s) * linTr n p.2 (Sizes.seqXmat sz n p.1)) := h0.const_mul _
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp h1)
  have hkey := lintegral_indep_pair hUmeas hAmeas hindep hFmeas
  rw [Markov_map_incr sz k] at hkey
  have hinner : ∀ y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
      (∫⁻ x, F (x, y) ∂(gueUnit sz)) =
        ENNReal.ofReal (Real.exp ((vGue sz n y : ℝ) * (r * s) ^ 2 / 2)) := by
    intro y
    have hint := Markov_integrable_exp_lin_Xmat n y (r * s)
    have hofreal := ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
    have hmgf := Markov_mgf_lin_Xmat n y (r * s)
    rw [mgf] at hmgf
    rw [hFdef]
    dsimp only
    rw [← hofreal, hmgf]
  have hp : MeasurableSet {y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ |
      (vGue sz n y : ℝ) * (r * s) ^ 2 / 2 ≤ c * r ^ 2 / 2} :=
    measurableSet_le (((Markov_measurable_vGue n).mul_const _).div_const _) measurable_const
  have hptwise : ∀ ω, (vGue sz n (A ω) : ℝ) * (r * s) ^ 2 / 2 ≤ c * r ^ 2 / 2 := by
    intro ω
    have h2 := hAs ω
    nlinarith [sq_nonneg r]
  have hae : ∀ᵐ y ∂(Pgue sz).map A, (vGue sz n y : ℝ) * (r * s) ^ 2 / 2 ≤ c * r ^ 2 / 2 := by
    rw [ae_map_iff hAmeas.aemeasurable hp]
    exact Filter.Eventually.of_forall hptwise
  have houter_eq : ∫⁻ ω, F (U ω, A ω) ∂(Pgue sz)
      = ∫⁻ y, ENNReal.ofReal (Real.exp ((vGue sz n y : ℝ) * (r * s) ^ 2 / 2))
          ∂((Pgue sz).map A) := by
    rw [hkey]; exact lintegral_congr hinner
  have houter_le : ∫⁻ ω, F (U ω, A ω) ∂(Pgue sz) ≤ ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) := by
    rw [houter_eq]
    calc ∫⁻ y, ENNReal.ofReal (Real.exp ((vGue sz n y : ℝ) * (r * s) ^ 2 / 2))
          ∂((Pgue sz).map A)
        ≤ ∫⁻ _y, ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) ∂((Pgue sz).map A) := by
          apply lintegral_mono_ae
          filter_upwards [hae] with y hy
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hy)
      _ = ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) * ((Pgue sz).map A) Set.univ := by
          rw [lintegral_const]
      _ ≤ ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) := by
          calc ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) * ((Pgue sz).map A) Set.univ
              ≤ ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) * 1 := by
                gcongr
                exact prob_le_one
            _ = ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) := mul_one _
  refine ⟨?_, ?_⟩
  · have hXmeas : Measurable (fun ω : PathΩ sz =>
        Real.exp (r * (s * linTr n (A ω) (Sizes.seqXmat sz n (ω (k + 1)))))) := by
      have h1 : Measurable (fun ω : PathΩ sz =>
          linTr n (A ω) (Sizes.seqXmat sz n (ω (k + 1)))) := by
        have heq : (fun ω : PathΩ sz => linTr n (A ω) (Sizes.seqXmat sz n (ω (k + 1))))
            = fun ω => ∑ i : Idx d (sz.L n) (sz.W n), ∑ k' : Idx d (sz.L n) (sz.W n),
              (A ω i k' * Sizes.seqXmat sz n (ω (k + 1)) k' i).re :=
          funext fun ω => Markov_linTr_eq_sum n (A ω) (Sizes.seqXmat sz n (ω (k + 1)))
        rw [heq]
        refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k' _ => ?_
        have hM : Measurable (fun ω : PathΩ sz => A ω i k') := Measurable.eval_matrix hAmeas
        have hX : Measurable (fun ω : PathΩ sz => Sizes.seqXmat sz n (ω (k + 1)) k' i) :=
          Measurable.eval_matrix ((Markov_measurable_seqXmat n).comp hUmeas)
        exact Complex.measurable_re.comp (hM.mul hX)
      exact Real.measurable_exp.comp ((h1.const_mul _).const_mul _)
    exact hXmeas.aestronglyMeasurable
  · rw [hasFiniteIntegral_def]
    have heq : ∀ ω, ‖Real.exp (r * (s *
        linTr n (A ω) (Sizes.seqXmat sz n (ω (k + 1)))))‖ₑ = F (U ω, A ω) := by
      intro ω
      rw [Real.enorm_eq_ofReal (Real.exp_pos _).le, hFdef]
      dsimp only
      congr 2
      ring
    simp_rw [heq]
    exact lt_of_le_of_lt houter_le ENNReal.ofReal_lt_top

private theorem Markov_cond_mgf_le (hA : Measurable[filt sz k] A) {s c : ℝ} (hc : 0 ≤ c)
    (hAs : ∀ ω, s ^ 2 * (vGue sz n (A ω) : ℝ) ≤ c) (r : ℝ) :
    ∀ᵐ ω ∂((Pgue sz).trim ((filt sz).le k)),
      mgf (fun ρ => s * linTr n (A ρ) (Sizes.seqXmat sz n (ρ (k + 1))))
        (condExpKernel (Pgue sz) (filt sz k) ω) r ≤ Real.exp (c * r ^ 2 / 2) := by
  classical
  set X : PathΩ sz → ℝ := fun ρ => s * linTr n (A ρ) (Sizes.seqXmat sz n (ρ (k + 1))) with hXdef
  set Gr : PathΩ sz → ℝ := fun ρ => Real.exp (r * X ρ) with hGrdef
  set Fr : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → Sizes.SeqΩ sz → ℝ :=
    fun y x => Real.exp (r * (s * linTr n y (Sizes.seqXmat sz n x))) with hFrdef
  have hFrmeas : Measurable
      (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ × Sizes.SeqΩ sz =>
        Fr p.1 p.2) := by
    have h1 : Measurable
        (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ × Sizes.SeqΩ sz =>
          linTr n p.1 (Sizes.seqXmat sz n p.2)) := Markov_measurable_linTr_uncurry n
    exact Real.measurable_exp.comp ((h1.const_mul _).const_mul _)
  have hGreq : (fun ρ : PathΩ sz => Fr (A ρ) (ρ (k + 1))) = Gr := by
    funext ρ; rw [hFrdef, hGrdef, hXdef]
  have hIntGr : Integrable Gr (Pgue sz) := Markov_integrable_exp_mul_X hA hc hAs r
  have hfreeze := gueCondExp_freeze sz k hA hFrmeas (hGreq ▸ hIntGr)
  have hRHS : (fun ρ : PathΩ sz => ∫ x, Fr (A ρ) x ∂(gueUnit sz))
      = fun ρ => Real.exp ((vGue sz n (A ρ) : ℝ) * (r * s) ^ 2 / 2) := by
    funext ρ
    have hmgf := Markov_mgf_lin_Xmat n (A ρ) (r * s)
    rw [mgf] at hmgf
    rw [← hmgf]
    have hpt : ∀ x, Fr (A ρ) x
        = Real.exp ((r * s) * linTr n (A ρ) (Sizes.seqXmat sz n x)) := by
      intro x; rw [hFrdef]; ring_nf
    simp_rw [hpt]
  rw [hRHS] at hfreeze
  rw [hGreq] at hfreeze
  have hm : filt sz k ≤ (inferInstance : MeasurableSpace (PathΩ sz)) := (filt sz).le k
  have hsm1 : StronglyMeasurable[filt sz k] ((Pgue sz)[Gr | filt sz k]) :=
    stronglyMeasurable_condExp
  have hsm2 : StronglyMeasurable[filt sz k]
      (fun ρ => Real.exp ((vGue sz n (A ρ) : ℝ) * (r * s) ^ 2 / 2)) := by
    have hcont : Measurable (fun y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
        Real.exp ((vGue sz n y : ℝ) * (r * s) ^ 2 / 2)) :=
      Real.measurable_exp.comp (((Markov_measurable_vGue n).mul_const _).div_const _)
    exact (hcont.comp hA).stronglyMeasurable
  have htrim := StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm hsm1 hsm2 hfreeze
  have hbridge := condExp_ae_eq_trim_integral_condExpKernel hm hIntGr
  have hcomb : ∀ᵐ ρ ∂(Pgue sz).trim hm,
      (∫ σ, Gr σ ∂condExpKernel (Pgue sz) (filt sz k) ρ)
        = Real.exp ((vGue sz n (A ρ) : ℝ) * (r * s) ^ 2 / 2) := by
    filter_upwards [hbridge, htrim] with ρ h1 h2
    rw [← h1, h2]
  filter_upwards [hcomb] with ρ hρ
  change (∫ σ, Gr σ ∂condExpKernel (Pgue sz) (filt sz k) ρ) ≤ Real.exp (c * r ^ 2 / 2)
  rw [hρ]
  apply Real.exp_le_exp.2
  have h2 := hAs ρ
  nlinarith [sq_nonneg r]

end MGFBound

end LinearMGF

/-- **Conditional sub-Gaussianity of a linear functional under `Pgue sz`**.  For a
`filt sz k`-measurable
direction `A`, a `filt sz k`-measurable set `E` and `c : ℝ≥0` with `s² · vGue sz n (A ω) ≤ c` on `E`,
the `E`-truncated variable `s · Re tr (A · seqXmat sz n (ω (k+1)))` has a conditionally
sub-Gaussian mgf with parameter `c` given `filt sz k`. -/
theorem gueHasCondSubgaussianMGF_linear (n k : ℕ) (s : ℝ)
    {A : PathΩ sz → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hA : Measurable[filt sz k] A) (E : Set (PathΩ sz)) (hE : MeasurableSet[filt sz k] E) (c : ℝ≥0)
    (hbound : ∀ ω ∈ E, s ^ 2 * (vGue sz n (A ω) : ℝ) ≤ c) :
    HasCondSubgaussianMGF (filt sz k) ((filt sz).le k)
      (fun ω => E.indicator (fun ω => s * linTr n (A ω) (Sizes.seqXmat sz n (ω (k + 1)))) ω)
      c (Pgue sz) := by
  classical
  have hc : (0 : ℝ) ≤ (c : ℝ) := c.coe_nonneg
  set A' : PathΩ sz → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
    fun ω => if ω ∈ E then A ω else 0 with hA'def
  have hA'meas : Measurable[filt sz k] A' :=
    Measurable.ite (p := fun ω => ω ∈ E) hE hA measurable_const
  have hAs : ∀ ω, s ^ 2 * (vGue sz n (A' ω) : ℝ) ≤ c := by
    intro ω
    by_cases hω : ω ∈ E
    · simpa [hA'def, hω] using hbound ω hω
    · simp only [hA'def, hω, ite_false, Markov_vGue_zero, NNReal.coe_zero, mul_zero]
      exact hc
  have hXeq : (fun ω => E.indicator
      (fun ω => s * linTr n (A ω) (Sizes.seqXmat sz n (ω (k + 1)))) ω)
      = fun ω => s * linTr n (A' ω) (Sizes.seqXmat sz n (ω (k + 1))) := by
    funext ω
    by_cases hω : ω ∈ E
    · simp [Set.indicator, hω, hA'def]
    · simp [Set.indicator, hω, hA'def, Markov_linTr_zero]
  rw [hXeq]
  change Kernel.HasSubgaussianMGF (fun ω => s * linTr n (A' ω) (Sizes.seqXmat sz n (ω (k + 1))))
    c (condExpKernel (Pgue sz) (filt sz k)) ((Pgue sz).trim ((filt sz).le k))
  refine Kernel.HasSubgaussianMGF.of_rat ?_ ?_
  · intro r
    rw [condExpKernel_comp_trim ((filt sz).le k)]
    exact Markov_integrable_exp_mul_X hA'meas hc hAs r
  · intro q
    exact Markov_cond_mgf_le hA'meas hc hAs (q : ℝ)

/-! ### `gue_highProb_incr_le`: the entrywise truncation event -/

section Truncation

/-- If every raw coordinate of `y` is `≤ t` in absolute value, every entry of `Xmat L W y` is `≤ 2t`
in norm (triangle inequality on the two coordinates `Xentry` reads; the diagonal case needs only
one of them, plus `t ≥ 0` from the other). -/
private theorem Markov_Xmat_apply {L W : ℕ} [NeZero L] [NeZero W] (y : Ω d L W) (i j : Idx d L W) :
    Xmat d L W y i j = Xentry d L W y i j := rfl

private theorem Markov_norm_Xentry_le {L W : ℕ} [NeZero L] [NeZero W] (y : Ω d L W)
    (i j : Idx d L W) {t : ℝ} (h : ∀ c : CoordF d L W, |y c| ≤ t) : ‖Xentry d L W y i j‖ ≤ 2 * t := by
  unfold Xentry
  split_ifs with h1 h2
  · calc ‖(y (i, j, true) : ℂ) + Complex.I * (y (i, j, false) : ℂ)‖
        ≤ ‖(y (i, j, true) : ℂ)‖ + ‖Complex.I * (y (i, j, false) : ℂ)‖ := norm_add_le _ _
      _ = |y (i, j, true)| + |y (i, j, false)| := by
          simp [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ t + t := add_le_add (h _) (h _)
      _ = 2 * t := by ring
  · calc ‖(y (j, i, true) : ℂ) - Complex.I * (y (j, i, false) : ℂ)‖
        ≤ ‖(y (j, i, true) : ℂ)‖ + ‖Complex.I * (y (j, i, false) : ℂ)‖ := norm_sub_le _ _
      _ = |y (j, i, true)| + |y (j, i, false)| := by
          simp [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ t + t := add_le_add (h _) (h _)
      _ = 2 * t := by ring
  · have h1 := h (i, j, true)
    have h2 := h (i, j, false)
    have ht0 : (0 : ℝ) ≤ t := (abs_nonneg _).trans h2
    rw [Complex.norm_real, Real.norm_eq_abs]
    linarith

end Truncation

/-! ### The Gaussian tail bound and the exponential-beats-polynomial fact -/

section Tail

private theorem Markov_hasSubgaussianMGF_id (v : ℝ≥0) :
    HasSubgaussianMGF (fun x : ℝ => x) v (gaussianReal 0 v) where
  integrable_exp_mul t := integrable_exp_mul_gaussianReal t
  mgf_le t := by
    have hlaw : HasLaw (fun x : ℝ => x) (gaussianReal 0 v) (gaussianReal (0 : ℝ) v) :=
      ⟨measurable_id.aemeasurable, by
        rw [show (fun x : ℝ => x) = id from rfl]; exact Measure.map_id⟩
    rw [mgf_gaussianReal hlaw]
    simp

/-- The two-sided Gaussian tail bound: for a centred Gaussian of variance `v ≤ 1`, the probability
of exceeding `t ≥ 0` in absolute value is `≤ 2 exp(-t²/2)`. -/
private theorem Markov_gaussian_tail_le {v : ℝ≥0} (hv0 : 0 < (v : ℝ)) (hv1 : (v : ℝ) ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) :
    (gaussianReal 0 v) {x : ℝ | t < |x|} ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / 2)) := by
  have hsub : HasSubgaussianMGF (fun x : ℝ => x) v (gaussianReal 0 v) :=
    Markov_hasSubgaussianMGF_id v
  have hexple : Real.exp (-(t ^ 2) / (2 * (v : ℝ))) ≤ Real.exp (-(t ^ 2) / 2) := by
    apply Real.exp_le_exp.2
    have hden : (0 : ℝ) < 2 * (v : ℝ) := by positivity
    have hle : (2 : ℝ) * (v : ℝ) ≤ 2 := by linarith
    have hkey : t ^ 2 / 2 ≤ t ^ 2 / (2 * (v : ℝ)) :=
      div_le_div_of_nonneg_left (sq_nonneg t) hden hle
    rw [neg_div, neg_div]
    linarith
  have h1 : (gaussianReal 0 v).real {x : ℝ | t ≤ x} ≤ Real.exp (-(t ^ 2) / (2 * (v : ℝ))) :=
    hsub.measure_ge_le ht
  have h2 : (gaussianReal 0 v).real {x : ℝ | t ≤ -x} ≤ Real.exp (-(t ^ 2) / (2 * (v : ℝ))) := by
    have h2' := hsub.neg.measure_ge_le ht
    simpa using h2'
  have hsub' : {x : ℝ | t < |x|} ⊆ {x : ℝ | t ≤ x} ∪ {x : ℝ | t ≤ -x} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    rcases le_total 0 x with hx0 | hx0
    · have heq : |x| = x := abs_of_nonneg hx0
      exact Or.inl (le_of_lt (heq ▸ hx))
    · have heq : |x| = -x := abs_of_nonpos hx0
      exact Or.inr (le_of_lt (heq ▸ hx))
  have hreal : (gaussianReal 0 v).real {x : ℝ | t < |x|} ≤ 2 * Real.exp (-(t ^ 2) / 2) := by
    calc (gaussianReal 0 v).real {x : ℝ | t < |x|}
        ≤ (gaussianReal 0 v).real ({x : ℝ | t ≤ x} ∪ {x : ℝ | t ≤ -x}) :=
          measureReal_mono hsub'
      _ ≤ (gaussianReal 0 v).real {x : ℝ | t ≤ x} + (gaussianReal 0 v).real {x : ℝ | t ≤ -x} :=
          measureReal_union_le _ _
      _ ≤ Real.exp (-(t ^ 2) / (2 * (v : ℝ))) + Real.exp (-(t ^ 2) / (2 * (v : ℝ))) :=
          add_le_add h1 h2
      _ ≤ Real.exp (-(t ^ 2) / 2) + Real.exp (-(t ^ 2) / 2) := add_le_add hexple hexple
      _ = 2 * Real.exp (-(t ^ 2) / 2) := by ring
  calc (gaussianReal 0 v) {x : ℝ | t < |x|}
      = ENNReal.ofReal ((gaussianReal 0 v).real {x : ℝ | t < |x|}) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / 2)) := ENNReal.ofReal_le_ofReal hreal

/-- The Gaussian tail `2 exp(-S²/8)` beats every polynomial `S^{-D'}`. -/
private theorem Markov_eventually_exp_beats_rpow (D' : ℝ) :
    ∀ᶠ N : ℕ in atTop, 2 * Real.exp (-((N : ℝ) ^ 2) / 8) ≤ (N : ℝ) ^ (-D') := by
  have hz : Filter.Tendsto (fun u : ℝ => u ^ (D' / 2 + 1) * Real.exp (-(1 / 8) * u)) atTop
      (nhds 0) := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (D' / 2 + 1) (1 / 8) (by norm_num)
  have hsq : Filter.Tendsto (fun x : ℝ => x ^ (2 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hN : Filter.Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hcomp : Filter.Tendsto (fun N : ℕ =>
      ((N : ℝ) ^ (2 : ℝ)) ^ (D' / 2 + 1) * Real.exp (-(1 / 8) * (N : ℝ) ^ (2 : ℝ))) atTop
      (nhds 0) := hz.comp (hsq.comp hN)
  have hev : ∀ᶠ N : ℕ in atTop,
      ((N : ℝ) ^ (2 : ℝ)) ^ (D' / 2 + 1) * Real.exp (-(1 / 8) * (N : ℝ) ^ (2 : ℝ)) < 1 :=
    hcomp.eventually (eventually_lt_nhds one_pos)
  filter_upwards [hev, eventually_ge_atTop 2] with N hev hN2
  have hN0 : (0 : ℝ) < N := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    linarith
  have hrpoweq : (N : ℝ) ^ (2 : ℝ) = (N : ℝ) ^ (2 : ℕ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  have hpoweq : ((N : ℝ) ^ (2 : ℝ)) ^ (D' / 2 + 1) = (N : ℝ) ^ (D' + 2) := by
    rw [← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1
    ring
  have hexpeq : -(1 / 8 : ℝ) * (N : ℝ) ^ (2 : ℝ) = -((N : ℝ) ^ 2) / 8 := by
    rw [hrpoweq]; ring
  rw [hpoweq, hexpeq] at hev
  have hDpos : (0 : ℝ) < (N : ℝ) ^ D' := Real.rpow_pos_of_pos hN0 _
  have hsplit : (N : ℝ) ^ (D' + 2) = (N : ℝ) ^ D' * (N : ℝ) ^ (2 : ℕ) := by
    rw [← hrpoweq, Real.rpow_add hN0]
  rw [hsplit] at hev
  have hN2R : (2 : ℝ) ≤ (N : ℝ) ^ 2 := by
    have h2N : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    nlinarith [sq_nonneg ((N : ℝ) - 2)]
  have hnn : (0 : ℝ) ≤ Real.exp (-((N : ℝ) ^ 2) / 8) * (N : ℝ) ^ D' :=
    mul_nonneg (Real.exp_pos _).le hDpos.le
  have hfinal : 2 * (Real.exp (-((N : ℝ) ^ 2) / 8) * (N : ℝ) ^ D')
      ≤ (N : ℝ) ^ 2 * (Real.exp (-((N : ℝ) ^ 2) / 8) * (N : ℝ) ^ D') :=
    mul_le_mul_of_nonneg_right hN2R hnn
  rw [Real.rpow_neg (Nat.cast_nonneg N), inv_eq_one_div, le_div_iff₀ hDpos]
  nlinarith [hfinal, hev]

end Tail

/-! ### The cardinality of the (step, coordinate) index set is polynomial in `sz.size n` -/

section Cardinality

private theorem Markov_card_Idx (n : ℕ) :
    Fintype.card (Idx d (sz.L n) (sz.W n)) = sz.size n :=
  Sizes.card_Idx sz n

private theorem Markov_card_coordFinset (n : ℕ) :
    (coordFinset (sz := sz) n).card = sz.size n * (sz.size n * 2) := by
  change (Finset.univ.map (Function.Embedding.sigmaMk (β := fun m => CoordF d (sz.L m) (sz.W m)) n)).card = _
  rw [Finset.card_map, Finset.card_univ]
  change Fintype.card (Idx d (sz.L n) (sz.W n) × (Idx d (sz.L n) (sz.W n) × Bool)) = _
  rw [Fintype.card_prod (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n) × Bool),
    Fintype.card_prod (Idx d (sz.L n) (sz.W n)) Bool, Fintype.card_bool, Markov_card_Idx]

private theorem Markov_card_K (n0 n : ℕ) :
    Fintype.card (Fin (gueGridK sz n0 n) × ↥(coordFinset (sz := sz) n))
      = (sz.size n + 1) ^ (32 * n0 + 64) * (sz.size n * (sz.size n * 2)) := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, Markov_card_coordFinset]
  rfl

/-- Pure arithmetic: for `S ≥ 2^(32 n₀ + 65)`, `(S+1)^(32 n₀+64) · (2 S²) ≤ S^(32 n₀ + 68)`. -/
private theorem Markov_card_arith (n0 S : ℕ) (hSbig : 2 ^ (32 * n0 + 65) ≤ S) :
    (((S + 1) ^ (32 * n0 + 64) * (S * (S * 2)) : ℕ) : ℝ) ≤ (S : ℝ) ^ (32 * n0 + 68) := by
  have hS1 : 1 ≤ S := le_trans (Nat.one_le_two_pow) hSbig
  have hS1R : (1 : ℝ) ≤ S := by exact_mod_cast hS1
  have h2S : (S : ℝ) + 1 ≤ 2 * S := by linarith
  have hpow2 : (2 * (S : ℝ)) ^ (32 * n0 + 64)
      = (2 : ℝ) ^ (32 * n0 + 64) * (S : ℝ) ^ (32 * n0 + 64) := mul_pow 2 (S : ℝ) _
  have hbig : (2 : ℝ) ^ (32 * n0 + 65) ≤ (S : ℝ) := by
    have : ((2 ^ (32 * n0 + 65) : ℕ) : ℝ) ≤ (S : ℝ) := by exact_mod_cast hSbig
    rwa [Nat.cast_pow, Nat.cast_ofNat] at this
  have hstep : ((S : ℝ) + 1) ^ (32 * n0 + 64) * ((S : ℝ) * ((S : ℝ) * 2))
      ≤ (2 : ℝ) ^ (32 * n0 + 65) * (S : ℝ) ^ (32 * n0 + 66) := by
    calc ((S : ℝ) + 1) ^ (32 * n0 + 64) * ((S : ℝ) * ((S : ℝ) * 2))
        ≤ (2 * (S : ℝ)) ^ (32 * n0 + 64) * ((S : ℝ) * ((S : ℝ) * 2)) := by
          gcongr
      _ = (2 : ℝ) ^ (32 * n0 + 64) * (S : ℝ) ^ (32 * n0 + 64) * ((S : ℝ) * ((S : ℝ) * 2)) := by
          rw [hpow2]
      _ = (2 : ℝ) ^ (32 * n0 + 65) * (S : ℝ) ^ (32 * n0 + 66) := by ring
  have hfinal : (2 : ℝ) ^ (32 * n0 + 65) * (S : ℝ) ^ (32 * n0 + 66) ≤ (S : ℝ) ^ (32 * n0 + 68) := by
    have hS66 : (0 : ℝ) ≤ (S : ℝ) ^ (32 * n0 + 66) := by positivity
    calc (2 : ℝ) ^ (32 * n0 + 65) * (S : ℝ) ^ (32 * n0 + 66)
        ≤ (S : ℝ) * (S : ℝ) ^ (32 * n0 + 66) := mul_le_mul_of_nonneg_right hbig hS66
      _ = (S : ℝ) ^ (32 * n0 + 67) := by ring
      _ ≤ (S : ℝ) ^ (32 * n0 + 68) := pow_le_pow_right₀ hS1R (by omega)
  calc (((S + 1) ^ (32 * n0 + 64) * (S * (S * 2)) : ℕ) : ℝ)
      = ((S : ℝ) + 1) ^ (32 * n0 + 64) * ((S : ℝ) * ((S : ℝ) * 2)) := by push_cast; ring
    _ ≤ (2 : ℝ) ^ (32 * n0 + 65) * (S : ℝ) ^ (32 * n0 + 66) := hstep
    _ ≤ (S : ℝ) ^ (32 * n0 + 68) := hfinal

private theorem Markov_eventually_cardK_le (hsize : Tendsto (fun n => sz.size n) atTop atTop)
    (n0 : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (Fintype.card (Fin (gueGridK sz n0 n) × ↥(coordFinset (sz := sz) n)) : ℝ)
        ≤ ((sz.size n : ℕ) : ℝ) ^ ((32 * n0 + 68 : ℕ) : ℝ) := by
  filter_upwards [hsize.eventually (eventually_ge_atTop (2 ^ (32 * n0 + 65)))] with n hbig
  rw [Real.rpow_natCast, Markov_card_K]
  exact Markov_card_arith n0 (sz.size n) hbig

end Cardinality

/-! ### `gue_highProb_incr_le` -/

section IncrTruncation

private theorem Markov_unitVar_pos (c : Sizes.SeqCoord sz) : 0 < (gueUnitVar sz c : ℝ) := by
  unfold gueUnitVar; split_ifs <;> norm_num

private theorem Markov_unitVar_le_one (c : Sizes.SeqCoord sz) : (gueUnitVar sz c : ℝ) ≤ 1 := by
  unfold gueUnitVar; split_ifs <;> norm_num

/-- **The entrywise truncation event of the unit GUE increments**.  With high probability on the
matrix
dimension `sz.size n`, every entry of every GUE increment `seqXmat sz n (ω k)`,
`1 ≤ k ≤ gueGridK sz n0 n`, is at most `sz.size n` in norm. -/
theorem gue_highProb_incr_le (n0 : ℕ) (hsize : Tendsto (fun n => sz.size n) atTop atTop) :
    HighProbAt (Pgue sz) sz.size (fun n => {ω | ∀ k, 1 ≤ k → k ≤ gueGridK sz n0 n →
      ∀ i j : Idx d (sz.L n) (sz.W n), ‖Sizes.seqXmat sz n (ω k) i j‖ ≤ ((sz.size n : ℕ) : ℝ)}) := by
  classical
  set K : ℕ → Type := fun n => Fin (gueGridK sz n0 n) × ↥(coordFinset (sz := sz) n) with hKdef
  set Ξ : ∀ n, K n → Set (PathΩ sz) :=
    fun n p => {ω | |ω (p.1.1 + 1) (p.2 : Sizes.SeqCoord sz)| ≤ ((sz.size n : ℕ) : ℝ) / 2}
    with hΞdef
  have hmeas : ∀ n (p : K n),
      Measurable (fun ω : PathΩ sz => ω (p.1.1 + 1) (p.2 : Sizes.SeqCoord sz)) :=
    fun n p => (measurable_pi_apply (p.2 : Sizes.SeqCoord sz)).comp
      (measurable_pi_apply (p.1.1 + 1))
  have hcompl : ∀ D : ℝ, 0 < D → ∀ᶠ n : ℕ in atTop, ∀ p : K n,
      (Pgue sz) (Ξ n p)ᶜ ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
    intro D _
    filter_upwards [hsize.eventually (Markov_eventually_exp_beats_rpow D)] with n hn p
    have hms : MeasurableSet {y : ℝ | ((sz.size n : ℕ) : ℝ) / 2 < |y|} :=
      measurableSet_lt measurable_const measurable_norm
    have heq : (Ξ n p)ᶜ = (fun ω : PathΩ sz => ω (p.1.1 + 1) (p.2 : Sizes.SeqCoord sz)) ⁻¹'
        {y : ℝ | ((sz.size n : ℕ) : ℝ) / 2 < |y|} := by
      ext ω; simp [hΞdef, not_le]
    rw [heq, ← Measure.map_apply (hmeas n p) hms]
    have hmapeq : (Pgue sz).map (fun ω : PathΩ sz => ω (p.1.1 + 1) (p.2 : Sizes.SeqCoord sz))
        = gaussianReal 0 (gueUnitVar sz (p.2 : Sizes.SeqCoord sz)) := by
      rw [show (fun ω : PathΩ sz => ω (p.1.1 + 1) (p.2 : Sizes.SeqCoord sz))
          = (fun y : Sizes.SeqΩ sz => y (p.2 : Sizes.SeqCoord sz)) ∘
            (fun ω : PathΩ sz => ω (p.1.1 + 1)) from rfl,
        ← Measure.map_map (measurable_pi_apply (p.2 : Sizes.SeqCoord sz))
          (measurable_pi_apply (p.1.1 + 1)),
        Markov_map_incr sz p.1.1, Markov_unitMapEval sz (p.2 : Sizes.SeqCoord sz)]
    rw [hmapeq]
    have htail := Markov_gaussian_tail_le (Markov_unitVar_pos sz (p.2 : Sizes.SeqCoord sz))
      (Markov_unitVar_le_one sz (p.2 : Sizes.SeqCoord sz))
      (show (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) / 2 by positivity)
    have hEq : -((((sz.size n : ℕ) : ℝ) / 2) ^ 2) / 2 = -(((sz.size n : ℕ) : ℝ) ^ 2) / 8 := by ring
    rw [hEq] at htail
    exact htail.trans (ENNReal.ofReal_le_ofReal hn)
  have hsub : ∀ n, (⋂ p : K n, Ξ n p) ⊆ {ω | ∀ k, 1 ≤ k → k ≤ gueGridK sz n0 n →
      ∀ i j : Idx d (sz.L n) (sz.W n), ‖Sizes.seqXmat sz n (ω k) i j‖ ≤ ((sz.size n : ℕ) : ℝ)} := by
    intro n ω hω k hk1 hkK i j
    simp only [Set.mem_iInter] at hω
    have hbound : ∀ c : CoordF d (sz.L n) (sz.W n),
        |Sizes.slice sz n (ω k) c| ≤ ((sz.size n : ℕ) : ℝ) / 2 := by
      intro c
      have hmem : (⟨n, c⟩ : Sizes.SeqCoord sz) ∈ coordFinset (sz := sz) n := by
        unfold coordFinset
        exact Finset.mem_map.2 ⟨c, Finset.mem_univ _, rfl⟩
      have hkey := hω (⟨⟨k - 1, by omega⟩, ⟨⟨n, c⟩, hmem⟩⟩ : K n)
      simp only [hΞdef, Set.mem_ofPred_eq] at hkey
      have heqk : k - 1 + 1 = k := by omega
      rw [heqk] at hkey
      exact hkey
    have hle := Markov_norm_Xentry_le (Sizes.slice sz n (ω k)) i j hbound
    unfold Sizes.seqXmat
    rw [Markov_Xmat_apply]
    calc ‖Xentry d (sz.L n) (sz.W n) (Sizes.slice sz n (ω k)) i j‖
        ≤ 2 * (((sz.size n : ℕ) : ℝ) / 2) := hle
      _ = ((sz.size n : ℕ) : ℝ) := by ring
  have hI := highProbAt_iInter (Pgue sz) sz.size (K := K) (Ξ := Ξ)
    (C := ((32 * n0 + 68 : ℕ) : ℝ)) (Nat.cast_nonneg _) (Markov_eventually_cardK_le sz hsize n0)
    hcompl
  intro D hD
  filter_upwards [hI D hD] with n hn
  exact le_trans (measure_mono (Set.compl_subset_compl.2 (hsub n))) hn

end IncrTruncation

/-! ### The sub-Gaussian law of the frozen linear functional (used by the compiled instances) -/

section LinearSubgaussian

variable {sz}

private theorem Markov_hasSubgaussianMGF_lin (n : ℕ)
    (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    HasSubgaussianMGF (fun x => linTr n A (Sizes.seqXmat sz n x)) (vGue sz n A) (gueUnit sz) where
  integrable_exp_mul t := Markov_integrable_exp_lin_Xmat n A t
  mgf_le t := by
    rw [Markov_mgf_lin_Xmat]

private theorem Markov_measurable_eval_filt (k : ℕ) (c : Sizes.SeqCoord sz) :
    Measurable[filt sz k] (fun ω : PathΩ sz => ω k c) := by
  have h : Measurable[filt sz k] (fun ω : PathΩ sz => ω k) := by
    have : (fun ω : PathΩ sz => ω k)
        = (fun g : Set.Iic k → Sizes.SeqΩ sz => g ⟨k, Set.mem_Iic.2 le_rfl⟩)
          ∘ (Preorder.restrictLe (π := fun _ : ℕ => Sizes.SeqΩ sz) k) := rfl
    rw [this]
    exact (measurable_pi_apply (⟨k, Set.mem_Iic.2 le_rfl⟩ : Set.Iic k)).comp
      (comap_measurable (Preorder.restrictLe (π := fun _ : ℕ => Sizes.SeqΩ sz) k))
  exact (measurable_pi_apply c).comp h

/-- The identity direction is non-degenerate at every size: the diagonal coordinate
`⟨n, (0, 0, true)⟩` has coefficient `1` in `Re tr (seqXmat sz n ·)` and variance `gueUnitVar = 1`. -/
private theorem Markov_vGue_one_pos (n : ℕ) :
    0 < (vGue sz n (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℝ) := by
  classical
  set c0 : Sizes.SeqCoord sz := ⟨n, (0, 0, true)⟩ with hc0
  have hcoef : linTr n (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
      (Sizes.seqXmat sz n (Pi.single c0 1)) = 1 := by
    unfold linTr
    rw [Matrix.one_mul, Matrix.trace, Complex.re_sum]
    have hdiag : ∀ j : Idx d (sz.L n) (sz.W n),
        (Matrix.diag (Sizes.seqXmat sz n (Pi.single c0 1)) j).re
          = if j = 0 then 1 else 0 := by
      intro j
      simp only [Matrix.diag_apply]
      change (Xentry d (sz.L n) (sz.W n) (Sizes.slice sz n (Pi.single c0 1)) j j).re = _
      unfold Xentry
      simp only [lt_self_iff_false, ite_false, Sizes.slice]
      by_cases hj : j = 0
      · subst hj; simp [hc0]
      · have hne : (⟨n, (j, j, true)⟩ : Sizes.SeqCoord sz) ≠ c0 := by
          intro h
          apply hj
          rw [hc0] at h
          simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and, and_true] at h
          exact h.1
        simp [hne, hj]
    rw [Finset.sum_congr rfl fun j _ => hdiag j]
    simp
  have hvar : (0 : ℝ) < (gueUnitVar sz c0 : ℝ) := by
    unfold gueUnitVar; split_ifs <;> norm_num
  have hmem : c0 ∈ coordFinset (sz := sz) n := by
    unfold coordFinset
    exact Finset.mem_map.2 ⟨(0, 0, true), Finset.mem_univ _, rfl⟩
  rw [Markov_vGue_eq_sum]
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun c =>
    (linTr n (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
      (Sizes.seqXmat sz n (Pi.single c 1))) ^ 2 * (gueUnitVar sz c : ℝ))
    (fun c _ => by positivity) hmem)
  simp only [hcoef, one_pow, one_mul]
  exact hvar

end LinearSubgaussian

end RBM.Univ.GUEPhase

/-! ## Compiled nonempty instances

`d = 3`, the sizes `RBM.Gauss.SizesInst.sz0` of `Grid.lean` §`GridCheck` (`L n = 4 (n + 1)`,
`W n = (2 (n + 1))^5`; size index `0`: `L = 4`, `W = 32`, `N = 2097152`), the identity direction
`A = 1`, and the diagonal coordinate `c₀ = ⟨0, (0, 0, true)⟩`.  The frozen variable of the freezing
instances is the real draw `ω k c₀` of step `k` (a non-constant `filt sz0 k`-measurable function),
and the frozen function is `F y x = cos y · Re tr (seqXmat sz0 0 x)`; every deterministic hypothesis
is discharged.  `vGue sz0 n 1 > 0` (`MarkovInst.vGue_one_pos_sz0`) shows the Gaussian laws are not
degenerate. -/

namespace RBM.Univ.GUEPhase.MarkovInst

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.LinearForm RBM.Path
  RBM.Univ.GUEPhase RBM.Gauss.SizesInst
open scoped NNReal ENNReal MeasureTheory

/-- The identity direction at size index `0` of `sz0`. -/
abbrev markovInstOne : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ := 1

/-- The diagonal coordinate `⟨0, (0, 0, true)⟩` of size index `0`. -/
def markovInstCoord : Sizes.SeqCoord sz0 := ⟨0, (0, 0, true)⟩

/-- The frozen function `F y x = cos y · Re tr (A · seqXmat sz0 0 x)`, `A = 1`. -/
def markovInstF (y : ℝ) (x : Sizes.SeqΩ sz0) : ℝ :=
  Real.cos y * linTr 0 markovInstOne (Sizes.seqXmat sz0 0 x)

/-- `vGue sz n 1 > 0` at every size of `sz0`. -/
theorem vGue_one_pos_sz0 (n : ℕ) :
    0 < (vGue sz0 n (1 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) : ℝ) :=
  Markov_vGue_one_pos n

/-- **`gueMap_lin_Xmat` at `sz0`, `A = 1`, every size index `n`**, with the nondegenerate
variance `vGue sz0 n 1 > 0`. -/
theorem gueMap_lin_Xmat_sz0 (n : ℕ) :
    (gueUnit sz0).map (fun y => linTr n
        (1 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ)
        (Sizes.seqXmat sz0 n y))
      = gaussianReal 0 (vGue sz0 n 1) ∧ 0 < (vGue sz0 n 1 : ℝ) :=
  ⟨gueMap_lin_Xmat sz0 n 1, vGue_one_pos_sz0 n⟩

private theorem markovInstF_measurable :
    Measurable (fun p : ℝ × Sizes.SeqΩ sz0 => markovInstF p.1 p.2) :=
  (Real.measurable_cos.comp measurable_fst).mul
    ((Markov_measurable_linTr_seqXmat 0 markovInstOne).comp measurable_snd)

private theorem markovInst_integrable (k : ℕ) :
    Integrable (fun ω : PathΩ sz0 => markovInstF (ω k markovInstCoord) (ω (k + 1))) (Pgue sz0) := by
  have hL : Integrable (fun x : Sizes.SeqΩ sz0 => linTr 0 markovInstOne (Sizes.seqXmat sz0 0 x))
      (gueUnit sz0) := (Markov_hasSubgaussianMGF_lin 0 markovInstOne).integrable
  have hmap : (Pgue sz0).map (fun ω : PathΩ sz0 => ω (k + 1)) = gueUnit sz0 :=
    Markov_map_incr sz0 k
  have hL' : Integrable (fun ω : PathΩ sz0 =>
      linTr 0 markovInstOne (Sizes.seqXmat sz0 0 (ω (k + 1)))) (Pgue sz0) := by
    have h2 : Integrable (fun x : Sizes.SeqΩ sz0 => linTr 0 markovInstOne (Sizes.seqXmat sz0 0 x))
        ((Pgue sz0).map (fun ω : PathΩ sz0 => ω (k + 1))) := by rw [hmap]; exact hL
    exact (integrable_map_measure h2.aestronglyMeasurable
      (measurable_pi_apply (k + 1)).aemeasurable).1 h2
  have hcos : Measurable (fun ω : PathΩ sz0 => Real.cos (ω k markovInstCoord)) :=
    Real.measurable_cos.comp ((measurable_pi_apply markovInstCoord).comp (measurable_pi_apply k))
  exact hL'.bdd_mul (c := 1) hcos.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by simpa using Real.abs_cos_le_one _)

/-- **`gueCondExp_freeze` at `sz0`**: `β = ℝ`, `Y ω = ω k c₀`, `F y x = cos y · Re tr (seqXmat sz0 0 x)`;
the integrability hypothesis is discharged. -/
theorem gueCondExp_freeze_sz0 (k : ℕ) :
    (Pgue sz0)[fun ω : PathΩ sz0 => markovInstF (ω k markovInstCoord) (ω (k + 1)) | filt sz0 k]
      =ᵐ[Pgue sz0] fun ω => ∫ x, markovInstF (ω k markovInstCoord) x ∂(gueUnit sz0) :=
  gueCondExp_freeze sz0 k (Y := fun ω : PathΩ sz0 => ω k markovInstCoord)
    (Markov_measurable_eval_filt k markovInstCoord) (F := markovInstF) markovInstF_measurable
    (markovInst_integrable k)

private theorem markovInstF_subgaussian (y : ℝ) :
    HasSubgaussianMGF (markovInstF y) (vGue sz0 0 markovInstOne) (gueUnit sz0) where
  integrable_exp_mul t := by
    have h := Markov_integrable_exp_lin_Xmat (sz := sz0) 0 markovInstOne (t * Real.cos y)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [markovInstF]
    ring_nf
  mgf_le t := by
    have h := Markov_mgf_lin_Xmat (sz := sz0) 0 markovInstOne (t * Real.cos y)
    have hmgf : mgf (markovInstF y) (gueUnit sz0) t
        = mgf (fun x => linTr 0 markovInstOne (Sizes.seqXmat sz0 0 x)) (gueUnit sz0)
            (t * Real.cos y) := by
      simp only [mgf, markovInstF]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only
      ring_nf
    rw [hmgf, h]
    apply Real.exp_le_exp.2
    have hv : (0 : ℝ) ≤ (vGue sz0 0 markovInstOne : ℝ) := NNReal.coe_nonneg _
    have hc : Real.cos y ^ 2 ≤ 1 := by nlinarith [Real.sin_sq_add_cos_sq y, sq_nonneg (Real.sin y)]
    have : (t * Real.cos y) ^ 2 ≤ t ^ 2 := by
      rw [mul_pow]; nlinarith [sq_nonneg t]
    nlinarith

/-- **`gueHasCondSubgaussianMGF_of_frozen` at `sz0`**: the same `Y`, `F`; the uniform parameter is
`c = vGue sz0 0 1 > 0` (`vGue_one_pos_sz0`), and `∀ y, HasSubgaussianMGF (F y) c (gueUnit sz0)` is
proved (the mgf of `cos y · L` is `exp (v cos²y t²/2) ≤ exp (v t²/2)`). -/
theorem gueHasCondSubgaussianMGF_of_frozen_sz0 (k : ℕ) :
    HasCondSubgaussianMGF (filt sz0 k) ((filt sz0).le k)
      (fun ω : PathΩ sz0 => markovInstF (ω k markovInstCoord) (ω (k + 1)))
      (vGue sz0 0 markovInstOne) (Pgue sz0) :=
  gueHasCondSubgaussianMGF_of_frozen sz0 k (Y := fun ω : PathΩ sz0 => ω k markovInstCoord)
    (Markov_measurable_eval_filt k markovInstCoord) (F := markovInstF) markovInstF_measurable
    markovInstF_subgaussian

/-- **`gueHasCondSubgaussianMGF_linear` at `sz0`**: size index `0`, `s = 1`, the constant direction
`A = 1` (`filt sz0 k`-measurable), the non-trivial `filt sz0 k`-measurable set
`E = {ω | ω k c₀ ≤ 0}`, and `c = vGue sz0 0 1 > 0`; the hypothesis `s² vGue ≤ c` holds with
equality. -/
theorem gueHasCondSubgaussianMGF_linear_sz0 (k : ℕ) :
    HasCondSubgaussianMGF (filt sz0 k) ((filt sz0).le k)
      (fun ω => ({ω : PathΩ sz0 | ω k markovInstCoord ≤ 0} : Set (PathΩ sz0)).indicator
        (fun ω => (1 : ℝ) * linTr 0 markovInstOne (Sizes.seqXmat sz0 0 (ω (k + 1)))) ω)
      (vGue sz0 0 markovInstOne) (Pgue sz0) :=
  gueHasCondSubgaussianMGF_linear sz0 0 k 1 (A := fun _ => markovInstOne) measurable_const
    {ω : PathΩ sz0 | ω k markovInstCoord ≤ 0}
    (measurableSet_le (Markov_measurable_eval_filt k markovInstCoord) measurable_const)
    (vGue sz0 0 markovInstOne) (fun _ _ => by simp)

/-- The hypothesis `Tendsto sz0.size atTop atTop` of `gue_highProb_incr_le` (from the merged
`sz0_tendsto`). -/
theorem sz0_size_tendsto_nat : Tendsto (fun n => sz0.size n) atTop atTop :=
  tendsto_natCast_atTop_iff.1 sz0_tendsto

/-- **`gue_highProb_incr_le` at `sz0`, `n0 = 1`** (`d = 3`; `gueGridK sz0 1 n = (sz0.size n + 1)^96`):
the hypothesis `Tendsto sz0.size atTop atTop` is discharged. -/
theorem gue_highProb_incr_le_sz0 :
    HighProbAt (Pgue sz0) sz0.size (fun n => {ω | ∀ k, 1 ≤ k → k ≤ gueGridK sz0 1 n →
      ∀ i j : Idx 3 (sz0.L n) (sz0.W n),
        ‖Sizes.seqXmat sz0 n (ω k) i j‖ ≤ ((sz0.size n : ℕ) : ℝ)}) :=
  gue_highProb_incr_le sz0 1 sz0_size_tendsto_nat

end RBM.Univ.GUEPhase.MarkovInst

end
