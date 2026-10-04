/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Green.IBP
import RBM3D.Green.Pins
import RBM3D.Green.EntryDom
import RBM3D.Green.LDE
import RBM3D.Green.IBPPoly
import RBM3D.Induction.PerTimeCalc
import RBM3D.Gauss.DominationAt
import RBM3D.Loop.GLoop

/-!
# `≺` under `E_k`, the minor replacement (4.9) and (`GijGEX`), (`GiiGEX`) for the Gaussian flow,
`d ≥ 3` (S1-24)

Ticket T2101.  Port of `RBM2D/Green/CondDom.lean` (359 declaration lines of 647), 
`RBM2D/Green/CondStable.lean` (433 of 645) and `RBM2D/Green/EntryGauss.lean` (108 of 151) at RBM2D
commit `c9a24cf`, to the `d`-dimensional sequence model of `RBM3D/Gauss/FineModel.lean`, with the
renaming rules R1-R4 of `docs/tickets/ST1-COMMON.md` (item 2): `d : Sizes` becomes `sz : Sizes d`,
`Z2 L`/`Idx L W` become `Zd d L`/`Idx d L W`, `size = (W L)^2` becomes `sz.size n = (W L)^d`,
`svar (sz.L n) (sz.W n)` becomes `svarF d (sz.L n) (sz.W n) (sz.lam n)`, `spectralZ`, `spectralM`
become the merged `zt`, `mE`.  The paper (arXiv:2507.20274) does not state these as lemmas:
`paper/tex/3_5_Loop_Hierarchy.tex:37` says that the estimates of `lem_GbEXP` (among them
(`GijGEX`), (`GiiGEX`), (`GavLGEX`)) have been proven as Lemma 4.1 of `[YY_25]` and that their
proofs are dimension-independent.  The mathematics is that of RBM1D `Gauss/CondDom.lean`
(`c06b103`): the exceptional event of Definition 2.1 (i) does not disappear under `E_k`, so a
deterministic envelope, the Fubini identity for the row section and Markov are needed.

## Contents (namespace `RBM.Green`)

* **CondDom** (`RBM2D/Green/CondDom.lean`): `condRowReal`, `rowSlice`, `measurableSet_rowSlice`,
  `measurable_measure_rowSlice`, `lintegral_measure_rowSlice`, `meas_measure_rowSlice_ge` (`E_k` of
  a real observable, the row section of a set, its measure, Fubini and Markov);
  `norm_condRow_le_split` (the pointwise good/bad split); `norm_green_diag_sub_mE_le`,
  `norm_condExpDiag_sub_le_offdiag` (the weighted reduction of `ibpRem`, diagonal coefficient
  `S_ii = W^{-d} (1 + 2 d g²)⁻¹ = svarF_diag`); `etaT_le_of_le`, `W_le_self`;
  **`perTimeDomAt_of_moment`** (moments give `≺`, per time and per index).
* **CondStable** (`RBM2D/Green/CondStable.lean`): `perTimeDomAt_const`,
  `perTimeDomAt_of_le_left_on`, `perTimeDomAt_of_highProb`, `inv_etaT_le_inv_etaT`,
  `perTimeDomAt_condRow_of_envelope` (`≺` under `E_k`), `perTimeDomAt_condRow_sub_self`,
  **`norm_greenDiagCentered_sub_minor_le`** ((4.9) on the good event).
* **EntryGauss** (`RBM2D/Green/EntryGauss.lean`): `gijOmegaSeq`, `giiOmegaSeq`,
  **`giiSeq_of_asGMc`**, `gijSeq_of_asGMc` (the `lem_GbEXP` components for the Gaussian flow with no
  large deviation hypothesis; the last two are conditional adapters, under `AsGMcSeq`).

## Differences from RBM2D (residual, after the renaming)

* `hG : GaussIBP d` is dropped (`gaussIBP` is a theorem, T2091 audit O1): `ibpRem_eq_add`,
  `condExpDiag_eq_sum_Sblk` are called without it.
* `W_le_self` and `perTimeDomAt_of_le_left_on` take `hd : 1 ≤ d` (RBM2D had `size = (W L)^2 ≥ 9`;
  at `d = 0` one has `size = 1`); paper-delta candidate `T2101a`.
* The EntryGauss statements take `hA : sz.Admissible 𝔠 𝔡` (merged `entry_bound_stochDom`,
  `GbEXPHypV3` order) in place of RBM2D's `hsz : SizeTendsto`, `hbw : Bandwidth`, and
  `giiOmegaSeq`, `giiSeq_of_asGMc` take `hd : 3 ≤ d` (merged `diag_bound_stochDom*`); `T2101b`.
* The only `Path/Scales` helper the three files use is `etaT`, which is the merged
  `RBM.Gauss.etaT` (`Loop/GLoop.lean:75`); no private scales copy is needed.
* Not ported: the private `Checks` sections of RBM2D (replaced by the instances at the end of
  this file at `d = 3`).
-/

set_option linter.style.longLine false

namespace RBM.Green

open MeasureTheory ProbabilityTheory Filter Matrix RBM.Gauss RBM.Path RBM.Ind.PerTimeCalc.PerTime
open scoped ENNReal

variable {d : ℕ} {sz : Sizes d} {n : ℕ}

/-! ### `E_k` of a real observable -/

/-- **`E_k[f]` for a real-valued `f`**, the same exact coordinate integral as `condRow`:
integrate the row-`k` coordinates out and freeze the others.  No `MeasureTheory.condExp` is
involved, and the identity is pointwise in `ω` (RBM2D `condRowReal`, `CondDom:84`). -/
noncomputable def condRowReal (sz : Sizes d) (n : ℕ) (k : Idx d (sz.L n) (sz.W n))
    (f : Sizes.SeqΩ sz → ℝ) : Sizes.SeqΩ sz → ℝ :=
  fun ω => ∫ ω', f (rowSplit sz n k ω ω') ∂(Sizes.seqP sz)

@[simp] theorem condRowReal_const (k : Idx d (sz.L n) (sz.W n)) (c : ℝ) :
    condRowReal sz n k (fun _ => c) = fun _ => c := by
  funext ω; simp [condRowReal]

/-! ### The row section of a set, and its measure -/

/-- The **row-`k` section** of `S` at `ω`: the `ω'` for which the split point `rowSplit k ω ω'`
lands in `S`.  `E_k[1_S](ω)` is its probability (RBM2D `rowSlice`, `CondDom:96`). -/
def rowSlice (sz : Sizes d) (n : ℕ) (k : Idx d (sz.L n) (sz.W n)) (S : Set (Sizes.SeqΩ sz))
    (ω : Sizes.SeqΩ sz) : Set (Sizes.SeqΩ sz) :=
  {ω' | rowSplit sz n k ω ω' ∈ S}

theorem measurableSet_rowSlice {k : Idx d (sz.L n) (sz.W n)} {S : Set (Sizes.SeqΩ sz)}
    (hS : MeasurableSet S) (ω : Sizes.SeqΩ sz) :
    MeasurableSet (rowSlice sz n k S ω) :=
  hS.preimage (measurable_rowSplit_right sz n k ω)

theorem measurable_measure_rowSlice (sz : Sizes d) (n : ℕ) (k : Idx d (sz.L n) (sz.W n))
    {S : Set (Sizes.SeqΩ sz)} (hS : MeasurableSet S) :
    Measurable fun ω => (Sizes.seqP sz) (rowSlice sz n k S ω) := by
  have hpre : MeasurableSet
      ((fun p : Sizes.SeqΩ sz × Sizes.SeqΩ sz => rowSplit sz n k p.1 p.2) ⁻¹' S) :=
    hS.preimage (measurable_rowSplit sz n k)
  exact measurable_measure_prodMk_left hpre

/-- **The Fubini identity for the row section.**  Averaging the probability of the section over
the frozen coordinates returns the probability of the set itself.  This is
`measurePreserving_rowSplit`, and it is the reason the exceptional event of Definition 2.1 (i) can
be controlled *after* conditioning. -/
theorem lintegral_measure_rowSlice (sz : Sizes d) (n : ℕ) (k : Idx d (sz.L n) (sz.W n))
    {S : Set (Sizes.SeqΩ sz)} (hS : MeasurableSet S) :
    ∫⁻ ω, (Sizes.seqP sz) (rowSlice sz n k S ω) ∂(Sizes.seqP sz) = (Sizes.seqP sz) S := by
  have hmeas := measurable_rowSplit sz n k
  have hpre : MeasurableSet
      ((fun p : Sizes.SeqΩ sz × Sizes.SeqΩ sz => rowSplit sz n k p.1 p.2) ⁻¹' S) :=
    hS.preimage hmeas
  have h1 : (Sizes.seqP sz) S
      = ((Sizes.seqP sz).prod (Sizes.seqP sz))
          ((fun p : Sizes.SeqΩ sz × Sizes.SeqΩ sz => rowSplit sz n k p.1 p.2) ⁻¹' S) := by
    conv_lhs => rw [← (measurePreserving_rowSplit sz n k).map_eq]
    exact Measure.map_apply hmeas hS
  rw [h1, Measure.prod_apply hpre]
  rfl

/-- **Markov for the row section.**  The set of frozen configurations whose section is not small
is itself small: `ε · P{ω : P(slice_ω) ≥ ε} ≤ P(S)`. -/
theorem meas_measure_rowSlice_ge (sz : Sizes d) (n : ℕ) (k : Idx d (sz.L n) (sz.W n))
    {S : Set (Sizes.SeqΩ sz)} (hS : MeasurableSet S) (ε : ℝ≥0∞) :
    ε * (Sizes.seqP sz) {ω | ε ≤ (Sizes.seqP sz) (rowSlice sz n k S ω)} ≤ (Sizes.seqP sz) S := by
  have h := mul_meas_ge_le_lintegral₀
    (μ := Sizes.seqP sz) (measurable_measure_rowSlice sz n k hS).aemeasurable ε
  rwa [lintegral_measure_rowSlice sz n k hS] at h

/-! ### The pointwise good/bad split of a row integral

On the good set the integrand obeys `‖X‖ ≤ c f`, and on the bad set it obeys only the
deterministic envelope, whose contribution is the envelope times the probability of the row
section. -/

/-- **The split.**  If `‖X‖ ≤ c f` off a set `S` and `‖X‖ ≤ Env` everywhere, then

  `‖E_k[X](ω)‖ ≤ c E_k[f](ω) + Env · P(slice of S at ω)`. -/
theorem norm_condRow_le_split {k : Idx d (sz.L n) (sz.W n)} {X : Sizes.SeqΩ sz → ℂ}
    (hX : Measurable X) {f : Sizes.SeqΩ sz → ℝ} (hf0 : ∀ ω, 0 ≤ f ω)
    (hfint : ∀ ω : Sizes.SeqΩ sz,
      Integrable (fun ω' => f (rowSplit sz n k ω ω')) (Sizes.seqP sz))
    {Env c : ℝ} (hEnv : ∀ σ, ‖X σ‖ ≤ Env) (hc : 0 ≤ c)
    {S : Set (Sizes.SeqΩ sz)} (hS : MeasurableSet S)
    (hgood : ∀ σ, σ ∉ S → ‖X σ‖ ≤ c * f σ) (ω : Sizes.SeqΩ sz) :
    ‖condRow sz n k X ω‖
      ≤ c * condRowReal sz n k f ω + Env * (Sizes.seqP sz).real (rowSlice sz n k S ω) := by
  have hsm := measurable_rowSplit_right sz n k ω
  have hSω : MeasurableSet (rowSlice sz n k S ω) := measurableSet_rowSlice hS ω
  have hXint : Integrable (fun ω' => X (rowSplit sz n k ω ω')) (Sizes.seqP sz) :=
    Integrable.mono' (integrable_const Env) ((hX.comp hsm).aestronglyMeasurable)
      (Eventually.of_forall fun _ => hEnv _)
  have hindint : Integrable ((rowSlice sz n k S ω).indicator fun _ => Env) (Sizes.seqP sz) :=
    (integrable_const Env).indicator hSω
  have hcf : Integrable (fun ω' => c * f (rowSplit sz n k ω ω')) (Sizes.seqP sz) :=
    (hfint ω).const_mul c
  have hpt : ∀ ω' : Sizes.SeqΩ sz, ‖X (rowSplit sz n k ω ω')‖
      ≤ c * f (rowSplit sz n k ω ω')
        + (rowSlice sz n k S ω).indicator (fun _ => Env) ω' := by
    intro ω'
    by_cases hω' : ω' ∈ rowSlice sz n k S ω
    · rw [Set.indicator_of_mem hω']
      have h1 := hEnv (rowSplit sz n k ω ω')
      have h2 : 0 ≤ c * f (rowSplit sz n k ω ω') := mul_nonneg hc (hf0 _)
      linarith
    · rw [Set.indicator_of_notMem hω']
      have h1 := hgood (rowSplit sz n k ω ω') hω'
      linarith
  rw [condRow_apply]
  calc ‖∫ ω', X (rowSplit sz n k ω ω') ∂(Sizes.seqP sz)‖
      ≤ ∫ ω', ‖X (rowSplit sz n k ω ω')‖ ∂(Sizes.seqP sz) := norm_integral_le_integral_norm _
    _ ≤ ∫ ω', (c * f (rowSplit sz n k ω ω')
        + (rowSlice sz n k S ω).indicator (fun _ => Env) ω') ∂(Sizes.seqP sz) :=
        integral_mono hXint.norm (hcf.add hindint) hpt
    _ = c * condRowReal sz n k f ω + Env * (Sizes.seqP sz).real (rowSlice sz n k S ω) := by
        rw [integral_add hcf hindint, integral_const_mul,
          integral_indicator_const _ hSω, smul_eq_mul, mul_comm ((Sizes.seqP sz).real _) Env]
        rfl

/-! ### The envelope of `G_{ii} - m`, and the weighted reduction of the remainder `ibpRem` -/

section Assembly

variable {E t : ℝ}

/-- `|G_{ii} - m| ≤ η_t⁻¹ + 1` on the whole space (RBM2D `norm_green_diag_sub_mE_le`,
`CondDom:201`); the merged `norm_greenDiagCentered_le_env`, with `(zt E t).im = η_t`. -/
theorem norm_green_diag_sub_mE_le (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (i : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    ‖green (Sizes.seqHflow sz n u ω) (zt E t) i i - mE E‖ ≤ (etaT E t)⁻¹ + 1 := by
  have h := norm_greenDiagCentered_le_env (sz := sz) (n := n) hE ht u i ω
  rwa [← etaT_eq_zt_im] at h

/-- **The weighted reduction.**  The remainder of the integration-by-parts display,
`E_i(G_{ii} - m) - t m² ∑_k S_{ik} (G_{kk} - m)`, is bounded by a bound `A` on
`ibpRem sz n E t (i, k)` for `k ≠ i`, plus the diagonal term with its own bound and its own
coefficient `S_ii`: the row sums of `S` are one (`IBP_sum_svarF_row`), so

  `‖remainder‖ ≤ A + S_{ii} · A_diag`

as soon as `‖ibpRem(i,k)‖ ≤ A` for `k ≠ i` and `‖ibpRem(i,i)‖ ≤ A_diag`.  Here
`S_ii = svarF (i, i) = W^{-d} (1 + 2 d g²)⁻¹` (RBM2D `norm_condExpDiag_sub_le_offdiag`,
`CondDom:217`: `(5 W²)⁻¹`), `g = sz.lam n`. -/
theorem norm_condExpDiag_sub_le_offdiag (hE : |E| < 2) (ht0 : 0 ≤ t)
    (ht : t < 1) (i : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) {A Adiag : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ k : Idx d (sz.L n) (sz.W n), k ≠ i → ‖ibpRem sz n E t (i, k) ω‖ ≤ A)
    (hAd : ‖ibpRem sz n E t (i, i) ω‖ ≤ Adiag) :
    ‖condExpDiag sz n t (zt E t) (mE E) i ω
        - (t : ℂ) * mE E ^ 2 * ∑ k, (svarF d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ)
          * (green (Sizes.seqHflow sz n t ω) (zt E t) k k - mE E)‖
      ≤ A + svarF d (sz.L n) (sz.W n) (sz.lam n) i i * Adiag := by
  classical
  have hterm : ∀ k : Idx d (sz.L n) (sz.W n),
      (svarF d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ) * ibpRem sz n E t (i, k) ω
      = (svarF d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ) * condRow sz n i
          (fun η => green (Sizes.seqHflow sz n t η) (zt E t) i i
            * (green (Sizes.seqHflow sz n t η) (zt E t) k k - mE E)) ω
        - mE E * ((svarF d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ)
          * (green (Sizes.seqHflow sz n t ω) (zt E t) k k - mE E)) := by
    intro k
    simp only [ibpRem]
    ring
  have hkey : condExpDiag sz n t (zt E t) (mE E) i ω
      - (t : ℂ) * mE E ^ 2 * ∑ k, (svarF d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ)
        * (green (Sizes.seqHflow sz n t ω) (zt E t) k k - mE E)
      = (t : ℂ) * mE E
        * ∑ k, (svarF d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ) * ibpRem sz n E t (i, k) ω := by
    rw [condExpDiag_eq_sum_Sblk hE hE.le ht0 ht i ω,
      Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hterm k),
      Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hSrow := IBP_sum_svarF_row (d := d) (L := sz.L n) (W := sz.W n) (sz.lam n)
    (sz.three_le_L n) i
  have hsum : ‖∑ k, (svarF d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ) * ibpRem sz n E t (i, k) ω‖
      ≤ A + svarF d (sz.L n) (sz.W n) (sz.lam n) i i * Adiag := by
    have hstep : ∑ k, svarF d (sz.L n) (sz.W n) (sz.lam n) i k * ‖ibpRem sz n E t (i, k) ω‖
        ≤ A + svarF d (sz.L n) (sz.W n) (sz.lam n) i i * Adiag := by
      rw [← Finset.add_sum_erase Finset.univ
        (fun k => svarF d (sz.L n) (sz.W n) (sz.lam n) i k * ‖ibpRem sz n E t (i, k) ω‖)
        (Finset.mem_univ i)]
      have hdiagle : svarF d (sz.L n) (sz.W n) (sz.lam n) i i * ‖ibpRem sz n E t (i, i) ω‖
          ≤ svarF d (sz.L n) (sz.W n) (sz.lam n) i i * Adiag :=
        mul_le_mul_of_nonneg_left hAd (svarF_nonneg _ _ _ _ _ _)
      have hoffle : ∑ k ∈ Finset.univ.erase i,
            svarF d (sz.L n) (sz.W n) (sz.lam n) i k * ‖ibpRem sz n E t (i, k) ω‖ ≤ A := by
        calc ∑ k ∈ Finset.univ.erase i,
              svarF d (sz.L n) (sz.W n) (sz.lam n) i k * ‖ibpRem sz n E t (i, k) ω‖
            ≤ ∑ k ∈ Finset.univ.erase i, svarF d (sz.L n) (sz.W n) (sz.lam n) i k * A := by
              refine Finset.sum_le_sum fun k hk => ?_
              exact mul_le_mul_of_nonneg_left (hA k (Finset.ne_of_mem_erase hk))
                (svarF_nonneg _ _ _ _ _ _)
          _ = (∑ k ∈ Finset.univ.erase i, svarF d (sz.L n) (sz.W n) (sz.lam n) i k) * A := by
              rw [Finset.sum_mul]
          _ ≤ (∑ k, svarF d (sz.L n) (sz.W n) (sz.lam n) i k) * A := by
              refine mul_le_mul_of_nonneg_right ?_ hA0
              exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
                fun k _ _ => svarF_nonneg _ _ _ _ _ _
          _ = A := by rw [hSrow, one_mul]
      linarith
    calc ‖∑ k, (svarF d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ) * ibpRem sz n E t (i, k) ω‖
        ≤ ∑ k, ‖(svarF d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ) * ibpRem sz n E t (i, k) ω‖ :=
          norm_sum_le _ _
      _ = ∑ k, svarF d (sz.L n) (sz.W n) (sz.lam n) i k * ‖ibpRem sz n E t (i, k) ω‖ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (svarF_nonneg _ _ _ _ _ _)]
      _ ≤ A + svarF d (sz.L n) (sz.W n) (sz.lam n) i i * Adiag := hstep
  rw [hkey, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_mE hE.le,
    mul_one]
  have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht.le
  calc |t| * ‖∑ k, (svarF d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ) * ibpRem sz n E t (i, k) ω‖
      ≤ 1 * ‖∑ k, (svarF d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ) * ibpRem sz n E t (i, k) ω‖ :=
        mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
    _ = ‖∑ k, (svarF d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ) * ibpRem sz n E t (i, k) ω‖ :=
        one_mul _
    _ ≤ A + svarF d (sz.L n) (sz.W n) (sz.lam n) i i * Adiag := hsum

end Assembly

/-! ### `η_t` is decreasing in `t`, and `W ≤ size` -/

/-- `η_t ≤ η_u` for `u ≤ t` (RBM2D `etaT_le_of_le`, `CondDom:292`), for `RBM.Gauss.etaT`. -/
theorem etaT_le_of_le {E : ℝ} (hE : |E| < 2) {u t : ℝ} (hut : u ≤ t) : etaT E t ≤ etaT E u := by
  change (1 - t) * (mE E).im ≤ (1 - u) * (mE E).im
  exact mul_le_mul_of_nonneg_right (by linarith) (mE_im_pos hE).le

/-- **`W ≤ size`** (RBM2D `W_le_self`, `CondDom:298`).  For `d ≥ 1`, `size n = (W L)^d`, so
`W ≤ W L ≤ (W L)^d` for every `n`; at `d = 0` one has `size = 1` and the statement is false
(paper-delta candidate `T2101a`). -/
theorem W_le_self (sz : Sizes d) (hd : 1 ≤ d) (n : ℕ) : sz.W n ≤ sz.size n := by
  have hL := sz.three_le_L n
  have hW := sz.W_pos n
  calc sz.W n ≤ sz.W n * sz.L n := Nat.le_mul_of_pos_right _ (by omega)
    _ ≤ (sz.W n * sz.L n) ^ d := Nat.le_self_pow (by omega) _

/-! ### Moments give `≺`, per time and per index -/

/-- **Markov's inequality, per time.**  The moment version of `PerTimeDomAt`, and the reason the
fixed-time inputs need no net: `PerTimeDomAt` bounds the failure probability at each index (and
each time) separately, so no union bound -- and hence no cardinality hypothesis, in contrast with
`stochDomAt_of_momentDomAt` -- is taken.  RBM2D `perTimeDomAt_of_moment` (`CondDom:316`), RBM1D
`unifDomIcc_of_moment` at one time; the size index `l` (`= n`) carries
`size l` in every power.

`hsize` replaces RBM1D's `N → ∞`; it cannot be dropped: on the constant sizes `L = 3`, `W = 2`
(`size ≡ 6^d`), `Y ≡ 10`, `Φ ≡ 1` satisfy `MomentDomAt`, while
`P{size^{1/10} Φ < |Y|} = 1 > size^{-1}` (the private `condDom_no_hsize` below, at `d = 3`).  The
threshold of the constant is `C ≤ size^{τp - D}` with `p ≥ (D + 1)/τ` (so the exponent is `≥ 1`). -/
theorem perTimeDomAt_of_moment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {size : ℕ → ℕ} (hsize : Tendsto size atTop atTop) {U : ℕ → Type*}
    {Y : ∀ l, U l → Ω → ℝ} {Φ : ∀ l, U l → ℝ} (hΦ : ∀ l u, 0 < Φ l u)
    (hint : ∀ (p l : ℕ) (u : U l), Integrable (fun ω => |Y l u ω| ^ (2 * p)) P)
    (hmom : MomentDomAt P size Y Φ) :
    PerTimeDomAt P size Y (fun l u _ => Φ l u) := by
  intro τ hτ D hD
  obtain ⟨p, hp⟩ := exists_nat_ge ((D + 1) / τ)
  have hDp : D + 1 ≤ τ * (p : ℝ) := by rw [div_le_iff₀ hτ] at hp; linarith
  obtain ⟨C, hC0, hCN⟩ := hmom τ hτ p
  have hexp : 0 < τ * (p : ℝ) - D := by linarith
  filter_upwards [hCN, hsize.eventually (eventually_ge_atTop 1),
    hsize.eventually (eventually_le_rpow C hexp)] with l hN hsize1 hCle u
  have hNpos : (0 : ℝ) < size l := by exact_mod_cast hsize1
  have hΦu := hΦ l u
  have hrp : (0 : ℝ) < (size l : ℝ) ^ τ := Real.rpow_pos_of_pos hNpos τ
  have ht : 0 < (size l : ℝ) ^ τ * Φ l u := mul_pos hrp hΦu
  refine (meas_gt_le_of_moment P ht (hint p l u) (hN u)).trans (ENNReal.ofReal_le_ofReal ?_)
  set a : ℝ := (size l : ℝ) ^ (τ * (p : ℝ)) with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos hNpos _
  have hb : (0 : ℝ) < Φ l u ^ (2 * p) := by positivity
  have h1 : ((size l : ℝ) ^ τ * Φ l u) ^ (2 * p) = a * a * Φ l u ^ (2 * p) := by
    rw [mul_pow, ha_def, ← Real.rpow_natCast ((size l : ℝ) ^ τ) (2 * p),
      ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]
    push_cast
    ring_nf
  have h2 : C * (a * Φ l u ^ (2 * p)) / (a * a * Φ l u ^ (2 * p)) = C * a⁻¹ := by
    field_simp
  have h3 : a⁻¹ = (size l : ℝ) ^ (-(τ * (p : ℝ))) := by
    rw [ha_def, Real.rpow_neg hNpos.le]
  rw [h1, h2]
  calc C * a⁻¹ ≤ (size l : ℝ) ^ (τ * (p : ℝ) - D) * a⁻¹ :=
        mul_le_mul_of_nonneg_right hCle (inv_nonneg.2 ha.le)
    _ = (size l : ℝ) ^ (-D) := by
        rw [h3, ← Real.rpow_add hNpos]
        congr 1
        ring

/-! ### Elementary facts on `size` -/

/-- `2 N^{-(D+1)} ≤ N^{-D}` for `2 ≤ N` (the pointwise form of `eventually_two_mul_rpow_le`; RBM2D
`CondStable_two_mul_rpow_le`, `CondStable:87`). -/
private theorem CondStable_two_mul_rpow_le {N : ℕ} (hN : 2 ≤ N) (D : ℝ) :
    2 * (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  rw [neg_add, Real.rpow_add hN0, Real.rpow_neg_one]
  have h := Real.rpow_nonneg hN0.le (-D)
  calc 2 * ((N : ℝ) ^ (-D) * (N : ℝ)⁻¹) = (N : ℝ) ^ (-D) * (2 / N) := by ring
    _ ≤ (N : ℝ) ^ (-D) * 1 := by
        gcongr; rw [div_le_one hN0]; exact hN2
    _ = _ := mul_one _

/-- `3 ≤ size` for `d ≥ 1` (RBM2D `CondStable_nine_le_size`, `CondStable:79`: `9 ≤ (W L)^2`):
`size = (W L)^d ≥ W L ≥ 3`.  False at `d = 0` (`size = 1`). -/
private theorem CondStable_three_le_size (sz : Sizes d) (hd : 1 ≤ d) (n : ℕ) : 3 ≤ sz.size n := by
  have hL := sz.three_le_L n
  have hW := sz.W_pos n
  have h3 : 3 ≤ sz.W n * sz.L n := by nlinarith
  calc 3 ≤ sz.W n * sz.L n := h3
    _ ≤ (sz.W n * sz.L n) ^ d := Nat.le_self_pow (by omega) _

/-! ### Combinators for `PerTimeDomAt` that have no merged equivalent -/

/-- **A deterministic eventual inequality is a `≺`** (RBM2D `perTimeDomAt_const`,
`CondStable:102`; RBM1D `unifDomIcc_const`).  `size ≥ 1` holds for every
`Sizes` (`Sizes.one_le_size`), so there is no `hsize` and no `hd`. -/
theorem perTimeDomAt_const (sz : Sizes d) {V : ℕ → Type*} {f g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n)
    (hfg : ∀ᶠ n : ℕ in atTop, f n ≤ g n) :
    PerTimeDomAt (Sizes.seqP sz) sz.size
      (fun n (_ : V n) (_ : Sizes.SeqΩ sz) => f n) (fun n _ _ => g n) := by
  intro τ hτ D hD
  filter_upwards [hfg] with n hn a
  have hs : (1 : ℝ) ≤ (sz.size n : ℝ) := by exact_mod_cast sz.one_le_size n
  have h1 : (1 : ℝ) ≤ (sz.size n : ℝ) ^ τ := Real.one_le_rpow hs hτ.le
  have hsub : {ω : Sizes.SeqΩ sz | (sz.size n : ℝ) ^ τ * g n < f n} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    nlinarith [hg n]
  rw [hsub, measure_empty]
  exact zero_le

/-- **Monotonicity in the dominated quantity, on a high-probability event** (RBM2D
`perTimeDomAt_of_le_left_on`, `CondStable:123`; RBM1D `UnifDomIcc.of_le_left_on`).
The event costs one more `size^{-(D+1)}`, and
`2 size^{-(D+1)} ≤ size^{-D}` holds since `size ≥ 3` (`hd : 1 ≤ d`; at `d = 0` `size = 1`,
paper-delta candidate `T2101a`). -/
theorem perTimeDomAt_of_le_left_on {sz : Sizes d} (hd : 1 ≤ d) {V : ℕ → Type*}
    {ξ ξ' ζ : ∀ n, V n → Sizes.SeqΩ sz → ℝ} {Ξ : ℕ → Set (Sizes.SeqΩ sz)}
    (hΞ : HighProbAt (Sizes.seqP sz) sz.size Ξ)
    (hle : ∀ᶠ n : ℕ in atTop, ∀ ω ∈ Ξ n, ∀ a : V n, ξ' n a ω ≤ ξ n a ω)
    (h : PerTimeDomAt (Sizes.seqP sz) sz.size ξ ζ) :
    PerTimeDomAt (Sizes.seqP sz) sz.size ξ' ζ := by
  intro τ hτ D hD
  have hD1 : (0 : ℝ) < D + 1 := by linarith
  filter_upwards [h τ hτ (D + 1) hD1, hΞ (D + 1) hD1, hle] with n hN hΞN hleN a
  have hp : (0 : ℝ) ≤ (sz.size n : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsub : {ω | (sz.size n : ℝ) ^ τ * ζ n a ω < ξ' n a ω}
      ⊆ {ω | (sz.size n : ℝ) ^ τ * ζ n a ω < ξ n a ω} ∪ (Ξ n)ᶜ := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    by_cases hmem : ω ∈ Ξ n
    · exact Or.inl (lt_of_lt_of_le hω (hleN ω hmem a))
    · exact Or.inr hmem
  calc (Sizes.seqP sz) {ω | (sz.size n : ℝ) ^ τ * ζ n a ω < ξ' n a ω}
      ≤ (Sizes.seqP sz) ({ω | (sz.size n : ℝ) ^ τ * ζ n a ω < ξ n a ω} ∪ (Ξ n)ᶜ) :=
        measure_mono hsub
    _ ≤ _ + _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((sz.size n : ℝ) ^ (-(D + 1)))
          + ENNReal.ofReal ((sz.size n : ℝ) ^ (-(D + 1))) :=
        add_le_add (hN a) hΞN
    _ = ENNReal.ofReal (2 * (sz.size n : ℝ) ^ (-(D + 1))) := by
        rw [two_mul, ENNReal.ofReal_add hp hp]
    _ ≤ ENNReal.ofReal ((sz.size n : ℝ) ^ (-D)) :=
        ENNReal.ofReal_le_ofReal
          (CondStable_two_mul_rpow_le (by have := CondStable_three_le_size sz hd n; omega) D)

/-- **A deterministic bound on a high-probability event gives a `≺`** (RBM2D
`perTimeDomAt_of_highProb`, `CondStable:156`; RBM1D `unifDomIcc_of_highProb`).  No condition on
`size` is needed. -/
theorem perTimeDomAt_of_highProb {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {size : ℕ → ℕ} {U : ℕ → Type*} {ξ ζ : ∀ l, U l → Ω → ℝ} {Ξ : ℕ → Set Ω}
    (hΞ : HighProbAt P size Ξ)
    (hle : ∀ τ > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ ω ∈ Ξ l, ∀ a : U l,
      ξ l a ω ≤ (size l : ℝ) ^ τ * ζ l a ω) :
    PerTimeDomAt P size ξ ζ := by
  intro τ hτ D hD
  filter_upwards [hΞ D hD, hle τ hτ] with l hΞl hlel a
  refine le_trans (measure_mono ?_) hΞl
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  exact fun hmem => absurd (hlel ω hmem a) (not_le.2 hω)

/-- **`≺` is transitive** (RBM2D `CondStable_trans`, `CondStable:172`; RBM1D `UnifDomIcc.trans`),
from the merged `perTimeCalc_of_imp_union` with the `τ/2` split.  Private: it is used only by
`perTimeDomAt_condRow_sub_self`. -/
private theorem CondStable_trans {sz : Sizes d} (hsize : Tendsto sz.size atTop atTop)
    {V : ℕ → Type*} {ξ ζ χ : ∀ n, V n → Sizes.SeqΩ sz → ℝ}
    (h₁ : PerTimeDomAt (Sizes.seqP sz) sz.size ξ ζ)
    (h₂ : PerTimeDomAt (Sizes.seqP sz) sz.size ζ χ) :
    PerTimeDomAt (Sizes.seqP sz) sz.size ξ χ := by
  refine perTimeCalc_of_imp_union hsize h₁ h₂ (fun τ hτ => ⟨τ / 2, half_pos hτ,
    Eventually.of_forall fun n u ω hω => ?_⟩)
  by_contra hno
  simp only [not_or, not_lt] at hno
  have hpos : (0 : ℝ) ≤ (sz.size n : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hcalc : ξ n u ω ≤ (sz.size n : ℝ) ^ τ * χ n u ω :=
    calc ξ n u ω ≤ (sz.size n : ℝ) ^ (τ / 2) * ζ n u ω := hno.1
      _ ≤ (sz.size n : ℝ) ^ (τ / 2) * ((sz.size n : ℝ) ^ (τ / 2) * χ n u ω) :=
          mul_le_mul_of_nonneg_left hno.2 hpos
      _ = (sz.size n : ℝ) ^ τ * χ n u ω := by
          rw [← mul_assoc, RBM.UnifDetDom.rpow_half_mul_rpow_half (sz.size n) hτ]
  exact absurd hω (not_lt.2 hcalc)

/-! ### `η_t` along the flow -/

/-- `η_u` is decreasing in `u`, so `η_{t_n}⁻¹` bounds `η_u⁻¹` for every `u ≤ t_n` (RBM2D
`inv_etaT_le_inv_etaT`, `CondStable:195`; RBM1D `inv_etaT_le_inv_etaT`).  This is the only way the
endpoint `t_n` enters the envelopes, and it enters polynomially (through `Kenv`), never as a
multiplicative constant in a `≺`. -/
theorem inv_etaT_le_inv_etaT {E : ℝ} (hE : |E| < 2) {u v : ℝ} (huv : u ≤ v) (hv : v < 1) :
    (etaT E u)⁻¹ ≤ (etaT E v)⁻¹ :=
  inv_anti₀ (etaT_pos hE hv) (etaT_le_of_le hE huv)

/-! ### `≺` under `E_k`, at a fixed time -/

/-- **`≺` under `E_k`, per time** (RBM2D `perTimeDomAt_condRow_of_envelope`, `CondStable:216`;
RBM1D `unifDomIcc_condRow_of_envelope`), with no cardinality hypothesis on
the index family `V`.

The exceptional set of `hdom` at `(τ/3, D₁)` with `D₁ = Kenv + B + D + 2` is `S`; the row-slice
Markov inequality makes `{ω : P(slice_ω) ≥ size^{-(Kenv+B)}}` have probability at most
`size^{-(D+2)}`.  Off this set and off the exceptional sets (at `(τ/3, D+2)`) of `hstab` and
`hlow`, `norm_condRow_le_split` gives
`‖E_k[X]‖ ≤ size^{τ/3} E_k[ζ] + Env · P(slice) ≤ size^{2τ/3} χ + size^{-B}`, and
`size^{-B} ≤ size^{τ/3} χ ≤ size^{2τ/3} χ`, so `‖E_k[X]‖ ≤ 2 size^{2τ/3} χ ≤ size^τ χ` when
`2 ≤ size^{τ/3}` (eventually, by `hsize`).  The three exceptional probabilities are at most
`size^{-(D+2)}` each, and `3 size^{-(D+2)} ≤ size^{-D}` eventually.  The statement does not
depend on `d` beyond `size = (W L)^d`.

The deterministic envelope `Env n` may grow polynomially: `Kenv` is free and is absorbed into
the exponent `D₁`. -/
theorem perTimeDomAt_condRow_of_envelope {sz : Sizes d} (hsize : Tendsto sz.size atTop atTop)
    {V : ℕ → Type*} {X : ∀ n, V n → Sizes.SeqΩ sz → ℂ}
    {ζ χ : ∀ n, V n → Sizes.SeqΩ sz → ℝ} {k : ∀ n, V n → Idx d (sz.L n) (sz.W n)}
    {Env : ℕ → ℝ} {Kenv B : ℝ}
    (hXmeas : ∀ (n : ℕ) (a : V n), Measurable (X n a))
    (hζmeas : ∀ (n : ℕ) (a : V n), Measurable (ζ n a))
    (hζ0 : ∀ (n : ℕ) (a : V n) (ω : Sizes.SeqΩ sz), 0 ≤ ζ n a ω)
    (hχ0 : ∀ (n : ℕ) (a : V n) (ω : Sizes.SeqΩ sz), 0 ≤ χ n a ω)
    (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (henv : ∀ (n : ℕ) (a : V n) (ω : Sizes.SeqΩ sz), ‖X n a ω‖ ≤ Env n)
    (hEnvpoly : ∀ᶠ n : ℕ in atTop, Env n ≤ (sz.size n : ℝ) ^ Kenv)
    (hrowint : ∀ (n : ℕ) (a : V n) (ω : Sizes.SeqΩ sz),
      Integrable (fun ω' => ζ n a (rowSplit sz n (k n a) ω ω')) (Sizes.seqP sz))
    (hlow : PerTimeDomAt (Sizes.seqP sz) sz.size
      (fun n (_ : V n) (_ : Sizes.SeqΩ sz) => (sz.size n : ℝ) ^ (-B)) χ)
    (hstab : PerTimeDomAt (Sizes.seqP sz) sz.size
      (fun n a ω => condRowReal sz n (k n a) (ζ n a) ω) χ)
    (hdom : PerTimeDomAt (Sizes.seqP sz) sz.size (fun n a ω => ‖X n a ω‖) ζ) :
    PerTimeDomAt (Sizes.seqP sz) sz.size
      (fun n a ω => ‖condRow sz n (k n a) (X n a) ω‖) χ := by
  intro τ hτ D hD
  have hτ3 : 0 < τ / 3 := by linarith
  set M : ℝ := Kenv + B with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; linarith
  set D₁ : ℝ := M + D + 2 with hD₁def
  have hD₁0 : 0 < D₁ := by rw [hD₁def]; linarith
  filter_upwards [hEnvpoly, hdom (τ / 3) hτ3 D₁ hD₁0, hstab (τ / 3) hτ3 (D + 2) (by linarith),
    hlow (τ / 3) hτ3 (D + 2) (by linarith), hsize.eventually (eventually_ge_atTop 1),
    hsize.eventually (eventually_le_rpow 2 hτ3),
    hsize.eventually (eventually_two_mul_rpow_le (D + 1)),
    hsize.eventually (eventually_two_mul_rpow_le D)] with
    n hEnvN hbadN hstabN hlowN hN1 h2N hdbl1 hdbl2 a
  have hNpos : (0 : ℝ) < sz.size n := by exact_mod_cast hN1
  have hNge1 : (1 : ℝ) ≤ (sz.size n : ℝ) := by exact_mod_cast hN1
  set S : Set (Sizes.SeqΩ sz) := {σ | (sz.size n : ℝ) ^ (τ / 3) * ζ n a σ < ‖X n a σ‖} with hSdef
  have hSmeas : MeasurableSet S :=
    measurableSet_lt (measurable_const.mul (hζmeas n a)) ((hXmeas n a).norm)
  have hSsmall : (Sizes.seqP sz) S ≤ ENNReal.ofReal ((sz.size n : ℝ) ^ (-D₁)) := hbadN a
  set ε : ℝ≥0∞ := ENNReal.ofReal ((sz.size n : ℝ) ^ (-M)) with hεdef
  have hεpos : (0 : ℝ) < (sz.size n : ℝ) ^ (-M) := Real.rpow_pos_of_pos hNpos _
  have hε0 : ε ≠ 0 := by
    rw [hεdef, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hεpos
  set A1 : Set (Sizes.SeqΩ sz) := {ω | ε ≤ (Sizes.seqP sz) (rowSlice sz n (k n a) S ω)} with hA1def
  set A2 : Set (Sizes.SeqΩ sz) :=
    {ω | (sz.size n : ℝ) ^ (τ / 3) * χ n a ω < condRowReal sz n (k n a) (ζ n a) ω} with hA2def
  set A3 : Set (Sizes.SeqΩ sz) :=
    {ω | (sz.size n : ℝ) ^ (τ / 3) * χ n a ω < (sz.size n : ℝ) ^ (-B)} with hA3def
  have hA1small : (Sizes.seqP sz) A1 ≤ ENNReal.ofReal ((sz.size n : ℝ) ^ (-(D + 2))) := by
    have h2 : ε * (Sizes.seqP sz) A1 ≤ ENNReal.ofReal ((sz.size n : ℝ) ^ (-D₁)) :=
      (meas_measure_rowSlice_ge sz n (k n a) hSmeas ε).trans hSsmall
    rw [mul_comm, ← ENNReal.le_div_iff_mul_le (Or.inl hε0) (Or.inl ENNReal.ofReal_ne_top)] at h2
    refine h2.trans (le_of_eq ?_)
    have hexp : -D₁ - -M = -(D + 2) := by rw [hD₁def, hMdef]; ring
    rw [hεdef, ← ENNReal.ofReal_div_of_pos hεpos, ← Real.rpow_sub hNpos, hexp]
  have hsub : {ω | (sz.size n : ℝ) ^ τ * χ n a ω < ‖condRow sz n (k n a) (X n a) ω‖}
      ⊆ A1 ∪ A2 ∪ A3 := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
    rw [hA1def] at h1
    simp only [Set.mem_ofPred_eq, not_le] at h1
    rw [hA2def] at h2
    simp only [Set.mem_ofPred_eq, not_lt] at h2
    rw [hA3def] at h3
    simp only [Set.mem_ofPred_eq, not_lt] at h3
    have hgood : ∀ σ : Sizes.SeqΩ sz, σ ∉ S → ‖X n a σ‖ ≤ (sz.size n : ℝ) ^ (τ / 3) * ζ n a σ := by
      intro σ hσ
      rw [hSdef] at hσ
      simpa only [Set.mem_ofPred_eq, not_lt] using hσ
    have hsplit := norm_condRow_le_split (hXmeas n a) (hζ0 n a) (hrowint n a)
      (henv n a) (Real.rpow_nonneg hNpos.le _) hSmeas hgood ω
    have hr1 : (Sizes.seqP sz).real (rowSlice sz n (k n a) S ω) ≤ (sz.size n : ℝ) ^ (-M) :=
      ENNReal.toReal_le_of_le_ofReal hεpos.le h1.le
    have hr0 : (0 : ℝ) ≤ (Sizes.seqP sz).real (rowSlice sz n (k n a) S ω) := measureReal_nonneg
    have hEnvterm : Env n * (Sizes.seqP sz).real (rowSlice sz n (k n a) S ω)
        ≤ (sz.size n : ℝ) ^ (-B) := by
      have hstep : Env n * (Sizes.seqP sz).real (rowSlice sz n (k n a) S ω)
          ≤ (sz.size n : ℝ) ^ Kenv * (sz.size n : ℝ) ^ (-M) :=
        mul_le_mul hEnvN hr1 hr0 (Real.rpow_nonneg hNpos.le _)
      refine hstep.trans (le_of_eq ?_)
      rw [← Real.rpow_add hNpos, hMdef]
      congr 1
      ring
    have hχu := hχ0 n a ω
    have hr3 : (0 : ℝ) ≤ (sz.size n : ℝ) ^ (τ / 3) := Real.rpow_nonneg hNpos.le _
    have hmono : (sz.size n : ℝ) ^ (τ / 3) ≤ (sz.size n : ℝ) ^ (2 * τ / 3) :=
      Real.rpow_le_rpow_of_exponent_le hNge1 (by linarith)
    have hprod : (sz.size n : ℝ) ^ (τ / 3) * (sz.size n : ℝ) ^ (τ / 3)
        = (sz.size n : ℝ) ^ (2 * τ / 3) := by
      rw [← Real.rpow_add hNpos]; congr 1; ring
    have hfin : (sz.size n : ℝ) ^ (τ / 3) * (sz.size n : ℝ) ^ (2 * τ / 3)
        = (sz.size n : ℝ) ^ τ := by
      rw [← Real.rpow_add hNpos]; congr 1; ring
    have hchain : ‖condRow sz n (k n a) (X n a) ω‖ ≤ (sz.size n : ℝ) ^ τ * χ n a ω := by
      have e1 : (sz.size n : ℝ) ^ (τ / 3) * condRowReal sz n (k n a) (ζ n a) ω
          ≤ (sz.size n : ℝ) ^ (τ / 3) * ((sz.size n : ℝ) ^ (τ / 3) * χ n a ω) :=
        mul_le_mul_of_nonneg_left h2 hr3
      have e3 : (sz.size n : ℝ) ^ (τ / 3) * χ n a ω
          ≤ (sz.size n : ℝ) ^ (2 * τ / 3) * χ n a ω :=
        mul_le_mul_of_nonneg_right hmono hχu
      have e4 : (sz.size n : ℝ) ^ (τ / 3) * ((sz.size n : ℝ) ^ (τ / 3) * χ n a ω)
          = (sz.size n : ℝ) ^ (2 * τ / 3) * χ n a ω := by rw [← mul_assoc, hprod]
      have e5 : (2 : ℝ) * ((sz.size n : ℝ) ^ (2 * τ / 3) * χ n a ω)
          ≤ (sz.size n : ℝ) ^ τ * χ n a ω := by
        have hnn : (0 : ℝ) ≤ (sz.size n : ℝ) ^ (2 * τ / 3) * χ n a ω :=
          mul_nonneg (Real.rpow_nonneg hNpos.le _) hχu
        calc (2 : ℝ) * ((sz.size n : ℝ) ^ (2 * τ / 3) * χ n a ω)
            ≤ (sz.size n : ℝ) ^ (τ / 3) * ((sz.size n : ℝ) ^ (2 * τ / 3) * χ n a ω) :=
              mul_le_mul_of_nonneg_right h2N hnn
          _ = ((sz.size n : ℝ) ^ (τ / 3) * (sz.size n : ℝ) ^ (2 * τ / 3)) * χ n a ω :=
              (mul_assoc _ _ _).symm
          _ = (sz.size n : ℝ) ^ τ * χ n a ω := by rw [hfin]
      linarith
    exact absurd hchain (not_le.2 hω)
  have hnn : (0 : ℝ) ≤ (sz.size n : ℝ) ^ (-(D + 2)) := Real.rpow_nonneg hNpos.le _
  refine (measure_mono hsub).trans ?_
  calc (Sizes.seqP sz) (A1 ∪ A2 ∪ A3)
      ≤ (Sizes.seqP sz) (A1 ∪ A2) + (Sizes.seqP sz) A3 := measure_union_le _ _
    _ ≤ ((Sizes.seqP sz) A1 + (Sizes.seqP sz) A2) + (Sizes.seqP sz) A3 := by
        gcongr; exact measure_union_le _ _
    _ ≤ (ENNReal.ofReal ((sz.size n : ℝ) ^ (-(D + 2)))
          + ENNReal.ofReal ((sz.size n : ℝ) ^ (-(D + 2))))
        + ENNReal.ofReal ((sz.size n : ℝ) ^ (-(D + 2))) :=
          add_le_add (add_le_add hA1small (hstabN a)) (hlowN a)
    _ = ENNReal.ofReal (3 * (sz.size n : ℝ) ^ (-(D + 2))) := by
        rw [show (3 : ℝ) * (sz.size n : ℝ) ^ (-(D + 2))
            = (sz.size n : ℝ) ^ (-(D + 2)) + (sz.size n : ℝ) ^ (-(D + 2))
              + (sz.size n : ℝ) ^ (-(D + 2)) by ring,
          ENNReal.ofReal_add (by positivity) hnn, ENNReal.ofReal_add hnn hnn]
    _ ≤ ENNReal.ofReal ((sz.size n : ℝ) ^ (-D)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e1 : 2 * (sz.size n : ℝ) ^ (-(D + 1 + 1)) ≤ (sz.size n : ℝ) ^ (-(D + 1)) := hdbl1
        have e2 : 2 * (sz.size n : ℝ) ^ (-(D + 1)) ≤ (sz.size n : ℝ) ^ (-D) := hdbl2
        have e3 : (sz.size n : ℝ) ^ (-(D + 1 + 1)) = (sz.size n : ℝ) ^ (-(D + 2)) := by
          congr 1; ring
        rw [e3] at e1
        linarith

/-! ### `E_k[X] - X` through a row-free surrogate, at a fixed time -/

/-- The `PerTimeDomAt` form of RBM1D `unifDomIcc_condRow_sub_self`; RBM2D
`perTimeDomAt_condRow_sub_self`, `CondStable:350`.  The merged calculus replaces the `UnifDomIcc`
algebra: `perTimeCalc_add` then `perTimeCalc_mono` (with `χ + χ ≤ 2 χ`) for `add'`, and
`PerTime.stochDom_of_le_left_eventually` for `of_le_left_icc`; transitivity is the private
`CondStable_trans`. -/
theorem perTimeDomAt_condRow_sub_self {sz : Sizes d} (hsize : Tendsto sz.size atTop atTop)
    {V : ℕ → Type*} {X X' : ∀ n, V n → Sizes.SeqΩ sz → ℂ}
    {ζ χ : ∀ n, V n → Sizes.SeqΩ sz → ℝ} {k : ∀ n, V n → Idx d (sz.L n) (sz.W n)}
    {Env : ℕ → ℝ} {Kenv B : ℝ}
    (hXmeas : ∀ (n : ℕ) (a : V n), Measurable (X n a))
    (hX'meas : ∀ (n : ℕ) (a : V n), Measurable (X' n a))
    (hζmeas : ∀ (n : ℕ) (a : V n), Measurable (ζ n a))
    (hζ0 : ∀ (n : ℕ) (a : V n) (ω : Sizes.SeqΩ sz), 0 ≤ ζ n a ω)
    (hχ0 : ∀ (n : ℕ) (a : V n) (ω : Sizes.SeqΩ sz), 0 ≤ χ n a ω)
    (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (henv : ∀ (n : ℕ) (a : V n) (ω : Sizes.SeqΩ sz), ‖X n a ω - X' n a ω‖ ≤ Env n)
    (hEnvpoly : ∀ᶠ n : ℕ in atTop, Env n ≤ (sz.size n : ℝ) ^ Kenv)
    (hrowint : ∀ (n : ℕ) (a : V n) (ω : Sizes.SeqΩ sz),
      Integrable (fun ω' => ζ n a (rowSplit sz n (k n a) ω ω')) (Sizes.seqP sz))
    (hlow : PerTimeDomAt (Sizes.seqP sz) sz.size
      (fun n (_ : V n) (_ : Sizes.SeqΩ sz) => (sz.size n : ℝ) ^ (-B)) χ)
    (hstab : PerTimeDomAt (Sizes.seqP sz) sz.size
      (fun n a ω => condRowReal sz n (k n a) (ζ n a) ω) χ)
    (hζχ : PerTimeDomAt (Sizes.seqP sz) sz.size ζ χ)
    (hfd : ∀ (n : ℕ) (a : V n), FinDepOffRow sz n (k n a) (X' n a))
    (hXint : ∀ (n : ℕ) (a : V n), RowIntegrable sz n (k n a) (X n a))
    (hdiff : PerTimeDomAt (Sizes.seqP sz) sz.size (fun n a ω => ‖X n a ω - X' n a ω‖) ζ) :
    PerTimeDomAt (Sizes.seqP sz) sz.size
      (fun n a ω => ‖condRow sz n (k n a) (X n a) ω - X n a ω‖) χ := by
  have hX'int : ∀ (n : ℕ) (a : V n), RowIntegrable sz n (k n a) (X' n a) := by
    intro n a ω
    have h : (fun ω' => X' n a (rowSplit sz n (k n a) ω ω')) = fun _ => X' n a ω := by
      funext ω'; exact (hfd n a).rowSplit_eq ω ω'
    rw [h]; exact integrable_const _
  have hbound : ∀ (n : ℕ) (a : V n) (ω : Sizes.SeqΩ sz),
      ‖condRow sz n (k n a) (X n a) ω - X n a ω‖
        ≤ ‖condRow sz n (k n a) (fun η => X n a η - X' n a η) ω‖
          + ‖X n a ω - X' n a ω‖ := by
    intro n a ω
    have e1 := congrFun (condRow_sub (k n a) (hXint n a) (hX'int n a)) ω
    have e2 := congrFun (condRow_of_finDepOffRow (hfd n a)) ω
    have hid : condRow sz n (k n a) (X n a) ω - X n a ω
        = condRow sz n (k n a) (fun η => X n a η - X' n a η) ω
          - (X n a ω - X' n a ω) := by
      rw [e1, e2]; ring
    rw [hid]
    exact norm_sub_le _ _
  have htool : PerTimeDomAt (Sizes.seqP sz) sz.size
      (fun n a ω => ‖condRow sz n (k n a) (fun η => X n a η - X' n a η) ω‖) χ :=
    perTimeDomAt_condRow_of_envelope hsize
      (fun n a => (hXmeas n a).sub (hX'meas n a)) hζmeas hζ0 hχ0 hKenv hB henv hEnvpoly
      hrowint hlow hstab hdiff
  have hsum := perTimeCalc_add hsize htool (CondStable_trans hsize hdiff hζχ)
  have hsum2 := perTimeCalc_mono hsize hχ0 2
    (Eventually.of_forall fun n a ω => by linarith) hsum
  exact stochDom_of_le_left_eventually (Eventually.of_forall fun n a ω => hbound n a ω) hsum2

/-! ### The minor replacement (4.9) on the good event -/

/-- **(4.9) pointwise, on the good event** (RBM2D `norm_greenDiagCentered_sub_minor_le`,
`CondStable:410`; RBM1D `norm_greenDiagCentered_sub_minor_le`).  The replacement error is
`|G_{kk} - G^{(i)}_{kk}| = |G_{ki} G_{ik} / G_{ii}| ≤ 2 |G_{ki}| |G_{ik}|`, since `|G_{ii}| ≥ 1/2`
on the good event (`δ' ≤ 1/2`).  The identification of `greenMinorMat` with the explicit formula
needs no event: `H_u` is Hermitian and `Im z_u ≠ 0`.  The statement does not depend on `d`.  The
pair of distinct indices `(i, k)` is `v : OffPair` of RBM1D (there `v.1.1 = i`, `v.1.2 = k`). -/
theorem norm_greenDiagCentered_sub_minor_le (sz : Sizes d) (n : ℕ) {E u : ℝ} (hE : |E| < 2)
    (hu1 : u < 1) {δ' : ℝ} (hδ' : δ' ≤ 1 / 2) {ω : Sizes.SeqΩ sz}
    (hω : GoodEvent (green (Sizes.seqHflow sz n u ω) (zt E u)) (mE E) δ')
    (i k : Idx d (sz.L n) (sz.W n)) (hik : i ≠ k) :
    ‖greenDiagCentered sz n u (zt E u) (mE E) k ω
        - greenMinorDiagCentered sz n u (zt E u) (mE E) i ⟨k, Ne.symm hik⟩ ω‖
      ≤ 2 * (‖green (Sizes.seqHflow sz n u ω) (zt E u) k i‖
          * ‖green (Sizes.seqHflow sz n u ω) (zt E u) i k‖) := by
  have hzt : (zt E u).im ≠ 0 := by
    rw [← etaT_eq_zt_im]
    exact (etaT_pos hE hu1).ne'
  have hid : greenDiagCentered sz n u (zt E u) (mE E) k ω
      - greenMinorDiagCentered sz n u (zt E u) (mE E) i ⟨k, Ne.symm hik⟩ ω
      = -(greenMinor (green (Sizes.seqHflow sz n u ω) (zt E u)) i k k
          - green (Sizes.seqHflow sz n u ω) (zt E u) k k) := by
    simp only [greenDiagCentered, greenMinorDiagCentered]
    rw [greenMinorMat_eq_minorGreen sz n u (zt E u) i ω
      (isUnit_det_Hflow_sub sz n u ω hzt) (green_Hflow_diag_ne_zero sz n u ω hzt i),
      minorGreen_eq_greenMinor]
    ring
  rw [hid, norm_neg]
  exact hω.norm_greenMinor_sub_le (norm_mE hE.le) hδ' i k k

/-! ### (`GijGEX`) and (`GiiGEX`) for the Gaussian flow, with no large deviation hypotheses

`entry_bound_stochDom`, `diag_bound_stochDom` and their `_of_asGMc` forms (`Green/EntryDom.lean`)
carry the four large deviation estimates `hLrow`, `hLcol`, `hLquad`, `hLdiag` as hypotheses.  For
the Gaussian flow they are theorems:

| hypothesis | proved in |
| --- | --- |
| `hLrow`  | `stochDom_ldeRow` (`Green/LDE.lean`) |
| `hLcol`  | `stochDom_ldeCol` (`Green/LDE.lean`) |
| `hLdiag` | `stochDom_normSq_Hflow_diag` (`Green/LDE.lean`) |
| `hLquad` | `stochDom_ldeQuad` (`Green/IBPPoly.lean`) |

This is the assembly (RBM2D `Green/EntryGauss.lean`, RBM1D `Gauss/EntryBoundGauss.lean` at
`86573b9`: `entry_bound_gauss`, `diag_bound_gauss`) in the per-sequence form of the pin
`GbEXPHypV3` (`Green/Pins.lean`): fixed `κ, 𝔠, 𝔡, δ`, then `sz.Admissible 𝔠 𝔡`, the energy and
time sequences `E, t` in the bulk with the range condition, and `c > 0`.  The range condition
`RangeCond` and `0 < δ` are premises of `GbEXPHypV3` that no merged input uses; they are kept,
named with a leading underscore, so that the theorems apply to the premises of `GbEXPHypV3` in
their order. -/

section EntryGauss

/-- **(`GijGEX`) for the Gaussian flow, `GijOmegaSeq`, for every `c > 0`,** with no large
deviation hypothesis: `entry_bound_stochDom` fed by `stochDom_ldeRow` and `stochDom_ldeCol`
(RBM2D `gijOmegaSeq`, `EntryGauss:55`).  The premises are those of `GbEXPHypV3`, in its order;
`_hδ` and `_hR` (the range condition) are not used. -/
theorem gijOmegaSeq (sz : Sizes d) {κ 𝔠 𝔡 δ : ℝ} (hκ : 0 < κ) (_hδ : 0 < δ)
    (hA : sz.Admissible 𝔠 𝔡) (E t : ℕ → ℝ) (hE : ∀ n, |E n| < 2 - κ)
    (h0 : ∀ n, 0 ≤ t n) (h1 : ∀ n, t n < 1) (_hR : sz.RangeCond δ t) (c : ℝ) (hc : 0 < c) :
    GijOmegaSeq sz E t c :=
  entry_bound_stochDom sz hκ hA (fun n => (hE n).le) h1 hc
    (stochDom_ldeRow sz hκ hA.2.2.1 (fun n => (hE n).le) h0 h1)
    (stochDom_ldeCol sz hκ hA.2.2.1 (fun n => (hE n).le) h0 h1)

/-- **(`GiiGEX`) for the Gaussian flow, `GiiOmegaSeq`, for every `c > 0`,** with no large
deviation hypothesis: `diag_bound_stochDom` fed by `stochDom_ldeRow`, `stochDom_ldeCol`,
`stochDom_ldeQuad` and `stochDom_normSq_Hflow_diag` (RBM2D `giiOmegaSeq`, `EntryGauss:67`).
Same premises as `gijOmegaSeq`, with `hd : 3 ≤ d` (as the merged `diag_bound_stochDom`). -/
theorem giiOmegaSeq (sz : Sizes d) (hd : 3 ≤ d) {κ 𝔠 𝔡 δ : ℝ} (hκ : 0 < κ) (_hδ : 0 < δ)
    (hA : sz.Admissible 𝔠 𝔡) (E t : ℕ → ℝ) (hE : ∀ n, |E n| < 2 - κ)
    (h0 : ∀ n, 0 ≤ t n) (h1 : ∀ n, t n < 1) (_hR : sz.RangeCond δ t) (c : ℝ) (hc : 0 < c) :
    GiiOmegaSeq sz E t c :=
  diag_bound_stochDom sz hd hκ hA (fun n => (hE n).le) h0 h1 hc
    (stochDom_ldeRow sz hκ hA.2.2.1 (fun n => (hE n).le) h0 h1)
    (stochDom_ldeCol sz hκ hA.2.2.1 (fun n => (hE n).le) h0 h1)
    (stochDom_ldeQuad sz hκ hA.2.2.1 (fun n => (hE n).le) h0 h1)
    (stochDom_normSq_Hflow_diag sz hA.2.2.1 h0 h1)

/-- **(`GijGEX`) without the indicator, for the Gaussian flow, under (`asGMc`) at `c`:**
`GijSeq`.  `entry_bound_stochDom_of_asGMc` fed by `stochDom_ldeRow` and `stochDom_ldeCol`.  A
conditional adapter (the hypothesis `AsGMcSeq sz E t c` is the paper's (`asGMc`), `3_5:30`), not
the statement without it.  Premises as in `gijOmegaSeq`, then `AsGMcSeq sz E t c` (RBM2D
`gijSeq_of_asGMc`, `EntryGauss:81`). -/
theorem gijSeq_of_asGMc (sz : Sizes d) {κ 𝔠 𝔡 δ : ℝ} (hκ : 0 < κ) (_hδ : 0 < δ)
    (hA : sz.Admissible 𝔠 𝔡) (E t : ℕ → ℝ) (hE : ∀ n, |E n| < 2 - κ)
    (h0 : ∀ n, 0 ≤ t n) (h1 : ∀ n, t n < 1) (_hR : sz.RangeCond δ t) (c : ℝ) (hc : 0 < c)
    (hAs : AsGMcSeq sz E t c) :
    GijSeq sz E t :=
  entry_bound_stochDom_of_asGMc sz hκ hA (fun n => (hE n).le) h1 hc hAs
    (stochDom_ldeRow sz hκ hA.2.2.1 (fun n => (hE n).le) h0 h1)
    (stochDom_ldeCol sz hκ hA.2.2.1 (fun n => (hE n).le) h0 h1)

/-- **(`GiiGEX`) without the indicator, for the Gaussian flow, under (`asGMc`) at `c`:**
`GiiSeq`.  `diag_bound_stochDom_of_asGMc` fed by the four large deviation theorems.  A conditional
adapter, as `gijSeq_of_asGMc`, with `hd : 3 ≤ d` (RBM2D `giiSeq_of_asGMc`, `EntryGauss:93`). -/
theorem giiSeq_of_asGMc (sz : Sizes d) (hd : 3 ≤ d) {κ 𝔠 𝔡 δ : ℝ} (hκ : 0 < κ) (_hδ : 0 < δ)
    (hA : sz.Admissible 𝔠 𝔡) (E t : ℕ → ℝ) (hE : ∀ n, |E n| < 2 - κ)
    (h0 : ∀ n, 0 ≤ t n) (h1 : ∀ n, t n < 1) (_hR : sz.RangeCond δ t) (c : ℝ) (hc : 0 < c)
    (hAs : AsGMcSeq sz E t c) :
    GiiSeq sz E t :=
  diag_bound_stochDom_of_asGMc sz hd hκ hA (fun n => (hE n).le) h0 h1 hc hAs
    (stochDom_ldeRow sz hκ hA.2.2.1 (fun n => (hE n).le) h0 h1)
    (stochDom_ldeCol sz hκ hA.2.2.1 (fun n => (hE n).le) h0 h1)
    (stochDom_ldeQuad sz hκ hA.2.2.1 (fun n => (hE n).le) h0 h1)
    (stochDom_normSq_Hflow_diag sz hA.2.2.1 h0 h1)

end EntryGauss

/-! ### Checks: a compiled nonempty instance of every target

The data (`d = 3`) is the preflight sequence `sz0` of `Defs/Sizes.lean` (`L_n = 4(n+1)`,
`W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`; `n = 0`: `L = 4`, `W = 32`, `lam = 1/64`,
`N = 2097152` sites of `Z_128^3`; `size_n → ∞`), the slice `n = 0`, `E = 0` (`m = i`), `t = 1/2`
(`η_t = (1 - t) Im m = 1/2`), the site `i = (0,0,0)`.  Only the negative statement
`condDom_no_hsize` needs another size sequence (constant sizes `L = 3`, `W = 2`).  The `≺`
statements are applied at non-constant bounded random variables of `Sizes.seqP sz0`. -/

section Checks

noncomputable section

set_option maxRecDepth 100000

open RBM.Gauss.SizesInst RBM.Gauss.StochDomAtInst RBM.Gauss.DominationAtInst

private abbrev condDomCkI : Type := Idx 3 (sz0.L 0) (sz0.W 0)

/-- The site `(0,0,0)` of slice `0`. -/
private def condDomCk0 : condDomCkI := fun _ => 0

/-- The row-`0` coordinate `⟨0, x, x, true⟩` (the real part of `H_{xx}` at slice `0`), `x = 0`. -/
private def condDomCkC : Sizes.SeqCoord sz0 := ⟨0, condDomCk0, condDomCk0, true⟩

/-- The nontrivial measurable set `S = {ω : ω_{c₀} < 0}`. -/
private def condDomCkSet : Set (Sizes.SeqΩ sz0) := {ω | ω condDomCkC < 0}

private theorem condDomCkSet_meas : MeasurableSet condDomCkSet :=
  measurableSet_lt (measurable_pi_apply condDomCkC) measurable_const

/-- `E_0` of a real constant. -/
example : condRowReal sz0 0 condDomCk0 (fun _ => (1 : ℝ)) = fun _ => 1 :=
  condRowReal_const _ _

/-- The row section of `S` at any frozen `ω`, its measure, the Fubini identity and Markov, at
`k = 0`, `ε = 1/2`. -/
example (ω : Sizes.SeqΩ sz0) :
    MeasurableSet (rowSlice sz0 0 condDomCk0 condDomCkSet ω) :=
  measurableSet_rowSlice condDomCkSet_meas ω

example : Measurable fun ω => (Sizes.seqP sz0)
    (rowSlice sz0 0 condDomCk0 condDomCkSet ω) :=
  measurable_measure_rowSlice sz0 0 condDomCk0 condDomCkSet_meas

example : ∫⁻ ω, (Sizes.seqP sz0) (rowSlice sz0 0 condDomCk0 condDomCkSet ω)
    ∂(Sizes.seqP sz0) = (Sizes.seqP sz0) condDomCkSet :=
  lintegral_measure_rowSlice sz0 0 condDomCk0 condDomCkSet_meas

example : (1 / 2 : ℝ≥0∞) * (Sizes.seqP sz0)
      {ω | (1 / 2 : ℝ≥0∞) ≤ (Sizes.seqP sz0)
        (rowSlice sz0 0 condDomCk0 condDomCkSet ω)}
    ≤ (Sizes.seqP sz0) condDomCkSet :=
  meas_measure_rowSlice_ge sz0 0 condDomCk0 condDomCkSet_meas _

/-- `norm_condRow_le_split` for `X = 2` on `S` and `X = 1` off `S` (the good bound `‖X‖ ≤ 1 · 1`
holds exactly off `S`; the envelope is `2`), at `k = 0` and every frozen `ω`. -/
example (ω : Sizes.SeqΩ sz0) :
    ‖condRow sz0 0 condDomCk0
        (fun σ => if σ condDomCkC < 0 then (2 : ℂ) else 1) ω‖
      ≤ 1 * condRowReal sz0 0 condDomCk0 (fun _ => (1 : ℝ)) ω
        + 2 * (Sizes.seqP sz0).real (rowSlice sz0 0 condDomCk0 condDomCkSet ω) :=
  norm_condRow_le_split (f := fun _ => (1 : ℝ))
    (Measurable.ite condDomCkSet_meas measurable_const measurable_const)
    (fun _ => zero_le_one) (fun _ => integrable_const _)
    (fun σ => by
      by_cases h : σ condDomCkC < 0
      · simp [h]
      · simp [h])
    zero_le_one condDomCkSet_meas
    (fun σ hσ => by
      have hσ' : ¬ σ condDomCkC < 0 := hσ
      simp [hσ']) ω

/-- `|G_{ii} - m| ≤ η_t⁻¹ + 1` at `u = 1/4 ≠ t = 1/2`, `E = 0`, every `ω`. -/
example (ω : Sizes.SeqΩ sz0) :
    ‖green (Sizes.seqHflow sz0 0 (1 / 4) ω) (zt 0 (1 / 2)) condDomCk0 condDomCk0
        - mE 0‖ ≤ (etaT 0 (1 / 2))⁻¹ + 1 :=
  norm_green_diag_sub_mE_le (by norm_num) (by norm_num) (1 / 4) condDomCk0 ω

/-- `η_{1/2} = 1/2` at `E = 0` (`Im m = 1`). -/
private theorem condDom_etaT_half : etaT 0 (1 / 2) = 1 / 2 := by
  have h4 : Real.sqrt (4 - (0 : ℝ) ^ 2) = 2 := by
    rw [show (4 : ℝ) - 0 ^ 2 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  change (1 - 1 / 2) * (mE 0).im = 1 / 2
  rw [mE_im, h4]
  norm_num

/-- The deterministic envelope of `ibpRem` at `E = 0`, `t = 1/2`: `(η_t⁻¹ + 1)² = 9`, at every
slice, every pair `(i, k)` (including `k = i`) and every `ω`.  (`‖G_{ii}‖ ≤ η⁻¹ = 2`,
`‖G_{kk} - m‖ ≤ 3`, `‖m‖ = 1`.) -/
private theorem condDom_norm_ibpRem_le {d : ℕ} (sz : Sizes d) (n : ℕ) (ω : Sizes.SeqΩ sz)
    (i k : Idx d (sz.L n) (sz.W n)) : ‖ibpRem sz n 0 (1 / 2) (i, k) ω‖ ≤ 9 := by
  have hE : |(0 : ℝ)| < 2 := by norm_num
  have ht : (1 / 2 : ℝ) < 1 := by norm_num
  have hz : ((zt 0 (1 / 2)).im)⁻¹ = 2 := by
    rw [← etaT_eq_zt_im, condDom_etaT_half]
    norm_num
  have hG : ∀ (η : Sizes.SeqΩ sz) (a : Idx d (sz.L n) (sz.W n)),
      ‖green (Sizes.seqHflow sz n (1 / 2) η) (zt 0 (1 / 2)) a a‖ ≤ 2 := by
    intro η a
    have h := norm_green_apply_le_etaT (sz := sz) (n := n) hE ht (1 / 2) a a η
    rwa [hz] at h
  have hGm : ∀ (η : Sizes.SeqΩ sz) (a : Idx d (sz.L n) (sz.W n)),
      ‖green (Sizes.seqHflow sz n (1 / 2) η) (zt 0 (1 / 2)) a a - mE 0‖ ≤ 3 := by
    intro η a
    have h := norm_greenDiagCentered_le_env (sz := sz) (n := n) hE ht (1 / 2) a η
    rw [hz] at h
    change ‖green (Sizes.seqHflow sz n (1 / 2) η) (zt 0 (1 / 2)) a a - mE 0‖ ≤ 2 + 1 at h
    linarith
  have hrow : ‖condRow sz n i (fun η =>
      green (Sizes.seqHflow sz n (1 / 2) η) (zt 0 (1 / 2)) i i
        * (green (Sizes.seqHflow sz n (1 / 2) η) (zt 0 (1 / 2)) k k - mE 0)) ω‖ ≤ 6 := by
    rw [condRow_apply]
    have hbd := norm_integral_le_of_norm_le_const (μ := Sizes.seqP sz)
      (f := fun ω' => green (Sizes.seqHflow sz n (1 / 2) (rowSplit sz n i ω ω'))
          (zt 0 (1 / 2)) i i
        * (green (Sizes.seqHflow sz n (1 / 2) (rowSplit sz n i ω ω'))
            (zt 0 (1 / 2)) k k - mE 0)) (C := 6)
      (Eventually.of_forall fun ω' => by
        rw [norm_mul]
        have h1 := hG (rowSplit sz n i ω ω') i
        have h2 := hGm (rowSplit sz n i ω ω') k
        nlinarith [norm_nonneg (green (Sizes.seqHflow sz n (1 / 2)
          (rowSplit sz n i ω ω')) (zt 0 (1 / 2)) i i),
          norm_nonneg (green (Sizes.seqHflow sz n (1 / 2) (rowSplit sz n i ω ω'))
            (zt 0 (1 / 2)) k k - mE 0)])
    simpa using hbd
  unfold ibpRem
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mE (by norm_num : |(0 : ℝ)| ≤ 2), one_mul]
  have := hGm ω k
  linarith

/-- **The weighted reduction** at `sz0`, `n = 0` (`d = 3`, `L = 4`, `W = 32`, `lam = 1/64`),
`E = 0`, `t = 1/2`, `i = (0,0,0)`, with `A = A_diag = 9 = (η⁻¹ + 1)²`; the weight is
`svarF (i,i) = W^{-d} (1 + 2 d g²)⁻¹ = 1/32816`, so the bound is `9 + 9/32816`.  Every
hypothesis is discharged, for every `ω`. -/
private theorem condDom_inst_offdiag (ω : Sizes.SeqΩ sz0) :
    ‖condExpDiag sz0 0 (1 / 2) (zt 0 (1 / 2)) (mE 0) condDomCk0 ω
        - ((1 / 2 : ℝ) : ℂ) * mE 0 ^ 2 * ∑ k : condDomCkI,
          (svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) condDomCk0 k : ℂ)
          * (green (Sizes.seqHflow sz0 0 (1 / 2) ω) (zt 0 (1 / 2)) k k - mE 0)‖
      ≤ 9 + 9 / 32816 := by
  have h := norm_condExpDiag_sub_le_offdiag (sz := sz0) (n := 0) (E := 0) (t := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) condDomCk0 ω (A := 9) (Adiag := 9)
    (by norm_num) (fun k _ => condDom_norm_ibpRem_le sz0 0 ω condDomCk0 k)
    (condDom_norm_ibpRem_le sz0 0 ω condDomCk0 condDomCk0)
  have hs : svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) condDomCk0 condDomCk0 = 1 / 32816 := by
    rw [svarF_diag]
    norm_num [sz0]
  rw [hs] at h
  linarith

/-- `η_t ≤ η_u` for `u = 0 ≤ t = 1/2`, and `W ≤ size` at `sz0`: `n = 0` (`32 ≤ 2097152`) and
`n = 1` (`1024 ≤ 549755813888`). -/
example : etaT 0 (1 / 2) ≤ etaT 0 0 := etaT_le_of_le (by norm_num) (by norm_num)

example : (32 : ℕ) ≤ 2097152 := W_le_self sz0 (by norm_num) 0

example : (1024 : ℕ) ≤ 549755813888 := W_le_self sz0 (by norm_num) 1

/-- `Y = 1_{ω_{c₀} < 0}`, a non-constant `{0,1}`-valued random variable on `Sizes.seqP sz0`. -/
private noncomputable def condDomCkY : ∀ _l : ℕ, Unit → Sizes.SeqΩ sz0 → ℝ :=
  fun _ _ ω => if ω condDomCkC < 0 then 1 else 0

private theorem condDomCkY_meas (l : ℕ) (u : Unit) : Measurable (condDomCkY l u) :=
  Measurable.ite (measurableSet_lt (measurable_pi_apply condDomCkC) measurable_const)
    measurable_const measurable_const

private theorem condDomCkY_abs_pow_le (p l : ℕ) (u : Unit) (ω : Sizes.SeqΩ sz0) :
    |condDomCkY l u ω| ^ (2 * p) ≤ 1 := by
  refine pow_le_one₀ (abs_nonneg _) ?_
  unfold condDomCkY
  split_ifs <;> simp

private theorem condDomCkY_int (p l : ℕ) (u : Unit) :
    Integrable (fun ω => |condDomCkY l u ω| ^ (2 * p)) (Sizes.seqP sz0) :=
  Integrable.of_bound
    (((continuous_abs.measurable.comp (condDomCkY_meas l u)).pow_const _).aestronglyMeasurable) 1
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact condDomCkY_abs_pow_le p l u ω)

private theorem condDomCkY_moment :
    MomentDomAt (Sizes.seqP sz0) sz0.size condDomCkY
      (fun _ _ => (1 : ℝ)) := by
  intro ε hε p
  refine ⟨1, one_pos, Eventually.of_forall fun l u => ?_⟩
  have h1 : ∫ ω, |condDomCkY l u ω| ^ (2 * p) ∂(Sizes.seqP sz0) ≤ 1 := by
    have := norm_integral_le_of_norm_le_const (μ := Sizes.seqP sz0)
      (f := fun ω => |condDomCkY l u ω| ^ (2 * p)) (C := 1)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact condDomCkY_abs_pow_le p l u ω)
    exact (le_abs_self _).trans (by simpa using this)
  have hs : (1 : ℝ) ≤ (sz0.size l : ℝ) := by
    exact_mod_cast sz0.one_le_size l
  have hp : (1 : ℝ) ≤ (sz0.size l : ℝ) ^ (ε * p) :=
    Real.one_le_rpow hs (mul_nonneg hε.le (Nat.cast_nonneg _))
  simpa using h1.trans hp

/-- **Markov, per time and per index** at `sz0`: `Y = 1_{ω_{c₀} < 0}` against `Φ ≡ 1`.  `hΦ`,
`hint`, `MomentDomAt` (with `C = 1`) and `hsize` (`tendsto_sz0_size`) are all discharged. -/
private theorem condDom_inst_moment :
    PerTimeDomAt (Sizes.seqP sz0) sz0.size condDomCkY
      (fun _ _ _ => (1 : ℝ)) :=
  perTimeDomAt_of_moment tendsto_sz0_size (fun _ _ => one_pos) condDomCkY_int
    condDomCkY_moment

/-- The constant sizes `L = 3`, `W = 2`, `lam = 1/2` (`size ≡ 216`), for the negative statement. -/
private def condDomCkS : Sizes 3 where
  L := fun _ => 3
  W := fun _ => 2
  lam := fun _ => 1 / 2
  three_le_L := fun _ => le_rfl
  W_pos := fun _ => by norm_num

/-- **`hsize` cannot be dropped from `perTimeDomAt_of_moment`** (a compiled negative statement).
On the constant sizes `L = 3`, `W = 2`, `d = 3` (`size ≡ 216`, so `size` does not tend to
infinity), the constant `Y ≡ 10` with control `Φ ≡ 1` satisfies `MomentDomAt` (with `C = 100^p`),
but the failure event `{216^{1/10} · 1 < 10}` is the whole space, of probability `1 > 216⁻¹`. -/
private theorem condDom_no_hsize :
    MomentDomAt (Sizes.seqP condDomCkS) condDomCkS.size
      (fun _ (_ : Unit) _ => (10 : ℝ)) (fun _ _ => (1 : ℝ)) ∧
    ¬ PerTimeDomAt (Sizes.seqP condDomCkS) condDomCkS.size
      (fun _ (_ : Unit) _ => (10 : ℝ)) (fun _ _ _ => (1 : ℝ)) := by
  have h216 : ∀ l : ℕ, condDomCkS.size l = 216 := fun _ => rfl
  constructor
  · intro ε hε p
    refine ⟨100 ^ p, by positivity, Eventually.of_forall fun l u => ?_⟩
    have hs : (1 : ℝ) ≤ (condDomCkS.size l : ℝ) ^ (ε * p) :=
      Real.one_le_rpow (by rw [h216]; norm_num) (mul_nonneg hε.le (Nat.cast_nonneg _))
    have hint : ∫ _ω, |(10 : ℝ)| ^ (2 * p) ∂(Sizes.seqP condDomCkS) = 100 ^ p := by
      rw [integral_const, probReal_univ, one_smul, abs_of_pos (by norm_num : (0 : ℝ) < 10),
        pow_mul]
      norm_num
    rw [hint]
    simp only [one_pow, mul_one]
    exact le_mul_of_one_le_right (by positivity) hs
  · intro h
    obtain ⟨l, hl⟩ := (h (1 / 10) (by norm_num) 1 (by norm_num)).exists
    have hl' := hl ()
    have hlt : ((condDomCkS.size l : ℕ) : ℝ) ^ ((1 : ℝ) / 10) * 1 < 10 := by
      rw [h216, mul_one]
      have h1 : (216 : ℝ) ^ ((1 : ℝ) / 10) ≤ (216 : ℝ) ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      have h2 : (216 : ℝ) ^ ((1 : ℝ) / 3) = 6 := by
        rw [show (216 : ℝ) = 6 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        norm_num
      push_cast
      linarith
    have huniv : {ω : Sizes.SeqΩ condDomCkS |
        ((condDomCkS.size l : ℕ) : ℝ) ^ ((1 : ℝ) / 10) * 1 < 10} = Set.univ :=
      Set.eq_univ_of_forall fun _ => hlt
    rw [huniv, measure_univ] at hl'
    have h2 : ENNReal.ofReal (((condDomCkS.size l : ℕ) : ℝ) ^ (-(1 : ℝ))) < 1 := by
      rw [ENNReal.ofReal_lt_one, h216, Real.rpow_neg_one]
      norm_num
    exact absurd hl' (not_le.2 h2)

/-! #### CondStable at `sz0`

`P = Sizes.seqP`, the one-element index family `V n = Unit`, the row `k n = 0`, and the bounded
random variable `X ω = 2` if `ω_{c₀} < 0` and `1` otherwise (`c₀` a coordinate of slice `0`), which
is not constant.  Every deterministic hypothesis is discharged; `hsize` is proved. -/

/-- The row `0` at every slice. -/
private def condStableK (n : ℕ) : Idx 3 (sz0.L n) (sz0.W n) := fun _ => 0

/-- `X = 2` on `{ω_{c₀} < 0}` and `1` off it. -/
private noncomputable def condStableX : ∀ _n : ℕ, Unit → Sizes.SeqΩ sz0 → ℂ :=
  fun _ _ ω => if ω condDomCkC < 0 then 2 else 1

private theorem condStableX_meas (n : ℕ) (a : Unit) : Measurable (condStableX n a) :=
  Measurable.ite (measurableSet_lt (measurable_pi_apply condDomCkC) measurable_const)
    measurable_const measurable_const

private theorem condStableX_norm_le (n : ℕ) (a : Unit) (ω : Sizes.SeqΩ sz0) :
    ‖condStableX n a ω‖ ≤ 2 := by
  unfold condStableX
  split_ifs <;> simp

/-- `‖X - 1‖ ≤ 1`. -/
private theorem condStableX_sub_norm_le (n : ℕ) (a : Unit) (ω : Sizes.SeqΩ sz0) :
    ‖condStableX n a ω - 1‖ ≤ 1 := by
  unfold condStableX
  split_ifs <;> norm_num

/-- `size ≥ 3` at the data (`size n = (W_n L_n)³ ≥ 2097152`). -/
private theorem condStable_three_le (n : ℕ) : (3 : ℝ) ≤ (sz0.size n : ℝ) := by
  exact_mod_cast CondStable_three_le_size sz0 (by norm_num) n

/-- `perTimeDomAt_condRow_of_envelope` at `X` above, `ζ ≡ 2`, `χ ≡ 1`, `Env ≡ 2`, `Kenv = 1`,
`B = 1`: `hdom : ‖X‖ ≺ 2` (`‖X‖ ≤ 1 · 2`), `hstab : E_0[2] = 2 ≺ 1` (`2 ≤ 2 · 1`),
`hlow : size⁻¹ ≺ 1`, `Env = 2 ≤ size¹`; the conclusion is `‖E_0[X]‖ ≺ 1`. -/
private theorem condStable_inst_envelope :
    PerTimeDomAt (Sizes.seqP sz0) sz0.size
      (fun n (a : Unit) ω => ‖condRow sz0 n (condStableK n) (condStableX n a) ω‖)
      (fun _ _ _ => (1 : ℝ)) := by
  refine perTimeDomAt_condRow_of_envelope (V := fun _ => Unit) (X := condStableX)
    (ζ := fun _ _ _ => (2 : ℝ)) (χ := fun _ _ _ => (1 : ℝ)) (k := fun n _ => condStableK n)
    (Env := fun _ => 2) (Kenv := 1) (B := 1) tendsto_sz0_size
    condStableX_meas (fun _ _ => measurable_const) (fun _ _ _ => by norm_num)
    (fun _ _ _ => zero_le_one) zero_le_one zero_le_one
    (fun n a ω => condStableX_norm_le n a ω)
    (Eventually.of_forall fun n => by
      have := condStable_three_le n
      rw [Real.rpow_one]; linarith)
    (fun _ _ _ => integrable_const _) ?_ ?_ ?_
  · refine perTimeDomAt_const sz0 (V := fun _ => Unit)
      (f := fun n => (sz0.size n : ℝ) ^ (-(1 : ℝ))) (g := fun _ => (1 : ℝ))
      (fun _ => zero_le_one) (Eventually.of_forall fun n => ?_)
    have := condStable_three_le n
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  · simp only [condRowReal_const]
    exact stochDom_of_le_const_mul tendsto_sz0_size (fun _ _ _ => by norm_num)
      (fun _ _ _ => zero_le_one) 2 (fun _ _ _ => by norm_num)
  · exact stochDom_of_le_const_mul tendsto_sz0_size (fun _ _ _ => norm_nonneg _)
      (fun _ _ _ => by norm_num) 1 (fun n a ω => by
        have := condStableX_norm_le n a ω
        linarith)

/-- `perTimeDomAt_condRow_sub_self` at the same `X`, the row-free surrogate `X' ≡ 1`
(`FinDepOffRow`, `RowIntegrable`), `Env ≡ 1 ≥ ‖X - X'‖`, `ζ ≡ χ ≡ 1`, `Kenv = 0`, `B = 1`. -/
private theorem condStable_inst_subself :
    PerTimeDomAt (Sizes.seqP sz0) sz0.size
      (fun n (a : Unit) ω => ‖condRow sz0 n (condStableK n) (condStableX n a) ω
        - condStableX n a ω‖)
      (fun _ _ _ => (1 : ℝ)) := by
  refine perTimeDomAt_condRow_sub_self (V := fun _ => Unit) (X := condStableX)
    (X' := fun _ _ _ => (1 : ℂ)) (ζ := fun _ _ _ => (1 : ℝ)) (χ := fun _ _ _ => (1 : ℝ))
    (k := fun n _ => condStableK n) (Env := fun _ => 1) (Kenv := 0) (B := 1)
    tendsto_sz0_size condStableX_meas (fun _ _ => measurable_const)
    (fun _ _ => measurable_const) (fun _ _ _ => zero_le_one) (fun _ _ _ => zero_le_one)
    le_rfl zero_le_one (fun n a ω => condStableX_sub_norm_le n a ω)
    (Eventually.of_forall fun n => by
      have := condStable_three_le n
      rw [Real.rpow_zero])
    (fun _ _ _ => integrable_const _) ?_ ?_ ?_
    (fun n a => ⟨∅, by simp, fun _ _ _ => rfl⟩)
    (fun n a => rowIntegrable_of_measurable_of_bound (condStableX_meas n a)
      (fun ω => condStableX_norm_le n a ω))
    ?_
  · refine perTimeDomAt_const sz0 (V := fun _ => Unit)
      (f := fun n => (sz0.size n : ℝ) ^ (-(1 : ℝ))) (g := fun _ => (1 : ℝ))
      (fun _ => zero_le_one) (Eventually.of_forall fun n => ?_)
    have := condStable_three_le n
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  · simp only [condRowReal_const]
    exact perTimeDomAt_const sz0 (V := fun _ => Unit) (f := fun _ => (1 : ℝ))
      (g := fun _ => (1 : ℝ)) (fun _ => zero_le_one) (Eventually.of_forall fun _ => le_rfl)
  · exact perTimeDomAt_const sz0 (V := fun _ => Unit) (f := fun _ => (1 : ℝ))
      (g := fun _ => (1 : ℝ)) (fun _ => zero_le_one) (Eventually.of_forall fun _ => le_rfl)
  · exact stochDom_of_le_const_mul tendsto_sz0_size (fun _ _ _ => norm_nonneg _)
      (fun _ _ _ => zero_le_one) 1 (fun n a ω => by
        have := condStableX_sub_norm_le n a ω
        linarith)

/-- The three combinators, at `Ξ = univ` (`highProbAt_univ`), `ξ = 1`, `ξ' = 1/2`. -/
private theorem condStable_inst_le_left_on :
    PerTimeDomAt (Sizes.seqP sz0) sz0.size
      (fun _ (_ : Unit) _ => (1 / 2 : ℝ)) (fun _ _ _ => (1 : ℝ)) :=
  perTimeDomAt_of_le_left_on (sz := sz0) (by norm_num)
    (ξ := fun _ (_ : Unit) _ => (1 : ℝ)) (Ξ := fun _ => Set.univ)
    (highProbAt_univ _ _)
    (Eventually.of_forall fun _ _ _ _ => by norm_num)
    (perTimeDomAt_const sz0 (V := fun _ => Unit) (f := fun _ => (1 : ℝ))
      (g := fun _ => (1 : ℝ)) (fun _ => zero_le_one) (Eventually.of_forall fun _ => le_rfl))

private theorem condStable_inst_of_highProb :
    PerTimeDomAt (Sizes.seqP sz0) sz0.size
      (fun _ (_ : Unit) _ => (1 : ℝ)) (fun _ _ _ => (1 : ℝ)) :=
  perTimeDomAt_of_highProb (Ξ := fun _ => Set.univ) (highProbAt_univ _ _)
    (fun τ hτ => Eventually.of_forall fun n _ _ _ => by
      have h := condStable_three_le n
      have : (1 : ℝ) ≤ (sz0.size n : ℝ) ^ τ := Real.one_le_rpow (by linarith) hτ.le
      linarith)

private theorem condStable_inst_const :
    PerTimeDomAt (Sizes.seqP sz0) sz0.size
      (fun n (_ : Unit) _ => (1 : ℝ) / (sz0.size n : ℝ)) (fun _ _ _ => (1 : ℝ)) :=
  perTimeDomAt_const sz0 (fun _ => zero_le_one)
    (Eventually.of_forall fun n => by
      have := condStable_three_le n
      rw [div_le_one (by linarith)]
      linarith)

/-- `η_u⁻¹ ≤ η_v⁻¹` at `E = 0`, `u = 0 ≤ v = 1/2 < 1`. -/
private theorem condStable_inst_inv_etaT : (etaT 0 0)⁻¹ ≤ (etaT 0 (1 / 2))⁻¹ :=
  inv_etaT_le_inv_etaT (by norm_num) (by norm_num) (by norm_num)

/-! #### (4.9) at a nondegenerate sample point

`sz : Sizes 3` any size sequence, slice `n = 0`, `E = 0` (`m = i`), `u = 1/4` (`z_u = (3/4) i`),
two distinct sites `i ≠ k`.  The sample `ω` carries the real coordinates `(i, k, true)` and
`(k, i, true)` equal to `1/2` and all other coordinates `0`; then `H_u = (1/4)(E_{ik} + E_{ki})` is
a rank-two perturbation, whose resolvent is explicit (`blk_green`, the `2 × 2` block algebra
`B² = P`, `B P = B`), `‖G - m‖_max = 2/5 ≤ 1/2`, and `G_{ki} = G_{ik} = 2/5 ≠ 0`.  The instance is
at `sz0` with `i = (0,0,0)`, `k = (1,0,0)` of `Z_128^3`. -/

section Rank2

variable {sz : Sizes 3} {i k : Idx 3 (sz.L 0) (sz.W 0)}

/-- The sample point: the real coordinates of the pair `(i, k)` equal `1/2`, all others vanish. -/
private def condStableΩ (sz : Sizes 3) (i k : Idx 3 (sz.L 0) (sz.W 0)) : Sizes.SeqΩ sz :=
  fun c => if c = ⟨0, (i, k, true)⟩ ∨ c = ⟨0, (k, i, true)⟩ then 1 / 2 else 0

private theorem condStable_seqXmat (hik : i ≠ k) :
    Sizes.seqXmat sz 0 (condStableΩ sz i k)
      = (1 / 2 : ℂ) • (single i k (1 : ℂ) + single k i 1) := by
  have hT : ∀ x y : Idx 3 (sz.L 0) (sz.W 0), sz.slice 0 (condStableΩ sz i k) (x, y, true)
      = if (x = i ∧ y = k) ∨ (x = k ∧ y = i) then 1 / 2 else 0 := by
    intro x y
    simp [Sizes.slice, condStableΩ, Prod.ext_iff]
  have hF : ∀ x y : Idx 3 (sz.L 0) (sz.W 0), sz.slice 0 (condStableΩ sz i k) (x, y, false) = 0 := by
    intro x y
    simp [Sizes.slice, condStableΩ]
  ext x y
  simp only [Sizes.seqXmat, Xmat, Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply,
    single_apply, smul_eq_mul]
  unfold Xentry
  have hrhs : (1 / 2 : ℂ) * ((if i = x ∧ k = y then 1 else 0) + if k = x ∧ i = y then 1 else 0)
      = if (x = i ∧ y = k) ∨ (x = k ∧ y = i) then 1 / 2 else 0 := by
    by_cases h1 : x = i ∧ y = k
    · obtain ⟨rfl, rfl⟩ := h1
      simp [hik, hik.symm]
    · by_cases h2 : x = k ∧ y = i
      · obtain ⟨rfl, rfl⟩ := h2
        simp [hik, hik.symm]
      · have h1' : ¬ (i = x ∧ k = y) := fun h => h1 ⟨h.1.symm, h.2.symm⟩
        have h2' : ¬ (k = x ∧ i = y) := fun h => h2 ⟨h.1.symm, h.2.symm⟩
        simp [h1, h2, h1', h2']
  rw [hrhs]
  rcases idxKey_lt_or_eq_or_lt 3 (sz.L 0) (sz.W 0) x y with h | h | h
  · rw [ite_eq_left h, hT, hF]
    split_ifs <;> simp
  · subst h
    have hlt : ¬ idxKey 3 (sz.L 0) (sz.W 0) x < idxKey 3 (sz.L 0) (sz.W 0) x := lt_irrefl _
    rw [ite_eq_right_iff.mpr (fun h' => absurd h' hlt),
      ite_eq_right_iff.mpr (fun h' => absurd h' hlt), hT]
    have : ¬ ((x = i ∧ x = k) ∨ (x = k ∧ x = i)) := by
      rintro (⟨a, b⟩ | ⟨a, b⟩)
      · exact hik (a.symm.trans b)
      · exact hik (b.symm.trans a)
    simp [this]
  · have hlt : ¬ idxKey 3 (sz.L 0) (sz.W 0) x < idxKey 3 (sz.L 0) (sz.W 0) y := not_lt.mpr h.le
    rw [ite_eq_right_iff.mpr (fun h' => absurd h' hlt), ite_eq_left h, hT, hF]
    have hyx : ((y = i ∧ x = k) ∨ (y = k ∧ x = i)) ↔ ((x = i ∧ y = k) ∨ (x = k ∧ y = i)) := by
      tauto
    simp only [hyx]
    split_ifs <;> simp

section Block

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem blk_BB (i k : ι) (hik : i ≠ k) :
    (single i k (1 : ℂ) + single k i 1) * (single i k 1 + single k i 1)
      = single i i 1 + single k k 1 := by
  simp [add_mul, mul_add, hik, hik.symm, add_comm]

private theorem blk_BP (i k : ι) (hik : i ≠ k) :
    (single i k (1 : ℂ) + single k i 1) * (single i i 1 + single k k 1)
      = single i k 1 + single k i 1 := by
  simp [add_mul, mul_add, hik, hik.symm, add_comm]

/-- The abstract algebra: `B² = P`, `B P = B`. -/
private theorem blk_alg (B P : Matrix ι ι ℂ) (hBB : B * B = P) (hBP : B * P = B) {b z : ℂ}
    (hz : z ≠ 0) (hden : b ^ 2 - z ^ 2 ≠ 0) :
    (b • B - z • (1 : Matrix ι ι ℂ)) * ((-1 / z) • (1 : Matrix ι ι ℂ)
        + (b ^ 2 / (z * (b ^ 2 - z ^ 2))) • P + (b / (b ^ 2 - z ^ 2)) • B) = 1 := by
  simp only [sub_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul,
    smul_smul, hBB, hBP]
  match_scalars <;> field_simp <;> ring

/-- The resolvent of a rank-two perturbation. -/
private theorem blk_green (i k : ι) (hik : i ≠ k) {b z : ℂ} (hz : z ≠ 0)
    (hden : b ^ 2 - z ^ 2 ≠ 0) :
    green (b • (single i k (1 : ℂ) + single k i 1)) z
      = (-1 / z) • (1 : Matrix ι ι ℂ)
        + (b ^ 2 / (z * (b ^ 2 - z ^ 2))) • (single i i (1 : ℂ) + single k k 1)
        + (b / (b ^ 2 - z ^ 2)) • (single i k (1 : ℂ) + single k i 1) := by
  unfold green
  exact Matrix.inv_eq_right_inv (blk_alg _ _ (blk_BB i k hik) (blk_BP i k hik) hz hden)

end Block

private theorem condStable_mE_zero : mE 0 = Complex.I := by
  have h4 : Real.sqrt (4 - (0 : ℝ) ^ 2) = 2 := by
    rw [show (4 : ℝ) - 0 ^ 2 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp only [mE, h4]
  push_cast
  ring

private theorem condStable_hflow (hik : i ≠ k) :
    Sizes.seqHflow sz 0 (1 / 4) (condStableΩ sz i k)
      = (1 / 4 : ℂ) • (single i k (1 : ℂ) + single k i 1) := by
  have hs : Real.sqrt (1 / 4) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [Sizes.seqHflow, condStable_seqXmat hik, hs, smul_smul]
  norm_num

private theorem condStable_zt : zt 0 (1 / 4) = (3 / 4 : ℂ) * Complex.I := by
  simp only [zt, condStable_mE_zero]
  push_cast
  ring

/-- The resolvent of the sample point at `E = 0`, `u = 1/4`, explicitly. -/
private theorem condStable_green (hik : i ≠ k) :
    green (Sizes.seqHflow sz 0 (1 / 4) (condStableΩ sz i k)) (zt 0 (1 / 4))
      = ((4 / 3 : ℂ) * Complex.I) • (1 : Matrix (Idx 3 (sz.L 0) (sz.W 0)) (Idx 3 (sz.L 0) (sz.W 0)) ℂ)
        + (-(2 / 15 : ℂ) * Complex.I) • (single i i (1 : ℂ) + single k k 1)
        + (2 / 5 : ℂ) • (single i k (1 : ℂ) + single k i 1) := by
  have hz : (3 / 4 : ℂ) * Complex.I ≠ 0 := by simp
  have hD : (1 / 4 : ℂ) ^ 2 - ((3 / 4 : ℂ) * Complex.I) ^ 2 = 5 / 8 := by
    rw [mul_pow, Complex.I_sq]; norm_num
  have hden : (1 / 4 : ℂ) ^ 2 - ((3 / 4 : ℂ) * Complex.I) ^ 2 ≠ 0 := by
    rw [hD]; norm_num
  rw [condStable_hflow hik, condStable_zt, blk_green _ _ hik hz hden, hD]
  have h0 : (-1 / ((3 / 4 : ℂ) * Complex.I)) = (4 / 3 : ℂ) * Complex.I := by
    rw [div_eq_iff hz]
    linear_combination (-1 : ℂ) * Complex.I_sq
  have h1 : (1 / 4 : ℂ) ^ 2 / (((3 / 4 : ℂ) * Complex.I) * (5 / 8))
      = -(2 / 15 : ℂ) * Complex.I := by
    rw [div_eq_iff (mul_ne_zero hz (by norm_num))]
    linear_combination (1 / 16 : ℂ) * Complex.I_sq
  have h2 : (1 / 4 : ℂ) / (5 / 8) = 2 / 5 := by norm_num
  rw [h0, h1, h2]

private theorem condStable_norm_realMul_I (r : ℝ) : ‖(r : ℂ) * Complex.I‖ = |r| := by
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

set_option linter.flexible false in
private theorem condStable_goodEvent_nd (hik : i ≠ k) :
    GoodEvent (green (Sizes.seqHflow sz 0 (1 / 4) (condStableΩ sz i k)) (zt 0 (1 / 4)))
      (mE 0) (1 / 2) := by
  rw [condStable_green hik, condStable_mE_zero]
  intro x y
  have hik' : ¬ k = i := fun h => hik h.symm
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, single_apply, smul_eq_mul]
  by_cases hxy : x = y
  · subst hxy
    by_cases hxi : x = i
    · subst hxi
      simp [hik']
      have e : (4 / 3 : ℂ) * Complex.I + -(2 / 15 * Complex.I) - Complex.I
          = ((1 / 5 : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [e, condStable_norm_realMul_I]
      norm_num [abs_of_pos]
    · by_cases hxk : x = k
      · subst hxk
        simp [hik]
        have e : (4 / 3 : ℂ) * Complex.I + -(2 / 15 * Complex.I) - Complex.I
            = ((1 / 5 : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [e, condStable_norm_realMul_I]
        norm_num [abs_of_pos]
      · simp [Ne.symm hxi, Ne.symm hxk]
        have e : (4 / 3 : ℂ) * Complex.I - Complex.I = ((1 / 3 : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [e, condStable_norm_realMul_I]
        norm_num [abs_of_pos]
  · have hP1 : ¬ (i = x ∧ i = y) := fun h => hxy (h.1.symm.trans h.2)
    have hP2 : ¬ (k = x ∧ k = y) := fun h => hxy (h.1.symm.trans h.2)
    have hyx : ¬ y = x := Ne.symm hxy
    have h25 : ‖(2 / 5 : ℂ)‖ ≤ 2⁻¹ := by
      have e : (2 / 5 : ℂ) = ((2 / 5 : ℝ) : ℂ) := by push_cast; ring
      rw [e, Complex.norm_real, Real.norm_eq_abs]
      norm_num [abs_of_pos]
    by_cases h1 : i = x ∧ k = y
    · have h2 : ¬ (k = x ∧ i = y) := fun h => hik (h1.1.trans h.1.symm)
      simpa [hxy, hyx, h1, h2] using h25
    · by_cases h2 : k = x ∧ i = y
      · simpa [hxy, hyx, h1, h2] using h25
      · simp [hxy, hP1, hP2, h1, h2]

private theorem condStable_green_ki (hik : i ≠ k) :
    green (Sizes.seqHflow sz 0 (1 / 4) (condStableΩ sz i k)) (zt 0 (1 / 4)) k i = 2 / 5 := by
  have hik' : ¬ k = i := fun h => hik h.symm
  rw [condStable_green hik]
  simp [hik, hik']

private theorem condStable_green_ik (hik : i ≠ k) :
    green (Sizes.seqHflow sz 0 (1 / 4) (condStableΩ sz i k)) (zt 0 (1 / 4)) i k = 2 / 5 := by
  have hik' : ¬ k = i := fun h => hik h.symm
  rw [condStable_green hik]
  simp [hik, hik']

/-- **(4.9) at a nondegenerate sample point** (any `sz : Sizes 3`, `n = 0`, `E = 0`, `u = 1/4`,
`i ≠ k`): `‖G - m‖_max = 2/5 ≤ 1/2 = δ'`, `G_{ik} = G_{ki} = 2/5`, so the event `Ω(t,c)` holds at
the level `δ' = 1/2` of the theorem, and both sides are nonzero. -/
private theorem condStable_inst_minor_nd (hik : i ≠ k) :
    ‖greenDiagCentered sz 0 (1 / 4) (zt 0 (1 / 4)) (mE 0) k (condStableΩ sz i k)
        - greenMinorDiagCentered sz 0 (1 / 4) (zt 0 (1 / 4)) (mE 0) i ⟨k, Ne.symm hik⟩
          (condStableΩ sz i k)‖
      ≤ 2 * (‖green (Sizes.seqHflow sz 0 (1 / 4) (condStableΩ sz i k)) (zt 0 (1 / 4)) k i‖
          * ‖green (Sizes.seqHflow sz 0 (1 / 4) (condStableΩ sz i k)) (zt 0 (1 / 4)) i k‖) ∧
    0 < ‖green (Sizes.seqHflow sz 0 (1 / 4) (condStableΩ sz i k)) (zt 0 (1 / 4)) k i‖
        * ‖green (Sizes.seqHflow sz 0 (1 / 4) (condStableΩ sz i k)) (zt 0 (1 / 4)) i k‖ :=
  ⟨norm_greenDiagCentered_sub_minor_le sz 0 (by norm_num) (by norm_num) (δ' := 1 / 2) le_rfl
    (condStable_goodEvent_nd hik) i k hik,
    by rw [condStable_green_ki hik, condStable_green_ik hik]; norm_num⟩

end Rank2

/-- The site `(1,0,0)` of slice `0`. -/
private def condDomCk1 : condDomCkI := Pi.single 0 1

private theorem condDomCk01 : condDomCk0 ≠ condDomCk1 := by
  intro h
  have := congrFun h 0
  simp only [condDomCk0, condDomCk1, Pi.single_eq_same] at this
  change (0 : ZMod 128) = 1 at this
  exact absurd this (by decide)

/-- **(4.9) at `sz0`**, `n = 0`, `E = 0`, `u = 1/4`, `i = (0,0,0)`, `k = (1,0,0)`. -/
example :=
  condStable_inst_minor_nd (sz := sz0) (i := condDomCk0) (k := condDomCk1) condDomCk01

/-! #### EntryGauss at the preflight sequence `sz0`

`sz0 : Sizes 3` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`; `n = 0`: `L = 4`,
`W = 32`, `N = 2097152`), admissible at `𝔠 = 1/6`, `𝔡 = 1/10`, the energy `E_n = lemE z_n` and the
time `t ≡ 1/16` of `Instance.premises` (`Green/Pins.lean`), `κ = δ = (1/10)/2`, `c = 1/40`.  The
two unconditional statements are applied with every hypothesis discharged; the two adapters keep
the paper's (`asGMc`) `AsGMcSeq` as a hypothesis (it is not proved here). -/

open RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst in
private theorem EntryGauss_chk_gij : GijOmegaSeq sz0 (STflowE z0) tInst (1 / 40) := by
  obtain ⟨hA, hE, h0, h1, hR⟩ := Instance.premises
  exact gijOmegaSeq sz0 (κ := (1 / 10) / 2) (δ := (1 / 10) / 2) (by norm_num) (by norm_num) hA
    (STflowE z0) tInst hE h0 h1 hR (1 / 40) (by norm_num)

open RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst in
private theorem EntryGauss_chk_gii : GiiOmegaSeq sz0 (STflowE z0) tInst (1 / 40) := by
  obtain ⟨hA, hE, h0, h1, hR⟩ := Instance.premises
  exact giiOmegaSeq sz0 (by norm_num) (κ := (1 / 10) / 2) (δ := (1 / 10) / 2) (by norm_num)
    (by norm_num) hA (STflowE z0) tInst hE h0 h1 hR (1 / 40) (by norm_num)

open RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst in
private theorem EntryGauss_chk_adapters (hAs : AsGMcSeq sz0 (STflowE z0) tInst (1 / 40)) :
    GijSeq sz0 (STflowE z0) tInst ∧ GiiSeq sz0 (STflowE z0) tInst := by
  obtain ⟨hA, hE, h0, h1, hR⟩ := Instance.premises
  exact ⟨gijSeq_of_asGMc sz0 (κ := (1 / 10) / 2) (δ := (1 / 10) / 2) (by norm_num) (by norm_num)
      hA (STflowE z0) tInst hE h0 h1 hR (1 / 40) (by norm_num) hAs,
    giiSeq_of_asGMc sz0 (by norm_num) (κ := (1 / 10) / 2) (δ := (1 / 10) / 2) (by norm_num)
      (by norm_num) hA (STflowE z0) tInst hE h0 h1 hR (1 / 40) (by norm_num) hAs⟩

end

end Checks

end RBM.Green
