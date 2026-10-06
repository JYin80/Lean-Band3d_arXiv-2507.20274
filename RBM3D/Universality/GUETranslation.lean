/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.Step1Band
import RBM3D.Universality.Step1RegularityGUE
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# `RBM3D.Universality.GUETranslation` (UN-14): the GUE translation `0 → E'`, the row `UNInfty1Row'`

Ticket T2226.  Paper: arXiv:2507.20274, `paper/tex/1_2_Intro_model_result.tex`, the proof of
`Thm: B_Univ` `1_2:566-581` (Step 1: the OU marginal against the GUE; here the GUE at energy `0`
against the GUE at `E'`).

Port of RBM2D `Universality/GUETranslation.lean` (commit `c9a24cf`, 1303 lines; read-only) to
`Sizes d`, `Ω d L W`, `N = (W L)^d = Nsz sz n`, on top of the merged `step1Band_row` (UN-13) and
`gueGoodHighProb` (UN-11).  Proves the owed pin `UNInfty1Row'` (`PinsDens.lean:88`, merged
unchanged) as `un_infty1Row'`, and the new `UNGUETranslation`, `UNGUETranslationRow` (proved here,
not registered).

Replaced against RBM2D: `freeConvST (v n) (tt n)` by the `Classical.choose` of the `∃ mfc`,
`∃ ρ'` of `GUEGoodAt` (as `Step1Band_core`); RBM2D's ratio `r = ρ'/ρ_sc(E₀)` by the `ρ^k` form of
`Step1Cond_scaledPairing_lipschitz` at `(ρ_sc(E₀), ρ'_n)`; `GUELocal`, `L32`, `GUEGoodHighProb` by
`UNGUELocal`, `UNL32`, `UNGUEGoodHighProb`; `ContDiff ∧ HasCompactSupport` by `IsTestFun`; `Sizes`
by `Sizes d` with `3 ≤ d`; `d.size` by `Nsz`.  The carrier-free helpers of RBM2D (`gue_count`,
`kPoint_shift`, `eventually_forall`, `abs_integral_kPoint_le`) are the merged public `step1Band_*`
of UN-13; the small private helpers of `Step1Band.lean` are copied under the prefix
`GUETranslation_`.  `d` enters only through `Idx d`, `Ω d`, `gueP d` and `N ≥ 27`; every exponent
involves `τs = 1/2`, `k` only; there is no `Admissible` on the GUE side.

Sections: 1 the two Props; 2 copied private helpers; 3 the conditional functional and target 1;
4 the worst-sequence core (target 2a); 5 uniformity (target 2b); 6 the translation (targets 3a,
3b); 7 the row (targets 4a-4c); 8 compiled nonempty instances (target 5).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal ENNReal

namespace RBM.Univ

/-! ### 1. The two Props (RBM2D `:52-73`) -/

/-- `UNGUETranslation` (proved here by `guetranslation`; not registered): the GUE translation `0 → E` (RBM2D
`GUETranslation`, `GUETranslation.lean:59`; RBM1D `gue_translation'`): for a bulk energy `E`, the GUE `k`-point
functional at `E` is asymptotically the GUE functional at energy `0` with the test function dilated by
`ρ_sc(0)/ρ_sc(E)`.  The carrier is the GUE alone (`gueP`): no `Admissible`, no `τ_U`. -/
def UNGUETranslation : Prop :=
  UNL32 → UNGUELocal →
    ∀ d : ℕ, 3 ≤ d → ∀ sz : Sizes d, Tendsto (fun n => sz.size n) atTop atTop →
      ∀ k : ℕ, ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ →
        ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
          Tendsto (fun n =>
            (∫ ω, kPoint k (fun α => O ((rhoSC 0 / rhoSC E) • α)) 0
                (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues ∂(gueP d (sz.L n) (sz.W n))) -
            (∫ ω, kPoint k O E (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues
                ∂(gueP d (sz.L n) (sz.W n))))
            atTop (𝓝 0)

/-- `UNGUETranslationRow` (proved here by `guetranslationRow`; not registered): the translation from the GUE-side
good event (RBM2D `GUETranslationRow`, `:73`). -/
def UNGUETranslationRow : Prop := UNGUEGoodHighProb → UNGUETranslation

/-! ### 2. Copied private helpers of `Step1Band.lean` (prefix `GUETranslation_`; RBM2D `:87-330`, `:463-493`) -/

private theorem GUETranslation_size_ge {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) : 27 ≤ sz.size n := by
  have h3 : 3 ≤ sz.W n * sz.L n :=
    (sz.three_le_L n).trans (Nat.le_mul_of_pos_left _ (sz.W_pos n))
  calc 27 = 3 ^ 3 := by norm_num
    _ ≤ 3 ^ d := Nat.pow_le_pow_right (by norm_num) hd
    _ ≤ (sz.W n * sz.L n) ^ d := Nat.pow_le_pow_left h3 d

private theorem GUETranslation_Nr_ge {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) : (27 : ℝ) ≤ Nsz sz n := by
  exact_mod_cast GUETranslation_size_ge hd sz n

private theorem GUETranslation_Nr_pos {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) : (0 : ℝ) < Nsz sz n := by
  linarith [GUETranslation_Nr_ge hd sz n]

private theorem GUETranslation_Nr_ge_one {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) : (1 : ℝ) ≤ Nsz sz n := by
  linarith [GUETranslation_Nr_ge hd sz n]

private theorem GUETranslation_card_real {d : ℕ} (sz : Sizes d) (n : ℕ) :
    (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ) = Nsz sz n := by
  rw [sz.card_Idx]

private theorem GUETranslation_Nr_tendsto {d : ℕ} {sz : Sizes d}
    (hsz : Tendsto (fun n => sz.size n) atTop atTop) :
    Tendsto (fun n => Nsz sz n) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp hsz

private theorem GUETranslation_size_tendsto {d : ℕ} {sz : Sizes d} (h : sz.SizeTendsto) :
    Tendsto (fun n => sz.size n) atTop atTop :=
  tendsto_natCast_atTop_iff.mp h

private theorem GUETranslation_rpow_tendsto_zero {d : ℕ} {sz : Sizes d}
    (hsz : Tendsto (fun n => sz.size n) atTop atTop) {e : ℝ} (he : e < 0) :
    Tendsto (fun n => Nsz sz n ^ e) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (y := -e) (by linarith)).comp (GUETranslation_Nr_tendsto hsz)
  simpa [Function.comp_def] using h
/-- `|kPoint k P E λ| ≤ N^k sup|P|`: the prefactor `N^k / descFactorial N k` times at most
`descFactorial N k` embeddings (copy of the private `Step1Band_abs_kPoint_le`; RBM2D `GUETranslation_abs_kPoint_le`,
`GUETranslation.lean:150` at `c9a24cf`). -/
private theorem GUETranslation_abs_kPoint_le {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    {P : (Fin k → ℝ) → ℝ} {B : ℝ} (hB : ∀ x, |P x| ≤ B) (E : ℝ) (lam : ι → ℝ) :
    |kPoint k P E lam| ≤ (Fintype.card ι : ℝ) ^ k * B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  unfold kPoint
  set M : ℕ := Fintype.card ι with hM
  set S : ℝ := ∑ f : Fin k ↪ ι, P (fun j => (M : ℝ) * (lam (f j) - E)) with hS
  have hcard : Fintype.card (Fin k ↪ ι) = M.descFactorial k := by
    rw [Fintype.card_embedding_eq, Fintype.card_fin]
  have hSle : |S| ≤ (M.descFactorial k : ℝ) * B := by
    calc |S| ≤ ∑ f : Fin k ↪ ι, |P (fun j => (M : ℝ) * (lam (f j) - E))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _f : Fin k ↪ ι, B := Finset.sum_le_sum fun f _ => hB _
      _ = (M.descFactorial k : ℝ) * B := by
          rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (M : ℝ) ^ k / (M.descFactorial k : ℝ))]
  by_cases h0 : (M.descFactorial k : ℝ) = 0
  · rw [h0, div_zero, zero_mul]; positivity
  · calc (M : ℝ) ^ k / (M.descFactorial k : ℝ) * |S|
        ≤ (M : ℝ) ^ k / (M.descFactorial k : ℝ) * ((M.descFactorial k : ℝ) * B) :=
          mul_le_mul_of_nonneg_left hSle (by positivity)
      _ = (M : ℝ) ^ k * B := by field_simp

private theorem GUETranslation_kPoint_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    {P : (Fin k → ℝ) → ℝ} (hP : ∀ x, 0 ≤ P x) (E : ℝ) (lam : ι → ℝ) :
    0 ≤ kPoint k P E lam := by
  unfold kPoint
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun f _ => hP _)

private theorem GUETranslation_kPoint_mono {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    {P Q : (Fin k → ℝ) → ℝ} (hPQ : ∀ x, P x ≤ Q x) (E : ℝ) (lam : ι → ℝ) :
    kPoint k P E lam ≤ kPoint k Q E lam := by
  unfold kPoint
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun f _ => hPQ _) (by positivity)

private theorem GUETranslation_kPoint_neg {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (P : (Fin k → ℝ) → ℝ) (E : ℝ) (lam : ι → ℝ) :
    kPoint k (fun β => -P β) E lam = -kPoint k P E lam := by
  unfold kPoint
  simp only [Finset.sum_neg_distrib, mul_neg]

/-- Integrability of the `k`-point functional of a measurable Hermitian matrix map. -/
private theorem GUETranslation_integrable_kPoint {Ω' : Type*} [MeasurableSpace Ω'] (Pm : Measure Ω')
    [IsFiniteMeasure Pm] {n : Type*} [Fintype n] [DecidableEq n] {Hm : Ω' → Matrix n n ℂ}
    (hm : Measurable Hm) (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ) {O : (Fin k → ℝ) → ℝ}
    (hO : Continuous O) {B : ℝ} (hB : ∀ x, |O x| ≤ B) (E : ℝ) :
    Integrable (fun ω => kPoint k O E (hH ω).eigenvalues) Pm :=
  Integrable.of_bound (measurable_kPoint_eigenvalues Hm hH hm k O hO E).aestronglyMeasurable
    ((Fintype.card n : ℝ) ^ k * B) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact GUETranslation_abs_kPoint_le k hB E _)
private theorem GUETranslation_integral_kPoint_nonneg {Ω' : Type*} [MeasurableSpace Ω']
    (Pm : Measure Ω') {n : Type*} [Fintype n] [DecidableEq n] (Hm : Ω' → Matrix n n ℂ)
    (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ) {P : (Fin k → ℝ) → ℝ} (hP : 0 ≤ P) (E : ℝ) :
    0 ≤ ∫ ω, kPoint k P E (hH ω).eigenvalues ∂Pm :=
  integral_nonneg fun _ => GUETranslation_kPoint_nonneg k (fun x => hP x) E _

/-- `|∫ kPoint P| ≤ ∫ kPoint Q` when `|P| ≤ Q` pointwise (smooth compactly supported `P`, `Q`). -/
private theorem GUETranslation_abs_integral_le_of_abs_le {Ω' : Type*} [MeasurableSpace Ω']
    (Pm : Measure Ω') [IsFiniteMeasure Pm] {n : Type*} [Fintype n] [DecidableEq n]
    {Hm : Ω' → Matrix n n ℂ} (hm : Measurable Hm) (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ)
    {P Q : (Fin k → ℝ) → ℝ} (hP : IsTestFun P) (hQ : IsTestFun Q)
    (hPQ : ∀ β, |P β| ≤ Q β) (E : ℝ) :
    |∫ ω, kPoint k P E (hH ω).eigenvalues ∂Pm| ≤ ∫ ω, kPoint k Q E (hH ω).eigenvalues ∂Pm := by
  obtain ⟨BP, hBP⟩ := hP.1.continuous.bounded_above_of_compact_support hP.2
  obtain ⟨BQ, hBQ⟩ := hQ.1.continuous.bounded_above_of_compact_support hQ.2
  have hBP' : ∀ x, |P x| ≤ BP := fun x => by simpa [Real.norm_eq_abs] using hBP x
  have hBQ' : ∀ x, |Q x| ≤ BQ := fun x => by simpa [Real.norm_eq_abs] using hBQ x
  have hIP := GUETranslation_integrable_kPoint Pm hm hH k hP.1.continuous hBP' E
  have hIQ := GUETranslation_integrable_kPoint Pm hm hH k hQ.1.continuous hBQ' E
  have hBPn : ∀ x, |(fun β => -P β) x| ≤ BP := fun x => by simpa using hBP' x
  have hIPn := GUETranslation_integrable_kPoint Pm hm hH k hP.1.neg.continuous hBPn E
  have h1 : ∫ ω, kPoint k P E (hH ω).eigenvalues ∂Pm ≤
      ∫ ω, kPoint k Q E (hH ω).eigenvalues ∂Pm :=
    integral_mono hIP hIQ fun ω =>
      GUETranslation_kPoint_mono k (fun β => (le_abs_self _).trans (hPQ β)) E _
  have h2 : ∫ ω, kPoint k (fun β => -P β) E (hH ω).eigenvalues ∂Pm ≤
      ∫ ω, kPoint k Q E (hH ω).eigenvalues ∂Pm :=
    integral_mono hIPn hIQ fun ω =>
      GUETranslation_kPoint_mono k (fun β => (neg_le_abs _).trans (hPQ β)) E _
  have h3 : ∫ ω, kPoint k (fun β => -P β) E (hH ω).eigenvalues ∂Pm =
      -∫ ω, kPoint k P E (hH ω).eigenvalues ∂Pm := by
    simp only [GUETranslation_kPoint_neg, integral_neg]
  rw [h3] at h2
  exact abs_le.mpr ⟨by linarith, h1⟩

/-- A dilate of a test function is a test function (`isTestFun_comp_smul`, written as `fun j => a * β j`). -/
private theorem GUETranslation_isTestFun_dilate {k : ℕ} {O : (Fin k → ℝ) → ℝ} (hO : IsTestFun O) {a : ℝ}
    (ha : a ≠ 0) : IsTestFun (fun β : Fin k → ℝ => O (fun j => a * β j)) :=
  isTestFun_comp_smul hO ha

/-- A nonnegative test function dominating `|O|`. -/
private theorem GUETranslation_exists_abs_dominating {k : ℕ} {O : (Fin k → ℝ) → ℝ} (hO : IsTestFun O) :
    ∃ Qa : (Fin k → ℝ) → ℝ, IsTestFun Qa ∧ 0 ≤ Qa ∧ ∀ β, |O β| ≤ Qa β := by
  have hO' : IsTestFun (fun β => -O β) := ⟨hO.1.neg, hO.2.neg⟩
  obtain ⟨Q1, hQ1, hQ10, h1⟩ := Step1Cond_exists_dominating_testFun hO 1 1
  obtain ⟨Q2, hQ2, hQ20, h2⟩ := Step1Cond_exists_dominating_testFun hO' 1 1
  refine ⟨fun β => Q1 β + Q2 β, ⟨hQ1.1.add hQ2.1, hQ1.2.add hQ2.2⟩,
    fun β => add_nonneg (hQ10 β) (hQ20 β), fun β => ?_⟩
  have e : (fun j => (1 : ℝ) * β j) = β := by funext j; simp
  have a1 := h1 1 ⟨le_rfl, le_rfl⟩ β
  have a2 := h2 1 ⟨le_rfl, le_rfl⟩ β
  rw [e] at a1 a2
  have b1 : 0 ≤ Q1 β := hQ10 β
  have b2 : 0 ≤ Q2 β := hQ20 β
  change |O β| ≤ Q1 β + Q2 β
  exact abs_le.mpr ⟨by linarith, by linarith⟩
private theorem GUETranslation_measurable_Xmat (d L W : ℕ) [NeZero L] [NeZero W] :
    Measurable (Xmat d L W) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => measurable_Xentry d L W i j

/-- Measurability of `dbmMat` in the GUE sample. -/
private theorem GUETranslation_measurable_dbm (d L W : ℕ) [NeZero L] [NeZero W] (v : Idx d L W → ℝ)
    (t : ℝ) : Measurable (dbmMat d L W v t) := by
  have hcont : Continuous (fun Y : Matrix (Idx d L W) (Idx d L W) ℂ =>
      Matrix.diagonal (fun i => (v i : ℂ)) + Real.sqrt t • Y) := by fun_prop
  exact hcont.measurable.comp (GUETranslation_measurable_Xmat d L W)

/-- Measurability of a single eigenvalue along a measurable Hermitian matrix map (Weyl's bound
`eigenvalues₀_abs_sub_le`; the analogous helpers of `EigenMeasurable`/`Step1Cond` are private; copy of the private
`Step1Band_measurable_eigenvalue`; RBM2D `GUETranslation_measurable_eigenvalue`, `GUETranslation.lean:298`). -/
private theorem GUETranslation_measurable_eigenvalue {Ω' : Type*} [MeasurableSpace Ω'] {n : Type*}
    [Fintype n] [DecidableEq n] {Hm : Ω' → Matrix n n ℂ} (hm : Measurable Hm)
    (hH : ∀ ω, (Hm ω).IsHermitian) (i : n) : Measurable (fun ω => (hH ω).eigenvalues i) := by
  have hcont : Continuous (fun x : {A : Matrix n n ℂ // A.IsHermitian} =>
      x.2.eigenvalues₀ ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm i)) := by
    rw [continuous_iff_continuousAt]
    intro x
    change Tendsto (fun y : {A : Matrix n n ℂ // A.IsHermitian} => y.2.eigenvalues₀ _)
      (𝓝 x) (𝓝 (x.2.eigenvalues₀ _))
    rw [tendsto_iff_dist_tendsto_zero]
    have hsub : Continuous (fun A : Matrix n n ℂ => A - x.1) := continuous_id.sub continuous_const
    have hc : Continuous (fun A : Matrix n n ℂ =>
        Real.sqrt (∑ a, ∑ b, ‖(A - x.1) a b‖ ^ 2)) :=
      Continuous.sqrt (continuous_finsetSum Finset.univ fun a _ =>
        continuous_finsetSum Finset.univ fun b _ =>
          (((continuous_apply b).comp (continuous_apply a)).comp hsub).norm.pow 2)
    have h0 : Tendsto (fun A : Matrix n n ℂ => Real.sqrt (∑ a, ∑ b, ‖(A - x.1) a b‖ ^ 2))
        (𝓝 x.1) (𝓝 0) := by
      have hval : Real.sqrt (∑ a, ∑ b, ‖(x.1 - x.1) a b‖ ^ 2) = 0 := by simp
      have := hc.continuousAt (x := x.1)
      rwa [ContinuousAt, hval] at this
    have hcomp : Tendsto (fun y : {A : Matrix n n ℂ // A.IsHermitian} =>
        Real.sqrt (∑ a, ∑ b, ‖(y.1 - x.1) a b‖ ^ 2)) (𝓝 x) (𝓝 0) :=
      h0.comp (continuous_subtype_val.continuousAt (x := x))
    refine squeeze_zero (fun _ => dist_nonneg) (fun y => ?_) hcomp
    rw [Real.dist_eq]
    exact eigenvalues₀_abs_sub_le y.2 x.2 _
  have hφ : Measurable (fun ω => (⟨Hm ω, hH ω⟩ : {A : Matrix n n ℂ // A.IsHermitian})) :=
    hm.subtype_mk (h := hH)
  have := hcont.measurable.comp hφ
  simpa [Matrix.IsHermitian.eigenvalues, Function.comp_def] using this
private theorem GUETranslation_dbmMat_shift (d L W : ℕ) [NeZero L] [NeZero W] (v : Idx d L W → ℝ)
    (t E : ℝ) (ω : Ω d L W) :
    dbmMat d L W (fun i => v i - E) t ω =
      dbmMat d L W v t ω - (E : ℂ) • (1 : Matrix (Idx d L W) (Idx d L W) ℂ) := by
  unfold dbmMat
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one, Complex.ofReal_sub]
    ring
  · simp [hij]

/-- The shift inside the DBM functional: `kPoint k O 0` of `dbmMat (v - E)` is `kPoint k O E` of
`dbmMat v`, pointwise and hence after integration over the GUE block (RBM2D `GUETranslation_integral_dbm_shift`, `GUETranslation.lean:478`). -/
private theorem GUETranslation_integral_dbm_shift (d L W : ℕ) [NeZero L] [NeZero W]
    (v : Idx d L W → ℝ) (t E : ℝ) (k : ℕ) (O : (Fin k → ℝ) → ℝ) :
    ∫ ω, kPoint k O 0 (dbmMat_isHermitian d L W (fun i => v i - E) t ω).eigenvalues
        ∂(gueP d L W) =
      ∫ ω, kPoint k O E (dbmMat_isHermitian d L W v t ω).eigenvalues ∂(gueP d L W) :=
  integral_congr_ae (Eventually.of_forall fun ω =>
    step1Band_kPoint_shift (dbmMat_isHermitian d L W v t ω)
      (dbmMat_isHermitian d L W (fun i => v i - E) t ω) E (GUETranslation_dbmMat_shift d L W v t E ω) k O)

/-! ### 3. The conditional functional and target 1 (RBM2D `:681-735`) -/

/-- The conditional (DBM) functional given the first block `ω` of the GUE (RBM2D `GUETranslation_Hs`, `:681`):
`∫ kPoint k O 0 (λ(diag(vGUE ω) + √(1 - e^{-t*}) X₂)) d gueP(X₂)`. -/
private def GUETranslation_F {d : ℕ} (sz : Sizes d) (τs E₀ : ℝ) (n k : ℕ) (O : (Fin k → ℝ) → ℝ)
    (ω : Ω d (sz.L n) (sz.W n)) : ℝ :=
  ∫ y, kPoint k O 0 (dbmMat_isHermitian d (sz.L n) (sz.W n) (vGUE sz n τs E₀ ω)
    (1 - Real.exp (-(ouTStar sz τs n))) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n))

/-- The conditional functional is measurable in the first block (RBM2D `GUETranslation_measurable_Hs`, `:688`). -/
private theorem GUETranslation_measurable_F {d : ℕ} (sz : Sizes d) (τs E₀ : ℝ) (n k : ℕ)
    {O : (Fin k → ℝ) → ℝ} (hO : Continuous O) : Measurable (GUETranslation_F sz τs E₀ n k O) := by
  set t := 1 - Real.exp (-(ouTStar sz τs n)) with ht
  have heig : Measurable (fun ω : Ω d (sz.L n) (sz.W n) =>
      fun i => (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues i) :=
    measurable_pi_iff.mpr fun i =>
      GUETranslation_measurable_eigenvalue (GUETranslation_measurable_Xmat d _ _)
        (Xmat_isHermitian d (sz.L n) (sz.W n)) i
  have hv : Measurable (fun ω : Ω d (sz.L n) (sz.W n) => vGUE sz n τs E₀ ω) :=
    measurable_pi_iff.mpr fun i => (((measurable_pi_apply i).comp heig).const_mul _).sub_const _
  have hGc : Continuous (fun q : (Idx d (sz.L n) (sz.W n) → ℝ) × Matrix (Idx d (sz.L n) (sz.W n))
      (Idx d (sz.L n) (sz.W n)) ℂ => Matrix.diagonal (fun i => (q.1 i : ℂ)) + Real.sqrt t • q.2) := by
    refine Continuous.add ?_ (continuous_snd.const_smul (Real.sqrt t))
    exact Continuous.matrix_diagonal (continuous_pi fun i =>
      Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_fst))
  have hm0 : Measurable (fun p : Ω d (sz.L n) (sz.W n) × Ω d (sz.L n) (sz.W n) =>
      ((vGUE sz n τs E₀ p.1, Xmat d (sz.L n) (sz.W n) p.2) :
        (Idx d (sz.L n) (sz.W n) → ℝ) × Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) :=
    (hv.comp measurable_fst).prodMk ((GUETranslation_measurable_Xmat d _ _).comp measurable_snd)
  have hmeq : (fun p : Ω d (sz.L n) (sz.W n) × Ω d (sz.L n) (sz.W n) =>
      dbmMat d (sz.L n) (sz.W n) (vGUE sz n τs E₀ p.1) t p.2) =
      (fun q : (Idx d (sz.L n) (sz.W n) → ℝ) × Matrix (Idx d (sz.L n) (sz.W n))
      (Idx d (sz.L n) (sz.W n)) ℂ => Matrix.diagonal (fun i => (q.1 i : ℂ)) + Real.sqrt t • q.2) ∘
      (fun p : Ω d (sz.L n) (sz.W n) × Ω d (sz.L n) (sz.W n) =>
      ((vGUE sz n τs E₀ p.1, Xmat d (sz.L n) (sz.W n) p.2) :
        (Idx d (sz.L n) (sz.W n) → ℝ) × Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) := by
    funext p
    simp only [Function.comp_apply, dbmMat]
  have hm : Measurable (fun p : Ω d (sz.L n) (sz.W n) × Ω d (sz.L n) (sz.W n) =>
      dbmMat d (sz.L n) (sz.W n) (vGUE sz n τs E₀ p.1) t p.2) := by
    rw [hmeq]; exact hGc.measurable.comp hm0
  have hf := measurable_kPoint_eigenvalues
    (fun p : Ω d (sz.L n) (sz.W n) × Ω d (sz.L n) (sz.W n) =>
      dbmMat d (sz.L n) (sz.W n) (vGUE sz n τs E₀ p.1) t p.2)
    (fun p => dbmMat_isHermitian d (sz.L n) (sz.W n) (vGUE sz n τs E₀ p.1) t p.2)
    hm k O hO 0
  exact (hf.stronglyMeasurable.integral_prod_right' (ν := gueP d (sz.L n) (sz.W n))).measurable

/-- **Target 1** `guetranslation_integral_gue` (RBM2D `GUETranslation_integral_gue`, `:720`, with the shift of
`GUETranslation_integral_dbm_shift`, `:478`): the GUE functional at `E₀` is the `gueP`-average of the DBM functional
of `vGUE` at energy `0`, time `1 - e^{-t*}` (GUE analogue of `step1Band_integral_ouP`): the merged
`Step1Cond_gueMatPairing_eq_integral` at `t = t* ≥ 0`, then the energy shift. -/
theorem guetranslation_integral_gue :
    ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (τs E₀ : ℝ) (k : ℕ) (O : (Fin k → ℝ) → ℝ), IsTestFun O →
      ∫ ω, kPoint k O E₀ (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues ∂(gueP d (sz.L n) (sz.W n)) =
        ∫ ω, (∫ y, kPoint k O 0 (dbmMat_isHermitian d (sz.L n) (sz.W n) (vGUE sz n τs E₀ ω)
            (1 - Real.exp (-(ouTStar sz τs n))) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n)))
          ∂(gueP d (sz.L n) (sz.W n)) := by
  intro d sz n τs E₀ k O hO
  have hT0 : 0 ≤ ouTStar sz τs n := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [Step1Cond_gueMatPairing_eq_integral d (sz.L n) (sz.W n) hT0 k hO E₀]
  refine integral_congr_ae (Eventually.of_forall fun ω₁ => ?_)
  exact (GUETranslation_integral_dbm_shift d (sz.L n) (sz.W n)
    (fun i => Real.exp (-(ouTStar sz τs n) / 2) * (Xmat_isHermitian d (sz.L n) (sz.W n) ω₁).eigenvalues i)
    (1 - Real.exp (-(ouTStar sz τs n))) E₀ k O).symm

/-! ### 4. The worst-sequence core (target 2a; RBM2D `GUETranslation_core`, `:736`) -/

/-- **Worst-sequence core, at the dilation `ρ_sc(E₀)`** (RBM2D `GUETranslation_core`, `:736`; the model-generic
template is `Step1Band_core`, `Step1Band.lean:719`, with `ρ n = ρ_sc(E₀)` constant): along any sequence `ω n`
eventually in `GUEGoodAt`, `UNL32` applies to `v n = vGUE … (ω n)` at energy `0`, time `1 - e^{-t*}`, with
`δ = σ = min (τ_s/4) ((1-τ_s)/3)`, `q = 1/2`, `c = min κ 1 / 960`, `C = CV = 2`, `g = N^{-1+τ_s/4}`,
`G = N^{-σ}`, `m = mfc_n`, `ρ = ρ'_n` (the choices of the event); the conditional functional at the dilation
`ρ_sc(E₀)` is close to the GUE functional at the dilation `ρ_sc(0)`.  The dilation `ρ'_n → ρ_sc(E₀)` (rate
`N^{-3τ_s/8}`) is removed with `Step1Cond_scaledPairing_lipschitz` and the counts of `UNL32` (a dominating test
function) and of the GUE (`step1Band_gue_count`). -/
private theorem GUETranslation_core_aux (hL32 : UNL32) (hGUE : UNGUELocal) {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d)
    (hsz : Tendsto (fun n => sz.size n) atTop atTop) {κ : ℝ} (hκ : 0 < κ) {τs : ℝ} (h0 : 0 < τs)
    (h1 : τs < 1) {E₀ : ℝ} (hE₀ : |E₀| ≤ 2 - κ) (k : ℕ) {O : (Fin k → ℝ) → ℝ} (hO : IsTestFun O)
    (ω : ∀ n, Ω d (sz.L n) (sz.W n)) (hω : ∀ᶠ n in atTop, GUEGoodAt sz n κ τs E₀ (ω n)) :
    Tendsto (fun n => GUETranslation_F sz τs E₀ n k (fun α => O (rhoSC E₀ • α)) (ω n) -
      ∫ y, kPoint k (fun α => O (rhoSC 0 • α)) 0 (Xmat_isHermitian d (sz.L n) (sz.W n) y).eigenvalues
        ∂(gueP d (sz.L n) (sz.W n))) atTop (𝓝 0) := by
  classical
  set ρ₁ := rhoSC E₀ with hρ₁
  set ρ₀ := rhoSC 0 with hρ₀
  have hρ₁pos : 0 < ρ₁ := rhoSC_pos (lt_of_le_of_lt hE₀ (by linarith))
  have hρ₀pos : 0 < ρ₀ := rhoSC_pos (by norm_num)
  set σ : ℝ := min (τs / 4) ((1 - τs) / 3) with hσ
  have hσpos : 0 < σ := lt_min (by positivity) (by linarith)
  have hc : 0 < min κ 1 / 960 := div_pos (lt_min hκ one_pos) (by norm_num)
  set mr : ℕ → ℝ := fun n => Nsz sz n ^ (-(3 * τs / 8)) with hmr
  have hm0 : Tendsto mr atTop (𝓝 0) := GUETranslation_rpow_tendsto_zero hsz (by linarith)
  have hMr : ∀ n, 0 ≤ mr n := fun n => Real.rpow_nonneg (GUETranslation_Nr_pos hd sz n).le _
  -- the free-convolution data chosen along the sequence
  have hex : ∀ n, ∃ p : (ℂ → ℂ) × ℝ, GUEGoodAt sz n κ τs E₀ (ω n) →
      IsRegular32 (vGUE sz n τs E₀ (ω n)) (Nsz sz n ^ (-1 + τs / 4)) (Nsz sz n ^ (-σ)) (min κ 1 / 960) 2 2 ∧
      IsFreeConv32 (vGUE sz n τs E₀ (ω n)) (1 - Real.exp (-(ouTStar sz τs n))) p.1 ∧
      Tendsto (fun η : ℝ => (p.1 ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 p.2) ∧ |p.2 - ρ₁| ≤ mr n := by
    intro n
    by_cases h : GUEGoodAt sz n κ τs E₀ (ω n)
    · obtain ⟨hreg, mfc, hfc, ρ', ht, hr⟩ := h
      exact ⟨(mfc, ρ'), fun _ => ⟨hreg, hfc, ht, hr⟩⟩
    · exact ⟨(fun _ => 0, 0), fun h' => absurd h' h⟩
  choose p hp using hex
  -- the data fed to `UNL32`
  let v : ∀ n, Idx d (sz.L n) (sz.W n) → ℝ := fun n => vGUE sz n τs E₀ (ω n)
  let tt : ℕ → ℝ := fun n => 1 - Real.exp (-(ouTStar sz τs n))
  let g : ℕ → ℝ := fun n => Nsz sz n ^ (-1 + τs / 4)
  let G : ℕ → ℝ := fun n => Nsz sz n ^ (-σ)
  let mfc : ℕ → ℂ → ℂ := fun n => (p n).1
  let ρs : ℕ → ℝ := fun n => (p n).2
  have hgood : ∀ᶠ n in atTop,
      IsRegular32 (v n) (g n) (G n) (min κ 1 / 960) 2 2 ∧ IsFreeConv32 (v n) (tt n) (mfc n) ∧
      Tendsto (fun η : ℝ => (mfc n ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 (ρs n)) ∧
      |ρs n - ρ₁| ≤ mr n := by
    filter_upwards [hω] with n hn
    exact hp n hn
  have hM2 : ∀ᶠ n in atTop, 2 ≤ Nsz sz n ^ (τs / 2) :=
    ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < τs / 2)).comp
      (GUETranslation_Nr_tendsto hsz)).eventually_ge_atTop 2
  have hprem : ∀ᶠ n in atTop,
      Nsz sz n ^ σ / Nsz sz n ≤ g n ∧ g n ≤ Nsz sz n ^ (-σ) ∧ G n ≤ Nsz sz n ^ (-σ) ∧
      g n * Nsz sz n ^ σ ≤ tt n ∧ tt n ≤ Nsz sz n ^ (-σ) * G n ^ 2 ∧
      |(fun _ : ℕ => (0 : ℝ)) n| ≤ 1 / 2 * G n ∧
      IsRegular32 (v n) (g n) (G n) (min κ 1 / 960) 2 2 ∧ IsFreeConv32 (v n) (tt n) (mfc n) ∧
      Tendsto (fun η : ℝ => (mfc n ⟨(fun _ : ℕ => (0 : ℝ)) n, η⟩).im / Real.pi) (𝓝[>] 0)
        (𝓝 (ρs n)) := by
    filter_upwards [hgood, hM2] with n hn hM2n
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := un_L32_arith (GUETranslation_Nr_ge_one hd sz n) h0 h1 hM2n
    exact ⟨a1, a2, a3, a4, a5, a6, hn.1, hn.2.1, hn.2.2.1⟩
  have hL : ∀ P : (Fin k → ℝ) → ℝ, IsTestFun P →
      Tendsto (fun n =>
        (∫ y, kPoint k (fun β => P (fun j => ρs n * β j)) 0
          (dbmMat_isHermitian d (sz.L n) (sz.W n) (v n) (tt n) y).eigenvalues
            ∂(gueP d (sz.L n) (sz.W n))) -
        ∫ y, kPoint k (fun β => P (fun j => ρ₀ * β j)) 0
          (Xmat_isHermitian d (sz.L n) (sz.W n) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n)))
        atTop (𝓝 0) := fun P hP =>
    hL32 d hd sz hsz σ σ (1 / 2) (min κ 1 / 960) 2 2 hσpos hσpos (by norm_num) (by norm_num) hc
      g G tt (fun _ => 0) v mfc ρs hprem k P hP
  -- the range of `ρs n`
  have hclose : ∀ᶠ n in atTop, mr n < ρ₁ / 2 := hm0.eventually (gt_mem_nhds (by positivity))
  have hrange : ∀ᶠ n in atTop, (ρ₁ / 2 ≤ ρs n ∧ ρs n ≤ ρ₁ + ρ₁ / 2) ∧ |ρs n - ρ₁| ≤ mr n := by
    filter_upwards [hgood, hclose] with n hn hcl
    have h1' : |ρs n - ρ₁| < ρ₁ / 2 := lt_of_le_of_lt hn.2.2.2 hcl
    rw [abs_lt] at h1'
    exact ⟨⟨by linarith [h1'.1], by linarith [h1'.2]⟩, hn.2.2.2⟩
  -- step (i): `UNL32` at `O`
  let A : ℕ → ℝ := fun n => ∫ y, kPoint k (fun β => O (fun j => ρs n * β j)) 0
    (dbmMat_isHermitian d (sz.L n) (sz.W n) (v n) (tt n) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n))
  let gue0 : ℕ → ℝ := fun n => ∫ y, kPoint k (fun β => O (fun j => ρ₀ * β j)) 0
    (Xmat_isHermitian d (sz.L n) (sz.W n) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n))
  have hA : Tendsto (fun n => A n - gue0 n) atTop (𝓝 0) := hL O hO
  -- step (ii): Lipschitz in the scale
  obtain ⟨Q, hQ, hQ0, Clip, hC⟩ := Step1Cond_scaledPairing_lipschitz hO (ρmin := ρ₁ / 2)
    (ρmax := ρ₁ + ρ₁ / 2) (by positivity) (by linarith)
  -- step (iii): domination and the counts
  obtain ⟨Q', hQ', hQ'0, hdom⟩ := Step1Cond_exists_dominating_testFun hQ (ρ₁ / 2) (ρ₁ + ρ₁ / 2)
  have hQ'1 : ∀ᶠ n in atTop,
      (∫ y, kPoint k (fun β => Q' (fun j => ρs n * β j)) 0
          (dbmMat_isHermitian d (sz.L n) (sz.W n) (v n) (tt n) y).eigenvalues
            ∂(gueP d (sz.L n) (sz.W n))) -
        ∫ y, kPoint k (fun β => Q' (fun j => ρ₀ * β j)) 0
          (Xmat_isHermitian d (sz.L n) (sz.W n) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n)) < 1 :=
    (hL Q' hQ').eventually (gt_mem_nhds one_pos)
  obtain ⟨Qa, hQa, hQa0, hQaO⟩ := GUETranslation_exists_abs_dominating hO
  have hGc := step1Band_gue_count hGUE d hd sz hsz τs h0 h1 k
    (fun β => Q' (fun j => ρ₀ * β j)) (GUETranslation_isTestFun_dilate hQ' hρ₀pos.ne')
    (fun β => hQ'0 (fun j => ρ₀ * β j))
  have hGa := step1Band_gue_count hGUE d hd sz hsz τs h0 h1 k
    (fun β => Qa (fun j => ρ₀ * β j)) (GUETranslation_isTestFun_dilate hQa hρ₀pos.ne')
    (fun β => hQa0 (fun j => ρ₀ * β j))
  set W : ℝ := ((ρ₁ / 2)⁻¹) ^ k with hW_def
  have hW0 : 0 < W := by positivity
  set K1 : ℝ := W * |Clip| with hK1_def
  set K2 : ℝ := W * ((k : ℝ) * (ρ₁ + ρ₁ / 2) ^ (k - 1)) with hK2_def
  have hKk : 0 ≤ (k : ℝ) * (ρ₁ + ρ₁ / 2) ^ (k - 1) := by positivity
  have hK2 : 0 ≤ K2 := by rw [hK2_def]; positivity
  set GQ : ℕ → ℝ := fun n => ∫ y, kPoint k (fun β => Q' (fun j => ρ₀ * β j)) 0
    (Xmat_isHermitian d (sz.L n) (sz.W n) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n)) with hGQ
  set Ga : ℕ → ℝ := fun n => ∫ y, kPoint k (fun β => Qa (fun j => ρ₀ * β j)) 0
    (Xmat_isHermitian d (sz.L n) (sz.W n) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n)) with hGa_def
  have hbound : ∀ᶠ n in atTop,
      ‖GUETranslation_F sz τs E₀ n k (fun α => O (ρ₁ • α)) (ω n) - gue0 n‖ ≤
        |A n - gue0 n| * (1 + K2 * mr n) + K1 * (mr n * GQ n + mr n) + K2 * (mr n * Ga n) := by
    filter_upwards [hrange, hQ'1] with n hr hQ'n
    obtain ⟨⟨hr1l, hr1u⟩, hdist⟩ := hr
    have hMrn := hMr n
    have hmeas := GUETranslation_measurable_dbm d (sz.L n) (sz.W n) (v n) (tt n)
    set Hh := dbmMat_isHermitian d (sz.L n) (sz.W n) (v n) (tt n) with hHh
    set X0 := GUETranslation_F sz τs E₀ n k (fun α => O (ρ₁ • α)) (ω n) with hX0
    have hX0' : X0 = ∫ y, kPoint k (fun β => O (fun j => ρ₁ * β j)) 0 (Hh y).eigenvalues
        ∂(gueP d (sz.L n) (sz.W n)) := rfl
    set X1 := A n with hX1
    have hX1' : X1 = ∫ y, kPoint k (fun β => O (fun j => ρs n * β j)) 0 (Hh y).eigenvalues
        ∂(gueP d (sz.L n) (sz.W n)) := rfl
    set g' := gue0 n with hg'
    set D := X1 - g' with hD
    -- the Lipschitz term
    set corrQ := ∫ y, kPoint k Q 0 (Hh y).eigenvalues ∂(gueP d (sz.L n) (sz.W n)) with hcorrQ_def
    have hcorrQ0 : 0 ≤ corrQ := GUETranslation_integral_kPoint_nonneg _ _ _ k hQ0 0
    obtain ⟨BQ, hBQ⟩ := hQ.1.continuous.bounded_above_of_compact_support hQ.2
    obtain ⟨BQ', hBQ'⟩ := hQ'.1.continuous.bounded_above_of_compact_support hQ'.2
    have hcont' : Continuous (fun β : Fin k → ℝ => Q' (fun j => ρs n * β j)) :=
      hQ'.1.continuous.comp (continuous_pi fun j => continuous_const.mul (continuous_apply j))
    have hmono : corrQ ≤ ∫ y, kPoint k (fun β => Q' (fun j => ρs n * β j)) 0
        (Hh y).eigenvalues ∂(gueP d (sz.L n) (sz.W n)) :=
      integral_mono
        (GUETranslation_integrable_kPoint _ hmeas Hh k hQ.1.continuous
          (fun x => by simpa [Real.norm_eq_abs] using hBQ x) 0)
        (GUETranslation_integrable_kPoint _ hmeas Hh k hcont'
          (fun x => by simpa [Real.norm_eq_abs] using hBQ' _) 0)
        (fun y => GUETranslation_kPoint_mono k (fun β => hdom (ρs n) ⟨hr1l, hr1u⟩ β) 0 _)
    have hcorrQ : corrQ ≤ GQ n + 1 := by
      have h2 : GQ n = ∫ y, kPoint k (fun β => Q' (fun j => ρ₀ * β j)) 0
          (Xmat_isHermitian d (sz.L n) (sz.W n) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n)) := rfl
      linarith
    have hlip := hC (gueP d (sz.L n) (sz.W n)) (dbmMat d (sz.L n) (sz.W n) (v n) (tt n)) hmeas Hh 0
      ρ₁ (ρs n) ⟨by linarith, by linarith⟩ ⟨hr1l, hr1u⟩
    rw [← hX0', ← hX1'] at hlip
    have hP1 : |ρ₁ ^ k * X0 - ρs n ^ k * X1| ≤ |Clip| * mr n * corrQ := by
      refine hlip.trans ?_
      calc Clip * |ρ₁ - ρs n| * corrQ ≤ |Clip| * |ρ₁ - ρs n| * corrQ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self Clip)
              (abs_nonneg _)) hcorrQ0
        _ ≤ |Clip| * mr n * corrQ := by
            rw [abs_sub_comm]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdist (abs_nonneg _)) hcorrQ0
    -- `|ρs^k - ρ^k| ≤ k (ρ₁ + ρ₁/2)^{k-1} mr`
    have hP2 : |ρs n ^ k - ρ₁ ^ k| ≤ mr n * ((k : ℝ) * (ρ₁ + ρ₁ / 2) ^ (k - 1)) := by
      have h := _root_.abs_pow_sub_pow_le (a := ρs n) (b := ρ₁) (n := k)
      have hmax : max |ρs n| |ρ₁| ≤ ρ₁ + ρ₁ / 2 := by
        rw [abs_of_pos (by linarith : (0 : ℝ) < ρs n), abs_of_pos hρ₁pos]
        exact max_le hr1u (by linarith)
      have hpow : max |ρs n| |ρ₁| ^ (k - 1) ≤ (ρ₁ + ρ₁ / 2) ^ (k - 1) :=
        pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) hmax _
      refine h.trans ?_
      calc |ρs n - ρ₁| * k * max |ρs n| |ρ₁| ^ (k - 1) ≤ mr n * k * (ρ₁ + ρ₁ / 2) ^ (k - 1) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hdist (Nat.cast_nonneg k)) hpow
              (by positivity) (mul_nonneg hMrn (Nat.cast_nonneg k))
        _ = mr n * ((k : ℝ) * (ρ₁ + ρ₁ / 2) ^ (k - 1)) := by ring
    -- the reference is bounded by a count
    have hT3 : |g'| ≤ Ga n :=
      GUETranslation_abs_integral_le_of_abs_le _ (GUETranslation_measurable_Xmat d _ _)
        (Xmat_isHermitian d (sz.L n) (sz.W n)) k (GUETranslation_isTestFun_dilate hO hρ₀pos.ne')
        (GUETranslation_isTestFun_dilate hQa hρ₀pos.ne') (fun β => hQaO _) 0
    -- assemble
    have hupos : 0 < ρ₁ ^ k := pow_pos hρ₁pos k
    have hwu : (ρ₁ ^ k)⁻¹ ≤ W := by
      rw [hW_def, inv_pow]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) k)
    have hsplit : X0 - X1 = (ρ₁ ^ k)⁻¹ * ((ρ₁ ^ k * X0 - ρs n ^ k * X1) + (ρs n ^ k - ρ₁ ^ k) * X1) := by
      field_simp
      ring
    have hX1b : |X1| ≤ |D| + Ga n := by
      have : X1 = D + g' := by rw [hD]; ring
      rw [this]
      exact (abs_add_le D g').trans (by linarith)
    have hmul : |(ρs n ^ k - ρ₁ ^ k) * X1| ≤ (mr n * ((k : ℝ) * (ρ₁ + ρ₁ / 2) ^ (k - 1))) * (|D| + Ga n) := by
      rw [abs_mul]
      exact mul_le_mul hP2 hX1b (abs_nonneg _) (mul_nonneg hMrn hKk)
    have hdiff : |X0 - X1| ≤ K1 * (mr n * GQ n + mr n) + K2 * (mr n * (|D| + Ga n)) := by
      rw [hsplit, abs_mul, abs_of_pos (inv_pos.mpr hupos)]
      have hin : |(ρ₁ ^ k * X0 - ρs n ^ k * X1) + (ρs n ^ k - ρ₁ ^ k) * X1| ≤
          |Clip| * mr n * (GQ n + 1) + (mr n * ((k : ℝ) * (ρ₁ + ρ₁ / 2) ^ (k - 1))) * (|D| + Ga n) :=
        (abs_add_le _ _).trans (add_le_add (hP1.trans (mul_le_mul_of_nonneg_left hcorrQ
          (mul_nonneg (abs_nonneg _) hMrn))) hmul)
      calc (ρ₁ ^ k)⁻¹ * |(ρ₁ ^ k * X0 - ρs n ^ k * X1) + (ρs n ^ k - ρ₁ ^ k) * X1|
          ≤ W * (|Clip| * mr n * (GQ n + 1) +
              (mr n * ((k : ℝ) * (ρ₁ + ρ₁ / 2) ^ (k - 1))) * (|D| + Ga n)) :=
            mul_le_mul hwu hin (abs_nonneg _) hW0.le
        _ = K1 * (mr n * GQ n + mr n) + K2 * (mr n * (|D| + Ga n)) := by
            rw [hK1_def, hK2_def]; ring
    have hD' : X0 - g' = D + (X0 - X1) := by rw [hD]; ring
    rw [Real.norm_eq_abs, hD']
    have h3 := abs_add_le D (X0 - X1)
    have e : |D| + (K1 * (mr n * GQ n + mr n) + K2 * (mr n * (|D| + Ga n))) =
        |D| * (1 + K2 * mr n) + K1 * (mr n * GQ n + mr n) + K2 * (mr n * Ga n) := by ring
    linarith
  have hU : Tendsto (fun n =>
      |A n - gue0 n| * (1 + K2 * mr n) + K1 * (mr n * GQ n + mr n) + K2 * (mr n * Ga n))
      atTop (𝓝 0) := by
    have h := ((hA.abs.mul ((tendsto_const_nhds (x := (1 : ℝ))).add (hm0.const_mul K2))).add
      ((hGc.add hm0).const_mul K1)).add (hGa.const_mul K2)
    simpa using h
  exact squeeze_zero_norm' hbound hU

/-- **Target 2a** `guetranslation_core` (RBM2D `GUETranslation_core`, `:736`): the core at the test function
`O(ρ_sc(E₀)⁻¹ ·)`: `O(ρ_sc(E₀)⁻¹ · ρ_sc(E₀) ·) = O` is the DBM side, `O(ρ_sc(E₀)⁻¹ ρ_sc(0) ·) =
O((ρ_sc(0)/ρ_sc(E₀)) ·)` the GUE side (`smul_smul`). -/
theorem guetranslation_core :
    UNL32 → UNGUELocal →
      ∀ d : ℕ, 3 ≤ d → ∀ sz : Sizes d, Tendsto (fun n => sz.size n) atTop atTop →
        ∀ κ : ℝ, 0 < κ → ∀ τs : ℝ, 0 < τs → τs < 1 → ∀ E₀ : ℝ, |E₀| ≤ 2 - κ →
          ∀ k : ℕ, ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
            ∀ ω : ∀ n, Ω d (sz.L n) (sz.W n), (∀ᶠ n in atTop, GUEGoodAt sz n κ τs E₀ (ω n)) →
              Tendsto (fun n =>
                (∫ y, kPoint k O 0 (dbmMat_isHermitian d (sz.L n) (sz.W n) (vGUE sz n τs E₀ (ω n))
                    (1 - Real.exp (-(ouTStar sz τs n))) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n))) -
                ∫ y, kPoint k (fun α => O ((rhoSC 0 / rhoSC E₀) • α)) 0
                  (Xmat_isHermitian d (sz.L n) (sz.W n) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n)))
                atTop (𝓝 0) := by
  intro hL32 hGUE d hd sz hsz κ hκ τs h0 h1 E₀ hE₀ k O hO ω hω
  have hρne : rhoSC E₀ ≠ 0 := (rhoSC_pos (lt_of_le_of_lt hE₀ (by linarith))).ne'
  have hO' : IsTestFun (fun β : Fin k → ℝ => O ((rhoSC E₀)⁻¹ • β)) :=
    isTestFun_comp_smul hO (inv_ne_zero hρne)
  have h := GUETranslation_core_aux hL32 hGUE hd sz hsz hκ h0 h1 hE₀ k hO' ω hω
  have e1 : (fun α : Fin k → ℝ => (fun β : Fin k → ℝ => O ((rhoSC E₀)⁻¹ • β)) (rhoSC E₀ • α)) = O := by
    funext α
    simp only [smul_smul, inv_mul_cancel₀ hρne, one_smul]
  have e2 : (fun α : Fin k → ℝ => (fun β : Fin k → ℝ => O ((rhoSC E₀)⁻¹ • β)) (rhoSC 0 • α)) =
      fun α => O ((rhoSC 0 / rhoSC E₀) • α) := by
    funext α
    simp only [smul_smul, div_eq_inv_mul]
  rw [e1, e2] at h
  exact h

/-! ### 5. Uniformity over the good event (target 2b; RBM2D `GUETranslation_uniform`, `:1015`) -/

/-- The good event has a sequence of members (eventually): by `UNGUEGoodHighProb` at `D = 1` its complement has
measure `≤ N^{-1} < 1` for large `n` (`N ≥ 27`), so it is nonempty; the sequence picks a member at each such `n`. -/
private theorem GUETranslation_exists_good_seq (hGood : UNGUEGoodHighProb) (hGUE : UNGUELocal) {d : ℕ}
    (hd : 3 ≤ d) (sz : Sizes d) (hsz : Tendsto (fun n => sz.size n) atTop atTop) {κ : ℝ} (hκ : 0 < κ)
    {τs : ℝ} (h0 : 0 < τs) (h1 : τs < 1) {E₀ : ℝ} (hE₀ : |E₀| ≤ 2 - κ) :
    ∃ b : ∀ n, Ω d (sz.L n) (sz.W n), ∀ᶠ n in atTop, GUEGoodAt sz n κ τs E₀ (b n) := by
  classical
  have hex : ∀ᶠ n in atTop, ∃ ω : Ω d (sz.L n) (sz.W n), GUEGoodAt sz n κ τs E₀ ω := by
    filter_upwards [hGood hGUE d hd sz hsz κ τs E₀ 1 hκ h0 h1 hE₀ one_pos] with n hn
    by_contra hne
    push Not at hne
    have huniv : {ω : Ω d (sz.L n) (sz.W n) | ¬ GUEGoodAt sz n κ τs E₀ ω} = Set.univ :=
      Set.eq_univ_of_forall fun ω => hne ω
    have hN27 := GUETranslation_Nr_ge hd sz n
    have hlt : ENNReal.ofReal (Nsz sz n ^ (-(1 : ℝ))) < 1 := by
      rw [ENNReal.ofReal_lt_one, Real.rpow_neg_one]
      exact inv_lt_one_of_one_lt₀ (by linarith)
    rw [huniv, measure_univ] at hn
    exact absurd hn (not_le.mpr hlt)
  refine ⟨fun n =>
    if h : ∃ ω : Ω d (sz.L n) (sz.W n), GUEGoodAt sz n κ τs E₀ ω then h.choose else fun _ => 0, ?_⟩
  filter_upwards [hex] with n hn
  have hbN : (if h : ∃ ω : Ω d (sz.L n) (sz.W n), GUEGoodAt sz n κ τs E₀ ω then h.choose else fun _ => 0) =
      hn.choose := by simp only [hn, ↓reduceDIte]
  rw [hbN]; exact hn.choose_spec

/-- **Target 2b** `guetranslation_uniform` (RBM2D `GUETranslation_uniform`, `:1015`; RBM1D `Step1GUETranslation.uniform`,
`:845`; worst-sequence argument `step1Band_eventually_forall` on the carrier `Ω d (sz.L n) (sz.W n)`): the core
uniformly on the good event, which is nonempty for large `n` by `UNGUEGoodHighProb` at `D = 1`. -/
theorem guetranslation_uniform :
    UNGUEGoodHighProb → UNL32 → UNGUELocal →
      ∀ d : ℕ, 3 ≤ d → ∀ sz : Sizes d, Tendsto (fun n => sz.size n) atTop atTop →
        ∀ κ : ℝ, 0 < κ → ∀ τs : ℝ, 0 < τs → τs < 1 → ∀ E₀ : ℝ, |E₀| ≤ 2 - κ →
          ∀ k : ℕ, ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O → ∀ ε : ℝ, 0 < ε →
            ∀ᶠ n in atTop, ∀ ω : Ω d (sz.L n) (sz.W n), GUEGoodAt sz n κ τs E₀ ω →
              |(∫ y, kPoint k O 0 (dbmMat_isHermitian d (sz.L n) (sz.W n) (vGUE sz n τs E₀ ω)
                  (1 - Real.exp (-(ouTStar sz τs n))) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n))) -
                ∫ y, kPoint k (fun α => O ((rhoSC 0 / rhoSC E₀) • α)) 0
                  (Xmat_isHermitian d (sz.L n) (sz.W n) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n))| ≤ ε := by
  intro hGood hL32 hGUE d hd sz hsz κ hκ τs h0 h1 E₀ hE₀ k O hO ε hε
  obtain ⟨b, hb1⟩ := GUETranslation_exists_good_seq hGood hGUE hd sz hsz hκ h0 h1 hE₀
  have h := step1Band_eventually_forall (α := fun n => Ω d (sz.L n) (sz.W n))
    (fun n ω => GUEGoodAt sz n κ τs E₀ ω)
    (fun n ω => |(∫ y, kPoint k O 0 (dbmMat_isHermitian d (sz.L n) (sz.W n) (vGUE sz n τs E₀ ω)
        (1 - Real.exp (-(ouTStar sz τs n))) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n))) -
      ∫ y, kPoint k (fun α => O ((rhoSC 0 / rhoSC E₀) • α)) 0
        (Xmat_isHermitian d (sz.L n) (sz.W n) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n))| ≤ ε) b hb1
    (fun f hf => by
      have hc := guetranslation_core hL32 hGUE d hd sz hsz κ hκ τs h0 h1 E₀ hE₀ k O hO f hf
      filter_upwards [Metric.tendsto_nhds.mp hc ε hε] with n hn
      rw [Real.dist_eq, sub_zero] at hn
      exact hn.le)
  filter_upwards [h] with n hn ω hω using hn ω hω

/-! ### 6. The translation (targets 3a, 3b; RBM2D `guetranslationRow`, `:1057`) -/

/-- **Target 3a** `guetranslationRow` (RBM2D `guetranslationRow`, `:1057`; RBM1D `gue_translation'`
`Flow/Step1GUETranslation.lean:966`), internal time `τs = 1/2` (independent of `τ_U`; RBM2D paper-delta #139).  The
good event: `UNGUEGoodHighProb` at `(κ, 1/2, E, D = k + 1)`; the bad event costs `2 sup|O| N^k N^{-k-1} = 2 sup|O| / N`
(`step1Band_abs_integral_kPoint_le`). -/
theorem guetranslationRow : UNGUETranslationRow := by
  intro hGood hL32 hGUE d hd sz hsz k κ hκ E hE O hO
  obtain ⟨BO, hBO⟩ := hO.1.continuous.bounded_above_of_compact_support hO.2
  have hBO' : ∀ x, |O x| ≤ BO := fun x => by simpa [Real.norm_eq_abs] using hBO x
  have hBO0 : 0 ≤ BO := (abs_nonneg _).trans (hBO' 0)
  set K0 : ℝ := 2 * BO with hK0
  have hK00 : 0 ≤ K0 := by positivity
  -- it suffices to show the difference in the order `GUE(E, O) - GUE(0, O(ρ_sc(0)/ρ_sc(E) ·))`
  suffices hmain : Tendsto (fun n =>
      (∫ ω, kPoint k O E (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues
          ∂(gueP d (sz.L n) (sz.W n))) -
      (∫ ω, kPoint k (fun α => O ((rhoSC 0 / rhoSC E) • α)) 0
          (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues ∂(gueP d (sz.L n) (sz.W n))))
      atTop (𝓝 0) by
    have h := hmain.neg
    rw [neg_zero] at h
    exact h.congr fun n => by ring
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hunif := guetranslation_uniform hGood hL32 hGUE d hd sz hsz κ hκ (1 / 2) (by norm_num)
    (by norm_num) E hE k O hO (ε / 2) (half_pos hε)
  have hbadP := hGood hGUE d hd sz hsz κ (1 / 2) E ((k + 1 : ℕ) : ℝ) hκ (by norm_num) (by norm_num) hE
    (by positivity)
  have hsmall : ∀ᶠ n in atTop, K0 / Nsz sz n < ε / 2 :=
    (tendsto_const_nhds.div_atTop (GUETranslation_Nr_tendsto hsz)).eventually
      (gt_mem_nhds (half_pos hε))
  filter_upwards [hunif, hbadP, hsmall] with n hU hB hS
  have hNpos := GUETranslation_Nr_pos hd sz n
  set N : ℝ := Nsz sz n with hN
  rw [Real.dist_eq, sub_zero, guetranslation_integral_gue sz n (1 / 2) E k O hO]
  set c := ∫ y, kPoint k (fun α => O ((rhoSC 0 / rhoSC E) • α)) 0
    (Xmat_isHermitian d (sz.L n) (sz.W n) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n)) with hc_def
  set F : Ω d (sz.L n) (sz.W n) → ℝ := GUETranslation_F sz (1 / 2) E n k O with hF_def
  have hFb : ∀ ω, |F ω| ≤ N ^ k * BO := fun ω => by
    have h := step1Band_abs_integral_kPoint_le (gueP d (sz.L n) (sz.W n)) _
      (dbmMat_isHermitian d (sz.L n) (sz.W n) (vGUE sz n (1 / 2) E ω)
        (1 - Real.exp (-(ouTStar sz (1 / 2) n)))) k (P := O) (B := BO) (fun x => hBO' _) 0
    rwa [GUETranslation_card_real] at h
  have hc : |c| ≤ N ^ k * BO := by
    have h := step1Band_abs_integral_kPoint_le (gueP d (sz.L n) (sz.W n)) (Xmat d (sz.L n) (sz.W n))
      (Xmat_isHermitian d (sz.L n) (sz.W n)) k
      (P := fun α => O ((rhoSC 0 / rhoSC E) • α)) (B := BO) (fun x => hBO' _) 0
    rwa [GUETranslation_card_real] at h
  have hFm : Measurable F := GUETranslation_measurable_F sz (1 / 2) E n k hO.1.continuous
  have hFint : Integrable F (gueP d (sz.L n) (sz.W n)) :=
    Integrable.of_bound hFm.aestronglyMeasurable (N ^ k * BO)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hFb ω)
  have hsplit : ∫ ω, F ω ∂(gueP d (sz.L n) (sz.W n)) - c =
      ∫ ω, (F ω - c) ∂(gueP d (sz.L n) (sz.W n)) := by
    rw [integral_sub hFint (integrable_const c), integral_const, probReal_univ, one_smul]
  change |∫ ω, F ω ∂(gueP d (sz.L n) (sz.W n)) - c| < ε
  rw [hsplit]
  refine abs_integral_le_integral_abs.trans_lt ?_
  set T := toMeasurable (gueP d (sz.L n) (sz.W n)) {ω | ¬ GUEGoodAt sz n κ (1 / 2) E ω} with hT_def
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hsubT : {ω | ¬ GUEGoodAt sz n κ (1 / 2) E ω} ⊆ T := subset_toMeasurable _ _
  set X : ℝ := N ^ k * BO + |c| with hX
  have hX0 : 0 ≤ X := by positivity
  have hpt : ∀ ω, |F ω - c| ≤ ε / 2 + T.indicator (fun _ => X) ω := by
    intro ω
    by_cases hω : GUEGoodAt sz n κ (1 / 2) E ω
    · have h2 : 0 ≤ T.indicator (fun _ => X) ω := Set.indicator_nonneg (fun _ _ => hX0) _
      have h3 : |F ω - c| ≤ ε / 2 := hU ω hω
      linarith
    · rw [Set.indicator_of_mem (hsubT hω)]
      have := abs_sub (F ω) c
      linarith [hFb ω]
  have hint : ∫ ω, |F ω - c| ∂(gueP d (sz.L n) (sz.W n)) ≤
      ε / 2 + (gueP d (sz.L n) (sz.W n)).real T * X := by
    refine (integral_mono_of_nonneg (Eventually.of_forall fun ω => abs_nonneg _)
      ((integrable_const _).add ((integrable_const _).indicator hTm))
      (Eventually.of_forall hpt)).trans ?_
    rw [integral_add (integrable_const _) ((integrable_const _).indicator hTm), integral_const,
      integral_indicator_const _ hTm, probReal_univ, one_smul, smul_eq_mul]
  have hTreal : (gueP d (sz.L n) (sz.W n)).real T ≤ N ^ (-((k + 1 : ℕ) : ℝ)) := by
    rw [measureReal_def, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg hNpos.le _) hB
  have hXle : X ≤ K0 * N ^ k := by
    have e : K0 * N ^ k = N ^ k * BO + N ^ k * BO := by rw [hK0]; ring
    rw [hX, e]; linarith
  have hfinal : (gueP d (sz.L n) (sz.W n)).real T * X ≤ K0 / N := by
    rw [Real.rpow_neg hNpos.le, Real.rpow_natCast] at hTreal
    calc (gueP d (sz.L n) (sz.W n)).real T * X ≤ (N ^ (k + 1))⁻¹ * (K0 * N ^ k) :=
          mul_le_mul hTreal hXle hX0 (by positivity)
      _ = K0 / N := by rw [pow_succ]; field_simp
  linarith

/-- **Target 3b** `guetranslation`: the GUE translation proved (`guetranslationRow gueGoodHighProb`; `gueGoodHighProb`
is UN-11, merged). -/
theorem guetranslation : UNGUETranslation := guetranslationRow gueGoodHighProb

/-! ### 7. The row `UNInfty1Row'` (targets 4a-4c; RBM2D `infty1Row_of_translation`, `:1151`) -/

/-- **Target 4a** `un_infty1Row'_of_translation` (RBM2D `infty1Row_of_translation`, `:1151`): `step1Band_row`
(`E' = 0`, `τ₁ = 𝔠𝔡`) plus `UNGUETranslation` at `κ = (2 - |E'|)/2`, `E := E'`, test function `O(ρ_sc(E') ·)`
(`isTestFun_comp_smul`, `rhoSC_pos`; `ρ_sc(E') • ((ρ_sc(0)/ρ_sc(E')) • α) = ρ_sc(0) • α` by `smul_smul`), added in `ℝ`:
`(model − GUE_0^{dil}) + (GUE_0^{dil} − GUE_{E'}^{dil}) = model − GUE_{E'}^{dil}`.  `UNL32` and `UNGUELocal` are
the hypotheses of the row shape. -/
theorem un_infty1Row'_of_translation : UNGUETranslation → UNInfty1Row' := by
  intro hT h32 hGUE d hd 𝔠 𝔡 sz hA M m E ρ δ hD hTr hCV E' hE' k O hO
  obtain ⟨τ₁, hτ₁, hband⟩ := step1Band_row h32 hGUE d hd 𝔠 𝔡 sz hA M m E ρ δ hD hTr hCV k O hO
  refine ⟨τ₁, hτ₁, fun τU hτU hle => ?_⟩
  have hsz : Tendsto (fun n => sz.size n) atTop atTop := GUETranslation_size_tendsto hA.2.2.1
  have hρ' : 0 < rhoSC E' := rhoSC_pos hE'
  have hO' : IsTestFun (fun α : Fin k → ℝ => O (rhoSC E' • α)) := isTestFun_comp_smul hO hρ'.ne'
  have habs := abs_nonneg E'
  have hlt : |E'| < 2 := hE'
  have hgue := hT h32 hGUE d hd sz hsz k ((2 - |E'|) / 2) (by linarith) E' (by linarith) _ hO'
  have e0 : rhoSC E' * (rhoSC 0 / rhoSC E') = rhoSC 0 := by field_simp
  have e' : ∀ α : Fin k → ℝ, O (rhoSC E' • (rhoSC 0 / rhoSC E') • α) = O (rhoSC 0 • α) := fun α => by
    rw [smul_smul, e0]
  have h := (hband τU hτU hle).add hgue
  rw [add_zero] at h
  unfold UNInfty1
  refine h.congr fun n => ?_
  simp only [e']
  ring

/-- **Target 4b** `un_infty1Row'`: **the owed row, proved** (`UNInfty1Row'`, `PinsDens.lean:88`):
`un_infty1Row'_of_translation guetranslation`.  The pins it takes (`UNL32` borrowed, `UNGUELocal` owed) are hypotheses
inside the row shape; the model-side Step 1 is the merged `step1Band_row` under `UNDens'` (finding T2190a: the
shifted data `unDensShift` are never `UNDens'`). -/
theorem un_infty1Row' : UNInfty1Row' := un_infty1Row'_of_translation guetranslation

/-- **Target 4c** `un_core'_of_univMainRow`: `UNCore'` needs only `UNUnivMainRow` (`un_core_of_rows' un_infty1Row'`,
`PinsDens.lean:220`). -/
theorem un_core'_of_univMainRow : UNUnivMainRow → UNCore' := un_core_of_rows' un_infty1Row'

/-! ### 8. Compiled nonempty instances at `d = 3` (CLAUDE.md §4 step 2; target 5)

The data: `RBM.Gauss.SizesInst.sz0` (`d = 3`; `n = 0`: `L = 4`, `W = 32`, `N = 2097152`), `𝔠 = 1/6`, `𝔡 = 1/10`, the band
model, `m = msc`, `k = 1`, `𝒪 = bump` (`bump 0 = 1`, `bump = 0` at `(3)`), internal time `τs = 1/2`.  `UNL32` (the
external input), `UNGUELocal` and the band, claim and main rows (`UNLocAvgBand`, `UNTrLocalBandRow`, `UNNormBandRow`,
`UNDensBandRow`, `UNClaimAll`, `UNUnivMainRow`, `UNGreenCorrAll`) are other gates' pins and stay hypotheses; every
deterministic hypothesis (`3 ≤ 3`, `Admissible`, `UNDens'`, `|E'| < 2`, `|E| ≤ 2 - κ`, `0 < δ ≤ κ/2`, `IsTestFun bump`,
`size → ∞`) is discharged.  The conclusions are eventual in `n` (the `ln N` thresholds are in the report;
DECISIONS §56); the instances do not use a concrete `n` (except target 1, an identity at `n = 0`). -/

namespace GUETranslationInst

open RBM.Gauss.SizesInst RBM.Univ.UNInst

/-- `inst_dilation_ne_one`: the dilation of the translation at `E = 1` is not `1` (`ρ_sc(0)/ρ_sc(1) = 2/√3`;
from `Step1BandInst.inst_rhoSC_one_lt_zero`). -/
theorem inst_dilation_ne_one : rhoSC 0 / rhoSC 1 ≠ 1 :=
  ((one_lt_div (rhoSC_pos (by norm_num : |(1 : ℝ)| < 2))).2
    Step1BandInst.inst_rhoSC_one_lt_zero).ne'

/-- `inst_guetranslation_sz0`: `guetranslation` at `sz0`, `k = 1`, `κ = 1`, `E = 1`, `O = bump` (target 3b). -/
theorem inst_guetranslation_sz0 :
    UNL32 → UNGUELocal →
      Tendsto (fun n =>
        (∫ ω, kPoint 1 (fun α => (bump : (Fin 1 → ℝ) → ℝ) ((rhoSC 0 / rhoSC 1) • α)) 0
            (Xmat_isHermitian 3 (sz0.L n) (sz0.W n) ω).eigenvalues ∂(gueP 3 (sz0.L n) (sz0.W n))) -
        (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 1
            (Xmat_isHermitian 3 (sz0.L n) (sz0.W n) ω).eigenvalues ∂(gueP 3 (sz0.L n) (sz0.W n))))
        atTop (𝓝 0) :=
  fun h32 hGL => guetranslation h32 hGL 3 le_rfl sz0 Step1RegularityGUEInst.inst_sz0_size_tendsto 1 1 one_pos 1
    (by norm_num) bump bump_testFun

/-- `inst_guetranslationRow_sz0`: `guetranslationRow` at the same data (target 3a); `UNGUEGoodHighProb` is a
hypothesis here. -/
theorem inst_guetranslationRow_sz0 :
    UNGUEGoodHighProb → UNL32 → UNGUELocal →
      Tendsto (fun n =>
        (∫ ω, kPoint 1 (fun α => (bump : (Fin 1 → ℝ) → ℝ) ((rhoSC 0 / rhoSC 1) • α)) 0
            (Xmat_isHermitian 3 (sz0.L n) (sz0.W n) ω).eigenvalues ∂(gueP 3 (sz0.L n) (sz0.W n))) -
        (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 1
            (Xmat_isHermitian 3 (sz0.L n) (sz0.W n) ω).eigenvalues ∂(gueP 3 (sz0.L n) (sz0.W n))))
        atTop (𝓝 0) :=
  fun hG h32 hGL => guetranslationRow hG h32 hGL 3 le_rfl sz0 Step1RegularityGUEInst.inst_sz0_size_tendsto 1 1
    one_pos 1 (by norm_num) bump bump_testFun

/-- `inst_guetranslation_integral_gue_sz0`: target 1 at `sz0`, `n = 0`, `τs = 1/2`, `E₀ = 1`, `k = 1`, `bump`. -/
theorem inst_guetranslation_integral_gue_sz0 :
    ∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 1
        (Xmat_isHermitian 3 (sz0.L 0) (sz0.W 0) ω).eigenvalues ∂(gueP 3 (sz0.L 0) (sz0.W 0)) =
      ∫ ω, (∫ y, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0
          (dbmMat_isHermitian 3 (sz0.L 0) (sz0.W 0) (vGUE sz0 0 (1 / 2) 1 ω)
            (1 - Real.exp (-(ouTStar sz0 (1 / 2) 0))) y).eigenvalues ∂(gueP 3 (sz0.L 0) (sz0.W 0)))
        ∂(gueP 3 (sz0.L 0) (sz0.W 0)) :=
  guetranslation_integral_gue sz0 0 (1 / 2) 1 1 bump bump_testFun

/-- `inst_good_nonempty_sz0`: the good event at `(κ, τs, E₀) = (1, 1/2, 1)` is eventually nonempty at `sz0`
(`gueGoodHighProb` at `D = 1`; `UNGUELocal` a hypothesis), so the quantifier of `guetranslation_uniform` is not
vacuous. -/
theorem inst_good_nonempty_sz0 :
    UNGUELocal → ∀ᶠ n in atTop, ∃ ω : Ω 3 (sz0.L n) (sz0.W n), GUEGoodAt sz0 n 1 (1 / 2) 1 ω := by
  intro hGL
  obtain ⟨b, hb⟩ := GUETranslation_exists_good_seq gueGoodHighProb hGL (d := 3) le_rfl sz0
    Step1RegularityGUEInst.inst_sz0_size_tendsto (κ := (1 : ℝ)) one_pos (τs := (1 / 2 : ℝ)) (by norm_num)
    (by norm_num) (E₀ := (1 : ℝ)) (by norm_num)
  exact hb.mono fun n hn => ⟨b n, hn⟩

/-- `inst_guetranslation_core_sz0`: target 2a at `sz0`: a sequence `ω` in the good event exists
(`inst_good_nonempty_sz0`), and along it the conditional DBM functional of `bump` is asymptotically the GUE
functional of the dilated `bump`. -/
theorem inst_guetranslation_core_sz0 :
    UNL32 → UNGUELocal →
      ∃ ω : ∀ n, Ω 3 (sz0.L n) (sz0.W n), (∀ᶠ n in atTop, GUEGoodAt sz0 n 1 (1 / 2) 1 (ω n)) ∧
        Tendsto (fun n =>
          (∫ y, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0
              (dbmMat_isHermitian 3 (sz0.L n) (sz0.W n) (vGUE sz0 n (1 / 2) 1 (ω n))
                (1 - Real.exp (-(ouTStar sz0 (1 / 2) n))) y).eigenvalues ∂(gueP 3 (sz0.L n) (sz0.W n))) -
          ∫ y, kPoint 1 (fun α => (bump : (Fin 1 → ℝ) → ℝ) ((rhoSC 0 / rhoSC 1) • α)) 0
            (Xmat_isHermitian 3 (sz0.L n) (sz0.W n) y).eigenvalues ∂(gueP 3 (sz0.L n) (sz0.W n)))
          atTop (𝓝 0) := by
  intro h32 hGL
  obtain ⟨b, hb⟩ := GUETranslation_exists_good_seq gueGoodHighProb hGL (d := 3) le_rfl sz0
    Step1RegularityGUEInst.inst_sz0_size_tendsto (κ := (1 : ℝ)) one_pos (τs := (1 / 2 : ℝ)) (by norm_num)
    (by norm_num) (E₀ := (1 : ℝ)) (by norm_num)
  exact ⟨b, hb, guetranslation_core h32 hGL 3 le_rfl sz0 Step1RegularityGUEInst.inst_sz0_size_tendsto 1 one_pos
    (1 / 2) (by norm_num) (by norm_num) 1 (by norm_num) 1 bump bump_testFun b hb⟩

/-- `inst_guetranslation_uniform_sz0`: target 2b at `sz0`, `ε = 1` (`UNGUEGoodHighProb` discharged by
`gueGoodHighProb`). -/
theorem inst_guetranslation_uniform_sz0 :
    UNL32 → UNGUELocal →
      ∀ᶠ n in atTop, ∀ ω : Ω 3 (sz0.L n) (sz0.W n), GUEGoodAt sz0 n 1 (1 / 2) 1 ω →
        |(∫ y, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0
            (dbmMat_isHermitian 3 (sz0.L n) (sz0.W n) (vGUE sz0 n (1 / 2) 1 ω)
              (1 - Real.exp (-(ouTStar sz0 (1 / 2) n))) y).eigenvalues ∂(gueP 3 (sz0.L n) (sz0.W n))) -
          ∫ y, kPoint 1 (fun α => (bump : (Fin 1 → ℝ) → ℝ) ((rhoSC 0 / rhoSC 1) • α)) 0
            (Xmat_isHermitian 3 (sz0.L n) (sz0.W n) y).eigenvalues ∂(gueP 3 (sz0.L n) (sz0.W n))| ≤ 1 :=
  fun h32 hGL => guetranslation_uniform gueGoodHighProb h32 hGL 3 le_rfl sz0
    Step1RegularityGUEInst.inst_sz0_size_tendsto 1 one_pos (1 / 2) (by norm_num) (by norm_num) 1 (by norm_num) 1
    bump bump_testFun 1 one_pos

/-- `inst_un_infty1Row'_of_translation_band_zero`: target 4a at `sz0`, the band model, `msc`, `E = 0`,
`ρ = rhoSC 0`, `δ = 1/2` (`un_dens'_msc_zero`), `E' = 1`, `k = 1`, `bump`; `UNGUETranslation` a hypothesis. -/
theorem inst_un_infty1Row'_of_translation_band_zero :
    UNGUETranslation → UNL32 → UNGUELocal → UNLocAvgBand → UNTrLocalBandRow → UNNormBandRow →
      ∃ τ₁ : ℝ, 0 < τ₁ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₁ →
        UNInfty1 sz0 (UNModel.band sz0) (fun _ => rhoSC 0) 0 1 1 (bump : (Fin 1 → ℝ) → ℝ) τU := by
  intro hT h32 hGL hLoc rT rN
  obtain ⟨CV₀, hCV, hN⟩ := rN 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm
  exact un_infty1Row'_of_translation hT h32 hGL 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm (UNModel.band sz0)
    (fun _ => msc) 0 (fun _ => rhoSC 0) (1 / 2) un_dens'_msc_zero
    (rT hLoc 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm 1 one_pos 0 (by norm_num) (1 / 2) (by norm_num)
      (by norm_num))
    ⟨CV₀, hCV, hN⟩ 1 (by norm_num) 1 bump bump_testFun

/-- `inst_un_infty1Row'_band_zero`: `un_infty1Row'` at `sz0` (`𝔠 = 1/6`, `𝔡 = 1/10`), the band model, `msc`, `E = 0`,
`ρ = rhoSC 0`, `δ = 1/2` (`un_dens'_msc_zero`), the local law from `UNTrLocalBandRow` at `κ = 1`, the norm bound from
`UNNormBandRow`, GUE energy `E' = 1` (the translation is nontrivial: `E' ≠ E`; as `Step1BandInst.inst_step1Band_row_band`,
`Step1Band.lean:1182`). -/
theorem inst_un_infty1Row'_band_zero :
    UNL32 → UNGUELocal → UNLocAvgBand → UNTrLocalBandRow → UNNormBandRow →
      ∃ τ₁ : ℝ, 0 < τ₁ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₁ →
        UNInfty1 sz0 (UNModel.band sz0) (fun _ => rhoSC 0) 0 1 1 (bump : (Fin 1 → ℝ) → ℝ) τU := by
  intro h32 hGL hLoc rT rN
  obtain ⟨CV₀, hCV, hN⟩ := rN 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm
  exact un_infty1Row' h32 hGL 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm (UNModel.band sz0)
    (fun _ => msc) 0 (fun _ => rhoSC 0) (1 / 2) un_dens'_msc_zero
    (rT hLoc 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm 1 one_pos 0 (by norm_num) (1 / 2) (by norm_num)
      (by norm_num))
    ⟨CV₀, hCV, hN⟩ 1 (by norm_num) 1 bump bump_testFun

/-- `inst_un_infty1Row'_band_one`: the same at `E = E' = 1` (`κ = 1/2`), `ρ = rhoSC 1`; the density from
`UNDensBandRow` through `unDensBandRow'_of_row` (as `Step1BandInst.inst_step1Band_band_one`, `Step1Band.lean:1163`). -/
theorem inst_un_infty1Row'_band_one :
    UNL32 → UNGUELocal → UNLocAvgBand → UNTrLocalBandRow → UNNormBandRow → UNDensBandRow →
      ∃ τ₁ : ℝ, 0 < τ₁ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₁ →
        UNInfty1 sz0 (UNModel.band sz0) (fun _ => rhoSC 1) 1 1 1 (bump : (Fin 1 → ℝ) → ℝ) τU := by
  intro h32 hGL hLoc rT rN rD
  obtain ⟨CV₀, hCV, hN⟩ := rN 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm
  obtain ⟨δ, hδκ, hD⟩ := unDensBandRow'_of_row rD (1 / 2) (by norm_num) 1 (by norm_num)
  have hδ : 0 < δ := hD.1.1
  exact un_infty1Row' h32 hGL 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm (UNModel.band sz0)
    (fun _ => msc) 1 (fun _ => rhoSC 1) δ hD
    (rT hLoc 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm (1 / 2) (by norm_num) 1 (by norm_num) δ hδ hδκ)
    ⟨CV₀, hCV, hN⟩ 1 (by norm_num) 1 bump bump_testFun

/-- `inst_un_core'_band_zero`: target 4c at `sz0`, the band model, `E = 0`, `E' = 1`, `k = 1`, `bump`: `UNCore'` from
`UNUnivMainRow` alone (`UNGreenCorrAll`, the claim `UNClaimAll`, the band rows and `UNL32`, `UNGUELocal` are other
gates' pins). -/
theorem inst_un_core'_band_zero :
    UNUnivMainRow → UNL32 → UNGUELocal → UNGreenCorrAll → UNLocAvgBand → UNTrLocalBandRow → UNNormBandRow →
      UNClaimAll sz0 (UNModel.band sz0) 0 →
        UNUnivDilAt sz0 (UNModel.band sz0) (fun _ => rhoSC 0) 0 1 1 (bump : (Fin 1 → ℝ) → ℝ) := by
  intro hU h32 hGL hGC hLoc rT rN hCl
  obtain ⟨CV₀, hCV, hN⟩ := rN 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm
  exact un_core'_of_univMainRow hU h32 hGL hGC 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm (UNModel.band sz0)
    (fun _ => msc) 0 (fun _ => rhoSC 0) (1 / 2) un_dens'_msc_zero
    (rT hLoc 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm 1 one_pos 0 (by norm_num) (1 / 2) (by norm_num)
      (by norm_num))
    ⟨CV₀, hCV, hN⟩ hCl 1 (by norm_num) 1 le_rfl bump bump_testFun

end GUETranslationInst


end RBM.Univ

end
