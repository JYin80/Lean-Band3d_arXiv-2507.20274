/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.Step1Good
import RBM3D.Universality.Step1Cond

/-!
# `RBM3D.Universality.Step1Band` (UN-13): Step 1 of `(1infyuniv)` against the GUE at energy `0`

Ticket T2214.  Paper: arXiv:2507.20274, `paper/tex/1_2_Intro_model_result.tex`, the proof of
`Thm: B_Univ` `1_2:566-581` (Step 1: the OU marginal `𝐇_{t*}`, `t* = N^{-1+τ_U}`, against the GUE).

Port of RBM2D `Universality/Step1Band.lean` (commit `c9a24cf`, 1259 lines; read-only) onto the
abstract model `UNModel` with the primed density hypothesis `UNDens'` (finding T2190a: never
`UNDens`), consuming `step1Good'` (UN-12, `Step1Good.lean:757`) as the regularity event,
`integral_kPoint_ouMat_cond` (UN-02b) as the conditioning and the borrowed `UNL32` ([32] Thm 2.2).
The conclusion is the merged `UNInfty1` (`Pins.lean:552`) at the GUE energy `E' = 0`.

Replaced against RBM2D: `seqP d`/`slice` by `M.μ` (the merged conditioning is model-indexed);
`Xmat_isHermitian … ω₁` eigenvalues by `(M.herm n ω).eigenvalues`; `step1Good_highProb … D` by one
call of `step1Good'` at `D = k + 1` (nonemptiness and the bad event); `rhoSC E₀` (density) by the
sequence `ρ n`, whose range `[c/π, C/π]` comes from `UNDens`; `|E| ≤ 2 - κ` dropped;
`min κ 1 / 960`, `C = 2`, `CV = 2` by the constants `c C` of `step1Good'` and `CV₀ + 1`; `L32` by
`UNL32`; `GUELocal` by `UNGUELocal`; `locSC` by `UNTrLocal`, `UNNormBound`; `τU ≤ 𝔠` by
`τU ≤ 𝔠 𝔡`.  `d` enters only through `τU ≤ 𝔠 𝔡` (via `step1Good'`) and the carrier `Idx d L W`;
the `UNL32` premises and the GUE count involve `N`, `τ` only.

Sections: 0 size facts; 1 elementary bounds on `ζ = 1 - e^{-T}`; 2 generic facts on `kPoint`
(target 1a); 3 measurability, counting; 4 the energy shift (target 1b); 5 the diagonal argument
(target 1c); 6 the GUE count (target 1d); 7 the conditional functional (target 2); 8 the
worst-sequence core; 9 uniformity and the assembly (targets 3a, 3b); 10 compiled nonempty
instances (target 4).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal ENNReal

namespace RBM.Univ

/-! ### 0. Size facts -/

private theorem Step1Band_size_ge {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) : 27 ≤ sz.size n := by
  have h3 : 3 ≤ sz.W n * sz.L n :=
    (sz.three_le_L n).trans (Nat.le_mul_of_pos_left _ (sz.W_pos n))
  calc 27 = 3 ^ 3 := by norm_num
    _ ≤ 3 ^ d := Nat.pow_le_pow_right (by norm_num) hd
    _ ≤ (sz.W n * sz.L n) ^ d := Nat.pow_le_pow_left h3 d

private theorem Step1Band_Nr_ge {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) : (27 : ℝ) ≤ Nsz sz n := by
  exact_mod_cast Step1Band_size_ge hd sz n

private theorem Step1Band_Nr_pos {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) : (0 : ℝ) < Nsz sz n := by
  linarith [Step1Band_Nr_ge hd sz n]

private theorem Step1Band_Nr_ge_one {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) : (1 : ℝ) ≤ Nsz sz n := by
  linarith [Step1Band_Nr_ge hd sz n]

private theorem Step1Band_card_real {d : ℕ} (sz : Sizes d) (n : ℕ) :
    (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ) = Nsz sz n := by
  rw [sz.card_Idx]

private theorem Step1Band_Nr_tendsto {d : ℕ} {sz : Sizes d}
    (hsz : Tendsto (fun n => sz.size n) atTop atTop) :
    Tendsto (fun n => Nsz sz n) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp hsz

private theorem Step1Band_size_tendsto {d : ℕ} {sz : Sizes d} (h : sz.SizeTendsto) :
    Tendsto (fun n => sz.size n) atTop atTop :=
  tendsto_natCast_atTop_iff.mp h

private theorem Step1Band_rpow_tendsto_zero {d : ℕ} {sz : Sizes d}
    (hsz : Tendsto (fun n => sz.size n) atTop atTop) {e : ℝ} (he : e < 0) :
    Tendsto (fun n => Nsz sz n ^ e) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (y := -e) (by linarith)).comp (Step1Band_Nr_tendsto hsz)
  simpa [Function.comp_def] using h

/-! ### 1. Elementary bounds on `ζ = 1 - e^{-T}` (RBM2D `:97-112`) -/

private theorem Step1Band_zeta_le (T : ℝ) : 1 - Real.exp (-T) ≤ T := by
  have := Real.add_one_le_exp (-T); linarith

private theorem Step1Band_zeta_nonneg {T : ℝ} (hT : 0 ≤ T) : 0 ≤ 1 - Real.exp (-T) := by
  have : Real.exp (-T) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  linarith

/-! ### 2. Generic facts about `kPoint` -/

/-- `|kPoint k P E λ| ≤ N^k sup|P|`: the prefactor `N^k / descFactorial N k` times at most
`descFactorial N k` embeddings (RBM2D `Step1Band_abs_kPoint_le`, `:118`). -/
private theorem Step1Band_abs_kPoint_le {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
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

private theorem Step1Band_kPoint_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    {P : (Fin k → ℝ) → ℝ} (hP : ∀ x, 0 ≤ P x) (E : ℝ) (lam : ι → ℝ) :
    0 ≤ kPoint k P E lam := by
  unfold kPoint
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun f _ => hP _)

private theorem Step1Band_kPoint_mono {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    {P Q : (Fin k → ℝ) → ℝ} (hPQ : ∀ x, P x ≤ Q x) (E : ℝ) (lam : ι → ℝ) :
    kPoint k P E lam ≤ kPoint k Q E lam := by
  unfold kPoint
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun f _ => hPQ _) (by positivity)

private theorem Step1Band_kPoint_neg {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (P : (Fin k → ℝ) → ℝ) (E : ℝ) (lam : ι → ℝ) :
    kPoint k (fun β => -P β) E lam = -kPoint k P E lam := by
  unfold kPoint
  simp only [Finset.sum_neg_distrib, mul_neg]

/-- Integrability of the `k`-point functional of a measurable Hermitian matrix map. -/
private theorem Step1Band_integrable_kPoint {Ω' : Type*} [MeasurableSpace Ω'] (Pm : Measure Ω')
    [IsFiniteMeasure Pm] {n : Type*} [Fintype n] [DecidableEq n] {Hm : Ω' → Matrix n n ℂ}
    (hm : Measurable Hm) (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ) {O : (Fin k → ℝ) → ℝ}
    (hO : Continuous O) {B : ℝ} (hB : ∀ x, |O x| ≤ B) (E : ℝ) :
    Integrable (fun ω => kPoint k O E (hH ω).eigenvalues) Pm :=
  Integrable.of_bound (measurable_kPoint_eigenvalues Hm hH hm k O hO E).aestronglyMeasurable
    ((Fintype.card n : ℝ) ^ k * B) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact Step1Band_abs_kPoint_le k hB E _)

/-- **Target 1a** `step1Band_abs_integral_kPoint_le`: `|∫ kPoint k P E λ| ≤ N^k sup|P|` (RBM2D
`Step1Band_abs_integral_kPoint_le`, `Universality/Step1Band.lean:170` at `c9a24cf`). -/
theorem step1Band_abs_integral_kPoint_le :
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (Pm : Measure Ω') [IsProbabilityMeasure Pm] {ι : Type} [Fintype ι]
      [DecidableEq ι] (Hm : Ω' → Matrix ι ι ℂ) (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ) {P : (Fin k → ℝ) → ℝ} {B : ℝ},
      (∀ x, |P x| ≤ B) → ∀ E : ℝ,
        |∫ ω, kPoint k P E (hH ω).eigenvalues ∂Pm| ≤ (Fintype.card ι : ℝ) ^ k * B := by
  intro Ω' _ Pm _ ι _ _ Hm hH k P B hB E
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := (Fintype.card ι : ℝ) ^ k * B)
    (Eventually.of_forall fun ω => ?_)).trans ?_
  · rw [Real.norm_eq_abs]; exact Step1Band_abs_kPoint_le k hB E _
  · rw [probReal_univ, mul_one]

private theorem Step1Band_integral_kPoint_nonneg {Ω' : Type*} [MeasurableSpace Ω']
    (Pm : Measure Ω') {n : Type*} [Fintype n] [DecidableEq n] (Hm : Ω' → Matrix n n ℂ)
    (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ) {P : (Fin k → ℝ) → ℝ} (hP : 0 ≤ P) (E : ℝ) :
    0 ≤ ∫ ω, kPoint k P E (hH ω).eigenvalues ∂Pm :=
  integral_nonneg fun _ => Step1Band_kPoint_nonneg k (fun x => hP x) E _

/-- `|∫ kPoint P| ≤ ∫ kPoint Q` when `|P| ≤ Q` pointwise (smooth compactly supported `P`, `Q`). -/
private theorem Step1Band_abs_integral_le_of_abs_le {Ω' : Type*} [MeasurableSpace Ω']
    (Pm : Measure Ω') [IsFiniteMeasure Pm] {n : Type*} [Fintype n] [DecidableEq n]
    {Hm : Ω' → Matrix n n ℂ} (hm : Measurable Hm) (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ)
    {P Q : (Fin k → ℝ) → ℝ} (hP : IsTestFun P) (hQ : IsTestFun Q)
    (hPQ : ∀ β, |P β| ≤ Q β) (E : ℝ) :
    |∫ ω, kPoint k P E (hH ω).eigenvalues ∂Pm| ≤ ∫ ω, kPoint k Q E (hH ω).eigenvalues ∂Pm := by
  obtain ⟨BP, hBP⟩ := hP.1.continuous.bounded_above_of_compact_support hP.2
  obtain ⟨BQ, hBQ⟩ := hQ.1.continuous.bounded_above_of_compact_support hQ.2
  have hBP' : ∀ x, |P x| ≤ BP := fun x => by simpa [Real.norm_eq_abs] using hBP x
  have hBQ' : ∀ x, |Q x| ≤ BQ := fun x => by simpa [Real.norm_eq_abs] using hBQ x
  have hIP := Step1Band_integrable_kPoint Pm hm hH k hP.1.continuous hBP' E
  have hIQ := Step1Band_integrable_kPoint Pm hm hH k hQ.1.continuous hBQ' E
  have hBPn : ∀ x, |(fun β => -P β) x| ≤ BP := fun x => by simpa using hBP' x
  have hIPn := Step1Band_integrable_kPoint Pm hm hH k hP.1.neg.continuous hBPn E
  have h1 : ∫ ω, kPoint k P E (hH ω).eigenvalues ∂Pm ≤
      ∫ ω, kPoint k Q E (hH ω).eigenvalues ∂Pm :=
    integral_mono hIP hIQ fun ω =>
      Step1Band_kPoint_mono k (fun β => (le_abs_self _).trans (hPQ β)) E _
  have h2 : ∫ ω, kPoint k (fun β => -P β) E (hH ω).eigenvalues ∂Pm ≤
      ∫ ω, kPoint k Q E (hH ω).eigenvalues ∂Pm :=
    integral_mono hIPn hIQ fun ω =>
      Step1Band_kPoint_mono k (fun β => (neg_le_abs _).trans (hPQ β)) E _
  have h3 : ∫ ω, kPoint k (fun β => -P β) E (hH ω).eigenvalues ∂Pm =
      -∫ ω, kPoint k P E (hH ω).eigenvalues ∂Pm := by
    simp only [Step1Band_kPoint_neg, integral_neg]
  rw [h3] at h2
  exact abs_le.mpr ⟨by linarith, h1⟩

/-- A dilate of a test function is a test function (`isTestFun_comp_smul`, written as `fun j => a * β j`). -/
private theorem Step1Band_isTestFun_dilate {k : ℕ} {O : (Fin k → ℝ) → ℝ} (hO : IsTestFun O) {a : ℝ}
    (ha : a ≠ 0) : IsTestFun (fun β : Fin k → ℝ => O (fun j => a * β j)) :=
  isTestFun_comp_smul hO ha

/-- A nonnegative test function dominating `|O|`. -/
private theorem Step1Band_exists_abs_dominating {k : ℕ} {O : (Fin k → ℝ) → ℝ} (hO : IsTestFun O) :
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

/-! ### 3. Measurability, counting, the Stieltjes transform -/

private theorem Step1Band_measurable_Xmat (d L W : ℕ) [NeZero L] [NeZero W] :
    Measurable (Xmat d L W) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => measurable_Xentry d L W i j

/-- Measurability of `dbmMat` in the GUE sample. -/
private theorem Step1Band_measurable_dbm (d L W : ℕ) [NeZero L] [NeZero W] (v : Idx d L W → ℝ)
    (t : ℝ) : Measurable (dbmMat d L W v t) := by
  have hcont : Continuous (fun Y : Matrix (Idx d L W) (Idx d L W) ℂ =>
      Matrix.diagonal (fun i => (v i : ℂ)) + Real.sqrt t • Y) := by fun_prop
  exact hcont.measurable.comp (Step1Band_measurable_Xmat d L W)

/-- Measurability of a single eigenvalue along a measurable Hermitian matrix map (Weyl's bound
`eigenvalues₀_abs_sub_le`; the analogous helpers of `EigenMeasurable`/`Step1Cond` are private; RBM2D
`Step1Band_measurable_eigenvalue`, `:268`). -/
private theorem Step1Band_measurable_eigenvalue {Ω' : Type*} [MeasurableSpace Ω'] {n : Type*}
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

/-- **Counting by the Stieltjes transform**: `#{i : |λ_i| ≤ η} ≤ 2 n η Im m(iη)` (RBM2D
`Step1Band_count_le_im`, `:319`). -/
private theorem Step1Band_count_le_im {n : Type*} [Fintype n] (lam : n → ℝ) {η : ℝ}
    (hη : 0 < η) :
    (((Finset.univ : Finset n).filter (fun i => |lam i| ≤ η)).card : ℝ) ≤
      2 * (Fintype.card n : ℝ) * η * (mV lam ⟨0, η⟩).im := by
  have hterm : ∀ i, (((lam i : ℂ) - ⟨0, η⟩)⁻¹).im = η / (lam i ^ 2 + η ^ 2) := by
    intro i
    rw [Complex.inv_im, Complex.normSq_apply]
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.sub_re, Complex.ofReal_re]
    ring
  have him : (mV lam ⟨0, η⟩).im =
      (Fintype.card n : ℝ)⁻¹ * ∑ i, η / (lam i ^ 2 + η ^ 2) := by
    unfold mV
    have hc : ((Fintype.card n : ℂ))⁻¹ = (((Fintype.card n : ℝ))⁻¹ : ℝ) := by simp
    rw [hc, Complex.im_ofReal_mul, Complex.im_sum]
    simp only [hterm]
  set S := (Finset.univ : Finset n).filter (fun i => |lam i| ≤ η) with hS
  have hsum : (S.card : ℝ) / (2 * η) ≤ ∑ i, η / (lam i ^ 2 + η ^ 2) := by
    calc (S.card : ℝ) / (2 * η) = ∑ _i ∈ S, 1 / (2 * η) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ i ∈ S, η / (lam i ^ 2 + η ^ 2) := Finset.sum_le_sum fun i hi => by
          have hi' : |lam i| ≤ η := (Finset.mem_filter.mp hi).2
          have h2 : lam i ^ 2 ≤ η ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hi' 2
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
      _ ≤ ∑ i, η / (lam i ^ 2 + η ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun i _ _ => by positivity)
  rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | hpos
  · have hempty : IsEmpty n := Fintype.card_eq_zero_iff.mp h0
    have : S = ∅ := by
      rw [hS]; exact Finset.eq_empty_of_forall_notMem fun i => (hempty.false i).elim
    simp [this]
  · have hc : (0 : ℝ) < Fintype.card n := by exact_mod_cast hpos
    rw [him]
    have e : 2 * (Fintype.card n : ℝ) * η * ((Fintype.card n : ℝ)⁻¹ *
        ∑ i, η / (lam i ^ 2 + η ^ 2)) = 2 * η * ∑ i, η / (lam i ^ 2 + η ^ 2) := by
      field_simp
    rw [e]
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * η)).mp hsum
    linarith

/-! ### 4. The energy shift (target 1b): eigenvalues of `A - c` are those of `A` shifted, up to a permutation -/

/-- Two finite families with the same multiset of values differ by a permutation of the index. -/
private theorem Step1Band_exists_perm {ι : Type*} [Fintype ι] {f g : ι → ℝ}
    (h : Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val) :
    ∃ σ : Equiv.Perm ι, ∀ i, g (σ i) = f i := by
  classical
  have hc : ∀ x : ℝ, (Finset.univ.filter (fun i => f i = x)).card =
      (Finset.univ.filter (fun i => g i = x)).card := by
    intro x
    have h1 := congrArg (Multiset.count x) h
    simpa [Multiset.count_map, Finset.card_def, Finset.filter_val, eq_comm] using h1
  let e : ∀ x : ℝ, {i // f i = x} ≃ {i // g i = x} := fun x =>
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype, Fintype.card_subtype]; exact hc x)
  exact ⟨Equiv.ofFiberEquiv e, fun i => Equiv.ofFiberEquiv_map e i⟩

/-- The eigenvalues of `A - c·1` are those of `A` minus `c`, up to a permutation of the index
(RBM2D `Step1Band_eigenvalues_shift`, `:378`). -/
private theorem Step1Band_eigenvalues_shift {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℝ)
    (hB : (A - (c : ℂ) • (1 : Matrix ι ι ℂ)).IsHermitian) :
    ∃ σ : Equiv.Perm ι, ∀ i, hA.eigenvalues (σ i) - c = hB.eigenvalues i := by
  have h1 : (A - (c : ℂ) • (1 : Matrix ι ι ℂ)).charpoly =
      A.charpoly.comp (Polynomial.X + Polynomial.C (c : ℂ)) := by
    have := Matrix.charpoly_sub_scalar A (c : ℂ)
    rw [Matrix.scalar_apply] at this
    rw [Matrix.smul_one_eq_diagonal]
    exact this
  have h2 : (A - (c : ℂ) • (1 : Matrix ι ι ℂ)).charpoly.roots =
      Multiset.map (fun i => ((hA.eigenvalues i - c : ℝ) : ℂ)) Finset.univ.val := by
    rw [h1]
    have h3 := Polynomial.roots_comp_C_mul_X_add_C A.charpoly 1 (c : ℂ) isUnit_one
    rw [Polynomial.C_1, one_mul] at h3
    rw [h3, hA.roots_charpoly_eq_eigenvalues, Multiset.map_map]
    refine Multiset.map_congr rfl fun i _ => ?_
    simp [Ring.inverse_one]
  have h4 : Multiset.map hB.eigenvalues Finset.univ.val =
      Multiset.map (fun i => hA.eigenvalues i - c) Finset.univ.val := by
    have h5 := hB.roots_charpoly_eq_eigenvalues
    rw [h2] at h5
    have h6 := congrArg (Multiset.map Complex.re) h5
    simp only [Multiset.map_map] at h6
    simpa [Function.comp_def] using h6.symm
  exact Step1Band_exists_perm h4

/-- `kPoint` is invariant under a permutation of the eigenvalue labels (RBM2D `Step1Band_kPoint_perm`,
`:406`). -/
private theorem Step1Band_kPoint_perm {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι)
    (k : ℕ) (O : (Fin k → ℝ) → ℝ) (E : ℝ) (lam : ι → ℝ) :
    kPoint k O E (fun i => lam (σ i)) = kPoint k O E lam := by
  let e : (Fin k ↪ ι) ≃ (Fin k ↪ ι) :=
    { toFun := fun f => f.trans σ.toEmbedding
      invFun := fun f => f.trans σ.symm.toEmbedding
      left_inv := fun f => by ext j; simp
      right_inv := fun f => by ext j; simp }
  unfold kPoint
  congr 1
  exact Fintype.sum_equiv e _ _ (fun f => rfl)

/-- **Target 1b** `step1Band_kPoint_shift`: the energy shift `kPoint k O 0 λ(A - c) = kPoint k O c λ(A)`
(RBM2D `Step1Band_kPoint_shift`, `:419`). -/
theorem step1Band_kPoint_shift :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (c : ℝ),
      B = A - (c : ℂ) • (1 : Matrix ι ι ℂ) → ∀ (k : ℕ) (O : (Fin k → ℝ) → ℝ),
        kPoint k O 0 hB.eigenvalues = kPoint k O c hA.eigenvalues := by
  intro ι _ _ A B hA hB c hBA k O
  subst hBA
  obtain ⟨σ, hσ⟩ := Step1Band_eigenvalues_shift hA c hB
  rw [← Step1Band_kPoint_perm σ k O c hA.eigenvalues]
  unfold kPoint
  congr 1
  refine Finset.sum_congr rfl fun f _ => ?_
  congr 1
  funext j
  rw [← hσ (f j)]
  ring

/-! ### 5. The diagonal argument (target 1c) -/

/-- **Target 1c** `step1Band_eventually_forall`: the worst-sequence (diagonal) argument for a carrier that
may depend on `n` (RBM2D `Step1Band_eventually_forall`, `:999`, constant carrier, from RBM1D
`RBM.eventually_forall_of_forall_sequences` with the trivial condition `A0 := True`). -/
theorem step1Band_eventually_forall :
    ∀ {α : ℕ → Type} (A P : ∀ n, α n → Prop) (b : ∀ n, α n),
      (∀ᶠ n in atTop, A n (b n)) →
      (∀ f : ∀ n, α n, (∀ᶠ n in atTop, A n (f n)) → ∀ᶠ n in atTop, P n (f n)) →
      ∀ᶠ n in atTop, ∀ z : α n, A n z → P n z := by
  intro α A P b hb hseq
  classical
  by_contra hnot
  rw [Filter.not_eventually] at hnot
  let bad (n : ℕ) : Prop := ∃ z, A n z ∧ ¬ P n z
  have hbad : ∃ᶠ n : ℕ in atTop, bad n :=
    hnot.mono fun n hn => by
      simp only [not_forall] at hn
      obtain ⟨z, ha1, hp⟩ := hn
      exact ⟨z, ha1, hp⟩
  let f (n : ℕ) : α n := if hn : bad n then hn.choose else b n
  have hf1 : ∀ᶠ n : ℕ in atTop, A n (f n) := by
    filter_upwards [hb] with n hbn
    by_cases hn : bad n
    · simpa [f, hn] using (hn.choose_spec : A n hn.choose ∧ ¬ P n hn.choose).1
    · simpa [f, hn] using hbn
  have hfP := hseq f hf1
  obtain ⟨n, hn, hp⟩ := (hbad.and_eventually hfP).exists
  have hfn : f n = hn.choose := by simp [f, hn]
  exact (hn.choose_spec : A n hn.choose ∧ ¬ P n hn.choose).2 (hfn ▸ hp)

/-! ### 6. The GUE count at scale `N^{-1+a}` (target 1d, from `UNGUELocal`) -/

/-- **Target 1d** `step1Band_gue_count` (RBM2D `Step1Band_gue_count`, `:466`; RBM1D `Step1BandNorm.gue_count`):
for a nonnegative test function `Q`, `N^{-3τ_s/8} · ∫ kPoint k Q 0 (λ(GUE)) → 0`.  The functional is bounded by
`E[#{i : |λ_i| ≤ R/N}^k]`; on the `UNGUELocal` good event at `z = i N^{-1+a}`, `a = τ_s/(8(k+1))`,
`τ_G = a/2` (so that `N^{τ_G}/√(N Im z) = 1`), one has `‖m_N - m_sc‖ ≤ 1`, `Im m_N ≤ 2` and the count is
`≤ 4 N^a`; the bad event costs `N^k N^{-(k+1)} ≤ 1`.  Slack: `3τ_s/8 - k a > τ_s/4`.  Only `N` enters. -/
theorem step1Band_gue_count :
    UNGUELocal → ∀ d : ℕ, 3 ≤ d → ∀ sz : Sizes d, Tendsto (fun n => sz.size n) atTop atTop →
      ∀ τs : ℝ, 0 < τs → τs < 1 → ∀ (k : ℕ) (Q : (Fin k → ℝ) → ℝ), IsTestFun Q → 0 ≤ Q →
        Tendsto (fun n => Nsz sz n ^ (-(3 * τs / 8)) *
          ∫ ω, kPoint k Q 0 (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues ∂(gueP d (sz.L n) (sz.W n)))
          atTop (𝓝 0) := by
  intro hGUE d hd sz hsz τs h0 h1 k Q hQ hQ0
  obtain ⟨B, R, hB, hR, hQR⟩ := Step1Cond_exists_le_indicator hQ
  set a : ℝ := τs / (8 * ((k : ℝ) + 1)) with ha_def
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have ha : 0 < a := by rw [ha_def]; positivity
  have ha1 : a ≤ 1 := by
    rw [ha_def, div_le_one (by positivity)]
    have : (1 : ℝ) ≤ 8 * ((k : ℝ) + 1) := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    linarith
  have hka : a * k + -(3 * τs / 8) < 0 := by
    rw [ha_def]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have : τs / (8 * ((k : ℝ) + 1)) * k ≤ τs / 8 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have hr : -(3 * τs / 8) < 0 := by linarith
  have hGN := hGUE d hd sz hsz 1 (a / 2) ((k + 1 : ℕ) : ℝ) one_pos (by positivity) (by positivity)
  have hNr := Step1Band_Nr_tendsto hsz
  have hRM : ∀ᶠ n in atTop, R ≤ Nsz sz n ^ a :=
    ((tendsto_rpow_atTop ha).comp hNr).eventually_ge_atTop R
  have hkM : ∀ᶠ n in atTop, 2 * (k : ℝ) + 1 ≤ Nsz sz n :=
    hNr.eventually_ge_atTop _
  have hbound : ∀ᶠ n in atTop,
      ∫ ω, kPoint k Q 0 (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues
          ∂(gueP d (sz.L n) (sz.W n)) ≤
        B * 2 ^ k * ((4 * Nsz sz n ^ a) ^ k + 1) := by
    filter_upwards [hGN, hRM, hkM] with n hGb hRMn hkMn
    have hNpos := Step1Band_Nr_pos hd sz n
    have hN1 := Step1Band_Nr_ge_one hd sz n
    have hcard := Step1Band_card_real sz n
    set N : ℝ := Nsz sz n with hN_def
    have hk : k < Fintype.card (Idx d (sz.L n) (sz.W n)) := by
      have : (k : ℝ) < (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ) := by rw [hcard]; linarith
      exact_mod_cast this
    have h1 := Step1Cond_corrPairing_le_count_smul (gueP d (sz.L n) (sz.W n))
      (Xmat d (sz.L n) (sz.W n)) (Step1Band_measurable_Xmat d _ _)
      (Xmat_isHermitian d (sz.L n) (sz.W n)) k hk hQ0 hB hQR 0
    rw [hcard] at h1
    refine h1.trans ?_
    -- the prefactor
    have hMk : (0 : ℝ) < N - k := by linarith
    have hX : (N / (N - k)) ^ k ≤ 2 ^ k := by
      refine pow_le_pow_left₀ (div_nonneg hNpos.le hMk.le) ?_ k
      rw [div_le_iff₀ hMk]; linarith
    -- the count moment
    set η : ℝ := N ^ (-1 + a) with hη_def
    have hηpos : 0 < η := Real.rpow_pos_of_pos hNpos _
    have hNη : N * η = N ^ a := by
      rw [hη_def]
      calc N * N ^ (-1 + a) = N ^ (1 : ℝ) * N ^ (-1 + a) := by rw [Real.rpow_one]
        _ = N ^ ((1 : ℝ) + (-1 + a)) := (Real.rpow_add hNpos _ _).symm
        _ = N ^ a := by congr 1; ring
    have hRη : R / N ≤ η := by
      rw [div_le_iff₀ hNpos, mul_comm, hNη]; exact hRMn
    have hz0 : 0 < (⟨0, η⟩ : ℂ).im := hηpos
    have hsqrt : Real.sqrt (N * η) = N ^ (a / 2) := by
      rw [hNη, Real.sqrt_eq_rpow, ← Real.rpow_mul hNpos.le]
      congr 1; ring
    set bad : Set (Ω d (sz.L n) (sz.W n)) := {ω | ∃ z : ℂ, |z.re| ≤ 2 - 1 ∧
        N ^ (-1 + a / 2) ≤ z.im ∧ z.im ≤ 10 ∧
        N ^ (a / 2) / Real.sqrt (N * z.im) <
          ‖stieltjesN (Xmat d (sz.L n) (sz.W n) ω) z - msc z‖} with hbad
    set T := toMeasurable (gueP d (sz.L n) (sz.W n)) bad with hT_def
    have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
    have hsubT : bad ⊆ T := subset_toMeasurable _ _
    have hμT : gueP d (sz.L n) (sz.W n) T = gueP d (sz.L n) (sz.W n) bad := measure_toMeasurable _
    set cnt : Ω d (sz.L n) (sz.W n) → ℝ := fun ω =>
      (((Finset.univ : Finset (Idx d (sz.L n) (sz.W n))).filter
        (fun i => |(Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues i - 0| ≤ R / N)).card : ℝ)
      with hcnt
    have hcnt0 : ∀ ω, 0 ≤ cnt ω := fun ω => Nat.cast_nonneg _
    have hcntM : ∀ ω, cnt ω ≤ N := fun ω => by
      rw [← hcard]
      have := Finset.card_filter_le (Finset.univ : Finset (Idx d (sz.L n) (sz.W n)))
        (fun i => |(Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues i - 0| ≤ R / N)
      rw [Finset.card_univ] at this
      simp only [hcnt]
      exact_mod_cast this
    have hcntgood : ∀ ω, ω ∉ bad → cnt ω ≤ 4 * N ^ a := by
      intro ω hω
      have hzcond : |(⟨0, η⟩ : ℂ).re| ≤ 2 - 1 ∧ N ^ (-1 + a / 2) ≤ (⟨0, η⟩ : ℂ).im ∧
          (⟨0, η⟩ : ℂ).im ≤ 10 := by
        refine ⟨by simp, ?_, ?_⟩
        · exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
        · have : η ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
          change η ≤ 10
          linarith
      have hle : ‖stieltjesN (Xmat d (sz.L n) (sz.W n) ω) ⟨0, η⟩ - msc ⟨0, η⟩‖ ≤ 1 := by
        by_contra hcon
        push Not at hcon
        refine hω ⟨⟨0, η⟩, hzcond.1, hzcond.2.1, hzcond.2.2, ?_⟩
        change N ^ (a / 2) / Real.sqrt (N * η) < _
        rw [hsqrt, div_self (Real.rpow_pos_of_pos hNpos _).ne']
        exact hcon
      set lam := (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues with hlam
      have hsubset : (Finset.univ : Finset (Idx d (sz.L n) (sz.W n))).filter
          (fun i => |lam i - 0| ≤ R / N) ⊆
          (Finset.univ : Finset (Idx d (sz.L n) (sz.W n))).filter (fun i => |lam i| ≤ η) := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, sub_zero] at hi ⊢
        exact hi.trans hRη
      have hc1 : cnt ω ≤ (((Finset.univ : Finset (Idx d (sz.L n) (sz.W n))).filter
          (fun i => |lam i| ≤ η)).card : ℝ) := by
        simp only [hcnt]
        exact_mod_cast Finset.card_le_card hsubset
      have hc2 := Step1Band_count_le_im lam hηpos
      rw [hcard] at hc2
      have hst : mV lam ⟨0, η⟩ = stieltjesN (Xmat d (sz.L n) (sz.W n) ω) ⟨0, η⟩ :=
        (stieltjesN_eq_mV (Xmat_isHermitian d (sz.L n) (sz.W n) ω) hz0).symm
      rw [hst] at hc2
      have hIm : (stieltjesN (Xmat d (sz.L n) (sz.W n) ω) ⟨0, η⟩).im ≤ 2 := by
        have h1 := Complex.im_le_norm (stieltjesN (Xmat d (sz.L n) (sz.W n) ω) ⟨0, η⟩)
        have h2 := norm_msc_lt_one hz0
        have h3 := norm_le_insert' (stieltjesN (Xmat d (sz.L n) (sz.W n) ω) ⟨0, η⟩) (msc ⟨0, η⟩)
        linarith
      calc cnt ω ≤ 2 * N * η * (stieltjesN (Xmat d (sz.L n) (sz.W n) ω) ⟨0, η⟩).im := hc1.trans hc2
        _ ≤ 2 * N * η * 2 := mul_le_mul_of_nonneg_left hIm (by positivity)
        _ = 4 * N ^ a := by rw [mul_assoc 2 N η, hNη]; ring
    have hg : Integrable (fun ω => (4 * N ^ a) ^ k + T.indicator (fun _ => N ^ k) ω)
        (gueP d (sz.L n) (sz.W n)) :=
      (integrable_const _).add ((integrable_const _).indicator hTm)
    have hpt : ∀ ω, cnt ω ^ k ≤ (4 * N ^ a) ^ k + T.indicator (fun _ => N ^ k) ω := by
      intro ω
      by_cases hω : ω ∈ bad
      · rw [Set.indicator_of_mem (hsubT hω)]
        have : cnt ω ^ k ≤ N ^ k := pow_le_pow_left₀ (hcnt0 ω) (hcntM ω) k
        have : 0 ≤ (4 * N ^ a) ^ k := by positivity
        linarith
      · have h1 : cnt ω ^ k ≤ (4 * N ^ a) ^ k :=
          pow_le_pow_left₀ (hcnt0 ω) (hcntgood ω hω) k
        have h2 : 0 ≤ T.indicator (fun _ => N ^ k) ω :=
          Set.indicator_nonneg (fun _ _ => by positivity) _
        linarith
    have hint : ∫ ω, cnt ω ^ k ∂(gueP d (sz.L n) (sz.W n)) ≤ (4 * N ^ a) ^ k + 1 := by
      refine (integral_mono_of_nonneg (Eventually.of_forall fun ω => pow_nonneg (hcnt0 ω) k) hg
        (Eventually.of_forall hpt)).trans ?_
      rw [integral_add (integrable_const _) ((integrable_const _).indicator hTm),
        integral_const, integral_indicator_const _ hTm, probReal_univ, one_smul, smul_eq_mul]
      have hTreal : (gueP d (sz.L n) (sz.W n)).real T ≤ N ^ (-((k + 1 : ℕ) : ℝ)) := by
        rw [measureReal_def, hμT]
        exact ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg hNpos.le _) hGb
      have hNpow : N ^ (-((k + 1 : ℕ) : ℝ)) * N ^ k ≤ 1 := by
        rw [Real.rpow_neg hNpos.le, Real.rpow_natCast,
          inv_mul_le_iff₀ (by positivity), mul_one]
        exact pow_le_pow_right₀ hN1 (Nat.le_succ k)
      have := mul_le_mul_of_nonneg_right hTreal (pow_nonneg hNpos.le k)
      linarith
    exact mul_le_mul (mul_le_mul_of_nonneg_left hX hB.le) hint
      (integral_nonneg fun ω => pow_nonneg (hcnt0 ω) k) (by positivity)
  -- conclude
  have hlim : Tendsto (fun n => Nsz sz n ^ (-(3 * τs / 8)) *
      (B * 2 ^ k * ((4 * Nsz sz n ^ a) ^ k + 1))) atTop (𝓝 0) := by
    have e : ∀ n, Nsz sz n ^ (-(3 * τs / 8)) *
        (B * 2 ^ k * ((4 * Nsz sz n ^ a) ^ k + 1)) =
        B * 2 ^ k * 4 ^ k * Nsz sz n ^ (a * k + -(3 * τs / 8)) +
          B * 2 ^ k * Nsz sz n ^ (-(3 * τs / 8)) := by
      intro n
      rw [Real.rpow_add (Step1Band_Nr_pos hd sz n), Real.rpow_mul_natCast (Step1Band_Nr_pos hd sz n).le,
        mul_pow]
      ring
    simp_rw [e]
    have hsum := ((Step1Band_rpow_tendsto_zero hsz hka).const_mul (B * 2 ^ k * 4 ^ k)).add
      ((Step1Band_rpow_tendsto_zero hsz hr).const_mul (B * 2 ^ k))
    simpa using hsum
  have hnn : ∀ n, 0 ≤ Nsz sz n ^ (-(3 * τs / 8)) *
      ∫ ω, kPoint k Q 0 (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues
        ∂(gueP d (sz.L n) (sz.W n)) := fun n =>
    mul_nonneg (Real.rpow_nonneg (Step1Band_Nr_pos hd sz n).le _)
      (Step1Band_integral_kPoint_nonneg _ _ _ k hQ0 0)
  have hle : ∀ᶠ n in atTop, Nsz sz n ^ (-(3 * τs / 8)) *
      ∫ ω, kPoint k Q 0 (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues
        ∂(gueP d (sz.L n) (sz.W n)) ≤
        Nsz sz n ^ (-(3 * τs / 8)) *
          (B * 2 ^ k * ((4 * Nsz sz n ^ a) ^ k + 1)) := by
    filter_upwards [hbound] with n hn
    exact mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg (Step1Band_Nr_pos hd sz n).le _)
  exact squeeze_zero' (Eventually.of_forall hnn) hle hlim

/-! ### 7. The conditional functional (target 2) -/

private theorem Step1Band_dbmMat_shift (d L W : ℕ) [NeZero L] [NeZero W] (v : Idx d L W → ℝ)
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
`dbmMat v`, pointwise and hence after integration over the GUE block (RBM2D `_integral_dbm_shift`, `:449`). -/
private theorem Step1Band_integral_dbm_shift (d L W : ℕ) [NeZero L] [NeZero W]
    (v : Idx d L W → ℝ) (t E : ℝ) (k : ℕ) (O : (Fin k → ℝ) → ℝ) :
    ∫ ω, kPoint k O 0 (dbmMat_isHermitian d L W (fun i => v i - E) t ω).eigenvalues
        ∂(gueP d L W) =
      ∫ ω, kPoint k O E (dbmMat_isHermitian d L W v t ω).eigenvalues ∂(gueP d L W) :=
  integral_congr_ae (Eventually.of_forall fun ω =>
    step1Band_kPoint_shift (dbmMat_isHermitian d L W v t ω)
      (dbmMat_isHermitian d L W (fun i => v i - E) t ω) E (Step1Band_dbmMat_shift d L W v t E ω) k O)

/-- **Target 2** `step1Band_integral_ouP` (RBM2D `Step1Band_integral_ouP`, `:711`, without its slice
transfer): the `ouP` functional of `𝐇_{t*}` at `E` is the `M.μ`-average of the DBM functional of
`vOU = e^{-t*/2} λ(H) - E` at energy `0`, time `1 - e^{-t*}` (`integral_kPoint_ouMat_cond` at `t = t*`, then the
shift). -/
theorem step1Band_integral_ouP :
    ∀ {d : ℕ} (sz : Sizes d) (M : UNModel sz) (n : ℕ) (τU E : ℝ) (k : ℕ) (O : (Fin k → ℝ) → ℝ), IsTestFun O →
      ∫ ω, kPoint k O E (ouMat_isHermitian M n (ouTStar sz τU n) ω).eigenvalues ∂(ouP M n) =
        ∫ ω, (∫ y, kPoint k O 0 (dbmMat_isHermitian d (sz.L n) (sz.W n) (vOU sz M n τU E ω)
            (1 - Real.exp (-(ouTStar sz τU n))) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n))) ∂M.μ := by
  intro d sz M n τU E k O hO
  rw [integral_kPoint_ouMat_cond M n (ouTStar sz τU n) k O hO.1.continuous hO.2 E]
  refine integral_congr_ae (Eventually.of_forall fun ω₁ => ?_)
  exact (Step1Band_integral_dbm_shift d (sz.L n) (sz.W n)
    (fun i => Real.exp (-(ouTStar sz τU n) / 2) * (M.herm n ω₁).eigenvalues i)
    (1 - Real.exp (-(ouTStar sz τU n))) E k O).symm

/-- The conditional functional of the first block (the integrand of target 2), for a test function `O`. -/
private def Step1Band_F {d : ℕ} (sz : Sizes d) (M : UNModel sz) (τs E₀ : ℝ) (n k : ℕ)
    (O : (Fin k → ℝ) → ℝ) (ω : Sizes.SeqΩ sz) : ℝ :=
  ∫ y, kPoint k O 0 (dbmMat_isHermitian d (sz.L n) (sz.W n) (vOU sz M n τs E₀ ω)
    (1 - Real.exp (-(ouTStar sz τs n))) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n))

/-- The conditional functional is measurable in the first block (RBM2D `Step1Band_measurable_Hs`, `:681`;
eigenvalues of `M.H n ω` measurable from `M.meas` and `eigenvalues₀_abs_sub_le`). -/
private theorem Step1Band_measurable_F {d : ℕ} (sz : Sizes d) (M : UNModel sz) (τs E₀ : ℝ) (n k : ℕ)
    {O : (Fin k → ℝ) → ℝ} (hO : Continuous O) : Measurable (Step1Band_F sz M τs E₀ n k O) := by
  set t := 1 - Real.exp (-(ouTStar sz τs n)) with ht
  have hHm : Measurable (M.H n) :=
    measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => M.meas n i j
  have heig : Measurable (fun ω : Sizes.SeqΩ sz => fun i => (M.herm n ω).eigenvalues i) :=
    measurable_pi_iff.mpr fun i => Step1Band_measurable_eigenvalue hHm (M.herm n) i
  have hv : Measurable (fun ω : Sizes.SeqΩ sz => vOU sz M n τs E₀ ω) :=
    measurable_pi_iff.mpr fun i => (((measurable_pi_apply i).comp heig).const_mul _).sub_const _
  have hGc : Continuous (fun q : (Idx d (sz.L n) (sz.W n) → ℝ) × Matrix (Idx d (sz.L n) (sz.W n))
      (Idx d (sz.L n) (sz.W n)) ℂ => Matrix.diagonal (fun i => (q.1 i : ℂ)) + Real.sqrt t • q.2) := by
    refine Continuous.add ?_ (continuous_snd.const_smul (Real.sqrt t))
    exact Continuous.matrix_diagonal (continuous_pi fun i =>
      Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_fst))
  have hm0 : Measurable (fun p : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n) =>
      ((vOU sz M n τs E₀ p.1, Xmat d (sz.L n) (sz.W n) p.2) :
        (Idx d (sz.L n) (sz.W n) → ℝ) × Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) :=
    (hv.comp measurable_fst).prodMk ((Step1Band_measurable_Xmat d _ _).comp measurable_snd)
  have hmeq : (fun p : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n) =>
      dbmMat d (sz.L n) (sz.W n) (vOU sz M n τs E₀ p.1) t p.2) =
      (fun q : (Idx d (sz.L n) (sz.W n) → ℝ) × Matrix (Idx d (sz.L n) (sz.W n))
      (Idx d (sz.L n) (sz.W n)) ℂ => Matrix.diagonal (fun i => (q.1 i : ℂ)) + Real.sqrt t • q.2) ∘
      (fun p : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n) =>
      ((vOU sz M n τs E₀ p.1, Xmat d (sz.L n) (sz.W n) p.2) :
        (Idx d (sz.L n) (sz.W n) → ℝ) × Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) := by
    funext p
    simp only [Function.comp_apply, dbmMat]
  have hm : Measurable (fun p : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n) =>
      dbmMat d (sz.L n) (sz.W n) (vOU sz M n τs E₀ p.1) t p.2) := by
    rw [hmeq]; exact hGc.measurable.comp hm0
  have hf := measurable_kPoint_eigenvalues
    (fun p : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n) =>
      dbmMat d (sz.L n) (sz.W n) (vOU sz M n τs E₀ p.1) t p.2)
    (fun p => dbmMat_isHermitian d (sz.L n) (sz.W n) (vOU sz M n τs E₀ p.1) t p.2)
    hm k O hO 0
  exact (hf.stronglyMeasurable.integral_prod_right' (ν := gueP d (sz.L n) (sz.W n))).measurable

/-! ### 8. The worst-sequence core: `UNL32` along one sequence in the good event -/

/-- The good event of `step1Good'` (its complement is the bad event of `UNStep1Good'`, `PinsDens.lean:73`). -/
private def Step1Band_good {d : ℕ} (sz : Sizes d) (M : UNModel sz) (ρ : ℕ → ℝ) (c C CV₀ τs E : ℝ)
    (n : ℕ) : Set (Sizes.SeqΩ sz) :=
  {ω | IsRegular32 (vOU sz M n τs E ω) (Nsz sz n ^ (-1 + τs / 4))
        (Nsz sz n ^ (-(min (τs / 4) ((1 - τs) / 3)))) c C (CV₀ + 1) ∧
      ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOU sz M n τs E ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧
        ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
          |ρ' - ρ n| ≤ Nsz sz n ^ (-(3 * τs / 8))}

/-- **Worst-sequence core** (RBM2D `Step1Band_core`, `:747`; RBM1D `Step1BandNorm.core`): along any sequence
`ω n` eventually in the good event, `UNL32` applies to `v n = vOU … (ω n)` at energy `0`, time
`1 - e^{-t*}`, with `δ = σ = min (τ_s/4) ((1-τ_s)/3)`, `q = 1/2`, `c C` of the event, `CV = CV₀ + 1`,
`g = N^{-1+τ_s/4}`, `G = N^{-σ}`, `m = mfc_n`, `ρ = ρ'_n` (the choices of the event); the conditional functional
at the dilation `ρ_n` is close to the GUE functional at the dilation `ρ_sc(0)`.  The density `ρ_n` enters through
its range `[a0, b0]` only; the dilation `ρ'_n → ρ_n` (rate `N^{-3τ_s/8}`) is removed with
`Step1Cond_scaledPairing_lipschitz` and the counts of `UNL32` (a dominating test function) and of the GUE
(`step1Band_gue_count`). -/
private theorem Step1Band_core (hL32 : UNL32) (hGUE : UNGUELocal) {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d)
    (hsz : Tendsto (fun n => sz.size n) atTop atTop) (M : UNModel sz) (ρ : ℕ → ℝ) {a0 b0 : ℝ}
    (ha0 : 0 < a0) (hab : a0 ≤ b0) (hρ : ∀ᶠ n in atTop, a0 ≤ ρ n ∧ ρ n ≤ b0) {τs : ℝ} (h0 : 0 < τs)
    (h1 : τs < 1) {CV₀ c C : ℝ} (hc : 0 < c) (E : ℝ) (k : ℕ) {O : (Fin k → ℝ) → ℝ} (hO : IsTestFun O)
    (ω : ℕ → Sizes.SeqΩ sz) (hω : ∀ᶠ n in atTop, ω n ∈ Step1Band_good sz M ρ c C CV₀ τs E n) :
    Tendsto (fun n => Step1Band_F sz M τs E n k (fun α => O (ρ n • α)) (ω n) -
      ∫ y, kPoint k (fun α => O (rhoSC 0 • α)) 0 (Xmat_isHermitian d (sz.L n) (sz.W n) y).eigenvalues
        ∂(gueP d (sz.L n) (sz.W n))) atTop (𝓝 0) := by
  classical
  set ρ₀ := rhoSC 0 with hρ₀
  have hρ₀pos : 0 < ρ₀ := rhoSC_pos (by norm_num)
  set σ : ℝ := min (τs / 4) ((1 - τs) / 3) with hσ
  have hσpos : 0 < σ := lt_min (by positivity) (by linarith)
  set mr : ℕ → ℝ := fun n => Nsz sz n ^ (-(3 * τs / 8)) with hmr
  have hm0 : Tendsto mr atTop (𝓝 0) := Step1Band_rpow_tendsto_zero hsz (by linarith)
  have hMr : ∀ n, 0 ≤ mr n := fun n => Real.rpow_nonneg (Step1Band_Nr_pos hd sz n).le _
  -- the free-convolution data chosen along the sequence
  have hex : ∀ n, ∃ p : (ℂ → ℂ) × ℝ, ω n ∈ Step1Band_good sz M ρ c C CV₀ τs E n →
      IsRegular32 (vOU sz M n τs E (ω n)) (Nsz sz n ^ (-1 + τs / 4)) (Nsz sz n ^ (-σ)) c C (CV₀ + 1) ∧
      IsFreeConv32 (vOU sz M n τs E (ω n)) (1 - Real.exp (-(ouTStar sz τs n))) p.1 ∧
      Tendsto (fun η : ℝ => (p.1 ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 p.2) ∧ |p.2 - ρ n| ≤ mr n := by
    intro n
    by_cases h : ω n ∈ Step1Band_good sz M ρ c C CV₀ τs E n
    · obtain ⟨hreg, mfc, hfc, ρ', ht, hr⟩ := h
      exact ⟨(mfc, ρ'), fun _ => ⟨hreg, hfc, ht, hr⟩⟩
    · exact ⟨(fun _ => 0, 0), fun h' => absurd h' h⟩
  choose p hp using hex
  -- the data fed to `UNL32`
  let v : ∀ n, Idx d (sz.L n) (sz.W n) → ℝ := fun n => vOU sz M n τs E (ω n)
  let tt : ℕ → ℝ := fun n => 1 - Real.exp (-(ouTStar sz τs n))
  let g : ℕ → ℝ := fun n => Nsz sz n ^ (-1 + τs / 4)
  let G : ℕ → ℝ := fun n => Nsz sz n ^ (-σ)
  let mfc : ℕ → ℂ → ℂ := fun n => (p n).1
  let ρs : ℕ → ℝ := fun n => (p n).2
  have hgood : ∀ᶠ n in atTop,
      IsRegular32 (v n) (g n) (G n) c C (CV₀ + 1) ∧ IsFreeConv32 (v n) (tt n) (mfc n) ∧
      Tendsto (fun η : ℝ => (mfc n ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 (ρs n)) ∧
      |ρs n - ρ n| ≤ mr n := by
    filter_upwards [hω] with n hn
    exact hp n hn
  have hM2 : ∀ᶠ n in atTop, 2 ≤ Nsz sz n ^ (τs / 2) :=
    ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < τs / 2)).comp
      (Step1Band_Nr_tendsto hsz)).eventually_ge_atTop 2
  have hprem : ∀ᶠ n in atTop,
      Nsz sz n ^ σ / Nsz sz n ≤ g n ∧ g n ≤ Nsz sz n ^ (-σ) ∧ G n ≤ Nsz sz n ^ (-σ) ∧
      g n * Nsz sz n ^ σ ≤ tt n ∧ tt n ≤ Nsz sz n ^ (-σ) * G n ^ 2 ∧
      |(fun _ : ℕ => (0 : ℝ)) n| ≤ 1 / 2 * G n ∧
      IsRegular32 (v n) (g n) (G n) c C (CV₀ + 1) ∧ IsFreeConv32 (v n) (tt n) (mfc n) ∧
      Tendsto (fun η : ℝ => (mfc n ⟨(fun _ : ℕ => (0 : ℝ)) n, η⟩).im / Real.pi) (𝓝[>] 0)
        (𝓝 (ρs n)) := by
    filter_upwards [hgood, hM2] with n hn hM2n
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := un_L32_arith (Step1Band_Nr_ge_one hd sz n) h0 h1 hM2n
    exact ⟨a1, a2, a3, a4, a5, a6, hn.1, hn.2.1, hn.2.2.1⟩
  have hL : ∀ P : (Fin k → ℝ) → ℝ, IsTestFun P →
      Tendsto (fun n =>
        (∫ y, kPoint k (fun β => P (fun j => ρs n * β j)) 0
          (dbmMat_isHermitian d (sz.L n) (sz.W n) (v n) (tt n) y).eigenvalues
            ∂(gueP d (sz.L n) (sz.W n))) -
        ∫ y, kPoint k (fun β => P (fun j => ρ₀ * β j)) 0
          (Xmat_isHermitian d (sz.L n) (sz.W n) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n)))
        atTop (𝓝 0) := fun P hP =>
    hL32 d hd sz hsz σ σ (1 / 2) c C (CV₀ + 1) hσpos hσpos (by norm_num) (by norm_num) hc
      g G tt (fun _ => 0) v mfc ρs hprem k P hP
  -- the range of `ρs n` and `ρ n`
  have hclose : ∀ᶠ n in atTop, mr n < a0 / 2 := hm0.eventually (gt_mem_nhds (by positivity))
  have hrange : ∀ᶠ n in atTop, (a0 / 2 ≤ ρs n ∧ ρs n ≤ b0 + a0 / 2) ∧ (a0 ≤ ρ n ∧ ρ n ≤ b0) ∧
      |ρs n - ρ n| ≤ mr n := by
    filter_upwards [hgood, hclose, hρ] with n hn hcl hρn
    have h1' : |ρs n - ρ n| < a0 / 2 := lt_of_le_of_lt hn.2.2.2 hcl
    rw [abs_lt] at h1'
    exact ⟨⟨by linarith [hρn.1], by linarith [hρn.2]⟩, hρn, hn.2.2.2⟩
  -- step (i): `UNL32` at `O`
  let A : ℕ → ℝ := fun n => ∫ y, kPoint k (fun β => O (fun j => ρs n * β j)) 0
    (dbmMat_isHermitian d (sz.L n) (sz.W n) (v n) (tt n) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n))
  let gue0 : ℕ → ℝ := fun n => ∫ y, kPoint k (fun β => O (fun j => ρ₀ * β j)) 0
    (Xmat_isHermitian d (sz.L n) (sz.W n) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n))
  have hA : Tendsto (fun n => A n - gue0 n) atTop (𝓝 0) := hL O hO
  -- step (ii): Lipschitz in the scale
  obtain ⟨Q, hQ, hQ0, Clip, hC⟩ := Step1Cond_scaledPairing_lipschitz hO (ρmin := a0 / 2)
    (ρmax := b0 + a0 / 2) (by positivity) (by linarith)
  -- step (iii): domination and the counts
  obtain ⟨Q', hQ', hQ'0, hdom⟩ := Step1Cond_exists_dominating_testFun hQ (a0 / 2) (b0 + a0 / 2)
  have hQ'1 : ∀ᶠ n in atTop,
      (∫ y, kPoint k (fun β => Q' (fun j => ρs n * β j)) 0
          (dbmMat_isHermitian d (sz.L n) (sz.W n) (v n) (tt n) y).eigenvalues
            ∂(gueP d (sz.L n) (sz.W n))) -
        ∫ y, kPoint k (fun β => Q' (fun j => ρ₀ * β j)) 0
          (Xmat_isHermitian d (sz.L n) (sz.W n) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n)) < 1 :=
    (hL Q' hQ').eventually (gt_mem_nhds one_pos)
  obtain ⟨Qa, hQa, hQa0, hQaO⟩ := Step1Band_exists_abs_dominating hO
  have hGc := step1Band_gue_count hGUE d hd sz hsz τs h0 h1 k
    (fun β => Q' (fun j => ρ₀ * β j)) (Step1Band_isTestFun_dilate hQ' hρ₀pos.ne')
    (fun β => hQ'0 (fun j => ρ₀ * β j))
  have hGa := step1Band_gue_count hGUE d hd sz hsz τs h0 h1 k
    (fun β => Qa (fun j => ρ₀ * β j)) (Step1Band_isTestFun_dilate hQa hρ₀pos.ne')
    (fun β => hQa0 (fun j => ρ₀ * β j))
  set W : ℝ := ((a0 / 2)⁻¹) ^ k with hW_def
  have hW0 : 0 < W := by positivity
  set K1 : ℝ := W * |Clip| with hK1_def
  set K2 : ℝ := W * ((k : ℝ) * (b0 + a0 / 2) ^ (k - 1)) with hK2_def
  have hb0 : 0 < b0 := lt_of_lt_of_le ha0 hab
  have hKk : 0 ≤ (k : ℝ) * (b0 + a0 / 2) ^ (k - 1) := by positivity
  have hK2 : 0 ≤ K2 := by rw [hK2_def]; positivity
  set GQ : ℕ → ℝ := fun n => ∫ y, kPoint k (fun β => Q' (fun j => ρ₀ * β j)) 0
    (Xmat_isHermitian d (sz.L n) (sz.W n) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n)) with hGQ
  set Ga : ℕ → ℝ := fun n => ∫ y, kPoint k (fun β => Qa (fun j => ρ₀ * β j)) 0
    (Xmat_isHermitian d (sz.L n) (sz.W n) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n)) with hGa_def
  have hbound : ∀ᶠ n in atTop,
      ‖Step1Band_F sz M τs E n k (fun α => O (ρ n • α)) (ω n) - gue0 n‖ ≤
        |A n - gue0 n| * (1 + K2 * mr n) + K1 * (mr n * GQ n + mr n) + K2 * (mr n * Ga n) := by
    filter_upwards [hrange, hQ'1] with n hr hQ'n
    obtain ⟨⟨hr1l, hr1u⟩, ⟨hr0l, hr0u⟩, hdist⟩ := hr
    have hMrn := hMr n
    have hmeas := Step1Band_measurable_dbm d (sz.L n) (sz.W n) (v n) (tt n)
    set Hh := dbmMat_isHermitian d (sz.L n) (sz.W n) (v n) (tt n) with hHh
    set X0 := Step1Band_F sz M τs E n k (fun α => O (ρ n • α)) (ω n) with hX0
    have hX0' : X0 = ∫ y, kPoint k (fun β => O (fun j => ρ n * β j)) 0 (Hh y).eigenvalues
        ∂(gueP d (sz.L n) (sz.W n)) := rfl
    set X1 := A n with hX1
    have hX1' : X1 = ∫ y, kPoint k (fun β => O (fun j => ρs n * β j)) 0 (Hh y).eigenvalues
        ∂(gueP d (sz.L n) (sz.W n)) := rfl
    set g' := gue0 n with hg'
    set D := X1 - g' with hD
    -- the Lipschitz term
    set corrQ := ∫ y, kPoint k Q 0 (Hh y).eigenvalues ∂(gueP d (sz.L n) (sz.W n)) with hcorrQ_def
    have hcorrQ0 : 0 ≤ corrQ := Step1Band_integral_kPoint_nonneg _ _ _ k hQ0 0
    obtain ⟨BQ, hBQ⟩ := hQ.1.continuous.bounded_above_of_compact_support hQ.2
    obtain ⟨BQ', hBQ'⟩ := hQ'.1.continuous.bounded_above_of_compact_support hQ'.2
    have hcont' : Continuous (fun β : Fin k → ℝ => Q' (fun j => ρs n * β j)) :=
      hQ'.1.continuous.comp (continuous_pi fun j => continuous_const.mul (continuous_apply j))
    have hmono : corrQ ≤ ∫ y, kPoint k (fun β => Q' (fun j => ρs n * β j)) 0
        (Hh y).eigenvalues ∂(gueP d (sz.L n) (sz.W n)) :=
      integral_mono
        (Step1Band_integrable_kPoint _ hmeas Hh k hQ.1.continuous
          (fun x => by simpa [Real.norm_eq_abs] using hBQ x) 0)
        (Step1Band_integrable_kPoint _ hmeas Hh k hcont'
          (fun x => by simpa [Real.norm_eq_abs] using hBQ' _) 0)
        (fun y => Step1Band_kPoint_mono k (fun β => hdom (ρs n) ⟨hr1l, hr1u⟩ β) 0 _)
    have hcorrQ : corrQ ≤ GQ n + 1 := by
      have h2 : GQ n = ∫ y, kPoint k (fun β => Q' (fun j => ρ₀ * β j)) 0
          (Xmat_isHermitian d (sz.L n) (sz.W n) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n)) := rfl
      linarith
    have hlip := hC (gueP d (sz.L n) (sz.W n)) (dbmMat d (sz.L n) (sz.W n) (v n) (tt n)) hmeas Hh 0
      (ρ n) (ρs n) ⟨by linarith, by linarith⟩ ⟨hr1l, hr1u⟩
    rw [← hX0', ← hX1'] at hlip
    have hP1 : |ρ n ^ k * X0 - ρs n ^ k * X1| ≤ |Clip| * mr n * corrQ := by
      refine hlip.trans ?_
      calc Clip * |ρ n - ρs n| * corrQ ≤ |Clip| * |ρ n - ρs n| * corrQ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self Clip)
              (abs_nonneg _)) hcorrQ0
        _ ≤ |Clip| * mr n * corrQ := by
            rw [abs_sub_comm]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdist (abs_nonneg _)) hcorrQ0
    -- `|ρs^k - ρ^k| ≤ k (b0 + a0/2)^{k-1} mr`
    have hP2 : |ρs n ^ k - ρ n ^ k| ≤ mr n * ((k : ℝ) * (b0 + a0 / 2) ^ (k - 1)) := by
      have h := _root_.abs_pow_sub_pow_le (a := ρs n) (b := ρ n) (n := k)
      have hmax : max |ρs n| |ρ n| ≤ b0 + a0 / 2 := by
        rw [abs_of_pos (by linarith : (0 : ℝ) < ρs n), abs_of_pos (by linarith : (0 : ℝ) < ρ n)]
        exact max_le hr1u (by linarith)
      have hpow : max |ρs n| |ρ n| ^ (k - 1) ≤ (b0 + a0 / 2) ^ (k - 1) :=
        pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) hmax _
      refine h.trans ?_
      calc |ρs n - ρ n| * k * max |ρs n| |ρ n| ^ (k - 1) ≤ mr n * k * (b0 + a0 / 2) ^ (k - 1) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hdist (Nat.cast_nonneg k)) hpow
              (by positivity) (mul_nonneg hMrn (Nat.cast_nonneg k))
        _ = mr n * ((k : ℝ) * (b0 + a0 / 2) ^ (k - 1)) := by ring
    -- the reference is bounded by a count
    have hT3 : |g'| ≤ Ga n :=
      Step1Band_abs_integral_le_of_abs_le _ (Step1Band_measurable_Xmat d _ _)
        (Xmat_isHermitian d (sz.L n) (sz.W n)) k (Step1Band_isTestFun_dilate hO hρ₀pos.ne')
        (Step1Band_isTestFun_dilate hQa hρ₀pos.ne') (fun β => hQaO _) 0
    -- assemble
    have hupos : 0 < ρ n ^ k := pow_pos (by linarith) k
    have hwu : (ρ n ^ k)⁻¹ ≤ W := by
      rw [hW_def, inv_pow]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) k)
    have hsplit : X0 - X1 = (ρ n ^ k)⁻¹ * ((ρ n ^ k * X0 - ρs n ^ k * X1) + (ρs n ^ k - ρ n ^ k) * X1) := by
      field_simp
      ring
    have hX1b : |X1| ≤ |D| + Ga n := by
      have : X1 = D + g' := by rw [hD]; ring
      rw [this]
      exact (abs_add_le D g').trans (by linarith)
    have hmul : |(ρs n ^ k - ρ n ^ k) * X1| ≤ (mr n * ((k : ℝ) * (b0 + a0 / 2) ^ (k - 1))) * (|D| + Ga n) := by
      rw [abs_mul]
      exact mul_le_mul hP2 hX1b (abs_nonneg _) (mul_nonneg hMrn hKk)
    have hdiff : |X0 - X1| ≤ K1 * (mr n * GQ n + mr n) + K2 * (mr n * (|D| + Ga n)) := by
      rw [hsplit, abs_mul, abs_of_pos (inv_pos.mpr hupos)]
      have hin : |(ρ n ^ k * X0 - ρs n ^ k * X1) + (ρs n ^ k - ρ n ^ k) * X1| ≤
          |Clip| * mr n * (GQ n + 1) + (mr n * ((k : ℝ) * (b0 + a0 / 2) ^ (k - 1))) * (|D| + Ga n) :=
        (abs_add_le _ _).trans (add_le_add (hP1.trans (mul_le_mul_of_nonneg_left hcorrQ
          (mul_nonneg (abs_nonneg _) hMrn))) hmul)
      calc (ρ n ^ k)⁻¹ * |(ρ n ^ k * X0 - ρs n ^ k * X1) + (ρs n ^ k - ρ n ^ k) * X1|
          ≤ W * (|Clip| * mr n * (GQ n + 1) +
              (mr n * ((k : ℝ) * (b0 + a0 / 2) ^ (k - 1))) * (|D| + Ga n)) :=
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

/-! ### 9. Uniformity over the good event and the assembly (targets 3a, 3b) -/

/-- The range of the density sequence from `UNDens`: eventually `c/π ≤ ρ n ≤ C/π`, and `c ≤ C`. -/
private theorem Step1Band_density_range {m : ℕ → ℂ → ℂ} {E : ℝ} {ρ : ℕ → ℝ} {δ : ℝ}
    (h : UNDens m E ρ δ) :
    ∃ cD CD : ℝ, 0 < cD ∧ cD ≤ CD ∧ ∀ᶠ n in atTop, cD / Real.pi ≤ ρ n ∧ ρ n ≤ CD / Real.pi := by
  obtain ⟨hδ, cD, CD, Lp, hcD, hCD, hLp, hev⟩ := h
  have hcC : cD ≤ CD := by
    obtain ⟨n, hn, -, -⟩ := hev.exists
    have := hn E 1 (by simpa using hδ.le) one_pos (by norm_num)
    exact this.1.trans this.2
  refine ⟨cD, CD, hcD, hcC, ?_⟩
  filter_upwards [hev] with n hn
  obtain ⟨hb, -, hlim⟩ := hn
  have hev0 : ∀ᶠ η : ℝ in 𝓝[>] 0, η ∈ Set.Ioo (0 : ℝ) 10 := Ioo_mem_nhdsGT (by norm_num)
  have hpi : 0 < Real.pi := Real.pi_pos
  constructor
  · refine ge_of_tendsto hlim ?_
    filter_upwards [hev0] with η hη
    have := (hb E η (by simpa using hδ.le) hη.1 hη.2.le).1
    exact div_le_div_of_nonneg_right this hpi.le
  · refine le_of_tendsto hlim ?_
    filter_upwards [hev0] with η hη
    have := (hb E η (by simpa using hδ.le) hη.1 hη.2.le).2
    exact div_le_div_of_nonneg_right this hpi.le

/-- **Uniformity over the good event** (RBM2D `Step1Band_uniform`, `:1025`; worst-sequence argument,
target 1c). -/
private theorem Step1Band_uniform (hL32 : UNL32) (hGUE : UNGUELocal) {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d)
    (hsz : Tendsto (fun n => sz.size n) atTop atTop) (M : UNModel sz) (ρ : ℕ → ℝ) {a0 b0 : ℝ}
    (ha0 : 0 < a0) (hab : a0 ≤ b0) (hρ : ∀ᶠ n in atTop, a0 ≤ ρ n ∧ ρ n ≤ b0) {τs : ℝ} (h0 : 0 < τs)
    (h1 : τs < 1) {CV₀ c C : ℝ} (hc : 0 < c) (E : ℝ) (k : ℕ) {O : (Fin k → ℝ) → ℝ} (hO : IsTestFun O)
    (hbad : ∀ᶠ n in atTop, M.μ (Step1Band_good sz M ρ c C CV₀ τs E n)ᶜ ≤ ENNReal.ofReal (Nsz sz n ^ (-1 : ℝ)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ ω ∈ Step1Band_good sz M ρ c C CV₀ τs E n,
      |Step1Band_F sz M τs E n k (fun α => O (ρ n • α)) ω -
        ∫ y, kPoint k (fun α => O (rhoSC 0 • α)) 0
          (Xmat_isHermitian d (sz.L n) (sz.W n) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n))| ≤ ε := by
  classical
  -- the good event is nonempty for large `n`: its complement has measure `≤ N^{-1} < 1`
  have hex : ∀ᶠ n in atTop, (Step1Band_good sz M ρ c C CV₀ τs E n).Nonempty := by
    filter_upwards [hbad] with n hn
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hN27 := Step1Band_Nr_ge hd sz n
    have hlt : ENNReal.ofReal (Nsz sz n ^ (-1 : ℝ)) < 1 := by
      rw [ENNReal.ofReal_lt_one, Real.rpow_neg_one]
      exact inv_lt_one_of_one_lt₀ (by linarith)
    rw [hne, Set.compl_empty, measure_univ] at hn
    exact absurd hn (not_le.mpr hlt)
  let b : ∀ n : ℕ, Sizes.SeqΩ sz := fun n =>
    if h : (Step1Band_good sz M ρ c C CV₀ τs E n).Nonempty then h.some else fun _ => 0
  have hb1 : ∀ᶠ n in atTop, b n ∈ Step1Band_good sz M ρ c C CV₀ τs E n := by
    filter_upwards [hex] with n hn
    have hbN : b n = hn.some := by simp only [b, hn, ↓reduceDIte]
    rw [hbN]; exact hn.some_mem
  have h := step1Band_eventually_forall (α := fun _ => Sizes.SeqΩ sz)
    (fun n ω => ω ∈ Step1Band_good sz M ρ c C CV₀ τs E n)
    (fun n ω => |Step1Band_F sz M τs E n k (fun α => O (ρ n • α)) ω -
      ∫ y, kPoint k (fun α => O (rhoSC 0 • α)) 0
        (Xmat_isHermitian d (sz.L n) (sz.W n) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n))| ≤ ε) b hb1
    (fun f hf => by
      have hcore := Step1Band_core hL32 hGUE hd sz hsz M ρ ha0 hab hρ h0 h1 hc E k hO f hf
      filter_upwards [Metric.tendsto_nhds.mp hcore ε hε] with n hn
      rw [Real.dist_eq, sub_zero] at hn
      exact hn.le)
  filter_upwards [h] with n hn ω hω using hn ω hω

/-- **Target 3a** `step1Band`: **Step 1 of `(1infyuniv)`, model-generic** (RBM2D `step1Band`, `:1072`; RBM1D
`step1_band'`): for an abstract model with the primed density hypothesis `UNDens'`, the tracial local law
`UNTrLocal` and the norm bound `UNNormBound`, every `0 < τ_U ≤ 𝔠𝔡`, every `k` and every test function, the
`𝐇_{t*}` functional at `E` dilated by `ρ_n` is asymptotically the GUE functional at energy `0` dilated by
`ρ_sc(0)`: `UNInfty1 sz M ρ E 0 k O τU` (`Pins.lean:552`).  RBM2D's `|E| ≤ 2 - κ` is not needed (`UNDens` gives
`ρ_n ∈ [c/π, C/π]`); `τ_U < 1` follows from `un_admissible_cd_lt_half`.  The external input is `UNL32`
([32] Theorem 2.2); `UNGUELocal` is another gate's pin; `step1Good'` (UN-12) supplies the regularity event. -/
theorem step1Band :
    UNL32 → UNGUELocal →
      ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
        ∀ (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
          UNDens' m E ρ δ → UNTrLocal sz M m E δ → (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz M CV₀) →
            ∀ k : ℕ, ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
              ∀ τU : ℝ, 0 < τU → τU ≤ 𝔠 * 𝔡 → UNInfty1 sz M ρ E 0 k O τU := by
  intro hL32 hGUE d hd 𝔠 𝔡 sz hA M m E ρ δ hD hT hCV k O hO τU h0 hτ
  obtain ⟨CV₀, hCV0, hCV⟩ := hCV
  have hd0 : 0 < d := by omega
  have h1 : τU < 1 := by
    have := un_admissible_cd_lt_half sz hd0 hA
    linarith
  have hsz : Tendsto (fun n => sz.size n) atTop atTop := Step1Band_size_tendsto hA.2.2.1
  obtain ⟨cD, CD, hcD, hcC, hρr⟩ := Step1Band_density_range hD.1
  have ha0 : 0 < cD / Real.pi := div_pos hcD Real.pi_pos
  have hab : cD / Real.pi ≤ CD / Real.pi := div_le_div_of_nonneg_right hcC Real.pi_pos.le
  -- the good event: one call at `D = k + 1`
  obtain ⟨c, C, hc, hgood⟩ := step1Good' d hd 𝔠 𝔡 sz hA M m E ρ δ hD hT CV₀ hCV0 hCV τU
    ((k + 1 : ℕ) : ℝ) h0 h1 hτ (by positivity)
  have hbad : ∀ᶠ n in atTop, M.μ (Step1Band_good sz M ρ c C CV₀ τU E n)ᶜ ≤
      ENNReal.ofReal (Nsz sz n ^ (-1 : ℝ)) := by
    filter_upwards [hgood] with n hn
    refine hn.trans (ENNReal.ofReal_le_ofReal ?_)
    exact Real.rpow_le_rpow_of_exponent_le (Step1Band_Nr_ge_one hd sz n) (by
      have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
      linarith)
  obtain ⟨BO, hBO⟩ := hO.1.continuous.bounded_above_of_compact_support hO.2
  have hBO' : ∀ x, |O x| ≤ BO := fun x => by simpa [Real.norm_eq_abs] using hBO x
  have hBO0 : 0 ≤ BO := (abs_nonneg _).trans (hBO' 0)
  set K0 : ℝ := 2 * BO with hK0
  have hK00 : 0 ≤ K0 := by positivity
  unfold UNInfty1
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hunif := Step1Band_uniform hL32 hGUE hd sz hsz M ρ ha0 hab hρr h0 h1 hc E k hO
    (by
      filter_upwards [hgood] with n hn
      refine hn.trans (ENNReal.ofReal_le_ofReal ?_)
      exact Real.rpow_le_rpow_of_exponent_le (Step1Band_Nr_ge_one hd sz n) (by
        have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
        linarith)) (ε / 2) (half_pos hε)
  have hsmall : ∀ᶠ n in atTop, K0 / Nsz sz n < ε / 2 :=
    (tendsto_const_nhds.div_atTop (Step1Band_Nr_tendsto hsz)).eventually
      (gt_mem_nhds (half_pos hε))
  filter_upwards [hunif, hgood, hsmall, hρr] with n hU hB hS hρn
  have hNpos := Step1Band_Nr_pos hd sz n
  have hρne : ρ n ≠ 0 := by
    have := lt_of_lt_of_le ha0 hρn.1
    exact this.ne'
  have hO' : IsTestFun (fun α : Fin k → ℝ => O (ρ n • α)) := isTestFun_comp_smul hO hρne
  set N : ℝ := Nsz sz n with hN
  rw [Real.dist_eq, sub_zero]
  have hcond := step1Band_integral_ouP sz M n τU E k (fun α => O (ρ n • α)) hO'
  rw [hcond]
  set c0 := ∫ y, kPoint k (fun α => O (rhoSC 0 • α)) 0
    (Xmat_isHermitian d (sz.L n) (sz.W n) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n)) with hc_def
  have hFb : ∀ ω, |Step1Band_F sz M τU E n k (fun α => O (ρ n • α)) ω| ≤ N ^ k * BO := fun ω => by
    have h := step1Band_abs_integral_kPoint_le (gueP d (sz.L n) (sz.W n)) _
      (dbmMat_isHermitian d (sz.L n) (sz.W n) (vOU sz M n τU E ω)
        (1 - Real.exp (-(ouTStar sz τU n)))) k (P := fun α => O (ρ n • α)) (B := BO)
      (fun x => hBO' _) 0
    rwa [Step1Band_card_real] at h
  have hc : |c0| ≤ N ^ k * BO := by
    have h := step1Band_abs_integral_kPoint_le (gueP d (sz.L n) (sz.W n)) (Xmat d (sz.L n) (sz.W n))
      (Xmat_isHermitian d (sz.L n) (sz.W n)) k
      (P := fun α => O (rhoSC 0 • α)) (B := BO) (fun x => hBO' _) 0
    rwa [Step1Band_card_real] at h
  have hFm : Measurable (Step1Band_F sz M τU E n k (fun α => O (ρ n • α))) :=
    Step1Band_measurable_F sz M τU E n k hO'.1.continuous
  have hFint : Integrable (Step1Band_F sz M τU E n k (fun α => O (ρ n • α))) M.μ :=
    Integrable.of_bound hFm.aestronglyMeasurable (N ^ k * BO)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hFb ω)
  have hsplit : ∫ ω, Step1Band_F sz M τU E n k (fun α => O (ρ n • α)) ω ∂M.μ - c0 =
      ∫ ω, (Step1Band_F sz M τU E n k (fun α => O (ρ n • α)) ω - c0) ∂M.μ := by
    rw [integral_sub hFint (integrable_const c0), integral_const, probReal_univ, one_smul]
  change |∫ ω, Step1Band_F sz M τU E n k (fun α => O (ρ n • α)) ω ∂M.μ - c0| < ε
  rw [hsplit]
  refine abs_integral_le_integral_abs.trans_lt ?_
  set T := toMeasurable M.μ (Step1Band_good sz M ρ c C CV₀ τU E n)ᶜ with hT_def
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hsubT : (Step1Band_good sz M ρ c C CV₀ τU E n)ᶜ ⊆ T := subset_toMeasurable _ _
  set X : ℝ := N ^ k * BO + |c0| with hX
  have hX0 : 0 ≤ X := by positivity
  have hpt : ∀ ω, |Step1Band_F sz M τU E n k (fun α => O (ρ n • α)) ω - c0| ≤
      ε / 2 + T.indicator (fun _ => X) ω := by
    intro ω
    by_cases hω : ω ∈ Step1Band_good sz M ρ c C CV₀ τU E n
    · have h2 : 0 ≤ T.indicator (fun _ => X) ω := Set.indicator_nonneg (fun _ _ => hX0) _
      linarith [hU ω hω]
    · rw [Set.indicator_of_mem (hsubT hω)]
      have := abs_sub (Step1Band_F sz M τU E n k (fun α => O (ρ n • α)) ω) c0
      linarith [hFb ω]
  have hint : ∫ ω, |Step1Band_F sz M τU E n k (fun α => O (ρ n • α)) ω - c0| ∂M.μ ≤
      ε / 2 + M.μ.real T * X := by
    refine (integral_mono_of_nonneg (Eventually.of_forall fun ω => abs_nonneg _)
      ((integrable_const _).add ((integrable_const _).indicator hTm))
      (Eventually.of_forall hpt)).trans ?_
    rw [integral_add (integrable_const _) ((integrable_const _).indicator hTm), integral_const,
      integral_indicator_const _ hTm, probReal_univ, one_smul, smul_eq_mul]
  have hTreal : M.μ.real T ≤ N ^ (-((k + 1 : ℕ) : ℝ)) := by
    rw [measureReal_def, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg hNpos.le _) hB
  have hXle : X ≤ K0 * N ^ k := by
    have e : K0 * N ^ k = N ^ k * BO + N ^ k * BO := by rw [hK0]; ring
    rw [hX, e]; linarith
  have hfinal : M.μ.real T * X ≤ K0 / N := by
    rw [Real.rpow_neg hNpos.le, Real.rpow_natCast] at hTreal
    calc M.μ.real T * X ≤ (N ^ (k + 1))⁻¹ * (K0 * N ^ k) :=
          mul_le_mul hTreal hXle hX0 (by positivity)
      _ = K0 / N := by rw [pow_succ]; field_simp
  linarith

/-- **Target 3b** `step1Band_row`: the consumer shape for UN-14, `UNInfty1Row'` (`PinsDens.lean:88`) at the GUE
energy `E' = 0` (`|0| < 2`), with `τ₁ = 𝔠𝔡`. -/
theorem step1Band_row :
    UNL32 → UNGUELocal →
      ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
        ∀ (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
          UNDens' m E ρ δ → UNTrLocal sz M m E δ → (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz M CV₀) →
            ∀ k : ℕ, ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
              ∃ τ₁ : ℝ, 0 < τ₁ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₁ → UNInfty1 sz M ρ E 0 k O τU := by
  intro hL32 hGUE d hd 𝔠 𝔡 sz hA M m E ρ δ hD hT hCV k O hO
  exact ⟨𝔠 * 𝔡, mul_pos hA.1 hA.2.1, fun τU h0 hτ =>
    step1Band hL32 hGUE d hd 𝔠 𝔡 sz hA M m E ρ δ hD hT hCV k O hO τU h0 hτ⟩

/-! ### 10. Compiled nonempty instances at `d = 3` (CLAUDE.md §4 step 2; target 4)

The data: `RBM.Gauss.SizesInst.sz0` (`d = 3`; `n = 0`: `L = 4`, `W = 32`, `lam = 1/64`, `N = 2097152`), `𝔠 = 1/6`,
`𝔡 = 1/10`, the band model, `m = msc`, `k = 1`, `𝒪 = bump` (`bump 0 = 1`, `bump = 0` at `(3)`), `τ_U = 1/60 = 𝔠𝔡`.
`UNL32` (the external input), `UNGUELocal` and the band rows `UNLocAvgBand`, `UNTrLocalBandRow`,
`UNNormBandRow`, `UNDensBandRow` are other gates' pins and stay hypotheses; every deterministic hypothesis
(`3 ≤ 3`, `Admissible`, `UNDens'`, `|E| ≤ 2 - κ`, `0 < δ ≤ κ/2`, `0 < τ_U ≤ 𝔠𝔡`, `IsTestFun bump`) is discharged.
The conclusions are eventual in `n` (the size conditions of `step1Good'` hold only for `N ≳ e^{2290}` at these
constants: the instances do not use a concrete `n`; DECISIONS §56). -/

namespace Step1BandInst

open RBM.Gauss.SizesInst RBM.Univ.UNInst

/-- `inst_step1Band_band`: `step1Band` at `sz0` (`d = 3`, `𝔠 = 1/6`, `𝔡 = 1/10`), the band model, `msc`, `E = 0`,
`ρ = rhoSC 0`, `δ = 1/2` (`un_dens'_msc_zero`), the local law from `UNTrLocalBandRow` at `κ = 1`, the norm bound
from `UNNormBandRow`, `k = 1`, `O = bump`, `τ_U = 1/60 = 𝔠𝔡`. -/
theorem inst_step1Band_band :
    UNL32 → UNGUELocal → UNLocAvgBand → UNTrLocalBandRow → UNNormBandRow →
      UNInfty1 sz0 (UNModel.band sz0) (fun _ => rhoSC 0) 0 0 1 (bump : (Fin 1 → ℝ) → ℝ) (1 / 60) := by
  intro h32 hGL hLoc rT rN
  obtain ⟨CV₀, hCV, hN⟩ := rN 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm
  exact step1Band h32 hGL 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm (UNModel.band sz0) (fun _ => msc) 0
    (fun _ => rhoSC 0) (1 / 2) un_dens'_msc_zero
    (rT hLoc 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm 1 one_pos 0 (by norm_num) (1 / 2) (by norm_num)
      (by norm_num))
    ⟨CV₀, hCV, hN⟩ 1 bump bump_testFun (1 / 60) (by norm_num) (by norm_num)

/-- `inst_step1Band_band_one`: the same at `E = 1` (`κ = 1/2`), `ρ = rhoSC 1`; the density from the row
`UNDensBandRow` through `unDensBandRow'_of_row` (`δ ≤ 1/4`, `0 < δ` from `UNDens`), so the energy shift `E ↦ 0`
and the dilation `ρ_sc(1) ≠ ρ_sc(0)` are both nontrivial. -/
theorem inst_step1Band_band_one :
    UNL32 → UNGUELocal → UNLocAvgBand → UNTrLocalBandRow → UNNormBandRow → UNDensBandRow →
      UNInfty1 sz0 (UNModel.band sz0) (fun _ => rhoSC 1) 1 0 1 (bump : (Fin 1 → ℝ) → ℝ) (1 / 60) := by
  intro h32 hGL hLoc rT rN rD
  obtain ⟨CV₀, hCV, hN⟩ := rN 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm
  obtain ⟨δ, hδκ, hD⟩ := unDensBandRow'_of_row rD (1 / 2) (by norm_num) 1 (by norm_num)
  have hδ : 0 < δ := hD.1.1
  exact step1Band h32 hGL 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm (UNModel.band sz0) (fun _ => msc) 1
    (fun _ => rhoSC 1) δ hD
    (rT hLoc 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm (1 / 2) (by norm_num) 1 (by norm_num) δ hδ hδκ)
    ⟨CV₀, hCV, hN⟩ 1 bump bump_testFun (1 / 60) (by norm_num) (by norm_num)

/-- `inst_rhoSC_one_lt_zero`: the two dilations of `inst_step1Band_band_one` differ (`√3/(2π) < 1/π`). -/
theorem inst_rhoSC_one_lt_zero : rhoSC 1 < rhoSC 0 := by
  unfold rhoSC
  exact (div_lt_div_iff_of_pos_right (by positivity)).2
    (Real.sqrt_lt_sqrt (by norm_num) (by norm_num))

/-- `inst_step1Band_row_band`: `step1Band_row` at the data of `inst_step1Band_band` (`E = 0`). -/
theorem inst_step1Band_row_band :
    UNL32 → UNGUELocal → UNLocAvgBand → UNTrLocalBandRow → UNNormBandRow →
      ∃ τ₁ : ℝ, 0 < τ₁ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₁ →
        UNInfty1 sz0 (UNModel.band sz0) (fun _ => rhoSC 0) 0 0 1 (bump : (Fin 1 → ℝ) → ℝ) τU := by
  intro h32 hGL hLoc rT rN
  obtain ⟨CV₀, hCV, hN⟩ := rN 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm
  exact step1Band_row h32 hGL 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm (UNModel.band sz0) (fun _ => msc) 0
    (fun _ => rhoSC 0) (1 / 2) un_dens'_msc_zero
    (rT hLoc 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm 1 one_pos 0 (by norm_num) (1 / 2) (by norm_num)
      (by norm_num))
    ⟨CV₀, hCV, hN⟩ 1 bump bump_testFun

/-- `inst_step1Band_abs_integral_kPoint_le`: target 1a at the GUE of `Idx 3 3 1` (`N = 27`), `k = 1`, `bump`. -/
theorem inst_step1Band_abs_integral_kPoint_le :
    |∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0 (Xmat_isHermitian 3 3 1 ω).eigenvalues ∂(gueP 3 3 1)| ≤
      (Fintype.card (Idx 3 3 1) : ℝ) ^ 1 * 1 :=
  step1Band_abs_integral_kPoint_le (gueP 3 3 1) (Xmat 3 3 1) (Xmat_isHermitian 3 3 1) 1
    (P := (bump : (Fin 1 → ℝ) → ℝ)) (B := 1)
    (fun x => by rw [abs_of_nonneg bump.nonneg]; exact bump.le_one) 0

/-- `inst_step1Band_kPoint_shift`: target 1b on `Fin 2` with `A = 1`, `B = 0 = A - 1 • 1`, shift `c = 1`. -/
theorem inst_step1Band_kPoint_shift :
    kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0 (Matrix.isHermitian_zero (n := Fin 2) (α := ℂ)).eigenvalues =
      kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 1 (Matrix.isHermitian_one (n := Fin 2) (α := ℂ)).eigenvalues :=
  step1Band_kPoint_shift Matrix.isHermitian_one Matrix.isHermitian_zero 1 (by simp) 1 bump

/-- `inst_step1Band_eventually_forall`: target 1c with the dependent carrier `Fin (n + 1)`,
`A n z := z = 0`, `P n z := z.val < 1`, `b n = 0`. -/
theorem inst_step1Band_eventually_forall :
    ∀ᶠ n in atTop, ∀ z : Fin (n + 1), z.val = 0 → z.val < 1 :=
  step1Band_eventually_forall (α := fun n => Fin (n + 1)) (fun _ z => z.val = 0)
    (fun _ z => z.val < 1) (fun _ => 0) (Eventually.of_forall fun _ => rfl)
    (fun f hf => hf.mono fun n hn => by simp only [hn]; exact Nat.zero_lt_one)

/-- `inst_step1Band_gue_count`: target 1d at `sz0`, `k = 1`, `τ_s = 1/60`, `Q = bump` (`UNGUELocal` a hypothesis). -/
theorem inst_step1Band_gue_count (hGL : UNGUELocal) :
    Tendsto (fun n => Nsz sz0 n ^ (-(3 * (1 / 60 : ℝ) / 8)) *
      ∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0 (Xmat_isHermitian 3 (sz0.L n) (sz0.W n) ω).eigenvalues
        ∂(gueP 3 (sz0.L n) (sz0.W n))) atTop (𝓝 0) :=
  step1Band_gue_count hGL 3 le_rfl sz0 (tendsto_natCast_atTop_iff.mp sz0_adm.2.2.1) (1 / 60)
    (by norm_num) (by norm_num) 1 bump bump_testFun (fun x => bump.nonneg)

/-- `inst_step1Band_integral_ouP`: target 2 at `sz0`, `n = 0`, the band model, `τ_U = 1/60`, `E = 0`, `k = 1`,
`bump`. -/
theorem inst_step1Band_integral_ouP :
    ∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0
        (ouMat_isHermitian (UNModel.band sz0) 0 (ouTStar sz0 (1 / 60) 0) ω).eigenvalues
        ∂(ouP (UNModel.band sz0) 0) =
      ∫ ω, (∫ y, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0
          (dbmMat_isHermitian 3 (sz0.L 0) (sz0.W 0) (vOU sz0 (UNModel.band sz0) 0 (1 / 60) 0 ω)
            (1 - Real.exp (-(ouTStar sz0 (1 / 60) 0))) y).eigenvalues ∂(gueP 3 (sz0.L 0) (sz0.W 0)))
        ∂(UNModel.band sz0).μ :=
  step1Band_integral_ouP sz0 (UNModel.band sz0) 0 (1 / 60) 0 1 bump bump_testFun

end Step1BandInst

end RBM.Univ

end
