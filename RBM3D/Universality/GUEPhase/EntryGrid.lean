/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.GUEPhase.EntryTailMain
import RBM3D.Universality.GUEPhase.Proc

/-!
# The grid form of Lemma 4.1: one-time law of the GUE-phase grid path, `d ≥ 3`

Ticket T2347 (UN-43).  Port of `RBM2D/Universality/GUEPhase/EntryGrid.lean` at `9e0f275`
(`:1-902`).  Paper: arXiv:2507.20274, the GUE phase of Thm 2.4
(`paper/tex/1_2_Intro_model_result.tex:566-570`, "essentially identical to [YY_25, Theorem 2.6]");
Lemma 4.1 (4.2)+(4.3) of [YY_25] is the merged `gueEntryMix` (`EntryTailMain.lean:545`).

* `map_gueH_eq_mixMat`: under `Pgue sz` the grid path at step `k` has the law of the mixture
  `mixMat sz n t₁ (u_k - t₁)` under `ouP (UNModel.band sz) n`, `u_k = gridTime k`.
* `gueGrid_entry_bound`: Lemma 4.1 (4.2)+(4.3) on the grid, from `gueEntryMix` after the transfer of
  the one-time law.

Reuse (DECISIONS §157): the source copies the private mixed-grid machinery of `Grid.lean`
(`EntryGrid_slice_add` … `EntryGrid_measurable_Xmat`, source `:49-373`); here the merged
`GUEPhaseGrid_` twins of `GUEPhase/Grid.lean` are used (the keyword `private` is deleted there on
`seqXmat_add/smul/sum`, `real_smul_matrix`, `map_combined_eq_mixed`, `Pgue_eq_mixed`,
`map_slice_infinitePi`, `measurable_Xmat`).

What changes from `d = 2` (rule R1 of the merged `Grid.lean`): `d : Sizes` becomes `sz : Sizes d`;
`Z2 L` becomes `Zd d L`; `Idx (d.L n) (d.W n)` becomes `Idx d (sz.L n) (sz.W n)`;
`spectralZ`/`spectralM` become `zt`/`mE`; `ouP L W` becomes `ouP (UNModel.band sz) n`;
`size = (W L)^d`, `W^{-2} ↦ W^{-d}`; `Admissible 𝔠 d ↦ sz.Admissible 𝔠 𝔡` with `hd : 3 ≤ d` for
`gueEntryMix` (statement delta `T2347a` of `gueGrid_entry_bound`).  The merged `llErrMat` is
`‖Gres M (zt E u) true i j - …‖` (one rewrite `Gres_eq_green_zSig`), the two-loop bound
`maxLoopPM ≤ loopMax _ 2` and `G_0 = m` are re-derived (the merged twins are `private`).

Layout: the one-time law (`EntryGrid_var`, `EntryGrid_map_gueH`, `map_gueH_eq_mixMat`) and its
preimage form `EntryGrid_pgue_preimage`; the bad set in matrix space and its measurability;
deterministic facts; the grid times and the exponent arithmetic; the main bound
`gueGrid_entry_bound`; the compiled instances.

Helpers are `private` or carry the prefix `EntryGrid_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Univ
open scoped NNReal ENNReal

variable {d : ℕ} (sz : Sizes d)

/-! ### The one-time law of the grid path at step `k` (T2) -/

section OneTimeLaw

/-- `gueUnitVar / N = gueVar` (`N = sz.size n = (W L)^d`): `1/N` on the diagonal, `1/(2N)` off it. -/
private lemma EntryGrid_gueUnitVar_div (n : ℕ) (c : CoordF d (sz.L n) (sz.W n)) :
    ((gueUnitVar sz ⟨n, c⟩ : ℝ≥0) : ℝ) / ((sz.size n : ℕ) : ℝ)
      = (RBM.Univ.gueVar d (sz.L n) (sz.W n) c : ℝ) := by
  have hsz : ((sz.size n : ℕ) : ℝ) = (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) := rfl
  unfold gueUnitVar RBM.Univ.gueVar
  by_cases hc : c.1 = c.2.1
  · simp only [hc, ite_true, hsz]
    push_cast
    simp
  · simp only [hc, ite_false, hsz]
    push_cast
    field_simp

/-- The coordinate variances of the grid path at step `k`:
`t₁ gvar_c + k (Δ/N) gueUnitVar_c`. -/
def EntryGrid_var (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (c : CoordF d (sz.L n) (sz.W n)) : ℝ≥0 :=
  NNReal.mk (Real.sqrt (t1 n) ^ 2) (sq_nonneg _) * Sizes.seqGvar sz ⟨n, c⟩
    + k • (NNReal.mk (Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) ^ 2) (sq_nonneg _)
        * gueUnitVar sz ⟨n, c⟩)

/-- **The one-time law of the grid path at step `k`**: `Xmat` of independent centred Gaussian
coordinates with variances `EntryGrid_var`. -/
theorem EntryGrid_map_gueH (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) :
    (Pgue sz).map (gueH sz t1 t0 K n k) =
      (Measure.infinitePi
        (fun c : CoordF d (sz.L n) (sz.W n) => gaussianReal 0 (EntryGrid_var sz t1 t0 K n k c))).map
        (Xmat d (sz.L n) (sz.W n)) := by
  set a : ℝ := Real.sqrt (t1 n) with hadef
  set b : ℝ := Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) with hbdef
  have hHeq : gueH sz t1 t0 K n k
      = fun ω => Sizes.seqXmat sz n (a • ω 0 + b • ∑ i ∈ Finset.Icc 1 k, ω i) := by
    funext ω
    rw [GUEPhaseGrid_seqXmat_add, GUEPhaseGrid_seqXmat_smul, GUEPhaseGrid_seqXmat_smul,
      GUEPhaseGrid_seqXmat_sum, GUEPhaseGrid_real_smul_matrix, GUEPhaseGrid_real_smul_matrix]
    rfl
  have hLHSmeas : Measurable (fun ω : PathΩ sz =>
      a • ω 0 + b • ∑ i ∈ Finset.Icc 1 k, ω i) := by
    have h1 : Measurable (fun ω : PathΩ sz => ω 0) := measurable_pi_apply 0
    have h2 : Measurable (fun ω : PathΩ sz => ∑ i ∈ Finset.Icc 1 k, ω i) :=
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    exact (h1.const_smul a).add (h2.const_smul b)
  have hfun : (fun ω : PathΩ sz => Sizes.seqXmat sz n
        (a • ω 0 + b • ∑ i ∈ Finset.Icc 1 k, ω i))
      = Xmat d (sz.L n) (sz.W n) ∘ Sizes.slice sz n ∘
          (fun ω : PathΩ sz => a • ω 0 + b • ∑ i ∈ Finset.Icc 1 k, ω i) := rfl
  rw [hHeq, hfun, ← Measure.map_map (GUEPhaseGrid_measurable_Xmat _ _)
      ((Sizes.measurable_slice sz n).comp hLHSmeas),
    ← Measure.map_map (Sizes.measurable_slice sz n) hLHSmeas,
    GUEPhaseGrid_Pgue_eq_mixed,
    GUEPhaseGrid_map_combined_eq_mixed (Sizes.seqGvar sz) (gueUnitVar sz) a b k]
  congr 1
  exact GUEPhaseGrid_map_slice_infinitePi _ n

/-- **T2: the law of the grid path at step `k` is the law of the mixture** `√t₁ X_band +
√(u_k - t₁) X_GUE` under `ouP`: the variance at step `k` is
`t₁ gvar + k Δ gueUnitVar / N`, which is `mixVar t₁ (k Δ)` because `gueVar = gueUnitVar / N` and
`gridTime k - t₁ = k Δ`. -/
theorem map_gueH_eq_mixMat (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ht1 : 0 ≤ t1 n)
    (ht10 : t1 n ≤ t0 n) :
    (Pgue sz).map (gueH sz t1 t0 K n k) =
      (ouP (UNModel.band sz) n).map
        (mixMat sz n (t1 n) (gridTime t1 t0 K n k - t1 n)) := by
  have hΔ : 0 ≤ gridStep t1 t0 K n := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hkΔ : 0 ≤ (k : ℝ) * gridStep t1 t0 K n := mul_nonneg (Nat.cast_nonneg _) hΔ
  have hbk : gridTime t1 t0 K n k - t1 n = (k : ℝ) * gridStep t1 t0 K n := by
    unfold gridTime; ring
  have hb : 0 ≤ gridTime t1 t0 K n k - t1 n := by rw [hbk]; exact hkΔ
  have hMpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by
    have h1 : 0 < sz.W n := sz.W_pos n
    have h2 : 0 < sz.L n := by have := sz.three_le_L n; omega
    have : 0 < sz.size n := by unfold Sizes.size; positivity
    exact_mod_cast this
  -- the `ouP` side: `mixMat = Xmat ∘ mixSample`, and `mixSample_law`
  have hcomp : mixMat sz n (t1 n) (gridTime t1 t0 K n k - t1 n)
      = Xmat d (sz.L n) (sz.W n) ∘
          mixSample sz n (t1 n) (gridTime t1 t0 K n k - t1 n) :=
    funext (mixMat_eq_Xmat_mixSample sz n _ _)
  rw [EntryGrid_map_gueH, hcomp,
    ← Measure.map_map (GUEPhaseGrid_measurable_Xmat _ _) (measurable_mixSample sz n _ _),
    mixSample_law sz n ht1 hb]
  congr 1
  refine congrArg Measure.infinitePi (funext fun c => ?_)
  congr 1
  apply NNReal.coe_injective
  have ha2 : Real.sqrt (t1 n) ^ 2 = t1 n := Real.sq_sqrt ht1
  have hb2 : Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) ^ 2
      = gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ) := Real.sq_sqrt (div_nonneg hΔ hMpos.le)
  have hunit := EntryGrid_gueUnitVar_div sz n c
  have hseq : ((Sizes.seqGvar sz ⟨n, c⟩ : ℝ≥0) : ℝ)
      = (gvarF d (sz.L n) (sz.W n) (sz.lam n) c : ℝ) := rfl
  have hmix := mixEntry_mixVar_coe d (sz.L n) (sz.W n) (sz.lam n) ht1 hb c
  rw [hmix, ← hunit, hbk]
  unfold EntryGrid_var
  simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk, nsmul_eq_mul, NNReal.coe_natCast]
  rw [ha2, hb2, hseq]
  ring

end OneTimeLaw

/-- The preimage form of T2: for a measurable set `B` of matrices, `Pgue` of the event
`{gueH_k ∈ B}` is the `ouP`-probability of `{mixMat ∈ B}`. -/
theorem EntryGrid_pgue_preimage (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ht1 : 0 ≤ t1 n)
    (ht10 : t1 n ≤ t0 n)
    {B : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)}
    (hB : MeasurableSet B) :
    Pgue sz (gueH sz t1 t0 K n k ⁻¹' B) =
      ouP (UNModel.band sz) n
        (mixMat sz n (t1 n) (gridTime t1 t0 K n k - t1 n) ⁻¹' B) := by
  rw [← Measure.map_apply (gueH_measurable sz t1 t0 K n k) hB,
    map_gueH_eq_mixMat sz t1 t0 K n k ht1 ht10,
    Measure.map_apply (measurable_mixMat sz n _ _) hB]

/-! ### The bad set in matrix space and its measurability -/

section MatrixSpace

variable (d L W : ℕ) [NeZero L] [NeZero W]

private theorem EntryGrid_measurable_inv_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Θ : Type*} [MeasurableSpace Θ] {M : Θ → Matrix ι ι ℂ} (hM : Measurable M) (i j : ι) :
    Measurable fun ω => (M ω)⁻¹ i j := by
  have h : (fun ω => (M ω)⁻¹ i j)
      = fun ω => Ring.inverse (M ω).det * (M ω).adjugate i j := by
    funext ω; rw [Matrix.inv_def]; rfl
  rw [h]
  refine Measurable.mul ?_ ?_
  · have hinv : Measurable (Ring.inverse : ℂ → ℂ) := by
      rw [Ring.inverse_eq_inv']; exact measurable_inv
    exact hinv.comp ((continuous_id.matrix_det).measurable.comp hM)
  · exact ((continuous_id.matrix_adjugate).measurable.comp hM).eval_matrix

/-- The merged `llErrMat` is `‖(M - z)⁻¹_{ij} - m δ_{ij}‖` (`Gres M z true` is `green M z`). -/
private theorem EntryGrid_llErrMat_eq (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (i j : Idx d L W) :
    RBM.Green.llErrMat d L W E u M i j
      = ‖(M - zt E u • (1 : Matrix (Idx d L W) (Idx d L W) ℂ))⁻¹ i j
          - (if i = j then mE E else 0)‖ := by
  unfold RBM.Green.llErrMat
  rw [RBM.Ind.Gres_eq_green_zSig]
  rfl

private theorem EntryGrid_measurable_llErrMat (E u : ℝ) (i j : Idx d L W) :
    Measurable fun M : Matrix (Idx d L W) (Idx d L W) ℂ => RBM.Green.llErrMat d L W E u M i j := by
  have hM : Measurable fun M : Matrix (Idx d L W) (Idx d L W) ℂ =>
      M - zt E u • (1 : Matrix (Idx d L W) (Idx d L W) ℂ) :=
    (continuous_id.sub continuous_const).measurable
  simp only [EntryGrid_llErrMat_eq]
  exact ((EntryGrid_measurable_inv_apply hM i j).sub measurable_const).norm

private theorem EntryGrid_measurable_maxLoopPM (E u : ℝ) :
    Measurable fun M : Matrix (Idx d L W) (Idx d L W) ℂ => RBM.Green.maxLoopPM d L W E u M := by
  have hloop : ∀ a b : Zd d L,
      Measurable fun M : Matrix (Idx d L W) (Idx d L W) ℂ => RBM.Green.loopPM d L W E u M a b :=
    fun a b => walk_measurable_loopFine d L W (zt E u) ![true, false] ![a, b]
  have hsup : Measurable (Finset.univ.sup' (Finset.univ_nonempty (α := Zd d L × Zd d L))
      (fun (p : Zd d L × Zd d L) (M : Matrix (Idx d L W) (Idx d L W) ℂ) =>
        ‖RBM.Green.loopPM d L W E u M p.1 p.2‖)) :=
    Finset.measurable_sup' Finset.univ_nonempty fun p _ => (hloop p.1 p.2).norm
  have heq : (fun M : Matrix (Idx d L W) (Idx d L W) ℂ => RBM.Green.maxLoopPM d L W E u M) =
      Finset.univ.sup' (Finset.univ_nonempty (α := Zd d L × Zd d L))
        (fun (p : Zd d L × Zd d L) (M : Matrix (Idx d L W) (Idx d L W) ℂ) =>
          ‖RBM.Green.loopPM d L W E u M p.1 p.2‖) := by
    funext M
    simp only [RBM.Green.maxLoopPM, Finset.sup'_apply]
  rw [heq]
  exact hsup

/-- The single-`k` bad set of `GUEEntryMix` in matrix space (`s = N^τ`, `δ`, energy `E`, time `u`):
the matrices `M` with `s (maxLoopPM M + W^{-d}) < ` the squared error entry on the event
`{all entries ≤ δ}`, for some entry `(i, j)`. -/
private def EntryGrid_badMat (E u δ s : ℝ) : Set (Matrix (Idx d L W) (Idx d L W) ℂ) :=
  {M | ∃ i j : Idx d L W, s * (RBM.Green.maxLoopPM d L W E u M + (((W : ℕ) : ℝ) ^ d)⁻¹) <
    (if ∀ x y, RBM.Green.llErrMat d L W E u M x y ≤ δ
      then RBM.Green.llErrMat d L W E u M i j ^ 2 else 0)}

private theorem EntryGrid_measurableSet_badMat (E u δ s : ℝ) :
    MeasurableSet (EntryGrid_badMat d L W E u δ s) := by
  have hll : ∀ x y : Idx d L W,
      Measurable fun M : Matrix (Idx d L W) (Idx d L W) ℂ => RBM.Green.llErrMat d L W E u M x y :=
    fun x y => EntryGrid_measurable_llErrMat d L W E u x y
  have hcond : MeasurableSet {M : Matrix (Idx d L W) (Idx d L W) ℂ |
      ∀ x y, RBM.Green.llErrMat d L W E u M x y ≤ δ} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun x => MeasurableSet.iInter fun y =>
      measurableSet_le (hll x y) measurable_const
  have hrhs : ∀ i j : Idx d L W, Measurable fun M : Matrix (Idx d L W) (Idx d L W) ℂ =>
      (if ∀ x y, RBM.Green.llErrMat d L W E u M x y ≤ δ
        then RBM.Green.llErrMat d L W E u M i j ^ 2 else 0) :=
    fun i j => Measurable.ite hcond ((hll i j).pow_const 2) measurable_const
  have hlhs : Measurable fun M : Matrix (Idx d L W) (Idx d L W) ℂ =>
      s * (RBM.Green.maxLoopPM d L W E u M + (((W : ℕ) : ℝ) ^ d)⁻¹) :=
    measurable_const.mul ((EntryGrid_measurable_maxLoopPM d L W E u).add measurable_const)
  have heq : EntryGrid_badMat d L W E u δ s = ⋃ i : Idx d L W, ⋃ j : Idx d L W,
      {M : Matrix (Idx d L W) (Idx d L W) ℂ |
        s * (RBM.Green.maxLoopPM d L W E u M + (((W : ℕ) : ℝ) ^ d)⁻¹) <
        (if ∀ x y, RBM.Green.llErrMat d L W E u M x y ≤ δ
          then RBM.Green.llErrMat d L W E u M i j ^ 2 else 0)} := by
    ext M
    simp [EntryGrid_badMat]
  rw [heq]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j =>
    measurableSet_lt hlhs (hrhs i j)

end MatrixSpace

/-! ### Deterministic facts -/

section Deterministic

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- `(green M z - m • 1)_{ij}` has norm `llErrMat` at `z = zt E u`, `m = mE E`. -/
private theorem EntryGrid_norm_green_sub_eq (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (i j : Idx d L W) :
    ‖(green M (zt E u) - mE E • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)) i j‖
      = RBM.Green.llErrMat d L W E u M i j := by
  rw [EntryGrid_llErrMat_eq]
  congr 1
  simp only [green, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero]

/-- `maxLoopPM ≤ loopMax _ 2`: the `(+,-)` two-loops `loopPM a b` have two signs and two labels
(re-derived: the merged `Proc_maxLoopPM_le_loopMax` is `private`). -/
private theorem EntryGrid_maxLoopPM_le (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) :
    RBM.Green.maxLoopPM d L W E u M ≤ RBM.Ind.loopMax d L W (blockMat d L W M) (zt E u) 2 := by
  unfold RBM.Green.maxLoopPM
  refine Finset.sup'_le _ _ fun p _ => ?_
  have h : RBM.Green.loopPM d L W E u M p.1 p.2
      = loopL d L W (blockMat d L W M) (zt E u) (loopOf ![true, false] ![p.1, p.2]) := by
    simp only [RBM.Green.loopPM, loopFine, loopM_eq_loopL]
  rw [h]
  exact RBM.Ind.norm_gloop_le_loopMax (loopOf ![true, false] ![p.1, p.2])
    (by simp [loopOf]) (by simp [loopOf])

end Deterministic

/-- `G_0(+) = m I` at `H = 0`, `u = 0` (`z_0 = E + m`, `m (m + E) = -1`), for any finite index
(re-derived: the merged `gres_zero_true`, `Green/Pins.lean:1181`, is `private`). -/
private theorem EntryGrid_gres_zero_true {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ℝ}
    (hE : |E| ≤ 2) :
    Gres (0 : Matrix ι ι ℂ) (zt E 0) true = mE E • (1 : Matrix ι ι ℂ) := by
  have hm := mE_mul hE
  have hzt : zt E 0 = (E : ℂ) + mE E := by simp [zt]
  have hmz : (-((E : ℂ) + mE E))⁻¹ = mE E := by
    refine inv_eq_of_mul_eq_one_right ?_
    linear_combination (-1 : ℂ) * hm
  have hne : (E : ℂ) + mE E ≠ 0 := by
    intro h0
    rw [add_comm, h0, mul_zero] at hm
    norm_num at hm
  rw [Gres]
  simp only [↓reduceIte]
  rw [hzt, zero_sub, ← neg_smul, ring_inverse_smul_one (neg_ne_zero.2 hne), hmz]

/-- Zero time: every entry of `green 0 z_0 - m • 1` vanishes, so `0 ∉` the bad set of time `0`. -/
private theorem EntryGrid_zero_not_mem_badMat (d L W : ℕ) [NeZero L] [NeZero W] {E : ℝ}
    (hE : |E| ≤ 2) (δ s : ℝ) (hs : 0 ≤ s) :
    (0 : Matrix (Idx d L W) (Idx d L W) ℂ) ∉ EntryGrid_badMat d L W E 0 δ s := by
  rintro ⟨i, j, h⟩
  have hll : ∀ x y : Idx d L W, RBM.Green.llErrMat d L W E 0 0 x y = 0 := by
    intro x y
    unfold RBM.Green.llErrMat
    rw [EntryGrid_gres_zero_true hE]
    by_cases hxy : x = y <;> simp [hxy]
  have hrhs : (if ∀ x y, RBM.Green.llErrMat d L W E 0 0 x y ≤ δ
      then RBM.Green.llErrMat d L W E 0 0 i j ^ 2 else 0) = 0 := by
    split_ifs
    · rw [hll i j]; norm_num
    · rfl
  rw [hrhs] at h
  have h0 : 0 ≤ s * (RBM.Green.maxLoopPM d L W E 0 0 + (((W : ℕ) : ℝ) ^ d)⁻¹) :=
    mul_nonneg hs (add_nonneg (RBM.Green.maxLoopPM_nonneg E 0 _) (by positivity))
  exact absurd h (not_lt.2 h0)

/-! ### The grid times -/

/-- `Δ ≥ 0`. -/
private theorem EntryGrid_gridStep_nonneg {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ}
    (h : t1 n ≤ t0 n) : 0 ≤ gridStep t1 t0 K n :=
  div_nonneg (by linarith) (Nat.cast_nonneg _)

private theorem EntryGrid_gridTime_sub (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) :
    gridTime t1 t0 K n k - t1 n = (k : ℝ) * gridStep t1 t0 K n := by
  unfold gridTime; ring

/-- `t₁ ≤ u_k`. -/
private theorem EntryGrid_gridTime_ge {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (k : ℕ)
    (ht10 : t1 n ≤ t0 n) : t1 n ≤ gridTime t1 t0 K n k := by
  have h := EntryGrid_gridTime_sub t1 t0 K n k
  have h2 : 0 ≤ (k : ℝ) * gridStep t1 t0 K n :=
    mul_nonneg (Nat.cast_nonneg _) (EntryGrid_gridStep_nonneg ht10)
  linarith

/-- `u_k ≤ t₀` for `k ≤ K`. -/
private theorem EntryGrid_gridTime_le {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n k : ℕ} (hK : K n ≠ 0)
    (ht10 : t1 n ≤ t0 n) (hk : k ≤ K n) : gridTime t1 t0 K n k ≤ t0 n := by
  rw [← gridTime_last t1 t0 K n hK]
  unfold gridTime
  have hΔ := EntryGrid_gridStep_nonneg (K := K) ht10
  have hk' : (k : ℝ) ≤ (K n : ℝ) := by exact_mod_cast hk
  nlinarith

/-- At grid time `0`: `t₁ = 0` and `k Δ = 0`, so the path vanishes. -/
private theorem EntryGrid_gueH_zero (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ht1 : 0 ≤ t1 n)
    (ht10 : t1 n ≤ t0 n) (hu : gridTime t1 t0 K n k = 0) (ω : PathΩ sz) :
    gueH sz t1 t0 K n k ω = 0 := by
  have hΔ := EntryGrid_gridStep_nonneg (K := K) ht10
  have hkΔ : 0 ≤ (k : ℝ) * gridStep t1 t0 K n := mul_nonneg (Nat.cast_nonneg _) hΔ
  have h := EntryGrid_gridTime_sub t1 t0 K n k
  have ht : t1 n = 0 := by rw [hu] at h; linarith [ht1]
  have hk : (k : ℝ) * gridStep t1 t0 K n = 0 := by rw [hu] at h; linarith [ht1]
  unfold gueH
  rw [ht, Real.sqrt_zero, Complex.ofReal_zero, zero_smul, zero_add]
  rcases mul_eq_zero.1 hk with h | h
  · have hk0 : k = 0 := by exact_mod_cast h
    subst hk0
    simp
  · rw [h, zero_div, Real.sqrt_zero, Complex.ofReal_zero, zero_smul]

/-! ### The parameters fed to `gueEntryMix` -/

/-- `a_k = t₁` at positive grid time (`1/2` at grid time `0`, where `0 < a + b` would fail). -/
private def EntryGrid_a (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) : ℝ :=
  if 0 < gridTime t1 t0 K n k then t1 n else 1 / 2

/-- `b_k = u_k - t₁` at positive grid time (`0` at grid time `0`). -/
private def EntryGrid_b (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) : ℝ :=
  if 0 < gridTime t1 t0 K n k then gridTime t1 t0 K n k - t1 n else 0

private theorem EntryGrid_params (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ht1 : 0 ≤ t1 n)
    (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1) (hK : K n ≠ 0) (hk : k ≤ K n) :
    0 ≤ EntryGrid_a t1 t0 K n k ∧ 0 ≤ EntryGrid_b t1 t0 K n k ∧
      0 < EntryGrid_a t1 t0 K n k + EntryGrid_b t1 t0 K n k ∧
      EntryGrid_a t1 t0 K n k + EntryGrid_b t1 t0 K n k < 1 := by
  by_cases hpos : 0 < gridTime t1 t0 K n k
  · have hge := EntryGrid_gridTime_ge (K := K) k ht10
    have hle := EntryGrid_gridTime_le hK ht10 hk
    simp only [EntryGrid_a, EntryGrid_b, hpos, ↓reduceIte]
    refine ⟨ht1, by linarith, by linarith, by linarith⟩
  · simp only [EntryGrid_a, EntryGrid_b, hpos, ↓reduceIte]
    norm_num

/-! ### The size bounds and the union arithmetic -/

/-- `2 ≤ N = (W L)^d` (`d ≥ 1`, `W ≥ 1`, `L ≥ 3`; RBM2D: `nlinarith` on `(W L)^2`). -/
private theorem EntryGrid_two_le_size (hd : 1 ≤ d) (n : ℕ) : 2 ≤ sz.size n := by
  have h1 : 1 ≤ sz.W n := sz.W_pos n
  have h3 : 3 ≤ sz.L n := sz.three_le_L n
  have h4 : 3 ≤ sz.W n * sz.L n := by nlinarith
  unfold Sizes.size
  calc 2 ≤ sz.W n * sz.L n := by omega
    _ ≤ (sz.W n * sz.L n) ^ d := Nat.le_self_pow (by omega) _

private theorem EntryGrid_gridK_le (hd : 1 ≤ d) (n0 n : ℕ) :
    gueGridK sz n0 n ≤ (sz.size n) ^ (64 * n0 + 128) := by
  unfold gueGridK
  have h2 := EntryGrid_two_le_size sz hd n
  calc (sz.size n + 1) ^ (32 * n0 + 64) ≤ (sz.size n ^ 2) ^ (32 * n0 + 64) :=
        Nat.pow_le_pow_left (by nlinarith) _
    _ = (sz.size n) ^ (64 * n0 + 128) := by rw [← pow_mul]; ring_nf

/-- `(K + 1) N^{-(D + 1 + m)} ≤ N^{-D}` for `K ≤ N^m`, `N ≥ 2` (dimension-free). -/
private theorem EntryGrid_union_arith (Nn Kn m : ℕ) (hN : 2 ≤ Nn) (hK : Kn ≤ Nn ^ m) (D : ℝ) :
    ((Kn + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((Nn : ℝ) ^ (-(D + 1 + (m : ℝ))))
      ≤ ENNReal.ofReal ((Nn : ℝ) ^ (-D)) := by
  have hN2 : (2 : ℝ) ≤ Nn := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < Nn := by linarith
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hKr : (Kn : ℝ) ≤ (Nn : ℝ) ^ m := by exact_mod_cast hK
  have h1 : (1 : ℝ) ≤ (Nn : ℝ) ^ m := one_le_pow₀ (by linarith)
  have hp : (0 : ℝ) ≤ (Nn : ℝ) ^ (-(D + 1 + (m : ℝ))) := Real.rpow_nonneg hN0.le _
  have hmul : (Nn : ℝ) ^ (m : ℝ) * (Nn : ℝ) ^ (-((D + 1) + (m : ℝ))) = (Nn : ℝ) ^ (-(D + 1)) :=
    rpow_mul_rpow_neg_add (by omega) (m : ℝ) (D + 1)
  have hnat : (Nn : ℝ) ^ (m : ℝ) = (Nn : ℝ) ^ m := Real.rpow_natCast _ _
  have hD1 : (2 : ℝ) * (Nn : ℝ) ^ (-(D + 1)) ≤ (Nn : ℝ) ^ (-D) := by
    rw [neg_add, Real.rpow_add hN0, Real.rpow_neg_one]
    have h := Real.rpow_nonneg hN0.le (-D)
    calc 2 * ((Nn : ℝ) ^ (-D) * (Nn : ℝ)⁻¹) = (Nn : ℝ) ^ (-D) * (2 / Nn) := by ring
      _ ≤ (Nn : ℝ) ^ (-D) * 1 := by
          gcongr; rw [div_le_one hN0]; exact hN2
      _ = _ := mul_one _
  calc ((Kn + 1 : ℕ) : ℝ) * (Nn : ℝ) ^ (-(D + 1 + (m : ℝ)))
      ≤ (2 * (Nn : ℝ) ^ m) * (Nn : ℝ) ^ (-(D + 1 + (m : ℝ))) := by
        apply mul_le_mul_of_nonneg_right _ hp
        push_cast; linarith
    _ = 2 * ((Nn : ℝ) ^ (m : ℝ) * (Nn : ℝ) ^ (-((D + 1) + (m : ℝ)))) := by rw [hnat]; ring
    _ = 2 * (Nn : ℝ) ^ (-(D + 1)) := by rw [hmul]
    _ ≤ (Nn : ℝ) ^ (-D) := hD1

/-! ### T1: Lemma 4.1 on the GUE-phase grid -/

/-- The pointwise step of `gueGrid_entry_bound`: if `ω` is in the bad event of the entry `(i, j)`
at grid step `k` (the bound `s (gueLmax + W^{-d}) < ` the indicator of the a priori event times the
squared entry of `green - m • 1`), then `gueH_k ω` lies in the bad set of matrix space
(`maxLoopPM ≤ gueLmax`, `‖(green M z - m • 1)_{ij}‖ = llErrMat M i j`). -/
private theorem EntryGrid_pointwise (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (n k : ℕ)
    (ω : PathΩ sz) (i j : Idx d (sz.L n) (sz.W n)) (s : ℝ) (hs : 0 ≤ s)
    (hlt : s * (gueLmax sz E t1 t0 K n 2 k ω + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) <
      {ω' : PathΩ sz | ∀ i j : Idx d (sz.L n) (sz.W n),
          ‖(green (gueH sz t1 t0 K n k ω') (zt (E n) (gridTime t1 t0 K n k)) -
            mE (E n) •
              (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) i j‖ ≤ δ n}.indicator
        (fun ω' => ‖(green (gueH sz t1 t0 K n k ω') (zt (E n) (gridTime t1 t0 K n k)) -
            mE (E n) •
              (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) i j‖ ^ 2) ω) :
    gueH sz t1 t0 K n k ω ∈
      EntryGrid_badMat d (sz.L n) (sz.W n) (E n) (gridTime t1 t0 K n k) (δ n) s := by
  have hnorm : ∀ (M' : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
      (x y : Idx d (sz.L n) (sz.W n)),
      ‖(green M' (zt (E n) (gridTime t1 t0 K n k)) -
          mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) x y‖
        = RBM.Green.llErrMat d (sz.L n) (sz.W n) (E n) (gridTime t1 t0 K n k) M' x y :=
    fun M' x y => EntryGrid_norm_green_sub_eq d _ _ _ _ M' x y
  have hle : s * (RBM.Green.maxLoopPM d (sz.L n) (sz.W n) (E n) (gridTime t1 t0 K n k)
        (gueH sz t1 t0 K n k ω) + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹)
      ≤ s * (gueLmax sz E t1 t0 K n 2 k ω + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) :=
    mul_le_mul_of_nonneg_left
      (add_le_add_left (EntryGrid_maxLoopPM_le d (sz.L n) (sz.W n) (E n) _ _) _) hs
  by_cases hall : ∀ x y, RBM.Green.llErrMat d (sz.L n) (sz.W n) (E n) (gridTime t1 t0 K n k)
      (gueH sz t1 t0 K n k ω) x y ≤ δ n
  · have hmem : ω ∈ {ω' : PathΩ sz | ∀ i j : Idx d (sz.L n) (sz.W n),
        ‖(green (gueH sz t1 t0 K n k ω') (zt (E n) (gridTime t1 t0 K n k)) -
          mE (E n) •
            (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) i j‖ ≤ δ n} := by
      intro x y
      rw [hnorm]
      exact hall x y
    rw [Set.indicator_of_mem hmem] at hlt
    refine ⟨i, j, ?_⟩
    simp only [hall, implies_true, ↓reduceIte]
    refine lt_of_le_of_lt hle (lt_of_lt_of_eq hlt ?_)
    simp only [hnorm]
  · have hnot : ω ∉ {ω' : PathΩ sz | ∀ i j : Idx d (sz.L n) (sz.W n),
        ‖(green (gueH sz t1 t0 K n k ω') (zt (E n) (gridTime t1 t0 K n k)) -
          mE (E n) •
            (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) i j‖ ≤ δ n} := by
      intro h
      apply hall
      intro x y
      rw [← hnorm]
      exact h x y
    rw [Set.indicator_of_notMem hnot] at hlt
    have h0 : 0 ≤ s * (gueLmax sz E t1 t0 K n 2 k ω + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) :=
      mul_nonneg hs (add_nonneg (RBM.Ind.loopMax_nonneg 2) (by positivity))
    exact absurd hlt (not_lt.2 h0)

/-- **Lemma 4.1 (4.2)+(4.3) on the GUE-phase grid**, on the size scale, `d ≥ 3`.  On the a priori
event `{all entries of G - m ≤ δ_n}`, `δ_n ≤ N^{-c₀}`, the squared entry `|(G_k - m)_{ij}|²` of the
grid resolvent at the grid time `u_k` is `≺ max_{a,b} |𝓛_{(+,-),(a,b)}| + W^{-d}` (`gueLmax _ 2`,
the 2-loop maximum), uniformly in `k ≤ K_n`, `i`, `j`.  Proof: per grid point `k` the bad event on
`Pgue` has the `ouP`-probability of the bad event of the mixture `mixMat t₁ (u_k - t₁)`
(`map_gueH_eq_mixMat`), a subset of the event of `gueEntryMix` (`a = t₁`, `b = u_k - t₁`); the union
over the `K_n + 1` grid points costs a power of `N` (`K_n ≤ N^{64 n₀ + 128}`,
`D ↦ D + 1 + 64 n₀ + 128`); at grid time `0` (`t₁ = 0`, `k = 0` or `Δ = 0`) `gueH = 0` and the bad
event is empty.  Statement delta `T2347a` against RBM2D: `hd : 3 ≤ d` and `𝔡` added (they are the
inputs of the merged `gueEntryMix`), `h𝔠` dropped (`hadm.1`), `W^{-2} ↦ W^{-d}`. -/
theorem gueGrid_entry_bound (hd : 3 ≤ d) {𝔠 𝔡 κ : ℝ} (hadm : sz.Admissible 𝔠 𝔡) (hκ : 0 < κ)
    (n0 : ℕ) {E t1 t0 : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n)
    (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1) {δ : ℕ → ℝ} (hδ0 : ∀ n, 0 ≤ δ n)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hδ : ∀ᶠ n in atTop, δ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-c₀)) :
    StochDomAt (Pgue sz) sz.size
      (fun n (p : Fin (gueGridK sz n0 n + 1) ×
          (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))) ω =>
        {ω' : PathΩ sz | ∀ i j : Idx d (sz.L n) (sz.W n),
            ‖(green (gueH sz t1 t0 (gueGridK sz n0) n p.1 ω')
                (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n p.1)) -
              mE (E n) •
                (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) i j‖ ≤
            δ n}.indicator
          (fun ω' => ‖(green (gueH sz t1 t0 (gueGridK sz n0) n p.1 ω')
                (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n p.1)) -
              mE (E n) •
                (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))
                p.2.1 p.2.2‖ ^ 2) ω)
      (fun n p ω => gueLmax sz E t1 t0 (gueGridK sz n0) n 2 p.1 ω +
          (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) := by
  intro τ hτ D hD
  have hd1 : 1 ≤ d := by omega
  have hD' : 0 < D + 1 + ((64 * n0 + 128 : ℕ) : ℝ) := by positivity
  have hmix := gueEntryMix hd 𝔠 𝔡 sz hadm κ hκ E hE (64 * n0 + 128) (gueGridK sz n0)
    (EntryGrid_gridK_le sz hd1 n0) (fun n k => EntryGrid_a t1 t0 (gueGridK sz n0) n k)
    (fun n k => EntryGrid_b t1 t0 (gueGridK sz n0) n k)
    (fun n k => EntryGrid_params t1 t0 (gueGridK sz n0) n k (ht1 n) (ht10 n) (ht0 n)
      (gueGridK_ne_zero sz n0 n) (Nat.lt_succ_iff.1 k.2))
    c₀ δ hc₀ hδ0 hδ τ (D + 1 + ((64 * n0 + 128 : ℕ) : ℝ)) hτ hD'
  filter_upwards [hmix] with n hn
  have hN2 := EntryGrid_two_le_size sz hd1 n
  have hs0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  -- Step 1: the bad event is inside the union over the grid of the preimages of the matrix bad sets
  refine le_trans (measure_mono (t := ⋃ k : Fin (gueGridK sz n0 n + 1),
    gueH sz t1 t0 (gueGridK sz n0) n k ⁻¹' EntryGrid_badMat d (sz.L n) (sz.W n) (E n)
      (gridTime t1 t0 (gueGridK sz n0) n k) (δ n) (((sz.size n : ℕ) : ℝ) ^ τ)) ?_) ?_
  · rintro ω ⟨⟨k, i, j⟩, hlt⟩
    exact Set.mem_iUnion.2
      ⟨k, EntryGrid_pointwise sz E t1 t0 (gueGridK sz n0) δ n k ω i j _ hs0 hlt⟩
  -- Step 2: each grid point costs at most the `ouP`-probability of the event of `gueEntryMix`
  have hk : ∀ k : Fin (gueGridK sz n0 n + 1),
      Pgue sz (gueH sz t1 t0 (gueGridK sz n0) n k ⁻¹' EntryGrid_badMat d (sz.L n) (sz.W n) (E n)
        (gridTime t1 t0 (gueGridK sz n0) n k) (δ n) (((sz.size n : ℕ) : ℝ) ^ τ))
      ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D + 1 + ((64 * n0 + 128 : ℕ) : ℝ)))) := by
    intro k
    by_cases hpos : 0 < gridTime t1 t0 (gueGridK sz n0) n k
    · rw [EntryGrid_pgue_preimage sz t1 t0 _ n k (ht1 n) (ht10 n)
        (EntryGrid_measurableSet_badMat d (sz.L n) (sz.W n) _ _ _ _)]
      refine le_trans (measure_mono ?_) hn
      intro ω hω
      obtain ⟨i, j, hij⟩ := hω
      refine ⟨k, i, j, ?_⟩
      have hab : EntryGrid_a t1 t0 (gueGridK sz n0) n k + EntryGrid_b t1 t0 (gueGridK sz n0) n k
          = gridTime t1 t0 (gueGridK sz n0) n k := by
        simp only [EntryGrid_a, EntryGrid_b, hpos, ↓reduceIte]; ring
      have ha : EntryGrid_a t1 t0 (gueGridK sz n0) n k = t1 n := by
        simp only [EntryGrid_a, hpos, ↓reduceIte]
      have hb : EntryGrid_b t1 t0 (gueGridK sz n0) n k
          = gridTime t1 t0 (gueGridK sz n0) n k - t1 n := by
        simp only [EntryGrid_b, hpos, ↓reduceIte]
      rw [hab, ha, hb]
      exact hij
    · have h0 : gridTime t1 t0 (gueGridK sz n0) n k = 0 :=
        le_antisymm (not_lt.1 hpos) (le_trans (ht1 n) (EntryGrid_gridTime_ge k (ht10 n)))
      have hempty : gueH sz t1 t0 (gueGridK sz n0) n k ⁻¹' EntryGrid_badMat d (sz.L n) (sz.W n)
          (E n) (gridTime t1 t0 (gueGridK sz n0) n k) (δ n) (((sz.size n : ℕ) : ℝ) ^ τ) = ∅ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
        rw [EntryGrid_gueH_zero sz t1 t0 _ n k (ht1 n) (ht10 n) h0 ω, h0]
        exact EntryGrid_zero_not_mem_badMat d (sz.L n) (sz.W n)
          (by linarith [hE n, hκ, abs_nonneg (E n)]) (δ n) _ hs0
      rw [hempty, measure_empty]
      exact zero_le
  -- Step 3: the union bound over the `K_n + 1` grid points and the arithmetic
  calc Pgue sz (⋃ k : Fin (gueGridK sz n0 n + 1),
        gueH sz t1 t0 (gueGridK sz n0) n k ⁻¹' EntryGrid_badMat d (sz.L n) (sz.W n) (E n)
          (gridTime t1 t0 (gueGridK sz n0) n k) (δ n) (((sz.size n : ℕ) : ℝ) ^ τ))
      ≤ ∑ k : Fin (gueGridK sz n0 n + 1),
          Pgue sz (gueH sz t1 t0 (gueGridK sz n0) n k ⁻¹' EntryGrid_badMat d (sz.L n) (sz.W n)
            (E n) (gridTime t1 t0 (gueGridK sz n0) n k) (δ n) (((sz.size n : ℕ) : ℝ) ^ τ)) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _k : Fin (gueGridK sz n0 n + 1),
          ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D + 1 + ((64 * n0 + 128 : ℕ) : ℝ)))) :=
        Finset.sum_le_sum fun k _ => hk k
    _ = ((gueGridK sz n0 n + 1 : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D + 1 + ((64 * n0 + 128 : ℕ) : ℝ)))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) :=
        EntryGrid_union_arith _ _ _ hN2 (EntryGrid_gridK_le sz hd1 n0 n) D

end RBM.Univ.GUEPhase

/-! ## Compiled instances

The merged instance sizes `RBM.Gauss.SizesInst.sz0` (`d = 3`, `L 0 = 4`, `W 0 = 32`,
`N = 2097152`), admissible at `(𝔠, 𝔡) = (1/6, 1/10)`; the data of `GUEPhase/Grid.lean` §`GridCheck`:
`t₀ = 9/10`, `t₁ = (1 - ζ(1/20)) t₀ = e^{-1/20} · 9/10`, `K = fun _ => 4`.  For
`gueGrid_entry_bound`: `E = 0`, `κ = 1`, `n₀ = 1`, `c₀ = 1/4`, `δ_n = N^{-1/4}`. -/

namespace RBM.Univ.GUEPhase.EntryGridInst

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Univ RBM.Univ.GUEPhase
open RBM.Gauss.SizesInst
open scoped NNReal ENNReal

/-- `t₁ = (1 - ζ(1/20)) · 9/10 ≤ 9/10 = t₀`. -/
private theorem t1_le : (1 - ouZeta (1 / 20)) * (9 / 10 : ℝ) ≤ 9 / 10 := by
  unfold ouZeta
  have : Real.exp (-(1 / 20 : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  nlinarith

-- `EntryGrid_var` at step `k = 0` (the band variance `t₁ gvar`), at the instance data
example (c : CoordF 3 (sz0.L 0) (sz0.W 0)) :
    EntryGrid_var sz0 (fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)) (fun _ => 9 / 10)
        (fun _ => 4) 0 0 c
      = NNReal.mk (Real.sqrt ((1 - ouZeta (1 / 20)) * (9 / 10)) ^ 2) (sq_nonneg _)
          * Sizes.seqGvar sz0 ⟨0, c⟩ := by
  simp [EntryGrid_var]

-- `EntryGrid_map_gueH` at the instance data, `n = 0` (`L = 4`, `W = 32`, `N = 2097152`), step `k = 2`
example :
    (Pgue sz0).map
        (gueH sz0 (fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)) (fun _ => 9 / 10)
          (fun _ => 4) 0 2) =
      (Measure.infinitePi (fun c : CoordF 3 (sz0.L 0) (sz0.W 0) => gaussianReal 0
        (EntryGrid_var sz0 (fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)) (fun _ => 9 / 10)
          (fun _ => 4) 0 2 c))).map (Xmat 3 (sz0.L 0) (sz0.W 0)) :=
  EntryGrid_map_gueH sz0 _ _ _ 0 2

-- `map_gueH_eq_mixMat` at the instance data, `n = 0`, step `k = 2` (`u_2 = t₁ + 2Δ ∈ (t₁, t₀)`)
example :
    (Pgue sz0).map
        (gueH sz0 (fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)) (fun _ => 9 / 10)
          (fun _ => 4) 0 2) =
      (ouP (UNModel.band sz0) 0).map
        (mixMat sz0 0 ((1 - ouZeta (1 / 20)) * (9 / 10))
          (gridTime (fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)) (fun _ => 9 / 10)
            (fun _ => 4) 0 2 - (1 - ouZeta (1 / 20)) * (9 / 10))) :=
  map_gueH_eq_mixMat sz0 _ _ _ 0 2 GridCheck.t1_pos t1_le

-- the same for every size index `n` and every step `k`
example (n k : ℕ) :
    (Pgue sz0).map
        (gueH sz0 (fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)) (fun _ => 9 / 10)
          (fun _ => 4) n k) =
      (ouP (UNModel.band sz0) n).map
        (mixMat sz0 n ((1 - ouZeta (1 / 20)) * (9 / 10))
          (gridTime (fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)) (fun _ => 9 / 10)
            (fun _ => 4) n k - (1 - ouZeta (1 / 20)) * (9 / 10))) :=
  map_gueH_eq_mixMat sz0 _ _ _ n k GridCheck.t1_pos t1_le

/-- The measurable set `{M | ∀ i, ‖M i i‖ ≤ 1}` of matrices of size `n = 0` (`N = 2097152`). -/
private theorem measurableSet_diag_le :
    MeasurableSet {M : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ |
      ∀ i, ‖M i i‖ ≤ 1} := by
  have h : {M : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ |
      ∀ i, ‖M i i‖ ≤ 1} = ⋂ i, {M | ‖M i i‖ ≤ 1} := by
    ext M
    simp
  rw [h]
  exact MeasurableSet.iInter fun i =>
    measurableSet_le ((continuous_id.matrix_elem i i).norm.measurable) measurable_const

-- `EntryGrid_pgue_preimage` at the instance data, `n = 0`, `k = 2`, for the set `{∀ i, |M_ii| ≤ 1}`
example :
    Pgue sz0 (gueH sz0 (fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)) (fun _ => 9 / 10)
        (fun _ => 4) 0 2 ⁻¹'
          {M : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ |
            ∀ i, ‖M i i‖ ≤ 1}) =
      ouP (UNModel.band sz0) 0
        (mixMat sz0 0 ((1 - ouZeta (1 / 20)) * (9 / 10))
            (gridTime (fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)) (fun _ => 9 / 10)
              (fun _ => 4) 0 2 - (1 - ouZeta (1 / 20)) * (9 / 10)) ⁻¹'
          {M : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ |
            ∀ i, ‖M i i‖ ≤ 1}) :=
  EntryGrid_pgue_preimage sz0 _ _ _ 0 2 GridCheck.t1_pos t1_le measurableSet_diag_le

-- `gueGrid_entry_bound` at `d = 3`, `sz0`, `(𝔠, 𝔡) = (1/6, 1/10)`, `κ = 1`, `E = 0`, `n₀ = 1`,
-- `t₀ = 9/10`, `t₁ = e^{-1/20} · 9/10`, `δ_n = N^{-1/4}`, `c₀ = 1/4`: every hypothesis is discharged
-- (`sz0_admissible` is the merged proof of the size pin; `hδ` holds with equality).
theorem gueGrid_entry_bound_sz0 :
    StochDomAt (Pgue sz0) sz0.size
      (fun n (p : Fin (gueGridK sz0 1 n + 1) ×
          (Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))) ω =>
        {ω' : PathΩ sz0 | ∀ i j : Idx 3 (sz0.L n) (sz0.W n),
            ‖(green (gueH sz0 (fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)) (fun _ => 9 / 10)
                (gueGridK sz0 1) n p.1 ω')
                (zt 0 (gridTime (fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)) (fun _ => 9 / 10)
                  (gueGridK sz0 1) n p.1)) -
              mE 0 • (1 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ)) i j‖ ≤
            ((sz0.size n : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))}.indicator
          (fun ω' => ‖(green (gueH sz0 (fun _ => (1 - ouZeta (1 / 20)) * (9 / 10))
                (fun _ => 9 / 10) (gueGridK sz0 1) n p.1 ω')
                (zt 0 (gridTime (fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)) (fun _ => 9 / 10)
                  (gueGridK sz0 1) n p.1)) -
              mE 0 • (1 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ))
                p.2.1 p.2.2‖ ^ 2) ω)
      (fun n p ω => gueLmax sz0 (fun _ => 0) (fun _ => (1 - ouZeta (1 / 20)) * (9 / 10))
          (fun _ => 9 / 10) (gueGridK sz0 1) n 2 p.1 ω + (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹) :=
  gueGrid_entry_bound sz0 le_rfl (𝔠 := 1 / 6) (𝔡 := 1 / 10) sz0_admissible (κ := 1) one_pos 1
    (E := fun _ => 0) (t1 := fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)) (t0 := fun _ => 9 / 10)
    (fun n => by simp) (fun n => GridCheck.t1_pos) (fun n => t1_le) (fun n => by norm_num)
    (δ := fun n => ((sz0.size n : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)))
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) (c₀ := 1 / 4) (by norm_num)
    (Eventually.of_forall fun n => le_rfl)

end RBM.Univ.GUEPhase.EntryGridInst

end
