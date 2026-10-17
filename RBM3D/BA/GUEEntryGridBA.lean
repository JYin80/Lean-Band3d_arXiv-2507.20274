/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GUEProcBA
import RBM3D.BA.GUEEntry2
import RBM3D.Universality.GUEPhase.EntryGrid

/-!
# BA-C5 row a: the grid form of Lemma 4.1 at block Anderson (UN-43 at BA)

Ticket T2519 (row a, target 4; DECISIONS §344 (4), §346, T2515 Decision (5)).  New BA leaf: no
merged file is edited.  Band twin: `Universality/GUEPhase/EntryGrid.lean`
(`map_gueH_eq_mixMat:118`, `gueGrid_entry_bound:518`).  Paper: the GUE phase of Thm 2.4
(`paper/tex/1_2_Intro_model_result.tex:566-570`, "essentially identical to [YY_25, Theorem 2.6]");
Lemma 4.1 (4.2)+(4.3) of [YY_25] at block Anderson is C3 b's `gueEntryMixBA`
(`BA/GUEEntry2.lean`, pin `GUEEntryMixBA`).

* `map_gueHBA_eq_mixMatBA` (text `T2519_MapMixBA` of the 1a-audit): under `Pgue (sz.withLam 0)`
  the BA grid path at step `k` has the law of C3 b's mixture `mixMatBA`
  (`g Ψ_I + √t₁ X_block + √(u_k - t₁) X_GUE`) under the BA carrier law
  `ouP (UNModel.band (sz.withLam 0)) n`: the band theorem at `sz.withLam 0`, translated by the
  deterministic `g Ψ_I`.
* `gueGrid_entry_boundBA`: Lemma 4.1 (4.2)+(4.3) on the BA grid, from `gueEntryMixBA` after the
  transfer of the one-time law.  On the a priori event `{‖G - M‖_max ≤ δ_n}`,
  `M = Mres (g Ψ_I) E m = M^{(B)} ⊗ 1`, the squared entry `|(G_k - M)_{ij}|²` is
  `≺ gueLmaxBA 2 + W^{-d}`.  The family premise is the one of `GUEEntryMixBA`
  (`∀ n, 0 < g n ≤ 𝔡⁻¹`, `BAReal`): the window is needed at every `n` by C3 b's text, so a
  consumer with an eventual window pads it first.

The helpers of `EntryGrid` that carry no band token (the grid times, the size and union
arithmetic, `EntryGrid_a/b`, `EntryGrid_params`, `EntryGrid_gueH_zero`, the measurability of the
inverse) are read by `open private`; the bad set in matrix space and its facts are re-derived for
`GUEEntry_llErr`, `GUEEntry_maxLoop`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open private EntryGrid_measurable_inv_apply EntryGrid_a EntryGrid_b EntryGrid_params EntryGrid_two_le_size
  EntryGrid_gridK_le EntryGrid_union_arith EntryGrid_gridTime_ge EntryGrid_gridTime_le EntryGrid_gridTime_sub
  EntryGrid_gridStep_nonneg EntryGrid_gueH_zero from RBM3D.Universality.GUEPhase.EntryGrid

noncomputable section

namespace RBM.BA

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Loop RBM.Univ RBM.Univ.GUEPhase
open scoped NNReal ENNReal

/-! ## 1. The one-time law of the BA grid path at step `k` -/

/-- **T2: the law of the BA grid path at step `k` is the law of the BA mixture** `g Ψ_I + √t₁ X_block + √(u_k - t₁) X_GUE` under
`ouP (UNModel.band (sz.withLam 0)) n` (text `T2519_MapMixBA`; twin of `map_gueH_eq_mixMat`, `EntryGrid:118`): the band theorem at
`sz.withLam 0` (`gueHBA = g Ψ_I + gueH`, `mixMatBA = g Ψ_I + mixMat`) pushed through the translation by `g Ψ_I`. -/
theorem map_gueHBA_eq_mixMatBA {d : ℕ} (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (ht1 : 0 ≤ t1 n) (ht10 : t1 n ≤ t0 n) :
    (Pgue (sz.withLam 0)).map (gueHBA sz g t1 t0 K n k) =
      (ouP (UNModel.band (sz.withLam 0)) n).map
        (mixMatBA sz n (g n) (t1 n) (gridTime t1 t0 K n k - t1 n)) := by
  set sh : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ →
      Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
    fun M => ((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + M with hsh
  have hshm : Measurable sh := (continuous_const.add continuous_id).measurable
  set gH : PathΩ (sz.withLam 0) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
    gueH (sz.withLam 0) t1 t0 K n k with hgH
  have hgHm : Measurable gH := gueH_measurable (sz.withLam 0) t1 t0 K n k
  set mX : Sizes.SeqΩ (sz.withLam 0) × Ω d ((sz.withLam 0).L n) ((sz.withLam 0).W n) →
      Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
    mixMat (sz.withLam 0) n (t1 n) (gridTime t1 t0 K n k - t1 n) with hmX
  have hmXm : Measurable mX := measurable_mixMat (sz.withLam 0) n _ _
  have hmap : (Pgue (sz.withLam 0)).map gH = (ouP (UNModel.band (sz.withLam 0)) n).map mX :=
    map_gueH_eq_mixMat (sz.withLam 0) t1 t0 K n k ht1 ht10
  calc (Pgue (sz.withLam 0)).map (gueHBA sz g t1 t0 K n k) = (Pgue (sz.withLam 0)).map (sh ∘ gH) := rfl
    _ = ((Pgue (sz.withLam 0)).map gH).map sh := (Measure.map_map hshm hgHm).symm
    _ = ((ouP (UNModel.band (sz.withLam 0)) n).map mX).map sh := by rw [hmap]
    _ = (ouP (UNModel.band (sz.withLam 0)) n).map (sh ∘ mX) := Measure.map_map hshm hmXm
    _ = (ouP (UNModel.band (sz.withLam 0)) n).map
          (mixMatBA sz n (g n) (t1 n) (gridTime t1 t0 K n k - t1 n)) := rfl

/-! ## 2. The bad set in matrix space and its facts

At the BA datum the entry error is C3 b's `GUEEntry_llErr` (`‖Gres H z_u true - M^{(B)} ⊗ 1‖` entrywise) and the 2-loop maximum is
`GUEEntry_maxLoop` (the `(+,-)` 2-loops of `H`), twins of `llErrMat` and `maxLoopPM`. -/

section MatrixSpace

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- `(green H z_u - M)_{ij}` has norm `GUEEntry_llErr` at `M = Mres (g Ψ_I) E m` (`BAMres_fine_apply`, `Im (E + m) ≠ 0`). -/
private theorem EntryGridBA_norm_green_sub_eq (g E : ℝ) (m : ℂ) (hw : ((E : ℂ) + m).im ≠ 0) (u : ℝ)
    (H : Matrix (Idx d L W) (Idx d L W) ℂ) (i j : Idx d L W) :
    ‖(green H (ztOf m E u) - Mres ((g : ℂ) • PsiI d L W) (E : ℂ) m) i j‖ = GUEEntry_llErr d L W g E m u H i j := by
  unfold GUEEntry_llErr
  rw [Matrix.sub_apply, BAMres_fine_apply d L W g (E : ℂ) m hw i j]
  have h : Gres H (ztOf m E u) true = green H (ztOf m E u) := by
    simp only [green, Gres, ↓reduceIte, Matrix.nonsing_inv_eq_ringInverse]
  rw [h]

private theorem EntryGridBA_maxLoop_le (m : ℂ) (E u : ℝ) (H : Matrix (Idx d L W) (Idx d L W) ℂ) :
    GUEEntry_maxLoop d L W m E u H ≤ RBM.Ind.loopMax d L W (blockMat d L W H) (ztOf m E u) 2 := by
  unfold GUEEntry_maxLoop
  refine Finset.sup'_le _ _ fun p _ => ?_
  have h : loopFine d L W H (ztOf m E u) ![true, false] ![p.1, p.2]
      = loopL d L W (blockMat d L W H) (ztOf m E u) (loopOf ![true, false] ![p.1, p.2]) := by
    simp only [loopFine, loopM_eq_loopL]
  rw [h]
  exact RBM.Ind.norm_gloop_le_loopMax (loopOf ![true, false] ![p.1, p.2]) (by simp [loopOf]) (by simp [loopOf])

private theorem EntryGridBA_maxLoop_nonneg (m : ℂ) (E u : ℝ) (H : Matrix (Idx d L W) (Idx d L W) ℂ) :
    0 ≤ GUEEntry_maxLoop d L W m E u H :=
  Finset.le_sup'_of_le (fun p : Zd d L × Zd d L => ‖loopFine d L W H (ztOf m E u) ![true, false] ![p.1, p.2]‖)
    (Finset.mem_univ ((0 : Zd d L), (0 : Zd d L))) (norm_nonneg _)

private theorem EntryGridBA_measurable_llErr (g E : ℝ) (m : ℂ) (u : ℝ) (i j : Idx d L W) :
    Measurable fun M : Matrix (Idx d L W) (Idx d L W) ℂ => GUEEntry_llErr d L W g E m u M i j := by
  have hM : Measurable fun M : Matrix (Idx d L W) (Idx d L W) ℂ =>
      M - ztOf m E u • (1 : Matrix (Idx d L W) (Idx d L W) ℂ) := (continuous_id.sub continuous_const).measurable
  have heq : ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, GUEEntry_llErr d L W g E m u M i j =
      ‖(M - ztOf m E u • (1 : Matrix (Idx d L W) (Idx d L W) ℂ))⁻¹ i j -
        (if (split d L W i).2 = (split d L W j).2 then
          BAMB d L g (E : ℂ) m (split d L W i).1 (split d L W j).1 else 0)‖ := by
    intro M
    unfold GUEEntry_llErr
    simp only [Gres, ↓reduceIte, Matrix.nonsing_inv_eq_ringInverse]
  simp only [heq]
  exact ((EntryGrid_measurable_inv_apply hM i j).sub measurable_const).norm

private theorem EntryGridBA_measurable_maxLoop (m : ℂ) (E u : ℝ) :
    Measurable fun M : Matrix (Idx d L W) (Idx d L W) ℂ => GUEEntry_maxLoop d L W m E u M := by
  have hloop : ∀ a b : Zd d L,
      Measurable fun M : Matrix (Idx d L W) (Idx d L W) ℂ => loopFine d L W M (ztOf m E u) ![true, false] ![a, b] :=
    fun a b => walk_measurable_loopFine d L W (ztOf m E u) ![true, false] ![a, b]
  have hsup : Measurable (Finset.univ.sup' (Finset.univ_nonempty (α := Zd d L × Zd d L))
      (fun (p : Zd d L × Zd d L) (M : Matrix (Idx d L W) (Idx d L W) ℂ) =>
        ‖loopFine d L W M (ztOf m E u) ![true, false] ![p.1, p.2]‖)) :=
    Finset.measurable_sup' Finset.univ_nonempty fun p _ => (hloop p.1 p.2).norm
  have heq : (fun M : Matrix (Idx d L W) (Idx d L W) ℂ => GUEEntry_maxLoop d L W m E u M) =
      Finset.univ.sup' (Finset.univ_nonempty (α := Zd d L × Zd d L))
        (fun (p : Zd d L × Zd d L) (M : Matrix (Idx d L W) (Idx d L W) ℂ) =>
          ‖loopFine d L W M (ztOf m E u) ![true, false] ![p.1, p.2]‖) := by
    funext M
    simp only [GUEEntry_maxLoop, Finset.sup'_apply]
  rw [heq]
  exact hsup

/-- The single-`k` bad set of `GUEEntryMixBA` in matrix space (`s = N^τ`, `δ`, the flow datum `(g, E, m)`, time `u`). -/
private def EntryGridBA_badMat (d L W : ℕ) [NeZero L] [NeZero W] (g E : ℝ) (m : ℂ) (u δ s : ℝ) :
    Set (Matrix (Idx d L W) (Idx d L W) ℂ) :=
  {M | ∃ i j : Idx d L W, s * (GUEEntry_maxLoop d L W m E u M + (((W : ℕ) : ℝ) ^ d)⁻¹) <
    (if ∀ x y, GUEEntry_llErr d L W g E m u M x y ≤ δ then GUEEntry_llErr d L W g E m u M i j ^ 2 else 0)}

private theorem EntryGridBA_measurableSet_badMat (g E : ℝ) (m : ℂ) (u δ s : ℝ) :
    MeasurableSet (EntryGridBA_badMat d L W g E m u δ s) := by
  have hll : ∀ x y : Idx d L W,
      Measurable fun M : Matrix (Idx d L W) (Idx d L W) ℂ => GUEEntry_llErr d L W g E m u M x y :=
    fun x y => EntryGridBA_measurable_llErr g E m u x y
  have hcond : MeasurableSet {M : Matrix (Idx d L W) (Idx d L W) ℂ | ∀ x y, GUEEntry_llErr d L W g E m u M x y ≤ δ} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun x => MeasurableSet.iInter fun y => measurableSet_le (hll x y) measurable_const
  have hrhs : ∀ i j : Idx d L W, Measurable fun M : Matrix (Idx d L W) (Idx d L W) ℂ =>
      (if ∀ x y, GUEEntry_llErr d L W g E m u M x y ≤ δ then GUEEntry_llErr d L W g E m u M i j ^ 2 else 0) :=
    fun i j => Measurable.ite hcond ((hll i j).pow_const 2) measurable_const
  have hlhs : Measurable fun M : Matrix (Idx d L W) (Idx d L W) ℂ =>
      s * (GUEEntry_maxLoop d L W m E u M + (((W : ℕ) : ℝ) ^ d)⁻¹) :=
    measurable_const.mul ((EntryGridBA_measurable_maxLoop m E u).add measurable_const)
  have heq : EntryGridBA_badMat d L W g E m u δ s = ⋃ i : Idx d L W, ⋃ j : Idx d L W,
      {M : Matrix (Idx d L W) (Idx d L W) ℂ |
        s * (GUEEntry_maxLoop d L W m E u M + (((W : ℕ) : ℝ) ^ d)⁻¹) <
        (if ∀ x y, GUEEntry_llErr d L W g E m u M x y ≤ δ then GUEEntry_llErr d L W g E m u M i j ^ 2 else 0)} := by
    ext M
    simp [EntryGridBA_badMat]
  rw [heq]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j => measurableSet_lt hlhs (hrhs i j)

/-- Zero time: `G_0 = M` at `H = g Ψ_I` (`z_0 = E + m`), so every entry error vanishes and `g Ψ_I ∉` the bad set of time `0`. -/
private theorem EntryGridBA_zero_not_mem_badMat (g E : ℝ) (m : ℂ) (hw : ((E : ℂ) + m).im ≠ 0) (δ s : ℝ) (hs : 0 ≤ s) :
    ((g : ℂ) • PsiI d L W) ∉ EntryGridBA_badMat d L W g E m 0 δ s := by
  rintro ⟨i, j, h⟩
  have hll : ∀ x y : Idx d L W, GUEEntry_llErr d L W g E m 0 ((g : ℂ) • PsiI d L W) x y = 0 := by
    intro x y
    rw [← EntryGridBA_norm_green_sub_eq g E m hw 0 _ x y, Matrix.sub_apply]
    have hz : green ((g : ℂ) • PsiI d L W) (ztOf m E 0) = Mres ((g : ℂ) • PsiI d L W) (E : ℂ) m := by
      simp only [green, Mres, ztOf, Complex.ofReal_zero, sub_zero, one_mul, Matrix.nonsing_inv_eq_ringInverse]
    rw [hz, sub_self, norm_zero]
  have hrhs : (if ∀ x y, GUEEntry_llErr d L W g E m 0 ((g : ℂ) • PsiI d L W) x y ≤ δ
      then GUEEntry_llErr d L W g E m 0 ((g : ℂ) • PsiI d L W) i j ^ 2 else 0) = 0 := by
    split_ifs
    · rw [hll i j]; norm_num
    · rfl
  rw [hrhs] at h
  have h0 : 0 ≤ s * (GUEEntry_maxLoop d L W m E 0 ((g : ℂ) • PsiI d L W) + (((W : ℕ) : ℝ) ^ d)⁻¹) :=
    mul_nonneg hs (add_nonneg (EntryGridBA_maxLoop_nonneg m E 0 _) (by positivity))
  exact absurd h (not_lt.2 h0)

end MatrixSpace

/-! ## 3. Lemma 4.1 on the BA grid -/

section Main

variable {d : ℕ}

private theorem EntryGridBA_measurable_gueHBA (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) :
    Measurable (gueHBA sz g t1 t0 K n k) := by
  have hshm : Measurable fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      ((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + M := (continuous_const.add continuous_id).measurable
  exact hshm.comp (gueH_measurable (sz.withLam 0) t1 t0 K n k)

private theorem EntryGridBA_measurable_mixMatBA (sz : Sizes d) (n : ℕ) (g a b : ℝ) : Measurable (mixMatBA sz n g a b) := by
  have hshm : Measurable fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      (g : ℂ) • PsiI d (sz.L n) (sz.W n) + M := (continuous_const.add continuous_id).measurable
  exact hshm.comp (measurable_mixMat (sz.withLam 0) n a b)

/-- The preimage form of T2 at BA: for a measurable set `B` of matrices, `Pgue` of the event `{gueHBA_k ∈ B}` is the
`ouP`-probability of `{mixMatBA ∈ B}`. -/
private theorem EntryGridBA_pgue_preimage (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ht1 : 0 ≤ t1 n)
    (ht10 : t1 n ≤ t0 n) {B : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)}
    (hB : MeasurableSet B) :
    Pgue (sz.withLam 0) (gueHBA sz g t1 t0 K n k ⁻¹' B) =
      ouP (UNModel.band (sz.withLam 0)) n (mixMatBA sz n (g n) (t1 n) (gridTime t1 t0 K n k - t1 n) ⁻¹' B) := by
  calc Pgue (sz.withLam 0) (gueHBA sz g t1 t0 K n k ⁻¹' B)
      = ((Pgue (sz.withLam 0)).map (gueHBA sz g t1 t0 K n k)) B :=
        (Measure.map_apply (EntryGridBA_measurable_gueHBA sz g t1 t0 K n k) hB).symm
    _ = ((ouP (UNModel.band (sz.withLam 0)) n).map
          (mixMatBA sz n (g n) (t1 n) (gridTime t1 t0 K n k - t1 n))) B := by
        rw [map_gueHBA_eq_mixMatBA sz g t1 t0 K n k ht1 ht10]
    _ = ouP (UNModel.band (sz.withLam 0)) n (mixMatBA sz n (g n) (t1 n) (gridTime t1 t0 K n k - t1 n) ⁻¹' B) :=
        Measure.map_apply (EntryGridBA_measurable_mixMatBA sz n _ _ _) hB

/-- At grid time `0` (`t₁ = 0` and `k = 0` or `Δ = 0`) the BA path is the deterministic `g Ψ_I`. -/
private theorem EntryGridBA_gueHBA_zero (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ht1 : 0 ≤ t1 n)
    (ht10 : t1 n ≤ t0 n) (hu : gridTime t1 t0 K n k = 0) (ω : PathΩ (sz.withLam 0)) :
    gueHBA sz g t1 t0 K n k ω = ((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) := by
  have h := EntryGrid_gueH_zero (sz.withLam 0) t1 t0 K n k ht1 ht10 hu ω
  unfold gueHBA
  rw [h, add_zero]
  rfl

/-- The pointwise step of `gueGrid_entry_boundBA` (twin of `EntryGrid_pointwise`): if `ω` is in the bad event of the entry `(i, j)`
at grid step `k`, then `gueHBA_k ω` lies in the bad set of matrix space (`GUEEntry_maxLoop ≤ gueLmaxBA 2`,
`‖(green M z - M^{(B)} ⊗ 1)_{ij}‖ = GUEEntry_llErr`). -/
private theorem EntryGridBA_pointwise (sz : Sizes d) (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (n k : ℕ)
    (hw : ((E n : ℂ) + m n).im ≠ 0) (ω : PathΩ (sz.withLam 0)) (i j : Idx d (sz.L n) (sz.W n)) (s : ℝ) (hs : 0 ≤ s)
    (hlt : s * (gueLmaxBA sz g E t1 t0 m K n 2 k ω + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) <
      {ω' : PathΩ (sz.withLam 0) | ∀ i j : Idx d (sz.L n) (sz.W n),
          ‖(green (gueHBA sz g t1 t0 K n k ω') (ztOf (m n) (E n) (gridTime t1 t0 K n k)) -
            Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) i j‖ ≤ δ n}.indicator
        (fun ω' => ‖(green (gueHBA sz g t1 t0 K n k ω') (ztOf (m n) (E n) (gridTime t1 t0 K n k)) -
            Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) i j‖ ^ 2) ω) :
    gueHBA sz g t1 t0 K n k ω ∈
      EntryGridBA_badMat d (sz.L n) (sz.W n) (g n) (E n) (m n) (gridTime t1 t0 K n k) (δ n) s := by
  have hnorm : ∀ (M' : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (x y : Idx d (sz.L n) (sz.W n)),
      ‖(green M' (ztOf (m n) (E n) (gridTime t1 t0 K n k)) -
          Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) x y‖
        = GUEEntry_llErr d (sz.L n) (sz.W n) (g n) (E n) (m n) (gridTime t1 t0 K n k) M' x y :=
    fun M' x y => EntryGridBA_norm_green_sub_eq (g n) (E n) (m n) hw _ M' x y
  have hle : s * (GUEEntry_maxLoop d (sz.L n) (sz.W n) (m n) (E n) (gridTime t1 t0 K n k)
        (gueHBA sz g t1 t0 K n k ω) + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹)
      ≤ s * (gueLmaxBA sz g E t1 t0 m K n 2 k ω + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) :=
    mul_le_mul_of_nonneg_left (add_le_add_left (EntryGridBA_maxLoop_le _ _ _ _) _) hs
  by_cases hall : ∀ x y, GUEEntry_llErr d (sz.L n) (sz.W n) (g n) (E n) (m n) (gridTime t1 t0 K n k)
      (gueHBA sz g t1 t0 K n k ω) x y ≤ δ n
  · have hmem : ω ∈ {ω' : PathΩ (sz.withLam 0) | ∀ i j : Idx d (sz.L n) (sz.W n),
        ‖(green (gueHBA sz g t1 t0 K n k ω') (ztOf (m n) (E n) (gridTime t1 t0 K n k)) -
          Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) i j‖ ≤ δ n} := by
      intro x y
      rw [hnorm]
      exact hall x y
    rw [Set.indicator_of_mem hmem] at hlt
    refine ⟨i, j, ?_⟩
    simp only [hall, implies_true, ↓reduceIte]
    refine lt_of_le_of_lt hle (lt_of_lt_of_eq hlt ?_)
    simp only [hnorm]
  · have hnot : ω ∉ {ω' : PathΩ (sz.withLam 0) | ∀ i j : Idx d (sz.L n) (sz.W n),
        ‖(green (gueHBA sz g t1 t0 K n k ω') (ztOf (m n) (E n) (gridTime t1 t0 K n k)) -
          Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) i j‖ ≤ δ n} := by
      intro h
      apply hall
      intro x y
      rw [← hnorm]
      exact h x y
    rw [Set.indicator_of_notMem hnot] at hlt
    have h0 : 0 ≤ s * (gueLmaxBA sz g E t1 t0 m K n 2 k ω + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) :=
      mul_nonneg hs (add_nonneg (by unfold gueLmaxBA; exact RBM.Ind.loopMax_nonneg 2) (by positivity))
    exact absurd hlt (not_lt.2 h0)

/-- **`gueGrid_entry_boundBA'`** (T2519 Amend 4 item 2): `gueGrid_entry_boundBA` with the family premise split into `BAReal` at every `n`
and the coupling window `0 < g n ≤ 𝔡⁻¹` eventually; the proof of `gueGrid_entry_boundBA` moved here, from `gueEntryMixBA'`. -/
theorem gueGrid_entry_boundBA' (sz : Sizes d) (hd : 3 ≤ d) {𝔠 𝔡 κ : ℝ} (hadm : sz.Admissible 𝔠 𝔡) (hκ : 0 < κ) (n0 : ℕ)
    {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ} (hr : ∀ n, BAReal d (sz.L n) (g n) κ (E n) (m n))
    (hwin : ∀ᶠ n in atTop, 0 < g n ∧ g n ≤ 𝔡⁻¹)
    (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1) {δ : ℕ → ℝ} (hδ0 : ∀ n, 0 ≤ δ n)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hδ : ∀ᶠ n in atTop, δ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-c₀)) :
    StochDomAt (Pgue (sz.withLam 0)) sz.size
      (fun n (p : Fin (gueGridK sz n0 n + 1) × (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))) ω =>
        {ω' : PathΩ (sz.withLam 0) | ∀ i j : Idx d (sz.L n) (sz.W n),
            ‖(green (gueHBA sz g t1 t0 (gueGridK sz n0) n p.1 ω')
                (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n p.1)) -
              Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) i j‖ ≤ δ n}.indicator
          (fun ω' => ‖(green (gueHBA sz g t1 t0 (gueGridK sz n0) n p.1 ω')
                (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n p.1)) -
              Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) p.2.1 p.2.2‖ ^ 2) ω)
      (fun n p ω => gueLmaxBA sz g E t1 t0 m (gueGridK sz n0) n 2 p.1 ω + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) := by
  intro τ hτ D hD
  have hd1 : 1 ≤ d := by omega
  have hD' : 0 < D + 1 + ((64 * n0 + 128 : ℕ) : ℝ) := by positivity
  have hmix := gueEntryMixBA' hd 𝔠 𝔡 sz hadm κ hκ g E m hr hwin (64 * n0 + 128) (gueGridK sz n0)
    (EntryGrid_gridK_le sz hd1 n0) (fun n k => EntryGrid_a t1 t0 (gueGridK sz n0) n k)
    (fun n k => EntryGrid_b t1 t0 (gueGridK sz n0) n k)
    (fun n k => EntryGrid_params t1 t0 (gueGridK sz n0) n k (ht1 n) (ht10 n) (ht0 n)
      (gueGridK_ne_zero sz n0 n) (Nat.lt_succ_iff.1 k.2))
    c₀ δ hc₀ hδ0 hδ τ (D + 1 + ((64 * n0 + 128 : ℕ) : ℝ)) hτ hD'
  filter_upwards [hmix] with n hn
  have hN2 := EntryGrid_two_le_size sz hd1 n
  have hs0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hw : ((E n : ℂ) + m n).im ≠ 0 := by
    have := (hr n).1.1
    simpa using this.ne'
  -- Step 1: the bad event is inside the union over the grid of the preimages of the matrix bad sets
  refine le_trans (measure_mono (t := ⋃ k : Fin (gueGridK sz n0 n + 1),
    gueHBA sz g t1 t0 (gueGridK sz n0) n k ⁻¹' EntryGridBA_badMat d (sz.L n) (sz.W n) (g n) (E n) (m n)
      (gridTime t1 t0 (gueGridK sz n0) n k) (δ n) (((sz.size n : ℕ) : ℝ) ^ τ)) ?_) ?_
  · rintro ω ⟨⟨k, i, j⟩, hlt⟩
    exact Set.mem_iUnion.2
      ⟨k, EntryGridBA_pointwise sz g E t1 t0 m (gueGridK sz n0) δ n k hw ω i j _ hs0 hlt⟩
  -- Step 2: each grid point costs at most the `ouP`-probability of the event of `gueEntryMixBA`
  have hk : ∀ k : Fin (gueGridK sz n0 n + 1),
      Pgue (sz.withLam 0) (gueHBA sz g t1 t0 (gueGridK sz n0) n k ⁻¹' EntryGridBA_badMat d (sz.L n) (sz.W n)
        (g n) (E n) (m n) (gridTime t1 t0 (gueGridK sz n0) n k) (δ n) (((sz.size n : ℕ) : ℝ) ^ τ))
      ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D + 1 + ((64 * n0 + 128 : ℕ) : ℝ)))) := by
    intro k
    by_cases hpos : 0 < gridTime t1 t0 (gueGridK sz n0) n k
    · rw [EntryGridBA_pgue_preimage sz g t1 t0 _ n k (ht1 n) (ht10 n)
        (EntryGridBA_measurableSet_badMat _ _ _ _ _ _)]
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
      have hempty : gueHBA sz g t1 t0 (gueGridK sz n0) n k ⁻¹' EntryGridBA_badMat d (sz.L n) (sz.W n) (g n) (E n)
          (m n) (gridTime t1 t0 (gueGridK sz n0) n k) (δ n) (((sz.size n : ℕ) : ℝ) ^ τ) = ∅ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
        rw [EntryGridBA_gueHBA_zero sz g t1 t0 _ n k (ht1 n) (ht10 n) h0 ω, h0]
        exact EntryGridBA_zero_not_mem_badMat (g n) (E n) (m n) hw (δ n) _ hs0
      rw [hempty, measure_empty]
      exact zero_le
  -- Step 3: the union bound over the `K_n + 1` grid points and the arithmetic
  calc Pgue (sz.withLam 0) (⋃ k : Fin (gueGridK sz n0 n + 1),
        gueHBA sz g t1 t0 (gueGridK sz n0) n k ⁻¹' EntryGridBA_badMat d (sz.L n) (sz.W n) (g n) (E n) (m n)
          (gridTime t1 t0 (gueGridK sz n0) n k) (δ n) (((sz.size n : ℕ) : ℝ) ^ τ))
      ≤ ∑ k : Fin (gueGridK sz n0 n + 1),
          Pgue (sz.withLam 0) (gueHBA sz g t1 t0 (gueGridK sz n0) n k ⁻¹' EntryGridBA_badMat d (sz.L n) (sz.W n)
            (g n) (E n) (m n) (gridTime t1 t0 (gueGridK sz n0) n k) (δ n) (((sz.size n : ℕ) : ℝ) ^ τ)) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _k : Fin (gueGridK sz n0 n + 1),
          ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D + 1 + ((64 * n0 + 128 : ℕ) : ℝ)))) :=
        Finset.sum_le_sum fun k _ => hk k
    _ = ((gueGridK sz n0 n + 1 : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D + 1 + ((64 * n0 + 128 : ℕ) : ℝ)))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) :=
        EntryGrid_union_arith _ _ _ hN2 (EntryGrid_gridK_le sz hd1 n0 n) D


end Main

/-! ## 4. Compiled nonempty instances

`d = 3`, `sz0` (`L_n = 4 (n + 1)`, `W_n = (2 (n + 1))^5`, `N_0 = 2^21`, admissible at `(𝔠, 𝔡) = (1/6, 1/10)`), the BA flow datum of `sz0`
at every `n` (`g = BAflowLam0`, `E = BAflowEs`, `m = BAmF`; `BAReal` at `κ = 1/2`, `0 < g ≤ 1 ≤ 𝔡⁻¹`), the grid `t₁ = 1/4`, `t₀ = 1/2`,
`K = gueGridK sz0 2`, the a priori threshold `δ_n = N^{-1/20}`, `c₀ = 1/20`.  Every hypothesis is discharged. -/

end RBM.BA

end
