/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.GUEPhase.Grid
import RBM3D.Universality.GUEPhase.Bootstrap
import RBM3D.Universality.GUEPhase.Generator
import RBM3D.Universality.GUEPhase.KPrim
import RBM3D.Universality.GUEPhase.EntryDet
import RBM3D.Induction.Split
import RBM3D.Induction.ConArgDet
import RBM3D.Path.Stop

/-!
# The process layer of the §7.2 random layer on the GUE-phase grid, `d ≥ 3` (T2322, UN-31a)

Port of RBM2D `Universality/GUEPhase/Proc.lean` at `81fca44` (`:1-860`; `:862-1424`,
`gueKproc_detDom`, is T2323 = UN-31b).  Paper: the GUE phase of Thm 2.4
(`paper/tex/1_2_Intro_model_result.tex:566-570`, "essentially identical to [YY_25, Theorem 2.6]");
the equation numbers (6.4), (5.117) are those of the `d = 2` paper `[YY_25]` as quoted in the
header of `Induction/Split.lean`, and (7.25)-(7.36) those of [YY_25] §7.2 as in the header of
`GUEPhase/Grid.lean`.

On the size scale:

* the a priori threshold `gueDelta` (`δ_n = (sz.size n)^{-τU/4}`), the tent function `gueTent`, the
  piecewise-linear interpolation `gueInterp`, the entry deviation `gueDev`, the freezing index
  `gueStop`;
* the loop maximum / deviation / deterministic running maximum `gueLmax`, `gueDmax`, `gueKbar` at
  the grid steps, and the stopped interpolated processes `gueLproc`, `gueDproc`, `gueKproc`;
* their structural facts `gueLproc_nonneg`, …, `gueLproc_time`, `gueDproc_time`;
* `gueLoopMax_odd_succ_le`, `gueLoopMax_four_mul_le` ((6.4) and (5.117)), the Ward lower bound
  `gue_inv_W_le_loopMax` (`W^{-d} ≤ 2 L^{d-2} g² L₂`), the bound `norm_egtNGUE_le` on
  `𝓔^{(G̃)}`, the one-step jump `gueDev_succ_le` of the entry deviation by the resolvent identity.

What changes from `d = 2` (renaming rules of `Induction/LoopGenN.lean:15-20` and of the merged
`GUEPhase/Grid.lean`): `d : Sizes` becomes `sz : Sizes d`; `Z2 L` becomes `Zd d L`;
`BlockIndex L W` becomes `Vtx d L W`; `Idx (d.L n) (d.W n)` becomes `Idx d (sz.L n) (sz.W n)`;
`spectralZ`/`spectralM` become `zt`/`mE`; `gloop L W (blockMat M)` becomes
`loopL d L W (blockMat d L W M)`; `RBM.Ind.loopMax L W` becomes `RBM.Ind.loopMax d L W`;
`N = sz.size n = (W L)^d`.  Only two statements are dimension-sensitive.

* `gue_inv_W_le_loopMax`: the Ward step `inv_N_le_maxLoopPM` gives
  `W^{-d} ≤ 2 L^d (1 - u) · maxLoopPM`; with `hell` the `ellT_eq_L` condition `L² (1 - u) ≤ g²`
  (`Bootstrap.lean:148`) and `L^d ≤ L^{d-2} L²`, the conclusion is `(W⁻¹)^d ≤ 2 L^{d-2} g² L₂`
  (RBM2D: `W^{-2} ≤ 2 L₂` under `L² (1 - u) ≤ 1`).
* `norm_egtNGUE_le`: `SBgue = L^{-d}`, the label sums over `Zd d L` have `L^d` terms, the
  prefactor is `W^d`, so `W^d · (L^d · L^d) · L^{-d} = (W L)^d`.

Everything else (`gueLoopMax_*`, `gueDev_succ_le`, the interpolation helpers) is dimension-free:
`‖G‖ ≤ η⁻¹` through the merged `norm_Gsig_le_inv_eta` (the replacement of RBM2D `norm_green_le`).
Helpers are `private` or carry the prefix `Proc_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Univ
open scoped NNReal ENNReal

variable {d : ℕ} (sz : Sizes d)

/-! ### Definitions -/

/-- The a priori threshold `δ_n = N^{-τU/4}`, `N = sz.size n`. -/
def gueDelta (τU : ℝ) (n : ℕ) : ℝ := ((sz.size n : ℕ) : ℝ) ^ (-(τU / 4))

/-- The tent function at the grid time `u_k`. -/
def gueTent (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (t : ℝ) : ℝ :=
  max 0 (1 - |t - gridTime t1 t0 K n k| / gridStep t1 t0 K n)

/-- Piecewise-linear interpolation of grid values (`f 0` if `Δ = 0`). -/
def gueInterp (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (f : ℕ → ℝ) (t : ℝ) : ℝ :=
  if gridStep t1 t0 K n = 0 then f 0
  else ∑ k ∈ Finset.range (K n + 1), f k * gueTent t1 t0 K n k t

/-- `max_{i,j} |(G_k - m)_{ij}|` at the grid step `k`. -/
def gueDev (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz) : ℝ :=
  ⨆ ij : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n),
    ‖(green (gueH sz t1 t0 K n k ω) (zt (E n) (gridTime t1 t0 K n k)) -
        mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) ij.1 ij.2‖

/-- The freezing index: the first grid step with `gueDev ≥ δ_n` (else `K n`). -/
def gueStop (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (n : ℕ) (ω : PathΩ sz) : ℕ :=
  firstHit (fun k ω' => gueDev sz E t1 t0 K n k ω') (δ n) (K n) ω

/-- `L^{(m)}_k = max_{σ,a} |L_{σ,a}|` at the grid step `k`. -/
def gueLmax (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n m k : ℕ) (ω : PathΩ sz) : ℝ :=
  RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k ω))
    (zt (E n) (gridTime t1 t0 K n k)) m

/-- `D^{(m)}_k = max_{x} |L_x - K̃_x|` at the grid step `k`. -/
def gueDmax (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ)
    (n m k : ℕ) (ω : PathΩ sz) : ℝ :=
  ⨆ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
    ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k ω))
        (zt (E n) (gridTime t1 t0 K n k)) (loopOf x.1 x.2) -
      Kt n (gridTime t1 t0 K n k) (loopOf x.1 x.2)‖

/-- `K̄^{(m)}_k = max_{j ≤ k} max_x |K̃(u_j, x)|`, the deterministic running maximum. -/
def gueKbar (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ)
    (n m k : ℕ) : ℝ :=
  ⨆ j : Fin (k + 1), ⨆ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
    ‖Kt n (gridTime t1 t0 K n j) (loopOf x.1 x.2)‖

/-- The stopped, interpolated `Lm` fed to `eq727GEAt`/`eq728GAt`. -/
def gueLproc (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (n m : ℕ) (t : ℝ) (ω : PathΩ sz) : ℝ :=
  gueInterp t1 t0 K n (fun k => gueLmax sz E t1 t0 K n m (min k (gueStop sz E t1 t0 K δ n ω)) ω) t

/-- The stopped, interpolated `Dm` fed to `eq727GEAt`/`eq728GAt`. -/
def gueDproc (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (n m : ℕ) (t : ℝ) (ω : PathΩ sz) : ℝ :=
  gueInterp t1 t0 K n
    (fun k => gueDmax sz E t1 t0 K Kt n m (min k (gueStop sz E t1 t0 K δ n ω)) ω) t

/-- The deterministic `Km` fed to `eq727GEAt`. -/
def gueKproc (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ)
    (n m : ℕ) (t : ℝ) : ℝ :=
  gueInterp t1 t0 K n (fun k => gueKbar sz t1 t0 K Kt n m k) t

/-! ### Generic helpers for `gueInterp` -/

section GueInterpHelpers

variable {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ}

private theorem Proc_gueTent_nonneg (k : ℕ) (t : ℝ) : 0 ≤ gueTent t1 t0 K n k t :=
  le_max_left _ _

private theorem Proc_gueInterp_add (f g : ℕ → ℝ) (t : ℝ) :
    gueInterp t1 t0 K n (fun k => f k + g k) t
      = gueInterp t1 t0 K n f t + gueInterp t1 t0 K n g t := by
  unfold gueInterp
  split_ifs with h0
  · rfl
  · rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring

private theorem Proc_gueInterp_mono {f g : ℕ → ℝ} (h : ∀ k, f k ≤ g k) (t : ℝ) :
    gueInterp t1 t0 K n f t ≤ gueInterp t1 t0 K n g t := by
  unfold gueInterp
  split_ifs with h0
  · exact h 0
  · exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (h k) (Proc_gueTent_nonneg k t)

private theorem Proc_gueInterp_nonneg {f : ℕ → ℝ} (h : ∀ k, 0 ≤ f k) (t : ℝ) :
    0 ≤ gueInterp t1 t0 K n f t := by
  unfold gueInterp
  split_ifs with h0
  · exact h 0
  · exact Finset.sum_nonneg fun k _ => mul_nonneg (h k) (Proc_gueTent_nonneg k t)

private theorem Proc_gueTent_continuous (j : ℕ) : Continuous (gueTent t1 t0 K n j) := by
  unfold gueTent
  fun_prop

private theorem Proc_gueInterp_continuousOn (f : ℕ → ℝ) :
    ContinuousOn (fun t => gueInterp t1 t0 K n f t) (Set.Icc (t1 n) (t0 n)) := by
  unfold gueInterp
  by_cases h0 : gridStep t1 t0 K n = 0
  · simp only [ite_eq_left h0]
    exact continuousOn_const
  · simp only [ite_eq_right h0]
    exact (continuous_finsetSum _ fun k _ =>
      continuous_const.mul (Proc_gueTent_continuous k)).continuousOn

private theorem Proc_gueInterp_sqrt_mul_le {a b : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (t : ℝ) :
    gueInterp t1 t0 K n (fun k => Real.sqrt (a k * b k)) t
      ≤ Real.sqrt (gueInterp t1 t0 K n a t * gueInterp t1 t0 K n b t) := by
  unfold gueInterp
  split_ifs with h0
  · exact le_refl _
  · have hw : ∀ k, 0 ≤ gueTent t1 t0 K n k t := fun k => Proc_gueTent_nonneg k t
    rw [Real.sqrt_mul (Finset.sum_nonneg fun k _ => mul_nonneg (ha k) (hw k))]
    have hcs := Real.sum_sqrt_mul_sqrt_le (Finset.range (K n + 1))
      (f := fun k => a k * gueTent t1 t0 K n k t) (g := fun k => b k * gueTent t1 t0 K n k t)
      (fun k => mul_nonneg (ha k) (hw k)) (fun k => mul_nonneg (hb k) (hw k))
    have heq : ∀ k, Real.sqrt (a k * gueTent t1 t0 K n k t)
        * Real.sqrt (b k * gueTent t1 t0 K n k t)
        = Real.sqrt (a k * b k) * gueTent t1 t0 K n k t := by
      intro k
      rw [← Real.sqrt_mul (mul_nonneg (ha k) (hw k)),
        show a k * gueTent t1 t0 K n k t * (b k * gueTent t1 t0 K n k t)
          = (a k * b k) * (gueTent t1 t0 K n k t) ^ 2 by ring,
        Real.sqrt_mul (mul_nonneg (ha k) (hb k)), Real.sqrt_sq (hw k)]
    calc ∑ k ∈ Finset.range (K n + 1), Real.sqrt (a k * b k) * gueTent t1 t0 K n k t
        = ∑ k ∈ Finset.range (K n + 1),
            Real.sqrt (a k * gueTent t1 t0 K n k t) * Real.sqrt (b k * gueTent t1 t0 K n k t) :=
          Finset.sum_congr rfl fun k _ => (heq k).symm
      _ ≤ Real.sqrt (∑ k ∈ Finset.range (K n + 1), a k * gueTent t1 t0 K n k t) *
            Real.sqrt (∑ k ∈ Finset.range (K n + 1), b k * gueTent t1 t0 K n k t) := hcs

/-- Tent functions form a Kronecker delta at grid points, provided the grid is nondegenerate
(`Δ ≠ 0`) and `t1 n ≤ t0 n` (so `Δ ≥ 0`). -/
private theorem Proc_gueTent_time_eq (ht10 : t1 n ≤ t0 n) (hstep : gridStep t1 t0 K n ≠ 0)
    (j k : ℕ) :
    gueTent t1 t0 K n j (gridTime t1 t0 K n k) = if j = k then 1 else 0 := by
  have hK0 : (K n : ℝ) ≠ 0 := by
    intro hc
    apply hstep
    unfold gridStep
    rw [hc, div_zero]
  have hKpos : (0:ℝ) < (K n : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hK0)
  have hΔ0 : 0 ≤ gridStep t1 t0 K n := by
    unfold gridStep
    exact div_nonneg (by linarith) hKpos.le
  have hΔpos : 0 < gridStep t1 t0 K n := hΔ0.lt_of_ne (Ne.symm hstep)
  have hdiff : gridTime t1 t0 K n k - gridTime t1 t0 K n j
      = ((k : ℝ) - (j : ℝ)) * gridStep t1 t0 K n := by
    unfold gridTime; ring
  have habs : |gridTime t1 t0 K n k - gridTime t1 t0 K n j|
      = |(k : ℝ) - (j : ℝ)| * gridStep t1 t0 K n := by
    rw [hdiff, abs_mul, abs_of_pos hΔpos]
  unfold gueTent
  rw [habs, mul_div_assoc, div_self hΔpos.ne', mul_one]
  by_cases hjk : j = k
  · simp [hjk]
  · have h1 : (1 : ℝ) ≤ |(k : ℝ) - (j : ℝ)| := by
      have hne : (k : ℝ) ≠ (j : ℝ) := by
        intro hc; exact hjk (by exact_mod_cast hc.symm)
      rcases lt_or_gt_of_ne hne with h | h
      · rw [abs_of_neg (by linarith)]
        have : (1:ℝ) ≤ (j:ℝ) - (k:ℝ) := by
          have hlt : (k:ℕ) < (j:ℕ) := by exact_mod_cast (by linarith : (k:ℝ) < (j:ℝ))
          have : (k:ℕ) + 1 ≤ (j:ℕ) := hlt
          have := (Nat.cast_le (α := ℝ)).2 this
          push_cast at this
          linarith
        linarith
      · rw [abs_of_pos (by linarith)]
        have hlt : (j:ℕ) < (k:ℕ) := by exact_mod_cast (by linarith : (j:ℝ) < (k:ℝ))
        have hle : (j:ℕ) + 1 ≤ (k:ℕ) := hlt
        have := (Nat.cast_le (α := ℝ)).2 hle
        push_cast at this
        linarith
    simp only [hjk, ite_false]
    have : 1 - |(k:ℝ) - (j:ℝ)| ≤ 0 := by linarith
    rw [max_eq_left_iff.2 this]

private theorem Proc_gueInterp_time {f : ℕ → ℝ} (hconst : gridStep t1 t0 K n = 0 → ∀ k', f k' = f 0)
    (ht10 : t1 n ≤ t0 n) {k : ℕ} (hk : k ≤ K n) :
    gueInterp t1 t0 K n f (gridTime t1 t0 K n k) = f k := by
  unfold gueInterp
  split_ifs with h0
  · exact (hconst h0 k).symm
  · rw [Finset.sum_eq_single k]
    · rw [Proc_gueTent_time_eq ht10 h0 k k, ite_eq_left rfl, mul_one]
    · intro j hj hjk
      rw [Proc_gueTent_time_eq ht10 h0 j k, ite_eq_right hjk, mul_zero]
    · intro hk'
      exact absurd (Finset.mem_range.2 (by omega)) hk'

end GueInterpHelpers

/-! ### Constancy of the grid processes when `Δ = 0` -/

section GueConstZero

variable {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ}

private theorem Proc_gueTime_const_of_step_zero (h0 : gridStep t1 t0 K n = 0) (k : ℕ) :
    gridTime t1 t0 K n k = t1 n := by
  unfold gridTime; rw [h0]; ring

private theorem Proc_gueH_const_of_step_zero (h0 : gridStep t1 t0 K n = 0) (k : ℕ)
    (ω : PathΩ sz) : gueH sz t1 t0 K n k ω = gueH sz t1 t0 K n 0 ω := by
  unfold gueH
  rw [h0, zero_div, Real.sqrt_zero]
  simp

variable {E : ℕ → ℝ}

private theorem Proc_gueLmax_const_of_step_zero (h0 : gridStep t1 t0 K n = 0) (m k : ℕ)
    (ω : PathΩ sz) :
    gueLmax sz E t1 t0 K n m k ω = gueLmax sz E t1 t0 K n m 0 ω := by
  unfold gueLmax
  rw [Proc_gueH_const_of_step_zero sz h0 k ω, Proc_gueTime_const_of_step_zero h0 k,
    Proc_gueTime_const_of_step_zero h0 0]

private theorem Proc_gueDmax_const_of_step_zero (h0 : gridStep t1 t0 K n = 0)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (m k : ℕ) (ω : PathΩ sz) :
    gueDmax sz E t1 t0 K Kt n m k ω = gueDmax sz E t1 t0 K Kt n m 0 ω := by
  unfold gueDmax
  rw [Proc_gueH_const_of_step_zero sz h0 k ω, Proc_gueTime_const_of_step_zero h0 k,
    Proc_gueTime_const_of_step_zero h0 0]

end GueConstZero

/-! ### Pointwise triangle-inequality helpers -/

section GueTriangle

private theorem Proc_norm_le_norm_sub_add_norm {α : Type*} [SeminormedAddGroup α] (a b : α) :
    ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
  calc ‖a‖ = ‖a - b + b‖ := by rw [sub_add_cancel]
    _ ≤ ‖a - b‖ + ‖b‖ := norm_add_le _ _

private theorem Proc_le_ciSup_finite {ι : Type*} [Finite ι] (f : ι → ℝ) (i : ι) :
    f i ≤ ⨆ j, f j :=
  le_ciSup (Set.Finite.bddAbove (Set.finite_range f)) i

variable {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {E : ℕ → ℝ}

private theorem Proc_gueLmax_le_gueDmax_add_gueKbar (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ)
    (n m k' k : ℕ) (hk' : k' ≤ k) (ω : PathΩ sz) :
    gueLmax sz E t1 t0 K n m k' ω ≤ gueDmax sz E t1 t0 K Kt n m k' ω + gueKbar sz t1 t0 K Kt n m k := by
  unfold gueLmax gueDmax gueKbar RBM.Ind.loopMax
  apply ciSup_le
  intro x
  have h1 := Proc_norm_le_norm_sub_add_norm
    (loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k' ω)) (zt (E n) (gridTime t1 t0 K n k'))
      (⟨List.ofFn x.1, List.ofFn x.2⟩ : RBM.Loop.LoopIdx (Zd d (sz.L n))))
    (Kt n (gridTime t1 t0 K n k') (⟨List.ofFn x.1, List.ofFn x.2⟩ : RBM.Loop.LoopIdx (Zd d (sz.L n))))
  have h2 : ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k' ω))
        (zt (E n) (gridTime t1 t0 K n k'))
        (⟨List.ofFn x.1, List.ofFn x.2⟩ : RBM.Loop.LoopIdx (Zd d (sz.L n)))
      - Kt n (gridTime t1 t0 K n k') (⟨List.ofFn x.1, List.ofFn x.2⟩ : RBM.Loop.LoopIdx (Zd d (sz.L n)))‖
      ≤ ⨆ y : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
          ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k' ω))
            (zt (E n) (gridTime t1 t0 K n k')) (loopOf y.1 y.2) -
            Kt n (gridTime t1 t0 K n k') (loopOf y.1 y.2)‖ :=
    Proc_le_ciSup_finite (fun y : (Fin m → Bool) × (Fin m → Zd d (sz.L n)) =>
        ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k' ω))
          (zt (E n) (gridTime t1 t0 K n k')) (loopOf y.1 y.2) -
          Kt n (gridTime t1 t0 K n k') (loopOf y.1 y.2)‖) x
  have h3 : ‖Kt n (gridTime t1 t0 K n k') (⟨List.ofFn x.1, List.ofFn x.2⟩ : RBM.Loop.LoopIdx (Zd d (sz.L n)))‖
      ≤ ⨆ j : Fin (k + 1), ⨆ y : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
          ‖Kt n (gridTime t1 t0 K n j) (loopOf y.1 y.2)‖ := by
    calc ‖Kt n (gridTime t1 t0 K n k') (⟨List.ofFn x.1, List.ofFn x.2⟩ : RBM.Loop.LoopIdx (Zd d (sz.L n)))‖
        ≤ ⨆ y : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
            ‖Kt n (gridTime t1 t0 K n k') (loopOf y.1 y.2)‖ :=
          Proc_le_ciSup_finite (fun y : (Fin m → Bool) × (Fin m → Zd d (sz.L n)) =>
            ‖Kt n (gridTime t1 t0 K n k') (loopOf y.1 y.2)‖) x
      _ ≤ ⨆ j : Fin (k + 1), ⨆ y : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
            ‖Kt n (gridTime t1 t0 K n j) (loopOf y.1 y.2)‖ :=
          Proc_le_ciSup_finite (fun j : Fin (k + 1) =>
            ⨆ y : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
              ‖Kt n (gridTime t1 t0 K n j) (loopOf y.1 y.2)‖) (⟨k', by omega⟩ : Fin (k + 1))
  linarith [h1, h2, h3]

private theorem Proc_gueDmax_le_gueLmax_add_gueKbar (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ)
    (n m k' k : ℕ) (hk' : k' ≤ k) (ω : PathΩ sz) :
    gueDmax sz E t1 t0 K Kt n m k' ω ≤ gueLmax sz E t1 t0 K n m k' ω + gueKbar sz t1 t0 K Kt n m k := by
  unfold gueDmax gueLmax RBM.Ind.loopMax gueKbar
  apply ciSup_le
  intro x
  have h1 := norm_sub_le
    (loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k' ω)) (zt (E n) (gridTime t1 t0 K n k'))
      (loopOf x.1 x.2))
    (Kt n (gridTime t1 t0 K n k') (loopOf x.1 x.2))
  have h2 : ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k' ω))
        (zt (E n) (gridTime t1 t0 K n k')) (loopOf x.1 x.2)‖
      ≤ ⨆ y : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
          ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k' ω))
            (zt (E n) (gridTime t1 t0 K n k'))
            ⟨List.ofFn y.1, List.ofFn y.2⟩‖ :=
    Proc_le_ciSup_finite (fun y : (Fin m → Bool) × (Fin m → Zd d (sz.L n)) =>
        ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k' ω))
          (zt (E n) (gridTime t1 t0 K n k')) ⟨List.ofFn y.1, List.ofFn y.2⟩‖) x
  have h3 : ‖Kt n (gridTime t1 t0 K n k') (loopOf x.1 x.2)‖
      ≤ ⨆ j : Fin (k + 1), ⨆ y : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
          ‖Kt n (gridTime t1 t0 K n j) (loopOf y.1 y.2)‖ := by
    calc ‖Kt n (gridTime t1 t0 K n k') (loopOf x.1 x.2)‖
        ≤ ⨆ y : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
            ‖Kt n (gridTime t1 t0 K n k') (loopOf y.1 y.2)‖ :=
          Proc_le_ciSup_finite (fun y : (Fin m → Bool) × (Fin m → Zd d (sz.L n)) =>
            ‖Kt n (gridTime t1 t0 K n k') (loopOf y.1 y.2)‖) x
      _ ≤ ⨆ j : Fin (k + 1), ⨆ y : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
            ‖Kt n (gridTime t1 t0 K n j) (loopOf y.1 y.2)‖ :=
          Proc_le_ciSup_finite (fun j : Fin (k + 1) =>
            ⨆ y : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
              ‖Kt n (gridTime t1 t0 K n j) (loopOf y.1 y.2)‖) (⟨k', by omega⟩ : Fin (k + 1))
  linarith [h1, h2, h3]

private theorem Proc_gueLmax_odd_sq_le (n l k : ℕ) (hl : 1 ≤ l) (ω : PathΩ sz) :
    gueLmax sz E t1 t0 K n (2 * l + 1) k ω ≤
      Real.sqrt (gueLmax sz E t1 t0 K n (2 * l) k ω * gueLmax sz E t1 t0 K n (2 * l + 2) k ω) := by
  unfold gueLmax
  exact Real.le_sqrt_of_sq_le
    (RBM.Ind.loopMax_odd_sq_le ((gueH_isHermitian sz t1 t0 K n k ω).submatrix _) hl)

end GueTriangle

private theorem Proc_le_ciSup_finite_aux {ι : Type*} [Finite ι] (f : ι → ℝ) (i : ι) :
    f i ≤ ⨆ j, f j :=
  le_ciSup (Set.Finite.bddAbove (Set.finite_range f)) i

/-! ### Structural facts of the stopped processes -/

theorem gueLproc_nonneg (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (n m : ℕ) (t : ℝ)
    (ω : PathΩ sz) : 0 ≤ gueLproc sz E t1 t0 K δ n m t ω := by
  unfold gueLproc
  exact Proc_gueInterp_nonneg (fun k => by unfold gueLmax; exact RBM.Ind.loopMax_nonneg m) t

theorem gueDproc_nonneg (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (n m : ℕ) (t : ℝ) (ω : PathΩ sz) :
    0 ≤ gueDproc sz E t1 t0 K δ Kt n m t ω := by
  unfold gueDproc
  exact Proc_gueInterp_nonneg
    (fun k => by unfold gueDmax; exact Real.iSup_nonneg fun _ => norm_nonneg _) t

theorem gueLproc_continuousOn (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (n m : ℕ)
    (ω : PathΩ sz) :
    ContinuousOn (fun t => gueLproc sz E t1 t0 K δ n m t ω) (Set.Icc (t1 n) (t0 n)) := by
  unfold gueLproc
  exact Proc_gueInterp_continuousOn _

theorem gueDproc_continuousOn (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (n m : ℕ) (ω : PathΩ sz) :
    ContinuousOn (fun t => gueDproc sz E t1 t0 K δ Kt n m t ω) (Set.Icc (t1 n) (t0 n)) := by
  unfold gueDproc
  exact Proc_gueInterp_continuousOn _

/-- `hLDK` for the stopped processes (every `t`, every `ω`). -/
theorem gueLproc_le (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (n m : ℕ) (t : ℝ) (ω : PathΩ sz) :
    gueLproc sz E t1 t0 K δ n m t ω ≤
      gueDproc sz E t1 t0 K δ Kt n m t ω + gueKproc sz t1 t0 K Kt n m t := by
  unfold gueLproc gueDproc gueKproc
  rw [← Proc_gueInterp_add]
  exact Proc_gueInterp_mono
    (fun k => Proc_gueLmax_le_gueDmax_add_gueKbar sz Kt n m (min k (gueStop sz E t1 t0 K δ n ω)) k
      (min_le_left _ _) ω) t

/-- `hDLK` for the stopped processes (every `t`, every `ω`). -/
theorem gueDproc_le (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (n m : ℕ) (t : ℝ) (ω : PathΩ sz) :
    gueDproc sz E t1 t0 K δ Kt n m t ω ≤
      gueLproc sz E t1 t0 K δ n m t ω + gueKproc sz t1 t0 K Kt n m t := by
  unfold gueDproc gueLproc gueKproc
  rw [← Proc_gueInterp_add]
  exact Proc_gueInterp_mono
    (fun k => Proc_gueDmax_le_gueLmax_add_gueKbar sz Kt n m (min k (gueStop sz E t1 t0 K δ n ω)) k
      (min_le_left _ _) ω) t

/-- `hodd` for the stopped processes: (6.4) at the grid, Cauchy–Schwarz for the tent weights. -/
theorem gueLproc_odd (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (n l : ℕ) (hl : 1 ≤ l) (t : ℝ)
    (ω : PathΩ sz) :
    gueLproc sz E t1 t0 K δ n (2 * l + 1) t ω ≤
      Real.sqrt (gueLproc sz E t1 t0 K δ n (2 * l) t ω *
        gueLproc sz E t1 t0 K δ n (2 * l + 2) t ω) := by
  unfold gueLproc
  set σ := gueStop sz E t1 t0 K δ n ω with hσ
  calc gueInterp t1 t0 K n (fun k => gueLmax sz E t1 t0 K n (2 * l + 1) (min k σ) ω) t
      ≤ gueInterp t1 t0 K n (fun k => Real.sqrt (gueLmax sz E t1 t0 K n (2 * l) (min k σ) ω *
          gueLmax sz E t1 t0 K n (2 * l + 2) (min k σ) ω)) t :=
        Proc_gueInterp_mono (fun k => Proc_gueLmax_odd_sq_le sz n l (min k σ) hl ω) t
    _ ≤ Real.sqrt (gueInterp t1 t0 K n (fun k => gueLmax sz E t1 t0 K n (2 * l) (min k σ) ω) t *
          gueInterp t1 t0 K n (fun k => gueLmax sz E t1 t0 K n (2 * l + 2) (min k σ) ω) t) :=
        Proc_gueInterp_sqrt_mul_le (fun k => by unfold gueLmax; exact RBM.Ind.loopMax_nonneg _)
          (fun k => by unfold gueLmax; exact RBM.Ind.loopMax_nonneg _) t

/-- Grid values of `gueLproc`. -/
theorem gueLproc_time (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (n m k : ℕ)
    (ht10 : t1 n ≤ t0 n) (hk : k ≤ K n) (ω : PathΩ sz) :
    gueLproc sz E t1 t0 K δ n m (gridTime t1 t0 K n k) ω =
      gueLmax sz E t1 t0 K n m (min k (gueStop sz E t1 t0 K δ n ω)) ω := by
  unfold gueLproc
  refine Proc_gueInterp_time (fun h0 k' => ?_) ht10 hk
  rw [Proc_gueLmax_const_of_step_zero sz h0 m (min k' (gueStop sz E t1 t0 K δ n ω)) ω, Nat.zero_min]

/-- Grid values of `gueDproc`. -/
theorem gueDproc_time (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (n m k : ℕ) (ht10 : t1 n ≤ t0 n) (hk : k ≤ K n)
    (ω : PathΩ sz) :
    gueDproc sz E t1 t0 K δ Kt n m (gridTime t1 t0 K n k) ω =
      gueDmax sz E t1 t0 K Kt n m (min k (gueStop sz E t1 t0 K δ n ω)) ω := by
  unfold gueDproc
  refine Proc_gueInterp_time (fun h0 k' => ?_) ht10 hk
  rw [Proc_gueDmax_const_of_step_zero sz h0 Kt m (min k' (gueStop sz E t1 t0 K δ n ω)) ω,
    Nat.zero_min]
/-! ### Structural facts on the loop maxima (R6a, R6b), the Ward lower bound (A3) -/

section LoopMaxFacts

/-- **(R6a)**: for even length `2l`, `L_{2l+1} ≤ √L₂ · L_{2l}` ((6.4) + (5.117)); dimension-free. -/
theorem gueLoopMax_odd_succ_le {L W : ℕ} [NeZero L]
    {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian) (z : ℂ) {l : ℕ}
    (hl : 1 ≤ l) :
    RBM.Ind.loopMax d L W H z (2 * l + 1) ≤
      Real.sqrt (RBM.Ind.loopMax d L W H z 2) * RBM.Ind.loopMax d L W H z (2 * l) := by
  have h0 := RBM.Ind.loopMax_two_mul_add_le (z := z) hH hl (le_refl 1)
  have h1 : RBM.Ind.loopMax d L W H z (2 * l + 2) ≤
      RBM.Ind.loopMax d L W H z (2 * l) * RBM.Ind.loopMax d L W H z 2 := by
    have e1 : 2 * (l + 1) = 2 * l + 2 := by ring
    have e2 : 2 * 1 = 2 := by norm_num
    rwa [e1, e2] at h0
  have h2 := RBM.Ind.loopMax_odd_sq_le (z := z) hH hl
  have h3 : RBM.Ind.loopMax d L W H z (2 * l + 1) ^ 2
      ≤ RBM.Ind.loopMax d L W H z (2 * l) *
        (RBM.Ind.loopMax d L W H z (2 * l) * RBM.Ind.loopMax d L W H z 2) :=
    h2.trans (mul_le_mul_of_nonneg_left h1 (RBM.Ind.loopMax_nonneg _))
  have h4 : RBM.Ind.loopMax d L W H z (2 * l + 1) ^ 2
      ≤ (RBM.Ind.loopMax d L W H z (2 * l)) ^ 2 * RBM.Ind.loopMax d L W H z 2 := by nlinarith [h3]
  calc RBM.Ind.loopMax d L W H z (2 * l + 1)
      ≤ Real.sqrt ((RBM.Ind.loopMax d L W H z (2 * l)) ^ 2 * RBM.Ind.loopMax d L W H z 2) :=
        Real.le_sqrt_of_sq_le h4
    _ = Real.sqrt (RBM.Ind.loopMax d L W H z 2 * (RBM.Ind.loopMax d L W H z (2 * l)) ^ 2) := by
        rw [mul_comm]
    _ = Real.sqrt (RBM.Ind.loopMax d L W H z 2) *
          Real.sqrt ((RBM.Ind.loopMax d L W H z (2 * l)) ^ 2) :=
        Real.sqrt_mul (RBM.Ind.loopMax_nonneg _) _
    _ = Real.sqrt (RBM.Ind.loopMax d L W H z 2) * RBM.Ind.loopMax d L W H z (2 * l) := by
        rw [Real.sqrt_sq (RBM.Ind.loopMax_nonneg _)]

/-- **(R6b)**: for even length `2l`, `L_{4l} ≤ L_{2l}²` ((5.117)); dimension-free. -/
theorem gueLoopMax_four_mul_le {L W : ℕ} [NeZero L]
    {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian) (z : ℂ) {l : ℕ}
    (hl : 1 ≤ l) :
    RBM.Ind.loopMax d L W H z (4 * l) ≤ RBM.Ind.loopMax d L W H z (2 * l) ^ 2 := by
  have h := RBM.Ind.loopMax_two_mul_add_le (z := z) hH hl hl
  have e : 4 * l = 2 * (l + l) := by ring
  rw [e, sq]
  exact h

/-- `max_{a,b} |𝓛_{u,(+,-),(a,b)}| ≤ L₂` (the two-loops `(+,-)` are loops of length `2`). -/
private theorem Proc_maxLoopPM_le_loopMax {L W : ℕ} [NeZero L] [NeZero W] (E u : ℝ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) :
    RBM.Green.maxLoopPM d L W E u M ≤ RBM.Ind.loopMax d L W (blockMat d L W M) (zt E u) 2 := by
  unfold RBM.Green.maxLoopPM
  refine Finset.sup'_le _ _ fun p _ => ?_
  have h : RBM.Green.loopPM d L W E u M p.1 p.2
      = loopL d L W (blockMat d L W M) (zt E u) (loopOf ![true, false] ![p.1, p.2]) := by
    simp only [RBM.Green.loopPM, loopFine, loopM_eq_loopL]
  rw [h]
  exact RBM.Ind.norm_gloop_le_loopMax (loopOf ![true, false] ![p.1, p.2])
    (by simp [loopOf]) (by simp [loopOf])

/-- **A3**: the Ward lower bound on the a-priori event, with `hell` the `ellT_eq_L` condition
`L² (1-u) ≤ g²` (`Bootstrap.lean:148`); it uses `inv_N_le_maxLoopPM` (`N = (W L)^d`), which gives
`W^{-d} = 2 L^d (1-u) · Im m / (2 N η)` (`η = (1-u) Im m`), and `L^d ≤ L^{d-2} L²` (`L ≥ 1`), so
`W^{-d} ≤ 2 L^{d-2} g² L₂` (RBM2D: `W^{-2} ≤ 2 L₂` under `L² (1-u) ≤ 1`). -/
theorem gue_inv_W_le_loopMax {L W : ℕ} [NeZero L] [NeZero W]
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) {E u : ℝ}
    (hE : |E| < 2) (hu : u < 1) {g : ℝ} (hell : (L : ℝ) ^ 2 * (1 - u) ≤ g ^ 2) {δ : ℝ}
    (hΩ : RBM.Green.GoodEvent (RBM.Green.greenBlk d L W E u M true) (mE E) δ)
    (hδ : δ ≤ (mE E).im / 2) :
    ((W : ℝ)⁻¹) ^ d ≤
      2 * (L : ℝ) ^ (d - 2) * g ^ 2 * RBM.Ind.loopMax d L W (blockMat d L W M) (zt E u) 2 := by
  have him : 0 < (mE E).im := spectralM_im_pos hE
  have hzeq : (zt E u).im = (1 - u) * (mE E).im := spectralZ_im E u
  have h1u : 0 < 1 - u := by linarith
  have hzim : 0 < (zt E u).im := by rw [hzeq]; exact mul_pos h1u him
  have hward := RBM.Univ.inv_N_le_maxLoopPM hM hzim hΩ hδ
  have hmax := Proc_maxLoopPM_le_loopMax (d := d) E u M
  have hmax0 : 0 ≤ RBM.Green.maxLoopPM d L W E u M := RBM.Green.maxLoopPM_nonneg E u M
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hWpos : (0 : ℝ) < (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hN : (((W * L) ^ d : ℕ) : ℝ) = (W : ℝ) ^ d * (L : ℝ) ^ d := by push_cast; ring
  rw [hN, hzeq] at hward
  have heq : ((W : ℝ)⁻¹) ^ d = (2 * ((L : ℝ) ^ d * (1 - u))) *
      ((mE E).im / (2 * ((W : ℝ) ^ d * (L : ℝ) ^ d * ((1 - u) * (mE E).im)))) := by
    have hWd : (W : ℝ) ^ d ≠ 0 := pow_ne_zero _ hWpos.ne'
    have hLd : (L : ℝ) ^ d ≠ 0 := pow_ne_zero _ hLpos.ne'
    rw [inv_pow]
    field_simp
  have hc0 : 0 ≤ 2 * ((L : ℝ) ^ d * (1 - u)) := by positivity
  calc ((W : ℝ)⁻¹) ^ d
      = (2 * ((L : ℝ) ^ d * (1 - u))) *
        ((mE E).im / (2 * ((W : ℝ) ^ d * (L : ℝ) ^ d * ((1 - u) * (mE E).im)))) :=
        heq
    _ ≤ (2 * ((L : ℝ) ^ d * (1 - u))) * RBM.Green.maxLoopPM d L W E u M :=
        mul_le_mul_of_nonneg_left hward hc0
    _ ≤ (2 * (L : ℝ) ^ (d - 2) * g ^ 2) * RBM.Green.maxLoopPM d L W E u M := by
        apply mul_le_mul_of_nonneg_right _ hmax0
        have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
        have hpow : (L : ℝ) ^ d ≤ (L : ℝ) ^ (d - 2) * (L : ℝ) ^ 2 := by
          rw [← pow_add]; exact pow_le_pow_right₀ hL1 (by omega)
        have hLd2 : (0 : ℝ) ≤ (L : ℝ) ^ (d - 2) := by positivity
        calc 2 * ((L : ℝ) ^ d * (1 - u))
            ≤ 2 * ((L : ℝ) ^ (d - 2) * (L : ℝ) ^ 2 * (1 - u)) := by
              have := mul_le_mul_of_nonneg_right hpow h1u.le
              linarith
          _ = 2 * (L : ℝ) ^ (d - 2) * ((L : ℝ) ^ 2 * (1 - u)) := by ring
          _ ≤ 2 * (L : ℝ) ^ (d - 2) * g ^ 2 :=
              mul_le_mul_of_nonneg_left hell (by positivity)
    _ ≤ (2 * (L : ℝ) ^ (d - 2) * g ^ 2) *
          RBM.Ind.loopMax d L W (blockMat d L W M) (zt E u) 2 :=
        mul_le_mul_of_nonneg_left hmax (by positivity)

end LoopMaxFacts

/-! ### The bound on `𝓔^{(G̃)}` for `SBgue` -/

section EgtBound

/-- **`𝓔^{(G̃)}` of the GUE profile** (`SBgue = L^{-d}`): `|𝓔̃_GUE(I)| ≤ n · (W L)^d · ε · B`
(hypothesis in the `avgErr`/`loopL` form).  The prefactor is `W^d`, `SBgue = L^{-d}` and the label
sums over `Zd d L` have `L^d` terms each, so that `W^d · (L^d · L^d) · L^{-d} = (W L)^d`. -/
theorem norm_egtNGUE_le (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (I : RBM.Loop.LoopIdx (Zd d L)) {ε B : ℝ}
    (hε : ∀ (σ : Bool) (a : Zd d L), ‖RBM.Green.avgErr d L W E u M σ a‖ ≤ ε)
    (hB : ∀ k ∈ Finset.Icc 1 I.length, ∀ b : Zd d L,
      ‖loopL d L W (blockMat d L W M) (zt E u) (I.cutGlue k b)‖ ≤ B) :
    ‖egtNGUE d L W E u M I‖ ≤ (I.length : ℝ) * (((W * L) ^ d : ℕ) : ℝ) * ε * B := by
  rcases Nat.eq_zero_or_pos I.length with hn0 | hn1
  · have hSempty : Finset.Icc 1 I.length = (∅ : Finset ℕ) := by
      rw [hn0]; exact Finset.Icc_eq_empty (by omega)
    unfold egtNGUE
    rw [hSempty]
    simp [hn0]
  · have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε true 0)
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1 (Finset.mem_Icc.2 ⟨le_refl 1, hn1⟩) 0)
    have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have hcard : Fintype.card (Zd d L) = L ^ d := card_Zd d L
    have hterm : ∀ k ∈ Finset.Icc 1 I.length, ∀ a b : Zd d L,
        ‖RBM.Green.avgErr d L W E u M (I.σ.getD (k - 1) false) a * SBgue d L a b *
            loopL d L W (blockMat d L W M) (zt E u) (I.cutGlue k b)‖
        ≤ ε * ((L : ℝ) ^ d)⁻¹ * B := by
      intro k hk a b
      rw [norm_mul, norm_mul]
      have h1 := hε (I.σ.getD (k - 1) false) a
      have h2 : ‖SBgue d L a b‖ = ((L : ℝ) ^ d)⁻¹ := by
        rw [SBgue_apply, norm_inv, norm_pow, Complex.norm_natCast]
      have h3 := hB k hk b
      rw [h2]
      have e1 : (0 : ℝ) ≤ ((L : ℝ) ^ d)⁻¹ := by positivity
      calc ‖RBM.Green.avgErr d L W E u M (I.σ.getD (k - 1) false) a‖ * ((L : ℝ) ^ d)⁻¹ *
            ‖loopL d L W (blockMat d L W M) (zt E u) (I.cutGlue k b)‖
          ≤ ε * ((L : ℝ) ^ d)⁻¹ * ‖loopL d L W (blockMat d L W M) (zt E u) (I.cutGlue k b)‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 e1) (norm_nonneg _)
        _ ≤ ε * ((L : ℝ) ^ d)⁻¹ * B := mul_le_mul_of_nonneg_left h3 (by positivity)
    have hTk : ∀ k ∈ Finset.Icc 1 I.length,
        ‖∑ a : Zd d L, ∑ b : Zd d L, RBM.Green.avgErr d L W E u M (I.σ.getD (k - 1) false) a *
            SBgue d L a b * loopL d L W (blockMat d L W M) (zt E u) (I.cutGlue k b)‖
        ≤ (L : ℝ) ^ d * ((L : ℝ) ^ d * (ε * ((L : ℝ) ^ d)⁻¹ * B)) := by
      intro k hk
      calc ‖∑ a : Zd d L, ∑ b : Zd d L, RBM.Green.avgErr d L W E u M (I.σ.getD (k - 1) false) a *
              SBgue d L a b * loopL d L W (blockMat d L W M) (zt E u) (I.cutGlue k b)‖
          ≤ ∑ a : Zd d L, ‖∑ b : Zd d L, RBM.Green.avgErr d L W E u M
              (I.σ.getD (k - 1) false) a * SBgue d L a b *
              loopL d L W (blockMat d L W M) (zt E u) (I.cutGlue k b)‖ := norm_sum_le _ _
        _ ≤ ∑ _a : Zd d L, (L : ℝ) ^ d * (ε * ((L : ℝ) ^ d)⁻¹ * B) := by
            apply Finset.sum_le_sum
            intro a _
            calc ‖∑ b : Zd d L, RBM.Green.avgErr d L W E u M (I.σ.getD (k - 1) false) a *
                    SBgue d L a b * loopL d L W (blockMat d L W M) (zt E u) (I.cutGlue k b)‖
                ≤ ∑ b : Zd d L, ‖RBM.Green.avgErr d L W E u M (I.σ.getD (k - 1) false) a *
                    SBgue d L a b * loopL d L W (blockMat d L W M) (zt E u)
                      (I.cutGlue k b)‖ := norm_sum_le _ _
              _ ≤ ∑ _b : Zd d L, ε * ((L : ℝ) ^ d)⁻¹ * B :=
                  Finset.sum_le_sum fun b _ => hterm k hk a b
              _ = (L : ℝ) ^ d * (ε * ((L : ℝ) ^ d)⁻¹ * B) := by
                  rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
                  push_cast; ring
        _ = (L : ℝ) ^ d * ((L : ℝ) ^ d * (ε * ((L : ℝ) ^ d)⁻¹ * B)) := by
            rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
            push_cast; ring
    unfold egtNGUE
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    calc (W : ℝ) ^ d * ‖∑ k ∈ Finset.Icc 1 I.length, ∑ a : Zd d L, ∑ b : Zd d L,
            RBM.Green.avgErr d L W E u M (I.σ.getD (k - 1) false) a * SBgue d L a b *
              loopL d L W (blockMat d L W M) (zt E u) (I.cutGlue k b)‖
        ≤ (W : ℝ) ^ d * ∑ k ∈ Finset.Icc 1 I.length, ‖∑ a : Zd d L, ∑ b : Zd d L,
            RBM.Green.avgErr d L W E u M (I.σ.getD (k - 1) false) a * SBgue d L a b *
              loopL d L W (blockMat d L W M) (zt E u) (I.cutGlue k b)‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ (W : ℝ) ^ d * ∑ _k ∈ Finset.Icc 1 I.length,
            (L : ℝ) ^ d * ((L : ℝ) ^ d * (ε * ((L : ℝ) ^ d)⁻¹ * B)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hTk) (by positivity)
      _ = (W : ℝ) ^ d * ((I.length : ℝ) * ((L : ℝ) ^ d * ((L : ℝ) ^ d *
            (ε * ((L : ℝ) ^ d)⁻¹ * B)))) := by
          have hc : (Finset.Icc 1 I.length).card = I.length := by
            rw [Nat.card_Icc]; omega
          rw [Finset.sum_const, hc, nsmul_eq_mul]
      _ = (I.length : ℝ) * (((W * L) ^ d : ℕ) : ℝ) * ε * B := by
          push_cast
          rw [mul_pow]
          field_simp

end EgtBound

/-! ### The one-step change of the entry deviation -/

section DevStep

open scoped Matrix.Norms.L2Operator

/-- `‖A‖ ≤ ∑_{ij} |A_{ij}|` for the `ℓ² → ℓ²` operator norm. -/
private theorem Proc_opNorm_le_sum_norm {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : ‖A‖ ≤ ∑ i : n, ∑ j : n, ‖A i j‖ := by
  set S : ℝ := ∑ i : n, ∑ j : n, ‖A i j‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  set T := toEuclideanCLM (n := n) (𝕜 := ℂ) A with hT
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine T.opNorm_le_bound hS0 fun x => ?_
  have hx : ∀ j, ‖x j‖ ≤ ‖x‖ := fun j => PiLp.norm_apply_le x j
  have hrow : ∀ i, ‖(T x) i‖ ≤ (∑ j, ‖A i j‖) * ‖x‖ := by
    intro i
    have : (T x) i = ∑ j, A i j * x j := by
      simp [hT, Matrix.mulVec, dotProduct]
    rw [this]
    calc ‖∑ j, A i j * x j‖ ≤ ∑ j, ‖A i j * x j‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖A i j‖ * ‖x‖ := Finset.sum_le_sum fun j _ => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hx j) (norm_nonneg _)
      _ = (∑ j, ‖A i j‖) * ‖x‖ := by rw [Finset.sum_mul]
  have hl2 : ‖T x‖ ≤ ∑ i, ‖(T x) i‖ := by
    rw [EuclideanSpace.norm_eq]
    calc Real.sqrt (∑ i, ‖(T x) i‖ ^ 2) ≤ Real.sqrt ((∑ i, ‖(T x) i‖) ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => norm_nonneg _)
      _ = ∑ i, ‖(T x) i‖ := Real.sqrt_sq (Finset.sum_nonneg fun i _ => norm_nonneg _)
  calc ‖T x‖ ≤ ∑ i, ‖(T x) i‖ := hl2
    _ ≤ ∑ i, (∑ j, ‖A i j‖) * ‖x‖ := Finset.sum_le_sum fun i _ => hrow i
    _ = S * ‖x‖ := by rw [hS, Finset.sum_mul]

/-- `‖G(H, z)‖ ≤ η⁻¹` for Hermitian `H` and `η ≤ |Im z|` (RBM2D `RBM.Gauss.norm_green_le`; the
merged route of `Green/IBPPoly.lean:411`: `norm_Gsig_le_inv_eta` at `s = true`, `Gres H z true =
green H z`). -/
private theorem Proc_norm_green_le {ν : Type*} [Fintype ν] [DecidableEq ν] {H : Matrix ν ν ℂ}
    (hH : H.IsHermitian) {η : ℝ} {z : ℂ} (hη : 0 < η) (hz : η ≤ |z.im|) :
    ‖green H z‖ ≤ η⁻¹ := by
  have h := norm_Gsig_le_inv_eta hH hη hz true
  have e : Gres H z true = green H z := by
    simp only [green, Gres, ↓reduceIte, Matrix.nonsing_inv_eq_ringInverse]
  rwa [e] at h

/-- The two-parameter resolvent bound
`‖G(H', z') - G(H, z)‖ ≤ ‖G(H', z')‖ (‖H' - H‖ + |z' - z|) ‖G(H, z)‖`
(`norm_green_sub_le_of_herm` is for equal `z`). -/
private theorem Proc_norm_green_sub_le {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
    {H H' : Matrix ν ν ℂ} (hH : H.IsHermitian) (hH' : H'.IsHermitian) {z z' : ℂ}
    (hz : z.im ≠ 0) (hz' : z'.im ≠ 0) :
    ‖green H' z' - green H z‖ ≤ ‖green H' z'‖ * (‖H' - H‖ + ‖z' - z‖) * ‖green H z‖ := by
  have hu := RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero hH hz
  have hu' := RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero hH' hz'
  have hd : IsUnit (H - z • (1 : Matrix ν ν ℂ)).det := (Matrix.isUnit_iff_isUnit_det _).mp hu
  have hd' : IsUnit (H' - z' • (1 : Matrix ν ν ℂ)).det := (Matrix.isUnit_iff_isUnit_det _).mp hu'
  have h1 : green H' z' * (H' - z' • (1 : Matrix ν ν ℂ)) = 1 := by
    rw [green]; exact Matrix.nonsing_inv_mul _ hd'
  have h2 : (H - z • (1 : Matrix ν ν ℂ)) * green H z = 1 := by
    rw [green]; exact Matrix.mul_nonsing_inv _ hd
  have hid : green H' z' - green H z
      = green H' z' * ((H - H') + (z' - z) • (1 : Matrix ν ν ℂ)) * green H z := by
    have hmid : (H - H') + (z' - z) • (1 : Matrix ν ν ℂ)
        = (H - z • (1 : Matrix ν ν ℂ)) - (H' - z' • (1 : Matrix ν ν ℂ)) := by
      module
    have e1 : green H' z' * (H - z • (1 : Matrix ν ν ℂ)) * green H z = green H' z' := by
      rw [Matrix.mul_assoc, h2, Matrix.mul_one]
    have e2 : green H' z' * (H' - z' • (1 : Matrix ν ν ℂ)) * green H z = green H z := by
      rw [h1, Matrix.one_mul]
    rw [hmid, Matrix.mul_sub, Matrix.sub_mul, e1, e2]
  rw [hid]
  have hnorm : ‖(H - H') + (z' - z) • (1 : Matrix ν ν ℂ)‖ ≤ ‖H' - H‖ + ‖z' - z‖ := by
    calc ‖(H - H') + (z' - z) • (1 : Matrix ν ν ℂ)‖
        ≤ ‖H - H'‖ + ‖(z' - z) • (1 : Matrix ν ν ℂ)‖ := norm_add_le _ _
      _ = ‖H' - H‖ + ‖z' - z‖ := by rw [norm_sub_rev H H', norm_smul, norm_one, mul_one]
  calc ‖green H' z' * ((H - H') + (z' - z) • (1 : Matrix ν ν ℂ)) * green H z‖
      ≤ ‖green H' z' * ((H - H') + (z' - z) • (1 : Matrix ν ν ℂ))‖ * ‖green H z‖ :=
        norm_mul_le _ _
    _ ≤ ‖green H' z'‖ * ‖(H - H') + (z' - z) • (1 : Matrix ν ν ℂ)‖ * ‖green H z‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ ‖green H' z'‖ * (‖H' - H‖ + ‖z' - z‖) * ‖green H z‖ := by
        gcongr

private theorem Proc_gridTime_mono {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (ht10 : t1 n ≤ t0 n)
    {i j : ℕ} (hij : i ≤ j) : gridTime t1 t0 K n i ≤ gridTime t1 t0 K n j := by
  have hstep0 : 0 ≤ gridStep t1 t0 K n := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  unfold gridTime
  nlinarith [hstep0]

/-- **One-step change of the entry deviation**: the
resolvent identity `G' - G = G' ((H - H') + (z' - z)) G`, `H' - H = √(Δ/N) X_{k+1}`,
`|z' - z| = Δ |m| = Δ`, and `η_u ≥ η_{t₀}` at the grid times. -/
theorem gueDev_succ_le (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (hE : |E n| < 2)
    (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1) (hk : k < K n) (ω : PathΩ sz) :
    gueDev sz E t1 t0 K n (k + 1) ω ≤ gueDev sz E t1 t0 K n k ω +
      (etaT (E n) (t0 n))⁻¹ ^ 2 * (Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) *
        ∑ i : Idx d (sz.L n) (sz.W n), ∑ j : Idx d (sz.L n) (sz.W n),
          ‖Sizes.seqXmat sz n (ω (k + 1)) i j‖ + gridStep t1 t0 K n) := by
  have : Nonempty (Idx d (sz.L n) (sz.W n)) := ⟨(0 : Zd d (sz.W n * sz.L n))⟩
  have hKne : K n ≠ 0 := by omega
  have hstep0 : 0 ≤ gridStep t1 t0 K n := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have htimeK : gridTime t1 t0 K n (K n) = t0 n := gridTime_last t1 t0 K n hKne
  have htk : gridTime t1 t0 K n k ≤ t0 n :=
    htimeK ▸ Proc_gridTime_mono ht10 (by omega : k ≤ K n)
  have htk1 : gridTime t1 t0 K n (k + 1) ≤ t0 n :=
    htimeK ▸ Proc_gridTime_mono ht10 (by omega : k + 1 ≤ K n)
  have him : 0 < (mE (E n)).im := mE_im_pos hE
  have hetak : etaT (E n) (t0 n) ≤ etaT (E n) (gridTime t1 t0 K n k) := by
    unfold etaT; nlinarith [htk]
  have hetak1 : etaT (E n) (t0 n) ≤ etaT (E n) (gridTime t1 t0 K n (k + 1)) := by
    unfold etaT; nlinarith [htk1]
  have het0pos : 0 < etaT (E n) (t0 n) := by unfold etaT; nlinarith [ht0]
  have hzkim : (zt (E n) (gridTime t1 t0 K n k)).im = etaT (E n) (gridTime t1 t0 K n k) :=
    zt_im (E n) (gridTime t1 t0 K n k)
  have hzk1im : (zt (E n) (gridTime t1 t0 K n (k + 1))).im
      = etaT (E n) (gridTime t1 t0 K n (k + 1)) := zt_im (E n) (gridTime t1 t0 K n (k + 1))
  have hetakpos : 0 < etaT (E n) (gridTime t1 t0 K n k) := lt_of_lt_of_le het0pos hetak
  have hetak1pos : 0 < etaT (E n) (gridTime t1 t0 K n (k + 1)) := lt_of_lt_of_le het0pos hetak1
  have hzkim0 : (zt (E n) (gridTime t1 t0 K n k)).im ≠ 0 := by rw [hzkim]; linarith
  have hzk1im0 : (zt (E n) (gridTime t1 t0 K n (k + 1))).im ≠ 0 := by
    rw [hzk1im]; linarith
  have hHk := gueH_isHermitian sz t1 t0 K n k ω
  have hHk1 := gueH_isHermitian sz t1 t0 K n (k + 1) ω
  have hGk_le : ‖green (gueH sz t1 t0 K n k ω) (zt (E n) (gridTime t1 t0 K n k))‖
      ≤ (etaT (E n) (t0 n))⁻¹ :=
    Proc_norm_green_le hHk het0pos (by rw [hzkim, abs_of_pos hetakpos]; exact hetak)
  have hGk1_le :
      ‖green (gueH sz t1 t0 K n (k + 1) ω) (zt (E n) (gridTime t1 t0 K n (k + 1)))‖
      ≤ (etaT (E n) (t0 n))⁻¹ :=
    Proc_norm_green_le hHk1 het0pos (by rw [hzk1im, abs_of_pos hetak1pos]; exact hetak1)
  have hHdiff : gueH sz t1 t0 K n (k + 1) ω - gueH sz t1 t0 K n k ω
      = (Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) : ℂ) •
          Sizes.seqXmat sz n (ω (k + 1)) := by
    unfold gueH
    have hins : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hins, Finset.sum_insert (by simp), smul_add]
    abel
  have hHnorm : ‖gueH sz t1 t0 K n (k + 1) ω - gueH sz t1 t0 K n k ω‖
      ≤ Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ))
        * ∑ i : Idx d (sz.L n) (sz.W n), ∑ j : Idx d (sz.L n) (sz.W n),
            ‖Sizes.seqXmat sz n (ω (k + 1)) i j‖ := by
    rw [hHdiff, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (Proc_opNorm_le_sum_norm _) (Real.sqrt_nonneg _)
  have hzdiff : zt (E n) (gridTime t1 t0 K n (k + 1)) -
      zt (E n) (gridTime t1 t0 K n k) = (-(gridStep t1 t0 K n : ℂ)) * mE (E n) := by
    unfold zt gridTime
    push_cast
    ring
  have hznorm : ‖zt (E n) (gridTime t1 t0 K n (k + 1)) -
      zt (E n) (gridTime t1 t0 K n k)‖ = gridStep t1 t0 K n := by
    rw [hzdiff, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hstep0,
      norm_mE (by linarith [abs_lt.mp hE]), mul_one]
  have hAZ : ‖gueH sz t1 t0 K n (k + 1) ω - gueH sz t1 t0 K n k ω‖
        + ‖zt (E n) (gridTime t1 t0 K n (k + 1)) - zt (E n) (gridTime t1 t0 K n k)‖
      ≤ Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) *
          ∑ i : Idx d (sz.L n) (sz.W n), ∑ j : Idx d (sz.L n) (sz.W n),
            ‖Sizes.seqXmat sz n (ω (k + 1)) i j‖ + gridStep t1 t0 K n := by
    rw [hznorm]; exact add_le_add hHnorm (le_refl _)
  have hAZ0 : 0 ≤ ‖gueH sz t1 t0 K n (k + 1) ω - gueH sz t1 t0 K n k ω‖
        + ‖zt (E n) (gridTime t1 t0 K n (k + 1)) - zt (E n) (gridTime t1 t0 K n k)‖ := by
    positivity
  have hGdiff := Proc_norm_green_sub_le hHk hHk1 hzkim0 hzk1im0
  have hop : ‖green (gueH sz t1 t0 K n (k + 1) ω) (zt (E n) (gridTime t1 t0 K n (k + 1)))
        - green (gueH sz t1 t0 K n k ω) (zt (E n) (gridTime t1 t0 K n k))‖
      ≤ (etaT (E n) (t0 n))⁻¹ ^ 2 *
        (Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) *
          ∑ i : Idx d (sz.L n) (sz.W n), ∑ j : Idx d (sz.L n) (sz.W n),
            ‖Sizes.seqXmat sz n (ω (k + 1)) i j‖ + gridStep t1 t0 K n) := by
    have hη0 : 0 ≤ (etaT (E n) (t0 n))⁻¹ := by positivity
    calc ‖green (gueH sz t1 t0 K n (k + 1) ω) (zt (E n) (gridTime t1 t0 K n (k + 1)))
            - green (gueH sz t1 t0 K n k ω) (zt (E n) (gridTime t1 t0 K n k))‖
        ≤ ‖green (gueH sz t1 t0 K n (k + 1) ω) (zt (E n) (gridTime t1 t0 K n (k + 1)))‖
            * (‖gueH sz t1 t0 K n (k + 1) ω - gueH sz t1 t0 K n k ω‖
              + ‖zt (E n) (gridTime t1 t0 K n (k + 1)) -
                  zt (E n) (gridTime t1 t0 K n k)‖)
            * ‖green (gueH sz t1 t0 K n k ω) (zt (E n) (gridTime t1 t0 K n k))‖ := hGdiff
      _ ≤ (etaT (E n) (t0 n))⁻¹
            * (Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) *
                ∑ i : Idx d (sz.L n) (sz.W n), ∑ j : Idx d (sz.L n) (sz.W n),
                  ‖Sizes.seqXmat sz n (ω (k + 1)) i j‖ + gridStep t1 t0 K n)
            * (etaT (E n) (t0 n))⁻¹ := by
          apply mul_le_mul (mul_le_mul hGk1_le hAZ hAZ0 hη0) hGk_le (norm_nonneg _)
          positivity
      _ = (etaT (E n) (t0 n))⁻¹ ^ 2 *
            (Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) *
              ∑ i : Idx d (sz.L n) (sz.W n), ∑ j : Idx d (sz.L n) (sz.W n),
                ‖Sizes.seqXmat sz n (ω (k + 1)) i j‖ + gridStep t1 t0 K n) := by
          ring
  unfold gueDev
  apply ciSup_le
  intro ij
  have heq : (green (gueH sz t1 t0 K n (k + 1) ω) (zt (E n) (gridTime t1 t0 K n (k + 1)))
        - mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) ij.1 ij.2
      = (green (gueH sz t1 t0 K n (k + 1) ω) (zt (E n) (gridTime t1 t0 K n (k + 1)))
          - green (gueH sz t1 t0 K n k ω) (zt (E n) (gridTime t1 t0 K n k))) ij.1 ij.2
        + (green (gueH sz t1 t0 K n k ω) (zt (E n) (gridTime t1 t0 K n k))
            - mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))
            ij.1 ij.2 := by
    simp only [Matrix.sub_apply]
    ring
  have hE1 : ‖(green (gueH sz t1 t0 K n (k + 1) ω) (zt (E n) (gridTime t1 t0 K n (k + 1)))
        - mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))
          ij.1 ij.2‖
      ≤ ‖(green (gueH sz t1 t0 K n (k + 1) ω) (zt (E n) (gridTime t1 t0 K n (k + 1)))
          - green (gueH sz t1 t0 K n k ω) (zt (E n) (gridTime t1 t0 K n k))) ij.1 ij.2‖
        + ‖(green (gueH sz t1 t0 K n k ω) (zt (E n) (gridTime t1 t0 K n k))
            - mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))
              ij.1 ij.2‖ := by
    rw [heq]; exact norm_add_le _ _
  have hE2 : ‖(green (gueH sz t1 t0 K n (k + 1) ω) (zt (E n) (gridTime t1 t0 K n (k + 1)))
        - green (gueH sz t1 t0 K n k ω) (zt (E n) (gridTime t1 t0 K n k))) ij.1 ij.2‖
      ≤ ‖green (gueH sz t1 t0 K n (k + 1) ω) (zt (E n) (gridTime t1 t0 K n (k + 1)))
          - green (gueH sz t1 t0 K n k ω) (zt (E n) (gridTime t1 t0 K n k))‖ :=
    RBM.Ind.norm_apply_le_l2_opNorm _ ij.1 ij.2
  have hE3 : ‖(green (gueH sz t1 t0 K n k ω) (zt (E n) (gridTime t1 t0 K n k))
        - mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))
          ij.1 ij.2‖
      ≤ ⨆ ij' : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n),
          ‖(green (gueH sz t1 t0 K n k ω) (zt (E n) (gridTime t1 t0 K n k))
            - mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))
              ij'.1 ij'.2‖ :=
    Proc_le_ciSup_finite_aux (fun ij' : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) =>
        ‖(green (gueH sz t1 t0 K n k ω) (zt (E n) (gridTime t1 t0 K n k))
          - mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))
            ij'.1 ij'.2‖) ij
  linarith [hE1, hE2, hE3, hop]

end DevStep

end RBM.Univ.GUEPhase

/-! ## Compiled instances

The merged instance sizes `RBM.Gauss.SizesInst.sz0` (`d = 3`, `L 0 = 4`, `W 0 = 32`,
`N = 2097152`), `t₀ = 9/10`, `t₁ = (1 - ζ(1/20)) t₀ = e^{-1/20} · 9/10`, `K = fun _ => 4`, `E = 0`,
`δ = gueDelta sz0 (1/2)`: the processes and the one-step jump at `n = 0`; the tent and the
interpolation on the grid `t₁ = 4/5`, `t₀ = 9/10`, `K = 4`; the loop-maximum facts, the Ward lower
bound and the `𝓔^{(G̃)}` bound at `d = 3`. -/

namespace RBM.Univ.GUEPhase.ProcInst

open MeasureTheory ProbabilityTheory Matrix RBM RBM.Gauss RBM.Path RBM.Univ RBM.Univ.GUEPhase

/-! ### Data -/

private abbrev t1c : ℕ → ℝ := fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)
private abbrev t0c : ℕ → ℝ := fun _ => 9 / 10
private abbrev Kc : ℕ → ℕ := fun _ => 4
private abbrev Ec : ℕ → ℝ := fun _ => 0
private abbrev Ktc : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd 3 (SizesInst.sz0.L n)) → ℂ := fun _ _ _ => 0

private theorem t1c_le : t1c 0 ≤ t0c 0 := by
  simp only [t1c, t0c, ouZeta]
  have h1 : Real.exp (-(1 / 20 : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  nlinarith

private theorem mE_zero_im : (mE 0).im = 1 := by
  rw [mE_im]
  have : (4 : ℝ) - 0 ^ 2 = 2 ^ 2 := by norm_num
  rw [this, Real.sqrt_sq (by norm_num)]
  norm_num

example : 0 < gueDelta SizesInst.sz0 (1 / 2) 0 := by
  unfold gueDelta
  exact Real.rpow_pos_of_pos (by exact_mod_cast (by norm_num [Sizes.size, SizesInst.sz0] : 0 < (SizesInst.sz0.size 0))) _

/-! ### Process layer at `sz0`, `n = 0` -/

example (ω : PathΩ SizesInst.sz0) (t : ℝ) :
    0 ≤ gueLproc SizesInst.sz0 Ec t1c t0c Kc (gueDelta SizesInst.sz0 (1 / 2)) 0 2 t ω :=
  gueLproc_nonneg SizesInst.sz0 Ec t1c t0c Kc _ 0 2 t ω

example (ω : PathΩ SizesInst.sz0) (t : ℝ) :
    0 ≤ gueDproc SizesInst.sz0 Ec t1c t0c Kc (gueDelta SizesInst.sz0 (1 / 2)) Ktc 0 2 t ω :=
  gueDproc_nonneg SizesInst.sz0 Ec t1c t0c Kc _ Ktc 0 2 t ω

example (ω : PathΩ SizesInst.sz0) :
    ContinuousOn (fun t => gueLproc SizesInst.sz0 Ec t1c t0c Kc (gueDelta SizesInst.sz0 (1 / 2)) 0 2 t ω)
      (Set.Icc (t1c 0) (t0c 0)) :=
  gueLproc_continuousOn SizesInst.sz0 Ec t1c t0c Kc _ 0 2 ω

example (ω : PathΩ SizesInst.sz0) :
    ContinuousOn (fun t => gueDproc SizesInst.sz0 Ec t1c t0c Kc (gueDelta SizesInst.sz0 (1 / 2)) Ktc 0 2 t ω)
      (Set.Icc (t1c 0) (t0c 0)) :=
  gueDproc_continuousOn SizesInst.sz0 Ec t1c t0c Kc _ Ktc 0 2 ω

example (ω : PathΩ SizesInst.sz0) (t : ℝ) :
    gueLproc SizesInst.sz0 Ec t1c t0c Kc (gueDelta SizesInst.sz0 (1 / 2)) 0 2 t ω ≤
      gueDproc SizesInst.sz0 Ec t1c t0c Kc (gueDelta SizesInst.sz0 (1 / 2)) Ktc 0 2 t ω +
        gueKproc SizesInst.sz0 t1c t0c Kc Ktc 0 2 t :=
  gueLproc_le SizesInst.sz0 Ec t1c t0c Kc _ Ktc 0 2 t ω

example (ω : PathΩ SizesInst.sz0) (t : ℝ) :
    gueDproc SizesInst.sz0 Ec t1c t0c Kc (gueDelta SizesInst.sz0 (1 / 2)) Ktc 0 2 t ω ≤
      gueLproc SizesInst.sz0 Ec t1c t0c Kc (gueDelta SizesInst.sz0 (1 / 2)) 0 2 t ω +
        gueKproc SizesInst.sz0 t1c t0c Kc Ktc 0 2 t :=
  gueDproc_le SizesInst.sz0 Ec t1c t0c Kc _ Ktc 0 2 t ω

example (ω : PathΩ SizesInst.sz0) (t : ℝ) :
    gueLproc SizesInst.sz0 Ec t1c t0c Kc (gueDelta SizesInst.sz0 (1 / 2)) 0 (2 * 1 + 1) t ω ≤
      Real.sqrt (gueLproc SizesInst.sz0 Ec t1c t0c Kc (gueDelta SizesInst.sz0 (1 / 2)) 0 (2 * 1) t ω *
        gueLproc SizesInst.sz0 Ec t1c t0c Kc (gueDelta SizesInst.sz0 (1 / 2)) 0 (2 * 1 + 2) t ω) :=
  gueLproc_odd SizesInst.sz0 Ec t1c t0c Kc _ 0 1 le_rfl t ω

/-- `gueLproc_time` at the last grid step `k = 4 = K 0`. -/
example (ω : PathΩ SizesInst.sz0) :
    gueLproc SizesInst.sz0 Ec t1c t0c Kc (gueDelta SizesInst.sz0 (1 / 2)) 0 2
        (gridTime t1c t0c Kc 0 4) ω =
      gueLmax SizesInst.sz0 Ec t1c t0c Kc 0 2
        (min 4 (gueStop SizesInst.sz0 Ec t1c t0c Kc (gueDelta SizesInst.sz0 (1 / 2)) 0 ω)) ω :=
  gueLproc_time SizesInst.sz0 Ec t1c t0c Kc _ 0 2 4 t1c_le le_rfl ω

example (ω : PathΩ SizesInst.sz0) :
    gueDproc SizesInst.sz0 Ec t1c t0c Kc (gueDelta SizesInst.sz0 (1 / 2)) Ktc 0 2
        (gridTime t1c t0c Kc 0 1) ω =
      gueDmax SizesInst.sz0 Ec t1c t0c Kc Ktc 0 2
        (min 1 (gueStop SizesInst.sz0 Ec t1c t0c Kc (gueDelta SizesInst.sz0 (1 / 2)) 0 ω)) ω :=
  gueDproc_time SizesInst.sz0 Ec t1c t0c Kc _ Ktc 0 2 1 t1c_le (by norm_num [Kc]) ω

/-- `gueDev_succ_le` at `d = 3`, `sz0`, `n = 0`, `k = 0 < 4 = K 0`. -/
example (ω : PathΩ SizesInst.sz0) :=
  gueDev_succ_le SizesInst.sz0 Ec t1c t0c Kc 0 0 (by norm_num [Ec]) t1c_le (by norm_num [t0c])
    (by norm_num [Kc]) ω

example (ω : PathΩ SizesInst.sz0) :=
  gueDev_succ_le SizesInst.sz0 Ec t1c t0c Kc 0 3 (by norm_num [Ec]) t1c_le (by norm_num [t0c])
    (by norm_num [Kc]) ω

/-! ### Tent and interpolation on a concrete grid -/

example : gueTent (fun _ => (4 : ℝ) / 5) (fun _ => 9 / 10) (fun _ => 4) 0 1 (33 / 40) = 1 := by
  norm_num [gueTent, gridTime, gridStep]

example : gueTent (fun _ => (4 : ℝ) / 5) (fun _ => 9 / 10) (fun _ => 4) 0 1 (17 / 20) = 0 := by
  norm_num [gueTent, gridTime, gridStep]

example : gueTent (fun _ => (4 : ℝ) / 5) (fun _ => 9 / 10) (fun _ => 4) 0 1 (67 / 80) = 1 / 2 := by
  norm_num [gueTent, gridTime, gridStep]

example : gueInterp (fun _ => (4 : ℝ) / 5) (fun _ => 9 / 10) (fun _ => 4) 0
    (fun k => (k : ℝ) ^ 2) (67 / 80) = 5 / 2 := by
  norm_num [gueInterp, gueTent, gridTime, gridStep, Finset.sum_range_succ]

example : gueInterp (fun _ => (4 : ℝ) / 5) (fun _ => 9 / 10) (fun _ => 4) 0
    (fun k => (k : ℝ) ^ 2) (7 / 8) = 9 := by
  norm_num [gueInterp, gueTent, gridTime, gridStep, Finset.sum_range_succ]

/-! ### The loop-maximum facts at `d = 3`, `L = 3`, `W = 2` -/

example : RBM.Ind.loopMax 3 3 2 (1 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I (2 * 1 + 1) ≤
    Real.sqrt (RBM.Ind.loopMax 3 3 2 (1 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I 2) *
      RBM.Ind.loopMax 3 3 2 (1 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I (2 * 1) :=
  gueLoopMax_odd_succ_le (Matrix.isHermitian_one) Complex.I (l := 1) le_rfl

example : RBM.Ind.loopMax 3 3 2 (1 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I (4 * 1) ≤
    RBM.Ind.loopMax 3 3 2 (1 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I (2 * 1) ^ 2 :=
  gueLoopMax_four_mul_le (Matrix.isHermitian_one) Complex.I (l := 1) le_rfl

/-! ### The Ward lower bound `gue_inv_W_le_loopMax` -/

/-- At `d = 3`, `L = 3`, `W = 4`, `E = 0`, `u = 26/27`, `g = 1` (`L² (1 - u) = 1/3 ≤ g²`),
`δ = 1/2 = Im m / 2`: every deterministic hypothesis is discharged; the local-law event `hΩ` of the
Hermitian matrix `M` is the consumer's input (UN-48/49), kept as a hypothesis. -/
example {M : Matrix (Idx 3 3 4) (Idx 3 3 4) ℂ} (hM : M.IsHermitian)
    (hΩ : RBM.Green.GoodEvent (RBM.Green.greenBlk 3 3 4 0 (26 / 27) M true) (mE 0) (1 / 2)) :
    (((4 : ℕ) : ℝ)⁻¹) ^ 3 ≤
      2 * ((3 : ℕ) : ℝ) ^ (3 - 2) * (1 : ℝ) ^ 2 *
        RBM.Ind.loopMax 3 3 4 (blockMat 3 3 4 M) (zt 0 (26 / 27)) 2 :=
  gue_inv_W_le_loopMax hM (by norm_num) (by norm_num) (by norm_num) hΩ
    (by rw [mE_zero_im])

/-- Every hypothesis discharged at `d = 3`, `L = 3`, `W = 2`, `E = 0`, `u = 0`, `g = 3`
(`L² (1 - u) = 9 = g²`), `M = 0` (`G_0 = m I`, so the event holds with `δ = 0`). -/
example : (((2 : ℕ) : ℝ)⁻¹) ^ 3 ≤
    2 * ((3 : ℕ) : ℝ) ^ (3 - 2) * (3 : ℝ) ^ 2 *
      RBM.Ind.loopMax 3 3 2 (blockMat 3 3 2 (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)) (zt 0 0) 2 :=
  gue_inv_W_le_loopMax (L := 3) (W := 2) (E := 0) (u := 0) (g := 3) (δ := 0)
    Matrix.isHermitian_zero (by norm_num) (by norm_num) (by norm_num)
    (by
      rw [RBM.Green.greenBlk_time_zero (by norm_num)]
      intro x y
      by_cases h : x = y <;> simp [h])
    (by rw [mE_zero_im]; norm_num)

/-! ### The bound on `𝓔^{(G̃)}` at `d = 3`, `L = 3`, `W = 2`, `E = 0`, `u = 1/2`, every Hermitian `M` -/

section Egt

open scoped Matrix.Norms.L2Operator

private theorem zt_half_im : (zt 0 (1 / 2)).im = 1 / 2 := by
  rw [spectralZ_im, mE_zero_im]; norm_num

private theorem norm_mSigma_zero (σ : Bool) : ‖mSigma 0 σ‖ = 1 := norm_mSigma (by norm_num) σ

/-- `‖𝓛_{(σ),(a)}‖`-type bound: `‖G_σ‖ ≤ 2` at `η = Im z = 1/2`. -/
private theorem egt_norm_G {M : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ} (hM : M.IsHermitian) (σ : Bool) :
    ‖Gres (blockMat 3 3 2 M) (zt 0 (1 / 2)) σ‖ ≤ 2 := by
  have hH : (blockMat 3 3 2 M).IsHermitian := hM.submatrix _
  have h := norm_Gsig_le_inv_eta hH (z := zt 0 (1 / 2)) (η := 1 / 2) (by norm_num)
    (by rw [zt_half_im, abs_of_pos (by norm_num)]) σ
  norm_num at h
  exact h

private theorem egt_hε {M : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ} (hM : M.IsHermitian) (σ : Bool)
    (a : Zd 3 3) : ‖RBM.Green.avgErr 3 3 2 0 (1 / 2) M σ a‖ ≤ 3 := by
  have e : RBM.Green.avgErr 3 3 2 0 (1 / 2) M σ a =
      Matrix.trace (Gres (blockMat 3 3 2 M) (zt 0 (1 / 2)) σ * Eblk 3 3 2 a) - mSigma 0 σ := by
    rw [RBM.Green.avgErr, RBM.Green.greenBlk, Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul,
      Matrix.one_mul, Matrix.trace_smul, trace_Eblk, smul_eq_mul, mul_one]
  rw [e]
  calc ‖Matrix.trace (Gres (blockMat 3 3 2 M) (zt 0 (1 / 2)) σ * Eblk 3 3 2 a) - mSigma 0 σ‖
      ≤ ‖Matrix.trace (Gres (blockMat 3 3 2 M) (zt 0 (1 / 2)) σ * Eblk 3 3 2 a)‖ + ‖mSigma 0 σ‖ :=
        norm_sub_le _ _
    _ ≤ ‖Gres (blockMat 3 3 2 M) (zt 0 (1 / 2)) σ‖ + 1 :=
        add_le_add (RBM.Ind.split_norm_trace_mul_Eblk_le _ a) (norm_mSigma_zero σ).le
    _ ≤ 3 := by linarith [egt_norm_G hM σ]

/-- The loop `⟨[+, -], [0, 0]⟩` of length `2`. -/
private def I2 : RBM.Loop.LoopIdx (Zd 3 3) := ⟨[true, false], [0, 0]⟩

private theorem egt_hB {M : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ} (hM : M.IsHermitian)
    (k : ℕ) (hk : k ∈ Finset.Icc 1 I2.length) (b : Zd 3 3) :
    ‖loopL 3 3 2 (blockMat 3 3 2 M) (zt 0 (1 / 2)) (I2.cutGlue k b)‖ ≤ 1 / 8 := by
  have hH : (blockMat 3 3 2 M).IsHermitian := hM.submatrix _
  have hk' : 1 ≤ k ∧ k ≤ 2 := by simpa [RBM.Loop.LoopIdx.length, I2] using hk
  have hlenσ : (I2.cutGlue k b).σ.length = 3 := by
    simp [RBM.Loop.LoopIdx.cutGlue, I2]; omega
  have hlena : (I2.cutGlue k b).a.length = 3 := by
    simp [RBM.Loop.LoopIdx.cutGlue, I2]; omega
  have h := RBM.Ind.norm_gloop_le_of_le_abs_im hH (z := zt 0 (1 / 2)) (η := 1 / 2) (by norm_num)
    (by rw [zt_half_im, abs_of_pos (by norm_num)]) (I2.cutGlue k b) (by rw [hlenσ, hlena])
    (by rw [hlena]; norm_num)
  rw [hlena] at h
  refine h.trans (le_of_eq ?_)
  norm_num

example {M : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ} (hM : M.IsHermitian) :
    ‖egtNGUE 3 3 2 0 (1 / 2) M I2‖ ≤ (I2.length : ℝ) * (((2 * 3) ^ 3 : ℕ) : ℝ) * 3 * (1 / 8) :=
  norm_egtNGUE_le 3 2 0 (1 / 2) M I2 (egt_hε hM) (egt_hB hM)

end Egt

end RBM.Univ.GUEPhase.ProcInst

end
