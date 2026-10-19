/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.GUEPhase.HypA
import RBM3D.Green.EntryDom
import RBM3D.Induction.PerTimeCalc

/-!
# (7.45)G and (7.46)G for the stopped GUE-phase processes, part II (`d ≥ 3`)

The equation numbers (7.45), (7.46) below are those of [YY_25, §7.2].  The argument follows the two-dimensional
formalization (`GUEPhase/HypB` of RBM2D): the pathwise assembly on
the stopped processes, the per-step events and the fixed-point argument, written against the public
`Hyp_` interface of `HypA.lean`.

Proof idea.  On the good event, pathwise, the discrete Duhamel formula `Hyp_grid` holds at every
grid time `k ≤ σ*` with the bilinear drift (`primRhsGUE_sub`, `norm_primBilGUE_le`, `HypB_bil`),
the `E^{(G)}` drift (`norm_egtNGUE_le`, with `ε ≤ ‖G − m‖_max` from the entry bound, the Ward lower bound and the
odd-length loop bound for (7.45)G (`HypB_entry_le`, `HypB_eG_745`) and `ε ≤ D₁` for (7.46)G (`HypB_eG_746`)) and the
discretization error of `K̃` (`Hyp_Kt_disc`); off the grid the exact linear interpolation of the affine prefactor
and the concavity of `√·` (`Hyp_interp_bound`); the exponent bookkeeping is `HypB_fixed`.

## Contents

* `HypB_entry_le`, `HypB_eG_745`, `HypB_eG_746`, `HypB_q_745`: the entry bound at the stopped grid
  times, the `E^{(G)}` drift lines and the martingale line;
* `HypB_ev_grid`, `HypB_ev_delta`, `HypB_highProb_range`: the per-step events;
* `HypB_fixed`, `HypB_step_le`, `HypB_Kt_le_one`, `HypB_Lproc_grid`, `HypB_Dproc_grid`,
  `HypB_sqrt_cont`: the fixed-point argument and the grid facts.

The other helpers (`HypB_sum_reflect`, `HypB_bil`, `HypB_le_Dmax`, `HypB_scale_pos`, `HypB_path`)
are `private`.

## Differences from RBM2D (`d = 2` to `d ≥ 3`; the renaming of `HypA.lean`, `Proc.lean`)

RBM2D's `d : Sizes` becomes `sz : Sizes d`; `Z2 L` becomes `Zd d L`; `BlockIndex L W` becomes `Vtx d L W`;
`Idx L W` becomes `Idx d L W`; `spectralZ`/`spectralM` become `zt`/`mE`; `gloop L W (blockMat M)`
becomes `loopL d L W (blockMat d L W M)`; `RBM.Ind.LLf L W E u M` becomes
`loopL d L W (blockMat d L W M) (zt E u)`; `RBM.Ind.loopMax L W` becomes `RBM.Ind.loopMax d L W`;
`KLoop.mSig` becomes `mSigma`; `KLoop.Kcal` becomes `sz.STKloop` (on `loopOf`, as in
`Hyp_Kt_one`); `N = (W L)^2 = d.size n` becomes `N = (W L)^d = sz.size n`; `(W⁻¹)^2` becomes
`(W⁻¹)^d`.  Loops are on `blockMat` with labels in `Zd d (sz.L n)`; the entry good event is
`RBM.Green.entryDom_goodEvent_of_llErr`; thresholds and failure rates are on `sz.size n`.
`HypB_ev_grid`, `HypB_ev_delta`, `HypB_highProb_range` assume `hsz : Tendsto sz.size atTop atTop`;
since `1 ≤ sz.size n` is proved, no hypotheses `1 ≤ N` or `W L ≤ N` are needed.

The departure, relative to `gue_inv_W_le_loopMax` (whose `hell` is
`L² (1 - u) ≤ g²` with `g² = lam²/L^{d-2}`): `HypB_entry_le` takes `hd : 2 ≤ d`,
`hellN : L^d (1 - t₁) ≤ lam²`, has `(W^d)⁻¹` in `hD4`, and concludes `√(A c L₂)` with the Ward-bound
constant `A = 1 + 2 lam²` (RBM2D: `3 = 1 + 2`, `d = 2`, `lam = 1`).  Consequently
`HypB_eG_745` carries `√(A c L₂)` in `hdiag` and the prefactor `m A c N` (RBM2D: `4 m c N`), and
`HypB_fixed` carries `hCe : Ce ≤ 4 A m² N^{τ/2} N` and `3 + 4A` for `7` in `hbig`.  At `lam = 1`
(`A = 3`) `HypB_entry_le` is the RBM2D statement and `HypB_eG_745` has `3 m c N ≤ 4 m c N`; in
`HypB_fixed` the constants `4A = 12`, `3 + 4A = 15` are not those of RBM2D (`4`, `7`; constants
need not be optimal); the consumer's pair `Ce := m A c N ≤ 4 A m² c N` fits.  Helpers carry the
prefix `HypB_` and are `private`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Topology Matrix RBM RBM.Gauss RBM.Path RBM.Univ
open scoped NNReal ENNReal

variable {d : ℕ} (sz : Sizes d)

/-! ### Small helpers -/

section HypBHelpers

private theorem HypB_size_pos (n : ℕ) : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by
  have h1 : 0 < sz.size n := by
    unfold Sizes.size
    have hW := sz.W_pos n
    have hL := sz.three_le_L n
    positivity
  exact_mod_cast h1

private theorem HypB_one_le_size (n : ℕ) : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  have h1 : 0 < sz.size n := by
    unfold Sizes.size
    have hW := sz.W_pos n
    have hL := sz.three_le_L n
    positivity
  exact_mod_cast h1

/-- `sz.size n = (W L)^d` as a cast. -/
private theorem HypB_size_cast (n : ℕ) :
    (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) = ((sz.size n : ℕ) : ℝ) := rfl

private theorem HypB_loopOf_wf {L k : ℕ} [NeZero L] (σ : Fin k → Bool) (a : Fin k → Zd d L) :
    (loopOf σ a).WF := by
  change (List.ofFn σ).length = (List.ofFn a).length
  simp

private theorem HypB_loopOf_length {L k : ℕ} [NeZero L] (σ : Fin k → Bool) (a : Fin k → Zd d L) :
    (loopOf σ a).length = k := by
  simp [loopOf, RBM.Loop.LoopIdx.length]

/-- `Gres H z true = green H z` (`Ring.inverse` is `⁻¹`; a private twin of `IBPRem_Gres_true`). -/
private theorem HypB_Gres_true {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (z : ℂ) :
    Gres H z true = green H z := by
  simp only [green, Gres, Matrix.nonsing_inv_eq_ringInverse, ite_true]

/-- `‖(G − m)_{ij}‖` is the `llErrMat` of the (4.9) bridge. -/
private theorem HypB_llErr_eq {L W : ℕ} [NeZero L] [NeZero W] (E u : ℝ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (i j : Idx d L W) :
    RBM.Green.llErrMat d L W E u M i j =
      ‖(green M (zt E u) - mE E • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)) i j‖ := by
  unfold RBM.Green.llErrMat
  rw [HypB_Gres_true]
  by_cases h : i = j
  · subst h; simp [Matrix.sub_apply, Matrix.smul_apply]
  · simp [h, Matrix.sub_apply, Matrix.smul_apply]

end HypBHelpers

/-! ### The entry bound at the stopped grid times (with the Ward lower bound) -/

section HypBEntry

/-- **The entry bound at the stopped grid times, with the Ward lower bound**: on the entry-bound event (at level `c`,
the hypothesis `hD4`), for `j < σ*` every diagonal entry of `G_j - m` is at most `√(A c L₂)`, `A = 1 + 2 lam²`
(RBM2D has `3 = 1 + 2`, `lam = 1`). -/
theorem HypB_entry_le (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 < κ) (n0 : ℕ) {E t1 t0 : ℕ → ℝ} {τU : ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1) (n : ℕ)
    (hellN : (sz.L n : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2) (hδN : gueDelta sz τU n ≤ (mE (E n)).im / 2)
    (ω : PathΩ sz) {c : ℝ} (hc : 0 ≤ c)
    (hD4 : ∀ (k : Fin (gueGridK sz n0 n + 1)) (i j : Idx d (sz.L n) (sz.W n)),
      {ω' : PathΩ sz | ∀ a b : Idx d (sz.L n) (sz.W n),
          ‖(green (gueH sz t1 t0 (gueGridK sz n0) n k ω')
              (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n k)) -
            mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) a b‖ ≤
          gueDelta sz τU n}.indicator
        (fun ω' => ‖(green (gueH sz t1 t0 (gueGridK sz n0) n k ω')
              (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n k)) -
            mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) i j‖ ^ 2) ω ≤
        c * (gueLmax sz E t1 t0 (gueGridK sz n0) n 2 k ω + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹))
    {j : ℕ} (hj : j < gueStop sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) n ω)
    (q : Idx d (sz.L n) (sz.W n)) :
    ‖(green (gueH sz t1 t0 (gueGridK sz n0) n j ω)
        (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n j)) -
        mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) q q‖ ≤
      Real.sqrt ((1 + 2 * sz.lam n ^ 2) * c * RBM.Ind.loopMax d (sz.L n) (sz.W n)
        (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 (gueGridK sz n0) n j ω))
        (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n j)) 2) := by
  have hσK : gueStop sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) n ω ≤ gueGridK sz n0 n :=
    firstHit_le _ _ _ ω
  have hjK : j < gueGridK sz n0 n + 1 := by omega
  have hj' : j < firstHit (fun k ω' => gueDev sz E t1 t0 (gueGridK sz n0) n k ω')
      (gueDelta sz τU n) (gueGridK sz n0 n) ω := hj
  have hdev : gueDev sz E t1 t0 (gueGridK sz n0) n j ω < gueDelta sz τU n :=
    lt_firstHit_imp (fun k ω' => gueDev sz E t1 t0 (gueGridK sz n0) n k ω') (gueDelta sz τU n)
      (gueGridK sz n0 n) hj'
  have hentry : ∀ i i' : Idx d (sz.L n) (sz.W n),
      ‖(green (gueH sz t1 t0 (gueGridK sz n0) n j ω)
        (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n j)) -
        mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) i i'‖ ≤
        gueDelta sz τU n := by
    intro i i'
    refine le_trans ?_ hdev.le
    unfold gueDev
    exact le_ciSup (f := fun ij : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) =>
      ‖(green (gueH sz t1 t0 (gueGridK sz n0) n j ω)
        (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n j)) -
        mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) ij.1 ij.2‖)
      (Set.finite_range _).bddAbove (i, i')
  have h4 : ‖(green (gueH sz t1 t0 (gueGridK sz n0) n j ω)
        (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n j)) -
        mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) q q‖ ^ 2 ≤
      c * (RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 (gueGridK sz n0) n j ω))
        (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n j)) 2 +
        (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) := by
    have h := hD4 ⟨j, hjK⟩ q q
    rw [Set.indicator_of_mem (show ω ∈ {ω' : PathΩ sz | ∀ a b : Idx d (sz.L n) (sz.W n),
      ‖(green (gueH sz t1 t0 (gueGridK sz n0) n j ω')
        (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n j)) -
        mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) a b‖ ≤
        gueDelta sz τU n} from hentry)] at h
    exact h
  -- the Ward lower bound: `W^{-d} ≤ 2 lam² L₂` on the a-priori event
  have hEN : |E n| < 2 := lt_of_le_of_lt (hE n) (by linarith)
  have hu1 : gridTime t1 t0 (gueGridK sz n0) n j < 1 :=
    lt_of_le_of_lt (Hyp_time_le (ht10 n) (gueGridK_ne_zero sz n0 n) (by omega)) (ht0 n)
  have hLpos : (0 : ℝ) < (sz.L n : ℝ) := by
    have := sz.three_le_L n; exact_mod_cast (by omega : 0 < sz.L n)
  have hLd : (0 : ℝ) < (sz.L n : ℝ) ^ (d - 2) := pow_pos hLpos _
  set g2 : ℝ := sz.lam n ^ 2 / (sz.L n : ℝ) ^ (d - 2) with hg2
  have hg20 : 0 ≤ g2 := div_nonneg (sq_nonneg _) hLd.le
  have hellj : (sz.L n : ℝ) ^ 2 * (1 - gridTime t1 t0 (gueGridK sz n0) n j) ≤
      Real.sqrt g2 ^ 2 := by
    rw [Real.sq_sqrt hg20, hg2, le_div_iff₀ hLd]
    have h1 := Hyp_time_ge (K := gueGridK sz n0) (ht10 n) j
    have h2 : 1 - gridTime t1 t0 (gueGridK sz n0) n j ≤ 1 - t1 n := by linarith
    have hpow : (sz.L n : ℝ) ^ d = (sz.L n : ℝ) ^ 2 * (sz.L n : ℝ) ^ (d - 2) := by
      rw [← pow_add]; congr 1; omega
    calc (sz.L n : ℝ) ^ 2 * (1 - gridTime t1 t0 (gueGridK sz n0) n j) * (sz.L n : ℝ) ^ (d - 2)
        = (sz.L n : ℝ) ^ d * (1 - gridTime t1 t0 (gueGridK sz n0) n j) := by rw [hpow]; ring
      _ ≤ (sz.L n : ℝ) ^ d * (1 - t1 n) :=
          mul_le_mul_of_nonneg_left h2 (pow_pos hLpos d).le
      _ ≤ sz.lam n ^ 2 := hellN
  have hW := gue_inv_W_le_loopMax (L := sz.L n) (W := sz.W n)
    (gueH_isHermitian sz t1 t0 (gueGridK sz n0) n j ω) hEN hu1 hellj
    (RBM.Green.entryDom_goodEvent_of_llErr _ _ _ _ _ _ _ fun i i' => by
      rw [HypB_llErr_eq]; exact hentry i i') hδN
  have hL0 := RBM.Ind.loopMax_nonneg (L := sz.L n) (W := sz.W n)
    (H := blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 (gueGridK sz n0) n j ω))
    (z := zt (E n) (gridTime t1 t0 (gueGridK sz n0) n j)) 2
  have hWinv : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ = (((sz.W n : ℕ) : ℝ)⁻¹) ^ d := by rw [inv_pow]
  have hgg : 2 * (sz.L n : ℝ) ^ (d - 2) * Real.sqrt g2 ^ 2 = 2 * sz.lam n ^ 2 := by
    rw [Real.sq_sqrt hg20, hg2]; field_simp
  rw [hgg] at hW
  apply Real.le_sqrt_of_sq_le
  calc _ ≤ c * (RBM.Ind.loopMax d (sz.L n) (sz.W n)
          (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 (gueGridK sz n0) n j ω))
          (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n j)) 2 +
          (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) := h4
    _ ≤ c * (RBM.Ind.loopMax d (sz.L n) (sz.W n)
          (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 (gueGridK sz n0) n j ω))
          (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n j)) 2 +
          2 * sz.lam n ^ 2 * RBM.Ind.loopMax d (sz.L n) (sz.W n)
          (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 (gueGridK sz n0) n j ω))
          (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n j)) 2) := by
        rw [hWinv]; gcongr
    _ = (1 + 2 * sz.lam n ^ 2) * c * RBM.Ind.loopMax d (sz.L n) (sz.W n)
          (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 (gueGridK sz n0) n j ω))
          (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n j)) 2 := by ring

end HypBEntry

/-! ### The `E^{(G)}` and martingale lines of (7.45)G and (7.46)G -/

section HypBLines

/-- `|L_k(J) - K̃_{u_k}(J)| ≤ D^{(|J|)}_k` for every well-formed `J`. -/
private theorem HypB_le_Dmax (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (n k : ℕ) (ω : PathΩ sz)
    (J : RBM.Loop.LoopIdx (Zd d (sz.L n))) (hJ : J.WF) :
    ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k ω))
        (zt (E n) (gridTime t1 t0 K n k)) J -
      Kt n (gridTime t1 t0 K n k) J‖ ≤ gueDmax sz E t1 t0 K Kt n J.length k ω := by
  obtain ⟨x, hx⟩ := Hyp_exists_loopOf J hJ
  unfold gueDmax
  have h := le_ciSup (f := fun x' : (Fin J.length → Bool) × (Fin J.length → Zd d (sz.L n)) =>
    ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k ω))
        (zt (E n) (gridTime t1 t0 K n k)) (loopOf x'.1 x'.2) -
      Kt n (gridTime t1 t0 K n k) (loopOf x'.1 x'.2)‖) (Set.finite_range _).bddAbove x
  simp only [hx] at h
  exact h

/-- **The drift line for (7.45)G** (even `m = 2l`): `|𝓔̃| ≤ m A c N L₂ L_m`, `A = 1 + 2 lam²`
(RBM2D has `4 m c N`), from `ε ≤ √(A c L₂)` (the entry bound, the conclusion of
`HypB_entry_le`) and the odd-length bound `L_{2l+1} ≤ √L₂ L_{2l}`. -/
theorem HypB_eG_745 {E t1 t0 : ℕ → ℝ} (K : ℕ → ℕ) (n j : ℕ) (ω : PathΩ sz)
    {c : ℝ} (hc : 1 ≤ c) {l : ℕ} (hl : 1 ≤ l)
    (hdiag : ∀ q : Idx d (sz.L n) (sz.W n),
      ‖(green (gueH sz t1 t0 K n j ω) (zt (E n) (gridTime t1 t0 K n j)) -
        mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) q q‖ ≤
      Real.sqrt ((1 + 2 * sz.lam n ^ 2) * c * RBM.Ind.loopMax d (sz.L n) (sz.W n)
        (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω))
        (zt (E n) (gridTime t1 t0 K n j)) 2))
    (x : (Fin (2 * l) → Bool) × (Fin (2 * l) → Zd d (sz.L n))) :
    ‖egtNGUE d (sz.L n) (sz.W n) (E n) (gridTime t1 t0 K n j) (gueH sz t1 t0 K n j ω)
        (loopOf x.1 x.2)‖ ≤
      (((2 * l : ℕ) : ℝ) * (1 + 2 * sz.lam n ^ 2) * c * ((sz.size n : ℕ) : ℝ)) *
        (RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω))
            (zt (E n) (gridTime t1 t0 K n j)) 2 *
          RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω))
            (zt (E n) (gridTime t1 t0 K n j)) (2 * l)) := by
  set M := gueH sz t1 t0 K n j ω with hMdef
  set u := gridTime t1 t0 K n j with hudef
  set a : ℝ := 1 + 2 * sz.lam n ^ 2 with hadef
  have ha1 : 1 ≤ a := by rw [hadef]; nlinarith [sq_nonneg (sz.lam n)]
  have hH : M.IsHermitian := gueH_isHermitian sz t1 t0 K n j ω
  have hHb : (blockMat d (sz.L n) (sz.W n) M).IsHermitian := hH.submatrix _
  set L2 := RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) (zt (E n) u) 2
    with hL2
  set Ln := RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) (zt (E n) u)
    (2 * l) with hLn
  have hL20 : 0 ≤ L2 := RBM.Ind.loopMax_nonneg _
  have hLn0 : 0 ≤ Ln := RBM.Ind.loopMax_nonneg _
  have hlen : (loopOf x.1 x.2).length = 2 * l := HypB_loopOf_length _ _
  have hb := norm_egtNGUE_le (sz.L n) (sz.W n) (E n) u M (loopOf x.1 x.2)
    (ε := Real.sqrt (a * c * L2)) (B := Real.sqrt L2 * Ln)
    (fun σ a' => Hyp_eps_le_dev hH (E n) u hdiag σ a')
    (fun k hk b => (Hyp_cutGlue_le (HypB_loopOf_wf _ _) hk b).trans (by
      rw [hlen]; exact gueLoopMax_odd_succ_le hHb (zt (E n) u) hl))
  rw [hlen, HypB_size_cast] at hb
  refine hb.trans ?_
  have hc0 : 0 ≤ c := by linarith
  have hac1 : 1 ≤ a * c := by nlinarith
  have hs : Real.sqrt (a * c * L2) * (Real.sqrt L2 * Ln) = Real.sqrt (a * c) * (L2 * Ln) := by
    rw [Real.sqrt_mul (by positivity) L2]
    have := Real.mul_self_sqrt hL20
    calc Real.sqrt (a * c) * Real.sqrt L2 * (Real.sqrt L2 * Ln)
        = Real.sqrt (a * c) * (Real.sqrt L2 * Real.sqrt L2) * Ln := by ring
      _ = Real.sqrt (a * c) * (L2 * Ln) := by rw [this]; ring
  have h3 : Real.sqrt (a * c) ≤ a * c := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hS : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hn : (0 : ℝ) ≤ ((2 * l : ℕ) : ℝ) := Nat.cast_nonneg _
  calc ((2 * l : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) * Real.sqrt (a * c * L2) *
        (Real.sqrt L2 * Ln)
      = ((2 * l : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) * (Real.sqrt (a * c) * (L2 * Ln)) := by
        rw [mul_assoc _ (Real.sqrt (a * c * L2)), hs]
    _ ≤ ((2 * l : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) * (a * c * (L2 * Ln)) := by
        gcongr
    _ = _ := by ring

/-- **The drift line for (7.46)G**: `|𝓔̃| ≤ m N D₁ L_{m+1}`, from `ε ≤ D^{(1)}` (`K̃ = m_σ` at
length `1`,
`Hyp_Kt_one`). -/
theorem HypB_eG_746 {E t1 t0 : ℕ → ℝ} (K : ℕ → ℕ) (n0 : ℕ) (hn0 : 1 ≤ n0)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ)
    (hKinit : ∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Kt n (t1 n) (loopOf σ a) = sz.STKloop n (E n) (t1 n) σ a)
    (hK : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : RBM.Loop.LoopIdx (Zd d (sz.L n)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t)
    (n j m : ℕ) (hu : gridTime t1 t0 K n j ∈ Set.Icc (t1 n) (t0 n)) (ω : PathΩ sz)
    (x : (Fin m → Bool) × (Fin m → Zd d (sz.L n))) :
    ‖egtNGUE d (sz.L n) (sz.W n) (E n) (gridTime t1 t0 K n j) (gueH sz t1 t0 K n j ω)
        (loopOf x.1 x.2)‖ ≤
      ((m : ℝ) * ((sz.size n : ℕ) : ℝ)) *
        (gueDmax sz E t1 t0 K Kt n 1 j ω *
          RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω))
            (zt (E n) (gridTime t1 t0 K n j)) (m + 1)) := by
  have hlen : (loopOf x.1 x.2).length = m := HypB_loopOf_length _ _
  have hε : ∀ (σ : Bool) (a : Zd d (sz.L n)),
      ‖RBM.Green.avgErr d (sz.L n) (sz.W n) (E n) (gridTime t1 t0 K n j) (gueH sz t1 t0 K n j ω) σ a‖ ≤
        gueDmax sz E t1 t0 K Kt n 1 j ω := by
    intro σ a
    have h1 : RBM.Green.avgErr d (sz.L n) (sz.W n) (E n) (gridTime t1 t0 K n j) (gueH sz t1 t0 K n j ω) σ a =
        loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω))
          (zt (E n) (gridTime t1 t0 K n j)) ⟨[σ], [a]⟩ - mSigma (E n) σ :=
      Hyp_trace_eq_gloop_one (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω)) (zt (E n) (gridTime t1 t0 K n j))
        (mSigma (E n)) σ a
    rw [h1, ← Hyp_Kt_one sz n0 hn0 Kt hKinit hK n hu σ a]
    exact HypB_le_Dmax sz E t1 t0 K Kt n j ω ⟨[σ], [a]⟩ rfl
  have hb := norm_egtNGUE_le (sz.L n) (sz.W n) (E n) (gridTime t1 t0 K n j) (gueH sz t1 t0 K n j ω)
    (loopOf x.1 x.2) hε
    (fun k hk b => by
      have := Hyp_cutGlue_le (L := sz.L n) (W := sz.W n)
        (H := blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω)) (z := zt (E n) (gridTime t1 t0 K n j))
        (HypB_loopOf_wf x.1 x.2) hk b
      rwa [hlen] at this)
  rw [hlen, HypB_size_cast] at hb
  refine hb.trans (le_of_eq ?_)
  ring

/-- The martingale line of h745E: `√(a L_{4l}) ≤ √a L_{2l}`, `a = N⁻¹η⁻²`. -/
theorem HypB_q_745 {L W : ℕ} [NeZero L] [NeZero W]
    {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian) (z : ℂ) {a : ℝ}
    (ha : 0 ≤ a) {l : ℕ} (hl : 1 ≤ l) :
    Real.sqrt (a * RBM.Ind.loopMax d L W H z (2 * (2 * l))) ≤
      Real.sqrt a * RBM.Ind.loopMax d L W H z (2 * l) := by
  have h := gueLoopMax_four_mul_le hH z hl
  rw [show 2 * (2 * l) = 4 * l by ring]
  calc Real.sqrt (a * RBM.Ind.loopMax d L W H z (4 * l))
      ≤ Real.sqrt (a * RBM.Ind.loopMax d L W H z (2 * l) ^ 2) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h ha)
    _ = Real.sqrt a * RBM.Ind.loopMax d L W H z (2 * l) := by
        rw [Real.sqrt_mul ha, Real.sqrt_sq (RBM.Ind.loopMax_nonneg _)]

end HypBLines

/-! ### Eventual deterministic facts on the size scale -/

section HypBEventually

/-- The grid is fine enough for the discretization error (`M³ N Δ ≤ 1`) and for the absorption of
the discretization error into `N^{-2n₀}` (`N = sz.size n`, `K = (N + 1)^{32 n₀ + 64}`). -/
private theorem HypB_grid_of_size (n0 N : ℕ) (hN : 3 * (2 * n0) ^ 6 + (2 * n0) ^ 3 + 1 ≤ N) :
    ((2 * n0 : ℕ) : ℝ) ^ 3 * (N : ℝ) * ((((N + 1) ^ (32 * n0 + 64) : ℕ) : ℝ))⁻¹ ≤ 1 ∧
      3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * (N : ℝ) ^ 2 * ((((N + 1) ^ (32 * n0 + 64) : ℕ) : ℝ))⁻¹ ≤
        ((N : ℝ)⁻¹) ^ (2 * n0) := by
  have hN1 : 1 ≤ N := by omega
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hKpos : (0 : ℝ) < (((N + 1) ^ (32 * n0 + 64) : ℕ) : ℝ) := by positivity
  have hKge : (N : ℝ) ^ (2 * n0 + 3) ≤ (((N + 1) ^ (32 * n0 + 64) : ℕ) : ℝ) := by
    push_cast
    calc (N : ℝ) ^ (2 * n0 + 3) ≤ (N : ℝ) ^ (32 * n0 + 64) :=
          pow_le_pow_right₀ hNR (by omega)
      _ ≤ ((N : ℝ) + 1) ^ (32 * n0 + 64) := pow_le_pow_left₀ hN0.le (by linarith) _
  have hA : ((3 * (2 * n0) ^ 6 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega)
  have hB : (((2 * n0) ^ 3 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega)
  push_cast at hA hB
  push_cast at hKpos hKge ⊢
  constructor
  · rw [← div_eq_mul_inv, div_le_one hKpos]
    calc ((2 * (n0 : ℝ))) ^ 3 * (N : ℝ) ≤ (N : ℝ) * (N : ℝ) :=
          mul_le_mul_of_nonneg_right hB hN0.le
      _ = (N : ℝ) ^ 2 := by ring
      _ ≤ (N : ℝ) ^ (2 * n0 + 3) := pow_le_pow_right₀ hNR (by omega)
      _ ≤ _ := hKge
  · rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ hKpos]
    have hpow : (0 : ℝ) < (N : ℝ) ^ (2 * n0) := pow_pos hN0 _
    rw [← div_eq_inv_mul, le_div_iff₀ hpow]
    calc 3 * (2 * (n0 : ℝ)) ^ 6 * (N : ℝ) ^ 2 * (N : ℝ) ^ (2 * n0)
        ≤ (N : ℝ) * (N : ℝ) ^ 2 * (N : ℝ) ^ (2 * n0) := by gcongr
      _ = (N : ℝ) ^ (2 * n0 + 3) := by ring
      _ ≤ _ := hKge

/-- The grid is fine enough for the discretization error (`M³ N Δ ≤ 1`) and for the absorption of
the discretization error into `N^{-2n₀}`, eventually in the size index (`N = sz.size n`, under
`hsz : Tendsto sz.size atTop atTop`). -/
theorem HypB_ev_grid (hsz : Tendsto sz.size atTop atTop) (n0 : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ((2 * n0 : ℕ) : ℝ) ^ 3 * ((sz.size n : ℕ) : ℝ) * ((gueGridK sz n0 n : ℝ))⁻¹ ≤ 1 ∧
      3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * ((sz.size n : ℕ) : ℝ) ^ 2 * ((gueGridK sz n0 n : ℝ))⁻¹ ≤
        (((sz.size n : ℕ) : ℝ)⁻¹) ^ (2 * n0) := by
  filter_upwards [hsz.eventually
    (eventually_ge_atTop (3 * (2 * n0) ^ 6 + (2 * n0) ^ 3 + 1))] with n hN
  exact HypB_grid_of_size n0 (sz.size n) hN

/-- `Im m ≥ √(2κ)/2` for `|E| ≤ 2 - κ`, hence `δ_n = N^{-τU/4} ≤ Im m / 2` eventually in the size
index. -/
theorem HypB_ev_delta {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU)
    (hsz : Tendsto sz.size atTop atTop) {E : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) :
    ∀ᶠ n : ℕ in atTop, gueDelta sz τU n ≤ (mE (E n)).im / 2 := by
  have hκ2 : κ ≤ 2 := by have := hE 0; have := abs_nonneg (E 0); linarith
  have hlow : ∀ n, Real.sqrt (2 * κ) / 2 ≤ (mE (E n)).im := by
    intro n
    rw [mE_im]
    have hsq : E n ^ 2 ≤ (2 - κ) ^ 2 := by
      have h := hE n
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    have : 2 * κ ≤ 4 - E n ^ 2 := by nlinarith
    gcongr
  have hc : 0 < Real.sqrt (2 * κ) / 4 := by positivity
  filter_upwards [hsz.eventually
    (eventually_le_rpow (Real.sqrt (2 * κ) / 4)⁻¹ (by positivity : 0 < τU / 4)),
    hsz.eventually (eventually_ge_atTop 1)] with n hN hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  unfold gueDelta
  rw [Real.rpow_neg hN0.le]
  have hpos : 0 < ((sz.size n : ℕ) : ℝ) ^ (τU / 4) := Real.rpow_pos_of_pos hN0 _
  calc (((sz.size n : ℕ) : ℝ) ^ (τU / 4))⁻¹ ≤ Real.sqrt (2 * κ) / 4 := by
        rw [inv_le_comm₀ hpos hc]; exact hN
    _ ≤ (mE (E n)).im / 2 := by linarith [hlow n]

end HypBEventually

/-! ### Finitely many high-probability events -/

/-- Finitely many `HighProbAt` events hold simultaneously with high probability. -/
theorem HypB_highProb_range {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (hsz : Tendsto sz.size atTop atTop) (M : ℕ) (Ξ : ℕ → ℕ → Set Ω)
    (h : ∀ m, 1 ≤ m → m ≤ M → HighProbAt P sz.size (Ξ m)) :
    HighProbAt P sz.size (fun n => {ω | ∀ m, 1 ≤ m → m ≤ M → ω ∈ Ξ m n}) := by
  induction M with
  | zero =>
    exact RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono (highProbAt_univ P sz.size)
      (Eventually.of_forall fun n ω _ m h1 h2 => by omega)
  | succ M ih =>
    have h1 := ih fun m hm1 hm2 => h m hm1 (by omega)
    have h2 := h (M + 1) (by omega) le_rfl
    refine RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono
      (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_inter hsz h1 h2)
      (Eventually.of_forall fun n ω hω m hm1 hm2 => ?_)
    rcases Nat.lt_or_ge m (M + 1) with hlt | hge
    · exact hω.1 m hm1 (by omega)
    · obtain rfl : m = M + 1 := by omega
      exact hω.2


/-! ### Drift bounds and the pathwise assembly -/

section HypBPath

/-- `∑_{j=2}^m h(m-j+2) = ∑_{j=2}^m h(j)`. -/
private theorem HypB_sum_reflect (n : ℕ) (h : ℕ → ℝ) :
    ∑ j ∈ Finset.Icc 2 n, h (n - j + 2) = ∑ j ∈ Finset.Icc 2 n, h j := by
  refine Finset.sum_nbij' (fun j => n - j + 2) (fun j => n - j + 2) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha; omega
  · intro a _; rfl

/-- **The bilinear drift** ((7.39), (7.40), `d ≥ 3`): with `|K̃(J)| ≤ c λ^{|J|-1}` and
`|L(J) - K̃(J)| ≤ D_{|J|}`, `|F(L) - F(K̃)| ≤ 3 m² c N ∑_{i=2}^m (λ^{i-1} + D_i) D_{m-i+2}`,
`N = (W L)^d`. -/
private theorem HypB_bil {L W : ℕ} [NeZero L] (Lf K : RBM.Loop.LoopIdx (Zd d L) → ℂ)
    (I : RBM.Loop.LoopIdx (Zd d L)) (hI : I.WF) (Dv : ℕ → ℝ) {lam c : ℝ} (hc : 1 ≤ c) (hlam : 0 ≤ lam)
    (hDv0 : ∀ i, 0 ≤ Dv i)
    (hD : ∀ J : RBM.Loop.LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖Lf J - K J‖ ≤ Dv J.length)
    (hK : ∀ J : RBM.Loop.LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖K J‖ ≤ c * lam ^ (J.length - 1)) :
    ‖primRhsGUE d L W Lf I - primRhsGUE d L W K I‖ ≤
      3 * (I.length : ℝ) ^ 2 * c * (((W * L) ^ d : ℕ) : ℝ) *
        ∑ i ∈ Finset.Icc 2 I.length, (lam ^ (i - 1) + Dv i) * Dv (I.length - i + 2) := by
  set n := I.length with hn
  set T := ∑ i ∈ Finset.Icc 2 n, (lam ^ (i - 1) + Dv i) * Dv (n - i + 2) with hT
  set S : ℝ := (((W * L) ^ d : ℕ) : ℝ) with hS
  have hS0 : 0 ≤ S := Nat.cast_nonneg _
  have hc0 : 0 ≤ c := by linarith
  have hBk0 : ∀ i, 0 ≤ c * lam ^ (i - 1) := fun i => mul_nonneg hc0 (pow_nonneg hlam _)
  have hD' : ∀ J : RBM.Loop.LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ n →
      ‖(Lf - K) J‖ ≤ Dv J.length := fun J h1 h2 h3 => by rw [Pi.sub_apply]; exact hD J h1 h2 h3
  rw [primRhsGUE_sub]
  have b1 := norm_primBilGUE_le d L W K (Lf - K) (fun i => c * lam ^ (i - 1)) Dv I hI
    hK hD' hBk0 hDv0
  have b2 := norm_primBilGUE_le d L W (Lf - K) K Dv (fun i => c * lam ^ (i - 1)) I hI
    hD' hK hDv0 hBk0
  have b3 := norm_primBilGUE_le d L W (Lf - K) (Lf - K) Dv Dv I hI hD' hD' hDv0 hDv0
  have hterm : ∀ i ∈ Finset.Icc 2 n, 0 ≤ (lam ^ (i - 1) + Dv i) * Dv (n - i + 2) :=
    fun i _ => mul_nonneg (add_nonneg (pow_nonneg hlam _) (hDv0 i)) (hDv0 _)
  have hT0 : 0 ≤ T := Finset.sum_nonneg hterm
  -- the three sums against `c T`
  have s2 : ∑ j ∈ Finset.Icc 2 n, Dv (n - j + 2) * (c * lam ^ (j - 1)) ≤ c * T := by
    rw [hT, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have := mul_nonneg (mul_nonneg hc0 (hDv0 i)) (hDv0 (n - i + 2))
    nlinarith
  have s1 : ∑ j ∈ Finset.Icc 2 n, c * lam ^ (n - j + 2 - 1) * Dv j ≤ c * T := by
    have hre := HypB_sum_reflect n (fun j => c * lam ^ (j - 1) * Dv (n - j + 2))
    have hre' : ∑ j ∈ Finset.Icc 2 n, c * lam ^ (n - j + 2 - 1) * Dv j =
        ∑ j ∈ Finset.Icc 2 n, c * lam ^ (n - j + 2 - 1) * Dv (n - (n - j + 2) + 2) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_Icc] at hj
      rw [show n - (n - j + 2) + 2 = j by omega]
    rw [hre', hre]
    refine le_trans (le_of_eq ?_) s2
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have s3 : ∑ j ∈ Finset.Icc 2 n, Dv (n - j + 2) * Dv j ≤ c * T := by
    refine le_trans ?_ (le_mul_of_one_le_left hT0 hc)
    rw [hT]
    refine Finset.sum_le_sum fun i _ => ?_
    have := hDv0 (n - i + 2)
    have := pow_nonneg hlam (i - 1)
    nlinarith [hDv0 i]
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * S := by positivity
  calc ‖primBilGUE d L W K (Lf - K) I + primBilGUE d L W (Lf - K) K I +
          primBilGUE d L W (Lf - K) (Lf - K) I‖
      ≤ ‖primBilGUE d L W K (Lf - K) I‖ + ‖primBilGUE d L W (Lf - K) K I‖ +
          ‖primBilGUE d L W (Lf - K) (Lf - K) I‖ := norm_add₃_le
    _ ≤ (n : ℝ) ^ 2 * S * (c * T) + (n : ℝ) ^ 2 * S * (c * T) + (n : ℝ) ^ 2 * S * (c * T) := by
        gcongr
        · exact b1.trans (mul_le_mul_of_nonneg_left s1 hn2)
        · exact b2.trans (mul_le_mul_of_nonneg_left s2 hn2)
        · exact b3.trans (mul_le_mul_of_nonneg_left s3 hn2)
    _ = 3 * (n : ℝ) ^ 2 * c * S * T := by ring

/-- `N η_u > 0` on `[t₁, t₀]`. -/
private theorem HypB_scale_pos {E t0 : ℕ → ℝ} {n : ℕ} (hE : |E n| < 2)
    (ht0 : t0 n < 1) {u : ℝ} (hu : u ≤ t0 n) : 0 < gueScale sz E n u := by
  unfold gueScale
  exact mul_pos (HypB_size_pos sz n) (etaT_pos hE (by linarith))

/-- **The pathwise bound at one length `m`**: on the good event, the
stopped interpolated `D_m(t)` is bounded by a constant times the right side
`N(t-t₁) sup g₁ + (Nη_t)^{-m} + N(t-t₁) sup g₃ + √(t-t₁) sup g₄`, for all `t ∈ [t₁, t₀]`. -/
private theorem HypB_path (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (n m : ℕ) (ω : PathΩ sz)
    (g3 g4 : ℝ → ℝ) {c Ce err A : ℝ}
    (hE : |E n| < 2) (ht1 : 0 ≤ t1 n) (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1) (hK0 : K n ≠ 0)
    (hm : 1 ≤ m) (hc : 1 ≤ c) (hA : 0 ≤ A) (hCe0 : 0 ≤ Ce)
    (hCe : Ce ≤ 4 * A * (m : ℝ) ^ 2 * c * ((sz.size n : ℕ) : ℝ))
    (hΔ : gridStep t1 t0 K n ≤ 1 - t0 n)
    (herr : ∀ t ∈ Set.Icc (t1 n) (t0 n), err ≤ (gueScale sz E n t)⁻¹ ^ m)
    (hg3 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ g3 u) (hg4 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ g4 u)
    (hg3c : ContinuousOn g3 (Set.Icc (t1 n) (t0 n)))
    (hg4c : ContinuousOn g4 (Set.Icc (t1 n) (t0 n)))
    (h0 : ∀ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
      ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n 0 ω))
          (zt (E n) (gridTime t1 t0 K n 0)) (loopOf x.1 x.2) -
        Kt n (gridTime t1 t0 K n 0) (loopOf x.1 x.2)‖ ≤ c * (gueScale sz E n (t1 n))⁻¹ ^ m)
    (hM : ∀ k ≤ K n, ∀ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
      ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k ω))
          (zt (E n) (gridTime t1 t0 K n k)) (loopOf x.1 x.2)
          - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n 0 ω))
            (zt (E n) (gridTime t1 t0 K n 0)) (loopOf x.1 x.2)
          - (gridStep t1 t0 K n : ℂ) * ∑ j ∈ Finset.range k,
              genMatGUE d (sz.L n) (sz.W n) (E n) (gridTime t1 t0 K n j)
                (gueH sz t1 t0 K n j ω) (loopOf x.1 x.2)‖ ≤
        c * (Real.sqrt (gridTime t1 t0 K n k - t1 n) *
          (⨆ j : Fin k, Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ *
            (etaT (E n) (gridTime t1 t0 K n j))⁻¹ ^ 2 *
            RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω))
              (zt (E n) (gridTime t1 t0 K n j)) (2 * m)))
          + (gueScale sz E n (gridTime t1 t0 K n k))⁻¹ ^ m))
    (hq : ∀ j < gueStop sz E t1 t0 K δ n ω,
      Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ * (etaT (E n) (gridTime t1 t0 K n j))⁻¹ ^ 2 *
        RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω))
          (zt (E n) (gridTime t1 t0 K n j)) (2 * m)) ≤ g4 (gridTime t1 t0 K n j))
    (hKt : ∀ j ≤ K n, ∀ J : RBM.Loop.LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ m →
      ‖Kt n (gridTime t1 t0 K n j) J‖ ≤ c * (gueScale sz E n (gridTime t1 t0 K n j))⁻¹ ^
        (J.length - 1))
    (heG : ∀ j < gueStop sz E t1 t0 K δ n ω, ∀ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
      ‖egtNGUE d (sz.L n) (sz.W n) (E n) (gridTime t1 t0 K n j) (gueH sz t1 t0 K n j ω)
          (loopOf x.1 x.2)‖ ≤ Ce * g3 (gridTime t1 t0 K n j))
    (hdisc : ∀ k ≤ K n, ∀ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
      ‖Kt n (gridTime t1 t0 K n k) (loopOf x.1 x.2) - Kt n (gridTime t1 t0 K n 0) (loopOf x.1 x.2) -
        (gridStep t1 t0 K n : ℂ) * ∑ j ∈ Finset.range k,
          primRhsGUE d (sz.L n) (sz.W n) (Kt n (gridTime t1 t0 K n j)) (loopOf x.1 x.2)‖ ≤ err)
    {t : ℝ} (ht : t ∈ Set.Icc (t1 n) (t0 n)) :
    gueDproc sz E t1 t0 K δ Kt n m t ω ≤ c * (2 + 2 ^ m + (3 + 4 * A) * (m : ℝ) ^ 2) *
      (((sz.size n : ℕ) : ℝ) * (t - t1 n) * supOn (fun u => ∑ k ∈ Finset.Icc 2 m,
          ((((sz.size n : ℕ) : ℝ) * etaT (E n) u)⁻¹ ^ (k - 1) +
            gueDproc sz E t1 t0 K δ Kt n k u ω) * gueDproc sz E t1 t0 K δ Kt n (m - k + 2) u ω)
          (t1 n) t
        + (((sz.size n : ℕ) : ℝ) * etaT (E n) t)⁻¹ ^ m
        + ((sz.size n : ℕ) : ℝ) * (t - t1 n) * supOn g3 (t1 n) t
        + Real.sqrt (t - t1 n) * supOn g4 (t1 n) t) := by
  set S : ℝ := ((sz.size n : ℕ) : ℝ) with hSdef
  have hS0 : 0 < S := HypB_size_pos sz n
  set σ := gueStop sz E t1 t0 K δ n ω with hσdef
  have hσK : σ ≤ K n := firstHit_le _ _ _ ω
  have hc0 : 0 ≤ c := by linarith
  have hscale_eq : ∀ u, gueScale sz E n u = S * etaT (E n) u := fun u => rfl
  have hηpos : ∀ u, u ≤ t0 n → 0 < etaT (E n) u := fun u hu => etaT_pos hE (by linarith)
  set g1 : ℝ → ℝ := fun u => ∑ k ∈ Finset.Icc 2 m,
    ((S * etaT (E n) u)⁻¹ ^ (k - 1) + gueDproc sz E t1 t0 K δ Kt n k u ω) *
      gueDproc sz E t1 t0 K δ Kt n (m - k + 2) u ω with hg1def
  have hg1 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ g1 u := by
    intro u hu
    refine Finset.sum_nonneg fun i _ => mul_nonneg (add_nonneg (pow_nonneg (inv_nonneg.2
      (mul_nonneg hS0.le (hηpos u hu.2).le)) _) (gueDproc_nonneg _ _ _ _ _ _ _ _ _ _ _))
      (gueDproc_nonneg _ _ _ _ _ _ _ _ _ _ _)
  have hηc : Continuous fun u => etaT (E n) u := by unfold etaT; fun_prop
  have hg1c : ContinuousOn g1 (Set.Icc (t1 n) (t0 n)) := by
    refine continuousOn_finsetSum _ fun i _ => ?_
    refine ContinuousOn.mul (ContinuousOn.add ?_ (gueDproc_continuousOn _ _ _ _ _ _ _ _ _ _))
      (gueDproc_continuousOn _ _ _ _ _ _ _ _ _ _)
    refine ContinuousOn.pow (ContinuousOn.inv₀ (continuous_const.mul hηc).continuousOn
      fun u hu => (mul_pos hS0 (hηpos u hu.2)).ne') _
  -- the bilinear drift, `Cf = 3 m² c S`
  have hF : ∀ j < σ, ∀ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
      ‖primRhsGUE d (sz.L n) (sz.W n) (loopL d (sz.L n) (sz.W n)
          (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω)) (zt (E n) (gridTime t1 t0 K n j))) (loopOf x.1 x.2) -
        primRhsGUE d (sz.L n) (sz.W n) (Kt n (gridTime t1 t0 K n j)) (loopOf x.1 x.2)‖ ≤
        (3 * (m : ℝ) ^ 2 * c * S) * g1 (gridTime t1 t0 K n j) := by
    intro j hj x
    have hjK : j ≤ K n := (le_of_lt hj).trans hσK
    have hmin : min j σ = j := min_eq_left hj.le
    have hDp : ∀ i, gueDproc sz E t1 t0 K δ Kt n i (gridTime t1 t0 K n j) ω =
        gueDmax sz E t1 t0 K Kt n i j ω := by
      intro i; rw [gueDproc_time sz E t1 t0 K δ Kt n i j ht10 hjK ω, ← hσdef, hmin]
    have hlen : (loopOf x.1 x.2).length = m := HypB_loopOf_length _ _
    have hb := HypB_bil (W := sz.W n)
      (loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω))
        (zt (E n) (gridTime t1 t0 K n j)))
      (Kt n (gridTime t1 t0 K n j)) (loopOf x.1 x.2) (HypB_loopOf_wf _ _)
      (fun i => gueDproc sz E t1 t0 K δ Kt n i (gridTime t1 t0 K n j) ω)
      (lam := (S * etaT (E n) (gridTime t1 t0 K n j))⁻¹) hc
      (inv_nonneg.2 (mul_nonneg hS0.le (hηpos _ (Hyp_time_le ht10 hK0 hjK)).le))
      (fun i => gueDproc_nonneg _ _ _ _ _ _ _ _ _ _ _)
      (fun J hJ _ _ => by rw [hDp]; exact HypB_le_Dmax sz E t1 t0 K Kt n j ω J hJ)
      (fun J hJ h2 hJn => by rw [hlen] at hJn; exact hKt j hjK J hJ h2 hJn)
    rw [hlen, HypB_size_cast] at hb
    refine hb.trans (le_of_eq ?_)
    rw [hg1def]
  have hCf0 : 0 ≤ 3 * (m : ℝ) ^ 2 * c * S := by positivity
  set Λ0 := (gueScale sz E n (t1 n))⁻¹ ^ m with hΛ0def
  set S1 := supOn g1 (t1 n) t with hS1def
  set S3 := supOn g3 (t1 n) t with hS3def
  set S4 := supOn g4 (t1 n) t with hS4def
  have hS1n : 0 ≤ S1 := supOn_nonneg fun u hu => hg1 u ⟨hu.1, hu.2.trans ht.2⟩
  have hS3n : 0 ≤ S3 := supOn_nonneg fun u hu => hg3 u ⟨hu.1, hu.2.trans ht.2⟩
  have hS4n : 0 ≤ S4 := supOn_nonneg fun u hu => hg4 u ⟨hu.1, hu.2.trans ht.2⟩
  have hlam : ∀ k ≤ K n, gridTime t1 t0 K n k ≤ t + gridStep t1 t0 K n →
      (fun u => (gueScale sz E n u)⁻¹ ^ m) (gridTime t1 t0 K n k) ≤
        2 ^ m * (fun u => (gueScale sz E n u)⁻¹ ^ m) t := by
    intro k hk hkt
    simp only
    have hmem := Hyp_time_mem (K := K) ht10 hK0 hk
    have him := mE_im_pos hE
    have hηk : etaT (E n) t ≤ 2 * etaT (E n) (gridTime t1 t0 K n k) := by
      unfold etaT
      have h1 : (gridTime t1 t0 K n k - t) * (mE (E n)).im ≤
          gridStep t1 t0 K n * (mE (E n)).im :=
        mul_le_mul_of_nonneg_right (by linarith) him.le
      have h2 : gridStep t1 t0 K n * (mE (E n)).im ≤ (1 - t0 n) * (mE (E n)).im :=
        mul_le_mul_of_nonneg_right hΔ him.le
      have h3 : (1 - t0 n) * (mE (E n)).im ≤
          (1 - gridTime t1 t0 K n k) * (mE (E n)).im :=
        mul_le_mul_of_nonneg_right (by linarith [hmem.2]) him.le
      nlinarith
    have hpk := HypB_scale_pos sz (E := E) hE ht0 hmem.2
    have hpt := HypB_scale_pos sz (E := E) hE ht0 ht.2
    have hinv : (gueScale sz E n (gridTime t1 t0 K n k))⁻¹ ≤ 2 * (gueScale sz E n t)⁻¹ := by
      rw [show (2 : ℝ) * (gueScale sz E n t)⁻¹ = 2 / gueScale sz E n t by ring, inv_eq_one_div,
        div_le_div_iff₀ hpk hpt]
      rw [hscale_eq, hscale_eq]
      nlinarith
    calc (gueScale sz E n (gridTime t1 t0 K n k))⁻¹ ^ m ≤ (2 * (gueScale sz E n t)⁻¹) ^ m :=
          pow_le_pow_left₀ (inv_nonneg.2 hpk.le) hinv m
      _ = 2 ^ m * (gueScale sz E n t)⁻¹ ^ m := by rw [mul_pow]
  have hint := Hyp_interp_bound (f := fun k => gueDmax sz E t1 t0 K Kt n m k ω) hσK hK0 ht10
    ht (fun u => (gueScale sz E n u)⁻¹ ^ m) (P := c * Λ0 + err) (Q := c)
    (A := 3 * (m : ℝ) ^ 2 * c * S * S1 + Ce * S3) (B := c * S4) (C := 2 ^ m) hc0
    (by positivity) (by positivity) hlam
    (fun k hk hkt => Hyp_grid sz E t1 t0 K δ Kt n m ω g1 g3 g4 ht10 hE ht1 ht0 hm hc0 hCf0 hCe0
      hg1 hg3 hg4 hg1c hg3c hg4c h0 hM hq hF heG hdisc ht hk hkt)
  have hLHS : gueDproc sz E t1 t0 K δ Kt n m t ω =
      gueInterp t1 t0 K n (fun k => gueDmax sz E t1 t0 K Kt n m (min k σ) ω) t := rfl
  rw [hLHS]
  refine hint.trans ?_
  set X2 := (gueScale sz E n t)⁻¹ ^ m with hX2def
  have hX2eq : (S * etaT (E n) t)⁻¹ ^ m = X2 := rfl
  rw [hX2eq]
  have hpt := HypB_scale_pos sz (E := E) hE ht0 ht.2
  have hX2n : 0 ≤ X2 := pow_nonneg (inv_nonneg.2 hpt.le) _
  have hΛ0le : Λ0 ≤ X2 := by
    have hp1 := HypB_scale_pos sz (E := E) hE ht0 ht10
    have hle : gueScale sz E n t ≤ gueScale sz E n (t1 n) := by
      rw [hscale_eq, hscale_eq]
      refine mul_le_mul_of_nonneg_left ?_ hS0.le
      unfold etaT
      have := mE_im_pos hE
      nlinarith [ht.1]
    exact pow_le_pow_left₀ (inv_nonneg.2 hp1.le) (inv_anti₀ hpt hle) m
  have herr' := herr t ht
  have htt : 0 ≤ t - t1 n := by linarith [ht.1]
  have hsq : 0 ≤ Real.sqrt (t - t1 n) := Real.sqrt_nonneg _
  have hn2 : (0 : ℝ) ≤ (m : ℝ) ^ 2 := by positivity
  have h2n : (0 : ℝ) ≤ 2 ^ m := by positivity
  have hX1 : 0 ≤ S * (t - t1 n) * S1 := by positivity
  have hX3 : 0 ≤ S * (t - t1 n) * S3 := by positivity
  have hX4 : 0 ≤ Real.sqrt (t - t1 n) * S4 := by positivity
  have e1 : c * Λ0 + err + c * (2 ^ m * X2) ≤ c * (2 + 2 ^ m) * X2 := by
    have := mul_le_mul_of_nonneg_left hΛ0le hc0
    have : err ≤ c * X2 := herr'.trans (le_mul_of_one_le_left hX2n hc)
    nlinarith
  have e2 : (3 * (m : ℝ) ^ 2 * c * S * S1 + Ce * S3) * (t - t1 n) ≤
      c * ((3 + 4 * A) * (m : ℝ) ^ 2) * (S * (t - t1 n) * S1 + S * (t - t1 n) * S3) := by
    have hCe' : Ce * S3 * (t - t1 n) ≤ 4 * A * (m : ℝ) ^ 2 * c * S * S3 * (t - t1 n) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCe hS3n) htt
    have ha : 0 ≤ c * (m : ℝ) ^ 2 * (S * (t - t1 n) * S1) := by positivity
    have hb : 0 ≤ c * (m : ℝ) ^ 2 * (S * (t - t1 n) * S3) := by positivity
    nlinarith
  have e3 : c * S4 * Real.sqrt (t - t1 n) ≤
      c * (2 + 2 ^ m + (3 + 4 * A) * (m : ℝ) ^ 2) * (Real.sqrt (t - t1 n) * S4) := by
    have hK1 : (1 : ℝ) ≤ 2 + 2 ^ m + (3 + 4 * A) * (m : ℝ) ^ 2 := by
      have h1 : 0 ≤ (3 + 4 * A) * (m : ℝ) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
      have h2 : (0 : ℝ) ≤ 2 ^ m := by positivity
      linarith
    have hX : 0 ≤ c * (Real.sqrt (t - t1 n) * S4) := by positivity
    have h := mul_le_mul_of_nonneg_left hK1 hX
    calc c * S4 * Real.sqrt (t - t1 n) = c * (Real.sqrt (t - t1 n) * S4) * 1 := by ring
      _ ≤ c * (Real.sqrt (t - t1 n) * S4) * (2 + 2 ^ m + (3 + 4 * A) * (m : ℝ) ^ 2) := h
      _ = c * (2 + 2 ^ m + (3 + 4 * A) * (m : ℝ) ^ 2) * (Real.sqrt (t - t1 n) * S4) := by ring
  have hfin : c * (2 + 2 ^ m + (3 + 4 * A) * (m : ℝ) ^ 2) *
      (S * (t - t1 n) * S1 + X2 + S * (t - t1 n) * S3 + Real.sqrt (t - t1 n) * S4) =
      c * (2 + 2 ^ m) * X2 + c * ((3 + 4 * A) * (m : ℝ) ^ 2) *
        (S * (t - t1 n) * S1 + S * (t - t1 n) * S3) +
      c * (2 + 2 ^ m + (3 + 4 * A) * (m : ℝ) ^ 2) * (Real.sqrt (t - t1 n) * S4) +
      (c * (2 + 2 ^ m) * (S * (t - t1 n) * S1 + S * (t - t1 n) * S3) +
        c * ((3 + 4 * A) * (m : ℝ) ^ 2) * X2) := by ring
  have hextra : 0 ≤ c * (2 + 2 ^ m) * (S * (t - t1 n) * S1 + S * (t - t1 n) * S3) +
      c * ((3 + 4 * A) * (m : ℝ) ^ 2) * X2 := by
    have hq : 0 ≤ (3 + 4 * A) * (m : ℝ) ^ 2 := mul_nonneg (by linarith) hn2
    have h1 : 0 ≤ S * (t - t1 n) * S1 + S * (t - t1 n) * S3 := add_nonneg hX1 hX3
    have h2 : (0 : ℝ) ≤ 2 + 2 ^ m := by positivity
    exact add_nonneg (mul_nonneg (mul_nonneg hc0 h2) h1) (mul_nonneg (mul_nonneg hc0 hq) hX2n)
  rw [hfin]
  linarith

end HypBPath


/-! ### The pathwise bound at a fixed size index with the exponent bookkeeping -/

section HypBFixed

/-- **One length, one size index, one sample point**: the eventual deterministic facts and the
good event at level `N^{τ/2}` give `D_m(t) ≤ N^τ · rhs(t)` for every `t ∈ [t₁, t₀]` (the bounds on
`K̃` and on the discretization error, the step-size conditions and the final absorption).
`N = sz.size n = (W L)^d`; since `1 ≤ sz.size n`, no hypotheses `1 ≤ N` or `W L ≤ N` are needed. -/
theorem HypB_fixed {τ : ℝ} (hτ : 0 < τ) (n0 : ℕ) {E t1 t0 : ℕ → ℝ} (τU : ℝ)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ)
    (hK : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : RBM.Loop.LoopIdx (Zd d (sz.L n)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t)
    (n m : ℕ) (ω : PathΩ sz) (g3 g4 : ℝ → ℝ) {Ce : ℝ}
    (hEb : |E n| < 2) (ht1 : 0 ≤ t1 n) (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1)
    (hm1 : 1 ≤ m) (hm : m ≤ 2 * n0)
    (hΔ : gridStep t1 t0 (gueGridK sz n0) n ≤ 1 - t0 n)
    (hgrid1 : ((2 * n0 : ℕ) : ℝ) ^ 3 * ((sz.size n : ℕ) : ℝ) * ((gueGridK sz n0 n : ℝ))⁻¹ ≤ 1)
    (hgrid2 : 3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * ((sz.size n : ℕ) : ℝ) ^ 2 * ((gueGridK sz n0 n : ℝ))⁻¹ ≤
      (((sz.size n : ℕ) : ℝ)⁻¹) ^ (2 * n0))
    (hbd : ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ J : RBM.Loop.LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length →
      J.length ≤ 2 * n0 → ‖Kt n t J‖ ≤ 1)
    (hKtc : ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ J : RBM.Loop.LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length →
      J.length ≤ 2 * n0 →
      ‖Kt n t J‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (gueScale sz E n t)⁻¹ ^ (J.length - 1))
    (hbig : 2 + 2 ^ (2 * n0) + (3 + 4 * (1 + 2 * sz.lam n ^ 2)) * ((2 * n0 : ℕ) : ℝ) ^ 2 ≤
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2))
    (hCe0 : 0 ≤ Ce)
    (hCe : Ce ≤ 4 * (1 + 2 * sz.lam n ^ 2) * (m : ℝ) ^ 2 * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
      ((sz.size n : ℕ) : ℝ))
    (hg3 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ g3 u) (hg4 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ g4 u)
    (hg3c : ContinuousOn g3 (Set.Icc (t1 n) (t0 n)))
    (hg4c : ContinuousOn g4 (Set.Icc (t1 n) (t0 n)))
    (h0 : ∀ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
      ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 (gueGridK sz n0) n 0 ω))
          (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n 0)) (loopOf x.1 x.2) -
        Kt n (gridTime t1 t0 (gueGridK sz n0) n 0) (loopOf x.1 x.2)‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (gueScale sz E n (t1 n))⁻¹ ^ m)
    (hM : ∀ k ≤ gueGridK sz n0 n, ∀ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
      ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 (gueGridK sz n0) n k ω))
            (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n k)) (loopOf x.1 x.2)
          - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 (gueGridK sz n0) n 0 ω))
            (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n 0)) (loopOf x.1 x.2)
          - (gridStep t1 t0 (gueGridK sz n0) n : ℂ) * ∑ j ∈ Finset.range k,
              genMatGUE d (sz.L n) (sz.W n) (E n) (gridTime t1 t0 (gueGridK sz n0) n j)
                (gueH sz t1 t0 (gueGridK sz n0) n j ω) (loopOf x.1 x.2)‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (Real.sqrt (gridTime t1 t0 (gueGridK sz n0) n k - t1 n) *
          (⨆ j : Fin k, Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ *
            (etaT (E n) (gridTime t1 t0 (gueGridK sz n0) n j))⁻¹ ^ 2 *
            RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 (gueGridK sz n0) n j ω))
              (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n j)) (2 * m)))
          + (gueScale sz E n (gridTime t1 t0 (gueGridK sz n0) n k))⁻¹ ^ m))
    (hq : ∀ j < gueStop sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) n ω,
      Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ *
        (etaT (E n) (gridTime t1 t0 (gueGridK sz n0) n j))⁻¹ ^ 2 *
        RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 (gueGridK sz n0) n j ω))
          (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n j)) (2 * m)) ≤
        g4 (gridTime t1 t0 (gueGridK sz n0) n j))
    (heG : ∀ j < gueStop sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) n ω,
      ∀ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
      ‖egtNGUE d (sz.L n) (sz.W n) (E n) (gridTime t1 t0 (gueGridK sz n0) n j)
          (gueH sz t1 t0 (gueGridK sz n0) n j ω) (loopOf x.1 x.2)‖ ≤
        Ce * g3 (gridTime t1 t0 (gueGridK sz n0) n j))
    {t : ℝ} (ht : t ∈ Set.Icc (t1 n) (t0 n)) :
    gueDproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) Kt n m t ω ≤
      ((sz.size n : ℕ) : ℝ) ^ τ *
      (((sz.size n : ℕ) : ℝ) * (t - t1 n) * supOn (fun u => ∑ k ∈ Finset.Icc 2 m,
          ((((sz.size n : ℕ) : ℝ) * etaT (E n) u)⁻¹ ^ (k - 1) +
            gueDproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) Kt n k u ω) *
            gueDproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) Kt n (m - k + 2) u ω)
          (t1 n) t
        + (((sz.size n : ℕ) : ℝ) * etaT (E n) t)⁻¹ ^ m
        + ((sz.size n : ℕ) : ℝ) * (t - t1 n) * supOn g3 (t1 n) t
        + Real.sqrt (t - t1 n) * supOn g4 (t1 n) t) := by
  have hNR : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := HypB_one_le_size sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set c := N ^ (τ / 2) with hcdef
  set A : ℝ := 1 + 2 * sz.lam n ^ 2 with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; nlinarith [sq_nonneg (sz.lam n)]
  have hc : 1 ≤ c := Real.one_le_rpow hNR (by positivity)
  have hK0 : gueGridK sz n0 n ≠ 0 := gueGridK_ne_zero sz n0 n
  have hKR : (1 : ℝ) ≤ (gueGridK sz n0 n : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hK0
  set Δ := gridStep t1 t0 (gueGridK sz n0) n with hΔdef
  have hΔ0 : 0 ≤ Δ := Hyp_step_nonneg ht10
  have hΔK : Δ ≤ ((gueGridK sz n0 n : ℝ))⁻¹ := by
    rw [hΔdef]; unfold gridStep
    rw [div_eq_mul_inv]
    have : t0 n - t1 n ≤ 1 := by linarith
    have hKi : 0 ≤ ((gueGridK sz n0 n : ℝ))⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
    have h0 : 0 ≤ t0 n - t1 n := by linarith
    calc (t0 n - t1 n) * ((gueGridK sz n0 n : ℝ))⁻¹ ≤ 1 * ((gueGridK sz n0 n : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_right this hKi
      _ = ((gueGridK sz n0 n : ℝ))⁻¹ := one_mul _
  -- the discretization condition `M³ N Δ ≤ 1`
  have hsmall : ((2 * n0 : ℕ) : ℝ) ^ 3 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) * Δ ≤ 1 := by
    rw [HypB_size_cast]
    calc ((2 * n0 : ℕ) : ℝ) ^ 3 * N * Δ
        ≤ ((2 * n0 : ℕ) : ℝ) ^ 3 * N * ((gueGridK sz n0 n : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_left hΔK (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hN0.le)
      _ ≤ 1 := hgrid1
  have hK' : ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : RBM.Loop.LoopIdx (Zd d (sz.L n)), I.WF →
      1 ≤ I.length → I.length ≤ 2 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t := fun t ht I hI h1 h2 => hK n t ht I hI h1 (by omega)
  set err := 3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * N ^ 2 * Δ * (t0 n - t1 n) with herrdef
  have hdisc : ∀ k ≤ gueGridK sz n0 n, ∀ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
      ‖Kt n (gridTime t1 t0 (gueGridK sz n0) n k) (loopOf x.1 x.2) -
          Kt n (gridTime t1 t0 (gueGridK sz n0) n 0) (loopOf x.1 x.2) -
        (Δ : ℂ) * ∑ j ∈ Finset.range k,
          primRhsGUE d (sz.L n) (sz.W n) (Kt n (gridTime t1 t0 (gueGridK sz n0) n j))
            (loopOf x.1 x.2)‖ ≤ err := fun k hk x => by
    have h := Hyp_Kt_disc sz Kt ht10 hK0 hK' hbd hsmall hk (loopOf x.1 x.2)
      (HypB_loopOf_wf _ _) (by rw [HypB_loopOf_length]; exact hm1)
      (by rw [HypB_loopOf_length]; exact hm)
    rw [HypB_size_cast] at h
    exact h
  have herr : ∀ t' ∈ Set.Icc (t1 n) (t0 n), err ≤ (gueScale sz E n t')⁻¹ ^ m := by
    intro t' ht'
    have hsc := HypB_scale_pos sz (E := E) hEb ht0 ht'.2
    have hsN : gueScale sz E n t' ≤ N := by
      unfold gueScale
      have hη1 : etaT (E n) t' ≤ 1 := by
        unfold etaT
        have hm1' : (mE (E n)).im ≤ 1 := by
          have h1 := Complex.abs_im_le_norm (mE (E n))
          rw [norm_mE hEb.le] at h1
          exact (abs_le.mp h1).2
        have hm0 := (mE_im_pos hEb).le
        have : 1 - t' ≤ 1 := by linarith [ht'.1]
        have : 0 ≤ 1 - t' := by linarith [ht'.2]
        nlinarith
      have hη0 : 0 ≤ etaT (E n) t' := by
        unfold etaT; have := (mE_im_pos hEb).le; nlinarith [ht'.2]
      nlinarith
    have hinv : N⁻¹ ≤ (gueScale sz E n t')⁻¹ := inv_anti₀ hsc hsN
    have hNi1 : N⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hNR
    have hNi0 : 0 ≤ N⁻¹ := inv_nonneg.2 hN0.le
    calc err ≤ 3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * N ^ 2 * ((gueGridK sz n0 n : ℝ))⁻¹ := by
          rw [herrdef]
          have h1 : t0 n - t1 n ≤ 1 := by linarith
          have h2 : 0 ≤ t0 n - t1 n := by linarith
          have h4 : Δ * (t0 n - t1 n) ≤ ((gueGridK sz n0 n : ℝ))⁻¹ := by
            calc Δ * (t0 n - t1 n) ≤ Δ * 1 := mul_le_mul_of_nonneg_left h1 hΔ0
              _ ≤ _ := by rw [mul_one]; exact hΔK
          have h5 : (0 : ℝ) ≤ 3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * N ^ 2 :=
            mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg _) _))
              (sq_nonneg _)
          calc 3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * N ^ 2 * Δ * (t0 n - t1 n)
              = 3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * N ^ 2 * (Δ * (t0 n - t1 n)) := by ring
            _ ≤ 3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * N ^ 2 * ((gueGridK sz n0 n : ℝ))⁻¹ :=
                mul_le_mul_of_nonneg_left h4 h5
      _ ≤ (N⁻¹) ^ (2 * n0) := hgrid2
      _ ≤ (N⁻¹) ^ m := pow_le_pow_of_le_one hNi0 hNi1 hm
      _ ≤ (gueScale sz E n t')⁻¹ ^ m := pow_le_pow_left₀ hNi0 hinv m
  -- the bound on `K̃` on the grid
  have hKt : ∀ j ≤ gueGridK sz n0 n, ∀ J : RBM.Loop.LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length →
      J.length ≤ m → ‖Kt n (gridTime t1 t0 (gueGridK sz n0) n j) J‖ ≤
        c * (gueScale sz E n (gridTime t1 t0 (gueGridK sz n0) n j))⁻¹ ^ (J.length - 1) :=
    fun j hj J hJ h2 hJn => hKtc _ (Hyp_time_mem ht10 hK0 hj) J hJ h2 (hJn.trans hm)
  have hn2 : (m : ℝ) ^ 2 ≤ ((2 * n0 : ℕ) : ℝ) ^ 2 := by
    have : (m : ℝ) ≤ ((2 * n0 : ℕ) : ℝ) := by exact_mod_cast hm
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
  have hpath := HypB_path sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) Kt n m ω g3 g4 (c := c)
    (Ce := Ce) (err := err) (A := A) hEb ht1 ht10 ht0 hK0 hm1 hc hA0 hCe0 hCe hΔ herr hg3 hg4 hg3c hg4c h0 hM hq
    hKt heG hdisc ht
  set R := N * (t - t1 n) * supOn (fun u => ∑ k ∈ Finset.Icc 2 m,
          ((N * etaT (E n) u)⁻¹ ^ (k - 1) +
            gueDproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) Kt n k u ω) *
            gueDproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) Kt n (m - k + 2) u ω)
          (t1 n) t
        + (N * etaT (E n) t)⁻¹ ^ m
        + N * (t - t1 n) * supOn g3 (t1 n) t
        + Real.sqrt (t - t1 n) * supOn g4 (t1 n) t with hRdef
  have hK0' : (0 : ℝ) < 2 + 2 ^ m + (3 + 4 * A) * (m : ℝ) ^ 2 := by
    have h1 : 0 ≤ (3 + 4 * A) * (m : ℝ) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have h2 : (0 : ℝ) < 2 ^ m := by positivity
    linarith
  have hDp0 := gueDproc_nonneg sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) Kt n m t ω
  have hcpos : 0 < c := by linarith
  have hR0 : 0 ≤ R := by
    by_contra hneg
    push Not at hneg
    have : c * (2 + 2 ^ m + (3 + 4 * A) * (m : ℝ) ^ 2) * R < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hcpos hK0') hneg
    linarith
  have hKn : 2 + 2 ^ m + (3 + 4 * A) * (m : ℝ) ^ 2 ≤ c := by
    have h2 : (2 : ℝ) ^ m ≤ 2 ^ (2 * n0) := pow_le_pow_right₀ (by norm_num) hm
    have h3 : (3 + 4 * A) * (m : ℝ) ^ 2 ≤ (3 + 4 * A) * ((2 * n0 : ℕ) : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hn2 (by linarith)
    rw [hcdef]
    linarith
  have hNτ : N ^ τ = c * c := by
    rw [hcdef, ← Real.rpow_add hN0]; ring_nf
  calc gueDproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) Kt n m t ω
      ≤ c * (2 + 2 ^ m + (3 + 4 * A) * (m : ℝ) ^ 2) * R := hpath
    _ ≤ c * c * R :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKn (by linarith)) hR0
    _ = N ^ τ * R := by rw [hNτ]

end HypBFixed


/-! ### Two more eventual facts at a fixed size index, the grid values and a continuity fact -/

section HypBFacts

/-- Step-size input: `Δ ≤ t₀ − t₁ ≤ N^{-τU} η_{t₀} ≤ 1 − t₀`. -/
theorem HypB_step_le {E t1 t0 : ℕ → ℝ} {τU : ℝ} (n0 n : ℕ) (hEb : |E n| < 2)
    (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1)
    (h730 : t0 n - t1 n ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) (t0 n)) (hτU : 0 < τU) :
    gridStep t1 t0 (gueGridK sz n0) n ≤ 1 - t0 n := by
  have hNR : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := HypB_one_le_size sz n
  have hKR : (1 : ℝ) ≤ (gueGridK sz n0 n : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (gueGridK_ne_zero sz n0 n)
  have hm1 : (mE (E n)).im ≤ 1 := by
    have h1 := Complex.abs_im_le_norm (mE (E n))
    rw [norm_mE hEb.le] at h1
    exact (abs_le.mp h1).2
  have hm0 := (mE_im_pos hEb).le
  have hη0 : 0 ≤ etaT (E n) (t0 n) := by unfold etaT; nlinarith
  have hη1 : etaT (E n) (t0 n) ≤ 1 - t0 n := by unfold etaT; nlinarith
  have hNp : ((sz.size n : ℕ) : ℝ) ^ (-τU) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hNR (by linarith)
  have hstep : gridStep t1 t0 (gueGridK sz n0) n ≤ t0 n - t1 n := by
    unfold gridStep
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  calc gridStep t1 t0 (gueGridK sz n0) n ≤ t0 n - t1 n := hstep
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) (t0 n) := h730
    _ ≤ 1 * etaT (E n) (t0 n) := mul_le_mul_of_nonneg_right hNp hη0
    _ ≤ 1 - t0 n := by rw [one_mul]; exact hη1

/-- `‖K̃_t(J)‖ ≤ 1` on `[t₁, t₀]` for `2 ≤ |J| ≤ 2n₀`, from the bound (7.36) at `τU/2` and
`(N η_t)^{-1} ≤ N^{-τU}`. -/
theorem HypB_Kt_le_one {E t1 t0 : ℕ → ℝ} {τU : ℝ} (hτU : 0 < τU) (n0 n : ℕ)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (hEb : |E n| < 2) (ht0 : t0 n < 1)
    (hK1 : ∀ p : TimeIcc t1 t0 n × LoopSet d (sz.L n) (2 * n0), ‖Kt n p.1 p.2.1‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ (τU / 2) * (gueScale sz E n p.1)⁻¹ ^ ((p.2.1).length - 1))
    (hscale : (gueScale sz E n (t0 n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU)) :
    ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ J : RBM.Loop.LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length →
      J.length ≤ 2 * n0 → ‖Kt n t J‖ ≤ 1 := by
  intro t ht J hJ h2 hJn
  have hNR : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := HypB_one_le_size sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have h := hK1 (⟨t, ht⟩, ⟨J, hJ, h2, hJn⟩)
  simp only at h
  have hst := HypB_scale_pos sz (E := E) hEb ht0 ht.2
  have hs0 := HypB_scale_pos sz (E := E) hEb ht0 (le_refl (t0 n))
  have hle : gueScale sz E n (t0 n) ≤ gueScale sz E n t := by
    unfold gueScale
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    unfold etaT
    have := (mE_im_pos hEb).le
    nlinarith [ht.2]
  have hinv : (gueScale sz E n t)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) :=
    (inv_anti₀ hs0 hle).trans hscale
  have hNp1 : ((sz.size n : ℕ) : ℝ) ^ (-τU) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hNR (by linarith)
  have hNp0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) := Real.rpow_nonneg hN0.le _
  have hpow : (gueScale sz E n t)⁻¹ ^ (J.length - 1) ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) := by
    calc (gueScale sz E n t)⁻¹ ^ (J.length - 1) ≤ (((sz.size n : ℕ) : ℝ) ^ (-τU)) ^ (J.length - 1) :=
          pow_le_pow_left₀ (inv_nonneg.2 hst.le) hinv _
      _ ≤ (((sz.size n : ℕ) : ℝ) ^ (-τU)) ^ 1 := pow_le_pow_of_le_one hNp0 hNp1 (by omega)
      _ = ((sz.size n : ℕ) : ℝ) ^ (-τU) := pow_one _
  have hcomb : ((sz.size n : ℕ) : ℝ) ^ (τU / 2) * ((sz.size n : ℕ) : ℝ) ^ (-τU) ≤ 1 := by
    rw [← Real.rpow_add hN0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hNR (by linarith)
  calc ‖Kt n t J‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (τU / 2) * (gueScale sz E n t)⁻¹ ^ (J.length - 1) := h
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τU / 2) * ((sz.size n : ℕ) : ℝ) ^ (-τU) :=
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hN0.le _)
    _ ≤ 1 := hcomb

/-- Grid values of the stopped process `L^{(m)}` before the stopping index. -/
theorem HypB_Lproc_grid (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (n m j : ℕ)
    (ω : PathΩ sz) (ht10 : t1 n ≤ t0 n) (hj : j < gueStop sz E t1 t0 K δ n ω) :
    gueLproc sz E t1 t0 K δ n m (gridTime t1 t0 K n j) ω =
      RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω))
        (zt (E n) (gridTime t1 t0 K n j)) m := by
  have hσK : gueStop sz E t1 t0 K δ n ω ≤ K n := firstHit_le _ _ _ ω
  rw [gueLproc_time sz E t1 t0 K δ n m j ht10 (by omega) ω, min_eq_left hj.le]
  rfl

/-- Grid values of the stopped process `D^{(m)}` before the stopping index. -/
theorem HypB_Dproc_grid (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (n m j : ℕ)
    (ω : PathΩ sz) (ht10 : t1 n ≤ t0 n) (hj : j < gueStop sz E t1 t0 K δ n ω) :
    gueDproc sz E t1 t0 K δ Kt n m (gridTime t1 t0 K n j) ω = gueDmax sz E t1 t0 K Kt n m j ω := by
  have hσK : gueStop sz E t1 t0 K δ n ω ≤ K n := firstHit_le _ _ _ ω
  rw [gueDproc_time sz E t1 t0 K δ Kt n m j ht10 (by omega) ω, min_eq_left hj.le]

/-- Continuity of `u ↦ √(N⁻¹ η_u⁻²)` on `[t₁, t₀]`. -/
theorem HypB_sqrt_cont {E t1 t0 : ℕ → ℝ} (n : ℕ) (hEb : |E n| < 2) (ht0 : t0 n < 1) :
    ContinuousOn (fun u => Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ * (etaT (E n) u)⁻¹ ^ 2))
      (Set.Icc (t1 n) (t0 n)) := by
  have hηc : Continuous fun u => etaT (E n) u := by unfold etaT; fun_prop
  have hη : ∀ u ∈ Set.Icc (t1 n) (t0 n), etaT (E n) u ≠ 0 := fun u hu =>
    (etaT_pos hEb (by linarith [hu.2])).ne'
  exact Real.continuous_sqrt.comp_continuousOn
    (continuousOn_const.mul ((hηc.continuousOn.inv₀ hη).pow 2))

end HypBFacts



end RBM.Univ.GUEPhase


end
