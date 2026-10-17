/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Path.Walk
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.Stopping

/-!
# Grid stopping times and their stopping-time properties

Ticket T2021 (MD-5).  Port of RBM2D `RBM2D/Path/Stop.lean` at `c9a24cf` (itself a port of RBM1D
`Gauss/GridStop.lean` and `Gauss/GridStopFilt.lean`, commit `86573b9`), with the renamings
`d : Sizes` → `sz : Sizes d`, `Idx (d.L n) (d.W n)` → `Idx d (sz.L n) (sz.W n)`.

The first block is generic (filtration-agnostic): `firstHit J θ K` is the first grid index
`j ≤ K` at which the adapted real process `J` reaches `θ` (else `K`), built on Mathlib's
`MeasureTheory.hittingBtwn`.  The second block specialises it to the coordinate filtration
`RBM.Path.filt sz` of the grid walk `pathH` (T2035), for processes `j ↦ F j (pathH … j ω)` with
every `F j` Borel on matrices.

Port map (RBM1D line numbers at `86573b9`): `GridStop.lean` declarations are ported with the
same names; `H_measurable_filt` (`GridStopFilt.lean:36`) → `pathH_measurable_filt`;
`adapted_of_measurable_H` (`:44`) → `adapted_of_measurable_pathH`; the four `*_grid` names are
unchanged.  Carrier replacements: `Ωg d` → `PathΩ sz`, `H` → `pathH`, `d.Idx N` →
`Idx d (sz.L n) (sz.W n)`, `Dims` → `Sizes`, and the size index `N` is renamed `n`.
-/

noncomputable section

namespace RBM.Path

open MeasureTheory RBM RBM.Gauss

section Generic

variable {Ω' : Type*} {m : MeasurableSpace Ω'}

/-- (T1) The first grid index `j ≤ K` at which `J j ω` reaches the threshold `θ`
(i.e. lands in `Set.Ici θ`), or `K` if it never does before the grid horizon. -/
noncomputable def firstHit (J : ℕ → Ω' → ℝ) (θ : ℝ) (K : ℕ) : Ω' → ℕ :=
  fun ω => MeasureTheory.hittingBtwn J (Set.Ici θ) 0 K ω

section OneProcess

variable {ℱ : Filtration ℕ m}

/-- (T2, part 1) `firstHit` is a stopping time for the filtration `ℱ`, provided the
underlying process `J` is `ℱ`-adapted. -/
theorem isStoppingTime_firstHit (J : ℕ → Ω' → ℝ) (θ : ℝ) (K : ℕ) (hJ : Adapted ℱ J) :
    IsStoppingTime ℱ (fun ω => (firstHit J θ K ω : ℕ)) :=
  hJ.isStoppingTime_hittingBtwn measurableSet_Ici

/-- (T2, part 2) `firstHit` never exceeds the grid horizon `K`. -/
theorem firstHit_le (J : ℕ → Ω' → ℝ) (θ : ℝ) (K : ℕ) (ω : Ω') :
    firstHit J θ K ω ≤ K :=
  MeasureTheory.hittingBtwn_le ω

/-- (T3, part 1) The event that the grid has not stopped by time `j` is
`ℱ j`-measurable. -/
theorem lt_firstHit_measurableSet (J : ℕ → Ω' → ℝ) (θ : ℝ) (K : ℕ) (hJ : Adapted ℱ J)
    (j : ℕ) : MeasurableSet[ℱ j] {ω | j < firstHit J θ K ω} := by
  have hτ := isStoppingTime_firstHit (ℱ := ℱ) J θ K hJ
  have hmeas : MeasurableSet[ℱ j] {ω : Ω' | firstHit J θ K ω ≤ j} := by
    have h' := hτ.measurableSet_le j
    simpa using h'
  have hset : {ω : Ω' | j < firstHit J θ K ω} = {ω : Ω' | firstHit J θ K ω ≤ j}ᶜ := by
    ext ω; simp [not_le]
  rw [hset]
  exact hmeas.compl

/-- (T3, part 2) Strictly before the grid stops, the process is strictly below the
threshold. -/
theorem lt_firstHit_imp (J : ℕ → Ω' → ℝ) (θ : ℝ) (K : ℕ) {j : ℕ} {ω : Ω'}
    (h : j < firstHit J θ K ω) : J j ω < θ := by
  have hnotmem : J j ω ∉ Set.Ici θ :=
    MeasureTheory.notMem_of_lt_hittingBtwn (u := J) (s := Set.Ici θ) (n := 0) h
      (Nat.zero_le j)
  simpa [Set.mem_Ici, not_le] using hnotmem

end OneProcess

/-- (T5) Per-`ω` identity turning a sum stopped at `τ` into a sum over the full
grid range with the stopped-indicator inserted, used to put stopped sums in Azuma
form. Purely combinatorial: no measurability or stopping-time hypothesis needed. -/
theorem sum_stopped {M : Type*} [AddCommMonoid M] (Y : ℕ → Ω' → M) (τ : Ω' → ℕ)
    (k : ℕ) (ω : Ω') :
    ∑ j ∈ Finset.range (min k (τ ω)), Y (j + 1) ω
      = ∑ j ∈ Finset.range k, ({ω' | j < τ ω'}.indicator (Y (j + 1))) ω := by
  have hfilter : (Finset.range k).filter (fun j => j < τ ω) = Finset.range (min k (τ ω)) := by
    ext j
    simp [Finset.mem_filter, Finset.mem_range, lt_min_iff]
  rw [← hfilter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j < τ ω <;> simp [hj]

end Generic

section Grid

variable {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

/-! ### The matrix-level measurability lemma

`pathH_adapted` (`Walk.lean`) only gives entrywise `StronglyMeasurable[filt sz k]` of the grid
walk `pathH`.  `Matrix i j ℂ` unfolds to the nested Pi type `i → j → ℂ`, and Mathlib's
`Matrix.measurable_iff` is stated for an arbitrary source `MeasurableSpace`, so it applies to the
relative measurable space `filt sz k`.  This assembles the entrywise statement into the
matrix-level one. -/
theorem pathH_measurable_filt (k : ℕ) :
    Measurable[filt sz k] (fun ω : PathΩ sz => pathH sz s t K n k ω) :=
  (@Matrix.measurable_iff (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ _ (PathΩ sz) (filt sz k)
      (fun ω => pathH sz s t K n k ω)).mpr
    (fun i j => stronglyMeasurable_iff_measurable.mp (pathH_adapted sz s t K n k i j))

/-- A "loop-observable" process built from a family `F` of measurable functions of the grid
matrix `pathH` is adapted to the coordinate filtration. -/
theorem adapted_of_measurable_pathH
    {F : ℕ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℝ}
    (hF : ∀ j, Measurable (F j)) :
    Adapted (filt sz) (fun j (ω : PathΩ sz) => F j (pathH sz s t K n j ω)) :=
  fun j => (hF j).comp (pathH_measurable_filt sz s t K n j)

/-- (T2) The event that a grid-observable process has not yet stopped by time `j` is
`filt sz j`-measurable. -/
theorem lt_firstHit_grid_measurableSet
    {F : ℕ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℝ}
    (hF : ∀ j, Measurable (F j)) (θ : ℝ) (K' : ℕ) (j : ℕ) :
    MeasurableSet[filt sz j]
      {ω | j < firstHit (fun j (ω : PathΩ sz) => F j (pathH sz s t K n j ω)) θ K' ω} :=
  lt_firstHit_measurableSet (ℱ := filt sz) (fun j (ω : PathΩ sz) => F j (pathH sz s t K n j ω)) θ K'
    (adapted_of_measurable_pathH sz s t K n hF) j

/-! ### Compiled nonempty instance at the preflight sequence `sz0`

`d = 3`, `L_0 = 4`, `W_0 = 32`; grid `s = 1/10`, `t = 1`, `K = 4`, `n = 0`.  The process is
`F j M = ‖M 0 0‖` (Borel in the matrix), the threshold is `θ = 1/2`, the horizon `K' = 4`. -/

end Grid

end RBM.Path

end
