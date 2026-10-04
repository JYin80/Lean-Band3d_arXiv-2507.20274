/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Path.Expansion
import RBM3D.Path.Azuma
import RBM3D.Path.Kernel
import RBM3D.Path.Stop
import RBM3D.Path.UBounds
import RBM3D.Path.StepDecompLoop

/-!
# Tail bounds for the stopped Duhamel martingale (`d ≥ 3`)

Ticket T2104 (ST2-27, first file).  Port of `RBM2D/Path/DuhamelTail.lean` at commit `c9a24cf`
(cited `DuhamelTail:<line>`; RBM2D ticket T2101), itself a port of RBM1D
`RBM1D/Gauss/GridDuhamelTail.lean` at `86573b9`.  Paper: arXiv:2507.20274, `alu9_STime`
(`3_5`), `int_K-L_ST`, `def_Ustz`, with the Burkholder-Davis-Gundy inequality replaced by
Azuma-Hoeffding (DECISIONS §10).

Renaming (`docs/tickets/ST1-COMMON.md` item 2): `d : Sizes` becomes `sz : Sizes d`, `Z2 L`
becomes `Zd d L`, the merged `Uop d L g ξ` (coupling `g`, `g = sz.lam n` for the model) replaces
RBM2D's `Uop L ξ`.  The only exponent that changes is the number of labels: `L ^ 4` becomes
`L ^ (2 * d)` (two slots in `Zd d L`; `Fintype.card (Zd d L × Zd d L) = (L ^ d) ^ 2`).  The
back-kernel constant `4` is dimension-free (merged `uopBack`).

* `stoppedEdge`, `stoppedEdge_apply`;
* `stopped_duhamel_azuma_tail_fixed`, `stopped_duhamel_azuma_union`, `stopped_duhamel_cheb_tail`,
  `stopped_duhamel_det_bound` (generic, in `Uop d L g ξ`);
* the pin `StoppedAzuma108`, the theorem `stoppedAzuma108` and its single-index form
  `stoppedAzuma108_at` (hypotheses only at the size index `n`, DECISIONS §29 (4)).

Every unpinned helper is `private` and carries the prefix `DuhamelTail_`.  Measurability of the
martingale differences along the walk needs no `HermTestFun`/`GoodEvent` (RBM2D
`GoodEvent_measurable_gloop`): `walk_measurable_loopFine` composed with `pathH_measurable_filt`.
-/

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

/-! ### 1. Generic algebra of the kernel `Uop` -/

section Setup

/-- Prepend a dummy zero term to a family `f : ℕ → M`
(RBM1D `prependZero`, `GridDuhamelTail.lean:54`). -/
private def DuhamelTail_prependZero {M : Type*} [Zero M] (f : ℕ → M) : ℕ → M
  | 0 => 0
  | j + 1 => f j

private theorem DuhamelTail_prependZero_succ {M : Type*} [Zero M] (f : ℕ → M) (j : ℕ) :
    DuhamelTail_prependZero f (j + 1) = f j := rfl

private theorem DuhamelTail_sum_range_succ_prependZero {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (K : ℕ) :
    ∑ i ∈ Finset.range (K + 1), DuhamelTail_prependZero f i = ∑ j ∈ Finset.range K, f j := by
  rw [Finset.sum_range_succ' (DuhamelTail_prependZero f) K]
  simp [DuhamelTail_prependZero]

/-- A finite sum of `MemLp _ 2 μ` real-valued functions is `MemLp _ 2 μ`
(RBM1D `memLp_finset_sum`, `GridDuhamelTail.lean:70`). -/
private theorem DuhamelTail_memLp_finset_sum {α : Type*} {m : MeasurableSpace α}
    {μ : Measure α} [IsFiniteMeasure μ] {ι : Type*} {s : Finset ι} (f : ι → α → ℝ)
    (hf : ∀ i ∈ s, MemLp (f i) 2 μ) : MemLp (fun x => ∑ i ∈ s, f i x) 2 μ := by
  have h := Finset.sum_induction f (fun g : α → ℝ => MemLp g 2 μ)
    (fun _ _ ha hb => ha.add hb) (memLp_const (0 : ℝ)) hf
  have heq : (∑ x ∈ s, f x) = fun x => ∑ i ∈ s, f i x := by
    funext x; rw [Finset.sum_apply]
  rwa [← heq]

/-- `‖(r : ℂ) * ζ‖ < 1` once `0 ≤ r ≤ t < 1` and `‖ζ‖ ≤ 1`
(RBM1D `norm_real_mul_lt_one`, `GridDuhamelTail.lean:80`). -/
private theorem DuhamelTail_norm_real_mul_lt_one {r t' : ℝ} (hr0 : 0 ≤ r) (hrt : r ≤ t')
    (ht1 : t' < 1) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1) : ‖(r : ℂ) * ζ‖ < 1 := by
  have heq : ‖(r : ℂ) * ζ‖ = r * ‖ζ‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0]
  rw [heq]
  calc r * ‖ζ‖ ≤ r * 1 := mul_le_mul_of_nonneg_left hζ hr0
    _ = r := mul_one r
    _ ≤ t' := hrt
    _ < 1 := ht1

/-- The backward factorisation: for any real `s` and `0 ≤ r ≤ t < 1`,
`𝒰_{s,r} = 𝒰_{t,r} ∘ 𝒰_{s,t}` (from `Uop_comp`; RBM1D `back_factor_apply`,
`GridDuhamelTail.lean:93`). -/
private theorem DuhamelTail_back_factor_apply (d L : ℕ) [NeZero L] (g : ℝ) (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ ≤ 1) {s t r : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hr0 : 0 ≤ r) (hrt : r ≤ t)
    (A : Zd d L × Zd d L → ℂ) :
    Uop d L g ξ s r A = Uop d L g ξ t r (Uop d L g ξ s t A) := by
  have ht' : ‖(t : ℂ) * ξ‖ < 1 := DuhamelTail_norm_real_mul_lt_one ht0 le_rfl ht1 hξ
  have hr' : ‖(r : ℂ) * ξ‖ < 1 := DuhamelTail_norm_real_mul_lt_one hr0 hrt ht1 hξ
  exact (Uop_comp d L g hL ht' hr' A).symm

/-- The backward factorisation applied to a finite sum: for `0 ≤ u 0 ≤ u 1 ≤ …`, `u K = t < 1`,
`k ≤ K` and any family `F`,
`Σ_{j<k} 𝒰_{u_{j+1},u_k} (F j) = 𝒰_{t,u_k} (Σ_{j<k} 𝒰_{u_{j+1},t} (F j))`
(RBM1D `back_factor_sum_apply`, `GridDuhamelTail.lean:104`). -/
private theorem DuhamelTail_back_factor_sum_apply (d L : ℕ) [NeZero L] (g : ℝ) (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ ≤ 1) {u : ℕ → ℝ} {t : ℝ} (hu0 : 0 ≤ u 0) (hu_succ : ∀ j, u j ≤ u (j + 1))
    {K : ℕ} (hut : u K = t) (ht1 : t < 1) {k : ℕ} (hkK : k ≤ K)
    (F : ℕ → Zd d L × Zd d L → ℂ) (a : Zd d L × Zd d L) :
    (∑ j ∈ Finset.range k, Uop d L g ξ (u (j + 1)) (u k) (F j)) a
      = Uop d L g ξ t (u k) (∑ j ∈ Finset.range k, Uop d L g ξ (u (j + 1)) t (F j)) a := by
  have hmono : Monotone u := monotone_nat_of_le_succ hu_succ
  have h0m : ∀ m, 0 ≤ u m := fun m => hu0.trans (hmono (Nat.zero_le m))
  have h0t : 0 ≤ t := hut ▸ h0m K
  have hle_t : ∀ m, m ≤ K → u m ≤ t := fun m hm => hut ▸ hmono hm
  have hstep : ∀ j < k, Uop d L g ξ (u (j + 1)) (u k) (F j)
      = Uop d L g ξ t (u k) (Uop d L g ξ (u (j + 1)) t (F j)) :=
    fun j _ => DuhamelTail_back_factor_apply d L g hL hξ h0t ht1 (h0m k) (hle_t k hkK) (F j)
  have hsum_eq : (∑ j ∈ Finset.range k, Uop d L g ξ (u (j + 1)) (u k) (F j))
      = Uop d L g ξ t (u k) (∑ j ∈ Finset.range k, Uop d L g ξ (u (j + 1)) t (F j)) := by
    calc (∑ j ∈ Finset.range k, Uop d L g ξ (u (j + 1)) (u k) (F j))
        = ∑ j ∈ Finset.range k, Uop d L g ξ t (u k) (Uop d L g ξ (u (j + 1)) t (F j)) :=
          Finset.sum_congr rfl (fun j hj => hstep j (Finset.mem_range.mp hj))
      _ = ∑ j ∈ Finset.range k, UopHom d L g ξ t (u k) (Uop d L g ξ (u (j + 1)) t (F j)) := by
          simp [UopHom_apply]
      _ = UopHom d L g ξ t (u k) (∑ j ∈ Finset.range k, Uop d L g ξ (u (j + 1)) t (F j)) :=
          (map_sum (UopHom d L g ξ t (u k)) _ _).symm
      _ = Uop d L g ξ t (u k) (∑ j ∈ Finset.range k, Uop d L g ξ (u (j + 1)) t (F j)) := by
          rw [UopHom_apply]
  exact congrFun hsum_eq a

/-- Given the back-kernel bound `‖𝒰_{t,r} V a‖ ≤ 4 ‖V‖_max` (merged `uopBack`) and a label `a`
where the threshold `4 x` is met, some label `b` meets the threshold `x` for `V`
(RBM1D `exists_label_of_back_bound`, `GridDuhamelTail.lean:137`, constant `2 ^ n` → `4`). -/
private theorem DuhamelTail_exists_label_of_back_bound (d L : ℕ) [NeZero L] (g : ℝ) (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ ≤ 1) {t r : ℝ} (hr0 : 0 ≤ r) (hrt : r ≤ t) (ht1 : t < 1)
    (V : Zd d L × Zd d L → ℂ) {x : ℝ} {a : Zd d L × Zd d L}
    (ha : 4 * x ≤ ‖Uop d L g ξ t r V a‖) :
    ∃ b, x ≤ ‖V b‖ := by
  have : Nonempty (Zd d L × Zd d L) := ⟨(0, 0)⟩
  have hA : ∀ b, ‖V b‖ ≤ Finset.univ.sup' Finset.univ_nonempty (fun b => ‖V b‖) :=
    fun b => Finset.le_sup' (fun b => ‖V b‖) (Finset.mem_univ b)
  have hbound : ‖Uop d L g ξ t r V a‖
      ≤ 4 * Finset.univ.sup' Finset.univ_nonempty (fun b => ‖V b‖) :=
    uopBack d g L hL ξ hξ r t hr0 hrt ht1 V _ hA a
  have hxM : x ≤ Finset.univ.sup' Finset.univ_nonempty (fun b => ‖V b‖) := by
    linarith [ha, hbound]
  obtain ⟨b, -, hb⟩ := (Finset.le_sup'_iff (H := Finset.univ_nonempty)).mp hxM
  exact ⟨b, hb⟩

/-- The number of labels is `L ^ (2 * d)` (RBM1D `card_loopArg_eq`, `GridDuhamelTail.lean:156`,
which counts `L ^ n` labels; here two slots of one index in `Zd d L` each; RBM2D: `L ^ 4`). -/
private theorem DuhamelTail_card_label (d L : ℕ) [NeZero L] :
    Fintype.card (Zd d L × Zd d L) = L ^ (2 * d) := by
  rw [Fintype.card_prod, card_Zd]
  ring

end Setup

/-! ### 2. The stopped edge -/

section StoppedEdge

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {ℱ : Filtration ℕ mΩ'}

/-- The stopped, evaluated-at-one-label kernel image of an increment,
`{j < τ}.indicator (fun ω' => (𝒰_{u_{j+1},t'} Z_{j+1} ω') b)`, with target time `t'`
(`t' = u k` for the fixed-target tails, `t' = t = u K` for the Chebyshev tail).  Port of RBM1D
`stoppedEdge` (`GridDuhamelTail.lean:169`) with `Uker L ξ` replaced by `Uop d L g ξ` and real times. -/
noncomputable def stoppedEdge (d L : ℕ) [NeZero L] (g : ℝ) (ξ : ℂ) (u : ℕ → ℝ)
    (t' : ℝ) (τ : Ω' → ℕ) (Z : ℕ → Ω' → Zd d L × Zd d L → ℂ) (b : Zd d L × Zd d L) (j : ℕ) :
    Ω' → ℂ :=
  {ω' | j < τ ω'}.indicator (fun ω' => Uop d L g ξ (u (j + 1)) t' (Z (j + 1) ω') b)

/-- Unfolding lemma for `stoppedEdge` (RBM1D `stoppedEdge_apply`, `GridDuhamelTail.lean:174`). -/
theorem stoppedEdge_apply (d L : ℕ) [NeZero L] (g : ℝ) (ξ : ℂ) (u : ℕ → ℝ) (t' : ℝ)
    (τ : Ω' → ℕ) (Z : ℕ → Ω' → Zd d L × Zd d L → ℂ) (b : Zd d L × Zd d L) (j : ℕ) (ω : Ω') :
    stoppedEdge d L g ξ u t' τ Z b j ω =
      {ω' | j < τ ω'}.indicator
        (fun ω' => Uop d L g ξ (u (j + 1)) t' (Z (j + 1) ω') b) ω := rfl

/-- `A ↦ (𝒰_{s,t} A) b` is continuous, so it preserves strong measurability
(RBM1D `stronglyMeasurable_Uker_apply`, `GridDuhamelTail.lean:181`). -/
private theorem DuhamelTail_stronglyMeasurable_Uop_apply (d L : ℕ) [NeZero L] (g : ℝ) (ξ : ℂ) (s t : ℝ)
    {i : ℕ} {W : Ω' → Zd d L × Zd d L → ℂ} (hW : StronglyMeasurable[ℱ i] W) (b : Zd d L × Zd d L) :
    StronglyMeasurable[ℱ i] (fun ω => Uop d L g ξ s t (W ω) b) := by
  have hcont : Continuous (fun A : Zd d L × Zd d L → ℂ => Uop d L g ξ s t A b) := by
    have heq : (fun A : Zd d L × Zd d L → ℂ => Uop d L g ξ s t A b)
        = fun A => ∑ c : Zd d L × Zd d L,
            (ukerMat d L g ξ s t b.1 c.1 * ukerMat d L g ξ s t b.2 c.2) * A c := by
      funext A; rfl
    rw [heq]
    exact continuous_finsetSum _ (fun c _ => continuous_const.mul (continuous_apply c))
  exact hcont.comp_stronglyMeasurable hW

/-- `stoppedEdge` is `ℱ (j+1)`-strongly measurable once `Z (j+1)` is
(RBM1D `stronglyMeasurable_stoppedEdge`, `GridDuhamelTail.lean:193`). -/
private theorem DuhamelTail_stronglyMeasurable_stoppedEdge (d L : ℕ) [NeZero L] (g : ℝ) (ξ : ℂ)
    (u : ℕ → ℝ) (t' : ℝ) {τ : Ω' → ℕ} {Z : ℕ → Ω' → Zd d L × Zd d L → ℂ} {j : ℕ}
    (hZ : StronglyMeasurable[ℱ (j + 1)] (Z (j + 1)))
    (hτmeas : ∀ j, MeasurableSet[ℱ j] {ω | j < τ ω}) (b : Zd d L × Zd d L) :
    StronglyMeasurable[ℱ (j + 1)] (stoppedEdge d L g ξ u t' τ Z b j) := by
  have hset : MeasurableSet[ℱ (j + 1)] {ω | j < τ ω} := (ℱ.mono (Nat.le_succ j)) _ (hτmeas j)
  have hW : StronglyMeasurable[ℱ (j + 1)]
      (fun ω => Uop d L g ξ (u (j + 1)) t' (Z (j + 1) ω) b) :=
    DuhamelTail_stronglyMeasurable_Uop_apply d L g ξ _ _ hZ b
  exact hW.indicator hset

private theorem DuhamelTail_stronglyMeasurable_stoppedEdge_re (d L : ℕ) [NeZero L] (g : ℝ) (ξ : ℂ)
    (u : ℕ → ℝ) (t' : ℝ) {τ : Ω' → ℕ} {Z : ℕ → Ω' → Zd d L × Zd d L → ℂ} {j : ℕ}
    (hZ : StronglyMeasurable[ℱ (j + 1)] (Z (j + 1)))
    (hτmeas : ∀ j, MeasurableSet[ℱ j] {ω | j < τ ω}) (b : Zd d L × Zd d L) :
    StronglyMeasurable[ℱ (j + 1)] (fun ω => (stoppedEdge d L g ξ u t' τ Z b j ω).re) :=
  Complex.continuous_re.comp_stronglyMeasurable
    (DuhamelTail_stronglyMeasurable_stoppedEdge d L g ξ u t' hZ hτmeas b)

private theorem DuhamelTail_stronglyMeasurable_stoppedEdge_im (d L : ℕ) [NeZero L] (g : ℝ) (ξ : ℂ)
    (u : ℕ → ℝ) (t' : ℝ) {τ : Ω' → ℕ} {Z : ℕ → Ω' → Zd d L × Zd d L → ℂ} {j : ℕ}
    (hZ : StronglyMeasurable[ℱ (j + 1)] (Z (j + 1)))
    (hτmeas : ∀ j, MeasurableSet[ℱ j] {ω | j < τ ω}) (b : Zd d L × Zd d L) :
    StronglyMeasurable[ℱ (j + 1)] (fun ω => (stoppedEdge d L g ξ u t' τ Z b j ω).im) :=
  Complex.continuous_im.comp_stronglyMeasurable
    (DuhamelTail_stronglyMeasurable_stoppedEdge d L g ξ u t' hZ hτmeas b)

/-- `sum_stopped` at one label: the sum up to `min k (τ ω)` is the `k`-horizon sum of
`stoppedEdge` (RBM1D `stopped_sum_apply_eq`, `GridDuhamelTail.lean:222`). -/
private theorem DuhamelTail_stopped_sum_apply_eq (d L : ℕ) [NeZero L] (g : ℝ) (ξ : ℂ) (u : ℕ → ℝ)
    (t' : ℝ) (τ : Ω' → ℕ) (Z : ℕ → Ω' → Zd d L × Zd d L → ℂ) (k : ℕ) (ω : Ω')
    (b : Zd d L × Zd d L) :
    (∑ j ∈ Finset.range (min k (τ ω)), Uop d L g ξ (u (j + 1)) t' (Z (j + 1) ω)) b
      = ∑ j ∈ Finset.range k, stoppedEdge d L g ξ u t' τ Z b j ω := by
  rw [Finset.sum_apply]
  exact sum_stopped (Ω' := Ω') (M := ℂ)
    (fun j ω => Uop d L g ξ (u j) t' (Z j ω) b) τ k ω

/-- The `τ ≤ K` form of `DuhamelTail_stopped_sum_apply_eq`
(RBM1D `inner_sum_apply_eq`, `GridDuhamelTail.lean:231`). -/
private theorem DuhamelTail_inner_sum_apply_eq (d L : ℕ) [NeZero L] (g : ℝ) (ξ : ℂ) (u : ℕ → ℝ) (t : ℝ)
    {K : ℕ} {τ : Ω' → ℕ} (hτK : ∀ ω, τ ω ≤ K) (Z : ℕ → Ω' → Zd d L × Zd d L → ℂ) (ω : Ω')
    (b : Zd d L × Zd d L) :
    (∑ j ∈ Finset.range (τ ω), Uop d L g ξ (u (j + 1)) t (Z (j + 1) ω)) b
      = ∑ j ∈ Finset.range K, stoppedEdge d L g ξ u t τ Z b j ω := by
  have h := DuhamelTail_stopped_sum_apply_eq d L g ξ u t τ Z K ω b
  rwa [min_eq_right (hτK ω)] at h

end StoppedEdge

/-! ### 3. The Azuma tails -/

section Azuma

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} [StandardBorelSpace Ω'] {μ : Measure Ω'}
  [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ'}

/-- The common Azuma step: for a fixed label `b`, target time `t'` and horizon `k`, conditional
sub-Gaussian stopped increments give the complex Azuma tail for their `k`-horizon sum
(RBM1D `azuma_stoppedEdge`, `GridDuhamelTail.lean:248`).  The measurability hypothesis is only
needed for `i ≤ k` (paper-delta candidate T2101b); the process is truncated to `0` beyond `k`
to feed `azuma_complex`, which asks for adaptedness at every index. -/
private theorem DuhamelTail_azuma_stoppedEdge (d L : ℕ) [NeZero L] (g : ℝ) (ξ : ℂ) (u : ℕ → ℝ) (t' : ℝ)
    {τ : Ω' → ℕ} (hτmeas : ∀ j, MeasurableSet[ℱ j] {ω | j < τ ω})
    {Z : ℕ → Ω' → Zd d L × Zd d L → ℂ} {k : ℕ}
    (hZ : ∀ i ≤ k, StronglyMeasurable[ℱ i] (Z i))
    (b : Zd d L × Zd d L) {c : ℕ → ℝ≥0}
    (hsubG : ∀ j < k,
      HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
        (fun ω => (stoppedEdge d L g ξ u t' τ Z b j ω).re) (c j) μ ∧
      HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
        (fun ω => (stoppedEdge d L g ξ u t' τ Z b j ω).im) (c j) μ)
    {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω | x ≤ ‖∑ j ∈ Finset.range k, stoppedEdge d L g ξ u t' τ Z b j ω‖} ≤
      4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ Finset.range k, (c j : ℝ))) := by
  set Y : ℕ → Ω' → ℂ := fun i =>
    if i ≤ k then DuhamelTail_prependZero (fun j => stoppedEdge d L g ξ u t' τ Z b j) i
    else 0 with hYdef
  set cc : ℕ → ℝ≥0 := DuhamelTail_prependZero c with hccdef
  have hYsucc : ∀ j, j + 1 ≤ k → Y (j + 1) = stoppedEdge d L g ξ u t' τ Z b j := by
    intro j hj
    simp only [hYdef, hj, ↓reduceIte, DuhamelTail_prependZero_succ]
  have hYzero : Y 0 = 0 := by
    simp [hYdef, DuhamelTail_prependZero]
  have hYR : StronglyAdapted ℱ (fun i ω => (Y i ω).re) := by
    intro i
    cases i with
    | zero => simpa [hYzero] using stronglyMeasurable_const
    | succ j =>
      by_cases hj : j + 1 ≤ k
      · have := DuhamelTail_stronglyMeasurable_stoppedEdge_re d L g ξ u t' (hZ (j + 1) hj) hτmeas b
        simpa [hYsucc j hj] using this
      · simpa [hYdef, hj] using stronglyMeasurable_const
  have hYI : StronglyAdapted ℱ (fun i ω => (Y i ω).im) := by
    intro i
    cases i with
    | zero => simpa [hYzero] using stronglyMeasurable_const
    | succ j =>
      by_cases hj : j + 1 ≤ k
      · have := DuhamelTail_stronglyMeasurable_stoppedEdge_im d L g ξ u t' (hZ (j + 1) hj) hτmeas b
        simpa [hYsucc j hj] using this
      · simpa [hYdef, hj] using stronglyMeasurable_const
  have h0R : HasSubgaussianMGF (fun ω => (Y 0 ω).re) (cc 0) μ := by
    simp [hYzero, hccdef, DuhamelTail_prependZero]
  have h0I : HasSubgaussianMGF (fun ω => (Y 0 ω).im) (cc 0) μ := by
    simp [hYzero, hccdef, DuhamelTail_prependZero]
  have hCR : ∀ i < k + 1 - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (fun ω => (Y (i + 1) ω).re) (cc (i + 1)) μ := by
    intro i hi
    simp only [Nat.add_sub_cancel] at hi
    have h1 := (hsubG i hi).1
    rw [hYsucc i hi]
    simpa [hccdef, DuhamelTail_prependZero_succ] using h1
  have hCI : ∀ i < k + 1 - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (fun ω => (Y (i + 1) ω).im) (cc (i + 1)) μ := by
    intro i hi
    simp only [Nat.add_sub_cancel] at hi
    have h1 := (hsubG i hi).2
    rw [hYsucc i hi]
    simpa [hccdef, DuhamelTail_prependZero_succ] using h1
  have hazuma := azuma_complex (Z := Y) (c := cc) hYR hYI (k + 1) h0R h0I hCR hCI hx
  rw [NNReal.coe_sum] at hazuma
  have hsum : ∀ ω, ∑ j ∈ Finset.range k, stoppedEdge d L g ξ u t' τ Z b j ω
      = ∑ i ∈ Finset.range (k + 1), Y i ω := by
    intro ω
    have h3 := congrFun
      (DuhamelTail_sum_range_succ_prependZero (fun j => stoppedEdge d L g ξ u t' τ Z b j) k) ω
    simp only [Finset.sum_apply] at h3
    rw [← h3]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    simp only [hYdef, hik, ↓reduceIte]
  have hsumeq : ∑ i ∈ Finset.range (k + 1), (cc i : ℝ) = ∑ j ∈ Finset.range k, (c j : ℝ) := by
    have := DuhamelTail_sum_range_succ_prependZero (M := ℝ≥0) c k
    have hcast : ((∑ i ∈ Finset.range (k + 1), DuhamelTail_prependZero c i : ℝ≥0) : ℝ)
        = ((∑ j ∈ Finset.range k, c j : ℝ≥0) : ℝ) := by exact_mod_cast this
    simpa [hccdef] using hcast
  have hset : {ω | x ≤ ‖∑ j ∈ Finset.range k, stoppedEdge d L g ξ u t' τ Z b j ω‖}
      = {ω | x ≤ ‖∑ i ∈ Finset.range (k + 1), Y i ω‖} := by
    ext ω
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hsum ω]
  rw [hset, ← hsumeq]
  exact hazuma

/-- **(T1′)** `stopped_duhamel_azuma_tail_fixed` (port of RBM1D
`stopped_duhamel_azuma_tail_fixed`, `GridDuhamelTail.lean:313`): the label-weighted Azuma tail for
a fixed target grid index `k` and a fixed label `a`, with deterministic constants `c k a j`.
Route: `sum_stopped` rewrites `(Σ_{j<min k τ} 𝒰_{u_{j+1},u_k} Z_{j+1}) a` as
`Σ_{j<k} {j<τ}·(𝒰_{u_{j+1},u_k} Z_{j+1}) a`, and `azuma_complex` is applied to that sum.

No hypothesis on `u`, `ξ` or `k` is needed: `Uop` is a total function of its real times.  The
measurability hypothesis is `∀ i ≤ k` (RBM1D has `∀ i`; T2101b). -/
theorem stopped_duhamel_azuma_tail_fixed (d L : ℕ) [NeZero L] (g : ℝ) {ξ : ℂ}
    {u : ℕ → ℝ} {τ : Ω' → ℕ} (hτmeas : ∀ j, MeasurableSet[ℱ j] {ω | j < τ ω})
    {Z : ℕ → Ω' → Zd d L × Zd d L → ℂ} (k : ℕ) (hZ : ∀ i ≤ k, StronglyMeasurable[ℱ i] (Z i))
    (a : Zd d L × Zd d L) {c : ℕ → Zd d L × Zd d L → ℕ → ℝ≥0}
    (hsubG : ∀ j < k,
      HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
        (fun ω => ({ω' | j < τ ω'}.indicator
          (fun ω' => Uop d L g ξ (u (j + 1)) (u k) (Z (j + 1) ω') a) ω).re) (c k a j) μ ∧
      HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
        (fun ω => ({ω' | j < τ ω'}.indicator
          (fun ω' => Uop d L g ξ (u (j + 1)) (u k) (Z (j + 1) ω') a) ω).im) (c k a j) μ)
    {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω | x ≤ ‖(∑ j ∈ Finset.range (min k (τ ω)),
        Uop d L g ξ (u (j + 1)) (u k) (Z (j + 1) ω)) a‖} ≤
      4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ Finset.range k, (c k a j : ℝ))) := by
  have hset : {ω | x ≤ ‖(∑ j ∈ Finset.range (min k (τ ω)),
        Uop d L g ξ (u (j + 1)) (u k) (Z (j + 1) ω)) a‖}
      = {ω | x ≤ ‖∑ j ∈ Finset.range k, stoppedEdge d L g ξ u (u k) τ Z a j ω‖} := by
    ext ω
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq,
      DuhamelTail_stopped_sum_apply_eq d L g ξ u (u k) τ Z k ω a]
  rw [hset]
  exact DuhamelTail_azuma_stoppedEdge d L g ξ u (u k) hτmeas hZ a (c := c k a) hsubG hx

/-- **(T1″)** `stopped_duhamel_azuma_union` (port of RBM1D `stopped_duhamel_azuma_union`,
`GridDuhamelTail.lean:347`): the union of the (T1′) events over all target grid indices `k ≤ K`
and all labels `a`, with a threshold `x k a` for each `(k, a)`.  On `{τ = k}` the `k`-th sum is
the linear term of the stopped Duhamel expansion at `u_τ`.

**The `k = 0` summand.**  For `k = 0` the inner constant sum is empty, so under Lean's `a / 0 = 0`
that summand would equal `4 * exp 0 = 4`, and the form summed over `k ≤ K` would be trivially
true.  In the paper's convention the `k = 0` summand is `0` (for `x 0 a > 0`), and the `k = 0`
event `{x 0 a ≤ ‖0‖}` is empty.  So the event is over all `k ≤ K`, `hx0 : ∀ a, 0 < x 0 a` is
assumed, and the right-hand side is summed over `k ∈ Icc 1 K` only.  This right-hand side is at
most the literal one, so this statement implies the literal form.  The measurability hypothesis is
`∀ i ≤ K` (RBM1D has `∀ i`; T2101b). -/
theorem stopped_duhamel_azuma_union (d L : ℕ) [NeZero L] (g : ℝ) {ξ : ℂ}
    {u : ℕ → ℝ} {τ : Ω' → ℕ} (hτmeas : ∀ j, MeasurableSet[ℱ j] {ω | j < τ ω})
    {Z : ℕ → Ω' → Zd d L × Zd d L → ℂ} (K : ℕ) (hZ : ∀ i ≤ K, StronglyMeasurable[ℱ i] (Z i))
    {c : ℕ → Zd d L × Zd d L → ℕ → ℝ≥0}
    (hsubG : ∀ k ≤ K, ∀ a : Zd d L × Zd d L, ∀ j < k,
      HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
        (fun ω => ({ω' | j < τ ω'}.indicator
          (fun ω' => Uop d L g ξ (u (j + 1)) (u k) (Z (j + 1) ω') a) ω).re) (c k a j) μ ∧
      HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
        (fun ω => ({ω' | j < τ ω'}.indicator
          (fun ω' => Uop d L g ξ (u (j + 1)) (u k) (Z (j + 1) ω') a) ω).im) (c k a j) μ)
    {x : ℕ → Zd d L × Zd d L → ℝ} (hx : ∀ k ≤ K, ∀ a, 0 ≤ x k a) (hx0 : ∀ a, 0 < x 0 a) :
    μ.real {ω | ∃ k ≤ K, ∃ a, x k a ≤ ‖(∑ j ∈ Finset.range (min k (τ ω)),
        Uop d L g ξ (u (j + 1)) (u k) (Z (j + 1) ω)) a‖} ≤
      ∑ k ∈ Finset.Icc 1 K, ∑ a : Zd d L × Zd d L,
        4 * Real.exp (-(x k a) ^ 2 / (4 * ∑ j ∈ Finset.range k, (c k a j : ℝ))) := by
  set E : ℕ → Zd d L × Zd d L → Set Ω' := fun k a => {ω | x k a ≤ ‖(∑ j ∈ Finset.range (min k (τ ω)),
        Uop d L g ξ (u (j + 1)) (u k) (Z (j + 1) ω)) a‖} with hEdef
  have hincl : {ω | ∃ k ≤ K, ∃ a, x k a ≤ ‖(∑ j ∈ Finset.range (min k (τ ω)),
        Uop d L g ξ (u (j + 1)) (u k) (Z (j + 1) ω)) a‖}
      ⊆ ⋃ k ∈ Finset.Icc 1 K, ⋃ a, E k a := by
    rintro ω ⟨k, hk, a, ha⟩
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · exfalso
      have h0 : (∑ j ∈ Finset.range (min 0 (τ ω)),
          Uop d L g ξ (u (j + 1)) (u 0) (Z (j + 1) ω)) a = 0 := by simp
      rw [h0, norm_zero] at ha
      exact absurd ha (not_le.mpr (hx0 a))
    · simp only [Set.mem_iUnion]
      exact ⟨k, Finset.mem_Icc.mpr ⟨hkpos, hk⟩, a, ha⟩
  calc μ.real {ω | ∃ k ≤ K, ∃ a, x k a ≤ ‖(∑ j ∈ Finset.range (min k (τ ω)),
        Uop d L g ξ (u (j + 1)) (u k) (Z (j + 1) ω)) a‖}
      ≤ μ.real (⋃ k ∈ Finset.Icc 1 K, ⋃ a, E k a) := measureReal_mono hincl (measure_ne_top _ _)
    _ ≤ ∑ k ∈ Finset.Icc 1 K, μ.real (⋃ a, E k a) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 K, ∑ a : Zd d L × Zd d L, μ.real (E k a) :=
        Finset.sum_le_sum fun k _ => measureReal_iUnion_fintype_le _
    _ ≤ ∑ k ∈ Finset.Icc 1 K, ∑ a : Zd d L × Zd d L,
        4 * Real.exp (-(x k a) ^ 2 / (4 * ∑ j ∈ Finset.range k, (c k a j : ℝ))) := by
        refine Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun a _ => ?_
        have hkK : k ≤ K := (Finset.mem_Icc.mp hk).2
        exact stopped_duhamel_azuma_tail_fixed d L g hτmeas k (fun i hi => hZ i (hi.trans hkK)) a
          (hsubG k hkK a) (hx k hkK a)

end Azuma

/-! ### 4. The Chebyshev tail -/

section Cheb

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ'}

/-- **(T2)** `stopped_duhamel_cheb_tail` (port of RBM1D `stopped_duhamel_cheb_tail`,
`GridDuhamelTail.lean:448`): the discrete Chebyshev tail bound for the stopped Duhamel
martingale-difference remainder (sup-norm, via the backward kernel).  Route: backward
factorisation (`Uop_comp`, merged `uopBack` with constant `4` in place of RBM1D's `2 ^ n`), then
per label the real/imaginary partial sums are martingales
(`martingale_of_condExp_sub_eq_zero_nat`), `martingale_sq_eq_sum`, and Markov's inequality.
The number of labels is `L ^ 4` (RBM1D: `L ^ n`).  `0 < x` is needed: at `x = 0` the right side is
`0` under `a / 0 = 0`.  The measurability hypothesis is `∀ i ≤ K` (RBM1D has `∀ i`; T2101b). -/
theorem stopped_duhamel_cheb_tail (d L : ℕ) [NeZero L] (g : ℝ) (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ ≤ 1) {u : ℕ → ℝ} {t : ℝ} (hu0 : 0 ≤ u 0) (hu_succ : ∀ j, u j ≤ u (j + 1))
    {K : ℕ} (hut : u K = t) (ht1 : t < 1) {τ : Ω' → ℕ} (hτK : ∀ ω, τ ω ≤ K)
    (hτmeas : ∀ j, MeasurableSet[ℱ j] {ω | j < τ ω}) {Y : ℕ → Ω' → Zd d L × Zd d L → ℂ}
    (hY : ∀ i ≤ K, StronglyMeasurable[ℱ i] (Y i)) {e : ℕ → ℝ}
    (hYmeanRe : ∀ b : Zd d L × Zd d L, ∀ j < K,
      μ[fun ω => ({ω' | j < τ ω'}.indicator
        (fun ω' => Uop d L g ξ (u (j + 1)) t (Y (j + 1) ω') b) ω).re | ℱ j] =ᵐ[μ] 0)
    (hYmeanIm : ∀ b : Zd d L × Zd d L, ∀ j < K,
      μ[fun ω => ({ω' | j < τ ω'}.indicator
        (fun ω' => Uop d L g ξ (u (j + 1)) t (Y (j + 1) ω') b) ω).im | ℱ j] =ᵐ[μ] 0)
    (hYmemLpRe : ∀ b : Zd d L × Zd d L, ∀ j < K,
      MemLp (fun ω => ({ω' | j < τ ω'}.indicator
        (fun ω' => Uop d L g ξ (u (j + 1)) t (Y (j + 1) ω') b) ω).re) 2 μ)
    (hYmemLpIm : ∀ b : Zd d L × Zd d L, ∀ j < K,
      MemLp (fun ω => ({ω' | j < τ ω'}.indicator
        (fun ω' => Uop d L g ξ (u (j + 1)) t (Y (j + 1) ω') b) ω).im) 2 μ)
    (hYbound : ∀ b : Zd d L × Zd d L, ∀ j < K,
      ∫ ω, ({ω' | j < τ ω'}.indicator
          (fun ω' => Uop d L g ξ (u (j + 1)) t (Y (j + 1) ω') b) ω).re ^ 2 ∂μ
        + ∫ ω, ({ω' | j < τ ω'}.indicator
          (fun ω' => Uop d L g ξ (u (j + 1)) t (Y (j + 1) ω') b) ω).im ^ 2 ∂μ ≤ e j)
    {x : ℝ} (hx : 0 < x) :
    μ.real {ω | ∃ a, 4 * x ≤
        ‖(∑ j ∈ Finset.range (τ ω), Uop d L g ξ (u (j + 1)) (u (τ ω)) (Y (j + 1) ω)) a‖} ≤
      (L : ℝ) ^ (2 * d) * (∑ j ∈ Finset.range K, e j) / x ^ 2 := by
  set vector : Ω' → Zd d L × Zd d L → ℂ :=
    fun ω => ∑ j ∈ Finset.range (τ ω), Uop d L g ξ (u (j + 1)) t (Y (j + 1) ω) with hvecdef
  have hincl : {ω | ∃ a, 4 * x ≤
      ‖(∑ j ∈ Finset.range (τ ω), Uop d L g ξ (u (j + 1)) (u (τ ω)) (Y (j + 1) ω)) a‖}
      ⊆ ⋃ b : Zd d L × Zd d L, {ω | x ≤ ‖vector ω b‖} := by
    intro ω hω
    obtain ⟨a, ha⟩ := hω
    have hfact := DuhamelTail_back_factor_sum_apply d L g hL hξ hu0 hu_succ hut ht1 (hτK ω)
      (fun j => Y (j + 1) ω) a
    rw [hfact] at ha
    have hmono : Monotone u := monotone_nat_of_le_succ hu_succ
    have h0m : ∀ m, 0 ≤ u m := fun m => hu0.trans (hmono (Nat.zero_le m))
    have hle_t : u (τ ω) ≤ t := hut ▸ hmono (hτK ω)
    obtain ⟨b, hb⟩ := DuhamelTail_exists_label_of_back_bound d L g hL hξ (h0m (τ ω)) hle_t ht1
      (vector ω) ha
    exact Set.mem_iUnion.mpr ⟨b, hb⟩
  calc μ.real {ω | ∃ a, 4 * x ≤
        ‖(∑ j ∈ Finset.range (τ ω), Uop d L g ξ (u (j + 1)) (u (τ ω)) (Y (j + 1) ω)) a‖}
      ≤ μ.real (⋃ b : Zd d L × Zd d L, {ω | x ≤ ‖vector ω b‖}) := measureReal_mono hincl
    _ ≤ ∑ b : Zd d L × Zd d L, μ.real {ω | x ≤ ‖vector ω b‖} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _b : Zd d L × Zd d L, (∑ j ∈ Finset.range K, e j) / x ^ 2 := by
        refine Finset.sum_le_sum (fun b _ => ?_)
        set W : ℕ → Ω' → ℂ := stoppedEdge d L g ξ u t τ Y b with hWdef
        set Mre : ℕ → Ω' → ℝ := fun i ω => ∑ j ∈ Finset.range (min i K), (W j ω).re
          with hMredef
        set Mim : ℕ → Ω' → ℝ := fun i ω => ∑ j ∈ Finset.range (min i K), (W j ω).im
          with hMimdef
        have hWadaptRe : ∀ j, j + 1 ≤ K → StronglyMeasurable[ℱ (j + 1)] (fun ω => (W j ω).re) :=
          fun j hj => DuhamelTail_stronglyMeasurable_stoppedEdge_re d L g ξ u t (hY (j + 1) hj)
            hτmeas b
        have hWadaptIm : ∀ j, j + 1 ≤ K → StronglyMeasurable[ℱ (j + 1)] (fun ω => (W j ω).im) :=
          fun j hj => DuhamelTail_stronglyMeasurable_stoppedEdge_im d L g ξ u t (hY (j + 1) hj)
            hτmeas b
        have hadpRe : StronglyAdapted ℱ Mre := by
          intro i
          refine Finset.stronglyMeasurable_fun_sum (Finset.range (min i K))
            (fun j hj => ?_)
          have hj' : j + 1 ≤ min i K := by
            simp only [Finset.mem_range] at hj
            omega
          exact (hWadaptRe j (hj'.trans (min_le_right i K))).mono
            (ℱ.mono (hj'.trans (min_le_left i K)))
        have hadpIm : StronglyAdapted ℱ Mim := by
          intro i
          refine Finset.stronglyMeasurable_fun_sum (Finset.range (min i K))
            (fun j hj => ?_)
          have hj' : j + 1 ≤ min i K := by
            simp only [Finset.mem_range] at hj
            omega
          exact (hWadaptIm j (hj'.trans (min_le_right i K))).mono
            (ℱ.mono (hj'.trans (min_le_left i K)))
        have hMemLpRe : ∀ i, MemLp (Mre i) 2 μ := fun i =>
          DuhamelTail_memLp_finset_sum (fun j ω => (W j ω).re)
            (fun j hj => hYmemLpRe b j
              (lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_right i K)))
        have hMemLpIm : ∀ i, MemLp (Mim i) 2 μ := fun i =>
          DuhamelTail_memLp_finset_sum (fun j ω => (W j ω).im)
            (fun j hj => hYmemLpIm b j
              (lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_right i K)))
        have hintRe : ∀ i, Integrable (Mre i) μ := fun i => (hMemLpRe i).integrable (by norm_num)
        have hintIm : ∀ i, Integrable (Mim i) μ := fun i => (hMemLpIm i).integrable (by norm_num)
        have hM0Re : Mre 0 = 0 := by funext ω; simp [hMredef]
        have hM0Im : Mim 0 = 0 := by funext ω; simp [hMimdef]
        have hstepRe : ∀ i, μ[Mre (i + 1) - Mre i | ℱ i] =ᵐ[μ] 0 := by
          intro i
          by_cases hiK : i < K
          · have heq : Mre (i + 1) - Mre i = fun ω => (W i ω).re := by
              funext ω
              simp only [hMredef, Pi.sub_apply]
              have h1 : min (i + 1) K = i + 1 := by omega
              have h2 : min i K = i := by omega
              rw [h1, h2, Finset.sum_range_succ]
              ring
            rw [heq]
            exact hYmeanRe b i hiK
          · have heq : Mre (i + 1) - Mre i = 0 := by
              funext ω
              simp only [hMredef, Pi.sub_apply, Pi.zero_apply]
              have h1 : min (i + 1) K = K := by omega
              have h2 : min i K = K := by omega
              rw [h1, h2]; ring
            rw [heq, condExp_zero]
        have hstepIm : ∀ i, μ[Mim (i + 1) - Mim i | ℱ i] =ᵐ[μ] 0 := by
          intro i
          by_cases hiK : i < K
          · have heq : Mim (i + 1) - Mim i = fun ω => (W i ω).im := by
              funext ω
              simp only [hMimdef, Pi.sub_apply]
              have h1 : min (i + 1) K = i + 1 := by omega
              have h2 : min i K = i := by omega
              rw [h1, h2, Finset.sum_range_succ]
              ring
            rw [heq]
            exact hYmeanIm b i hiK
          · have heq : Mim (i + 1) - Mim i = 0 := by
              funext ω
              simp only [hMimdef, Pi.sub_apply, Pi.zero_apply]
              have h1 : min (i + 1) K = K := by omega
              have h2 : min i K = K := by omega
              rw [h1, h2]; ring
            rw [heq, condExp_zero]
        have hMartRe : Martingale Mre ℱ μ :=
          martingale_of_condExp_sub_eq_zero_nat hadpRe hintRe hstepRe
        have hMartIm : Martingale Mim ℱ μ :=
          martingale_of_condExp_sub_eq_zero_nat hadpIm hintIm hstepIm
        have hsqRe := martingale_sq_eq_sum hMartRe hM0Re hMemLpRe K
        have hsqIm := martingale_sq_eq_sum hMartIm hM0Im hMemLpIm K
        have hMreK : Mre K = fun ω => ∑ j ∈ Finset.range K, (W j ω).re := by
          simp [hMredef, min_self]
        have hMimK : Mim K = fun ω => ∑ j ∈ Finset.range K, (W j ω).im := by
          simp [hMimdef, min_self]
        have hΔRe : ∀ j < K, ∀ ω, Mre (j + 1) ω - Mre j ω = (W j ω).re := by
          intro j hj ω
          simp only [hMredef]
          have h1 : min (j + 1) K = j + 1 := by omega
          have h2 : min j K = j := by omega
          rw [h1, h2, Finset.sum_range_succ]
          ring
        have hΔIm : ∀ j < K, ∀ ω, Mim (j + 1) ω - Mim j ω = (W j ω).im := by
          intro j hj ω
          simp only [hMimdef]
          have h1 : min (j + 1) K = j + 1 := by omega
          have h2 : min j K = j := by omega
          rw [h1, h2, Finset.sum_range_succ]
          ring
        have hsumRe : ∫ ω, (Mre K ω) ^ 2 ∂μ = ∑ j ∈ Finset.range K, ∫ ω, (W j ω).re ^ 2 ∂μ := by
          rw [hsqRe]
          refine Finset.sum_congr rfl (fun j hj => ?_)
          refine integral_congr_ae (Filter.EventuallyEq.of_eq ?_)
          funext ω
          rw [hΔRe j (Finset.mem_range.mp hj) ω]
        have hsumIm : ∫ ω, (Mim K ω) ^ 2 ∂μ = ∑ j ∈ Finset.range K, ∫ ω, (W j ω).im ^ 2 ∂μ := by
          rw [hsqIm]
          refine Finset.sum_congr rfl (fun j hj => ?_)
          refine integral_congr_ae (Filter.EventuallyEq.of_eq ?_)
          funext ω
          rw [hΔIm j (Finset.mem_range.mp hj) ω]
        have hboundtot :
            ∫ ω, (Mre K ω) ^ 2 ∂μ + ∫ ω, (Mim K ω) ^ 2 ∂μ ≤ ∑ j ∈ Finset.range K, e j := by
          rw [hsumRe, hsumIm, ← Finset.sum_add_distrib]
          exact Finset.sum_le_sum (fun j hj => hYbound b j (Finset.mem_range.mp hj))
        have hveceq : ∀ ω, ‖vector ω b‖ ^ 2 = (Mre K ω) ^ 2 + (Mim K ω) ^ 2 := by
          intro ω
          have hv : vector ω b = ∑ j ∈ Finset.range K, W j ω := by
            rw [hvecdef]; exact DuhamelTail_inner_sum_apply_eq d L g ξ u t hτK Y ω b
          have hre : (vector ω b).re = Mre K ω := by rw [hv, hMreK]; simp [Complex.re_sum]
          have him : (vector ω b).im = Mim K ω := by rw [hv, hMimK]; simp [Complex.im_sum]
          have hns : ‖vector ω b‖ ^ 2 = (vector ω b).re ^ 2 + (vector ω b).im ^ 2 := by
            rw [Complex.norm_eq_sqrt_sq_add_sq, Real.sq_sqrt (by positivity)]
          rw [hns, hre, him]
        have hintf : Integrable (fun ω => (Mre K ω) ^ 2 + (Mim K ω) ^ 2) μ :=
          ((hMemLpRe K).integrable_sq).add ((hMemLpIm K).integrable_sq)
        have hnn : 0 ≤ᵐ[μ] fun ω => (Mre K ω) ^ 2 + (Mim K ω) ^ 2 :=
          ae_of_all _ fun ω => by positivity
        have hmarkov := mul_meas_ge_le_integral_of_nonneg hnn hintf (x ^ 2)
        have hsetEq :
            {ω | x ≤ ‖vector ω b‖} = {ω | x ^ 2 ≤ (Mre K ω) ^ 2 + (Mim K ω) ^ 2} := by
          ext ω
          rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, ← hveceq ω]
          constructor
          · intro h; exact pow_le_pow_left₀ hx.le h 2
          · intro h
            exact (pow_le_pow_iff_left₀ hx.le (norm_nonneg _) two_ne_zero).mp h
        rw [hsetEq]
        rw [le_div_iff₀ (by positivity : (0:ℝ) < x ^ 2)]
        calc μ.real {ω | x ^ 2 ≤ (Mre K ω) ^ 2 + (Mim K ω) ^ 2} * x ^ 2
            = x ^ 2 * μ.real {ω | x ^ 2 ≤ (Mre K ω) ^ 2 + (Mim K ω) ^ 2} := by ring
          _ ≤ ∫ ω, (Mre K ω) ^ 2 + (Mim K ω) ^ 2 ∂μ := hmarkov
          _ = ∫ ω, (Mre K ω) ^ 2 ∂μ + ∫ ω, (Mim K ω) ^ 2 ∂μ :=
            integral_add (hMemLpRe K).integrable_sq (hMemLpIm K).integrable_sq
          _ ≤ ∑ j ∈ Finset.range K, e j := hboundtot
    _ = (L : ℝ) ^ (2 * d) * (∑ j ∈ Finset.range K, e j) / x ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, DuhamelTail_card_label, nsmul_eq_mul]
        push_cast
        ring

end Cheb

/-! ### 5. The deterministic bound -/

section Det

variable {Ω' : Type*}

set_option linter.unusedVariables false in
/-- **(T3)** `stopped_duhamel_det_bound` (port of RBM1D `stopped_duhamel_det_bound`,
`GridDuhamelTail.lean:662`): the pointwise bound for the stopped sum of a guarded norm-bounded
remainder.  It is meant for the `O(Δ^{3/2})` errors of the stopped Duhamel expansion only, not for
the drift.  Pure linear algebra: backward factorisation, then merged `uopBack` (constant `4` in
place of RBM1D's `2 ^ n`).

`hR : ∀ j ω, j < τ ω → ∀ b, ‖R j ω b‖ ≤ r j` is the guarded hypothesis.  `hFwd` is the
forward-kernel bound on the same guarded range.  It is a separate hypothesis because the forward
kernel `𝒰_{u_{j+1},t}` has no uniform max-norm bound as `t ‖ξ‖ → 1⁻`.  So `hR` does not imply
`hFwd` for general `t < 1`, and the proof uses only `hFwd` and `hr0`: this is a conditional
adapter, not a general bound (paper-delta candidate T2101c). -/
theorem stopped_duhamel_det_bound (d L : ℕ) [NeZero L] (g : ℝ) (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ ≤ 1) {u : ℕ → ℝ} {t : ℝ} (hu0 : 0 ≤ u 0) (hu_succ : ∀ j, u j ≤ u (j + 1))
    {K : ℕ} (hut : u K = t) (ht1 : t < 1) {τ : Ω' → ℕ} (hτK : ∀ ω, τ ω ≤ K)
    (R : ℕ → Ω' → Zd d L × Zd d L → ℂ) {r : ℕ → ℝ} (hr0 : ∀ j, 0 ≤ r j)
    (hR : ∀ j ω, j < τ ω → ∀ b, ‖R j ω b‖ ≤ r j)
    (hFwd : ∀ j ω, j < τ ω → ∀ a, ‖Uop d L g ξ (u (j + 1)) t (R j ω) a‖ ≤ 4 * r j)
    (ω : Ω') (a : Zd d L × Zd d L) :
    ‖(∑ j ∈ Finset.range (τ ω), Uop d L g ξ (u (j + 1)) (u (τ ω)) (R j ω)) a‖ ≤
      4 * (4 * ∑ j ∈ Finset.range K, r j) := by
  have hmono : Monotone u := monotone_nat_of_le_succ hu_succ
  have h0m : ∀ m, 0 ≤ u m := fun m => hu0.trans (hmono (Nat.zero_le m))
  have hle_t : u (τ ω) ≤ t := hut ▸ hmono (hτK ω)
  rw [DuhamelTail_back_factor_sum_apply d L g hL hξ hu0 hu_succ hut ht1 (hτK ω) (fun j => R j ω) a]
  have hM' : ∀ b, ‖(∑ j ∈ Finset.range (τ ω), Uop d L g ξ (u (j + 1)) t (R j ω)) b‖
      ≤ 4 * ∑ j ∈ Finset.range K, r j := by
    intro b
    calc ‖(∑ j ∈ Finset.range (τ ω), Uop d L g ξ (u (j + 1)) t (R j ω)) b‖
        = ‖∑ j ∈ Finset.range (τ ω), Uop d L g ξ (u (j + 1)) t (R j ω) b‖ := by
          rw [Finset.sum_apply]
      _ ≤ ∑ j ∈ Finset.range (τ ω), ‖Uop d L g ξ (u (j + 1)) t (R j ω) b‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range (τ ω), 4 * r j :=
          Finset.sum_le_sum (fun j hj => hFwd j ω (Finset.mem_range.mp hj) b)
      _ = 4 * ∑ j ∈ Finset.range (τ ω), r j := by rw [Finset.mul_sum]
      _ ≤ 4 * ∑ j ∈ Finset.range K, r j := by
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (hτK ω))
              (fun j _ _ => hr0 j)) (by norm_num)
  have hM0 : 0 ≤ 4 * ∑ j ∈ Finset.range K, r j :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg (fun j _ => hr0 j))
  exact uopBack d g L hL ξ hξ (u (τ ω)) t (h0m (τ ω)) hle_t ht1 _ _ hM' a

end Det

/-! ### 6. The pin (108) in grid form -/

section Pin

variable {d : ℕ} (sz : Sizes d)

/-- **Pin (108), grid form** (`alu9_STime`, `3_5`, with BDG replaced by Azuma-Hoeffding as in
DECISIONS §10; RBM2D `StoppedAzuma108`, `DuhamelTail:718`): if the stopped, propagated
martingale differences are conditionally sub-Gaussian with deterministic proxies `c j` (real and
imaginary parts), then
`P(|Σ_{j<k∧τ} (𝒰_{u_{j+1},u_k} ξ_{j+1})_a| ≥ x) ≤ 4 exp(-x²/(4 Σ_{j<k} c_j))`.
The kernel is the merged `Uop d (sz.L n) (sz.lam n)` at `ξ = |m(E)|²`, as `StoppedDuhamel105`. -/
def StoppedAzuma108 [IsFiniteMeasure (pathP sz)] (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  |E| < 2 → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → (∀ n, K n ≠ 0) →
  ∀ (n : ℕ) (τ : PathΩ sz → ℕ), (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
    ∀ (k : ℕ), k ≤ K n → ∀ (a : Zd d (sz.L n) × Zd d (sz.L n)) (c : ℕ → ℝ≥0),
      (∀ j < k,
        HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
          (fun ω => ({ω' | j < τ ω'}.indicator (fun ω' =>
            Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ)
              (gridTime s t K n (j + 1)) (gridTime s t K n k) (martInc sz E s t K n j ω') a)
            ω).re) (c j) (pathP sz) ∧
        HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
          (fun ω => ({ω' | j < τ ω'}.indicator (fun ω' =>
            Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ)
              (gridTime s t K n (j + 1)) (gridTime s t K n k) (martInc sz E s t K n j ω') a)
            ω).im) (c j) (pathP sz)) →
      ∀ x : ℝ, 0 ≤ x →
        (pathP sz).real {ω | x ≤ ‖∑ j ∈ Finset.range (min k (τ ω)),
            Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ)
              (gridTime s t K n (j + 1)) (gridTime s t K n k) (martInc sz E s t K n j ω) a‖} ≤
          4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ Finset.range k, (c j : ℝ)))

section PinHelpers

variable (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

/-- Every label of `A_i` is `filt sz i`-measurable: `Avec` is `loopFine` of the walk minus a
constant (merged `walk_measurable_loopFine`, `pathH_measurable_filt`; no window hypothesis). -/
private theorem DuhamelTail_measurable_Avec (E : ℝ) (i : ℕ) (a : Zd d (sz.L n) × Zd d (sz.L n)) :
    Measurable[filt sz i] (fun ω => Avec sz E s t K n i ω a) := by
  have h1 := (walk_measurable_loopFine d (sz.L n) (sz.W n) (zt E (gridTime s t K n i))
    (![true, false] : Fin 2 → Bool) (![a.1, a.2] : Fin 2 → Zd d (sz.L n))).comp
    (pathH_measurable_filt sz s t K n i)
  exact h1.sub measurable_const

/-- The martingale difference `ξ_{j+1}` is `filt sz (j+1)`-strongly measurable as a tensor. -/
private theorem DuhamelTail_stronglyMeasurable_martInc (E : ℝ) (j : ℕ) :
    StronglyMeasurable[filt sz (j + 1)] (martInc sz E s t K n j) := by
  have hme : Measurable[filt sz (j + 1)] (martInc sz E s t K n j) := by
    refine @measurable_pi_iff _ _ _ (filt sz (j + 1)) _ _ |>.mpr fun a => ?_
    have h1 := DuhamelTail_measurable_Avec sz s t K n E (j + 1) a
    have h2 : StronglyMeasurable[filt sz (j + 1)]
        (fun ω => (pathP sz)[fun ω' => Avec sz E s t K n (j + 1) ω' a | filt sz j] ω) :=
      stronglyMeasurable_condExp.mono ((filt sz).mono (Nat.le_succ j))
    exact h1.sub h2.measurable
  exact hme.stronglyMeasurable

/-- The process `Z_0 = 0`, `Z_{j+1} = ξ_{j+1}` fed to the generic tail. -/
private def DuhamelTail_Z (E : ℝ) : ℕ → PathΩ sz → Zd d (sz.L n) × Zd d (sz.L n) → ℂ
  | 0 => fun _ => 0
  | j + 1 => martInc sz E s t K n j

end PinHelpers

/-- **The pin (108), grid form, at one size index** (DECISIONS §29 (4)): no window hypothesis is
needed at all, because `Uop` is a total function of its real times and the measurability of the
martingale differences does not use `|E| < 2` or the grid window.  This is the generic
`stopped_duhamel_azuma_tail_fixed` at `Ω' = PathΩ sz`, `ℱ = filt sz`, `μ = pathP sz`,
`ξ = |m(E)|²`, `u = gridTime s t K n`, `Z_0 = 0`, `Z_{j+1} = martInc j`, with the constant proxy
`c`.  A conditional adapter: the sub-Gaussian hypothesis is an input, not derived. -/
theorem stoppedAzuma108_at (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (τ : PathΩ sz → ℕ) (hτ : ∀ j, MeasurableSet[filt sz j] {ω | j < τ ω})
    (k : ℕ) (a : Zd d (sz.L n) × Zd d (sz.L n)) (c : ℕ → ℝ≥0)
    (hsubG : ∀ j < k,
      HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
        (fun ω => ({ω' | j < τ ω'}.indicator (fun ω' =>
          Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ)
            (gridTime s t K n (j + 1)) (gridTime s t K n k) (martInc sz E s t K n j ω') a)
          ω).re) (c j) (pathP sz) ∧
      HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
        (fun ω => ({ω' | j < τ ω'}.indicator (fun ω' =>
          Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ)
            (gridTime s t K n (j + 1)) (gridTime s t K n k) (martInc sz E s t K n j ω') a)
          ω).im) (c j) (pathP sz))
    {x : ℝ} (hx : 0 ≤ x) :
    (pathP sz).real {ω | x ≤ ‖∑ j ∈ Finset.range (min k (τ ω)),
        Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ)
          (gridTime s t K n (j + 1)) (gridTime s t K n k) (martInc sz E s t K n j ω) a‖} ≤
      4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ Finset.range k, (c j : ℝ))) := by
  have hZ : ∀ i ≤ k, StronglyMeasurable[filt sz i] (DuhamelTail_Z sz s t K n E i) := by
    intro i _
    cases i with
    | zero => exact stronglyMeasurable_const
    | succ j => exact DuhamelTail_stronglyMeasurable_martInc sz s t K n E j
  have h := stopped_duhamel_azuma_tail_fixed d (sz.L n) (sz.lam n) (μ := pathP sz)
    (ℱ := filt sz) (ξ := ((Complex.normSq (mE E) : ℝ) : ℂ)) (u := gridTime s t K n) (τ := τ) hτ
    (Z := DuhamelTail_Z sz s t K n E) k hZ a (c := fun _ _ j => c j) hsubG hx
  simp only [Finset.sum_apply] at h
  exact h

/-- **The pin (108), grid form, proved**: `StoppedAzuma108 sz E s t K`.  The instance argument
`[IsFiniteMeasure (pathP sz)]` is the pin's (redundant: `isProbabilityMeasure_pathP`). -/
theorem stoppedAzuma108 [IsFiniteMeasure (pathP sz)] (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) :
    StoppedAzuma108 sz E s t K :=
  fun _ _ _ _ _ n τ hτ k _ a c hsubG _ hx =>
    stoppedAzuma108_at sz E s t K n τ hτ k a c hsubG hx

end Pin

/-! ### 7. Compiled nonempty instances (`d = 3`)

`stoppedAzuma108` at the merged `sz0` (`d = 3`, `L_0 = 4`, `W_0 = 32`, `lam_0 = 1/64`), at
`n = 0`, `E = 0`, `s ≡ 1/10`, `t ≡ 1/2`, `K ≡ 4`, `k = 2`, `τ ≡ 3` (so the stopped sum has the two
genuine terms `j = 0, 1`).  The conditional sub-Gaussian hypothesis is the pin's input (Mathlib has
no conditional Hoeffding lemma, so it cannot be derived for the martingale differences of the walk)
and stays a hypothesis of the first example; the second example (`τ ≡ 0`, `c ≡ 0`) discharges it
by `HasCondSubgaussianMGF.fun_zero`.  `stopped_duhamel_det_bound` is applied at `d = 3`, `L = 3`,
`g = 1/2`, `ξ = 1`, grid `u j = j / 10`, with all hypotheses discharged on a nonzero remainder. -/

section Instances

open RBM.Gauss.SizesInst

private def DuhamelTail_instS : ℕ → ℝ := fun _ => 1 / 10
private def DuhamelTail_instT : ℕ → ℝ := fun _ => 1 / 2
private def DuhamelTail_instK : ℕ → ℕ := fun _ => 4

private theorem DuhamelTail_inst_s0 : ∀ n, 0 ≤ DuhamelTail_instS n := fun _ => by
  norm_num [DuhamelTail_instS]

private theorem DuhamelTail_inst_st : ∀ n, DuhamelTail_instS n ≤ DuhamelTail_instT n := fun _ => by
  norm_num [DuhamelTail_instS, DuhamelTail_instT]

private theorem DuhamelTail_inst_t1 : ∀ n, DuhamelTail_instT n < 1 := fun _ => by
  norm_num [DuhamelTail_instT]

private theorem DuhamelTail_inst_K : ∀ n, DuhamelTail_instK n ≠ 0 := fun _ => by
  norm_num [DuhamelTail_instK]

/-- **`stoppedAzuma108` at `sz0`** (sub-Gaussian input kept as the hypothesis `hsubG`). -/
example (a : Zd 3 (sz0.L 0) × Zd 3 (sz0.L 0)) (c : ℕ → ℝ≥0)
    (hsubG : ∀ j < 2,
      HasCondSubgaussianMGF (filt sz0 j) ((filt sz0).le j)
        (fun ω => ({ω' | j < (fun _ : PathΩ sz0 => 3) ω'}.indicator (fun ω' =>
          Uop 3 (sz0.L 0) (sz0.lam 0) ((Complex.normSq (mE 0) : ℝ) : ℂ)
            (gridTime DuhamelTail_instS DuhamelTail_instT DuhamelTail_instK 0 (j + 1))
            (gridTime DuhamelTail_instS DuhamelTail_instT DuhamelTail_instK 0 2)
            (martInc sz0 0 DuhamelTail_instS DuhamelTail_instT DuhamelTail_instK 0 j ω') a) ω).re)
        (c j) (pathP sz0) ∧
      HasCondSubgaussianMGF (filt sz0 j) ((filt sz0).le j)
        (fun ω => ({ω' | j < (fun _ : PathΩ sz0 => 3) ω'}.indicator (fun ω' =>
          Uop 3 (sz0.L 0) (sz0.lam 0) ((Complex.normSq (mE 0) : ℝ) : ℂ)
            (gridTime DuhamelTail_instS DuhamelTail_instT DuhamelTail_instK 0 (j + 1))
            (gridTime DuhamelTail_instS DuhamelTail_instT DuhamelTail_instK 0 2)
            (martInc sz0 0 DuhamelTail_instS DuhamelTail_instT DuhamelTail_instK 0 j ω') a) ω).im)
        (c j) (pathP sz0))
    (x : ℝ) (hx : 0 ≤ x) :
    (pathP sz0).real {ω | x ≤ ‖∑ j ∈ Finset.range (min 2 ((fun _ : PathΩ sz0 => 3) ω)),
        Uop 3 (sz0.L 0) (sz0.lam 0) ((Complex.normSq (mE 0) : ℝ) : ℂ)
          (gridTime DuhamelTail_instS DuhamelTail_instT DuhamelTail_instK 0 (j + 1))
          (gridTime DuhamelTail_instS DuhamelTail_instT DuhamelTail_instK 0 2)
          (martInc sz0 0 DuhamelTail_instS DuhamelTail_instT DuhamelTail_instK 0 j ω) a‖} ≤
      4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ Finset.range 2, (c j : ℝ))) :=
  stoppedAzuma108 sz0 0 DuhamelTail_instS DuhamelTail_instT DuhamelTail_instK (by simp)
    DuhamelTail_inst_s0 DuhamelTail_inst_st DuhamelTail_inst_t1 DuhamelTail_inst_K 0
    (fun _ => 3) (fun _ => MeasurableSet.const _) 2 (by norm_num [DuhamelTail_instK]) a c hsubG x hx

/-- Fully discharged companion at `τ ≡ 0`, `c ≡ 0` (the stopped increments vanish, so the
sub-Gaussian hypothesis holds by `HasCondSubgaussianMGF.fun_zero`). -/
example (a : Zd 3 (sz0.L 0) × Zd 3 (sz0.L 0)) (x : ℝ) (hx : 0 ≤ x) :
    (pathP sz0).real {ω | x ≤ ‖∑ j ∈ Finset.range (min 2 ((fun _ : PathΩ sz0 => 0) ω)),
        Uop 3 (sz0.L 0) (sz0.lam 0) ((Complex.normSq (mE 0) : ℝ) : ℂ)
          (gridTime DuhamelTail_instS DuhamelTail_instT DuhamelTail_instK 0 (j + 1))
          (gridTime DuhamelTail_instS DuhamelTail_instT DuhamelTail_instK 0 2)
          (martInc sz0 0 DuhamelTail_instS DuhamelTail_instT DuhamelTail_instK 0 j ω) a‖} ≤
      4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ Finset.range 2, (((fun _ => 0 : ℕ → ℝ≥0) j : ℝ≥0) : ℝ))) := by
  refine stoppedAzuma108 sz0 0 DuhamelTail_instS DuhamelTail_instT DuhamelTail_instK (by simp)
    DuhamelTail_inst_s0 DuhamelTail_inst_st DuhamelTail_inst_t1 DuhamelTail_inst_K 0
    (fun _ => 0) (fun _ => MeasurableSet.const _) 2 (by norm_num [DuhamelTail_instK]) a
    (fun _ => 0) ?_ x hx
  intro j _
  have h0 : ∀ f : PathΩ sz0 → ℂ,
      (fun ω => ({ω' | j < (fun _ : PathΩ sz0 => 0) ω'}.indicator f ω).re) = fun _ => (0 : ℝ) := by
    intro f; funext ω; simp
  have h1 : ∀ f : PathΩ sz0 → ℂ,
      (fun ω => ({ω' | j < (fun _ : PathΩ sz0 => 0) ω'}.indicator f ω).im) = fun _ => (0 : ℝ) := by
    intro f; funext ω; simp
  refine ⟨?_, ?_⟩
  · rw [h0]; exact HasCondSubgaussianMGF.fun_zero
  · rw [h1]; exact HasCondSubgaussianMGF.fun_zero

/-- Boundary `k = 0` (DECISIONS §29): the sum is empty and the right side is `4 exp 0 = 4`. -/
example (a : Zd 3 (sz0.L 0) × Zd 3 (sz0.L 0)) (τ : PathΩ sz0 → ℕ)
    (hτ : ∀ j, MeasurableSet[filt sz0 j] {ω | j < τ ω}) (c : ℕ → ℝ≥0) (x : ℝ) (hx : 0 ≤ x) :
    (pathP sz0).real {ω | x ≤ ‖∑ j ∈ Finset.range (min 0 (τ ω)),
        Uop 3 (sz0.L 0) (sz0.lam 0) ((Complex.normSq (mE 0) : ℝ) : ℂ)
          (gridTime DuhamelTail_instS DuhamelTail_instT DuhamelTail_instK 0 (j + 1))
          (gridTime DuhamelTail_instS DuhamelTail_instT DuhamelTail_instK 0 0)
          (martInc sz0 0 DuhamelTail_instS DuhamelTail_instT DuhamelTail_instK 0 j ω) a‖} ≤ 4 := by
  have h := stoppedAzuma108 sz0 0 DuhamelTail_instS DuhamelTail_instT DuhamelTail_instK (by simp)
    DuhamelTail_inst_s0 DuhamelTail_inst_st DuhamelTail_inst_t1 DuhamelTail_inst_K 0 τ hτ 0
    (Nat.zero_le _) a c (fun j hj => absurd hj (Nat.not_lt_zero j)) x hx
  simpa using h

private def DuhamelTail_instU : ℕ → ℝ := fun j => (j : ℝ) / 10

/-- **`stopped_duhamel_det_bound`** at `d = 3`, `L = 3`, `g = 1/2`, `ξ = 1`, `u j = j / 10`,
`K = 4`, `t = u 4 = 2/5`, `τ ≡ 3`: the remainder `R j = 𝒰_{t,u_{j+1}} 1` (the back kernel applied
to the constant tensor `1`, nonzero because `𝒰_{u_{j+1},t} R j = 1`) has `‖R j‖ ≤ 4 = r j` by
`uopBack`, and `‖𝒰_{u_{j+1},t} R j‖ = 1 ≤ 4 r j` by the semigroup law. -/
example (a : Zd 3 3 × Zd 3 3) :
    ‖(∑ j ∈ Finset.range ((fun _ : Unit => 3) ()),
        Uop 3 3 (1 / 2) 1 (DuhamelTail_instU (j + 1)) (DuhamelTail_instU ((fun _ : Unit => 3) ()))
          (Uop 3 3 (1 / 2) 1 (DuhamelTail_instU 4) (DuhamelTail_instU (j + 1)) (fun _ => 1))) a‖ ≤
      4 * (4 * ∑ _j ∈ Finset.range 4, (4 : ℝ)) := by
  have hu : ∀ j ≤ 4, 0 ≤ DuhamelTail_instU j ∧ DuhamelTail_instU j ≤ 2 / 5 := by
    intro j hj
    have : (j : ℝ) ≤ 4 := by exact_mod_cast hj
    unfold DuhamelTail_instU
    constructor <;> linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hnorm : ∀ v : ℝ, 0 ≤ v → v ≤ 2 / 5 → ‖(v : ℂ) * (1 : ℂ)‖ < 1 := fun v h0 h1 => by
    rw [mul_one, Complex.norm_real, Real.norm_of_nonneg h0]; linarith
  refine stopped_duhamel_det_bound 3 3 (1 / 2) (by norm_num) (ξ := 1) (by simp)
    (u := DuhamelTail_instU) (t := DuhamelTail_instU 4) (by simpa using (hu 0 (by norm_num)).1)
    (fun j => by
      unfold DuhamelTail_instU; push_cast; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
    (K := 4) rfl (by norm_num [DuhamelTail_instU]) (τ := fun _ : Unit => 3)
    (fun _ => by norm_num)
    (R := fun j _ => Uop 3 3 (1 / 2) 1 (DuhamelTail_instU 4) (DuhamelTail_instU (j + 1))
      (fun _ => 1)) (r := fun _ => 4) (fun _ => by norm_num) ?_ ?_ () a
  · intro j _ hj b
    have hj' : j + 1 ≤ 4 := by omega
    have h := uopBack 3 (1 / 2) 3 (by norm_num) 1 (by simp) (DuhamelTail_instU (j + 1))
      (DuhamelTail_instU 4) (hu _ hj').1 (by
        have : (j : ℝ) + 1 ≤ 4 := by exact_mod_cast hj'
        unfold DuhamelTail_instU; push_cast; linarith)
      (by norm_num [DuhamelTail_instU]) (fun _ => (1 : ℂ)) 1 (fun _ => by simp) b
    simpa using h
  · intro j _ hj b
    have hj' : j + 1 ≤ 4 := by omega
    rw [Uop_comp 3 3 (1 / 2) (by norm_num) (hnorm _ (hu _ hj').1 (hu _ hj').2)
      (hnorm _ (hu 4 le_rfl).1 (hu 4 le_rfl).2),
      Uop_self 3 3 (1 / 2) (by norm_num) (hnorm _ (hu 4 le_rfl).1 (hu 4 le_rfl).2)]
    norm_num

end Instances

end RBM.Path
