/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.GUEPhase.EntryTail

/-!
# The probabilistic half of Lemma 4.1 at the mixture profile, second half, `d ≥ 3` (T2298, UN-42)

Port of `RBM2D/Universality/GUEPhase/EntryTail.lean` at `c9a24cf`, lines `876-1525` (the union
of the four failure events, its probability, the union bound over the grid at one size, the size
scale and the main theorem `gueEntryMix`), to `d ≥ 3`.  The first half (carrier, law, profile,
tails, deterministic bridge) is `EntryTail.lean` (T2293).

* `mixCq`, `mixBad d L W g a b z Λ` (the union of the four large-deviation failure events at the
  profile `Smix d L W g a b`), `mixBad_tail` (`gaussLaw (mixVar) (mixBad) ≤ 4 N² Cq / Λ^{q+1}`,
  `N = (W L)^d`);
* `mixEntry_event_subset`: on `ouP (UNModel.band sz) n` the event of the pin is inside
  `mixSample⁻¹ (mixBad …)` (`mixEntry_det`, coupling `g = sz.lam n ∈ (0, Λ]`);
* `mixEntry_union`: the union over the `K + 1` mixtures, `≤ (K + 1) 4 N² Cq / Φ^{q+1}`;
* `gueEntryMix (hd : 3 ≤ d) : GUEEntryMix d`: `Φ = N^{τ'}`, `τ' = min (τ/4) c₀`, `q` with
  `τ'(q+1) ≥ D + n0 + 3`; the constants `mixDelta d 𝔡⁻¹ κ`, `mixCdet d 𝔡⁻¹ κ` do not depend on `n`
  (`Kstab3` is `L`-free), so the size scale of RBM2D `:1240-1384` (`Kstab2 ≲ log L`) is replaced by
  `eventually_le_rpow`; the coupling window `0 < sz.lam n ≤ 𝔡⁻¹` is the consequence of `WO 𝔡`.

The `d ≥ 3` changes against RBM2D: the carrier (`ouP (UNModel.band sz) n`, coupling `sz.lam n`),
`W^{-2} ↦ W^{-d}`, `(W L)^2 ↦ (W L)^d`, `Admissible 𝔠 d ↦ sz.Admissible 𝔠 𝔡`, the interface of
`mixEntry_det` (`hd : 3 ≤ d`, `0 < g ≤ Λ`), and the size scale (constants instead of `log L`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace RBM.Univ

open MeasureTheory ProbabilityTheory Filter Matrix
open RBM.Gauss RBM.Green
open scoped NNReal ENNReal

/-! ## Part 2.6 The union of the four failure events and its probability -/

section MixBad

/-- The constant of the common polynomial bound of the three tails: for `Λ ≥ 2`, each of
`A_q / ((Λ-1)²)^{q+1}`, `A_q / Λ^{q+1}`, `2 exp(-Λ/2)` is at most `mixCq q / Λ^{q+1}`
(RBM2D `:884`, verbatim). -/
def mixCq (q : ℕ) : ℝ := 4 ^ (q + 1) * hwConst q + 2 ^ (q + 2) * ((q + 1).factorial : ℝ)

theorem mixCq_pos (q : ℕ) : 0 < mixCq q := by
  unfold mixCq
  have := hwConst_pos q
  positivity

theorem mixEntry_tail_row_le {Λ : ℝ} (hΛ : 2 ≤ Λ) (q : ℕ) :
    hwConst q / ((Λ - 1) ^ 2) ^ (q + 1) ≤ mixCq q / Λ ^ (q + 1) := by
  have hΛ0 : 0 < Λ := by linarith
  have h1 : Λ / 4 ≤ (Λ - 1) ^ 2 := by nlinarith
  have h2 : (Λ / 4) ^ (q + 1) ≤ ((Λ - 1) ^ 2) ^ (q + 1) :=
    pow_le_pow_left₀ (by positivity) h1 _
  have h3 : hwConst q / ((Λ - 1) ^ 2) ^ (q + 1) ≤ hwConst q / (Λ / 4) ^ (q + 1) :=
    div_le_div_of_nonneg_left (hwConst_pos q).le (by positivity) h2
  have h4 : hwConst q / (Λ / 4) ^ (q + 1) = 4 ^ (q + 1) * hwConst q / Λ ^ (q + 1) := by
    rw [div_pow]
    field_simp
  have h5 : 4 ^ (q + 1) * hwConst q ≤ mixCq q := by
    unfold mixCq
    have : 0 ≤ 2 ^ (q + 2) * ((q + 1).factorial : ℝ) := by positivity
    linarith
  rw [h4] at h3
  exact h3.trans (div_le_div_of_nonneg_right h5 (by positivity))

theorem mixEntry_tail_quad_le {Λ : ℝ} (hΛ : 0 < Λ) (q : ℕ) :
    hwConst q / Λ ^ (q + 1) ≤ mixCq q / Λ ^ (q + 1) := by
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  unfold mixCq
  have h1 : (1 : ℝ) ≤ 4 ^ (q + 1) := one_le_pow₀ (by norm_num)
  have h2 := hwConst_pos q
  have : 0 ≤ 2 ^ (q + 2) * ((q + 1).factorial : ℝ) := by positivity
  nlinarith

theorem mixEntry_tail_diag_le {Λ : ℝ} (hΛ : 0 < Λ) (q : ℕ) :
    2 * Real.exp (-Λ / 2) ≤ mixCq q / Λ ^ (q + 1) := by
  have hfac : (0 : ℝ) < ((q + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have h1 := Real.pow_div_factorial_le_exp (x := Λ / 2) (by positivity) (q + 1)
  have hexp : Real.exp (-Λ / 2) = (Real.exp (Λ / 2))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have hpos : 0 < (Λ / 2) ^ (q + 1) / ((q + 1).factorial : ℝ) := by positivity
  have h3 : (Real.exp (Λ / 2))⁻¹ ≤ ((Λ / 2) ^ (q + 1) / ((q + 1).factorial : ℝ))⁻¹ :=
    inv_anti₀ hpos h1
  have h4 : ((Λ / 2) ^ (q + 1) / ((q + 1).factorial : ℝ))⁻¹
      = 2 ^ (q + 1) * ((q + 1).factorial : ℝ) / Λ ^ (q + 1) := by
    rw [inv_div, div_pow]
    field_simp
  rw [hexp]
  have h5 : 2 * (Real.exp (Λ / 2))⁻¹ ≤ 2 * (2 ^ (q + 1) * ((q + 1).factorial : ℝ) / Λ ^ (q + 1)) :=
    mul_le_mul_of_nonneg_left (h3.trans_eq h4) (by norm_num)
  refine h5.trans ?_
  have h6 : 2 * (2 ^ (q + 1) * ((q + 1).factorial : ℝ) / Λ ^ (q + 1))
      = 2 ^ (q + 2) * ((q + 1).factorial : ℝ) / Λ ^ (q + 1) := by
    rw [pow_succ 2 (q + 1)]
    ring
  rw [h6]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  unfold mixCq
  have := hwConst_pos q
  have h7 : (0 : ℝ) ≤ 4 ^ (q + 1) * hwConst q := by positivity
  linarith

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- **The union of the four large-deviation failure events** at the mixture `(a, b)`, the profile
`Smix d L W g a b`, the spectral parameter `z` and the factor `Λ`: some row sum (4.8), some column
sum (4.8), some quadratic form (4.7), or some diagonal entry exceeds its proxy by the factor `Λ`.
On the complement, `mixEntry_det` (`mix_det`) applies.  RBM2D `:954`. -/
def mixBad (g a b : ℝ) (z : ℂ) (Λ : ℝ) : Set (Ω d L W) :=
  (⋃ p : Idx d L W × Idx d L W, {s : Ω d L W | p.1 ≠ p.2 ∧
      Λ * ldeRowRHS (Smix d L W g a b) (green (Xmat d L W s) z) p.1 p.2 <
        ldeRowLHS (Xmat d L W s) (green (Xmat d L W s) z) p.1 p.2}) ∪
  (⋃ p : Idx d L W × Idx d L W, {s : Ω d L W | p.1 ≠ p.2 ∧
      Λ * ldeColRHS (Smix d L W g a b) (green (Xmat d L W s) z) p.1 p.2 <
        ldeColLHS (Xmat d L W s) (green (Xmat d L W s) z) p.1 p.2}) ∪
  (⋃ i : Idx d L W, {s : Ω d L W | Λ * ldeQuadRHS (Smix d L W g a b) (green (Xmat d L W s) z) i <
      ldeQuadLHS (Xmat d L W s) (green (Xmat d L W s) z) (Smix d L W g a b) 1 i}) ∪
  (⋃ i : Idx d L W, {s : Ω d L W | Λ * Smix d L W g a b i i < ‖Xmat d L W s i i‖ ^ 2})

private theorem mixEntry_measurableSet_and {α : Type*} [MeasurableSpace α] {P : Prop}
    {A : Set α} (hA : P → MeasurableSet A) : MeasurableSet {s | P ∧ s ∈ A} := by
  by_cases hP : P
  · have : {s | P ∧ s ∈ A} = A := by ext s; simp [hP]
    rw [this]
    exact hA hP
  · have : {s | P ∧ s ∈ A} = ∅ := by ext s; simp [hP]
    rw [this]
    exact MeasurableSet.empty

private theorem mixEntry_measure_and_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {P : Prop} {A : Set α} {B : ℝ≥0∞} (hA : P → μ A ≤ B) : μ {s | P ∧ s ∈ A} ≤ B := by
  by_cases hP : P
  · have : {s | P ∧ s ∈ A} = A := by ext s; simp [hP]
    rw [this]
    exact hA hP
  · have : {s | P ∧ s ∈ A} = ∅ := by ext s; simp [hP]
    rw [this, measure_empty]
    exact zero_le

theorem mixEntry_measurableSet_mixBad (g a b : ℝ) {z : ℂ} (hz : z.im ≠ 0) (Λ : ℝ) :
    MeasurableSet (mixBad d L W g a b z Λ) := by
  unfold mixBad
  refine ((MeasurableSet.union (MeasurableSet.union (MeasurableSet.union ?_ ?_) ?_) ?_))
  · exact MeasurableSet.iUnion fun p => mixEntry_measurableSet_and (A :=
      {s : Ω d L W | Λ * ldeRowRHS (Smix d L W g a b) (green (Xmat d L W s) z) p.1 p.2 <
        ldeRowLHS (Xmat d L W s) (green (Xmat d L W s) z) p.1 p.2}) fun _ =>
      measurableSet_lt ((mixEntry_meas_ldeRowRHS _ hz p.1 p.2).const_mul Λ)
        (mixEntry_meas_ldeRowLHS hz p.1 p.2)
  · exact MeasurableSet.iUnion fun p => mixEntry_measurableSet_and (A :=
      {s : Ω d L W | Λ * ldeColRHS (Smix d L W g a b) (green (Xmat d L W s) z) p.1 p.2 <
        ldeColLHS (Xmat d L W s) (green (Xmat d L W s) z) p.1 p.2}) fun _ =>
      measurableSet_lt ((mixEntry_meas_ldeColRHS _ hz p.1 p.2).const_mul Λ)
        (mixEntry_meas_ldeColLHS hz p.1 p.2)
  · exact MeasurableSet.iUnion fun i =>
      measurableSet_lt ((mixEntry_meas_ldeQuadRHS _ hz i).const_mul Λ)
        (mixEntry_meas_ldeQuadLHS _ 1 hz i)
  · exact MeasurableSet.iUnion fun i =>
      measurableSet_lt (measurable_const.mul measurable_const) (mixEntry_meas_diag i)

/-- **The probability of the union of the failure events** (RBM1D's union bound over the grid
`gueEntry_stochDom_of_tail`, for one mixture): for `Λ ≥ 2`, `N = (W L)^d` and
`ε = mixCq q / Λ^{q+1}`, `gaussLaw (mixVar g a b) (mixBad g a b z Λ) ≤ 4 N² ε`.  RBM2D `:1008`
(`(W L)^2 ↦ (W L)^d`; the outer `^ 2` is the pair count). -/
theorem mixBad_tail (g : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 < a + b) {z : ℂ}
    (hz : z.im ≠ 0) {Λ : ℝ} (hΛ : 2 ≤ Λ) (q : ℕ) :
    gaussLaw d L W (mixVar d L W g a b) (mixBad d L W g a b z Λ)
      ≤ ENNReal.ofReal (4 * (((W * L) ^ d : ℕ) : ℝ) ^ 2 * (mixCq q / Λ ^ (q + 1))) := by
  have hv := mixVar_tagFree d L W g a b
  have hS := mixProfOK (d := d) (L := L) (W := W) g ha hb
  have hΛ0 : 0 < Λ := by linarith
  have hΛ1 : 1 < Λ := by linarith
  set ε : ℝ := mixCq q / Λ ^ (q + 1) with hε
  have hε0 : 0 ≤ ε := by
    have := mixCq_pos q
    positivity
  set Nn : ℕ := (W * L) ^ d with hNn
  have hNn1 : (1 : ℝ) ≤ (Nn : ℝ) := by
    have : 0 < W * L := Nat.mul_pos (NeZero.pos W) (NeZero.pos L)
    exact_mod_cast Nat.one_le_pow _ _ this
  have hcardI : Fintype.card (Idx d L W) = Nn := RBM.Gauss.card_Idx d L W
  have hcardP : Fintype.card (Idx d L W × Idx d L W) = Nn * Nn := by
    rw [Fintype.card_prod, hcardI]
  -- the four sums
  have hrow : gaussLaw d L W (mixVar d L W g a b) (⋃ p : Idx d L W × Idx d L W, {s : Ω d L W |
      p.1 ≠ p.2 ∧ Λ * ldeRowRHS (Smix d L W g a b) (green (Xmat d L W s) z) p.1 p.2 <
        ldeRowLHS (Xmat d L W s) (green (Xmat d L W s) z) p.1 p.2}) ≤
      ENNReal.ofReal ((Nn : ℝ) ^ 2 * ε) := by
    refine (measure_iUnion_fintype_le _ _).trans ?_
    have hp : ∀ p : Idx d L W × Idx d L W, gaussLaw d L W (mixVar d L W g a b) {s : Ω d L W |
        p.1 ≠ p.2 ∧ Λ * ldeRowRHS (Smix d L W g a b) (green (Xmat d L W s) z) p.1 p.2 <
          ldeRowLHS (Xmat d L W s) (green (Xmat d L W s) z) p.1 p.2} ≤ ENNReal.ofReal ε :=
      fun p =>
      mixEntry_measure_and_le (A := {s : Ω d L W |
        Λ * ldeRowRHS (Smix d L W g a b) (green (Xmat d L W s) z) p.1 p.2 <
          ldeRowLHS (Xmat d L W s) (green (Xmat d L W s) z) p.1 p.2}) _ fun hpp =>
        (mixEntry_row_tail hv hS hz hpp hΛ1 q).trans
          (ENNReal.ofReal_le_ofReal (mixEntry_tail_row_le hΛ q))
    refine (Finset.sum_le_sum fun p _ => hp p).trans ?_
    rw [Finset.sum_const, Finset.card_univ, hcardP, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    push_cast
    ring
  have hcol : gaussLaw d L W (mixVar d L W g a b) (⋃ p : Idx d L W × Idx d L W, {s : Ω d L W |
      p.1 ≠ p.2 ∧ Λ * ldeColRHS (Smix d L W g a b) (green (Xmat d L W s) z) p.1 p.2 <
        ldeColLHS (Xmat d L W s) (green (Xmat d L W s) z) p.1 p.2}) ≤
      ENNReal.ofReal ((Nn : ℝ) ^ 2 * ε) := by
    refine (measure_iUnion_fintype_le _ _).trans ?_
    have hp : ∀ p : Idx d L W × Idx d L W, gaussLaw d L W (mixVar d L W g a b) {s : Ω d L W |
        p.1 ≠ p.2 ∧ Λ * ldeColRHS (Smix d L W g a b) (green (Xmat d L W s) z) p.1 p.2 <
          ldeColLHS (Xmat d L W s) (green (Xmat d L W s) z) p.1 p.2} ≤ ENNReal.ofReal ε :=
      fun p =>
      mixEntry_measure_and_le (A := {s : Ω d L W |
        Λ * ldeColRHS (Smix d L W g a b) (green (Xmat d L W s) z) p.1 p.2 <
          ldeColLHS (Xmat d L W s) (green (Xmat d L W s) z) p.1 p.2}) _ fun hpp =>
        (mixEntry_col_tail hv hS hz hpp hΛ1 q).trans
          (ENNReal.ofReal_le_ofReal (mixEntry_tail_row_le hΛ q))
    refine (Finset.sum_le_sum fun p _ => hp p).trans ?_
    rw [Finset.sum_const, Finset.card_univ, hcardP, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    push_cast
    ring
  have hquad : gaussLaw d L W (mixVar d L W g a b) (⋃ i : Idx d L W, {s : Ω d L W |
      Λ * ldeQuadRHS (Smix d L W g a b) (green (Xmat d L W s) z) i <
        ldeQuadLHS (Xmat d L W s) (green (Xmat d L W s) z) (Smix d L W g a b) 1 i}) ≤
      ENNReal.ofReal ((Nn : ℝ) * ε) := by
    refine (measure_iUnion_fintype_le _ _).trans ?_
    have hp : ∀ i : Idx d L W, gaussLaw d L W (mixVar d L W g a b) {s : Ω d L W |
        Λ * ldeQuadRHS (Smix d L W g a b) (green (Xmat d L W s) z) i <
          ldeQuadLHS (Xmat d L W s) (green (Xmat d L W s) z) (Smix d L W g a b) 1 i} ≤
        ENNReal.ofReal ε := fun i =>
      (mixEntry_quad_tail hv hS hz i hΛ0 q).trans
        (ENNReal.ofReal_le_ofReal (mixEntry_tail_quad_le hΛ0 q))
    refine (Finset.sum_le_sum fun i _ => hp i).trans ?_
    rw [Finset.sum_const, Finset.card_univ, hcardI, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have hdiag : gaussLaw d L W (mixVar d L W g a b) (⋃ i : Idx d L W, {s : Ω d L W |
      Λ * Smix d L W g a b i i < ‖Xmat d L W s i i‖ ^ 2}) ≤ ENNReal.ofReal ((Nn : ℝ) * ε) := by
    refine (measure_iUnion_fintype_le _ _).trans ?_
    have hp : ∀ i : Idx d L W, gaussLaw d L W (mixVar d L W g a b) {s : Ω d L W |
        Λ * Smix d L W g a b i i < ‖Xmat d L W s i i‖ ^ 2} ≤ ENNReal.ofReal ε := fun i =>
      (mixEntry_diag_tail hS i (mixEntry_Smix_diag_pos d L W g ha hb hu i) hΛ0).trans
        (ENNReal.ofReal_le_ofReal (by
          have := mixEntry_tail_diag_le hΛ0 q
          rw [hε]
          exact this))
    refine (Finset.sum_le_sum fun i _ => hp i).trans ?_
    rw [Finset.sum_const, Finset.card_univ, hcardI, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  -- assemble
  unfold mixBad
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add ((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
    (add_le_add hrow hcol)) hquad)) hdiag).trans ?_
  have hN0 : 0 ≤ (Nn : ℝ) := Nat.cast_nonneg _
  have e1 : ENNReal.ofReal ((Nn : ℝ) ^ 2 * ε) + ENNReal.ofReal ((Nn : ℝ) ^ 2 * ε) +
      ENNReal.ofReal ((Nn : ℝ) * ε) + ENNReal.ofReal ((Nn : ℝ) * ε)
      = ENNReal.ofReal ((Nn : ℝ) ^ 2 * ε + (Nn : ℝ) ^ 2 * ε + (Nn : ℝ) * ε + (Nn : ℝ) * ε) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [e1]
  refine ENNReal.ofReal_le_ofReal ?_
  have : (Nn : ℝ) ≤ (Nn : ℝ) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right this hε0]

end MixBad

/-! ## Part 2.7 The event of the pin is inside the failure events; the union over the grid -/

section MixEvent

variable {d : ℕ}

/-- **The event of the pin (one mixture, one pair) is contained in the failure events** (RBM1D
`gueGrid_entry_bound`, `:2299`, the `key` step): outside `mixBad`, the four large-deviation inputs
hold with the factor `Φ`, and `mixEntry_det` (i.e. `mix_det`, coupling `g = sz.lam n ∈ (0, Λ]`) gives
`|(G - m)_{ij}|² ≤ mixCdet d Λ κ Φ² maxLoopPM ≤ T maxLoopPM ≤ T (maxLoopPM + W^{-d})` on the a
priori event, which contradicts the strict inequality of the pin.  RBM2D `:1125`. -/
theorem mixEntry_event_subset (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) {Λ κ E a b δ Φ T : ℝ}
    (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ Λ) (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hu : 0 < a + b) (hu1 : a + b < 1) (hδ : δ ≤ mixDelta d Λ κ) (hΦ1 : 1 ≤ Φ)
    (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hT : mixCdet d Λ κ * Φ ^ 2 ≤ T) :
    {ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n) | ∃ i j : Idx d (sz.L n) (sz.W n),
      T * (maxLoopPM d (sz.L n) (sz.W n) E (a + b) (mixMat sz n a b ω) +
          (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) <
        (if ∀ x y, llErrMat d (sz.L n) (sz.W n) E (a + b) (mixMat sz n a b ω) x y ≤ δ
          then llErrMat d (sz.L n) (sz.W n) E (a + b) (mixMat sz n a b ω) i j ^ 2 else 0)}
      ⊆ mixSample sz n a b ⁻¹' mixBad d (sz.L n) (sz.W n) (sz.lam n) a b (zt E (a + b)) Φ := by
  rintro ω ⟨i, j, hij⟩
  by_contra hnot
  rw [mixMat_eq_Xmat_mixSample] at hij
  set s := mixSample sz n a b ω with hs
  have hnot' : s ∉ mixBad d (sz.L n) (sz.W n) (sz.lam n) a b (zt E (a + b)) Φ := hnot
  have hT0 : 0 ≤ T := le_trans (mul_nonneg (mixCdet_nonneg hκ d Λ) (sq_nonneg Φ)) hT
  have hmL : 0 ≤ maxLoopPM d (sz.L n) (sz.W n) E (a + b) (Xmat d (sz.L n) (sz.W n) s) :=
    maxLoopPM_nonneg E (a + b) _
  have hW0 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  by_cases hall : ∀ x y, llErrMat d (sz.L n) (sz.W n) E (a + b) (Xmat d (sz.L n) (sz.W n) s) x y ≤ δ
  · simp only [hall, implies_true, ↓reduceIte] at hij
    have hrow : ∀ i j, i ≠ j → ldeRowLHS (Xmat d (sz.L n) (sz.W n) s)
        (green (Xmat d (sz.L n) (sz.W n) s) (zt E (a + b))) i j ≤
        Φ * ldeRowRHS (Smix d (sz.L n) (sz.W n) (sz.lam n) a b)
          (green (Xmat d (sz.L n) (sz.W n) s) (zt E (a + b))) i j := by
      intro i j hij'
      by_contra h
      have h := not_le.1 h
      apply hnot'
      refine Or.inl (Or.inl (Or.inl (Set.mem_iUnion.2 ⟨(i, j), hij', h⟩)))
    have hcol : ∀ k j, k ≠ j → ldeColLHS (Xmat d (sz.L n) (sz.W n) s)
        (green (Xmat d (sz.L n) (sz.W n) s) (zt E (a + b))) k j ≤
        Φ * ldeColRHS (Smix d (sz.L n) (sz.W n) (sz.lam n) a b)
          (green (Xmat d (sz.L n) (sz.W n) s) (zt E (a + b))) k j := by
      intro k j hkj
      by_contra h
      have h := not_le.1 h
      apply hnot'
      refine Or.inl (Or.inl (Or.inr (Set.mem_iUnion.2 ⟨(k, j), hkj, h⟩)))
    have hquad : ∀ i, ldeQuadLHS (Xmat d (sz.L n) (sz.W n) s)
        (green (Xmat d (sz.L n) (sz.W n) s) (zt E (a + b)))
        (Smix d (sz.L n) (sz.W n) (sz.lam n) a b) 1 i ≤
        Φ * ldeQuadRHS (Smix d (sz.L n) (sz.W n) (sz.lam n) a b)
          (green (Xmat d (sz.L n) (sz.W n) s) (zt E (a + b))) i := by
      intro i
      by_contra h
      have h := not_le.1 h
      apply hnot'
      exact Or.inl (Or.inr (Set.mem_iUnion.2 ⟨i, h⟩))
    have hdiag : ∀ i, ‖Xmat d (sz.L n) (sz.W n) s i i‖ ^ 2 ≤
        Φ * Smix d (sz.L n) (sz.W n) (sz.lam n) a b i i := by
      intro i
      by_contra h
      have h := not_le.1 h
      apply hnot'
      exact Or.inr (Set.mem_iUnion.2 ⟨i, h⟩)
    have hdet := mixEntry_det hd (sz.three_le_L n) (Xmat_isHermitian d (sz.L n) (sz.W n) s) hg hgΛ
      hκ hE ha hb hu hu1 hall hδ hΦ1 hΦδ hrow hcol hquad hdiag i j
    have h1 : mixCdet d Λ κ * Φ ^ 2 * maxLoopPM d (sz.L n) (sz.W n) E (a + b)
        (Xmat d (sz.L n) (sz.W n) s)
        ≤ T * maxLoopPM d (sz.L n) (sz.W n) E (a + b) (Xmat d (sz.L n) (sz.W n) s) :=
      mul_le_mul_of_nonneg_right hT hmL
    have h2 : T * maxLoopPM d (sz.L n) (sz.W n) E (a + b) (Xmat d (sz.L n) (sz.W n) s) ≤
        T * (maxLoopPM d (sz.L n) (sz.W n) E (a + b) (Xmat d (sz.L n) (sz.W n) s) +
          (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hW0) hT0
    linarith
  · simp only [hall, ↓reduceIte] at hij
    have : 0 ≤ T * (maxLoopPM d (sz.L n) (sz.W n) E (a + b) (Xmat d (sz.L n) (sz.W n) s) +
        (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) :=
      mul_nonneg hT0 (add_nonneg hmL hW0)
    linarith

/-- **The union over the grid `k ≤ K` at one size** (RBM1D `gueEntry_stochDom_of_tail` with the
count `K + 1`): the event of the pin has `ouP`-probability at most
`(K + 1) · 4 N² · mixCq q / Φ^{q+1}`, `N = size n = (W L)^d`, for every `q`, whenever the scalar
side conditions hold.  RBM2D `:1189`. -/
theorem mixEntry_union (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) {Λ κ E δ Φ T : ℝ}
    (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ Λ) (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) {K : ℕ}
    {a b : Fin (K + 1) → ℝ} (hab : ∀ k, 0 ≤ a k ∧ 0 ≤ b k ∧ 0 < a k + b k ∧ a k + b k < 1)
    (hδ : δ ≤ mixDelta d Λ κ) (hΦ2 : 2 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1)
    (hT : mixCdet d Λ κ * Φ ^ 2 ≤ T) (q : ℕ) :
    ouP (UNModel.band sz) n {ω | ∃ (k : Fin (K + 1)) (i j : Idx d (sz.L n) (sz.W n)),
      T * (maxLoopPM d (sz.L n) (sz.W n) E (a k + b k) (mixMat sz n (a k) (b k) ω) +
          (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) <
        (if ∀ x y, llErrMat d (sz.L n) (sz.W n) E (a k + b k) (mixMat sz n (a k) (b k) ω) x y ≤ δ
          then llErrMat d (sz.L n) (sz.W n) E (a k + b k) (mixMat sz n (a k) (b k) ω) i j ^ 2
          else 0)}
      ≤ ENNReal.ofReal (((K : ℝ) + 1) *
          (4 * ((sz.size n : ℕ) : ℝ) ^ 2 * (mixCq q / Φ ^ (q + 1)))) := by
  have hΦ1 : 1 ≤ Φ := by linarith
  have hsub : {ω | ∃ (k : Fin (K + 1)) (i j : Idx d (sz.L n) (sz.W n)),
      T * (maxLoopPM d (sz.L n) (sz.W n) E (a k + b k) (mixMat sz n (a k) (b k) ω) +
          (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) <
        (if ∀ x y, llErrMat d (sz.L n) (sz.W n) E (a k + b k) (mixMat sz n (a k) (b k) ω) x y ≤ δ
          then llErrMat d (sz.L n) (sz.W n) E (a k + b k) (mixMat sz n (a k) (b k) ω) i j ^ 2
          else 0)}
      ⊆ ⋃ k : Fin (K + 1), mixSample sz n (a k) (b k) ⁻¹'
          mixBad d (sz.L n) (sz.W n) (sz.lam n) (a k) (b k) (zt E (a k + b k)) Φ := by
    rintro ω ⟨k, i, j, hω⟩
    refine Set.mem_iUnion.2 ⟨k, ?_⟩
    obtain ⟨ha, hb, hu, hu1⟩ := hab k
    exact mixEntry_event_subset hd sz n hg hgΛ hκ hE ha hb hu hu1 hδ hΦ1 hΦδ hT ⟨i, j, hω⟩
  refine (measure_mono hsub).trans ?_
  refine (measure_iUnion_fintype_le _ _).trans ?_
  have hk : ∀ k : Fin (K + 1), ouP (UNModel.band sz) n (mixSample sz n (a k) (b k) ⁻¹'
      mixBad d (sz.L n) (sz.W n) (sz.lam n) (a k) (b k) (zt E (a k + b k)) Φ) ≤
      ENNReal.ofReal (4 * ((sz.size n : ℕ) : ℝ) ^ 2 * (mixCq q / Φ ^ (q + 1))) := by
    intro k
    obtain ⟨ha, hb, hu, hu1⟩ := hab k
    rw [ouP_mixSample_preimage sz n ha hb (mixEntry_measurableSet_mixBad d (sz.L n) (sz.W n)
      (sz.lam n) (a k) (b k) (zt_im_ne_zero hκ hE hu1) Φ)]
    exact mixBad_tail d (sz.L n) (sz.W n) (sz.lam n) ha hb hu (zt_im_ne_zero hκ hE hu1) hΦ2 q
  refine (Finset.sum_le_sum fun k _ => hk k).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hB : 0 ≤ 4 * ((sz.size n : ℕ) : ℝ) ^ 2 * (mixCq q / Φ ^ (q + 1)) := by
    have := mixCq_pos q
    have : 0 < Φ := by linarith
    positivity
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  push_cast
  ring

end MixEvent

/-! ## Part 2.8 Size-scale bookkeeping: the thresholds and the arithmetic of the union bound

`δ_n ≤ N^{-c₀}` against the `n`-free constant `mixDelta d 𝔡⁻¹ κ`, `mixCdet d 𝔡⁻¹ κ` against
`N^{τ/2}` (T2278a: `Kstab3` is `L`-free, so RBM2D's `Kstab2 κ L_n ≲ log L_n` asymptotics
`:1240-1384` become `eventually_le_rpow`), the coupling window from `WO`, and the arithmetic of the
union bound (RBM1D `gueEntry_tail_eventually`, `:2060`). -/

section MixAsymp

variable {d : ℕ} (sz : Sizes d)

/-- The coupling window: `(eq:WO)` gives `0 < sz.lam n ≤ 𝔡⁻¹` eventually
(`W^{-d/2+𝔡} > 0` since `W ≥ 1`; the argument of `Induction/Step6Kit.lean:1232`, shape only). -/
private theorem EntryTail_eventually_lam {𝔡 : ℝ} (h : sz.WO 𝔡) :
    ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
  filter_upwards [h] with n hn
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) hn.1, hn.2⟩

/-- `N^{-c₀} ≤ mixDelta d Λ κ` eventually (`mixDelta_pos`, `eventually_le_rpow`; the constant does
not depend on `n`). -/
private theorem EntryTail_eventually_delta {κ c₀ : ℝ} (Λ : ℝ) (hκ : 0 < κ) (hκ2 : κ ≤ 2)
    (hc₀ : 0 < c₀) (hsz0 : Tendsto sz.size atTop atTop) :
    ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-c₀) ≤ mixDelta d Λ κ := by
  have hpos := mixDelta_pos hκ hκ2 d Λ
  filter_upwards [hsz0.eventually (eventually_le_rpow (mixDelta d Λ κ)⁻¹ hc₀),
    hsz0.eventually_gt_atTop 0] with n hn hN0
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN0
  have hNp : 0 < ((sz.size n : ℕ) : ℝ) ^ c₀ := Real.rpow_pos_of_pos hN _
  rw [Real.rpow_neg hN.le]
  calc (((sz.size n : ℕ) : ℝ) ^ c₀)⁻¹ ≤ ((mixDelta d Λ κ)⁻¹)⁻¹ := inv_anti₀ (by positivity) hn
    _ = mixDelta d Λ κ := inv_inv _

/-- `mixCdet d Λ κ ≤ N^{τ/2}` eventually (`eventually_le_rpow`; the constant does not depend on
`n`). -/
private theorem EntryTail_eventually_mixCdet {τ : ℝ} (Λ κ : ℝ) (hτ : 0 < τ)
    (hsz0 : Tendsto sz.size atTop atTop) :
    ∀ᶠ n in atTop, mixCdet d Λ κ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
  hsz0.eventually (eventually_le_rpow (mixCdet d Λ κ) (half_pos hτ))

end MixAsymp

/-- **The arithmetic of the union bound.**  With `N ≥ 1`, `Kn ≤ N^{n0}`, `τ'(q+1) ≥ D + n0 + 3` and
`8 C_q ≤ N`: `(Kn + 1) · 4 N² · C_q / (N^{τ'})^{q+1} ≤ N^{-D}`.  RBM2D `:1388`, verbatim. -/
private theorem mixEntry_final_arith {N Cq τ' D : ℝ} {Kn n0 q : ℕ} (hN1 : 1 ≤ N)
    (hK : (Kn : ℝ) ≤ N ^ n0) (hq : D + n0 + 3 ≤ τ' * (q + 1)) (hCq0 : 0 ≤ Cq)
    (hCq : 8 * Cq ≤ N) :
    ((Kn : ℝ) + 1) * (4 * N ^ 2 * (Cq / (N ^ τ') ^ (q + 1))) ≤ N ^ (-D) := by
  have hN0 : 0 < N := by linarith
  have hpow : (N ^ τ') ^ (q + 1) = N ^ (τ' * (q + 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have hexp : N ^ (D + n0 + 3) ≤ N ^ (τ' * (q + 1)) := Real.rpow_le_rpow_of_exponent_le hN1 hq
  have hsplit : N ^ (D + n0 + 3) = N ^ D * N ^ n0 * N ^ 3 := by
    rw [Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_natCast]
    norm_num
  have hXD : 0 < N ^ D := Real.rpow_pos_of_pos hN0 D
  have hY1 : 1 ≤ N ^ n0 := one_le_pow₀ hN1
  have hYp : 0 < N ^ n0 := by linarith
  have hneg : N ^ (-D) = (N ^ D)⁻¹ := Real.rpow_neg hN0.le D
  have hden : 0 < N ^ D * N ^ n0 * N ^ 3 := by positivity
  rw [hpow, hneg]
  have h1 : Cq / N ^ (τ' * (q + 1)) ≤ Cq / (N ^ D * N ^ n0 * N ^ 3) := by
    rw [← hsplit]
    exact div_le_div_of_nonneg_left hCq0 (by positivity) hexp
  have h2 : ((Kn : ℝ) + 1) ≤ 2 * N ^ n0 := by linarith
  calc ((Kn : ℝ) + 1) * (4 * N ^ 2 * (Cq / N ^ (τ' * (q + 1))))
      ≤ (2 * N ^ n0) * (4 * N ^ 2 * (Cq / (N ^ D * N ^ n0 * N ^ 3))) := by
        refine mul_le_mul h2 (mul_le_mul_of_nonneg_left h1 (by positivity)) ?_ (by positivity)
        have : 0 ≤ Cq / N ^ (τ' * (q + 1)) := by
          have := Real.rpow_pos_of_pos hN0 (τ' * (q + 1))
          positivity
        positivity
    _ = 8 * Cq / (N ^ D * N) := by
        field_simp
        ring
    _ ≤ N / (N ^ D * N) := by
        refine div_le_div_of_nonneg_right hCq (by positivity)
    _ = (N ^ D)⁻¹ := by
        field_simp

/-- The scalar conditions of `of_det` (`Green/EntryDom.lean:94-114`): `δ ≤ N^{-c₀}`, `τ' ≤ c₀`,
`36 ≤ N^{c₀}` give `36 N^{τ'} δ² ≤ 1`.  RBM2D `:1429`, verbatim. -/
private theorem mixEntry_scalar_36 {N δ c₀ τ' : ℝ} (hN1 : 1 ≤ N) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ N ^ (-c₀)) (hτ'c : τ' ≤ c₀) (hτ'0 : 0 < τ') (h36 : 36 ≤ N ^ c₀) :
    36 * N ^ τ' * δ ^ 2 ≤ 1 := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hNc : 0 < N ^ c₀ := Real.rpow_pos_of_pos hN0 c₀
  have hNneg : N ^ (-c₀) = (N ^ c₀)⁻¹ := Real.rpow_neg hN0.le c₀
  have hΦc : N ^ τ' ≤ N ^ c₀ := Real.rpow_le_rpow_of_exponent_le hN1 hτ'c
  have hΦ1 : 1 ≤ N ^ τ' := Real.one_le_rpow hN1 hτ'0.le
  have h1 : δ ^ 2 ≤ (N ^ (-c₀)) ^ 2 := pow_le_pow_left₀ hδ0 hδ 2
  have h2 : N ^ τ' * (N ^ (-c₀)) ^ 2 ≤ N ^ (-c₀) := by
    rw [hNneg]
    have h3 : N ^ τ' * (N ^ c₀)⁻¹ ≤ 1 := by
      rw [mul_inv_le_iff₀ hNc, one_mul]
      exact hΦc
    calc N ^ τ' * ((N ^ c₀)⁻¹) ^ 2 = (N ^ τ' * (N ^ c₀)⁻¹) * (N ^ c₀)⁻¹ := by ring
      _ ≤ 1 * (N ^ c₀)⁻¹ := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = (N ^ c₀)⁻¹ := one_mul _
  have h4 : 36 * N ^ (-c₀) ≤ 1 := by
    rw [hNneg, ← div_eq_mul_inv, div_le_one hNc]
    exact h36
  have h5 : 0 ≤ N ^ τ' := by linarith
  calc 36 * N ^ τ' * δ ^ 2 ≤ 36 * (N ^ τ' * (N ^ (-c₀)) ^ 2) := by
        have := mul_le_mul_of_nonneg_left h1 h5
        linarith
    _ ≤ 36 * N ^ (-c₀) := by linarith
    _ ≤ 1 := h4

/-! ## Part 2.9 The theorem `gueEntryMix` -/

section MixMain

variable {d : ℕ}

/-- **`GUEEntryMix d` (Lemma 4.1 (4.2)+(4.3) of [YY_25] for the profile `S_u = a S(g) + b N⁻¹`,
one-time-law form on `ouP (UNModel.band sz) n`, size scale) is proved, `d ≥ 3`.**  This is the port
of RBM2D `gueEntryMix` (`:1470`; RBM1D `gueGrid_entry_bound`, `GUEPhaseEntry.lean:2299`) at the
mixture profile: the deterministic `mixEntry_det` (E1) outside the four failure events `mixBad`,
whose probabilities are the Gaussian large-deviation tails of the auxiliary carrier (E0) pulled back
to `ouP` by `mixSample` (`mixBad_tail`, `mixSample_law`), with the per-`n` form of the `of_det`
engine (`Green/EntryDom.lean:66`): `Φ = N^{τ'}`, `τ' = min (τ/4) c₀`, the `n`-free constant
`mixCdet d 𝔡⁻¹ κ` absorbed by `N^{τ/2}`, the coupling `g = sz.lam n ∈ (0, 𝔡⁻¹]` from `WO 𝔡`, and
the union bound over `k ≤ K_n ≤ N^{n0}`, `i, j`. -/
theorem gueEntryMix (hd : 3 ≤ d) : GUEEntryMix d := by
  intro 𝔠 𝔡 sz hAdm κ hκ E hE n0 K hK a b hab c₀ δ hc₀ hδ0 hδ τ D hτ hD
  obtain ⟨h𝔠, h𝔡, hsz, hbw, hWO⟩ := hAdm
  have hsz0 : Tendsto sz.size atTop atTop := tendsto_natCast_atTop_iff.mp hsz
  have hκ2 : κ ≤ 2 := by
    have := hE 0
    linarith [abs_nonneg (E 0)]
  set τ' : ℝ := min (τ / 4) c₀ with hτ'
  have hτ'0 : 0 < τ' := lt_min (by positivity) hc₀
  have hτ'c : τ' ≤ c₀ := min_le_right _ _
  have hτ'τ : τ' ≤ τ / 4 := min_le_left _ _
  obtain ⟨q, hq⟩ : ∃ q : ℕ, D + n0 + 3 ≤ τ' * (q + 1) := by
    refine ⟨⌈(D + n0 + 3) / τ'⌉₊, ?_⟩
    have h1 := Nat.le_ceil ((D + n0 + 3) / τ')
    rw [div_le_iff₀ hτ'0] at h1
    nlinarith [hτ'0]
  filter_upwards [hsz.eventually_ge_atTop 1, hδ, hsz0.eventually (eventually_le_rpow 36 hc₀),
    hsz0.eventually (eventually_le_rpow 2 hτ'0),
    EntryTail_eventually_delta sz 𝔡⁻¹ hκ hκ2 hc₀ hsz0,
    EntryTail_eventually_mixCdet sz 𝔡⁻¹ κ hτ hsz0,
    hsz.eventually_ge_atTop (8 * mixCq q), EntryTail_eventually_lam sz hWO] with n hN1 hδn h36
    hΦ2 hdelta hcdet hCq hlam
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hδ' : δ n ≤ mixDelta d 𝔡⁻¹ κ := hδn.trans hdelta
  have hΦ1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ' := Real.one_le_rpow hN1 hτ'0.le
  have hΦδ : 36 * ((sz.size n : ℕ) : ℝ) ^ τ' * δ n ^ 2 ≤ 1 :=
    mixEntry_scalar_36 hN1 (hδ0 n) hδn hτ'c hτ'0 h36
  have hΦsq : (((sz.size n : ℕ) : ℝ) ^ τ') ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    push_cast
    nlinarith
  have hT : mixCdet d 𝔡⁻¹ κ * (((sz.size n : ℕ) : ℝ) ^ τ') ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by
    calc mixCdet d 𝔡⁻¹ κ * (((sz.size n : ℕ) : ℝ) ^ τ') ^ 2
        ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
          mul_le_mul hcdet hΦsq (sq_nonneg _) (Real.rpow_nonneg hN0.le _)
      _ = ((sz.size n : ℕ) : ℝ) ^ τ := by
          rw [← Real.rpow_add hN0]
          congr 1
          ring
  have hmain : ouP (UNModel.band sz) n {ω | ∃ (k : Fin (K n + 1)) (i j : Idx d (sz.L n) (sz.W n)),
      ((sz.size n : ℕ) : ℝ) ^ τ *
          (maxLoopPM d (sz.L n) (sz.W n) (E n) (a n k + b n k)
              (mixMat sz n (a n k) (b n k) ω) + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) <
        (if ∀ x y, llErrMat d (sz.L n) (sz.W n) (E n) (a n k + b n k)
              (mixMat sz n (a n k) (b n k) ω) x y ≤ δ n
          then llErrMat d (sz.L n) (sz.W n) (E n) (a n k + b n k)
                (mixMat sz n (a n k) (b n k) ω) i j ^ 2
          else 0)} ≤
      ENNReal.ofReal (((K n : ℝ) + 1) * (4 * ((sz.size n : ℕ) : ℝ) ^ 2 *
        (mixCq q / (((sz.size n : ℕ) : ℝ) ^ τ') ^ (q + 1)))) :=
    mixEntry_union hd sz n hlam.1 hlam.2 hκ (hE n) (hab n) hδ' hΦ2 hΦδ hT q
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have hK' : (K n : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ n0 := by exact_mod_cast hK n
  exact mixEntry_final_arith hN1 hK' hq (mixCq_pos q).le hCq

end MixMain

/-! ## Compiled nonempty instances (T2298; CLAUDE.md §4 step 2)

Namespace `EntryTailMainCheck`; `d = 3`.  `gueEntryMix` is a theorem (not a hypothesis), so every
instance applies it, or the target it is built from, with every hypothesis discharged.

* `inst_mixBad_tail`: `Idx 3 3 2` (`N = 216`), `g = 1`, `(a, b) = (1/4, 1/4)`, `z = zt 0 (1/2)`,
  `Λ = 2`, `q = 1` (the bound exceeds `1`: the data is nondegenerate, the inequality weak);
  `inst_mixBad_tail_small`: the same at `Λ = 10^6`, bound `≤ 1/1000`.
* `inst_mixEntry_event_subset`, `inst_mixEntry_union`: `sz0` (`n = 0`: `L = 4`, `W = 32`,
  `lam = 1/64`, `N = 2^21`), `Λ = 10`, `κ = 1`, `E = 0`, `Φ = 2`, `δ = min (mixDelta 3 10 1) (1/12)`,
  `T = mixCdet 3 10 1 · Φ²`; the union at the three mixtures `(1/2, 0), (1/4, 1/4), (0, 1/2)`.
* `inst_entryMix`: `sz0`, `(𝔠, 𝔡) = (1/6, 1/10)`, `κ = 1`, `E ≡ 0`, `K ≡ 2`, the three mixtures,
  `c₀ = 1/4`, `δ_n = N^{-1/4}`, `τ = 1/10`, `D = 2`; `inst_entryMix_quarter`: `K ≡ 0`,
  `a ≡ b ≡ 1/4`, `δ_n = N^{-1/2}`, `c₀ = 1/2`, `n0 = 0`; `inst_lam_window`: `0 < sz0.lam n ≤ 10`. -/

namespace EntryTailMainCheck

open RBM.Gauss.SizesInst

theorem inst_mixCq_pos : 0 < mixCq 1 := mixCq_pos 1

theorem mixCq_one : mixCq 1 = 5200 := by
  unfold mixCq hwConst
  norm_num [Nat.factorial]

/-- `mixBad_tail` at `Idx 3 3 2`, `g = 1`, `(1/4, 1/4)`, `z = zt 0 (1/2)`, `Λ = 2`, `q = 1`. -/
theorem inst_mixBad_tail :
    gaussLaw 3 3 2 (mixVar 3 3 2 1 (1 / 4) (1 / 4))
        (mixBad 3 3 2 1 (1 / 4) (1 / 4) (zt 0 (1 / 2)) 2) ≤
      ENNReal.ofReal (4 * (((2 * 3) ^ 3 : ℕ) : ℝ) ^ 2 * (mixCq 1 / 2 ^ (1 + 1))) :=
  mixBad_tail 3 3 2 1 (by norm_num) (by norm_num) (by norm_num) EntryTailCheck.inst_zt_im_ne
    (by norm_num) 1

/-- `mixBad_tail` with a bound below `1`: `Λ = 10^6`, `q = 1`, `4 N² mixCq 1 / Λ² < 1/1000`. -/
theorem inst_mixBad_tail_small :
    gaussLaw 3 3 2 (mixVar 3 3 2 1 (1 / 4) (1 / 4))
        (mixBad 3 3 2 1 (1 / 4) (1 / 4) (zt 0 (1 / 2)) 1000000) ≤
      ENNReal.ofReal (1 / 1000) :=
  (mixBad_tail 3 3 2 1 (by norm_num) (by norm_num) (by norm_num) EntryTailCheck.inst_zt_im_ne
    (Λ := 1000000) (by norm_num) 1).trans
    (ENNReal.ofReal_le_ofReal (by rw [mixCq_one]; norm_num))

/-- The coupling window of the preflight sequence: `0 < lam n ≤ 10` for every `n`
(`lam n = (2 (n + 1))^{-6}`). -/
theorem inst_lam_window (n : ℕ) : 0 < sz0.lam n ∧ sz0.lam n ≤ 10 := by
  have h1 : (1 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hlam : sz0.lam n = ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ := rfl
  rw [hlam]
  refine ⟨by positivity, ?_⟩
  exact (inv_le_one_of_one_le₀ (one_le_pow₀ h1)).trans (by norm_num)

/-- `δ = min (mixDelta 3 10 1) (1/12)`: below `mixDelta 3 10 1` and `36 · 2 · δ² ≤ 1`. -/
def delta0 : ℝ := min (mixDelta 3 10 1) (1 / 12)

theorem delta0_nonneg : 0 ≤ delta0 :=
  le_min (mixDelta_pos (κ := 1) one_pos (by norm_num) 3 10).le (by norm_num)

theorem delta0_le : delta0 ≤ 1 / 12 := min_le_right _ _

theorem delta0_36 : 36 * 2 * delta0 ^ 2 ≤ 1 := by
  nlinarith [delta0_nonneg, delta0_le]

/-- `ζ_k = k / 2`: `k = 0` the band, `k = 1` the half mixture, `k = 2` the flat GUE. -/
def zeta3 (k : Fin 3) : ℝ := ((k : ℕ) : ℝ) / 2

def aMix (_n : ℕ) (k : Fin (2 + 1)) : ℝ := (1 - zeta3 k) / 2

def bMix (_n : ℕ) (k : Fin (2 + 1)) : ℝ := zeta3 k / 2

theorem mix_params_ok (n : ℕ) (k : Fin (2 + 1)) :
    0 ≤ aMix n k ∧ 0 ≤ bMix n k ∧ 0 < aMix n k + bMix n k ∧ aMix n k + bMix n k < 1 := by
  have h2 : ((k : ℕ) : ℝ) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.1 k.2
  have h0 : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold aMix bMix zeta3
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- The three parameter pairs at `u = 1/2`: the band `ζ = 0`, a mixture, the flat GUE `ζ = 1`. -/
theorem mix_params_values :
    (aMix 0 0 = 1 / 2 ∧ bMix 0 0 = 0) ∧ (aMix 0 1 = 1 / 4 ∧ bMix 0 1 = 1 / 4) ∧
      (aMix 0 2 = 0 ∧ bMix 0 2 = 1 / 2) := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [aMix, bMix, zeta3]

/-- `mixEntry_event_subset` at `sz0`, `n = 0`, `(a, b) = (1/4, 1/4)`, `Λ = 10`, `κ = 1`, `E = 0`,
`Φ = 2`, `δ = delta0`, `T = mixCdet 3 10 1 · Φ²`. -/
theorem inst_mixEntry_event_subset :
    {ω : Sizes.SeqΩ sz0 × Ω 3 (sz0.L 0) (sz0.W 0) | ∃ i j : Idx 3 (sz0.L 0) (sz0.W 0),
      (mixCdet 3 10 1 * 2 ^ 2) *
          (maxLoopPM 3 (sz0.L 0) (sz0.W 0) 0 (1 / 4 + 1 / 4) (mixMat sz0 0 (1 / 4) (1 / 4) ω) +
            (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹) <
        (if ∀ x y, llErrMat 3 (sz0.L 0) (sz0.W 0) 0 (1 / 4 + 1 / 4)
              (mixMat sz0 0 (1 / 4) (1 / 4) ω) x y ≤ delta0
          then llErrMat 3 (sz0.L 0) (sz0.W 0) 0 (1 / 4 + 1 / 4)
                (mixMat sz0 0 (1 / 4) (1 / 4) ω) i j ^ 2
          else 0)} ⊆
      mixSample sz0 0 (1 / 4) (1 / 4) ⁻¹'
        mixBad 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (1 / 4) (1 / 4) (zt 0 (1 / 4 + 1 / 4)) 2 :=
  mixEntry_event_subset (d := 3) (by norm_num) sz0 0 (Λ := 10) (κ := 1) (E := 0) (a := 1 / 4)
    (b := 1 / 4) (δ := delta0) (Φ := 2) (T := mixCdet 3 10 1 * 2 ^ 2) (inst_lam_window 0).1
    (inst_lam_window 0).2 one_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (min_le_left _ _) (by norm_num) delta0_36 le_rfl

/-- `mixEntry_union` at `sz0`, `n = 0`, `K = 2`, the three mixtures `(1/2, 0), (1/4, 1/4),
(0, 1/2)`, `Λ = 10`, `κ = 1`, `E = 0`, `Φ = 2`, `δ = delta0`, `q = 1`. -/
theorem inst_mixEntry_union :
    ouP (UNModel.band sz0) 0 {ω | ∃ (k : Fin (2 + 1)) (i j : Idx 3 (sz0.L 0) (sz0.W 0)),
      (mixCdet 3 10 1 * 2 ^ 2) *
          (maxLoopPM 3 (sz0.L 0) (sz0.W 0) 0 (aMix 0 k + bMix 0 k)
              (mixMat sz0 0 (aMix 0 k) (bMix 0 k) ω) + (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹) <
        (if ∀ x y, llErrMat 3 (sz0.L 0) (sz0.W 0) 0 (aMix 0 k + bMix 0 k)
              (mixMat sz0 0 (aMix 0 k) (bMix 0 k) ω) x y ≤ delta0
          then llErrMat 3 (sz0.L 0) (sz0.W 0) 0 (aMix 0 k + bMix 0 k)
                (mixMat sz0 0 (aMix 0 k) (bMix 0 k) ω) i j ^ 2
          else 0)} ≤
      ENNReal.ofReal ((((2 : ℕ) : ℝ) + 1) *
        (4 * ((sz0.size 0 : ℕ) : ℝ) ^ 2 * (mixCq 1 / 2 ^ (1 + 1)))) :=
  mixEntry_union (d := 3) (by norm_num) sz0 0 (Λ := 10) (κ := 1) (E := 0) (δ := delta0) (Φ := 2)
    (T := mixCdet 3 10 1 * 2 ^ 2) (inst_lam_window 0).1 (inst_lam_window 0).2 one_pos
    (by norm_num) (K := 2) (a := aMix 0) (b := bMix 0) (mix_params_ok 0) (min_le_left _ _)
    le_rfl delta0_36 le_rfl 1

/-- `K ≡ 2 ≤ N` along `sz0`. -/
theorem sz0_size_ge_two (n : ℕ) : 2 ≤ sz0.size n ^ 1 := by
  rw [pow_one]
  have h1 : 4 * (n + 1) ≤ (2 * (n + 1)) ^ 5 * (4 * (n + 1)) :=
    Nat.le_mul_of_pos_left _ (by positivity)
  have h2 : (2 * (n + 1)) ^ 5 * (4 * (n + 1)) ≤ ((2 * (n + 1)) ^ 5 * (4 * (n + 1))) ^ 3 :=
    Nat.le_self_pow (by norm_num) _
  change 2 ≤ ((2 * (n + 1)) ^ 5 * (4 * (n + 1))) ^ 3
  omega

/-- **Instance of `gueEntryMix`** at `sz0` (`d = 3`), `(𝔠, 𝔡) = (1/6, 1/10)`, `κ = 1`, `E ≡ 0`,
`K ≡ 2`, `(a, b) ∈ {(1/2, 0), (1/4, 1/4), (0, 1/2)}` (the band, a mixture, the flat GUE),
`c₀ = 1/4`, `δ_n = N^{-1/4}`, `τ = 1/10`, `D = 2`: the conclusion at this data. -/
theorem inst_entryMix :
    ∀ᶠ n in atTop, ouP (UNModel.band sz0) n
      {ω | ∃ (k : Fin (2 + 1)) (i j : Idx 3 (sz0.L n) (sz0.W n)),
        ((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) *
            (maxLoopPM 3 (sz0.L n) (sz0.W n) 0 (aMix n k + bMix n k)
                (mixMat sz0 n (aMix n k) (bMix n k) ω) + (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹) <
          (if ∀ x y, llErrMat 3 (sz0.L n) (sz0.W n) 0 (aMix n k + bMix n k)
                (mixMat sz0 n (aMix n k) (bMix n k) ω) x y ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))
            then llErrMat 3 (sz0.L n) (sz0.W n) 0 (aMix n k + bMix n k)
                (mixMat sz0 n (aMix n k) (bMix n k) ω) i j ^ 2
            else 0)} ≤ ENNReal.ofReal (((sz0.size n : ℕ) : ℝ) ^ (-(2 : ℝ))) :=
  gueEntryMix (by norm_num : 3 ≤ 3) (1 / 6) (1 / 10) sz0 sz0_admissible 1 one_pos (fun _ => 0)
    (fun n => by norm_num) 1 (fun _ => 2) sz0_size_ge_two aMix bMix mix_params_ok (1 / 4)
    (fun n => ((sz0.size n : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))) (by norm_num) (fun n => by positivity)
    (Eventually.of_forall fun n => le_rfl) (1 / 10) 2 (by norm_num) (by norm_num)

/-- **Instance of `gueEntryMix`** with the single mixture `K ≡ 0`, `a ≡ b ≡ 1/4` (`u = 1/2`),
`n0 = 0`, `c₀ = 1/2`, `δ_n = N^{-1/2}`, `τ = 1/10`, `D = 2`. -/
theorem inst_entryMix_quarter :
    ∀ᶠ n in atTop, ouP (UNModel.band sz0) n
      {ω | ∃ (_k : Fin (0 + 1)) (i j : Idx 3 (sz0.L n) (sz0.W n)),
        ((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) *
            (maxLoopPM 3 (sz0.L n) (sz0.W n) 0 ((1 / 4 : ℝ) + 1 / 4)
                (mixMat sz0 n (1 / 4) (1 / 4) ω) + (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹) <
          (if ∀ x y, llErrMat 3 (sz0.L n) (sz0.W n) 0 ((1 / 4 : ℝ) + 1 / 4)
                (mixMat sz0 n (1 / 4) (1 / 4) ω) x y ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))
            then llErrMat 3 (sz0.L n) (sz0.W n) 0 ((1 / 4 : ℝ) + 1 / 4)
                (mixMat sz0 n (1 / 4) (1 / 4) ω) i j ^ 2
            else 0)} ≤ ENNReal.ofReal (((sz0.size n : ℕ) : ℝ) ^ (-(2 : ℝ))) :=
  gueEntryMix (by norm_num : 3 ≤ 3) (1 / 6) (1 / 10) sz0 sz0_admissible 1 one_pos (fun _ => 0)
    (fun n => by norm_num) 0 (fun _ => 0) (fun n => by simp) (fun _ _ => 1 / 4)
    (fun _ _ => 1 / 4) (fun n _ => by norm_num) (1 / 2)
    (fun n => ((sz0.size n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) (by norm_num) (fun n => by positivity)
    (Eventually.of_forall fun n => le_rfl) (1 / 10) 2 (by norm_num) (by norm_num)

end EntryTailMainCheck

end RBM.Univ

end
