/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Green.FlucIter

/-!
# Iterating the vanishing lemma: counting, the graded iteration and the moment bound, `d ≥ 3`
(S1-21, second part of `Green/FlucIter.lean`)

Ticket T2096.  Port of the second part of `RBM2D/Green/FlucIter.lean` at commit `c9a24cf`
(lines `:819-:1877`, from the `Counting` docstring to the end of the file; the first part,
`:81-:818`, is `RBM3D/Green/FlucIter.lean`, T2089, which this file imports) to the fine lattice
`Z_{WL}^d`, with the renaming rules R1-R4 of `docs/tickets/ST1-COMMON.md` (item 2):
`d : Sizes` becomes `sz : Sizes d`, `Idx (d.L n) (d.W n)` becomes `Idx d (sz.L n) (sz.W n)`,
`spectralZ E t` and `spectralM E` become `zt E t` and `mE E`.  The paper (arXiv:2507.20274) does
not state these lemmas: `paper/tex/3_5_Loop_Hierarchy.tex:37` says that the estimates of
`lem_GbEXP` (among them `(GavLGEX)`, `3_5:33`) have been proven as Lemma 4.1 of `[YY_25]` and
that their proofs are dimension-independent.

## What is proved here

Everything lives at one slice `n` of a size sequence `sz : Sizes d`.

1. **Counting by lone slots** (`loneSlots`, `two_mul_card_image_le_add_card_loneSlots`,
   `card_filter_card_image_le`): `2 · #(image v) ≤ #ι + #(lone slots of v)`; generic in `ι`, `κ`.
2. **The stratified weight sum** (`sum_prod_abs_card_image_le`, `sum_weighted_le`): for a
   *bounded weight* `t` (`0 ≤ t ≤ c`, `∑ t ≤ 1`), `c ≤ ρ² ≤ 1`, the multi-indices with `a` lone
   slots carry weight `≤ n^n ρ^{n-a}`, so `∑_v ∏_i |t_{v i}| f(v) ≤ (n + 1) n^n (K ρ B)^n`.
3. **The length-graded iteration** (`OpsOkOut.length_le`, `norm_integral_prod_applyOps_le_graded`,
   `norm_integral_prod_qRow_le_graded`): `‖∫ ∏_i ℓ_i Q_{k i} X_i‖ ≤ (2 max(1,ρ))^{(#ι-1) r} ρ^r
   B^{#ι} ρ^{∑ numQ}` for `r` pivots, from the invariant `OpsOkOut` of T2089.
4. **The gain interface** `FlucGainUpTo'` (`B`, `ρ`, word length `M`, slot number `K`) and the
   **moment bound** `integral_norm_flucAvg_pow_le_iter_budget` (RBM2D `:1453`):
   `E|∑_k T_k Z_k|^{2p} ≤ (2p+1)(2p)^{2p} (2^{2p-1} ρ B)^{2p}`.
5. The gain interface holds gain-free at crude constants (`flucIter_flucGainUpTo'_of_crude`,
   private); the instances at the end of the file use it.

## Differences from RBM2D (residual, after the renaming)

* **Bounded weight (DECISIONS §30, T2061, paper-delta candidate `T2061a`).**  RBM2D takes
  `UniformWeight t c A` (`t = c` on `A`, mass `c · #A ≤ 1`) in `sum_prod_abs_card_image_le`
  (`:966`), `sum_weighted_le` and `integral_norm_flucAvg_pow_le_iter_budget` (`:1453`); here it is
  `BoundedWeight t c A` (`0 ≤ t ≤ c`, `t = 0` off `A`, `∑ t ≤ 1`).  The row `j ↦ S_{ij}` is a
  bounded weight (`boundedWeight_svarF`, `c = W^{-d}`, `#A = (2d + 1) W^d`) and not a uniform one.
* **`sum_prod_abs_card_image_le` has a new proof; its signature is RBM2D's after the renaming
  and `UniformWeight → BoundedWeight`.**  RBM2D counts the multi-indices in `A^ι` with `≤ s`
  values (`≤ (#A)^s s^n`, `card_filter_card_image_le`) and bounds each by `c^n`; the step
  `(c · #A)^s ≤ 1` uses the mass bound of the uniform weight and is false for the row at `d ≥ 3`
  (`c · #A = 2d + 1`; the chain would lose `(2d+1)^s`).  Here a multi-index with `≤ s` values is
  `w ∘ φ` for a labelling `φ : ι → Fin s`; for fixed `φ` the sum over `w` is a product of the
  one-letter sums `∑_x t_x^{n_b} ≤ c^{n_b - 1}` (`t_x^b ≤ c^{b-1} t_x`, `∑ t ≤ 1`), and there are
  `s^n` labellings, so the conclusion `≤ c^{n-s} s^n` and the budget constants of the targets are
  unchanged.  The labelling bound (private, `c ≤ 1`) is applied at `min c 1`, since a bounded
  weight has `t ≤ ∑ t ≤ 1`; the hypothesis `hs : s ≤ #A` is kept and not used.
  `sum_weighted_le` and `integral_norm_flucAvg_pow_le_iter_budget` have RBM2D's signatures after
  the renaming and `UniformWeight → BoundedWeight`.
* No other `d = 2` exponent occurs in the code of this part: the counting, the graded iteration,
  the gain interface and the budget carry no `d`; the checks are redone at `d = 3`.
-/

namespace RBM.Green

open MeasureTheory ProbabilityTheory Matrix Finset RBM.Gauss

/-! ### Counting multi-indices by the number of lone slots

The multi-indices are split by the *number* of their lone slots, not only by whether there is
one: that number is the number of pivots available, hence the power of the gain.  The counting
input is that a value taken by a non-lone slot uses up at least two slots, so

  `2 · #(image v) ≤ #ι + #(lone slots of v)`. -/

section Counting

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

/-- The set of slots whose value occurs nowhere else. -/
def loneSlots (v : ι → κ) : Finset ι :=
  (Finset.univ : Finset ι).filter fun i => ∀ j, j ≠ i → v j ≠ v i

@[simp] theorem mem_loneSlots {v : ι → κ} {i : ι} :
    i ∈ loneSlots v ↔ ∀ j, j ≠ i → v j ≠ v i := by
  simp [loneSlots]

/-- The values taken exactly once are exactly the values of the lone slots. -/
theorem image_loneSlots_eq (v : ι → κ) :
    (loneSlots v).image v
      = ((Finset.univ : Finset ι).image v).filter
          fun b => ((Finset.univ : Finset ι).filter fun i => v i = b).card = 1 := by
  classical
  ext b
  simp only [Finset.mem_image, Finset.mem_filter, mem_loneSlots]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨⟨i, Finset.mem_univ i, rfl⟩, ?_⟩
    have : ((Finset.univ : Finset ι).filter fun j => v j = v i) = {i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun hj => by_contra fun hji => hi j hji hj, fun hj => by rw [hj]⟩
    rw [this, Finset.card_singleton]
  · rintro ⟨⟨i, -, rfl⟩, hcard⟩
    obtain ⟨j, hj⟩ := Finset.card_eq_one.1 hcard
    have hij : i = j := by
      have : i ∈ ({j} : Finset ι) := by
        rw [← hj]; exact Finset.mem_filter.2 ⟨Finset.mem_univ i, rfl⟩
      exact Finset.mem_singleton.1 this
    refine ⟨i, fun j' hj' hvj' => ?_, rfl⟩
    have : j' ∈ ({j} : Finset ι) := by
      rw [← hj]; exact Finset.mem_filter.2 ⟨Finset.mem_univ j', hvj'⟩
    exact hj' (by rw [Finset.mem_singleton.1 this, ← hij])

/-- **The refined counting inequality.**  Every value of `v` uses up at least one slot, and a
value that is not the value of a lone slot uses up at least two. -/
theorem two_mul_card_image_le_add_card_loneSlots (v : ι → κ) :
    2 * ((Finset.univ : Finset ι).image v).card
      ≤ Fintype.card ι + (loneSlots v).card := by
  classical
  set I : Finset κ := (Finset.univ : Finset ι).image v with hI
  set pr : κ → Prop := fun b => ((Finset.univ : Finset ι).filter fun i => v i = b).card = 1
    with hpr
  have hinj : Set.InjOn v (loneSlots v) := by
    intro i hi j hj hij
    by_contra hne
    exact (mem_loneSlots.1 hi) j (Ne.symm hne) hij.symm
  have hSa : (I.filter pr).card = (loneSlots v).card := by
    rw [← image_loneSlots_eq v, Finset.card_image_of_injOn hinj]
  have hfib : (Fintype.card ι)
      = ∑ b ∈ I, ((Finset.univ : Finset ι).filter fun i => v i = b).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise fun i _ =>
      Finset.mem_coe.2 (Finset.mem_image_of_mem v (Finset.mem_univ i))
  have hlow : ∀ b ∈ I, (if pr b then 1 else 2)
      ≤ ((Finset.univ : Finset ι).filter fun i => v i = b).card := by
    intro b hb
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hb
    have hpos : 1 ≤ ((Finset.univ : Finset ι).filter fun j => v j = v i).card :=
      Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, rfl⟩⟩
    by_cases hp : pr (v i)
    · rw [ite_eq_left hp]; exact hpos
    · rw [ite_eq_right hp]
      rw [hpr] at hp
      omega
  have hsum : (∑ b ∈ I, (if pr b then (1 : ℕ) else 2)) ≤ Fintype.card ι := by
    rw [hfib]; exact Finset.sum_le_sum hlow
  have hval : (∑ b ∈ I, (if pr b then (1 : ℕ) else 2)) + (I.filter pr).card
      = 2 * I.card := by
    rw [← Finset.sum_filter_add_sum_filter_not I pr fun b => (if pr b then (1 : ℕ) else 2)]
    have e1 : ∑ b ∈ I.filter pr, (if pr b then (1 : ℕ) else 2) = (I.filter pr).card := by
      rw [Finset.sum_congr rfl fun b hb => ite_eq_left (Finset.mem_filter.1 hb).2,
        Finset.sum_const, smul_eq_mul, mul_one]
    have e2 : ∑ b ∈ I.filter (fun b => ¬ pr b), (if pr b then (1 : ℕ) else 2)
        = 2 * (I.filter fun b => ¬ pr b).card := by
      rw [Finset.sum_congr rfl fun b hb => ite_eq_right (Finset.mem_filter.1 hb).2,
        Finset.sum_const, smul_eq_mul, mul_comm]
    rw [e1, e2]
    have hcards := Finset.card_filter_add_card_filter_not (s := I) pr
    omega
  omega

/-- **The number of multi-indices with a small image.**  Such a `v` has its image inside an
`s`-element subset of `A`, and is then one of the `s^{#ι}` functions into it. -/
theorem card_filter_card_image_le (A : Finset κ) (s : ℕ) (hs : s ≤ A.card) :
    ((Fintype.piFinset fun _ : ι => A).filter
        fun v => ((Finset.univ : Finset ι).image v).card ≤ s).card
      ≤ A.card ^ s * s ^ Fintype.card ι := by
  classical
  have hsub : ((Fintype.piFinset fun _ : ι => A).filter
      fun v => ((Finset.univ : Finset ι).image v).card ≤ s)
      ⊆ (A.powersetCard s).biUnion fun S => Fintype.piFinset fun _ : ι => S := by
    intro v hv
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hv
    obtain ⟨hvA, hvs⟩ := hv
    have h1 : (Finset.univ : Finset ι).image v ⊆ A := by
      intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 ha
      exact hvA i
    obtain ⟨S, hS1, hS2, hS3⟩ := Finset.exists_subsuperset_card_eq h1 hvs hs
    exact Finset.mem_biUnion.2 ⟨S, Finset.mem_powersetCard.2 ⟨hS2, hS3⟩,
      Fintype.mem_piFinset.2 fun i => hS1 (Finset.mem_image_of_mem v (Finset.mem_univ i))⟩
  calc ((Fintype.piFinset fun _ : ι => A).filter
        fun v => ((Finset.univ : Finset ι).image v).card ≤ s).card
      ≤ ((A.powersetCard s).biUnion fun S => Fintype.piFinset fun _ : ι => S).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ S ∈ A.powersetCard s, (Fintype.piFinset fun _ : ι => S).card :=
        Finset.card_biUnion_le
    _ = ∑ _S ∈ A.powersetCard s, s ^ Fintype.card ι := by
        refine Finset.sum_congr rfl fun S hS => ?_
        rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
          (Finset.mem_powersetCard.1 hS).2]
    _ = (A.card).choose s * s ^ Fintype.card ι := by
        rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]
    _ ≤ A.card ^ s * s ^ Fintype.card ι := Nat.mul_le_mul_right _ (Nat.choose_le_pow _ _)

end Counting

/-! ### The stratified weight sum

With the per-multi-index bound `K^a ρ^a B^n` (`a` = number of lone slots) in hand, the sum over
multi-indices weighted by `∏_i |t_{v i}|` is stratified by `a`.  A multi-index with `a` lone
slots has at most `(n + a)/2` distinct values, so the weight of its stratum is at most
`c^{n - (n+a)/2} ((n+a)/2)^n ≤ ρ^{n-a} n^n` (`sum_prod_abs_card_image_le`, `c ≤ ρ²`), and the
`ρ^a` of the iteration completes it to `ρ^n`.  **This is why the iteration gives `Ψ^{4p}`**: with
`c ≍ Ψ²` (so `ρ ≍ Ψ`) and `B ≍ Ψ`, the bound is `C_n (B ρ)^n = C_p Ψ^{4p}`.

The weight is a *bounded weight* (DECISIONS §30): only `0 ≤ t ≤ c` and `∑ t ≤ 1` are used. -/

section Strata

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
/-- `∑_x t_x^k ≤ c^{k-1}` for `k ≥ 1`, from `0 ≤ t ≤ c`, `∑ t ≤ 1`. -/
private theorem flucIterGain_sum_pow_le {t : κ → ℝ} {c : ℝ} (hc0 : 0 ≤ c) (ht0 : ∀ x, 0 ≤ t x)
    (htc : ∀ x, t x ≤ c) (hsum : ∑ x, t x ≤ 1) {k : ℕ} (hk : 1 ≤ k) :
    ∑ x, t x ^ k ≤ c ^ (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  calc ∑ x, t x ^ (j + 1) = ∑ x, t x ^ j * t x := by simp_rw [pow_succ]
    _ ≤ ∑ x, c ^ j * t x := Finset.sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (ht0 x) (htc x) j) (ht0 x)
    _ = c ^ j * ∑ x, t x := by rw [Finset.mul_sum]
    _ ≤ c ^ j * 1 := mul_le_mul_of_nonneg_left hsum (pow_nonneg hc0 j)
    _ = c ^ j := mul_one _

omit [DecidableEq ι] [DecidableEq κ] in
/-- The weight of the multi-indices of one fixed labelling `φ : ι → β`: a product of the
one-letter sums `∑_x t_x^{n_b}`. -/
private theorem flucIterGain_sum_comp_le {β : Type*} [Fintype β] [DecidableEq β] {t : κ → ℝ}
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ht0 : ∀ x, 0 ≤ t x) (htc : ∀ x, t x ≤ c)
    (hsum : ∑ x, t x ≤ 1) (x₀ : κ) (φ : ι → β) :
    ∑ w ∈ Fintype.piFinset
          (fun b : β => if ∃ i, φ i = b then (Finset.univ : Finset κ) else {x₀}),
        ∏ i, t (w (φ i)) ≤ c ^ (Fintype.card ι - Fintype.card β) := by
  classical
  set nb : β → ℕ := fun b => (Finset.univ.filter fun i => φ i = b).card with hnb
  have hprod : ∀ w : β → κ, ∏ i, t (w (φ i)) = ∏ b, t (w b) ^ nb b := by
    intro w
    rw [← Finset.prod_fiberwise' Finset.univ φ (fun b => t (w b))]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [Finset.prod_const]
  have hfac : ∀ b : β, ∑ x ∈ (if ∃ i, φ i = b then (Finset.univ : Finset κ) else {x₀}),
      t x ^ nb b ≤ c ^ (nb b - 1) := by
    intro b
    by_cases h : ∃ i, φ i = b
    · rw [ite_eq_left h]
      obtain ⟨i, hi⟩ := h
      have : 1 ≤ nb b := Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩⟩
      exact flucIterGain_sum_pow_le hc0 ht0 htc hsum this
    · rw [ite_eq_right h]
      have h0 : nb b = 0 := by
        rw [hnb]
        simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ,
          forall_const]
        exact fun i hi => h ⟨i, hi⟩
      simp [h0]
  have hsumn : ∑ b, nb b = Fintype.card ι := by
    rw [← Finset.card_univ]
    exact (Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ (φ i))).symm
  have hexp : Fintype.card ι - Fintype.card β ≤ ∑ b, (nb b - 1) := by
    have h1 : ∑ b, nb b ≤ ∑ b, ((nb b - 1) + 1) :=
      Finset.sum_le_sum fun b _ => by omega
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
      hsumn] at h1
    omega
  set Tb : β → Finset κ := fun b => if ∃ i, φ i = b then (Finset.univ : Finset κ) else {x₀}
    with hTb
  calc ∑ w ∈ Fintype.piFinset Tb, ∏ i, t (w (φ i))
      = ∑ w ∈ Fintype.piFinset Tb, ∏ b, t (w b) ^ nb b :=
        Finset.sum_congr rfl fun w _ => hprod w
    _ = ∏ b, ∑ x ∈ Tb b, t x ^ nb b :=
        (Finset.prod_univ_sum Tb (fun b x => t x ^ nb b)).symm
    _ ≤ ∏ b, c ^ (nb b - 1) :=
        Finset.prod_le_prod₀ (fun b _ => Finset.sum_nonneg fun x _ => pow_nonneg (ht0 x) _)
          fun b _ => hfac b
    _ = c ^ ∑ b, (nb b - 1) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ c ^ (Fintype.card ι - Fintype.card β) := pow_le_pow_of_le_one hc0 hc1 hexp

/-- The labelling bound behind `sum_prod_abs_card_image_le`, for a bound `c ≤ 1`.  The
multi-indices `v : ι → κ` with `#(image v) ≤ s` are `v = w ∘ φ` for a labelling `φ : ι → Fin s`
and a value assignment `w` (default value off the range of `φ`); for fixed `φ` the weight is a
product of the one-letter sums `∑_x t_x^{n_b} ≤ c^{n_b - 1}` (`t ≤ c`, `∑ t ≤ 1`), so the total
is `≤ s^n c^{n - s}`. -/
private theorem flucIterGain_sum_prod_abs_card_image_le_of_le_one {t : κ → ℝ} {c : ℝ}
    {A : Finset κ} (hw : BoundedWeight t c A) (hc1 : c ≤ 1) {s n : ℕ} (hsn : s ≤ n)
    (hcard : Fintype.card ι = n) :
    ∑ v ∈ (Finset.univ : Finset (ι → κ)).filter
        (fun v => ((Finset.univ : Finset ι).image v).card ≤ s), ∏ i, |t (v i)|
      ≤ c ^ (n - s) * (s : ℝ) ^ n := by
  classical
  have hc0 := hw.nonneg_c
  have htc : ∀ x, t x ≤ c := fun x => by
    by_cases hx : x ∈ A
    · exact hw.le x hx
    · rw [hw.not_mem x hx]; exact hc0
  have habs : ∀ v : ι → κ, ∏ i, |t (v i)| = ∏ i, t (v i) := fun v =>
    Finset.prod_congr rfl fun i _ => abs_of_nonneg (hw.nonneg _)
  simp_rw [habs]
  have hrhs : 0 ≤ c ^ (n - s) * (s : ℝ) ^ n := by positivity
  have hnn : ∀ v : ι → κ, 0 ≤ ∏ i, t (v i) := fun v =>
    Finset.prod_nonneg fun i _ => hw.nonneg _
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · rcases isEmpty_or_nonempty ι with hι | hι
    · have hn0 : n = 0 := by rw [← hcard]; exact Fintype.card_eq_zero
      have hs0 : s = 0 := by omega
      subst hn0 hs0
      calc _ ≤ ∑ v : ι → κ, ∏ i, t (v i) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun v _ _ => hnn v
        _ = 1 := by simp
        _ ≤ _ := by simp
    · have : (Finset.univ : Finset (ι → κ)) = ∅ := Finset.univ_eq_empty
      rw [this]
      simpa using hrhs
  · obtain x₀ := Classical.arbitrary κ
    set T : (ι → Fin s) → Finset (Fin s → κ) := fun φ => Fintype.piFinset
      (fun b : Fin s => if ∃ i, φ i = b then (Finset.univ : Finset κ) else {x₀}) with hT
    set Ω : Finset (Σ _ : ι → Fin s, Fin s → κ) :=
      (Finset.univ : Finset (ι → Fin s)).sigma T with hΩ
    set g : (Σ _ : ι → Fin s, Fin s → κ) → (ι → κ) := fun x i => x.2 (x.1 i) with hg
    set F : Finset (ι → κ) := (Finset.univ : Finset (ι → κ)).filter
      (fun v => ((Finset.univ : Finset ι).image v).card ≤ s) with hF
    have hcover : F ⊆ Ω.image g := by
      intro v hv
      have hvs : ((Finset.univ : Finset ι).image v).card ≤ s := (Finset.mem_filter.1 hv).2
      set I : Finset κ := (Finset.univ : Finset ι).image v with hI
      obtain ⟨e⟩ : Nonempty (↥I ↪ Fin s) :=
        Function.Embedding.nonempty_of_card_le (by simpa using hvs)
      set φ : ι → Fin s := fun i => e ⟨v i, Finset.mem_image_of_mem v (Finset.mem_univ i)⟩
        with hφ
      set w : Fin s → κ := fun b =>
        if h : ∃ i, φ i = b then v (Classical.choose h) else x₀ with hw'
      have hwφ : ∀ i, w (φ i) = v i := by
        intro i
        have h : ∃ j, φ j = φ i := ⟨i, rfl⟩
        have hc := Classical.choose_spec h
        simp only [hw', h, ↓reduceDIte]
        have := e.injective hc
        exact congrArg Subtype.val this
      refine Finset.mem_image.2 ⟨⟨φ, w⟩, ?_, funext hwφ⟩
      refine Finset.mem_sigma.2 ⟨Finset.mem_univ _, ?_⟩
      refine Fintype.mem_piFinset.2 fun b => ?_
      by_cases h : ∃ i, φ i = b
      · rw [ite_eq_left h]; exact Finset.mem_univ _
      · rw [ite_eq_right h]
        simp [hw', h]
    calc ∑ v ∈ F, ∏ i, t (v i)
        ≤ ∑ v ∈ Ω.image g, ∏ i, t (v i) :=
          Finset.sum_le_sum_of_subset_of_nonneg hcover fun v _ _ => hnn v
      _ ≤ ∑ x ∈ Ω, ∏ i, t (g x i) :=
          Finset.sum_image_le_of_nonneg fun v _ => hnn v
      _ = ∑ φ : ι → Fin s, ∑ w ∈ T φ, ∏ i, t (w (φ i)) := by
          rw [hΩ, Finset.sum_sigma]
      _ ≤ ∑ _φ : ι → Fin s, c ^ (n - s) := by
          refine Finset.sum_le_sum fun φ _ => ?_
          have := flucIterGain_sum_comp_le hc0 hc1 hw.nonneg htc hw.sum_le x₀ φ
          rwa [hcard, Fintype.card_fin] at this
      _ = c ^ (n - s) * (s : ℝ) ^ n := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hcard,
            nsmul_eq_mul]
          push_cast
          ring

/-- **The weight of the multi-indices with at most `s` distinct values** (RBM2D `FlucIter:966`,
bounded weight, DECISIONS §30).  Proved by the labelling argument
(`flucIterGain_sum_prod_abs_card_image_le_of_le_one`) at the bound `min c 1`: a bounded weight
satisfies `t ≤ ∑ t ≤ 1`, and `(min c 1)^{n-s} ≤ c^{n-s}`.  Only `0 ≤ t ≤ c` and `∑ t ≤ 1` enter:
neither `t = c` on the support nor the mass bound `c · #A ≤ 1` of the uniform weight is used (it
fails for the row `j ↦ S_{ij}`, where `c · #A = 2d + 1`); `hs` is kept from RBM2D's signature. -/
theorem sum_prod_abs_card_image_le {t : κ → ℝ} {c : ℝ} {A : Finset κ}
    (hw : BoundedWeight t c A) {s n : ℕ} (_hs : s ≤ A.card) (hsn : s ≤ n)
    (hcard : Fintype.card ι = n) :
    ∑ v ∈ (Finset.univ : Finset (ι → κ)).filter
        (fun v => ((Finset.univ : Finset ι).image v).card ≤ s), ∏ i, |t (v i)|
      ≤ c ^ (n - s) * (s : ℝ) ^ n := by
  have ht1 : ∀ k, t k ≤ 1 := fun k =>
    le_trans (Finset.single_le_sum (fun j _ => hw.nonneg j) (Finset.mem_univ k)) hw.sum_le
  have hw' : BoundedWeight t (min c 1) A :=
    { nonneg_c := le_min hw.nonneg_c zero_le_one
      nonneg := hw.nonneg
      le := fun k hk => le_min (hw.le k hk) (ht1 k)
      not_mem := hw.not_mem
      sum_le := hw.sum_le }
  refine le_trans
    (flucIterGain_sum_prod_abs_card_image_le_of_le_one hw' (min_le_right c 1) hsn hcard) ?_
  have hm0 : 0 ≤ min c 1 := le_min hw.nonneg_c zero_le_one
  gcongr
  exact min_le_left c 1

/-- **The stratified sum.**  If every multi-index `v` satisfies the iterated bound
`f v ≤ (K ρ)^{#lone slots} · B^n`, then the weighted sum over all multi-indices is at most
`(n + 1) n^n (K ρ B)^n`: the gain `ρ` is paid `#lone` times by the iteration and `n - #lone`
times by the counting.  The constant depends only on `n = 2p`. -/
theorem sum_weighted_le {t : κ → ℝ} {c : ℝ} {A : Finset κ} (hw : BoundedWeight t c A)
    {n : ℕ} (hcard : Fintype.card ι = n) (hn : n ≤ A.card)
    {ρ B K : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hK : 1 ≤ K) (hB : 0 ≤ B)
    (hcρ : c ≤ ρ ^ 2) {f : (ι → κ) → ℝ}
    (hf : ∀ v, f v ≤ K ^ (loneSlots v).card * ρ ^ (loneSlots v).card * B ^ n) :
    ∑ v : ι → κ, (∏ i, |t (v i)|) * f v
      ≤ ((n : ℝ) + 1) * (n : ℝ) ^ n * (K * ρ * B) ^ n := by
  classical
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK
  have hmaps : ∀ v ∈ (Finset.univ : Finset (ι → κ)),
      (loneSlots v).card ∈ Finset.range (n + 1) := by
    intro v _
    refine Finset.mem_range.2 ?_
    have := Finset.card_le_card (Finset.subset_univ (loneSlots v))
    rw [Finset.card_univ, hcard] at this
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    fun v => (∏ i, |t (v i)|) * f v]
  -- each stratum
  have hstrat : ∀ a ∈ Finset.range (n + 1),
      ∑ v ∈ (Finset.univ : Finset (ι → κ)).filter (fun v => (loneSlots v).card = a),
          (∏ i, |t (v i)|) * f v
        ≤ (n : ℝ) ^ n * (K * ρ * B) ^ n := by
    intro a ha
    have han : a ≤ n := by have := Finset.mem_range.1 ha; omega
    set sa : ℕ := (n + a) / 2 with hsa
    have hsan : sa ≤ n := by omega
    have hsub : (Finset.univ : Finset (ι → κ)).filter (fun v => (loneSlots v).card = a)
        ⊆ (Finset.univ : Finset (ι → κ)).filter
            (fun v => ((Finset.univ : Finset ι).image v).card ≤ sa) := by
      intro v hv
      obtain ⟨-, hva⟩ := Finset.mem_filter.1 hv
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      have h1 := two_mul_card_image_le_add_card_loneSlots v
      rw [hcard, hva] at h1
      omega
    have hbound : ∀ v ∈ (Finset.univ : Finset (ι → κ)).filter
        (fun v => (loneSlots v).card = a),
        (∏ i, |t (v i)|) * f v ≤ (∏ i, |t (v i)|) * (K ^ a * ρ ^ a * B ^ n) := by
      intro v hv
      obtain ⟨-, hva⟩ := Finset.mem_filter.1 hv
      refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun i _ => abs_nonneg _)
      have := hf v
      rwa [hva] at this
    have hwsum : ∑ v ∈ (Finset.univ : Finset (ι → κ)).filter
        (fun v => (loneSlots v).card = a), ∏ i, |t (v i)|
        ≤ c ^ (n - sa) * (sa : ℝ) ^ n := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) ?_
      · exact fun v _ _ => Finset.prod_nonneg fun i _ => abs_nonneg _
      · exact sum_prod_abs_card_image_le hw (le_trans hsan hn) hsan hcard
    -- `c^(n - sa) ≤ ρ^(n - a)`
    have hcpow : c ^ (n - sa) ≤ ρ ^ (n - a) := by
      have h1 : c ^ (n - sa) ≤ (ρ ^ 2) ^ (n - sa) :=
        pow_le_pow_left₀ hw.nonneg_c hcρ _
      have h2 : (ρ ^ 2) ^ (n - sa) = ρ ^ (2 * (n - sa)) := by rw [← pow_mul]
      have h3 : n - a ≤ 2 * (n - sa) := by omega
      have h4 : ρ ^ (2 * (n - sa)) ≤ ρ ^ (n - a) := pow_le_pow_of_le_one hρ0 hρ1 h3
      calc c ^ (n - sa) ≤ (ρ ^ 2) ^ (n - sa) := h1
        _ = ρ ^ (2 * (n - sa)) := h2
        _ ≤ ρ ^ (n - a) := h4
    have hsan' : (sa : ℝ) ^ n ≤ (n : ℝ) ^ n :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hsan) _
    calc ∑ v ∈ (Finset.univ : Finset (ι → κ)).filter (fun v => (loneSlots v).card = a),
          (∏ i, |t (v i)|) * f v
        ≤ ∑ v ∈ (Finset.univ : Finset (ι → κ)).filter (fun v => (loneSlots v).card = a),
            (∏ i, |t (v i)|) * (K ^ a * ρ ^ a * B ^ n) := Finset.sum_le_sum hbound
      _ = (∑ v ∈ (Finset.univ : Finset (ι → κ)).filter (fun v => (loneSlots v).card = a),
            ∏ i, |t (v i)|) * (K ^ a * ρ ^ a * B ^ n) := by rw [Finset.sum_mul]
      _ ≤ (c ^ (n - sa) * (sa : ℝ) ^ n) * (K ^ a * ρ ^ a * B ^ n) := by
          refine mul_le_mul_of_nonneg_right hwsum (by positivity)
      _ ≤ (ρ ^ (n - a) * (n : ℝ) ^ n) * (K ^ n * ρ ^ a * B ^ n) := by
          have hKa : K ^ a ≤ K ^ n := pow_le_pow_right₀ hK han
          have h5 : c ^ (n - sa) * (sa : ℝ) ^ n ≤ ρ ^ (n - a) * (n : ℝ) ^ n := by
            refine mul_le_mul hcpow hsan' (by positivity) (by positivity)
          refine mul_le_mul h5 ?_ (by positivity) (by positivity)
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKa (by positivity)) ?_
          positivity
      _ = (n : ℝ) ^ n * (K * ρ * B) ^ n := by
          have hrho : ρ ^ (n - a) * ρ ^ a = ρ ^ n := by
            rw [← pow_add, Nat.sub_add_cancel han]
          rw [mul_pow, mul_pow, ← hrho]
          ring
  calc ∑ a ∈ Finset.range (n + 1),
        ∑ v ∈ (Finset.univ : Finset (ι → κ)).filter (fun v => (loneSlots v).card = a),
          (∏ i, |t (v i)|) * f v
      ≤ ∑ _a ∈ Finset.range (n + 1), (n : ℝ) ^ n * (K * ρ * B) ^ n :=
        Finset.sum_le_sum hstrat
    _ = ((n : ℝ) + 1) * ((n : ℝ) ^ n * (K * ρ * B) ^ n) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ = ((n : ℝ) + 1) * (n : ℝ) ^ n * (K * ρ * B) ^ n := by ring

end Strata

section Slice2

variable {d : ℕ} {sz : Sizes d} {n : ℕ}

/-! ### The moment bound

Putting the three pieces together: the expansion of `E|∑_k t_k Z_k|^{2p}` into multi-indices
(`prod_epsHom_sum_eq`, G4.1), the iterated vanishing lemma applied to each multi-index with its
own set of lone slots, and the stratified weight sum. -/

section Assemble

variable {E t : ℝ} {p : ℕ}

theorem bddMeas_epsHom_flucDiag (hE : |E| < 2) (ht : t < 1) (u : ℝ) (p : ℕ)
    (i : Fin p ⊕ Fin p) (k : Idx d (sz.L n) (sz.W n)) :
    BddMeas sz fun ω => epsHom p i (flucDiag sz n u (zt E t) (mE E) k ω) := by
  obtain ⟨C, hC⟩ := (bddMeas_flucDiag hE ht u k).bdd
  exact ⟨(measurable_epsHom p i).comp (bddMeas_flucDiag hE ht u k).meas, C,
    fun ω => by rw [norm_epsHom]; exact hC ω⟩

end Assemble

/-! ### The length-graded iteration

The words the iteration builds carry one letter per pivot, the pivots are lone slots, so the
words have length at most `#ι = 2p`; the induction invariant `OpsOkOut` already *says* so
(`OpsOkOut.length_le`), and no extra length bookkeeping has to be threaded through the
iteration.  The gain hypothesis `hgain` below is therefore only asked for words of length
`≤ #ι`. -/

section GradedWords

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **The induction invariant bounds the length.**  A word admissible outside `R` uses
pairwise distinct rows, each the row of a slot outside `R`; the slots realizing them are
therefore distinct, so the word has at most `#ι - #R` letters.  In particular a word arising in
`norm_integral_prod_applyOps_le_graded` never has more than `#ι` letters (`#ι = 2p` at
`ι = Fin p ⊕ Fin p`), which is why the gain interface only ever needs to hold up to that length. -/
theorem OpsOkOut.length_le {k : ι → Idx d (sz.L n) (sz.W n)} {i : ι} {R : Finset ι}
    {l : List (Bool × Idx d (sz.L n) (sz.W n))} (h : OpsOkOut k i R l) :
    l.length + R.card ≤ Fintype.card ι := by
  classical
  have hsub : (l.map Prod.snd).toFinset ⊆ (Finset.univ \ R).image k := by
    intro x hx
    rw [List.mem_toFinset] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨⟨j, hjR, hxj⟩, _⟩ := h.2 y hy
    exact Finset.mem_image.2 ⟨j, Finset.mem_sdiff.2 ⟨Finset.mem_univ j, hjR⟩, hxj.symm⟩
  have h1 : (l.map Prod.snd).toFinset.card = l.length := by
    rw [List.toFinset_card_of_nodup h.1, List.length_map]
  have h2 : ((Finset.univ \ R).image k).card ≤ (Finset.univ \ R).card := Finset.card_image_le
  have h3 : (Finset.univ \ R : Finset ι).card = Fintype.card ι - R.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ R), Finset.card_univ]
  have h4 := Finset.card_le_card hsub
  have hR : R.card ≤ Fintype.card ι := Finset.card_le_univ R
  omega

end GradedWords

/-! #### The iteration, against the graded interface -/

section GradedIterate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **The iteration, with the gain assumed only for short words.**  By induction on the number
`r` of pivots still to perform: if every row `k i₀` (`i₀ ∈ R`) is lone and every word is
admissible outside `R`, then
`‖∫ ∏_i ℓ_i Q_{k i} X_i‖ ≤ (2 max(1,ρ))^{(#ι-1) r} ρ^r · B^{#ι} ρ^{∑_i numQ ℓ_i}`.  The gain
hypothesis is restricted to words of length at most `#ι`, and that restriction is discharged
where the hypothesis is used — at the bottom of the induction — from the invariant `OpsOkOut`
itself (`OpsOkOut.length_le`). -/
theorem norm_integral_prod_applyOps_le_graded {k : ι → Idx d (sz.L n) (sz.W n)}
    {X : ι → Sizes.SeqΩ sz → ℂ} (hX : ∀ i, BddMeas sz (X i)) (hXd : ∀ i, FinDep sz (X i))
    {B ρ : ℝ} (hB : 0 ≤ B) (hρ : 0 ≤ ρ)
    (hgain : ∀ L : ι → List (Bool × Idx d (sz.L n) (sz.W n)), (∀ i, OpsOk k i (L i)) →
      (∀ i, (L i).length ≤ Fintype.card ι) →
      ∫ ω, ∏ i, ‖applyOps sz n (L i) (qRow sz n (k i) (X i)) ω‖ ∂(Sizes.seqP sz)
        ≤ B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i)) :
    ∀ (r : ℕ) (R : Finset ι) (L : ι → List (Bool × Idx d (sz.L n) (sz.W n))), R.card = r →
      (∀ i₀ ∈ R, ∀ j, j ≠ i₀ → k j ≠ k i₀) →
      (∀ i, OpsOkOut k i R (L i)) →
      ‖∫ ω, ∏ i, applyOps sz n (L i) (qRow sz n (k i) (X i)) ω ∂(Sizes.seqP sz)‖
        ≤ (2 * max 1 ρ) ^ ((Fintype.card ι - 1) * r) * ρ ^ r
          * (B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i)) := by
  classical
  intro r
  induction r with
  | zero =>
      intro R L _ _ hL
      simp only [Nat.mul_zero, pow_zero, one_mul]
      refine le_trans (norm_integral_le_integral_norm _) ?_
      refine le_trans (le_of_eq ?_)
        (hgain L (fun i => (hL i).opsOk)
          (fun i => le_trans (Nat.le_add_right _ _) (hL i).length_le))
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => norm_prod _ _)
  | succ r ih =>
      intro R L hR hlone hL
      obtain ⟨i₀, hi₀⟩ : R.Nonempty := Finset.card_pos.1 (by omega)
      have hFb : ∀ i, BddMeas sz (applyOps sz n (L i) (qRow sz n (k i) (X i))) :=
        fun i => ((hX i).qRow (k i)).applyOps (L i)
      have hFd : ∀ i, FinDep sz (applyOps sz n (L i) (qRow sz n (k i) (X i))) :=
        fun i => finDep_applyOps (L i) (finDep_qRow (k i) (hXd i))
      have h0 : condRow sz n (k i₀) (applyOps sz n (L i₀) (qRow sz n (k i₀) (X i₀))) = 0 :=
        condRow_applyOps_qRow sz n (k i₀) (L i₀) (hX i₀)
      have htcard : (Finset.univ.erase i₀).card = Fintype.card ι - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ]
      have hM1 : (1 : ℝ) ≤ max 1 ρ := le_max_left _ _
      have hM0 : (0 : ℝ) ≤ max 1 ρ := le_trans zero_le_one hM1
      have hA0 : (0 : ℝ) ≤ (2 * max 1 ρ) ^ ((Fintype.card ι - 1) * r) * ρ ^ r
          * B ^ Fintype.card ι := by positivity
      have hexp : ∫ ω, ∏ i, applyOps sz n (L i) (qRow sz n (k i) (X i)) ω ∂(Sizes.seqP sz)
          = ∑ S ∈ (Finset.univ.erase i₀).powerset,
              ∫ ω, ∏ i, pivotFam sz n (k i₀) i₀ S
                (fun j => applyOps sz n (L j) (qRow sz n (k j) (X j))) i ω ∂(Sizes.seqP sz) := by
        rw [← integral_finsetSum _ fun S _ =>
          (bddMeas_prod _ fun i _ => bddMeas_pivotFam sz n (k i₀) i₀ S hFb i).integrable]
        exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
          prod_eq_sum_pivotFam sz n (k i₀) i₀
            (fun j => applyOps sz n (L j) (qRow sz n (k j) (X j))) ω)
      have hterm : ∀ S ∈ (Finset.univ.erase i₀).powerset,
          ‖∫ ω, ∏ i, pivotFam sz n (k i₀) i₀ S
              (fun j => applyOps sz n (L j) (qRow sz n (k j) (X j))) i ω ∂(Sizes.seqP sz)‖
            ≤ ((2 * max 1 ρ) ^ ((Fintype.card ι - 1) * r) * ρ ^ r * B ^ Fintype.card ι)
                * ρ ^ (∑ i, numQ (L i)) * (ρ * max 1 ρ ^ (Fintype.card ι - 1)) := by
        intro S hSmem
        have hSt : S ⊆ Finset.univ.erase i₀ := Finset.mem_powerset.1 hSmem
        by_cases hSe : S = ∅
        · subst hSe
          rw [integral_prod_pivotFam_empty sz n hFb hFd h0, norm_zero]
          positivity
        · have hc1 : 1 ≤ S.card := Finset.card_pos.2 (Finset.nonempty_of_ne_empty hSe)
          have hc2 : S.card ≤ Fintype.card ι - 1 := htcard ▸ Finset.card_le_card hSt
          have hrw : ∀ ω : Sizes.SeqΩ sz, ∏ i, pivotFam sz n (k i₀) i₀ S
              (fun j => applyOps sz n (L j) (qRow sz n (k j) (X j))) i ω
              = ∏ i, applyOps sz n (pivotWords k i₀ S L i) (qRow sz n (k i) (X i)) ω :=
            fun ω => Finset.prod_congr rfl fun i _ => by
              rw [pivotFam_eq_applyOps sz n (X := X) L i]
          have hL' : ∀ i, OpsOkOut k i (R.erase i₀) (pivotWords k i₀ S L i) := by
            intro i
            by_cases h : i = i₀
            · have hw : pivotWords k i₀ S L i = L i₀ := by simp [pivotWords, h]
              rw [hw, h]
              exact (hL i₀).mono (Finset.erase_subset _ _)
            · by_cases hi : i ∈ S
              · have hw : pivotWords k i₀ S L i = (true, k i₀) :: L i := by
                  simp [pivotWords, h, hi]
                rw [hw]; exact (hL i).cons (hlone i₀ hi₀) hi₀ h true
              · have hw : pivotWords k i₀ S L i = (false, k i₀) :: L i := by
                  simp [pivotWords, h, hi]
                rw [hw]; exact (hL i).cons (hlone i₀ hi₀) hi₀ h false
          have hstep := ih (R.erase i₀) (pivotWords k i₀ S L)
            (by rw [Finset.card_erase_of_mem hi₀, hR]; omega)
            (fun i₁ hi₁ => hlone i₁ (Finset.mem_of_mem_erase hi₁)) hL'
          rw [sum_numQ_pivotWords hSt L] at hstep
          rw [integral_congr_ae (Filter.Eventually.of_forall hrw)]
          refine le_trans hstep ?_
          have hpow : ρ ^ S.card ≤ ρ * max 1 ρ ^ (Fintype.card ι - 1) := by
            obtain ⟨c, hc⟩ : ∃ c, S.card = c + 1 := ⟨S.card - 1, by omega⟩
            rw [hc, pow_succ]
            have h1 : ρ ^ c ≤ max 1 ρ ^ c := pow_le_pow_left₀ hρ (le_max_right 1 ρ) c
            have h2 : max 1 ρ ^ c ≤ max 1 ρ ^ (Fintype.card ι - 1) :=
              pow_le_pow_right₀ hM1 (by omega)
            calc ρ ^ c * ρ ≤ max 1 ρ ^ (Fintype.card ι - 1) * ρ := by
                  exact mul_le_mul_of_nonneg_right (le_trans h1 h2) hρ
              _ = ρ * max 1 ρ ^ (Fintype.card ι - 1) := by ring
          have hexpand : (2 * max 1 ρ) ^ ((Fintype.card ι - 1) * r) * ρ ^ r
              * (B ^ Fintype.card ι * ρ ^ ((∑ i, numQ (L i)) + S.card))
              = ((2 * max 1 ρ) ^ ((Fintype.card ι - 1) * r) * ρ ^ r * B ^ Fintype.card ι)
                * ρ ^ (∑ i, numQ (L i)) * ρ ^ S.card := by
            rw [pow_add]; ring
          rw [hexpand]
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
      calc ‖∫ ω, ∏ i, applyOps sz n (L i) (qRow sz n (k i) (X i)) ω ∂(Sizes.seqP sz)‖
          = ‖∑ S ∈ (Finset.univ.erase i₀).powerset,
              ∫ ω, ∏ i, pivotFam sz n (k i₀) i₀ S
                (fun j => applyOps sz n (L j) (qRow sz n (k j) (X j))) i ω ∂(Sizes.seqP sz)‖ := by
            rw [hexp]
        _ ≤ ∑ S ∈ (Finset.univ.erase i₀).powerset,
              ‖∫ ω, ∏ i, pivotFam sz n (k i₀) i₀ S
                (fun j => applyOps sz n (L j) (qRow sz n (k j) (X j))) i ω ∂(Sizes.seqP sz)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _S ∈ (Finset.univ.erase i₀).powerset,
              (((2 * max 1 ρ) ^ ((Fintype.card ι - 1) * r) * ρ ^ r * B ^ Fintype.card ι)
                * ρ ^ (∑ i, numQ (L i)) * (ρ * max 1 ρ ^ (Fintype.card ι - 1))) :=
            Finset.sum_le_sum hterm
        _ = (2 : ℝ) ^ (Fintype.card ι - 1)
              * (((2 * max 1 ρ) ^ ((Fintype.card ι - 1) * r) * ρ ^ r * B ^ Fintype.card ι)
                * ρ ^ (∑ i, numQ (L i)) * (ρ * max 1 ρ ^ (Fintype.card ι - 1))) := by
            rw [Finset.sum_const, Finset.card_powerset, htcard, nsmul_eq_mul]
            norm_num
        _ = (2 * max 1 ρ) ^ ((Fintype.card ι - 1) * (r + 1)) * ρ ^ (r + 1)
              * (B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i)) := by
            rw [Nat.mul_succ, pow_add, mul_pow, pow_succ]
            ring

omit [DecidableEq ι] in
/-- **The iteration from empty words**: `norm_integral_prod_applyOps_le_graded` with every word
empty (`L i = []`) and `r = #R`. -/
theorem norm_integral_prod_qRow_le_graded {k : ι → Idx d (sz.L n) (sz.W n)} (R : Finset ι)
    (hlone : ∀ i₀ ∈ R, ∀ j, j ≠ i₀ → k j ≠ k i₀)
    {X : ι → Sizes.SeqΩ sz → ℂ} (hX : ∀ i, BddMeas sz (X i)) (hXd : ∀ i, FinDep sz (X i))
    {B ρ : ℝ} (hB : 0 ≤ B) (hρ : 0 ≤ ρ)
    (hgain : ∀ L : ι → List (Bool × Idx d (sz.L n) (sz.W n)), (∀ i, OpsOk k i (L i)) →
      (∀ i, (L i).length ≤ Fintype.card ι) →
      ∫ ω, ∏ i, ‖applyOps sz n (L i) (qRow sz n (k i) (X i)) ω‖ ∂(Sizes.seqP sz)
        ≤ B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i)) :
    ‖∫ ω, ∏ i, qRow sz n (k i) (X i) ω ∂(Sizes.seqP sz)‖
      ≤ (2 * max 1 ρ) ^ ((Fintype.card ι - 1) * R.card) * ρ ^ R.card
        * B ^ Fintype.card ι := by
  classical
  have h := norm_integral_prod_applyOps_le_graded hX hXd hB hρ hgain R.card R (fun _ => [])
    rfl hlone (fun i => opsOkOut_nil k i R)
  simpa only [applyOps_nil, numQ_nil, Finset.sum_const, smul_eq_mul, mul_zero, pow_zero,
    mul_one] using h

end GradedIterate

/-! ### The gain interface and the moment bound

`FlucGainUpTo'` asks for the higher-order minor expansion for words of length `≤ M` **and** for
at most `K` slots.  The second budget is not cosmetic: without it, `ι = Fin j`, every word empty
and every pivot equal to a single `k` are admissible, the gain exponent is `0`, and the interface
would read `∫ ‖Z_k‖^j ≤ B^j` for **every** `j`, i.e. an `L^∞` bound `‖Z_k‖ ≤ B`.  The `2p`-th
moment expansion instantiates the interface at `ι = Fin p ⊕ Fin p` and nowhere else, so
`#ι = 2p`, exactly as `OpsOkOut.length_le` makes the words have length `≤ 2p`; both budgets are
`2p` and the consumers ask for `M = K = 2p`. -/

section Budget

/-- **The gain interface with both budgets.**  `M` budgets the length of the words, `K` the
number of slots `#ι`; the `2p`-th moment expansion has `M = K = 2p`.  The words `L i` use
pairwise distinct rows, none of them the row `k i` of the slot they sit on. -/
def FlucGainUpTo' (sz : Sizes d) (n : ℕ) (u : ℝ) (z m : ℂ) (B ρ : ℝ) (M K : ℕ) : Prop :=
  0 ≤ B ∧ 0 ≤ ρ ∧
    ∀ (ι : Type) [Fintype ι] (k : ι → Idx d (sz.L n) (sz.W n))
      (L : ι → List (Bool × Idx d (sz.L n) (sz.W n))),
      (∀ i, ((L i).map Prod.snd).Nodup) → (∀ i, ∀ x ∈ L i, x.2 ≠ k i) →
      (∀ i, (L i).length ≤ M) → Fintype.card ι ≤ K →
      ∫ ω, ∏ i, ‖applyOps sz n (L i) (flucDiag sz n u z m (k i)) ω‖ ∂(Sizes.seqP sz)
        ≤ B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i)

theorem FlucGainUpTo'.B_nonneg {u : ℝ} {z m : ℂ} {B ρ : ℝ} {M K : ℕ}
    (h : FlucGainUpTo' sz n u z m B ρ M K) : 0 ≤ B := h.1

theorem FlucGainUpTo'.rho_nonneg {u : ℝ} {z m : ℂ} {B ρ : ℝ} {M K : ℕ}
    (h : FlucGainUpTo' sz n u z m B ρ M K) : 0 ≤ ρ := h.2.1

theorem FlucGainUpTo'.gain {u : ℝ} {z m : ℂ} {B ρ : ℝ} {M K : ℕ}
    (h : FlucGainUpTo' sz n u z m B ρ M K) (ι : Type) [Fintype ι] (k : ι → Idx d (sz.L n) (sz.W n))
    (L : ι → List (Bool × Idx d (sz.L n) (sz.W n))) (h1 : ∀ i, ((L i).map Prod.snd).Nodup)
    (h2 : ∀ i, ∀ x ∈ L i, x.2 ≠ k i) (h3 : ∀ i, (L i).length ≤ M)
    (h4 : Fintype.card ι ≤ K) :
    ∫ ω, ∏ i, ‖applyOps sz n (L i) (flucDiag sz n u z m (k i)) ω‖ ∂(Sizes.seqP sz)
      ≤ B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i) := h.2.2 ι k L h1 h2 h3 h4

/-! #### The consumers, against the doubly budgeted interface

Each is the graded statement with `#ι ≤ K` in the interface and `2 * p ≤ K` in the hypotheses;
the budget is discharged at the single point where the interface is used, from
`Fintype.card (Fin p ⊕ Fin p) = 2 * p`. -/

section BudgetFluc

variable {E t : ℝ} {p : ℕ}

/-- **The iteration at order `2p`.**  For `v : (Fin p ⊕ Fin p) → Idx` and a set `R` of lone slots
of `v`,
`‖∫ ∏_i ε_i Z_{v i}‖ ≤ (2 max(1,ρ))^{(2p-1) #R} ρ^{#R} B^{2p}`, where `ε_i` is the identity
(`i = inl _`) or complex conjugation (`i = inr _`). -/
theorem norm_integral_prod_epsHom_flucDiag_le_budget (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    {B ρ : ℝ} {M K : ℕ} (hg : FlucGainUpTo' sz n u (zt E t) (mE E) B ρ M K)
    (hM : 2 * p ≤ M) (hK : 2 * p ≤ K)
    (v : (Fin p ⊕ Fin p) → Idx d (sz.L n) (sz.W n)) (R : Finset (Fin p ⊕ Fin p))
    (hlone : ∀ i₀ ∈ R, ∀ j, j ≠ i₀ → v j ≠ v i₀) :
    ‖∫ ω, ∏ i, epsHom p i (flucDiag sz n u (zt E t) (mE E) (v i) ω)
        ∂(Sizes.seqP sz)‖
      ≤ (2 * max 1 ρ) ^ ((2 * p - 1) * R.card) * ρ ^ R.card * B ^ (2 * p) := by
  classical
  have hcard : Fintype.card (Fin p ⊕ Fin p) = 2 * p := by
    simp [Fintype.card_sum, two_mul]
  set X : (Fin p ⊕ Fin p) → Sizes.SeqΩ sz → ℂ :=
    fun i ω => epsHom p i (greenDiagCentered sz n u (zt E t) (mE E) (v i) ω)
    with hXdef
  have hXb : ∀ i, BddMeas sz (X i) := by
    intro i
    obtain ⟨C, hC⟩ := (bddMeas_greenDiagCentered hE ht u (v i)).bdd
    refine ⟨((measurable_epsHom p i).comp
      (bddMeas_greenDiagCentered (E := E) (t := t) hE ht u (v i)).meas), C, fun ω => ?_⟩
    rw [hXdef]
    simpa only [norm_epsHom] using hC ω
  have hXd : ∀ i, FinDep sz (X i) :=
    fun i => (finDep_greenDiagCentered sz n u (zt E t) (mE E) (v i)).imp
      (fun _ h ω ω' hω => by rw [hXdef]; exact congrArg (epsHom p i) (h ω ω' hω))
  have hq : ∀ i, qRow sz n (v i) (X i)
      = fun ω => epsHom p i (flucDiag sz n u (zt E t) (mE E) (v i) ω) := by
    intro i
    have := applyOps_epsHom sz n p i [] (greenDiagCentered sz n u (zt E t) (mE E) (v i))
    cases i with
    | inl j => simp only [hXdef, epsHom_inl]; rfl
    | inr j =>
        simp only [hXdef, epsHom_inr]
        exact qRow_conj sz n (v (Sum.inr j))
          (greenDiagCentered sz n u (zt E t) (mE E) _)
  have hgain : ∀ L : (Fin p ⊕ Fin p) → List (Bool × Idx d (sz.L n) (sz.W n)),
      (∀ i, OpsOk v i (L i)) →
      (∀ i, (L i).length ≤ Fintype.card (Fin p ⊕ Fin p)) →
      ∫ ω, ∏ i, ‖applyOps sz n (L i) (qRow sz n (v i) (X i)) ω‖ ∂(Sizes.seqP sz)
        ≤ B ^ Fintype.card (Fin p ⊕ Fin p) * ρ ^ ∑ i, numQ (L i) := by
    intro L hL hlen
    have hrw : ∀ ω : Sizes.SeqΩ sz, ∏ i, ‖applyOps sz n (L i) (qRow sz n (v i) (X i)) ω‖
        = ∏ i, ‖applyOps sz n (L i)
            (flucDiag sz n u (zt E t) (mE E) (v i)) ω‖ := by
      intro ω
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hq i, applyOps_epsHom sz n p i (L i) (flucDiag sz n u (zt E t) (mE E) (v i)),
        norm_epsHom]
    rw [integral_congr_ae (Filter.Eventually.of_forall hrw)]
    exact hg.gain (Fin p ⊕ Fin p) v L (fun i => (hL i).1) (fun i => (hL i).2)
      (fun i => le_trans (hlen i) (by rw [hcard]; exact hM)) (by rw [hcard]; exact hK)
  have h := norm_integral_prod_qRow_le_graded (k := v) R hlone hXb hXd hg.B_nonneg
    hg.rho_nonneg hgain
  rw [hcard] at h
  simpa only [hq] using h

/-- **The moment bound for the fluctuation average.**  For a bounded weight `T` (`0 ≤ T ≤ c ≤ ρ²`
on a set `A` with `2p ≤ #A`, `∑ T ≤ 1`; DECISIONS §30) and `ρ ≤ 1`,
`E|∑_k T_k Z_k|^{2p} ≤ (2p+1)(2p)^{2p} (2^{2p-1} ρ B)^{2p}`.  The `2p`-th moment uses the
interface at `#ι = 2p` slots and words of length `≤ 2p`, so `M = K = 2p` suffices. -/
theorem integral_norm_flucAvg_pow_le_iter_budget (hE : |E| < 2) (ht : t < 1) {u : ℝ}
    {B ρ c : ℝ} {M K : ℕ} {A : Finset (Idx d (sz.L n) (sz.W n))} {T : Idx d (sz.L n) (sz.W n) → ℝ}
    (hg : FlucGainUpTo' sz n u (zt E t) (mE E) B ρ M K) (hM : 2 * p ≤ M)
    (hK : 2 * p ≤ K)
    (hρ1 : ρ ≤ 1) (hcρ : c ≤ ρ ^ 2)
    (hw : BoundedWeight T c A) (hp : 2 * p ≤ A.card) :
    ∫ ω, ‖flucAvg sz n u (zt E t) (mE E) T ω‖ ^ (2 * p) ∂(Sizes.seqP sz)
      ≤ ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
        * ((2 : ℝ) ^ (2 * p - 1) * ρ * B) ^ (2 * p) := by
  classical
  have hcardι : Fintype.card (Fin p ⊕ Fin p) = 2 * p := by
    simp [Fintype.card_sum, two_mul]
  have hB := hg.B_nonneg
  have hρ0 := hg.rho_nonneg
  have hbm : ∀ (v : (Fin p ⊕ Fin p) → Idx d (sz.L n) (sz.W n)),
      BddMeas sz fun ω =>
        ∏ i, epsHom p i (flucDiag sz n u (zt E t) (mE E) (v i) ω) :=
    fun v => bddMeas_prod _ fun i _ => bddMeas_epsHom_flucDiag hE ht u p i (v i)
  have hI : ∫ ω, ((‖flucAvg sz n u (zt E t) (mE E) T ω‖ ^ (2 * p) : ℝ) : ℂ)
        ∂(Sizes.seqP sz)
      = ∑ v : (Fin p ⊕ Fin p) → Idx d (sz.L n) (sz.W n), (∏ i, (T (v i) : ℂ))
          * ∫ ω, ∏ i, epsHom p i (flucDiag sz n u (zt E t) (mE E) (v i) ω)
              ∂(Sizes.seqP sz) := by
    have hexp : ∀ ω : Sizes.SeqΩ sz,
        ((‖flucAvg sz n u (zt E t) (mE E) T ω‖ ^ (2 * p) : ℝ) : ℂ)
        = ∑ v : (Fin p ⊕ Fin p) → Idx d (sz.L n) (sz.W n), (∏ i, (T (v i) : ℂ))
            * ∏ i, epsHom p i (flucDiag sz n u (zt E t) (mE E) (v i) ω) :=
      fun ω => prod_epsHom_sum_eq p T fun k => flucDiag sz n u (zt E t) (mE E) k ω
    simp_rw [hexp]
    rw [integral_finsetSum _ fun v _ =>
      ((bddMeas_const sz (∏ i, (T (v i) : ℂ))).mul (hbm v)).integrable]
    exact Finset.sum_congr rfl fun v _ => integral_const_mul _ _
  have hf : ∀ v : (Fin p ⊕ Fin p) → Idx d (sz.L n) (sz.W n),
      ‖∫ ω, ∏ i, epsHom p i (flucDiag sz n u (zt E t) (mE E) (v i) ω)
          ∂(Sizes.seqP sz)‖
        ≤ ((2 : ℝ) ^ (2 * p - 1)) ^ (loneSlots v).card * ρ ^ (loneSlots v).card
          * B ^ (2 * p) := by
    intro v
    have hlone : ∀ i₀ ∈ loneSlots v, ∀ j, j ≠ i₀ → v j ≠ v i₀ :=
      fun i₀ hi₀ => mem_loneSlots.1 hi₀
    have key := norm_integral_prod_epsHom_flucDiag_le_budget hE ht u hg hM hK v
      (loneSlots v) hlone
    rwa [max_eq_left hρ1, mul_one, pow_mul] at key
  have hK1 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * p - 1) := one_le_pow₀ (by norm_num)
  have hsum := sum_weighted_le (ι := Fin p ⊕ Fin p) hw hcardι hp hρ0 hρ1 hK1 hB hcρ hf
  have hofR : (∫ ω, ((‖flucAvg sz n u (zt E t) (mE E) T ω‖ ^ (2 * p) : ℝ) : ℂ)
        ∂(Sizes.seqP sz))
      = ((∫ ω, ‖flucAvg sz n u (zt E t) (mE E) T ω‖ ^ (2 * p)
          ∂(Sizes.seqP sz) : ℝ) : ℂ) :=
    integral_complex_ofReal
  have hreal : ∫ ω, ‖flucAvg sz n u (zt E t) (mE E) T ω‖ ^ (2 * p)
        ∂(Sizes.seqP sz)
      = ‖∫ ω, ((‖flucAvg sz n u (zt E t) (mE E) T ω‖ ^ (2 * p) : ℝ) : ℂ)
          ∂(Sizes.seqP sz)‖ := by
    rw [hofR, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun ω => by positivity)]
  rw [hreal, hI]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ v : (Fin p ⊕ Fin p) → Idx d (sz.L n) (sz.W n),
      ‖(∏ i, (T (v i) : ℂ))
          * ∫ ω, ∏ i, epsHom p i (flucDiag sz n u (zt E t) (mE E) (v i) ω)
              ∂(Sizes.seqP sz)‖
        = (∏ i, |T (v i)|)
          * ‖∫ ω, ∏ i, epsHom p i (flucDiag sz n u (zt E t) (mE E) (v i) ω)
              ∂(Sizes.seqP sz)‖ := by
    intro v
    rw [norm_mul, norm_prod]
    congr 1
    exact Finset.prod_congr rfl fun i _ => by rw [Complex.norm_real, Real.norm_eq_abs]
  simp_rw [hterm]
  exact le_trans hsum (le_of_eq (by push_cast; ring))

end BudgetFluc

end Budget

/-! ### The gain interface is satisfiable

The words of a gain-free instance are bounded crudely, `‖ℓ X‖ ≤ 2^{numQ ℓ} b`
(`norm_applyOps_le`); with `b = 2 (η⁻¹ + 1)` (the envelope of `Z_k`) and `B ρ^q ≥ 2^q b` for the
admissible `q`, the gain interface `FlucGainUpTo'` holds at `(B, ρ)` without any local law.  The
two private lemmas below feed the checks at the end of the file. -/

section Crude

/-- The integral of a product of the norms of words is bounded by the crude pointwise bound. -/
private theorem flucIter_integral_prod_norm_applyOps_le_crude {ι : Type*} [Fintype ι]
    {F : ι → Sizes.SeqΩ sz → ℂ} {b : ℝ} (hF : ∀ i ω, ‖F i ω‖ ≤ b)
    (L : ι → List (Bool × Idx d (sz.L n) (sz.W n))) {B ρ : ℝ}
    (hcrude : ∀ i, 2 ^ numQ (L i) * b ≤ B * ρ ^ numQ (L i)) :
    ∫ ω, ∏ i, ‖applyOps sz n (L i) (F i) ω‖ ∂(Sizes.seqP sz)
      ≤ B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i) := by
  have hpt : ∀ ω : Sizes.SeqΩ sz, ∏ i, ‖applyOps sz n (L i) (F i) ω‖
      ≤ B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i) := by
    intro ω
    calc ∏ i, ‖applyOps sz n (L i) (F i) ω‖ ≤ ∏ i, (B * ρ ^ numQ (L i)) :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ =>
            le_trans (norm_applyOps_le (L i) (hF i) ω) (hcrude i)
      _ = B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
            Finset.prod_pow_eq_pow_sum]
  calc ∫ ω, ∏ i, ‖applyOps sz n (L i) (F i) ω‖ ∂(Sizes.seqP sz)
      ≤ ∫ _ω, B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i) ∂(Sizes.seqP sz) :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun ω => Finset.prod_nonneg fun i _ => norm_nonneg _)
          (integrable_const _) (Filter.Eventually.of_forall hpt)
    _ = B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i) := by simp

/-- **The gain interface holds gain-free.**  If `2^q · 2 (η⁻¹ + 1) ≤ B ρ^q` for every `q ≤ M`,
then `FlucGainUpTo'` holds at `(B, ρ, M, K)` for every `K`. -/
private theorem flucIter_flucGainUpTo'_of_crude {E t : ℝ} (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    {B ρ : ℝ} (hB : 0 ≤ B) (hρ : 0 ≤ ρ) {M K : ℕ}
    (hcrude : ∀ q ≤ M, 2 ^ q * (2 * (((zt E t).im)⁻¹ + 1)) ≤ B * ρ ^ q) :
    FlucGainUpTo' sz n u (zt E t) (mE E) B ρ M K := by
  refine ⟨hB, hρ, fun ι _ k L _ _ hlen _ => ?_⟩
  exact flucIter_integral_prod_norm_applyOps_le_crude
    (F := fun i => flucDiag sz n u (zt E t) (mE E) (k i))
    (b := 2 * (((zt E t).im)⁻¹ + 1))
    (fun i ω => norm_flucDiag_le (norm_greenDiagCentered_le_env hE ht u (k i)) ω) L
    fun i => hcrude _ (le_trans List.countP_le_length (hlen i))

end Crude

end Slice2

/-! ### Compiled nonempty instances at `d = 3`, `L = 3`, `W = 2`, `g = 1/2`

`RBM.Green.FlucIterGainInst.szG` is the size sequence of the numeric check of the preflight
(`d = 3`, `L n = 3`, `W n = 2`, `lam n = 1/2` for every `n`; constant sequences, no limit
statement is claimed at it), at the slice `n = 0`: `N = (W L)^3 = 216` sites, `W^d = 8`.
Energy `E = 0` (`|E| < 2`), time `t = 1/2` (`t < 1`), `u = 1/2`, `z_t = zt 0 (1/2) = i/2`,
`m = mE 0 = i`, `η_t = 1/2`, so `‖Z_k‖ ≤ 2 (η⁻¹ + 1) = 6`.

* The gain interface holds gain-free (`flucIter_flucGainUpTo'_of_crude`) at `(B, ρ, M, K) =
  (96, 1/2, 2, 2)` (`2^q · 6 ≤ 96 · 2^{-q}` for `q ≤ 2`, tight at `q = 2`) and at
  `(96, 1, 4, 4)` (`2^q · 6 ≤ 96` for `q ≤ 4`, tight at `q = 4`).  No local law is used and no
  limit is claimed: `FlucGainUpTo'` is a hypothesis of the consumers.
* The two weights are the true row `j ↦ S_{0j}` of the variance profile (`boundedWeight_svarF`:
  `c = W^{-3} = 1/8`, `#A = (2d + 1) W^d = 56`, `c · #A = 7 > 1`, so it is not a `UniformWeight`)
  and the block average of the block `0` (`c = 1/8`, `#A = W^d = 8`, `c · #A = 1`).  Both satisfy
  `c = 1/8 ≤ ρ² = 1/4` at `ρ = 1/2` and `2p ≤ #A`.
* `integral_norm_flucAvg_pow_le_iter_budget` is applied at `p = 1`, `(96, 1/2)`: budget
  `3 · 4 · (2 · (1/2) · 96)² = 110592` (row and block), and at `p = 2`, `(96, 1)`: budget
  `5 · 4⁴ · (2³ · 96)⁴ = 445302209249280` (row).
* The counting and weight-sum lemmas are applied at the lattice `Idx 3 3 2` (`#ι = 2`) and at
  small finite types; the iteration lemmas at the two distinct sites `(0,0,0)`, `(0,0,1)` of the
  block `0`, as slots `Fin 1 ⊕ Fin 1` resp. `Fin 2`.
There is no external hypothesis. -/

namespace FlucIterGainInst

noncomputable section

/-- The sizes `d = 3`, `L = 3`, `W = 2`, `g = 1/2` (constant sequences). -/
private def szG : Sizes 3 where
  L := fun _ => 3
  W := fun _ => 2
  lam := fun _ => 1 / 2
  three_le_L := fun _ => le_rfl
  W_pos := fun _ => by norm_num

/-- `η_t = Im z_t = 1/2` at `E = 0`, `t = 1/2`. -/
private theorem eta_eq : (zt 0 (1 / 2)).im = 1 / 2 := by
  have hs : Real.sqrt (4 - (0 : ℝ) ^ 2) = 2 := by
    rw [show (4 - (0 : ℝ) ^ 2) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [zt_im, mE_im, hs]
  norm_num

private theorem hE0 : |(0 : ℝ)| < 2 := by norm_num
private theorem ht0 : (1 / 2 : ℝ) < 1 := by norm_num

/-- The gain interface at `(B, ρ, M, K) = (96, 1/2, 2, 2)`, gain-free (tight at `q = 2`).
Private: a public theorem concluding `FlucGainUpTo' …` would make the premise scan treat the
interface as proved (it is proved only gain-free, at crude constants). -/
private theorem flucGainUpTo'_szG_half (u : ℝ) :
    FlucGainUpTo' szG 0 u (zt 0 (1 / 2)) (mE 0) 96 (1 / 2) 2 2 :=
  flucIter_flucGainUpTo'_of_crude (E := 0) (t := 1 / 2) hE0 ht0 u (by norm_num) (by norm_num)
    fun q hq => by
      rw [eta_eq]
      interval_cases q <;> norm_num

/-- The gain interface at `(B, ρ, M, K) = (96, 1, 4, 4)`, gain-free (tight at `q = 4`). Private,
as the previous one. -/
private theorem flucGainUpTo'_szG_one (u : ℝ) :
    FlucGainUpTo' szG 0 u (zt 0 (1 / 2)) (mE 0) 96 1 4 4 :=
  flucIter_flucGainUpTo'_of_crude (E := 0) (t := 1 / 2) hE0 ht0 u (by norm_num) (by norm_num)
    fun q hq => by
      rw [eta_eq]
      interval_cases q <;> norm_num

/-- **Instance of the projections of `FlucGainUpTo'`.** -/
theorem flucGainUpTo'_szG_projections (u : ℝ) : 0 ≤ (96 : ℝ) ∧ 0 ≤ (1 / 2 : ℝ) :=
  ⟨(flucGainUpTo'_szG_half u).B_nonneg, (flucGainUpTo'_szG_half u).rho_nonneg⟩

/-- Two distinct sites of the block `0` of `Z_6^3`. -/
private def siteA : Idx 3 (szG.L 0) (szG.W 0) := ![0, 0, 0]
private def siteB : Idx 3 (szG.L 0) (szG.W 0) := ![0, 0, 1]

private theorem siteB_ne_siteA : siteB ≠ siteA := by decide

/-- The two rows of the iteration checks, indexed by `Fin 2`. -/
private def rowK : Fin 2 → Idx 3 (szG.L 0) (szG.W 0) := ![siteA, siteB]

/-- The gain interface with `M = K = 2` also holds for words of the iteration at `ι = Fin 2`:
instance of `FlucGainUpTo'.gain` with the nonempty word `Q`-free `P_{siteB}` on slot `0`. -/
theorem flucGainUpTo'_szG_gain (u : ℝ) :
    ∫ ω, ∏ i : Fin 2, ‖applyOps szG 0 (![[(false, siteB)], []] i)
        (flucDiag szG 0 u (zt 0 (1 / 2)) (mE 0) (rowK i)) ω‖ ∂(Sizes.seqP szG)
      ≤ 96 ^ Fintype.card (Fin 2) * (1 / 2 : ℝ) ^ ∑ i, numQ (![[(false, siteB)], []] i) := by
  refine (flucGainUpTo'_szG_half u).gain (Fin 2) rowK ![[(false, siteB)], []] ?_ ?_ ?_ ?_
  · intro i; fin_cases i <;> simp
  · intro i x hx
    fin_cases i
    · obtain rfl := List.mem_singleton.1 hx
      exact siteB_ne_siteA
    · exact absurd hx (List.not_mem_nil)
  · intro i; fin_cases i <;> simp
  · simp

/-! #### The counting lemmas -/

/-- The multi-index `v = (0, 0, 1, 2) : Fin 4 → Fin 3`: the value `0` is taken twice, `1` and `2`
once each. -/
private def vCount : Fin 4 → Fin 3 := ![0, 0, 1, 2]

/-- Nondegeneracy of the counting instance: three values, two lone slots (`{2, 3}`). -/
theorem counting_values :
    ((Finset.univ : Finset (Fin 4)).image vCount).card = 3 ∧ (loneSlots vCount).card = 2 := by
  decide

/-- **Instance of `two_mul_card_image_le_add_card_loneSlots`**: `2 · 3 ≤ 4 + 2` (tight). -/
theorem counting_two_mul : 2 * ((Finset.univ : Finset (Fin 4)).image vCount).card
    ≤ Fintype.card (Fin 4) + (loneSlots vCount).card :=
  two_mul_card_image_le_add_card_loneSlots vCount

/-- **Instance of `image_loneSlots_eq`** at `vCount`. -/
theorem counting_image_lone :
    (loneSlots vCount).image vCount
      = ((Finset.univ : Finset (Fin 4)).image vCount).filter
          fun b => ((Finset.univ : Finset (Fin 4)).filter fun i => vCount i = b).card = 1 :=
  image_loneSlots_eq vCount

/-- **Instance of `mem_loneSlots`**: the slot `2` of `vCount` is lone, the slot `0` is not. -/
theorem counting_mem_lone : (2 : Fin 4) ∈ loneSlots vCount ∧ (0 : Fin 4) ∉ loneSlots vCount := by
  decide

/-- **Instance of `card_filter_card_image_le`**: multi-indices `Fin 3 → Fin 3` with at most
`2` values. -/
theorem counting_card_filter :
    ((Fintype.piFinset fun _ : Fin 3 => (Finset.univ : Finset (Fin 3))).filter
        fun v => ((Finset.univ : Finset (Fin 3)).image v).card ≤ 2).card
      ≤ (Finset.univ : Finset (Fin 3)).card ^ 2 * 2 ^ Fintype.card (Fin 3) :=
  card_filter_card_image_le (ι := Fin 3) (Finset.univ : Finset (Fin 3)) 2 (by simp)

/-! #### The weight sum at the two families -/

/-- The row `j ↦ S_{0j}` of the variance profile. -/
private def rowW : Idx 3 (szG.L 0) (szG.W 0) → ℝ :=
  fun j => svarF 3 (szG.L 0) (szG.W 0) (szG.lam 0) 0 j

/-- The support of the row. -/
private def rowA : Finset (Idx 3 (szG.L 0) (szG.W 0)) :=
  (Finset.univ : Finset (Idx 3 (szG.L 0) (szG.W 0))).filter fun j =>
    (split 3 (szG.L 0) (szG.W 0) j).1 - (split 3 (szG.L 0) (szG.W 0) 0).1
      ∈ flucVanish_sbSupport 3 (szG.L 0)

private theorem rowW_bounded :
    BoundedWeight rowW ((((szG.W 0 : ℕ) : ℝ) ^ 3)⁻¹) rowA :=
  boundedWeight_svarF 3 (szG.L 0) (szG.W 0) (szG.three_le_L 0) (szG.lam 0) 0

/-- Nondegeneracy: the row has `(2d + 1) W^d = 56` sites in its support, and
`c · #A = 7 > 1`, so `UniformWeight.mass` fails for it. -/
theorem rowA_card : rowA.card = 56 := by
  rw [rowA, flucVanish_card_svarSupport_eq 3 (szG.L 0) (szG.W 0) (szG.three_le_L 0)]
  norm_num [szG]

/-- **Instance of `sum_prod_abs_card_image_le`** at the true row, `ι = Fin 2`, `n = 2`, `s = 1`:
the weight of the diagonal multi-indices is at most `c^{n-s} s^n = 1/8`. -/
theorem sum_prod_abs_card_image_row :
    ∑ v ∈ (Finset.univ : Finset (Fin 2 → Idx 3 (szG.L 0) (szG.W 0))).filter
        (fun v => ((Finset.univ : Finset (Fin 2)).image v).card ≤ 1), ∏ i, |rowW (v i)|
      ≤ 1 / 8 := by
  refine le_trans (sum_prod_abs_card_image_le (ι := Fin 2) (s := 1) (n := 2) rowW_bounded
    (by rw [rowA_card]; norm_num) (by norm_num) (by simp)) ?_
  norm_num [szG]

/-- **Instance of `sum_weighted_le`** at the true row, `ι = Fin 2` (`n = 2`), `ρ = 1/2`,
`K = B = 1`, `f v = (K ρ)^{#lone v} B^n`: the weighted sum is at most
`(n + 1) n^n (K ρ B)^n = 3`. -/
theorem sum_weighted_row :
    ∑ v : Fin 2 → Idx 3 (szG.L 0) (szG.W 0), (∏ i, |rowW (v i)|)
        * (((1 : ℝ) * (1 / 2)) ^ (loneSlots v).card * (1 : ℝ) ^ 2)
      ≤ (((2 : ℕ) : ℝ) + 1) * ((2 : ℕ) : ℝ) ^ 2 * ((1 : ℝ) * (1 / 2) * 1) ^ 2 := by
  refine sum_weighted_le (ι := Fin 2) (n := 2) rowW_bounded (by simp)
    (by rw [rowA_card]; norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [szG]) fun v => le_of_eq ?_
  simp

/-! #### The moment bound `integral_norm_flucAvg_pow_le_iter_budget` -/

/-- **Instance of `integral_norm_flucAvg_pow_le_iter_budget`** (the key statement, RBM2D `:1453`),
the true row `j ↦ S_{0j}`, `p = 1`, `(B, ρ, M, K) = (96, 1/2, 2, 2)`, `c = 1/8 ≤ ρ² = 1/4`,
`#A = 56`: the bound is `3 · 4 · (2 · (1/2) · 96)² = 110592`. -/
theorem moment_row_p1 (u : ℝ) :
    ∫ ω, ‖flucAvg szG 0 u (zt 0 (1 / 2)) (mE 0) rowW ω‖ ^ (2 * 1) ∂(Sizes.seqP szG)
      ≤ 110592 := by
  refine le_trans (integral_norm_flucAvg_pow_le_iter_budget (p := 1) (E := 0) (t := 1 / 2)
    hE0 ht0 (flucGainUpTo'_szG_half u) le_rfl le_rfl (by norm_num) ?_ rowW_bounded ?_) ?_
  · norm_num [szG]
  · rw [rowA_card]; norm_num
  · norm_num

/-- **Instance of the key statement** at the true row, `p = 2`, `(B, ρ, M, K) = (96, 1, 4, 4)`,
`c = 1/8 ≤ ρ² = 1`, `#A = 56 ≥ 4`: the bound is `5 · 4⁴ · (2³ · 96)⁴ = 445302209249280`. -/
theorem moment_row_p2 (u : ℝ) :
    ∫ ω, ‖flucAvg szG 0 u (zt 0 (1 / 2)) (mE 0) rowW ω‖ ^ (2 * 2) ∂(Sizes.seqP szG)
      ≤ 445302209249280 := by
  refine le_trans (integral_norm_flucAvg_pow_le_iter_budget (p := 2) (E := 0) (t := 1 / 2)
    hE0 ht0 (flucGainUpTo'_szG_one u) le_rfl (by norm_num) le_rfl ?_ rowW_bounded ?_) ?_
  · norm_num [szG]
  · rw [rowA_card]; norm_num
  · norm_num

/-- The block average of the block `0`, `k ↦ W^{-3} 1(k ∈ 𝓘_0)`. -/
private def blockW : Idx 3 (szG.L 0) (szG.W 0) → ℝ :=
  fun k => if (split 3 (szG.L 0) (szG.W 0) k).1 = 0 then (((szG.W 0 : ℕ) : ℝ) ^ 3)⁻¹ else 0

/-- The support of the block average. -/
private def blockA : Finset (Idx 3 (szG.L 0) (szG.W 0)) :=
  (Finset.univ : Finset (Idx 3 (szG.L 0) (szG.W 0))).filter fun k =>
    (split 3 (szG.L 0) (szG.W 0) k).1 = 0

private theorem blockW_bounded :
    BoundedWeight blockW ((((szG.W 0 : ℕ) : ℝ) ^ 3)⁻¹) blockA :=
  (uniformWeight_blockAvg2 3 (szG.L 0) (szG.W 0) 0).toBoundedWeight

/-- Nondegeneracy: the block has `W^d = 8` sites (`c · #A = 1`). -/
theorem blockA_card : blockA.card = 8 := by
  rw [blockA, flucVanish_card_blockSupport]
  norm_num [szG]

/-- **Instance of the key statement** at the block average, `p = 1`, `(96, 1/2, 2, 2)`,
`c = 1/8 ≤ 1/4`, `#A = 8`: the bound is `110592`. -/
theorem moment_block_p1 (u : ℝ) :
    ∫ ω, ‖flucAvg szG 0 u (zt 0 (1 / 2)) (mE 0) blockW ω‖ ^ (2 * 1) ∂(Sizes.seqP szG)
      ≤ 110592 := by
  refine le_trans (integral_norm_flucAvg_pow_le_iter_budget (p := 1) (E := 0) (t := 1 / 2)
    hE0 ht0 (flucGainUpTo'_szG_half u) le_rfl le_rfl (by norm_num) ?_ blockW_bounded ?_) ?_
  · norm_num [szG]
  · rw [blockA_card]; norm_num
  · norm_num

/-! #### The iteration lemmas -/

/-- **Instance of `bddMeas_epsHom_flucDiag`**: the conjugated centred fluctuation at `siteA`. -/
theorem bddMeas_epsHom_flucDiag_szG (u : ℝ) :
    BddMeas szG fun ω => epsHom 1 (Sum.inr 0) (flucDiag szG 0 u (zt 0 (1 / 2)) (mE 0) siteA ω) :=
  bddMeas_epsHom_flucDiag hE0 ht0 u 1 (Sum.inr 0) siteA

/-- The slots `(0, 0, 0)` and `(0, 0, 1)` of the instance of
`norm_integral_prod_epsHom_flucDiag_le_budget`. -/
private def slotV : (Fin 1 ⊕ Fin 1) → Idx 3 (szG.L 0) (szG.W 0) :=
  Sum.elim (fun _ => siteA) fun _ => siteB

/-- **Instance of `norm_integral_prod_epsHom_flucDiag_le_budget`** (the iteration at order
`2p = 2`): both slots are lone, `R` is all of them, `#R = 2`, and the bound is
`(2 max(1, 1/2))^{(2p - 1) 2} (1/2)² 96² = 9216`. -/
theorem iter_epsHom_budget (u : ℝ) :
    ‖∫ ω, ∏ i, epsHom 1 i (flucDiag szG 0 u (zt 0 (1 / 2)) (mE 0) (slotV i) ω)
        ∂(Sizes.seqP szG)‖ ≤ 9216 := by
  have hlone : ∀ i₀ ∈ (Finset.univ : Finset (Fin 1 ⊕ Fin 1)), ∀ j, j ≠ i₀ →
      slotV j ≠ slotV i₀ := by
    decide
  refine le_trans (norm_integral_prod_epsHom_flucDiag_le_budget (p := 1) (E := 0) (t := 1 / 2)
    hE0 ht0 u (flucGainUpTo'_szG_half u) le_rfl le_rfl slotV Finset.univ hlone) ?_
  simp
  norm_num

/-- The crude gain hypothesis of the graded iteration at `ι = Fin 2`, `(B, ρ) = (96, 1/2)`. -/
private theorem hgain_graded (u : ℝ)
    (L : Fin 2 → List (Bool × Idx 3 (szG.L 0) (szG.W 0)))
    (_hL : ∀ i, OpsOk rowK i (L i))
    (hlen : ∀ i, (L i).length ≤ Fintype.card (Fin 2)) :
    ∫ ω, ∏ i, ‖applyOps szG 0 (L i) (qRow szG 0 (rowK i)
        (greenDiagCentered szG 0 u (zt 0 (1 / 2)) (mE 0) (rowK i))) ω‖ ∂(Sizes.seqP szG)
      ≤ 96 ^ Fintype.card (Fin 2) * (1 / 2 : ℝ) ^ ∑ i, numQ (L i) := by
  refine flucIter_integral_prod_norm_applyOps_le_crude
    (b := 2 * (((zt 0 (1 / 2)).im)⁻¹ + 1))
    (fun i ω => norm_flucDiag_le (norm_greenDiagCentered_le_env (E := 0) (t := 1 / 2)
      hE0 ht0 u _) ω) L fun i => ?_
  have hq : numQ (L i) ≤ 2 :=
    le_trans List.countP_le_length ((hlen i).trans (by simp))
  rw [eta_eq]
  have : ∀ q ≤ 2, 2 ^ q * (2 * (((1 / 2 : ℝ))⁻¹ + 1)) ≤ 96 * (1 / 2 : ℝ) ^ q := by
    intro q hq
    interval_cases q <;> norm_num
  exact this _ hq

private theorem opsOkOut_one :
    ∀ i, OpsOkOut rowK i ({0} : Finset (Fin 2)) (![[(false, siteB)], []] i) := by
  rw [Fin.forall_fin_two]
  refine ⟨⟨by simp, ?_⟩, opsOkOut_nil _ _ _⟩
  intro x hx
  obtain rfl := List.mem_singleton.1 hx
  exact ⟨⟨1, by simp, rfl⟩, siteB_ne_siteA⟩

/-- **Instance of `OpsOkOut.length_le`**: the word `P_{siteB}` outside `R = {0}` has
`1 + 1 ≤ #ι = 2` letters-plus-pivots. -/
theorem opsOkOut_length_le_szG :
    (![[(false, siteB)], []] (0 : Fin 2)).length + ({0} : Finset (Fin 2)).card
      ≤ Fintype.card (Fin 2) :=
  (opsOkOut_one 0).length_le

/-- **Instance of `norm_integral_prod_applyOps_le_graded`** (the iteration with a nonempty word):
the slots `Fin 2` carry the rows `siteA`, `siteB`, `R = {0}` (`r = 1`), the word of slot `0` is the
single letter `P_{siteB}`, that of slot `1` is empty; the bound is
`(2 max(1, 1/2))^{(2 - 1) 1} (1/2) (96² (1/2)⁰) = 9216`. -/
theorem iter_graded (u : ℝ) :
    ‖∫ ω, ∏ i : Fin 2, applyOps szG 0 (![[(false, siteB)], []] i) (qRow szG 0 (rowK i)
          (greenDiagCentered szG 0 u (zt 0 (1 / 2)) (mE 0) (rowK i))) ω ∂(Sizes.seqP szG)‖
      ≤ 9216 := by
  have hX : ∀ i, BddMeas szG (greenDiagCentered szG 0 u (zt 0 (1 / 2)) (mE 0) (rowK i)) :=
    fun i => bddMeas_greenDiagCentered (E := 0) (t := 1 / 2) hE0 ht0 u _
  have hXd : ∀ i, FinDep szG (greenDiagCentered szG 0 u (zt 0 (1 / 2)) (mE 0) (rowK i)) :=
    fun i => finDep_greenDiagCentered szG 0 u _ _ _
  have hlone : ∀ i₀ ∈ ({0} : Finset (Fin 2)), ∀ j, j ≠ i₀ → rowK j ≠ rowK i₀ := by
    decide
  have h := norm_integral_prod_applyOps_le_graded (k := rowK) hX hXd
    (B := 96) (ρ := 1 / 2) (by norm_num) (by norm_num) (hgain_graded u) 1 {0}
    ![[(false, siteB)], []] rfl hlone opsOkOut_one
  refine le_trans h ?_
  simp [numQ]
  norm_num

/-- **Instance of `norm_integral_prod_qRow_le_graded`** (the iteration from empty words): the same
data with `R = {0, 1}`; the bound is `(2 max(1, 1/2))^{(2 - 1) 2} (1/2)² 96² = 9216`. -/
theorem iter_qRow (u : ℝ) :
    ‖∫ ω, ∏ i : Fin 2, qRow szG 0 (rowK i)
          (greenDiagCentered szG 0 u (zt 0 (1 / 2)) (mE 0) (rowK i)) ω ∂(Sizes.seqP szG)‖
      ≤ 9216 := by
  have hX : ∀ i, BddMeas szG (greenDiagCentered szG 0 u (zt 0 (1 / 2)) (mE 0) (rowK i)) :=
    fun i => bddMeas_greenDiagCentered (E := 0) (t := 1 / 2) hE0 ht0 u _
  have hXd : ∀ i, FinDep szG (greenDiagCentered szG 0 u (zt 0 (1 / 2)) (mE 0) (rowK i)) :=
    fun i => finDep_greenDiagCentered szG 0 u _ _ _
  have hlone : ∀ i₀ ∈ (Finset.univ : Finset (Fin 2)), ∀ j, j ≠ i₀ → rowK j ≠ rowK i₀ := by
    decide
  refine le_trans (norm_integral_prod_qRow_le_graded (k := rowK) Finset.univ hlone hX
    hXd (B := 96) (ρ := 1 / 2) (by norm_num) (by norm_num) (hgain_graded u)) ?_
  simp
  norm_num

/-- **Instance of `condRow_condRow_comm`** (RBM2D `flucIter_check_comm`): `E_{siteA}` and
`E_{siteB}` commute on the bounded measurable function `G_{kk} - m`, `k = siteA`. -/
theorem iter_comm (u : ℝ) :
    condRow szG 0 (rowK 0) (condRow szG 0 (rowK 1)
        (greenDiagCentered szG 0 u (zt 0 (1 / 2)) (mE 0) (rowK 0)))
      = condRow szG 0 (rowK 1) (condRow szG 0 (rowK 0)
        (greenDiagCentered szG 0 u (zt 0 (1 / 2)) (mE 0) (rowK 0))) :=
  condRow_condRow_comm szG 0 _ _
    (bddMeas_greenDiagCentered (E := 0) (t := 1 / 2) hE0 ht0 u _)

end

end FlucIterGainInst

end RBM.Green
