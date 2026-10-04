/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Green.MinorDiff
import RBM3D.Green.MinorGoodLe
import RBM3D.Green.CondDom

/-!
# Conditionalizing the minor-difference gain on the good event, `d ≥ 3` (S1-26)

ST-1 ticket T2117.  Port of RBM2D `Green/MinorDiffCond.lean` at commit `c9a24cf` (lines 98-903 of
1464; the private `section Checks` at 905-1387 is replaced by the instances at the end of this
file) to the fine lattice `Z_{WL}^d`, with the renaming rules R1-R4 of `docs/tickets/ST1-COMMON.md`
(item 2): `d : Sizes` becomes `sz : Sizes d`, `Idx (d.L n) (d.W n)` becomes
`Idx d (sz.L n) (sz.W n)`, `d.size n` becomes `sz.size n`, `spectralZ E t` and `spectralM E` become
`zt E t` and `mE E`.  The module is the closing step of the chain `Green/MinorGoodLe` (S1-22, the
interface `MinorDiffGainUpTo'` and its reduction `flucGainUpTo'_of_minorDiffGainUpTo'`),
`Green/MinorDiff` (S1-25, the word estimates on `MinorGoodLe`) and `Green/CondDom` (S1-24,
`rowSlice` and `norm_condRow_le_split`): it **produces** the hypothesis `MinorDiffGainUpTo'` that
S1-22 left open, from the per-time good event of the paper and one smallness condition `hsmall`.

The paper (arXiv:2507.20274) has the event `Ω(t, ε₀) = {‖G_t - M‖_max ≤ W^{-ε₀}}`
(`def_asGMc`, `paper/tex/3_5_Loop_Hierarchy.tex:16`, in `lem_GbEXP`, `:14`) and states the entry
estimates on it with the indicator `1_Ω` and the relation `≺`; the proofs are deferred to Lemma 4.1
of `[YY_25]` "whose proofs are dimension-independent" (`:37`).  This file has no counterpart in the
TeX: it is Lean's passage from the event `Ω` to the moment bound that the `2p`-th moment expansion
consumes.

## Why an indicator does not work, and what does

`flucDiagSet` **is** `qRow k (…)`, a conditional expectation, and `applyOps` stacks further `E_κ`
on top of it, so multiplying by `1_Ω` does not commute past the operators.  The legitimate tool is
`norm_condRow_le_split` (`Green/CondDom.lean`): off the exceptional set the integrand obeys the
sharp bound, on the whole space the deterministic envelope, and `E_κ` splits into the two
contributions, the second weighted by the probability of the **row section** of the exceptional
set.  A single exceptional set with `∀ ω, P(rowSlice κ Bad ω) ≤ ε` is not available (conditionally
on a catastrophic configuration of the other rows the good event fails with probability one);
`badStep` enlarges a set by the frozen configurations whose section is not `ε`-small, `badTower`
iterates it, `BadFamily` is the resulting interface and `badFamily_badTower` **produces** it for
any measurable base.  `meas_badStep_le`, `meas_badTower_le` are the price: one factor
`(ε + #rows)/ε` per letter, `#rows = size n = (W L)^d` (`flucAvg_card_Idx_eq_size`).

## Contents (namespace `RBM.Green`)

* the tower: `badStep`, `badTower`, `BadFamily`, `badFamily_badTower`, `meas_badStep_le`,
  `meas_badTower_le` (and the `sz.size n` forms `minorDiffCond_meas_badStep_le_size`,
  `minorDiffCond_meas_badTower_le_size`);
* the word estimate `norm_applyOps_le_badFamily` (a word of `l` letters is sharp off `Bad l`, up to
  `l · Env · ε`), the one-point size `norm_minorDiff_qList_greenSetDiagCentered_le`, and their
  combination `norm_applyOps_minorDiff_flucDiagSet_le_badFamily`;
* the envelope `condEnv`, the price `condCost`, the pointwise bound
  `norm_applyOps_minorDiff_flucDiagSet_le_condEnv`, the moment bound
  `integral_prod_applyOps_minorDiff_le_on` (no `∀ ω` hypothesis; additive remainder
  `condEnv^{#ι} P(Bad_{M+1})`);
* the base `badBase` (the measurable hull of the complement of
  `{ω | ∀ i j, llErrMat … i j ≤ δ n}` at the time `t n`), `minorGoodLe_of_notMem_badBase`;
* the budget: `condEps` (with `condCost_condEps`: the price at `ε = condEps` is exactly `Ψ`),
  `minorDiffGainUpTo'_of_le_on`;
* **the endpoints** `minorDiffGainUpTo'_goodEvent` (RBM2D `MinorDiffCond:869`) and
  `flucGainUpTo'_goodEvent` (`MinorDiffCond:890`).

## The gain exponent at `d ≥ 3`

At `Ψ = 2 δ n` the endpoint gives `B = 2 (2 C_M Ψ + condCost)` and `ρ = 2 Ψ = 4 δ n`; at
`ε = condEps`, `condCost = Ψ` and `B = 2 (2 C_M + 1) Ψ`, with `C_M = minorDiffC M` depending on
`M` only.  `ρ < 1` iff `δ n < 1/4` (`hδ4`).  The layer `q ≤ M` costs `B ρ^q ∝ δ^{q+1}`; with
`δ = W^{-c}`, `c ∈ [ε₀, d/2]` (the window of `initialGT2`, `3_5:28`), each layer gains `W^{-c}`,
sharp `c = d/2` (RBM2D, `d = 2`: `W^{-1}`).  The statement itself contains no `W`, `L`, `d`
exponent: `d` enters through the type `Idx d (sz.L n) (sz.W n)` and the row count `size n`.
The preflight (a) of the prove report measures the per-layer exponent at `d = 3`.

## `hB1` and `hsmall`

`hB1` (`2 C_M Ψ + condCost ≤ 1`) and `hsmall` (`condEnv^K P(badTower (M+1)) ≤ B₀^K (2Ψ)^{KM}`)
are hypotheses of the endpoints.  `hB1` is a deterministic inequality (at `ε = condEps`,
`(2 C_M + 1) Ψ ≤ 1`, i.e. `δ ≤ 1/524290` at `M = 1`).  `hsmall` is the owed high-probability input:
by `meas_badTower_le` it follows from `P(Ω^c) ≤ W^{-D}` with `D` large enough (G4.12, a separate
gate).  Neither involves a weight, so DECISIONS §30 (D192) does not touch this file; the statements
are at one slice `n` with `|E n| < 2`, `t n < 1`, a real `u` (here `u = t n`), no `∀ᶠ n`, no `ilambda`,
no window (DECISIONS §29).

## Differences from RBM2D (residual, after the renaming)

* `RBM2D.Path.Step2Props` is not imported: `etaT` is `RBM.Gauss.etaT` (`Loop/GLoop.lean:75`;
  `etaT E t = (1 - t) * (mE E).im` by definition, so `spectralZ_im` becomes `zt_im`,
  `Defs/Semicircle.lean:182`) and `llErrMat` is `Green/Pins.lean:73` (explicit `d L W`).
* The bridge from `llErrMat … ≤ δ` to `GoodEvent (green H z) m δ` goes through the private
  `minorDiffCond_Gres_true` (`Gres H z true = green H z`; the merged `Gres` is a `Ring.inverse`,
  `green` is `Matrix.inv`; the same restatement as in `Green/MinorGoodLe.lean`).
* `open … RBM.Path` is dropped; nothing else of the 806 ported lines (98-903) changes beyond the
  renaming (script diff in the prove report).
* No declaration of lines 98-903 is dropped.
-/

set_option linter.style.longLine false

namespace RBM.Green

open MeasureTheory ProbabilityTheory Matrix Finset RBM.Gauss

open scoped ENNReal

variable {d : ℕ} {sz : Sizes d} {n : ℕ}

/-! ### The tower of exceptional sets -/

/-- One step of the tower: enlarge `S` by the frozen configurations whose row-`κ` section of `S` is
not `ε`-small, for some row `κ` (RBM1D `badStep`, `MinorDiffCond:101` at `c06b103`). -/
def badStep (sz : Sizes d) (n : ℕ) (ε : ℝ) (S : Set (Sizes.SeqΩ sz)) : Set (Sizes.SeqΩ sz) :=
  S ∪ ⋃ κ : Idx d (sz.L n) (sz.W n), {ω | ε < (Sizes.seqP sz).real (rowSlice sz n κ S ω)}

theorem subset_badStep (sz : Sizes d) (n : ℕ) (ε : ℝ) (S : Set (Sizes.SeqΩ sz)) :
    S ⊆ badStep sz n ε S :=
  Set.subset_union_left

theorem measurable_measureReal_rowSlice (sz : Sizes d) (n : ℕ) (κ : Idx d (sz.L n) (sz.W n))
    {S : Set (Sizes.SeqΩ sz)} (hS : MeasurableSet S) :
    Measurable fun ω => (Sizes.seqP sz).real (rowSlice sz n κ S ω) :=
  (measurable_measure_rowSlice sz n κ hS).ennreal_toReal

theorem measurableSet_badStep {ε : ℝ} {S : Set (Sizes.SeqΩ sz)} (hS : MeasurableSet S) :
    MeasurableSet (badStep sz n ε S) :=
  hS.union (MeasurableSet.iUnion fun κ =>
    measurableSet_lt measurable_const (measurable_measureReal_rowSlice sz n κ hS))

/-- Off `badStep`, every row section of `S` is `ε`-small. -/
theorem measureReal_rowSlice_le_of_notMem_badStep {ε : ℝ} {S : Set (Sizes.SeqΩ sz)}
    (κ : Idx d (sz.L n) (sz.W n)) {ω : Sizes.SeqΩ sz} (hω : ω ∉ badStep sz n ε S) :
    (Sizes.seqP sz).real (rowSlice sz n κ S ω) ≤ ε := by
  by_contra h
  exact hω (Or.inr (Set.mem_iUnion.2 ⟨κ, not_le.1 h⟩))

/-- **The tower.**  `badTower sz n ε S j` is `S` enlarged `j` times (RBM1D `badTower`,
`MinorDiffCond:123`). -/
def badTower (sz : Sizes d) (n : ℕ) (ε : ℝ) (S : Set (Sizes.SeqΩ sz)) : ℕ → Set (Sizes.SeqΩ sz)
  | 0 => S
  | j + 1 => badStep sz n ε (badTower sz n ε S j)

@[simp] theorem badTower_zero (sz : Sizes d) (n : ℕ) (ε : ℝ) (S : Set (Sizes.SeqΩ sz)) :
    badTower sz n ε S 0 = S := rfl

@[simp] theorem badTower_succ (sz : Sizes d) (n : ℕ) (ε : ℝ) (S : Set (Sizes.SeqΩ sz)) (j : ℕ) :
    badTower sz n ε S (j + 1) = badStep sz n ε (badTower sz n ε S j) := rfl

/-- **The interface the word estimate consumes.**  A monotone measurable family whose `j`-th member
has `ε`-small row sections off the `(j+1)`-st (RBM1D `BadFamily`, `MinorDiffCond:142`).

This replaces a hypothesis `∀ κ ω, P(rowSlice κ Bad ω) ≤ ε` with a single set `Bad`, which is a
`∀ ω` statement (and, by RBM1D's analysis, false for the good event: see the module docstring).
`badStep` enlarges the set by the frozen configurations where the section is not `ε`-small, once
per letter of the word. -/
structure BadFamily (sz : Sizes d) (n : ℕ) (ε : ℝ) (Bad : ℕ → Set (Sizes.SeqΩ sz)) : Prop where
  /-- Every member is measurable. -/
  meas : ∀ j, MeasurableSet (Bad j)
  /-- The family increases. -/
  mono : ∀ j, Bad j ⊆ Bad (j + 1)
  /-- Off the next member, the row sections of the current one are `ε`-small. -/
  slice : ∀ (j : ℕ) (κ : Idx d (sz.L n) (sz.W n)) {ω : Sizes.SeqΩ sz}, ω ∉ Bad (j + 1) →
    (Sizes.seqP sz).real (rowSlice sz n κ (Bad j) ω) ≤ ε

theorem BadFamily.mono_le {ε : ℝ} {Bad : ℕ → Set (Sizes.SeqΩ sz)} (h : BadFamily sz n ε Bad) :
    ∀ {j j' : ℕ}, j ≤ j' → Bad j ⊆ Bad j' := by
  intro j j' hjj'
  induction j' with
  | zero => rw [Nat.le_zero.1 hjj']
  | succ k ih =>
      rcases Nat.lt_or_ge j (k + 1) with hlt | hge
      · exact (ih (Nat.lt_succ_iff.1 hlt)).trans (h.mono k)
      · rw [le_antisymm hjj' hge]

/-- **The tower is a `BadFamily`.**  Nothing is assumed about `S` beyond measurability, so the
hypothesis of the word estimate is *produced*, not postulated. -/
theorem badFamily_badTower (sz : Sizes d) (n : ℕ) (ε : ℝ) {S : Set (Sizes.SeqΩ sz)}
    (hS : MeasurableSet S) : BadFamily sz n ε (badTower sz n ε S) where
  meas := by
    intro j
    induction j with
    | zero => exact hS
    | succ k ih => exact measurableSet_badStep ih
  mono := fun j => subset_badStep sz n ε _
  slice := fun j κ _ hω => measureReal_rowSlice_le_of_notMem_badStep κ hω

/-! ### The measure of the tower -/

/-- **One step costs a factor `1 + #rows / ε`**, by Fubini and Markov for the row section
(`meas_measure_rowSlice_ge`).  Stated multiplicatively to avoid division in `ℝ≥0∞`.  The rows are
the `size n = (W L)^d` sites of the lattice (`flucAvg_card_Idx_eq_size`); RBM1D has `N`. -/
theorem meas_badStep_le (sz : Sizes d) (n : ℕ) {ε : ℝ} {S : Set (Sizes.SeqΩ sz)}
    (hS : MeasurableSet S) :
    ENNReal.ofReal ε * (Sizes.seqP sz) (badStep sz n ε S)
      ≤ (ENNReal.ofReal ε + (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ≥0∞)) * (Sizes.seqP sz) S := by
  classical
  have hsub : ∀ κ : Idx d (sz.L n) (sz.W n),
      {ω : Sizes.SeqΩ sz | ε < (Sizes.seqP sz).real (rowSlice sz n κ S ω)}
        ⊆ {ω : Sizes.SeqΩ sz | ENNReal.ofReal ε ≤ (Sizes.seqP sz) (rowSlice sz n κ S ω)} := by
    intro κ ω hω
    exact ENNReal.ofReal_le_of_le_toReal hω.le
  have hstep : ∀ κ : Idx d (sz.L n) (sz.W n),
      ENNReal.ofReal ε * (Sizes.seqP sz)
        {ω : Sizes.SeqΩ sz | ε < (Sizes.seqP sz).real (rowSlice sz n κ S ω)}
        ≤ (Sizes.seqP sz) S := by
    intro κ
    refine le_trans (mul_le_mul_right (measure_mono (hsub κ)) _) ?_
    exact meas_measure_rowSlice_ge sz n κ hS (ENNReal.ofReal ε)
  have hunion : (Sizes.seqP sz) (badStep sz n ε S)
      ≤ (Sizes.seqP sz) S + ∑ κ : Idx d (sz.L n) (sz.W n), (Sizes.seqP sz)
          {ω : Sizes.SeqΩ sz | ε < (Sizes.seqP sz).real (rowSlice sz n κ S ω)} := by
    refine le_trans (measure_union_le _ _) (add_le_add_right ?_ _)
    exact measure_iUnion_fintype_le _ _
  calc ENNReal.ofReal ε * (Sizes.seqP sz) (badStep sz n ε S)
      ≤ ENNReal.ofReal ε * ((Sizes.seqP sz) S
          + ∑ κ : Idx d (sz.L n) (sz.W n), (Sizes.seqP sz)
              {ω : Sizes.SeqΩ sz | ε < (Sizes.seqP sz).real (rowSlice sz n κ S ω)}) :=
        mul_le_mul_right hunion _
    _ = ENNReal.ofReal ε * (Sizes.seqP sz) S
          + ∑ κ : Idx d (sz.L n) (sz.W n), ENNReal.ofReal ε * (Sizes.seqP sz)
              {ω : Sizes.SeqΩ sz | ε < (Sizes.seqP sz).real (rowSlice sz n κ S ω)} := by
        rw [mul_add, Finset.mul_sum]
    _ ≤ ENNReal.ofReal ε * (Sizes.seqP sz) S
          + ∑ _κ : Idx d (sz.L n) (sz.W n), (Sizes.seqP sz) S :=
        add_le_add_right (Finset.sum_le_sum fun κ _ => hstep κ) _
    _ = (ENNReal.ofReal ε + (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ≥0∞)) * (Sizes.seqP sz) S := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, add_mul]

/-- **The tower's measure**: `ε^j P(Bad_j) ≤ (ε + #rows)^j P(Bad_0)`, with `#rows = size n`.  Since
`P(Bad_0)` is super-polynomially small (it is the complement of (4.1)) while `#rows = size n` and
`ε` is a fixed negative power of `size n`, the whole tower is still super-polynomially small for
every fixed number `j` of letters. -/
theorem meas_badTower_le (sz : Sizes d) (n : ℕ) {ε : ℝ} {S : Set (Sizes.SeqΩ sz)}
    (hS : MeasurableSet S) (j : ℕ) :
    ENNReal.ofReal ε ^ j * (Sizes.seqP sz) (badTower sz n ε S j)
      ≤ (ENNReal.ofReal ε + (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ≥0∞)) ^ j
          * (Sizes.seqP sz) S := by
  induction j with
  | zero => simp
  | succ k ih =>
      have hmeas : MeasurableSet (badTower sz n ε S k) :=
        (badFamily_badTower sz n ε hS).meas k
      calc ENNReal.ofReal ε ^ (k + 1) * (Sizes.seqP sz) (badTower sz n ε S (k + 1))
          = ENNReal.ofReal ε ^ k * (ENNReal.ofReal ε
              * (Sizes.seqP sz) (badStep sz n ε (badTower sz n ε S k))) := by
            rw [badTower_succ, pow_succ]; ring
        _ ≤ ENNReal.ofReal ε ^ k
              * ((ENNReal.ofReal ε + (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ≥0∞))
                  * (Sizes.seqP sz) (badTower sz n ε S k)) :=
            mul_le_mul_right (meas_badStep_le sz n hmeas) _
        _ = (ENNReal.ofReal ε + (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ≥0∞))
              * (ENNReal.ofReal ε ^ k * (Sizes.seqP sz) (badTower sz n ε S k)) := by ring
        _ ≤ (ENNReal.ofReal ε + (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ≥0∞))
              * ((ENNReal.ofReal ε + (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ≥0∞)) ^ k
                  * (Sizes.seqP sz) S) :=
            mul_le_mul_right ih _
        _ = (ENNReal.ofReal ε + (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ≥0∞)) ^ (k + 1)
              * (Sizes.seqP sz) S := by
            rw [pow_succ]; ring

/-- `meas_badStep_le` with the row count written as `size n` (`#Idx = size n`,
`flucAvg_card_Idx_eq_size`), the form in which the consumers polynomially bound it. -/
theorem minorDiffCond_meas_badStep_le_size (sz : Sizes d) (n : ℕ) {ε : ℝ} {S : Set (Sizes.SeqΩ sz)}
    (hS : MeasurableSet S) :
    ENNReal.ofReal ε * (Sizes.seqP sz) (badStep sz n ε S)
      ≤ (ENNReal.ofReal ε + (sz.size n : ℝ≥0∞)) * (Sizes.seqP sz) S := by
  have h := meas_badStep_le sz n (ε := ε) hS
  rwa [flucAvg_card_Idx_eq_size] at h

/-- `meas_badTower_le` with the row count written as `size n`. -/
theorem minorDiffCond_meas_badTower_le_size (sz : Sizes d) (n : ℕ) {ε : ℝ} {S : Set (Sizes.SeqΩ sz)}
    (hS : MeasurableSet S) (j : ℕ) :
    ENNReal.ofReal ε ^ j * (Sizes.seqP sz) (badTower sz n ε S j)
      ≤ (ENNReal.ofReal ε + (sz.size n : ℝ≥0∞)) ^ j * (Sizes.seqP sz) S := by
  have h := meas_badTower_le sz n (ε := ε) hS j
  rwa [flucAvg_card_Idx_eq_size] at h

/-! ### A word applied to a function that is good off the tower -/

/-- Words concatenate. -/
theorem applyOps_append (sz : Sizes d) (n : ℕ) (l₁ l₂ : List (Bool × Idx d (sz.L n) (sz.W n)))
    (X : Sizes.SeqΩ sz → ℂ) :
    applyOps sz n (l₁ ++ l₂) X = applyOps sz n l₁ (applyOps sz n l₂ X) := by
  induction l₁ with
  | nil => rfl
  | cons x l ih =>
      obtain ⟨b, κ⟩ := x
      cases b
      · simp only [List.cons_append, applyOps_cons_false, ih]
      · simp only [List.cons_append, applyOps_cons_true, ih]

/-- **The conditionalized word estimate.**

If `X` obeys the sharp bound `c` off `Bad 0` and the deterministic envelope `Env` everywhere, then a
word of `l.length` letters obeys the sharp bound off `Bad l.length`, up to the additive loss
`l.length · Env · ε` from the row sections that the conditional expectations integrate over.

Multiplying the integrand by an indicator is *not* available: `flucDiagSet` is itself a `qRow`, and
`applyOps` stacks further `E_κ` on top of it, so an indicator does not commute past the conditional
expectations.  What does pass is `norm_condRow_le_split`: on the good set the integrand obeys the
sharp bound, on the whole space the envelope, and `E_κ` splits accordingly, at the price of one
further enlargement of the exceptional set per letter. -/
theorem norm_applyOps_le_badFamily {X : Sizes.SeqΩ sz → ℂ} (hX : BddMeas sz X)
    {Bad : ℕ → Set (Sizes.SeqΩ sz)} {ε Env c : ℝ} (hfam : BadFamily sz n ε Bad)
    (hEnv : ∀ ω, ‖X ω‖ ≤ Env) (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (hgood : ∀ ω ∉ Bad 0, ‖X ω‖ ≤ c) :
    ∀ (l : List (Bool × Idx d (sz.L n) (sz.W n))) (ω : Sizes.SeqΩ sz), ω ∉ Bad l.length →
      ‖applyOps sz n l X ω‖ ≤ 2 ^ numQ l * (c + l.length * Env * ε) := by
  have hEnv0 : 0 ≤ Env := le_trans (norm_nonneg _) (hEnv 0)
  intro l
  induction l with
  | nil => intro ω hω; simpa using hgood ω hω
  | cons x l ih =>
      obtain ⟨b, κ⟩ := x
      intro ω hω
      have hωl : ω ∉ Bad l.length := fun h => hω (hfam.mono l.length h)
      set A : ℝ := 2 ^ numQ l * (c + l.length * Env * ε) with hA
      have hA0 : 0 ≤ A := by rw [hA]; positivity
      have hinner : ∀ σ ∉ Bad l.length, ‖applyOps sz n l X σ‖ ≤ A * (1 : ℝ) := by
        intro σ hσ; rw [mul_one]; exact ih σ hσ
      have hEnvl : ∀ σ, ‖applyOps sz n l X σ‖ ≤ 2 ^ numQ l * Env := fun σ =>
        norm_applyOps_le l hEnv σ
      have hsplit := norm_condRow_le_split (k := κ) (X := applyOps sz n l X)
        (hX.applyOps l).meas (f := fun _ : Sizes.SeqΩ sz => (1 : ℝ)) (fun _ => zero_le_one)
        (fun _ => integrable_const 1) hEnvl hA0 (hfam.meas l.length) hinner ω
      have hcr : condRowReal sz n κ (fun _ : Sizes.SeqΩ sz => (1 : ℝ)) ω = 1 := by
        rw [condRowReal_const]
      rw [hcr, mul_one] at hsplit
      have hsl := hfam.slice l.length κ hω
      have hEnvpos : (0 : ℝ) ≤ 2 ^ numQ l * Env := by positivity
      have hterm : 2 ^ numQ l * Env * (Sizes.seqP sz).real (rowSlice sz n κ (Bad l.length) ω)
          ≤ 2 ^ numQ l * Env * ε := mul_le_mul_of_nonneg_left hsl hEnvpos
      have hcond : ‖condRow sz n κ (applyOps sz n l X) ω‖ ≤ A + 2 ^ numQ l * Env * ε := by
        linarith
      have hEe : (0 : ℝ) ≤ 2 ^ numQ l * Env * ε := by positivity
      cases b
      · rw [applyOps_cons_false, numQ_cons_false]
        refine hcond.trans (le_of_eq ?_)
        rw [hA, List.length_cons]
        push_cast
        ring
      · rw [applyOps_cons_true, numQ_cons_true]
        have htri : ‖qRow sz n κ (applyOps sz n l X) ω‖
            ≤ ‖applyOps sz n l X ω‖ + ‖condRow sz n κ (applyOps sz n l X) ω‖ := by
          rw [qRow_apply]; exact norm_sub_le _ _
        have hgoal : 2 ^ (numQ l + 1) * (c + ((l.length : ℝ) + 1) * Env * ε)
            = 2 * A + 2 * (2 ^ numQ l * Env * ε) := by
          rw [hA]; ring
        have h1 := ih ω hωl
        rw [List.length_cons]
        push_cast
        rw [hgoal]
        linarith

/-! ### The sharp size of the word's minor difference, at one sample point -/

section Words

variable {u : ℝ} {z m : ℂ} {Ψ : ℝ} {M : ℕ}

theorem numQ_append_true (L : List (Bool × Idx d (sz.L n) (sz.W n))) (k : Idx d (sz.L n) (sz.W n)) :
    numQ (L ++ [(true, k)]) = numQ L + 1 := by
  simp [numQ, List.countP_append]

/-- **Both grades of the gain in one statement**, at a *single* sample point: the word's minor
difference of `G^{(·)}_{kk} - m` is at most `C_M Ψ^{#Q + 1}`.

The empty word is (4.3) itself (`norm_greenSetDiagCentered_le`) and a non-empty word is the `Δ_κ`
calculus (`norm_minorDiff_greenSetDiagCentered_le`).  `ω` appears only as the point at which the
hypothesis and the conclusion are read: no `∀ ω`. -/
theorem norm_minorDiff_qList_greenSetDiagCentered_le {ω : Sizes.SeqΩ sz}
    (hg : MinorGoodLe sz n u z m ω Ψ M) (hΨ0 : 0 ≤ Ψ) (hΨ1 : Ψ ≤ 1) (k : Idx d (sz.L n) (sz.W n))
    (L : List (Bool × Idx d (sz.L n) (sz.W n))) (h1 : ((L.map Prod.snd)).Nodup)
    (h2 : ∀ x ∈ L, x.2 ≠ k) (hM : L.length ≤ M) :
    ‖minorDiff sz n (qList L) (greenSetDiagCentered sz n u z m k) ω‖
      ≤ minorDiffC M * Ψ ^ (numQ L + 1) := by
  classical
  have hlenq : (qList L).length = numQ L := length_qList L
  have hnodup : (qList L).Nodup := qList_nodup h1
  have hne : ∀ y ∈ qList L, y ≠ k := fun y hy => mem_qList_ne h2 hy
  have hCM := one_le_minorDiffC M
  cases hqs : qList L with
  | nil =>
      have hzero : numQ L = 0 := by rw [← hlenq, hqs]; rfl
      rw [hzero, pow_one]
      have hb := norm_greenSetDiagCentered_le hg hΨ0 k ∅ (by simp)
      simp only [minorDiff_nil]
      nlinarith
  | cons κ l' =>
      have hκmem : κ ∈ qList L := by rw [hqs]; exact List.mem_cons_self
      have hkκ : k ≠ κ := Ne.symm (hne κ hκmem)
      have hnd' : (κ :: l').Nodup := by rw [← hqs]; exact hnodup
      have hkl : ∀ x ∈ l', x ≠ k := by
        intro x hx
        exact hne x (by rw [hqs]; exact List.mem_cons_of_mem _ hx)
      have hm : numQ L = l'.length + 1 := by rw [← hlenq, hqs]; simp [List.length_cons]
      have hq : numQ L ≤ L.length := List.countP_le_length
      have hlM1 : l'.length + 1 ≤ M := by omega
      have hlM : l'.length ≤ M := by omega
      rw [hm]
      refine le_trans (norm_minorDiff_greenSetDiagCentered_le hg hΨ0 hΨ1 k κ l'
        hkκ hnd' hkl hlM1) ?_
      have hmono := minorDiffC_mono hlM
      have hpow : (0 : ℝ) ≤ Ψ ^ (l'.length + 2) := pow_nonneg hΨ0 _
      have : l'.length + 1 + 1 = l'.length + 2 := by omega
      rw [this]
      exact mul_le_mul_of_nonneg_right hmono hpow

end Words

/-! ### The conditionalized estimate for one factor -/

section Factor

variable {E t : ℝ}

/-- **One factor of the `2p`-th moment, conditionalized.**

The object is `applyOps L (Δ_{qList L} Z^{(·)}_k)`.  Since `Z^{(S)}_k = Q_k (G^{(S)}_{kk} - m)` and
`Δ` commutes with `Q_k` (`minorDiff_flucDiagSet_eq`), the whole object is the *single* word
`L ++ [(true, k)]` applied to the **deterministic** family `Δ_{qList L} (G^{(·)}_{kk} - m)`, which
is where the good event enters pointwise.  `norm_applyOps_le_badFamily` then carries it through the
`#L + 1` conditional expectations. -/
theorem norm_applyOps_minorDiff_flucDiagSet_le_badFamily
    (hE : |E| < 2) (ht : t < 1) (u : ℝ) {Ψ ε : ℝ} (hΨ0 : 0 ≤ Ψ) (hΨ1 : Ψ ≤ 1) (hε : 0 ≤ ε)
    {M : ℕ} {Bad : ℕ → Set (Sizes.SeqΩ sz)} (hfam : BadFamily sz n ε Bad)
    (hgood : ∀ ω ∉ Bad 0, MinorGoodLe sz n u (zt E t) (mE E) ω Ψ M)
    (k : Idx d (sz.L n) (sz.W n)) (L : List (Bool × Idx d (sz.L n) (sz.W n)))
    (h1 : ((L.map Prod.snd)).Nodup) (h2 : ∀ x ∈ L, x.2 ≠ k) (hM : L.length ≤ M)
    (ω : Sizes.SeqΩ sz) (hω : ω ∉ Bad (L.length + 1)) :
    ‖applyOps sz n L
        (minorDiff sz n (qList L) (flucDiagSet sz n u (zt E t) (mE E) k)) ω‖
      ≤ 2 ^ (numQ L + 1)
        * (minorDiffC M * Ψ ^ (numQ L + 1)
            + ((L.length : ℝ) + 1) * (2 ^ numQ L * ((etaT E t)⁻¹ + 1)) * ε) := by
  classical
  set Y : Sizes.SeqΩ sz → ℂ :=
    minorDiff sz n (qList L) (greenSetDiagCentered sz n u (zt E t) (mE E) k) with hY
  have hrw : applyOps sz n L
        (minorDiff sz n (qList L) (flucDiagSet sz n u (zt E t) (mE E) k))
      = applyOps sz n (L ++ [(true, k)]) Y := by
    rw [minorDiff_flucDiagSet_eq hE ht u k (qList L), applyOps_append, hY]
    rfl
  have hYbdd : BddMeas sz Y :=
    bddMeas_minorDiff _ _ fun S => bddMeas_greenSetDiagCentered hE ht u k S
  have hYenv : ∀ ω', ‖Y ω'‖ ≤ 2 ^ numQ L * ((etaT E t)⁻¹ + 1) := by
    intro ω'
    have hb := norm_minorDiff_le (qList L)
      (greenSetDiagCentered sz n u (zt E t) (mE E) k)
      (fun S ω'' => norm_greenSetDiagCentered_le_env hE ht u k S ω'') ω'
    rwa [length_qList, zt_im] at hb
  have hYgood : ∀ ω' ∉ Bad 0, ‖Y ω'‖ ≤ minorDiffC M * Ψ ^ (numQ L + 1) := fun ω' hω' =>
    norm_minorDiff_qList_greenSetDiagCentered_le (hgood ω' hω') hΨ0 hΨ1 k L h1 h2 hM
  have hc0 : 0 ≤ minorDiffC M * Ψ ^ (numQ L + 1) :=
    mul_nonneg (minorDiffC_nonneg M) (pow_nonneg hΨ0 _)
  have hlen : (L ++ [(true, k)]).length = L.length + 1 := by simp
  have hωa : ω ∉ Bad ((L ++ [(true, k)]).length) := by rwa [hlen]
  have hkey := norm_applyOps_le_badFamily hYbdd hfam hYenv hc0 hε hYgood
    (L ++ [(true, k)]) ω hωa
  rw [numQ_append_true, hlen] at hkey
  rw [hrw]
  refine hkey.trans (le_of_eq ?_)
  push_cast
  ring

end Factor

/-! ### The conditionalized moment bound -/

section Moment

variable {E t : ℝ}

/-- A pointwise family of bounds **valid only off a measurable set** gives the expectation bound,
with the set's probability charged at the deterministic envelope. -/
theorem integral_prod_norm_le_of_bounds_on {ι : Type*} [Fintype ι] {F : ι → Sizes.SeqΩ sz → ℂ}
    (hF : ∀ i, BddMeas sz (F i)) {b : ι → ℝ} {Genv : ℝ} {S : Set (Sizes.SeqΩ sz)}
    (hS : MeasurableSet S) (hb0 : ∀ i, 0 ≤ b i)
    (hb : ∀ ω ∉ S, ∀ i, ‖F i ω‖ ≤ b i) (hG : ∀ ω, ∏ i, ‖F i ω‖ ≤ Genv) :
    ∫ ω, ∏ i, ‖F i ω‖ ∂(Sizes.seqP sz) ≤ (∏ i, b i) + Genv * (Sizes.seqP sz).real S := by
  classical
  have hnorm : (fun ω : Sizes.SeqΩ sz => ∏ i, ‖F i ω‖) = fun ω => ‖∏ i, F i ω‖ :=
    funext fun ω => (norm_prod _ _).symm
  have hint : Integrable (fun ω : Sizes.SeqΩ sz => ∏ i, ‖F i ω‖) (Sizes.seqP sz) := by
    rw [hnorm]; exact (bddMeas_prod Finset.univ fun i _ => hF i).integrable.norm
  have hindint : Integrable (S.indicator fun _ : Sizes.SeqΩ sz => Genv) (Sizes.seqP sz) :=
    (integrable_const Genv).indicator hS
  have hb0' : (0 : ℝ) ≤ ∏ i, b i := Finset.prod_nonneg fun i _ => hb0 i
  have hpt : ∀ ω : Sizes.SeqΩ sz, ∏ i, ‖F i ω‖ ≤ (∏ i, b i) + S.indicator (fun _ => Genv) ω := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      linarith [hG ω]
    · rw [Set.indicator_of_notMem hω, add_zero]
      exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => hb ω hω i
  calc ∫ ω, ∏ i, ‖F i ω‖ ∂(Sizes.seqP sz)
      ≤ ∫ ω, ((∏ i, b i) + S.indicator (fun _ => Genv) ω) ∂(Sizes.seqP sz) :=
        integral_mono hint ((integrable_const _).add hindint) hpt
    _ = (∏ i, b i) + Genv * (Sizes.seqP sz).real S := by
        rw [integral_add (integrable_const _) hindint, integral_indicator_const _ hS,
          smul_eq_mul, mul_comm ((Sizes.seqP sz).real S) Genv]
        simp

/-- The deterministic envelope of one factor, for words of length at most `M`:
`2^{2M+1}(η_t⁻¹ + 1)` (RBM1D `condEnv`, `MinorDiffCond:464`), with `η_t = etaT`. -/
noncomputable def condEnv (E t : ℝ) (M : ℕ) : ℝ :=
  2 ^ (2 * M + 1) * ((etaT E t)⁻¹ + 1)

theorem condEnv_nonneg (hE : |E| < 2) (ht : t < 1) (M : ℕ) : 0 ≤ condEnv E t M := by
  have hη : 0 < etaT E t := etaT_pos hE ht
  unfold condEnv
  positivity

/-- **The price of conditionalizing**, per factor: the `#L + 1` conditional expectations each
integrate over a row section of the exceptional set, and each such section is only `ε`-small.
Dividing by `(2Ψ)^M` is what puts the loss into the *constant* `B` of the graded interface rather
than into the gain `ρ` (RBM1D `condCost`, `MinorDiffCond:475`). -/
noncomputable def condCost (E t : ℝ) (M : ℕ) (Ψ ε : ℝ) : ℝ :=
  ((M : ℝ) + 1) * condEnv E t M * ε * ((2 * Ψ) ^ M)⁻¹

theorem condCost_nonneg (hE : |E| < 2) (ht : t < 1) (M : ℕ) {Ψ ε : ℝ} (hΨ0 : 0 ≤ Ψ)
    (hε : 0 ≤ ε) : 0 ≤ condCost E t M Ψ ε := by
  have := condEnv_nonneg hE ht (E := E) (t := t) M
  unfold condCost
  have h2 : (0 : ℝ) ≤ ((2 * Ψ) ^ M)⁻¹ := by positivity
  have h3 : (0 : ℝ) ≤ ((M : ℝ) + 1) := by positivity
  positivity

theorem norm_applyOps_minorDiff_flucDiagSet_le_condEnv (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    {M : ℕ} (k : Idx d (sz.L n) (sz.W n)) (L : List (Bool × Idx d (sz.L n) (sz.W n)))
    (hM : (L).length ≤ M) (ω : Sizes.SeqΩ sz) :
    ‖applyOps sz n L
        (minorDiff sz n (qList L) (flucDiagSet sz n u (zt E t) (mE E) k)) ω‖
      ≤ condEnv E t M := by
  have hη : 0 < etaT E t := etaT_pos hE ht
  have hq : numQ L ≤ M := le_trans List.countP_le_length hM
  have hdiff : ∀ ω', ‖minorDiff sz n (qList L)
      (flucDiagSet sz n u (zt E t) (mE E) k) ω'‖
        ≤ 2 ^ numQ L * (2 * ((etaT E t)⁻¹ + 1)) := by
    intro ω'
    have hb := norm_minorDiff_le (qList L) (flucDiagSet sz n u (zt E t) (mE E) k)
      (fun S ω'' => norm_flucDiagSet_le_env hE ht u k S ω'') ω'
    rwa [length_qList, zt_im] at hb
  refine le_trans (norm_applyOps_le L hdiff ω) ?_
  have hpow : (2 : ℝ) ^ numQ L * (2 ^ numQ L * (2 * ((etaT E t)⁻¹ + 1)))
      = 2 ^ (2 * numQ L + 1) * ((etaT E t)⁻¹ + 1) := by
    rw [show 2 * numQ L + 1 = numQ L + numQ L + 1 by omega, pow_succ, pow_add]
    ring
  rw [hpow]
  unfold condEnv
  have hmono : (2 : ℝ) ^ (2 * numQ L + 1) ≤ 2 ^ (2 * M + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hnn : (0 : ℝ) ≤ (etaT E t)⁻¹ + 1 := by positivity
  exact mul_le_mul_of_nonneg_right hmono hnn

/-- **(4.12)'s last input, conditionalized on the good event.**

`hgood` is read at one sample point at a time and only *off* `Bad 0`; there is no hypothesis
quantified over all `ω`.  The price is the two explicit terms:

* the per-factor constant grows from `2 C_M Ψ` to `2 C_M Ψ + condCost`, i.e. by
  `(M+1) 2^{2M+1}(η_t⁻¹+1) ε (2Ψ)^{-M}`, where `ε` is the row-section threshold of the
  `BadFamily`;
* an additive remainder `(2^{2M+1}(η_t⁻¹+1))^{#slots} P(Bad_{M+1})`.

The additive remainder is *not* removable inside an interface whose index type `ι` is
unrestricted; it is absorbed by the budget `#ι ≤ K` in `minorDiffGainUpTo'_of_le_on`. -/
theorem integral_prod_applyOps_minorDiff_le_on
    (hE : |E| < 2) (ht : t < 1) (u : ℝ) {Ψ ε : ℝ} (hΨ0 : 0 < Ψ) (hΨhalf : 2 * Ψ ≤ 1)
    (hε : 0 ≤ ε) {M : ℕ} {Bad : ℕ → Set (Sizes.SeqΩ sz)} (hfam : BadFamily sz n ε Bad)
    (hgood : ∀ ω ∉ Bad 0, MinorGoodLe sz n u (zt E t) (mE E) ω Ψ M)
    (ι : Type) [Fintype ι] (k : ι → Idx d (sz.L n) (sz.W n))
    (L : ι → List (Bool × Idx d (sz.L n) (sz.W n)))
    (h1 : ∀ i, ((L i).map Prod.snd).Nodup) (h2 : ∀ i, ∀ x ∈ L i, x.2 ≠ k i)
    (hM : ∀ i, (L i).length ≤ M) :
    ∫ ω, ∏ i, ‖applyOps sz n (L i)
        (minorDiff sz n (qList (L i)) (flucDiagSet sz n u (zt E t) (mE E) (k i))) ω‖
        ∂(Sizes.seqP sz)
      ≤ (2 * minorDiffC M * Ψ + condCost E t M Ψ ε) ^ Fintype.card ι
          * (2 * Ψ) ^ ∑ i, numQ (L i)
        + condEnv E t M ^ Fintype.card ι * (Sizes.seqP sz).real (Bad (M + 1)) := by
  classical
  have hη : 0 < etaT E t := etaT_pos hE ht
  have hΨ0' : (0 : ℝ) ≤ Ψ := hΨ0.le
  have hΨ1 : Ψ ≤ 1 := by linarith
  have hEnv0 : 0 ≤ condEnv E t M := condEnv_nonneg hE ht M
  have hcost0 : 0 ≤ condCost E t M Ψ ε := condCost_nonneg hE ht M hΨ0' hε
  have h2Ψ0 : (0 : ℝ) < 2 * Ψ := by linarith
  set B : ℝ := 2 * minorDiffC M * Ψ + condCost E t M Ψ ε with hB
  have hB0 : 0 ≤ B := by
    have := minorDiffC_nonneg M
    rw [hB]
    have : (0:ℝ) ≤ 2 * minorDiffC M * Ψ := by positivity
    linarith
  -- the per-factor bound off the exceptional set
  have hb : ∀ ω ∉ Bad (M + 1), ∀ i : ι,
      ‖applyOps sz n (L i)
        (minorDiff sz n (qList (L i)) (flucDiagSet sz n u (zt E t) (mE E) (k i))) ω‖
        ≤ B * (2 * Ψ) ^ numQ (L i) := by
    intro ω hω i
    have hωi : ω ∉ Bad ((L i).length + 1) := by
      intro hmem
      exact hω (hfam.mono_le (by have := hM i; omega) hmem)
    have hkey := norm_applyOps_minorDiff_flucDiagSet_le_badFamily hE ht u hΨ0' hΨ1 hε hfam
      hgood (k i) (L i) (h1 i) (h2 i) (hM i) ω hωi
    refine hkey.trans ?_
    set q : ℕ := numQ (L i) with hq
    have hqM : q ≤ M := le_trans List.countP_le_length (hM i)
    -- the gain term is exact
    have hgain : (2 : ℝ) ^ (q + 1) * (minorDiffC M * Ψ ^ (q + 1))
        = (2 * Ψ) ^ q * (2 * minorDiffC M * Ψ) := by
      rw [mul_pow, pow_succ, pow_succ]
      ring
    -- the exceptional term is charged to `condCost`
    have hpowle : ((2 * Ψ) ^ M : ℝ) ≤ (2 * Ψ) ^ q :=
      pow_le_pow_of_le_one h2Ψ0.le hΨhalf hqM
    have hexact : (2 * Ψ) ^ M * condCost E t M Ψ ε = ((M : ℝ) + 1) * condEnv E t M * ε := by
      unfold condCost
      field_simp
    have hlen : ((L i).length : ℝ) + 1 ≤ (M : ℝ) + 1 := by
      have : ((L i).length : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM i
      linarith
    have h2q : (2 : ℝ) ^ (q + 1) * (2 ^ q * ((etaT E t)⁻¹ + 1)) ≤ condEnv E t M := by
      unfold condEnv
      have hrw : (2 : ℝ) ^ (q + 1) * (2 ^ q * ((etaT E t)⁻¹ + 1))
          = 2 ^ (2 * q + 1) * ((etaT E t)⁻¹ + 1) := by
        rw [show 2 * q + 1 = q + q + 1 by omega, pow_succ, pow_add]
        ring
      rw [hrw]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
    have hexc : (2 : ℝ) ^ (q + 1)
        * (((L i).length + 1) * (2 ^ q * ((etaT E t)⁻¹ + 1)) * ε)
        ≤ (2 * Ψ) ^ q * condCost E t M Ψ ε := by
      have hstep : (2 : ℝ) ^ (q + 1)
          * (((L i).length + 1) * (2 ^ q * ((etaT E t)⁻¹ + 1)) * ε)
          = (((L i).length : ℝ) + 1)
              * (2 ^ (q + 1) * (2 ^ q * ((etaT E t)⁻¹ + 1))) * ε := by
        ring
      rw [hstep]
      have hA : (((L i).length : ℝ) + 1)
            * (2 ^ (q + 1) * (2 ^ q * ((etaT E t)⁻¹ + 1))) * ε
          ≤ ((M : ℝ) + 1) * condEnv E t M * ε := by
        have hnn1 : (0 : ℝ) ≤ ((L i).length : ℝ) + 1 := by positivity
        have hnn2 : (0 : ℝ) ≤ (2 : ℝ) ^ (q + 1) * (2 ^ q * ((etaT E t)⁻¹ + 1)) := by
          positivity
        have := mul_le_mul hlen h2q hnn2 (by positivity)
        exact mul_le_mul_of_nonneg_right this hε
      refine hA.trans ?_
      rw [← hexact]
      exact mul_le_mul_of_nonneg_right hpowle hcost0
    have hsplit : (2 : ℝ) ^ (q + 1)
        * (minorDiffC M * Ψ ^ (q + 1)
            + ((L i).length + 1) * (2 ^ q * ((etaT E t)⁻¹ + 1)) * ε)
        = 2 ^ (q + 1) * (minorDiffC M * Ψ ^ (q + 1))
          + 2 ^ (q + 1) * (((L i).length + 1) * (2 ^ q * ((etaT E t)⁻¹ + 1)) * ε) := by
      ring
    rw [hsplit, hgain, hB]
    calc (2 * Ψ) ^ q * (2 * minorDiffC M * Ψ)
          + 2 ^ (q + 1) * (((L i).length + 1) * (2 ^ q * ((etaT E t)⁻¹ + 1)) * ε)
        ≤ (2 * Ψ) ^ q * (2 * minorDiffC M * Ψ) + (2 * Ψ) ^ q * condCost E t M Ψ ε := by
          linarith
      _ = (2 * minorDiffC M * Ψ + condCost E t M Ψ ε) * (2 * Ψ) ^ q := by ring
  -- the global envelope
  have hG : ∀ ω : Sizes.SeqΩ sz, ∏ i, ‖applyOps sz n (L i)
      (minorDiff sz n (qList (L i)) (flucDiagSet sz n u (zt E t) (mE E) (k i))) ω‖
      ≤ condEnv E t M ^ Fintype.card ι := by
    intro ω
    calc ∏ i, ‖applyOps sz n (L i)
          (minorDiff sz n (qList (L i)) (flucDiagSet sz n u (zt E t) (mE E) (k i)))
            ω‖
        ≤ ∏ _i : ι, condEnv E t M :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ =>
            norm_applyOps_minorDiff_flucDiagSet_le_condEnv hE ht u (k i) (L i) (hM i) ω
      _ = condEnv E t M ^ Fintype.card ι := by
          rw [Finset.prod_const, Finset.card_univ]
  have hbm : ∀ i : ι, BddMeas sz (applyOps sz n (L i)
      (minorDiff sz n (qList (L i)) (flucDiagSet sz n u (zt E t) (mE E) (k i)))) :=
    fun i => bddMeas_applyOps_minorDiff_flucDiagSet hE ht u (k i) (L i)
  have hb0 : ∀ i : ι, 0 ≤ B * (2 * Ψ) ^ numQ (L i) := fun i => by positivity
  refine le_trans (integral_prod_norm_le_of_bounds_on hbm (hfam.meas (M + 1)) hb0 hb hG) ?_
  have heq : (∏ i : ι, B * (2 * Ψ) ^ numQ (L i))
      = B ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum,
      Finset.card_univ]
  rw [heq]

end Moment

/-! ### The hypothesis is produced from the good event, not postulated -/

section Bridge

/-- The merged `Gres H z true` (a `Ring.inverse`) is `RBM.green H z = (H - z)⁻¹` (the private lemma
`flucIterHigh_Gres_true_eq_green` of `Green/MinorGoodLe.lean`, restated). -/
private theorem minorDiffCond_Gres_true {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (z : ℂ) : Gres H z true = green H z := by
  simp only [green, Gres, ↓reduceIte, Matrix.nonsing_inv_eq_ringInverse]

variable {E t δ : ℕ → ℝ}

/-- The base of the tower: a **measurable** hull of the complement of the per-time good event
`{ω | ∀ i j, llErrMat … i j ≤ δ n}` at the time `t n` (`‖G_{t n} - m‖_max ≤ δ n`, the paper's
`Ω(t,c)` of (4.1)).  This is RBM1D `badBase` (`MinorDiffCond:649`) with `goodSetFlow` on the
one-point interval replaced by the per-time event of `RBM2D/Green/IBPRem.lean` (`hΩ`).  Measures
in Mathlib are outer measures, so the hull has exactly the same measure as the complement itself
(`meas_badBase`), and a high-probability statement about the event bounds that. -/
noncomputable def badBase (sz : Sizes d) (E t δ : ℕ → ℝ) (n : ℕ) : Set (Sizes.SeqΩ sz) :=
  toMeasurable (Sizes.seqP sz)
    {ω : Sizes.SeqΩ sz | ∀ i j : Idx d (sz.L n) (sz.W n),
      llErrMat d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) i j ≤ δ n}ᶜ

theorem measurableSet_badBase (sz : Sizes d) (E t δ : ℕ → ℝ) (n : ℕ) :
    MeasurableSet (badBase sz E t δ n) := measurableSet_toMeasurable _ _

theorem meas_badBase (sz : Sizes d) (E t δ : ℕ → ℝ) (n : ℕ) :
    (Sizes.seqP sz) (badBase sz E t δ n)
      = (Sizes.seqP sz) {ω : Sizes.SeqΩ sz | ∀ i j : Idx d (sz.L n) (sz.W n),
          llErrMat d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) i j ≤ δ n}ᶜ :=
  measure_toMeasurable _

/-- **`hgood` is a theorem.**  Off the hull of the complement of the per-time good event, the
level-budgeted good event holds at threshold `2 δ n`.  This is `minorGoodLe_of_goodEvent_flow`
composed with the definitional identity of `llErrMat … i j ≤ δ` and `GoodEvent (green H z) m δ`
(the entry `‖G_{ij} - m 1_{i=j}‖`; RBM1D `minorGoodLe_of_notMem_badBase`, `MinorDiffCond:663`). -/
theorem minorGoodLe_of_notMem_badBase (hE : |E n| ≤ 2)
    (hz : (zt (E n) (t n)).im ≠ 0) {M : ℕ}
    (hδ0 : 0 ≤ δ n) (hδ4 : δ n ≤ 1 / 4) (hMδ : 8 * M * δ n ≤ 1)
    {ω : Sizes.SeqΩ sz} (hω : ω ∉ badBase sz E t δ n) :
    MinorGoodLe sz n (t n) (zt (E n) (t n)) (mE (E n)) ω (2 * δ n) M := by
  have hmem : ω ∈ {ω : Sizes.SeqΩ sz | ∀ i j : Idx d (sz.L n) (sz.W n),
      llErrMat d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) i j ≤ δ n} := by
    by_contra h
    exact hω (subset_toMeasurable (Sizes.seqP sz) _ h)
  have hG : GoodEvent (green (Sizes.seqHflow sz n (t n) ω) (zt (E n) (t n))) (mE (E n)) (δ n) := by
    intro i j
    have h := hmem i j
    simpa only [llErrMat, minorDiffCond_Gres_true] using h
  exact minorGoodLe_of_goodEvent_flow hE hz hδ0 hδ4 hMδ hG

end Bridge

/-! ### The conditionalized estimate, packaged as a budgeted interface

With the cardinality budget `#ι ≤ K` the additive remainder of `integral_prod_applyOps_minorDiff_le_on`
**is** absorbable, and the conditionalized (4.12) input becomes an interface again rather than an
inequality with a tail.  The arithmetic is the one the budget was introduced for:

  `condEnv^{#ι} P(Bad) ≤ condEnv^K P(Bad) ≤ B₀^K (2Ψ)^{KM} ≤ B₀^{#ι} (2Ψ)^{∑ q}`,

using `1 ≤ condEnv`, `#ι ≤ K`, `B₀ ≤ 1`, `2Ψ ≤ 1` and `∑ q ≤ #ι M ≤ K M`; the middle step is the
one genuine hypothesis, a smallness condition on the measure of the tower.  Adding the remainder to
the main term then costs a factor `2 ≤ 2^{#ι}`, i.e. `B = 2 B₀`, and the gain `ρ = 2Ψ` is
untouched.

At `#ι = 0` the bound `1 + P(Bad) ≤ 1` would be false, so that case is not routed through the
remainder at all: the integrand is an empty product, the integral of `1` against a probability
measure, and the conclusion is `1 ≤ 1`. -/

section Budget

variable {E t : ℝ}

theorem one_le_condEnv (hE : |E| < 2) (ht : t < 1) (M : ℕ) : 1 ≤ condEnv E t M := by
  have hη : 0 < etaT E t := etaT_pos hE ht
  have h1 : (1 : ℝ) ≤ 2 ^ (2 * M + 1) := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ (etaT E t)⁻¹ + 1 := by
    have := inv_nonneg.2 hη.le
    linarith
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ 2 ^ (2 * M + 1) * ((etaT E t)⁻¹ + 1) := by
        exact mul_le_mul h1 h2 zero_le_one (by positivity)
    _ = condEnv E t M := rfl

/-- **The row-section threshold that makes the conditionalization cost exactly `Ψ`.**

`condCost` is linear in `ε`, so there is one choice of the `BadFamily` threshold for which the
price of conditionalizing is the same `Ψ` as the gain itself; with it the constant of the budgeted
interface is `2(2 minorDiffC M + 1) Ψ`, i.e. `≍ Ψ`, which is the paper's size (RBM1D `condEps`,
`MinorDiffCond:727`). -/
noncomputable def condEps (E t : ℝ) (M : ℕ) (Ψ : ℝ) : ℝ :=
  Ψ * (2 * Ψ) ^ M * (((M : ℝ) + 1) * condEnv E t M)⁻¹

theorem condEps_nonneg (hE : |E| < 2) (ht : t < 1) (M : ℕ) {Ψ : ℝ} (hΨ : 0 ≤ Ψ) :
    0 ≤ condEps E t M Ψ := by
  have hEnv0 : 0 < condEnv E t M := lt_of_lt_of_le zero_lt_one (one_le_condEnv hE ht M)
  unfold condEps
  positivity

theorem condCost_condEps (hE : |E| < 2) (ht : t < 1) (M : ℕ) {Ψ : ℝ} (hΨ : 0 < Ψ) :
    condCost E t M Ψ (condEps E t M Ψ) = Ψ := by
  have hEnv0 : 0 < condEnv E t M := lt_of_lt_of_le zero_lt_one (one_le_condEnv hE ht M)
  have hMEnv : (0 : ℝ) < ((M : ℝ) + 1) * condEnv E t M := by positivity
  have h1 : ((2 * Ψ) ^ M : ℝ) ≠ 0 := by positivity
  have h2 : (((M : ℝ) + 1) * condEnv E t M) ≠ 0 := ne_of_gt hMEnv
  unfold condCost condEps
  calc ((M : ℝ) + 1) * condEnv E t M
          * (Ψ * (2 * Ψ) ^ M * (((M : ℝ) + 1) * condEnv E t M)⁻¹) * ((2 * Ψ) ^ M)⁻¹
      = (((M : ℝ) + 1) * condEnv E t M * (((M : ℝ) + 1) * condEnv E t M)⁻¹)
          * ((2 * Ψ) ^ M * ((2 * Ψ) ^ M)⁻¹) * Ψ := by ring
    _ = Ψ := by rw [mul_inv_cancel₀ h2, mul_inv_cancel₀ h1, mul_one, one_mul]

/-- **The conditionalized (4.12) input, as a budgeted interface.**

The hypotheses are those of `integral_prod_applyOps_minorDiff_le_on` plus the two that the
absorption needs: `hB1`, that the per-factor constant is at most `1` (automatic at
`B₀ ≍ Ψ → 0`), and `hsmall`, that the tower is small enough at the two budgets.  Neither is a
`∀ ω` hypothesis, and neither involves the index type.

The constant doubles, `B = 2 B₀`; the gain is exactly the `ρ = 2Ψ` of
`integral_prod_applyOps_minorDiff_le_on`, unchanged (RBM1D `minorDiffGainUpTo'_of_le_on`,
`MinorDiffCond:759`, with the budget `n` of RBM1D renamed `K`). -/
theorem minorDiffGainUpTo'_of_le_on
    (hE : |E| < 2) (ht : t < 1) (u : ℝ) {Ψ ε : ℝ} (hΨ0 : 0 < Ψ) (hΨhalf : 2 * Ψ ≤ 1)
    (hε : 0 ≤ ε) {M K : ℕ} {Bad : ℕ → Set (Sizes.SeqΩ sz)} (hfam : BadFamily sz n ε Bad)
    (hgood : ∀ ω ∉ Bad 0, MinorGoodLe sz n u (zt E t) (mE E) ω Ψ M)
    (hB1 : 2 * minorDiffC M * Ψ + condCost E t M Ψ ε ≤ 1)
    (hsmall : condEnv E t M ^ K * (Sizes.seqP sz).real (Bad (M + 1))
      ≤ (2 * minorDiffC M * Ψ + condCost E t M Ψ ε) ^ K * (2 * Ψ) ^ (K * M)) :
    MinorDiffGainUpTo' sz n u (zt E t) (mE E)
      (2 * (2 * minorDiffC M * Ψ + condCost E t M Ψ ε)) (2 * Ψ) M K := by
  classical
  have hΨ0' : (0 : ℝ) ≤ Ψ := hΨ0.le
  have h2Ψ0 : (0 : ℝ) < 2 * Ψ := by linarith
  have hcost0 : 0 ≤ condCost E t M Ψ ε := condCost_nonneg hE ht M hΨ0' hε
  have hC := minorDiffC_nonneg M
  set B₀ : ℝ := 2 * minorDiffC M * Ψ + condCost E t M Ψ ε with hB₀def
  have hB₀0 : 0 ≤ B₀ := by
    have : (0 : ℝ) ≤ 2 * minorDiffC M * Ψ := by positivity
    rw [hB₀def]; linarith
  refine ⟨by positivity, by positivity, fun ι _ k L h1 h2 hlen hcard => ?_⟩
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
  · have hemp : IsEmpty ι := Fintype.card_eq_zero_iff.1 h0
    simp [Finset.univ_eq_empty]
  · have hmain := integral_prod_applyOps_minorDiff_le_on hE ht u hΨ0 hΨhalf hε hfam hgood
      ι k L h1 h2 hlen
    refine hmain.trans ?_
    -- the sum of the gain exponents is at most `K * M`
    have hq : (∑ i, numQ (L i)) ≤ K * M := by
      have hstep : (∑ i, numQ (L i)) ≤ ∑ _i : ι, M :=
        Finset.sum_le_sum fun i _ => le_trans List.countP_le_length (hlen i)
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hstep
      exact le_trans hstep (Nat.mul_le_mul_right M hcard)
    have hEnv1 : 1 ≤ condEnv E t M := one_le_condEnv hE ht M
    have hPnn : 0 ≤ (Sizes.seqP sz).real (Bad (M + 1)) := measureReal_nonneg
    have hmainnn : 0 ≤ B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i) := by positivity
    -- the remainder is dominated by the main term
    have hrem : condEnv E t M ^ Fintype.card ι * (Sizes.seqP sz).real (Bad (M + 1))
        ≤ B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i) := by
      calc condEnv E t M ^ Fintype.card ι * (Sizes.seqP sz).real (Bad (M + 1))
          ≤ condEnv E t M ^ K * (Sizes.seqP sz).real (Bad (M + 1)) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hEnv1 hcard) hPnn
        _ ≤ B₀ ^ K * (2 * Ψ) ^ (K * M) := hsmall
        _ ≤ B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i) := by
            refine mul_le_mul (pow_le_pow_of_le_one hB₀0 hB1 hcard)
              (pow_le_pow_of_le_one h2Ψ0.le hΨhalf hq) (by positivity) (by positivity)
    -- and the doubling is paid by `2 ≤ 2 ^ #ι`
    have hdouble : (2 : ℝ) ≤ 2 ^ Fintype.card ι := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ Fintype.card ι := pow_le_pow_right₀ one_le_two hpos
    calc B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i)
            + condEnv E t M ^ Fintype.card ι * (Sizes.seqP sz).real (Bad (M + 1))
        ≤ B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i)
            + B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i) := by linarith
      _ = 2 * (B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i)) := by ring
      _ ≤ 2 ^ Fintype.card ι * (B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i)) :=
          mul_le_mul_of_nonneg_right hdouble hmainnn
      _ = (2 * B₀) ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i) := by
          rw [mul_pow (2 : ℝ) B₀ (Fintype.card ι)]; ring

end Budget

/-! ### The budgeted interface, produced from the per-time good event

The composition of `minorDiffGainUpTo'_of_le_on` with the bridge of the previous section: the
*only* probabilistic input is the per-time good event `{ω | ∀ i j, llErrMat … i j ≤ δ n}` (the
paper's `Ω(t,c)` of (4.1) at the time `t n`), there is **no** hypothesis quantified over all sample
points, and the exceptional set charged is the explicit tower `badTower` over the measurable hull
of its complement.  The residual hypothesis `hsmall` is a statement about the *measure* of that
tower, which `meas_badTower_le` bounds by `((ε + size n)/ε)^{M+1} P(Ω(t,c)ᶜ)`: super-polynomially
small for each fixed pair of budgets (the high-probability input of the event is a separate gate,
G4.12). -/

section Endpoints

variable {E t δ : ℕ → ℝ}

/-- **`MinorDiffGainUpTo'` from the per-time good event (4.1)** (RBM1D
`minorDiffGainUpTo'_goodSetFlow`, `MinorDiffCond:834`, at the time `t n`). -/
theorem minorDiffGainUpTo'_goodEvent (hE : |E n| < 2) (ht1 : t n < 1) {ε : ℝ} (hε : 0 ≤ ε)
    {M K : ℕ} (hδ0 : 0 < δ n) (hδ4 : δ n ≤ 1 / 4) (hMδ : 8 * M * δ n ≤ 1)
    (hB1 : 2 * minorDiffC M * (2 * δ n) + condCost (E n) (t n) M (2 * δ n) ε ≤ 1)
    (hsmall : condEnv (E n) (t n) M ^ K
        * (Sizes.seqP sz).real (badTower sz n ε (badBase sz E t δ n) (M + 1))
      ≤ (2 * minorDiffC M * (2 * δ n) + condCost (E n) (t n) M (2 * δ n) ε) ^ K
          * (2 * (2 * δ n)) ^ (K * M)) :
    MinorDiffGainUpTo' sz n (t n) (zt (E n) (t n)) (mE (E n))
      (2 * (2 * minorDiffC M * (2 * δ n) + condCost (E n) (t n) M (2 * δ n) ε))
      (2 * (2 * δ n)) M K := by
  have hz : (zt (E n) (t n)).im ≠ 0 := by
    rw [zt_im]; exact ne_of_gt (etaT_pos hE ht1)
  exact minorDiffGainUpTo'_of_le_on (E := E n) (t := t n) hE ht1 (t n) (Ψ := 2 * δ n)
    (by linarith) (by linarith) hε
    (badFamily_badTower sz n ε (measurableSet_badBase sz E t δ n))
    (fun ω hω => minorGoodLe_of_notMem_badBase hE.le hz hδ0.le hδ4 hMδ hω) hB1 hsmall

/-- **`FlucGainUpTo'` from the per-time good event (4.1)**: the interface consumed by the
`2p`-th moment expansion (G4.11, G4.12), with every hypothesis produced from (4.1) at the time
`t n` and explicit numeric side conditions (RBM1D `flucGainUpTo'_goodSetFlow`,
`MinorDiffCond:855`). -/
theorem flucGainUpTo'_goodEvent (hE : |E n| < 2) (ht1 : t n < 1) {ε : ℝ} (hε : 0 ≤ ε)
    {M K : ℕ} (hδ0 : 0 < δ n) (hδ4 : δ n ≤ 1 / 4) (hMδ : 8 * M * δ n ≤ 1)
    (hB1 : 2 * minorDiffC M * (2 * δ n) + condCost (E n) (t n) M (2 * δ n) ε ≤ 1)
    (hsmall : condEnv (E n) (t n) M ^ K
        * (Sizes.seqP sz).real (badTower sz n ε (badBase sz E t δ n) (M + 1))
      ≤ (2 * minorDiffC M * (2 * δ n) + condCost (E n) (t n) M (2 * δ n) ε) ^ K
          * (2 * (2 * δ n)) ^ (K * M)) :
    FlucGainUpTo' sz n (t n) (zt (E n) (t n)) (mE (E n))
      (2 * (2 * minorDiffC M * (2 * δ n) + condCost (E n) (t n) M (2 * δ n) ε))
      (2 * (2 * δ n)) M K :=
  flucGainUpTo'_of_minorDiffGainUpTo' (E := E n) (t := t n) hE ht1 (t n)
    (minorDiffGainUpTo'_goodEvent hE ht1 hε hδ0 hδ4 hMδ hB1 hsmall)

end Endpoints

/-! ### Compiled nonempty instances at `d = 3`, `L = 3`, `W = 2`

`RBM.Green.MinorDiffCondInst.szC` is the constant size sequence `d = 3`, `L n = 3`, `W n = 2`,
`lam n = 1/2`, at the slice `n = 0`: `size 0 = (W L)^3 = 216` rows (`inst_size`), `W^d = 8`.

* **Targets** `minorDiffGainUpTo'_goodEvent`, `flucGainUpTo'_goodEvent` at a positive time
  (`inst_minorDiffGain_pos`, `inst_flucGain_pos`, `inst_gain_applied_pos`): `E = 0`,
  `t = 10^{-8}`, `M = 0`, `K = 2`, `δ = 1/64`, `Ψ = 1/32`, `ε = condEps`.  Every deterministic
  hypothesis is discharged (`hB1` reads `17/32 ≤ 1`); the conclusion is at `(B, ρ) = (17/16, 1/16)`.
  `hsmall` stays a hypothesis: it is the owed high-probability input `P(Ω^c) ≤ N^{-D}` of
  `lem_GbEXP` (G4.12), true at these data (prove report: a Gaussian union bound gives
  `P(badBase) ≤ 3.7·10^{-8}`, pushed through `meas_badTower_le`).  At `t > 0` the flow does not
  vanish, and `G_{kk} - m` is not identically zero.
* The same targets at `t = 0` (`inst_minorDiffGain`, `inst_flucGain`, `inst_gain_applied`) with
  `hsmall` proved (`inst_hsmall`), at `M = 1`, `K = 2`, `δ = 2^{-20}`.  These are **collapsed**: at
  `t = 0` the flow vanishes, `H_0 = 0`, `G = m 1`, so `flucDiagSet` and every word applied to its
  minor differences are identically `0`, and the conclusion reduces to `0 ≤ B^{#ι} ρ^{Σ q}`.  They
  only check that the hypotheses can be discharged together at `t = 0`.
* **`meas_badStep_le`, `meas_badTower_le`, `badFamily_badTower`** at a half-space
  `S = {ω | ω_c < 0}` (a single Gaussian coordinate, `c = (0, ((0,0,0), (0,0,1), true))`), `ε = 1`,
  two letters, `size 0 = 216` rows.
* **`norm_applyOps_le_badFamily`, `norm_applyOps_minorDiff_flucDiagSet_le_condEnv`,
  `integral_prod_applyOps_minorDiff_le_on`** at `u = t = 1/2` (`…_half`), where the flow does not
  vanish; every hypothesis is discharged (`hgood` of the moment bound from
  `minorGoodLe_of_notMem_badBase`).  The `u = t = 0` instances of the same three theorems are
  collapsed in the same way as above (the left sides are `0`).
There is no external hypothesis besides `hsmall` at `t > 0`. -/

namespace MinorDiffCondInst

noncomputable section

/-- The sizes `d = 3`, `L = 3`, `W = 2`, `lam = 1/2` (constant sequences). -/
private def szC : Sizes 3 where
  L := fun _ => 3
  W := fun _ => 2
  lam := fun _ => 1 / 2
  three_le_L := fun _ => le_rfl
  W_pos := fun _ => by norm_num

/-- Sites of the fine lattice `Z_6^3`. -/
private def siteA : Idx 3 (szC.L 0) (szC.W 0) := ![0, 0, 0]
private def siteB : Idx 3 (szC.L 0) (szC.W 0) := ![0, 0, 1]
private def siteC : Idx 3 (szC.L 0) (szC.W 0) := ![0, 1, 0]

private theorem siteB_ne_siteA : siteB ≠ siteA := by decide
private theorem siteC_ne_siteA : siteC ≠ siteA := by decide
private theorem siteB_ne_siteC : siteB ≠ siteC := by decide

/-- `size 0 = (W L)^d = 216`. -/
theorem inst_size : szC.size 0 = 216 := by
  simp [Sizes.size, szC]

private theorem hE0 : |(0 : ℝ)| < 2 := by norm_num

private theorem sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `m^{(0)} = i`. -/
private theorem mE_zero : mE 0 = Complex.I := by
  apply Complex.ext <;> simp [mE, sqrt_four]

/-- `z_0^{(0)} = i`. -/
private theorem zt_zero : zt 0 0 = Complex.I := by
  simp [zt, mE_zero]

/-- `η_0 = 1`. -/
private theorem etaT_zero : etaT 0 0 = 1 := by
  rw [etaT, mE_zero]; simp

/-- `H_0 = 0` at every sample point. -/
private theorem seqHflow_zero_time (ω : Sizes.SeqΩ szC) : Sizes.seqHflow szC 0 0 ω = 0 := by
  rw [Sizes.seqHflow_eq_smul]
  simp

/-- `G = (0 - i)⁻¹ = i 1`. -/
private theorem green_zero_I {ν : Type*} [Fintype ν] [DecidableEq ν] :
    green (0 : Matrix ν ν ℂ) Complex.I = Complex.I • (1 : Matrix ν ν ℂ) := by
  unfold green
  refine Matrix.inv_eq_right_inv ?_
  simp [smul_smul]

/-- `i • 1` satisfies (4.1) at `m = i` exactly, for every threshold `δ ≥ 0`. -/
private theorem goodEvent_I {ν : Type*} [DecidableEq ν] {δ : ℝ} (hδ : 0 ≤ δ) :
    GoodEvent (Complex.I • (1 : Matrix ν ν ℂ)) Complex.I δ := by
  intro x y
  by_cases h : x = y
  · subst h; simp [hδ]
  · simp [h, hδ]

/-- (4.1) at `E = 0`, `t = 0`: the entrywise error `llErrMat` vanishes at every sample point. -/
private theorem llErr_zero (ω : Sizes.SeqΩ szC) {δ : ℝ} (hδ : 0 ≤ δ)
    (i j : Idx 3 (szC.L 0) (szC.W 0)) :
    llErrMat 3 (szC.L 0) (szC.W 0) 0 0 (Sizes.seqHflow szC 0 0 ω) i j ≤ δ := by
  have h : GoodEvent (green (Sizes.seqHflow szC 0 0 ω) (zt 0 0)) (mE 0) δ := by
    rw [seqHflow_zero_time, zt_zero, mE_zero, green_zero_I]
    exact goodEvent_I hδ
  have := h i j
  simpa only [llErrMat, minorDiffCond_Gres_true] using this

/-- The base of the tower is a null set at `t = 0`: the good event is the whole space. -/
theorem inst_badBase_null {δ : ℝ} (hδ : 0 ≤ δ) :
    (Sizes.seqP szC) (badBase szC (fun _ => 0) (fun _ => 0) (fun _ => δ) 0) = 0 := by
  rw [meas_badBase]
  have huniv : {ω : Sizes.SeqΩ szC | ∀ i j : Idx 3 (szC.L 0) (szC.W 0),
      llErrMat 3 (szC.L 0) (szC.W 0) 0 0 (Sizes.seqHflow szC 0 0 ω) i j ≤ δ} = Set.univ :=
    Set.eq_univ_of_forall fun ω i j => llErr_zero ω hδ i j
  simp only [huniv, Set.compl_univ, measure_empty]

/-- The numbers: `condEnv 0 0 1 = 2³ (1⁻¹ + 1) = 16`. -/
theorem inst_condEnv : condEnv 0 0 1 = 16 := by
  unfold condEnv
  rw [etaT_zero]
  norm_num

/-- The constants: `minorDiffC 1 = 131072 = 4 · 32³`. -/
theorem inst_minorDiffC_one : minorDiffC 1 = 131072 := by
  unfold minorDiffC
  norm_num [atomC]

/-- `condEps` at `M = 1`, `Ψ = 2^{-19}`: `ε = Ψ (2Ψ) / (2 · 16) = 2^{-42}`. -/
theorem inst_condEps : condEps 0 0 1 (2 * (1 / 1048576 : ℝ)) = 1 / 4398046511104 := by
  unfold condEps
  rw [inst_condEnv]
  norm_num

/-- `condCost` at `ε = condEps` is `Ψ` (`condCost_condEps`), here `Ψ = 2^{-19}`. -/
theorem inst_condCost :
    condCost 0 0 1 (2 * (1 / 1048576 : ℝ)) (condEps 0 0 1 (2 * (1 / 1048576 : ℝ)))
      = 2 * (1 / 1048576 : ℝ) :=
  condCost_condEps (by norm_num) (by norm_num) 1 (by norm_num)

private theorem inst_hε : (0 : ℝ) ≤ condEps 0 0 1 (2 * (1 / 1048576 : ℝ)) := by
  rw [inst_condEps]; norm_num

/-- `hB1`: `2 C_1 Ψ + Ψ = 262145/524288 ≤ 1`. -/
private theorem inst_hB1 :
    2 * minorDiffC 1 * (2 * (1 / 1048576 : ℝ))
      + condCost 0 0 1 (2 * (1 / 1048576 : ℝ)) (condEps 0 0 1 (2 * (1 / 1048576 : ℝ))) ≤ 1 := by
  rw [inst_condCost, inst_minorDiffC_one]; norm_num

/-- The constant of the conclusion: `B = 2 (2 C_1 Ψ + Ψ) = 262145/262144`. -/
private theorem inst_B :
    2 * (2 * minorDiffC 1 * (2 * (1 / 1048576 : ℝ))
      + condCost 0 0 1 (2 * (1 / 1048576 : ℝ)) (condEps 0 0 1 (2 * (1 / 1048576 : ℝ))))
      = 262145 / 262144 := by
  rw [inst_condCost, inst_minorDiffC_one]; norm_num

/-- Every tower over the null base is null (`meas_badTower_le` with `ε > 0`). -/
private theorem inst_badTower_null (j : ℕ) :
    (Sizes.seqP szC)
      (badTower szC 0 (condEps 0 0 1 (2 * (1 / 1048576 : ℝ)))
        (badBase szC (fun _ => 0) (fun _ => 0) (fun _ => 1 / 1048576) 0) j) = 0 := by
  have hε : (0 : ℝ) < condEps 0 0 1 (2 * (1 / 1048576 : ℝ)) := by
    rw [inst_condEps]; norm_num
  have h := meas_badTower_le szC 0 (ε := condEps 0 0 1 (2 * (1 / 1048576 : ℝ)))
    (measurableSet_badBase szC (fun _ => 0) (fun _ => 0) (fun _ => 1 / 1048576) 0) j
  rw [inst_badBase_null (by norm_num), mul_zero, nonpos_iff_eq_zero] at h
  rcases mul_eq_zero.1 h with h1 | h1
  · exact absurd h1 (pow_ne_zero _ (by simpa using hε))
  · exact h1

/-- **`hsmall`, proved at `t = 0`**: the left side is `condEnv^K · 0`. -/
private theorem inst_hsmall :
    condEnv 0 0 1 ^ 2 * (Sizes.seqP szC).real
        (badTower szC 0 (condEps 0 0 1 (2 * (1 / 1048576 : ℝ)))
          (badBase szC (fun _ => 0) (fun _ => 0) (fun _ => 1 / 1048576) 0) (1 + 1))
      ≤ (2 * minorDiffC 1 * (2 * (1 / 1048576 : ℝ))
          + condCost 0 0 1 (2 * (1 / 1048576 : ℝ))
              (condEps 0 0 1 (2 * (1 / 1048576 : ℝ)))) ^ 2
        * (2 * (2 * (1 / 1048576 : ℝ))) ^ (2 * 1) := by
  rw [Measure.real, inst_badTower_null, ENNReal.toReal_zero, mul_zero]
  positivity

/-- **Collapsed instance of `minorDiffGainUpTo'_goodEvent`** (target) at `t = 0`: `d = 3`, `L = 3`,
`W = 2`, `n = 0`, `E = t = 0`, `M = 1`, `K = 2`, `δ = 2^{-20}`, `ε = condEps = 2^{-42}`; every
hypothesis is discharged (`inst_hB1`, `inst_hsmall`), at `(B, ρ) = (262145/262144, 2^{-18})`.  At
`t = 0` the integrand is identically `0` (`H_0 = 0`), so the conclusion holds trivially; the
instance at a positive time is `inst_minorDiffGain_pos`. -/
theorem inst_minorDiffGain :
    MinorDiffGainUpTo' szC 0 0 (zt 0 0) (mE 0) (262145 / 262144) (2 * (2 * (1 / 1048576 : ℝ)))
      1 2 := by
  have h := minorDiffGainUpTo'_goodEvent (sz := szC) (n := 0) (E := fun _ => 0) (t := fun _ => 0)
    (δ := fun _ => 1 / 1048576) (ε := condEps 0 0 1 (2 * (1 / 1048576 : ℝ))) (M := 1) (K := 2)
    hE0 (by norm_num) inst_hε (by norm_num) (by norm_num) (by norm_num) inst_hB1 inst_hsmall
  rwa [inst_B] at h

/-- **Collapsed instance of `flucGainUpTo'_goodEvent`** (target) at `t = 0`: the same data; the
conclusion is `FlucGainUpTo'` at `(B, ρ) = (262145/262144, 2^{-18})`, trivially true at `t = 0`;
the instance at a positive time is `inst_flucGain_pos`. -/
theorem inst_flucGain :
    FlucGainUpTo' szC 0 0 (zt 0 0) (mE 0) (262145 / 262144) (2 * (2 * (1 / 1048576 : ℝ)))
      1 2 := by
  have h := flucGainUpTo'_goodEvent (sz := szC) (n := 0) (E := fun _ => 0) (t := fun _ => 0)
    (δ := fun _ => 1 / 1048576) (ε := condEps 0 0 1 (2 * (1 / 1048576 : ℝ))) (M := 1) (K := 2)
    hE0 (by norm_num) inst_hε (by norm_num) (by norm_num) (by norm_num) inst_hB1 inst_hsmall
  rwa [inst_B] at h

/-! #### The tower, its measure, the word estimate, the moment bound -/

/-- The half-space `{ω | ω_c < 0}` of one Gaussian coordinate `c = (0, ((0,0,0), (0,0,1), true))`:
a measurable set that is neither empty nor the whole space, with `0 ∉ S`. -/
private def halfS : Set (Sizes.SeqΩ szC) :=
  {ω | ω (⟨0, (siteA, siteB, true)⟩ : Sizes.SeqCoord szC) < 0}

private theorem measurableSet_halfS : MeasurableSet halfS :=
  measurableSet_lt (measurable_pi_apply _) measurable_const

/-- **Instance of `meas_badStep_le`**: `ε = 1`, `S = halfS`, row count `#Idx`. -/
theorem inst_meas_badStep :
    ENNReal.ofReal 1 * (Sizes.seqP szC) (badStep szC 0 1 halfS)
      ≤ (ENNReal.ofReal 1 + (Fintype.card (Idx 3 (szC.L 0) (szC.W 0)) : ℝ≥0∞))
          * (Sizes.seqP szC) halfS :=
  meas_badStep_le szC 0 measurableSet_halfS

/-- **Instance of `meas_badTower_le`**: two letters, row count `#Idx`. -/
theorem inst_meas_badTower :
    ENNReal.ofReal 1 ^ 2 * (Sizes.seqP szC) (badTower szC 0 1 halfS 2)
      ≤ (ENNReal.ofReal 1 + (Fintype.card (Idx 3 (szC.L 0) (szC.W 0)) : ℝ≥0∞)) ^ 2
          * (Sizes.seqP szC) halfS :=
  meas_badTower_le szC 0 measurableSet_halfS 2

/-- The `size n` forms, with `size 0 = 216` rows. -/
theorem inst_meas_badTower_size :
    ENNReal.ofReal 1 ^ 2 * (Sizes.seqP szC) (badTower szC 0 1 halfS 2)
      ≤ (ENNReal.ofReal 1 + (216 : ℝ≥0∞)) ^ 2 * (Sizes.seqP szC) halfS := by
  have h := minorDiffCond_meas_badTower_le_size szC 0 (ε := 1) measurableSet_halfS 2
  rwa [inst_size] at h

/-- **Instance of `badFamily_badTower`** (and `BadFamily.mono_le`). -/
theorem inst_badFamily :
    BadFamily szC 0 1 (badTower szC 0 1 halfS)
      ∧ badTower szC 0 1 halfS 0 ⊆ badTower szC 0 1 halfS 3 :=
  ⟨badFamily_badTower szC 0 1 measurableSet_halfS,
    (badFamily_badTower szC 0 1 measurableSet_halfS).mono_le (by norm_num)⟩

/-- At `ε = 1` nothing is added to the complement of `S`: row sections have probability `≤ 1`. -/
private theorem notMem_badStep_one {S : Set (Sizes.SeqΩ szC)} {ω : Sizes.SeqΩ szC}
    (h : ω ∉ S) : ω ∉ badStep szC 0 1 S := by
  intro hmem
  rcases hmem with hS | hU
  · exact h hS
  · obtain ⟨κ, hκ⟩ := Set.mem_iUnion.1 hU
    exact absurd (measureReal_le_one (μ := Sizes.seqP szC)) (not_le.2 hκ)

private theorem zero_notMem_tower (j : ℕ) :
    (0 : Sizes.SeqΩ szC) ∉ badTower szC 0 1 halfS j := by
  induction j with
  | zero => simp [halfS]
  | succ k ih => exact notMem_badStep_one ih

private theorem hEnv_flucDiagSet (ω : Sizes.SeqΩ szC) :
    ‖flucDiagSet szC 0 0 (zt 0 0) (mE 0) siteA ∅ ω‖ ≤ 4 := by
  have h := norm_flucDiagSet_le_env (sz := szC) (n := 0) (E := 0) (t := 0) hE0 (by norm_num) 0
    siteA ∅ ω
  have hη : (zt 0 0).im = 1 := by rw [zt_zero]; simp
  rw [hη] at h
  norm_num at h
  exact h

/-- **Collapsed instance (`u = 0`, `X ≡ 0`) of `norm_applyOps_le_badFamily`**: `X = Z^{(∅)}_{(0,0,0)}` (`flucDiagSet`, envelope
`Env = c = 4`), the family `badTower 1 halfS`, the word `Q_{(0,0,1)} P_{(0,1,0)}` of two letters,
at the sample point `ω = 0 ∉ halfS`. -/
theorem inst_norm_applyOps_le_badFamily :
    ‖applyOps szC 0 ([(true, siteB), (false, siteC)] : List (Bool × Idx 3 (szC.L 0) (szC.W 0)))
        (flucDiagSet szC 0 0 (zt 0 0) (mE 0) siteA ∅) 0‖
      ≤ 2 ^ numQ ([(true, siteB), (false, siteC)] : List (Bool × Idx 3 (szC.L 0) (szC.W 0)))
          * (4 + (([(true, siteB), (false, siteC)] :
              List (Bool × Idx 3 (szC.L 0) (szC.W 0))).length : ℝ) * 4 * 1) :=
  norm_applyOps_le_badFamily (X := flucDiagSet szC 0 0 (zt 0 0) (mE 0) siteA ∅)
    (bddMeas_flucDiagSet hE0 (by norm_num) 0 siteA ∅)
    (Bad := badTower szC 0 1 halfS) (ε := 1) (Env := 4) (c := 4)
    (badFamily_badTower szC 0 1 measurableSet_halfS) hEnv_flucDiagSet (by norm_num)
    zero_le_one (fun ω _ => hEnv_flucDiagSet ω) _ 0 (zero_notMem_tower _)

/-- **Collapsed instance (`u = 0`, left side `≡ 0`) of
`norm_applyOps_minorDiff_flucDiagSet_le_condEnv`**: the word `Q_{(0,0,1)}
P_{(0,1,0)}` (length `2 ≤ M = 2`) at the slot `k = (0,0,0)`, every sample point. -/
theorem inst_envelope (ω : Sizes.SeqΩ szC) :
    ‖applyOps szC 0 ([(true, siteB), (false, siteC)] : List (Bool × Idx 3 (szC.L 0) (szC.W 0)))
        (minorDiff szC 0
          (qList ([(true, siteB), (false, siteC)] : List (Bool × Idx 3 (szC.L 0) (szC.W 0))))
          (flucDiagSet szC 0 0 (zt 0 0) (mE 0) siteA)) ω‖
      ≤ condEnv 0 0 2 :=
  norm_applyOps_minorDiff_flucDiagSet_le_condEnv hE0 (by norm_num) 0 (M := 2) siteA _
    (by simp) ω

/-- `condEnv 0 0 2 = 2^5 (1⁻¹ + 1) = 64`. -/
theorem inst_condEnv_two : condEnv 0 0 2 = 64 := by
  unfold condEnv
  rw [etaT_zero]
  norm_num

/-- **Collapsed instance (integrand `≡ 0`) of `integral_prod_applyOps_minorDiff_le_on`**: `E = t = u = 0`, `Ψ = 2^{-19}`,
`ε = condEps`, `M = 1`, the family `badTower ε badBase`, `hgood` from the bridge
`minorGoodLe_of_notMem_badBase`; one slot `ι = Fin 1` at `k = (0,0,0)` with the word
`Q_{(0,0,1)}`. -/
example :=
  integral_prod_applyOps_minorDiff_le_on (sz := szC) (n := 0) (E := 0) (t := 0) hE0
    (by norm_num) 0 (Ψ := 2 * (1 / 1048576 : ℝ)) (ε := condEps 0 0 1 (2 * (1 / 1048576 : ℝ)))
    (by norm_num) (by norm_num) inst_hε (M := 1)
    (Bad := badTower szC 0 (condEps 0 0 1 (2 * (1 / 1048576 : ℝ)))
      (badBase szC (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) (fun _ => 1 / 1048576) 0))
    (badFamily_badTower szC 0 _ (measurableSet_badBase szC _ _ _ 0))
    (fun ω hω => minorGoodLe_of_notMem_badBase (sz := szC) (n := 0) (E := fun _ => (0 : ℝ))
      (t := fun _ => (0 : ℝ)) (δ := fun _ => 1 / 1048576) (M := 1) hE0.le
      (by rw [zt_zero]; simp) (by norm_num) (by norm_num) (by norm_num) hω)
    (Fin 1) (fun _ => siteA) (fun _ => [(true, siteB)]) (by simp)
    (by simp [siteB_ne_siteA]) (by simp)

/-- **The conclusion of `inst_minorDiffGain` applied** (collapsed: the integrand is `0` at `t = 0`) to one slot `ι = Fin 1` at the row
`(0,0,0)` and the word `Q_{(0,0,1)}`: the integral is at most `B^1 ρ^1`. -/
theorem inst_gain_applied :
    ∫ ω, ∏ _i : Fin 1, ‖applyOps szC 0 [(true, siteB)]
        (minorDiff szC 0 (qList [(true, siteB)]) (flucDiagSet szC 0 0 (zt 0 0) (mE 0) siteA)) ω‖
        ∂(Sizes.seqP szC)
      ≤ (262145 / 262144 : ℝ) ^ Fintype.card (Fin 1)
          * (2 * (2 * (1 / 1048576 : ℝ))) ^ ∑ _i : Fin 1, numQ [(true, siteB)] :=
  inst_minorDiffGain.2.2 (Fin 1) (fun _ => siteA) (fun _ => [(true, siteB)]) (by simp)
    (by simp [siteB_ne_siteA]) (by simp) (by simp)


/-! #### Instances at a positive time (the flow does not vanish) -/

/-- `z_{1/2}^{(0)} = i/2`, so `Im z = 1/2 ≠ 0`. -/
private theorem zt_half_im : (zt 0 (1 / 2)).im = 1 / 2 := by
  simp [zt, mE_zero]; norm_num

/-- `η_{1/2} = 1/2`. -/
private theorem etaT_half : etaT 0 (1 / 2) = 1 / 2 := by
  rw [etaT, mE_zero]; norm_num

/-- `condEnv 0 (1/2) 2 = 2^5 (2 + 1) = 96`. -/
theorem inst_condEnv_half : condEnv 0 (1 / 2) 2 = 96 := by
  unfold condEnv
  rw [etaT_half]
  norm_num

/-- **Instance of `norm_applyOps_minorDiff_flucDiagSet_le_condEnv` at `u = t = 1/2`**: the word
`Q_{(0,0,1)} P_{(0,1,0)}` (length `2 ≤ M = 2`) at the slot `k = (0,0,0)`, every sample point;
`H_{1/2} = √(1/2) X`, `z = i/2`. -/
theorem inst_envelope_half (ω : Sizes.SeqΩ szC) :
    ‖applyOps szC 0 ([(true, siteB), (false, siteC)] : List (Bool × Idx 3 (szC.L 0) (szC.W 0)))
        (minorDiff szC 0
          (qList ([(true, siteB), (false, siteC)] : List (Bool × Idx 3 (szC.L 0) (szC.W 0))))
          (flucDiagSet szC 0 (1 / 2) (zt 0 (1 / 2)) (mE 0) siteA)) ω‖
      ≤ 96 := by
  rw [← inst_condEnv_half]
  exact norm_applyOps_minorDiff_flucDiagSet_le_condEnv hE0 (by norm_num) (1 / 2) (M := 2) siteA _
    (by simp) ω

private theorem hEnv_flucDiagSet_half (ω : Sizes.SeqΩ szC) :
    ‖flucDiagSet szC 0 (1 / 2) (zt 0 (1 / 2)) (mE 0) siteA ∅ ω‖ ≤ 6 := by
  have h := norm_flucDiagSet_le_env (sz := szC) (n := 0) (E := 0) (t := 1 / 2) hE0 (by norm_num)
    (1 / 2) siteA ∅ ω
  rw [zt_half_im] at h
  norm_num at h
  exact h

/-- **Instance of `norm_applyOps_le_badFamily` at `u = t = 1/2`**: `X = Z^{(∅)}_{(0,0,0)}`
(`flucDiagSet`, envelope `Env = c = 2 (2 + 1) = 6`), the family `badTower 1 halfS`, the word
`Q_{(0,0,1)} P_{(0,1,0)}` of two letters, at every sample point off the tower (`0` is one,
`zero_notMem_tower`). -/
theorem inst_norm_applyOps_le_badFamily_half (ω : Sizes.SeqΩ szC)
    (hω : ω ∉ badTower szC 0 1 halfS 2) :
    ‖applyOps szC 0 ([(true, siteB), (false, siteC)] : List (Bool × Idx 3 (szC.L 0) (szC.W 0)))
        (flucDiagSet szC 0 (1 / 2) (zt 0 (1 / 2)) (mE 0) siteA ∅) ω‖
      ≤ 2 ^ numQ ([(true, siteB), (false, siteC)] : List (Bool × Idx 3 (szC.L 0) (szC.W 0)))
          * (6 + (([(true, siteB), (false, siteC)] :
              List (Bool × Idx 3 (szC.L 0) (szC.W 0))).length : ℝ) * 6 * 1) :=
  norm_applyOps_le_badFamily (X := flucDiagSet szC 0 (1 / 2) (zt 0 (1 / 2)) (mE 0) siteA ∅)
    (bddMeas_flucDiagSet hE0 (by norm_num) (1 / 2) siteA ∅)
    (Bad := badTower szC 0 1 halfS) (ε := 1) (Env := 6) (c := 6)
    (badFamily_badTower szC 0 1 measurableSet_halfS) hEnv_flucDiagSet_half (by norm_num)
    zero_le_one (fun ω _ => hEnv_flucDiagSet_half ω) _ ω hω

/-- **Instance of `integral_prod_applyOps_minorDiff_le_on` at `u = t = 1/2`**: `E = 0`, `M = 1`,
`δ = 1/16`, `Ψ = 2δ = 1/8`, `ε = condEps 0 (1/2) 1 (1/8)`, the family `badTower ε badBase` over the
per-time good event at `t = 1/2`, `hgood` from `minorGoodLe_of_notMem_badBase`; one slot
`ι = Fin 1` at `k = (0,0,0)` with the word `Q_{(0,0,1)}`. -/
theorem inst_integral_prod_half :
    ∫ ω, ∏ _i : Fin 1, ‖applyOps szC 0 [(true, siteB)]
        (minorDiff szC 0 (qList [(true, siteB)])
          (flucDiagSet szC 0 (1 / 2) (zt 0 (1 / 2)) (mE 0) siteA)) ω‖ ∂(Sizes.seqP szC)
      ≤ (2 * minorDiffC 1 * (1 / 8) + condCost 0 (1 / 2) 1 (1 / 8) (condEps 0 (1 / 2) 1 (1 / 8)))
            ^ Fintype.card (Fin 1) * (2 * (1 / 8)) ^ ∑ _i : Fin 1, numQ [(true, siteB)]
        + condEnv 0 (1 / 2) 1 ^ Fintype.card (Fin 1) * (Sizes.seqP szC).real
            (badTower szC 0 (condEps 0 (1 / 2) 1 (1 / 8))
              (badBase szC (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 1 / 16) 0)
              (1 + 1)) := by
  have h := integral_prod_applyOps_minorDiff_le_on (sz := szC) (n := 0) (E := 0) (t := 1 / 2) hE0
    (by norm_num) (1 / 2) (Ψ := 1 / 8) (ε := condEps 0 (1 / 2) 1 (1 / 8))
    (by norm_num) (by norm_num) (condEps_nonneg hE0 (by norm_num) 1 (by norm_num)) (M := 1)
    (Bad := badTower szC 0 (condEps 0 (1 / 2) 1 (1 / 8))
      (badBase szC (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 1 / 16) 0))
    (badFamily_badTower szC 0 _ (measurableSet_badBase szC _ _ _ 0))
    (fun ω hω => by
      have := minorGoodLe_of_notMem_badBase (sz := szC) (n := 0) (E := fun _ => (0 : ℝ))
        (t := fun _ => (1 / 2 : ℝ)) (δ := fun _ => 1 / 16) (M := 1) (by norm_num)
        (by rw [zt_half_im]; norm_num) (by norm_num) (by norm_num) (by norm_num) hω
      norm_num at this ⊢
      exact this)
    (Fin 1) (fun _ => siteA) (fun _ => [(true, siteB)]) (by simp)
    (by simp [siteB_ne_siteA]) (by simp)
  exact h

/-! At `t = 10^{-8}`, `M = 0`, `K = 2`, `δ = 1/64` (`Ψ = 1/32`, `ε = condEps = Ψ / condEnv`):
`condCost = Ψ`, `hB1` is `2 · 8 · (1/32) + 1/32 = 17/32 ≤ 1`, `B = 17/16`, `ρ = 1/16`. -/

/-- `minorDiffC 0 = 4^0 · 2^3 = 8`. -/
theorem inst_minorDiffC_zero : minorDiffC 0 = 8 := by
  unfold minorDiffC
  norm_num [atomC]

private theorem inst_pos_cost :
    condCost 0 (1 / 100000000) 0 (2 * (1 / 64 : ℝ)) (condEps 0 (1 / 100000000) 0 (2 * (1 / 64 : ℝ)))
      = 2 * (1 / 64 : ℝ) :=
  condCost_condEps hE0 (by norm_num) 0 (by norm_num)

private theorem inst_pos_hB1 :
    2 * minorDiffC 0 * (2 * (1 / 64 : ℝ))
      + condCost 0 (1 / 100000000) 0 (2 * (1 / 64 : ℝ))
          (condEps 0 (1 / 100000000) 0 (2 * (1 / 64 : ℝ))) ≤ 1 := by
  rw [inst_pos_cost, inst_minorDiffC_zero]; norm_num

private theorem inst_pos_B :
    2 * (2 * minorDiffC 0 * (2 * (1 / 64 : ℝ))
      + condCost 0 (1 / 100000000) 0 (2 * (1 / 64 : ℝ))
          (condEps 0 (1 / 100000000) 0 (2 * (1 / 64 : ℝ)))) = 17 / 16 := by
  rw [inst_pos_cost, inst_minorDiffC_zero]; norm_num

/-- **Instance of `minorDiffGainUpTo'_goodEvent` at a positive time** (target): `d = 3`, `L = 3`,
`W = 2`, `n = 0`, `E = 0`, `t = 10^{-8}`, `M = 0`, `K = 2`, `δ = 1/64`, `ε = condEps`.  Every
deterministic hypothesis is discharged; `hsmall` (the owed input of G4.12) is a hypothesis, true at
these data (prove report).  The conclusion is `MinorDiffGainUpTo'` at `(B, ρ) = (17/16, 1/16)`. -/
theorem inst_minorDiffGain_pos
    (hsmall : condEnv 0 (1 / 100000000) 0 ^ 2 * (Sizes.seqP szC).real
        (badTower szC 0 (condEps 0 (1 / 100000000) 0 (2 * (1 / 64 : ℝ)))
          (badBase szC (fun _ => 0) (fun _ => 1 / 100000000) (fun _ => 1 / 64) 0) (0 + 1))
      ≤ (2 * minorDiffC 0 * (2 * (1 / 64 : ℝ))
          + condCost 0 (1 / 100000000) 0 (2 * (1 / 64 : ℝ))
              (condEps 0 (1 / 100000000) 0 (2 * (1 / 64 : ℝ)))) ^ 2
        * (2 * (2 * (1 / 64 : ℝ))) ^ (2 * 0)) :
    MinorDiffGainUpTo' szC 0 (1 / 100000000) (zt 0 (1 / 100000000)) (mE 0) (17 / 16)
      (2 * (2 * (1 / 64 : ℝ))) 0 2 := by
  have h := minorDiffGainUpTo'_goodEvent (sz := szC) (n := 0) (E := fun _ => 0)
    (t := fun _ => 1 / 100000000) (δ := fun _ => 1 / 64)
    (ε := condEps 0 (1 / 100000000) 0 (2 * (1 / 64 : ℝ))) (M := 0) (K := 2)
    hE0 (by norm_num) (condEps_nonneg hE0 (by norm_num) 0 (by norm_num)) (by norm_num)
    (by norm_num) (by norm_num) inst_pos_hB1 hsmall
  rwa [inst_pos_B] at h

/-- **Instance of `flucGainUpTo'_goodEvent` at a positive time** (target): the same data and the
same `hsmall`; the conclusion is `FlucGainUpTo'` at `(B, ρ) = (17/16, 1/16)`. -/
theorem inst_flucGain_pos
    (hsmall : condEnv 0 (1 / 100000000) 0 ^ 2 * (Sizes.seqP szC).real
        (badTower szC 0 (condEps 0 (1 / 100000000) 0 (2 * (1 / 64 : ℝ)))
          (badBase szC (fun _ => 0) (fun _ => 1 / 100000000) (fun _ => 1 / 64) 0) (0 + 1))
      ≤ (2 * minorDiffC 0 * (2 * (1 / 64 : ℝ))
          + condCost 0 (1 / 100000000) 0 (2 * (1 / 64 : ℝ))
              (condEps 0 (1 / 100000000) 0 (2 * (1 / 64 : ℝ)))) ^ 2
        * (2 * (2 * (1 / 64 : ℝ))) ^ (2 * 0)) :
    FlucGainUpTo' szC 0 (1 / 100000000) (zt 0 (1 / 100000000)) (mE 0) (17 / 16)
      (2 * (2 * (1 / 64 : ℝ))) 0 2 := by
  have h := flucGainUpTo'_goodEvent (sz := szC) (n := 0) (E := fun _ => 0)
    (t := fun _ => 1 / 100000000) (δ := fun _ => 1 / 64)
    (ε := condEps 0 (1 / 100000000) 0 (2 * (1 / 64 : ℝ))) (M := 0) (K := 2)
    hE0 (by norm_num) (condEps_nonneg hE0 (by norm_num) 0 (by norm_num)) (by norm_num)
    (by norm_num) (by norm_num) inst_pos_hB1 hsmall
  rwa [inst_pos_B] at h

/-- **The conclusion of `inst_minorDiffGain_pos` applied** to two slots `ι = Fin 2` at the rows
`(0,0,0)`, `(0,0,1)` with empty words: `E |Z_{(0,0,0)}| |Z_{(0,0,1)}| ≤ (17/16)^2` at `t = 10^{-8}`. -/
theorem inst_gain_applied_pos
    (hsmall : condEnv 0 (1 / 100000000) 0 ^ 2 * (Sizes.seqP szC).real
        (badTower szC 0 (condEps 0 (1 / 100000000) 0 (2 * (1 / 64 : ℝ)))
          (badBase szC (fun _ => 0) (fun _ => 1 / 100000000) (fun _ => 1 / 64) 0) (0 + 1))
      ≤ (2 * minorDiffC 0 * (2 * (1 / 64 : ℝ))
          + condCost 0 (1 / 100000000) 0 (2 * (1 / 64 : ℝ))
              (condEps 0 (1 / 100000000) 0 (2 * (1 / 64 : ℝ)))) ^ 2
        * (2 * (2 * (1 / 64 : ℝ))) ^ (2 * 0)) :
    ∫ ω, ∏ i : Fin 2, ‖applyOps szC 0 []
        (minorDiff szC 0 (qList []) (flucDiagSet szC 0 (1 / 100000000) (zt 0 (1 / 100000000))
          (mE 0) (![siteA, siteB] i))) ω‖ ∂(Sizes.seqP szC)
      ≤ (17 / 16 : ℝ) ^ Fintype.card (Fin 2)
          * (2 * (2 * (1 / 64 : ℝ))) ^ ∑ _i : Fin 2,
            numQ ([] : List (Bool × Idx 3 (szC.L 0) (szC.W 0))) :=
  (inst_minorDiffGain_pos hsmall).2.2 (Fin 2) ![siteA, siteB] (fun _ => []) (by simp) (by simp)
    (by simp) (by simp)

end

end MinorDiffCondInst

end RBM.Green
