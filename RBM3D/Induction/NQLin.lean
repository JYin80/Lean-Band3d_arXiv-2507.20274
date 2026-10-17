/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.NQBudget
import RBM3D.Induction.NQGood2
import RBM3D.Induction.GridGoodN
import RBM3D.Induction.SEforLn2
import RBM3D.Induction.AzumaProxyN

/-!
# Route (R) of the non-alternating endpoint (`d ≥ 3`): the linear good set `GoodLinN`, its
# exit time, the linear drift level, the sub-Gaussian input and the linear budget

Ticket T2186 (S3-12a, stochastic layer ST-3, first of three; the primed pins are in
`Induction/Step34PinsP`).  Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex`
(`3_5:line`): `lem:SEforLn` (`3_5:1017-1065`), `lem:STOeq_NQ` (`3_5:1136`, bound `(am;asoiuw)`
`3_5:1143-1148`, proof `3_5:1152-1190`).  DECISIONS §62 (2), supervisor `2026-10-05-0755`
answer 2 and (R): the merged `GoodSetN` is used at a *crude* level `Φ` (only its level-free
clauses Herm, Dec, Va, Vb and (D4) are used, through the merged field theorems that take any
`τ` with `hτG`); the drift comes from the new set `GoodLinN` alone, whose clauses (D1'), (D2'),
(D3') sit at their own deterministic levels `Φ₁, Φ₂, Φ₃` (no `Φ²`, no crude level).  The
current length enters only as `B_v^{1/6} Φ_cur` inside `Φ₂`.

## What is here

* §1 (`RBM.Gauss.Sizes`) the vocabulary `GoodLinN`, `nqLinPhi1`-`3`, `NQLinConcl`, `NQLinGood`
  (check file `docs/tickets/checks/T2186-check.lean`, section 2, verbatim);
* §2 `measurableGoodLinN` (copies of the private measurability helpers of `GridGoodN`),
  `goodSetN_subset_goodLinN`;
* §3 `nqLinGood_holds : ∀ d, NQLinGood d` (the shape of `gridGoodN_holds`, with the `ε/3`
  split);
* §4 (`RBM.Ind`) `dDriftLinN`, `nqLinExitTauN` (section 3 of the check file),
  `dDriftNonAltN_eq_lin`, `driftTensorN_norm_le_of_goodLin`, `nqLin_hdriftN`,
  `mem_of_lt_nqLinExitTauN`, `nqLinExitMeasN`, `subGaussStop_linN`;
* §5 `assembledRHSLinN`, `tbDriftLinN`, `budgetNonAltLinN`;
* §6 compiled nonempty instances at `d = 3` (namespace `RBM.Ind.NQLinInst`).

Every helper that the ticket does not pin is `private` or prefixed `nqLin_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 1. The vocabulary -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section GoodLin

variable {d : ℕ} (sz : Sizes d)

/-- **The linear set `G_lin`** (DECISIONS §62 (2); supervisor 2026-10-05-0755 answer 2, (R)): the clauses
(D1), (D2), (D3) of `GoodSetN` (`GridGoodN.lean:124`) with a separate deterministic level each:
(D1') `‖[𝒦^{(l)}∼(𝓛-𝒦)]^{(k)}‖ ≤ Γ(ΓΦ₁)B^k/η` (`3 ≤ l ≤ k`), (D2') `‖ℰ^{(𝓛-𝒦)×(𝓛-𝒦)}‖ ≤ Γ(ΓΦ₂)B^k/η`
(linear in `Φ₂`, in place of `Γ k (ΓΦ)²`), (D3') `‖ℰ^{G̃}‖ ≤ Γ(ΓΦ₃)B^k/η`. -/
def GoodLinN (n : ℕ) (E u : ℝ) (k : ℕ) (Γ Φ₁ Φ₂ Φ₃ : ℝ) :
    Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
  {H | (∀ l : ℕ, 3 ≤ l → l ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖STksimLKM sz n E u H l (loopOf σ a)‖ ≤ Γ * (Γ * Φ₁) * ((sz.Bctl n u) ^ k / etaT E u)) ∧
    (∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖STelklkM sz n E u H (loopOf σ a)‖ ≤ Γ * (Γ * Φ₂) * ((sz.Bctl n u) ^ k / etaT E u)) ∧
    (∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖STegtM sz n E u H (loopOf σ a)‖ ≤ Γ * (Γ * Φ₃) * ((sz.Bctl n u) ^ k / etaT E u))}

end GoodLin

/-- The (D1') level from the controls of lengths `2 ≤ m ≤ k-1` (`3_5:1058-1061`; the lengths `k-l+2`,
`3 ≤ l ≤ k`, of conjunct 2 of `STSEforLnConcl`); `0` for `k = 2`. -/
def nqLinPhi1 (XLK : ℕ → ℝ) (k : ℕ) : ℝ := ∑ m ∈ Finset.Icc 2 (k - 1), XLK m

/-- The (D2') level `Φ₂ = Σ_{n'} XLK(k+2-n') (XL(n'₁) XL(n'₂))^{1/2} + B^{1/6} Φ_cur` (conjunct 3 of
`STSEforLnConcl` with the controls in place of `Ξ̂`; `B` is the caller's `B_v` at the grid endpoint, `Φ_cur`
the deterministic control of the current length). -/
def nqLinPhi2 (XL XLK : ℕ → ℝ) (B : ℝ) (k : ℕ) (Φcur : ℝ) : ℝ :=
  ∑ n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
      XLK (k + 2 - n') * (XL (STn12 n').1 * XL (STn12 n').2) ^ (1 / 2 : ℝ) +
    B ^ (1 / 6 : ℝ) * Φcur

/-- The (D3') level `(XL(n₁) XL(n₂))^{1/2}`, `(n₁, n₂) = STn12E k` (`𝓛`-lengths `k-1 … k+1`; conjunct 1 of
`STSEforLnConcl`). -/
def nqLinPhi3 (XL : ℕ → ℝ) (k : ℕ) : ℝ := (XL (STn12E k).1 * XL (STn12E k).2) ^ (1 / 2 : ℝ)

section NQLinGood

variable {d : ℕ}

/-- **The conclusion of the pin `NQLinGood`** at `(sz, E, s, t)` (the shape of `GridGoodNConcl`,
`GridGoodN.lean:505`): for every grid end `v ∈ [s,t]`, grid size `K`, loop length `k ≥ 2`, and deterministic
controls `XL m n`, `XLK m n ≥ 1` of `Ξ̂^{𝓛}_m` (`m ≤ k+1`) and `Ξ̂^{𝓛-𝒦}_m` (`m ≤ k`, the current length
included) uniformly on `[s_n, v_n]`, with high probability the grid walk is in `GoodLinN` at every
`j ≤ K n`, at the levels `nqLinPhi1`, `nqLinPhi2` (with `B = B_{v_n}`, `Φ_cur = XLK k n`), `nqLinPhi3`. -/
def NQLinConcl (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  ∀ v : ℕ → ℝ, (∀ n, s n ≤ v n) → (∀ n, v n ≤ t n) → ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) →
    ∀ k : ℕ, 2 ≤ k → ∀ XL XLK : ℕ → ℕ → ℝ, (∀ m n, 1 ≤ XL m n) → (∀ m n, 1 ≤ XLK m n) →
    (∀ m : ℕ, 1 ≤ m → m ≤ k + 1 →
      Prec sz (U := fun n => TimeIcc s v n)
        (fun n u ω => STXiL sz n (E n) (u : ℝ) m ω) (fun n _ _ => XL m n)) →
    (∀ m : ℕ, 1 ≤ m → m ≤ k →
      Prec sz (U := fun n => TimeIcc s v n)
        (fun n u ω => STXiLK sz n (E n) (u : ℝ) m ω) (fun n _ _ => XLK m n)) →
    ∀ C : ℝ, (∀ᶠ n in atTop, ((K n + 1 : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C) →
    ∀ ε : ℝ, 0 < ε →
      HighProbAt (pathP sz) sz.size (fun n => {ω | ∀ j ≤ K n,
        pathH sz s v K n j ω ∈ GoodLinN sz n (E n) (gridTime s v K n j) k
          (((sz.size n : ℕ) : ℝ) ^ ε) (nqLinPhi1 (fun m => XLK m n) k)
          (nqLinPhi2 (fun m => XL m n) (fun m => XLK m n) (sz.Bctl n (v n)) k (XLK k n))
          (nqLinPhi3 (fun m => XL m n) k)})

/-- **Pin (`NQLinGood`)**: the Step 3-4 ingredient shape (`STIngR`, any regime) with the conclusion
`NQLinConcl` (as `GridGoodN`, `GridGoodN.lean:528`). -/
def NQLinGood (d : ℕ) : Prop := STIngR d STAny (fun sz E s t => NQLinConcl sz E s t)

end NQLinGood

/-! ## 2. Measurability of `GoodLinN`, and `GoodSetN ⊆ GoodLinN` -/

section MeasurableProof

private theorem nqLin_measurableSet_forall {ι α : Type*} [Countable ι] [MeasurableSpace α]
    {p : ι → α → Prop} (h : ∀ i, MeasurableSet {x | p i x}) :
    MeasurableSet {x | ∀ i, p i x} := by
  have e : {x | ∀ i, p i x} = ⋂ i, {x | p i x} := by
    ext x; simp
  rw [e]
  exact MeasurableSet.iInter h

private theorem nqLin_measurableSet_imp {α : Type*} [MeasurableSpace α] {p : Prop}
    {q : α → Prop} (h : p → MeasurableSet {x | q x}) : MeasurableSet {x | p → q x} := by
  by_cases hp : p
  · simpa [hp] using h hp
  · simp [hp]

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

private theorem nqLin_meas_STLIM (E τ : ℝ) (I : LoopIdx (Zd d (sz.L n))) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STLIM sz n E τ H I :=
  (walk_measurable_loopL d (sz.L n) (sz.W n) (zt E τ) I).comp
    (walk_measurable_blockMat d (sz.L n) (sz.W n))

private theorem nqLin_meas_STLKIM (E τ : ℝ) (I : LoopIdx (Zd d (sz.L n))) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STLKIM sz n E τ H I :=
  (nqLin_meas_STLIM sz n E τ I).sub_const _

private theorem nqLin_meas_STksimLKM (E u : ℝ) (l : ℕ) (I : LoopIdx (Zd d (sz.L n))) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STksimLKM sz n E u H l I := by
  unfold STksimLKM
  refine measurable_const.mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _
    fun l' _ => Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_)
  refine Measurable.add ?_ ?_
  · exact Measurable.ite (MeasurableSet.const _)
      (((nqLin_meas_STLKIM sz n E u _).mul_const _).mul_const _) measurable_const
  · exact Measurable.ite (MeasurableSet.const _)
      ((measurable_const.mul_const _).mul (nqLin_meas_STLKIM sz n E u _)) measurable_const

private theorem nqLin_meas_STelklkM (E u : ℝ) (I : LoopIdx (Zd d (sz.L n))) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STelklkM sz n E u H I := by
  unfold STelklkM
  refine measurable_const.mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _
    fun l' _ => Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_)
  exact ((nqLin_meas_STLKIM sz n E u _).mul_const _).mul (nqLin_meas_STLKIM sz n E u _)

private theorem nqLin_meas_STavgErrM (E u : ℝ) (σ : Bool) (a : Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STavgErrM sz n E u H σ a := by
  unfold STavgErrM
  exact (nqLin_meas_STLIM sz n E u _).sub_const _

private theorem nqLin_meas_STegtM (E u : ℝ) (I : LoopIdx (Zd d (sz.L n))) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STegtM sz n E u H I := by
  unfold STegtM
  refine measurable_const.mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _
    fun a _ => Finset.measurable_sum _ fun b _ => ?_)
  exact ((nqLin_meas_STavgErrM sz n E u _ a).mul_const _).mul (nqLin_meas_STLIM sz n E u _)

end MeasurableProof

/-- **Target `measurableGoodLinN`**: `GoodLinN` is a measurable set of matrices, for every
`sz n E u k Γ Φ₁ Φ₂ Φ₃` (no hypothesis): a finite conjunction, over finitely many labels, of inequalities
between measurable functions of `H` (norms of the loop observables).  The three-clause analogue of
`measurableGoodSetN` (`GridGoodN.lean:361`). -/
theorem measurableGoodLinN {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (k : ℕ) (Γ Φ₁ Φ₂ Φ₃ : ℝ) :
    MeasurableSet (GoodLinN sz n E u k Γ Φ₁ Φ₂ Φ₃) := by
  unfold GoodLinN
  simp only [Set.ofPred_and]
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
  · exact nqLin_measurableSet_forall fun l => nqLin_measurableSet_imp fun _ =>
      nqLin_measurableSet_imp fun _ => nqLin_measurableSet_forall fun σ =>
        nqLin_measurableSet_forall fun a =>
          measurableSet_le (nqLin_meas_STksimLKM sz n E u l (loopOf σ a)).norm measurable_const
  · exact nqLin_measurableSet_forall fun σ => nqLin_measurableSet_forall fun a =>
      measurableSet_le (nqLin_meas_STelklkM sz n E u (loopOf σ a)).norm measurable_const
  · exact nqLin_measurableSet_forall fun σ => nqLin_measurableSet_forall fun a =>
      measurableSet_le (nqLin_meas_STegtM sz n E u (loopOf σ a)).norm measurable_const

/-! ## 3. `nqLinGood_holds`: the grid walk stays in `GoodLinN` with high probability

The grid state `H_j` has the law of the single-time flow `seqHflow` at the grid time `u_j` (`map_pathH_eq`), and
`GoodLinN` is measurable; so the failure probability of the event at the grid index `j` is at most that of the
event "`seqHflow sz n u ω ∈ GoodLinN … u` for every `u ∈ [s_n,v_n]`", which is a finite conjunction of `≺`
statements uniform in `u` (conjuncts 1-3 of `lem:SEforLn`, restricted from `[s,t]` to `[s,v]`, and the hypotheses
`Ξ̂^{𝓛}_m ≺ XL m`, `Ξ̂^{𝓛-𝒦}_m ≺ XLK m`), all at the exponent `ε/3`.  Then `highProbAt_iInter` over `j ≤ K n`. -/

section Helpers

open RBM.Gauss

/-- A finite family of `w.h.p.` events holds simultaneously `w.h.p.` (copy of the private
`gridGood_whp_iInter` of `GridGoodN`). -/
private theorem nqLin_whp_iInter {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}
    (hsize : Tendsto size atTop atTop) {ι : Type*} [Finite ι] {Ξ : ι → ℕ → Set Ω}
    (h : ∀ i, HighProbAt P size (Ξ i)) : HighProbAt P size (fun n => ⋂ i, Ξ i n) := by
  have := Fintype.ofFinite ι
  refine HighProbAt.biInter (K := fun _ => ι) (C := 1) zero_le_one ?_ ?_
  · filter_upwards [hsize.eventually (eventually_ge_atTop (Fintype.card ι))] with l hl
    rw [Real.rpow_one]
    exact_mod_cast hl
  · intro D hD
    have : ∀ᶠ l in atTop, ∀ i, P (Ξ i l)ᶜ ≤ ENNReal.ofReal ((size l : ℝ) ^ (-D)) :=
      Filter.eventually_all.2 fun i => h i D hD
    exact this.mono fun l hl i => hl i

/-- A `Finset`-indexed family of `w.h.p.` events holds simultaneously `w.h.p.` -/
private theorem nqLin_whp_forall_mem {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {size : ℕ → ℕ} (hsize : Tendsto size atTop atTop) {ι : Type*} (S : Finset ι)
    {p : ι → ℕ → Ω → Prop} (h : ∀ i ∈ S, HighProbAt P size (fun n => {ω | p i n ω})) :
    HighProbAt P size (fun n => {ω | ∀ i ∈ S, p i n ω}) := by
  have := nqLin_whp_iInter hsize (ι := ↥S) (Ξ := fun i n => {ω | p i.1 n ω})
    (fun i => h i.1 i.2)
  refine this.mono (Eventually.of_forall fun n ω hω i hi => ?_)
  have := Set.mem_iInter.1 hω ⟨i, hi⟩
  exact this

/-- Two `w.h.p.` events hold simultaneously `w.h.p.` (set-builder form). -/
private theorem nqLin_whp_and {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}
    (hsize : Tendsto size atTop atTop) {p q : ℕ → Ω → Prop}
    (hp : HighProbAt P size (fun n => {ω | p n ω})) (hq : HighProbAt P size (fun n => {ω | q n ω})) :
    HighProbAt P size (fun n => {ω | p n ω ∧ q n ω}) :=
  HighProbAt.inter hsize hp hq

end Helpers

section Arith

/-- `N^{ε/3} N^{ε/3} N^{ε/3} = N^ε` (the `ε/3` split). -/
private theorem nqLin_rpow_third {N ε : ℝ} (hN : 0 ≤ N) (hε : 0 < ε) :
    N ^ (ε / 3) * N ^ (ε / 3) * N ^ (ε / 3) = N ^ ε := by
  rw [← Real.rpow_add' hN (by positivity), ← Real.rpow_add' hN (by positivity)]
  congr 1; ring

/-- `√(x₁ x₂) ≤ A √(c₁ c₂)` when `0 ≤ x_i ≤ A c_i`, `A, c_i ≥ 0`. -/
private theorem nqLin_sqrt_bound {x₁ x₂ A c₁ c₂ : ℝ} (hx1 : 0 ≤ x₁) (hx2 : 0 ≤ x₂) (hA : 0 ≤ A)
    (hc1 : 0 ≤ c₁) (hc2 : 0 ≤ c₂) (h1 : x₁ ≤ A * c₁) (h2 : x₂ ≤ A * c₂) :
    (x₁ * x₂) ^ (1 / 2 : ℝ) ≤ A * (c₁ * c₂) ^ (1 / 2 : ℝ) := by
  calc (x₁ * x₂) ^ (1 / 2 : ℝ) ≤ ((A * c₁) * (A * c₂)) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (mul_nonneg hx1 hx2) (mul_le_mul h1 h2 hx2 (mul_nonneg hA hc1))
          (by norm_num)
    _ = (A * A * (c₁ * c₂)) ^ (1 / 2 : ℝ) := by ring_nf
    _ = (A * A) ^ (1 / 2 : ℝ) * (c₁ * c₂) ^ (1 / 2 : ℝ) :=
        Real.mul_rpow (mul_nonneg hA hA) (mul_nonneg hc1 hc2)
    _ = A * (c₁ * c₂) ^ (1 / 2 : ℝ) := by rw [← Real.sqrt_eq_rpow, Real.sqrt_mul_self hA]

/-- The clauses (D1'), (D3'): `x ≤ A (Bk (A Y))` with `A ≤ Γ`, `Y ≤ Φ` gives `x ≤ Γ (Γ Φ) Bk`. -/
private theorem nqLin_clause {x A Γ Bk Y Φ : ℝ} (hA0 : 0 ≤ A) (hAΓ : A ≤ Γ) (hBk : 0 ≤ Bk)
    (hY : 0 ≤ Y) (hYΦ : Y ≤ Φ) (hx : x ≤ A * (Bk * (A * Y))) : x ≤ Γ * (Γ * Φ) * Bk := by
  have hΓ0 : 0 ≤ Γ := hA0.trans hAΓ
  have h1 : A * A * Y ≤ Γ * Γ * Φ :=
    mul_le_mul (mul_le_mul hAΓ hAΓ hA0 hΓ0) hYΦ hY (mul_nonneg hΓ0 hΓ0)
  calc x ≤ A * (Bk * (A * Y)) := hx
    _ = (A * A * Y) * Bk := by ring
    _ ≤ (Γ * Γ * Φ) * Bk := mul_le_mul_of_nonneg_right h1 hBk
    _ = Γ * (Γ * Φ) * Bk := by ring

/-- The clause (D2'), linear in the level: the sum over `n'` has the terms
`Y_{k+2-n'} (X_{n'₁} X_{n'₂})^{1/2} ≤ A² XLK_{k+2-n'} (XL_{n'₁} XL_{n'₂})^{1/2}` and the last term
`B_u^{1/6} Y_k ≤ B_v^{1/6} A XLK_k ≤ A² B_v^{1/6} XLK_k`; so `x ≤ A (Bk (A² Φ₂)) ≤ Γ (Γ Φ₂) Bk` when
`A³ ≤ Γ²` (`A = N^{ε/3}`, `Γ = N^ε ≥ 1`).  No `B ≤ 1`, no `gridGood_D2_arith`. -/
private theorem nqLin_D2_arith {k : ℕ} (hk : 2 ≤ k) {A Γ Bk b6u b6v x : ℝ}
    {Y X XL XLK : ℕ → ℝ} (hA1 : 1 ≤ A) (hAΓ : A * A * A ≤ Γ * Γ) (hBk : 0 ≤ Bk) (hb6 : 0 ≤ b6u)
    (hb6' : b6u ≤ b6v) (hXL1 : ∀ m, 1 ≤ XL m) (hXLK1 : ∀ m, 1 ≤ XLK m)
    (hY : ∀ m, 1 ≤ m → m ≤ k → 0 ≤ Y m ∧ Y m ≤ A * XLK m)
    (hX : ∀ m, 1 ≤ m → m ≤ k + 1 → 0 ≤ X m ∧ X m ≤ A * XL m)
    (hx : x ≤ A * (Bk * (∑ n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
        Y (k + 2 - n') * (X (STn12 n').1 * X (STn12 n').2) ^ (1 / 2 : ℝ) + b6u * Y k))) :
    x ≤ Γ * (Γ * (∑ n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
        XLK (k + 2 - n') * (XL (STn12 n').1 * XL (STn12 n').2) ^ (1 / 2 : ℝ) + b6v * XLK k)) * Bk := by
  have hA0 : 0 ≤ A := by linarith
  have hb6v : 0 ≤ b6v := hb6.trans hb6'
  set T : ℝ := ∑ n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
      XLK (k + 2 - n') * (XL (STn12 n').1 * XL (STn12 n').2) ^ (1 / 2 : ℝ) with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun n' _ =>
    mul_nonneg (zero_le_one.trans (hXLK1 _)) (Real.rpow_nonneg
      (mul_nonneg (zero_le_one.trans (hXL1 _)) (zero_le_one.trans (hXL1 _))) _)
  have hterm : ∀ n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
      Y (k + 2 - n') * (X (STn12 n').1 * X (STn12 n').2) ^ (1 / 2 : ℝ) ≤
        A * A * (XLK (k + 2 - n') * (XL (STn12 n').1 * XL (STn12 n').2) ^ (1 / 2 : ℝ)) := by
    intro n' hn'
    rw [Finset.mem_Icc] at hn'
    have hy := hY (k + 2 - n') (by omega) (by omega)
    have hi : 1 ≤ (STn12 n').1 ∧ (STn12 n').1 ≤ k + 1 ∧ 1 ≤ (STn12 n').2 ∧ (STn12 n').2 ≤ k + 1 := by
      unfold STn12
      split_ifs with h2 <;> simp only <;> omega
    have hx1 := hX _ hi.1 hi.2.1
    have hx2 := hX _ hi.2.2.1 hi.2.2.2
    have hsq := nqLin_sqrt_bound hx1.1 hx2.1 hA0 (zero_le_one.trans (hXL1 _))
      (zero_le_one.trans (hXL1 _)) hx1.2 hx2.2
    calc Y (k + 2 - n') * (X (STn12 n').1 * X (STn12 n').2) ^ (1 / 2 : ℝ)
        ≤ (A * XLK (k + 2 - n')) * (A * (XL (STn12 n').1 * XL (STn12 n').2) ^ (1 / 2 : ℝ)) :=
          mul_le_mul hy.2 hsq (Real.rpow_nonneg (mul_nonneg hx1.1 hx2.1) _)
            (mul_nonneg hA0 (zero_le_one.trans (hXLK1 _)))
      _ = A * A * (XLK (k + 2 - n') * (XL (STn12 n').1 * XL (STn12 n').2) ^ (1 / 2 : ℝ)) := by ring
  have hsum : ∑ n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
      Y (k + 2 - n') * (X (STn12 n').1 * X (STn12 n').2) ^ (1 / 2 : ℝ) ≤ A * A * T := by
    rw [hT, Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hYk := hY k (by omega) le_rfl
  have hlast : b6u * Y k ≤ A * A * (b6v * XLK k) := by
    calc b6u * Y k ≤ b6v * (A * XLK k) := mul_le_mul hb6' hYk.2 hYk.1 hb6v
      _ ≤ b6v * (A * A * XLK k) := by
          refine mul_le_mul_of_nonneg_left ?_ hb6v
          have : A * XLK k ≤ A * A * XLK k :=
            mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hA0 hA1) (zero_le_one.trans (hXLK1 _))
          exact this
      _ = A * A * (b6v * XLK k) := by ring
  have hΦ2 : 0 ≤ T + b6v * XLK k := add_nonneg hT0 (mul_nonneg hb6v (zero_le_one.trans (hXLK1 _)))
  have hΓ0 : 0 ≤ Γ * Γ := by nlinarith
  calc x ≤ A * (Bk * (∑ n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
        Y (k + 2 - n') * (X (STn12 n').1 * X (STn12 n').2) ^ (1 / 2 : ℝ) + b6u * Y k)) := hx
    _ ≤ A * (Bk * (A * A * (T + b6v * XLK k))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hBk) hA0
        nlinarith [hsum, hlast]
    _ = (A * A * A) * (T + b6v * XLK k) * Bk := by ring
    _ ≤ (Γ * Γ) * (T + b6v * XLK k) * Bk :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAΓ hΦ2) hBk
    _ = Γ * (Γ * (T + b6v * XLK k)) * Bk := by ring

end Arith

section Uniform

variable {d : ℕ}

private theorem nqLin_one_le_STXiL (sz : Sizes d) {n : ℕ} {E v : ℝ} (k : ℕ) (ω : sz.SeqΩ)
    (hB : 0 < sz.Bctl n v) : 1 ≤ STXiL sz n E v k ω := by
  unfold STXiL
  have h0 : 0 ≤ STmaxL sz n E v k ω :=
    le_trans (norm_nonneg _) (Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
      ‖Lloop sz n E v p.1 p.2 ω‖) (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Zd d (sz.L n))))))
  have := div_nonneg h0 (pow_pos hB (k - 1)).le
  linarith

private theorem nqLin_one_le_STXiLK (sz : Sizes d) {n : ℕ} {E v : ℝ} (k : ℕ) (ω : sz.SeqΩ)
    (hB : 0 < sz.Bctl n v) : 1 ≤ STXiLK sz n E v k ω := by
  unfold STXiLK
  have h0 : 0 ≤ STmaxLK sz n E v k ω :=
    le_trans (norm_nonneg _) (Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
      ‖Lloop sz n E v p.1 p.2 ω - STKloop sz n E v p.1 p.2‖)
      (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Zd d (sz.L n))))))
  have := div_nonneg h0 (pow_pos hB k).le
  linarith

/-- `lem:SEforLn` on the window `[s,t]` gives it on `[s,v]`, `v ≤ t` (restriction of the parameter set). -/
private theorem nqLin_SE_restrict {sz : Sizes d} {E s t v : ℕ → ℝ} (hvt : ∀ n, v n ≤ t n)
    (h : STSEforLnConcl sz E s t) : STSEforLnConcl sz E s v := by
  intro k hk
  obtain ⟨h1, h2, h3, h4⟩ := h k hk
  let φ : ∀ n, TimeIcc s v n → TimeIcc s t n := fun n u => ⟨u.1, u.2.1, u.2.2.trans (hvt n)⟩
  refine ⟨?_, fun l hl3 hlk => ?_, ?_, fun q hq => ?_⟩
  · exact StochDomAt.precomp_param (V := fun n => TimeIcc s v n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      h1 (fun n p => (φ n p.1, p.2))
  · exact StochDomAt.precomp_param (V := fun n => TimeIcc s v n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (h2 l hl3 hlk) (fun n p => (φ n p.1, p.2))
  · exact StochDomAt.precomp_param (V := fun n => TimeIcc s v n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      h3 (fun n p => (φ n p.1, p.2))
  · exact StochDomAt.precomp_param
      (V := fun n => TimeIcc s v n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)) × (Fin k → Zd d (sz.L n)))
      (h4 q hq) (fun n p => (φ n p.1, p.2))

/-- **The uniform good event**: from the hypotheses of `NQLinConcl` and the three conjuncts of `lem:SEforLn` on
`[s,v]`, with high probability `seqHflow n u ω ∈ GoodLinN … u` for every `u ∈ [s_n,v_n]` at once, at the levels
`Φ₁ = nqLinPhi1`, `Φ₂ = nqLinPhi2` (with `B = B_{v_n}`, `Φ_cur = XLK k n`), `Φ₃ = nqLinPhi3` and the loss `N^ε`
(the `ε/3` split: every `≺` is used at the exponent `ε/3`). -/
private theorem nqLin_whp_uniform (sz : Sizes d) {E s v : ℕ → ℝ} (hsz : sz.SizeTendsto)
    (hE : ∀ n, |E n| < 2) (hv1 : ∀ n, v n < 1) (hSE : STSEforLnConcl sz E s v) {k : ℕ} (hk : 2 ≤ k)
    {XL XLK : ℕ → ℕ → ℝ} (hXL1 : ∀ m n, 1 ≤ XL m n) (hXLK1 : ∀ m n, 1 ≤ XLK m n)
    (hX : ∀ m : ℕ, 1 ≤ m → m ≤ k + 1 →
      Prec sz (U := fun n => TimeIcc s v n)
        (fun n u ω => STXiL sz n (E n) (u : ℝ) m ω) (fun n _ _ => XL m n))
    (hY : ∀ m : ℕ, 1 ≤ m → m ≤ k →
      Prec sz (U := fun n => TimeIcc s v n)
        (fun n u ω => STXiLK sz n (E n) (u : ℝ) m ω) (fun n _ _ => XLK m n))
    {ε : ℝ} (hε : 0 < ε) :
    Whp sz (fun n => {ω | ∀ u : TimeIcc s v n, sz.seqHflow n (u : ℝ) ω ∈
      GoodLinN sz n (E n) (u : ℝ) k (((sz.size n : ℕ) : ℝ) ^ ε) (nqLinPhi1 (fun m => XLK m n) k)
        (nqLinPhi2 (fun m => XL m n) (fun m => XLK m n) (sz.Bctl n (v n)) k (XLK k n))
        (nqLinPhi3 (fun m => XL m n) k)}) := by
  have hsz' : Tendsto sz.size atTop atTop := tendsto_size sz hsz
  have hε3 : 0 < ε / 3 := by positivity
  -- positivity of the scales on the window
  have hpos : ∀ n (u : TimeIcc s v n), 0 < sz.Bctl n (u : ℝ) ∧ 0 < etaT (E n) (u : ℝ) := by
    intro n u
    have hu1 : (u : ℝ) < 1 := (u.2.2).trans_lt (hv1 n)
    exact ⟨st_Bctl_pos sz hu1, etaT_pos (hE n) hu1⟩
  -- the w.h.p. events, all at the exponent `ε/3`
  have wY := nqLin_whp_forall_mem hsz' (Finset.Icc 1 k) (fun m hm => by
    rw [Finset.mem_Icc] at hm
    exact (hY m hm.1 hm.2).whp sz hε3)
  have wX := nqLin_whp_forall_mem hsz' (Finset.Icc 1 (k + 1)) (fun m hm => by
    rw [Finset.mem_Icc] at hm
    exact (hX m hm.1 hm.2).whp sz hε3)
  have hSE' := hSE k hk
  have wD3 := hSE'.1.whp sz hε3
  have wD1 := nqLin_whp_forall_mem hsz' (Finset.Icc 3 k) (fun l hl => by
    rw [Finset.mem_Icc] at hl
    exact (hSE'.2.1 l hl.1 hl.2).whp sz hε3)
  have wD2 := hSE'.2.2.1.whp sz hε3
  have wAll := nqLin_whp_and hsz' wY (nqLin_whp_and hsz' wX (nqLin_whp_and hsz' wD1
    (nqLin_whp_and hsz' wD2 wD3)))
  refine wAll.mono (Eventually.of_forall fun n ω hω u => ?_)
  obtain ⟨hY', hX', hD1', hD2', hD3'⟩ := hω
  have hu1 : (u : ℝ) < 1 := (u.2.2).trans_lt (hv1 n)
  obtain ⟨hBpos, hηpos⟩ := hpos n u
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
  have hA1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (ε / 3) := Real.one_le_rpow hN1 hε3.le
  have hA0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (ε / 3) := by linarith
  have hΓ1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ ε := Real.one_le_rpow hN1 hε.le
  have hAΓ : ((sz.size n : ℕ) : ℝ) ^ (ε / 3) ≤ ((sz.size n : ℕ) : ℝ) ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hAAA : ((sz.size n : ℕ) : ℝ) ^ (ε / 3) * ((sz.size n : ℕ) : ℝ) ^ (ε / 3) *
      ((sz.size n : ℕ) : ℝ) ^ (ε / 3) ≤ ((sz.size n : ℕ) : ℝ) ^ ε * ((sz.size n : ℕ) : ℝ) ^ ε := by
    rw [nqLin_rpow_third hN0 hε]
    exact le_mul_of_one_le_left (by linarith) hΓ1
  have hBk : 0 ≤ (sz.Bctl n (u : ℝ)) ^ k / etaT (E n) (u : ℝ) :=
    div_nonneg (pow_nonneg hBpos.le _) hηpos.le
  have hYb : ∀ m, 1 ≤ m → m ≤ k →
      0 ≤ STXiLK sz n (E n) (u : ℝ) m ω ∧
        STXiLK sz n (E n) (u : ℝ) m ω ≤ ((sz.size n : ℕ) : ℝ) ^ (ε / 3) * XLK m n := fun m h1 h2 =>
    ⟨zero_le_one.trans (nqLin_one_le_STXiLK sz m ω hBpos), hY' m (Finset.mem_Icc.2 ⟨h1, h2⟩) u⟩
  have hXb : ∀ m, 1 ≤ m → m ≤ k + 1 →
      0 ≤ STXiL sz n (E n) (u : ℝ) m ω ∧
        STXiL sz n (E n) (u : ℝ) m ω ≤ ((sz.size n : ℕ) : ℝ) ^ (ε / 3) * XL m n := fun m h1 h2 =>
    ⟨zero_le_one.trans (nqLin_one_le_STXiL sz m ω hBpos), hX' m (Finset.mem_Icc.2 ⟨h1, h2⟩) u⟩
  rw [GoodLinN, Set.mem_ofPred_eq]
  refine ⟨fun l hl3 hlk σ a => ?_, fun σ a => ?_, fun σ a => ?_⟩
  · -- (D1')
    have h := hD1' l (Finset.mem_Icc.2 ⟨hl3, hlk⟩) ((u, σ, a) : TimeIcc s v n × (Fin k → Bool) ×
      (Fin k → Zd d (sz.L n)))
    have hm := hYb (k - l + 2) (by omega) (by omega)
    have hΦ : XLK (k - l + 2) n ≤ nqLinPhi1 (fun m => XLK m n) k :=
      Finset.single_le_sum (f := fun m => XLK m n) (fun m _ => zero_le_one.trans (hXLK1 m n))
        (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    exact nqLin_clause hA0 hAΓ hBk (zero_le_one.trans (hXLK1 _ n)) hΦ
      (h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm.2 hBk) hA0))
  · -- (D2')
    have h := hD2' ((u, σ, a) : TimeIcc s v n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
    have hb6 : (sz.Bctl n (u : ℝ)) ^ (1 / 6 : ℝ) ≤ (sz.Bctl n (v n)) ^ (1 / 6 : ℝ) :=
      Real.rpow_le_rpow hBpos.le (Sizes.STBctl_mono sz n (u.2.2) (hv1 n)) (by norm_num)
    exact nqLin_D2_arith hk (Y := fun m => STXiLK sz n (E n) (u : ℝ) m ω)
      (X := fun m => STXiL sz n (E n) (u : ℝ) m ω) (XL := fun m => XL m n) (XLK := fun m => XLK m n)
      hA1 hAAA hBk (Real.rpow_nonneg hBpos.le _) hb6 (fun m => hXL1 m n) (fun m => hXLK1 m n)
      hYb hXb h
  · -- (D3')
    have h := hD3' ((u, σ, a) : TimeIcc s v n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
    have hi : 1 ≤ (STn12E k).1 ∧ (STn12E k).1 ≤ k + 1 ∧ 1 ≤ (STn12E k).2 ∧
        (STn12E k).2 ≤ k + 1 := by
      unfold STn12E
      split_ifs with h2 <;> simp only <;> omega
    have hx1 := hXb _ hi.1 hi.2.1
    have hx2 := hXb _ hi.2.2.1 hi.2.2.2
    have hsq := nqLin_sqrt_bound hx1.1 hx2.1 hA0 (zero_le_one.trans (hXL1 _ n))
      (zero_le_one.trans (hXL1 _ n)) hx1.2 hx2.2
    have hΦ3 : 0 ≤ nqLinPhi3 (fun m => XL m n) k :=
      Real.rpow_nonneg (mul_nonneg (zero_le_one.trans (hXL1 _ n)) (zero_le_one.trans (hXL1 _ n))) _
    exact nqLin_clause hA0 hAΓ hBk hΦ3 le_rfl
      (h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hBk) hA0))

end Uniform

/-! ### The grid: transfer to the single-time flow and the union bound over `j ≤ K n` -/

section Grid

variable {d : ℕ}

private theorem nqLin_gridTime_mem {s v : ℕ → ℝ} {K : ℕ → ℕ} (hsv : ∀ n, s n ≤ v n)
    (hK : ∀ n, K n ≠ 0) (n j : ℕ) (hj : j ≤ K n) :
    gridTime s v K n j ∈ Set.Icc (s n) (v n) := by
  have hKpos : (0 : ℝ) < K n := by exact_mod_cast Nat.pos_of_ne_zero (hK n)
  have hstep : 0 ≤ gridStep s v K n := div_nonneg (by linarith [hsv n]) hKpos.le
  have hjK : (j : ℝ) ≤ K n := by exact_mod_cast hj
  unfold gridTime
  constructor
  · nlinarith [mul_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j) hstep]
  · have h1 : (j : ℝ) * gridStep s v K n ≤ (K n : ℝ) * gridStep s v K n :=
      mul_le_mul_of_nonneg_right hjK hstep
    have hK' : (K n : ℝ) * gridStep s v K n = v n - s n := by
      unfold gridStep; field_simp
    linarith

private theorem nqLin_measurable_pathH (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) :
    Measurable (pathH sz s t K n k) :=
  Measurable.of_eval_matrix _ fun i j => measurable_pathH sz s t K n k i j

private theorem nqLin_measurable_seqHflow (sz : Sizes d) (n : ℕ) (u : ℝ) :
    Measurable (sz.seqHflow n u) :=
  Measurable.of_eval_matrix _ fun i j => measurable_seqHflow_entry sz n u i j

/-- **The transfer and the union bound**: if with high probability `seqHflow n u ω ∈ GoodLinN … u` for every
`u ∈ [s_n,v_n]`, then with high probability the grid walk `pathH … j` is in `GoodLinN` at every grid index
`j ≤ K n` (`map_pathH_eq` at each `j`, `measurableGoodLinN`, then `highProbAt_iInter` over `j ≤ K n`,
`K n + 1 ≤ N^C`; the shape of the private `gridGood_grid` of `GridGoodN`). -/
private theorem nqLin_grid (sz : Sizes d) {E s v : ℕ → ℝ} {K : ℕ → ℕ} (hs0 : ∀ n, 0 ≤ s n)
    (hsv : ∀ n, s n ≤ v n) (hK : ∀ n, K n ≠ 0) {C : ℝ}
    (hC : ∀ᶠ n in atTop, ((K n + 1 : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C) {k : ℕ}
    {Γ Φ₁ Φ₂ Φ₃ : ℕ → ℝ}
    (hW : Whp sz (fun n => {ω | ∀ u : TimeIcc s v n, sz.seqHflow n (u : ℝ) ω ∈
      GoodLinN sz n (E n) (u : ℝ) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)})) :
    HighProbAt (pathP sz) sz.size (fun n => {ω | ∀ j ≤ K n,
      pathH sz s v K n j ω ∈ GoodLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)}) := by
  have hgrid : ∀ n j, j ≤ K n →
      pathP sz {ω | pathH sz s v K n j ω ∈
        GoodLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)}ᶜ ≤
      sz.seqP {ω | ∀ u : TimeIcc s v n, sz.seqHflow n (u : ℝ) ω ∈
        GoodLinN sz n (E n) (u : ℝ) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)}ᶜ := by
    intro n j hj
    have hmem := nqLin_gridTime_mem hsv hK n j hj
    have hG := (measurableGoodLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)).compl
    have h1 := Measure.map_apply (μ := pathP sz) (nqLin_measurable_pathH sz s v K n j) hG
    have h2 := Measure.map_apply (μ := sz.seqP)
      (nqLin_measurable_seqHflow sz n (gridTime s v K n j)) hG
    have h3 := map_pathH_eq sz s v K n j (hs0 n) (hsv n) (hK n)
    have e1 : {ω | pathH sz s v K n j ω ∈
        GoodLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)}ᶜ =
        pathH sz s v K n j ⁻¹'
          (GoodLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n))ᶜ := by
      ext ω; simp
    rw [e1, ← h1, h3, h2]
    refine measure_mono ?_
    intro ω hω hall
    exact hω (hall ⟨gridTime s v K n j, hmem⟩)
  have hN1 : ∀ n, (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := fun n => by exact_mod_cast sz.one_le_size n
  have hI := highProbAt_iInter (pathP sz) sz.size (K := fun n => Fin (K n + 1))
    (Ξ := fun n j => {ω | pathH sz s v K n j.1 ω ∈
      GoodLinN sz n (E n) (gridTime s v K n j.1) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)}) (C := max C 0)
    (le_max_right _ _)
    (by
      filter_upwards [hC] with n hn
      rw [Fintype.card_fin]
      exact hn.trans (Real.rpow_le_rpow_of_exponent_le (hN1 n) (le_max_left _ _)))
    (fun D hD => (hW D hD).mono fun n hn j =>
      (hgrid n j.1 (Nat.lt_succ_iff.1 j.2)).trans hn)
  refine hI.mono (Eventually.of_forall fun n ω hω j hj => ?_)
  exact Set.mem_iInter.1 hω ⟨j, Nat.lt_succ_of_le hj⟩

end Grid

/-- **`nqLinGood_holds`: the pin `NQLinGood` is a theorem for every `d ≥ 3`.**  `𝔠_d` is that of
`stSEforLn_holds` (`lem:SEforLn`); the conjuncts 2, 3, 1 of `STSEforLnConcl` (restricted from `[s,t]` to `[s,v]`)
give the levels (D1'), (D2'), (D3') from the hypotheses `Ξ̂^{𝓛}_m ≺ XL m`, `Ξ̂^{𝓛-𝒦}_m ≺ XLK m` (all at the exponent
`ε/3`; `B_u^{1/6} ≤ B_v^{1/6}`, `STBctl_mono`, `v_n < 1`); then `nqLin_grid`.  The other premises of the pin
(`STKbound`, `STKward`, `STLK s`, `(con_st_ind)`, `STStep2Concl`) enter only through `stSEforLn_holds`. -/
theorem nqLinGood_holds (d : ℕ) : NQLinGood d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠d, h𝔠d0, h𝔠d1, H⟩ := stSEforLn_holds d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨𝔠d, h𝔠d0, h𝔠d1, ?_⟩
  intro 𝔠 sz z hflow s t hs hst ht hR hK hKw hLK hcon hStep2
  have hSE := H 𝔠 sz z hflow s t hs hst ht hR hK hKw hLK hcon hStep2
  have him : ∀ n, 0 < (z n).im := fun n =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.one_le_size n) _)
      (hflow.2 n).2.1
  have ht1 : ∀ n, t n < 1 := fun n => (ht n).trans_lt (lemT_lt_one (him n))
  have hE : ∀ n, |STflowE z n| < 2 := fun n => abs_lemE_lt_two (him n)
  intro v hsv hvt K hK0 k hk XL XLK hXL hXLK hX hY C hC ε₁ hε₁
  have hSEv := nqLin_SE_restrict hvt hSE
  have hW := nqLin_whp_uniform sz hflow.1.2.2.1 hE (fun n => (hvt n).trans_lt (ht1 n)) hSEv hk hXL hXLK
    hX hY hε₁
  exact nqLin_grid sz hs hsv hK0 hC hW

/-! ### The hypotheses `hX`, `hY` of `NQLinConcl` at the levels `XL ≡ XLK ≡ 1`: they follow from `STLmaxU`, `STLKU`

(Used by the instance of `nqLinGood_holds`, section 6; the other gates' pins `STLmaxU`, `STLKU` stay hypotheses
there.  Copies of the private lemmas of `GridGoodN` §6, on an arbitrary window `[s,t]`, and the restriction of
`STLmaxU`, `STLKU` from `[s,t]` to `[s,v]`.) -/

end RBM.Gauss.Sizes

/-! ## 4. The linear drift, the exit time of `GoodSetN ∩ GoodLinN`, the sub-Gaussian input -/

namespace RBM.Ind

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-- **The linear drift level** (replaces `dDriftNonAltN`, `NQGood2.lean:96`): the sum of the `k-2` copies of
(D1'), one (D2') and one (D3'): `Γ·Γ·(B_u^k/η_u)·((k-2)Φ₁ + Φ₂ + Φ₃)`; no additive `W^{-D'}`. -/
def dDriftLinN {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (k : ℕ) (Γ Φ₁ Φ₂ Φ₃ : ℝ) : ℝ :=
  Γ * Γ * ((sz.Bctl n u) ^ k / etaT E u) * (((k : ℝ) - 2) * Φ₁ + Φ₂ + Φ₃)

/-- **The exit time of the grid walk from `GoodSetN ∩ GoodLinN`** (the merged generic `gridExitTauN`,
`GridGoodN.lean:169`; `GoodSetN` is used at the crude level `Φ`, only its level-free clauses and (D4)). -/
def nqLinExitTauN {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (s v : ℕ → ℝ) (K : ℕ → ℕ) (k : ℕ)
    (Γ Λ Φ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (τ' D' : ℝ) (n : ℕ) : PathΩ sz → ℕ :=
  gridExitTauN sz s v K n (fun j =>
    sz.GoodSetN n (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D' ∩
      GoodLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n))

/-- **Target `driftTensorN_norm_le_of_goodLin`** (the proof of `driftTensorN_norm_le_of_goodSet`,
`NQGood1.lean:104`, with three levels): on `GoodLinN` the drift tensor is bounded by the linear level
`Γ²(B_u^k/η_u)((k-2)Φ₁ + Φ₂ + Φ₃)` (`k-2` copies of (D1'), one of (D2'), one of (D3')). -/
theorem driftTensorN_norm_le_of_goodLin {d : ℕ} (sz : Sizes d) {n : ℕ} {E u Γ Φ₁ Φ₂ Φ₃ : ℝ}
    {k : ℕ} (hk : 2 ≤ k)
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hM : M ∈ GoodLinN sz n E u k Γ Φ₁ Φ₂ Φ₃) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    ‖driftTensorN sz n E u M σ a‖ ≤ dDriftLinN sz n E u k Γ Φ₁ Φ₂ Φ₃ := by
  obtain ⟨hD1, hD2, hD3⟩ := hM
  set X : ℝ := (sz.Bctl n u) ^ k / etaT E u with hX
  have h1 : ‖∑ l ∈ Finset.Icc 3 k, sz.STksimLKM n E u M l (loopOf σ a)‖ ≤
      ((k - 2 : ℕ) : ℝ) * (Γ * (Γ * Φ₁) * X) := by
    refine (norm_sum_le _ _).trans ?_
    have hle : ∀ l ∈ Finset.Icc 3 k, ‖sz.STksimLKM n E u M l (loopOf σ a)‖ ≤
        Γ * (Γ * Φ₁) * X := fun l hl =>
      hD1 l (Finset.mem_Icc.1 hl).1 (Finset.mem_Icc.1 hl).2 σ a
    refine (Finset.sum_le_card_nsmul _ _ _ hle).trans ?_
    rw [nsmul_eq_mul, Nat.card_Icc]
    have : (k + 1 - 3 : ℕ) = k - 2 := by omega
    rw [this]
  have h2 := hD2 σ a
  have h3 := hD3 σ a
  have hc : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
    rw [Nat.cast_sub hk]; norm_num
  unfold driftTensorN dDriftLinN
  refine (norm_add₃_le).trans ?_
  rw [hc] at h1
  nlinarith [h1, h2, h3]

/-- **Target `nqLin_hdriftN`** (the field `hdrift` on `{H_j ∈ GoodLinN(u_j), j < τ}`): the drift tensor along
the walk is bounded by `dDriftLinN` (`driftTensorN_norm_le_of_goodLin`; the merged `nonAlt_hdriftN` with the
linear level). -/
theorem nqLin_hdriftN {d : ℕ} (sz : Sizes d) {n k : ℕ} (hk : 2 ≤ k) (σ : Fin k → Bool)
    (E s v : ℕ → ℝ) (K : ℕ → ℕ) (Γ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (τ : PathΩ sz → ℕ)
    (hτG : ∀ ω j, j < τ ω → pathH sz s v K n j ω ∈
      GoodLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)) :
    ∀ ω j, j < K n → j < τ ω → ∀ b : Fin k → Zd d (sz.L n),
      ‖driftTensorN sz n (E n) (gridTime s v K n j) (pathH sz s v K n j ω) σ b‖ ≤
        dDriftLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) :=
  fun ω j _ hjτ b => driftTensorN_norm_le_of_goodLin sz hk (hτG ω j hjτ) σ b

/-- **Target `mem_of_lt_nqLinExitTauN`**: strictly before the exit, the grid state is in
`GoodSetN ∩ GoodLinN` (`mem_of_lt_gridExitTauN`). -/
theorem mem_of_lt_nqLinExitTauN {d : ℕ} {sz : Sizes d} {E : ℕ → ℝ} {s v : ℕ → ℝ} {K : ℕ → ℕ} {k : ℕ}
    {Γ Λ Φ Φ₁ Φ₂ Φ₃ : ℕ → ℝ} {τ' D' : ℝ} {n : ℕ} {ω : PathΩ sz} {j : ℕ}
    (h : j < nqLinExitTauN sz E s v K k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D' n ω) :
    pathH sz s v K n j ω ∈ sz.GoodSetN n (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D' ∩
      GoodLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) :=
  mem_of_lt_gridExitTauN h

/-- **Target `nqLinExitMeasN`**: `{j < nqLinExitTauN}` is `filt j`-measurable (`gridExitTauN_measurableSet`
with `measurableGoodSetN` and `measurableGoodLinN`). -/
theorem nqLinExitMeasN {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (Γ Λ Φ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (τ' D' : ℝ) (j : ℕ) :
    MeasurableSet[filt sz j] {ω | j < nqLinExitTauN sz E s v K k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D' n ω} :=
  gridExitTauN_measurableSet (fun j =>
    (measurableGoodSetN d sz n _ _ _ _ _ _ _ _).inter
      (measurableGoodLinN sz n _ _ _ _ _ _ _)) j

/-- **Target `subGaussStop_linN`**: the merged `subGaussStop_nonAltN` (`NQGood2.lean:564`) with the exit time
`nqLinExitTauN` (from `azumaProxy_subG_ugen`, `AzumaProxyN.lean:980`, with `G j = GoodSetN ∩ GoodLinN`,
`mem_of_lt_nqLinExitTauN`, `nqLinExitMeasN`, and `hQ_nonAltN` on the `GoodSetN` component); same hypotheses, same
proxy `cQVNonAltN` (independent of `Φ, Φ₁, Φ₂, Φ₃`). -/
theorem subGaussStop_linN {d k : ℕ} (Λg κ' : ℝ) (hd : 3 ≤ d) (hk : 2 ≤ k) (hΛg : 0 < Λg)
    (hκ' : 0 < κ') (sz : Sizes d) {E s v : ℕ → ℝ} {K : ℕ → ℕ} (hE : ∀ n, |E n| < 2)
    (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1) (n : ℕ)
    (hwL : v n ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - v n) / (1 - s n)) (hκm : κ' ≤ (mE (E n)).im)
    (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ Λg) {ε τ' D' D'' : ℝ}
    (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hD'' : (k : ℝ) + 1 < D'') {σ : Fin k → Bool} (hσ : ∃ i, σ i = σ (finRotate k i))
    (Γ Λ Φ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (hΓ : 0 ≤ Γ n) (hΛ : 0 ≤ Λ n) (m : ℕ) (hm : m ≤ K n)
    (a : Fin k → Zd d (sz.L n)) (j : ℕ) (hj : j < m)
    (hδ : ((sz.W n : ℕ) : ℝ) ^ (-D') + eeShiftErrN d (sz.L n) (sz.W n) (E n) k
      (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'')) :
    SubGaussStopN sz (E n) σ (gridTime s v K n)
      (nqLinExitTauN sz E s v K k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D' n)
      (fun j ω => ZvecN sz E s v K n j σ ω) m a j
      (cQVNonAltN sz E s v K n k Λg κ' ε Γ Λ D'' m a j) :=
  azumaProxy_subG_ugen sz (azumaSubGN sz s v K) hE hs0 hsv hv1 n k hk σ
    (nqLinExitTauN sz E s v K k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D' n)
    (fun j => sz.GoodSetN n (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D' ∩
      GoodLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n))
    (nqLinExitMeasN sz E s v K n k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D')
    (fun ω j hj => mem_of_lt_nqLinExitTauN hj) m hm a j hj
    (cQVNonAltN sz E s v K n k Λg κ' ε Γ Λ D'' m a j)
    (fun M hM hMh => hQ_nonAltN Λg κ' hd hk hΛg hκ' sz E s v K n (hE n) (hs0 n) (hsv n) (hv1 n) hwL
      hWt hκm hg hgΛ hW hε0 hε1 hWε hdW hD'' hσ Γ Λ Φ hΓ hΛ m hm a j hj hδ M hM.1 hMh)

/-! ## 5. The linear budget -/

/-- **The right-hand side of the merged `AssembledN` at `m = K n` with the linear drift**: the merged
`assembledRHSNonAltN` (`NQBudget.lean:77`) with `dDriftNonAltN … (Γ n) (Φ n)` replaced by
`dDriftLinN … (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)`; no crude level `Φ` (the QV proxy `cQVNonAltN` has none). -/
def assembledRHSLinN {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (Λg κ' ε : ℝ) (Γ Λ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (D' D'' D_Y τK εq X0 : ℝ) (a : Fin k → Zd d (sz.L n)) : ℝ :=
  kappaNonAltN d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) 0 (K n) * X0 +
    epsNonAltN d k Λg κ' ((sz.W n : ℕ) : ℝ) 0 (K n) * ((sz.W n : ℕ) : ℝ) ^ (-D') +
    gridStep s v K n * ∑ j ∈ Finset.range (K n),
      (kappaNonAltN d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) (j + 1) (K n) *
          dDriftLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) +
        epsNonAltN d k Λg κ' ((sz.W n : ℕ) : ℝ) (j + 1) (K n) * ((sz.W n : ℕ) : ℝ) ^ (-D')) +
    ((sz.size n : ℕ) : ℝ) ^ εq * Real.sqrt (∑ j ∈ Finset.range (K n),
      (cQVNonAltN sz E s v K n k Λg κ' ε Γ Λ D'' (K n) a j : ℝ)) +
    ((sz.size n : ℕ) : ℝ) ^ (-D_Y) +
    ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k *
      stepErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1))
        (gridStep s v K n)
        (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ k)

section Budget

variable {d : ℕ} (sz : Sizes d)

/-- The absorption step of a far part (copy of the private `nqBudget_absorb`, `NQBudget.lean:327`):
`y N_p ≤ B`, `N_p⁻¹ ≤ X`, `B ≥ 0` give `y ≤ B X`. -/
private theorem nqLin_absorb {y Np B X : ℝ} (hNp : 0 < Np) (hB : 0 ≤ B) (h : y * Np ≤ B)
    (hX : Np⁻¹ ≤ X) : y ≤ B * X := by
  have h1 : y ≤ B * Np⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hNp]; exact h
  exact h1.trans (mul_le_mul_of_nonneg_left hX hB)

/-- `0 ≤ u_i` on the grid `0 ≤ s_n ≤ v_n`. -/
private theorem nqLin_gridTime_nonneg {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hs0 : 0 ≤ s n)
    (hsv : s n ≤ v n) (i : ℕ) : 0 ≤ gridTime s v K n i := by
  have h := ST_gridTime_mono s v K n hsv (Nat.zero_le i)
  rw [ST_gridTime_zero] at h
  linarith

/-- `u_i ≤ v_n` for `i ≤ K_n`, `K_n ≠ 0`. -/
private theorem nqLin_gridTime_le {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hsv : s n ≤ v n)
    (hK : K n ≠ 0) {i : ℕ} (hi : i ≤ K n) : gridTime s v K n i ≤ v n :=
  (ST_gridTime_mono s v K n hsv hi).trans_eq (gridTime_last s v K n hK)

/-- `K Δ = v - s`. -/
private theorem nqLin_K_mul_step {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hK : K n ≠ 0) :
    (K n : ℝ) * gridStep s v K n = v n - s n := by
  have hK' : (K n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK
  unfold gridStep
  rw [mul_div_cancel₀ _ hK']

/-- **The linear drift term at the data of S3-10b** (the analogue of `tbDriftNonAltN`, `NQBudget.lean:391`): the
drift term of `assembledRHSLinN` is at most `W^{Cε} Γ²((k-2)Φ₁ + Φ₂ + Φ₃) B_v^k Σ_j Δ/η_{u_j} +
(KΔ)(W^C W^{-D'})` (`tbDriftN` with `a = Γ²((k-2)Φ₁ + Φ₂ + Φ₃) ≥ 0`, `b = 0`, the sharp kernel
`kappaNonAltN_succ_mul_Bctl_pow_le`; `dDriftLinN = a B_{u_j}^k/η_{u_j}`). -/
theorem tbDriftLinN {E s v : ℕ → ℝ} {K : ℕ → ℕ} (n k : ℕ) (Λg κ' ε : ℝ) (Γ Φ₁ Φ₂ Φ₃ : ℕ → ℝ)
    (D' : ℝ) (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1)
    (hK : K n ≠ 0) (hk : 2 ≤ k) (hΓ : 0 ≤ Γ n) (hΦ₁ : 0 ≤ Φ₁ n) (hΦ₂ : 0 ≤ Φ₂ n) (hΦ₃ : 0 ≤ Φ₃ n)
    (hη : (etaT (E n) (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) :
    gridStep s v K n * ∑ j ∈ Finset.range (K n),
      (kappaNonAltN d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) (j + 1) (K n) *
          dDriftLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) +
        epsNonAltN d k Λg κ' ((sz.W n : ℕ) : ℝ) (j + 1) (K n) * ((sz.W n : ℕ) : ℝ) ^ (-D')) ≤
      ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
          (Γ n * Γ n * (((k : ℝ) - 2) * Φ₁ n + Φ₂ n + Φ₃ n)) *
          (sz.Bctl n (v n)) ^ k *
          ∑ j ∈ Finset.range (K n), gridStep s v K n / etaT (E n) (gridTime s v K n j) +
        ((K n : ℝ) * gridStep s v K n) *
          (((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' * ((sz.W n : ℕ) : ℝ) ^ (-D')) := by
  have hW : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hu0 : ∀ i, 0 ≤ gridTime s v K n i := fun i => nqLin_gridTime_nonneg hs0 hsv i
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi =>
    (nqLin_gridTime_le hsv hK hi).trans_lt hv1
  have huK := gridTime_last s v K n hK
  have hmono : ∀ i m, i ≤ m → gridTime s v K n i ≤ gridTime s v K n m := fun i m him =>
    ST_gridTime_mono s v K n hsv him
  have hΔ0 : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n hsv
  have hN1 : (1 - v n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := nqBudget_inv_one_sub_le hE hv1 hη
  have hk2 : (0 : ℝ) ≤ (k : ℝ) - 2 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have ha0 : 0 ≤ Γ n * Γ n * (((k : ℝ) - 2) * Φ₁ n + Φ₂ n + Φ₃ n) :=
    mul_nonneg (mul_nonneg hΓ hΓ) (add_nonneg (add_nonneg (mul_nonneg hk2 hΦ₁) hΦ₂) hΦ₃)
  have hsucc : ∀ j < K n, kappaNonAltN d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε
      (gridTime s v K n) (j + 1) (K n) * (sz.Bctl n (gridTime s v K n j)) ^ k ≤
      ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
        (sz.Bctl n (gridTime s v K n (K n))) ^ k := fun j hj =>
    kappaNonAltN_succ_mul_Bctl_pow_le sz n k Λg κ' ε hW (gridTime s v K n) j (K n)
      (hmono j (j + 1) (by omega)) (hmono (j + 1) (K n) (by omega)) (hu1 _ le_rfl)
  have h := tbDriftN (E := E n) (k := k) (K := K n) (Δ := gridStep s v K n)
    (Cκ := ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε))
    (Cε := ((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ')
    (Cfar := nqBudget_kapFar sz n k Λg κ' ε)
    (a := Γ n * Γ n * (((k : ℝ) - 2) * Φ₁ n + Φ₂ n + Φ₃ n)) (b := 0)
    (δmax := ((sz.W n : ℕ) : ℝ) ^ (-D')) (gridTime s v K n)
    (fun i => sz.Bctl n (gridTime s v K n i))
    (kappaNonAltN d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n))
    (epsNonAltN d k Λg κ' ((sz.W n : ℕ) : ℝ))
    (fun j => dDriftLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n))
    (fun _ => ((sz.W n : ℕ) : ℝ) ^ (-D')) hΔ0 ha0 le_rfl
    (fun j hj => nonAlt_hκ0N d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε hW (K n) _ (j + 1) (K n)
      (by omega) le_rfl)
    (fun j hj => nonAlt_hε0N d k Λg κ' ((sz.W n : ℕ) : ℝ) hW (K n) (j + 1) (K n) (by omega) le_rfl)
    hsucc
    (fun j hj => nqBudget_kappa_le_kapFar sz n k Λg κ' ε (gridTime s v K n) (hu0 (j + 1))
      (hmono (j + 1) (K n) (by omega)) (hu1 _ le_rfl) (by rw [huK]; exact hN1))
    (fun _ _ => le_rfl)
    (fun j hj => by
      unfold dDriftLinN
      rw [add_zero]
      apply le_of_eq
      rw [div_eq_mul_inv]; ring)
    (fun _ _ => Real.rpow_nonneg hW _) (fun _ _ => le_rfl)
    (fun j hj => etaT_pos hE (hu1 j hj.le))
  rw [huK] at h
  simpa only [mul_zero, zero_add] using h

/-- The final bookkeeping of the linear budget on plain reals: the six term bounds `t₁ ≤ P₀X/6`, `t₂ ≤ P₀X/12`,
`t₃ ≤ P₀(Φ₁+Φ₂+Φ₃)X/12 + P₀X/12`, `t₄ ≤ P₀Λ^{1/2}X/12 + P₀X/12`, `t₅, t₆ ≤ P₀X/6` give
`Σ t ≤ P₀ (Λ^{1/2} + Φ₁ + Φ₂ + Φ₃) X` (coefficients of `Λ^{1/2}X`: `5/6`; of each `Φ_iX`: `1/12`; `X ≤ Λ^{1/2} X`
for `Λ^{1/2} ≥ 1`; the analogue of `nqBudget_final`, `NQBudget.lean:527`, with `Φ + Φ²` replaced by
`Φ₁ + Φ₂ + Φ₃`). -/
private theorem nqLin_final {t1 t2 t3 t4 t5 t6 P0 X Λr Φ₁ Φ₂ Φ₃ : ℝ} (hP0 : 0 ≤ P0) (hX : 0 ≤ X)
    (hΛr : 1 ≤ Λr) (hΦ₁ : 0 ≤ Φ₁) (hΦ₂ : 0 ≤ Φ₂) (hΦ₃ : 0 ≤ Φ₃) (T1 : t1 ≤ P0 / 6 * X)
    (T2 : t2 ≤ P0 / 12 * X) (T3 : t3 ≤ P0 / 12 * ((Φ₁ + Φ₂ + Φ₃) * X) + P0 / 12 * X)
    (T4 : t4 ≤ P0 / 12 * (Λr * X) + P0 / 12 * X) (T5 : t5 ≤ P0 / 6 * X)
    (T6 : t6 ≤ P0 / 6 * X) :
    t1 + t2 + t3 + t4 + t5 + t6 ≤ P0 * (Λr + Φ₁ + Φ₂ + Φ₃) * X := by
  have hPX : P0 * X ≤ P0 * (Λr * X) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hX hΛr) hP0
  have hΦ₁X : 0 ≤ P0 * (Φ₁ * X) := mul_nonneg hP0 (mul_nonneg hΦ₁ hX)
  have hΦ₂X : 0 ≤ P0 * (Φ₂ * X) := mul_nonneg hP0 (mul_nonneg hΦ₂ hX)
  have hΦ₃X : 0 ≤ P0 * (Φ₃ * X) := mul_nonneg hP0 (mul_nonneg hΦ₃ hX)
  have e : P0 * (Λr + Φ₁ + Φ₂ + Φ₃) * X =
      P0 * (Λr * X) + P0 * (Φ₁ * X) + P0 * (Φ₂ * X) + P0 * (Φ₃ * X) := by ring
  rw [e]
  nlinarith [T1, T2, T3, T4, T5, T6, hPX, hΦ₁X, hΦ₂X, hΦ₃X]

set_option maxHeartbeats 400000 in
-- the 450-line proof of `budgetNonAltN` with a longer drift term needs more than 200000
/-- **The (5.93) budget of the non-alternating endpoint at the linear drift** (`d ≥ 3`; the merged
`budgetNonAltN`, `NQBudget.lean:555`, with `dDriftLinN`): at a fixed `n`, under explicit numerical inequalities
only, `assembledRHSLinN ≤ N^{ε₀} (Λ^{1/2} + Φ₁ + Φ₂ + Φ₃) B_v^k`.  `ha2` has `Γ²` (`(N^{ε₁})²`) in place of `Γ³`;
no `Φ²`, no crude level (`tbInitNonAltN`, `tbQvNonAltN` unchanged; the drift term is `tbDriftLinN`;
final bookkeeping `nqLin_final`). -/
theorem budgetNonAltLinN {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (Λg κ' ε : ℝ) (Γ Λ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (D' D'' D_Y D_t τK εq ε₀ ε₁ X0 : ℝ)
    (a : Fin k → Zd d (sz.L n))
    (hk : 2 ≤ k) (hε₁ : 0 ≤ ε₁) (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n)
    (hv1 : v n < 1) (hK : K n ≠ 0)
    (hη : (etaT (E n) (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ))
    (hΔη : gridStep s v K n * (etaT (E n) (v n))⁻¹ ≤ 1)
    (hΓ : Γ n = ((sz.size n : ℕ) : ℝ) ^ ε₁) (hΛ : 1 ≤ Λ n) (hΦ₁ : 0 ≤ Φ₁ n) (hΦ₂ : 0 ≤ Φ₂ n)
    (hΦ₃ : 0 ≤ Φ₃ n)
    (hlog : ∑ j ∈ Finset.range (K n), gridStep s v K n / etaT (E n) (gridTime s v K n j) ≤
      (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ))
    (hX0 : X0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ k)
    (hR : ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k *
        stepErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1))
          (gridStep s v K n)
          (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ k) ≤
      ((sz.size n : ℕ) : ℝ) ^ (-D_t))
    (ha1 : ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) * ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6)
    (ha2 : (k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
        (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 2 *
        ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12)
    (ha3 : ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
        ((sz.size n : ℕ) : ℝ) ^ ε₁ *
        Real.sqrt ((k : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1))) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12)
    (he1 : ((sz.size n : ℕ) : ℝ) ^ k *
        (((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' * ((sz.W n : ℕ) : ℝ) ^ (-D')) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12)
    (he2 : ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.size n : ℕ) : ℝ) ^ k *
        Real.sqrt ((k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε * ((sz.W n : ℕ) : ℝ) ^ (-D'')))) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12)
    (he3 : ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-D_Y) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6)
    (he4 : ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-D_t) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6) :
    assembledRHSLinN sz E s v K n k Λg κ' ε Γ Λ Φ₁ Φ₂ Φ₃ D' D'' D_Y τK εq X0 a ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n) *
        (sz.Bctl n (v n)) ^ k := by
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
    have h : 1 ≤ (sz.W n * sz.L n) ^ d :=
      Nat.one_le_pow _ _ (Nat.mul_pos (sz.W_pos n) (by have := sz.three_le_L n; omega))
    exact_mod_cast (show 1 ≤ sz.size n from h)
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hNk : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) ^ k := pow_pos hN0 k
  have hW0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hu0 : ∀ i, 0 ≤ gridTime s v K n i := fun i => nqLin_gridTime_nonneg hs0 hsv i
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi =>
    (nqLin_gridTime_le hsv hK hi).trans_lt hv1
  have huK := gridTime_last s v K n hK
  have hΔ0 : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n hsv
  have hKΔ1 : (K n : ℝ) * gridStep s v K n ≤ 1 := by
    rw [nqLin_K_mul_step hK]; linarith
  have hΓ0 : 0 ≤ Γ n := by rw [hΓ]; exact Real.rpow_nonneg hN0.le _
  have hΓ1 : 1 ≤ Γ n := by rw [hΓ]; exact Real.one_le_rpow hN1 hε₁
  have hΛ0 : 0 ≤ Λ n := by linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hBv0 := Sizes.STBctl_pos sz n hv1
  have hX0' : 0 ≤ (sz.Bctl n (v n)) ^ k := pow_nonneg hBv0.le _
  have hXN : (((sz.size n : ℕ) : ℝ) ^ k)⁻¹ ≤ (sz.Bctl n (v n)) ^ k := by
    rw [← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 hN0.le)
      (ContinuityNet.cont_inv_size_le_Bctl sz n (hs0.trans hsv) hv1) k
  have hP0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ := Real.rpow_nonneg hN0.le _
  have hLs0 : 0 ≤ (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) :=
    mul_nonneg (inv_nonneg.2 (mE_im_pos hE).le) (Real.log_nonneg hN1)
  have hWC0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' := Real.rpow_nonneg hW0 _
  have hWD0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D') := Real.rpow_nonneg hW0 _
  have hWCε0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) :=
    Real.rpow_nonneg hW0 _
  have hΛr1 : 1 ≤ Λ n ^ ((1 : ℝ) / 2) := Real.one_le_rpow hΛ (by norm_num)
  -- the far part `W^C W^{-D'}` is absorbed once (`he1`)
  have hfar : ((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ k :=
    nqLin_absorb hNk (by positivity) ((mul_comm _ _).trans_le he1) hXN
  -- T1: the initial term
  have T1 : _ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 * (sz.Bctl n (v n)) ^ k :=
    (tbInitNonAltN sz n k Λg κ' ε (((sz.size n : ℕ) : ℝ) ^ ε₁) X0 hs0 hsv hv1 hK
      (Real.rpow_nonneg hN0.le _) hX0).trans (mul_le_mul_of_nonneg_right ha1 hX0')
  -- T2: the initial decay error
  have T2 : epsNonAltN d k Λg κ' ((sz.W n : ℕ) : ℝ) 0 (K n) * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ k := by
    unfold epsNonAltN
    exact hfar
  -- T3: the drift term (linear in the levels `Φ₁, Φ₂, Φ₃`)
  have T3 : gridStep s v K n * ∑ j ∈ Finset.range (K n),
      (kappaNonAltN d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) (j + 1) (K n) *
          dDriftLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) +
        epsNonAltN d k Λg κ' ((sz.W n : ℕ) : ℝ) (j + 1) (K n) * ((sz.W n : ℕ) : ℝ) ^ (-D')) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (((Φ₁ n + Φ₂ n + Φ₃ n)) * (sz.Bctl n (v n)) ^ k) +
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ k := by
    have h := tbDriftLinN sz n k Λg κ' ε Γ Φ₁ Φ₂ Φ₃ D' hE hs0 hsv hv1 hK hk hΓ0 hΦ₁ hΦ₂ hΦ₃ hη
    refine h.trans ?_
    have hk2 : (0 : ℝ) ≤ (k : ℝ) - 2 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have ha0 : 0 ≤ Γ n * Γ n * (((k : ℝ) - 2) * Φ₁ n + Φ₂ n + Φ₃ n) :=
      mul_nonneg (mul_nonneg hΓ0 hΓ0) (add_nonneg (add_nonneg (mul_nonneg hk2 hΦ₁) hΦ₂) hΦ₃)
    have ha_le : Γ n * Γ n * (((k : ℝ) - 2) * Φ₁ n + Φ₂ n + Φ₃ n) ≤
        (k : ℝ) * Γ n ^ 2 * (Φ₁ n + Φ₂ n + Φ₃ n) := by
      have h0 : 0 ≤ Γ n ^ 2 * (2 * Φ₁ n + ((k : ℝ) - 1) * Φ₂ n + ((k : ℝ) - 1) * Φ₃ n) := by
        refine mul_nonneg (sq_nonneg _) ?_
        have h1 : 0 ≤ (k : ℝ) - 1 := by linarith
        nlinarith [mul_nonneg h1 hΦ₂, mul_nonneg h1 hΦ₃]
      have e : (k : ℝ) * Γ n ^ 2 * (Φ₁ n + Φ₂ n + Φ₃ n) -
          Γ n * Γ n * (((k : ℝ) - 2) * Φ₁ n + Φ₂ n + Φ₃ n) =
          Γ n ^ 2 * (2 * Φ₁ n + ((k : ℝ) - 1) * Φ₂ n + ((k : ℝ) - 1) * Φ₃ n) := by ring
      linarith
    have m1 : ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
          (Γ n * Γ n * (((k : ℝ) - 2) * Φ₁ n + Φ₂ n + Φ₃ n)) *
          (sz.Bctl n (v n)) ^ k *
          ∑ j ∈ Finset.range (K n), gridStep s v K n / etaT (E n) (gridTime s v K n j) ≤
        ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
          (Γ n * Γ n * (((k : ℝ) - 2) * Φ₁ n + Φ₂ n + Φ₃ n)) *
          (sz.Bctl n (v n)) ^ k *
          ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (mul_nonneg (mul_nonneg hWCε0 ha0) hX0')
    have m2 : ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
          (Γ n * Γ n * (((k : ℝ) - 2) * Φ₁ n + Φ₂ n + Φ₃ n)) *
          (sz.Bctl n (v n)) ^ k *
          ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) ≤
        ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
          ((k : ℝ) * Γ n ^ 2 * (Φ₁ n + Φ₂ n + Φ₃ n)) *
          (sz.Bctl n (v n)) ^ k *
          ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha_le hWCε0) hX0') hLs0
    have m3 : ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
          ((k : ℝ) * Γ n ^ 2 * (Φ₁ n + Φ₂ n + Φ₃ n)) *
          (sz.Bctl n (v n)) ^ k *
          ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) =
        ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
          (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 2 *
          ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ))) *
          ((Φ₁ n + Φ₂ n + Φ₃ n) * (sz.Bctl n (v n)) ^ k) := by
      rw [hΓ]; ring
    have m4 : ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
          (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 2 *
          ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ))) *
          ((Φ₁ n + Φ₂ n + Φ₃ n) * (sz.Bctl n (v n)) ^ k) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * ((Φ₁ n + Φ₂ n + Φ₃ n) * (sz.Bctl n (v n)) ^ k) :=
      mul_le_mul_of_nonneg_right ha2 (mul_nonneg (by positivity) hX0')
    have f1 : ((K n : ℝ) * gridStep s v K n) *
          (((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' * ((sz.W n : ℕ) : ℝ) ^ (-D')) ≤
        ((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' * ((sz.W n : ℕ) : ℝ) ^ (-D') :=
      (mul_le_mul_of_nonneg_right hKΔ1 (mul_nonneg hWC0 hWD0)).trans_eq (one_mul _)
    exact add_le_add (m1.trans (m2.trans (m3.le.trans m4))) (f1.trans hfar)
  -- T4: the quadratic-variation term (unchanged)
  have T4 : ((sz.size n : ℕ) : ℝ) ^ εq * Real.sqrt (∑ j ∈ Finset.range (K n),
      (cQVNonAltN sz E s v K n k Λg κ' ε Γ Λ D'' (K n) a j : ℝ)) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (Λ n ^ ((1 : ℝ) / 2) * (sz.Bctl n (v n)) ^ k) +
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ k := by
    have h := tbQvNonAltN sz n k Λg κ' ε Γ Λ D'' a hE hs0 hsv hv1 hK hΛ0 hη
    have hSv : ∑ j ∈ Finset.range (K n),
        gridStep s v K n / etaT (E n) (gridTime s v K n (j + 1)) ≤
        (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1 := by
      have hsucc := nqBudget_sum_succ_le (K := K n)
        (fun j => gridStep s v K n / etaT (E n) (gridTime s v K n j))
        (div_nonneg hΔ0 (etaT_pos hE (hu1 0 (Nat.zero_le _))).le)
      simp only [huK] at hsucc
      have hlast : gridStep s v K n / etaT (E n) (v n) ≤ 1 := by
        rw [div_eq_mul_inv]; exact hΔη
      linarith
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hQe0 : 0 ≤ (k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε * ((sz.W n : ℕ) : ℝ) ^ (-D'')) := by
      have hq : 0 ≤ nqBudget_qvFar sz n k Λg κ' ε := by
        unfold nqBudget_qvFar nqBudget_kapFar
        have hr : 0 ≤ (1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ) := by positivity
        have h1 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
            ((1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ)) ^ (k - 1) := by positivity
        have h2 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ k := by positivity
        have h3 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' := hWC0
        positivity
      positivity
    have hΓX : 0 ≤ Γ n * (sz.Bctl n (v n)) ^ k := mul_nonneg hΓ0 hX0'
    have hZ0 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
        (Γ n * (sz.Bctl n (v n)) ^ k)) ^ 2 * ((k : ℝ) * (
        (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) * Λ n) := by
      have : 0 ≤ (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1 := by linarith
      positivity
    have hsum : ∑ j ∈ Finset.range (K n),
        (cQVNonAltN sz E s v K n k Λg κ' ε Γ Λ D'' (K n) a j : ℝ) ≤
        (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) * (Γ n * (sz.Bctl n (v n)) ^ k)) ^ 2 *
          ((k : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) * Λ n) +
        (k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε * ((sz.W n : ℕ) : ℝ) ^ (-D'')) := by
      refine h.trans ?_
      have hc0 : 0 ≤ (k : ℝ) * (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε)) ^ 2 *
          (Γ n * (Γ n * Λ n)) * ((sz.Bctl n (v n)) ^ k) ^ 2 := by
        have : Γ n * (Γ n * Λ n) = Γ n ^ 2 * Λ n := by ring
        rw [this]; positivity
      have n1 := mul_le_mul_of_nonneg_left hSv hc0
      have n2 : ((K n : ℝ) * gridStep s v K n) *
          ((k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε * ((sz.W n : ℕ) : ℝ) ^ (-D''))) ≤
          (k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε * ((sz.W n : ℕ) : ℝ) ^ (-D'')) :=
        (mul_le_mul_of_nonneg_right hKΔ1 hQe0).trans_eq (one_mul _)
      have e : (k : ℝ) * (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε)) ^ 2 *
            (Γ n * (Γ n * Λ n)) * ((sz.Bctl n (v n)) ^ k) ^ 2 *
            ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) =
          (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) * (Γ n * (sz.Bctl n (v n)) ^ k)) ^ 2 *
            ((k : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) * Λ n) := by ring
      linarith
    have hs1 := Real.sqrt_le_sqrt hsum
    have hs2 : Real.sqrt ((((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
          (Γ n * (sz.Bctl n (v n)) ^ k)) ^ 2 *
          ((k : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) * Λ n) +
        (k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε * ((sz.W n : ℕ) : ℝ) ^ (-D''))) ≤
        ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) * (Γ n * (sz.Bctl n (v n)) ^ k) *
          (Real.sqrt ((k : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)) *
            Real.sqrt (Λ n)) +
        Real.sqrt ((k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε * ((sz.W n : ℕ) : ℝ) ^ (-D''))) := by
      refine (nqBudget_sqrt_add_le hZ0 hQe0).trans ?_
      have hA0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
          (Γ n * (sz.Bctl n (v n)) ^ k) := mul_nonneg hWCε0 hΓX
      have hP00 : 0 ≤ (k : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) :=
        mul_nonneg hk0 (by linarith)
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hA0, Real.sqrt_mul hP00]
    have hsΛ : Real.sqrt (Λ n) = Λ n ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow (Λ n)
    have hNe : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ εq := Real.rpow_nonneg hN0.le _
    have k1 : ((sz.size n : ℕ) : ℝ) ^ εq *
        (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) * (Γ n * (sz.Bctl n (v n)) ^ k) *
          (Real.sqrt ((k : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)) *
            Real.sqrt (Λ n))) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (Λ n ^ ((1 : ℝ) / 2) * (sz.Bctl n (v n)) ^ k) := by
      have e : ((sz.size n : ℕ) : ℝ) ^ εq *
          (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) * (Γ n * (sz.Bctl n (v n)) ^ k) *
            (Real.sqrt ((k : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)) *
              Real.sqrt (Λ n))) =
          (((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
            ((sz.size n : ℕ) : ℝ) ^ ε₁ *
            Real.sqrt ((k : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)))) *
          (Λ n ^ ((1 : ℝ) / 2) * (sz.Bctl n (v n)) ^ k) := by
        rw [hsΛ, hΓ]; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right ha3 (mul_nonneg (by linarith) hX0')
    have k2 : ((sz.size n : ℕ) : ℝ) ^ εq *
        Real.sqrt ((k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε * ((sz.W n : ℕ) : ℝ) ^ (-D''))) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ k := by
      refine nqLin_absorb hNk (by positivity) ?_ hXN
      have e : ((sz.size n : ℕ) : ℝ) ^ εq *
          Real.sqrt ((k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε * ((sz.W n : ℕ) : ℝ) ^ (-D''))) *
            ((sz.size n : ℕ) : ℝ) ^ k =
          ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.size n : ℕ) : ℝ) ^ k *
            Real.sqrt ((k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε *
              ((sz.W n : ℕ) : ℝ) ^ (-D'')))) := by ring
      rw [e]; exact he2
    calc ((sz.size n : ℕ) : ℝ) ^ εq * Real.sqrt (∑ j ∈ Finset.range (K n),
          (cQVNonAltN sz E s v K n k Λg κ' ε Γ Λ D'' (K n) a j : ℝ))
        ≤ ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
            (Γ n * (sz.Bctl n (v n)) ^ k) *
            (Real.sqrt ((k : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)) *
              Real.sqrt (Λ n)) +
          Real.sqrt ((k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε * ((sz.W n : ℕ) : ℝ) ^ (-D'')))) :=
          mul_le_mul_of_nonneg_left (hs1.trans hs2) hNe
      _ = ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
            (Γ n * (sz.Bctl n (v n)) ^ k) *
            (Real.sqrt ((k : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)) *
              Real.sqrt (Λ n))) +
          ((sz.size n : ℕ) : ℝ) ^ εq *
            Real.sqrt ((k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε *
              ((sz.W n : ℕ) : ℝ) ^ (-D''))) := by ring
      _ ≤ _ := add_le_add k1 k2
  -- T5, T6
  have T5 : ((sz.size n : ℕ) : ℝ) ^ (-D_Y) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 * (sz.Bctl n (v n)) ^ k :=
    nqLin_absorb hNk (by positivity) ((mul_comm _ _).trans_le he3) hXN
  have T6 : _ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 * (sz.Bctl n (v n)) ^ k :=
    hR.trans (nqLin_absorb hNk (by positivity) ((mul_comm _ _).trans_le he4) hXN)
  unfold assembledRHSLinN
  exact nqLin_final hP0 hX0' hΛr1 hΦ₁ hΦ₂ hΦ₃ T1 T2 T3 T4 T5 T6

end Budget

/-! ## 6. Compiled nonempty instances at `d = 3`

Data (the merged instance data of `GridGoodN` §7, `AzumaProxyN` §6, `NQGood1` §6, `NQGood2` §5, `NQBudget` §6):
`sz0` (`n = 0`: `L = 4`, `W = 32`, `N = 2^21`, `lam = 1/64`), `E ≡ 1/2` (`Im m = √15/4 ≈ 0.968`), `s ≡ 0`, `v ≡ 1/32`,
`K ≡ 4` (`Δ = 1/128`, `u_j = j/128`), `k = 3`, `σ = (+,-,+)`, `Λ_g = 10`, `κ' = 1/2`, `ε = 4/5`, crude levels
`(Γ, Λ, Φ) = (4, 3, 1)` of `GoodSetN`, linear levels `(Φ₁, Φ₂, Φ₃) = (1, 12, 1)` (`12 = kΓΦ²`, so that
`GoodSetN ⊆ GoodLinN` there, `goodSetN_subset_goodLinN`), `τ' = 1/5`, `D' = 6`, `D'' = 5`, `ε₀ = C + 12` with the
abstract `C = nqGood1C 3 3 10 (1/2) > 0`.
* (2) the exit time `nqLinExitTauN … = NQGood2Inst.tau0`, positive at every sample; the drift bound
  `driftTensorN_norm_le_of_goodLin` at `0 ∈ GoodLinN`; `nqLin_hdriftN`, `mem_of_lt_nqLinExitTauN`,
  `nqLinExitMeasN`, `subGaussStop_linN` at the data of `NQGood2Inst.subGaussStop_instance`;
* (3) `nqLinGood_holds 3` through `inst_ing` at `(sz0, z0, 0, 1/16)`, `v ≡ 1/32`, `K ≡ 4`, `XL ≡ XLK ≡ 1`, `ε = 1/10`,
  `k ∈ {2, 4}`; the premises `STKbound`, `STKward`, `STLK`, `STStep2Concl` of `STIngR` and the Step 3-4 conclusions
  `STLmaxU`, `STLKU` (other gates' pins) are hypotheses; `hX`, `hY` of `NQLinConcl` are *discharged* from them;
* (4) `budgetNonAltLinN`: every hypothesis discharged (`hlog`, `hR` by the merged `NQBudgetInst`, `ha1`-`he4` for every
  `C > 0`; `ha2` with `(N^{ε₁})² = 16`). -/

/-! ### (2) The exit time, the linear drift and the sub-Gaussian input at the data of `NQGood2Inst` -/

/-! ### (3) `nqLinGood_holds` at the data: with high probability the grid walk is in `GoodLinN` at every `j ≤ 4`

`inst_ing` (the merged shape of the instances of `STIngR`) at `(sz0, z0, 0, 1/16)`, the grid end `v ≡ 1/32`
(`Δ = 1/128`, `u_j = j/128`), `K ≡ 4` (`K + 1 = 5 ≤ N^1`), `XL ≡ XLK ≡ 1`, `ε = 1/10`.  The hypotheses `STKbound`,
`STKward`, `STLK`, `STStep2Concl` and `STLmaxU`, `STLKU` are other gates' pins and stay hypotheses; `hX`, `hY` of
`NQLinConcl` (window `[0, 1/32]`) are *discharged* from the last two (`nqLin_prec_XiL_one`,
`nqLin_prec_XiLK_one` after the restriction from `[0, 1/16]`), and `0 ≤ s ≤ v ≤ t`, `K ≠ 0`, `K + 1 ≤ N^C`, the
controls `≥ 1` are proved at the data. -/

/-! ### (4) `budgetNonAltLinN` at the data of `NQBudgetInst.budgetNonAltN_instance`

`d = 3`, `sz0`, `n = 0`: `Γ = N^{2/21} = 4`, `Λ = 3`, `Φ₁ = Φ₃ = 1`, `Φ₂ = 12` (`= kΓΦ²`), `D' = 6`, `D'' = 5`, `D_Y = 1`,
`D_t = -5`, `τ_K = 1/21`, `ε_q = 1`, `ε₀ = C + 12`, `X0 = 4 B_0^3`, label `aFar`.  `hlog`, `hR` are the merged
`NQBudgetInst.hlog_instance`, `hR_instance`; `ha1`, `ha3`, `he1`-`he4` are re-derived (the originals are private to
`NQBudget`), `ha2` is the new inequality with `(N^{ε₁})² = 16`. -/

end RBM.Ind

end
