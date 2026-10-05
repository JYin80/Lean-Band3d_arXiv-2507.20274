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

/-- **Target `goodSetN_subset_goodLinN`**: `GoodSetN` lies in `GoodLinN` at `Φ₁ = Φ₃ = Φ`, `Φ₂ = kΓΦ²` (the
merged quadratic level; (D2) rewrites by `ring`). -/
theorem goodSetN_subset_goodLinN {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (k : ℕ)
    (Γ Λ Φ τ' D' : ℝ) :
    sz.GoodSetN n E u k Γ Λ Φ τ' D' ⊆ GoodLinN sz n E u k Γ Φ ((k : ℝ) * Γ * Φ ^ 2) Φ := by
  intro H hH
  obtain ⟨-, -, -, hD1, hD2, hD3, -, -, -⟩ := hH
  refine ⟨hD1, fun σ a => ?_, hD3⟩
  have h := hD2 σ a
  have e : Γ * ((k : ℝ) * (Γ * Φ) ^ 2) * ((sz.Bctl n u) ^ k / etaT E u) =
      Γ * (Γ * ((k : ℝ) * Γ * Φ ^ 2)) * ((sz.Bctl n u) ^ k / etaT E u) := by ring
  rw [← e]
  exact h

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

section LevelsOne

variable {d : ℕ}

/-- `Prec` from its `w.h.p.` form for every exponent (copy of the private `gridGood_prec_of_whp`). -/
private theorem nqLin_prec_of_whp (sz : Sizes d) {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (h : ∀ τ : ℝ, 0 < τ → Whp sz (fun n => {ω | ∀ u : U n,
      ξ n u ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ n u ω})) : Prec sz ξ ζ := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with n hn
  refine le_trans (le_of_eq ?_) hn
  congr 1
  ext ω
  simp [badSetAt]

private theorem nqLin_one_add_le {a : ℝ} (ha : 2 ≤ a) : 1 + a ≤ a * a := by nlinarith

/-- `Ξ̂^{(𝓛)}_m ≺ 1` on the window from `STLmaxU` (copy of `gridGood_prec_XiL_one`). -/
private theorem nqLin_prec_XiL_one (sz : Sizes d) (hsz : sz.SizeTendsto) {E s t : ℕ → ℝ}
    (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hL : STLmaxU sz E s t) {m : ℕ} (hm : 1 ≤ m) :
    Prec sz (U := fun n => TimeIcc s t n) (fun n u ω => STXiL sz n (E n) (u : ℝ) m ω)
      (fun _ _ _ => (1 : ℝ)) := by
  refine nqLin_prec_of_whp sz fun τ hτ => ?_
  have hw := (hL m hm).whp sz (half_pos hτ)
  refine hw.mono ?_
  filter_upwards [((tendsto_rpow_atTop (half_pos hτ)).comp hsz).eventually_ge_atTop 2] with n hN2 ω hω u
  have hBpos : 0 < sz.Bctl n (u : ℝ) := st_Bctl_pos sz ((u.2.2).trans_lt (ht1 n))
  have hpb : 0 < (sz.Bctl n (u : ℝ)) ^ (m - 1) := pow_pos hBpos _
  have hmax : STmaxL sz n (E n) (u : ℝ) m ω ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
      (sz.Bctl n (u : ℝ)) ^ (m - 1) :=
    Finset.sup'_le _ _ fun p _ => hω (u, p)
  have hdiv : STmaxL sz n (E n) (u : ℝ) m ω / (sz.Bctl n (u : ℝ)) ^ (m - 1) ≤
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    rw [div_le_iff₀ hpb]; exact hmax
  have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsq : ((sz.size n : ℕ) : ℝ) ^ τ =
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add' hN0 (by linarith)]; ring_nf
  calc STXiL sz n (E n) (u : ℝ) m ω = 1 + STmaxL sz n (E n) (u : ℝ) m ω /
        (sz.Bctl n (u : ℝ)) ^ (m - 1) := rfl
    _ ≤ 1 + ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by linarith
    _ ≤ _ := nqLin_one_add_le hN2
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * 1 := by rw [hsq, mul_one]

/-- `Ξ̂^{(𝓛-𝒦)}_m ≺ 1` on the window from `STLKU` (copy of `gridGood_prec_XiLK_one`). -/
private theorem nqLin_prec_XiLK_one (sz : Sizes d) (hsz : sz.SizeTendsto) {E s t : ℕ → ℝ}
    (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hL : STLKU sz E s t) {m : ℕ} (hm : 1 ≤ m) :
    Prec sz (U := fun n => TimeIcc s t n) (fun n u ω => STXiLK sz n (E n) (u : ℝ) m ω)
      (fun _ _ _ => (1 : ℝ)) := by
  refine nqLin_prec_of_whp sz fun τ hτ => ?_
  have hw := (hL m hm).whp sz (half_pos hτ)
  refine hw.mono ?_
  filter_upwards [((tendsto_rpow_atTop (half_pos hτ)).comp hsz).eventually_ge_atTop 2] with n hN2 ω hω u
  have hBpos : 0 < sz.Bctl n (u : ℝ) := st_Bctl_pos sz ((u.2.2).trans_lt (ht1 n))
  have hpb : 0 < (sz.Bctl n (u : ℝ)) ^ m := pow_pos hBpos _
  have hmax : STmaxLK sz n (E n) (u : ℝ) m ω ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
      (sz.Bctl n (u : ℝ)) ^ m :=
    Finset.sup'_le _ _ fun p _ => hω (u, p)
  have hdiv : STmaxLK sz n (E n) (u : ℝ) m ω / (sz.Bctl n (u : ℝ)) ^ m ≤
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    rw [div_le_iff₀ hpb]; exact hmax
  have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsq : ((sz.size n : ℕ) : ℝ) ^ τ =
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add' hN0 (by linarith)]; ring_nf
  calc STXiLK sz n (E n) (u : ℝ) m ω = 1 + STmaxLK sz n (E n) (u : ℝ) m ω /
        (sz.Bctl n (u : ℝ)) ^ m := rfl
    _ ≤ 1 + ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by linarith
    _ ≤ _ := nqLin_one_add_le hN2
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * 1 := by rw [hsq, mul_one]

/-- `STLmaxU` on `[s,t]` gives it on `[s,v]`, `v ≤ t` (restriction of the parameter set). -/
private theorem nqLin_LmaxU_restrict {sz : Sizes d} {E s t v : ℕ → ℝ} (hvt : ∀ n, v n ≤ t n)
    (h : STLmaxU sz E s t) : STLmaxU sz E s v := fun k hk =>
  StochDomAt.precomp_param
    (V := fun n => TimeIcc s v n × (Fin k → Bool) × (Fin k → Zd d (sz.L n))) (h k hk)
    (fun n p => (⟨p.1.1, p.1.2.1, p.1.2.2.trans (hvt n)⟩, p.2))

/-- `STLKU` on `[s,t]` gives it on `[s,v]`, `v ≤ t`. -/
private theorem nqLin_LKU_restrict {sz : Sizes d} {E s t v : ℕ → ℝ} (hvt : ∀ n, v n ≤ t n)
    (h : STLKU sz E s t) : STLKU sz E s v := fun k hk =>
  StochDomAt.precomp_param
    (V := fun n => TimeIcc s v n × (Fin k → Bool) × (Fin k → Zd d (sz.L n))) (h k hk)
    (fun n p => (⟨p.1.1, p.1.2.1, p.1.2.2.trans (hvt n)⟩, p.2))

end LevelsOne

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

/-- **Target `dDriftNonAltN_eq_lin`**: the merged quadratic level is the linear level at `Φ₁ = Φ₃ = Φ`,
`Φ₂ = kΓΦ²` (by `ring`). -/
theorem dDriftNonAltN_eq_lin {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (k : ℕ) (Γ Φ : ℝ) :
    dDriftNonAltN sz n E u k Γ Φ = dDriftLinN sz n E u k Γ Φ ((k : ℝ) * Γ * Φ ^ 2) Φ := by
  unfold dDriftNonAltN dDriftLinN
  ring

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

namespace NQLinInst

open Filter RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst
  RBM.Gauss.GridGoodNInst RBM.Gauss.Step34Inst RBM.Ind.AzumaProxyNInst RBM.Ind.NQGood1Inst
  RBM.Ind.NQGood2Inst

private theorem W0 : ((sz0.W 0 : ℕ) : ℝ) = 32 := by rw [sz0_values.2.1]; norm_num

private theorem lam0 : sz0.lam 0 = 1 / 64 := sz0_values.2.2.2

private theorem L0 : sz0.L 0 = 4 := sz0_values.1

private theorem L0r : ((sz0.L 0 : ℕ) : ℝ) = 4 := by rw [L0]; norm_num

private theorem N0 : ((sz0.size 0 : ℕ) : ℝ) = 2097152 := by rw [sz0_values.2.2.1]; norm_num

private theorem rpow32_fifth : (32 : ℝ) ^ ((1 : ℝ) / 5) = 2 := by
  have : (32 : ℝ) = 2 ^ (5 : ℝ) := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  rw [this, ← Real.rpow_mul (by norm_num)]; norm_num

private theorem rpow32_four_fifth : (32 : ℝ) ^ ((4 : ℝ) / 5) = 16 := by
  have : (32 : ℝ) = 2 ^ (5 : ℝ) := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  rw [this, ← Real.rpow_mul (by norm_num)]
  rw [show (5 : ℝ) * (4 / 5) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num

private theorem abs_half : |(1 / 2 : ℝ)| < 2 := by norm_num [abs_of_pos]

private theorem im_ge : (24 / 25 : ℝ) ≤ (mE (1 / 2)).im := by
  rw [mE_im]
  have : (48 / 25 : ℝ) ≤ Real.sqrt (4 - (1 / 2) ^ 2) := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num
  linarith

private theorem im_mE_half : (1 / 2 : ℝ) ≤ (mE (1 / 2)).im := by
  have := im_ge
  linarith

private theorem hσ3 : ∃ i : Fin 3, sig3 i = sig3 (finRotate 3 i) := ⟨2, by decide⟩

private theorem hW1 : 1 < ((sz0.W 0 : ℕ) : ℝ) := by rw [W0]; norm_num

private theorem hWε : 4 ≤ ((sz0.W 0 : ℕ) : ℝ) ^ (4 / 5 : ℝ) := by
  rw [W0, rpow32_four_fifth]; norm_num

private theorem hdW : ((3 : ℕ) : ℝ) * ((sz0.W 0 : ℕ) : ℝ) ^ (1 / 5 : ℝ) ≤
    ((sz0.W 0 : ℕ) : ℝ) ^ (4 / 5 : ℝ) := by
  rw [W0, rpow32_fifth, rpow32_four_fifth]; norm_num

private theorem hvL : vg 0 ≤ 1 - sz0.lam 0 ^ 2 / ((sz0.L 0 : ℕ) : ℝ) ^ 2 := by
  have : vg 0 = 1 / 32 := rfl
  rw [this, lam0, L0r]; norm_num

/-! ### (2) The exit time, the linear drift and the sub-Gaussian input at the data of `NQGood2Inst` -/

/-- **The exit time of `GoodSetN ∩ GoodLinN` at the data is the merged exit time** `tau0` (levels `(4, 3, 1)`,
`τ' = 1/5`, `D' = 6`): `GoodSetN ⊆ GoodLinN` at `Φ₂ = 3 · 4 · 1² = 12` (`goodSetN_subset_goodLinN`). -/
theorem nqLinExitTauN_eq_tau0 :
    nqLinExitTauN sz0 Einst sInst vg Kg 3 Γ4 Λ3 Φ1 Φ1 (fun _ => 12) Φ1 (1 / 5) 6 0 = tau0 := by
  unfold nqLinExitTauN tau0 goodExitTauN
  congr 1
  funext j
  ext H
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    have h2 := goodSetN_subset_goodLinN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 j) 3 (Γ4 0) (Λ3 0)
      (Φ1 0) (1 / 5) 6 h
    have e : ((3 : ℕ) : ℝ) * Γ4 0 * Φ1 0 ^ 2 = (fun _ : ℕ => (12 : ℝ)) 0 := by norm_num
    rw [e] at h2
    exact h2

/-- **The exit time is positive at every sample** (`tau0_pos`: `H_0 = 0 ∈ GoodSetN`). -/
theorem nqLinExitTauN_pos (ω : PathΩ sz0) :
    0 < nqLinExitTauN sz0 Einst sInst vg Kg 3 Γ4 Λ3 Φ1 Φ1 (fun _ => 12) Φ1 (1 / 5) 6 0 ω := by
  rw [nqLinExitTauN_eq_tau0]
  exact tau0_pos ω

/-- `H_0 = 0 ∈ GoodLinN` at the data (`zero_mem_goodSetN_inst` and `goodSetN_subset_goodLinN`; levels
`(Γ, Φ₁, Φ₂, Φ₃) = (4, 1, 12, 1)`). -/
theorem zero_mem_goodLinN_inst :
    (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) ∈
      GoodLinN sz0 0 (1 / 2) 0 3 4 1 12 1 := by
  have h := goodSetN_subset_goodLinN sz0 0 (1 / 2) 0 3 4 3 1 (1 / 5) 6 zero_mem_goodSetN_inst
  have e : ((3 : ℕ) : ℝ) * 4 * 1 ^ 2 = 12 := by norm_num
  rw [e] at h
  exact h

/-- **Instance of `goodSetN_subset_goodLinN`** at the data (`k = 3`, `Γ = 4`, `Φ = 1`): the merged good set
at the levels `(4, 3, 1)` lies in `GoodLinN` at `(4, 1, 12, 1)`. -/
example : sz0.GoodSetN 0 (1 / 2) 0 3 4 3 1 (1 / 5) 6 ⊆ GoodLinN sz0 0 (1 / 2) 0 3 4 1 (((3 : ℕ) : ℝ) * 4 * 1 ^ 2) 1 :=
  goodSetN_subset_goodLinN sz0 0 (1 / 2) 0 3 4 3 1 (1 / 5) 6

/-- **Instance of `measurableGoodLinN`** at the data. -/
example : MeasurableSet (GoodLinN sz0 0 (1 / 2) (1 / 32) 3 4 1 12 1) :=
  measurableGoodLinN sz0 0 (1 / 2) (1 / 32) 3 4 1 12 1

/-- **Instance of `dDriftNonAltN_eq_lin`** at the data. -/
example (u : ℝ) : dDriftNonAltN sz0 0 (1 / 2) u 3 4 1 = dDriftLinN sz0 0 (1 / 2) u 3 4 1 (((3 : ℕ) : ℝ) * 4 * 1 ^ 2) 1 :=
  dDriftNonAltN_eq_lin sz0 0 (1 / 2) u 3 4 1

/-- **Instance of `driftTensorN_norm_le_of_goodLin`**: `H_0 = 0 ∈ GoodLinN`, `k = 3`, `σ = (+,-,+)`, every label
vector `a`; the bound is the positive number `4² · (B_0^3/η_0) · ((3-2)·1 + 12 + 1)`. -/
theorem drift_lin_instance (a : Fin 3 → Zd 3 (sz0.L 0)) :
    ‖driftTensorN sz0 0 (1 / 2) 0 (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0))
        (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) sig3 a‖ ≤ dDriftLinN sz0 0 (1 / 2) 0 3 4 1 12 1 :=
  driftTensorN_norm_le_of_goodLin sz0 (by norm_num) zero_mem_goodLinN_inst sig3 a

/-- The linear drift level at the data is positive (so the bound above is not vacuous). -/
theorem dDriftLinN_inst_pos : 0 < dDriftLinN sz0 0 (1 / 2) 0 3 4 1 12 1 := by
  unfold dDriftLinN
  have hu1 : (0 : ℝ) < 1 := one_pos
  have hη := etaT_pos abs_half (show (0 : ℝ) < 1 from one_pos)
  have hB := Sizes.STBctl_pos sz0 0 (show (0 : ℝ) < 1 from one_pos)
  positivity

/-- **Instance of `nqLin_hdriftN`**: along the walk, strictly before the exit time of `GoodSetN ∩ GoodLinN`,
`‖Dr_j(b)‖ ≤ dDriftLinN` (`mem_of_lt_nqLinExitTauN` gives the membership). -/
theorem hdrift_lin_instance :
    ∀ ω j, j < Kg 0 →
      j < nqLinExitTauN sz0 Einst sInst vg Kg 3 Γ4 Λ3 Φ1 Φ1 (fun _ => 12) Φ1 (1 / 5) 6 0 ω →
      ∀ b : Fin 3 → Zd 3 (sz0.L 0),
      ‖driftTensorN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 j) (pathH sz0 sInst vg Kg 0 j ω) sig3 b‖ ≤
        dDriftLinN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 j) 3 (Γ4 0) (Φ1 0) ((fun _ => (12 : ℝ)) 0) (Φ1 0) :=
  nqLin_hdriftN sz0 (n := 0) (k := 3) (by norm_num) sig3 Einst sInst vg Kg Γ4 Φ1 (fun _ => 12) Φ1
    (nqLinExitTauN sz0 Einst sInst vg Kg 3 Γ4 Λ3 Φ1 Φ1 (fun _ => 12) Φ1 (1 / 5) 6 0)
    (fun ω j hj => (mem_of_lt_nqLinExitTauN hj).2)

/-- **Instance of `mem_of_lt_nqLinExitTauN`**: strictly before the exit, the grid state is in the intersection. -/
example (ω : PathΩ sz0) (j : ℕ)
    (h : j < nqLinExitTauN sz0 Einst sInst vg Kg 3 Γ4 Λ3 Φ1 Φ1 (fun _ => 12) Φ1 (1 / 5) 6 0 ω) :
    pathH sz0 sInst vg Kg 0 j ω ∈ sz0.GoodSetN 0 (Einst 0) (gridTime sInst vg Kg 0 j) 3 (Γ4 0) (Λ3 0) (Φ1 0)
        (1 / 5) 6 ∩
      GoodLinN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 j) 3 (Γ4 0) (Φ1 0) ((fun _ => (12 : ℝ)) 0) (Φ1 0) :=
  mem_of_lt_nqLinExitTauN h

/-- **Instance of `nqLinExitMeasN`**: `{j < nqLinExitTauN}` is `filt sz0 j`-measurable. -/
example (j : ℕ) :
    MeasurableSet[filt sz0 j] {ω | j < nqLinExitTauN sz0 Einst sInst vg Kg 3 Γ4 Λ3 Φ1 Φ1 (fun _ => 12) Φ1
      (1 / 5) 6 0 ω} :=
  nqLinExitMeasN sz0 Einst sInst vg Kg 0 3 Γ4 Λ3 Φ1 Φ1 (fun _ => 12) Φ1 (1 / 5) 6 j

/-- **Instance of `subGaussStop_linN`**: the `SubGaussStopN` input of `AssembledN` at the exit time of
`GoodSetN ∩ GoodLinN` and the proxy `cQVNonAltN`, for every `m ≤ 4`, `j < m` and every label vector `a`
(the hypotheses are those of `NQGood2Inst.subGaussStop_instance`). -/
theorem subGaussStop_lin_instance (m : ℕ) (hm : m ≤ Kg 0) (a : Fin 3 → Zd 3 (sz0.L 0)) (j : ℕ)
    (hj : j < m) :
    SubGaussStopN sz0 (Einst 0) sig3 (gridTime sInst vg Kg 0)
      (nqLinExitTauN sz0 Einst sInst vg Kg 3 Γ4 Λ3 Φ1 Φ1 (fun _ => 12) Φ1 (1 / 5) 6 0)
      (fun j ω => ZvecN sz0 Einst sInst vg Kg 0 j sig3 ω) m a j
      (cQVNonAltN sz0 Einst sInst vg Kg 0 3 10 (1 / 2) (4 / 5) Γ4 Λ3 5 m a j) :=
  subGaussStop_linN (d := 3) (k := 3) 10 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) sz0 (E := Einst) (s := sInst) (v := vg) (K := Kg) Einst_abs_lt sInst_nonneg
    sInst_le_vg vg_lt_one 0 hvL (by rw [W0]; norm_num [sInst, vg]) im_mE_half
    (by rw [lam0]; norm_num) (by rw [lam0]; norm_num) hW1 (by norm_num) (by norm_num) hWε hdW
    (by norm_num) hσ3 Γ4 Λ3 Φ1 Φ1 (fun _ => 12) Φ1 (by norm_num) (by norm_num) m hm a j hj
    (delta_shift_ok j (hj.trans_le hm))

/-! ### (3) `nqLinGood_holds` at the data: with high probability the grid walk is in `GoodLinN` at every `j ≤ 4`

`inst_ing` (the merged shape of the instances of `STIngR`) at `(sz0, z0, 0, 1/16)`, the grid end `v ≡ 1/32`
(`Δ = 1/128`, `u_j = j/128`), `K ≡ 4` (`K + 1 = 5 ≤ N^1`), `XL ≡ XLK ≡ 1`, `ε = 1/10`.  The hypotheses `STKbound`,
`STKward`, `STLK`, `STStep2Concl` and `STLmaxU`, `STLKU` are other gates' pins and stay hypotheses; `hX`, `hY` of
`NQLinConcl` (window `[0, 1/32]`) are *discharged* from the last two (`nqLin_prec_XiL_one`,
`nqLin_prec_XiLK_one` after the restriction from `[0, 1/16]`), and `0 ≤ s ≤ v ≤ t`, `K ≠ 0`, `K + 1 ≤ N^C`, the
controls `≥ 1` are proved at the data. -/

/-- **`nqLinGood_holds` at `sz0`** (`k ≥ 2`, `K ≡ 4`, `v ≡ 1/32`, `ε = 1/10`, `XL ≡ XLK ≡ 1`): with high probability the
grid walk stays in `GoodLinN` at every `j ≤ 4`, at the levels `Φ₁ = nqLinPhi1 1 k`, `Φ₂ = nqLinPhi2 1 1 B_v k 1`,
`Φ₃ = nqLinPhi3 1 k`. -/
theorem nqLinGood_instance (k : ℕ) (hk : 2 ≤ k) (hKb : STKbound sz0 (STflowE z0))
    (hKw : STKward sz0 (STflowE z0)) (hLK : STLK sz0 (STflowE z0) sInst)
    (hStep2 : STStep2Concl sz0 (STflowE z0) sInst tInst 1)
    (hL : STLmaxU sz0 (STflowE z0) sInst tInst) (hLKU : STLKU sz0 (STflowE z0) sInst tInst) :
    HighProbAt (pathP sz0) sz0.size (fun n => {ω | ∀ j ≤ Kg n,
      pathH sz0 sInst vg Kg n j ω ∈ GoodLinN sz0 n (STflowE z0 n) (gridTime sInst vg Kg n j) k
        (((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ)) (nqLinPhi1 (fun _ => 1) k)
        (nqLinPhi2 (fun _ => 1) (fun _ => 1) (sz0.Bctl n (vg n)) k 1) (nqLinPhi3 (fun _ => 1) k)}) := by
  obtain ⟨𝔠d, -, -, hG⟩ := inst_ing STAny (fun sz E s t => NQLinConcl sz E s t) (nqLinGood_holds 3)
    sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst sz0_ht trivial sz0_con 1 one_pos
  have hGG := hG hKb hKw hLK hStep2
  have hsv : ∀ n, sInst n ≤ vg n := sInst_le_vg
  have hvt : ∀ n, vg n ≤ tInst n := fun n => by simp only [tInst, vg]; norm_num
  have hLv := nqLin_LmaxU_restrict hvt hL
  have hLKv := nqLin_LKU_restrict hvt hLKU
  refine hGG vg hsv hvt Kg (fun n => by simp [Kg]) k hk (fun _ _ => 1) (fun _ _ => 1)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun m hm1 _ => nqLin_prec_XiL_one sz0 sz0_tendsto hsv vg_lt_one hLv hm1)
    (fun m hm1 _ => nqLin_prec_XiLK_one sz0 sz0_tendsto hsv vg_lt_one hLKv hm1) 1 ?_ (1 / 10)
    (by norm_num)
  filter_upwards [sz0_tendsto.eventually_ge_atTop (5 : ℝ)] with n hn
  rw [Real.rpow_one]
  simpa [Kg] using hn

/-- The good event of the instance is eventually nonempty: for large `n` some sample of the grid walk is in
`GoodLinN` at every grid time `j ≤ 4` (so the linear set is nonempty at each grid time). -/
theorem nqLinGood_instance_nonempty (k : ℕ) (hk : 2 ≤ k) (hKb : STKbound sz0 (STflowE z0))
    (hKw : STKward sz0 (STflowE z0)) (hLK : STLK sz0 (STflowE z0) sInst)
    (hStep2 : STStep2Concl sz0 (STflowE z0) sInst tInst 1)
    (hL : STLmaxU sz0 (STflowE z0) sInst tInst) (hLKU : STLKU sz0 (STflowE z0) sInst tInst) :
    ∀ᶠ n in atTop, ∃ ω : PathΩ sz0, ∀ j ≤ Kg n,
      pathH sz0 sInst vg Kg n j ω ∈ GoodLinN sz0 n (STflowE z0 n) (gridTime sInst vg Kg n j) k
        (((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ)) (nqLinPhi1 (fun _ => 1) k)
        (nqLinPhi2 (fun _ => 1) (fun _ => 1) (sz0.Bctl n (vg n)) k 1) (nqLinPhi3 (fun _ => 1) k) :=
  (nqLinGood_instance k hk hKb hKw hLK hStep2 hL hLKU).nonempty (tendsto_size sz0 sz0_tendsto)
    (measure_univ) |>.mono fun n hn => hn

/-- The instance at the minimal loop length `k = 2` (no `l ∈ [3,k]`, empty sum over `n'`) and at `k = 4`
(`l ∈ {3,4}`, `n' = 3`): the clauses (D1'), (D2') are not vacuous at `k = 4`; the levels at `XL ≡ XLK ≡ 1`:
`Φ₁ = k - 2`, `Φ₃ = 1` (and `Φ₂ = B_v^{1/6} + (k = 4 ? 1 : 0)`). -/
example : Finset.Icc 3 2 = ∅ ∧ Finset.Icc ((2 + 1) / 2 + 1) (2 - 1) = ∅ ∧ Finset.Icc 3 4 = {3, 4} ∧
    Finset.Icc ((4 + 1) / 2 + 1) (4 - 1) = {3} := by decide

example : nqLinPhi1 (fun _ => 1) 2 = 0 ∧ nqLinPhi1 (fun _ => 1) 4 = 2 ∧ nqLinPhi3 (fun _ => 1) 4 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [nqLinPhi1]
  · norm_num [nqLinPhi1, show Finset.Icc 2 (4 - 1) = {2, 3} by decide]
  · simp [nqLinPhi3]

example (B : ℝ) : nqLinPhi2 (fun _ => 1) (fun _ => 1) B 2 1 = B ^ (1 / 6 : ℝ) := by
  simp [nqLinPhi2]

example (B : ℝ) : nqLinPhi2 (fun _ => 1) (fun _ => 1) B 4 1 = 1 + B ^ (1 / 6 : ℝ) := by
  simp [nqLinPhi2]

example (hKb : STKbound sz0 (STflowE z0)) (hKw : STKward sz0 (STflowE z0))
    (hLK : STLK sz0 (STflowE z0) sInst) (hStep2 : STStep2Concl sz0 (STflowE z0) sInst tInst 1)
    (hL : STLmaxU sz0 (STflowE z0) sInst tInst) (hLKU : STLKU sz0 (STflowE z0) sInst tInst) :=
  nqLinGood_instance 2 le_rfl hKb hKw hLK hStep2 hL hLKU

example (hKb : STKbound sz0 (STflowE z0)) (hKw : STKward sz0 (STflowE z0))
    (hLK : STLK sz0 (STflowE z0) sInst) (hStep2 : STStep2Concl sz0 (STflowE z0) sInst tInst 1)
    (hL : STLmaxU sz0 (STflowE z0) sInst tInst) (hLKU : STLKU sz0 (STflowE z0) sInst tInst) :=
  nqLinGood_instance 4 (by norm_num) hKb hKw hLK hStep2 hL hLKU

/-! ### (4) `budgetNonAltLinN` at the data of `NQBudgetInst.budgetNonAltN_instance`

`d = 3`, `sz0`, `n = 0`: `Γ = N^{2/21} = 4`, `Λ = 3`, `Φ₁ = Φ₃ = 1`, `Φ₂ = 12` (`= kΓΦ²`), `D' = 6`, `D'' = 5`, `D_Y = 1`,
`D_t = -5`, `τ_K = 1/21`, `ε_q = 1`, `ε₀ = C + 12`, `X0 = 4 B_0^3`, label `aFar`.  `hlog`, `hR` are the merged
`NQBudgetInst.hlog_instance`, `hR_instance`; `ha1`, `ha3`, `he1`-`he4` are re-derived (the originals are private to
`NQBudget`), `ha2` is the new inequality with `(N^{ε₁})² = 16`. -/

private theorem eta_inv_le {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 32) : (etaT (1 / 2) t)⁻¹ ≤ 11 / 10 := by
  have hpos : 0 < etaT (1 / 2) t := etaT_pos abs_half (by linarith)
  rw [inv_eq_one_div, div_le_iff₀ hpos]
  have h1 : (31 / 32 : ℝ) ≤ 1 - t := by linarith
  have h2 := im_ge
  have h3 : (31 / 32 : ℝ) * (24 / 25) ≤ (1 - t) * (mE (1 / 2)).im :=
    mul_le_mul h1 h2 (by norm_num) (by linarith)
  unfold etaT
  linarith

private theorem eta_inv_le_N : (etaT (Einst 0) (vg 0))⁻¹ ≤ ((sz0.size 0 : ℕ) : ℝ) := by
  rw [N0]
  have h := eta_inv_le (t := vg 0) (by norm_num [vg]) (by norm_num [vg])
  have e : Einst 0 = 1 / 2 := rfl
  rw [e]
  linarith

private theorem eta_inv_le_v : (etaT (Einst 0) (vg 0))⁻¹ ≤ 11 / 10 :=
  eta_inv_le (t := vg 0) (by norm_num [vg]) (by norm_num [vg])

private theorem step0 : gridStep sInst vg Kg 0 = 1 / 128 := grid_data.1

private theorem two_pow_rpow (m : ℕ) (y : ℝ) : ((2 : ℝ) ^ m) ^ y = (2 : ℝ) ^ ((m : ℝ) * y) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]

private theorem two_rpow_nat_mul (C : ℝ) (m : ℕ) : (2 : ℝ) ^ ((m : ℝ) * C) = ((2 : ℝ) ^ C) ^ m := by
  rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_natCast]

private theorem W_rpow (y : ℝ) : ((sz0.W 0 : ℕ) : ℝ) ^ y = (2 : ℝ) ^ ((5 : ℝ) * y) := by
  have h := two_pow_rpow 5 y
  rw [W0, show (32 : ℝ) = 2 ^ 5 by norm_num, h]; norm_num

private theorem N_rpow (y : ℝ) : ((sz0.size 0 : ℕ) : ℝ) ^ y = (2 : ℝ) ^ ((21 : ℝ) * y) := by
  have h := two_pow_rpow 21 y
  rw [N0, show (2097152 : ℝ) = 2 ^ 21 by norm_num, h]; norm_num

private theorem W_eps (C : ℝ) : ((sz0.W 0 : ℕ) : ℝ) ^ (C * (4 / 5)) = ((2 : ℝ) ^ C) ^ 4 := by
  rw [W_rpow, show (5 : ℝ) * (C * (4 / 5)) = ((4 : ℕ) : ℝ) * C by push_cast; ring, two_rpow_nat_mul]

private theorem W_C (C : ℝ) : ((sz0.W 0 : ℕ) : ℝ) ^ C = ((2 : ℝ) ^ C) ^ 5 := by
  rw [W_rpow, show (5 : ℝ) * C = ((5 : ℕ) : ℝ) * C by push_cast; ring, two_rpow_nat_mul]

private theorem N_eps0 (C : ℝ) :
    ((sz0.size 0 : ℕ) : ℝ) ^ (C + 12) = ((2 : ℝ) ^ C) ^ 21 * 2 ^ 252 := by
  rw [N_rpow, show (21 : ℝ) * (C + 12) = ((21 : ℕ) : ℝ) * C + ((252 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_add (by norm_num), two_rpow_nat_mul, Real.rpow_natCast]

private theorem N_eps1 : ((sz0.size 0 : ℕ) : ℝ) ^ ((2 : ℝ) / 21) = 4 := by
  rw [N_rpow, show (21 : ℝ) * (2 / 21) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num

private theorem N_one : ((sz0.size 0 : ℕ) : ℝ) ^ (1 : ℝ) = 2097152 := by
  rw [Real.rpow_one, N0]

private theorem N_negone : ((sz0.size 0 : ℕ) : ℝ) ^ (-(1 : ℝ)) = 2097152⁻¹ := by
  rw [Real.rpow_neg_one, N0]

private theorem N_five : ((sz0.size 0 : ℕ) : ℝ) ^ (-(-5 : ℝ)) = 2097152 ^ 5 := by
  rw [neg_neg, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, N0]

private theorem W_neg (m : ℕ) : ((sz0.W 0 : ℕ) : ℝ) ^ (-(m : ℝ)) = ((32 : ℝ) ^ m)⁻¹ := by
  rw [Real.rpow_neg (by rw [W0]; norm_num), Real.rpow_natCast, W0]

private theorem log_N : Real.log ((sz0.size 0 : ℕ) : ℝ) = 21 * Real.log 2 := by
  rw [N0, show (2097152 : ℝ) = 2 ^ 21 by norm_num, Real.log_pow]; norm_num

private theorem Ls_bounds :
    14 ≤ (mE (Einst 0)).im⁻¹ * Real.log ((sz0.size 0 : ℕ) : ℝ) ∧
      (mE (Einst 0)).im⁻¹ * Real.log ((sz0.size 0 : ℕ) : ℝ) ≤ 16 := by
  have e : Einst 0 = 1 / 2 := rfl
  rw [e, log_N]
  have hpos : 0 < (mE (1 / 2)).im := mE_im_pos abs_half
  have h1 : 1 ≤ (mE (1 / 2)).im⁻¹ := (one_le_inv₀ hpos).2 (nqBudget_im_le_one _)
  have h2 : (mE (1 / 2)).im⁻¹ ≤ 25 / 24 := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]; linarith [im_ge]
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  constructor
  · nlinarith
  · nlinarith

private theorem le_P0 {x : ℝ} (hx : 1 ≤ x) {m : ℕ} (hm : m ≤ 21) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c ≤ 2 ^ 252 / 12) : x ^ m * c ≤ x ^ 21 * 2 ^ 252 / 12 := by
  have h1 : x ^ m ≤ x ^ 21 := pow_le_pow_right₀ hx hm
  have h0 : 0 ≤ x ^ 21 := by positivity
  calc x ^ m * c ≤ x ^ 21 * c := mul_le_mul_of_nonneg_right h1 hc0
    _ ≤ x ^ 21 * (2 ^ 252 / 12) := mul_le_mul_of_nonneg_left hc h0
    _ = _ := by ring

private theorem ha1_inst (C : ℝ) (hC : 0 < C) :
    ((sz0.W 0 : ℕ) : ℝ) ^ (C * (4 / 5)) * ((sz0.size 0 : ℕ) : ℝ) ^ ((2 : ℝ) / 21) ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (C + 12) / 6 := by
  have hx : 1 ≤ (2 : ℝ) ^ C := Real.one_le_rpow (by norm_num) hC.le
  rw [W_eps, N_eps1, N_eps0]
  have h := le_P0 hx (m := 4) (c := 4) (by norm_num) (by norm_num) (by norm_num)
  have h21 : 0 ≤ ((2 : ℝ) ^ C) ^ 21 * 2 ^ 252 := by positivity
  linarith

/-- **`ha2` of `budgetNonAltLinN` at the data** (the new inequality, `(N^{ε₁})² = 16` in place of `(N^{ε₁})³ = 64`):
`3 W^{Cε} 16 Ls ≤ N^{ε₀}/12` for every `C > 0`. -/
private theorem ha2_inst (C : ℝ) (hC : 0 < C) :
    ((3 : ℕ) : ℝ) * ((sz0.W 0 : ℕ) : ℝ) ^ (C * (4 / 5)) *
        (((sz0.size 0 : ℕ) : ℝ) ^ ((2 : ℝ) / 21)) ^ 2 *
        ((mE (Einst 0)).im⁻¹ * Real.log ((sz0.size 0 : ℕ) : ℝ)) ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (C + 12) / 12 := by
  have hx : 1 ≤ (2 : ℝ) ^ C := Real.one_le_rpow (by norm_num) hC.le
  have hLs := Ls_bounds
  rw [W_eps, N_eps1, N_eps0]
  have hx0 : 0 ≤ ((2 : ℝ) ^ C) ^ 4 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hLs.2 (by positivity : (0 : ℝ) ≤ 3 * ((2 : ℝ) ^ C) ^ 4 * 4 ^ 2)
  have h := le_P0 hx (m := 4) (c := 768) (by norm_num) (by norm_num) (by norm_num)
  push_cast
  nlinarith

private theorem ha3_inst (C : ℝ) (hC : 0 < C) :
    ((sz0.size 0 : ℕ) : ℝ) ^ (1 : ℝ) * (((sz0.W 0 : ℕ) : ℝ) ^ (C * (4 / 5)) *
        ((sz0.size 0 : ℕ) : ℝ) ^ ((2 : ℝ) / 21) *
        Real.sqrt (((3 : ℕ) : ℝ) * ((mE (Einst 0)).im⁻¹ * Real.log ((sz0.size 0 : ℕ) : ℝ) + 1))) ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (C + 12) / 12 := by
  have hx : 1 ≤ (2 : ℝ) ^ C := Real.one_le_rpow (by norm_num) hC.le
  have hLs := Ls_bounds
  have hs : Real.sqrt (((3 : ℕ) : ℝ) * ((mE (Einst 0)).im⁻¹ * Real.log ((sz0.size 0 : ℕ) : ℝ) + 1)) ≤ 8 :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by push_cast; nlinarith [hLs.2]⟩
  rw [W_eps, N_eps1, N_eps0, N_one]
  have hx0 : 0 ≤ ((2 : ℝ) ^ C) ^ 4 := by positivity
  have h1 : ((2 : ℝ) ^ C) ^ 4 * 4 * Real.sqrt (((3 : ℕ) : ℝ) *
      ((mE (Einst 0)).im⁻¹ * Real.log ((sz0.size 0 : ℕ) : ℝ) + 1)) ≤ ((2 : ℝ) ^ C) ^ 4 * 4 * 8 :=
    mul_le_mul_of_nonneg_left hs (by positivity)
  have h := le_P0 hx (m := 4) (c := 2 ^ 26) (by norm_num) (by norm_num) (by norm_num)
  nlinarith

private theorem W_neg6 : ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ)) = ((32 : ℝ) ^ 6)⁻¹ := by
  rw [show (-(6 : ℝ)) = -((6 : ℕ) : ℝ) by norm_num, W_neg]

private theorem W_neg5 : ((sz0.W 0 : ℕ) : ℝ) ^ (-(5 : ℝ)) = ((32 : ℝ) ^ 5)⁻¹ := by
  rw [show (-(5 : ℝ)) = -((5 : ℕ) : ℝ) by norm_num, W_neg]

private theorem he1_inst (C : ℝ) (hC : 0 < C) :
    ((sz0.size 0 : ℕ) : ℝ) ^ 3 * (((sz0.W 0 : ℕ) : ℝ) ^ C * ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ))) ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (C + 12) / 12 := by
  have hx : 1 ≤ (2 : ℝ) ^ C := Real.one_le_rpow (by norm_num) hC.le
  rw [W_C, W_neg6, N_eps0, N0]
  have h := le_P0 hx (m := 5) (c := 8589934592) (by norm_num) (by norm_num) (by norm_num)
  have e : (2097152 : ℝ) ^ 3 * (((2 : ℝ) ^ C) ^ 5 * ((32 : ℝ) ^ 6)⁻¹) =
      ((2 : ℝ) ^ C) ^ 5 * 8589934592 := by ring
  rw [e]
  exact h

private theorem he3_inst (C : ℝ) (hC : 0 < C) :
    ((sz0.size 0 : ℕ) : ℝ) ^ 3 * ((sz0.size 0 : ℕ) : ℝ) ^ (-(1 : ℝ)) ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (C + 12) / 6 := by
  have hx : 1 ≤ (2 : ℝ) ^ C := Real.one_le_rpow (by norm_num) hC.le
  rw [N_eps0, N_negone, N0]
  have h := le_P0 hx (m := 0) (c := 4398046511104) (by norm_num) (by norm_num) (by norm_num)
  have h21 : 0 ≤ ((2 : ℝ) ^ C) ^ 21 * 2 ^ 252 := by positivity
  have e : (2097152 : ℝ) ^ 3 * (2097152 : ℝ)⁻¹ = 4398046511104 := by norm_num
  rw [e]
  simp only [pow_zero, one_mul] at h
  linarith

private theorem he4_inst (C : ℝ) (hC : 0 < C) :
    ((sz0.size 0 : ℕ) : ℝ) ^ 3 * ((sz0.size 0 : ℕ) : ℝ) ^ (-(-5 : ℝ)) ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (C + 12) / 6 := by
  have hx : 1 ≤ (2 : ℝ) ^ C := Real.one_le_rpow (by norm_num) hC.le
  rw [N_eps0, N_five, N0]
  have h1 : 1 ≤ ((2 : ℝ) ^ C) ^ 21 := one_le_pow₀ hx
  nlinarith

private theorem he2_inst (hC : 0 < nqGood1C 3 3 10 (1 / 2)) :
    ((sz0.size 0 : ℕ) : ℝ) ^ (1 : ℝ) * (((sz0.size 0 : ℕ) : ℝ) ^ 3 *
        Real.sqrt (((3 : ℕ) : ℝ) * (nqBudget_qvFar sz0 0 3 10 (1 / 2) (4 / 5) *
          ((sz0.W 0 : ℕ) : ℝ) ^ (-(5 : ℝ))))) ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (nqGood1C 3 3 10 (1 / 2) + 12) / 12 := by
  unfold nqBudget_qvFar nqBudget_kapFar
  generalize nqGood1C 3 3 10 (1 / 2) = C at hC ⊢
  have hx : 1 ≤ (2 : ℝ) ^ C := Real.one_le_rpow (by norm_num) hC.le
  rw [W_eps, W_C, W_neg5, N_eps0, lam0, N_one]
  generalize (2 : ℝ) ^ C = x at hx ⊢
  have hx0 : 0 ≤ x := by linarith
  simp only [Nat.cast_ofNat]
  rw [W0, N0]
  have h8 : x ^ 8 ≤ x ^ 10 := pow_le_pow_right₀ hx (by norm_num)
  have h9 : x ^ 9 ≤ x ^ 10 := pow_le_pow_right₀ hx (by norm_num)
  have h5 : x ^ 5 ≤ x ^ 10 := pow_le_pow_right₀ hx (by norm_num)
  have hq : 3 * ((x ^ 4 * ((1 + (1 / 64 : ℝ) ^ 2) * 2097152) ^ (3 - 1) *
        (x ^ 4 * ((1 + (1 / 64 : ℝ) ^ 2) * 2097152) ^ (3 - 1) + x ^ 5) + x ^ 5 * 32 ^ 3) *
        ((32 : ℝ) ^ 5)⁻¹) ≤ (x ^ 5 * 2 ^ 31) ^ 2 := by
    norm_num
    nlinarith [h8, h9, h5]
  have hs := Real.sqrt_le_iff.2 ⟨by positivity, hq⟩
  have h1 := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 2097152 ^ 3)
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2097152)
  have e : (2097152 : ℝ) * (2097152 ^ 3 * (x ^ 5 * 2 ^ 31)) = x ^ 5 * 2 ^ 115 := by ring
  rw [e] at h2
  have h := le_P0 hx (m := 5) (c := 2 ^ 115) (by norm_num) (by positivity) (by norm_num)
  linarith

/-- **`tbDriftLinN` at the data** (levels `(Γ, Φ₁, Φ₂, Φ₃) = (4, 1, 12, 1)`, `D' = 6`): the drift term of
`assembledRHSLinN` is at most `W^{Cε} Γ²((k-2)Φ₁ + Φ₂ + Φ₃) B_v^k Σ_j Δ/η_{u_j} + (KΔ)(W^C W^{-D'})`. -/
example :
    gridStep sInst vg Kg 0 * ∑ j ∈ Finset.range (Kg 0),
      (kappaNonAltN 3 3 10 (1 / 2) (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (4 / 5)
          (gridTime sInst vg Kg 0) (j + 1) (Kg 0) *
          dDriftLinN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 j) 3 (Γ4 0) (Φ1 0)
            ((fun _ : ℕ => (12 : ℝ)) 0) (Φ1 0) +
        epsNonAltN 3 3 10 (1 / 2) ((sz0.W 0 : ℕ) : ℝ) (j + 1) (Kg 0) *
          ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ))) ≤
      ((sz0.W 0 : ℕ) : ℝ) ^ (nqGood1C 3 3 10 (1 / 2) * (4 / 5)) *
          (Γ4 0 * Γ4 0 * ((((3 : ℕ) : ℝ) - 2) * Φ1 0 + (fun _ : ℕ => (12 : ℝ)) 0 + Φ1 0)) *
          (sz0.Bctl 0 (vg 0)) ^ 3 *
          ∑ j ∈ Finset.range (Kg 0), gridStep sInst vg Kg 0 /
            etaT (Einst 0) (gridTime sInst vg Kg 0 j) +
        ((Kg 0 : ℕ) * gridStep sInst vg Kg 0) *
          (((sz0.W 0 : ℕ) : ℝ) ^ nqGood1C 3 3 10 (1 / 2) * ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ))) :=
  tbDriftLinN sz0 (E := Einst) (s := sInst) (v := vg) (K := Kg) 0 3 10 (1 / 2) (4 / 5) Γ4 Φ1
    (fun _ => 12) Φ1 6 (Einst_abs_lt 0) (by norm_num [sInst]) (by norm_num [sInst, vg])
    (by norm_num [vg]) (by norm_num [Kg]) (by norm_num) (by norm_num [Γ4]) (by norm_num [Φ1])
    (by norm_num) (by norm_num [Φ1]) eta_inv_le_N

/-- **`budgetNonAltLinN` at the data of `budgetNonAltN_instance`** (`d = 3`, `sz0`, `n = 0`: `L = 4`, `W = 32`,
`N = 2^21`; `E = 1/2`, grid `(sInst, vg, Kg)`: `Δ = 1/128`; `k = 3`, `Λ_g = 10`, `κ' = 1/2`, `ε = 4/5`; levels
`(Γ, Λ, Φ₁, Φ₂, Φ₃) = (4, 3, 1, 12, 1)` with `Γ = N^{2/21}`; `D' = 6`, `D'' = 5`, `D_Y = 1`, `D_t = -5`,
`τ_K = 1/21`, `ε_q = 1`, `ε₀ = C + 12` with the abstract `C = nqGood1C 3 3 10 (1/2) > 0`; `X0 = 4 B_0^3`; label
`aFar`): every hypothesis is discharged (`hlog`, `hR` from `NQBudgetInst`, `ha1`-`he4` for every `C > 0`); nothing is
left open.  The right side is `N^{ε₀}(Λ^{1/2} + Φ₁ + Φ₂ + Φ₃) B_v^3` with `Φ₂ = 12`: no `Φ²`. -/
theorem budgetNonAltLinN_instance :
    assembledRHSLinN sz0 Einst sInst vg Kg 0 3 10 (1 / 2) (4 / 5) Γ4 Λ3 Φ1 (fun _ => 12) Φ1 6 5 1
        (1 / 21) 1 (4 * (sz0.Bctl 0 (sInst 0)) ^ 3) aFar ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (nqGood1C 3 3 10 (1 / 2) + 12) *
        (Λ3 0 ^ ((1 : ℝ) / 2) + Φ1 0 + (fun _ : ℕ => (12 : ℝ)) 0 + Φ1 0) * (sz0.Bctl 0 (vg 0)) ^ 3 :=
  budgetNonAltLinN sz0 Einst sInst vg Kg 0 3 10 (1 / 2) (4 / 5) Γ4 Λ3 Φ1 (fun _ => 12) Φ1 6 5 1 (-5)
    (1 / 21) 1 (nqGood1C 3 3 10 (1 / 2) + 12) (2 / 21) (4 * (sz0.Bctl 0 (sInst 0)) ^ 3) aFar
    (by norm_num) (by norm_num) (Einst_abs_lt 0) (by norm_num [sInst]) (by norm_num [sInst, vg])
    (by norm_num [vg]) (by norm_num [Kg]) eta_inv_le_N (by rw [step0]; linarith [eta_inv_le_v])
    (by rw [N_eps1]) (by norm_num [Λ3]) (by norm_num [Φ1]) (by norm_num) (by norm_num [Φ1])
    NQBudgetInst.hlog_instance (by rw [N_eps1]) NQBudgetInst.hR_instance
    (ha1_inst _ nqGood1C_pos_instance) (ha2_inst _ nqGood1C_pos_instance)
    (ha3_inst _ nqGood1C_pos_instance) (he1_inst _ nqGood1C_pos_instance)
    (he2_inst nqGood1C_pos_instance) (he3_inst _ nqGood1C_pos_instance)
    (he4_inst _ nqGood1C_pos_instance)

end NQLinInst

end RBM.Ind

end

#print axioms RBM.Gauss.Sizes.GoodLinN
#print axioms RBM.Gauss.Sizes.nqLinPhi1
#print axioms RBM.Gauss.Sizes.nqLinPhi2
#print axioms RBM.Gauss.Sizes.nqLinPhi3
#print axioms RBM.Gauss.Sizes.NQLinConcl
#print axioms RBM.Gauss.Sizes.NQLinGood
#print axioms RBM.Gauss.Sizes.measurableGoodLinN
#print axioms RBM.Gauss.Sizes.goodSetN_subset_goodLinN
#print axioms RBM.Gauss.Sizes.nqLinGood_holds
#print axioms RBM.Ind.dDriftLinN
#print axioms RBM.Ind.nqLinExitTauN
#print axioms RBM.Ind.dDriftNonAltN_eq_lin
#print axioms RBM.Ind.driftTensorN_norm_le_of_goodLin
#print axioms RBM.Ind.nqLin_hdriftN
#print axioms RBM.Ind.mem_of_lt_nqLinExitTauN
#print axioms RBM.Ind.nqLinExitMeasN
#print axioms RBM.Ind.subGaussStop_linN
#print axioms RBM.Ind.assembledRHSLinN
#print axioms RBM.Ind.tbDriftLinN
#print axioms RBM.Ind.budgetNonAltLinN
#print axioms RBM.Ind.NQLinInst.nqLinExitTauN_eq_tau0
#print axioms RBM.Ind.NQLinInst.nqLinExitTauN_pos
#print axioms RBM.Ind.NQLinInst.zero_mem_goodLinN_inst
#print axioms RBM.Ind.NQLinInst.drift_lin_instance
#print axioms RBM.Ind.NQLinInst.dDriftLinN_inst_pos
#print axioms RBM.Ind.NQLinInst.hdrift_lin_instance
#print axioms RBM.Ind.NQLinInst.subGaussStop_lin_instance
#print axioms RBM.Ind.NQLinInst.nqLinGood_instance
#print axioms RBM.Ind.NQLinInst.nqLinGood_instance_nonempty
#print axioms RBM.Ind.NQLinInst.budgetNonAltLinN_instance
