/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.NQBudgetGen
import RBM3D.Induction.NQLin

/-!
# The linear good set of the non-alternating endpoint over the carrier

Generic forms of `Induction/NQLin` over a carrier `Cm : Step2Mat sz`, namespace `RBM.BA`, no `BA/*` import.
Paper: Lemma 4.3 (`lem:SEforLn`), Lemma 4.6 (`lem:STOeq_NQ`), (4.22) `am;asoiuw` and the proof of Lemma 4.6.
`etaT E u` is `Cm.eta n u`, `STksimLKM`, `STelklkM`, `STegtM` are `STksimLKMg`, `STelklkMg`, `STegtMg`;
`StepDecompGen_LoopForm` replaces `|E n| < 2`.

* **Vocabulary** `GoodLinNg`, `NQLinConclg`, `NQLinGoodgL`, the levels `nqLinPhi1`-`3` (model-free, band names),
  `measurableGoodLinNg`.
* **The statements** `nqLinConclg_of` (one carrier: `STSEforLnConclgL` on `[s, t]`, restricted to `[s, v]`, the law
  `Step2EventsGen_Law`, `StepDecompGen_LoopForm`) and `nqLinGoodgL_of` (family form).
* **The linear drift and the budget** `dDriftLinNg`, `nqLinExitTauNg`, `driftTensorNg_norm_le_of_goodLin`,
  `nqLin_hdriftNg`, `mem_of_lt_nqLinExitTauNg`, `nqLinExitMeasNg`, `subGaussStop_linNg`,
  `assembledRHSLinNg`, `tbDriftLinNg`, `budgetNonAltLinNg`.

The private measurability helpers and the one-lower-bound lemmas of `GridGoodGen` are reused by `open private`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open private GridGoodGen_precL_whp GridGoodGen_one_le_STXiLg GridGoodGen_one_le_STXiLKg GridGoodGen_meas_STksimLKMg
  GridGoodGen_meas_STelklkMg GridGoodGen_meas_STegtMg from RBM3D.Chain.GridGoodGen

open private gridGood_whp_forall_mem gridGood_whp_and gridGood_gridTime_mem gridGood_measurableSet_forall gridGood_measurableSet_imp
  from RBM3D.Induction.GridGoodN

open private nqLin_rpow_third nqLin_sqrt_bound nqLin_clause nqLin_D2_arith nqLin_absorb nqLin_gridTime_nonneg nqLin_gridTime_le
  nqLin_K_mul_step nqLin_final from RBM3D.Induction.NQLin

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes
open RBM.Ind (nqBudget_sum_succ_le nqBudget_sqrt_add_le nqGood1C)

/-! ## 1. The vocabulary -/

section GoodLin

variable {d : ℕ} {sz : Sizes d}

/-- **`GoodLinNg`** (band `GoodLinN`): the linear set over a carrier, the three clauses
for `STksimLKg`, `STelklkg`, `STegtg` of `GoodSetNg` at separate deterministic levels; `etaT E u` is `Cm.eta n u`, `sz.Bctl` stays (size level). -/
def GoodLinNg (Cm : Step2Mat sz) (n : ℕ) (u : ℝ) (k : ℕ) (Γ Φ₁ Φ₂ Φ₃ : ℝ) :
    Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
  {H | (∀ l : ℕ, 3 ≤ l → l ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖STksimLKMg Cm n u H l (loopOf σ a)‖ ≤ Γ * (Γ * Φ₁) * ((sz.Bctl n u) ^ k / Cm.eta n u)) ∧
    (∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖STelklkMg Cm n u H (loopOf σ a)‖ ≤ Γ * (Γ * Φ₂) * ((sz.Bctl n u) ^ k / Cm.eta n u)) ∧
    (∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖STegtMg Cm n u H (loopOf σ a)‖ ≤ Γ * (Γ * Φ₃) * ((sz.Bctl n u) ^ k / Cm.eta n u))}

/-- **`NQLinConclg`** (band `NQLinConcl`): `Prec sz` is `PrecL sz μ`, `STXiL`/`STXiLK` are
`STXiLg`/`STXiLKg`, `pathP`/`pathH` are `Cm.Pp`/`Cm.Hpath`, `GoodLinN` is `GoodLinNg`; the levels are the band's model-free
`nqLinPhi1`-`3` (reused under their names). -/
def NQLinConclg (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ v : ℕ → ℝ, (∀ n, s n ≤ v n) → (∀ n, v n ≤ t n) → ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) →
    ∀ k : ℕ, 2 ≤ k → ∀ XL XLK : ℕ → ℕ → ℝ, (∀ m n, 1 ≤ XL m n) → (∀ m n, 1 ≤ XLK m n) →
    (∀ m : ℕ, 1 ≤ m → m ≤ k + 1 →
      PrecL sz μ (U := fun n => TimeIcc s v n)
        (fun n u ω => STXiLg Cm.toFlowFM n (u : ℝ) m ω) (fun n _ _ => XL m n)) →
    (∀ m : ℕ, 1 ≤ m → m ≤ k →
      PrecL sz μ (U := fun n => TimeIcc s v n)
        (fun n u ω => STXiLKg Cm.toFlowFM n (u : ℝ) m ω) (fun n _ _ => XLK m n)) →
    ∀ C : ℝ, (∀ᶠ n in atTop, ((K n + 1 : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C) →
    ∀ ε : ℝ, 0 < ε →
      HighProbAt Cm.Pp sz.size (fun n => {ω | ∀ j ≤ K n,
        Cm.Hpath s v K n j ω ∈ GoodLinNg Cm n (gridTime s v K n j) k
          (((sz.size n : ℕ) : ℝ) ^ ε) (nqLinPhi1 (fun m => XLK m n) k)
          (nqLinPhi2 (fun m => XL m n) (fun m => XLK m n) (sz.Bctl n (v n)) k (XLK k n))
          (nqLinPhi3 (fun m => XL m n) k)})

end GoodLin

/-- **The statement `NQLinGoodgL`** (band `NQLinGood`): `STIngRgL d STAny` over a carrier family
with the conclusion `NQLinConclg` (the shape of `GridGoodNgL`, `Chain/GridGoodGen`). -/
def NQLinGoodgL (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngRgL d STAny law Flow (fun sz z => (mkM sz z).toFlowFM) T0
    (fun sz z s t => NQLinConclg (mkM sz z) (law sz) s t)

/-! ## 2. Measurability of `GoodLinNg` -/

section MeasurableProof

variable {d : ℕ} {sz : Sizes d} {Cm : Step2Mat sz}

/-- **`measurableGoodLinNg`** (band `measurableGoodLinN`): `GoodLinNg` is a measurable set of matrices under
`StepDecompGen_LoopForm` (a finite conjunction, over finitely many labels, of inequalities between measurable functions of `H`; the measurability
of `Cm.LIM` in the matrix is `GridGoodGen_meas_of_loopForm`). -/
theorem measurableGoodLinNg {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E) (n : ℕ) (u : ℝ) (k : ℕ) (Γ Φ₁ Φ₂ Φ₃ : ℝ) :
    MeasurableSet (GoodLinNg Cm n u k Γ Φ₁ Φ₂ Φ₃) := by
  obtain ⟨-, hLIM⟩ := GridGoodGen_meas_of_loopForm hL n u
  unfold GoodLinNg
  simp only [Set.ofPred_and]
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
  · exact gridGood_measurableSet_forall fun l => gridGood_measurableSet_imp fun _ =>
      gridGood_measurableSet_imp fun _ => gridGood_measurableSet_forall fun σ =>
        gridGood_measurableSet_forall fun a =>
          measurableSet_le (GridGoodGen_meas_STksimLKMg hLIM l (loopOf σ a)).norm measurable_const
  · exact gridGood_measurableSet_forall fun σ => gridGood_measurableSet_forall fun a =>
      measurableSet_le (GridGoodGen_meas_STelklkMg hLIM (loopOf σ a)).norm measurable_const
  · exact gridGood_measurableSet_forall fun σ => gridGood_measurableSet_forall fun a =>
      measurableSet_le (GridGoodGen_meas_STegtMg hLIM (loopOf σ a)).norm measurable_const

end MeasurableProof

/-! ## 3. The statement `NQLinGood` over a carrier

The proofs below are the ports of `nqLin_whp_uniform` and `nqLin_grid` to a carrier `Cm`, a flow matrix `Hf`
and a law `μ`.  `GoodLinNg` has no Hermitian clause and no decay clause, so neither `Step34Gen_LCompat` nor `StepDecompGen_WalkForm`
is read: the three clauses are `STksimLKg`, `STelklkg`, `STegtg` at `Hf n u ω` by definition, and `StepDecompGen_LoopForm` is read only for
`η > 0` and for the measurability of `GoodLinNg`. -/

section Uniform

variable {d : ℕ} {sz : Sizes d}

/-- `STSEforLnConclgL` on the window `[s,t]` gives it on `[s,v]`, `v ≤ t` (restriction of the parameter set; band `nqLin_SE_restrict`). -/
private theorem NQLinGen_SE_restrict {Cm : Step2Mat sz}
    {Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n)  (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {μ : Measure sz.SeqΩ}
    {s t v : ℕ → ℝ} (hvt : ∀ n, v n ≤ t n) (h : STSEforLnConclgL Cm Hf μ s t) : STSEforLnConclgL Cm Hf μ s v := by
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

/-- **The uniform good event** (band `nqLin_whp_uniform`): from the hypotheses of `NQLinConclg` and the three conjuncts of `lem:SEforLn` on
`[s,v]`, with high probability `Hf n u ω ∈ GoodLinNg … u` for every `u ∈ [s_n,v_n]` at once, at the levels `Φ₁ = nqLinPhi1`,
`Φ₂ = nqLinPhi2` (with `B = B_{v_n}`, `Φ_cur = XLK k n`), `Φ₃ = nqLinPhi3` and the loss `N^ε` (the `ε/3` split: every `≺` is used at the exponent
`ε/3`). -/
private theorem NQLinGen_whp_uniform {Cm : Step2Mat sz} {E : ℕ → ℝ} {μ : Measure sz.SeqΩ}
    {Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hL : StepDecompGen_LoopForm Cm E) (hsz : sz.SizeTendsto) {s v : ℕ → ℝ} (hv1 : ∀ n, v n < 1)
    (hSE : STSEforLnConclgL Cm Hf μ s v) {k : ℕ} (hk : 2 ≤ k) {XL XLK : ℕ → ℕ → ℝ} (hXL1 : ∀ m n, 1 ≤ XL m n)
    (hXLK1 : ∀ m n, 1 ≤ XLK m n)
    (hX : ∀ m : ℕ, 1 ≤ m → m ≤ k + 1 →
      PrecL sz μ (U := fun n => TimeIcc s v n)
        (fun n u ω => STXiLg Cm.toFlowFM n (u : ℝ) m ω) (fun n _ _ => XL m n))
    (hY : ∀ m : ℕ, 1 ≤ m → m ≤ k →
      PrecL sz μ (U := fun n => TimeIcc s v n)
        (fun n u ω => STXiLKg Cm.toFlowFM n (u : ℝ) m ω) (fun n _ _ => XLK m n))
    {ε : ℝ} (hε : 0 < ε) :
    HighProbAt μ sz.size (fun n => {ω | ∀ u : TimeIcc s v n, Hf n (u : ℝ) ω ∈
      GoodLinNg Cm n (u : ℝ) k (((sz.size n : ℕ) : ℝ) ^ ε) (nqLinPhi1 (fun m => XLK m n) k)
        (nqLinPhi2 (fun m => XL m n) (fun m => XLK m n) (sz.Bctl n (v n)) k (XLK k n))
        (nqLinPhi3 (fun m => XL m n) k)}) := by
  have hsz' : Tendsto sz.size atTop atTop := tendsto_size sz hsz
  have hε3 : 0 < ε / 3 := by positivity
  have hpos : ∀ n (u : TimeIcc s v n), 0 < sz.Bctl n (u : ℝ) ∧ 0 < Cm.eta n (u : ℝ) := by
    intro n u
    have hu1 : (u : ℝ) < 1 := (u.2.2).trans_lt (hv1 n)
    exact ⟨st_Bctl_pos sz hu1, NQGood1Gen_eta_pos hL n hu1⟩
  have wY := gridGood_whp_forall_mem hsz' (Finset.Icc 1 k) (fun m hm => by
    rw [Finset.mem_Icc] at hm
    exact GridGoodGen_precL_whp (hY m hm.1 hm.2) hε3)
  have wX := gridGood_whp_forall_mem hsz' (Finset.Icc 1 (k + 1)) (fun m hm => by
    rw [Finset.mem_Icc] at hm
    exact GridGoodGen_precL_whp (hX m hm.1 hm.2) hε3)
  have hSE' := hSE k hk
  have wD3 := GridGoodGen_precL_whp hSE'.1 hε3
  have wD1 := gridGood_whp_forall_mem hsz' (Finset.Icc 3 k) (fun l hl => by
    rw [Finset.mem_Icc] at hl
    exact GridGoodGen_precL_whp (hSE'.2.1 l hl.1 hl.2) hε3)
  have wD2 := GridGoodGen_precL_whp hSE'.2.2.1 hε3
  have wAll := gridGood_whp_and hsz' wY (gridGood_whp_and hsz' wX (gridGood_whp_and hsz' wD1
    (gridGood_whp_and hsz' wD2 wD3)))
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
  have hBk : 0 ≤ (sz.Bctl n (u : ℝ)) ^ k / Cm.eta n (u : ℝ) :=
    div_nonneg (pow_nonneg hBpos.le _) hηpos.le
  have hYb : ∀ m, 1 ≤ m → m ≤ k →
      0 ≤ STXiLKg Cm.toFlowFM n (u : ℝ) m ω ∧
        STXiLKg Cm.toFlowFM n (u : ℝ) m ω ≤ ((sz.size n : ℕ) : ℝ) ^ (ε / 3) * XLK m n := fun m h1 h2 =>
    ⟨zero_le_one.trans (GridGoodGen_one_le_STXiLKg Cm.toFlowFM m ω hBpos), hY' m (Finset.mem_Icc.2 ⟨h1, h2⟩) u⟩
  have hXb : ∀ m, 1 ≤ m → m ≤ k + 1 →
      0 ≤ STXiLg Cm.toFlowFM n (u : ℝ) m ω ∧
        STXiLg Cm.toFlowFM n (u : ℝ) m ω ≤ ((sz.size n : ℕ) : ℝ) ^ (ε / 3) * XL m n := fun m h1 h2 =>
    ⟨zero_le_one.trans (GridGoodGen_one_le_STXiLg Cm.toFlowFM m ω hBpos), hX' m (Finset.mem_Icc.2 ⟨h1, h2⟩) u⟩
  rw [GoodLinNg, Set.mem_ofPred_eq]
  refine ⟨fun l hl3 hlk σ a => ?_, fun σ a => ?_, fun σ a => ?_⟩
  ·  -- the clause for `STksimLKg`
    have h := hD1' l (Finset.mem_Icc.2 ⟨hl3, hlk⟩) ((u, σ, a) : TimeIcc s v n × (Fin k → Bool) ×
      (Fin k → Zd d (sz.L n)))
    have hm := hYb (k - l + 2) (by omega) (by omega)
    have hΦ : XLK (k - l + 2) n ≤ nqLinPhi1 (fun m => XLK m n) k :=
      Finset.single_le_sum (f := fun m => XLK m n) (fun m _ => zero_le_one.trans (hXLK1 m n))
        (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    exact nqLin_clause hA0 hAΓ hBk (zero_le_one.trans (hXLK1 _ n)) hΦ
      (h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm.2 hBk) hA0))
  ·  -- the clause for `STelklkg`
    have h := hD2' ((u, σ, a) : TimeIcc s v n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
    have hb6 : (sz.Bctl n (u : ℝ)) ^ (1 / 6 : ℝ) ≤ (sz.Bctl n (v n)) ^ (1 / 6 : ℝ) :=
      Real.rpow_le_rpow hBpos.le (Sizes.STBctl_mono sz n (u.2.2) (hv1 n)) (by norm_num)
    exact nqLin_D2_arith hk (Y := fun m => STXiLKg Cm.toFlowFM n (u : ℝ) m ω)
      (X := fun m => STXiLg Cm.toFlowFM n (u : ℝ) m ω) (XL := fun m => XL m n) (XLK := fun m => XLK m n)
      hA1 hAAA hBk (Real.rpow_nonneg hBpos.le _) hb6 (fun m => hXL1 m n) (fun m => hXLK1 m n)
      hYb hXb h
  ·  -- the clause for `STegtg`
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

section Grid

variable {d : ℕ} {sz : Sizes d}

/-- **The transfer and the union bound** (band `nqLin_grid`): if with high probability `Hf n u ω ∈ GoodLinNg … u` for every
`u ∈ [s_n,v_n]`, then with high probability the carrier walk `Cm.Hpath … j` is in `GoodLinNg` at every grid index `j ≤ K n` (the law
`Step2EventsGen_Law` at each `j` and `measurableGoodLinNg`, then `highProbAt_iInter` over `j ≤ K n`, `K n + 1 ≤ N^C`). -/
private theorem NQLinGen_grid {Cm : Step2Mat sz} {E : ℕ → ℝ} {μ : Measure sz.SeqΩ}
    {Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hL : StepDecompGen_LoopForm Cm E) (hLaw : Step2EventsGen_Law Cm μ Hf) {s v : ℕ → ℝ} {K : ℕ → ℕ}
    (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hK : ∀ n, K n ≠ 0) {C : ℝ}
    (hC : ∀ᶠ n in atTop, ((K n + 1 : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C) {k : ℕ} {Γ Φ₁ Φ₂ Φ₃ : ℕ → ℝ}
    (hW : HighProbAt μ sz.size (fun n => {ω | ∀ u : TimeIcc s v n, Hf n (u : ℝ) ω ∈
      GoodLinNg Cm n (u : ℝ) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)})) :
    HighProbAt Cm.Pp sz.size (fun n => {ω | ∀ j ≤ K n,
      Cm.Hpath s v K n j ω ∈ GoodLinNg Cm n (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)}) := by
  have hgrid : ∀ n j, j ≤ K n →
      Cm.Pp {ω | Cm.Hpath s v K n j ω ∈
        GoodLinNg Cm n (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)}ᶜ ≤
      μ {ω | ∀ u : TimeIcc s v n, Hf n (u : ℝ) ω ∈
        GoodLinNg Cm n (u : ℝ) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)}ᶜ := by
    intro n j hj
    have hmem := gridGood_gridTime_mem hsv (fun n => le_rfl) hK n j hj
    have hG := (measurableGoodLinNg hL n (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)).compl
    have e1 : {ω | Cm.Hpath s v K n j ω ∈
        GoodLinNg Cm n (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)}ᶜ =
        {ω | Cm.Hpath s v K n j ω ∈ (GoodLinNg Cm n (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n))ᶜ} := by
      ext ω; simp
    rw [e1, hLaw s v K n j (hs0 n) (hsv n) (hK n) _ hG]
    refine measure_mono ?_
    intro ω hω hall
    exact hω (hall ⟨gridTime s v K n j, hmem⟩)
  have hN1 : ∀ n, (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := fun n => by exact_mod_cast sz.one_le_size n
  have hI := highProbAt_iInter Cm.Pp sz.size (K := fun n => Fin (K n + 1))
    (Ξ := fun n j => {ω | Cm.Hpath s v K n j.1 ω ∈
      GoodLinNg Cm n (gridTime s v K n j.1) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)}) (C := max C 0)
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

/-! ### The public theorems -/

section Public

variable {d : ℕ} {sz : Sizes d}

/-- **`nqLinConclg_of`** (band `nqLinGood_holds`, one carrier): the statement `NQLinConclg` over a carrier `Cm` and a law `μ`, from
`StepDecompGen_LoopForm` (for `η > 0` and the measurability of `GoodLinNg`), the law of the grid state `Step2EventsGen_Law`, the size growth, the window
`0 ≤ s ≤ t < 1` and `STSEforLnConclgL` on `[s,t]` (restricted to `[s,v]`, `v ≤ t`). -/
theorem nqLinConclg_of (Cm : Step2Mat sz) (E : ℕ → ℝ) (μ : Measure sz.SeqΩ)
    (Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (s t : ℕ → ℝ) (hL : StepDecompGen_LoopForm Cm E) (hLaw : Step2EventsGen_Law Cm μ Hf) (hsz : sz.SizeTendsto)
    (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1) (hSE : STSEforLnConclgL Cm Hf μ s t) :
    NQLinConclg Cm μ s t := by
  intro v hsv hvt K hK k hk XL XLK hXL hXLK hX hY C hC ε hε
  have hSEv := NQLinGen_SE_restrict hvt hSE
  have hW := NQLinGen_whp_uniform hL hsz (fun n => (hvt n).trans_lt (ht1 n)) hSEv hk hXL hXLK hX hY hε
  exact NQLinGen_grid hL hLaw hs0 hsv hK hC hW

/-- **`nqLinGoodgL_of`** (band `nqLinGood_holds` as a statement): the family form `NQLinGoodgL d law Flow mkM T0`
from the statement `lem:SEforLn` over the family (`STSEforLngL`), the carrier facts per flow (`Step2EventsGen_Flow` for `Admissible` and `T0 < 1`, `StepDecompGen_LoopForm`) and
the law and the loop compatibility `Step34Gen_LCompat` for every `(sz, z)`.  The hypothesis `StepDecompGen_WalkForm` is part of the shape and is not read:
`GoodLinNg` has no Hermitian clause, and neither is `Step34Gen_LCompat`. -/
theorem nqLinGoodgL_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (E lam' : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Ψ : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hSE : STSEforLngL d STAny law Flow mkM Hf T0) (hFlow : Step2EventsGen_Flow d Flow T0)
    (hL : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_LoopForm (mkM sz z) (E sz z))
    (hW : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_WalkForm (mkM sz z) (lam' sz z) (Ψ sz z))
    (hLaw : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2EventsGen_Law (mkM sz z) (law sz) (Hf sz z))
    (hC : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step34Gen_LCompat (mkM sz z) (Hf sz z)) :
    NQLinGoodgL d law Flow mkM T0 := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠d, h𝔠d0, h𝔠d1, H⟩ := hSE hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨𝔠d, h𝔠d0, h𝔠d1, ?_⟩
  intro 𝔠 sz z hflow s t hs hst ht hR hK hKw hLK hcon hStep2
  have hSE' := H 𝔠 sz z hflow s t hs hst ht hR hK hKw hLK hcon hStep2
  have hA := hFlow.1 sz κ ε 𝔠 𝔡 z hflow
  have ht1 : ∀ n, t n < 1 := fun n => (ht n).trans_lt (hFlow.2 sz κ ε 𝔠 𝔡 z hκ hflow n)
  exact nqLinConclg_of (mkM sz z) (E sz z) (law sz) (Hf sz z) s t (hL sz κ ε 𝔠 𝔡 z hκ hflow) (hLaw sz z) hA.2.2.1 hs ht1 hSE'

end Public

/-! ## 4. The linear drift, the exit time of `GoodSetNg ∩ GoodLinNg`, the sub-Gaussian input -/

section Drift

variable {d : ℕ} {sz : Sizes d}

/-- **The linear drift level** (band `dDriftLinN`): the sum of the `k-2` copies of the first clause, one of the second and one of the third:
`Γ·Γ·(B_u^k/η_u)·((k-2)Φ₁ + Φ₂ + Φ₃)`, `η_u = Cm.eta n u`; no additive `W^{-D'}`. -/
def dDriftLinNg (Cm : Step2Mat sz) (n : ℕ) (u : ℝ) (k : ℕ) (Γ Φ₁ Φ₂ Φ₃ : ℝ) : ℝ :=
  Γ * Γ * ((sz.Bctl n u) ^ k / Cm.eta n u) * (((k : ℝ) - 2) * Φ₁ + Φ₂ + Φ₃)

/-- **The exit time of the carrier walk from `GoodSetNg ∩ GoodLinNg`** (band `nqLinExitTauN`; `GoodSetNg` is used at the crude level `Φ`, only its
level-free clauses and the clause for `STeeMg`). -/
def nqLinExitTauNg (Cm : Step2Mat sz) (s v : ℕ → ℝ) (K : ℕ → ℕ) (k : ℕ)
    (Γ Λ Φ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (τ' D' : ℝ) (n : ℕ) : PathΩ sz → ℕ :=
  gridExitTauNg Cm s v K n (fun j =>
    {H | GoodSetNg Cm n (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D' H} ∩
      GoodLinNg Cm n (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n))

variable {Cm : Step2Mat sz}

/-- **`driftTensorNg_norm_le_of_goodLin`** (band `driftTensorN_norm_le_of_goodLin`): on `GoodLinNg` the drift tensor is bounded by the linear level `Γ²(B_u^k/η_u)((k-2)Φ₁ + Φ₂ + Φ₃)`. -/
theorem driftTensorNg_norm_le_of_goodLin {n : ℕ} {u Γ Φ₁ Φ₂ Φ₃ : ℝ} {k : ℕ} (hk : 2 ≤ k)
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hM : M ∈ GoodLinNg Cm n u k Γ Φ₁ Φ₂ Φ₃) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    ‖driftTensorNg Cm n u M σ a‖ ≤ dDriftLinNg Cm n u k Γ Φ₁ Φ₂ Φ₃ := by
  obtain ⟨hD1, hD2, hD3⟩ := hM
  set X : ℝ := (sz.Bctl n u) ^ k / Cm.eta n u with hX
  have h1 : ‖∑ l ∈ Finset.Icc 3 k, STksimLKMg Cm n u M l (loopOf σ a)‖ ≤ ((k - 2 : ℕ) : ℝ) * (Γ * (Γ * Φ₁) * X) := by
    refine (norm_sum_le _ _).trans ?_
    have hle : ∀ l ∈ Finset.Icc 3 k, ‖STksimLKMg Cm n u M l (loopOf σ a)‖ ≤ Γ * (Γ * Φ₁) * X := fun l hl =>
      hD1 l (Finset.mem_Icc.1 hl).1 (Finset.mem_Icc.1 hl).2 σ a
    refine (Finset.sum_le_card_nsmul _ _ _ hle).trans ?_
    rw [nsmul_eq_mul, Nat.card_Icc]
    have : (k + 1 - 3 : ℕ) = k - 2 := by omega
    rw [this]
  have h2 := hD2 σ a
  have h3 := hD3 σ a
  have hc : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by rw [Nat.cast_sub hk]; norm_num
  unfold driftTensorNg dDriftLinNg
  refine (norm_add₃_le).trans ?_
  rw [hc] at h1
  nlinarith [h1, h2, h3]

/-- **`nqLin_hdriftNg`** (band `nqLin_hdriftN`; the field `hdrift` on `{H_j ∈ GoodLinNg(u_j), j < τ}`): the drift tensor along the walk is
bounded by `dDriftLinNg`. -/
theorem nqLin_hdriftNg {n k : ℕ} (hk : 2 ≤ k) (σ : Fin k → Bool)
    (s v : ℕ → ℝ) (K : ℕ → ℕ) (Γ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (τ : PathΩ sz → ℕ)
    (hτG : ∀ ω j, j < τ ω → Cm.Hpath s v K n j ω ∈
      GoodLinNg Cm n (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)) :
    ∀ ω j, j < K n → j < τ ω → ∀ b : Fin k → Zd d (sz.L n),
      ‖driftTensorNg Cm n (gridTime s v K n j) (Cm.Hpath s v K n j ω) σ b‖ ≤
        dDriftLinNg Cm n (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) :=
  fun ω j _ hjτ b => driftTensorNg_norm_le_of_goodLin hk (hτG ω j hjτ) σ b

/-- **`mem_of_lt_nqLinExitTauNg`** (band `mem_of_lt_nqLinExitTauN`): strictly before the exit, the grid state is in `GoodSetNg ∩ GoodLinNg`
(`mem_of_lt_gridExitTauNg`). -/
theorem mem_of_lt_nqLinExitTauNg {s v : ℕ → ℝ} {K : ℕ → ℕ} {k : ℕ} {Γ Λ Φ Φ₁ Φ₂ Φ₃ : ℕ → ℝ} {τ' D' : ℝ} {n : ℕ} {ω : PathΩ sz} {j : ℕ}
    (h : j < nqLinExitTauNg Cm s v K k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D' n ω) :
    Cm.Hpath s v K n j ω ∈ {H | GoodSetNg Cm n (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D' H} ∩
      GoodLinNg Cm n (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) :=
  mem_of_lt_gridExitTauNg h

/-- **`nqLinExitMeasNg`** (band `nqLinExitMeasN`): `{j < nqLinExitTauNg}` is `filt j`-measurable (`gridExitTauNg_measurableSet` with
`measurableGoodSetNg`, `measurableGoodLinNg` under `StepDecompGen_LoopForm`, and the adaptedness of the walk under `StepDecompGen_WalkForm`). -/
theorem nqLinExitMeasNg {E lam' : ℕ → ℝ} {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ) (s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (Γ Λ Φ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (τ' D' : ℝ) (j : ℕ) :
    MeasurableSet[filt sz j] {ω | j < nqLinExitTauNg Cm s v K k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D' n ω} :=
  gridExitTauNg_measurableSet hW (fun j =>
    (measurableGoodSetNg hL n _ k _ _ _ _ _).inter (measurableGoodLinNg hL n _ _ _ _ _ _)) j

variable {k : ℕ} {E gK : ℕ → ℝ} {A Ck Cv : ℝ}

/-- **`subGaussStop_linNg`** (band `subGaussStop_linN`): the sub-Gaussian input with the exit time `nqLinExitTauNg` (from
`azumaProxy_subG_ugeng`, with `G j = GoodSetNg ∩ GoodLinNg`, `mem_of_lt_nqLinExitTauNg`, `nqLinExitMeasNg`, and `hQ_nonAltNg` on the `GoodSetNg` component); the proxy is `cQVNonAltNg` (independent of `Φ, Φ₁, Φ₂, Φ₃`). -/
theorem subGaussStop_linNg [IsProbabilityMeasure Cm.Pp] {g lam' s v : ℕ → ℝ} {K : ℕ → ℕ}
    {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hd : 0 < d) (hk : 2 ≤ k)
    (h : AzumaSubGNg Cm g s v K) (hL : StepDecompGen_LoopForm Cm E) (hW' : StepDecompGen_WalkForm Cm lam' Ψ) (hQV : QVPropagatedNg Cm g)
    (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1) (n : ℕ) (hm : ‖Cm.m n‖ ≤ 1)
    (hS : ∀ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hcmp : ∀ m, 0 ≤ gK m * sz.lam m ∧ gK m ^ 2 ≤ sz.lam m ^ 2 ∧ sz.lam m ^ 2 ≤ A * gK m ^ 2) (hA : 1 ≤ A)
    (hKer : NQGoodGen_KerNAL Cm.toFlowFM gK k Ck n) (hRow : GridRepTailGen_Ker Cm.toFlowFM n) (hCv : Ck ≤ Cv)
    (hwL : v n ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - v n) / (1 - s n))
    {ε τ' D' D'' : ℝ} (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hε0 : 0 < ε) (hε1 : ε < 1) (hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hdW : (d : ℝ) * Real.sqrt A * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hAk : A ^ (k - 1) ≤ ((sz.W n : ℕ) : ℝ) ^ ((Cv - Ck) * ε)) (hD'' : (k : ℝ) + 1 < D'')
    {σ : Fin k → Bool} (hσ : ∃ i, σ i = σ (finRotate k i)) (Γ Λ Φ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (hΛ : 0 ≤ Λ n) (m : ℕ) (hmK : m ≤ K n)
    (a : Fin k → Zd d (sz.L n)) (j : ℕ) (hj : j < m)
    (hδ : ((sz.W n : ℕ) : ℝ) ^ (-D') + eeShiftErrNg Cm n k (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'')) :
    SubGaussStopNg Cm σ (gridTime s v K n) (nqLinExitTauNg Cm s v K k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D' n)
      (fun j ω => ZvecNg Cm s v K n j σ ω) m a j (cQVNonAltNg Cm s v K n k Cv ε Γ Λ D'' m a j) :=
  azumaProxy_subG_ugeng h hL hQV hs0 hsv hv1 n k hRow hk σ (nqLinExitTauNg Cm s v K k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D' n)
    (fun j => {H | GoodSetNg Cm n (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D' H} ∩
      GoodLinNg Cm n (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n))
    (nqLinExitMeasNg hL hW' s v K n k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D')
    (fun ω j hj => mem_of_lt_nqLinExitTauNg hj) m hmK a j hj (cQVNonAltNg Cm s v K n k Cv ε Γ Λ D'' m a j)
    (fun M hM hMh => hQ_nonAltNg hd hL hm hS hcmp hA hKer hRow hCv (hs0 n) (hsv n) (hv1 n) hwL hWt hW hε0 hε1 hWε hdW hAk
      hD'' hσ Γ Λ Φ hΛ m hmK a j hj hδ M hM.1 hMh)

end Drift

/-! ## 5. The linear budget -/

section Budget

variable {d : ℕ} {sz : Sizes d}

/-- **The right-hand side of `AssembledNg` at `m = K n` with the linear drift** (band `assembledRHSLinN`): the right-hand side with the drift level
`dDriftLinNg … (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)`; no crude level `Φ` (the QV proxy `cQVNonAltNg` has none). -/
def assembledRHSLinNg {sz : Sizes d} (Cm : Step2Mat sz) (s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (Ck ε : ℝ)
    (Γ Λ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (D' D'' D_Y τK εq X0 : ℝ) (a : Fin k → Zd d (sz.L n)) : ℝ :=
  kappaNonAltNg k Ck (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) 0 (K n) * X0 +
    epsNonAltNg Ck ((sz.W n : ℕ) : ℝ) 0 (K n) * ((sz.W n : ℕ) : ℝ) ^ (-D') +
    gridStep s v K n * ∑ j ∈ Finset.range (K n),
      (kappaNonAltNg k Ck (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) (j + 1) (K n) *
          dDriftLinNg Cm n (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) +
        epsNonAltNg Ck ((sz.W n : ℕ) : ℝ) (j + 1) (K n) * ((sz.W n : ℕ) : ℝ) ^ (-D')) +
    ((sz.size n : ℕ) : ℝ) ^ εq * Real.sqrt (∑ j ∈ Finset.range (K n),
      (cQVNonAltNg Cm s v K n k Ck ε Γ Λ D'' (K n) a j : ℝ)) +
    ((sz.size n : ℕ) : ℝ) ^ (-D_Y) +
    ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k *
      stepErrNg Cm.toFlowFM n k (gridTime s v K n j) (gridTime s v K n (j + 1))
        (gridStep s v K n)
        (((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (gridTime s v K n (j + 1)))⁻¹ ^ k)

/-- **The linear drift term at the data** (band `tbDriftLinN`): the drift term of `assembledRHSLinNg` is at most
`W^{Ck ε} Γ²((k-2)Φ₁ + Φ₂ + Φ₃) B_v^k Σ_j Δ/η_{u_j} + (KΔ)(W^{Ck} W^{-D'})` (`tbDriftNg` with `a = Γ²((k-2)Φ₁ + Φ₂ + Φ₃) ≥ 0`, `b = 0`, the sharp
kernel `kappaNonAltNg_succ_mul_Bctl_pow_le`; `dDriftLinNg = a B_{u_j}^k/η_{u_j}`). -/
theorem tbDriftLinNg {E s v : ℕ → ℝ} {K : ℕ → ℕ} (Cm : Step2Mat sz) (hL : StepDecompGen_LoopForm Cm E) (n k : ℕ) (Ck ε : ℝ)
    (Γ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (D' : ℝ) (hm : ‖Cm.m n‖ ≤ 1) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1)
    (hK : K n ≠ 0) (hk : 2 ≤ k) (hΓ : 0 ≤ Γ n) (hΦ₁ : 0 ≤ Φ₁ n) (hΦ₂ : 0 ≤ Φ₂ n) (hΦ₃ : 0 ≤ Φ₃ n)
    (hη : (Cm.eta n (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) :
    gridStep s v K n * ∑ j ∈ Finset.range (K n),
      (kappaNonAltNg k Ck (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) (j + 1) (K n) *
          dDriftLinNg Cm n (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) +
        epsNonAltNg Ck ((sz.W n : ℕ) : ℝ) (j + 1) (K n) * ((sz.W n : ℕ) : ℝ) ^ (-D')) ≤
      ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
          (Γ n * Γ n * (((k : ℝ) - 2) * Φ₁ n + Φ₂ n + Φ₃ n)) *
          (sz.Bctl n (v n)) ^ k *
          ∑ j ∈ Finset.range (K n), gridStep s v K n / Cm.eta n (gridTime s v K n j) +
        ((K n : ℝ) * gridStep s v K n) *
          (((sz.W n : ℕ) : ℝ) ^ Ck * ((sz.W n : ℕ) : ℝ) ^ (-D')) := by
  have hW : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hu0 : ∀ i, 0 ≤ gridTime s v K n i := fun i => nqLin_gridTime_nonneg hs0 hsv i
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi =>
    (nqLin_gridTime_le hsv hK hi).trans_lt hv1
  have huK := gridTime_last s v K n hK
  have hmono : ∀ i m, i ≤ m → gridTime s v K n i ≤ gridTime s v K n m := fun i m him =>
    ST_gridTime_mono s v K n hsv him
  have hΔ0 : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n hsv
  have hN1 : (1 - v n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := NQBudgetGen_inv_one_sub_le hL hm hv1 hη
  have hk2 : (0 : ℝ) ≤ (k : ℝ) - 2 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have ha0 : 0 ≤ Γ n * Γ n * (((k : ℝ) - 2) * Φ₁ n + Φ₂ n + Φ₃ n) :=
    mul_nonneg (mul_nonneg hΓ hΓ) (add_nonneg (add_nonneg (mul_nonneg hk2 hΦ₁) hΦ₂) hΦ₃)
  have hsucc : ∀ j < K n, kappaNonAltNg k Ck (sz.lam n) ((sz.W n : ℕ) : ℝ) ε
      (gridTime s v K n) (j + 1) (K n) * (sz.Bctl n (gridTime s v K n j)) ^ k ≤
      ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
        (sz.Bctl n (gridTime s v K n (K n))) ^ k := fun j hj =>
    kappaNonAltNg_succ_mul_Bctl_pow_le sz n k Ck ε hW (gridTime s v K n) j (K n)
      (hmono j (j + 1) (by omega)) (hmono (j + 1) (K n) (by omega)) (hu1 _ le_rfl)
  have h := tbDriftNg Cm n (k := k) (K := K n) (Δ := gridStep s v K n)
    (Cκ := ((sz.W n : ℕ) : ℝ) ^ (Ck * ε))
    (Cε := ((sz.W n : ℕ) : ℝ) ^ Ck)
    (Cfar := NQBudgetGen_kapFar sz n k Ck ε)
    (a := Γ n * Γ n * (((k : ℝ) - 2) * Φ₁ n + Φ₂ n + Φ₃ n)) (b := 0)
    (δmax := ((sz.W n : ℕ) : ℝ) ^ (-D')) (gridTime s v K n)
    (fun i => sz.Bctl n (gridTime s v K n i))
    (kappaNonAltNg k Ck (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n))
    (epsNonAltNg Ck ((sz.W n : ℕ) : ℝ))
    (fun j => dDriftLinNg Cm n (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n))
    (fun _ => ((sz.W n : ℕ) : ℝ) ^ (-D')) hΔ0 ha0 le_rfl
    (fun j hj => nonAlt_hκ0Ng k Ck (sz.lam n) ((sz.W n : ℕ) : ℝ) ε hW (K n) _ (j + 1) (K n)
      (by omega) le_rfl)
    (fun j hj => nonAlt_hε0Ng Ck ((sz.W n : ℕ) : ℝ) hW (K n) (j + 1) (K n) (by omega) le_rfl)
    hsucc
    (fun j hj => NQBudgetGen_kappa_le_kapFar sz n k Ck ε (gridTime s v K n) (hu0 (j + 1))
      (hmono (j + 1) (K n) (by omega)) (hu1 _ le_rfl) (by rw [huK]; exact hN1))
    (fun _ _ => le_rfl)
    (fun j hj => by
      unfold dDriftLinNg
      rw [add_zero]
      apply le_of_eq
      rw [div_eq_mul_inv]; ring)
    (fun _ _ => Real.rpow_nonneg hW _) (fun _ _ => le_rfl)
    (fun j hj => NQGood1Gen_eta_pos hL n (hu1 j hj.le))
  rw [huK] at h
  simpa only [mul_zero, zero_add] using h

set_option maxHeartbeats 400000 in
-- the 270-line proof of `budgetNonAltLinNg` with a longer drift term needs more than 200000
/-- **The budget of the non-alternating endpoint at the linear drift** (band `budgetNonAltLinN`; (4.22) `am;asoiuw`): at a
fixed `n`, under explicit numerical inequalities only, `assembledRHSLinNg ≤ N^{ε₀} (Λ^{1/2} + Φ₁ + Φ₂ + Φ₃) B_v^k`.  `ha2` has `Γ²` (`(N^{ε₁})²`) in place of
`Γ³`; no `Φ²`, no crude level (`tbInitNonAltNg` and `tbQvNonAltNg` are used as they are; the drift term is `tbDriftLinNg`; final bookkeeping `nqLin_final`). -/
theorem budgetNonAltLinNg {E : ℕ → ℝ} (Cm : Step2Mat sz) (hL : StepDecompGen_LoopForm Cm E) (s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (Ck ε : ℝ) (Γ Λ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (D' D'' D_Y D_t τK εq ε₀ ε₁ X0 : ℝ)
    (a : Fin k → Zd d (sz.L n))
    (hk : 2 ≤ k) (hε₁ : 0 ≤ ε₁) (hm : ‖Cm.m n‖ ≤ 1) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n)
    (hv1 : v n < 1) (hK : K n ≠ 0)
    (hη : (Cm.eta n (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ))
    (hΔη : gridStep s v K n * (Cm.eta n (v n))⁻¹ ≤ 1)
    (hΓ : Γ n = ((sz.size n : ℕ) : ℝ) ^ ε₁) (hΛ : 1 ≤ Λ n) (hΦ₁ : 0 ≤ Φ₁ n) (hΦ₂ : 0 ≤ Φ₂ n)
    (hΦ₃ : 0 ≤ Φ₃ n)
    (hlog : ∑ j ∈ Finset.range (K n), gridStep s v K n / Cm.eta n (gridTime s v K n j) ≤
      (Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ))
    (hX0 : X0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ k)
    (hR : ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k *
        stepErrNg Cm.toFlowFM n k (gridTime s v K n j) (gridTime s v K n (j + 1))
          (gridStep s v K n)
          (((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (gridTime s v K n (j + 1)))⁻¹ ^ k) ≤
      ((sz.size n : ℕ) : ℝ) ^ (-D_t))
    (ha1 : ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) * ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6)
    (ha2 : (k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
        (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 2 *
        ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12)
    (ha3 : ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
        ((sz.size n : ℕ) : ℝ) ^ ε₁ *
        Real.sqrt ((k : ℝ) * ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1))) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12)
    (he1 : ((sz.size n : ℕ) : ℝ) ^ k *
        (((sz.W n : ℕ) : ℝ) ^ Ck * ((sz.W n : ℕ) : ℝ) ^ (-D')) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12)
    (he2 : ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.size n : ℕ) : ℝ) ^ k *
        Real.sqrt ((k : ℝ) * (NQBudgetGen_qvFar sz n k Ck ε * ((sz.W n : ℕ) : ℝ) ^ (-D'')))) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12)
    (he3 : ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-D_Y) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6)
    (he4 : ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-D_t) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6) :
    assembledRHSLinNg Cm s v K n k Ck ε Γ Λ Φ₁ Φ₂ Φ₃ D' D'' D_Y τK εq X0 a ≤
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
      (RBM.Ind.ContinuityNet.cont_inv_size_le_Bctl sz n (hs0.trans hsv) hv1) k
  have hP0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ := Real.rpow_nonneg hN0.le _
  have hLs0 : 0 ≤ (Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) :=
    mul_nonneg (inv_nonneg.2 (hL n).1.le) (Real.log_nonneg hN1)
  have hWC0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ Ck := Real.rpow_nonneg hW0 _
  have hWD0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D') := Real.rpow_nonneg hW0 _
  have hWCε0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) :=
    Real.rpow_nonneg hW0 _
  have hΛr1 : 1 ≤ Λ n ^ ((1 : ℝ) / 2) := Real.one_le_rpow hΛ (by norm_num)
  -- the far part `W^C W^{-D'}` is absorbed once (`he1`)
  have hfar : ((sz.W n : ℕ) : ℝ) ^ Ck * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ k :=
    nqLin_absorb hNk (by positivity) ((mul_comm _ _).trans_le he1) hXN
  -- T1: the initial term
  have T1 : _ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 * (sz.Bctl n (v n)) ^ k :=
    (tbInitNonAltNg sz n k Ck ε (((sz.size n : ℕ) : ℝ) ^ ε₁) X0 hs0 hsv hv1 hK
      (Real.rpow_nonneg hN0.le _) hX0).trans (mul_le_mul_of_nonneg_right ha1 hX0')
  -- T2: the initial decay error
  have T2 : epsNonAltNg Ck ((sz.W n : ℕ) : ℝ) 0 (K n) * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ k := by
    unfold epsNonAltNg
    exact hfar
  -- T3: the drift term (linear in the levels `Φ₁, Φ₂, Φ₃`)
  have T3 : gridStep s v K n * ∑ j ∈ Finset.range (K n),
      (kappaNonAltNg k Ck (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) (j + 1) (K n) *
          dDriftLinNg Cm n (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) +
        epsNonAltNg Ck ((sz.W n : ℕ) : ℝ) (j + 1) (K n) * ((sz.W n : ℕ) : ℝ) ^ (-D')) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (((Φ₁ n + Φ₂ n + Φ₃ n)) * (sz.Bctl n (v n)) ^ k) +
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ k := by
    have h := tbDriftLinNg Cm hL n k Ck ε Γ Φ₁ Φ₂ Φ₃ D' hm hs0 hsv hv1 hK hk hΓ0 hΦ₁ hΦ₂ hΦ₃ hη
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
    have m1 : ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
          (Γ n * Γ n * (((k : ℝ) - 2) * Φ₁ n + Φ₂ n + Φ₃ n)) *
          (sz.Bctl n (v n)) ^ k *
          ∑ j ∈ Finset.range (K n), gridStep s v K n / Cm.eta n (gridTime s v K n j) ≤
        ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
          (Γ n * Γ n * (((k : ℝ) - 2) * Φ₁ n + Φ₂ n + Φ₃ n)) *
          (sz.Bctl n (v n)) ^ k *
          ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (mul_nonneg (mul_nonneg hWCε0 ha0) hX0')
    have m2 : ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
          (Γ n * Γ n * (((k : ℝ) - 2) * Φ₁ n + Φ₂ n + Φ₃ n)) *
          (sz.Bctl n (v n)) ^ k *
          ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) ≤
        ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
          ((k : ℝ) * Γ n ^ 2 * (Φ₁ n + Φ₂ n + Φ₃ n)) *
          (sz.Bctl n (v n)) ^ k *
          ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha_le hWCε0) hX0') hLs0
    have m3 : ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
          ((k : ℝ) * Γ n ^ 2 * (Φ₁ n + Φ₂ n + Φ₃ n)) *
          (sz.Bctl n (v n)) ^ k *
          ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) =
        ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
          (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 2 *
          ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ))) *
          ((Φ₁ n + Φ₂ n + Φ₃ n) * (sz.Bctl n (v n)) ^ k) := by
      rw [hΓ]; ring
    have m4 : ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
          (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 2 *
          ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ))) *
          ((Φ₁ n + Φ₂ n + Φ₃ n) * (sz.Bctl n (v n)) ^ k) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * ((Φ₁ n + Φ₂ n + Φ₃ n) * (sz.Bctl n (v n)) ^ k) :=
      mul_le_mul_of_nonneg_right ha2 (mul_nonneg (by positivity) hX0')
    have f1 : ((K n : ℝ) * gridStep s v K n) *
          (((sz.W n : ℕ) : ℝ) ^ Ck * ((sz.W n : ℕ) : ℝ) ^ (-D')) ≤
        ((sz.W n : ℕ) : ℝ) ^ Ck * ((sz.W n : ℕ) : ℝ) ^ (-D') :=
      (mul_le_mul_of_nonneg_right hKΔ1 (mul_nonneg hWC0 hWD0)).trans_eq (one_mul _)
    exact add_le_add (m1.trans (m2.trans (m3.le.trans m4))) (f1.trans hfar)
  -- T4: the quadratic-variation term
  have T4 : ((sz.size n : ℕ) : ℝ) ^ εq * Real.sqrt (∑ j ∈ Finset.range (K n),
      (cQVNonAltNg Cm s v K n k Ck ε Γ Λ D'' (K n) a j : ℝ)) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (Λ n ^ ((1 : ℝ) / 2) * (sz.Bctl n (v n)) ^ k) +
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ k := by
    have h := tbQvNonAltNg Cm hL n k Ck ε Γ Λ D'' a hm hs0 hsv hv1 hK hΛ0 hη
    have hSv : ∑ j ∈ Finset.range (K n),
        gridStep s v K n / Cm.eta n (gridTime s v K n (j + 1)) ≤
        (Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1 := by
      have hsucc := nqBudget_sum_succ_le (K := K n)
        (fun j => gridStep s v K n / Cm.eta n (gridTime s v K n j))
        (div_nonneg hΔ0 (NQGood1Gen_eta_pos hL n (hu1 0 (Nat.zero_le _))).le)
      simp only [huK] at hsucc
      have hlast : gridStep s v K n / Cm.eta n (v n) ≤ 1 := by
        rw [div_eq_mul_inv]; exact hΔη
      linarith
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hQe0 : 0 ≤ (k : ℝ) * (NQBudgetGen_qvFar sz n k Ck ε * ((sz.W n : ℕ) : ℝ) ^ (-D'')) := by
      have hq : 0 ≤ NQBudgetGen_qvFar sz n k Ck ε := by
        unfold NQBudgetGen_qvFar NQBudgetGen_kapFar
        have hr : 0 ≤ (1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ) := by positivity
        have h1 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
            ((1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ)) ^ (k - 1) := by positivity
        have h2 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ k := by positivity
        have h3 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ Ck := hWC0
        positivity
      positivity
    have hΓX : 0 ≤ Γ n * (sz.Bctl n (v n)) ^ k := mul_nonneg hΓ0 hX0'
    have hZ0 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
        (Γ n * (sz.Bctl n (v n)) ^ k)) ^ 2 * ((k : ℝ) * (
        (Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) * Λ n) := by
      have : 0 ≤ (Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1 := by linarith
      positivity
    have hsum : ∑ j ∈ Finset.range (K n),
        (cQVNonAltNg Cm s v K n k Ck ε Γ Λ D'' (K n) a j : ℝ) ≤
        (((sz.W n : ℕ) : ℝ) ^ (Ck * ε) * (Γ n * (sz.Bctl n (v n)) ^ k)) ^ 2 *
          ((k : ℝ) * ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) * Λ n) +
        (k : ℝ) * (NQBudgetGen_qvFar sz n k Ck ε * ((sz.W n : ℕ) : ℝ) ^ (-D'')) := by
      refine h.trans ?_
      have hc0 : 0 ≤ (k : ℝ) * (((sz.W n : ℕ) : ℝ) ^ (Ck * ε)) ^ 2 *
          (Γ n * (Γ n * Λ n)) * ((sz.Bctl n (v n)) ^ k) ^ 2 := by
        have : Γ n * (Γ n * Λ n) = Γ n ^ 2 * Λ n := by ring
        rw [this]; positivity
      have n1 := mul_le_mul_of_nonneg_left hSv hc0
      have n2 : ((K n : ℝ) * gridStep s v K n) *
          ((k : ℝ) * (NQBudgetGen_qvFar sz n k Ck ε * ((sz.W n : ℕ) : ℝ) ^ (-D''))) ≤
          (k : ℝ) * (NQBudgetGen_qvFar sz n k Ck ε * ((sz.W n : ℕ) : ℝ) ^ (-D'')) :=
        (mul_le_mul_of_nonneg_right hKΔ1 hQe0).trans_eq (one_mul _)
      have e : (k : ℝ) * (((sz.W n : ℕ) : ℝ) ^ (Ck * ε)) ^ 2 *
            (Γ n * (Γ n * Λ n)) * ((sz.Bctl n (v n)) ^ k) ^ 2 *
            ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) =
          (((sz.W n : ℕ) : ℝ) ^ (Ck * ε) * (Γ n * (sz.Bctl n (v n)) ^ k)) ^ 2 *
            ((k : ℝ) * ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) * Λ n) := by ring
      linarith
    have hs1 := Real.sqrt_le_sqrt hsum
    have hs2 : Real.sqrt ((((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
          (Γ n * (sz.Bctl n (v n)) ^ k)) ^ 2 *
          ((k : ℝ) * ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) * Λ n) +
        (k : ℝ) * (NQBudgetGen_qvFar sz n k Ck ε * ((sz.W n : ℕ) : ℝ) ^ (-D''))) ≤
        ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) * (Γ n * (sz.Bctl n (v n)) ^ k) *
          (Real.sqrt ((k : ℝ) * ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)) *
            Real.sqrt (Λ n)) +
        Real.sqrt ((k : ℝ) * (NQBudgetGen_qvFar sz n k Ck ε * ((sz.W n : ℕ) : ℝ) ^ (-D''))) := by
      refine (nqBudget_sqrt_add_le hZ0 hQe0).trans ?_
      have hA0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
          (Γ n * (sz.Bctl n (v n)) ^ k) := mul_nonneg hWCε0 hΓX
      have hP00 : 0 ≤ (k : ℝ) * ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1) :=
        mul_nonneg hk0 (by linarith)
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hA0, Real.sqrt_mul hP00]
    have hsΛ : Real.sqrt (Λ n) = Λ n ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow (Λ n)
    have hNe : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ εq := Real.rpow_nonneg hN0.le _
    have k1 : ((sz.size n : ℕ) : ℝ) ^ εq *
        (((sz.W n : ℕ) : ℝ) ^ (Ck * ε) * (Γ n * (sz.Bctl n (v n)) ^ k) *
          (Real.sqrt ((k : ℝ) * ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)) *
            Real.sqrt (Λ n))) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (Λ n ^ ((1 : ℝ) / 2) * (sz.Bctl n (v n)) ^ k) := by
      have e : ((sz.size n : ℕ) : ℝ) ^ εq *
          (((sz.W n : ℕ) : ℝ) ^ (Ck * ε) * (Γ n * (sz.Bctl n (v n)) ^ k) *
            (Real.sqrt ((k : ℝ) * ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)) *
              Real.sqrt (Λ n))) =
          (((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
            ((sz.size n : ℕ) : ℝ) ^ ε₁ *
            Real.sqrt ((k : ℝ) * ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)))) *
          (Λ n ^ ((1 : ℝ) / 2) * (sz.Bctl n (v n)) ^ k) := by
        rw [hsΛ, hΓ]; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right ha3 (mul_nonneg (by linarith) hX0')
    have k2 : ((sz.size n : ℕ) : ℝ) ^ εq *
        Real.sqrt ((k : ℝ) * (NQBudgetGen_qvFar sz n k Ck ε * ((sz.W n : ℕ) : ℝ) ^ (-D''))) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ k := by
      refine nqLin_absorb hNk (by positivity) ?_ hXN
      have e : ((sz.size n : ℕ) : ℝ) ^ εq *
          Real.sqrt ((k : ℝ) * (NQBudgetGen_qvFar sz n k Ck ε * ((sz.W n : ℕ) : ℝ) ^ (-D''))) *
            ((sz.size n : ℕ) : ℝ) ^ k =
          ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.size n : ℕ) : ℝ) ^ k *
            Real.sqrt ((k : ℝ) * (NQBudgetGen_qvFar sz n k Ck ε *
              ((sz.W n : ℕ) : ℝ) ^ (-D'')))) := by ring
      rw [e]; exact he2
    calc ((sz.size n : ℕ) : ℝ) ^ εq * Real.sqrt (∑ j ∈ Finset.range (K n),
          (cQVNonAltNg Cm s v K n k Ck ε Γ Λ D'' (K n) a j : ℝ))
        ≤ ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
            (Γ n * (sz.Bctl n (v n)) ^ k) *
            (Real.sqrt ((k : ℝ) * ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)) *
              Real.sqrt (Λ n)) +
          Real.sqrt ((k : ℝ) * (NQBudgetGen_qvFar sz n k Ck ε * ((sz.W n : ℕ) : ℝ) ^ (-D'')))) :=
          mul_le_mul_of_nonneg_left (hs1.trans hs2) hNe
      _ = ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ (Ck * ε) *
            (Γ n * (sz.Bctl n (v n)) ^ k) *
            (Real.sqrt ((k : ℝ) * ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1)) *
              Real.sqrt (Λ n))) +
          ((sz.size n : ℕ) : ℝ) ^ εq *
            Real.sqrt ((k : ℝ) * (NQBudgetGen_qvFar sz n k Ck ε *
              ((sz.W n : ℕ) : ℝ) ^ (-D''))) := by ring
      _ ≤ _ := add_le_add k1 k2
  -- T5, T6
  have T5 : ((sz.size n : ℕ) : ℝ) ^ (-D_Y) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 * (sz.Bctl n (v n)) ^ k :=
    nqLin_absorb hNk (by positivity) ((mul_comm _ _).trans_le he3) hXN
  have T6 : _ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 * (sz.Bctl n (v n)) ^ k :=
    hR.trans (nqLin_absorb hNk (by positivity) ((mul_comm _ _).trans_le he4) hXN)
  unfold assembledRHSLinNg
  exact nqLin_final hP0 hX0' hΛr1 hΦ₁ hΦ₂ hΦ₃ T1 T2 T3 T4 T5 T6

end Budget

end RBM.BA

end
