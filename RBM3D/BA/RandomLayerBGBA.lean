/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.GUEPhase.RandomLayerBG
import RBM3D.BA.UNPins
import RBM3D.BA.MReg
import RBM3D.BA.FlowPins
import RBM3D.BA.MFixedPoint
import RBM3D.Chain.Carrier

/-!
# UN-51 repaired at `UNKind.ba` (BA leaf of `RandomLayerBG`): the four BA instances and the compatibility input

T2475 (BA stage M/N row C5g; supervisor 2049 GMN-C3).  The generic file `Universality/GUEPhase/RandomLayerBG.lean`
(no `BA/*` import) states the repaired inputs `RBG_Flow`, `RBG_Dom`, `RBG_Prod`, `RBG_Que`, the compatibility input
`RBG_Comp` and `g1Rowk_of_inputsG`.  This leaf supplies the BA side, at `K = UNKind.ba d`:

* the vocabulary: `BAfT` (`t₀ = BAt0 w (BAm …)`), `BAfE` (`BAflowE`), `BAEd` (the margin datum
  `∃ m₀, BAReal d L (√t₀ g) κ' E m₀`, i.e. `(eq:t0E0_BA)`'s flow point has `Im m₀ ≥ κ'`), `BAMO` (conjuncts 1, 5, 4
  of `UNMLOutBA`);
* `ba_dom_of_bulk` (`BAm_im_lower_window` at `x = E`, `BA/MReg.lean:227`);
* `ba_flowG` (`Flow'`, `κ' = c = (πκ)^5/2048`, `cT = κ'/(κ'+1)`), `ba_domG` (`Dom'`, `κ' = (πκ)^5/2048`),
  `ba_mlout` (the merged T5 `RandomLayerB_MLout` from `UNMLOutBA`, unchanged);
* `RandomLayerBGBA_comp` (target 13): `RBG_ProfComp (UNKind.ba d) P → RBG_Comp (UNKind.ba d) P`; the law is
  `seqP (sz.withLam 0)` (`withLam_comp`, `measurePreserving_reindex`), the bulk `BAbulk d (sz.L n) (sz.lam n)` is
  definitional; the profile half is C3's (`UNOUProfile.ba` is a variable `P` until C3).

The producers `RBG_Prod`, `RandomLayerB_LL`, `RBG_Que` at `UNKind.ba` are C5's, `RBG_ProfComp` at BA is C3's and
`UNMLOutBA` is V3's: they are hypotheses of the instances only (CLAUDE.md §4 step 2).  The paper-delta `T2449b`:
the UN-51 interface Flow/Dom/Bulk is false at BA (`T1` conj. 1, 2, 4, `T1'`, `T6`); the repaired inputs carry
`κ' = (πκ)^5/2048`, `cT`, `η_{t₀} := √fT Im z`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.BA

open MeasureTheory Filter Topology
open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Univ RBM.Univ.GUEPhase RBM.Endpoints

/-! ### The vocabulary of the BA kind (target 10) -/

/-- `t₀` of the flow at `w` (`BAflowT0 sz z n = BAfT d sz n (z n)` definitionally). -/
def BAfT (d : ℕ) (sz : Sizes d) (n : ℕ) (w : ℂ) : ℝ := BAt0 w (BAm d (sz.L n) (sz.lam n) w)

/-- `E` of the flow at `w` (`BAflowEs sz z n = BAfE d sz n (z n)` definitionally). -/
def BAfE (d : ℕ) (sz : Sizes d) (n : ℕ) (w : ℂ) : ℝ := BAflowE w (BAm d (sz.L n) (sz.lam n) w)

/-- The margin datum `Ed κ'` at BA: the flow point `(√t₀ g, E)` has a real solution `m₀` of the self-consistent
equation with `Im m₀ ≥ κ'`. -/
def BAEd (d : ℕ) (κ' : ℝ) (sz : Sizes d) (n : ℕ) (w : ℂ) : Prop :=
  ∃ m₀ : ℂ, BAReal d (sz.L n) (Real.sqrt (BAfT d sz n w) * sz.lam n) κ' (BAfE d sz n w) m₀

/-- The `G`-loop outputs `MO` at BA: conjuncts 1, 5, 4 of `UNMLOutBA` (`STLKgL`, `STLocalEntrygL`, `STExp2gL` on the
carrier `baFMz sz z` and the law `seqP (sz.withLam 0)`). -/
def BAMO (d : ℕ) (sz : Sizes d) (z : ℕ → ℂ) (t : ℕ → ℝ) : Prop :=
  STLKgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ∧ STLocalEntrygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ∧
    STExp2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t

/-! ### Targets 9-12 -/

/-- **Target 9**: the chain domain from the ρ-bulk, uniformly in `L`, `g` (`BAm_im_lower_window`,
`BA/MReg.lean:227`, at `x = E`). -/
theorem ba_dom_of_bulk (d L : ℕ) [NeZero L] (g κ : ℝ) (hκ : 0 < κ) {z : ℂ} (hb : BAbulk d L g κ z.re)
    (h0 : 0 < z.im) (h1 : z.im ≤ 1) : (Real.pi * κ) ^ 5 / 2048 ≤ (BAm d L g z).im := by
  have := BAm_im_lower_window d L g κ z.re z.re z.im hκ hb (by simp only [sub_self, abs_zero]; positivity) h0
    (by linarith)
  rwa [Complex.re_add_im] at this

/-- `cT = κ'/(κ'+1) ≤ b/(b+a)` and `1 - b/(b+a) ≤ a/κ'` for `κ' ≤ b`, `0 < a ≤ 1` (`t₀ = b/(b+a)`, `b = Im m`, `a = Im z`). -/
private theorem RandomLayerBGBA_t0_ineq {κ' a b : ℝ} (hk : 0 < κ') (ha : 0 < a) (ha1 : a ≤ 1) (hb : κ' ≤ b) :
    κ' / (κ' + 1) ≤ b / (b + a) ∧ 1 - b / (b + a) ≤ a / κ' := by
  have hb0 : 0 < b := lt_of_lt_of_le hk hb
  constructor
  · rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left ha1 hk.le]
  · have : 1 - b / (b + a) = a / (b + a) := by field_simp; ring
    rw [this]
    exact div_le_div_of_nonneg_left ha.le hk (by linarith)

/-- The margin datum from `Im m ≥ κ'` (`BAdom_real`, `BAm_self`). -/
theorem ba_Ed_of_im (d : ℕ) (κ' : ℝ) (sz : Sizes d) (n : ℕ) (z : ℂ) (h0 : 0 < z.im)
    (hm : κ' ≤ (BAm d (sz.L n) (sz.lam n) z).im) : BAEd d κ' sz n z :=
  ⟨_, BAdom_real h0 (BAm_self d _ _ z h0) hm⟩

/-- **Target 10**: `Flow'` at `UNKind.ba` with `κ' = c = (πκ)^5/2048` and `cT = κ'/(κ'+1)`. -/
theorem ba_flowG (d : ℕ) : RBG_Flow (UNKind.ba d) (BAEd d) (BAfT d) := by
  intro κ hκ
  have hk : 0 < (Real.pi * κ) ^ 5 / 2048 := by positivity
  refine ⟨(Real.pi * κ) ^ 5 / 2048, (Real.pi * κ) ^ 5 / 2048,
    (Real.pi * κ) ^ 5 / 2048 / ((Real.pi * κ) ^ 5 / 2048 + 1), hk, hk, by positivity, ?_⟩
  intro sz n z hb h0 h1
  have hm := ba_dom_of_bulk d (sz.L n) (sz.lam n) κ hκ (hb : BAbulk d (sz.L n) (sz.lam n) κ z.re) h0 h1
  obtain ⟨i1, i2⟩ := RandomLayerBGBA_t0_ineq hk h0 h1 hm
  exact ⟨ba_Ed_of_im d _ sz n z h0 hm, i1, BAt0_lt_one h0 (lt_of_lt_of_le hk hm), i2⟩

/-- **Target 11**: `Dom'` at `UNKind.ba`, `Fl = BAFlow`, `κ' = (πκ)^5/2048`. -/
theorem ba_domG (d : ℕ) : RBG_Dom (UNKind.ba d) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) := by
  intro κ hκ
  refine ⟨(Real.pi * κ) ^ 5 / 2048, by positivity, ?_⟩
  intro 𝔠 𝔡 ε sz hA hε E η hb h1 h2
  refine ⟨hA, fun n => ?_⟩
  have hη0 : 0 < η n := lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.one_le_size n) _) (h1 n)
  exact ⟨ba_dom_of_bulk d (sz.L n) (sz.lam n) κ hκ (z := (E n : ℂ) + (η n : ℂ) * Complex.I)
    (by have h : BAbulk d (sz.L n) (sz.lam n) κ (E n) := hb n; simpa using h)
    (by simpa using hη0) (by simpa using h2 n), by simpa using h1 n, by simpa using h2 n⟩

/-- **Target 12**: the merged T5 `RandomLayerB_MLout` (unchanged) at `Fl = BAFlow`, `fT = BAfT`, `MO = BAMO`, from
`UNMLOutBA` (V3's pin). -/
theorem ba_mlout (d : ℕ) (hd : 3 ≤ d) (h : UNMLOutBA d) :
    RandomLayerB_MLout (BAfT d) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (BAMO d) := by
  intro κ ε 𝔡 𝔠 hκ hε h𝔡 sz z hf t ht0 ht
  obtain ⟨h1, -, -, h4, h5⟩ := h hd κ ε 𝔡 𝔠 hκ hε h𝔡 sz z hf t ht0 ht
  exact ⟨h1, h5, h4⟩

/-! ### Target 13: the compatibility input at `UNKind.ba` -/

/-- **Target 13**: `RBG_ProfComp (UNKind.ba d) P → RBG_Comp (UNKind.ba d) P`.  The law is `seqP (sz.withLam 0)`,
`R = reindex (sz.withLam 0) φ` (`measurePreserving_reindex`, `withLam_comp`); the bulk is definitional; the profile
half is the hypothesis (C3's, with `UNOUProfile.ba`). -/
theorem RandomLayerBGBA_comp (d : ℕ) {P : UNOUProfile (UNKind.ba d)} (hP : RBG_ProfComp (UNKind.ba d) P) :
    RBG_Comp (UNKind.ba d) P :=
  RandomLayerBG_Comp_of_law _ _ hP (fun _ _ _ _ _ h => h) fun sz φ hφ =>
    ⟨reindex (sz.withLam 0) φ, measurePreserving_reindex (sz.withLam 0) φ hφ.injective, fun _ _ => rfl, fun _ => rfl⟩

/-! ## Compiled nonempty instances (target 14, `d = 3`)

`S0 = clsS 4 (g = 3/10)` (`BA/UNPins.lean:884`) and `sz0` with `zSeq` (`BA/FlowPins.lean:1181`).  Every deterministic
premise is discharged; `UNMLOutBA`, `RBG_ProfComp`, and C5's producers `RBG_Prod`, `RandomLayerB_LL`, `RBG_Que` at BA
stay hypotheses (other gates' pins). -/

end RBM.BA

end
