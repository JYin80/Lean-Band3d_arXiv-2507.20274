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

section Inst

open RBM.BA.UNPinsInst RBM.Univ.BAInst RBM.BA.FlowPinsInst RBM.Gauss.SizesInst

private theorem RandomLayerBGBA_hg : (0 : ℝ) < 3 / 10 := by norm_num

/-- `Flow'` at `S0`, `n = 0`, `z = E_* + i/2` (hypothesis-free). -/
example : let z : ℂ := ⟨(fp 4 RandomLayerBGBA_hg).E, 1 / 2⟩; ∃ κ' c cT : ℝ, 0 < κ' ∧ 0 < c ∧ 0 < cT ∧
    BAEd 3 κ' S0 0 z ∧ cT ≤ BAfT 3 S0 0 z ∧ BAfT 3 S0 0 z < 1 ∧ 1 - BAfT 3 S0 0 z ≤ z.im / c := by
  intro z
  obtain ⟨κ', c, cT, h1, h2, h3, H⟩ := ba_flowG 3 (clsκ 4 RandomLayerBGBA_hg) (clsκ_pos 4 RandomLayerBGBA_hg)
  exact ⟨κ', c, cT, h1, h2, h3, H S0 0 z (cls_bulk 4 (by norm_num) RandomLayerBGBA_hg) (by norm_num) (by norm_num)⟩

/-- `Flow'` at `S0` for every `n`, at the scale `Im z = N^{-19/20}`. -/
example (n : ℕ) : let z : ℂ := ⟨(fp 4 RandomLayerBGBA_hg).E, Nsz S0 n ^ (-(19 : ℝ) / 20)⟩; ∃ κ' c cT : ℝ,
    0 < κ' ∧ 0 < c ∧ 0 < cT ∧ BAEd 3 κ' S0 n z ∧ cT ≤ BAfT 3 S0 n z ∧ BAfT 3 S0 n z < 1 ∧
      1 - BAfT 3 S0 n z ≤ z.im / c := by
  intro z
  obtain ⟨κ', c, cT, h1, h2, h3, H⟩ := ba_flowG 3 (clsκ 4 RandomLayerBGBA_hg) (clsκ_pos 4 RandomLayerBGBA_hg)
  have hN : (1 : ℝ) ≤ Nsz S0 n := by exact_mod_cast S0.one_le_size n
  exact ⟨κ', c, cT, h1, h2, h3, H S0 n z (cls_bulk 4 (by norm_num) RandomLayerBGBA_hg)
    (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num))⟩

/-- `Dom'` at `S0` (`ε = 1/20`, `E ≡ E_*`, `η_n = N^{-1+ε}`), then T5 (`ba_mlout`) along that flow at the times
`t_n ≡ cT` (`cT ≤ fT` from `Flow'` at the same points): `UNMLOutBA 3` is the hypothesis. -/
example (hML : UNMLOutBA 3) : ∃ κ'' cT : ℝ, 0 < κ'' ∧ 0 < cT ∧
    BAFlow S0 κ'' (1 / 20) (1 / 6) (1 / 10)
      (fun n => (((fp 4 RandomLayerBGBA_hg).E : ℝ) : ℂ) + ((Nsz S0 n ^ (-1 + 1 / 20 : ℝ) : ℝ) : ℂ) * Complex.I) ∧
    BAMO 3 S0 (fun n => (((fp 4 RandomLayerBGBA_hg).E : ℝ) : ℂ) + ((Nsz S0 n ^ (-1 + 1 / 20 : ℝ) : ℝ) : ℂ) * Complex.I)
      (fun _ => cT) := by
  obtain ⟨κ', c, cT, h1, h2, h3, F⟩ := ba_flowG 3 (clsκ 4 RandomLayerBGBA_hg) (clsκ_pos 4 RandomLayerBGBA_hg)
  obtain ⟨κ'', hκ'', D⟩ := ba_domG 3 (clsκ 4 RandomLayerBGBA_hg) (clsκ_pos 4 RandomLayerBGBA_hg)
  have hN : ∀ n, (1 : ℝ) ≤ Nsz S0 n := fun n => by exact_mod_cast S0.one_le_size n
  have hle : ∀ n, Nsz S0 n ^ (-1 + 1 / 20 : ℝ) ≤ 1 := fun n =>
    Real.rpow_le_one_of_one_le_of_nonpos (hN n) (by norm_num)
  have hflow := D (1 / 6) (1 / 10) (1 / 20) S0 S0_adm (by norm_num) (fun _ => (fp 4 RandomLayerBGBA_hg).E)
    (fun n => Nsz S0 n ^ (-1 + 1 / 20 : ℝ)) (fun _ => cls_bulk 4 (by norm_num) RandomLayerBGBA_hg) (fun n => le_rfl) hle
  have hcT : ∀ n, cT ≤ BAfT 3 S0 n ((((fp 4 RandomLayerBGBA_hg).E : ℝ) : ℂ) +
      ((Nsz S0 n ^ (-1 + 1 / 20 : ℝ) : ℝ) : ℂ) * Complex.I) := fun n => by
    have hz : ((((fp 4 RandomLayerBGBA_hg).E : ℝ) : ℂ) + ((Nsz S0 n ^ (-1 + 1 / 20 : ℝ) : ℝ) : ℂ) * Complex.I) =
        (⟨(fp 4 RandomLayerBGBA_hg).E, Nsz S0 n ^ (-1 + 1 / 20 : ℝ)⟩ : ℂ) := Complex.ext (by simp) (by simp)
    rw [hz]
    exact (F S0 n ⟨(fp 4 RandomLayerBGBA_hg).E, Nsz S0 n ^ (-1 + 1 / 20 : ℝ)⟩
      (cls_bulk 4 (by norm_num) RandomLayerBGBA_hg) (Real.rpow_pos_of_pos (by linarith [hN n]) _) (hle n)).2.1
  exact ⟨κ'', cT, hκ'', h3, hflow, ba_mlout 3 le_rfl hML κ'' (1 / 20) (1 / 10) (1 / 6) hκ'' (by norm_num)
    (by norm_num) S0 _ hflow (fun _ => cT) (fun _ => h3.le) hcT⟩

/-- `Dom'` at `S0` and the T5 instance of the probe (`sz0`, `zSeq`, `κ = 1/2`, `ε = 1/10`, `t_n ≡ 1/2`):
`UNMLOutBA 3` is the hypothesis. -/
example (hML : UNMLOutBA 3) : BAMO 3 sz0 zSeq (fun _ => 1 / 2) :=
  ba_mlout 3 le_rfl hML (1 / 2) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 zSeq
    flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => le_trans (by norm_num) (t0_sz0 n))

/-- Target 13 at `S0` with `φ = (2 * ·)`: the profile `P` and its `RBG_ProfComp` are hypotheses (C3's). -/
example (P : UNOUProfile (UNKind.ba 3)) (hP : RBG_ProfComp (UNKind.ba 3) P) (j : ℕ) :
    (∀ κ e : ℝ, (UNKind.ba 3).bulk S0 κ e (2 * j) → (UNKind.ba 3).bulk (S0.comp (2 * ·)) κ e j) ∧
    (∀ (τU e s δ : ℝ) (p : ℕ), RandomLayerB_LLAt (UNKind.ba 3) (S0.comp (2 * ·)) τU j e s δ p →
      RandomLayerB_LLAt (UNKind.ba 3) S0 τU (2 * j) e s δ p) ∧
    (∀ 𝔡 e s τ : ℝ, RandomLayerB_QueAt (UNKind.ba 3) P (S0.comp (2 * ·)) 𝔡 j e s τ →
      RandomLayerB_QueAt (UNKind.ba 3) P S0 𝔡 (2 * j) e s τ) :=
  RandomLayerBGBA_comp 3 hP S0 (2 * ·) (fun a b h => by change 2 * a < 2 * b; omega) j

/-- **The BA reading of D2 at `S0`** (N2's instance): targets 10-13 discharge `Flow'`, `Dom'`, `RBG_Comp`, T5;
`RBG_Prod`, `RandomLayerB_LL`, `RBG_Que` at BA (C5), `RBG_ProfComp` (C3), `UNMLOutBA` (V3) stay hypotheses. -/
example (P : ∀ d, UNOUProfile (UNKind.ba d))
    (KF PB : ∀ d : ℕ, ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop)
    (hP : ∀ d, 3 ≤ d → RBG_ProfComp (UNKind.ba d) (P d))
    (hProd : ∀ d, 3 ≤ d → RBG_Prod (BAEd d) (BAfE d) (BAfT d) (BAMO d) (KF d) (PB d))
    (hLL : ∀ d, 3 ≤ d → RandomLayerB_LL (UNKind.ba d) (BAfE d) (BAfT d) (PB d))
    (hQue : ∀ d, 3 ≤ d → RBG_Que (UNKind.ba d) (P d) (BAEd d) (BAfE d) (BAfT d) (BAMO d) (KF d) (PB d))
    (hML : ∀ d : ℕ, UNMLOutBA d) (hLoc : UNLocAvgBA) (hQ : UNQueBA) :
    UNOULLk (UNKind.ba 3) S0 (ouTauMax (1 / 6) (1 / 10)) ∧
      UNOUEq747k (UNKind.ba 3) (P 3) S0 (1 / 10) (ouTauMax (1 / 6) (1 / 10)) :=
  g1Rowk_of_inputsG (fun d => UNKind.ba d) P (∀ d : ℕ, UNMLOutBA d) UNLocAvgBA UNQueBA BAEd BAfE BAfT
    (fun d sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) BAMO KF PB (fun d _ => ba_flowG d) (fun d _ => ba_domG d)
    (fun d hd => RandomLayerBGBA_comp d (hP d hd)) hProd hLL hQue (fun hML' d hd => ba_mlout d hd (hML' d)) hML hLoc hQ
    3 le_rfl (1 / 6) (1 / 10) S0 S0_adm _ (ouTauMax_pos (by norm_num) (by norm_num)) le_rfl

end Inst

end RBM.BA

end
