/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.MainIndChain
import RBM3D.Induction.Step4
import RBM3D.Induction.Step3
import RBM3D.Induction.DuhamelII
import RBM3D.Induction.IniTermI
import RBM3D.Induction.LocalAvg2
import RBM3D.Graph.LWExpTerm6
import RBM3D.BA.UNPins

/-!
# From `lem:main_ind` to `UNMLOut` at every `0 ≤ t_n ≤ lemT z_n`

The loop estimates of Lemma 2.21 `ML:GLoop`, Lemma 2.22 `ML:GLoop_expec` and Lemma 2.23 `ML:GtLocal`
at every `0 ≤ t_n ≤ T0`, from the induction of Theorem 2.24 (`lem:main_ind`).

* `STMLOutG`: the output over a carrier `(law, Flow, mk, T0)` (`ML:GLoop`, `ML:GLoop_expec`,
  `ML:GtLocal`);
* `stMLOutG_of_mainIndG`: `STMainIndG` + `STHorizonG` + `STBaseG` give `STMLOutG`.  Run the chain to
  `t'_n = t_n` if `t_n > 0`, `T0_n/2` if `t_n = 0`, and mix with the zero sequence on the class
  `t_n = 0` (`StochDomAt.of_subset_union`: no subsequence, no pattern classes);
* `RBM.Univ.unMLOut_iff` (`Iff.rfl`: `UNMLOut` is `STMLOutG` at the band data),
  `unMLOut_of_mainInd` (`STMainInd d → UNMLOut d`, no further hypothesis);
* `RBM.Gauss.Sizes.stMainInd_of_LW`: `STMainInd` from the two light-weight estimates `LWterm`,
  `LWtermExp` (every other premise of `ST_mainInd_of_pins'` is proved, `stDuhamelII_holds`), and
  `RBM.Univ.unMLOut_of_LW`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

open MeasureTheory Filter
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Ind

namespace RBM.BA

/-! ## 1. The statement -/

/-- **The output over a carrier**: `ML:GLoop`, `ML:GLoop_expec`, `ML:GtLocal` at every `0 ≤ t_n ≤ T0`;
band: `UNMLOut`. -/
def STMLOutG (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 𝔠 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ),
    Flow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
      STLKgL (mk sz z) (law sz) t ∧ STLmaxgL (mk sz z) (law sz) t ∧ STDecaygL (mk sz z) (law sz) t ∧
        STExp2gL (mk sz z) (law sz) t ∧ STLocalEntrygL (mk sz z) (law sz) t

/-! ## 2. Mixing at the class `t_n = 0` (formal: `StochDomAt.of_subset_union`) -/

section Mix
variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (hs : Tendsto sz.size atTop atTop)
  {t t' : ℕ → ℝ} (hm : ∀ n, t n = 0 ∨ t n = t' n)
include hs hm

private theorem STLKgL_mix (h0 : STLKgL C μ (fun _ => 0)) (h1 : STLKgL C μ t') : STLKgL C μ t := fun k hk =>
  StochDomAt.of_subset_union hs (h0 k hk) (h1 k hk) fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun n ω ⟨u, hu⟩ => by
    rcases hm n with h | h
    exacts [Or.inl ⟨u, by simpa [h] using hu⟩, Or.inr ⟨u, by simpa [h] using hu⟩]⟩

private theorem STLmaxgL_mix (h0 : STLmaxgL C μ (fun _ => 0)) (h1 : STLmaxgL C μ t') : STLmaxgL C μ t := fun k hk =>
  StochDomAt.of_subset_union hs (h0 k hk) (h1 k hk) fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun n ω ⟨u, hu⟩ => by
    rcases hm n with h | h
    exacts [Or.inl ⟨u, by simpa [h] using hu⟩, Or.inr ⟨u, by simpa [h] using hu⟩]⟩

private theorem STDecaygL_mix (h0 : STDecaygL C μ (fun _ => 0)) (h1 : STDecaygL C μ t') : STDecaygL C μ t := fun D hD =>
  StochDomAt.of_subset_union hs (h0 D hD) (h1 D hD) fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun n ω ⟨u, hu⟩ => by
    rcases hm n with h | h
    exacts [Or.inl ⟨u, by simpa [h] using hu⟩, Or.inr ⟨u, by simpa [h] using hu⟩]⟩

private theorem STExp2gL_mix (h0 : STExp2gL C μ (fun _ => 0)) (h1 : STExp2gL C μ t') : STExp2gL C μ t :=
  StochDomAt.of_subset_union hs h0 h1 fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun n ω ⟨u, hu⟩ => by
    rcases hm n with h | h
    exacts [Or.inl ⟨u, by simpa [h] using hu⟩, Or.inr ⟨u, by simpa [h] using hu⟩]⟩

private theorem STLocalEntrygL_mix (h0 : STLocalEntrygL C μ (fun _ => 0)) (h1 : STLocalEntrygL C μ t') :
    STLocalEntrygL C μ t :=
  StochDomAt.of_subset_union hs h0 h1 fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun n ω ⟨u, hu⟩ => by
    rcases hm n with h | h
    exacts [Or.inl ⟨u, by simpa [h] using hu⟩, Or.inr ⟨u, by simpa [h] using hu⟩]⟩

end Mix

/-! ## 3. The assembly over a carrier -/

/-- **The assembly**: every `0 ≤ t_n ≤ T0`: run the chain to `t'_n = t_n` if `t_n > 0`, `T0_n/2` if `t_n = 0`, and mix
with the zero sequence on the class `t_n = 0`.  No subsequence, no case split on `n` beyond the class
`t_n = 0`.  From the three hypotheses `STMainIndG`, `STHorizonG`, `STBaseG` and nothing else. -/
theorem stMLOutG_of_mainIndG (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hmain : STMainIndG d law Flow mk T0)
    (hhor : STHorizonG d Flow T0) (hbase : STBaseG d law Flow mk) : STMLOutG d law Flow mk T0 := by
  intro hd κ ε 𝔡 𝔠 hκ hε h𝔡 sz z hf t ht0 htT
  obtain ⟨hadm, hT, -⟩ := hhor κ ε 𝔠 𝔡 sz z hκ hε hf
  have hs : Tendsto sz.size atTop atTop := tendsto_natCast_atTop_iff.1 hadm.2.2.1
  set t' : ℕ → ℝ := fun n => if t n = 0 then T0 sz z n / 2 else t n with ht'
  have hpos : ∀ n, 0 < t' n := fun n => by
    by_cases h : t n = 0
    · simp only [ht', h, ite_true]; linarith [(hT n).1]
    · simp only [ht', h, ite_false]; exact lt_of_le_of_ne (ht0 n) (Ne.symm h)
  have hle : ∀ n, t' n ≤ T0 sz z n := fun n => by
    by_cases h : t n = 0
    · simp only [ht', h, ite_true]; linarith [(hT n).1]
    · simp only [ht', h, ite_false]; exact htT n
  have hm : ∀ n, t n = 0 ∨ t n = t' n := fun n => by
    by_cases h : t n = 0
    · exact Or.inl h
    · exact Or.inr (by simp only [ht', h, ite_false])
  have h1 := stPosConclG_of_mainIndG hmain hhor hbase hd κ ε 𝔡 𝔠 hκ hε h𝔡 sz z hf t' hpos hle
  have h0 := hbase hd κ ε 𝔡 𝔠 hκ hε h𝔡 sz z hf
  exact ⟨STLKgL_mix _ _ hs hm h0.1 h1.1, STLmaxgL_mix _ _ hs hm h0.2.1 h1.2.1,
    STDecaygL_mix _ _ hs hm h0.2.2.1 h1.2.2.1, STExp2gL_mix _ _ hs hm h0.2.2.2.1 h1.2.2.2.1,
    STLocalEntrygL_mix _ _ hs hm h0.2.2.2.2.1 h1.2.2.2.2.1⟩

end RBM.BA

/-! ## 4. The band output `UNMLOut` -/

namespace RBM.Univ

open RBM.BA

/-- `UNMLOut` is `STMLOutG` at the band data (`Iff.rfl`). -/
theorem unMLOut_iff (d : ℕ) : UNMLOut d ↔ STMLOutG d (fun sz => Sizes.seqP sz)
    (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := Iff.rfl

/-- **`UNMLOut` from `STMainInd`**: `∀ d, STMainInd d → UNMLOut d` with no further hypothesis (the base case is `stBase_band`,
the horizon `stHorizon_band`). -/
theorem unMLOut_of_mainInd (d : ℕ) (hmain : STMainInd d) : UNMLOut d :=
  (unMLOut_iff d).2 (stMLOutG_of_mainIndG d _ _ _ _ ((STMainInd_iff d).1 hmain) (stHorizon_band d) (stBase_band d))

end RBM.Univ

/-! ## 5. `STMainInd` and `UNMLOut` from the two light-weight estimates -/

namespace RBM.Gauss.Sizes

/-- **`STMainInd` from the two light-weight estimates** (`LWterm`, `LWtermExp`): `ST_mainInd_of_pins'` with every other
premise proved (`stDuhamelII_holds`). -/
theorem stMainInd_of_LW (d : ℕ) (hLW : LWterm d) (hLWE : LWtermExp d) : STMainInd d := fun hd =>
  have hEM : STEtermsMid d := stEtermsMid_of_LWT d (STLWT_of_LWtermExp hd hLWE)
  ST_mainInd_of_pins' d (ST_step2_of_pinsLW' hd (stNewKLK_holds d) hLWE (stEMn2Exp_holds d hd) (stGridRepN_holds d hd)
      (stOptL2_of_pins hd (STLWB_of_LWterm hd hLW) (stGridMart_holds d hd)) (stLocalAvgOfL2_holds hd))
    (stStep3RegIII_holds d) (stStep3RegI_holds d) (stStep3II_holds d)
    (ST_step5_caseI_of_pins hEM (stDuhamelI_holds d) (stIniTermI_holds d))
    (ST_step5_caseII_of_pins hEM (stDuhamelII_holds d) (stIniTermII_holds d) (stWardII_holds d))
    (stStep6I_holds d) (stStep6II_holds d) (stStep6III_holds d) hd

end RBM.Gauss.Sizes

namespace RBM.Univ

/-- **`UNMLOut` from the two light-weight estimates**: `unMLOut_of_mainInd` and `stMainInd_of_LW`. -/
theorem unMLOut_of_LW (d : ℕ) (hLW : LWterm d) (hLWE : LWtermExp d) : UNMLOut d :=
  unMLOut_of_mainInd d (stMainInd_of_LW d hLW hLWE)

end RBM.Univ
