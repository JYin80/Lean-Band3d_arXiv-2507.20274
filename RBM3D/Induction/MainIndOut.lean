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
# ST-6 R3 (ticket T2340): from `lem:main_ind` to `UNMLOut` at every `0 ≤ t_n ≤ lemT z_n`

Design `docs/reports/T2338-design.md` §4-§6 (probe `RBM3D/Probe/T2338Pins.lean` on `t/T2338`, lines
69-76, 140-174, 289-313, 357-380).  Paper `1_2:1194-1243, 1309-1311`.

* `STMLOutG`: the output over a carrier `(law, Flow, mk, T0)` (`ML:GLoop`, `ML:GLoop_expec`,
  `ML:GtLocal`);
* `stMLOutG_of_mainIndG`: `STMainIndG` + `STHorizonG` (R2) + `STBaseG` (R1) give `STMLOutG`.  Run
  the chain (R2) to `t'_n = t_n` if `t_n > 0`, `T0_n/2` if `t_n = 0`, and mix with the zero
  sequence (R1) on the class `t_n = 0` (`StochDomAt.of_subset_union`: no subsequence, no pattern
  classes);
* `RBM.Univ.unMLOut_iff` (`Iff.rfl`: `UNMLOut` is `STMLOutG` at the band data),
  `unMLOut_of_mainInd` (`STMainInd d → UNMLOut d`, no further hypothesis), `unMLOutBA_of_pins`
  (instantiation at the block Anderson data; the three BA pins stay owed to BA-V);
* `RBM.Gauss.Sizes.stMainInd_of_LW`: `STMainInd` from the two owed LW pins `LWterm`, `LWtermExp`
  (every other premise of `ST_mainInd_of_pins'` is proved, `stDuhamelII_holds` since T2339), and
  `RBM.Univ.unMLOut_of_LW`.

Imports: the check file's, minus the transitive ones (`DuhamelI` through `DuhamelII`,
`Universality.Pins` through `BA.UNPins`, `AzumaProxyN` through `MainIndBase`) and `Main.FixedZ`
(not used).
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

open MeasureTheory Filter
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Ind

namespace RBM.BA

/-! ## 1. The pin -/

/-- **R3 (the ST-6 output)**: `ML:GLoop`, `ML:GLoop_expec`, `ML:GtLocal` at every `0 ≤ t_n ≤ T0`;
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

/-- **R3**: every `0 ≤ t_n ≤ T0`: run the chain to `t'_n = t_n` if `t_n > 0`, `T0_n/2` if `t_n = 0` (R2), and mix
with the zero sequence (R1) on the class `t_n = 0`.  No subsequence, no case split on `n` beyond the class
`t_n = 0`.  Over the three pins `STMainIndG`, `STHorizonG`, `STBaseG` and nothing else. -/
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

/-! ## 4. The band output `UNMLOut` and the block Anderson output `UNMLOutBA` -/

namespace RBM.Univ

open RBM.BA

/-- `UNMLOut` is `STMLOutG` at the band data (`Iff.rfl`). -/
theorem unMLOut_iff (d : ℕ) : UNMLOut d ↔ STMLOutG d (fun sz => Sizes.seqP sz)
    (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := Iff.rfl

/-- **The ST-6 output**: `∀ d, STMainInd d → UNMLOut d` with no further hypothesis (the base case is `stBase_band`,
the horizon `stHorizon_band`). -/
theorem unMLOut_of_mainInd (d : ℕ) (hmain : STMainInd d) : UNMLOut d :=
  (unMLOut_iff d).2 (stMLOutG_of_mainIndG d _ _ _ _ ((STMainInd_iff d).1 hmain) (stHorizon_band d) (stBase_band d))

/-- **Route G**: `UNMLOutBA` is `STMLOutG` at the block Anderson data (`Iff.rfl`); it follows from the BA instances
of the three pins (owed to BA-V). -/
theorem unMLOutBA_of_pins (d : ℕ)
    (hmain : STMainIndG d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0)
    (hhor : STHorizonG d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) BAflowT0)
    (hbase : STBaseG d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz) :
    UNMLOutBA d := stMLOutG_of_mainIndG d _ _ _ _ hmain hhor hbase

end RBM.Univ

/-! ## 5. `STMainInd` from the two owed LW pins, and the ST-6 output from them -/

namespace RBM.Gauss.Sizes

/-- **`STMainInd` from the two owed LW pins** (`LWterm`, `LWtermExp`: LW-01): `ST_mainInd_of_pins'` with every other
premise proved on `main` (`stDuhamelII_holds` since T2339). -/
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

/-- **The ST-6 output from the two owed LW pins**: `unMLOut_of_mainInd` and `stMainInd_of_LW`. -/
theorem unMLOut_of_LW (d : ℕ) (hLW : LWterm d) (hLWE : LWtermExp d) : UNMLOut d :=
  unMLOut_of_mainInd d (stMainInd_of_LW d hLW hLWE)

end RBM.Univ

/-! ## 6. Compiled nonempty instances (`d = 3`, merged data `sz0`, `z0`, `zSeq`) -/

namespace RBM.Gauss.MainIndInst

open RBM.BA RBM.BA.FlowPinsInst RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst

/-- `stMLOutG_of_mainIndG` at the band data and the time sequence `t ≡ 0`, the class `t_n = 0` that the mixing
handles (`t'_n = lemT z_n/2`): the six conclusions are the base case (R1) mixed with the chain to `t'` (R2).  The pin
`STMainInd 3` (`lem:main_ind`, owed) is a hypothesis; `STHorizonG` and `STBaseG` are proved. -/
example (hmain : STMainInd 3) : STLKgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) (fun _ => 0) ∧
    STLmaxgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) (fun _ => 0) ∧
    STDecaygL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) (fun _ => 0) ∧
    STExp2gL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) (fun _ => 0) ∧
    STLocalEntrygL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) (fun _ => 0) :=
  stMLOutG_of_mainIndG 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) ((STMainInd_iff 3).1 hmain) (stHorizon_band 3)
    (stBase_band 3) (by norm_num) (1 / 10) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 z0
    flow_z0 _ (fun _ => le_rfl) (fun n => (lemT_pos (z0_im_pos n)).le)

/-- `unMLOut_of_mainInd` at `sz0`, `z0`, `t = lemT z/2`: with the one hypothesis `STMainInd 3` (`lem:main_ind`, owed),
`STLK`. -/
example (hmain : STMainInd 3) : sz0.STLK (STflowE z0) (fun n => lemT (z0 n) / 2) :=
  (RBM.Univ.unMLOut_of_mainInd 3 hmain (by norm_num) (1 / 10) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num)
    (by norm_num) sz0 z0 flow_z0 _ (fun n => (half_pos (lemT_pos (z0_im_pos n))).le)
    (fun n => by linarith [lemT_pos (z0_im_pos n)])).1

/-- `unMLOutBA_of_pins` at the block Anderson data `sz0`, `zSeq` (`BAFlow` by `flow_sz0`, `t_n = 1/2 ≤ 2/3 ≤ t₀_n` by
`t0_sz0`): the three BA pins (`STMainIndG`, `STHorizonG`, `STBaseG` at the BA data, owed to BA-V) are hypotheses. -/
example
    (hmain : STMainIndG 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0)
    (hhor : STHorizonG 3 (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) BAflowT0)
    (hbase : STBaseG 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz) :
    STLKgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) :=
  (RBM.Univ.unMLOutBA_of_pins 3 hmain hhor hbase (by norm_num) (1 / 2) (1 / 10) (1 / 10) (1 / 6) (by norm_num)
    (by norm_num) (by norm_num) sz0 zSeq flow_sz0 _ (fun _ => by norm_num)
    (fun n => (by norm_num : (1 / 2 : ℝ) ≤ 2 / 3).trans (t0_sz0 n))).1

/-- `stMainInd_of_LW` and `unMLOut_of_LW` at `sz0`, `z0`, `t = lemT z/2`: the two owed LW pins (`LWterm 3`, `LWtermExp 3`,
LW-01) are the only hypotheses. -/
example (hLW : LWterm 3) (hLWE : LWtermExp 3) : STMainInd 3 := stMainInd_of_LW 3 hLW hLWE

example (hLW : LWterm 3) (hLWE : LWtermExp 3) : sz0.STLK (STflowE z0) (fun n => lemT (z0 n) / 2) :=
  (RBM.Univ.unMLOut_of_LW 3 hLW hLWE (by norm_num) (1 / 10) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num)
    (by norm_num) sz0 z0 flow_z0 _ (fun n => (half_pos (lemT_pos (z0_im_pos n))).le)
    (fun n => by linarith [lemT_pos (z0_im_pos n)])).1

end RBM.Gauss.MainIndInst
