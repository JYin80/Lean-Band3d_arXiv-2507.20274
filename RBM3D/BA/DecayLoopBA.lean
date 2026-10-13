/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.DecayGenTw
import RBM3D.Chain.Step2EventsGenTw
import RBM3D.BA.KDecayBA
import RBM3D.BA.Step2CloseBA
import RBM3D.BA.NetLiftBA
import RBM3D.BA.SEforLnBA

/-!
# The BA readings of the loop decay `lem_decayLoop` (BA-T row T7-BA, ticket T2495)

Check file `docs/tickets/checks/T2495-check.lean`.  Setting `(law, Flow, carrier, T0) = (seqP
(sz.withLam 0), BAFlow, baFMz, BAflowT0)`.
A leaf: no merged file is edited, and no module imports it.  Every result is a composition of
merged results.

* **Target 1** `baDecayLoopU_of`: `stDecayLoopUgL_of_step2` at the BA carrier, with the far decay
  of `𝒦` closed by `baKcalDecay_holds`
  (U2-BA), the Ward pair `DecayGenTw_baWardPair` (T7a), F3 `EMn2BA_mF_data` (`κm = κ`) and `t < 1`
  from `EMn2BA_T0_lt_one`.  It is the `hU` of
  `baEtermDecaygL` (`Step2EventsGenTw_toFlowFM` is `rfl`) and conjunct 4 of `twSteps`.
* **Target 2** `baFlow_sizeInv_le` (the eventual range `N⁻¹ ≤ 1 - t`, from `baFlow_premises`) and
  `baDecayLoopPT_of` (the per-time form
  through `stDecayLoopPTgL_of_step2`; the private helper `DecayLoopBA_PT_of_U` reads `STGdecayWgL`
  per time through
  `RBM.Path.perTimeOfStochDomAt`).
* **Target 3** `baDecayLoopAt_holds`: the merged pin `STDecayLoopAtgL` at `baFMz sz z` along every
  BA flow.
* **Target 4** `baStep2Decay_holds`: `twSteps` conjuncts 1 and 4 at BA, from `baStep2_holds` and
  target 1; inputs `BALWterm d`,
  `BALWtermExp d` (stage L, exact type).
* **Target 5** `baSTLWB_of`, `baSTLWT_of`: the L-bridges `stLWBgL_of_LWtermG`,
  `stLWTgL_of_LWtermExpG` at BA (F1 `BAFlow`, F7
  `Step2EventsGenTw_baRot3`).  They close the notes "owed: T1-BA / T7-BA" of `BASTLWB`, `BASTLWT`
  (`BA/LWPinsBA.lean`).
* **Target 6**: compiled nonempty instances at `d = 3`, `sz0`, `zSeq`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

open MeasureTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Targets 1-3: the loop decay at the BA carrier -/

/-- **Target 1, `baDecayLoopU_of`** (`lem_decayLoop` uniformly in `u ∈ [s,t]`, `3_5:1126`; BA `7_8:1994`): `stDecayLoopUgL_of_step2` at
`baFMz sz z`, law `seqP (sz.withLam 0)`; F3 inline (`κm = κ`, `EMn2BA_mF_data`), `Admissible` from the flow, `t < 1` from
`EMn2BA_T0_lt_one`, the Ward pair `DecayGenTw_baWardPair`, the far decay of `𝒦` from `baKcalDecay_holds`.  Only the Step 2 decay
`STGdecayWgL` stays an input. -/
theorem baDecayLoopU_of (d : ℕ) :
    3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ (s t : ℕ → ℝ) (Cd : ℝ), (∀ n, 0 ≤ s n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        STGdecayWgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd →
          STDecayLoopUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t := by
  intro hd sz κ ε 𝔠 𝔡 z hκ hflow s t Cd hs ht hG
  exact stDecayLoopUgL_of_step2 hd sz _ _ κ 𝔠 𝔡 s t Cd ⟨hκ, fun n => (EMn2BA_mF_data sz hflow n).1, fun n t => rfl⟩ hflow.1 hs
    (fun n => (ht n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)) (DecayGenTw_baWardPair sz _ _)
    (baKcalDecay_holds d hd sz κ ε 𝔠 𝔡 z hκ hflow) hG

/-- **Target 2 (a), `baFlow_sizeInv_le`**: the eventual range `N⁻¹ ≤ 1 - t_n` below the BA horizon, from `baFlow_premises`
(`RangeCond (ε/2) t`) and `N^{-1} ≤ N^{-1+ε/2}`. -/
theorem baFlow_sizeInv_le (d : ℕ) :
    ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, t n ≤ BAflowT0 sz z n) → ∀ᶠ n in atTop, (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - t n := by
  intro sz κ ε 𝔠 𝔡 z hκ hε hflow t ht
  have hr : sz.RangeCond (ε / 2) t := (baFlow_premises d κ ε 𝔠 𝔡 hκ hε sz z hflow t ht).2
  filter_upwards [hr] with n hn
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have h1 : ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  rw [Real.rpow_neg_one] at h1
  exact h1.trans hn

/-- The uniform Step 2 decay gives the per-time one (`perTimeOfStochDomAt`), at every carrier and law (finding G4). -/
private theorem DecayLoopBA_PT_of_U {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) (Cd : ℝ)
    (h : STGdecayWgL C μ s t Cd) : STStep2DecayPTgL C μ Cd s t :=
  fun D hD => perTimeOfStochDomAt μ sz.size _ _ (h D hD)

/-- **Target 2 (b), `baDecayLoopPT_of`** (the BA twin of T7a target 5): `stDecayLoopPTgL_of_step2` at the BA setting, `hrange` from
target 2 (a); the per-time Step 2 decay `STStep2DecayPTgL` stays an input. -/
theorem baDecayLoopPT_of (d : ℕ) :
    3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ (s t : ℕ → ℝ) (Cd : ℝ), (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        STStep2DecayPTgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) Cd s t →
          STDecayLoopPTgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t := by
  intro hd sz κ ε 𝔠 𝔡 z hκ hε hflow s t Cd hs hst ht hD
  exact stDecayLoopPTgL_of_step2 hd sz _ _ κ 𝔠 𝔡 s t Cd ⟨hκ, fun n => (EMn2BA_mF_data sz hflow n).1, fun n t => rfl⟩ hflow.1 hs hst
    (fun n => (ht n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)) (baFlow_sizeInv_le d sz κ ε 𝔠 𝔡 z hκ hε hflow t ht)
    (DecayGenTw_baWardPair sz _ _) (baKcalDecay_holds d hd sz κ ε 𝔠 𝔡 z hκ hflow) hD

/-- **Target 3, `baDecayLoopAt_holds`** (the BA twin of T7a target 4, single time): the merged pin `STDecayLoopAtgL` at `baFMz sz z`
along every BA flow, with `κm = κ`; its own premises (`DecayGen_Spec`, `Admissible`, the time window, the prefactor, the decay input)
stay inside the merged body. -/
theorem baDecayLoopAt_holds (d : ℕ) :
    3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ (C₀ : ℝ) (u P : ℕ → ℝ), STDecayLoopAtgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) κ 𝔠 𝔡 C₀ u P := by
  intro hd sz κ ε 𝔠 𝔡 z hκ hflow C₀ u P
  exact stDecayLoopAtgL_of hd sz _ _ (DecayGenTw_baWardPair sz _ _) (baKcalDecay_holds d hd sz κ ε 𝔠 𝔡 z hκ hflow) κ 𝔠 𝔡 C₀ u P

/-! ## 2. Target 4: Step 2 with the loop decay -/

/-- **Target 4, `baStep2Decay_holds`**: `twSteps` conjuncts 1 and 4 at BA in the frame of `STStep2G` (`Chain/Step2Gen.lean:591`), from
`baStep2_holds` and target 1.  The constants `Cd, 𝔠d` come before `(𝔠, sz, z)`.  Inputs: the two stage-L pins (exact type). -/
theorem baStep2Decay_holds (d : ℕ) :
    BALWterm d → BALWtermExp d → 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
      ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
          ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ BAflowT0 sz z n) → (∀ n, s n < t n) →
            (∀ n, t n ≤ BAflowT0 sz z n) →
            STLKgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s → STDecaygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s →
            STConStInd sz 𝔠d s t →
            STStep1LoopgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t →
            STStep1WeakgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t →
              STStep2ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd ∧
                STDecayLoopUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t := by
  intro hLW hLWE hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨Cd, hCd, 𝔠d, h𝔠d, h1, H⟩ := baStep2_holds d hLW hLWE hd κ ε 𝔡 hκ hε h𝔡
  refine ⟨Cd, hCd, 𝔠d, h𝔠d, h1, fun 𝔠 sz z hflow s t hs hsT hst htT hLK hDec hCon hS1L hS1W => ?_⟩
  have h := H 𝔠 sz z hflow s t hs hsT hst htT hLK hDec hCon hS1L hS1W
  exact ⟨h, baDecayLoopU_of d hd sz κ ε 𝔠 𝔡 z hκ hflow s t Cd hs htT h.2.2⟩

/-! ## 3. Target 5: the L-bridges at BA -/

/-- **Target 5, `baSTLWB_of`**: the generic L-bridge `stLWBgL_of_LWtermG` at BA (F1 `BAFlow`, F7 `Step2EventsGenTw_baRot3`), every `d`. -/
theorem baSTLWB_of (d : ℕ) : 3 ≤ d → BALWterm d → BASTLWB d := fun hd h =>
  stLWBgL_of_LWtermG d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) BAflowT0 baFMz hd
    (fun _ _ _ _ _ _ h => h.1) (fun sz z => Step2EventsGenTw_baRot3 sz _ _) h

/-- **Target 5, `baSTLWT_of`**: the generic L-bridge `stLWTgL_of_LWtermExpG` at BA, every `d`. -/
theorem baSTLWT_of (d : ℕ) : 3 ≤ d → BALWtermExp d → BASTLWT d := fun hd h =>
  stLWTgL_of_LWtermExpG d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) BAflowT0 baFMz hd
    (fun _ _ _ _ _ _ h => h.1) (fun sz z => Step2EventsGenTw_baRot3 sz _ _) h

/-! ## 4. Target 6: compiled nonempty instances (`d = 3`)

Data: `sz0`, `zSeq`, `flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq` (`BA/FlowPins.lean:1214`), `s ≡ 1/10 < t ≡ 1/2 < t₀`
(`half_lt_t0`).  The Step 2 decays (`STGdecayWgL`, `STStep2DecayPTgL`; other gates' outputs), the stage-L pins `BALWterm 3`,
`BALWtermExp 3` and the `STStep2G` binders stay hypotheses; every deterministic premise is discharged. -/

section Instances

open RBM.Gauss.SizesInst RBM.BA.FlowPinsInst

local notation "μ0" => Sizes.seqP (sz0.withLam 0)

/-- Target 1 at the data. -/
example (Cd : ℝ) (hG : STGdecayWgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) (fun _ => 1 / 2) Cd) :
    STDecayLoopUgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) (fun _ => 1 / 2) :=
  baDecayLoopU_of 3 le_rfl sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq (by norm_num) flow_sz0 _ _ Cd (fun _ => by norm_num)
    (fun n => (half_lt_t0 n).le) hG

/-- Target 2 (a) at the data: the range holds from `n = 0` on, here in the form `∀ᶠ`. -/
example : ∀ᶠ n in atTop, (((sz0.size n : ℕ) : ℝ))⁻¹ ≤ 1 - (1 / 2 : ℝ) :=
  baFlow_sizeInv_le 3 sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq (by norm_num) (by norm_num) flow_sz0 (fun _ => 1 / 2)
    (fun n => (half_lt_t0 n).le)

/-- Target 2 (b) at the data, the per-time input from the uniform one (finding G4). -/
example (Cd : ℝ) (hG : STGdecayWgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) (fun _ => 1 / 2) Cd) :
    STDecayLoopPTgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) (fun _ => 1 / 2) :=
  baDecayLoopPT_of 3 le_rfl sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq (by norm_num) (by norm_num) flow_sz0 _ _ Cd
    (fun _ => by norm_num) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le)
    (DecayLoopBA_PT_of_U (baFMz sz0 zSeq) μ0 _ _ Cd hG)

/-- Target 3 at the data (`u ≡ 1/2`, `ℓ_u = 1`, `P ≡ 1`, `C₀ = 0`, `k = 3`, `τ' = 1/10`, `D' = 1`): every premise of the pin but the decay input of
the `(+,-)` 2-loops is discharged. -/
example (hdec : ∀ D : ℝ, 0 < D →
      PrecPTL sz0 μ0 (U := fun n => Unit × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
        (fun n p ω => ‖(baFMz sz0 zSeq).L n (1 / 2) p.2.1 p.2.2 ω - (baFMz sz0 zSeq).K n (1 / 2) p.2.1 p.2.2‖)
        (fun n p _ => 1 * STWB sz0 n (1 / 2) (zdistInf 3 (sz0.L n) (p.2.2 0 - p.2.2 1)) *
            Real.exp (-(((zdistInf 3 (sz0.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) / ellT (sz0.L n) (sz0.lam n) (1 / 2)) ^ (1 / 2 : ℝ)) +
          ((sz0.W n : ℕ) : ℝ) ^ (-D))) :
    PrecPTL sz0 μ0 (U := fun n => Unit × (Fin 3 → Bool) × (Fin 3 → Zd 3 (sz0.L n)))
      (fun n p ω => (‖(baFMz sz0 zSeq).L n (1 / 2) p.2.1 p.2.2 ω‖ +
          ‖(baFMz sz0 zSeq).L n (1 / 2) p.2.1 p.2.2 ω - (baFMz sz0 zSeq).K n (1 / 2) p.2.1 p.2.2‖) *
        (if ellT (sz0.L n) (sz0.lam n) (1 / 2) * ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ (STdiamInf p.2.2 : ℝ) then 1 else 0))
      (fun n _ _ => ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) :=
  baDecayLoopAt_holds 3 le_rfl sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq (by norm_num) flow_sz0 0 (fun _ => 1 / 2) (fun _ => 1)
    ⟨by norm_num, fun n => (EMn2BA_mF_data sz0 flow_sz0 n).1, fun n t => rfl⟩ flow_sz0.1 (fun _ => by norm_num)
    (fun _ => by norm_num) (Filter.Eventually.of_forall fun n => ⟨le_rfl, by simp⟩) hdec 3 (by norm_num) (1 / 10) (by norm_num) 1
    (by norm_num)

/-- Target 4 at the data: constants first, then the conclusion under the binders of the frame; the stage-L pins stay hypotheses. -/
example (hLW : BALWterm 3) (hLWE : BALWtermExp 3) : ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
    (STLKgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) → STDecaygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) →
      STConStInd sz0 𝔠d (fun _ => 1 / 10) (fun _ => 1 / 2) →
      STStep1LoopgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) (fun _ => 1 / 2) →
      STStep1WeakgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) (fun _ => 1 / 2) →
        STStep2ConclgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) (fun _ => 1 / 2) Cd ∧
          STDecayLoopUgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) (fun _ => 1 / 2)) := by
  obtain ⟨Cd, hCd, 𝔠d, h𝔠d, h𝔠d1, h⟩ := baStep2Decay_holds 3 hLW hLWE le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num)
  exact ⟨Cd, hCd, 𝔠d, h𝔠d, h𝔠d1, h (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 10) (fun _ => 1 / 2) (fun _ => by norm_num)
    (fun n => by have := half_lt_t0 n; change (1 / 10 : ℝ) ≤ BAflowT0 sz0 zSeq n; linarith) (fun _ => by norm_num)
    (fun n => (half_lt_t0 n).le)⟩

/-- Target 5 at `d = 3`. -/
example (h : BALWterm 3) : BASTLWB 3 := baSTLWB_of 3 le_rfl h

example (h : BALWtermExp 3) : BASTLWT 3 := baSTLWT_of 3 le_rfl h

/-- Closing the `hU` of `baEtermDecaygL` (`BA/SEforLnBA.lean:274`) by target 1 at the data (finding G3: the carrier text is the same
by `Step2EventsGenTw_toFlowFM`, `rfl`). -/
example (Cd : ℝ) (hG : STGdecayWgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) (fun _ => 1 / 2) Cd) :
    ∀ k : ℕ, 2 ≤ k → ∀ σ : Fin k → Bool, True := by
  have h := baEtermDecaygL 3 le_rfl sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq (by norm_num) flow_sz0 (fun _ => 1 / 10)
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
    (baDecayLoopU_of 3 le_rfl sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq (by norm_num) flow_sz0 _ _ Cd (fun _ => by norm_num)
      (fun n => (half_lt_t0 n).le) hG)
  exact fun _ _ _ => trivial

/-- The far set of target 1 is nonempty (`k = 3`, `τ = 1/20`, `u = 0`, `inst_baKcalDecay_far`): the far decay of `𝒦` used in target 1 has content. -/
example := KDecayBAInst.inst_baKcalDecay_far

end Instances

end RBM.BA

end
