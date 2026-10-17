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
# The block Anderson reading of the loop decay `lem_decayLoop`

Setting `(law, Flow, carrier, T0) = (seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`.
Every result is a composition of results of other files.

* `baDecayLoopU_of`: `stDecayLoopUgL_of_step2` at the BA carrier, with the far decay
  of `𝒦` closed by `baKcalDecay_holds`, the Ward pair `DecayGenTw_baWardPair`, `EMn2BA_mF_data` (`κm = κ`) and `t < 1`
  from `EMn2BA_T0_lt_one`.  It is the `hU` of `baEtermDecaygL` and conjunct 4 of `twSteps`.
* `baStep2Decay_holds`: `twSteps` conjuncts 1 and 4 at BA, from `baStep2_holds` and
  `baDecayLoopU_of`; inputs `BALWterm d`, `BALWtermExp d`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

open MeasureTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The loop decay at the BA carrier -/

/-- **`baDecayLoopU_of`** (Claim 4.5 `lem_decayLoop` uniformly in `u ∈ [s,t]`; for the block Anderson model, the proof of
Step 2 of Theorem 8.2 `lem:main_ind_BA`): `stDecayLoopUgL_of_step2` at
`baFMz sz z`, law `seqP (sz.withLam 0)`; `κm = κ` (`EMn2BA_mF_data`), `Admissible` from the flow, `t < 1` from
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

/-! ## 2. Step 2 with the loop decay -/

/-- **`baStep2Decay_holds`**: `twSteps` conjuncts 1 and 4 at BA in the frame of `STStep2G`, from
`baStep2_holds` and `baDecayLoopU_of`.  The constants `Cd, 𝔠d` come before `(𝔠, sz, z)`.  Inputs: `BALWterm d`, `BALWtermExp d`. -/
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

end RBM.BA

end
