/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.DecayGen
import RBM3D.BA.TwistPins
import RBM3D.BA.Step2BA
import RBM3D.BA.EMn2BA

/-!
# The BA readings of `Chain/DecayGen` and the TLF-C5 examples (BA-T row T7a leaf, ticket T2454)

A leaf (no module imports it): it may import `BA/`, while `Chain/DecayGen.lean` may not.

* `DecayGenTw_baWardPair` (F4 at BA): `DecayGen_WardPair (baFM sz lam0 E)`, from `DecayGen_ward`
  at `H = seqHflowBA` (`EMn2BA_seqHflowBA_herm`, `BA/EMn2BA.lean:68`), `z = ztOf`,
  `η = etaOf = Im ztOf` (`ztOf_im`).  F3 at BA is `EMn2BA_mF_data` (`BA/EMn2BA.lean:125`), F1-F2
  are `BAFlow`, `EMn2BA_T0_lt_one`.
* **TLF-C5 (target 12).** `twSteps` (`BA/TwistPins.lean:133`) is `STStep2ConclgL ∧ (conjunct 2) ∧
  (conjunct 3) ∧ STDecayLoopUgL`: the first `example` is `Iff.rfl` (supervisor
  `2026-10-11-1049.md:123-127`), the second extracts conjunct 4 from `twSteps` (`h.2.2.2`).
* **Target 13.** Target 6 (`stDecayLoopUgL_of_step2`) elaborated at the BA carrier `baFMz sz z`
  with the law `seqP (sz.withLam 0)`; open: F5 (`STKcalDecaygL`, U2-BA's `BAKcalDecay`) and the
  Step 2 decay `STGdecayWgL` (T1-BA).  The band instances (`d = 3`, `sz0`) are in
  `Chain/DecayGen.lean`, section 5.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

open MeasureTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. F4 at BA -/

/-- **F4 at BA** (`DecayGen_WardPair`): `H = seqHflowBA` (`EMn2BA_seqHflowBA_herm`), `z = ztOf`, `η = etaOf = Im ztOf`
(`ztOf_im`). -/
theorem DecayGenTw_baWardPair {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) : DecayGen_WardPair (baFM sz lam0 E) := by
  intro n k hk σ a
  obtain ⟨c, hc1, hc2⟩ := DecayGen_ward (d := d) (L := sz.L n) (W := sz.W n) hk σ a
  exact ⟨c, hc1, fun u ω hη => hc2 _ (ztOf (BAmF sz lam0 E n) (E n) u) (etaOf (BAmF sz lam0 E n) u)
    (EMn2BA_seqHflowBA_herm sz lam0 n u ω) hη (by rw [ztOf_im]; exact le_abs_self _)⟩

/-! ## 2. Target 12 (TLF-C5): `twSteps` and `STDecayLoopUgL` -/

/-- `twSteps` is definitionally `STStep2ConclgL ∧ (conjunct 2) ∧ (conjunct 3) ∧ STDecayLoopUgL` (conjuncts 2-3 verbatim from
`BA/TwistPins.lean:136-138`). -/
example {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) (Cd : ℝ) :
    twSteps C μ s t Cd ↔ (STStep2ConclgL C μ s t Cd ∧
      (∀ k : ℕ, 1 ≤ k → PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (k - 1))) ∧
      (∀ k : ℕ, 1 ≤ k → PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1 p.2.2‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ k)) ∧
      STDecayLoopUgL C μ s t) := Iff.rfl

/-- Conjunct 4 of `twSteps` is `STDecayLoopUgL`. -/
example {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) (Cd : ℝ) (h : twSteps C μ s t Cd) :
    STDecayLoopUgL C μ s t := h.2.2.2

/-! ## 3. Target 13: target 6 at the BA carrier -/

/-- **Target 6 at the BA carrier** `baFMz sz z`, law `seqP (sz.withLam 0)`, statement level: F3 from `EMn2BA_mF_data`, F1-F2 from
`BAFlow` (`EMn2BA_T0_lt_one`), F4 from `DecayGenTw_baWardPair`; open: F5 (`STKcalDecaygL`, U2-BA's `BAKcalDecay`) and the Step 2 decay
`STGdecayWgL` (T1-BA). -/
example {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ) (h : BAFlow sz κ ε 𝔠 𝔡 z)
    {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (ht : ∀ n, t n ≤ BAflowT0 sz z n) (Cd : ℝ) (hK : STKcalDecaygL (baFMz sz z))
    (hG : STGdecayWgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd) :
    STDecayLoopUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t :=
  stDecayLoopUgL_of_step2 hd sz _ _ κ 𝔠 𝔡 s t Cd ⟨hκ, fun n => (EMn2BA_mF_data sz h n).1, fun n t => rfl⟩ h.1 hs
    (fun n => (ht n).trans_lt (EMn2BA_T0_lt_one hκ sz h n)) (DecayGenTw_baWardPair sz _ _) hK hG

end RBM.BA

end
