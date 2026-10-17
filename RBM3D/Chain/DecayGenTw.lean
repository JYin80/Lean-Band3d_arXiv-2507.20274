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

/-! ## 3. Target 13: target 6 at the BA carrier -/

end RBM.BA

end
