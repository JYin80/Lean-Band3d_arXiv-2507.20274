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
# The Ward-pair hypothesis of `Chain/DecayGen` at the block Anderson carrier

`DecayGenTw_baWardPair` is `DecayGen_WardPair (baFM sz lam0 E)`.  It follows from `DecayGen_ward`
for the Hermitian matrix `seqHflowBA` (`EMn2BA_seqHflowBA_herm`), the spectral parameter `ztOf`
and `η = etaOf = Im ztOf` (`ztOf_im`).
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

open MeasureTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The Ward pair at the block Anderson carrier -/

/-- The Ward-pair statement `DecayGen_WardPair` at `baFM sz lam0 E`: `H = seqHflowBA` (`EMn2BA_seqHflowBA_herm`),
`z = ztOf` and `η = etaOf = Im ztOf` (`ztOf_im`). -/
theorem DecayGenTw_baWardPair {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) : DecayGen_WardPair (baFM sz lam0 E) := by
  intro n k hk σ a
  obtain ⟨c, hc1, hc2⟩ := DecayGen_ward (d := d) (L := sz.L n) (W := sz.W n) hk σ a
  exact ⟨c, hc1, fun u ω hη => hc2 _ (ztOf (BAmF sz lam0 E n) (E n) u) (etaOf (BAmF sz lam0 E n) u)
    (EMn2BA_seqHflowBA_herm sz lam0 n u ω) hη (by rw [ztOf_im]; exact le_abs_self _)⟩

end RBM.BA

end
