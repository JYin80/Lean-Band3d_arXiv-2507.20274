/-
Release check for T2036 (dispatcher V1, Sat Oct  3 05:44 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §15).
Pinned `Prop` of KL6: the probe pin `KLwardPin` (`64b58eb:RBM3D/Probe/T2004Pins.lean` lines 770–779),
verbatim.  Namespace `RBM.Loop.T2036Check` here; the theorem goes to `RBM.Loop`.
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2036-check.lean`.
-/
import RBM3D

#check @RBM.Loop.KLK
#check @RBM.Loop.KLK_isKLoop
#check @RBM.Loop.KLK_unique
#check @RBM.Loop.KLK_rotate
#check @RBM.Loop.KLK_translate
#check @RBM.Loop.IsKLoop
#check @RBM.Loop.LoopIdx
#check @RBM.Gauss.etaT
#check @RBM.mSigma

namespace RBM.Loop.T2036Check

open RBM RBM.Loop
open Finset

/-- **Pin `lem_WI_K`, `(WI_calK)`**, `σ₁ = -σ_n`, `η_t = (1-t) Im m(E)` of `(eta)`:
`∑_{a_n} 𝒦^{(n)}_{t,σ,a} = (2 i W^d η_t)⁻¹ (𝒦^{(n-1)}_{t,(+,σ₂..σ_{n-1}),â} - 𝒦^{(n-1)}_{t,(-,σ₂..σ_{n-1}),â})`.
Here `σ = (s, μ, -s)`, `n = μ.length + 2 ≥ 2`. -/
def KLwardPin : Prop :=
  ∀ (d L W : ℕ) [NeZero L] (g E : ℝ), 3 ≤ L → 1 ≤ W → |E| < 2 → ∀ t : ℝ, 0 ≤ t → t < 1 →
    ∀ (s : Bool) (μ : List Bool) (a : List (Zd d L)), a.length = μ.length + 1 →
      ∑ x : Zd d L, KLK d L g W E t ⟨s :: μ ++ [!s], a ++ [x]⟩
        = (2 * Complex.I * (W : ℂ) ^ d * (Gauss.etaT E t : ℂ))⁻¹ *
            (KLK d L g W E t ⟨true :: μ, a⟩ - KLK d L g W E t ⟨false :: μ, a⟩)


end RBM.Loop.T2036Check
