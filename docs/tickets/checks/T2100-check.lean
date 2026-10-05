/-
Release check for T2100 (dispatcher V1, Sun Oct  4 01:13 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §15, §29).
Pinned `Prop`s of KL10: the probe pins `KLindStepAt`, `KLindStepPin` (`64b58eb:RBM3D/Probe/T2004Pins.lean`
lines 845–863), verbatim.  Namespace `RBM.Loop.T2100Check` here; KL10b proves the pin in `RBM.Loop`.
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2100-check.lean`.
-/
import RBM3D

#check @RBM.Loop.KLSigmaPi
#check @RBM.Loop.thetaEdge
#check @RBM.Loop.KLPar
#check @RBM.Loop.KLPT
#check @RBM.Loop.KLDecay
#check @RBM.Loop.KLShort
#check @RBM.Loop.KLDiffOne
#check @RBM.Loop.KLDiffTwo
#check @RBM.Loop.KLZero
#check @RBM.Loop.KLmolecule_holds
#check @RBM.Loop.KLsumZero_holds
#check @RBM.Loop.KLShort_holds
#check @RBM.Loop.inv_pow_pair_le
#check @RBM.Bparam
#check @RBM.norm_Theta_le
#check @RBM.mSigma

namespace RBM.Loop.T2100Check

open RBM RBM.Loop
open Finset

/-- **Route pin `(eq:ind-step-bound)`** (the new `d ≥ 3` estimate; properties 5, 5', 6, 7, 8 and
the two estimates of `KLsumZeroAt`), in the form the cut at an innermost long edge uses
(`RBM2D/Loop/KBoundCut.lean:1954` `Kpi_cut`, `innerId`): the root leaf `p` is long
(`σ_p ≠ σ_{p+1}`) and the other leaves carry `Θ^{(σ_i,σ_{i+1})}_t`;
`∑_{b} |∑_{δ_p = b} Σ^{(∅)}(t,σ,δ) ∏_{i≠p} Θ_{t,a_i δ_i}| ≺ B_{t,0}^{n-2}`.  (The paper's
`Θ̃_t ∈ {Θ_t, tS^{(B)}Θ_t^{(+,-)}}` is not needed: `tSΘ^{(+,-)} = Θ^{(+,-)} - I`, and the glued
edge is `ξ_J S_{uw}` times a standard leaf of the outer polygon.) -/
def KLindStepAt (d n : ℕ) [NeZero n] (κ gmax : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool) (r : Fin n),
    σ r ≠ σ (r + 1) → ∀ a : Fin n → Zd d p.L,
      ∑ b : Zd d p.L, ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d p.L => δ r = b),
          KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ *
            ∏ i ∈ Finset.univ.erase r,
              thetaEdge d p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) (a i) (δ i)‖
        ≤ C * (p.L : ℝ) ^ τ * (Bparam d p.L p.g p.t 0) ^ (n - 2)

def KLindStepPin : Prop :=
  ∀ (d n : ℕ) [NeZero n] (κ gmax : ℝ), 3 ≤ d → 3 ≤ n → 0 < κ → 0 < gmax → KLPT d κ gmax →
    KLindStepAt d n κ gmax

end RBM.Loop.T2100Check
