/-
Release check for T2106 (dispatcher V1, Sun Oct  4 03:16 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §15, §29).
Pinned `Prop`s of KL10: the probe pins `KLindStepAt`, `KLindStepPin` (`64b58eb:RBM3D/Probe/T2004Pins.lean`
lines 845–863), verbatim.  Namespace `RBM.Loop.T2106Check` here; KL10b (T2106) defines both in `RBM.Loop`
verbatim and proves `KLindStepPin`.  The `#check`s are the merged KL10a interface (T2100, c4c1f80).
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2106-check.lean`.
-/
import RBM3D

#check @RBM.Loop.KLSigmaPi
#check @RBM.Loop.thetaEdge
#check @RBM.Loop.KLPar
#check @RBM.Loop.KLPT
#check @RBM.Loop.KLShort_holds
#check @RBM.Loop.KLmaxDist
#check @RBM.Loop.KLsigAlt
#check @RBM.Bparam
#check @RBM.mSigma
#check @RBM.Loop.KLf0
#check @RBM.Loop.KLf1
#check @RBM.Loop.KLf2
#check @RBM.Loop.KLf_split
#check @RBM.Loop.KLf0_bound
#check @RBM.Loop.KLf_crude_bound
#check @RBM.Loop.KLf12_bound
#check @RBM.Loop.KLSigmaPi_reflect
#check @RBM.Loop.KLslice_f1_vanish
#check @RBM.Loop.KLsumZero_weighted
#check @RBM.Loop.KLIndStepA_sumZero_signed
#check @RBM.Loop.KLindStep_nonAlt
#check @RBM.Loop.KLlat_pow_dim_rpow
#check @RBM.Loop.KLlat_pair_rpow
#check @RBM.Loop.KLlat_inv_le_Bparam
#check @RBM.Loop.KLlat_sum_norm_Theta_row_le
#check @RBM.Loop.KLIndStepA_alt_cases
#check @RBM.Loop.KLIndStepA_dist_le_maxDist
#check @RBM.Loop.KLIndStepA_thetaEdge_long

namespace RBM.Loop.T2106Check

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

end RBM.Loop.T2106Check
