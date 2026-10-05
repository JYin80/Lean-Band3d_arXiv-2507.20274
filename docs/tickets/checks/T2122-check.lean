/-
Release check for T2122 (dispatcher V1, Sun Oct  4 07:07 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §15, §29).
Pinned `Prop`s of KL12: the probe pins `KLwardIneqAt`, `KLwardIneqPin` (`64b58eb:RBM3D/Probe/T2004Pins.lean`
lines 786-798), verbatim.  Namespace `RBM.Loop.T2122Check` here; KL12 (T2122) defines them in `RBM.Loop` and
proves `KLwardIneqPin`.  The `#check`s are the merged names KL12 builds on (KL1, KL10, KL11; `STKward` of S3-01).
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2122-check.lean`.
-/
import RBM3D

#check @RBM.Loop.KLK
#check @RBM.Loop.KLKpi
#check @RBM.Loop.KLK_eq_sum_Kpi
#check @RBM.Loop.KLPar
#check @RBM.Loop.KLPT
#check @RBM.Loop.KLindStepPin_holds
#check @RBM.Loop.KLboundPin_holds
#check @RBM.Loop.KLKpiBoundPin_holds
#check @RBM.Loop.KLKpi_cut
#check @RBM.Loop.KLKpi_step
#check @RBM.Loop.KLInduct_Kpi_empty_bound
#check @RBM.Gauss.Sizes.STKward
#check @RBM.Bparam
#check @RBM.Gauss.etaT

namespace RBM.Loop.T2122Check

open RBM RBM.Loop
open Finset

/-- **Pin `lem_wardineq_K`, `(wardineq_K)`** (consumer: `lem:SEforLn`): for `n ≥ 2`,
`max_σ ∑_{a_n} |𝒦^{(n)}_{t,σ,a}| ≺ (W^d η_t)⁻¹ (W^{-d} B_{t,0})^{n-2}`. -/
def KLwardIneqAt (d n : ℕ) (κ gmax : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool)
    (a : Fin (n - 1) → Zd d p.L),
    ∑ x : Zd d p.L, ‖KLK d p.L p.g p.W p.E p.t ⟨List.ofFn σ, List.ofFn a ++ [x]⟩‖
      ≤ C * (p.L : ℝ) ^ τ * (((p.W : ℝ) ^ d) * Gauss.etaT p.E p.t)⁻¹
          * (((p.W : ℝ) ^ d)⁻¹ * Bparam d p.L p.g p.t 0) ^ (n - 2)

def KLwardIneqPin : Prop :=
  ∀ (d n : ℕ) (κ gmax : ℝ), 3 ≤ d → 2 ≤ n → 0 < κ → 0 < gmax → KLPT d κ gmax →
    KLwardIneqAt d n κ gmax


end RBM.Loop.T2122Check
