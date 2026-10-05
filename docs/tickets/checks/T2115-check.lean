/-
Release check for T2115 (dispatcher V1, Sun Oct  4 05:50 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §15, §29).
Pinned `Prop`s of KL11: the probe pins `KLBoundAt`, `KLboundPin`, `KLKpiBoundAt`, `KLKpiBoundPin`
(`64b58eb:RBM3D/Probe/T2004Pins.lean` lines 504-514, 778-784, 798-808), verbatim.  Namespace
`RBM.Loop.T2115Check` here; KL11 (T2115) defines them in `RBM.Loop` and proves `KLKpiBoundPin`, `KLboundPin`.
The `#check`s are the merged names KL11 builds on (KL1, KL2, KL10).
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2115-check.lean`.
-/
import RBM3D

#check @RBM.Loop.KLK
#check @RBM.Loop.KLKpi
#check @RBM.Loop.KLK_eq_sum_Kpi
#check @RBM.Loop.KLKpi_eq_sum_SigmaPi
#check @RBM.Loop.KLsum_cut
#check @RBM.Loop.KLloopOf
#check @RBM.Loop.KLK_two
#check @RBM.Loop.KLK_three
#check @RBM.Loop.KLPar
#check @RBM.Loop.KLPT
#check @RBM.Loop.KLindStepPin
#check @RBM.Loop.KLindStepPin_holds
#check @RBM.Loop.KLindStepAt
#check @RBM.Bparam
#check @RBM.mSigma

namespace RBM.Loop.T2115Check

open RBM RBM.Loop
open Finset

/-- **`(eq:bcal_k)` at a fixed `n`** (the conclusion of `ML:Kbound`): `n`, `κ`, `gmax` and `τ`
are fixed before the constant `C`, which does not depend on `L`, `W`, `g ∈ (0, gmax]`, `E`,
`t ∈ [0,1)`, `σ`, `a`.  Loss `L^τ`, `τ > 0` arbitrary; since `L^τ ≤ N^{τ/d}` for
`N = (WL)^d` (`KL_rpow_le`) this implies the paper's `≺` (deterministic, `N = (WL)^d`). -/
def KLBoundAt (d n : ℕ) (κ gmax : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool)
    (a : Fin n → Zd d p.L),
    ‖KLK d p.L p.g p.W p.E p.t (KLloopOf d p.L σ a)‖
      ≤ C * (p.L : ℝ) ^ τ * (((p.W : ℝ) ^ d)⁻¹ * Bparam d p.L p.g p.t 0) ^ (n - 1)



/-- **Pin `ML:Kbound`, `(eq:bcal_k)`**, for every `n ≥ 1`, conditional on the shapes of
`lem_propTH` (`KLPT`).  `(Kn2sol)`, `(Kn3sol)` are `KLK_two`, `KLK_three`. -/
def KLboundPin : Prop :=
  ∀ (d n : ℕ) (κ gmax : ℝ), 3 ≤ d → 1 ≤ n → 0 < κ → 0 < gmax → KLPT d κ gmax →
    KLBoundAt d n κ gmax


/-- **Pin `(eq:K-pi-bound)`**: `|K^{(π)}(t,σ,a)| ≺ B_{t,0}^{n-1}`, every `π`, `n ≥ 3`. -/
def KLKpiBoundAt (d n : ℕ) [NeZero n] (κ gmax : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool)
    (π : Finset (Fin n × Fin n)) (a : Fin n → Zd d p.L),
    ‖KLKpi d p.L p.g (mSigma p.E) p.t σ a π‖
      ≤ C * (p.L : ℝ) ^ τ * (Bparam d p.L p.g p.t 0) ^ (n - 1)

def KLKpiBoundPin : Prop :=
  ∀ (d n : ℕ) [NeZero n] (κ gmax : ℝ), 3 ≤ d → 3 ≤ n → 0 < κ → 0 < gmax → KLPT d κ gmax →
    KLKpiBoundAt d n κ gmax

end RBM.Loop.T2115Check
