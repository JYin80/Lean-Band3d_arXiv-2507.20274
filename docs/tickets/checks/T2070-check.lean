/-
Release check for T2070 (dispatcher V1, Sat Oct  3 19:24 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §15, §29).
Pinned `Prop`s of KL8+9: the probe pins `KLmoleculePin`, `KLsumZeroPin` (`64b58eb:RBM3D/Probe/T2004Pins.lean`
lines 821–843), verbatim.  Namespace `RBM.Loop.T2070Check` here; the theorems go to `RBM.Loop`.
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2070-check.lean`.
-/
import RBM3D

#check @RBM.Loop.KLSigmaPi
#check @RBM.Loop.KLmaxDist
#check @RBM.Loop.KLsigAlt
#check @RBM.Loop.KLPar
#check @RBM.Loop.KLShort
#check @RBM.Loop.KLPT
#check @RBM.Loop.KLSigmaPi_alt_sumZero_le
#check @RBM.mSigma

namespace RBM.Loop.T2070Check

open RBM RBM.Loop
open Finset

/-- **Route pin `(eq:molecule-decay)`**: `|Σ^{(∅)}(t,σ,b)| ≤ C e^{-c max|b_i-b_j|}`, every `σ`. -/
def KLmoleculeAt (d n : ℕ) [NeZero n] (κ gmax : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool)
    (δ : Fin n → Zd d p.L),
    ‖KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ‖ ≤ C * Real.exp (-(c * (KLmaxDist d p.L δ : ℝ)))

def KLmoleculePin : Prop :=
  ∀ (d n : ℕ) [NeZero n] (κ gmax : ℝ), 3 ≤ d → 3 ≤ n → 0 < κ → 0 < gmax → KLShort d κ gmax →
    KLmoleculeAt d n κ gmax

/-- **Route pin `(eq:Sigma-empty-sum-zero)`**, `σ = σ^{(alt)}`, `n` even: the signed sum is
`O(|1-t|)` ([YY_25] Lemma 3.10) and the absolute sum is `O(g² + |1-t|)` ([RBSO1D] Claim 4.30,
cited by the paper; `RBM1D`/`RBM2D` work at `g = 1` and have no analogue; split row KL9 derives it
from the signed estimate and `(prop:ThfadC_short)`). -/
def KLsumZeroAt (d n : ℕ) [NeZero n] (κ gmax : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (x : Zd d p.L),
    ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d p.L => δ 0 = x),
        KLSigmaPi d p.L p.g (mSigma p.E) p.t (KLsigAlt n) ∅ δ‖ ≤ C * (1 - p.t) ∧
    ∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d p.L => δ 0 = x),
        ‖KLSigmaPi d p.L p.g (mSigma p.E) p.t (KLsigAlt n) ∅ δ‖ ≤ C * (p.g ^ 2 + (1 - p.t))

def KLsumZeroPin : Prop :=
  ∀ (d n : ℕ) [NeZero n] (κ gmax : ℝ), 3 ≤ d → 4 ≤ n → Even n → 0 < κ → 0 < gmax →
    KLShort d κ gmax → KLsumZeroAt d n κ gmax

end RBM.Loop.T2070Check
