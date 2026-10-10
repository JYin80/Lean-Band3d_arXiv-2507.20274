/-
Release check for T2374 (dispatcher V2, Sat Oct 10 07:24 UTC 2026; DECISIONS §185).  BA-K05b: `BA/KTreeRep.lean`, the chord pairs,
`IsKLoopS` for the spliced family, `BAKsolve`, `BATreeRep` (supervisor 0350 C1–C5).
Part 1: the pin `BATreeRep` (verbatim from the probe `t/T2360:RBM3D/Probe/T2360Pins.lean:362`; copied by the ticket into
namespace `RBM.BA`; here in `RBM.BA.T2374Check`; the auditor adds `example : @RBM.BA.BATreeRep = @RBM.BA.T2374Check.BATreeRep
:= rfl`).  Part 2: merged names (on `main`; K05a's names are on `t/T2370` until it merges and are not checked here).
No proofs, no sorry.  Run: lake env lean docs/tickets/checks/T2374-check.lean
-/
import RBM3D.BA.KSolve
import RBM3D.BA.KCactus
import RBM3D.BA.KBase
import RBM3D.Loop.KLCut
import RBM3D.Loop.KLTree

open RBM RBM.Loop

namespace RBM.BA.T2374Check

/-- `tree-representation_BA` (`A:592-598`, [RBSO1D L4.16], stated there for `n ≥ 4`; `n = 3` is `(Kn3sol)`, `1_2:1176`, the
same formula with one tree): `𝒦^{(n)} = W^{-d(n-1)} ∑_{F ∈ TSP(n)} Γ_M(F)`, `n ≥ 3`, with `Γ` the `M`-graph value
(`A:380-583`; rules and numerical check in `T2360-design.md` §3). -/
def BATreeRep (d : ℕ)
    (Γ : ∀ (L n : ℕ) [NeZero L] [NeZero n], (Bool → Matrix (Zd d L) (Zd d L) ℂ) → ℝ →
      Finset (Fin n × Fin n) → (Fin n → Bool) → (Fin n → Zd d L) → ℂ) : Prop :=
  ∀ (Λ κ : ℝ), 0 < Λ → 0 < κ → ∀ (L : ℕ) (hL : 3 ≤ L) (W : ℕ) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
    haveI : NeZero L := ⟨by omega⟩
    BAReal d L g κ E m → ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ (σ : Fin n → Bool) (a : Fin n → Zd d L),
      BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t (KLloopOf d L σ a)
        = (((W : ℂ) ^ d)⁻¹) ^ (n - 1) *
            ∑ F ∈ TSP n, Γ L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t F σ a

/-- The target of `baTreeRep` is a `Prop` (statement shape only). -/
example : Prop := ∀ d : ℕ, BATreeRep d (@RBM.BA.BAGamma d)

end RBM.BA.T2374Check

/-! ## Part 2: merged names -/
#check @RBM.BA.BAKsolve
#check @RBM.BA.BAKsol
#check @RBM.BA.BAKsol_isKLoopS
#check @RBM.BA.baK_unique
#check @RBM.BA.BAGamma
#check @RBM.BA.BACactusVal_sum_zero_BAMLoop
#check @RBM.BA.BATheta_resolvent
#check @RBM.BA.BATheta_swap
#check @RBM.BA.BATheta_isSymm
#check @RBM.Loop.IsKLoopS
#check @RBM.Loop.treeEqRhsS
#check @RBM.Loop.KLsum_cut
#check @RBM.Loop.KLFIn
#check @RBM.Loop.KLFOut
#check @RBM.Loop.KLshiftIn
#check @RBM.Loop.KLshiftOut
#check @RBM.Loop.KLinV
#check @RBM.Loop.KLoutV
#check @RBM.Loop.KLloopOf
#check @RBM.Loop.TSP
