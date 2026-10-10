/-
Release check for T2367 (dispatcher V2, Sat Oct 10 01:25 UTC 2026; DECISIONS §175).  BA-K04: the cactus, `BA/KCactus.lean`.
Part 1: the pins the auditor checks on the branch:
  `example (d : ℕ) : Prop := RBM.BA.T2367Check.BATreeRep d (@RBM.BA.BAGamma d)` (the type of `BAGamma` fits the probe pin), and
  `example (d : ℕ) : RBM.BA.T2367Check.BAGammaType d := @RBM.BA.BAGamma d`.
Part 2: merged names the targets use.  No proofs, no sorry.  Run: lake env lean docs/tickets/checks/T2367-check.lean
-/
import RBM3D.BA.KBase
import RBM3D.BA.FlowPins
import RBM3D.Loop.KLCut
import RBM3D.Loop.KLTree
import RBM3D.Loop.Partition

open RBM RBM.Loop

namespace RBM.BA.T2367Check

/-- The type of the `M`-graph value `Γ` (probe `t/T2360:RBM3D/Probe/T2360Pins.lean:362`, the parameter of `BATreeRep`):
sizes, `M(σ)` as a function of the charge, `t`, a crossing-free diagonal set, charges, labels. -/
def BAGammaType (d : ℕ) : Type :=
  ∀ (L n : ℕ) [NeZero L] [NeZero n], (Bool → Matrix (Zd d L) (Zd d L) ℂ) → ℝ →
    Finset (Fin n × Fin n) → (Fin n → Bool) → (Fin n → Zd d L) → ℂ

/-- **`BATreeRep`** (verbatim: probe 362; `tree-representation_BA`, `A:592-598`, here `n ≥ 3`, D634): the K05b target; K04
defines its `Γ`. -/
def BATreeRep (d : ℕ)
    (Γ : ∀ (L n : ℕ) [NeZero L] [NeZero n], (Bool → Matrix (Zd d L) (Zd d L) ℂ) → ℝ →
      Finset (Fin n × Fin n) → (Fin n → Bool) → (Fin n → Zd d L) → ℂ) : Prop :=
  ∀ (Λ κ : ℝ), 0 < Λ → 0 < κ → ∀ (L : ℕ) (hL : 3 ≤ L) (W : ℕ) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
    haveI : NeZero L := ⟨by omega⟩
    BAReal d L g κ E m → ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ (σ : Fin n → Bool) (a : Fin n → Zd d L),
      BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t (KLloopOf d L σ a)
        = (((W : ℂ) ^ d)⁻¹) ^ (n - 1) *
            ∑ F ∈ TSP n, Γ L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t F σ a

end RBM.BA.T2367Check

/-! ## Part 2: merged names -/
#check @RBM.Loop.KLgval
#check @RBM.Loop.KLgval_congr
#check @RBM.Loop.KLsum_cut
#check @RBM.Loop.KLnodes
#check @RBM.Loop.KLleafPar
#check @RBM.Loop.KLnodePar
#check @RBM.Loop.KLleafPar_spec
#check @RBM.Loop.KLnodePar_spec
#check @RBM.Loop.KLIsTSP
#check @RBM.Loop.KLisTSP_of_mem_TSP
#check @RBM.Loop.TSP
#check @RBM.Loop.KLloopOf
#check @RBM.Loop.KLtreeValW
#check @RBM.PropThetaQ
#check @RBM.BA.BATheta
#check @RBM.BA.BAMss
#check @RBM.BA.BAMsigma
#check @RBM.BA.BATheta_isSymm
#check @RBM.BA.BATheta_swap
#check @RBM.BA.BAMLoop_apply
#check @RBM.BA.BAMLoop_trace
#check @RBM.BA.BAKsol
