/-
Release check for T2368 (dispatcher V2, Sat Oct 10 01:40 UTC 2026; DECISIONS §176).  BA-K03: `BA/KSolve.lean`, the levels
`n ≤ 3` of the BA `K`-loop equation and the BA instances of K01 (moved here, DECISIONS §172).
Compile only after T2366 (K01 generic part: `uniqS_holds`, `retireS_holds`, `rotS_holds`, `translS_holds`) has merged.
Part 1: the pins (copied verbatim by the ticket into namespace `RBM.BA`; here in `RBM.BA.T2368Check`; the auditor adds
`example : @RBM.BA.X = @RBM.BA.T2368Check.X := rfl` for each).  Part 2: merged names.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2368-check.lean
-/
import RBM3D.BA.KBase
import RBM3D.BA.FlowPins
import RBM3D.BA.Ward
import RBM3D.Loop.Unique
import RBM3D.Loop.KLUnique

open RBM RBM.Loop

namespace RBM.BA.T2368Check

/-- **`IsKLoopSLe`**: the system of `IsKLoopS` (`Loop/KLTree.lean:828`) on the loops of length `≤ N`.  Closed: the cuts of a
loop of length `n` have lengths in `[1, n]`, and length `1` is the third clause. -/
def IsKLoopSLe (d L W : ℕ) [NeZero L] (N : ℕ) (S : Matrix (Zd d L) (Zd d L) ℂ) (m : Bool → ℂ)
    (M : LoopIdx (Zd d L) → ℂ) (T : Set ℝ) (K : ℝ → LoopIdx (Zd d L) → ℂ) : Prop :=
  (∀ t ∈ T, ∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length → I.length ≤ N →
      HasDerivAt (fun s => K s I) (treeEqRhsS d L W S (K t) I) t) ∧
  (∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length → I.length ≤ N → K 0 I = M I) ∧
  (∀ t ∈ T, ∀ (s : Bool) (a : Zd d L), K t ⟨[s], [a]⟩ = m s)

/-- **`BAKsolve`** (verbatim: probe `t/T2360:RBM3D/Probe/T2360Pins.lean:281`): existence of the BA `𝒦` on `[0,1)` with
`(Kn2sol)`; the target of K05b, a closing condition of stage K (supervisor 2051 Q5). -/
def BAKsolve (d : ℕ) : Prop :=
  ∀ (Λ κ : ℝ), 0 < Λ → 0 < κ → ∀ (L : ℕ) (hL : 3 ≤ L) (W : ℕ) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
    haveI : NeZero L := ⟨by omega⟩
    BAReal d L g κ E m →
      ∃ K : ℝ → LoopIdx (Zd d L) → ℂ,
        IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) (PropSpin m)
          (BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m))) (Set.Ico (0 : ℝ) 1) K ∧
        ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (σ : Bool × Bool) (a₁ a₂ : Zd d L),
          K t ⟨[σ.1, σ.2], [a₁, a₂]⟩ =
            (((W : ℂ) ^ d)⁻¹) * (BATheta d L g E m t σ.1 σ.2 * BAMss d L (BAMB d L g (E : ℂ) m) σ.1 σ.2) a₁ a₂

/-- **`BAKsolveLe3`** (K03's target): the levels `n ≤ 3` of the BA system are solved by `(Kn2sol)` and `(Kn3sol)`
(`1_2:1175-1177`, D634), with the K00 convention (`BAMLoop` pairs `σ_i` with `(a_{i-1}, a_i)`; a leaf at `a_v` carries
`Θ^{(σ_v, σ_{v+1})}`). -/
def BAKsolveLe3 (d : ℕ) : Prop :=
  ∀ (Λ κ : ℝ), 0 < Λ → 0 < κ → ∀ (L : ℕ) (hL : 3 ≤ L) (W : ℕ) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
    haveI : NeZero L := ⟨by omega⟩
    BAReal d L g κ E m →
      ∃ K : ℝ → LoopIdx (Zd d L) → ℂ,
        IsKLoopSLe d L W 3 (1 : Matrix (Zd d L) (Zd d L) ℂ) (PropSpin m)
          (BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m))) (Set.Ico (0 : ℝ) 1) K ∧
        (∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (σ : Bool × Bool) (a₁ a₂ : Zd d L),
          K t ⟨[σ.1, σ.2], [a₁, a₂]⟩ =
            (((W : ℂ) ^ d)⁻¹) * (BATheta d L g E m t σ.1 σ.2 * BAMss d L (BAMB d L g (E : ℂ) m) σ.1 σ.2) a₁ a₂) ∧
        ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (σ₁ σ₂ σ₃ : Bool) (a₁ a₂ a₃ : Zd d L),
          K t ⟨[σ₁, σ₂, σ₃], [a₁, a₂, a₃]⟩ =
            ∑ b₁ : Zd d L, ∑ b₂ : Zd d L, ∑ b₃ : Zd d L,
              BATheta d L g E m t σ₁ σ₂ a₁ b₁ * BATheta d L g E m t σ₂ σ₃ a₂ b₂ * BATheta d L g E m t σ₃ σ₁ a₃ b₃ *
                BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) ⟨[σ₁, σ₂, σ₃], [b₁, b₂, b₃]⟩

end RBM.BA.T2368Check

/-! ## Part 2: merged names -/
#check @RBM.Loop.IsKLoopS
#check @RBM.Loop.treeEqRhsS
#check @RBM.Loop.uniqS_holds
#check @RBM.Loop.retireS_holds
#check @RBM.Loop.rotS_holds
#check @RBM.Loop.translS_holds
#check @RBM.Loop.UniqS
#check @RBM.Loop.RotS
#check @RBM.Loop.TranslS
#check @RBM.BA.BAMLoop_apply
#check @RBM.BA.BAMLoop_trace
#check @RBM.BA.BATheta_resolvent
#check @RBM.BA.BATheta_hasDerivAt
#check @RBM.BA.BATheta_isSymm
#check @RBM.BA.BATheta_swap
#check @RBM.BA.BAMB_shift
#check @RBM.BA.BAMB_symm
#check @RBM.BA.BAKsol
#check @RBM.PropSpin
