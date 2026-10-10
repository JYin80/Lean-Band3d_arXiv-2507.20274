/-
Release check for T2369 (dispatcher V2, Sat Oct 10 01:55 UTC 2026; DECISIONS §177).  BA-K02: Ward's identity `lem_WI_K` over a
general kernel `S` (route G in place in `Loop/KLWard.lean`) and its BA instance (`BA/KWard.lean`).
Part 1: the pins (copied verbatim by the ticket into namespace `RBM.Loop`; here in `RBM.Loop.T2369Check`).  The auditor checks
`WardS` by `rfl` and the structure `KernelFacts` field by field (DECISIONS §175 (1)).
Part 2: G1, the band statements unchanged.  No proofs (only `@name`), no sorry.
Run: lake env lean docs/tickets/checks/T2369-check.lean
-/
import RBM3D.Loop.KLWard

open Finset

namespace RBM.Loop.T2369Check

/-- **`KernelFacts`** (verbatim: probe `t/T2360:RBM3D/Probe/T2360Pins.lean:204`): the four properties of `S` that
`Loop/KLWard.lean` uses (`SB_transpose`, `conj (SB a b) = SB a b`, `sum_SB_row`, `norm_SB_apply_le`). -/
structure KernelFacts {d L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℂ) : Prop where
  symm : ∀ a b, S a b = S b a
  real : ∀ a b, (starRingEnd ℂ) (S a b) = S a b
  colSum : ∀ b, ∑ a, S a b = 1
  entry : ∀ a b, ‖S a b‖ ≤ 1

/-- **`WardS`**: `(WI_calK)` for every family of `K`-loops on `[0,1)` over a kernel with `KernelFacts`, from:
`Im m(+) > 0` and `m(-) = conj m(+)`; the initial data flip to their conjugate and are cyclically invariant; the
initial data satisfy the identity at `t = 0` on the loops of length `≥ 3`; the family satisfies it at length `2`.
`η_t = (1 - t) Im m(+)`. -/
def WardS : Prop :=
  ∀ (d L W : ℕ) [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℂ) (m : Bool → ℂ) (M : LoopIdx (Zd d L) → ℂ),
    KernelFacts S → 1 ≤ W → 0 < (m true).im → m false = (starRingEnd ℂ) (m true) →
    (∀ (σ : List Bool) (a : List (Zd d L)), σ.length = a.length → 2 ≤ a.length →
      M ⟨σ.map not, a⟩ = (starRingEnd ℂ) (M ⟨σ, a⟩)) →
    (∀ (s : Bool) (b : Zd d L) (σ : List Bool) (a : List (Zd d L)), σ.length = a.length →
      M ⟨s :: σ, b :: a⟩ = M ⟨σ ++ [s], a ++ [b]⟩) →
    (∀ (μ : List Bool) (a : List (Zd d L)), a.length = μ.length + 1 → 1 ≤ μ.length →
      ∑ x : Zd d L, M ⟨true :: μ ++ [false], a ++ [x]⟩
        = (2 * Complex.I * (W : ℂ) ^ d * ((m true).im : ℂ))⁻¹ * (M ⟨true :: μ, a⟩ - M ⟨false :: μ, a⟩)) →
    ∀ {K : ℝ → LoopIdx (Zd d L) → ℂ}, IsKLoopS d L W S m M (Set.Ico 0 1) K →
    (∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ a : Zd d L,
      ∑ x : Zd d L, K t ⟨[true, false], [a, x]⟩ = (((W : ℂ) ^ d) * ((1 - t : ℝ) : ℂ))⁻¹) →
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (s : Bool) (μ : List Bool) (a : List (Zd d L)), a.length = μ.length + 1 →
      ∑ x : Zd d L, K t ⟨s :: μ ++ [!s], a ++ [x]⟩
        = (2 * Complex.I * (W : ℂ) ^ d * (((1 - t) * (m true).im : ℝ) : ℂ))⁻¹ *
            (K t ⟨true :: μ, a⟩ - K t ⟨false :: μ, a⟩)

/-! ## Part 2: G1 (old statement := old name) -/

example : ∀ (d L W : ℕ) [NeZero L] (g E : ℝ), 3 ≤ L → 1 ≤ W → |E| < 2 → ∀ t : ℝ, 0 ≤ t → t < 1 →
    ∀ (s : Bool) (μ : List Bool) (a : List (Zd d L)), a.length = μ.length + 1 →
      ∑ x : Zd d L, KLK d L g W E t ⟨s :: μ ++ [!s], a ++ [x]⟩
        = (2 * Complex.I * (W : ℂ) ^ d * (Gauss.etaT E t : ℂ))⁻¹ *
            (KLK d L g W E t ⟨true :: μ, a⟩ - KLK d L g W E t ⟨false :: μ, a⟩) :=
  @RBM.Loop.KLK_ward

example : ∀ (d L W : ℕ) [NeZero L] (g E : ℝ), 3 ≤ L → 1 ≤ W → |E| < 2 → ∀ t ∈ Set.Ico (0 : ℝ) 1,
    ∀ (σ : List Bool) (a : List (Zd d L)), σ.length = a.length → 1 ≤ a.length →
      KLK d L g W E t ⟨σ.map not, a⟩ = (starRingEnd ℂ) (KLK d L g W E t ⟨σ, a⟩) :=
  @RBM.Loop.KLWard_flip

end RBM.Loop.T2369Check

/-! ## Names the targets use (merged) -/
#check @RBM.Loop.IsKLoopS
#check @RBM.Loop.IsKLoop_iff_IsKLoopS
#check @RBM.Loop.KLK_isKLoop
#check @RBM.Loop.KLward_two
#check @RBM.SB_transpose
#check @RBM.Gauss.etaT
