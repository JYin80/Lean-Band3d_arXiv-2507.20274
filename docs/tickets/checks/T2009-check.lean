/-
Release check for T2009 (dispatcher V1, Fri Oct  2 23:47 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §14).
Pinned definitions and `Prop` statements of the PT-B1 pilot (route H, Fable review §2 S3-Z, F1–F2).
Namespace `RBM.Heat.T2009Check` here becomes `RBM.Heat` in the ticket.
Definitions and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2009-check.lean`.
Revised 2026-10-02 23:59 UTC: `Real.cosh_le_exp_half_sq` lives in `Mathlib.Analysis.SpecialFunctions.Trigonometric.Series`, which `RBM3D` does not import; import added.
-/
import RBM3D
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

#check @Real.cosh_le_exp_half_sq
#check @integral_gaussian
#check @MeasureTheory.integral_tsum
#check @Real.mul_le_sin
#check @Complex.cosh

namespace RBM.Heat.T2009Check

open Complex

/-- `N_j(n)`: the number of `±1`-sequences of length `j` whose sum is `n`. -/
def walkCount (j : ℕ) (n : ℤ) : ℕ :=
  ((Finset.univ : Finset (Fin j → Bool)).filter
    (fun ε => (∑ i, (if ε i then (1 : ℤ) else -1)) = n)).card

/-- The heat kernel of the 1D discrete Laplacian on `ℤ`, `h_τ(n) = e^{-2τ} Σ_j τ^j N_j(n) / j!`
(`= e^{-2τ} I_n(2τ)`; route H, step S1). -/
noncomputable def hkZ (τ : ℝ) (n : ℤ) : ℝ :=
  Real.exp (-2 * τ) * ∑' j : ℕ, τ ^ j * (walkCount j n : ℝ) / (Nat.factorial j : ℝ)

/-- The torus kernel `hk(τ, x) = L⁻¹ Σ_{k ∈ ℤ_L} cos(2πkx/L) e^{-2τ(1 - cos(2πk/L))}` (the kernel of
`e^{-τΔ}` on `ℤ_L`; route H, steps S1–S2). -/
noncomputable def hkT (L : ℕ) [NeZero L] (τ : ℝ) (x : ZMod L) : ℝ :=
  (L : ℝ)⁻¹ * ∑ k : ZMod L,
    Real.cos (2 * Real.pi * (k.val : ℝ) * (x.val : ℝ) / L)
      * Real.exp (-2 * τ * (1 - Real.cos (2 * Real.pi * (k.val : ℝ) / L)))

/-- Target 1: positivity. -/
def Nonneg : Prop := ∀ τ : ℝ, 0 ≤ τ → ∀ n : ℤ, 0 ≤ hkZ τ n

/-- Target 2: summability and total mass one. -/
def Mass : Prop := ∀ τ : ℝ, 0 ≤ τ → Summable (hkZ τ) ∧ ∑' n : ℤ, hkZ τ n = 1

/-- Target 3: symmetry. -/
def Symm : Prop := ∀ τ : ℝ, ∀ n : ℤ, hkZ τ (-n) = hkZ τ n

/-- Target 4: the moment generating function (Fable review F2 (i)). -/
def MGF : Prop := ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℂ, z ≠ 0 →
  HasSum (fun n : ℤ => (hkZ τ n : ℂ) * z ^ n) (Complex.exp ((τ : ℂ) * (z + z⁻¹) - 2 * (τ : ℂ)))

/-- Target 5: the tilted inversion formula (Fable review F2 (ii); no contour shift). -/
def Tilt : Prop := ∀ τ : ℝ, 0 ≤ τ → ∀ ν : ℝ, ∀ n : ℤ,
  ((Real.exp (ν * n) * hkZ τ n : ℝ) : ℂ) =
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ k in (-Real.pi)..Real.pi,
      Complex.exp (-((k : ℂ) * (n : ℂ)) * Complex.I)
        * Complex.exp (2 * (τ : ℂ) * (Complex.cosh ((ν : ℂ) + (k : ℂ) * Complex.I) - 1))

/-- Target 6: the torus kernel is the periodisation of the `ℤ` kernel (images). -/
def Images : Prop := ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 ≤ τ → ∀ x : ZMod L,
  HasSum (fun y : ℤ => hkZ τ ((x.val : ℤ) + (L : ℤ) * y)) (hkT L τ x)

/-- Target 7: the torus kernel is a probability on `ℤ_L`. -/
def TorusMass : Prop := ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 ≤ τ →
  (∀ x : ZMod L, 0 ≤ hkT L τ x) ∧ ∑ x : ZMod L, hkT L τ x = 1

end RBM.Heat.T2009Check
