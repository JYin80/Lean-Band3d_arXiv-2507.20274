/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Matrix.Basis
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The deterministic core of the expansions `(Owx)` and `(Oe2x)`

The weight expansion `(Owx)` and the `GG` expansion `(Oe2x)` of Section 7 (the paper
attributes both to `[yang2021delocalization]`, Lemmas 3.5 and 3.14) are identities
"in expectation" (`=_𝔼`) for a random band matrix `H` and its resolvent `G = (H - z)⁻¹`.
Stating them faithfully needs the random layer: the `N × N` model and its law, `m(z)`,
`S^±`, expectation, and derivatives `∂_{h_{αx}}` in the matrix entries.  None of that is
in this repository yet, and `docs/QUEUE.md` Q8 records why the two axioms are not
written here.

What *is* deterministic, and is exactly what links `(Owx)` to `Graph/Model.lean`, is
how the derivative `∂_{h_{αw}}` acts on a resolvent entry:

  `∂_{h_{αw}} G_{β₁β₂} = - G_{β₁α} G_{wβ₂}`.

In the third term of `(Owx)`, `m Σ_α S_{wα} G_{αw} ∂_{h_{αw}} f(G)`, the derivative hits a
solid edge `G_{β₁β₂}` (or a light-weight `Ǧ_{β₁β₂} = G_{β₁β₂} - m δ_{β₁β₂}`, which has the
same derivative) and replaces it by `G_{β₁α} G_{wβ₂}`; together with the prefactor
`G_{αw}` these are the three new solid edges `e₁ = G_{β₁α}`, `e₂ = G_{wβ₂}`,
`e₃ = G_{αw}` whose diagonal pattern `Graph/Model.lean` classifies.  This file proves
that identity for the inverse of any invertible matrix, as a derivative along the
matrix unit `E_{αw}`: no axiom, no probability.

## Main results

* `RBM.Graph.hasDerivAt_inverse_apply` :
  `d/ds (A + s E_{αw})⁻¹_{ij} |_{s=0} = -(A⁻¹)_{iα} (A⁻¹)_{wj}`
* `RBM.Graph.hasDerivAt_inverse_sub_apply` : the same for `(A + s E_{αw})⁻¹ - M`
  with `M` fixed, i.e. for a light-weight `Ǧ = G - M`
-/

namespace RBM.Graph

open Matrix
open scoped Matrix.Norms.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `(P E_{αw} Q)_{ij} = P_{iα} Q_{wj}`. -/
theorem mul_single_mul_apply (P Q : Matrix n n ℂ) (α w i j : n) :
    (P * single α w (1 : ℂ) * Q) i j = P i α * Q w j := by
  classical
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]

/-- **`∂_{h_{αw}} G_{ij} = -G_{iα} G_{wj}`.**  For an invertible matrix `A` with inverse
`G = A⁻¹`, the derivative of `s ↦ (A + s E_{αw})⁻¹_{ij}` at `s = 0` is `-G_{iα} G_{wj}`.
With `A = H - z` this is the resolvent identity behind the derivative terms of
`(Owx)` and `(Oe2x)`. -/
theorem hasDerivAt_inverse_apply {A : Matrix n n ℂ} (hA : IsUnit A) (α w i j : n) :
    HasDerivAt (fun s : ℂ => Ring.inverse (A + s • single α w (1 : ℂ)) i j)
      (-(Ring.inverse A i α * Ring.inverse A w j)) 0 := by
  obtain ⟨u, rfl⟩ := hA
  set E : Matrix n n ℂ := single α w 1
  -- the path `s ↦ u + s E` through `u` with velocity `E`
  have hpath : HasDerivAt (fun s : ℂ => (u : Matrix n n ℂ) + s • E) E 0 := by
    have h := ((hasDerivAt_id (0 : ℂ)).smul_const E).const_add (u : Matrix n n ℂ)
    simp only [id, one_smul] at h
    exact h
  set D := -ContinuousLinearMap.mulLeftRight ℂ (Matrix n n ℂ) ↑u⁻¹ ↑u⁻¹
  have hinv : HasFDerivAt Ring.inverse D ((u : Matrix n n ℂ) + (0 : ℂ) • E) := by
    rw [zero_smul, add_zero]
    exact hasFDerivAt_ringInverse (𝕜 := ℂ) u
  have hcomp := hinv.comp_hasDerivAt (0 : ℂ) hpath
  -- read off the `(i, j)` entry
  let ent : Matrix n n ℂ →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (entryLinearMap ℂ ℂ i j)
  have hent := ent.hasFDerivAt.comp_hasDerivAt (0 : ℂ) hcomp
  have hval : ent (D E)
      = -(Ring.inverse (u : Matrix n n ℂ) i α * Ring.inverse (u : Matrix n n ℂ) w j) := by
    simp only [D, Ring.inverse_unit]
    simp [ent, E, mul_single_mul_apply]
  exact hent.congr_deriv hval

/-- The same derivative for a light-weight `Ǧ = G - M` with `M` independent of `H`. -/
theorem hasDerivAt_inverse_sub_apply {A : Matrix n n ℂ} (hA : IsUnit A) (M : Matrix n n ℂ)
    (α w i j : n) :
    HasDerivAt (fun s : ℂ => (Ring.inverse (A + s • single α w (1 : ℂ)) - M) i j)
      (-(Ring.inverse A i α * Ring.inverse A w j)) 0 := by
  exact (hasDerivAt_inverse_apply hA α w i j).sub_const (M i j)

end RBM.Graph
