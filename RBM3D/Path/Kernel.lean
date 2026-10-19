/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Propagator.Props4

/-!
# The one-index kernel of `𝒰_{v,w}` and the Duhamel telescope

The kernel `ukerMat` of the evolution `𝒰_{v,w}`, its composition law and the abstract discrete
Duhamel telescope.  It follows RBM2D `Path/Kernel` (itself a development of RBM1D `GridDuhamel`).
Paper: (3.12) `def_Ustz`.

The lattice is `Zd d L`; the propagator `Theta d L g` and `SB d L g` carry the coupling `g` as an
explicit real parameter, so `ukerMat` carries `(d, L, g)` (for the model, `g = sz.lam n`).  The
algebraic facts `mul_Theta_of_three_le`, `Theta_commute_of_three_le` of `Propagator/Props4`
discharge `‖SB d L g‖ = 1`
from `3 ≤ L`.

* `ukerMat`: the one-index kernel `(1 - v ξ S^{(B)}) Θ^{(B)}_{w ξ}`.
* `ukerMat_mul`, `ukerMat_self`: the composition law and the kernel at equal times.
* `duhamel_telescope`: the abstract discrete Duhamel telescope.

`d` enters only through `Theta d L g` and `SB d L g`; no closed form of `Θ` is used.  The dimension
and the coupling are free (`3 ≤ L` is the only constraint, as in every RBM2D statement).
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Path

open Matrix

section Kernel

variable (d L : ℕ) [NeZero L] (g : ℝ)

/-- The one-index kernel `(1 - v ξ S^{(B)}) Θ^{(B)}_{w ξ}` of `𝒰_{v,w}` ((3.12) `def_Ustz`). -/
def ukerMat (ξ : ℂ) (v w : ℝ) : Matrix (Zd d L) (Zd d L) ℂ :=
  (1 - ((v : ℂ) * ξ) • SB d L g) * Theta d L g ((w : ℂ) * ξ)

end Kernel

section KernelLemmas

variable (d L : ℕ) [NeZero L] (g : ℝ)

/-- The one-index kernels compose (RBM1D `edgeKer_mul`): `(1 - vξS) Θ_{wξ} (1 - uξS) Θ_{vξ} = (1 - uξS) Θ_{wξ}`. -/
theorem ukerMat_mul (hL : 3 ≤ L) {ξ : ℂ} {u v w : ℝ} (hv : ‖(v : ℂ) * ξ‖ < 1)
    (hw : ‖(w : ℂ) * ξ‖ < 1) :
    ukerMat d L g ξ v w * ukerMat d L g ξ u v = ukerMat d L g ξ u w := by
  set P : Matrix (Zd d L) (Zd d L) ℂ := 1 - ((u : ℂ) * ξ) • SB d L g with hP
  set Q : Matrix (Zd d L) (Zd d L) ℂ := 1 - ((v : ℂ) * ξ) • SB d L g with hQ
  set Tw : Matrix (Zd d L) (Zd d L) ℂ := Theta d L g ((w : ℂ) * ξ) with hTw
  set Tv : Matrix (Zd d L) (Zd d L) ℂ := Theta d L g ((v : ℂ) * ξ) with hTv
  have h1 : Commute Tw P :=
    (Commute.one_right Tw).sub_right
      ((Theta_commute_SB_of_three_le (g := g) hL hw).smul_right ((u : ℂ) * ξ))
  have h2 : Commute Q P :=
    (Commute.one_left P).sub_left
      ((Commute.one_right (((v : ℂ) * ξ) • SB d L g)).sub_right
        (((Commute.refl (SB d L g)).smul_left ((v : ℂ) * ξ)).smul_right ((u : ℂ) * ξ)))
  have h3 : Commute Tw Tv := Theta_commute_of_three_le (g := g) hL hw hv
  have h4 : Q * Tv = 1 := mul_Theta_of_three_le (g := g) hL hv
  calc ukerMat d L g ξ v w * ukerMat d L g ξ u v = Q * Tw * (P * Tv) := rfl
    _ = Q * (Tw * P) * Tv := by noncomm_ring
    _ = Q * (P * Tw) * Tv := by rw [h1.eq]
    _ = (Q * P) * (Tw * Tv) := by noncomm_ring
    _ = (P * Q) * (Tv * Tw) := by rw [h2.eq, h3.eq]
    _ = P * (Q * Tv) * Tw := by noncomm_ring
    _ = P * Tw := by rw [h4, Matrix.mul_one]

/-- At equal times the one-index kernel is the identity (RBM1D `edgeKer_self`). -/
theorem ukerMat_self (hL : 3 ≤ L) {ξ : ℂ} {v : ℝ} (hv : ‖(v : ℂ) * ξ‖ < 1) :
    ukerMat d L g ξ v v = 1 :=
  mul_Theta_of_three_le (g := g) hL hv

end KernelLemmas

section Telescope

variable {V : Type*} [AddCommGroup V]

/-- **The discrete Duhamel telescoping identity.**  For a family `U j k : V →+ V`
satisfying the evolution-kernel laws `U k k = id` and `(U j k).comp (U i j) = U i k`
for `i ≤ j ≤ k`, and any sequence `A : ℕ → V`,
`A k - U 0 k (A 0) = ∑_{j < k} U (j+1) k (A (j+1) - U j (j+1) (A j))`. -/
theorem duhamel_telescope (U : ℕ → ℕ → V →+ V)
    (hself : ∀ k, U k k = AddMonoidHom.id V)
    (hcomp : ∀ i j k, i ≤ j → j ≤ k → (U j k).comp (U i j) = U i k)
    (A : ℕ → V) (k : ℕ) :
    A k - U 0 k (A 0) =
      ∑ j ∈ Finset.range k, U (j + 1) k (A (j + 1) - U j (j + 1) (A j)) := by
  induction k with
  | zero =>
      have h0 : U 0 0 (A 0) = A 0 := by rw [hself 0]; rfl
      simp [h0]
  | succ k ih =>
      have hrw : ∀ j ∈ Finset.range k,
          U (j + 1) (k + 1) (A (j + 1) - U j (j + 1) (A j))
            = U k (k + 1) (U (j + 1) k (A (j + 1) - U j (j + 1) (A j))) := by
        intro j hj
        have hjk : j + 1 ≤ k := Finset.mem_range.mp hj
        have hcomp' := hcomp (j + 1) k (k + 1) hjk (Nat.le_succ k)
        rw [← hcomp']
        rfl
      have hsum : ∑ j ∈ Finset.range k, U (j + 1) (k + 1) (A (j + 1) - U j (j + 1) (A j))
          = U k (k + 1) (A k - U 0 k (A 0)) := by
        rw [ih]
        rw [map_sum (U k (k+1))]
        exact Finset.sum_congr rfl (fun j hj => hrw j hj)
      have htail : U (k + 1) (k + 1) (A (k + 1) - U k (k + 1) (A k))
          = A (k + 1) - U k (k + 1) (A k) := by rw [hself (k+1)]; rfl
      have hfront : U k (k + 1) (A k - U 0 k (A 0))
          = U k (k + 1) (A k) - U 0 (k + 1) (A 0) := by
        rw [map_sub]
        have := hcomp 0 k (k + 1) (Nat.zero_le k) (Nat.le_succ k)
        rw [show U k (k+1) (U 0 k (A 0)) = (U k (k+1)).comp (U 0 k) (A 0) from rfl, this]
      rw [Finset.sum_range_succ, hsum, hfront, htail]
      abel

end Telescope

end RBM.Path

end
