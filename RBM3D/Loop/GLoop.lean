/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Gauss.Model
import RBM3D.Defs.Semicircle
import RBM3D.Analysis.Resolvent

/-!
# `G`-loops

`(Eq:defGLoop)`: for `σ ∈ {+,-}^n` and `a ∈ (Z_L^d)^n`, the `n`-`G`-loop is

  `L^(n)_{t,σ,a} = tr ( Π_i G_t(σ_i) E_{a_i} )`,  `(E_a)_{xy} = W^{-d} 1(x = y ∈ [a])`,

with `G_t(+) = (H_t - z_t)^{-1}` and `G_t(-) = G_t^*`, along the flow
`z_t = E + (1-t) m^{(E)}` of `(eq:zt)`.

## What is here

The definitions, and the two facts that do not need any operator-norm machinery:

* `RBM.Gauss.Eblk` : the rescaled block identity `E_a`, and `Eblk_isHermitian`;
* `RBM.Gauss.etaT` : `η_t = (1-t) Im m^{(E)}`, `etaT_eq_zt_im`, and `etaT_pos` -- positive
  for `|E| < 2` and `t < 1`, which is what puts `z_t` off the real axis and makes the
  resolvent exist;
* `RBM.Gauss.Gsig` : `G_t(σ)` as `Ring.inverse (H - z • 1)`, in the same style as
  `RBM.Theta`, and `gloop`, `loopMax`.

## What is missing, and what it needs

The deterministic envelope `|L^(n)| ≤ (η_t^{-1})^n` of `(5.2)`.  The analytic input is in
place (`RBM3D/Analysis/Resolvent.lean`: `‖(H-z)⁻¹‖ ≤ (Im z)⁻¹` pointwise on the whole
space), but turning it into a bound on a **trace of a product** needs `|tr X| ≤ rank · ‖X‖`
or a trace-norm inequality, and Mathlib's `Matrix.trace` has no such API for the `ℓ²`
operator norm.  That gap is recorded in `docs/QUEUE.md` (Q50) rather than papered over
here: the project does not state what it cannot prove.
-/

namespace RBM.Gauss

open Matrix Complex

variable (d L W : ℕ) [NeZero L] (g : ℝ)

/-! ### The rescaled block identity `E_a` -/

/-- `(E_a)_{xy} = W^{-d} 1(x = y ∈ [a])` of `(Eq:defGLoop)`. -/
noncomputable def Eblk (a : Zd d L) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  Matrix.diagonal fun x => if x.1 = a then ((W : ℂ) ^ d)⁻¹ else 0

variable {d L W}

omit [NeZero L] in
theorem Eblk_apply (a : Zd d L) (x y : Vtx d L W) :
    Eblk d L W a x y = if x = y then (if x.1 = a then ((W : ℂ) ^ d)⁻¹ else 0) else 0 := by
  simp [Eblk, Matrix.diagonal_apply]

omit [NeZero L] in
theorem Eblk_isHermitian (a : Zd d L) : (Eblk d L W a).IsHermitian := by
  refine Matrix.isHermitian_diagonal_iff.mpr fun x => ?_
  by_cases h : x.1 = a <;> simp [h, IsSelfAdjoint]

/-! ### The flow `z_t` and its imaginary part -/

variable (E t : ℝ)

/-- `η_t = (1 - t) Im m^{(E)}`, the imaginary part of the flow `(eq:zt)`; `(eta)`. -/
noncomputable def etaT : ℝ := (1 - t) * (mE E).im

variable {E t}

theorem etaT_eq_zt_im : etaT E t = (zt E t).im := by
  rw [etaT, zt_im]

/-- `η_t > 0` in the bulk for `t < 1`: this is what keeps `z_t` off the real axis. -/
theorem etaT_pos (hE : |E| < 2) (ht : t < 1) : 0 < etaT E t :=
  mul_pos (by linarith) (mE_im_pos hE)

/-! ### `G_t(σ)` and the loops -/

variable (d L W)

/-- `G_t(σ)`: the resolvent at `z_t` for `σ = +` and at `conj z_t` for `σ = -`, as
`Ring.inverse`, in the same style as `RBM.Theta`. -/
noncomputable def Gsig (ω : Omega d L W) (E t : ℝ) (σ : Bool) :
    Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  Ring.inverse (Hmat d L W ω - (if σ then zt E t else (starRingEnd ℂ) (zt E t)) • 1)

/-- **`(Eq:defGLoop)`**: the `n`-`G`-loop `tr (Π_i G_t(σ_i) E_{a_i})`. -/
noncomputable def gloop (ω : Omega d L W) (E t : ℝ) {n : ℕ} (σ : Fin n → Bool)
    (a : Fin n → Zd d L) : ℂ :=
  Matrix.trace (List.ofFn fun i : Fin n => Gsig d L W ω E t (σ i) * Eblk d L W (a i)).prod

/-- `max_{σ,a} |L^(n)_{t,σ,a}|`, the quantity the loop estimates are stated for. -/
noncomputable def loopMax (ω : Omega d L W) (E t : ℝ) (n : ℕ) : ℝ :=
  ⨆ p : (Fin n → Bool) × (Fin n → Zd d L), ‖gloop d L W ω E t p.1 p.2‖

end RBM.Gauss
