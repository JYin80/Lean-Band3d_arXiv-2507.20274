/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.Real.Sqrt
import RBM3D.Defs.Lattice

/-!
# The control parameters `ℓ_t` and `B_{t,K}`

`(eq:ellt)`     `ℓ_t   := min (max (g |1-t|^{-1/2}) 1) L`
`(eq_B_param)`  `B_{t,K} := (g² + |1-t|)^{-1} (K+1)^{-(d-2)} + (L^d |1-t|)^{-1}`

`ℓ_t` is the effective range of the propagator and `B_{t,K}` its decay profile; both
appear in essentially every estimate in the paper.

Two deviations from the paper's notation, both recorded in `docs/paper-deltas.md`:

* `|1-t|^{-1/2}` is written `1 / Real.sqrt |1 - t|`, avoiding `rpow`.  At `t = 1` this
  is `1 / 0 = 0` in Lean, so `ellT` is `1` there rather than undefined; every use site
  in the paper has `t < 1`.
* the exponent `d - 2` is natural subtraction.  For `d ≥ 2` it agrees with the paper,
  and `3 ≤ d` is the standing hypothesis of the paper anyway.
-/

namespace RBM

open Real

/-- `ℓ_t` of `(eq:ellt)`: the effective range of the propagator. -/
noncomputable def ellT (L : ℕ) (g t : ℝ) : ℝ :=
  min (max (g / Real.sqrt |1 - t|) 1) L

/-- `B_{t,K}` of `(eq_B_param)`: the decay profile of the propagator. -/
noncomputable def Bparam (d L : ℕ) (g t : ℝ) (K : ℕ) : ℝ :=
  (g ^ 2 + |1 - t|)⁻¹ * (((K : ℝ) + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * |1 - t|)⁻¹

theorem one_le_ellT {L : ℕ} {g t : ℝ} (hL : 1 ≤ (L : ℝ)) : 1 ≤ ellT L g t :=
  le_min (le_max_right _ _) hL

theorem ellT_le_L {L : ℕ} {g t : ℝ} : ellT L g t ≤ (L : ℝ) := min_le_right _ _

theorem ellT_pos {L : ℕ} {g t : ℝ} (hL : 1 ≤ (L : ℝ)) : 0 < ellT L g t :=
  lt_of_lt_of_le zero_lt_one (one_le_ellT hL)


/-! ### The absorption step of `claim:TTk`

`(eq:key_T_reudce)` ends by turning `Ψ_t² ℓ²` into `(W^dη_t)^{-1}` up to logarithms.  The
deterministic half of that is the inequality below: under the standing hypothesis
`1 - t ≥ ĝ²/L²` of `claim:TTk`, the two parameters are related by
`B_{t,0} ℓ_t² ≤ 3 |1-t|^{-1}` -- with an explicit constant, no `≲`.

Both terms of `B_{t,0}` are accounted for: the first gives exactly `|1-t|^{-1}`, and the
zero-mode term gives `2 L^{2-d} |1-t|^{-1} ≤ 2|1-t|^{-1}`, which is where `d ≥ 2` and the
hypothesis `ĝ² ≤ L²(1-t)` are used.  Since `η_t ≍ 1-t` (`(eta)`), this is the paper's
`ℓ_t² B_{t,0} ≲ |1-t|^{-1} ≲ η_t^{-1}`.
-/

/-- `ℓ_u² ≤ g²/(1-u) + 1`.  Moved here from `Kernel/PropT.lean`, where it was first
needed: it is a fact about `(eq:ellt)` alone. -/
theorem ellT_sq_le {L : ℕ} {g u : ℝ} (hg : 0 ≤ g) (hv : 0 < 1 - u) :
    ellT L g u ^ 2 ≤ g ^ 2 / (1 - u) + 1 := by
  have h0 : 0 ≤ ellT L g u :=
    le_min (le_trans zero_le_one (le_max_right _ _)) (Nat.cast_nonneg L)
  have hx : 0 ≤ g / √|1 - u| := div_nonneg hg (Real.sqrt_nonneg _)
  have hle : ellT L g u ≤ max (g / √|1 - u|) 1 := min_le_left _ _
  have hsq : (g / √|1 - u|) ^ 2 = g ^ 2 / (1 - u) := by
    rw [div_pow, Real.sq_sqrt (abs_nonneg _), abs_of_pos hv]
  calc ellT L g u ^ 2 ≤ (max (g / √|1 - u|) 1) ^ 2 := pow_le_pow_left₀ h0 hle 2
    _ ≤ (g / √|1 - u|) ^ 2 + 1 := by
        rcases le_total (g / √|1 - u|) 1 with h | h
        · rw [max_eq_right h]; nlinarith
        · rw [max_eq_left h]; linarith
    _ = g ^ 2 / (1 - u) + 1 := by rw [hsq]

/-- **`(1-s) ℓ_s² ≤ ĝ² + |1-s|`**, the form `lem:sum_decay` uses: the sum over a ball of
radius `≍ ℓ_s` costs `ℓ_s²`, and this is what turns that into `ĝ² + |1-s|`. -/
theorem one_sub_mul_ellT_sq_le {L : ℕ} {g s : ℝ} (hg : 0 ≤ g) (hs : s < 1) :
    |1 - s| * ellT L g s ^ 2 ≤ g ^ 2 + |1 - s| := by
  have hv : (0 : ℝ) < 1 - s := by linarith
  have habs : |1 - s| = 1 - s := abs_of_pos hv
  have h := ellT_sq_le (L := L) (g := g) (u := s) hg hv
  rw [habs]
  calc (1 - s) * ellT L g s ^ 2 ≤ (1 - s) * (g ^ 2 / (1 - s) + 1) :=
        mul_le_mul_of_nonneg_left h hv.le
    _ = g ^ 2 + (1 - s) := by field_simp

theorem Bparam_mul_ellT_sq_le {d L : ℕ} {g t : ℝ} (hd : 2 ≤ d) (hL : 1 ≤ (L : ℝ))
    (hg : 0 ≤ g) (ht : t < 1) (hgL : g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t)) :
    Bparam d L g t 0 * ellT L g t ^ 2 ≤ 3 / (1 - t) := by
  have hu : (0 : ℝ) < 1 - t := by linarith
  have habs : |1 - t| = 1 - t := abs_of_pos hu
  have hB : Bparam d L g t 0 = (g ^ 2 + (1 - t))⁻¹ + ((L : ℝ) ^ d * (1 - t))⁻¹ := by
    simp [Bparam, habs]
  have hgu : (0 : ℝ) < g ^ 2 + (1 - t) := by positivity
  have hLd : (0 : ℝ) < (L : ℝ) ^ d := by positivity
  have hBnn : 0 ≤ Bparam d L g t 0 := by rw [hB]; positivity
  have hell : ellT L g t ^ 2 ≤ (g ^ 2 + (1 - t)) / (1 - t) := by
    have h := ellT_sq_le (L := L) (g := g) (u := t) hg hu
    calc ellT L g t ^ 2 ≤ g ^ 2 / (1 - t) + 1 := h
      _ = (g ^ 2 + (1 - t)) / (1 - t) := by field_simp
  -- the zero-mode term costs at most `2`
  have hzero : (g ^ 2 + (1 - t)) / ((L : ℝ) ^ d * (1 - t)) ≤ 2 := by
    have hL2d : (L : ℝ) ^ 2 ≤ (L : ℝ) ^ d := pow_le_pow_right₀ hL hd
    have hLd1 : (1 : ℝ) ≤ (L : ℝ) ^ d := one_le_pow₀ hL
    have hstep : (L : ℝ) ^ 2 * (1 - t) ≤ (L : ℝ) ^ d * (1 - t) :=
      mul_le_mul_of_nonneg_right hL2d hu.le
    have hstep2 : (1 - t) ≤ (L : ℝ) ^ d * (1 - t) := by nlinarith
    rw [div_le_iff₀ (by positivity)]
    linarith
  calc Bparam d L g t 0 * ellT L g t ^ 2
      ≤ Bparam d L g t 0 * ((g ^ 2 + (1 - t)) / (1 - t)) :=
        mul_le_mul_of_nonneg_left hell hBnn
    _ = (1 + (g ^ 2 + (1 - t)) / ((L : ℝ) ^ d * (1 - t))) / (1 - t) := by
        rw [hB]; field_simp
    _ ≤ 3 / (1 - t) := by gcongr; linarith

end RBM
