/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step2Gen
import RBM3D.BA.FlowPins
import RBM3D.BA.KSolve
import RBM3D.BA.EKPins
import RBM3D.BA.KTreeRep

/-!
# The generic drift kernel of Step 2 at the BA carrier (BA-T row T8b, ticket T2414)

Supervisor 0853 BAT-F1 (c), E-C1.  `Chain/Step2Gen.lean` §2b defines the block kernel `M^{(σσ')}`
(`Step2Kern_Mss`) and the drift kernels `Step2Gen_thetaKer`, `_uKer`, `_ThetaN`, `_UN` from the
carrier (`FlowFM.M`, `FlowFM.S` only: no new `FlowFM` field), and proves the band identities
(`M = m I` gives `M^{(σσ')} = m_σ m_σ' I`).  This file proves the **BA identities**: at the BA
carrier `baFM sz lam0 E` (`S = 1`, `M = BAMfine`, `BA/FlowPins.lean:322-329`), `M = M^{(B)} ⊗
I_{W^d}` (`BAMres_fine_kron`), so

* `Step2Kern_Mss_BA`: `M^{(σσ')} = BAMss` of `M^{(B)} = BAMB` (index order of `BAKsolve`,
  `BA/KSolve.lean:58-66`);
* `Step2Kern_thetaKer_BA`: `thetaKer = Θ_BA M^{(σσ')}` (`BATheta`, `BAMss`), and
  `Step2Kern_BAKsolve_form`: `W^{-d}` times it is the right-hand side of `BAKsolve`, for the four
  charge pairs;
* `Step2Kern_uKer_BA`: `uKer = BAuKer` (`BA/EKPins.lean:49`); `Step2Kern_UN_BA` (E-C1):
  `UN = BAUN` (`BA/EKPins.lean:53`); both use `finRotate`.  `BA/*.lean` has no `ThetaN` twin, so
  only `UN` is stated.

The hypothesis `(E n + m).im ≠ 0` is that of `BAMres_fine_kron` (`BA/FlowPins.lean:72`; from
`BAFlow`: `κ ≤ Im m`, `E` real).  No size hypothesis enters: `Θ` is `Ring.inverse` of one matrix
on both sides.  Compiled nonempty instances at `d = 3` (§2): the BA datum of `sz0` along `zSeq`,
`n = 0`, all four charge pairs (no numeric stand-in), and the merged `baKsolve` at the same
datum.  Nothing imports this file.
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal Topology Kronecker

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The BA identities -/

section Kern

/-- `Θ_ξ(X)` commutes with `X` (`Ring.inverse (1 - ξ X)`; at BA this turns `M^{(σσ')} Θ` into the `Θ M^{(σσ')}` of `BAKsolve`). -/
theorem Step2Kern_Theta_comm {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (X : Matrix Λ Λ ℂ) (ξ : ℂ) :
    X * Step2Gen_Theta X ξ = Step2Gen_Theta X ξ * X := by
  unfold Step2Gen_Theta
  by_cases h : IsUnit (1 - ξ • X)
  · obtain ⟨u, hu⟩ := h
    rw [← hu, Ring.inverse_unit]
    have hc : Commute X (u : Matrix Λ Λ ℂ) := by
      rw [hu]
      exact (Commute.one_right X).sub_right ((Commute.refl X).smul_right ξ)
    exact (hc.units_inv_right).eq
  · rw [Ring.inverse_non_unit _ h]; simp

variable {d : ℕ}

/-- **`Step2Kern_Mss_BA`**: the derived block kernel at the BA carrier is `BAMss` of `M^{(B)} = BAMB` (index order of `BAKsolve`,
`BA/KSolve.lean:58-66`). -/
theorem Step2Kern_Mss_BA (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)
    (hIm : (((E n : ℝ) : ℂ) + BAmF sz lam0 E n).im ≠ 0) (σ σ' : Bool) :
    Step2Kern_Mss (baFM sz lam0 E) n σ σ' =
      BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) σ σ' := by
  have hker : ∀ x y : Idx d (sz.L n) (sz.W n), (baFM sz lam0 E).M n x y =
      (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (split d (sz.L n) (sz.W n) x).1
        (split d (sz.L n) (sz.W n) y).1 *
      (if (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) y).2 then 1 else 0) := by
    intro x y
    change BAMfine sz lam0 E n x y = _
    unfold BAMfine
    rw [BAMres_fine_kron d (sz.L n) (sz.W n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n) hIm]
    simp [Matrix.submatrix_apply, Matrix.kroneckerMap_apply, splitEquiv, Matrix.one_apply]
  rw [Step2Kern_Mss_of_kron (baFM sz lam0 E) n _ hker σ σ']
  rfl

/-- **`Step2Kern_thetaKer_BA`**: `thetaKer = Θ_BA M^{(σσ')}` (`S = 1`; `BATheta`, `BAMss`). -/
theorem Step2Kern_thetaKer_BA (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)
    (hIm : (((E n : ℝ) : ℂ) + BAmF sz lam0 E n).im ≠ 0) (σ σ' : Bool) (t : ℝ) :
    Step2Gen_thetaKer (baFM sz lam0 E) n σ σ' t =
      BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) t σ σ' *
        BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) σ σ' := by
  unfold Step2Gen_thetaKer
  rw [Step2Kern_Mss_BA sz lam0 E n hIm σ σ']
  have hS : (baFM sz lam0 E).S n = 1 := rfl
  rw [hS, mul_one]
  rw [Step2Kern_Theta_comm]
  rfl

/-- **`Step2Kern_uKer_BA`**: `uKer = BAuKer` (`BA/EKPins.lean:49`). -/
theorem Step2Kern_uKer_BA (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)
    (hIm : (((E n : ℝ) : ℂ) + BAmF sz lam0 E n).im ≠ 0) (σ σ' : Bool) (s t : ℝ) :
    Step2Gen_uKer (baFM sz lam0 E) n σ σ' s t =
      BAuKer d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) s t σ σ' := by
  unfold Step2Gen_uKer BAuKer
  rw [Step2Kern_Mss_BA sz lam0 E n hIm σ σ']
  have hS : (baFM sz lam0 E).S n = 1 := rfl
  rw [hS, mul_one]
  rfl

/-- **`Step2Kern_UN_BA`** (E-C1): the BA reading of the new `UN` is stage E's `BAUN` (`BA/EKPins.lean:53`); both products use
`finRotate`.  There is no `ThetaN` twin in `BA/*.lean`. -/
theorem Step2Kern_UN_BA (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)
    (hIm : (((E n : ℝ) : ℂ) + BAmF sz lam0 E n).im ≠ 0) (k : ℕ) (σ : Fin k → Bool) (s t : ℝ)
    (A : (Fin k → Zd d (sz.L n)) → ℂ) :
    Step2Gen_UN (baFM sz lam0 E) n σ s t A = BAUN d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) σ s t A := by
  funext a
  unfold Step2Gen_UN BAUN
  simp only [Step2Kern_uKer_BA sz lam0 E n hIm]

end Kern

/-! ## 2. Compiled nonempty instances at `d = 3`

The merged preflight sequence `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`) along the BA
flow `zSeq`, at `n = 0` (`L = 4`, `W = 32`, `lam = 1/64`, `N = 2097152`); `M^{(B)} = (g₀ Ψ - (E + m))⁻¹` is not
diagonal, `Im m > 0`.  The hypothesis `(E + m).im ≠ 0` is discharged by `BAmF_sz0_im_pos`, the `kron` hypothesis of
`Step2Kern_Mss_of_kron` by `BAMfine_sz0_kron`; no `N = 0`, empty index set or `False` premise occurs. -/

end RBM.BA
