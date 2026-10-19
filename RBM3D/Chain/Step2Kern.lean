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
# The generic drift kernel of Step 2 at the block Anderson carrier

`Chain/Step2Gen` defines the block kernel `M^{(σσ')}` (`Step2Kern_Mss`) and the drift kernels
`Step2Gen_thetaKer`, `Step2Gen_uKer`, `Step2Gen_ThetaN`, `Step2Gen_UN` from the carrier (the
fields `M` and `S` only), and proves the identities for the band carriers (`M = m I` gives
`M^{(σσ')} = m_σ m_σ' I`).  This file proves the identities at the block Anderson carrier
`baFM sz lam0 E` (`S = 1`, `M = BAMfine`): `M = M^{(B)} ⊗ I_{W^d}` (`BAMres_fine_kron`), so

* `Step2Kern_Mss_BA`: `M^{(σσ')} = BAMss` of `M^{(B)} = BAMB` (index order of `BAKsolve`);
* `Step2Kern_thetaKer_BA`: `thetaKer = Θ_BA M^{(σσ')}` (`BATheta`, `BAMss`);
* `Step2Kern_uKer_BA`: `uKer = BAuKer`; `Step2Kern_UN_BA`: `UN = BAUN`; both use `finRotate`.

The hypothesis `(E n + m).im ≠ 0` is that of `BAMres_fine_kron`.  No size hypothesis enters: `Θ` is
`Ring.inverse` of one matrix on both sides, and `Step2Kern_Theta_comm` says that it commutes with
that matrix.
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

/-- `Θ_ξ(X)` commutes with `X` (`Ring.inverse (1 - ξ X)`; at the block Anderson carrier this turns `M^{(σσ')} Θ` into the `Θ M^{(σσ')}` of `BAKsolve`). -/
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

/-- `Step2Kern_Mss_BA`: the derived block kernel at the block Anderson carrier is `BAMss` of `M^{(B)} = BAMB` (index order of `BAKsolve`). -/
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

/-- `Step2Kern_thetaKer_BA`: `thetaKer = Θ_BA M^{(σσ')}` (`S = 1`; `BATheta`, `BAMss`). -/
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

/-- `Step2Kern_uKer_BA`: `uKer = BAuKer`. -/
theorem Step2Kern_uKer_BA (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)
    (hIm : (((E n : ℝ) : ℂ) + BAmF sz lam0 E n).im ≠ 0) (σ σ' : Bool) (s t : ℝ) :
    Step2Gen_uKer (baFM sz lam0 E) n σ σ' s t =
      BAuKer d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) s t σ σ' := by
  unfold Step2Gen_uKer BAuKer
  rw [Step2Kern_Mss_BA sz lam0 E n hIm σ σ']
  have hS : (baFM sz lam0 E).S n = 1 := rfl
  rw [hS, mul_one]
  rfl

/-- `Step2Kern_UN_BA`: `Step2Gen_UN` at the block Anderson carrier is `BAUN` (`BA/EKPins`); both products use
`finRotate`. -/
theorem Step2Kern_UN_BA (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)
    (hIm : (((E n : ℝ) : ℂ) + BAmF sz lam0 E n).im ≠ 0) (k : ℕ) (σ : Fin k → Bool) (s t : ℝ)
    (A : (Fin k → Zd d (sz.L n)) → ℂ) :
    Step2Gen_UN (baFM sz lam0 E) n σ s t A = BAUN d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) σ s t A := by
  funext a
  unfold Step2Gen_UN BAUN
  simp only [Step2Kern_uKer_BA sz lam0 E n hIm]

end Kern

end RBM.BA
