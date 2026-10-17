/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GridDriftBA
import RBM3D.BA.SEforLnBA
import RBM3D.BA.KDecayBA
import RBM3D.Chain.AzumaProxyGen
import RBM3D.Chain.GridEnvelopeGen
import RBM3D.Chain.DecayGenTw
import RBM3D.BA.GridRepTailBA
import RBM3D.BA.GreenLDE
import RBM3D.BA.CombesThomas
import RBM3D.BA.Ward
import RBM3D.BA.KBase

/-!
# The block Anderson readings of T4s2's outputs (BA-T row T5-BA (b), ticket T2492)

The BA instances of the pin `GridGoodNgL`, of the envelope of the grid drift, of the Azuma proxies and of the initial membership of
`GoodSetNg` (supervisor 2351 T4S2-C1).  No merged file is edited.

* §1 target 8: `baGridGood_of` (the four T2486 (a) facts as hypotheses of exact type) and the closure `baGridGood_holds`.
* §2 target 9: the envelope `baGridDrift_envelope` (a private copy of `gridDriftNg_envelope` taking the drift eventually, F1).
* §3 target 10: the Azuma and `Y` readings.
* §4 target 7: the initial membership `baGoodSetNg_init`.
* §5 compiled nonempty instances at `d = 3`, `sz0`, `zSeq`, `flow_sz0`.

Every helper is `private` or prefixed `GridGoodBA_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open private gridEnv_gridTime_le gridEnv_gridTime_nonneg from RBM3D.Induction.GridEnvelopeN

open private gdn_loopOf_eq from RBM3D.Induction.GridDriftN

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Target 8: `GridGoodNgL` at BA -/

/-! ## 2. Target 9: the envelope with the eventual drift (finding F1) -/

/-! ## 3. Target 10: the Azuma and `Y` readings at BA -/

/-! ## 4. Target 7: the initial membership `baGoodSetNg_init`

At `s n = 0` the grid state is `H_0 = g₀ Ψ` (`azumaProxy_Hpath_zerog`) and `u_0 = 0`, `z_0 = E + m`, so `G_0 = M = M^{(B)} ⊗ I` and the
loops are the initial loops: `𝓛_0 = BAMLoop = 𝒦_0` on every well-formed loop (`BAMLoop_trace`, the initial clause of `BAKsol_isKLoopS`,
`M_aa = m`).  Every clause of `GoodSetNg` that carries `𝓛 - 𝒦` has the value `0`.  The clauses that carry `𝓛` alone are bounded
entrywise: `‖M^{(σ)}_{xy}‖ ≤ 1` (Ward) and `‖M^{(σ)}_{xy}‖ ≤ c⁻¹ e^{-c|x-y|}` (Combes-Thomas), the `ee` clause once through
`Σ_b ‖M_{xb}‖ ‖M_{yb}‖ ≤ 1` (Cauchy-Schwarz and Ward). -/

section Init

variable {d : ℕ}

/-! ### 4.1 Lists and products -/

/-! ### 4.2 The entries of `M^{(σ)}` and the bounds on `BAMLoop` -/

/-! ### 4.3 The initial loops: `𝓛_0 = BAMLoop = 𝒦_0` -/

section InitLoops

open scoped Kronecker

variable (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)

/-- **`G_0 = M`**: at `H = g₀ Ψ`, `z_0 = E + m`, the signed Green factors are `M(σ) ⊗ I_{W^d}` (`BAMres_fine_kron`, `ST_Gres_false`). -/
private theorem GridGoodBA_Gres_init (hm : 0 < (BAmF sz lam0 E n).im) (σ : Bool) :
    Gres (blockMat d (sz.L n) (sz.W n) (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)))
        (ztOf (BAmF sz lam0 E n) (E n) 0) σ =
      (BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) σ) ⊗ₖ
        (1 : Matrix (Fin (sz.W n ^ d)) (Fin (sz.W n ^ d)) ℂ) := by
  have hw : (((E n : ℝ) : ℂ) + BAmF sz lam0 E n).im ≠ 0 := by simpa using hm.ne'
  have hk := BAMres_fine_kron d (sz.L n) (sz.W n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n) hw
  have hz0 : ztOf (BAmF sz lam0 E n) (E n) 0 = (E n : ℂ) + BAmF sz lam0 E n := by
    simp [ztOf]
  have htrue : Gres (blockMat d (sz.L n) (sz.W n) (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)))
      (ztOf (BAmF sz lam0 E n) (E n) 0) true =
      BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n) ⊗ₖ
        (1 : Matrix (Fin (sz.W n ^ d)) (Fin (sz.W n ^ d)) ℂ) := by
    unfold Gres
    simp only [↓reduceIte]
    rw [hz0, ← Matrix.nonsing_inv_eq_ringInverse]
    have e1 : blockMat d (sz.L n) (sz.W n) (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) -
        ((E n : ℂ) + BAmF sz lam0 E n) • (1 : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ) =
        (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) -
          ((E n : ℂ) + BAmF sz lam0 E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)).submatrix
          (splitEquiv d (sz.L n) (sz.W n)).symm (splitEquiv d (sz.L n) (sz.W n)).symm := by
      unfold blockMat
      simp only [Matrix.submatrix_sub, Matrix.submatrix_smul, Pi.sub_apply, Pi.smul_apply, Matrix.submatrix_one_equiv]
    rw [e1, Matrix.inv_submatrix_equiv, Matrix.nonsing_inv_eq_ringInverse]
    change (Mres (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (BAmF sz lam0 E n)).submatrix _ _ = _
    rw [hk, Matrix.submatrix_submatrix]
    simp
  cases σ
  · have hH : (blockMat d (sz.L n) (sz.W n) (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n))).IsHermitian := by
      unfold blockMat
      refine Matrix.IsHermitian.submatrix ?_ _
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_smul, (PsiI_isHermitian d _ _).eq,
        show star ((lam0 n : ℝ) : ℂ) = ((lam0 n : ℝ) : ℂ) from Complex.conj_ofReal _]
    rw [ST_Gres_false hH, htrue, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
    simp [BAMsigma]
  · rw [htrue]
    simp [BAMsigma]

/-- **`𝓛_0 = BAMLoop`** on the loops `(σ, a)` of length `j ≥ 1` (`loopFine`, `BAMLoop_trace`). -/
private theorem GridGoodBA_loopFine_init (hm : 0 < (BAmF sz lam0 E n).im) {j : ℕ} (hj : 1 ≤ j) (σ : Fin j → Bool)
    (a : Fin j → Zd d (sz.L n)) :
    loopFine d (sz.L n) (sz.W n) (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n))
        (ztOf (BAmF sz lam0 E n) (E n) 0) σ a =
      BAMLoop d (sz.L n) (sz.W n) (BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)))
        (loopOf σ a) := by
  rw [BAMLoop_trace d (sz.L n) (sz.W n) _ hj σ a]
  unfold loopFine loopM
  simp only [GridGoodBA_Gres_init sz lam0 E n hm]

/-- `BAMLoop` of a one-loop is `m(σ)`: `M(σ)_{aa} = m` or `m̄` (`BAMB_diag_eq`). -/
private theorem GridGoodBA_BAMLoop_one_loop {L : ℕ} [NeZero L] {W : ℕ} {g : ℝ} {z m : ℂ} (h : BASelf d L g z m) (s : Bool)
    (a : Zd d L) :
    BAMLoop d L W (BAMsigma d L (BAMB d L g z m)) ⟨[s], [a]⟩ = PropSpin m s := by
  unfold BAMLoop
  simp only [LoopIdx.length, List.length_singleton, Nat.sub_self, pow_zero, one_mul, List.rotate_zero, List.zip_cons_cons,
    List.zip_nil_right, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  cases s
  · simp [BAMsigma, PropSpin, Matrix.conjTranspose_apply, BAMB_diag_eq d L g z m h a]
  · simp [BAMsigma, PropSpin, BAMB_diag_eq d L g z m h a]

end InitLoops

/-! ### 4.4 The pair form `𝓔⊗𝓔` at the initial state -/

/-! ### 4.5 The clauses with `𝓛 - 𝒦`: value `0` -/

/-! ### 4.6 `H_0 = g₀ Ψ` is good at one index -/

/-! ### 4.7 The eventual threshold and the theorem -/

end Init

/-! ## 5. Compiled nonempty instances (targets 7-10)

`d = 3`, the preflight sequence `sz0`, the spectral parameters `zSeq` with `flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq`, the grid
`(s, t, K) = (0, 1/32, 4)`.  Every deterministic premise is discharged; `STKboundgL` and `STKwardgL` by the merged `inst_BAKbound` and `baKward_holds`.  What
stays a hypothesis of an example is another gate's pin: `STLKgL`, `STStep2ConclgL` (T1-BA) and `hQ` of target 10 (U3s2-U3s3). -/

end RBM.BA

end
