/-
Release check for T2167 (dispatcher V1, Mon Oct  5 02:38 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19, §29, §45 O2).
S3-10b: non-alternating good-set inputs part 2: constants and class, the fields of `GridAssemblyHypN`, the
quadratic-variation constant, `subGaussStop_nonAltN`.  Section 1: the merged names it builds on (S3-10a
`Induction/NQGood1`, T2166 691566a; `GridGoodN`, `GridAssemblyN`, `AzumaProxyN`, `StepDecompN`, `GridDuhamelN`,
`ScaleFacts`, the instance data) and the downstream pins.  Section 2: the pinned vocabulary (six definitions),
in namespace `RBM.Ind.T2167Check` here; T2167 defines it in `RBM.Ind` verbatim.
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2167-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names -/

-- S3-10a (`Induction/NQGood1`)
#check @RBM.Ind.driftTensorN
#check @RBM.Ind.driftTensorN_norm_le_of_goodSet
#check @RBM.Ind.driftTensorN_far_of_goodSet
#check @RBM.Ind.nqGood1C
#check @RBM.Ind.nqGood1C_pos
#check @RBM.Ind.hker_of_case1N
#check @RBM.Ind.nqGood1_mE_im_ge
#check @RBM.Ind.nqGood1_qvFormN_le_of_bounds
#check @RBM.Ind.qvFormN_le_of_goodSetN
#check @RBM.Ind.loopShiftErrN
#check @RBM.Ind.nqGood1_ellT_mono
#check @RBM.Ind.eeShiftErrN
#check @RBM.Ind.norm_STeeM_shiftN_le
-- good set, exit time, assembly, Azuma proxy, step decomposition, Duhamel vocabulary
#check @RBM.Gauss.Sizes.GoodSetN
#check @RBM.Path.goodExitTauN
#check @RBM.Path.mem_of_lt_gridExitTauN
#check @RBM.Path.goodExitMeasN
#check @RBM.Ind.qvFormN
#check @RBM.Ind.GridAssemblyHypN
#check @RBM.Ind.AssembledN
#check @RBM.Ind.assembledN
#check @RBM.Ind.GridAssemblyNInst.gridAsm_bundle
#check @RBM.Ind.azumaSubGN
#check @RBM.Ind.zero_mem_goodSetN_of_levels
#check @RBM.Ind.azumaProxy_pathH_zero_of_s_zero
#check @RBM.Ind.azumaProxy_subG_goodExit
#check @RBM.Ind.azumaProxy_pos_gridExitTauN
#check @RBM.Ind.ZvecN
#check @RBM.Ind.stoppedEdgeN
#check @RBM.Ind.SubGaussStopN
#check @RBM.Ind.Ugen
#check @RBM.Ind.AvecN
-- scales, times, labels
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.STBctl_pos
#check @RBM.Gauss.Sizes.STBctl_mono
#check @RBM.Bparam
#check @RBM.ellT
#check @RBM.mE
#check @RBM.Gauss.etaT
#check @RBM.Gauss.etaT_pos
#check @RBM.Green.etaT_le_of_le
#check @RBM.Gauss.Sizes.STLKM
#check @RBM.Gauss.Sizes.STeeM
#check @RBM.Gauss.Sizes.STdiamInf
#check @RBM.Path.gridStep
#check @RBM.Path.gridTime
#check @RBM.Path.pathH
#check @RBM.Path.gridTime_last
#check @RBM.Gauss.Sizes.ST_gridTime_zero
#check @RBM.Gauss.Sizes.ST_gridTime_mono
#check @RBM.Gauss.Sizes.ST_gridStep_nonneg
-- instance data
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.SizesInst.sz0_values
#check @RBM.Gauss.InductionDefsInst.sInst
#check @RBM.Gauss.GridGoodNInst.vg
#check @RBM.Gauss.GridGoodNInst.Kg
#check @RBM.Gauss.GridGoodNInst.grid_data
#check @RBM.Ind.AzumaProxyNInst.Einst
#check @RBM.Ind.AzumaProxyNInst.sig3
#check @RBM.Ind.AzumaProxyNInst.Einst_abs_lt
#check @RBM.Ind.AzumaProxyNInst.sInst_nonneg
#check @RBM.Ind.AzumaProxyNInst.sInst_le_vg
#check @RBM.Ind.AzumaProxyNInst.vg_lt_one
#check @RBM.Ind.AzumaProxyNInst.Γ4
#check @RBM.Ind.AzumaProxyNInst.Λ3
#check @RBM.Ind.AzumaProxyNInst.Φ1
#check @RBM.Ind.NQGood1Inst.zero_mem_goodSetN_inst_grid
#check @RBM.Ind.NQGood1Inst.aFar
#check @RBM.Ind.NQGood1Inst.diam_aFar
-- downstream pins (S3-12)
#check @RBM.Gauss.Sizes.STNQConcl
#check @RBM.Gauss.Sizes.STOeqNQ

/-! ## 2. Pinned vocabulary (T2167 target 1; defined in `RBM.Ind` verbatim) -/

noncomputable section

namespace RBM.Ind.T2167Check

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Ind
open scoped NNReal

/-- **The kernel class of the non-alternating case** (RBM2D `nonAltCls`, `NonAltGood:1168`):
`Cls i δ X :⇔ δ ≤ W^{-Dc}` and `‖X b‖ ≤ δ` when `ℓ_{u_i} W^{τ'} ≤ diam_∞ b` -- exactly the hypotheses
`hδD`, `hXcls` of `hker_of_case1N` at `s = u_i`, `D = Dc`; the radius is the `L^∞` one of `GoodSetN`. -/
def nonAltClsN (d L : ℕ) {k : ℕ} (g W τ' Dc : ℝ) (u : ℕ → ℝ) :
    ℕ → ℝ → ((Fin k → Zd d L) → ℂ) → Prop :=
  fun i δ X => δ ≤ W ^ (-Dc) ∧
    ∀ b : Fin k → Zd d L, ellT L g (u i) * W ^ τ' ≤ (STdiamInf b : ℝ) → ‖X b‖ ≤ δ

/-- **The kernel weight `κ_{i,m}`** (RBM2D `kappaNonAlt`, `NonAltGood:1174`): the coefficient of `M`
in `hker_of_case1N`, `W^{Cε} ((g²+|1-u_i|)/(g²+|1-u_m|))^{k-1}`, `C = nqGood1C d k Λg κ'`. -/
def kappaNonAltN (d k : ℕ) (Λg κ' g W ε : ℝ) (u : ℕ → ℝ) (i m : ℕ) : ℝ :=
  W ^ (nqGood1C d k Λg κ' * ε) * ((g ^ 2 + |1 - u i|) / (g ^ 2 + |1 - u m|)) ^ (k - 1)

/-- **The additive decay-error weight `ε_{i,m}`** (RBM2D `epsNonAlt`, `NonAltGood:1179`): the
coefficient of `δ` in `hker_of_case1N`, the constant `W^C`. -/
def epsNonAltN (d k : ℕ) (Λg κ' W : ℝ) (_i _m : ℕ) : ℝ :=
  W ^ nqGood1C d k Λg κ'

/-- **The drift level** (RBM2D `dDriftNonAlt`, `NonAltGood:1184`): the right side of
`driftTensorN_norm_le_of_goodSet`, `Γ(ΓΦ)(B_u^k/η_u)((k-1) + kΓΦ)`; no additive `W^{-D'}`. -/
def dDriftNonAltN {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (k : ℕ) (Γ Φ : ℝ) : ℝ :=
  Γ * (Γ * Φ) * ((sz.Bctl n u) ^ k / etaT E u) * (((k : ℝ) - 1) + (k : ℝ) * (Γ * Φ))

/-- **The variance majorant** (RBM2D `qvBdNonAlt`, `NonAltGood:1385`): the right side of
`nqGood1_qvFormN_le_of_bounds` at `(v, w) = (u, w)` with `M_ee = Γ(ΓΛ)B_u^{2k}/η_u + W^{-D''}` and
`δ = W^{-D''}`. -/
def qvBdNonAltN {d : ℕ} (sz : Sizes d) (n : ℕ) (E : ℝ) (k : ℕ)
    (Λg κ' ε Γ Λ D'' u w : ℝ) : ℝ :=
  (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
      ((sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - w|)) ^ (k - 1)) *
    ((((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
        ((sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - w|)) ^ (k - 1)) *
      (Γ * (Γ * Λ) * ((sz.Bctl n u) ^ (2 * k) / etaT E u) + ((sz.W n : ℕ) : ℝ) ^ (-D'')) +
      ((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' * ((sz.W n : ℕ) : ℝ) ^ (-D'')) +
    ((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' *
      (((sz.W n : ℕ) : ℝ) ^ k * ((sz.W n : ℕ) : ℝ) ^ (-D''))

/-- **The sub-Gaussian proxy of the `j`-th propagated increment towards `u_m`** (RBM2D `cQVNonAlt`,
`NonAltGood:1495`): `Δ · k · qvBdNonAltN(u_{j+1}, u_m)` (the label `a` does not enter). -/
def cQVNonAltN {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (Λg κ' ε : ℝ)
    (Γ Λ : ℕ → ℝ) (D'' : ℝ) (m : ℕ) (_a : Fin k → Zd d (sz.L n)) (j : ℕ) : ℝ≥0 :=
  (gridStep s v K n * ((k : ℝ) * qvBdNonAltN sz n (E n) k Λg κ' ε (Γ n) (Λ n) D''
    (gridTime s v K n (j + 1)) (gridTime s v K n m))).toNNReal

end RBM.Ind.T2167Check

end
