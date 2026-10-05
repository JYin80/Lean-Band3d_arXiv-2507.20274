/-
Release check for T2172 (dispatcher V1, Mon Oct  5 03:23 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19, §29, §45 O2).
S5-08: `res_deccalE_wG` (`Path/LemDecCalEwG`): the hypothesis bundle `E2HypWG`, the pinned statement
`LemDecCalE_wG`, the `d ≥ 3` square-root convolution of the tail, and `lemDecCalE_wG`, for every `σ ∈ {±}²`.
Section 1: the merged names it builds on (S5-05 `Path/LemDecCalE`, T2164 6e63fbc; the light-weight vocabulary of
`Induction/Step2Defs`, `Step2Iterate`; `Green/Pins`; `Induction/Split`; the instance data `sz0`, `szCL`) and the
downstream pins (S5-09: `STLemDecCalEConcl`, second conjunct; the source `STLmaxU` of the loop premise).
Section 2: the pinned bundle `E2HypWG` and the pinned shape `LemDecCalE_wGShape` (the loss as a parameter
`loss`), in namespace `RBM.Path.T2172Check` here; T2172 defines `E2HypWG` in `RBM.Path` verbatim and
`LemDecCalE_wG d` as the body of `LemDecCalE_wGShape d loss` with `loss := lossE2wG`.
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2172-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names -/

-- S5-05 (`Path/LemDecCalE`, T2164 6e63fbc)
#check @RBM.Path.lossE2
#check @RBM.Path.E2Hyp
#check @RBM.Path.LemDecCalE_e1
#check @RBM.Path.LemDecCalE_e1_rpow
#check @RBM.Path.LemDecCalE_e2
#check @RBM.Path.LemDecCalE_floor
#check @RBM.Path.LemDecCalE_floor_A
#check @RBM.Path.LemDecCalE_tailT_anti
#check @RBM.Path.LemDecCalE_tailT_shift
#check @RBM.Path.LemDecCalE_e4c
#check @RBM.Path.LemDecCalE_tailT_le_two_inv_sq
#check @RBM.Path.LemDecCalE_e6_err
#check @RBM.Path.LemDecCalE_e6
#check @RBM.Path.LemDecCalE_e7
#check @RBM.Path.LemDecCalE_e8
#check @RBM.Path.LemDecCalE_e9
#check @RBM.Path.LemDecCalE_e10a
#check @RBM.Path.LemDecCalE_e10b
#check @RBM.Path.LemDecCalE_sum_zd_le
#check @RBM.Path.LemDecCalE_exp_conv
#check @RBM.Path.LemDecCalE_sum_tail_tail
#check @RBM.Path.LemDecCalE_loopPM_le
#check @RBM.Path.LemDecCalE_lk_const_le_lossE2
#check @RBM.Path.LemDecCalE_e2Hyp_zero
#check @RBM.Path.LemDecCalE_inst
-- the light-weight term, its prefactor and its three-loops
#check @RBM.Gauss.Sizes.STEGtM
#check @RBM.Gauss.Sizes.STEGt
#check @RBM.Gauss.Sizes.STavgM
#check @RBM.Gauss.Sizes.STavgErrM
#check @RBM.Gauss.Sizes.STmsig
#check @RBM.Gauss.Sizes.STLM
#check @RBM.Gauss.Sizes.STLIM
#check @RBM.Gauss.Sizes.STavgM_eq_STavgErrM
#check @RBM.Gauss.Sizes.STEGtM_eq_STegtM
#check @RBM.Gauss.Sizes.STLM_eq_STLIM
#check @RBM.Gauss.Sizes.KLloopOf_cutGlue1
#check @RBM.Gauss.Sizes.KLloopOf_cutGlue2
#check @RBM.Gauss.Sizes.ST_Gres_false
#check @RBM.Gauss.Sizes.STblk
#check @RBM.Loop.KLloopOf
#check @RBM.Gauss.loopFine
#check @RBM.Gauss.blockMat
#check @RBM.Gauss.splitEquiv
#check @RBM.Gauss.Gres
#check @RBM.Green.avgErr
#check @RBM.Green.greenBlk
#check @RBM.Green.gexRHS
#check @RBM.Green.loopPM
#check @RBM.Ind.norm_gloop_le_of_le_abs_im
#check @RBM.SB
#check @RBM.sum_norm_SB_row
#check @RBM.mSigma
#check @RBM.norm_mSigma
#check @RBM.mE_im
#check @RBM.mE_im_pos
-- scales, tails, distances
#check @RBM.tailTD
#check @RBM.Gauss.zdistInf
#check @RBM.ellT
#check @RBM.Bparam
#check @RBM.Gauss.Sizes.Bctl
-- downstream pins (S5-09) and the sources of the premises
#check @RBM.Gauss.Sizes.STLemDecCalEConcl
#check @RBM.Gauss.Sizes.STLemDecCalE
#check @RBM.Gauss.Sizes.STIngR5
#check @RBM.Gauss.Sizes.STReg5III
#check @RBM.Gauss.Sizes.STtailTD
#check @RBM.Gauss.Sizes.STLmaxU
#check @RBM.Gauss.Sizes.STAvgU
-- instance data
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.SizesInst.sz0_values
#check @RBM.Gauss.Step5Inst.szCL
#check @RBM.Gauss.Step5Inst.szCL_L_real
#check @RBM.Gauss.Step5Inst.szCL_W_real
#check @RBM.Gauss.Step5Inst.szCL_log_W

/-! ## 2. Pinned vocabulary (T2172 target 1; defined in `RBM.Path` verbatim) -/

noncomputable section

namespace RBM.Path.T2172Check

open Filter Matrix RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Green

/-- **The hypothesis bundle of `res_deccalE_wG`** at `d ≥ 3` (one time `u`, the fine matrix `M`): the merged
`E2Hyp` (S5-05), the floor `(L^d W^{6d})² ≤ W^D` (the `d`-form of RBM2D's `L²W¹² ≤ W^{D/2}`, `LemDecCalE.lean:63`
at `c9a24cf`; it gives the square-root convolution floor `W^{-D} L^{2d} ≤ M_u^{-2}` and a near long-edge term
without `J ≤ W`), and the three-loop bound `|𝓛^{(3)}_{u,σ,a}| ≤ Λ (W^d(1-u))^{-2}` for every `σ`, `a` (clause 2 of
RBM2D `goodSet` at `k = 3`, `GoodSet.lean:49`, used by RBM2D `LemDecCalEwG.lean:592-598`; not in `E2Hyp`; S5-09
source: `STLmaxU`). -/
def E2HypWG {d : ℕ} (sz : Sizes d) (n : ℕ) (E u D Λ K₀ J : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : Prop :=
  E2Hyp sz n E u D Λ K₀ J M ∧
    (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D ∧
    ∀ (σ : Fin 3 → Bool) (a : Fin 3 → Zd d (sz.L n)),
      ‖STLM sz n E u M σ a‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2

/-- **The shape of `res_deccalE_wG`** (`3_5:2322-2325`), deterministic at one time `u`, every `σ ∈ {±}²`, with the
loss as a parameter:
`|ℰ^{G̃,(2)}_{u,σ,a}| ≤ loss · (1-u)⁻¹ [1(|a₁-a₂|_∞ ≤ (log W)^{3/2}) + (W^d|1-u|)^{-1/2} J^{3/2}] T_{u,D}(|a₁-a₂|)`;
the right side after `loss · ` is the second conjunct of `STLemDecCalEConcl` (`Step5Pins.lean:171-177`) at
`J := Jst n u D`.  The power `J^{3/2}` is the paper's (RBM2D's pin has `J²`).  T2172 defines `LemDecCalE_wG d` as
this body with `loss := lossE2wG`. -/
def LemDecCalE_wGShape (d : ℕ) (loss : ℕ → ℕ → ℕ → ℝ → ℝ → ℝ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E u D Λ K₀ J : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
    E2HypWG sz n E u D Λ K₀ J M → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      ‖STEGtM sz n E u M σ a‖ ≤ loss d (sz.L n) (sz.W n) Λ K₀ *
        ((1 - u)⁻¹ *
          ((if ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤
                Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) +
            (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 / 2 : ℝ)) *
          STtailTD sz n u D a)

end RBM.Path.T2172Check

end
