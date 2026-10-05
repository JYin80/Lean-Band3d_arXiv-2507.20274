/-
Release check for T2171 (dispatcher V1, Mon Oct  5 03:23 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19, §29, §45 O2).
S5-06: `res_deccalE_dif` part 1 (`Path/LemDecCalEdif`): the hypothesis bundle `E2HypDif`, the pinned statement
`LemDecCalE_dif` (proved by S5-07), the bridge `STeeM` -> two six-loops for every `σ ∈ {±}²`, the near and far cut
bounds of one six-loop.  Section 1: the merged names it builds on (S5-05 `Path/LemDecCalE`, T2164 6e63fbc; the loop
vocabulary of `Induction/Step2Defs`, `Step34Pins`, `Step2Iterate`, `Split`; `Green/Pins`; the instance data `sz0`,
`szCL`) and the downstream pins (S5-09: `STLemDecCalEConcl`, third conjunct; the source `STLmaxU` of the loop
premises).  Section 2: the pinned bundle `E2HypDif` and the pinned shape `LemDecCalE_difShape` (the loss as a
parameter `loss`), in namespace `RBM.Path.T2171Check` here; T2171 defines `E2HypDif` in `RBM.Path` verbatim and
`LemDecCalE_dif d` as the body of `LemDecCalE_difShape d loss` with `loss := lossE2dif`.
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2171-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names -/

-- S5-05 (`Path/LemDecCalE`, T2164 6e63fbc)
#check @RBM.Path.lossE2
#check @RBM.Path.E2Hyp
#check @RBM.Path.LemDecCalE_lk
#check @RBM.Path.lemDecCalE_lk
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
#check @RBM.Path.LemDecCalE_e10a
#check @RBM.Path.LemDecCalE_e10b
#check @RBM.Path.LemDecCalE_sum_zd_le
#check @RBM.Path.LemDecCalE_exp_conv
#check @RBM.Path.LemDecCalE_sum_tail_tail
#check @RBM.Path.LemDecCalE_lk_le
#check @RBM.Path.LemDecCalE_loopPM_le
#check @RBM.Path.LemDecCalE_lk_const_le_lossE2
#check @RBM.Path.LemDecCalE_e2Hyp_zero
#check @RBM.Path.LemDecCalE_inst
-- loops of a fine matrix, the quadratic-variation loop and its cuts
#check @RBM.Gauss.Sizes.STLM
#check @RBM.Gauss.Sizes.STLIM
#check @RBM.Gauss.Sizes.STeeM
#check @RBM.Gauss.Sizes.STeeLoop
#check @RBM.Gauss.Sizes.STee
#check @RBM.Gauss.Sizes.STeeM_seqHflow
#check @RBM.Gauss.Sizes.STLM_eq_STLIM
#check @RBM.Gauss.Sizes.STeeLoop_one
#check @RBM.Gauss.Sizes.STeeLoop_two
#check @RBM.Gauss.Sizes.ST_Gres_false
#check @RBM.Gauss.Sizes.STblk
#check @RBM.Loop.KLloopOf
#check @RBM.Gauss.loopFine
#check @RBM.Gauss.loopL
#check @RBM.Gauss.blockMat
#check @RBM.Gauss.splitEquiv
#check @RBM.Gauss.Gres
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
-- downstream pins (S5-09) and the source of the loop premises
#check @RBM.Gauss.Sizes.STLemDecCalEConcl
#check @RBM.Gauss.Sizes.STLemDecCalE
#check @RBM.Gauss.Sizes.STIngR5
#check @RBM.Gauss.Sizes.STReg5III
#check @RBM.Gauss.Sizes.STtailTD
#check @RBM.Gauss.Sizes.STLmaxU
-- instance data
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.SizesInst.sz0_values
#check @RBM.Gauss.Step5Inst.szCL
#check @RBM.Gauss.Step5Inst.szCL_L_real
#check @RBM.Gauss.Step5Inst.szCL_W_real
#check @RBM.Gauss.Step5Inst.szCL_log_W

/-! ## 2. Pinned vocabulary (T2171 target 1; defined in `RBM.Path` verbatim) -/

noncomputable section

namespace RBM.Path.T2171Check

open Filter Matrix RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Green

/-- **The hypothesis bundle of `res_deccalE_dif`** at `d ≥ 3` (one time `u`, the fine matrix `M`): the merged
`E2Hyp` (S5-05), the floor `(L^d W^{6d})² ≤ W^D` (the `d`-form of RBM2D's `L²W¹² ≤ W^{D/2}`, `LemDecCalE.lean:63`
at `c9a24cf`, with `W^{6d}` so that the near long-edge term needs no `J ≤ W`), and the four- and six-loop bounds
`|𝓛^{(k)}_{u,σ,a}| ≤ Λ (W^d(1-u))^{-(k-1)}` for every `σ`, `a` (clause 2 of RBM2D `goodSet` at `k = 4, 6`,
`GoodSet.lean:49`, used by RBM2D `LemDecCalEdif.lean:639, 708`; not in `E2Hyp`; S5-09 source: `STLmaxU`). -/
def E2HypDif {d : ℕ} (sz : Sizes d) (n : ℕ) (E u D Λ K₀ J : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : Prop :=
  E2Hyp sz n E u D Λ K₀ J M ∧
    (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D ∧
    (∀ (σ : Fin 4 → Bool) (a : Fin 4 → Zd d (sz.L n)),
      ‖STLM sz n E u M σ a‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 3) ∧
    ∀ (σ : Fin 6 → Bool) (a : Fin 6 → Zd d (sz.L n)),
      ‖STLM sz n E u M σ a‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 5

/-- **The shape of `res_deccalE_dif`** (`3_5:2327-2334`), deterministic at one time `u`, every `σ ∈ {±}²`, with
the loss as a parameter: for `|a_i - a'_i|_∞ ≤ (log W)^{3/2}`,
`|(ℰ⊗ℰ)^{M,(2)}_{u,σ,a,a'}| ≤ loss · (1-u)⁻¹ [1(|a₁-a₂|_∞ ≤ 4(log W)^{3/2}) + (W^d|1-u|)^{-1/2} J³] T_{u,D}(|a₁-a₂|)²`;
the right side after `loss · ` is the third conjunct of `STLemDecCalEConcl` (`Step5Pins.lean:178-186`) at
`J := Jst n u D`.  T2171 defines `LemDecCalE_dif d` as this body with `loss := lossE2dif`. -/
def LemDecCalE_difShape (d : ℕ) (loss : ℕ → ℕ → ℕ → ℝ → ℝ → ℝ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E u D Λ K₀ J : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
    E2HypDif sz n E u D Λ K₀ J M → ∀ (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)),
      (∀ i : Fin 2, ((zdistInf d (sz.L n) (a i - a' i) : ℕ) : ℝ) ≤
        Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
      ‖STeeM sz n E u M σ a a'‖ ≤ loss d (sz.L n) (sz.W n) Λ K₀ *
        ((1 - u)⁻¹ *
          ((if ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤
                4 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) +
            (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 : ℝ)) *
          STtailTD sz n u D a ^ 2)

end RBM.Path.T2171Check

end
