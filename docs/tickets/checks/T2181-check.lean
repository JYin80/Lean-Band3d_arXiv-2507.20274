/-
Release check for T2181 (dispatcher V1, Mon Oct  5 05:59 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §29, §45 O2, §53).
S5-07: `res_deccalE_dif` part 2 (`Path/LemDecCalEdif2`): `lemDecCalE_dif (d : ℕ) : LemDecCalE_dif d`, the statement
T2171 pinned and merged (7d9f111), from T2171's `LemDecCalEdif_STeeM_le`, `_cut_near`, `_cut_far`, for every
`σ ∈ {±}²` and every `a'` in the range.  Section 1: the merged names it builds on (S5-06 `Path/LemDecCalEdif`;
S5-05 `Path/LemDecCalE`, T2164 6e63fbc; S5-08 `Path/LemDecCalEwG`, T2172 3e22603, loss shape and pattern only;
`Defs/Block`, `Defs/Lattice`, `Defs/Tail`; the instance data `sz0`, `szCL`) and the downstream pins (S5-09:
`STLemDecCalEConcl`, third conjunct; `STeeM_seqHflow`; the source `STLmaxU` of the loop premises).
Section 2: the target type `lemDecCalE_difTarget` and the two pinned instance statements `instNear`, `instFar`, in
namespace `RBM.Path.T2181Check` here; T2181 proves `lemDecCalE_dif` in `RBM.Path` and states its two `example`s with
the bodies of `instNear`, `instFar` verbatim.
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2181-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names -/

-- S5-06 (`Path/LemDecCalEdif`, T2171 7d9f111): the pinned vocabulary and the cut bounds
#check @RBM.Path.E2HypDif
#check @RBM.Path.lossE2dif
#check @RBM.Path.LemDecCalE_dif
#check @RBM.Path.LemDecCalEdif_STeeM_le
#check @RBM.Path.LemDecCalEdif_cut_near
#check @RBM.Path.LemDecCalEdif_cut_far
#check @RBM.Path.LemDecCalEdif_hyp_zero
#check @RBM.Path.LemDecCalEdif_inst_a
#check @RBM.Path.LemDecCalEdif_inst_b
-- S5-05 (`Path/LemDecCalE`, T2164 6e63fbc)
#check @RBM.Path.lossE2
#check @RBM.Path.E2Hyp
#check @RBM.Path.LemDecCalE_e10a
#check @RBM.Path.LemDecCalE_sum_tail_tail
#check @RBM.Path.LemDecCalE_e1
#check @RBM.Path.LemDecCalE_e1_rpow
#check @RBM.Path.LemDecCalE_tailT_anti
#check @RBM.Path.LemDecCalE_tailT_shift
#check @RBM.Path.LemDecCalE_e4c
#check @RBM.Path.LemDecCalE_e2
#check @RBM.Path.LemDecCalE_floor
#check @RBM.Path.LemDecCalE_floor_A
#check @RBM.Path.LemDecCalE_tailT_le_two_inv_sq
#check @RBM.Path.LemDecCalE_lk_const_le_lossE2
-- S5-08 (`Path/LemDecCalEwG`, T2172 3e22603): the same loss shape `lossE2 · κ · (1 + log P)^{2d}`; pattern
#check @RBM.Path.lossE2wG
#check @RBM.Path.LemDecCalE_wG
#check @RBM.Path.lemDecCalE_wG
-- the sum over `b, b'`: `S^{(B)}`, the lattice, the tail, the distance
#check @RBM.SB
#check @RBM.SB_apply
#check @RBM.sbKernel
#check @RBM.sum_norm_SB_row
#check @RBM.Zd
#check @RBM.card_Zd
#check @RBM.Gauss.zdistInf
#check @RBM.tailTD
#check @RBM.tailTD_nonneg
#check @RBM.Gauss.Sizes.three_le_L
-- loops of a fine matrix and the downstream pins (S5-09)
#check @RBM.Gauss.Sizes.STeeM
#check @RBM.Gauss.Sizes.STLM
#check @RBM.Gauss.Sizes.STtailTD
#check @RBM.Gauss.Sizes.STee
#check @RBM.Gauss.Sizes.STeeM_seqHflow
#check @RBM.Gauss.Sizes.STLemDecCalEConcl
#check @RBM.Gauss.Sizes.STLemDecCalE
#check @RBM.Gauss.Sizes.STIngR5
#check @RBM.Gauss.Sizes.STLmaxU
-- instance data
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.SizesInst.sz0_values
#check @RBM.Gauss.Step5Inst.szCL
#check @RBM.Gauss.Step5Inst.szCL_L_real
#check @RBM.Gauss.Step5Inst.szCL_W_real
#check @RBM.Gauss.Step5Inst.szCL_log_W
#check @RBM.Gauss.Step5Inst.szCL_one_le_log_W

/-! ## 2. Pinned target type and instance statements (T2181 target 1 and its two `example`s) -/

noncomputable section

namespace RBM.Path.T2181Check

open Filter Matrix RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Green RBM.Gauss.SizesInst RBM.Gauss.Step5Inst

/-- **The type of `lemDecCalE_dif`** (target 1): the merged pin `LemDecCalE_dif` (`Path/LemDecCalEdif.lean:80`)
for every `d`; `E2HypDif` carries `3 ≤ d`. -/
def lemDecCalE_difTarget : Prop :=
  ∀ d : ℕ, LemDecCalE_dif d

/-- **Instance (a), near branch**: `lemDecCalE_dif 3` at T2171's `LemDecCalEdif_inst_a` (`sz0`, `n = 1`: `L = 8`,
`W = 1024`, `E = 1/2`, `u = 0`, `D = 38`, `Λ = K₀ = J = 1`, `M = 0`), `σ = (+,+)`, `a = a' = (0, e₁)`
(`|a₀ - a₁|_∞ = 1 ≤ 4 (log 1024)^{3/2} ≈ 73.0`); `R` is the right side of the pin at these data, and `R > 0`. -/
def instNear : Prop :=
  let a : Fin 2 → Zd 3 (sz0.L 1) := ![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1]
  let R : ℝ := lossE2dif 3 (sz0.L 1) (sz0.W 1) 1 1 *
    ((1 - (0 : ℝ))⁻¹ *
      ((if ((zdistInf 3 (sz0.L 1) (a 0 - a 1) : ℕ) : ℝ) ≤
            4 * Real.log ((sz0.W 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) +
        (((sz0.W 1 : ℕ) : ℝ) ^ 3 * |1 - (0 : ℝ)|)⁻¹ ^ (1 / 2 : ℝ) * (1 : ℝ) ^ (3 : ℝ)) *
      STtailTD sz0 1 0 38 a ^ 2)
  0 < R ∧
    ‖STeeM sz0 1 (1 / 2) 0
        (0 : Matrix (Idx 3 (sz0.L 1) (sz0.W 1)) (Idx 3 (sz0.L 1) (sz0.W 1)) ℂ) ![true, true] a a‖ ≤ R

/-- **Instance (b), far branch**: `lemDecCalE_dif 3` at T2171's `LemDecCalEdif_inst_b` (`szCL`, `n = 0`:
`L = 2·24⁵`, `W = 2^24`, `E = 1/2`, `u = 0`, `D = 42`, `Λ = K₀ = J = 1`, `M = 0`), `σ = (+,-)`, `a = (0, 300 e₁)`,
`a' = (e₂, 300 e₁)` (`|a₀ - a₁|_∞ = 300 > 4 (24 log 2)^{3/2} ≈ 271.4`, `|a₀ - a'₀|_∞ = 1 ≤ (24 log 2)^{3/2}`,
`|a₁ - a'₁|_∞ = 0`); `R` is the right side of the pin at these data, and `R > 0`. -/
def instFar : Prop :=
  let a : Fin 2 → Zd 3 (szCL.L 0) := ![(0 : Zd 3 (szCL.L 0)), Pi.single 0 300]
  let a' : Fin 2 → Zd 3 (szCL.L 0) := ![(Pi.single 1 1 : Zd 3 (szCL.L 0)), Pi.single 0 300]
  let R : ℝ := lossE2dif 3 (szCL.L 0) (szCL.W 0) 1 1 *
    ((1 - (0 : ℝ))⁻¹ *
      ((if ((zdistInf 3 (szCL.L 0) (a 0 - a 1) : ℕ) : ℝ) ≤
            4 * Real.log ((szCL.W 0 : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) +
        (((szCL.W 0 : ℕ) : ℝ) ^ 3 * |1 - (0 : ℝ)|)⁻¹ ^ (1 / 2 : ℝ) * (1 : ℝ) ^ (3 : ℝ)) *
      STtailTD szCL 0 0 42 a ^ 2)
  0 < R ∧
    ‖STeeM szCL 0 (1 / 2) 0
        (0 : Matrix (Idx 3 (szCL.L 0) (szCL.W 0)) (Idx 3 (szCL.L 0) (szCL.W 0)) ℂ) ![true, false] a a'‖ ≤ R

end RBM.Path.T2181Check

end
