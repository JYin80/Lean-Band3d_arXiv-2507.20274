/-
Release check for T2229 (dispatcher V1, Mon Oct  5 23:36 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20, §29,
§45 O2, §64 (4), §67, §68, §71).
S6-12a (stochastic layer ST-5, Step 6, regime (ii), Ward decomposition `6:137-141`): proves the merged pin `STExpWardII`
(`RBM3D/Induction/Step6Pins.lean:376`, text unchanged) in the new file `RBM3D/Induction/ExpWardII.lean`; deletes its one owed
registry line (`RBM3D/Test/Axioms.lean:236` on `main` 0d5868e).  The integrated pin `STExpIntII` (`:441`) is S6-12b (next
ticket, `Induction/ExpIntII.lean`), not this one.
Section 1: the merged names the proof uses (exact namespaces, from the enclosing `namespace … end` blocks; file and last
commit on `main` 0d5868e), and the Mathlib lemmas of the route (modules imported below).
Section 2: the statements of the public theorems of `ExpWardII.lean` as closed `Prop`s, in the temporary namespace
`RBM.Gauss.Sizes.T2229Check` (T2229 proves each, same name, in `RBM.Gauss.Sizes`).
Section 3: the statements of the instances T2229 compiles (`RBM.Gauss.Step6Inst`; merged data `szB` (`L = 4`, `W_n = n + 4`,
`lam = 1`), `zB`, regime (ii) times `(15/16, 31/32)`), as `Prop`-valued `example`s (no proof obligation).
Statement and `#check` only: no theorem, no proof, no placeholder.  Never imported or merged.
Imports: merged modules only, not `RBM3D`.
Run from the main worktree: `lake env lean docs/tickets/checks/T2229-check.lean`.
-/
import RBM3D.Induction.Step6Kit
import RBM3D.Induction.WardII
import RBM3D.Induction.ExpAvg
import RBM3D.Induction.ExpEtermsA
import RBM3D.Induction.ExpDuhamel
import RBM3D.Loop.KLUnique
import RBM3D.Path.Walk
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Dedup

/-! ## 1. Merged names -/

-- `RBM3D/Induction/Step6Pins.lean` (cda3bb2; S6-01 = T2204): the pin, its conclusion, its vocabulary, its instances
#check @RBM.Gauss.Sizes.STExpWardII
#check @RBM.Gauss.Sizes.STExpWardIIConcl
#check @RBM.Gauss.Sizes.STExpIntII
#check @RBM.Gauss.Sizes.STExpAvgU
#check @RBM.Gauss.Sizes.STExpErr
#check @RBM.Gauss.Sizes.STIngR6
#check @RBM.Gauss.Sizes.STStep6II
#check @RBM.Gauss.Sizes.STStep6Concl
#check @RBM.Gauss.Step6Inst.InstIng6Concl
#check @RBM.Gauss.Step6Inst.inst_ing6_II
#check @RBM.Gauss.Step6Inst.inst_step6II
#check @RBM.Gauss.Step6Inst.inst_expWardII
#check @RBM.Gauss.Step6Inst.inst_expIntII

-- `RBM3D/Induction/Step6Kit.lean` (9e0d6a7; S6-02 = T2211): the consumer (§45 O2) and the glue used
#check @RBM.Gauss.Sizes.ST_step6_caseII_of_pins
#check @RBM.Gauss.Sizes.st6_expAvgU_of_pin
#check @RBM.Gauss.Sizes.st6_prec_det_iff
#check @RBM.Gauss.Sizes.st6_flowE_le
#check @RBM.Gauss.Sizes.st6_mE_im_ge
#check @RBM.Gauss.Step6Inst.inst_skeleton6II

-- `RBM3D/Induction/WardII.lean` (8ec98a6; S5-28 = T2148): `(WI_calL)`, `(WI_calK)` summed over the first label, samplewise
#check @RBM.Gauss.Sizes.stWardII_identity

-- merged proofs of the other premises of `inst_skeleton6II` (instance target 2)
#check @RBM.Gauss.Sizes.stExpLKLKHi_holds
#check @RBM.Gauss.Sizes.stImproveExpAver_holds
#check @RBM.Gauss.Sizes.stExpDuhamelZ_holds
#check @RBM.Gauss.Sizes.LWtermEXP

-- `RBM3D/Induction/Step2Defs.lean` (86124dc), `Induction/Defs.lean` (64bdfd3): `𝓛`, `𝓛 - 𝒦` of a matrix, `𝒦`, the flow
#check @RBM.Gauss.Sizes.STLM
#check @RBM.Gauss.Sizes.STLKM
#check @RBM.Gauss.Sizes.STLM_seqHflow
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE

-- `RBM3D/Loop/KLTree.lean` (b06ff9b), `Loop/KLUnique.lean`: `𝒦^{(1)} = m`, cyclic invariance of `𝒦`
#check @RBM.Loop.KLK
#check @RBM.Loop.KLK_one
#check @RBM.Loop.KLK_rotate

-- `RBM3D/Loop/GLoopFlow.lean` (868b3b4), `Loop/GLoop.lean` (e0c58e6), `Path/Walk.lean` (ddf5f74), `Gauss/FineModel.lean`:
-- the loops, the envelope, measurability, the law
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.Sizes.norm_Lloop_le
#check @RBM.Gauss.Sizes.walk_measurable_Lloop
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.seqHflow
#check @RBM.Gauss.Sizes.seqHflow_isHermitian
#check @RBM.Gauss.Sizes.isProbabilityMeasure_seqP
#check @RBM.Gauss.etaT
#check @RBM.Gauss.etaT_pos
#check @RBM.Gauss.etaT_eq_zt_im

-- `RBM3D/Kernel/Evolution.lean` (ff8d36d), `Induction/ZeroModeCalc.lean` (d1cb5a6): `P^{(i)}`, `Q^{(i)}`, `Q^{(A)}`
#check @RBM.avgOp
#check @RBM.zeroModeOp
#check @RBM.zeroModeSet
#check @RBM.norm_zeroModeOp_le
#check @RBM.norm_zeroModeSet_le
#check @RBM.zeroModeSet_sub

-- `RBM3D/Defs/Sizes.lean` (0a873f1), `Defs/Params.lean` (c3f3d5d), `Defs/StochDomAt.lean` (9e2b00f), `Defs/Semicircle.lean`
-- (fbc9870): sizes, `W^{-d}B_{u,0}`, `≺`, `m`
#check @RBM.Gauss.Sizes.size
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Bparam
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.tendsto_size
#check @RBM.StochDomAt.add
#check @RBM.StochDomAt.precomp_param
#check @RBM.StochDomAt.of_le_left
#check @RBM.mE
#check @RBM.mE_im
#check @RBM.mE_im_pos
#check @RBM.mSigma

-- `RBM3D/Induction/Step5Pins.lean` (d7da51e), `Step5Kit.lean` (85e43db), `Step34Pins.lean` (fc76526): regime, index sets,
-- glue, instance data
#check @RBM.Gauss.Sizes.STReg5II
#check @RBM.Gauss.Sizes.STIdx2P
#check @RBM.Gauss.Sizes.STSigMixed
#check @RBM.Gauss.Sizes.st5_prec_mono
#check @RBM.Gauss.Sizes.st5_t_lt_one
#check @RBM.Gauss.Step5Inst.szB_reg5II
#check @RBM.Gauss.Step34Inst.szB
#check @RBM.Gauss.Step34Inst.zB
#check @RBM.Gauss.Step34Inst.flow_zB

-- Mathlib (modules imported above): finite sums, differences, quotients and imaginary parts under the integral,
-- integrability of a bounded measurable function, the list of `Finset.univ : Finset (Fin 2)`
#check @MeasureTheory.integral_finsetSum
#check @MeasureTheory.integral_sub
#check @MeasureTheory.integral_div
#check @integral_im
#check @integral_ofReal
#check @MeasureTheory.Integrable.of_bound
#check @Finset.length_toList
#check @Finset.nodup_toList

/-! ## 2. Statements of the public theorems of `ExpWardII.lean` (closed `Prop`s) -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes.T2229Check

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ### 1. Deterministic, one size (`|E| < 2`, `0 ≤ u < 1`) -/

-- `6:138-140`, first slot: the expectation of the merged samplewise identity `stWardII_identity` (`WardII.lean:143`):
-- `f - Q^{(1)} f = Im 𝔼(𝓛-𝒦)^{(1)}_{u,+,a₂} / (N η_u)` for `σ₁ ≠ σ₂` (`f = STExpErr`, `𝒦^{(1)} = m`).
def expWII_slot0 : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {E u : ℝ}, |E| < 2 → 0 ≤ u → u < 1 →
    ∀ {σ : Fin 2 → Bool}, σ 0 ≠ σ 1 → ∀ a : Fin 2 → Zd d (sz.L n),
      sz.STExpErr n E u σ a - RBM.zeroModeOp d (sz.L n) 0 (fun b => sz.STExpErr n E u σ b) a =
        ((((∫ ω, sz.Lloop n E u (fun _ : Fin 1 => true) (fun _ => a 1) ω ∂(sz.seqP)) -
            RBM.mSigma E true).im : ℝ) : ℂ) /
          (((sz.size n : ℕ) : ℂ) * (RBM.Gauss.etaT E u : ℂ))

-- second slot (new: the merged identity sums over the first label only): through the rotation `(σ,a) ↦ (σ∘swap, a∘swap)` of the
-- 2-loop (trace cyclicity for `𝓛`, `KLK_rotate` for `𝒦`) the second slot is the first slot of the rotated loop.
def expWII_slot1 : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {E u : ℝ}, |E| < 2 → 0 ≤ u → u < 1 →
    ∀ {σ : Fin 2 → Bool}, σ 0 ≠ σ 1 → ∀ a : Fin 2 → Zd d (sz.L n),
      sz.STExpErr n E u σ a - RBM.zeroModeOp d (sz.L n) 1 (fun b => sz.STExpErr n E u σ b) a =
        ((((∫ ω, sz.Lloop n E u (fun _ : Fin 1 => true) (fun _ => a 0) ω ∂(sz.seqP)) -
            RBM.mSigma E true).im : ℝ) : ℂ) /
          (((sz.size n : ℕ) : ℂ) * (RBM.Gauss.etaT E u : ℂ))

-- `Q^{({1,2})} = Q^{(1)} ∘ Q^{(2)}` (either order of `Finset.univ.toList`): `T - Q_iQ_jT = (T - Q_iT) + Q_i(T - Q_jT)` and
-- `‖Q_i g‖_∞ ≤ 2‖g‖_∞` (`norm_zeroModeOp_le`); any tensor.
def expWII_two_slot_bound : Prop :=
  ∀ {d L : ℕ} [NeZero L] (T : (Fin 2 → Zd d L) → ℂ) {M : ℝ},
    (∀ b, ‖T b - RBM.zeroModeOp d L 0 T b‖ ≤ M) → (∀ b, ‖T b - RBM.zeroModeOp d L 1 T b‖ ≤ M) →
      ∀ a, ‖T a - RBM.zeroModeSet d L (Finset.univ : Finset (Fin 2)) T a‖ ≤ 3 * M

-- `(N η_u)⁻¹ ≤ (Im m)⁻¹ W^{-d}B_{u,0}` (`η_u = (1-u) Im m`, `W^{-d}B_{u,0} ≥ W^{-d}(L^d(1-u))⁻¹ = (N(1-u))⁻¹`): every
-- regime, every `d`.
def expWII_inv_Neta_le : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {E u : ℝ}, |E| < 2 → u < 1 →
    (((sz.size n : ℕ) : ℝ) * RBM.Gauss.etaT E u)⁻¹ ≤ ((RBM.mE E).im)⁻¹ * sz.Bctl n u

-- the decomposition bound at one size, from a bound `M` of the one-point averages (`6:138-140`, constant `3`).
def expWII_det_bound : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {E u : ℝ}, |E| < 2 → 0 ≤ u → u < 1 →
    ∀ {σ : Fin 2 → Bool}, σ 0 ≠ σ 1 → ∀ {M : ℝ},
      (∀ x : Zd d (sz.L n),
        ‖(∫ ω, sz.Lloop n E u (fun _ : Fin 1 => true) (fun _ => x) ω ∂(sz.seqP)) - RBM.mSigma E true‖ ≤ M) →
      ∀ a : Fin 2 → Zd d (sz.L n),
        ‖sz.STExpErr n E u σ a -
            RBM.zeroModeSet d (sz.L n) (Finset.univ : Finset (Fin 2)) (fun b => sz.STExpErr n E u σ b) a‖ ≤
          3 * (M * (((sz.size n : ℕ) : ℝ) * RBM.Gauss.etaT E u)⁻¹)

/-! ### 2. Along the sequence (deterministic `Prec`, uniform in `u ∈ [s,t]`) -/

-- the conclusion `STExpWardIIConcl` from `(res_ELK_n=1)` uniformly in `u` (`STExpAvgU`), bulk `|E_n| ≤ 2 - κ`; no regime,
-- no flow: both sides are deterministic (`st6_prec_det_iff`), `(Im m)⁻¹ ≤ 2/√(2κ)` is absorbed into `N^{τ/2}`.
def STExpWardIIConcl_of_avgU : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), sz.SizeTendsto → ∀ {κ : ℝ}, 0 < κ → ∀ {E s t : ℕ → ℝ},
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
      STExpAvgU sz E s t → STExpWardIIConcl sz E s t

-- the pin `STExpWardII` (`Step6Pins.lean:376`, unchanged), every `d`
def stExpWardII_holds : Prop := ∀ d : ℕ, STExpWardII d

end RBM.Gauss.Sizes.T2229Check

/-! ## 3. Statements of the instances (`RBM.Gauss.Step6Inst`; `szB`, `zB`, regime (ii) at `(15/16, 31/32)`) -/

namespace RBM.Gauss.Step6Inst.T2229Check

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst

-- statement of `inst_expWardII_holds` (= `inst_expWardII (stExpWardII_holds 3)`, `Step6Pins.lean:613`)
example : Prop :=
  InstIng6Concl (fun sz E s t => STExpAvgU sz E s t → STExpWardIIConcl sz E s t) szB zB
    (fun _ => 15 / 16) (fun _ => 31 / 32)

-- statement of `inst_skeleton6II_Wd` (= `inst_skeleton6II` (`Step6Kit.lean:1116`) with the merged `stExpLKLKHi_holds 3`,
-- `stImproveExpAver_holds 3`, `stExpDuhamelZ_holds 3` and `stExpWardII_holds 3`; open: `LWtermEXP` (LW-14), `STExpIntII` (S6-12b))
example : Prop :=
  LWtermEXP 3 → STExpIntII 3 →
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32)

-- statement of `inst_expWII_concl` (`STExpWardIIConcl_of_avgU` at `szB`, the flow `zB`, `κ = 1/10`)
example : Prop :=
  STExpAvgU szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) →
    STExpWardIIConcl szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32)

-- statement of `inst_expWII_inv_Neta_le` (`szB`, `n = 0`: `N = 4096`, `E = 0`: `Im m = 1`, `u = 15/16`:
-- `(Nη)⁻¹ = 1/256 ≤ W^{-3}B = (16/17 + 1/4)/64 ≈ 0.0186`)
example : Prop :=
  (((szB.size 0 : ℕ) : ℝ) * RBM.Gauss.etaT 0 (15 / 16))⁻¹ ≤ ((RBM.mE 0).im)⁻¹ * szB.Bctl 0 (15 / 16)

-- statement of `inst_expWII_slot0` (`expWII_slot0` at `szB`, `n = 0`, `E = 0`, `u = 15/16`, `σ = (+,-)`, `a = (0,0)`)
example : Prop :=
  szB.STExpErr 0 0 (15 / 16) ![true, false] ![0, 0] -
      RBM.zeroModeOp 3 (szB.L 0) 0 (fun b => szB.STExpErr 0 0 (15 / 16) ![true, false] b) ![0, 0] =
    ((((∫ ω, szB.Lloop 0 0 (15 / 16) (fun _ : Fin 1 => true) (fun _ => (0 : Zd 3 (szB.L 0))) ω ∂(szB.seqP)) -
        RBM.mSigma 0 true).im : ℝ) : ℂ) /
      (((szB.size 0 : ℕ) : ℂ) * (RBM.Gauss.etaT 0 (15 / 16) : ℂ))

end RBM.Gauss.Step6Inst.T2229Check

end
