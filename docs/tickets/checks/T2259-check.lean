/-
Release check for T2259 (dispatcher V1, Tue Oct  6 04:40 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §80 (2), §80 (1),
§69 A, §64 (4), §45 O2, §29, §20, §17, §16).  S3-24b (ST-3): the proof of the R2* pins `STIterations'`,
`STIterationsII'` (`STIterR'` at its two regimes; hypothesis `STXiBoot'`), through the primed step
`RBM.Gauss.Sizes.iterationsB_step` (= merged `iterationsA_step` with `hboot : STXiBoot'` and `hlow` taken at `w = s`).
Section 1: `#check` of every merged name the ticket cites (exact namespaces; `main` 24b85cd).
Section 2: the pinned statements (the new file proves them; a statement script checks
`example : RBM.Gauss.Sizes.T2259Check.<name> := @<new name>`).
Section 3: well-formedness `example`s (Prop-valued, no proof obligation).
Statement and `#check` only: no proofs, no `sorry`, no `by`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2259-check.lean`.
-/
import RBM3D.Induction.NQEndFlow
import RBM3D.Induction.IterationsA
import RBM3D.Induction.Step34Pins
import RBM3D.Induction.KDecay
import RBM3D.Induction.ScaleFacts
import RBM3D.Green.Pins
import RBM3D.Loop.KLFinal
import RBM3D.Defs.StochDomAt
import RBM3D.Defs.Semicircle

/-! ## 1. Merged names -/

-- the R2* pins and the bridge (`Induction/NQEndFlow` 0f60da2)
#check @RBM.Gauss.Sizes.STXiBoot'
#check @RBM.Gauss.Sizes.STIterR'
#check @RBM.Gauss.Sizes.STIterations'
#check @RBM.Gauss.Sizes.STIterationsII'
#check @RBM.Gauss.Sizes.stXiBoot'_of_stXiBoot

-- the unprimed pins and their vocabulary (`Induction/Step34Pins` fc76526)
#check @RBM.Gauss.Sizes.STXiBoot
#check @RBM.Gauss.Sizes.STIterR
#check @RBM.Gauss.Sizes.STIterations
#check @RBM.Gauss.Sizes.STIterationsII
#check @RBM.Gauss.Sizes.STIterHyp
#check @RBM.Gauss.Sizes.STPsi
#check @RBM.Gauss.Sizes.STAI
#check @RBM.Gauss.Sizes.STAII
#check @RBM.Gauss.Sizes.STRegIterI
#check @RBM.Gauss.Sizes.STCaseI
#check @RBM.Gauss.Sizes.STCaseII
#check @RBM.Gauss.Sizes.STPair
#check @RBM.Gauss.Sizes.STlenL
#check @RBM.Gauss.Sizes.STbootRHS
#check @RBM.Gauss.Sizes.STXiL
#check @RBM.Gauss.Sizes.STXiLK
#check @RBM.Gauss.Sizes.STAvgU
#check @RBM.Gauss.Sizes.STStep2Concl
#check @RBM.Gauss.Sizes.st_Bctl_pos

-- the step of `lem:iterations` and its public tools (`Induction/IterationsA` 6583ca2)
#check @RBM.Gauss.Sizes.IterationsAScale
#check @RBM.Gauss.Sizes.IterationsAScale.Bctl
#check @RBM.Gauss.Sizes.IterationsAScale.t_lt_one
#check @RBM.Gauss.Sizes.iterationsA_step
#check @RBM.Gauss.Sizes.iterationsA_boot_bound
#check @RBM.Gauss.Sizes.iterationsA_xiL_odd_le
#check @RBM.Gauss.Sizes.iterationsA_STPsi_nonneg
#check @RBM.Gauss.Sizes.iterationsA_one_le_STPsi
#check @RBM.Gauss.Sizes.iterationsA_STPsi_anti_k
#check @RBM.Gauss.Sizes.iterationsA_prec_mono_right
#check @RBM.Gauss.Sizes.iterationsA_prec_mono_left
#check @RBM.Gauss.Sizes.iterationsA_prec_absorb
#check @RBM.Gauss.Sizes.iterationsA_prec_rpow
#check @RBM.Gauss.Sizes.iterationsA_prec_one_add_mul
#check @RBM.Gauss.Sizes.st_one_le_XiL
#check @RBM.Gauss.Sizes.st_one_le_XiLK
#check @RBM.Gauss.Sizes.st_prec_one_add_sup
#check @RBM.Gauss.Sizes.iterationsA_avg_of_STAvgU
#check @RBM.Gauss.Sizes.iterationsA_apriori_of_lRB1
#check @RBM.Gauss.Sizes.iterationsA_rela_of_K
#check @RBM.Gauss.Sizes.iterationsA_scale_I
#check @RBM.Gauss.Sizes.iterationsA_scale_II

-- the setting (`Induction/Defs` 64bdfd3, `Defs/Sizes` 0a873f1, `Defs/Semicircle` fbc9870, `Green/Pins` 64bdfd3)
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.STKbound
#check @RBM.Gauss.Sizes.STLK
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.STStep1Loop
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.lemT_lt_one
#check @RBM.abs_lemE_lt_two
#check @RBM.Green.v3_premises_of_stFlow
#check @RBM.Green.perTime_timeIcc_of_forall_seq

-- the uniform `𝒦` bound (`Induction/KDecay` dab074c, `Loop/KLFinal` 471b643)
#check @RBM.Gauss.Sizes.stKbound_timeIcc
#check @RBM.Gauss.Sizes.stKbound_of_flow
#check @RBM.Gauss.Sizes.stKbound_holds

-- `≺` calculus (`Defs/StochDomAt` 9e2b00f)
#check @RBM.Gauss.Sizes.prec_of_le
#check @RBM.Gauss.Sizes.tendsto_size
#check @RBM.StochDomAt.precomp_param

-- instance data (`Induction/Step34Pins` fc76526)
#check @RBM.Gauss.Step34Inst.szB
#check @RBM.Gauss.Step34Inst.zB
#check @RBM.Gauss.Step34Inst.flow_zB
#check @RBM.Gauss.Step34Inst.szB_W_tendsto
#check @RBM.Gauss.Step34Inst.szB_tendsto
#check @RBM.Gauss.Step34Inst.szB_WO
#check @RBM.Gauss.Step34Inst.lemT_zB
#check @RBM.Gauss.Step34Inst.szB_flow_ht
#check @RBM.Gauss.Step34Inst.szB_regIterI
#check @RBM.Gauss.Step34Inst.szB_caseII
#check @RBM.Gauss.Step34Inst.conStInd_const
#check @RBM.Gauss.Step34Inst.InstIterConcl
#check @RBM.Gauss.Step34Inst.inst_iter
#check @RBM.Gauss.Step34Inst.inst_iterations
#check @RBM.Gauss.Step34Inst.inst_iterationsII

/-! ## 2. Pinned statements -/

namespace RBM.Gauss.Sizes.T2259Check

open MeasureTheory Filter
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Target 2**: `RBM.Gauss.Sizes.iterationsB_step` has exactly this type (the binders of the merged
`iterationsA_step`, `IterationsA.lean:1283-1294`, with `STXiBoot` replaced by `STXiBoot'`). -/
def T2259_iterationsB_step : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), Tendsto sz.size atTop atTop →
    ∀ {E s t A T : ℕ → ℝ} {cB cv K : ℝ}, IterationsAScale sz E s t A T cB cv K →
      STXiBoot' sz E s t →
      (∀ m, 1 ≤ m → sz.Prec (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
        (fun n q ω => 1 + sz.Bctl n q.1.1 * STXiLK sz n (E n) q.1.1 m ω)) →
      sz.Prec (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 1 ω) (fun _ _ _ => 1) →
      (∀ m, 1 ≤ m → sz.Prec (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
        (fun n q _ => (etaT (E n) (s n) / etaT (E n) q.1.2) ^ (m - 1))) →
      ∀ {N k : ℕ}, 2 ≤ N → 1 ≤ k →
        (∀ r, 2 ≤ r → r + 1 ≤ N → STIterHyp sz E s t A r k) →
        (∀ r, 2 ≤ r → r ≤ N + 2 → STIterHyp sz E s t A r (k - 1)) →
        STIterHyp sz E s t A N k

/-- **Target 4 (main, case (i))**: `RBM.Gauss.Sizes.stIterations'_holds`. -/
def T2259_stIterations'_holds : Prop := ∀ d : ℕ, STIterations' d

/-- **Target 4 (main, case (ii))**: `RBM.Gauss.Sizes.stIterationsII'_holds`. -/
def T2259_stIterationsII'_holds : Prop := ∀ d : ℕ, STIterationsII' d

/-- **Target 5, instance (1)**: `RBM.Gauss.IterationsBInst.inst_iterations'` has exactly this type
(`STIterations' 3` at `(szB, zB, 7/8, 15/16)`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`; the shape of the merged
`InstIterConcl` `Step34Pins.lean:883` with `STXiBoot'`; the stochastic premises stay hypotheses). -/
def T2259_inst_iterations' : Prop :=
  ∀ Cd : ℝ, 0 < Cd → ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
    (STKbound RBM.Gauss.Step34Inst.szB (STflowE RBM.Gauss.Step34Inst.zB) →
      STLK RBM.Gauss.Step34Inst.szB (STflowE RBM.Gauss.Step34Inst.zB) (fun _ => 7 / 8) →
      STStep1Loop RBM.Gauss.Step34Inst.szB (STflowE RBM.Gauss.Step34Inst.zB) (fun _ => 7 / 8) (fun _ => 15 / 16) →
      STStep2Concl RBM.Gauss.Step34Inst.szB (STflowE RBM.Gauss.Step34Inst.zB) (fun _ => 7 / 8) (fun _ => 15 / 16) Cd →
      STXiBoot' RBM.Gauss.Step34Inst.szB (STflowE RBM.Gauss.Step34Inst.zB) (fun _ => 7 / 8) (fun _ => 15 / 16) →
      ∀ n_ k : ℕ, 2 ≤ n_ → 1 ≤ k →
        (∀ r, 2 ≤ r → r + 1 ≤ n_ → STIterHyp RBM.Gauss.Step34Inst.szB (STflowE RBM.Gauss.Step34Inst.zB)
          (fun _ => 7 / 8) (fun _ => 15 / 16) (fun n => STAI RBM.Gauss.Step34Inst.szB n) r k) →
        (∀ r, 2 ≤ r → r ≤ n_ + 2 → STIterHyp RBM.Gauss.Step34Inst.szB (STflowE RBM.Gauss.Step34Inst.zB)
          (fun _ => 7 / 8) (fun _ => 15 / 16) (fun n => STAI RBM.Gauss.Step34Inst.szB n) r (k - 1)) →
        STIterHyp RBM.Gauss.Step34Inst.szB (STflowE RBM.Gauss.Step34Inst.zB)
          (fun _ => 7 / 8) (fun _ => 15 / 16) (fun n => STAI RBM.Gauss.Step34Inst.szB n) n_ k)

/-- **Target 5, instance (2)**: `RBM.Gauss.IterationsBInst.inst_iterationsII'` (`STIterationsII' 3` at
`(szB, zB, 15/16, 31/32)`). -/
def T2259_inst_iterationsII' : Prop :=
  ∀ Cd : ℝ, 0 < Cd → ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
    (STKbound RBM.Gauss.Step34Inst.szB (STflowE RBM.Gauss.Step34Inst.zB) →
      STLK RBM.Gauss.Step34Inst.szB (STflowE RBM.Gauss.Step34Inst.zB) (fun _ => 15 / 16) →
      STStep1Loop RBM.Gauss.Step34Inst.szB (STflowE RBM.Gauss.Step34Inst.zB) (fun _ => 15 / 16) (fun _ => 31 / 32) →
      STStep2Concl RBM.Gauss.Step34Inst.szB (STflowE RBM.Gauss.Step34Inst.zB) (fun _ => 15 / 16) (fun _ => 31 / 32) Cd →
      STXiBoot' RBM.Gauss.Step34Inst.szB (STflowE RBM.Gauss.Step34Inst.zB) (fun _ => 15 / 16) (fun _ => 31 / 32) →
      ∀ n_ k : ℕ, 2 ≤ n_ → 1 ≤ k →
        (∀ r, 2 ≤ r → r + 1 ≤ n_ → STIterHyp RBM.Gauss.Step34Inst.szB (STflowE RBM.Gauss.Step34Inst.zB)
          (fun _ => 15 / 16) (fun _ => 31 / 32) (fun n => STAII RBM.Gauss.Step34Inst.szB (fun _ => 15 / 16) n) r k) →
        (∀ r, 2 ≤ r → r ≤ n_ + 2 → STIterHyp RBM.Gauss.Step34Inst.szB (STflowE RBM.Gauss.Step34Inst.zB)
          (fun _ => 15 / 16) (fun _ => 31 / 32) (fun n => STAII RBM.Gauss.Step34Inst.szB (fun _ => 15 / 16) n) r (k - 1)) →
        STIterHyp RBM.Gauss.Step34Inst.szB (STflowE RBM.Gauss.Step34Inst.zB)
          (fun _ => 15 / 16) (fun _ => 31 / 32) (fun n => STAII RBM.Gauss.Step34Inst.szB (fun _ => 15 / 16) n) n_ k)

/-! ## 3. Well-formedness (Prop-valued, no proof obligation) -/

-- the two conclusions together, and the unprimed (superseded) pair beside them
example : Prop := STIterations' 3 ∧ STIterationsII' 3
example : Prop := STIterations 3 ∧ STIterationsII 3
-- `STIterR'` at the two regimes is literally the main pins (the `Aof` of case (ii) reads `s`)
example : Prop := STIterR' 3 STRegIterI (fun sz _ n => STAI sz n)
example : Prop := STIterR' 3 STCaseII (fun sz s n => STAII sz s n)
-- the scale facts at the instance data, case (i) and case (ii) (as `iterationsA_scale_I/II` produce them)
example : Prop :=
  IterationsAScale RBM.Gauss.Step34Inst.szB (STflowE RBM.Gauss.Step34Inst.zB) (fun _ => 7 / 8) (fun _ => 15 / 16)
    (fun n => STAI RBM.Gauss.Step34Inst.szB n) (fun n => 2 * (STAI RBM.Gauss.Step34Inst.szB n)⁻¹) 2 2 2
example : Prop :=
  IterationsAScale RBM.Gauss.Step34Inst.szB (STflowE RBM.Gauss.Step34Inst.zB) (fun _ => 15 / 16) (fun _ => 31 / 32)
    (fun n => STAII RBM.Gauss.Step34Inst.szB (fun _ => 15 / 16) n)
    (fun n => (STAII RBM.Gauss.Step34Inst.szB (fun _ => 15 / 16) n) ^ (-1 + 1 / 100 : ℝ)) 1 1 1
-- the one changed slot: the bootstrap right side at `B_s` (R2*) versus at `B_u`
example : Prop :=
  ∀ (sz : Sizes 3) (XL XLK : ℕ → ℝ) (s u : ℝ) (n N p : ℕ),
    STbootRHS 1 XL XLK (sz.Bctl n u) N p ≤ STbootRHS 1 XL XLK (sz.Bctl n s) N p
-- the step's conclusion at the instance data, case (i), `(N, k) = (3, 2)` (as `IterationsA.lean:1954`)
example : Prop :=
  STIterHyp RBM.Gauss.Step34Inst.szB (STflowE RBM.Gauss.Step34Inst.zB) (fun _ => 7 / 8) (fun _ => 15 / 16)
    (fun n => STAI RBM.Gauss.Step34Inst.szB n) 3 2

end RBM.Gauss.Sizes.T2259Check
