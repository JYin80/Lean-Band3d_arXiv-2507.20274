/-
Release check for T2304 (dispatcher V1, Tue Oct  6 14:15 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §62 (1)/(2)/(4),
§80, §85, §90, §91 (2), §95 (3), §105 (1), §29, §20, §17).  S3-22c, the last ticket of the case-(ii) chain
(S3-21 = T2274 95d8b2a, S3-22a = T2284 9664e13, S3-22b = T2292 59a0ab5, S3-22b2 = T2299 2cf288c):
  * the regime-generic self-absorption bootstrap (supervisor `docs/supervisor/2026-10-06-1356.md` §3, O2):
    `RBM.Ind.stBoot_rounds` (abstract), `RBM.Ind.stXiBoot'_of_round` (setting), `RBM.Ind.stXiBootR_of_round`
    (`STIngR`, regime `R` a parameter; reused by S3-18b2 at `STCaseI`);
  * the `newPQ` combination for case (ii): `RBM.Ind.stXiRoundNZ_holds`;
  * the target `RBM.Ind.stOeqQtNZ'_holds : ∀ d, STOeqQtNZ' d` (deletes the owed line `Test/Axioms.lean:126`).
File `RBM3D/Induction/QtNonzeroBoot.lean`.
Section 1: `#check` of every merged name the ticket cites (exact namespaces; `main` 3deaafe).
Section 2: the pin text `STXiRound'` (one round of `(am;asoi222)` with the current-length control).
Section 3: the pinned statements as `Prop`s.
Section 4: well-formedness `example`s (Prop-valued, no proof obligation).
Statement and `#check` only: no proofs, no `sorry`, no `by`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2304-check.lean`.
-/
import RBM3D.Induction.QtNonzeroFlowLift
import RBM3D.Induction.QtNonzeroFlow
import RBM3D.Induction.NQEndFlowLift
import RBM3D.Induction.NQEndFlow
import RBM3D.Induction.NewPQ
import RBM3D.Induction.ZeroModeCalc
import RBM3D.Induction.NQGood1
import RBM3D.Induction.GridGoodN
import RBM3D.Induction.KDecay
import RBM3D.Induction.Step6Kit
import RBM3D.Induction.ExpWardII
import RBM3D.Induction.ContinuityNet
import RBM3D.Induction.ScaleFacts
import RBM3D.Induction.ScaleFacts3
import RBM3D.Induction.Step2Events
import RBM3D.Induction.Step2Defs
import RBM3D.Induction.Step34Pins
import RBM3D.Induction.IterationsB
import RBM3D.Induction.Defs
import RBM3D.Defs.StochDomAt
import RBM3D.Defs.Sizes
import RBM3D.Gauss.FineModel
import RBM3D.Green.Pins
import RBM3D.Kernel.Evolution

/-! ## 1. Merged names -/

-- the R2* pins and the target (`Induction/NQEndFlow` 0f60da2)
#check @RBM.Gauss.Sizes.STXiBoot'
#check @RBM.Gauss.Sizes.STOeqQt'
#check @RBM.Gauss.Sizes.STOeqQtNZ'
#check @RBM.Gauss.Sizes.STIterR'
#check @RBM.Gauss.Sizes.stXiBoot'_of_stXiBoot
#check @RBM.Gauss.Sizes.STNQConcl''
#check @RBM.Gauss.Sizes.STOeqNQ''

-- the case-(ii) uniform projected endpoint (`Induction/QtNonzeroFlowLift` 2cf288c, `Induction/QtNonzeroFlow` 59a0ab5)
#check @RBM.Gauss.Sizes.STNZConcl''
#check @RBM.Gauss.Sizes.STOeqNZ''
#check @RBM.Ind.stOeqNZ''_holds
#check @RBM.Ind.stOeqNZPT''_holds
#check @RBM.Ind.QtNonzeroFlowLiftInst.inst_OeqNZ''

-- the case-(i) analogue and the envelope (`Induction/NQEndFlowLift` d0484be)
#check @RBM.Ind.nqFlowSharp
#check @RBM.Ind.stOeqNQ''_holds

-- `lem: newPQ` and the zero-mode calculus (`Induction/NewPQ` f28fd9c, `Induction/ZeroModeCalc` d1cb5a6,
-- `Kernel/Evolution` ff8d36d)
#check @RBM.Gauss.Sizes.STNewPQ
#check @RBM.Gauss.Sizes.stNewPQ_holds
#check @RBM.Gauss.Sizes.zeroModeCalc_LK_expansion_empty
#check @RBM.zeroModeSet
#check @RBM.zeroModeSet_sub
#check @RBM.norm_zeroModeSet_le

-- the setting and the pins' vocabulary (`Induction/Step34Pins` fc76526, `Induction/Defs` 64bdfd3)
#check @RBM.Gauss.Sizes.STPair
#check @RBM.Gauss.Sizes.STmaxLK
#check @RBM.Gauss.Sizes.STXiL
#check @RBM.Gauss.Sizes.STXiLK
#check @RBM.Gauss.Sizes.STIdiff
#check @RBM.Gauss.Sizes.STCaseI
#check @RBM.Gauss.Sizes.STCaseII
#check @RBM.Gauss.Sizes.STAny
#check @RBM.Gauss.Sizes.STlenL
#check @RBM.Gauss.Sizes.STbootRHS
#check @RBM.Gauss.Sizes.STIngR
#check @RBM.Gauss.Sizes.STStep3II
#check @RBM.Gauss.Sizes.STStep4II
#check @RBM.Gauss.Sizes.STLK
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.STKbound
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.STFlow

-- the crude start (`Induction/NQGood1` 691566a, `Induction/GridGoodN` 2f246bf, `Gauss/FineModel` 0a873f1,
-- `Induction/Step2Defs` 86124dc, `Induction/KDecay` dab074c, `Induction/Step6Kit` 9e0d6a7)
#check @RBM.Ind.STXiLKM_crudeN
#check @RBM.Gauss.Sizes.STXiLKM
#check @RBM.Gauss.Sizes.gridGood_STXiLKM_seqHflow
#check @RBM.Gauss.Sizes.seqHflow_isHermitian
#check @RBM.Gauss.Sizes.STLKM
#check @RBM.Gauss.Sizes.STLM_seqHflow
#check @RBM.Gauss.Sizes.stKbound_timeIcc
#check @RBM.Gauss.Sizes.st6_prec_det_iff

-- the contraction exponent (`Defs/Sizes` 0a873f1, `Induction/ContinuityNet` 5b6cbc1, `Green/Pins` 64bdfd3,
-- `Induction/ScaleFacts` 5d1e6b1, `Induction/ScaleFacts3` 7c3072a)
#check @RBM.Gauss.Sizes.WO
#check @RBM.Gauss.Sizes.Bandwidth
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.lam_sq_mul_pow_ge
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Ind.ContinuityNet.cont_Bctl_eq
#check @RBM.Ind.ContinuityNet.cont_inv_size_le_Bctl
#check @RBM.Gauss.Sizes.RangeCond
#check @RBM.Green.v3_premises_of_stFlow
#check @RBM.Gauss.Sizes.STBctl_pos
#check @RBM.Gauss.Sizes.STBctl_mono
#check @RBM.Gauss.Sizes.st_bootRHS_one

-- the lower-length terms of `(eq:expandQAempty)` (`Induction/ExpWardII` e64e4f0, `Induction/Step2Events` 7f9bfa1)
#check @RBM.Gauss.Sizes.expWII_inv_Neta_le
#check @RBM.Gauss.Sizes.ST_mE_im_ge

-- `≺` algebra (`Defs/StochDomAt` 9e2b00f)
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.prec_of_le
#check @RBM.Gauss.Sizes.tendsto_size
#check @RBM.StochDomAt.of_subset
#check @RBM.StochDomAt.precomp_param
#check @RBM.StochDomAt.of_le_left
#check @RBM.StochDomAt.of_eventually_empty
#check @RBM.StochDomAt.trans
#check @RBM.StochDomAt.add
#check @RBM.StochDomAt.const_mul_left

-- consumers (`Induction/IterationsB` 64ed77f; S3-25 combines with `STXiBoot'` from here)
#check @RBM.Gauss.Sizes.stIterations'_holds
#check @RBM.Gauss.Sizes.stIterationsII'_holds

-- instance data (case (ii): `Induction/Step34Pins` fc76526)
#check @RBM.Gauss.Step34Inst.szB
#check @RBM.Gauss.Step34Inst.szB_W_tendsto
#check @RBM.Gauss.Step34Inst.zB
#check @RBM.Gauss.Step34Inst.flow_zB
#check @RBM.Gauss.Step34Inst.conStInd_const
#check @RBM.Gauss.Step34Inst.szB_caseII
#check @RBM.Gauss.Step34Inst.szB_flow_ht
#check @RBM.Gauss.Step34Inst.InstIngConcl
#check @RBM.Gauss.Step34Inst.inst_ing
#check @RBM.Gauss.Step34Inst.inst_OeqQtNZ

/-! ## 2. Pin

Inside `RBM.Gauss.Sizes.T2304Check`, so that every name resolves as in `Induction/NQEndFlow.lean`.  T2304 defines
`STXiRound'` as `RBM.Gauss.Sizes.STXiRound'` with exactly this body (inside `section Pins` with
`variable {d : ℕ} (sz : Sizes d)`, which gives the same binders `{d} (sz) (E s t)`).  Script diff against the merged
`STXiBoot'` (`NQEndFlow.lean:95-104`) — the only hunks allowed:
* the range of the `XLK` hypotheses `m + 1 ≤ n_` ↦ `m ≤ n_` (the current length is controlled: the round's input);
* the right side `STbootRHS 1 … (sz.Bctl n (s n)) n_ p` ↦
  `(sz.Bctl n q.1.2) ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 + STbootRHS 1 … (sz.Bctl n (s n)) n_ p`
  (the self-absorbing summand of `(am;asoiuw_smalleta)` `3_5:1916`, at the endpoint `u = q.1.2`; R2* unchanged). -/

namespace RBM.Gauss.Sizes.T2304Check

open MeasureTheory ProbabilityTheory Filter Matrix
open RBM RBM.Loop RBM.Path RBM.Gauss
open scoped NNReal ENNReal

/-- **One round of `(am;asoi222)` with the current-length control** (T2304; `lem:STOeq_Qt_nonzero` `3_5:1561`, the
display before "solving which" `3_5:1924-1930`; `lem:STOeq_Qt` `3_5:1362`; DECISIONS §62 (1), §80, §105 (1)): under
`Ξ̂ ≺ Ξ` for every length `m ≤ n_` (the current one included), over the pairs `(v, u)`:
`Ξ̂^{(𝓛-𝒦)}_{v,n_} ≺ B_u^{1/6} XLK n_ u + STbootRHS 1 XL XLK B_s n_ p`. -/
def STXiRound' {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 n_ ω)
      (fun n q _ => (sz.Bctl n q.1.2) ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 +
        STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p)

/-! ## 3. Pinned statements -/

/-- **The abstract self-absorption bootstrap** (§62 (1)): from a crude start `ξ ≺ N^{C₀}` and a round
`ξ ≺ Y ⇒ ξ ≺ N^{-c} Y + R` (every deterministic `Y ≥ 1` of the endpoint `π q`), `ξ ≺ R` after `⌈C₀/c⌉ + 1` rounds.
`RBM.Ind.stBoot_rounds` has exactly this type. -/
def T2304_stBoot_rounds : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), sz.SizeTendsto →
    ∀ {U : ℕ → Type} (π : ∀ n, U n → ℝ) (ξ : ∀ n, U n → sz.SeqΩ → ℝ) (R : ℕ → ℝ → ℝ) (c C₀ : ℝ),
      0 < c → 0 ≤ C₀ → (∀ n u, 1 ≤ R n u) →
      Prec sz (U := U) ξ (fun n _ _ => ((sz.size n : ℕ) : ℝ) ^ C₀) →
      (∀ Y : ℕ → ℝ → ℝ, (∀ n u, 1 ≤ Y n u) →
        Prec sz (U := U) ξ (fun n q _ => Y n (π n q)) →
        Prec sz (U := U) ξ (fun n q _ => ((sz.size n : ℕ) : ℝ) ^ (-c) * Y n (π n q) + R n (π n q))) →
      Prec sz (U := U) ξ (fun n q _ => R n (π n q))

/-- **The bootstrap at a flow setting** (regime-free): `STXiRound' → STXiBoot'`.  `RBM.Ind.stXiBoot'_of_round` has
exactly this type. -/
def T2304_stXiBoot'_of_round : Prop :=
  ∀ {d : ℕ}, 3 ≤ d → ∀ κ ε 𝔠 𝔡 : ℝ, 0 < κ → 0 < ε → ∀ (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) →
      STXiRound' sz (STflowE z) s t → STXiBoot' sz (STflowE z) s t

/-- **The regime-generic bootstrap** (supervisor 1356 O2; reused by S3-18b2 at `R := STCaseI`).
`RBM.Ind.stXiBootR_of_round` has exactly this type. -/
def T2304_stXiBootR_of_round : Prop :=
  ∀ (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop),
    STIngR d R (fun sz E s t => STXiRound' sz E s t) → STIngR d R (fun sz E s t => STXiBoot' sz E s t)

/-- **The case-(ii) round** (the `newPQ` combination on `STNZConcl''`).  `RBM.Ind.stXiRoundNZ_holds` has exactly
this type. -/
def T2304_stXiRoundNZ_holds : Prop := ∀ d : ℕ, STIngR d STCaseII (fun sz E s t => STXiRound' sz E s t)

/-- **T2304 (main)**: `RBM.Ind.stOeqQtNZ'_holds` has exactly this type
(`example : RBM.Gauss.Sizes.T2304Check.T2304_stOeqQtNZ'_holds := @RBM.Ind.stOeqQtNZ'_holds`). -/
def T2304_stOeqQtNZ'_holds : Prop := ∀ d : ℕ, STOeqQtNZ' d

/-- Consumer shape, case (ii) (compiled in the Lean file as
`fun d h => stXiBootR_of_round d STCaseII h`). -/
def T2304_consumer_II : Prop :=
  ∀ d : ℕ, STIngR d STCaseII (fun sz E s t => STXiRound' sz E s t) → STOeqQtNZ' d

/-- Consumer shape, case (i) = S3-18b2 (compiled in the Lean file as `fun d h => stXiBootR_of_round d STCaseI h`). -/
def T2304_consumer_I : Prop :=
  ∀ d : ℕ, STIngR d STCaseI (fun sz E s t => STXiRound' sz E s t) → STOeqQt' d

end RBM.Gauss.Sizes.T2304Check

/-! ## 4. Well-formedness (Prop-valued; no proof obligation) -/

namespace RBM.Gauss.Step34Inst.T2304Check

open RBM RBM.Gauss RBM.Gauss.Sizes

/-- The round at the case-(ii) instance data of the merged `inst_OeqQtNZ` (`Step34Pins.lean:1006`). -/
example : Prop :=
  RBM.Gauss.Sizes.T2304Check.STXiRound' szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32)

/-- Its ingredient form at `(szB, zB, 15/16, 31/32)`, `C_d = 1` (instance (2)). -/
example : Prop :=
  InstIngConcl (fun sz E s t => RBM.Gauss.Sizes.T2304Check.STXiRound' sz E s t) szB zB
    (fun _ => 15 / 16) (fun _ => 31 / 32) 1

/-- The target's ingredient form at the same data (instance (1)). -/
example : Prop :=
  InstIngConcl (fun sz E s t => STXiBoot' sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) 1

/-- The target and the case-(i) consumer target at `d = 3`. -/
example : Prop := STOeqQtNZ' 3

example : Prop := STOeqQt' 3

/-- The Step-3/4 targets of S3-25/S3-26 that consume `STOeqQtNZ'` (supervisor 1356 O4). -/
example : Prop := STStep3II 3 ∧ STStep4II 3

end RBM.Gauss.Step34Inst.T2304Check
