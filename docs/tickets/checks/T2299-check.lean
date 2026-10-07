/-
Release check for T2292 (dispatcher V1, Tue Oct  6 11:50 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §62 (2)/(4),
§95 (3), §91 (2), §96 (3), §94 (2), §80, §64 (4), §45 O2, §29, §20, §17).  S3-22b of the case-(ii) chain
(S3-21 = T2274 merged 95d8b2a, S3-22a = T2284 merged 9664e13; S3-22c next), cut now (supervisor
`docs/supervisor/2026-10-06-0956.md` O5) into
  * **T2292** (this ticket): the per-time flow endpoint of `Q^{(A)}(𝓛-𝒦)^{(n_)}`, every `σ`, every `A ⊇ I_diff(σ)`,
    `RBM.Ind.stOeqNZPT''_holds : ∀ d, STOeqNZPT'' d` (file `RBM3D/Induction/QtNonzeroFlow.lean`);
  * **T2292b** (next): the uniform lift `RBM.Ind.stOeqNZ''_holds : ∀ d, STOeqNZ'' d`
    (file `RBM3D/Induction/QtNonzeroFlowLift.lean`).
Section 1: `#check` of every merged name the ticket cites (exact namespaces; `main` 9664e13).
Section 2: the pin texts of T2292 (`STNZConclPT''`, `STOeqNZPT''`) and of T2292b (`STNZConcl''`, `STOeqNZ''`).
Section 3: the pinned statements as `Prop`s.
Section 4: well-formedness `example`s (Prop-valued, no proof obligation).
Statement and `#check` only: no proofs, no `sorry`, no `by`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2292-check.lean`.
-/
import RBM3D.Induction.QtNonzeroEnd
import RBM3D.Induction.NQEndFlow
import RBM3D.Induction.NQEndFlowLift
import RBM3D.Induction.ZeroModeCalc
import RBM3D.Induction.GridGoodN
import RBM3D.Induction.NQLin
import RBM3D.Induction.ScaleFacts
import RBM3D.Induction.ScaleFacts3
import RBM3D.Induction.Step2Events
import RBM3D.Induction.Step2Defs
import RBM3D.Induction.Step34Pins
import RBM3D.Induction.ContinuityNet
import RBM3D.Induction.LemDecCalELip
import RBM3D.Green.Pins
import RBM3D.Path.Walk
import RBM3D.Kernel.Evolution
import RBM3D.Loop.KLFinal
import RBM3D.Gauss.Domination
import RBM3D.Induction.NewPQ

/-! ## 1. Merged names -/

-- the grid endpoint and its instances (`Induction/QtNonzeroEnd` 9664e13)
#check @RBM.Ind.nzGridEndN
#check @RBM.Ind.QtNonzeroEndInst.KB
#check @RBM.Ind.QtNonzeroEndInst.nzEnd_instance
#check @RBM.Ind.QtNonzeroEndInst.nzEnd_instance_collapsed

-- the case-(i) per-time chain = format model, and the R2* pins (`Induction/NQEndFlow` 0f60da2)
#check @RBM.Gauss.Sizes.STNQConclPT''
#check @RBM.Gauss.Sizes.STNQConcl''
#check @RBM.Gauss.Sizes.STOeqNQPT''
#check @RBM.Gauss.Sizes.STOeqNQ''
#check @RBM.Gauss.Sizes.STXiBoot'
#check @RBM.Gauss.Sizes.STOeqQtNZ'
#check @RBM.Gauss.Sizes.stOeqQtNZ'_of_stOeqQtNZ
#check @RBM.Ind.nqFlowLam
#check @RBM.Ind.nqFlowPhiC
#check @RBM.Ind.stOeqNQPT''_holds
#check @RBM.Ind.NQEndFlowInst.inst_OeqNQPT''

-- the case-(i) lift = format model of T2292b (`Induction/NQEndFlowLift` d0484be)
#check @RBM.Ind.nqFlowSharp
#check @RBM.Ind.stOeqNQ''_holds
#check @RBM.Gauss.Sizes.stKloop_lip
#check @RBM.Ind.NQEndFlowLiftInst.inst_OeqNQ''

-- the zero-mode projection (`Kernel/Evolution` ff8d36d, `Induction/ZeroModeCalc` d1cb5a6, `Induction/QtNonzero` 95d8b2a)
#check @RBM.zeroModeSet
#check @RBM.zeroModeSetLin
#check @RBM.norm_zeroModeSet_le
#check @RBM.zeroModeSet_sub
#check @RBM.zeroModeSet_idem

-- the S3-22c consumer check, preflight (iv) (`Induction/Step34Pins` fc76526 `:330`, `Induction/NewPQ` f28fd9c `:584`)
#check @RBM.Gauss.Sizes.STNewPQ
#check @RBM.Gauss.Sizes.stNewPQ_holds

-- the good events (`Induction/GridGoodN` 2f246bf, `Induction/NQLin` d783ee3)
#check @RBM.Gauss.Sizes.GoodSetN
#check @RBM.Gauss.Sizes.GridGoodNConcl
#check @RBM.Gauss.Sizes.GridGoodN
#check @RBM.Gauss.Sizes.gridGoodN_holds
#check @RBM.Gauss.Sizes.GoodLinN
#check @RBM.Gauss.Sizes.NQLinConcl
#check @RBM.Gauss.Sizes.NQLinGood
#check @RBM.Gauss.Sizes.nqLinGood_holds
#check @RBM.Gauss.Sizes.nqLinPhi1
#check @RBM.Gauss.Sizes.nqLinPhi2
#check @RBM.Gauss.Sizes.nqLinPhi3

-- the setting and the pins' vocabulary (`Induction/Step34Pins` fc76526, `Induction/Defs` 64bdfd3)
#check @RBM.Gauss.Sizes.STIngR
#check @RBM.Gauss.Sizes.STCaseII
#check @RBM.Gauss.Sizes.STAny
#check @RBM.Gauss.Sizes.STIdiff
#check @RBM.Gauss.Sizes.STOeqQtNZ
#check @RBM.Gauss.Sizes.STPair
#check @RBM.Gauss.Sizes.STXiL
#check @RBM.Gauss.Sizes.STXiLK
#check @RBM.Gauss.Sizes.STlenL
#check @RBM.Gauss.Sizes.STbootRHS
#check @RBM.Gauss.Sizes.st_Bctl_pos
#check @RBM.Gauss.Sizes.STLK
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.Gauss.Sizes.STKbound
#check @RBM.Gauss.Sizes.STKward
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.STStep2Concl
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.stKbound_of_flow
#check @RBM.Gauss.Sizes.stKward_of_flow

-- scale facts, window, range (`Induction/ScaleFacts` 5d1e6b1, `ScaleFacts3` 7c3072a, `Green/Pins` 64bdfd3)
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.STBctl_pos
#check @RBM.Gauss.Sizes.STBctl_mono
#check @RBM.Gauss.Sizes.st_conStInd_sub
#check @RBM.Gauss.Sizes.RangeCond
#check @RBM.Green.v3_premises_of_stFlow

-- `≺`, per-time `≺`, sections (`Defs/StochDomAt` 9e2b00f)
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.PrecPT
#check @RBM.Gauss.Sizes.prec_of_le
#check @RBM.Gauss.Sizes.precPT_of_le
#check @RBM.StochDomAt
#check @RBM.StochDomAt.precomp_param
#check @RBM.StochDomAt.of_subset
#check @RBM.Path.TimeIcc
#check @RBM.Path.PerTimeDomAt
#check @RBM.Path.perTimeDomAt_iff_forall_section
#check @RBM.Path.stochDomAt_of_perTimeDomAt

-- loops at the flow and on matrices; the walk and the transfer (`Loop/GLoopFlow` 868b3b4, `Induction/Step2Defs`
-- 86124dc, `Gauss/FineModel` 0a873f1, `Path/Walk` ddf5f74, `Induction/Step2Events` 7f9bfa1)
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.Sizes.STLKM
#check @RBM.Gauss.Sizes.seqHflow
#check @RBM.Path.PathΩ
#check @RBM.Path.pathP
#check @RBM.Path.pathH
#check @RBM.Path.gridTime
#check @RBM.Path.gridTime_last
#check @RBM.Path.map_pathH_eq
#check @RBM.Gauss.Sizes.ST_gridTime_zero

-- for T2292b only (`Induction/ContinuityNet` 5b6cbc1, `Induction/LemDecCalELip` e4126a2, `Gauss/Domination` 1c2e756)
#check @RBM.Ind.ContinuityNet.contGood
#check @RBM.Ind.ContinuityNet.cont_core
#check @RBM.Ind.ContinuityNet.cont_highProbAt_good
#check @RBM.Ind.ContinuityNet.cont_inv_size_le_Bctl
#check @RBM.Gauss.Sizes.LemDecCalELip_Lloop_sub
#check @RBM.Gauss.Sizes.LemDecCalELip_env
#check @RBM.Gauss.netSize
#check @RBM.Gauss.netPt
#check @RBM.Gauss.exists_netPt_close

-- instance data (case (ii): `Induction/Step34Pins` fc76526; `Induction/AzumaProxyN` 43ab861)
#check @RBM.Gauss.Step34Inst.szB
#check @RBM.Gauss.Step34Inst.zB
#check @RBM.Gauss.Step34Inst.flow_zB
#check @RBM.Gauss.Step34Inst.szB_caseII
#check @RBM.Gauss.Step34Inst.szB_flow_ht
#check @RBM.Gauss.Step34Inst.szB_W_tendsto
#check @RBM.Gauss.Step34Inst.conStInd_const
#check @RBM.Gauss.Step34Inst.InstIngConcl
#check @RBM.Gauss.Step34Inst.inst_ing
#check @RBM.Gauss.Step34Inst.inst_OeqQtNZ
#check @RBM.Ind.AzumaProxyNInst.sig3

/-! ## 2. Pins

Inside `RBM.Gauss.Sizes.T2292Check`, so that every name resolves as in `Induction/NQEndFlow.lean`.  T2292 defines
`STNZConclPT''` and `STOeqNZPT''` as `RBM.Gauss.Sizes.<name>` with exactly these bodies (the `sz`-level one inside
`section Pins` with `variable {d : ℕ} (sz : Sizes d)`, which gives the same binders `{d} (sz) (E s t)`); T2292b defines
`STNZConcl''` and `STOeqNZ''` likewise.  Script diff against the merged `STNQConclPT''` (`NQEndFlow.lean:107`) — the
only hunks allowed:
* the index set `{σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)}` ↦
  `{σA : (Fin n_ → Bool) × Finset (Fin n_) // STIdiff σA.1 ⊆ σA.2}` (every `σ`, every `A ⊇ I_diff(σ)`);
* the quantity `‖Lloop … q.2.1.1 q.2.2 ω - STKloop … q.2.1.1 q.2.2‖` ↦
  `‖zeroModeSet d (sz.L n) q.2.1.1.2 (fun b => Lloop … q.2.1.1.1 b ω - STKloop … q.2.1.1.1 b) q.2.2‖`.
The hypotheses, the normalisation `/ B_u^{n_}` and the right side (`B_u^{1/6}·XLK n_ + STbootRHS 2 … B_s n_ p`,
R2*) are unchanged.  `STNZConcl''` vs `STNZConclPT''`: `PrecPT sz (U := …` ↦ `Prec sz (U := …` (one hunk). -/

namespace RBM.Gauss.Sizes.T2292Check

open MeasureTheory ProbabilityTheory Filter Matrix
open RBM RBM.Loop RBM.Path RBM.Gauss
open scoped NNReal ENNReal

/-- **Per-time case-(ii) projected endpoint** (T2292; `lem:STOeq_Qt_nonzero` `3_5:1561`, `(am;asoiuw_smalleta)`
`3_5:1916-1922` at each fixed `u`, `3_5:1931`; R2*: first summand of `STbootRHS` at `B_s`): for every sign vector
`σ`, every `A ⊇ I_diff(σ)` and every label `a`, `‖(Q^{(A)}(𝓛-𝒦)^{(n_)})_{u,σ,a}‖ / B_u^{n_} ≺ B_u^{1/6} XLK n_ u +
STbootRHS 2 XL XLK B_s n_ p`, per time (`PrecPT`). -/
def STNZConclPT'' {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    PrecPT sz (U := fun n => TimeIcc s t n × {σA : (Fin n_ → Bool) × Finset (Fin n_) // STIdiff σA.1 ⊆ σA.2} ×
        (Fin n_ → Zd d (sz.L n)))
      (fun n q ω => ‖zeroModeSet d (sz.L n) q.2.1.1.2
          (fun b : Fin n_ → Zd d (sz.L n) =>
            Lloop sz n (E n) (q.1 : ℝ) q.2.1.1.1 b ω - STKloop sz n (E n) (q.1 : ℝ) q.2.1.1.1 b) q.2.2‖ /
        (sz.Bctl n (q.1 : ℝ)) ^ n_)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * XLK n_ n (q.1 : ℝ) +
        STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ)) (sz.Bctl n (s n)) n_ p)

/-- The per-time pin in the ingredient shape (case (ii)): the conclusion of `stOeqNZPT''_holds` (T2292). -/
def STOeqNZPT'' (d : ℕ) : Prop := STIngR d STCaseII (fun sz E s t => STNZConclPT'' sz E s t)

/-- **Uniform case-(ii) projected endpoint** (T2292b; the paper's `N^{-C}`-net remark `3_5:1931`): `STNZConclPT''`
with `PrecPT` ↦ `Prec` in the conclusion. -/
def STNZConcl'' {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    Prec sz (U := fun n => TimeIcc s t n × {σA : (Fin n_ → Bool) × Finset (Fin n_) // STIdiff σA.1 ⊆ σA.2} ×
        (Fin n_ → Zd d (sz.L n)))
      (fun n q ω => ‖zeroModeSet d (sz.L n) q.2.1.1.2
          (fun b : Fin n_ → Zd d (sz.L n) =>
            Lloop sz n (E n) (q.1 : ℝ) q.2.1.1.1 b ω - STKloop sz n (E n) (q.1 : ℝ) q.2.1.1.1 b) q.2.2‖ /
        (sz.Bctl n (q.1 : ℝ)) ^ n_)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * XLK n_ n (q.1 : ℝ) +
        STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ)) (sz.Bctl n (s n)) n_ p)

/-- The uniform pin in the ingredient shape (case (ii)): the conclusion of `stOeqNZ''_holds` (T2292b); consumed by
S3-22c (`newPQ` combination + bootstrap → `stOeqQtNZ'_holds`). -/
def STOeqNZ'' (d : ℕ) : Prop := STIngR d STCaseII (fun sz E s t => STNZConcl'' sz E s t)

/-! ## 3. Pinned statements -/

/-- **T2292 (main)**: `RBM.Ind.stOeqNZPT''_holds` has exactly this type
(`example : RBM.Gauss.Sizes.T2292Check.T2292_stOeqNZPT''_holds := @RBM.Ind.stOeqNZPT''_holds` must compile in the
statement script). -/
def T2292_stOeqNZPT''_holds : Prop := ∀ d : ℕ, STOeqNZPT'' d

/-- **T2292b (main)**: `RBM.Ind.stOeqNZ''_holds` has exactly this type
(`example : RBM.Gauss.Sizes.T2292Check.T2292b_stOeqNZ''_holds := @RBM.Ind.stOeqNZ''_holds`). -/
def T2292b_stOeqNZ''_holds : Prop := ∀ d : ℕ, STOeqNZ'' d

end RBM.Gauss.Sizes.T2292Check

/-! ## 4. Well-formedness (Prop-valued; no proof obligation) -/

namespace RBM.Gauss.Step34Inst.T2292Check

open RBM RBM.Gauss RBM.Gauss.Sizes

/-- The per-time pin at the case-(ii) instance data of the merged `inst_OeqQtNZ` (`Step34Pins.lean:1006`). -/
example : Prop :=
  RBM.Gauss.Sizes.T2292Check.STNZConclPT'' szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32)

/-- Its ingredient form at `(szB, zB, 15/16, 31/32)`, `C_d = 1` (instance (1) of T2292). -/
example : Prop :=
  InstIngConcl (fun sz E s t => RBM.Gauss.Sizes.T2292Check.STNZConclPT'' sz E s t) szB zB
    (fun _ => 15 / 16) (fun _ => 31 / 32) 1

/-- The uniform pin at the same data (instance (1) of T2292b). -/
example : Prop :=
  InstIngConcl (fun sz E s t => RBM.Gauss.Sizes.T2292Check.STNZConcl'' sz E s t) szB zB
    (fun _ => 15 / 16) (fun _ => 31 / 32) 1

/-- The two targets at `d = 3`. -/
example : Prop := RBM.Gauss.Sizes.T2292Check.STOeqNZPT'' 3

example : Prop := RBM.Gauss.Sizes.T2292Check.STOeqNZ'' 3

/-- The S3-22c target (merged pin, owed `Test/Axioms.lean:126`) at the same data, for the consumer check. -/
example : Prop := RBM.Gauss.Sizes.STOeqQtNZ' 3

end RBM.Gauss.Step34Inst.T2292Check
