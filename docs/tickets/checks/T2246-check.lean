/-
Release check for T2246 (dispatcher V1, Tue Oct  6 02:47 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §80, §69 A, §62,
§64 (4), §45 O2, §29, §20, §17).  S3-12c1 (ST-3, non-alternating chain; S3-12a = T2186 merged d783ee3, S3-12b =
T2199 merged cef761a; S3-12c2 next): (i) the R2* primed pins (`STbootRHS … (sz.Bctl n (s n))` in place of
`(sz.Bctl n u)`, first summand only; supervisor `docs/supervisor/2026-10-05-1955.md` A1); (ii) the trivial bridges;
(iii) the per-time flow endpoint at `B_s`, `RBM.Ind.stOeqNQPT''_holds : ∀ d, STOeqNQPT'' d`.
Section 1: `#check` of every merged name the ticket cites (exact namespaces; `main` 8256045).
Section 2: the ten pin texts (the new file defines `RBM.Gauss.Sizes.<name>` with exactly these bodies) and the two
vocabulary defs `nqFlowLam`, `nqFlowPhiC`.
Section 3: the pinned statements of the public (and one private) theorems as `Prop`s.
Section 4: well-formedness `example`s (Prop-valued, no proof obligation).
Statement and `#check` only: no proofs, no `sorry`, no `by`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2246-check.lean`.
-/
import RBM3D.Induction.NQEndLin
import RBM3D.Induction.Step34PinsP
import RBM3D.Induction.GridGoodN
import RBM3D.Induction.NQLin
import RBM3D.Induction.SEforLn2
import RBM3D.Induction.ScaleFacts
import RBM3D.Induction.ScaleFacts3
import RBM3D.Induction.IterationsA
import RBM3D.Induction.Step2Events
import RBM3D.Induction.Step2Defs
import RBM3D.Induction.Step2Iterate
import RBM3D.Induction.ContinuityNet
import RBM3D.Induction.LemDecCalELip
import RBM3D.Induction.QProxy
import RBM3D.Green.Pins
import RBM3D.Loop.KLFinal
import RBM3D.Loop.KLTreeDeriv
import RBM3D.Path.Walk

/-! ## 1. Merged names -/

-- the pins being primed and their vocabulary (`Induction/Step34Pins` fc76526, `Induction/Step34PinsP` d783ee3)
#check @RBM.Gauss.Sizes.STbootRHS
#check @RBM.Gauss.Sizes.STNQConcl'
#check @RBM.Gauss.Sizes.STOeqNQ'
#check @RBM.Gauss.Sizes.STNQConcl
#check @RBM.Gauss.Sizes.STOeqNQ
#check @RBM.Gauss.Sizes.STXiBoot
#check @RBM.Gauss.Sizes.STOeqQt
#check @RBM.Gauss.Sizes.STOeqQtNZ
#check @RBM.Gauss.Sizes.STIterR
#check @RBM.Gauss.Sizes.STIterations
#check @RBM.Gauss.Sizes.STIterationsII
#check @RBM.Gauss.Sizes.STIterHyp
#check @RBM.Gauss.Sizes.STPsi
#check @RBM.Gauss.Sizes.STAI
#check @RBM.Gauss.Sizes.STAII
#check @RBM.Gauss.Sizes.STRegIterI
#check @RBM.Gauss.Sizes.STIngR
#check @RBM.Gauss.Sizes.STCaseI
#check @RBM.Gauss.Sizes.STCaseII
#check @RBM.Gauss.Sizes.STAny
#check @RBM.Gauss.Sizes.STPair
#check @RBM.Gauss.Sizes.STlenL
#check @RBM.Gauss.Sizes.STsupXiLK
#check @RBM.Gauss.Sizes.STXiL
#check @RBM.Gauss.Sizes.STXiLK
#check @RBM.Gauss.Sizes.STn12
#check @RBM.Gauss.Sizes.STn12E
#check @RBM.Gauss.Sizes.STKward
#check @RBM.Gauss.Sizes.STStep2Concl
#check @RBM.Gauss.Sizes.STLocalEntryU
#check @RBM.Gauss.Sizes.STAvgU
#check @RBM.Gauss.Sizes.STGdecayW
#check @RBM.Gauss.Sizes.STSEforLnConcl
#check @RBM.Gauss.Sizes.st_Bctl_pos
#check @RBM.Gauss.Sizes.stOeqNQ'_of_stOeqNQ
#check @RBM.Gauss.Step34PInst.inst_OeqNQ'
#check @RBM.Gauss.Step34Inst.InstIngConcl
#check @RBM.Gauss.Step34Inst.inst_ing
#check @RBM.Gauss.Step34Inst.sz0_caseI
#check @RBM.Gauss.Step34Inst.sz0_hs0
#check @RBM.Gauss.Step34Inst.sz0_hst
#check @RBM.Gauss.Step34Inst.sz0_ht
#check @RBM.Gauss.Step34Inst.sz0_con
-- the setting (`Induction/Defs` 64bdfd3, `Defs/Sizes` 0a873f1, `Defs/Semicircle` fbc9870, `Loop/KLFinal` 471b643)
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.STLK
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.STKbound
#check @RBM.Gauss.Sizes.STStep1Loop
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.lemT
#check @RBM.lemT_lt_one
#check @RBM.Gauss.Sizes.stKbound_holds
-- scale facts, window, range (`Induction/ScaleFacts` 5d1e6b1, `ScaleFacts3` 7c3072a, `Green/Pins` 64bdfd3,
-- `Induction/Step2Iterate` c5bbae7)
#check @RBM.Gauss.Sizes.STBctl_mono
#check @RBM.Gauss.Sizes.STBctl_ge
#check @RBM.Gauss.Sizes.st_window
#check @RBM.Gauss.Sizes.st_conStInd_sub
#check @RBM.Gauss.Sizes.scaleFacts3_W_tendsto
#check @RBM.Gauss.Sizes.RangeCond
#check @RBM.Green.rangeCond_mono
#check @RBM.Green.v3_premises_of_stFlow
#check @RBM.Gauss.Sizes.ST_one_sub_lemT
-- `≺`, per-time `≺`, sections, reindexing (`Defs/StochDomAt` 9e2b00f)
#check @RBM.StochDomAt
#check @RBM.badSetAt
#check @RBM.Gauss.HighProbAt
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.PrecPT
#check @RBM.Gauss.Sizes.Prec.whp
#check @RBM.Gauss.Sizes.prec_of_le
#check @RBM.Path.TimeIcc
#check @RBM.Path.PerTimeDomAt
#check @RBM.Path.perTimeDomAt_iff_forall_section
#check @RBM.Path.stochDomAt_of_perTimeDomAt
#check @RBM.Path.highProbAt_iInter
#check @RBM.StochDomAt.of_subset
#check @RBM.StochDomAt.precomp_param
#check @RBM.StochDomAt.of_subset_union
#check @RBM.StochDomAt.mul
-- loops at the flow and on matrices (`Loop/GLoopFlow` 868b3b4, `Induction/Step2Defs` 86124dc, `Gauss/FineModel` 0a873f1)
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.Sizes.STLKM
#check @RBM.Gauss.Sizes.STXiLKM
#check @RBM.Gauss.Sizes.gridGood_STXiLKM_seqHflow
#check @RBM.Gauss.Sizes.seqHflow
-- the grid walk and the transfer (`Path/Walk` ddf5f74, `Induction/Step2Events` 7f9bfa1)
#check @RBM.Path.PathΩ
#check @RBM.Path.pathP
#check @RBM.Path.pathH
#check @RBM.Path.gridTime
#check @RBM.Path.gridTime_last
#check @RBM.Path.map_pathH_eq
#check @RBM.Gauss.Sizes.ST_gridTime_zero
-- the good events (`Induction/GridGoodN` 2f246bf, `Induction/NQLin` d783ee3, `Induction/SEforLn2` ae259a6)
#check @RBM.Gauss.Sizes.GoodSetN
#check @RBM.Gauss.Sizes.GridGoodNConcl
#check @RBM.Gauss.Sizes.GridGoodN
#check @RBM.Gauss.Sizes.gridGoodN_holds
#check @RBM.Gauss.Sizes.GoodLinN
#check @RBM.Gauss.Sizes.nqLinPhi1
#check @RBM.Gauss.Sizes.nqLinPhi2
#check @RBM.Gauss.Sizes.nqLinPhi3
#check @RBM.Gauss.Sizes.NQLinConcl
#check @RBM.Gauss.Sizes.NQLinGood
#check @RBM.Gauss.Sizes.nqLinGood_holds
#check @RBM.Gauss.Sizes.stSEforLn_holds
-- the grid endpoint (`Induction/NQEndLin` cef761a)
#check @RBM.Ind.nqGridEndLinN
-- the consumer of `STXiBoot` whose `hlow` motivates R2* (`Induction/IterationsA` 6583ca2)
#check @RBM.Gauss.Sizes.IterationsAScale
#check @RBM.Gauss.Sizes.iterationsA_step
-- for the split section (S3-12c2; `Induction/ContinuityNet` 5b6cbc1, `Loop/KLTreeDeriv` e2aa5fe,
-- `Induction/LemDecCalELip` e4126a2, `Induction/QProxy` 9a207a1)
#check @RBM.Ind.ContinuityNet.cont_core
#check @RBM.Ind.ContinuityNet.contGood
#check @RBM.Ind.ContinuityNet.cont_highProbAt_good
#check @RBM.Ind.ContinuityNet.cont_Bctl_ratio
#check @RBM.Loop.KLK_isKLoop
#check @RBM.Gauss.Sizes.LemDecCalELip_Lloop_sub
#check @RBM.Ind.qvFormQN_le_of_goodSetN
-- instance data
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.InductionDefsInst.z0
#check @RBM.Gauss.InductionDefsInst.flow_z0
#check @RBM.Gauss.InductionDefsInst.sInst
#check @RBM.Gauss.InductionDefsInst.tInst

/-! ## 2. Pins (R2*, DECISIONS §80 (1)) and vocabulary

Inside `RBM.Gauss.Sizes.T2246Check`, so that every name resolves as in `Induction/Step34PinsP.lean`.  The new file
defines each `X` below as `RBM.Gauss.Sizes.X` with exactly this body (for the `sz`-level pins inside
`section Pins` with `variable {d : ℕ} (sz : Sizes d)`, which gives the same binders `{d} (sz) (E s t)`).
Script diff against the merged texts — the only hunks allowed:
* `STNQConcl''` vs `STNQConcl'` (`Step34PinsP.lean:53`): in the `STbootRHS 2 …` argument,
  `(sz.Bctl n (q.1 : ℝ)) n_ p` ↦ `(sz.Bctl n (s n)) n_ p` (one hunk; the `^ (1 / 6 : ℝ)` term and the `/ … ^ n_`
  normalisation unchanged);
* `STXiBoot'` vs `STXiBoot` (`Step34Pins.lean:414`): `(sz.Bctl n q.1.2) n_ p` ↦ `(sz.Bctl n (s n)) n_ p`;
* `STIterR'` vs `STIterR` (`Step34Pins.lean:478`): `STXiBoot sz (STflowE z) s t` ↦ `STXiBoot' sz (STflowE z) s t`;
* `STOeqNQ''`, `STOeqQt'`, `STOeqQtNZ'`, `STIterations'`, `STIterationsII'`: the merged one-liners with the primed
  conclusion / setting;
* `STNQConclPT''` vs `STNQConcl''`: the conclusion's `Prec sz (U := fun n => TimeIcc …` ↦ `PrecPT sz (U := …`. -/

namespace RBM.Gauss.Sizes.T2246Check

open MeasureTheory ProbabilityTheory Filter Matrix
open RBM RBM.Loop RBM.Path RBM.Gauss
open scoped NNReal ENNReal

/-- **`lem:STOeq_NQ`, R2*** (`3_5:1136`, `(am;asoiuw)` `3_5:1143-1148`; DECISIONS §80 (1)): `STNQConcl'` with the
first summand of `STbootRHS` at the window start `B_s`. -/
def STNQConcl'' {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    Prec sz (U := fun n => TimeIcc s t n × {σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} ×
        (Fin n_ → Zd d (sz.L n)))
      (fun n q ω => ‖Lloop sz n (E n) (q.1 : ℝ) q.2.1.1 q.2.2 ω - STKloop sz n (E n) (q.1 : ℝ) q.2.1.1 q.2.2‖ /
        (sz.Bctl n (q.1 : ℝ)) ^ n_)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * XLK n_ n (q.1 : ℝ) +
        STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ)) (sz.Bctl n (s n)) n_ p)

/-- `lem:STOeq_NQ`, R2* (case (i)). -/
def STOeqNQ'' (d : ℕ) : Prop := STIngR d STCaseI (fun sz E s t => STNQConcl'' sz E s t)

/-- **`(am;asoi222)`, R2*** (`3_5:1366`; DECISIONS §80 (1)): `STXiBoot` with the first summand of `STbootRHS` at
`B_s`. -/
def STXiBoot' {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m + 1 ≤ n_ →
      Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 n_ ω)
      (fun n q _ => STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p)

/-- `lem:STOeq_Qt`, R2* (`3_5:1362`): case (i). -/
def STOeqQt' (d : ℕ) : Prop := STIngR d STCaseI (fun sz E s t => STXiBoot' sz E s t)

/-- `lem:STOeq_Qt_nonzero`, R2* (`3_5:1561`): case (ii). -/
def STOeqQtNZ' (d : ℕ) : Prop := STIngR d STCaseII (fun sz E s t => STXiBoot' sz E s t)

/-- **`lem:iterations`, R2*** (`3_5:1407-1417`, `3_5:1575-1595`): `STIterR` with the hypothesis `STXiBoot'`.
Proof: S3-24b (copy of `iterationsA_step` with `hlow` at `w = s`; DECISIONS §80 (2)). -/
def STIterR' (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (Aof : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) →
          R sz s t → STKbound sz (STflowE z) → STLK sz (STflowE z) s → STConStInd sz 𝔠d s t →
          STStep1Loop sz (STflowE z) s t → STStep2Concl sz (STflowE z) s t Cd →
          STXiBoot' sz (STflowE z) s t →
          ∀ n_ k : ℕ, 2 ≤ n_ → 1 ≤ k →
            (∀ r, 2 ≤ r → r + 1 ≤ n_ → STIterHyp sz (STflowE z) s t (Aof sz s) r k) →
            (∀ r, 2 ≤ r → r ≤ n_ + 2 → STIterHyp sz (STflowE z) s t (Aof sz s) r (k - 1)) →
            STIterHyp sz (STflowE z) s t (Aof sz s) n_ k

/-- `lem:iterations`, case (i), R2*. -/
def STIterations' (d : ℕ) : Prop := STIterR' d STRegIterI (fun sz _ n => STAI sz n)

/-- The case-(ii) analogue, R2*. -/
def STIterationsII' (d : ℕ) : Prop := STIterR' d STCaseII (fun sz s n => STAII sz s n)

/-- **Per-time R2* conclusion** (target 6; the union over `u` outside `P`, DECISIONS §7): `STNQConcl''` with
`Prec` ↦ `PrecPT` in the conclusion. -/
def STNQConclPT'' {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    PrecPT sz (U := fun n => TimeIcc s t n × {σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} ×
        (Fin n_ → Zd d (sz.L n)))
      (fun n q ω => ‖Lloop sz n (E n) (q.1 : ℝ) q.2.1.1 q.2.2 ω - STKloop sz n (E n) (q.1 : ℝ) q.2.1.1 q.2.2‖ /
        (sz.Bctl n (q.1 : ℝ)) ^ n_)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * XLK n_ n (q.1 : ℝ) +
        STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ)) (sz.Bctl n (s n)) n_ p)

/-- The per-time pin in the ingredient shape (case (i)): the conclusion of target 6. -/
def STOeqNQPT'' (d : ℕ) : Prop := STIngR d STCaseI (fun sz E s t => STNQConclPT'' sz E s t)

/-- **The level `Λ` of `GoodSetN`'s (D4) clause** (vocabulary, `RBM.Ind.nqFlowLam` in the new file):
`Λ = XL(2k−1) (XL(4p)/B)^{1/(2p)}`; at `B = B_s`, `Λ^{1/2}` is the first summand of `STbootRHS 2 … B_s k p`
(R2*: G1 row `0`).  The ticket uses `max 1 (nqFlowLam X B_s k p)`. -/
noncomputable def nqFlowLam (XL : ℕ → ℝ) (B : ℝ) (k p : ℕ) : ℝ :=
  XL (2 * k - 1) * (XL (4 * p) / B) ^ (1 / (2 * (p : ℝ)))

/-- **The crude level `Φc` of `GoodSetN`** (vocabulary, `RBM.Ind.nqFlowPhiC` in the new file; preflight (iii)):
the sum of the controls of lengths `1 … k+1` at the window end, so that `hX`, `hY` of `GridGoodNConcl` follow from
the pair hypotheses (`nqGridEndLinN` quantifies over every `Φc`). -/
noncomputable def nqFlowPhiC (X Y : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (k + 1), (X m + Y m)

/-! ## 3. Pinned statements -/

/-- Private bridge (target 2; `stNQConcl''_of_stNQConcl'` has exactly this type, by a compiled `example` in the
new file). -/
def T2246_stNQConcl''_of_stNQConcl' : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ), (∀ n, t n < 1) →
    STNQConcl' sz E s t → STNQConcl'' sz E s t

/-- Public bridge (target 2): `RBM.Gauss.Sizes.stOeqNQ''_of_stOeqNQ'`. -/
def T2246_stOeqNQ''_of_stOeqNQ' : Prop := ∀ d : ℕ, STOeqNQ' d → STOeqNQ'' d

/-- Bridge (target 2): `RBM.Gauss.Sizes.stXiBoot'_of_stXiBoot`. -/
def T2246_stXiBoot'_of_stXiBoot : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ), (∀ n, t n < 1) →
    STXiBoot sz E s t → STXiBoot' sz E s t

/-- Bridge (target 2): `RBM.Gauss.Sizes.stOeqQt'_of_stOeqQt`. -/
def T2246_stOeqQt'_of_stOeqQt : Prop := ∀ d : ℕ, STOeqQt d → STOeqQt' d

/-- Bridge (target 2): `RBM.Gauss.Sizes.stOeqQtNZ'_of_stOeqQtNZ`. -/
def T2246_stOeqQtNZ'_of_stOeqQtNZ : Prop := ∀ d : ℕ, STOeqQtNZ d → STOeqQtNZ' d

/-- **Target 6 (main)**: `RBM.Ind.stOeqNQPT''_holds` has exactly this type
(`example : RBM.Gauss.Sizes.T2246Check.T2246_stOeqNQPT''_holds := @RBM.Ind.stOeqNQPT''_holds`). -/
def T2246_stOeqNQPT''_holds : Prop := ∀ d : ℕ, STOeqNQPT'' d

/-- For the split section: the target of S3-12c2 (`RBM.Ind.stOeqNQ''_holds`). -/
def T2246_stOeqNQ''_holds_c2 : Prop := ∀ d : ℕ, STOeqNQ'' d

/-! ## 4. Well-formedness (Prop-valued, no proof obligation) -/

-- the primed conclusions at the merged instance data fit `InstIngConcl` (instances (1), (2), (3))
example : Prop :=
  RBM.Gauss.Step34Inst.InstIngConcl (fun sz E s t => STNQConclPT'' sz E s t) RBM.Gauss.SizesInst.sz0
    RBM.Gauss.InductionDefsInst.z0 RBM.Gauss.InductionDefsInst.sInst RBM.Gauss.InductionDefsInst.tInst 1
example : Prop :=
  RBM.Gauss.Step34Inst.InstIngConcl (fun sz E s t => STNQConcl'' sz E s t) RBM.Gauss.SizesInst.sz0
    RBM.Gauss.InductionDefsInst.z0 RBM.Gauss.InductionDefsInst.sInst RBM.Gauss.InductionDefsInst.tInst 1
example : Prop :=
  STXiBoot' RBM.Gauss.SizesInst.sz0 (STflowE RBM.Gauss.InductionDefsInst.z0)
    RBM.Gauss.InductionDefsInst.sInst RBM.Gauss.InductionDefsInst.tInst
example : Prop := STIterations' 3 ∧ STIterationsII' 3 ∧ STOeqQt' 3 ∧ STOeqQtNZ' 3 ∧ STOeqNQ'' 3
example : Prop := nqFlowLam (fun _ => 1) (1 / 2) 3 1 ≤ nqFlowPhiC (fun _ => 1) (fun _ => 1) 3

end RBM.Gauss.Sizes.T2246Check
