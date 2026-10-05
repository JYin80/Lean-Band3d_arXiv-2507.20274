/-
Release check for T2207 (dispatcher V1, Mon Oct  5 2026; CLAUDE.md §4 step 0; DECISIONS §29, §45 O2, §62 (2),
§64 (4)).  S3-12c (ST-3, non-alternating chain, third of three; S3-12a = T2186 merged d783ee3, S3-12b = T2199
merged cef761a): the flow endpoint.  From the grid endpoint `nqGridEndLinN`, the good events of
`gridGoodN_holds` (crude level `Φc = N^{C₀}`, real `Λ`) and `nqLinGood_holds`, the initial event `STLK s`, the
transfer `map_pathH_eq` and the uniform-in-`u` lift, prove the merged primed pin `STOeqNQ' d` for every `d`.
Section 1: the merged names the ticket cites.  Section 2: the pinned statements as `Prop`s in
`RBM.Ind.T2207Check` (the final theorem `RBM.Ind.stOeqNQ'_holds : ∀ d, STOeqNQ' d`; the per-time form
`STNQConclPT'`, `STOeqNQPT'` (vocabulary, verbatim in the new file); the regularised controls `nqFlowSharp`
and the level `nqFlowLam` (vocabulary)).
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2207-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names -/

-- the primed pin (`Induction/Step34PinsP`, d783ee3) and the ingredient shape (`Induction/Step34Pins`, fc76526)
#check @RBM.Gauss.Sizes.STNQConcl'
#check @RBM.Gauss.Sizes.STOeqNQ'
#check @RBM.Gauss.Sizes.stOeqNQ'_of_stOeqNQ
#check @RBM.Gauss.Step34PInst.inst_OeqNQ'
#check @RBM.Gauss.Sizes.STIngR
#check @RBM.Gauss.Sizes.STCaseI
#check @RBM.Gauss.Sizes.STAny
#check @RBM.Gauss.Sizes.STPair
#check @RBM.Gauss.Sizes.STlenL
#check @RBM.Gauss.Sizes.STbootRHS
#check @RBM.Gauss.Sizes.STXiL
#check @RBM.Gauss.Sizes.STXiLK
#check @RBM.Gauss.Sizes.STn12
#check @RBM.Gauss.Sizes.STn12E
#check @RBM.Gauss.Sizes.st_Bctl_pos
#check @RBM.Gauss.Step34Inst.sz0_caseI
-- the setting (`Induction/Defs`, `Defs/Sizes`, `Green/Pins`, `Induction/ScaleFacts`)
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.STLK
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.STKbound
#check @RBM.Gauss.Sizes.STKward
#check @RBM.Gauss.Sizes.STStep2Concl
#check @RBM.Gauss.Sizes.STLocalEntryU
#check @RBM.Gauss.Sizes.STAvgU
#check @RBM.Gauss.Sizes.STGdecayW
#check @RBM.Gauss.Sizes.RangeCond
#check @RBM.Green.rangeCond_mono
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.STBctl_mono
#check @RBM.Gauss.Sizes.STBctl_ge
#check @RBM.Gauss.Sizes.stKbound_holds
#check @RBM.lemT_lt_one
-- `≺`, per-time `≺`, the section lemma, w.h.p. (`Defs/StochDomAt`, 9e2b00f)
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.PrecPT
#check @RBM.Gauss.Sizes.Prec.whp
#check @RBM.StochDomAt
#check @RBM.badSetAt
#check @RBM.Gauss.HighProbAt
#check @RBM.Path.TimeIcc
#check @RBM.Path.PerTimeDomAt
#check @RBM.Path.perTimeDomAt_iff_forall_section
#check @RBM.Path.stochDomAt_of_perTimeDomAt
#check @RBM.Path.highProbAt_iInter
-- loops at the flow and on matrices (`Loop/GLoopFlow`, `Induction/Defs`, `Induction/Step2Defs`)
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.Gauss.Sizes.STLKM
#check @RBM.Gauss.Sizes.STXiLKM
#check @RBM.Gauss.Sizes.seqHflow
-- the grid walk and the transfer (`Path/Walk`, ddf5f74; `Induction/Step2Events`)
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
#check @RBM.Gauss.Sizes.STSEforLnConcl
#check @RBM.Gauss.Sizes.stSEforLn_holds
-- crude bounds (`Induction/NQGood1`, 691566a)
#check @RBM.Ind.STXiLKM_crudeN
-- the grid endpoint (`Induction/NQEndLin`, cef761a)
#check @RBM.Ind.nqGridEndLinN
-- the net lift and its inputs (`Induction/ContinuityNet` 5b6cbc1, `Induction/LemDecCalELip` e4126a2)
#check @RBM.Ind.ContinuityNet.cont_core
#check @RBM.Ind.ContinuityNet.contGood
#check @RBM.Ind.ContinuityNet.cont_highProbAt_good
#check @RBM.Ind.ContinuityNet.cont_inv_size_le_Bctl
#check @RBM.Ind.ContinuityNet.cont_Bctl_ratio
#check @RBM.Gauss.Sizes.LemDecCalELip_Lloop_norm
#check @RBM.Gauss.Sizes.LemDecCalELip_Lloop_sub
#check @RBM.Gauss.Sizes.LemDecCalELip_STKloop_two_sub
#check @RBM.Gauss.Sizes.LemDecCalELip_lift
-- instance data (as T2199)
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.InductionDefsInst.z0
#check @RBM.Gauss.InductionDefsInst.flow_z0
#check @RBM.Gauss.InductionDefsInst.sInst
#check @RBM.Gauss.InductionDefsInst.tInst
#check @RBM.Gauss.Step34Inst.InstIngConcl
#check @RBM.Gauss.Step34Inst.inst_ing

/-! ## 2. Pins and vocabulary -/

namespace RBM.Ind.T2207Check

open MeasureTheory ProbabilityTheory Filter Matrix
open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Ind
open scoped NNReal ENNReal

/-- **Target (final)**: `lem:STOeq_NQ`, primed, for every dimension (`3_5:1136`; the merged pin
`STOeqNQ'`, `Induction/Step34PinsP.lean:70`, unchanged).  T2207 proves `RBM.Ind.stOeqNQ'_holds` with
exactly this type (`example : RBM.Ind.T2207Check.T2207_stOeqNQ'_holds := @RBM.Ind.stOeqNQ'_holds`). -/
def T2207_stOeqNQ'_holds : Prop := ∀ d : ℕ, STOeqNQ' d

/-- **Per-time primed conclusion** (vocabulary; copy verbatim into the new file): `STNQConcl'`
(`Step34PinsP.lean:53`) with `Prec` replaced by `PrecPT` (union over `u` outside `P`, DECISIONS §7).  The only
diff against `STNQConcl'` is `Prec sz (U := fun n => TimeIcc …` ↦ `sz.PrecPT (U := fun n => TimeIcc …` in the
conclusion (script diff). -/
def STNQConclPT' {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      sz.Prec (U := STPair s t) (fun n q ω => sz.STXiL n (E n) q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      sz.Prec (U := STPair s t) (fun n q ω => sz.STXiLK n (E n) q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    sz.PrecPT (U := fun n => TimeIcc s t n × {σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} ×
        (Fin n_ → Zd d (sz.L n)))
      (fun n q ω => ‖sz.Lloop n (E n) (q.1 : ℝ) q.2.1.1 q.2.2 ω - sz.STKloop n (E n) (q.1 : ℝ) q.2.1.1 q.2.2‖ /
        (sz.Bctl n (q.1 : ℝ)) ^ n_)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * XLK n_ n (q.1 : ℝ) +
        STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ)) (sz.Bctl n (q.1 : ℝ)) n_ p)

/-- The per-time pin in the ingredient shape (case (i)), the conclusion of target 3 (S3-12c1 if split). -/
def STOeqNQPT' (d : ℕ) : Prop := STIngR d STCaseI (fun sz E s t => STNQConclPT' sz E s t)

/-- The statement of target 3 (`stOeqNQPT'_holds`). -/
def T2207_stOeqNQPT'_holds : Prop := ∀ d : ℕ, STOeqNQPT' d

/-- **The regularised control** (vocabulary, target 4(a)): `X♯ m n u = inf_{u' ∈ [u, t_n]} X m n u'`;
non-decreasing in `u ∈ [s_n, t_n]`, `1 ≤ X♯ ≤ X` there when `X ≥ 1`, and the pair hypotheses
`Ξ̂_w ≺ X m n u` (`w ≤ u`) imply `Ξ̂_w ≺ X♯ m n u` (bad-set inclusion: `X♯ < y` gives `u' ≥ u` with `X u' < y`). -/
noncomputable def nqFlowSharp (t : ℕ → ℝ) (X : ℕ → ℕ → ℝ → ℝ) : ℕ → ℕ → ℝ → ℝ :=
  fun m n u => sInf ((fun w => X m n w) '' Set.Icc u (t n))

/-- **The level `Λ` of `GoodSetN`'s (D4) clause** from the controls (vocabulary, preflight gate G1):
`Λ = XL(2k-1) (XL(4p)/B)^{1/(2p)}`, so `Λ^{1/2} = B^{-1/(4p)} XL(2k-1)^{1/2} XL(4p)^{1/(4p)}`, the first
summand of `STbootRHS 2 … B k p` exactly when `B` is the endpoint value `B_v`. -/
noncomputable def nqFlowLam (XL : ℕ → ℝ) (B : ℝ) (k p : ℕ) : ℝ :=
  XL (2 * k - 1) * (XL (4 * p) / B) ^ (1 / (2 * (p : ℝ)))

end RBM.Ind.T2207Check
