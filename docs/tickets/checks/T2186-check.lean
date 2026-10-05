/-
Release check for T2186 (dispatcher V1, Mon Oct  5 2026; CLAUDE.md §4 step 0; DECISIONS §29, §45 O2, §57, §62).
S3-12a (first of three; S3-12b grid endpoint, S3-12c flow endpoint): the primed pins `STNQConcl'`,
`STOeqNQ'` (RBM2D `STOeqPT` form, DECISIONS §62 (1)) in the new file `Induction/Step34PinsP`, and route (R)
(§62 (2)) in the new file `Induction/NQLin`: the linear set `GoodLinN` with (D1'), (D2'), (D3') at separate
deterministic levels, its measurability and high probability, the exit time of `GoodSetN ∩ GoodLinN`, the
linear drift level, the primed `subGaussStop` wrapper and the linear budget.
Section 1: the merged names the ticket cites.  Section 2: pinned vocabulary in `RBM.Gauss.Sizes.T2186Check`
(T2186 defines it in `RBM.Gauss.Sizes` verbatim).  Section 3: pinned vocabulary in `RBM.Ind.T2186Check`
(defined in `RBM.Ind` verbatim).  Section 4: pinned statements as `Prop`s (T2186 proves each with this
statement, in the namespace named in its docstring).  Spelling: the check file writes `GoodLinN sz …`
(not `sz.GoodLinN`, which would resolve to the not-yet-existing `RBM.Gauss.Sizes.GoodLinN` here); T2186 uses
the same spelling.
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2186-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names (the private helpers the ticket cites by file:line, `gridGood_*` in `GridGoodN` and
`nqBudget_final` in `NQBudget`, cannot be `#check`ed and are copied, not called) -/

-- the Step 3-4 pins (`Induction/Step34Pins`, fc76526) and their instance data
#check @RBM.Gauss.Sizes.STPair
#check @RBM.Gauss.Sizes.STXiL
#check @RBM.Gauss.Sizes.STXiLK
#check @RBM.Gauss.Sizes.STCaseI
#check @RBM.Gauss.Sizes.STAny
#check @RBM.Gauss.Sizes.STn12E
#check @RBM.Gauss.Sizes.STn12
#check @RBM.Gauss.Sizes.STSEforLnConcl
#check @RBM.Gauss.Sizes.STlenL
#check @RBM.Gauss.Sizes.STsupXiLK
#check @RBM.Gauss.Sizes.STbootRHS
#check @RBM.Gauss.Sizes.STXiBoot
#check @RBM.Gauss.Sizes.STNQConcl
#check @RBM.Gauss.Sizes.STIngR
#check @RBM.Gauss.Sizes.STSEforLn
#check @RBM.Gauss.Sizes.STOeqNQ
#check @RBM.Gauss.Sizes.STKbound
#check @RBM.Gauss.Sizes.STKward
#check @RBM.Gauss.Sizes.STLK
#check @RBM.Gauss.Sizes.STStep2Concl
#check @RBM.Gauss.Sizes.STLmaxU
#check @RBM.Gauss.Sizes.STLKU
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.Gauss.Step34Inst.InstIngConcl
#check @RBM.Gauss.Step34Inst.inst_ing
#check @RBM.Gauss.Step34Inst.sz0_caseI
#check @RBM.Gauss.Step34Inst.sz0_hs0
#check @RBM.Gauss.Step34Inst.sz0_hst
#check @RBM.Gauss.Step34Inst.sz0_ht
#check @RBM.Gauss.Step34Inst.sz0_con
#check @RBM.Gauss.Step34Inst.inst_OeqNQ
#check @RBM.Gauss.InductionDefsInst.sInst
#check @RBM.Gauss.InductionDefsInst.tInst
#check @RBM.Gauss.InductionDefsInst.z0
#check @RBM.Gauss.InductionDefsInst.flow_z0
-- lem:SEforLn (`Induction/SEforLn2`, ae259a6)
#check @RBM.Gauss.Sizes.stSEforLn_holds
-- the good set, exit times, good event (`Induction/GridGoodN`, 2f246bf)
#check @RBM.Gauss.Sizes.GoodSetN
#check @RBM.Gauss.Sizes.measurableGoodSetN
#check @RBM.Gauss.Sizes.GridGoodNConcl
#check @RBM.Gauss.Sizes.GridGoodN
#check @RBM.Gauss.Sizes.gridGoodN_holds
#check @RBM.Path.gridExitTauN
#check @RBM.Path.goodExitTauN
#check @RBM.Path.mem_of_lt_gridExitTauN
#check @RBM.Path.gridExitTauN_eq_of_forall_mem
#check @RBM.Path.gridExitTauN_measurableSet
#check @RBM.Path.goodExitMeasN
#check @RBM.Gauss.GridGoodNInst.vg
#check @RBM.Gauss.GridGoodNInst.Kg
#check @RBM.Gauss.GridGoodNInst.gridGood_instance
#check @RBM.Gauss.GridGoodNInst.gridGood_instance_nonempty
-- matrix-level `ℰ` terms, scales
#check @RBM.Gauss.Sizes.STksimLKM
#check @RBM.Gauss.Sizes.STelklkM
#check @RBM.Gauss.Sizes.STegtM
#check @RBM.Gauss.Sizes.STBctl_mono
#check @RBM.Gauss.Sizes.STBctl_pos
#check @RBM.Gauss.etaT
#check @RBM.Gauss.etaT_pos
#check @RBM.Gauss.loopOf
#check @RBM.lemT_lt_one
-- `≺`, high probability, the walk (`Defs/StochDomAt` 9e2b00f, `Path/Walk` ddf5f74)
#check @RBM.Gauss.Sizes.Prec
#check @RBM.StochDomAt.mul
#check @RBM.StochDomAt.trans
#check @RBM.StochDomAt.of_subset
#check @RBM.Gauss.HighProbAt
#check @RBM.Gauss.HighProbAt.nonempty
#check @RBM.Path.highProbAt_iInter
#check @RBM.Path.TimeIcc
#check @RBM.Path.PathΩ
#check @RBM.Path.pathP
#check @RBM.Path.pathH
#check @RBM.Path.filt
#check @RBM.Path.gridTime
#check @RBM.Path.gridStep
#check @RBM.Path.map_pathH_eq
-- S3-10a (`Induction/NQGood1`, 691566a)
#check @RBM.Ind.driftTensorN
#check @RBM.Ind.driftTensorN_norm_le_of_goodSet
#check @RBM.Ind.driftTensorN_far_of_goodSet
#check @RBM.Ind.STXiLKM_crudeN
#check @RBM.Ind.nqGood1C
#check @RBM.Ind.eeShiftErrN
#check @RBM.Ind.NQGood1Inst.zero_mem_goodSetN_inst
#check @RBM.Ind.NQGood1Inst.drift_norm_instance
-- S3-10b (`Induction/NQGood2`, cc96b69)
#check @RBM.Ind.nonAltClsN
#check @RBM.Ind.kappaNonAltN
#check @RBM.Ind.epsNonAltN
#check @RBM.Ind.dDriftNonAltN
#check @RBM.Ind.cQVNonAltN
#check @RBM.Ind.kappaNonAltN_succ_mul_Bctl_pow_le
#check @RBM.Ind.nonAlt_hA0clsN
#check @RBM.Ind.nonAlt_hdriftN
#check @RBM.Ind.nonAlt_hDclsN
#check @RBM.Ind.hQ_nonAltN
#check @RBM.Ind.subGaussStop_nonAltN
#check @RBM.Ind.NQGood2Inst.tau0
#check @RBM.Ind.NQGood2Inst.tau0_pos
#check @RBM.Ind.NQGood2Inst.subGaussStop_instance
#check @RBM.Ind.NQGood2Inst.gridAssemblyHyp_instance
-- S3-11 (`Induction/NQBudget`, 5b887a6)
#check @RBM.Ind.assembledRHSNonAltN
#check @RBM.Ind.nqBudget_qvFar
#check @RBM.Ind.tbInitN
#check @RBM.Ind.tbDriftN
#check @RBM.Ind.tbQvN
#check @RBM.Ind.tbInitNonAltN
#check @RBM.Ind.tbDriftNonAltN
#check @RBM.Ind.tbQvNonAltN
#check @RBM.Ind.budgetNonAltN
#check @RBM.Ind.NQBudgetInst.budgetNonAltN_instance
-- proxies and assembly (`Induction/AzumaProxyN` 43ab861, `Induction/GridAssemblyN` 686cf71, `StepDecompN`)
#check @RBM.Ind.AzumaSubGN
#check @RBM.Ind.azumaSubGN
#check @RBM.Ind.azumaProxy_subG_ugen
#check @RBM.Ind.azumaProxy_subG_goodExit
#check @RBM.Ind.azumaProxy_pos_gridExitTauN
#check @RBM.Ind.GridAssemblyHypN
#check @RBM.Ind.AssembledN
#check @RBM.Ind.assembledN
#check @RBM.Ind.SubGaussStopN
#check @RBM.Ind.ZvecN
#check @RBM.Ind.stepErrN
#check @RBM.Ind.AzumaProxyNInst.Einst
#check @RBM.Ind.AzumaProxyNInst.Γ4
#check @RBM.Ind.AzumaProxyNInst.Λ3
#check @RBM.Ind.AzumaProxyNInst.Φ1

/-! ## 2. Pinned vocabulary in `RBM.Gauss.Sizes` (T2186 targets 1-3; defined in `RBM.Gauss.Sizes` verbatim:
`STNQConcl'`, `STOeqNQ'` in `Induction/Step34PinsP`, the rest in `Induction/NQLin`) -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes.T2186Check

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

section Pins

variable {d : ℕ} (sz : Sizes d)

/-- **`lem:STOeq_NQ`, primed** (`3_5:1136`, bound `(am;asoiuw)` `3_5:1143-1148`; DECISIONS §62 (1), the form of
RBM2D `STOeqPT`, `Induction/Defs.lean:247` at `c9a24cf`): the merged `STNQConcl` (`Step34Pins.lean:428`) with
the hypothesis `Ξ̂^{𝓛-𝒦}_m ≺ XLK m` for `1 ≤ m ≤ n_` (the current length included) and the random self-term
`B_u^{1/6} · STsupXiLK … (s n) u n_` replaced by the deterministic `B_u^{1/6} · XLK n_ n u`
(paper-delta candidate `T2186a`). -/
def STNQConcl' (E s t : ℕ → ℝ) : Prop :=
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
        STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ)) (sz.Bctl n (q.1 : ℝ)) n_ p)

/-- **The linear set `G_lin`** (DECISIONS §62 (2); supervisor 2026-10-05-0755 answer 2, (R)): the clauses
(D1), (D2), (D3) of `GoodSetN` (`GridGoodN.lean:124`) with a separate deterministic level each:
(D1') `‖[𝒦^{(l)}∼(𝓛-𝒦)]^{(k)}‖ ≤ Γ(ΓΦ₁)B^k/η` (`3 ≤ l ≤ k`), (D2') `‖ℰ^{(𝓛-𝒦)×(𝓛-𝒦)}‖ ≤ Γ(ΓΦ₂)B^k/η`
(linear in `Φ₂`, in place of `Γ k (ΓΦ)²`), (D3') `‖ℰ^{G̃}‖ ≤ Γ(ΓΦ₃)B^k/η`. -/
def GoodLinN (n : ℕ) (E u : ℝ) (k : ℕ) (Γ Φ₁ Φ₂ Φ₃ : ℝ) :
    Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
  {H | (∀ l : ℕ, 3 ≤ l → l ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖STksimLKM sz n E u H l (loopOf σ a)‖ ≤ Γ * (Γ * Φ₁) * ((sz.Bctl n u) ^ k / etaT E u)) ∧
    (∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖STelklkM sz n E u H (loopOf σ a)‖ ≤ Γ * (Γ * Φ₂) * ((sz.Bctl n u) ^ k / etaT E u)) ∧
    (∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖STegtM sz n E u H (loopOf σ a)‖ ≤ Γ * (Γ * Φ₃) * ((sz.Bctl n u) ^ k / etaT E u))}

end Pins

/-- `lem:STOeq_NQ` primed (`3_5:1136`): case (i), the conclusion `STNQConcl'`. -/
def STOeqNQ' (d : ℕ) : Prop := STIngR d STCaseI (fun sz E s t => STNQConcl' sz E s t)

/-- The (D1') level from the controls of lengths `2 ≤ m ≤ k-1` (`3_5:1058-1061`; the lengths `k-l+2`,
`3 ≤ l ≤ k`, of conjunct 2 of `STSEforLnConcl`); `0` for `k = 2`. -/
def nqLinPhi1 (XLK : ℕ → ℝ) (k : ℕ) : ℝ := ∑ m ∈ Finset.Icc 2 (k - 1), XLK m

/-- The (D2') level `Φ₂ = Σ_{n'} XLK(k+2-n') (XL(n'₁) XL(n'₂))^{1/2} + B^{1/6} Φ_cur` (conjunct 3 of
`STSEforLnConcl` with the controls in place of `Ξ̂`; `B` is the caller's `B_v` at the grid endpoint, `Φ_cur`
the deterministic control of the current length). -/
def nqLinPhi2 (XL XLK : ℕ → ℝ) (B : ℝ) (k : ℕ) (Φcur : ℝ) : ℝ :=
  ∑ n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
      XLK (k + 2 - n') * (XL (STn12 n').1 * XL (STn12 n').2) ^ (1 / 2 : ℝ) +
    B ^ (1 / 6 : ℝ) * Φcur

/-- The (D3') level `(XL(n₁) XL(n₂))^{1/2}`, `(n₁, n₂) = STn12E k` (`𝓛`-lengths `k-1 … k+1`; conjunct 1 of
`STSEforLnConcl`). -/
def nqLinPhi3 (XL : ℕ → ℝ) (k : ℕ) : ℝ := (XL (STn12E k).1 * XL (STn12E k).2) ^ (1 / 2 : ℝ)

section NQLinGood

variable {d : ℕ}

/-- **The conclusion of the pin `NQLinGood`** at `(sz, E, s, t)` (the shape of `GridGoodNConcl`,
`GridGoodN.lean:505`): for every grid end `v ∈ [s,t]`, grid size `K`, loop length `k ≥ 2`, and deterministic
controls `XL m n`, `XLK m n ≥ 1` of `Ξ̂^{𝓛}_m` (`m ≤ k+1`) and `Ξ̂^{𝓛-𝒦}_m` (`m ≤ k`, the current length
included) uniformly on `[s_n, v_n]`, with high probability the grid walk is in `GoodLinN` at every
`j ≤ K n`, at the levels `nqLinPhi1`, `nqLinPhi2` (with `B = B_{v_n}`, `Φ_cur = XLK k n`), `nqLinPhi3`. -/
def NQLinConcl (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  ∀ v : ℕ → ℝ, (∀ n, s n ≤ v n) → (∀ n, v n ≤ t n) → ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) →
    ∀ k : ℕ, 2 ≤ k → ∀ XL XLK : ℕ → ℕ → ℝ, (∀ m n, 1 ≤ XL m n) → (∀ m n, 1 ≤ XLK m n) →
    (∀ m : ℕ, 1 ≤ m → m ≤ k + 1 →
      Prec sz (U := fun n => TimeIcc s v n)
        (fun n u ω => STXiL sz n (E n) (u : ℝ) m ω) (fun n _ _ => XL m n)) →
    (∀ m : ℕ, 1 ≤ m → m ≤ k →
      Prec sz (U := fun n => TimeIcc s v n)
        (fun n u ω => STXiLK sz n (E n) (u : ℝ) m ω) (fun n _ _ => XLK m n)) →
    ∀ C : ℝ, (∀ᶠ n in atTop, ((K n + 1 : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C) →
    ∀ ε : ℝ, 0 < ε →
      HighProbAt (pathP sz) sz.size (fun n => {ω | ∀ j ≤ K n,
        pathH sz s v K n j ω ∈ GoodLinN sz n (E n) (gridTime s v K n j) k
          (((sz.size n : ℕ) : ℝ) ^ ε) (nqLinPhi1 (fun m => XLK m n) k)
          (nqLinPhi2 (fun m => XL m n) (fun m => XLK m n) (sz.Bctl n (v n)) k (XLK k n))
          (nqLinPhi3 (fun m => XL m n) k)})

/-- **Pin (`NQLinGood`)**: the Step 3-4 ingredient shape (`STIngR`, any regime) with the conclusion
`NQLinConcl` (as `GridGoodN`, `GridGoodN.lean:528`). -/
def NQLinGood (d : ℕ) : Prop := STIngR d STAny (fun sz E s t => NQLinConcl sz E s t)

end NQLinGood

end RBM.Gauss.Sizes.T2186Check

/-! ## 3. Pinned vocabulary in `RBM.Ind` (T2186 targets 4-5; defined in `RBM.Ind` verbatim, `Induction/NQLin`) -/

namespace RBM.Ind.T2186Check

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Ind RBM.Gauss.Sizes.T2186Check

/-- **The linear drift level** (replaces `dDriftNonAltN`, `NQGood2.lean:96`): the sum of the `k-2` copies of
(D1'), one (D2') and one (D3'): `Γ·Γ·(B_u^k/η_u)·((k-2)Φ₁ + Φ₂ + Φ₃)`; no additive `W^{-D'}`. -/
def dDriftLinN {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (k : ℕ) (Γ Φ₁ Φ₂ Φ₃ : ℝ) : ℝ :=
  Γ * Γ * ((sz.Bctl n u) ^ k / etaT E u) * (((k : ℝ) - 2) * Φ₁ + Φ₂ + Φ₃)

/-- **The exit time of the grid walk from `GoodSetN ∩ GoodLinN`** (the merged generic `gridExitTauN`,
`GridGoodN.lean:169`; `GoodSetN` is used at the crude level `Φ`, only its level-free clauses and (D4)). -/
def nqLinExitTauN {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (s v : ℕ → ℝ) (K : ℕ → ℕ) (k : ℕ)
    (Γ Λ Φ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (τ' D' : ℝ) (n : ℕ) : PathΩ sz → ℕ :=
  gridExitTauN sz s v K n (fun j =>
    sz.GoodSetN n (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D' ∩
      GoodLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n))

/-- **The right-hand side of the merged `AssembledN` at `m = K n` with the linear drift**: the merged
`assembledRHSNonAltN` (`NQBudget.lean:77`) with `dDriftNonAltN … (Γ n) (Φ n)` replaced by
`dDriftLinN … (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)`; no crude level `Φ` (the QV proxy `cQVNonAltN` has none). -/
def assembledRHSLinN {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (Λg κ' ε : ℝ) (Γ Λ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (D' D'' D_Y τK εq X0 : ℝ) (a : Fin k → Zd d (sz.L n)) : ℝ :=
  kappaNonAltN d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) 0 (K n) * X0 +
    epsNonAltN d k Λg κ' ((sz.W n : ℕ) : ℝ) 0 (K n) * ((sz.W n : ℕ) : ℝ) ^ (-D') +
    gridStep s v K n * ∑ j ∈ Finset.range (K n),
      (kappaNonAltN d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) (j + 1) (K n) *
          dDriftLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) +
        epsNonAltN d k Λg κ' ((sz.W n : ℕ) : ℝ) (j + 1) (K n) * ((sz.W n : ℕ) : ℝ) ^ (-D')) +
    ((sz.size n : ℕ) : ℝ) ^ εq * Real.sqrt (∑ j ∈ Finset.range (K n),
      (cQVNonAltN sz E s v K n k Λg κ' ε Γ Λ D'' (K n) a j : ℝ)) +
    ((sz.size n : ℕ) : ℝ) ^ (-D_Y) +
    ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k *
      stepErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1))
        (gridStep s v K n)
        (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ k)

/-! ## 4. Pinned statements (T2186 proves each with exactly this statement) -/

/-- Target 1b (`RBM.Gauss.Sizes.stOeqNQ'_of_stOeqNQ`, public, `Induction/Step34PinsP`): the merged pin
implies the primed one. -/
def T2186_stOeqNQ'_of_stOeqNQ : Prop := ∀ d : ℕ, STOeqNQ d → STOeqNQ' d

/-- Target 1a (`RBM.Gauss.Sizes.stNQConcl'_of_stNQConcl`, **private**, `Induction/Step34PinsP`; registry: a
public form would put `STNQConcl` among the found premises): old conclusion implies new. -/
def T2186_stNQConcl'_of_stNQConcl : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ), sz.SizeTendsto → (∀ n, t n < 1) →
    STNQConcl sz E s t → STNQConcl' sz E s t

/-- Target 2b (`RBM.Gauss.Sizes.measurableGoodLinN`). -/
def T2186_measurableGoodLinN : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (k : ℕ) (Γ Φ₁ Φ₂ Φ₃ : ℝ),
    MeasurableSet (GoodLinN sz n E u k Γ Φ₁ Φ₂ Φ₃)

/-- Target 2c (`RBM.Gauss.Sizes.goodSetN_subset_goodLinN`): `GoodSetN` lies in `GoodLinN` at
`Φ₁ = Φ₃ = Φ`, `Φ₂ = kΓΦ²` (the merged quadratic level). -/
def T2186_goodSetN_subset_goodLinN : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (k : ℕ) (Γ Λ Φ τ' D' : ℝ),
    sz.GoodSetN n E u k Γ Λ Φ τ' D' ⊆ GoodLinN sz n E u k Γ Φ ((k : ℝ) * Γ * Φ ^ 2) Φ

/-- Target 3 (`RBM.Gauss.Sizes.nqLinGood_holds`). -/
def T2186_nqLinGood_holds : Prop := ∀ d : ℕ, NQLinGood d

/-- Target 4a (`RBM.Ind.dDriftNonAltN_eq_lin`): the merged quadratic level is the linear level at
`Φ₁ = Φ₃ = Φ`, `Φ₂ = kΓΦ²`. -/
def T2186_dDriftNonAltN_eq_lin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (k : ℕ) (Γ Φ : ℝ),
    dDriftNonAltN sz n E u k Γ Φ = dDriftLinN sz n E u k Γ Φ ((k : ℝ) * Γ * Φ ^ 2) Φ

/-- Target 4b (`RBM.Ind.driftTensorN_norm_le_of_goodLin`). -/
def T2186_driftTensorN_norm_le_of_goodLin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {n : ℕ} {E u Γ Φ₁ Φ₂ Φ₃ : ℝ} {k : ℕ}, 2 ≤ k →
    ∀ {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ},
      M ∈ GoodLinN sz n E u k Γ Φ₁ Φ₂ Φ₃ →
      ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
        ‖driftTensorN sz n E u M σ a‖ ≤ dDriftLinN sz n E u k Γ Φ₁ Φ₂ Φ₃

/-- Target 4c (`RBM.Ind.nqLin_hdriftN`): the field `hdrift` on `{H_j ∈ GoodLinN(u_j), j < τ}`. -/
def T2186_nqLin_hdriftN : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {n k : ℕ}, 2 ≤ k → ∀ (σ : Fin k → Bool) (E s v : ℕ → ℝ) (K : ℕ → ℕ)
    (Γ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (τ : PathΩ sz → ℕ),
    (∀ ω j, j < τ ω → pathH sz s v K n j ω ∈
      GoodLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)) →
    ∀ ω j, j < K n → j < τ ω → ∀ b : Fin k → Zd d (sz.L n),
      ‖driftTensorN sz n (E n) (gridTime s v K n j) (pathH sz s v K n j ω) σ b‖ ≤
        dDriftLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)

/-- Target 4d (`RBM.Ind.nqLinExitMeasN`): `{j < nqLinExitTauN}` is `filt j`-measurable. -/
def T2186_nqLinExitMeasN : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (Γ Λ Φ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (τ' D' : ℝ)
    (j : ℕ), MeasurableSet[filt sz j] {ω | j < nqLinExitTauN sz E s v K k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D' n ω}

/-- Target 4e (`RBM.Ind.subGaussStop_linN`): the merged `subGaussStop_nonAltN` (`NQGood2.lean:564`) with the
exit time `nqLinExitTauN` (from `azumaProxy_subG_ugen`, `AzumaProxyN.lean:980`); same hypotheses, same
proxy `cQVNonAltN` (independent of `Φ, Φ₁, Φ₂, Φ₃`). -/
def T2186_subGaussStop_linN : Prop :=
  ∀ {d k : ℕ} (Λg κ' : ℝ) (_hd : 3 ≤ d) (_hk : 2 ≤ k) (_hΛg : 0 < Λg)
    (_hκ' : 0 < κ') (sz : Sizes d) {E s v : ℕ → ℝ} {K : ℕ → ℕ} (_hE : ∀ n, |E n| < 2)
    (_hs0 : ∀ n, 0 ≤ s n) (_hsv : ∀ n, s n ≤ v n) (_hv1 : ∀ n, v n < 1) (n : ℕ)
    (_hwL : v n ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (_hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - v n) / (1 - s n)) (_hκm : κ' ≤ (mE (E n)).im)
    (_hg : 0 < sz.lam n) (_hgΛ : sz.lam n ≤ Λg) {ε τ' D' D'' : ℝ}
    (_hW : 1 < ((sz.W n : ℕ) : ℝ)) (_hε0 : 0 < ε) (_hε1 : ε < 1)
    (_hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (_hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (_hD'' : (k : ℝ) + 1 < D'') {σ : Fin k → Bool} (_hσ : ∃ i, σ i = σ (finRotate k i))
    (Γ Λ Φ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (_hΓ : 0 ≤ Γ n) (_hΛ : 0 ≤ Λ n) (m : ℕ) (_hm : m ≤ K n)
    (a : Fin k → Zd d (sz.L n)) (j : ℕ) (_hj : j < m)
    (_hδ : ((sz.W n : ℕ) : ℝ) ^ (-D') + eeShiftErrN d (sz.L n) (sz.W n) (E n) k
      (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'')),
    SubGaussStopN sz (E n) σ (gridTime s v K n)
      (nqLinExitTauN sz E s v K k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D' n) (fun j ω => ZvecN sz E s v K n j σ ω) m a j
      (cQVNonAltN sz E s v K n k Λg κ' ε Γ Λ D'' m a j)

/-- Target 5b (`RBM.Ind.budgetNonAltLinN`; hypotheses in this order, named `hk hε₁ hE hs0 hsv hv1 hK hη hΔη
hΓ hΛ hΦ₁ hΦ₂ hΦ₃ hlog hX0 hR ha1 ha2 ha3 he1 he2 he3 he4`): the merged `budgetNonAltN` (`NQBudget.lean:555`,
T2179 check §3) at the linear drift: `ha2` has `Γ²` (`(N^{ε₁})^2`) in place of `Γ³`, and the right side is
`N^{ε₀}(Λ^{1/2} + Φ₁ + Φ₂ + Φ₃) B_v^k` (no `Φ²`, no crude level). -/
def T2186_budgetNonAltLinN : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (Λg κ' ε : ℝ)
    (Γ Λ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (D' D'' D_Y D_t τK εq ε₀ ε₁ X0 : ℝ) (a : Fin k → Zd d (sz.L n)),
    (2 ≤ k) → (0 ≤ ε₁) →
    (|E n| < 2) → (0 ≤ s n) → (s n ≤ v n) → (v n < 1) → (K n ≠ 0) →
    ((etaT (E n) (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) →
    (gridStep s v K n * (etaT (E n) (v n))⁻¹ ≤ 1) →
    (Γ n = ((sz.size n : ℕ) : ℝ) ^ ε₁) → (1 ≤ Λ n) → (0 ≤ Φ₁ n) → (0 ≤ Φ₂ n) → (0 ≤ Φ₃ n) →
    ((∑ j ∈ Finset.range (K n), gridStep s v K n / etaT (E n) (gridTime s v K n j)) ≤
      (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) →
    (X0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ k) →
    ((∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k *
        stepErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1))
          (gridStep s v K n)
          (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ k)) ≤
      ((sz.size n : ℕ) : ℝ) ^ (-D_t)) →
    (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) * ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6) →
    ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
        (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 2 *
        ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12) →
    (((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
        ((sz.size n : ℕ) : ℝ) ^ ε₁ *
        Real.sqrt ((k : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1))) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12) →
    (((sz.size n : ℕ) : ℝ) ^ k *
        (((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' * ((sz.W n : ℕ) : ℝ) ^ (-D')) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12) →
    (((sz.size n : ℕ) : ℝ) ^ εq * (((sz.size n : ℕ) : ℝ) ^ k *
        Real.sqrt ((k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε * ((sz.W n : ℕ) : ℝ) ^ (-D'')))) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12) →
    (((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-D_Y) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6) →
    (((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-D_t) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6) →
    assembledRHSLinN sz E s v K n k Λg κ' ε Γ Λ Φ₁ Φ₂ Φ₃ D' D'' D_Y τK εq X0 a ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n) *
        (sz.Bctl n (v n)) ^ k

end RBM.Ind.T2186Check

end
