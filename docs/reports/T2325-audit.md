Auditor model: claude-opus-5-5

# T2325 audit (round 1): BA-DP2, report-only design probe. Written Thu Oct  8 07:34:53 UTC 2026 (date -u)

Inputs: ticket `docs/tickets/T2325.md`, `docs/reports/T2325-prove.md` (296 lines), `docs/reports/T2325-portmap.md` (161 lines), branch `t/T2325` at 05b9293. Audit worktree `RBM3D-wt/T2325-audit1`, detached at 05b9293. The targets are the report's tables (answers (i) and (ii), the re-portmap, the totals, one cap). The probe is optional, has no pinned target, and is never merged.

## 1. Diff, build, axioms, hygiene (probe `RBM3D/Probe/T2325BAGen.lean`)
```
$ git diff --stat main...t/T2325
 RBM3D/Probe/T2325BAGen.lean | 213 ++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 213 insertions(+)
$ git diff --stat 044707b main -- RBM3D/Graph RBM3D/Induction RBM3D/Universality RBM3D/BA/{FlowPins,MReg,CouplingWindow,KKernel}.lean | wc -l
       0            # the cited files are unchanged between the prover's base 044707b and main 0da5856
$ lake build RBM3D.Probe.T2325BAGen        (audit worktree; error lines: grep -c '^error' = 0)
✔ [3906/3906] Built RBM3D.Probe.T2325BAGen (3.9s)
Build completed successfully (3906 jobs).
$ lake env lean RBM3D/Probe/T2325BAGen.lean; echo "exit $?"
exit 0
$ lake env lean Ax.lean     # the probe file plus 7 #print axioms lines
'RBM.Probe.T2325.baEngine_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2325.baGraph_size_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2325.inst_size_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2325.BALvl1Good_ofLGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2325.ba_mu_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2325.baMu_wf' does not depend on any axioms
'RBM.Probe.T2325.scalarM_hyp_fails_at_baD' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom|^ *axiom " RBM3D/Probe/T2325BAGen.lean | wc -l
       0
$ grep -n "^import" RBM3D/Probe/T2325BAGen.lean
6:import RBM3D.Graph.LWExpTerm5
7:import RBM3D.Graph.BAExpandWOrd          # merged modules only, not RBM3D
$ git status --short docs/reports/T2325*   (main worktree)
?? docs/reports/T2325-portmap.md
?? docs/reports/T2325-prove.md
```
The diff contains only sole-writable files, and no merged file changes. The report sizes are within the limits (portmap 161 ≤ 400, prove 296 ≤ 300).

## 2. Citations behind every "parametric" / "instantiate" verdict, and the main "twin" verdicts
Script `cites.sh` prints `sed -n <line>p` of each cited file:line, in the audit worktree. OK means the cited declaration is on that line.
```
OK   Graph/LWExpTerm5.lean:189 expandG | def expandG {X : Type*} (st : X → Option (List ((ℕ × ℕ) × X))) : ℕ → X → ...
OK   Graph/LWExpTerm5.lean:199 ExpandGSum | def ExpandGSum {X : Type*} (st : X → Option (List ((ℕ × ℕ) × X))) ...
OK   Graph/LWExpTerm5.lean:234 expandG_sum | theorem expandG_sum {X : Type*} (st : ...
OK   Graph/LWExpTerm5.lean:594 lwExpandIdentity_holds | theorem lwExpandIdentity_holds : ∀ (sel : Sel) (fuel : ℕ), ...
OK   Graph/LWExpTerm5.lean:124 RCand | structure RCand (P : PGraph (Fin 2)) where
OK   Graph/LWLvl1.lean:989 Lvl1Good | def Lvl1Good (Γ : LGraph E₁ I₁) (Q : LGraph E₂ I₂) : Prop :=
OK   Graph/LWLvl1.lean:3778 Lvl1Mu / :3782 Lvl1Lt (a b : ℕ × ℕ × ℕ × ℕ) / :3785 lvl1Lt_wf / :3790 lvl1_mu_lt
OK   Graph/LWLvl1.lean:3981 lvl1Cutoff (c : ℝ) (K0 d : ℕ) (D : ℝ) (G : Counters) : ℕ
OK   Graph/LWLvl1.lean:3989 lvl1_size_le (... (G : Counters) ... (Q : Counters) ...)
OK   Graph/LWLvl1.lean:3260 LocStep (m : ℂ) : PGraph E → List (PGraph E) → Prop  / :3290 / :3590 / :3655 / :3828 / :3907
OK   Graph/BAVocab.lean:55 structure BAGraph (E I : Type*) extends RBM.Graph.LGraph E I
OK   Graph/BAVocab.lean:39 structure BALData (ι : Type*) extends RBM.Graph.LData ι  / :533 counters_ofLGraph / :163 baSplitSolid
OK   Graph/AuxGraph.lean:979 LWGtoAG ; body line 5: (∀ x y, D.M x y = if x = y then m else 0) →
OK   Graph/LWSizeClaim.lean:1118 lwClaimSize ; (hM : ∀ x y, D.M x y = if x = y then m else 0)
OK   BA/KKernel.lean:352 BAK_adj_sum_ge
OK   Graph/AnpKey.lean:41 AnpDetGhAt (d) (Γ : NGraph p q): ∀ L ψ θ ξ, ξ symmetric ≥ 0, ξ ≤ ψ(zdistInf), Σξ² ≤ θ → ...
OK   Graph/AnpKey.lean:689 lwAnpKeyGh_of_det / AnpKey6.lean:862 anpDetGh_holds
OK   Graph/LWPsi.lean:47-66 LWWindow (ε₀) (Ψ : ℕ → ℝ), LWClass, LWPsiRel, LWPsiAll (Φ : ℕ → ℝ → ℝ)
OK   Graph/LWVocab.lean:1339 val_eq_partition (hM : ∀ x, D.M x x = m ...)
OK   Graph/LWStein.lean:1239 owx_integral (hG : GaussIBP sz) ...
OK   Graph/LWExpCert.lean:46 MNode / LWExpCertS1.lean:297 cert_all / LWExpSim.lean:1093 partitionSim
OK   Graph/LocalRegular.lean:1856 PathInv / LocalRegular6d.lean:1107 lw_localregular (p) (m : ℂ) ...
OK   Universality/PinsK.lean:426 UNOURowk ; BA/Step1Fam.lean:361 BAStep1 ; BA/FlowPins.lean:332 FlowFM, :540, :565
OK   Induction/Step34Pins.lean:221 STStep2Concl, :250 STStep3R ; Step2Iterate.lean:284, :1393 ; Step2Defs.lean:119, :363
OK   Induction/Defs.lean:77 STGM, :283 STflowE := fun n => lemE (z n) ; ContractPt.lean:463 ; Contract.lean:1046
OK   Induction/LoopGenN.lean:548 loopGenN ; Step3.lean:377 ; Step4.lean:189 ; PfStep5.lean:2473 ; MainIndRegimes.lean:165
OK   Induction/Step6Kit.lean:737 ST_step6_caseIII_of_pins ; BA/CouplingWindow.lean:688 ; BA/MReg.lean:84
MISS Graph/ScalingOrder.lean:54 nV | /-- internal vertices (internal atoms, in the block Anderson variant ...) -/
```
(The MISS line is the docstring of `nV`. The report cites it as "documents the BA slot", so the citation is accurate.)
Spot checks of the claims a verdict rests on:
```
$ sed -n '322,324p' BA/FlowPins.lean  -> "... it does **not** make the merged band *proofs* generic. -/"
$ sed -n '39p' BA/MReg.lean           -> "Not here: the coupling shift |m(z, λ e^{t/2}) - m(z, λ)| ≤ C t (BA-N1), `BAPropM` (D4)."
$ grep -l GaussIBP Induction/*.lean | wc -l                                   -> 0
$ grep -cE "SB |Theta|KLK|mE |Lloop|STKloop|mSigma|gvarF|Ugen" Induction/ContractPt.lean -> 0   (T6 "instantiate after publishing")
$ sed -n '1229,1231p' Graph/BAVocab.lean -> def baD : BALData (Fin 2) where / G := ![![1,2],![3,4]] / M := ![![5,6],![7,8]]
```
Verdicts checked against the signatures:
- Rows 5, 12, 14 and 17 of portmap §2 ("parametric as is"). Each statement reads only `Counters`, ℕ⁴, an arbitrary carrier `X`, `NGraph`/`ξ`/`ψ`/`θ`, or real sequences. No band object occurs in any of the signatures above. The probe compiles rows 5 and 14 at BA objects (`baGraph_size_le`, `baMu_wf`, `baEngine_sum`). Confirmed.
- Row 6 ("generalization G, 31 lines"). `BALvl1Good_ofLGraph` proves `BALvl1Good (ofLGraph Γ) (ofLGraph Q) ↔ Lvl1Good Γ Q`, and `ba_mu_lt` reuses `Lvl1Lt`. Confirmed.
- Rows 7 to 11, 13, 15 and 16 ("twin"). The signatures read `LocStep m`, `GaussIBP sz` and the scalar-`M` hypothesis. `scalarM_hyp_fails_at_baD` compiles the failure of that hypothesis at the merged `baD`. Confirmed.
- §3 (ii), "no row collapses by instantiation". `STStep3R`, `STflowE`, `STGM` and `STthetaOp` are stated on the band carrier, and FlowPins:324 says in its own text that the band proofs are not made generic. Confirmed. T6 is the only "instantiate" verdict in the chain, and ContractPt has 0 band tokens. Confirmed.

## 3. Coverage of the re-portmap (every remaining BA row)
```
$ sed -n '995,1112p' docs/reports/T2161-portmap.md | grep -oE '^ *BA-[A-Z][0-9]+' | sort -u | wc -l   -> 57
$ ls RBM3D/BA RBM3D/Graph/BA*   (merged files) -> rows D1 D2 D3 D4 D6 D7 P1 P2 P3(KSymbol, 0da5856) G1 S1 S2 S3 L1, L2 partial
```
57 portmap rows, less 13 merged and P3, leave 43 rows: L2 (open part, row L2c), L3, L4; P4-P8, K1-K5, E1-E3, G2-G6, M1-M3, N1-N2 (23 rows); T1-T8, U1-U6, V1-V3 (17 rows). Adding C3-C5 (`T2173-prove.md:234-236`) gives 46. Portmap §5 lists every one of these rows: group A has 26 rows, the chain 17 rows (V2 split a/b), the graph rows are L2c and L3a-d, plus L4. Coverage is complete.

Arithmetic, recomputed by the auditor:
- Group A tickets add up to 25.
- Chain, route T: 27449 + 50891 + 13655 = 91995 lines, so 92 tickets.
- Graph, route T: 31253 lines.
- Totals: route I is 26+25+78+27+7 = 163; route T is 26+25+92+31 = 174. Both match the report.

The cap is one number, 175 (§7). The merge candidates (a) to (e) are each checked against merged code (§6). The (d) and (e) checks rest on MReg:39, CouplingWindow:688 and the content of Ward/KKernel, all verified above.

## 4. Paper deltas
- `B_graphical_lemmas.tex:409` says "we only sketch the proof", and `:497` says "carries over verbatim". This is covered by **T2325a**.
- `7_8_light_weight.tex:2101` says that Steps 3-6 "extend verbatim … except … sec:Step5_larget … parallel those in [RBSO1D, Section 7.3]. We therefore omit the details." This is covered by **T2325c**.
- The scalar-`M` hypothesis of `LWGtoAG` and `lwClaimSize` is shown false at BA data. This is covered by **T2325b**.
- The finding that the paper's "verbatim" steps are ports in Lean is a cost statement, not a statement delta. No uncovered Lean/paper statement difference was found.

## 5. Per-target verdicts
| target | verdict |
|---|---|
| (i) graph-layer table, per declaration family, with file:line and the model object read | PASS |
| (ii) chain table, per BA row, with the ST theorems twinned, the band objects read, verdict and cost | PASS |
| re-portmap covering every remaining row, totals for both routes, one cap | PASS |
| acceptance: diff only the probe; probe `lake env lean` exit 0, no `sorry` | PASS |

## 6. Observations (no RETURN)
1. The report calls BA-P3 (T2324) "in flight". It merged at 0da5856 after the prover's base 044707b. The totals already count it among the 26 used tickets, so no number changes.
2. The probe instance `inst_size_le` uses `L = 1`, `K0 = 0` and `D = -2`, so the lattice is collapsed and the bound is weak (`W^2`). The probe is not a ticket target and has no endpoint theorem, so §4 step 2 does not apply. It shows only that the merged lemma applies at BA counters.
3. The chain and graph estimates (route T at 0.80 × source lines, route I at 1.45 × D) depend on the prover's file-to-row assignment (`chain.py`, `reportcalc.py`, in the prover's scratchpad). The auditor checked the cited declarations, not each file assignment. The report itself labels these "judgment, not script output" (prove report, Narrative).
4. The cap recommended in this report (175, against the current cap of 72 from DECISIONS §128) is, by the ticket's design, a number for the dispatcher to take to Jun. It is not an audit sign-off item.

Verdict: **PASS**.
