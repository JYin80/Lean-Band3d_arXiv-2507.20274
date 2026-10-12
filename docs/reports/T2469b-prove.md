Prover model: claude-sonnet-5-5
## (a) Math preflight
Stage 1a of the row is `docs/reports/T2469-prove.md` (a), lines 2-103 (written Mon Oct 12 20:26:20 UTC 2026): every target PASS (mathematics: 0 `PathInv2` violations at term level, routes close, witnesses exist); the row-level BLOCKED was the
split sign-off of CONTROL H257 (3), given. This report has no separate (a): `docs/reports/T2469b-prove.md` did not exist when stage 1b started (`wc: docs/reports/T2469b-prove.md: open: No such file or directory` in the tool log).
## (a′) Preflight corrections — Mon Oct 12 22:22:51 UTC 2026
No verdict changes. Two statements of `T2469-prove.md` (a) are corrected (its own (a′), lines 105-108, corrects the route of the 18 terms of file 1 and is not repeated):
- Table rows I1 (trA) and I2 (trB), route "ext (0,0) 70L" (`BALocReg1_pathAt_ext`): in Lean both close with `BALocReg2_pathAt_ext2` and one `localReg2_VRepl.same` at the molecule map of the extension (trA: the edge `p.1` becomes the loop `Ǧ_{ββ}`,
  `D₁ = {p.1}`, `D₂ = {Ǧ_{ββ}}`; trB: `D₁ = D₂ = 0`, the two edges agree as multisets in the molecules), 23 and 21 lines (`lines.py` below), no budget lemma.
- Fit row 8 / (c): file 2 estimate 890 lines, central 2,130; delivered `Graph/BALocReg2B` 624 lines (below), `Graph/BALocReg2` 886 lines (`T2469-prove.md` (b)), 1,510 together.
## (b) Script output — stage 1b, L3b2b (targets 1 (b)-(d), 2, 3, 4), branch t/T2469b — Mon Oct 12 22:22:51 UTC 2026
Scripts: `scratchpad/T2469b/` (`evidence.sh`, `evidence2.sh`, `lines.py`, `stmt.py`, `pins.py`, `clash.sh`, `pins.lean` = scratch copy of the check file with `import RBM3D.Graph.BALocReg2B` and the nine pin examples, `mlnames.lean`). Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2469b`.
```
$ git log --oneline -8; git diff --stat main...t/T2469b; wc -l RBM3D/Graph/BALocReg2B.lean
40493044 T2469 (L3b2b): BALocReg2B module docstring: contents of section 6
6fae0035 T2469 (L3b2b): BALocReg2B whitespace-linter fix (one signature line break)
f94dbbd4 T2469 (L3b2b): BALocReg2B instances of the binder baShapeLLBinder_holds and of baLocRegConcl_upto5
62b106f1 T2469 (L3b2b): BALocReg2B weight step with an e2 output at a start term, target 2 at the twisted edge step
6f0e37f4 T2469 (L3b2b): BALocReg2B instances of the moved shapes, stage 2, target 2 and target 3 (section 6)
8a68a7a9 T2469 (L3b2b): BALocReg2B stage 2, shapes e2/macroA/macroB, closed step and contract, composed statement (sections 1-5)
d20f81ed T2469b: merge main into t/T2469b
a931034a T2469: merge L3b2a Graph/BALocReg2 (split; L3b2b follows on t/T2469b)
 RBM3D/Graph/BALocReg2B.lean | 624 ++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 624 insertions(+)
     624 RBM3D/Graph/BALocReg2B.lean
$ for c in 8a68a7a9 6f0e37f4 62b106f1 f94dbbd4 6fae0035 40493044; do git show $c:RBM3D/Graph/BALocReg2B.lean | wc -l; done   # the stop-rule wc -l at the six section commits (stop line 2,000)
8a68a7a9      391
6f0e37f4      510
62b106f1      610
f94dbbd4      626
6fae0035      624
40493044      624
$ python3 lines.py
file lines: 624
/-! ## 1. Outputs and tags -/                                          lines 57-96 (40)
/-! ## 2. Stage 2 (target 1 (b)) -/                                    lines 97-211 (115)
/-! ## 3. Target 1 (c), (d): the shapes `e2`, `macroA`, `macroB` of `B lines 212-345 (134)
/-! ## 4. Target 2: the twin of `LocalRegular2`, closed -/             lines 346-353 (8)
/-! ## 5. Target 3: the composed statement -/                          lines 354-388 (35)
/-! ## 6. Nonempty instances (target 4), every deterministic hypothesi lines 389-624 (236)
BALocReg2B_trA               lines 105-127 (23)
BALocReg2B_trB               lines 131-151 (21)
BALocReg2B_macroA            lines 155-170 (16)
BALocReg2B_macroB            lines 173-208 (36)
baShapePath_e2_tn            lines 218-261 (44)
baShapePath_macroA_tn        lines 265-294 (30)
baShapePath_macroB_tn        lines 298-335 (38)
baPathBinder_holds           lines 338-342 (5)
baPathStep_closed            lines 349-349 (1)
baLocReg15_closed            lines 352-352 (1)
baShapeLLBinder_holds        lines 358-362 (5)
baLocRegConcl_upto5          lines 367-377 (11)
ba_localregular_upto5        lines 381-387 (7)
examples: 15
$ lake build RBM3D.Graph.BALocReg2B 2>&1 | tail -2   # the first line is a replayed linter note of an upstream module
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3847 jobs).
$ lake build RBM3D   # with `import RBM3D.Graph.BALocReg2B` added to RBM3D.lean locally (reverted by `git checkout RBM3D.lean`, not committed); log lines
5526:info: RBM3D.lean:544:0: axiom audit: 13845 theorems, 4390 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
5771:Build completed successfully (4312 jobs).
5772:exit=0
$ lake env lean docs/tickets/checks/T2469-check.lean; echo exit=$?
exit=0 error lines: 0
$ grep -nE "sorry|admit|native_decide|^axiom|^inductive|^structure|: Prop" RBM3D/Graph/BALocReg2B.lean; echo "grep exit=$?"
grep exit=1
$ git diff main...t/T2469b -- RBM3D/Test/Axioms.lean RBM3D.lean | wc -l
       0
```
```
$ lake env lean pins.lean | grep "depends on axioms" | sed ...   # #print axioms of the 13 public theorems and the 3 instance defs of the file, grouped
pins.lean (scratch copy of the check file + the file's import + 9 pin examples + 2 shape examples): exit=0 error lines: 0
[propext, Classical.choice, Quot.sound]: baShapePath_e2_tn baShapePath_macroA_tn baShapePath_macroB_tn baPathBinder_holds baPathStep_closed baLocReg15_closed baShapeLLBinder_holds baLocRegConcl_upto5 ba_localregular_upto5 BALocReg2B_trA BALocReg2B_trB BALocReg2B_macroA BALocReg2B_macroB BALocReg2BInst.outsErT BALocReg2BInst.stepErT BALocReg2BInst.pathInv2_ErT
$ python3 pins.py   # the nine T2469_* pin bodies against the theorem statements (whitespace normalised)
T2469_E2Path       baShapePath_e2_tn          identical-after-whitespace: True
T2469_MacroAPath   baShapePath_macroA_tn      identical-after-whitespace: True
T2469_MacroBPath   baShapePath_macroB_tn      identical-after-whitespace: True
T2469_PathBinder   baPathBinder_holds         identical-after-whitespace: True
T2469_PathStep     baPathStep_closed          identical-after-whitespace: True
T2469_LocReg15     baLocReg15_closed          identical-after-whitespace: True
T2469_Binder6      baShapeLLBinder_holds      identical-after-whitespace: True
T2469_ConclUpto5   baLocRegConcl_upto5        identical-after-whitespace: True
T2469_Upto5        ba_localregular_upto5      identical-after-whitespace: True
$ python3 stmt.py <names>   # statements extracted from the file
theorem baShapePath_e2_tn : BAShapePath BAShape.e2 BAFrameStepTN
theorem baShapePath_macroA_tn : BAShapePath BAShape.macroA BAFrameStepTN
theorem baShapePath_macroB_tn : BAShapePath BAShape.macroB BAFrameStepTN
theorem baPathBinder_holds : ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapePath sh BAFrameStepTN
theorem baPathStep_closed : BAPathStep (untag BALocStepT)
theorem baLocReg15_closed : BALocReg15
theorem baShapeLLBinder_holds : ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapeLL sh BAFrameStepTN
theorem baLocRegConcl_upto5 : ∀ (p : ℕ) (c : ℝ) (K0 d : ℕ) (D : ℝ) (outs errs : List (BAPGraph (Fin 2))), BALocRegConcl p c K0 d D outs errs → (∀ Q ∈ outs ++ errs, Q.img.PathInv2 p ∧ Q.g.nM ≤ p ∧ PGraph.LocReg2 Q.img p) ∧ ∀ Q ∈ outs, PGraph.LocReg1 Q.img ∧ PGraph.LocReg345 Q.img p ∧ (BAShadowPG Q).LocReg345 p
theorem ba_localregular_upto5 : ∀ (p : ℕ) (c : ℝ), 0 < c → ∀ (K0 d : ℕ) (D : ℝ), ∃ outs errs : List (BAPGraph (Fin 2)), BALocRegConcl p c K0 d D outs errs ∧ (∀ Q ∈ outs ++ errs, p ≤ Q.g.waved.countP (fun e => !e.col)) ∧ (∀ Q ∈ outs ++ errs, Q.img.PathInv2 p ∧ Q.g.nM ≤ p ∧ PGraph.LocReg2 Q.img p) ∧ ∀ Q ∈ outs, PGraph.LocReg1 Q.img ∧ PGraph.LocReg345 Q.img p ∧ (BAShadowPG Q).LocReg345 p
theorem BALocReg2B_trA (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hp1 : p.1.σ = true ∧ p.1.circ = true) : ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt (Γ.BAScost_trA p) k a b
theorem BALocReg2B_trB (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hsame : Γ.sameAtom p.1.src q.1.dst = true) (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) : ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt (Γ.BAScost_trB p q) k a b
$ grep -nE "^example|^theorem pathInv2|^theorem stepErT|^def " RBM3D/Graph/BALocReg2B.lean | cut -c1-150
470:example : (∃ Q, (BAShape.e2, Q) ∈ (baPG baPB).withinOutsT pB ∧ Q.img.PathInv2 1) ∧
478:example (far : Bool) : (∃ Q, (BAShape.e2, Q) ∈ (baPG baPB).withinOutsT pB ∧ locCostGeA far (-4) Q) ∧
487:example : (∃ Q, (BAShape.e2, Q) ∈ (baPG baPC).splitOutsT pC qC 0 ∧ Q.img.PathInv2 2) ∧
495:example : (∃ Q, (BAShape.macroB, Q) ∈ (baPG baPC).outsT (fun _ => BAShape.macroB)
521:example : ∃ Q, (BAShape.e2, Q) ∈ ggFT ∧ Q.img.PathInv2 2 := by
526:example : ∃ Q, (BAShape.e2, Q) ∈ BALocReg1Inst.outsEr ∧ Q.img.PathInv2 1 := by
533:def outsErT : List (BAShape × BAPGraph (Fin 2)) := BALocReg1Inst.outsEr.map fun x => (x.1, BAPGraph.twist true true x.2)
535:theorem stepErT : BALocStepT ((baPG BALocReg1Inst.baPEr).twist true true) outsErT :=
538:theorem pathInv2_ErT : ((baPG BALocReg1Inst.baPEr).twist true true).img.PathInv2 1 := (baPathTwist_holds true true _ 1).2 BALocReg1Inst.pathInv2_E
543:example : (∃ Q, (BAShape.e2, Q) ∈ BALocReg2BInst.outsErT ∧ Q.img.PathInv2 1) ∧ ∀ Q ∈ BALocReg2BInst.outsErT.map Prod.snd, Q.img.PathInv2 1 := by
550:example : ∃ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph 2)).partition, ∃ (LT : List (BAShape × BAPGraph (Fin 2))) (Q : BAPGraph (Fin 2)),
558:example : ∃ Q, (BAShape.e2, Q) ∈ (baPG BALocReg2Inst.baPL).outsT (BALocReg2Inst.baPL.tagStd 2) (BALocReg2Inst.baPL.lw2 BALocReg2Inst.pL) ++
567:example : BALocReg1_PathAt (baPB.BAScost_trA pB) 1 0 1 ∧
574:example : BALocReg1_PathAt (baPC.BAScost_trB pC qC) 2 0 1 ∧
584:example : ∃ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph 2)).partition, ∃ (K : ℤ) (Q : BAPGraph (Fin 2)), BAReach K P0 Q ∧ ¬ P0.g.LocStd ∧ Q.g.LocStd ∧
591:example : ∃ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph 2)).partition, P0.g.nM ≤ 2 ∧ P0.img.PathInv2 2 ∧ PGraph.LocReg2 P0.img 2 ∧
599:example : ∃ outs errs : List (BAPGraph (Fin 2)), BALocRegConcl 2 (1 / 4) 2 3 10 outs errs ∧
607:example : ∃ outs errs : List (BAPGraph (Fin 2)), BALocRegConcl 2 (1 / 4) 2 3 10 outs errs ∧
$ clash.sh
public declarations of the new file: 16
files on main mentioning the new names: 0
t/* branches other than t/T2469b scanned: 475, total files with hits: 0
files other than Graph/BALocReg2B.lean in this worktree mentioning the new names: 0
$ lake env lean mlnames.lean | grep -c error; grep -c "^#check" mlnames.lean
0
31
$ lake env lean <copy of the file with linter.unusedVariables true> | grep "not explicitly referenced"
132:83: warning: Variable name `hsame` is not explicitly referenced.
133:5: warning: Variable name `hwf1` is not explicitly referenced.
133:49: warning: Variable name `hwf2` is not explicitly referenced.
$ for f in BAShapeO2B BALocReg2; do git log -1 --format=%h -- RBM3D/Graph/$f.lean; done; grep -n 'RBM1D\|RBM2D' RBM3D/Graph/BALocReg2B.lean | cut -c1-120
00f4a104
ff8a75b9
44:C1: combinatorial except `ba_localregular_upto5` (data `BASelf`, `0 ≤ t < 1`, only through the merged `ba_localregula
```
Instance examples (all in `Graph/BALocReg2B.lean`, section 6; the listing above gives their first lines).  Ticket target 4 (i) = 470; (ii) = 487, stages 495; (iii) = 521; (iv) = 526; (v) = 550 (start term, below), (v′) = 558 (hand-built `baPL`);
(vi) = 584, 591; (vii) = 607 (below); target 3 (a) at `P_B` = 478; target 3 (b) = 599 (below); target 2 (step) at the twisted `edge` step = 543; stage 2 (target 1 (b)) at `P_B`, `P_C` = 567, 574; (viii) = `Graph/BALocReg2` section 6 (merged a931034a).
Witness sizes (from `BASim3.lean:1909` and the examples): `gg` at `P_A` has 31 outputs (23 `band`, 8 `e2`), `ggSplit` at `P_C` has 48 (8 `band`, 1 `e1`, 5 `e2`, 34 `macroB`); the tag existence is `decide +kernel`, the invariant of the parent is a proved family (`pathInv2_A/_B/_C/_Er/_L`).
```
$ sed -n 549,554p RBM3D/Graph/BALocReg2B.lean   # (v)
/-- (v) `weight` at a start term of `p = 2` (`PathInv2 2` at its image by `baPathInit_holds`): the weight step at the blue circled loop `Ǧ_{β₀β₀}` has an `e2` output, and `baShapePath_e2_tn` gives the invariant at it -/
example : ∃ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph 2)).partition, ∃ (LT : List (BAShape × BAPGraph (Fin 2))) (Q : BAPGraph (Fin 2)),
    BAFrameStepTN P0 LT ∧ (BAShape.e2, Q) ∈ LT ∧ P0.img.PathInv2 2 ∧ Q.img.PathInv2 2 := by
  obtain ⟨P0, hP0, LT, hLT, Q, hQ⟩ := BALocReg2B_start_weight_e2
  exact ⟨P0, hP0, LT, Q, ⟨BAGraph.partition_normal _ P0 hP0, hLT⟩, hQ, baPathInit_holds 2 P0 hP0,
    baShapePath_e2_tn _ _ ⟨BAGraph.partition_normal _ P0 hP0, hLT⟩ Q hQ 2 (baPathInit_holds 2 P0 hP0)⟩
$ sed -n 598,603p RBM3D/Graph/BALocReg2B.lean   # target 3 (b)
/-- target 3 (b) at `p = 2`, `c = 1/4`, `K0 = 2`, `d = 3`, `D = 10`: the hypothesis `BALocRegConcl` is the conclusion of `ba_localregularX` at `baShapeLLBinder_holds` (the engine, proved), and the lists carry (1)-(5) -/
example : ∃ outs errs : List (BAPGraph (Fin 2)), BALocRegConcl 2 (1 / 4) 2 3 10 outs errs ∧
    (∀ Q ∈ outs ++ errs, Q.img.PathInv2 2 ∧ Q.g.nM ≤ 2 ∧ PGraph.LocReg2 Q.img 2) ∧
      ∀ Q ∈ outs, PGraph.LocReg1 Q.img ∧ PGraph.LocReg345 Q.img 2 ∧ (BAShadowPG Q).LocReg345 2 := by
  obtain ⟨outs, errs, hC, -⟩ := ba_localregularX baShapeLLBinder_holds 2 (1 / 4) (by norm_num) 2 3 10
  exact ⟨outs, errs, hC, baLocRegConcl_upto5 2 (1 / 4) 2 3 10 outs errs hC⟩
$ sed -n 606,618p RBM3D/Graph/BALocReg2B.lean   # (vii)
/-- (vii) target 3 (c) at `p = 2`, `c = 1/4`, `K0 = 2`, `d = 3`, `D = 10` with the identity of expectations at the flow point of `BAEngineInst` (`d = 3`, `L = 4`, `W = 2`, `flowP_data`, `ℓ0`); no hypothesis -/
example : ∃ outs errs : List (BAPGraph (Fin 2)), BALocRegConcl 2 (1 / 4) 2 3 10 outs errs ∧
    (∀ Q ∈ outs, Q.g.LocStd ∧ Q.g.nM ≤ 2 ∧ PGraph.LocReg345 Q.img 2 ∧ (BAShadowPG Q).LocReg345 2) ∧
    ∫ ω, (BAGraph.ofLGraph (fxyPowGraph 2)).val
        (BAlwData 3 4 2 RBM.BA.CouplingWindowInst.g0P RBM.BA.CouplingWindowInst.EP RBM.BA.CouplingWindowInst.t0P RBM.BA.CouplingWindowInst.m0P ω)
        BASymm1Inst.ℓ0 ∂(PF 3 4 2 0) =
      ∫ ω, BAComb.val (outs ++ errs)
        (BAlwData 3 4 2 RBM.BA.CouplingWindowInst.g0P RBM.BA.CouplingWindowInst.EP RBM.BA.CouplingWindowInst.t0P RBM.BA.CouplingWindowInst.m0P ω)
        BASymm1Inst.ℓ0 ∂(PF 3 4 2 0) := by
  obtain ⟨outs, errs, h, -, h1, h2⟩ := ba_localregular_upto5 2 (1 / 4) (by norm_num) 2 3 10
  exact ⟨outs, errs, h, fun Q hQ => ⟨(h.1 Q hQ).1, (h1 Q (List.mem_append_left _ hQ)).2.1, (h2 Q hQ).2.1, (h2 Q hQ).2.2⟩,
    h.2.2.2 4 2 (by norm_num) RBM.BA.CouplingWindowInst.g0P RBM.BA.CouplingWindowInst.EP RBM.BA.CouplingWindowInst.t0P RBM.BA.CouplingWindowInst.m0P
      RBM.BA.CouplingWindowInst.flowP_data.2.2 RBM.BA.CouplingWindowInst.flowP_data.1.le RBM.BA.CouplingWindowInst.flowP_data.2.1 BASymm1Inst.ℓ0⟩
```
Narrative.
1. Scope: L3b2b of T2469 (CONTROL H257 (3)): targets 1 (b)-(d), 2, 3, 4, in `RBM3D/Graph/BALocReg2B.lean`; target 1 (a) is `Graph/BALocReg2` (merged a931034a, not edited). The branch is t/T2469 (ff8a75b9) plus the merge of main (d20f81ed). Reserve `BALocReg2C` not used.
2. Root import: `RBM3D.lean` is not on the branch (`git diff main...t/T2469b` is the one file). The hub adds `import RBM3D.Graph.BALocReg2B` at merge (rule (A) 4; CONTROL merge log for L3b2a: "root import added at merge (the branch had none)"); the full-library lines above come from a local edit, reverted.
3. Stop rule (CONTROL H134): `wc -l` at the six section commits gave 391, 510, 610, 626, 624, 624 lines; stop line 2,000.
4. Section 1: `BALocReg2B_group` is the path form of the private `BAShapeO2B_group` (`BALocReg1_pathInv2_pack`: a group of outputs whose terms carry the invariant of `P.g` carries it to the packed outputs); `_group_ne`, `_tagStd_ne`, `_tagT1_ne`, `_mem_pq` are copies of the private helpers (`BAShapeO2B:51-69, 213-217`) under the stem.
5. Section 2 (target 1 (b)): route (β), term level at the transfer graph `tr`. `BALocReg2B_trA` and `_trB` are one `localReg2_VRepl.same` each (they take the hypotheses of the check shapes; the proof of `_trB` does not use `hsame`, `hwf1`, `hwf2`, see the linter lines);
   `BALocReg2B_macroA`, `_macroB` compose them with the lists of `Graph/BALocReg2` at `Γ := tr` (`BALocReg2_lw2/lw4/gg2/gg4`), with `tr` normal and the pair a member of `lwSplit tr.solid` from the public `BAShapeO2B_ext_normal`, `_lwSplit_last`, `_fresh_wf`. Route (α) is not used.
6. Section 3 (targets 1 (c), (d)): the three `_tn` proofs are the case analyses of `baShapeLL_e2_tn`, `_macroA_tn`, `_macroB_tn` (`BAShapeO2B:221-342`) with the cost lemmas replaced by the path lists of `Graph/BALocReg2` (same binders) and `BAShapeO2B_group` by `BALocReg2B_group`. No hypothesis is added;
   no public theorem has a shape binder. `baPathBinder_holds` is the three `_tn` as the binder `hX` of `baPathStep_holds`, `baLocReg15_holds`.
7. Sections 4, 5 (targets 2, 3): `baPathStep_closed`, `baLocReg15_closed` are `baPathStep_holds`, `baLocReg15_holds` at `baPathBinder_holds`; `baShapeLLBinder_holds` is the discharge of the T2448 binder with the three `baShapeLL_*_tn` (the content of `baLocReg6_holds`, `BAShapeO2B:356-359`).
   `baLocRegConcl_upto5`: conjunct (c) of `BALocRegConcl` gives `P0` and `BAReach`, `baLocReg15_closed` the clauses at every `Q ∈ outs ++ errs`, conjunct (a) gives `Q.g.LocStd` for `Q ∈ outs`. `ba_localregular_upto5` is `ba_localregularX baShapeLLBinder_holds` plus it.
8. Instances (section 6): the kernel cannot evaluate the packed outputs at a start term (`BAGraph.partition` is noncomputable and the outputs live over quotient types), so (v) uses a good renaming of the concrete `D0 = BALocReg1B_D0` (`BALocReg1B_merge_map`, `_lanlwD_map`, `_sameAtom_map` of `BALocReg1B`):
   `BALocReg2B_extraB_map` shows the tag `e2` of the renamed output is read on `D0`, `BALocReg2B_weight_out_e2` builds the tagged step and the output, `BALocReg2B_start_weight_e2` finds an extra `M`-split `T` of `lanlwD D0 p1 q` by `decide +kernel`; then `baShapePath_e2_tn` and `baPathInit_holds 2`. (v′) is the same at the hand-built `baPL`.
9. Instances (vi): target 2 at the graph of `BALocReg1B_reach_locStd` (two weight steps from a `p = 2` start term, no start term is `LocStd`), with no hypothesis. (vii) is the instance of `BAEngineInst:483` without `hX`, through `ba_localregular_upto5`.
10. Limits of the instances: in 3 (b), (c) the lists `outs`, `errs` are the existential data of the engine (`ba_localregularX`), as in the merged `BAEngineInst:483`; the instance does not show `outs ++ errs ≠ []`. The invariant `PathInv2` of the parent is satisfied, not assumed, at every witness. The preflight numerics (a) row 7 were not rerun.
11. No port from `../RBM1D`, `../RBM2D`: the proofs adapt the merged RBM3D files `Graph/BAShapeO2B.lean` (00f4a104) and `Graph/BALocReg2.lean` (ff8a75b9); the only `RBM1D`/`RBM2D` text in the new file is the "no port" line in the header docstring (grep above). The paper statements used: `B_graphical_lemmas.tex:393-405`, `:416`.
## (c) Verified Mathlib names used
Every name below elaborates under `#check @name` in `scratchpad/T2469b/mlnames.lean` (31 names, 0 errors, see (b)); names verified absent: none (no name was tried and dropped).
- `Function`: `comp_apply`
- `List`: `any_map`, `append_assoc`, `exists_mem_of_ne_nil`, `getElem_mem`, `map_cons`, `map_nil`, `mem_append`, `mem_append_left`, `mem_append_right`, `mem_cons`, `mem_cons_of_mem`, `mem_cons_self`, `mem_flatMap`, `mem_map`, `mem_of_getElem?`, `mem_of_mem_eraseIdx`, `mem_singleton`, `not_mem_nil`
- `Multiset`: `coe_nil`, `cons_coe`, `insert_eq_cons`, `map_add`, `map_cons`, `map_singleton`, `map_zero`, `mem_singleton`, `singleton_add`
- `Prod`: `map_apply`; `Sym2`: `map_mk`, `mk_isDiag_iff`
## (d) Open issues and paper-delta candidates
No open issue blocks L3b2b. Consumers named by `docs/tickets/T2469.md`: target 2 `baLocReg15_closed` and target 3 (b) `baLocRegConcl_upto5` for L3d2 (T2470), L5; `ba_localregular_upto5` for L3d4, L5, L6; `baPathBinder_holds` discharges `T2469_PathBinder` for any consumer that carries `hX` (O2R-C3).
The unused hypotheses of `BALocReg2B_trB` (`hsame`, `hwf1`, `hwf2`) are kept to fit the check shape; `BALocReg2B_macroB` uses them only to call it.
- `T2469d` (paper `B_graphical_lemmas.tex:393-405`, `GGGamma` at the transferred pair, and `:416`): the paper has no path argument for the stage-2 transfer graphs. Lean proves it per stage: `Γ → tr` is one replacement of molecular edges (`trA`: the edge inside an atom becomes the blue loop `Ǧ_{ββ}`; `trB`: the pair
  `(a, y)`, `(y', a')` becomes `(β, y)`, `(y', β)` with `β` in the molecule of `a`, the molecular edges unchanged), then the weight and `GGGamma` terms at `tr` (route (β)).
- `T2469e` (statement difference to the band `lw_localregular_upto5`, `LocalRegular2:1857`): the band states `LocReg1 ∧ LocReg2 p ∧ LocReg345 p` for `outs` only; the BA statement gives `PathInv2 p`, `n_M ≤ p` and `LocReg2` on the image at every graph of `outs ++ errs`, `LocReg1`, `LocReg345` on the image and `LocReg345` on the shadow
  for `outs` (the errors carry no `LocStd`), as in the contract `BALocReg15` (`BALocReg1B:251-259`; `n_M ≤ p` is stated on `Q.g` and inside `LocReg2` on the image, `(eq:MolVW)` counts atoms: `T2397c`).
