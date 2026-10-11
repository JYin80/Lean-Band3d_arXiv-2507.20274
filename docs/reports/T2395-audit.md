Auditor model: claude-opus-5-5

# T2395 audit (round 2, after repair `4c1de4c`): BA-L3a3 design gate (G1 + S test). Verdict: **PASS**

Written Sun Oct 11 00:34:00 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2395-audit2`, detached at `t/T2395` = `4c1de4c`; `main` = `c2d7eb5`.
Scratch checks `a2.lean`, `a3.lean` are in the auditor scratchpad `T2395/` (not in the repository). Round-1 items PASS there (S1, G1, C1/L5, row table, deltas) were re-read only where the repair touched them.

## 1. Build, hygiene, scope (CLAUDE.md §5.3-5.4; stop rule 400 / 300)

```
$ lake build RBM3D.Probe.T2395Pins
✔ [3793/3793] Built RBM3D.Probe.T2395Pins (116s)
Build completed successfully (3793 jobs).
exit 0        (error lines: 0; warnings in T2395Pins.lean: none)
$ git diff --stat main...HEAD
 RBM3D/Probe/T2395Pins.lean   | 396 +++++++++++++++++++++++++++++++++++++++++++
 docs/reports/T2395-design.md | 173 +++++++++++++++++++
$ wc -l RBM3D/Probe/T2395Pins.lean docs/reports/T2395-design.md
     396 RBM3D/Probe/T2395Pins.lean
     173 docs/reports/T2395-design.md
$ grep -nE 'sorry|admit|native_decide|^axiom' RBM3D/Probe/T2395Pins.lean | wc -l
       0
$ lake env lean a2.lean   (#print axioms)
'RBM.Graph.ba_lvl1StepGood_of_sim' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.T2395Inst.ggFrame' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.T2395Inst.ggStep' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.ba_good_of_lit' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.ba_twist_counters' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAGraph.twist_atomAdj' depends on axioms: [propext, Classical.choice, Quot.sound]
$ git grep -nE '(def|theorem|abbrev|lemma) +<n>( |$)' main -- 'RBM3D/*.lean' | wc -l      (new public names of the repair)
BAstepMono 0   BAtwistInv 0   ba_lvl1StepGood_of_sim 0   ggFrame 0
```
(The five evidence theorems `ba_gg2_first` .. `ba_withinMacro` are unchanged since round 1, where their axioms were standard.) The design report on the branch equals the main-worktree copy (`diff` empty). PASS.

## 2. Round-1 defects

### D1 (the transport as a proved reduction): repaired
The repair adds only declarations; no earlier pin changed:
```
$ git diff f0b651f 4c1de4c -- RBM3D/Probe/T2395Pins.lean | grep '^-' (declarations)
-theorem ggStep ...  (re-stated through ggFrame, same type)
$ added: def BAstepMono (269), def BAtwistInv (272), private good_congr (301), private lit_of_band (311),
         theorem ba_lvl1StepGood_of_sim (323), theorem ggFrame (369), 4 examples (375-379)
```
Statement (probe 323, extracted):
```
theorem ba_lvl1StepGood_of_sim {m : ℂ} (hi : BAimg) (hs : BAsim m) (hm : BAstepMono) (ht : BAtwistInv) : BAlvl1StepGood
```
- Conclusion is the round-1 pin `BAlvl1StepGood` (259, unchanged): every output of a `BALocStep` at a normal `P` is normal and `BALvl1Good P.g Q.g`.
- Hypotheses: four Prop pins with every quantifier in the signature (no structure field). `BAstepMono` = required item 1 verbatim (normal, `ord ≤`, `n_M ≤`, `n_A - n_W ≤`, `nExt ≤`, for every `BAFrameStep` output). `BAtwistInv` = the twist invariance of `Normal`, `nExt`, loops, pairs asked in item 2; the counters come from the proved `ba_twist_counters`.
- The band theorem is used through the image as the ticket asks: the first disjunct of `BAsim` calls the merged `lvl1_step_good` (`LWLvl1.lean:3290`) at `(P.twist c t).img`, with normality from `BAimg`, read back by `lit_of_band`, and `nExt` is added by `ba_good_of_lit`. Disjuncts 2/3 use `BAstepMono` only.
- No cycle: the proof uses the four pins, `ba_twist_counters`, `ba_good_of_lit` and merged `lvl1_step_good`; the probe imports merged modules only.
- Row ownership is in design §4/§6: `BAstepMono` and the reduction go to L3a4, `BAtwistInv` to L3a1, `BAimg` to R0, `BAsim` to R1.

### D2 (instances): repaired
Every pin now has a compiled application (probe 372-394, build above):
```
372 BAlvl1StepGood @ ggStep      373 BAlvl1ExistsStep @ baGGLhs   374 BAlvl1Lemma 3 @ (K=10, baGGLhs)
375 BAsim Complex.I @ ggFrame    376 BAstepMono @ ggFrame         377 BAtwistInv @ (true,true,baGGLhs)
378 ba_lvl1StepGood_of_sim @ ggStep (all four pins as hypotheses)
386 BAlvl1StepIdentity 3, 389 BAtwistIntegral 3, 391 BAexpFrameE 3 @ BA flow datum sz0 (BASelf by BAflow_real, 0 ≤ 1/2 < 1 by norm_num)
394 BAimg @ baGGLhs
```
Deterministic hypotheses (normality, the step constructor) are discharged by `decide`/`rfl`. The pins remain hypotheses because they are other rows' statements. **Non-vacuity at the instance** (auditor check): the conclusion of each pin used by the reduction example is true at that data, so the hypotheses of the example hold jointly there. `ggF` is the `packMerge` of `splitG`; `packMerge` is classical, so the check runs on `splitG`, and (F) shows that `splitG` has no `=`-dotted edge to merge.
```
$ lake env lean a3.lean      (exit 0, no error lines; 1:02 wall)
(A) ∀ T ∈ gg2/gg4 ggP ggQ, ∀ Q ∈ T.splitG, Q.Normal ∧ ord ≤ ∧ nM ≤ ∧ nA-nW ≤ ∧ nExt ≤   [BAstepMono concl.]   decide +kernel ✔
(B) ∀ ..., ord baGGLhs < ord Q ∨ Q.nExt < baGGLhs.nExt                                 [BAsim, disj. 2/3]    decide +kernel ✔
(C) ∀ c t, (Normal → twist Normal) ∧ nExt, nLoops, nPairs kept at baGGLhs               [BAtwistInv concl.]   decide +kernel ✔
(D) ∀ ..., (Q.twist false false).Normal ∧ BALvl1Good baGGLhs (Q.twist false false)      [BAlvl1StepGood]      decide +kernel ✔
(F) ∀ ..., ∀ e ∈ Q.dotted, e.eq = false                                                 [packMerge trivial]   decide +kernel ✔
#eval number of outputs of the step: 15
#eval (ord, nExt, nS, LocStd, Normal) of baGGLhs: (0, 2, 2, false, true)
```
The instance is nondegenerate: 15 outputs; the parent is normal, not locally standard, and has 2 external atoms and 2 solid edges. The previous claims are corrected: prove (b) line 178 notes that `BAsim` had no instance at `f0b651f`, and design §0/§4 now list all 10 pins and the reduction with probe lines. I verified the line numbers against the file.

### Items 4, 5
- Design §2 ("Lean form of the transport") states the reduction and its inputs. §3 Step 3 links Lemma S (a), (c) to `BAstepMono`.
- §6 re-prices L3a1 (+60/+80/+150) and L3a4 (+40), and the totals are 5,900 / 7,230 / 12,530.
- The probe has 396 lines (limit 400). PASS.

## 3. Statements of the other pins (unchanged since round 1)
The diff in §2 shows no change to `BAimg`, `BAsim`, `BAlvl1StepGood`, `BAlvl1ExistsStep`, `BAlvl1Lemma`, `BAlvl1StepIdentity`, `BAtwistIntegral`, `BAexpFrameE`, `BAFrameStep`, `BALocStep`, `BALvl1Good`, `LocStd`. My round-1 comparison with `lvl1_lemma` (`LWLvl1.lean:3903`), `lanlw_val` (`BAExpandW.lean:908`), `(eq:LW)` (`B:376-385`) and `GGGamma` with D402 (`B:393-405`) still holds.

Plausibility of `BAimg` (R0), from merged definitions (no proof here):
- `LGraph.adj` (`LWVocab.lean:157`) joins only waved and `=`-dotted edges. The image's new `×`-dots therefore do not merge molecules, and the image `n_M` is consistent with `BAGraph.nM` (`BAVocab.lean:150`).
- `LGraph.Normal` (`LWVocab.lean:990`) (ii) `XBetween ↔ SBetween` matches the image's `×`-dot on every non-loop solid edge (probe 225).

## 4. Vacuity, hidden hypotheses, C1, deltas
- **Vacuity and hidden hypotheses.** All pins are `Prop` definitions with explicit binders. `BAPGraph` has only instance and surjectivity fields. §2 shows the pins jointly satisfiable at the concrete step.
- **C1/L5.** The repair adds no constant, decay, `ρ` or smallness. Design §5 (`c1.py`, `g = 1/64, 1, 10`) is unchanged: PASS.
- **Paper deltas.** The new candidate `T2395f` (`B:407-416`) covers the two BA-specific statements of the repair (`nExt` monotonicity, twist invariance of the atom structure). `T2395a`-`e` cover K1-K4, the order-keeping first sum and `Lvl1Ident`. Coverage: PASS.

## 5. Observations (no RETURN)
- O1 (round 1, open). Lemma E is checked exhaustively by `table.py` for `D_q`, `T1/3a`, `3b`, `S1`. The `(M⁺S⁺)` parts and `GGGamma` sum 3 with `W - 1` are argued "same structure" (design §7 Limits (1)), while §0 says "no mathematical step is missing". This is for R1/L3a4 to close.
- O2. The reduction covers `lvl1_step_good` only. No pin derives `BAlvl1Lemma` from `BAlvl1StepGood` + `BAlvl1ExistsStep` + `BAlvl1StepIdentity`; that induction is row L3a5's own work (design §3 Step 4: measure with `nExt`, `lvl1Lt_wf` with one more component). `Lvl1Ident` is BA-specific by K4/F5. The ticket's "lvl1_lemma / Lvl1Ident / lvl1_step_good through the map" is therefore met for step-good; the other two are BA-specific, as the decision S′ states.
- O3. Design header (line 5) lists probe commits up to `3fd0e51`, but the tip `4c1de4c` also changes the probe. This is text only.
- O4. `BAimg` is not evaluated at a concrete graph (classical `mergeP`). R0 must prove it.
- O5 (round 1 O2, unchanged). Sibling numbering on `main` (G2 = T2397, LW-14 = T2398) differs from the ticket. The report follows main.

## 6. Verdict per target

| target | verdict |
|---|---|
| S1 (atomic correspondence, test) | PASS |
| S2 (decision S′, Lean form = proved reduction `ba_lvl1StepGood_of_sim`) | PASS (D1 repaired) |
| G1 (BA `lvl1` reduction, paper level) | PASS with O1 |
| pins L3a1-L3a5, R0, R1 (10 pins + reduction, each with a compiled instance) | PASS (D2 repaired) |
| C1 / L5, row table, paper deltas | PASS |
| build, axioms, hygiene, scope, stop rule | PASS |

Overall: **PASS** (report-only merge of `docs/reports/T2395-design.md`; the probe stays on `t/T2395`). Needs dispatcher sign-off: no (the ticket itself routes the outcome to the L4 REQ).
