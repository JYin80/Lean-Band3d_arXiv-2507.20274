Auditor model: claude-opus-5-5

# T2493b (U5d-2, `BA/Step5IIIWalk2.lean`, targets 6-8) -- audit round 1 -- Tue Oct 13 09:38:30 UTC 2026

Branch `t/T2493b` @ 4f21ab26; main @ c72bc745 (= merge-base). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2493b-audit1` (detached).

## 1. Diff scope

```
$ git diff --stat main...t/T2493b
 RBM3D.lean                  |    1 +
 RBM3D/BA/Step5IIIWalk2.lean | 1067 +++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean      |    1 +
$ git diff main...t/T2493b -- RBM3D.lean        (after the last import line, before #assert_rbm_axioms)
 import RBM3D.Chain.NQEndFlowGen
+import RBM3D.BA.Step5IIIWalk2
$ git diff main...t/T2493b -- RBM3D/Test/Axioms.lean   (owedProps, one line)
+    `RBM.BA.STDecayStronggL, -- `(Eq:Gdecay+s<g)` at the start time `s` over a carrier (`Chain/Carrier.lean:105`), the loop-level
     induction hypothesis at `s`: premise of `baStep5III_walk_at` (T2493 U5d-2, ...); ... owner the BA main induction (V) (DECISIONS §297 (5), CONTROL H278 (3))
$ git diff main...HEAD -- RBM3D/BA/Step5IIIWalk.lean | wc -l      (file 1, merged, untouched)
0
$ grep -rln "import RBM3D.BA.Step5IIIWalk2" RBM3D RBM3D.lean ; wc -l RBM3D/BA/Step5IIIWalk2.lean
RBM3D.lean          1067 (stop line 2000; Step5IIIWalk3 not created)
```
All three files are sole writable files (ticket "Sole writable files"; `Test/Axioms.lean` under answer (6) + CONTROL H278 (3), which approves exactly this `STDecayStronggL` line). No merged file edited; no frozen signature touched.
## 2. Statements against the pins (script diff)

`stmtdiff.py`: extracts each `T2493_*` def body from `docs/tickets/checks/T2493-check.lean` and the declaration from the file, normalizes whitespace,
renames `T2493_BAWalkConcl/BAWalk/BAFromWalk` to the file's names, inlines `T2493_ReadPremises` into `T2493_WalkAt`, cuts the theorem at ` := by`.
```
$ python3 -I stmtdiff.py
T2493_BAWalkConcl vs BAStep5IIIWalkConcl: IDENTICAL [594/594 chars]
T2493_BAWalk vs BAStep5IIIWalk: IDENTICAL [205/205 chars]
T2493_BAFromWalk vs BAStep5IIIFromWalk: IDENTICAL [320/320 chars]
T2493_WalkAt vs baStep5III_walk_at: IDENTICAL [565/565 chars]
```
`baStep5IIIWalk_holds : BAStep5IIIWalk`, `baStep5IIIFromWalk_holds : BAStep5IIIFromWalk` (types are the pinned defs). Against the probe `T2459_BAfromWalk`
the only difference is correction (a) (`0 < ε → 0 < 𝔡`), confirmed by dispatcher answer (5) and already in the pin.

Auditor's examples (acceptance criterion "the auditor adds `example : T2493_BAWalk := baStep5IIIWalk_holds` ..."): a copy of the check file with
`import RBM3D.BA.Step5IIIWalk2` added, then
```
example : T2493_WalkAt := baStep5III_walk_at
example : T2493_BAWalk := baStep5IIIWalk_holds
example : T2493_BAFromWalk := baStep5IIIFromWalk_holds
-- plus `Iff.rfl` for the three defs against their pins
example : STPfStep5gL 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 := by ...  -- U5e shape, check :320
$ lake env lean AuditT2493b.lean > audit_ex.log 2>&1; echo "exit $?"; grep -c error audit_ex.log
exit 0
0
```
Quantifier order (read off the pinned text): fixed `κ ε 𝔡 Cd` and positivity before `𝔠 sz z`, flow, `s t`, horizon, regime, read premises; inside
`BAStep5IIIWalkConcl`: `∃ ε₁ ∀ ε₀ < ε₁ ∀ D ∃ D* ≥ D + 2d ∀ tt ∀ D' ∃ K (K n ≠ 0) ∀ᶠ n`, probability bound `N^{-D'}` (band shape `PfStep5_walkConcl`).
The read set of `baStep5III_walk_at` is exactly `T2493_ReadPremises` (5 premises; none added). In `baStep5IIIWalk_holds` (l.763-770) the nine
carrier binders are introduced and only `hDecS, hStep2.2.1, hStep2.2.2, hLmax, hLKU` are passed; `𝔠d = 1/100`, as pinned (`le_rfl` for `≤ 1/100`).
## 3. Vacuity, hidden hypotheses, cycles

`grep -n "structure\|^private def\|^def\|^theorem\|^private theorem"`: public 63/73/79 (defs), 582/763/977 (theorems); private structure 90,
private theorems 116/365/782/866/1027, private defs 997/1005 (instance bundles).
- The private structure `Step5IIIWalk2_Num` is a numerics bundle built inside the proof of `baStep5III_walk_at` (anonymous constructor from
  `filter_upwards` outputs); it appears in no public statement. Public statements use only merged names (`STIngR5gL` `Chain/Step5Gen:191`,
  `BAFlow`, `BAStep5IIIJsharp`, `STPfConclgL`, ...) plus the three pinned defs.
- No new external hypothesis. The premises are the binders of the merged `STIngR5gL` shape (UBA-C3) and, for target 7, target 6's conclusion.
  `STDecayStronggL` at `s` is the loop-level induction hypothesis (dispatcher answer (1)); registered as owed (H278 (3)).
- No cycle: imports `BA/Step5IIIWalk` (merged f2af0245), `BA/NetLiftBA`, `Induction/Step1Setup`, all on main; `open private` only from merged files
  (`Induction/PfStep5`, `BA/GridMartBA`, `BA/NetLiftBA`, `Path/NetLift2`); no `open private` of file 1.
## 4. Compiled nonempty instances (target 8)

File section 7 (l.987-1065), all compiled in the module build. Data: `d = 3`, `SizesInst.sz0`, `FlowPinsInst.zSeq`,
`flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq` (`BA/FlowPins:1214`), `s ≡ 1/10 < t ≡ 1/2`, `t ≤ t₀` by `half_lt_t0` (`FlowPins:1254`),
regime `Step5IIIGood_reg_sz0 : STReg5III sz0 (1/10) (1/2)` (`BA/Step5IIIGood:623`), `Cd = 1`, `(con_st_ind)` by
`s1Setup_conStInd_const (s0 := 1/10) (t0 := 1/2) _ _ h0` (`Induction/Step1Setup:1226`).
- l.1018 `example (hread : Step5IIIWalk2_instRead) : BAStep5IIIWalkConcl sz0 ... (1/10) (1/2) := baStep5III_walk_at (1/2) (1/10) (1/10) 1 ...`
  -- every deterministic premise discharged (`norm_num`, `one_pos`, `flow_sz0`, `half_lt_t0`, `Step5IIIGood_reg_sz0`); the five read premises stay.
- l.1027/1036 `baStep5IIIWalk_holds le_rfl (1/2) (1/10) (1/10) ... 1 one_pos`, applied at the same data; `STConStInd` discharged; the nine carrier
  predicates of Steps 1-4 (`Step5IIIWalk2_instPrem`) stay hypotheses.
- l.1042 `baStep5IIIFromWalk_holds` at the same data with `0 < κ, 0 < ε, 0 < 𝔡` by `norm_num`; hypothesis: the grid conclusion (target 6's output).
- l.1050 the chain walk -> lift: `STPfConclgL sz0 ... (1/10) (1/2)` from `Step5IIIWalk2_instPrem` only.
- l.1058 U5e's reading `STPfStep5gL 3 ... baFMz BAflowT0` from the two `_holds` (no hypothesis).
Remaining hypotheses are exactly those the ticket's target 8 (c) allows (Steps 1-4 carrier predicates; other gates' pins). Data nondegenerate
(`s < t` strict, `t < t₀ < 1`, `W, L` growing along `sz0`), no `False` premise, no empty index.
## 5. Build and axioms

```
$ lake build RBM3D.BA.Step5IIIWalk2           (audit worktree)
✔ [4106/4106] Built RBM3D.BA.Step5IIIWalk2 (11s)
Build completed successfully (4106 jobs).
EXIT 0
$ lake build                                   (full library, registry pre-check)
info: RBM3D.lean:602:0: axiom audit: 14876 theorems, 4612 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 126 (borrowed 1, owed 59, structural 46, refuted 6, superseded 14).
Build completed successfully (4370 jobs).
EXIT 0
$ (#print axioms in AuditT2493b.lean)
'RBM.BA.BAStep5IIIWalkConcl' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5III_walk_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAStep5IIIWalk' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5IIIWalk_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAStep5IIIFromWalk' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5IIIFromWalk_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE '\bsorry\b|\badmit\b|^axiom|native_decide' RBM3D/BA/Step5IIIWalk2.lean
(no output)
```
## 6. Ticket greps (new file)

```
$ grep -nE 'BAK_le_small|BAMB_upper_small|BAGbEXP|Mbound_AO|W\^\(-eps|BAm_im_lower_window|STLocalEntryUgL|STDecaygL\b'
1009:    STDecaygL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) ∧
$ grep -nE 'STGridRepNgL|\|E\||norm_mE|mSigma|SB d|E2Hyp|gexRHS|STGMMg|≤ A \*'
(no output)
$ grep -n withLam | grep -vE 'seqP \((sz|SizesInst.sz0)\.withLam 0\)|pathP \(...\)'
864:`contGood (sz.withLam 0)`, as `NetLiftBA_decay`): ...      (docstring)
942:    (cont_highProbAt_good (sz.withLam 0) hsizeN)
$ grep -n -A1 "theorem cont_highProbAt_good" RBM3D/Induction/ContinuityNet.lean ; grep -c "cont_highProbAt_good (sz.withLam 0)" RBM3D/BA/NetLiftBA.lean
369:theorem cont_highProbAt_good {d : ℕ} (sz : Sizes d) (hsize : Tendsto sz.size atTop atTop) :
370-    HighProbAt sz.seqP sz.size (contGood sz) := by
3
$ grep -nE '(def|abbrev|structure) (BAStep5IIIEScalar|BAStep5IIIEMatrix|BAStep5IIIJsharp|BAStep5IIIGood|STLmaxUgL|STLKUgL|STGridRepNAtgL)\b'
(no output)
```
Labels: l.1009 is the carried `STDecaygL` binder of `STIngR5gL` inside the instance bundle `Step5IIIWalk2_instPrem` (a hypothesis, never read;
the proof of `baStep5IIIWalk_holds` drops `hDec`). l.942 is a proof term whose type is `HighProbAt (sz.withLam 0).seqP ...`, i.e. the law
`seqP (sz.withLam 0)`; same use as merged `NetLiftBA`. No statement hit.
## 7. Paper deltas

- Targets 6-7 split `lem:pf_step5` at BA into the grid walk and the lift (band shape `PfStep5_walkConcl` / `pfStep5_PT_of_walk`); their
  composition is U5e's `STPfStep5gL 3` (compiled, §4 l.1058). The BA proof the paper omits (`7_8:2101`) is candidate T2459a, listed as pending
  in `docs/paper-deltas.md:1598` ("numbered at row merge"); the `J`-free `dif` factor is T2459f (`T2459-design.md:268`).
- Correction (a) (`0 < ε`, `0 < 𝔡`) is a probe-vs-pin difference; the paper assumes both (`STIngR5gL` already carries them). Not a paper delta.
- No other Lean/paper statement difference found in targets 6-7. Coverage complete.
## 8. Observations (no verdict effect)

- O1. The added `owedProps` comment differs from the H278 (3) text: it names `baStep5III_walk_at` (the real declaration) instead of
  `baStep5IIIWalk_at`, and adds "U5d-2, `BA/Step5IIIWalk2.lean`" and "CONTROL H278 (3)". Comment only; the registered name `RBM.BA.STDecayStronggL`
  is the approved one. The need for the line is taken from the prove report's quoted first-build error; not re-run (no source edit in audit).
- O2. `BAStep5IIIGood` (the other H278 (3) line) was not added; the full build passes without it (§5).
- O3. T2459a is still unnumbered; the dispatcher numbers it at this row's merge (per `paper-deltas.md:1598`).
## Verdict

| target | statement | hidden/vacuity/cycle | instance | build/axioms | deltas | verdict |
|---|---|---|---|---|---|---|
| 6 (a) `BAStep5IIIWalkConcl` | identical to pin | none | used in all §4 instances | pass | T2459a | PASS |
| 6 (b) `baStep5III_walk_at` | identical to pin (ReadPremises inlined) | none | l.1018 | pass | T2459a | PASS |
| 6 (c) `baStep5IIIWalk_holds` | `: BAStep5IIIWalk` = pin | none | l.1027-1040 | pass | T2459a | PASS |
| 7 `baStep5IIIFromWalk_holds` | `: BAStep5IIIFromWalk` = pin (corr. (a)) | none | l.1042, l.1050 | pass | -- | PASS |

**T2493b: PASS.** No dispatcher sign-off needed.
