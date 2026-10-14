Auditor model: claude-opus-5-5

# T2500 audit (round 1) — U1-BA, `RBM3D/BA/ZeroModeBA.lean` — Wed Oct 14 03:03:16 UTC 2026

Branch `t/T2500` at fc90ad3a; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2500-audit1` (detached).

## 1. Diff scope

```
$ git diff --stat main...t/T2500
 RBM3D.lean               |   1 +
 RBM3D/BA/ZeroModeBA.lean | 409 +++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean   |   2 +-
$ git diff --stat main...t/T2500 -- RBM3D/Chain RBM3D/Induction RBM3D/BA/SEforLnBA.lean RBM3D/BA/B45BA.lean RBM3D/BA/GridRepTailBA.lean RBM3D/BA/TwistStep2.lean | wc -l
       0
$ git diff main...t/T2500 -- RBM3D.lean
+import RBM3D.BA.ZeroModeBA            (after `import RBM3D.BA.Step5IIITargets`, before `#assert_rbm_axioms`)
$ git diff main...t/T2500 -- RBM3D/Test/Axioms.lean   (STIterR' owner text only)
-   ... generic: `stIterationsgL'_of`, `stIterationsIIgL'_of` (T2497, `Chain/IterationsGen2`); BA: U1-BA
+   ... generic: `stIterationsgL'_of`, `stIterationsIIgL'_of` (T2497, `Chain/IterationsGen2`); BA: `baSTIterationsgL'_holds`, `baSTIterationsIIgL'_holds` (T2500, `BA/ZeroModeBA`)
```
Only the three sole writable files; no `owedProps` line added or deleted (ticket registry (ii)). Importers of the new module: `RBM3D.lean` only.

## 2. Statements against the pins (script)

Scratch file = `docs/tickets/checks/T2500-check.lean` + `import RBM3D.BA.ZeroModeBA` + the lines below inserted before `end RBM.BA`
(uncommitted, deleted after the run), compiled in the audit worktree:
```
example : T2500_NewPQWardCls := stNewPQgL_wardCls
example : T2500_NewPQBA := baSTNewPQgL
example : T2500_ZeroModeSetUNBA := baZeroModeSet_UN
example : T2500_ZeroModeSetThetaNBA := baZeroModeSet_ThetaN
example : T2500_USemigroupBA := baStep2Gen_USemigroup
example : T2500_IterFamBA := baIterationsGen2_fam
example : T2500_IterationsBA := baSTIterationsgL'_holds
example : T2500_IterationsIIBA := baSTIterationsIIgL'_holds
$ lake env lean T2500_audit_scratch.lean ; echo EXIT
EXIT 0        (no error line; the whole check file, Part 1 #checks and shapes, also elaborates on the branch)
```
All eight pins are matched by plain term ascription (definitional equality, no unfolding lemma, no extra premise). In particular target 6
is stated at `baFMz sz z` (the pin's carrier), and `stIterationsgL'_of … (baStep2Mat …)` is accepted at it by defeq (stop rule not triggered).
Every statement is `∀ d` (decision (10)); the R2* pins keep `3 ≤ d`, `∃ 𝔠d ≤ 1/100` before `(𝔠, sz, z)` (merged text
`Chain/NQEndFlowGen.lean:123-137`, read).

## 3. Hidden hypotheses, vacuity, cycles

```
$ F=RBM3D/BA/ZeroModeBA.lean
C1   grep -nE 'BAK_le_small|BAMB_upper_small|BAGbEXP|Mbound_AO|\|E\||norm_mE|mSigma|SB d|E2Hyp|STGridRepNgL|etaT|lemT' $F | wc -l  ->  0
X1-C4 grep -nE '^(noncomputable )?(def|abbrev|structure) ' $F | wc -l                                                         ->  0
private defs: 159 σ3, 242 szI, 249 wI, 250 mI, 251 zI   (instance data only)
local copies of STNewPQgL|ZeroModeGen_WardCls|ZeroModeGen_KerSums|Step2Gen_USemigroup|IterationsGen2_Fam|STIterRgL'|STIterationsgL'|STXiBootgL' or T2463_|T2497_ -> 0
UBA  grep -n withLam $F | grep -v 'seqP (' -> (none);  grep -nE 'gK|≤ A \*' $F | wc -l -> 0
hygiene grep -nE '\bsorry\b|\badmit\b|^axiom|native_decide' $F | wc -l -> 0
$ wc -l $F  ->  409   (central 320, stop line 640)
```
No new structure, so no field-hidden hypothesis. Public premises of targets 1-6 are only `d`, the flow `0 < κ`, `BAFlow …` and the
pin's own binders. Dependencies (all on `main`): `zeroModeGen_newPQ`, `zeroModeSet_UNg`, `zeroModeSet_ThetaNg` (T2463),
`baZeroModeGen_wardCls`, `baZeroModeGen_kerSums`, `baStep2Mat_loopForm`, `baStep34_LCompat` (T2486), `gridRepTailGen_ker_BA` (T2471),
`Step2EventsGenTw_baFlow` (T2467), `Step2Kern_UN_BA`, `BAflow_real`, `BAm_norm_le_one`, `EMn2BA_seqHflowBA_herm`,
`stIterationsgL'_of`, `stIterationsIIgL'_of` (T2497). The new module is a leaf (no importer except the root): no cycle.
No external hypothesis is introduced. The private `ZeroModeBA_coef` is a copy of the private `ZeroModeGen_coef` (ticket allows).

Name clashes (`git grep "theorem <name>"` on main, t/T2498, t/T2501, t/T2501a2, excluding ZeroModeBA): 0 rows for all eight target
names and for namespace `RBM.BA.ZeroModeBAInst`.

## 4. Compiled nonempty instances (d = 3)

| target | instance (file:line) | data | deterministic premises discharged |
|---|---|---|---|
| 1 | `example` :183 | `sz0`, `baFMz sz0 zSeq`, m = 3, σ = (+,−,+), A = ∅, n = 0, τ = 1/2 | class via `baZeroModeGen_wardCls … flow_sz0`, `0<τ`, `τ<1` |
| 2 | `inst_newPQ_ba` :166 | same; `∅ ∪ STIdiff σ3 ≠ ∅` proved (:161, `decide +kernel`) | flow `flow_sz0`, `0 < 1/2`, τ bounds |
| 3 UN | `example` :190 | A = {0}, s = 1/10, t = 1/2, T ≡ 1 | `0 < κ`, `flow_sz0` |
| 3 ThetaN | `example` :199 | A = {0}, t = 1/2, T ≡ 1 | `0 < κ`, `flow_sz0` |
| 4 | `inst_usemigroup` :205 | every n | `0 < κ`, `flow_sz0` |
| 7(c) | `example`s :215, :222 | `baStep2Mat sz0 …`, n = 0, s ≡ 1/10 ≤ t ≡ 1/2, K = 4 | carrier premises from 4 and `baZeroModeGen_kerSums` (:209), window by `norm_num` |
| 5, 6(i) | `inst_iterationsgL'` :364 | new datum `szI` (L ≡ 4, W_n = n+25, λ ≡ 2), `(κ,ε,𝔠,𝔡) = (3/1000,1/2,1/9,1/10)`, s ≡ 0 < t ≡ 1/400 | `3 ≤ 3`, κ, ε, 𝔡 > 0, flow `flowI.1` (proved :254-335), `0 ≤ s`, `s < t`, `t ≤ T₀` (:344), `STRegIterI` (:347: 4/16 ≤ 399/400, 1 ≤ 4), `STConStInd` (`conStInd_const`) |
| 5, 6(ii) | `inst_iterationsIIgL'` :386 | `TwistStep2_szII` (L ≡ 4, λ ≡ 5), `(3/5000,1/2,1/9,1/10)`, s ≡ 0 < t ≡ 1/2000 | flow + window `TwistStep2_flowII`, `STCaseII` (:357: 1 ≤ 25/16), `STConStInd` |

Kept as hypotheses in the target-6 instances: `STKboundgL`, `STLKgL`, `STStep1LoopgL`, `STStep2ConclgL`, `STXiBootgL'` and the two
induction hypotheses (other gates' pins, ticket 7(d)); `Cd > 0` is a universally quantified constant of the pin. Target 5 has no
premise beyond `d` and is applied at d = 3 inside both target-6 instances. No `N = 0`, empty index, collapsed window (s < t at every n),
`False` premise or astronomically large witness (κ = 3/1000, `size n = ((n+25)·4)^3`).

## 5. Build and axioms (audit worktree)

```
$ lake build RBM3D.BA.ZeroModeBA      -> Built RBM3D.BA.ZeroModeBA (5.6s) ... Build completed successfully (4128 jobs).  EXIT 0
   error lines: 0; warnings in ZeroModeBA: longLine (:19-30), `show` linter (:291-359) only
$ lake build RBM3D                    -> Built RBM3D.Test.Axioms (4.1s); Built RBM3D (72s); Build completed successfully (4378 jobs). EXIT 0
   (the root module runs `#assert_rbm_axioms` after the owner-text edit; error lines: 0)
#print axioms (scratch file above):
'RBM.BA.stNewPQgL_wardCls' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSTNewPQgL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baZeroModeSet_UN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baZeroModeSet_ThetaN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep2Gen_USemigroup' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baIterationsGen2_fam' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSTIterationsgL'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSTIterationsIIgL'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ZeroModeBAInst.inst_newPQ_ba' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ZeroModeBAInst.inst_usemigroup' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ZeroModeBAInst.inst_iterationsgL'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ZeroModeBAInst.inst_iterationsIIgL'' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Frozen signatures: no merged file touched (§1).

## 6. Paper deltas

Targets 1-6 are BA readings of merged generic texts; the Lean/paper differences (carrier classes in place of `|E| < 2`, `M = mI`,
inline `‖m‖ ≤ 1` for `‖m‖ = 1`; R2* at `B_{s,0}`) are those of D720 and D563 (present in `docs/paper-deltas.md:1772`, `:1522`).
Target 3 `ThetaN` at the carrier `Step2Gen_ThetaN (baFMz …)` is a Lean form choice (no BA twin), not a statement difference.
Prove report (d): no candidate. No uncovered difference found.

## 7. Observations (no verdict effect)

- O1: target 1's instance (:183) and the U1s1/U1s2 instances (:215, :222) end in `True` after a `have` of the applied theorem; the
  application compiles with every premise discharged, which is what §4 step 2 asks. Target 2's instance states its conclusion.
- O2: 409 lines against the central 320 (below the 640 stop line); the case-(i) `BAFlow` proof is :254-335 (82 lines, below 120).
- O3: prover proved `t ≤ T₀` for `szI` directly (:327-335) instead of via `TwistStep2_T0_ge`; no statement effect.

## 8. Verdict

| target | verdict |
|---|---|
| 1 `stNewPQgL_wardCls` | PASS |
| 2 `baSTNewPQgL` | PASS |
| 3 `baZeroModeSet_UN`, `baZeroModeSet_ThetaN` | PASS |
| 4 `baStep2Gen_USemigroup` | PASS |
| 5 `baIterationsGen2_fam` | PASS |
| 6 `baSTIterationsgL'_holds`, `baSTIterationsIIgL'_holds` | PASS |
| 7 instances | PASS |

**T2500: PASS.** No dispatcher sign-off needed.
