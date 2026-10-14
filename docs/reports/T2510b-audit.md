Auditor model: claude-opus-5-5

# T2510 row b audit (round 1) — Wed Oct 14 17:42:12 UTC 2026

Branch `t/T2510b` 7dc39fd9, merge-base `dff951fe` (= `main`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2510b-audit1` (detached).
Scratch `S` = scratchpad `T2510b/` (uncommitted). Targets 11-15 of `docs/tickets/T2510.md`.

## 1. Diff scope (sole writable files: `RBM3D/BA/Step6BA.lean` new, `RBM3D.lean` import, `RBM3D/Test/Axioms.lean` row-b owner texts)
```
$ git diff --name-only main...t/T2510b
RBM3D.lean
RBM3D/BA/Step6BA.lean
RBM3D/Test/Axioms.lean
$ git diff main...t/T2510b -- RBM3D.lean      # one line after the last import, before #assert_rbm_axioms
 import RBM3D.Chain.ExpIntIQGen
+import RBM3D.BA.Step6BA
$ git diff main...t/T2510b -- RBM3D/Test/Axioms.lean | grep -E "^[+-] " | grep -oE "^[+-]\s+\`[A-Za-z.']+" | sort | uniq -c
   1 -   `RBM.BA.STExp            (STExp2UgL)        1 +   `RBM.BA.STExp
   1 -   `RBM.BA.STExpIntIgL                          1 +   `RBM.BA.STExpIntIgL
   1 -   `RBM.BA.STExpIntIIIgL                        1 +   `RBM.BA.STExpIntIIIgL
   1 -   `RBM.BA.STExpIntIVgL                         1 +   `RBM.BA.STExpIntIVgL
   1 -   `RBM.BA.STExpWardIIgL                        1 +   `RBM.BA.STExpWardIIgL
   1 -   `RBM.Gauss.Sizes.STExp   (STExp2U)           1 +   `RBM.Gauss.Sizes.STExp
```
(columns joined by the auditor.) Every changed `Axioms.lean` line keeps its name; only the `--` owner text changes; hunks at 225-226, 235, 237, 239-240, 242 = the ticket's row-b lines (`:225, :226, :235, :237, :239, :240, :242`). No merged Lean file under `Chain/`, `Induction/`, `Graph/`, `BA/` changes; no frozen signature touched.

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.BA.Step6BA ; echo exit $?
Build completed successfully (4246 jobs).
exit 0
$ grep -E "error" S/build.log | wc -l ; (non-longLine Step6BA warnings)
0 ; 0
$ lake env lean -Dlinter.unusedVariables=false S/audit_pins.lean ; echo exit=$?     # #print axioms lines
exit=0
'RBM.BA.baExpWardIIgL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baExpIntIIIgL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baExpIntIVgL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baExpIntIgL'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep6RegI_of_pins' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep6RegIII_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep6RegI_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep6RegII_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep6RegIV_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ F=RBM3D/BA/Step6BA.lean
$ grep -nE "\bsorry\b|\badmit\b|^\s*axiom |native_decide" $F | wc -l            -> 0
$ grep -nE "^(private |noncomputable )*(def|abbrev|structure) " $F | wc -l       -> 0   (X1-C4: no new def in row b)
$ grep -nE 'mE\b|\|E\||SB d|M = m|m • 1|etaT|STFlow|bandFM' $F | wc -l           -> 0   (C1)
$ grep -nE 'STImproveExpAver|st6_expAvgU_of_ping|LWtermEXPG' $F                  -> line 24 only (module docstring "no `STImproveExpAvergL` ...")
$ grep -o "[A-Za-z_.]*withLam [0-9a-z]*" $F | sort | uniq -c                     -> every hit is `<sz>.withLam 0` (UBA-C1)
   1 .withLam 0 / 8 PinsBA_szI.withLam 0 / 3 PinsBA_szII.withLam 0 / 4 PinsBA_szIV.withLam 0 / 13 sz.withLam 0
```
The full `lake build` (`#assert_rbm_axioms`) is the hub's at merge; the prove report pastes one (exit 0, 0 axioms in `RBM`).

## 3. Statements against the pins (auditor scratch `S/audit_pins.lean`)
Built by script: imports of `T2508-check.lean` and `T2510-check.lean` plus `RBM3D.BA.Step6BA`; `T2508-check.lean:97-247` and
`T2510-check.lean:139-216` copied verbatim; then the auditor's `example`s. Compiles, exit 0 (above).
```
$ grep -n "^example" S/audit_pins.lean | cut -c1-150
282:example : T2510_RowB := fun d => ⟨baStep6RegIII_holds d, baStep6RegI_holds d, baStep6RegII_holds d, baStep6RegIV_holds d⟩
283:example (d : ℕ) : BAStep6R d STReg5I = T2510_Step6BA d STReg5I := rfl
284:example (d : ℕ) : STExpWardIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz
285:example (d : ℕ) : STExpIntIIIgL d (… BA tuple …) := baExpIntIIIgL d
286:example (d : ℕ) : STExpIntIVgL d (… BA tuple …) := baExpIntIVgL d
287:example (d : ℕ) : T2508_ExpIntIgL' d (… BA tuple …) := baExpIntIgL' d
288:example (d : ℕ) : STExpIntIgL' d (… BA tuple …) → T2510_Step6BA d STReg5I := baStep6RegI_of_pins d
289:example (d : ℕ) : STExpIntIgL' d (… BA tuple …) = T2508_ExpIntIgL' d (… BA tuple …) := rfl
```
(lines 285-289 abbreviated by the auditor; the file carries the full tuple `(fun sz => Sizes.seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`.)

| target | Lean statement (extracted) | pin | result |
|---|---|---|---|
| 11 `baExpWardIIgL`, `baExpIntIIIgL`, `baExpIntIVgL` | `(d : ℕ) : STExpWardIIgL / STExpIntIIIgL / STExpIntIVgL d <BA tuple>`; no hypothesis | merged generic pins at the BA tuple (ticket target 11, `T2508_RowAOf` conclusions) | equal (284-286); all `d`, the `3 ≤ d →` sits inside the merged pin texts |
| 12 `baExpIntIgL'` | `(d : ℕ) : STExpIntIgL' d <BA tuple>` | `T2508_RowBOf` conclusion `T2508_ExpIntIgL'` | equal (287, 289 `rfl`) |
| 13 `baStep6RegI_of_pins` | `STExpIntIgL' d <BA tuple> → BAStep6R d STReg5I` | ticket target 13 (shape of `T2510_RegIIIOfPin` with the primed IntI pin) | equal (288) |
| 14 `baStep6Reg{III,I,II,IV}_holds` | `(d : ℕ) : BAStep6R d STReg5{III,I,II,IV}` | `T2510_RowB` (binding) | equal (282) |

Quantifier order, `∃ 𝔠d` inside each pin, ranges `0 ≤ s < t ≤ T₀`, windows: all carried by the merged pin texts (`STIngR6gL`); row b restates none.

## 4. Hidden hypotheses, vacuity, cycles
- No structure, no new `def`, no hypothesis binder on 11, 12, 14. 13 has exactly one premise, the merged pin `STExpIntIgL'` (discharged by 12 in `baStep6RegI_holds`).
- Every family row is a merged BA theorem passed to the T2508 producers (`Step6BA.lean:56-105`): `isProbabilityMeasure_seqP`, `baStep5CasesGen_flowFacts`, `baCltRepg_holds`, `baKsol_oneLoop`, `baStep5CasesGen_wardIdent`, `baB45Gen_facts`, `baEKSumNdecaygL_holds`, `baEKKer_flow` (first three conjuncts via private `Step6BA_Ker3`; all four for IntI'), `baIniTermGen_cltFlow`, `SEforLnBA_Kbound` (after `intro hd`), `baEKSumRes2NALgL_holds`, `baEKSumRes2gL_holds`, `Step6PinsBA_Aof`, `baStep5KerGen_thDecay` (binder-swap adapter, decision (7)), `baExpDuhamelQgL`. These compiled with no extra hypothesis.
- Regime (i) body (`Step6BA.lean:108-145`) reads row a's `baExpLKLKHigL`, `baExpDriftDecaygL`, `baExpWardIgL'`, `baExpIniIgL'`, `baExpDuhamelZgL/QgL`, `baExpAvgUgL_of_tl1`, `Step6BridgeBA_LW` and core `st6_caseI_coreg'`; TL1/TL2 come only from the `Concl` slot of `BAStep6R` (pin). No `STImproveExpAvergL`, every-`n` `hK1` or `LWtermEXPG` (grep above).
- Dependencies are merged (`main` dff951fe: T2508 a/b, T2510 row a); row b defines nothing they import, so no cycle.
- No external hypothesis is added.

## 5. Compiled nonempty instances (target 15; `Step6BA.lean` section `Inst`, compiled in the build above)
Nine `example`s at `d = 3`, one per public theorem (11: three; 12; 13; 14: four). Data are row a's merged private data read by `open private`:
```
Step5CasesBA.lean:391  private def Step5CasesBA_Datum … := 0 < κ ∧ BAFlow sz κ (1/2) (1/9) (1/10) z ∧ (∀ n, 0 ≤ s n) ∧ (∀ n, s n < t n) ∧
                      (∀ n, t n ≤ BAflowT0 sz z n) ∧ ∀ 𝔠d, 0 < 𝔠d → STConStInd sz 𝔠d s t
Step6PinsBA.lean:351  Step6PinsBA_szI := Step5CasesBA_sz 4 25 2 …   ; datI : Datum szI zI (3/1000) (fun _ => 0) (fun _ => 1/400)
Step6PinsBA.lean:367  datII : Datum szII zII (3/5000) 0 (1/2000)   (L,W₀,lam) = (4,25,5)
Step6PinsBA.lean:373  datIV : Datum szIV zIV (1/1000) 0 (1/2000)   (L,W₀,lam) = (3,40,6)
Step6PinsBA.lean:325,337,341  reg3, con0, tT0 at (sz0, zSeq, flow_sz0), s ≡ 1/2 < t ≡ 3/5
Step6PinsBA.lean:378  regI / regII / regIV : STReg5I/II/IV proved by norm_num at those data
```
All of these are theorems (proved, merged): the flow, `0 ≤ s < t ≤ T₀`, the regime and `(con_st_ind)` are discharged; `L ≥ 3`, `W₀ ≥ 25`,
`t > s` — nondegenerate, no `N = 0`, no empty window. Binders left in the examples: `Step6PinsBA_prem` (the seven Step 1-5 premises of
`STIngR6gL`: `STLKgL`, `STDecaygL`, `STExp2gL`, `STStep2CoregL`, `STLmaxUgL`, `STLKUgL`, `STGdecayWgL`) and `Step6PinsBA_TL` (TL1, TL2 at
every `u ∈ [s,t]`): other gates' pins, allowed. The pins' own conclusion-slot antecedents (Duhamel identity, drift bounds, `STExpAvgUgL`)
remain as antecedents of the conclusion, as in the pin text. Targets 13, 14 conclude `STStep6ConclgL` at the data. Present, nondegenerate.

## 6. Paper deltas
Row b states no new Lean/paper difference: 11, 12 are the merged generic pins at the BA tuple; 14 is `BAStep6R` (row a's def, merged).
The primed regime-(i) pins it reads are covered by D725/D732 (`docs/paper-deltas.md:1808, 1833`); the eventual `hK1` (F1) is Lean-internal
(DECISIONS §332 (3)). Prove report proposes none (`T2510ba` unused); none needed.

## 7. Observations (no verdict effect)
- O1: the prove report (b) "Registry scan" and full build were run by the prover; the auditor reproduced the module build and axioms only (full build is the hub's at merge).
- O2: 9 `longLine` style warnings from the module docstring (`set_option linter.style.longLine false` is set after it); harmless.

## Verdicts
- Target 11 (`baExpWardIIgL`, `baExpIntIIIgL`, `baExpIntIVgL`): **PASS**
- Target 12 (`baExpIntIgL'`): **PASS**
- Target 13 (`baStep6RegI_of_pins`): **PASS**
- Target 14 (`baStep6RegIII_holds`, `baStep6RegI_holds`, `baStep6RegII_holds`, `baStep6RegIV_holds` = `T2510_RowB`): **PASS**
- Target 15 (instances): **PASS**

**T2510b: PASS.** No dispatcher sign-off needed.
