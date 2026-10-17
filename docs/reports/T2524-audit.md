Auditor model: claude-opus-5-5

# T2524 audit, round 1 (1a-audit of the BA-D design gate, with Amend 1 items 1-5)
Written Sat Oct 17 01:02:59 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2524-audit1`, detached at `t/T2524` = 67f99efb.
Audited: `docs/reports/T2524-design.md` (240 lines), probe `RBM3D/Probe/T2524Pins.lean` (409 lines), Amend 1 items 1-5.
Scratch: `scratchpad/T2524/audit/`. **Census base (Amend 1 (b)): `afab243f`**, because T2523 has not merged: `git diff --stat main...t/T2523` = `docs/claude-team/tools/DeadDecls.lean` only; `main` = 99651343, and `git diff --stat afab243f main -- RBM3D` is empty.

**Verdict: PASS** (report-only design gate; no stop rule fired; no dispatcher sign-off needed).

## 1. Scope, build, axioms
```
$ git diff --stat main...HEAD            # and the same with `-- RBM3D`
 RBM3D/Probe/T2524Pins.lean | 409 +++++  (1 file changed, 409 insertions)   -- only the probe; no merged file changed
$ grep -nE '\b(sorry|admit|axiom|native_decide)\b' RBM3D/Probe/T2524Pins.lean   -> no match (exit 1)
$ lake env lean RBM3D/Probe/T2524Pins.lean -> exit=0, 0 output lines
$ lake build RBM3D.Probe.T2524Pins          -> Build completed successfully (4443 jobs).
$ lake env lean ax.lean   # `#print axioms` of every `theorem T2524_*` (31, extracted by grep)
  31 X depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean docs/tickets/checks/T2524-check.lean -> exit=0, 33 lines, 0 error lines
```
Probe: 409 <= 500. No `structure`/`axiom` in the probe; hypotheses of the chain theorems are the D2 texts (the rows' targets) and `UNL32` (authorized external).

## 2. Statements against the ticket's pin
Ticket pin (final target) `baStep5III_holds_any (d : ℕ) (hd : 3 ≤ d) : STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0`.
```
$ grep -cF '<the pinned conclusion text>' <file>
T2524.md: 1   T2524-amend-1.md: 1   T2524-design.md: 2   T2524Pins.lean: 2   (probe :375 T2524_Step5IIIAny, :101)
```
D2 texts at `d = 3` equal the merged texts (probe :112-119: `Iff.rfl` for `Good`, `Walk`; `3 ≤ 3 →` for `GoodThm`, `FromWalk`), so the general texts are the merged ones with `3 → d` and `3 ≤ d →` in front (house shape of `STIngR5gL d`). Chain D2 → `STPfStep5gL d` → `STStep5IIIgL d` → `BAThm27L d` (merged `baThm27L_any`, `BA/UNBUniv:286`) compiles (probe :89-107). `T2524_Thm27 := ∀ d, 3 ≤ d → BAThm27L d` (:355); `T2524_final_shape` keeps `UNL32` as the single external hypothesis (:364); `d = 3` recoveries (:370, :387-392) compile.

**Independent check of the decisive claim ((c) = none, chain closes at every d).** I recompiled the prover's scratch generalization of Good, Good2, Walk, Walk2, Targets (copied to my scratch, built against my worktree; module root `T2524G`) and checked the exact pinned type with fully qualified merged names:
```
Good: exit=0 output_lines=0 | Good2: exit=0 0 | Walk: exit=0 0 | Walk2: exit=0 0 | Targets: exit=0 0
grep sorry|admit|axiom|native_decide in the five generalized files: none (the `open private` lines of Walk, Walk2 are identical to afab243f)
$ lake env lean audit_chk.lean    # import T2524G.Targets
example : ∀ d : ℕ, 3 ≤ d → RBM.BA.STStep5IIIgL d (fun sz => RBM.Gauss.Sizes.seqP (sz.withLam 0))
    (fun sz κ ε 𝔠 𝔡 z => RBM.BA.BAFlow sz κ ε 𝔠 𝔡 z) RBM.BA.baFMz RBM.BA.BAflowT0 := RBM.BA.baStep5III_holds_any   -- exit 0
baStep5IIIGoodThm_holds : ∀ (d : ℕ), BAStep5IIIGoodThm d
baStep5IIIWalk_holds : ∀ (d : ℕ), BAStep5IIIWalk d
baStep5IIIFromWalk_holds : ∀ (d : ℕ), BAStep5IIIFromWalk d
'RBM.BA.baStep5III_holds_any' depends on axioms: [propext, Classical.choice, Quot.sound]
(same for baStep5III_holds, baStep5IIIGoodThm_holds, baStep5IIIWalk_holds, baStep5IIIFromWalk_holds, baPfStep5_holds)
```
So `baStep5III_holds_any` is provable at the exact pinned type with no premise beyond `3 ≤ d`, against the unchanged merged imports: no class (c) item, and no chain input merged only at `d = 3` outside U5 (BAD-C3 (2)).

## 3. D1 census, re-derived by my own grep at afab243f
```
$ python3 -I census.py afab243f   # head = lines before the instance section (`/-! ## N. Compiled`/`Instances`)
file     lines grepL(Sizes3|Zd3) occ | headA headB headEval Fin3 | tailA+B
Edet      1493     9     9 |     0     4     0   10 |    28
Edet2     1277     6     6 |     0    23     1    0 |    27
Good       704    17    17 |    23    31    18    8 |     8
Good2      198     1     1 |     1     5     2    2 |     5
Ker        709     2     2 |     0     0     0    0 |     4
Ker2       471     8     9 |     0     3     1    0 |    27
Walk      1799    21    21 |    17    19     7    2 |    58
Walk2     1067    52    52 |   114    48    15    0 |     0
Targets    112     0     0 |     0     0     0    0 |     0
total     7830   116   117 |   155   133    44   22 |   157
```
(A = `Sizes|Zd|Idx|zdistInf|KLloopOf|tailTD|Ctot|Grid_level|lossE2wG 3`; B = `) ^ 3`, `((3 : ℕ) : ℝ)`, `6|2|12 * 3`, `(3 : ℝ) *`; Eval = `3 ≤ 3`, `1 ≤ 3`, `le_rfl`.)
- Per-file `Sizes 3|Zd 3` lines (116) and occurrences (117) match the report exactly; 22 `Fin 3` match.
- Head A of Edet, Edet2, Ker, Ker2 = 0, as reported. Their head B hits are d-free (`τ^3` of 4-loops, `(1 + log W)^3`, `(2JE)^3`, `((1-v)/(1-w))^3`, `3*3*3`); these heads are stated at `(d : ℕ)` already.
- What remains of my patterns in the five **generalized** heads (`grep` over the scratch files): Good :362, :373, :407 (`τ^3`, 4-loop); Walk :201 (`τ^3`), :746 (`N^3`), :1436 (`((1-v)/(1-w))^3`); Walk2 :111, :144, :246, :318, :329, :333, :393, :941 (`N^3`), :920, :943 (`Cv = ((3 : ℕ) : ℝ)`, the polynomial exponent, the report's b7). All d-free, as the report says. No `3 ≤ 3` or `1 ≤ 3` remains.
- My lexical totals (five heads: A 155, B 103) differ from the report's (151, 85) by pattern choice (I count `Grid_level 3`/`lossE2wG 3` as A and the d-free `) ^ 3` as B). This is an **observation** only: the classification (a)/(b), (c) = 0 is confirmed by the compile above.

## 4. D4 price, re-derived
```
$ python3 -I price.py   # difflib, afab243f -> generalized, changed/added lines on the new side, imports excluded
file     orig   new  changed  head  tail
Good      704   706      50     48     2
Good2     198   200      12      9     3
Walk     1799  1799      37     33     4
Walk2    1067  1069     173    167     6
Targets   112   117      14     13     1
total changed 286: head 270, tail 16
new-files layout (heads before the instance section): Good 604; Good2 81; Walk 1520; Walk2 986; Targets 60 -> 3251
```
Report: head 272, tail 16, copied heads 3,251. My head count is 270 (difflib alignment vs diff(1); Walk2 167 vs 169): agrees to 2 lines. In place ≈ 300 landing (≈ 520 at ×1.74) against ≈ 3,330 for new files: the recommendation (in place, BAD-C4) and row sizes (R1 ≈ 520 ≤ 1,950; R2 ≈ 190) stand. Rows sequential (import chain; R2 imports R1's theorem): correct.

## 5. Amend 1 items 1-5
| item | where in the design report | audit check | result |
|---|---|---|---|
| 1 (a) "deleted by T2523" column | §1 (b)-table column and the 35-name list (lines 100-119); §4 row table last column | Re-ran the T2523 tool: `diff <(git show t/T2523:docs/claude-team/tools/DeadDecls.lean) DeadDecls_T2523.lean` identical; `lake env lean` exit 0; `cmp` with the prover's output: identical. Unreached list (section (b)) vs the 35 names: `zSeq flow_sz0 half_lt_t0 sz0_lam_pos Step5IIIGood_sz0_lam_le Step5IIIGood_reg_sz0` = yes, the other 29 (incl. `lam_sq_mul_pow_ge pfStep5Grid_level pfStep5_fl baKbound_holds baEMn2ExpHK baKsol_one baGridRepNAt2_holds baFlow_premises baStep5CasesGen_flowFacts ST_step5_caseIII_of_pfgL STIngR5gL STStep5IIIgL STPfStep5gL lossE2wG baThm27L_any BAThm27L Thm27 final_shape sz0 Step5IIIWalk_Ctot Step5IIIGood_Wpow`) = no. Matches the report. | PASS |
| 1 (a) cont. | — | Identifiers of the generalized heads that T2523 deletes: only `baStep5III_EMatrix_level` (Walk:79) and `baStep5III_duhamel` (Walk:677), which are themselves unreached head declarations (the report's "2 in heads"), plus docstring mentions; identifiers new in the generalized heads: none deleted. | PASS |
| 1 (b) | report states base afab243f | census re-derived on afab243f (§3 above); T2523 unmerged | done |
| 1 (c) | §4: restore price 0 | consistent with 1 (a) | PASS |
| 2 `d = 4` instance | §5 "Instances"; probe :241-304 (`T2524_sz4`, `Admissible (1/8) (1/10)` every `n`), :397-407 | compiled; decol, locSC, QUE, QDiff of `Thm27 4` applied at `T2524_sz4` with `T2524_sz4_adm`; hypotheses: the rows' texts (other gates' pins) and `UNL32`; 78 lines < 150. BUniv not applied: its `d = 3` instance needs the bulk witness `S0_bulk`/`fp` (`Main/FinalShape:108-109`), so a `d = 4` application needs a `d = 4` bulk energy. Exceeds the fallback "Sizes 4 + Admissible". `n = 0` included, nondegenerate (`L = 4(n+1)`, `W = (2(n+1))^5`). | PASS |
| 3 BAD-C3 | §7, three answers with file:line | (1) no: no (c) item; (2) no: confirmed by the compile at abstract `d` (§2); (3) forecast 3 < 8 | PASS (all "no": no REQ) |
| 4 BAD-C4 | §4 "Recommend (A)", §7 "rows start after T2523 merges" | — | PASS |
| 5 D5 texts | §5 lines 206-215; probe :355, :364, :374, :383, :387-392 | pinned type verbatim (§2); `Thm27`, `final_shape` with single `UNL32`; one-line recoveries of `baStep5III_holds`, `baThm27L_three`, `Thm27_of_L32` at `d = 3` compile | PASS |

## 6. Ticket acceptance list and stop rules
- Check compiles on `main`: yes (§1). Probe compiles, 31/31 theorems standard axioms, no `sorry`: yes. `git diff main...t/T2524 -- RBM3D` = probe only: yes.
- D1 re-derived (§3), D4 re-derived (§4). Every (c) item: none; none open, so no Fable check is needed.
- Stop rules: merged file changed: no; probe 409 <= 500; open (c): none.
- Compiled nonempty instances: the chain at `d = 3` with every hypothesis discharged by merged theorems, only `UNL32` left (`T2524_baThm27L_three`, :135); the `d = 4` instance (:397); the (b) lemmas at `d = 4` (:306-350).

## 7. Paper deltas
Lean will now match the paper (Thm 2.7 at every `d ≥ 3`). D723 is withdrawn as D754 (`docs/paper-deltas.md:1873`, present). Candidate `T2524a` (D712 (d), "targets 3, 4 only at `d = 3`", superseded by R1) is proposed in §6 of the report. No uncovered Lean/paper difference found.

## 8. Observations (no RETURN)
- O1: the report's lexical token counts (151/85) depend on its patterns; mine give 155/103 (§3). The classification is confirmed by compilation.
- O2: head edit lines: 272 (report, diff(1)) vs 270 (audit, difflib).
- O3: the report's §5 reason for skipping BUniv at `d = 4` ("UN data at `d = 3`, `S0`, `fp`, `clsκ`") is loose. The conjunct `BAEnd_BUnivL 4` (`BA/UNPins:343`) needs a `d = 4` bulk-energy witness (`∀ᶠ n, BAbulk 4 …`). This does not affect item 2, which only requires `Sizes 4` + `Admissible`.
- O4: the report's header calls the prover "stage-1b"; this was a stage-1a design run. Process only.

## Verdict
T2524: **PASS**. The design report and the probe meet the ticket's acceptance list and Amend 1 items 1-5. No item is missing, no (c) item is open, and BAD-C3 is all "no", so no REQ is triggered. Merge only `docs/reports/T2524-design.md`; the probe stays on `t/T2524`.
