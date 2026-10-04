Auditor model: claude-opus-5-5
# T2092 audit (round 1): ST2-04 `Induction/Step2Iterate.lean`. Verdict: PASS
`date -u`: Sun Oct  4 01:23:55 UTC 2026. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2092-audit1` (detached at 1c43ba9 = t/T2092). Scratch: `scratchpad/T2092/`.
Pin: ticket T2092 says "copy verbatim from probe `0362cbc:RBM3D/Probe/T2039Pins.lean`, ranges 2243-2525 and 3572-5346, merged declarations imported". The check file `docs/tickets/checks/T2092-check.lean` only `#check`s merged names. So the statement check is a script diff against the probe.

## 1. Statements against the pin (script diff)
`stmtdiff.py`: every `theorem/def/abbrev/structure` header in the probe ranges vs the file, up to `:=`, whitespace-normalised, `ST2_Bctl`→`STBctl`:
```
probe decls in ranges 88 file decls 73
statement identical: 53
statement differs: ['ST_step2_concl']
  PROBE 4871 : theorem ST_step2_concl {d : ℕ} (h : STStep2 d) : 3 ≤ d → ∀ κ ε 𝔡 ... 
  FILE  1502 : theorem ST_step2_concl {d : ℕ} (h : STStep2Parts d) : 3 ≤ d → ∀ κ ε 𝔡 ... 
probe-only (merged/dropped): ['STScaleInv', 'STScaleOk', 'STScaleAdm', 'ST_STprof_pos', 'ST_card_lab_le', 'STScaleExists', 'STOptL2', 'STL2decayPT', 'STLocalAvgOfL2', 'STAvgU', 'STLocalEntryU', 'STGdecayW', 'STStep2Concl', 'STLI', 'STKI', 'STLKI', 'STksimLK', 'STelklk', 'STavgErr', 'STegt', 'STeeLoop', 'STee', 'STLIM', 'STLKIM', 'STksimLKM', 'STelklkM', 'STavgErrM', 'STegtM', 'STeeM', 'STgAN', 'STgDriftN', 'STeeUM', 'STGridRepNAt', 'STGridRepN']
file-only (new): ['STStep2Parts', "ST_step2_of_pins'", "ST_step2_of_pinsN'", "ST_step2_of_pinsLW'", 'ST_K2e_of_flow', 'ST_hq_of_data', 'hs0', 'hst', 'tInst_nonneg', 'ht1', 'htT', 'bdata_sz0', 'bdata_spec', 'k2_sz0', 'CK0_pos', 'hK2_sz0', 'hq_sz0', 'scale_sz0', 'Kseq0_adm']
```
54 moved = 53 identical + `ST_step2_concl`. All 11 named targets except `ST_step2_concl` have their probe statements unchanged, in particular `ST_step2_of_pins` and `ST_step2_of_pinsN` (`: STStep2 d`, nine pins as hypotheses).
Moved defs, full body (`defs.py`): `STSelfImp 56 2266 SAME`; `STStep2Parts` new.
The 34 dropped declarations match the merged text exactly (`merged.py`, full def body / theorem header):
```
STScaleInv Step2Events:159 SAME | STScaleOk Step2Defs:624 SAME | STScaleAdm Step2Defs:635 SAME
ST_STprof_pos Step2Events:165 SAME | ST_card_lab_le Step2Events:172 SAME | STScaleExists Step2Defs:656 SAME
STOptL2 Step2Defs:667 SAME | STL2decayPT Step2Defs:683 SAME | STLocalAvgOfL2 Step2Defs:694 SAME
STAvgU/STLocalEntryU/STGdecayW/STStep2Concl Step34Pins:192/199/208/221 SAME
STLI..STee (9) Step34Pins:107-159 SAME | STLIM..STGridRepN (12) Step2Defs:713-854 SAME
STBdata (conclusion of ST_Bdata_holds): probe 2542 merged Step2Events:209 SAME
```
**D-1 / `ST_step2_concl`.** The merged `STStep2` (`Step2Defs.lean:599`) concludes `STStep2Concl`, but the probe's `STStep2` (probe 805) concludes the triple. The probe's `STStep2` is now the new def `STStep2Parts`. Check: the def body diffs against probe 805-818 with no change except the name (`diff` of the whitespace-normalised bodies after renaming `STStep2Parts`→`STStep2`: identical up to the trailing context lines). `ST_step2_concl : STStep2Parts d → (merged STStep2 body)` is therefore the probe's intended `STStep2(triple) ⇒ bundle` bridge, and its hypotheses are unchanged. This is the forced adaptation that the preflight flagged. Paper-delta coverage is §5 below. Quantifier order, `3 ≤ d`, the `∀ᶠ` placement, the exponents `1/5`, `1/6` and `(3C+1)𝔠_d ≤ 1/60` all come verbatim from the probe.
New corollaries (ticket-requested; they do not change the probe statements):
```
theorem ST_step2_of_pins' {d} (hNew : STNewKLK d) (hLWT : STLWT d) (hEMe : STEMn2Exp d) (hMart : STGridMart d) (hOpt : STOptL2 d) (hClos : STLocalAvgOfL2 d) : STStep2 d
theorem ST_step2_of_pinsN' ... (hRep : STGridRepN d) ... : STStep2 d
theorem ST_step2_of_pinsLW' {d} (hd : 3 ≤ d) (hNew : STNewKLK d) (hLW : LWtermExp d) ... : STStep2 d   -- bridge STLWT_of_LWtermExp, carries hd (D143)
```
Discharged by merged proved theorems:
```
Induction/Step2K2.lean:132:theorem stK2decay_holds (d : ℕ) : STK2decay d
Path/NetLift2.lean:688:theorem stNetLift2_holds (d : ℕ) : STNetLift2 d
Induction/Step2Scale.lean:430:theorem stScaleExists_holds (d : ℕ) : STScaleExists d
```
Remaining pins: `STNewKLK`, `STLWT`, `STEMn2Exp`, `STGridMart`/`STGridRepN`, `STOptL2`, `STLocalAvgOfL2`. These match the ticket.

## 2. Vacuity, hidden hypotheses, cycles
- No new `structure`; the only new def is `STStep2Parts`, a plain Prop with the same body as the probe's `STStep2`. The pins are explicit hypotheses in the signatures, not fields.
- No cycle: the file imports only merged modules (`Step2Events`, `Step2Scale`, `Path.NetLift2`, `Step2K2`); the discharged pins are merged theorems (axioms below).
- Every external input stays a named pin hypothesis. Concrete limit data for `sz0` are the merged `sz0_tendsto`, `sz0_bandwidth`, `flow_z0`, `conStInd_inst`, `Bctl_tInst_tendsto` (`Induction/Defs.lean:510-517`); the instances use them.

## 3. Compiled nonempty instances (d = 3, `sz0`, `z0`, `s ≡ 0`, `t ≡ 1/16`, `C = 1`, `𝔠_d = 1/240`)
```
$ grep -n "^example" RBM3D/Induction/Step2Iterate.lean | cut -c1-100
1929 ST_Bdata_holds (via bdata_sz0, at κ=ε=𝔡=1/10, 𝔠=1/6, z0, tInst)
1937 ST_selfImprove_section   1948 ST_iterate   1957 ST_decay_pt   1966 ST_L2_decay_pt
1973 ST_base_inv   1982 ST_avgU_of_avg   1986 ST_concl_of_step2
1993 ST_step2_of_pins   2003 ST_step2_of_pins'   2012 ST_step2_of_pinsLW' (→ pinsN')
2021 ST_step2_of_pinsN   2031 ST_step2_concl   2041 ST_gridMart_of_repN
```
(annotated by hand from file lines 1929-2059; all 11 named targets plus the 3 corollaries are covered.)
Discharged deterministic hypotheses, read off the example bodies:
- `SizeTendsto` (`sz0_tendsto`), `Bandwidth 1/6` (`sz0_bandwidth`), `STFlow` (`flow_z0`);
- time data `hs0`, `hst`, `ht1`, `htT` (`sixteenth_le_lemT`), and `STConStInd` (`conStInd_inst`);
- size data `hBd`/`cB`, `c` (from `ST_Bdata_holds`), the `𝒦^{(2)}` bound `hK2` (from `stK2decay_holds` via `ST_K2e_of_flow`);
- closure arithmetic `hq` (`ST_hq_of_data` with `h3 : (3·1+1)/240 ≤ 1/60`), the scale family `STScaleAdm`/`STScaleOk` (`stScaleExists_holds`), and the time section `tt ≡ 1/32 ∈ [0,1/16]`;
- the `STStep2 3` data (merged `inst_step2`, `Step2Defs.lean:880`, which discharges `3 ≤ 3`, `κ, ε, 𝔡 = 1/10`, `flow_z0`, the times and `conStInd_inst`);
- grid `K_n = ⌈N^{C_K}⌉ ≠ 0` (`Nat.ceil_pos`, `one_le_size_sz0`).
Left as example hypotheses:
- the pins (`STLWT`, `STEMn2Exp`, `STNewKLK(At)`, `STGridMart(At)`, `STGridRepN`, `STOptL2` or its conclusion, `STLocalAvgOfL2`, `STK2decay`, `STNetLift2`, `STScaleExists` in the unprimed forms);
- stochastic premises of the statements (`STDecay`, `STStep1Weak`, `STScaleInv`, `STStep2Avg/Local/Decay`, `STStep2DecayPT`, `STStep2Parts`);
- the one-step input `hSelf`/`hbase` of `ST_iterate`/`ST_decay_pt`.
No `N = 0`, empty index, collapsed window or `False` premise: `W_n = (2(n+1))^5`, `L_n = 4(n+1)`, `[s,t] = [0,1/16]`. Every example compiles (module build below).

## 4. Build, axioms, hygiene, diff scope
```
$ lake build RBM3D.Induction.Step2Iterate   (audit worktree)
Build completed successfully (3759 jobs).   exit=0   (no `error` lines; no "declaration uses 'sorry'")
$ lake env lean scratch/Ax.lean   (#print axioms)
'RBM.Gauss.Sizes.ST_selfImprove_section' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_iterate' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_decay_pt' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_L2_decay_pt' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_base_inv' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_Bdata_holds' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_step2_of_pins' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_avgU_of_avg' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_step2_concl' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_gridMart_of_repN' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_step2_of_pinsN' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_step2_of_pins'' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_step2_of_pinsN'' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_step2_of_pinsLW'' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_concl_of_step2' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_K2e_of_flow' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_hq_of_data' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step2IterateInst.bdata_sz0' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step2IterateInst.k2_sz0' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step2IterateInst.hq_sz0' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step2IterateInst.scale_sz0' [propext, Classical.choice, Quot.sound]
$ grep -cE '\bsorry\b|\badmit\b|native_decide|^axiom ' RBM3D/Induction/Step2Iterate.lean
0
$ git diff --name-status main...t/T2092
A	RBM3D/Induction/Step2Iterate.lean
M	RBM3D/Test/Axioms.lean        (+7 lines inside `owedProps` only: 1 comment + STScaleOk, STScaleAdm, STGridMartAt, STStep2Local, STStep2Avg, STStep2Parts)
$ git merge-base main t/T2092 → 6583ca2; main = 382b6d9; git merge-tree --write-tree main t/T2092 → exit 0 (no conflict);
  no change since 6583ca2 to Test/Axioms, Step2Defs, Step2Events, Step2Scale, NetLift2, Step2K2, Step34Pins
$ name-clash grep of the 73 declaration names of the file against `main` (RBM3D/**, excl. Probe): 0 clashes
```
Frozen signatures: no merged file is touched. The full `lake build` with `#assert_rbm_axioms` is run by the hub at merge. The prove report shows the registry pre-check failing before the 6 lines and passing after (`3058 theorems, 1144 definitions, 0 axioms`).

## 5. Paper deltas
- `STStep2` (library) concludes `STStep2Concl`, the probe's concludes the triple; `STStep2Parts`/`ST_step2_concl` bridge them. This is covered by the existing `docs/paper-deltas.md:405` (D92/T2039j note: "库里的 `STStep2` 结论是合并的 `STStep2Concl`（T2066a…）") and `:402` (D89/T2039g, `STStep2Avg` single-charge vs `STAvgU`), and by the new candidate `T2092a` in the prove report.
- Registry lines are candidate `T2092b`; new names are `T2092c`. All other target statements are verbatim probe text, whose paper deltas are the T2039 entries.

## Verdict per target
| target | verdict |
|---|---|
| ST_selfImprove_section, ST_iterate, ST_decay_pt, ST_L2_decay_pt, ST_base_inv, ST_Bdata_holds | PASS |
| ST_step2_of_pins, ST_step2_of_pinsN (+ primed corollaries, LW' with `3 ≤ d`) | PASS |
| ST_avgU_of_avg, ST_gridMart_of_repN | PASS |
| ST_step2_concl (hypothesis `STStep2Parts` = probe `STStep2` verbatim; forced by merged `STStep2`, delta covered) | PASS |
Overall: **PASS**. No dispatcher sign-off needed.

## Observations (no effect on statement, instance, build, axioms or delta coverage)
1. `ST_K2e_of_flow`, `ST_hq_of_data` are public unpinned helpers in `RBM.Gauss.Sizes`, neither `private` nor stem-prefixed (CLAUDE.md §3 (E)). The prove report discloses them (T2092c). The instance helpers (`hs0`, `hst`, `ht1`, `bdata_sz0`, …) are public but sit in the stem namespace `RBM.Gauss.Step2IterateInst`.
2. The file also imports `RBM3D.Induction.Step2K2` (merged, T2093), which `stK2decay_holds` needs; the ticket allows "the merged files they need".
3. The examples for `ST_iterate` and `ST_decay_pt` take `hSelf` and `hbase` as hypotheses rather than chaining `ST_selfImprove` and `ST_base_inv`. The full chain from the pins alone is exercised by the `ST_step2_of_pins*` examples.
4. Prove report (a) line 38 says the three proved pins need no `3 ≤ d`. `STK2decay d` has `3 ≤ d →` inside its body (`Step2Defs.lean:569`), so `ST_K2e_of_flow` carries `hd3`. This is a report wording inaccuracy only.
