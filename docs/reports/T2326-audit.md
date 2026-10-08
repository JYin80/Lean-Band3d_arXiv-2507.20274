Auditor model: claude-opus-5-5

# T2326 audit (round 1): BA-DP3 G-in-place pilot (report-only design ticket)

Written Thu Oct  8 12:09:53 UTC 2026 (`date -u`). Audit worktree `RBM3D-wt/T2326-audit1`, detached at `t/T2326` = `4fca3d2` (merge-base with main `cc1158a`). Inputs: ticket, `T2326-prove.md`, `T2326-pilot.md`, the two probe files. Memory gate (CONTROL H122/H101 (4)): no certificate-module build running; free+spec+inactive 11.9 GB; one short `lake env lean` of another workflow.

## 1. Scope and sole writable files
```
$ git diff --stat main...HEAD
 RBM3D/Probe/T2326PilotQ.lean     | 878 +++++++++++++++++++++++++++++++++++++
 RBM3D/Probe/T2326PilotStep2.lean | 909 +++++++++++++++++++++++++++++++++++++++
 2 files changed, 1787 insertions(+)
$ grep import (heads of the probe files)
import RBM3D.Induction.Step2Iterate
import RBM3D.BA.FlowPins
import RBM3D.Induction.QDriftA
$ grep -cE '\bsorry\b|\badmit\b|native_decide|^axiom' RBM3D/Probe/T2326Pilot*.lean
RBM3D/Probe/T2326PilotQ.lean:0
RBM3D/Probe/T2326PilotStep2.lean:0
```
Only probe files on the branch (the two `docs/reports/T2326-*` files live in the main worktree, untracked, as for every ticket). No root import of `RBM3D`, no frozen signature touched (additions only). Stop rule: 1787 ≤ 2500.

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Probe.T2326PilotStep2      (12:07:44 UTC)
✔ [3778/3778] Built RBM3D.Probe.T2326PilotStep2 (23s)
Build completed successfully (3778 jobs).     exit 0, no error lines
$ lake build RBM3D.Probe.T2326PilotQ
✔ [3847/3847] Built RBM3D.Probe.T2326PilotQ (4.2s)
Build completed successfully (3847 jobs).     exit 0, no error lines
$ lake env lean S/AuditAx.lean   # #print axioms + rfl checks of the recovered types; exit 0
'RBM.Probe.T2326.ST_selfImprove_sectionG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2326.recovers_merged' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2326.bandStep2Facts' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2326.baStep2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.T2326Pilot.recovers_{dGridQN_eq_dFlowQN, dFlowQN_sumZero, aTrueQN_sumZero, hker_altQN, alt_hkerQN,
   goodSetN_A0clsQN, alt_hA0clsQN, measurable_altB4N, measurable_altB5N, measurable_STQopDriftN,
   measurable_dFlowQN}', 'bandQ', 'bandKer'  -- 13 lines, each: [propext, Classical.choice, Quot.sound]
example : type_of% @RBM.Probe.T2326.recovers_merged = type_of% @RBM.Gauss.Sizes.ST_selfImprove_section := rfl  -- ok
example : type_of% @RBM.Ind.T2326Pilot.recovers_goodSetN_A0clsQN = type_of% @RBM.Ind.goodSetN_A0clsQN := rfl -- ok
example : type_of% @RBM.Ind.T2326Pilot.recovers_alt_hA0clsQN = type_of% @RBM.Ind.alt_hA0clsQN := rfl       -- ok
$ lake env lean S/AuditCopy.lean  # band-free declarations copied unchanged; exit 0
example : type_of% @RBM.Ind.T2326Pilot.Qop_fastDecay = type_of% @RBM.Ind.Qop_fastDecay := rfl                -- ok
example : type_of% @RBM.Ind.T2326Pilot.fastDecay_of_diamInf = type_of% @RBM.Ind.fastDecay_of_diamInf := rfl  -- ok
example : type_of% @RBM.Ind.T2326Pilot.QDriftA_W0_gt_one = type_of% @RBM.Ind.QDriftA_W0_gt_one := rfl        -- ok
'RBM.Ind.T2326Pilot.hker_altQN' / 'goodSetN_A0clsQN' depend on axioms: [propext, Classical.choice, Quot.sound]
```

## 3. Statement check (ticket method (c)/(d))
Targets of this design ticket: the generic restatements (c) and the band recovery of the merged statements (d).
- **Site 1.** `ST_selfImprove_sectionG (Cm : Step2Data sz) (Fa : Step2Facts Cm) ...` (`T2326PilotStep2.lean:304`). `recovers_merged : type_of% @ST_selfImprove_section` (`:787`) proves the *exact* type of the merged theorem (`Step2Iterate.lean:284`) from the generic one at `bandStep2 sz z`, `bandStep2Facts sz z`, `bandStep2_martPin`; the `rfl` check above confirms the type. Hypotheses, quantifier order, the loss `(3C+1)`, `(·)^{1/5}`, `D`, `tt` are therefore the merged ones, not a variant.
- **Site 2.** All 14 public theorems of `QDriftA.lean:54-637` are covered: 11 by `recovers_* : type_of% @RBM.Ind.<merged>` (`T2326PilotQ.lean:787-825`), 3 band-free ones (`Qop_fastDecay`, `fastDecay_of_diamInf`, `QDriftA_W0_gt_one`) by unchanged copies whose types are `rfl`-equal to the merged ones (above). Several recoveries go through the constant sequence `fun _ => E` (merged statements take a real `E`); this is the merged type, checked by `type_of%`.
- Site choice: QDriftA is in the cone of `stStep3RegI_holds` (22 declarations reached, prove report B6); the (a) proposal to substitute `QtNonzeroFlow` was withdrawn in (a′) because that file is in the cone of `stStep3II_holds` only. Ticket rule followed.

## 4. Hidden hypotheses, vacuity, cycles
- The carrier facts are fields (`Step2Data`: 6 base facts; `Step2Facts`: the 7 lemma calls; `QDriftData`: 7 facts; `QKerData.ek4`). This is the design under measurement (route G), not a hidden hypothesis of a delivered theorem: every field is discharged at the band carriers by merged lemmas (`bandStep2` `:701-751`, `bandStep2Facts` `:754-777` = `ST_event_weak/init/lw/mg`, `ST_good_prob`, `ST_good_engine`, `ST_model_le_path`; `bandQ` `:761-780`; `bandKer` via `ekSumDecay2_holds`), so the recovered statements carry no extra hypothesis (they have the merged types exactly, §3). Carriers are inhabited (band instances compile), so the generic theorems are not vacuous.
- BA side: `baStep2` (`:867-903`) leaves 11 obligations as constructor arguments (`ev1-4`, `Good`, `ident`, `martTail`, `pLWT`, `pEMe`, `pNew`, `flowOK_m`); the pilot lists them as open BA work (pilot §4, §9). Nothing BA is claimed proved beyond `baLKM_eq` (rfl), `baLKM_meas`, `baFlow_T0_lt_one`.
- No cycle: probes import only merged modules; never imported themselves. No external hypothesis added.

## 5. Compiled nonempty instances
```
$ sed -n 801-809p RBM3D/Probe/T2326PilotStep2.lean   (compiled by the build of §2)
example (hLWT : STLWT 3) (hEMe : STEMn2Exp 3) (hnew : STNewKLKAt 3 (1 / 10) (1 / 10) 1 (1 / 10)) (hmart : STGridMartAt 3 1)
    (hDec : STDecay sz0 (STflowE z0) sInst) (hS1W : STStep1Weak sz0 (STflowE z0) sInst tInst)
    (hinv : STScaleInv sz0 (STflowE z0) sInst tInst (Kseq0 0)) :=
  ST_selfImprove_sectionG (bandStep2 sz0 z0) (bandStep2Facts sz0 z0) hLWT hEMe (by norm_num) ... flow_z0 hs0 htT
    (C := 1) (δ₀ := 1 / 10) (C₀ := 1) (𝔠d := 1 / 240) ... (conStInd_inst (by norm_num)) ... bdata_spec.1 ...
```
Same data and same remaining hypotheses (pins and the stochastic premises) as the merged instance `Step2Iterate.lean:1937-1948` (compared by `sed -n 1930,1950p`); d = 3, L_n = 4(n+1), `h3` at equality 4/240 = 1/60; every deterministic hypothesis discharged. Site 2: 7 `example`s (`T2326PilotQ.lean:834-874`) at `sz0`, `E0`, `s0`, `t0`, `K0`, `moll`, `sigma4`, `H1 ≠ 0` with no open hypotheses (targets 2, 3, 4a, 7a-7d). Targets 4b, 4c, 5a, 5b, 6a, 6b have no concrete-data example in the probe (observation O1).

## 6. The edited fraction g (re-run by the auditor)
```
$ sed -n 277,667p Step2Iterate.lean > am1; awk BEGIN/END-marker PilotStep2 > ag1; sed -n 54,637p QDriftA.lean > am2; awk ... PilotQ > ag2
$ wc -l am1.txt ag1.txt am2.txt ag2.txt
     391 am1.txt
     391 ag1.txt
     584 am2.txt
     497 ag2.txt
$ git diff --no-index --numstat am1.txt ag1.txt; git diff --no-index --numstat am2.txt ag2.txt
58	58	{am1.txt => ag1.txt}
90	177	{am2.txt => ag2.txt}
$ python3 -I S/ag.py am1.txt ag1.txt; python3 -I S/ag.py am2.txt ag2.txt   # auditor's own difflib script
merged 391 generic 391 equal 333 removed 58 added 58 cost 61 g_add=0.148 g_cost=0.156 g_changed_merged=0.148
merged 584 generic 497 equal 407 removed 177 added 90 cost 177 g_add=0.154 g_cost=0.303 g_changed_merged=0.303
```
Reproduces the prove report B5 and pilot §2 exactly (g₁ = 0.148, g₂ = 0.303, pair 235/975 = 0.241). Block boundaries checked: `Step2Iterate.lean:277` is the `variable` line before `set_option ... in` and the docstring of `:284`; `:667` closes the proof (`end Main` at `:669`); no private helpers of the theorem elsewhere in the file (`grep '^private'` on `:1-700`: none).

## 7. Cap arithmetic (re-computed)
```
$ python3 -c '<chain = (1-f)·90226·g + f·90226·0.8 + 15·245 + 167·15 + 15·100 + 43·60 + B>'
0.15 0.1 3800 33.5 G total 113.5 +KG 136.0
0.2 0.125 3800 38.9 G total 118.9 +KG 141.4
0.241 0.125 3800 42.1 G total 122.1 +KG 144.6
0.3 0.3 10000 60.9 G total 140.9 +KG 163.4
literal S*g+B (S=115.8k,B=3.8k): 0.148 20.9 tickets; total 105.9 +KG 128.4
literal S*g+B (S=115.8k,B=3.8k): 0.303 38.9 tickets; total 123.9 +KG 146.4
literal S*g+B (S=115.8k,B=3.8k): 0.241 31.7 tickets; total 116.7 +KG 139.2
$ grep -n '163\|174' docs/reports/T2325-portmap.md   →  :146 | **total** | **163 [128..214]** | **174 [141..223]** |
```
Pilot §5/§6 numbers reproduce (G 118.9 → 141.4 with K/G; I 185.5; T 196.5). One recommended BA cap is given: **165** (pilot §0, §8), with 200 if route G is not adopted. Frozen-signature list (167 by row) and timing (after ST-4..ST-6 close, supervisor O3) are in pilot §7.

## 8. Paper deltas
The probes state no new mathematics: every generic statement specialises to the merged statement (compiled `type_of%` recoveries). No Lean/paper difference is introduced; "none" in prove report (d) is correct.

## 9. Observations (no RETURN)
- O1. Site-2 targets 4b, 4c, 5a, 5b, 6a, 6b have no concrete-data `example` in the probe. Not a defect for this ticket: each has a compiled `recovers_*` of the *exact* merged type (4b, 4c also `hker_altQN`/`alt_hkerQN` over `bandKer`), so every merged instance at `QDriftA.lean:711-1337` is an instance of the recovered statement; the probe is never merged and the ticket's acceptance asks for the band-instance examples (step (d)), which compile.
- O2. The ticket's formula "S × g + B" is replaced in the pilot by a refined model (instance sections excluded, semantic share at twin rate 0.8, carrier/wrapper/BA-wiring overhead). The literal formula gives 20.9-38.9 chain tickets (above), at or below the pilot's central 38.9; the pilot is the more conservative of the two. The overhead terms are assumptions A1-A2 (stated as such, pilot §9).
- O3. `g` counts the 87 lines of site 2 that move unchanged into the band instance as removed; the "changed or added only" reading (ticket wording) gives 0.154; both are printed (pilot §2).
- O4. The calibrated chain g = 0.20 rests on two points (pilot §9 says so); the tripwire in pilot §8 (2) is the dispatcher's to adopt.
- O5. Pilot §0 cites DECISIONS §144 (no BA cap); the cap is delivered as a planning figure, as the ticket requests.

## 10. Verdict
| target | verdict |
|---|---|
| Site 1: `ST_selfImprove_sectionG` + `recovers_merged` + d = 3 example | PASS |
| Site 2: QDriftA:54-637 generic block, 11 `recovers_*`, 3 unchanged copies, 7 examples | PASS |
| g by script (0.148 / 0.303), route totals G/I/T, one cap (165), frozen list, timing | PASS |

**Ticket T2326: PASS.** Report-only; no dispatcher sign-off needed for the merge (the route/cap recommendation is input to the dispatcher by design).
