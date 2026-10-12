Auditor model: claude-opus-5-5

# T2454 1a-audit round 2 (design gate): resubmission (a‴) of `docs/reports/T2454-prove.md`

Written Mon Oct 12 15:22 UTC 2026 (`date -u` at the last run: Mon Oct 12 15:22:19 UTC 2026). This overwrites the round-1 1a-audit (RETURN, sign-off; answered by CONTROL H248 (2)).
Own detached worktree `../RBM3D-wt/T2454-1a-audit2` at `t/T2454` = `e949c71` (probe unchanged; main `1debc23`). Scratch `<scratchpad>/T2454/aud2/` (copies of the prover's `v2/*.py`, re-pointed to this worktree, plus `cone.py`).

## 1. Probe, check file, pinned bodies (unchanged inputs, recompiled)

```
$ git diff --stat main...HEAD
 RBM3D/Probe/T2454Pins.lean | 397 +++++++++++++++++++++++++++++++++++++++++++++
$ date -u; lake env lean RBM3D/Probe/T2454Pins.lean > probe.out 2>&1; echo exit=$?; date -u
Mon Oct 12 15:20:18 UTC 2026
exit=0
Mon Oct 12 15:20:25 UTC 2026
$ wc -l < probe.out; grep -ci "error\|warning" probe.out; grep -c "" T2454Pins.lean; grep -cE "sorry|admit|native_decide|^axiom" T2454Pins.lean
28 / 0 / 397 / 0
$ lake env lean check.lean   # docs/tickets/checks/T2454-check.lean (551fa94)
check-exit=0   errors: 0
$ lake env lean rfl.lean     # probe :1-394 + check bodies chkU, chkK; lines 405-407:
#   STDecayLoopUgL C μ s t ↔ chkU C μ s t := Iff.rfl ;  STKcalDecaygL C ↔ chkK C := Iff.rfl ;  twSteps … → chkU … := fun h => h.2.2.2
rfl-exit=0   errors: 0
```

## 2. Numerics of (a) (i)-(ii), rerun

```
$ python3 -I inst.py ; python3 -I ext.py      # rc=0, rc=0; inst output identical to the prover's script run
Admissible(1/6,1/10) at sz0: N^c<=W : ln(N^(1/6))-lnW = 2.426 - 3.466 (y=2: worst case y=2)
WO lower: -(d/2-dd)lnW = -4.852 <= ln lam = -4.159 ; ln lam <= ln(1/dd)=2.303
lam^2 W^d >= W^{2dd}: 2.079 >= 0.693
…
STGdecayWgL rhs at far pair (dist=y, ell<=1): exp(-sqrt y)<=W^-33=y^-165 iff y>=6.73e+06; below that the exp term dominates the floor
STKcalDecaygL at tau=1/10: premise needs dist>=W^(1/10)=y^(1/2); max dist L/2=y: slack factor y^(1/2) (y=1e6: 1000)
```
Same as round 1 (§2 there); (a)-(a″) are unchanged by (a‴). The large thresholds are `∀ᶠ n` thresholds as in the band, not witnesses.

## 3. Item 1 (vii): central lines per file and in total; the 1,950 rule

```
$ python3 -I central.py > central.mine; diff central.mine ../v2/central.out && echo identical
identical
wrap factor probe/Step2Gen chars per line = 1.355
  DecayGen            820 = header 40 + pins[p] 60 + stmts4-6[p] 20 + bridges[p] 45 + proofs4-6[b] 622 + inst4-6[p] 33
  DecayGenTw           63 = header 30 + TLF-C5[p] 14 + BAward+BAinst6[p] 19
  Step2EventsGen     1038 = header 40 + pins[p] 89 + stmts8-11[p] 103 + bridges[p] 16 + proofs8-11[b] 458 + helpers[b] 179 + EGt=LWE[b] 26 + F7[b] 14 + goodAt+readings[e] 45 + cstar+impos[e] 7 + inst10[p] 16 + inst8-9[b] 45
  Step2EventsGenTw*    58 = header 25 + BAgrid+BAflow+Rot3[p] 22 + inst11[p] 11
SPLIT (4 files): T7a = DecayGen + DecayGenTw + 3 registry lines = 886;  T7b = Step2EventsGen + Step2EventsGenTw* + 5 registry lines = 1101
UNSPLIT layout (A) … DecayGen 820  Step2EventsGen 1038  DecayGenTw 96  + Test/Axioms.lean 8  = CENTRAL 1962
  sensitivity: low 1727 …; high 2102 …
  shared pointwise lemma: NOT used in the central figure (no probe statement; saving at most 118 lines, T7a only)
  stop rule (central > 1950 -> split): 1962 > 1950 is True; per file < 2000: True
$ python3 -I overlap.py
DecayLoopA_main nonblank lines: 214  DecayLoopB_main_u nonblank lines: 243  common lines (LCS, names normalised): 133
```
Script read (`central.py`): band bodies are measured from `Induction/DecayLoopA/B`, `Step2Events`, `Step2Core` declarations by name (26 names); probe parts are probe blocks x 1.355; three items are marked ESTIMATE (45 + 7 lines). It counts instances (targets 4-6, 8-11, 13), helper copies of item 3, headers and 8 registry lines, as round-1 item 1 required. Arithmetic checked: 820 + 1038 + (63 + 58 − 25) + 8 = 1962; 820 + 63 + 3 = 886; 1038 + 58 + 5 = 1101.
**Split confirmed** (H248 (2), pre-signed): the committed central 1,962 exceeds 1,950, so T7a/T7b at the file boundary. **T7a** = `Chain/DecayGen` (targets 1-6) + the decay part of `Chain/DecayGenTw` (target 12, target-13 BA instance of target 6) + 3 registry lines, 886 predicted lines; the 1b does T7a only. Every file is far below 2,000.

## 4. Item 2 (i): layout (A), imports, reverse cones, BA-side facts

```
$ python3 -I layout.py      # vs ../v2/layout.out: differences only in the print order of Python sets/dicts (same members)
  DecayGen             0 identifiers; modules: {}
  Step2EventsGen       0 identifiers; modules: {}
  DecayGenTw          12 identifiers; modules: {'RBM3D.BA.FlowPins': 7, 'RBM3D.BA.Step2BA': 1, 'RBM3D.BA.EMn2BA': 3, 'RBM3D.BA.TwistPins': 1}
LAYOUT (A) split T7a = DecayGen + DecayGenTw, T7b = Step2EventsGen + Step2EventsGenTw (4th file)
  Chain.DecayGen: imports ['Induction.DecayLoopB', 'Chain.Step2Gen']; closure 86 modules, BA modules in it 0; importers ['Chain.DecayGenTw']; …
  Chain.DecayGenTw: imports ['Chain.DecayGen', 'BA.TwistPins', 'BA.Step2BA', 'BA.EMn2BA']; closure 273 modules, BA modules in it 29; importers []; …
EMn2BA: reverse cone on main (modules that import it, directly or not): 16 ; none of them is a new module; …
$ python3 -I cone.py        # auditor's own script over the `import RBM3D.` lines of main
DecayGen closure 86 BA modules: []
Step2EventsGen closure 74 BA modules: []
EMn2BA in cone of TwistPins+Step2BA: False
modules importing RBM3D.Chain.DecayGen/Step2EventsGen/DecayGenTw on main: []
loopFine module RBM3D.Loop.GLoopFlow in Step2EventsGen closure: True
$ python3 -I names.py       # identical to ../v2/names.out
DecayGen: 15 public names; occurrences on main outside Probe/: none
Step2EventsGen: 37 public names; occurrences on main outside Probe/: none
DecayGenTw: 4 public names; occurrences on main outside Probe/: none
```
Layout is stated with imports, predicted lines and reverse cones; the BA-side facts go in the leaf `DecayGenTw` with `import RBM3D.BA.EMn2BA`, and it stays a leaf (no importer; `EMn2BA` is not already in its cone, so the import is needed). `DecayGen` has no `BA/` module in its closure. The T7a BA instance of target 6 (probe :384) uses `EMn2BA_mF_data`, `EMn2BA_T0_lt_one`, `baFM_WardPair` directly, not `baFlow_facts` (read at probe :384-388), so T7a's `DecayGenTw` is complete without the events part. Public helpers take the file-stem prefix (`DecayGen_band*`, `DecayGenTw_ba*`, `Step2EventsGen_*`); pinned names stay. Met.

## 5. Item 3 (vi): the 51 declarations read by T1

```
$ python3 -I readers2.py    # identical to ../v2/readers2.out
51 public declarations of Step2Events+Step2Core read by Step2Iterate/OptL2a/OptL2b …
(A) 30 model-free, reused: … (B) generic form here: targets 8-11 (STScaleInv, ST_event_*, ST_good_prob, STGoodAt, STBdata, STLWT_of_LWtermExp),
   helpers ST_grid_whp_of_sections, ST_grid_whp_zero, ST_prec_mono_eventually, ST_prec_of_le_ev, ST_prec_sup, ST_sections_of_PT, ST_PT_of_sections, ST_model_le_path  =>  Step2EventsGen_<stem>
   spectral (F3): ST_cstar_le, ST_flow_im_pos, ST_mE_im_ge  =>  Step2EventsGen_cstar_le; projection / band reading of DecayGen_Spec
(C) ST_good_engine <-Step2Iterate: NOT copied here: target P4 of T1 (T2452-design.md:184 …)
(D) unclassified: []  total 51
$ sed -n 184p docs/reports/T2452-design.md   (merged 6bdc5a3)
| P4 | generic `ST_good_engine` (`mI`, the `hNew` instance as hypotheses) | `Step2Core:997` | additive restatement | 280 / 330 / 420 | read at `Step2Iterate:609` | T | target of T1 (ST side) |
```
Each of the 51 has a decision; the six named in round-1 item 3 are decided explicitly (`ST_good_engine` → T1 P4 per the merged U-D census, T7 supplies its hypothesis `STGoodAtg`); the copied ones are in item 1's count (`helpers[b] 179`, `cstar+impos[e] 7`). Met. (All in T7b after the split.)

## 6. Item 4: explicit premises; one `owedProps` list

```
$ sed -n 213-218p RBM3D/Probe/T2454Pins.lean   # S2EvGen_Sect: 8 conjuncts
  (∀ n, 0 ≤ s n) ∧ (∀ n, t n ≤ T0z n) ∧ STStep1WeakgL C μ s t ∧ 0 < cB ∧ 0 < c ∧ (∀ᶠ … Bctl bounds) ∧ (∀ᶠ … Kf cap) ∧ STScaleInvgL C μ s t Kf
$ python3 -I registry.py    # identical to ../v2/registry.out
owedProps lines to add: 8: ['STKcalDecaygL', 'STScaleInvgL', 'STGoodAtg', 'STStep2DecayPTgL', 'STGdecayWgL', 'STDecaygL', 'LWtermG', 'LWtermExpG']
STStep1WeakgL    | RBM3D/Chain/Carrier.lean:184 | line 146 | targets 8, 9 (explicit premise) | S1/BA chain
$ sed -n 425-446p RBM3D/Test/Axioms.lean   # scanPremises: Prop defs in theorem binders, minus those some theorem concludes; :518 throws on unregistered
```
Removing the two pins leaves 6 deterministic conjuncts, as (a‴) says; `STScaleInvgL`, `STStep1WeakgL` become explicit binders, so the scan sees them. One list, owner per line; T7a adds `STKcalDecaygL`, `STStep2DecayPTgL`, `STGdecayWgL`. T7a premises `DecayGen_Spec`, `DecayGen_WardPair` are concluded by the band theorems (`bandFM_Spec`, `bandFM_WardPair` → `DecayGen_band*`) and leave the scan. Met.

## 7. H248 (2) decisions and stop lines

| decision / stop line | finding |
|---|---|
| BA facts in leaf `DecayGenTw` + `import RBM3D.BA.EMn2BA` | met (§4) |
| F7 (`S2EvGen_Rot3` at BA) by the 1b, trace cyclicity, or T1-BA past 150 lines | proved generically as `Step2EventsGen_loopFine_rot3` (band `STB_trace_six`+`STB_loop_rot`, 14 lines; `loopFine` is in `Loop/GLoopFlow`, inside `Step2EventsGen`'s closure, no BA import); BA/band F7 are corollaries. In T7b after the split; T7a needs no F7 (only target 11 uses it) |
| central > 1,950 → split T7a/T7b, confirm at round 2 | 1,962 → **split confirmed**; 1b = T7a |
| file-stem prefix or private for public helpers | met (§4 `names.py`, 0 clashes) |
| 2,000 lines per file | max 1,038 (T7b), T7a max 820 |
| new `FlowFM`/`Step2Mat` field | none (F1-F9 are `Prop` predicates/hypotheses; unchanged probe) |
| forbidden items in generic statements | none (round-1 `hyprules.py`, probe unchanged) |
| carrier fact without BA source or owner | none: F3, F4 proved at BA in T7a; F5 U2-BA; Step 2 decay T1/T1-BA |
| TLF-C5 `Iff.rfl` | holds (§1) |

## 8. Verdict per round-1 item

| round-1 item | verdict |
|---|---|
| 1 (vii) central per file and total, script | met; split applies and is confirmed |
| 2 (i) layout, imports, reverse cones, BA facts | met |
| 3 (vi) the 51 declarations | met |
| 4 registry: explicit premises, one list | met |
| 5 dispatcher sign-off | answered by H248 (2) |

Paper-delta coverage: candidates `T2454a`-`d` (F4/F7 explicit, F9 explicit, `|E| ≤ 2 − κ` → `DecayGen_Spec`, target 5/6 premise changes) are unchanged and cover the Lean/band differences; (a‴) introduces no new statement difference.

Observations (no RETURN; for the dispatcher's T7b ticket and notice REQ):
- O1. H248 names T7b = `Step2EventsGen` (and, by "the decay part of `DecayGenTw`", the events part of `DecayGenTw`). (a‴) instead proposes a 4th leaf `Chain/Step2EventsGenTw.lean` and calls it "needed". It is not needed: T7b could add `import RBM3D.Chain.Step2EventsGen` and the events part to the leaf `DecayGenTw` after T7a merges. Either form keeps the layering. The T7b ticket decides. T7a is not affected.
- O2. T7b: if `Step2EventsGen_Sect` (6 deterministic conjuncts) stays a `Prop` def premise of public theorems and no theorem concludes it, `scanPremises` reports it as unregistered (`Test/Axioms.lean:518`). It is not in the 8-line list. Unbundle it into binders, or classify it.
- O3. The central figure is a bound with a 12-line margin (sensitivity 1,727-2,102). The rule was applied as written.
- O4. H248 places F7 in `DecayGenTw`; (a‴) places it generically in `Step2EventsGen`. The generic placement is stronger and allowed by the layering, and it lands in T7b.
- T7a 1b scope: sole writable files `Chain/DecayGen.lean`, `Chain/DecayGenTw.lean` (imports `Chain.DecayGen`, `BA.TwistPins`, `BA.Step2BA`, `BA.EMn2BA` only), `RBM3D.lean`, `Test/Axioms.lean` (3 lines). No `Step2EventsGen`. Target 7 stays with U2 (no `Chain/Step34Gen` on main).

## 9. Verdict: PASS (T7a; split T7a/T7b confirmed)

Every stage-1a deliverable is met, and round-1 items 1-4 are answered with reproducible script output. No binding stop line is hit except the 1,950 split rule, which applies and is executed as pre-signed in H248 (2). No further sign-off is requested. The 1b (`prover-hard`) does T7a only. The dispatcher files T7b and the non-blocking notice REQ (O1, O2 are inputs to that ticket).
