Auditor model: claude-opus-5-5
# T2443 1a-audit (design gate) — Mon Oct 12 08:50:49 UTC 2026

Inputs: ticket `docs/tickets/T2443.md`, check file `docs/tickets/checks/T2443-check.lean`, section (a) and (a″) of `docs/reports/T2443-prove.md`,
branch `t/T2443` = 6b5ad59 (probe only). Audit worktree: `../RBM3D-wt/T2443-1a-audit` (detached at 6b5ad59; build cache cloned from main; main = 458ec8c,
Lean tree of main = branch base c43bdf1 per (a″)). Scratch: `scratchpad/T2443/aud_*`.

## 1. Probe recompile, hygiene, diff
```
$ cd ../RBM3D-wt/T2443-1a-audit && lake env lean RBM3D/Probe/T2443Pins.lean; echo "exit: $?"     (08:45:45 -> 08:45:58 UTC)
exit: 0
... (19 #check lines identical to (a″)) ...
theorems of this file: 16; outside the standard axioms: []; unregistered unproved premises in RBM.Graph: []
$ wc -l < RBM3D/Probe/T2443Pins.lean            -> 393          (ticket limit 400)
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^ *axiom " RBM3D/Probe/T2443Pins.lean; echo $?   -> 1
$ git diff --stat main...t/T2443
 RBM3D/Probe/T2443Pins.lean | 393 +++++++++++++++++++++++++++++++++++++++++++++
```

## 2. Statements: check file vs probe, checked by Lean (not only text)
`aud_eq.lean` = probe lines 1-355 + the check file's Part 2 `T2443_*` defs verbatim + the equalities below; compiled in the audit worktree.
```
example : T2443_FrameT = BAFrameStepTN := rfl          example : T2443_LocStepT = BALocStepT := rfl
example : T2443_Untag ↔ (∀ P L, untag BALocStepT P L ↔ P.g.Normal ∧ BALocStep P L) := Iff.rfl
example : T2443_Bridge = BABridge := rfl                example : T2443_EquivCost = BAEquivCost := rfl
example : T2443_CostTwist = BACostTwist := rfl          example : T2443_SimC = BASimC' := rfl
example : T2443_ShapeTwist ↔ (∀ sh, BAShapeLL sh BAFrameStepTN → BAShapeLL sh BALocStepT) := Iff.rfl
example : T2443_Final = BAFinalS := rfl
example : T2443_Untag := baUntag_locStepT               example : T2443_Bridge := baBridge_holds
example : T2443_EquivCost := baEquivCost_holds          example : T2443_CostTwist := baCostTwist_holds
example : T2443_ShapeTwist := baShapeLL_twist           example (m : ℂ) : T2443_SimC m T2443_LocStepT := baSimC'_holds m
example : T2443_StepOfSimC := baStep_of_simC'           example (R) : T2443_Final R := baFinalS_holds R
example : T2443_OrdGe := ba_ord_ge_of_simC'
example : BALocReg6 → T2443_LocReg6 := fun h p P0 h0 _ hX => h p P0 h0 hX
$ lake env lean scratchpad/T2443/aud_eq.lean; echo "exit: $?"
'RBM.Graph.baLocReg6_of_shapes' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.ba_ord_ge_of_simC'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baSimC'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baFinalS_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baReach_bReach' depends on axioms: [propext, Classical.choice, Quot.sound]
exit: 0
```
Result: eleven of twelve pins are definitionally the check file's (by `rfl`), and the probe's theorems prove exactly the check-file
Props. The twelfth, `BALocReg6`, drops the frame-normality hypothesis; it implies `T2443_LocReg6` (last line, compiled). It is stronger,
which the ticket allows ("the probe's text binds and the report diffs it"). The diff is reported in (a″) finding 1 and rerun here:
```
$ python3 -I scratchpad/T2443/diffstmts2.py | head -3
11 of 12 statements IDENTICAL (name substitution, whitespace normalised): FrameT->BAFrameStepTN, ... OrdGe->ba_ord_ge_of_simC'
T2443_LocReg6 -> BALocReg6: DIFFERENT
    --- check
```
`BASimC'` matches `T2423-prove.md:240-242` (the pseudo-Lean, with `∃ L' : List (PGraph (Fin 2))` typed). `BAFinalS` equals the merged `BAFinal`
(`BAScost.lean:126-129`) with `P.g.LocStd` in place of `locStdA P.g`. `BAFrameStepTN`/`BALocStepT` are `def`s (no new inductive, so no registry line).

## 3. Premise scan under `import RBM3D` (the ticket's pre-check, run early)
`aud_full.lean` = `import RBM3D` + probe lines 21-357 + `#assert_rbm_axioms`; `Test/Axioms.lean` unchanged.
```
$ lake env lean scratchpad/T2443/aud_full.lean > aud_full.out 2>&1; echo "exit $?"; grep -c error aud_full.out
exit 0
0
```
The probe's own control (`ctrl1.lean`, (a″)) shows that `baUntag_locStepT_intro` and `baInit_locReg6InvA` are the provers that clear
`untag` and `locReg6InvA`. `BANormal` is concluded by `baNormal_locStepT`, `BASimC'` by `baSimC'_holds`, `BAFinalS` by `baFinalS_holds`, `BALocReg6`
by `baLocReg6_of_shapes`.

## 4. Numerics and greps of section (a), rerun
```
$ python3 -I scratchpad/T2443/inst.py            (exit 0; output identical to (a)(ii))
target 3 (twist): scostA equal at all 15 setoids >= atoms; far-min/all-min P: 1 1  twist: 1 1
target 2 (bridge) P_B      : image has 2 ext + 2 int vertices; scost(img,q)=scostA(comap q) at all 15 setoids; min all/far: 1/1 (A) = 1/1 (img)
p=2: 16 start terms; all satisfy locReg6InvA 2 (min all >= 4, min far >= 6): True; ...
LocStd graph: LocStd = True  atoms [0, 1, 2, 3, 3]  ord = 8  cost at trivial merge (atoms) = 8  min_all = 8  min_far = 8  ext atoms distinct: True
$ python3 -I scratchpad/T2443/grepnames2.py      (identical to (a″): 0 declarations of the new names on main, t/T2433-5, t/T2441, t/T2442)
$ for r in main t/T2433 t/T2434 t/T2435 t/T2441 t/T2442; do git grep -nE "^\s*(private |...)*(def|theorem|...) (<22 probe names incl. LTB|LTC|stepB|stepC|pL>)\b" $r -- RBM3D | grep -v Probe/ | wc -l; done
main: 0   t/T2433: 0   t/T2434: 0   t/T2435: 0   t/T2441: 0   t/T2442: 0
```

## 5. Stage-1a deliverables
| item | evidence | status |
|---|---|---|
| (i) `BAMatchTw` | `git grep BAMatchTw main -- RBM3D` -> `BALvl1A.lean:42`, `BASim.lean:16` (docstrings only); T2442 ticket :16 "Not here"; T2423 Amend 1 :3 allows the drop when there is no consumer; target 3 proved (`baCostTwist_holds`), so the default route stands | met: dropped |
| (ii) bridge route, `BAEquivC` transfer | `baBridge_holds`, `baEquivCost_holds` compiled (§2) | met |
| (iii) final step | `baFinalS_holds` compiled. The half-edge table is not needed because `locReg6_of_locCostGe` handles `#elem = 0`. The distinct-externals lemma is the inline `hext` (probe :236-242) | met |
| (iv) O2 priced | 17 builder shapes plus two stage-2 implications; analog sizes rechecked: `BAScostLL_S1` :836-904 (69), `macroA` :1057-1132 (76), `lanlwT1` :1140-1219 (80), `macroB` :1237-1290 (54) | met (see §6) |
| (v) size, boundary | predicted ~1,020 in `BAStepS.lean` (< 1,700); `BAStepS2` not written; boundary after `baStep_of_simC'`; probe: proof items in 214 lines | met |
| (vi) probe | texts diffed (§2), `baStep_of_simC'` and `ba_ord_ge_of_simC'` proved, names grepped (§4) | met |
| premise provers | listed in (a); compiled (§3) | met |

Stop lines: probe 393 ≤ 400; predicted file ≤ 1,700 < 2,000 (binding); `BAStepS2` not triggered. No stop line is hit.

## 6. O2 decision (the ticket's rule, applied at this gate)
The ticket's rule: "in this row if ≤ 400 lines, else a new row". The price in (a)(iv) is about 1,200-1,600 lines. A floor from the measured analogs
is already above 400: 8 builder terms × 54 lines = 432, before the stage-2 implications. **Decision: the O2 inputs stay hypotheses of the closed form**
(`∀ sh ∈ {e2, macroA, macroB}, BAShapeLL sh BAFrameStepTN` in `BALocReg6`, as in the probe). The dispatcher opens one more row for them (stage L 50
-> 51). This follows the ticket's pre-stated rule, so it needs no sign-off. It is a dispatcher follow-up.

## 7. Target-5 closures not in the probe (route checked by reading signatures, as the probe step does not require them)
- `s1`: `grep -n "\.s1\b\|BAShape.s1" RBM3D/Graph/BASim*.lean` prints nothing. The tags are `tagStd` (`e2`/`band`), `tagT1` (`e1`/`band`) and the constants
  `macroA`/`macroB` (`BASim.lean:113-136`). So `BAShapeLL s1 BAFrameStepTN` is vacuous.
- `e1`: only `P.outsT P.g.tagT1 [lanlwT1 P.g p]` in `edge` and `ggSplit` carries it. `outsT`'s entry `{E' := Q.E', ext := Q.ext ∘ P.ext, g := Q.g}`
  with `Q = T'.packMerge` is definitionally `BAScost_pack P Q0` (`BAScost.lean:670-675`), with `Q0 ∈ partition = splitG.map packMerge` (`BAVocab:229-231`).
  `hp` and `σ ∧ circ` come from the constructors, which matches the hypothesis of `baShapeLL_e1` (`BAScost2.lean:82-85`).

## 8. Instances in the probe (target 8)
Targets 1 and 4 are instantiated at the `(true,true)` twists of `baPG baPB` (`within`) and `baPG baPC` (`ggSplit`, j = 0). The steps are `stepB` and `stepC`.
The tags are checked by `decide +kernel`, and `untag` is shown equal to R1's `locStepB/C`. Target 2/3 are instantiated at `baPG baPB`. Target 6 is
instantiated at `pL`: `LocStd`, `scalingOrder = 8` and distinct external atoms are all proved by `decide`. Target 7 is instantiated at `p = 2`, where
`partition ≠ []` is proved by `decide`. Its hypotheses `hs1`, `he1` (1b) and `hX` (O2) are kept. All are nondegenerate and compiled.

## 9. Observations (no RETURN)
- O1. The probe's instance names `LTB`, `LTC`, `stepB`, `stepC`, `pL` are public in `RBM.Graph`. In `BAStepS.lean` they must be `private` or carry the
  stem `BAStepS_` (CLAUDE.md §3 (E)).
- O2. Dispatcher information: the closed form needs no frame normality (`baNormal_locStepT`, unconditional). So the dispatcher note "L3d2/L3d3
  discharge it with T2442's `BAstepMono`" is no longer needed for this row. The extra `BAstepMono` corollary becomes moot.
- O3. The 1b's `baLocReg6_of_shapes` must close `hs1` and `he1` (§7). The hypothesis-free corollary waits on the O2 row. Until then `BALocReg6` is
  conditional on open inputs whose satisfiability is that row's question. 1b should state this as a special-case caveat (CLAUDE.md §5.6).
- O4. (a)(ii) is a Python model rather than Lean. The probe's Lean instances (§8) supersede it.
- O5. Paper-delta candidates (`BAFinalS` at atom-level `LocStd`, the per-output `BASimC'`, the O2 hypotheses) are 1b report items. They are not 1a deliverables.

## Verdict
Design gate: **PASS**. Every stage-1a deliverable (i)-(vi) and the premise-scan list is met. No binding stop line is hit. The only statement change is
`BALocReg6` without frame normality; it is stronger, compiled, and reported. O2 decision: keep as hypotheses and open a new row (the ticket's rule).
No dispatcher sign-off is required for 1b to start.
