Auditor model: claude-opus-5-5
# T2443 audit, round 1 (BA-L L3b4' `Graph/BAStepS`) — Mon Oct 12 09:15:11 UTC 2026

Branch `t/T2443` at `e9528ea` (merge base `c43bdf1`); audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2443-audit1` (detached). Main at `ff2c7a5`.
Scratch files: `<scratchpad>/T2443/AuditCheck.lean`, `AuditAll.lean`.

## 1. Diff and hygiene
```
$ git diff --name-status main...t/T2443
A	RBM3D/Graph/BAStepS.lean
A	RBM3D/Probe/T2443Pins.lean
$ git show t/T2443:RBM3D/Graph/BAStepS.lean | grep -cE "\bsorry\b|\badmit\b|native_decide|^ *axiom "
0
```
Both files are sole writable files. `RBM3D/Probe/T2443Pins.lean` is the probe (never merged): the hub must bring in only `RBM3D/Graph/BAStepS.lean` (+ root import). `RBM3D.lean`, `Test/Axioms.lean` untouched; no frozen signature touched (new file only). `BAStepS2.lean` not written (523 lines < 1,700).

Public names of `BAStepS.lean` (24) and declarations of them on other refs (excluding `Probe/`):
```
$ git show t/T2443:RBM3D/Graph/BAStepS.lean | grep -nE "^(theorem|def) " | awk '{print $1,$2}'
64:def BAFrameStepTN  67:def BALocStepT  72:def BABridge  76:def BAEquivCost  80:def BACostTwist  84:def BASimC'  91:def BAFinalS  98:def BALocReg6
107:theorem baUntag_locStepT  129:theorem baNormal_locStepT  137:theorem baUntag_locStepT_intro  141:theorem baInit_locReg6InvA
160:theorem baBridge_holds  186:theorem baEquivCost_holds  225:theorem baCostTwist_holds  232:theorem baShapeLL_twist  244:theorem baSimC'_holds
258:theorem baStep_of_simC'  353:theorem baShapeLL_s1_tn  358:theorem baShapeLL_e1_tn  368:theorem baFinalS_holds  389:theorem ba_ord_ge_of_simC'
403:theorem baReach_bReach  413:theorem baLocReg6_reach
$ for r in main t/T2433 t/T2434 t/T2441; do git grep -nE '^(theorem|def|lemma|abbrev) (<the 24 names>)\b' $r -- RBM3D | grep -v Probe/ | wc -l; done
main: 0   t/T2433: 0   t/T2434: 0   t/T2441: 0
```
(output lines joined; all helpers are `private` with stem `BAStepS_`.)

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Graph.BAStepS
✔ [3825/3825] Built RBM3D.Graph.BAStepS (8.6s)
Build completed successfully (3825 jobs).
$ lake build RBM3D 2>&1 | grep -E "^error|Build completed" | tail -3
Build completed successfully (4264 jobs).
$ printf 'import RBM3D\nimport RBM3D.Graph.BAStepS\n#assert_rbm_axioms\n' > AuditAll.lean; lake env lean AuditAll.lean > all.out; echo "exit $?"
exit 0
$ grep -nE "error|axiom audit|unregistered" all.out
1:axiom audit: 12938 theorems, 4063 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ # AuditCheck.lean: #print axioms of the 16 public theorems
  16 [propext, Classical.choice, Quot.sound]
```
The premise scan of `#assert_rbm_axioms` passes with `BAStepS` imported and `Test/Axioms.lean` unchanged (premise provers present: `baUntag_locStepT_intro`, `baNormal_locStepT`, `baInit_locReg6InvA`, `baSimC'_holds`, `baFinalS_holds`, `baStep_of_simC'`, `baLocReg6_reach`). No recursive inductive added.

## 3. Statements against the ticket's pins (compiled)
`AuditCheck.lean` = `import RBM3D.Graph.BAStepS` + Part 2 of `docs/tickets/checks/T2443-check.lean` verbatim (the `T2443_*` defs) + the lines below. It compiles with no error and no warning line (the only output is the `#check`s and `#print axioms` lines):
```
example : BAFrameStepTN = T2443_FrameT := rfl
example : BALocStepT = T2443_LocStepT := rfl
example : T2443_Untag := baUntag_locStepT
example : BABridge = T2443_Bridge := rfl
example : BAEquivCost = T2443_EquivCost := rfl
example : BACostTwist = T2443_CostTwist := rfl
example : T2443_ShapeTwist := baShapeLL_twist
example : BASimC' = T2443_SimC := rfl
example : T2443_StepOfSimC := baStep_of_simC'
example : BAFinalS = T2443_Final := rfl
example : T2443_OrdGe := ba_ord_ge_of_simC'
example : BALocReg6 → T2443_LocReg6 := fun h p P0 h0 _ hX => h p P0 h0 hX
example : T2443_LocReg6 := fun p P0 h0 _ hX => baLocReg6_reach p P0 h0 hX
example : ∀ m : ℂ, T2443_SimC m T2443_LocStepT := baSimC'_holds
example : BAShapeLL BAShape.s1 T2443_FrameT ∧ BAShapeLL BAShape.e1 T2443_FrameT := ⟨baShapeLL_s1_tn, baShapeLL_e1_tn⟩
example : ∀ R : BAPGraph (Fin 2) → Prop, T2443_Final R := baFinalS_holds
```
Result: 11 of 12 pins are definitionally equal to the check file (`rfl`) or have exactly its type. The twelfth, `BALocReg6`, drops the check file's frame-normality hypothesis `(∀ P outs, BAFrameStep P outs → P.g.Normal → ∀ Q ∈ outs, Q.g.Normal)`. It is **stronger**, and it implies `T2443_LocReg6` (compiled above). The hypothesis is redundant because `baNormal_locStepT : BANormal (untag BALocStepT)` has no hypothesis: every `BAFrameStepT` output is an `outsT` element of a partition (`BAGraph.partition_normal`), and twisting back keeps normality (`ba_twist_inv_out`). The probe's text binds (ticket "Targets"); the 1a-audit recorded this change (§2), and the prove report reports it as `T2443c`.

Ticket targets vs mathematics:
- T1: `BALocStepT` is normal at `P`, has a `BAFrameStepT` at `P.twist c t`, and twists the outputs back with tags kept. `untag ↔ Normal ∧ BALocStep` holds in both directions. PASS.
- T2: `BABridge` is an iff for all `P far k`. `BAEquivCost` is an iff along `BAEquivC`. No `CircIffLoop`/normality hypothesis. PASS.
- T3: iff for all `c t P far k`. `baShapeLL_twist` holds for every `sh`. PASS.
- T4: `BASimC'` is per output (`L'` per `band` output, `P'` per step), as pinned (`T2423-prove.md:240-242`). `baSimC'_holds` holds for every `m`. The literal `BASimC` is excluded by the ticket. PASS.
- T5: `baStep_of_simC'` holds for general `T`. `s1` and `e1` are closed unconditionally for `BAFrameStepTN`. PASS.
- T6: `BAFinalS` reads `P.g.LocStd` (atom-level), as L4-C3 asks; `baFinalS_holds` holds for every `R`. PASS.
- T7: `ba_ord_ge_of_simC'` is identical to the pin. In the closed form `baLocReg6_reach`, the only hypotheses are the start term and the O2 shape inputs `e2`, `macroA`, `macroB` (decided at the 1a-audit §6 by the ticket's ≤ 400-line rule; priced ≈ 1,200-1,600 lines). The quantifier order `p, P0, hP0, hX, K, Q` follows the pin. The thresholds `2p` (all) and `3p` (far, distinct external atoms) are unchanged from the merged `locReg6InvA`. PASS.

## 4. Vacuity, hidden hypotheses, cycles
- The pins are plain `def`s over merged `Prop`s (`locCostGeA`, `BAShapeLL`, `BAStep`, `BANormal`, `untag`, `BReach` = `ReflTransGen`, `BAScost:65-154`). No structure fields carry hypotheses.
- Dependencies are merged modules only (imports `BASim`, `BASim3`, `BALvl1A`, `BAScost`, `BAScost2`, `BAAtomic`, `BAVocab`, `BASymm1/2`, `LocalRegular*`, `LWLvl1`, `LWSymm`). No dependency on the probe. No cycle.
- The remaining hypothesis of `BALocReg6` / `hX` is `BAShapeLL sh BAFrameStepTN` for `sh ∈ {e2, macroA, macroB}`. It is an open combinatorial pin of a future row (T2426 audit O2), not an analytic external input, so no limit check applies. The merged tools `baShapeLL_e2/macroA/macroB` (`BAScost2:52-127`) reduce it to `BAScostLL` at builder terms (`#check` output in `AuditCheck.lean`). Because of this, `baLocReg6_reach` is a conditional form, not the hypothesis-free (6) along `BAReach`. The report says so (§5.6 caveat, `T2443d`).

## 5. Compiled nonempty instances (`BAStepS.lean` §8, built in §2 above)
| target | instance | data / discharged hypotheses |
|---|---|---|
| T1 | :438-452 `BAStepS_stepB/C`, example :450 | twists `(true,true)` of `baPG baPB` (`within`) and `baPG baPC` (`ggSplit`, `j=0`). Normality comes from `normalB/C`, steps from `hTB/hTC`. `untag` is introduced at R1's `locStepB/C`. Tags `band,e1,e2,macroA,macroB` are present (`decide +kernel`, :444) |
| T2, T3 | :466 | `baBridge_holds`, `baEquivCost_holds` (reflexive `BAEquivC`), `baCostTwist_holds` at `baPG baPB` |
| T4 | :455 | `baSimC'_holds` at both concrete steps, with a `band` output found by `decide +kernel` |
| T5 | :472, :488 | `baStep_of_simC'` at the `P_B` step (hypothesis `hX` = O2 pin, allowed); the `e1` shape at an `e1` output of the `P_C` step |
| T6 | :498 | `BAStepS_pL` (`E=Fin 2`, `I=Fin 3`): `LocStd` by `decide`, `scalingOrder = 8`, distinct external atoms by `decide`; both `far` cases |
| T7 | :508 | `p = 2`: start-term list nonempty by `decide`, `locReg6InvA 2 P0` by `baInit_locReg6InvA`, `baLocReg6_reach` at every `BAReach K P0 Q` (`hX` kept) |

No `N = 0`, no empty index, no `False` premise. The free `k` with hypothesis `locCostGeA far k _` (examples :472, :488, :498) holds for small enough `k`, so it is not vacuous.

## 6. Paper deltas
The prove report §(d) proposes `T2443a` (atom-level `LocStd` in `BAFinalS` vs vertex-level `locStdA` in the merged `BAFinal`), `T2443b` (per-output `BASimC'`; the literal `BASimC` is not stated), `T2443c` (`BALocReg6` without frame normality), and `T2443d` (`BALocReg6` conditional on the O2 inputs). These cover every Lean/pin difference found in §3–§4.

## 7. Observations (no verdict effect)
- O1. The T7 instance (:508) uses only the first conjunct (`locReg6InvA 2 Q`) of `baLocReg6_reach`. `ba_ord_ge_of_simC'` is applied with every hypothesis discharged inside `baLocReg6_reach` (:425), at `T = BALocStepT`, `m = 0`.
- O2. Dispatcher follow-up: open the O2 row (`BAShapeLL` for `e2`, `macroA`, `macroB` of `BAFrameStepTN`) to get the hypothesis-free (6). The frame-normality corollary from T2442's `BAstepMono` is moot (`baNormal_locStepT` is unconditional).
- O3. Merge: bring in `RBM3D/Graph/BAStepS.lean` only. `RBM3D/Probe/T2443Pins.lean` stays on the branch.

## Verdict
Targets 1–8: **PASS**. No repair list. No dispatcher sign-off needed (the `BALocReg6` strengthening and the O2 decision follow the ticket's own rules and are recorded in the 1a-audit).
