Auditor model: claude-opus-5-5
# T2448 audit (round 1) — BA-L L3d3 `BAEngine` — Mon Oct 12 11:26:15 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2448-audit1`, detached at `t/T2448` = `a810b5d`; merge base with `main` `20917ed`; `main` = `adb4a19`.
Scratch: `scratchpad/T2448/{stmtdiff.py, T2448audit_check.lean, T2448audit_ax.lean, build.log}`.

## 0. Diff and binder state
```
$ git diff --name-only main...t/T2448
RBM3D/Graph/BAEngine.lean
$ git diff main...t/T2448 -- RBM3D.lean | wc -l
       0
$ git log --oneline main | grep T2447
1fec089 H240: ticket T2447 and check, DECISIONS §259, CONTROL
$ git log --oneline -1 t/T2447; head -1 docs/queue/T2447.state
272d1f0 T2447: BAShapeO2, BAShapeO2B: root imports, docstrings
state: proving
$ sed -n 100p RBM3D/Graph/BAStepS.lean
    (∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapeLL sh BAFrameStepTN) →
```
Only the sole writable file is touched. The root import line is not committed; the hub adds it at merge (§3 (A) 4). T2447 is not merged, so under O2R-C3 targets 3 and 4 must take the binder `T2448_Binder` as their first hypothesis. They do (§1).

## 1. Statements against the pins (script diff, then Lean defeq)
`stmtdiff.py` normalises whitespace, renames `T2448_LocRegConcl`→`BALocRegConcl`, and for targets 3–4 puts `(T2448_Binder body) →` in front of the pin.
```
$ python3 stmtdiff.py docs/tickets/checks/T2448-check.lean RBM3D-wt/T2448-audit1/RBM3D/Graph/BAEngine.lean
BALocRegConcl sig : IDENTICAL
BALocRegConcl body: IDENTICAL
baStep_nWS          : IDENTICAL (pin T2448_StepNWS)
ba_nWS_ge           : IDENTICAL (pin T2448_NWSGe)
baStart_nWS         : IDENTICAL (pin T2448_StartNWS)
baEngine_assemble   : IDENTICAL (pin T2448_Binder → T2448_Assemble)
ba_localregularX    : IDENTICAL (pin T2448_Binder → T2448_LocRegX)
```
Lean check: the full check file, plus `import RBM3D.Graph.BAEngine`, plus these lines:
```
example (p : ℕ) (c : ℝ) (K0 d : ℕ) (D : ℝ) (o e : List (BAPGraph (Fin 2))) : T2448_LocRegConcl p c K0 d D o e = BALocRegConcl p c K0 d D o e := rfl
example : T2448_StepNWS := baStep_nWS
example : T2448_NWSGe := ba_nWS_ge
example : T2448_StartNWS := baStart_nWS
example : T2448_Binder → T2448_Assemble := baEngine_assemble
example : T2448_Binder → T2448_LocRegX := ba_localregularX
$ lake env lean T2448audit_check.lean; echo exit $?
... (#check output of Part 1, no error line) ...
exit 0
```
Checks against the ticket's mathematics:
- Target 1, conjunct (a): `2p ≤ ord`, and `3p ≤ ord` only under `¬ atomSetoid` of the two external vertices (L4-C4 (b)).
- Target 1, conjunct (b): the window is `W^{-d/2} ≤ Ψ ≤ W^{-c}`, `L^d ≤ W^{K0}`.
- Target 1, conjunct (c): there is a `P0 ∈ start` with `BAReach (lvl1Cutoff … P0.g.counters)` to the graph, and the counters are bounded against that `P0`.
- Target 1, conjunct (d): the data hypotheses are only `BASelf`, `0 ≤ t`, `t < 1`, `3 ≤ L` (C1).
- Target 4 has no `∀ m ≠ 0`, as the ticket says. Parameter order: `p c (0<c) K0 d D` and then `∃ outs errs`, as in the band `lw_localregularX`.
- (1)–(5) are not in the conclusion, by dispatcher answer (b).
**Statement: PASS for targets 1–4.**

## 2. Hidden hypotheses, vacuity, cycles
```
$ grep -nE "^(theorem|def|lemma|abbrev|instance|structure|inductive|class)" RBM3D/Graph/BAEngine.lean
190:theorem baStep_nWS …   201:theorem ba_nWS_ge …   208:theorem baStart_nWS …
220:def BALocRegConcl …    268:theorem baEngine_assemble …   335:theorem ba_localregularX …
405:def BAEngine_pL : BAGraph (Fin 2) (Fin 3) :=        413:theorem BAEngine_pL_locStd : BAEngine_pL.LocStd := by decide
```
- **Structures and inductives:** no new `structure` or `inductive`. `BALocRegConcl` is a plain `def` of four conjuncts with no fields.
- **Imports:** only `RBM3D.Graph.BALvl1C` and `RBM3D.Graph.BAStepS`, both on `main`. There is no cycle, since the file is new and imported by nothing.
- **Unproved premises:** the only one is the O2R-C3 binder on targets 3–4. It is verbatim `BAStepS:100`, the pin of the T2447 gate, which the ticket permits. It is not restated as a new `Prop`.
- **Merged inputs used** (signatures in the `#check` output above): `baLocReg6_reach : BALocReg6`, `baLvl1LemmaSize_holds : ∀ d, BAlvl1LemmaSize d`, `BAGraph.partition_normal`, `BAGraph.val_eq_partition`, `ba_lvl1_induction`, `lvl1_choose_list`, `lvl1_sum_flatMap`, `owx_integral_list_sum`.
- **Premise scan** (`LocStd` sits inside the hypothesis of `baEngine_assemble`), run with `Test/Axioms.lean` unchanged:
```
$ printf 'import RBM3D\nimport RBM3D.Graph.BAEngine\n#assert_rbm_axioms\n' > T2448audit_ax.lean
$ lake env lean T2448audit_ax.lean 2>&1 | grep -E "error|axiom audit|premise\(s\) that no"
axiom audit: 13141 theorems, 4131 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ lake env lean T2448audit_ax.lean >/dev/null 2>&1; echo lean-exit $?
lean-exit 0
```
**PASS.**

## 3. Compiled nonempty instances (`BAEngineInst`, `BAEngine.lean:417-502`; they compile because the module builds, §4)
| target | instance | data and nondegeneracy |
|---|---|---|
| 1 `BALocRegConcl` (def) | `:422` conjunct (a) at `baPG BAEngine_pL`; full `BALocRegConcl 2 (1/4) 2 3 10 …` is concluded in `:470`, `:483` | `BAEngine_pL` is `LocStd` (`decide`), `ord = 8` (`decide +kernel`) |
| 2 `baStart_nWS` | `:430` | `p = 2`; `length = 16` (`decide`); no start term is `LocStd` (`BAEngine_start_not_locStd`, a solid loop, `decide +kernel`); each has 2 black waved edges |
| 2 `baStep_nWS` | `:439` | start term not `LocStd`; step from `baLvl1ExistsStep_holds`; `outs ≠ []` (`BAEngine_frame_ne_nil`) |
| 2 `ba_nWS_ge` | `:452` | `BAReach (ord P0 + 1) P0 Q` built by `BAReach.step` from `BAReach.refl` (a real step); `2 ≤ black(Q)` |
| 3 `baEngine_assemble` | `:470` | `p=2, c=1/4, K0=2, d=3, D=10`; every per-start-term hypothesis discharged by `BAEngine_lists` (= `baLvl1LemmaSize_holds` at the 16 terms) |
| 4 `ba_localregularX` | `:483` | same constants; the size conjunct is instantiated at `W=4, L=2, Ψ=1/4`, with the window inequalities proved; the identity is at the flow point `d=3, L=4, W=2, (g0P,EP,t0P,m0P), ℓ0` via `flowP_data` |

- **Hypotheses of the examples:** only `hX` (the T2447 pin). All deterministic hypotheses are discharged.
- **Degeneracy:** no `N = 0`, no empty start list (16), no collapsed window, no `False` premise.

**PASS.**

## 4. Build, axioms, hygiene
```
$ cd RBM3D-wt/T2448-audit1 && lake build RBM3D.Graph.BAEngine; echo exit $?
Build completed successfully (3829 jobs).
exit 0
$ grep "BAEngine.lean" build.log | grep -E "error|warning" | wc -l
       0
$ lake build RBM3D 2>&1 | tail -1          # root as on the branch (without the BAEngine import), for the premise-scan run of §2
Build completed successfully (4273 jobs).
$ #print axioms (in T2448audit_check.lean)
'RBM.Graph.BALocRegConcl' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baStep_nWS' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.ba_nWS_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baStart_nWS' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baEngine_assemble' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.ba_localregularX' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAEngine_pL_locStd' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom " RBM3D/Graph/BAEngine.lean | wc -l
       0
```
- **Size:** the file has 506 lines, under the 2,000 stop line, and `BAEngine2` is not used.
- **Frozen signatures:** none touched, since only the new file changes.
- **§3 (E) naming:** the unpinned public names `BAEngine_pL` and `BAEngine_pL_locStd` carry the file stem. All other helpers are `private`.

**PASS.**

## 5. Paper deltas
The report's §(d) proposes two candidates:
- **T2448a:** `BALocRegConcl` omits items (1)–(5) of `lem:localregular`, and the far half of (6) holds only at distinct external atoms.
- **T2448b:** targets 3–4 are conditional on the T2426-O2 shape inputs (the binder) until T2447 merges and a consumer discharges them. This is a special case, not the unconditional lemma (§5.6).

Also covered: the missing `m ≠ 0` is the BA form of the band's tag mechanism, not a paper difference; `P0.g.nM ≤ p` is owed to L3b1 (DECISIONS §260 (c), report §(d) item 3).

**Coverage: PASS.**

## Observations (no statement, instance, build, axiom or coverage effect)
- **O1 (for the dispatcher).** Under dispatcher note (b) the 1a was to "stop and report" if a consumer reads (1)–(5). The audit confirms that the band consumer reads them:
  ```
  $ sed -n 1275p RBM3D/Graph/LWMoment.lean;  sed -n 1288p …
    obtain ⟨-, hc2, hc3, -, hc5⟩ := hc
        obtain ⟨-, -, h345, h6, -⟩ := hc5 _ hq
  ```
  So the band `lwMoment_prec_far_r` reads `LocReg345` from inside `LWLocRegConcl`. The 1a reported this (finding 1) and continued, reading the stop rule as not triggered: no BA consumer contract exists yet, and conjunct (c) (`BAReach` from a start term) is the composition point the ticket names for L3b1/L3b2. The statement is exactly as pinned. Before L3d2 is drafted, the dispatcher should confirm that the L3d2 contract takes `LocReg345` along conjunct (c) and not inside `BALocRegConcl`.
- **O2.** `BAEngine_pL_locStd` is a concrete instance that satisfies the premise scan for `BAGraph.LocStd`. The band precedent is `localReg2_inst_Q_locStd`. The prover suggests a registry or structural classification of `LocStd` instead. This is for the dispatcher; the ticket says "Registry: none" and `Test/Axioms.lean` is unchanged.
- **O3.** The target-4 instance does not show `outs ++ errs ≠ []`. The ticket asks only for a nonempty start list, which is shown (16).
- **O4.** L4d (T2419) is not imported by the file. The ticket's note (d) is to drop it from the inputs.

## Verdict
- **Target 1 `BALocRegConcl`:** PASS.
- **Target 2 `baStep_nWS`, `ba_nWS_ge`, `baStart_nWS`:** PASS.
- **Target 3 `baEngine_assemble`:** PASS. It is in the form `T2448_Binder → T2448_Assemble`, per O2R-C3, because T2447 is not merged.
- **Target 4 `ba_localregularX`:** PASS. It is in the form `T2448_Binder → T2448_LocRegX`, for the same reason.
- **Target 5 instances:** PASS.

**Ticket verdict: PASS.** No dispatcher sign-off is required for the merge. O1 and O2 are recorded for the dispatcher.
