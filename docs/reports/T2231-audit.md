Auditor model: claude-opus-5-5

# T2231 audit (S5-11b `Induction/PfStep5`), round 1. Written Tue Oct  6 01:43:19 UTC 2026

Branch `t/T2231` at `9885f4c`; worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2231-audit1`; `S` = `<scratchpad>/T2231/`; `F` = `RBM3D/Induction/PfStep5.lean`.

## 1. Diff scope, merge cleanliness
```
$ git diff --stat main...t/T2231
 RBM3D/Induction/PfStep5.lean | 2581 ++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean       |    3 +-
$ git merge-tree --write-tree --name-only main t/T2231 >/dev/null; echo $?      # main = e5b944a
0
$ git diff main...t/T2231 -- RBM3D/Test/Axioms.lean | grep '^[-+] '
-   `RBM.Gauss.Sizes.STStep5III, -- Step 5, case (iii): from `STPfStep5` (S5-03), proved internally (DECISIONS §40); S5-01 (T2138, DECISIONS §40: owed)
-   `RBM.Gauss.Sizes.STPfStep5, -- `lem:pf_step5`; proved internally (DECISIONS §40); S5-01 (T2138, DECISIONS §40: owed)
+   `RBM.Gauss.Sizes.PfStep5_walkConcl, -- `lem:pf_step5` grid conclusion ... hypothesis of `pfStep5_PT_of_walk` (T2231, S5-11b: owed)
```
Only the two sole writable files. No frozen signature touched (`Step5Pins.lean` unchanged). Imports of `F`: exactly
`RBM3D.Induction.PfStep5Grid`, `RBM3D.Induction.TailtoTailSq`, `RBM3D.Path.DifREP3`.

## 2. Statements (script diff against the check file; ascription against the pins)
Every docstring+`def PfStep5_*` block (3 vocabulary, 6 pins) extracted by awk from the check file and from `F`:
```
$ wc -l S/T2231-check.lean.defs S/PfStep5.lean.defs; diff S/T2231-check.lean.defs S/PfStep5.lean.defs; echo "diff exit: $?"
      63 .../T2231-check.lean.defs
      63 .../PfStep5.lean.defs
diff exit: 0
$ grep -c "^def PfStep5_" S/T2231-check.lean.defs S/PfStep5.lean.defs
T2231-check.lean.defs:9
PfStep5.lean.defs:9
$ grep -nE "^theorem (pfStep5_(realize|goodMeas|farAbsorb|walk|PT_of_walk|lift)|stPfStep5_holds|stStep5III_holds) " F
208:theorem pfStep5_realize {d : ℕ} (sz : Sizes d) : PfStep5_realize_pin sz := by
270:theorem pfStep5_goodMeas {d : ℕ} (sz : Sizes d) : PfStep5_goodMeas_pin sz := by
406:theorem pfStep5_farAbsorb {d : ℕ} (sz : Sizes d) : PfStep5_farAbsorb_pin sz := by
2129:theorem pfStep5_walk (d : ℕ) : PfStep5_walk_pin d := by
2320:theorem pfStep5_PT_of_walk (d : ℕ) : PfStep5_PT_of_walk_pin d := by
2398:theorem pfStep5_lift (d : ℕ) : PfStep5_lift_pin d := by
2457:theorem stPfStep5_holds (d : ℕ) : STPfStep5 d := by
2473:theorem stStep5III_holds (d : ℕ) : STStep5III d := ST_step5_caseIII_of_pf (stPfStep5_holds d)
```
`S/ax.lean` (imports only `RBM3D.Induction.PfStep5`) re-elaborates each target against its pin by ascription, e.g.
`example : ∀ d (sz : RBM.Gauss.Sizes d), PfStep5_realize_pin sz := @pfStep5_realize`, ...,
`example : ∀ d, STPfStep5 d := stPfStep5_holds`, `example : ∀ d, STStep5III d := stStep5III_holds`: exit 0 (section 4).
Section `variable {d : ℕ}` lines (`:1035, :1203, :1400, :1473, :1775, :1981, :2280`) add nothing to the target types
(the ascriptions above close with no extra argument). Targets 7, 8 are the merged `STPfStep5` / `STStep5III`
(`Step5Pins.lean:211`, `:458`) unchanged: the merged pin `STIngR5 d STReg5III STPfConcl` is proved outright.

## 3. Hidden hypotheses, vacuity, cycles, public names
```
$ grep -E "^(...)?(theorem|lemma|def|abbrev|structure|instance|inductive|class) " F | <name>   # public declarations
PfStep5_walkConcl PfStep5_PTConcl PfStep5_PrecConcl PfStep5_realize_pin PfStep5_goodMeas_pin PfStep5_farAbsorb_pin
PfStep5_walk_pin PfStep5_PT_of_walk_pin PfStep5_lift_pin pfStep5_realize pfStep5_goodMeas pfStep5_farAbsorb pfStep5_walk
pfStep5_PT_of_walk pfStep5_lift stPfStep5_holds stStep5III_holds pfStep5_inst_realize pfStep5_inst_realize_one
pfStep5_inst_goodMeas pfStep5_inst_farAbsorb pfStep5_inst_walk pfStep5_inst_PT pfStep5_inst_lift pfStep5_inst_Prec
pfStep5_inst_PT_of_premises pfStep5_inst_Prec_of_premises pfStep5_inst_pf pfStep5_inst_step5III
$ grep -cE "^private " F; <private names not prefixed pfStep5_/PfStep5> | wc -l
53
0
```
- Public names = exactly the ticket's interface list. No public structure; the private `PfStep5Num` is internal only and
  appears in no target type.
- Target 5 (`PfStep5_PT_of_walk_pin`) and target 6 (`PfStep5_lift_pin`) are conditional adapters by the ticket's pin
  design. The hypothesis of target 5 (`PfStep5_walkConcl`) is discharged in `stPfStep5_holds` (`F:2463-2470`) by
  `pfStep5_walk` (target 4); the hypothesis of target 6 (`PfStep5_PTConcl`) is discharged by target 5. So the endpoint
  `STPfStep5 d` is unconditional beyond the merged `STIngR5` premises.
- No cycle: `F` imports only three merged modules; `STPfStep5`/`STStep5III` occur only as conclusions.
- `𝔠_d := 1/100` with `STConStInd` and `STKbound, STKward, STLK, STDecay, STStep1Loop` unused (report (b) item 5). The
  Lean statement is the merged pin, so this does not change it; it only means the proof does not need these premises.

## 4. Build, axioms, hygiene (audit worktree)
```
$ lake build RBM3D.Induction.PfStep5 > S/build2.out 2>&1; echo "exit $?"; grep -c "^error" S/build2.out; grep -c "PfStep5\.lean" S/build2.out; tail -1 S/build2.out
exit 0
0
0
Build completed successfully (3885 jobs).
$ ls -lT .lake/build/lib/lean/RBM3D/Induction/PfStep5.olean    # built in this worktree (local time = UTC-7)
-rw-r--r--@ 1 junyin  staff  6937920 Oct  5 18:40:32 2026 .lake/build/lib/lean/RBM3D/Induction/PfStep5.olean
$ lake env lean S/ax.lean > S/ax.out 2>&1; echo "exit $?"; sed 's/.*depends on axioms: //' S/ax.out | sort | uniq -c
exit 0
  20 [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom |maxHeartbeats|implemented_by|extern|unsafe|opaque" F | wc -l
0
```
(20 = 8 targets + 12 instances.) The module's own warnings in the build log: 0 lines (the other warnings are replayed upstream modules).

Registry. On the branch as it is, the root has no `import RBM3D.Induction.PfStep5` yet (the hub adds it at merge), so the root
check flags `STPfStep5`, whose `owedProps` line was removed:
```
$ lake build RBM3D 2>&1 | grep -A1 "axiom audit: 1 premise"
error: RBM3D.lean:275:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refutedProps`:
  [RBM.Gauss.Sizes.STPfStep5]
```
A merged root, simulated as a scratch file (every `import` of `RBM3D.lean`, then `import RBM3D.Induction.PfStep5`, then the rest of
`RBM3D.lean`, which ends with `#assert_rbm_axioms`):
```
$ grep -c "^import" S/root_sim.lean; lake env lean S/root_sim.lean > S/root_sim.out 2>&1; echo "root-sim exit: $?"
273
root-sim exit: 0
$ grep -nE "error|axiom audit|STPfStep5|STStep5III|PfStep5" S/root_sim.out
1:axiom audit: 6823 theorems, 2337 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
97:  RBM.Gauss.Sizes.PfStep5_walkConcl: 3 [no certificate]
```
So merge step (A)4 (the root import) is required; with it the registry check passes, and `STPfStep5` and `STStep5III` are no longer owed.

## 5. Compiled nonempty instances (namespace `RBM.Gauss.PfStep5Inst`, `F:2489-2581`; axioms in section 4)
| target | instance | data / discharged hypotheses | remaining hypotheses |
|---|---|---|---|
| 1 | `pfStep5_inst_realize`, `_realize_one` | `sz0`, `s≡0`, `t≡1/16`, `K≡8`, `n=0`, `j=3` (grid time `3/128>0`), `ω≡0` and `ω≡1`; `0≤s` `le_rfl`, `s≤t` `norm_num` | none |
| 2 | `pfStep5_inst_goodMeas` | `sz0`, `E=STflowE z0`, `D=55`, `Jst≡1`, `τ'=1/10`, `n=0`, `u=1/16` | none |
| 3 | `pfStep5_inst_farAbsorb` | `sz0`, `(𝔠,𝔡)=(1/6,1/10)`, `sz0_admissible`, `D*=55` | none |
| 4 | `pfStep5_inst_walk` | `inst_ing5_III STReg5III _ (pfStep5_walk 3) sz0_reg5III 1 one_pos`: `3≤3`, `flow_z0`, `0≤s<t≤lemT`, regime, `sz0_con` (`STConStInd`) | stochastic `STIngR5` premises inside `InstIng5Concl` (other gates' pins) |
| 5 | `pfStep5_inst_PT`, `_PT_of_premises` | `sz0_hs0`, `s≤t`, `t<1` (`norm_num`), `sz0_reg5III`, `pfStep5_Wev sz0 sz0_admissible` | walk conclusion = output of target 4; `_PT_of_premises` composes 4+5 |
| 6 | `pfStep5_inst_lift`, `_Prec`, `_Prec_of_premises` | `3≤3`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, `flow_z0`, `sz0_hs0/hst/ht`, regime | `PfStep5_PTConcl` = output of target 5; `_Prec_of_premises` composes 4+5+6 |
| 7 | `pfStep5_inst_pf` | `inst_pfStep5 (stPfStep5_holds 3) 1 one_pos` | stochastic `STIngR5` premises only |
| 8 | `pfStep5_inst_step5III` | `inst_skeletonIII (stPfStep5_holds 3) 1 one_pos` | stochastic `STIngR5` premises only |

The merged `InstIng5Concl` (`Step5Pins.lean:539-544`) keeps only `STKbound, STKward, STLK, STDecay, STDecayStrong, STStep1Loop,
STStep2Concl, STLmaxU, STLKU` as hypotheses. All of them are other gates' stochastic pins (CLAUDE.md §4 step 2). Every
deterministic hypothesis is discharged at `sz0` (`N_0 = 2097152`, `L_0 = 4`, `W_0 = 32`, nonempty index: `lam² = 1/4096 ≤ 15/16`).
None of the instances is degenerate (`N = 0`, an empty index set, a collapsed window or a `False` premise).

## 6. Paper deltas
- Existing: D318 (T2134d, pin form "for all `D`"), D529 (T2209d, levels `D_u`, `D*`), D530 (T2209e, closure `ε<𝔡/4`, `τ=𝔠ε/2`).
- Proposed in the prove report (d): T2231a (grid strong induction replaces the stopping time `T`), T2231b (per-section grids
  and the one net lift), T2231c (explicit `ε₁ = min(𝔡/8,1/4)`, `D* = max(D, 2/𝔠+12d)+2d+1`).
- No other Lean/paper statement difference was found: targets 1-6 are internal pins, and targets 7-8 are merged pins unchanged.

## 7. Observations (no effect on statement, instance, build, axiom or delta coverage)
1. The ticket's acceptance line says the `Test/Axioms.lean` diff has "deletions only", but the diff also has one insertion
   (`PfStep5_walkConcl` added to `owedProps`). The ticket's registry clause explicitly allows this insertion ("if the registry
   pre-check flags a name, append one line and report"), and it follows the §20 precedent for conclusion predicates used as
   adapter hypotheses (`STXiBoot`, `STStep2DecayPT`, `STGoodAt`: "owed"). Confirming the class is the dispatcher's routine registry step.
2. The hub must add the root import (merge step (A)4) before the full build. Without it, `#assert_rbm_axioms` flags `STPfStep5`
   (section 4).
3. The ticket's preflight script data (`𝔠 = 1/2`, `d = 3`) violates `Bandwidth`. The prove report (a) row 0 records this and
   uses `sz0` (`𝔠 = 1/6`) instead. This is a ticket-text defect.
4. `F` has 2581 lines, against the ticket estimate of 1050/1300/1600. The stop rule applied only to the 1a preflight.
5. The eventual closure threshold is intrinsic (report (a) row 9: `log W ≥ 4267` at saturated bandwidth). The instances
   therefore cannot exhibit the `∀ᶠ` conclusion at a finite `n`. The instances keep the stochastic premises as hypotheses,
   which §4 step 2 allows.

## Verdict
Targets 1-4: PASS. Targets 5, 6: PASS (conditional adapters by pin design; their hypotheses are discharged in target 7).
Target 7 `stPfStep5_holds`: PASS (merged `STPfStep5`, unconditional). Target 8 `stStep5III_holds`: PASS (merged `STStep5III`).

Ticket T2231: **PASS**. No dispatcher sign-off is needed. Merge requires the root import (observation 2).
