Auditor model: claude-opus-5-5

# T2218 audit (round 1) — S6-04 `Induction/ExpHier`: prove the pin `STExpHier`

Mon Oct  5 22:08:58 UTC 2026. Branch `t/T2218` at `71de123`, merge base with `main` `5d313ca` (`main` now `63d62b4`, T2205 report-only in between).
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2218-audit1` (detached at `71de123`). Scratch: `<scratchpad>/T2218/`.

## 1. Diff scope and pin unchanged

```
$ git diff --stat main...t/T2218
 RBM3D/Induction/ExpHier.lean | 891 +++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean       |   1 -
$ git diff main...t/T2218 -- RBM3D/Test/Axioms.lean | grep "^[-+][^-+]"
-   `RBM.Gauss.Sizes.STExpHier, -- `3_5:73` at n = 2, `6:90` expected hierarchy: S6-04; S6-01 (T2204, DECISIONS §67: owed)
$ git diff main...t/T2218 -- RBM3D/Induction/Step6Pins.lean | wc -l
       0
$ grep -n "^import" RBM3D/Induction/ExpHier.lean
6:import RBM3D.Induction.Step6Kit
7:import RBM3D.Induction.LoopGenN
8:import RBM3D.Path.DriftAlgebra
9:import RBM3D.Loop.KLTree
10:import RBM3D.Gauss.LoopGenerator
```
Only the two sole writable files; the Axioms diff is exactly the one owed line of `STExpHier`; imports = the check file's (merged modules, not `RBM3D`).

## 2. Statements against the pin (check file sections 2–3, script, compiled)

Script `mkeq.py`: check-file imports + `import RBM3D.Induction.ExpHier` + sections 1–2 verbatim + one
`example : RBM.Gauss.Sizes.T2218Check.X := @RBM.Gauss.Sizes.X` per section-2 `def X` + `example (d : ℕ) : STExpHier d := stExpHier_holds d`
+ one `example : <section-3 statement> := @RBM.Gauss.Step6Inst.<name>` per section-3 block (statement text extracted by regex).
```
$ python3 mkeq.py          # (#section-2 pins, #section-3 instances)
9 5
$ grep -c "^example" eq.lean; grep -c ":= @RBM.Gauss.Sizes\.\|:= @RBM.Gauss.Step6Inst\.\|:= stExpHier_holds d" eq.lean
15
15
$ grep -o ":= @RBM.Gauss.Step6Inst\.[a-z_A-Z]*" eq.lean | tr '\n' ' '
:= @RBM.Gauss.Step6Inst.inst_expHier_holds := @RBM.Gauss.Step6Inst.inst_expHier_pp := @RBM.Gauss.Step6Inst.inst_expHier_half := @RBM.Gauss.Step6Inst.inst_expHier_Kloop := @RBM.Gauss.Step6Inst.inst_expHier_hierarchy_two
$ lake env lean eq.lean > eq.out 2>&1; echo "exit $?"; grep -c error eq.out
exit 0
0
```
All 9 public theorems have exactly the check-file statements; `stExpHier_holds d : STExpHier d` for every `d` (the merged pin
`Step6Pins.lean:213`, text unchanged: `3 ≤ d → ∀ sz n E, |E| < 2 → ∀ σ a, ContinuousOn f [0,1) ∧ ContinuousOn D [0,1) ∧ ∀ u ∈ (0,1), HasDerivAt f (Θ f + D) u`).
Time ranges (continuity on `Ico 0 1` incl. `u = 0`, derivative on `Ioo 0 1`), every `σ : Fin 2 → Bool`, every `a`, every `sz`, `n` — as pinned.
The fixed-size intermediates are at least as general as the ticket's mathematics (1a for every `LoopIdx`, no `WF`; 1c, 1d every `σ`).

## 3. Vacuity, hidden hypotheses, cycles

```
$ grep -nE "^(private )?(structure|class|def|abbrev|instance|noncomputable def)" RBM3D/Induction/ExpHier.lean
63:private structure expHier_Good (d L W : ℕ) [NeZero L] [NeZero W] (b : ℝ)
$ grep -nE "^(theorem|lemma) " RBM3D/Induction/ExpHier.lean | grep -v "expHier_\|stExpHier_holds"   # (no output)
$ grep -c "^private theorem\|^private lemma" RBM3D/Induction/ExpHier.lean
36
```
- No public theorem takes a structure/class hypothesis; `expHier_Good` is private and internal (no public signature mentions it; §2 signatures).
- `stExpHier_holds (d : ℕ) : STExpHier d` has no hypothesis; all inputs come from the five merged imports. No cycle (the file is new; nothing imports it).
- No external hypothesis is introduced, so no limit check applies.

## 4. Compiled nonempty instances (`ExpHier.lean` §6, namespace `RBM.Gauss.Step6Inst`)

Data: `d = 3`, `sz0`, `n = 0` (`L = 4`, `W = 32`, `lam = 1/64`), `E = 1/2`, `a = (0, e₁)`; all hypotheses discharged by `norm_num`/`simp`.
| target | instance | data | hypotheses discharged |
|---|---|---|---|
| 3 `stExpHier_holds` | `inst_expHier_holds` = `inst_expHier (stExpHier_holds 3)`; `inst_expHier_pp` | `σ=(+,-)`, `(+,+)` | `3≤3`, `|1/2|<2` |
| 2c `expHier_hasDerivAt` | `inst_expHier_half` (`.2.2 (1/2)`) | `σ=(-,-)`, `u=1/2` | `0<1/2<1` |
| 2a, 2b | unnamed `example`s (l. 865, 870) | `σ=(+,-)` | `|1/2|<2` |
| 1a | `example` (l. 842) | `(L,W,g)=(4,32,1/64)`, loop `((+,-),(0,e₁))` | `|1/2|<2` |
| 1b | `example` (l. 850) | sample `ω ≡ 1`, `u=1/2` | `0<u<1`, `WF` by `simp` |
| 1c | `inst_expHier_Kloop` | `σ=(+,+)`, `u=1/2` | `0≤u<1` |
| 1d | `inst_expHier_hierarchy_two` | `M=1` (`isHermitian_one`), `σ=(-,-)` | all |
| 1e | `example` (l. 860) | `σ=(+,-)`, `u=1/2` | `0<u<1` |
None degenerate (no `N = 0`, empty index, collapsed window or `False` premise); every instance compiles (build below).

## 5. Build, axioms, hygiene (audit worktree)

```
$ lake build RBM3D.Induction.ExpHier > build.out 2>&1; echo "exit $?"; grep -c "^error" build.out
exit 0
0
$ grep "ExpHier.lean" build.out | grep -v axioms | cut -c1-90
warning: RBM3D/Induction/ExpHier.lean:16:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Induction/ExpHier.lean:25:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Induction/ExpHier.lean:30:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Induction/ExpHier.lean:34:100: This line exceeds the 100 character limit, please shorten it!
$ tail -1 build.out
Build completed successfully (3853 jobs).
$ grep "ExpHier.lean.*depends on axioms" build.out | sed 's/.*: .\(RBM[^ ]*\)'"'"' depends on axioms: /\1 /'
RBM.Gauss.Sizes.expHier_continuousOn_integral_loopL [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.expHier_genMat_eq_cuts [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.expHier_Kloop_hasDerivAt [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.expHier_hierarchy_two [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.expHier_hasDerivAt_fixed [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.expHier_continuousOn_err [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.expHier_continuousOn_drift [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.expHier_hasDerivAt [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.stExpHier_holds [propext, Classical.choice, Quot.sound]
RBM.Gauss.Step6Inst.inst_expHier_holds [propext, Classical.choice, Quot.sound]
RBM.Gauss.Step6Inst.inst_expHier_pp [propext, Classical.choice, Quot.sound]
RBM.Gauss.Step6Inst.inst_expHier_half [propext, Classical.choice, Quot.sound]
RBM.Gauss.Step6Inst.inst_expHier_Kloop [propext, Classical.choice, Quot.sound]
RBM.Gauss.Step6Inst.inst_expHier_hierarchy_two [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Induction/ExpHier.lean | wc -l
       0
```
Registry pre-check (§20 (2)), temporary file `pre.lean` = the 258 import lines of `RBM3D.lean` + `import RBM3D.Induction.ExpHier` + `#assert_rbm_axioms`
(all those modules built first: `grep "^import" RBM3D.lean | awk '{print $2}' | xargs lake build RBM3D.Induction.ExpHier` → exit 0, `Build completed successfully (4020 jobs).`):
```
$ lake env lean pre.lean > pre.out 2>&1; echo "exit $?"; grep -c STExpHier pre.out
exit 0
0
$ grep -n "premises found by scanning\|^registry:\|error" pre.out | cut -c1-140
155:premises found by scanning: 127 (borrowed 1, owed 95, structural 25, refuted 6).
156:registry: 2 borrowed + 146 owed + 80 structural + 7 refuted; 108 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
```
(Same run before the dependency build used the stale main-cache `Test/Axioms` olean and printed `147 owed`, `STExpHier` twice: the base count.)
Owed count 147 → 146, `STExpHier` absent, no unregistered premise, only the three standard axioms. The full `lake build` with the root import is the hub's step at merge.

## 6. Paper deltas

The proved statement is the merged signed pin `STExpHier` verbatim (its paper reading `3_5:73` at `n = 2` after expectation, `6:90`, audited PASS in T2191 `docs/reports/T2191-audit.md:60`).
No hypothesis added, no statement weakened; the intermediates are internal fixed-size forms. RBM2D's `f_0 = 0` conjunct is not in the pin
(ticket: not a target). No new Lean/paper difference, so no candidate needed; the prove report proposes none — coverage complete.

## 7. Observations (no statement, instance, build, axiom or coverage effect)

- O1: four header lines of `ExpHier.lean` (16, 25, 30, 34) exceed 100 characters (style linter warnings only).
- O2: the targets 1a, 1b, 1e, 2a, 2b have unnamed `example`s rather than named checks; allowed by CLAUDE.md §4 step 2.
- O3: the ticket cites `Axioms.lean:230` / `main` 14513ee; on the branch base 5d313ca the line was `:229` and was deleted by content (correct line).
- Merge note for the hub (ticket §20 (3)): T2217 deletes the adjacent owed line `STImproveExpAver`; keep both deleted on conflict.

## Verdict

| target | verdict |
|---|---|
| 1a `expHier_continuousOn_integral_loopL` | PASS |
| 1b `expHier_genMat_eq_cuts` | PASS |
| 1c `expHier_Kloop_hasDerivAt` | PASS |
| 1d `expHier_hierarchy_two` | PASS |
| 1e `expHier_hasDerivAt_fixed` | PASS |
| 2a `expHier_continuousOn_err` | PASS |
| 2b `expHier_continuousOn_drift` | PASS |
| 2c `expHier_hasDerivAt` | PASS |
| 3 `stExpHier_holds` (pin `STExpHier`) | PASS |
| 4 five instances | PASS |

**T2218: PASS.** No dispatcher sign-off needed.

