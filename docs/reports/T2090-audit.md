Auditor model: claude-opus-5-5
# T2090 audit (round 1) — S1-36 `Induction/Step1`: `step1TargetV3_holds`

Audit written: Sun Oct  4 01:17:01 UTC 2026. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2090-audit1`, detached at `t/T2090` = `7aea0e5`.

## Target 1: `theorem step1TargetV3_holds (d : ℕ) : RBM.Ind.Step1TargetV3 d` — PASS

### 1. Statement (script diff against the ticket pin, line 7)
```
$ grep -o 'theorem step1TargetV3_holds (d : ℕ) : RBM.Ind.Step1TargetV3 d' docs/tickets/T2090.md | head -1 > pin.txt
$ sed -n 525p RBM3D/Induction/Step1.lean | sed 's/ := by$//' > lean.txt; diff pin.txt lean.txt && echo "diff: identical"
diff: identical
$ lake env lean ax.lean     # import RBM3D.Induction.Step1; #print axioms; #check; #print Step1TargetV3
'RBM.Ind.step1TargetV3_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
step1TargetV3_holds : ∀ (d : ℕ), Step1TargetV3 d
def RBM.Ind.Step1TargetV3 : ℕ → Prop :=
fun d => RBM.Gauss.Sizes.STGbEXPii d → RBM.Gauss.Sizes.STGbEXPij d → RBM.Gauss.Sizes.STStep1 d
exit 0
```
The type is the merged pin (`Step1Setup.lean:149`) verbatim, so hypotheses, quantifier order, ranges
(`0 < 𝔠d ≤ 1/100`, `0 ≤ s`, `s ≤ lemT`, `s < t`, `t ≤ lemT`), losses and dimensions are those of the
merged `STStep1` (`Defs.lean:349`) and `STGbEXPii/ij` (`Defs.lean:308,315`), unchanged; `d` is a free
parameter (no `3 ≤ d` needed). Both conjuncts `STStep1Loop ∧ STStep1Weak` are produced (proof line 538).
Not a special case or conditional adapter: the antecedents `STGbEXPii`, `STGbEXPij` are part of the pin.

### 2. Vacuity / hidden hypotheses / cycles
- The theorem has no hypothesis beyond `d`; the structure `S1Std` (T2079) is *derived* inside the proof by
  `s1_std_of_stFlow` (line 527), not assumed. No new `structure`/`class` in the file:
```
$ grep -n "^structure\|^class\|^def \|^abbrev \|^theorem \|^private \|^instance" RBM3D/Induction/Step1.lean
91:private abbrev s1x … 95:private abbrev s1a … 99:private abbrev s1f … 104:private theorem s1_card_loops
130:private theorem s1_wl_seq … 224:private def s1Net … 228/235/262/372/398/431/455/474: private theorems
525:theorem step1TargetV3_holds (d : ℕ) : RBM.Ind.Step1TargetV3 d := by
589:private def sz2 … 591/602/636/643: private theorems (instance helpers)
```
- Imports: `RBM3D.Induction.Step1Setup`, `RBM3D.Induction.Continuity` (both on main). The proof uses
  no owed pin as a hypothesis (it does not take `STBootstrap`, `STForbidden`, `STNetLift`).
- External hypotheses: `STGbEXPii/ij` are the pin's own antecedents (authorized `lem_GbEXP` inputs,
  D28); this ticket adds none. The preflight's limit check (u = 0: `G_0 = m`, both sides vanish;
  `|m(1/2)| = 1`) is in the prove report (a)(ii).
- Branch base `c7acfed`; main is `6583ca2`. Changes on main since base touch no file this module imports:
```
$ git diff --stat c7acfed main -- RBM3D/ RBM3D.lean
 RBM3D.lean                       |    2 +
 RBM3D/Induction/IterationsA.lean | 2033 ++++++
 RBM3D/Induction/Step2K2.lean     |  220 +++++
 RBM3D/Test/Axioms.lean           |    2 +
$ for n in step1TargetV3_holds Step1Inst; do echo "$n: $(git grep -n -w -F -e $n main -- RBM3D | wc -l)"; done
step1TargetV3_holds:        0
Step1Inst:        0
```

### 3. Compiled nonempty instance (same file, compiled by the build below)
Step1.lean:566-574 (verbatim):
```
example (hii : STGbEXPii 3) (hij : STGbEXPij 3)
    (hK : STKbound sz0 (STflowE z0)) (hLK : STLK sz0 (STflowE z0) sInst)
    (hLoc : STLocalMax sz0 (STflowE z0) sInst) :
    STStep1Loop sz0 (STflowE z0) sInst tInst ∧ STStep1Weak sz0 (STflowE z0) sInst tInst :=
  step1TargetV3_holds 3 hii hij (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num) (1 / 100) (by norm_num) le_rfl (1 / 6) sz0 z0 flow_z0 sInst tInst
    (fun _ => le_rfl) zero_le_lemT (fun n => by simp only [sInst, tInst]; norm_num)
    sixteenth_le_lemT hK hLK hLoc (conStInd_inst (by norm_num))
```
Data (merged): `Defs/Sizes.lean:260` `sz0` (`sz0_values`: L 0 = 4, W 0 = 32, size 0 = 2097152),
`Defs.lean:439-440` `sInst ≡ 0`, `tInst ≡ 1/16` (window of positive length), `flow_z0` (`Defs.lean:435`),
`conStInd_inst` (`Defs.lean:516`). Every deterministic hypothesis (positivity, `𝔠d ∈ (0,1/100]`, `STFlow`,
time ranges, `s < t`, `STConStInd`) is discharged. Remaining hypotheses are other gates' pins
(`STGbEXPii 3`, `STGbEXPij 3`, `STKbound`, `STLK`, `STLocalMax`), allowed by CLAUDE.md §4 step 2.
Further instances: line 578 (`sz1`, lower end of (eq:WO)), 607 (`sz2`, `lam ≡ 10`), 618 (window
`[1/32, 1/16]`, `s > 0`, `𝔠d = 1/200`). None degenerate (no `N = 0`, empty index, collapsed window, `False`).

### 4. Build, axioms, hygiene, diff scope
```
$ lake build RBM3D.Induction.Step1 2>&1 | grep -E "error|warning|sorry|Build"     # audit worktree
Build completed successfully (3332 jobs).
$ grep -n -E "sorry|admit|native_decide|^\s*axiom |set_option|unsafe|implemented_by|@\[extern" RBM3D/Induction/Step1.lean
75:set_option linter.style.longLine false
$ git diff --name-only main...t/T2090
RBM3D/Induction/Step1.lean
$ git diff main...t/T2090 -- RBM3D/Test/Axioms.lean RBM3D.lean | wc -l
       0
$ git diff main...t/T2090 | grep -c "^-[^-]"      # removed lines (frozen signatures untouched)
0
```
Axioms: `[propext, Classical.choice, Quot.sound]` (section 1). Only sole writable file touched; the file is
new; no existing signature changed. (Full `lake build` is the hub's at merge.)

### 5. Paper deltas
The statement is the merged pin; its differences from the paper are already numbered in
`docs/paper-deltas.md`:
```
$ grep -n "T2079a\|T2079b\|T2079c\|T2079d\|T2079e\|T2015c\|T2015d\|T2015e\|T2015g" docs/paper-deltas.md | cut -c1-70
263:## D27 · `lem:main_ind` 的时间限 `t ≤ t₀(z)`（2026-10-03，T2015c；
267:## D28 · 「小 `ε₀`」读作任意 `ε₀ > 0`（2026-10-03，T2015d；
271:## D29 · Step 1 对任意起点 `s ≥ 0`，时间连续性单独成陈述（2026-10-03，T201
279:## D31 · `STStep1` 对每个 `𝔠_d ∈ (0, 10^{-2}]`，只用 (a)、(c) 与 `ML:K
559:## D138 · `Step1TargetV3` 的 d 维形式（2026-10-03，T2079a；S1-35 `Induction
563:## D139 · Step 1 的维数常数（2026-10-03，T2079b；S1-35，4f186cf）
567:## D140 · `S1Std` 的新字段与 `𝔠_d` 的范围（2026-10-03，T2079c；S1-35，4f186cf）
571:## D141 · Step 1 在 `u < 1/2` 区间的处理（2026-10-03，T2079d；S1-35，4f186cf）
575:## D142 · 常数 `c' = c₀/8`（2026-10-03，T2079e；S1-35，4f186cf）
```
No new statement difference is introduced by this file (the target's type is the pin; private helpers are
not statements of record). Coverage complete.

## Observations (no verdict effect)
- O1. `set_option linter.style.longLine false` at line 75: style only.
- O2. Registry: `RBM3D/Test/Axioms.lean` (main:182) still lists `RBM.Ind.Step1TargetV3` as owed ("proved by
  S1-36"); after merge it can be removed by the dispatcher (ticket line 13; prove report (b)).
- O3. `STBootstrap`, `STForbidden` (registered owed with comment "S1-36") are not targets of this ticket and
  are not proved here (prove report (d) Observation 1) — for the dispatcher's registry bookkeeping.
- O4. Ticket line 9 names `stNetLift_holds`; the proof uses `step1NetLift` (T2062, same file) instead. Not a
  statement issue.
- O5. Branch base `c7acfed` is behind main `6583ca2`; the intervening commits add only new modules (section 2),
  so the hub's merge build should be unaffected.

## Verdict
- `step1TargetV3_holds`: **PASS**. No dispatcher sign-off needed.
