Auditor model: claude-opus-5-5

# T2422 audit (round 1) — Sun Oct 11 10:56:12 UTC 2026

Branch `t/T2422` at `c2be2dd` (merge-base with `main`: `6c42b16`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2422-audit1` (detached).
Scratch files under the auditor's scratchpad `T2422/` (`ax.lean`, `inst.lean`); no source edited.

## 1. Diff and sole writable files

```
$ git diff --numstat main...t/T2422
1	0	RBM3D.lean
30	0	RBM3D/BA/GbEXPav.lean
1	3	RBM3D/Test/Axioms.lean
```
Exactly the three sole writable files. `RBM3D.lean`: one line `import RBM3D.BA.GbEXPav` after the last import (`RBM3D.Chain.Step2Kern`),
before `#assert_rbm_axioms`. Stop line 400: 30 + net (1 − 3) = 28. No frozen signature touched (`Step1Boot.lean`, `GreenLocal.lean`,
`GreenMinor3.lean`, `GreenCond2.lean` unchanged).

## 2. Statements against the pin

```
$ lake env lean ax.lean     # import RBM3D.BA.GbEXPav
baGbEXPav_holds : ∀ (d : ℕ), 2 ≤ d → BAGbEXPav d
baFAav_greenLocal : ∀ (d : ℕ), BAFAav d → GreenLocal_FAav d
```
Ticket pins: target 1 `BAFAav d → GreenLocal_FAav d`; target 2 `baGbEXPav_holds (d : ℕ) (hd : 2 ≤ d) : BAGbEXPav d` (`BA/Step1Boot.lean:123`). Match.
`BAGbEXPav` itself is the unchanged pin (`Step1Boot.lean:123-128`): `∀ κ ε 𝔡 > 0, ∀ 𝔠 sz z, BAFlow … → ∀ t, 0 ≤ t ≤ T₀ → ∀ ε₀ > 0, BAGavLGEX sz z t ε₀`,
and `BAGavLGEX` (`:97-103`) keeps the window `W^{-d/2} ≤ Ψ ≤ W^{-ε₀}` and `STInitialGT2gL` as binders inside the `Prop`, conclusion `≺ Ψ²`.

Target 1 (the two definition bodies, names normalised):
```
$ sed -n 859,869p RBM3D/BA/GreenMinor3.lean | sed 's/BAFAav/NAME/' > a
$ sed -n 745,755p RBM3D/BA/GreenLocal.lean  | sed 's/GreenLocal_FAav/NAME/' > b
$ diff a b && echo IDENTICAL $(wc -l < a)
IDENTICAL 11
```
(headers `def BAFAav (d : ℕ) : Prop :=` at `GreenMinor3.lean:858`, `def GreenLocal_FAav (d : ℕ) : Prop :=` at `GreenLocal.lean:744`.)
Also checked definitionally: `example : BAFAav = GreenLocal_FAav := rfl` compiles (in `ax.lean`, exit 0). The proof `fun h => h` is the identity; no
difference in substance, as the ticket requires.

Target 2 proof: `greenLocal_gbEXPav_of_fa d hd (baFAav_greenLocal d (baFAav_holds d))`, with
`greenLocal_gbEXPav_of_fa (d) (hd : 2 ≤ d) : GreenLocal_Wiring d` and `GreenLocal_Wiring d := GreenLocal_FAav d → BAGbEXPav d` (`GreenLocal.lean:788,793`),
`baFAav_holds (d : ℕ) : BAFAav d` (`GreenCond2.lean:1730`). All merged on `main`. The guard `2 ≤ d` is that of the wiring (inherited from GL2
`baGbEXPii_holds`); the paper reads `d ≥ 3`, so the Lean statement is the more general one.

- Target 1 `baFAav_greenLocal`: **PASS**.
- Target 2 `baGbEXPav_holds`: **PASS** (the general pin, not a special case; quantifier order is the pin's).

## 3. Hidden hypotheses, vacuity, cycles

- No new hypothesis (C1): the theorem's only hypothesis is `2 ≤ d`; `STInitialGT2gL` and the window remain binders inside the pinned `Prop`
  exactly as in `BAGavLGEX`. No structure field carries a hypothesis.
- No cycle: `GbEXPav.lean` imports `BA.GreenLocal` and `BA.GreenCond2` only; neither imports `GbEXPav` (new file).
- No external hypothesis is introduced, so no limit check is owed.

## 4. Compiled nonempty instances

In the file (`GbEXPav.lean:28`), compiled by the module build:
```
example : BAGbEXPav 3 := baGbEXPav_holds 3 (by norm_num)
```
`d = 3`, the guard `2 ≤ 3` discharged; this is the ticket's target 4 verbatim. Audit-side extra check that the binders of the pin are
realised at concrete nondegenerate data (the merged flow instance of `GreenLocalInst`: `sz0`, `L = 4`, `W = 32`, `flow_sz0` with
`κ = 1/2, ε = 1/10, 𝔡 = 1/10, 𝔠 = 1/6`, `t ≡ 1/2 ≤ T₀`, `ε₀ = 1/10`):
```
$ cat inst.lean | sed -n 4,6p
example : BAGavLGEX sz0 zSeq (fun _ => 1 / 2) (1 / 10) :=
  baGbEXPav_holds 3 (by norm_num) (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 10) (by norm_num)
$ lake env lean inst.lean; echo exit $?
exit 0
```
Every deterministic hypothesis is discharged; what remains is `BAGavLGEX`'s own `∀ Ψ` with the window and `STInitialGT2gL` (the induction's
output, registry owed), as in the pin. Instance: **PASS**.

## 5. Build, axioms, hygiene

```
$ lake build RBM3D.BA.GbEXPav 2>&1 | grep -E "error|GbEXPav|Build completed"
Build completed successfully (3804 jobs).
$ lake build 2>&1 | grep -E "error:|Build completed"          # full library, runs #assert_rbm_axioms
Build completed successfully (4230 jobs).
$ lake build 2>&1 | grep -B2 -A2 "no project axioms"
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
$ lake env lean ax.lean
'RBM.BA.baGbEXPav_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baFAav_greenLocal' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/BA/GbEXPav.lean; echo "grep exit $?"
grep exit 1
$ lake env lean /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2422-check.lean >/dev/null; echo "check (branch) exit $?"
check (branch) exit 0
```
Build warnings are only pre-existing line-length/unused-hypothesis lints in other modules; none in `GbEXPav.lean`.
Names: `baFAav_greenLocal`, `baGbEXPav_holds` are the pinned names; no private helpers were needed.

## 6. Registry (target 3)

```
$ git diff main...t/T2422 -- RBM3D/Test/Axioms.lean   (summary of the 4 changed lines)
-  `RBM.BA.BAGbEXPii, ... (owner BA-G6)
-  `RBM.BA.BAGbEXPav, ... (owner BA-G6)
-  `RBM.BA.STInitialGT2gL, ... owner BA-G6b (the BA Step 1 / `(initialGT2)` chain)
+  `RBM.BA.STInitialGT2gL, ... owner BA-V (the BA Step 1 / main-induction chain), as the band's `STInitialGT2` (`Test/Axioms.lean:129`)
$ sed -n 129p RBM3D/Test/Axioms.lean | cut -c1-60
   `RBM.Gauss.Sizes.STInitialGT2, -- `(initialGT2)` (`3_5:28
$ lake build -v 2>&1 | grep -n "BAGbEXP\|STInitialGT2gL"   # usage table of the full-build registry check
10026:  RBM.BA.BAGbEXPij: 14 [no certificate]
10027:  RBM.BA.STInitialGT2gL: 4 [no certificate]
```
`BAGbEXPii` (proved by `baGbEXPii_holds`) and `BAGbEXPav` (proved here) removed; `BAGbEXPij` kept (G7); the `STInitialGT2gL` owner text is the
ticket's text verbatim and the cross-reference `:129` is correct on the branch. The registry check (`#assert_rbm_axioms`, unregistered-premise test)
passes in the full build: removing `BAGbEXPii` left no unclassified premise. Target 3: **PASS**.

## 7. Paper deltas

Only Lean/paper difference: the guard `2 ≤ d` (paper `d ≥ 3`, `7_8:1916-1946`), a weaker hypothesis than the paper's. It is the guard of the wiring
GL6 / GL2, already proposed as candidate `T2408b` (`docs/reports/T2408-prove.md:229`: "GL2, GL3, GL4, GL6 carry `2 ≤ d`") and `T2403a`
(`docs/reports/T2403-prove.md:83`). Neither is yet numbered in `docs/paper-deltas.md` (last change `fde321d`, Oct 9); the dispatcher
numbers them. Coverage: **PASS**.

## 8. Observations (no effect on verdict)

- O1. The prove report is 101 lines; the ticket asks for ≤ 80 (CLAUDE.md §6 limit 300 is met). Report-only defect.
- O2. Section (a) says the compared bodies are "12 lines each"; the script above gives 11 body lines plus the one-line header. Immaterial.

## Verdict

| target | verdict |
|---|---|
| 1 `baFAav_greenLocal` | PASS |
| 2 `baGbEXPav_holds` | PASS |
| 3 registry edits | PASS |
| 4 instance `BAGbEXPav 3` | PASS |
| 5 C1 (no new hypothesis) | PASS |

**T2422: PASS.** No dispatcher sign-off needed.
