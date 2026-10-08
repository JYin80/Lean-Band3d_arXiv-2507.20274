Auditor model: claude-opus-5-5

# T2343 audit (round 1) — UN-34/35 `Universality/GUEPhase/Drift.lean`

Written Thu Oct  8 20:37:51 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2343-audit1`, detached at `t/T2343` = d577e3b (merge-base with `main` 84cd789; `main` now 03ec112).

## 1. Diff scope and the OneStep edit

```
$ git diff --stat main...t/T2343
 RBM3D/Path/OneStep.lean                |   42 +-
 RBM3D/Universality/GUEPhase/Drift.lean | 1474 ++++++++++++++++++++++++++++++++
 2 files changed, 1495 insertions(+), 21 deletions(-)
$ git diff -U0 main...t/T2343 -- RBM3D/Path/OneStep.lean | python3 -I -c '<pair removed/added lines>'
removed 21 added 21
each added = removed minus leading private: True
hunk lines: +851 +1179 +1188 +1194 +1204 +1264 +1278 +1283 +1288 +1305 +1314 +1336 +1344 +1379 +1391 +1418 +1435 +1498 +1507 +1597 +1625
```
Both files are the sole writable files. Every hunk falls in `:809-1666` and only deletes `private` (the ticket's allowed edit). No frozen signature was changed.

Name clashes against current `main` (03ec112):
```
$ git grep -nwE "(def|theorem|lemma|abbrev) (<21 un-privated OneStep_ names>)" main -- RBM3D | grep -v Path/OneStep.lean | wc -l
       0
$ git grep -nwE "oneStepEnvelopeGUE|gueH_succ|condExp_loop_step_gue|condExp_loop_drift_gue|DriftInst|labels_sz0|..._check" main -- RBM3D RBM3D.lean | grep -v Probe/ | wc -l
       0
$ git diff --stat 84cd789 main -- RBM3D/Path RBM3D/Universality/GUEPhase RBM3D.lean
 RBM3D.lean | 5 +++++      (root imports only; no upstream source of this ticket changed)
```

## 2. Build, hygiene, axioms

```
$ lake build RBM3D.Universality.GUEPhase.Drift RBM3D.Path.OneStep ; echo EXIT=$?
Built RBM3D.Path.OneStep (19s)
Built RBM3D.Universality.GUEPhase.Drift (8.0s)
Build completed successfully (3773 jobs).
EXIT=0
$ grep -c error build.log ; grep '^warning' build.log | sed 's/:.*//' | sort -u
0
(warnings only in replayed upstream modules: Defs/Tail, Green/*, Path/Markov, Path/Walk, Propagator/*; none in OneStep or Drift)
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom |unsafe|implemented_by|opaque " Drift.lean
(no output)
$ grep -n "^import" Drift.lean
6:import RBM3D.Path.LoopStep
7:import RBM3D.Universality.GUEPhase.Generator
8:import RBM3D.Universality.GUEPhase.Markov
```
Non-private declarations (all others, 70 lines, are `private`):
```
756:theorem oneStepEnvelopeGUE         925:theorem gueH_succ
1208:theorem condExp_loop_step_gue     1318:theorem condExp_loop_drift_gue
1371,1422,1431,1449: DriftInst.*_check (4)   1391: DriftInst.labels_sz0
```
`labels_sz0` is an unpinned public name, but it sits in the instance namespace `DriftInst`. That is an observation, not a defect.

## 3. Statement against the pin (check-file equality) and axioms

The scratch file `check_eq.lean` holds the check file's imports, `import RBM3D.Universality.GUEPhase.Drift`, the check file's section 2 with the `#check` lines removed, then the four equality examples and the `#print axioms` lines.
```
example : RBM.Univ.GUEPhase.T2343Check.T2343_oneStepEnvelopeGUE := @RBM.Univ.GUEPhase.oneStepEnvelopeGUE
example : RBM.Univ.GUEPhase.T2343Check.T2343_gueH_succ := @RBM.Univ.GUEPhase.gueH_succ
example : RBM.Univ.GUEPhase.T2343Check.T2343_condExp_loop_step_gue := @RBM.Univ.GUEPhase.condExp_loop_step_gue
example : RBM.Univ.GUEPhase.T2343Check.T2343_condExp_loop_drift_gue := @RBM.Univ.GUEPhase.condExp_loop_drift_gue
$ lake env lean check_eq.lean ; echo EXIT
'RBM.Univ.GUEPhase.oneStepEnvelopeGUE' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.gueH_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.condExp_loop_step_gue' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.condExp_loop_drift_gue' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.DriftInst.oneStepEnvelopeGUE_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.DriftInst.condExp_loop_drift_gue_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.DriftInst.condExp_loop_step_gue_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.DriftInst.gueH_succ_check' depends on axioms: [propext, Classical.choice, Quot.sound]
def RBM.Gauss.SizesInst.sz0 : Sizes 3 :=
{ L := fun n => 4 * (n + 1), W := fun n => (2 * (n + 1)) ^ 5, lam := fun n => ((2 * (↑n + 1)) ^ 6)⁻¹,
EXIT=0
```
All four definitional-equality examples elaborate with no error. So each Lean statement is exactly the dispatcher's pinned text, with the same hypotheses, quantifier order, `d`-general dimensions, envelope `envConst d L W` and exponent `Δ^{3/2}`. All four targets hold for every `d`, `L`, `W` (`NeZero`), or for every `sz : Sizes d`. None assumes `3 ≤ d`, none is a special case, and none has an `∀ᶠ`.

## 4. Hidden hypotheses, vacuity, cycles

- The statements carry no structure-field hypotheses beyond the merged `Sizes d` (`Defs/Sizes.lean:138`). Its fields are `three_le_L : ∀ n, 3 ≤ L n` and `W_pos : ∀ n, 0 < W n`, both satisfiable; `sz0` meets them.
- `envConst` (`OneStep.lean:78`) is `16 (k+3)^4 ((W L)^d)^4 (1 + (etaT E v)⁻¹)^(k+4)`, which is finite. The hypotheses `|E|<2`, `0≤u`, `0≤Δ`, `u+Δ<1` and `WF` are jointly satisfiable (§5), so the statements are not vacuous.
- Dependencies are all merged modules on `main`: `Path/LoopStep`, `Path/OneStep`, `GUEPhase/Generator`, `Grid`, `Markov`. `condExp_loop_drift_gue` uses `condExp_loop_step_gue`, `oneStepEnvelopeGUE` and the merged `gueH_isHermitian` (`Grid.lean:164`), so there is no cycle.
- There is no external hypothesis, so no limit check is owed. `K n ≠ 0` and `k < K n` are pinned but unused (`intro … _hK _hk`). This matches the band twin (D151).

## 5. Compiled nonempty instances (Drift.lean §14, namespace `DriftInst`)

| target | instance | data | hypotheses discharged |
|---|---|---|---|
| `oneStepEnvelopeGUE` | `oneStepEnvelopeGUE_check` :1371 | d=3, L=W=2 (N=64), E=0, u=0, Δ=1/4, M=0, loop `⟨[true],[0]⟩` (one edge) | `by norm_num` (\|E\|<2, 0≤Δ, u+Δ<1), `le_rfl`, `DriftInst_loop1_wf := rfl`, `Matrix.isHermitian_zero` |
| `gueH_succ` | `gueH_succ_check` :1422 | sz0, n=0, k=0, t1=(1−ouZeta(1/20))·9/10, t0=9/10, K=4 | no hypotheses |
| `condExp_loop_step_gue` | `condExp_loop_step_gue_check` :1431 | sz0 (L₀=4, W₀=32), n=k=0, E=0, loop `(+,−;0,1)` | `by norm_num`, `DriftInst_loop2_wf`, `DriftInst_gridTime_lt` (proved) |
| `condExp_loop_drift_gue` | `condExp_loop_drift_gue_check` :1449 | same | plus `DriftInst_t1_nonneg`, `DriftInst_t1_le_t0` (proved), `K≠0`, `0<K` by `norm_num` |

These match the ticket's instance spec: `d=3`, `L=W=2`, `E=0`, `u=0`, `Δ=1/4`, `M=0`, a one-edge loop, plus the `GridCheck` sizes. Every deterministic hypothesis is discharged by a proof term and nothing remains as a premise. The data are nondegenerate: N=64 and N=(32·4)^3; the step is Δ_g=(t0−t1)/4>0 because t1=e^{-1/20}·0.9<0.9; and `labels_sz0` shows the two loop labels are distinct (0≠1 in `Z_4^3`). The constants are of ordinary size: the witness does not rely on an astronomically large quantity, since `envConst` is the statement's own bound. All four instances compiled (§2 build; axioms in §3).

## 6. Paper deltas

- The bound `envConst · Δ^{3/2}` (the merged band envelope, `N^4` with `N=(W L)^d`) and the unused `K n ≠ 0` and `k < K n` are the same Lean/paper differences that D151 already records for the band twin `condExp_loop_drift`. Prove report (d) states them for the GUE twin ("Carried from the pin …").
- No other statement differs from the source shape (§3 equality with the pin, which the dispatcher built from the band twins).
- Observation: the report does not tag this as `T2343a`. The dispatcher may extend D151 by one clause, "and its GUE twins `oneStepEnvelopeGUE` / `condExp_loop_drift_gue` (T2343)". This affects no statement.

## 7. Observations (no RETURN)

- O1: the unpinned public `DriftInst.labels_sz0` is in the instance namespace. §3 (E) is satisfied in spirit, but it could have been `private`.
- O2: §6, the GUE twin is not tagged in paper-deltas (D151 covers the content).
- O3: prove report (b) says the full build ran at 6fe322f. The last commit, d577e3b, changes docstrings only. `main` has since advanced to 03ec112 (root imports only); the hub's merge build covers this.

## Verdicts

| target | verdict |
|---|---|
| `oneStepEnvelopeGUE` | PASS |
| `gueH_succ` | PASS |
| `condExp_loop_step_gue` | PASS |
| `condExp_loop_drift_gue` | PASS |

Ticket T2343: **PASS**. No dispatcher sign-off is needed.
