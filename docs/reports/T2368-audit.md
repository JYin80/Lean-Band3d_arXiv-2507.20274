Auditor model: claude-opus-5-5

# T2368 audit, round 2 (BA-K03, `RBM3D/BA/KSolve.lean`; Amend 1: one `owedProps` line), Sat Oct 10 04:10:09 UTC 2026

Branch `t/T2368` at `f3004f5`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2368-audit2` (detached, fresh build cache).
Scope (CONTROL H163): the ticket and Amend 1. Scratch files: `<scratchpad>/T2368/`.

## 1. Amend 1: `git diff 057f0f4..HEAD` is exactly the pinned line
```
$ git diff --stat 057f0f4..t/T2368
 RBM3D/Test/Axioms.lean | 1 +
 1 file changed, 1 insertion(+)
$ grep -o '`` `RBM.BA.BAKsolve.*removes this line ``' docs/tickets/T2368-amend-1.md | sed 's/^`` //; s/ ``$//' > pin_line.txt
$ git diff -U0 057f0f4..t/T2368 | grep '^[+-]' | grep -v '^+++\|^---' > diffl.txt; wc -l < diffl.txt
       1
$ sed 's/^+ *//' diffl.txt > got.txt; diff pin_line.txt got.txt && echo LINE_MATCH
LINE_MATCH
$ git show t/T2368:RBM3D/Test/Axioms.lean | grep -n 'STLocalMaxgL, --\|BA.BAKsolve' | cut -c1-60
140:   `RBM.BA.STLocalMaxgL, -- `(Gt_bound+IND)` at a law `μ` o
141:   `RBM.BA.BAKsolve, -- existence of the BA `𝒦` on `[0,1)` w
$ git diff --stat a5c1a1a main -- RBM3D/Test/Axioms.lean    # main has not touched the file since the merge base
(no output)
```
Placement: inside `owedProps`, directly after the `STLocalMaxgL` line, as Amend 1 pins. `KSolve.lean` unchanged since 057f0f4.

## 2. Registry pre-check (temporary, uncommitted, scratchpad)
```
$ cat RegPre.lean
import RBM3D
import RBM3D.BA.KSolve

#assert_rbm_axioms
$ lake build RBM3D   (worktree root, needed for `import RBM3D`)
Build completed successfully (4177 jobs).
$ lake env lean RegPre.lean; echo "exit=$?"     (excerpt)
axiom audit: 10762 theorems, 3156 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: ...
  RBM.BA.BAKsolve: 6 [no certificate]
premises found by scanning: 134 (borrowed 1, owed 72, structural 42, refuted 6, superseded 13).
registry: 2 borrowed + 126 owed + 109 structural + 7 refuted + 14 superseded; 124 registered premise(s) carry nothing yet: [...]
exit=0
```
The 6 theorems on `BAKsolve` are `BAKsol_isKLoopS`, `BAKsol_rotate`, `BAKsol_translate`, `KSolveInst.{unique,rotate,translate}_inst`.

## 3. Statements against the pins (check file Part 1) and the ticket
```
$ { check file lines import..`end RBM.BA.T2368Check` + `import RBM3D.BA.KSolve`; then: }
example : @RBM.BA.IsKLoopSLe = @RBM.BA.T2368Check.IsKLoopSLe := rfl
example : @RBM.BA.BAKsolve = @RBM.BA.T2368Check.BAKsolve := rfl
example : @RBM.BA.BAKsolveLe3 = @RBM.BA.T2368Check.BAKsolveLe3 := rfl
example : ∀ d, RBM.BA.T2368Check.BAKsolveLe3 d := RBM.BA.baKsolveLe3_holds
$ lake env lean AuditPins.lean; echo "exit=$?"     -> no errors (axiom lines in §5), exit=0
$ lake env lean docs/tickets/checks/T2368-check.lean >/dev/null 2>&1; echo "exit=$?"   (on the branch)
exit=0
```
Other targets, read from the signatures (`KSolve.lean:521-640`):
- `BAMLoop_rot`: `BAMLoop d L W M ⟨s :: σ, b :: a⟩ = BAMLoop d L W M ⟨σ ++ [s], a ++ [b]⟩` under `σ.length = a.length`, any `M`: the `RotS` hypothesis at `M = BAMLoop`, as the ticket asks.
- `BAMLoop_translate`: under `∀ σ x y c, M σ (x+c) (y+c) = M σ x y`; `BAMsigma_shift`: that hypothesis for `BAMsigma d L (BAMB d L g z m)` with no extra hypothesis.
- `baK_unique`: two `IsKLoopS d L W 1 m (BAMLoop d L W Ms) (Set.Ico 0 1)` solutions agree for all `t ∈ [0,1)`, `I.WF`, `2 ≤ I.length`; no bound hypothesis (it is derived from `retireS_holds`). Matches the ticket; stronger than probe `baK_unique_of_UniqS` (no `R`, no `UniqS` premise).
- `baK_rotate`, `baK_translate`: conclusions are verbatim the bodies of `KLK_rotate` (`Loop/KLUnique.lean:713-716`) and `KLK_translate` (`:257-260`) with `KLK` replaced by `K`; generic `m`, `Ms`; translate needs exactly the ticket's `Ms` shift hypothesis.
- `BAKsol_isKLoopS`: identical to the probe `t/T2360:RBM3D/Probe/T2360Pins.lean` text (`h : BAKsolve d`, `Λ κ L W g E m`, `0<Λ`, `0<κ`, `3≤L`, `0<g≤Λ`, `BAReal`). `BAKsol_rotate/translate`: the same hypotheses, conclusions = `baK_rotate/translate` at `BAKsol`.
Verdict on statements: all match pins / ticket mathematics; no special case passed off as general.

## 4. Hidden hypotheses, vacuity, cycles
- New defs are the three pins only (rfl-equal to the check copies); no structure/class introduced (`grep '^structure\|^class'`: none).
- `baKsolveLe3_holds` uses only `BAReal`, `3 ≤ L` (via `NeZero L`), `t ∈ [0,1)`; `W` arbitrary (prove report T2368a: stronger than paper `W ≥ 1`).
- `BAKsolve` is a hypothesis only of `BAKsol_*` and the three `_inst`; it is K05b's owed target, now registered in `owedProps` (Amend 1). Not an external input; partial consistency evidence: `baKsolveLe3_holds` gives levels `n ≤ 3` with the same `(Kn2sol)`.
- Dependencies: `uniqS_holds`, `retireS_holds`, `rotS_holds`, `translS_holds`, `kernel_one_rot_transl` (merged T2366), `BA/KBase` (merged), `BAMB_shift` (`BA/Ward`). No cycle (new file, imports only merged modules).

## 5. Build, axioms, hygiene
```
$ lake build RBM3D.BA.KSolve 2>&1 | grep -E '^error|Build completed'; lake build RBM3D.BA.KSolve 2>&1 | grep -c 'KSolve.lean'
Build completed successfully (3740 jobs).
0
$ lake env lean AuditPins.lean   (#print axioms part)
'RBM.BA.baKsolveLe3_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baK_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baK_rotate' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baK_translate' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMLoop_rot' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMLoop_translate' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMsigma_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAKsol_isKLoopS' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAKsol_rotate' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAKsol_translate' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KSolveInst.le3_nondeg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KSolveInst.rot_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KSolveInst.translate_BAMLoop' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KSolveInst.unique_inst' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KSolveInst.rotate_inst' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KSolveInst.translate_inst' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^axiom' RBM3D/BA/KSolve.lean RBM3D/Test/Axioms.lean   (non-comment hits)
RBM3D/Test/Axioms.lean:18:Any `sorry` (`sorryAx`) therefore breaks the build, and so does any new `axiom` that has
$ git diff --name-only main...t/T2368
RBM3D/BA/KSolve.lean
RBM3D/Test/Axioms.lean
$ wc -l RBM3D/BA/KSolve.lean
     767 RBM3D/BA/KSolve.lean        (stop line 1400)
```
The `Axioms.lean:18` hit is docstring prose. Both touched files are sole writable files (ticket + Amend 1); no existing signature changed.

## 6. Compiled nonempty instances (namespace `RBM.BA.KSolveInst`, data `P` of `BA/MFixedPoint`, `d=3`, `L=4`, `W=2`, `Λ=10`, `κ=Im m₀`)
- `baKsolveLe3_holds`: `example` at `KSolve.lean:655`, every hypothesis discharged (`P.real`, `P.g0_pos`, `P.g0_le`, `norm_num`); `le3_nondeg` proves the 2-loop at `t=0`, `σ=(+,-)`, `a=(0,0)` equals `8⁻¹·m₀·conj m₀` and is `≠ 0`.
- `BAMLoop_rot`: `rot_witness` at the K00 witness `BAMLoop_witM` (value `15`, nonzero).
- `BAMsigma_shift`: `example` at `P`, shift `e₁`; `BAMLoop_translate`: `translate_BAMLoop` on a 3-loop, plus a nonzero 2-loop.
- `baK_unique` / `baK_rotate` / `baK_translate` / `BAKsol_*`: `unique_inst`, `rotate_inst` (lengths 2 and 3), `translate_inst` (lengths 2 and 3) at `t = 1/2`, with `BAKsolve 3` (K05b's pin, not yet proved) as the only remaining hypothesis; all deterministic hypotheses discharged. The family of `baKsolveLe3_holds` only solves `n ≤ 3`, so a full-length `IsKLoopS` family requires that pin (CLAUDE.md §4 step 2 allows it).
All compile (§5 axioms lines). None degenerate.

## 7. Paper deltas
Prove report (d): T2368a (`W ≥ 1` dropped, stronger, proved), T2368b (`(Kn3sol)` with K00 convention, cites D632/D634: present in `docs/paper-deltas.md:1591,1593`), T2368c (ticket wording). Amend 1 adds a registry line, no statement change, so no new delta. Coverage complete.

## Observations (no verdict effect)
- O1. Public example-names `le3_nondeg`, `rot_witness`, `translate_BAMLoop`, `unique_inst`, `rotate_inst`, `translate_inst` are scoped by namespace `KSolveInst` rather than `private`/stem prefix (rule (E)); unchanged since round 1.
- O2. The repair section's pasted pre-check prints `exit 0` before the output excerpt (ordering of the paste); my rerun in §2 gives exit 0.

## Verdict
| Target | Verdict |
|---|---|
| `IsKLoopSLe`, `BAKsolve`, `BAKsolveLe3` (pins) | PASS |
| `baKsolveLe3_holds` | PASS |
| `baK_unique`, `baK_rotate`, `baK_translate` | PASS |
| `BAMLoop_rot`, `BAMLoop_translate`, `BAMsigma_shift` | PASS |
| `BAKsol_isKLoopS`, `BAKsol_rotate`, `BAKsol_translate` | PASS |
| Amend 1 (one `owedProps` line; registry pre-check exit 0) | PASS |

**T2368: PASS.** No dispatcher sign-off needed.
