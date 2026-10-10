Auditor model: claude-opus-5-5

# T2383 audit (round 1) — Sat Oct 10 12:33:05 UTC 2026

Inputs: ticket `docs/tickets/T2383.md`, Amend 1 `docs/tickets/T2383-amend-1.md` (sole writable `Induction/LoopGenN.lean`; `HierarchyN.lean` untouched; non-band instance, no `BA/*` import), prove report `docs/reports/T2383-prove.md`, branch `t/T2383` at `ddf93af` (merge-base `2192dea`), audit worktree `RBM3D-wt/T2383-audit1` (detached at `ddf93af`). Scratch: `scratchpad/T2383/`.

## 1. Diff scope, imports, forbidden tokens
```
$ git diff --numstat main...t/T2383
160	99	RBM3D/Induction/LoopGenN.lean
$ git diff --quiet main...t/T2383 -- RBM3D/Induction/HierarchyN.lean RBM3D/Test/Axioms.lean && echo ...
HierarchyN.lean, Test/Axioms.lean: no diff
$ git diff --name-only 2192dea main -- RBM3D/Induction/LoopGenN.lean RBM3D/Induction/HierarchyN.lean | wc -l
0            (main moved to ada2b54 since the merge-base; neither file touched there)
$ grep '^import' (branch LoopGenN.lean)
import RBM3D.Induction.HierarchyN
import RBM3D.Hierarchy.ContractionSecondLoop
import RBM3D.Hierarchy.ContractionBasic
import RBM3D.Gauss.LoopCoordinate
import RBM3D.Gauss.LoopGenerator          (unchanged from main; no BA/* import)
$ grep -nE 'sorry|admit|native_decide|^axiom|^\s*axiom ' (branch LoopGenN.lean)
none
$ diff <public decls main> <public decls branch>
0a1,2
> def genMatOf
> theorem genMat_eq_genMatOf
4a7,8
> theorem loopGenNOf
> theorem recovers_loopGenN
```
No public declaration removed; four added (all probe names; prove report's grep: no clash). New private helper `LoopGenN_hasDerivAt_ztOf` carries the file stem.

## 2. Statement checks (script diffs)

Target 1, generic block against the probe `t/T2379:RBM3D/Probe/T2379Pins.lean` (the ticket's pin):
```
$ blk(){ awk '/^def genMatOf /{p=1} p&&/^end GenBlock|^\/-- \*\*`loopGenN`\*\*/{exit} p{print}' "$1"; }
$ diff <(blk probe.lean) <(blk branch LoopGenN.lean)     # genMatOf, genMat_eq_genMatOf, loopGenNOf (statement + proof)
genMatOf..loopGenNOf block probe/branch lines: 77/77
IDENTICAL
$ diff <recovers_loopGenN probe> <recovers_loopGenN branch>
recovers_loopGenN IDENTICAL
```
`loopGenNOf` hypotheses: `3 ≤ L`, `0 < m.im`, `u < 1`, `M.IsHermitian`; `g`, `E`, `W`, `d`, `k`, `σ`, `a` free. No `|E| < 2`, no structure argument. Flow `ztOf m E u = E + (1-u) m` (`Loop/GLoopFlow.lean:55`, merged), drift `PropSpin m` (`Propagator/Pins.lean:30`, merged: `if σ then m else conj m`). `genMat_eq_genMatOf : genMat .. E .. = genMatOf .. (mE E) E ..` closes by `rfl`.

G1 (band statements unchanged; targets 1, 3):
```
$ diff <main loopGenN statement> <branch loopGenN statement>
13c13
<           loopL d L W (blockMat d L W M) (zt E u) ((loopOf σ a).cutGlue k' y) := by
---
>           loopL d L W (blockMat d L W M) (zt E u) ((loopOf σ a).cutGlue k' y) :=
(only the proof separator differs; statement text identical)
$ (statement md5, main vs branch)
stLoopGenNForm_holds stmt main==branch: yes
hierarchyN_holds stmt main==branch: yes
LoopGenN_check_stLoopGenNForm_sz0 stmt main==branch: yes
LoopGenN_check_hierarchyN_sz0 stmt main==branch: yes
LoopGenN_check_loopGenN stmt main==branch: yes
```
Auditor G1 file `scratchpad/T2383/G1audit.lean` (imports `RBM3D.Induction.LoopGenN`, `RBM3D.Induction.HierarchyN`): `example <main's loopGenN statement, verbatim> := loopGenN ..`; `example (d) : STLoopGenNForm d := stLoopGenNForm_holds d`; `example (d) : HierarchyN d := hierarchyN_holds d`; `example (d) : HierarchyN d := hierarchyN_of_loopGenN d (stLoopGenNForm_holds d)`; `example : type_of% @loopGenN := recovers_loopGenN`; non-band facts (`¬ |3| < 2`, `0 < I.im`, `ztOf I 3 (1/2) = 3 + (1/2) I`).
```
$ cd RBM3D-wt/T2383-audit1 && lake env lean scratchpad/T2383/G1audit.lean; echo exit=$?
'RBM.Ind.loopGenNOf' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ lake env lean docs/tickets/checks/T2383-check.lean   (audit worktree, then main worktree)
check-file exit (branch)=0
check-file exit (main)=0
check-file #check output main == branch (      32 lines)
```
`HierarchyN.lean` is byte-identical to main (§1), so its declarations' G1 holds trivially (Amend 1).

## 3. Vacuity, hidden hypotheses, cycles
- No hypothesis in a structure field: `loopGenNOf` takes only explicit `Prop` hypotheses `hL`, `hm`, `hu1`, `hM`; none is `False` at the instance below.
- No cycle: `loopGenNOf` precedes `loopGenN` in the file and the band theorem is the term `loopGenNOf d L W g (mE E) E hL (mE_im_pos hE) u hu1 M hM σ a`; `stLoopGenNForm_holds`/`hierarchyN_holds` keep their main proofs. Imports unchanged (all merged modules).
- No external hypothesis (the identity is deterministic); no limit check needed.

## 4. Compiled nonempty instances (section `Instances`, branch `LoopGenN.lean:760-768`)
```
example :=
  loopGenNOf 3 3 2 (1 / 2) Complex.I 3 le_rfl (by simp) (1 / 2) (by norm_num)
    LoopGenN_M0 LoopGenN_M0_isHermitian ![true, false, true] ![(0 : Zd 3 3), 1, 2]
example :=
  loopGenNOf 3 3 2 (1 / 2) (mE (1 / 2)) (1 / 2) le_rfl (mE_im_pos (by norm_num [abs_of_pos])) (1 / 2)
    (by norm_num) LoopGenN_M0 LoopGenN_M0_isHermitian ![true, false, true] ![(0 : Zd 3 3), 1, 2]
```
Non-band instance (Amend 1): `m = i` (`0 < m.im` by `simp`), `E = 3` (`¬|E| < 2`, checked above), `d = 3`, `L = 3`, `W = 2` (216 sites), `g = 1/2`, `u = 1/2`, `k = 3`, loop `(+,-,+)`, `M = LoopGenN_M0` Hermitian with entry `(0,1) = 1` (`LoopGenN_M0_apply`, merged). Every hypothesis discharged; nondegenerate; no `BA/*` import. The band corollary `loopGenN` keeps its merged instance `LoopGenN_check_loopGenN`; `stLoopGenNForm_holds`/`hierarchyN_holds` keep `..._sz0` checks (statements unchanged, §2). `genMat_eq_genMatOf` and `recovers_loopGenN` are bridges (`rfl` / term) with no hypotheses.

## 5. Build and axioms (audit worktree)
```
$ lake build RBM3D.Induction.LoopGenN 2>&1 | grep -Ei "error|warning|sorry|axioms|Build completed" | tail
(error lines: none; warnings only in RBM3D/Path/Markov.lean: line length / unused variable, pre-existing, not in the diff)
info: RBM3D/Induction/LoopGenN.lean:776:0: 'RBM.Ind.loopGenNOf' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/LoopGenN.lean:777:0: 'RBM.Ind.loopGenN' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/LoopGenN.lean:778:0: 'RBM.Ind.recovers_loopGenN' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/LoopGenN.lean:779:0: 'RBM.Ind.genMat_eq_genMatOf' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/LoopGenN.lean:780:0: 'RBM.Ind.stLoopGenNForm_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/LoopGenN.lean:781:0: 'RBM.Ind.hierarchyN_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3756 jobs).
```
Registry (target 6): theorems/def only, no owed pin; `Test/Axioms.lean` untouched. Full `lake build` is the hub's at merge.

## 6. Tripwire (target 5, binding C6) and stop line
```
$ git diff -U0 main...t/T2383 -- RBM3D/Induction/LoopGenN.lean | <hunk counter>
added in block (new line <650): 139  added after: 21  removed: 99
g (block, /568) = 0.245 ; g (two files, /804) = 0.173
$ wc -l: main 720, branch 781
```
`g = 0.245 ≤ 0.5`; `f_sem = 0` (the 21 lines after the block are `recovers_loopGenN`, the two instance `example`s and 3 `#print axioms`; no band text moved into an instance) `≤ 0.30`. Tripwire does not fire. Net diff 259 lines < stop line 800. Matches the prove report.

## 7. Paper deltas
`ztOf m E t = E + (1-t) m` is the paper's `(eq:zt)` with `m` as data (`paper/tex/1_2_Intro_model_result.tex:716`); at `m = mE E` the generic identity is exactly the merged band `loopGenN` (`eq:mainStoflow`, drift part with `def_EwtG`), shown by `recovers_loopGenN`. The generic version assumes only `0 < m.im` (not that `m` solves `(self_m)`), a weakening of hypotheses for an algebraic identity, not a change of the paper's statement. No Lean/paper statement difference; "none" (prove report (d)) is accepted.

## 8. Observations (no effect on verdict)
- O1. Prove report section (a) still lists target 4 as "PASS (BA instance, import `BA/FlowPins`)"; superseded by Amend 1 and recorded in (a′) and (d). The branch follows Amend 1.
- O2. The prove report's G1 checks were run from a scratch file; this audit reran them independently (§2).
- O3. Two extra blank lines introduced in the private-lemma region (cosmetic).

## Verdict per target
| target | verdict |
|---|---|
| 1 `LoopGenN.lean` generic `loopGenNOf` (probe text, identical) + band `loopGenN` corollary, old name/statement | PASS |
| 2 `HierarchyN.lean` (Amend 1: band-only, 0 edits) | PASS (untouched, verified) |
| 3 G1 checks | PASS |
| 4 instance (Amend 1: non-band `m = i`, `E = 3`, no `BA/*` import) | PASS |
| 5 tripwire `g = 0.245`, `f_sem = 0` | PASS (no fire) |
| 6 registry | PASS (no new owed line) |

**Overall: PASS.** No dispatcher sign-off needed.
