Auditor model: claude-opus-5-5

# T2523 audit, round 2 (Sat Oct 17 07:54:39 UTC 2026)

`t/T2523` 89856dac (repair on 8395d2d6), worktree `RBM3D-wt/T2523-audit2`; base e3540151. Main 857542e6 changes no file under
`RBM3D/`, `RBM3D.lean`, the tool or the check file since the base. `$S` = scratch `T2523/audit2/`; `$R` = scratch `T2523/` (round-1 scripts).
Scope: Amend 1 D1 items 1-3, the D2 sign-offs, and round 1's A1-A7 after the repair.

**Verdict: PASS.** D1 items 1-3 are done and checked independently. The D2 (a) and (b) sign-offs apply. A1-A7 still hold.

## B1. The repair commit: deletions only, the five names gone (D1 item 1)
```text
$ git diff --stat 8395d2d6 89856dac
 RBM3D/Graph/BALocReg1B.lean           | 25 -------------------------
 RBM3D/Green/MinorDiff.lean            | 33 ---------------------------------
 docs/claude-team/tools/DeadDecls.lean |  5 -----
 3 files changed, 63 deletions(-)
$ git diff 8395d2d6 89856dac | grep '^[+]' | grep -v '^+++' | wc -l
       0
$ grep -rnwE 'toyHalf|toyPow|BALocReg1B_extMap|sqrt_four|mE_zero|RelabelOps' RBM3D RBM3D.lean docs/claude-team/tools/DeadDecls.lean | wc -l
       0
$ python3 -I $R/cmp2.py $R/consts_br.txt $S/consts_br2.txt     # round-1 branch constants vs repaired branch (RBM namespace, type/value hashes)
user-facing (aux filtered): common 25311  new-on-branch 0  type-hash diffs 0  def-value/ctor diffs 0
removed since round 1: 6   RBM.Graph.BALocReg1B_extMap (+ .match_1), MinorDiffInst.{mE_zero, sqrt_four, toyHalf, toyPow} (private)   added: 0
```
The deleted scopes are namespace `MinorDiffInst` and its `noncomputable section` (now empty), and sections `RelabelOps` and `Inst` in
`BALocReg1B.lean`. `Inst` then held only an `open` and a heading comment. The deleted lines include those scopes' heading comments.

## B2. A per-name reason for each of the 80 remaining `restoredRoots` names (D1 item 2)
The report's R-C table gives one use site per name. Each site was checked against the branch source:
```text
$ python3 -I $R/r1.py <wt> restoredRoots | tail -1; (counts of identifier references, comments stripped)
80 names        # 3 with 0 references (the three @[simp] lemmas), 77 with >= 1
$ python3 -I $S/site.py <wt> docs/reports/T2523-prove.md     # each R-C "first use file:line" line contains the name as a token
site lines containing the name: 77 missing: 0
  (6 sites are inside local tactic macros: BALocReg2_simp0 (BALocReg2.lean:258-260), lwEngine_nws (LWEngine.lean:478), localReg2_msnormx
   (LocalRegular2.lean:1190); inspected: each macro's simp list names the lemma)
```
Are the using declarations kept for their own sake? A scratch copy of the tool with `restoredRoots := []` and nothing else changed
(`diff`: line 82 only) was run on the built branch:
```text
$ lake env lean $S/DeadNoR1.lean > $S/toolNoR1.out      # exit 0
- (35 constants in RBM.Audit and its sub-namespaces; 34958 in-scope constants reached in the core)
- declarations (non-meta units): 22733; meta declarations: 69 (unreached meta: 60)
- unreached (non-meta): 80
- modules with no reached declaration: 0
$ (names of the 80 unreached in section (b)) vs (restoredRoots names): diff
unreached(no restoredRoots) == restoredRoots: 80 names
```
So without these roots, the unreached declarations are exactly the 80 restored names. Every other declaration, including every use site
above, is reached from the core, G1-G4 and `scanProvers`. Each restored name is named in the source of a reached proof but leaves no trace
in its term, which is the stated reason.

The three zero-reference `@[simp]` lemmas, each deleted in a scratch copy of its module and compiled against the repaired branch build:
```text
$ awk 'NR!=190' RBM3D/BA/GreenMinor3.lean > $S/GM3_del.lean; lake env lean $S/GM3_del.lean      # GreenMinor_a_zero
GM3_del.lean:442:8: error: Type mismatch: After simplification, term      exit 1, 1 error  (GreenMinor_diffBd_atom, `simpa using h`)
$ awk 'NR<89||NR>92' RBM3D/Gauss/LoopFlowStein.lean > $S/LFS_del.lean; lake env lean $S/LFS_del.lean   # wordDirectionMap_nil
LFS_del.lean:194:8: error: unsolved goals                                  exit 1, 1 error  (loopWordDeriv_split, case nil)
$ awk 'NR<141||NR>142' RBM3D/Green/MinorDiffCond.lean > $S/MDC_del.lean; lake env lean $S/MDC_del.lean  # badTower_zero
MDC_del.lean:235:9: error: unsolved goals                                  exit 1, 1 error  (meas_badTower_le, case zero)
```
These match the report's R-B, which ran on 8395d2d6. All three failing proofs are reached (no-R1 run above).

## B3. Full build in the audit worktree (D1 item 3; 06:23:08-07:51:23 UTC)
```text
$ lake build > $S/build.log 2>&1; grep -c '^error' $S/build.log; grep -n 'axiom audit:\|premises found\|^registry:\|Build completed\|^exit' $S/build.log
0
7013:info: RBM3D.lean:656:0: axiom audit: 10486 theorems, 3858 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
7119:premises found by scanning: 94 (borrowed 1, owed 36, structural 57, refuted 0, superseded 0).
7120:registry: 2 borrowed + 98 owed + 130 structural + 3 refuted + 4 superseded; 143 registered premise(s) carry nothing yet: [...
7264:Build completed successfully (4426 jobs).
7265:exit 0
$ grep -n 'unregistered' RBM3D/Test/Axioms.lean | sed -n 2,3p
532:  let unregistered := found.filter fun n => !classified.contains n
533:  unless unregistered.isEmpty do
$ tail -1 RBM3D.lean
#assert_rbm_axioms
```
The build passed and the scan throws on any unregistered premise, so `unregistered: []`. The definition count dropped by 1 from round 1
(3859 -> 3858): `BALocReg1B_extMap`. The scan and registry lines are unchanged.

## B4. Tool rerun, check file, axioms (07:51:50-07:53:44 UTC)
```text
$ lake env lean docs/claude-team/tools/DeadDecls.lean > $S/tool.out     # exit 0
DeadDecls report: modules 6766, in scope 656, constants in scope 42483, counted declarations 22802
- (35 constants in RBM.Audit and its sub-namespaces; 35038 in-scope constants reached in the core)
- every core root reached: true
- declarations (non-meta units): 22733; meta declarations: 69 (unreached meta: 60)
- unreached (non-meta): 0
- modules with no reached declaration: 0
- roots: 20 / 31 / 3 / 16 (G1-G4); already reached in the core: all; not reached in the core: 0
- totals over 9 name lists: 240 names, 237 in scope, 0 unreached in the core
## (c) ... (none)
$ grep -c 'core: restored by T2523' $S/tool.out; grep -c 'core: kept by T2523' $S/tool.out
80
42
$ lake env lean /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2523-check.lean     # check file: not touched by the branch
exit 0, errors 0
$ lake env lean $S/ax.lean      # scratch, not committed
'RBM.Endpoints.final_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThm27L_any' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.bUniv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThm27L_of_ML' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baEnd_BUnivL_of_ML' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Counts: 22733 - 22543 (T2522 core + G1-G4, the report's figure) = 190 = 80 (R1) + 110 (R2). Every figure in the report's repair
section (R-A, R-D) matches B3-B5.

## B5. D2 sign-offs (Amend 1) and diff scope
```text
$ git diff --shortstat main...t/T2523; git diff --shortstat main...t/T2523 -- RBM3D RBM3D.lean
 650 files changed, 484 insertions(+), 149231 deletions(-)
 649 files changed, 291 insertions(+), 149220 deletions(-)
$ git diff --name-status main...t/T2523 | cut -f1 | sort | uniq -c       ->  17 D, 633 M
$ git diff --name-only main...t/T2523 | grep -vE '^(RBM3D/|RBM3D\.lean$|docs/claude-team/tools/DeadDecls\.lean$)' | wc -l
       0
```
- D2 (a): `scanProvers` still lists 42 roots ("kept by T2523" = 42), and the R2 set is unchanged from round 1 (the repair touches no other
  declaration; B1). This matches the sign-off.
- D2 (b): 291 insertions under `RBM3D/` and `RBM3D.lean`, within the limit of 300 that the sign-off sets. The tool's root lists are
  excluded by the sign-off.

## B6. Round 1's A1-A7 after the repair
- A1 (scope): B5. Only the sole writable files are touched.
- A2 (build): B3.
- A3 (axioms): B4. `sorry`/`admit`/`axiom`/`native_decide`: the repair adds no line (B1).
- A4 (statements): the check file compiles (B4). Main vs the repaired branch, with round 1's `consts.lean`/`cmp2.py`:
  ```text
  $ python3 -I $R/cmp2.py $R/consts_main.txt $S/consts_br2.txt
  user-facing (aux filtered): common 25309  new-on-branch 2  type-hash diffs 4  def-value/ctor diffs 5
  ```
  These are the same new/type/value names as in round 1 (two `_abel` aux names, a universe-name or auto-instance-name change, and the
  four registry lists). Round 1 had common 25314; the difference is the 5 deleted names. No statement of a surviving declaration changed.
- A5 (non-deletion line changes, clutter): the repair adds 0 lines (B1), so B15 (51 lines) and the clutter result are unchanged.
- A6 (registry): `RBM3D/Test/Axioms.lean` is not touched by the repair (B1 stat).
- A7 (tool): B4.
- Compiled instances: the ticket adds no endpoint theorem. The exempt `example`s are untouched by the repair. O1 below.
- Paper deltas: none needed (no Lean statement changed).

## Observations (no RETURN)
- O1 (round 1 O1, Amend 1): `baThm27L_any` still has no compiled instance in the library. The dispatcher deferred it to T2534.
- O2: the prove report has 753 lines, against the ticket's "≤ 120 lines apart from the deletion script and the tool's summary" and
  CLAUDE.md §6's limit of 300. It is a report-length defect only.
- O3: the repair deleted the heading comments inside the removed scopes (`MinorDiffInst`, `Inst`). These are deletions of now-empty
  scopes (ticket item 5), not rewording. `Green/MinorDiff.lean:914` (a comment) still names `MinorDiffInst.szM`; the report notes it for the
  comment ticket.
- O4: the doc comment of `restoredRoots` in the tool still gives the single general reason. The per-name reasons are in the report (R-C),
  as Amend 1 requires.
