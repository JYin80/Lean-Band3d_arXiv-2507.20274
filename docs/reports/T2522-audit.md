Auditor model: claude-opus-5-5

# T2522 audit, round 1 (release clean-up step 1: dead-code report; report-and-tool ticket)

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2522-audit1`, detached at `t/T2522` 0aea2069 (parent `main` 316653b9). Written Fri Oct 16 20:52:24 UTC 2026 (`date -u`). Scratch: `<scratchpad>/T2522/`.

The ticket has no Lean target theorem (no statement, no endpoint instance, no paper delta). The audit checks the Acceptance list and that the roots match the ticket (core, G1-G4).

## 1. Scope of the diff, hygiene, build
```
$ git diff --name-only main...t/T2522
docs/claude-team/tools/DeadDecls.lean
$ git diff main...t/T2522 -- RBM3D RBM3D.lean | wc -l
       0
$ git diff main...t/T2522 | grep -nE "^\+.*\b(sorry|admit|axiom|native_decide)\b"; echo "grep exit $?"
grep exit 1
$ lake build RBM3D        # audit worktree
Build completed successfully (4443 jobs).
```
Only a sole writable file is touched (`docs/reports/T2522-dead.md`, `T2522-prove.md` are untracked in the main worktree, as the ticket intends). Nothing under `RBM3D/`, no `RBM3D.lean` change, so no axiom set changes. Closure method unchanged: in the diff, the only `edges` lines are the call site moving into the new `closure` function; `edges`, `unitOf`, `inductUnit?`, `mentionsMeta` are not in the diff.

## 2. The tool runs to completion from the main worktree; the report is its verbatim output
```
$ cd /Users/junyin/Lean_proof/RBM3D && date -u && lake env lean /Users/junyin/Lean_proof/RBM3D-wt/T2522-audit1/docs/claude-team/tools/DeadDecls.lean > out_main.txt 2>&1; echo exit $?; date -u; wc -l out_main.txt
Fri Oct 16 20:45:05 UTC 2026
exit 0
Fri Oct 16 20:45:59 UTC 2026
   12060 out_main.txt
$ sed -n '12,12071p' docs/reports/T2522-dead.md > dead_body.txt; diff dead_body.txt out_main.txt && echo IDENTICAL
IDENTICAL
```
So the 12060 lines of `T2522-dead.md` between its ```` ``` ```` fences are the tool's output byte for byte. The summary and group tables under the fence match (e) and (f) of the output:
```
- declarations (non-meta units): 32770; meta declarations: 222 (unreached meta: 213)
- unreached (non-meta): 10243
- sum of unreached line spans (end-start+1 per declaration): 100272
- modules with no reached declaration: 17
G1: roots 20; in core 16; not 4 (inst_bridge_loc, inst_bridge_que, unOUClaims_holds, unOUQUE_holds); extra 4 decl, 27 lines
G2: roots 31; in core 22; not 9; extra 10 decl, 53 lines
G3: roots 3; in core 2; not 1 (RBM.BA.baThm27L_any); extra 2 decl, 12 lines
G4: roots 16; in core 16; extra 0 (inside the core)
```
(abridged from (f); the verbatim lines are in `T2522-dead.md`.)

## 3. Roots against the ticket
Core fixed roots in the tool: `final_shape`, `Thm27`, `Thm27_of_L32`, `band_terminal` (as pinned). G3 roots: `baThm27L_any`, `baThm27L_of_ML`, `baEnd_BUnivL_of_ML` (as pinned). The (a) output has no `[MISSING]` line and no `MISSING ROOTS` line (`grep -n MISSING out_main.txt`: only the G-group header lines print).

`RBM.Audit` roots: the tool takes every in-scope constant with prefix `RBM.Audit`. Count, recomputed by my own scan: `audit constants independently counted: 35`; tool: `(35 constants in RBM.Audit and its sub-namespaces; 34795 in-scope constants reached in the core)`. The three `private` defs in `RBM.Audit` (`Test/Axioms.lean:465,471,476`) do not have the `RBM.Audit` prefix after mangling. They are not roots, but they are reached: `| RBM3D.Test.Axioms | 9 | 9 | 0 |`, and they are not in the meta list.

Hand-listed `example` roots (core: FinalShape; G1: BandTerminal §Instances; G2: MAPins; G4: BUnivHolds). These were checked mechanically. A script copied all 24 `example`s (7 FinalShape, 10 BandTerminal, 5 MAPins, 2 BUnivHolds) into a scratch file under the same namespaces and `open`s as `noncomputable def T2522S_<tag>_i`, with a local copy of the private `*_hg`. It elaborated them, collected every in-scope (`RBM3D.*`) constant of their types and values, and tested membership in the tool's own closure (its `edges` and `fixedRoots`/`exampleRoots`/`groups`):
```
$ lake env lean <scratch>/Ex2.lean
audit constants independently counted: 35
FS: 75 in-scope constants used by the elaborated examples; not in closure(core ∪ FS roots): 0 []
G1: 65 in-scope constants used by the elaborated examples; not in closure(core ∪ G1 roots): 0 []; not in closure(G1 roots alone): 0 []
G2: 79 in-scope constants used by the elaborated examples; not in closure(core ∪ G2 roots): 0 []; not in closure(G2 roots alone): 0 []
G4: 28 in-scope constants used by the elaborated examples; not in closure(core ∪ G4 roots): 0 []; not in closure(G4 roots alone): 0 []
```
So each hand list covers its `example`s exactly, up to closure. The private `FinalShape_hg` and `MAPins_hg` are passed through `privName`, and they resolve: G2 prints `private RBM.BA.MAPins_hg` without `[MISSING]`.

## 4. Sanity checks
```
$ grep -n -A7 "^## sanity checks" out_main.txt   (= dead.md lines 145-152)
- every core root reached: true
- RBM.BA.baThm27L_three: reached in the core
  reached via ...: RBM.BA.baThm27L_three <- RBM.Endpoints.Thm27_of_L32
- RBM.BA.unMLOutBA_three: reached in the core
  reached via ...: RBM.BA.unMLOutBA_three <- RBM.BA.baThm27L_three <- RBM.Endpoints.Thm27_of_L32
- RBM.Endpoints.bUniv_holds: reached in the core
  reached via ...: RBM.Endpoints.bUniv_holds <- RBM.Endpoints.unBUniv_of_L32 <- RBM.Endpoints.BUniv_of_L32 <- RBM.Endpoints.band_terminal
```
These paths were confirmed in the source. `FinalShape.lean:39` `Thm27_of_L32 ... := RBM.BA.baThm27L_three`; `UNBUniv.lean:282` `fun h32 => baThm27L_of_ML 3 le_rfl h32 unMLOutBA_three`; `BandTerminal.lean:95-96` `unBUniv_of_L32 ... := fun h32 => bUniv_holds unNormBandRow h32 ...`, `:100` `BUniv_of_L32 := unBUniv_of_L32`, `:104-105` `band_terminal ... ⟨..., BUniv_of_L32 h32, ...⟩`. All three names are reached, and the report says so.
```
$ git ls-files RBM3D/Probe | wc -l          # audit worktree (= t/T2522)
       0
$ git ls-tree -r main --name-only | grep -c "^RBM3D/Probe"
0
```

## 5. Deletion test (own scratch copy, not committed)
The module is `RBM3D.Universality.GUEPhase.RandomLayerBGD`. Tool: `| ... RandomLayerBGD | 8 | 4 | 4 |`. Unreached: `inst_unClaimRowkD_band_zero 120-135`, `inst_un_claimAll_of_rowskD 137-149`, `inst_ouRowk_of_pinsD 151-161`, `inst_g1Rowk_of_inputsGD 163-177`. No other file names them: `grep -rn` of the four names over `RBM3D RBM3D.lean`, excluding the file itself, prints nothing.
```
$ cp -c -R /Users/junyin/Lean_proof/RBM3D-wt/T2522-audit1 <scratch>/audit-del; cd <scratch>/audit-del
$ sed -i '' '120,177d' RBM3D/Universality/GUEPhase/RandomLayerBGD.lean
$ diff <audit-wt>/RBM3D/Universality/GUEPhase/RandomLayerBGD.lean RBM3D/... | grep -c "^<"
58
$ date -u; lake build > audit_delbuild.txt 2>&1; echo "exit $?"; date -u
Fri Oct 16 20:48:59 UTC 2026
exit 0
Fri Oct 16 20:50:26 UTC 2026
$ grep -E "RandomLayerBGD|Build completed|UNBUniv \(" audit_delbuild.txt | tail -3
✔ [4439/4443] Built RBM3D.Universality.GUEPhase.RandomLayerBGD (5.0s)
✔ [4440/4443] Built RBM3D.BA.UNBUniv (8.0s)
Build completed successfully (4443 jobs).
```
This reproduces the prove report's deletion test (same module, same 58 lines, exit 0). The full `lake build` includes `#assert_rbm_axioms`.

## 6. Report-format items
- (a) roots with group tags; (b) per-module table with unreached `name start-end` sorted by line; (c) 17 whole-dead modules with importers; (d) meta list (54 modules, 213 entries, all local `notation`/`macro_rules`/`unexpand` aux constants by name); (e) totals; (f) G1-G4 with top-5 modules and "in core / not in core" root counts, so G1/G2 are explicitly not wholly inside the core; (g) 9 name lists, 54 of 287 in-scope names unreached. All present.
- (g) list sizes cross-checked against the source for `borrowedProps` (2 literals, lines 91-93) and `refutedProps` (7 literals, lines 399-406): they match the tool (`2 names`, `7 names`).
- Port: `diff` of the tool on `main` against `../RBM2D/docs/claude-team/tools/DeadDecls.lean`, counting lines without `RBM2D`/`RBM3D`, prints `0`. RBM2D HEAD `9e0f275`, as reported.

## 7. Paper deltas
None needed: no Lean statement is added or changed, and the tool is not part of the library.

## Observations (no effect on statement, instance, build, axioms, deltas)
1. The prove report is 127 lines. Its non-script part, section (a) plus the narrative, is well under the ticket's 80-line budget for everything outside (b)-(d), (g), so this is not a defect.
2. For the deletion ticket, which the dispatcher decides (prove report (d)1-3): some unreached helpers are used by `example`s that are not roots (`GUEPathBoundsBA` `j_*`, `GUELLBAInst.hg`), and the simp-list name `GUETwistBA_Pi_apply` is reported unreached. Deleting them needs those `example`s and simp lists edited. `Test/InterfaceShape.lean` (namespace `RBM.Test`) is not a root and is reported as a whole-dead module.
3. Scratch hygiene, mine: the session scratchpad already held the prover's `T2522/wt-scratch`. My first `cp -c -R` nested a copy into it, and one `sed` hit the prover's scratch copy of `RandomLayerBGD.lean`. I restored that file (copied it back from the audit worktree and re-applied the prover's 120-177 deletion; `wc -l` 125) and ran my test in the separate `audit-del`. These files were never under git control in any project directory, and no repository file changed.

## Verdict
T2522: **PASS**. All Acceptance items hold, the roots match the ticket (core plus G1-G4), and the report reproduces byte for byte. No dispatcher sign-off is needed for the merge. Observation 2 is input for the deletion ticket.
