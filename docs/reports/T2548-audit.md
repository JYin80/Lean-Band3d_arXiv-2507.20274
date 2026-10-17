Auditor model: claude-opus-5-5

# T2548 audit (round 1): public axiom audit replaces the premise registry; AuditNegative deleted

Written Sat Oct 17 08:59:46 UTC 2026. Branch `t/T2548` at 86f6ec03, from main b51d55d7. Audit worktree `RBM3D-wt/T2548-audit1` (detached).
Release clean-up ticket: no target theorem, so no statement or instance to check. The audit checks the deliverables,
the acceptance list, that no mathematical declaration changed, the build and axioms, and that the diff stays in the sole writable files.

## 1. Diff scope (sole writable files)

```
$ git diff --name-status main...HEAD
M	RBM3D.lean
D	RBM3D/Test/AuditNegative.lean
M	RBM3D/Test/Axioms.lean
$ git diff main...HEAD -- RBM3D.lean | grep -E '^[-+][^-+]'
-import RBM3D.Test.AuditNegative
```
All three are sole writable files. No file outside `RBM3D/Test/` and `RBM3D.lean` is touched, so no mathematical declaration changed.
`DeadDecls.lean` is not edited. Item 4 applies only if a root names a removed declaration, and none does: the roots take every
constant of `RBM.Audit` by prefix.
```
$ grep -n 'Audit' docs/claude-team/tools/DeadDecls.lean | sed -n '4,5p'
426:  let auditNames := modOf.toList.filterMap fun (c, _) => if `RBM.Audit |>.isPrefixOf c then some c else none
428:  for r in auditSorted do rootsUsed := rootsUsed.push (r, "core: namespace RBM.Audit")
```

## 2. Deliverable 1: `Axioms.lean` is the RBM2D form

```
$ diff RBM3D/Test/Axioms.lean ../RBM2D/RBM2D/Test/Axioms.lean && echo "identical to RBM2D"
identical to RBM2D
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h -- RBM2D/Test/Axioms.lean
81fca44
```
The file has the copyright header, a module docstring, `namespace RBM.Audit`, `allowedAxioms` and `#assert_rbm_axioms` (it fails
on any axiom outside the three, and on fewer than 100 constants), and nothing else. The RBM2D text needs no renaming: it already
uses the namespace `RBM` and the RBM3D copyright header.

Removed-name uses:
```
$ grep -rn 'RBM\.Audit\.\|AuditNegative\|borrowedProps\|owedProps\|structuralProps\|refutedProps\|supersededProps\|assert_rbm_audit_detects\|interfaceAxioms' RBM3D RBM3D.lean docs/claude-team/tools/DeadDecls.lean lakefile*
RBM3D/Test/Axioms.lean:30:/-- Fails unless every declaration in `RBM` uses only `RBM.Audit.allowedAxioms`. -/
RBM3D/Universality/PinsDens.lean:27:(class `refutedProps` of `RBM3D/Test/Axioms.lean`): ...
RBM3D/Universality/PinsC2.lean:32:move to the class `refutedProps`. ...
RBM3D/BA/Step5IIIWalk.lean:46:Registry: ... (its `owedProps` line is removed). ...
RBM3D/Evolution/SumDecay.lean:28:`EKFastDecay`, ... is listed in `structuralProps` of
RBM3D/Induction/PfStep5.lean:57:`owedProps`. ...
```
(Matched lines are shortened with `...`.) No code uses a removed name; the other hits are comments (see Observations).

## 3. Deliverables 2 and 3: AuditNegative deleted; `RBM3D.lean` ends with the audit

```
$ ls RBM3D/Test/
Axioms.lean
$ tail -2 RBM3D.lean
/-! Hard axiom audit of the whole library: see `RBM3D.Test.Axioms`. -/
#assert_rbm_axioms
$ grep -nE 'T[0-9]{4}|DECISIONS|ticket|registry|owed|borrowed|dispatcher' RBM3D.lean RBM3D/Test/Axioms.lean ; echo exit $?
exit 1
```
`#assert_rbm_axioms` is still the last command. Neither file has any process reference.

## 4. Build and axioms (audit worktree)

```
$ lake build 2>&1 | grep -Ev '^(✔|⣿|ℹ \[)' | tail -2 ; echo exit ${pipestatus[1]}
info: RBM3D.lean:655:0: axiom audit: 24150 declarations in `RBM`, all within [propext, Classical.choice, Quot.sound]
Build completed successfully (4425 jobs).
exit 0
```
The only other output is pre-existing `linter.style.header` warnings, in files this ticket does not touch.

Scratch files, not committed, in the scratchpad `T2548/`:
```
== neg_axiom.lean: import RBM3D; namespace RBM.Scratch; axiom auditAx : 2 = 3; theorem auditUse : 2 = 3 := auditAx; #assert_rbm_axioms
neg_axiom.lean:6:0: error: axiom audit failed:
RBM.Scratch.auditAx depends on [RBM.Scratch.auditAx]
RBM.Scratch.auditUse depends on [RBM.Scratch.auditAx]
neg_axiom exit 1
== neg_sorry.lean: import RBM3D; namespace RBM.Scratch; theorem auditSorry : 2 = 3 := by sorry; #assert_rbm_axioms
neg_sorry.lean:3:8: warning: declaration uses `sorry`
neg_sorry.lean:5:0: error: axiom audit failed:
RBM.Scratch.auditSorry depends on [sorryAx]
neg_sorry exit 1
== pos.lean: import RBM3D; #print axioms ...; #check @RBM.Audit.allowedAxioms; #assert_rbm_axioms
'RBM.Endpoints.final_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Thm27_of_L32' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThm27L_all' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM.Audit.allowedAxioms : List Lean.Name
axiom audit: 24150 declarations in `RBM`, all within [propext, Classical.choice, Quot.sound]
pos exit 0
```
The ticket's check file (published root statements unchanged) passes against the branch:
```
$ lake env lean docs/tickets/checks/T2548-check.lean >/dev/null 2>&1; echo exit $?
exit 0
$ lake env lean docs/tickets/checks/T2548-check.lean 2>&1 | grep -i error
(no output)
```
Forbidden tokens in added lines:
```
$ git diff main...HEAD | grep -E '^\+' | grep -nE 'sorry|admit|native_decide|^\+axiom'
7:+particular any `sorry` (`sorryAx`) or user-declared `axiom` anywhere in the `RBM` namespace breaks
```
This one hit is docstring text, not a use.

## 5. Statement, vacuity, instance, paper deltas

- The diff changes no mathematical statement and no frozen signature. The check file still elaborates the five pinned root statements.
- Nothing is vacuous: the audit rejects a namespace with fewer than 100 constants (it finds 24150), and the two negative scratch
  files show that it fails on an axiom and on a `sorry`.
- No endpoint theorem, so no instance is required.
- There is no Lean/paper statement difference, so no paper delta is needed. The prove report proposes none.

## 6. Observations (not RETURN)

- O1. Comments in five merged modules still name the removed registry lists: `Universality/PinsDens.lean:27`,
  `Universality/PinsC2.lean:32`, `BA/Step5IIIWalk.lean:46`, `Evolution/SumDecay.lean:28`, `Induction/PfStep5.lean:57`. These files
  are outside T2548's sole writable files; the comment tickets T2536-T2547 cover them. Dispatcher: check that their scopes drop these references.
- O2. In `docs/claude-team/tools/DeadDecls.lean`, section (g) (lines 251, 603-605) and the header comments (lines 16, 166) describe
  the registry lists, which no longer exist. Section (g) will now report nothing. The prove report flags this for the dispatcher. It is
  a tool-wording question, outside item 4.

## Verdict

T2548: **PASS**. Every deliverable and acceptance item is met. The diff touches only sole writable files. The full build passes with
the new audit (24150 `RBM` declarations, all within propext, Classical.choice and Quot.sound). No mathematical declaration changed.
At merge, bring the deletion in with `git rm RBM3D/Test/AuditNegative.lean`, as the ticket says.
