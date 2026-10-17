Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 17 08:46:24 UTC 2026

(i) no exponents; (ii) not applicable; PASS

## (b) Script output

Commit on `t/T2548`: 86f6ec03 (`RBM3D.lean`, `RBM3D/Test/Axioms.lean`, `RBM3D/Test/AuditNegative.lean` deleted by `git rm`).
Written Sat Oct 17 08:57:12 UTC 2026 (`date -u`).

```
$ lake build        # worktree T2548, tail
✔ [4423/4425] Built RBM3D.Test.Axioms (4.4s)
ℹ [4424/4425] Built RBM3D (10s)
info: RBM3D.lean:655:0: axiom audit: 24150 declarations in `RBM`, all within [propext, Classical.choice, Quot.sound]
Build completed successfully (4425 jobs).
```

```
$ git diff --stat main...t/T2548
 RBM3D.lean                    |   1 -
 RBM3D/Test/AuditNegative.lean |  30 ---
 RBM3D/Test/Axioms.lean        | 612 ++----------------------------------------
 3 files changed, 22 insertions(+), 621 deletions(-)
$ diff RBM3D/Test/Axioms.lean ../RBM2D/RBM2D/Test/Axioms.lean && echo same
same        # RBM2D source: commit 81fca44 (git log -1 -- RBM2D/Test/Axioms.lean); header already the RBM3D one
$ wc -l RBM3D/Test/Axioms.lean
48 RBM3D/Test/Axioms.lean
```

Negative scratch files (not committed; in the scratchpad `T2548/`), each `namespace RBM.Scratch` + `#assert_rbm_axioms`:
```
== axiom (axiom badAx : False; theorem useBad : 1 = 2 := badAx.elim)
neg_axiom.lean:6:0: error: axiom audit failed:
RBM.Scratch.useBad depends on [RBM.Scratch.badAx]
RBM.Scratch.badAx depends on [RBM.Scratch.badAx]
== sorry (theorem useSorry : 1 = 2 := by sorry)
neg_sorry.lean:3:8: warning: declaration uses `sorry`
neg_sorry.lean:5:0: error: axiom audit failed:
RBM.Scratch.useSorry depends on [sorryAx]
```

```
$ lake env lean pr.lean     # import RBM3D; #print axioms RBM.Endpoints.final_shape
'RBM.Endpoints.final_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean docs/tickets/checks/T2548-check.lean ; echo exit $?
(three #check outputs: baStep5III_holds_any, bUniv_holds, UNL32; no errors)
exit 0
```

Removed-name use (`grep -rn 'RBM.Audit\.' RBM3D RBM3D.lean docs/claude-team/tools/DeadDecls.lean` on the branch): only the docstring of `allowedAxioms` in `RBM3D/Test/Axioms.lean:30`. No other module uses a removed name.

Item 4 (`DeadDecls.lean`): not edited. Its roots take every constant of the namespace `RBM.Audit` by prefix (line 426: `` `RBM.Audit |>.isPrefixOf c ``), not by name; no root names a removed declaration. Section (g) reads `RBM3D/Test/Axioms.lean` as text and now finds no name lists; its header and comments (lines 16, 166, 603-605) mention the registry. That is a dispatcher question (tool and report wording), outside this ticket's item 4.

Item 3: `RBM3D.lean` keeps `#assert_rbm_axioms` as the last command; its comment `/-! Hard axiom audit of the whole library: see `RBM3D.Test.Axioms`. -/` has no process reference. The new `Axioms.lean` docstring is the RBM2D wording and has none.

Narrative: the registry, premise scan, `#assert_rbm_audit_detects`, `certificates`, `interfaceAxioms` and helpers are gone with the old 616-line file; the new file is the RBM2D file verbatim. No mathematical declaration changed. This is not a theorem ticket (no target theorem, no instance needed).

## (c) Verified Mathlib names

None used.

## (d) Open issues and paper-delta candidates

- No paper-delta candidates.
- Dispatcher: `docs/claude-team/tools/DeadDecls.lean` section (g) and its comments refer to the removed registry (see above); not changed here.
