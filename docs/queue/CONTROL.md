# CONTROL — written only by the dispatcher (Cowork). The hub may only append `done:` lines under Approved instructions.

mode: RUN
parallel: 4
updated: 2026-10-03 02:20 UTC (dispatcher V1: T2012, T2013 merged; T2018 (MD-4) released on check exit 0; H16)
reason: RUN (Jun, DECISIONS §8). Scope and rules: DECISIONS §3–§7.

The standing hub rules are in CLAUDE.md §3 (auto-merge, one automatic repair per RETURN, date -u, report headers, private helpers, nothing undecided starts, parallelism, API errors).

## Released tickets (only those not yet merged)
Priority order (CLAUDE.md §3 (G)); at most `parallel` workflows at once.
4. T2014 — `docs/tickets/T2014.md` (KL2, tree cut and cut bijection; role `prover-max`; check exit 0 at 01:12 UTC; preflight-fail on ticket text → Amend 1, H13). Start: at the next free slot.
5. T2015 — `docs/tickets/T2015.md` (ST-D1, report only: design of `lem:main_ind` pins and Step 1, split of sub-gate ST-1; role `prover-max`). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).
6. T2016 — `docs/tickets/T2016.md` (EK-D1, report only: evolution-kernel pins on the PT pins, audit of `RBM3D/Kernel/*`, split; role `prover-max`). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).
7. T2017 — `docs/tickets/T2017.md` (PT-C, route H: torus kernel bounds and gap; role `prover-hard`). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).
8. T2018 — `docs/tickets/T2018.md` (MD-4, grid walk carrier, transfer law, independent increments; role `prover-hard`). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).

## Pre-release checks (the hub compiles in the same loop iteration; the dispatcher releases — CLAUDE.md §4 step 0, H4)
Compile each file with `lake env lean <file>` in the main worktree and append one `done:` line under this list per file: the exit code and the error lines, verbatim.
- `docs/tickets/checks/T2015-check.lean` (ST-D1; released conditionally above, DECISIONS §17).
  done: 2026-10-03 01:22 UTC — `lake env lean docs/tickets/checks/T2015-check.lean`: exit 0; no error lines.
- `docs/tickets/checks/T2016-check.lean` (EK-D1; released conditionally above, DECISIONS §17).
  done: 2026-10-03 01:52 UTC — `lake env lean docs/tickets/checks/T2016-check.lean`: exit 0; no error lines. T2016 waits for a free slot (4 of 4 in use).
- `docs/tickets/checks/T2017-check.lean` (PT-C; released conditionally above, DECISIONS §17).
  done: 2026-10-03 02:07 UTC — `lake env lean docs/tickets/checks/T2017-check.lean`: exit 0; no error lines. T2017 waits for a free slot (T2016 takes the slot freed by T2012).
- `docs/tickets/checks/T2018-check.lean` (MD-4; released conditionally above, DECISIONS §17).
  done: 2026-10-03 02:52 UTC — `lake env lean docs/tickets/checks/T2018-check.lean`: exit 0; no error lines. T2018 waits for a free slot (4 of 4 in use).

## Approved instructions
- H7 (dispatcher V1, 2026-10-02 23:47 UTC). Stage by name only and commit with message `Dispatcher V1: DECISIONS §12–§15, route H (Fable review), tickets T2006–T2009`: `docs/DECISIONS.md`, `docs/ROUTES.md`, `docs/rework-ledger.md`, `docs/tickets/QUEUE.md`, `docs/tickets/T2006.md`, `docs/tickets/T2007.md`, `docs/tickets/T2008.md`, `docs/tickets/T2009.md`, `docs/tickets/checks/T2006-check.lean`, `docs/tickets/checks/T2007-check.lean`, `docs/tickets/checks/T2008-check.lean`, `docs/tickets/checks/T2009-check.lean`, `docs/claude-team/fable/2026-10-02-routeH.md`, `docs/claude-team/WORKLOG.md`, `docs/queue/CONTROL.md`, `docs/queue/CONTROL-archive.md`; then `git push origin main` (no force). One `done:` line with the hash.
  done: 2026-10-02 23:52 UTC — committed 6a555f7 (16 files staged by name), pushed to origin/main.
- H8 (dispatcher V1, 2026-10-03 00:07 UTC). After compiling the Pre-release files above, stage by name only and commit with message `Dispatcher V1: T2008 released, T2009 check import, T2010 (PT-E)`: `docs/DECISIONS.md`, `docs/ROUTES.md`, `docs/tickets/QUEUE.md`, `docs/tickets/T2009.md`, `docs/tickets/checks/T2009-check.lean`, `docs/tickets/T2010.md`, `docs/tickets/checks/T2010-check.lean`, `docs/claude-team/WORKLOG.md`, `docs/queue/CONTROL.md`, `docs/queue/CONTROL-archive.md`; then `git push origin main` (no force). One `done:` line with the hash.
  done: 2026-10-03 00:12 UTC — committed 01b7ed8 (10 files staged by name, after compiling T2010-check: exit 0), pushed to origin/main.
- H9 (dispatcher V1, 2026-10-03 00:34 UTC; DECISIONS §16). T2007 and T2008 are blocked at merge step 5 by the axiom registry only. (a) T2007: run `docs/tickets/T2007.md` Amend 1 — one `repairer` stage on branch t/T2007 (sole writable file of the amend: `RBM3D/Test/Axioms.lean`), then a fresh `auditor` (round 2, scope: the amend), then the normal merge; this takes priority over starting a new ticket. (b) After T2007 is merged: resume T2008's merge from step 5 (`docs/tickets/T2008.md` Note 1; branch unchanged). (c) If T2006 reaches merge before T2007 is merged and the registry stops it, wait for (a) and resume T2006 from step 5. If any full build then fails for another reason, set `blocked` with the error lines. One `done:` line per step.
  done: 2026-10-03 00:41 UTC — (a) started: repairer stage for T2007 Amend 1 on t/T2007, then auditor round 2 (workflow wf_9715274f-bae). (c) not needed: T2006 merged 0a873f1 before this instruction, its full build passed (registry did not stop it).
  done: 2026-10-03 00:46 UTC — (a) T2007 Amend 1: repairer 64e6082, auditor round 2 PASS; merged b20c658.
  done: 2026-10-03 00:46 UTC — (b) T2008 merge resumed from step 5: full build OK; merged 710acd2.
- H10 (dispatcher V1, 2026-10-03 00:53 UTC). After compiling the Pre-release files above: run `lake build RBM3D.Loop.GLoop` (module-doc change only, T2002f), then stage by name only and commit with message `Dispatcher V1: DECISIONS §16, paper-deltas D17–D24, tickets T2011–T2013, GLoop module doc (T2002f)`: `docs/DECISIONS.md`, `docs/ROUTES.md`, `docs/paper-deltas.md`, `docs/rework-ledger.md`, `docs/tickets/QUEUE.md`, `docs/tickets/T2007.md`, `docs/tickets/T2008.md`, `docs/tickets/T2011.md`, `docs/tickets/T2012.md`, `docs/tickets/T2013.md`, `docs/tickets/checks/T2011-check.lean`, `docs/tickets/checks/T2012-check.lean`, `docs/tickets/checks/T2013-check.lean`, `RBM3D/Loop/GLoop.lean`, `docs/claude-team/WORKLOG.md`, `docs/queue/CONTROL.md`, `docs/queue/CONTROL-archive.md`; then `git push origin main` (no force). One `done:` line with the hash.
  done: 2026-10-03 01:02 UTC — T2011–T2013 checks compiled (exit 0 each); `lake build RBM3D.Loop.GLoop` exit 0 (3220 jobs); committed e0c58e6 (17 files staged by name), pushed to origin/main.
- H11 (dispatcher V1, 2026-10-03 01:03 UTC). After H10: stage by name only and commit with message `Dispatcher V1: T2007/T2008 merged bookkeeping, ticket T2014 (KL2)`: `docs/ROUTES.md`, `docs/rework-ledger.md`, `docs/tickets/QUEUE.md`, `docs/tickets/T2014.md`, `docs/tickets/checks/T2014-check.lean`, `docs/claude-team/WORKLOG.md`, `docs/queue/CONTROL.md`, `docs/queue/CONTROL-archive.md`; then `git push origin main` (no force). One `done:` line with the hash. (If H10 is still open when you read this, do H10 and H11 as one commit with H10's message plus ", T2014 (KL2)" and both file lists.)
  done: 2026-10-03 01:12 UTC — T2014 check compiled (exit 0); committed 06b1fa9 (6 changed files staged by name; `docs/rework-ledger.md` and `docs/queue/CONTROL-archive.md` had no changes), pushed to origin/main.
- H12 (dispatcher V1, 2026-10-03 01:19 UTC). Standing from now (DECISIONS §17): a Released ticket whose start condition names its Pre-release check starts in the same loop iteration in which you compile that check with exit 0, if a slot is free. Now: stage by name only and commit with message `Dispatcher V1: T2011–T2014 released, ticket T2015 (ST-D1), DECISIONS §17`: `docs/DECISIONS.md`, `docs/tickets/QUEUE.md`, `docs/tickets/T2015.md`, `docs/tickets/checks/T2015-check.lean`, `docs/claude-team/WORKLOG.md`, `docs/queue/CONTROL.md`, `docs/queue/CONTROL-archive.md`; then `git push origin main` (no force). One `done:` line with the hash.
  done: 2026-10-03 01:22 UTC — committed c950f27 (7 files staged by name), pushed to origin/main. T2015 check exit 0; T2015 waits for a free slot (4 of 4 in use by T2011, T2013, T2012, T2014).
- H13 (dispatcher V1, 2026-10-03 01:33 UTC). T2014 `preflight-fail` (ticket text): `docs/tickets/T2014.md` Amend 1 corrects it. Restart T2014 on its branch at the next free slot (before T2015's successors; T2014 keeps its place in the Released order): stage 1a `preflight` confirms the two amended points only (append to section (a), do not rewrite it), then stage 1b `prover-max` and stage 2 as usual. This is not a RETURN (rule (B) count unchanged). One `done:` line when it restarts.
  done: 2026-10-03 01:56 UTC — T2014 restarted on t/T2014 in the slot freed by T2011 (merged 13dbbc0): workflow wf_66870ea1-906, preflight confirms the two amended points (append to (a)), then prover-max, then auditor.
- H14 (dispatcher V1, 2026-10-03 01:49 UTC). After compiling the T2016 check: stage by name only and commit with message `Dispatcher V1: T2014 Amend 1, ticket T2016 (EK-D1)`: `docs/ROUTES.md`, `docs/tickets/QUEUE.md`, `docs/tickets/T2014.md`, `docs/tickets/T2016.md`, `docs/tickets/checks/T2016-check.lean`, `docs/claude-team/WORKLOG.md`, `docs/queue/CONTROL.md`; then `git push origin main` (no force). One `done:` line with the hash.
  done: 2026-10-03 01:52 UTC — committed 03fd13f (7 files staged by name), pushed to origin/main.
- H15 (dispatcher V1, 2026-10-03 02:05 UTC). After H14 and compiling the T2017 check: stage by name only and commit with message `Dispatcher V1: route H pilot passed (T2011), ticket T2017 (PT-C)`: `docs/DECISIONS.md`, `docs/ROUTES.md`, `docs/rework-ledger.md`, `docs/tickets/QUEUE.md`, `docs/tickets/T2017.md`, `docs/tickets/checks/T2017-check.lean`, `docs/claude-team/WORKLOG.md`, `docs/queue/CONTROL.md`; then `git push origin main` (no force). One `done:` line with the hash.
  done: 2026-10-03 02:07 UTC — committed 110a9a2 (8 files staged by name, after compiling T2017-check: exit 0), pushed to origin/main.
- H16 (dispatcher V1, 2026-10-03 02:20 UTC). After H15 and compiling the T2018 check: stage by name only and commit with message `Dispatcher V1: T2012/T2013 merged bookkeeping, D25, ticket T2018 (MD-4)`: `docs/ROUTES.md`, `docs/paper-deltas.md`, `docs/rework-ledger.md`, `docs/tickets/QUEUE.md`, `docs/tickets/T2018.md`, `docs/tickets/checks/T2018-check.lean`, `docs/claude-team/WORKLOG.md`, `docs/queue/CONTROL.md`; then `git push origin main` (no force). One `done:` line with the hash.
(H1–H6 archived in `docs/queue/CONTROL-archive.md`. Standing from H4: compile every file listed under Pre-release checks in the same loop iteration you see it.)

## Merge log (the hub appends one `done:` line per merge)
done: 2026-10-02 19:05 UTC — T2001 merged a62eeef (report only: state, prove, audit, coverage reports); audit PASS round 2 after one repair; pushed 3c11d7b..a62eeef.
done: 2026-10-02 21:58 UTC — T2005 merged 709c5c7 (RBM3D/Defs/SemicircleIntegral.lean, root import; lake build 3254 jobs, axiom audit 510 theorems / 0 axioms); audit PASS round 1; pushed 4908ddf..709c5c7.
done: 2026-10-02 23:11 UTC — T2002 merged 06f2064 (report only: state, prove, audit, portmap reports); audit PASS round 1 (after rule-(H) prover-max rerun); pushed 709c5c7..06f2064.
done: 2026-10-02 23:22 UTC — T2003 merged 7ba7ba5 (report only: state, prove, audit reports; H6 sign-off, DECISIONS §13); pushed 06f2064..7ba7ba5.
done: 2026-10-02 23:23 UTC — T2004 merged 0b91f7a (report only: state, prove, audit reports); audit PASS round 1 (after rule-(H) prover-max rerun); pushed.
done: 2026-10-03 00:38 UTC — T2006 merged 0a873f1 (RBM3D/Defs/Sizes.lean, RBM3D/Gauss/FineModel.lean, RBM3D/Gauss/LinearForm.lean, root imports; lake build 3326 jobs, axiom audit 612 theorems / 0 axioms); audit PASS round 1; pushed.
done: 2026-10-03 00:40 UTC — T2009 merged 73cf5c1 (RBM3D/Propagator/HeatKernel1D.lean, root import; lake build 3686 jobs, axiom audit 620 theorems / 0 axioms); audit PASS round 1; pushed.
done: 2026-10-03 00:41 UTC — T2010 merged 315e65e (RBM3D/Propagator/LaplaceGauss.lean, root import; lake build 3688 jobs, axiom audit 627 theorems / 0 axioms); audit PASS round 1; pushed.
done: 2026-10-03 00:46 UTC — T2007 merged b20c658 (Pins.lean, Prop5Short.lean, Test/Axioms.lean Amend 1, root imports; lake build 3690 jobs, 643 theorems / 0 axioms); audit PASS rounds 1 and 2; pushed.
done: 2026-10-03 00:46 UTC — T2008 merged 710acd2 (RBM3D/Loop/KLTree.lean, root import; lake build 3691 jobs, 731 theorems / 0 axioms); audit PASS round 1, merge resumed at step 5 (H9 b); pushed.
done: 2026-10-03 01:56 UTC — T2011 merged 13dbbc0 (RBM3D/Propagator/HeatBounds1D.lean, root import; lake build 3695 jobs, axiom audit 734 theorems / 0 axioms); audit PASS round 1; pushed.
done: 2026-10-03 02:07 UTC — T2012 merged 9e2b00f (RBM3D/Defs/StochDomAt.lean, RBM3D/Gauss/DominationAt.lean, RBM3D/Test/Axioms.lean, root imports; lake build 3697 jobs, axiom audit 832 theorems / 0 axioms); audit PASS round 1; pushed.
done: 2026-10-03 02:17 UTC — T2013 merged 868b3b4 (RBM3D/Loop/GLoopFlow.lean, RBM3D/Gauss/BlockAnderson.lean, root imports; lake build 3699 jobs, axiom audit 880 theorems / 0 axioms); audit PASS round 1; pushed.

## Pending approval (information only — the hub must NOT act on these)
(none)
