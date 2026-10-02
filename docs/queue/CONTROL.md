# CONTROL — written only by the dispatcher (Cowork). The hub may only append `done:` lines under Approved instructions.

mode: RUN
parallel: 4
updated: 2026-10-02 23:47 UTC (dispatcher V1: T2008, T2009 under pre-release check; H7 commit)
reason: RUN (Jun, DECISIONS §8). Scope and rules: DECISIONS §3–§7.

The standing hub rules are in CLAUDE.md §3 (auto-merge, one automatic repair per RETURN, date -u, report headers, private helpers, nothing undecided starts, parallelism, API errors).

## Released tickets (only those not yet merged)
Priority order (CLAUDE.md §3 (G)); at most `parallel` workflows at once.
1. T2006 — `docs/tickets/T2006.md` (MD-1, model vocabulary: `Sizes`, fine-lattice model, `LinearForm`; role `prover-max`; critical path: MD-2, MD-3 and every ST/UN/BA ticket wait for it). Start: now.
2. T2007 — `docs/tickets/T2007.md` (PT-A, propagator pins, bridges, property 5s; role `prover-hard`). Start: now.

## Pre-release checks (the hub compiles in the same loop iteration; the dispatcher releases — CLAUDE.md §4 step 0, H4)
Compile each file with `lake env lean <file>` in the main worktree and append one `done:` line under this list per file: the exit code and the error lines, verbatim.
- `docs/tickets/checks/T2008-check.lean`
  done: 2026-10-02 23:52 UTC — `lake env lean docs/tickets/checks/T2008-check.lean`: exit 0; no error lines.
- `docs/tickets/checks/T2009-check.lean`
  done: 2026-10-02 23:52 UTC — `lake env lean docs/tickets/checks/T2009-check.lean`: exit 1; error lines: `docs/tickets/checks/T2009-check.lean:10:8: error(lean.unknownIdentifier): Unknown constant `Real.cosh_le_exp_half_sq``

## Approved instructions
- H7 (dispatcher V1, 2026-10-02 23:47 UTC). Stage by name only and commit with message `Dispatcher V1: DECISIONS §12–§15, route H (Fable review), tickets T2006–T2009`: `docs/DECISIONS.md`, `docs/ROUTES.md`, `docs/rework-ledger.md`, `docs/tickets/QUEUE.md`, `docs/tickets/T2006.md`, `docs/tickets/T2007.md`, `docs/tickets/T2008.md`, `docs/tickets/T2009.md`, `docs/tickets/checks/T2006-check.lean`, `docs/tickets/checks/T2007-check.lean`, `docs/tickets/checks/T2008-check.lean`, `docs/tickets/checks/T2009-check.lean`, `docs/claude-team/fable/2026-10-02-routeH.md`, `docs/claude-team/WORKLOG.md`, `docs/queue/CONTROL.md`, `docs/queue/CONTROL-archive.md`; then `git push origin main` (no force). One `done:` line with the hash.
(H1–H6 archived in `docs/queue/CONTROL-archive.md`. Standing from H4: compile every file listed under Pre-release checks in the same loop iteration you see it.)

## Merge log (the hub appends one `done:` line per merge)
done: 2026-10-02 19:05 UTC — T2001 merged a62eeef (report only: state, prove, audit, coverage reports); audit PASS round 2 after one repair; pushed 3c11d7b..a62eeef.
done: 2026-10-02 21:58 UTC — T2005 merged 709c5c7 (RBM3D/Defs/SemicircleIntegral.lean, root import; lake build 3254 jobs, axiom audit 510 theorems / 0 axioms); audit PASS round 1; pushed 4908ddf..709c5c7.
done: 2026-10-02 23:11 UTC — T2002 merged 06f2064 (report only: state, prove, audit, portmap reports); audit PASS round 1 (after rule-(H) prover-max rerun); pushed 709c5c7..06f2064.
done: 2026-10-02 23:22 UTC — T2003 merged 7ba7ba5 (report only: state, prove, audit reports; H6 sign-off, DECISIONS §13); pushed 06f2064..7ba7ba5.
done: 2026-10-02 23:23 UTC — T2004 merged 0b91f7a (report only: state, prove, audit reports); audit PASS round 1 (after rule-(H) prover-max rerun); pushed.

## Pending approval (information only — the hub must NOT act on these)
(none)
