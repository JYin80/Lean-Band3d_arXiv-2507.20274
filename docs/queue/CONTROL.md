# CONTROL — written only by the dispatcher (Cowork). The hub may only append `done:` lines under Approved instructions.

mode: RUN
parallel: 4
updated: 2026-10-02 19:35 UTC (dispatcher V1: H4 compile T2005 check; H5 commit)
reason: RUN (Jun, DECISIONS §8). Scope and rules: DECISIONS §3–§7.

The standing hub rules are in CLAUDE.md §3 (auto-merge, one automatic repair per RETURN, date -u, report headers, private helpers, nothing undecided starts, parallelism, API errors).

## Released tickets (only those not yet merged)
Priority order (CLAUDE.md §3 (G)); at most `parallel` workflows at once. T2002–T2004 are report-only (the hub skips merge steps 3–5; it commits the state file, the reports and any `docs/reports/T####-*.md` file the ticket names as sole writable).
1. T2002 — `docs/tickets/T2002.md` (MD-D1, model and flow vocabulary + RBM2D port map; role `prover-max`). Start: now.
2. T2003 — `docs/tickets/T2003.md` (PT-D1, propagator properties 5–8; role `prover-max`). Start: now.
3. T2004 — `docs/tickets/T2004.md` (KL-D1, K-loop layer; role `prover-max`). Start: now.

## Pre-release checks (the hub compiles; the dispatcher releases — CLAUDE.md §4 step 0)
Compile each file with `lake env lean <file>` in the main worktree and append one `done:` line under this list per file: the exit code and the error lines, verbatim.
- `docs/tickets/checks/T2005-check.lean`
  done: 2026-10-02 19:35 UTC — `lake env lean docs/tickets/checks/T2005-check.lean`: exit 0; no error lines.

## Approved instructions
(H1–H3 archived in `docs/queue/CONTROL-archive.md`)
- H4 (dispatcher V1, 2026-10-02 19:35 UTC). Compile `docs/tickets/checks/T2005-check.lean` (`lake env lean`, main worktree) and append one `done:` line under Pre-release checks (exit code; error lines verbatim). From now on, compile every file listed under Pre-release checks in the same loop iteration you see it (CLAUDE.md §4 step 0), without a separate H.
  done: 2026-10-02 19:35 UTC — compiled T2005-check.lean: exit 0, no error lines (done: line under Pre-release checks).
- H5 (dispatcher V1, 2026-10-02 19:35 UTC). Stage by name only and commit with message `Dispatcher V1: DECISIONS §9–§11, T2005, ledgers`: `docs/DECISIONS.md`, `docs/ROUTES.md`, `docs/rework-ledger.md`, `docs/tickets/QUEUE.md`, `docs/tickets/T2005.md`, `docs/tickets/checks/T2005-check.lean`, `docs/claude-team/WORKLOG.md`, `docs/queue/CONTROL.md`, `docs/queue/CONTROL-archive.md`; then `git push origin main` (no force; if rejected, stop and report). One `done:` line with the hash.

## Merge log (the hub appends one `done:` line per merge)
done: 2026-10-02 19:05 UTC — T2001 merged a62eeef (report only: state, prove, audit, coverage reports); audit PASS round 2 after one repair; pushed 3c11d7b..a62eeef.

## Pending approval (information only — the hub must NOT act on these)
(none)
