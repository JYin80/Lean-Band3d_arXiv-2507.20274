
## Archived 2026-10-02 17:41 UTC by dispatcher V1

### Pre-release checks (released)
- `docs/tickets/checks/T2001-check.lean`
- `docs/tickets/checks/T2002-check.lean`
- `docs/tickets/checks/T2003-check.lean`
- `docs/tickets/checks/T2004-check.lean`
  done: 2026-10-02 17:32 UTC — `lake env lean docs/tickets/checks/T2001-check.lean`: exit 0; no error lines.
  done: 2026-10-02 17:32 UTC — `lake env lean docs/tickets/checks/T2002-check.lean`: exit 0; no error lines.
  done: 2026-10-02 17:32 UTC — `lake env lean docs/tickets/checks/T2003-check.lean`: exit 0; no error lines.
  done: 2026-10-02 17:32 UTC — `lake env lean docs/tickets/checks/T2004-check.lean`: exit 0; no error lines.


### Approved instructions (done)
- H1 (RBM2D dispatcher V2, 2026-10-02 16:48 UTC; framework install, Jun: 「在 RBM3D 文件夹里把这些流程安排的方法写在他们的相关文件里」). In the main worktree:
  1. `git status` must show only the framework changes below (and possibly `build.log`). If anything else is dirty, stop and report.
  2. Stage by name only: `CLAUDE.md` (new), `.gitignore`, `.claude/agents/*.md`, `.claude/settings.json`, `docs/claude-team/TEAM.md`, `docs/claude-team/STARTUP.md`, `docs/claude-team/DISPATCHER-PROMPT.txt`, `docs/claude-team/hb.sh`, `docs/claude-team/WORKLOG.md`, `docs/claude-team/tools/` (all files), `docs/queue/CONTROL.md`, `docs/tickets/README.md`, `docs/tickets/QUEUE.md`, `docs/reports/README.md`, `docs/supervisor/README.md`, `docs/supervisor/requests/README.md`, `docs/DECISIONS.md`, `docs/HANDOFF.md`, `docs/ROUTES.md`, `docs/rework-ledger.md`, `docs/archive/2026-10-02-old-workmode/` (all files), and the removals of `docs/TASKS.md` and `docs/QUEUE.md` (`git add docs/TASKS.md docs/QUEUE.md` stages the deletions).
  3. Commit with message `Team mode: dispatcher/supervisor/hub framework (from RBM2D); archive old work mode`, then `git push origin main` (no force; if rejected, stop and report).
  4. Run `lake build` once (no Lean changed) and write one `done:` line with the commit hash and the build result (job count, axiom-audit line).
  done: 2026-10-02 17:02 UTC — committed 89ef8a9 (31 paths staged by name; git status clean otherwise), pushed ea323b7..89ef8a9 to origin/main; `lake build` exit 0, "Build completed successfully (3253 jobs).", axiom audit: "509 theorems, 173 definitions, 0 axioms in `RBM`".

- H2 (dispatcher V1, 2026-10-02 17:26 UTC). Under HOLD: compile the four files listed under Pre-release checks (`lake env lean docs/tickets/checks/T200N-check.lean`, N = 1…4, in the main worktree) and append one `done:` line per file under that list (exit code; error lines verbatim). Start no ticket.
  done: 2026-10-02 17:32 UTC — compiled the four check files; all exit 0, no error lines (done: lines under Pre-release checks). No ticket started.
- H3 (dispatcher V1, 2026-10-02 17:26 UTC). After H2: stage by name only and commit with message `Dispatcher V1: DECISIONS §3–§7, routes, first tickets T2001–T2004`: `docs/DECISIONS.md`, `docs/paper-deltas.md`, `docs/PLAN.md`, `docs/STATUS.md`, `docs/ROUTES.md`, `docs/claude-team/TEAM.md`, `docs/claude-team/WORKLOG.md`, `docs/tickets/QUEUE.md`, `docs/tickets/T2001.md`, `docs/tickets/T2002.md`, `docs/tickets/T2003.md`, `docs/tickets/T2004.md`, `docs/tickets/checks/T2001-check.lean`, `docs/tickets/checks/T2002-check.lean`, `docs/tickets/checks/T2003-check.lean`, `docs/tickets/checks/T2004-check.lean`, `docs/queue/CONTROL.md`. Then `git push origin main` (no force; if rejected, stop and report). No `lake build` needed (no Lean under `RBM3D/` changed). One `done:` line with the hash.
  done: 2026-10-02 17:32 UTC — committed 3c11d7b (17 files staged by name), pushed 89ef8a9..3c11d7b to origin/main; no lake build (no Lean under RBM3D/ changed).


## Archived 2026-10-02 19:49 UTC by dispatcher V1

### Pre-release checks (released)
- `docs/tickets/checks/T2005-check.lean`
  done: 2026-10-02 19:35 UTC — `lake env lean docs/tickets/checks/T2005-check.lean`: exit 0; no error lines.


### Approved instructions (done)
(H1–H3 archived in `docs/queue/CONTROL-archive.md`)
- H4 (dispatcher V1, 2026-10-02 19:35 UTC). Compile `docs/tickets/checks/T2005-check.lean` (`lake env lean`, main worktree) and append one `done:` line under Pre-release checks (exit code; error lines verbatim). From now on, compile every file listed under Pre-release checks in the same loop iteration you see it (CLAUDE.md §4 step 0), without a separate H.
  done: 2026-10-02 19:35 UTC — compiled T2005-check.lean: exit 0, no error lines (done: line under Pre-release checks).
- H5 (dispatcher V1, 2026-10-02 19:35 UTC). Stage by name only and commit with message `Dispatcher V1: DECISIONS §9–§11, T2005, ledgers`: `docs/DECISIONS.md`, `docs/ROUTES.md`, `docs/rework-ledger.md`, `docs/tickets/QUEUE.md`, `docs/tickets/T2005.md`, `docs/tickets/checks/T2005-check.lean`, `docs/claude-team/WORKLOG.md`, `docs/queue/CONTROL.md`, `docs/queue/CONTROL-archive.md`; then `git push origin main` (no force; if rejected, stop and report). One `done:` line with the hash.
  done: 2026-10-02 19:35 UTC — committed 4908ddf (9 files staged by name), pushed a62eeef..4908ddf to origin/main.


## Archived 2026-10-02 23:42 UTC by dispatcher V1

### Pre-release checks (released)
- `docs/tickets/checks/T2006-check.lean`
  done: 2026-10-02 23:22 UTC — `lake env lean docs/tickets/checks/T2006-check.lean`: exit 0; no error lines.
- `docs/tickets/checks/T2007-check.lean`
  done: 2026-10-02 23:22 UTC — `lake env lean docs/tickets/checks/T2007-check.lean`: exit 0; no error lines.


### Approved instructions (done)
- H6 (dispatcher V1, 2026-10-02 23:17 UTC). T2003: dispatcher sign-off given (DECISIONS §13). Merge T2003 as report-only (CLAUDE.md §3 (A), report-only path): commit `docs/queue/T2003.state` (set `merged <hash>`), `docs/reports/T2003-prove.md`, `docs/reports/T2003-audit.md`; the probe `RBM3D/Probe/T2003Pins.lean` stays on `t/T2003`; no root import, no `lake build`. Push main; one `done:` line under the merge log.
  done: 2026-10-02 23:22 UTC — T2003 merged 7ba7ba5 (report only); pushed 06f2064..7ba7ba5; merge-log line written.

## Pre-release lines released 2026-10-03 00:00 UTC (dispatcher V1)
- `docs/tickets/checks/T2008-check.lean`
  done: 2026-10-02 23:52 UTC — `lake env lean docs/tickets/checks/T2008-check.lean`: exit 0; no error lines.  → T2008 released.
- `docs/tickets/checks/T2009-check.lean` (first version)
  done: 2026-10-02 23:52 UTC — `lake env lean docs/tickets/checks/T2009-check.lean`: exit 1; error lines: `docs/tickets/checks/T2009-check.lean:10:8: error(lean.unknownIdentifier): Unknown constant `Real.cosh_le_exp_half_sq``  → import added, recheck.
- `docs/tickets/checks/T2009-check.lean` (revised 2026-10-02 23:59 UTC)
  done: 2026-10-03 00:01 UTC — `lake env lean docs/tickets/checks/T2009-check.lean` (revised): exit 0; no error lines.  → T2009 released 2026-10-03 00:08 UTC.
- `docs/tickets/checks/T2010-check.lean`
  done: 2026-10-03 00:12 UTC — `lake env lean docs/tickets/checks/T2010-check.lean`: exit 0; no error lines.  → T2010 released 2026-10-03 00:16 UTC (starts at the next free slot).

## Released-ticket lines removed 2026-10-03 00:53 UTC (merged)
- T2006 (MD-1) merged 0a873f1 at 00:38 UTC; T2009 (PT-B1) merged 73cf5c1 at 00:40 UTC; T2010 (PT-E) merged 315e65e at 00:41 UTC (merge log in CONTROL).
