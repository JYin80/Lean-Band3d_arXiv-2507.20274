# CONTROL — written only by the dispatcher (Cowork). The hub may only append `done:` lines under Approved instructions.

mode: HOLD
parallel: 4
updated: 2026-10-02 16:48 UTC (framework installed by the RBM2D dispatcher V2 at Jun's request; DECISIONS §1)
reason: HOLD until Jun confirms scope and fidelity (DECISIONS §2). The hub executes Approved instructions only.

The standing hub rules are in CLAUDE.md §3 (auto-merge, one automatic repair per RETURN, date -u, report headers, private helpers, nothing undecided starts, parallelism, API errors).

## Released tickets (only those not yet merged)
(none)

## Pre-release checks (the hub compiles; the dispatcher releases — CLAUDE.md §4 step 0)
Compile each file with `lake env lean <file>` in the main worktree and append one `done:` line under this list per file: the exit code and the error lines, verbatim.

## Approved instructions
- H1 (RBM2D dispatcher V2, 2026-10-02 16:48 UTC; framework install, Jun: 「在 RBM3D 文件夹里把这些流程安排的方法写在他们的相关文件里」). In the main worktree:
  1. `git status` must show only the framework changes below (and possibly `build.log`). If anything else is dirty, stop and report.
  2. Stage by name only: `CLAUDE.md` (new), `.gitignore`, `.claude/agents/*.md`, `.claude/settings.json`, `docs/claude-team/TEAM.md`, `docs/claude-team/STARTUP.md`, `docs/claude-team/DISPATCHER-PROMPT.txt`, `docs/claude-team/hb.sh`, `docs/claude-team/WORKLOG.md`, `docs/claude-team/tools/` (all files), `docs/queue/CONTROL.md`, `docs/tickets/README.md`, `docs/tickets/QUEUE.md`, `docs/reports/README.md`, `docs/supervisor/README.md`, `docs/supervisor/requests/README.md`, `docs/DECISIONS.md`, `docs/HANDOFF.md`, `docs/ROUTES.md`, `docs/rework-ledger.md`, `docs/archive/2026-10-02-old-workmode/` (all files), and the removals of `docs/TASKS.md` and `docs/QUEUE.md` (`git add docs/TASKS.md docs/QUEUE.md` stages the deletions).
  3. Commit with message `Team mode: dispatcher/supervisor/hub framework (from RBM2D); archive old work mode`, then `git push origin main` (no force; if rejected, stop and report).
  4. Run `lake build` once (no Lean changed) and write one `done:` line with the commit hash and the build result (job count, axiom-audit line).

## Merge log (the hub appends one `done:` line per merge)

## Pending approval (information only — the hub must NOT act on these)
(none)
