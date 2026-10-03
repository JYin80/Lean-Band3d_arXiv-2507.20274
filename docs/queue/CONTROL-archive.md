
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

## Pre-release lines released 2026-10-03 01:18 UTC (dispatcher V1): T2011, T2012, T2013, T2014
- `docs/tickets/checks/T2011-check.lean` (PT-B2, route H pilot part 2).
  done: 2026-10-03 01:02 UTC — `lake env lean docs/tickets/checks/T2011-check.lean`: exit 0; no error lines.
- `docs/tickets/checks/T2012-check.lean` (MD-2).
  done: 2026-10-03 01:02 UTC — `lake env lean docs/tickets/checks/T2012-check.lean`: exit 0; no error lines.
- `docs/tickets/checks/T2013-check.lean` (MD-3).
- `docs/tickets/checks/T2014-check.lean` (KL2).
  done: 2026-10-03 01:02 UTC — `lake env lean docs/tickets/checks/T2013-check.lean`: exit 0; no error lines.
  done: 2026-10-03 01:12 UTC — `lake env lean docs/tickets/checks/T2014-check.lean`: exit 0; no error lines. (The T2013 line above sits under the T2014 entry because CONTROL was rewritten between the hub's write and the dispatcher's; it refers to T2013.)

## Archived 2026-10-03 05:25 UTC by dispatcher V1

### Pre-release checks (released, tickets merged)
- `docs/tickets/checks/T2015-check.lean` (ST-D1; released conditionally above, DECISIONS §17).
  done: 2026-10-03 01:22 UTC — `lake env lean docs/tickets/checks/T2015-check.lean`: exit 0; no error lines.
- `docs/tickets/checks/T2016-check.lean` (EK-D1; released conditionally above, DECISIONS §17).
  done: 2026-10-03 01:52 UTC — `lake env lean docs/tickets/checks/T2016-check.lean`: exit 0; no error lines. T2016 waits for a free slot (4 of 4 in use).
- `docs/tickets/checks/T2017-check.lean` (PT-C; released conditionally above, DECISIONS §17).
  done: 2026-10-03 02:07 UTC — `lake env lean docs/tickets/checks/T2017-check.lean`: exit 0; no error lines. T2017 waits for a free slot (T2016 takes the slot freed by T2012).
- `docs/tickets/checks/T2018-check.lean` (MD-4; released conditionally above, DECISIONS §17).
  done: 2026-10-03 02:52 UTC — `lake env lean docs/tickets/checks/T2018-check.lean`: exit 0; no error lines. T2018 waits for a free slot (4 of 4 in use).
- `docs/tickets/checks/T2019-check.lean` (PT-D; released conditionally above, DECISIONS §17).
  done: 2026-10-03 03:28 UTC — `lake env lean docs/tickets/checks/T2019-check.lean`: exit 0; no error lines. T2019 starts now (2 slots free).
- `docs/tickets/checks/T2020-check.lean` (KL3; released conditionally above, DECISIONS §17).
  done: 2026-10-03 03:42 UTC — `lake env lean docs/tickets/checks/T2020-check.lean`: exit 0; no error lines. T2020 starts now (1 slot free).
- `docs/tickets/checks/T2021-check.lean` (MD-5; released conditionally above, DECISIONS §17).
  done: 2026-10-03 03:42 UTC — `lake env lean docs/tickets/checks/T2021-check.lean`: exit 0; no error lines. T2021 waits for a free slot.
- `docs/tickets/checks/T2023-check.lean` (PT-F1; released conditionally above, DECISIONS §17).
  done: 2026-10-03 04:12 UTC — `lake env lean docs/tickets/checks/T2023-check.lean`: exit 0; no error lines. T2023 starts now (1 slot free).
- `docs/tickets/checks/T2024-check.lean` (PT-F2; released conditionally above, DECISIONS §17).
  done: 2026-10-03 04:12 UTC — `lake env lean docs/tickets/checks/T2024-check.lean`: exit 0; no error lines. Waits for a free slot.
- `docs/tickets/checks/T2022-check.lean` (EK-1; released conditionally above, DECISIONS §17).
  done: 2026-10-03 04:12 UTC — `lake env lean docs/tickets/checks/T2022-check.lean`: exit 0; no error lines. Waits for a free slot.
- `docs/tickets/checks/T2026-check.lean` (EK-2; released conditionally above, DECISIONS §17).
  done: 2026-10-03 04:42 UTC — `lake env lean docs/tickets/checks/T2026-check.lean`: exit 0; no error lines. T2026 starts now (1 slot free).

### Approved instructions (done)
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
- H13 (dispatcher V1, 2026-10-03 01:33 UTC). T2014 `preflight-fail` (ticket text): `docs/tickets/T2014.md` Amend 1 corrects it. Restart T2014 on its branch at the next free slot (before T2015's successors; T2014 keeps its place in the Released order): stage 1a `preflight` confirms the two amended points only (append to section (a), do not rewrite it), then stage 1b `prover-max` and stage 2 as usual. This is not a RETURN (rule (B) count unchanged). One `done:` line when it restarts.
  done: 2026-10-03 01:56 UTC — T2014 restarted on t/T2014 in the slot freed by T2011 (merged 13dbbc0): workflow wf_66870ea1-906, preflight confirms the two amended points (append to (a)), then prover-max, then auditor.
- H14 (dispatcher V1, 2026-10-03 01:49 UTC). After compiling the T2016 check: stage by name only and commit with message `Dispatcher V1: T2014 Amend 1, ticket T2016 (EK-D1)`: `docs/ROUTES.md`, `docs/tickets/QUEUE.md`, `docs/tickets/T2014.md`, `docs/tickets/T2016.md`, `docs/tickets/checks/T2016-check.lean`, `docs/claude-team/WORKLOG.md`, `docs/queue/CONTROL.md`; then `git push origin main` (no force). One `done:` line with the hash.
  done: 2026-10-03 01:52 UTC — committed 03fd13f (7 files staged by name), pushed to origin/main.
- H15 (dispatcher V1, 2026-10-03 02:05 UTC). After H14 and compiling the T2017 check: stage by name only and commit with message `Dispatcher V1: route H pilot passed (T2011), ticket T2017 (PT-C)`: `docs/DECISIONS.md`, `docs/ROUTES.md`, `docs/rework-ledger.md`, `docs/tickets/QUEUE.md`, `docs/tickets/T2017.md`, `docs/tickets/checks/T2017-check.lean`, `docs/claude-team/WORKLOG.md`, `docs/queue/CONTROL.md`; then `git push origin main` (no force). One `done:` line with the hash.
  done: 2026-10-03 02:07 UTC — committed 110a9a2 (8 files staged by name, after compiling T2017-check: exit 0), pushed to origin/main.
- H16 (dispatcher V1, 2026-10-03 02:20 UTC). After H15 and compiling the T2018 check: stage by name only and commit with message `Dispatcher V1: T2012/T2013 merged bookkeeping, D25, ticket T2018 (MD-4)`: `docs/ROUTES.md`, `docs/paper-deltas.md`, `docs/rework-ledger.md`, `docs/tickets/QUEUE.md`, `docs/tickets/T2018.md`, `docs/tickets/checks/T2018-check.lean`, `docs/claude-team/WORKLOG.md`, `docs/queue/CONTROL.md`; then `git push origin main` (no force). One `done:` line with the hash.
  done: 2026-10-03 02:52 UTC — committed b64efda (8 files staged by name, after compiling T2018-check: exit 0), pushed to origin/main.
- H17 (dispatcher V1, 2026-10-03 03:22 UTC). After compiling the T2019 check: stage by name only and commit with message `Dispatcher V1: T2017 merged bookkeeping, ticket T2019 (PT-D)`: `docs/ROUTES.md`, `docs/rework-ledger.md`, `docs/tickets/QUEUE.md`, `docs/tickets/T2019.md`, `docs/tickets/checks/T2019-check.lean`, `docs/claude-team/WORKLOG.md`, `docs/queue/CONTROL.md`; then `git push origin main` (no force). One `done:` line with the hash.
  done: 2026-10-03 03:28 UTC — committed 022103c (7 files staged by name, after compiling T2019-check: exit 0), pushed to origin/main.
- H18 (dispatcher V1, 2026-10-03 03:37 UTC). After compiling the T2020 and T2021 checks: stage by name only and commit with message `Dispatcher V1: T2014/T2018 merged bookkeeping, tickets T2020 (KL3), T2021 (MD-5)`: `docs/ROUTES.md`, `docs/rework-ledger.md`, `docs/tickets/QUEUE.md`, `docs/tickets/T2020.md`, `docs/tickets/T2021.md`, `docs/tickets/checks/T2020-check.lean`, `docs/tickets/checks/T2021-check.lean`, `docs/claude-team/WORKLOG.md`, `docs/queue/CONTROL.md`; then `git push origin main` (no force). One `done:` line with the hash.
  done: 2026-10-03 03:42 UTC — committed 5d3b282 (9 files staged by name, after compiling T2020/T2021 checks: exit 0 each), pushed to origin/main.
- H19 (dispatcher V1, 2026-10-03 04:10 UTC). After compiling the T2022–T2024 checks: stage by name only and commit with message `Dispatcher V1: DECISIONS §18 (EK-D1 sign-off), tickets T2022 (EK-1), T2023 (PT-F1), T2024 (PT-F2)`: `docs/DECISIONS.md`, `docs/ROUTES.md`, `docs/rework-ledger.md`, `docs/tickets/QUEUE.md`, `docs/tickets/T2022.md`, `docs/tickets/T2023.md`, `docs/tickets/T2024.md`, `docs/tickets/checks/T2022-check.lean`, `docs/tickets/checks/T2023-check.lean`, `docs/tickets/checks/T2024-check.lean`, `docs/claude-team/WORKLOG.md`, `docs/queue/CONTROL.md`; then `git push origin main` (no force). One `done:` line with the hash.
  done: 2026-10-03 04:12 UTC — committed ea34a14 (12 files staged by name, after compiling T2022–T2024 checks: exit 0 each), pushed to origin/main.
- H20 (dispatcher V1, 2026-10-03 04:41 UTC). After compiling the T2025 and T2026 checks: stage by name only and commit with message `Dispatcher V1: T2020/T2021/T2022 merged bookkeeping, tickets T2025 (KL4+5), T2026 (EK-2)`: `docs/ROUTES.md`, `docs/rework-ledger.md`, `docs/tickets/QUEUE.md`, `docs/tickets/T2025.md`, `docs/tickets/T2026.md`, `docs/tickets/checks/T2025-check.lean`, `docs/tickets/checks/T2026-check.lean`, `docs/claude-team/WORKLOG.md`, `docs/queue/CONTROL.md`; then `git push origin main` (no force). One `done:` line with the hash.
  done: 2026-10-03 04:42 UTC — committed 9187a77 (9 files staged by name, after compiling T2025/T2026 checks: exit 0 each), pushed to origin/main.
- H21 (dispatcher V1, 2026-10-03 05:14 UTC). After compiling the T2027–T2033 checks: stage by name only and commit with message `Dispatcher V1: DECISIONS §19 (ST-D1 sign-off), ST1-COMMON, tickets T2027 (PT-G), T2028–T2033 (ST-1 first wave)`: `docs/DECISIONS.md`, `docs/ROUTES.md`, `docs/rework-ledger.md`, `docs/tickets/QUEUE.md`, `docs/tickets/ST1-COMMON.md`, `docs/tickets/T2027.md`, `docs/tickets/T2028.md`, `docs/tickets/T2029.md`, `docs/tickets/T2030.md`, `docs/tickets/T2032.md`, `docs/tickets/T2033.md`, `docs/tickets/T2031.md`, `docs/tickets/checks/T2027-check.lean`, `docs/tickets/checks/T2028-check.lean`, `docs/tickets/checks/T2029-check.lean`, `docs/tickets/checks/T2030-check.lean`, `docs/tickets/checks/T2032-check.lean`, `docs/tickets/checks/T2033-check.lean`, `docs/tickets/checks/T2031-check.lean`, `docs/claude-team/WORKLOG.md`, `docs/queue/CONTROL.md`; then `git push origin main` (no force). One `done:` line with the hash.
  done: 2026-10-03 05:22 UTC — committed 1892ec6 (21 files staged by name, after compiling T2027–T2033 checks: exit 0 each), pushed to origin/main.

## Archived 2026-10-03 05:56 UTC by dispatcher V1

### Approved instructions (done)
- H22 (dispatcher V1, 2026-10-03 05:28 UTC). After compiling the T2034 and T2035 checks: stage by name only and commit with message `Dispatcher V1: CONTROL tidy, tickets T2034 (EK-3), T2035 (EK-5)`: `docs/queue/CONTROL.md`, `docs/queue/CONTROL-archive.md`, `docs/ROUTES.md`, `docs/tickets/QUEUE.md`, `docs/tickets/T2034.md`, `docs/tickets/T2035.md`, `docs/tickets/checks/T2034-check.lean`, `docs/tickets/checks/T2035-check.lean`, `docs/claude-team/WORKLOG.md`; push.
  done: 2026-10-03 05:32 UTC — committed 976030d (9 files staged by name, after compiling T2034/T2035 checks: exit 0 each), pushed to origin/main.
- H23 (dispatcher V1, 2026-10-03 05:42 UTC; DECISIONS §20). (a) T2029: run `docs/tickets/T2029.md` Amend 1 now — one `repairer` stage on t/T2029 (registry lines in `RBM3D/Test/Axioms.lean` only), the registry pre-check, then a round-2 `auditor` on that diff, then resume the merge from step 5. (b) Standing: when two branches both append lines to the registry lists of `RBM3D/Test/Axioms.lean`, resolve the conflict by keeping both sides' lines (union), then run the full build. (c) Standing: a merge that stops at step 5 only on unregistered premises gets state `blocked` with the names (as T2029 did); if the ticket has Amend 1 of DECISIONS §20, run its repairer stage and round-2 audit at once without waiting for the dispatcher. (d) Order: after (a), free slots go to T2034 (EK-3), then T2036 (KL6), then T2033, T2031, T2035 — the Released numbering is the priority order. (e) Stage by name only and commit with message `Dispatcher V1: DECISIONS §20 (registry pre-check), T2029 Amend 1, Amend 1 for T2027–T2035, T2025 merged bookkeeping, ticket T2036 (KL6)`: `docs/DECISIONS.md`, `docs/ROUTES.md`, `docs/rework-ledger.md`, `docs/tickets/QUEUE.md`, `docs/tickets/ST1-COMMON.md`, `docs/tickets/T2027.md` … `docs/tickets/T2036.md` (10 files), `docs/tickets/checks/T2036-check.lean` (after compiling it), `docs/claude-team/WORKLOG.md`, `docs/queue/CONTROL.md`; push.
  done: 2026-10-03 05:47 UTC — (e) T2036 check compiled (exit 0); committed 611830e (18 files staged by name), pushed. (a) started: T2029 Amend 1 repairer + auditor round 2 (workflow wf_68517bfe-28f), in the slot freed by T2027 (merged 6cc5032). (d) T2034 next at the following free slot.

## Archived 2026-10-03 06:15 UTC by dispatcher V1

### Approved instructions (done)
- H24 (dispatcher V1, 2026-10-03 05:56 UTC). After compiling the T2037 and T2038 checks: stage by name only and commit with message `Dispatcher V1: T2027/T2029/T2030 merged bookkeeping (gate PT complete), tickets T2037 (S1-02), T2038 (S1-11)`: `docs/ROUTES.md`, `docs/rework-ledger.md`, `docs/tickets/QUEUE.md`, `docs/tickets/ST1-COMMON.md`, `docs/tickets/T2037.md`, `docs/tickets/T2038.md`, `docs/tickets/checks/T2037-check.lean`, `docs/tickets/checks/T2038-check.lean`, `docs/claude-team/WORKLOG.md`, `docs/queue/CONTROL.md`, `docs/queue/CONTROL-archive.md`; push. Order of the queued tickets is the Released numbering (T2038 before T2031, T2033).
  done: 2026-10-03 06:00 UTC — T2037/T2038 checks compiled (exit 0 each); committed 55f30d1 (11 files staged by name), pushed to origin/main.

## Archived 2026-10-03 06:27 UTC by dispatcher V1

### Approved instructions (done)
- H25 (dispatcher V1, 2026-10-03 06:15 UTC). After compiling the T2039, T2040, T2041 checks: stage by name only and commit with message `Dispatcher V1: T2032 merged bookkeeping, design tickets T2039 (ST-D2), T2040 (LW-D1), T2041 (ST-D3)`: `docs/ROUTES.md`, `docs/rework-ledger.md`, `docs/tickets/QUEUE.md`, `docs/tickets/ST1-COMMON.md`, `docs/tickets/T2039.md`, `docs/tickets/T2040.md`, `docs/tickets/T2041.md`, `docs/tickets/checks/T2039-check.lean`, `docs/tickets/checks/T2040-check.lean`, `docs/tickets/checks/T2041-check.lean`, `docs/claude-team/WORKLOG.md`, `docs/queue/CONTROL.md`, `docs/queue/CONTROL-archive.md`; push.
  done: 2026-10-03 06:19 UTC — T2039/T2040/T2041 checks compiled (exit 0 each); committed 6231342 (13 files staged by name), pushed to origin/main.

## Archived 2026-10-03 07:57 UTC by dispatcher V1

### Approved instructions (done)
- H26 (dispatcher V1, 2026-10-03 06:27 UTC). After compiling the T2042 check: stage by name only and commit with message `Dispatcher V1: T2034 merged bookkeeping, ticket T2042 (EK-4)`: `docs/ROUTES.md`, `docs/rework-ledger.md`, `docs/tickets/QUEUE.md`, `docs/tickets/T2042.md`, `docs/tickets/checks/T2042-check.lean`, `docs/claude-team/WORKLOG.md`, `docs/queue/CONTROL.md`, `docs/queue/CONTROL-archive.md`; push.
  done: 2026-10-03 06:29 UTC — T2042 check compiled (exit 0); committed da72e0a (8 files staged by name), pushed to origin/main.
- H27 (dispatcher V1, 2026-10-03 06:37 UTC; Jun: the hub's usage is at about 5 %, reset expected about 07:49 UTC). Save the remaining usage for T2028: (a) stop the workflows of T2039, T2040 and T2042 now (they are in stage 1a), set each state back to `queued` with reason `paused for the usage limit (H27)`; nothing of theirs is lost but the preflight. (b) Start no new workflow before 07:50 UTC; T2028 keeps running. (c) If any stage fails on the usage limit, set the state `paused: usage limit (<stage>)`; after 07:50 UTC rerun that stage from its start (rule H); it is not a RETURN and not rework. (d) After 07:50 UTC resume in Released order (T2040, T2042, T2039, T2041, …). No commit needed for this instruction; append one `done:` line when (a) is done and one when you resume.
  done: 2026-10-03 06:42 UTC — (a) stopped the workflows of T2040 (stage 1a), T2042 (stage 1a) and T2039 (stage 1a had returned PASS; stopped at the start of stage 1b); states set to `queued` (paused for the usage limit (H27)); branches and worktrees kept. T2028 continues (auditor1 running). No new start before 07:50 UTC.
  done: 2026-10-03 07:52 UTC — (c) T2028 auditor1 had failed twice on the usage limit; stage 2 rerun (workflow wf_ae238841-d6e). (d) resumed in Released order: T2040 (wf_e9fd256f-5f5), T2042 (wf_e344e86f-d18), T2039 (wf_b4d5f757-24c, preflight PASS cached). 4 of 4 slots in use.

## Archived 2026-10-03 08:15 UTC by dispatcher V1

### Approved instructions (done)
- H28 (dispatcher V1, 2026-10-03 07:57 UTC). After compiling the T2043 and T2044 checks: stage by name only and commit with message `Dispatcher V1: T2031/T2036/T2038 merged bookkeeping, H27 usage pause, tickets T2043 (KL7a), T2044 (S1-13)`: `docs/ROUTES.md`, `docs/rework-ledger.md`, `docs/tickets/QUEUE.md`, `docs/tickets/T2043.md`, `docs/tickets/T2044.md`, `docs/tickets/checks/T2043-check.lean`, `docs/tickets/checks/T2044-check.lean`, `docs/claude-team/WORKLOG.md`, `docs/queue/CONTROL.md`, `docs/queue/CONTROL-archive.md`; push. Standing from now (also in the note below): scratch files of each workflow go to `scratchpad/<ticket>/`.
  done: 2026-10-03 08:02 UTC — T2043/T2044 checks compiled (exit 0 each); committed efc8a7f (10 files staged by name), pushed to origin/main. Workflow prompts now name the scratch subdirectory `scratchpad/<ticket>/`.
