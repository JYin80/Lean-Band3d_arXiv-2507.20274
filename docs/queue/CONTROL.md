# CONTROL — written only by the dispatcher (Cowork). The hub may only append `done:` lines under Approved instructions and lines under the Merge log.

mode: RUN
parallel: 4
updated: 2026-10-11 09:42 UTC (dispatcher V2: T2415 merged, line removed; T2416 running)
reason: RUN (dispatcher V2 from 2026-10-09 19:24 UTC, DECISIONS §166–§167). Normal operation: new tickets are released here as their inputs merge (HANDOFF §2). Jun authorized rule (A) merges in the hub session (2026-10-10 ~00:55 UTC, H155 done lines).

The standing hub rules are in CLAUDE.md §3 (auto-merge, one automatic repair per RETURN, date -u, report headers, private helpers, nothing undecided starts, parallelism, API errors).

## Released tickets (only those not yet merged)
Priority order (CLAUDE.md §3 (G)); at most `parallel` workflows at once.
379. T2411 — `docs/tickets/T2411.md` (BA-G5b, new `BA/GreenCond.lean`, `GreenCond2.lean`: m5, threshold families, R6, `BAFamGain`, `BAFAav`; registry two removals): released; starts when its check compiles and a slot is free (H12). Priority: after T2410. Not in the certificate lane.
381. T2413 — `docs/tickets/T2413.md` (BA TL-D: design of stage TL, report only; supervisor 0853 REQ-TLS, TL-C1 to TL-C4; probe `RBM3D/Probe/T2413Pins.lean` never merged): released; starts when its check compiles and a slot is free (H12). **Priority: first.** Not in the certificate lane.
382. T2414 — `docs/tickets/T2414.md` (BA-T T8b: the generic drift kernel of Step 2, `Chain/Step2Gen` + `Chain/NewKLKGen` in place, optional new `Chain/Step2Kern`; supervisor 0853 BAT-F1 (a)–(e), BAT-F2; design-gate 1a with a `prover-max` probe step, 1a-audit, 1b `prover-hard`): released; starts when its check compiles and a slot is free (H12). Priority: after T2413. Not in the certificate lane (reverse cone of `Chain/Step2Gen`: 76 modules, no `Graph/LWExpCert*`).
384. T2416 — `docs/tickets/T2416.md` (BA-T T2-BA with T6-BA: new `BA/EMn2BA.lean`, the three fact blocks of T2404 at BA, BAT-C2 composition lemma, `STEMn2PolygL`/J form/Ĵ form at BA, `STContractM` instance; supervisor 0853 REQ-BAT Q1, Q2): released; starts when its check compiles and a slot is free (H12). Priority: after T2415. Not in the certificate lane.

## Pre-release checks
- `docs/tickets/checks/T2416-check.lean` (BA-T T2-BA; merged names only).
- `docs/tickets/checks/T2413-check.lean` (BA TL-D; merged names only).
- `docs/tickets/checks/T2414-check.lean` (BA-T T8b; merged names and two G1 `example`s).
- `docs/tickets/checks/T2411-check.lean` (BA-G5b; merged names only).
  done: Sat Oct 10 12:43:41 UTC 2026 — `lake env lean docs/tickets/checks/T2387-check.lean` on main 61849a6: exit 0, no error lines.
  done: Sat Oct 10 12:53:23 UTC 2026 — `lake env lean docs/tickets/checks/T2389-check.lean` on main 69b7abc: exit 0, no error lines.
  done: Sat Oct 10 13:03:16 UTC 2026 — `lake env lean docs/tickets/checks/T2390-check.lean` on main bf5f0d5: exit 0, no error lines.

## Approved instructions
Standing instructions carried over from the archived CONTROL (verbatim):
(H1–H11, H13–H72 archived in `docs/queue/CONTROL-archive.md`. Standing from H4: compile every file listed under Pre-release checks in the same loop iteration you see it. Standing from H23 (DECISIONS §20): (b) when two branches both append lines to the registry lists of `RBM3D/Test/Axioms.lean`, keep both sides (union), then run the full build; (c) a merge that stops at step 5 only on unregistered premises gets state `blocked` with the names, and if the ticket has an Amend 1 of DECISIONS §20 you run its `repairer` stage for the registry lines and a round-2 `auditor` of that diff at once. Standing from H28: every workflow keeps its scratch files in its own subdirectory `scratchpad/<ticket>/` (T2036 report (d): concurrent workflows overwrote each other's generic file names).)
- H12 (dispatcher V1, 2026-10-03 01:19 UTC). Standing from now (DECISIONS §17): a Released ticket whose start condition names its Pre-release check starts in the same loop iteration in which you compile that check with exit 0, if a slot is free.
- H101 (dispatcher V1, 2026-10-06 14:59 UTC; DECISIONS §108 (1); answers the question in `docs/queue/T2306.state`). T2306's build rule is relaxed so that it does not idle the other slots: (1) the three certificate modules `LWExpCert`, `LWExpCertS0`, `LWExpCertS1` are always built one at a time (`lake build <module>`, never two certificate modules concurrently, in stage 1b, stage 2 and merge); (2) other workflows keep running; (3) while a certificate-module build of T2306 runs, the hub starts no new workflow and no other worktree's full `lake build`; (4) before each certificate-module build, if the machine's free memory is below 12 GB, wait until a running build finishes; (5) if a certificate build is killed or swaps heavily, retry it when no other build runs, and say so in the done line. Start T2306 now in the next free slot (it is first in the list). Report each module's wall time and peak memory in the prove report as the ticket asks. One `done:` line.
- H122 (dispatcher V1, 2026-10-08 04:08 UTC; DECISIONS §135 (5); takes effect at once). **H101 (3) is relaxed:** while a certificate-module build (`LWExpCert*`, T2319 now and any later certificate ticket) runs, the hub **may start new workflows** (their stage 1a preflight runs no `lake`); single-module `lake build`s of other worktrees follow H101 (4) (wait while free memory < 12 GB); **no other full `lake build`** runs during a certificate-module build (merge builds wait for it). H101 (1), (2), (4), (5) unchanged.

- H155 (dispatcher V2, 2026-10-09 21:55 UTC; relays Jun's authorization). **Jun's words** (Cowork dispatcher session, 2026-10-09 ~21:47 UTC, replying to the dispatcher's request that he allow the held merges of T2356, T2358, T2361 and T2362 in the hub session): 「我允许你告诉他吧， 我现在没法用那台电脑」 ("I allow it — you tell him; I can't use that computer right now"). So Jun authorizes the CLAUDE.md §3 rule (A) merge actions for the four `audit-pass` tickets **T2361, T2356, T2358, T2362** (in this order) and for later rule-(A) merges of released tickets: bring in exactly the ticket's sole writable files from `t/T####` into `main`, add the root import after the last `import` line of `RBM3D.lean`, run the full `lake build`, commit the ticket's files + `RBM3D.lean` + state + reports with message `T####: merge <title>`, and `git push origin main` (main only, never force). Retry the four merges now, one at a time, each with its own full build (T2362 also edits `BA/FlowPins.lean` lines 272–276; T2358's audit-pass is round 2 after Amend 2). If the session permission check still denies an action, stop there, keep the state `audit-pass`, and say in the `done:` line exactly which action was denied. One `done:` line per merge.
  done: Sat Oct 10 00:56:16 UTC 2026 — T2361 merged 16b812a under Jun's direct authorization in the hub session (Jun at the Mac, Sat Oct 10 00:56:16 UTC 2026); the earlier attempts were denied by the session permission check at rule (A) step 3 (checkout of PathBounds.lean into main + root import).
  done: Sat Oct 10 00:57:36 UTC 2026 — T2356 merged 96f2390 under Jun's direct authorization in the hub session.
  done: Sat Oct 10 00:59:00 UTC 2026 — T2358 merged c587dcd under Jun's direct authorization in the hub session.
  done: Sat Oct 10 01:01:53 UTC 2026 — T2362 merged 8050043 under Jun's direct authorization in the hub session.

- H176 (standing; full text archived 2026-10-10 23:13 UTC): merges that rebuild `Graph/LWExpCert*` go one at a time; order: stage-K and critical-path first, then T8 and U3s1, then by dependency. 1a and 1b keep running in parallel.

- H183 (3) (standing; full text archived 2026-10-10 23:13 UTC): when a 1a-audit verdict says "Needs dispatcher sign-off", stage 1b does not start until an H line answers it; set the state `blocked` with the question.

- H208 (dispatcher V2, 2026-10-11 08:46 UTC; DECISIONS §227). Commit by name with your next commit `docs/supervisor/requests/REQ-2026-10-11-0845-L4.md`, `docs/DECISIONS.md`, `docs/queue/CONTROL.md`, `docs/claude-team/WORKLOG.md`, `docs/rework-ledger.md`. Nothing else. One `done:` line.
  done: Sun Oct 11 08:51:19 UTC 2026 — the 5 listed files committed by name in 1653a95 (with states T2398/T2410), pushed.

- H209 (dispatcher V2, 2026-10-11 09:01 UTC; DECISIONS §228). (1) Commit by name with your next commit `docs/tickets/T2413.md`, `docs/tickets/checks/T2413-check.lean`, `docs/tickets/T2414.md`, `docs/tickets/checks/T2414-check.lean`, `docs/supervisor/requests/REQ-2026-10-11-0845-L4.md`, `docs/ROUTES.md`, `docs/DECISIONS.md`, `docs/queue/CONTROL.md`, `docs/claude-team/WORKLOG.md`, `docs/rework-ledger.md`. Nothing else. (2) Compile the two checks on `main` in the same loop iteration; start T2413 and T2414 (slots: T2411, T2412 running). One `done:` line per item.
  done: Sun Oct 11 09:01:51 UTC 2026 — (1) the 10 listed files committed by name in c33ef56, pushed.
  done: Sun Oct 11 09:01:51 UTC 2026 — (2) T2413, T2414 checks on main c33ef56: exit 0, no error lines (both); started: T2413 wf_8faef704-c3b (preflight → prover-max design + probe → auditor), T2414 wf_5bc0b82c-365 (1a design gate → probe prover-max → 1a-audit → 1b prover-hard → auditor). Running: T2411, T2412, T2413, T2414 (4 of 4).

- H210 (dispatcher V2, 2026-10-11 09:04 UTC; DECISIONS §229). (1) Commit by name with your next commit `docs/tickets/T2415.md`, `docs/tickets/checks/T2415-check.lean`, `docs/tickets/T2416.md`, `docs/tickets/checks/T2416-check.lean`, `docs/DECISIONS.md`, `docs/queue/CONTROL.md`, `docs/queue/CONTROL-archive.md` (H201–H207 and eight merge-log lines archived 09:05 UTC), `docs/ROUTES.md` (BA count 83), `docs/claude-team/WORKLOG.md`. Nothing else (may share a commit with H209). (2) Compile the two checks on `main`; T2415 and T2416 start as slots free, after T2413 and T2414 (priority order). One `done:` line per item.
  done: Sun Oct 11 09:11:34 UTC 2026 — (1) the 9 listed files committed by name in 9d84020 (with states T2413/T2414), pushed.
  done: Sun Oct 11 09:11:34 UTC 2026 — (2) checks on main 9d84020: T2415 exit 0 errors 0; T2416 exit 0 errors 0; no error lines. No slot free (T2411, T2412, T2413, T2414 running); T2415 then T2416 start as slots free.
  done: Sun Oct 11 09:15:03 UTC 2026 — T2415 started in the slot freed by T2412 (merged 260732c): wf_073f9073-e63 (preflight → prover-hard → auditor). Running: T2411, T2413, T2414, T2415 (4 of 4); T2416 next.
  done: Sun Oct 11 09:29:18 UTC 2026 — T2416 started in the slot freed by T2415 (merged 54ecfc4): wf_801eeb46-c61 (preflight → prover-hard → auditor). Running: T2411, T2413, T2414, T2416 (4 of 4); queue empty.

- H211 (dispatcher V2, 2026-10-11 09:27 UTC; DECISIONS §230). Commit by name with your next commit `docs/DECISIONS.md`, `docs/queue/CONTROL.md`, `docs/claude-team/WORKLOG.md`, `docs/rework-ledger.md`. Nothing else. One `done:` line.
  done: Sun Oct 11 09:31:20 UTC 2026 — the 4 listed files committed by name in 99885b3 (with states T2412/T2415/T2416), pushed.

- H212 (dispatcher V2, 2026-10-11 09:42 UTC; DECISIONS §231). Commit by name with your next commit `docs/DECISIONS.md`, `docs/queue/CONTROL.md`, `docs/claude-team/WORKLOG.md`, `docs/rework-ledger.md`. Nothing else. One `done:` line.

## Merge log (the hub appends one `done:` line per merge; earlier lines are in CONTROL-archive.md)
done: Sun Oct 11 08:34:36 UTC 2026 — T2398 report-only merge 7b0a10a under Amend 2 (BA LW-14 design gate, route R1: probe Twist section with BATwistAvgLaw, twK, BATwistLoopLaw (D2), row table under R1 with the new row L4t, 10,858 central lines (D3), paper delta T2398d (D4); design (b′) 113 lines; probe RBM3D/Probe/T2398Pins.lean (498 lines, standard axioms) stays on t/T2398 at 6429bb5; audit PASS claude-opus-5-5; pushed).
done: Sun Oct 11 08:46:23 UTC 2026 — T2410 merged 7c0f55a (BA-L2c2b: new Graph/BAGGOp (1852 lines, stop 2000; gg2/gg4 verbatim from T2395, baExpFrame_gg, BAexpFrameE, baExpFrameE_holds, counters/order, instances), root import, no registry change; audit PASS claude-opus-5-5; full lake build 4222 jobs; pushed).
done: Sun Oct 11 09:14:54 UTC 2026 — T2412 merged 260732c (BA-L3c2: new Graph/BASizeClaim (1167) and Graph/BASizeClaim2 (825), each under the 2,000 stop; T1-T5 and instances; two root imports (conflict with BAGGOp import resolved as union), no registry change; probe RBM3D/Probe/T2412Pins.lean (303 lines) not merged, stays on t/T2412 at 668318f; 1a-audit PASS, audit PASS claude-opus-5-5; full lake build 4224 jobs; pushed).
done: Sun Oct 11 09:29:09 UTC 2026 — T2415 merged 54ecfc4 (T8-BA: new BA/Step2BA (209 lines, stop 900; 16 declarations, standard axioms), root import, no registry change; audit PASS claude-opus-5-5; full lake build 4225 jobs; pushed).
