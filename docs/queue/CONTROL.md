# CONTROL — written only by the dispatcher (Cowork). The hub may only append `done:` lines under Approved instructions.

mode: RUN
parallel: 4
updated: 2026-10-05 03:51 UTC (dispatcher V1: CONTROL archived (H60–H72, old merge log); H73 commits the dispatcher files; T2167–T2170 running, T2171–T2174 queued)
reason: RUN (Jun, DECISIONS §8). Scope and rules: DECISIONS §3–§7.

The standing hub rules are in CLAUDE.md §3 (auto-merge, one automatic repair per RETURN, date -u, report headers, private helpers, nothing undecided starts, parallelism, API errors).

## Released tickets (only those not yet merged)
Priority order (CLAUDE.md §3 (G)); at most `parallel` workflows at once.
130. T2161 — `docs/tickets/T2161.md` (BA-D1, block Anderson design (report only)); audit PASS, both sign-off items settled by Jun (DECISIONS §51 bulk form `ρ_N(E) ≥ κ`, §52 BA approved, cap 70) — merge per H71.
136. T2167 — `docs/tickets/T2167.md` (S3-10b, `Induction/NQGood2` (non-alternating good-set inputs part 2: classes and constants, the `GridAssemblyHypN` fields, the QV constant, `subGaussStop_nonAltN`; §49); role `prover-hard`). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).
137. T2168 — `docs/tickets/T2168.md` (ST2-12, `Path/DifREP1` (`STGridRepN` part 1: grid split, remainder bound, assembly from the two tails; ST2-13a/b follow); role `prover-hard`). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).
138. T2169 — `docs/tickets/T2169.md` (S5-24, `Evolution/CltMoments2` (CLT moment counting part 2: `(eq:2p_product)` expansion, isolated/paired split, Markov); role `prover-hard`). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).
139. T2170 — `docs/tickets/T2170.md` (LW-11a, `Graph/AuxGraph` (auxiliary graph, `GtoAG`, scalemole, nested form; claim:xi to LW-11b); role `prover-hard`). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).
140. T2171 — `docs/tickets/T2171.md` (S5-06, `Path/LemDecCalEdif` (`res_deccalE_dif` part 1; S5-07 follows in `LemDecCalEdif2`); role `prover-hard`). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).
141. T2172 — `docs/tickets/T2172.md` (S5-08, `Path/LemDecCalEwG` (`res_deccalE_wG`); role `prover-hard`). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).
142. T2173 — `docs/tickets/T2173.md` + `T2173-amend-1.md` (BA-DS (label per Amend 1), block Anderson form of Claim (417) (design supplement, report only; §48 (i), §52); role `prover-max`). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).
143. T2174 — `docs/tickets/T2174.md` (UN-01, `Universality/Pins` (the UN-D1 probe promoted to the library: vocabulary, pins, rows, registry lines; DECISIONS §50); role `prover`). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).

## Pre-release checks (the hub compiles in the same loop iteration; the dispatcher releases — CLAUDE.md §4 step 0, H4)
Compile each file with `lake env lean <file>` in the main worktree and append one `done:` line under this list per file: the exit code and the error lines, verbatim.
- `docs/tickets/checks/T2167-check.lean` (S3-10b; released conditionally above, DECISIONS §17).
- `docs/tickets/checks/T2168-check.lean` (ST2-12; released conditionally above, DECISIONS §17).
- `docs/tickets/checks/T2169-check.lean` (S5-24; released conditionally above, DECISIONS §17).
- `docs/tickets/checks/T2170-check.lean` (LW-11a; released conditionally above, DECISIONS §17).
- `docs/tickets/checks/T2171-check.lean` (S5-06; released conditionally above, DECISIONS §17).
- `docs/tickets/checks/T2172-check.lean` (S5-08; released conditionally above, DECISIONS §17).
- `docs/tickets/checks/T2173-check.lean` (BA-DS; released conditionally above, DECISIONS §17).
- `docs/tickets/checks/T2174-check.lean` (UN-01; released conditionally above, DECISIONS §17).

## Approved instructions
- H12 (dispatcher V1, 2026-10-03 01:19 UTC). Standing from now (DECISIONS §17): a Released ticket whose start condition names its Pre-release check starts in the same loop iteration in which you compile that check with exit 0, if a slot is free. Now: stage by name only and commit with message `Dispatcher V1: T2011–T2014 released, ticket T2015 (ST-D1), DECISIONS §17`: `docs/DECISIONS.md`, `docs/tickets/QUEUE.md`, `docs/tickets/T2015.md`, `docs/tickets/checks/T2015-check.lean`, `docs/claude-team/WORKLOG.md`, `docs/queue/CONTROL.md`, `docs/queue/CONTROL-archive.md`; then `git push origin main` (no force). One `done:` line with the hash.
  done: 2026-10-03 01:22 UTC — committed c950f27 (7 files staged by name), pushed to origin/main. T2015 check exit 0; T2015 waits for a free slot (4 of 4 in use by T2011, T2013, T2012, T2014).
- H73 (dispatcher V1, 2026-10-05 03:51 UTC; replaces the commit part of H60, which was never executed). Commit the dispatcher's files that have been waiting since H52. In the main worktree: (1) build the file list by script, `git status --porcelain --untracked-files=all -- docs/DECISIONS.md docs/ROUTES.md docs/rework-ledger.md docs/paper-deltas.md docs/tickets docs/claude-team docs/queue/CONTROL.md docs/queue/CONTROL-archive.md docs/supervisor | awk '{print $2}' | grep -v __pycache__ > /tmp/H73-files.txt` (it must contain no path under `RBM3D/`, `docs/reports/` or `docs/queue/T*.state`; if it does, stop and report); (2) `git add -- $(cat /tmp/H73-files.txt)` (explicit names, no `-A`, no `.`); (3) commit with message `Dispatcher V1: bookkeeping D158–D404, DECISIONS §32–§53, tickets T2095–T2174, supervisor verdicts, CONTROL archive (H73)`; (4) `git push origin main` (no force). One `done:` line with the hash and the number of files. Do this in the next loop iteration; it does not touch any running ticket.
(H1–H11, H13–H72 archived in `docs/queue/CONTROL-archive.md`. Standing from H4: compile every file listed under Pre-release checks in the same loop iteration you see it. Standing from H23 (DECISIONS §20): (b) when two branches both append lines to the registry lists of `RBM3D/Test/Axioms.lean`, keep both sides (union), then run the full build; (c) a merge that stops at step 5 only on unregistered premises gets state `blocked` with the names, and if the ticket has an Amend 1 of DECISIONS §20 you run its `repairer` stage for the registry lines and a round-2 `auditor` of that diff at once. Standing from H28: every workflow keeps its scratch files in its own subdirectory `scratchpad/<ticket>/` (T2036 report (d): concurrent workflows overwrote each other's generic file names).)


## Merge log (the hub appends one `done:` line per merge)
done: Sun Oct  4 22:41:19 UTC 2026 — T2163 merged 69b1099 (RBM3D/Induction/IniTermII.lean, RBM3D/Test/Axioms.lean (STIniTermII removed as proved, H23 b), root import; lake build 3936 jobs); audit PASS round 1; pushed.
done: Sun Oct  4 23:12:15 UTC 2026 — T2162 merged 04aedec (report only: state, prove, audit, portmap reports; probe RBM3D/Probe/T2162Pins.lean stays on t/T2162 at 73b451c); audit PASS round 1, sign-off per H70 (DECISIONS §48); pushed.
done: Sun Oct  4 23:31:04 UTC 2026 — T2151 merged 32d895b (RBM3D/Graph/LocalRegular2.lean, root import; lake build 3937 jobs); audit PASS round 1 after Amend 1 (H69); pushed.
done: Sun Oct  4 23:39:58 UTC 2026 — T2165 merged daa7cc1 (RBM3D/Evolution/CltMoments1.lean, root import; lake build 3938 jobs); audit PASS round 2 after one repair (rule B); pushed.
done: Mon Oct  5 01:20:07 UTC 2026 — T2166 merged 691566a (RBM3D/Induction/NQGood1.lean, root import; lake build 3941 jobs); audit PASS round 1 (stage 1b rerun after session-limit API error, rule H); pushed.
done: Mon Oct  5 03:02:16 UTC 2026 — T2161 merged 87f617a (report only: state, prove, audit, portmap reports; probe RBM3D/Probe/T2161Pins.lean stays on t/T2161 at 82e72b3); audit PASS round 1, sign-off per H71 (DECISIONS §51, §52); pushed.

## Pending approval (information only — the hub must NOT act on these)
(none)
