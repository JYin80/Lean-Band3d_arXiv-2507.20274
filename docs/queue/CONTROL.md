# CONTROL — written only by the dispatcher (Cowork). The hub may only append `done:` lines under Approved instructions.

mode: RUN
parallel: 4
updated: 2026-10-03 05:28 UTC (dispatcher V1: CONTROL tidied (merged Pre-release entries, H7–H11, H13–H21 archived); T2034 (EK-3), T2035 (EK-5) released on check exit 0; H22)
reason: RUN (Jun, DECISIONS §8). Scope and rules: DECISIONS §3–§7.

The standing hub rules are in CLAUDE.md §3 (auto-merge, one automatic repair per RETURN, date -u, report headers, private helpers, nothing undecided starts, parallelism, API errors).

## Released tickets (only those not yet merged)
Priority order (CLAUDE.md §3 (G)); at most `parallel` workflows at once.
16. T2025 — `docs/tickets/T2025.md` (KL4+KL5, uniqueness, retirement of `TwoLoopBounded`, rotation/translation; role `prover-max`). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).
17. T2027 — `docs/tickets/T2027.md` (PT-G, route H: properties 6, 7 by the path lemma, `Prop5to8`, old interface as theorems, registry update; role `prover-hard`). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).
18. T2028 — `docs/tickets/T2028.md` (S1-07, ST-1 pins: `Induction/Defs` from the T2015 probe, `Green/Pins` port, registry; role `prover-max`). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).
19. T2029 — `docs/tickets/T2029.md` (S1-10, `Green/EntryCore` (head of the ST-1 critical path); role `prover`). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).
20. T2034 — `docs/tickets/T2034.md` (EK-3, `(sum_res_1)` and `(sum_res_2_NAL)` for every `n`; role `prover-hard`; ahead of the queued ST-1 tickets because EK-3 → EK-4 is the longest serial chain of gate EK). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).
21. T2030 — `docs/tickets/T2030.md` (S1-01, `Gauss/FlowCalculus`; role `prover`). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).
22. T2032 — `docs/tickets/T2032.md` (S1-03, `Hierarchy/ContractionBasic`; role `prover`). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).
23. T2033 — `docs/tickets/T2033.md` (S1-09, `Induction/Split`; role `prover-hard`). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).
24. T2031 — `docs/tickets/T2031.md` (S1-12, `Green/LDEQuad`; role `prover`). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).
25. T2035 — `docs/tickets/T2035.md` (EK-5, `lem:sum_decay_nonzero` loss-free, both charges; role `prover`). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).

## Pre-release checks (the hub compiles in the same loop iteration; the dispatcher releases — CLAUDE.md §4 step 0, H4)
Compile each file with `lake env lean <file>` in the main worktree and append one `done:` line under this list per file: the exit code and the error lines, verbatim.
- `docs/tickets/checks/T2025-check.lean` (KL4+KL5; released conditionally above, DECISIONS §17).
  done: 2026-10-03 04:42 UTC — `lake env lean docs/tickets/checks/T2025-check.lean`: exit 0; no error lines. Waits for a free slot.
- `docs/tickets/checks/T2027-check.lean` (T2027; released conditionally above, DECISIONS §17).
  done: 2026-10-03 05:22 UTC — `lake env lean docs/tickets/checks/T2027-check.lean`: exit 0; no error lines. Starts now.
- `docs/tickets/checks/T2028-check.lean` (T2028; released conditionally above, DECISIONS §17).
  done: 2026-10-03 05:22 UTC — `lake env lean docs/tickets/checks/T2028-check.lean`: exit 0; no error lines. Starts now.
- `docs/tickets/checks/T2029-check.lean` (T2029; released conditionally above, DECISIONS §17).
  done: 2026-10-03 05:22 UTC — `lake env lean docs/tickets/checks/T2029-check.lean`: exit 0; no error lines. Starts now.
- `docs/tickets/checks/T2030-check.lean` (T2030; released conditionally above, DECISIONS §17).
  done: 2026-10-03 05:22 UTC — `lake env lean docs/tickets/checks/T2030-check.lean`: exit 0; no error lines. Waits for a free slot.
- `docs/tickets/checks/T2032-check.lean` (T2032; released conditionally above, DECISIONS §17).
  done: 2026-10-03 05:22 UTC — `lake env lean docs/tickets/checks/T2032-check.lean`: exit 0; no error lines. Waits for a free slot.
- `docs/tickets/checks/T2033-check.lean` (T2033; released conditionally above, DECISIONS §17).
  done: 2026-10-03 05:22 UTC — `lake env lean docs/tickets/checks/T2033-check.lean`: exit 0; no error lines. Waits for a free slot.
- `docs/tickets/checks/T2031-check.lean` (T2031; released conditionally above, DECISIONS §17).
  done: 2026-10-03 05:22 UTC — `lake env lean docs/tickets/checks/T2031-check.lean`: exit 0; no error lines. Waits for a free slot.
- `docs/tickets/checks/T2034-check.lean` (EK-3; released conditionally above, DECISIONS §17).
  done: 2026-10-03 05:32 UTC — `lake env lean docs/tickets/checks/T2034-check.lean`: exit 0; no error lines. Waits for a free slot.
- `docs/tickets/checks/T2035-check.lean` (EK-5; released conditionally above, DECISIONS §17).
  done: 2026-10-03 05:32 UTC — `lake env lean docs/tickets/checks/T2035-check.lean`: exit 0; no error lines. Waits for a free slot.

## Approved instructions
- H12 (dispatcher V1, 2026-10-03 01:19 UTC). Standing from now (DECISIONS §17): a Released ticket whose start condition names its Pre-release check starts in the same loop iteration in which you compile that check with exit 0, if a slot is free. Now: stage by name only and commit with message `Dispatcher V1: T2011–T2014 released, ticket T2015 (ST-D1), DECISIONS §17`: `docs/DECISIONS.md`, `docs/tickets/QUEUE.md`, `docs/tickets/T2015.md`, `docs/tickets/checks/T2015-check.lean`, `docs/claude-team/WORKLOG.md`, `docs/queue/CONTROL.md`, `docs/queue/CONTROL-archive.md`; then `git push origin main` (no force). One `done:` line with the hash.
  done: 2026-10-03 01:22 UTC — committed c950f27 (7 files staged by name), pushed to origin/main. T2015 check exit 0; T2015 waits for a free slot (4 of 4 in use by T2011, T2013, T2012, T2014).
- H22 (dispatcher V1, 2026-10-03 05:28 UTC). After compiling the T2034 and T2035 checks: stage by name only and commit with message `Dispatcher V1: CONTROL tidy, tickets T2034 (EK-3), T2035 (EK-5)`: `docs/queue/CONTROL.md`, `docs/queue/CONTROL-archive.md`, `docs/ROUTES.md`, `docs/tickets/QUEUE.md`, `docs/tickets/T2034.md`, `docs/tickets/T2035.md`, `docs/tickets/checks/T2034-check.lean`, `docs/tickets/checks/T2035-check.lean`, `docs/claude-team/WORKLOG.md`; push.
(H1–H11, H13–H21 archived in `docs/queue/CONTROL-archive.md`. Standing from H4: compile every file listed under Pre-release checks in the same loop iteration you see it.)

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
done: 2026-10-03 03:12 UTC — T2017 merged 33049c0 (RBM3D/Propagator/HeatTorus1D.lean, root import; lake build 3701 jobs, axiom audit 884 theorems / 0 axioms); audit PASS round 1; pushed.
done: 2026-10-03 03:20 UTC — T2014 merged fa2ebc7 (RBM3D/Loop/KLCut.lean, root import; lake build 3702 jobs, axiom audit 948 theorems / 0 axioms); audit PASS round 1 after Amend 1 restart (observation O1: 22 public KL helpers); pushed.
done: 2026-10-03 03:28 UTC — T2018 merged ddf5f74 (RBM3D/Path/Walk.lean, root import; lake build 3712 jobs, axiom audit 978 theorems / 0 axioms); audit PASS round 1; pushed.
done: 2026-10-03 04:01 UTC — T2019 merged cf8e79e (RBM3D/Propagator/HeatProduct.lean, root import; lake build 3715 jobs, axiom audit 985 theorems / 0 axioms); audit PASS round 1; pushed.
done: 2026-10-03 04:04 UTC — T2016 merged c154f29 (report only: state, prove, audit reports); audit PASS round 1 (after rule-(H) prover-max rerun); pushed.
done: 2026-10-03 04:19 UTC — T2021 merged 58bedae (RBM3D/Path/Markov.lean, Stop.lean, Azuma.lean, root imports; lake build 3722 jobs, axiom audit 1017 theorems / 0 axioms); audit PASS round 1; pushed.
done: 2026-10-03 04:23 UTC — T2020 merged e2aa5fe (RBM3D/Loop/KLTreeDeriv.lean, root import; lake build 3724 jobs, axiom audit 1027 theorems / 0 axioms); audit PASS round 1; pushed.
done: 2026-10-03 04:31 UTC — T2022 merged 5fb7729 (RBM3D/Evolution/Pins.lean, root import; lake build 3725 jobs, axiom audit 1032 theorems / 0 axioms); audit PASS round 1; pushed.
done: 2026-10-03 04:54 UTC — T2026 merged 3dc4f1c (RBM3D/Evolution/XiPins.lean, root import; lake build 3726 jobs, axiom audit 1037 theorems / 0 axioms); audit PASS round 1; pushed.
done: 2026-10-03 04:56 UTC — T2024 merged 1c434bb (RBM3D/Propagator/PropUnit.lean, root import; lake build 3727 jobs, axiom audit 1039 theorems / 0 axioms); audit PASS round 1; pushed.
done: 2026-10-03 04:57 UTC — T2023 merged f40d8ca (RBM3D/Propagator/Prop5Hold.lean, root import; lake build 3728 jobs, axiom audit 1041 theorems / 0 axioms); audit PASS round 1; pushed.
done: 2026-10-03 05:00 UTC — T2015 merged 5e7de62 (report only: state, prove, audit, portmap reports); audit PASS round 2 after one repair; pushed.

## Pending approval (information only — the hub must NOT act on these)
(none)
