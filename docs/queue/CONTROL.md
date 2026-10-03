# CONTROL — written only by the dispatcher (Cowork). The hub may only append `done:` lines under Approved instructions.

mode: RUN
parallel: 4
updated: 2026-10-03 13:54 UTC (dispatcher V1: T2055 (S3-04) merged; T2059 (S3-05) released; H39)
reason: RUN (Jun, DECISIONS §8). Scope and rules: DECISIONS §3–§7.

The standing hub rules are in CLAUDE.md §3 (auto-merge, one automatic repair per RETURN, date -u, report headers, private helpers, nothing undecided starts, parallelism, API errors).

## Released tickets (only those not yet merged)
Priority order (CLAUDE.md §3 (G)); at most `parallel` workflows at once.
17. T2039 — `docs/tickets/T2039.md` (ST-D2, design of Step 2 and the path layer, `d ≥ 3` argument; role `prover-max`, report only). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).
18. T2050 — `docs/tickets/T2050.md` (LW-03, graph vocabulary `Graph/LWVocab`; role `prover-hard`; first LW ticket). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).
19. T2054 — `docs/tickets/T2054.md` (S3-02, contraction inequality `STContract`, new at d ≥ 3; role `prover-hard`). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).
20. T2057 — `docs/tickets/T2057.md` (S1-16, `Green/EntryDom`: block-average error and `(GavLGEX)`; role `prover-hard`; ST-1 critical path). Start: when the `done:` line of its Pre-release check below says exit 0, **T2045 (S1-08) is merged** (done: 5d1e6b1), and a slot is free.
21. T2056 — `docs/tickets/T2056.md` (KL7c, port `Loop/SumZeroWard`: `Q(σ_alt, ∅)|_{t=1} = 0` and the signed sum-zero bound; role `prover-max`; KL chain). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).
22. T2053 — `docs/tickets/T2053.md` (EK-6, the `STEK*` consumer pins from the merged `EK*` pins; role `prover-hard`). Start: when the `done:` line of its Pre-release check below says exit 0, **T2035 (EK-5) is merged** (done: c163ca8), and a slot is free.
23. T2058 — `docs/tickets/T2058.md` (S3-23, deterministic scale facts of Steps 3–4: `hscale`/`k_min`, `hBA`, window, regime split; role `prover-hard`). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).
24. T2059 — `docs/tickets/T2059.md` (S3-05, `lem_+Q`: `STQopNorm` and the decay clause; role `prover`). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).
25. T2047 — `docs/tickets/T2047.md` (S1-33, `Induction/ContinuityNet` (first part of `Continuity`); role `prover-hard`). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).
26. T2052 — `docs/tickets/T2052.md` (S1-14, `Green/LDEQuadT`; role `prover`). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).
27. T2033 — `docs/tickets/T2033.md` (S1-09, `Induction/Split`; role `prover-hard`). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).
28. T2037 — `docs/tickets/T2037.md` (S1-02, `Gauss/LoopCoordinate`; role `prover`). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).
29. T2051 — `docs/tickets/T2051.md` (LW-15, deterministic `Ψ_t` facts `Graph/LWPsi`; role `prover`). Start: when the `done:` line of its Pre-release check below says exit 0 and a slot is free (DECISIONS §17).

## Pre-release checks (the hub compiles in the same loop iteration; the dispatcher releases — CLAUDE.md §4 step 0, H4)
Compile each file with `lake env lean <file>` in the main worktree and append one `done:` line under this list per file: the exit code and the error lines, verbatim.
- `docs/tickets/checks/T2033-check.lean` (T2033; released conditionally above, DECISIONS §17).
  done: 2026-10-03 05:22 UTC — `lake env lean docs/tickets/checks/T2033-check.lean`: exit 0; no error lines. Waits for a free slot.
- `docs/tickets/checks/T2037-check.lean` (S1-02; released conditionally above, DECISIONS §17).
  done: 2026-10-03 06:00 UTC — `lake env lean docs/tickets/checks/T2037-check.lean`: exit 0; no error lines. Waits for a free slot.
- `docs/tickets/checks/T2047-check.lean` (S1-33; released conditionally above, DECISIONS §17).
  done: 2026-10-03 08:22 UTC — `lake env lean docs/tickets/checks/T2047-check.lean`: exit 0; no error lines. Waits for a free slot.
- `docs/tickets/checks/T2051-check.lean` (LW-15; released conditionally above, DECISIONS §17).
  done: 2026-10-03 10:37 UTC — `lake env lean docs/tickets/checks/T2051-check.lean`: exit 0; no error lines. Waits for a free slot.
- `docs/tickets/checks/T2052-check.lean` (S1-14; released conditionally above, DECISIONS §17).
  done: 2026-10-03 10:52 UTC — `lake env lean docs/tickets/checks/T2052-check.lean`: exit 0; no error lines. Waits for a free slot.
- `docs/tickets/checks/T2053-check.lean` (EK-6; released conditionally above; starts after T2035 merges).
  done: 2026-10-03 12:52 UTC — `lake env lean docs/tickets/checks/T2053-check.lean`: exit 0; no error lines.
- `docs/tickets/checks/T2056-check.lean` (KL7c; released conditionally above, DECISIONS §17).
  done: 2026-10-03 13:12 UTC — `lake env lean docs/tickets/checks/T2056-check.lean`: exit 0; no error lines. Waits for a free slot.
- `docs/tickets/checks/T2058-check.lean` (S3-23; released conditionally above, DECISIONS §17).
  done: 2026-10-03 13:32 UTC — `lake env lean docs/tickets/checks/T2058-check.lean`: exit 0; no error lines. Waits for a free slot.
- `docs/tickets/checks/T2059-check.lean` (S3-05; released conditionally above, DECISIONS §17).
  done: 2026-10-03 14:02 UTC — `lake env lean docs/tickets/checks/T2059-check.lean`: exit 0; no error lines. Waits for a free slot.

## Approved instructions
- H12 (dispatcher V1, 2026-10-03 01:19 UTC). Standing from now (DECISIONS §17): a Released ticket whose start condition names its Pre-release check starts in the same loop iteration in which you compile that check with exit 0, if a slot is free. Now: stage by name only and commit with message `Dispatcher V1: T2011–T2014 released, ticket T2015 (ST-D1), DECISIONS §17`: `docs/DECISIONS.md`, `docs/tickets/QUEUE.md`, `docs/tickets/T2015.md`, `docs/tickets/checks/T2015-check.lean`, `docs/claude-team/WORKLOG.md`, `docs/queue/CONTROL.md`, `docs/queue/CONTROL-archive.md`; then `git push origin main` (no force). One `done:` line with the hash.
  done: 2026-10-03 01:22 UTC — committed c950f27 (7 files staged by name), pushed to origin/main. T2015 check exit 0; T2015 waits for a free slot (4 of 4 in use by T2011, T2013, T2012, T2014).
- H39 (dispatcher V1, 2026-10-03 13:54 UTC). Compile the T2059 check (Pre-release list), then stage by name only and commit with message `Dispatcher V1: T2055 merged bookkeeping, paper-deltas D48–D56 (T2041a–i), ticket T2059 (S3-05)`: `docs/paper-deltas.md`, `docs/ROUTES.md`, `docs/rework-ledger.md`, `docs/tickets/QUEUE.md`, `docs/tickets/T2059.md`, `docs/tickets/checks/T2059-check.lean`, `docs/claude-team/WORKLOG.md`, `docs/queue/CONTROL.md`, `docs/queue/CONTROL-archive.md`; push. One `done:` line.
(H1–H11, H13–H38 archived in `docs/queue/CONTROL-archive.md`. Standing from H4: compile every file listed under Pre-release checks in the same loop iteration you see it. Standing from H23 (DECISIONS §20): (b) when two branches both append lines to the registry lists of `RBM3D/Test/Axioms.lean`, keep both sides (union), then run the full build; (c) a merge that stops at step 5 only on unregistered premises gets state `blocked` with the names, and if the ticket has an Amend 1 of DECISIONS §20 you run its `repairer` stage for the registry lines and a round-2 `auditor` of that diff at once. Standing from H28: every workflow keeps its scratch files in its own subdirectory `scratchpad/<ticket>/` (T2036 report (d): concurrent workflows overwrote each other's generic file names).)

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
done: 2026-10-03 05:38 UTC — T2025 merged c8bedf7 (RBM3D/Loop/KLUnique.lean, root import; lake build 3729 jobs, axiom audit 1058 theorems / 0 axioms); audit PASS round 1; pushed.
done: 2026-10-03 05:46 UTC — T2027 merged 6cc5032 (RBM3D/Propagator/Prop6Hold.lean, RBM3D/Test/Axioms.lean, root import; lake build 3730 jobs, axiom audit 1065 theorems / 0 axioms); audit PASS round 1; pushed.
done: 2026-10-03 05:52 UTC — T2029 merged 890a89f (RBM3D/Green/EntryCore.lean, RBM3D/Test/Axioms.lean Amend 1 lines applied onto main (H23 b), root import; lake build 3731 jobs, axiom audit 1110 theorems / 0 axioms); audit PASS rounds 1 and 2; pushed.
done: 2026-10-03 05:53 UTC — T2030 merged 6f99812 (RBM3D/Gauss/FlowCalculus.lean, root import; lake build 3734 jobs, axiom audit 1166 theorems / 0 axioms); audit PASS round 1; pushed.
done: 2026-10-03 06:00 UTC — T2032 merged e318c24 (RBM3D/Hierarchy/ContractionBasic.lean, root import; lake build 3735 jobs, axiom audit 1196 theorems / 0 axioms); audit PASS round 1; pushed.
done: 2026-10-03 06:18 UTC — T2034 merged 1678ea4 (RBM3D/Evolution/SumDecay.lean, RBM3D/Test/Axioms.lean Amend-1 line applied onto main (H23 b), root import; lake build 3736 jobs, axiom audit 1206 theorems / 0 axioms); audit PASS round 1; pushed.
done: 2026-10-03 06:29 UTC — T2038 merged cace419 (RBM3D/Green/RowIndep.lean, RBM3D/Test/Axioms.lean union-merged with EKFastDecay (H23 b), root import; lake build 3737 jobs, axiom audit 1265 theorems / 0 axioms); audit PASS round 1; pushed.
done: 2026-10-03 06:32 UTC — T2036 merged 85ab436 (RBM3D/Loop/KLWard.lean, root import; lake build 3738 jobs, axiom audit 1273 theorems / 0 axioms); audit PASS round 1; pushed.
done: 2026-10-03 06:33 UTC — T2031 merged cca94be (RBM3D/Green/LDEQuad.lean, RBM3D/Test/Axioms.lean union-merged (H23 b), root import; lake build 3739 jobs, axiom audit 1345 theorems / 0 axioms); audit PASS round 1; pushed.
done: 2026-10-03 08:03 UTC — T2028 merged 64bdfd3 (RBM3D/Induction/Defs.lean, RBM3D/Green/Pins.lean, RBM3D/Test/Axioms.lean union-merged (H23 b), root imports; lake build 3741 jobs, axiom audit 1441 theorems / 0 axioms); audit PASS round 2 after one repair; pushed.
done: 2026-10-03 09:02 UTC — T2043 merged cb7d4ba (RBM3D/Loop/KLSumZero.lean, root import; lake build 3742 jobs, axiom audit 1476 theorems / 0 axioms); audit PASS + sign-off (H30); pushed.
done: 2026-10-03 09:45 UTC — T2042 merged d9de66f (RBM3D/Evolution/Pins.lean Amend-1 edits, RBM3D/Evolution/SumDecayZero.lean, root import; lake build 3743 jobs, axiom audit 1477 theorems / 0 axioms); audit PASS round 1 after Amend 1 restart; pushed.
done: 2026-10-03 10:21 UTC — T2041 merged 3747ff7 (report only: state, prove, audit, portmap reports); audit PASS round 2 after one repair; pushed.
done: 2026-10-03 10:23 UTC — T2040 merged 45e2630 (report only: state, prove, audit, inventory reports); audit PASS round 2 after one repair; pushed.
done: 2026-10-03 10:24 UTC — T2046 merged ea63565 (RBM3D/Green/Stability.lean, root import; lake build 3744 jobs, axiom audit 1484 theorems / 0 axioms); audit PASS round 1; pushed.
done: 2026-10-03 10:36 UTC — T2044 merged 84e54a8 (RBM3D/Green/LDEQuadMom.lean, root import; lake build 3745 jobs, axiom audit 1517 theorems / 0 axioms); audit PASS round 1; pushed.
done: 2026-10-03 10:57 UTC — T2049 merged 56c30fb (RBM3D/Induction/Step34Pins.lean, RBM3D/Test/Axioms.lean (registry lines applied onto main, H23 b), root import; lake build 3746 jobs, axiom audit 1563 theorems / 0 axioms); audit PASS round 2 after one repair; pushed.
done: 2026-10-03 12:55 UTC — T2048 merged 057edb0 (RBM3D/Loop/KLSumAll.lean, root import; lake build 3747 jobs, axiom audit 1569 theorems / 0 axioms); audit PASS round 1 (rerun after usage limit); pushed.
done: 2026-10-03 13:08 UTC — T2035 merged c163ca8 (RBM3D/Evolution/Nonzero.lean, root import; lake build 3748 jobs, axiom audit 1570 theorems / 0 axioms); audit PASS round 1; pushed.
done: 2026-10-03 13:08 UTC — T2045 merged 5d1e6b1 (RBM3D/Induction/ScaleFacts.lean, RBM3D/Induction/PerTimeCalc.lean, root imports; lake build 3750 jobs, axiom audit 1653 theorems / 0 axioms); audit PASS + sign-off (H36); pushed.
done: 2026-10-03 13:44 UTC — T2055 merged 6b2494e (RBM3D/Induction/QopAlgebra.lean, root import; lake build 3751 jobs, axiom audit 1675 theorems / 0 axioms); audit PASS round 2 after one repair; pushed.

## Pending approval (information only — the hub must NOT act on these)
(none)
