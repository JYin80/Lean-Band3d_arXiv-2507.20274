Amend 1 to T2523 (dispatcher V5, 2026-10-17 05:05 UTC; DECISIONS §376; audit round 1 `docs/reports/T2523-audit.md` D2 sign-off, D1 repair)

**Sign-off D2 (a): the 110 scan-kept declarations (R2) stay for now.** The 42 premise-prover theorems and their 68 helpers (1,094 lines) are kept and listed as tool roots (`scanProvers`), because the full build's premise scan needs them. No registry class is assigned to the 42 `Prop`s in this ticket. Reason: after stage BA-D's assembly merges, the public axiom audit (DECISIONS §371 (5), supervisor 2346 BAD-C5) replaces the registry and the premise scan by the plain three-axiom check; the final DeadDecls rerun after that deletes these declarations together with the `scanProvers` root list. Classifying the 42 `Prop`s now would be removed again then.

**Sign-off D2 (b): the insertion limit applies to `RBM3D/` (and `RBM3D.lean`) only.** The tool file's root lists (`restoredRoots`, `scanProvers`) and its report code are not counted. Under `RBM3D/` the default diff has 291 insertions ≤ 300: accepted.

**D1: one rule-(B) repair, as the audit requires** (audit D1 items 1–3):
1. Delete `MinorDiffInst.sqrt_four`, `mE_zero`, `toyPow`, `toyHalf` (`Green/MinorDiff.lean:937-958`, with the namespace / `noncomputable section` if left empty) and `BALocReg1B_extMap` (`Graph/BALocReg1B.lean:332-336`, with section `RelabelOps` and its `variable` line if left empty); remove the five from `restoredRoots`.
2. Give each remaining `restoredRoots` name a per-name reason in the report (use site `file:line`, or the build error when it is deleted); for the three zero-reference `@[simp]` lemmas (`GreenMinor_a_zero`, `wordDirectionMap_nil`, `badTower_zero`) show the failing proof, or delete them if nothing fails.
3. Full `lake build`, tool rerun (0 unreached), check file, axioms; update the counts in the report.
Then audit round 2.

**Observation O1** (`baThm27L_any` has no compiled instance after the deletion): no action here. After BA-D, `baThm27L_all` applies `baThm27L_any` at every `d ≥ 3` (T2534), and its `d = 3`, `d = 4` instances exercise it.
