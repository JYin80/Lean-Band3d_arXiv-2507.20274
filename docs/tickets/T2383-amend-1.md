# T2383 Amend 1 (dispatcher V2, Sat Oct 10 12:15 UTC 2026; DECISIONS §196; answers the question in `docs/queue/T2383.state`; 1a report `docs/reports/T2383-prove.md` verdict table)

- **Situation:** the 1a passed targets 1 and 3–6; the tripwire did not fire (`g` = 0.239, `f_sem` = 0). It blocked on target 2: the generic `HierarchyN` reads objects defined outside the two sole files, namely
  - `STKloop` (via `KLK`), `STLKIM`, `STksimLKM`, `STelklkM`, `STegtM` (`Induction/Step2Defs.lean`);
  - `STllPairN` (`Induction/HierAlgebra.lean`);
  - and its proof uses `loopDrift_sub_K_deriv_n` (HierAlgebra, T5s2).
- **Decision: (A).** `Induction/HierarchyN.lean` stays band-only and unchanged in this ticket (0 edit lines). Its generic restatement goes to **T5s2**, together with `HierAlgebra`, after T8 (the generic `Step2Defs` vocabulary, additive per L1). Its G1 checks hold trivially here.
- **BA instance (target 4): moved out of this ticket.** Importing `BA/FlowPins` into the chain file `Induction/LoopGenN.lean` would put the BA layer upstream of the chain and widen every later rebuild cone. Instead:
  - the generic theorem gets a **nonvacuous non-band instance** at a concrete `m` with `0 < m.im` (e.g. `m = Complex.I`, or the band `m` at a shifted `E`), with no `BA/*` import;
  - the BA instance (probe 385-388) goes to the BA-side row **T5-BA**.
- **Sole writable files:** `RBM3D/Induction/LoopGenN.lean` only. Plus `RBM3D/Test/Axioms.lean` only if a new owed line is needed; none is expected.
- **Unchanged:** targets 1, 3, 5, 6 as in the ticket; the stop line 800; the tripwire rule.
- **Auditor:** checks that `HierarchyN.lean` is untouched, that `LoopGenN.lean` imports no `BA/*` file, and that the non-band instance is nonvacuous.
