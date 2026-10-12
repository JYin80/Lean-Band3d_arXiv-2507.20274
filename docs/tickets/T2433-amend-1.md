Amend 1 to T2433 (dispatcher V3, Mon Oct 12 05:59 UTC 2026; DECISIONS §251; supervisor `docs/supervisor/2026-10-12-0554.md` (REQ-0451-L4S3: **scoped HOLD** on the S3 block of stage L, finding L4S3-F1; O1–O3; Q2 "L4e-C keeps the generic half"); answers the open point of the 1a-audit RETURN "file 2 would break the 2,000 stop line").

**1. Scope: the generic half only.** This row now delivers, for any root list:
- `BACtx`;
- the GG-with-context Lemma, for both charges, with its `kids` form;
- `BAselStar`, widened to any `BACtx` candidate if L4S3-L1 (item 2) needs candidates off `S*`;
- `BAG5LeafProps` and `BAG5Attached`.

**Dropped** (no named consumer; supervisor 0554 O1): the concrete closure table over `baG5Graph` (128 root terms, the relabelling lemma, `decide` over the kids) and target 4 (`BAG5Expand'` with `BAG5Identity` at `baG5Graph`). `BAG5Tgt`, `BAG5Leaf`, `BAG5Expand` stay as pins (statements) if the generic half needs them; no theorem about `baG5Graph` is proved here.

**2. The lift run L4S3-L1 (supervisor 0554, §"HOLD scope and lift"), inside this ticket's scratch step.** Run it in the current route-measurement scratch step (`prover-max`, scratch only, nothing merged); if that step has already ended, as a separate `prover-max` scratch step before the 1a-audit round 2. Paste the output into `docs/reports/T2433-prove.md` as section (a⁗) "L4S3-L1".
- **(a) Roots** as `BAGraph` data with `mdot`: `T3C-tr_k` (`k = 0, 1`), `D1X`, `D2X` (vertex data: `docs/reports/T2434-prove.md` (iii)). Check them against `BAGGGammaR` (`Graph/BAGGExp.lean:72-77`) and `BAlanlwR` (`Graph/BAExpand.lean:106`). Check them numerically against T2434's Monte Carlo `mc_cut.py` (branch `t/T2434`, scratch `T2434/`): the four S3 integrands equal the root values sample by sample.
- **(b) Closure** over all partition terms, both tail charges, `x ≁ y` and `x ~ y`, with the engine mirroring the merged definitions (`baSplitSolid`, `gg2`/`gg4` with `owxDE`, `BAExpandId_gg2r`/`gg4r`, `atom`, `mol`, `nA`, `nM`); the selector may take any `BACtx` candidate. Report per root: parents, depth, leaves, minimal margin, stuck nodes (below target with no `BACtx` candidate); check the leaf properties `Normal`, `n_M ≤ 1`, `2 ≤ n_W`, attachment, `BAG5Tgt`. Sample randomly beyond depth 2 if the tree is large.
- **Outcome rule:** 0 stuck nodes and every leaf property holds → say so in the first line of (a⁗); the dispatcher lifts the HOLD and writes L4d2. Some node stuck → stop before 1b and paste the stuck graphs; the dispatcher writes the short REQ.

**3. Process:** current scratch step (with item 2) → 1a-audit round 2 (judges the generic half; the file-2 stop-line point is answered by the scope cut) → 1b `prover-max` on the generic half → auditor. Files, stop line 2,000 per file, unchanged; `BAG5Leaf2` may stay unused.
