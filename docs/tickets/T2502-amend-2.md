Amend 2 to T2502 (dispatcher V4, 2026-10-14 09:51 UTC; DECISIONS §324 (1); answers the row c audit sign-off request, `docs/reports/T2502c-audit.md:54-64`, `:126`, rule (B))

**Sign-off: accept `hFF`.** The binding shapes of targets 16a, 16b (Amend 1 check `T2502_Target16a`, `T2502_Target16b`) carry one more family premise, before the others:

- 16a: `Step5CasesGen_FlowFacts d Flow mk T0 → T2502_Target16a d law Flow mk T0`.
- 16b: `Step5CasesGen_FlowFacts d Flow mk T0 → T2502_Target16b d law Flow mk T0`.

These are the shapes the auditor compiled (`Audit.lean:138-139`). Why:

- This is family table row 3 (`T2502.md:49`), which already lists targets 15 and 16. Amend 1 item 2 changed rows 9, 14 and 15 only. Its shapes left row 3 out by oversight.
- It has both discharges: band `step5CasesGen_flowFacts_band`, BA `baStep5CasesGen_flowFacts` (merged).
- The merged row-a wrappers take it the same way (`Step6KitGen:677, 716, 747, 795`).
- The proof needs it: `SizeTendsto`, `T0 < 1` and `κm ≤ Im m`, which `ExpAvgGen_W1fam` does not supply.
- It is not a paper delta: it is part of the setting of `lem:main_ind` (`6:12-21`).

Nothing else changes. Row c merges on its round-1 audit (PASS per target).
