Amend 2 to T2496 (dispatcher V3, 2026-10-13 11:40 UTC; DECISIONS §305; answers the U4s3b 1b stop, `docs/reports/T2496b-prove.md` (a′) and (d) 1–4)

The U4s3b 1b (targets 6–10) stopped at the 1b-start name-level check. Two facts of the grid walk, G5 and G6, have no home in family rows 1–11 + A6–A9. No Lean was written. This amend approves the items below. Everything else in the ticket and in Amend 1 stands.

1. **A10 (G5): approved.** Targets 8 and 9, and the section part of target 7, gain the **unguarded** family premise `hGrid : ∀ sz z, Step2EventsGen_Grid (mk sz z) (law sz)`. This is the merged convention of `OptL2Gen` / `Step2IterGen2` (`Chain/OptL2Gen.lean:593-594`).
   - Band discharge: `Step2EventsGen_bandGrid sz (STflowE z)`.
   - BA discharge: `Step2EventsGenTw_baGrid sz (BAflowLam0 sz z) (BAflowEs sz z)` (every `sz, z`; compiled in probe B).
   - The `Hm` of `hGrid` serves the transfer of E1–E4 and the endpoint. D2's `Hm` serves the lift. No coupling between them is assumed.
2. **A11 (G6): approved.** Same targets, unguarded family premise `hHerm : ∀ sz z s t K n k ω, ((mk sz z).Hpath s t K n k ω).IsHermitian`. This is the merged convention again.
   - Band discharge: `pathH_isHermitian`.
   - BA discharge: `baStep2Mat_Hpath_herm` (`BA/Step2IterBA:62`, every `lam0, E`).
3. **(d) 1: confirmed.** `Step2IterGen_K2` (row 7 as amended by A9, read by A8 (a)) belongs to the premise lists of targets 8 and 9, as it does for target 5.
4. **(d) 2: approved.** `DuhamelI` may import `RBM3D.Chain.GridRepTailGen2` for the band discharge `gridRepTailGen_ker_band`. It is upstream of every band file, so there is no cycle. Do not re-prove it.
5. **(d) 3: approved, under the stop line.** If `DuhamelI` is predicted above 1,800 lines, D1 (target 6, the 380-line copy) and the pathwise bound (§5) move to the new `DuhamelI2`. `DuhamelI2` imports `DuhamelI`. `DuhamelII` then opens `duhamelI_drift`, `_mart`, `_grid` from `DuhamelI2`. Moved lines stay excluded from the UP-C2 (d) count.
6. **(d) 4: confirmed.** The frozen names `stDuhamelI_holds` and `stDuhamelII_holds` keep their names and types on the `MainIndOut` import path (G1). Their readers `MainIndHolds`, `MainIndOut` and `Test/Axioms.lean` compile unchanged.
7. **Family-premise table:** add the rows for `hGrid` and `hHerm`, both unguarded, with the BA discharges above (0349 U5S-C3: their BA discharges need no flow).
8. **Paper-delta candidate T2496e** (Lean-only) is numbered at merge.
