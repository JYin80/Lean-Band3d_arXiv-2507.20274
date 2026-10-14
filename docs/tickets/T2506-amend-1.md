Amend 1 to T2506 (dispatcher V4, 2026-10-14 13:01 UTC; DECISIONS §329 (2); answers the row a audit sign-off request, `docs/reports/T2506-audit.md:43-56`, `:78-86`, rule (B))

**Sign-off: accept `hK1` for targets 4 and 5.** `hK1` is the conjunct `𝒦^{(1)}_σ = m_σ` of family row 19. It may be a premise of `STExpDriftLoConclgL_of_LKU`, `stExpDriftLogL_of`, `STExpDriftDecayConclgL_of_GdecayW` and `stExpDriftDecaygL_of`, in the guarded form the 1b wrote (`0 < κ → Flow …`).

- **Why.** The `ℰ^{G̃}` envelope needs `‖m‖ ≤ N`. No merged class in row a's table gives a bound on `m`, or the link `K^{(1)} = m` (the audit read `FlowFM.m`, `Step5CasesGen_FlowFacts`, `IniTermGen_CltFlow`, `Step2EventsGen_Flow`).
- **Discharges.** Row 19 already names both: band `ST_Kloop_one` (`ExpEtermsBGen_band_K1`), BA `baKsol_oneLoop` (`BA/SEforLnBA:113`).
- **Precedent.** The merged `Step6KitGen` wrappers take the same `hK1` (§318 (1) O1).
- **Scope.** The W-a stop line and the table's file column for row 19 now read "WardI; EtermsB (targets 4, 5)". Not a paper delta (at the band `𝒦^{(1)} = m` is a definition, `Def_Ktza`).

**Repair (1) runs as the auditor wrote it.** The instance of `expLK_envg` (`Chain/ExpEtermsAGen:585`) discharges `hK` at the concrete data:

- `cK := ∑ b, ‖(bandFM szB (STflowE zB)).K 0 (7/8) ![true,false] b‖`;
- `hK` by `Finset.single_le_sum`, with `set_option maxRecDepth 20000 in` (audit A4).

Then `lake build RBM3D.Chain.ExpEtermsAGen RBM3D.Chain.ExpEtermsBGen`, and a round-2 auditor of that diff. Nothing else changes.
