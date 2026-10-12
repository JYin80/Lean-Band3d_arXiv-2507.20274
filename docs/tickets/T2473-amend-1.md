Amend 1 to T2473 (dispatcher V3, Mon Oct 12 23:28 UTC 2026; DECISIONS §281; answer to the 1a-audit RETURN of 23:18 UTC (H183 (3)): stop lines S1, S2 and the substitution S3)

**Decisions (binding).**
1. **S1 (split / third row): three rows.** The 1a-audit's D3 gives own central 4,029 > 3,900 and T4s2b = 2,643 > 1,950. The row splits at the file boundaries into
   - **T4s2a** = `Chain/GridGoodGen` + `Chain/GridEnvelopeGen` (targets 1–5, central ≈ 1,386): **its 1b starts now**;
   - **T4s2b** = `Chain/GridAssemblyGen` (target 7, the assembly; target 6 was dropped by the dispatcher answers; ≈ 1,211), on a branch stacked on `t/T2473` after T4s2a's audit PASS, merged after T4s2a;
   - **T4s2c** = `Chain/AzumaProxyGen` (targets 8–10; ≈ 1,432; reserve `AzumaProxyGen2` only if a file is predicted above 1,800 lines), stacked after T4s2b, merged after it.
   The third row is reported to the supervisor in a short notice REQ (`REQ-2026-10-12-2328-T4s2`); it is non-blocking.
2. **S2 (premise `∀ n, (Cm.m n).im ≤ 1`): admitted** as an inline premise of target 5 (`SumWeightedStepErrNg_Stmt` and the envelope), next to `0 < Cm.eta n v ∧ Cm.eta n v ≤ 1 - v` (the `hη` of the merged `exists_norm_KI_le_wing`). Band discharge: `hierDriftGen_band_eta` / `|E n| ≤ 2 − κ`; BA discharge owed by T4-BA (`BAm_norm_le_one`, with its side conditions). No named `Prop`, no registry line. The E′ reduction of the port stays.
3. **S3 (target 4 (a)/(b)): approved.** In place of W, KCompat and the measurability compat, target 4 takes the merged `StepDecompGen_LoopForm Cm E` (T2474) and the merged `Step2EventsGen_Law Cm μ Hf` (T2467, the last conjunct of F9): both are merged single texts (X1-C4). This supersedes dispatcher answer (4) of the ticket on this point (W is T2474's class, read here through `LoopForm`; F9's `Law` conjunct is read by name). Band discharges and BA sources as in the probe (`baStep2Mat_loopForm` up to `0 < Im m`; `Step2EventsGenTw_baLaw`).
4. The BA initial membership stays an owed T4-BA item (answer (5)); recorded, no RETURN.
5. The 1a adds an (a‴) section with these answers (the D3 table per row, the target-5 premise list); then the 1b of T4s2a starts.

Sole writable files: unchanged; under the three-row split, T4s2a keeps `GridGoodGen` and `GridEnvelopeGen`, T4s2b `GridAssemblyGen`, T4s2c `AzumaProxyGen` (and its reserve).
