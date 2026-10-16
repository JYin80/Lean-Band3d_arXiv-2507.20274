# T2519 Amend 5 (dispatcher V5, 2026-10-16 17:08 UTC; DECISIONS §364; supervisor 2026-10-16-1652 PASS) — release of row d: landing rules C5D-L1/L2, producer instance in the GUE-phase regime (C5D-C2)

Supervisor `docs/supervisor/2026-10-16-1652.md` answered REQ-2026-10-16-1547-C5bprime (row b′ above its line) with **PASS**: row d may start now. The overrun of b′ does not reach row d, which reads `gueGrid_twistBA` by name. A duplicate verdict, `withdrawn/2026-10-16-1654.md`, agrees and is not binding. Row d gets the ticket, Amends 1–4, and this Amend.

1. **Start.** Row d starts from `main` 98cb433d on `t/T2519d`, role `prover-max` (supervisor O1) → `auditor`. Its targets are 13–17 as in the ticket. Writable files are `BA/GUELLBA` and `BA/GUEHyp`, plus the reserve `BA/GUEHyp2`, which is used only once `GUEHyp` passes 1,500 (Amend 2 item 2).
2. **C5D-L1 (row line).** The line stays **2,386**, measured as landed `wc -l` over `GUELLBA`, `GUEHyp` and `GUEHyp2`, probe excluded.
   - The report gives the **instance section** of item 4 as a separate subtotal.
   - If row d lands in **(2,386, 2,640]** and its excess over 2,386 is at most that subtotal, **no REQ** is needed: the merge line records it, and N2's 1b may start.
   - Any other landing above 2,386 → short REQ before N2's 1b.
3. **C5D-L2 (total line, last row).** **12,000** is the absolute cap; 12,000 − 9,360 = **2,640** is left for row d. Row d above 2,640 → short REQ before N2's 1b, whatever the reason.
4. **C5D-C2 (producer instance: non-degenerate data; necessary).**
   - **Why `zSeq` fails.** At `zSeq`, `BAflowT0 ≤ 5/6` for every `n` (row c audit §7). Then `RBG_Prod`'s `∀ n` premise `t₁ ≤ fT` and its premise `∀ᶠ n, L^d (1 − t₁) ≤ λ²` contradict each other, so the instance would be vacuous: the defect class of b′ round 1.
   - **Use data in the GUE-phase regime:**
     - a bulk energy `E_*` as in `BA/MAPins:205-224`;
     - `Im z_n = η_n := c · λ_n² / (2 L_n³)`, with `c = (πκ)^5/2048` the explicit constant of `ba_flowG`;
     - `t₁ := fT − N^{-τD} · √fT · η_n`.
   - **What this data gives.** By `ba_flowG`: `Ed κ'`, `cT ≤ fT < 1` and `1 − fT ≤ λ²/(2L³)` at every `n`. Hence `0 ≤ t₁ ≤ fT` and `L³(1 − t₁) ≤ λ²` (and `≤ 1`) at every `n`. The relation `fT − t₁ ≤ N^{-τD} √fT Im z` holds with equality. `(N √fT η)⁻¹ ≤ N^{-τD}` holds eventually: from `n = 13` at `τD = 1/20` (supervisor's arithmetic, `√fT ≥ 1/2`).
   - **`MO` (`BAMO`).** It may stay an open premise, as in row c. Or it may be discharged by `unMLOutBA_three` + `ba_domG`, which needs `N^{-1+ε} ≤ η_n` at every `n` (a larger `η_n` at small `n`). The row chooses.
   - **Optional.** Drop `hKb` from b′'s `twist_sz0` (b′ audit observation 2, compiled `audit_hKb`). This is done only by a primed instance in row d's own files (`GUETwistBA2` is not writable), and it counts in the item 2 subtotal.
   - **Row c's instance note** (§362 (2)): its `hLK`/`hLoc` at `zSeq` are type-shaped only. Row d's producer instance uses the data above, not `zSeq`.
5. **Stop rule (add).** If the instance needs a lemma beyond the merged `ba_flowG`/`ba_domG`, the bulk-energy instance and `Sizes` arithmetic (for example new estimates of `BAm` at small `η`), stop and write it to `docs/queue/T2519d.state`. Do not build it inside the row.
6. **Report (supervisor O3).** Besides the ticket's items, the report gives:
   - the item 2 subtotal;
   - the instance data (`E_*`, `η_n`, `t₁`, `τD`), with the `n` from which each eventual premise holds;
   - the per-file check against 2,000 on a landed forecast (Amend 2 item 8).
7. **Lesson (instance regime; supervisor 1652).** Wherever a premise contains `hell` (`L^d (1 − t₁) ≤ λ²`), the data must sit in the GUE phase: `1 − t₁ ≲ λ²/L^d`, hence `Im z ≲ c λ²/L^d` at the flow point. A second RETURN of this defect class is a REQ trigger (TEAM §6). The withdrawn duplicate reads T2515 row b's degenerate-point RETURNs as the same class (then already twice). The preventive measure is the same either way: item 4 here.
