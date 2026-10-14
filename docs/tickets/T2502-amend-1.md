Amend 1 to T2502 (dispatcher V4, 2026-10-14 08:12 UTC; DECISIONS §319 (1); answers the row c W1 gate: probe `RBM3D/Probe/T2502Pins.lean` on `t/T2502c` 0f0ad532, 1a-audit `docs/reports/T2502c-1a-audit.md`, verdict BLOCKED for sign-off, H183 (3))

**Sign-off: (A), per-time form.** Row c stays generic. The Stein remainder at a non-scalar `M` is controlled by two new premises, W1 (iii) and W1 (iv). Binding texts: `docs/tickets/checks/T2502-amend-1-check.lean` (probe `T2502c_*` → `T2502_*`). They supersede the drafts `T2502-check.lean:330-342`.
- Why not (B): it puts `M = m • 1` into a generic statement (C1, ticket `:70`). It would also make V1-BA repeat row c's Stein argument at the BA tuple.
- Why (A) is allowed: each new premise has a named BA discharge and an owner. This lifts the stop line "a family premise without a named BA discharge or owner" (`:75`) for W1 (iii), W1 (iv) and row 15.
  - (iii): from TL1 `BATwistAvgLaw` (`BA/TwistPins:91`; registry `Test/Axioms:192`; at each time V2a supplies it by `TwistStep2_tl1`, T2503 design `:143`) through `TwistPins_circ_term` (`BA/TwistPins:439`).
  - (iv): from `CltFlowBA_MB_decay` (`BA/CltFlowBA:221`, constants at `(κ, 𝔡)`), summed over `q`.
  - Owner of both bridges: **V1-BA**. V1-BA already reads TL1 at each time in Step 6 (T2503 design `:143`).
- Why per time: at BA, TL1 is a premise at each time `u` (V1-BA's `BAStep6R`), not a fact for every `u` along every flow. So (iii) enters the core beside `LWAvgLawgL u` and `STLKgL u`. The merged row-a pin `STImproveExpAvergL` (`Chain/Step6Gen:316`, premises `LWAvgLawgL`, `STLKgL` only) is then proved only for carriers whose (iii) follows from `LWAvgLawgL` (row 15, band type).

**Changes to the ticket.**
1. **Target 16 splits into three.**
   - **16a** `stImproveCoregL_of`: the shape `T2502_Target16a`, i.e. family rows 9 + 14 (with (iv)) → the per-time core `STImproveCoregL` (= `T2502_ImproveCoregL`). This is the row's main proof. The remainder route follows the 1a: `|R_a| ≤ u Σ_q |M^{(B)}_{aq}| Σ_p S_{qp} 𝔼|g_p - m||t_{aq} - M^{(++)}_{aq}|`, closed by (iii), (iv) and the moments of `LWAvgLawgL`.
   - **16b** `stImproveExpAvergL_of`: the shape `T2502_Target16b`, proved from 16a and row 15.
   - **16c** `stExpAvgUgL_of_core`: a per-flow variant of `st6_expAvgU_of_ping` (`Chain/Step6KitGen:338`). It concludes `STExpAvgUgL` on `[s,t]` from 16a at that flow plus `∀ u ∈ [s,t]`, W1 (iii), in place of the global `hAvg`. This is the hook V1-BA feeds from TL1. The 1b fixes its shape; report (3) gives the statement.
   - Band instances:
     - rows 9 + 14 with (iv) at the band tuple (probe `T2502c_band_W1fam` `:121`, `CM = 1`);
     - row 15 at the band tuple (probe `T2502c_band_collapse` `:153`);
     - band `stImproveExpAver_holds` (`ExpAvg:879`) re-derived through 16b.
2. **Family-premise table.**
   - Row c (targets 14–16): rows 9 and 14 merge into one row, `T2502_W1fam`. Its guard: `∃ Cs CM` after `(κ, ε, 𝔡)` and before `(𝔠, sz, z)`, one witness `(H₀, g', E)` per flow. Its BA discharge: probe `T2502c_ba_W1fam` (`:227-262`) plus (iv), owner V1-BA.
   - Row b keeps row 9 as written (targets 10–13).
   - **New row 15** `T2502_W1iiiOfLW`: guarded; band discharge as in item 1; no BA discharge by design (BA goes through 16a); target 16b only.
   - (iii) is not a family row. It is a per-time premise of 16a, like `LWAvgLawgL`.
3. **Public defs.** The stop line "a public def outside `Chain/Step6Gen`" is lifted for row c's W1 vocabulary only, because `Step6Gen` is merged and V1-BA must name these. Allowed in `Chain/ExpAvgGen`:
   - `ExpAvgGen_W1i`, `ExpAvgGen_W1ii`, `ExpAvgGen_tM`, `ExpAvgGen_MB`;
   - `ExpAvgGen_W1iii`, `ExpAvgGen_W1iv`, `ExpAvgGen_W1fam`, `ExpAvgGen_W1iiiOfLW`;
   - `STImproveCoregL`.

   Each must equal its check text after the name map (report (3)).
4. **Registry.** Row c's writable files add `RBM3D/Test/Axioms.lean`, registry lines only (located by name; union with row b and T2504).
   - `ExpAvgGen_W1fam` and `ExpAvgGen_W1iii` are owed at BA. Owner text: "V1-BA: (iii) from TL1 `BATwistAvgLaw` via `TwistPins_circ_term`; rows 9 + 14 from the probe `T2502c_ba_W1fam` (`t/T2502c` 0f0ad532), (iv) from a public `CltFlowBA_MB_decay`".
   - `ExpAvgGen_W1iiiOfLW` is band-only.
   - Which block each line goes in is decided by the 1b and checked by the auditor.
5. **Size.**
   - Row c central 1,020 → **1,260**: W1 200 → 440 (remainder bound 120, band (iii)/(iv) 60, 16a/16b split 30, 16c 30).
   - Stop 1,450 → **1,750** (under the 1,800 rule; `ExpAvgGen2` reserved as before).
   - Counts unchanged: BA 190, V forecast ≈ 12.
6. **Imports unchanged.** No `BA/*` and no `Chain/Step2Kern` (`Step2Kern_Mss` is in `Chain/Step2Gen:181`; 1a-audit O4).
7. **Paper delta.** The ticket's expectation "paper-delta: none" for row c is replaced by **`T2502ca` = D727** (§319): `6:12-21` covers the scalar `M` only. The 1b report (d) confirms the lines (1a-audit O5).
8. **Unchanged:** rows a and b; row c's cut and file; role `prover-hard`; all other stop rules. 1a-audit O1–O4 are taken as written.
9. **Start.** H300 hands this to the row c workflow (wf_4ab5ae0a-798). The 1b starts after that H line, on `t/T2502c`. The probe stays on the branch and is never merged.
