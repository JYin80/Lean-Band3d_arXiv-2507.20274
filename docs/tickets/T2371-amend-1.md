# T2371 Amend 1 (dispatcher V2, Sat Oct 10 04:31 UTC 2026; DECISIONS §184; 1a report `docs/reports/T2371-prove.md` (ii), plan steps 5–6)

- **Situation:** the 1a PASSed. It proves leaves 9 (`UNDensBandRow`) and 10 (`UNTrLocalBandRow`) here. It keeps leaf 11 (`UNNormBandRow`) as a hypothesis unless it fits in the remainder of the stop line. It replaces `UNGUELocal` by `UNGUESchurTail` through `un_gueLocal_of_tail`. It reports that leaves 11 and 16 have no ticket.
- **Decision:** both now have producers. Leaf 11 is **T2372** (UN-10a, `Universality/NormBand.lean`, `unNormBandRow`). Leaf 16 is **T2373** (UN-10b, `Universality/GUELocalSchur.lean`, `gueSchurTail`, `gueLocal`).
- **Edits to the plan:**
  - Plan step 5 is dropped. Do **not** start leaf 11 here, even if it would fit. It stays a hypothesis of `bUniv_holds`.
  - Leaves 9 and 10 stay as planned (steps 3–4), with the same stop line 500.
  - The docstring of `bUniv_holds` names the producers: leaf 11 → T2372; `UNGUESchurTail` → T2373; `UNMLOut` → ST-6; `UNLocAvgBand`, `UNQueBand` → MA inputs; `UNL32` → borrowed.
- **Unchanged:** the other targets; the registry rule (delete only the lines of leaves proved here); the sole writable files. `Test/Axioms.lean` line `:196` (`UNNormBandRow`) belongs to T2372: do not touch it.
- **Auditor:** checks that no `NormBand`-type proof of leaf 11 appears in the diff, and that the docstring names the producers.
