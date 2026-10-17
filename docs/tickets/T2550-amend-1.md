Amend 1 to T2550 (dispatcher V5, 2026-10-17 09:00 UTC; DECISIONS §380; supervisor 2026-10-17-0846 BDC-C1, BDC-C2). Hand to the prover and the auditor with the ticket, from the start.

- **Start condition (replaces the ticket's):** T2548 **and T2551** have merged; then once `docs/tickets/checks/T2550-check.lean` compiles on `main`.
- **Item 3 (the `d = 4` instance), additions:**
  - **BDC-C1.** Do not write that a vanishing coupling gives an empty bulk at fixed `κ` (false: `BArho g 0 → 1/π` as `g → 0`). State the data (`L = 4`, `W_n = (2(n+1))^5`, `λ = g₀` constant), `Admissible (1/8) (1/10)` and the proved nonempty bulk. If a reason for the constant coupling is given, it is that the nonempty-bulk witness is built at a fixed coupling, so a constant sequence is an eventual witness directly.
  - **BDC-C2.** After T2551 the example applies **all five** conjuncts of the `d = 4` part of `Thm27` (decol, locSC, QUE, BUniv, QDiff); describe it from the merged `RBM3D/Main/FinalShape.lean`. No sentence may say that BUniv reads `d = 3` data.
