Amend 1 to T2390 (dispatcher V2, Sat Oct 10 21:10 UTC 2026; DECISIONS §203; answers the question in `docs/queue/T2390.state` and the 1a-audit `docs/reports/T2390-1a-audit.md` §4, "Required for resubmission" D1–D4)

**Held:** T2390 does not resume until a dispatcher H line says so (Jun, 21:09 UTC: the hub is being switched after this wave; DECISIONS §203). This amend fixes what the resumed run does.

1. **D2 (decision): `BAGbEXPii'` is not pinned; the merged `BAGbEXPii` (`BA/Step1Boot.lean:108`) stands in for it.**
   - Section G.3 of the 1a proves the merged shape `1_Ω ‖G_t − M‖²_max ≺ max 𝓛^{(2)}` (all pairs) by the same argument. Under `max 𝓛 ≺ Ψ_t²` it implies the printed `(GiiGEX_BA)(a)` (`7_8:1930-1932`).
   - The consumers (`baBootstrap'_holds`, `baStep1_holds`) read the merged shape.
   - The supervisor's C3 named `BAGbEXPii'` because of F1. F1 concerns `BAGijGEX`, whose band shape needs a window comparison that is not in the TeX. The diagonal pin needs no such comparison.
   - Paper-delta candidate **T2390d**: the right side is `max 𝓛` in place of `Ψ_t`; it is stronger than the printed form and proved.
   - The C2 REQ asks the supervisor to confirm this. Only `BAGbEXPij'` is re-pinned (and `BAGbEXPav'` stays as merged, G.7).
2. **D1 (process): the probe compile is a separate step with a Lean role.** Before the 1a repair, the hub runs one short step with the role `prover-max`. Its sole writable file is `RBM3D/Probe/T2390Pins.lean` on `t/T2390`, never merged.
   - It writes `BAGbEXPij'` and `BAStab` from G.7 / G.8.
   - It runs `lake env lean RBM3D/Probe/T2390Pins.lean` in the T2390 worktree.
   - It pastes the command, the exit code and the `#check` output into the prove report as `(a″)`.

   CLAUDE.md §4 bars `preflight` from Lean, so the step cannot be the preflight. It contains no proofs beyond `example … := by …` for nonemptiness, and no `sorry`.
3. **D3 (1a repair, rule (B) once): `preflight` writes `(a′)`.**
   - The two-sided inequality for `R_{a,y}` with explicit constants: each of its three terms derived from (E1′) and the minor identity.
   - A **local** closure: either the `R` closure in the weighted norm (the absorbed term localised by `|G_vw| ≤ |M_vw| + |Δ_vw|`, with `Δ` weighted), or iteration `⌈D/ε₀⌉` times to `W^{-D}`. Write out the absorbed term.
   - Then G.4's linear part restated with that local bound, and the constant of the `c_λ` weights tracked.

   If this cannot be closed, stop and RETURN. The question to Jun is then the mathematical one of supervisor C2: one question.
4. **D4 (instance plan):** replace the `t = 0` plan in G.8 with concrete nondegenerate data (`t > 0`, `Δ ≠ 0`, explicit numeric `K`, `ρ`, `δ` with `Kδ ≤ 1/2`). Name the hypotheses that remain other gates' pins: `BALDEin` is now merged (T2389, b6cc9d2), so name it by its merged name; `BAStab` belongs to G3b.
5. **Order once resumed:** D1 step → `(a′)` → 1a-audit round 2 → 1b `prover-max` (T2389 has merged: no further wait) → auditor. After the 1a-audit round 2 PASS the dispatcher sends the C2 REQ (it does not block 1b).

Unchanged: targets of stage 1b (G.8 row G3a, `BA/GreenCore.lean`), C1, the stop line 2000, the sole writable files of 1b, the acceptance criteria.
