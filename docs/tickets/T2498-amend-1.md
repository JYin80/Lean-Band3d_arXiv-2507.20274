Amend 1 to T2498 (dispatcher V4, 2026-10-14 02:32 UTC; DECISIONS §311 (4); from the T2501 (U4-BA) draft's consistency check)

**Family row 9 governs over the check shape.** `docs/tickets/T2498.md:73` (family row 9) has the `Θ`-decay premise with `∃ C₆` **after** `κ`: per `(𝔡, κ)`, then `∀ (sz, ε, 𝔠, z)` under the flow, `Step5KerGen_ThDecay (mkM sz z).toFlowFM (gK sz z) 𝔡⁻¹ C₆`. The shape `example` at `docs/tickets/checks/T2498-check.lean:254-258` (a Prop-valued shape, not binding) puts `∃ C₆` before `κ`; read it with `∃ C₆` after `0 < κ`.

Reason: the BA source of the constant, `NewKLKBA_tail` (`RBM3D/BA/NewKLKBA.lean:269`), gives `Q₀` in `(d, Λ, κ)`; a family premise with `C₆` chosen before `κ` has no BA discharge. The BA producer is T2501 target 1 (`baStep5KerGen_thDecay`, row a1), which publishes `∃ C₆` after `κ`.

What to do: if row a's text (1a table, probe, or 1b) already quantifies the premise with `∃ C₆` before `κ`, move it after `0 < κ` before the 1a-audit, or at the 1b start. This only weakens a premise: no target statement changes, and the band discharge is unaffected (its constant does not depend on `κ`). Rows b and c read the same order. Nothing else in the ticket changes.
