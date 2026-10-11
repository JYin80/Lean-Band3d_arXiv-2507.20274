Amend 1 to T2419 (dispatcher V2, Sun Oct 11 10:59 UTC 2026; DECISIONS §236; answers `docs/reports/T2419-audit.md` §3 / "Required for resubmission" item 1 (dispatcher sign-off)).

**Decision: (b), both charges in this row.** The step is the paper's: a vertex with two solid edges **of the same charge** (`B_graphical_lemmas.tex`, the sentence before `\label{GGGamma}`; T2398 design `:67, :96`; the design's `HasGGCand` is charge-symmetric, T2398 probe 77-79), and supervisor 0951 L4-C3's leaf shape (an internal atom has no solid edge or exactly two of opposite colour) needs red pairs to be expandable. A blue-only `BAexpand` would be the special case that does not generalise (TEAM §6).

**Targets added (rule-(B) repair):**
1. **The red-charge `GG` identity** as the complex conjugate of the blue one: from `baExpFrame_gg` (`Graph/BAGGOp.lean:788`, hypotheses `p.1.σ = q.1.σ = true`) by conjugating the graph value (`G(z̄) = G(z)*`, so a red solid edge is the conjugate-transpose of a blue one; `M(−) = M(+)*` by the carrier convention; waved and dotted edges real; the coefficient functional `f` conjugated), with the conjugated output lists of `gg2`/`gg4`. State it as `baExpFrame_gg_red` (or the 1b's name) and prove it from the blue theorem plus a conjugation lemma for `BAGraph.val` / `BAlwData` (the BA law is invariant under `H ↦ H̄` only if it is; if not, conjugate the identity in expectation directly — say which).
2. `BARCand` carries the charge `σ` of the pair (`p.1.σ = q.1.σ = σ`); `kids`, `kids_identity`, `kids_normal`, `BAstep`, `baExpandIdentity_holds` are extended to both charges.
3. One instance at a red candidate (in addition to the blue one).

**Stop rule.** If the red identity needs a new mathematical input beyond conjugation (for example the law is not conjugation-invariant and the conjugated identity in expectation does not follow), stop and RETURN with the obstacle; the dispatcher then falls back to (a) with a successor row. Stop line 2,000 unchanged (current file 462 lines).
**Process:** rule-(B) repair (1b `prover-hard` on `t/T2419` at de1eb31) → auditor round 2.
