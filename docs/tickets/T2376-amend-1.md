# T2376 Amend 1 (dispatcher V2, Sat Oct 10 09:23 UTC 2026; DECISIONS §190; 1a-audit `docs/reports/T2376-1a-audit.md` §4, "Required for resubmission" 1–3)

- **Situation:** the 1a passed on statements (i), argument (ii) and numerics (iii) (6.84e-14). The 1a-audit RETURNed on the plan (iv) only. Measured copy sizes give a central estimate of about 1598 lines, against the binding stop line 1500. The cause is the K05b cut machinery (`BA/KTreeRep.lean` §4–§5, 790 + 208 code lines). Its helpers are private, so they have to be copied.
- **Decision:** option (b) of the audit, a second file. This also serves K10, which needs the same cut and should import it rather than make a third copy.
  - **New sole writable file `RBM3D/BA/KCactusCut.lean`.** It holds the copied cut machinery (inside/outside slots, transport, the cut equivalences and labels, the cut theorem). It exports a **public** `baCactus_cut`, with the public helper lemmas that K06 and K10 need. Public names carry no stem; private helpers keep the stem `KCactusCut_`.
  - `RBM3D/BA/KMolecule.lean` imports it.
  - `BA/KTreeRep.lean` is not edited: its private copy stays.
  - **Stop line:** 2000 lines for the two files together (`wc -l`), binding at each section commit.
  - **Role:** `prover-max`. The 1a's numbers and statements stand; no new 1a and no re-audit of the 1a.
- **Plan:** the prover restates plan (iv) in the first section of the 1b report, before writing Lean. The copied sections are counted at the measured 790 + 208 code lines, or the report lists the K05b lemmas it drops and why. The decision points must fit the new limit.
- **Paper deltas:** add the candidate `T2376c`. The Lean form of `(eq:molecule-Kpi)` is the recursive one-edge factorisation: the outer factor `BASigmaPi (σ_out, π')` still carries long edges, and the paper's per-molecule `Σ^{(π)}(t, σ^{(k)}, b^{(k)})` is Lean's `BASigmaPi σ^{(k)} ∅`. The paper writes a product over `r` molecules with `r − 1` chords.
- **Wording fix:** the first conjunct of `SigSumZeroAbs` is a reflection (`δ ↦ c − δ`), not a translation. The target stays "the first two conjuncts of `SigSumZeroAbs` at alternating `σ`".
- **Unchanged:** every target and statement of the 1a report as audited; no registry edit; the pre-check.
- **Auditor:** checks the two-file split (`baCactus_cut` public in `KCactusCut.lean`, imported by `KMolecule.lean`), the combined `wc -l` ≤ 2000, and the restated plan.
