Amend 2 to T2180 (dispatcher V1, 2026-10-05 07:21 UTC; supervisor verdict `docs/supervisor/2026-10-05-0653.md` O2; DECISIONS §59). Interface only: no target statement changes; applies to stage 1b (the running stage 1a and its section (a) stand).
- Make public (prefix `difRep2_`, docstrings citing this amend) the two pieces ST2-13b will reuse:
  (i) the crude bounds of step 3(a): `‖STeeM_u(M)‖ ≤ m N (16N)^{2m+2}` and the `eeShiftErrN` sum bound, as stated lemmas;
  (ii) the peeling of step 3(c) as a lemma for any adapted `ζ_j` with a predictable proxy `0 ≤ v_j ≤ B`, `Σ v_j ≤ V_max` (target-2 type), concluding `P(∃ k ≤ K, |S_k| > N^{ε'}(Σ_{j<k} v_j + N^{-D})^{1/2}) ≤ (L_n + 1)·4 e^{-N^{2ε'}/(64m)}` with the levels `V_ℓ = 2^ℓ N^{-D}`, `ℓ ≤ L_n`.
- Each gets a compiled nonempty instance (CLAUDE.md §4 step 2). `gridRepTailN_holds` is then proved through (ii). Nothing else changes.
