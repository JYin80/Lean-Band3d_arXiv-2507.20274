Amend 1 to T2460 (dispatcher V3, Mon Oct 12 17:10 UTC 2026; DECISIONS §271; answer to the stage-1a preflight FAIL of 16:54 UTC)

**What failed.** Target 1, `T2460_Bridge`, third conjunct H3 (quadratic variation), was pinned as an equality `twEEk … = STEEMg …` (verbatim from U-D's probe `T2452_Bridge`). It is false: `twEEk` has cross terms, while `STEEMg` holds only the two diagonal 6-loops. It held in 0 of 216 random Hermitian cases; at H = 0, σ = (+,+), a0 = a1 the two sides are 4 and 2 times |z|⁻⁶W⁻⁴ᵈ (`docs/reports/T2460-prove.md:28-58`). H1 and H2 hold; targets 2, 3, 5 PASS.

**Amendment (binding).**
1. The check file `docs/tickets/checks/T2460-check.lean` is amended by the dispatcher: the third conjunct of `T2460_Bridge` now reads `‖twEEk … (a 0) (a 1) (a 1) k ω‖ ≤ 2 * ‖STEEMg … σ a‖` (H3′; sharp, the constant is the slot count 2; true in the prover's numerics with 0 violations, by |Q₁+Q₂|² ≤ 2|Q₁|² + 2|Q₂|²). Nothing else in the check changes.
2. The glue of target 2 uses H3′ in place of the equality: the pin event at ε′ lies inside TL's event at ε′/2, eventually in n (N ≥ 2^{1/ε′}, `SizeTendsto`), as in the report's (iii). Target 2's statement `T2460_GridMart` is unchanged.
3. **Target 4 (`T2460_GridRepN2`, the m = 2 list form with clause 4) leaves this row before 1b**, as pre-signed in the dispatcher notes: clause 4 weights two slots (`Step2Gen_UN`), TL's clause (iv) one slot (`twU`), so it does not follow from TL. Its consumer is U5 (T2459). Whether U5 can use the one-slot clause, or a new T row (two-slot BA tail) is opened, is decided after T2459's design report (DECISIONS §271).
4. Resume: re-run the preflight check of H3′ against the amended check file (the numerics already done count), then 1b `prover-hard` → auditor, with targets 1 (amended), 2, 3, 5, 6.

Sole writable files: unchanged (`RBM3D/BA/GridMartBA.lean`, `RBM3D.lean` import line).
