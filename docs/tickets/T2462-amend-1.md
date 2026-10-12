Amend 1 to T2462 (dispatcher V3, Mon Oct 12 18:11 UTC 2026; DECISIONS §273 (1)–(2); answer to supervisor verdict 1752 TN-F1 / TN-C1 and to the 1a-audit of 18:07 UTC)

**Why.** Supervisor 1752 (TN-F1, scoped HOLD) found that the comparison hypothesis of §271 (4), `∀ n, 0 ≤ gK n ∧ gK n ≤ sz.lam n ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2`, cannot be discharged in either model for a general admissible `sz`: `Sizes.lam` has no sign at every `n` (`Defs/Sizes.lean:144`; `WO` is eventual), and at BA `gK = BAflowLam0 = √t₀ · sz.lam` exceeds `sz.lam` wherever `sz.lam n < 0`. No 1b may start or merge on that text. Your 1a-audit's O1 found the same.

**Amendment (binding).**
1. **The one comparison text (R1)** is
   `∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2`.
   It replaces the 1457 text in the check and E1 (the §271 (4) text) in the probe. Band: `gK = sz.lam`, `A = 1` (`mul_self_nonneg`, `le_refl`). BA: `gK = BAflowLam0 sz z`, `A = (κ+1)/κ` (`0 ≤ √t₀ · lam²`; `TwistStep2_lam0_sq`, `BA/TwistStep2:740`). Both hold at every `n`, for every admissible `sz`.
2. **The check file is amended by the dispatcher** (`docs/tickets/checks/T2462-check.lean`): the comparison clause of `T2462_ProfileK`, the band and BA UBA-C1 shape lines, and one new shape line (the per-index consequence). Nothing else changes. Recompile it on `main` before the 1b.
3. **Per-index use.** `ProfileK` reads the comparison at one index under the guard `0 < gK n`. Add a private three-line lemma: from R1 at `n` and `0 < gK n`, get `0 < sz.lam n` and `gK n ≤ sz.lam n` (if `sz.lam n < 0`, `0 ≤ gK n * sz.lam n` forces `gK n ≤ 0`; if `sz.lam n = 0`, `gK n ^ 2 ≤ 0` forces `gK n = 0`; so `0 < sz.lam n`, and `gK n ^ 2 ≤ sz.lam n ^ 2` with both positive gives `gK n ≤ sz.lam n`). The rest of the probe proof is unchanged.
4. **Target 12 (a)'s grep literal is the R1 text.** It supersedes `T2462.md:74` and the §271 (4) text.
5. **Non-band instance** (1a-audit O2): do not copy `probeSz1 := sz0.withLam …`. Take a coupling below `sz.lam` for any `sz`, e.g. `gK = fun n => sz.lam n / 2`, `A = 4` (R1 holds at every `n`).
6. **Split confirmed** (1a-audit §8 D4; central 2,011 > 1,950): U4s1a = `Chain/Step5CasesGen` (targets 1–7, the seven registry lines); U4s1b = `Chain/Step5KerGen` + `Chain/NewKLKLGen` (targets 8–11, no registry line). U4s1b runs on its own branch without waiting for U4s1a. Only U4s1b states the comparison (target 9); if any U4s1a statement turns out to need it, it uses R1.
7. The 1a-audit's design decisions D1–D3, F2–F4 stand. O3 (2.6 × the `Step5CasesGen` central is above 2,000) keeps the 2,000 stop line binding in U4s1a's 1b.

Sole writable files: unchanged; under the split, U4s1a keeps `Step5CasesGen` and its registry lines, U4s1b the other two files.
