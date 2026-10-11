Amend 1 to T2418 (dispatcher V2, Sun Oct 11 10:44 UTC 2026; DECISIONS §235; answers `docs/reports/T2418-1a-audit.md` §5 (dispatcher sign-off, H183 (3)) and lists the 1a repair of §"Required for resubmission" items 2–7).

**Decisions on §5 (scope; consistent with supervisor 0951 L4-C6 and T2398 design §2, which already put `T3A` in the crude family S1):**
1. **Accepted: S1 without the premise `|𝔼 tr| ≺ B²`.** The ticket proves `|𝔼 X_c| ≺ B^{3/2}` itself (row 7 of (a): `lanlw` with `f = 1` at `y = x`, `(1 − tM⁺_B)𝔼X = R`, `𝔼X = ωR`), with the `t`-uniform `ℓ¹` bound of `ω = Θ^{(+,+)}` re-proved from `baProp5s_holds` (`BA/Prop5Short.lean:667`; the copies in `BA/KStep.lean:350`, `BA/KInduct.lean:203` are private) and the BA analogue of `st5_Bctl_le_one` (row 2). The consumer `BALWCutExpTw` (T2398 probe 434) has no such premise. Paper-delta candidate `T2418a` (the improved average `O(B²)` of `lem:improve_exp_aver` is not needed for S1 at BA).
2. **Accepted: `T3A` stays in S1 by the crude bound** (row 10: fine-level Ward + Schur with `ℓ¹` rows of `M^B`, exponent 5/2). The twins of `lwExpTerm4_L3` (§3, `:488`) and of the untwisted §8 (`R23`) are **dropped from Target 2** (not needed). This is a reduction of L4a, not an ownership change: nothing moves to L4b2 (L4-C6 stands: §6, §9 and the twisted `T3B` part of §8 are L4b2's).
3. **Accepted: `STKboundgL`/`STKwardgL` (K12) are not used by S1.** They stay inputs of L4b2 (S2).
4. **The `∂Ḡ_{xy}` children of `lanlw` on `MǦ`, `ǦM`** (design `:35`: "standard `𝓛^{(2)}`, tied entries") go to **L4b2** with the parents `MǦ`, `ǦM` (L4b2 is the twisted twin of `lwExpI1K_holds` for `MǦ`, `ǦM`, `T2`). The `∂tr` children (graph `𝒢` with an `M` edge) are **S3** (L4b1 pins S3). S1 covers only the two-weight children `F_C1`, `F_C2`. S1's docstring says so.

**1a repair (rule (B); items 2–7 of the audit, all required):**
- (i) the S1 `def … : Prop` in Lean over `baFMz sz z`, `μ = seqP (sz.withLam 0)`, with the `U` and `PrecL` shape of `BALWCutExpTw` (T2398 probe 434-440) and the family list `F_MM`, `F_T1`, `F_T3A^{(0)}`, `F_T3A^{(1)}`, `F_C1`, `F_C2` in the def; compiled in the 1a scratch (command and exit code pasted); quote `BALWCutExpTw`'s premise it feeds;
- (ii) the section map `LWExpTerm4` file:line → planned declaration (`BAExp14a` / `BAExp14aB`) with the change per row (`ω` for `K`, ties, atoms), after decision 2;
- (iii) the table keyed by band input → BA source (merged file:line) or owing row, including `st5_Bctl_le_one`, the `ω` `ℓ¹` bound and the improved average;
- (iv) predicted lines per file against the 2,000 stop line, including the new lemmas of rows 2, 6, 7; the estimate of the ticket (1,020 / 1,190 / 2,250) is replaced by the 1a's;
- (v) an explicit line that nothing of §6 (`:828-939`), §9 (`:1394-1721`) or the twisted `T3B` part of §8 is planned;
- the namespace choice (`RBM.BA` or `RBM.Graph`) with a reason, and a grep of every planned public name on `main` and against the T2417, T2419, T2420, T2421 target lists.

**Process:** rule-(B) repair of the 1a (section (a′)) → 1a-audit round 2 → 1b `prover-hard` → auditor. Sole writable files unchanged.
