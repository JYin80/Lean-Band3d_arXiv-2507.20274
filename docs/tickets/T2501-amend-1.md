Amend 1 to T2501 (dispatcher V4, 2026-10-14 03:33 UTC; DECISIONS §313 (2); from the row a2 prove report (d) and audit O2)

**Row b, target 12: instance data for Step 5 cases (i) and (ii).** Row a2 found that the regime windows of cases (i), (ii) are empty at `(sz0, zSeq, flow_sz0)` and that `half_lt_t0` (`BA/FlowPins:1254`) does not give them, and its own datum (B) is `private` in `BA/CltFlowBA`. So:

1. Row b may build **private** instance data in `BA/Step5CasesBA` (stem `Step5CasesBA_`), on the patterns of the merged public `TwistStep2_szII` / `TwistStep2_flowII` (`BA/TwistStep2:1341`, `:1353`) and T2500's private case-(i) datum (`BA/ZeroModeBA:254-335`, `lam ≡ 2`), choosing `lam`, `s`, `t` so that the Step 5 regime windows of cases (i) and (ii) are nonempty. Each datum together with its `BAFlow` proof is at most 120 lines. Re-proving the flow of row a2's datum (B) privately is also allowed.
2. No public `def` (X1-C4); no edit of a merged file (a `private` stays private).
3. The nine carrier predicates of `STIngR5gL` may stay hypotheses, as target 12 already says; the flow, the window and the regime are discharged when a datum exists.
4. **Fallback (no stop):** if no nonempty window is found within the budget, keep the case-(i)/(ii) instances with regime and window as hypotheses and report the numbers tried.
5. Row b's stop line rises from 700 to **900** to cover the data. Nothing else in the ticket changes.
