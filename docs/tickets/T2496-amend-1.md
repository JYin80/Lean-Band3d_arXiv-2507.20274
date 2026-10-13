Amend 1 to T2496 (dispatcher V3, 2026-10-13 09:17 UTC; DECISIONS §301; answers the U4s3a 1b stop, `docs/reports/T2496-prove.md` (d) A6–A9, `:207-211`)

The 1b of U4s3a stopped before writing Lean (the 1b-start name-level check). Four facts that the converted proofs read have no home in premise rows 1–11 as the 1a-audit fixed them (G1–G4). This amend approves the four additions under the conditions below. Nothing else in the ticket changes: D1 (the merged `Step5IIIWalk_duhamel`), the loop modulus, the `EtermsMid2` cut A3 and the split all stand.

1. **A6 (G1) — approved as written.** D2 gains the F9 clause-1 conjunct `∀ n u ω x y, Cm.GMM n u (Hm n u ω) x y = Cm.GM n u ω x y` after the LM conjunct. The first four conjuncts keep the text the 1a-audit fixed. The 1b states the extended form as the conclusion of a public forgetful lemma, so the auditor's `example : T2496_FlowMod .. := ..` still applies. Band: `rfl`. BA: `Step2EventsGenTw_baGrid` clause 1.
2. **A7 (G2) — approved as written.** Add an inline guarded premise next to `‖m‖ ≤ 1`: `∀ n a, ∑ b, ‖(mkM sz z).S n a b‖ ≤ 1` (precedent T2491 answer (5); text from `SEforLnGen_Facts`). Band: `sum_norm_SB_row`. BA: `S = 1`.
3. **A8 (G3) — approved, in this order.**
   - (a) First derive the bound on `𝒦^{(2)}` from A9's merged decay class `Step2IterGen_K2` plus an upper bound on `STprof`. Do this at the head of the 1b, before other Lean.
   - (b) If (a) does not close there, use the inline eventual premise `∀ᶠ n, ∀ u ∈ [0, t n], ∀ σ a, ‖C.K n u σ a‖ ≤ N`. Name its band discharge and its BA discharge (for example `baKbound_holds` through `STKboundgL` at `k = 2`) in the prove report.
   - If (b) has no BA discharge, stop and report (no unprovable premise at BA).
4. **A9 (G4) — approved.** Row 7 moves to carrier level.
   - The `𝒦^{(2)}` decay is the merged `Step2IterGen_K2 d Flow mkM` (BA: `baStep2_K2`).
   - `lem:newKLK` at `ℓ = L` becomes a new carrier-level class. It has `∃ C δ₀` per `(κ, 𝔡)` fixed before the sizes, quantifies `∀ᶠ n`, and has the body of `STNewKLKLAtgL'` at `mkM sz z`. It needs the sharp `ℓ = L` form with `J² · prof` and a `W^{-D}` floor; the general-`ℓ` `Step2IterGen_NewKLK` does not suffice.
   - Its band discharge comes from `stNewKLKL_holds` at index `n` (the pattern of `step2IterGen_newKLKAtN_band`, `Step2IterGen:104`). Its BA owner is **U4-BA** at mixed coupling, with the pattern of `baStep2_newKLK` (`Step2IterBA:701-705`; R1 enters only inside that BA discharge).
   - `STK2decaygL'`, `STNewKLKLgL'` and the glue `mkM = mkE ∘ E` then leave the premise lists of targets 5, 8 and 9.
   - **No probe for the new class.** The 1b compiles the class text and its band discharge first, before the targets that read it, and pastes the class text at the head of the prove report. The auditor checks it against the use in `(S5WG+M000)` and against the 0349 U5S-C3 rules (family-uniform `∃`, eventual `∀ᶠ n`, flow guard if the BA discharge needs it).
5. **Family-premise table:** add rows for A7, A8 (if (b)) and A9, each marked guarded or unguarded, with its BA discharge.
6. **Sizes and layout:** the four additions add lines. The pre-signed split stands. Under the 1,800 rule, a file predicted above 1,800 uses the reserve `EtermsMid2`. The UP-C2 (d) calibration count includes these lines; moved lines stay excluded.
7. **Targets 6–9 (U4s3b):** G1, G2 and G4 probably recur there. The same texts apply; no further amend is needed for them.
