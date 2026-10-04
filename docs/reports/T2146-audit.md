Auditor model: claude-opus-5-5

# T2146 audit (round 1): ST2-32 `GoodSetN`, exit times, measurability, `GridGoodN`

Written Sun Oct  4 18:24:53 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2146-audit1`, detached at `t/T2146` = `9b4564f`.
The ticket pins no Lean text (`docs/tickets/checks/T2146-check.lean` has only `#check`s of upstream names), so each statement is checked against the ticket's mathematics, the RBM2D source `GridGoodN.lean` at `c9a24cf`, and the merged signatures it uses.

## 1. Build, axioms, hygiene (audit worktree)
```
$ lake build RBM3D.Induction.GridGoodN 2>&1 | grep -E "error|warning: .*GridGoodN|depends on axioms|Build completed|sorry" | grep GridGoodN
info: RBM3D/Induction/GridGoodN.lean:1235:0: 'RBM.Gauss.Sizes.gridGood_STmaxLM_seqHflow' depends on axioms: [propext, Classical.choice, Quot.sound]
  ... (lines 1236-1244, same axiom list)
info: RBM3D/Induction/GridGoodN.lean:1245:0: 'RBM.Gauss.Sizes.gridGoodN_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/GridGoodN.lean:1246:0: 'RBM.Gauss.GridGoodNInst.grid_data' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/GridGoodN.lean:1247:0: 'RBM.Gauss.GridGoodNInst.tInst_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/GridGoodN.lean:1248:0: 'RBM.Gauss.GridGoodNInst.gridGood_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/GridGoodN.lean:1249:0: 'RBM.Gauss.GridGoodNInst.gridGood_instance_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3783 jobs).
$ lake env lean RBM3D/Induction/GridGoodN.lean   # fresh elaboration, no cache
  16 output lines; 15 "depends on axioms: [propext, Classical.choice, Quot.sound]"; 0 lines matching error|warning|sorry
$ bash scratchpad/T2146/scan.sh   (excerpt)
--- diff stat main...t/T2146 (Axioms.lean, RBM3D.lean):
       0
--- forbidden tokens in GridGoodN.lean (sorry|admit|native_decide|axiom):
       0
--- files touched by git diff --name-only main...t/T2146:
RBM3D/Induction/GridGoodN.lean
```
Only the sole writable file is touched; `RBM3D/Test/Axioms.lean` unchanged (no new premise); no merged file or frozen signature touched.
Name-clash scan (declarations on `main` named `STmaxLM STmaxLKM STXiLM STXiLKM GoodSetN gridExitTauN goodExitTauN MeasurableGoodSetN GoodExitMeasN measurableGoodSetN goodExitMeasN GridGoodNConcl GridGoodN gridGoodN_holds GridGoodNInst gridExitTauN_le mem_of_lt_gridExitTauN gridExitTauN_eq_of_forall_mem gridExitTauN_measurableSet`): `decls-on-main=0` for each of the 19.

## 2. Target 1: `GoodSetN` (file :124-149)
Checked against the ticket's clause list and RBM2D `GoodSetN` (`c9a24cf:GridGoodN.lean:81`). The ticket lets the preflight drop clauses that no consumer uses. Consumer destructurings at `c9a24cf`:
```
$ for f in GridEnvelopeN GridGoodEvent GridAssemblyN AzumaProxyN NonAltGood AltEnd AltLevelsQ AltEndCompose AltProxyQ; do git show c9a24cf:RBM2D/Induction/$f.lean | grep -nE "obtain ⟨[^⟩]*⟩ := ..." ; done   (GoodSetN hits)
NonAltGood 79:  obtain ⟨-, -, -, -, -, -, hD1, hD2, hD3, -, -, -⟩ := hM
NonAltGood 103: obtain ⟨-, -, -, -, -, -, -, -, -, -, hVa, -⟩ := hM
NonAltGood 130: obtain ⟨-, -, -, -, -, -, -, -, -, hD4, -, hVb⟩ := hM
NonAltGood 424: obtain ⟨hMh, -, -, -, -, hDec, -⟩ := hM
NonAltGood 1287: obtain ⟨-, -, -, -, -, hDec, -⟩ := hM
AltEnd 517:     obtain ⟨-, -, hG2, -, -, hDec, -⟩ := hM
AltLevelsQ 173: obtain ⟨-, -, -, -, -, -, hD1, hD2, hD3, -, hV, -⟩ := hM
AltLevelsQ 332: obtain ⟨-, -, hG2, -, -, hDec, -⟩ := hM
AltEndCompose 449 / AltProxyQ 955: obtain ⟨-, -, -, -, -, -, -, -, -, hD4, -, hVb⟩ := hM
(projection uses: hM.1 only, at NonAltGood:1431, AltEnd:506, AltLevelsQ:321, AltEndCompose:448)
```
No consumer ever names positions 2 (G1 `Ξ^L_{2k+2}`), 4 (G3 products `·M⁻¹`) or 5 (G4 `Ξ^L_{k+1}`), so dropping them follows the ticket's rule. The 9 remaining clauses (Herm, G2, Dec, D1-D4, Va, Vb) are each checked against the merged statement that should give them:
| clause | Lean (`GoodSetN`) | merged source (signature read) | check |
|---|---|---|---|
| G2 | `STXiLKM m H ≤ ΓΦ`, `1 ≤ m < k` | `STXiLK` (`Step34Pins:68`); `STXiLKM (seqHflow) = STXiLK` by `rfl` (:95) | matches |
| Dec | `‖loopFine‖+‖loopFine − STKloop‖ ≤ W^{-D'}` if `ell_u W^{τ'} ≤ STdiamInf a`, `1 ≤ j ≤ 2k+2` | `STDecayLoopU` (`DecayLoopB:792`): same window, same `STdiamInf`, every `k ≥ 1`, `τ' D' > 0` | matches |
| D1 | `‖STksimLKM l (loopOf σ a)‖ ≤ Γ(ΓΦ)B^k/η`, `3 ≤ l ≤ k` | conjunct (2) of `STSEforLnConcl` (`Step34Pins:369`): `B^k/η · Ξ^{LK}_{k-l+2}`, same `l` range | level = one `Γ` from `≺`, `Ξ^{LK} ≤ ΓΦ` |
| D2 | `‖STelklkM‖ ≤ Γ·k(ΓΦ)²B^k/η` | conjunct (3) (:374): `B^k/η[Σ_{n'} Ξ^{LK}(Ξ^LΞ^L)^{1/2} + B^{1/6}Ξ^{LK}_k]` | `Φ²` forced (no `M⁻¹`); delta `T2146b` |
| D3 | `‖STegtM‖ ≤ Γ(ΓΦ)B^k/η` | conjunct (1) (:365): `B^k/η (Ξ^L_{n1}Ξ^L_{n2})^{1/2}` | matches |
| D4 | `‖STeeM σ a a'‖ ≤ Γ(ΓΛ)B^{2k}/η` | conjunct (4) (:381): `B^{2k−1/(2q)}/η · Ξ^L_{2k−1}(Ξ^L_{4q})^{1/(2q)}` = `B^{2k}/η · Ξ_{2k−1}(Ξ_{4q}/B)^{1/(2q)}` = `hQ` | matches |
| Va, Vb | far decay of `Σ_l ksimLK + elklk + egt` and of `ee` (`Fin.append a a'`) | `stEtermDecay` (`DecayLoopB:2209`) | same shape as RBM2D |
The matrix-level terms `STksimLKM`, `STelklkM`, `STegtM`, `STeeM` are the merged ones (`Step2Defs:723,737,750,757`). The clauses take no hypotheses, have no structure fields, and are not vacuous: their levels are positive and finite whenever `B, η > 0`, and the instance in §5 shows that the good event is eventually nonempty. **PASS.**

## 3. Target 2: exit times (file :169-219)
`gridExitTauN` and `goodExitTauN` are, token for token, RBM2D `:123-145` with `d : Sizes` replaced by `sz : Sizes d` (the same `firstHit` of the complement indicator at `1/2`, horizon `K n`). Signatures of the four lemmas (`_le`, `mem_of_lt_`, `_eq_of_forall_mem`, `_measurableSet`) are identical modulo `sz`. `firstHit_eq_of_below` is reproved as private `gridGood_firstHit_eq_of_below`. **PASS.**

## 4. Target 3: measurability (file :233, :361, :411, :423)
`MeasurableGoodSetN d := ∀ sz n E u k Γ Λ Φ τ' D', MeasurableSet (sz.GoodSetN …)` has no hypothesis (RBM2D: no hypothesis either). `GoodExitMeasN` has the RBM2D form. `goodExitMeasN` is unconditional (it uses `measurableGoodSetN`). **PASS.**

## 5. Target 4: `GridGoodN` / `gridGoodN_holds` (file :505-528, :930)
`GridGoodN d := STIngR d STAny (fun sz E s t => GridGoodNConcl sz E s t)`. `STIngR` (`Step34Pins:445`) is exactly the ticket's context: `3 ≤ d`, `κ ε 𝔡 Cd > 0`, `∃ 𝔠d ∈ (0,1/100]`, `STFlow`, `0 ≤ s < t ≤ lemT z`, `STKbound`, `STKward`, `STLK s`, `STConStInd`, `STStep2Concl … Cd`. `STAny` is `True` (:272).
`GridGoodNConcl` against the ticket:
- `s ≤ v ≤ t`, `K n ≠ 0`, `k ≥ 2`, `Λ, Φ ≥ 1` (for all `n`; the ticket says "Λ, Φ ≥ 1").
- `hX`: `Prec[TimeIcc s t] Ξ^L_m ≺ Φ` for `m ≤ k+1`. `hY`: `Ξ^{LK}_m ≺ Φ` for `m ≤ k`. `hQ`: for one caller-chosen `q ≥ 1`, `Ξ^L_{2k−1}(Ξ^L_{4q}/B)^{1/(2q)} ≺ Λ`. These are of the `STXiBoot` shape the ticket asks for, and the lengths cover every `Ξ̂` in the four conjuncts.
- `K+1 ≤ N^C` only eventually. This is weaker than the ticket's bound, so the theorem is stronger.
- Conclusion: for every `ε, τ', D' > 0`, `HighProbAt (pathP sz) sz.size {∀ j ≤ K n, pathH … j ∈ GoodSetN … (gridTime …) k (N^ε) Λ Φ τ' D'}`. This is the ticket's conclusion, and its quantifier order is RBM2D's.
The RBM2D premises `MainIndHyp, KboundConcl, KcalDecay, GbEXPHypV3, Step2LocalPT, Step2DecayPT, DecayLoopPT, PT` are absent. Their replacements are listed in the `GridGoodNConcl` docstring (file :499-504) and in prove report row 22.
Dependencies, all merged on `main` (the module builds): `stSEforLn_holds` (T2137/T2139), `stDecayLoopU_of_step2`, `stEtermDecay`, `map_pathH_eq`, `STBctl_mono`. The new file creates no cycle: `gridGoodN_holds` depends only on these merged results.
**PASS.**

## 6. Compiled nonempty instances (file :1117-1229; all elaborate, see §1)
- `measurableGoodSetN`: `example` at `sz0`, `n = 0` (`L = 4`, `W = 32`, `N = 2097152`), `E = 1/2`, `u = 1/32`, `k = 2`, `Γ = 4`, `Λ = 3`, `Φ = 1`, `τ' = 1/2`, `D' = 1`.
- `goodExitMeasN`, and the three exit-time lemmas: `example`s at `sz0` on the grid `s ≡ 0`, `v ≡ 1/32`, `K ≡ 4`. `grid_data` proves `Δ = 1/128`, `u_0 = 0`, `u_1 = 1/128`, `u_4 = 1/32`, so the window is not collapsed. `K ≡ 4` is the merged grid size `K0` (`GridDriftN.lean:1194`).
- `gridGoodN_holds`: `gridGood_instance k hk`, through `inst_ing` at `d = 3`, `sz0`, `flow_z0`, `s ≡ 0`, `t ≡ 1/16`, `Cd = 1`, with examples at `k = 2` and `k = 4`. Every deterministic hypothesis is discharged: `s ≤ v ≤ t`, `K ≠ 0`, `Λ_n = max 1 (B_n(0)^{-1/10}) ≥ 1`, `Φ ≡ 1`, `q = 5`, `K+1 = 5 ≤ N^1` eventually, `ε = 1/10`, `τ' = 1/2`, `D' = 1`. `hX`, `hY`, `hQ` are proved from `STLmaxU` and `STLKU`.
- Kept as hypotheses: `STKbound`, `STKward`, `STLK`, `STStep2Concl` (the `STIngR` premises) and `STLmaxU`, `STLKU`. All are registered owed pins of other gates (`RBM3D/Test/Axioms.lean:90,100,101`, `STStep2Concl` class "owed", line 183 note). This is allowed by CLAUDE.md §4 step 2.
- `gridGood_instance_nonempty`: under the same pins, `∀ᶠ n, ∃ ω, ∀ j ≤ 4, pathH … ∈ GoodSetN …`, so `GoodSetN` is not vacuous at the instance.
No instance uses `N = 0`, an empty index, a collapsed window, a `False` premise, or an astronomically large witness. **PASS.**

## 7. Paper-delta coverage
Each Lean-vs-paper/RBM2D difference has a candidate in prove report (d):
- the dropped clauses G1, G3, G4, and `hQ` as the source of `Λ`: `T2146a`;
- the D1-D4 levels, with no `(k−1)`, `Φ²` in D2, and no additive `W^{-D'}`: `T2146b`;
- `STdiamInf` (ℓ^∞), `sz : Sizes d`, and the `STIngR` shape with the RBM2D hypotheses replaced: `T2146c`.
The remaining differences are covered by these candidates or are Lean-only shapes: `1 ≤ Λ, Φ` for every `n` (the ticket's wording), and `K+1 ≤ N^C` only eventually (this strengthens the theorem). **PASS.**

## 8. Observations (no RETURN)
- O1: `0 ∈ GoodSetN` at `u = 0` is not a Lean statement here. It is a script check only (prove report (a) row 15, (d)). RBM2D consumers `AzumaProxyN:1300`, `NonAltGood:996` used it, so ST2-33/34 may need it as a separate lemma. It is not a target of this ticket.
- O2: the proof does not use the hypothesis `1 ≤ Λ n`, nor the pin premises `STKbound`, `STKward`, `STLK s`. They are harmless: they are part of the pinned `STIngR` shape.
- O3: the public `vg`, `Kg`, `grid_data`, `tInst_lt_one` lack the `gridGood_` prefix but sit in the file-specific namespace `RBM.Gauss.GridGoodNInst`. They do not clash (§1).
- O4: the vocabulary defs `STmaxLM`, `STmaxLKM`, `STXiLM`, `STXiLKM` are public and are needed by the pinned `GoodSetN`. Each is `rfl`-linked to the merged `STmaxL`/`STmaxLK`/`STXiL`/`STXiLK` at `seqHflow` (file :86-96).

## Verdict
| target | verdict |
|---|---|
| `GoodSetN` | PASS |
| `gridExitTauN`, `goodExitTauN` + 4 lemmas | PASS |
| `MeasurableGoodSetN`, `GoodExitMeasN`, `measurableGoodSetN`, `goodExitMeasN` | PASS |
| `GridGoodN`, `GridGoodNConcl`, `gridGoodN_holds` | PASS |
Ticket T2146: **PASS**. No dispatcher sign-off is needed.
