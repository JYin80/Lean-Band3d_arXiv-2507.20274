Auditor model: claude-opus-5-5

# T2494b audit (row b of T2494: files B + C, target 9, root imports), round 1 — Tue Oct 13 09:20:07 UTC 2026
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2494b-audit1`, detached at `t/T2494b` 49855655. Scratch: scratchpad `T2494b/` (not committed).

## 1. Diff scope
```
$ git diff --name-only main...t/T2494b
RBM3D.lean
RBM3D/Graph/BALWOut.lean
RBM3D/Graph/BATermHoldsB.lean
RBM3D/Test/Axioms.lean
$ grep -rln "import RBM3D.Graph.BATermHoldsB\|import RBM3D.Graph.BALWOut" RBM3D RBM3D.lean
RBM3D.lean
```
All four are sole writable files of the ticket. `RBM3D.lean`: +2 import lines after the last import (`:593-594`), `#assert_rbm_axioms` still last. No merged `.lean` file other than the registry is touched, so no frozen signature is changed.
`Test/Axioms.lean` (diff read in full): `RBM.BA.BALWterm`, `RBM.BA.BALWtermExp` and the T2487 header comment are removed. The owner texts of `LWtermG` and `LWtermExpG` now read "BA: proved (`baLWterm_holds`, `baLWtermExp_holds`, T2494)". The notes of `STLocalEntryUgL`, `STAvgUgL` and `STStep2ConclgL` now read "BA: `baStep2_closed` (T2494)". These are comment edits only, as target 9 specifies. `:197` (`STGdecayWgL`) still says "BA-L6"; per the ticket that line belongs to T2495, so this is an observation only.

## 2. Statements against the pins (check file `docs/tickets/checks/T2494-check.lean`)
Script: copy the check file, add `import RBM3D.Graph.BATermHolds/BATermHoldsB/BALWOut`, and append these lines inside its namespace:
```
example : T2494_TermClosed := baLWterm_holds
example : T2494_TermExpClosed := baLWtermExp_holds
example : T2494_Step2Closed := baStep2_closed
example : T2494_CutClosed := baLWCutExpTw_holds
example : T2494_EXPClosed := baLWtermEXPTw_holds
#print axioms baLWtermExpS_holds / baLWtermExp_holds / baStep2_closed / baLWCutExpTw_holds / baLWtermEXPTw_holds
$ lake env lean T2494b/chk.lean ; echo exit=$?
exit=0
$ grep -nE "error|sorry|depends on axioms" chk.out
405:'RBM.BA.baLWtermExpS_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
406:'RBM.BA.baLWtermExp_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
407:'RBM.BA.baStep2_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
408:'RBM.BA.baLWCutExpTw_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
409:'RBM.BA.baLWtermEXPTw_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Targets 5, 6, 7 (a), 7 (b) are definitionally the binding `T2494_*` texts, which are the merged pins `baPin LWtermExpG`, `BAStep2`, `BALWCutExpTw` and `BALWtermEXPTw`, each `∀ d`. The pins are unchanged because no merged pin file is in the diff. Target 2 (row a) still type-checks against its pin.

Target 4 is the statement def `BALWtermExpS` (B:821-832; read in full). Compared with the merged `LWtermExpG` (`Chain/LWGen.lean`) and with row a's `BALWtermExpN` (`BATermHolds.lean:715`), it has:
- the same binders and order: `3 ≤ d`, `κ ε 𝔡 > 0`, `𝔠 sz z`, `BAFlow`, `0 ≤ t ≤ BAflowT0`, `ε₀ Ψ ℓ`, `LWAssmExpgL`, `∀ D > 0`;
- the same observable `‖LWEg‖` and the same bound `η⁻¹ Bctl^{1/2} W^{-d} tailW … D`;
- the index set restricted to `λ²/L² < 1 - t`, which is the strict complement of `BALWtermExpN`'s `1 - t ≤ λ²/L²`.

The two regimes cover every index, and the union step (B:865-876) uses `by_cases` on exactly this predicate. The theorem `baLWtermExpS_holds` covers every `D > 0`, through `max D (2d+1)` and monotonicity of `tailW` in `D`. It is not restricted to `D ≥ 2d+1`. Quantifier order is the pin's: the fixed parameters come before `sz, z`, and there is no `∃ C` after `(sz, z)`.

The binder of `baStep2_closed` is `d` only. It is the one line from the ticket: `baStep2_holds d (baLWterm_holds d) (baLWtermExp_holds d)`.
The L6 lines are `fun d => baLWCutExpTw_of_S2 d (baExp14bS2_holds d)` and `fun d => baLWtermEXPTw_of_S2 d (baExp14bS2_holds d)`. `BAExp14bS2` is read only at its merged type.

## 3. Vacuity, hidden hypotheses, cycles
```
$ grep -nE "^(theorem|lemma|def|abbrev|structure|class|instance|inductive)" B C     (public declarations)
BALWOut.lean:48:theorem baLWCutExpTw_holds : ∀ d : ℕ, BALWCutExpTw d :=
BALWOut.lean:54:theorem baLWtermEXPTw_holds : ∀ d : ℕ, BALWtermEXPTw d :=
BATermHoldsB.lean:821:def BALWtermExpS (d : ℕ) : Prop :=
BATermHoldsB.lean:838:theorem baLWtermExpS_holds : ∀ d : ℕ, BALWtermExpS d := by
BATermHoldsB.lean:865:theorem baLWtermExp_holds : ∀ d : ℕ, BALWtermExp d := by
BATermHoldsB.lean:879:theorem baStep2_closed : ∀ d : ℕ, BAStep2 d := fun d => ...
$ grep -cE "^private (theorem|lemma|def)" B C        -> BALWOut 1, BATermHoldsB 18
$ grep -n "theorem baExp14bS2_holds|baLWCutExpTw_of_S2|baLWtermEXPTw_of_S2|baTwistAvgProd_holds|baStep2_holds" -r RBM3D
RBM3D/Graph/BAExp14a2.lean:272:theorem baLWCutExpTw_of_S2 : ∀ d : ℕ, BALWCutExpTwOfS2 d := by
RBM3D/Graph/BAExp14a2.lean:326:theorem baLWtermEXPTw_of_S2 : ∀ d : ℕ, BALWtermEXPTwOfS2 d :=
RBM3D/Graph/BAExp14b2B.lean:1064:theorem baExp14bS2_holds (d : ℕ) : BAExp14bS2 d := by
RBM3D/BA/Step2CloseBA.lean:181:theorem baStep2_holds (d : ℕ) (hLW : BALWterm d) (hLWE : BALWtermExp d) : BAStep2 d := by
RBM3D/BA/TwistAvgB.lean:451:theorem baTwistAvgProd_holds (d : ℕ) : BATwistAvgProd d :=
$ grep -cE "STGridRepNgL|BAAnpAuxG|BAShapePath" B C ; grep -cwE 'mE|STGM|STKloop|etaT|STflowE|lwS' B C ; grep -cw inductive B C
0 0 ; 0 0 ; 0 0
```
- Every producer that is used is merged on `main` and unconditional. The axiom lines in §2 show that nothing open sits in the dependency closure.
- No public result has a pin binder: the theorems have binder `d` only. The only `LWAssmExpgL` binder is on a private lemma (B:399).
- `LWAssmExpgL` enters only as the antecedent inside the pin text, which is the merged pin's own form. It is not a structure field and is not hidden.
- No cycle: B and C import only merged modules, and nothing except `RBM3D.lean` imports them.

## 4. Compiled nonempty instances (read in full: B:895-1000, C:62-122)
All instances use `d = 3`, `sz0` (L ≥ 3; `n = 0` gives `L = 4`, `W = 32`, `λ = 1/64`), `zSeq`, `flow_sz0` (`κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`) and `t ≡ 1/2` with `half_lt_t0`. Every deterministic hypothesis is discharged by `norm_num`, `le_rfl`, `flow_sz0` or `half_lt_t0`.

| target | instance | remaining hypotheses (other gates' pins, allowed by ticket :39) | nondegeneracy |
|---|---|---|---|
| 4 `baLWtermExpS_holds` | B:960 | `STInitialGT2gL`, `LWLoopExpgL` | Fields discharged: `ε₀ = 1/10 > 0`; `Ψ0_window`; `ℓ = ellT ≥ 1`; `ℓ ≤ (log W)^{10} ℓ_t` (from `log W ≥ 1`). `D = 5 < 2d+1` exercises the `max` branch. Index set nonempty at every `n` (B:945). |
| 5 `baLWtermExp_holds` | B:973 | same | Full index set `(Fin 2 → Bool) × (Fin 2 → Zd 3 L)`, nonempty. |
| 6 `baStep2_closed` | B:986 | none: the `ST*` antecedents belong to the `BAStep2` conclusion | `s ≡ 1/10 ≤ BAflowT0`, `s < t`, both discharged. |
| 7 (b) `baLWtermEXPTw_holds` | C:94 | `STLocalEntrygL`, `LWAvgLawgL`, `STLmaxgL`, `STLKgL`, `STDecaygL`, TL2 `BATwistLoopLaw` | TL1 discharged by `baTwistAvgProd_holds 3`. Index `λ²/L³ ≤ 1/2` holds at every `n` (`BALWOut_reg`); nonempty (C:87). |
| 7 (a) `baLWCutExpTw_holds` | C:109 | same | same |

The 8 (c) shape check: the conclusion text of C:94 matches the check's instance-8 (c) shape (`U` with `^ 3`, `‖∫ LWEg‖`, `(1-t)⁻¹ Bctl^{5/2}`), and TL1 is dropped through its producer. The hypotheses are the ones the check lists.

The regime `1 - t ≤ λ²/L²` is `baLWtermExpN_holds`, row a's merged target 3, not a target of this row. Ticket 8 (b) allows "n/a with the reason". The reason is compiled at B:952: for every `t ≤ BAflowT0 sz0 zSeq n ≤ 25/36` we have `λ²/L² ≤ 2^{-12} < 1 - t`, so that index set is empty at the merged flow data. Target 5's instance is still nondegenerate, because its index set is the full product.

## 5. Builds and axioms
```
$ lake build RBM3D.Graph.BATermHoldsB RBM3D.Graph.BALWOut   (Tue Oct 13 09:17:38 → 09:17:59 UTC 2026)
Build completed successfully (4146 jobs).        exit=0
$ lake build   (full library, registry check; Tue Oct 13 09:18:42 → 09:19:55 UTC 2026)
Build completed successfully (4365 jobs).        exit=0
$ grep -c error full.log ; grep -n "axiom audit" full.log ; grep -c BALWterm full.log
0
6385:info: RBM3D.lean:597:0: axiom audit: 14822 theorems, 4587 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
0
$ grep -nwE "sorry|admit|native_decide|axiom" B C ; echo exit=$?
exit=1
```
`#assert_rbm_axioms` passes after the target-9 edits. The `#print axioms` output in §2 shows only the three standard axioms.

## 6. Paper deltas
```
$ grep -nE "T2342|T2375|T2398d" docs/paper-deltas.md   (excerpt)
1605:- **D641（T2375a–d）** … (c) … 归约要 `D ≥ 2d+1`（交叉项 `W^{-D}𝖳`），小 `D` 经 `2d+1` 处的前提 …
415:- **D99（T2040k）**：`1 − t ≤ ĝ²/L²` 时的 `lem: EWGn2_N` … 单钉为 `LWtermExpN`（LW-16）。
1630:- **D666（T2398d）**：`B:118` … BA 情形的 Lemma B.1（`lem:LWterm_EXP`）「类比……省略细节」 …
```
Each Lean/paper difference in this row is covered:
- The regime split and the `D ≥ 2d+1` branch are already in the file (D99, D641 (c)).
- The R1 seven-premise form of `lem:LWterm_EXP` at BA is D666 (T2398d).
- The `|M_yx|` term of `(eq:directG2)` at BA, regime `1 - t > λ²/L²`, is the new candidate `T2494c` (prove report (d)). Its companion is row a's `T2494a`.
- The radius `ρ_n = log N √(log N)` of `baGbyZeta_holds` (B:28, B:403), instead of the ticket's `ρ = 1`, is covered by row a's candidate `T2494b` (`T2494-prove.md:207`).

## 7. Observations (no RETURN)
- O1. The row-b prove report does not cite row a's candidate `T2494b` for the radius used in file B (B:403). The candidate exists and covers it.
- O2. `Test/Axioms.lean:197` (`STGdecayWgL`) is now a stale "BA-L6" note. Per the ticket it is T2495's line, and the prover reports it too.
- O3. Closing condition (ix): the five-premise `BALWtermEXP` (`LWPinsBA:49`) has no producer and no registry line, as recorded. The ticket requires no edit.

## Verdict
| target | verdict |
|---|---|
| 4 `baLWtermExpS_holds` (def `BALWtermExpS`) | PASS |
| 5 `baLWtermExp_holds` | PASS |
| 6 `baStep2_closed` | PASS |
| 7 `baLWCutExpTw_holds`, `baLWtermEXPTw_holds` | PASS |
| 8 (b), (c), (d) instances | PASS (8 (b) regime N: n/a with compiled reason, as the ticket allows) |
| 9 registry | PASS |

Overall: **PASS**. No dispatcher sign-off needed.
