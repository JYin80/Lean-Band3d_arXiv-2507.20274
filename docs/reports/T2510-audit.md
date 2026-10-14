Auditor model: claude-opus-5-5

# T2510 row a audit (targets 1-10): `BA/Step6BridgeBA`, `BA/Step6PinsBA`

Audit started Wed Oct 14 15:36:24 UTC 2026 (`date -u`). Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2510-audit1`, detached at `t/T2510` = eb8a998b (base d1839622). Row b (targets 11-15) is not in scope.

## 1. Diff scope and build

```
$ git diff --stat main...HEAD
 RBM3D.lean                  |   2 +
 RBM3D/BA/Step6BridgeBA.lean | 395 +++++
 RBM3D/BA/Step6PinsBA.lean   | 488 +++++
 RBM3D/Test/Axioms.lean      |  22 +-
$ git diff --name-only --diff-filter=M main...HEAD      -> RBM3D.lean, RBM3D/Test/Axioms.lean
$ git diff --name-only --diff-filter=A main...HEAD      -> RBM3D/BA/Step6BridgeBA.lean, RBM3D/BA/Step6PinsBA.lean
$ git diff --stat main...HEAD -- RBM3D/Chain RBM3D/Induction RBM3D/Graph RBM3D/Defs RBM3D/Gauss | wc -l
0
$ lake build RBM3D.BA.Step6BridgeBA RBM3D.BA.Step6PinsBA     (no error lines)
Build completed successfully (4240 jobs).
```
`RBM3D.lean`: two import lines (`BA.Step6BridgeBA`, `BA.Step6PinsBA`) after the last import, before `#assert_rbm_axioms`. All four files are row a's sole writable files. No merged file and no frozen signature is touched.

Registry (`Test/Axioms.lean`). Only comment texts change; the lists of names are identical:
```
$ diff <(git show d1839622:RBM3D/Test/Axioms.lean | grep -oE "^\s+\`[A-Za-z0-9_.']+") <(grep -oE "^\s+\`[A-Za-z0-9_.']+" RBM3D/Test/Axioms.lean) && echo identical
registry name lists identical
```
The owner texts changed: STImproveExpAvergL, ExpAvgGen_W1fam, ExpAvgGen_W1iii, ExpAvgGen_W1iiiOfLW, STExpLKLKHigL, STExpDriftLogL, STExpDriftDecaygL, STExpWardIgL, STExpIniIgL, STExpIntIIgL, LWtermEXPG. At b4147edc these are lines 227-234, 236, 238, 241, which is the ticket's row-a list. 230 and 241 keep "not produced" and add the T2510 route. Row-b lines 225, 226, 235, 237, 239, 240, 242 are untouched.

## 2. Hygiene greps (both files)

```
# sorry/admit/axiom/native_decide        Step6PinsBA.lean:0  Step6BridgeBA.lean:0
# public def/abbrev/structure/class/instance
RBM3D/BA/Step6PinsBA.lean:59:def BAStep6R (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
# cut grep T2508|ExpWardIIGen|ExpIntEasyGen|ExpIntIGen|QopDecayGen|ExpIntIQGen   Step6BridgeBA:0  Step6PinsBA:0
# withLam not of the form `seqP (X.withLam 0)`                                    0
# C1  mE\b|\|E\||SB d|M = m|m • 1|etaT|STFlow|bandFM  in the 18 public statements 0
# V1L-C1 STImproveExpAver|st6_expAvgU_of_ping|LWtermEXPG in the 18 public statements 0
# name clash: git grep "(theorem|lemma|def|abbrev|structure) (<18 names>)" <ref> -- RBM3D
main: 0   t/T2508b: 0   t/T2509: 0
```
Every helper is `private` and carries the stem `Step6BridgeBA_` or `Step6PinsBA_`. Merged privates are read through `open private`: `TwistPins_circ_term` (+3), `CltFlowBA_MB_decay`, `SEforLnBA_Kbound`, `Step5CasesBA_sz/_z/_Datum/_datum`. No `private` is deleted (no merged file changes).

## 3. Statements against the pins (`docs/tickets/checks/T2510-check.lean` Part 2)

Elaborator check (uncommitted scratch `scratchpad/T2510/audit_pins.lean`). It contains the check's imports plus the two new modules, the `T2510_*` defs copied from the check, then the examples below:
```
example (d) (R) : T2510_Step6BA d R = BAStep6R d R := rfl
example (d) (R) : BAStep6R d R ↔ T2510_Step6BA d R := Iff.rfl
example : ∀ d, T2510_W1iiiOfTL1 d := baExpAvgGen_W1iii_of_tl1
example : ∀ d, T2510_W1ivBA d := baExpAvgGen_W1iv
example : ∀ d, T2510_W1famBA d := baExpAvgGen_W1fam
example : ∀ d, T2510_CoreBA d := baImproveCoregL
example : ∀ d, T2510_ExpAvgUBA d := baExpAvgUgL_of_tl1
example : ∀ d, T2510_IngBA d := fun d => ⟨baExpLKLKHigL d, baExpDriftLogL d, baExpDriftDecaygL d, baExpWardIgL d,
  baExpWardIgL' d, baExpIniIgL' d, baExpIntIIgL d, baExpDuhamelZgL d, baExpDuhamelQgL d⟩
example : ∀ d, T2510_RegIIIOfPin d := baStep6RegIII_of_pin
example : ∀ d, T2510_RegIVOfPin d := baStep6RegIV_of_pin
example : ∀ d, T2510_RegIIOfPin d := baStep6RegII_of_pin
$ lake env lean audit_pins.lean; echo "exit: $?"
exit: 0
```
Textual diff by script: the whitespace-normalised theorem statement is compared with the pin body.
```
baExpAvgGen_W1iii_of_tl1 identical text
baExpAvgGen_W1iv identical text
baExpAvgGen_W1fam identical text
baImproveCoregL identical text
baExpAvgUgL_of_tl1 identical text
baStep6RegIII_of_pin identical text (T2510_Step6BA -> BAStep6R)
baStep6RegIV_of_pin identical text (T2510_Step6BA -> BAStep6R)
baStep6RegII_of_pin identical text (T2510_Step6BA -> BAStep6R)
BAStep6R vs T2510_Step6BA (signature+body): identical text
```
Targets 7 and 8 are stated as the merged pin predicates (`STExpLKLKHigL d …`, …, `STExpDuhamelQgL d …`) at the BA tuple, with no extra hypothesis. The elaborator example above accepts them as the conjuncts of `T2510_IngBA`.

Statement reading:
**Target 1.** No range premise on `u` was added: F7, and decision (6) left it optional. **Target 2.** `∃ CM` comes after `(κ, 𝔡)` and before `(ε, 𝔠, sz, z)` (U5S-C3). **Target 4.** The eventual `hK1` lives only in the private twins `Step6BridgeBA_LWAvg_ev` and `_expAvgU_of_core`, whose `hK1 : ∀ᶠ n, …` matches the shape `T2510_LWAvgEv`. It is discharged inside the proof by `baKsol_oneLoop` (`Step6BridgeBA_K1`), so no every-`n` `hK1` remains in any public statement (F1, §332 (3)). **Target 9.** The only extra hypotheses are the T2508-owned pins (`STExpIntIIIgL`, `STExpIntIVgL`, `STExpWardIIgL`), which have merged type, as pinned. Every other input is discharged in the proofs: `baExpLKLKHigL`, `baExpDriftLogL`, `baExpIntIIgL`, `baExpDuhamelZgL`, `Step6BridgeBA_LW`, `baExpAvgUgL_of_tl1`, `st6_ini_sumNdecayg`/`st6_ini_nonzerog` with `baEKKer_flow` and `Aof κ = (κ+1)/κ`. `𝔠d = min` of the input pins' constants.

## 4. Vacuity, hidden hypotheses, cycles

The only new public def is `BAStep6R`, which is literally `T2510_Step6BA`. No new structure exists, so no hypothesis can sit in a field. `BAFlow` and the `STIngR6gL` premises are merged predicates read from their signatures. Targets 7 and 8 are unconditional theorems. Target 3 (`baImproveCoregL`) is `stImproveCoregL_of (baStep5CasesGen_flowFacts d) (baExpAvgGen_W1fam d)`. Targets 1 and 4 keep TL1 (`BATwistAvgLaw`), and `BAStep6R` keeps TL1 and TL2 on its `Concl` slot, all as pinned. These are owed pins of other gates; the paper delta is D666, D685, D727. Cycles: Lean imports admit none, and every import is a merged module on the base d1839622. The cut grep is 0, so no T2508-row-b or unmerged name is read. External hypotheses: none added.

## 5. Compiled nonempty instances (in the files; compiled by the build in §1)

Data: `d = 3`.
Flow `(sz0, zSeq, flow_sz0)` with `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`, where `L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^-6`. Regimes (i), (ii), (iv) are empty at `sz0`, so they use the merged private datum `Step5CasesBA_datum` (decision (10)), with `(L, W₀, lam, κ, t)`: - (i) `(4, 25, 2, 3/1000, 1/400)` - (ii) `(4, 25, 5, 3/5000, 1/2000)` - (iv) `(3, 40, 6, 1/1000, 1/2000)` - In each, `s ≡ 0`, `W_n = n + W₀`, and `(ε, 𝔠, 𝔡) = (1/2, 1/9, 1/10)`. `Step5CasesBA_Datum` (merged, `BA/Step5CasesBA.lean:391`) is purely deterministic: `0 < κ ∧ BAFlow … ∧ 0 ≤ s ∧ s < t ∧ t ≤ T₀ ∧ ∀ 𝔠d > 0, STConStInd`. It is proved by `norm_num` side conditions at the numbers above.

| target | example (file:line) | data | binders left (other gates' pins) |
|---|---|---|---|
| 1 | Bridge:358 | sz0, `u ≡ 1/2` | `LWAvgLawgL`, `STLmaxgL` at u (TL1 built by `baTwistAvgProd_holds`) |
| 2 | Bridge:363 | sz0 flow | none |
| 3 W1fam | Bridge:368 | sz0 flow | none |
| 3 Core | Bridge:376 | sz0, `u ≡ 1/2` | `LWAvgLawgL`, `STLmaxgL`, `STLKgL` |
| 4 | Bridge:383 | sz0, `s ≡ 1/2 < t ≡ 3/5 ≤ 2/3 ≤ T₀` | `STStep2CoregL`, `STLKUgL`, TL1 on [s,t] |
| 6 | via 9 (Pins:461-482) | as 9 | as 9 |
| 7 LKLK | Pins:345 | sz0, `STDriftHi` from `STReg5III` | `Step6PinsBA_prem` (7 stochastic Step 1/2/4/5 pins) |
| 7 DriftLog | Pins:397 | datum (iv), `STReg5IV` | prem; `STExpAvgUgL` (pin's own premise) |
| 7 DriftDecay, WardI, WardI′, IniI′ | Pins:403, 408, 414, 420 | datum (i), `STReg5I` | prem (+ `STExpAvgUgL` for WardI/I′) |
| 7 IntII | Pins:425 | datum (ii), `STReg5II` | prem; Duhamel/drift premises of the pin's conclusion |
| 8 | Pins:437, 451 | sz0, index n = 1, `0 < g₀` (`inst_lam0_pos`) | none (all of KLoop, KTwo, KLink, loop form, `S = SB`, semigroup discharged) |
| 9 (iii) | Pins:461 | sz0, `[1/2, 3/5]`, `STReg5III` | `STExpIntIIIgL`, prem, TL1/TL2 |
| 9 (iv) | Pins:469 | datum (iv) | `STExpIntIVgL`, prem, TL1/TL2 |
| 9 (ii) | Pins:477 | datum (ii) | `STExpWardIIgL`, prem, TL1/TL2 |

Every regime premise `R sz s t` and `(con_st_ind)`, together with `0 ≤ s < t ≤ T₀`, the flow and the positivity facts, is discharged at the data (`Step6PinsBA_reg3`, `_regI/_regII/_regIV`, `_con0`, `_tT0`, `Step5CasesBA_datum`).
- `Step6PinsBA_prem` (Pins:306) is exactly the seven stochastic premises of `STIngR6gL`: `STLKgL`, `STDecaygL`, `STExp2gL`, `STStep2CoregL`, `STLmaxUgL`, `STLKUgL`, `STGdecayWgL … 0`.
- No instance uses `N = 0`, an empty index or window, a `False` premise, or an astronomically large witness. `L ≥ 3`, `W_n → ∞` and `s < t` hold throughout.

## 6. Axioms

```
$ lake env lean audit_pins.lean  (#print axioms of the 18 public declarations)
18 × "depends on axioms: [propext, Classical.choice, Quot.sound]"; no other output line
```
Names: baExpAvgGen_W1iii_of_tl1, baExpAvgGen_W1iv, baExpAvgGen_W1fam, baImproveCoregL, baExpAvgUgL_of_tl1, BAStep6R, baExpLKLKHigL, baExpDriftLogL, baExpDriftDecaygL, baExpWardIgL, baExpWardIgL', baExpIniIgL', baExpIntIIgL, baExpDuhamelZgL, baExpDuhamelQgL, baStep6RegIII_of_pin, baStep6RegIV_of_pin, baStep6RegII_of_pin.

## 7. Paper deltas

Row a has no new Lean/paper statement difference.
**Eventual Duhamel (target 8):** D725. **W1 (iii)/(iv) and the TL1 premise of `lem:improve_exp_aver` at BA (targets 1-4):** D727. **TL1/TL2 in the LW and Step-6 slot (`BAStep6R`, `Step6BridgeBA_LW`):** D666, D685 (and D696 for `BALWtermEXPTw`). **Eventual `hK1` (F1):** Lean-internal. DECISIONS §332 (3) says no paper delta. **Instance-data change in (a′):** this changes no statement.

The report's "none (`T2510a` not used)" is consistent with this.

## 8. Observations (no statement, instance, build, axiom or coverage effect)

- O1. `git merge-tree --write-tree main t/T2510` against current main (beefb80b, T2509 merged) reports `CONFLICT (content): Merge conflict in RBM3D.lean`. Both branches append import lines at the same place. This is the union that CONTROL H312 (3) anticipates; `Test/Axioms.lean` merges cleanly. The hub's rule (A) step 4 (adding imports by hand) resolves it.
- O2. The ticket's file-2 import list gains `Chain/ExpEtermsAGen` and `BA/Step5CasesBA`. This is reported in (a′). The ticket says "the 1a fixes the lists", and neither import is a T2508 module.
- O3. Section (a) (ii)'s instance pointer for regime (ii) (`TwistStep2_szII`) differs from the built data (`Step5CasesBA_datum` at the same numbers). (a′) records this.

## Verdict

| target | verdict |
|---|---|
| 1 `baExpAvgGen_W1iii_of_tl1` | PASS |
| 2 `baExpAvgGen_W1iv` | PASS |
| 3 `baExpAvgGen_W1fam`, `baImproveCoregL` | PASS |
| 4 `baExpAvgUgL_of_tl1` | PASS |
| 5 private glue (`Step6BridgeBA_LW`, `_decay`) | PASS (used by 7, 9; compiled) |
| 6 `BAStep6R` | PASS |
| 7 seven pins at BA | PASS |
| 8 `baExpDuhamelZgL`, `baExpDuhamelQgL` | PASS |
| 9 `baStep6RegIII/IV/II_of_pin` | PASS |
| 10 instances | PASS |

**T2510 row a: PASS.** No dispatcher sign-off needed.
