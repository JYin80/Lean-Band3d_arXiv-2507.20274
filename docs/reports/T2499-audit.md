Auditor model: claude-opus-5-5

# T2499 audit (round 1) — U5e `RBM3D/BA/Step5IIITargets.lean`

Written Wed Oct 14 01:57:27 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2499-audit1`, detached at `t/T2499` = 0c272838.

## 0. Diff scope

```
$ git diff --stat main...t/T2499
 RBM3D.lean                    |   1 +
 RBM3D/BA/Step5IIITargets.lean | 112 ++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean        |   3 +-
$ git diff --stat main...HEAD -- RBM3D/BA/Step5IIIWalk.lean RBM3D/BA/Step5IIIWalk2.lean RBM3D/BA/SEforLnBA.lean RBM3D/Chain RBM3D/Induction
(empty)
$ grep -rln "RBM3D.BA.Step5IIITargets" RBM3D RBM3D.lean
RBM3D.lean
```
Only the sole writable files. `RBM3D.lean`: one import line, inserted among the imports (not after `#assert_rbm_axioms`). `Test/Axioms.lean`: one `owedProps` line deleted (`RBM.BA.STPfStep5gL`), one note appended to the T2462 header comment, as CONTROL H291 (3) / decision (4) require:
```
$ git show main:RBM3D/Test/Axioms.lean | grep -c "RBM.BA.STPfStep5gL"   -> 1
$ git show t/T2499:RBM3D/Test/Axioms.lean | grep -c "RBM.BA.STPfStep5gL" -> 0
```
`STDecayStronggL` line stays (Axioms.lean:229 on the branch).

## 1. Statements against the binding pins (script)

Scratch file (uncommitted, scratchpad `T2499/AuditT2499.lean`): the check's imports plus `RBM3D.BA.Step5IIITargets`, the pin text
copied verbatim from `docs/tickets/checks/T2499-check.lean:95-106`, then
```
example : T2499_MainOfParts := baPfStep5_of_walk
example : T2499_STPfStep5BA := baPfStep5_holds
example : T2499_STStep5IIIBA := baStep5III_holds
#print axioms baPfStep5_of_walk
#print axioms baPfStep5_holds
#print axioms baStep5III_holds
```
```
$ lake env lean $S/AuditT2499.lean; echo "exit=$?"
'RBM.BA.baPfStep5_of_walk' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baPfStep5_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5III_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```
The three pins close by the term itself (no unfolding, no coercion), so each target is its pin up to the name:
- T1 `baPfStep5_of_walk : BAStep5IIIWalk → BAStep5IIIFromWalk → STPfStep5gL 3 (fun sz => seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow …) baFMz BAflowT0`.
- T2 `baPfStep5_holds : STPfStep5gL 3 …` (same tuple), no premise.
- T3 `baStep5III_holds : STStep5IIIgL 3 …` (same tuple), no premise.

Quantifier order is the merged `STIngR5gL` (`Chain/Step5Gen.lean:190-213`): `3 ≤ d → ∀ κ ε 𝔡 > 0, ∀ Cd > 0, ∃ 𝔠d, 0 < 𝔠d ∧ 𝔠d ≤ 1/100 ∧ ∀ 𝔠 sz z, Flow → ∀ s t, …`; the
only `∃` is `𝔠d`, before `(sz, z)`; no `∃ C` after `(sz, z)`. Regime `STReg5III sz s t := ∀ n, sz.lam n ^ 2 ≤ 1 - t n` (`Induction/Step5Pins.lean:58`) = paper case `1 − t ≥ λ²` (`3_5:2284`). Check file on the branch:
```
$ lake env lean docs/tickets/checks/T2499-check.lean ; echo exit=$?   -> exit=0, 0 error lines
```

## 2. Vacuity, hidden hypotheses, cycles

- No new structure; one `private def Step5IIITargets_instPrem : Prop` (conjunction used only by the instances; not in any target signature).
- T1's premises are the two merged closed Props; T2/T3 have none. Their inputs are merged theorems:
```
ST_step5_caseIII_of_pfgL : ∀ d law Flow mk T0, Step5CasesGen_FlowFacts d Flow mk T0 → STPfStep5gL d law Flow mk T0 → STStep5IIIgL d law Flow mk T0
baStep5CasesGen_flowFacts : ∀ d, Step5CasesGen_FlowFacts d (fun sz κ ε 𝔠 𝔡 z => BAFlow …) (fun sz z => baFMz sz z) fun sz z => BAflowT0 sz z
```
  plus `baStep5IIIWalk_holds`, `baStep5IIIFromWalk_holds` (merged `BA/Step5IIIWalk2`). No dependency on this file from below (new leaf, importer only `RBM3D.lean`): no cycle.
- No external hypothesis is added.

Greps on the new file (hypothesis rules of the ticket):
```
--forbidden  grep -nE '\bsorry\b|\badmit\b|\baxiom\b|native_decide'                 -> (none)
--C1         grep -nE 'BAK_le_small|…|STGridRepNgL'                                 -> (none)
--X1-C4      grep -nE '^(noncomputable )?(def|abbrev|structure) '                   -> (none)
             grep -nE '^(private )?(noncomputable )?(def|abbrev|structure) '        -> 68:private def Step5IIITargets_instPrem : Prop :=
--UBA        withLam outside `seqP (sz.withLam 0)` / `seqP (SizesInst.sz0.withLam 0)` -> (none);  'gK|≤ A \*' -> (none)
--T2459/T2462 text                                                                  -> (none)
```
The single private def is under the stem (rule (E)), a bundle of instance hypotheses, permitted by the ticket ("private instance bundles under the stem only").

## 3. Compiled nonempty instance (target 4)

Data: `SizesInst.sz0 : Sizes 3` (`Defs/Sizes.lean:260`: `L n = 4(n+1)`, `W n = (2(n+1))^5`, `lam n = (2(n+1))^{-6}`; `sz0_values`: `L 0 = 4, W 0 = 32, lam 0 = 1/64`), `zSeq`,
`(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`, `s ≡ 1/10 < t ≡ 1/2`, `Cd = 1`. Ingredient signatures (`#check` in the audit worktree):
```
FlowPinsInst.flow_sz0 : BAFlow SizesInst.sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) FlowPinsInst.zSeq
FlowPinsInst.half_lt_t0 : ∀ (n : ℕ), 1 / 2 < BAflowT0 SizesInst.sz0 FlowPinsInst.zSeq n
Step5IIIGood_reg_sz0 : SizesInst.sz0.STReg5III (fun x => 1 / 10) fun x => 1 / 2
@Ind.Step1SetupInst.s1Setup_conStInd_const : ∀ {s0 t0 𝔠d : ℝ}, s0 < t0 → t0 < 1 → 0 < 𝔠d → SizesInst.sz0.STConStInd 𝔠d (fun x => s0) fun x => t0
@ST_step5_assemblygL : ∀ {d} {sz : Sizes d} (C : FlowFM sz) μ (s t : ℕ → ℝ), (∀ n, s n ≤ t n) → STStep5ConclgL C μ s t → STDecaygL C μ t ∧ STDecayStronggL C μ t
```
Discharged at the data in the file (lines 80-110): `3 ≤ 3` (`le_rfl`), `0 < κ, ε, 𝔡`, `0 < Cd` (`norm_num`/`one_pos`), Flow (`flow_sz0`),
`0 ≤ s`, `s < t` (`norm_num`), `t ≤ T0` (`half_lt_t0`), the regime (`Step5IIIGood_reg_sz0`), `(con_st_ind)` at the pin's own `𝔠d`
(`s1Setup_conStInd_const … h0`, so not fixed by the prover). Left as hypotheses (`Step5IIITargets_instPrem`): exactly the nine carrier
predicates `STKboundgL, STKwardgL, STLKgL, STDecaygL, STDecayStronggL, STStep1LoopgL, STStep2ConclgL, STLmaxUgL, STLKUgL`; the last two are
`#print`ed and unfold to the two inline `PrecL` premises of `STIngR5gL` (`Step5Gen.lean:205-212`) — other gates' pins, allowed by §4 step 2.
Instances: (a) `example … : STPfConclgL …` (T2), (b) `example … : STStep5ConclgL …` (T3), (c) `example … : STDecaygL … ∧ STDecayStronggL …` at `t ≡ 1/2` (T3 then `ST_step5_assemblygL`).
T1 is exercised through (a) (T2 := T1 at the merged parts). Nondegenerate: `L ≥ 4`, `W ≥ 32`, `lam ≤ 1/64`, `s < t` strictly, no `False` premise, no large witness. All compile (build below).

## 4. Build and axioms

```
$ lake build RBM3D.BA.Step5IIITargets 2>&1 | grep -E "error|Build completed"
Build completed successfully (4122 jobs).
$ lake build 2>&1 | grep -E "error:|premises found by scanning|Build completed"
premises found by scanning: 123 (borrowed 1, owed 56, structural 46, refuted 6, superseded 14).
Build completed successfully (4377 jobs).
$ lake build RBM3D 2>&1 | grep -c STPfStep5gL
0
```
Axioms of T1–T3: standard three (section 1). `#assert_rbm_axioms` passes on the branch; `STPfStep5gL` is no longer listed anywhere in the
registry output (neither owed nor "carry nothing yet"). The only diagnostics of the new file are `linter.style.longLine` warnings at lines
13-24 (module docstring; `set_option` follows it).

## 5. Paper deltas

- Lean vs paper: T2/T3 are `lem:pf_step5` (`3_5:2364-2383`) and Step 5 case (iii) (`3_5:2284`) at the BA tuple through the merged generic
  pins; the paper (`7_8:2101`) omits the BA argument — covered by D702 (T2459a), whose open note "U5e 尚未写" (`docs/paper-deltas.md:1710`)
  the report proposes to close with the three names (report `:160`).
- `d = 3` only (decision (8), U-C5): recorded in D712 (d) ("目标 3、4 只在 `d = 3`", `paper-deltas.md:1720`) for the U5d inputs this row composes.
- No new Lean/paper difference introduced by this row; no new candidate needed.

## 6. Observations (no effect on statement, instance, build, axioms or delta coverage)

- O1: prove report is 162 lines (`wc -l`), above the ticket's ≤ 120 (within CLAUDE.md §6's 300).
- O2: long-line linter warnings in the module docstring (lines 13-24); harmless.

## Verdicts

| target | statement vs pin | vacuity / hidden / cycle | instance | build / axioms | deltas | verdict |
|---|---|---|---|---|---|---|
| 1 `baPfStep5_of_walk` | = `T2499_MainOfParts` | none | via 4(a) | pass / std 3 | D702 | PASS |
| 2 `baPfStep5_holds` | = `T2499_STPfStep5BA` | none | 4(a) | pass / std 3 | D702 | PASS |
| 3 `baStep5III_holds` | = `T2499_STStep5IIIBA` | none | 4(b), 4(c) | pass / std 3 | D702, D712 | PASS |
| 4 instances | shapes of the check | nine carrier pins only | compiled, nondegenerate | pass | — | PASS |
| registry edit | `STPfStep5gL` line removed, note added | — | — | full build pass | — | PASS |

**Ticket verdict: PASS.** No dispatcher sign-off needed.
