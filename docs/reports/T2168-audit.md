Auditor model: claude-opus-5-5

# T2168 audit (round 1): ST2-12 `STGridRepN` part 1, `RBM3D/Path/DifREP1.lean`

Time: Mon Oct  5 04:14:08 UTC 2026 (`date -u`). Branch `t/T2168` at `5b72e15`, merge base `87f617a`.
Audit worktree: `/Users/junyin/Lean_proof/RBM3D-wt/T2168-audit1` (detached, cache cloned with `cp -c -R`).
Scratch: `scratchpad/T2168/` (`AuditCheck.lean`, `Reg.lean`, `Reg2.lean`, logs).

## 1. Diff scope

```
$ git diff --stat main...t/T2168
 RBM3D/Path/DifREP1.lean | 1458 +++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean  |    2 +
$ git diff main...t/T2168 -- RBM3D/Test/Axioms.lean   (the added lines only)
+   `RBM.Ind.GridRepTailNAt, -- clause (iii) / (iv) of `STGridRepNAt` for `difRepMartN`: ST2-13 (T2168)
+   `RBM.Ind.GridRepWTailNAt, -- clause (iii) / (iv) of `STGridRepNAt` for `difRepMartN`: ST2-13 (T2168)
```
Only the two sole writable files are touched. The registry change is exactly the two pinned `owedProps` lines. The `STGridRepN` line is unchanged. No existing declaration or frozen signature is touched.

## 2. Statements against the pin (check file `docs/tickets/checks/T2168-check.lean`, sections 2-3)

Text diff by script (python, whitespace-normalised). Definitions: `def X` block in the check file vs. the branch file. Theorems: the body of `XStmt : Prop :=` vs. the theorem type:
```
difRepMartN IDENTICAL 3 lines          difRep_identity IDENTICAL
difRepRemN IDENTICAL 6 lines           difRepMartN_succ_sub IDENTICAL
GridRepRemNAt IDENTICAL 18 lines       difRep_Ugen_step_le IDENTICAL
GridRepTailNAt IDENTICAL 14 lines      difRep_flow_bounds IDENTICAL
GridRepWTailNAt IDENTICAL 19 lines     gridRepRemN_holds IDENTICAL
                                       stGridRepNAt_of_parts IDENTICAL
                                       stGridRepN_of_tails IDENTICAL
                                       stGridMartAt_of_parts2 IDENTICAL
                                       stGridMart_of_tail IDENTICAL
```
Lean check: `AuditCheck.lean` = `import RBM3D.Path.DifREP1` + check-file lines 101-248 verbatim (namespace `RBM.Ind.T2168Check`), followed by
```
example : @T2168Check.difRepMartN = @RBM.Ind.difRepMartN := rfl      -- and the same for difRepRemN,
example : T2168Check.GridRepRemNAt = RBM.Ind.GridRepRemNAt := rfl    -- GridRepTailNAt, GridRepWTailNAt
example : T2168Check.DifRepIdentityStmt := @RBM.Ind.difRep_identity  -- and the same for all 9 targets
```
`lake env lean AuditCheck.lean`: no errors, and all 14 `example`s elaborate (output in §4). Each target's type is the pinned one. The quantifier order is the pin's. Fixed `κ ε 𝔡 𝔠 sz z s t` come before `∃ CK`, `∃ CK` before `∀ K`, and `∀ K` before `∀ᶠ n`. `C₀ = m + 9` depends on `m` only. The window `0 ≤ s ≤ t ≤ lemT (z n)` matches the pin. `3 ≤ d` appears only on `gridRepRemN_holds`, `stGridRepN_of_tails` and `stGridMart_of_tail` (§36).

`stGridRepNAt_of_parts` concludes the merged pin `STGridRepNAt d m C₀` and `stGridMartAt_of_parts2` concludes the merged pin `STGridMartAt d C₀`. So the vocabulary is not weaker than the pin's clauses (i)-(iv) for `Mart = difRepMartN`. Neither is a special case: `gridRepRemN_holds` is the general statement for every `d ≥ 3` and `m ≥ 2`.

## 3. Vacuity, hidden hypotheses, cycles

- No new `structure`/`class`. The five definitions are `def`s identical to the pin (§2). No hypothesis is hidden in a field.
- `gridRepRemN_holds` takes no premise beyond `3 ≤ d` and `2 ≤ m` (plus the pin's `STFlow` and window inside `GridRepRemNAt`). Its axioms are the standard three (§4). It is therefore unconditional, and `STFlow` is satisfiable: the instance uses the merged `flow_z0`. The proof uses `CK = 8m + 20` (`DifREP1.lean:1162`).
- Owed premises: `GridRepTailNAt`, `GridRepWTailNAt` (clauses (iii)/(iv), owed to ST2-13a/b). They are registered in `owedProps`, as the ticket pins. They are not external inputs, so TEAM §8 lesson 14 does not apply. `stGridRepN_of_tails` and `stGridMart_of_tail` are conditional on them, and their statements say so.
- No cycle: no target uses `STGridRepN`/`STGridMart` as a premise in its proof. Grep shows that the 15 public names (14 targets plus namespace `DifREP1Inst`) have 0 hits on `main`:
```
DifREP1Inst main-hits=0   difRepMartN main-hits=0   ...   stGridMart_of_tail main-hits=0   (all 15: 0)
```

## 4. Build and axioms

```
$ lake build RBM3D.Path.DifREP1          (audit worktree; DifREP1 olean absent before, compiled fresh)
✔ [3838/3838] Built RBM3D.Path.DifREP1 (6.8s)
Build completed successfully (3838 jobs).
exit=0
```
The build log has no `error` lines and no warning lines for `DifREP1.lean`. Every warning is a line-length lint in other files.
```
$ grep -nE "\bsorry\b|\badmit\b|^\s*axiom\b|native_decide|implemented_by|@\[extern" RBM3D/Path/DifREP1.lean
grep-exit=1   (no hits)
$ lake env lean AuditCheck.lean    (#print axioms)
'RBM.Ind.difRepMartN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.difRepRemN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.GridRepRemNAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.GridRepTailNAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.GridRepWTailNAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.difRep_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.difRepMartN_succ_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.difRep_Ugen_step_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.difRep_flow_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.gridRepRemN_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.stGridRepNAt_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.stGridRepN_of_tails' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.stGridMartAt_of_parts2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.stGridMart_of_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.DifREP1Inst.inst_difRep_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.DifREP1Inst.inst_difRepMartN_succ_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.DifREP1Inst.inst_difRep_Ugen_step_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.DifREP1Inst.inst_difRep_flow_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.DifREP1Inst.inst_gridRepRemN' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Registry pre-check: the whole library plus the new module. This needs `lake build RBM3D` in the worktree, which gave `exit=0`.
```
$ printf 'import RBM3D\nimport RBM3D.Path.DifREP1\n#assert_rbm_axioms\n' > Reg2.lean; lake env lean Reg2.lean
exit=0
  RBM.Gauss.Sizes.STGridRepN: 6 [no certificate]
  RBM.Ind.GridRepTailNAt: 4 [no certificate]
  RBM.Ind.GridRepWTailNAt: 2 [no certificate]
registry: 1 borrowed + 87 owed + 49 structural; ...
```

## 5. Compiled nonempty instances (`DifREP1.lean:1320-1456`, namespace `RBM.Ind.DifREP1Inst`)

| target | instance | data | owed hypotheses kept |
|---|---|---|---|
| `difRep_identity` | `inst_difRep_identity`, `example := … ω0` | `sz0`, `z0`, `s ≡ 0`, `t ≡ 1/16`, `K ≡ 4` (`gridStep = 1/64`, proved), `n = 0`, `m = 3`, `σ = (+,-,+)`, `k = 3`, `ω0` | none |
| `difRepMartN_succ_sub` | `inst_difRepMartN_succ_sub`, `example := … ω0` | same, `j = 2` | none |
| `difRep_Ugen_step_le` | `inst_difRep_Ugen_step_le` | `L = 4`, `g = 1/64`, `E = 1/2`, `k = 3`, `σ3`, `u = 0`, `Δ = 1/128`, `A ≡ 1`, `M = 1` | none |
| `difRep_flow_bounds` | `inst_difRep_flow_bounds` | `κ = 1/10`, `flow_z0`, `n = 0`, `u = 1/16` (`sixteenth_le_lemT`) | none |
| `gridRepRemN_holds` | `inst_gridRepRemN`, `example`s at `m = 2`, `m = 3` | `d = 3`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `sz0`, `z0`, `flow_z0`, `sInst`, `tInst`, `K n = ⌈N^CK⌉₊ + 1`, both clauses | none |
| `stGridRepNAt_of_parts` | `example` (`m = 3`, `C₀ = 12`) | clauses (i)-(ii) from `gridRepRemN_holds` | `GridRepTailNAt 3 3`, `GridRepWTailNAt 3 3` |
| `stGridRepN_of_tails` | `example : STGridRepN 3` | `d = 3` | the two tails, `∀ m ≥ 2` |
| `stGridMartAt_of_parts2` | `example` (`C₀ = 11`) | `gridRepRemN_holds 3 _ 2` | `GridRepTailNAt 3 2` |
| `stGridMart_of_tail` | `example : STGridMart 3` | `d = 3` | `GridRepTailNAt 3 2` |
| chain | 3 `example`s to `STStep2 3` (`ST_step2_of_pinsN'`, `ST_step2_of_pins'`) and to `STStep2Concl` at `(sz0, z0, 0, 1/16)` (`inst_step2`) | | `STNewKLK`, `STLWT`, `STEMn2Exp`, `STOptL2`, `STLocalAvgOfL2`, the tails |

All instances compile, because the module builds (§4). None is degenerate:
- the window `[0, 1/16]` is not collapsed (`Δ = 1/64 > 0`);
- every index set is nonempty (`N ≥ 1`, `m ≥ 2`);
- no premise is `False`;
- every deterministic hypothesis is discharged (`by norm_num`, `flow_z0`, `sixteenth_le_lemT`, `hs0/hst/htT`).

The hypotheses left in the instances are only other gates' pins (CLAUDE.md §4 step 2). `K n = ⌈N^{8m+20}⌉ + 1` is the grid that the pin's `∀ K, N^CK ≤ K` requires, and the ticket prescribes it. It is not a witness chosen to be large. This covers every instance the ticket lists.

## 6. Paper-delta coverage

The prove report §(d) proposes:
- T2168a: `Rem`/`Mart` are the grid device, and `Mart` is the full martingale including the second-order part;
- T2168b: `C₀ = m + 9`, `CK = 8m + 20`, `d`-free;
- T2168c: the identity holds pathwise for every `k`;
- T2168d: `3 ≤ d` through `STKbound` (D263, §36);
- T2168e: `STGridRepN`/`STGridMart` are conditional on the owed tails;
- T2168f: an observation.

This covers every expected candidate in the ticket. The audit found no Lean/paper statement difference without a candidate.

## 7. Observations (no effect on verdict)

- O1. `Reg.lean` (only `RBM3D.Path.DifREP1` + `RBM3D.Test.Axioms`, without the root) lists 15 unregistered premises (`STNewKLK`, `STLocalAvgOfL2`, `STEMn2Exp`, …). None is a T2168 name. They are certified by theorems outside this module's import closure. With `import RBM3D` (Reg2, §4) the check exits 0.
- O2. The public instance helpers `hs0`, `hst`, `htT`, `gridStep_inst`, `σ3`, `ω0` live in the file-stem namespace `RBM.Ind.DifREP1Inst`, which has 0 hits on `main`. That namespace is consistent with §3 (E).
- O3. The prove report's line 1 is `Prover model: claude-sonnet-5-5` (role `prover-hard`). The report is 218 lines, within 300.

## 8. Verdict

| target | verdict |
|---|---|
| 1 vocabulary (`difRepMartN`, `difRepRemN`, `GridRepRemNAt`, `GridRepTailNAt`, `GridRepWTailNAt`) | PASS |
| 2 `difRep_identity`, `difRepMartN_succ_sub` | PASS |
| 3 `difRep_Ugen_step_le`, `difRep_flow_bounds` | PASS |
| 4 `gridRepRemN_holds` (`C₀ = m + 9`) | PASS |
| 5 `stGridRepNAt_of_parts`, `stGridRepN_of_tails`, `stGridMartAt_of_parts2`, `stGridMart_of_tail` | PASS (conditional on the owed tails, as pinned) |

**Ticket verdict: PASS.** Dispatcher sign-off is not needed. The hub runs the full `lake build` with the root import at merge.
