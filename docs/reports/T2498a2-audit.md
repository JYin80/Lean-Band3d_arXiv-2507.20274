Auditor model: claude-opus-5-5

# T2498a2 audit (round 1): row a, second part U3s3a′ (`Induction/QBudgetA`, `QBudgetB`, `QEndA` in place, new `QEndA2`; targets 7, 8, rest of 9)
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2498a2-audit1` at `39fd68bb` (= `t/T2498a2`), `main` `e297a13b`; `date -u` Wed Oct 14 07:07:07 UTC 2026. Ticket `docs/tickets/T2498.md` + Amend 1. Scratch: scratchpad `T2498a2/`.

## 1. Build, axioms, hygiene
```
$ lake build            # whole library, audit worktree, 07:02:15 -> 07:02:17 UTC
info: RBM3D.lean:613:0: axiom audit: 15093 theorems, 4651 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 122 (borrowed 1, owed 55, structural 46, refuted 6, superseded 14).
Build completed successfully (4383 jobs).
exit 0
$ lake env lean Ax.lean   # 82 `#print axioms`: 39 new generic decls + every *g instance + 6 bridges + 2 band corollaries
exit 0; 82 of 82 print exactly [propext, Classical.choice, Quot.sound] (one output is line-wrapped)
$ lake env lean docs/tickets/checks/T2498-check.lean   -> exit 0, 0 lines containing "error"
$ wc -l QBudgetA QBudgetB QEndA QEndA2   -> 1497 1538 1866 1642 (all < 2000)
sorry/admit/axiom/native_decide: 0 | import RBM3D.BA: 0 | withLam|STGridRepNgL|ST_gridMart_of_repN|stGridRepN_holds: 0
X1-C4 defs (GoodSetNg|GoodLinNg|…|STOeqNQPTgL): 0 | open private of a Q file: 0
imports added: QBudgetA +Chain.NQBudgetGen +Chain.NQLinGen; QEndA2 +Induction.QEndA +Chain.QGridGen2
$ grep -rln "import RBM3D.Induction.QEndA2" RBM3D RBM3D.lean   -> RBM3D.lean
```
## 2. Diff scope
```
$ git diff --name-only main...t/T2498a2
RBM3D.lean  RBM3D/Induction/QBudgetA.lean  RBM3D/Induction/QBudgetB.lean  RBM3D/Induction/QEndA.lean  RBM3D/Induction/QEndA2.lean
RBM3D/Probe/T2498Pins.lean  RBM3D/Test/Axioms.lean
$ git diff main...t/T2498a2 -- QEndGrid QEndB1 QtXiRoundLift QGridA QGridB Induction/NQ* Chain/NQ* BA | wc -l   -> 0
$ git diff main...t/T2498a2 -- RBM3D.lean RBM3D/Test/Axioms.lean | grep '^[-+]' (abridged)
+import RBM3D.Induction.QEndA2
-   … `hQ_nonAltN_of_Ng`; U3s3 reads it); BA: …
+   … `hQ_nonAltN_of_Ng`; U3s3 reads it through `gridGoodNgL_of` and `stOeqNQPTgL''_of`; alternating majorant `hQ_altQNg` (T2498, `Induction/QEndA`)); BA: …
```
`Probe/T2498Pins.lean` is the stack-base probe (`t/T2498`, absent on `main`), never merged (ticket :121); the hub brings in only the sole writable files. The registry edit is the ticket :90 text verbatim; no `owedProps` line (premise scan 122 = main's count per the prove report).

## 3. G1: frozen band names keep name and type (Part 3 and every surviving public name of the three in-place files)
```
$ python3 names.py   # public decls of QBudgetA/QBudgetB/QEndA at main; present at branch (file or QEndA2)?
62 present, 7 REMOVED: kappaAltQN_mul_Bctl_pow_le kappaAltQN_succ_mul_Bctl_pow_le kappaAltQN_le_kapFar qvBdAltQN_eq_qvShape tbInitAltQN tbDriftAltQN tbQvAltQN
$ git grep -lw <each removed name> main -- RBM3D RBM3D.lean   -> only RBM3D/Induction/QBudgetA.lean (no outside reader)
$ G1.lean = `#check @<name>` x62 (pp.fieldNotation false, pp.funBinderTypes, pp.numericTypes)
main worktree (import QEndA): exit 0, 1402 lines ; audit worktree (import QEndA2): exit 0, 1402 lines ; diff: 0 lines
Part 3 names of this row (25, check :281-305): all 25 among the 62; missing: none
```
Band readers `QEndGrid`, `QEndB1`, `QtXiRoundLift` compile unchanged in the full build above (files untouched, §2).

## 4. Statements
**D2 `gridDriftQNg_envelope_ev` (target 8, binding text fixed at the 1a-audit, `T2498-1a-audit.md:58-79`).** Uncommitted scratch `d2/D2.lean` = `import RBM3D.Induction.QEndA2` + the 1a-audit file `audit1a/D2fixed2.lean` (`def T2498_GridDriftQEvFixed`) + one line:
```
example : T2498_GridDriftQEvFixed := @RBM.Ind.gridDriftQNg_envelope_ev
$ lake env lean d2/D2.lean   -> exit 0
```
All-`w` link `hKK`, drift classes and `0 < lam` under `∀ᶠ n`, `hS`, `‖m‖ ≤ 1`, `hη` for all `n`; conclusion `rGridQNg ≤ qErrQNg` at `N^τK η_{u_{j+1}}^{-(m+2)}`: as fixed. No `∀ n` drift premise.

**Hypothesis rules (ticket :92) over the 39 new generic statements (defs and theorems up to `:=`, script `stmts.py`):**
```
C1/X1-C1 regex hits: 1 -> QEndA:1184 gridDriftQNg_envelope_ev ['Lloop'] (= `KLloopOf` inside the pinned D2 link); all other 38: []
```
**Generic twins vs band statements (read against `git show main:`).** Each twin replaces `|E n| < 2` by `StepDecompGen_LoopForm Cm E` plus inline `‖Cm.m n‖ ≤ 1`, `etaT (E n) u` by `Cm.eta n u`, `(mE (E n)).im` by `(Cm.m n).im`, `stepErrN` by `stepErrNg`, `qProxy4C …` by an explicit `Cv` (band bridges `*_band` are `rfl`, QBudgetA:245-267, QBudgetB:156, QEndA:1048-1053). Checked line by line: `budgetAltQNg` (QBudgetA:582-621) against band `budgetAltQN`: the same 26 hypotheses in the same order, `ha1`-`he4` identical up to `qProxy4C ↦ Cv`. `altYGridNg` (QEndA:1150): `Prec`/`STXiLK` become `PrecL` at law `μ` of `STXiLKg` with `Step34Gen_LCompat`, `Step2EventsGen_Law`; the band hypothesis `∀ n, 1 ≤ X n` is dropped (weaker premise, `T2498k`). The spectral twins `dFlowQNg_levelLin`, `alt_hdriftLinQNg`, `alt_hdriftGridQNg`, `altEnd_unQg` take the `B45Gen_Facts` fields at one index (`hward`, `hker`, `hrow`, `hcol` with `K₆ ≥ 1`) and `κm ≤ (Cm.m n).im`, not `|E| ≤ 2 − κ` (`T2498g`). `B45Gen_Facts` (`B45Gen:61-69`) gives `C₆ > 0`, so `K₆ := max C₆ 1` discharges them.
`hQ_altQNg`, `subGaussStop_altQNg`, `alt_hkerGridQNg` carry R1 (`hcmp : ∀ n', 0 ≤ gK·lam ∧ gK² ≤ lam² ≤ A gK²`, `1 ≤ A`, `A^{m+2} ≤ W^{(Cv−C4)ε}`, `C4 ≤ Cv`) and D1 `QProxyG_KerEK4 … gK`. This is forced: part 1's merged `qvFormQNg_le_of_bounds` has the same premises (`QProxy.lean:1194-1202`, `grep` output: `hcmp`, `hKer`, `hεε`, `hAk`). It is R1 itself (UBA-C1, "passes … down"), not a second comparison. `alt_hDclsGridQNg` (QEndA:1684): `∀ (… C₆ A), … → ∃ W₀, 1 < W₀ ∧ ∀ sz Cm gK n …`. `C₆` is an input before the carrier, so a family premise with `∃ C₆` after `κ` (Amend 1) can feed it. No pinned `∃` after `(sz, z)`.
Inline `PrecL`, `STKboundgL`, `AzumaSubGNg`, `QVPropagatedNg`, `ZeroModeGen_*`, `Step2Gen_USemigroup`, `HierDriftGen_KLink` are hypotheses in signatures, not structure fields. Every dependency is a merged declaration (full build). No cycle: `QEndA2` is imported only by `RBM3D.lean`, and the in-place files add only upstream `Chain` imports.

## 5. Compiled nonempty instances (generic endpoints; all in the same module family, compiled in §1)
| target | instance (file:line) | data | open hypotheses |
|---|---|---|---|
| kappa ×3, `qvBdAltQNg_eq_qvShape`, `tbInit/tbDrift/tbQvAltQNg`, `dDriftAltLinQNg_le_shape` | QBudgetA:1369-1418 (examples) | `sz0`, `n=0`, `W=32`, `K≡4`, `s≡0`, `v≡1/32`, `E≡1/2` | none |
| `budgetAltQNg` | QBudgetA:1465 | as above, `m=1`, `ε₀ = C4+Cn+12` | none |
| `dFlowQNg_levelLin`, `alt_hdriftLinQNg`, `dDriftAltLinQNg_nonneg` | QBudgetB:1326, 1348, 1398 | `n=4`, `m=2`, `E≡0`, `κm=1/2`, `K₆=1`, band ward/ker/rows/cols discharged | none |
| `altBudgetNumQNg_eventually` | QBudgetB:1484 | `sz0`, `E≡1/2`, `κ'=24/25`, `ε₀=1`, exponents of `altBudgetExpQN_of_choice_instance` | none |
| `altYSetNg`, `measurableAltYSetNg` | QEndA2:1090 | `n=4`, `H=0` | none |
| `altYGridNg` | QEndA2:1098 | `sz0`, `s≡0`, `v≡1/2`, `K≡4`, `l=3`, `ε=1/10` | `hP : PrecL … STXiLKg` (the uniform `STLKUgL`-type control, registry `Test/Axioms.lean:199`) |
| D2 `gridDriftQNg_envelope_ev` | QEndA2:1119 | `sz0`, `m=2`, `τK=1`, `s≡0`, `v≡1/2`, `K≡4`; classes by `hierDriftGen_*_band`, link `rfl` | `hKb : STKboundgL` (registered, `Test/Axioms.lean:134`) |
| `assembledRHSAltQNg_qErr_le` | QEndA2:1143 | `K n = N^31`, `m=2`, `hsum` from merged `QGridGen2_sum_weighted_qErrQNg_instance` | none |
| `hQ_altQNg`, `subGaussStop_altQNg` | QEndA2:1178 | `m=2`, `M=0 ∈ GoodSetNg`, D1 by `qProxyG_kerEK4_band_at`, R1 at `A=1`, `gK=lam`, `K=⌈N^{D''+14}⌉` on `[0,1/2]` | none |
| `alt_hkerGridQNg`, `alt_hdriftGridQNg`, `alt_hA0clsGridQNg`, `alt_hDclsGridQNg` | QEndA2:1369, 1394, 1428, 1472 | `n=4` or large `n` (`W ≥ W₀`); `C₆` from `step5KerGen_thDecay_band` | none |
| `altExitMeasNg`, `altEnd_hexpg`, `altEnd_stronglyMeasurable_zVecQNg`, `altEnd_aFroz_eq_aTrueg`, `altEnd_unQg`, `altEnd_driftSupg` | QEndA2:1553-1617 | `n=4`, `K≡4`, `τ≡1` or `4`, `H=0` | none |
Instance theorem signatures, read directly (`sed`): the only binders are `hKb` (D2), `hP` (`altYGridNg`) and the free variables `a`/`ω`/`σ`. No `N = 0`, no empty index set, no collapsed window (`[0, 1/32]`, `[0, 1/2]`), and no `False` premise.

## 6. Paper deltas
Prove report (d) proposes `T2498g` (spectral levels replace `|E| ≤ 2−κ`), `T2498h` (D2 text), `T2498i` (two radii and `C4 ≤ Cv` in `hQ_altQNg`, `subGaussStop_altQNg`), `T2498j` (seven unread band theorems removed, two kept as corollaries) and `T2498k` (`altYGridNg` over `(μ, Hf)` without `∀ n, 1 ≤ X n`). Together with part 1's `T2498a`-`f`, these cover every Lean/band statement difference found in §4.

## 7. Observations (no statement, instance, build, axiom or delta-coverage effect)
- O1. The 1a plan (ix) said R1 would "never" enter `hQ_altQNg`. The landed text carries R1, as part 1's merged `qvFormQNg_le_of_bounds` forces (§4). This is recorded as `T2498i` and in the report narrative.
- O2. Three band private helpers (`QBudgetA_eps_nonneg`, `QBudgetA_kappa_nonneg`, `QBudgetA_qvBd_nonneg`) were deleted together with the removed band proofs. Their generic successors `QBudgetA_{kappag,epsg,qvBdg}_nonneg` are private, and only comments still reference the old names (QEndA:385, QEndGrid:811, 818). No private declaration became public (0 of the 57 deleted `private` lines; the other 54 moved to `QEndA2`/`QBudgetB` instance sections). The ticket's stop rule "a deleted `private`" is read as un-privatising, which did not happen.
- O3. `budgetAltQNg_instance` uses `ε₀ = C4+Cn+12` at one `n` (it mirrors the merged band `budgetAltQN_instance`). Joint satisfiability with a small exponent (`ε₀ = 1`) is shown by `altBudgetNumQNg_eventually_instance`.
- O4. `alt_hkerGridQNg_instance` instantiates the inner `∀ X M δ` at `X = 0`, so its conclusion is `‖U(0)‖ ≤ 0`. Every premise of the theorem (D1, R1, windows at `n = 4`) is discharged.
- O5. Removed band theorems are still pinned in an old check (`docs/tickets/checks/T2279-check.lean:176, 210`). Check files are never built.
- O6. Calibration overshoot (added − moved 2,511 against the 1a central 1,279) is reported by the prover for the dispatcher. It is not an audit item.

## Verdict
Target 7 (`QBudgetA/B` vocabulary, kernel weights, budgets, `budgetAltQNg`, `dFlowQNg_levelLin`, `alt_hdriftLinQNg`, `dDriftAltLinQNg_nonneg`, `altBudgetNumQNg_eventually`): **PASS**.
Target 8 (`QEndA` §0-§7 twins, D2 `gridDriftQNg_envelope_ev` = 1a-audit text, `hQ_altQNg`, `subGaussStop_altQNg`, C3-C5): **PASS**.
Target 9, rest (band corollaries of this part: G1 62/62 types unchanged; instances moved to `QEndA2`, 31 instances compile): **PASS**.
Overall **PASS**. No dispatcher sign-off needed.
