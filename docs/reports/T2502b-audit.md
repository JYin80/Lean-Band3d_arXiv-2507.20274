Auditor model: claude-opus-5-5

# T2502 row b (V1s1b: `Chain/ExpHierGen`, `Chain/ExpDuhamelGen`; targets 10-13) — audit round 1

Written Wed Oct 14 08:23:00 UTC 2026 (`date -u`). Branch `t/T2502b` at 94db77fa; audit worktree `RBM3D-wt/T2502b-audit1` (detached).
Inputs: `docs/tickets/T2502.md`, `docs/tickets/T2502-amend-1.md` (row b: "keeps row 9 as written"), check `docs/tickets/checks/T2502-check.lean`,
`docs/reports/T2502b-prove.md`. Scratch: `<scratchpad>/T2502b/audit_pins.lean` (uncommitted; check text + auditor examples).

## Verdict: PASS (targets 10, 11, 12, 13)

## 1. Build, diff, hygiene (audit worktree)
```
$ lake build RBM3D.Chain.ExpHierGen RBM3D.Chain.ExpDuhamelGen > build.out 2>&1; echo "exit $?"; tail -1 build.out; grep -c "^error" build.out
exit 0
Build completed successfully (3879 jobs).
0
$ ls -la .lake/build/lib/lean/RBM3D/Chain/ExpHierGen.olean      # fresh build in this worktree (01:17 PDT = 08:17 UTC)
-rw-r--r--@ 1 junyin  staff  1751304 Oct 14 01:17 .lake/build/lib/lean/RBM3D/Chain/ExpHierGen.olean
$ lake build RBM3D > full.out 2>&1; echo "exit $?"; tail -1 full.out; grep -E "axiom audit|premises found" full.out
exit 0
Build completed successfully (4387 jobs).
info: RBM3D.lean:617:0: axiom audit: 15194 theorems, 4696 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 144 (borrowed 1, owed 65, structural 58, refuted 6, superseded 14).
$ git diff main...t/T2502b --name-only
RBM3D.lean
RBM3D/Chain/ExpDuhamelGen.lean
RBM3D/Chain/ExpHierGen.lean
$ git diff main...t/T2502b -- RBM3D.lean | grep "^[+-]"
+import RBM3D.Chain.ExpHierGen
+import RBM3D.Chain.ExpDuhamelGen
$ grep -n "ExpHierGen\|ExpDuhamelGen\|assert_rbm" RBM3D.lean      # after the last import line; assert stays last
613:import RBM3D.Chain.ExpHierGen
614:import RBM3D.Chain.ExpDuhamelGen
617:#assert_rbm_axioms
$ git diff main...t/T2502b --name-only -- RBM3D/Induction RBM3D/Graph RBM3D/BA RBM3D/Gauss RBM3D/Evolution RBM3D/Test | wc -l
       0
$ grep -nE "\bsorry\b|\badmit\b|^\s*axiom|native_decide" <new files> | wc -l
       0
$ grep -nE "^(noncomputable )?(def|abbrev|structure|instance) " <new files> | wc -l     # X1-C4: rows b, c add no def
       0
$ import closure of the two new modules (script); forbidden = BA.*, Chain.Step2Kern, Q*/Qt*, Step3/4, Iterations*, BALWOut, LWPinsBA
closure size 177
forbidden []
$ git grep -n "Chain.ExpHierGen\|Chain.ExpDuhamelGen" -- RBM3D RBM3D.lean | cut -d: -f1 | sort -u     # importers
RBM3D.lean
RBM3D/Chain/ExpDuhamelGen.lean
$ C1 / X1-C1 / TN-C4 regex over every public `theorem` signature (mE, zt E, |E|, etaT, mSigma, seqHflow, withLam, STGridRepNgL, lemT, STFlow, Ugen, ThetaN d, STthetaOp)
(no hits)
```
Sole writable files of row b: `Chain/ExpHierGen.lean`, `Chain/ExpDuhamelGen.lean` (new), `RBM3D.lean` (import lines). The diff touches only these.
No registry edit; the scan count is unchanged (144), so row b has no scan hit of its own (ticket "Registry").

## 2. Statements against the pins (auditor scratch file, compiled)
`audit_pins.lean` = `import RBM3D.Chain.ExpDuhamelGen` + `import RBM3D.BA.Step2BA` + the check text verbatim + the block below.
```
-- (P1) example ... : T2502_ExpHierAtOf Cm μ H₀ g' E n := stExpHiergL_at Cm μ H₀ g' E n
-- (P2) example ... : T2502_ExpDuhamelZAtOf C μ n := stExpDuhamelZgL_at C μ n
-- (P3) example ... : Step2Gen_USemigroup C n → T2502_ExpHierAtgL C μ n → T2502_ExpDuhamelQAtgL C μ n := stExpDuhamelQgL_at C μ n
-- (P4) T2502_ExpHierAtgL = STExpHierAtgL, T2502_ExpDuhamelZAtgL = STExpDuhamelZAtgL, T2502_ExpDuhamelQAtgL = STExpDuhamelQAtgL,
--      T2502_ExpDuhamelZgL = STExpDuhamelZgL, STExpDuhamelQgL = (∀ sz κ ε 𝔠 𝔡 z, 0 < κ → Flow … → ∀ᶠ n, T2502_ExpDuhamelQAtgL …),
--      T2502_ExpDuhEqgL = STExpDuhEqgL  : all `rfl`
-- (P5) #check fun {d} law Flow mk mkM hmk hrep hcls hU =>
--        (stExpDuhamelZgL_ev (d := d) law Flow mk mkM hmk hrep hcls hU : T2502_ExpDuhamelZgL d law Flow mk)
-- (P6) example (sz : Sizes d) (z) : (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).toFlowFM = baFMz sz z := rfl
-- (P7) ExpHierGen_Kloop_hasDerivAt and ExpHierGen_hierarchy_two applied at bandStep2Mat sz0 (1/2), n = 0, u = 1/2, M = 0,
--      σ = (+,-), a = (0, e₁), every hypothesis by the band theorems (hierDriftGen_k*_band, stepDecompGen_loopForm_band, rfl)
$ lake env lean audit_pins.lean > pins.out 2>&1; echo "exit $?"; grep -c "error" pins.out
exit 0
0
```
| target | Lean | pin / ticket text | result |
|---|---|---|---|
| 10 | private `ExpHierGen_Good_*`, `ExpHierGen_genMat_eq_cuts`, `ExpHierGen_hasDerivAt_integral` (W2 at Hermitian `M₀`, `ztOf`) | private by the ticket | internal; feeds 12 |
| 11 | `ExpHierGen_Kloop_hasDerivAt`, `ExpHierGen_continuousOn_K`, `ExpHierGen_hierarchy_two`, private `ExpHierGen_hierarchyNg_at` | per index `n`; premises `KLoop`, `KTwo`, `KLink` at `n`, `LoopForm`, `S n = SB d L (g n)` | no `∀ n` premise; matches |
| 12 | `stExpHiergL_at` | `T2502_ExpHierAtOf` (P1), head `T2502_ExpHierAtgL` (P4) | equal |
| 12 | `stExpHiergL_ev` | ticket: `∀ᶠ n` under the family table rows 9-12 | see §3 |
| 12 | `stExpHier_of_gL : STExpHier d` | band re-derivation (`H₀ = 0`, `g' = sz.lam`) | as required |
| 13 | `stExpDuhamelZgL_at`, `stExpDuhamelQgL_at` | `T2502_ExpDuhamelZAtOf` (P2); Q form at the pin texts (P3) | equal |
| 13 | `stExpDuhamelZgL_ev`, `stExpDuhamelQgL_ev` | conclusions `STExpDuhamelZgL` = `T2502_ExpDuhamelZgL` (P4, P5), `STExpDuhamelQgL` = Q twin (P4) | equal |
| 13 | `stExpDuhamelZ_of_gL`, `stExpDuhamelQ_of_gL` | band re-derivations of `STExpDuhamelZ/Q d` | as required |
`T2502_ExpDuhEqgL` (row a text, row b proof): `ExpDuhamelGen.lean:570` derives `STExpDuhEqgL` (= the pin, P4) from `stExpDuhamelZgL_ev_inst`
through row a's merged `st6_duhEq_of_ping`; the chain compiles.
Zero mode: the pin applies `zeroModeSet` outside `Step2Gen_UN`; the proof (`ExpDuhamelGen.lean:279-304`) uses `zeroModeSet_add` and linearity
only; no commutation of `zeroModeSet` with `Step2Gen_UN` is stated or used.

## 3. Hidden hypotheses, vacuity, cycles
- 0 new `def`/`structure`: no hypothesis can sit in a new structure field. The premises are merged classes (`CltRepg`, `StepDecompGen_LoopForm`,
  `HierDriftGen_KLoop/KTwo/KLink`, `Step2Gen_USemigroup`), all listed in the ticket's family table (rows 9-13). C1 tokens: 0 hits (§1).
- Family premises of the `_ev` theorems against the table: `hrep` = rows 9 + 10 in one guarded `∃ H₀ g' E` (shared `E`; amend-1 keeps row 9
  as written); `hcls` = rows 11, 12 as `∀ᶠ n` (guarded); `hU` = row 13 as `∀ᶠ n` (guarded); no `∀ n` hierarchy/drift premise; no `∃` constant
  after `(sz, z)`. Named BA discharges, by grep of the merged signatures:
```
BA/CltFlowBA.lean:316  baCltRepg_holds : CltRepg (baFMz sz z) (Sizes.seqP (sz.withLam 0)) (fun n => (λ₀ : ℂ) • PsiI …) (fun _ => 0) (BAflowEs sz z)
BA/SEforLnBA.lean:135  baStep2Mat_loopForm : … BAFlow … → StepDecompGen_LoopForm (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (BAflowEs sz z)
BA/GridDriftBA.lean:631 baHierDrift_classes : (∀ n, HierDriftGen_KLink (baStep2Mat …) n) ∧ ∀ᶠ n in atTop, HierDriftGen_KLoop … ∧ HierDriftGen_KTwo … ∧ …
BA/Step5KerBA.lean:161 baIniTermGen_kerFacts (row 13 owner, first conjunct per the ticket)
```
  The `E` of `CltRepg` and of `LoopForm` is the same `BAflowEs sz z` at BA, so the shared-`E` packaging of `hrep` is dischargeable.
- No cycle: the new modules import only merged modules (§1 closure); `ExpDuhamelGen` imports `ExpHierGen`, nothing imports either except `RBM3D.lean`.
- No external hypothesis is introduced (all premises are merged carrier classes with merged BA producers), so no limit check is required.

## 4. Compiled nonempty instances (in the files; build §1 compiles them)
| endpoint | instance (file:line) | data | hypotheses |
|---|---|---|---|
| `stExpHiergL_at` | `stExpHiergL_at_inst` `ExpHierGen:844`; derivative at `u = 1/2` `:851` | `d = 3`, `sz0`, `n = 0` (`L = 4`, `W = 32`, `lam = 1/64`), band carrier `E = 1/2`, `H₀ = 0`, `g' = sz0.lam` | all six discharged by merged band theorems |
| `stExpHiergL_ev` | `stExpHiergL_ev_inst` `:857`, applied at `sz0` `:867` | band tuple, `Flow = True` | `hmk` rfl, `hrep`, `hcls` discharged |
| `stExpHier_of_gL` | `:871` | `sz0`, `n = 0`, `E = 1/2` | `|E| < 2` by `norm_num` |
| W2 core (target 10) | `:877` | `M₀ = 1` (nonzero Hermitian), `m = i`, `L = 4`, `W = 32`, `u = 1/2` | discharged |
| `stExpDuhamelZgL_at` | `stExpDuhamelZgL_at_inst` `ExpDuhamelGen:507`; applied at `[1/4,1/2]`, `A = univ` `:514` | as above | `step2Gen_USemigroup_band`, `stExpHiergL_at_inst` |
| `stExpDuhamelQgL_at` | `stExpDuhamelQgL_at_inst` `:510`; applied with a mollifier from `stMollifierEx_holds` `:529` | as above | discharged |
| `stExpDuhamelZ/QgL_ev` | `:547`, `:558`; `:570` (consumer `STExpDuhEqgL`), `:574` | band tuple, `Flow = True` | `hmk`, `hrep`, `hcls`, `hU` discharged |
| `stExpDuhamelZ/Q_of_gL` | `:578` at `d = 3` | — | none |
No `N = 0`, empty index set, collapsed window (`1/4 < 1/2 < 1`) or `False` premise; `Flow = True` is the family parameter, not a premise.

## 5. Axioms
```
$ (in audit_pins.lean) #print axioms of the 12 target theorems and the 6 named instances; grep -o "depends on axioms: .*" pins.out | sort | uniq -c
  18 depends on axioms: [propext, Classical.choice, Quot.sound]
```
Full build: "0 axioms in `RBM`" (§1).

## 6. Paper deltas
Lean vs paper differences of row b: (i) `H₀ ≠ 0` generalization of the hierarchy/Duhamel at the carrier (paper `6:12-21`, "same as [YY_25]");
(ii) the eventual-in-`n` family forms `STExpDuhamelZgL/QgL`, `STExpDuhEqgL` (paper: every `n`). Both are covered by the existing entry
`docs/paper-deltas.md:1808` **D725** ← `T2502a` (eventual form, UP-C4; `H₀ ≠ 0` covered by `6:12-21`). Row b adds no further statement
difference (targets 12, 13 equal the dispatcher pins; P1-P5). The prove report's "no candidate" is consistent.

## 7. Observations (no statement, instance, build, axiom or delta effect)
- O1. Target-11 public theorems `ExpHierGen_Kloop_hasDerivAt`, `ExpHierGen_continuousOn_K`, `ExpHierGen_hierarchy_two` have no `example` of
  their own in the file; they are intermediate (consumed by private `ExpHierGen_hasDerivAt_fixed`, `:638`, `:650`, and by `stExpHiergL_at`
  `:779`), and the pin endpoints of target 12 carry instances. The auditor's P7 applies them at `sz0`, `n = 0`, `u = 1/2`, `M = 0` with every
  hypothesis discharged; it compiles. Not a RETURN.
- O2. `hmk : ∀ sz z, (mkM sz z).toFlowFM = mk sz z` is unguarded (table row 10 lists it under the guard): a stronger premise, met by `rfl` at
  the BA tuple for every `z` (P6) and at the band tuple (`fun _ _ => rfl` in the instances).
- O3. `ExpHierGen_hierarchy_two` is stated for `0 < u < 1` (band `expHier_hierarchy_two` has `0 ≤ u`); no pin is affected (the pin's
  derivative clause is on `Ioo 0 1`).
- O4. The ticket text of target 13 ("`zeroModeSet` commutes with `Step2Gen_UN`") is not used; the pinned form needs only linearity (§2).
  The prove report flags this as a dispatcher text fix; it is not a Lean/paper statement difference.
- O5. The carrier instances are at `H₀ = 0` (band); a carrier with `H₀ ≠ 0` is BA's and BA is not importable here (ticket layering);
  the W2 core has a compiled instance at `M₀ = 1`.
- O6. The prove report has 291 lines: within CLAUDE.md §6 (300) but over the ticket's "≤ 250" acceptance line. Report-only defect.
