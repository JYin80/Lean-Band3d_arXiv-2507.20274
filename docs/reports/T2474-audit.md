Auditor model: claude-opus-5-5
# T2474 audit (round 1) — ST T5s2: StepDecompGen, HierDriftGen

Audited: `t/T2474` at 662c05c2, worktree `RBM3D-wt/T2474-audit1` (merge-base 97341078); Mon Oct 12 22:27:21 UTC 2026; scratch `$S/{StmtAudit,Band8,Ax,Full}.lean` (not committed).

**Verdict: PASS (targets 1–12).** No dispatcher sign-off needed. Observations O1–O5 below change no statement, instance, build or axiom.

## 1. Build, axioms, hygiene, diff
```
$ lake build RBM3D.Chain.StepDecompGen RBM3D.Chain.HierDriftGen
Build completed successfully (3777 jobs).
$ lake build RBM3D                                   # branch root (new modules not yet imported)
Build completed successfully (4310 jobs).
$ printf 'import RBM3D\nimport RBM3D.Chain.HierDriftGen\n#assert_rbm_axioms\n' > Full.lean; lake env lean Full.lean; echo exit $?
exit 0
axiom audit: 13884 theorems, 4415 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
$ # Ax.lean: #print axioms of every public decl of the two files (114 names, extracted by grep)
$ lake env lean Ax.lean > ax.out; echo exit $?; grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" ax.out; grep -vc ... ax.out
exit 0
114
0
$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Chain/StepDecompGen.lean RBM3D/Chain/HierDriftGen.lean
RBM3D/Chain/StepDecompGen.lean:0
RBM3D/Chain/HierDriftGen.lean:0
$ git diff --name-only main...t/T2474
RBM3D/Chain/HierDriftGen.lean
RBM3D/Chain/StepDecompGen.lean
$ git diff main...t/T2474 -- RBM3D/Induction RBM3D/Chain/Step2Gen.lean RBM3D/Chain/Step2Kern.lean RBM3D/Chain/Carrier.lean RBM3D/Chain/GridDuhamelGen.lean RBM3D/BA RBM3D/Test | wc -l
       0
$ git diff main t/T2474 --stat -- <the six band files>      # also identical to current main (ae791953)
(empty)
$ wc -l RBM3D/Chain/StepDecompGen.lean RBM3D/Chain/HierDriftGen.lean ; ls RBM3D/Chain/HierDriftGen2.lean     -> 1246, 1381
ls: RBM3D/Chain/HierDriftGen2.lean: No such file or directory
```
Both files are below the binding stop line 2,000; reserve not used (1,381 ≤ 1,800). `RBM3D.lean` is not touched on the branch (hub adds the two imports).

## 2. Statements against the pins (check file `T2474-check.lean`)
`StmtAudit.lean` = the whole check file (Parts 1–3, verbatim) + `import RBM3D.Chain.HierDriftGen` + the examples below.
```
$ lake env lean $S/StmtAudit.lean > stmt.out; echo exit $?; grep -c error stmt.out; grep -c "^example" StmtAudit.lean
exit 0
0
50          # 20 from the check file + 30 added by the auditor
```
(A) classes and pinned conclusions, each `example … : T2474_X … ↔ <Lean name> … := Iff.rfl` compiles:
`T2474_LoopForm ↔ StepDecompGen_LoopForm`, `T2474_WalkForm ↔ StepDecompGen_WalkForm`, `T2474_HermLoopOf ↔ HermTestFunLoopNOf`,
`T2474_QVg ↔ QVPropagatedNg`, `T2474_SubGaussFormNg ↔ SubGaussFormNg`, `T2474_SubGaussStopNg ↔ SubGaussStopNg`, `T2474_KLoop ↔ HierDriftGen_KLoop`,
`T2474_KTwo ↔ HierDriftGen_KTwo`, `T2474_HierarchyNg ↔ HierarchyNg`, `T2474_GridDriftNg ↔ GridDriftNg`, `T2474_Expand ↔ HierDriftGen_Expand`,
`T2474_UStep ↔ HierDriftGen_UStep` (12/12).
(B) generic results at the check shapes (each an `example : <shape> := fun … => <name> …`):
```
T2474_HermLoopOf                                                := hermTestFunLoopNOf
LoopForm → (∀ n, Cm.S n = SB d (sz.L n) (g n)) → T2474_QVg       := qvPropagatedNg
KLoop → KTwo → T2474_LoopDrift                                  := loopDrift_sub_K_deriv_ng
LoopForm → S = SB → (∀n KLoop) → (∀n KTwo) → T2474_HierarchyNg   := hierarchyNg_of
9 (b): check shape + (∀ n, KI ∘ KLloopOf = K on [0,1)) → T2474_GridDriftNg := gridDriftNg      (extra premise: O2)
target 10 window shape (verbatim)                               := exists_norm_KI_le_wing
target 10 envelope shape (verbatim)                             := HierDriftGen_exists_envelope
```
(C) band routes / discharges: `HermTestFunLoopN sz := hermTestFunLoopN_of_Of`, `QVPropagatedN d := qvPropagatedN_of_Ng`,
`HierarchyN d := hierarchyN_of_Ng`, `GridDriftN sz E s t K := hierDriftGen_band_gridDriftN` (implies the check's target-8 band shape),
`(∀n,|E n|<2) → T2474_LoopForm (bandStep2Mat sz E) E`, `T2474_WalkForm (bandStep2Mat sz E) sz.lam 0`, `KLoop ∧ KTwo ∧ UStep` at band,
`T2474_Expand` at band, the check's `ZvecN` bridge (via `bandStep2_ZvecN`), and target 4's `martIncNg = ZvecNg + YvecNg`, `ZvecNg = dirDerivN …` (`rfl`).
Target 8 forward band direction at general `sz, E` (`Band8.lean`):
```
$ lake env lean $S/Band8.lean; echo exit $?     # (∀ n, |E n| < 2) → GridDriftNg (bandStep2Mat sz E) s t K := gridDriftNg (band discharges)
exit 0
```
Target 5 (no `T2474_*` pin; ticket mathematics): the six generic theorems (`ZvecNg_eq_stepZCN` S:802, `UN_stepZCNg` S:812, `martIncNg_eq_stepXiCN` S:842,
`YvecNg_eq_stepYCN` S:889, `UN_stepYCNg` S:902, `subGaussStopNg_zvecNg` S:941) are the band statements (`StepDecompN:1150-1317`) with
`pathP sz`/`pathH sz`/`Ugen`/`uKer`-product read as `pathP (sz.withLam lam')`/`Ψ n + pathH (sz.withLam lam')` (inside `loopFamNgShift`)/`Step2Gen_UN`/
`Step2Gen_uKer`-product, and `|E n| < 2` replaced by `LoopForm`, `WalkForm`; hypotheses `hst, ht1, hj` kept, `hs0 : 0 ≤ s n` dropped (weaker premise,
stronger theorem). Quantifier order and `∀ᵐ ω ∂Cm.Pp` placement as in the band. Matches.
`HierDriftGen_UStep` first field vs T2471's K3 (`T2471-check.lean:215-216`): identical text (read side by side).
`BA` reading of the extra premise: `baStep2Mat … .KI n u (KLloopOf σ a) = BAKloop …` (`BA/Step2BA.lean:89-91`, `rfl`) and
`baFM … .K := fun n t σ a => BAKloop …` (`BA/FlowPins.lean:324`): the premise holds by `rfl` at BA as at band.

## 3. Vacuity, hidden hypotheses, cycles
- Classes are `def … : Prop` (no structure fields); each has a band discharge theorem in these files (`stepDecompGen_loopForm_band` S:459,
  `_walkForm_band` S:465, `hierDriftGen_kLoop_band` H:387, `_kTwo_band` H:394, `_expand_band` H:1197, `_uStep_band` H:1182, `_kLink_band` H:682),
  all used in the compiled instances below, so no class is vacuous at the band.
- New modules import only `Chain.GridDuhamelGen`, `Induction.StepDecompN` (S) and `Chain.StepDecompGen`, `Induction.GridDriftN` (H): merged
  modules, no cycle.
```
$ grep -n '^import RBM3D.BA' RBM3D/Chain/StepDecompGen.lean RBM3D/Chain/HierDriftGen*.lean
(no output)
$ grep -rln "RBM3D.Chain.StepDecompGen\|RBM3D.Chain.HierDriftGen" RBM3D RBM3D.lean
RBM3D/Chain/HierDriftGen.lean
$ grep -c STGridRepNgL <new files>      -> 0, 0        (TN-C4)
$ grep -c NetLift <new files>           -> 0, 0
```
- External hypothesis: only `STKboundgL` (registered, `Test/Axioms.lean:134`), left as a hypothesis of the target-10 instance; limit check in
  1a row 10 (k = 1, 2 at n = 0, 5, 500). The `#assert_rbm_axioms` premise scan passes with both modules loaded (§1).
- X1-C1 (`grep -nE "\bmE\b|zt E|…|withLam"`, hits attributed to the enclosing declaration by an awk script): in generic declarations every hit is
  `withLam` (WalkForm, the shifted walk of target 5, `StepDecompGen_pathH`), `SB d`/`gvarF` (the accepted variance premise, targets 3, 7; §276 (4)),
  or a docstring. Remaining hits are in band bridges/discharges/re-derivations, the copied band helper `HierDriftGen_sum_norm_uKer_sub_one`, and the
  instances. Example residual lines checked by hand: S:746/766/854 (`StepDecompGen_pathH sz lam'`), H:785 (same), S:85/120/458/518, H:386/456/676 (docstrings).
- U-C4: no matrix/tensor-valued kernel among the `def`/`abbrev`s (`loopFamNg`, `ZvecNg`, … are vectors/families; `StepDecompGen_pathH` is the walk).
- Name clash (114 public names, `git grep -w` outside the two new files):
```
main: 0 hits    t/T2475: 0 hits    (t/T2473, t/T2476, t/T2477: no branch)
```

## 4. Compiled nonempty instances (in the files; built in §1)
Data: `d = 3`, `sz0` (`L_0 = 4`, `W_0 = 32`, `size = 2097152`), band carrier `E ≡ 0` (`Im m = 1`), `Ψ = 0`, `lam' = sz0.lam`, `s ≡ 0`, `t ≡ 1/2`,
`K ≡ 4` (`Δ = 1/8`), `k = 3`, `σ = (+,-,+)`, steps `j = 0` and `j = 1` (random `H_1`). Nondegenerate (no `N = 0`, window nonempty, `K ≠ 0`).
```
StepDecompGen  S:1159 hermTestFunLoopNOf_instance (non-band m = 3/10 + i/2, E = 1/5, u = 1/2)   S:1175 qvPropagatedNg   S:1179 StepDecompGen_hermLoop
               S:1182-1204 ZvecNg_eq_stepZCN, martIncNg_eq_stepXiCN, YvecNg_eq_stepYCN, UN_stepZCNg, UN_stepYCNg (j = 0, 1)
               S:1231 subGaussStopNg_zvecNg (τ ≡ 4, proxy c3 from the deterministic A_0, bounds discharged)
HierDriftGen   H:1312 norm_primBilS_le   H:1318 primRhsS_split   H:1323 loopDrift_sub_K_deriv_ng   H:1328 hierarchyNg_of
               H:1333 gridDriftNg (all classes discharged)   H:1339/1353 HierDriftGen_exists_envelope   H:1345/1358 gridDriftNg_at (j = 0, 1)
               H:1366 band GridDriftN   H:1370 exists_norm_KI_le_wing (hyp: STKboundgL, registered; all deterministic premises discharged)
```
Every endpoint theorem of targets 2–10 has an instance; the only premise left open is the registered `STKboundgL`.

## 5. Paper deltas
Lean/paper differences and their coverage (prove report (d)): carrier data form (shifted walk `Ψ + pathH(sz.withLam lam')`, loops at `ztOf m E u`)
→ `T2474a`; explicit `KI ∘ KLloopOf = K` premise of `gridDriftNg(_at)` → `T2474b`; band re-derivations under `∀ n, |E n| < 2` → `T2474c`. All
proposed; numbering by the dispatcher at merge. No uncovered difference found.

## 6. Per-target verdicts
| target | verdict | note |
|---|---|---|
| 1 classes LoopForm/WalkForm + band | PASS | Iff.rfl to pins; band by `rfl`/`zero_add` |
| 2 hermTestFunLoopNOf, hermLoop, band | PASS | proves `T2474_HermLoopOf`; instance at non-band `m` |
| 3 QVPropagatedNg, qvPropagatedNg, band | PASS | check shape; `QVPropagatedN d` re-derived |
| 4 vocabulary + 7 bridges | PASS | SubGaussForm/Stop Iff.rfl; bridges compile |
| 5 six identifications | PASS | band statements over the carrier; `0 ≤ s n` dropped |
| 6 primBilS, KLoop, KTwo, loopDrift | PASS | `T2474_LoopDrift` from KLoop, KTwo |
| 7 HierarchyNg, hierarchyNg_of | PASS | check shape; `HierarchyN d` re-derived |
| 8 stepErrNg, GridDriftNg + band | PASS | Iff.rfl; both band directions compile |
| 9 Expand, UStep, gridDriftNg(_at) | PASS | + KLink premise (O2) |
| 10 envelopes | PASS | check shapes verbatim |
| 11 instances | PASS | §4 |
| 12 G1 | PASS | band diff empty; Part 3 `#check`s compile on the branch |

## 7. Observations (no verdict effect)
- O1 (split). The 1a central 2,748 > 1,950 fires the pre-signed split, but both files are delivered on `t/T2474`. Each file is independently
  under the stop line, the file boundary is clean (H imports S, S imports neither), and both files are audited here. Merge order/rows: hub/dispatcher.
- O2 (KLink). `gridDriftNg`, `gridDriftNg_at` take `HierDriftGen_KLink Cm n` (`∀ w ∈ [0,1), KI n w (KLloopOf σ a) = K n w σ a`) beyond the
  non-binding 9 (b) shape. It is an input listed by the ticket ("inputs used as hypotheses only" (e)), holds by `rfl` at band and BA (§2), and the
  conclusion is exactly `T2474_GridDriftNg`. Candidate `T2474b` asks whether to fold it into `HierDriftGen_KLoop`.
- O3. `gridDriftNg_at` takes `LoopForm`/`WalkForm` for all `n` (their pinned text is `∀ n`); the other classes and the window are at `n` only.
- O4. The band re-derivations of target 5 and `hierDriftGen_band_gridDriftN`'s route use `∀ n, |E n| < 2` (single-index band forms not
  re-derived; the merged band theorems are unchanged). Covered by `T2474c`.
- O5 (C6). 1a f_sem(HierAlgebra) 0.255 (T2379 method), 0.309 on the widest reading; no class-(t) segment of `HierAlgebra` is copied
  (`KTwo` is a class with an 8-line band discharge, H:394-401).
