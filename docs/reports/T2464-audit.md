Auditor model: claude-opus-5-5

# T2464 audit (round 1) — BA-L L4c1 `Graph/BAExp14c`, `BAExp14cB`

Time: Mon Oct 12 19:29:52 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2464-audit1`, detached at `t/T2464` = 51f5a5b8, merge base a1628b9d.
Check file `docs/tickets/checks/T2464-check.lean`, md5 ec146746651f760a5655cc8e10814fca (identical on `main` and on the branch).

## 1. Diff, size, hygiene
```
$ git diff --name-only main...HEAD
RBM3D/Graph/BAExp14c.lean
RBM3D/Graph/BAExp14cB.lean
$ wc -l RBM3D/Graph/BAExp14c*.lean        # stop line 2,000 per file
     919 RBM3D/Graph/BAExp14c.lean
    1153 RBM3D/Graph/BAExp14cB.lean
$ git diff main...HEAD -- RBM3D/Test/Axioms.lean RBM3D.lean | wc -l
       0
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^\s*axiom\b' RBM3D/Graph/BAExp14c*.lean; echo $?
1
$ grep -nwE 'mE|STGM|STKloop|etaT|STflowE|lwS|lwSplus' RBM3D/Graph/BAExp14c*.lean; echo $?     # C1
1
```
Only the sole writable files; no merged file (no frozen signature) touched; no `inductive`; `BAExp14cC.lean` not created.

## 2. Build
```
$ lake build RBM3D.Graph.BAExp14c RBM3D.Graph.BAExp14cB 2>&1 | grep -E 'BAExp14c|^error' ; tail -1
✔ [4031/4032] Built RBM3D.Graph.BAExp14c (7.9s)
✔ [4032/4032] Built RBM3D.Graph.BAExp14cB (9.4s)
Build completed successfully (4032 jobs).          # 0 error lines; warnings only in pre-existing modules
```

## 3. Statements against the pins (script diff + elaboration)
Text diff (`pdiff.py`: def/theorem bodies, whitespace collapsed, `T2464_` stripped, `rT0 ↦ baS3RootT0`, proofs cut at `:= by`):
```
$ python3 -I pdiff.py T2464-check.lean BAExp14c.lean BAExp14cB.lean
T2464_rootT0_sub       -> baS3RootT0_sub         IDENTICAL
T2464_rootT0_list      -> baS3RootT0_list        IDENTICAL
T2464_BAS3Bridge       -> BAS3Bridge             IDENTICAL
T2464_val_zero         -> BAExp14c_val_zero      IDENTICAL
T2464_val_env          -> BAExp14c_val_env       IDENTICAL
T2464_BAFoldLeafT      -> BAFoldLeafT            IDENTICAL
T2464_foldTCongr       -> baFoldLeafT_congr      IDENTICAL
T2464_foldT_weaken     -> baFoldLeafT_fold       IDENTICAL
T2464_foldT_cat        -> baS3FoldT_holds        IDENTICAL
T2464_BAS3CloseT       -> BAS3CloseT             IDENTICAL
T2464_xy_support       -> BAExp14c_xy_support    IDENTICAL
T2464_BAG5LeafPrec     -> BAG5LeafPrec           IDENTICAL
T2464_BAS3LeafAvg      -> BAS3LeafAvg            IDENTICAL
T2464_S3OfLeaf         -> BAExp14bS3OfLeaf       IDENTICAL
```
Auditor's own scratch check (not committed): `import RBM3D.Graph.BAExp14cB` + the check file verbatim + the lines below, all
closed by the target as a term (no tactic), plus `#print axioms`:
```
example : T2464_rootT0_eq baS3RootT0 := fun s => rfl
example : T2464_rootT0_sub baS3RootT0 := baS3RootT0_sub
example : T2464_rootT0_list baS3RootT0 := baS3RootT0_list
example (d : ℕ) : T2464_rootT0_identity baS3RootT0 d := baS3RootT0_identity d
example (d : ℕ) : T2464_BAS3Bridge baS3RootT0 d := baS3Bridge_holds d
example (d : ℕ) : T2464_BAS3Bridge baS3RootT0 d = BAS3Bridge d := rfl
example : T2464_val_zero := BAExp14c_val_zero
example : T2464_val_env := BAExp14c_val_env
example (q : BAPGraph (Fin 2)) : T2464_BAFoldLeafT q = BAFoldLeafT q := rfl
example : T2464_foldTCongr := baFoldLeafT_congr
example : T2464_foldT_weaken := baFoldLeafT_fold
example : T2464_foldT_cat := baS3FoldT_holds
example : T2464_BAS3CloseT := baS3CloseT_holds
example : T2464_BAS3CloseT = BAS3CloseT := rfl
example : T2464_xy_support := BAExp14c_xy_support
example (d : ℕ) : T2464_BAG5LeafPrec d = BAG5LeafPrec d := rfl
example (d : ℕ) : T2464_BAS3LeafAvg d := baS3LeafAvg_holds d
example (d : ℕ) : T2464_BAS3LeafAvg d = BAS3LeafAvg d := rfl
example (d : ℕ) : T2464_S3OfLeaf d := baExp14bS3_of_leaf d
example (d : ℕ) : T2464_S3OfLeaf d = BAExp14bS3OfLeaf d := rfl
$ lake env lean check_audit.lean; echo exit=$?   -> exit=0, 0 error lines (one unused-variable warning on `fun s => rfl`)
```
`T2464_S3OfLeaf` concludes the merged pin `BAExp14bS3` (`BAExp14b:181`, untouched) unchanged, all four families, five premises.
Quantifier order, `0 ≤ t ≤ T₀`, all `ω, σ, a, b` (incl. `a = b`), `t^{n_W}`, `(1−t)⁻¹B^{5/2}` and the `t` factor are as pinned (text identity).

## 4. Axioms
```
'RBM.BA.baS3RootT0_sub' / 'baS3RootT0_list' / 'baS3RootT0_identity' / 'baS3Bridge_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14c_val_zero' / 'BAExp14c_val_env' / 'BAExp14c_eta_le_one' / 'BAExp14c_floor'     depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baFoldLeafT_congr' / 'baFoldLeafT_fold' / 'baS3FoldT_holds' / 'baS3CloseT_holds'       depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14c_xy_support' / 'baS3LeafAvg_holds' / 'baExp14bS3_of_leaf'                       depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14cInst.rootT0_inst' / 'rootT0_inst_identity' / 'closeT_inst' / 'offsets_exist'   depends on axioms: [propext, Classical.choice, Quot.sound]
```
(19 `#print axioms` lines, condensed by name only; every line printed exactly the standard three.)

## 5. Hidden hypotheses, vacuity, cycles
- No `structure` is introduced; all statement defs (`BAS3Bridge`, `BAFoldLeafT`, `BAS3CloseT`, `BAG5LeafPrec`, `BAS3LeafAvg`,
  `BAExp14bS3OfLeaf`) are explicit Props, identical to the pins; the bridge, closure, catalogue and leaf-average defs are
  concluded by public theorems.
- The only open inputs are the leaf pin `BAG5LeafPrec` (antecedent of `BAS3LeafAvg`, `BAExp14bS3OfLeaf`; owed by L4c2 + L4g, as
  the ticket fixes) and the five Step 1/2 pins inside statement defs. No public theorem has a `BAG5LeafProps`/`BAG5Tgt`/
  `BAG5Attached`/`BACtx`/`BAG5LeafPrec`/Step 1/2 binder: grep of the signatures of the public helpers
  (`BAExp14c_etainv`, `_scale`, `_int_slice`, `_integrable_val`, `_int_avg`, `_avg_le`, `_avg_le_tied`, `_integrable_graph`)
  returns only `:= by` lines (exit 1 on the binder names).
- Dependencies are merged files only (`BAS3Close*`, `BAVocab`, `BAExpandId` via `open private`, precedent `BAS3CloseC:41-50`);
  no circularity (part B imports part A only).
- External-hypothesis limit check: the leaf pin and the five Step 1/2 pins are other gates' pins; the prove report (a)(ii)
  `s7_premises.py` gives their leading terms at the instance (ratio 0.983 to `Bctl`, leaf-pin RHS 1.5e-11 above the floor 1.6e-16).

## 6. Compiled nonempty instances (`BAExp14cB.lean:930-1150`, namespace `BAExp14cInst`; compiled in §2)
| target | instance | data / open hypotheses |
|---|---|---|
| 1 | `rootT0_inst s` (partition nonempty, `P` in both partitions, `q` in both lists, `q` a leaf); `rootT0_inst_identity` | `BAselStar`, fuel 2; identity at `d=3, L=3, W=1, t=1/2, m=i`, `BASelf` discharged |
| 2 | `example … := baS3Bridge_holds 3 … sz0 zSeq flow_sz0 0 (1/2) …` | `d=3`, `sz0` (`W=32, L=4`), `n=0`, all `ω σ a b`; none open |
| 3 | `val_zero` at `baS3Stuck false 0 false` (`anchor_nW`, decided); `val_env`; `eta_le_one`; floor at an eventual `n` | none open |
| 4 | `foldT_rho0` (`ρ' = ½·1[c₃=c₁∧c₄=c₂](M^B_{c₁c₂})²`), `foldT_anchor`, `closeT_inst` (both disjuncts in `MERGED`'s list, `s=false`) | none open |
| 5 | `xy_support` at `tiedGraph` with `offsets_exist` (labels of different offsets exist); `baS3LeafAvg_holds` at the fold anchor and at a `BAG5LeafProps` leaf of `MERGED`'s list | `BAG5LeafPrec 3` + five Step 1/2 pins at `t ≡ 1/2` |
| 6 | `baExp14bS3_of_leaf 3 hpin`; full application at `sz0, zSeq, t ≡ 1/2` | `BAG5LeafPrec 3` + five Step 1/2 pins |
No `N = 0`, empty index, collapsed window or `False` premise; every deterministic hypothesis (`BAFlow` by `flow_sz0`,
`t ≤ T₀` by `half_lt_t0`, `0 < κ, ε, 𝔡`, `3 ≤ d`) is discharged.

## 7. Paper deltas
The report proposes no `T2464a`. Lean/paper differences touched by these statements are already recorded:
`(Gammamuxy)` carrying `t^{n_W}` (`B:84-90`; leaf pin `BAG5LeafPrec`) is D573; the BA fold route in `[a]×[b]`-averaged form for
`M`-separated 4-cycles (0851 Q3 disjunction, `BAFoldLeafT`, `BAS3LeafAvg`) is D665 (A′). The `x ~ y` support (offset version of
the paper's `x = y` case, `eq:sizeGammamu_E`) is a proved lemma inside the route, not a changed statement of the paper. Coverage: complete.

## 8. Observations (no verdict change)
- O1. The prove report's narrative says the target-1 identity instance uses `W = 1` (the merged `BAS3CloseInst` data); the
  nondegenerate `W = 32` instance of the same graph values is the target-2 example. Acceptable (index set has 27 sites, no hypothesis left open).
- O2. `BAExp14c_floor` (not pinned) is stated at a fixed `n` with `2 ≤ N`, `Bctl ≤ 2`, rather than as the ticket's "eventually `N^{-K} ≤ …`"; it is
  a helper, its instance obtains such an `n` from `BAExp14a_eventual_scalars`.
- O3. `RBM3D.lean` import lines are left to the hub (`import RBM3D.Graph.BAExp14c`, `import RBM3D.Graph.BAExp14cB`); the full build runs at merge.

## Verdicts
| target | verdict |
|---|---|
| 1 sub-root `baS3RootT0`, `_sub`, `_list`, `_identity` | PASS |
| 2 bridge `BAS3Bridge`, `baS3Bridge_holds` | PASS |
| 3 kit `BAExp14c_val_zero`, `_val_env` (+ `_eta_le_one`, `_floor`) | PASS |
| 4 `BAFoldLeafT`, `_congr`, `_fold`, `baS3FoldT_holds`, `BAS3CloseT`, `baS3CloseT_holds` | PASS |
| 5 `BAExp14c_xy_support`, `BAG5LeafPrec` (statement), `BAS3LeafAvg`, `baS3LeafAvg_holds` | PASS |
| 6 `BAExp14bS3OfLeaf`, `baExp14bS3_of_leaf` (conditional on the leaf pin, as the ticket specifies) | PASS |
| 7 instances | PASS |

**Overall: PASS.** No dispatcher sign-off needed.
