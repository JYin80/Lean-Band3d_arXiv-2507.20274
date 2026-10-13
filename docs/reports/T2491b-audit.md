Auditor model: claude-opus-5-5

# T2491b audit (U3s2b: `Chain/NQBudgetGen`, `Chain/NQLinGen`, targets 7-10), round 1

Audit worktree `RBM3D-wt/T2491b-audit1`, detached at `t/T2491b` = `2cd1f7db`. Written Tue Oct 13 08:17:05 UTC 2026 (`date -u`).
Scratch: scratchpad `T2491b/` (`pinaudit.lean`, `pindiff.py`, `ax.lean`, `fullbuild.txt`). No source edited.

## 1. Diff scope and G1
```
$ git diff main...t/T2491b --stat
 RBM3D.lean                   |    2 +
 RBM3D/Chain/NQBudgetGen.lean |  982 +++++
 RBM3D/Chain/NQLinGen.lean    | 1101 ++++++
 RBM3D/Probe/T2491Pins.lean   |  397 +++++     (t/T2491 probe, inherited; never merged)
$ git diff main...t/T2491b -- RBM3D/Induction RBM3D/Path RBM3D/BA RBM3D/Test | wc -l
       0
$ git diff main...t/T2491b -- RBM3D.lean   (changed lines)
+import RBM3D.Chain.NQBudgetGen
+import RBM3D.Chain.NQLinGen
$ git merge-base main t/T2491b ; git rev-parse --short main
3238c365 ; 1843bd31          (main has since merged T2493, T2494; the hub's merge brings only the listed files)
```
All touched files are sole writable files of row b (plus the probe, excluded by the ticket). Frozen/band files untouched.

## 2. Build, axioms, hygiene
```
$ lake build RBM3D.Chain.NQBudgetGen RBM3D.Chain.NQLinGen 2>&1 | grep -E "^error|Build completed"
Build completed successfully (3881 jobs).
$ lake build   (full library, both import lines; 08:14:10 -> 08:15:59 UTC) | grep -E "error|warning: .*(NQBudgetGen|NQLinGen)|premises|Build"
warning: RBM3D/Chain/NQBudgetGen.lean:{10,12,13,14,17,18,19,20,21}:100: This line exceeds the 100 character limit ...
warning: RBM3D/Chain/NQLinGen.lean:{10,12,13,14,16,17,18,19,20,21,23}:100: This line exceeds the 100 character limit ...
premises found by scanning: 128 (borrowed 1, owed 61, structural 46, refuted 6, superseded 14).
non-vacuity certificates: 0 of 123 premises in the two ledgers; ...
Build completed successfully (4363 jobs).
exit 0
$ lake env lean ax.lean   (#print axioms of all 39 public theorem/def/abbrev names of the two files)
exit 0; lines "depends on axioms: [propext, Classical.choice, Quot.sound]": 39; other lines: 0
$ grep -cE "sorry|\badmit\b|native_decide|^axiom|withLam"   -> NQBudgetGen 0, NQLinGen 0
$ grep -nE "^(structure|class|instance) " (both) | wc -l   -> 0
```
`#assert_rbm_axioms` passes (full build exit 0). The premise-scan count 128 equals the U3s2a figure: no new owed `Prop` premise.

## 3. Layering and hypothesis-rule greps
```
$ grep -n "^import" (both)
NQBudgetGen.lean:6:import RBM3D.Chain.NQGood2Gen      NQBudgetGen.lean:7:import RBM3D.Induction.NQBudget
NQLinGen.lean:6:import RBM3D.Chain.NQBudgetGen        NQLinGen.lean:7:import RBM3D.Induction.NQLin
$ git grep -l -E "import RBM3D.Chain.(NQBudgetGen|NQLinGen)"   -> RBM3D.lean, RBM3D/Chain/NQLinGen.lean
$ grep -cE "def .*[Kk]er\b|def Ugen|STGridRepNgL|ST_gridMart_of_repN"   -> 0, 0
$ X1-C4 grep "(def|abbrev|structure) (GoodSetNg|...|stepErrNg)\b"     -> 0, 0
$ grep -cE "GridDriftNg|HierarchyNg"   (note (9), D5)                 -> 0, 0
$ grep -nE "∀ \(sz : Sizes d\)"  -> NQLinGen:93,94 (NQLinGoodgL), 359-370 (nqLinGoodgL_of)  = family-premise rows 1-5
$ name clash: git grep -w -F -f names.txt (39 names) <ref> -- RBM3D, declarations outside the two files
main 1843bd31: 0 | t/T2491c: 0 | t/T2496: 0 | t/T2492: 0
```
No BA import, no `Q*`/`Qt*`/`Iterations*`/`Step3/4` import, no new kernel, carrier field or structure.

## 4. Target 8 and 9: statement against the binding pins
```
$ python3 -I pindiff.py   (whitespace-collapsed text, check file vs NQLinGen.lean)
T2491_GoodLinNg vs GoodLinNg : identical after T2491_ -> "" and dropping {d} {sz} binders: True 576 576
T2491_NQLinConclg vs NQLinConclg : identical ...: True 895 895
T2491_NQLinGoodgL vs NQLinGoodgL : identical ...: True 326 326
$ lake env lean pinaudit.lean   (check file's Part 1-2 + `import RBM3D.Chain.NQLinGen`, then:)
example : @T2491_GoodLinNg = @GoodLinNg := rfl
example : @T2491_NQLinConclg = @NQLinConclg := rfl
example : @T2491_NQLinGoodgL = @NQLinGoodgL := rfl
example : T2491_NQLinGoodOf := nqLinGoodgL_of
example : ∀ d, NQLinGood d := nqLinGood_holds          (band name unchanged)
pin exit 0   (no error lines)
```
Target 9 is the pinned family theorem verbatim (hypothesis list and conclusion), including the guards of rows 3-4 (`0 < κ → Flow … →`)
and the unguarded rows 5 (`Law`, `LCompat`); no `∃` after `(sz, z)`; the `∃ 𝔠d` comes from `hSE` before `(sz, z)` (proof lines 375-377).

## 5. Targets 7 and 10: statement against the band (ticket's mathematics: band text over a carrier)
Hypothesis-name diff, band theorem vs generic (script on the signatures):
```
budgetNonAltN: band-only ['hE'] | generic-only ['hL', 'hm'] | common 21
nqBudget_merged_inputs: band-only ['hκ', 'hE'] | generic-only ['hspec', 'him1'] | common 14
budgetNonAltLinN: band-only ['hE'] | generic-only ['hL', 'hm'] | common 23
```
Read by hand (NQBudget:555 vs NQBudgetGen:452; NQBudget:834 vs NQBudgetGen:734; NQLin:792 vs NQLinGen:485; NQLin:966 vs NQLinGen:605):
- `budgetNonAltNg`, `budgetNonAltLinNg`: identical conclusions and absorption hypotheses `ha1`-`he4` with `nqGood1C d k Λg κ'` -> `Ck`,
  `etaT (E n)` -> `Cm.eta n`, `(mE (E n)).im` -> `(Cm.m n).im`, `stepErrN` -> `stepErrNg Cm.toFlowFM`; `|E n| < 2` -> `LoopForm` + `‖Cm.m n‖ ≤ 1` (D3).
  Losses `N^{ε₀}(Λ^{1/2}+Φ+Φ²)B_v^k` / `N^{ε₀}(Λ^{1/2}+Φ₁+Φ₂+Φ₃)B_v^k` unchanged.
- `nqBudget_merged_inputsg`: same `C_K` inequalities h1-h4, same `∀ᶠ n` conclusion (`hlog ∧ hR`); `|E n| ≤ 2-κ` -> `DecayGen_Spec Cm.toFlowFM κm` +
  `∀ n, (Cm.m n).im ≤ 1` (the premises of the merged `sum_gridStep_div_etaNg_le`, `sum_weighted_stepErrNg_le`); quantifier order kept.
- `subGaussStop_linNg`: band `hE, hκm, hg, hgΛ, hΛg, hκ'` -> the hypotheses of the merged (row a, PASS) `hQ_nonAltNg` (`hL, hm, hS, hcmp, hA,
  hKer, hRow, hCv, hAk`) plus `AzumaSubGNg`, `QVPropagatedNg`, `WalkForm`; `3 ≤ d` -> `0 < d` (weaker); same exit time `GoodSetNg ∩ GoodLinNg`,
  same proxy `cQVNonAltNg` with `Cv`. R1 enters only here (UBA-C1 table as pinned). Other target-10 items (`dDriftLinNg`, `nqLinExitTauNg`,
  `driftTensorNg_norm_le_of_goodLin`, `nqLin_hdriftNg`, `mem_of_lt_`, `nqLinExitMeasNg`, `tbDriftLinNg`) are the band texts under the same substitutions
  (prove report (b) statement list, lines 92-102, matches the file).
No special case is passed off as the general target: every statement is per carrier `Cm : Step2Mat sz` (or the family) with `d` a parameter.

## 6. Vacuity, hidden hypotheses, cycles
- No `structure`/`class` in either file; the only `Prop` definitions are the pinned `NQLinConclg`, `NQLinGoodgL` (concluded by `nqLinGoodgL_of`).
- Dependencies are merged: `hQ_nonAltNg`, `NQGoodGen_KerNAL` (U3s2a, main 9df6a9e7), T4s2/T5s2/U3s1 names; imports acyclic (section 3).
- External/pin hypotheses: `STSEforLngL`/`STSEforLnConclgL` (U2 pin `lem:SEforLn`); at the band it is discharged by the merged
  `stSEforLn_holds` (`nqLinGood_holds_of_gen`, NQLinGen:389, no open hypothesis), which is the concrete limit check.

## 7. Compiled nonempty instances (same files, section 6; compiled in the build above)
Data: `d = 3`, `sz0` (`n = 0`: `L = 4`, `W = 32`, `N = 2^21`, `lam = 1/64`), carrier `bandStep2Mat sz0 Einst` (`E ≡ 1/2`), `k = 3`,
`σ = (+,-,+)`, `ε = 4/5`, `K ≡ 4`, `Δ = 1/128`, levels `(Γ,Λ,Φ,Φ₁,Φ₂,Φ₃) = (4,3,1,1,12,1)`, `H_0 = 0 ∈ GoodSetNg ∩ GoodLinNg`.
| endpoint | instance (file:line) | open hypotheses |
|---|---|---|
| `budgetNonAltNg` | NQBudgetGen:918 | none (`hlog`, `hR` = band explicit bounds; `ha1`-`he4` for every `Ck > 0`) |
| `nqBudget_merged_inputsg` | NQBudgetGen:958 (`sz0`, `E ≡ 0`, `K n = N^21`, `C_K = 21`) | none |
| `tbInitNg`, `tbDriftNg`, `tbQvNg`, `tb*NonAltNg`, bridges | NQBudgetGen:789-902 | none |
| `goodSetNg_subset_goodLinNg`, `measurableGoodLinNg` | NQLinGen:938, 943 | none |
| `nqLinConclg_of` | NQLinGen:954 (`sz0`, `[0, 1/16]`) | `STSEforLnConclgL` (U2 pin) only |
| `nqLinGoodgL_of` | NQLinGen:963 (band family, `d = 3`; also yields `NQLinGood 3`) | none |
| `subGaussStop_linNg` | NQLinGen:1045 (`m = 4`, `j = 0`, `aFar`, `A = 1`, `gK = sz.lam`) | none (`AzumaSubGNg` by `azumaSubGNg`) |
| `nqLin_hdriftNg`, `mem_of_lt_`, `nqLinExitMeasNg`, `dDriftNonAltNg_eq_lin` | NQLinGen:1001-1039 | none |
| `tbDriftLinNg`, `budgetNonAltLinNg` | NQLinGen:1061, 1079 | none |
Nondegeneracy: exit time positive at every sample (NQLinGen:997), `dDriftLinNg > 0` (:1017), `K = 4 ≠ 0`, window `[0, 1/32]` nonempty.

## 8. Paper deltas
Prove report (d) proposes `T2491-b1` (D3: `|E|<2` -> `LoopForm` + `‖m‖ ≤ 1`; `|E| ≤ 2-κ` -> `DecayGen_Spec` + `Im m ≤ 1`),
`T2491-b2` (explicit `Ck` for `nqGood1C`), `T2491-b3` (linear set over `TimeIcc`, `Cm.Hpath`, law via `Step2EventsGen_Law`). The
`subGaussStop_linNg` hypothesis change is that of `hQ_nonAltNg` (row a, `T2491a`). Every Lean/paper difference found in sections 4-5 is covered.

## 9. Observations (no statement, instance, build, axiom or coverage change)
- O1. `nqLinGoodgL_of` does not read `hW` (WalkForm, row 4) or `hC` (`Step34Gen_LCompat`); they are in the pinned shape `T2491_NQLinGoodOf`, so they
  stay. Dropping them is the dispatcher's choice (prove report (d) 4).
- O2. Budget instances use `ε₀ = Ck + 12` and `D_t = -5` (inherited band data); the bound is still finite and every hypothesis is discharged.
- O3. 20 long-line linter warnings in the two module docstrings (lines 10-23); no other warning.
- O4. Candidate tags are `T2491-b1..b3` rather than the `T####a` pattern; the dispatcher renumbers anyway.
- O5. `main` moved to 1843bd31 (T2493, T2494) after the branch base 3238c365; the three-dot diff is clean and the hub's merge build rechecks.

## Verdict
| target | statement | vacuity / hidden / cycle | instance | build / axioms | deltas | verdict |
|---|---|---|---|---|---|---|
| 7 budgets (`NQBudgetGen`) | band text over carrier, D3 + `Ck` | ok | ok | ok | b1, b2 | PASS |
| 8 `GoodLinNg`, `NQLinConclg`, `NQLinGoodgL` | = pins (rfl, text diff) | ok | ok | ok | b3 | PASS |
| 9 `nqLinGoodgL_of` (+ `nqLinConclg_of`) | = `T2491_NQLinGoodOf` | ok | ok | ok | b3 | PASS |
| 10 linear drift/exit/budget (`NQLinGen` §4-§5) | band text over carrier | ok | ok | ok | b1, T2491a | PASS |

**T2491b (U3s2b): PASS.** No dispatcher sign-off needed.
