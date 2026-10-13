Auditor model: claude-opus-5-5
# T2473b (T4s2b, target 7: `Chain/GridAssemblyGen`): audit round 1, Tue Oct 13 03:11:39 UTC 2026
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2473b-audit1`, detached at `t/T2473b` ce109b72. Binding: ticket T2473, Amend 1 (three rows; T4s2b = `GridAssemblyGen`, target 7), Amend 2, supervisor 2351 T4S2-C2/C3 (CONTROL H263 (4)).

**Verdict: PASS (target 7).** No dispatcher sign-off needed.

## 1. Diff scope, frozen files, probe
```
$ git diff --stat main...t/T2473b
 RBM3D/Chain/GridAssemblyGen.lean | 1197 ++++++++++++++++++++++++++++++++++++++
 RBM3D/Probe/T2473Pins.lean       |  400 +++++++++++++
$ git diff t/T2473:RBM3D/Probe/T2473Pins.lean t/T2473b:RBM3D/Probe/T2473Pins.lean | head; echo exit=$?
exit=0                                   # probe = the 1a probe b8c9b113 (1a-only file, never merged)
$ git diff main...t/T2473b -- RBM3D/Induction RBM3D/Path RBM3D/BA RBM3D/Chain/{Carrier,Step2Gen,Step2Kern,GridDuhamelGen,DecayGen,Step34Gen,StepDecompGen,GridRepTailGen,GridRepTailGen2}.lean RBM3D/Test RBM3D.lean | wc -l
       0
```
Both files are sole writable files; the hub brings in only `GridAssemblyGen.lean` (+ the root import line).

## 2. Statements: the eight pins against the 1a probe texts (script)
`pindiff.py`: every `def`/`structure` block of both files, docstrings stripped, whitespace normalised, compared by name.
```
$ python3 pindiff.py RBM3D/Probe/T2473Pins.lean RBM3D/Chain/GridAssemblyGen.lean
IDENTICAL qvFormNg 206
IDENTICAL StoppedAzumaZNg 683
IDENTICAL AzumaSubGNg 772
IDENTICAL YMomentBoundsNg 938
IDENTICAL YMomentsConclNg 421
IDENTICAL YMomentsNg 278
IDENTICAL GridAssemblyHypNg 1565
IDENTICAL AssembledNg 1572
identical 8 of 8
other defs/structures in file: []
```
Section variables are the same in both (`variable {d : ℕ} {sz : Sizes d}`, probe :120, file :58).

Theorems against the band originals (`Induction/GridAssemblyN`):
| target theorem | band original | generic premises | check |
|---|---|---|---|
| `stoppedAzumaZNg Cm hL hW s t K : StoppedAzumaZNg Cm s t K` (:423) | `stoppedAzumaZN (E s t K) : StoppedAzumaZN sz E s t K` (:1014) | `StepDecompGen_LoopForm Cm E`, `StepDecompGen_WalkForm Cm lam' Ψ` | same intro pattern; window premises unused in both |
| `assembledNg Cm : AssembledNg Cm` (:807) | `assembledN : AssembledN sz` (:1605) | `[IsProbabilityMeasure Cm.Pp]` only | same route (`gridAsm_zBudget`, core, budgets) |
| `GridAssemblyGen_stronglyMeasurable_ZvecNg/_YvecNg` (:363, :372) | `gridAsm_stronglyMeasurable_ZvecN/_YvecN` (:927, :937) | `hL`, `hW` | same conclusion `StronglyMeasurable[filt sz (j+1)]` |

The premises are T2474's merged single texts (`Chain/StepDecompGen.lean:60, :73`): `LoopForm` (`0 < Im m`, `Cm.LM = loopFine … (ztOf (Cm.m n) (E n) u)`, …) and `WalkForm` (`Ψ n` Hermitian, `Cm.Pp = pathP (sz.withLam lam')`, `Cm.Hpath = Ψ n + pathH`). They are the ticket's input (d) "W and compat" (D2 (1); Amend 1 item 3 / Amend 2 item 1 use the same two texts). No premise outside (a)-(i), no new named `Prop`. Quantifier order of `AssembledNg` (fixed `k, ε, D, D₁, C_P, C_K` before `∀ᶠ n`, then the data) is the band order with `E : ℝ` removed (T2473f).

## 3. Hidden hypotheses, vacuity, cycles
- `GridAssemblyHypNg.hKer : GridRepTailGen_Ker Cm.toFlowFM n` is the pinned D2 (5) replacement of `hE : |E| ≤ 2` (probe text, passed at the 1a-audit), merged T2471 text (`GridRepTailGen.lean:54`); discharged at the band by `gridRepTailGen_ker_band (hE : |E n| ≤ 2)` (`GridRepTailGen2.lean:672`), used in the instances below. No other premise sits in a field outside the band bundle's fields.
- `LoopForm`/`WalkForm` are satisfiable: `stepDecompGen_loopForm_band (hE : ∀ n, |E n| < 2)` (:459), `stepDecompGen_walkForm_band` (:465); both used in the instances.
- No cycle: the file imports only merged modules (`GridDuhamelGen`, `StepDecompGen`, `GridRepTailGen2`, `DecayGen`, `Induction/GridAssemblyN`) and has no importer:
```
$ git grep -l "RBM3D.Chain.GridAssemblyGen" HEAD -- 'RBM3D/*.lean' RBM3D.lean; echo importers-exit=$?
importers-exit=1
```

## 4. Compiled nonempty instances (all in the file; compiled by the build of §5)
| line | endpoint | data | open hypotheses |
|---|---|---|---|
| :990 | `_stronglyMeasurable_ZvecNg` ∧ `_YvecNg` | `bandStep2Mat sz0 gridAsm_E` (`E ≡ 1/2`), `n = 0`, `j = 2`, `k = 3`, window `(sInst, tInst) = (0, 1/16)`, `K_n = N_n^17` | none |
| :1002 | `stoppedAzumaZNg` | `n = 0`, grid `(0, 1/32)`, `Kg = 4`, `k = 3`, `τ ≡ m = 4`, proxy `C > 0`; conclusion: tail `< 1` | the `SubGaussStopNg` family of `ZvecNg` (output of `azumaSubGNg`, T4s2c pin, not yet proved) |
| :1173 | `stoppedAzumaZNg` | `bandStep2Mat sz0 0`, window `(0, 1/2)`, `K = 4`, `m = 1`, `k = 3`, `σ = (+,-,+)` | none (sub-Gaussianity from merged `subGaussStopNg_zvecNg`) |
| :1080 (via private :1023) | `assembledNg` | `sz0_tendsto`, `k = 3`, `ε = 1`, `D = D₁ = 1`, `C_P = 0`, `C_K = 17` (`1+4+3+0+8 = 16 ≤ 17`), `K_n = N_n^17`, `Δ = gridStep`, `P = 1`, `A₀ ≡ 1`, `Z = gridAsm_witZvec` (random, `gridAsm_witZ_ne_zero`, `GridAssemblyN:2185`), proxy `gridAsm_witProxy > 0`; bundle via `bandStep2_GridAssemblyHypN` (`hKer` = `gridRepTailGen_ker_band`) | none |
| :1100 | `assembledNg` with `Z = ZvecNg` | same, `ε = 1/100` | the `SubGaussStopNg` family of `ZvecNg` (T4s2c) |
| :1121, :1127 | `bandStep2_qvFormN`, `GridAssemblyGen_norm_UN_coarse` | `n = 0`, `w = 1/16`; `v = 1/16 > w = 1/32` | none |

No `N = 0` (`n = 0` gives `L = 4`, `W = 32`, `N = 2097152`), no empty index, no collapsed window, no `False` premise. `K_n = N_n^{C_K}` is forced by the pin (`Δ ≤ N^{-C_K}`, `KΔ ≤ 1`), not a large-witness trick. The open hypothesis of :1002/:1100 is another row's unproved pin (allowed); :1173 and :1080 have none. Band corollaries: `stoppedAzumaZN_of_Ng` (:917, the merged `StoppedAzumaZN sz E s t K` in full) and the `E n`-slice of `AssembledN` (:938) compile.

## 5. Build, axioms, hygiene, greps
```
$ lake build RBM3D.Chain.GridAssemblyGen 2>&1 | grep -E "error|warning: declaration uses|Build completed|sorry"   (03:07:31-03:07:41 UTC)
Build completed successfully (3863 jobs).
exit=0
$ lake env lean Ax.lean     (#print axioms of the 17 public declarations)
RBM.BA.qvFormNg / StoppedAzumaZNg / AzumaSubGNg / YMomentBoundsNg / YMomentsConclNg / YMomentsNg / GridAssemblyHypNg /
AssembledNg / GridAssemblyGen_norm_UN_coarse / GridAssemblyGen_stronglyMeasurable_ZvecNg / _YvecNg / stoppedAzumaZNg /
assembledNg / bandStep2_qvFormN / bandStep2_YMomentBoundsN / bandStep2_GridAssemblyHypN / stoppedAzumaZN_of_Ng:
  each line: [propext, Classical.choice, Quot.sound]       (17 of 17; exit=0)
$ lake env lean root_check.lean   (RBM3D.lean + `import RBM3D.Chain.GridAssemblyGen` after the last import; 03:10:25-03:11:31 UTC)
exit=0
axiom audit: 14377 theorems, 4526 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ grep -niE "error|unregistered|not registered|warning|unknown" root_check.out | wc -l
0                                         # no registry line needed; RBM3D/Test/Axioms.lean untouched
$ grep -nwE "sorry|admit|native_decide|axiom" F ; echo $?            -> exit=1
$ grep -nE "def .*[Kk]er\b|def Ugen" F ; echo $?   (U-C4)            -> exit=1
$ grep -n STGridRepNgL F ; echo $?               (TN-C4)             -> exit=1
$ grep -n '^import RBM3D.BA' F ; echo $?         (layering)          -> exit=1
$ grep -nE "InitMem|zero_mem_goodSet|GoodSetNg" F ; echo $?  (T4S2-C2) -> exit=1
$ grep -c "^open private" F                      (T4S2-C3)           -> 1
$ grep -nE "withLam|BAflowLam0|gK" F | cut -d: -f1   (UBA-C1)        -> 79 282 318 1162 1165
$ grep -nE "<ticket hypothesis-rule pattern>" F | cut -d: -f1
22 31 32 65 117 123 195 206 251 252 282 292 310 316 318 325 390 845 846 863 872 885 886 916 926 930 956 1051 1054 1072 1166
```
Classification (lines read): 22-32, 65, 117, 123, 195, 206, 251-252, 282, 292, 310, 390, 845, 863, 872, 916, 926, 930, 956 docstrings; 316, 318 (`pathH` / `sz.withLam lam'`), 325 (`loopFine` at `ztOf (Cm.m n) (E n) u`) proof bodies under `WalkForm`/`LoopForm`; 846, 885-886 band bridges; 1051-1072, 1162-1166 band instances. Generic statement text (pins :61-186, :253-256, :363-375, :423-426, :807): 0 hits. UBA-C1: 79, 282 docstrings, 318 inside W, 1162/1165 band instance; no `g′`/`gK` vs `sz.lam` comparison.
T4S2-C2: no initial-membership statement, no BA reading in this file. T4S2-C3: the single `open private` (lines 41-43) opens nine model-free helpers of `Induction/GridAssemblyN` (`gridAsm_measurable_deriv_zero`, `gridAsm_loopL_line_regular`, `gridAsm_azuma_step`, `gridAsm_mart_moment4`, `gridAsm_norm_pow4_le_re_im`, `gridAsm_zBudget`, `gridAsm_moment4_budget_le`, `gridAsm_yBudget`, `gridAsm_card_label`); none is an S2/`LoopForm` BA reading.
Name clash (`git grep -wE` of the 17 public names + `GridAssemblyGenCheck`): main 0 hits; every other `t/T24*` branch 0 files (probe excluded).

## 6. Paper deltas
Lean/paper (and Lean/band) differences of target 7 and their coverage (report (d), temporary tags, to be numbered by the dispatcher):
- per-carrier energy, `|E n| < 2` / `hE` gone, `AssembledN` band corollary only the `E n`-slice: **T2473f**;
- coarse bound from K3, not K2 (no order on `u`): **T2473g**;
- `LoopForm` + `WalkForm` premises of `stoppedAzumaZNg` and the measurability theorems: **T2473h**;
- `bandStep2_qvFormN` window `|E n| ≤ 2`, `0 ≤ w < 1`: **T2473i**.
All differences found in §2-§4 are covered.

## 7. Observations (no verdict effect)
- O1. The prove report has no section (a) of its own; it points to `T2473-prove.md` (a)/(a″)/(a‴) and the 1a-audit. Not a statement/instance/build/delta defect.
- O2. `YMomentsNg` (pin defined here, proved in T4s2c) replaces `0 < κ`, `|E n| ≤ 2 - κ` by `DecayGen_Spec`; covered here only by the generic-energy wording of T2473f. T4s2c should propose its own candidate when it proves `yMomentsNg`.
- O3. Instance :1173 does not prove `c3 > 0`; its value is that every hypothesis is discharged. The quantitative tail `< 1` is shown by :1002.
- O4. The private abbreviations of `GridAssemblyGenCheck` (`E0`, `s0`, `hL0`, …) carry no file stem; they are `private`, so §3 (E) holds.

## Verdict
Target 7 (`qvFormNg`, `StoppedAzumaZNg`, `AzumaSubGNg`, `YMomentBoundsNg`, `YMomentsConclNg`, `YMomentsNg`, `GridAssemblyHypNg`, `AssembledNg`; `stoppedAzumaZNg`, `assembledNg`, `GridAssemblyGen_stronglyMeasurable_ZvecNg/_YvecNg`): **PASS**. Hub at merge: add `import RBM3D.Chain.GridAssemblyGen` after the last import of `RBM3D.lean`; do not bring in `RBM3D/Probe/T2473Pins.lean`.
