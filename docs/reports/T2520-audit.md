Auditor model: claude-opus-5-5

# T2520 audit, round 1 (M/N N2: `Universality/PinsKD`, `Universality/GUEPhase/RandomLayerBGD`, `BA/UNBUniv`)

Written Fri Oct 16 19:41:10 UTC 2026 (`date -u`). Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2520-audit1`, detached at `t/T2520` = d01e9789; `main` = 07f90182.
Scratch (uncommitted): `<scratchpad>/T2520/` with `aud_ties.lean`, `aud_statdiff.py`, `aud_scan.lean`, `aud_band.lean`.
The probe `RBM3D/Probe/T2520Pins.lean` (82ef67a8) is branch-only and not judged.

## 1. Statements against the pins (all targets)
`aud_ties.lean` = the imports of `T2520-pins.lean`, its Part 3 verbatim (namespace renamed `RBM.Univ.PC`), the signed T2519 texts
verbatim (`git show b992c2e7:RBM3D/Probe/T2519Pins.lean` lines 6-12, 21-75, namespace `RBM.BA.T2519Probe`), then 60 ties
`example : PC.T2520_X := <final name>` (`= … := rfl` for the 14 defs), built against the branch:
```
$ lake env lean <S>/aud_ties.lean ; echo exit=$?      (in the audit worktree)
exit=0          errors: 0         examples in namespace AudT2520: 60
  defs (rfl): UNQuekD UNLocAvgkD UNOUClaimskD UNOURowkD UNEMCTE2RowkD UNJakUywRowkD UNClaimRowkD UNG1RowkD
              UNLocAvgBAD UNQueBAD UNOURowBAD UNEMCTE2RowBAD UNJakUywRowBAD UNClaimRowBAD
  G1 (2):     UNQuekD_true … UNG1RowkD_true (8), band_locAvg, band_ouRow
  G2 (3a):    un_claimAll_of_rowskD, unClaimRowkD, ouRowk_of_pinsD, g1Rowk_of_inputsGD
  BA (3b-6):  unLocAvgBAD_iff_at, unQueBAD_iff_at, unTrLocalBAAt_of_locAvg : T2520_TrLocalAt, unTrLocalInitBAAt'_of_locAvg,
              jakUywRowkD, un_claimAll_of_rowsBAD, baBUniv_of_rowsD, unNormBARow_holds, unEMCTE2RowBAD_holds,
              unG1RowkBAD_holds, unOURowBAD_holds, unG1RowkBA_holds, unOURowBA_holds, baEnd_BUnivL_of_ML, baThm27L_of_ML,
              baEnd_BUnivL_three, baThm27L_three, baThm27L_any
  C5 (stop rule, exact type): PC.T2520_C5ProdBA BAKFam BAPB := ba_prodG ; …LLBA BAPB := ba_LLG ; …QueBA BAKFam BAPB := ba_QueG
              T2519Probe.T2519_ProdBA BAKFam BAPB := ba_prodG ; T2519_LLBA BAPB := ba_LLG ; T2519_QueBA BAKFam BAPB := ba_QueG
              @BAKFam = @T2519Probe.T2519_KFamBA := rfl ; @BAPB = @T2519Probe.T2519_PBBA := rfl
              T2519_ProducersBA := ⟨ba_prodG, ba_LLG, ba_QueG⟩ ; @PC.T2520_C5{ProdBA,LLBA,QueBA} = @T2519Probe.T2519_… := rfl
              T2520_G1RowBAOfC5, T2520_Thm27ThreeOfC5
#check @baEnd_BUnivL_three   ->   baEnd_BUnivL_three : UNL32 → BAEnd_BUnivL 3
#check @baThm27L_three       ->   baThm27L_three : UNL32 → BAThm27L 3
```
So every target equals its `T2520_*` text, and C5's producers on `main` equal the signed T2519 texts (Amend 1 form: `n₀ = 4`,
`gueGridK sz 4`) at exact type, `BAKFam`/`BAPB` definitionally. Stop rule (C5 producers): not hit.

Filter placement against the merged texts (MNO-C2, statdiff; script deletes `(Dm : ℕ → Prop)`, `Dm d →`, the `D` suffix):
```
$ python3 -I <S>/aud_statdiff.py
UNQuekD UNLocAvgkD UNOUClaimskD UNOURowkD UNEMCTE2RowkD UNJakUywRowkD UNClaimRowkD (vs PinsK) UNG1RowkD (vs OUInterfaceK),
un_claimAll_of_rowskD (vs PinsK): identical after filter map: True   [9 script lines joined here]
unClaimRowkD           vs Universality/UnivMain.lean:unClaimRowk  identical after filter map: False
 merged: : ∀ K : ∀ d, UNKind d, UNClaimRowk K
 new   : (K : ∀ d, UNKind d) : UNClaimRowk K
ouRowk_of_pinsD (vs OUInterfaceK), g1Rowk_of_inputsGD (vs RandomLayerBG): identical after filter map: True   [2 lines joined]
```
The one `False` is a binder written before the colon instead of `∀ K,` after it: the same type (the tie
`T2520_UnClaimRowkD := unClaimRowkD` compiles). Not a statement difference.

Per-dimension use (MNO-C2), read from `BA/UNBUniv.lean`: `baBUniv_of_rowsD` reads `hLoc`, `rT0`, `rT`, `rD`, `rN` at its own `d`
(`hLd` from `hLoc` through `unLocAvgBAD_iff_at d`). `unG1RowkBAD_holds` feeds `ba_flowG d`, `ba_prodG d hd`, `ba_mlout d hd (hML' d hdd)`.
`baEnd_BUnivL_of_ML` feeds `baEnd_locSCL d hML`, `unQueBAAt_of_ML d hd hML`, `fun d' h => h ▸ hML`. No input is used at another dimension.

Closing (vi): the two D6 signatures above have `UNL32` as the only hypothesis. There is no `STStep5IIIgL`, no `∀ d … UNMLOutBA`,
no `UNLocAvgBA`/`UNQueBA`. `UNL32` is borrowed and authorized (`Test/Axioms.lean:93`, `borrowedProps`; DECISIONS §5).
Closing (vii): the `d > 3` forms are `baEnd_BUnivL_of_ML`/`baThm27L_of_ML` (hypothesis `UNMLOutBA d`) and `baThm27L_any`
(hypothesis `STStep5IIIgL d`).

## 2. Vacuity, hidden hypotheses, cycles
- No new `structure` and no new `class`. The new `def`s are the 8 filtered pins and the 6 BA readings, all tied above.
- No `∃` constant added: `unNormBARow_holds` gives `CV₀ = 3` to the merged `∃ CV₀` of `UNNormBARow` (`BA/UNPins:190`, unedited).
- Dependencies: only merged names on `main` (C5 rows a-d merged; the C5 ties above build against `main`'s modules).
  No N2 name is used by a merged file (all 36 public names below: 0 hits on `main`). No cycle.
- External hypothesis: only `UNL32` (already borrowed and limit-checked at UN-01). This ticket adds no new external input.

## 3. Compiled nonempty instances (same files; `d = 3`; built)
- `BA/UNBUniv` §5, data `S0` with `(L, g) = (4, 3/10)`, `(𝔠, 𝔡) = (1/6, 1/10)`, `κ_* = clsκ 4`, `E_* = (fp 4 _).E`, `k = 1`,
  `E' = 0`, `O = bump`, `τ_U = ouTauMax (1/6) (1/10) > 0`.
  - No hypothesis: `inst_unNormBARow`, `inst_UNOURowBAD`, `inst_UNEMCTE2RowBAD`, `inst_UNJakUywRowBAD`, `inst_claimAll_baD`,
    `inst_unG1RowkBAD`.
  - Hypothesis `UNL32` only: `inst_univ_baD` (`baBUniv_of_rowsD`), `inst_baEnd_BUnivL_three`, `inst_baThm27L_three`.
  - The final `example` applies `baEnd_BUnivL_of_ML`, `baThm27L_of_ML` and `baThm27L_any` at `d = 3`
    (`baThm27L_any` with `baStep5III_holds`).
- The `_iff_at` links are instantiated inside `UNBUniv_hLoc3`, `UNBUniv_hQ3`. The G1 `Iff`s are instantiated at the band kind
  (`PinsKD` 151-182). G2 has four band instances (`RandomLayerBGD` 122-177). The G2 theorems are also applied, with every premise
  discharged, at the BA kind through `inst_claimAll_baD`, `inst_UNOURowBAD`, `inst_unG1RowkBAD`.
- Nondegenerate: `S0` has `L = 4 ≥ 3` and positive sizes; the filter `(· = 3)` holds at `d = 3` by `rfl`; no `False` premise.
```
'RBM.Univ.BAInst.inst_baEnd_BUnivL_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.BAInst.inst_baThm27L_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.BAInst.inst_unNormBARow' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 4. Build, axioms, diff, registry
```
$ lake build RBM3D.Universality.PinsKD RBM3D.Universality.GUEPhase.RandomLayerBGD RBM3D.BA.UNBUniv | grep -E 'error|Build'
Build completed successfully (4426 jobs).          exit=0   (warnings only from upstream files: longLine, module doc-string)
$ lake build | grep -E '^error|axiom audit|Build completed'      (whole library, audit worktree)
info: RBM3D.lean:672:0: axiom audit: 15817 theorems, 4857 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4442 jobs).          exit=0
$ #print axioms (from aud_ties.lean)
'RBM.BA.baEnd_BUnivL_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThm27L_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unNormBARow_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baEnd_BUnivL_of_ML' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThm27L_any' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unOURowBA_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unG1RowkBA_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean <S>/aud_band.lean     (MNO-C1: before = main 07f90182, after = t/T2520 d01e9789)
main 07f90182:  'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
                'RBM.Endpoints.bUniv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
t/T2520:        'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
                'RBM.Endpoints.bUniv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nwE 'sorry|admit|axiom|native_decide' <3 files> | wc -l          ->  0
$ git diff --name-status main...HEAD
M RBM3D.lean   A RBM3D/BA/UNBUniv.lean   A RBM3D/Probe/T2520Pins.lean   M RBM3D/Test/Axioms.lean
A RBM3D/Universality/GUEPhase/RandomLayerBGD.lean   A RBM3D/Universality/PinsKD.lean
$ git diff --numstat main...HEAD -- RBM3D.lean RBM3D/Test/Axioms.lean   ->  3 0 RBM3D.lean ; 14 13 RBM3D/Test/Axioms.lean
$ wc -l   188 PinsKD (stop 450) | 183 RandomLayerBGD (stop 400) | 397 UNBUniv (stop 1,100) | 768 total
$ C1 grep (BA|band|Band|.ba) in the G1 pin texts (PinsKD 32-97) and the G2 chain (RandomLayerBGD 36-114): 0, 0
$ name clash: 36 public N2 names, git grep -w on main: 0 files each
```
- Diff: only sole writable files. No merged Lean file is modified (both `M` files are named writable). No frozen signature is touched.
- `RBM3D.lean`: three imports added after the last `import` line, before `#assert_rbm_axioms`.
- `Test/Axioms.lean`: the Registry lines only. Owed `UNOURowBA`, `UNEMCTE2RowBA`, `UNJakUywRowBA`, `UNNormBARow` are deleted.
  The header `:175` is updated, and so are the owner texts of `UNOULLk`, `UNG1Rowk`, `UNNormBound`, `UNClaim417(C)`, `UNQuek`,
  `UNLocAvgk`, `UNOUQUEk`. Five structural lines are added; the ticket allows at most 5.
Registry scan (`scanPremises`, `import RBM3D`, ignore `RBM.Audit`; `<S>/aud_scan.lean`):
```
before (main 07f90182): found 124; owedProps 115; structural 143; watched found: [UNNormBARow, UNOURowBA, UNOULLk, UNQuek];
   watched not found: [UNEMCTE2RowBA, UNJakUywRowBA, UNG1Rowk, UNLocAvgk]; unregistered: []
after (t/T2520):        found 127; owedProps 111; structural 148; watched found: [UNOULLk, UNQuek];
   watched not found: [UNNormBARow, UNOURowBA, UNEMCTE2RowBA, UNJakUywRowBA, UNG1Rowk, UNLocAvgk]; unregistered: []
```
Owed −4, within the ticket's −2 to −4. The new names found by the scan (`UNQueBAD`, `UNLocAvgBAD`, `UNClaimRowBAD`,
`UNJakUywRowBAD`, `UNEMCTE2RowkD`) are all registered (unregistered: []).

## 5. Paper deltas
Lean differs from the paper only through D723 (`docs/paper-deltas.md:1803`: BA Theorem 2.7 at `d = 3`, with `d > 3` in hypothesis
form) and the borrowed `UNL32`. The filter `Dm` is internal to Lean (T2513, `paper-deltas.md:1837`). `UNNormBARow` is the merged
text, unedited. No uncovered difference; no new candidate is needed.

## Observations (no statement, instance, build, axiom or delta effect)
- O1: the branch carries the 1a probe `RBM3D/Probe/T2520Pins.lean`. It is a listed sole writable file ("1a only, never merged")
  and has 0 importers. The hub merges the other five files.
- O2: `UNClaimRowBAD` and `UNJakUywRowBAD` are registered as structural, although `unClaimRowkD _ _` and `jakUywRowkD … _ba`
  prove them at every filter (prove report O1). Two one-line `∀ Dm` theorems would remove two structural lines.
  This is a dispatcher choice, not a defect.
- O3: owed `UNG1Rowk` was already absent from the scan on `main` and is kept with an updated owner text, as the ticket's
  Registry paragraph requires; the dispatcher may delete it.
- O4: `inst_unG1RowkBA` and `inst_unOURowBA` keep `∀ d, UNMLOutBA d`, `UNLocAvgBA`, `UNQueBA` as hypotheses. These are the
  antecedents of the merged `UNOURowBA` text itself (`d > 3` is out of scope, D723). The filtered `d = 3` twins
  (`inst_unG1RowkBAD`, `inst_UNOURowBAD`) discharge everything.
- O5: the G2 band instances keep the band pins `UNLocAvgBand`, `UNQueBand`, `UNMLOut`, `UNOUClaims` as hypotheses. Those are
  not deterministic hypotheses, and the BA instances in `UNBUniv` apply the same theorems with every premise discharged.
- O6: the docstring of `UNNormBARow` (`UNPins:187-189`) says `‖V‖ ≤ N`; the statement is the polynomial `N^{CV₀}` form. This is a merged docstring, not evidence (CLAUDE.md §5.7).

## Verdict
Every target is **PASS**: G1 (targets 1, 2), G2 (3a), BA leaf (3b, 4, 5, 6, 7). No stop rule is hit: C5 producers equal the signed
texts at exact type; D6 needs `UNL32` only; band axioms unchanged; no merged statement or band proof touched; every file under its
stop line; scan clean. No dispatcher sign-off is needed.
