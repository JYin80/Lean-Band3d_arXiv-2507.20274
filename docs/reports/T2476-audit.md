Auditor model: claude-opus-5-5
# T2476 audit, round 1 (Mon Oct 12 23:48:05 UTC 2026)
Branch `t/T2476` at b27bc334, merge base eaa247c4; current `main` 08daf959. Audit worktree `../RBM3D-wt/T2476-audit1` (detached at b27bc334); second scratch worktree `../RBM3D-wt/T2476-audit1-main` (detached at main, used for the "before" axioms and a trial merge, no commit). Scratch files are in `scratchpad/T2476/` (`G1.lean`, `props.lean`, `ax.lean`, `sig-*.txt`, `t2476.patch`, `*.log`).

## 1. Statements (targets 1–10 against the check-file pins and proposals)
```
$ lake env lean /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2476-check.lean   (audit worktree, branch)
check file exit 0
$ lake env lean scratchpad/T2476/props.lean   # = check file + import RBM3D.BA.EMCTE2BA, without #check lines, plus:
#   example : T2476_eq225Shift := eq225_intervalShift
#   example : T2476_unEMCTE2k_ba := unEMCTE2k_ba
#   example (K) : T2476_BulkWindowk K ↔ UNBulkWindowk K := Iff.rfl     (same for BadBoundk, Bad2Boundk)
#   example : <check-file shape of unJak_of_ouClaimsk>  := unJak_of_ouClaimsk
#   example : <check-file shape of unUyw_of_ouClaimsk>  := unUyw_of_ouClaimsk
#   example : <check-file shape of jakUywRowk>          := jakUywRowk
#   example : <band triple> := ⟨UNBulkWindowk_band, UNBadBoundk_band, UNBad2Boundk_band⟩
#   example : <BA triple>   := ⟨UNBulkWindowk_ba, UNBadBoundk_ba, UNBad2Boundk_ba⟩
#   example : UNEMCTE2RowBA := unEMCTE2RowBA_holds
#   example : UNJakUywRowBA := unJakUywRowBA_holds
#   example : T2476_BUnivBA := fun hcore … hQ => baBUniv_of_rows hcore … rC unEMCTE2RowBA_holds unJakUywRowBA_holds rO hML hLoc hQ
#   example : <statement of eq225_interval, verbatim from EMCTE2.lean:455-470> := by … eq225_intervalShift … 0 Matrix.isHermitian_zero …
'RBM.Univ.unEMCTE2RowBA_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unJakUywRowBA_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.eq225_intervalShift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unEMCTE2k_ba' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unJak_of_ouClaimsk' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unUyw_of_ouClaimsk' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.jakUywRowk' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.bUniv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```
Binder adjustments against the proposals: none (every comparison is the identity or `Iff.rfl`). The kind hypotheses keep the check-file names minus the `T2476_` prefix with the stem `UN…k` (`UNBulkWindowk`, `UNBadBoundk`, `UNBad2Boundk`), as the ticket allows ("names are proposals").
Statement reading (hypotheses, quantifiers, losses):
- Targets 4, 10 are the merged pins `UNEMCTE2RowBA`, `UNJakUywRowBA` themselves, proved outright (closed terms, no hypothesis).
- `unEMCTE2k_ba` keeps `SizeTendsto` and `τU ≤ Cn τU`, as `unEMCTE2_of_sizeTendsto`. `eq225_intervalShift` is `eq225_interval` with a deterministic Hermitian shift `A`, kernels at `A + ouMat`; it is the general form (`A = 0` gives `eq225_interval` verbatim, last example above).
- The K-forms have the band order of quantifiers (`d, 3 ≤ d, 𝔠 𝔡, sz, Admissible, κ > 0, E eventually in bulk, nf, τU ∈ (0,1/4], UNOUQUEk, UNOUDiagk`), with loss `C = 3nf+16`, `c' = 𝔠𝔡/30`. Their only extra premises are the three kind hypotheses, and each is proved at both kinds (`*_band`, `*_ba`). The BA transfers keep the factor `2d+1`, which is weaker than the one-block bound; this is covered by paper-delta T2476b (§5).

## 2. Vacuity, hidden hypotheses, cycles
- No new structure. The three kind hypotheses are `def … : Prop` used as explicit binders of the K-forms, and they are discharged by `UNBulkWindowk_ba` (`BAbulk_window`), `UNBadBoundk_ba` (`unBadY_of_blockM` + `unBadYBA_measure_le`) and `UNBad2Boundk_ba` (`EMCTE2BA_bad2_subset`, proved in the leaf). `unJakUywRowBA_holds := jakUywRowk (fun d => UNKind.ba d) UNBulkWindowk_ba UNBadBoundk_ba UNBad2Boundk_ba UNLocAvgBA` has no residual premise. `UNLocAvgBA` and `UNOUClaimsk` stay antecedents inside the pin, as the ticket requires.
- Not vacuous: `S0_bulk` (merged) puts `E_*` in the BA bulk eventually, and `inst_unJak_k_ba` / `inst_unUyw_k_ba` consume it together with all three BA kind hypotheses.
- No cycle. The leaf imports `EMCTE2`, `Uyw`, `BA/UNPins`, `BA/MReg` (all merged); it reaches the `Jak`/`Uyw`/`EMCTE2` privates by `open private` (lines 53–57) and has 0 importers. The external inputs (`UNOUQUEk`, `UNOUDiagk`, `UNLocAvgBA`) are owed pins of other rows, not new external hypotheses.
```
$ grep -n '^import RBM3D.BA' RBM3D/Universality/{Jak,JakSpectral,Uyw}.lean        -> (nothing)
$ grep -rln 'import RBM3D.BA.EMCTE2BA' RBM3D RBM3D.lean                          -> RBM3D.lean
$ grep -rln 'T2476Pins' RBM3D RBM3D.lean                                         -> (nothing; probe not imported)
```

## 3. Compiled nonempty instances (`BA/EMCTE2BA.lean`, namespace `EMCTE2BAInst`, d = 3; all built, §4)
| target | instance | data | hypotheses left |
|---|---|---|---|
| 1 | `inst_translate` :805, `inst_wirtSecond_translate` :811 | `sz0`, n=0, `A = λ_0Ψ`, `z = ![I]` | none |
| 2 | `inst_eq225_intervalShift` :820 | same, t=0, T=1, `Bd` from `EMCTE2_hsum_bdd` | none |
| 3 | `inst_unEMCTE2k_ba_sz0` :860 | `sz0`, E=0, nf=2, τU=1/2, Cn=1 | none |
| 4 | `inst_unEMCTE2Rowk_ba` :865 | `S0`, `E_*`, nf=1 | none |
| 5–6 band | `inst_unJak_k_band` :871, `inst_unUyw_k_band` :879, `inst_jakUywRowk_band` :899, `inst_unJak_unUyw_band_recover` :888 | `UNKind.band 3`, `sz0`, κ=1/2, E=1, nf=2 | `UNOUQUEk`, `UNOUDiagk` (resp. `UNLocAvgBand`, `UNOUClaims`) |
| 5–9 BA | `inst_unJak_k_ba` :910, `inst_unUyw_k_ba` :917, `inst_bulk_window_ba` :925 | `S0`, `κ_*`, `E_*`, nf=2 | `UNOUQUEk`, `UNOUDiagk` |
| 10 | `inst_unJakUywRowBA` :943 | `S0`, nf=2 | `rO hML hLoc hQ` (other gates' pins) |
| consumer | `inst_univ_ba_rows` :951, `example` :960 | `baBUniv_of_rows` with `rE`, `rJ` discharged | other rows' pins |
Every deterministic hypothesis is discharged. None of the instances is degenerate (`sz0`/`S0` have L ≥ 3, W ≥ 1, `E_*` in the bulk, κ > 0).

## 4. Builds, axioms, scope
```
$ lake build RBM3D.Universality.Jak RBM3D.Universality.Uyw RBM3D.BA.EMCTE2BA RBM3D.Universality.UnivMain RBM3D.Main.BUniv RBM3D.Main.BUnivHolds RBM3D.Main.BandTerminal   (branch)
Build completed successfully (4156 jobs).   exit 0          # no error lines; no "declaration uses 'sorry'"
$ grep "EMCTE2BA.lean.*depends on axioms" build1.log | wc -l ; … | grep -vc "[propext, Classical.choice, Quot.sound]"
35
0
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom " BA/EMCTE2BA.lean Universality/Jak.lean Universality/Uyw.lean Probe/T2476Pins.lean | wc -l
0
$ lake build   (branch, full)                       23:43:58 -> 23:45:01 UTC, exit 0
info: RBM3D.lean:549:0: axiom audit: 14102 theorems, 4456 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4317 jobs).
```
GMN-C2 (c), `#print axioms` before and after (`scratchpad/T2476/ax.lean`):
```
== main 08daf959 (worktree T2476-audit1-main; lake build …BandTerminal …BUnivHolds: 4149 jobs)
'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.bUniv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
== t/T2476 b27bc334 (worktree T2476-audit1)
'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.bUniv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Identical. Trial merge on the current base (dispatcher answer (6); T2475 and T2477 are merged since eaa247c4). In `T2476-audit1-main`: `git apply --3way t2476.patch` (the five files, probe excluded). `RBM3D.lean` and `Test/Axioms.lean` conflict as union hunks. The auditor's resolution keeps both import lines and takes the branch's 7 comment lines; main's removal of the `UNGreenCorrC`, `UNGreenCorrAllC` and `UNCoreC''` lines stays (net `git diff HEAD --numstat Test/Axioms.lean`: 7 7).
```
$ lake build      23:45:42 -> 23:47:27 UTC, exit 0
info: RBM3D.lean:551:0: axiom audit: 14143 theorems, 4467 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 124 (borrowed 1, owed 58, structural 45, refuted 6, superseded 14).
Build completed successfully (4319 jobs).
'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.bUniv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
GMN-C2 (b), signature diff (the ticket's awk script, `main` against `t/T2476`) and G1:
```
Jak main=7 branch=7 difflines=0 | JakSpectral main=24 branch=24 difflines=0 | Uyw main=7 branch=7 difflines=0 | EMCTE2 main=8 branch=8 difflines=0   (no CHANGED line)
$ lake env lean scratchpad/T2476/G1.lean   # 14 `example : <main statement> := <name>` generated from sig-{Jak,Uyw}-main.txt
exit 0                                       # JakSpectral, EMCTE2: git diff main...t/T2476 empty (below)
```
Scope:
```
$ git diff --stat main...t/T2476
 RBM3D.lean | 1 +  ; RBM3D/BA/EMCTE2BA.lean | 986 + ; RBM3D/Probe/T2476Pins.lean | 300 + ; RBM3D/Test/Axioms.lean | 14 +- ; RBM3D/Universality/Jak.lean | 76 ; RBM3D/Universality/Uyw.lean | 78
$ git diff main...t/T2476 -- Universality/{Pins,PinsK,PinsC2,PinsDens,JakKernel,UywKernel,EMCTE2,OUGenerator,OUHessian,OUContraction,UnivMain,JakSpectral}.lean BA/UNPins.lean BA/MReg.lean Main | wc -l
0
$ wc -l Jak.lean Uyw.lean BA/EMCTE2BA.lean     -> 1017 / 984 / 986   (stop line 2,000; twin < 1,800; reserve BA/JakUywBA not created)
$ name-clash: 41 top-level names of BA/EMCTE2BA.lean, git grep -w on main 08daf959 (RBM3D, RBM3D.lean): 0 hits
```
`RBM3D/Probe/T2476Pins.lean` is not a sole writable file. CONTROL H259 (4) declares it a non-merged probe on the branch, so the hub must not bring it in. The other five files are sole writable files. The registry diff is comment-only on `:177-181` and `:187-188` (7+/7−; premises stay in `owedProps`). The private edits of `Jak` and `Uyw` are the four privates of the 1a table (v): `*_grid_energy_lt` drops `hE` and concludes `|e − E| < κ/2`, and `*_fixed_time` uses `lamV` and `hbad` in place of `hlam`/`hE`/`hque`. Both band callers rebuild `hbad` from `measure_bad(2)_le_of_queBadMat` and `hdiag` from `|E| ≤ 2 − κ`.

## 5. Paper deltas
- T2476a (prove report (d), ticket): `(EMCTE2)` for BA is stated as the shifted generator identity `eq225_intervalShift` (deterministic Hermitian `A = λΨ`, kernels at coupling 0). It covers targets 1–4.
- T2476b (prove report (d), ticket): the two couplings, the kind bulk window `UNBulkWindowk` (band `κ/2, κ/2`; BA `κ/2, (πκ)³/8`), `κ_eff = min κ (min 2 (2r))`, and the factor `2d+1` kept for BA (weaker than the one-block bound). It covers targets 5–10.
- No other Lean/paper statement difference found. The band statements are unchanged (G1).

## 6. Observations (no effect on statement, instance, build, axioms or delta coverage)
1. The prove report has 284 lines; the ticket asks for ≤ 200 (CLAUDE.md §6 allows 300). Its section order differs from the ticket's list (1)–(9).
2. The conclusion of `inst_bad_ba` (:932) is only `∀ᶠ n, 0 < S0.W n`. The BA transfers are applied inside its proof with the trivial QUE bound `p = 1`. Targets 7–9 are exercised substantively through `inst_unJak_k_ba`, `inst_unUyw_k_ba` and `inst_unJakUywRowBA`.
3. The leaf's `A = 0` example (:249) keeps `0 + ouMat` in its kernel hypothesis. The auditor's `props.lean` derives the verbatim statement of `eq225_interval`.
4. Merge note for the hub: union-resolve `RBM3D.lean` (both import lines) and `Test/Axioms.lean` (§4 trial merge, full build green). Exclude `RBM3D/Probe/T2476Pins.lean`.
5. The K-forms sit in the leaf, not in `Jak`/`Uyw` (dispatcher answer (4), 1a finding (3)). The band theorems keep their re-instantiated calls.

## Verdicts
| target | verdict |
|---|---|
| 1 `EMCTE2BA_testFunH_translate`, `EMCTE2BA_wirtSecond_translate` | PASS |
| 2 `eq225_intervalShift` | PASS |
| 3 `unEMCTE2k_ba` | PASS |
| 4 `unEMCTE2RowBA_holds : UNEMCTE2RowBA` | PASS |
| 5 private fixed-time lemmas (`Jak`, `Uyw` in place; public statements verbatim) | PASS |
| 6 `unJak_of_ouClaimsk`, `unUyw_of_ouClaimsk`, `jakUywRowk` + band kind instances | PASS |
| 7 `UNBulkWindowk_ba` | PASS |
| 8 `UNBadBoundk_ba` | PASS |
| 9 `UNBad2Boundk_ba` (`EMCTE2BA_bad2_subset`) | PASS |
| 10 `unJakUywRowBA_holds : UNJakUywRowBA` | PASS |
**Overall: PASS.** No dispatcher sign-off needed.
