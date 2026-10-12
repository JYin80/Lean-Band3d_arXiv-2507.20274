Auditor model: claude-opus-5-5

# T2477 audit (round 1): BA M/N N3b, E3 + E4 C-forms (`GreenCorr`, `Step1Band`, `UnivMain`)

Date (`date -u`): Mon Oct 12 23:10:35 UTC 2026. Branch `t/T2477` = 2b1c9956 (base eaa247c4); `main` = ab435c6e
(eaa247c4..ab435c6e touches Lean only in a docstring of `Chain/CltGen.lean`). T2476 (N3a) is not merged
(`docs/queue/T2476.state`: `proving`), so the H259 (4) comparison runs on `main` ab435c6e.
Worktrees: branch `../RBM3D-wt/T2477-audit1` (detached at 2b1c9956), main `../RBM3D-wt/T2477-audit1-main` (detached at ab435c6e).
Scratch (not committed): `<scratchpad>/T2477/{sigs.py,G1dump.lean,auditcheck.lean,ax.lean}`.

## 1. Diff scope and line counts
```
$ git diff --name-only main...t/T2477
RBM3D/Test/Axioms.lean  RBM3D/Universality/GreenCorr.lean  RBM3D/Universality/Step1Band.lean  RBM3D/Universality/UnivMain.lean
$ git diff main...t/T2477 -- PinsK PinsC2 Pins GUETranslation Step1Cond Step1Good PinsDens RBM3D/BA RBM3D/Main RBM3D.lean | wc -l
0
$ git diff main...t/T2477 | grep '^[+-]import'
+import RBM3D.Universality.PinsK (GreenCorr) | +import RBM3D.Universality.PinsC2 (Step1Band) | +import RBM3D.Universality.PinsC2 (UnivMain)
GreenCorr main=1004 br=1238 | Step1Band main=1240 br=1533 | UnivMain main=690 br=905   (all < 1,800; reserve Step1BandC not created)
4 files changed, 857 insertions(+), 118 deletions(-)   (net +742 < 1,560)
$ git diff main...t/T2477 -- RBM3D/Test/Axioms.lean   (3 deletions, 0 additions)
-   `RBM.Univ.UNGreenCorrC, -- ... (T2187, UN-01b: owed; ...)
-   `RBM.Univ.UNGreenCorrAllC, -- ... (T2187, UN-01b: owed; ...)
-   `RBM.Univ.UNCoreC'', -- ... (T2213, UN-12b: owed; ...)
$ git diff main...t/T2477 | grep '^+' | grep -wE "sorry|admit|axiom|native_decide|open private|implemented_by|extern"
(no output)
```
All touched files are sole writable files; no frozen file touched; no private deleted (`comm` of `^private ... <name>` lists, main minus branch: empty for all three files).

## 2. GMN-C2 signature diff (text) and G1 (elaborated types)
Text script (the ticket's spec: non-private column-0 declarations up to the first depth-0 `:=`/`where`, whitespace collapsed):
```
== GreenCorr main=8 br=14 removed/changed=0 added=6
== Step1Band main=16 br=23 removed/changed=0 added=7
== UnivMain main=15 br=26 removed/changed=0 added=11
== PinsDens main=31 br=31 removed/changed=0 added=0
```
G1 by elaboration (stronger than text): a meta command prints, for every non-private, non-internal constant whose module is one
of the four files, `module name hash(type) levelParams`; run with `lake env lean` in each worktree, then `comm`:
```
main: 74 lines   branch: 98 lines
pre-existing (main) decls missing or with changed type on branch:
(none)
added on branch: 24 names = the 9 targets + the 15 instances listed in §5 (full list in G1.br)
```
So every read-outside declaration (`greenCorrAll`, `univMainRow`, `unClaimRow(k)`, the six `step1Band_*`, the 15 `PinsDens`
names) and every other pre-existing public declaration of the four files keeps its elaborated statement exactly.
Name clash: `git grep -w -F` of the 9 target names on `main`, `t/T2476`, `t/T2475`: 0 hits.

## 3. Statements against the pins (check file `T2477_*`)
`auditcheck.lean` = `docs/tickets/checks/T2477-check.lean` verbatim + the auditor's tail; compiled on the branch:
```
$ lake env lean auditcheck.lean ; echo check_exit=$?      -> check_exit=0, no `error`, no `sorry` in output
example : T2477_GreenCorrC := fun sz h M => unGreenCorrC sz h M
example : T2477_GreenCorrAllC := greenCorrAllC
example : T2477_integral_ouPC := step1Band_integral_ouPC
example : T2477_Step1BandC := step1BandC''
example : T2477_Step1BandRowC := step1Band_rowC''
example : T2477_Infty1RowC := un_infty1RowC''
example : T2477_univMain_transferC := fun sz M n k O E => univMain_transferC sz M n k O E
example : T2477_UnivMainRowC := univMainRowC
example : T2477_CoreC := unCoreC''_holds
example : UNCoreC'' := (unCoreC''_holds : T2477_CoreC)
example : UNGreenCorrAllC := (greenCorrAllC : T2477_GreenCorrAllC)
```
Read against the pins (`PinsK:187,204`, `PinsC2:106`, check-file Part 2): same hypotheses, same quantifier order
(fixed parameters, then `∀ M : UNModelC sz` with no `UNKind.ba` premise, then `k, O`, then `∃ τ`, then `∀ τU`), `τU ≤ 𝔠𝔡`
in target 4a, `|E'| < 2` in 5, `1 ≤ k` in 8 (inside `UNCoreC''`); `UNTrLocal` is not a premise of 4/5; no dropped premise;
targets 1, 6 differ only in binder implicitness of `d` (allowed). Targets 2 and 8 are the merged pins themselves.
No special case, no adapter: each target is the general pin.

## 4. Hidden hypotheses, vacuity, cycles
- New public theorems carry no structure-packaged hypothesis: their premises are the merged Props `UNL32`, `UNGUELocal`,
  `UNGreenCorrAllC`, `UNDens'`/`UNDens`, `UNTrLocal`, `UNTrLocalInit'`, `UNNormBound`, `UNMeanBound`, `UNClaimAllC`,
  `IsTestFun`, `Sizes.Admissible` (signatures in §2). New private Props `GreenCorr_Claim417`, `GreenCorr_Apriori` occur
  only in private lemma binders, instantiated at the pins' own premises.
- `UNL32` is the authorized external input (borrowed, registry `:93`), unchanged; its limit check is that of its owner
  ticket; this ticket adds no external hypothesis.
- Cycles: the three new imports are acyclic (full build passes, §6). Dependencies are merged declarations only.
- Registry: the full build's scan reports `premises found by scanning: 130 (borrowed 1, owed 64, ...)` and the
  `#assert_rbm_axioms` check passes with the three owed lines deleted (they are now concluded by targets 1, 2, 8).

## 5. Compiled nonempty instances
In-file (all compiled in §6; `d = 3`, `sz0` with `sz0.size 0 = 2097152`, `(𝔠,𝔡) = (1/6,1/10)`, `k = 1`, `bump`, `τU = 1/60`):
| target | in-file instance(s) | deterministic premises discharged | kept (other gates' pins) |
|---|---|---|---|
| 1 `unGreenCorrC` | `instance_unGreenCorrC_band`, `_baC` (mean `≠ 0` proved, `r_n = 1+1/(n+1)`) | size → ∞, `0 < c'`, dilation window | `UNClaim417C`, `UNApriori` (inside the pin) |
| 2 `greenCorrAllC` | `instance_greenCorrAllC_band`, `_baC` | same | same |
| 3 `step1Band_integral_ouPC` | `inst_step1Band_integral_ouPC` (∃ M, flow `≠ ouMat`), `_band` | `IsTestFun bump` | none |
| 4a/4b | `inst_step1BandC''_band`, `inst_step1Band_rowC''_band` | `Admissible`, `UNDens'`, `UNTrLocalInit'`, `UNMeanBound`, `τU = 𝔠𝔡 > 0` | `UNL32`, `UNGUELocal`, band `UNTrLocal`, `UNNormBound` |
| 5 | `inst_un_infty1RowC''_band_zero` (`E' = 0`), `_band_one` (`E' = 1`) | as 4 + `|E'| < 2` | as 4 |
| 6 | `inst_univMain_transferC_band`, `_nonzero_mean` | none needed | none |
| 7 | `inst_univMainRowC_band_zero`, `_nonzero_mean` | `UNGreenCorrAllC` (by target 2), `UNDens` | `UNTrLocal`, `UNClaimAllC` |
| 8 | `inst_unCoreC''_holds_band_zero` | `UNGreenCorrAllC`, `UNDens'`, `UNTrLocalInit'`, `UNMeanBound`, `E' = 0`, `1 ≤ k` | `UNL32`, `UNGUELocal`, `UNTrLocal`, `UNNormBound`, `UNClaimAllC` |
No `N = 0`, no empty index, no `False` premise. Auditor's nonzero-mean checks (dispatcher note (5)), in `auditcheck.lean`, compiled (exit 0):
```
open private GreenCorr_baC GreenCorr_baC_mean_ne from RBM3D.Universality.GreenCorr in
example : ∃ i j : Idx 3 (sz0.L 0) (sz0.W 0), (UNModelC.ba sz0).mean 0 i j ≠ 0 := by
  have e : GreenCorr_baC = UNModelC.ba sz0 := rfl
  rw [← e]; exact GreenCorr_baC_mean_ne
example : UNGreenCorrC sz0 (UNModelC.ba sz0) := greenCorrAllC 3 le_rfl sz0 GreenCorrCheck.sz0_size_tendsto (UNModelC.ba sz0)
example : UNGreenCorrC sz0 (UNModelC.ba sz0) := unGreenCorrC sz0 GreenCorrCheck.sz0_size_tendsto (UNModelC.ba sz0)
-- targets 4a, 5 (E' = 1), 8, 3, 6 at UNModelC.ba sz0 (n = 0 for 3, 6), each with UNDens'.mono .. un_dens'_msc_zero,
-- ⟨1, zero_le_one, hN, unMeanBound_ba sz0 UNInst.sz0_adm 1 one_pos⟩, UNInst.bump_testFun, greenCorrAllC (for 8); kept:
-- UNL32, UNGUELocal, UNTrLocal, UNTrLocalInit', UNNormBound .. 1, UNClaimAllC (BA rows). E.g. target 8:
example (...) : UNUnivDilAt sz0 (UNModelC.ba sz0).toUNModel (fun _ => rhoSC 0) 0 0 1 bump := unCoreC''_holds h32 hGL greenCorrAllC ...
-- consumer S5:
example : UNL32 → UNGUELocal → UNDensBARow' → UNTrLocalBARow → UNTrLocalInitBARow' → UNNormBARow → UNClaimRowBA →
    UNEMCTE2RowBA → UNJakUywRowBA → UNOURowBA → (∀ d, UNMLOutBA d) → UNLocAvgBA → UNQueBA → ∀ d, RBM.BA.BAEnd_BUnivL d :=
  fun h32 hGL rD rT0 rT rN rC rE rJ rO hML hLoc hQ =>
    baBUniv_of_rows unCoreC''_holds h32 hGL greenCorrAllC rD rT0 rT rN rC rE rJ rO hML hLoc hQ
```

## 6. Builds and axioms
```
$ lake build RBM3D.Universality.GreenCorr RBM3D.Universality.Step1Band RBM3D.Universality.UnivMain   (branch worktree)
✔ [3409/3411] Built RBM3D.Universality.Step1Band (7.9s)  ℹ [3408/3411] Built ...GreenCorr  ℹ [3411/3411] Built ...UnivMain
Build completed successfully (3411 jobs).   exit=0   (errors: 0; no warning in the three files)
$ lake build      (full, branch worktree)
info: RBM3D.lean:548:0: axiom audit: 14089 theorems, 4452 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 130 (borrowed 1, owed 64, structural 45, refuted 6, superseded 14).
Build completed successfully (4316 jobs).   exit=0   (errors: 0; 2:58.31)
$ lake env lean ax.lean   (#print axioms of the 24 added public declarations)
24 lines; 24 x "depends on axioms: [propext, Classical.choice, Quot.sound]"; no other line
```
H259 (4) / GMN-C2 (c), `#print axioms` in `G1dump.lean`, before (main ab435c6e) and after (t/T2477 2b1c9956):
```
main  : 'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
main  : 'RBM.Endpoints.bUniv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
branch: 'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
branch: 'RBM.Endpoints.bUniv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Identical. N3a (T2476) is not merged; if it merges first, the hub re-runs this comparison and the full build on that base.

## 7. Paper deltas
Lean/paper differences: (1) Step 1 and `(univ-main)` run on the centred flow, DBM data `λ(μ + e^{-t*/2}(H-μ))` (`vOUC`);
(2) the Green-function comparison holds for every model with a deterministic mean, from Claim (417) and the a priori bound.
Both are proposed in the prove report (d) as `T2477a`, `T2477b`. Target 5 at every `|E'| < 2` and the `τU ≤ 𝔠𝔡` window
are the merged pins' (T2187/T2213) and add no new difference. Coverage: complete.

## 8. Observations (no RETURN)
- `Step1Band.lean` has no `#print axioms` line (0); axioms checked by the scratch `ax.lean` (§6).

## Verdicts
Targets 1 `unGreenCorrC`, 2 `greenCorrAllC`, 3 `step1Band_integral_ouPC`, 4 `step1BandC''`/`step1Band_rowC''`,
5 `un_infty1RowC''`, 6 `univMain_transferC`, 7 `univMainRowC`, 8 `unCoreC''_holds`: PASS each; 9 instances, 10 registry: PASS.
Overall: **PASS**. No dispatcher sign-off needed.
