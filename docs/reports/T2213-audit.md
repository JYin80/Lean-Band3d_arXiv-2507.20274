Auditor model: claude-opus-5-5

# T2213 audit (UN-12b, C'' re-pin, C-form Step 1, conditional refutation) — round 1, Mon Oct  5 21:33:55 UTC 2026 (`date -u`)

Audit worktree `RBM3D-wt/T2213-audit1`, detached at `t/T2213` = 5fae3de (merge base with main ed9c0f1; main now 18a41d3).
Scratch files: scratchpad `T2213/` (not committed). No source edited.

## 1. Diff scope and registry edit
```
$ git diff --stat main...t/T2213
 RBM3D/Test/Axioms.lean         |   11 +-
 RBM3D/Universality/PinsC2.lean | 1711 ++++++++++++++++++++++++++++++++++++++++
$ git diff main...t/T2213 -- RBM3D/Test/Axioms.lean   (hunks, abridged to +/- lines)
-   `RBM.Univ.UNTrLocalInit, -- ... (T2187, UN-01b: owed)
-   `RBM.Univ.UNStep1GoodC', -- ... (T2201, UN-01c: owed; UN-12 or a BA-N ticket)
-   `RBM.Univ.UNCoreC', -- ... (T2201, UN-01c: owed; BA-C1b)
+   `RBM.Univ.UNTrLocalInit', -- ... tolerance W^τ (Bctl + t*) (T2213, UN-12b: owed; band: unTrLocalInit'_band_zero; BA: BA-C1b row)
+   `RBM.Univ.UNCoreC'', -- ... successor of the superseded UNCoreC' (T2213, UN-12b: owed; BA-C1b)
+   `RBM.Univ.UNMeanBound, -- ... (T2213, UN-12b; DECISIONS §69)          [structuralProps, after UNDens']
-   `RBM.Univ.UNCoreC]       -- ...
+   `RBM.Univ.UNCoreC,       -- ...
+   `RBM.Univ.UNTrLocalInit, -- false for the band model ... successor `UNTrLocalInit'`
+   `RBM.Univ.UNStep1GoodC', -- false: `not_UNStep1GoodC'_of_diag` ... successor `UNStep1GoodC''` (proved: `step1GoodC''`)
+   `RBM.Univ.UNCoreC']      -- superseded, not shown false ... successor `UNCoreC''`
$ python3 cnt.py   (entries per list, git show <ref>:RBM3D/Test/Axioms.lean)
main {'borrowedProps': 2, 'owedProps': 148, 'structuralProps': 79, 'refutedProps': 4}
t/T2213 {'borrowedProps': 2, 'owedProps': 147, 'structuralProps': 80, 'refutedProps': 7}
```
Exactly the two sole writable files; the `Axioms.lean` edit is the ticket's text (owed -3 +2, structural +1, refuted 4 → 7). No merged
declaration changed (no other file in the diff); `PinsC2.lean` imports `RBM3D.Universality.Step1Good`, `Mathlib.Analysis.Matrix.{PosDef,Spectrum}` only.

## 2. Statements against the pins (script diffs)
```
$ python3 subdiff.py   (merged pin text + exactly the ticket's substitutions, vs PinsC2.lean; whitespace-normalised)
  def UNTrLocalInit: 'sz.Bctl n (1 - z.im) <' occurs 1
PinsK.lean def UNTrLocalInit -> def UNTrLocalInit' IDENTICAL
  def UNStep1GoodC': 'UNTrLocalInit sz' occurs 1 ; 'UNNormBound sz M.toUNModel CV₀ →' occurs 1
PinsDens.lean def UNStep1GoodC' -> def UNStep1GoodC'' IDENTICAL
  def UNCoreC': 'UNTrLocalInit sz' occurs 1 ; 'UNNormBound sz M.toUNModel CV₀)' occurs 1
PinsDens.lean def UNCoreC' -> def UNCoreC'' IDENTICAL
$ python3 pindiff.py   (check file T2213-check.lean sections 2-3 vs PinsC2.lean; `Type*`→`Type`)
def UNTrLocalInit' IDENTICAL / def UNMeanBound IDENTICAL / def UNStep1GoodC'' IDENTICAL / def UNCoreC'' IDENTICAL
un_eigenvalues_abs_le_convex IDENTICAL       un_exists_eigenvalues_eq_diagonal IDENTICAL   stieltjesN_diagonal IDENTICAL
stieltjesN_vert_le IDENTICAL                 mV_vOUC IDENTICAL                             stieltjesN_ouInit_toC IDENTICAL
unTrLocalInit'_of_unTrLocal IDENTICAL        unTrLocalInit'_band_zero IDENTICAL            not_UNStep1GoodC'_of_diag IDENTICAL
step1GoodC''_det IDENTICAL                   inst_diag_model IDENTICAL                     inst_unTrLocalInit'_band IDENTICAL
inst_step1GoodC''_band IDENTICAL             inst_coreC_band'' IDENTICAL
```
`UNDens'.mono`, `UNTrLocal.mono`, `unMeanBound_toC` state their hypotheses before the colon (not text-comparable); checked by elaboration:
```
$ lake env lean audcheck.lean   (check file with `import RBM3D.Universality.PinsC2` added, plus 22 auditor lines:
    4 × `example : @<pin> = @RBM.Univ.<pin> := rfl`; 17 × `example : T2213_<name> := @RBM.Univ[.PinsC2Inst].<name>`
    for every name of section 3 incl. the 3 monotonicity/mean lemmas and the 4 instances; `example : RBM.Univ.UNStep1GoodC'' := RBM.Univ.step1GoodC''`)
exit 0 ; lines containing "error": 0
```
Quantifier order: fixed data `(d, 𝔠, 𝔡, sz, M, m, E, ρ, δ, CV₀)` and `(τs, D)` before `∃ c C`, then `∀ᶠ n`, as the merged
`UNStep1GoodC'`; `step1GoodC''_det` has `∃ c C` before `∀ᶠ n, ∀ ω` and the two `ω`-events as hypotheses inside, as pinned.
`step1GoodC''` has type exactly `UNStep1GoodC''` (the pin is proved, not assumed).

## 3. Hidden hypotheses, vacuity, cycles
- New structures: none. `diagModel` (namespace `PinsC2Inst`) fills the merged `UNModelC` fields with `Sizes.seqP sz`, `inferInstance`,
  `PinsC2_diag_herm`, `measurable_const` — no Prop field assumed.
- `UNMeanBound` is a condition on data (structural, DECISIONS §69); `UNTrLocalInit'`, `UNCoreC''` owed. Registry pre-check:
```
$ printf 'import RBM3D\nimport RBM3D.Universality.PinsC2\n#assert_rbm_axioms\n' > reg.lean; lake env lean reg.lean   → exit 0
axiom audit: 6351 theorems, 2203 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 128 (borrowed 1, owed 96, structural 25, refuted 6).
registry: 2 borrowed + 147 owed + 80 structural + 7 refuted; 108 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
$ grep -oE "RBM\.Univ\.(UNTrLocalInit'|UNCoreC''|UNMeanBound|UNStep1GoodC'')[^,\]]*" reg.out | sort | uniq -c
   1 RBM.Univ.UNCoreC'': 1 [no certificate
   1 RBM.Univ.UNMeanBound
   1 RBM.Univ.UNTrLocalInit'
   1 RBM.Univ.UNTrLocalInit': 3 [no certificate
```
  No "unregistered premise" line; `UNStep1GoodC''` is not a premise anywhere (proved), consistent with T2213a.
- Cycles: none; the only project import is the merged `Step1Good` (UN-12, a42cad0). `UNCoreC''` is a hypothesis only of `inst_coreC_band''`.
- Non-vacuity of the pins: `UNStep1GoodC''`'s hypotheses are jointly met at the band data (`inst_step1GoodC''_band`, deterministic ones
  discharged); `UNCoreC''`'s deterministic hypotheses are discharged in `inst_coreC_band''`.
- External hypotheses kept by the instances (`UNLocAvgBand`, `UNTrLocalBandRow`, `UNNormBandRow`, `UNL32`, `UNGUELocal`, `UNGreenCorrAllC`,
  `UNClaimAllC`, the band local law at `1/2`, `UNNormBound`) each have a limit/number row in prove report (a) "External hypotheses" (O3).

## 4. Compiled nonempty instances (from `PinsC2.lean`, all compiled in the module build of §5)
| target | instance | data / discharged |
|---|---|---|
| pins, `step1GoodC''`, `UNDens'.mono`, `unMeanBound_toC` | `inst_step1GoodC''_band` | `sz0`, `𝔠=1/6`, `𝔡=1/10`, `(band sz0).toC`, `msc`, `E=0`, `δ=1/4`, `τs=1/60`, `D=1`; `sz0_adm`, `UNDens'.mono … un_dens'_msc_zero`, `unMeanBound_toC`, `norm_num` side conditions; kept: `UNLocAvgBand`, `UNTrLocalBandRow`, `UNNormBandRow` |
| `step1GoodC''_det` | `inst_step1GoodC''_det_band` | same data, `CV₀ = 1`; all hypotheses before `∃ c C` discharged (`ω`-events are part of the statement) |
| `unTrLocalInit'_band_zero`, `unTrLocalInit'_of_unTrLocal` | `inst_unTrLocalInit'_band` | `sz0`; local law from `UNTrLocalBandRow` at `κ=1`, `E=0`, `δ=1/2`; `K`, `Lp` discharged inside `band_zero` |
| `UNCoreC''`, `UNTrLocal.mono` | `inst_coreC_band''` | `E'=0`, `k=1`, `bump`, `bump_testFun`, `UNTrLocal.mono`, `unTrLocalInit'_band_zero`, `unMeanBound_toC`; kept: `UNCoreC''` and other gates' pins |
| matrix facts, `mV_vOUC`, `stieltjesN_ouInit_toC` | `inst_un_eigenvalues_abs_le_convex`, `inst_un_exists_eigenvalues_eq_diagonal`, `inst_stieltjesN_diagonal`, `inst_stieltjesN_vert_le`, `inst_mV_vOUC`, `inst_stieltjesN_ouInit_toC` | `Fin 3` diagonals `(1,2,3)`, `(2,-1,1/2)`, `(-1,1,0)`, `a = 1/3`, `R = 2`, `z = i, 2i`; band `sz0`, `n = 0`; no hypothesis left |
| `not_UNStep1GoodC'_of_diag` | `inst_diag_model` (ticket's required instance; structural hypotheses for every `γ`), `inst_not_UNStep1GoodC'_diag` | `sz0`, `msc`, `E=0`, `δ=1/4`, `CV₀=1`; `UNDens'` discharged; kept: `UNStep1GoodC'` (the refuted pin), `UNTrLocalInit`, `UNNormBound` of `diagModel sz0 γ` (see Observation 1) |

No `N = 0`, empty index, collapsed window (`δ = 1/4 > 0`, `δ' = 1/2`), or `False` premise among the discharged data.

## 5. Build, axioms, hygiene
```
$ lake build RBM3D.Universality.PinsC2 RBM3D.Test.Axioms      (audit worktree)
Build completed successfully (3344 jobs).   exit 0 ; lines with "error": 0
warnings in PinsC2.lean: 20 × "This line exceeds the 100 character limit" (lines 13-45, module docstring)
$ lake build RBM3D        (root as committed, branch Axioms.lean)    exit 0
info: RBM3D.lean:256:0: axiom audit: 6325 theorems, 2198 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
registry: 2 borrowed + 147 owed + 80 structural + 7 refuted; 110 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
Build completed successfully (4016 jobs).
$ lake env lean ax.lean   (#print axioms of all 31 public declarations of PinsC2.lean, generated by grep of ^theorem/^def)
exit 0 ; 31 of 31 lines "depends on axioms: [propext, Classical.choice, Quot.sound]" ; other lines: 0
$ grep -nE "sorry|admit|native_decide|^axiom|[^a-zA-Z_]axiom " RBM3D/Universality/PinsC2.lean   → no match (exit 1)
$ grep -n maxHeartbeats PinsC2.lean → 581, 1336 (`set_option maxHeartbeats 1000000 in`, two declarations)
$ name-clash: git grep -nF <name> main -- RBM3D RBM3D.lean, for the 18 new public names, `diagModel`, `PinsC2` → 0 hits each
$ git grep -c "^private" PinsC2.lean → 43 (helpers `PinsC2_*`)
```

## 6. Paper deltas
Prove report (d) proposes T2213a (registry: `UNStep1GoodC''` proved, not registered), T2213b (refuted-class wording), T2213c (`τs < 2/3`
at `τ = τs/8`), T2213e/f (proof-route constants only), T2213g (`UNTrLocalInit'` tolerance `W^τ(Bctl + t*)` vs (G_bound_ave), window
`1/2 → 1/4` in `unTrLocalInit'_band_zero`), T2208b. The re-pin itself and `UNMeanBound`'s class are recorded in DECISIONS §69.
Covered except as in Observation 2.

## 7. Verdicts
| target | verdict |
|---|---|
| 1 pins `UNTrLocalInit'`, `UNMeanBound`, `UNStep1GoodC''`, `UNCoreC''` | PASS |
| 2 `un_eigenvalues_abs_le_convex`, `un_exists_eigenvalues_eq_diagonal`, `stieltjesN_diagonal`, `stieltjesN_vert_le`, `mV_vOUC`, `stieltjesN_ouInit_toC` | PASS |
| 3 `UNDens'.mono`, `UNTrLocal.mono`, `unMeanBound_toC` | PASS |
| 4 `unTrLocalInit'_of_unTrLocal`, `unTrLocalInit'_band_zero` | PASS |
| 5 `not_UNStep1GoodC'_of_diag` (conditional refutation; a special case, not the general T2208a refutation — as the ticket states) | PASS |
| 6 `step1GoodC''_det`, `step1GoodC''` | PASS |
| 7 instances `inst_diag_model`, `inst_unTrLocalInit'_band`, `inst_step1GoodC''_band`, `inst_coreC_band''` | PASS |
| registry edit (`Test/Axioms.lean`) | PASS |

Overall: **PASS**. No dispatcher sign-off needed.

## 8. Observations (no RETURN)
1. `inst_not_UNStep1GoodC'_diag` keeps `UNNormBound sz0 (diagModel sz0 γ).toUNModel 1` for an arbitrary `γ`. A bounded `γ`
   (`∀ n i, |γ n i| ≤ 2`) would let it be discharged with the file's own `PinsC2_eig_diag_abs`; the joint satisfiability with
   `UNTrLocalInit` (semicircle quantiles) stays argued as the ticket allows ("Only `UNTrLocalInit` … is not compiled"). The ticket's
   required instance for this target, `inst_diag_model`, is present with every hypothesis discharged.
2. `UNMeanBound` (new hypothesis of `UNStep1GoodC''`, `UNCoreC''`) has no dedicated paper-delta candidate; it is decided in DECISIONS §69
   and registered structural. Suggest the dispatcher name it in the T2213a/T2213g entry (as D512 did for `UNDens'`).
3. Main has advanced to 18a41d3 since the merge base ed9c0f1; at merge, `Axioms.lean` follows the ticket's union rule
   (`UNTrLocalInit`, `UNStep1GoodC'`, `UNCoreC'` must not be in `owedProps`).
