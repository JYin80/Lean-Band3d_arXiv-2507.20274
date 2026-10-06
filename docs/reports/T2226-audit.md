Auditor model: claude-opus-5-5
# T2226 audit (round 1) — UN-14 `Universality/GUETranslation` — written Tue Oct  6 00:01:37 UTC 2026
Branch `t/T2226` = e8d327b (merge-base with main 0d5868e). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2226-audit1`
(detached at e8d327b); scratch files in the scratchpad `T2226/`.

## 1. Scope of the diff
```
$ git diff --name-status main...t/T2226
M	RBM3D/Test/Axioms.lean
A	RBM3D/Universality/GUETranslation.lean
$ git diff main...t/T2226 -- RBM3D/Test/Axioms.lean   (changed lines only)
-   `RBM.Univ.UNInfty1Row', -- bulk universality pin, primed successor of the refuted UNInfty1Row (T2201, UN-01c: owed; UN-14)
+   `RBM.Univ.GUEGoodAt, -- bulk universality: the GUE-side good event (...), an event on the data; a hypothesis of
    `guetranslation_core`, `guetranslation_uniform` (T2226, UN-14; DECISIONS §20: condition on data, as `IsRegular32`)
$ git diff 0d5868e main --stat -- RBM3D/Test/Axioms.lean RBM3D.lean
 RBM3D.lean | 3 +++
```
Only the two sole writable files. No merged signature touched. The owed line is deleted as the ticket asks. The added
`structuralProps` line for `GUEGoodAt` is the case the ticket allows ("if the pre-check flags a premise, append it
(one line, one comment) and report"). It is reported as T2226c.

## 2. Hygiene
```
$ grep -nE 'sorry|admit|native_decide|^axiom|set_option' RBM3D/Universality/GUETranslation.lean
38:set_option linter.style.longLine false
39:set_option linter.unusedSectionVars false
$ grep -nE '^import' RBM3D/Universality/GUETranslation.lean
6:import RBM3D.Universality.Step1Band
7:import RBM3D.Universality.Step1RegularityGUE
8:import Mathlib.Order.Filter.AtTopBot.Archimedean
```
The public declarations are only the pinned names plus extra instances in `RBM.Univ.GUETranslationInst`. There are 22
helpers, all `private` with the prefix `GUETranslation_`.
```
$ for n in UNGUETranslation guetranslation un_infty1Row "un_core'_of_univMainRow" GUETranslationInst GUETranslation_; do git grep -nF "$n" main -- RBM3D RBM3D.lean | wc -l; done
0 0 0 0 0 0
```

## 3. Build (audit worktree)
```
$ lake build RBM3D.Universality.GUETranslation
✔ [3368/3368] Built RBM3D.Universality.GUETranslation (6.5s)
Build completed successfully (3368 jobs).
exit=0      (0 lines starting with `error`; no warning in GUETranslation.lean; the olean was absent from main's cache, so this was a fresh build)
```

## 4. Statements against the pin (check file sections 2.1-2.5, compiled)
The scratch file `AuditCheck.lean` (173 lines) contains:
- `import RBM3D.Universality.GUETranslation`;
- check-file lines from `noncomputable section` to the end of section 2, verbatim (`sed`);
- 2 `Iff.rfl` lines and 12 `example : T2226Check.T2226_<name> := <library name>` lines;
- `#print axioms` of all 19 public theorems.
```
example : T2226Check.UNGUETranslation ↔ UNGUETranslation := Iff.rfl      (and the same for UNGUETranslationRow)
example : T2226Check.T2226_<x> := <x>     for x in guetranslation_integral_gue, guetranslation_core, guetranslation_uniform,
  guetranslationRow, guetranslation, un_infty1Row'_of_translation, un_infty1Row', un_core'_of_univMainRow, and
  GUETranslationInst.{inst_dilation_ne_one, inst_guetranslation_sz0, inst_un_infty1Row'_band_zero, inst_un_infty1Row'_band_one}
$ lake env lean AuditCheck.lean ; echo exit=$?
exit=0      (no error lines; output = the axiom lines of §5 only)
```
All 14 pins are matched at the type level: the 2 vocabulary Props by `Iff.rfl`, and the 12 theorem and instance bodies.
The prover's whitespace diff (report b.5) also says "ALL IDENTICAL".

Mathematical reading of the pinned statements (checked against `Pins.lean:552` `UNInfty1` and `PinsDens.lean:88` `UNInfty1Row'`):
- `UNGUETranslation` compares the GUE at `0`, with the test function dilated by `ρ_sc(0)/ρ_sc(E)`, against the GUE at `E`.
  This is the right direction, because the local spacing at `E` is `1/ρ_sc(E)`.
  The order of the quantifiers is: fixed `d, sz, k, κ, E, O`, then `n → ∞`.
  The bulk condition is `|E| ≤ 2-κ` with `0<κ`. There is no `τ_U` and no `Admissible`, as the design says (§29 (3)).
- `un_infty1Row'` is the merged pin `UNInfty1Row'` unchanged. It is the general statement, not a special case or adapter:
  it holds for all `d ≥ 3`, all admissible `sz`, all `M`, and all `E'` with `|E'| < 2`.
  It is assembled from `step1Band_row` (merged; takes `UNDens'`) and `UNGUETranslation` at `κ=(2-|E'|)/2`. The proof is
  `smul_smul`, then `Tendsto.add`, then `ring` (file :763-785).

## 5. Axioms
```
$ (lake env lean AuditCheck.lean, 19 `#print axioms` lines) | join wrapped lines | grep -c "depends on axioms: [propext, Classical.choice, Quot.sound]"
19
$ ... | grep -v "[propext, Classical.choice, Quot.sound]" | wc -l
0
names: the 8 targets 1-4c + 11 GUETranslationInst instances (inst_dilation_ne_one, inst_guetranslation_sz0,
inst_guetranslationRow_sz0, inst_guetranslation_integral_gue_sz0, inst_good_nonempty_sz0, inst_guetranslation_core_sz0,
inst_guetranslation_uniform_sz0, inst_un_infty1Row'_of_translation_band_zero, inst_un_infty1Row'_band_zero,
inst_un_infty1Row'_band_one, inst_un_core'_band_zero)
```

## 6. Registry pre-check (root audit with the merge import)
At the branch head alone, `lake build RBM3D` fails at the root audit. This is expected: the owed line is gone, but the
root import is not yet there.
```
$ lake build RBM3D
error: RBM3D.lean:269:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of ...:
  [RBM.Univ.UNInfty1Row']
build_exit=1
```
Scratch root `Root2.lean` = the import lines of the branch's `RBM3D.lean` + `import RBM3D.Universality.GUETranslation`
after the last import + the root's trailing `#assert_rbm_axioms`. This is the state that hub step (A)4 produces.
```
$ lake env lean Root2.lean     (Tue Oct  6 00:00:42 UTC 2026)
axiom audit: 6614 theorems, 2243 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms: ...
  RBM.Univ.UNL32: 29 [no certificate]          (borrowed)
  RBM.Univ.UNGUELocal: 38 [no certificate]     (owed)
exit=0 ; lines containing `error`: 0 ; lines containing UNInfty1Row' / GUEGoodAt / UNGUETranslation: 0
```
**Merge note for the hub:** the root import line is required for the full build to pass (rule (A)4 adds it).
Main has moved by 3 root imports since the base, and `Test/Axioms.lean` is unchanged on main since 0d5868e.

## 7. Per-target verdicts

| target | statement vs pin | hidden hyp / vacuity / cycle | compiled nonempty instance | verdict |
|---|---|---|---|---|
| 1 `guetranslation_integral_gue` | identical (§4) | no premise beyond `IsTestFun O` | `inst_guetranslation_integral_gue_sz0`: `sz0`, `n=0` (`L=4, W=32, N=2^21`), `τs=1/2`, `E₀=1`, `bump` | PASS |
| 2a `guetranslation_core` | identical | `GUEGoodAt` is a `def` (an event on the data), not a structure field. It is nonempty by `inst_good_nonempty_sz0` (from `gueGoodHighProb`, `D=1`) | `inst_guetranslation_core_sz0`: produces `ω` with eventual `GUEGoodAt` at `(κ,τs,E₀)=(1,1/2,1)` and applies the core | PASS |
| 2b `guetranslation_uniform` | identical | as 2a; `UNGUEGoodHighProb` is discharged by the merged `gueGoodHighProb` | `inst_guetranslation_uniform_sz0` (`ε=1`) | PASS |
| 3a `guetranslationRow` | identical | — | `inst_guetranslationRow_sz0` (`k=1`, `κ=1`, `E=1`, `bump`) | PASS |
| 3b `guetranslation` | identical | `UNL32` (borrowed), `UNGUELocal` (owed) are premises of the pinned Prop | `inst_guetranslation_sz0`; dilation `≠ 1` by `inst_dilation_ne_one` | PASS |
| 4a `un_infty1Row'_of_translation` | identical | deps `step1Band_row`, `isTestFun_comp_smul`, `rhoSC_pos` (all merged). No cycle: `un_infty1Row'` uses only `guetranslation` | `inst_un_infty1Row'_of_translation_band_zero` | PASS |
| 4b `un_infty1Row'` | identical; closes the owed pin | as 4a | `inst_un_infty1Row'_band_zero` (band, `msc`, `E=0`, `δ=1/2` by `un_dens'_msc_zero`, `E'=1 ≠ E`); `inst_un_infty1Row'_band_one` (`E=E'=1`, `κ=1/2`, `δ` from `unDensBandRow'_of_row`) | PASS |
| 4c `un_core'_of_univMainRow` | identical | `un_core_of_rows' un_infty1Row'` | `inst_un_core'_band_zero` | PASS |
| 5 instances (2.5) | identical (4 pinned + 7 extra) | — | — | PASS |

In every instance, all deterministic hypotheses are discharged at concrete data: `3 ≤ 3`; `sz0_adm` (`𝔠=1/6`, `𝔡=1/10`);
`inst_sz0_size_tendsto`; `|1| ≤ 2-1`, `|1| < 2`, `0 < 1/2 ≤ κ/2`; `bump_testFun`; `UNDens'` via `un_dens'_msc_zero` or `unDensBandRow'_of_row`.

The premises kept are other gates' pins only: `UNL32`, `UNGUELocal`, `UNLocAvgBand`, `UNTrLocalBandRow`, `UNNormBandRow`,
`UNDensBandRow`, `UNUnivMainRow`, `UNGreenCorrAll`, and `UNClaimAll sz0 (band) 0`. In `inst_guetranslationRow_sz0` the
merged `UNGUEGoodHighProb` is also kept as a premise, because it is the Row shape.

There is no degenerate data: `N_0 = 2^21`, `k = 1`, `E' = 1 ≠ E = 0`, `ρ_sc(0)/ρ_sc(1) ≠ 1`.

No new external hypothesis is introduced. The only hypotheses are `UNL32` (already borrowed; its limit check is in T2162)
and the owed `UNGUELocal`.

## 8. Paper deltas
The targets add no Lean/paper statement difference. Existing coverage:
- `UNInfty1Row'` is the merged pin = `(1infyuniv)` (`1-2:344`) with `UNDens'`; its registry classes are in D512.
- `UNGUELocal` and the GUE-side inputs are in D383 (T2162b).
The report proposes non-statement candidates T2226a (design table: UN-08 transitive only), T2226b (internal
`τs = 1/2`, proof-internal, as RBM2D #139), T2226c (`GUEGoodAt` registered structural; dispatcher may reclassify).
Coverage is complete.

## 9. Observations (no RETURN)
- O1. Prove report b.9 says the Lipschitz window is `[ρ_sc(E₀)/2, 3ρ_sc(E₀)/2]`, not the ticket design's
  `[ρ_sc(E₀)/2, 2ρ_sc(E₀)]`. This is proof-internal and changes no statement.
- O2. The registry gained one `structuralProps` line (`GUEGoodAt`), where the ticket said "expected: no new line". The
  ticket's own fallback allows this; recorded as T2226c, classification left to the dispatcher (not a sign-off blocker).

## Verdict
**PASS** for all targets (1, 2a, 2b, 3a, 3b, 4a, 4b, 4c, 5). No dispatcher sign-off needed.
