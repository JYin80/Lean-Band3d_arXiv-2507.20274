Auditor model: claude-opus-5-5

# T2241 audit (BA-C1b, `RBM3D/BA/UNPins.lean`), round 1

Branch `t/T2241` at `3eeab33`; detached audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2241-audit1`; scratch in `scratchpad/T2241/`.
All commands below were run by the auditor in the audit worktree.

## 1. Diff scope (sole writable files)
```
$ git diff --stat main...t/T2241
 RBM3D/BA/UNPins.lean   | 1312 ++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean |   12 +
$ git diff main...HEAD -- RBM3D/Test/Axioms.lean   (all 12 lines are additions inside `owedProps`)
+   -- T2241 (BA-C1b, DECISIONS §20): the UN-side block Anderson pins (`RBM3D/BA/UNPins.lean`)
+   `RBM.Univ.UNLocAvgBA, ... owner BA-M1        +   `RBM.Univ.UNMLOutBA, ... owner BA-V3
+   `RBM.Univ.UNOURowBA / UNEMCTE2RowBA / UNJakUywRowBA / UNClaimRowBA, ... owner the model-generic UN rows at `UNKind.ba`
+   `RBM.Univ.UNDensBARow', ... owner BA-C2      +   `RBM.Univ.UNTrLocalBARow / UNTrLocalInitBARow' / UNNormBARow, ... owner BA-N1
+   `RBM.BA.BAEnd_QUEL, ... owner BA-M3
```
This is exactly the expected `owedProps` list of the ticket (11 names). `UNQueBA`, `BAEnd_BUnivL`, `UNMeanBound` are not registered, as the ticket requires. No merged file is modified, and no frozen signature is touched.

## 2. Build, axioms, hygiene
```
$ lake build RBM3D.BA.UNPins
Build completed successfully (3748 jobs).        exit 0   (grep -c "UNPins.lean" build.out -> 0: no warning/error in the file)
$ lake build RBM3D                                -> Build completed successfully (4043 jobs).  exit 0
$ printf 'import RBM3D\nimport RBM3D.BA.UNPins\n#assert_rbm_axioms\n' > pre_audit.lean; lake env lean pre_audit.lean   -> exit 0
axiom audit: 7038 theorems, 2377 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; ...
  RBM.Univ.UNLocAvgBA: 8 [no certificate]      RBM.Univ.UNMLOutBA: 7       RBM.Univ.UNOURowBA: 6
  RBM.Univ.UNEMCTE2RowBA: 5   RBM.Univ.UNJakUywRowBA: 5   RBM.Univ.UNClaimRowBA: 4   RBM.Univ.UNDensBARow': 3
  RBM.Univ.UNTrLocalBARow: 2  RBM.Univ.UNTrLocalInitBARow': 3   RBM.Univ.UNNormBARow: 3   RBM.BA.BAEnd_QUEL: 3
$ lake env lean ax_audit.lean   (collectAxioms over every non-internal constant of module RBM3D.BA.UNPins)
declarations in RBM3D.BA.UNPins (non-internal): 109; with a non-standard axiom: []
'RBM.Univ.unMeanBound_ba' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.baBUniv_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.un_claimAll_of_rowsBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.UNQueBA_of_BAEnd_QUEL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.ouMatC_ba_eq_ouMat' / 'admissible_lamHat' / 'unBadYBA_measure_le' / 'BAInst.inst_univ_ba' /
'RBM.Univ.BAInst.inst_step1GoodC''_ba' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nwE "sorry|admit|axiom|native_decide" RBM3D/BA/UNPins.lean   -> no output
$ grep -n "seqP sz\b\|sz.seqP" RBM3D/BA/UNPins.lean                   -> no output (exit 1)   [§57 (3)]
$ grep -n "^private" RBM3D/BA/UNPins.lean  -> UNPins_eig_le_rowsum, UNPins_psiI_rowsum, UNPins_one_le_Nsz,
                                               UNPins_normBound_mono, UNPins_hg_3_10, UNPins_hg10   [all prefixed, §3 (E)]
```
The file imports exactly the four RBM3D modules and three Mathlib modules that the ticket allows (lines 6-12).

## 3. Statements against the pins (independent compiled comparison)
The auditor's own scratch file `acc_audit.lean` is the check file `docs/tickets/checks/T2241-check.lean` with `import RBM3D.BA.UNPins` added, followed by 38 generated `example`s:
- `KBA @UNModelC.ba d = UNKind.ba d := rfl` and `UNModelCba_spec @UNModelC.ba := @UNModelC.ba_spec`;
- 9 Mba-pins (`UNQueBA`, `UNLocAvgBA`, `UNOURowBA`, `UNEMCTE2RowBA`, `UNJakUywRowBA`, `UNClaimRowBA`, `UNTrLocalBARow`, `UNTrLocalInitBARow'`, `UNNormBARow`) by `rfl`;
- `UNMLOutBA`, `UNDensBARow'`, `lamHat`, `BAqueConclL`, `BAEnd_QUEL`, `BAEnd_BUnivL` by `rfl`;
- 21 `X_stmt (@UNModelC.ba) := @X` for every `_stmt` of check section 3: 15 Mba-statements and 6 Mba-free ones, with `BASelf_msc` in `RBM.BA`.
```
$ lake env lean scratchpad/T2241/acc_audit.lean > acc_audit.out 2>&1; echo "exit $?"; grep -E "error" acc_audit.out
38
exit 0
```
So every pinned definition is definitionally the check-file pin, and every target theorem has exactly the check-file statement. This covers the hypotheses, the quantifier order (fixed parameters before `∀ᶠ n`), the bulk `∀ᶠ n, BAbulk`, the law `Sizes.seqP (sz.withLam 0)`, the window and the dimension `3 ≤ d`. Two signatures are more general than the check file, and both compile against it:
- `unBadYBA_measure_le` uses `{Ω : Type*}` where the check file has `Type`;
- `admissible_lamHat` has an explicit `{sz}` binder.

Verbatim check against the probe: whitespace-normalised and word-diffed by the auditor, on `git show a543154:RBM3D/Probe/T2173Pins.lean`, 4045 lines.
```
IDENTICAL UNMLOutBA, lamHat, unBadY_subset', SBR_zero_ne, unBadYBA_subset, unBadYBA_measure_le, fp, fp_kappa_pos, clsSz,
          clsSz_L_le_W, clsSz_tendsto, clsSz_bandwidth, clsSz_WO, clsSz_admissible, clsS, clsκ, clsκ_pos
DIFFERS   admissible_lamHat   insert  probe: (none) | file: {sz : Sizes d}           [probe had `variable {sz}`]
DIFFERS   cls_bulk            delete  probe: (huniq : BAmUniqReal 3) | file: (none)  replace huniq -> baMUniqReal_holds 3
```
Both differences are listed substitutions: `huniq` is removed by the ticket, and the binder form does not change the statement.

R3 and the new proof. `UNCoreC''` (`PinsC2.lean:106`) asks for the conjunct `∃ CV₀, 0 ≤ CV₀ ∧ UNNormBound … CV₀ ∧ UNMeanBound sz M CV₀`.
- `baBUniv_of_rows` (lines 367-380) supplies `⟨CV₀+1, _, UNPins_normBound_mono hN _, unMeanBound_ba sz hA _ _⟩`. `CV₀` comes from `rN`, and `UNDens'`, `UNTrLocal` and `UNTrLocalInit'` come from the rows at `δ₀`.
- `unMeanBound_ba` (lines 285-304) bounds every eigenvalue of `(UNModelC.ba sz).mean_herm n` (the field that `UNMeanBound` reads) by the maximal row sum. The chain is `2d·λ_n ≤ 2d·𝔡⁻¹ ≤ N^{CV₀}`, eventually:
  - the row sum is `2d` by `RBM.card_adj` with `sz.three_le_L`;
  - `λ_n ≤ 𝔡⁻¹` is the WO component of `Admissible`;
  - `N^{CV₀} → ∞` comes from `tendsto_rpow_atTop`, using `0 < CV₀`.

  This is the ticket's route (R3), and it needs no extra hypothesis.

## 4. Vacuity, hidden hypotheses, cycles
- **Structures.** `UNModelC.ba` fills the only Prop field, `mean_herm`, with a proof (lines 67-70; `PsiI_isHermitian`). `UNKind` (`PinsK.lean:307`) has no Prop field other than the `bulk` predicate, which is data and is set to `BAbulk`. No hypothesis is hidden in a structure.
- **Refuted pins.** The ticket's grep:
  ```
  $ grep -nw "UNStep1Good\|UNInfty1Row\|UNStep1GoodC\|UNCoreC\|UNTrLocalInit\|UNStep1GoodC'\|UNCoreC'" RBM3D/BA/UNPins.lean
  ```
  It gives 17 lines. The code lines among them are 185 (`UNTrLocalInit' …`), 367 (`(hcore : UNCoreC'')`) and 1063 (same). Each is the merged primed successor that the ticket mandates (R2, R3); `grep -w` matches it because `'` is not a word character. With PCRE excluding a trailing `'`/word character:
  ```
  23, 29, 30, 176   (all docstring lines)
  ```
  No refuted pin occurs in any statement or hypothesis.
- **Cycles.** All dependencies are merged on `main`, and the full library plus `UNPins` builds (§2). The only new proof obligations discharged inside the file are `mean_herm`, `unMeanBound_ba` and the `rfl`/algebraic facts of targets 5-7. Everything else is an explicit hypothesis that is registered as owed. `baBUniv_of_rows` concludes `BAEnd_BUnivL`, which is not among its hypotheses.

## 5. Compiled nonempty instances (target 8 and one per endpoint theorem)
The data are `S0 = clsS 4 _ (3/10)`, at `d = 3`, `L = 4`, `0 < λ = g0 ≤ 3/10` (`clsSz`, lines 776-783: `W_n = (2(n+1))^5`). `S0_adm : S0.Admissible (1/6) (1/10)` and `S0_bulk : ∀ᶠ n, BAbulk 3 … κ* E*` are proved with no hypothesis. `κ* > 0` is proved by `clsκ_pos`.
```
target                                  instance (line)                       hypotheses left (all other-gate / owed pins)
UNModelC.ba_spec, UNKind.ba_M           inst_UNModelC_ba_spec (1215)          none; mean λΨ ≠ 0 (inst_ba_mean_ne_zero)
un_claimAll_of_rowsBA                   inst_claimAll_ba (1052)               rC rE rJ rO hML hLoc hQ
unMeanBound_ba                          inst_unMeanBound_ba (1113)            none (CV₀ = 1/2)
UNQueBA_of_BAEnd_QUEL                   inst_UNQueBA_of_BAEnd_QUEL (1238)     ∀ d, BAEnd_QUEL d
baBUniv_of_rows                         inst_univ_ba (1063)                   UNCoreC'' UNL32 UNGUELocal UNGreenCorrAllC + 11 BA pins; k=1, O=UNInst.bump, E'=0
step1GoodC'' at BA (R5)                 inst_step1GoodC''_ba (1120)           rD rT rN hLoc; τs = 1/100 ≤ 𝔠𝔡 = 1/60, D = 1
ouMatC_ba_eq_ouMat                      inst_ouMatC_ba_eq_ouMat (1093)        none; s = t*, plus lamHat ≠ lam (model really shifted)
ouP_ba_withLam, ouP_ba_eq_band          inst_ouP_ba (1247)                    none
ouMatC_ba_eq_band_add, ouInit_ba        inst_ouMatC_ba_eq_band_add, inst_ouInit_ba   none
admissible_lamHat                       inst_admissible_lamHat (1077)         none; 0 ≤ t* ≤ 1 proved
ba_zero_H/_mean, ouMatC_ba_zero, UN*k_ba_zero   inst_ba_zero, inst_ba_zero_pins (1270, 1282)   none (sizes S0.withLam 0)
BASelf_msc                              inst_BASelf_msc (1294)                none (d=3, L=4, z=i)
unBadY_subset', SBR_zero_ne             inst_unBadY_subset', inst_SBR_zero_ne none (d=3, L=4, W=32)
unBadYBA_subset, unBadYBA_measure_le    inst_badYBA_subset, inst_badYBA_measure  none (L=4, W=32, lamQ=1/64, WO window proved)
class sequences (8a)                    clsSz_admissible, cls_bulk, ...       none (no huniq)
```
- None of the instances uses `N = 0`, an empty index type, a collapsed window or a `False` premise.
- `inst_UNMLOutBA` applies the pin at the merged `sz0`, `zSeq`, `flow_sz0` and `t0_sz0`, with time `0 ≤ 0 ≤ t₀`.
- All of these compile, since the whole module builds (§2).

## 6. Paper deltas
- The prove report (d) proposes no new candidate.
- Every Lean/paper statement difference here is already covered:
  - the BA law `seqP (sz.withLam 0)` is `docs/paper-deltas.md:1402` (D443, T2173a);
  - the bulk `ρ_N(E) ≥ κ` instead of `|E| ≤ e_λ − κ` is DECISIONS §51 (`DECISIONS.md:362`);
  - the dilated universality form `UNUnivDilAt` is DECISIONS §11 (`DECISIONS.md:98`).
- The extra eventual exponent `CV₀ + 1` and the `0 < CV₀` premise of `unMeanBound_ba` are internal to the C″ interface, not paper statements.

## 7. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. The report counts "94 public declarations". `collectAxioms` over the non-internal constants of the module counts 109, a figure that includes auxiliary equation lemmas. This is a count only.
- O2. The ticket's literal `grep -w` acceptance form cannot return docstring-only lines, because it matches the mandated primed successors `UNTrLocalInit'` and `UNCoreC''`. The report states this (narrative 8). The strict form is clean (§4).
- O3. `inst_badYBA_measure` (probe text) concludes `≤ 1` under a Dirac probability, which is trivially true. Every hypothesis of `unBadYBA_measure_le` is nevertheless discharged at concrete data (`L = 4`, `W = 32`, the WO window), and `inst_badYBA_subset` exercises the nontrivial `queBadMat` content.
- O4. Preflight finding F1 is an obligation for the owner of `UNTrLocalInitBARow'` (BA-N1). Under the C″ form, the BA initial matrix's local law at `λ̂` lives on a window wider by `|E|(1−a)/a`, and bulk stability is assumed only on `|x−E| ≤ δ`. The dispatcher may want it copied into the BA-N1 ticket. It does not affect the pins here.

## Verdict
| target | verdict |
|---|---|
| 1 `UNModelC.ba`, `ba_spec`, `ba_toUNModel`, `UNKind.ba`, `UNKind.ba_M` | PASS |
| 2 `UNQueBA`, `UNLocAvgBA`, `UNMLOutBA`, four BA rows, `un_claimAll_of_rowsBA` | PASS |
| 3 `UNDensBARow'`, `UNTrLocalBARow`, `UNTrLocalInitBARow'`, `UNNormBARow`, `unMeanBound_ba` | PASS |
| 4 `BAqueConclL`, `BAEnd_QUEL`, `BAEnd_BUnivL`, `UNQueBA_of_BAEnd_QUEL`, `baBUniv_of_rows` (via `UNCoreC''`) | PASS |
| 5 centred flow (`lamHat`, `ouMatC_ba_eq_ouMat`, `ouP_ba_*`, `ouMatC_ba_eq_band_add`, `ouInit_ba`, `admissible_lamHat`) | PASS |
| 6 `λ = 0` extremes, `BASelf_msc` | PASS |
| 7 one-block bad event | PASS |
| 8 instances (`RBM.BA.UNPinsInst`, `RBM.Univ.BAInst`) | PASS |

Overall: **PASS**. No dispatcher sign-off needed.
