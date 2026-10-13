Auditor model: claude-opus-5-5

# T2495 audit (round 1) — BA-T T7-BA, `RBM3D/BA/DecayLoopBA.lean`

Written Tue Oct 13 07:34:59 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2495-audit1`, detached at
`t/T2495` = `add74cd9`; merge base with `main` = `b3ead83b`. Split: section (a) did **not** confirm the pre-signed split
(own count ~253 lines, file 228 lines), so all targets 1-6 are delivered in one file and audited here.

## 1. Diff scope (sole writable files)

```
$ git diff --stat main...t/T2495
 RBM3D.lean                |   1 +
 RBM3D/BA/DecayLoopBA.lean | 228 ++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean    |   4 +-
$ diff <(git show main:RBM3D/Test/Axioms.lean | sed 's/ --.*//') <(git show t/T2495:RBM3D/Test/Axioms.lean | sed 's/ --.*//') && echo ...
code (comment-stripped) identical
$ git diff main...t/T2495 -- RBM3D/Test/Axioms.lean | grep "^+ " | grep -o "BA reader.*"
BA reader: `baDecayLoopPT_of` (T2495; per-time reading of `STGdecayWgL` through `perTimeOfStochDomAt`)
BA reader: `baDecayLoopU_of`, `baStep2Decay_holds` (T2495)
$ git diff main...t/T2495 -- RBM3D.lean | grep "^[+-]"
+import RBM3D.BA.DecayLoopBA            (after the last import line; `#assert_rbm_axioms` stays last)
```
All three files are sole writable files; no merged `Chain/`, `Induction/`, `Path/`, `BA/` file is touched; registry lines
221-222 (T2494) untouched; no frozen signature changed. Reserve `BA/DecayLoopBA2.lean` not created.

## 2. Statements against the pins (`docs/tickets/checks/T2495-check.lean`)

Textual diff (whitespace-normalized theorem statement vs pin body), script `scratchpad/T2495/stmtdiff.py`:
```
$ python3 -I stmtdiff.py
DecayLoopU   baDecayLoopU_of        IDENTICAL
SizeInv      baFlow_sizeInv_le      IDENTICAL
DecayLoopPT  baDecayLoopPT_of       IDENTICAL
DecayLoopAt  baDecayLoopAt_holds    IDENTICAL
Step2Decay   baStep2Decay_holds     IDENTICAL
STLWB        baSTLWB_of             IDENTICAL
STLWT        baSTLWT_of             IDENTICAL
```
Elaboration check: the check file with `import RBM3D.BA.DecayLoopBA` and, before `end RBM.BA`,
`example (d : ℕ) : T2495_X d := @name d` for the seven names plus `#print axioms` (scratch `pincheck.lean`):
```
$ lake env lean scratchpad/T2495/pincheck.lean ; echo exit $?
exit 0          (0 error lines)
'RBM.BA.baDecayLoopU_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baFlow_sizeInv_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baDecayLoopPT_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baDecayLoopAt_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep2Decay_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSTLWB_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSTLWT_of' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Against the ticket mathematics (stop rule 2): target 1 premises are exactly `3 ≤ d`, `0 < κ`, `BAFlow`, `0 ≤ s`, `t ≤ T0` and the
input `STGdecayWgL`; 2 (a) adds only `0 < ε`; 2 (b) adds `0 < ε`, `s ≤ t`, input `STStep2DecayPTgL`; target 4 keeps the
`STStep2G` order (constants `Cd, 𝔠d` before `𝔠, sz, z`); target 5 is `3 ≤ d → BALWterm/BALWtermExp d → BASTLWB/BASTLWT d`.
Conclusions are the merged generic pins `STDecayLoopUgL`/`PTgL`/`AtgL` (`Chain/DecayGen.lean:65-115`) at
`(baFMz sz z, seqP (sz.withLam 0))`; paper `lem_decayLoop` (`3_5_Loop_Hierarchy.tex:1126-1131`): `n ≥ 2`, `u ∈ [s,t]`,
far set `max|a_i-a_j| ≥ W^ε ℓ_u`, `|𝓛|+|𝒦|`; Lean differences are the merged generic ones (below, §5).

## 3. Vacuity, hidden hypotheses, cycles

```
$ F=RBM3D/BA/DecayLoopBA.lean
$ grep -nE "sorry|admit|native_decide|^axiom" $F                                  -> (0 hits)
$ grep -nE '^(noncomputable )?(def|abbrev|structure|class|instance) ' $F          -> (0 hits)
$ grep -nE 'STGridRepNgL|baStep1_holds\b|\|E\||2 - κ|\bmE\b|zt E|STFlow|lemT|‖m‖ = 1' $F   -> (0 hits)
$ grep -nE '≤ A \*|\(κ \+ 1\) / κ' $F                                              -> (0 hits; no R1 text)
$ grep -n withLam $F | grep -v "seqP (sz.withLam 0)\|seqP (sz0.withLam 0)"
17:(sz.withLam 0), BAFlow, baFMz, BAflowT0)`.     (module docstring line wrap; not a statement)
$ git grep -n "import RBM3D.BA.DecayLoopBA"
RBM3D.lean:588:import RBM3D.BA.DecayLoopBA
$ grep -n "^private" $F
85:private theorem DecayLoopBA_PT_of_U ...           (stem-prefixed, §3 (E))
```
- No new structure/def, so no hypothesis hidden in a field. Every proof is a term application of merged public results
  (`stDecayLoopUgL_of_step2`, `stDecayLoopPTgL_of_step2`, `stDecayLoopAtgL_of`, `baKcalDecay_holds`, `baStep2_holds`,
  `baFlow_premises`, `stLWBgL_of_LWtermG`, `stLWTgL_of_LWtermExpG`, `DecayGenTw_baWardPair`, `EMn2BA_mF_data`,
  `EMn2BA_T0_lt_one`, `Step2EventsGenTw_baRot3`), all in merged modules imported from `main`; leaf module, no cycle.
- No per-index guard `0 < g₀ n` (G1) appears; `DecayGen_Spec` is discharged as `⟨hκ, EMn2BA_mF_data.1, rfl⟩`.
- Remaining unproved inputs are of exact registered type: `STGdecayWgL` (registry :197), `STStep2DecayPTgL` (:196),
  `BALWterm`, `BALWtermExp` (:221-222, owner T2494); `STStep2G` binders in target 4 are binders of the frame (as pinned).
  None is a cited external input, so no limit check is required (they are other gates' pins).
- Target 3's conclusion `STDecayLoopAtgL` carries its own premises (`DecayGen_Spec`, `Admissible`, window, prefactor, decay
  input) as pinned (dispatcher answer (8)); the instance below discharges all deterministic ones.

## 4. Compiled nonempty instances (target 6, file section 4, `d = 3`)

Data: `sz0`, `zSeq`, `flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq`, `s ≡ 1/10`, `t ≡ 1/2`, `t ≤ T0` by `half_lt_t0`.
| target | example (file line) | deterministic premises discharged | left as hypothesis |
|---|---|---|---|
| 1 | 157-160 | `3 ≤ 3`, `0 < 1/2`, `flow_sz0`, `0 ≤ 1/10`, `1/2 ≤ T0` | `STGdecayWgL` (Step 2 output) |
| 2 (a) | 163-165 | all (`0<κ`, `0<ε`, flow, `t ≤ T0`) | none |
| 2 (b) | 168-172 | as 1, plus `0<ε`, `1/10 ≤ 1/2` | `STGdecayWgL` (PT input via private G4 helper) |
| 3 | 176-190 | `DecayGen_Spec`, `Admissible` (`flow_sz0.1`), `0 ≤ u`, `u < 1`, prefactor `P ≡ 1`, `C₀ = 0`; applied at `k = 3`, `τ' = 1/10`, `D' = 1` | the `(+,-)` 2-loop decay input `hdec` (Step 2 output) |
| 4 | 193-204 | `3 ≤ 3`, `0<κ, ε, 𝔡`, `flow_sz0`, `0 ≤ s`, `s ≤ T0`, `s < t`, `t ≤ T0` | `BALWterm 3`, `BALWtermExp 3`; frame binders inside the conclusion |
| 5 | 207, 209 | `3 ≤ 3` | `BALWterm 3` / `BALWtermExp 3` |
Non-degeneracy: `sz0` has `L n ≥ 4`, `N(0) = 2^21` (preflight numerics), window `[1/10, 1/2]` nonempty, far set of `𝒦`
nonempty via `example := KDecayBAInst.inst_baKcalDecay_far` (line 222). No `N = 0`, empty index, collapsed window or `False`
premise. All examples compile (module build below).

## 5. Build and axioms

```
$ lake build RBM3D.BA.DecayLoopBA ; echo exit $?        (audit worktree)
Build completed successfully (4104 jobs).
exit 0          (grep error|sorry: 0 lines)
$ lake build ; echo exit $?                              (whole library, branch root imports incl. RBM3D.BA.DecayLoopBA; runs #assert_rbm_axioms)
non-vacuity certificates: 0 of 123 premises in the two ledgers; ...
Build completed successfully (4359 jobs).
exit 0          (grep "error:": 0 lines)
```
Axioms: see §2, standard three for all seven public declarations.

## 6. Paper deltas

| Lean/paper difference | coverage |
|---|---|
| far set by `STdiamInf` (`L^∞`) vs paper `max|a_i - a_j|` | D18 (T2002b) |
| `k ≥ 1` (vacuous at `k = 1`), `|𝓛|+|𝓛−𝒦|`, per-time `≺`, `τ' = ε` | D298 (T2133c), inherited via the generic pin |
| hypothesis is the `(+,-)` 2-loop decay only, no `(Gt_bound_flow)` | D296 (T2133a) |
| `3 ≤ d` | D297 (T2133b) |
| `|E| ≤ 2-κ` replaced by `DecayGen_Spec` (`κm = κ` at BA), F4/F7/F9 explicit, F6 range | T2454a-d candidates (pending numbering at T7a merge, `paper-deltas.md:1598`) |
| `lem_decayLoop` not named in `7_8_light_weight.tex:1994` (BA reading via generic proof) | T2495a (citation only, proposed in prove report (d)) |
| 2 (a) range, target 4 conjunction, target 5 bridges | no paper statement (Lean auxiliaries of Step 2); no delta needed |
Verified: `grep -n decayLoop paper/tex/*.tex` gives only `3_5:1126, 1153`, confirming the T2495a citation finding.

## 7. Observations (no RETURN)

- O1: the `hU` example (lines 213-219) concludes `True`; it checks that target 1 fits the `hU` premise of `baEtermDecaygL`
  (the `have` elaborates), not the ℰ-term decay. Not an endpoint target; the prove report states this.
- O2: one `withLam` grep hit is the module docstring wrap at line 17; no statement hit. Labelled in the prove report.
- O3: the prove report's base note (check and (a) on `main 0a68e61d`, branch on `b3ead83b`) does not affect any statement;
  the pins compile against the branch (§2).

## Verdict

| target | verdict |
|---|---|
| 1 `baDecayLoopU_of` | PASS |
| 2 (a) `baFlow_sizeInv_le` | PASS |
| 2 (b) `baDecayLoopPT_of` | PASS |
| 3 `baDecayLoopAt_holds` | PASS |
| 4 `baStep2Decay_holds` | PASS |
| 5 `baSTLWB_of`, `baSTLWT_of` | PASS |
| 6 instances | PASS |

**Overall: PASS.** No dispatcher sign-off needed.
