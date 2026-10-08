Auditor model: claude-opus-5-5

# T2320 audit (round 1): S3-25, Step 3 of `lem:main_ind` at regimes (iii), (i), case (ii)

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2320-audit1`, detached at `t/T2320` = `10258f1`; `main` = `4f99be7`.
Written Thu Oct  8 04:35:43 UTC 2026 (`date -u`).

## 1. Statements against the pin (check-file equality, run by the auditor)

```
$ { imports of docs/tickets/checks/T2320-check.lean; import RBM3D.Induction.Step3;
    the check file's section 2 (defs T2320_*) without its #check lines;
    example : RBM.Ind.T2320Check.T2320_stStep3RegIII := RBM.Ind.stStep3RegIII_holds
    example : RBM.Ind.T2320Check.T2320_stStep3RegI := RBM.Ind.stStep3RegI_holds
    example : RBM.Ind.T2320Check.T2320_stStep3II := RBM.Ind.stStep3II_holds } > checkeq.lean
$ lake env lean checkeq.lean; echo "lean exit=$?"
lean exit=0          (no output lines: no error)
$ grep -n "^theorem stStep3" RBM3D/Induction/Step3.lean
377:theorem stStep3RegIII_holds : ∀ d : ℕ, STStep3R d STReg5III := by
408:theorem stStep3RegI_holds : ∀ d : ℕ, STStep3R d STReg5I := by
432:theorem stStep3II_holds : ∀ d : ℕ, STStep3II d := by
```
The three targets are definitionally the pinned `Prop`s (`T2320_stStep3RegIII/RegI/II`). The pins themselves (merged, unchanged):
`STStep3R d R` (`Step34Pins.lean:250`) = `3 ≤ d → ∀ κ ε 𝔡 > 0, ∀ Cd > 0, ∃ 𝔠d ∈ (0,1/100], ∀ 𝔠 sz z, STFlow → ∀ s t,
0 ≤ s, s < t, t ≤ lemT z → R sz s t → STKbound → STKward → STLK s → STConStInd 𝔠d → STStep1Loop → STStep2Concl Cd → STLmaxU`;
`STStep3II d = STStep3R d STCaseII` (`:278`); regimes `STReg5III` = `∀ n, lam² ≤ 1 - t n` and
`STReg5I` = `∀ n, lam²/L² ≤ 1 - t n ∧ 1 - s n ≤ lam²` (`Step5Pins.lean:44,58`), `STCaseII` = `∀ n, 1 - s n ≤ lam²/L²`.
Quantifier order (constants `κ ε 𝔡 Cd` before `∃ 𝔠d`, then sizes, then `∀ᶠ n` inside `Prec`) is the pin's; the ticket's
regimes are exactly the ones targeted (ticket "Targets" 1-3). `STStep3I` (straddling case (i)) is not claimed (correct per ticket).

## 2. Vacuity, hidden hypotheses, cycles

- The targets are closed theorems of the pinned `Prop`s; no structure carries a hypothesis. All helpers (`step3_xB`, `step3_finish`,
  `step3_skeleton`, `step3_psi0_le`, `step3_hbase`, `step3_K_pairs`, `step3_flowLam`, `step3_assemble`) are `private` and their
  premises are discharged inside the target proofs (lines 377-451): `hS`/`hscale`/`hBA` by the merged `iterationsA_scale_I/II`,
  `st_hscale_I'/II'`, `st_hBA_I/II`; `hIter` by `stIterations'_holds`/`stIterationsII'_holds` fed `STXiBoot'` from
  `stOeqQt'_holds`/`stOeqQtNZ'_holds`; `(con_st_ind)` passed down by `st5_conStInd_mono` at `𝔠d := min c₁ c₂`.
- Dependencies: all used names are merged on `main` (the check file's section 1 `#check`s them; the module builds against main's
  oleans, §4). The new file imports only `RBM3D.Induction.QtXiRoundLift`, `RBM3D.Induction.IterationsB` (the other four ticket
  imports transitive, prove report script); no `MainIndRegimes`, no `RBM3D`, so no cycle with T2321.
- Pin premises not used: target 1 does not use `STKbound`, `STKward`, `STLK`, `STConStInd`, `STStep2Concl` (`_`-named); this
  makes the theorem stronger, not vacuous. The regime premise is used (`hgu`, line ~392) and is satisfiable (§3).
- External hypotheses: none added by this ticket (no new hypothesis beyond the pin).

## 3. Compiled nonempty instances (namespace `RBM.Ind.Step3Inst`)

```
$ grep -nE "^theorem (inst_|sz0_regIII)|^example" RBM3D/Induction/Step3.lean
473:theorem sz0_regIII : STReg5III sz0 sInst tInst := by
490:theorem inst_regIII (Cd : ℝ) (hCd : 0 < Cd) :
500:theorem inst_regI (Cd : ℝ) (hCd : 0 < Cd) :
514:theorem inst_II (Cd : ℝ) (hCd : 0 < Cd) :
530:example : (1 - (0 : ℝ)) / (1 - 1 / 32) * sz0.Bctl 0 0 ≤ 4 * sz0.Bctl 0 (1 / 32) := by
537:example : (1 - (0 : ℝ)) / (1 - 1 / 32) * sz0.Bctl 0 0 ≤ 2 * sz0.Bctl 0 (1 / 32) := by
```
| target | data (`d = 3`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, any `Cd>0`) | deterministic hypotheses discharged by | left as hypotheses |
|---|---|---|---|
| 1 `inst_regIII` | `sz0`, `z0`, `s ≡ 0`, `t ≡ 1/16` | `inst_step3R` with `flow_z0`, `sz0_hs0`, `sz0_hst`, `sz0_ht`, `sz0_regIII` (`lam_n² ≤ 1/4096 ≤ 15/16`), `sz0_con`; `stKbound_of_flow`, `stKward_of_flow` | `STLK`, `STStep1Loop`, `STStep2Concl` |
| 2 `inst_regI` | `szB`, `zB`, `s ≡ 7/8`, `t ≡ 15/16` | `flow_zB`, `norm_num` (`0 ≤ s`, `s < t`), `szB_flow_ht`, `szB_regIterI` (`1/16 ≤ 1/16`, `1/8 ≤ 1`), `conStInd_const` (`Bctl → 0`, `W = n+4 → ∞`); `stKbound_of_flow`, `stKward_of_flow` | same three |
| 3 `inst_II` | `szB`, `zB`, `s ≡ 15/16`, `t ≡ 31/32` | as 2 with `szB_caseII` (`1/16 ≤ 1/16`) | same three |

`inst_step3R` (`Step34Pins.lean:917`) applies the target at the data and returns `InstStep3Concl` (`:870`: `∃ 𝔠d ∈ (0,1/100]`,
`STKbound → STKward → STLK → STStep1Loop → STStep2Concl → STLmaxU`); the instances then discharge `STKbound`, `STKward`.
The three remaining premises are stochastic pins of other gates (Step 1 `(lRB1)`, Step 2, the induction hypothesis at `s`),
allowed by CLAUDE.md §4 step 2. Data nondegenerate: `s < t` with a non-collapsed window, `L ≥ 4`, `W → ∞`, `lam > 0`;
regimes (i)/(ii) are met on `szB` with equality at one boundary (`lam²/L² = 1 - t` resp. `= 1 - s`), not collapsed.
The (R3) comparison at concrete numbers (ticket "Instances") compiles with constant 4 and with the proof's constant 2.

## 4. Build, axioms, hygiene, scope

```
$ lake build RBM3D.Induction.Step3   (audit worktree; 04:33:15 → 04:33:23 UTC)
$ grep -c "^error" build.out
0
$ grep "Induction/Step3.lean" build.out | cut -c1-140
info: RBM3D/Induction/Step3.lean:547:0: 'RBM.Ind.stStep3RegIII_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/Step3.lean:548:0: 'RBM.Ind.stStep3RegI_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/Step3.lean:549:0: 'RBM.Ind.stStep3II_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/Step3.lean:550:0: 'RBM.Ind.Step3Inst.inst_regIII' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/Step3.lean:551:0: 'RBM.Ind.Step3Inst.inst_regI' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/Step3.lean:552:0: 'RBM.Ind.Step3Inst.inst_II' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3908 jobs).
exit=0
$ git show t/T2320:RBM3D/Induction/Step3.lean | grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom|^\s*axiom " | wc -l
       0
$ git diff --stat main...t/T2320
 RBM3D/Induction/Step3.lean | 552 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean     |   1 -
 2 files changed, 552 insertions(+), 1 deletion(-)
$ git diff main...t/T2320 -- RBM3D/Test/Axioms.lean | grep "^[-+]" | cut -c1-110
--- a/RBM3D/Test/Axioms.lean
+++ b/RBM3D/Test/Axioms.lean
-   `RBM.Gauss.Sizes.STStep3II, -- Step 3, case (ii): consumer `ST_mainIndR_*_of_steps` (T2245; S3-27 cancelle
$ git show t/T2320:RBM3D/Test/Axioms.lean | grep -c "RBM.Gauss.Sizes.STStep3R,\|RBM.Gauss.Sizes.STStep3I,"
2
```
(lines 114 `STStep3R` and 116 `STStep3I` remain, untouched, as the ticket requires.) Only the two sole writable files are touched;
no merged file (hence no frozen signature) changes.

Registry pre-check (auditor): scratch copy of `RBM3D.lean` with `import RBM3D.Induction.Step3` inserted after the last import
(line 358), run against the worktree's oleans (`lake build RBM3D` without the import fails, as expected, on
`[RBM.Gauss.Sizes.STStep3II]` being neither proved nor listed):
```
$ diff RBM3D.lean rootpre.lean
358a359
> import RBM3D.Induction.Step3
$ lake env lean rootpre.lean; echo exit=$?
exit=0
axiom audit: 9085 theorems, 2945 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
  RBM.Gauss.Sizes.STStep3R: 4 [no certificate]
  RBM.Gauss.Sizes.STStep3I: 8 [no certificate]
```
So the merge needs the root import (hub step §3 (A) 4), which the ticket assigns to the hub.

Name clash (new public names, outside `Probe/` and the new file):
```
$ grep -rnw "sz0_regIII\|inst_regIII\|inst_regI\|inst_II\|step3_skeleton\|stStep3II_holds" RBM3D --include='*.lean' \
    | grep -v "Induction/Step3.lean\|/Probe/" | wc -l
       0
```

## 5. Paper deltas

Lean/paper differences, and whether the prove report (d) covers them:
- Target 1 holds only on `lam² ≤ 1 - t`, while the paper splits at `1 - u = lam²` and the full case (i) is `STStep3I` (owed):
  covered by `T2320a`.
- `B_{u,0} ≍ |1-u|⁻¹` (`3_5:1384`) holds with fixed constants only when `1 - u ≥ lam²`; Lean uses constant 2 (`step3_xB`):
  covered by `T2320b`.
- `k = 1` goes through `(rela_XILXILK)` at `m = 1`, while the paper states it for `n ≥ 2` (`3_5:1387`): covered by `T2320c`.
- Targets 2 and 3 are the pinned regimes `STReg5I`, `STCaseII`, a choice made by the dispatcher (DECISIONS §132 (2)), and the
  report says they are not the paper's full case split (`T2320a`).
Every statement difference is proposed as a candidate.

## 6. Observations (not RETURN grounds)

- O1. `sz0_regIII` is a public, unprefixed name in `RBM.Ind.Step3Inst`. It sits in the ticket's instance namespace and has
  0 clashes, so it is harmless. Rule §3 (E) would prefer `step3_` or `private`.
- O2. Prove report (b) line 139 prints one `sed` command covering three ranges; the pasted text matches the file (lines 490-523).
- O3. The ticket's (R3) constant `4^{k-1}` is sharpened to `2^{k-1}`. Both forms are absorbed by `≺`, and the statement is the same.

## Verdict

| target | statement | hidden hyp / vacuity / cycle | instance | build / axioms | paper deltas | verdict |
|---|---|---|---|---|---|---|
| `stStep3RegIII_holds` | = pin | none | `inst_regIII` compiled | ok / standard 3 | T2320a, b | **PASS** |
| `stStep3RegI_holds` | = pin | none | `inst_regI` compiled | ok / standard 3 | T2320a, c | **PASS** |
| `stStep3II_holds` | = pin | none | `inst_II` compiled | ok / standard 3 | T2320a, c | **PASS** |

Overall: **PASS**. No dispatcher sign-off needed. The hub adds `import RBM3D.Induction.Step3` at merge (registry pre-check above).
