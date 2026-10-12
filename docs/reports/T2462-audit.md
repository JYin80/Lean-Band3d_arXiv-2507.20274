Auditor model: claude-opus-5-5

# T2462 audit, round 1: U4s1a only (`Chain/Step5CasesGen`, targets 1-7) — Mon Oct 12 18:48:13 UTC 2026
Branch `t/T2462` at `d0aa6c00`; audit worktree `RBM3D-wt/T2462-audit1` (detached at `d0aa6c00`); `main` at `5812a277`.
Binding: Amend 1 (`docs/tickets/T2462-amend-1.md`, H254 (3), DECISIONS §273 (1)-(2)). Comparison text R1; targets 8-11 (U4s1b,
`t/T2462b`) are not in scope. Scratch files are in `<scratchpad>/T2462/`.

## 1. Build, axioms, hygiene, diff
```
$ lake build RBM3D.Chain.Step5CasesGen ; echo exit=$? ; grep -E "^error|Step5CasesGen|Build completed" build.log
exit=0   Build completed successfully (3782 jobs).   (no warning or error line names Step5CasesGen)
$ lake build RBM3D   (branch root, without the new import)  ->  Build completed successfully (4288 jobs). exit=0
$ lake env lean ax.lean   (#print axioms, the ten public declarations)
'RBM.BA.Step5CasesGen_FlowFacts' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.step5CasesGen_flowFacts_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Step5CasesGen_WardIdent' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.step5CasesGen_wardIdent_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stWardIIgL_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ST_step5_caseI_of_pinsgL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ST_step5_caseII_of_pinsgL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ST_step5_caseIII_of_pfgL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stStep5IVgL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ST_step5_assemblygL' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Chain/Step5CasesGen.lean ; echo hits=$?  ->  hits=1 (no hit)
$ wc -l RBM3D/Chain/Step5CasesGen.lean  ->  784   (stop line 2,000)
$ grep -n "^import\|open private" RBM3D/Chain/Step5CasesGen.lean
6:import RBM3D.Chain.Step5Gen
7:import RBM3D.Induction.Step5Cases
8:import RBM3D.Induction.WardII
45:open private wardII_Bctl_le from RBM3D.Induction.WardII
$ grep -nE "^(private|protected) (theorem|lemma|def|abbrev)" ... (non-public declarations)
63 Step5CasesGen_prec_mono; 82 Step5CasesGen_prec_mono'; 100 Step5CasesGen_prec_cover; 114 Step5CasesGen_prec_of_isEmpty;
123 Step5CasesGen_prec_scale; 148 Step5CasesGen_flow_dom; 265 Step5CasesGen_Bctl_mono; 511 Step5CasesGen_compare_IIward;
730 Step5CasesGen_wardIIgL_band          (all private and carry the stem prefix: rule (E))
$ git diff --stat main...t/T2462  ->  Chain/Step5CasesGen.lean 784 + | Probe/T2462Pins.lean 359 + | Test/Axioms.lean 8 +
$ git diff main...t/T2462 -- RBM3D/Induction RBM3D/Chain/{Carrier,Step2Gen,Step2Kern,GridDuhamelGen,NewKLKGen,Step5Gen}.lean RBM3D/BA RBM3D.lean | wc -l
0
```
The imports match the Layout list for `Step5CasesGen`, and there is no direct `BA/*` import. Every touched file is a sole writable file.
`Probe/T2462Pins.lean` is the 1a probe ("never merged"), and the hub must leave it out at merge. `Test/Axioms.lean`: 8 added lines
(one comment and seven `owedProps` entries), 0 removed, so the change is append-only.

## 2. Statements against the amended check pins (`docs/tickets/checks/T2462-check.lean` @ b6821280, Part 2)
Scratch file `audit_pins.lean` is the full check file plus `import RBM3D.Chain.Step5CasesGen`, followed by these auditor examples:
```
example : @T2462_FlowFacts = @Step5CasesGen_FlowFacts := rfl
example : @T2462_WardIdent = @Step5CasesGen_WardIdent := rfl
example (d : ℕ) : T2462_FlowFacts_band d := step5CasesGen_flowFacts_band d
example : T2462_WardIdent_band := fun sz E hE => step5CasesGen_wardIdent_band sz E hE
example : T2462_caseI d law Flow mk T0 := ST_step5_caseI_of_pinsgL d law Flow mk T0          (variables d law Flow mk T0 generic)
example : T2462_caseII d law Flow mk T0 := ST_step5_caseII_of_pinsgL d law Flow mk T0
example : T2462_caseIII d law Flow mk T0 := ST_step5_caseIII_of_pfgL d law Flow mk T0
example : T2462_caseIV d law Flow mk T0 := stStep5IVgL_holds d law Flow mk T0
example : T2462_stWardIIgL_of d law Flow mk T0 := stWardIIgL_of d law Flow mk T0
example ... : T2462_assembly C μ s t := fun hst h => ST_step5_assemblygL C μ s t hst h
-- target 13 band re-derivations, every d, through U6's bridges:
example (d) : STEtermsMid d → STDuhamelI d → STIniTermI d → STStep5I d               (via target 2 + target 1)
example (d) : STEtermsMid d → STDuhamelII d → STIniTermII d → STWardII d → STStep5II d (via target 3 + target 1)
example (d) : STPfStep5 d → STStep5III d                                             (via target 4)
example (d) : STStep5IV d                                                            (via target 5, no pin)
$ grep -c sorry audit_pins.lean -> 0 ;  lake env lean audit_pins.lean > pins.out 2>&1; echo exit=$?; grep -n error pins.out
exit=0                       (no error line)
```
The two `def`s agree with the pins by `rfl` (equal as terms). The eight theorems inhabit the pinned `Prop`s at fully generic
arguments (same hypotheses, same order). The pinned check (with all of its `#check`s and shape lines) compiles together with the
branch module. Hypotheses, quantifier order (`∀ κ > 0, ∃ κm > 0, ∀ sz …`), index ranges (`∀ n`, `0 ≤ u < 1`, `σ 0 ≠ σ 1`) and
the normalisation `N η_u` with `N = sz.size n` all match the pins.
Coupling: under Amend 1 item 6, U4s1a states no comparison. Checked: `gK`, R1 and the old texts have 0 hits (section 4).

## 3. Hidden hypotheses, vacuity, cycles
- `Step5CasesGen_FlowFacts` and `Step5CasesGen_WardIdent` are `def … : Prop`, not structures, and have no fields. Each is a
  hypothesis of targets 2-7 and each is concluded at the band by a public result (`step5CasesGen_flowFacts_band`,
  `step5CasesGen_wardIdent_band`). Neither is vacuous: the band flow `flow_zB` (merged) satisfies the premise of FlowFacts in the
  target 1 instance.
- The other premises are U6's generic pins (`STEtermsMidgL`, `STDuhamelI/IIgL`, `STIniTermI/IIgL`, `STPfStep5gL`,
  `STStep5ConclgL`). All are merged definitions in `Chain/Step5Gen`, and their band forms come through U6's `_iff_gL` bridges (§2).
- Cycle: the module imports only merged modules (§1). Nothing on the branch imports it (it has no root import yet).
- Registry pre-check (branch root + this module):
```
$ printf 'import RBM3D\nimport RBM3D.Chain.Step5CasesGen\n#assert_rbm_axioms\n' > pre.lean; lake env lean pre.lean > pre.out 2>&1; echo exit=$?
exit=0
axiom audit: 13379 theorems, 4253 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ grep -nE "STStep5ConclgL|STEtermsMidgL|STDuhamelI+gL|STIniTermI+gL|STPfStep5gL" pre.out
103:  RBM.BA.STStep5ConclgL: 2 [no certificate]
104:  RBM.BA.STEtermsMidgL: 3 [no certificate]
105:  RBM.BA.STDuhamelIgL: 2 [no certificate]
106:  RBM.BA.STDuhamelIIgL: 2 [no certificate]
107:  RBM.BA.STIniTermIgL: 2 [no certificate]
108:  RBM.BA.STIniTermIIgL: 2 [no certificate]
109:  RBM.BA.STPfStep5gL: 2 [no certificate]
```
  The seven owed lines are the seven listed in the ticket's Registry section, and the premise scan passes with them.

## 4. Target 12 greps (U4s1a part)
```
(a) grep -cE "withLam|lam0|BAflowLam0|seqHflowBA"            -> 0
(a) grep -cE "gK|A \* gK|sz.lam n \^ 2 ≤ A"                     -> 0   (no comparison stated: Amend 1 item 6)
(c) grep -cE "Ring.inverse|Matrix.of|cycProd"                   -> 0
(c) grep -cE "(def|theorem|lemma|abbrev) [A-Za-z_']*Ugen"       -> 0
(c) grep -cE "RBM\.UN|\bUN d|uKer d|Theta d|thetaKer d|Ugen"    -> 0
(b) X1-C1 pattern, hit lines: 138 139 147 149 154 157 158 162 163 197 201 509 519 520 523 718 719 720 729 731 732 734 736 774 775 779 780
```
Labels for (b), each hit inspected: docstrings at 138, 139, 147, 154, 197 and 509; the private band helper `Step5CasesGen_flow_dom` at
149; the band result of target 1 and its proof at 157-163; the proof of the target 7 band result at 201; the proof body of the
private size-level `Step5CasesGen_compare_IIward` at 519-523 (its signature at 511-516 reads only `sz.lam`, `STAI`, `Bctl` and `η`,
`m`, `c`); instances at 718-780. No generic signature (lines 140, 169, 187, 205, 286, 340, 406, 548) has a hit.

## 5. Compiled nonempty instances (section `Instances`, lines 704-782, built in §1)
```
718 T1  step5CasesGen_flowFacts_band 3 at κ = 1/10, (szB, zB, ε 1/10, 𝔠 1/6, 𝔡 1/10), flow discharged by `flow_zB`
725 T7  Step5CasesGen_WardIdent (bandFM szB 0)                (|0| < 2 by norm_num)
730/739 T7 stWardIIgL_of at the band tuple -> STWardII d          (private theorem; re-derives stWardII_holds)
742 T7  inst_wardII at (szB, zB, 15/16, 31/32), no pin left
747 T2  inst_step5I at (szB, zB, 7/8, 15/16)        open: STEtermsMid 3, STDuhamelI 3, STIniTermI 3
754 T3  inst_step5II at (szB, zB, 15/16, 31/32)     open: STEtermsMid 3, STDuhamelII 3, STIniTermII 3 (Ward pin discharged by T7)
761 T4  inst_step5III at (sz0, z0, sInst, tInst)    open: STPfStep5 3
767 T5  inst_step5IV at (szG, zB, 5/8, 3/4)         no pin
773 T6  T5 chained with ST_step5_assemblygL at (szG, zB, 5/8, 3/4), hst by norm_num
```
`InstIng5Concl` (`Induction/Step5Pins.lean:539`) is `∃ 𝔠d, 0 < 𝔠d ∧ 𝔠d ≤ 1/100 ∧ (STKbound … → STLKU … → Concl …)`. The
remaining premises are the stochastic Step 1-4 pins and the case pins of U4s2, U4s3 and U5. These are other gates' pins, which the
rules allow to stay open. The merged `inst_*` theorems discharge every deterministic hypothesis (flow, `0 ≤ s < t ≤ T0`, the regime,
`(con_st_ind)`). The data are `d = 3`, `L = 4`, `W_n = n + 4` and `κ = 1/10`, so there is no `N = 0`, no empty index and no
collapsed window. Every endpoint theorem (targets 1-7, including `ST_step5_assemblygL` and `stWardIIgL_of`) is applied at least once.

## 6. Paper deltas
The only difference between Lean and the paper is the carrier-data form: the flow facts and the `(zYU1)` identity are hypotheses
of targets 2-7, discharged at the band by targets 1 and 7. The prove report proposes this as candidate `T2462a`
(`T2462-prove.md:268`). The case statements are U6's merged pins and are restated here with no change.

## 7. Observations (not RETURN)
- O1 (D1 and T2463). T2463 merged first (`01b4c521`), so ticket note (7) and DECISIONS §274 (1) asked this 1b to check how the text
  relates to `ZeroModeGen_WardCls`. The 1b delivered the pinned default (§273 (2), Amend 1 item 7) and wrote no bridge. Its reason
  holds:
  `ZeroModeGen_WardFam` (`Chain/ZeroModeGen.lean`) contains only rotation and `Σ_x T⟨s::μ++[!s], a++[x]⟩ = κ(T⟨true::μ,a⟩ − T⟨false::μ,a⟩)`.
  `grep -c "conj\|starRingEnd" RBM3D/Chain/ZeroModeGen.lean` gives 0, so `Im X₊` is not available without an extra conjugation
  hypothesis. T2463 may later conclude `Step5CasesGen_WardIdent` from its class (note (7)). The question stays open for the
  dispatcher (prove report (d) 1); it changes no statement here.
- O2. The probe `RBM3D/Probe/T2462Pins.lean` on the branch still holds the superseded E1 text and `sz0.withLam`. It is never merged:
  at merge the hub brings in only `Chain/Step5CasesGen.lean`, the seven registry lines and the root import.
- O3. Prove report (a) line 65 says "T2463 held, not merged". Section (a‴) records that this is out of date.

## Verdict
Each of targets 1-7 (`Step5CasesGen_FlowFacts`, `step5CasesGen_flowFacts_band`, `ST_step5_caseI_of_pinsgL`,
`ST_step5_caseII_of_pinsgL`, `ST_step5_caseIII_of_pfgL`, `stStep5IVgL_holds`, `ST_step5_assemblygL`, `Step5CasesGen_WardIdent`,
`step5CasesGen_wardIdent_band`, `stWardIIgL_of`) is **PASS**: the statement equals its pin, there is no hidden or vacuous
hypothesis, a nondegenerate instance compiles, the build passes, the axioms are the standard three, and the delta is covered.
**U4s1a: PASS.** No dispatcher sign-off is needed to merge; O1 is a non-blocking follow-up.
