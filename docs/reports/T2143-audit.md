Auditor model: claude-opus-5-5

# T2143 audit (S5-02, `RBM3D/Induction/Step5Kit.lean`) — round 1, Sun Oct  4 17:03:32 UTC 2026 (date -u)

Branch `t/T2143` at `5ac1418`, merge base = `main` `c8e4f17`. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2143-audit1` (detached).
`$P` = `git show 7b2b789:RBM3D/Probe/T2134Pins.lean` (the ticket's pin source; the check file has `#check` lines only).

## 1. Statement (script diff against the pin `7b2b789`)

```
$ diff <(sed -n 33,587p Step5Kit) <(sed -n "477,731p;740,1039p" $P) && echo EMPTY
EMPTY
$ sed -n 732,739p $P | head -1        # the excluded block (ticket: use the merged one)
theorem st5_reg5I_mid {sz : Sizes d} (hd : 2 ≤ d) {s t : ℕ → ℝ} (h : STReg5I sz s t) : STReg5Mid sz s t := by
$ grep -n "theorem st5_reg5I_mid" RBM3D/Induction/Step5Pins.lean     # merged, identical signature
464:theorem st5_reg5I_mid {sz : Sizes d} (hd : 2 ≤ d) {s t : ℕ → ℝ} (h : STReg5I sz s t) : STReg5Mid sz s t := by
$ diff <(sed -n 595,630p Step5Kit) <(sed -n 1819,1854p $P) && echo EMPTY      # 7 instances
EMPTY
$ diff <(sed -n 632,638p Step5Kit) <(sed -n 2255,2261p $P) && echo EMPTY      # inst_skeletonI only
EMPTY
$ grep -n "^namespace\|^end \|^import" Step5Kit      # vs probe: namespace RBM.Gauss.T2134Inst (1719), imports KDecay/NewKLK/GridDuhamelN
5-8: import RBM3D.Induction.Step5Pins / KDecay / NewKLK / GridDuhamelN
38:namespace RBM.Gauss.Sizes   589:end RBM.Gauss.Sizes   591:namespace RBM.Gauss.Step5Inst   640:end RBM.Gauss.Step5Inst
```
The only differences from the pin are the two the ticket documents (namespace `T2134Inst` -> `Step5Inst`; `st5_reg5I_mid` not re-declared) plus file header/`end` lines. No `import RBM3D`.

Against the paper (`3_5:1937-1940`): the four regimes of the merged `STReg5I..IV` are the paper's (i)-(iv) verbatim; case (iv) "follows from
`(Eq:L-KGt-flow)` in Step 4" is exactly `stStep5IV_holds` (uses `hLKU`, the Step-4 uniform conclusion, plus `st5_compare_IV`,
`st5_Bctl_le_one`); `ST_step5_assembly` evaluates the uniform conclusion `STStep5Concl = STGdecayW … 0 ∧ STDecayStrongU` (DECISIONS §40)
at `u = t`. Quantifier order of `STIngR5` (constants `κ ε 𝔡`, `Cd`, then `∃ 𝔠d ∈ (0,1/100]`, then `𝔠`, sizes, `z`) is the merged pin, unchanged.

| target | statement | verdict |
|---|---|---|
| `st5_*` comparisons (17), `st5_prec_mono`, `st5_prec_cover` | = probe, empty diff | PASS |
| `ST_step5_assembly` | = probe; `STStep5Concl ⇒ STDecay ∧ STDecayStrong` at `t`, `hst : s ≤ t` | PASS |
| `ST_step5_caseI_of_pins` | = probe; `STEtermsMid d → STDuhamelI d → STIniTermI d → STStep5I d` | PASS (conditional on three owed pins; not claimed as `STStep5I`, which stays owed) |
| `stStep5IV_holds` | = probe; `∀ d, STStep5IV d`, no hypothesis | PASS |
| instances (8) | = probe | PASS |

## 2. Vacuity, hidden hypotheses, cycles

```
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " Step5Kit; echo $?
1
$ grep -n "structure\|class " Step5Kit; echo $?
1
```
No new structure/def; every hypothesis is in the signatures above. Dependencies are merged (`Step5Pins` T2138 c8e4f17, `KDecay`, `NewKLK`,
`GridDuhamelN`); no cycle (the file imports only merged modules). `stStep5IV_holds` picks `𝔠d = 1/100` (allowed `≤ 1/100`).
Regime nonemptiness: the merged `szG_reg4`, `szB_reg5I`, `szB_reg5II`, `sz0_reg5III` prove each regime at its data (Step5Pins 511-520).
No external hypothesis is introduced by this ticket.

## 3. Compiled nonempty instances

```
$ lake env lean $S/ax.lean      # #check
Step5Inst.inst_step5IV_proved : ∀ (Cd : ℝ),
  0 < Cd →
    Step5Inst.InstIng5Concl (fun {d} sz E s t => sz.STStep5Concl E s t) Step5Inst.szG Step34Inst.zB (fun x => 5 / 8)
      (fun x => 3 / 4) Cd
```
- `stStep5IV_holds`: `inst_step5IV_proved` (Step5Kit:618) at `(szG, zB, 5/8, 3/4)`, `d = 3`, no pin hypothesis. Deterministic hypotheses
  discharged in merged `inst_ing5_IV` (Step5Pins:582-590): `flow_zG`, `0 ≤ s`, `s < t` (`norm_num`), `t ≤ lemT` (`szB_flow_ht`),
  `szG_reg4`, `STConStInd` for every `𝔠d > 0` (`conStInd_const`). Data: `L = 4`, `W_n = n+4`, `ilambda = 5`; `1-s = 3/8 ≤ 25/64`.
- `ST_step5_caseI_of_pins`: `inst_skeletonI` (Step5Kit:636) at `(szB, zB, 7/8, 15/16)`; hypotheses = the three owed ingredient pins only.
- `ST_step5_assembly`: `inst_assembly` (Step5Kit:628) at `(sz0, z0, 0, 1/16)`; `hst` discharged by `sz0_hst`; hypothesis = the owed
  Step-5 conclusion `STStep5Concl` at that data (another gate's result, allowed).
- `inst_step5I/II/III/IV`, `inst_step5`: pins as hypotheses at nondegenerate regime data (T2138 audit O1). None uses `N = 0`, an empty index,
  a collapsed window, or a `False` premise.

## 4. Build and axioms

```
$ lake build RBM3D.Induction.Step5Kit 2>&1 | grep -E "Step5Kit|error|Build completed"
Build completed successfully (3775 jobs).
$ lake build RBM3D 2>&1 | grep -E "^error|axiom audit|Build completed"     # root without the new import (hub adds it)
info: RBM3D.lean:188:0: axiom audit: 4432 theorems, 1575 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (3889 jobs).
$ printf 'import RBM3D\nimport RBM3D.Induction.Step5Kit\n#assert_rbm_axioms\n' > precheck.lean; lake env lean precheck.lean   # registry pre-check (§20)
axiom audit: 4460 theorems, 1575 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: ...
exit=0
$ lake env lean $S/ax.lean
'RBM.Gauss.Sizes.ST_step5_assembly' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_step5_caseI_of_pins' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stStep5IV_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.st5_compare_I' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.st5_compare_IV' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.inst_step5IV_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.inst_skeletonI' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.inst_assembly' depends on axioms: [propext, Classical.choice, Quot.sound]
$ git diff --stat main...t/T2143
 RBM3D/Induction/Step5Kit.lean | 640 ++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean        |   3 +-
$ git diff main...t/T2143 -- RBM3D/Test/Axioms.lean | grep '^[-+] '
-   `RBM.Gauss.Sizes.STPfStep5] -- `lem:pf_step5`; proved internally (DECISIONS §40); S5-01 (T2138, DECISIONS §40: owed)
+   `RBM.Gauss.Sizes.STPfStep5, -- `lem:pf_step5`; proved internally (DECISIONS §40); S5-01 (T2138, DECISIONS §40: owed)
+   `RBM.Gauss.Sizes.STStep5Concl] -- uniform Step-5 conclusion ... S5-02 (T2143; class proposed: owed, as `STStep2Concl`, DECISIONS §40)
```
Only the two sole writable files; no frozen signature touched; `STStep5IV` not registered, `STStep5I` still owed (Axioms.lean:167).

## 5. Paper deltas

No new Lean/paper difference: every statement is the §40-accepted probe text; its deltas are D315-D324 (`docs/paper-deltas.md:1271-1282`;
D323 covers the `g² ≤ 1−t` index set of `STDecayStrongU` used by the assembly). The prove report cites them and proposes none. Covered.

## 6. Observations (no statement/instance/build/axiom/delta effect)

- O1. Registry: `STStep5Concl` (hypothesis of `inst_assembly`) was not in §40's class list; registered **owed** per DECISIONS §20
  ("if unsure, record owed and raise it in the report"), and the prove report (d) raises it. The dispatcher may reclassify; the
  pre-check passes either way. The `]` -> `,` edit on the previous line is the minimal change needed to append to the list.
- O2. `st5_prec_cover` is unused in this file (consumer: case (iii), S5-03); it is a general `Prec` calculus lemma, copied verbatim as
  pinned, with no standalone `example`. The other 16 `st5_*` are exercised by `stStep5IV_holds`/`ST_step5_caseI_of_pins` (grep of uses).
- O3. Prove report (b) quotes `RBM3D.lean:189` for the axiom audit (with the temporary root import); in this worktree without it, line 188.

## Verdict

All targets: **PASS**. No dispatcher sign-off required (O1 is the §20 default, already flagged for the dispatcher in the prove report).
