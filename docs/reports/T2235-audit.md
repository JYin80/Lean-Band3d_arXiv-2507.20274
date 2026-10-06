Auditor model: claude-opus-5-5
# T2235 audit (round 1): S6-08 `Induction/ExpIntEasy` (`STExpIntIII`, `STExpIntIV`, `STStep6IV`)

Written `Tue Oct  6 01:12:37 UTC 2026` (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2235-audit1`, detached at
`t/T2235` = `1a9c99f` (base `3a58663`; `main` = `f6650b2`). Scratch files: scratchpad `T2235/`.

## 1. Scope (sole writable files, frozen signatures)
```
$ git diff --stat main...t/T2235
 RBM3D/Induction/ExpIntEasy.lean | 764 ++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean          |   3 -
$ git diff main...t/T2235 -- RBM3D/Test/Axioms.lean | grep -E '^[-+][^-+]'
-   `RBM.Gauss.Sizes.STStep6IV, -- `6:94-96` regime (iv) pin: S6-02; S6-07, S6-08; S6-01 (T2204, DECISIONS §67: owed)
-   `RBM.Gauss.Sizes.STExpIntIII, -- `6:94-96` integrated estimate, regime (iii): S6-08; S6-01 (T2204, DECISIONS §67: owed)
-   `RBM.Gauss.Sizes.STExpIntIV, -- `6:94-96` integrated estimate, regime (iv): S6-08; S6-01 (T2204, DECISIONS §67: owed)
$ git diff main...t/T2235 --stat -- RBM3D/Induction/Step6Pins.lean RBM3D/Induction/Step6Kit.lean | wc -l
       0
```
Exactly the two sole writable files; the `Axioms.lean` diff is the three ticket-named deletions; no merged pin touched.
Since the branch base, `main` changed `Test/Axioms.lean` once (T2233, `git diff 3a58663 f6650b2`: `-  RBM.Gauss.Sizes.STExpIntII, …`),
in the same region. The ticket's merge note covers this: keep both deletions.

## 2. Statements against the ticket's pin (compiled check-file equality, script)
Scratch `eqcheck.lean` = check file lines 1-27 + `import RBM3D.Induction.ExpIntEasy` + sections 1-2 (lines 28-290), then
one `example : RBM.Gauss.Sizes.T2235Check.X := @RBM.Gauss.Sizes.X` for each `def X` of section 2, three `example (d : ℕ)` lines, and
nine section-3 instance statements copied verbatim by script as `example : <statement> := @RBM.Gauss.Step6Inst.<name>`.
```
$ grep -n '^example' eqcheck.lean | cut -c1-140
294:example : RBM.Gauss.Sizes.T2235Check.expIntEasy_integral_rpow := @RBM.Gauss.Sizes.expIntEasy_integral_rpow
295..307: the same line for expIntIII_rates_le_target … stStep6IV_holds (13 more, one per section-2 `def`, in check-file order)
308:example (d : ℕ) : STExpIntIII d := stExpIntIII_holds d
309:example (d : ℕ) : STExpIntIV d := stExpIntIV_holds d
310:example (d : ℕ) : STStep6IV d := stStep6IV_holds d
315..343: 9 × `example : <section-3 statement> := @RBM.Gauss.Step6Inst.<inst_…>`
$ lake env lean eqcheck.lean ; echo exit=$?      # in the audit worktree
exit=0
$ grep -cE 'error|sorry|declaration uses' eq.out ; grep -c warning eq.out
0
0
```
The 14 public theorems equal the check file's `def`s and the 9 instances equal section 3. `stExpIntIII_holds`, `stExpIntIV_holds`,
`stStep6IV_holds` have types `STExpIntIII d`, `STExpIntIV d`, `STStep6IV d`, the merged texts (`Step6Pins.lean:425`, `:432`, `:140`,
unchanged). Hypotheses, quantifier order (`STIngR6`: `3 ≤ d → ∀ κ ε 𝔡 … → ∃ 𝔠d … ∀ 𝔠 sz z …`), the regime (`STReg5III` /
`STReg5IV`), the sign class `STSigAll`, `A = ∅` and the target `F + STExpTarget` (i.e. `B²((λ²W^d)^{-1/5}+B)`) are the pinned
ones, with no weakening. The witness `𝔠d = 1/100` satisfies `0 < 𝔠d ≤ 1/100` as the pin requires; `𝔠` stays universal.

## 3. Vacuity, hidden hypotheses, cycles
```
$ grep -rnE 'class |structure ' RBM3D/Induction/ExpIntEasy.lean | wc -l
       0
$ grep -nE '^(private )?theorem ' RBM3D/Induction/ExpIntEasy.lean   (visibility column)
private: expIntIII_Bctl_le:73 expIntEasy_ii_rpow:199 expIntEasy_term_integral:210 expIntIII_pointwise:231
         expIntEasy_drift_pi_hi:397 expIntEasy_drift_pi_lo:423 expIntEasy_lift_core:445
public : the 14 pinned names + 9 inst_* (namespace RBM.Gauss.Step6Inst)
```
- The file defines no new `Prop` or structure, so no hypothesis hides in a field. The premises of the targets are the pins' own:
  `STExpDuhEq`, and `STExpDriftHiConcl` / `STExpDriftLoConcl` (the conclusions of other merged or owed gates).
- No external hypothesis is added.
- `stStep6IV_holds` = `ST_step6_caseIV_of_pins (stImproveExpAver_holds d) (stExpDuhamelZ_holds d) (stExpDriftLo_holds d)
  (stExpIntIV_holds d)`. All four are merged theorems or are proved in this file. No cycle: none of the dependencies imports
  `ExpIntEasy`.
- `λ ≠ 0` is used only in regime (iii). It is obtained eventually from `WO` (`st6_lam_pos`) and is not a new premise.
- Unused pinned binder: `_ht1 : ∀ n, t n < 1` in `STExpIntConcl_of_int`, which is the check file's statement. Harmless.

Registry pre-check (scratch `precheck.lean` = every `import` of the branch's `RBM3D.lean` + `import RBM3D.Induction.ExpIntEasy` +
`#assert_rbm_axioms`; first built those modules: `… | xargs lake build` → `Build completed successfully (4037 jobs).`, exit 0):
```
$ lake env lean precheck.lean ; echo precheck_exit=$?
precheck_exit=0
axiom audit: 6877 theorems, 2332 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 130 (borrowed 1, owed 92, structural 31, refuted 6).
registry: 2 borrowed + 142 owed + 88 structural + 7 refuted; 109 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
$ grep -nE 'STExpIntIII[],: ]|STExpIntIV[],: ]|STStep6IV[],: ]' precheck.out | wc -l
0
```

## 4. Compiled nonempty instances (`ExpIntEasy.lean:633-740`, compiled in the module build of §5)
| target | instance | data | open (allowed) |
|---|---|---|---|
| 7b `stExpIntIII_holds` | `inst_expIntIII_holds` | `sz0, z0, [0,1/16]` | stochastic premises of `InstIng6Concl` |
| 7b `stExpIntIV_holds` | `inst_expIntIV_holds` | `szG, zB, [5/8,3/4]` | same |
| 8 `stStep6IV_holds` | `inst_skeleton6IV_Int` | `szG, zB, [5/8,3/4]` | same (no pin open) |
| 7b + skeleton (iii) | `inst_skeleton6III_Int` | `sz0, z0, [0,1/16]` | `LWtermEXP 3` (LW-14, unproved pin) |
| 7a (iii) | `inst_expIntIII_concl` | `sz0, z0, κ=1/10, flow_z0, sz0_hs0/hst/ht/reg5III`, Duhamel `inst_duhEq_holds` | `STExpDriftHiConcl` |
| 7a (iv) | `inst_expIntIV_concl` | `szG, zB, flow_zG, 5/8<3/4, szB_flow_ht`, Duhamel `st6_duhEq_of_pin` | `STExpDriftLoConcl` |
| 1 | `inst_expIntEasy_integral_rpow` | `s=0, u=1/16, r=6/5` | none |
| 2a | `inst_expIntIII_rates_le_target` | `sz0, n=0, u=1/16, lam=1/64≠0, (1/64)²≤15/16` | none |
| 2b | `inst_expIntIV_rate_le_target` | `szG, n=0, u=3/4` | none |
| 3a, 3b | `example`s at `:697`, `:712` | `sz0,[0,1/16],M=1`; `szG,[5/8,3/4],M=1`; `F` = the nonzero bound | none |
| 4, 5a, 5b, 6 | `example`s at `:724-737` (partial applications) | `sz0/z0/[0,1/16]`, `szG/zB/[5/8,3/4]` | see Observation O1 |
Every window has positive length, `N ≥ 4096`, `L = 4`, and no `False` premise. The deterministic hypotheses (`3 ≤ 3`, `0 < 1/10`,
flow, time ordering, regime (iii), `t ≤ lemT`, `u < 1`, `λ ≠ 0`, `λ² ≤ 1-u`) are discharged by named merged facts or `norm_num`.

## 5. Build, axioms, hygiene (audit worktree)
```
$ lake build RBM3D.Induction.ExpIntEasy ; echo exit=$?
Build completed successfully (3859 jobs).
exit=0
$ grep -n 'ExpIntEasy' build.log | grep -E 'error|warning' | wc -l
0
$ grep -A1 'ExpIntEasy.lean:7[4-6][0-9]' build.log | grep -oE "'[^']+' depends on axioms: \[[^]]*\]"   (23 lines; all identical tail)
'RBM.Gauss.Sizes.expIntEasy_integral_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
… (expIntIII_rates_le_target, expIntIV_rate_le_target, expIntIII_drift_integral_le, expIntIV_drift_integral_le,
   expIntEasy_kernel_seq, expIntIII_int_unif, expIntIV_int_unif, STExpIntConcl_of_int, STExpIntIIIConcl_of_flow,
   STExpIntIVConcl_of_flow, stExpIntIII_holds, stExpIntIV_holds, stStep6IV_holds, and the 9 Step6Inst.inst_*: same list)
'RBM.Gauss.Step6Inst.inst_expIntIV_rate_le_target' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -E "depends on axioms" build.log | grep -v 'propext, Classical.choice, Quot.sound\]' | wc -l
0
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^\s*axiom ' RBM3D/Induction/ExpIntEasy.lean | wc -l
0
```
The hub still has to run the full `lake build` at merge, with the root import `RBM3D.Induction.ExpIntEasy`. The §3 pre-check with
that import exits 0.

## 6. Paper deltas
The prove report (d) proposes `T2235a`, `T2235b` and `T2235c`, which are the ticket's acceptance items (a), (b) and (c):
(a) one-sided `(1-v)B_v ≤ 2(1-u)B_u`, constant 64 (regime iii); (b) regime (iv) needs no regime, constant 1; (c) `ilambda > 0` eventually.

No other Lean/paper statement difference is introduced: the pins are merged texts, and their own deltas are already filed under
T2191/T2204. Coverage: complete.

## 7. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. The `example`s for targets 4 (`expIntEasy_kernel_seq`), 5a/5b (`expIntIII/IV_int_unif`) and 6 (`STExpIntConcl_of_int`) are
  partial applications. They leave open, respectively:
  - target 4: `X`, `hX` and the eventual drift bound;
  - targets 5a/5b: the drift-conclusion premise;
  - target 6: the drift-integral `Prec`.

  Ticket target 9 does not ask for instances of these, and each of them runs at fully concrete data inside the compiled proofs of
  `inst_expIntIII_concl` / `inst_expIntIV_concl` (`STExpIntIII/IVConcl_of_flow` → `*_int_unif` → `expIntEasy_kernel_seq`). Those
  proofs leave only `STExpDriftHiConcl` / `STExpDriftLoConcl` open, and both are other gates' conclusions.
- O2. The branch is not rebased on `f6650b2` (T2233). The hub merges by hand in the `Axioms.lean` owed region `:234-242`, as the
  ticket's merge note says.
- O3. Prove report (c) lists Mathlib names and says "Names verified absent: none checked". This is a report detail only.

## Verdict
| target | verdict |
|---|---|
| 1 `expIntEasy_integral_rpow` | PASS |
| 2a `expIntIII_rates_le_target`, 2b `expIntIV_rate_le_target` | PASS |
| 3a `expIntIII_drift_integral_le`, 3b `expIntIV_drift_integral_le` | PASS |
| 4 `expIntEasy_kernel_seq` | PASS |
| 5a `expIntIII_int_unif`, 5b `expIntIV_int_unif` | PASS |
| 6 `STExpIntConcl_of_int` | PASS |
| 7a `STExpIntIIIConcl_of_flow`, `STExpIntIVConcl_of_flow`; 7b `stExpIntIII_holds`, `stExpIntIV_holds` | PASS |
| 8 `stStep6IV_holds` | PASS |
| 9 instances (9) | PASS |
**Overall: PASS.** No dispatcher sign-off needed.
