Auditor model: claude-opus-5-5

# T2223 audit (round 1): S6-11 `Induction/ExpIniI`, route A

Time: Mon Oct  5 23:10:37 UTC 2026 (`date -u`). Branch `t/T2223` at `0d2f9ad` (base `afdb81e`). Audit worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2223-audit1` (detached, cache cloned per CLAUDE.md §2). Scratch files in
`<scratchpad>/T2223/`.

## 1. Scope and frozen files
```
$ git diff --stat main...t/T2223
 RBM3D/Induction/ExpIniI.lean | 1324 ++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean       |    3 +-
$ git diff main...HEAD -- RBM3D/Induction/Step6Pins.lean RBM3D/Induction/Step6Kit.lean | wc -l
       0
$ git diff main...HEAD -- RBM3D/Test/Axioms.lean   (the +/- lines)
-   `RBM.Gauss.Sizes.STExpIniIConcl] -- ... S6-01 (T2204, DECISIONS §67: structural)
+   `RBM.Gauss.Sizes.STExpIniIConcl, -- ... S6-01 (T2204, DECISIONS §67: structural)
+   `RBM.Gauss.Sizes.STExpIniIConcl'] -- ... positive mollifier constants (`6:117`; T2223a); S6-11 (T2223, DECISIONS §20: structural)
$ grep -nE "sorry|admit|native_decide|^\s*axiom |implemented_by|unsafe|opaque" RBM3D/Induction/ExpIniI.lean; echo $?
1
```
Only the two sole writable files; the Axioms change is exactly the route-A line (owed `STExpIniI` line kept).

## 2. Statements against the ticket pin (check file sections 2–3, compiled)
Scratch file `eq_check.lean` = check-file imports + `import RBM3D.Induction.ExpIniI` + check sections 1–2 verbatim
(lines `/^\/-! ## 1/,/^end RBM.Gauss.Sizes.T2223Check/`) + the following, then `#print axioms` of 19 declarations:
```
example : T2223Check.expIniI_fastDecay := @RBM.Gauss.Sizes.expIniI_fastDecay
example : T2223Check.expIniI_fastDecay_mono := @RBM.Gauss.Sizes.expIniI_fastDecay_mono
example : T2223Check.expIniI_same := @RBM.Gauss.Sizes.expIniI_same
example : T2223Check.expIniI_Qop := @RBM.Gauss.Sizes.expIniI_Qop
example : T2223Check.expIniI_mixed := @RBM.Gauss.Sizes.expIniI_mixed
example : T2223Check.expIniI_props_shift := @RBM.Gauss.Sizes.expIniI_props_shift
example : T2223Check.stExpIniI'_holds := @RBM.Gauss.Sizes.stExpIniI'_holds
example : T2223Check.ST_step6_caseI_of_pins' := @RBM.Gauss.Sizes.ST_step6_caseI_of_pins'
example : @T2223Check.STExpIniI' = @RBM.Gauss.Sizes.STExpIniI' := rfl
example : @T2223Check.STExpIniIConcl' = @RBM.Gauss.Sizes.STExpIniIConcl' := rfl
-- section 3 (namespace RBM.Gauss.Step6Inst), each statement copied from the check file:
example : InstIng6Concl (fun sz E s t => RBM.Gauss.Sizes.T2223Check.STExpIniIConcl' sz E s t) szB zB
    (fun _ => 7 / 8) (fun _ => 15 / 16) := inst_expIniI'
example : STExpLKLKHi 3 → ... → STExpIntI 3 → InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB ... := @inst_skeleton6I'
example : STDecay szB (STflowE zB) (fun _ => 7 / 8) → ∀ ε' D : ℝ, ... := @inst_expIniI_fastDecay
example : ∀ (C c : ℝ) (ϑ : ℝ → (Fin 2 → Zd 3 4) → ℂ), 0 ≤ c → ... := @inst_expIniI_props_shift
$ lake env lean eq_check.lean; echo exit=$?      (non-#check output lines; no 'error' line)
exit=0
```
All 8 pinned theorems, the 2 new `Prop` definitions (by `rfl`) and the 4 pinned instance statements match the check
file. Quantifier order, hypotheses (`3 ≤ d`, `0 < κ`, `0 < 𝔠d`, `d 𝔠d < 1`, `0 ≤ s`, `s < t`, `t ≤ lemT z`,
`STReg5I`, `STDecay`/`STExp2` at `s`, `STConStInd`, `0 < C`, `0 < c`, `∀ᶠ n` mollifier) are those of the pin.

Primed consumer vs merged consumer (script diff of the theorem bodies):
```
$ diff <Step6Kit.lean ST_step6_caseI_of_pins> <ExpIniI.lean ST_step6_caseI_of_pins'>
1c1  < theorem ST_step6_caseI_of_pins (hLK ...      > theorem ST_step6_caseI_of_pins' {d : ℕ} (hLK ...
3c3  <     (hIni : STExpIniI d) ...                  >     (hIni : STExpIniI' d) ...
54c54 <     (hini.2 C c' ϑ hϑ)                       >     (hini.2 C c' hC hc' ϑ hϑ)
85,90d84  (trailing section header of Step6Kit only)
```
Exactly the change the ticket allows (target 7).

## 3. Route, special case, vacuity, hidden hypotheses
- Route A, as the ticket expects: `STExpIniI'` is the merged `STExpIniI` with `0 < C → 0 < c →` in the second conjunct.
  This is a weaker variant of the merged pin and is **not** claimed as `STExpIniI`: the owed line stays
  (`RBM.Gauss.Sizes.STExpIniI: 4 [no certificate]` in the pre-check below). The ticket pins exactly this target.
- Against the paper: `Def:QtPt` (`paper/tex/3_5_Loop_Hierarchy.tex`) reads "along with the following estimates for a
  constant $c>0$"; `0 < C` is forced anyway by clause 1 of `STMollifierProps` (`Σ ϑ = 1` with `‖ϑ‖ ≤ C·(positive)`).
  So the primed statement is the paper's. The merged pin's `c ≤ 0` case is the T2223a finding (not compiled as a
  refutation; `expIniI_props_shift` + `inst_expIniI_props_shift_ex` show the class is larger, nothing more).
- No new structure; `STExpIniIConcl'` and `STExpIniI'` are `Prop` defs (`rfl` above), no hypothesis hidden in a field.
- Dependencies: every name used is on `main` (check file section 1 compiles in the same file); no cycle (the new
  file imports 9 merged modules; nothing imports it).
- `stExpIniI'_holds` instantiates `𝔠_d = 1/(100 d)` and uses only `STDecay`, `STExp2`, `STConStInd` and the
  deterministic data of `STIngR6`; the other `STIngR6` premises are dropped (`_`): stronger, not weaker.
- External hypotheses: none new. The random inputs `STDecay`, `STExp2` at `s` are premises of the merged `STIngR6`.

## 4. Compiled nonempty instances (namespace `RBM.Gauss.Step6Inst`, same file, all compile)
| endpoint | instance | data / what stays a hypothesis |
|---|---|---|
| 1a `expIniI_fastDecay` | `inst_expIniI_fastDecay` | `szB`, `zB`, `s ≡ 7/8`; `flow_zB`, `szB_flow_ht` discharged; `STDecay` at `s` kept |
| 1b `expIniI_fastDecay_mono` | `inst_expIniI_fastDecay_mono` | `d=3,L=4,n=2,g=1,s=7/8,v=15/16,W=5,ε=1/100,D=5`, `A=1_{a₀=a₁}`; hypothesis proved |
| 2 `expIniI_same` | `inst_expIniI_same` | `szB`,`zB`,`(7/8,15/16)`, `𝔠d=1/300`, `szB_reg5I`, `conStInd_const`; `STDecay`,`STExp2` kept |
| 3 `expIniI_Qop` | `inst_expIniI_Qop` | as 2, mollifier from `st6_mollifier_family` (`0<C`,`0<c`, eventual props proved) |
| 4 `expIniI_mixed` | `inst_expIniI_mixed` | as 2 + mollifier family as 3 |
| 5 `expIniI_props_shift` | `inst_expIniI_props_shift`, `inst_expIniI_props_shift_ex` | `d=3,L=4,g=1,v=2e₀`; `_ex` builds `ϑ` from `stMollifierEx_holds` with `0<C,0<c`, premise discharged |
| 6a `stExpIniI'_holds` | `inst_expIniI'` | `inst_ing6_I STReg5I _ (stExpIniI'_holds 3) szB_reg5I`; stochastic premises of `InstIng6Concl` kept |
| 7 `ST_step6_caseI_of_pins'` | `inst_skeleton6I'` | other regime-(i) pins (`STExpLKLKHi … STExpIntI`) kept as hypotheses (other gates' pins) |
Data `szB`: `L = 4`, `W_n = n + 4`, `ilambda = 1`, `(s,t) = (7/8, 15/16)` (`1-t = ilambda²/L²`): nondegenerate, no
`N = 0`, no empty index, no `False` premise. Every deterministic hypothesis is discharged.

## 5. Build and axioms (audit worktree)
```
$ lake build RBM3D.Induction.ExpIniI      (warning/error lines naming ExpIniI.lean: none)
✔ [3847/3847] Built RBM3D.Induction.ExpIniI (17s)
Build completed successfully (3847 jobs).
exit=0
$ lake build   (full library, root #assert_rbm_axioms; tail)
Build completed successfully (4024 jobs).
exit=0
$ lake env lean eq_check.lean | grep 'depends on axioms' | sed 's/.*axioms: //' | sort | uniq -c
  19 [propext, Classical.choice, Quot.sound]
  (the 19: expIniI_fastDecay, _mono, expIniI_same, expIniI_Qop, expIniI_mixed, expIniI_props_shift, stExpIniI'_holds,
   ST_step6_caseI_of_pins', STExpIniIConcl', STExpIniI', inst_expIniI', inst_skeleton6I', inst_expIniI_fastDecay,
   inst_expIniI_fastDecay_mono, inst_expIniI_same, inst_expIniI_Qop, inst_expIniI_mixed, inst_expIniI_props_shift(_ex))
$ registry pre-check: pre.lean = import RBM3D; import RBM3D.Induction.ExpIniI; #assert_rbm_axioms; lake env lean
  RBM.Gauss.Sizes.STExpIniI: 4 [no certificate]
premises found by scanning: 125 (borrowed 1, owed 94, structural 24, refuted 6).
registry: 2 borrowed + 145 owed + 81 structural + 7 refuted; 110 registered premise(s) carry nothing yet: [...
 RBM.EKFastDecay,
 RBM.Gauss.Sizes.STExpIniIConcl,
 RBM.Gauss.Sizes.STExpIniIConcl',
exit=0
```
Owed count 145 unchanged, structural 80 → 81 (prove report's base output), as route A requires.

## 6. Paper deltas
- Lean/paper difference 1: merged `STExpIniIConcl` quantifies over all `(C, c)` (paper `c > 0`): proposed as
  candidate `T2223a` in prove report (d); not yet in `docs/paper-deltas.md` (`grep -n T2223` empty), which is the
  dispatcher's step. Covered.
- `STExpIniI'`/`STExpIniIConcl'` themselves agree with `Def:QtPt` (`c > 0`); no further delta. Same unrestricted
  quantifier in `STExpIntQConcl`, `STExpWardIConcl` is recorded in (d) for the dispatcher (not this ticket's targets).

## 7. Verdicts
| target | verdict |
|---|---|
| 1a `expIniI_fastDecay` | PASS |
| 1b `expIniI_fastDecay_mono` | PASS |
| 2 `expIniI_same` | PASS |
| 3 `expIniI_Qop` | PASS |
| 4 `expIniI_mixed` | PASS |
| 5 `expIniI_props_shift` | PASS |
| 6a `STExpIniIConcl'`, `STExpIniI'`, `stExpIniI'_holds` | PASS (route A; primed successor, merged `STExpIniI` stays owed) |
| 6b `stExpIniI_holds` | not a target on route A |
| 7 `ST_step6_caseI_of_pins'` | PASS |
| 8 instances | PASS |

**Overall: PASS.**

## 8. Observations (no RETURN)
1. Registry artifact: `scanPremises` now counts `expIniI_fastDecay_mono` (conclusion head `EKFastDecay`) as a proof
   of the structural `RBM.EKFastDecay`, so the scanned structural count drops 25 → 24 and `EKFastDecay` joins the
   "carry nothing yet" list. `#assert_rbm_axioms` exits 0; documented in prove report (d). Dispatcher may note it.
2. The ticket's line reference `Axioms.lean:239` is `:237` at the branch base (prove report observation); no effect.
3. `main` moved to `cd6fcba` (T2222, which deletes owed line `:232`) after the branch base `afdb81e`; the T2223
   Axioms hunk is at the end of `structuralProps`, so the hub's union must keep `]` on the last entry.
4. The routing decision for the merged `STExpIniI` (`c ≤ 0`: Ward route or "superseded") stays with the
   dispatcher/supervisor per the ticket; it does not affect this verdict.
