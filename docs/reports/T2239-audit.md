Auditor model: claude-opus-5-5

# T2239 audit (S6-09a, `RBM3D/Induction/ExpIntI.lean`) — round 1, Tue Oct  6 02:09:09 UTC 2026

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2239-audit1` at `t/T2239` = `3fcac0f` (base `e5b944a`; `main` = `fd80185`); scratch `…/scratchpad/T2239/audit_*`.

## 1. Diff scope, frozen files
```
$ git diff --stat main...t/T2239
 RBM3D/Induction/ExpIntI.lean | 901 +++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean       |   6 +-
$ git diff --stat main...HEAD -- RBM3D/Induction/{Step6Pins,Step6Kit,ExpIniI,ExpWardI,ExpIntII}.lean RBM3D/Evolution/Prec.lean | wc -l
       0
$ git merge-tree --write-tree main t/T2239 >/dev/null; echo rc=$?     # main = fd80185
rc=0
```
`Axioms.lean` diff (verbatim hunks, abbreviated to the `+`/`-` lines):
```
-   `RBM.Gauss.Sizes.STExpIntI, -- `6:97`, `6:104-132` integrated estimate, regime (i): S6-09; S6-01 (...: owed)
-   `RBM.Gauss.Sizes.STExpIniI, -- `6:117`, ... initial term, regime (i): S6-11; S6-01 (...: owed)
+   `RBM.Gauss.Sizes.STExpIntI, -- superseded, not needed (DECISIONS §68 (9), §73 (4)): successor STExpIntI' (S6-09) / STExpIniI' (proved, T2223); consumer ST_step6_caseI_of_pins'' (T2239)
+   `RBM.Gauss.Sizes.STExpIniI, -- superseded, not needed (DECISIONS §68 (9), §73 (4)): ... (same comment)
+   `RBM.Gauss.Sizes.STExpIntI', -- `6:97`, `6:104-132` integrated estimate, regime (i), primed (...): S6-09b; S6-09a (T2239, DECISIONS §20: owed)
+   `RBM.Gauss.Sizes.STExpIntQConcl', -- conclusion of the integrated estimate with Q, regime (i), positive mollifier constants (...); S6-09a (T2239, DECISIONS §20: structural)
```
Exactly the lines the ticket's "Sole writable files" paragraph prescribes (comments rewritten, both lines kept; owed after `STExpIniI`; structural after `STExpWardIConcl'`).

## 2. Statements against the ticket's pin (check file `docs/tickets/checks/T2239-check.lean`)
Scratch `audit_eq.lean` = check-file lines 1-31 (imports) + `import RBM3D.Induction.ExpIntI` + check-file lines 32-283 (sections 1-2) +
7 `example : RBM.Gauss.Sizes.T2239Check.X := @RBM.Gauss.Sizes.X` (X = `expIntI_ratio_le`, `expIntI_log_ratio`, `expIntI_kernel_unif`,
`expIntI_concl_of_kernel`, `expIntI_same`, `ST_step6_caseI_of_pins''`, `ST_step6I_of_LW_Int`) + 2 `rfl` (`STExpIntI'`, `@STExpIntQConcl'`)
+ 3 section-3 statements `:= @RBM.Gauss.Step6Inst.inst_skeleton6I''`, `@…inst_expIntI_same`, `@…inst_expIntI_log_ratio`.
```
$ lake env lean audit_eq.lean > audit_eq.log 2>&1; echo exit=$?; grep -cE "error" audit_eq.log
exit=0
0
```
So all seven theorem statements, both `Prop` definitions (definitional `rfl`) and the three section-3 instance statements are exactly the pinned ones.
Mathematical reading (against ticket "Mathematics" (1)-(5), `6:97`, `(sum_res_2_NAL)`/`(sum_res_2)` `3_5:1649-1662`):
- T1 `(g²+|1-v|)/(g²+|1-u|) ≤ 2` under `s ≤ v ≤ u < 1`, `1-s ≤ g²`: the regime-(i) ratio, constant 2 as in the ticket.
- T2 `∫_s^u (1-v)⁻¹ ≤ 2 log L` under `1-s ≤ g²`, `g²/L² ≤ 1-u`: exactly the regime-(i) window `λ²/L² ≤ 1-u ≤ 1-s ≤ λ²`.
- T3 hypotheses `∀ n`, conclusion `∀ᶠ n, ∀ u ∈ [s_n,t_n], ∀ v ∈ [s_n,u]` (uniform in the end time; parameters before `∀ᶠ`), case split NAL `σ0 = σ1` / sum-zero, loss `4X` (= max of `ρ ≤ 2`, `ρ² ≤ 4`).
- T4 `A = ∅`, `P` arbitrary, kernel hypothesis with drift rate `(1-v)⁻¹(B^{11/5}+B^{5/2})`; conclusion `STExpIntConcl sz ∅ P E s t`.
- T5 first conjunct `STExpIntConcl … ∅ STSigSame …` from Duhamel + drift hi + drift decay, flow `STflowE z`, `(con_st_ind)` with `d𝔠_d < 1`.
- T6a/6b: conclusion `STStep6I d` unchanged; premises `STExpWardI' d`, `STExpIntI' d` as fixed by §73 (3).
No special case / conditional adapter is presented as a general statement: T3-T5 are the regime-(i) lemmas the ticket asks for; the `𝒬` conjunct is explicitly S6-09b.

## 3. Hidden hypotheses, vacuity, cycles
```
$ grep -nE "^\s*(variable|set_option|attribute|local instance|@\[)" RBM3D/Induction/ExpIntI.lean
41:set_option linter.style.longLine false
$ grep -nE "^(theorem|def|private|namespace|end)" RBM3D/Induction/ExpIntI.lean | cut -c1-60   (excerpt)
56:def STExpIntQConcl' ...      71:def STExpIntI' ...          80:theorem expIntI_ratio_le ...
90:theorem expIntI_log_ratio ...253:theorem expIntI_kernel_unif ...  356:theorem expIntI_concl_of_kernel ...
465:theorem expIntI_same ...    573:theorem ST_step6_caseI_of_pins'' ...  660:theorem ST_step6I_of_LW_Int ...
```
No `variable` binders, no new structure; the only new `Prop` definitions are the two pinned ones (verified `rfl` above).
`STExpIntI'` is a hypothesis of 6a/6b/`inst_skeleton6I''`, registered owed (S6-09b); `STExpIntQConcl'` registered structural. Dependencies
are merged declarations (imports: `ExpWardI`, `ExpIntII`, `ExpIniI`, `ExpEtermsA`, `ExpEtermsB`, `ExpAvg`, `ExpDuhamel`, `Evolution.Prec`); no cycle.
Consumer check (§45 O2):
```
$ sed -n 1127,1208p ExpIniI.lean > audit_old.lean; sed -n 573,654p ExpIntI.lean > audit_new.lean; diff audit_old.lean audit_new.lean
1,3c1,3
< theorem ST_step6_caseI_of_pins' {d : ℕ} (hLK : STExpLKLKHi d) (hLW : LWtermEXP d) (hAvg : STImproveExpAver d)
<     (hDu : STExpDuhamelZ d) (hDuQ : STExpDuhamelQ d) (hDec : STExpDriftDecay d) (hWd : STExpWardI d)
<     (hIni : STExpIniI' d) (hInt : STExpIntI d) : STStep6I d := by
---
> theorem ST_step6_caseI_of_pins'' {d : ℕ} (hLK : STExpLKLKHi d) (hLW : LWtermEXP d) (hAvg : STImproveExpAver d)
>     (hDu : STExpDuhamelZ d) (hDuQ : STExpDuhamelQ d) (hDec : STExpDriftDecay d) (hWd : STExpWardI' d)
>     (hIni : STExpIniI' d) (hInt : STExpIntI' d) : STStep6I d := by
53c53
<   have hmainQ := hint.2 C c' ϑ hϑ hduhQ (fun n p => STExpTarget sz n (p.1 : ℝ)) (fun n p => hT0 n _ p.1.2.2)
---
>   have hmainQ := hint.2 C c' hC hc' ϑ hϑ hduhQ (fun n p => STExpTarget sz n (p.1 : ℝ)) (fun n p => hT0 n _ p.1.2.2)
55c55
<   have hw := (hward C c' ϑ hϑ).1
---
>   have hw := (hward C c' hC hc' ϑ hϑ).1
```
Exactly the name, the two binder types and the two application lines, as the ticket requires.
External hypotheses kept open: `LWtermEXP` (LW-14), `STExpIntI'` (S6-09b), `STExpDriftHiConcl`/`STExpDriftDecayConcl` (stochastic conclusions
of S6-06/LW-14/S6-07). The ticket names them as allowed open hypotheses; none is introduced by this ticket except `STExpIntI'` (pinned by §73 (3)).

## 4. Compiled nonempty instances (namespace `RBM.Gauss.Step6Inst`, `d = 3`, `szB`: `L = 4`, `W_n = n+4`, `λ = 1`; `zB`; `(s,t) = (7/8, 15/16)`)
| target | instance (file line) | open hypotheses | deterministic data discharged |
|---|---|---|---|
| T1 | `inst_expIntI_ratio_le` (707) | none | `(7/8, 7/8, 15/16)`, `g = 1` |
| T2 | `inst_expIntI_log_ratio` (701) | none | `L = 4`, `g = 1`, `1-u = g²/L²` |
| T3 NAL | `inst_expIntI_kernel_unif` (735) | `τ > 0` only | `σ = (+,+)`, `𝒜 = 1_{a₀=a₁}` (decay proved), `X ≡ 1`, flow, regime, `conStInd_const`, `𝔠d = 1/300` |
| T3 sum-zero | `inst_expIntI_kernel_unif_sumzero` (838) | `τ > 0` only | `σ = ![true,false]`, dipole `1_{a₁=a₀} − 1_{a₁=a₀+e₀}`, sum-zero and decay proved |
| T3 nonzero | `inst_expIntI_tensors_ne_zero` (871) | none | both tensors `≠ 0` at `a = 0` |
| T4 | `inst_expIntI_concl_of_kernel` (884); also applied inside `expIntI_same` at the `inst_expIntI_same` data | `hker` (kernel bound of the drift; derived in T5 from the drift conclusions) | `A = ∅`, `STSigSame`, Duhamel `st6_duhEq_of_pin` |
| T5 | `inst_expIntI_same` (687) | `STExpDriftHiConcl`, `STExpDriftDecayConcl` (other gates' conclusions) | flow `flow_zB`, `szB_flow_ht`, `szB_reg5I`, `conStInd_const`, Duhamel from `stExpDuhamelZ_holds 3` |
| T6a/6b | `inst_skeleton6I''` (680) = `inst_step6I (ST_step6I_of_LW_Int 3 hLW hInt)` | `LWtermEXP 3`, `STExpIntI' 3` | all other Step-6 ingredient pins by their merged proofs |
No `N = 0` (`size ≥ 1`), no empty index (`L = 4`), window `7/8 < 15/16` nondegenerate, no `False` premise. All compile (build §5).

## 5. Build, axioms, forbidden tokens (audit worktree)
```
$ lake build RBM3D.Induction.ExpIntI; echo exit=$?
✔ [3873/3873] Built RBM3D.Induction.ExpIntI (11s)
Build completed successfully (3873 jobs).
exit=0
$ grep -c "ExpIntI.lean" audit_build.log        # warning/error lines of the new file
0
$ grep -nE "sorry|admit|native_decide|^axiom|[^a-z_]axiom " RBM3D/Induction/ExpIntI.lean; echo rc=$?
rc=1
$ lake env lean audit_ax.lean | sed 's/.*depends on axioms: //' | sort | uniq -c   # #print axioms of the 17 public declarations
  17 [propext, Classical.choice, Quot.sound]
(names: STExpIntQConcl', STExpIntI', the 7 theorems of §2, inst_skeleton6I'', inst_expIntI_{same,log_ratio,ratio_le,kernel_unif,
 kernel_unif_sumzero,tensors_ne_zero,concl_of_kernel})
$ lake build RBM3D; echo exit=$?                 # branch root (new module not yet imported)
info: RBM3D.lean:281:0: axiom audit: 6934 theorems, 2340 definitions, 0 axioms in `RBM` (...)
registry: 2 borrowed + 143 owed + 89 structural + 7 refuted; 114 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
exit=0
$ lake env lean audit_pre.lean   # import RBM3D; import RBM3D.Induction.ExpIntI; #assert_rbm_axioms (registry pre-check, §20 (2))
exit=0
axiom audit: 6949 theorems, 2342 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
registry: 2 borrowed + 143 owed + 89 structural + 7 refuted; 113 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
```

## 6. Paper deltas
- Positive mollifier constants in `STExpIntQConcl'`/`STExpIntI'`: covered by D542 (T2223a) and D549 (T2232a) in `docs/paper-deltas.md`
  (`grep -n "T2223a\|T2232a" docs/paper-deltas.md` → lines 1501, 1508).
- Regime-(i) `σ₁ = σ₂` made explicit (ratio `≤ 2`, `∫ ≤ 2 log L`, rates `3T_u`, loss `4` absorbed into `N^τ`): proposed as `T2239b` in the prove report (d).
- Finding `T2239a` (S6-09b route): proposed in the prove report (d). Audit check of the premise: the merged clause 4 of `STMollifierProps`
  (`Step34Pins.lean:515`) is `‖deriv (fun τ => ϑ τ a) t‖ ≤ C * (1 - t)⁻¹ * (((ellT L g t) ^ d)⁻¹) ^ m` — no spatial decay factor, as stated.
No other Lean/paper statement difference found.

## 7. Observations (no verdict effect)
- O1. The prove report's tag naming swaps the ticket's: the ticket calls the explicit-`(sum_res_2_NAL)` candidate "(a)" and the finding "T2239a";
  the report uses `T2239a` = finding, `T2239b` = explicit regime-(i) candidate. Both candidates are present; the dispatcher numbers them.
- O2. `T2239a` is a pending dispatcher item for S6-09b (ticket (iv)); it does not affect any statement of this ticket (the two definitions are
  fixed by §73 (3) "in any case"). Its resolution decides whether `STExpIntI'` is provable; until then 6a/6b/`inst_skeleton6I''` carry it as an owed premise.
- O3. `𝔠d = 1/300` in the instances makes `(con_st_ind)` hold only from `n ≈ 1.3e30` (prove report F2); the instance discharges it by the
  merged limit lemma `conStInd_const` (an `∀ᶠ` statement), not by an explicit astronomical witness; value pinned by the ticket.
- O4. `inst_expIntI_concl_of_kernel` keeps `hker` open; T4 is also applied at the same data inside `expIntI_same` (`inst_expIntI_same`).

## Verdict
| target | verdict |
|---|---|
| 1 `expIntI_ratio_le` | PASS |
| 2 `expIntI_log_ratio` | PASS |
| 3 `expIntI_kernel_unif` | PASS |
| 4 `expIntI_concl_of_kernel` | PASS |
| 5 `expIntI_same` | PASS |
| 6 `STExpIntQConcl'`, `STExpIntI'`, `ST_step6_caseI_of_pins''`, `ST_step6I_of_LW_Int` | PASS |
| 7 instances `inst_skeleton6I''`, `inst_expIntI_same`, `inst_expIntI_log_ratio` (+5 extra) | PASS |
| registry (`Test/Axioms.lean`) | PASS |
Overall: **PASS**. No dispatcher sign-off needed for this ticket; T2239a goes to the dispatcher before S6-09b per the ticket.
