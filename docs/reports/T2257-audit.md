Auditor model: claude-opus-5-5
# T2257 audit (S6-09b, `Induction/ExpIntIQ`), round 1 (Tue Oct  6 06:00:44 UTC 2026)

Branch `t/T2257` head `4d984b5` (merge base `a18620d`; `main` now `d0484be`). Audit worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2257-audit1` (detached at `4d984b5`). Scratch files in the session scratchpad `T2257/`.

## 1. Diff scope, frozen files, merge
```
$ git diff --stat main...t/T2257
 RBM3D/Induction/ExpIntIQ.lean | 1545 +++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean        |    2 +-
$ git diff main...t/T2257 -- RBM3D/Test/Axioms.lean   (hunks only)
@@ -256,7 +256,6 @@ def owedProps
-   `RBM.Gauss.Sizes.STExpIntI', -- `6:97`, `6:104-132` integrated estimate, regime (i), primed (...): S6-09b; S6-09a (T2239, DECISIONS §20: owed)
@@ -360,6 +359,7 @@ def structuralProps
+   `RBM.Gauss.Sizes.STSigMixed, -- the sign class `σ₁ ≠ σ₂` of the index set `STIdx2P` (`6:104`): a data predicate, ... (T2257, DECISIONS §20: structural)
$ git diff main...t/T2257 --stat -- ExpIntI Step6Pins QopDecay ExpWardI QopAlgebra QopNorm Step6Kit Step34Pins | wc -l
0
$ git merge-tree --write-tree main t/T2257 >/dev/null; echo $?
0
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Induction/ExpIntIQ.lean; echo $?
1
```
`STSigMixed` is `def STSigMixed (σ : Fin 2 → Bool) : Prop := σ 0 ≠ σ 1` (`Step5Pins.lean:312`). This is a data condition,
so DECISIONS §20 classifies it as structural. The ticket allows a line forced by the pre-check if it is listed, and the prove report lists it (narrative 7, (d)(i)).

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Induction.ExpIntIQ
✔ [3875/3875] Built RBM3D.Induction.ExpIntIQ (14s)
Build completed successfully (3875 jobs).        exit 0   (0 warnings in ExpIntIQ.lean)
$ lake env lean T2257_auditax.lean    # #print axioms of all 23 public `theorem`/`def` lines of the file
'RBM.Gauss.Sizes.expIntIQ_star' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expIntIQ_star_props' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expIntIQ_Qop_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expIntIQ_diff_sumZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expIntIQ_src_sumZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expIntIQ_src_decay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expIntIQ_ini' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expIntIQ_star_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expIntIQ_back' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expIntIQ_concl' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stExpIntI'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stStep6I_of_LW' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expIntI'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expIntIQ_star_props' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expIntI'_mixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_stStep6I_of_LW' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expIntIQ_Qop_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expIntIQ_diff_sumZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expIntIQ_src_sumZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expIntIQ_src_decay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expIntIQ_ini' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expIntIQ_star_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expIntIQ_back' depends on axioms: [propext, Classical.choice, Quot.sound]
ax exit 0
```
Registry pre-check, using no source edit: a scratch file with the content of the branch's `RBM3D.lean` and
`import RBM3D.Induction.ExpIntIQ` added after its last import line. The file ends with `#assert_rbm_axioms`. All imported modules were built by `lake build RBM3D`.
```
$ lake env lean T2257_auditroot.lean      exit 0
axiom audit: 7599 theorems, 2548 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 153 (borrowed 1, owed 97, structural 38, refuted 6, superseded 11).
registry: 2 borrowed + 157 owed + 99 structural + 7 refuted + 12 superseded; ...
$ lake build RBM3D        # branch root WITHOUT the new import (control)
error: RBM3D.lean:300:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of ...:
  [RBM.Gauss.Sizes.STExpIntI']
```
The control behaves as expected. Once its `owedProps` line is deleted, `STExpIntI'` is proved only by `ExpIntIQ`. The hub must therefore
add the root import `import RBM3D.Induction.ExpIntIQ` in the same merge commit (§3 (A) step 4).

## 3. Statements against the pin: check-file equality, compiled
Script `mkeq.py` builds the scratch file from: lines 1–314 of `docs/tickets/checks/T2257-check.lean` (sections 1–2), `import RBM3D.Induction.ExpIntIQ`,
one vocabulary equality, 11 theorem equalities, and 4 section-3 instance equalities. For the instance equalities, `T2257Check.expIntIQ_star` is rewritten to `expIntIQ_star`.
```
$ python3 mkeq.py
equality examples: 12 + instance examples: 4
example : @RBM.Gauss.Sizes.T2257Check.expIntIQ_star = @RBM.Gauss.Sizes.expIntIQ_star := rfl
example : RBM.Gauss.Sizes.T2257Check.<X> := @RBM.Gauss.Sizes.<X>   for X in expIntIQ_star_props, expIntIQ_Qop_sub,
  expIntIQ_diff_sumZero, expIntIQ_src_sumZero, expIntIQ_src_decay, expIntIQ_ini, expIntIQ_star_bound, expIntIQ_back,
  expIntIQ_concl, stExpIntI'_holds, stStep6I_of_LW
example : <section-3 statement> := @RBM.Gauss.Step6Inst.<I>  for I in inst_expIntI', inst_expIntIQ_star_props,
  inst_expIntI'_mixed, inst_stStep6I_of_LW
$ lake env lean T2257_auditeq.lean   -> no error lines; eq exit 0
```
- Target 10: `stExpIntI'_holds (d : ℕ) : STExpIntI' d`. This is the merged pin `ExpIntI.lean:71`, and the file is unchanged (§1). The pin keeps
  `STIngR6 d STReg5I (… → STExpWardIConcl' … → STExpIntConcl … ∧ STExpIntQConcl' …)`, quantifies `∀ C c, 0<C → 0<c → ∀ ϑ` over the whole
  admissible class with an arbitrary `F`, uses the index set `STIdx2P sz STSigMixed s t` (σ₁ ≠ σ₂), and has the right-hand side `F + STExpTarget`. These match `6:104-132` (`int_K-L+QE`).
  The witness `𝔠d = 1/(100 d)` satisfies `0 < 𝔠d ≤ 1/100` and `d𝔠d = 1/100 < 1` for every `d ≥ 3` (file `:1349-1354`).
- Target 11: `stStep6I_of_LW d h := ST_step6I_of_LW_Int d h (stExpIntI'_holds d)`, as pinned. `LWtermEXP` is the only open input.
- Targets 1–9: these are the check-file statements (compiled above). They are the transfer steps (d)(1)–(5). `ϑ*` is `QopAlgebra_mollifier d (L n) 1 (lam n)`
  verbatim (`rfl`). Constants `C* = (1+40d)6^d`, `c = 1/2` appear only in targets 1 and 8 and in the instances. None of them is a special-case substitute for a general target:
  the general pin (target 10) is proved for every `d` and every admissible `ϑ`.

## 4. Hidden hypotheses, vacuity, cycles
- The new file declares no `structure`, `class` or `instance` (outline grep: only `def expIntIQ_star`, `theorem`s, and `private theorem`s with prefix `expIntIQ_`).
  No hypothesis is carried in a field.
- Dependencies are merged modules only (imports `:6-18`, all on `main`). No pin of this ticket is assumed. `expIntIQ_concl` takes
  `STExpDriftHiConcl`, `STExpDriftDecayConcl` and `STExpWardIConcl'` as premises, exactly as the pin `STExpIntI'` does. No cycle.
- External hypothesis: none new. `STConStInd` enters through the merged `conStInd_const` (eventual). The prove report (a)(ii) gives the limit check:
  `B_t = Bparam(t) W⁻³ → 0`.
- Unused premises reported in (d): `0<ε`, `s<t` in target 5; `0 ≤ G` in target 7; `s<t`, `t<1` in target 8; `STExpDuhEqQ … ϑ` in target 9.
  They are pinned hypotheses that the proofs do not need. This is not vacuity and does not weaken any statement.

## 5. Compiled nonempty instances (in `ExpIntIQ.lean`, `RBM.Gauss.Step6Inst`)
The data are `d = 3`, `szB` (`L = 4`, `W_n = n+4`, `ilambda = 1`), `zB`, the flow `(1/10,1/10,1/6,1/10)`, times `(7/8, 15/16)` and `𝔠d = 1/300`.
| target | instance | deterministic hypotheses discharged | left open (other gates' pins) |
|---|---|---|---|
| 1 | `inst_expIntIQ_star_props` | `szB_WO` | none |
| 2 | `inst_expIntIQ_Qop_sub` | mollifiers `g = 1/2, 1`, diagonal `A` | none |
| 3 | `inst_expIntIQ_diff_sumZero` | `ϑ`, its shift by `2e₀` (both via `QopAlgebra_mollifier_props`) | none |
| 4 | `inst_expIntIQ_src_sumZero` | `n=0, E=0, v=7/8, σ=(+,-)` | none |
| 5 | `inst_expIntIQ_src_decay` | flow, times, regime `szB_reg5I` | `STExpDriftHiConcl`, `STExpDriftDecayConcl` |
| 6 | `inst_expIntIQ_ini` | `st6_mollifier_family`, `conStInd_const` | `STExpWardIConcl'`, the control `F` (statement datum) |
| 7 | `inst_expIntIQ_star_bound` | as above | drift and Ward conclusions |
| 8 | `inst_expIntIQ_back` | `st6_mollifier_family`, `inst_expIntIQ_star_props` | `STExpWardIConcl'` |
| 9 | `inst_expIntI'_mixed` | `ϑ = ϑ*`, `C*`, `1/2`, `STExpDuhEqQ` by `st6_duhEqQ_of_pin` | drift and Ward conclusions |
| 10 | `inst_expIntI'` | `inst_ing6_I STReg5I _ (stExpIntI'_holds 3) szB_reg5I` | stochastic premises of `InstIng6Concl` |
| 11 | `inst_stStep6I_of_LW` | `inst_step6I (stStep6I_of_LW 3 h)` | `LWtermEXP 3` |
No instance uses `N = 0`, an empty index set, a collapsed window (`7/8 < 15/16`, regime (i)) or a `False` premise. All four required instances match
check section 3 by the compiled equality (§3).

## 6. Paper deltas
- The report proposes candidate (a) (`6:104-132`, transfer `R_s = (𝒫f_s)(ϑ_s − ϑ*_s)` from one decaying mollifier, keeping the paper's class). It is already
  recorded in `main:docs/paper-deltas.md:1515` (D556 / T2239a, "形式化保留论文的类作结论，由显式磨光函数 `QopAlgebra_mollifier` 转移").
- No `T2257a` (preflight (v) PASS) and no `T2257b…` (no statement lacked a hypothesis). The Lean statements (check file) add no other difference from
  the paper.

## 7. Observations (no RETURN)
1. Merge: the root import of `RBM3D.Induction.ExpIntIQ` is mandatory in the same commit. Without it the root `#assert_rbm_axioms` fails on `STExpIntI'` (§2 control).
   `Axioms.lean` has two hunks: the deletion and the forced `STSigMixed` structural line. The ticket's merge note expected one hunk.
   `git merge-tree` with the current `main` is clean.
2. Seven additional public instance names `inst_expIntIQ_{Qop_sub,diff_sumZero,src_sumZero,src_decay,ini,star_bound,back}` are not pinned. They have
   0 hits on `main` (`git grep -F`), live in `RBM.Gauss.Step6Inst`, and carry the file stem.
3. `(con_st_ind)` at `𝔠d = 1/300` holds only for `W ≳ 1.3e30` (prove report (a)(ii)). This comes from the merged eventual hypothesis and its
   `conStInd_const` limit lemma, as in every merged Step-6 instance. It is not specific to T2257.
4. The ticket's equality script needs `@` on the left of the vocabulary equality (implicit `d`). The prove report notes this (narrative 8).

## Verdict
Targets 1–11 and the instances (target 12): **PASS**. No dispatcher sign-off needed.
