Auditor model: claude-opus-5-5
# T2041 audit (round 2) — ST-D3, Steps 3–4 pins (design / probe)
Written Sat Oct  3 10:20:25 UTC 2026 (`date -u`). Audit worktree `../RBM3D-wt/T2041-audit2`, detached at `3c58211` (`t/T2041`), merge-base with `main` `64bdfd3`.

**Verdict: PASS.** Round 1 (at `80162ae`) returned R1–R3. This round checks the repair commit `3c58211` and re-runs the build and axiom checks. Dispatcher sign-off is not needed: the split has 34 tickets, which is in 25–40 (DECISIONS §9 O2).

## 0. Repair scope: instances only, no pin changed
```
$ git log --oneline main..t/T2041 | head -1
3c58211 T2041: probe repair R1, R2: instances of STLmax_of_STLmaxU, STLK_of_STLKU and the case-(ii) Step 3 skeleton
$ git diff --numstat 80162ae HEAD; git diff -U0 80162ae HEAD | grep "^@@"
132	0	RBM3D/Probe/T2041Pins.lean
@@ -1801,0 +1802,10 @@ theorem inst_step4_skeletonB (hBoot : STXiBoot szB (STflowE zB) (fun _ => 15 / 1
@@ -1892,0 +1903,114 @@ theorem inst_step3_skeleton
@@ -2067,0 +2192,8 @@ end RBM.Gauss.T2041Inst
```
The commit only adds lines (0 deletions). All of them go into namespace `RBM.Gauss.T2041Inst` or the `#print axioms` block. So every pin statement audited in round 1 is unchanged byte for byte.

## 1. Statements (per target)
Round 1 compared every pin with the paper and the comparison still holds (§0): `STLmaxU`/`STLKU` against `(Eq:LGxb)`/`(Eq:L-KGt-flow)` (`1_2:1361,1371`), `STStep3R`/`STStep4R` with `∀ C_d ∃ 𝔠_d`, `STCaseI`/`STCaseII` against `3_5:1105`, `STIterR` against `lem:iterations` (`3_5:1407–1417`), `STbootRHS` against `(am;asoi222)`/`(am;asoiuw)`, `STContract` against `ygdhmsgq`, and the `STEK*` consumer forms against `lem:sum_Ndecay`/`lem:sum_decay`/`lem:sum_decay_nonzero`. Round 1 also tried the extreme input `1−s → g²/L^d`, `n = 50`, large `L`; nothing collapsed. Round 1 found one gap, in the hypothesis set (R3). It is a paper-delta coverage gap and is checked in §5.
The paper text that `T2041i` cites, re-checked:
```
$ sed -n 1313p 1_2_Intro_model_result.tex | cut -c1-200
The proof of \Cref{lem:main_ind} is divided into six steps, ... Throughout these steps, we assume the hypotheses of \Cref{lem:main_ind} hold. Moreover, each ste
$ for l in 1137 1365 1408 1562; do sed -n ${l}p 3_5_Loop_Hierarchy.tex | cut -c1-60; done
Under the assumptions of \Cref{lem:main_ind}, suppose $1-t\ge
Under the assumptions of \Cref{lem:main_ind}, suppose $1-t\ge
In the setting of \Cref{lem:main_ind}, suppose \eqref{lRB1}-
Under the assumptions of \Cref{lem:main_ind}, suppose $1-s\le
```
**Statements: PASS** for all targets.

## 2. Vacuity, hidden hypotheses, cycles
No change since round 1. `Sizes` has only the fields `L, W, lam, three_le_L, W_pos`. There are no cycles (Step 4 consumes `STLmaxU`; `STIterR` consumes `STXiBoot`). The probe imports only merged modules (`Induction.Defs`, `Evolution.SumDecay`, `Propagator.Prop6Hold`, `Loop.KLWard`). **PASS.**

## 3. Compiled nonempty instances
```
$ grep -c "^theorem inst_" RBM3D/Probe/T2041Pins.lean
33
$ sed -n 1802,1810p (R1)
theorem inst_STLmax_of_STLmaxU (h : STLmaxU sz0 (STflowE z0) sInst tInst) : STLmax sz0 (STflowE z0) tInst :=
  STLmax_of_STLmaxU sz0 (fun n => (sz0_hst n).le) h
theorem inst_STLK_of_STLKU (h : STLKU sz0 (STflowE z0) sInst tInst) : STLK sz0 (STflowE z0) tInst :=
  STLK_of_STLKU sz0 (fun n => (sz0_hst n).le) h
$ grep -n "theorem sz0_hst" RBM3D/Probe/T2041Pins.lean
1413:theorem sz0_hst : ∀ n, sInst n < tInst n := fun n => by simp only [sInst, tInst]; norm_num
```
- **R1 closed.** Both bridge theorems are applied at `(sz0, z0, s ≡ 0, t ≡ 1/16)` (`d = 3`, `L_n = 4(n+1)`). The only deterministic hypothesis, `hst`, is discharged. `STLmaxU`/`STLKU` remain as hypotheses; they are the conclusions of Step 3/Step 4, which other gates own.
- **R2 closed.** `inst_step3_skeletonII` applies `st_step3_skeleton` at `(szB, zB, s ≡ 15/16, t ≡ 31/32)` (`L = 4`, `W_n = n+4`, `g = 1`) with `A = STAII szB s = (W^{-3}B_{15/16,0})⁻¹`. The deterministic hypotheses are discharged as follows:
  - `hsize`: `tendsto_size szB szB_tendsto`;
  - `hA`: from `szB_AII_ge_one`;
  - `ht1`: `norm_num`;
  - `hscale`: `szB_scale_PsiII` (`k = 8`, `c = 1+2^{r−1}`);
  - `hBA`: `szB_scale_BII` (`c = 64`).
  Only `hIter` (the conclusion of `STIterationsII` at the data), `hbase` (the a priori level) and `hrela` (`(rela_XILXILK)`) remain as hypotheses; these are the stochastic ingredients. The data lie in case (ii) (`szB_caseII`, L1308) and are not degenerate:
```
$ python3 (exact fractions, L=4, g=1, d=3, s=15/16, t=31/32)
caseII 1-s<=g^2/L^2: True  1-t>=g^2/L^d: True  s<t<1: True
B_{s,0}: (1+1/16)^-1+(64/16)^-1 = 81/68      (matches the Lean lemma szB_AII_eq: STAII = 68/81 · W³ ≥ 1 for W ≥ 4)
```
  Case (ii) is taken at its boundary `1−s = g²/L²` with `1−t = 2·g²/L^d`, so the window `[s,t]` is nonempty and not collapsed.
- The 30 round-1 instances are unchanged (§0). **PASS.**

## 4. Build, axioms, hygiene, files
```
$ lake build RBM3D.Probe.T2041Pins > build2.out 2>&1; echo exit=$?; tail -2 build2.out
exit=0
info: RBM3D/Probe/T2041Pins.lean:2199:0: 'RBM.Gauss.T2041Inst.inst_step3_skeletonII' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3703 jobs).
$ grep -cE "T2041Pins.lean:[0-9]+:[0-9]+: (warning|error)" build2.out
0
$ grep "depends on axioms" build2.out | sed 's/.*depends on axioms: //' | sort | uniq -c; grep -c "does not depend on any axioms" build2.out
 173 [propext, Classical.choice, Quot.sound]
   2 [propext, Quot.sound]
4
$ grep -E "inst_STLmax_of_STLmaxU|inst_STLK_of_STLKU|szB_AII_ge_one'|szB_scale_PsiII|szB_scale_BII|inst_step3_skeletonII" build2.out | cut -d: -f2,5-
2192: [propext, Classical.choice, Quot.sound]   (inst_STLmax_of_STLmaxU)
2193: [propext, Classical.choice, Quot.sound]   (inst_STLK_of_STLKU)
2195: [propext, Classical.choice, Quot.sound]   (szB_AII_ge_one)
2197: [propext, Classical.choice, Quot.sound]   (szB_scale_PsiII)
2198: [propext, Classical.choice, Quot.sound]   (szB_scale_BII)
2199: [propext, Classical.choice, Quot.sound]   (inst_step3_skeletonII)
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom " RBM3D/Probe/T2041Pins.lean | wc -l
       0
$ git diff --name-only main...t/T2041
RBM3D/Probe/T2041Pins.lean
```
The two `[propext, Quot.sound]` lines are `STAlternating` and `ekE`; both axiom sets are subsets of the allowed three. The diff touches only the sole writable probe. The probe stays on its branch and is never imported, so no frozen signature changes. These figures match report b.1 (179 axiom lines: 173 + 2 + 4). **PASS.**

## 5. Paper deltas
`T2041a`–`T2041h` were checked in round 1. **R3 closed:** report (d) L273 adds `T2041i`. It states that `STStep3R`, `STStep4R`, `STIngR` and `STIterR` assume, out of the hypotheses of `lem:main_ind`, only (a) `STLK` at `s`. They drop `STDecay`, `STDecayStrong`, `STLocalMax` and `STExp2`, and add `STKbound` and `STKward`. The candidate cites `1_2:1313`, `3_5:1137,1365,1408,1562` (checked in §1) and the only uses of `(Eq:L-KGt+IND)`, at `3_5:1159,1681,1902`:
```
$ awk 'NR>=900&&NR<=1934&&/L-KGt\+IND/{print NR}' paper/tex/3_5_Loop_Hierarchy.tex | tr '\n' ' '
1159 1681 1902
```
Every Lean/paper statement difference found in either round has a candidate. **PASS.**

## Observations (not grounds for RETURN)
- O1 (carried over): `st_step3_skeleton` concludes only `k ≥ 2`. The `k = 1` case of `STLmaxU` follows from `STAvgU` and `STKbound`, and the proving ticket must close it.
- O2 (carried over, still present): the docstring of `STMollifierProps` (L515) tags the mollifier delta `T2041c`, but report (d) numbers it `T2041b`.
- O3: in `szB_scale_PsiII`, case (ii) takes `k = 8`, so `A^{1−k/8} = 1`. This is a valid deterministic scale fact at the data. It does not exercise the paper's choice `k > 2 + 8𝔠_d(n−1)`, which the S3 proving ticket must handle for general `n`.

## Per-target verdict
All targets (items 1–9: pins, EK-6 consumer forms, skeletons, instances, report-only items): **PASS**. No repair list; no dispatcher sign-off needed.
