Auditor model: claude-opus-5-5
# T2463 audit (round 1) — Mon Oct 12 18:09:54 UTC 2026
Branch `t/T2463` at 81ca99ae (base `main` e288560e); audit worktree `RBM3D-wt/T2463-audit1` (detached). Scratch files in the session scratchpad `T2463/`.
Verdict: **PASS** (targets 1–8, 10; target 9 moved to U1-BA under the ticket's own condition, see §5).

## 1. Build, axioms, hygiene, diff
```
$ lake build RBM3D.Chain.ZeroModeGen 2>&1 | grep -E "error|Build completed"; echo rc
Build completed successfully (3766 jobs).
rc=0
$ # ax.lean = import RBM3D.Chain.ZeroModeGen + `#print axioms RBM.BA.<n>` for every `^(theorem|def) ` of the file
$ lake env lean ax.lean | sed -E 's/^.*depends on axioms: //' | sort | uniq -c
  28 [propext, Classical.choice, Quot.sound]
$ printf 'import RBM3D\nimport RBM3D.Chain.ZeroModeGen\n#assert_rbm_axioms\n' > pre.lean; lake env lean pre.lean | grep "axiom audit"; echo exit=0
axiom audit: 13482 theorems, 4280 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" RBM3D/Chain/ZeroModeGen.lean | wc -l
       0
$ git diff --stat main...t/T2463
 RBM3D/Chain/ZeroModeGen.lean | 878 +++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 878 insertions(+)
$ git diff main...t/T2463 -- RBM3D/Induction RBM3D/Chain/Carrier.lean RBM3D/Chain/Step2Gen.lean RBM3D/Chain/Step2Kern.lean \
    RBM3D/Chain/GridDuhamelGen.lean RBM3D/Chain/Step5Gen.lean RBM3D/BA RBM3D/Test/Axioms.lean RBM3D.lean | wc -l
       0
$ lake env lean docs/tickets/checks/T2463-check.lean; echo exit   (on the branch; includes Part 3, the 58 band names)
exit=0   (0 error lines)
```
Only the sole writable file `RBM3D/Chain/ZeroModeGen.lean` is touched (878 lines < stop line 2,000; `ZeroModeGenB` unused). G1 (target 10) diff empty; `Test/Axioms.lean`, `RBM3D.lean` untouched (the hub adds the import at merge).

## 2. Statements against the pins (targets 1–6)
Scratch `pins.lean` = check file lines 1–32, `import RBM3D.Chain.ZeroModeGen`, check lines 33–363 (Parts 1–2), then the auditor's lines below, then check lines 364–440 (Part 3):
```
example {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) : T2463_KerSums C n ↔ ZeroModeGen_KerSums C n := Iff.rfl
example (d L : ℕ) [NeZero L] (κ : ℂ) (T : LoopIdx (Zd d L) → ℂ) : T2463_WardFam d L κ T ↔ ZeroModeGen_WardFam d L κ T := Iff.rfl
example {d : ℕ} (sz : Sizes d) (C : FlowFM sz) : T2463_WardCls sz C ↔ ZeroModeGen_WardCls sz C := Iff.rfl
example : T2463_KerSumsBand := @zeroModeGen_kerSums_band
example : T2463_ZeroModeSetUNg := @zeroModeSet_UNg
example : T2463_ZeroModeSetThetaNg := @zeroModeSet_ThetaNg
example : T2463_DuhamelInsideAtg := @zeroModeCalc_duhamel_inside_atg
example : T2463_LoopLWardFam := @zeroModeGen_loopL_wardFam
example (d : ℕ) : T2463_NewPQExpansion d := zeroModeGen_newPQ d
example : T2463_WardClsBand := @zeroModeGen_wardCls_band
example (d : ℕ) : T2463_LKExpansiongL d := zeroModeCalc_LK_expansiong d
example (d : ℕ) : T2463_LKExpansionEmptygL d := zeroModeCalc_LK_expansion_emptyg d
example : T2463_ColSumThetaKerg := @QopAlgebra_col_sum_thetaKerg
example : T2463_ColSumUKerg := @QopAlgebra_col_sum_uKerg
example : T2463_ThetaNSumZerog := @QopAlgebra_ThetaN_sumZerog
example : T2463_UNSumZerog := @QopAlgebra_UN_sumZerog
example : T2463_ThetaNSubg := @QopAlgebra_ThetaN_subg
example : T2463_UNSubg := @QopAlgebra_UN_subg
example : T2463_CommutatorThetaNg := @QopAlgebra_commutator_ThetaNg
example : T2463_CommutatorUNg := @QopAlgebra_commutator_UNg
```
```
$ lake env lean pins.lean > pins.out; echo exit=$?; grep -c error pins.out
exit=0
0
```
The three defined `Prop`s (targets 1, 4, 5) are definitionally the pins (`Iff.rfl`); the 17 theorem pins (20 pin names in all) are closed by the named theorems with no extra arguments, so hypotheses, quantifier order (`(ℓ,k,ξ,σ',ι,A')` before `L, κ, T` and before `sz, C`), the coefficients `(L^{-d}κ)^{m-k}` and `ξ/(2iNη)^{m-k}`, the index ranges (`1 ≤ k α`, `k α + 1 ≤ m`, `Fin (m+1)`) and the absence of windows are exactly the pinned ones. No special case: every generic target ranges over arbitrary `FlowFM sz` / `Step2Mat sz` / `LoopIdx` functions and every `d`.

## 3. Hidden hypotheses, vacuity, cycles
- Premises of the generic theorems, read from the signatures: `ZeroModeGen_KerSums` (targets 2, 3, 6 sum-zero), `Step2Gen_USemigroup` (target 3), `ZeroModeGen_WardFam`/`WardCls` (targets 4, 5), `IsUnit (1 - t•X)` + column sum `c` (target 6 values), `STPsum A = 0` (target 6), grid conditions `0 ≤ s ≤ t < 1`, `K ≠ 0`, `min j τ ≤ K`. These are exactly the ticket's inputs (a)–(e); no other `Prop` premise. No new `structure`; the only `def`s are the three `Prop`s and private instance data (§4 grep).
- Non-vacuity: `KerSums` is concluded unconditionally at `bandFM` (`zeroModeGen_kerSums_band`, sig `(sz) (E) (n)` only); `WardCls` at `bandFM` under `∀ n, |E n| < 2` (`zeroModeGen_wardCls_band`); `IsUnit` by `zeroModeGen_isUnit_band` (`|E n| ≤ 2`, `0 ≤ t < 1`); `Step2Gen_USemigroup` by merged `step2Gen_USemigroup_band`. All discharged in §4's instances.
- Dependencies: imports `GridDuhamelGen`, `ZeroModeCalc`, `QopAlgebra`, all on `main`; reverse cone of the new file is empty (no file imports it), so no cycle. `open private` reuses band privates (`npq_main`, `npq_ward_of_fam`, `npq_loopL_*`, `zmcSlot*`, `qa_*`) without editing their files.
- External hypotheses: none new (all premises are carrier/model facts with band discharges above); the BA discharges are U1-BA's, as the ticket says.

## 4. Compiled nonempty instances (section 8, `namespace ZeroModeGenInst`, lines 668–874; built in §1)
Data: `d = 3`, `sz0` at `n = 0` (`L = 4`, `W = 32`), `E ≡ 0`, `σ = (+,−,+)`, `τ = 1/2`.
| target | line | data / discharged hypotheses |
|---|---|---|
| 1 | 690 | `KerSums (bandFM sz0 0) 0` |
| 2 UN, ThetaN | 694, 703 | `A = I_diff σ` with `card = 2` (`decide`), tensor `δ₀ ≠ 0` (proved), `s,t = 9/10, 99/100`; `KerSums` |
| 3 | 713 | `bandStep2Mat sz0`, `s = 1/10`, `t = 1/2`, `K = 4`, `τ ≡ 3`, `j = 4` (3-term sums); `USemigroup` (`|0| ≤ 2`), `KerSums`, grid inequalities by `norm_num` |
| 4 loopL / newPQ | 737, 746 | `H_{1/2}(ω)` Hermitian (`gLoopFlow_seqHflow_isHermitian`), `Im z_{1/2} ≠ 0` (`etaT_pos`); `m = 3` |
| 5 class / expansions | 769, 774, 792 | `WardCls` (`|0| < 2`); `A = ∅` and `A = {2}`, `τ = 1/2 ∈ [0,1)` |
| 6 col sums | 812 | `(+,−)`, `s = 1/10`, `t = 1/2`; `IsUnit` by `zeroModeGen_isUnit_band` |
| 6 sum-zero | 837 | `A = 𝒬_{1/2} 1` (mollifier at `g = lam_0`), sum-zero by `QopAlgebra_Psum_Qop` |
| 6 sub, commutators | 846, 856, 865 | `δ₀`, `zmgA0`, label `0` |
Nondegeneracy of the sum-zero tensor (not proved in Lean; checked numerically from the merged definitions `qaU`, `qaZ1`, `qaPhi`, QA:48, 139, 339; `zdist` taken as the periodic distance):
```
$ python3 -I -c "...L,d,m,g,t=4,3,2,1/64,0.5; y=1+g/sqrt(1-t); u=1/y+1/L; z1=sum(exp(-u*min(x,L-x)) for x in range(L)) ..."
u=1.2284 z1=1.6712  (Q_{1/2} 1)(a=0) = 1 - L^(dm)/z1^(dm) = -186.9835
```
No `N = 0`, empty index set, collapsed window, `False` premise or large witness. Target 7 (a) band `example`s (lines 573–656: `Ind.zeroModeSet_Ugen`, `Ind.zeroModeCalc_duhamel_inside_at`, `zeroModeCalc_LK_expansion` and `_empty`, `QopAlgebra_ThetaN_sumZero`, `QopAlgebra_col_sum_thetaKer` at `mSigma (E n) ∘ σ`) compile in the module build.

## 5. Target 8 greps, target 9
```
$ grep -n "^import" F                                    -> 6 GridDuhamelGen, 7 ZeroModeCalc, 8 QopAlgebra   (d: no BA/*, CltGen, U-row file)
$ grep -nE "RBM\.UN|\bUN d|ThetaN d|uKer d|thetaKer d|Ugen|EKsgn|PropSpin|Theta d|SB d|cycProd|mSigma" F | cut -d: -f1
15 62 69 78 88 96 97 571 575 576 577 586 589 593 598 638 642 651 652 814 816 817
$ grep -nE "^(private |noncomputable |private noncomputable )*(def|abbrev|structure) " F | cut -c1-40
54 def ZeroModeGen_KerSums  226 def ZeroModeGen_WardFam  289 def ZeroModeGen_WardCls  673-681 private zmg* data  826,830 private abbrev zmgVartheta, zmgA0
$ grep -nE "Ring\.inverse|Matrix\.of|cycProd" F | cut -d: -f1   -> 22 103 105 108 110 121 435 444 456   (docstrings and rewrite lemmas; no def body)
$ grep -c "Step2Gen_UN" F ; grep -cE "^(def|theorem|abbrev) .*Ugen" F   -> 36 ; 0
$ grep -nE "mE|zt E|zt \(|2 - κ|\|E|etaT|cltCk|norm_mE|seqHflow|Lloop|STKloop|KLK|STFlow|lemT|‖m‖" F | cut -d: -f1
91 93 196 224 297 298 299 304 305 306 307 308 309 311 313 314 315 328 572 582 602 607 609 611 613 615 625 627 629 631 633 648 649 663 740 741 742 751 754 760 765 766 768
$ grep -nE "sz\.lam|lam0|BAflowLam0|withLam|gK|ellT|Bctl" F | cut -d: -f1
62 72 96 309 314 315 575 576 586 589 593 642 651 678 715 716 717 719 721 722 724 726 727 729 730 732 733
```
Labels (checked against the file): 15, 196, 224, 328, 572, 602, 648, 663 docstrings; 62–97 band bridges (`zeroModeGen_X/rowSum/colSum/kerSums/isUnit_band`); 297–315 `zeroModeGen_wardCls_band`; 571–656 target 7 (a) band examples; 668–874 instances (`zmgK` in 678–733 is the grid name, substring `gK`). No hit in a generic statement (targets 1–6 at lines 54–58, 115–184, 197–215, 226–280, 289–295, 329–376, 419–561). UBA-C1 / H252 (2) comparison: not used, none needed.
Target 9:
```
$ head -1 docs/queue/T2457.state; git ls-tree main --name-only RBM3D/Chain/ | grep -c Step34Gen
state: held
0
```
T2457 is unmerged, so by the ticket's condition target 9 moves to U1-BA (count-neutral); the file does not import `Step34Gen`. Not a defect. H251 (2): the Ward text `ZeroModeGen_WardFam` is the pinned `T2463_WardFam` (`Iff.rfl`, §2).
Name clash: `git grep -nwE "(<28 public names>)" main -- 'RBM3D/*.lean'` excluding the new file: `0`.

## 6. Paper deltas
Prove report (d) proposes T2463a (Θ as `Ring.inverse`: commutation and constant column sums for every `s, t`, explicit values under `IsUnit`; stronger than the paper's `‖tμ‖ < 1`) and T2463b (`lem: newPQ` model-free over `ZeroModeGen_WardFam` with coefficient `(L^{-d}κ)^{m-k}`, the model only through `ZeroModeGen_WardCls`). These cover the Lean/paper differences found: the abstract kernel premise `ZeroModeGen_KerSums` replacing `3 ≤ L`/symmetric Θ/`‖tμ‖ < 1` is the content of T2463a; target 3's generic `Step2Gen_USemigroup` premise is the T4s1 (T2453) carrier abstraction already merged. No uncovered difference.

## 7. Observations (no verdict effect)
- O1: the sum-zero instance tensor `𝒬_{1/2} 1` is nonzero only by the numeric check in §4, not by a Lean lemma; the linearity/commutator instances use `δ₀ ≠ 0`, proved.
- O2: public helpers beyond the pins (`zeroModeGen_X/rowSum/colSum/isUnit_band`, `zeroModeGen_projMat_comm_*`, `zeroModeOp_ThetaNg`) carry the file stem or the ticket's naming, §3 (E) satisfied.

## Verdict per target
| target | verdict |
|---|---|
| 1 `ZeroModeGen_KerSums`, `zeroModeGen_kerSums_band` | PASS |
| 2 `zeroModeSet_UNg`, `zeroModeSet_ThetaNg` | PASS |
| 3 `zeroModeCalc_duhamel_inside_atg` | PASS |
| 4 `ZeroModeGen_WardFam`, `zeroModeGen_loopL_wardFam`, `zeroModeGen_newPQ` | PASS |
| 5 `ZeroModeGen_WardCls`, `zeroModeGen_wardCls_band`, `zeroModeCalc_LK_expansiong`, `_emptyg` | PASS |
| 6 `QopAlgebra_*g` (8) | PASS |
| 7 band corollaries and instances | PASS |
| 8 greps | PASS |
| 9 `stNewPQgL_wardCls` | not due (T2457 held; moved to U1-BA by the ticket's condition) |
| 10 G1 | PASS |
Overall: **PASS**. No dispatcher sign-off needed.
