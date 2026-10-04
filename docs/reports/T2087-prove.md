Prover model: claude-sonnet-5-5
## (a) Math preflight — Sat Oct  3 23:19:40 UTC 2026

Notation: `A` = `STAI` (`A=ilambda²W^d`, case I) or `STAII` (`A=B_s⁻¹`, case II) (`Step34Pins.lean:76-91`); `ρ=η_s/η_u=(1-s)/(1-u)≥1`; `B_u=sz.Bctl n u`; `v=B_u⁻¹` (the factor of (5.118) `loopXi_le`, `Split.lean:640`); `Ψ=STPsi A ρ n k=A^{3/4}+ρ^{n-1}A^{1-k/8}` (paper `(adsyzz0s8d6)`, `3_5:1396`); `c=𝔠d≤1/100` (`STIterR`); `b=A^{1/8}`; `X=Ξ^{L-K}`, `Y=Ξ^{L}`. RBM2D = `Induction/Step3.lean` at `c9a24cf`.

### (i) Exponent table
**Cut (RBM2D `c9a24cf`, lines 1-777; `end Generic` is `:777`; `MatrixLevel` starts `:781` = S3-24b).** `Step3Target:96`; Real `:104-285` (`rpow_quarter:107 rpow_half_eq:112 rpow_three_quarter_eq:116 self_eq_rpow_quarter_pow:120 rpow_pred_eq:125 rpow_one_sub_le:133 scale_facts:145 ineq_5120:162 ineq_quad:221 ineq_quad_two:252 ineq_long:269`); PsiDefs `:289-344` (`Psi:294 psi:299 psi_of_ne_zero psi_zero Psi_nonneg psi_nonneg Psi_eq psi_pred_le:326 Psi_mono:339`); Abstract `:352-695` (`trans:359 one_add_inv_mul:378 Step3Scales:392 .kit:402 S:414 Lemma514:421 Hyp:432 rhs5119:449 xiL_5119:455 rhs5119_le:484 xiL_two_mul_add_two:498 xiLK_two_le:506 quad_of:522 S_of_S:540 S_all:633 Psi_succ_le:651 xiLK_le:665 xiL_le_one_of:679`); Generic `:699-777` (`rpow_mul_rpow_neg_add:706 of_forall_le_rpow_mul:712 mul_det:724 pullback:731 label_max:743`). All `private`.
**Finding F1 (the ticket's premise "exponents dimension-free" is false).** The RBM2D calculus is built on `step3_Psi As R=As^{1/2}+R^{n-1}As^{1-k/4}`, `R²As^{3/4}≤M_u≤As`, final `k=n+1`, and `Lemma514` (`X_n≺Λ^{1/2}+Φ`, `Y_{2n+2}≺Λ`). At `d≥3` (`3_5:1387-1417`, proof `3_5:1773-1830`, `(xiu2n+2psi)` `3_5:1785`): `Ψ=A^{3/4}+ρ^{n-1}A^{1-k/8}`, no `R²M^{3/4}≤M_u` row (replaced by `ρ≤aA^c`, `v≤c_vA`, `B_v≤c_BA^{-1+δ}`), depth `k_min=⌊2+8c(r-1)⌋+1` (merged `st_kmin`), and the `Lemma514` slot is the pin `STXiBoot` (`3_5:1366`, the term `B^{-1/(4p)}Y_{2n-1}^{1/2}Y_{4p}^{1/(4p)}`, with `Y_{2n-1}^{1/2}≤(Y_{2n-2}Y_{2n})^{1/4}`, `Y_{2n}≤vY_{2l1}Y_{2l2}`, `l1+l2=n`, from `loopXi_le` + `loopMax_odd_sq_le`). Section (4) of the script shows `step3_Psi` is not `STPsi` for any `As`, `k` (no coincidence: "use `STPsi`" means: use `STPsi` and do not port `step3_Psi`; `step3_psi`'s `k=0` branch is `STPsi` at `k=0`, `A^{3/4}+ρ^{n-1}A`, the a priori bound `(sef8w483r324)` `3_5:1391`). Section (5): the RBM2D `step3_ineq_*` are true as real inequalities, but their hypotheses/conclusions are in `b²,b³,b⁴` with `b=As^{1/4}`, so they do not apply to `STPsi`; they must be restated (below), not copied.
**Map RBM2D → merged.** `Step3Target:96` ↔ merged `STStep3R` (`Step34Pins.lean:250`; RBM2D vocabulary `KboundConcl, MainIndHyp, Step1LoopPT, ...` has no 3D counterpart, so no new `Step3Target`); `step3_Psi/psi` ↔ `STPsi`; `Step3Hyp.xiL_le` ↔ `Y≤1+B X` (`STXiL`,`STXiLK` normalizations `B^{k-1}`, `B^k`, `Step34Pins.lean:63-70`); `.xiL_split` ↔ `RBM.Ind.loopXi_le`; `.lemma514` ↔ `STXiBoot`; `Step3Scales` ↔ rows below; `step3_S_of_S/S_all` ↔ one step of `STIterR` + `st_iterate` (`ScaleFacts3.lean:106`); `step3_label_max/pullback` ↔ `st_prec_of_xi`, `st_prec_one_add_sup` (item 2).
**Rows (all with `A≥1`, `ρ≥1`; the `≺` absorbs constants, so equality of exponents is allowed).**
| quantity | value / constraint | slack at `c=1/100` |
|---|---|---|
| `ρ` | `ρ≤aA^c`, `a=2^c` (I), `a=1` (II) (`st_hscale_I/II` proofs) | n/a |
| `v=B_u⁻¹` | `v≤2A` (I: `x_u≤x_s≤g²`, = `st_BI_lower` at `(s,u)`, **private** in `ScaleFacts3`, re-prove); `v≤A` (II: `B_u≥B_s`, `STBctl_mono`) | n/a |
| `B_u` | **`B_u≤c_B A^{-1+δ}`**: I `δ=0,c_B=2` (inside `st_hBA_I` proof, not exposed); II `δ=c,c_B=1` (`scaleFacts_R2`) | n/a |
| merged `hBA` (`B_vA^{3/4}≤c_B`) | = `δ=1/4`: **insufficient**, see quad row and script (3) | quad ratio `∝A^{1/4}` |
| `Y_m` at level `l` | `Y_m≤1+c_BA^{-1+δ}Ψ(m,l)≤1+c_B+c_Bρ^{m-1}A^{δ-l/8}` (uses `δ≤1/4`); used at `l=k` (`m≤n-1`) and `l=k-1` (`m≤n+2`) | n/a |
| quad `Ψ(n+2-m,k)(Y_{n1'}Y_{n2'})^{1/2}≲Ψ(n,k)`, `3≤m≤n-1` | needs `ρ²A^{δ-k/8}≲1` at `k=1`: `2c+δ≤1/8` (`δ=0`: `c≤1/16`; `δ=c`: `c≤1/24`) | `0.105` (I), `0.095` (II) |
| chain term 1 `v^{1/(4p)}v^{1/2}ρ≲A^{3/4}` | `c+1/(4p)≤1/4` (`p≥2`; paper `p≥4`) | `0.1775` (`p=4`) |
| chain term 2 `ρ^{n+1}v^{1/(4p)+1/2}A^{δ+1/8-k/8}≲ρ^{n-1}A^{1-k/8}` | `2c+1/(4p)+δ≤3/8` | `0.2925` (I), `0.2825` (II) at `p=4` |
| `n=2,3` a priori `v^{1/(4p)}ρ^n≲A^{3/4}` (`Y_{2n-1}≺ρ^{2n-2}`, `Y_{4p}≺ρ^{4p-1}`, `3_5:1391`) | `nc+1/(4p)≤3/4` | `0.6575` (`n=3,p=4`) |
| long `max_{n'=n-1}^{n+1}Y_{n'}≲Ψ(n,k)` | `c+δ+1/8≤1` and `1≤A^{3/4}` | `0.865` (I) |
| mono `Ψ(m,k)≤Ψ(n,k)` (`m≤n`), `Ψ(n,k)≤Ψ(n,k-1)` | `ρ≥1`, `A≥1` | exact |
| depth `k_min` | `k>2+8c(r-1)` (T2058 `st_kmin`) | `(k-2-8c(r-1))/8∈(0,1/8]` |
| `d`-dependence | none in the table: `d` enters only through `A=ilambda²W^d`, `v` | n/a |
**Real inequalities to prove (d-dimensional replacements of `ineq_5120/quad/long`; `b=A^{1/8}`, `ρ²A^{δ}≤A^{1/8}·`const).** (5120′) `v^{1/(4p)+1/2}[∏_{i=1}^4(1+c_BA^{-1+δ}Ψ(2l_i,k-1))]^{1/4}ρ≤C Ψ(n,k)`, `l=(⌈n/2⌉,⌊n/2⌋,⌊n/2⌋,⌊(n-1)/2⌋)`; (quad′) as in the row; (long′) as in the row. No `v≤b⁴`, `R²b³≤v`, `e≤b³` hypotheses exist at `d≥3`.

### (ii) One concrete nondegenerate instance
Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2087/pre.py` (python only; ratios = LHS/`Ψ(n,k)` maxima over `n≤12`, `k≤12`, `p∈{4,5,8}`, no constants applied). Instance (6): `sz0`, `d=3,L=4,W=32,g=1/64`, `c=1/100`, `(s,t)` with `1-s=1.002e-4,1-t=1e-4` (case I) and `5.015e-6, 5e-6` (case II); all hypotheses of (i) are checked in the `hyps` list (`A≥1`, `ρ≤(2A)^c`, `con: B_t^c≤x_t/x_s<1`, regime, `B_t≤2/A` resp. `B_t≤A^{-(1-c)}`, `v` window). External hypotheses: none (`con`, the regime and `WO` are merged structural predicates; `A≥1` holds numerically at `A=8`, `4.596`). Section (1) is the ticket grid `b∈{1,2,10}`, `ρ∈{1,3}`, `v∈{A/2,2A}`; `ρ=3` is admissible only at `b=10` (`ρ²≤b`).
```
(1) 3D calculus, ticket grid b=A^(1/8) in {1,2,10}, rho in {1,3}; closure hyps rho^2<=b (2c<=1/8), B<=cB/A (delta=0,cB=2), v at ends A/2 and 2A
 b   rho   A         adm  v     chain(xiu2n+2psi) n=2,3 quad   long   mono
 1    1         1  yes A/2       1.730      0.489  5.000  2.500 1.000
 1    1         1  yes 2A        3.692      0.522  5.000  2.500 1.000
 1    3         1  no  (rho^2=9 > b=1: outside hypothesis)
 2    1       256  yes A/2       0.359      0.021  2.500  0.023 1.000
 2    1       256  yes 2A        0.783      0.023  2.500  0.023 1.000
 2    3       256  no  (rho^2=9 > b=2: outside hypothesis)
10    1     1e+08  yes A/2       0.022      0.000  1.220  0.000 1.000
10    1     1e+08  yes 2A        0.048      0.000  1.220  0.000 1.000
10    3     1e+08  yes A/2       0.066      0.000  1.020  0.000 1.000
10    3     1e+08  yes 2A        0.143      0.000  1.020  0.000 1.000
(2) actual scales c=1/100: rho=a*A^c, A in {8,1e4,1e16}; case I (a=2^c,cB=2,delta=0,v<=2A), case II (a=1,cB=1,delta=c,v<=A)
A=       8 rho_I= 1.028 case I: chain 2.20/0.25 quad 3.71 long 0.45 mono 0.998 | case II: chain 1.07/0.24 quad 2.38 long 0.33 mono 0.999
A=   1e+04 rho_I= 1.104 case I: chain 0.35/0.00 quad 1.76 long 0.00 mono 1.000 | case II: chain 0.22/0.00 quad 1.39 long 0.00 mono 1.000
A=   1e+16 rho_I= 1.455 case I: chain 0.00/0.00 quad 1.00 long 0.00 mono 1.000 | case II: chain 0.00/0.00 quad 1.00 long 0.00 mono 1.000
(3) weak merged hBA form B<=2A^(-3/4) (delta=1/4), rho=1, A=b^8: ratios grow with A
b=   10 chain 0.862 quad 23 long 1.85e-05
b= 1000 chain 0.0933 quad 2e+03 long 2e-15
(4) 2D shape step3_Psi(As,R,n,k)=As^(1/2)+R^(n-1)As^(1-k/4) vs 3D STPsi(A,r,n,k)=A^(3/4)+r^(n-1)A^(1-k/8), A=256, r=1.5, n=4
k=1: 3D 496.0000  2D(As=A) 232.0000  2D(As=A^(3/2)) 1792.0000
k=4: 3D 118.0000  2D(As=A) 19.3750  2D(As=A^(3/2)) 67.3750
(5) RBM2D step3_ineq_5120/quad/long as stated (b=As^(1/4), R2b3<=v<=b4, 0<=e<=b3): max LHS/RHS over n<=12, alpha+beta=2n, alpha,beta<=n+1, p_i at bound
b= 1 R=1: ratios 5120 1.000  quad 0.500  long 0.667  (all <=1 expected)
b= 1 R=3: hypotheses R^2 b^3<=v<=b^4 empty (R^2=9>b)
b= 2 R=1: ratios 5120 0.391  quad 0.375  long 0.125  (all <=1 expected)
b= 2 R=3: hypotheses R^2 b^3<=v<=b^4 empty (R^2=9>b)
b=10 R=1: ratios 5120 0.255  quad 0.275  long 0.004  (all <=1 expected)
b=10 R=3: ratios 5120 0.255  quad 0.086  long 0.003  (all <=1 expected)
(6) instance sz0 (d=3,L=4,W=32,g=1/64), c=1/100; B_u=W^-d[(g^2+x)^-1+(L^d x)^-1] (Bparam,K=0); chain/quad/long ratios with the ACTUAL B_u, rho, v=1/B_u
case I : A=8.000 rho=1.0020 B_t=0.0934 B_s=0.0934 1/B_t=10.70 hyps=True [True, True, True, True, True, True, True, True, True] chain 1.106 quad 2.020 long 0.291
case II: A=4.596 rho=1.0030 B_t=0.2179 B_s=0.2176 1/B_t=4.59 hyps=True [True, True, True, True, True, True, True] chain 1.184 quad 2.510 long 0.501
```
Reading: (1),(2),(6) all ratios are `≤5` (the maximum is `quad` at `b=1`, `A=1`) and do not grow with `A`; (3) the merged weak `hBA` form makes `quad` grow like `A^{1/4}` (23 at `b=10`, 2e+03 at `b=1000`); (4) the `d=2` and `d=3` `Ψ` differ for all `k` tried; (5) the RBM2D inequalities hold as stated (`b=1,R=1`: 5120 ratio `1.000` is the equality case) but their hypothesis `R²≤b` is already empty at `(b,R)=(2,3)`.

### Verdicts
- **Target 1 (port of RBM2D `Step3.lean:1-777`, `d`-dimensional): PASS with mandatory restatement.** The exponents close with the `d≥3` `Ψ` (table), slack `≥0.095` at `c=1/100`; the RBM2D real lemmas, `Step3Scales`, `Lemma514`, `step3_Psi` cannot be copied verbatim (F1) and the `Lemma514` slot is `STXiBoot`. Required corrections for stage 1b: (C1) hypotheses `B_u≤c_BA^{-1+δ}` (`δ≤1/8-2c`) and `v≤c_vA` are inputs of the new calculus, not the merged `hBA` (`δ=1/4`, insufficient: script (3)); (C2) `st_BI_lower` is `private` in `ScaleFacts3.lean:185`: re-prove inside `IterationsA.lean` (short algebra: `1-u≤1-s≤g²` gives `B_u≥W^{-d}/(2g²)=1/(2A)`); (C3) no new `Step3Target`: the `d`-dimensional form is the merged `STStep3R`; (C4) `step3_Psi` is not `STPsi`; paper-delta candidates: `T2087a` (ticket premise "`b³,b⁴,R²` dimension-free" false), `T2087b` (merged `hBA` too weak for the iteration; the sharper `B_v≤2/A` is local to its proof).
- **Target 2 (four `≺` helpers verbatim from `3c58211`): PASS.** Their statements (`Prec` transfer through a finite label sup; `STXiL, STXiLK ≥ 1` when `Bctl>0`) contain no exponent and no dimension.

## (b) Script output (generated Sun Oct  4 00:48:27 UTC 2026); `$SCR` = the session scratchpad directory `.../scratchpad/T2087`

### b.1 Commit, scope, builds, registry pre-check, axioms
```
$ git log --oneline -1; git diff --stat main...t/T2087
8e442ed T2087: S3-24a Induction/IterationsA (Psi-calculus, chain bound (xiu2n+2psi), lem:iterations step at d >= 3, probe helpers)
 RBM3D/Induction/IterationsA.lean | 2033 ++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean           |    2 +
 2 files changed, 2035 insertions(+)
$ lake build RBM3D.Induction.IterationsA 2>&1 | tail -1
Build completed successfully (3709 jobs).
$ lake build 2>&1 | tail -1   # whole library incl. root #assert_rbm_axioms (the root does not import the new module yet: the hub adds it at merge)
Build completed successfully (3829 jobs).
$ lake env lean $SCR/precheck.lean   # scratch file outside the repo: import RBM3D; import RBM3D.Induction.IterationsA; #assert_rbm_axioms
exit=0
axiom audit: 2893 theorems, 1123 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ lake env lean $SCR/precheck0.lean   # baseline, import RBM3D only
exit=0
axiom audit: 2853 theorems, 1121 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ lake env lean $SCR/axioms.lean   # #print axioms of the public declarations (names: $SCR/public_names.txt)
exit=0
-> 31 public declarations printed; 31 depend on exactly the 3 standard axioms (or none); other: []
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Induction/IterationsA.lean   # hits
0
```

### b.2 The cut, the declaration lists on both sides, name-clash grep, RBM2D diff-stat, verbatim copies
```
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks show c9a24cf:RBM2D/Induction/Step3.lean | sed -n 1,777p | grep -n "^end Generic\|^def Step3Target"  # the cut
96:def Step3Target (κ c τ : ℝ) (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
777:end Generic
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks show c9a24cf:RBM2D/Induction/Step3.lean | sed -n 1,777p | python3 $SCR/rbm2d_names.py  # RBM2D side (all private except Step3Target)
44 declarations:
Step3Target step3_rpow_quarter step3_rpow_half_eq step3_rpow_three_quarter_eq step3_self_eq_rpow_quarter_pow step3_rpow_pred_eq step3_rpow_one_sub_le step3_scale_facts
step3_ineq_5120 step3_ineq_quad step3_ineq_quad_two step3_ineq_long step3_Psi step3_psi step3_psi_of_ne_zero step3_psi_zero step3_Psi_nonneg step3_psi_nonneg step3_Psi_eq
step3_psi_pred_le step3_Psi_mono step3_trans step3_one_add_inv_mul Step3Scales Step3Scales.kit step3S step3Lemma514 Step3Hyp step3rhs5119 step3_xiL_5119 step3_rhs5119_le
step3_xiL_two_mul_add_two step3_xiLK_two_le step3_quad_of step3_S_of_S step3_S_all step3_Psi_succ_le step3_xiLK_le step3_xiL_le_one_of step3_rpow_mul_rpow_neg_add
step3_of_forall_le_rpow_mul step3_mul_det step3_pullback step3_label_max
$ sed "s/RBM.Gauss.Sizes.//; s/RBM.Ind.//" $SCR/public_names.txt | tr "\n" " " | fold -s -w 170  # this file, public declarations (namespace-tracked grep of theorem/structure lines)
st_prec_one_add_sup st_prec_of_xi st_one_le_XiL st_one_le_XiLK iterationsA_ineq_long iterationsA_ineq_quad iterationsA_ineq_chain iterationsA_STPsi_eq 
iterationsA_rpow_pred iterationsA_STPsi_pred iterationsA_STPsi_nonneg iterationsA_one_le_STPsi iterationsA_STPsi_mono_n iterationsA_STPsi_anti_k iterationsA_chain_term 
iterationsA_boot_bound iterationsA_STmaxL_eq iterationsA_STXiL_eq iterationsA_xiL_odd_le iterationsA_prec_mono_right iterationsA_prec_mono_left iterationsA_prec_absorb 
iterationsA_prec_rpow iterationsA_prec_one_add_mul IterationsAScale iterationsA_step iterationsA_avg_of_STAvgU iterationsA_apriori_of_lRB1 iterationsA_rela_of_K 
iterationsA_scale_I iterationsA_scale_II
$ echo; grep -c "^private \(theorem\|noncomputable def\|def\)" RBM3D/Induction/IterationsA.lean  # private declarations

46
$ bash $SCR/clash.sh  # name-clash grep: git grep -w -c NAME main -- RBM3D RBM3D.lean, number of matching files per new public name (0 = no clash)
st_prec_one_add_sup:0 st_prec_of_xi:0 st_one_le_XiL:0 st_one_le_XiLK:0 iterationsA_ineq_long:0 iterationsA_ineq_quad:0 iterationsA_ineq_chain:0 iterationsA_STPsi_eq:0 
iterationsA_rpow_pred:0 iterationsA_STPsi_pred:0 iterationsA_STPsi_nonneg:0 iterationsA_one_le_STPsi:0 iterationsA_STPsi_mono_n:0 iterationsA_STPsi_anti_k:0 
iterationsA_chain_term:0 iterationsA_boot_bound:0 iterationsA_STmaxL_eq:0 iterationsA_STXiL_eq:0 iterationsA_xiL_odd_le:0 iterationsA_prec_mono_right:0 
iterationsA_prec_mono_left:0 iterationsA_prec_absorb:0 iterationsA_prec_rpow:0 iterationsA_prec_one_add_mul:0 IterationsAScale:0 iterationsA_step:0 
iterationsA_avg_of_STAvgU:0 iterationsA_apriori_of_lRB1:0 iterationsA_rela_of_K:0 iterationsA_scale_I:0 iterationsA_scale_II:0
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks log -1 --format=%h; git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Induction/Step3.lean
9e0f275
 RBM2D/Induction/Step3.lean | 291 ++++++++++++---------------------------------
 1 file changed, 77 insertions(+), 214 deletions(-)
$ python3 $SCR/vdiff.py  # probe 3c58211:RBM3D/Probe/T2041Pins.lean (:840 :866 :1067-1068 :1077) vs this file, docstring included
st_prec_one_add_sup : probe 25 lines, IterationsA 25 lines, IDENTICAL
st_prec_of_xi : probe 20 lines, IterationsA 20 lines, IDENTICAL
st_one_le_XiL : probe 9 lines, IterationsA 9 lines, IDENTICAL
st_one_le_XiLK : probe 9 lines, IterationsA 9 lines, IDENTICAL
```

### b.3 Target statements (extracted from the file by script) and the structure `IterationsAScale`
```
$ python3 $SCR/stmts.py <names>   # theorem NAME ... up to `:=` (whitespace collapsed), with the line of the declaration in IterationsA.lean
[181] theorem iterationsA_ineq_long {b ρ e T cB K : ℝ} (hb : 1 ≤ b) (hρ : 1 ≤ ρ) (hK : 1 ≤ K) (hcB : 0 ≤ cB) (hT : 0 ≤ T) (he : 0 ≤ e) (hT1 : T * b ^ 6 ≤ cB) (hT2 : T * ρ ^ 2 *
    b ^ 7 ≤ cB * K) {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m) (hmN : m ≤ N + 1) : 1 + T * (b ^ 6 + ρ ^ (m - 1) * (b * e)) ≤ (1 + cB + cB * K) * (b ^ 6 + ρ ^ (N - 1) * e)
[214] theorem iterationsA_ineq_quad {b ρ e T cB K : ℝ} (hb : 1 ≤ b) (hρ : 1 ≤ ρ) (hK : 1 ≤ K) (hcB : 0 ≤ cB) (hT : 0 ≤ T) (he : 0 ≤ e) (he7 : e ≤ b ^ 7) (hT1 : T * b ^ 6 ≤ cB)
    (hT2 : T * ρ ^ 2 * b ^ 7 ≤ cB * K) {N m j : ℕ} (_hj : 1 ≤ j) (hm : 1 ≤ m) (hjN : j ≤ N) (hmN : m ≤ N) (hjm : j + m = N + 2) {xj xa xb : ℝ} (hxj : xj ≤ 1 + (b ^ 6 + ρ
    ^ (j - 1) * e)) (hxj0 : 0 ≤ xj) (hxa : xa ≤ 1 + T * (b ^ 6 + ρ ^ (m - 1) * e)) (hxb : xb ≤ 1 + T * (b ^ 6 + ρ ^ (m - 1) * e)) (hxb0 : 0 ≤ xb) : xj * (xa * xb) ^ (1 /
    2 : ℝ) ≤ (2 + 3 * cB + cB * K) * (b ^ 6 + ρ ^ (N - 1) * e)
[279] theorem iterationsA_ineq_chain {b ρ e T cB cv K w x y : ℝ} {N p : ℕ} (hb : 1 ≤ b) (hρ : 1 ≤ ρ) (hK : 1 ≤ K) (hcB : 0 ≤ cB) (hcv : 1 ≤ cv) (hT : 0 ≤ T) (he : 0 ≤ e) (hρK :
    ρ ^ 2 ≤ K * b) (hT2 : T * ρ ^ 2 * b ^ 7 ≤ cB * K) (hw1 : 1 ≤ w) (hwb : w ≤ b) (hN : 1 ≤ N) (hp : 1 ≤ p) (hx0 : 0 ≤ x) (hx : x ≤ 1 + cv * b ^ 8 * ((1 + cB) + T * ρ ^ N
    * (b * e)) ^ 2) (hy0 : 0 ≤ y) (hy : y ≤ (2 * ρ) ^ (4 * p)) : cv * w * (x ^ (1 / 2 : ℝ) * y ^ (1 / (4 * (p : ℝ)))) ≤ (2 * cv * K + 2 * cv ^ 2 * (1 + cB) * K + 2 * cv ^
    2 * cB * K) * (b ^ 6 + ρ ^ (N - 1) * e)
[542] theorem iterationsA_chain_term (cB cv K : ℝ) (hcB : 0 ≤ cB) (hcv : 1 ≤ cv) (hK : 1 ≤ K) (N k : ℕ) (hN : 2 ≤ N) (hk : 1 ≤ k) : ∃ C : ℝ, 0 < C ∧ ∀ (A ρ T Bu x y : ℝ) (p :
    ℕ), 2 ≤ p → 1 ≤ A → 1 ≤ ρ → ρ ^ 2 ≤ K * A ^ (1 / 8 : ℝ) → 0 ≤ T → T * ρ ^ 2 * A ^ (7 / 8 : ℝ) ≤ cB * K → (cv * A)⁻¹ ≤ Bu → 1 ≤ x → x ≤ 1 + cv * A * ((1 + cB) + T * ρ
    ^ N * A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8)) ^ 2 → 1 ≤ y → y ≤ 1 + ρ ^ (4 * p - 1) → Bu ^ (-(1 : ℝ) / (4 * (p : ℝ))) * x ^ (1 / 2 : ℝ) * y ^ (1 / (4 * (p : ℝ))) ≤ C * STPsi
    A ρ N k
[630] theorem iterationsA_boot_bound (cB cv K : ℝ) (hcB : 0 ≤ cB) (hcv : 1 ≤ cv) (hK : 1 ≤ K) (N k : ℕ) (hN : 2 ≤ N) (hk : 1 ≤ k) : ∃ C : ℝ, 0 < C ∧ ∀ (A ρ T Bu : ℝ) (p : ℕ)
    (XL XLK : ℕ → ℝ), 2 ≤ p → 1 ≤ A → 1 ≤ ρ → ρ ^ 2 ≤ K * A ^ (1 / 8 : ℝ) → 0 ≤ T → T * A ^ (3 / 4 : ℝ) ≤ cB → T * ρ ^ 2 * A ^ (7 / 8 : ℝ) ≤ cB * K → (cv * A)⁻¹ ≤ Bu → (∀
    m, 1 ≤ m → m ≤ N + 1 → XL m ≤ 1 + T * STPsi A ρ m (k - 1)) → (∀ m, 1 ≤ m → m + 1 ≤ N → XL m ≤ 1 + T * STPsi A ρ m k) → (∀ m, 1 ≤ XL m) → XL (2 * N - 1) ≤ 1 + cv * A *
    ((1 + cB) + T * ρ ^ N * A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8)) ^ 2 → XL (4 * p) ≤ 1 + ρ ^ (4 * p - 1) → (∀ m, 1 ≤ XLK m) → (∀ m, 1 ≤ m → m + 1 ≤ N → XLK m ≤ 1 + STPsi A ρ m
    k) → STbootRHS 1 XL XLK Bu N p ≤ C * STPsi A ρ N k
[473] theorem iterationsA_STPsi_eq {A : ℝ} (hA : 0 ≤ A) (ρ : ℝ) (m k : ℕ) : STPsi A ρ m k = (A ^ (1 / 8 : ℝ)) ^ 6 + ρ ^ (m - 1) * A ^ (1 - (k : ℝ) / 8)
[490] theorem iterationsA_STPsi_pred {A : ℝ} (hA : 0 < A) (ρ : ℝ) (m : ℕ) {k : ℕ} (hk : 1 ≤ k) : STPsi A ρ m (k - 1) = (A ^ (1 / 8 : ℝ)) ^ 6 + ρ ^ (m - 1) * (A ^ (1 / 8 : ℝ) *
    A ^ (1 - (k : ℝ) / 8))
[494] theorem iterationsA_STPsi_nonneg {A ρ : ℝ} (hA : 0 ≤ A) (hρ : 0 ≤ ρ) (m k : ℕ) : 0 ≤ STPsi A ρ m k
[497] theorem iterationsA_one_le_STPsi {A ρ : ℝ} (hA : 1 ≤ A) (hρ : 0 ≤ ρ) (m k : ℕ) : 1 ≤ STPsi A ρ m k
[504] theorem iterationsA_STPsi_mono_n {A ρ : ℝ} (hA : 0 ≤ A) (hρ : 1 ≤ ρ) {m n : ℕ} (hmn : m ≤ n) (k : ℕ) : STPsi A ρ m k ≤ STPsi A ρ n k
[510] theorem iterationsA_STPsi_anti_k {A ρ : ℝ} (hA : 1 ≤ A) (hρ : 0 ≤ ρ) (m : ℕ) {k : ℕ} (hk : 1 ≤ k) : STPsi A ρ m k ≤ STPsi A ρ m (k - 1)
[481] theorem iterationsA_rpow_pred {A : ℝ} (hA : 0 < A) {k : ℕ} (hk : 1 ≤ k) : A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8) = A ^ (1 / 8 : ℝ) * A ^ (1 - (k : ℝ) / 8)
[729] theorem iterationsA_STXiL_eq (n : ℕ) (E v : ℝ) (m : ℕ) (ω : sz.SeqΩ) : STXiL sz n E v m ω = 1 + RBM.Ind.loopXi d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (seqHflow
    sz n v ω)) (zt E v) (sz.Bctl n v)⁻¹ m
[740] theorem iterationsA_xiL_odd_le (n : ℕ) {E v : ℝ} (ω : sz.SeqΩ) (hB : 0 < sz.Bctl n v) {N : ℕ} (hN : 3 ≤ N) : STXiL sz n E v (2 * N - 1) ω ≤ 1 + (sz.Bctl n v)⁻¹ * ((STXiL
    sz n E v (2 * ((N + 1) / 2)) ω * STXiL sz n E v (2 * (N / 2)) ω) * (STXiL sz n E v (2 * (N / 2)) ω * STXiL sz n E v (2 * ((N - 1) / 2)) ω)) ^ (1 / 2 : ℝ)
[1283] theorem iterationsA_step (hsize : Tendsto sz.size atTop atTop) {E s t A T : ℕ → ℝ} {cB cv K : ℝ} (hS : IterationsAScale sz E s t A T cB cv K) (hboot : STXiBoot sz E s t)
    (hrela : ∀ m, 1 ≤ m → sz.Prec (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q ω => 1 + sz.Bctl n q.1.1 * STXiLK sz n (E n) q.1.1 m ω)) (havg :
    sz.Prec (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 1 ω) (fun _ _ _ => 1)) (hapri : ∀ m, 1 ≤ m → sz.Prec (U := STPair s t) (fun n q ω => STXiL sz n (E n)
    q.1.1 m ω) (fun n q _ => (etaT (E n) (s n) / etaT (E n) q.1.2) ^ (m - 1))) {N k : ℕ} (hN : 2 ≤ N) (hk : 1 ≤ k) (IH1 : ∀ r, 2 ≤ r → r + 1 ≤ N → STIterHyp sz E s t A r
    k) (IH2 : ∀ r, 2 ≤ r → r ≤ N + 2 → STIterHyp sz E s t A r (k - 1)) : STIterHyp sz E s t A N k
[1631] theorem iterationsA_scale_I (hd : 2 ≤ d) {E s t : ℕ → ℝ} {𝔠d 𝔡 : ℝ} (h𝔠d : 0 < 𝔠d) (hc : 𝔠d ≤ 1 / 16) (hreg : STRegIterI sz s t) (hcon : sz.STConStInd 𝔠d s t) (hWO :
    sz.WO 𝔡) (ht1 : ∀ n, t n < 1) (hE : ∀ n, |E n| < 2) : IterationsAScale sz E s t (fun n => sz.STAI n) (fun n => 2 * (sz.STAI n)⁻¹) 2 2 2
[1704] theorem iterationsA_scale_II {E s t : ℕ → ℝ} {𝔠d : ℝ} (h𝔠d : 0 < 𝔠d) (hc : 𝔠d ≤ 1 / 24) (hcon : sz.STConStInd 𝔠d s t) (ht1 : ∀ n, t n < 1) (hE : ∀ n, |E n| < 2) :
    IterationsAScale sz E s t (fun n => sz.STAII s n) (fun n => (sz.STAII s n) ^ (-1 + 𝔠d)) 1 1 1
[1359] theorem iterationsA_avg_of_STAvgU (hsize : Tendsto sz.size atTop atTop) {E s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1) (h : STAvgU sz E s t) : sz.Prec (U := STPair s t) (fun n q ω
    => STXiLK sz n (E n) q.1.1 1 ω) (fun _ _ _ => 1)
[1385] theorem iterationsA_apriori_of_lRB1 (hsize : Tendsto sz.size atTop atTop) {E s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1) (hE : ∀ n, |E n| < 2) (h : STStep1Loop sz E s t) (m : ℕ)
    (hm : 1 ≤ m) : sz.Prec (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q _ => (etaT (E n) (s n) / etaT (E n) q.1.2) ^ (m - 1))
[1454] theorem iterationsA_rela_of_K (hsize : Tendsto sz.size atTop atTop) {E s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1) (m : ℕ) (hm : 1 ≤ m) (hK : sz.Prec (U := fun n => STPair s t n ×
    ((Fin m → Bool) × (Fin m → Zd d (sz.L n)))) (fun n p _ => ‖STKloop sz n (E n) p.1.1.1 p.2.1 p.2.2‖) (fun n p _ => sz.Bctl n p.1.1.1 ^ (m - 1))) : sz.Prec (U := STPair
    s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q ω => 1 + sz.Bctl n q.1.1 * STXiLK sz n (E n) q.1.1 m ω)
$ sed -n "/^structure IterationsAScale/,/^$/p"
structure IterationsAScale (sz : Sizes d) (E s t A T : ℕ → ℝ) (cB cv K : ℝ) : Prop where
  cB_nonneg : 0 ≤ cB
  one_le_cv : 1 ≤ cv
  one_le_K : 1 ≤ K
  A_nonneg : ∀ n, 0 ≤ A n
  T_nonneg : ∀ n, 0 ≤ T n
  t_lt_one : ∀ n, t n < 1
  one_le_A : ∀ᶠ n in atTop, 1 ≤ A n
  rho : ∀ᶠ n in atTop, ∀ q : STPair s t n, 1 ≤ etaT (E n) (s n) / etaT (E n) q.1.2 ∧
    (etaT (E n) (s n) / etaT (E n) q.1.2) ^ 2 ≤ K * A n ^ (1 / 8 : ℝ) ∧
    T n * (etaT (E n) (s n) / etaT (E n) q.1.2) ^ 2 * A n ^ (7 / 8 : ℝ) ≤ cB * K
  TA : ∀ᶠ n in atTop, T n * A n ^ (3 / 4 : ℝ) ≤ cB
  Bctl : ∀ᶠ n in atTop, ∀ w : TimeIcc s t n, (cv * A n)⁻¹ ≤ sz.Bctl n (w : ℝ) ∧ sz.Bctl n (w : ℝ) ≤ T n

```

### b.4 Compiled nonempty instances: `python3 $SCR/inst.py` (target: lines of its `example`s in the file; section 9 of the file, `szB`: `d = 3`, `L = 4`, `W_n = n + 4`, `ilambda = 1`, flow `zB`)
```
31 examples; target -> example lines:
st_prec_one_add_sup: [1892, 1898]; st_prec_of_xi: [1898]; st_one_le_XiL: [1888]; st_one_le_XiLK: [1889]; iterationsA_ineq_long: [1800]; iterationsA_ineq_quad: [1807];
iterationsA_ineq_chain: [1815]; iterationsA_STPsi_eq: [1864]; iterationsA_rpow_pred: [1871]; iterationsA_STPsi_pred: [1867]; iterationsA_STPsi_nonneg: [1874];
iterationsA_one_le_STPsi: [1875]; iterationsA_STPsi_mono_n: [1876]; iterationsA_STPsi_anti_k: [1878]; iterationsA_chain_term: [1846]; iterationsA_boot_bound: [1825];
iterationsA_STmaxL_eq: [1905]; iterationsA_STXiL_eq: [1909]; iterationsA_xiL_odd_le: [1914]; iterationsA_prec_mono_right: [2012]; iterationsA_prec_mono_left: [2016];
iterationsA_prec_absorb: [2021]; iterationsA_prec_rpow: [2029]; iterationsA_prec_one_add_mul: [2025]; IterationsAScale: [1933, 1945, 1939, 1949]; iterationsA_step: [1954,
1971]; iterationsA_avg_of_STAvgU: [1990]; iterationsA_apriori_of_lRB1: [1996]; iterationsA_rela_of_K: [2003]; iterationsA_scale_I: [1933, 1945]; iterationsA_scale_II:
[1939, 1949]
```

### b.5 Narrative (facts from b.1-b.4, `RBM3D/Induction/IterationsA.lean` and (a)):
1. Delivered: `RBM3D/Induction/IterationsA.lean` (2033 lines: 31 public declarations, 46 private, 31 `example`s) and two registry lines in `RBM3D/Test/Axioms.lean`
   (`owedProps`: `STXiBoot`, `STAvgU`, the premises `iterationsA_step`, `iterationsA_avg_of_STAvgU` take); the scan found no other unregistered premise (b.1: exit 0).
2. Finding F1 of (a) stands: the ticket's "`b³, b⁴, R²` are dimension-free" is false.  RBM2D's `step3_Psi`, `Step3Scales`, `Lemma514` and the `step3_ineq_*` are the `d = 2`
   calculus (`As^{1/2}`, `As^{1-k/4}`, `R² As^{3/4} ≤ M_u`); `step3_Psi` is not `STPsi`.  They are not copied; the `d ≥ 3` calculus of the paper (`3_5:1387-1417`, `3_5:1772-1864`)
   is proved instead, with `STXiBoot` (`(am;asoi222)`) in the slot of `Lemma514`.  The cut line, the declaration lists and the RBM2D → this-file map are in b.2 and in the module docstring.
3. Class b, the `d`-dimensional exponents: `Ψ = A^{3/4} + ρ^{n-1} A^{1-k/8}` (`STPsi`; RBM2D `As^{1/2} + R^{n-1} As^{1-k/4}`); `b = A^{1/8}` (RBM2D `As^{1/4}`), so `A^{3/4} = b⁶`,
   `A^{7/8} = b⁷`, `A = b⁸`; RBM2D's row `R² b³ ≤ v ≤ b⁴` becomes `(cv A)⁻¹ ≤ B_v ≤ T`, `T A^{3/4} ≤ cB`, `T ρ² A^{7/8} ≤ cB K`, `ρ² ≤ K A^{1/8}` (`IterationsAScale`);
   `Y_{2n+2}` (5.119/5.120) becomes the odd chain `Ξ̂_{2N-1} ≤ 1 + B⁻¹ ((Ξ̂_{2l₁}Ξ̂_{2l₂})(Ξ̂_{2l₃}Ξ̂_{2l₄}))^{1/2}` (`iterationsA_xiL_odd_le`, from `loopXi_le` (5.118) and `loopMax_odd_sq_le` (6.4)).
4. Case (i) (`A = ilambda² W^d`): `T = 2A⁻¹`, `cB = cv = K = 2`, needs `2 ≤ d` (`L^d ≥ L²`) and `𝔠d ≤ 1/16`; case (ii) (`A = (W^{-d}B_{s,0})⁻¹`): `T = A^{-1+𝔠d}`, `cB = cv = K = 1`, `𝔠d ≤ 1/24`
   (`B_v ≤ B_s^{1-𝔠d}` only: a loss `A^{𝔠d}` in `(rela_XILXILK)`; the paper omits case (ii), `3_5:1594`).  `STIterR` has `𝔠d ≤ 1/100`, so both hold.
5. `iterationsA_step` (the step of `lem:iterations`) takes: `IterationsAScale` (proved by `iterationsA_scale_I/II`), `STXiBoot`, `hrela`, `havg`, `hapri` and the induction hypotheses
   in the form of `STIterR`.  `havg`, `hapri` follow from the merged pins `STAvgU`, `STStep1Loop` (`iterationsA_avg_of_STAvgU`, `iterationsA_apriori_of_lRB1`); `hrela` from the `𝒦`-loop
   bound uniform in `(v,u)` and the labels (`iterationsA_rela_of_K`; `STKbound` itself is per time sequence, portmap F-H).  The step holds for every `d` (the scale theorems carry the dimension).
6. Proof route (differences from (a), no statement change): `p = N + 4` (so `4p > N+1`, `4p ≠ 2N-1`); the a priori bound is used only at `m = 4p`; `N = 2` needs no chain (`Ξ̂_3` is among the
   controls `m ≤ N+1`), `N ≥ 3` uses the chain (the paper uses the a priori bound for `N ∈ {2,3}`, `3_5:1818`).  The constants of `iterationsA_boot_bound` depend on `(cB, cv, K, N, k)` only.
7. DECISIONS §29 (the four checks), for every statement with a time window or `∀ᶠ n`: (1) no statement has `0 ≤ s` as a hypothesis or uses it (neither the fields of `IterationsAScale` nor the hypotheses of `iterationsA_scale_I/II`, b.3, contain it; the time
   hypotheses are `t < 1`); proofs use `u < 1` only, so times `< 0` are allowed; instances: `s = 7/8, 15/16`, `t < 1`.  (2) the boundary
   `1 - ilambda²/L²` enters only as the pinned `STCaseI` (`ilambda²/L² ≤ 1 - t`, case (i)); case (ii) does not use `STCaseII`; instance `ilambda = 1 < L = 4`.  (3) `L^d ≤ W^K` is not used;
   the constants `cB, cv, K ∈ {1, 2}` contain no `W`, `L`, `ilambda`.  (4) `A ≥ 0`, `T ≥ 0`, `t < 1` are `∀ n` (proved for every `n`, in both cases, by `iterationsA_scale_I/II`), all other fields `∀ᶠ n` (b.3).
8. Instances (b.4): every deterministic hypothesis of every public theorem is discharged at concrete nondegenerate data: real data `A = 256` (`b = 2`), `ρ = 3/2`, `T = 1/256`, `N = 3`, `k = 2`, `p = 7`; model data
   `szB` (`d = 3`).  `iterationsA_step` at `(N,k) = (3,2)` (case (i), chain branch) and `(2,1)` (case (ii)); `STXiBoot`, `hrela`, `havg`, `hapri`, `IH1`, `IH2` stay hypotheses (other gates' pins).

## (c) Verified Mathlib names (one line each for the non-obvious ones)
```
$ lake env lean $SCR/chk_names.lean   # #check @NAME of the 39 Mathlib/core names used by the file (those not defined in RBM3D); exit 0, no error
Real.rpow_le_rpow_of_nonpos : ∀ {x y z : ℝ}, 0 < x → x ≤ y → z ≤ 0 → y ^ z ≤ x ^ z
Real.rpow_lt_rpow_iff : ∀ {x y z : ℝ}, 0 ≤ x → 0 ≤ y → 0 < z → (x ^ z < y ^ z ↔ x < y)
Real.pow_rpow_inv_natCast : ∀ {x : ℝ} {n : ℕ}, 0 ≤ x → n ≠ 0 → (x ^ n) ^ (↑n)⁻¹ = x
Real.rpow_le_self_of_one_le : ∀ {x y : ℝ}, 1 ≤ x → y ≤ 1 → x ^ y ≤ x
Real.sqrt_le_iff : ∀ {x y : ℝ}, √x ≤ y ↔ 0 ≤ y ∧ x ≤ y ^ 2
Real.sqrt_eq_rpow : ∀ (x : ℝ), √x = x ^ (1 / 2)
Finset.sup'_univ_eq_ciSup : ∀ {ι : Type u_1} {α : Type u_2} [inst : ConditionallyCompleteLattice α] [inst_1 : Fintype ι] [inst_2 : Nonempty ι] (f : ι → α), Finset.univ.
Finset.sum_le_card_nsmul : ∀ {ι : Type u_1} {N : Type u_2} [inst : AddCommMonoid N] [inst_1 : Preorder N] [AddLeftMono N] (s : Finset ι) (f : ι → N) (n : N), (∀ x ∈ s,
Finset.sup'_le : ∀ {α : Type u_1} {β : Type u_2} [inst : SemilatticeSup α] {s : Finset β} (H : s.Nonempty) (f : β → α) {a : α}, (∀ b ∈ s, f b ≤ a) → s.sup' H
inv_le_of_inv_le₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] [MulPosReflectLT G₀] {a b : G₀}, 0 < a → a⁻¹ ≤ b
Nat.card_Icc : ∀ (a b : ℕ), (Finset.Icc a b).card = b + 1 - a
ite_eq_left : ∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u_1} {t e : α}, (if c then t else e) = t
ite_eq_right : ∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u_1} {t e : α}, (if c then t else e) = e
also resolved in the same run: Real.inv_rpow, Real.mul_rpow, Real.one_le_rpow, Real.rpow_add, Real.rpow_le_one_of_one_le_of_nonpos, Real.rpow_le_rpow,
Real.rpow_le_rpow_of_exponent_le, Real.rpow_mul, Real.rpow_natCast, Real.rpow_neg, Real.rpow_neg_one, Real.rpow_nonneg, Real.rpow_one, Real.rpow_pos_of_pos, Real.sq_sqrt,
Finset.le_sup', Finset.exists_mem_eq_sup', Nat.cast_sub, one_le_inv₀, inv_anti₀, div_le_div_of_nonneg_left, pow_le_pow_right₀, pow_le_pow_left₀, one_le_pow₀, le_div_iff₀,
div_le_iff₀
```
`if_pos`, `if_neg`, `if_false` are deprecated in this toolchain (build warning "Use `ite_eq_left` / `ite_eq_right` / `ite_false`"): the file uses `ite_eq_left`, `ite_eq_right`.  Names verified absent: none needed.

## (d) Open issues and paper-delta candidates
- `T2087a` (premise, not a paper statement): the ticket's "`b³, b⁴, R²` dimension-free" and RBM2D `Induction/Step3.lean:1-777` are `d = 2`; the `d ≥ 3` `Ψ` is `A^{3/4} + ρ^{n-1} A^{1-k/8}` (`3_5:1396`), `b = A^{1/8}` (module docstring of the file).
- `T2087b`: the merged `hBA` (T2058, `B_v A^{3/4} ≤ c`, i.e. `δ = 1/4`) is too weak for the step (script (3) of (a)); the step needs `B_v ≤ cB A^{-1+δ}` with `ρ² A^δ ≤ K A^{1/8}` (fields `rho`, `TA`, `Bctl` of `IterationsAScale`; case (i) `δ = 0`, case (ii) `δ = 𝔠d`).
- `T2087c`: case (ii) uses `(rela_XILXILK)` with the loss `T = A^{-1+𝔠d}` (`B_v ≤ B_s^{1-𝔠d}`), absorbed because `𝔠d ≤ 1/24`; the paper omits case (ii) (`3_5:1594`).
- Open for S3-24b (`STIterations`, `STIterationsII`): (1) `iterationsA_rela_of_K` needs `STKbound` uniform in `(v,u)` and the labels (portmap F-H: the maximizing-time lemma, not proved here); (2) `STXiBoot` (S3-18b, S3-22) stays a hypothesis;
  (3) the assembly `STIterR`: `𝔠d := 1/100`, `hsize` from `Admissible`, `t < 1` from `t ≤ lemT z` and `lemT_lt_one`, `|E| < 2` from `abs_lemE_lt_two`, then `iterationsA_scale_I/II`, `iterationsA_step`.
- RBM2D declarations of lines 1-777 without counterpart (reasons in the module docstring): `step3_ineq_quad_two`, `step3_xiLK_two_le`, `step3_xiL_5119`, `step3_rhs5119_le`, `step3_xiL_two_mul_add_two` (the `Y_{2n+2}` chain of the `d = 2` proof), `step3_scale_facts`, `Step3Scales.kit`;
  `Step3Target` is the merged `STStep3R`; `step3_S_all` is the merged `st_iterate`; `step3_Psi_succ_le`, `step3_xiLK_le`, `step3_xiL_le_one_of` are covered by `st_hscale_I/II` and the skeleton of S3-25.
- Public API beyond the ticket's list, for S3-24b: `IterationsAScale`, `iterationsA_scale_I/II`, `iterationsA_step`, `iterationsA_{avg_of_STAvgU,apriori_of_lRB1,rela_of_K}`, `iterationsA_chain_term`, `iterationsA_boot_bound`, `iterationsA_STXiL_eq`, `iterationsA_xiL_odd_le`, `iterationsA_STPsi_*`;
  the RBM2D helpers made public (ports of `step3_trans`, `step3_one_add_inv_mul`, `Psi_*`): `iterationsA_prec_{mono_right,mono_left,absorb,rpow,one_add_mul}` and the `iterationsA_STPsi_*` lemmas.

