Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 10:43:37 UTC 2026

Sources: ticket T2049; probe `3c58211:RBM3D/Probe/T2041Pins.lean` (2199 lines; `P`); `docs/reports/T2041-prove.md`; `docs/DECISIONS.md` §16, §20, §25; main `9233ea3`. Scratch scripts: `scratchpad/T2049/*.py|*.sh` (Python/shell; no Lean file written).

### (i) Exponent table (data: `sz0` = `L=4(n+1), W=(2(n+1))^5, ilambda=(2(n+1))^-6`; `szB` = `L=4, W=n+4, ilambda=1`; `d=3`, `κ=ε=𝔡=1/10`, `𝔠=1/6`)

| item | value | constraint | slack |
|---|---|---|---|
| `d` | 3 | pins `3 ≤ d`; `Bparam` has `(K+1)^{d-2}` | 0 (boundary value; pins are uniform in `d`) |
| `𝔠` (bandwidth) | 1/6 | `N^𝔠 ≤ W`, `N=(WL)^d` | `sz0` n=0: 11.31 ≤ 32; `szB` n=0: 4 ≤ 4 (slack 0, `n=5`: 6 ≤ 9; the pin is eventual) |
| `𝔡` (`eq:WO`) | 1/10 | `W^{-d/2+𝔡} ≤ ilambda ≤ 𝔡⁻¹ = 10` | `sz0` n=0: 7.8e-3 ≤ 1.56e-2 ≤ 10; `szB`: `W^-1.4 ≤ 1 ≤ 10` |
| `κ, ε` / `locDomain` | 1/10, 1/10 | `\|Re z\| ≤ 2-κ`, `N^{-1+ε} ≤ Im z ≤ 1` | `sz0` n=0: 2.0e-6 ≤ 8.8e-6 ≤ 1; `szB` (`z=1/2+i/64`): 5.6e-4 ≤ 1/64 |
| time window | `(s,t)=(0,1/16)` / `(15/16,31/32)` / `(7/8,15/16)` | `0 ≤ s < t ≤ lemT(z)` | `lemT(z0_0)=0.999991` vs 1/16; `lemT(zB)=0.983992` vs 0.96875 (0.015) |
| `𝔠_d` (pin: `∀C_d ∃𝔠_d ≤ 1/100`, T2041e) | arbitrary `>0` (pin's witness) | `(con_st_ind)`: `Bctl(t)^{𝔠_d} ≤ (1-t)/(1-s) < 1`, eventually | `sz0` (ratio 15/16): holds from n=0 at `𝔠_d=1/100` (0.9020 ≤ 0.9375). `szB` (ratio 1/2, `Bctl ≤ 1.47 W^-3`): threshold `n ≥ 8` at `𝔠_d=0.1`, `n ≥ 1.2e10` at `𝔠_d=1/100`; the hypothesis is `∀ᶠ n`, discharged by `Bctl → 0` for every `𝔠_d > 0`, not by one threshold (see Notes 4) |
| loss `C_d` of `STGdecayW` | any `>0` (instance: 1) | base `(1-s)/(1-u) ≥ 1` for `s ≤ u < 1` | `u=t=31/32, s=15/16`: base 2, loss `2^{C_d}` |
| case (i) `STCaseI` | `1-t ≥ ilambda²/L²` | | `sz0` n=0: 1.5e-5 ≤ 0.9375; `szB` `(7/8,15/16)`: 1/16 ≤ 1/16 (slack 0) |
| `STRegIterI` | `1-s ≤ ilambda²` and case (i) | | `1/8 ≤ 1`; second part slack 0 |
| case (ii) `STCaseII` | `1-s ≤ ilambda²/L²` | | `szB` `(15/16,31/32)`: 1/16 ≤ 1/16 (slack 0); intermediate regime `ilambda²/L³=1/64 ≤ 1-t=1/32` (×2) |
| `STLmaxU`/`STLKU`/`STKward` powers | `B^{k-1}` (`k≥1`), `B^k` (`k≥1`), `B^{k-2}` (`k≥2`) | natural-number subtraction nonnegative | exact on the stated ranges; `B=Bctl>0` for `u<1` (`st_Bctl_pos`) |
| `STGdecayW` powers | `B^{1/5}`, `exp(-(r/ℓ)^{1/2})`, `W^{-D}` | `D>0` | n/a (exponents are constants of the paper `Eq:Gdecay_w`) |
| `STbootRHS` / `STXiBoot` | `B^{-1/(4p)}`, `XL^{1/2}`, `XL^{1/(4p)}`; lengths `m ≤ n_+1`, `2n_-1`, `4p`; `XLK` `m ≤ n_-1`; `lo ∈ {1,2}` | every index the right side uses must be controlled by the hypotheses (else the pin is false for free `XL`) | script below: 0 uncovered indices for `n_<40, p≤5, lo∈{1,2}` |
| `STSEforLnConcl` indices | `(n₁,n₂)=(k-1,k+1)\|(k,k)`, `(n'₁,n'₂)`, `k+2-n'`, `k-l+2`, `2k-1`, `4q` | all Ξ-indices `≥ 1` | script below: 0 violations, `k<40` |
| `STContract` | powers `1/2`, `1/(2p)`; `1≤k≤m-1`; second part `4≤m`, `1≤k<j<l≤m-1`, `p≥1`, `\|𝒜(x)\|≤C` | | T2041 b.8 (`T2041-prove.md`): max ratio 0.938 ≤ 1 over four regimes of `1-u` (n=3); instance data below |
| `Ψ` of `STIterR` | `A^{3/4} + r^{n-1} A^{1-k/8}`; `A=ilambda²W^d` (i), `A=(W^{-d}B_{s,0})⁻¹` (ii) | `A ≥ 1` | `szB` W=7, (ii): `A=287.95=68/81·W³`, `A^{3/4}=69.9` |
| `STQopNorm` | `4 ≤ W^ε`, `L^d ≤ W^K`, `K=2` | | `L=3,g=1,W=25,ε=1/2,D=2`: `W^ε=5`, `27 ≤ 625` |
| `STMollifierProps` | `C, c`: sum 1; `‖ϑ‖ ≤ C(ℓ^d)^{-m}e^{-c Σ\|a_i-a_0\|/ℓ}`; `‖∂_tϑ‖ ≤ C(1-t)^{-1}(ℓ^d)^{-m}` | satisfiable at `d=3` with `t`-differentiable `ϑ` | `d=3,L=7,g=1,m=1,c=1/2`: needed `C ≥ 2.09` (sup), `0.21` (derivative); `C=2.5` works; sum 1 to 1e-12 |

**Pins (P.2 of `T2041-portmap.md`): says / hypothesis of / class (§25; "owed"=proved by a later ticket).**

| pin | says | hypothesis of | class |
|---|---|---|---|
| `STLmaxU`, `STLKU` | `(Eq:LGxb)`, `(Eq:L-KGt-flow)`, uniform in `u∈[s,t]` | `STLmaxU`: `STStep4R`, `STLmax_of_STLmaxU`; `STLKU`: `STLK_of_STLKU` | owed; **`STLKU` is not in the ticket's list** (Notes 1) |
| `STStep2Concl` (`STLocalEntryU`, `STAvgU`, `STGdecayW`) | `Gt_bound_flow`, `Gt_avgbound_flow`, `Eq:Gdecay_w` | `STStep3R/4R`, `STIngR`, `STIterR` | owed (ST-2, T2039) |
| `STKward` | `lem_wardineq_K` at scale `N` | `STStep3R/4R`, `STIngR` | owed (KL12) |
| `STCaseI/II`, `STAny`, `STRegIterI` | regime predicates | argument `R` of `STStep3R/4R/STIngR/STIterR` | structural |
| `STStep3R/4R` and `STStep3/3I/3II/4/4I/4II` | Steps 3, 4 per regime | the `inst_step*` instances | owed (assembly S3-27); **not in the ticket's list** |
| `STIngR`, `STIterR` | generic setting of an ingredient / of `lem:iterations` | `inst_ing`, `inst_iter` | owed; **not in the ticket's list** |
| `STContract`, `STNewPQ` | `(yi2oslxj2)`, `(u2jzooi-2)`; `lem: newPQ` | `inst_contract`, `inst_newPQ` | owed (new at `d ≥ 3`) |
| `STSEforLn`, `STOeqNQ/Qt/QtNZ`, `STXiBoot`, `STIterHyp`, `STIterations(II)` | `lem:SEforLn`, `lem:STOeq_*`, `(am;asoi222)`, `(eq:iteration_induc)`, `lem:iterations` | `inst_*`; `STXiBoot`, `STIterHyp` in `STIterR` | owed |
| `STMollifierProps` | mollifier properties | `STQopNorm`, `STWardTypeP`, `STB45` | structural |
| `STMollifierEx`, `STQopNorm`, `STWardTypePPin`, `STB45Pin` | `rmk:choosechi`, `lem_+Q`, `(eq:Ward_typeP)`, `(y27kasdfg)` | `inst_mollifier`, `inst_qopNorm`, `inst_WardTypeP`, `inst_B45` | owed |
| `STEKDecay/Low/Win` | data conditions of the kernel forms | `STEKSumRes*` | structural |
| `STEKSumNdecay/Res1/Res2NAL/Res2/Nonzero` | EK-6 consumer forms | no theorem in the copy-set | owed |
| `STAlternating` | `σ_k ≠ σ_{k+1}` for all `k` | `STWardTypeP`, `STB45` | structural |

### (ii) One concrete nondegenerate instance (all hypotheses of the deterministic targets at once)
```
$ python3 scratchpad/T2049/inst_check.py | grep -E "n=0|lemT\(zB\)|case|iterations|cd=|qopNorm|contract|ALL|FAIL"   (abridged: n=3, n=20, szB n=5,100 also OK in the full run)
OK   n=0 L>=3 L=4 W=32 N=2097152 lam=1.562e-02
OK   n=0 Bandwidth N^c<=W N^c=11.31 <= W=32
OK   n=0 WO W^(-3/2+dd)<=lam<=1/dd 7.813e-03<=1.562e-02<=10
OK   n=0 locDomain 2.044e-06<=8.764e-06<=1
OK   n=0 0<=s<t<=lemT(z) lemT=0.999991
OK   n=0 case(i) lam^2/L^2<=1-t 1.526e-05<=0.9375
OK   n=0 con_st_ind at cd=1/100: Bctl^cd<=(1-t)/(1-s)<1 Bctl=3.305e-05 Bctl^0.01=0.9020 <= 0.9375
OK   lemT(zB)>=31/32 lemT=0.983992
OK   n=0 Bandwidth N^c<=W N^c=4 <= W=4        (szB)
OK   case(ii) (s,t)=(15/16,31/32) case(ii) 1-s<=lam^2/L^2 1-s=0.0625 lam^2/L^2=0.0625
     intermediate regime lam^2/L^3 <= 1-t: True 0.015625 0.03125
OK   case(ii) (s,t)=(15/16,31/32) (1-t)/(1-s)<1 ratio=0.5
     cd=0.1: con_st_ind needs W>=11.46 (W=n+4, so n>=8); holds eventually (Bctl~W^-3->0)
     cd=0.01: con_st_ind needs W>=1.23e+10 (W=n+4, so n>=12304834824); holds eventually (Bctl~W^-3->0)
OK   iterations (s,t)=(7/8,15/16) 1-s<=lam^2 and 1-t>=lam^2/L^2 1-s=0.125<=1; 1-t=0.0625>=0.0625
OK   contract: |E|<2, 0<=tau<1, m=3,k=1: 1<=k,k+1<=m
OK   contract part 2: m=4,k=1,j.val+1=2,l=3,p=1,C=1,|A(x)|=1<=C
OK   qopNorm: L>=3,0<g<=Lambda=1,W>1,0<eps<1,D>1,4<=W^eps,L^3<=W^K (K=2) W^eps=5.0 L^3=27 W^2=625.0
ALL OK
$ python3 scratchpad/T2049/idx_check.py | head -2
STbootRHS: indices of XL not covered by STlenL / XLK not <= n_-1 (n_<40,p<=5,lo in {1,2}): [] 0
lem:SEforLn index ranges (k<40) with a Xi-index < 1: [] 0
$ python3 scratchpad/T2049/moll_check.py | tail -1
constants: sup bound C>= 2.0921  derivative bound C>= 0.2096  (c=0.5, d=3, L=7, g=1, m=1)
```
Concrete data, bridges: `s ≡ 0 < t ≡ 1/16` (`hst : ∀ n, s n ≤ t n` holds), `d=3`, flows `z0`/`zB`. Stochastic premises (`STKbound`, `STKward`, `STLK`, `STStep1Loop`, `STStep2Concl`, `STXiBoot`, `STLmaxU`, `STLKU`) stay hypotheses of the instances (CLAUDE.md §4 step 2). Every hypothesis of the form `Prop`-valued pin is an owed pin (class table above); no external hypothesis (no limit computation owed beyond `Bctl → 0` above).

Script (ii-b), copy-set against `P`:
```
$ bash scratchpad/T2049/dep_check.sh
sections 5-6 declarations: 12; used inside lines 45-683: 0
lines 1164-1553 use these section 5-6 names:
  st_Bctl_pos
copy-set line counts: 45-683 = 639; st_Bctl_pos 928-938 = 11; 1164-1553 = 390
forbidden tokens in copy-set: 0
T2041[a-z] tags in 45-683 (absolute line):
  line 419: T2041a`
  line 515: T2041c`
```
The O2 correction is exactly line 515 (`STMollifierProps` docstring, `T2041c` → `T2041b`; `T2041b` = mollifier pinned by properties, §25). Stage 1b acceptance check: `diff <(git --no-optional-locks show 3c58211:RBM3D/Probe/T2041Pins.lean | sed -n 45,683p) <(sed -n '<block lines>' RBM3D/Induction/Step34Pins.lean)` must print exactly the one line-515 hunk.

**Notes (mathematics only).**
1. Registry: a scan over the copy-set (theorem binders naming a `Prop`-valued def; script `scan.py`) reports `STB45Pin STContract STIngR STIterR STIterations STIterationsII STLKU STLmaxU STMollifierEx STNewPQ STOeqNQ STOeqQt STOeqQtNZ STQopNorm STSEforLn STStep3 STStep3I STStep3II STStep3R STStep4 STStep4I STStep4II STStep4R STWardTypePPin`. Not in the ticket's lists: `STLKU`, `STIngR`, `STIterR`, `STStep3R/4R`, `STStep3/3I/3II/4/4I/4II`; proposal: owed (conclusions of Steps 3–4 and their generic forms; §20 "unsure: owed and say so"); the dispatcher signs. `STCaseI/II`, `STRegIterI` are proved by `sz0_caseI`, `szB_caseII`, `szB_regIterI` (conclusion heads), so the scan will not report them; registering them is harmless (§16: unused registered names only log). The remaining listed names carry no binder in the copy-set (info line only).
2. Item 2: `st_Bctl_pos` (probe 928–938, self-contained) is needed by `Bctl_tendsto_const` in the instance block, so it is copied; `st_prec_of_xi`, `st_prec_one_add_sup` (probe 840, 866) are used only by sections 5–6, not by lines 45–683 or 1164–1553, so they are not copied.
3. Item 3 (HierVocab, `c9a24cf`, 664 lines, 444 kept; RBM2D `HEAD` is `9e0f275`, file changed 77+/315-): probe section 1 already contains the content of `Psum, Qop, LLf, LKf, ksimLK, elklkN, egtN, eeLoop, eeN, lkTensor` (as `STPsum, STQop, STLI, STKI, STksimLK, STelklk, STegt, STeeLoop, STee, STLKtensor`), `Alternating` (`STAlternating`), and replaces `QopNorm, BcalEPT, B45PT, STOeqTargetV2` by pins (`STQopNorm, STSEforLn, STB45Pin, STOeq*`). Skip, with reasons: `vartheta, varthetaDot, thetaSig` (the `Θ`-based mollifier violates the sup bound at `d ≥ 3`: `T2041-prove.md` F-B, b.8: `(1-t)Θ_t(0,0)ℓ_t^d` grows 0.73 → 28.4); `QopAlgebra, QopDecay*` (S3-04, S3-05); `HierarchyN, KcalDecay, DecayLoop*, B5, B4, AvecN, martIncN, predIncN, StoppedDuhamelN, GridDriftN, StoppedAzumaN, loopDerivN, QVPropagatedN, PPTargetV2, MainIndPinV2, MLExpPin, llPairN, LoopGenN` (ST-2 grid / `PP*` basis, `d=2` content; F-A, F-D: T2039 and later tickets).
4. `(con_st_ind)` at `szB` is a `∀ᶠ n` statement; its threshold in `n` depends on the pin's `𝔠_d` (table). At `sz0, (0,1/16)` it holds from `n=0` for `𝔠_d = 1/100`. If the prover wants a case-(ii) datum with a small threshold at `𝔠_d=1/100`, `ilambda = 10 = 𝔡⁻¹` (still `eq:WO`) makes `1-s ≤ ilambda²/L² = 6.25` automatic for `s ∈ [0,1)` and allows ratio `(1-t)/(1-s)` near 1; this is optional (the probe's `szB` compiles).
5. The copy-set omits the probe's header lines 38–44 (`set_option linter.style.longLine false`, `noncomputable section`, `open …`) and `end RBM.Gauss.Sizes` (probe line 1162); the new file needs them around the block.

### Verdict per target
1. Probe sections 1–4 (lines 45–683) verbatim, O2 tag: **PASS** (self-contained: no use of sections 5–6; no forbidden token; satisfiable data above).
2. Bridges `STLmax_of_STLmaxU`, `STLK_of_STLKU` (inside 45–683) **PASS**; `st_Bctl_pos` added (Notes 2).
3. HierVocab port: **PASS with skip list** (Notes 3): section 1 contains every declaration with a `d ≥ 3` meaning; the rest is `d=2`-specific or ST-2.
4. Instances (probe 1164–1553 with `szB`): **PASS** (data above; `STMollifierEx`, `STQopNorm`, `STContract`, `STNewPQ`, regime pins stay hypotheses of their instances).
5. Registry: **PASS**, with the 11 additional names of Notes 1 to register (owed) so the full build does not fail.

## (b) Script output — Sat Oct  3 10:48:49 UTC 2026

Branch `t/T2049`, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2049`, commit `0d33ee7`; `Step34Pins.lean` has     1083 lines.

```
$ lake build RBM3D.Induction.Step34Pins 2>&1 | tail -1;  lake build RBM3D.Test.Axioms 2>&1 | tail -1
Build completed successfully (3703 jobs).
Build completed successfully (2 jobs).
$ lake build 2>&1 | tail -1   (full library; the new module is not yet imported by RBM3D.lean, the hub adds it at merge)
Build completed successfully (3745 jobs).
$ git diff main...t/T2049 --stat
 RBM3D/Induction/Step34Pins.lean | 1083 +++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean          |   26 +-
 2 files changed, 1108 insertions(+), 1 deletion(-)
$ grep -c "sorry\|admit\|native_decide\|^axiom " RBM3D/Induction/Step34Pins.lean
0
```

Copy checks against the probe (script diff; probe lines 45-683 = file lines 38-676; `st_Bctl_pos` probe 928-938 = file 678-688; instances probe 1164-1553 = file 692-1081):
```
$ diff <(git show 3c58211:RBM3D/Probe/T2041Pins.lean | sed -n 45,683p) <(sed -n 38,676p RBM3D/Induction/Step34Pins.lean)
471c471
< `T2041c`).  The RBM2D choice `ϑ = (1-t)^{m} Π Θ_t(a₁,a_i)` (`HierVocab.lean:66`) violates the first bound at `d ≥ 3`:
---
> `T2041b`).  The RBM2D choice `ϑ = (1-t)^{m} Π Θ_t(a₁,a_i)` (`HierVocab.lean:66`) violates the first bound at `d ≥ 3`:
$ diff <(probe 928-938) <(file 678-688)
exit=0
$ diff <(probe 1164-1553) <(file 692-1081)
13c13
< namespace RBM.Gauss.T2041Inst
---
> namespace RBM.Gauss.Step34Inst
```

Registry pre-check (DECISIONS §20): scratch file `scratchpad/T2049/precheck.lean` = `import RBM3D` + `import RBM3D.Induction.Step34Pins` + `#assert_rbm_axioms`, run in the worktree.
```
$ lake env lean scratchpad/T2049/precheck.lean ; echo exit=$?   (before the registry lines the same file reported 24 unclassified premises, listed in (d))
(after the 24 owed lines were appended to Axioms.lean:)
exit=0
0
axiom audit: 1563 theorems, 628 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
```

Axioms (script `scratchpad/T2049/axioms.lean`: `#print axioms` of all 127 declarations of the file):
```
$ lake env lean scratchpad/T2049/axioms.lean | grep -c "depends on axioms"; ... "does not depend"
123
4
$ grep "depends on axioms" axioms.out | grep -v "\[propext, Classical.choice, Quot.sound\]"
'RBM.Gauss.Sizes.STAlternating' depends on axioms: [propext, Quot.sound]
(targets and instance theorems:)
'RBM.Gauss.Sizes.STLmaxU' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.STLKU' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.STStep2Concl' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.STStep3R' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.STStep4R' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.STLmax_of_STLmaxU' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.STLK_of_STLKU' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step34Inst.inst_ing' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step34Inst.inst_iter' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step34Inst.inst_step3R' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step34Inst.inst_step4R' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step34Inst.inst_step3' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step34Inst.inst_step4II' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step34Inst.inst_contract' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step34Inst.inst_newPQ' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step34Inst.inst_mollifier' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step34Inst.inst_qopNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Name clash (new public names against all declarations of `main`, last name component, `scratchpad/T2049/clash.py`):
```
new public names: 127 ; declarations scanned on main: 2563 ; clashes: []
```

Target statements (extracted by `scratchpad/T2049/ext.py`):
```lean
-- STLmaxU (lines 176-180)
def STLmaxU (E s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (k - 1))
-- STLKU (lines 184-188)
def STLKU (E s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω - STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
      (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ k)
-- STStep2Concl (lines 221-222)
def STStep2Concl (E s t : ℕ → ℝ) (Cd : ℝ) : Prop :=
  STLocalEntryU sz E s t ∧ STAvgU sz E s t ∧ STGdecayW sz E s t Cd
-- STStep3R (lines 250-257)
def STStep3R (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) →
          R sz s t → STKbound sz (STflowE z) → STKward sz (STflowE z) →
          STLK sz (STflowE z) s → STConStInd sz 𝔠d s t → STStep1Loop sz (STflowE z) s t →
          STStep2Concl sz (STflowE z) s t Cd → STLmaxU sz (STflowE z) s t
-- STStep4R (lines 261-269)
def STStep4R (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) →
          R sz s t → STKbound sz (STflowE z) → STKward sz (STflowE z) →
          STLK sz (STflowE z) s → STConStInd sz 𝔠d s t → STStep1Loop sz (STflowE z) s t →
          STStep2Concl sz (STflowE z) s t Cd → STLmaxU sz (STflowE z) s t →
          STLKU sz (STflowE z) s t
```

Compiled nonempty instances, in the same file (`RBM.Gauss.Step34Inst`): the targets `STStep3R`/`STStep4R` are applied at `(sz0, z0, s ≡ 0, t ≡ 1/16)` and `(szB, zB, 15/16, 31/32)` with every deterministic hypothesis (`STFlow`, `0 ≤ s < t ≤ lemT`, the regime predicate, `STConStInd` for every `𝔠d > 0`) discharged; the stochastic pins (`STKbound`, `STKward`, `STLK`, `STStep1Loop`, `STStep2Concl`, `STXiBoot`, `STLmaxU`) and the owed pins `h` stay hypotheses (`d = 3`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`).
```lean
-- inst_step3R (lines 916-924)
theorem inst_step3R (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (h : STStep3R 3 R)
    (sz : Sizes 3) (z : ℕ → ℂ) (hflow : STFlow sz (1 / 10) (1 / 10) (1 / 6) (1 / 10) z)
    (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht : ∀ n, t n ≤ lemT (z n))
    (hR : R sz s t) (hcon : ∀ 𝔠d : ℝ, 0 < 𝔠d → STConStInd sz 𝔠d s t) (Cd : ℝ) (hCd : 0 < Cd) :
    InstStep3Concl sz z s t Cd := by
  obtain ⟨𝔠d, h0, h1, H⟩ := h (by norm_num) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num) Cd hCd
  exact ⟨𝔠d, h0, h1, fun hK hKw ha h1' h2 =>
    H (1 / 6) sz z hflow s t hs0 hst ht hR hK hKw ha (hcon 𝔠d h0) h1' h2⟩
-- inst_step3 (lines 948-950)
theorem inst_step3 (h : STStep3 3) (Cd : ℝ) (hCd : 0 < Cd) :
    InstStep3Concl sz0 z0 sInst tInst Cd :=
  inst_step3R STAny h sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst sz0_ht trivial sz0_con Cd hCd
-- inst_step4II (lines 972-976)
theorem inst_step4II (h : STStep4II 3) (Cd : ℝ) (hCd : 0 < Cd) :
    InstStep4Concl szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) Cd :=
  inst_step4R STCaseII h szB zB flow_zB (fun _ => 15 / 16) (fun _ => 31 / 32) (fun _ => by norm_num)
    (fun _ => by norm_num) (szB_flow_ht (by norm_num)) szB_caseII
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠) Cd hCd
```
Further compiled instances of the deterministic pins: `inst_ing, inst_iter, inst_step3I/3II/4/4I, inst_SEforLn, inst_OeqNQ/Qt/QtNZ, inst_WardTypeP, inst_B45, inst_iterations(II), inst_contract, inst_newPQ, inst_mollifier, inst_qopNorm`, the data `szB, zB, flow_zB, lemT_zB, szB_admissible, conStInd_const, szB_caseI/II, szB_regIterI, sz0_caseI` and the EK-6 data of the probe lines 1409-1553 only (no `ekδ`/`inst_ekNdecay` block: probe lines 1554+ are not copied).

Ports (CLAUDE.md §5.2): RBM2D `Induction/HierVocab.lean` at `c9a24cf` (RBM2D `HEAD` is `9e0f275`, from `git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks log -1 --format=%h`): per section (a) Notes 3, the content of `Psum, Qop, LLf, LKf, ksimLK, elklkN, egtN, eeLoop, eeN, lkTensor, Alternating` is already in the probe's section 1 (`STPsum, STQop, STLI, STKI, STksimLK, STelklk, STegt, STeeLoop, STee, STLKtensor, STAlternating`), so no further text was ported.
```
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Induction/HierVocab.lean
 RBM2D/Induction/HierVocab.lean | 392 ++++++++---------------------------------
 1 file changed, 77 insertions(+), 315 deletions(-)
```

Narrative.
* The new file is the probe's header (imports of the probe plus `RBM3D.Evolution.Pins`, a new module docstring), sections 1-4 verbatim (probe 45-683), `st_Bctl_pos` (probe 928-938; needed by `Bctl_tendsto_const`), `end RBM.Gauss.Sizes`, then the instances (probe 1164-1553) in `RBM.Gauss.Step34Inst` (renamed from `T2041Inst`).
* No statement of a copied declaration changed; the probe's base (`64bdfd3`) compiled unchanged against `main` `9233ea3`.
* Not copied: probe sections 5-6 (EK-6, S3-25/S3-26), the probe's EK-6 consumer instances (lines 1554+), `st_prec_of_xi`, `st_prec_one_add_sup` (item 2: used only by sections 5-6, not by the copy-set; section (a) Notes 2).
* HierVocab port: no extra declaration (section (a) Notes 3).
* The file-line 508 docstring tag is `T2041b`; `T2041a` (line 412) is unchanged.
* The registry pre-check initially reported 24 premises (listed in (d)); all 24 were appended to `owedProps`.

## (c) Verified Mathlib names
None new: the file uses only names already verified in the probe; it builds against Mathlib `v4.34.0` (build tail in (b)).

## (d) Open issues and paper-delta candidates
* Registry: the 24 premises reported by the pre-check, all appended to `owedProps` (comment on each line): `STLmaxU STLKU STStep3R STStep4R STStep3 STStep3I STStep3II STStep4 STStep4I STStep4II STIngR STIterR STContract STNewPQ STSEforLn STOeqNQ STOeqQt STOeqQtNZ STIterations STIterationsII STMollifierEx STQopNorm STWardTypePPin STB45Pin`. Not in the ticket's list and registered as owed on section (a) Notes 1 (the dispatcher signs): `STLKU STStep3R STStep4R STStep3 STStep3I STStep3II STStep4 STStep4I STStep4II STIngR STIterR`.
* Not registered (the pre-check did not report them: no theorem takes them as a hypothesis in this file): `STKward STStep2Concl STLocalEntryU STAvgU STGdecayW STXiBoot STIterHyp STEK*` (owed in §25) and `STMollifierProps STCaseI STCaseII STAny STRegIterI STEKDecay STEKLow STEKWin STAlternating` (structural in §25). The ticket asks only for the reported ones; the ticket that first uses each as a hypothesis registers it (DECISIONS §20).
* `STIterationsII`, `STContract`: see DECISIONS §25 (risk).
* Paper-delta candidates: none new; T2041a-i are cited as signed in DECISIONS §25. The one text change is the O2 docstring tag (`T2041c` to `T2041b`), no statement change.

## Repair — Sat Oct  3 10:54:11 UTC 2026 (audit round 1, D1; repairer claude-opus-5-5)
D1 (no compiled instance of the bridges): two `example`s added in `RBM.Gauss.Step34Inst`, after `inst_step4II`; `hst` is discharged by `sz0_hst`, the owed `STLmaxU`/`STLKU` stay premises. No other line changed.
```
$ git log --oneline -1 ; git diff --stat HEAD~1 HEAD
6d9ce32 T2049: repair D1, compiled instances of STLmax_of_STLmaxU and STLK_of_STLKU at (sz0, z0, 0, 1/16)
 RBM3D/Induction/Step34Pins.lean | 8 ++++++++
 1 file changed, 8 insertions(+)
$ sed -n '979,980p;983,984p' RBM3D/Induction/Step34Pins.lean
example (h : STLmaxU sz0 (STflowE z0) sInst tInst) : STLmax sz0 (STflowE z0) tInst :=
  STLmax_of_STLmaxU sz0 (fun n => (sz0_hst n).le) h
example (h : STLKU sz0 (STflowE z0) sInst tInst) : STLK sz0 (STflowE z0) tInst :=
  STLK_of_STLKU sz0 (fun n => (sz0_hst n).le) h
$ lake build RBM3D.Induction.Step34Pins > build_r.out 2>&1; echo exit=$?; tail -1 build_r.out
exit=0
Build completed successfully (3703 jobs).
$ grep -E "^(warning|error)" build_r.out | grep Step34
warning: RBM3D/Induction/Step34Pins.lean:12:0: The module doc-string for a file should be the first command after the imports.
$ lake build RBM3D 2>&1 | tail -1
Build completed successfully (3745 jobs).
$ lake env lean precheck.lean > precheck.out 2>&1; echo exit=$?   # import RBM3D / import RBM3D.Induction.Step34Pins / #assert_rbm_axioms
exit=0
$ grep -E "^axiom audit|^premises found" precheck.out
axiom audit: 1563 theorems, 628 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 50 (borrowed 2, owed 36, structural 12).
$ grep -ic unclassified precheck.out
0
```
