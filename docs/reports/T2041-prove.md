Prover model: claude-sonnet-5-5
## (a) Math preflight — Sat Oct  3 08:29:35 UTC 2026

Notation: `x=1−u`, `g=ilambda`, `Δ_u=W^{-d}B_{u,0}`, `B_{u,K}=(g²+x)^{-1}(K+1)^{2−d}+(L^d x)^{-1}` (1_2:1108), `r=(1−s)/(1−t)`, `A=g²W^d` (case (i), `1−s≤g²`) or `Δ_s^{-1}` (case (ii)), `𝔠_d`=con_st_ind exponent (1_2:1297), `δ=1/(4p)`, `tr`=unnormalised Tr (main.tex:201). Instance `sz0`, n=0 (`RBM3D/Defs/Sizes.lean:260`): d=3, L=4, W=32, g=1/64, N=2^21, κ=ε=1/10, 𝔡=1/10, 𝔠=1/6.

### (i) Exponent table (values at sz0 n=0, 𝔠_d=1/400; "derived" = my algebra from displayed paper inequalities, checked in the scripts below)
| quantity | value | constraint (source) | slack |
|---|---|---|---|
| 𝔠_d, Step 2 coupling | 1/400 | `𝔠_d C_d<1/5−1/6=1/30` from `Δ^{1/5}r^{C_d}≤Δ^{1/6}` (3_5:1069–1070); `C_d` unfixed by paper | 1/30 vs 𝔠_d·C_d=C_d/400 (C_d<13.3) |
| 𝔠_d, evolution-kernel window | d𝔠_d=0.0075 | `(1−t)/(1−s)≥W^{-1}` needed by `lem:sum_decay` (3_5:1637); con_st_ind + `Δ≥W^{-d}/(g²+1)` give `r≤Δ^{-𝔠_d}≤W` iff d𝔠_d<1 (derived) | r_max=1.026≤W=32; paper cap 10⁻² only gives d≤99, so 𝔠_d must depend on d (it does, 1_2:1295) |
| 𝔠_d, closure of `lem:iterations` | c_max=0.1874 | all terms of the bootstrap (3_5:1775–1861) ≤Ψ(n,k): `c≤3/16−δ/2` (derived; closure.py), independent of n | 1/400 vs 0.1874 (×75) |
| window | (1−t)/(1−s)∈[Δ_t^{𝔠_d},1) | con_st_ind (1_2:1297) | R2: 0.99409≤0.99751; R3: 0.99620≤0.99701; R4: 0.99684≤0.99701 (nonempty) |
| ε in `η_t≥N^{-1+ε}` | 0.1 | N(1−t)≥N^ε | R4 point 1−t=3e-6: N(1−t)=6.3≥4.29 |
| iteration depth k | k_min=⌊2+8𝔠_d(n−1)⌋+1 | `(η_s/η_t)^{n-1}A^{1−k/8}≤A^{3/4}` iff `k>2+8𝔠_d(n−1)` (3_5:1427) | n≤50: k=3 (ratio second/first 0.78..0.995 at A=8); n=51: k=4 |
| #`lem:iterations` calls for (n,k) | k(n−1)+k(k−1) (derived: level l needs r≤n+2(k−l)) | O(1) in the sequence | n=3,k=3: 12; n=10: 33 |
| Ψ exponents (case i / case ii) | `A^{3/4}+r^{n−1}A^{1−k/8}` with A=g²W^d / `Δ_s^{-1}` | (3_5:1396; 3_5:1577: written `(W^{-d}B_{s,0})^{-3/4}+(η_s/η_t)^{n-1}(W^{-d}B_{s,0})^{k/8−1}`) | R2 n=3,k=3: 4.757+3.686; R3: 3.139+2.610; R4: 2.584+2.219 |
| sharp scales | `Δ^{n−1}`, `Δ^n` (n=3) | Step 3 / Step 4 targets (1_2:1362, 1372) | R2 8.73e-3, 8.16e-4; R3 4.75e-2, 1.03e-2; R4 7.98e-2, 2.25e-2 |
| regime values of Δ_t | R1 1.03e-4 (x=0.3); R2 0.0935 (x=1e-4); R3 0.218 (x=5e-6); R4 0.282 (x=3e-6) | R1 x≥g²; R2 g²/L²≤x≤g²; R3 g²/L^d≤x≤g²/L²; R4 x<g²/L^d (g²=2.44e-4, g²/L²=1.53e-5, g²/L^d=3.81e-6) | zero-mode share of B_{t,0}: 0.015, 0.051, 0.438, 0.563; R1 needs no iteration ((lRB1), 3_5:1384) |
| case split | (i) `1−t≥g²/L²`, (ii) `1−s≤g²/L²` | 3_5:1104; middle time `u=1−g²/L²` (footnote) | R2 pair in (i), R3/R4 pairs in (ii) (script checks) |
| martingale loss | δ=1/(4p), p≥4 | `A^δ(Ξ^L_{2n−1})^{1/2}(Ξ^L_{4p})^δ≺Ψ` (3_5:1785–1861); p=⌈1/(4ε')⌉ | ε'=0.01: p=25, Δ^{−δ}≤1.11≤N^{ε'}=1.157 |
| Gronwall absorption | Δ^{1/6}·log r/κ | self term `Δ^{1/6}Ξ̂_n` (sahwNQ, 3_5:1160) must be ≪1/2 | R2 0.040, R3 0.030, R4 0.026 |
| `Ξ^L≲1+ΔΞ^{LK}` (rela_XILXILK) | A^{−1}Ψ | needs A≥1: `g²W^d≥W^{2𝔡}` (1_2:363) | A=8≥1; Ξ^L ≲ 1+A^{-1/4} |
| contract inequality (d≥3) | naive/Ward = `ℓ^dηB_{u,0}` | Ward gives `(W^dη)^{-1}Δ^{n-2}` (3_5:923) vs naive `ℓ^dΔ^{n-1}`; excess `ℓ^{d−2}` (3_5:906) | x=1e-4: 1.17 (ℓ^{d-2}=1.56); x=2e-5: 3.90 (3.49); R3/R4 ℓ=L: 2.28, 1.78 |
| `(ℓ^dη)^{-1}≲B_{u,0}` (eq:Ward_typeP, 3_5:1264) | ratio ≤1 | case (i) only (1−u≥g²/L²) | 0.985, 0.856, 0.257 (x=0.3, 1e-4, 2e-5) |
| EK interface (W^{Cε}≤N^{ε'}, `4≤W^ε`, `log L≤W^ε`, Λ=(log W)^{10}) | W^ε=4 at ε=0.4 (W=32); log L=1.39 | EK pins (Evolution/Pins.lean:76–125): W^{Cε}→N^{ε'} with ε=ε'/C_n, `W^{−D}≤N^{−𝔠D}`; Λ²=(log W)^{20}=o(N^{ε'}) | asymptotic only (inside `≺`, never a hypothesis of a target); witness of Λ²≤N^{ε'} is astronomically large, so no target instance uses it |
| d=2 tokens (RBM2D `c9a24cf`) | | `RBM2D/Induction/Step3.lean:294` Ψ=M_s^{1/2}+R^{n−1}M_s^{1−k/4}, R=(ℓ_t/ℓ_s)² (:57–62), final k=n+1 (:63); `:440` (5.118) split `Ξ_{2n+2}≤Ξ_{2l₁}Ξ_{2l₂}M_u` | d=3: 3/4, k/8, r=η_s/η_t, k>2+8𝔠_d(n−1), splitting of `L^{(2n−1)}` into chains (3_5:1841–1861) |

### (ii) One concrete nondegenerate instance
All deterministic hypotheses at once (d=3, N=2^21, L=4, W=32; `(s,t)` pairs in R2 (case i) and R3/R4 (case ii); nothing collapsed): 𝔠_d=1/400 window, case condition, `N(1−t)≥N^ε`, `(1−t)/(1−s)≥W^{-1}`, k_min, Ψ. Command (`S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2041`): `python3 $S/inst.py | sed -n '1,11p;21,26p;28,32p;34,35p;39p'`
```
sz0 n=0: d=3 L=4 W=32 g=1/64 N=2097152  g^2=0.0002441 g^2/L^2=1.526e-05 g^2/L^d=3.815e-06 N^(-1+eps)=2.044e-06  g^2W^d=8
c_d=0.00250  d*c_d=0.0075 <1 ; W^-1=0.03125
--- (1) one (s,t) pair per regime: window, Delta, Psi, Xi-chain at n=3, k=kmin ---
R1 case(i) 1-s>g^2         1-t=0.3 1-s=0.306 r=1.0200  Delta_t=0.0001032 Delta_s=0.0001012  Delta_t^cd=0.97731<=1/r=0.98039 True | case(i) ok=True  N(1-t)>=N^eps True  (1-t)/(1-s)>=1/W True | zero-mode share of B_t0=0.015
R2 case(i) 1-s<=g^2        1-t=0.0001 1-s=0.0001002 r=1.0025  Delta_t=0.09345 Delta_s=0.09337  Delta_t^cd=0.99409<=1/r=0.99751 True | case(i) ok=True  N(1-t)>=N^eps True  (1-t)/(1-s)>=1/W True | zero-mode share of B_t0=0.051
      n=3 k=kmin=3 A=8  Psi=A^3/4+r^(n-1)A^(1-k/8)= 4.757 + 3.686 ; second/first=0.775 (<1 iff k>2+8cd(n-1)); Delta^(n-1)=0.008732 Delta^n=0.000816 ; iterations k(n-1)+k(k-1)=12
R3 case(ii) g^2/L^d<=1-t   1-t=5e-06 1-s=5.015e-06 r=1.0030  Delta_t=0.2179 Delta_s=0.2176  Delta_t^cd=0.99620<=1/r=0.99701 True | case(ii) ok=True  N(1-t)>=N^eps True  (1-t)/(1-s)>=1/W True | zero-mode share of B_t0=0.438
      n=3 k=kmin=3 A=4.596  Psi=A^3/4+r^(n-1)A^(1-k/8)= 3.139 + 2.61 ; second/first=0.831 (<1 iff k>2+8cd(n-1)); Delta^(n-1)=0.04746 Delta^n=0.01034 ; iterations k(n-1)+k(k-1)=12
R4 case(ii) 1-t<g^2/L^d    1-t=3e-06 1-s=3.009e-06 r=1.0030  Delta_t=0.2824 Delta_s=0.2819  Delta_t^cd=0.99684<=1/r=0.99701 True | case(ii) ok=True  N(1-t)>=N^eps True  (1-t)/(1-s)>=1/W True | zero-mode share of B_t0=0.563
      n=3 k=kmin=3 A=3.547  Psi=A^3/4+r^(n-1)A^(1-k/8)= 2.584 + 2.219 ; second/first=0.859 (<1 iff k>2+8cd(n-1)); Delta^(n-1)=0.07977 Delta^n=0.02253 ; iterations k(n-1)+k(k-1)=12
      (R1: 1-s>g^2 -> B_u0 ~ 1/(1-u); (lRB1) already gives the sharp bound, no iteration; 3_5:1384)
eps'=0.10 p=ceil(1/(4eps'))=3  Delta^(-1/(4p))<=(C W^d)^(1/(4p)) with W^d=32768: 2.3785 ; N^eps'=4.287
eps'=0.01 p=ceil(1/(4eps'))=25  Delta^(-1/(4p))<=(C W^d)^(1/(4p)) with W^d=32768: 1.1096 ; N^eps'=1.157
1-t=0.0001 Delta^(1/6)=0.6736  log r/kappa=0.0593  product=0.03992 <<1/2
1-t=5e-06 Delta^(1/6)=0.7757  log r/kappa=0.0381  product=0.02955 <<1/2
1-t=3e-06 Delta^(1/6)=0.8100  log r/kappa=0.0316  product=0.02560 <<1/2
lower bound Delta>=W^-d/(g^2+1)=3.051e-05 ; r_max=Delta_min^-cd=1.0263 ; W^-1 window need d*cd<1 : r_max<=W: True
1-u=0.3 ell=1.000  ell^d*(1-u)*B_u0=1.015  ell^(d-2)=1.000  (ell^d(1-u))^-1/B_u0=0.985
1-u=0.0001 ell=1.562  ell^d*(1-u)*B_u0=1.168  ell^(d-2)=1.562  (ell^d(1-u))^-1/B_u0=0.856
1-u=2e-05 ell=3.494  ell^d*(1-u)*B_u0=3.896  ell^(d-2)=3.494  (ell^d(1-u))^-1/B_u0=0.257
1-u=5e-06 ell=4.000  ell^d*(1-u)*B_u0=2.284  ell^(d-2)=4.000  (ell^d(1-u))^-1/B_u0=0.438
1-u=3e-06 ell=4.000  ell^d*(1-u)*B_u0=1.777  ell^(d-2)=4.000  (ell^d(1-u))^-1/B_u0=0.563
m=   0 L=    4 W=32 g=0.0156 N=2.1e+06 | (g^2W^d)^-1=0.125 N^-eps=0.233 Delta<= 0.358 | (g^2W^d)^(-1/4)=0.595
m=   1 L=    8 W=1.02e+03 g=0.000244 N=5.5e+11 | (g^2W^d)^-1=0.0156 N^-eps=0.067 Delta<= 0.0826 | (g^2W^d)^(-1/4)=0.354
m= 999 L= 4000 W=3.2e+16 g=1.56e-20 N=2.1e+60 | (g^2W^d)^-1=1.25e-10 N^-eps=9.29e-07 Delta<= 9.29e-07 | (g^2W^d)^(-1/4)=0.00334
```
External hypotheses (Step 1–2 conclusions `STLK/STLmax/STDecay/STLocalMax`, stochastic, owed to ST-1/ST-2): concrete limit along sz0 above, `Δ≤(g²W^d)^{-1}+N^{-ε}→0` (m=0..999: 0.358→9.3e-7), so every `≺` bound is nonvacuous and the Δ-gains strict. Numeric check at the ticket's size, `python3 $S/loop3.py` (d=3, W=2, L=3, N=216, g=1/2, E=0, `H_u=√u·H`, `z_u=i(1−u)`, S from 1_2:302–305, 100 samples; max over all 8 σ and 27³ a of `|Tr∏G(σ_i)E_{a_i}|`; case (i) rows 1–3, case (ii) rows 4–7; Δ≈1 at W=2 near g²/L^d, so only O(1) ratios are visible; from the table, max over samples/Δ² is 0.89, 0.66, 2.0, 2.9, 5.1, 6.8 for the rows with Δ<1 and 15 for the last row, mean/Δ² in [0.47, 2.7]):
```
d,W,L,g,N= 3 2 3 0.5 216  n=3 loops: 8 sigma x 27^3 a-triples; samples=100
g^2=0.25  g^2/L^2=0.02778  g^2/L^d=0.009259
regime (case)                           1-u   Delta_u  (Delta)^2 mean max|L3| max max|L3| mean/Delta^2
1-u>=g^2 [case i]                       0.5    0.1759    0.03095    0.02521    0.02764     0.814
g^2/L^2<=1-u<=g^2 [case i]              0.1    0.4034     0.1628    0.07702     0.1072     0.473
1-u=g^2/L^2 boundary [case i]       0.02778    0.6167     0.3803     0.2745     0.7616     0.722
g^2/L^d<=1-u<=g^2/L^2 [case ii]        0.02    0.6944     0.4823     0.4291      1.384     0.890
g^2/L^d<=1-u<=g^2/L^2 [case ii]       0.012    0.8629     0.7446     0.9651      3.792     1.296
1-u~g^2/L^d [case ii, extreme]     0.009259    0.9821     0.9646      1.522      6.605     1.578
1-u=g^2/(2L^d) <g^2/L^d [beyond]    0.00463     1.491      2.223      5.952      33.62     2.678
python3 loop3.py  114.43s user 0.23s system 99% cpu 1:54.85 total
```
Closure of `lem:iterations` (exponent algebra of 3_5:1775–1861 with only its stated hypotheses; `python3 $S/closure.py`):
```
c_d=1/400, p=1000: chain (r,l), 1<=l<=k_min(n), 2<=r<=n+2(k-l), uses only the hypotheses of lem:iterations
n=  2 k_min= 3 closes=True 
n=  3 k_min= 3 closes=True 
n=  4 k_min= 3 closes=True 
n=  5 k_min= 3 closes=True 
n= 10 k_min= 3 closes=True 
n= 50 k_min= 3 closes=True 
n=100 k_min= 4 closes=True 
n=300 k_min= 8 closes=True 
largest c for which the chain closes (bisection), per n:
n=  4 c_max=0.1874
n=  8 c_max=0.1874
n= 16 c_max=0.1874
n= 32 c_max=0.1874
n= 64 c_max=0.1874
```
### Verdict per target (math preflight)
- Targets 2, 3, 4, 6, 9 (pins for Steps 3–4, EK-6 consumer form, exponent table, skeleton, instances): **PASS**. Every exponent closes: Ψ recursion for all n with 𝔠_d<3/16−δ/2; `k>2+8𝔠_d(n−1)`; Gronwall self-term ≪1/2; Step 4 (saww02) needs only `Δ^{-δ}≺1`, p arbitrary.
- Targets 1, 5, 7, 8 (inventory, routes, block Anderson, split): no mathematical hypothesis to check; **PASS**.
- Findings for stage 1b (leads, derived by me, not proved): (F1) the window `(1−t)/(1−s)≥W^{-1}` of the EK pins follows from con_st_ind only if d𝔠_d<1 (𝔠_d depends on d, 1_2:1295; the cap 10⁻² alone gives d≤99). (F2) The splitting of `L^{(2n−1)}` into two chains (3_5:1841, "following (5.118) of [YY_25]") is an external-paper step; in case (i) its constant is `g²W^d`; in case (ii) the paper omits the proof (3_5:1594) and the constant must be `Δ_s^{-1}`: at the R4 point `g²W^d=8` vs `Δ_s^{-1}=3.55`, and for g≍1 the step `A^{1/2+δ}r≤Δ_s^{-3/4}` would fail with `g²W^d` (≫Nx). (F3) `lem:iterations` lists only r≤n+2 at level k−1; its proof also uses the a priori bound for `Ξ^L_{4p}` (3_5:1861, p≥4). (F4) Ψ(·,0)=`A^{3/4}+r^{n−1}A` (a priori, 3_5:1391).
## (b) Script output — probe `RBM3D/Probe/T2041Pins.lean` (branch `t/T2041`, commit `3c58211`, base `64bdfd3`, 2199 lines); tables, routes, split, scripts: `docs/reports/T2041-portmap.md` (P.1–P.10; written at `80162ae`)
**Size against DECISIONS §9 O2 (item 8): 34 proof tickets (S3-01…S3-27, with a/b sub-tickets; P.7), estimated 37820 lines (600–1500 per ticket): above 25 and not above 40, so not above 50 and no question to Jun.  The 41 RBM2D ST-3 files (38991 kept lines) are: 24 sources (25261 kept lines), 10 not on the d ≥ 3 route (10819 kept lines: PP*, LocalForm*, AltSymm), 3 elsewhere (1166: Chain to ST-6, HierAlgebra and HierarchyN to ST-2), 3 moved to ST-1 by T2015 (1745), 1 unreachable (Region).**

### b.1 Build, axioms, hygiene
```
$ date -u; git log --oneline 64bdfd3..HEAD; git diff --name-only 64bdfd3 HEAD; git status --short | wc -l
Sat Oct  3 10:17:10 UTC 2026
3c58211 T2041: probe repair R1, R2: instances of STLmax_of_STLmaxU, STLK_of_STLKU and the case-(ii) Step 3 skeleton
80162ae T2041: probe: docstring cites corrected (TeX labels, HierVocab port range 150-193)
3a71bc9 T2041: probe: exact TeX line cites in docstrings (labels checked against the TeX)
23a8d08 T2041: probe RBM3D/Probe/T2041Pins.lean (ST-D3: Steps 3-4 pins, ingredients, EK consumer forms, skeletons, instances)
RBM3D/Probe/T2041Pins.lean
0
```
```
$ lake build RBM3D.Probe.T2041Pins > build.out 2>&1; tail -1 build.out; <counts of build.out>; grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Probe/T2041Pins.lean; decls.py; grep "^import RBM3D"
Build completed successfully (3703 jobs).
warnings in T2041Pins.lean: 0; errors: 0; `#print axioms` lines: 179; exactly [propext, Classical.choice, Quot.sound]: 173; no axiom: 4; proper subset of the three: 2 (STAlternating [propext, Quot.sound]; ekE [propext, Quot.sound])
forbidden tokens: 0; public declarations: theorem=94 abbrev=1 def=85
import RBM3D.Induction.Defs;import RBM3D.Evolution.SumDecay;import RBM3D.Propagator.Prop6Hold;import RBM3D.Loop.KLWard;
$ lake env lean RBM3D/Probe/T2041Pins.lean > lean.out; echo exit=$?; wc -l < lean.out; tail -1 lean.out
exit=0
179
'RBM.Gauss.T2041Inst.inst_step3_skeletonII' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep "depends on axioms" build.out | <the 19 target theorems and the 4 skeleton/bridge instances below>
exactly [propext, Classical.choice, Quot.sound] for 23 of 23: STLmax_of_STLmaxU STLK_of_STLKU inst_step3 inst_step3I inst_step3II inst_step4 inst_step4I inst_step4II inst_SEforLn inst_OeqNQ inst_OeqQt inst_OeqQtNZ inst_iterations inst_iterationsII stek_sumNdecay stek_sumRes2NAL st_iterate st_step3_skeleton st_step4_skeleton inst_STLmax_of_STLmaxU inst_STLK_of_STLKU inst_step3_skeleton inst_step3_skeletonII
```

### b.2 Item 1 — inventory (the 41-row table: lines, kept lines, class, tokens, labels, ST-4/5/6 consumers, importers: P.1)
```
$ python3 inv.py; (public names of ST-3 files referenced by ST-4/ST-5/ST-6 files, from inv.json)
files=41 lines=50307 kept=38991; moved to ST-1 by T2015: 3 files, kept=1745
token check (recomputed vs portmap): ScaleFacts:2!=0
classes {'b': 37, 'a': 2, 'd': 1, 'c': 1}
ST-4: mono_right_eventually, perTimeCalc_mono, perTimeCalc_of_imp, perTimeCalc_of_imp_union, stochDom_of_le_left_eventually
ST-5: Alternating, BcalEDecay_sum_sum_norm_SB, HierarchyN, KcalDecay, MLExpPin, SumZeroQ_Psum_Qop, SumZeroQ_Psum_vartheta, SumZeroQ_commutator, SumZeroQ_hasDerivAt_vartheta, SumZeroQ_varthetaDot_eq, elklkN, hierarchyN, kcalDecay, lkTensor, norm_gloop_le_opNorm, norm_sum_SB_le_left, norm_sum_SB_le_right, qopDecay, qopNorm, thetaSig, vartheta, varthetaDot
ST-6: AltAbsorb, AltLevelsE, MLExpPin, PPTargetV2, STOeqTargetV2, chainStepCond, chainTarget, decayLoopFromML, gridGoodPPN, initAtZero, kcalDecay, ppArithN, ppCondVarN, ppDriftN, ppDriftSumN, ppKernelN, ppQVSumN, ppTargetV2_of_ppPins, step3, step4, step5, stoeqTargetV2
```
(`token check`: ScaleFacts has 2 hits of the portmap regexes, both in comments (lines 18, 69); the T2002 row 582 gives no token count; the file moved to ST-1.)

### b.3 Targets: Steps 3 and 4 and their inputs (statements extracted by script; every pin and ingredient: P.2)
```lean
L183: def STLmaxU (E s t : ℕ → ℝ) : Prop := ∀ k : ℕ, 1 ≤ k → Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n))) (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (k - 1))
L191: def STLKU (E s t : ℕ → ℝ) : Prop := ∀ k : ℕ, 1 ≤ k → Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n))) (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω - STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ k)
L228: def STStep2Concl (E s t : ℕ → ℝ) (Cd : ℝ) : Prop := STLocalEntryU sz E s t ∧ STAvgU sz E s t ∧ STGdecayW sz E s t Cd
L257: def STStep3R (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop := 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd → ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) → R sz s t → STKbound sz (STflowE z) → STKward sz (STflowE z) → STLK sz (STflowE z) s → STConStInd sz 𝔠d s t → STStep1Loop sz (STflowE z) s t → STStep2Concl sz (STflowE z) s t Cd → STLmaxU sz (STflowE z) s t
L268: def STStep4R (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop := 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd → ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) → R sz s t → STKbound sz (STflowE z) → STKward sz (STflowE z) → STLK sz (STflowE z) s → STConStInd sz 𝔠d s t → STStep1Loop sz (STflowE z) s t → STStep2Concl sz (STflowE z) s t Cd → STLmaxU sz (STflowE z) s t → STLKU sz (STflowE z) s t
L421: def STXiBoot (E s t : ℕ → ℝ) : Prop := ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ, (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) → (∀ m, 1 ≤ m → STlenL n_ p m → Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q _ => XL m n q.1.2)) → (∀ m, 1 ≤ m → m + 1 ≤ n_ → Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) → Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 n_ ω) (fun n q _ => STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n q.1.2) n_ p)
L485: def STIterR (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (Aof : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → ℕ → ℝ) : Prop := 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd → ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) → R sz s t → STKbound sz (STflowE z) → STLK sz (STflowE z) s → STConStInd sz 𝔠d s t → STStep1Loop sz (STflowE z) s t → STStep2Concl sz (STflowE z) s t Cd → STXiBoot sz (STflowE z) s t → ∀ n_ k : ℕ, 2 ≤ n_ → 1 ≤ k → (∀ r, 2 ≤ r → r + 1 ≤ n_ → STIterHyp sz (STflowE z) s t (Aof sz s) r k) → (∀ r, 2 ≤ r → r ≤ n_ + 2 → STIterHyp sz (STflowE z) s t (Aof sz s) r (k - 1)) → STIterHyp sz (STflowE z) s t (Aof sz s) n_ k
L282: def STStep3 (d : ℕ) : Prop := STStep3R d STAny
L284: def STStep3I (d : ℕ) : Prop := STStep3R d STCaseI
L285: def STStep3II (d : ℕ) : Prop := STStep3R d STCaseII
L283: def STStep4 (d : ℕ) : Prop := STStep4R d STAny
L286: def STStep4I (d : ℕ) : Prop := STStep4R d STCaseI
L287: def STStep4II (d : ℕ) : Prop := STStep4R d STCaseII
L279: def STAny {d : ℕ} (_sz : Sizes d) (_s _t : ℕ → ℝ) : Prop := True
L291: theorem STLmax_of_STLmaxU {E s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (h : STLmaxU sz E s t) : STLmax sz E t
L298: theorem STLK_of_STLKU {E s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (h : STLKU sz E s t) : STLK sz E t
```

### b.4 Compiled nonempty instances (item 9): 33 `theorem inst_*` (the 26 named in P.8, the generic `inst_ing`, `inst_iter`, `inst_step3R`, `inst_step4R`, and the repair instances `inst_STLmax_of_STLmaxU`, `inst_STLK_of_STLKU`, `inst_step3_skeletonII`); five shown
```lean
L1341: def InstStep3Concl (sz : Sizes 3) (z : ℕ → ℂ) (s t : ℕ → ℝ) (Cd : ℝ) : Prop := ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧ (STKbound sz (STflowE z) → STKward sz (STflowE z) → STLK sz (STflowE z) s → STStep1Loop sz (STflowE z) s t → STStep2Concl sz (STflowE z) s t Cd → STLmaxU sz (STflowE z) s t)
L1430: theorem inst_step3II (h : STStep3II 3) (Cd : ℝ) (hCd : 0 < Cd) : InstStep3Concl szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) Cd
L1488: theorem inst_iterations (h : STIterations 3) (Cd : ℝ) (hCd : 0 < Cd) : InstIterConcl (fun sz _ n => STAI sz n) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) Cd
L1804: theorem inst_STLmax_of_STLmaxU (h : STLmaxU sz0 (STflowE z0) sInst tInst) : STLmax sz0 (STflowE z0) tInst
L1809: theorem inst_STLK_of_STLKU (h : STLKU sz0 (STflowE z0) sInst tInst) : STLK sz0 (STflowE z0) tInst
L1998: theorem inst_step3_skeletonII (hIter : ∀ n_ k : ℕ, 2 ≤ n_ → 1 ≤ k → (∀ r, 2 ≤ r → r + 1 ≤ n_ → STIterHyp szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) (fun n => STAII szB (fun _ => 15 / 16) n) r k) → (∀ r, 2 ≤ r → r ≤ n_ + 2 → STIterHyp szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) (fun n => STAII szB (fun _ => 15 / 16) n) r (k - 1)) → STIterHyp szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) (fun n => STAII szB (fun _ => 15 / 16) n) n_ k) (hbase : ∀ r, 2 ≤ r → STIterHyp szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) (fun n => STAII szB (fun _ => 15 / 16) n) r 0) (hrela : ∀ r, 2 ≤ r → Prec szB (U := STPair (fun _ => (15 / 16 : ℝ)) (fun _ => 31 / 32)) (fun n q ω => STXiL szB n (STflowE zB n) q.1.1 r ω) (fun n q ω => 1 + szB.Bctl n q.1.1 * STXiLK szB n (STflowE zB n) q.1.1 r ω)) : ∀ k, 2 ≤ k → Prec szB (U := fun n => TimeIcc (fun _ => (15 / 16 : ℝ)) (fun _ => 31 / 32) n × (Fin k → Bool) × (Fin k → Zd 3 (szB.L n))) (fun n p ω => ‖Lloop szB n (STflowE zB n) (p.1 : ℝ) p.2.1 p.2.2 ω‖) (fun n p _ => (szB.Bctl n (p.1 : ℝ)) ^ (k - 1))
L1908: theorem szB_AII_eq (n : ℕ) : STAII szB (fun _ => 15 / 16) n = 68 / 81 * ((szB.W n : ℕ) : ℝ) ^ 3
```
```
$ sed -n 1805p; sed -n 1810p; sed -n 2014,2015p RBM3D/Probe/T2041Pins.lean   (proof terms: the deterministic hypotheses discharged)
  STLmax_of_STLmaxU sz0 (fun n => (sz0_hst n).le) h
  STLK_of_STLKU sz0 (fun n => (sz0_hst n).le) h
  st_step3_skeleton szB (tendsto_size szB szB_tendsto) (fun n => lt_of_lt_of_le one_pos (szB_AII_ge_one n))
    (fun _ => by norm_num) hIter hbase (fun r _ => szB_scale_PsiII r) szB_scale_BII hrela
$ grep -c '^theorem inst_' RBM3D/Probe/T2041Pins.lean; grep "depends on axioms" build.out | grep "\.inst_" | grep -c "\[propext, Classical.choice, Quot.sound\]"
33
33
```

### b.5 EK-6 consumer form (item 3): kernel statements used in `3_5:900-1934`, and two derivations from merged pins, compiled
```
$ python3 ekuse.py   (one line per label; the lines are joined with " | " here)
lem:sum_Ndecay no occurrence | sum_res_Ndecay [1439] | sum_res_1 no occurrence | sum_res_2_NAL [1133, 1153, 1159, 1166] | sum_res_2 [1261, 1358, 1681, 1711] | lem:sum_decay [1133, 1439] | lem:sum_decay_nonzero [1557, 1559, 1902, 1908] | sum_res_Ndecay_nonzero [1440] | lem:propT no occurrence | claim:TTk no occurrence | eq:latticesum_d3 no occurrence | eq:THETAINFTINF no occurrence | prop:ThfadC [1123] | prop:ThfadC0 [1440]
```
```lean
L691: theorem stek_sumNdecay (d : ℕ) : STEKSumNdecay d
L718: theorem stek_sumRes2NAL (d : ℕ) : STEKSumRes2NAL d
L644: def STEKSumRes2NAL (d : ℕ) : Prop := 3 ≤ d → ∀ n_ : ℕ, 2 ≤ n_ → ∀ κ 𝔠 𝔡 : ℝ, 0 < κ → ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ s t : ℕ → ℝ, STEKWin sz s t → ∀ m : ℕ → ℂ, (∀ n, ‖m n‖ = 1) → (∀ n, κ ≤ (m n).im) → ∀ σ : Fin n_ → Bool, (∃ k, σ k = σ (finRotate n_ k)) → ∀ 𝒜 : (∀ n, TimeIcc s t n → sz.SeqΩ → (Fin n_ → Zd d (sz.L n)) → ℂ), STEKDecay sz s t 𝒜 → ∀ X : (∀ n, TimeIcc s t n → sz.SeqΩ → ℝ), STEKLow sz s t X → Prec sz (U := fun n => TimeIcc s t n) (fun n v ω => ‖𝒜 n v ω‖) X → Prec sz (U := fun n => TimeIcc s t n) (fun n v ω => ‖UN d (sz.L n) (sz.lam n) (EKsgn (m n) σ) (v : ℝ) (t n) (𝒜 n v ω)‖) (fun n v ω => ((sz.lam n ^ 2 + |1 - (v : ℝ)|) / (sz.lam n ^ 2 + |1 - t n|)) ^ (n_ - 1) * X n v ω)
```

### b.6 Skeletons (item 6; the ingredients are hypotheses)
```lean
L1052: theorem st_iterate {S : ℕ → ℕ → Prop} (hbase : ∀ r, 2 ≤ r → S r 0) (hstep : ∀ n k, 2 ≤ n → 1 ≤ k → (∀ r, 2 ≤ r → r + 1 ≤ n → S r k) → (∀ r, 2 ≤ r → r ≤ n + 2 → S r (k - 1)) → S n k) : ∀ k r, 2 ≤ r → S r k
L952: theorem st_step4_skeleton {E s t : ℕ → ℝ} {Λ : ℝ} (hsize : Tendsto sz.size atTop atTop) (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1) (hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λ) (hBoot : STXiBoot sz E s t) (h3 : STLmaxU sz E s t) (h1 : STAvgU sz E s t) : STLKU sz E s t
L1094: theorem st_step3_skeleton {E s t : ℕ → ℝ} {A : ℕ → ℝ} (hsize : Tendsto sz.size atTop atTop) (hA : ∀ n, 0 < A n) (ht1 : ∀ n, t n < 1) (hIter : ∀ n_ k : ℕ, 2 ≤ n_ → 1 ≤ k → (∀ r, 2 ≤ r → r + 1 ≤ n_ → STIterHyp sz E s t A r k) → (∀ r, 2 ≤ r → r ≤ n_ + 2 → STIterHyp sz E s t A r (k - 1)) → STIterHyp sz E s t A n_ k) (hbase : ∀ r, 2 ≤ r → STIterHyp sz E s t A r 0) (hscale : ∀ r, 2 ≤ r → ∃ k : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ q : STPair s t n, STPsi (A n) (etaT (E n) (s n) / etaT (E n) q.1.2) r k ≤ c * A n ^ (3 / 4 : ℝ)) (hBA : ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ n in atTop, ∀ v : TimeIcc s t n, sz.Bctl n (v : ℝ) * A n ^ (3 / 4 : ℝ) ≤ c) (hrela : ∀ r, 2 ≤ r → Prec sz (U
```

### b.7 Name clash, ports, RBM2D citations
```
$ python3 clash.py RBM3D/Probe/T2041Pins.lean <main worktree>; python3 cites.py
probe public declarations: 172; library files scanned: 79
full-name clashes (probe vs library): 0 []
same short name, different namespace: 2 ['ekAz', 'ekE']
cites checked (RBM2D at c9a24cf, RBM3D commits as named): 52; token found on the cited line (or the next): 52; failures: 0
```
```
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Induction/HierVocab.lean
 RBM2D/Induction/HierVocab.lean | 392 ++++++++---------------------------------
 1 file changed, 77 insertions(+), 315 deletions(-)
(RBM2D HEAD 9e0f275; ported: the definitions `LLf … eeN`, probe section 1, cited `HierVocab.lean:150-193` at `c9a24cf`, `eeN` ends at 193, `end Hierarchy` at 200; `T41_sum_fin_two` is `c961e62:RBM3D/Probe/T2016Pins.lean:507`; no RBM1D text)
```

### b.8 Numeric checks of the new statements (`d = 3`, `W = 2`, `L = 3`; discussion P.8)
```
$ python3 contract.py; python3 vartheta.py
d,W,L,g,N= 3 2 3 0.5 216 ; samples 6
regime                          1-u      eta | contraction n=3: max over (sigma,a1,a2) of sum_a3|L3| / RHS(k=1), RHS(k=2) | Ward n=2: max|P1 L2 - (L1+ - L1-)/(2iN eta)|
1-u=0.5                         0.5      0.5 | max ratio k=1: 0.938  k=2: 0.938 (must be <= 1) | 6.94e-18
1-u=g^2/L^2                  0.0278   0.0278 | max ratio k=1: 0.818  k=2: 0.818 (must be <= 1) | 7.49e-16
1-u=g^2/(2L^3)              0.00463  0.00463 | max ratio k=1: 0.854  k=2: 0.854 (must be <= 1) | 2.86e-14
1-u=g^2/(10L^3)            0.000926 0.000926 | max ratio k=1: 0.437  k=2: 0.437 (must be <= 1) | 1.44e-12
d=3 g=0.50 L=48: Theta_t(0,0)=L^-d sum_k 1/(1-t Shat(k))
       1-t    ell_t (1-t)Theta(0,0)         ell^-2         ell^-d  ratio to ell^-d
   1.0e-01     1.58      1.849e-01      4.000e-01      2.530e-01             0.73
   1.0e-02     5.00      2.288e-02      4.000e-02      8.000e-03             2.86
   1.0e-03    15.81      2.450e-03      4.000e-03      2.530e-04             9.68
   3.0e-04    28.87      7.490e-04      1.200e-03      4.157e-05            18.02
   1.0e-04    48.00      2.566e-04      4.340e-04      9.042e-06            28.38
   3.0e-05    48.00      8.341e-05      4.340e-04      9.042e-06             9.22
```

### b.9 Narrative
1. Deliverables: the probe (2199 lines, 180 public declarations, 3c58211), the portmap `T2041-portmap.md` (written at 80162ae) (P.1 inventory, P.2 pins, P.3 EK-6, P.4 exponents with the `d = 2` tokens, P.5 routes, P.6 block Anderson, P.7 split, P.8 instances / extreme inputs / numerics, P.9 findings, P.10 scripts verbatim) and this report.  T2028 is merged at the base `64bdfd3`: the probe imports `RBM3D.Induction.Defs` (ST-1 pins) and copies nothing from `T2015Pins`.
2. Uniformity in `u`: `STPair s t n` is `{(v,u) : s_n ≤ v ≤ u ≤ t_n}`; `STLmaxU`, `STLKU` take `TimeIcc s t n` into the `Prec` index (union inside `P`, scale `N = (WL)^d`); the endpoint `u = t` is the ST-1 `STLmax`/`STLK` (compiled `STLmax_of_STLmaxU`, `STLK_of_STLKU`).  Control parameters are constant in `v` (T2041a).
3. `STStep3R`, `STStep4R` are generic in a regime predicate `R` (`STAny`, `STCaseI`, `STCaseII`; case (i) `1-t ≥ g²/L²`, case (ii) `1-s ≤ g²/L²`): `∀ κ ε 𝔡, ∀ C_d, ∃ 𝔠_d ≤ 1/100, ∀ 𝔠 sz z …`; hypotheses: `STLK` at `s`, `(lRB1)`, `STStep2Concl`, `(con_st_ind)`, `STKbound`, `STKward`.
4. Step 2: the ST-1 pins are at one time `τ`; Step 3 needs `(Gt_bound_flow)`, `(Gt_avgbound_flow)` and `(Eq:Gdecay_w)` for all `u ∈ [s,t]`, the last with the loss `((1-s)/(1-u))^{C_d}`; they are bundled as `STStep2Concl` (`STLocalEntryU`, `STAvgU`, `STGdecayW`), which T2039 must imply.
5. Ingredients (P.2): `STContract` ((yi2oslxj2), (u2jzooi-2)), `STSEforLn`, `STXiBoot` ((am;asoi222)), `STOeqNQ`, `STOeqQt`, `STOeqQtNZ`, `STNewPQ`, `STIterations`/`STIterationsII` (`Ψ = A^{3/4} + r^{n-1}A^{1-k/8}`, `A = ilambda² W^d` resp. `(W^{-d}B_{s,0})⁻¹`), `STMollifierProps`, `STQopNorm`; zero modes through the merged `zeroModeSet`.
6. EK-6 (b.5, P.3): consumer Props at scale `N`: `STEKSumNdecay`, `STEKSumRes2NAL`, `STEKSumRes2`, `STEKNonzero` (used in `3_5:900-1934` by ekuse.py) and `STEKSumRes1` (listed by the ticket; `(sum_res_1)` does not occur there); `lem:propT`, `claim:TTk`, `(eq:latticesum_d3)` do not occur either, so Steps 3–4 do not consume them.  Two Props are derived by compiled theorems from the merged `ekSumNdecay_holds`, `ekSumDecayNAL_holds`.
7. Skeletons (b.6): `st_iterate` (double induction on `(n,k)`), `st_step4_skeleton` (saww02 inductively in `n`), `st_step3_skeleton` (both cases, generic in `A`, from `lem:iterations` / `STOeqQtNZ`; instantiated in case (i) by `inst_step3_skeleton` at `(szB, 7/8, 15/16)`, `A = STAI`, and in case (ii) by `inst_step3_skeletonII` at `(szB, 15/16, 31/32)`, `A = STAII = (68/81) W³`); the generic `Prec` calculus lemmas (`st_prec_of_xi`, `st_prec_one_add_sup`) are proved.
8. Instances (b.4, P.8): 33 `theorem inst_*` at two `d = 3` sequences, the merged `sz0` and the new `szB` (`L = 4`, `W_n = n+4`, `ilambda = 1`).  Case (ii) is instantiated at `(s,t) = (15/16, 31/32)` with `1-s = ilambda²/L²` exactly, `lem:iterations` at `(7/8, 15/16)` with `1-t = ilambda²/L²` exactly.  Only stochastic premises stay hypotheses.  The deep regime `1-t < g²/L^d` is numeric only (P.8, (a)(ii)).
9. Numerics (b.8): the contraction inequality `(yi2oslxj2)` at `n = 3` has max ratio 0.938 over four regimes of `1-u` (must be ≤ 1); the Ward step of `lem: newPQ` holds to 1.44e-12; the RBM2D `Θ`-based `ϑ` violates the sup bound at `d = 3`: `(1-t)Θ_t(0,0) ℓ_t^d` grows from 0.73 to 28.4 (F-B).
10. Split (P.7): 34 tickets, 37820 estimated lines; roles prover: 5, prover-hard: 23, prover-max: 6, risks low: 4, medium: 21, high: 9; the tickets without an RBM2D source are S3-02, S3-03, S3-20, S3-21, S3-22, S3-23, S3-27; the critical prover-max tickets are S3-12, S3-18b, S3-22, S3-24b.
11. Block Anderson (P.6): `7_8:2101` says Steps 3–6 extend verbatim except `sec:Step5_larget` and `lem:LWterm_EXP`; the `Prec` calculus, skeletons and pin shapes carry over; the BA gate adds the flow, `Mbound_AO` decay for the zero-mode kernels, and the BA Step-2 pins.
12. New at `d ≥ 3` and without a printed proof (risk for the auditor): `STContract` (checked numerically only), `STNewPQ`, `STOeqQtNZ`, `STIterationsII` (the paper omits the case-(ii) iteration, `3_5:1594`: F-F).  Each pin has a compiled instance with its deterministic hypotheses discharged (b.4, P.8).

## (c) Verified Mathlib names
```
$ lake env lean origin.lean (one `#origin NAME` per identifier of the probe; `resolveGlobalConstNoOverload`, module from `env.getModuleIdxFor?`); mathlib_names.txt
119 distinct names resolved, 108 in Mathlib.*, 11 in Init.*, 0 unresolved (names below by their resolved full name; the tactics `by_cases`, `by_contra`, `norm_num`, which also resolve, are omitted)
```
abs_le abs_of_pos abs_pos add_le_add Complex.I div_le_div_iff₀ div_le_div_of_nonneg_left div_le_div_of_nonneg_right div_le_iff₀ div_lt_iff₀ div_lt_one div_nonneg div_nonpos_of_nonpos_of_nonneg div_pos exists_nat_gt Filter.eventually_ge_atTop Filter.Eventually.of_forall Filter.tendsto_atTop_mono Filter.tendsto_pow_atTop Fin.ext Fin.sum_univ_three Finset.exists_mem_eq_sup' Finset.Icc Finset.Ioc
Finset.le_sup' Finset.mem_univ Finset.sum_filter Finset.sum_ite_eq' Finset.sum_sub_distrib Finset.univ Finset.univ_nonempty Fintype.sum_equiv Fintype.sum_prod_type' Function.update gt_mem_nhds inv_anti₀ inv_le_one_of_one_le₀ inv_one inv_pos ite_false le_of_eq le_rfl le_trans List.ofFn lt_div_iff₀ lt_min lt_of_le_of_lt lt_of_lt_of_le Matrix.cons_val_zero MeasureTheory.measure_mono min_le_left
min_le_right mul_comm mul_le_mul mul_le_mul_of_nonneg_left mul_le_mul_of_nonneg_right mul_neg_of_pos_of_neg mul_nonneg mul_one mul_pos Nat.cast_nonneg Nat.le_add_right Nat.le_mul_of_pos_right Nat.le_self_pow Nat.lt_or_ge Nat.pow_le_pow_left Nat.strong_induction_on Nat.succ_pos norm_nonneg norm_zero not_or one_le_div one_le_pow₀ one_pos Or.inr pi_norm_le_iff_of_nonneg Pi.zero_apply pow_le_pow_left₀
pow_nonneg pow_pos Real.exp Real.one_le_rpow Real.one_lt_rpow Real.one_rpow Real.pow_rpow_inv_natCast Real.rpow_add Real.rpow_le_one Real.rpow_le_one_of_one_le_of_nonpos Real.rpow_le_rpow Real.rpow_le_rpow_of_exponent_le Real.rpow_le_rpow_of_nonpos Real.rpow_mul Real.rpow_natCast Real.rpow_neg Real.rpow_nonneg Real.rpow_one Real.rpow_pos_of_pos Real.sqrt Real.sqrt_eq_rpow Real.sqrt_le_sqrt
Real.sqrt_one Real.sqrt_sq Real.zero_rpow Set.Icc Set.Ico Set.mem_univ Set.univ sq_nonneg sub_zero tendsto_const_nhds tendsto_natCast_atTop_atTop tendsto_natCast_atTop_iff tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_rpow_atTop two_pos zero_le_one zero_sub ZMod.val_one'' ZMod.val_zero
Names verified absent: none searched (a missing name would fail the build).  The other identifiers of the probe are RBM3D declarations (checked by the build).

## (d) Open issues, paper-delta candidates, registry classes
(a′): no correction to section (a).  Its leads were used: F1 (window) in `STEKWin` and the P.4 row `(con_st_ind)` (the pin only fixes `𝔠_d ≤ 1/100`, so the proving ticket S3-23 can take `𝔠_d ≤ min(1/100, 1/(2d))`); F2 in `STAI`/`STAII` and T2041f; F3 in `STlenL` and the hypotheses of `STIterR`; F4 as the base case `S r 0` of `st_iterate`.
**Findings (P.9).**
- (F-A) 10 of the 37 files (`PP*` six files 4454 kept lines; `LocalForm*` three files 5958; `AltSymm` 407) are not on the `d ≥ 3` route: `(Eq:Gdecay_w)` covers all four charges (`1_2:1349`), and `(sum_res_2)` needs only sum-zero and decay (EK-4), not the `a-local-form` of the `d = 2` paper; 10819 kept lines are not ported.
- (F-B) the `Θ`-based `ϑ` of RBM2D is not a valid mollifier at `d ≥ 3` (P.8); `ϑ` must be differentiable in `t` (`ℓ_t` has kinks): `STMollifierProps`.
- (F-C) `(yi2oslxj2)` and `(u2jzooi-2)` are new at `d ≥ 3`.
- (F-D) ST-2 imports nine ST-3 files in RBM2D (P.1): ST-3 tickets S3-01, S3-06 (and the drift algebra `HierAlgebra`, `HierarchyN`, 742 kept lines, which I leave to the ST-2 design T2039) must precede the ST-2 grid proofs.
- (F-E) `lem:propT`, `claim:TTk`, `(sum_res_1)`, `(eq:latticesum_d3)` are not consumed by Steps 3–4 (P.3); `(eq:sumtwoloop)` needs the lattice sum `W^d Σ_{a₂} 𝒯_t(|a₁-a₂|) ≺ η_t⁻¹` of the tail function, which is not an EK pin (route: merged `RadialSum`, S3-06).
- (F-F) the case-(ii) iteration (`eq:psipara_smalletacase`, `3_5:1577`) has no proof in the paper ("we omit the details", `3_5:1594`): `STIterationsII` is a new proof obligation with `A = (W^{-d}B_{s,0})⁻¹`.
- (F-G) `lem:iterations` uses `(5.118)` of [YY_25] (`3_5:1841`), an external step; RBM2D has it as `loopXi_le` (ST-1, S1-09).
- (F-H) `STKbound`/`STKward` are per time sequence; the uniform-in-`u` form needed in `st_step3_skeleton` follows because the `𝒦`-bounds are deterministic (choose the maximizing `u_n`): one small lemma in S3-06.
- (F-I) the regimes are properties of the whole sequence (`∀ n`); the footnote of `3_5:1105` (middle time `u = 1-g²/L²`) is handled for general `(s,t)` by S3-27, by modifying the sequences off the set of `n` where a regime fails.
**Paper-delta candidates.**
- `T2041a`: `(am;asoi222)` is pinned with control parameters constant in `v ∈ [s,u]` (depending on the endpoint `u`), the maxima over `O(1)` terms written as sums, and only the lengths that occur controlled; `lem:STOeq_NQ` has the supremum of the hatted self-term on the right.
- `T2041b`: the mollifier of `rmk:choosechi` is pinned by its properties (`STMollifierProps`: sum one, sup bound, differentiable, `∂_t` bound) and an existence pin; the scale in `f_t` must be smoothed (kinks of `ℓ_t`).
- `T2041c`: `lem_+Q` carries `4 ≤ W^ε` and `L^d ≤ W^K` (same defect as T2016b, T2042a).
- `T2041d`: Steps 3–4 are pinned per regime `R ∈ {STAny, STCaseI, STCaseII}`; the general statement is an assembly pin (S3-27).
- `T2041e`: the quantifier order `∀ C_d ∃ 𝔠_d` (`(eq:sumtwoloop)`, `3_5:1070`: "sufficiently small depending on `C_d`"), consistent with `STMainInd` when `C_d` is the Step-2 exponent.
- `T2041f`: case-(ii) `A = (W^{-d}B_{s,0})⁻¹` (the printed `Ψ`); case (i) `A = g² W^d`.
- `T2041g`: `lem:SEforLn` (4) is pinned for `(ℰ⊗ℰ)^{M,(n)} = Σ_k (ℰ⊗ℰ)^{M,(n;k)}` (`defEOTE`, `3_5:176-180`); the paper states it for each `(n;k)`, which implies the sum up to the factor `n`.
- `T2041h`: `lem_wardineq_K` is pinned at the scale `N` (`STKward`), from the `L^τ`-loss form of KL12.
- `T2041i`: the paper proves Steps 3–4 and their ingredients under all hypotheses of `lem:main_ind` (`1_2:1313` "Throughout these steps, we assume the hypotheses of lem:main_ind hold"; `3_5:1137,1365,1408,1562` "Under the assumptions / In the setting of lem:main_ind"). `STStep3R`, `STStep4R`, `STIngR`, `STIterR` assume only (a) `(Eq:L-KGt+IND)` at `s` (`STLK`) out of those hypotheses, and drop (b)–(d) (`STDecay`, `STDecayStrong`, `STLocalMax`, `STExp2` at `s`, carried by `STMainInd`); they add `STKbound` (`ML:Kbound`) and `STKward` (`lem_wardineq_K`). The only uses of an induction hypothesis in the Steps 3–4 text (`3_5:900-1934`) are the citations of `(Eq:L-KGt+IND)` at `3_5:1159,1681,1902` (script in the Repair section); the pins are therefore stronger statements than the paper's, with a hypothesis set that differs from it.
**Registry classes (DECISIONS §16, §20) of the `Prop`s taken as hypotheses.**
- Nothing is left without a proving ticket.
- `STKbound` (KL7), `STLK` (ST-6 chain induction), `STStep1` (S1-36; its output `STStep1Loop` is a hypothesis here): merged, in `owedProps` of `RBM3D/Test/Axioms.lean`; `STConStInd`, `STFlow`: merged, in `structuralProps`.
- `STKward`: owed (KL12, bridge in S3-06).
- `STStep2Concl` and its three parts, `STGdecayW`: owed (ST-2, T2039).
- `STLmaxU` (hypothesis of Step 4), `STXiBoot` (hypothesis of `STIterR`), `STIterHyp`: owed (S3-25, S3-18b/S3-22).
- `STContract`, `STNewPQ`, `STSEforLn`, `STOeq*`, `STIterations*`, `STMollifierEx`, `STQopNorm`, `STWardTypePPin`, `STB45Pin`: owed when used as hypotheses.
- `STEK*` consumer pins: owed (EK-6).
- `STMollifierProps`, `STCaseI`, `STCaseII`, `STAny`, `STRegIterI`, `STEKDecay`, `STEKLow`, `STEKWin`, `STAlternating`: structural (properties of an object, regimes, data conditions).  The probe is never imported, so `RBM3D/Test/Axioms.lean` is not touched.
**Open.** (1) The regime `1-t < g²/L^d` is numeric only (no compiled instance: it needs `lemT z ≥ 1-t` at `N`-dependent `Im z`).  (2) Every pin named in P.7 is a statement, not a proof; `STContract`, `STNewPQ`, `STOeqQtNZ`, `STIterationsII` have no RBM2D proof to port.  (3) The probe is not imported by `RBM3D.lean`, so `RBM3D/Test/Axioms.lean` is untouched.

## Repair (round 1 audit `T2041-audit.md`, RETURN R1–R3) — Sat Oct  3 10:18:32 UTC 2026 (`date -u`), Prover model: claude-opus-5-5
```
$ git -C ../RBM3D-wt/T2041 log --oneline -1; git -C ../RBM3D-wt/T2041 diff --stat 80162ae 3c58211
3c58211 T2041: probe repair R1, R2: instances of STLmax_of_STLmaxU, STLK_of_STLKU and the case-(ii) Step 3 skeleton
 RBM3D/Probe/T2041Pins.lean | 132 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 132 insertions(+)
$ grep -rnw <each new name> RBM3D/ (main worktree library) | wc -l
inst_STLmax_of_STLmaxU 0, inst_STLK_of_STLKU 0, szB_AII_eq 0, szB_AII_ge_one 0, szB_ratioII 0, szB_scale_PsiII 0, szB_scale_BII 0, inst_step3_skeletonII 0
$ awk 'NR>=900&&NR<=1934&&/L-KGt\+IND/{print NR}' paper/tex/3_5_Loop_Hierarchy.tex | tr '\n' ' '
1159 1681 1902
```
- R1: `inst_STLmax_of_STLmaxU`, `inst_STLK_of_STLKU` at `(sz0, z0, sInst, tInst)` (`d = 3`), `hst` from `sz0_hst`; `STLmaxU`/`STLKU` stay hypotheses (b.4, axioms b.1).
- R2: `inst_step3_skeletonII` at `(szB, zB, 15/16, 31/32)` (the `STCaseII` data of `szB_caseII`), `A = STAII szB (fun _ => 15/16)`; `hsize`, `hA` (`szB_AII_ge_one`), `ht1`, `hscale` (`szB_scale_PsiII`: `k = 8`, `c = 1 + 2^{r-1}`), `hBA` (`szB_scale_BII`: `c = 64`) discharged; `hIter`, `hbase`, `hrela` stay hypotheses (b.4).
- R3: candidate `T2041i` in (d).
