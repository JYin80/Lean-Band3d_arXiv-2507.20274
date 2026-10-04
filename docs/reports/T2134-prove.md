Prover model: claude-sonnet-5-5
## (a) Math preflight — Sun Oct  4 12:21:12 UTC 2026

Notation: `x=1−u`, `g=ilambda`, `A=g²W^d`, `Δ_u=W^{-d}B_{u,0}`, `ρ=(1−s)/(1−t)`, `B_{u,K}=(g²+x)^{-1}(K+1)^{2−d}+(L^d x)^{-1}` (1_2:1107), `ℓ_u=min(max(g x^{-1/2},1),L)` (1_2:1121), `c_d`=con_st_ind exponent (1_2:1296). Instance `sz0` (`Defs/Sizes.lean`, `L=4(n+1), W=(2(n+1))^5, g=(2(n+1))^{-6}`), `n=0`: d=3, L=4, W=32, g=1/64, N=2^21, A=8, 𝔡=ε=1/10, c_d=1/400 (T2041's choice; paper only 0<c_d≤10^{-2}, 1_2:1295). "derived" = my algebra from displayed paper lines, checked by the scripts below.

### (i) Exponent table (d=3; numbers from the scripts in (ii))
| quantity | value | constraint (source) | slack |
|---|---|---|---|
| ρ window | ρ_ext=Δ_t^{-c_d}: 1.0059 (i), 1.0038 (ii), 1.0232 (iii) | `Δ_t^{c_d}≤1/ρ<1` (1_2:1296); `Δ_t≥W^{-d}/(1+g²)` | ρ≤(W^d(1+g²))^{c_d}=1.026 at n=0 |
| A | 8 (n=0); `A_n=(2(n+1))³` | `A≥W^{2𝔡}` (from `W^{-d/2+𝔡}≤g`, 1_2:363) | W^{2𝔡}=2.0 ≤ 8 |
| (i) amplitude | `B_{u,0}g²=0.748` ∈[1/2,1+L^{2−d}]; `(1−s)²ℓ_s⁴/g⁴=1.0000` | `B_{u,0}≍g^{-2}`, `ℓ_u≍g x^{-1/2}` (3_5:1958); `Δ_u≥1/(2A)` | exact equality of the CLT amplitude (3_5:2209) |
| (i) ρ-losses in `(iois-mtx)` (3_5:2046–2067) | `ρA^{-1/3}`, `ρA^{-1/2}`, `ρ³A^{-1/4}` against target `A^{-1/5}`; ratios 0.7624, 0.5391, 0.9174 | `ρ≤A^{2/15}, A^{3/10}, A^{1/60}`: ρ³ = `(1−s)²/(1−t)²` (uuwmskiow) × ρ (uwftgwesj) | binding: martingale; `(2A)^{c_d}≤A^{1/60}` iff `A≥2^{c_d/(1/60−c_d)}`=1.13 (c_d=1/400), 2.83 (c_d=1/100); A=8 |
| (i) Step-2 inputs | `A^{-1/6}` (3_5:1961), `A^{-1/3}` (3_5:1970), `A^{-1/2}` (3_5:1975) | target `Δ^{1/5}` (1_2:1380): exponents 1/3, 1/2 ≥ 1/5; 1/6 enters only squared (`S5WG+M000`, → 1/3) | 1/3−1/5=2/15 and 1/2−1/5=3/10 (these set `ρ≤A^{2/15}, A^{3/10}`) |
| (i) initial term | IND `A^{-6/5}/(|a|^{d−2}+1)` (3_5:2154) vs target `A^{-1/5}W^{-d}𝒯_t≍A^{-6/5}/(|a|+1)` | CLT target `ℓ_s⁴/(|a|^{d−2}+1)·(1−s)²g^{-4}A^{-6/5}` | `(1−s)²ℓ_s⁴/g⁴=1` (case i), 0.108 (case ii) |
| (i) CLT counting | cluster of size k: `d−(d−2)k+(d+2)(k−1)+2=4k`; `Σ(|x|^{d−1}+1)^{-k}<∞` iff `(d−1)k>d` | k≥2 at d=3 (fails k=1 and d=2,k=2); singletons killed by isolation W^{-D} (3_5:2245: cited DYYY25 (7.39), RBSO1D (A.112)) | identity holds ∀d≥3,k (script) |
| (i) CLT gain (toy) | at ℓ_t=12: Q_triv=30.3 → Q_mean=1.61 (exact), Q_fl=0.62 | see (ii) part B; target normalised O(1)·log | gain 19× (mean), 49× (fluct) |
| (eq:assmtlarge) 3_5:1953 | `(log W)^{10}`; at n=0: W^{d c_d}=1.026 ≪ (log W)^{10}=2.5e5 | branch ρ>(log W)^{10} needs ρ≤(W^d(1+g²))^{c_d}: only for log W ≳ 1.26e4 (c_d=1/400) | large-ρ branch is not instantiable at a concrete W: pin as case split |
| (eq:ells_to_ellt, ellt2) 3_5:2119, 2124 | `ℓ_t/ℓ_s=ρ^{1/2}>(log W)^5` | `ℓ_s(log W)^{5/2}≤½(log W)^{3/2}ℓ_t` iff `ℓ_t/ℓ_s≥2 log W` (derived) | holds iff (log W)⁴≥2, W≥3.28 |
| (ii) zero mode | `ℓ=L`; `B_{u,0}g²=1.743≥1`; `(1−s)L²/g²=0.3287` | `‖Θ̊‖_{∞→∞}≺g^{-2}L²` (3_5:2264); `(1−s)²‖Θ̊‖‖Θ‖≤ρ(1−s)L²/g²≤ρ` (derived; paper says "similar argument", 3_5:2268) | one ρ, not ρ²; `ρA^{-1/4}≤A^{-1/5}` by c_d |
| (ii) Ward term (zYU1) | `A^{-1}(L^dx)^{-1}` / `A^{-1/5}B_{t,L/2}e^{-(1/2)^{1/2}}`=0.2691 | ≤1 (3_5:2258; `Nη_t≍W^dL^d(1−t)` by `η_t≍1−t`, 1_2:720) | A^{-4/5}=0.1895 |
| (iv) | `(L^dx)^{-1}≥g^{-2}≥(g²+x)^{-1}` at `x≤g²/L^d` (derived) | zero mode ≥ half of `B_{t,0}`; handled by Step 4 (1_2:1371) | no new exponent |
| (iii) amplitude | `B_{u,0}(1−u)`=0.5156 at x=g², 1.0148 at x=0.3 ∈[1/2,1+L^{-d}] | `(W^{-d}B_{u,0})²≍(W^d(1−u))^{-2}` (3_5:2288), constants in [1/4,(1+L^{-d})²] | factor ≤4 |
| (iii) ⇒ `(Gdecay_flow)` | ratio `Δ²e^{-√r}/[Δ^{1/5}W^{-d}B_{t,r}e^{-√r}]`=0.001–0.31 at r≤2 | needs `(r+1)Δ^{4/5}≲1` for `r≤(D log W)²`, beyond which `e^{-√r}≤W^{-D}` (derived; paper 3_5:2382 "stronger") | `Δ^{-4/5}`=9.0 (x=g²), 1545 (x=0.3) vs `r+1≤3`: holds up to ≺ only |
| tailtoTail (3_5:2345; `neiwuj` 2357) | q=2dtg²/(1+2dg²−t)=0.8564, 0.3996, 0.5452, 0.8486 | `q≤2d/(2d+1)=6/7=0.8571` using `1−t≥g²` (Fable §2) | 7e-4 at the boundary `1−t=g²` |
| tailtoTail constant | `max_a (U∘T_s)/T_t`=1.3590, 1.0716, 1.1151, 1.3460 (ρ=10³,10³,10³,10²) | `≤C'²`, `C'=ΣP̃e^{√|x|}`=3.59,1.73,2.06,3.50 (C'²=12.9,3.0,4.2,12.3) | Fable's 1.36 reproduced at new point (L=16, ρ=10³) |
| (iii) closure in ε | exponents `2ε−2𝔡`, `1.5ε−𝔡`, `1.5ε−𝔡/2` (Fable §4(3), from `res_deccalE_*`, `W^{-2𝔡}≥A^{-1}`) | each ≤ε iff ε≤2𝔡, 2𝔡, 𝔡 | ε<𝔡=0.1 (Fable: 𝔡/4); asymptotic in W only |

### (ii) One concrete nondegenerate instance
Scripts in `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2134` (python3, numpy). All deterministic hypotheses at once: d=3, `sz0` n=0, window ρ≤Δ_t^{-c_d}, case conditions, `0≤s<t<1`, `W^{-d/2+𝔡}≤g≤1/𝔡`, `N(1−t)≥N^ε` (the `η_t≥N^{-1+ε}` window of T2041 (a)); the other n show the sequence (A_n→∞).
A. `python3 $S/seq.py | awk 'NR<=2 || /^ +(0|9|999) /'`
```
sz0_n: L=4(n+1) W=(2(n+1))^5 g=(2(n+1))^-6 (Defs/Sizes.lean sz0); pair (s,t) per case with rho=Delta_t^-cd (extremal con_st_ind)
   n      A=g^2W^d  WO:g>=W^(-d/2+fd)  case:  Delta_t      rho    1-t        1-s<=bound  N(1-t)>=N^eps  s>=0,t<1
     0            8  True   (i)    8.7240e-02  1.00612  1.221e-04  True   True  (256>=4.29)  True
     0            8  True   (ii)   2.1717e-01  1.00382  5.035e-06  True   True  (10.6>=4.29)  True
     0            8  True   (iii)  1.0323e-04  1.02321  3.000e-01  True   True  (6.29e+05>=4.29)  True
     9         8000  True   (i)    8.3337e-05  1.02376  1.221e-16  True   True  (2.56e+08>=270)  True
     9         8000  True   (ii)   1.3444e-04  1.02254  5.035e-20  True   True  (1.06e+05>=270)  True
     9         8000  True   (iii)  1.0173e-19  1.11553  3.000e-01  True   True  (6.29e+23>=270)  True
   999        8e+09  True   (i)    8.3333e-11  1.05974  1.221e-40  True   True  (2.56e+20>=1.08e+06)  True
   999        8e+09  True   (ii)   1.2509e-10  1.05866  5.035e-48  True   True  (1.06e+13>=1.08e+06)  True
   999        8e+09  True   (iii)  1.0173e-49  1.32581  3.000e-01  True   True  (6.29e+59>=1.08e+06)  True
```
A'. `python3 $S/exps.py | grep -v 'r=1:\|r=2:'` (n=0 numbers of the table; `r` = |a₁−a₂|)
```
sz0: d=3 L=4 W=32 g=1/64 N=2097152 g^2=2.4414e-04 g^2/L^2=1.5259e-05 g^2/L^d=3.8147e-06 A=g^2W^d=8.0 W^(2fd)=2.000 cd=0.0025
--- case (i)  g2/L2<=1-t<=1-s<=g2: 1-t=0.0001 rho=Delta_t^-cd=1.00594 1-s=0.000100594 case-ok=True  Delta_t=0.09345 Delta_s=0.09326
    B_t0*g^2=0.748 B_t0*(1-t)=0.3062  ell_t=1.562 ell_s=1.558 sqrt(rho)=1.0030  (1-s)^2 ell_s^4/g^4=1.0000
    r=0: (Gdecay_flow) Delta^(1/5)W^-d B_tr e^-(r/ell)^.5=5.8166e-02 | (Gdecay+s<g) Delta^2 e^-sqrt r=8.7322e-03 | ratio(iii)/(i)=0.150
--- case (ii) g2/Ld<=1-t<=1-s<=g2/L2: 1-t=5e-06 rho=Delta_t^-cd=1.00382 1-s=5.01909e-06 case-ok=True  Delta_t=0.2179 Delta_s=0.2175
    B_t0*g^2=1.743 B_t0*(1-t)=0.0357  ell_t=4.000 ell_s=4.000 sqrt(rho)=1.0019  (1-s)^2 ell_s^4/g^4=0.1082
    r=0: (Gdecay_flow) Delta^(1/5)W^-d B_tr e^-(r/ell)^.5=1.6062e-01 | (Gdecay+s<g) Delta^2 e^-sqrt r=4.7462e-02 | ratio(iii)/(i)=0.295
--- case (iii) 1-s>=1-t>=g2: 1-t=0.3 rho=Delta_t^-cd=1.02321 1-s=0.306963 case-ok=True  Delta_t=0.0001032 Delta_s=0.0001009
    B_t0*g^2=0.001 B_t0*(1-t)=1.0148  ell_t=1.000 ell_s=1.000 sqrt(rho)=1.0115  (1-s)^2 ell_s^4/g^4=1580859.7193
    r=0: (Gdecay_flow) Delta^(1/5)W^-d B_tr e^-(r/ell)^.5=1.6466e-05 | (Gdecay+s<g) Delta^2 e^-sqrt r=1.0657e-08 | ratio(iii)/(i)=0.001
--- case (i) closure of rho-losses vs target A^-1/5 (rho<=Delta_t^-cd, Delta_t>=1/(2A)):
    rho*A^-1/3 / A^-1/5 [L-K x L-K] = 0.7624 <=1 True
    rho*A^-1/2 / A^-1/5 [G-circ] = 0.5391 <=1 True
    rho^3*A^-1/4 / A^-1/5 [martingale, uuwmskiow x uwftgwesj] = 0.9174 <=1 True
    max rho allowed by rho^3 A^-1/20<=1: A^(1/60)=1.0353; (2A)^cd=1.0070<=A^(1/60) True
--- case (ii): Ward term (zYU1): A^-1 (L^d x)^-1 vs A^-1/5 B_tr e^-(r/L)^.5, r=L/2, x=5e-6
    ratio=0.2691  (A^-4/5=0.1895)
    (1-s)L^2/g^2 = 0.3287<=1
--- (eq:assmtlarge) crossover: W^(d cd) = (log W)^10 ; x=log W
    at sz0 W^(d cd)=1.0263 <= (log W)^10=2.500e+05; crossover log W ~ 12587 (W=e^12587)
--- case (iii) closure exponents (derived from Fable/YY25 sketch), per eps; closure iff each exponent <= eps:
    E^{LK x LK}: 2eps-2fd: <=eps iff eps<=2*fd -> eps<=0.200 at fd=0.1
    E^{G~}: 1.5eps-fd: <=eps iff eps<=2*fd -> eps<=0.200 at fd=0.1
    mart: 1.5eps-fd/2: <=eps iff eps<=1*fd -> eps<=0.100 at fd=0.1
--- (iii) => (Gdecay_flow): needs (r+1)Delta^(4/5)<~1 for r<=(D log W)^2 (else e^-sqrt r<=W^-D)
    sz0 x=0.3: Delta^(-4/5)=1545.1; x=g2: Delta^(-4/5)=9.0; L/2+1=3
--- CLT cluster exponent (eq:2p_product_pair): d-(d-2)k+(d+2)(k-1)+2 == 4k for all d>=3,k>=1: True
--- (|x|^(d-1)+1)^-k summable on Z^d iff (d-1)k>d: d=3: [(1, False), (2, True), (3, True)] ; d=2 k=2: False
```
B. CLT cancellation, `python3 $S/clt.py`. Cancelled object: `f^far=(1−s)²Σ_{b1 far}Σ_{b2}Θ_{a1b1}𝓑_{b1b2}(Θ_{b2a2}−Θ_{b1a2})`, `𝓑=(𝓛−𝓚)^{(2)}_s` (3_5:2160, `lem;CLT` 2173). Mean part: `E𝓑` symmetric, translation invariant ⇒ first difference becomes half second difference (BD2, gain `|r|/|a₂−b₁|`); fluctuation part: `IE𝓑` centred, independent beyond `10(log W)³ℓ_s`, 2p-th moment over clusters (gain ~ square root of the number ~ (ℓ_t/ℓ_s)^d of independent summands). Toy: unit profile `𝓑=1/(|x|^{d−2}+1)` for `|x|≤R`, exact periodic `Θ_t` at d=3, `Q=(|a|+1)|f|` (target O(1) up to logs, since `(1−s)²g^{-4}ℓ_s⁴=1`); Q_triv = triangle inequality on `|ΔΘ|`; Q_mean-BD2 = same with `|½ second difference|`; Q_fl = rms of independent centred entries. The toy is not the loop: it idealises independence. At W=2 the paper cutoffs `(log W)³ℓ_s=0.33<1` collapse the b2-range, so R, r0 are free toy cutoffs (L=5 row).
```
  L  ell_t   rho   k  far#  Q_triv  Q_mean-exact Q_mean-BD2 | Q_fl(y-indep) Q_fl(b1-indep,y-coh) | triv/Q_mean triv/Q_fl(b1)   [g=0.3, 1-s=g^2, R=r0=2 (L=5: R=r0=1)]
  5  2.50    6.2   2    80    0.835     0.424     0.597  |   0.0316    0.0988 |     2.0     8.5
 31  3.00    9.0   4 29566    1.478     0.310     0.763  |   0.0109    0.0732 |     4.8    20.2
 31  6.00   36.0   4 29566    8.945     0.761     3.576  |   0.0370    0.2845 |    11.7    31.4
 31 12.00  144.0   4 29566   30.346     1.608     9.960  |   0.0764    0.6185 |    18.9    49.1
 31 12.00  144.0   8 29541   45.079     2.690    14.210  |   0.0962    0.7977 |    16.8    56.5
```
C. tailtoTail at the new point, `python3 $S/ttt.py` (periodic ℓ^∞, `T_{u}(r)=(W^d(1−u))^{-2}e^{-√r}`, `U=P⊗P`, `P=(1−sS)(1−tS)^{-1}`, exact by FFT; the `W^{-D}` part gives exactly ρ²W^{-D}):
```
d=3 L=16 periodic l_inf; tail T_{u,D}(r)=(W^d(1-u))^-2 e^-sqrt r (+W^-D part contributes exactly rho^2 W^-D)
g=0.03  1-s=0.9    1-t=0.0009  rho= 1000.0 | P>=0 True rowsum=rho True g2<=1-t True | q=0.8564 max(1-t)Th/q^|x|1=0.038 offdiag Pt-(1-t)Th<=0 True | R(r=0,1,2,3)=0.266,0.659,0.854,0.974 max_a R=1.3590 C'^2=12.86
g=0.01  1-s=0.9    1-t=0.0009  rho= 1000.0 | P>=0 True rowsum=rho True g2<=1-t True | q=0.3996 max(1-t)Th/q^|x|1=0.107 offdiag Pt-(1-t)Th<=0 True | R(r=0,1,2,3)=0.602,1.018,1.037,1.030 max_a R=1.0716 C'^2=2.98
g=0.01  1-s=0.5    1-t=0.0005  rho= 1000.0 | P>=0 True rowsum=rho True g2<=1-t True | q=0.5452 max(1-t)Th/q^|x|1=0.087 offdiag Pt-(1-t)Th<=0 True | R(r=0,1,2,3)=0.492,0.957,1.032,1.043 max_a R=1.1151 C'^2=4.24
g=0.1   1-s=1      1-t=0.01    rho=  100.0 | P>=0 True rowsum=rho True g2<=1-t True | q=0.8486 max(1-t)Th/q^|x|1=0.039 offdiag Pt-(1-t)Th<=0 True | R(r=0,1,2,3)=0.272,0.672,0.865,0.981 max_a R=1.3460 C'^2=12.26
```
External hypotheses (stochastic, owed to ST-1/ST-2/LW/EK: `STGdecayW`, `STStep4R`, IND at s, `eq:LW_conclusion_exp`, `eq:MG_conclusion3`): concrete limit along `sz0`: `Δ_t` (case i) = 8.7e-2, 8.3e-5, 8.3e-11 at n=0, 9, 999 (seq output), A_n=8→8e9, so every `≺` target size →0 and the window `[Δ_t^{c_d},1)` is nonempty at each n (ρ_ext=1.006…1.33, s<t strictly).

### Verdict
- Target 2 (pins, cases (i),(ii),(iii), tailtoTail, `STDecay ∧ STDecayStrong` assembly) and 3 (exponent table), 5 (skeleton), 7 (instances): **PASS**: every hypothesis holds at the instance above; exponents close with the slacks in the table.
- Targets 1, 4, 6 (inventory, route, split): no mathematical obstruction found; **PASS** (nothing for preflight to falsify).
- Risks for stage 1b (not failures): (R1) `eq:assmtlarge` branch is only asymptotic: pin `ρ>(log W)^{10} → t≥1−(log W)^{-10}` as an implication, no concrete instance; (R2) case (i) martingale needs c_d≲1/60 and the paper omits the case (ii) analogue ("similar argument"); (R3) case (iii) ⇒ `(Gdecay_flow)` and the `(log W)` factors hold only under `≺`/`W^{-D}`; (R4) `eq:bound_isolated` and the `lem_dec_calE` estimates are cited (DYYY25, RBSO1D, YY_25): external hypotheses, class to be proposed; (R5) `tailtoTail` as in Fable (`T_{u,D}`, not `𝒯_t`) is confirmed numerically (max R=1.359≤1.36).

## (a′) Preflight corrections — Sun Oct  4 15:23:05 UTC 2026
- Row "(eq:assmtlarge) 3_5:1953": the label is at `3_5:1954`; no number, instance or verdict of (a) changes.  Replay of the four script blocks of (a) at stage 1b (`python3 check_a.py`: seq.py, exps.py, clt.py, ttt.py re-run with the pipes of (a), compared with the pasted blocks):
```
$ grep -n 'label{eq:assmtlarge}' paper/tex/3_5_Loop_Hierarchy.tex | cut -c1-40
1954:\be\label{eq:assmtlarge} |1-s|/|1-t
$ python3 check_a.py
seq.py | awk       block 11 lines, rerun 11 lines: identical
exps.py | grep -v  block 28 lines, rerun 28 lines: identical
clt.py             block  6 lines, rerun  6 lines: identical
ttt.py             block  5 lines, rerun  5 lines: identical
```

## (b) Script output — Sun Oct  4 15:23:05 UTC 2026; probe `RBM3D/Probe/T2134Pins.lean` (branch `t/T2134`, commit `36fbd3c`, base `3389d24`, 2061 lines); tables, routes, split, registry, scripts: `docs/reports/T2134-portmap.md` (P.1–P.9)
**Size against DECISIONS §9 O2 (item 6): 29 proof tickets S5-01…S5-29 (4 are T2039's ST2-36..39 moved to ST-4 by §28), estimated 25675 lines (mean 885, 600–1400 per ticket): above 25 and not above 40, so not above 50 and no question to Jun (P.5).**
### b.1 Build, axioms, hygiene
```
$ git -C ../RBM3D-wt/T2134 log --oneline 3389d24..HEAD | wc -l; git diff --name-only 3389d24 HEAD; git status --short | wc -l
12
RBM3D/Probe/T2134Pins.lean
0
$ lake build RBM3D.Probe.T2134Pins > build.out 2>&1; grep "Build completed\|^exit=" build.out; grep -c "warning: RBM3D/Probe\|error" build.out
Build completed successfully (3774 jobs).
exit=0
0  (warnings from T2134Pins.lean: 0; errors: 0)
$ lake env lean RBM3D/Probe/T2134Pins.lean > lean.out 2>&1; echo exit=$?; grep -v "depends on axioms" lean.out | grep -vc "^real\|^user\|^sys\|^exit=\|^$"; tail -1 lean.out   (the acceptance command of the ticket)
exit=0
0  (no warning, error or other message)
'RBM.Gauss.T2134Inst.inst_expInv' depends on axioms: [propext, Classical.choice, Quot.sound]
$ python3 axioms.py   (the `#print axioms` lines of lean.out, grouped by axiom set)
print-axioms lines: 72; theorems declared in the probe: 72; theorems without a line: []; lines without a theorem: []
[propext, Classical.choice, Quot.sound] : 72 declarations   [lines in build.out: 72, of which exactly the three: 72]
$ grep -cE "sorry|admit|native_decide|^axiom" T2134Pins.lean; grep -c "^import RBM3D" T2134Pins.lean
0  3  (imports: Induction.KDecay;Induction.NewKLK;Induction.GridDuhamelN)
```
### b.2 Item 1 — inventory (21 rows: lines, kept lines, class, tokens, labels, ST-5/6 consumers, disposition: P.1)
```
$ python3 inv4.py | head -2; python3 map4.py | grep "Case3 \|Case3Defs\|Case5\|CltStep\|^--"
ST-4 files (rule of mkportmap.py): 17; lines 16772; kept 15101; classes {'b': 17}
moved/reference files: Path/LemDecCalE.lean 1258/857/b; Path/LemDecCalEdif.lean 1691/1664/b; Path/LemDecCalEwG.lean 1402/1385/b; Induction/Step45.lean 1445/1318/b
Evolution/Case3               4275  3828   68 sum_decay     d=2 `sum_res_3` + `clt-lemma` (7:100, 7:363-418): no d>=3 counterpart (paper has no `sum_res_3`) [`sum_res_3` in 0 paper files]
Evolution/Case3Defs            182   147    0 sum_decay     d=2 vocabulary of Case 3 / `clt-lemma` (`CltCase1Prec`, `CltCase2Prec`): not needed [absent in RBM3D]
Evolution/Case5               1562  1439   63 sum_decay     d=2 `2k`-kernel (`eq:double_sum_zero_tensor`, 7:119): no d>=3 counterpart [`double_sum_zero` in 0 paper files]
Evolution/CltStep              737   730    1 CLT           source of S5-21 (per-step bound)
-- per group (files, lines, kept): {'sum_decay': (9, 10077, 9113), 'CLT': (8, 6695, 5988), 'lem_dec_calE': (3, 4351, 3906), 'Step 5 d=2': (1, 1445, 1318)}
-- the 17 ST-4 files (T2002 rule): files 17 lines 16772 kept 15101
```
### b.3 Targets: Step 5, its assembly and the skeletons (statements extracted by script; every pin and ingredient: P.2b)
```lean
L81: def STDecayStrongU (E s t : ℕ → ℝ) : Prop := ∀ D : ℝ, 0 < D → Prec sz (U := fun n => {_p : TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) // sz.lam n ^ 2 ≤ 1 - t n}) (fun n p ω => ‖Lloop sz n (E n) (p.1.1 : ℝ) p.1.2.1 p.1.2.2 ω - STKloop sz n (E n) (p.1.1 : ℝ) p.1.2.1 p.1.2.2‖) (fun n p _  ...
L94: def STIngR5 (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop := 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd → ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠  ...
L109: def STStep5Concl {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop := STGdecayW sz E s t 0 ∧ STDecayStrongU sz E s t
L113: def STStep5R (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop := STIngR5 d R (fun sz E s t => STStep5Concl sz E s t)
L463: def STStep5I (d : ℕ) : Prop := STStep5R d STReg5I
L466: def STStep5II (d : ℕ) : Prop := STStep5R d STReg5II
L468: def STStep5III (d : ℕ) : Prop := STStep5R d STReg5III
L470: def STStep5IV (d : ℕ) : Prop := STStep5R d STReg5IV
L473: def STStep5 (d : ℕ) : Prop := STStep5R d STAny
L523: theorem ST_step5_assembly {E s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (h : STStep5Concl sz E s t) : STDecay sz E t ∧ STDecayStrong sz E t :=
L1001: theorem stStep5IV_holds (d : ℕ) : STStep5IV d :=
L744: theorem ST_step5_caseI_of_pins (hE : STEtermsMid d) (hD : STDuhamelI d) (hI : STIniTermI d) : STStep5I d :=
L1546: theorem ST_step5_caseII_of_pins (hE : STEtermsMid d) (hD : STDuhamelII d) (hI : STIniTermII d) (hWd : STWardII d) : STStep5II d :=
L1315: theorem ST_step5_caseIII_of_pf (hPf : STPfStep5 d) : STStep5III d :=
```
### b.4 Item 2 — the 18 pins (line, paper cite, registry class, proof ticket, compiled consumers, instance; `python3 pins.py`)
```
 line pin            paper        class     ticket         compiled consumers (skeleton/bridge theorems) | instance
L463  STStep5I       1_2:1379-1388 owed      S5-02          ST_step5_caseI_of_pins | inst_step5I
L466  STStep5II      1_2:1379-1388 owed      S5-03          ST_step5_caseII_of_pins | inst_step5II
L468  STStep5III     1_2:1379-1388 owed      S5-03          ST_step5_caseIII_of_pf | inst_step5III
L470  STStep5IV      1_2:1379-1388 proved    S5-02          stStep5IV_holds | inst_step5IV
L473  STStep5        3_5:1939     owed      S5-29          - | inst_step5
L285  STEtermsMid    3_5:1968-1979 owed      S5-13          ST_step5_caseI_of_pins ST_step5_caseII_of_pins | inst_etermsMid inst_skeletonI inst_skeletonII
L327  STDuhamelI     3_5:2067     owed      S5-15          ST_step5_caseI_of_pins | inst_duhamelI inst_skeletonI
L332  STIniTermI     3_5:2072     owed      S5-16          ST_step5_caseI_of_pins | inst_iniTermI inst_skeletonI
L408  STCltFar       3_5:2173-2176 owed      S5-25          - | inst_cltFar
L438  STCltIso       3_5:2245     borrowed  S5-17..S5-21   - | inst_cltIso
L453  STExpInv       3_5:2196-2200 owed      S5-22          - | inst_expInv
L337  STDuhamelII    3_5:2263-2277 owed      S5-15,S5-26    ST_step5_caseII_of_pins | inst_duhamelII inst_skeletonII
L343  STIniTermII    3_5:2275-2281 owed      S5-27          ST_step5_caseII_of_pins | inst_iniTermII inst_skeletonII
L358  STWardII       3_5:2257-2262 owed      S5-28          ST_step5_caseII_of_pins | inst_wardII inst_skeletonII
L133  STTailtoTail   3_5:2344-2362 owed      S5-04          - | inst_tailtoTail
L203  STLemDecCalE   3_5:2314     borrowed  S5-05..S5-09   - | inst_lemDecCalE
L221  STPfStep5      3_5:2380     borrowed  S5-10,S5-11    ST_step5_caseIII_of_pf | inst_pfStep5 inst_skeletonIII
L257  STNewKLKL      3_5:628-651  owed      S5-12          - | inst_newKLKL
-- 18 pins; namespaces: ['Sizes']
```
### b.5 Item 7 — compiled nonempty instances: 28 `theorem inst_*` (P.7), by data; regime inequalities recomputed in exact fractions; index sets of the conclusions at the data (re-run at `7b2b789`, written Sun Oct  4 15:46:31 UTC 2026: `python3 repair/inst_groups_r1.py; python3 extreme.py | head -4; python3 repair/szcl.py | head -1; python3 statements.py --oneline --max 330 <5 instances>`)
```
28 instance theorems (RBM.Gauss.T2134Inst), by data
generic shape (any data): inst_ing5
data (szB, zB, 7/8, 15/16): inst_ing5_I inst_step5I inst_etermsMid inst_duhamelI inst_iniTermI inst_skeletonI
data (szB, zB, 15/16, 31/32): inst_ing5_II inst_step5II inst_duhamelII inst_iniTermII inst_wardII inst_skeletonII
data (sz0, z0, 0, 1/16): inst_ing5_III inst_step5III inst_step5 inst_assembly inst_lemDecCalE inst_pfStep5 inst_skeletonIII
data (szG, zB, 5/8, 3/4): inst_ing5_IV inst_step5IV inst_step5IV_proved
data (szCL, zCL, 0, 1 - L_n^{-2}): inst_cltFar inst_cltIso
deterministic pin, own data: inst_tailtoTail inst_newKLKL inst_expInv
szB      g^2=1 L=4 (s,t)=(7/8,15/16): g^2/L^2=1/16 g^2/L^3=1/64 1-t=1/16 1-s=1/8 | regimes holding ['(i)'] | boundary hit: ['1-t = g^2/L^2']
szB      g^2=1 L=4 (s,t)=(15/16,31/32): g^2/L^2=1/16 g^2/L^3=1/64 1-t=1/32 1-s=1/16 | regimes holding ['(ii)'] | boundary hit: ['1-s = g^2/L^2']
szG      g^2=25 L=4 (s,t)=(5/8,3/4): g^2/L^2=25/16 g^2/L^3=25/64 1-t=1/4 1-s=3/8 | regimes holding ['(iv)'] | boundary hit: none
sz0 n=0  g^2=1/4096 L=4 (s,t)=(0,1/16): g^2/L^2=1/65536 g^2/L^3=1/262144 1-t=15/16 1-s=1 | regimes holding ['(iii)'] | boundary hit: ['s = 0']
szCL n=0 L=15925248 W=2^24: g^2/L^2 = 1-t = 1/253613523861504, 1-s = 1 | (i): True | (log W)^5 l_s = 1274041 <= l_t = 15925248: True | L/2 = 7962624 >= 10 (log W)^3 l_s = 46037: True
```
```lean
L1774: theorem inst_ing5 (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (h : STIngR5 3 R Concl) (sz : Sizes 3) (z : ℕ → ℂ) (hflow : STFlow sz (1 / 10) (1 / 10) (1 / 6) (1 / 10) z) (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht : ∀ n, t n ≤ lemT (z n)) ...
L1822: theorem inst_step5I (h : STStep5I 3) (Cd : ℝ) (hCd : 0 < Cd) : InstIng5Concl (fun sz E s t => STStep5Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) Cd :=
L1832: theorem inst_step5III (h : STStep5III 3) (Cd : ℝ) (hCd : 0 < Cd) : InstIng5Concl (fun sz E s t => STStep5Concl sz E s t) sz0 z0 sInst tInst Cd :=
L1852: theorem inst_assembly (h : STStep5Concl sz0 (STflowE z0) sInst tInst) : STDecay sz0 (STflowE z0) tInst ∧ STDecayStrong sz0 (STflowE z0) tInst :=
L2286: theorem inst_tailtoTail (h : STTailtoTail 3) : ∃ C : ℝ, 0 < C ∧ ‖UN 3 5 (1 / 2 : ℝ) (EKsgn Complex.I ![true, false]) (1 / 2 : ℝ) (3 / 4 : ℝ) (fun b : Fin 2 → Zd 3 5 => ((tailTD 3 25 (1 / 2 : ℝ) 2 (zdistInf 3 5 (b 0 - b 1) : ℕ) : ℝ) : ℂ)) ![0, ![1, 0, 0]]‖ ≤ C * tailTD 3 25 (3 / 4 : ℝ) 2 (zdistInf 3 5 ((![0, ![1, 0, 0]] : Fin 2 → ...
```
**Index sets of the instance conclusions at their data** (compiled checks: Repair section): nonempty at every `n` in every instance (`TimeIcc` at the five data; the sign classes `STSigAll`, `STSigMixed`, `STSigSame`; all `(σ, a)`; the pair index of `STLemDecCalEConcl` at sz0 with `a' = a`; `U n` of `STCltFarConcl` at szCL: `szCL_cltFar_index_nonempty`; a `p = 1` configuration meeting the window and isolation premises of `STCltIsoConcl` at szCL: `szCL_cltIso_witness`), with one exception: the conjunct `STDecayStrongU` of `STStep5Concl` (index `g² ≤ 1-t`) is **empty** in `inst_step5I`, `inst_step5II`, `inst_step5IV`, `inst_step5IV_proved`, `inst_skeletonI`, `inst_skeletonII` (szB: `1 > 1/16`, `1 > 1/32`; szG: `25 > 1/4`; the paper states `(Eq:Gdecay+s<g_flow)` only for `1-t ≥ g²`), where the conjunct `STGdecayW` is nonempty; it is nonempty at sz0 (`inst_step5`, `inst_step5III`, `inst_skeletonIII`, `inst_pfStep5`, and `STDecayStrong` in `inst_assembly`).  `inst_ing5`, `inst_ing5_I..IV` take any `Concl`; `inst_tailtoTail` is one inequality at `a = (0, e₁)`.
### b.6 Item 3 — the d = 2 tokens behind the d = 3 exponents (`python3 tokens2.py`: `file:line` of each row, grouped by file here; text and d = 3 replacement of each: P.3)
```
Path/Scales.lean: 38,41,44,48,52; Path/Step2PropsV3.lean: 41; Path/Step2Props.lean: 116; Induction/Step45.lean: 1223,1258; Path/LemDecCalE.lean: 53,61,72,24; Evolution/CltDecorrelation.lean: 263,277,278; Evolution/Case3Defs.lean: 72,98; Evolution/CltMoments.lean: 155; Loop/LatticeCount.lean: 174; Induction/Defs.lean: 151; Evolution/MLExpInv.lean: 729
```
### b.7 Item 6 — split summary (`python3 split.py | tail -4 | head -3`; the 29 rows with files, statements, sources, dependencies, role, risk: P.5)
```
tickets 29 (of which 4 are T2039 ST2-36..39, counted in ST-4 by DECISIONS 28); est lines 25675; mean 885; min 600; max 1400
role count: {'prover': 11, 'prover-hard': 15, 'prover-max': 3} | risk: {'high': 6, 'low': 4, 'medium': 19}
O2 (DECISIONS 9): band 25/40/50: in 25-40 -> question to Jun: no
```
### b.8 Name clash, ports, RBM2D citations
```
$ RBM_ROOT=<clean copy of main 250a118> python3 clash.py; python3 clash2d.py; git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- <the 21 inventory files> | tail -1
new public declarations in the probe: 122 (48 def, 2 abbrev, 72 theorem); distinct short names 122
namespaces: ['RBM', 'RBM.Gauss.Sizes', 'RBM.Gauss.T2134Inst']
(1a) merged declarations with the same FULL name as a new one: 0
(1b) merged declarations with the same SHORT name (other namespace): 1 -> RBM.Green.FlucIterGainInst.szG @ RBM3D/Green/FlucIterGain.lean:977 (private)
(2) grep -rlwE <122 new short names> RBM3D RBM3D.lean (Probe excluded): 1 files -> RBM3D/Green/FlucIterGain.lean
122 public names of the probe; files of RBM2D at c9a24cf (438 files) containing any of them (grep -w): 1 -> RBM2D/Evolution/MLExpVocab.lean:1002 `inst_assembly`: theorem inst_assembly (hDuh : ExpDuhamelPin sizes) (hQDuh : ExpQDuhamelPin sizes)
RBM2D HEAD 9e0f275: 28 files changed, 824 insertions(+), 4315 deletions(-)
```
Ports: none.  No declaration of the probe is taken over from `../RBM1D` or `../RBM2D` (the one coincidence of names is a different statement); RBM2D is read only, cited as file:line at `c9a24cf` (P.1–P.4); the diff-stat above is `c9a24cf..HEAD` over the 21 inventory files (the 9 later RBM2D commits are the dead-code deletion T2274 and the comment clean-ups T2275–T2278, `9e0f275`).
### b.9 Numeric checks of the new statements (d = 3): the block (`newklkl.py`, `ttt2.py`, `strongweak.py`) pasted here at 15:23:05 UTC is moved verbatim to portmap P.8a (Sun Oct  4 15:49:05 UTC 2026, to keep this report within 300 lines)
### b.10 Narrative
1. Deliverables: the probe (2061 lines, 122 public declarations (48 def, 2 abbrev, 72 theorem); 18 pins, 28 `inst_*`, every theorem with exactly the three standard axioms), this report and `T2134-portmap.md` (P.1–P.9).  The probe is never imported, so `Test/Axioms.lean` is untouched.  Main moved after the base (T2131–T2133 and T2135: `LWSymm`, `DecayLoopA/B`, `QGridA`); the clash check and the routes use main `250a118` (F-I).
2. Shape.  Every Step-5 pin is `STIngR5 d R Concl`, the shape of `STIngR` (`Step34Pins.lean:445`): `3 ≤ d`, `∀ κ ε 𝔡 C_d`, `∃ 𝔠_d ∈ (0, 1/100]`, then `𝔠`, `sz`, `z`, `s < t ≤ lemT z`, a regime `R`, and the conclusions of Steps 1–4 (`STDecay`, `STDecayStrong` at `s`, `STStep1Loop`, `STStep2Concl C_d`, `STLmaxU`, `STLKU`) as premises.  `STStep5Concl = STGdecayW … 0 ∧ STDecayStrongU`: the loss `((1-s)/(1-u))^{C_d}` of Step 2 is removed (`C_d = 0`), uniformly in `u ∈ [s,t]` (`TimeIcc`); `ST_step5_assembly` gives `STDecay ∧ STDecayStrong` at `t`.
3. Case (iv) is proved from Step 4 (`stStep5IV_holds`; `3_5:1940`: `ℓ_t = L` and `B_{t,0}` is dominated by the zero mode `(L^d|1-t|)^{-1}`); no ingredient pin.
4. Case (iii): `STPfStep5` (`lem:pf_step5`: `T ≥ t` w.h.p. ⟺ `|𝓛-𝒦| ≺ T_{u,D}`) gives both estimates (`ST_step5_caseIII_of_pf`); `T_{u,D}` is the new `tailTD` (`def_WTuD`, amplitude `η_u^{-2}`), not `tailT` (DECISIONS §33).  `(Eq:Gdecay+s<g_flow)` implies `(Eq:Gdecay_flow)` only up to a polylogarithm that `≺` absorbs (`st5_compare_IIIb`, F-G).  `STTailtoTail` is Fable's `(neiwuj)` (constant `C_d²`, every charge); its instance sits at the boundary `1-t = g²`; numerics: ratio ≤ 1.36 (b.9).
5. Cases (i), (ii) close from three, resp. four, ingredient pins (`ST_step5_caseI_of_pins`, `ST_step5_caseII_of_pins`): `STEtermsMid` ((S5WG+M000), (S5WG+M)), `STDuhamelI/II` ((iois-mtx2): Azuma on the grid; the `ρ`-losses `ρA^{-1/3}`, `ρA^{-1/2}`, `ρ³A^{-1/4} ≤ A^{-1/5}` close for `ρ ≤ (2A)^{𝔠_d}`, `𝔠_d ≤ 1/100 < 1/60`, (a) row 4), `STIniTermI/II` ((iksjuwjx0), (zYU2)), `STWardII` ((zYU1)); the comparison with `(Eq:Gdecay_flow)` is compiled (`st5_compare_I`, `st5_compare_IIward`).  The compiled links stop at these pins: `STIniTermI ⟸ STCltFar` and `STPfStep5 ⟸ STLemDecCalE + STTailtoTail` are proof obligations (F-H).
6. CLT of case (i): `STCltFar` (`lem;CLT`), `STCltIso` (`(eq:bound_isolated)`), `STExpInv`.  New against RBM2D's CLT (`Evolution/Clt*.lean`, the `clt-lemma` used in `lem:sum_decay` Case 3): two-label loops `𝓑_{b₁b₂}` with first differences `Θ_{b₂a₂}-Θ_{b₁a₂}` (RBM2D `CltFarThm` takes one common one-label form, `CltDecorrelation.lean:277-278`); the conclusion keeps `1/(|a₁-a₂|^{d-2}+1)`, so the moment sum needs `(d-1)k > d`, i.e. `k ≥ 2` at `d = 3` (`3_5:2241`; it fails at `d = 2, k = 2`) and singletons are removed by `(eq:bound_isolated)`; the mean part uses translation/reflection invariance and `prop:BD2`; toy gain at `ℓ_t = 12`: 19× (mean), 49× (fluctuation) ((a), part B).
7. `lem:newKLK`: the printed `(juwo=Lklk)` carries `Ĵ + Ĵ²`; with `Ĵ ≺ A^{-1/6}` it is too weak by `ρ A^{1/30}`; the sharp form at `ℓ = L` that the paper's proof gives (`3_5:1968`) is `STNewKLKL` (T2134a); numerics: `R_sharp ≤ 0.64` (b.9).
8. Inventory: the 17 ST-4 files (15101 kept lines) are 9 `lem:sum_decay` files (9113; merged EK-2..EK-6 or no d ≥ 3 counterpart) and 8 CLT files (5988, sources of S5-17..S5-24); with the 3 `LemDecCalE*` files (3906) the sources of Step 5 are 11 RBM2D files (P.1b).
9. Split: 29 tickets, 25675 lines (mean 885), roles 11 prover / 15 prover-hard / 3 prover-max, risks 4 low / 19 medium / 6 high; high: S5-10/11 (`lem:pf_step5`), S5-15 (Duhamel and martingale), S5-23..25 (CLT moments and assembly); `prover-max`: S5-11, S5-15, S5-25.
10. Instances: data `(szB, zB, 7/8, 15/16)`, `(szB, zB, 15/16, 31/32)`, `(sz0, z0, 0, 1/16)`, `(szG, zB, 5/8, 3/4)`, and for `inst_cltFar`, `inst_cltIso` `(szCL, zCL, 0, 1 - L_n^{-2})` (`L_n = 2(n+24)^5`, `W_n = 2^{n+24}`, `g = 1`; at szB, `L = 4`, their index set, resp. isolation premise, is empty: audit round 1 §4); index sets of every instance (b.5): nonempty at every `n`, except the `STDecayStrongU` conjunct in `inst_step5I/II/IV`, `inst_step5IV_proved`, `inst_skeletonI/II` (`g² > 1-t` at szB, szG); boundaries hit exactly: `1-t = g²/L²` (case (i): szB, szCL), `1-s = g²` and `s = 0` (szCL), `1-s = g²/L²` (case (ii)), `s = 0` (case (iii), sz0); only stochastic premises stay hypotheses; `inst_tailtoTail` is at `1-t = g²`, `inst_newKLKL` at `H = 0`, `u = 0` (`δ₀` is existential, T2039 O3).

## (c) Verified Mathlib names
```
$ lake env lean uses_mathlib.lean   (metaprogram: the theorems of Mathlib/Init/Std referenced by the elaborated declarations of RBM3D.Probe.T2134Pins), filtered by `mathlib_names.py` to names that occur in the probe source
-- 110 names (verified present: they are constants of the elaborated environment of RBM3D.Probe.T2134Pins)
```
Complex.norm_real Eq.symm Eq.trans Even.pow_nonneg Filter.Eventually.of_forall Filter.Tendsto.comp Filter.Tendsto.eventually Filter.Tendsto.eventually_ge_atTop Filter.eventually_ge_atTop Filter.tendsto_atTop_mono' Finset.sup_le
IsEmpty.false LE.le.trans LE.le.trans_lt LT.lt.le Matrix.isHermitian_zero Nat.cast_nonneg Real.div_rpow Real.exp_add Real.exp_one_lt_d9 Real.exp_pos Real.inv_rpow Real.log_nonneg Real.mul_rpow Real.norm_of_nonneg Real.one_le_rpow
Real.one_rpow Real.rpow_add Real.rpow_def_of_pos Real.rpow_le_one_of_one_le_of_nonpos Real.rpow_le_rpow Real.rpow_le_rpow_of_exponent_ge Real.rpow_le_rpow_of_exponent_le Real.rpow_mul Real.rpow_natCast Real.rpow_neg Real.rpow_neg_one
Real.rpow_nonneg Real.rpow_one Real.rpow_pos_of_pos Real.rpow_zero Real.sqrt_eq_rpow Real.sqrt_le_sqrt Real.sqrt_nonneg Real.sqrt_sq Set.ext Set.mem_empty_iff_false abs_nonneg abs_of_pos add_le_add add_nonneg div_div_eq_mul_div
div_le_div_iff₀ div_le_div_of_nonneg_left div_le_one div_le_self div_nonneg div_nonpos_of_nonpos_of_nonneg div_one half_pos iff_false inv_anti₀ inv_eq_one_div inv_le_one_of_one_le₀ inv_one le_div_iff₀ le_max_left le_max_right le_or_gt
le_rfl le_self_pow₀ le_total le_trans lt_min lt_of_le_of_lt lt_of_lt_of_le max_eq_left max_eq_right max_le_add_of_nonneg min_eq_left min_le_left min_le_right mul_assoc mul_comm mul_inv mul_le_mul mul_le_mul_of_nonneg_left
mul_le_mul_of_nonneg_right mul_le_of_le_one_right mul_nonneg mul_one mul_pos mul_pow norm_add_le not_exists one_le_pow₀ one_mul one_pos one_pow pow_le_pow_left₀ pow_le_pow_right₀ pow_mul pow_nonneg sq sq_nonneg sq_pos_of_pos
sub_add_cancel tendsto_rpow_atTop trivial zero_le_one
Names verified absent: none searched (a missing name would fail the build).  The other identifiers of the probe are RBM3D declarations (checked by the build; locations: P.4).

## (d) Open issues, paper-delta candidates, registry classes
Leads of (a) used: its exponent rows in the closure remarks of `STDuhamelConcl`, `STEtermsMidConcl`, `st5_compare_*`; R1 → F-E; R2 → F-F; R3 → F-G; R4 → registry (borrowed); R5 → `STTailtoTail` (instance and b.9).
**Findings (portmap P.8).**
- (F-A) 9 of the 17 ST-4 files (9113 kept lines) are the d = 2 `lem:sum_decay` forms (merged EK-2..EK-6, or no d ≥ 3 counterpart); the sources of Step 5 are the 8 CLT files (5988) and the 3 `LemDecCalE*` files (3906).
- (F-B) the d = 2 CLT is one-label with no decay in `|a₁-a₂|`; the d ≥ 3 `lem;CLT` is two-label and keeps the decay: S5-21, S5-23, S5-24 are new work on a ported skeleton (risk high).
- (F-C) the printed `lem:newKLK` is too weak for case (i) by `ρ A^{1/30}`; the sharp form at `ℓ = L` is `STNewKLKL`.
- (F-D) `lem_dec_calE`, `lem:pf_step5`, `(eq:bound_isolated)` are cited, not proved, in the paper (`3_5:2338`, `2380`, `2248`); the d = 3 closure of `lem:pf_step5` is Fable's sketch (confidence 85%, `docs/claude-team/fable/2026-10-04-tailtotail.md` §4(3), §7).
- (F-E) `(eq:assmtlarge)` cannot be instantiated at a concrete `W` (its large-`ρ` branch needs `log W ≳ 1.26·10^4`, (a)); no pin assumes it, the proofs treat both branches.
- (F-F) the case-(ii) closure is not printed (`3_5:2268`, "a similar argument"): `(1-s)² ‖Θ̊‖ ‖Θ‖ ≤ ρ (1-s) L²/g² ≤ ρ`, one `ρ` ((a) row (ii)).
- (F-G) strong ⟹ weak in case (iii) holds only up to a polylogarithm: `st5_compare_IIIb` (constant 4) needs `y^{4/5}((D log W)²+1)^{d-2} ≤ 1`, which holds at the extreme `1-u = g²` only for `W ≳ 2^{102}` (b.9; below it `T/target` exceeds 4 for large `L`); under `≺` it is absorbed (`st5_polylog_le_W`).
- (F-H) the compiled links stop at the pins: `STIniTermI ⟸ STCltFar` (regime reduction `3_5:2119-2128`, `f + g` `2130-2135`, Ward term `g_a` `2136-2146`, `f^{near}` `2160-2171`) and `STPfStep5 ⟸ STLemDecCalE + STTailtoTail` are proof obligations of S5-16 and S5-10/11.
- (F-I) main moved after the base `3389d24` (T2131–T2133 and T2135); (F-J) `STExpInv` is shared with Step 6 (RBM2D `Evolution/MLExpInv.lean` is class c, ST-5): S5-22 or the Step-6 ticket, whichever lands first.
**Paper-delta candidates** (Lean/paper statement differences).
- `T2134a`: `lem:newKLK` at `ℓ = L` in the sharp form `C/(1-u) (Ĵ² W^{-d}𝒯̃^L + Ĵ W^{-d-D})` (`STNewKLKL`); the printed `(juwo=Lklk)` has `Ĵ + Ĵ² 1_{ℓ≥1}`; the paper's remark at `3_5:1968` ("the index sets are empty") is the source, the floor `Ĵ W^{-d-D}` covers `𝒯_u(L) < W^{-D}` (`3_5:612-616`).
- `T2134b`: `TailtoTail` for `T_{u,D}` of `def_WTuD` with explicit constants: `C T_{t,D} + ((1-s)/(1-t))² W^{-D}` (the paper's `≲`), `0 ≤ s ≤ t < 1`, `g² ≤ 1-t` (paper `1-s ≥ 1-t ≥ g²`; `0 ≤ s` implicit), every charge `m`, `σ`, `zdistInf`.
- `T2134c`: `lem_dec_calE` as a `Prec` statement: the control `J*_{u,D} ≥ 1` is a hypothesis function, `W^D ≥ N` is `∀ᶠ n, size ≤ W^D`, uniform in `u ∈ [s,t]`; `T2134d`: `lem:pf_step5` as `max|𝓛-𝒦|/T_{u,D} ≺ 1` for every `D > 0` (paper: `T ≥ t` w.h.p. for small `ε`; `T_{u,D}` decreases in `D`).
- `T2134e`: `(eq:bound_isolated)`, cited in the paper, is pinned (`STCltIso`, every `p ≥ 1`, `D > 0`, eventually in `n`) and proved internally (S5-17..S5-21); `T2134f`: `lem;CLT` is pinned with `(eq:ells_to_ellt)`, `(eq:ells_to_ellt2)` as index-set conditions, `σ₁ ≠ σ₂`.
- `T2134g`: case (ii) is pinned as `STDuhamelII` (`Q^{(1)}` for `σ₁ ≠ σ₂`, none for `σ₁ = σ₂`), `STIniTermII`, `STWardII`; the paper says "we omit the details" / "a similar argument" (`3_5:2253`, `2268`).
- `T2134h`: `(iksjuwjx0)` is pinned with `A^{-1/5} W^{-d}𝒯̃^L_{u,D} + W^{-D}` instead of `A^{-1/5} W^{-d}𝒯_t + W^{-D}` (`𝒯̃^L_{t,D}(r) ≤ 𝒯_t(r) + W^{-D}`: equivalent under `≺`); `T2134i`: the invariance of `𝔼 𝓛^{(2)}` used informally at `3_5:2196` is pinned as `STExpInv`; `STDecayStrongU` has the index set `g² ≤ 1-t` (empty otherwise), as the merged `STDecayStrong`.
- `T2134j` (repair, audit round 1, Required 3): the integrated hierarchy `(iois-mtx2)` (`3_5:2067`) bounds `(𝓛-𝒦)_t` by the random initial term `𝒰∘(𝓛-𝒦)_s` plus `A^{-1/5}W^{-d}𝒯̃^L_{t,D}`; `STDuhamelConcl` pins it conditionally: for every deterministic `F ≥ 0` with initial term `≺ F`, `Q∘(𝓛-𝒦)_u ≺ F + A^{-1/5}W^{-d}𝒯̃^L_{u,D} + W^{-D}`, uniformly in `u ∈ [s,t]`; this covers case (i) (`STDuhamelI`, `Q = ∅`) and case (ii) (`STDuhamelII`), and composes with `(iksjuwjx0)` (`STIniTermI/II`, `F` = its bound).
**Registry classes (DECISIONS §16, §20), proposed (P.6).**
- owed: `STStep5I/II/III`, `STStep5`, `STEtermsMid`, `STDuhamelI/II`, `STIniTermI/II`, `STWardII`, `STNewKLKL`, `STCltFar`, `STExpInv`, `STTailtoTail`; borrowed (the paper cites them, §16; proved internally by S5-05..S5-11, S5-17..S5-21, §5): `STLemDecCalE`, `STPfStep5`, `STCltIso`; structural: `STReg5I/II/III/IV/Mid`; proved in the probe: `STStep5IV`.
- premises of `STIngR5` (`python3 reg.py`, clean copy of main `250a118`): `STFlow`, `STConStInd` structural; `STLK`, `STDecay`, `STDecayStrong`, `STLmaxU`, `STLKU`, `STGdecayW` owed (already listed); `STKbound`, `STKward`, `STStep1Loop`, `STStep2Concl` not listed (proved, or not assumed by a merged theorem).  Nothing is left without a proving ticket; S5-01 adds the registry lines (the probe is not imported).
**Open / for the dispatcher.** (1) Sign-off of the nine candidates and of the registry classes (§4, §20).  (2) T2039's ST2-36..39 are S5-05..S5-08 (§28).  (3) `inst_newKLKL` is at `H = 0`, `u = 0` (T2039 O3 precedent).  (4) The probe's base is `3389d24`: S5-01 starts from main.  (5) `tailTD` is defined in the probe (namespace `RBM`, in the style of `tailT`); S5-01 declares it in its new file `Induction/Step5Pins.lean` unless the dispatcher adds the merged `Defs/Tail.lean` to S5-01's writable files (the ticket asked for it "in `Defs/Tail.lean`'s vocabulary").
## Repair (audit round 1) — Sun Oct  4 15:47:56 UTC 2026; Repairer model: claude-opus-5-5. Required 1–2 in probe commit `7b2b789` (data `szCL`, `zCL`, `sCL`, `tCL`, `xCL`; `inst_cltFar`, `inst_cltIso` moved to it; witnesses `szCL_cltFar_index_nonempty`, `szCL_cltIso_witness`), 3 in (d) `T2134j`, 4 in b.5, b.10 item 10, portmap P.7a/P.7c; full outputs, `IndexCheck.lean` and the 35 Mathlib names the repair adds to (c): portmap P.10.  b.1, b.8, b.10 item 1 and (c) describe `36fbd3c`; at `7b2b789`: 2434 lines, 99 theorems.
```
$ lake build RBM3D.Probe.T2134Pins; lake env lean RBM3D/Probe/T2134Pins.lean > lean.out   (summary line by echo); python3 axioms.py | head -2
Build completed successfully (3774 jobs). build exit=0 | probe warnings: 0 | lake env lean exit=0
print-axioms lines: 99; theorems declared in the probe: 99; theorems without a line: []; lines without a theorem: []
[propext, Classical.choice, Quot.sound] : 99 declarations
$ python3 statements.py --oneline --max 330 inst_cltFar inst_cltIso szCL_cltFar_index_nonempty szCL_cltIso_witness
L2226: theorem inst_cltFar (h : STCltFar 3) (Cd : ℝ) (hCd : 0 < Cd) : InstIng5Concl (fun sz E s t => STCltFarConcl sz E s t) szCL zCL sCL tCL Cd :=
L2232: theorem inst_cltIso (h : STCltIso 3) (Cd : ℝ) (hCd : 0 < Cd) : InstIng5Concl (fun sz E s t => STCltIsoConcl sz E s t) szCL zCL sCL tCL Cd :=
L2163: theorem szCL_cltFar_index_nonempty (n : ℕ) : Nonempty {p : {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd 3 (szCL.L n)) // Real.log ((szCL.W n : ℕ) : ℝ) ^ 5 * ellT (szCL.L n) (szCL.lam n) (sCL n) ≤ ellT (szCL.L n) (szCL.lam n) (tCL n) ∧ ((zdistInf 3 (szCL.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ≤ (1 / 2 : ℝ) * Real.log ((szCL.W n : ℕ) : ℝ ...
L2192: theorem szCL_cltIso_witness (n : ℕ) : ∃ b : Fin (2 * 1) → (Fin 2 → Zd 3 (szCL.L n)), (∀ k, ((zdistInf 3 (szCL.L n) ((b k) 0 - (b k) 1) : ℕ) : ℝ) ≤ Real.log ((szCL.W n : ℕ) : ℝ) ^ 3 * ellT (szCL.L n) (szCL.lam n) (sCL n)) ∧ (∃ i, ∀ j, j ≠ i → 10 * Real.log ((szCL.W n : ℕ) : ℝ) ^ 3 * ellT (szCL.L n) (szCL.lam n) (sCL n) ≤ ((zdistI ...
$ python3 repair/pinmatch.py; lake env lean repair/IndexCheck.lean > indexcheck.out; echo "IndexCheck exit=$? / errors+warnings: $(grep -c 'error\|warning' indexcheck.out)"
STCltFarConcl U (sz,d,s,t := szCL,3,sCL,tCL) == szCL_cltFar_index_nonempty: True
STCltIsoConcl premises (p := 1) == szCL_cltIso_witness: True
IndexCheck exit=0 / errors+warnings: 0
$ grep -rlwE <32 new names> (worktree RBM3D/, RBM3D.lean; main 1ef8fa7; ../RBM2D/RBM2D, ../RBM1D/RBM1D), counts by echo
new names: 32 | files in worktree RBM3D/ RBM3D.lean outside the probe: 0 | in main 1ef8fa7: 0 | in ../RBM2D/RBM2D, ../RBM1D: 0
```
