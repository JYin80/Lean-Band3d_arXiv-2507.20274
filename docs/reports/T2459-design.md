Verdict: BA case (iii) of Step 5 CLOSES WITH NAMED INPUTS (P1 = clause 4 of `STGridRepNAtgL d 2` at `baStep2Mat` = T2460 target 4, which must stay (H249 (3)); U4s1's `T2462_caseIII`; the Steps 1-4 premises of `STIngR5gL`); no stop rule fired (the g = 10 record constants grow with L but the regime is empty: judged not a stop, see (f)). Regime: `STReg5III` read at g = `sz.lam` (empty at g = 1, 10; nonempty at `sz0`, t = 1/2); kernel at g0 = sqrt(t0) g <= g (UBA-C4: only g0 <= g is read, A = (kappa+1)/kappa does not enter). U5 adds no entry-level input and no `BAKellStarEv` (P5). U5's 1b: 5 rows, central 6,900 lines (lo 4,650 / hi 10,600); inputs without producer: none.

# T2459 design: the d = 3 argument for BA case (iii) of Step 5 (U5)
Written Mon Oct 12 17:33:36 UTC 2026 (`date -u`) by the stage-1b prover (claude-sonnet-5-5) on branch `t/T2459` (base `main` 1debc23 = U6 merged). Probe `RBM3D/Probe/T2459Pins.lean` (394 lines, `lake env lean` exit 0). Scripts and the verbatim outputs pasted below: `docs/reports/T2459/` (`bash docs/reports/T2459/run_all.sh` regenerates `out/*.out` in about one minute; `stab.py` is a copy of `docs/reports/T2390/stab.py` of the main worktree, same sha1 98bf532d). Section (a) of `docs/reports/T2459-prove.md` (preflight, PASS) is not edited. `X:N` = `RBM3D/X.lean:N` at the checkout (declaration lines: `out/cite.out`, 99 names, 0 NOT FOUND; other lines: `out/cite_lines.out` prints the cited line of each of 86 citations, 0 out of range); `3_5:N`, `7_8:N` = lines of `paper/tex/3_5_Loop_Hierarchy.tex`, `7_8_light_weight.tex`; probe lines `:N`.

## (a) Numerics (U5-6)
Data as G3a (`T2390-prove.md:11-60`): d = 3, w = i eta (eta = 1.2 at g = 1/64 and 1, 1.0 at g = 10), z = w - m_S(w), t0 = Im m/(Im m + Im z), g0 = sqrt(t0) g, m0 = m/sqrt(t0), K = |M^(B)|^2, Theta_t = (1-tK)^-1, uKer_{s,t} = (1-sK)(1-tK)^-1; Lam = 1/dd = 10; kappa = 1/2, 1/4, 0.04 (kappa <= Im m at every L listed).
```
$ python3 docs/reports/T2459/num.py exps
exponent/threshold table of the argument (d=3, flow (kappa,eps,c,dd)=(1/2,1/10,1/6,1/10), sz0 of Defs/Sizes:260)
n=  0 L=4 W=32 lam=1.562e-02 lam/W^(-d/2+dd)=2.0 N^(1/6)/W=3.54e-01 lam^2<=1/2: True  lam^2 W^d = W^0.600 (need >= W^0.2)  (log W)^(3/2)/8 = 0.81  L/2 = 2
n=  1 L=8 W=1024 lam=2.441e-04 lam/W^(-d/2+dd)=4.0 N^(1/6)/W=8.84e-02 lam^2<=1/2: True  lam^2 W^d = W^0.600 (need >= W^0.2)  (log W)^(3/2)/8 = 2.28  L/2 = 4
n= 10 L=44 W=5.154e+06 lam=8.820e-09 lam/W^(-d/2+dd)=22.0 N^(1/6)/W=2.92e-03 lam^2<=1/2: True  lam^2 W^d = W^0.600 (need >= W^0.2)  (log W)^(3/2)/8 = 7.59  L/2 = 22
n=100 L=404 W=3.363e+11 lam=1.472e-14 lam/W^(-d/2+dd)=202.0 N^(1/6)/W=3.47e-05 lam^2<=1/2: True  lam^2 W^d = W^0.600 (need >= W^0.2)  (log W)^(3/2)/8 = 17.09  L/2 = 202
eps1=min(dd/8,1/4)=0.0125; walk level eps0 < eps1; closure needs eps0 < dd/4=0.025; closure terms: J^(2)*tau <= W^(2 eps0 - 2dd) = -0.180, tau^(1/2) J^(3/2) <= W^(1.5 eps0 - dd) = -0.085, tau^(1/2) J^3 <= W^(3 eps0 - dd) = -0.070, dE^M martingale sqrt(log W) J^(3/2) tau^(1/4) <= W^(eps0*1.5-dd/2) = -0.035  (all < eps0 = 0.01)
```
`sz0` is `Defs/Sizes:260`; `lam^2 W^d = W^0.6` against `W^(2 dd) = W^0.2` of `Admissible`; flow `(kappa, eps, c, dd)` of `flow_sz0` (`FlowPins:1214`); `eps1 = min(dd/8, 1/4)` is the band's (`PfStep5:34, 2139`) and the closure `J* <= C + log W + W^(2 eps - dd/2)` needs `eps < dd/4` (`Step5Pins:194-201`). The four closure exponents (lk, wG, dif, martingale) are negative at eps0 = 0.01: margins 0.035 to 0.18.
```
$ python3 docs/reports/T2459/num.py regime
regime STReg5III (sz.lam^2 <= 1-t) on [0, t0] and the comparison  g0 <= g,  g^2 <= A g0^2, A = (kappa+1)/kappa (TwistStep2_lam0_sq, TwistStep2:740)
g=0.015625 L=  4 t0=0.6937 t0>=kappa/(kappa+1)=0.3333: True g0=0.0130 g0<=g: True g^2/g0^2=1/t0=1.441 <= A=3.00: True window[g]=(0,0.6937] window[g0]=(0,0.6937]
g=0.015625 L= 64 t0=0.6937 t0>=kappa/(kappa+1)=0.3333: True g0=0.0130 g0<=g: True g^2/g0^2=1/t0=1.441 <= A=3.00: True window[g]=(0,0.6937] window[g0]=(0,0.6937]
g=1        L=  4 t0=0.3148 t0>=kappa/(kappa+1)=0.2000: True g0=0.5610 g0<=g: True g^2/g0^2=1/t0=3.177 <= A=5.00: True window[g]=(0,0.0000] window[g0]=(0,0.3148]
g=1        L= 64 t0=0.2862 t0>=kappa/(kappa+1)=0.2000: True g0=0.5350 g0<=g: True g^2/g0^2=1/t0=3.494 <= A=5.00: True window[g]=(0,0.0000] window[g0]=(0,0.2862]
g=10       L=  4 t0=0.3138 t0>=kappa/(kappa+1)=0.0385: True g0=5.6017 g0<=g: True g^2/g0^2=1/t0=3.187 <= A=26.00: True window[g]=(0,0.0000] window[g0]=(0,0.0000]
g=10       L= 64 t0=0.0442 t0>=kappa/(kappa+1)=0.0385: True g0=2.1024 g0<=g: True g^2/g0^2=1/t0=22.624 <= A=26.00: True window[g]=(0,0.0000] window[g0]=(0,0.0000]
```
`STReg5III` (`sz.lam^2 <= 1-t`, with `s >= 0`, `s < t`) is empty for `sz.lam >= 1`: vacuous at g = 1 and 10 (the `window[g]` columns). With the reading g0 (not the size-level name: ticket stop rule 4) it would be nonempty at g = 1 (`(0, 0.2862]`) and still empty at g = 10. At `sz0` it is nonempty: `lam <= 1/64` (`T2459_sz0_lam_le`, probe :94), `t = 1/2 < t0` (`half_lt_t0`, `FlowPins:1254`). The comparison `g0 <= g`, `g^2/g0^2 = 1/t0 <= A` holds in every row (`TwistStep2_lam0_sq`, `TwistStep2:740`); Step 5 reads only the first conjunct.
```
$ python3 docs/reports/T2459/num.py flow big
kernel numerics: per g, L: t_b = min(t0, 1-g^2) (reading sz.lam=g) or min(t0, 1-g0^2) (g0 reading, g=1) or t0 (g=10, record)
cols: ward=|sum_b|M_0b|^2-1|, (1-|m0|^2)/g0^2, gamma(mu_obs)=sum_b K_0b e^{mu_obs |b|_1}, mu_obs = largest mu with t_b gamma(mu) <= (1+t_b)/2 [needs 1-t_b >= g0^2: checked], CU = max_{a,pairs,s} sum_b|uKer_{s,t_b}(a,b)| e^{sqrt|a-b|_inf} / rho (s in {0,t/4,t/2,t}), bound 3 e^{1/(4 mu_obs)}
--- g=0.015625 kappa=0.5  Lean: c=4.1580e-03 A=10^11.5 S1=10^16.8 mu_an=min(c,1/(2 A S1))=10^-28.6 (bound 3exp(1/(4mu)) = exp(10^28.0)) ---
L=  4 t0=0.6937 g0=0.0130 Imm=0.8325 Imm0=0.9995 |m0|=0.99949 ward=0e+00 (1-|m0|^2)/g0^2=5.990 | t_b=0.6937 1-t_b>=g0^2:True mu_obs=>=5 (search cap) gamma(mu_obs)=1.202688 gap(t_b)=0.306 CU=1.0039 bound=3.154
L=  8 t0=0.6937 g0=0.0130 Imm=0.8325 Imm0=0.9995 |m0|=0.99949 ward=0e+00 (1-|m0|^2)/g0^2=5.991 | t_b=0.6937 1-t_b>=g0^2:True mu_obs=>=5 (search cap) gamma(mu_obs)=1.193466 gap(t_b)=0.306 CU=1.0039 bound=3.154
L= 16 t0=0.6937 g0=0.0130 Imm=0.8325 Imm0=0.9995 |m0|=0.99949 ward=4e-16 (1-|m0|^2)/g0^2=5.991 | t_b=0.6937 1-t_b>=g0^2:True mu_obs=>=5 (search cap) gamma(mu_obs)=1.193448 gap(t_b)=0.306 CU=1.0039 bound=3.154
L= 32 t0=0.6937 g0=0.0130 Imm=0.8325 Imm0=0.9995 |m0|=0.99949 ward=0e+00 (1-|m0|^2)/g0^2=5.991 | t_b=0.6937 1-t_b>=g0^2:True mu_obs=>=5 (search cap) gamma(mu_obs)=1.193448 gap(t_b)=0.306 CU=1.0039 bound=3.154
L= 64 t0=0.6937 g0=0.0130 Imm=0.8325 Imm0=0.9995 |m0|=0.99949 ward=1e-16 (1-|m0|^2)/g0^2=5.991 | t_b=0.6937 1-t_b>=g0^2:True mu_obs=>=5 (search cap) gamma(mu_obs)=1.193448 gap(t_b)=0.306 CU=1.0039 bound=3.154
L=128 t0=0.6937 g0=0.0130 Imm=0.8325 Imm0=0.9995 |m0|=0.99949 ward=4e-16 (1-|m0|^2)/g0^2=5.991 | t_b=0.6937 1-t_b>=g0^2:True mu_obs=>=5 (search cap) gamma(mu_obs)=1.193448 gap(t_b)=0.306 CU=1.0039 bound=3.154
--- g=1 kappa=0.25  Lean: c=2.0812e-03 A=10^13.9 S1=10^18.3 mu_an=min(c,1/(2 A S1))=10^-32.5 (bound 3exp(1/(4mu)) = exp(10^31.9)) ---
L=  4 t0=0.3148 g0=0.5610 Imm=0.3777 Imm0=0.6732 |m0|=0.67325 ward=1e-15 (1-|m0|^2)/g0^2=1.737 | t_b=0.3148 1-t_b>=g0^2:True mu_obs=0.318 gamma(mu_obs)=2.088477 gap(t_b)=0.685 CU=1.4795 bound=6.587
L=  8 t0=0.2887 g0=0.5373 Imm=0.3464 Imm0=0.6447 |m0|=0.64474 ward=2e-15 (1-|m0|^2)/g0^2=2.024 | t_b=0.2887 1-t_b>=g0^2:True mu_obs=0.307 gamma(mu_obs)=2.232060 gap(t_b)=0.711 CU=1.5053 bound=6.78
L= 16 t0=0.2862 g0=0.5350 Imm=0.3435 Imm0=0.6420 |m0|=0.64200 ward=1e-15 (1-|m0|^2)/g0^2=2.054 | t_b=0.2862 1-t_b>=g0^2:True mu_obs=0.291 gamma(mu_obs)=2.246876 gap(t_b)=0.714 CU=1.5158 bound=7.076
L= 32 t0=0.2862 g0=0.5350 Imm=0.3435 Imm0=0.6420 |m0|=0.64199 ward=2e-15 (1-|m0|^2)/g0^2=2.054 | t_b=0.2862 1-t_b>=g0^2:True mu_obs=0.288 gamma(mu_obs)=2.246931 gap(t_b)=0.714 CU=1.5163 bound=7.137
L= 64 t0=0.2862 g0=0.5350 Imm=0.3435 Imm0=0.6420 |m0|=0.64199 ward=1e-15 (1-|m0|^2)/g0^2=2.054 | t_b=0.2862 1-t_b>=g0^2:True mu_obs=0.288 gamma(mu_obs)=2.246931 gap(t_b)=0.714 CU=1.5163 bound=7.14
--- g=10 kappa=0.04  Lean: c=3.3328e-04 A=10^20.3 S1=10^22.2 mu_an=min(c,1/(2 A S1))=10^-42.8 (bound 3exp(1/(4mu)) = exp(10^42.2)) ---
L=  4 t0=0.3138 g0=5.6017 Imm=0.3138 Imm0=0.5602 |m0|=0.56017 ward=2e-15 (1-|m0|^2)/g0^2=0.022 | t_b=0.3138 1-t_b>=g0^2:False mu_obs=0.206 gamma(mu_obs)=2.093398 gap(t_b)=0.686 CU=1.6318 bound=10.08
L=  8 t0=0.1380 g0=3.7146 Imm=0.1380 Imm0=0.3715 |m0|=0.37146 ward=6e-15 (1-|m0|^2)/g0^2=0.062 | t_b=0.1380 1-t_b>=g0^2:False mu_obs=0.197 gamma(mu_obs)=4.123715 gap(t_b)=0.862 CU=1.5648 bound=10.64
L= 16 t0=0.0604 g0=2.4575 Imm=0.0604 Imm0=0.2458 |m0|=0.24575 ward=2e-14 (1-|m0|^2)/g0^2=0.156 | t_b=0.0604 1-t_b>=g0^2:False mu_obs=0.162 gamma(mu_obs)=8.778942 gap(t_b)=0.940 CU=1.5119 bound=14.1
L= 32 t0=0.0469 g0=2.1662 Imm=0.0469 Imm0=0.2166 |m0|=0.21662 ward=1e-14 (1-|m0|^2)/g0^2=0.203 | t_b=0.0469 1-t_b>=g0^2:False mu_obs=0.101 gamma(mu_obs)=11.155529 gap(t_b)=0.953 CU=1.8702 bound=35.5
L= 64 t0=0.0442 g0=2.1024 Imm=0.0442 Imm0=0.2102 |m0|=0.21024 ward=2e-14 (1-|m0|^2)/g0^2=0.216 | t_b=0.0442 1-t_b>=g0^2:False mu_obs=0.065 gamma(mu_obs)=11.812202 gap(t_b)=0.956 CU=2.7080 bound=140.4
L=128 t0=0.0439 g0=2.0955 Imm=0.0439 Imm0=0.2095 |m0|=0.20955 ward=2e-14 (1-|m0|^2)/g0^2=0.218 | t_b=0.0439 1-t_b>=g0^2:False mu_obs=0.048 gamma(mu_obs)=11.886978 gap(t_b)=0.956 CU=3.6888 bound=562.5
L=256 t0=0.0439 g0=2.0953 Imm=0.0439 Imm0=0.2095 |m0|=0.20953 ward=2e-14 (1-|m0|^2)/g0^2=0.218 | t_b=0.0439 1-t_b>=g0^2:False mu_obs=0.040 gamma(mu_obs)=11.888961 gap(t_b)=0.956 CU=4.0068 bound=1548
```
`1-t_b>=g0^2` is the inequality the proof needs (`g0^2 <= g^2 <= 1-t`). **g = 1/64** (reading g, `t_b = t0`): `ward <= 4e-16`, `CU` = 1.0039 for L = 4..128, `gap(t_b)` = 0.306, `mu_obs` at the search cap 5. **g = 1** (reading g0, `t_b = t0`): `ward <= 2e-15`, `CU` = 1.4795, 1.5053, 1.5158, 1.5163, 1.5163 for L = 4..64, `gap` 0.685-0.714, `mu_obs` 0.318 -> 0.288, below `bound = 3 e^(1/(4 mu_obs))` = 6.59-7.14 in every row. **g = 10**: both readings empty (`1-t_b>=g0^2:False`); record only: `CU` = 1.63, 1.56, 1.51, 1.87, 2.71, 3.69, 4.01 for L = 4..256 (increments +36% then +8.6% for the last two doublings), `mu_obs` 0.206 -> 0.040, `gap` 0.686-0.956.
```
$ python3 docs/reports/T2459/num.py far
Theta far field and the identity Theta_xy = t (Theta K)_xy (x != y) that gives the Theta-level far field from the K-level baEMn2ExpHK (K^(2) = W^-d Theta K, EMn2BA_K_two)
g=0.015625 L=32 t_b=0.6937: max_(x!=0)|Theta - t Theta K|=1.1e-16;  (1-t) max_(|x|_inf=r)|Theta_0x| at r=1,2,4,8,12,16: 1:3.81e-04 2:2.10e-07 4:6.35e-14 8:3.40e-17 12:5.40e-17 16:6.80e-17
   W=3e+01: (1/8)(log W)^(3/2)=0.81, r0=1 (L/2=16): (1-t) max_(|x|>=min(r0,L/2)) Theta = 3.81e-04
   W=1e+03: (1/8)(log W)^(3/2)=2.27, r0=3 (L/2=16): (1-t) max_(|x|>=min(r0,L/2)) Theta = 1.15e-10
   W=1e+06: (1/8)(log W)^(3/2)=6.42, r0=7 (L/2=16): (1-t) max_(|x|>=min(r0,L/2)) Theta = 6.80e-17
g=1 L=32 t_b=0.2862: max_(x!=0)|Theta - t Theta K|=2.9e-17;  (1-t) max_(|x|_inf=r)|Theta_0x| at r=1,2,4,8,12,16: 1:9.17e-03 2:8.83e-04 4:3.77e-05 8:1.66e-07 12:1.31e-09 16:4.32e-11
   W=3e+01: (1/8)(log W)^(3/2)=0.81, r0=1 (L/2=16): (1-t) max_(|x|>=min(r0,L/2)) Theta = 9.17e-03
   W=1e+03: (1/8)(log W)^(3/2)=2.27, r0=3 (L/2=16): (1-t) max_(|x|>=min(r0,L/2)) Theta = 1.71e-04
   W=1e+06: (1/8)(log W)^(3/2)=6.42, r0=7 (L/2=16): (1-t) max_(|x|>=min(r0,L/2)) Theta = 6.07e-07
$ python3 docs/reports/T2459/num.py hs
HS inequality |Tr prod_i G_i E_{c_i}| <= prod_i ||E_{c_{i-1}}^{1/2} G_i E_{c_i}^{1/2}||_HS (any matrices), the glue form for k = 6, and the Ward sum, random Hermitian H
max ratio |Tr| / HS-product over 400 x 20 samples: k=3,4: 0.6849; k=6 all legs: 0.5392; k=6 glue form: 0.6660  (all <= 1 required); max |sum_b L2_ab - Im L1_a/eta|(Ward) = 5.3e-15
$ python3 docs/reports/T2459/num.py sums
lattice sums of the E-layer (uniform in L): Sigma(theta, L) = sum_{y in Z_L^3} exp(-theta sqrt|y|_inf) against L = infinity; analytic Lean constants S_d = (1+1536 d^4)^d, C_sq = 5 (1+24576 d^4)^d
theta=0.5: L=16,32,64,128: 1239.12 6106.96 24929.8 79217.1 | Z^3 (k<4e5): 368656
theta=0.25: L=16,32,64,128: 2242.68 14017.9 79299 390788 | Z^3 (k<4e5): 2.3593e+07
theta=0.146: L=16,32,64,128: 2878.31 19915.9 129855 779229 | Z^3 (k<4e5): 5.9471e+08
S_d(d=3) = 1.926e+15, C_sq(d=3) = 3.944e+19  (analytic, ~1e10 above the lattice sums)
$ python3 docs/reports/T2459/num.py consts
deterministic constants introduced by (b) (d=3, Lam=1/dd=10); analytic (Lean-formula) values; observed values are in `flow`, `sums`
kappa=0.5: c=BAct_rate=4.1580e-03 C=BAct_C=1152 A=BAp5s_A=3.070e+11 S=BAp5s_S=2.055e+13 S1=(2/(e c))expC(1,c/2)=5.819e+16 mu=min(c,1/(2 A S1))=2.798e-29  Cc=(3 e^(1/(4mu)))^2 = exp(1.787e+28) (L-independent)  A_UBA=(kappa+1)/kappa=3.00 (not entered)
kappa=0.25: c=BAct_rate=2.0812e-03 C=BAct_C=9216 A=BAp5s_A=7.844e+13 S=BAp5s_S=3.275e+14 S1=(2/(e c))expC(1,c/2)=1.853e+18 mu=min(c,1/(2 A S1))=3.441e-33  Cc=(3 e^(1/(4mu)))^2 = exp(1.453e+32) (L-independent)  A_UBA=(kappa+1)/kappa=5.00 (not entered)
kappa=0.04: c=BAct_rate=3.3328e-04 C=BAct_C=2.25e+06 A=BAp5s_A=1.823e+20 S=BAp5s_S=4.980e+17 S1=(2/(e c))expC(1,c/2)=1.759e+22 mu=min(c,1/(2 A S1))=1.559e-43  Cc=(3 e^(1/(4mu)))^2 = exp(3.207e+42) (L-independent)  A_UBA=(kappa+1)/kappa=26.00 (not entered)
lk constant 2 S_d + 1 = 3.852e+15 (S_d = (1+1536 d^4)^d = 1.926e+15); wG sqrt-sum constant C_sq = 5 (1+24576 d^4)^d = 3.944e+19; sum_(Z^3) e^(-sqrt|y|/2) = 3.7e5 (sums)
lossE2 (Path/LemDecCalE:54) constant 10^12 (1600 d^4)^d = 2.177e+27; its W-dependent factors below are e^(8 (log W)^(3/4)) = e^(8 sqrt(l*)) and polylogs
  W=3e+01: l*=(log W)^(3/2)=6.45; sqrt(l*)=2.54; ball counts 2(2 l*+1)^3 = 5.376e+03, 2(6 l*+1)^3 = 1.253e+05; shifts e^(3 sqrt(l*)) = 2.04e+03, e^(2 sqrt(6 l*)) = 2.54e+05 <= e^(8 sqrt(l*)) = 6.69e+08; thresholds 2l*=12.9, 6l*=38.7
  W=1e+03: l*=(log W)^(3/2)=18.16; sqrt(l*)=4.26; ball counts 2(2 l*+1)^3 = 1.039e+05, 2(6 l*+1)^3 = 2.657e+06; shifts e^(3 sqrt(l*)) = 3.56e+05, e^(2 sqrt(6 l*)) = 1.16e+09 <= e^(8 sqrt(l*)) = 6.37e+14; thresholds 2l*=36.3, 6l*=108.9
  W=1e+06: l*=(log W)^(3/2)=51.35; sqrt(l*)=7.17; ball counts 2(2 l*+1)^3 = 2.230e+06, 2(6 l*+1)^3 = 5.907e+07; shifts e^(3 sqrt(l*)) = 2.17e+09, e^(2 sqrt(6 l*)) = 1.76e+15 <= e^(8 sqrt(l*)) = 7.89e+24; thresholds 2l*=102.7, 6l*=308.1
  W=1e+12: l*=(log W)^(3/2)=145.24; sqrt(l*)=12.05; ball counts 2(2 l*+1)^3 = 4.953e+07, 2(6 l*+1)^3 = 1.328e+09; shifts e^(3 sqrt(l*)) = 5.03e+15, e^(2 sqrt(6 l*)) = 4.38e+25 <= e^(8 sqrt(l*)) = 7.44e+41; thresholds 2l*=290.5, 6l*=871.5
```
`max_(x!=0)|Theta - t Theta K| <= 1.1e-16`: the identity `Theta_xy = t (Theta K)_xy` of `T2459_Theta_far`. `(1-t) Theta` at distance `>= r0 = ceil((1/8)(log W)^(3/2))`: 6.8e-17 (g = 1/64) and 6.07e-07 (g = 1) at W = 1e6; at W = 30 it is 3.81e-04 and 9.17e-03 (the far field is asymptotic in W). `hs`: ratios `|Tr|/(HS product)` <= 0.685 on 400 x 20 random Hermitian samples (all <= 1 required), Ward sum error 5.3e-15. `sums`: the torus sums grow with L toward the finite `Z^3` value (a torus sum is a sub-sum of it), so they are bounded in L. `consts`: the Lean constants (`BAct_rate` `CombesThomas:45`, `BAp5s_A`, `BAp5s_S` `Prop5Short:49, 52`, `expC` `Defs/RadialSum:271`) depend on (d, Lam, kappa) only; `Cc = (3 e^(1/(4 mu)))^2` is huge and L-independent, the observed `CU` above is what the instance needs.
```
$ python3 docs/reports/T2459/num.py shape
T2458 BA shape  forall lam0, STTailtoTailgL' 3 (baFM . lam0)  (check:462): R*(t) = max_R (1-t)^2 e^{sqrt R} (Theta*Theta*f)(R), f = e^{-sqrt|.|}, charge (+,-), s = 0
lam0=g0=0.5350 L=64: ell_g0 = g0/sqrt(1-t) (sz.lam^2 = 1-t); ell_K = sqrt(t D'/(2(1-t))), D' = sum_x K(x) x_1^2 = 0.9860
  t=0.50000 ell_g0=    0.76 ell_K=    0.70 R*=  1.080 (at R=32; torus L/2=32)
  t=0.90000 ell_g0=    1.69 ell_K=    2.11 R*=  1.395 (at R=32; torus L/2=32)
  t=0.99000 ell_g0=    5.35 ell_K=    6.99 R*=  2.898 (at R=32; torus L/2=32)
  t=0.99900 ell_g0=   16.92 ell_K=   22.19 R*=  3.158 (at R=32; torus L/2=32)
  t=0.99999 ell_g0=  169.18 ell_K=  222.03 R*=  3.134 (at R=32; torus L/2=32)
necessary condition N*(t) = max_(|x|_inf <= L/4) (1-t) Theta_t(0,x) e^(sqrt(2|x|_inf)/2) <= sqrt(C_c)  (test A = tau^2 delta_(0,0), a2 = -a1), g0=0.5350, L=128:
  t=0.5000 ell_g0=   0.76 ell_K=   0.70 N*=0.6323
  t=0.9000 ell_g0=   1.69 ell_K=   2.11 N*=0.1637
  t=0.9900 ell_g0=   5.35 ell_K=   6.99 N*=0.01785
  t=0.9990 ell_g0=  16.92 ell_K=  22.19 N*=0.001813
  t=0.9999 ell_g0=  53.50 ell_K=  70.21 N*=0.0001822
baFMz-consistent (g0 = sqrt(t0) g <= sz.lam = g, t = t_b): g=0.015625 ell_g0 = g0/sqrt(1-t_b) = 0.024 ell_K = 0.020 R* = 1.0010
$ python3 docs/reports/T2459/num.py gron
H249 (3): one-slot route; C_ell(u) = (1-u) sum_x Theta_u(0,x) e^{sqrt|x|_inf}; Gronwall loss ((1-s)/(1-t))^(C_ell - 1) at s = 0 (proxy: M of the flow g = 1/64, Theta_u at 1-u >= g^2)
  1-u=5.000e-01: (1-u) row sum = 1.000000  C_ell=1.001742  loss (1/(1-u))^(C_ell-1) = 1.001
  1-u=1.000e-01: (1-u) row sum = 1.000000  C_ell=1.015548  loss (1/(1-u))^(C_ell-1) = 1.036
  1-u=1.000e-02: (1-u) row sum = 1.000000  C_ell=1.156905  loss (1/(1-u))^(C_ell-1) = 2.06
  1-u=1.000e-03: (1-u) row sum = 1.000000  C_ell=1.956138  loss (1/(1-u))^(C_ell-1) = 738.6
  1-u=2.441e-04: (1-u) row sum = 1.000000  C_ell=3.135762  loss (1/(1-u))^(C_ell-1) = 5.19e+07
  Gronwall: Y_t <= Y_s ((1-s)/(1-t))^(C_ell-1) with Y = (1-u) sup|Z|; a loss > W^eps0 at 1-t = lam^2 is a lost bootstrap (closure needs loss 1)
$ python3 docs/reports/T2459/num.py cont
continuum (Yukawa) estimate for the shape: necessary condition from A = tau^2 delta_(0,0): ((1-t) Theta_t(0,x))^2 <= C_c exp(-sqrt(2|x|_inf)); Yukawa (1-t) Theta ~ e^{-|x|/ell}/(4 pi ell^2 |x|)
with Lambda(ell) := max_R log[Yukawa(R)/e^{-sqrt(2R)/2}] (x along an axis, |x|_inf = |x|_2 = R) the condition fails iff Lambda(ell) > (1/2) log C_c
  ell=  20: Lambda(ell) =    -7.87 at R=1 (torus needs L >= 4)
  ell=  50: Lambda(ell) =    -9.65 at R=200 (torus needs L >= 800)
  ell= 100: Lambda(ell) =    -6.28 at R=1040 (torus needs L >= 4162)
  ell= 150: Lambda(ell) =    -1.69 at R=2504 (torus needs L >= 10014)
  ell= 200: Lambda(ell) =     3.40 at R=4591 (torus needs L >= 18365)
  ell= 300: Lambda(ell) =    14.26 at R=10642 (torus needs L >= 42567)
  ell= 500: Lambda(ell) =    37.21 at R=30242 (torus needs L >= 120969)
  log C_c =     0: Lambda(ell) > (1/2) log C_c  iff  ell > 167.0   (4 log C_c = 0)
  log C_c =    10: Lambda(ell) > (1/2) log C_c  iff  ell > 215.2   (4 log C_c = 40)
  log C_c =   100: Lambda(ell) > (1/2) log C_c  iff  ell > 608.7   (4 log C_c = 400)
  log C_c =  1000: Lambda(ell) > (1/2) log C_c  iff  ell > 4271.1   (4 log C_c = 4000)
lattice vs Yukawa at g = 1 (flow data of num.py flow), L = 128, ratio (1-t) Theta_t(r e_1) / Yukawa(r; ell_K), ell_K from the measured D':
  t=0.99: ell_K = 6.99 (D' = 0.9860); r=2: 0.957  r=4: 0.916  r=8: 0.931  r=16: 0.952  r=32: 0.975
  t=0.999: ell_K = 22.19 (D' = 0.9860); r=2: 0.986  r=4: 0.958  r=8: 0.975  r=16: 0.990  r=32: 1.007
```

## (b) The argument (U5-0 ... U5-5)
Notation: `tau_u = (W^d (1-u))^-1`, `lambda = l* = (log W)^(3/2)`, `T_u(r) = tau_u^2 e^(-sqrt r) + W^-D` (`tailTD`, `Defs/Tail.lean:173`; `STtailTD`, `Step5Pins:151`), `r = |a0-a1|_inf`, `g = sz.lam`, `g0 = BAflowLam0` (`FlowPins:386`), `K = BAK` (`KKernel:48`). Case (iii) is `g^2 <= 1-u`: then `ell_u = 1` (`ellT` `Defs/Params:32`) and `Bctl_u = W^-d Bparam` (`Defs/Sizes:214`, `Defs/Params:36`) is `W^-d [(g^2 + 1-u)^-1 + (L^d (1-u))^-1]`, between `tau_u/2` and `2 tau_u`.

### U5-0 Inventory (band case-(iii) stack, 11 files; `inventory.sh`)
```
$ bash docs/reports/T2459/inventory.sh
file                          lines |   (i)  (ii) (iii)  (iv)   (v)
Induction/TailtoTail            628 |     1     0     0    40     7
Induction/TailtoTailSq         1043 |     2     0     0    52    18
Induction/LemDecCalELip        1365 |     3     0    42    20    49
Induction/LemDecCalEPrec       1704 |     2    36     5    18    65
Induction/PfStep5              2581 |     0    12     3    12    44
Induction/PfStep5Alg            785 |     4    11     0     0    50
Induction/PfStep5Grid          1292 |     1     0    15    12    69
Path/LemDecCalE                1477 |     3    46    22     9    42
Path/LemDecCalEdif             1643 |     2    32     1     8    25
Path/LemDecCalEdif2            1035 |     0    16     6     0     0
Path/LemDecCalEwG              2510 |     1    36    13     8    19
total lines: 16063
--- global counts at this checkout (drafting values in the ticket: ‖m‖=1/norm_mE 4, |E|<2 23, mE 34, SB d 81, gexRHS 30, Theta d 117)
‖m‖ = 1|norm_mE    4
\|E\| < 2              17
\|E\| (<|≤) 2        59
mE                     34
SB d                   81
gexRHS                 30
Theta d                117
```
The ticket's drafting count 23 for `|E| < 2` is not reproduced (17 for the literal spelling, 59 for `<` or `≤`); the others agree. Classes and the BA replacement (new BA lines, estimate): **(i) `|m| = 1`**: `STTailtoTail` (`Step5Pins:121-136`, `TailtoTail:459`), `PfStep5Alg:183, 224`, `norm_mSigma` (`LemDecCalE:1008, 1368`), `Lip:332-358`. BA has no `|m| = 1`: `K_aa = |m|^2` (`BAK_diag` `KKernel:120`), `Sum_b K_ab = 1` (`:124`), `Sum_{b!=a} K_ab = 1-|m|^2` (`:133`), and the weighted row sum of U5-1. **(ii) `M = mI` premises**: (P-e6), (P-e7/8) of `E2Hyp` (`LemDecCalE:69-95`), used in e6-e9 (`:976-1200`), `avg_le_hyp` (`EwG:1301-1390`), `far_pt` (`:1398`), `dif` (`LemDecCalEdif:571, 577, 682`), the good event (`LemDecCalEPrec:670`), `GijGEXPTSwap` (`Green/Pins:283`). BA: not needed (U5-2). **(iii) `S = SB d`**: `lemDecCalE_SB_support` (`LemDecCalE:770`), `9^d` counts; BA `S = 1` (`FlowPins:327`), single sums; the model-free lattice lemmas `LemDecCalE_sum_tail_tail` (`:395`), `LemDecCalE_e10a` (`:186`), `LemDecCalEwG_sum_sqrt_tail` (`EwG:318`) are imported. **(iv) explicit `Theta d`**: `TailtoTail*`, `lemDecCalEPrec_kell` (`LemDecCalEPrec:979`), (H3) of `tailtoTailSq_kernelGen` (`TailtoTailSq:906`). BA: `BATheta`; far field `T2459_Theta_far` (probe :242) from `baEMn2ExpHK` (`EMn2BA:637`). **(v) `|E| < 2`, `STflowE`, `lemT`, `mE`**: BA has `kappa <= Im m` (`BAReal` `MFixedPoint:432`, `BAflow_real` `GreenSchur:59`), `BAflowT0 < 1` (`EMn2BA:106`), `C.eta`.
Fate per file: `TailtoTail` rewritten (U5a, 350 lines); `TailtoTailSq` rewritten (U5a, 500); `LemDecCalELip` only the `J#` part (U5c, 150); `LemDecCalEPrec` good event rewritten with (vi) (U5c, 650); `PfStep5` rewritten (U5d, 1,500); `PfStep5Alg` `riemann`, `closure`, `tailAnti` imported, `ugenSum'` rewritten (U5d, 250); `PfStep5Grid` `level` imported (`:71`), Duhamel = merged `StoppedDuhamelNg` (U5d, 300); `LemDecCalE` lattice lemmas imported, `lk` rewritten (U5b, 150); `LemDecCalEdif` rewritten with HS (U5b, 1,000); `LemDecCalEdif2` replaced by the glue form (inside U5b); `LemDecCalEwG` rewritten (U5b, 600). Sum 5,450 lines; rows (d) add the HS lemmas, the sum `S_theta`, `T2459_Theta_far`, the semigroup instance, the list-loop bridge, the targets and the instances.

### U5-1 The kernel (the `|m| = 1` question of §266 (4))
Carrier `baFM sz lam0 E`, kernel `Step2Gen_UN = BAUN` (`Step2Kern_UN_BA` `Step2Kern:124`), `U_{s,t} = (1-sK)(1-tK)^-1 = (s/t) I + (1-s/t) Theta_t` (`BAuKer_convex` `EKPins:79`, for `t > 0`). Facts: **(K1)** `K` is doubly stochastic with `K_aa = |m|^2` (above); **(K2)** `|M^(s,s')_ab| = K_ab` for the four charge pairs (`BAMss_norm_eq_BAK` `KKernel:102`), so `|Theta^(s,s')| <= Theta`, `|U^(s,s')| <= U`; **(K3)** `K_ab <= A g0^2 e^(-2c|a-b|_1)` for `0 < g0 <= Lam` (`BAK_off_le` `KKernel:198`; `A = BAp5s_A`, `c = BAct_rate`).
1. *Weighted row sum* (pin `T2459_BAweighted`, probe :69). `gamma(mu) = max_a Sum_b K_ab e^(mu|a-b|_1) = 1 + Sum_{b!=a} K_ab (e^(mu|a-b|) - 1) <= 1 + mu A g0^2 S1` (`e^x-1 <= x e^x`, `r e^(-cr/2) <= 2/(ec)`, `BAsum_exp_decay_le` `Prop5Short:251`; `S1 = (2/(ec)) expC(1, c/2)`). With `mu = min(c, 1/(2 A S1))` and `g0^2 <= g^2 <= 1-t`: `t gamma <= t + (1-t)/2 = (1+t)/2`. This is the only use of the regime, through `g0 <= g` (`T2459_lam0_le_lam` :58) and `g^2 <= 1-t` (UBA-C1: size level at `g`, kernel fact at `g0`).
2. `e^(mu|a-c|) <= e^(mu|a-b|) e^(mu|b-c|)` gives `Sum_b Theta_ab e^(mu|a-b|) <= Sum_k (t gamma)^k <= 2/(1-t)`; with `(t-s)/t <= 1-s` and `s/t <= 1`: `Sum_b |U_ab| e^(mu|a-b|_1) <= 3 rho`, `rho = (1-s)/(1-t) >= 1`, for all four charge pairs.
3. *TailtoTail* (pin `T2459_BAKernel` :78). `sqrt|x|_inf <= mu|x|_1 + 1/(4mu)` (AM-GM) and `sqrt|a1-a2| <= sqrt|b1-b2| + sqrt|a1-b1| + sqrt|a2-b2|` (triangle, `sqrt` subadditive) give `Sum_b |U_{a1 b1}||U_{a2 b2}| e^(-sqrt|b1-b2|) <= e^(-sqrt|a1-a2|) prod_i Sum_b |U_{a_i b}| e^(sqrt|a_i-b|) <= (3 e^(1/(4mu)) rho)^2 e^(-sqrt|a1-a2|)`; `tau_s rho = tau_t` and the floor `rho^2 W^-D` give U6's `STTailtoTailConclgL` (`Step5Gen:169`) with `Cc = (3 e^(1/(4mu)))^2`. `T2459_kernel_at_flow` (:84, proved) states it at `baFMz`; instance :357. Observed `CU` 1.0039 / 1.5163 against bound 3.15 / 7.14 (a).
4. *Martingale kernel* (`tailtoTailSq_kernelGen` `TailtoTailSq:906`, (H1)-(H3)) at `Step2Gen_UN`: (H1) is the dif bound of U5-2 (near cut 2 l*); (H2) `|STeeM| <= N^C` from `|G| <= eta^-1`, `eta_u = (1-u) Im m >= kappa lam^2 >= 1/(16N)` eventually (`difRep2_norm_STeeM_le_N` `DifREP2:1277`, restated, <= 80 lines); (H3) the Theta-level far field: for `x != x'`, `Theta_xx' = t (Theta M)_xx'` (`BATheta_resolvent` `KBase:330`) and `K^(2) = W^-d (Theta M)` (`EMn2BA_K_two` `EMn2BA:624`), so `baEMn2ExpHK` (`:637`, delta = 1, level D + d) gives `|Theta_xx'| <= W^-D` beyond `ell*_t` (theorem `T2459_Theta_far`, :242, instance :384).
Constants `mu`, `Cc` depend on (d, Lam = dd^-1, kappa) only (values in (a)).
**The shape `forall lam0, STTailtoTailgL' 3 (baFM . lam0)`** (T2458-check:462; primed pin `Step5Gen:178`): not a target; at `baFMz` (`lam0 <= sz.lam`) it is `T2459_BAKernel`. At a free `lam0` it is expected FALSE (a sketch, not a proof). Quantifier order: `forall lam0, ..., exists Cc, forall sz n E D s t`, so `Cc` may depend on `lam0`, `kappa`, not on `sz`. Test `A_b = tau_0^2 1(b = (0,0))` (allowed, `T_{0,D}(0) >= tau_0^2`), `a2 = -a1`, `s = 0`, charges `(+,-)` (then `U = Theta_t`, `K^(+-) = K`); `W -> infinity` at fixed `L, lam0, t` forces `((1-t) Theta_t(0,x))^2 <= Cc e^(-sqrt(2|x|_inf))` for all `x`. Take `sz.lam n^2 = 1-t` with `lam0 n` fixed and `sz.lam n -> 0`: the length `ell_K = sqrt(t D'/(2(1-t)))` (`D'` = per-axis second moment of `K`, 0.9860 at g = 1, `shape`) is unbounded; along an axis `(1-t) Theta_t(0, R e_1) ~ e^(-R/ell)/(4 pi ell^2 R)` (checked on the lattice, g = 1, L = 128: ratio 0.916-1.007, `cont`), and `Lambda(ell) = max_R log[Yukawa/e^(-sqrt(2R)/2)] = ell/8 - log(4 pi ell^2 R*) + O(1)`, `R* = ell^2/8`; the condition fails once `Lambda(ell) > (1/2) log Cc` (`ell > 167` for `Cc = 1`, `> 609` for `e^100`, `> 4271` for `e^1000`; about `4 log Cc`). The violation needs `L >= 4R* = O(ell^2)` (>= 18,365 at `ell = 200`), out of FFT reach (`L <= 256`); at `L <= 128` the lattice `R*`, `N*` stay O(1) (`shape`). So: false for every fixed `Cc` by continuum asymptotics, undecided by lattice numerics; a note for U6's report (§267 (4)); U5 does not read it.

### U5-2 The ℰ-bounds (`lem_dec_calE` at BA, `3_5:2314-2338`)
Premise bundle (probe `T2459_BAscalar` :107, `T2459_BAmatrix` :116): the scalar part of `E2Hyp` without (P-e6), (P-e7/8), `|E| < 2`; the matrix part is the loop-level content of one good event: (i) stopped control `|(L-K)^(2)| <= J T_{u,D}` (four charge patterns), (ii) `|K^(2)_{(+-)}| <= K0 tau_u`, (iii) the K-level far field at `l*` (`baEMn2ExpHK`), (iv) `|L^(1) - m| <= Lam tau_u` (`STAvgUgL`, a conjunct of `STStep2ConclgL`, `Step2Gen:514`), (v) `|L^(k)| <= Lam tau_u^(k-1)`, k = 2, 3, 4, 6 (`STLmaxU`), (vi) the `J`-free long-leg decay `|(L-K)^(2)| <= W^(theta d (Cd+1)) Lam tau_u^2 e^(-theta sqrt r) + W^-D` (below). Sources: `H` Hermitian = `BAAuxGraph2_seqHflowBA_herm` (`Graph/BAAuxGraph2:448`, merged); (i) is the definition of `J#`; (ii) `STKboundgL` (`Carrier:147`); (iii) `baEMn2ExpHK`; (iv), (v) are Steps 2-4 premises of `STIngR5gL` (pins `T2459_LmaxU`, `T2459_LKU`); (vi) is derived from `STLKU` (k = 2) and `STGdecayWgL` (a conjunct of `STStep2ConclgL`); the probability bookkeeping is `T2459_BAgoodThm`. `BAGbEXPii` (`Step1Boot:108`), `BAGbEXPij'` (`GreenCore:1644`), `BAGbEXPav` (`baGbEXPav_holds` `GbEXPav:24`) are not read; of the premises of `STIngR5gL` the entry-level conjuncts (`STLocalEntryUgL`, `STDecaygL`, `STDecayStronggL`) are not read, the loop-level `STGdecayWgL` is.
*(vi), why it is needed.* A `J^2` on the indicator term of `dif` would make the quadratic variation `~ J^2 (1-u)^-1 T^2`, the martingale `~ J sqrt(loss) log W`, and the bootstrap `J < W^(eps0)` would not close. The `dif` configuration `r <= 6 lambda`, `c` far has two short legs and four long legs; the long legs carry `J` if bounded by the stopped control, so they are bounded by Steps 2 and 4 instead: `STLKU` (k = 2): `|(L-K)^(2)| <= A1 = Lam tau^2`; `STGdecayWgL` (Eq:Gdecay_w, `ell_u = 1`, `Bctl <= 2 tau`): `|(L-K)^(2)| <= A2 e^(-sqrt r) + W^-D`, `A2 = rho_s^Cd (2 tau)^(6/5)`, `rho_s = (1-s)/(1-u) <= lam^-2 <= W^d`. Interpolation (`0 < theta < 1`; for `theta >= 1` the claim would be false) `min(A1, A2 e^(-sqrt r)) <= A1^(1-theta) A2^theta e^(-theta sqrt r)` gives `Lam tau^2 (tau^(-4/5) rho_s^Cd)^theta e^(-theta sqrt r) <= W^(theta d (Cd+1)) Lam tau^2 e^(-theta sqrt r)` (`tau >= W^-d`): this is (vi), a fixed small power of `W` (`theta` arbitrary) and a slower decay rate; the floors are absorbed by `D` large.
*Why no entry-level input.* **(O1) Hilbert-Schmidt.** `E_a = W^-d 1_[a]` (`Eblk`, `Loop/GLoop:55`) and `L^(k)_{sigma,a} = tr prod_i G(sigma_i) E_{a_i}` (`loopM`, `Loop/GLoopFlow:92`). With `X_i = E_{c_{i-1}}^(1/2) G(s_i) E_{c_i}^(1/2)`: `L^(k) = tr(X_1...X_k)` (cyclicity, `E^(1/2)E^(1/2) = E`), `|tr(X_1...X_k)| <= prod ||X_i||_F` (`T2459_trace_mul_le`, `T2459_trace_mul3_le`, probe :299, proved; `Matrix.frobenius_norm_mul`) and `||X_i||_F^2 = tr[E G E' G*] = L^(2)_{(s,-s),(c,c')} =: Gamma` (H Hermitian, no `W` factors): every loop is bounded by two-loops, which the stopped control and the `K` bounds control: `Gamma_ab <= |K^(2)_ab| + J T_u(|a-b|)`, `|K^(2)| <= K0 tau` always, `<= W^-D` beyond `l*`; where a `J`-free bound is needed, (vi) replaces the stopped control. **(O2)** The non-scalar `M` enters only through `K^(2)` (order `tau`, not `g0`): the main risk of the ticket does not arise; `BAMB_row_l1`, `BAMB_ward_row` are not used. **(O3)** `BAGbEXPij'` has a deterministic `Phi` and `1_Omega L ≺ Phi^2` at a fixed time; under the stopped control it would assume the claim. All inputs above are deterministic inequalities on one event (`T2459_BAgood` :186).
Pin `T2459_BAEdet` (:134), loss `lossE2wG` (`EwG:74`), `tau = tau_u`, `lambda = l*`, `S = 1`:
- `lk`: `|E^{LK x LK}| <= W^d J^2 Sum_x T(|x-a1|) T(|a0-x|) <= (2S_d+1) J^2 (1-u)^-1 tau T(r)` by `LemDecCalE_sum_tail_tail` (amplitude `A = tau^2`, `W^d tau^2 = tau/(1-u)`; floor `W^-D L^d <= tau^2`).
- `wG` (`STEGtMg`, `Step2Gen:368`): `|E^G~| <= (Lam/(1-u)) Sigma_3`, `Sigma_3 = Sum_x (|L^(3)_{(x,a0,a1)}| + |L^(3)_{(a0,x,a1)}|)`. Ball `B` of radius `lambda` about `a0`, `a1` (`#B <= 2(2 lambda+1)^d`, `LemDecCalE_e10a`). *r <= 2 lambda*: on `B`, `LmaxU(3)`: `<= 2 Lam #B e^(sqrt(2 lambda)) T(r)`; off `B`, HS with `Gamma_{a0a1} <= Lam tau` (`LmaxU(2)`) and two long legs `Gamma <= 2 J T`: `<= sqrt(Lam tau) 2J C_sq tau sqrt(T(r)) <= ... e^(sqrt(lambda/2)) T(r)` (`EwG_sum_sqrt_tail`, floor `W^-D L^(2d) <= tau^2`). *r > 2 lambda*: on `B` one short leg and two long (`|x-a1| >= r-lambda`, `T(r-lambda) <= e^(sqrt lambda) T(r)`): `<= #B sqrt(Lam tau) 2J e^(sqrt(lambda)/2) T(r)`; off `B` three long legs: `(2J)^(3/2) C_sq tau T(r)`. Total `<= loss [1(r <= 2 lambda) + tau^(1/2) J^(3/2)] (1-u)^-1 T(r)`; the indicator term is `J`-free (`LmaxU(3)`), every `J` comes with `tau^(1/2)`.
- `dif` (`STeeMg`, `Step2Gen:960`; `S = 1` makes the cut points coincide; `STeeLoop` `Step34Pins:152`): the six-loop has blocks `(a0, a1, c, a1', a0', c)`, legs `(a0,a1), (a1,c), (c,a1'), (a1',a0'), (a0',c), (c,a0)`. *r <= 6 lambda*: (A) `c` within `3 lambda` of `a0` or `a1`: `LmaxU(6)`, count `2(6 lambda+1)^d`, `T(r)^2 >= tau^4 e^(-2 sqrt(6 lambda))`, `J`-free; (B) `c` farther: two short legs `(a0,a1)`, `(a1',a0')`, `Gamma <= Lam tau` (`LmaxU(2)`), four long legs (distance `>= lambda`, `K^(2)` negligible) with (vi): `|L^(6)| <= Lam tau prod_4 sqrt(W^(theta d (Cd+1)) Lam tau^2 e^(-theta sqrt(.)))`, `W^d Sum_c <= (1-u)^-1 Lam^3 W^(2 theta d (Cd+1)) S_theta tau^4`, `S_theta = Sum_y e^(-(theta/2) sqrt|y|)`: the factor in the pin (probe :134), `J`-free. *r > 6 lambda*, `c` within `3 lambda` of `a0` (or `a1`): glue the two legs at `c`, `|Tr| <= ||Y||_F ||X||_F`, `||Y||_F^2 = L^(4)_{(a0',c,a0,c)} <= Lam tau^3` (`LmaxU(4)`), `||X||_F <= prod` of the four other legs, each long (`>= lambda`), `<= (2J)^2 e^(3 sqrt lambda) T(r)^2`; times `W^d` and the count: `(1-u)^-1 tau^(1/2) (...) T^2`. `c` outside both balls: six long legs, `(2J)^3 (2S_d+1) tau^2 W^d T(r)^2 = (1-u)^-1 tau (...) T^2`. The `tau^(1/2)` is the glue's `sqrt(tau^3)`. Every `J`-dependent term has a factor `tau^(1/2)`; the indicator term is `J`-free.
- *Thresholds (T2459b).* The far field is proved at `l*` (`emn2ExpHK`, delta = 1), not `l*/8` (band `E2Hyp`): indicators at `2 l*` (wG) and `6 l*` (dif), near cut `2 l*` for `|a_i - a_i'|`. The band closure uses the indicators only as `<= 1` (`PfStep5:1134, 1143`), so the thresholds change constants only. The pin reuses the band loss `lossE2wG` as a budget: its constant `10^12 (1600 d^4)^d = 2.2e27` (`consts`) exceeds each structural constant (`C_sq` 3.9e19, `2S_d+1` 3.9e15, products with the counts and the shifts `<= e^(5 sqrt lambda)` are absorbed by its polylog and `e^(8 (log W)^(3/4))` factors: design-level count); a primed loss is the fallback. The new lattice sum `S_theta` (rate `theta/2`, no merged lemma: the merged ones are `LemDecCalE_sum_zd_le` at `1/2`, `1/4`) is a U5b item (~60 lines).
- *Where `S = 1` simplifies* (`Step2Gen:368-403`): `STELKLKMg`, `STEGtMg` are single sums over `x`, no `SB` support lemma, no `9^d`; `STeeMg`, `STEEkMg` have `c = c'`, which allows the glue at `c`.
- *Far-field route:* the K-level `baEMn2ExpHK` (merged), not `BAKellStarEv`: no new row (P5 of T2452 D5, 90/100/160 lines, is dropped), both mixed charges are covered, the Theta-level fact follows (`T2459_Theta_far`), and `EMn2BA_arith` stays private. Uniformity in `u in [0, t_n]` follows from the sequence form (take `u_n` a violator).

### U5-3 `lem:pf_step5` at BA (`3_5:2364-2383`)
- *Stopping time* `(eq:def_TTT)`: on the grid `u_k` (`K >= N^(max(C_K, C_R))`, `PfStep5:34`) it is the strong induction `J#(u_k, D_{u_k}) < W^(eps0)` of `T2459_BAWalkConcl` (:199; `T2459_BAJsharp` :170), level `D_u = D* + 2 log_W (1-u)` (`PfStep5Grid_level` `PfStep5Grid:71`), `eps0 < eps1 = min(dd/8, 1/4)`; good event `T2459_BAgood` (:186) at each grid time; probability bookkeeping as `lemDecCalEPrec_prob`, transfer `pathP` to `seqP` by the `Hpath` field of `baStep2Mat` (`Step2BA:70`, `baStep2Mat_Hpath` `:94`).
- *Stopped hierarchy on a grid:* `StoppedDuhamelNg` (`GridDuhamelGen:243`, merged), hypothesis `Step2Gen_USemigroup` from `BAuKerSemigroup_holds` (`TwistGrid:199`, ~30 lines in U5d). For m = 2 the sum over `l = 3..m` of `STgDriftNg` is empty: the drift is `Theta^(2) o (L-K) + E^{LK x LK} + E^{G~}`; the list-loop to pair-loop bridge (`STelklkMg` at `KLloopOf` vs `STELKLKMg`, ~120 lines) is in U5d.
- *Martingale:* clause 4 of `STGridRepNAtgL 3 2` at `baStep2Mat` (`Step2Gen:994`; pin `T2459_P1` :209, T2460 target 4): `Step2Gen_UN` on both slots with quadratic variation `STeeUMg` (`Step2Gen:983`), bounded by the BA `tailtoTailSq` (U5-1 step 4) and Riemann sums.
- *QV and flow bounds with `C.eta`:* `difRep_flow_bounds` (`DifREP1:600`, read at `PfStep5:2112`) and `difRep2_norm_STeeM_le_N` (`DifREP2:1277`, read at `PfStep5:1714`), restated (<= 80 lines each, U5d); `lossE2wG` reused by name.
- *Closure inequality* (Duhamel from `s`, one kernel per term, no compounding; `|U_{v,u} o A| <= Cc T_u + rho^2 W^-D` for `|A| <= T_v`): on `{J#(v) < W^(eps0), v < u}`, `J#(u) <= Cc [J#(s) + loss (J^2 tau_u + d log W + 2 tau_u^(1/2) J^(3/2))] + M(u)`, using `Int (1-v)^-1 tau_v dv <= tau_u`, `Int (1-v)^-1 dv <= d log W` (`1-u >= lam^2 >= W^(-d+2dd)`) and `Int (1-v)^-1 tau_v^(1/2) dv <= 2 tau_u^(1/2)`; `tau_u <= W^(-2dd)` (`lam^2 W^d >= W^(2dd)`); the martingale `M(u) <= C sqrt(log W) sqrt(loss W^(2 theta d (Cd+1)) S_theta (d log W + tau_u^(1/2) J^3))` w.h.p. (clause 4, `tailtoTailSq`). The loss is `lossE2wG` at `Lam = K0 = N^(tau')`, a power `W^(o(1) + 8 tau'/cB)` (`cB` the bandwidth exponent, `Sizes.Bandwidth` `Defs/Sizes:168`); `theta` is chosen after `eps0` so that `W^(2 theta d (Cd+1)) < W^(eps0/4)`, hence the right side is `< W^(eps0)`.
- *Closure:* `pfStep5Alg_closure` (`PfStep5Alg:447`, sizes only) with `C_tot` the sum of the BA constants (kernel `Cc`, E-layer loss, QV) and `tau > 0` after it; exponents in (a): `J^2 tau`, `tau^(1/2) J^(3/2)`, `tau^(1/2) J^3`, martingale `sqrt(log W) J^(3/2) tau^(1/4)` all negative at eps0 = 0.01. `pfStep5Alg_riemann` (`:343`) is model-free and imported. Band parameters (`PfStep5:34`): `D* = max(D, D0) + 2d + 1`, `D0 = 2/c + 12 d`.
- *Lift* `PrecPT -> Prec` and descent `D_u >= D` (pin `T2459_BAfromWalk` :218): the floor `T >= W^-D` and the Lipschitz constant of `u -> L^(2)_u(H)` (`|G| <= eta^-1`, `eta >= kappa lam^2`) give a net of `N^C'` points (~300 lines, U5d).
**H249 (3): can BA case (iii) use TL's one-slot clause (iv) (`twU`, `TwistGrid:105`) instead of the two-slot clause 4? No.** (1) In the twisted hierarchy the second slot is not a kernel: `Theta^(2)` appears as the source `twB1M` (`TwistGrid:90`), linear in the unknown with weight `(1-u)^-1`; closing it is a Gronwall `Y_t <= Y_s ((1-s)/(1-t))^(C_ell - 1)`, `C_ell = (1-u) Sum_x Theta_u(0,x) e^(sqrt|x|)`, which is the lossy Step 2 conclusion, not the loss-free Step 5 one: `gron` (a proxy, not a proof of impossibility): loss 1.001 at `1-u = 1/2`, 5.19e7 at `1-u = lam^2 = 2.4e-4`. Two slots as a kernel give the constant `Cc` (U5-1). (2) Clause (iv) has one frozen twist; the two-slot weighted sum superposes twists `c = b2` and its QV has cross terms between twists that (iv) does not control; the triangle in slot 2 costs `rho^(1/2)`, `rho <= Bctl^(-c_d)` a fixed power of `W` (`STConStInd`), while the closure needs `W^(eps0)` with `eps0` arbitrarily small. These are argument sketches, not machine-checked; the summation-by-parts outline of section (a)(i) of the prove report has the same unchecked step (the cross-twist quadratic variation). So T2460 target 4 stays.

### U5-4 Targets
`T2459_STPfStep5BA`, `T2459_STStep5IIIBA` (probe :35) are U6's `STPfStep5gL` (`Step5Gen:252`), `STStep5IIIgL` (`:228`) at `(seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`. `STStep5IIIgL` follows from `STPfStep5gL` through U4s1's generic successor of `ST_step5_caseIII_of_pf` (`Step5Cases:311`; band proof reads sizes only): U4s1 is T2462 (released H251, target 4 `T2462_caseIII`, `docs/tickets/checks/T2462-check.lean:225`). Pin `T2459_caseIII_succ` (:47, verbatim copy); its premise `T2462_FlowFacts` (copy `T2459u4_FlowFacts` :39) holds at BA by merged names (`T2459_flowFacts_BA` :52, proved): **one line in U5's 1b** (instance :342).

### U5-5 Constants (C1)
Every constant depends on (d, Lam = dd^-1, kappa), the closure also on (eps, dd).
| step | uniform facts used (file:line) | constants | the A of UBA-C1 |
|---|---|---|---|
| kernel K1-K2 | `BAK_row_sum` `KKernel:124`, `BAK_diag` `:120`, `BAK_offdiag_sum` `:133`, `BAMss_norm_eq_BAK` `:102`, `BAuKer_convex` `EKPins:79` | none | no |
| weighted sum | `BAK_off_le` `:198`, `BAct_rate` `CombesThomas:45`, `BAp5s_A/S` `Prop5Short:49, 52`, `BAsum_exp_decay_le` `:251`, `BAflow_lam0_window` `GreenSchur:72`, `BAflow_real` `:59` | `mu = min(c, 1/(2 A S1))` | no: reads `g0 <= g` only |
| TailtoTail | steps 2-3 | `Cc = (3 e^(1/(4mu)))^2` | no |
| Theta far field | `BATheta_resolvent` `KBase:330`, `EMn2BA_K_two` `EMn2BA:624`, `baEMn2ExpHK` `:637` | none new | no |
| lk, wG, dif | HS (probe :299), `LemDecCalE_sum_tail_tail` `:395`, `EwG_sum_sqrt_tail` `:318`, `STLmaxU`, `STKboundgL`, `STLKU`, `STGdecayWgL` | `S_d`, `C_sq`, counts, shifts, `S_theta` (`consts`) | no |
| walk, closure | `StoppedDuhamelNg`, clause 4, `pfStep5Alg_closure` | `C_tot`, `tau` | no |
| regime | `TwistStep2_lam0_sq` `TwistStep2:740` | first conjunct only | **not entered** |
Forbidden facts (C1): none used. `grep -cE 'BAK_le_small|BAMB_upper_small|BAGbEXPij[^'"'"']|Mbound_AO|W\^\(-eps|BAm_im_lower_window' RBM3D/Probe/T2459Pins.lean` is 0 (no `g <= W^-eps`, no smallness of `‖M - m0 I‖`, no `(C lam)^|a-b|`, no `BAm_im_lower_window`). The Lean constants are far above the observed ones (`consts`, `flow big`): `Cc` is `exp(1.8e28)` at kappa = 1/2 against `CU` 1.0039.

## (c) Probe pins and the U6 re-check (U5-7)
Probe `RBM3D/Probe/T2459Pins.lean`, 394 lines, exit 0, no output. U6 is merged (1debc23), so its statements are used by name (ticket `Sibling scan`, U6 coupling), not copied under `T2459u6_`; the re-check below replaces the copy table. Acceptance script:
```
$ bash docs/reports/T2459/probe_check.sh
lines:      394
lake env lean RBM3D/Probe/T2459Pins.lean: exit=0, output lines=       0
lake build RBM3D.Probe.T2459Pins: exit=0, last line: Build completed successfully (4065 jobs)., warning/error lines in the probe file: 0
forbidden (sorry|admit|axiom|native_decide|inductive|structure): 0
defs/abbrevs: 26, theorems: 11, examples: 9
T2459_flowFacts_BA: [propext, Classical.choice, Quot.sound]
T2459_lam0_le_lam: [propext, Classical.choice, Quot.sound]
T2459_kernel_at_flow: [propext, Classical.choice, Quot.sound]
T2459_sz0_lam_le: [propext, Classical.choice, Quot.sound]
T2459_scalar_sz0: [propext, Classical.choice, Quot.sound]
T2459_main_of_parts: [propext, Classical.choice, Quot.sound]
T2459_Theta_far: [propext, Classical.choice, Quot.sound]
T2459_trace_mul_le: [propext, Classical.choice, Quot.sound]
T2459_trace_mul3_le: [propext, Classical.choice, Quot.sound]
T2459_reg_sz0: [propext, Classical.choice, Quot.sound]
T2459_inst_IngR5: [propext, Classical.choice, Quot.sound]
--- name clash: declarations named T2459_* / T2459u4_* / T2459u6_* on main and on the sibling branches that exist (absent = no such branch)
main:0 t/T2450:0 t/T2452:0 t/T2454:0 t/T2455:0 t/T2456:0 t/T2457:0 t/T2458:0 t/T2460:0 t/T2461:0 t/T2462:0 t/T2463:absent 
references to T2459Pins or BA/Step5III on main: 0
```
| ticket item | probe | instance |
|---|---|---|
| (i) U6 statements | by name: `STPfStep5gL`, `STStep5IIIgL`, `STIngR5gL`, `STPfConclgL`, `STTailtoTailConclgL`, `STStep5ConclgL`, `STDecayStrongUgL` | below |
| (ii) BA targets | `T2459_STPfStep5BA` :35, `T2459_STStep5IIIBA` | :338 via `T2459_inst_IngR5` :328; `T2459_prem` (:322) = the Steps 1-4 premises as hypotheses |
| (iii) kernel | `T2459_BAweighted` :69, `T2459_BAKernel` :78, `T2459_kernel_at_flow` :84 | :346 (weighted), :357 (kernel) |
| (iii) premise bundle, ℰ-bounds | `T2459_BAscalar` :107, `T2459_BAmatrix` :116, `T2459_BAEdet` :134 | scalar part proved (`T2459_scalar_sz0` :154, n = 1, u = 1/2, D = 40); :364 (matrix part a hypothesis) |
| (iii) good event, walk | `T2459_BAgood`, `T2459_BAgoodThm` :191 (hypotheses `STKboundgL`, `STAvgUgL`, `T2459_LmaxU`, `T2459_LKU`, `STGdecayWgL`), `T2459_BAWalkConcl`, `T2459_BAWalk` :213, `T2459_BAfromWalk` :218, `T2459_BAclosure`, `T2459_main_of_parts` :227 | :373 (good event), :379 (walk, lift), chain :234 |
| (iv) unmerged inputs | `T2459_P1` :209 (T2460 target 4), `T2459_caseIII_succ` (T2462 target 4), `T2459u4_FlowFacts` | hypotheses of exact type; P5 not needed (`T2459_Theta_far`, :384) |
| HS bound | `T2459_trace_mul_le` :281, `T2459_trace_mul3_le` | proved |
The matrix part of `T2459_BAmatrix` (stopped control, `K0`, far field, avg, `LmaxU`, (vi)) is the good-event content of other gates' stochastic pins: a witness `H` must satisfy bounds on `(baStep2Mat ..).K`, which is `BAKloop` (`FlowPins:298`), defined through the choice-valued `BAKsol` and characterized only by `BAKsol_isKLoopS` (`KSolve:606`); no evaluation at concrete data is merged, so the matrix part stays a hypothesis of the ℰ-bounds instance. `T2459_P1` has no instance of its own (an unmerged row's pin enters as a hypothesis).
```
$ bash docs/reports/T2459/u6_recheck.sh
lake env lean exit=0, error lines: 0, warning lines: 0
```
Re-check table (Part 2 of `docs/tickets/checks/T2458-check.lean`, lines 174-466, against merged `Chain/Step5Gen.lean`; each pair is `Iff.rfl`, no change of content): `T2458_STDecayStrongUgL` :186 = `STDecayStrongUgL` :51; `T2458_STStep5ConclgL` :196 = :62; `T2458_STPfConclgL` :254 = :139; `T2458_STTailtoTailConclgL` :281 = :169; `T2458_STTailtoTailgL'` :289 = :178; `T2458_LmaxU_inline` :297 and `T2458_LKU_inline` :302 = the premises of `STIngR5gL` :191 (explicit `PrecL` form, as `T2459_LmaxU`, `T2459_LKU`); `T2458_STIngR5gL` :309 = :191; `T2458_STStep5RgL` :325 = :214; `T2458_STStep5IIIgL` :338 = :228; `T2458_STPfStep5gL` :361 = :252. `T2458_STLemDecCalEConclgL` (:368) is the conditional target 11 of T2458 (`docs/tickets/T2458.md:20`); it is absent from merged `Chain/Step5Gen.lean` (grep 0) and not used by U5.

## (d) Rows of U5's 1b (U5-8)
New BA files only, namespace `RBM.BA`, no in-place edit, not in the certificate lane; statements = the probe pins.
| row | file | statements | lo / central / hi | role | dependencies | order |
|---|---|---|---|---|---|---|
| U5a | `BA/Step5IIIKer` | `T2459_BAweighted`, `T2459_BAKernel`, BA `tailtoTailSq` (H1-H3), `T2459_Theta_far` | 800 / 1,200 / 1,800 | prover-hard | stage E merged (`KKernel`, `EKPins`, `Step2Kern`), U6 merged, `baEMn2ExpHK` merged | 1 |
| U5b | `BA/Step5IIIEdet` | the HS lemmas and glue form, `T2459_BAscalar/BAmatrix/BAEdet` (lk, wG, dif) | 1,600 / 2,350 / 3,600 (splits at wG / dif, ~1,100 + 1,250) | prover-max (new mathematics) | U6 names; `LemDecCalE_sum_tail_tail`, `EwG_sum_sqrt_tail` (imports) | 1 (parallel to U5a) |
| U5c | `BA/Step5IIIGood` | `T2459_BAJsharp`, `T2459_BAgood`, `T2459_BAgoodThm` (with the interpolation (vi)) | 600 / 900 / 1,350 | prover-hard | U5b; Steps 1-4 BA pins as hypotheses (T1-BA, U3-BA) | 2 |
| U5d | `BA/Step5IIIWalk` | `T2459_BAWalkConcl`, `T2459_BAWalk`, `T2459_BAfromWalk`, `T2459_BAclosure` | 1,500 / 2,200 / 3,400 | prover-max | U5a, U5b, U5c; P1 = T2460 target 4; `StoppedDuhamelNg` (merged); `BAuKerSemigroup_holds` | 3 |
| U5e | `BA/Step5IIITargets` | `T2459_main_of_parts`, `T2459_STPfStep5BA`, `T2459_STStep5IIIBA`, instances | 150 / 250 / 450 | prover-hard | U5d; T2462 target 4 (fallback: a 60-line local copy) | 4 |
| total | | | 4,650 / 6,900 / 10,600 | | | |
Basis: the band stack has 16,063 lines (U5-0); the BA files import the model-free band lemmas (lattice sums, ball counts, `riemann`, `closure`, `level`) and the merged `StoppedDuhamelNg`, and replace the entry-level layer (e6-e9, `fG`, `tri`, `avg`, Lipschitz) by the Hilbert-Schmidt route; per-file estimates (U5-0) sum to 5,450 lines, the rows add 1,450 for the HS lemmas, the sum `S_theta`, `T2459_Theta_far`, the semigroup instance, the bridge, the targets and the instances. T2379 priced U5 at one ticket, 1,300 central (`T2379-design.md:132`), which is low. **Inputs with no producer: none** (P1: T2460, released H249; U4s1: T2462, released H251; the crude QV bound, the list-loop bridge and the semigroup instance are inside U5d; P5 is dropped). Merge order: U5a and U5b in parallel, then U5c, U5d, U5e.

## (e) Paper-delta text (U5-9)
**T2459a** (`7_8:2101`, with `3_5:2284-2383`). *What the paper omits.* The proofs of Steps 3-6 "extend verbatim to the block Anderson model, except for the arguments in sec:Step5_larget and the proof of lem:LWterm_EXP"; in sec:Step5_larget the block Anderson arguments "are based on lem_GbEXP_BA and parallel those in [RBSO1D, Section 7.3]. We therefore omit the details." *The argument formalized* (case `1-t >= lambda^2` of Step 5 for `S^(B) = I`, `M = M^(B) (x) I`, `g0 = sqrt(t0) g <= g`): (1) *Kernel.* `K = |M^(B)|^2` is doubly stochastic with `K_aa = |m|^2` (Ward, eq:WardM) and `K_ab <= A g0^2 e^(-2c|a-b|)` (Mbound_AO2); for `g0^2 <= g^2 <= 1-t` the weighted row sum satisfies `t Sum_b K_ab e^(mu|a-b|) <= (1+t)/2`, so `(1-sK)(1-tK)^-1` has `Sum_b |U_ab| e^(sqrt|a-b|) <= C (1-s)/(1-t)` and (neiwuj) holds with `C = C(d, lambda_max, kappa)`; `|m| = 1` and smallness of `g` are not used. (2) *lem_dec_calE.* The three bounds follow from the stopped bound on `(L-K)^(2)`, the bound on `K^(2)` and its far field (prop:ThfadC), the loop bounds (Eq:L-KGt2) and `|tr X_1...X_k| <= prod ||X_i||_HS` for block-compressed legs, `||E_a^(1/2) G E_b^(1/2)||_HS^2 = L^(2)_{(a,b)}`; no entrywise bound on `G` and no use of (GijGEX_BA). (3) *Closure.* The stopped hierarchy (int_K-L_ST) on a grid with the closure `J <= C + log W + W^(2 eps - dd/2) < W^eps`. *Regime:* the case predicate reads `g = lambda` and the kernel `g0 <= g`; for `lambda >= 1` the case is empty.
**T2459b**: the Lean cut-offs of (res_deccalE_wG) and (res_deccalE_dif) are `2 l*` and `6 l*` (near cut `2 l*`), the paper's `l*`, `4 l*`, `l*`, because the K-level far field is proved at `l*`; only constants change.
**T2459c**: Lean does not use `lem_GbEXP_BA` in case (iii); the loop-level (Hilbert-Schmidt) route replaces the entrywise one of the band Lean (`LemDecCalE*`, e6-e9). The paper statement is unchanged.
**T2459d**: the shape `forall lam0, STTailtoTailgL' 3 (baFM . lam0)` (T2458-check:462) is expected false; the kernel bound is stated at `lam0 <= sz.lam` (§U5-1).
**T2459e**: the Theta-level far field is derived from the K-level one (`T2459_Theta_far`); `BAKellStarEv` (T2452c) is not needed.
**T2459f**: the Lean `dif` bound carries the extra factor `W^(2 theta d (Cd+1)) Sum_y e^(-(theta/2) sqrt|y|)` (`theta in (0,1)` arbitrary, `Cd` the exponent of (Eq:Gdecay_w)) from the `J`-free long legs; the paper's `≺` absorbs it.

## (f) Stop rules, findings, fill-in table (H250 (4))
*Verification level.* U5-1 and U5-2 are derived by hand at paper level from the cited merged statements; compiled are the pins, the instances, `T2459_Theta_far`, `T2459_flowFacts_BA` and the Hilbert-Schmidt trace bound; the numerics check the kernel constants, the lattice-vs-Yukawa formula and the Hilbert-Schmidt inequality.
*Stop rules.* (1) the argument closes at paper level with the named inputs: no gap found; no question for Jun. (2) C1-forbidden fact: none. (3) constant growing with L or degenerating as t -> t0: none where the regime is nonempty (g = 1/64, g = 1 under g0: flat in L, `gap(t_b)` >= 0.306). At g = 10 (regime empty under both readings, kernel constants "for the record") `CU` grows 1.63 -> 4.01 for L = 4..256; this is not applied as a stop: the regime is empty, the analytic constant is L-independent (`consts`), the increments shrink (+36%, +8.6%), `1/mu_obs` = 15 to 25 sites at L = 64..256; the dispatcher may overrule. (4) U6 content change: none (11 `Iff.rfl`); merged statement change: none. (5) probe 394 <= 400 lines, report 321 <= 450 lines (`wc -l`).
*Findings.* F1 P5 `BAKellStarEv` is not needed. F2 the entry-level conjuncts of the `STIngR5gL` premises are carried but not read; no `BAGbEXP*` is read, so the event-conditioning issue (O3) does not arise; the loop-level `STGdecayWgL` and `STLKU` (k = 2) are read, for (vi). F2b the stopped control alone cannot bound the long legs of `dif` in the configuration `r <= 6 lambda`, `c` far without a `J^2` on the J-free indicator term, which breaks the closure (U5-2); (vi) is the extra Steps 2 and 4 input that removes it. F3 BA case (iii) at g >= 1 is empty by the size-level name. F4 analytic constants are huge but uniform in L. F5 T2460 target 4 must stay (H249 (3)). F6 thresholds `2 l*`, `6 l*` (T2459b). F7 the free-`lam0` shape is expected false (T2459d). F8 `T2462_FlowFacts` holds at BA by merged names. F9 the ticket's count 23 for `|E| < 2` is not reproduced.
| item | where |
|---|---|
| D1 first line: verdict, regime reading, rows and total central of U5's 1b | line 1 |
| D1 order: (a) numerics, (b) U5-0 ... U5-5, (c) probe pins and U6 re-check, (d) rows, (e) paper delta | (a) 6, (b) 132, (c) 210, (d) 250, (e) 262 |
| D2 probe <= 400 lines, never merged, nonvacuous instances | (c) 210; 394 lines; branch t/T2459 only |
| U5-0 inventory: classes (i)-(v), BA replacements | 135-162 |
| U5-1 kernel: statement, proof, constant C(d, Lam, kappa) | 163-171; probe :69, :78 |
| U5-1 also answer: the free-lam0 shape (check:462) | 170 |
| U5-2 premise bundle (successor of E2Hyp) and its sources | 173; probe :107, :116 |
| U5-2 main risk (G near M, non-scalar M) | 175 |
| U5-2 the three bounds lk, wG, dif at BA | 176; probe :134 |
| U5-2 where S = 1 simplifies STELKLKMg, STEGtMg, STEEkMg | 181 |
| U5-2 the K inputs: bound and far field, the route and why | 182; probe :242 |
| U5-3 stopping time | 185; probe :199 |
| U5-3 stopped hierarchy on a grid (StoppedDuhamelNg) | 186 |
| U5-3 martingale: clause 4 of STGridRepNAtgL d 2 at baStep2Mat | 187; probe :209 |
| U5-3 QV and flow bounds with C.eta | 188 |
| U5-3 closure with the BA exponents | 190; exponents in (a) 9 |
| U5-3 lift PrecPT -> Prec | 191; probe :218 |
| U5-4 targets; STStep5IIIgL from STPfStep5gL through U4s1 (one line?) | 194-196; probe :47 |
| U5-5 table: step -> uniform facts (file:line), Lam = dd^-1 | 197-209 |
| U5-5 forbidden facts (C1) | 208 |
| U5-6 per g: t0, g0, Im m0, usable kappa | 30 (columns t0, g0, Imm, Imm0; kappa in the headers) |
| U5-6 STReg5III nonempty on [0, t0], readings g and g0 | 19 |
| U5-6 Ward row-sum error; 1-|m0|^2 against g0^2 | 30 (columns ward, (1-|m0|^2)/g0^2) |
| U5-6 weighted row sum and its rate mu | 30 (mu_obs, gamma); analytic mu in consts 76 |
| U5-6 max_a Sum_b |uKer| e^sqrt / rho over s <= t, four charge pairs | 30 (column CU) |
| U5-6 far field of Theta at (1/8)(log W)^(3/2) | 57 |
| U5-6 every deterministic constant of (b); bounded in L | consts 76, sums 70 |
| U5-6 vacuity at g = 1, 10; kernel constants at the g0 boundary; stop on growth | regime 19; stop rule (f) 272 |
| U5-7 (i) U6 statements copied verbatim as T2459u6_* | n/a, because U6 is merged (1debc23): used by name, re-check table 248 |
| U5-7 (ii) BA targets as def : Prop over (i) | probe :35 |
| U5-7 (iii) intermediate pins: kernel, premise bundle, ℰ-bounds, walk conclusion | (c) table 238 |
| U5-7 (iv) unmerged inputs as hypotheses: P1, P5, U4s1's comparison | (c) table 241; P5 dropped |
| U5-7 (v) nonvacuous d = 3 instance of each pin | (c) table, instance column 234; matrix part and P1 stay hypotheses: 243 |
| U5-7 U6 re-check table | 248 |
| U5-8 rows: files, statements, lo / central / hi, role, dependencies, order | 250-261 |
| U5-8 re-estimate against the band stack; list of inputs without producer | 260 |
| U5-9 T2459a: omitted text, BA argument summary, inputs, regime | 262-269 |
| Probe rule: pins compile, unmerged inputs as hypotheses, no axiom/sorry/admit/native_decide/inductive, theorems use merged names | probe_check output 213 |
| Stop rules (binding) | 272 |
| H249 (3): one-slot clause (iv) instead of clause 4 | 192 |
| H250 (3) UBA-C4: kernel at g0, regimes at g, the constant A in the C1 table | line 1; (a) 19; U5-5 table 199 |
| Acceptance: probe exit 0, standard axioms, <= 400 lines | 213 |
| Acceptance: `git diff --stat main...t/T2459` shows only probe, report, docs/reports/T2459/ | docs/reports/T2459-prove.md (b) |
| Acceptance: numerics first; file:line for every merged fact; scripts reproduce | (a) 6; out/cite.out, out/cite_lines.out (86 citations) |
| Acceptance: every pin has a compiled nonvacuous instance and carries its parameters | (c) 234 |
| Findings | 273 |
