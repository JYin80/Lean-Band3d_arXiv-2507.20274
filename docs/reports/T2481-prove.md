Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct 13 00:46:45 UTC 2026

**Kernel route (dispatcher answer (1)): route (b)** for target 3, route (i) for 4 (b). Target 2 (`T2481_BAweighted`) is **dropped**: route (b)
needs no weighted K-row sum. Proof skeleton (all four charge pairs): `u_{s,t}=(s/t)1+(1-s/t)Θ_t` (`BAuKer_convex`, `EKPins:79`, `t>0`; `t=0` forces `s=0`, `u=1`);
`|Θ_t(a,x)| ≤ C5 Bparam e^{-c5|a-x|_1}` (`baProp5_holds`, `Prop6Path:850`, `Λ=𝔡⁻¹`, `g=lam0`), `ellT=1` since `lam0² ≤ lam² ≤ 1-t`;
`Bparam ≤ 2/(1-t)`; `k√r ≤ (c5/2)r + k²/(2c5)`; `Σ_x e^{-(c5/2)|a-x|_1} ≤ expC(d-2,c5/2)` (`BAsum_exp_decay_le`, `Prop5Short:251`);
row sum `Σ_x|u| ≤ ρ=(1-s)/(1-t)` (Neumann series with `|M^{σσ'}_{ab}|=K_{ab}` (`BAMss_norm_eq_BAK`, `KKernel:102`) and Ward `BAK_row_sum` `KKernel:124`: `s/t+(1-s/t)/(1-t)=ρ`).

### (i) Exponent / constant table (d=3, flow_sz0 data `(κ,ε,𝔠,𝔡)=(1/2,1/10,1/6,1/10)`, `Λ=𝔡⁻¹=10`, `sz0`: `L=4(n+1)`, `W=(2(n+1))^5`, `lam=(2(n+1))^{-6}`)
| quantity | value | constraint | slack |
|---|---|---|---|
| `t0=BAflowT0` | `→25/36=0.6944` (`g→0`; num. 0.6937 at g=1/64) | `κ/(κ+1)=1/3 ≤ t0 < 1` (`TwistStep2:731`, `EMn2BA:106`) | 0.36 below; `1-t0 ≥ 0.306` |
| target 1: `lam0=√t0·lam` | `lam0/lam=0.833` | `0<lam0 ⇒ lam0 ≤ lam`, from `lam0² ≤ lam² ≤ ((κ+1)/κ) lam0²` (`TwistStep2:740`) | `1/t0=1.44 ≤ 3` |
| regime | `lam² ≤ 1-w`, `w ≤ t0` | `ellT(L,lam0,w)=min(max(lam0/√(1-w),1),L)=1` | `lam0²/(1-w)=3.4e-40` at n=1000, w=1/2 |
| `Bparam` | `≤ 2/(1-w) ≤ 2/lam² ≤ 2W^{d-2𝔡}=2W^{2.8}` | `lam²W^d ≥ W^{2𝔡}` (`Defs/Sizes:193`, from WO) | exponent `2.8` vs need `d` |
| `C5,c5` (`baProp5_holds`) | existential in `(d,Λ,κ)`; `c5 ≤ c'/2`, `c'=BAp5s_rate(3,10,1/2)=1.29e-32` (`inst.py`) | positive, free of `L,n,t,s` | none used |
| weighted consts | `Wk=max(1, 2·C5·e^{k²/(2c5)}·expC(d-2,c5/2))`, `k=1,2` | `Σ_x|u_{s,t}(a,x)|e^{k√|a-x|_∞} ≤ Wk ρ` (`|x|_∞≤|x|_1`) | num. `CU ≤ 2.56`, `CU2 ≤ 14.94` (L-stable) |
| `Cc` (target 3) | `W1²` | `Σ_b Π|u|τ_s²e^{-√|b0-b1|} ≤ W1² τ_t²e^{-√|a0-a1|}`, `τ_s=(W^d(1-s))⁻¹` | `W^{-D}` term has coeff `ρ²` exactly |
| `Cq` (target 5) | `2·max(1,W2²)` | `Cq ≥ 2W2²` (near amplitude), `Cq ≥ 2` (floor `2W^{-2D}ρ⁴`); `(x+y)²≤2x²+2y²` | num. `max RN=0.9913 ≤ 2` |
| `τ_vρ=τ_w` | exact | `ρ²(W^d(1-v))⁻²=(W^d(1-w))⁻²` | 0 (identity) |
| row sum `ρ` | `Σ_x|u|≤ρ` | coefficient 1 in the far term `4YL^dρ³W^{-D₂}` | num. `rowmax=1.000000` (tight, 0) |
| `ℓ*=(log W)^{3/2}`, cut `2ℓ*` | n=1000: `log W=38.01`, `ℓ*=234.3`, `2ℓ*=468.7`, `L/2=2002` | `4 ≤ log W`; far pair ⇒ some `|a_i-b_i|` or `|a_i-b'_i|>ℓ*` (triangle: `2ℓ*<|b_i-b'_i|`) | `log W` 38.0 vs 4; `L/2` vs `2ℓ*`: 4.3x |
| far count | 4 events × `L^d` × `ρ³` | union bound over `(i, b|b')` | num. `RF ≤ 0.152` (overcount upper bound) |
| 4 (b) decay | `‖u(x,y)‖ ≤ 2C5 lam⁻² e^{-c5ℓ*} ≤ W^{-D}` | `2C5 W^{d+D} ≤ e^{c5(log W)^{3/2}}` ⇐ `(log W)^{1/2} ≥ 2(d+D)/c5` (and `log W` ≥ log(2C5)/(d+D)) | threshold in W is existential (`∀ᶠ n`); analytic `log W ≳ 1.5e66` at D=1 (record, not a witness) |
| g=10 | regime empty (`1-t0 < g0²`) | record only | `mu_obs` falls 0.065→0.040 (L 64→256): not used |
Constants `Cc,Cq` depend on `(d,𝔡⁻¹,κ)` only (not on `L,n,t,s,v,w`); the threshold of 4 (b) also on `D`. No C1-forbidden fact (`BAK_le_small`, `BAMB_upper_small`, `BAGbEXPij`, `Mbound_AO`, `g ≤ W^{-ε}`) is used.

### (ii) One nondegenerate instance (all hypotheses at once) and the numerics
Instance: `sz0`, `zSeq` (`w=1.2i`), n=1000, `v=s=1/10`, `w=t=1/2`, `D=1`. `(H1)-(H2)` witness: `X(b,b')=p·T_v(b)²` (equality in (H1)), `Y=p T_v(0)²`; this is the worst case computed in `t5` below (limit computation of the external premises). The Lean instances of 4 (b), 5 are `∀ᶠ n` statements at `flow_sz0` (no witness `n`); n=1000 is a concrete point where every hypothesis holds; the conclusions are checked numerically at moderate `(L,W)` because the analytic threshold is astronomically large (table, row 4 (b)).
$ python3 inst.py | head -19
n=1000: L=4004 W=3.216032e+16 lam=1.553e-20 N=2.135e+60 t0(g->0)=0.6944444444444444 (25/36) lam0=1.294e-20 log W=38.010 l*=234.34 2l*=468.7 L/2=2002 L^d=6.419e+10
  Admissible_WO_lower: True
  WO_upper: True
  Bandwidth_W_ge_N_1_6: True
  t0_ge_kappa_over_kappa_plus_1: True
  t0_ge_2_3: True
  t0_lt_1: True
  lam0_pos_le_lam_le_dinv: True
  R1_lam2_le_A_lam0_2: True
  regime_lam2_le_1_minus_w: True
  s_le_t_lt_1: True
  v_le_w_lt_1: True
  four_le_logW: True
  near_cut_below_half_torus: True
  lam_sq_W_d_ge_W_2dd: True
  all hypotheses hold: True
record: BAct_rate(d=3,Lam=10,kappa=1/2)=4.1580e-03; BAp5s_rate (same-charge rate c' of Prop5s)<= 1.29e-32; proof threshold log W >= (2(d+D)/c5)^2 with c5 <= c'/2 -> >= 1.5e+66 for D=1 (existential threshold; statement is 'eventually')
$ python3 num.py regime | grep -E 'L= 64' | cut -c1-210
g=0.015625 L= 64 t0=0.6937 t0>=kappa/(kappa+1)=0.3333: True g0=0.0130 g0<=g: True g^2/g0^2=1/t0=1.441 <= A=3.00: True window[g]=(0,0.6937] window[g0]=(0,0.6937]
g=1        L= 64 t0=0.2862 t0>=kappa/(kappa+1)=0.2000: True g0=0.5350 g0<=g: True g^2/g0^2=1/t0=3.494 <= A=5.00: True window[g]=(0,0.0000] window[g0]=(0,0.2862]
g=10       L= 64 t0=0.0442 t0>=kappa/(kappa+1)=0.0385: True g0=2.1024 g0<=g: True g^2/g0^2=1/t0=22.624 <= A=26.00: True window[g]=(0,0.0000] window[g0]=(0,0.0000]
$ python3 num.py consts | head -2 | cut -c1-260
deterministic constants introduced by (b) (d=3, Lam=1/dd=10); analytic (Lean-formula) values; observed values are in `flow`, `sums`
kappa=0.5: c=BAct_rate=4.1580e-03 C=BAct_C=1152 A=BAp5s_A=3.070e+11 S=BAp5s_S=2.055e+13 S1=(2/(e c))expC(1,c/2)=5.819e+16 mu=min(c,1/(2 A S1))=2.798e-29  Cc=(3 e^(1/(4mu)))^2 = exp(1.787e+28) (L-independent)  A_UBA=(kappa+1)/kappa=3.00 (not entered)
$ grep -E '^L= 64' flow.out | cut -c1-285
L= 64 t0=0.6937 g0=0.0130 Imm=0.8325 Imm0=0.9995 |m0|=0.99949 ward=1e-16 (1-|m0|^2)/g0^2=5.991 | t_b=0.6937 1-t_b>=g0^2:True mu_obs=>=5 (search cap) gamma(mu_obs)=1.193448 gap(t_b)=0.306 CU=1.0039 bound=3.154
L= 64 t0=0.2862 g0=0.5350 Imm=0.3435 Imm0=0.6420 |m0|=0.64199 ward=1e-15 (1-|m0|^2)/g0^2=2.054 | t_b=0.2862 1-t_b>=g0^2:True mu_obs=0.288 gamma(mu_obs)=2.246931 gap(t_b)=0.714 CU=1.5163 bound=7.14
L= 64 t0=0.0442 g0=2.1024 Imm=0.0442 Imm0=0.2102 |m0|=0.21024 ward=2e-14 (1-|m0|^2)/g0^2=0.216 | t_b=0.0442 1-t_b>=g0^2:False mu_obs=0.065 gamma(mu_obs)=11.812202 gap(t_b)=0.956 CU=2.7080 bound=140.4
$ python3 num.py far | grep -E 'L=32 t_b|W=1e\+03' | cut -c1-200
g=0.015625 L=32 t_b=0.6937: max_(x!=0)|Theta - t Theta K|=1.1e-16;  (1-t) max_(|x|_inf=r)|Theta_0x| at r=1,2,4,8,12,16: 1:3.81e-04 2:2.10e-07 4:6.35e-14 8:3.40e-17 12:5.40e-17 16:6.80e-17
   W=1e+03: (1/8)(log W)^(3/2)=2.27, r0=3 (L/2=16): (1-t) max_(|x|>=min(r0,L/2)) Theta = 1.15e-10
g=1 L=32 t_b=0.2862: max_(x!=0)|Theta - t Theta K|=2.9e-17;  (1-t) max_(|x|_inf=r)|Theta_0x| at r=1,2,4,8,12,16: 1:9.17e-03 2:8.83e-04 4:3.77e-05 8:1.66e-07 12:1.31e-09 16:4.32e-11
   W=1e+03: (1/8)(log W)^(3/2)=2.27, r0=3 (L/2=16): (1-t) max_(|x|>=min(r0,L/2)) Theta = 1.71e-04
$ grep -E 'L= 64|L=128' cu2.out | cut -c1-175
g=0.015625 Im w=1.2 L= 64 t0=0.6937 t_b=0.6937 | t=0.6937: CU=1.0039 CU2=1.0147 rowmax=1.000000 | t=0.3469: CU=1.0009 CU2=1.0034 rowmax=1.000000
g=0.015625 Im w=0.4 L= 64 t0=0.1625 t_b=0.1625 | t=0.1625: CU=1.0001 CU2=1.0003 rowmax=1.000000 | t=0.0812: CU=1.0000 CU2=1.0001 rowmax=1.000000
g=0.5 Im w=1.2 L= 64 t0=0.4413 t_b=0.4413 | t=0.4413: CU=1.4710 CU2=3.1095 rowmax=1.000000 | t=0.2207: CU=1.1878 CU2=1.8022 rowmax=1.000000
g=1 Im w=1.2 L= 64 t0=0.2862 t_b=0.2862 | t=0.2862: CU=1.5163 CU2=3.9429 rowmax=1.000000 | t=0.1431: CU=1.2292 CU2=2.2375 rowmax=1.000000
g=1 Im w=0.8 L= 64 t0=0.4702 t_b=0.4702 | t=0.4702: CU=2.5550 CU2=14.9405 rowmax=1.000000 | t=0.2351: CU=1.6074 CU2=5.5304 rowmax=1.000000
g=1 Im w=2.0 L= 64 t0=0.1439 t_b=0.1439 | t=0.1439: CU=1.1389 CU2=1.6138 rowmax=1.000000 | t=0.0720: CU=1.0657 CU2=1.2868 rowmax=1.000000
$ grep -E 'W=1e\+03|W=1e\+06' far4b.out | grep -E 'Im w=1.2|Im w=0.8' | sed 's/pairs beyond: [0-9]*//' | cut -c1-290
W=1e+03 l*=18.16 (L=64, L/2=32, ) g=0.015625 Im w=1.2 t_b=0.6937: max|uKer|=4.441e-16  max Theta^K_w=2.046e-16  W^-1=1.0e-03  max<=W^-1: True  max <= W^-D for D=2,3: True, True
W=1e+03 l*=18.16 (L=64, L/2=32, ) g=0.5 Im w=1.2 t_b=0.4413: max|uKer|=2.220e-16  max Theta^K_w=3.024e-17  W^-1=1.0e-03  max<=W^-1: True  max <= W^-D for D=2,3: True, True
W=1e+03 l*=18.16 (L=64, L/2=32, ) g=1 Im w=1.2 t_b=0.2862: max|uKer|=5.978e-13  max Theta^K_w=5.978e-13  W^-1=1.0e-03  max<=W^-1: True  max <= W^-D for D=2,3: True, True
W=1e+03 l*=18.16 (L=64, L/2=32, ) g=1 Im w=0.8 t_b=0.4702: max|uKer|=1.815e-09  max Theta^K_w=1.815e-09  W^-1=1.0e-03  max<=W^-1: True  max <= W^-D for D=2,3: True, False
W=1e+06 l*=51.35 (L=128, L/2=64, ) g=0.015625 Im w=1.2 t_b=0.6937: max|uKer|=2.220e-16  max Theta^K_w=1.110e-16  W^-1=1.0e-06  max<=W^-1: True  max <= W^-D for D=2,3: True, False
W=1e+06 l*=51.35 (L=128, L/2=64, ) g=0.5 Im w=1.2 t_b=0.4413: max|uKer|=1.110e-16  max Theta^K_w=4.564e-17  W^-1=1.0e-06  max<=W^-1: True  max <= W^-D for D=2,3: True, False
W=1e+06 l*=51.35 (L=128, L/2=64, ) g=1 Im w=1.2 t_b=0.2862: max|uKer|=1.110e-16  max Theta^K_w=1.110e-16  W^-1=1.0e-06  max<=W^-1: True  max <= W^-D for D=2,3: True, False
W=1e+06 l*=51.35 (L=128, L/2=64, ) g=1 Im w=0.8 t_b=0.4702: max|uKer|=1.110e-16  max Theta^K_w=1.110e-16  W^-1=1.0e-06  max<=W^-1: True  max <= W^-D for D=2,3: True, False
$ python3 cu2big.py
g=1 Im w=0.8 L=32: CU2 = 14.8635
g=1 Im w=0.8 L=64: CU2 = 14.9405
g=1 Im w=0.8 L=96: CU2 = 14.9406
g=1 Im w=0.8 L=128: CU2 = 14.9406
$ grep -E 'W=6e\+01' t5.out | sed 's/np.float64(\([^)]*\))/\1/g' | cut -c1-290
W=6e+01 L=48 l*=8.48 2l*=16.96 far set nonempty: True g=0.015625 Im w=1.2 t_b=0.6937: max RN=0.9913 at (w,v,sigma,r,D)=(0.693739809288363, 0, (0, 1), 0, 3.0); max RF(upper bound of F)=1.382e-01
W=6e+01 L=48 l*=8.48 2l*=16.96 far set nonempty: True g=0.015625 Im w=0.4 t_b=0.1625: max RN=0.6702 at (w,v,sigma,r,D)=(0.16246787111433875, 0, (0, 1), 0, 3.0); max RF(upper bound of F)=1.517e-01
W=6e+01 L=48 l*=8.48 2l*=16.96 far set nonempty: True g=0.5 Im w=1.2 t_b=0.4413: max RN=0.9112 at (w,v,sigma,r,D)=(0.44130170019614184, 0, (0, 1), 0, 3.0); max RF(upper bound of F)=1.438e-01
W=6e+01 L=48 l*=8.48 2l*=16.96 far set nonempty: True g=1 Im w=1.2 t_b=0.2862: max RN=0.7939 at (w,v,sigma,r,D)=(0.2862161685305261, 0, (0, 1), 0, 3.0); max RF(upper bound of F)=1.161e-01
W=6e+01 L=48 l*=8.48 2l*=16.96 far set nonempty: True g=1 Im w=0.8 t_b=0.4702: max RN=0.9268 at (w,v,sigma,r,D)=(0.4702382354729143, 0, (0, 1), 0, 3.0); max RF(upper bound of F)=1.228e-01
W=6e+01 L=48 l*=8.48 2l*=16.96 far set nonempty: True g=1 Im w=2.0 t_b=0.1439: max RN=0.6506 at (w,v,sigma,r,D)=(0.1439084720782062, 0, (0, 1), 0, 3.0); max RF(upper bound of F)=1.150e-01

### Verdicts
- Target 1 `baStep5III_lam0_le_lam`: PASS (`lam0>0 ⇒ lam>0`, `lam0² ≤ lam²` from `TwistStep2:740`; numerics `g0<=g: True`, rows above).
- Target 2 `BAStep5IIIWeighted`: DROPPED by the route choice (b) (dispatcher answer (1)); no consumer under (b); the T2459 `mu_obs` for it is stable (0.288 at g=1, L=64) but unused.
- Target 3 `BAStep5IIIKernel` (+ `_at_flow`): PASS via route (b); `Cc=W1²`; numerics `CU ≤ 2.56` (L-stable); regime nonempty at g=1/64 and g=1 (g0 reading), g=10 empty.
- Target 4 (a) `baStep5III_Theta_far`: PASS (compiled T2459 probe text, copy); off-diagonal `Θ=t(ΘK)` check error 1.1e-16 (`far` rows above).
- Target 4 (b) `baStep5III_uKer_far`: PASS (true as stated: route (i), `|u(x,y)| ≤ (1-v/w)|Θ_w(x,y)|` for `x≠y`); numerics: `max|uKer|` beyond `ℓ*` is ≤ 5.98e-13 at W=1e3 (1.8e-9 for g=1, Im w=0.8) and ≤ 2.3e-16 at W=1e6, against `W^{-1}`.
- Target 5 `BAStep5IIITailSq` and its QV reading: PASS (true as stated; exact worst-case X, four charge pairs, `v ≤ w`, `r ≤ 24`, `D ∈ {1,3}`: `max RN=0.9913 ≤ Cq`, `max RF ≤ 0.152 ≤ 1`). Formulas: rows `Cq`, `τ_vρ=τ_w`, row sum, far count. (H2) stays a premise (U5d); (H3) is 4 (b).
- Target 6 instances: PASS (hypotheses of 1, 3, 4, 5 hold at `flow_sz0`, n=1000: `inst.py` output). No stop rule triggered (no pin false; no constant grows with `L` or degenerates as `t→t0` where the regime is nonempty; no C1-forbidden fact; no comparison text, `withLam` or free `lam0`). Size and split decision: outside section (a) (stage 1a rule).
- Note for 1b: the exact-constant input is the one-index row sum `Σ_x|u_{s,t}(a,x)| ≤ ρ` (Neumann series + Ward, above; numerically `rowmax=1.000000`); every other constant is absorbed in `Cc, Cq`.

## (b) Script output — Tue Oct 13 01:20:56 UTC 2026  (branch t/T2481; RBM3D.lean untouched: the hub adds the two imports at merge, rule (A) step 4)
### (1) Lines per file against the stop line 2,000; (2) routes; split decision
$ git log --format='%h %s' main..t/T2481; wc -l <the two files>
a778b55f T2481: module docstrings of BA/Step5IIIKer, Step5IIIKer2
532f67a1 T2481: BA/Step5IIIKer2 targets 5, 6 (tailtoTailSq, QV reading, instances); Step5I
b2e85a74 T2481: BA/Step5IIIKer targets 1, 3, 4 (a), 4 (b) and instances
     709 RBM3D/BA/Step5IIIKer.lean
     471 RBM3D/BA/Step5IIIKer2.lean
    1180 total
Landed 709 / 471 (total 1,180) against the ticket's central 750 / 450 and stop line 2,000 per file: the pre-signed split (central > 1,950) and the reserve rule (> 1,800) are not triggered; no `t/T2481b`. Section (a) is unchanged; no (a′).
- Target 3: route (b) (answer (1)): `Step5IIIKer_uKer_weighted` = `baProp5_holds` (`ellT = 1` in the regime) + `BAuKer_convex`, row sum `EKPins_norm_uKer_le`; `Cc = W₁²`. Target 2 (`T2481_BAweighted`) is dropped (as (a) says), not proved.
- Target 4 (b): route (i): `baProp5_holds`, `(1-w)⁻¹ ≤ W^d` (`lam_sq_mul_pow_ge`), `2C W^{d+D} ≤ e^{c ℓ*}` eventually (`Step5IIIKer_poly_le_exp`). 4 (a) is the probe text (copy).
### (3) Statement diff against the check pins and the probe
$ python3 stmt_diff.py   # extracts each statement, normalises whitespace, compares after the name (pairs joined by ;)
BAKernel ~ BAStep5IIIKernel (header) =;BAKernel ~ BAStep5IIIKernel (body) =;BATailSq ~ BAStep5IIITailSq (header) =
BATailSq ~ BAStep5IIITailSq (body) =;BATailSqQV ~ BAStep5IIITailSqQV (header) =;BATailSqQV ~ BAStep5IIITailSqQV (body) =
KernelAtFlow body ~ baStep5IIIKernel_at_flow statement =;UKerFar body ~ baStep5III_uKer_far statement =;probe T2459_BAKernel body ~ BAStep5IIIKernel body =
probe T2459_lam0_le_lam ~ baStep5III_lam0_le_lam =;probe T2459_Theta_far ~ baStep5III_Theta_far =;probe T2459_BAweighted ~ (dropped; check pin BAweighted) =
(= means IDENTICAL; the probe's `T2459_kernel_at_flow` has `ε 𝔠` before `∃ Cc` and the hypothesis `hK`; the binding pin `T2481_KernelAtFlow` has them after, and the theorem proves the pin; the last pair compares the probe's dropped target-2 text with its pin and proves nothing.)
$ awk: print the statement of each target from its file (up to ":= by" / the end of the def); 4 (a), 5, 5-QV by line range (their text is the diffed one above)
RBM3D/BA/Step5IIIKer.lean:399: theorem baStep5III_lam0_le_lam {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {sz : Sizes d} {z : ℕ → ℂ} (hflow : BAFlow sz κ ε 𝔠 𝔡 z)
RBM3D/BA/Step5IIIKer.lean:400:     (n : ℕ) (hpos : 0 < BAflowLam0 sz z n) : BAflowLam0 sz z n ≤ sz.lam n
RBM3D/BA/Step5IIIKer.lean:410: def BAStep5IIIKernel (d : ℕ) : Prop :=
RBM3D/BA/Step5IIIKer.lean:411:   3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ Cc : ℝ, 0 < Cc ∧ ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (D s t : ℝ),
RBM3D/BA/Step5IIIKer.lean:412:     BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n) → 0 < lam0 n → lam0 n ≤ 𝔡⁻¹ → lam0 n ≤ sz.lam n →
RBM3D/BA/Step5IIIKer.lean:413:     0 ≤ s → s ≤ t → t < 1 → sz.lam n ^ 2 ≤ 1 - t → STTailtoTailConclgL (baFM sz lam0 E) n Cc D s t
RBM3D/BA/Step5IIIKer.lean:414: 
RBM3D/BA/Step5IIIKer.lean:480: theorem baStep5IIIKernel_at_flow (d : ℕ) : 3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ Cc : ℝ, 0 < Cc ∧
RBM3D/BA/Step5IIIKer.lean:481:     ∀ (ε 𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ᶠ n in atTop, ∀ D s t : ℝ, 0 ≤ s → s ≤ t → t < 1 →
RBM3D/BA/Step5IIIKer.lean:482:       sz.lam n ^ 2 ≤ 1 - t → STTailtoTailConclgL (baFMz sz z) n Cc D s t
RBM3D/BA/Step5IIIKer.lean:564: theorem baStep5III_uKer_far (d : ℕ) : 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ D : ℝ, 0 < D →
RBM3D/BA/Step5IIIKer.lean:565:     ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
RBM3D/BA/Step5IIIKer.lean:566:       ∀ᶠ n in atTop, ∀ v w : ℝ, 0 ≤ v → v ≤ w → w ≤ BAflowT0 sz z n → sz.lam n ^ 2 ≤ 1 - w →
RBM3D/BA/Step5IIIKer.lean:567:         ∀ (τ τ' : Bool) (x y : Zd d (sz.L n)),
RBM3D/BA/Step5IIIKer.lean:568:           Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (x - y) : ℝ) →
RBM3D/BA/Step5IIIKer.lean:569:           ‖Step2Gen_uKer (baFMz sz z) n τ τ' v w x y‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D)
RBM3D/BA/Step5IIIKer.lean: theorem baStep5III_Theta_far lines 495-499
RBM3D/BA/Step5IIIKer2.lean: def BAStep5IIITailSq  lines 268-286
RBM3D/BA/Step5IIIKer2.lean: def BAStep5IIITailSqQV lines 340-356
$ lake env lean chk2481.lean   # check file + imports of both modules + `example : ∀ d, T2481_X d := …` for X = BAKernel, KernelAtFlow, BATailSq, BATailSqQV, UKerFar; binder adapters for ThetaFar, Lam0LeLam
exit 0; lines containing 'error': 0; adapters in the file: 7
### (4) Build, axioms, premise scan, instances, greps
$ lake build RBM3D.BA.Step5IIIKer RBM3D.BA.Step5IIIKer2 | tail -1
Build completed successfully (4064 jobs).
$ #print axioms (ax.lean) of all 44 public declarations of the two files; the 10 target-level names:
baStep5III_lam0_le_lam BAStep5IIIKernel baStep5IIIKernel_holds baStep5IIIKernel_at_flow baStep5III_Theta_far baStep5III_uKer_far BAStep5IIITailSq baStep5IIITailSq_holds BAStep5IIITailSqQV baStep5IIITailSqQV_holds
every one of the 44 (targets included) depends on exactly [propext, Classical.choice, Quot.sound]: count 44 of 44
$ import RBM3D + both modules + #assert_rbm_axioms (prechk.lean) vs import RBM3D alone (prechk0.lean), outputs from line 2 on diffed
axiom audit: 14252 theorems, 4497 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
diff of the premise-scan/ledger lines: 0 lines (registry: none; no new line asked for)
$ grep -nE '^example' <the two files>   # instances: targets 1, 3, 4a, 4b | 5, 5-QV
RBM3D/BA/Step5IIIKer.lean:675:example : ∀ᶠ n in atTop, 0 < BAflowLam0 SizesInst.sz0 Flow
RBM3D/BA/Step5IIIKer.lean:681:example : ∃ Cc : ℝ, 0 < Cc ∧ ∀ᶠ n in atTop, ∀ D : ℝ,
RBM3D/BA/Step5IIIKer.lean:689:example : ∀ᶠ n in atTop, ∀ (x x' : Zd 3 (SizesInst.sz0.L n
RBM3D/BA/Step5IIIKer.lean:698:example : ∀ᶠ n in atTop, ∀ (τ τ' : Bool) (x y : Zd 3 (Size
RBM3D/BA/Step5IIIKer2.lean:410:example : ∃ Cq : ℝ, 0 < Cq ∧ ∀ᶠ n in atTop, ∀ (σ : Fin 2 
RBM3D/BA/Step5IIIKer2.lean:437:example : ∃ Cq : ℝ, 0 < Cq ∧ ∀ᶠ n in atTop,
Instances at `d = 3`, `sz0`, `zSeq`, `flow_sz0` `(κ,ε,𝔠,𝔡) = (1/2,1/10,1/6,1/10)`, `v = 1/10 < w = 1/2 < t₀` (`half_lt_t0`), regime from `sz0.lam ≤ 1/64` (`Step5IIIKer_sz0_reg`). Target 5: `p = 1`, nonzero `X = Step5IIIKer2_Xinst` (equality in (H1)), `Y = Step5IIIKer2_Yinst`, `D = D₂ = 1`: (H1)-(H3) and every deterministic premise discharged. 5-QV: (H1)-(H2) stay premises (U5b/U5c/U5d sources), (H3) and `4 ≤ log W` discharged eventually. Non-emptiness of `ℓ* ≤ zdistInf` is numerical only ((a), `far set nonempty: True`).
$ grep -nE <C1 list 1> F; grep -nE <C1 list 2> F; grep -nE "sorry|admit|native_decide|axiom" F   # F = the two files, exit codes (1 = no hit)
C1 list 1 exit 1
C1 list 2 exit 1
hygiene exit 1
$ name-clash: git grep -l (stems Step5IIIKer|baStep5III|BAStep5III) on main and every other t/* branch; the 44 public names on main
refs scanned: main + 485 t/* branches (excluding t/T2481)
total files with a hit: 0
scan exact public names (44) on main:
(no CLASH line above = 0 clashes)
docs/tickets/T2480.md: 1 line (sibling-scan line 80 names the file stem; no declaration). Ports from ../RBM1D, ../RBM2D: none (no diff-stat).
$ git diff --stat main...t/T2481 | tail -3
 RBM3D/BA/Step5IIIKer.lean  | 709 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/BA/Step5IIIKer2.lean | 471 ++++++++++++++++++++++++++++++
 2 files changed, 1180 insertions(+)
Narrative. Lean skeleton: `Step5IIIKer_theta_entry` (`baProp5_holds`, `ellT = 1`, `Bparam ≤ 2/(1-t)`) gives `|Θ_t(a,x)| ≤ 2C(1-t)⁻¹e^{-c|a-x|₁}`; `Step5IIIKer_uKer_weighted` (AM-GM `k√r ≤ (c/2)r + k²/(2c)`, `BAsum_exp_decay_le`, `BAuKer_convex`, `t = 0` case `u = 1`) gives `Σ_x|u(a,x)|e^{k√|a-x|_∞} ≤ W_k ρ`; `Step5IIIKer_two_slot` (product of two row sums, exponential triangle inequality for `√`) gives target 3 with `τ_sρ = τ_t`. Target 5 is `Step5IIIKer2_tailsq_abstract` (near part by `two_slot` with weight `c = 2`; far part by the four events `{ℓ* ≤ |a_i - b_i|}`, `{ℓ* ≤ |a_i - b'_i|}` through `Step5IIIKer2_slot_far`, `#Zd = L^d`) plus the arithmetic `A₀ρ² = A_w` (`Step5IIIKer2_arith`); the QV reading is the same term (`baStep2Mat_toFlowFM` definitional). The one-index row sum `≤ ρ` is the merged `EKPins_norm_uKer_le` (no Neumann series re-proved); `Cq = 2W₂²` equals (a)'s `2·max(1,W₂²)` as `W₂ ≥ 1`. The pin's `4 ≤ log W` is carried and not used.
### (5) Constants (formulas in `(d, 𝔡⁻¹, κ)`; none depends on `L, n, s, t, v, w`)
`(C,c) = baProp5_holds d 𝔡⁻¹ κ`; `V_k = 2C e^{k²/(2c)} expC(d-2, c/2)`; `W_k = max(1, V_k)`; `Cc = W₁²` (target 3), `Cq = 2W₂²` (target 5), `ρ = (1-s)/(1-t)`. Target 4 (b) threshold (`∀ᶠ n`, also on `D`): `2C W^{d+D} ≤ exp(c (log W)^{3/2})`, true once `log W ≥ max(1, K²)`, `K = (d+D+|log 2C|+1)/c` (`Step5IIIKer_poly_le_exp`). Numerical values: (a) (i) table.
### (6) UBA-C1 table as used; greps in (4)
Target 1: size level `sz.lam n`, kernel level `BAflowLam0`, crossing the guarded `0 < g₀ → g₀ ≤ sz.lam` (`TwistStep2:740`), no `A`. Targets 3, 5, 4 (b): statements carry `0 < lam0 n`, `lam0 n ≤ 𝔡⁻¹`, `lam0 n ≤ sz.lam n`, regime `sz.lam n ^ 2 ≤ 1 - t`; only `lam0² ≤ lam² ≤ 1 - t` is used (`Step5IIIKer_sq_le`, for `ellT = 1`); at the flow target 1 discharges `lam0 ≤ lam`. 4 (a): `emn2ExpEllStar` level, no crossing. No R1 or comparison text, `withLam`, free `lam0`; `STGridRepNgL` 0 hits (TN-C4).
### (7) Hypotheses as used (premise → merged source); `open private`: none
- BAReal, `0 < g₀ ≤ 𝔡⁻¹` at the flow: `BAflow_real` (BA/GreenSchur:59), `BAflow_lam0_window` (:72); `uKer = BAuKer`, `UN = BAUN`: `Step2Kern_uKer_BA` (Chain/Step2Kern:112), `Step2Kern_UN_BA` (:124).
- Row sum, convex form: `EKPins_norm_uKer_le` (BA/EKPins:185) via `RBM.sum_norm_row_le` (Kernel/Evolution:78); `BAuKer_convex` (EKPins:79), `BAuKer_eq_one_add` (:62).
- Decay: `baProp5_holds` (BA/Prop6Path:850), `baP8_BATheta_shift` (:497), `BAsum_exp_decay_le` (BA/Prop5Short:251), `lam_sq_mul_pow_ge` (Defs/Sizes:193), `zdistInf_le_zdistD` (:117); `W_n → ∞` from `Admissible`.
- 4 (a): `baEMn2ExpHK` (BA/EMn2BA:637), `EMn2BA_K_two` (:624), `EMn2BA_T0_lt_one` (:106), `BATheta_resolvent` (BA/KBase:330). Target 1: `TwistStep2_lam0_sq` (BA/TwistStep2:740). Target 5 QV: `STeeUMg` (Chain/Step2Gen:983), `baStep2Mat_toFlowFM` (BA/Step2BA:75).
- Inline premises of target 5: (H1) near bound, (H2) crude bound (U5b/U5c/U5d); (H3) is `baStep5III_uKer_far` at the flow.
- Copies (not ports from RBM1D/RBM2D): `Step5IIIKer_zdistInf_{neg,add_le,tri,sub_comm,zero}` from the private `Induction/EMn2Poly.lean:442-467`; `Step5IIIKer_W_tendsto` from `Chain/Step34Gen.lean:610` (not imported); `baStep5III_lam0_le_lam`, `baStep5III_Theta_far`, `Step5IIIKer_sz0_lam_le` from the probe `t/T2459` `:58`, `:240-276`, `:94`.
## (c) Verified Mathlib names (all used in the compiled files; checked by compile or `grep` in `.lake/packages/mathlib`)
`Finset.prod_univ_sum` + `Fintype.piFinset_univ` (sum of products over `Fin 2 → Z`); `Finset.prod_le_prod₀` (Algebra/Order/BigOperators/GroupWithZero/Finset:39; `Finset.prod_le_prod` has the one-hypothesis form); `Finset.single_le_sum`; `Real.rpow_add'`, `Real.rpow_def_of_pos`, `Real.rpow_add`, `Real.rpow_natCast`, `Real.rpow_neg`, `Real.one_le_rpow`; `Real.le_log_iff_exp_le`, `Real.exp_nat_mul`, `Real.tendsto_log_atTop`, `Real.sqrt_le_left`, `Real.le_sqrt_of_sq_le`, `Real.sqrt_eq_rpow`; `tendsto_atTop_mono'`, `tendsto_rpow_atTop`; `pow_le_pow_left₀`, `one_le_pow₀`, `inv_anti₀`, `inv_le_one_of_one_le₀`, `div_le_iff₀`, `le_div_iff₀`; `Matrix.one_apply_ne`, `Complex.norm_real`. Absent: `Real.sqrt_add_le*` (grep `sqrt_add_le` in Mathlib: 0 hits; proved as `Step5IIIKer_sqrt_add_le`); `push_neg` is deprecated (use `push Not`).
## (d) Open issues and paper-delta candidates
- Hub: add `import RBM3D.BA.Step5IIIKer` and `import RBM3D.BA.Step5IIIKer2` after the last import line of `RBM3D.lean`. Target 2 is not proved (dropped by the route, no consumer under (b)). U5d: `baStep5IIITailSqQV_holds` with (H3) from `baStep5III_uKer_far` at `D₂ = D`; (H1), (H2) stay with U5b/U5c/U5d.
- T2481a (= T2459a, kernel part): `(neiwuj)` at BA on `Step2Gen_UN` at `baFM`, guarded per-index form (`0 < lam0 n`, `lam0 n ≤ sz.lam n`, `lam0 n ≤ 𝔡⁻¹`) instead of `‖m‖ = 1`; proved through `(prop:ThfadC)` (the paper's hint `3_5:2364`), `Cc = W₁²(d, 𝔡⁻¹, κ)`.
- T2481b (= T2459b): near cut `2ℓ*` (far pair ⇒ `|a_i - b_i| ≥ ℓ*` or `|a_i - b'_i| ≥ ℓ*`). T2481c (= T2459e): the Θ-level far field at mixed charges from the K-level `baEMn2ExpHK` (4 (a), probe copy).
- T2481d: the BA `tailtoTailSq` against band 7g (`tailtoTailSq_kernelGen`, `Induction/TailtoTailSq.lean:906`): near cut `2ℓ*` (band `ℓ*`); (H3) on `uKer`, all four charge pairs, beyond `ℓ*` (band: `Θ_w` beyond `(1/8)ℓ*ℓ_w`); `Cq = 2W₂²(d, 𝔡⁻¹, κ)` (band `18e^{8d+2}`); `BAReal`, `0 < lam0 ≤ 𝔡⁻¹`, `lam0 ≤ sz.lam` in place of `|E| ≤ 2`. T2481e: 4 (b), the `uKer` far field uniform in `0 ≤ v ≤ w ≤ t₀`, `sz.lam² ≤ 1 - w`, for the QV bound `3_5:2364-2383`.
Scratch files (scratchpad `T2481/`): `stmt_diff.py`, `chk2481.lean`, `ax.lean`, `prechk.lean`, `prechk0.lean`, `T2459Pins.lean` (= `git show t/T2459:RBM3D/Probe/T2459Pins.lean`), `report_b.sh`.
