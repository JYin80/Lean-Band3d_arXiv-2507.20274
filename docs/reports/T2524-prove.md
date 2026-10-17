Prover model: claude-sonnet-5-5

## (a) Math preflight — Fri Oct 16 23:50:30 UTC 2026
Mathematics only; no Lean. Data: the sz0 family of `Defs/Sizes:260` (`L=4(n+1), W=x^5, lam=x^-6, x=2(n+1), N=(WL)^d`) at `d=3` (the merged data) and `d=4`; flow `(κ,ε,𝔡)=(1/2,1/10,1/10)`. Line refs `X:N` = `RBM3D/X.lean:N` at main afab243f.

### (i) Exponent table (d = 3 | d = 4; constraint; slack). "d-free" = same number at every d
| # | item (where the U5 files fix it at 3) | d=3 \| d=4 | constraint | slack |
|---|---|---|---|---|
| 1 | dimension `d`; `Sizes 3`/`Zd 3` (116 places) | 3 \| 4 | `3 ≤ d` | — |
| 2 | band `𝔠`, `Bandwidth` `Sizes:168` | 1/6 \| 1/8 (=1/(2d)) | `W ≥ N^𝔠`; `W^d ≤ N` forces `𝔠 ≤ 1/d`; sz0: `𝔠 ≤ log W/log N` (→ 5/(6d)) | n=1: .2564-.1667 \| .1923-.125 |
| 3 | `(eq:WO)` `WO 𝔡` `Sizes:164`, `𝔡=1/10` | `W^(-d/2+𝔡)=x^-7` \| `x^-9.5` ≤ `lam=x^-6` ≤ 10 | `𝔡 ≤ d/2-6/5` for this lam | x^1 \| x^3.5; 𝔡max .3 \| .8 |
| 4 | `lam²W^d` (`W^3` in Good:569, Walk2:99, Walk:282-285) | `x^3=W^(3/5)` \| `x^8=W^(8/5)` | ≥ `W^(2𝔡)=x^1` (`lam_sq_mul_pow_ge`); ⇒ `τ=(W^d(1-u))^-1 ≤ W^(-2𝔡)`, `lam² ≥ W^-d` | x^2 \| x^7 |
| 5 | `ε₁=min(𝔡/8,1/4)`, `ε₀=1/100`, closure `ε₀<𝔡/4` | .0125, .01, .025 (d-free) | `ε₀<ε₁` | .0025 |
| 6 | four closure exponents (`J²τ`, `τ^½J^{3/2}`, `τ^½J³`, mart. `τ^¼J^{3/2}√log W`) | W^-.180, -.085, -.070, -.035 (d-free: only `τ≤W^-2𝔡` enters) | < `ε₀` | .19, .095, .08, .045 |
| 7 | floor premise `(L^dW^{6d})² ≤ W^D` (`(L^3W^{6·3})²`: Good2:55,136; Walk:256,1320; `Dst-2·3`) | D=40 used \| need `W^(13d)`: 39 \| 52 (sz0: `L²≤W`) | `D ≥ 2·(log L^d W^{6d})/log W`; in general `D ≥ 2/𝔠+12d`=48 \| 64 (`L^d ≤ N ≤ W^{1/𝔠}`) | D0-13d = 9 \| 12; exact n<3000 |
| 8 | `D₀=2/𝔠+12d`, `D*=max(D,D₀)+2d+1`, `D₂=2D*+8/𝔠+3d+1` (PfStep5:34-35) | 48, 55, 168 \| 64, 73, 223 | band proof's exponents, already in `d` | — |
| 9 | `(W^3)^7` in `hRm` (Walk2:108); `W^(-Dst)` | `W^{7d} ≤ N^7`; `W^-Dst ≥ N^(-Dst/d)`, Dst/d=18.33 \| 18.25 | grid `Δ` chosen from `N^7, Dst/d` | n=0 exact |
| 10 | `W^{θ(3(Cd+1))}` (Good:463, Walk:1323) | `(W^d)^{θ(Cd+1)} ≤ N^{θ(Cd+1)}` | `θ∈(0,1)`, `Cd>0` | d-free in N |
| 11 | `ℓ*=(log W)^{3/2}`, `(log W)^{3/4}` (Good2:100, Edet:441,462,760) | paper threshold `7_8:95,97`, d-free | `log W ≥ 4`: 3.466 at n=0 (fails), 6.931 at n=1 | n≥1 |
| 12 | ball count `(2ℓ*+1)^d ≤ (1+log P)^{2d}`, `P=L^dW^{6d}` (Edet:757) | n=1: 37.5 ≤ 17425 \| 30861 | base inequality, `d` enters only via `log P` | ×465 \| ×823 |
| 13 | lattice sums `S_d=(1+1536d⁴)^d`, `C_sq=5(1+24576d⁴)^d`, `10^12(1600d⁴)^d` (LemDecCalE:312, EwG:219; already generic) | 1.926e15, 3.944e19, 2.177e27 \| 2.391e22, 7.834e27, 2.815e34 | `Σ_{Z^d}e^{-c√\|y\|∞} ≤ (1+96d⁴/c⁴)^d` | true sums 3.69e5 \| 1.65e8 (c=1/2) |
| 14 | CT/Prop5 constants `BAct_C=16d²/κ³`, `BAct_rate`, `A`, `S=expC(d-2)c`, `S1`, `μ` (Ker:187; generic in `d`) | c=4.158e-3, μ=2.8e-29 \| c=3.120e-3, μ=9.3e-35 | `μ>0`; `Cc` L-independent (as at d=3) | observed CU=1.0039 \| 1.0052 |
| 15 | `Bparam` `(K+1)^(d-2)` at `K=0` (Params:36); `Bctl∈[τ/2,2τ]` | 1 \| 1 | `g²≤1-u`, `L≥1` | d-free |
| 16 | `mS L g := BAmSubord 3 L g wI` (MFixedPoint:865); `g²L^3 ≤ 1/64` (FlowPins:1131,1147) | `g²L^d` n=0: 1/64 (equality) \| **1/16** | `Im m ≥ 1.2/(1.44+g²L^d)`; needs ≥ κ=1/2 and `t0=Im m/1.2 > t=1/2` | .824 \| **.7987** (4/5 shortcut fails at d=4,n=0; n≥1 holds) |
| 17 | Yukawa normalisation of the shape check (design T2459 `cont`: `e^{-R/ℓ}/(4πℓ²R)`) | `G_d=(2π)^{-d/2}ℓ^{-d}r^{1-d/2}K_{d/2-1}(r)`, `r=R/ℓ`; threshold ℓ*: 167.0 \| 243.7 | `ℓ_K<ℓ*`; `ℓ_K²=tD'/(2(1-t))` | `ℓ_K=0.020` (g=1/64, both d) |

### (ii) Instance (d=4, n=1) beside d=3
`(L,W,lam,N)=(8, 1024, 1/4096, 4.5036e15)` at d=4 (N=5.4976e11 at d=3); `𝔠=1/8` (1/6), `𝔡=1/10`, `κ=1/2`, `ε=1/10`, `s=t=1/2`, `ε₀=1/100`, `D=13d=52` (39). Hypotheses: `Admissible` (rows 2-3), `BAdom` (Im m=.83333≥κ; `N^{-.9}≤.3667≤Im z`; `Im z≤1`), `s<t≤t0=.69444`, `STReg5III` (lam²≤1/2), `1≤lam²W^d` (64 \| 65536), `4≤log W`, floor, `J≤W^{1/2}`, `ε₀<ε₁`: all hold. External hypotheses (Step 2-4 predicates of `STIngR5gL`, `UNL32`) stay hypotheses; their d-free numerics are rows 5-6 and CU/ward of the flow lines.
Command: `python3 preflight.py sizes exps floor ms sums consts flow yuk` (scratch `T2524/preflight.py`, reuses `num.py`+`stab.py` of `t/T2459` 2a6ad6e0, `stab.d` set to 3, 4); output verbatim:
```
sz0-type sequence L=4(n+1), W=(2(n+1))^5, lam=(2(n+1))^-6, N=(WL)^d; kappa,eps,c,dd = 1/2,1/10,c_d,1/10
d=3 n= 0 L=4 W=32 lam=x^-6=1.562e-02 N=(WL)^d=2.0972e+06 | c_d=1/(2d)=1/6: N^c<=W exact True (L<=W: True); sup c at n = log W/log N = 0.2381 (n->inf: 5/(6d) = 0.2778); N^(-1+eps) = 2.044e-06 <= 1/4: True
d=3 n= 1 L=8 W=1024 lam=x^-6=2.441e-04 N=(WL)^d=5.4976e+11 | c_d=1/(2d)=1/6: N^c<=W exact True (L<=W: True); sup c at n = log W/log N = 0.2564 (n->inf: 5/(6d) = 0.2778); N^(-1+eps) = 2.715e-11 <= 1/4: True
d=4 n= 0 L=4 W=32 lam=x^-6=1.562e-02 N=(WL)^d=2.6844e+08 | c_d=1/(2d)=1/8: N^c<=W exact True (L<=W: True); sup c at n = log W/log N = 0.1786 (n->inf: 5/(6d) = 0.2083); N^(-1+eps) = 2.594e-08 <= 1/4: True
d=4 n= 1 L=8 W=1024 lam=x^-6=2.441e-04 N=(WL)^d=4.5036e+15 | c_d=1/(2d)=1/8: N^c<=W exact True (L<=W: True); sup c at n = log W/log N = 0.1923 (n->inf: 5/(6d) = 0.2083); N^(-1+eps) = 8.162e-15 <= 1/4: True
log W (hlog: 4 <= log W needed): n=0: 3.466  n=1: 6.931 ; lam^2 W^d at n=1 (x=4): d=3: 64  d=4: 65536
exact integer scan n = 0..5999 (d = 3, 4): L<=W, L^2<=W, size>=2^21 (d=3) / 2^28 (d=4): True True True
(eq:WO) and lam^2 W^d >= W^(2 dd), exponents in x = 2(n+1) (W = x^5):
d=3: W^(-d/2+dd) = x^-7 <= lam = x^-6: True (slack 1 powers of x; max dd allowed by this lam: 3/10); lam<=1/dd=10: True; lam^2 W^d = x^3 = W^3/5 >= W^(2dd) = x^1 = W^1/5: True (slack x^2)
d=4: W^(-d/2+dd) = x^-19/2 <= lam = x^-6: True (slack 7/2 powers of x; max dd allowed by this lam: 4/5); lam<=1/dd=10: True; lam^2 W^d = x^8 = W^8/5 >= W^(2dd) = x^1 = W^1/5: True (slack x^7)
closure exponents (d-free: only lam^2 W^d >= W^(2dd) enters; tau = (W^d(1-u))^-1 <= W^(-2dd) at 1-u >= lam^2):
eps1 = min(dd/8,1/4) = 1/80 = 0.0125; eps0 = 1/100 < eps1: True; closure needs eps0 < dd/4 = 1/40: True
  J^2 tau <= W^(-9/50) = W^-0.180  < eps0: True (margin 0.190); same at d = 3 and d = 4
  tau^(1/2) J^(3/2) <= W^(-17/200) = W^-0.085  < eps0: True (margin 0.095); same at d = 3 and d = 4
  tau^(1/2) J^3 <= W^(-7/100) = W^-0.070  < eps0: True (margin 0.080); same at d = 3 and d = 4
  martingale sqrt(log W) J^(3/2) tau^(1/4) <= W^(-7/200) = W^-0.035  < eps0: True (margin 0.045); same at d = 3 and d = 4
Bparam d L g t K at K = 0: ((K+1)^(d-2))^-1 = [1, 1] (d-free); (1-u) in [lam^2, 1]: tau/2 <= Bctl <= 2 tau needs only g^2<=1-u, L>=1
floor premise (L^d W^(6d))^2 <= W^D, D0 = 2/c + 12 d (c = 1/(2d) => D0 = 16 d), D* = D0 + 2d + 1 (PfStep5 header), D2 = 2 D* + 8/c + 3d + 1, (3,32,55) = pfStep5Grid_level 3 32 55 at FlowPins:1143
d=3: c=1/6 D0=48 D*=55 D2=168; sz0: L^2<=W so (L^dW^6d)^2 <= W^(13d)=39: exact n<3000: True; <= W^D0: True; n=0 exact: L^6W^36 = 2^192 <= W^39 = 2^195: True  (d=3: Good2:136 uses D=40; 13d=39)
d=4: c=1/8 D0=64 D*=73 D2=223; sz0: L^2<=W so (L^dW^6d)^2 <= W^(13d)=52: exact n<3000: True; <= W^D0: True; n=0 exact: L^8W^48 = 2^256 <= W^52 = 2^260: True  (d=3: Good2:136 uses D=40; 13d=39)
W^d <= N, so W^(7d) <= N^7, W^(2 theta d (Cd+1)) <= N^(2 theta (Cd+1)), W^(-Dst) >= N^(-Dst/d) (W_rpow_le, Defs/Sizes:~232):
  d=3 n=0: W^d=32768 <= N=2097152: True; (W^d)^7=4.056e+31 <= N^7: True; Dst/d at c=1/(2d) = 55/3 = 18.333
  d=4 n=0: W^d=1048576 <= N=268435456: True; (W^d)^7=1.394e+42 <= N^7: True; Dst/d at c=1/(2d) = 73/4 = 18.250
Im m_S lower bound wI.im/(|wI|^2 + g^2 L^d) (BASelf_subord d L g; FlowPins:1100), wI = 6i/5; t0 = Im m/Im w; flow needs kappa=1/2 <= Im m, 1/2 < t0
  d=3 n=0 g=1/64 L=4: g^2 L^d = 1.5625e-02 (<=1/64: True) Im m >= 0.82439 (>=4/5: True; >=1/2: True); Im m <= 5/6; t0 >= 0.68699 > 1/2: True; Im z = 6/5 - Im m in [0.3667,0.3756] within [N^(-1+eps),1]: True
  d=3 n=1 g=1/4096 L=8: g^2 L^d = 3.0518e-05 (<=1/64: True) Im m >= 0.83332 (>=4/5: True; >=1/2: True); Im m <= 5/6; t0 >= 0.69443 > 1/2: True; Im z = 6/5 - Im m in [0.3667,0.3667] within [N^(-1+eps),1]: True
  d=4 n=0 g=1/64 L=4: g^2 L^d = 6.2500e-02 (<=1/64: False) Im m >= 0.79867 (>=4/5: False; >=1/2: True); Im m <= 5/6; t0 >= 0.66556 > 1/2: True; Im z = 6/5 - Im m in [0.3667,0.4013] within [N^(-1+eps),1]: True
  d=4 n=1 g=1/4096 L=8: g^2 L^d = 2.4414e-04 (<=1/64: True) Im m >= 0.83319 (>=4/5: True; >=1/2: True); Im m <= 5/6; t0 >= 0.69433 > 1/2: True; Im z = 6/5 - Im m in [0.3667,0.3668] within [N^(-1+eps),1]: True
lattice sums sum_{y in Z^d} exp(-c sqrt|y|_inf) vs the generic Lean bound (1 + 96 d^4 / c^4)^d (LemDecCalE:312 c=1/2: 1536 d^4; EwG:219 c=1/4: 24576 d^4)
  d=3 c=0.5: sum (r<400000) = 3.6866e+05 <= bound 1.9259e+15: True
  d=3 c=0.25: sum (r<400000) = 2.3593e+07 <= bound 7.8884e+18: True
  d=3 c=0.05: sum (r<4000000) = 3.6864e+11 <= bound 1.9259e+27: True
  d=4 c=0.5: sum (r<400000) = 1.6515e+08 <= bound 2.3907e+22: True
  d=4 c=0.25: sum (r<400000) = 4.2279e+10 <= bound 1.5668e+27: True
  d=4 c=0.05: sum (r<4000000) = 1.6515e+16 <= bound 2.3907e+38: True
  d=3: S_d=(1+1536d^4)^d=1.926e+15  C_sq=5(1+24576d^4)^d=3.944e+19  lossE2 const 10^12(1600d^4)^d=2.177e+27
  d=4: S_d=(1+1536d^4)^d=2.391e+22  C_sq=5(1+24576d^4)^d=7.834e+27  lossE2 const 10^12(1600d^4)^d=2.815e+34
ball count (2 l*+1)^d <= (1+log P)^(2d), P = L^d W^(6d), l* = (log W)^(3/2):
  d=3 n=1: 2l*+1=37.50 <= (1+log P)^2 = 17425.3: True; log W>=4: True
  d=4 n=1: 2l*+1=37.50 <= (1+log P)^2 = 30861.0: True; log W>=4: True
Lean constants BAct_C = 16 d^2/kappa^3, BAct_rate = min(log(1+kappa/(4 d Lam)), kappa/2), A = 4 (C/c)^2, S = expC (d-2) c, S1 = (2/(e c)) expC (d-2) (c/2), mu = min(c, 1/(2 A S1)); kappa = 1/2, Lam = 1/dd = 10
  d=3: c=4.1580e-03 C=1152.0 A=3.070e+11 S=2.055e+13 S1=5.819e+16 mu=2.798e-29  Cc=(3e^(1/(4mu)))^2 = exp(1.787e+28)
  d=4: c=3.1201e-03 C=2048.0 A=1.723e+12 S=4.155e+17 S1=3.136e+21 mu=9.253e-35  Cc=(3e^(1/(4mu)))^2 = exp(5.404e+33)
kernel numerics at the sz0 flow point (g_n, L_n), w = 1.2 i, K = |M|^2, t_b = t0 (g^2 <= 1-t0 for g<=1/64): d = 3 and 4
  d=3 n=0 L= 4 g=1/64: D'=0.0003 ell_K=0.020 Im m=0.83249 t0=0.69374 (>1/2: True) g0<=g: True 1-t0=0.3063>=g^2: True ward=0.0e+00 mu_obs=>=5 (cap) gap(t0)=0.306 CU=1.0039
  d=3 n=1 L= 8 g=1/4096: D'=0.0000 ell_K=0.000 Im m=0.83333 t0=0.69444 (>1/2: True) g0<=g: True 1-t0=0.3056>=g^2: True ward=4.4e-16 mu_obs=>=5 (cap) gap(t0)=0.306 CU=1.0000
  d=3 n=2 L=12 g=1/46656: D'=0.0000 ell_K=0.000 Im m=0.83333 t0=0.69444 (>1/2: True) g0<=g: True 1-t0=0.3056>=g^2: True ward=4.4e-16 mu_obs=>=5 (cap) gap(t0)=0.306 CU=1.0000
  d=4 n=0 L= 4 g=1/64: D'=0.0003 ell_K=0.020 Im m=0.83221 t0=0.69351 (>1/2: True) g0<=g: True 1-t0=0.3065>=g^2: True ward=2.2e-16 mu_obs=4.750 gap(t0)=0.306 CU=1.0052
  d=4 n=1 L= 8 g=1/4096: D'=0.0000 ell_K=0.000 Im m=0.83333 t0=0.69444 (>1/2: True) g0<=g: True 1-t0=0.3056>=g^2: True ward=4.4e-16 mu_obs=>=5 (cap) gap(t0)=0.306 CU=1.0000
  d=4 n=2 L=12 g=1/46656: D'=0.0000 ell_K=0.000 Im m=0.83333 t0=0.69444 (>1/2: True) g0<=g: True 1-t0=0.3056>=g^2: True ward=2.2e-16 mu_obs=>=5 (cap) gap(t0)=0.306 CU=1.0000
Yukawa normalisation (1-t)Theta ~ G_d(R; ell): G_3 = e^(-R/ell)/(4 pi ell^2 R) (design T2459:cont); general d: (2pi)^(-d/2) ell^-d r^(1-d/2) K_{d/2-1}(r), r=R/ell
  d=3 closed form 7.644311e-05 vs Bessel 7.644311e-05
  d=4 Hankel check: int_0^inf x^2 J_1(bx)/(x^2+a^2) dx = 0.01088873 vs a K_1(ab) = 0.01088873
  threshold ell*(logCc=0): Lambda_d(ell) = max_R [log G_d(R;ell) + sqrt(2R)/2] > 0 iff ell > ell*; d=3 reproduces 167.0 of T2459:cont
  d=3: ell* = 167.0
  d=4: ell* = 243.7
```
n=0 at d=4 fails only the 4/5 shortcut of row 16 (Im m ≥ .79867 ≥ 1/2, t0 ≥ .66556 > 1/2 still hold); the instance is taken at n=1 (also needed for `log W ≥ 4`).

### Verdict
- Targets: D1-D6 design gate (no theorem proved here). **PASS**: every row of (i) closes at d=4; no hypothesis set is empty; no exponent fails. Rows 4, 7, 9, 10, 16 are d-dependent constants of the U5 files at 3 (class (b)); rows 5, 6, 11, 12, 15 are d-free; rows 8, 13, 14 are already generic in `d`.
- Finding for D1/D4: `mS`/`zS`/`FlowPinsInst.sz0_lam_L`, `mS_im_half` are stated at `3` (instance data, not the theorems), and `g²L^3 ≤ 1/64` becomes `g²L^d ≤ 1/64`, false at d=4, n=0 (row 16).

## (a′) Preflight corrections — Sat Oct 17 00:55:29 UTC 2026
Observation, no verdict change: row 10 cites Good:463 for `W^{θ(3(Cd+1))}`; that exponent is at Good:407 (`BAStep5IIIGood`, conjunct (vi)) and Walk:1323; Good:463 carries the (iii) far field `W^{-(D+3)}`, also `d`-dependent (design report §1, rows `BAStep5IIIGood`, `baStep5IIIGoodThm_holds`, `Step5IIIWalk_pertime`).  Row 16's flow-instance data (`FlowPinsInst.zSeq`, `flow_sz0`, `half_lt_t0`, `sz0_lam_pos`, `sz0_lam_L`, `mS_im_half`, BA/FlowPins:1131-1254) are deleted by T2523 (`deadcheck.py`, design report §1): no row needs them.

## (b) Script output (report-only design ticket: the deliverables are `docs/reports/T2524-design.md`, 240 lines, and the probe `RBM3D/Probe/T2524Pins.lean`, 409 lines, branch `t/T2524` only)
Branch `t/T2524` (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2524`), five commits on `main` afab243f, only the probe.  Scripts: scratchpad `T2524/` (`/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d6ebe5cd-b9c4-4c2a-9b3c-fa912982a931/scratchpad/T2524`; `probe_check.sh`, `pipeline.sh`, `census_summary.py`, `census_annot.py`, `price.sh`, `deadcheck.py`, `extract_targets.py`); the design report pastes the census, prices and experiment outputs.  The block below is `probe_check.sh` and its companions.
```
$ lake build RBM3D.Probe.T2524Pins 2>&1 | tail -3   # cwd = RBM3D-wt/T2524
 RBM.Gauss.Sizes.STLWT].
non-vacuity certificates: 0 of 113 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4443 jobs).
$ bash probe_check.sh   # cwd = RBM3D-wt/T2524
lines:      409
lake env lean RBM3D/Probe/T2524Pins.lean: exit=0, output lines=0
lake build RBM3D.Probe.T2524Pins: exit=0, last line: Build completed successfully (4443 jobs)., warning/error lines in the probe file: 0
forbidden (sorry|admit|axiom|native_decide|inductive|structure): 0
defs: 8, theorems: 31, examples: 9
#print axioms, every probe theorem: 31 of 31 with exactly [propext, Classical.choice, Quot.sound]; other lines: 0
--- name clash: declarations named T2524_ on main (RBM3D/), outside the probe, and on the other t/* branches
main: 0 files; this tree outside the probe: 0
other t/* branches: 0 files
--- git diff --stat main...t/T2524 -- RBM3D
 RBM3D/Probe/T2524Pins.lean | 409 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 409 insertions(+)
$ lake env lean axioms_probe.lean   # #print axioms of the 31 probe theorems, each [propext, Classical.choice, Quot.sound]:
  T2524_baPfStep5_of_walk, T2524_baStep5III_holds_any, T2524_baThm27L_of_texts, T2524_walk_three
  T2524_fromWalk_three, T2524_goodThm_three, T2524_baStep5III_three, T2524_baThm27L_three
  T2524_walk_of_walk_at, T2524_vol, T2524_tau_le, T2524_level
  T2524_floor, T2524_logbound, T2524_card_le, T2524_Wpow
  T2524_sz4_L_le_W, T2524_sz4_size_le, T2524_sz4_bandwidth_at, T2524_sz4_tendsto
  T2524_sz4_WO_at, T2524_sz4_adm, T2524_sz4_vol, T2524_sz4_tau
  T2524_sz4_floor, T2524_sz4_card, T2524_Thm27_of_texts, T2524_final_shape
  T2524_Thm27_three, T2524_Step5IIIAny_of_texts, T2524_baThm27L_all
$ lake env lean docs/tickets/checks/T2524-check.lean; echo exit=$?   # acceptance: the check compiles
exit=0 (output lines 33, lines containing 'error': 0)
$ lake env lean scan_probe.lean   # RBM.Audit.scanPremises (registry rule of Test/Axioms.lean)
scanPremises over the environment with the probe: 128 premises in all; probe premises: [RBM.BA.T2524_WalkAt]
$ python3 deadcheck_probe.py   # every identifier of the probe that is an RBM3D declaration, against the T2523 dead set (roots core + G1-G4)
names deleted by T2523: none
$ python3 extract_targets_b.py   # the targets of the probe (the chain and the final texts), extracted from the file
:89   theorem T2524_baPfStep5_of_walk (d : ℕ) :
:90       T2524_BAStep5IIIWalk d → T2524_BAStep5IIIFromWalk d →
:91         STPfStep5gL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 := by
:100  theorem T2524_baStep5III_holds_any (d : ℕ) (hd : 3 ≤ d) (walk : T2524_BAStep5IIIWalk d) (fromWalk : T2524_BAStep5IIIFromWalk d) :
:101      STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 :=
:105  theorem T2524_baThm27L_of_texts (d : ℕ) (hd : 3 ≤ d) (walk : T2524_BAStep5IIIWalk d) (fromWalk : T2524_BAStep5IIIFromWalk d)
:106      (h32 : RBM.Univ.UNL32) : BAThm27L d :=
:374  def T2524_Step5IIIAny : Prop :=
:383  theorem T2524_baThm27L_all (h5 : T2524_Step5IIIAny) (h32 : RBM.Univ.UNL32) : T2524_Thm27 :=
:355  def T2524_Thm27 : Prop := ∀ d : ℕ, 3 ≤ d → BAThm27L d
:364  theorem T2524_final_shape (hW : ∀ d : ℕ, 3 ≤ d → T2524_BAStep5IIIWalk d) (hF : ∀ d : ℕ, 3 ≤ d → T2524_BAStep5IIIFromWalk d) :
:365      RBM.Univ.UNL32 → (RBM.Endpoints.decol ∧ RBM.Endpoints.locSC ∧ RBM.Endpoints.QUE ∧ RBM.Endpoints.BUniv ∧ RBM.Endpoints.QDiff) ∧
:366        T2524_Thm27 :=
:370  theorem T2524_Thm27_three (h : T2524_Thm27) : RBM.Endpoints.Thm27 := h 3 le_rfl
$ sed -n 132,136p, 394,407p RBM3D/Probe/T2524Pins.lean   # the compiled nonempty instances: the chain at d = 3 (UNL32 only) and the d = 4 conjuncts of Thm27
:132  
:133  /-- **Nonempty instance of the chain at `d = 3`**: `BAThm27L 3` with every deterministic hypothesis discharged by merged theorems;
:134  `UNL32` (the borrowed input) is the only hypothesis. -/
:135  theorem T2524_baThm27L_three (h32 : RBM.Univ.UNL32) : BAThm27L 3 :=
:136    T2524_baThm27L_of_texts 3 le_rfl T2524_walk_three T2524_fromWalk_three h32
:394  /-- **Closing condition (vii), the `d = 4` instance**: the four conjuncts of `Thm27` at `d = 4` that read only `Sizes d` and `Admissible`
:395  (decol, locSC, QUE, QDiff) applied to `T2524_sz4` (`T2524_sz4_adm`, every `n`, `n = 0` included).  The rows' texts are hypotheses here (they are
:396  theorems after the rows), `UNL32` is the borrowed input.  The BUniv conjunct reads the UN spectral data (`S0`, `fp`, `clsκ`: `d = 3` data). -/
:397  example (hW : ∀ d : ℕ, 3 ≤ d → T2524_BAStep5IIIWalk d) (hF : ∀ d : ℕ, 3 ≤ d → T2524_BAStep5IIIFromWalk d)
:398      (h32 : RBM.Univ.UNL32) : True := by
:399    have h := T2524_Thm27_of_texts hW hF h32 4 (by norm_num)
:400    have _ := h.1 (by norm_num) (1 / 8) (1 / 10) T2524_sz4 T2524_sz4_adm (1 / 2) 1 1 (by norm_num) (by norm_num) (by norm_num)
:401    have _ := h.2.1 (by norm_num) (1 / 8) (1 / 10) T2524_sz4 T2524_sz4_adm (1 / 2) (1 / 10) 1 1 (by norm_num) (by norm_num) (by norm_num)
:402      (by norm_num)
:403    have _ := h.2.2.1 (by norm_num) (1 / 8) (1 / 10) T2524_sz4 T2524_sz4_adm (1 / 2) (by norm_num) (1 / 30) (1 / 60) (1 / 300)
:404      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
:405    have _ := h.2.2.2.2 (by norm_num) (1 / 8) (1 / 10) T2524_sz4 T2524_sz4_adm (1 / 2) (1 / 10) 1 1 (by norm_num) (by norm_num) (by norm_num)
:406      (by norm_num)
:407    trivial
```
Ports: none (no RBM1D/RBM2D text is copied; `git diff --stat` of the RBM1D/RBM2D trees is not applicable).  Name clash: the grep in `probe_check.sh` above (`T2524_`: 0 files on main, 0 in this tree outside the probe, 0 on the other `t/*` branches).

Narrative (results only).
- **Verdict:** PASS.  The census (design §1) has 24 rows in the five U5 files that change: 151 class (a) and 85 class (b) tokens in the heads, **0 class (c)**; Edet, Edet2, Ker, Ker2 are general already; 1,006 lines of instance tails are `d = 3` data (deleted by T2523 with the `example`s).
- **Experiment** (scratch, design §3-§4): 13 lexical rules plus 77 hand-edited head lines and 16 tail call sites turn Good, Good2, Walk, Walk2, Targets into general-`d` files that compile in import order against unchanged imports and prove `baStep5III_holds_any : ∀ d, 3 ≤ d → STStep5IIIgL d …` with standard axioms; the in-place price is 272 head edit lines (+ ≈ 30 doc lines), the new-file price 3,251 copied lines.
- **Probe:** the D2 texts, the chain to `BAThm27L d`, the `d = 3` recovery (the texts at `d = 3` are the merged texts; the merged theorems prove them; the chain at `d = 3` has `UNL32` only), the (b) inequalities, `Sizes 4` with `Admissible (1/8) (1/10)` for every `n`, the `d = 4` conjuncts of `Thm27`, the exact type `T2524_Step5IIIAny` and the producer `T2524_baThm27L_all`.
- **Amend 1:** BAD-C2 column and method (design §1), BAD-C3 three "no" (§7), `d = 4` instance 78 lines (§5), BAD-C4 in place (§4), the exact-type texts and `d = 3` recoveries (§5).
- **Stop rules:** no merged file changed (`git diff --stat` above); probe 409 ≤ 500; no open (c) item; design report 240 ≤ 300 lines (`wc -l`); no `sorry`/`axiom` in the probe.
- **Instances:** every probe theorem that is an endpoint (`T2524_baThm27L_of_texts`) has the nonempty instance at `d = 3` (`T2524_baThm27L_three`, only `UNL32`); the `d = 4` instance keeps the two texts as hypotheses (they are the rows' theorems); no `N = 0`, no empty index set: `T2524_sz4` has `L = 4(n+1) ≥ 4`, `W = (2(n+1))^5 ≥ 32`.

## (c) Verified Mathlib names used (resolved by `#check`, `lake env lean names.lean`, exit 0, 0 errors; names verified absent: none)
- @Real.one_le_rpow : ∀ {x z : ℝ}, 1 ≤ x → 0 ≤ z → 1 ≤ x ^ z
- @inv_le_iff_one_le_mul₀' : ∀ [PosMulReflectLT G₀] {a b : G₀}, 0 < a → (a⁻¹ ≤ b ↔ 1 ≤ a * b)
- @inv_anti₀ : ∀ [PosMulReflectLT G₀] [MulPosReflectLT G₀] {a b : G₀}, 0 < b → b ≤ a → a⁻¹ ≤ b⁻¹
- @Real.rpow_pos_of_pos : ∀ {x : ℝ}, 0 < x → ∀ (y : ℝ), 0 < x ^ y
- @Real.rpow_neg : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), x ^ (-y) = (x ^ y)⁻¹
- Real.rpow_natCast : ∀ (x : ℝ) (n : ℕ), x ^ ↑n = x ^ n
- @Real.rpow_mul : ∀ {x : ℝ}, 0 ≤ x → ∀ (y z : ℝ), x ^ (y * z) = (x ^ y) ^ z
- @Real.rpow_nonneg : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), 0 ≤ x ^ y
- @Real.rpow_le_rpow : ∀ {x y z : ℝ}, 0 ≤ x → x ≤ y → 0 ≤ z → x ^ z ≤ y ^ z
- @Real.rpow_le_rpow_of_exponent_le : ∀ {x y z : ℝ}, 1 ≤ x → y ≤ z → x ^ y ≤ x ^ z
- @Real.pow_rpow_inv_natCast : ∀ {x : ℝ} {n : ℕ}, 0 ≤ x → n ≠ 0 → (x ^ n) ^ (↑n)⁻¹ = x
- Real.log_pow : ∀ (x : ℝ) (n : ℕ), Real.log (x ^ n) = ↑n * Real.log x
- @Real.log_le_log : ∀ {x y : ℝ}, 0 < x → x ≤ y → Real.log x ≤ Real.log y
- @inv_pos : ∀ [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
- @pow_pos : ∀ {a : M₀} [PosMulStrictMono M₀] [ZeroLEOneClass M₀], 0 < a → ∀ (n : ℕ), 0 < a ^ n
- @mul_pos : ∀ {α : Type u_1} {a b : α} [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
- @mul_le_mul : ∀ {α : Type u_1} {a b c d : α} [PosMulMono α] [MulPosMono α], a ≤ b → c ≤ d → 0 ≤ c → 0 ≤ b → a * c ≤ b * d
- @mul_le_mul_of_nonneg_left : ∀ {α : Type u_1} {a b c : α} [PosMulMono α], b ≤ c → 0 ≤ a → a * b ≤ a * c
- @mul_le_mul_of_nonneg_right : ∀ {α : Type u_1} {a b c : α} [MulPosMono α], b ≤ c → 0 ≤ a → b * a ≤ c * a
- @le_mul_of_one_le_left : ∀ {α : Type u_1} {a b : α} [MulPosMono α], 0 ≤ b → 1 ≤ a → b ≤ a * b
- @pow_le_pow_left₀ : ∀ {a b : M₀} [PosMulMono M₀] [MulPosMono M₀], 0 ≤ a → a ≤ b → ∀ (n : ℕ), a ^ n ≤ b ^ n
- @one_le_pow₀ : ∀ {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀], 1 ≤ a → ∀ {n : ℕ}, 1 ≤ a ^ n
- @inv_le_one_of_one_le₀ : ∀ [PosMulReflectLT G₀] {a : G₀} [ZeroLEOneClass G₀], 1 ≤ a → a⁻¹ ≤ 1
- Fintype.card_prod : ∀ (α : Type u_1) (β : Type u_2) , Fintype.card (α × β) = Fintype.card α * Fintype.card β
- @Fintype.card_fun : ∀ {α : Type u_1} {β : Type u_2} , Fintype.card (α → β) = Fintype.card β ^ Fintype.card α
- Fintype.card_bool : Fintype.card Bool = 2
- Fintype.card_fin : ∀ (n : ℕ), Fintype.card (Fin n) = n
- ZMod.card : ∀ (n : ℕ) , Fintype.card (ZMod n) = n
- @Nat.le_self_pow : ∀ {n : ℕ}, n ≠ 0 → ∀ (a : ℕ), a ≤ a ^ n
- @Nat.le_mul_of_pos_left : ∀ {n : ℕ} (m : ℕ), 0 < n → m ≤ n * m
- @Nat.pow_le_pow_left : ∀ {n m : ℕ}, n ≤ m → ∀ (i : ℕ), n ^ i ≤ m ^ i
- @Nat.pow_le_pow_right : ∀ {n : ℕ}, n > 0 → ∀ {i j : ℕ}, i ≤ j → n ^ i ≤ n ^ j
- @Filter.tendsto_atTop_mono : ∀ {α : Type u_1} {β : Type u_2} {l : Filter α} {f g : α → β}, (∀ (n : α), f n ≤ g n) → Filter.Tendsto f l Filte
- @tendsto_natCast_atTop_atTop : ∀ [IsOrderedRing R] [Archimedean R], Filter.Tendsto Nat.cast Filter.atTop Filter.atTop
- @Nat.cast_nonneg : ∀ {α : Type u_1} [IsOrderedRing α] (n : ℕ), 0 ≤ ↑n

## (d) Open issues and paper-delta candidates
- **O1.** The experiment's scripts are in the scratchpad `T2524/` (`gen_rules.py`, `patchF_*.py`, `tailpatch.py`, `pipeline.sh`), not in the repo; design §4 states the recipe (13 lexical rules, the 77 hand edits by kind) so that R1's ticket can carry it as an amend.
- **O2.** All line numbers are at afab243f; T2523 has not merged (`git diff --stat main...t/T2523`: `DeadDecls.lean` only).  The 1a-audit states its own base (BAD-C2 (b)); R1 starts after T2523 merges.
- **O3.** After T2523 the U5 instance sections are gone; the nonempty instances of R1's theorems are then the `Thm27` instances in `Main/FinalShape.lean` (`d = 3` existing, `d = 4` new).  The dispatcher confirms that this meets CLAUDE.md §4 step 2 for R1.
- **O4.** The BUniv conjunct of `Thm27` at `d = 4` is not applied: it reads the UN spectral data at `d = 3` (`S0`, `fp`, `clsκ`).
- **O5.** The numerics of `docs/reports/T2459-design.md` (`S_d`, the Yukawa threshold 167 at `d = 3`) are design-level; the Lean constants are general in `d`; the `d = 4` values are in section (a) rows 13, 14, 17.
- **Paper-delta candidates:** `T2524a`: D712 (d) ("targets 3, 4 only at `d = 3`") is superseded once R1 merges.  D723's withdrawal is D754 (dispatcher, DECISIONS §371): no new candidate.  No Lean/paper statement difference arises from this gate.
