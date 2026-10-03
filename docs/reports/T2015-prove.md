Prover model: claude-sonnet-5-5

ST-1 size (DECISIONS section 9 O2): 36 proof tickets S1-01..S1-36, above 25 and not above 40, so no question to Jun is needed before ST-1 starts; ~37239 lines estimated (32003 kept at 0c1330a: 86 files plus 4 re-assigned), critical path 12 tickets, first wave 6 tickets (b.9; portmap P.7).
Stage 1b result: all eight targets and the registry list delivered.  Probe `RBM3D/Probe/T2015Pins.lean` (branch `t/T2015`, 1958 lines, commit 6f8684e) compiles with the three standard axioms only; 111 of 1309 public declarations of the 86 files are referenced by ST-2..ST-6 (item 1).  Inventory, interface, closures, d = 2 token lines, split table, probe extracts, names and scripts: `docs/reports/T2015-portmap.md`.

## (a) Math preflight — 2026-10-03 01:30:25 UTC (`date -u`)

Notation: `x=1-t`, `a_u := W^{-d}B_{u,0}` with `B_{u,K}=(g²+x_u)^{-1}/(K+1)^{d-2}+(L^d x_u)^{-1}` (1_2:1107), `g=\ilambda`, `ℓ_u=min(max(g x_u^{-1/2},1),L)` (1_2:1121), `η_u=x_u Im m(E)` (1_2:720), `N=(WL)^d`. Scripts: `python3 $SP/t2015_{expo,inst,theta,giigex}.py`, `SP=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad` (Python only).

### (i) Exponent table (general `d ≥ 3`; numbers at `d=3, W=2^5, L=8, g=2^-6, 𝔡=1/4, 𝔠_W=1/5, κ=ε=1/10, E=1/2, z=E+i2^-14`, `N=2^24`)

| # | quantity | value / form | constraint | slack |
|---|---|---|---|---|
| 1 | `(eq:WO)` 1_2:363 | `W^{-d/2+𝔡}=2^-6.25 ≤ g=2^-6 ≤ 𝔡^{-1}=4` | `𝔡 ≤ (1.5·5-6)/5=0.3` at `g=2^-6` | 0.05 in 𝔡; also tested at the endpoint `g=W^{-d/2+𝔡}` (`extreme` lines below) |
| 2 | `(Main_DEL_COND)` 1_2:359 | `W ≥ N^{𝔠_W}`; here `W=N^{5/24}` | `𝔠_W ≤ 5/24=0.2083`; always `W ≤ N^{1/d}` | 0.0083 |
| 3 | scale conversion (D23) | `W^τ ≤ N^{τ/d}` (as `L ≥ 1`), `N^τ ≤ W^{τ/𝔠_W}`; here `W^τ=N^{(5/24)τ}` | `≺` at scale `N` ⟺ the paper's `W^τ` statements | `5/24 ≤ 1/3` |
| 4 | domain `𝐃_{κ,ε}` 1_2:381 | `|E| ≤ 1.9`, `η=2^-14 ∈ [N^{-1+ε}=2^-21.6, 1]` | `1-t_0=η/(Im m+η)=6.3035e-05 ≥ N^{-1+ε}/2` (RBM2D `RangeCond` adds this, T2005d) | factor `2^7.6` |
| 5 | polynomial smallness of `a_t` | `a_t ≤ W^{-d}g^{-2}+(Nx_t)^{-1} ≤ W^{-2𝔡}+2N^{-ε}`, so `a_t ≤ N^{-ν}`, `ν=min(2𝔡𝔠_W, ε)=0.1` | needs `x_t ≥ N^{-1+ε}/2`, `g ≥ W^{-d/2+𝔡}` | finite-size values in rows 6–7 (a up to 0.28) are not small: only the inequalities are tested |
| 6 | `B_{t,0}` / `ℓ_t` regimes (script table) | R1 `x≥g²`: `a≈W^{-d}/x`, `ℓ=1`. R2 `g²/L²≤x≤g²`: `a≈W^{-d}g^{-2}`, `ℓ=g x^{-1/2}`. R3 `g²/L^d≤x≤g²/L²`: `a≈W^{-d}g^{-2}`, `ℓ=L`. R4 `x≤g²/L^d`: `a≈(Nx)^{-1}`, `ℓ=L` | **finding F1**: `B` changes at `g²` and `g²/L^d` (not `g²/L²`); R2 and R3 differ only in `ℓ`; the ticket's three regimes omit R4 (`x ≤ g²/L^d`, allowed since `N^{-1+ε}<g²/L^d` is possible: here `2^-21.6<2^-21`) | R4 occurs at `x=3.9e-7` |
| 7 | values of `a` at the four regime points (table below) | R1 `x=0.3`: `a=1.0184e-04`; R2 `x=2^-14`: `0.1010`; R3 `x=2^-19`: `0.1553`; R4 `x=2^-21.3`: `0.2787` | `a<1` | — |
| 8 | `η_s/η_t` | `=x_s/x_t` exactly (no regime dependence) | RBM2D `etaT_div_etaT` (`Path/Scales.lean:92`) | 0 |
| 9 | `ℓ_t/ℓ_s ≤ (x_s/x_t)^{1/2}` | holds for `g>0` in all four regimes (checked in script: 3 steps × 3 `u` × 4 regimes × 2 `𝔠`) | RBM2D `ellT_mono_ratio` (`Scales.lean:135`) has `g=1` | the `max(·,1)` in `ℓ_t` is the only `g`-change |
| 10 | monotonicity | `a_s ≤ a_u ≤ a_t` for `s≤u≤t`; `x·B_{·,0}=x/(g²+x)+L^{-d}` is nondecreasing in `x`, so `a_t ≤ a_u x_u/x_t` | `B x=x/(g²+x)+L^{-d}` increasing in `x` | exact |
| 11 | `(con_st_ind)` 1_2:1296 | `a_t^{𝔠} ≤ x_t/x_s <1`; paper `0<𝔠_d ≤ 10^-2`; RBM2D uses `M_s^{-1} ≤ (x_t/x_s)^{30}`, i.e. `a_s^{1/30} ≤ x_t/x_s` (`Path/Step2Props.lean:116`) | **finding F2**: the paper's hypothesis (`a_t`) implies RBM2D's (`a_s ≤ a_t`); the closure of Step 1 below holds under either; pin the paper's | `𝔠_d`: see row 12 |
| 12 | `(Gtmwc)` closure | `‖G_u-M‖² ≺ a_s x_s/x_u ≤ a_s^{1-𝔠} ≤ a_u^{1/2}` ⇒ `‖G_u-M‖ ≺ a_u^{1/4}` | needs `1-𝔠 ≥ 1/2`, i.e. `𝔠 ≤ 1/2` (uses `a_s ≤ a_u`) | `1/2-𝔠 = 0.49` at `𝔠=10^-2`, `0.4667` at `1/30` |
| 13 | `(lRB1)` = `(res_lo_bo_eta)` first form | `(x_s/x_u)^{n-1}a_s^{n-1}` `=` `(a_s η_s/η_u)^{n-1}` (identical); `≤ a_t^{-(n-1)𝔠}a_s^{n-1}`; RBM2D form `(ℓ_u/ℓ_s)^{2(n-1)}M_u^{-(n-1)}` equals `M_s^{-1}η_s/η_u` in `d=2` (`M=W²ℓ²η`), has no closed form in `d≥3`: use `a_s x_s/x_u` directly | `n≥2`; `n=1`: `|𝓛^{(1)}| ≤ ‖G‖_max Tr E_a ≤ C_0` | — |
| 14 | `lem_ConArg` start `ε ≤ s` (3_5:42) vs main_ind `s ∈ [0,t_0]` | for `s<1/2` use `t₁=max(s,1/2)` and the deterministic bound at `u ≤ 1/2`: `|𝓛^{(n)}_u| ≤ η_u^{-n}‖E‖^{n-1}Tr E ≤ (2/Im m)^n W^{-d(n-1)}`, `Im m ≥ √(2κ)/2=0.2236`, `(2/Im m)=8.94`; `W^{-d(n-1)} ≤ (1+g²)^{n-1}a_u^{n-1}` | **finding F3**: the paper defers this case to `[YY_25 §5.1]`; RBM2D `Induction/Step1.lean:36,513,522` does exactly this with weight `W^{-2}` (here `W^{-d}`, `Tr E_a=1`) | `t₁=max(s,1/2) ≥ ε` for every `ε ≤ 1/2` |
| 15 | `lem_GbEXP` part 3 (3_5:28): `W^{-d/2} ≤ Ψ_t ≤ W^{-ε_0}` | `Ψ² := (1+𝔡^{-2}) a_s x_s/x_u` | lower: `a_s ≥ W^{-d}/(g²+1)` (script `c3`); upper: `Ψ² ≤ a_t^{1-𝔠}≤N^{-ν(1-𝔠)}`, so `ε_0 ≤ ν(1-𝔠)/2=0.0495` (`N^{-x}≤W^{-x}`) | factor 2 in `ε_0` |
| 16 | `Ω(t,ε_0)` ⇒ `‖G‖_max ≤ C_0=2` | `|m(E)|=1` (`|E|≤2`), `‖G-M‖ ≤ W^{-ε_0} ≤ 1` | ConArg event `Ω_t` | `ε_0>0` |
| 17 | hypotheses (a)-(d) at `s` | RHS: (a) `a_s^n`; (b) `a_s^{1/5}W^{-d}B_{s,|a|}e^{-(|a|/ℓ_s)^{1/2}}`, `|a|` is `L^∞` (T2002b); (b<g) `a_s²e^{-√|a|}` needed only if `1-s ≥ g²`; (c) `a_s^{1/2}`; (d) `a_s²((g²W^d)^{-1/5}+a_s)` | Step 1 uses (a),(c) and `Kbound` (`eq:bcal_k` 1_2:1056) for `eq:loopbound_s`; (b),(d) are not used by RBM2D's Step 1 (`Induction/Step1.lean:66`: `InitDecay` not used; `MainIndHyp` has no (d)); carried to Steps 2-6 | — |
| 18 | `𝒦` input (external, borrowed): `max|𝒦^{(n)}_t| ≺ a_t^{n-1}` | `n=2`: `𝒦^{(2)}=W^{-d}Θ_t`, `Θ_t(0,0)/B_{t,0} ∈ [0.2478, 0.9974]` (limit table below) | borrowed (DECISIONS §16: `Prop5to8`, `KLPT`); `KboundConcl` is the consumer's hypothesis | ratio `≤1` |

### (ii) One concrete nondegenerate instance (all deterministic hypotheses at once) and extremes

```
$ python3 $SP/t2015_expo.py | grep -v "L=512"      # exponent table values, closure checks, extremes
N=2^24  W=N^0.2083  W^-d/2+dd=2^-6.25 <= g=2^-6 <= 1/dd=4.0: True
Main_DEL_COND W>=N^cW (cW=0.20): True ; W^tau = N^(0.2083 tau)
N^(-1+eps)=2^-21.60 ; g^2=2^-12 ; g^2/L^2=2^-18 ; g^2/L^d=2^-21
z=0.5+i2^-14 in D_{kap,eps}: |E|<=1.9:True, N^(-1+eps)<=eta<=1:True
m(z)=-0.249992+0.968215i  t0=|m|^2=0.999936965  1-t0=6.3035e-05  eta/(Im m+eta)=6.3035e-05  E_flow=-2Re m/|m|=0.500000
regime   x=1-t      ell       a=W^-dB    a*N^.1    g^-2W^-d  1/(Nx)    N*x
1:       3.000e-01  1.000     1.0184e-04 5.375e-04 1.250e-01 1.987e-07 5.03e+06
2:       6.104e-05  2.000     1.0098e-01 5.330e-01 1.250e-01 9.766e-04 1.02e+03
3:       1.907e-06  8.000     1.5528e-01 8.196e-01 1.250e-01 3.125e-02 32
4:       3.873e-07  8.000     2.7870e-01 1.471e+00 1.250e-01 1.539e-01 6.5
c=0.0100: all closure checks (ell-ratio<=(x_s/x_u)^1/2, a_s<=a_u<=a_t, a_s x_s/x_u<=a_u^1/2, >=W^-d, <=a_t^(1-c)) over 4 regimes x 3 steps x 3 u: True
c=0.0333: all closure checks (ell-ratio<=(x_s/x_u)^1/2, a_s<=a_u<=a_t, a_s x_s/x_u<=a_u^1/2, >=W^-d, <=a_t^(1-c)) over 4 regimes x 3 steps x 3 u: True
extreme g=W^(-d/2+dd): a(x=N^-0.9)=3.659e-01 a(0.3)=1.019e-04
extreme g=1/dd: a(x=N^-0.9)=1.895e-01 a(0.3)=2.071e-06
L=8 (L large): a(x=0.3)=1.0184e-04, a(2^-14)=1.0098e-01, W^-d/(g2+x)=1.0000e-01 | L=64: a(2^-14)=1.0000e-01 (L→∞ removes only the (L^d x)^{-1} term)
$ python3 $SP/t2015_inst.py        # A: t=t0(z) (regime 2); B: regime 1 with 1-s >= g^2 (so (Eq:Gdecay+IND_s<g) is a hypothesis)
A: t=t0(z), regime 2: s=0.999935645 t=0.999936965 x_s/x_t=1.02094 (<= a_t^-c=1.02326) a_s=9.9850e-02 a_t=1.0029e-01 ell_s=1.948 ell_t=1.968
  deterministic hypotheses: {'WO': True, 'Bandwidth': True, 'kappa': True, 'eps_le_s': True, 's_le_t_lt_1': True, 't_le_t0': True, 'con_st_ind': True, 'range': True, 'one_minus_s_ge_g2': False}
  RHS (a) n=1,2,3: ['9.985e-02', '9.970e-03', '9.955e-04'] | (c) a_s^(1/2)=3.1599e-01 | (d) a_s^2((g^2W^d)^(-1/5)+a_s)=7.5733e-03
  conclusions at u=t: (lRB1) n=2,3 = ['1.019e-01', '1.039e-02'] ; (res_lo_bo_eta)<= ['1.024e-01', '1.048e-02'] ; (Gtmwc) a_t^(1/4)=5.6276e-01 ; (con) ||G-M||^2<=a_s x_s/x_t=1.0194e-01 <= a_t^(1/2)=3.1669e-01: True
B: regime 1 (1-t>=g^2): s=0.674004896 t=0.700000000 x_s/x_t=1.08665 (<= a_t^-c=1.09628) a_s=9.3726e-05 a_t=1.0184e-04 ell_s=1.000 ell_t=1.000
  deterministic hypotheses: {'WO': True, 'Bandwidth': True, 'kappa': True, 'eps_le_s': True, 's_le_t_lt_1': True, 't_le_t0': True, 'con_st_ind': True, 'range': True, 'one_minus_s_ge_g2': True}
  RHS (b) |a1-a2|=0,2,4: ['1.466e-05', '1.193e-06', '4.000e-07'] | (b_s<g) a_s^2 e^{-sqrt|a|}: ['8.785e-09', '2.136e-09', '1.189e-09']
  conclusions at u=t: (lRB1) n=2,3 = ['1.018e-04', '1.037e-08'] ; (res_lo_bo_eta)<= ['1.107e-04', '1.225e-08'] ; (Gtmwc) a_t^(1/4)=1.0046e-01 ; (con) ||G-M||^2<=a_s x_s/x_t=1.0185e-04 <= a_t^(1/2)=1.0092e-02: True
```
Instance A has `s=0.99993565 ≥ ε=0.1`, `s<t=t_0<1`, `W=32`, `L=8`, `N=2^24` (no `N=0`, empty index, collapsed window); `𝔠=10^-2`; `x_s/x_t=1.02094` is a single induction step (con_st_ind forces `x_s/x_t ≤ a_t^{-𝔠}=1.02326`). Extremes: `t→1` is `x=N^-0.9` (`a=0.3659` at `g=W^{-d/2+𝔡}`, `0.1895` at `g=𝔡^{-1}`), `g→W^{-d/2+𝔡}` and `L` large are run above; closure checks hold at all four regimes.

External hypothesis (`𝒦` bound, borrowed): limit computation, `Θ_t=(1-tS^{(B)})^{-1}` (`|m(E)|=1`, 1_2:472), `g=2^-6`, `L→∞`:
```
$ python3 $SP/t2015_theta.py
Theta_t(0,0)/B_{t,0}, B=(g^2+x)^-1+(L^d x)^-1, d=3, g=2^-6 (Theta=(1-tS)^-1; KboundConcl n=2: max|K^(2)|=W^-d max Theta <= C W^-d B)
x         L=8       L=16      L=32      L=64      
3.000e-01 0.9955    0.9972    0.9974    0.9974    
6.104e-05 0.2636    0.2640    0.2643    0.2643    
1.907e-06 0.3817    0.2627    0.2484    0.2478    
3.873e-07 0.6530    0.3407    0.2601    0.2507    
```
`(GiiGEX)`-type numeric check, `d=3, W=2, L=3, N=216`, `g=1/2` (`W^{-1.25}=0.42 ≤ g`), complex Hermitian Gaussian `H` with variance `W^{-d}S^{(B)}` (1_2:293-305), `M=m(E)I`, flow `G_t=(√t H-z_t)^{-1}`, `𝓛^{(2)}_{(-,+),(a,b)}=Tr(G^*E_aGE_b)`:
```
$ python3 $SP/t2015_giigex.py | tail -7
flow G_t=(sqrt(t)H-z_t)^-1, z_t=E+(1-t)m(E), M=m(E)I, E=0.5, Im m(E)=0.9682; 20 samples
eta_t=0.5 t=0.4836: ||G-M||^2_max mean 2.7347e-01 | max_ab L2_(-,+) mean 1.7714e-01 | ratio mean 1.545 max 2.177 min 0.990 | log2(max ratio)=1.122 (=tau with W^tau=ratio, W=2)
eta_t=0.1 t=0.8967: ||G-M||^2_max mean 1.0417e+00 | max_ab L2_(-,+) mean 3.4137e-01 | ratio mean 3.063 max 3.986 min 2.386 | log2(max ratio)=1.995 (=tau with W^tau=ratio, W=2)
direct G(z)=(H-z)^-1, z=E+i eta, M=m(z)I
eta=0.5: ||G-M||^2_max mean 2.0247e-01 | max L2 mean 1.1643e-01 | ratio mean 1.740 max 2.475 min 1.363
eta=0.1: ||G-M||^2_max mean 1.0235e+00 | max L2 mean 3.0261e-01 | ratio mean 3.390 max 5.815 min 2.589
```
At `W=2` the event `Ω(t,ε_0)` (`‖G-M‖ ≤ W^{-ε_0}`) is not guaranteed (`‖G-M‖²_max` is 0.27-1.04), so only the un-indicated comparison is tested: the ratio is `≤ 5.815` over all 80 samples; no sample has ratio below 0.99 (the ratio can be `<1` because `𝓛` contains `G` and `‖G-M‖` contains `M`).

### Verdicts
* Pin `lem:main_ind` at sequence level (hypotheses (a)-(d), `con_st_ind`, conclusions at every `t`): **PASS** (rows 1-5, 10-12, 17; instances A, B).
* `lem_GbEXP` (three parts): **PASS** (rows 15-16; `Ψ²` choice in row 15; numeric check above).
* `lem_ConArg` and Step 1 `(lRB1)`, `(Gtmwc)`: **PASS** with the `t₁=max(s,1/2)` start (row 14) and `𝔠_d ≤ 1/2` (row 12; paper's `≤10^-2`).
* Exponent table with regimes: **PASS** after correcting the regime list (F1: four regimes).
* Block Anderson reuse (item 6) and split table (item 7): no mathematics beyond rows 1-18; `lem_GbEXP_BA`/`lem_ConArg_BA` (7_8:1916, 1956) were not read here, hence no claim.
* Findings for stage 1b: F1 (regime R4), F2 (`CondStInd` in RBM2D uses `a_s`; paper `a_t`; propose paper-delta `T2015a` if the pin takes `a_s`), F3 (`s<ε` route), F4 (`(b)` uses the `L^∞` distance, T2002b; `𝒦`-bound is a borrowed hypothesis).

Overall verdict: **PASS**.

## (a′) Preflight corrections — Sat Oct  3 04:48:09 UTC 2026 (`date -u`)

* Row 18 calls the `𝒦` input "external, borrowed".  `RBM.Loop.KLoopBound` (`RBM3D/Loop/KBound.lean:74`) is `ML:Kbound` (1_2:1054) as a `Prop` and is registered **owed**: the paper proves it (`A_deterministic_estimates.tex:661` "we provide the proof below", proof 672-806).  So the proposed class of `STKbound` is owed; only the inputs of its proof, `Prop5to8` and `KLPT`, are borrowed.  The limit table of row 18 is not affected.
* F2 is void: the pin `STConStInd` takes the paper's `a_t` form, so no paper-delta `T2015a` is needed (d).  The RBM2D lines cited in (a) rows 8, 9, 11, 14, 17 are correct (`cite_check.py` on the text of (a), b.1; `Scales.lean:135` of row 9 is `Path/Scales.lean:135`, b.6).

## (b) Script output

### b.1 Build, axioms, hygiene (worktree `RBM3D-wt/T2015`, commit 6f8684e, Sat Oct  3 04:48:09 UTC 2026)
```
$ lake build RBM3D.Probe.T2015Pins > build.out 2>&1; echo "exit=$? std=$(grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]' build.out) warnings=$(grep -c '^warning' build.out) errors=$(grep -c '^error' build.out)"; tail -1 build.out
exit=0 std=51 warnings=0 errors=0
Build completed successfully (3308 jobs).
$ lake env lean RBM3D/Probe/T2015Pins.lean > probe.out 2>&1; echo "exit=$? lines=$(wc -l < probe.out | tr -d ' ') std=$(grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]' probe.out) other=$(grep -vc 'depends on axioms: \[propext, Classical.choice, Quot.sound\]' probe.out)"
exit=0 lines=51 std=51 other=0
$ echo "lines=$(wc -l < RBM3D/Probe/T2015Pins.lean | tr -d ' ') forbidden=$(grep -cE 'sorry|admit|native_decide|^axiom' RBM3D/Probe/T2015Pins.lean)"
lines=1958 forbidden=0
$ grep -E "RBM.Gauss.Sizes.(STMainInd|STGbEXP|STConArg|STStep1)'" probe.out
'RBM.Gauss.Sizes.STMainInd' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.STGbEXP' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.STConArg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.STStep1' depends on axioms: [propext, Classical.choice, Quot.sound]
$ git diff --name-only $(git merge-base HEAD main) HEAD
RBM3D/Probe/T2015Pins.lean
$ python3 cite_check.py RBM3D/Probe/T2015Pins.lean --quiet; python3 cite_check.py <(a) of this report> --quiet; python3 cite_check.py <(a′), b.6, b.7, (d) of this report> --quiet     # RBM2D file:line read at c9a24cf
citations checked: 18; failures: 0
citations checked: 6; failures: 0
citations checked: 29; failures: 0
```

### b.2 Binding to the merged declarations (T2012 = MD-2, T2013 = MD-3 are on `main`).  Section 0 of the probe is the copy of the T2002 probe that the ticket asks for (`normalized` below: equal after the dot-notation and section-variable rewriting of `vocabdiff.py`, portmap P.10); `mkbind.py`: section 0 deleted, imports `RBM3D.Defs.StochDomAt`, `RBM3D.Loop.GLoopFlow`, `RBM3D.Gauss.DominationAt` added, `open` lines changed (`bind1`); `bind3`: also the probe's own `StochDomAt.of_subset`, `of_subset_union` deleted; `bind2`: `bind1` plus `bind2_extra.lean` (portmap P.8.4)
```
$ git show 5d2a4a8:RBM3D/Probe/T2002Vocab.lean > T2002Vocab.lean; python3 vocabdiff.py T2015Pins.lean T2002Vocab.lean
identical (7): Gres loopM blockMat loopFine badSetAt StochDomAt TimeIcc
normalized (7): Gt Lloop HighProbAt PerTimeDomAt Prec PrecPT Whp
DIFFERENT (0): 
$ (cd <main worktree>; for v in bind1 bind2 bind3; do lake env lean $v.lean > $v.out 2>&1; echo "$v exit=$? removed=$(diff T2015Pins.lean $v.lean | grep -c '^<') added=$(diff T2015Pins.lean $v.lean | grep -c '^>') std=$(grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]' $v.out) other=$(grep -vc 'depends on axioms: \[propext, Classical.choice, Quot.sound\]' $v.out)"; done)   # copies in one scratch directory
bind1 exit=0 removed=117 added=15 std=51 other=0
bind2 exit=0 removed=117 added=28 std=52 other=0
bind3 exit=0 removed=150 added=15 std=49 other=0
'RBM.Gauss.Sizes.STEnvelope_of_merged' depends on axioms: [propext, Classical.choice, Quot.sound]
```
So the pins (sections 1-5, apart from the `open` lines) bind to the merged `Prec`, `PrecPT`, `Whp`, `Gt`, `Lloop`, `TimeIcc` unchanged, and `STEnvelope` is a corollary of merged T2013 (`bind2`: `norm_loopM_le_sharp` at `blockMat (seqHflow ..)`).

### b.3 Targets: the pins (script `extract.py`, docstrings omitted).  Probe lines: STflowE 396, STFlow 399, STMainInd 407, STGbEXPii 421, STGbEXPij 428, STGbEXPav 435, STGbEXP 442, STConArg 447, STStep1 462.  `STLK` ... `STKbound`, `STGiiGEX` ... and `STflowE`, `STFlow`, `STBootstrap`, `STNetLift`: portmap P.8.
```lean
def STMainInd (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ lemT (z n)) → (∀ n, s n < t n) →
          (∀ n, t n ≤ lemT (z n)) →
          (STLK sz (STflowE z) s ∧ STDecay sz (STflowE z) s ∧ STDecayStrong sz (STflowE z) s ∧
            STLocalMax sz (STflowE z) s ∧ STExp2 sz (STflowE z) s) →
          STConStInd sz 𝔠d s t →
          STLK sz (STflowE z) t ∧ STLmax sz (STflowE z) t ∧ STDecay sz (STflowE z) t ∧
            STExp2 sz (STflowE z) t ∧ STLocalEntry sz (STflowE z) t ∧
            STDecayStrong sz (STflowE z) t
def STGbEXPii (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ ε₀ : ℝ, 0 < ε₀ → STGiiGEX sz (STflowE z) t ε₀
def STGbEXP (d : ℕ) : Prop := STGbEXPii d ∧ STGbEXPij d ∧ STGbEXPav d
def STConArg (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 ε₁ C₀ : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → 0 < ε₁ → 0 < C₀ →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, ε₁ ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
        STLmax sz (STflowE z) s →
        ∀ k : ℕ, 2 ≤ k →
          Prec sz (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
            (fun n p ω => STomegaC sz n (STflowE z n) (t n) C₀ ω *
              ‖Lloop sz n (STflowE z n) (t n) p.1 p.2 ω‖)
            (fun n _ _ => (sz.Bctl n (s n) *
              (etaT (STflowE z n) (s n) / etaT (STflowE z n) (t n))) ^ (k - 1))
def STStep1 (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 1 / 100 →
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ lemT (z n)) → (∀ n, s n < t n) →
          (∀ n, t n ≤ lemT (z n)) →
          STKbound sz (STflowE z) → STLK sz (STflowE z) s → STLocalMax sz (STflowE z) s →
          STConStInd sz 𝔠d s t →
            STStep1Loop sz (STflowE z) s t ∧ STStep1Weak sz (STflowE z) s t
```
$ python3 samebody.py T2015Pins.lean STGbEXPii 'STGbEXPij=STGijGEX->STGiiGEX' 'STGbEXPav=STGavLGEX->STGiiGEX'
STGbEXPij: identical to STGbEXPii with STGijGEX -> STGiiGEX
STGbEXPav: identical to STGbEXPii with STGavLGEX -> STGiiGEX

### b.4 Compiled nonempty instances (item 8) and the skeleton instance (item 5), statements by script (`--head`; proofs in the probe).  Probe lines: inst_mainInd 634, inst_gbEXP 650, inst_conArg 665, inst_step1 679, inst_skeleton 1889, ST_step1_skeleton 1775.  `ST_step1_skeleton` itself: portmap P.8.3.
```lean
theorem inst_mainInd (h : STMainInd 3) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ((STLK sz0 (STflowE z0) sInst ∧ STDecay sz0 (STflowE z0) sInst ∧
          STDecayStrong sz0 (STflowE z0) sInst ∧ STLocalMax sz0 (STflowE z0) sInst ∧
          STExp2 sz0 (STflowE z0) sInst) →
        (STLK sz0 (STflowE z0) tInst ∧ STLmax sz0 (STflowE z0) tInst ∧
          STDecay sz0 (STflowE z0) tInst ∧ STExp2 sz0 (STflowE z0) tInst ∧
          STLocalEntry sz0 (STflowE z0) tInst ∧ STDecayStrong sz0 (STflowE z0) tInst))
theorem inst_gbEXP (h : STGbEXP 3) :
    STGiiGEX sz0 (STflowE z0) tInst (1 / 20) ∧ STGijGEX sz0 (STflowE z0) tInst (1 / 20) ∧
      STGavLGEX sz0 (STflowE z0) tInst (1 / 20)
theorem inst_conArg (h : STConArg 3) (hL : STLmax sz0 (STflowE z0) (fun _ => 1 / 16)) :
    ∀ k : ℕ, 2 ≤ k →
      Prec sz0 (U := fun n => (Fin k → Bool) × (Fin k → Zd 3 (sz0.L n)))
        (fun n p ω => STomegaC sz0 n (STflowE z0 n) ((fun _ => (1 : ℝ) / 2) n) 2 ω *
          ‖Lloop sz0 n (STflowE z0 n) ((fun _ => (1 : ℝ) / 2) n) p.1 p.2 ω‖)
        (fun n _ _ => (sz0.Bctl n ((fun _ => (1 : ℝ) / 16) n) *
          (etaT (STflowE z0 n) ((fun _ => (1 : ℝ) / 16) n) /
            etaT (STflowE z0 n) ((fun _ => (1 : ℝ) / 2) n))) ^ (k - 1))
theorem inst_step1 (h : STStep1 3) {𝔠d : ℝ} (h0 : 0 < 𝔠d) (h1 : 𝔠d ≤ 1 / 100)
    (hK : STKbound sz0 (STflowE z0)) (ha : STLK sz0 (STflowE z0) sInst)
    (hc : STLocalMax sz0 (STflowE z0) sInst) :
    STStep1Loop sz0 (STflowE z0) sInst tInst ∧ STStep1Weak sz0 (STflowE z0) sInst tInst
theorem inst_skeleton (hGii : STGbEXPii 3) (hCA : STConArg 3) (hBoot : STBootstrap 3) (hNet : STNetLift 3)
    (hEnv : STEnvelope sz0) {𝔠d : ℝ} (h0 : 0 < 𝔠d) (h1 : 𝔠d ≤ 1 / 100)
    (hKb : STKbound sz0 (STflowE z0)) (ha : STLK sz0 (STflowE z0) sInst)
    (hc : STLocalMax sz0 (STflowE z0) sInst) :
    STStep1Loop sz0 (STflowE z0) sInst tInst ∧ STStep1Weak sz0 (STflowE z0) sInst tInst
```
Data: `sz0` of MD-1 (`d = 3`, `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^-6`; `n = 0`: `L = 4`, `W = 32`, `N = 2097152`), `z_n = 1/2 + i N_n^(-4/5)`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `s ≡ 0`, `t ≡ 1/16` (`lem_ConArg`: `ε₁ = 1/16`, `s ≡ 1/16`, `t ≡ 1/2`).
Discharged: `3 ≤ d`, `STFlow`, the time ranges, `(con_st_ind)` for every `𝔠_d > 0`, `0 ≤ s`, `hsmall` at `ε₀ = 1/4`.  Hypotheses left: (a)-(d) at `s`, `(eq:loopbound_s)`, `ML:Kbound`, the gate pins.  Extremes: the same pins at `lam_n = W_n^(-3/2+1/10)` (lower end of `(eq:WO)`): 4 theorems `inst_*_lowg`; `lem_GbEXP`, `lem_ConArg` at the end of the flow `t = t₀ = lemT z_n` (`t -> 1`): `inst_gbEXP_endT` (probe line 725), `inst_conArg_endT` (737).

### b.5 Name clashes (script `clash.py`: full qualified names of the probe against all `.lean` files of `RBM3D/` on `main` and on the branch, Probe excluded)
$ python3 clash.py | sed -n 3,4p
full-name clashes (probe vs library): 0
same short name, different namespace (probe copies of merged declarations, section 0, and instance names): 17
The 17 short-name coincidences are the section-0 copies of merged declarations (deleted by the binding of b.2), `of_subset_union` and two instance names (`z0`, `z0_im_pos`).

### b.6 Exponent table with the d = 2 tokens (item 3); every RBM2D `file:line` below is read at `c9a24cf` by `cite_check.py` (b.1); the RBM3D lines (`RBM3D/...`) are read in `main` at `9187a77`.  Regimes, `x = 1-t`: R1 `x >= g²`; R2 `g²/L² <= x <= g²`; R3 `g²/L^d <= x <= g²/L²`; R4 `x <= g²/L^d`.  Values at `d = 3, W = 2^5, L = 8, g = 2^-6`: (a) rows 6-7 (`W^-d B_{t,0}` = 1.0e-4, 0.101, 0.155, 0.279 in R1..R4).

| quantity | RBM2D d = 2 token | d >= 3 (paper line; Lean) | change |
|---|---|---|---|
| `W^-d B_{t,0}` | `scaleM` (Path/Scales.lean:44) `= W² ℓ² η`; `scaleM_eq'` (Path/Scales.lean:124) `= Im m · min(W², N(1-u))` | `W^-d [(g²+x)⁻¹ + (L^d x)⁻¹]` (1_2:1107; merged `Sizes.Bctl`) | min of two scales -> sum of two terms with `g`; `a_s <= a_t`: `scaleM_anti_ratio` (Path/Scales.lean:163) -> `STBctl_mono`; `x·a(x)` nondecreasing: `STBctl_xmono` |
| regimes | d = 2 has no coupling (formulas at `g = 1`): `x >= L^-2` (`M = Im m W²`, `ℓ = x^-1/2`) and `x <= L^-2` (`M = Im m N x`, `ℓ = L`) | four regimes (F1 of (a); T2002 (b.6) lists R1..R3) | R1 needs `g < 1`; R3 is empty at d = 2 (`L^d = L²`) |
| `η_s/η_t` | `etaT_div_etaT` (Path/Scales.lean:92) `= (1-s)/(1-u)` | same (`STetaT_div`) | none |
| `ℓ_t` | `ellT` (Path/Scales.lean:41) `= min(1/√(1-u), L)`; `ellT_mono_ratio` (Path/Scales.lean:135) | `min(max(g/√x, 1), L)` (1_2:1121; merged `ellT`) | `g`, `max(.,1)`; `ℓ_u/ℓ_s <= (x_s/x_u)^1/2` holds in R1..R4 (a row 9) |
| loop scale (lRB1) | `Step1LoopPT` (Path/Step2Props.lean:141) `(ℓ_u/ℓ_s)^(2(k-1)) M_u^-(k-1)` | `((1-s)/(1-u))^(k-1) (W^-d B_{s,0})^(k-1)` (1_2:1321); (res_lo_bo_eta) `(a_s η_s/η_t)^(k-1)` (3_5:52) | at d = 2 `(ℓ_u/ℓ_s)² M_u⁻¹ = M_s⁻¹ η_s/η_u` (Induction/ConArg.lean:60): same shape; at d >= 3 `a_s x_s/x_u` is used |
| `(con_st_ind)` | `CondStInd` (Path/Step2Props.lean:116) `M_s⁻¹ <= ((1-t)/(1-s))^30`; `scaleFacts_R2_pt` (Induction/ScaleFacts.lean:87) `M_s^(29/30) <= M_u` | `a_t^𝔠_d <= x_t/x_s < 1`, `𝔠_d <= 10^-2` (1_2:1296) | `1/30 -> 𝔠_d`; `a_s x_s/x_u <= a_s^(1-𝔠_d)` and `(.)^1/2 <= a_s^(3/8)` need `𝔠_d <= 1/4` (`closure_scale`, `closure_sq_le`) |
| forbidden region | `[M_s^-1/4 / 2, 2 M_s^-1/4]`, bound `6 M_s^-7/15` (Induction/Step1.lean:57-58); `(ℓ_u/ℓ_s)² M_u⁻¹ <= M_s^-14/15` (Induction/Step1.lean:272) | `[α/2, 2α]`, `α = a_s^1/4`, bound `a_s^(3/8)` (`STForbidden`) | `7/15 -> 3/8` |
| ball counts | `gexRHS <= 25·maxLoop + (W²)⁻¹` (Green/LocalLaw.lean:141; Induction/Step1.lean:825) | `(3^d)²` points of two `L^∞` unit balls (1_2:274), `+ W^-d` | `25 -> 9^d` |
| block weight | `norm_Eblk_le_inv_W_sq` (Gauss/LoopEnvelope.lean:45) `‖E_a‖ <= (W⁻¹)²`; `card_BlockIndex` (Gauss/LoopEnvelope.lean:92) `(L W)²` | `W^-d` (`norm_Eblk_le_inv_W_pow`, RBM3D/Loop/GLoopFlow.lean:788, private), `(L W)^d` (`card_Idx`, RBM3D/Defs/Sizes.lean:107) | `2 -> d` |
| bandwidth, range | `Bandwidth` (Path/Step2Props.lean:112) `W >= N^c`; `RangeCond` (Path/Step2Props.lean:121) `1-t >= N^(-1+τ)` | `Sizes.Bandwidth 𝔠` (1_2:359); `locDomain κ ε` (1_2:380), `t <= lemT z`, `1-t₀ >= η/2` (a row 4) | `c <= 1/d` (a row 2) |
| stability | `Kstab2` (Green/Stability.lean:40) `= O(1+log L)` | d >= 3 lattice sum (`eq:latticesum_d3`, merged Kernel/SumDecay) | class c: S1-15 |

### b.7 Route per pin (items 2, 4).  Column 4: the merged declarations that each pin's statement uses (script `pinuses.py`, closure through the probe's `ST...` definitions, portmap P.8.5); all pins also use `Sizes Admissible locDomain Idx Zd` (MD-1); `Eblk` is inside `Lloop` (merged `loopM`), `Bparam` inside `Bctl`; none in flight.

| pin | RBM2D source (c9a24cf) | d-changes | merged declarations used | tickets; est lines | risk |
|---|---|---|---|---|---|
| `STMainInd` | `MainIndPinV3` (Induction/MainInd.lean:65), `MainIndHyp` (Induction/Defs.lean:229), `MainIndConcl` (Induction/Defs.lean:302); proof `mainIndPinV3_of_R3` (Induction/MainInd.lean:110) | (b) strong form, (d), conclusions `(Gt_bound)`, `(Gdecay+s<g)`, `(Gtlp_exp)` new; `RangeCond -> locDomain`; `κ c τ -> κ ε 𝔡 𝔠` | `zdistInf Prec Gt Lloop KLK Bctl Bparam ellT mE lemE lemT` | statement: S1-07 (886; probe ~180 lines); proof: ST-6 (not estimated here) | stmt low, proof high |
| `STGbEXP` | `GbEXPHypV3` (Green/Pins.lean:152), `GbEXPV3Theorem` (Green/Pins.lean:166); proof `gbEXPV3` (Green/GbEXP.lean:45), 44 ST-1 files | per entry `PerTimeDomAt` -> `Prec` (merged `Path.stochDomAt_of_perTimeDomAt`, RBM3D/Defs/StochDomAt.lean:249); `(GavLGEX)` keeps `W^-d/2 <= Ψ` (RBM2D: `Ψ <= N^-a`); `25 -> 9^d`; `W⁻² -> W^-d`; Stability | `zdistInf Prec Gt Lloop mE lemE lemT` | S1-07, S1-10..S1-30; 23781 | high |
| `STConArg` | `ConArgPin` (Induction/ConArg.lean:61), `conArg` (Induction/ConArg.lean:613); `ConArgDet` (6.3)-(6.12) | `(ℓ₂/ℓ₁)^(2(k-1)) M_{t₂}^-(k-1) -> (a_s η_s/η_t)^(k-1)`; `W⁻² -> W^-d`; `t < 1` (RBM2D T2006d); `C₀` general (RBM2D 2) | `Prec Gt Lloop Bctl etaT lemE` | S1-31, S1-32: 2205 (+ S1-08, S1-09: 2303, shared) | medium |
| `STStep1`, `STBootstrap`, `STNetLift` | `Step1TargetV3` (Induction/Step1.lean:84), `step1` (Induction/Step1.lean:1378); `Step1NetLift` (Induction/Continuity.lean:1261), `step1NetLift` (Induction/Continuity.lean:1331); `GopboundPin` (Induction/Continuity.lean:65), `gopbound` (Induction/Continuity.lean:1269); `forbidden_region` (Induction/PerTimeCalc.lean:698), `stepOneBootstrap` (Induction/PerTimeCalc.lean:826) | scale facts (b.6); restart at `max(s,1/2)` (`s1T1`, Induction/Step1.lean:513); pins instead of the bundle `GbEXPHypV3`, `KboundConcl`, `MainIndHyp` | STStep1 `Prec TimeIcc Gt Lloop KLK Bctl mE lemE lemT`; STBootstrap `Prec Whp Gt Bctl mE lemE lemT`; STNetLift `Prec TimeIcc Lloop Bctl lemE lemT` | S1-33..S1-36: 3621 (+ S1-08, S1-09, shared) | medium |
| `STLK` ... `STKbound` | `InitLK` (Induction/Defs.lean:199), `InitDecay` (Path/Step2Props.lean:125), `InitLocal` (Path/Step2Props.lean:133), `Step1LoopUnif` (Induction/Defs.lean:212), `Step1WeakLawUnif` (Induction/Defs.lean:220), `KboundConcl` (Induction/Defs.lean:179) | profile `B_{s,K}`, exponent `1/5` in (b); strong (b); (d) new | STKbound `Prec KLK Bctl` | S1-07: 886 | low |

### b.8 Block Anderson reuse (item 6; paper `7_8_light_weight.tex`)

| BA statement | shape against the RBM pin | carries over | gate BA adds |
|---|---|---|---|
| `lem:main_ind_BA` (7_8:1825) | same (a)-(d) and conclusions; flow `zztE_BA` (7_8:1796): `t₀ = Im m(z,g)/(Im m + Im z)`, `E = (t₀ Re z - (1-t₀) Re m)/√t₀`, `g₀ = √t₀ g`; domain `|Re z| <= e_g - κ` | `STMainInd` with `STFlowBA`; `Prec`, `Lloop`, `Bctl`; merged `Gt_BA`, `seqHflowBA` (T2013) | `m(z,g)`, `M^(B)`, `e_g` (DECISIONS section 11); `STGM` with the non-scalar `M^(B)` |
| `lem_GbEXP_BA` (7_8:1916) | no event `Ω`; hypotheses `(initialGT2)` and deterministic `0 < Φ_t(a,b) <= W^-ε₀`, `𝓛^(2)_{(-,+),(a,b)} ≺ Φ_t²`; conclusions `‖G-M‖_max ≺ Ψ_t`, `max_a \|tr((G-M)E_a)\| ≺ Ψ_t²`, entries `≺ Σ Φ_t(a',b') e^(-c_g(\|a'-a\|+\|b'-b\|)) + Ψ_t e^(-c_g\|a-b\|) + W^-D` | `STGbEXPii`, `STGbEXPij` do not | pin `STGbEXP_BA`, **borrowed**: paper "verbatim" [RBSO1D, Lemma 6.1] with `(Mbound_AO)`, `(Mbound_AO2)` of `lem:propM` (7_8:1847) |
| `lem_ConArg_BA` (7_8:1956) | part 1 at `(z_s, g_s)`, `g_s = g √(s/t)`, no indicator, factor `max_a tr(Im G_t E_a)`; part 2: `Im(G_t)_{vv}`, `(G_t)_{vw}` `≲ η_s/η_t` for unit vectors | range `ε₁ <= s <= t < 1`, scale `(a_s η_s/η_t)^(n-1)` | pin `STConArg_BA`, **borrowed**: "exactly Lemma 7.1 of [RBSO1D]"; Step 1 for BA is "the same as [RBSO1D, 7.1]" (paper): route = skeleton 4.2-4.4 adapted to the two pins (not compiled) |

### b.9 Split (item 7): 36 tickets; the table (files, sources with kept lines, est, dependencies, role, key statements) is portmap P.7.  Kept lines / est lines / tickets, by `splitcalc.py`:

* S1-01..06 Gaussian calculus, loop algebra: 4873 / 5329 / 6; S1-07..09 pins; Step 1 scale facts, per-time calculus, splitting: 2413 / 3189 / 3; S1-10..30 Green: lem_GbEXP: 19976 / 22895 / 21; S1-31..36 Step 1 proper: 4741 / 5826 / 6
* total 32003 / 37239 / 36; roles prover 10, prover-hard 22, prover-max 4; est per ticket 603..1504 (S1-11 is 1504; S1-01 is lowered by 222 lines that merged `mE`, `zt`, GLoopFlow cover); critical path 12 tickets; first wave S1-01, S1-03, S1-07, S1-09, S1-10, S1-12.
* above 25 and not above 40 (DECISIONS section 9 O2).  T2002 put 86 files in ST-1; Step 1 and Green also import `Induction/{ScaleFacts, PerTimeCalc, Split}` (ST-3: 1745 kept) and `Induction/Defs` (ST-6): re-assigned to S1-07..S1-09.  After 7 import cuts for the `lem_GbEXP` chain and 9 for the Step 1 chain (13 distinct, portmap P.4) no ST-2 file is needed; PT and KL enter only through S1-15, `STKbound` and the merged MD files.

### b.10 Premises the pins take as hypotheses that no ST-1 ticket proves: proposed registry class (DECISIONS section 16; `RBM3D/Test/Axioms.lean` is a writable file of S1-07)

* `STKbound` (hypothesis of `STStep1`): proved by the KL gate (KL7): **owed** ((a′)).  `STConStInd`, `STFlow` (= `Admissible` and `locDomain`, already structural): **structural**.
* `STLK`, `STLmax`, `STDecay`, `STDecayStrong`, `STLocalMax`, `STExp2` at `s` (hypotheses of `STMainInd`): proved by the chain induction of ST-6: **owed** until it merges.  BA: `STGbEXP_BA`, `STConArg_BA`: **borrowed** (b.8).
* Not premises: `STLoopBase` (`STLoopBase_holds`) and `STEnvelope` (b.2) are proved; `STGbEXP` is proved by S1-30, `STConArg` by S1-32, `STNetLift` by S1-34, `STBootstrap` by S1-36 (assembled from the generic `forbidden_region`, `stepOneBootstrap` of S1-08 and the time continuity of S1-01).

Extreme inputs of the pins (TEAM section 8 lesson 25): `g -> W^(-d/2+𝔡)`: Lean instances `sz1`, `inst_*_lowg` (b.4), numbers (a)(ii) `extreme g=W^(-d/2+dd)`; `t -> 1`: Lean instances `inst_gbEXP_endT`, `inst_conArg_endT` at `t = t₀ = lemT z_n` (b.4);
for `STMainInd`, `STStep1` numbers only (a)(ii) instance A at `t = t₀(z)` and `a(x=N^-0.9)`: a step `(s,t)` with `(con_st_ind)` near `t₀` needs `1-t₀` and a lower bound of `W^-d B_{t,0}` there; `STDecayStrong` is vacuous at `1-t < g²` (as in the paper).  `L` large: (a)(ii) `L = 64`, `a(2^-14) = 0.1000` (the pins see `L` through `Bctl`, `ellT` only).

## (c) Verified Mathlib names

`names.py`: every candidate identifier of the probe is `#check`ed in a file that opens only `MeasureTheory ProbabilityTheory Filter Matrix`: 144 of 167 elaborate (one line each with its type: portmap P.9); the other 23 are RBM3D names and local hypotheses.  The 12 below are all among the 144:
```
$ python3 usedby.py RBM3D/Probe/T2015Pins.lean --wrap 400 Matrix.mul_diagonal Matrix.submatrix_apply Matrix.nonsing_inv_eq_ringInverse Matrix.inv_submatrix_equiv Matrix.conjTranspose_nonsing_inv Fintype.sum_prod_type inv_le_comm₀ inv_anti₀ div_le_div_iff₀ pow_le_pow_left₀ mul_inv_cancel₀ tendsto_rpow_atTop
Bctl_const_le_gen: inv_anti₀; STBctl_mono: inv_anti₀; STBctl_xmono: div_le_div_iff₀; STBctl_ge: inv_anti₀; closure_scale: inv_anti₀; ST_norm_trace_mul_Eblk: Matrix.mul_diagonal Fintype.sum_prod_type; ST_Gres_blockMat_true: Matrix.submatrix_apply Matrix.nonsing_inv_eq_ringInverse Matrix.inv_submatrix_equiv; ST_Gres_false: Matrix.nonsing_inv_eq_ringInverse Matrix.conjTranspose_nonsing_inv;
ST_Lmax_of_LK: tendsto_rpow_atTop; ST_loop_at_time: tendsto_rpow_atTop; ST_early_bound: inv_le_comm₀ inv_anti₀ pow_le_pow_left₀ mul_inv_cancel₀ tendsto_rpow_atTop; ST_apriori: pow_le_pow_left₀; hsmall_inst: inv_anti₀ pow_le_pow_left₀
$ lake env lean Deprec.lean 2>&1 | grep -oE '(error|warning)[^ ]* .*' | cut -c1-110 | paste -sd'|' -     # Deprec.lean: #check @Nat.pos_pow_of_pos, @if_true, @if_false; push_neg; used instead: pow_pos, ite_true, ite_false, not_lt.mp
error(lean.unknownIdentifier): Unknown constant `Nat.pos_pow_of_pos`|warning: `if_true` has been deprecated: Use `ite_true` instead|warning: `if_false` has been deprecated: Use `ite_false` instead|warning: `push_neg` has been deprecated. Prefer using `push Not` instead.
```

## (d) Open issues and paper-delta candidates

* Paper-delta candidates (tags `T2015b`..; `T2015a` of (a) F2 is void, the pin takes the paper's `a_t`): `T2015b` `lem_ConArg` for `t < 1` (paper `t <= 1`, 3_5:42: at `t = 1`, `η_t = 0` and the right side is `x/0`; RBM2D T2006d);
  `T2015c` `t <= t₀` added to the ranges of `lem:main_ind` (the flow framework ends at `t₀`); `T2015d` `lem_GbEXP` "small `ε₀`" read as every `ε₀ > 0` (equivalent); `T2015e` Step 1 for every start `s >= 0`: the paper defers to [YY_25, 5.1], the route
  restarts `lem_ConArg` at `max(s,1/2)` and uses the sharp envelope at `u < 1/2` (RBM2D Induction/Step1.lean:36,513,522), and the time continuity `Gopboundu` (RBM2D Induction/Continuity.lean:65) has no statement in the d >= 3 paper;
  `T2015f` `(Eq:Gdecay+IND_s<g)`, `(Eq:Gdecay+s<g)` only at the sizes with `g² <= 1-τ`;  `T2015g` (audit D2(i)) `STStep1` is stated for **every** `𝔠_d ∈ (0,10^-2]` with premises `(a)`, `(c)` and `ML:Kbound` (`STKbound`) only, a stronger statement than the paper's Step 1 (`1_2:1317-1328`), which sits inside `lem:main_ind` under its single `∃𝔠_d` and all of `(a)`-`(d)`;  `T2015h` (audit D2(ii)) `STConArg` keeps only the first bound of `(res_lo_bo_eta)` (`3_5:52-56`), `≺ ((W^-d B_{s,0}) η_s/η_t)^{n-1}`; the omitted second inequality `≤ ((W^-d B_{t,0}) η_s/η_t)^{n-1}` is deterministic and follows from `STBctl_mono` (probe:962, `Bctl n s ≤ Bctl n u` for `s ≤ u < 1`).
* Open: (i) `𝔠_d` precedes `𝔠` (the paper lists `d, κ, ε, 𝔡`); Step 1 holds for every `𝔠_d <= 1/4` (a rows 11-12), Steps 2-5 are not checked here.  (ii) `hsmall` of the skeleton (a rows 5, 15) is discharged at `sz0` only;
  its general proof is S1-08 (RBM2D Induction/ScaleFacts.lean:72, `scaleFacts_R1`).  (iii) `t -> 1`: Lean instances for `STGbEXP`, `STConArg` only (b.4); for `STMainInd`, `STStep1` a step `(s,t)` near `t₀` is numeric (a)(ii): `(1-t₀) Im mE(lemE z) = √t₀ Im z` (merged `zt_im_lemma28`) gives `1-t₀`, but a lower bound of `W^-d B_{t,0}` there is not in the probe.
  (iv) S1-15 takes the PT pins as hypotheses.  (v) Moving 4 files from ST-3/ST-6 to ST-1 and the 36-ticket plan are for the dispatcher to confirm.
## Repair (repairer model: claude-opus-5-5; audit round 1: D1 instance, D2 deltas in (d) `T2015g`, `T2015h`) — Sat Oct  3 04:58:28 UTC 2026 (`date -u`)
D1: `inst_gbEXP_av` (probe:666, commit 752e027) applies `(inst_gbEXP h).2.2` at `Ψ_n = W_n^{-1}`, `ε₀ = 1/20`; both window bounds `W^{-3/2} ≤ Ψ_n ≤ W^{-1/20}` are proved (`Real.rpow_le_rpow_of_exponent_le`, `sz0.W_pos`); its hypotheses are `STGbEXP 3` and the two `Prec` premises of `(initialGT2)` only.
```
$ lake build RBM3D.Probe.T2015Pins > build.out 2>&1; echo "exit=$? std=$(grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]' build.out) warnings=$(grep -c '^warning' build.out) errors=$(grep -c '^error' build.out) $(tail -1 build.out)"; grep "inst_gbEXP_av'" build.out; echo "clash=$(grep -rl 'inst_gbEXP_av' /Users/junyin/Lean_proof/RBM3D/RBM3D | wc -l | tr -d ' ')"
exit=0 std=52 warnings=0 errors=0 Build completed successfully (3308 jobs).
info: RBM3D/Probe/T2015Pins.lean:1964:0: 'RBM.Probe.T2015.Inst.inst_gbEXP_av' depends on axioms: [propext, Classical.choice, Quot.sound]
clash=0
```
