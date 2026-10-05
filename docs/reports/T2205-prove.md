Prover model: claude-sonnet-5-5
BA count (target 7): 4 used / 66 planned with BA-D3 (ticket baseline 63; cap 70, DECISIONS §52): within the cap.  New rows BA-D8, BA-S2a, BA-V2b (V2 split into V2a/V2b; V2b is a port), no row superseded; 65 if S2a is folded into S2.  Table and reasons: `docs/reports/T2205-portmap.md` P.1-P.4.
## (a) Math preflight — Mon Oct  5 19:14:40 UTC 2026
Notation: `b = Im m`, `w_i = gλ_i − E − m` (λ_i ∈ [−2d, 2d] eigenvalues of `PsiB`, `Adj` = ℓ¹-distance 1, `Defs/Lattice.lean:108`), `⟨·⟩ = L^{-d}Σ_i`, `M² ↔ w_i^{-2}`. Real-axis `(self_m)`: `m = ⟨w^{-1}⟩`; `BAward_avg` at `Im z = 0` gives `⟨|w|^{-2}⟩ = 1`.

### (i) Exponent table (`d=3`; family `Fam(u)`: (A) `τ ∈ [min(t₀,max(u,1−c₁)), t₀]`, (B) `g'/g₀ ∈ [√max(u,1−c₁), 1]`)
| # | quantity | value / derivation | constraint | slack |
|---|---|---|---|---|
| 1 | gap (`BAgapReal`) | `Re(1−⟨w^{-2}⟩) = 2b²⟨|w|^{-4}⟩ ≥ 2b²` (`Re w^{-2}=(a²−b²)/|w|⁴`, Ward, Cauchy–Schwarz) | `≥ 2b²` | min gap/(2b²)=2.32 (15 pts); identity to 8e-16 |
| 2 | `∂_g m` | `−⟨λw^{-2}⟩/(1−⟨w^{-2}⟩)`, `|⟨λw^{-2}⟩| ≤ 2d` ⇒ `|∂_g m| ≤ d/b²`; `C = 4d/κ²` on `b ≥ κ/2` | `Lip ≤ C` | observed max `|∂_g m|b²/d`=0.038; Lip/C ≤ 0.0095 |
| 3 | `c₁(κ,Λ)` | `min(1/2, κ³/(8dΛ))` | `C·(1−√(1−c₁))Λ ≤ κ/2` | `1−√(1−c₁) ≤ 0.586c₁` (c₁≤½): factor ≥1.7; observed min `Im m` ≥ 0.9985κ on window |
| 4 | κ-dependence of `c₁` | fixed `c₁=1/2` fails | — | `Im m` leaves `[κ/2,∞)` in 6/10 cases ⇒ `c₁` must depend on κ; `c₁=½` binds only if `κ³ ≥ 4dΛ` |
| 5 | `s₀ = 1−c₁` | ConArg start; `ε₁ := 1/2` | `ε₁ ≤ s₀`, `s₀<1` | `s₀ ≥ 1/2` (sz0: 2/3) |
| 6 | κ-loss | `BAdom κ ⇒ BAWinBulk (κ/2)`; pins applied at `κ/2` (`BAdom` monotone in κ). (A) members: `Im m(z',g)=√τ Im m₀' ≥ κ/(2√2)`; `BAConArg'` premise `Im m(E,g_s) ≥ κ/2` | `κ/2 ≥ κ/(2√2)` | factor √2 |
| 7 | `t₀`, member couplings | `t₀ ≥ κ/(κ+1)` (`Im z ≤ 1`); `√(1−c₁)g₀ ≥ √(κ/(2(κ+1))) g` | §29(2) | P: 4.67 ≥ 3.22 |
| 8 | trivial loop, `u ≤ 1−c₁` | `η_u=(1−u)Im m ≥ c₁κ/2`, `‖G_u‖ ≤ 2/(c₁κ)`; `|𝓛^{(k)}| ≤ ‖G‖^k W^{-(k−1)d}` (`E_a = W^{-d}1_{[a]}`, `Loop/GLoop.lean:55`); `Bparam ≥ (g²+1)^{-1}` ⇒ `W^{-d} ≤ (g²+1)Bctl(s)` | constants only, no power of N | sz0 n=0: `‖G_{s₀}‖ ≤ 3.00 ≤ 12` |
| 9 | ConArg ratio | `η_{s₀}/η_u ≤ (2/κ)(1−s₀)/(1−u)` (`Im m ≤ 1`, `‖m‖ ≤ 1`) | constant `(2/κ)^{k−1}` | — |
| 10 | `s<1−c₁` comparison | `x·Bparam(1−x,0) = x/(g²+x)+L^{-d}` (`Params.lean:36`), derivative `g²/(g²+x)²>0` ⇒ `(1−s₀)Bctl(s₀) ≤ (1−s)Bctl(s)` | `≤` | sz0: equal to 4 digits (3.097e-05), strict |
| 11 | `(con_st_ind)` | `(1−t)/(1−s₀) ≥ (1−t)/(1−s) ≥ Bctl_t^{𝔠_d}`, `𝔠_d ≤ 1/100` (before the sequence) | `Bctl^{𝔠_d} ≤ ratio < 1` | sz0 (s,t)=(.66,.68): 0.9412 vs 0.9117/0.8216/0.7731 |
| 12 | (A) member ranges | `Im z' = (1−τ)Im m₀'/√τ ≤ (1−τ)/√τ ≤ 0.7071` (τ ≥ ½); `Im z' ≥ (κ/(2√2)) Im z` | `≤ 1`; `≥ N^{-1+ε/2}` | 0.29; general `N ≥ (2√2/κ)^{2/ε}=1.13e15` (κ=½, ε=1/10); sz0 actual ≥ 1.8e5·N^{-0.9} |
| 13 | stage patterns | 4 stages, nonempty ones contiguous: `C(4,2)+4` | =10 | — |
| 14 | `Admissible(1/6,1/10)` at sz0 | `W^6=(2(n+1))^{30} ≥ N=(2(n+1))^{15}(4(n+1))^3`; `W^{-1.4}=(2(n+1))^{-7} ≤ lam_n=(2(n+1))^{-6}` | `N^{1/6} ≤ W`, `WO` | see (ii) |

### (ii) Concrete instance and scripts (scratch dir `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2205`; python3 numpy 2.0.2; `ba.py`: torus spectrum `2Σcos`, Newton at `η↓0`)
Instance: `d=3`, `sz0` (`L_n=4(n+1)`, `W_n=(2(n+1))^5`, `lam_n=(2(n+1))^{-6}`), `z_n=z_S` (`w=6i/5`), `(κ,ε,𝔠,𝔡)=(½,1/10,1/6,1/10)`, `Λ=1/64`, `c₁=1/3`, `C=48`, `(s,t)=(.66,.68)` straddling `1−c₁=2/3`, `𝔠_d=1/100`; second point: `P=(L,g)=(4,10)`.
`cd $S && python3 chk_inst.py | head -7` (the point `P`; here `t₀=0.218 < 1−c₁`: (A)-family = main flow only):
```
I. (L,g)=(4,10): z_S=0.00000+0.93803j, m_S=-0.00000+0.26197j, t0=0.21831, E=0.00000, g0=4.67234, m0=-0.00000+0.56068j, kappa=Im m0=0.56068
   BAReal 3 4 g0 kappa E m0 residual 1.1e-16;  Lambda=10: c1=7.3440e-04, C=4d/kappa^2=38.17
   window [sqrt(1-c1) g0, g0]=[4.67062,4.67234]: min Im m = 0.56068 >= kappa/2=0.28034: True; max |m-m0|/(g0-g')=0.0007 <= C: True
   at (g0,E): <|w|^-2>-1=-1.1e-16, Re gap=1.98819 >= 2(Im m0)^2=0.62873: True; |dm/dg|=0.0007 <= d/kappa^2=9.543
   BAzztE_inv tau=0.5: z'=0.00000+0.39580j, residual of (self_m) at (g,z') for m'=sqrt(tau)m0': 2.2e-16, t0 err 0.0e+00, E err 2.0e-31
   BAzztE_inv tau=0.9: z'=0.00000+0.05897j, residual of (self_m) at (g,z') for m'=sqrt(tau)m0': 1.1e-16, t0 err 0.0e+00, E err 2.0e-31
   section 29(2): t0=0.21831 >= kappa_dom/(kappa_dom+1) with kappa_dom=Im m(z_S,g)=0.26197: True; couplings sqrt(1-c1) g0=4.6706 >= sqrt(kappa/(2(kappa+1))) g=3.2217: True
```
`cd $S && python3 inst.py` (sz0, all hypotheses of `BAmWindow`, `BAWinBulk_of_dom`, `BAFamCone_closed_stmt`, `BAStep1`/`BAMainInd` shapes, `BAConArg'` premise):
```
INSTANCE sz0, d=3, (kappa,eps,c,dd)=(1/2,1/10,1/6,1/10), Lambda=sup lam_n=1/64: c1=min(1/2,kappa^3/(8d Lam))=0.3333, C=4d/kappa^2=48, s0=1-c1=0.6667, (s,t)=(0.66,0.68), cd=1/100
 n=0: t0=0.69374>=s0? True, t>=0.68: True; BAdom True; BAReal(1/2): Im m0=0.9995; window min Im m=0.9995>=1/4: True, Lip=0.0778<=48: True
      con_st_ind: Bctl_t^cd=0.9117 <= (1-t)/(1-s)=0.9412 <1: True; (1-s0)Bctl(s0)=3.097e-05 <= (1-s)Bctl(s)=3.097e-05: True; W^-d<=(g^2+1)Bctl(s0): True
      ConArg' source at (g_s=g0 sqrt(s0/u)=0.01289): Im m(E,g_s)=0.9995>=kappa/2: True; eta_s0=0.3332>=c1*kappa/2=0.0833: True (||G_s0||<=3.00<=2/(c1 kappa)=12)
      A-member tau=0.68687 in [0.68000,0.69374]: Im z'=0.3776, Im m'=0.8284; its source horizon tau*s0/u=0.67340 in [0.66667,0.69374]: True; B-member lam'=0.011873->source 0.011756 in [sqrt(s0) g0,g0]=[0.010626,0.013014]: True
 n=1: t0=0.69444>=s0? True, t>=0.68: True; BAdom True; BAReal(1/2): Im m0=1.0000; window min Im m=1.0000>=1/4: True, Lip=0.0012<=48: True
      con_st_ind: Bctl_t^cd=0.8216 <= (1-t)/(1-s)=0.9412 <1: True; (1-s0)Bctl(s0)=9.331e-10 <= (1-s)Bctl(s)=9.331e-10: True; W^-d<=(g^2+1)Bctl(s0): True
      ConArg' source at (g_s=g0 sqrt(s0/u)=0.00020): Im m(E,g_s)=1.0000>=kappa/2: True; eta_s0=0.3333>=c1*kappa/2=0.0833: True (||G_s0||<=3.00<=2/(c1 kappa)=12)
      A-member tau=0.68722 in [0.68000,0.69444]: Im z'=0.3773, Im m'=0.8290; its source horizon tau*s0/u=0.67375 in [0.66667,0.69444]: True; B-member lam'=0.000186->source 0.000184 in [sqrt(s0) g0,g0]=[0.000166,0.000203]: True
 n=2: t0=0.69444>=s0? True, t>=0.68: True; BAdom True; BAReal(1/2): Im m0=1.0000; window min Im m=1.0000>=1/4: True, Lip=0.0001<=48: True
      con_st_ind: Bctl_t^cd=0.7731 <= (1-t)/(1-s)=0.9412 <1: True; (1-s0)Bctl(s0)=2.128e-12 <= (1-s)Bctl(s)=2.128e-12: True; W^-d<=(g^2+1)Bctl(s0): True
      ConArg' source at (g_s=g0 sqrt(s0/u)=0.00002): Im m(E,g_s)=1.0000>=kappa/2: True; eta_s0=0.3333>=c1*kappa/2=0.0833: True (||G_s0||<=3.00<=2/(c1 kappa)=12)
      A-member tau=0.68722 in [0.68000,0.69444]: Im z'=0.3773, Im m'=0.8290; its source horizon tau*s0/u=0.67375 in [0.66667,0.69444]: True; B-member lam'=0.000016->source 0.000016 in [sqrt(s0) g0,g0]=[0.000015,0.000018]: True
```
`cd $S && head -4 adm.out` (`Admissible`; limits: N_n → ∞, W^6/N → ∞, lam_n/W^{-1.4} = (2(n+1)) → ∞):
```
Admissible(c=1/6, dd=1/10) at sz0, d=3: n, N, N^(1/6)<=W, W^(-d/2+dd)<=lam<=1/dd
  n=0: N=2.097e+06 N^(1/6)=1.131e+01 <= W=3.200e+01: True; W^-1.4=7.813e-03 <= lam=1.562e-02 <= 10: True
  n=1: N=5.498e+11 N^(1/6)=9.051e+01 <= W=1.024e+03: True; W^-1.4=6.104e-05 <= lam=2.441e-04 <= 10: True
  n=2: N=8.125e+14 N^(1/6)=3.055e+02 <= W=7.776e+03: True; W^-1.4=3.572e-06 <= lam=2.143e-05 <= 10: True
```
`cd $S && python3 pre.py` (≈100 s; items (i)–(iv) of the ticket preflight):
```
(i-a) 15 real-axis bulk points, L in {4,6,16}, d=3; #(Im m<0.15)=8; min Im m=0.0559
   max|<|w|^-2>-1|=7.8e-16; max|Re gap - 2b^2<|w|^-4>|=7.8e-16; min gap/(2b^2)=2.320; max|dm/dg formula - central diff|=4.3e-08; max|dm/dg| b^2/d=0.0378 (<=1)
   e.g. L=16 g=1.5 E=6: Im m=0.0957, Re gap=0.8956 >= 2b^2=0.0183
(i-b) 10 (L,g0,E), kappa=Im m(E,g0) in [0.056,..], Lambda=g0, c1 in [1.8e-06,7.1e-03]: min_window Im m/(kappa/2) >= 1.997; max Lip/(4d/kappa^2) = 0.0095;
   stress c1=1/2 (kappa-independent window): Im m leaves [kappa/2,..) in 6/10 cases => c1 must depend on kappa
(ii) 200000 random (t0,c1,u<=t0,s<u,member): violations of [main flow in A(u); tau>=u; A(u) in B(u); ConArg source (A: tau*sc/u in A(sc); B: rho*sqrt(sc/u) in B(sc), sc=max(s,1-c1)); A(t') in A(s') for s'<=t'] = [0, 0, 0, 0, 0, 0]
    fixed window [sqrt(1-c1),1], c1=.3,u=.8,s=.75: bottom target rho=.8367 -> source .8101 < .8367 (outside); cone B(u)-bottom .8944 -> .8660 = B(s)-bottom. t0=.4<1-c1=.7: A(u)={t0} only
(iii) d=3, min over |E|<=2-kappa, g' in (0,g0] of rho=Im m/pi (24 g' log-spaced, 41 E); [all E | E with Im m(E,g0)>=0.05]; rho_sc(2-kappa)=.0994(k=.1), .1677(k=.3)
   L= 4 kappa=0.1: g0=0.5: 0.0994|0.0994   g0=2: 0.0000|0.0000   g0=10: 0.0000|0.0000
   L= 4 kappa=0.3: g0=0.5: 0.1677|0.1677   g0=2: 0.0000|0.0402   g0=10: 0.0000|0.0000
   L=16 kappa=0.1: g0=0.5: 0.0994|0.0994   g0=2: 0.0582|0.0582   g0=10: 0.0000|0.0000
   L=16 kappa=0.3: g0=0.5: 0.1629|0.1629   g0=2: 0.0563|0.0563   g0=10: 0.0000|0.0000
   Sec.51-bulk E=3.2, L=16: Im m(3.2,g')= 0.9:0.2380, 0.5:0.1389, 0.3:0, 0.13:0; 2+2d*0.13=2.78<3.2
(iv) sz0 (kappa=1/2,eps=1/10), n=0,1,2: members tau in {1/2,mid,t0}; z'=(E+(1-tau)m0')/sqrt(tau), m0'=m(E,sqrt(tau)g)
   n=0: L=4 N=2.10e+06 t0=0.69374 E=0.0 Im z_n=0.3675 kappa_0=Im m0=0.9995; max resid(self_m,t0,E)=3.3e-16; Im z' in [0.3675,0.7068], min Im z'/N^(-0.9)=1.8e+05; min Im m'=0.7068 >= kappa/(2sqrt2)=.3536
   n=1: L=8 N=5.50e+11 t0=0.69444 E=0.0 Im z_n=0.3667 kappa_0=Im m0=1.0000; max resid(self_m,t0,E)=2.2e-16; Im z' in [0.3667,0.7071], min Im z'/N^(-0.9)=1.4e+10; min Im m'=0.7071 >= kappa/(2sqrt2)=.3536
   n=2: L=12 N=8.12e+14 t0=0.69444 E=0.0 Im z_n=0.3667 kappa_0=Im m0=1.0000; max resid(self_m,t0,E)=1.1e-16; Im z' in [0.3667,0.7071], min Im z'/N^(-0.9)=9.6e+12; min Im m'=0.7071 >= kappa/(2sqrt2)=.3536
   general: Im z' >= (kappa/(2 sqrt2)) Im z  => BAFlow(eps/2) for all members iff N >= (2 sqrt2/kappa)^(2/eps) = 1.13e+15 (N_0=2.1e6 < this; at sz0 the actual Im z' >= .36 >> N^-.95: no modification needed)
```
`cd $S && python3 gap.py; python3 chk4.py` (gaps are genuine: Im m ∝ η; BAConArg' premise at T2197 data; BAzztE_inv at the supervisor 1806 §1.4 data):
```
L=4 E=-1.045 g'=1.0327: eta=8.9e-04: Im m=6.22e-03; eta=8.6e-05: Im m=6.03e-04; eta=8.2e-06: Im m=5.80e-05 -> Im m(E+i0)=0 (ratio Im m/eta ~ const)
L=16 E=-1.9 g'=6.7002: eta=8.9e-04: Im m=8.97e-04; eta=8.6e-05: Im m=8.63e-05; eta=8.2e-06: Im m=8.30e-06 -> Im m(E+i0)=0 (ratio Im m/eta ~ const)
(4a) T2197 inst_BAConArg data (sz0 n=0, E=0, source g_s=g0*sqrt(s/t), s=1/16,t=1/2 -> g_s=0.00460): min_{g' in (0,g0]} Im m(E,g')=0.9995 >= kappa=1/2: True
(4b) supervisor 1806 s1.4 data via BAzztE_inv (L=16, g=1, tau=.81, E=3.2): m0=-0.2938+0.2380j, z'=3.4935+0.0502j, m(z',1)=sqrt(tau)m0=-0.2644+0.2142j, resid=2.8e-17
```
Stochastic pins (`STKboundg`, `STLKgL`, `STLocalMaxgL`, `BAGbEXPpre`, loop bound at the ConArg source) are other gates' pins: hypotheses of the shape-check examples, not discharged here.

### Verdicts
- Target 0 (vocabulary): PASS (nothing mathematical to fail).
- Target 1 (family pins): PASS. Both families are closed (ii), contain the main flow at every `u ≤ t₀`, and (A) ⊂ (B) (`g'/g₀=√(τ/t₀) ≥ √max(u,1−c₁)`). A fixed window is not closed. (A) needs `BAFlow(κ/(2√2), ε/2)` per member (row 12): general threshold `N ≥ 1.13e15`, so a finite modification is needed in general, none at sz0. Premise for `BAStep1/BAMainInd`: `BAWinBulk sz z c₁ κ'` with `κ' = κ_dom/2` (row 6), i.e. apply the pin at `κ_dom/2`.
- Target 2 (`BAgapReal`, `BAmWindow`, `BAzztE_inv`, `BAWinBulk_of_dom_stmt`): PASS, all four true. `BAgapReal` and `BAzztE_inv` are algebra (checked above: `z'+m' = (E+m₀)/√τ`, `t₀(z',m')=τ`, `E(z',m')=E`). `BAmWindow`/`BAWinBulk_of_dom`: continuation in `g` with rows 1–3. `grep -i gap RBM3D/BA/MFixedPoint.lean` finds no gap statement; inputs are `BAward_avg` and the spectral form of `M²` (the private `MFixedPoint_inv_spectral`, `MFixedPoint.lean:614`).
- Target 3 (ConArg from `s₀`): PASS (rows 8–11; one application per target time `u`, no chain).
- Target 4 (`BAConArg'`): PASS. Added premise at T2197's instance data holds (4a); `BAWinBulk` covers only `[√(1−c₁)g₀, g₀]`, T2197's source coupling `g₀√(1/8)` is below it, so the premise is checked directly there. `BAzztE_inv` is the inversion of the §1.4 data (4b).
- Target 5 (Steps 3–6, gluing): PASS (row 13; `A(t') ⊂ A(s')`, `Fam(t') ⊂ Fam(s')`).
- Target 6 (T2001g): `|E| ≤ 2−κ` does not keep the coupling path in the bulk at d=3: with `E` in the bulk at `g₀` (`Im m ≥ 0.05`) the min of `ρ` over `g' ≤ g₀` is 0.0000 for L=4 (κ=.1: g₀=2,10; κ=.3: g₀=10) and L=16 (g₀=10), and `Im m ∝ η` there (gap.out); for g₀=0.5 it is 0.099–0.168 (≈ρ_sc(2−κ)); grid 24 g' × 41 E, finite L only. So `T2205a` should say "condition of the paper's route, which fails at d=3 for finite L (L=4: g₀ ≥ 2; L=16: g₀=10); not used, route replaced"; §51 set kept (E=3.2, L=16: `Im m` 0.2380 at g'=.9, 0 at g' ≤ .3).
- Targets 7–8 (split, two-data test): PASS (no mathematical obstruction). The window `c₁ ~ κ³` is tiny at the bulk edge (P: 7.3e-4, κ=.56; row 4), nonzero for every κ>0.

## (a′) Preflight corrections — Mon Oct  5 21:50:29 UTC 2026
No verdict of (a) changes.  Differences between (a) and the compiled proofs, none a mistake of (a):
- Rows 2-3: (a) gives the derivative-route window constants `c₁ = min(1/2, κ³/(8dΛ))`, `C = 4d/κ²` (ticket F-d).  The compiled `BAmWindow_holds` uses a one-step Newton contraction: `c₁ = min(1/2, κ⁹/(64dΛ))`, `C = 2d/κ⁴` (valid, weaker; the pin is `∃ c₁ ∃ C`).  The iteration `BAwindow_iter/floor` (floor `3/5`) gives the window at `sz0` for `c₁ = 1/2` (`sz0_win_half`).
- Rows 6, 12: the compiled `BAFlowMember_holds` has `κ' = c_κ κ`, `c_κ = √min(κ/(κ+1), 1/2)`, `ε' = ε/2`; it does not split off the main-flow case, so it is cruder than (a)'s `κ/(2√2)` for small `κ`.  The statement needs only some `κ', ε'`.
- Target 4: confirmed and compiled: the added premise of `BAConArg'` at in-window sources is `sz0_conArg_bulk`; at T2197's own data it is not given by `BAWinBulk` (b.5).

## (b) Script output — Mon Oct  5 21:48:05 UTC 2026
`S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2205`; probe `RBM3D/Probe/T2205Pins.lean` (branch `t/T2205`, base `cef761a`), edited only in the worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2205`; `(law)` below abbreviates `(Sizes.seqP (sz.withLam 0))`.
### b.1 Build, axioms, hygiene
```text
$ cd RBM3D-wt/T2205 && lake env lean RBM3D/Probe/T2205Pins.lean > out.txt 2>&1; echo "exit=$? output_lines=$(wc -l < out.txt)"; tail -5 out.txt   # the probe is outside the library: acceptance is `lake env lean`
exit=0 output_lines=0 real_seconds=28.34
$ git log -1 --format="%h %an: %s"; wc -l < RBM3D/Probe/T2205Pins.lean; git diff --stat main...t/T2205 | tail -2
96e4087 Jun Yin: T2205: probe, general-position main induction through (A) compiled (BAMainIndR_of_c
probe lines: 3989
 RBM3D/Probe/T2205Pins.lean | 3989 ++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 3989 insertions(+)
$ python3 mkax.py $(cat axnames.txt); lake env lean $S/axcheck.lean > axcheck.out; python3 s_axsum.py axcheck.out   # axcheck.lean = the probe with every example renamed to a theorem + a #print axioms line per name + a meta loop over all declarations
#print axioms: 102 lines (53 named theorems + 49 examples renamed ex<k>): 102 x [propext, Classical.choice, Quot.sound]; errors/warnings in the output: 0
meta loop over all constants of the file: 494 declarations; union of axioms = [Quot.sound, Classical.choice, propext]; with a non-standard axiom: []
non-internal names outside RBM.Probe.T2205: 7, all ending in .eq_N/.congr_simp (made by simp/unfold for merged definitions): True
$ grep -cE "sorry|admit|native_decide|(^|[^A-Za-z_])axiom([^A-Za-z_]|$)" RBM3D/Probe/T2205Pins.lean
0
$ grep -nE "^(namespace|end RBM|end Check)" RBM3D/Probe/T2205Pins.lean | tr "\n" " "; grep -cE "^(private )?(theorem|def|abbrev|structure|lemma) +(RBM[.]|_root_)" RBM3D/Probe/T2205Pins.lean   # one namespace; no root-qualified declaration
41:namespace RBM.Probe.T2205 3868:namespace Check 3967:end Check 3987:end RBM.Probe.T2205  -> 0 root-qualified declarations
$ python3 $S/s_clash.py   # last components of the declared names vs every declaration in RBM3D/ of the main worktree (main 5d313ca; branch base cef761a), Probe/ excluded
probe declarations at top level: 271 public, 5 private (outside the Check copy)
public names declared in merged RBM3D/ (same last component, any namespace): 0
private names also declared in merged RBM3D/: 0
$ grep -ci gap RBM3D/BA/MFixedPoint.lean   # (no stability-gap statement in the merged file)
0
$ grep -c "RBM1D\|RBM2D" RBM3D/Probe/T2205Pins.lean   # no text ported from RBM1D/RBM2D (the one hit is a docstring naming RBM2D `s1_h55` as a model)
1
```
### b.2 Target statements (script-extracted from the probe)
```text
$ python3 s_stmt.py BAWinBulk BAFamZ BAFamCone BAStep1 BAMainInd "BAConArg'" BAgapReal BAmWindow BAzztE_inv BAWinBulk_of_dom_stmt BAFamCone_closed_stmt BATrivialLmax BABootstrap BAFlowMember BALmaxFromLK BAFamZ_closed BAwindow_step BAFamZ_main BAStep1_of_parts BA_mainIndR_of_steps BAExactLaw BAMainIndR_of_cover BAMainIndR_pat BA_mainInd_of_regimes   # "line def|theorem name binders : statement", whitespace-normalised; (law) = (Sizes.seqP (sz.withLam 0)); d is a section variable in DetPins/Family
1242 def BAWinBulk (sz : Sizes d) (z : ℕ → ℂ) (c₁ κ : ℝ) : Prop := ∀ (n : ℕ) (g' : ℝ), Real.sqrt (1 - c₁) * BAflowLam0 sz z n ≤ g' → g' ≤ BAflowLam0 sz z n → κ ≤ (BAm d (sz.L n) g' (BAflowEs sz z n : ℂ)).im
1252 def BAFamZ (sz : Sizes d) (z : ℕ → ℂ) (c₁ : ℝ) (u : ℕ → ℝ) (z' : ℕ → ℂ) : Prop := ∀ n, BAflowEs sz z' n = BAflowEs sz z n ∧ min (BAflowT0 sz z n) (max (u n) (1 - c₁)) ≤ BAflowT0 sz z' n ∧ BAflowT0 sz z' n ≤ BAflowT0 sz z n
1247 def BAFamCone (sz : Sizes d) (z : ℕ → ℂ) (c₁ : ℝ) (u lam' : ℕ → ℝ) : Prop := ∀ n, Real.sqrt (max (u n) (1 - c₁)) * BAflowLam0 sz z n ≤ lam' n ∧ lam' n ≤ BAflowLam0 sz z n
1695 def BAStep1 (d : ℕ) : Prop := ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 1 / 100 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) → ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ BAflowT0 sz z n) → (∀ n, s n < t n) → (∀ n, t n ≤ BAflowT0 sz z n) → (∀ z' : ℕ → ℂ, BAFamZ sz z c₁ s z' → STKboundgL (baFMz sz z') (law) ∧ STLKgL (baFMz sz z') (law) s ∧ STLocalMaxgL (baFMz sz z') (law) s) → STConStInd sz 𝔠d s t → ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ t z' → STStep1LoopgL (baFMz sz z') (law) s t ∧ STStep1WeakgL (baFMz sz z') (law) s t
1715 def BAMainInd (d : ℕ) : Prop := 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) → ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ BAflowT0 sz z n) → (∀ n, s n < t n) → (∀ n, t n ≤ BAflowT0 sz z n) → (∀ z' : ℕ → ℂ, BAFamZ sz z c₁ s z' → (STLKgL (baFMz sz z') (law) s ∧ STDecaygL (baFMz sz z') (law) s ∧ STDecayStronggL (baFMz sz z') (law) s ∧ STLocalMaxgL (baFMz sz z') (law) s ∧ STExp2gL (baFMz sz z') (law) s)) → STConStInd sz 𝔠d s t → ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ t z' → STLKgL (baFMz sz z') (law) t ∧ STLmaxgL (baFMz sz z') (law) t ∧ STDecaygL (baFMz sz z') (law) t ∧ STExp2gL (baFMz sz z') (law) t ∧ STLocalEntrygL (baFMz sz z') (law) t ∧ STDecayStronggL (baFMz sz z') (law) t
423 def BAConArg' (d : ℕ) : Prop := ∀ κ ε 𝔡 ε₁ : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → 0 < ε₁ → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, ε₁ ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → (∀ n, κ ≤ (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n).im) → STLmaxgL (baFM sz (BAlamS sz z s t) (BAflowEs sz z)) (law) s → (∀ k : ℕ, 2 ≤ k → BAConArgLoop sz z s t k) ∧ BAConArgVec sz z s t
493 def BAgapReal : Prop := ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hL)⟩ BASelf d L g (E : ℂ) m → 2 * m.im ^ 2 ≤ (1 - (((L ^ d : ℕ) : ℂ))⁻¹ * (BAMB d L g (E : ℂ) m * BAMB d L g (E : ℂ) m).trace).re
504 def BAmWindow (Λ κ : ℝ) : Prop := 3 ≤ d → 0 < Λ → 0 < κ → ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hL)⟩ BAReal d L g κ E m → ∀ g' : ℝ, Real.sqrt (1 - c₁) * g ≤ g' → g' ≤ g → BAReal d L g' (κ / 2) E (BAm d L g' (E : ℂ)) ∧ ‖BAm d L g' (E : ℂ) - m‖ ≤ C * (g - g')
514 def BAzztE_inv : Prop := ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → ∀ (τ E : ℝ) (m₀ : ℂ), haveI : NeZero L := ⟨Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hL)⟩ 0 < τ → τ < 1 → BASelf d L (Real.sqrt τ * g) (E : ℂ) m₀ → BAm d L g (ztOf m₀ E τ / (Real.sqrt τ : ℂ)) = (Real.sqrt τ : ℂ) * m₀ ∧ BAt0 (ztOf m₀ E τ / (Real.sqrt τ : ℂ)) ((Real.sqrt τ : ℂ) * m₀) = τ ∧ BAflowE (ztOf m₀ E τ / (Real.sqrt τ : ℂ)) ((Real.sqrt τ : ℂ) * m₀) = E
1264 def BAWinBulk_of_dom_stmt (d : ℕ) : Prop := 3 ≤ d → ∀ κ Λ : ℝ, 0 < κ → 0 < Λ → ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 2 ∧ ∀ (ε : ℝ) (sz : Sizes d) (z : ℕ → ℂ), (∀ n, 0 < sz.lam n ∧ sz.lam n ≤ Λ) → (∀ n, BAdom d (sz.L n) (sz.size n) (sz.lam n) κ ε (z n)) → BAWinBulk sz z c₁ (κ / 2)
1258 def BAFamCone_closed_stmt (d : ℕ) : Prop := ∀ (sz : Sizes d) (z : ℕ → ℂ) (c₁ : ℝ) (s u lam' : ℕ → ℝ), (∀ n, 0 ≤ sz.lam n) → (∀ n, 1 - c₁ ≤ s n) → (∀ n, s n ≤ u n) → (∀ n, 0 < s n) → BAFamCone sz z c₁ u lam' → BAFamCone sz z c₁ s (fun n => Real.sqrt (s n / u n) * lam' n)
1779 def BATrivialLmax (d : ℕ) : Prop := ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) → ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ → ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ (fun _ => 0) z' → STLmaxgL (baFMz sz z') (law) (fun _ => 1 - c₁)
1810 def BABootstrap (d : ℕ) : Prop := ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 1 / 100 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) → ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ BAflowT0 sz z n) → (∀ n, s n < t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ t z' → STKboundgL (baFMz sz z') (law) → STLKgL (baFMz sz z') (law) s → STLocalMaxgL (baFMz sz z') (law) s → STConStInd sz 𝔠d s t → (∀ u : ℕ → ℝ, (∀ n, max (s n) (1 - c₁) ≤ u n) → (∀ n, u n ≤ t n) → (∀ k : ℕ, 2 ≤ k → BAConArgLoop sz z' (fun n => max (s n) (1 - c₁)) u k) ∧ BAConArgVec sz z' (fun n => max (s n) (1 - c₁)) u) → STStep1LoopgL (baFMz sz z') (law) s t ∧ STStep1WeakgL (baFMz sz z') (law) s t
1796 def BAFlowMember (d : ℕ) : Prop := ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ κ' ε' : ℝ, 0 < κ' ∧ κ' ≤ κ ∧ 0 < ε' ∧ ε' ≤ ε ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) → ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ → ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ (fun _ => 0) z' → ∃ n₀ : ℕ, BAFlow sz κ' ε' 𝔠 𝔡 (fun n => if n < n₀ then z n else z' n)
1789 def BALmaxFromLK (d : ℕ) : Prop := ∀ (sz : Sizes d) (C : FlowFM sz) (τ : ℕ → ℝ), sz.SizeTendsto → (∀ n, 0 ≤ τ n) → (∀ n, τ n < 1) → (∀ᶠ n in atTop, sz.Bctl n (τ n) ≤ 1) → STKboundgL C (law) → STLKgL C (law) τ → STLmaxgL C (law) τ
1478 theorem BAFamZ_closed (sz : Sizes d) (z : ℕ → ℂ) {c₁ κ : ℝ} (hκ : 0 < κ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 2) (hlam : ∀ n, 0 ≤ sz.lam n) (hwin : BAWinBulk sz z c₁ κ) (hT1 : ∀ n, BAflowT0 sz z n < 1) (s u : ℕ → ℝ) (hs : ∀ n, 1 - c₁ ≤ s n) (hsu : ∀ n, s n ≤ u n) (hu : ∀ n, u n ≤ BAflowT0 sz z n) {z' : ℕ → ℂ} (hz' : BAFamZ sz z c₁ u z') : BAFamZ sz z c₁ s (BAzSrc sz z' s u)
884 theorem BAwindow_step (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (hd : 1 ≤ d) {g g' E κ : ℝ} (hκ : 0 < κ) (hg : 0 < g) {m : ℂ} (hm : BASelf d L g (E : ℂ) m) (hκm : κ ≤ m.im) (hg' : g' ≤ g) (hδ : g - g' ≤ κ ^ 9 / (64 * d)) : ∃ m' : ℂ, BASelf d L g' (E : ℂ) m' ∧ ‖m' - m‖ ≤ 2 * d * (g - g') / κ ^ 4 ∧ κ / 2 ≤ m'.im
1294 theorem BAFamZ_main (sz : Sizes d) (z : ℕ → ℂ) (c₁ : ℝ) (u : ℕ → ℝ) : BAFamZ sz z c₁ u z
1830 theorem BAStep1_of_parts (d : ℕ) (hmem : BAFlowMember d) (hL : BALmaxFromLK d) (hT : BATrivialLmax d) (hC : BAConArg' d) (hB : BABootstrap d) : BAStep1 d
2406 theorem BA_mainIndR_of_steps (d : ℕ) (R Rc : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (hRc : ∀ {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ), 3 ≤ d → R sz s t → Rc sz s t) (hK : BAKboundF d) (hKw : BAKwardF d) (h1 : BAStep1 d) (h2 : BAStep2 d) (h3 : BAStep3R d Rc) (h4 : BAStep4R d Rc) (h5 : BAStep5R d R) (h6 : BAStep6R d R) : BAMainIndR d R
2804 def BAExactLaw (d : ℕ) : Prop := ∀ (sz : Sizes d) (φ : ℕ → ℕ), StrictMono φ → (∀ B : Set (szComp sz φ).SeqΩ, Sizes.seqP (sz.withLam 0) (szReindex sz φ ⁻¹' B) = Sizes.seqP ((szComp sz φ).withLam 0) B) ∧ (∀ g : (szComp sz φ).SeqΩ → ℂ, ∫ ω, g (szReindex sz φ ω) ∂(law) = ∫ ω, g ω ∂(Sizes.seqP ((szComp sz φ).withLam 0)))
3111 theorem BAMainIndR_of_cover (hlaw : BAExactLaw d) {ι : Type} [Fintype ι] [Nonempty ι] (Rat : ι → ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → ℕ → Prop) (hcov : 3 ≤ d → ∀ (sz : Sizes d) (s t : ℕ → ℝ), (∀ n, 0 < sz.lam n) → (∀ n, s n < t n) → ∀ n, ∃ k, Rat k sz s t n) (hcomp : ∀ k (sz : Sizes d) (φ : ℕ → ℕ) (s t : ℕ → ℝ) (j : ℕ), Rat k (szComp sz φ) (fun n => s (φ n)) (fun n => t (φ n)) j ↔ Rat k sz s t (φ j)) (h : ∀ k, BAMainIndR d (fun {d} sz s t => ∀ n, Rat k sz s t n)) : BAMainIndR d STAny
3252 theorem BAMainIndR_pat (h₃ : BAMainIndR d STReg5III) (h₁ : BAMainIndR d STReg5I) (h₂ : BAMainIndR d STReg5II) (h₄ : BAMainIndR d STReg5IV) : ∀ b : ℕ, b ≤ 3 → ∀ a : ℕ, a ≤ b → BAMainIndR d (BAPat a b)
3293 theorem BA_mainInd_of_regimes (d : ℕ) (hlaw : BAExactLaw d) (h₃ : BAMainIndR d STReg5III) (h₁ : BAMainIndR d STReg5I) (h₂ : BAMainIndR d STReg5II) (h₄ : BAMainIndR d STReg5IV) : BAMainInd d
$ python3 s_stmt.py BAgapReal_holds BAzztE_inv_holds BAmWindow_holds BAWinBulk_of_dom_holds BAFamCone_closed BAFlowMember_holds BALmaxFromLK_holds   # joined with ";"
BAgapReal_holds (d : ℕ) : BAgapReal d;BAzztE_inv_holds (d : ℕ) : BAzztE_inv d;BAmWindow_holds (d : ℕ) (Λ κ : ℝ) : BAmWindow d Λ κ;BAWinBulk_of_dom_holds (d : ℕ) : BAWinBulk_of_dom_stmt d;BAFamCone_closed (d : ℕ) : BAFamCone_closed_stmt d;BAFlowMember_holds (d : ℕ) : BAFlowMember d;BALmaxFromLK_holds (d : ℕ) : BALmaxFromLK d
```
### b.3 Comparisons with the check file and the T2161/T2173 probe texts; compiled nonempty instances (first instance of each endpoint theorem: `d = 3`, merged `sz0`, one-point flow `(L, g) = (4, 10)` of `MFixedPointInst`)
```text
$ python3 checkdiff.py   # check-file pins (docs/tickets/checks/T2205-check.lean) vs the probe: Check copy and probe definitions
check file docs/tickets/checks/T2205-check.lean lines 121-222 vs the probe (whitespace-normalised declarations; Check copy = probe lines 3868-3967)
  Check copy == check text for all 8 pins: True
  probe definition identical to the check text: BAgapReal, BAmWindow, BAzztE_inv, BAWinBulk_of_dom_stmt, BAFamCone_closed_stmt
  equal after replacing the written-out terms by the T2197 names BAflowT0/BAflowEs/BAflowLam0 (and {d} by the section variable): BAWinBulk, BAFamCone, BAFamZ
  differing in any other way: []
$ grep -c "^example.*Check[.]" RBM3D/Probe/T2205Pins.lean; grep -n "^example.*Check[.]" ... | sed -n "1p;\$p"   # the rfl / proof examples of section 8, all inside the compiled file
13
3971:example (d : ℕ) : BAgapReal d = Check.BAgapReal d := rfl
3985:example (d : ℕ) : Check.BAWinBulk_of_dom_stmt d := BAWinBulk_of_dom_holds d
$ python3 vocabdiff.py   # T2161 (82e72b3) / T2173 (a543154) probe texts read with git show vs the vocabulary region of the probe; the line list is in the portmap P.9
vocabulary region of the probe: lines 45-478, 354 non-blank; source: T2161 (82e72b3) + T2173 (a543154) ranges, 257 non-blank lines
  probe lines identical to a source line: 246; changed or new: L1 13, L3 8, L2 (STMainIndG) 13, L4 (bridges) 39, L5 (BAConArg') 7, doc/comment 21, structure 7; unexplained non-doc: 0; source lines absent from the probe: 24
$ git show main:RBM3D/Induction/SizesComp.lean > a_src/RBM3D/Induction/SizesComp.lean (last commit touching it: 8810a23); lake env lean --root=a_src -o a_build/RBM3D/Induction/SizesComp.olean ...   # main's T2206 file in this worktree's environment
exit=0 output_lines=0
$ cp the olean into the worktree build cache (.lake, untracked); lake env lean a_test.lean; rm the olean   # a_test.lean: import SizesComp, the probe definitions szComp, szReindex, BAExactLaw, two rfl examples, theorem BAExactLaw_of_T2206 := ⟨seqP_withLam_reindex_preimage .. 0 .., integral_reindex ..⟩
'RBM.Probe.T2205.BAExactLaw_of_T2206' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
olean removed from the worktree cache: yes; worktree status lines: 0
definitions copied into a_test.lean identical to the probe (whitespace-normalised): szComp True, szReindex True, BAExactLaw True
$ python3 s_inst.py   # label, line, kind, docstring (the older (A) feasibility examples of 6.5/7.3 are not listed)
gap                       3678 example      `BAgapReal` at the real-axis data of the flow point: `Re (1 - 4^{-3} tr M²) ≥ 2 (Im m₀)²` at `L 
zztE_inv                  3672 example      `BAzztE_inv` at these data: the inverse of `zztE_BA` returns `m(z', 10) = √t₀ m₀`, horizon `t₀`,
window                    3663 example      The window at the flow point of `(L, g) = (4, 10)` (`BAmWindow_holds`; no hypothesis): the chain
WinBulk_of_dom            3597 example      `BAWinBulk_of_dom` along `sz0` (`κ = 1/2`, `Λ = 1/64`): the window in the `1/4`-bulk (`BAmWindow
window sz0 (iterated)     3464 sz0_win      The window along `sz0`, proved (deterministic, no hypothesis): for every `c₁` with `1 - √(1 - c₁
closure (A)               3566 example      The ConArg source of the main flow at the ConArg regime: `c₁ = 1/3`, source time `s ≡ 2/3 = 1 - 
closure (B)               3582 example      Route (B): the cone is closed under the rescaling, at the same data.
finite modification       3762 example      The member transfer: a single-flow pin (a tail-local `Q` at every `z''` with `BAFlow`) gives `Q`
Step 1 skeleton           3696 example      example (hT : BATrivialLmax 3) (hC : BAConArg' 3) (hB : BABootstrap 3) : BAStep1 3 := BAStep1_of
ConArg premise            3521 example      `BAConArg'` applied at `sz0` (`κ = ε = 𝔡 = 1/10`, `ε₁ = 1/2`, `(s, t) = (2/3, 17/25)`): the adde
regime step               3699 example      Regime (iii) of Steps 3-6: Steps 3-4 in case I (`STCaseI_of_STReg5III`).
regime gluing             3719 example      The four regimes glued in generic position (`BA_mainInd_compose` three times).
general-position main step  3725 example      The main induction in general position (target 5, `BA_mainInd_of_regimes`): the four regime pins
pattern pin (1,2)         3729 example      The pin of the stage pattern `(a, b) = (1, 2)` (regimes (i) and (ii), glued at the cut `c₂`).
pattern (0,3) at sz0      3743 example      `(s, t) = (0, 1 - lam²/(2 L³))` is the pattern `(0, 3)` at every size of `sz0` (all four stages 
pattern (0,0) at sz0      3733 example      The pattern predicates at `sz0`: `(s, t) = (0, 1/16)` is the pattern `(0, 0)` (regime (iii)) at 
BAStep1 at sz0            3532 inst_BAStep1 `BAStep1`, instantiated: `κ = ε = 𝔡 = 1/10`, `sz0`, `z_n = zSeq`, `c₁ = 1/3`, `(s, t) = (0, 1/16
BAMainInd at sz0          3545 inst_BAMainInd `BAMainInd`, instantiated at the same data: the constant `𝔠_d`, then the one-step statement for 
```
### b.4 Window constants (numerics) and the `STMainIndF` measurement
```text
$ python3 s_win.py
d=3, E at the kappa-bulk edge of g0 (kappa = Im m(E,g0)), Lambda = g0, window g' in [sqrt(1-c1) g0, g0] (400-point grid, Newton continuation)
c1(Lean)=min(1/2,k^9/(64 d Lam)), C(Lean)=2d/k^4; c1* = largest c1 (bisection) with min Im m >= kappa/2; Lip over the c1* window
 L   g0    E    kappa   c1(Lean)   c1*      c1*/c1(Lean)  minIm/kappa  Lip(c1*)   C(Lean)   Lip<=C   (6 of the 10 rows shown)
 4  0.90  0.50  0.5347  2.07e-05   0.5000    2.42e+04      1.0001     0.2319       73.4  True
 4  1.00  6.00  0.0751  3.97e-13   0.1430     3.6e+11      0.5000     5.1469   188303.0  True
 6  4.00  8.75  0.0559  6.98e-15   0.0016    2.34e+11      0.5000     8.6033   613075.7  True
16  1.50  6.00  0.0957  2.34e-12   0.1985    8.47e+10      0.5000     2.2389    71467.3  True
16  0.90  2.00  0.3981  1.45e-06   0.5000    3.44e+05      1.0002     0.4739      238.9  True
16  2.00  0.30  0.2233  3.60e-09   0.5000    1.39e+08      1.0006     0.1290     2411.5  True
c1 = 1/2 is admissible in 4 of 10 rows; Lean constants are conservative (c1* >= c1(Lean) in all rows: True); Lip <= C on the c1* window in all rows: True
$ awk (non-blank lines of `def STMainIndF`; of the band bridge `STMainInd_iff_F`) stf.lean   # draft in stf.lean, between BEGIN/END-STMainIndF
  def STMainIndF: 17 lines
  band bridge (a proof, not Iff.rfl): 12 lines
$ lake env lean $S/stf.lean   # vocabulary + the two declarations
  exit=0 output_lines=       0
$ lake env lean $S/stf2.lean   # probe + the draft + `BAMainInd d <-> STMainIndF ... := Iff.rfl`
/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2205/stf2.lean:4024:106: error: Type mismatch
  Iff.rfl
has type
  ?m.37 ↔ ?m.37
```

### b.5 Narrative (every number is from b.1-b.4, section (a) or the files named)
- **Target 0.** The vocabulary region of the probe equals the T2161/T2173 probe texts except L1 13, L3 8, L2 13, L4 39, L5 7 lines, 21 docstring lines and 7 `section`/`variable` lines; 0 unexplained (b.3; full list portmap P.9).  `STMainInd_iff`, `STStep1_iff` and the 13 `bandFM_*` bridges are `Iff.rfl`/`rfl`.
- **Target 1: route (A).**  Compiled reasons: the chain pins a member's Steps 1-6 consume (`BAGbEXP`, `BAConArg'`, `BAKbound`, `BAStep2`, `BAEMn2Exp`, ticket F-g) are indexed by a spectral parameter with `BAFlow`; `BAmember_transfer` (any tail-local `Q`) and `BAFlowMember_holds` (finite modification, `κ' = c_κ κ`, `ε' = ε/2`) apply them to a member; the ConArg source of a member is a member (`BAzSrc_spec`, `BAFamZ_closed`, built with `BAzztE_inv_core`); (A) ⊂ (B) (`BAFamZ_subCone`); (B) is closed too (`BAFamCone_closed`) but needs carrier forms of those pins and a flow-data setting.  A fixed window is not closed ((a) (ii)).  `BAWinBulk` is a premise so that `BAStep1`, `BAMainInd` and the induction composing them use one `c₁`.  One addition to the ticket's shape: `∀ n, 0 < sz.lam n` (T2205d).  `STMainIndF`: not used.  The definition (17 non-blank lines) plus the band bridge (12, a proof, not `Iff.rfl`) are 29 lines for `BAMainInd` alone; the BA bridge is not `Iff.rfl` either (b.4) and `BAStep1` needs its own copy.
- **Target 2.**  All four pins are compiled theorems: gap 149 probe lines (2.1, with the public spectral form of `tr M²`; `BAward_avg` is not used, `⟨|w|^{-2}⟩ = 1` is the imaginary part of `(self_m)`), `BAzztE_inv` 73 (2.2), `BAmWindow` 485 (2.3; over the 200-line bound: a one-step Newton contraction `BAwindow_step` plus an iteration), `BAWinBulk_of_dom` 28 (3.2).  `MFixedPoint` has no gap statement (b.1).  Merged facts used: portmap P.8.  `∀ n` premises (§29 (4)): met by `0 < lam n ≤ Λ` and `BAdom` pointwise, with `c₁` before the sequence.  The constants are valid but conservative (b.4: `c₁*/c₁(Lean)` up to 4·10^11).
- **Target 3.**  Skeleton `BAStep1_of_parts` / `BAStep1_of_pins` compiled from the pins `BATrivialLmax`, `BABootstrap`, `BAConArg'` (owed) and the proved `BAFlowMember_holds`, `BALmaxFromLK_holds`, with the window and the closure of the family.  Missing link: `BAGbEXP` inside `BABootstrap` (the forbidden-region estimate needs the event form, T2205e).
- **Target 4.**  `BAConArg'` is verbatim (b.2).  It is what the skeleton applies, to the finite modification of the member, from `max(s, 1-c₁)`.  At T2197's data `(s,t) = (1/16, 1/2)` the source `g₀√(1/8)` is below the window `[√(1-c₁) g₀, g₀]`, so `BAWinBulk_of_dom` does not give the premise ((a) (4a): true, 0.9995); T2197's instance should take `s ≥ 1-c₁` (compiled: `sz0_conArg_bulk`, `(s,t) = (2/3, 17/25)`).  `BAzztE_inv` is the inversion `not_BAConArg_of_norm` needs ((a) (4b): `L=16, g=1, τ=.81, E=3.2`, residual 2.8e-17; it needs `BASelf` at `(g₀, E)` = `(0.9, 3.2)`).
- **Target 5.**  Compiled: the per-regime assemblies `BA_mainIndR_of_steps` (regimes (iii), (i), (ii), (iv)) and the whole general-position step `BA_mainInd_of_regimes` (6.7): `BAMainIndR_pat` glues the regime pins into the pins of the 10 nonempty stage patterns `(a,b)` through the cuts (`BA_mainInd_compose`); `BAMainIndR_of_cover` applies the pin of each infinite pattern class along its subsequence (`Nat.nth`), carries the hypotheses at `s` down (`*_fwd`, through the extension of a member by the main flow) and the six conclusions back through the finite cover (`*_cov`).  Its one input from (A) is `BAExactLaw`, the exact image law of the BA law for every set and every integrand; T2206 (ST-A, `main` 8810a23, merged after this branch's base) proves it: `BAExactLaw_of_T2206` compiles in scratch against main's file (b.3).  Consumers of (A): BA-V2b only, now a port of probe 6.5-6.7.  T2161 has no `BAStep3..6` pin, so no row of the S3-27/S5-29/S6-13 kind exists; BA-U3, U6, V1 keep their rows (portmap P.4).
- **Target 6.**  From (a) (iii), not rerun: `|E| ≤ 2-κ` does not keep the coupling path in the bulk at `d = 3` (L=4: `g₀ ≥ 2`; L=16: `g₀ = 10`); T2205a.  **Targets 7, 8.**  Portmap P.1-P.3 and P.6; the six extreme inputs are compiled or scripted (b.3, b.4).

## (c) Verified Mathlib names (`names_check.lean`: the selected, less common names the probe uses, each checked with `#check`; none invented)
```text
$ lake env lean names_check.lean   # #check of 38 selected Mathlib names that the probe uses (exit 0); 17 shown, full output in names_check.out
present @ContractingWith.exists_fixedPoint' : ∀ {α : Type u_1} [inst : EMetricSpace α] {K : NNReal} {f : α → α} {s : Set α}, IsComplete 
present @LipschitzWith.of_dist_le_mul : ∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] {K :
present @Measure.le_map_apply : ∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α} {f : α
present @Measure.eq_infinitePi : ∀ {ι : Type u_1} {X : ι → Type u_2} {mX : (i : ι) → MeasurableSpace (X i)} (μ : (i : ι) → Measure (X i)
present @Matrix.IsHermitian.mulVec_eigenvectorBasis : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {n : Type u_2} [inst_1 : Fintype n] {A : Matrix
present Complex.abs_im_le_norm : ∀ (z : ℂ), |z.im| ≤ ‖z‖
present @norm_sub_le_norm_sub_add_norm_sub : ∀ {E : Type u_1} [inst : SeminormedAddGroup E] (a b c : E), ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖
present @Real.le_sqrt_of_sq_le : ∀ {x y : ℝ}, x ^ 2 ≤ y → x ≤ √y
present @Real.sqrt_le_one : ∀ {x : ℝ}, √x ≤ 1 ↔ x ≤ 1
present @exists_nat_ge : ∀ {R : Type u_1} [inst : Semiring R] [inst_1 : PartialOrder R] [IsOrderedRing R] [Archimedean R] (x : R), ∃ n, 
present @div_le_div_of_nonneg_right : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [MulPosReflectLT G₀] {a b c
present @div_left_inj' : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] {a b c : G₀}, c ≠ 0 → (a / c = b / c ↔ a = b)
present Nat.even_or_odd' : ∀ (n : ℕ), ∃ k, n = 2 * k ∨ n = 2 * k + 1
present @Set.mem_ofPred_eq : ∀ {α : Type u_1} {x : α} {p : α → Prop}, (x ∈ {y | p y}) = p x
present @Nat.nth_strictMono : ∀ {p : ℕ → Prop}, (Set.ofPred p).Infinite → StrictMono (Nat.nth p)
present @Nat.range_nth_of_infinite : ∀ {p : ℕ → Prop}, (Set.ofPred p).Infinite → Set.range (Nat.nth p) = Set.ofPred p
present @Finset.lt_inf'_iff : ∀ {α : Type u_1} {ι : Type u_2} [inst : LinearOrder α] {s : Finset ι} (H : s.Nonempty) {f : ι → α} {a : α}
absent  Unknown identifier `div_left_injective₀`
absent  Unknown constant `Real.sqrt_le_one_of_le`
absent  Unknown constant `Complex.abs_im_le_abs`
```

## (d) Open issues and paper-delta candidates
- Owed pins introduced or reshaped here (class and owner rows: portmap P.2): `BATrivialLmax` (BA-S2a), `BABootstrap` (BA-S2b), `BAStep1` (BA-S3), `BAMainIndR`, `BAMainInd` (BA-V2a/b), `BAStep3R..6R` (BA-U/V1), `BAConArg'` (BA-S1).  Proved in the probe, to be ported: BA-D8 (window, gap, `BAzztE_inv`), BA-S3 (`BAFlowMember`, `BALmaxFromLK`, family closure).
- The probe base `cef761a` precedes T2204 (S6-01), T2206 (ST-A) and T2211.  The probe's `szComp`, `szReindex` are `Sizes.comp`, `Sizes.reindex` of T2206 by `rfl` (b.3): port with T2206's names; the ST-side shapes copied for `BAStep6R` must be rechecked against the merged `Induction/Step6Pins.lean` when BA-V2a is written.
- T2197 `inst_BAConArg'`: use `(s, t)` with `s ≥ 1 - c₁` (b.5).  The window constants are conservative (b.4); constants need not be optimal, but `c₁` is as small as `10^{-13}` at a bulk edge with `κ ≈ 0.07`.
- Not done: no proof of `BATrivialLmax`, `BABootstrap`, `BAConArg'`, or the step pins (owed rows); no event-form restatement of `BAGbEXP` (T2205e).
- **T2205a** (T2001g, target 6): the `|E| ≤ 2-κ` of `zztE_BA` (`7_8:1797`) is a condition of the paper's route (ConArg chain from `t ≈ 0`), not a typo; it fails to keep the coupling path in the bulk at `d = 3` for finite `L` ((a) (iii): L=4, `g₀ ≥ 2`; L=16, `g₀ = 10`; `Im m ∝ η` there); not used, the route is replaced (the §51 set `ρ_N(E) ≥ κ` is kept; the window `BAWinBulk` takes its place).
- **T2205b**: Step 1 of `lem:main_ind_BA` (`7_8:1987-1990`, "the same as [RBSO1D, Section 7.1]") and the induction hold over the family `Fam(u)` of flows: `lem_ConArg_BA` (`7_8:1956-1966`) bounds the loops of the flow `(E, g₀)` at `t` by those of the flow `(E, g_s)`, `g_s = g₀√(s/t)`, at `s` (`BAlamS`; `BAzSrc_spec`: source horizon `t₀(z') s/u`), and needs `Im m(E, g_s) ≥ κ` (F1: `BAConArg` is false without it).
- **T2205c**: the gap `Re(1 - L^{-d} tr M²) ≥ 2 (Im m)²` (`BAgapReal_holds`) and the window `c₁ = min(1/2, κ⁹/(64dΛ))`, `C = 2d/κ⁴` (`BAmWindow_holds`) are not in the paper; the commented-out `7_8:1812-1813` ("`z_t` stays within the bulk ... provided `t ≥ 1 - ε`, `ε` small depending on `κ`") is the continuous form.
- **T2205d**: the family pins carry `∀ n, 0 < sz.lam n`; `BAFlow` gives positivity only eventually (`WO`); conclusions are eventual, so consumers pass to a tail (`Sizes.comp`, `comp_admissible`).
- **T2205e**: T2161's `BAGbEXP` (`:1115`) has global premises (`(initialGT2)`, `𝓛^{(2)} ≺ Φ²`) and no event; the band's `STGiiGEX`, `STGijGEX`, `STGavLGEX` (`Induction/Defs.lean:202`) carry `1(Ω(t,ε₀))` and `step1TargetV3_holds` (`Induction/Step1.lean:525`) uses them: BA-G6 / BA-S2b need the event form (risk for BA-G3, G4, G6, S2b).
