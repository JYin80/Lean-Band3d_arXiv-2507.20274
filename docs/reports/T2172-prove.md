Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct  5 04:28:24 UTC 2026
Notation (d≥3, one time u): m=M_u⁻¹=(W^d(1−u))⁻¹, 1≤M_u≤W^d (`LemDecCalE_e2`); ℓ_u=1 (`ellT=min(max(lam/√(1−u),1),L)`, `Defs/Params.lean:32`, =1 as lam²≤1−u, 3≤L); P=L^dW^{6d}, X=P⁻¹; ℓ*=(log W)^{3/2}≥8; ℓ**=4(log P)²; Y=(log W)^{3/4}; T=tailTD d W u D; δ=zdistInf(a₀−a₁); Λ,K₀,J≥1; fG(p,q)=max(‖G_pq‖,‖G_qp‖) (G(−)=G(+)ᴴ).
Scripts (scratchpad `T2172/`): `tok.sh consts2.py chain.py inst.py sqrtconv.py wgnum.py trichk.py consumer.py`, driver `run_all.sh`; outputs pasted in (ii).

### (i) Exponent table
| # | quantity | value / derivation | constraint | slack |
|---|---|---|---|---|
| 1 | `d=2` tokens (counts in the `tok.sh` output below) | `Z2→Zd d L`; `zdist2→zdistInf`; `(W:ℝ)^2→W^d`; `scaleM=W²ℓ²η→M_u=W^d(1−u)`; `etaT`, `ρ=ℓ_u/ℓ_s`, endpoint `v`, `tailT…v` vanish (conclusion at `u`: `tailTD d W u D`, no `tailT_mono_scale`); `(L:ℝ)^2*(W:ℝ)^12→P`; `25→9^d` (e7), `50→2·9^d` (e8, long edge), `125→3^d√5·√(ΛJ)·X`, `225→9^{d+1}`; `30000ℓ²M⁻¹→C_sq(d)M⁻¹`; `(2R+1)^2→(2R+1)^d`; `ellStar→ℓ*`; `jStarMat^2→J^{3/2}` | every token replaced, none ported | script count only |
| 2 | target 2, route (T2a) `√(Ae^{−√p}+w)≤√A e^{−√p/2}+√w`; (T2b) `e^{−(√p+√q)/2}≤e^{−√r/2}(e^{−√p/4}+e^{−√q/4})`, `r≤p+q` = `LemDecCalE_exp_conv` at (p,q,r)/4, `r=zdistInf(a₀−a₁)≤p+q` by the triangle inequality; (T2c) `Σ_x ≤ 2S_{¼}Ae^{−√r/2}+(2S_{½}+1)√(Aw)` with `wL^d≤√(Aw)` ⇔ `wL^{2d}≤A` | `S_γ=Σ_z e^{−γ√∣z∣_∞}≤(1+96/γ′⁴)^d`, `γ′=γ/d`: `S_{¼}≤Ŝ:=(1+24576d⁴)^d`, `S_{½}≤(1+1536d⁴)^d≤Ŝ` (product bound of `LemDecCalE_sum_zd_le`, `γ=(4d)⁻¹`); `a+b≤√2√(a²+b²)` with `a²+b²=A(Ae^{−√r}+w)`; **`C_sq(d)=5Ŝ`** (3√2=4.24≤5); `d=3`: Ŝ=7.89e18, `C_sq(3)=3.94e19` | floor `wL^{2d}≤A` at `A=M_u⁻²`, `w=W^{−D}`: `W^{−D}L^{2d}≤P⁻²L^{2d}=W^{−12d}≤W^{−2d}≤M_u⁻²` (slack `W^{10d}≥W^{30}`); numeric: worst LHS/RHS(C_sq:=1)=333.5 (L≤9) vs 3.94e19 (slack 1.2e17) |
| 3 | floors in the near case (`δ≤ℓ*`): beyond `ℓ**`, e7 applies (`ℓ**≥ℓ*/8+2`, as `ℓ*≤(log W)²≤(log P)²`, `log P≥6d·log W≥72`); `W^{−D}≤P⁻²`; `T(x−2)≤M_u⁻²e^{−(2log P−1)}+P⁻²≤(e+1)P⁻²≤4P⁻²` (`√(4Λ²−2)≥2Λ−1` for Λ=log P≥¾); `fG²≤9^dΛ(1+4J)P⁻²` ⇒ `fG≤3^d√(5ΛJ)X` | far-y sum `≤L^d·2·(2Λ)²·fG=8√5·3^dΛ^{5/2}J^{1/2}W^{−6d}` (`L^dX=W^{−6d}`), times prefactor `Λ(1−u)⁻¹`; needs `≤(1−u)⁻¹·m^{1/2}J^{3/2}·M_u⁻²e^{−Y}·c`, i.e. `W^{−6d}≤M_u^{−5/2}` and `J^{1/2}≤J^{3/2}`: **no `J≤W`** (RBM2D uses `hJW` only at `LemDecCalEwG.lean:695`, `near_sum`; none of the 10 other occurrences is a use) | `ℓ**−(ℓ*/8+2)≥2·10⁴`; floor `W^D/P²`=2² at (a), 2^{0.45} at (b); `W^{−6d}/M_u^{−5/2}`=2.5e−32 at (a), 1.4e−76 at (b) (`chain.py`); close `y`: `(2ℓ**+1)^d≤(9(log P)²)^d` (log P≥1): 2.59e15≤3.69e15 at (a); normalisation `m²≤e^Y T(δ)`: `LemDecCalE_e4c`, `C=1`, `T(δ−ℓ*)≥M_u⁻²` as `δ≤ℓ*` |
| 4 | power of `J`: near close `J⁰`; near far-y `J^{1/2}`; far, `y` within `ℓ*/2` of `a₁` or `a₂`: two long edges `fG²≤2·9^dΛJe^YT(δ)` (e7, `W^{−D}≤T≤Je^YT`, shift by 2 and `tail_le_Y`; AM–GM) = `J¹`, times `avg≤(2Λ+2·3^d√(ΛK₀J))√m` (e8: `fG²≤2·9^dΛK₀m(1+Jm)≤4·9^dΛK₀Jm`; diagonal `2ΛW^{−d}≤2Λ√m`) = `J^{1/2}`; far, three long edges: `(3^{d+1}√(ΛJ))³=3^{3d+3}(ΛJ)^{3/2}` times target 2 (`≤C_sq m√T(δ)`) | total `J^{3/2}` in every configuration; edge lengths: `δ>ℓ*`, `x≥δ−ℓ*/2≥ℓ*/8+2` and `x−2≥δ−ℓ*` (as `ℓ*≥8`) | RBM2D's `J²` has **two** sources: `fG_off` (`≤10ΛK₀J√m`, `:839`) and the weakening `hk3: k³≤(225ΛJ)²` (`:1107`, in `far_sum`); both are weakenings, neither is forced: keeping `√J` and `k³` gives `J^{3/2}` |
| 5 | counts and loss: `(2ℓ**+1)^d≤9^d(log P)^{2d}`; `(ℓ*+1)^d≤(9/8)^d(1+log P)^{2d}`; prefactor `W^dΛm=Λ(1−u)⁻¹` (`LemDecCalE_e1`); coefficients (×`Λ^aK₀^be^Y`, absorbed by `Λ⁶K₀²e^{8Y}` of `lossE2`): N1=`2·9^d` [with `(log P)^{2d}`] (close), N2=`8√5·3^d` (near far-y), F1=`8·9^d(9/8)^d(2+2·3^d)` [with `(1+log P)^{2d}`] (far, averaged edge), F2=`2C_sq(d)3^{3d+3}` (far, three long edges) | **`κ_wG(d)=1000^d`**, `lossE2wG=lossE2·1000^d·(1+log P)^{2d}`: need max(N1,N2,F1,F2)≤`10¹²(1600d⁴)^d·κ_wG` for all d≥3 (F2≤270·(663579d⁴)^d≤10¹²(1.6·10⁶d⁴)^d); polylog in N times `e^{O(Y)}` | min margin over d (decades; `consts2.py`) 10.7 at d=3, 11.1 at d=4, 12.6 at d=8, 17.2 at d=20, using no growth of `log P`; at the instances (a),(b) 47.7, 67.1 decades (`chain.py`); `κ=1` is negative from d=4 without `log P≥72`, so not chosen |
| 6 | general `σ∈{±}²`: loops `L3(σ₀σ₀σ₁;(y,a₀,a₁))`, `L3(σ₀σ₁σ₁;(a₀,y,a₁))`; prefactors `⟨G̃(σ₀)E_x⟩`, `⟨G̃(σ₁)E_x⟩` (e9 for both signs); `Σ_x‖SB_{xy}‖=1`; `tri` sign-free since `‖G(σ)_{pq}‖≤fG(p,q)`; swap `tri(c₁,c₂,c₃)=tri(c₂,c₁,c₃)` | 3-loop clause for every `σ:Fin 3→Bool`, `a` | `trichk.py`: `∣L3∣/tri≤0.56` over 8 sign patterns, 19683 triples; swap defect 6.5e−19; four `σ` in `wgnum.py` |
| 7 | consumer (§45 O2): RHS of `LemDecCalE_wGShape` vs `Step5Pins.lean:171-177` (u:=p.1, a:=p.2.2, J:=Jst n u D, `loss·` removed): identical (`consumer.py`); `STEGt=STEGtM…(seqHflow n u ω)` (`Step2Defs.lean:312`); paper `3_5:2322-2325`: `(1−u)⁻¹[1(∣a₁−a₂∣≤(log W)^{3/2})+(W^d∣1−u∣)^{−1/2}(J*)^{3/2}]T_{u,D}`, same structure | new premise 3-loop ← `STLmaxU` (`Step34Pins.lean:176`, hypothesis of `STIngR5`, `Step5Pins.lean:91`) at `k=3`: `≺Bctl²`, `Bctl=W^{−d}[(lam²+(1−u))⁻¹+(L^d(1−u))⁻¹]≤2m` (`Sizes.lean:214`, `Params.lean:36`, `K=0`); new premise floor `P²≤W^D` ← **missing** (only `size≤W^D`, `Step5Pins.lean:163`; `size=(WL)^d`, `Sizes.lean:157`; floor ⇔ `W^D≥size²W^{10d}`); T2164's M2, M3 still open | S5-09 must add the floor (extends T2164 M1) |

### (ii) One concrete nondegenerate instance
Data (a) `sz0`, n=1: d=3, L=8, W=1024, lam=1/4096, E=1/2, u=0, D=38, M=0, Λ∈{1,2}, K₀=J=1. (b) `szCL`, n=0: L=2·24⁵, W=2²⁴, lam=1, D=42. All 12 numeric premises of `E2HypWG` (3≤d, |E|<2, 0≤u<1, lam>0, lam²≤1−u, 1≤lam²W^d, 1≤Λ,K₀, 4≤log W, `L^dW^{2d}≤W^D`, `P²≤W^D` in exact integers, 1≤J≤W, 3-loop at M=0) hold; the other conjuncts of `E2Hyp` at M=0 are those of `LemDecCalE_e2Hyp_zero`. 3-loop at M=0,u=0: `L3=m₁m₂m₃·tr(E_{a₀}E_{a₁}E_{a₂})=W^{−2d}·1(a₀=a₁=a₂)` (∣m∣=1) ≤ `Λ·W^{−2d}`; alternative `(Im m(E))⁻³=1.10≤Λ=2`. Concrete computation of the 3-loop premise (`Λ₃=max∣L3∣/m²`) at `M=0`, `u=0` on a torus: the `wgnum.py 0.0 …` command below (=1.000).
`wgnum.py` (d=3, E=1/2, W=2, L=3 and 5, random Hermitian `M`): `Λ,K₀,J` are the minimal values ≥1 making (e6), (e7/8), (e9), the 3-loop clause, the `K` bound and `∣L−K∣≤J·T` hold; `D` is the least integer with `P²≤W^D`; `4≤log W` and the Kell* clause are not imposed (log 2<4), so it tests the shape of the inequality only; computed `J=1`, so the exponent of `J` is not exercised numerically (row 4 is by mathematics).
$ bash tok.sh
token:count in LemDecCalEwG.lean(1402 lines) / TailSums.lean 74-84,586-722
 [Z2]:59/9 [zdist2]:71/27 [(W : ℝ) ^ 2]:38/4 [scaleM]:35/6 [etaT]:6/0 [ellT]:41/4 [tailT L W E D v]:14/0 [(L : ℝ) ^ 2 * (W : ℝ) ^ 12]:11/0 [25]:39/5 
[50]:24/0 [125]:14/0 [225]:13/0 [30000]:8/5 [(2 * R + 1) ^ 2]:2/0 [ellStar]:32/1 [jStarMat L W E D u M ^ 2]:2/0
hJW uses in RBM2D wG, excluding the 10 'obtain ... facts h' lines:
695:      mul_le_mul_of_nonneg_right hJW (by positivity)
$ python3 consts2.py | grep -E "^ +(3|4|8|20) |^ d"
 d   N1     N2     F1     F2    | avail(k=1)  avail(k=1000^d) | min margin k=1  min margin k=1000^d  (F2 w/o log P growth)
  3    3.2   2.7   5.7   25.6 |    27.3      36.3 |      1.7      10.7
  4    4.1   3.2   7.1   35.4 |    34.4      46.4 |     -0.9      11.1
  8    7.9   5.1  13.1   77.9 |    66.5      90.5 |    -11.4      12.6
 20   19.4  10.8  30.9  223.0 |   180.2     240.2 |    -42.8      17.2
$ python3 chain.py | grep -E "kappa|min slack|T\(l"
kappa_wG(3)=1000^3=1000000000.0 ; C_sq(3)=3.9442e+19 ; S_{3,1/4}<= 7.8884e+18 ; S_{3,1/2}<= (1+1536*81)^3 = 1.9259e+15
    T(l**-2)*P^2 = 1.0000 <= 4 : True ; far-y: W^{-6d}=6.525e-55 <= M^{-5/2}=2.647e-23 : True
    log10: N1(near,1)=17.7 N2(near,J^{3/2})=4.5 F1(far,avg)=11.2 F2(far,conv)=25.6  vs  lossE2wG=73.4  -> min slack 47.7 decades
    T(l**-2)*P^2 = 1.0000 <= 4 : True ; far-y: W^{-6d}=9.017e-131 <= M^{-5/2}=6.525e-55 : True
    log10: N1(near,1)=22.0 N2(near,J^{3/2})=6.3 F1(far,avg)=14.6 F2(far,conv)=25.6  vs  lossE2wG=92.7  -> min slack 67.1 decades
$ python3 inst.py | grep -E "^== |premises|log2 P|l\*=|Im m|^\(c\)"
== instance (a) sz0 n=1 : L=8 (3<=L True) W=1024 lam=1/4096 D=38 Lam=1
   premises true: 12/12 (false: [])
   log W=6.9315  l*=(log W)^{3/2}=18.2490  log P=131.005  l**=4(log P)^2=68649.0  l*/8+2=4.281 <= l** True
   log2 P^2 = 378.0000 , log2 W^D = 380.0000 , slack (bits) = 2.0000
== instance (a) with Lam=2 : L=8 (3<=L True) W=1024 lam=1/4096 D=38 Lam=2
   premises true: 12/12 (false: [])
   log W=6.9315  l*=(log W)^{3/2}=18.2490  log P=131.005  l**=4(log P)^2=68649.0  l*/8+2=4.281 <= l** True
   log2 P^2 = 378.0000 , log2 W^D = 380.0000 , slack (bits) = 2.0000
== instance (b) szCL n=0 : L=15925248 (3<=L True) W=16777216 lam=1 D=42 Lam=1
   premises true: 12/12 (false: [])
   log W=16.6355  l*=(log W)^{3/2}=67.8508  log P=349.190  l**=4(log P)^2=487734.2  l*/8+2=10.481 <= l** True
   log2 P^2 = 1007.5489 , log2 W^D = 1008.0000 , slack (bits) = 0.4511
Im m(1/2) = sqrt(15)/4 = 0.968246 ; (Im m)^{-3} = 1.101649 <= 2 (Lam0=2): True
(c)-a: a=![0,e0], |a0-a1|_inf = 1 <= l*(a)=18.249 -> near branch: True
(c)-b: a=![0,100 e0], |a0-a1|_inf = 100 > l*(b)=67.851 -> far branch: True ; need L>=201: True
$ python3 sqrtconv.py | grep -E "C_sq|w L\^6/A=1 |largest|instance"
C_sq(3) = 5 (1+24576*81)^3 = 3.9442e+19
L=3  w L^6/A=1       max LHS/(sqrtA sqrt(A e^-sqrt r + w)) =   17.1929 at (a1,r)=((0, 0, 1), 1)
L=4  w L^6/A=1       max LHS/(sqrtA sqrt(A e^-sqrt r + w)) =   38.9528 at (a1,r)=((0, 0, 2), 2)
L=5  w L^6/A=1       max LHS/(sqrtA sqrt(A e^-sqrt r + w)) =   68.7898 at (a1,r)=((0, 0, 2), 2)
L=6  w L^6/A=1       max LHS/(sqrtA sqrt(A e^-sqrt r + w)) =  117.8354 at (a1,r)=((0, 0, 3), 3)
L=7  w L^6/A=1       max LHS/(sqrtA sqrt(A e^-sqrt r + w)) =  170.5893 at (a1,r)=((0, 3, 0), 3)
L=8  w L^6/A=1       max LHS/(sqrtA sqrt(A e^-sqrt r + w)) =  255.1614 at (a1,r)=((4, 0, 0), 4)
L=9  w L^6/A=1       max LHS/(sqrtA sqrt(A e^-sqrt r + w)) =  333.4516 at (a1,r)=((0, 0, 4), 4)
largest ratio over L<=9 and the four w-levels = 333.4516 ;  ratio / C_sq(3) = 8.454e-18
instance (d): w L^6 = 2^-362 <= A = 2^-60 : True ; LHS = 8.265315e-17 ; sqrtA sqrt(A e^-1 + w) = 5.260815e-19 ; LHS/that = 157.1109 ; LHS <= C_sq*that: True
$ python3 wgnum.py 0.3 0.5 0.0 3 5   (u=0.3, lam=0.5, no perturbation, L=3 and 5, W=2, E=1/2)
L=3  dim=216  (build 0.2s)   M_u=W^d(1-u)=5.60  D=46 (P^2<=W^D: True)
  premise constants: Lam6=0.635 Lam78=0.025 Lam9=0.515 Lam3=0.622 -> Lam=1.000 ; K0=1.000 ; J=1.000 ; l*=(log W)^{3/2}=0.577
  max|EGt|/[(1-u)^-1(1(near)+m^{1/2}J^{3/2})T], all (a0,a1), (near/far) per sigma ++,+-,-+,--: 0.140/0.052  0.077/0.050  0.077/0.050  0.140/0.052
  => implied loss <= 0.140 over all 4 sigma (pinned lossE2wG(3) >= 1e27)
L=5  dim=1000  (build 25.0s)   M_u=W^d(1-u)=5.60  D=50 (P^2<=W^D: True)
  premise constants: Lam6=0.599 Lam78=0.030 Lam9=0.629 Lam3=0.664 -> Lam=1.000 ; K0=1.000 ; J=1.000 ; l*=(log W)^{3/2}=0.577
  max|EGt|/[(1-u)^-1(1(near)+m^{1/2}J^{3/2})T], all (a0,a1), (near/far) per sigma ++,+-,-+,--: 0.152/0.090  0.165/0.086  0.165/0.086  0.152/0.090
  => implied loss <= 0.165 over all 4 sigma (pinned lossE2wG(3) >= 1e27)
$ python3 wgnum.py 0.0 0.5 0.0 3 | grep premise   (u=0, M=0, L=3, W=2: three-loop premise Lam3 = max|L3|/m^2, exactly W^{-2d}/m^2 = 1)
  premise constants: Lam6=0.000 Lam78=0.000 Lam9=0.000 Lam3=1.000 -> Lam=1.000 ; K0=1.000 ; J=1.000 ; l*=(log W)^{3/2}=0.577
$ python3 wgnum.py 0.74 0.5 0.8 3    (1-u=0.26 >= lam^2=0.25, diagonal perturbation 0.8)
  premise constants: Lam6=1.363 Lam78=0.062 Lam9=1.053 Lam3=0.183 -> Lam=1.363 ; K0=1.000 ; J=1.000 ; l*=(log W)^{3/2}=0.577
  max|EGt|/[(1-u)^-1(1(near)+m^{1/2}J^{3/2})T], all (a0,a1), (near/far) per sigma ++,+-,-+,--: 0.038/0.083  0.071/0.183  0.071/0.183  0.038/0.083
  => implied loss <= 0.183 over all 4 sigma (pinned lossE2wG(3) >= 1e27)
$ python3 trichk.py
max over 8 sign patterns and all 19683 block triples of |L3|/tri = 0.5597  (<= 1 required)
tri symmetric in (c1,c2): max |tri[a,b,c]-tri[b,a,c]| = 6.51e-19
$ python3 consumer.py | tail -1
IDENTICAL after removing the outer parenthesis of `loss * (...)`: True

### Verdict
- Target 1 (`E2HypWG`, `lossE2wG` with `κ_wG(d)=1000^d`, `LemDecCalE_wG`): PASS. All premises hold at once at (a) and (b); the loss closes for every d≥3 (row 5).
- Target 2 (`LemDecCalEwG_sum_sqrt_tail`): PASS. Route closes with `C_sq(d)=5(1+24576d⁴)^d` under `wL^{2d}≤A` (row 2; `d=3`: worst measured ratio 333.5 ≤ 3.94e19).
- Target 3 (`lemDecCalE_wG`, every σ, `J^{3/2}`): PASS. Every configuration gives `J^{3/2}`; `J≤W` is not needed; no forced `J²` (rows 3, 4, 6). Stop-and-report conditions of the ticket: none triggered.
- Target 4 (`LemDecCalEwG_hyp_zero`): PASS. Numeric premises of `LemDecCalE_e2Hyp_zero` with the floor `P²≤W^D` and `1≤Λ` give `E2HypWG` at `M=0`; 3-loop clause is exactly `W^{−2d}` (row 7, (ii)).
- Flag, not a failure of T2172: the floor `(L^dW^{6d})²≤W^D` has no `STIngR5` source (row 7), nor have T2164's M2, M3; they are for S5-09.

## (b) Script output (stage 1b; worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2172`, branch `t/T2172`; scripts in scratchpad `T2172/`)
$ date -u
Mon Oct  5 05:16:28 UTC 2026
$ git log -1 --format='%h %s' t/T2172; git diff --stat main...t/T2172 | tail -2; wc -l RBM3D/Path/LemDecCalEwG.lean
ac6a3f6 T2172: LemDecCalEwG docstring: sources of the square-root convolution and line cites
 RBM3D/Path/LemDecCalEwG.lean | 2510 ++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 2510 insertions(+)
    2510 RBM3D/Path/LemDecCalEwG.lean
$ lake build RBM3D.Path.LemDecCalEwG 2>&1 | grep -E 'LemDecCalEwG|error|Build completed'   # the fresh build before commit ac6a3f6 printed '✔ [3781/3781] Built RBM3D.Path.LemDecCalEwG (20s)'
Build completed successfully (3781 jobs).
$ lake build 2>&1 | tail -1   # whole library (RBM3D.lean does not yet import the module: the hub adds the import at merge)
Build completed successfully (3943 jobs).
$ grep -nE 'sorry|admit|native_decide|^axiom' RBM3D/Path/LemDecCalEwG.lean | wc -l
       0
$ lake env lean axioms.lean   # #print axioms of every new public declaration
'RBM.Path.E2HypWG' [propext, Classical.choice, Quot.sound]
'RBM.Path.lossE2wG' [propext, Classical.choice, Quot.sound]
'RBM.Path.LemDecCalE_wG' [propext, Classical.choice, Quot.sound]
'RBM.Path.LemDecCalEwG_sum_sqrt_tail' [propext, Classical.choice, Quot.sound]
'RBM.Path.lemDecCalE_wG' [propext, Classical.choice, Quot.sound]
'RBM.Path.LemDecCalEwG_hyp_zero' [propext, Classical.choice, Quot.sound]
'RBM.Path.LemDecCalEwG_inst' [propext, Classical.choice, Quot.sound]
'RBM.Path.LemDecCalEwG_inst_CL' [propext, Classical.choice, Quot.sound]
$ python3 extract.py 'def E2HypWG' 'def lossE2wG' 'def LemDecCalE_wG (d' 'theorem LemDecCalEwG_sum_sqrt_tail' 'theorem lemDecCalE_wG' 'theorem LemDecCalEwG_hyp_zero'
64: def E2HypWG {d : ℕ} (sz : Sizes d) (n : ℕ) (E u D Λ K₀ J : ℝ)
65:     (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : Prop :=
66:   E2Hyp sz n E u D Λ K₀ J M ∧
67:     (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D ∧
68:     ∀ (σ : Fin 3 → Bool) (a : Fin 3 → Zd d (sz.L n)),
69:       ‖STLM sz n E u M σ a‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2
74: def lossE2wG (d L W : ℕ) (Λ K₀ : ℝ) : ℝ :=
75:   lossE2 d L W Λ K₀ * ((1000 : ℝ) ^ d * (1 + Real.log ((L : ℝ) ^ d * (W : ℝ) ^ (6 * d))) ^ (2 * d))
81: def LemDecCalE_wG (d : ℕ) : Prop :=
82:   ∀ (sz : Sizes d) (n : ℕ) (E u D Λ K₀ J : ℝ)
83:     (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
84:     E2HypWG sz n E u D Λ K₀ J M → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
85:       ‖STEGtM sz n E u M σ a‖ ≤ lossE2wG d (sz.L n) (sz.W n) Λ K₀ *
86:         ((1 - u)⁻¹ *
87:           ((if ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤
88:                 Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) +
89:             (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 / 2 : ℝ)) *
90:           STtailTD sz n u D a)
318: theorem LemDecCalEwG_sum_sqrt_tail {d L : ℕ} [NeZero L] (hd : 1 ≤ d) {A w : ℝ} (hA : 0 ≤ A)
319:     (hw : 0 ≤ w) (hfl : w * (L : ℝ) ^ (2 * d) ≤ A) (a₀ a₁ : Zd d L) :
320:     ∑ x : Zd d L, Real.sqrt (A * Real.exp (-Real.sqrt (zdistInf d L (x - a₁) : ℝ)) + w) *
321:         Real.sqrt (A * Real.exp (-Real.sqrt (zdistInf d L (a₀ - x) : ℝ)) + w) ≤
322:       5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d * Real.sqrt A *
323:         Real.sqrt (A * Real.exp (-Real.sqrt (zdistInf d L (a₀ - a₁) : ℝ)) + w) :=
1995: theorem lemDecCalE_wG (d : ℕ) : LemDecCalE_wG d :=
2233: theorem LemDecCalEwG_hyp_zero (sz : Sizes d) (n : ℕ) {E D Λ K₀ J : ℝ} (hd : 3 ≤ d)
2234:     (hE : |E| < 2) (hlam : 0 < sz.lam n) (hlam1 : sz.lam n ^ 2 ≤ 1)
2235:     (hlamW : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) (hΛ : 1 ≤ Λ) (hK : 1 ≤ K₀)
2236:     (hlog : 4 ≤ Real.log ((sz.W n : ℕ) : ℝ))
2237:     (hfloor : (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤
2238:       ((sz.W n : ℕ) : ℝ) ^ D)
2239:     (hJ : 1 ≤ J) (hJW : J ≤ ((sz.W n : ℕ) : ℝ)) :
2240:     E2HypWG sz n E 0 D Λ K₀ J
2241:       (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
$ python3 inst_list.py   # compiled nonempty instances (first and last line of each block)
2283-2308: theorem LemDecCalEwG_inst :
      last line: · rw [hWc]; norm_num
2313-2331: theorem LemDecCalEwG_inst_CL :
      last line: · rw [szCL_W_real]; norm_num
2388-2398: example :
      last line: lemDecCalE_wG 3 sz0 1 (1 / 2) 0 38 1 1 1 0 LemDecCalEwG_inst _ _
2401-2407: example : 0 < lossE2wG 3 (sz0.L 1) (sz0.W 1) 1 1 * ((1 - (0 : ℝ))⁻¹ *
      last line: lemDecCalEwG_rhs_pos LemDecCalEwG_inst _
2411-2421: example :
      last line: lemDecCalE_wG 3 szCL 0 (1 / 2) 0 42 2 1 1 0 LemDecCalEwG_inst_CL _ _
2424-2430: example : 0 < lossE2wG 3 (szCL.L 0) (szCL.W 0) 2 1 * ((1 - (0 : ℝ))⁻¹ *
      last line: lemDecCalEwG_rhs_pos LemDecCalEwG_inst_CL _
2442-2455: example : ((zdistInf 3 (sz0.L 1) (![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1] 0 -
      last line: linarith
2459-2486: example : ¬ (((zdistInf 3 (szCL.L 0) (![(0 : Zd 3 (szCL.L 0)), Pi.single 0 100] 0 -
      last line: linarith
2490-2506: example :
      last line: exact zpow_le_zpow_right₀ (by norm_num) (by norm_num)) 0 (Pi.single 0 1)
$ python3 diffs.py   # against docs/tickets/checks/T2172-check.lean section 2 and Step5Pins.lean:171-177
E2HypWG: check file 6 lines, T2172 6 lines, identical: True
LemDecCalE_wG body vs LemDecCalE_wGShape body (loss -> lossE2wG): 9 vs 9 lines, identical: True
RHS of LemDecCalE_wG (inside `lossE2wG * (...)`) vs Step5Pins.lean:171-177 (inside `fun n p _ => ...`) after u:=p.1, a:=p.2.2, J:=Jst n u D: identical: True
$ for n in E2HypWG lossE2wG LemDecCalE_wG lemDecCalE_wG LemDecCalEwG_sum_sqrt_tail LemDecCalEwG_hyp_zero LemDecCalEwG_inst LemDecCalEwG_inst_CL; do grep -rnw "$n" /Users/junyin/Lean_proof/RBM3D/RBM3D --include='*.lean' | grep -v Path/LemDecCalEwG.lean | wc -l; done   # main worktree; printed as name=count
E2HypWG=0 lossE2wG=0 LemDecCalE_wG=0 lemDecCalE_wG=0 LemDecCalEwG_sum_sqrt_tail=0 LemDecCalEwG_hyp_zero=0 LemDecCalEwG_inst=0 LemDecCalEwG_inst_CL=0 
$ grep -rln 'LemDecCalEwG' /Users/junyin/Lean_proof/RBM3D/RBM3D | wc -l   # the prefix itself
       0
$ grep -n hJW RBM3D/Path/LemDecCalEwG.lean   # the conjunct 'J <= W' of E2Hyp (T2164 M3): named only in the premise of hyp_zero
2239:    (hJ : 1 ≤ J) (hJW : J ≤ ((sz.W n : ℕ) : ℝ)) :
2258:  refine ⟨LemDecCalE_e2Hyp_zero sz n hd hE hlam hlam1 hlamW hΛ hK hlog hfloor' hJ hJW, hfloor, ?_⟩
$ grep -c -- '-, hLK, hK14, hK15' RBM3D/Path/LemDecCalEwG.lean   # destructurings of E2Hyp that clear the conjunct J <= W
10
$ premise sources (Consumers paragraph): STLmaxU, the only size premise of STLemDecCalEConcl, STLmaxU in STIngR5
176:def STLmaxU (E s t : ℕ → ℝ) : Prop :=
   180: (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (k - 1))
   Step5Pins.lean:163: ∀ D : ℝ, 0 < D → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ D) →
   Step5Pins.lean:91: STStep2Concl sz (STflowE z) s t Cd → STLmaxU sz (STflowE z) s t → STLKU sz (STflowE z) s t →
$ registry pre-check: lake env lean precheck.lean  (import RBM3D; import RBM3D.Path.LemDecCalEwG; #assert_rbm_axioms)
exit=0
axiom audit: 5120 theorems, 1769 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
lines of the output mentioning E2HypWG/LemDecCalE_wG/lossE2wG: 0
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks log -1 --format=%h; git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Path/LemDecCalEwG.lean RBM2D/Path/TailSums.lean
9e0f275
 RBM2D/Path/LemDecCalEwG.lean |  50 ++++------------
 RBM2D/Path/TailSums.lean     | 137 ++++++++++---------------------------------
 2 files changed, 43 insertions(+), 144 deletions(-)
(no RBM1D file was ported: no RBM1D command was run)

### Narrative
- Module `RBM3D/Path/LemDecCalEwG.lean` (2510 lines; commits c3e8b95 and ac6a3f6, the second changes docstrings only) imports only `RBM3D.Path.LemDecCalE`, not `Step2Iterate`/`Split`: `ST_Gres_false`, `st5_ellT_one` and the `M = 0` lemmas are copied as private `lemDecCalEwG_*`.
- Layout: §0 `:56` pinned vocabulary (`E2HypWG` and the `LemDecCalE_wG` body verbatim, script diff above; `lossE2wG` with `κ_wG(d) = 1000^d`); §1 `:92` lattice helpers; §2 `:261` target 2; §3 `:458` `wt`, `tri`, `avg` for an abstract symmetric edge bound `f` on `Vtx d L W`; §4 `:676` `fG`, (e6)-(e8), prefactor; §5 `:914` near; §6 `:1193` far; §7 `:1765` loss, `near_norm`, `lemDecCalE_wG`; §8 `:2121` target 4; §9 `:2267` instances.
- Ports (RBM2D `c9a24cf`, read with `git show c9a24cf:<path>`): §3-§7 follow `LemDecCalEwG.lean:90-1385` with the replacements of preflight row 1 (`Z2 L -> Zd d L`, `BlockIndex -> Vtx`, `25,50,125,225 -> 9^d, 2·9^d, 5·9^d, 9^(d+1)`, `(2R+1)^2 -> (2R+1)^d`, `L²W¹² -> P`); the fine entries are read on `Vtx` by `lemDecCalEwG_Gres_blockMat` (`:698`, `Gres (blockMat M) = (Gres M).submatrix e.symm e.symm`). Target 2 (`:318`) is proved by the ticket's route (T2a)-(T2c); RBM2D `TailSums.lean` was used for its statement (`:74`) only.
- Constants: `fG_near_far` (`:973`) gives `fG ≤ 5·9^d Λ J P⁻¹` (weaker than preflight row 3, enough as `J ≤ J^{3/2}`). `loss_ge` (`:1777`) bounds the three constants (near `2·9^dΛ²(1+log P)^{2d}e^Y` and `40·9^dΛ⁴e^Y`; far `2Λ(16·27^dΛ²K₀e^Y(1+log P)^{2d} + 27^(d+1)C_sq(d)Λ²)`) by `lossE2wG` through `c0 = (1600d⁴)^d 1000^d` and the factors 2, 40, 302 against `10^12`; `27(1+24576d⁴) ≤ 1.6·10⁶ d⁴` is where `κ_wG = 1000^d` is used.
- `J^{3/2}`: both RBM2D weakenings are absent. `fG_off` (`:1301`) keeps `√J` (`fG ≤ 2·3^dΛK₀√J√m`); `far_pt` (`:1398`) keeps `k³` and `lemDecCalEwG_k_cube_le` (`:1538`) gives `k³ ≤ 27^(d+1)Λ²J√J`; `J√J = J^{3/2}` by `lemDecCalEwG_rpow_three_halves` (`:1984`). The far-`y` term of the near case is `J¹` and uses `W6_le` (`:1963`, `W^{-6d} ≤ M_u⁻²√(M_u⁻¹)`); `J ≤ W` is not used (grep above).
- Every `σ`: `EGt_le_pref` (`:849`) uses (e9) at both signs; `loops_le_tri` (`:1075`) bounds the two three-loops of `STEGtM` by `2·tri(a₀,y,a₁)`; no case split on `σ`.
- Target 4 (`:2233`): the three-loop at `M = 0`, `u = 0` is computed exactly (`lemDecCalEwG_STLM_zero_three` `:2212`, `|𝓛^(3)| ≤ W^{-2d}`), so only `1 ≤ Λ` is needed; `L^dW^{2d} ≤ W^D` follows from `(L^dW^{6d})² ≤ W^D`.
- Instances: (a) `LemDecCalEwG_inst` (`sz0`, `n = 1`, `Λ = 1`, `D = 38`), (b) `LemDecCalEwG_inst_CL` (`szCL`, `n = 0`, `Λ = 2`, `D = 42`). `lemDecCalE_wG 3` is applied at (a) with `σ = (+,+)`, `a = (0,e₁)` (`:2388`; indicator 1, `:2442`) and at (b) with `σ = (+,-)`, `a = (0,100e₁)` (`:2411`; indicator 0, `:2459`); right sides `> 0` (`:2401`, `:2424`); `LemDecCalEwG_sum_sqrt_tail` at `d = 3`, `L = 8`, `A = 2^-60`, `w = 2^-380` (`:2490`). At `M = 0` the left sides are expected to be `0` (`G = mI`; not proved here), so the examples test the hypotheses and the shape, not the sharpness; section (a) `wgnum.py` runs test random Hermitian `M`.
- §29 (5)-(7): the premises are deterministic at one time `u`; every lower bound (those of `E2Hyp`, the floor) is a premise and `ℓ_u = 1` is derived by `lemDecCalEwG_ellT_one` (`:767`) from `lam² ≤ 1-u`; the right side of `LemDecCalE_wG` equals `Step5Pins.lean:171-177` (script diff above); the `STIngR5` sources of the two new premises are in (d).
- `(a′)`: none, no step of section (a) was found wrong. No stop-and-report condition of the ticket arose; no pinned signature was changed.

## (c) Verified Mathlib names used (all compiled in `LemDecCalEwG.lean`; none looked up as absent)
`Real.exp_half`; `Real.sqrt_div`; `Real.sqrt_mul`; `Real.sqrt_le_iff`; `Real.sqrt_lt'`; `Real.le_sqrt`; `Real.le_sqrt_of_sq_le`; `Real.mul_self_sqrt`;
`Real.sqrt_eq_rpow`; `Real.sqrt_eq_zero_of_nonpos`; `Real.rpow_add`; `Real.rpow_lt_rpow`; `Real.rpow_le_rpow_of_exponent_le`; `Real.rpow_natCast`;
`Real.pow_div_factorial_le_exp`; `Real.exp_nat_mul`; `Real.log_pow`; `Real.le_log_iff_exp_le`; `Real.exp_one_lt_d9`; `Real.log_two_gt_d9`; `Real.log_two_lt_d9`;
`sum_Ioo_inv_sq_le`; `Finset.sum_range_reflect`; `Finset.prod_univ_sum`; `Fintype.piFinset_univ`; `Fintype.sum_equiv`; `ZMod.val_cast_of_lt`;
`Matrix.inv_submatrix_equiv`; `Matrix.nonsing_inv_eq_ringInverse`; `Matrix.diagonal_mul_diagonal`; `Matrix.trace_diagonal`;
`pow_le_pow_left₀`; `pow_le_pow_right₀`; `pow_le_one₀`; `le_self_pow₀`; `one_le_pow₀`; `inv_anti₀`; `inv_le_one_of_one_le₀`; `zpow_le_zpow_right₀`; `zpow_add₀`.

## (d) Open issues and paper-delta candidates
- Premises S5-09 must supply for `E2HypWG` (Consumers paragraph; `STIngR5` sources in the grep above): the three-loop clause <- `STLmaxU` at `k = 3` (`Step34Pins.lean:176`, `≺ Bctl^2`) with `Bctl ≤ 2 (W^d(1-u))⁻¹`, deterministic at one `u`; the floor `(L^dW^{6d})² ≤ W^D` has **no source** (`Step5Pins.lean:163` gives only `size ≤ W^D`); T2164's M2 (the `GijGEX` conjunct) and M3 (`J ≤ W`, carried by `E2Hyp`, unused here) are still open.
- Size: 2510 lines against the estimate 1600-1800; three `maxHeartbeats` raises (`:1600`, `:1772`, `:1989`), each with a reason comment.
- RBM2D HEAD `9e0f275` differs from the pinned `c9a24cf` in both ported files (diff stat above); the port follows `c9a24cf`.
- Registry: the pre-check passes with no entry; `E2HypWG` is concluded by `LemDecCalEwG_hyp_zero`, `LemDecCalE_wG` by `lemDecCalE_wG`; `Test/Axioms.lean` is not touched.
- Paper-delta candidates (the dispatcher numbers them):
  - T2172a: three-loop premise `|𝓛^(3)_{u,σ,a}| ≤ Λ (W^d(1-u))^-2` for every `σ, a` (clause 2 of RBM2D `goodSet` at `k = 3`), not carried by `E2Hyp`: third conjunct of `E2HypWG`.
  - T2172b: floor `(L^dW^{6d})² ≤ W^D`, stronger than D374's `L^dW^{2d} ≤ W^D` and than the paper's `W^D ≥ N`; no `STIngR5` source.
  - T2172c: every `σ ∈ {±}²` (RBM2D `EGt` at `(+,-)` only): (e9) at both signs, `norm_loop3_le_tri` sign-free.
  - T2172d: `J^{3/2}` as in the paper (RBM2D's pin has `J²`): `√J` kept in `fG_off`, `k³` kept in `far_pt`.
  - T2172e: `lossE2wG = lossE2 · 1000^d (1 + log P)^{2d}`, `P = L^dW^{6d}`.
  - T2172f: `LemDecCalEwG_sum_sqrt_tail`, `C_sq(d) = 5 (1 + 24576 d⁴)^d` under `w L^{2d} ≤ A` (RBM2D: `30000 ℓ² M_u⁻¹` under `L² ≤ W^{D/2-2}`).
  - T2172g: `J ≤ W` not used; the near far-`y` term is `W^{-6d} ≤ M_u⁻² √(M_u⁻¹)` (RBM2D uses `hJW`, `LemDecCalEwG.lean:695`).
