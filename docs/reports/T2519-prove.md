Prover model: claude-sonnet-5-5
## (a) Math preflight — Fri Oct 16 11:06:24 UTC 2026
Notation (maths only). Grid time `k`: one-time Gaussian law `H = gΨ_I + X`, `E|X_xy|² = Ŝ_{[x][y]}/W^d`, `Ŝ = t₁·1 + σJ`, `u = t₁ + L^dσ ≤ 1`, `z_u = E+(1-u)m`, `η_u = (1-u)Im m`, `Λ_u = (Nη_u)⁻¹`; `T(q,a) = twTr(q,a) = W^{-d}Σ_i (G−M)_{(q,i),(a,i)}`; `g_r = W^{-d}Σ_{i}G_{(r,i),(r,i)}`, `d_p = Σ_r Ŝ_pr (g_r − m)` (`Σ_r Ŝ_pr = u`). Targets: T7 = `T2519_HoffBA` (`T(q,a) ≺ Λ_u` from PB, `docs/tickets/checks/T2519-pins.lean`), T15 = `T2519_KdiscBA`, T16 producers, T1 vocabulary. `SCR` = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d6ebe5cd-b9c4-4c2a-9b3c-fa912982a931/scratchpad`.
### (i) Exponent table
| # | quantity | value / constraint | slack |
|---|---|---|---|
| 1 | Stein identity (exact: `G−M = −M(X+um)G`, `E[X_xyΦ]=S_xyE∂_{h_yx}Φ`) | `E T(q,a) = Σ_p M_qp E[d_p(M_pa+T(p,a))]`; `E|T|² = Σ_p M_qp E[d_p(M_pa+T(p,a)) conj T(q,a)] + E R₂`, `R₂ = Σ_p M_qp W^{-2d}Σ_{ij}Σ_y S_{(p,i)y} G_{y,(a,i)} conj(G_{y,(a,j)} G_{(q,j),(p,i)})` (= `𝒮₂` of `T2398-TL-proofs.md:77-84`, grid profile) | MC z-scores 1.6 / 0.3 / 0.5 (runs A / B / X); control (R₂ dropped) off by 1.65e-1 vs |diff| 6.6e-3 (A) |
| 2 | self-term (C5S-C2): `T(p,a)` is in its own leading term | coefficient `Σ_p|M_qp||d_p| ≤ CM·u·ρΛ_u`, `ρ=N^{ε/4}` (PB `lk 1`), absorbed iff `α = CM ρ Λ_u ≤ 1/2`; else `Nη_u ≤ N^{2ε}` and `|T| ≤ ‖G−M‖_max ≺ Λ_u^{1/2} ≤ N^{ε}Λ_u` (PB `localLaw`) is trivial. Premises used: PB, `BAReal`, `baM_row_l1`; no `L`, `g` in `α` | nontrivial regime `α ≤ CM N^{-7ε/4} ≤ 1/2` iff `N ≥ (2CM)^{4/(7ε)}`: ε=0.1: N ≥ 3.7e40; ε=0.02 along `sz0`: α=2.56 (n=100), 3.2e-3 (n=1000) |
| 3 | `CM` (`baM_row_l1` `GreenStab:116`; `BAct_rate` `CombesThomas:45`; `expC` `RadialSum:271`) | `d=3, κ=1/2, Λ=1/64`: c₀=0.25, CM=6.29e6; `ρ₂ = max Σ_b|M_ab||M_bc| ≤ 1` (`baM_rho2`) | true row ℓ¹ 1.10 (×5.7e6 slack, a constant) |
| 4 | **`R₂` exponent (the derivative term)** | closes at `|R₂| ≲ Λ_u²`: HS-pairing `|R₂| ≤ Σ_p|M_qp| W^{-2d}‖X^{(p)}‖_HS‖Y^{(p)}‖_HS`, `‖X^{(p)}‖²_HS` = loop of length **4** (`tr(E_aG*E_pGE_aG*E_pG)`), `‖Y^{(p)}‖²_HS` = 2-loop: `(Λ³·Λ)^{1/2} = Λ²`. With entrywise inputs only (`localLaw`, Λ^{1/2} per entry) `|R₂| ≲ Λ_u^{3/2}`, so `X² ≤ αX + Λ^{3/2}` gives `T ≺ Λ_u^{3/4}` | needed exponent 2, available from `lk ≤ 3` + `localLaw`: 3/2 (slack −1/2 on `R₂`, −1/4 on `T`); MC: CS(HS)/Λ² = 3.387 (N=512), 3.378 (N=1728) constant; abs-sum/Λ^{3/2} = 2.27, 1.87 constant, abs-sum/Λ² = 3.37 → 5.12 grows |
| 5 | `n0` of PB (`lk k`, `k ≤ n0`; pinned `n0=3` in `T2519_PBBA`) | R₂ needs `L^{(4)} ≺ Λ³`, `L^{(2)} ≺ Λ` at the same grid time: `lk 4` and `‖Kt_k‖ ≲ (2Λ_u)^{k-1}` (k=2,4): needs `n0 ≥ 4` (T2398 Step 4 uses (I3) at n=4, 2). Repair inside C5 (no `RBG_*` change; PB, KF are RBG arguments): `n0=4`, K lengths `≤ 4·n0 = 16` (`gueK_existsBA` takes `n0`, `GUEKPrim:1015`), `gueGridK` exponent `32n0+64`: 160 → 192; band `GUEPathBounds`, `PathBounds:331` are `n0`-generic (`2 ≤ n0`) | pinned 3 vs needed 4: **slack −1**; 192 ≥ 20+2c for every c ≤ 86 |
| 6 | K-bound (`STKboundgL` `Carrier:147`, `baKbound_holds` `KBound:245`, needs `BAFlow` ∀ n): `‖K^{(k)}‖ ≺ (W^{-d}B_{τ,0})^{k-1}`, `B = (g²+1−τ)⁻¹ + (L^d(1−τ))⁻¹` | `W^{-d}B ≤ 2/(N(1−τ))` iff `L^d(1−τ) ≤ λ²` (`h730`); `(N(1−τ))⁻¹ = Λ_u Im m ≤ Λ_u` | S0: 0.344 ≤ 0.440 (×1.28) |
| 7 | twist moment `p`, Markov (T.7 Step 6) | `p ≥ D/ε + 1`, `P(|T|>N^{2ε}Λ) ≤ (C_pN^{-ε})^{2p} ≤ N^{-D}`; union over ≤ N² pairs and the grid | ε=0.1, D=5: p=51 |
| 8 | `RBG_Prod` scale premises (`RandomLayerBG:72-85`) | `fT−t1 ≤ N^{-τD}√fT Im z`; `(N√fT Im z)⁻¹ ≤ N^{-τD}`; `L^d(1−t1) ≤ λ²`, `≤ 1`; `Admissible 1/6 1/10` (`sz0_admissible`) | S0 (τD=0.05): 1.0e-7 ≤ 9.7e-7; 0.238 ≤ 0.483; 1.39e-4 ≤ 2.44e-4 (×1.76) |
| 9 | `κ'`, `cT` (`ba_flowG` `RandomLayerBGBA:103`) | `κ'=(πκ)^5/2048`, `cT=κ'/(κ'+1)`, `Ed κ'` ⇒ `BAReal` at `(√t₀λ, BAfE, m₀)` (`BASelf_unique`), `Im m₀ ≥ κ'` | S0: κ'=0.5 ≤ Im m₀ = 0.9676; fT = 0.99999793 ≥ cT = 1/3 |
| 10 | regime `L^dη_u ≲ 1` (GUE phase, `h730`) | expected (heuristic: a block average over rank `W^d` fluctuates like `(W^dN)^{-1/2}`, which exceeds `Λ` once `L^dη ≫ 1`) to fail outside it, so PB `lk 1` is a hypothesis only inside it; the K-bound hypothesis carries it | MC `√E|T|²/Λ`: 0.71 / 0.69 at `L^dη=0.28` (N=512/1728), 2.82 at `L^dη=6.9` (run X; `max|g−m|/Λ` 11.88) |
| 11 | T15 `b₂ ≤ 1`, `NΔ ≤ 1`, `u,u+Δ ∈ [t₁,t₀]` | `‖K̃₂‖ ≤ b₂ = 1`, `Δ ≤ 1/N` | S0 proxy `W^{-d}max|Θ_tM^{(σσ')}|` = 0.255 (×3.9); NΔ = 0.21 (×4.8) |
| 12 | `0 < g ≤ Λ` only eventually (`BAflow_lam0_window` `GreenSchur:72`, `Sizes.lam` unsigned) | `g=√t₀λ_n`; `BAKFam`, `T2519_HoffBA` guard `∀ᶠ n`; C4's `∀ n` text via an eventually-equal family `z'` (`BAFlow` ∀ n: bulk point `E=0` for `n<n₀`, `ba_dom_of_bulk`); `StochDomAt` is eventual | padding ≈ 40, as booked |
| 13 | price of T7 (`GUETwistBA`) | ticket 800 [500, 1,400]; `n0=4` expected to change no line count (band files `n0`-generic) | upper end puts row b pure at 2,236 > 1,950 |
### (ii) One concrete nondegenerate instance
`d=3`, `L=4`, `W=32`, `λ=1/64` (`sz0`, `n=0`, `N=2^21`), `z=0.5+2e-6 i`, `κ'=1/2`, `τD=1/20`, `t₁=t₀−1e-7`. At `n=0` every deterministic hypothesis of T7, T15, T16 holds (`BAReal`, `0≤t₁≤t₀<1`, `0<g≤Λ=1/64`, T16 scale premises, `b₂`, `NΔ`; `Kt` on 1-loops is `mSigOf` by definition); along `sz0` only the scale premises were evaluated (`τD`-condition true for n = 0, 10, …, 10⁵ in `s0.py`; `L^d(1−t₁) ≤ λ²` by the choice of `η_n`). Externals: PB (T7, `Kt` of `BAKFam`) is a hypothesis; limit (lesson 14): along `sz0` with `η_n = 0.97λ_n²/(2L_n^d)`, `Nη_n = 3.88(n+1)³ → ∞`, `Λ_n → 0` (rows n=100, 1000 below), and the pathwise constants `max|g−m|/Λ = max|T|/Λ` do not grow with N (4.74 at N=512, 2.66 at N=1728). MC datum `g=0.85, E=0.5, t₁=0.99, u=0.992` (`L^d(1−t₁)=0.64 ≤ g²`, `Im m=0.5397 ≥ 0.5`), `W=2,3`.
```
$ cd $SCR/T2519 && python3 s0.py | grep -E "^S0|^flow|fT-t1|N sqrt|L\^d\(1-t1\)|^K-bound|^CM|eps=0.02 n=(0|100|1000):|eps=0.1: nontrivial"
S0: d=3 L=4 W=32 N=2097152=2^21 L^d=64 lam=0.015625; z=0.5+2e-06i: m=-0.249635+0.967584j Im m=0.967584
flow: t0=BAt0=0.9999979330 1-t0=2.067e-06; g0=sqrt(t0)lam=0.01562498; E'=BAflowE=0.500000; m0=m/sqrt(t0)=-0.249635+0.967585j Im m0=0.967585; BASelf residual at (g0,E',m0)=1.6e-16 (real-axis datum, BAReal needs Im m0>=kappa')
  0<=t1=0.9999978330<=fT<1 : True; fT-t1=1.00e-07 <= N^-tauD*sqrt(fT)*Im z=9.66e-07: True
  (N sqrt(fT) Im z)^-1 = 0.2384 <= N^-tauD=0.4830: True   [N eta = 4.19]
  L^d(1-t1) = 1.387e-04 <= lam^2 = 2.441e-04: True (slack x1.76);  <= 1: True
K-bound scale (STKboundgL): W^-d B_(t1,0) = 3.4395e-01; 2/(N(1-t1)) = 4.4009e-01; Lam_u=(N eta_u)^-1 at t1: eta_u=(1-t1) Im m0=2.097e-06, Lam_u=2.2742e-01; W^-d B <= 2 (N(1-t1))^-1 : True
CM (baM_row_l1, GreenStab:116; c0=BAct_rate=min(log(1+kappa/(4 d Lam)),kappa/2), CombesThomas:45; expC RadialSum:271) = 6.2925e+06 (c0=0.25000); actual max row l1 of M^B at (g0,E',m0) = 1.1006; rho2<=1: max_ac sum_b|M_ab||M_bc| = 1.0000
  eps=0.1: nontrivial regime N eta_u>N^(2eps): alpha<=CM N^(-7eps/4)<=1/2 iff N>=3.720e+40 (log2 N>=134.8); at n=0 N=2^21: trivial regime N eta=4.19 <= N^(2eps)=18.38: True
  eps=0.02 n=0: N eta=3.880e+00 Lam=2.58e-01 alpha=1.74e+06 >1/2; trivial regime False; tauD-condition (N eta)^-1<=N^-tauD(0.05): True
  eps=0.02 n=100: N eta=3.998e+06 Lam=2.50e-07 alpha=2.56e+00 >1/2; trivial regime False; tauD-condition (N eta)^-1<=N^-tauD(0.05): True
  eps=0.02 n=1000: N eta=3.892e+09 Lam=2.57e-10 alpha=3.24e-03 <=1/2 ok; trivial regime False; tauD-condition (N eta)^-1<=N^-tauD(0.05): True
$ python3 kdisc.py | tail -1
b2=1 >= max|K2|=0.2553; N*Delta=0.210 <= 1: True; window [t1,t0]=[0.999997833,0.999997933] length 1.0e-07; u=t1, u+Delta=t0 in window; 0<=t1
$ python3 mc_hoff.py {A,B,X} > mc_{A,B,X}.out   # S=4000/150/600; then grep -E "^\[MC\]|first moment|pathwise|\(q,a\)=\(0,0\)" mc_A.out mc_B.out mc_X.out
A [MC] d=3 L=4 W=2 N=512 g=0.85 E=0.5 t1=0.99 sigma L^d=0.002 u=0.9920: Im m=0.5397 eta_u=4.3173e-03 N eta=2.21 Lam=(N eta)^-1=4.5239e-01 L^d eta=0.276 S=4000
A     first moment: max|E T - E[M d (T+M)]|=1.71e-02 (se<= 8.8e-03); max|E T|=1.01e-02 = 0.049 Lam^2; row-l1 max_q sum|M_qp|=6.033
A     pathwise: max_p|g_p-m|/Lam=4.74; max_(q,a)|twTr|/Lam=4.74
A     pair (q,a)=(0,0): E|T|^2=1.034e-01; self-term+R2 = 1.003e-01 (+6e-03i); |diff|=6.6e-03 (z=1.6); sqrt(E|T|^2)/Lam=0.711; |E R2|/Lam^2=0.804; E|R2|/Lam^2=0.896; CS(HS) bound/Lam^2=3.387; abs-sum bound/Lam^2=3.371; abs-sum/Lam^(3/2)=2.268; |self|/Lam^2=0.383; negative control (R2 dropped): |E|T|^2-self|=1.65e-01
B [MC] d=3 L=4 W=3 N=1728 g=0.85 E=0.5 t1=0.99 sigma L^d=0.002 u=0.9920: Im m=0.5397 eta_u=4.3173e-03 N eta=7.46 Lam=(N eta)^-1=1.3404e-01 L^d eta=0.276 S=150
B     first moment: max|E T - E[M d (T+M)]|=2.68e-02 (se<= 1.2e-02); max|E T|=1.83e-02 = 1.017 Lam^2; row-l1 max_q sum|M_qp|=6.033
B     pathwise: max_p|g_p-m|/Lam=2.66; max_(q,a)|twTr|/Lam=2.66
B     pair (q,a)=(0,0): E|T|^2=8.666e-03; self-term+R2 = 8.860e-03 (+3e-04i); |diff|=3.6e-04 (z=0.3); sqrt(E|T|^2)/Lam=0.694; |E R2|/Lam^2=0.703; E|R2|/Lam^2=0.714; CS(HS) bound/Lam^2=3.378; abs-sum bound/Lam^2=5.115; abs-sum/Lam^(3/2)=1.873; |self|/Lam^2=0.292; negative control (R2 dropped): |E|T|^2-self|=1.23e-02
X [MC] d=3 L=4 W=2 N=512 g=0.85 E=0.5 t1=0.5 sigma L^d=0.3 u=0.8000: Im m=0.5397 eta_u=1.0793e-01 N eta=55.26 Lam=(N eta)^-1=1.8096e-02 L^d eta=6.908 S=600
X     first moment: max|E T - E[M d (T+M)]|=6.01e-03 (se<= 2.6e-03); max|E T|=5.29e-03 = 16.169 Lam^2; row-l1 max_q sum|M_qp|=6.033
X     pathwise: max_p|g_p-m|/Lam=11.88; max_(q,a)|twTr|/Lam=11.88
X     pair (q,a)=(0,0): E|T|^2=2.610e-03; self-term+R2 = 2.678e-03 (+7e-06i); |diff|=6.9e-05 (z=0.5); sqrt(E|T|^2)/Lam=2.823; |E R2|/Lam^2=9.552; E|R2|/Lam^2=9.585; CS(HS) bound/Lam^2=14.367; abs-sum bound/Lam^2=20.166; abs-sum/Lam^(3/2)=2.713; |self|/Lam^2=2.017; negative control (R2 dropped): |E|T|^2-self|=3.06e-03
```
### Census per file (T2515/T2517 formula `1.24(0.85B+0.6P+0.05M)`, non-blank lines; ticket ranges `Proc 1-911`, …)
```
$ python3 census6.py   # scripts: SCR/T2519/census.py (T2517 copy), census6.py
repro OneLoop 868 1030 (ticket 866/1031, 404/603, 72/491)
repro Eq729A 408 615 (ticket 866/1031, 404/603, 72/491)
repro Drift 72 519 (ticket 866/1031, 404/603, 72/491)
Proc       1-911   pure B/P/M (53, 143, 572) ->  198 | wide (297, 85, 386) ->  400 | mean    299 | ticket (200, 403)
HypA       1-1118  pure B/P/M (195, 50, 749) ->  289 | wide (398, 18, 578) ->  469 | mean    379 | ticket (309, 479)
ProcK      1-734   pure B/P/M (327, 54, 271) ->  402 | wide (381, 0, 271) ->  418 | mean    410 | ticket (412, 428)
EntryGrid  1-609   pure B/P/M (239, 32, 236) ->  290 | wide (303, 59, 145) ->  372 | mean    331 | ticket (280, 361)
DuhamelA2  1-1090  pure B/P/M (0, 0, 940) ->   58 | wide (132, 10, 798) ->  196 | mean    127 | ticket (60, 193)
DuhamelB   1-1034  pure B/P/M (0, 115, 764) ->  133 | wide (422, 125, 332) ->  558 | mean    346 | ticket (120, 555)
DuhamelC   1-1510  pure B/P/M (379, 155, 815) ->  565 | wide (874, 0, 475) ->  951 | mean    758 | ticket (457, 948)
HypB       1-1083  pure B/P/M (208, 445, 302) ->  569 | wide (763, 10, 182) ->  823 | mean    696 | ticket (558, 815)
BoundsA    1-766   pure B/P/M (230, 145, 276) ->  367 | wide (388, 46, 217) ->  457 | mean    412 | ticket (377, 469)
PathBounds 1-668   pure B/P/M (397, 44, 127) ->  459 | wide (527, 15, 26) ->  568 | mean    514 | ticket (465, 566)
LLTransfer 1-469   pure B/P/M (213, 28, 130) ->  253 | wide (213, 36, 122) ->  259 | mean    256 | ticket (238, 238)
Eq729B     1-1323  pure B/P/M (666, 69, 449) ->  781 | wide (718, 81, 385) ->  841 | mean    811 | ticket (785, 846)
$ python3 central.py   # central = census − reuse + BA-only new + inst/hdr, the ticket columns
file            row   pure  wide  mean   ticket pure/wide
GUEProcBA       a      408   610   509   410/613
GUEHypABA       a      931  1127  1029   961/1147
GUEEntryGridBA  a      365   447   406   355/436
GUEDuhamelBA    b      776  1675  1226   657/1666
GUETwistBA      b      860   860   860   860/860
GUEHypBBA       c     1111  1455  1283   1110/1459
GUEPathBoundsBA c      534   643   588   540/641
GUELLBA         d      313   319   316   298/298
GUEHyp          d     1116  1176  1146   1120/1181
row a: pure 1704 wide 2184 mean 1944  vs cap 1950: pure ok (slack 246), wide OVER (-234), mean ok (6)
row b: pure 1636 wide 2535 mean 2086  vs cap 1950: pure ok (slack 314), wide OVER (-585), mean OVER (-136)
row c: pure 1645 wide 2098 mean 1872  vs cap 1950: pure ok (slack 305), wide OVER (-148), mean ok (78)
row d: pure 1429 wide 1495 mean 1462  vs cap 1950: pure ok (slack 521), wide ok (455), mean ok (488)
total: pure 6414 wide 8312 mean 7363; C5S-C1 line 9025: wide slack 713; with hoff at 1400 (+600): wide 8912 slack 113; row b pure with hoff 1400: 2236 (cap 1950)
  x1.1: pure 7055 wide 9143;  x1.34: pure 8595 wide 11138;  x1.43: pure 9172 wide 11886;  x1.67: pure 10711 wide 13881;
Duhamel layer: L1 central pure 776 wide 1675; in place at 1.2 model 796+150=946, at x2.54: 1685+150=1835; saving of in-place (L1 - in place): 1.2: pure -170 wide 729; x2.54: pure -1059 wide -160 (C5S-C3 needs >= 500 at x2.54)
```
Reading: my census reproduces T2517's landed figures (868/1030, 408/615, 72/519 vs 866/1031, 404/603, 72/491) but not the device script's per-file figures exactly (DuhamelC pure 565 vs 457, HypA 289 vs 309); totals agree (wide 8,312 vs 8,301). Stop line 1,500 per file: only `GUEDuhamelBA` wide (1,675) exceeds it (reserve file `GUEDuhamelBA2` as laid out); none near 2,000.
**Split (Decision (3): the pure census decides):** pure rows a 1,704, b 1,636, c 1,645, d 1,429 are all ≤ 1,950 ⇒ **a | b | c | d stands, no reserve booked** (a′, b′, c′ stay unbooked); wide/mean rows a 2,184/1,944, b 2,535/2,086, c 2,098/1,872 are the cases the reserves cover (b′ would be booked first: b mean 2,086, and b pure 2,236 if T7 costs 1,400). **C5S-C1:** total wide central 8,312 ≤ 9,025 (slack 713; 113 with T7 at 1,400); note 9,025 = 1.43 × the ticket's pure 6,311, and my pure total 6,414 × 1.43 = 9,172 would pass the line by 147 under that reading (for the 1a-audit).
**D1 (iv) layout:** Duhamel layer in place at the ×2.54 price 1,685+150 = 1,835 vs L1 pure 776 / wide 1,675: saving −1,059 / −160 < 500 ⇒ C5S-C3 not met ⇒ **L1** (no REQ; ×1.2 model alone gives pure −170, wide +729).
**D1 (v) `M`-local law:** `grep -c` on the twelve files (`mE•1` local-law form / `zt` / `gueH`): Proc 8/76/42, HypA 2/26/19, HypB 12/51/52, BoundsA 15/19/18, PathBounds 3/6/6, EntryGrid 5/20/27, the other six files have no `mE•1` form (they carry `zt`/`gueH`/`etaT` tokens, counted in the census). `norm_egtNGUE_le` (`Proc:596`) uses no local law: its hypotheses are `avgErr` and loop bounds, and `avgErr` is the trace `(G−m)E_a`, i.e. the diagonal `M_xx=m` (`BAMB_diag_eq` `Ward:89`; `zt ↦ ztOf`): it needs only the diagonal. The entrywise `‖G−m‖_max` (`gueDev`, `HypB_entry_le`, `localLaw`) becomes `‖G−Mres(gΨ_I,E,m)‖_max`, a fixed deterministic matrix (one-step jump unchanged).
## Verdicts
- **T7 / D1 (i) `T2519_HoffBA`: FAIL as pinned.** R1 from PB `lk ≤ 3` and `localLaw` at the same grid time does not reach `Λ_u` (row 4: exponent 3/2 vs 2, conclusion `Λ_u^{3/4}`); the self-term is fine (row 2, C5S-C2 not hit). Needs `lk 4` and the K-bound on 2-, 4-loops (row 5): a change of `T2519_PBBA`/`T2519_HoffBA` (`n0 = 4`, extra hypothesis `‖Kt_k‖ ≤ C(2Λ_u)^{k-1}`), not of any `RBG_*`. Stop rule D1 (i) is hit as written (R1 from the two PB fields does not close): short REQ / dispatcher decides the repaired text. Not probed: the repaired text is untested by Lean here; evidence is the exact identity (row 1) and the scalings (row 4).
- T1 vocabulary D1 (ii): PASS (`T2519-pins.lean` compiled, CONTROL H322 (2) `done` line: exit 0, no error lines; exact-type `example` included), subject to `n0 = 4`.
- D1 (iii): PASS (`hKb` from `Ed κ'` + eventual scale rows + `BAFlow` on `z'`; padding ≈ 40; no primed `RBG_Prod`). T15 PASS (row 11). T16 producers: hypotheses hold at S0 (row 8), conclusions rest on T7. D1 (iv) L1; D1 (v) decided; split/price: above.
- Paper-delta candidates: `T2519a` (the twisted 1-loop law at the grid time needs loops of length 4: `n0 = 4`), `T2519b` (grid local law against `M^{(B)}⊗1`).

## (a′) Preflight corrections — Fri Oct 16 12:08:29 UTC 2026
Amend 1 item 7: D1 (i) redone (rows 4–5 with `lk 4`, the C5H-C1 K-bound, both derivative terms `𝒮₁`, `𝒮₂`; census of `GUETwistBA` by T.7's steps). Rows 2, 3, 6, 8, 9, 11, 12, D1 (ii)–(v), and the census of the other nine files stand. Rows 4, 5, 7, 13 and the Verdicts for T7 of (a) are replaced by the rows below. `SCR/T2519/` = scratch scripts (kb.py, mc_p2.py, mc_loops.py, tl1seg.py, price7.py).
**Exact p-moment identity** (re-derived from `G−M = −M(X+um)G`, `E[X_xy F]=S_xy E∂_{h_yx}F`, `∂_{yx}T = −W^{-d}Σ_j G_{(q,j),y}G_{x,(a,j)}`, `∂_{yx}T̄ = conj ∂_{xy}T`), `Φ = T^{p−1}T̄^p`, `T=T(q,a)`:
`E|T|^{2p} = Σ_r M_qr E[d_r(M_ra+T(r,a))Φ] + (p−1) E[R₁ T^{p−2}T̄^p] + p E[R₂|T|^{2p−2}]`, `R₁ = Σ_r M_qr W^{-2d}Σ_{ij}Σ_y S_{(r,i)y} G_{y,(a,i)}G_{(q,j),y}G_{(r,i),(a,j)}` (= `𝒮₁`, charges (+,+,−,−), present iff `p ≥ 2`), `R₂` as in (a) row 1 (= `𝒮₂`, charges (+,−,+,−)).
### (i′) Exponent table (replacement rows)
| # | quantity | value / constraint | slack |
|---|---|---|---|
| 4′ | HS pairing of **both** derivative terms (`T2398-TL-proofs.md:80-83`, mirror form of `twAvgSCS`, `TwistAvgA2:45-52`): `|R₁| ≤ Σ_r|M_qr| (Σ_s Ŝ_rs L⁴_{(++−−),(q,s,a,s)}{}^{1/2}) L²_{(+−),(r,a)}{}^{1/2}`, `|R₂| ≤ Σ_p|M_qp| (Σ_r Ŝ_pr L⁴_{(+−+−),(a,r,a,r)}{}^{1/2}) L²_{(+−),(q,p)}{}^{1/2}`; `Σ_r Ŝ_pr = u ≤ 1` and the triangle inequality over `r`/`s` carry the J-part of `Ŝ = t₁1+σJ` (no new input) | needed `|R_i| ≲ Λ_u²`. PB `lk k`: `|L^{(k)}−Kt_k| ≺ Λ^k`; K-bound (C5H-C1): `|Kt_k| ≤ N^ε Λ^{k−1}`; so `|L⁴| ≺ Λ³`, `|L²| ≺ Λ`, `|R_i| ≺ C_M(Λ³Λ)^{1/2} = C_MΛ²`; `X² ≤ αX+β`, `α~Λ`, `β~Λ²` ⇒ `T ≺ Λ`. `lk 4` is uniform in `Fin 4 → Bool`, `Fin 4 → Zd` (pins `T2519_PathBoundsBA`), so both charge patterns and repeated indices are covered; `LoopIdx.WF` is only `σ.length = a.length` (`Loop/TreeRep:68`), so the K-bound covers them | exponents (script `kb.py`, below): 3 + 1 → 2, needed 2: **slack 0** (tight; the `N^ε` losses are inside `≺`); `lk` terms carry `Λ^k`, slack +1 over `Λ^{k−1}`. (a) row 4 had 3/2 → `T ≺ Λ^{3/4}` (slack −1/2, −1/4) |
| 5′ | `n0` and lengths with `lk 4` (replaces row 5): `T2519_PBBA` `n0 = 4`, `gueGridK sz 4`; `T2519_KFamBA` `I.length ≤ 4*4` | `gueGridK` exponent `32 n0+64` (`Grid:106`) = 192 (160 at `n0=3`); `Hyp_Kt_detDom` conclusion range `2 ≤ |I| ≤ 2 n0` (`HypA:690-711`) = [2,8] ⊇ {2,4}; its `hK` needs lengths `≤ 4 n0` = 16 = `KFamBA` bound; `gueGrid_eq729` needs `3 ≤ n0` (supervisor 1134 Q1 (a), `Eq729B:622`) | `lk 4`: need `n0 ≥ 4`, have 4: slack 0 (was −1); range 8 vs 4: +4; `hK` 16 vs 16: 0; eq729: +1 |
| 6′ | K-bound premise of `T2519_HoffBA` (Amend 1 item 1 (c)): `∀ ε>0, ∀ᶠ n, ∀ s ∈ [t₁,t₀]`, WF `I`, `2 ≤ |I| ≤ 4`: `‖Kt n s I‖ ≤ N^ε (N etaOf (m n) s)^{-(|I|−1)}` = conclusion of `Hyp_Kt_detDom` (`HypA:690`) at `n0=4`, applied at the grid time `s = gridTime t1 t0 K n k ∈ [t₁,t₀]` | from (a) row 6: `W^{-d}B ≤ 2Λ_u Im m`, constant `2^{k−1} = 8` at `k=4` absorbed by `N^ε`: eventual, `N^ε ≥ 8` | `kb.py`: along `sz0` (`N_n = 2^21(n+1)^18`) `N^ε ≥ 8` from `n=1` (ε=0.1), `n=143` (ε=0.02); with `α ≤ 1/2` both hold from `n=412` / `n=177` |
| 7′ | twist moment `p`, Markov, union (replaces row 7). `StochDomAt` has the union over the index inside `P` (`Defs/StochDomAt:61`): the conclusion needs a union over `K+1 = (N+1)^{192}` grid points × `L^{2d} ≤ N²` pairs, which (a) row 7 omitted | `TwistAvgB_expo` (`:289`): `D'+4 ≤ pτ`, `D' = D+192+1+2` (pairs counted conservatively) | `(τ,D) = (0.1,5)`: `p ≥ 2040` (was 51); `p` is a fixed natural number in Lean, `C_p = (4p+2)C_M+2` (`TwistAvgB_S1`) a fixed constant: no slack lost |
| 10′ | no scale premise needed in `T2519_HoffBA`: every bad-event envelope is relative, `‖G‖ ≤ η_u^{-1} = N Λ_u`, so `E[|T|^{2p}1_bad] ≤ N^{-D'}(NΛ_u)^{2p}` and `D'` is free; `Λ_u ≥ N^{-2ε}` is the trivial regime of (a) row 2 (`T ≺ ‖G−M‖_max ≺ Λ^{1/2} ≤ N^εΛ`) | `StochDomAt` weight `‖M_aq‖Λ_u` unchanged (`t_aq−Q_aq = M_aq T(q,a)`, T2517 (a) row 8) | stable regime `C_MρΛ_u ≤ 1/2` (the self-coefficient of (a) row 2; the consumer band `gueGrid_eq729` also carries `hscale`, `Eq729B:622+`, which `T2519_HoffBA` does not, hence the trivial-regime split): along `sz0`, `α ≤ 1/2` from `n=412` (ε=0.1), `n=177` (ε=0.02) |
```
$ cd $SCR/T2519 && python3 -I kb.py
row4': L4 exp 3 L2 exp 1 -> |S1|,|S2| exp 2 (needed 2); beta exp 2 -> T exp 1 (needed 1)
   entrywise-only (a) row 4: |S_i| exp 3/2 -> T exp 3/4
n0=3: lk fields k<=n0: [1, 2, 3]; gueGridK exponent 160; Hyp_Kt_detDom |I| range [2,6] needs {2,4}: ok (slack 2); hK / KFam length bound 4*n0=12; lk 4 present: False; eq729 (3<=n0): ok
n0=4: lk fields k<=n0: [1, 2, 3, 4]; gueGridK exponent 192; Hyp_Kt_detDom |I| range [2,8] needs {2,4}: ok (slack 4); hK / KFam length bound 4*n0=16; lk 4 present: True; eq729 (3<=n0): ok
row7': union exponent 195 (grid 192+1, pairs 2); p >= (D+195+4)/tau = 2040 at (tau,D)=(0.1,5); band-free value D/eps+1 = 51
eps=0.1: first n with N^eps>=8 (K-bound constant 2^3): n=1; first n with alpha<=1/2 (stable regime): n=412; both: n>=412  [N_n=2^21 (n+1)^18]
    n=412: log2 N=177, N eta=2.733e+08, alpha=4.98e-01, N^eps=2.19e+05>=8: True
    n=4120: log2 N=237, N eta=2.715e+11, alpha=1.41e-03, N^eps=1.38e+07>=8: True
eps=0.02: first n with N^eps>=8 (K-bound constant 2^3): n=143; first n with alpha<=1/2 (stable regime): n=177; both: n>=177  [N_n=2^21 (n+1)^18]
    n=177: log2 N=156, N eta=2.188e+07, alpha=4.93e-01, N^eps=8.64e+00>=8: True
    n=1770: log2 N=215, N eta=2.155e+10, alpha=6.16e-04, N^eps=1.98e+01>=8: True
```
### (ii′) Instance at `n0 = 4` and limit computations (lesson 14)
The instance of (a) (S0: `d=3, L=4, W=32, λ=1/64, N=2^21`, `κ'=1/2`) is unchanged in every deterministic hypothesis; the amended texts add only external hypotheses: PB at `n0=4` (`lk 1..4`, `localLaw`) and the K-bound of row 6′ (both along `n`, eventual). `K n = (N+1)^{192}` is only the index size (proof device, never witnessed). Limit computations (`N=512` → `1728`, regime A of (a): `g=0.85, E=0.5, t₁=0.99, σL^d=0.002`, `N η_u = 2.21 → 7.46`): the 4- and 2-loops that enter `R_i` scale as PB + K-bound say (flat or decreasing constants), the HS bounds of both derivative terms are flat, the identity holds at `p = 1, 2, 3`:
```
$ python3 -I mc_loops.py        # E max_r L4_r/Λ³ (loop (+-+-)), E max L2/Λ
[loops] N=512 Lam=4.524e-01 Nη=2.21 S=300: E max_r L4_r/Lam^3 = 2.549 (max over samples 29.844); E max_(q,a) L2/Lam = 2.349 (max 7.181)
[loops] N=1728 Lam=1.340e-01 Nη=7.46 S=30: E max_r L4_r/Lam^3 = 1.110 (max over samples 1.982); E max_(q,a) L2/Lam = 1.036 (max 1.227)
$ python3 -I mc_p2.py {A,B2,A3} | grep "(q,a)=(0,0)"   # p=2 N=512 (S=3000); p=2 N=1728 (S=600); p=3 N=512 (S=3000)
[MC p=2] d=3 L=4 W=2 N=512 g=0.85 E=0.5 t1=0.99 sigma L^d=0.002 u=0.9920: Im m=0.5397 eta_u=4.317e-03 N eta=2.21 Lam=4.5
 (q,a)=(0,0): E|T|^4=2.657e-02; self=-1.784e-02, S1-term=-2.486e-02, S2-term=6.917e-02; |E|T|^4-sum|=1.7e-03 (z=0.48); control drop S1-term: 2.8e-02, drop S2-term: 7.5e-02; (E|T|^4)^(1/4)/Lam=0.892; E|R1|/Lam^2=0.692; E|R2|/Lam^2=0.894; CS(HS) S1 bound/Lam^2=3.100, S2 bound/Lam^2=3.388
[MC p=2] d=3 L=4 W=3 N=1728 g=0.85 E=0.5 t1=0.99 sigma L^d=0.002 u=0.9920: Im m=0.5397 eta_u=4.317e-03 N eta=7.46 Lam=1.
 (q,a)=(0,0): E|T|^4=1.622e-04; self=-5.445e-05, S1-term=-1.807e-05, S2-term=2.277e-04; |E|T|^4-sum|=7.4e-06 (z=0.49); control drop S1-term: 1.5e-05, drop S2-term: 2.5e-04; (E|T|^4)^(1/4)/Lam=0.842; E|R1|/Lam^2=0.254; E|R2|/Lam^2=0.708; CS(HS) S1 bound/Lam^2=2.976, S2 bound/Lam^2=3.349
[MC p=3] d=3 L=4 W=2 N=512 g=0.85 E=0.5 t1=0.99 sigma L^d=0.002 u=0.9920: Im m=0.5397 eta_u=4.317e-03 N eta=2.21 Lam=4.5
 (q,a)=(0,0): E|T|^6=1.526e-02; self=-1.327e-02, S1-term=-3.142e-02, S2-term=6.588e-02; |E|T|^6-sum|=1.2e-02 (z=1.59); control drop S1-term: 4.0e-02, drop S2-term: 7.0e-02; (E|T|^6)^(1/6)/Lam=1.101; E|R1|/Lam^2=0.673; E|R2|/Lam^2=0.870; CS(HS) S1 bound/Lam^2=3.044, S2 bound/Lam^2=3.328
```
Reading: the identity (self + `𝒮₁` + `𝒮₂` terms) matches `E|T|^{2p}` within noise (z = 0.48, 0.49, 1.59); dropping the `𝒮₁` term moves it by 2.8e-2 vs |diff| 1.7e-3 at `N=512` (`p=2`), dropping `𝒮₂` by 7.5e-2; at `N=1728` the `𝒮₁` term is only 11% of `E|T|⁴` (1.8e-5 of 1.62e-4; control 1.5e-5 vs |diff| 7.4e-6: weakly discriminating). CS(HS) bounds of both terms / `Λ²`: 3.10 / 3.39 (`N=512`) → 2.98 / 3.35 (`N=1728`): flat, i.e. `Λ²`. `L⁴/Λ³`, `L²/Λ` (means over samples of the max over blocks): 2.55 / 2.35 → 1.11 / 1.04 (sample maxima 29.8 / 7.2 at `N=512`, 1.98 / 1.23 at `N=1728`; heavy tail, decreasing constants; the PB and K-bound scalings hold in the datum).
### (iii′) Census of `GUETwistBA` by T.7's steps (calibrated against the landed TL1 files, non-blank lines)
Landed: `BA/TwistAvgA` 1,085, `A2` 1,228, `B` 504 = 2,817 `wc -l`, 2,511 non-blank (design central was 1,936: `T2413-design.md` row table TL1a 1,036 + TL1b 900; landed/design ×1.46). Step ranges by section headers (`tl1seg.py`); carry-over fractions to the grid are mine (lo / central / hi) with the reasons: the BA-law transport, `BAFlow` ceilings (`Bctl`) and carrier regularity (TL1: lanlw transport 70, BC 41, Reg 186, Bctl 105 lines) are replaced by the Gaussian product law (C4 a's Stein layer `GUEOneLoop_stein_coord`, `_stein_int`, `ExpAvgGen_G_*` read by `open private`; C4 a landed 360 non-blank lines for the `p=1` Stein layer plus 232 for the core, 423 for the bound at one time, `BA/GUEOneLoop` §3–§5); what remains is copied: `Φ_p` and its coordinate derivative, the twist algebra, HS loops, the bootstrap, Markov. `T.6` is not copied: the bad event is split inline as in `GUEOneLoop_expect_core` (`μ.real T ≤ δ`).
```
$ python3 -I price7.py
T.7 step / item                                                                                TL1    lo   cen    hi
1 Stein/IBP identity, Phi_p, continuity/envelopes                                              630   346   441   567
2 non-derivative term, twist algebra (max over pairs)                                          157    94   126   157
3 HS bounds on S2 and S1 (loops, CS, SPrec)                                                    419   230   314   398
4 moment bootstrap (T6, Holder, core, recursion, S1-quadratic, Bctl, Xmax)                     793   357   436   555
5 Markov + union + output                                                                      169   118   152   186
vocabulary: twTr, S1, S2, Phi_p at the grid (TL1 §1: 100)                                        -    40    60    80
header + docs (TL1: 119)                                                                         -    40    50    60
PB interface: lk k, localLaw, K-bound -> pathwise events; t_aq-Q_aq = M_aq twTr (T2517 row 8)     -   120   170   240
relative envelope 1/eta_u = N Lam_u; trivial regime Lam >= N^-2eps                               -    40    60    90
grid index Fin(K+1), eventual 0<g, BAReal forall n plumbing                                      -    40    60    90
compiled nonempty instance d=3 (hypothesis PB kept)                                              -    60    75   100
sum, non-blank lines (landed basis)                                                           2168  1485  1944  2523
TL1 files wc -l = 2817, non-blank = 2511; wc/non-blank = 1.122
landed basis, wc lines: lo 1666 central 2181 hi 2830; central/TL1 wc = 0.77
central-equivalent, /1.34 (ticket's recent-landing ratio, T2519.md Price): lo 1243 central 1628 hi 2112
   rows: b (Duhamel alone, b' booked) pure 776 wide 1675; b' (GUETwistBA) lo/central/hi 1243/1628/2112 vs cap 1950: slack 322 (central), -162 (hi)
   row b unsplit pure 2404 (cap 1950: OVER), with lo 2019
   C5S-C1: total wide central = 8312-860+1628 = 9080 vs 9025: FIRES (margin -55); lo 8695, hi 9564; trigger T = 1573
central-equivalent, /1.46 (TL1's own landed/design: 2,817/1,936): lo 1145 central 1499 hi 1945
   rows: b (Duhamel alone, b' booked) pure 776 wide 1675; b' (GUETwistBA) lo/central/hi 1145/1499/1945 vs cap 1950: slack 451 (central), 5 (hi)
   row b unsplit pure 2275 (cap 1950: OVER), with lo 1921
   C5S-C1: total wide central = 8312-860+1499 = 8951 vs 9025: does not fire (margin +74); lo 8597, hi 9397; trigger T = 1573
```
**Reading.** `GUETwistBA` central 1,628 (lo 1,243, hi 2,112) at the ticket's landed/central ratio 1.34 (T2519.md Price), 1,499 (1,145 / 1,945) at TL1's own ratio 1.46; ticket 860 [500, 1,400]. **Row b unsplit** (Duhamel 776 pure + `GUETwistBA`) is 2,404 (2,275; even lo gives 2,019 / 1,921) > 1,950 ⇒ **reserve b′ is booked** (pre-signed, Amend 1 item 5; no REQ): b = `GUEDuhamelBA` (pure 776, wide 1,675), b′ = `GUETwistBA` (central 1,628, slack 322 below 1,950; hi 2,112 is 162 above, lo 1,243). **C5S-C1** (fixed 9,025 against total wide central; 8,312 − 860 + `GUETwistBA`): 9,080 at ratio 1.34 → **fires by 55** (trigger `GUETwistBA` > 1,573); 8,951 at ratio 1.46 → does not fire (margin 74); lo 8,695, hi 9,564. The call is within ±1% of the line and rests on the calibration ratio: for the dispatcher / 1a-audit. `GUETwistBA` above 1,950 with b′ taken (fourth reserve REQ) is not reached at the central (1,628 / 1,499). M/N count with b′: rows a–d = 13–16, b′ = 17, N2 after = 18 (flag 20, REQ line forecast > 20: not reached). BA count: b′ is one of the ticket's three reserve slots (BA 203–205).
**`BA/TwistAvg*` lemmas read by name (1044 Q4; statements read, none edited)**, line numbers at `main` 25e22c0b (`t/T2519` = same): `TwistAvgA_pow_eq:892`, `_pow_eq':900`, `_sh:227`, `_Tpol:231`, `_Tbpol:236`, `_Phi:241`; `TwistAvgA2_E:79`, `_trace_submatrix:92`, `_loop_eq:98`, `_HS:113`, `_E_conjTranspose:148`, `_cs:320`, `_sum_ite:357`, `_sum3:364`, `_sqrt_arith:400`, `_holder:641`, `_root_pow:648`, `_root_pow_self:654`, `_holder_nat:662`, `_lyap1:696`, `_lyap2:702`, `_sqrt_int_le:742`, `_err:1013`; private, by `open private … from RBM3D.BA.TwistAvgB` (C4 a precedent): `TwistAvgB_S1:53` (the real-number bootstrap `X^{2p} ≤ K(wB)(X^{2p−1}+X·X^{2p−1}) + 2pK(wB²)X^{2p−2}+e ⇒ X ≤ ((4p+2)K+2)wB`, needs `K·w·B ≤ 1/2` = the α condition of (a) row 2), `_markov:273`, `_expo:289`, `_union:313`. Statements-only reading for calibration (not used by name, BA-law typed): `twAvgSCS`, `twAvgSPrec`, `twAvgT6` (`TwistAvgA2:45-70`), `TwistAvgA_dH_Phi:291`, `TwistAvgA2_core:902`, `baTwistAvgRec_holds:1040`.
```
$ import closure of the by-name modules (python over `^import RBM3D.` lines, read-only)
RBM3D.BA.TwistAvgA2 295 closure; MainInd/TwistPins/Step6/TwistStep modules: ['RBM3D.BA.TwistPins']
RBM3D.BA.TwistAvgB 296 closure; MainInd/TwistPins/Step6/TwistStep modules: ['RBM3D.BA.TwistPins']
direct imports of TwistAvgA: ['RBM3D.BA.TwistPins']; of TwistAvgA2: ['RBM3D.BA.TwistAvgA']; of TwistAvgB: ['RBM3D.BA.TwistAvgA2']
```
Observation for the 1a-audit: the direct-import grep of the ticket (`^import RBM3D.BA.(MainInd|TwistPins|Step6|TwistStep)`, 0 hits) stays 0, but importing `BA/TwistAvgA2`/`B` puts `RBM3D.BA.TwistPins` (TL stage pins, not V) into the transitive closure, which the ticket's start-condition evidence ("closure … no `BA.TwistPins`") excluded for the planned imports; no `BA.MainInd*`/`Step6*` enters.
### Verdicts (replace the T7 verdict of (a))
- **T7 / D1 (i) `T2519_HoffBA`: PASS** with Amend 1's input list (items 1, 3): the exponents close at slack 0 (rows 4′, 5′), both derivative terms (`𝒮₁`, `𝒮₂`) pair a 4-loop `≺ Λ³` with a 2-loop `≺ Λ`, the self-term (row 2) and the scale-free envelope (row 10′) need nothing outside PB `lk 1..4`, `localLaw`, the K-bound at the same grid time, `Kt = m` on 1-loops, `BAReal`, `baM_row_l1`, `ol_gueHBA_eq`/`mixMatBA` and the `TwistAvg*` lemmas above. No stop of Amend 1 item 4 (no twisted 2-loop at `(Nη)⁻²`, no `twTr` at `t₁`, no `n0 ≥ 5`, no K-bound at another time, no extra premise of `gueGrid_eq729BA` found by mathematics). Not Lean-tested here (probe step).
- Price: **b′ booked** (row b unsplit 2,404 > 1,950); **C5S-C1 fires by 55 at ratio 1.34** (8,951, margin 74, at ratio 1.46): the dispatcher reads this line.
- Paper-delta candidates: `T2519a` (C5H-C4: the GUE grid needs (I3) at `n = 4`, path bounds to `n₀ = 4` against the band's `n₀ = 3`, and the twisted 1-loop law takes T.7's input set, plus `p` of row 7′ carries the grid union); `T2519b` (grid local law against `M^{(B)}⊗1`) unchanged.

## (a″) Probe compile — Fri Oct 16 12:58:39 UTC 2026
Role `prover-max`; probe step after (a′) (Amend 1 items 1, 2, 5, 7). Branch `t/T2519`, commit `b992c2e7` (parent `25e22c0b` = `main`); `git diff --name-only 25e22c0b..HEAD` = `RBM3D/Probe/T2519Pins.lean` only; **298 lines** (ticket: ≤ 200, cap 300; the eight restated texts alone are `:29-98`); imports = the seven modules of `T2519-pins.lean`; no `sorry`/`admit`/`native_decide`/`axiom` (`grep -c` = 0). `SCR` = scratchpad of (a); scripts and outputs in `SCR/T2519/`.
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2519 && (date -u; lake env lean docs/tickets/checks/T2519-pins.lean; echo "exit=$?"; date -u)     # baseline: the pins compile in this worktree
Fri Oct 16 12:54:32 UTC 2026
exit=0
Fri Oct 16 12:54:37 UTC 2026
$ (date -u; lake env lean RBM3D/Probe/T2519Pins.lean; echo "exit=$?"; date -u)     # the probe; committed file = compiled file (`git diff HEAD --quiet`)
Fri Oct 16 12:58:23 UTC 2026
'RBM.BA.T2519Probe.probe_ident' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2519Probe.probe_lead' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2519Probe.probe_Kt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
T2519_HoffBA : ℕ → Prop
T2519_LeadBA : ℕ → Prop
exit=0
Fri Oct 16 12:58:30 UTC 2026
$ python3 -I SCR/T2519/diffdefs.py docs/tickets/checks/T2519-pins.lean RBM3D/Probe/T2519Pins.lean     # the eight restated texts against the pins (comments dropped, token diff)
T2519_ProdBA: IDENTICAL
T2519_LLBA: IDENTICAL
T2519_QueBA: IDENTICAL
T2519_KFamBA: 1 token change(s)
   replace: [3] -> [4]
T2519_PathBoundsBA: IDENTICAL
T2519_PBBA: 1 token change(s)
   replace: [3) 3] -> [4) 4]
T2519_ProducersBA: IDENTICAL
T2519_HoffBA: 3 token change(s)
   replace: [1] -> [4]
   insert: [] -> [0 < g n →]
   insert: [] -> [→ (∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)), I.WF → 2 ≤ I.length → I.length ≤ 4 → ‖Kt n s I‖ ≤ ((sz.size n : ℕ) : ℝ) ^ ε * (((sz.size n : ℕ) : ℝ) * etaOf (m n) s)⁻¹ ^ (I.length - 1))]
$ python3 -I SCR/T2519/verbatim.py RBM3D/BA/GUEOneLoop.lean RBM3D/Probe/T2519Pins.lean     # `K := gueGridK sz n0` in the 2nd StochDomAt of the merged text of T2517_OneLoopBA
second StochDomAt of gueGrid_expect_oneLoopBA (K := gueGridK sz n0) == conclusion of T2519_HoffBA : True
lengths 645 645
$ python3 -I SCR/T2519/closure.py . RBM3D/Probe/T2519Pins.lean
direct imports: 7 ; closure: 273 modules; BA.(MainInd|TwistPins|Step6|TwistStep|TwistAvg*) in closure: []
$ python3 SCR/T2519/lead_check.py     # MC of T2519_LeadBA at d = 1, L = 3, W = 2 (N = 6), 10^6 samples; Var X_xy = (t1 [x]=[y] + sigma)/W^d; 2nd line: sigma x 1.5 in the right side (control)
L=3 W=2 N=6 g=0.4 E=0.8 m=(0.1+0.75j) t1=0.2 u=0.7 sigma_scale=1.0 S=1000000: max|E T|=1.974e-01; max|E[T - RHS]|=6.167e-04; max z=0.97; mean z=0.53
L=3 W=2 N=6 g=0.4 E=0.8 m=(0.1+0.75j) t1=0.2 u=0.7 sigma_scale=1.5 S=1000000: max|E T|=1.973e-01; max|E[T - RHS]|=7.153e-02; max z=124.92; mean z=110.42
$ python3 -I SCR/T2519/inst_check2.py     # regime of the Lean instance of section 4 (exact rationals; Im m in [1/2, 1])
 n  | L^3(1-t1) / lam^2 | N*delta | N*eta_t0 lower | (t0-t1)/eta_t0 <= 2/N  vs  N^-1/20 | (N eta)^-1 <= 4/(n+1)^3  vs  N^-1/20
0    | 0.0625 (<= 1: True) | 0.5 | 0.25 | 9.54e-07 <= 4.830e-01: True | 4.000e+00 <= 4.830e-01: False
2    | 0.0625 (<= 1: True) | 13.5 | 6.75 | 2.46e-15 <= 1.797e-01: True | 1.481e-01 <= 1.797e-01: True
10   | 0.0625 (<= 1: True) | 665.5 | 332.8 | 1.72e-25 <= 5.580e-02: True | 3.005e-03 <= 5.580e-02: True
100  | 0.0625 (<= 1: True) | 5.152e+05 | 2.576e+05 | 7.97e-43 <= 7.586e-03: True | 3.882e-06 <= 7.586e-03: True
1000 | 0.0625 (<= 1: True) | 5.015e+08 | 2.508e+08 | 9.37e-61 <= 9.628e-04: True | 3.988e-09 <= 9.628e-04: True
$ name-clash: grep -rnw --include='*.lean' -e NAME RBM3D | grep -v RBM3D/Probe/T2519Pins.lean | wc -l     # 28 new names, then 6 C5 names expected absent
twTrBA=0 KClauses=0 probe_iblk=0 probe_ident=0 probe_lead=0 probe_Kt_one=0 T2519_ProdBA=0 T2519_LLBA=0 T2519_QueBA=0 T2519_KFamBA=0 T2519_PathBoundsBA=0 T2519_PBBA=0 T2519_ProducersBA=0 T2519_HoffBA=0 T2519_LeadBA=0 inst_g=0 inst_E=0 inst_m=0 inst_δ=0 inst_t0=0 inst_t1=0 inst_baReal=0 inst_t10=0 inst_t0_lt=0 inst_t1_nonneg=0 inst_δ_pos=0 inst_δ_le=0 
Hyp_Kt_detDomBA=0 Hyp_Kt_oneBA=0 gueGrid_eq729BA=0 gueGrid_twistBA=0 GUEPathBoundsBA=0 gueGrid_pathBoundsBA=0 
$ lake env lean SCR/T2519/S3.lean     # S3 = the probe with ONE change, the guard `0 < g n →` removed from the Kt = m premise of T2519_HoffBA (line 85; `diff` = that line only); 2 errors, exit=1, both this mismatch (first in full)
SCR/T2519/S3.lean:241:72: error: Application type mismatch: The argument
  probe_Kt_one sz hκ hKF hE ht1 ht10 ht0
has type
  ∀ (n : ℕ),
    0 < g n →
      ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ (σ : Bool) (a : Zd d (sz.L n)), Kt n s { σ := [σ], a := [a] } = mSigOf (m n) σ
but is expected to have type
  ∀ (n : ℕ),
    ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ (σ : Bool) (a : Zd d (sz.L n)), Kt n s { σ := [σ], a := [a] } = mSigOf (m n) σ
in the application
  hH hd sz κ Λ hκ hΛ g E t1 t0 m 4 Kt hsize le_rfl hlam hE ht1 ht10 ht0 (probe_Kt_one sz hκ hKF hE ht1 ht10 ht0)
...
SCR/T2519/S3.lean:289:24: error: Application type mismatch: The argument
  probe_Kt_one sz0 ?m.85 hKF inst_baReal inst_t1_nonneg inst_t10 inst_t0_lt
has type
...
```
**What compiles (probe lines).**
- `:29-98` the eight texts (token diff above).
- `:103-143` `probe_iblk`, `twTrBA`, **`probe_ident`**: the identity `t_{aq} - M^{(++)}_{aq} = M^{(B)}_{aq} twTr(q,a)` for every matrix `G` (hypothesis `(E + m).im ≠ 0` only). Its left side is the summand `:92-96` of the conclusion of `T2519_HoffBA` at `G = Gres (gueHBA …) (ztOf …) true`, `a = p.2.1`, `q = p.2.2`, so `hoff` is `‖M^{(B)}_{aq}‖ ‖twTr(q,a)‖ ≺ ‖M^{(B)}_{aq}‖ (Nη_u)⁻¹`.
- `:147-159` **`T2519_LeadBA`**, R1's leading expansion at grid time `k` (statement only): `𝔼 T(q,a) = Σ_{p,r} Ŝ_{pr} 𝔼[M^{(B)}_{qp} (M^{(B)}_{pa} + T(p,a)) (g_r - m)]`, `Ŝ = t₁δ + σ_k`, `σ_k = (u_k - t₁)/L^d`; it is (C.3) at `Φ = 1` with (C.4) of T.7 (`T2398-TL-proofs.md:70-75`) on the grid, the twisted twin of the merged `GUEOneLoop_blockId` (`BA/GUEOneLoop:471`); the moments `Φ = T^{p-1} T̄^p` add the derivative terms `𝒮₁`, `𝒮₂`. The MC above: max z = 0.97 over the nine pairs at signal `max|E T|` = 0.197; control (wrong `σ`) z = 125.
- `:162-193` **`probe_lead`** (pair stability): `‖Σ_{p,r} Ŝ_{pr} M_{qp} (M_{pa} + τ_p) γ_r‖ ≤ u ρΛ_u (1 + C_M T_max)` from `‖τ_p‖ ≤ T_max`, `‖γ_r‖ ≤ ρΛ_u`, `C_M = (BAct_rate d Λ κ)⁻¹ expC (d-2) (BAct_rate d Λ κ)`. **`twTr` does appear in its own leading term** (`τ_p = twTr(p,a)`), with the self-coefficient `u ρΛ_u C_M`, **`L`- and `g`-free** as `T2517_StableBA`. Premises: `BAReal`, the hypotheses of `baM_row_l1` (`GreenStab:116`), `baM_rho2` (`GreenStab:132`, premise `BASelf` = first part of `BAReal`), and PB `lk 1` as the good event `‖γ_r‖ ≤ ρΛ_u`. **C5S-C2 is not hit.**
- `:199` (i) `T2519_ProducersBA → UNG1Rowk …` typechecks with the amended `T2519_PBBA`, `T2519_KFamBA`. `:209` `T2519_KFamBA d sz E' t1 t0 Kt → KClauses …` at `g = √t₀ λ`, `m = BAm …` (`⟨h.1, h.2.1⟩`). `:214` `probe_Kt_one` = `Hyp_Kt_oneBA`: `Kt = m_σ` on 1-loops from `hKinit`, `hK` (`baKsol_one`, the mean-value bound, `Hyp_primRhs_one` by `open private`).
- `:235` (ii): the hypotheses of `gueGrid_eq729BA` (BA twin of `Eq729B:622-637`, `n₀ = 4`) supply every premise of `T2519_HoffBA`: PB from `hP`; the K-bound from the conclusion of `Hyp_Kt_detDomBA` at `n₀ = 4` (twin of `HypA:704-707`; range `≤ 2 * 4`, cut to `≤ 4` by `omega`); `Kt = m` on 1-loops by `probe_Kt_one`; the rest are the band's `hsize`, `hlam`, `hE`, `ht*`.
- `:246` the conclusion of `T2519_HoffBA` is, by type, the `hoff` argument of the merged `gueGrid_expect_oneLoopBA` at `K = gueGridK sz 4` (plus the script check above: textually equal).
- `:251-290` the `d = 3` instance: `sz0` (`N_0 = 2^21`), its flow datum (`BAReal` at `κ = 1/2` for every `n`), `t₀ = 1 - δ`, `t₁ = t₀ - δ/N`, `δ_n = (2^22 (n+1)^15)⁻¹` (a window of positive length). `:277` the family `KClauses` is nonempty (`gueK_existsBA`, length bound `4 * 4`, guarded by `0 < g n`). `:286` applies `T2519_HoffBA 3` with `Tendsto size`, `∀ᶠ n, 0 < g n ≤ (1/10)⁻¹`, `BAReal ∀ n`, the three time premises and `Kt = m` on 1-loops discharged; only PB (row c) and the K-bound (row a) stay hypotheses. Regime of the data (table above): `L^3 (1 - t₁)/λ² = 0.0625`, `(t₀ - t₁)/η_{t₀} ≤ 2/N ≤ N^{-1/20}`, `(N η_{t₀})⁻¹ ≤ 4/(n+1)^3 ≤ N^{-1/20}` at `n = 2, 10, 100, 1000` (false at `n = 0`; that premise is `∀ᶠ n`).
**Not compiled here:** the Stein identity itself (`T2519_LeadBA` is a statement), the Hilbert-Schmidt bounds on `𝒮₁`, `𝒮₂`, the moment bootstrap, Markov and the union (row b; no `BA/TwistAvg*` lemma is read by the probe, closure above); `Hyp_Kt_detDomBA` (row a) and PB (row c) stay hypotheses. The probe adds no census figure: (a′)'s price and C5S-C1 reading (fires by 55 at ratio 1.34, margin 74 at 1.46) are unchanged and left to the dispatcher and the 1a-audit.
**Findings for the 1a-audit** (the token diff above is Amend 1 item 1 plus two edits of `T2519_HoffBA`, F1 and F2).
- **F1 `1 ≤ n0` → `4 ≤ n0`.** PB must contain `lk 4` (Amend 1 item 3; (a′) rows 4′-5′); with `1 ≤ n0` the text admits `n0 ∈ {1, 2, 3}`, where R1 has no 4-loop input. The consumer passes `n0 = 4` (`:235`, `:246`, `:286`). The literal text (pins plus the one premise) is a well-formed definition as well; the choice is the audit's, I propose `4 ≤ n0`.
- **F2 guard `0 < g n →` on the `Kt = m` premise.** The clauses of `BAKFam` and `KClauses` are guarded by `0 < g n` (`Sizes.lam` has no sign; ticket coverage row 14), so `Hyp_Kt_oneBA` gives the 1-loop equation only where `0 < g n`; without the guard the two examples that discharge that premise (`:235`, `:286`) fail (S3 above). The guard makes the premise weaker (the text stronger), and R1 needs the equation only eventually (the window premise gives `∀ᶠ n, 0 < g n`). This is paper-delta candidate `T2519c` (positivity guard), now used.
- **F3 window of C4's text.** `gueGrid_expect_oneLoopBA` takes `∀ n, 0 < g n ∧ g n ≤ Λ`; `T2519_HoffBA` and the band `hlam` have `∀ᶠ n`. `:246` takes the `∀ n` form as its own premise and passes `Eventually.of_forall` to `T2519_HoffBA`: the padding of coverage row 14 sits at the call of `gueGrid_expect_oneLoopBA`, not in `T2519_HoffBA`.
- **F4 Amend 1 item 4 against the probe.** No statement has a twisted 2-loop or `twTr` at `t₁` (the only `twTr` is at `gridTime … k`); no `n₀ ≥ 5`; the K-bound premise is quantified over `s ∈ [t₁, t₀]` only; the import closure has no TL/V stage module; the premises of `gueGrid_eq729BA` used are the band's (`hsize`, `hlam`, `hE`, `ht*`, `hKinit`, `hK`, PB, K-bound).
**Names.** Verified present (compile): `Finset.sum_nbij'`, `norm_image_sub_le_of_norm_deriv_le_segment'`, `inv_le_comm₀`, `one_le_pow₀`, `div_le_self`, `Complex.norm_real`, `Real.norm_of_nonneg`, `Finset.sum_ite_eq`, `Equiv.symm_apply_apply`, `Equiv.apply_symm_apply`, `tendsto_natCast_atTop_iff`, `Exists.choose_spec`, simprocs `↓reduceDIte`, `↓reduceIte`; merged: `BAMres_fine_apply` (`FlowPins:102`), `baM_row_l1`, `baM_rho2` (`GreenStab:116, 132`), `baKsol_one` (`KInduct:77`), `gueK_existsBA` (`GUEKPrim:1015`), `BAflow_real`, `BAflow_lam0_window` (`GreenSchur:59, 72`), `flow_sz0`, `zSeq`, `sz0`, `Sizes.one_le_size` (`StochDomAt:130`). Deprecated in this Mathlib (compile warnings seen while writing; replaced): `if_true`, `dif_pos`, `dite_cond_eq_true`.

## (b) Row a, stage 1b — `prover-max` (claude-sonnet-5-5), branch `t/T2519`, worktree `RBM3D-wt/T2519`
Script output first; times from `date -u`. Stage 1b started Fri Oct 16 13:15:38 UTC 2026; `main` (cabd9a3d) merged in at 13:16:21 (c0c75da1). **First commit, the §1 vocabulary `GUEPathBoundsBA`, `BAKFam`, `BAPB` (rows b, b′ stack on it): `19df37e2`** (13:22:59; its parent is the merge c0c75da1). Final commit `f44898b4`; the full `lake build` on it ran 14:17:07 → 14:18:24. The probe `b992c2e7` stays on the branch, never merged. Scripts (`stmts.py`, `statdiff.py`, `c1grep.py`, `nametab.py`, `closure.py`) and the two Lean check files are in the session scratchpad `T2519/`, not in the repo.
```
$ git log --format='%h %ad %s' --date=format:%H:%M:%S%z c0c75da1..HEAD     # local time (UTC-7)
f44898b4 07:17:07-0700 T2519 row a: Hyp_gridBA instance with every hypothesis discharged (finite-sum constants, 
9f070ca8 07:06:33-0700 T2519 row a: GUEHypABA_hell_of_hell (RBG zero-mode premises to the K-lemma premise), docs
c53b0a69 07:01:13-0700 T2519 row a: GUEHypABA instances at n0 = 4 (the n0 of the amended texts), docstring
a620faef 06:56:20-0700 T2519 row a: BA/GUEEntryGridBA, map_gueHBA_eq_mixMatBA, gueGrid_entry_boundBA, instances,
82cd7476 06:50:03-0700 T2519 row a: BA/GUEHypABA, Hyp_Kt_detDomBA, gueKproc_detDomBA, Hyp_Kt_oneBA, Hyp_gridBA, 
83170e46 06:39:26-0700 T2519 row a: BA/GUEProcBA sections 2-4, the BA process layer (gueDevBA ... gueDprocBA, st
19df37e2 06:22:59-0700 T2519 row a: BA/GUEProcBA section 1, the vocabulary GUEPathBoundsBA, BAKFam, BAPB (Amend 
$ git diff --name-only cabd9a3d...t/T2519      # cabd9a3d = main at the merge (main is now 66649d46, a docs-only commit); the probe is branch-only
RBM3D.lean RBM3D/BA/GUEEntryGridBA.lean RBM3D/BA/GUEHypABA.lean RBM3D/BA/GUEProcBA.lean RBM3D/Probe/T2519Pins.lean RBM3D/Test/Axioms.lean 
$ git show --stat --format='%h' 19df37e2   # the first commit
19df37e2 RBM3D.lean | 1 + RBM3D/BA/GUEProcBA.lean | 133 ++++++++++++++++++++++++++++++++++++++++++++++++ RBM3D/Test/Axioms.lean | 1 + 3 files changed, 135 insertions(+) 
```
**Build, axioms, hygiene.**
```
$ lake build RBM3D.BA.GUEProcBA RBM3D.BA.GUEHypABA RBM3D.BA.GUEEntryGridBA      # 14:18:41 -> 14:18:44, HEAD f44898b4
Build completed successfully (4000 jobs).
$ for f in GUEProcBA GUEHypABA GUEEntryGridBA; do lake env lean RBM3D/BA/$f.lean | wc -l; done      # warnings + errors, HEAD
0 0 0
$ lake build      # full library at HEAD f44898b4, exit=0 (14:17:07 -> 14:18:24); `#assert_rbm_axioms` ran inside it
info: RBM3D.lean:661:0: axiom audit: 15604 theorems, 4796 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 124 (borrowed 1, owed 51, structural 52, refuted 6, superseded 14).
registry: 2 borrowed + 115 owed + 143 structural + 7 refuted + 19 superseded; 162 registered premise(s) carry nothing yet: [... RBM.BA.GUEPathBoundsBA ...]
Build completed successfully (4431 jobs).
$ #print axioms of every public declaration of the three files (27: 3 vocabulary defs, 6 process defs, 9 facts, norm_egtNGUEOf_le, gueDevBA_succ_le, 4 K/grid theorems, GUEHypABA_hell_of_hell, 2 entry theorems)
27 declarations with axioms [propext, Classical.choice, Quot.sound]
$ grep -cE '\bsorry\b|\badmit\b|native_decide|^\s*axiom ' the three files        # HEAD: 0 0 0
$ grep -cE '^\s*(private )?(def|abbrev|structure) (gueHBA|ztOf|etaOf|mSigOf|genMatGUEOf|egtNGUEOf|Mres|BAReal|kTwoGUEBA|mixMatBA|GUEEntryMixBA|RBG_[A-Za-z]+|BAEd|BAMO)\b'      # X1-C4, HEAD: 0 0 0
$ grep -cE '^import RBM3D\.BA\.(MainInd|TwistPins|Step6|TwistStep|TwistAvg)'; closure.py on each file      # HEAD: 0 0 0; closures 255 / 263 / 266 modules, forbidden modules in the closure: [] [] []
$ c1grep.py (C1 regex of the ticket on the statements of the 27 public declarations; `gueH`, `Pgue`, `PathΩ` only at `(sz.withLam 0)`; the one allowed `ouP (UNModel.band (sz.withLam 0))`)
TOTAL C1 hits on public statements: 0        # UBA-C1: `sz.lam` occurs only in the pinned `BAKFam`/`BAPB` (`g = √t₀ λ`)
$ name-clash: git grep -w NAME main -- RBM3D RBM3D.lean   for the 27 new public names -> names with a main hit: 0; on the branch outside the three files: only the registry line (`GUEPathBoundsBA`), the three `import` lines and docstrings of the branch-only probe
```
**Statements against the signed texts (target 1 and `map_gueHBA_eq_mixMatBA`), by script and by Lean.**
```
$ statdiff.py RBM3D/Probe/T2519Pins.lean RBM3D/BA/GUEProcBA.lean T2519_PathBoundsBA=GUEPathBoundsBA T2519_KFamBA=BAKFam T2519_PBBA=BAPB   # token diff, comments dropped, names mapped
T2519_PathBoundsBA -> GUEPathBoundsBA: IDENTICAL  (261 tokens)
T2519_KFamBA -> BAKFam: IDENTICAL  (252 tokens)
T2519_PBBA -> BAPB: IDENTICAL  (68 tokens)
$ lake env lean signed.lean   # (scratchpad file, not committed) imports the built probe: `example : @T2519_PathBoundsBA = @GUEPathBoundsBA := rfl`, likewise `T2519_KFamBA`/`BAKFam`, `T2519_PBBA`/`BAPB`, `T2519_ProducersBA`; `example : T2519_MapMixBA-text := fun … => map_gueHBA_eq_mixMatBA …`
exit=0
$ lake env lean chain.lean   # (scratchpad file, not committed) Amend 3 item 5: `hKdet` of the probe `:238-240` restated as `HKdetTy` (n₀ = 4); `example … : HKdetTy sz t1 t0 m Kt := Hyp_Kt_detDomBA hd sz … 4 …`; `Kt = m` premise of `T2519_HoffBA` from `Hyp_Kt_oneBA`; `BAKFam` clauses = `hKinit`, `hK`
exit=0
```
**Target statements extracted by script** (`stmts.py`: signature up to the top-level `:=`, comments dropped, whitespace collapsed; `gueDevBA` with its body). Declaration index (name:line): GUEProcBA — GUEPathBoundsBA:58 BAKFam:76 BAPB:93 gueDevBA:117 gueStopBA:123 gueLmaxBA:127 gueDmaxBA:132 gueLprocBA:140 gueDprocBA:145 gueLprocBA_nonneg:247 gueDprocBA_nonneg:252 gueLprocBA_continuousOn:258 gueDprocBA_continuousOn:263 gueLprocBA_le:270 gueDprocBA_le:281 gueLprocBA_odd:292 gueLprocBA_time:307 gueDprocBA_time:315 norm_egtNGUEOf_le:338 gueDevBA_succ_le:417; GUEHypABA — Hyp_Kt_detDomBA:268 gueKproc_detDomBA:291 Hyp_Kt_oneBA:454 GUEHypABA_hell_of_hell:483 Hyp_gridBA:509; GUEEntryGridBA — map_gueHBA_eq_mixMatBA:57 gueGrid_entry_boundBA:296.
```
def gueDevBA (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ (sz.withLam 0)) : ℝ := ⨆ ij : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n), ‖(green (gueHBA sz g t1 t0 K n k ω) (ztOf (m n) (E n) (gridTime t1 t0 K n k)) - Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) ij.1 ij.2‖
theorem gueDevBA_succ_le (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ) (n k : ℕ) (hm : 0 < (m n).im) (hm1 : ‖m n‖ ≤ 1) (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1) (hk : k < K n) (ω : PathΩ (sz.withLam 0)) : gueDevBA sz g E t1 t0 m K n (k + 1) ω ≤ gueDevBA sz g E t1 t0 m K n k ω + (etaOf (m n) (t0 n))⁻¹ ^ 2 * (Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) * ∑ i : Idx d (sz.L n) (sz.W n), ∑ j : Idx d (sz.L n) (sz.W n), ‖Sizes.seqXmat (sz.withLam 0) n (ω (k + 1)) i j‖ + gridStep t1 t0 K n)
theorem norm_egtNGUEOf_le (L W : ℕ) [NeZero L] [NeZero W] (m : ℂ) (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (I : LoopIdx (Zd d L)) {ε B : ℝ} (hε : ∀ (σ : Bool) (a : Zd d L), ‖Matrix.trace (Gres (blockMat d L W M) (ztOf m E u) σ * Eblk d L W a) - mSigOf m σ‖ ≤ ε) (hB : ∀ k ∈ Finset.Icc 1 I.length, ∀ b : Zd d L, ‖loopL d L W (blockMat d L W M) (ztOf m E u) (I.cutGlue k b)‖ ≤ B) : ‖egtNGUEOf d L W m E u M I‖ ≤ (I.length : ℝ) * (((W * L) ^ d : ℕ) : ℝ) * ε * B
theorem Hyp_Kt_detDomBA {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) {κ Λ τU : ℝ} (hκ : 0 < κ) (hΛ : 0 < Λ) (hτU : 0 < τU) (n0 : ℕ) {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ} (hr : ∀ n, BAReal d (sz.L n) (g n) κ (E n) (m n)) (hlam : ∀ᶠ n : ℕ in atTop, 0 < g n ∧ g n ≤ Λ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1) (hsz : Tendsto sz.size atTop atTop) (h730 : ∀ᶠ n : ℕ in atTop, t0 n - t1 n ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaOf (m n) (t0 n)) (hell : ∀ᶠ n : ℕ in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ 2 * g n ^ 2) (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) (hKinit : ∀ n, 0 < g n → ∀ I : LoopIdx (Zd d (sz.L n)), Kt n (t1 n) I = BAKsol d (sz.L n) (sz.W n) (BAMsigma d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n))) (PropSpin (m n)) (t1 n) I) (hK : ∀ n, 0 < g n → ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)), I.WF → 1 ≤ I.length → I.length ≤ 4 * n0 → HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I) (Set.Icc (t1 n) (t0 n)) t) : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)), I.WF → 2 ≤ I.length → I.length ≤ 2 * n0 → ‖Kt n s I‖ ≤ ((sz.size n : ℕ) : ℝ) ^ ε * (((sz.size n : ℕ) : ℝ) * etaOf (m n) s)⁻¹ ^ (I.length - 1)
theorem gueKproc_detDomBA {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) {κ Λ τU : ℝ} (hκ : 0 < κ) (hΛ : 0 < Λ) (hτU : 0 < τU) (n0 : ℕ) {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ} (hr : ∀ n, BAReal d (sz.L n) (g n) κ (E n) (m n)) (hlam : ∀ᶠ n : ℕ in atTop, 0 < g n ∧ g n ≤ Λ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1) (hsz : Tendsto sz.size atTop atTop) (h730 : ∀ᶠ n : ℕ in atTop, t0 n - t1 n ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaOf (m n) (t0 n)) (hell : ∀ᶠ n : ℕ in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ 2 * g n ^ 2) (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) (hKinit : ∀ n, 0 < g n → ∀ I : LoopIdx (Zd d (sz.L n)), Kt n (t1 n) I = BAKsol d (sz.L n) (sz.W n) (BAMsigma d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n))) (PropSpin (m n)) (t1 n) I) (hK : ∀ n, 0 < g n → ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)), I.WF → 1 ≤ I.length → I.length ≤ 4 * n0 → HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I) (Set.Icc (t1 n) (t0 n)) t) : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ (t : TimeIcc t1 t0 n) (l : Set.Icc 2 (2 * n0)), gueKproc sz t1 t0 (gueGridK sz n0) Kt n (l : ℕ) (t : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ ε * (((sz.size n : ℕ) : ℝ) * etaOf (m n) (t : ℝ))⁻¹ ^ ((l : ℕ) - 1)
theorem Hyp_Kt_oneBA {d : ℕ} (sz : Sizes d) {κ : ℝ} (hκ : 0 < κ) {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ} (n0 : ℕ) (hn0 : 1 ≤ n0) (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) (hr : ∀ n, BAReal d (sz.L n) (g n) κ (E n) (m n)) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1) (hKinit : ∀ n, 0 < g n → ∀ I : LoopIdx (Zd d (sz.L n)), Kt n (t1 n) I = BAKsol d (sz.L n) (sz.W n) (BAMsigma d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n))) (PropSpin (m n)) (t1 n) I) (hK : ∀ n, 0 < g n → ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)), I.WF → 1 ≤ I.length → I.length ≤ 4 * n0 → HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I) (Set.Icc (t1 n) (t0 n)) t) (n : ℕ) (hg : 0 < g n) {u : ℝ} (hu : u ∈ Set.Icc (t1 n) (t0 n)) (σ : Bool) (a : Zd d (sz.L n)) : Kt n u ⟨[σ], [a]⟩ = mSigOf (m n) σ
theorem Hyp_gridBA {d : ℕ} (sz : Sizes d) (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) (n l : ℕ) (ω : PathΩ (sz.withLam 0)) (g1 g3 g4 : ℝ → ℝ) {c Cf Ce err Λ0 : ℝ} (ht10 : t1 n ≤ t0 n) (hm : 0 < (m n).im) (ht0 : t0 n < 1) (hc : 0 ≤ c) (hCf : 0 ≤ Cf) (hCe : 0 ≤ Ce) (hg1 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ g1 u) (hg3 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ g3 u) (hg4 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ g4 u) (hg1c : ContinuousOn g1 (Set.Icc (t1 n) (t0 n))) (hg3c : ContinuousOn g3 (Set.Icc (t1 n) (t0 n))) (hg4c : ContinuousOn g4 (Set.Icc (t1 n) (t0 n))) (h0 : ∀ x : (Fin l → Bool) × (Fin l → Zd d (sz.L n)), ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n 0 ω)) (ztOf (m n) (E n) (gridTime t1 t0 K n 0)) (loopOf x.1 x.2) - Kt n (gridTime t1 t0 K n 0) (loopOf x.1 x.2)‖ ≤ c * Λ0) (hM : ∀ k ≤ K n, ∀ x : (Fin l → Bool) × (Fin l → Zd d (sz.L n)), ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k ω)) (ztOf (m n) (E n) (gridTime t1 t0 K n k)) (loopOf x.1 x.2) - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n 0 ω)) (ztOf (m n) (E n) (gridTime t1 t0 K n 0)) (loopOf x.1 x.2) - (gridStep t1 t0 K n : ℂ) * ∑ j ∈ Finset.range k, genMatGUEOf d (sz.L n) (sz.W n) (m n) (E n) (gridTime t1 t0 K n j) (gueHBA sz g t1 t0 K n j ω) (loopOf x.1 x.2)‖ ≤ c * (Real.sqrt (gridTime t1 t0 K n k - t1 n) * (⨆ j : Fin k, Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ * (etaOf (m n) (gridTime t1 t0 K n j))⁻¹ ^ 2 * RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω)) (ztOf (m n) (E n) (gridTime t1 t0 K n j)) (2 * l))) + (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n k))⁻¹ ^ l)) (hq : ∀ j < gueStopBA sz g E t1 t0 m K δ n ω, Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ * (etaOf (m n) (gridTime t1 t0 K n j))⁻¹ ^ 2 * RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω)) (ztOf (m n) (E n) (gridTime t1 t0 K n j)) (2 * l)) ≤ g4 (gridTime t1 t0 K n j)) (hF : ∀ j < gueStopBA sz g E t1 t0 m K δ n ω, ∀ x : (Fin l → Bool) × (Fin l → Zd d (sz.L n)), ‖primRhsGUE d (sz.L n) (sz.W n) (loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω)) (ztOf (m n) (E n) (gridTime t1 t0 K n j))) (loopOf x.1 x.2) - primRhsGUE d (sz.L n) (sz.W n) (Kt n (gridTime t1 t0 K n j)) (loopOf x.1 x.2)‖ ≤ Cf * g1 (gridTime t1 t0 K n j)) (heG : ∀ j < gueStopBA sz g E t1 t0 m K δ n ω, ∀ x : (Fin l → Bool) × (Fin l → Zd d (sz.L n)), ‖egtNGUEOf d (sz.L n) (sz.W n) (m n) (E n) (gridTime t1 t0 K n j) (gueHBA sz g t1 t0 K n j ω) (loopOf x.1 x.2)‖ ≤ Ce * g3 (gridTime t1 t0 K n j)) (hdisc : ∀ k ≤ K n, ∀ x : (Fin l → Bool) × (Fin l → Zd d (sz.L n)), ‖Kt n (gridTime t1 t0 K n k) (loopOf x.1 x.2) - Kt n (gridTime t1 t0 K n 0) (loopOf x.1 x.2) - (gridStep t1 t0 K n : ℂ) * ∑ j ∈ Finset.range k, primRhsGUE d (sz.L n) (sz.W n) (Kt n (gridTime t1 t0 K n j)) (loopOf x.1 x.2)‖ ≤ err) {t : ℝ} (ht : t ∈ Set.Icc (t1 n) (t0 n)) {k : ℕ} (hkσ : k ≤ gueStopBA sz g E t1 t0 m K δ n ω) (hkt : ∀ j < k, gridTime t1 t0 K n j ≤ t) : gueDmaxBA sz g E t1 t0 m K Kt n l k ω ≤ (c * Λ0 + err) + c * (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n k))⁻¹ ^ l + (Cf * supOn g1 (t1 n) t + Ce * supOn g3 (t1 n) t) * (gridTime t1 t0 K n k - t1 n) + (c * supOn g4 (t1 n) t) * Real.sqrt (gridTime t1 t0 K n k - t1 n)
theorem GUEHypABA_hell_of_hell {d L : ℕ} (hd : 3 ≤ d) (hL : 3 ≤ L) {t1 t0 lam : ℝ} (ht10 : t1 ≤ t0) (hell : (L : ℝ) ^ d * (1 - t1) ≤ lam ^ 2) (hell1 : (L : ℝ) ^ d * (1 - t1) ≤ 1) : (L : ℝ) ^ d * (1 - t1) ≤ 2 * (Real.sqrt t0 * lam) ^ 2
theorem map_gueHBA_eq_mixMatBA {d : ℕ} (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ht1 : 0 ≤ t1 n) (ht10 : t1 n ≤ t0 n) : (Pgue (sz.withLam 0)).map (gueHBA sz g t1 t0 K n k) = (ouP (UNModel.band (sz.withLam 0)) n).map (mixMatBA sz n (g n) (t1 n) (gridTime t1 t0 K n k - t1 n))
theorem gueGrid_entry_boundBA (sz : Sizes d) (hd : 3 ≤ d) {𝔠 𝔡 κ : ℝ} (hadm : sz.Admissible 𝔠 𝔡) (hκ : 0 < κ) (n0 : ℕ) {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ} (hdata : ∀ n, 0 < g n ∧ g n ≤ 𝔡⁻¹ ∧ BAReal d (sz.L n) (g n) κ (E n) (m n)) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1) {δ : ℕ → ℝ} (hδ0 : ∀ n, 0 ≤ δ n) {c₀ : ℝ} (hc₀ : 0 < c₀) (hδ : ∀ᶠ n in atTop, δ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-c₀)) : StochDomAt (Pgue (sz.withLam 0)) sz.size (fun n (p : Fin (gueGridK sz n0 n + 1) × (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))) ω => {ω' : PathΩ (sz.withLam 0) | ∀ i j : Idx d (sz.L n) (sz.W n), ‖(green (gueHBA sz g t1 t0 (gueGridK sz n0) n p.1 ω') (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n p.1)) - Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) i j‖ ≤ δ n}.indicator (fun ω' => ‖(green (gueHBA sz g t1 t0 (gueGridK sz n0) n p.1 ω') (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n p.1)) - Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) p.2.1 p.2.2‖ ^ 2) ω) (fun n p ω => gueLmaxBA sz g E t1 t0 m (gueGridK sz n0) n 2 p.1 ω + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹)
```
**Compiled nonempty instances** (`example`s in the same files, built by the commands above; data: `d = 3`, `sz0` (`N_0 = 2^21`), its BA flow datum `(g, E, m) = (BAflowLam0, BAflowEs, BAmF)` with `BAReal` at `κ = 1/2` for every `n`, grid `K = 4`; K lemmas at `n₀ = 4`, `τ_U = 1/20`, window `1 - t₀ = λ²/(4L³)`, `t₀ - t₁ = x/(2N)`; entry bound at `(𝔠, 𝔡) = (1/6, 1/10)`, `c₀ = 1/20`).
```
$ (inline python over the three files)   # line:public declarations applied by each `example` block
GUEProcBA.lean  99:BAKFam+BAPB  541:BAKFam  574:gueLprocBA+gueDprocBA+gueLprocBA_nonneg+gueDprocBA_nonneg  586:gueLprocBA_le  589:gueDprocBA_le  592:gueLprocBA_odd  595:gueLprocBA_time  598:gueDprocBA_time  601:gueLprocBA_continuousOn  604:gueDprocBA_continuousOn  610:gueDevBA_succ_le  617:norm_egtNGUEOf_le
GUEHypABA.lean  774:Hyp_Kt_detDomBA  785:gueKproc_detDomBA  796:Hyp_Kt_oneBA  862:gueStopBA+gueDmaxBA+Hyp_gridBA  912:GUEHypABA_hell_of_hell
GUEEntryGridBA.lean  408:map_gueHBA_eq_mixMatBA  413:gueGrid_entry_boundBA
```
Reading: `BAKFam` is nonempty at the flow datum (`gueK_existsBA` per `n`, `GUEProcBA:541`); every `gueLprocBA …` fact, `gueDevBA_succ_le`, `norm_egtNGUEOf_le` (ε the finite supremum of the trace errors, B the finite sum of the cut-loop norms), `Hyp_Kt_detDomBA`, `gueKproc_detDomBA`, `Hyp_Kt_oneBA`, `GUEHypABA_hell_of_hell`, `map_gueHBA_eq_mixMatBA`, `gueGrid_entry_boundBA` is applied with every hypothesis discharged. `Hyp_gridBA` (`GUEHypABA:862`) is applied for every path `ω`, threshold `δ` and primitive family `Kt`, with the constants `c, C_f, C_e, err, g₄` chosen as finite sums of the left sides (as in the band instance `HypAInst`): the constants are independent of `k` and the conclusion holds for every `k ≤ gueStopBA`. `GUEPathBoundsBA` and `BAPB` have no nonempty instance here (it is row c's `gueGrid_pathBoundsBA`); their exact-type example is `GUEProcBA:99`.
**Lines per file (ticket item 1; Amend 2 item 8).**
```
$ wc -l RBM3D/BA/GUEProcBA.lean RBM3D/BA/GUEHypABA.lean RBM3D/BA/GUEEntryGridBA.lean ; census figures from (a)/(a″): pure/wide per file 408/610, 931/1,127, 365/447; row a pure 1,704, wide 2,184, mean 1,944; landing line 2,927 = max(1.67 x 1,704, 1.34 x 2,184); stop lines 1,500 per file, 2,000 binding
645 GUEProcBA.lean; 920 GUEHypABA.lean; 425 GUEEntryGridBA.lean; 1990 total
row a landed 1990: 1.17 x pure, 0.91 x wide, 0.68 x landing line; largest file 920 = 0.46 x the 2,000 line; per file landed/pure-census [1.58, 0.99, 1.16]
```
**Registry and scan (Amend 3 item 4), sibling scan.**
```
$ git diff cabd9a3d...t/T2519 -- RBM3D.lean RBM3D/Test/Axioms.lean | grep '^[+-][^+-]' | cut -c1-110
+import RBM3D.BA.GUEProcBA
+import RBM3D.BA.GUEHypABA
+import RBM3D.BA.GUEEntryGridBA
+   `RBM.BA.GUEPathBoundsBA, -- BA twin of `GUEPathBounds` (T2519 row a, `BA/GUEProcBA`; DECISIONS §344 (4) OQ
$ (inline python) entries of the five lists of `Test/Axioms.lean` on main (identical at cabd9a3d and 66649d46) and on t/T2519
main: borrowed 2, owed 115, structural 142, refuted 7, superseded 19;  t/T2519: borrowed 2, owed 115, structural 143, refuted 7, superseded 19
```
Registered: the new `structuralProps` line `RBM.BA.GUEPathBoundsBA` (first commit; the `:383` `GUEPathBounds` owner comment is row c's). No `owedProps` line is added (expected none). The scan above found 124 premises and no unclassified one; `GUEPathBoundsBA` is in its list "registered premise(s) carry nothing yet" (no theorem of row a takes it as a hypothesis; rows b-d and N2 will). No row-a theorem takes `BAKFam`, `BAPB` or another new `Prop` as a hypothesis. Sibling scan: shared files are `RBM3D.lean` (my three import lines after `BA.GUEEntry2`, lines 656-658) and `Test/Axioms.lean` (my line follows the `GUEPhase.GUEPathBounds` line; T2520 owns `:179`, `:184` and the instance halves of `:168-169`): disjoint lines, union at merge.
**Name-level table (supervisor 0149 `:98`) and coverage as used (Amend 3 item 4).** Upstream names read, `name:line` on this tree (`nametab.py`, first top-level declaration of that name); band twin sources are `main` files last changed at Proc e17d56f8, ProcK ba2ddf39, HypA 9b66b53f, EntryGrid f9f498d1; these are RBM3D files, so no RBM1D/RBM2D port is made here (RBM1D/RBM2D untouched, no `diff --stat` applies); private band helpers read by `open private … from`: 15 (Proc), 12 (ProcK), 6 (HypA), 12 (EntryGrid).
```
BA/GUEOneLoop  gueHBA:58 gueHBA_isHermitian:62 gueHBA_succ:72 ol_gueHBA_eq:85
BA/GUEEntry2  GUEEntry_llErr:48 GUEEntry_maxLoop:55 mixMatBA:448 GUEEntryMixBA:738 gueEntryMixBA:785
BA/GUEKPrim  kTwoGUEBA:634 gueK_existsBA:1015
BA/KBound  baKBoundAt_holds:85
BA/KInduct  BAKBoundAt:55 baKsol_one:77
BA/FlowPins  BAKsol:283 BAMres_fine_apply:102 BAmF:252 BAflowLam0:386 BAflowEs:383 BAflowT0:380 flow_sz0:1214 zSeq:1181
BA/GreenSchur  BAflow_real:59 BAflow_lam0_window:72
BA/Ward  BAm_norm_le_one:136
Loop/GLoopFlow  ztOf:55 etaOf:58 Gres:74 Mres:81 loopOf:117 loopL:123 blockMat:105
Universality/GUEPhase/Generator  mSigOf:62 genMatGUEOf:68 egtNGUEOf:79 loopGenGUEOf:1168
Universality/GUEPhase/Bootstrap  eq736:442 eventually_small:481 primRhsGUE:178
Universality/GUEPhase/Grid  gueH:77 Pgue:61 gueGridK:106 gueH_measurable:205
Universality/GUEPhase/Proc  gueTent:74 gueInterp:78 gueKbar:106 gueKproc:122 gueDev:83 gueDev_succ_le:771 norm_egtNGUE_le:596 gueLproc:112 gueDproc:116
Universality/GUEPhase/ProcK  gueKproc_detDom:553
Universality/GUEPhase/HypA  Hyp_Kt_detDom:690 Hyp_Kt_one:712 Hyp_grid:981 Hyp_Kt_disc:864
Universality/GUEPhase/EntryGrid  map_gueH_eq_mixMat:118 gueGrid_entry_bound:518
```
| ticket coverage row | used in row a as | where |
|---|---|---|
| 1, 16 (`RBG_Prod`, LL, `RBG_Que`; `h1`) | `BAKFam`, `BAPB` have the types of `KF`, `PB` in the three texts (exact-type example); `Hyp_Kt_oneBA` is the `Kt = m` premise (guarded by `0 < g n`) | GUEProcBA:99; GUEHypABA:454 |
| 3 (`gueK_existsBA` → `BAKFam`) | `BAKFam` nonempty at `sz0` | GUEProcBA:541 |
| 6 (`gueHBA`, `gueHBA_succ`) | every process def; `gueDevBA_succ_le` (increment `√(Δ/N) X_{k+1}`) | GUEProcBA |
| 10 (`GUEEntryMixBA`, `mixMatBA`, `GUEEntry_llErr`, `GUEEntry_maxLoop`) | `gueGrid_entry_boundBA` (from `gueEntryMixBA`), `map_gueHBA_eq_mixMatBA` | GUEEntryGridBA |
| 12 (`hKb`) | not a premise: `baKBoundAt_holds` (`BAReal` data, `0 < g ≤ Λ` eventually) gives `K̃` at `t₁`; no `BAFlow`, no `STKboundgL` | GUEHypABA `HypABA_initial` |
| 13, 14 (flow datum, windows) | statements at `(g, E, m)`; window eventual in `Hyp_Kt_detDomBA`, `gueKproc_detDomBA`, `Hyp_Kt_oneBA`; `∀ n` in `gueGrid_entry_boundBA` (text of `GUEEntryMixBA`) | see (d) 1 |
| 15 (local law against `M`) | `gueDevBA`, `GUEPathBoundsBA.localLaw`, `gueGrid_entry_boundBA` are against `Mres (g Ψ_I) E m`; `norm_egtNGUEOf_le` uses only `tr (G E_a) - m(σ)` (the diagonal) | GUEProcBA, GUEEntryGridBA |
| 18 (premises of `T2517_OneStepBA`: 2-loop bound of `Kt`) | `Hyp_Kt_detDomBA` (pointwise), `gueKproc_detDomBA` (interpolated) | GUEHypABA |
| 19 (grid layer read at `sz.withLam 0`) | `Pgue`, `PathΩ`, `gueH` only at `(sz.withLam 0)` in the 27 public statements (C1 script: 0 hits) | all three |
| 21 (T4, T5) | not read; rows 2, 4, 5, 7-9, 11, 17, 20 are other rows' | n/a |
**Narrative (row a; no stop rule of the ticket or of Amends 1-3 was hit).**
1. Row a is delivered in three BA leaves, 1990 `wc -l` (0.68 of the landing line 2,927, largest file 920): `BA/GUEProcBA` (targets 1, 2), `BA/GUEHypABA` (3), `BA/GUEEntryGridBA` (4). No merged file is edited; the shared edits are three import lines and one registry line.
2. Target 1 (first commit, `19df37e2`): `GUEPathBoundsBA`, `BAKFam`, `BAPB` are `def … : Prop` with the bodies of the signed `T2519_PathBoundsBA`, `T2519_KFamBA`, `T2519_PBBA` (Amend 1 item 1: `n₀ = 4`, `gueGridK sz 4`, lengths `≤ 4 * 4`); token diff IDENTICAL and `rfl` against the probe's definitions. The registry line was added in the same commit.
3. Target 2: the band proofs of `Proc` are copied with `gueH ↦ gueHBA`, `zt (E n) ↦ ztOf (m n) (E n)`, `etaT ↦ etaOf (m n)` and the centre `mE E • 1 ↦ Mres (g Ψ_I) E m`; the loop length is `l` (`m` is the flow's complex family). `norm_egtNGUEOf_le` is proved through the generic `egtNGUEOf` with the trace error `tr (G(σ) E_a) - m(σ)`; `gueDevBA_succ_le` uses `‖z' - z‖ = Δ ‖m‖ ≤ Δ` (`‖m‖ ≤ 1`, `BAm_norm_le_one`): the centre `M` does not move with the grid, so the jump is the band one.
4. Target 3. **(i) No pin `hKb`**: the 1a booked `hKb` from `STKboundgL` under `BAFlow` with padding (≈ 40 lines). The per-`n` deterministic core `baKBoundAt_holds` (`|𝒦^{(k)}| ≤ C L^τ (W^{-d} B_{t,0}(g))^{k-1}` for `BAReal` data, `0 < g ≤ Λ`) gives `K̃` at `t₁` directly (`HypABA_initial`), so the K lemmas need `0 < g n ≤ Λ` only **eventually** and no `BAFlow`, no padding. **(ii)** `hell : L^d (1 - t₁) ≤ 2 g²` (constant 2); `GUEHypABA_hell_of_hell` derives it from the RBG premises `L^d (1 - t₁) ≤ λ²`, `L^d (1 - t₁) ≤ 1` (`t₀ ≥ t₁ ≥ 26/27`). **(iii)** `Hyp_Kt_detDomBA` concludes, at `n₀ = 4`, exactly the probe's `hKdet` (checked in Lean, `chain.lean`); `Hyp_Kt_oneBA` is the guarded `Kt = m` premise; `gueKproc_detDomBA` is the interpolated form (the unused band `hscale` is not carried); `Hyp_gridBA` replaces the band split `Hyp_genMat_split` by the generic `loopGenGUEOf` (every loop length, no `3 ≤ L`, `0 < Im m` for `|E| < 2`); it does not need the band's `ht1 : 0 ≤ t1 n` and `hm : 1 ≤ m` (they fed `Hyp_genMat_split`).
5. Target 4: `map_gueHBA_eq_mixMatBA` is the band theorem at `sz.withLam 0` pushed through the translation by `g Ψ_I` (text `T2519_MapMixBA`, checked by an `example` against the restated text, `signed.lean`). `gueGrid_entry_boundBA` follows `gueGrid_entry_bound`: bad set in matrix space for `GUEEntry_llErr`, `GUEEntry_maxLoop`, measurability, grid union over `K + 1 ≤ N^{64 n₀ + 128}` points, zero time (`g Ψ_I`, error `0`). Its family premise is the one of C3 b's `GUEEntryMixBA`: `∀ n, 0 < g n ≤ 𝔡⁻¹ ∧ BAReal …` (see (d) 1).
6. Instances: `sz0` flow datum; the window of the K lemmas is `1 - t₀ = x_n`, `t₀ - t₁ = x_n/(2N_n)`, `x_n = λ_n²/(4 L_n³)` (positive length; `t₀ ≥ 1/4` and `Im m ≥ 1/2` along the flow give `hell`, `h730` for every `n`); `Hyp_gridBA` is applied for every `ω`, `δ`, `Kt` with finite-sum constants, every hypothesis discharged.
7. Not used: `BA/TwistAvg*` (no name read), V modules; `BA.TwistPins` is not in the closure of row a. Private band helpers are read by `open private` (45 names), none copied a third time; helpers of mine are `private` or prefixed `GUEHypABA_`.

## (c) Verified Mathlib names (all compile in the three files; `#check @name` exit 0 in the final tree; none checked absent)
Used and verified present (60): Complex.im_le_norm, Complex.norm_natCast, Complex.norm_real, Finset.Icc_eq_empty, Finset.card_range, Finset.card_univ, Finset.le_sup'_of_le, Finset.measurable_sup', Finset.mem_Icc, Finset.mem_range, Finset.single_le_sum, Finset.sum_const, Finset.sum_le_sum, Finset.sum_nonneg, Finset.sup'_apply, Finset.sup'_le, Fintype.card_fin, Matrix.nonsing_inv_eq_ringInverse, Matrix.sub_apply, Measurable.ite, MeasurableSet.iInter, MeasurableSet.iUnion, Measure.map_apply, Measure.map_map, Nat.card_Icc, Nat.one_le_iff_ne_zero, Real.iSup_le, Real.iSup_nonneg, Real.rpow_add, Real.rpow_le_one_of_one_le_of_nonpos, Real.rpow_le_rpow_of_exponent_le, Real.rpow_neg_one, Real.rpow_nonneg, Real.rpow_pos_of_pos, Real.sq_sqrt, Real.sqrt_nonneg, Real.sqrt_pos, Set.Finite.bddAbove, Set.finite_range, Set.indicator_of_mem, Set.indicator_of_notMem, ciSup_le, continuousOn_const, div_le_iff₀, inv_anti₀, inv_le_one_of_one_le₀, le_ciSup, le_div_iff₀, measurableSet_le, measurableSet_lt, measure_empty, measure_iUnion_fintype_le, measure_mono, norm_image_sub_le_of_norm_deriv_le_segment', norm_sum_le, nsmul_eq_mul, one_le_pow₀, pow_le_pow_left₀, pow_le_pow_right₀, tendsto_natCast_atTop_iff.

## (d) Open issues and paper-delta candidates
1. **Window padding is not done in row a, by the text of the merged inputs.** `GUEEntryMixBA` (C3 b) takes `∀ n, 0 < g n ≤ 𝔡⁻¹` and `gueGrid_expect_oneLoopBA` (C4 a) `∀ n, 0 < g n ≤ Λ`; the BA producers have the window only eventually (`Sizes.lam` is unsigned). Row a's K lemmas are eventual; only `gueGrid_entry_boundBA` carries the `∀ n` window. A consumer must apply the entry bound and `gueGrid_expect_oneLoopBA` to the shifted sizes `sz.comp (· + n₀)` (`Sizes.comp_admissible`, the precedent of `MainIndOutBA:138`) or supply an eventually equal valid datum; the shift needs a transfer of `StochDomAt (Pgue …)` along `Sizes.reindex` (`Induction/SizesComp` has the exact image law for `seqP`; I found none for `Pgue`), the second way an existence lemma of valid `BAReal` data at every `L ≥ 3` and margin `κ`. Not in the ticket's row-a targets; owner and price for the dispatcher (rows c, d, N2).
2. Report length: sections (a), (a′), (a″) written by earlier stages take 262 lines (before this section); with (b)-(d) the file is over the 300 of CLAUDE.md §6 and the 250 of the ticket; those sections are not mine to shorten.
3. For rows c, d: `Hyp_Kt_detDomBA`, `gueKproc_detDomBA`, `Hyp_Kt_oneBA` take `hr : ∀ n, BAReal …`, `hlam` (eventual), `hKinit`, `hK` as the clauses of `BAKFam` (`0 < g n →`, lengths `≤ 4 * n₀`) and `hell` in the `2 g²` form (`GUEHypABA_hell_of_hell`, needs `hell1`). `GUEPathBoundsBA` is a conjunction (`.1` is `lk`, `.2` is `localLaw`), as signed.
4. `GUEPathBoundsBA` carries nothing in the premise scan until rows b-d/N2 use it; the `:383` owner comment and the `UNOULLk`, `UNG1Rowk`, `UNOUQUEk` comments stay with rows c, d.
5. Paper-delta candidates (tags of row a; the dispatcher numbers them): **`T2519b`** the grid local law against `M^{(B)} ⊗ 1` (`GUEPathBoundsBA.localLaw`, `gueDevBA`, `gueGrid_entry_boundBA`), the paper's GUE phase having `‖G - m‖_max`; **`T2519c`** positivity: `0 < g n` only eventually in the K lemmas (the guard of `BAKFam`), `∀ n` in the entry bound; **`T2519e`** the zero-mode regime at BA is `L^d (1 - t₁) ≤ 2 g²` with `g = λ₀` (from `L^d (1 - t₁) ≤ λ²`, `≤ 1`); **`T2519f`** the grid-step jump of `z_u` is `Δ‖m‖ ≤ Δ` (`‖m‖ ≤ 1`) where the band has `Δ`.
