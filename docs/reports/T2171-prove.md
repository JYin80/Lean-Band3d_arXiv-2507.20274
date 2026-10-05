Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 04:27:04 UTC 2026

Scripts: `cd $SP` with `SP=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2171` (`tok.py consts.py rows.py geom.py limit.py zero.py loops.py cons.py`). Notation as in the ticket; `d = 3` numbers; `ℓ_u = 1` (`lam² ≤ 1−u` ⇒ `max(lam/√(1−u),1) = 1 ≤ L`).

### (i) Exponent table
| # | quantity | value / derivation | constraint | slack |
|---|---|---|---|---|
| 1 | `d=2` tokens → `d≥3` | `Z2→Zd d L`, `zdist2→zdistInf d L`, `(W:ℝ)^2→(W:ℝ)^d`, `scaleM→W^d(1−u)=M_u`, `etaT` dropped, `ellT=1`, `ellStar…v→(log W)^{3/2}` (`v=u`), `tailT…v→tailTD d W u D`, `L²W¹²→P=L^dW^{6d}`, `25→9^d` (1 hit, `edge_u` `:442`), `50→2·9^d`, `200→3^{d+1}`, `(2R+1)²→(2R+1)^d` (0 hits here; `count_le` is in part 2), `BlockIndex→Vtx d L W`, `EE→STeeM` | script count below | — |
| 2a | floor | `P² ≤ W^D` ⇒ `W^{-D} ≤ P^{-2}` (`wD_le`) and `L^dW^{2d} ≤ W^D` (`P² ≥ L^dW^{2d}`) | `log P ≥ 6d log W ≥ 72` | (a) `2^378≤2^380` (2 bits); (b) `2^1007.55≤2^1008` (0.45 bit) |
| 2b | `ℓ**=4(log P)²` | `ℓ*/8+2 ≤ ℓ**`; `√(ℓ**−2) ≥ 2log P−1`; `T(ℓ**−2) ≤ (e+1)P^{-2} ≤ 4P^{-2}` (`M_u ≥ 1`, `W^{-D} ≤ P^{-2}`) | `(e+1) ≤ 4` | `P²T(ℓ**−2)`: 0.25 (a), 0.73 (b) vs 4 |
| 2c | long edge, block dist `>ℓ**` | `‖G_pq‖² ≤ 9^dΛ(W^{-D}+J T) ≤ 2·9^dΛJ·4P^{-2} = 8·9^d ΛJ P^{-2} ≤ (3^{d+1}ΛJP^{-1})²`; `c_long=3^{d+1}=81`; `c_near=(2Λ)^5·c_long/Λ⁵=32·3^{d+1}=2592` (RBM2D `32·200`) | `8·9^d ≤ 9^{d+1}`, `ΛJ ≥ 1` | factor 1.125 on the square |
| 3a | far edge (e7) | `‖G_pq‖² ≤ c_e ΛJ T(r−2)`, `c_e=2·9^d=1458` (`W^{-D} ≤ T ≤ JT`) | needs `r ≥ ℓ*/8+2` | — |
| 3b | shift | `T(y) ≤ S T(x)` for `y ≥ x−4−4ℓ*`, `S=e²e^{2Y}` (`LemDecCalE_tailT_anti`, `_tailT_shift` `c=4`, `_e4c` `C=4`); `S`=3.8e4 (a), 1.06e8 (b) | `W ≥ 1` | random check max `T(y)/(S T(x))`=0.13/0.12 |
| 3c | four-loop | `√(ΛM_u^{-3}) ≤ ΛM_u^{-3/2}` (`Λ ≥ 1`); pin target 4 with `Λ*((W^d(1−u))⁻¹)^(3/2:ℝ)` so `LemDecCalE_e1_rpow` (`a=3/2`) applies | `Λ ≥ 1` | — |
| 4 | general `σ` | loop `tr(A E₁ C E₂ A E₃ Aᴴ E₄ Cᴴ E₅ Aᴴ E₆)`, `A=G(σ₀)`,`C=G(σ₁)`; `=tr(E₁·mid·E₅·X)`, `mid=C E₂ A E₃ Aᴴ E₄ Cᴴ` (pointwise only), `X=AᴴE₆A` Hermitian; rotation by 3 = same pattern with `σ→σ̄`, glue `A E₃ Aᴴ`; CS four-loop `tr(E₁XE₅X)` signs `(σ₀,σ̄₀,σ₀,σ̄₀)` real `≥0`. Edges: `C_{x₁x₂}`,`Cᴴ_{x₄x₅}` paired by AM–GM (both signs obey (e7)); `A_{x₂x₃}`,`Aᴴ_{x₃x₄}`; `Aᴴ_{x₅x₆}`,`A_{x₆x₁}`. `k=1,2` cut index lists checked vs `STeeLoop` (Step34Pins:152) for general `a'` | numeric below | — |
| 5 | label geometry | `cut_far` cases `(1a)(1b)(2a)(2b)` verbatim from RBM2D at `L^∞`: every edge used has dist `≥ ℓ*/8+2` and `≥ x−2−4ℓ*`, shift `bA ≥ d−4−4ℓ*` | `ℓ* ≥ 8` (`log W ≥ 4`), `|A₁−A₂| > 4ℓ*` | 0 violations in 199979 tuples (below) |
| 6 | constants, both parts | rows `N1,N2,F1,F2` below; `κ_dif(d)=729^d` | each row `≤ lossE2dif=lossE2·κ_dif·(1+log P)^{2d}` | `κ=1` already passes: scan d=3..60 has min `log10(lossE2dif/row)` = 21.0, attained at d=3, L=3, log W=4 |
| 7 | consumer | §Consumer below | — | floor missing |

Row 6 chain (Σ_{b'}|SB|=1, `W^dM_u^{-a}=(1−u)^{-1}M_u^{1−a}`, `W^dM_u^{-2}=(1−u)^{-1}M_u^{-1}`):
- Near (`|a₁−a₂| ≤ 4ℓ*`): `‖STeeM‖ ≤ W^dΣ_b[ΛM^{-5}(1(|a₀−b|≤ℓ**)+1(|a₁−b|≤ℓ**))+2c_nearΛ⁶JP⁻¹]`. `(2ℓ**+1)^d ≤ 9^d(log P)^{2d}`; `M^{-4} ≤ e^{4Y}T²` (`√(4ℓ*)=2Y`): `N1 = 2·9^dΛ(log P)^{2d}e^{4Y}`. Long-edge term `=2c_nearΛ⁶J W^{-5d}`; `(1−u)^{-1}M^{-9/2} = W^dM^{-11/2} ≥ W^{-9d/2}` (`M ≤ W^d`) and `J ≤ J³`, so it sits under `(1−u)^{-1}M^{-1/2}J³T²e^{-4Y}`: `N2 = 2c_nearΛ⁶e^{4Y}`. **No `J ≤ W` is used** (RBM2D `near_far_small` `:1167` needs it because `L²W¹²` is too small; here `W^dL^d/P=W^{-5d}`).
- Far: `F1 = 8(2ℓ*+3)^d c_e²Λ³S³` (counts: 4 indicators×`(2(ℓ*+1)+1)^d`×2 cuts; `J² ≤ J³`; `(2ℓ*+3)^d ≤ 3^d(log W)^{3d/2} ≤ 3^d(1+log P)^{2d}`); `F2 = 2c_e³(2S_d+1)Λ³S³`, `S_d=(1+1536d⁴)^d` (`LemDecCalE_sum_tail_tail`, `floor_A`; `M^{-1} ≤ M^{-1/2}`).
- `lossE2` carries `10¹²(1600d⁴)^dΛ⁶(1+log(L^dW^{2d}))⁴(1+log W)³e^{8Y}`; `κ_dif=729^d=(c_e/2)³` makes `F2 ≤ lossE2dif` follow from `2S_d+1 ≤ 3(1600d⁴)^d` and `48e⁶ ≤ 10¹²` (no `(1+24d)^{2d} ≥ 729^d` step).

### (ii) Concrete nondegenerate instance
```
$ python3 tok.py
RBM2D LemDecCalEdif.lean:1-1031 @c9a24cf, tokens/lines:
Z2 35/32; zdist2 84/72; (W : R) ^ 2 3/3; scaleM 15/15; etaT 3/3; ellT 47/32; ellStar..v 24/22; tailT..v 72/49; L^2*W^12 11/11; 25 1/1; 50 12/12; 200 12/11; (2R+1)^2 0/0; BlockIndex 76/54; greenBlk 80/48; EE (Step2Vocab) 7/7
$ python3 consts.py
Im m(1/2)=0.968246 (Im m)^-6=1.2136 |m|^2=1.000000
(a) sz0 n=1 d=3 L=8 log2W=10.00 lam=0.0002441 D=38: log2 P^2=378.0000 <= log2 W^D=380; premises 12, failing []
   logW=6.931 l*=18.249 4l*=72.996 Y=4.272 S=3.794e+04 logP=131.00 l**=6.865e+04 l*/8+2=4.281
(b) szCL n=0 d=3 L=15925248 log2W=24.00 lam=1 D=42: log2 P^2=1007.5489 <= log2 W^D=1008; premises 12, failing []
   logW=16.636 l*=67.851 4l*=271.403 Y=8.237 S=1.055e+08 logP=349.19 l**=4.877e+05 l*/8+2=10.481
(e): |A1-A2|=300 > 4l*=271.403; L/2=7962624 > 300
d=3: c_e=2*9^d=1458  c_long=3^(d+1)=81  c_near=32*3^(d+1)=2592  (RBM2D: 50, 200, 32*200)
extreme   kappa=1     log10 lossE2dif=56.4; log10(lossE2dif/row): near1=37.0 near2=47.7 far1=35.3 far2=21.0
extreme   kappa=729^d log10 lossE2dif=65.0; log10(lossE2dif/row): near1=45.6 near2=56.3 far1=43.9 far2=29.6
(a)       kappa=1     log10 lossE2dif=64.4; log10(lossE2dif/row): near1=41.1 near2=53.2 far1=38.6 far2=25.2
(a)       kappa=729^d log10 lossE2dif=72.9; log10(lossE2dif/row): near1=49.7 near2=61.8 far1=47.2 far2=33.8
(b)       kappa=1     log10 lossE2dif=83.7; log10(lossE2dif/row): near1=50.9 near2=65.6 far1=45.9 far2=34.2
(b)       kappa=729^d log10 lossE2dif=92.3; log10(lossE2dif/row): near1=59.5 near2=74.2 far1=54.5 far2=42.8
scan d=3..60, L in {3,1e3,1e9}, log W in [4,1e5]: min log10(loss/row): kappa=1 -> (21.01, (3, 3, 4.0)) ; kappa=729^d -> (29.6, (3, 3, 4.0))
$ python3 zero.py     # M=0,u=0: G_0=mI, loops of E2HypDif clauses 4,6 exactly (W^d=8 torus d=3,L=3)
m(m+E)=0.000e+00  |m|=1.000000  G_0=(0-z)^-1 equals m: 1.24e-16
M=0,u=0 (W^d=8): max_sigma,c |L^(k)(c,..,c)| * W^{d(k-1)} = 1.000000000000 (k=4), 1.000000000000 (k=6) (Lam=1 suffices); max |L^(k)| at distinct labels = 0.0e+00, 0.0e+00
$ python3 limit.py   # external-type premise (floor) along the two sequences, exact integers
sz0  (L=4(n+1), W=(2(n+1))^5, D=38): floor fails at n in [0] ; holds for 1<=n<=3000. Closed form: P^2/W^D=64/(2(n+1))^4 (n=1: 1/4)
szCL (L=2(n+24)^5, W=2^(n+24), D=42): floor fails at n in [] ; holds for 0<=n<=3000. P^2/W^D = 64 m^30 2^(-6m), m=n+24 (decreasing for m>=8)
$ python3 rows.py   # rows 2b, 2c, 3b, 6, Bctl
(a) log P=131.005 >= 6d log W=124.766:True | l*/8+2=4.281 <= l**=68649.0:True | sqrt(l**-2)=262.006 >= 2logP-1=261.010:True
   P^2 W^-D = 2.500e-01 <= 1: True ; P^2 T(l**-2) = 0.2500 <= 4 (worst Mu=1 gives e+1=3.7183)
   shift T(y)<=S T(x), y>=x-4-4l*: max T(y)/(S T(x)) over 20000 draws = 1.292e-01 (<=1); S=3.794e+04
   counts: (2l**+1)^d <= 9^d Lg^2d: True ; (2l*+3)^d = 6.162e+04 ; W^d L^d/P = W^-5d = 2^-150.0 <= W^(-9d/2) = 2^-135.0
(b) log P=349.190 >= 6d log W=299.440:True | l*/8+2=10.481 <= l**=487734.2:True | sqrt(l**-2)=698.378 >= 2logP-1=697.380:True
   P^2 W^-D = 7.315e-01 <= 1: True ; P^2 T(l**-2) = 0.7315 <= 4 (worst Mu=1 gives e+1=3.7183)
   shift T(y)<=S T(x), y>=x-4-4l*: max T(y)/(S T(x)) over 20000 draws = 1.180e-01 (<=1); S=1.055e+08
   counts: (2l**+1)^d <= 9^d Lg^2d: True ; (2l*+3)^d = 2.668e+06 ; W^d L^d/P = W^-5d = 2^-360.0 <= W^(-9d/2) = 2^-324.0
long edge: |G|^2 <= 2*9^d Lam J *4 P^-2 = 8*9^d (LamJ) P^-2 <= (3^(d+1) LamJ P^-1)^2 needs 8*9^d<=9^(d+1)*1: True ; c_near=32*3^(d+1)=2592
Bctl: Bparam(K=0)=(lam^2+1-u)^-1+(L^d(1-u))^-1 <= (1+1/27)/(1-u) <= 2/(1-u): True
$ python3 geom.py
L^inf geometry of cut_far at d=3 (W=2^24: l*=67.85, l*/8+2=10.48), 199979 random far label tuples: sub-case counts {'1a': 63196, '1b': 70065, '2a': 427, '2b': 66291}; tuples violating an edge precondition: 0
$ python3 loops.py 7   # d=3, L=7, W=2 (N=2744), random Hermitian M with block variances SB/W^d, E=.5, u=.3, lam=.8
d=3 L=7 W=2 N=2744  E=0.50 u=0.30 lam=0.80  Mu=W^d(1-u)=5.600  ||G-(-)^H||=7.45e-15  ellT=1.000
target 2 index identity (2000 random sigma,a,a',b,b'): True
target 2: |STeeM| <= W^d sum|SB|(|L6 s0s1|+|L6 s1s0|): max lhs/rhs over 24 (sigma,a) = 0.1716 (<=1)
Lambda candidates: e6 0.802  avg 1.964  gex 0.037  L4(sampled) 0.174  L6(sampled) 0.072  -> Lambda=1.964
l*=0.577 4l*=2.308 thr l*/8+2=2.072; J_e (e7-consequence, pairs with dist>=thr; diam=3)=1.0000
P=L^d W^6d=8.992e+07, l**=4(log P)^2=1341.7 (> diam: indicator is always 1 on this torus)
target 3 (near): max |L6|/RHS over 12000 random tuples, all 4 sign pairs = 0.0000
general-sigma chain (1200 tuples incl. s0=s1): |L6|<=alpha*beta and <=alpha*sqrt|L4| both hold: True; max ratios pt 0.000 cs 0.002; min Re L4=2.11e-16, max |Im L4|=4.0e-21
target 4 (far): 9604 tuples, max |L6|/RHS = 2.002e-19 ; on the 4464 tuples whose six edges all have dist>=l*/8+2: max = 1.775e-24
```
The random-`M` run is a structure test (Λ from entries/avg/gex/sampled loops, `J_e` from the (e7) consequence only, since `K` is not computable for random `M`); at `L=7` the tests of targets 3–4 have huge slack (constants `c_near, c_e, S`), `ℓ**=1341.7` exceeds the diameter so the near indicator is always 1; they check the general-`σ` chain, not the sharp constants.

Instances (all premises of every target hold at once; `Λ₀=1` suffices by `zero.py`, `Λ₀=2` also via `norm_gloop_le_of_le_abs_im`, `(Im m)^{-6}=1.21`):
- (a) `E2HypDif sz0 1 (1/2) 0 38 Λ₀ 1 1 0`: `d=3, L=8, W=1024, lam=1/4096`, `M=0`, `u=0`, `M_u=W³=2^30`, `lam²W^d=64≥1`, `log W=6.93≥4`, floors `2^69≤2^380`, `2^378≤2^380`; entry/avg/gex clauses exact at `G=mI`; `K=W^{-d}δ_ab`, `LK=0` (T2164 (ii)); four/six-loop clauses `=W^{-d(k-1)}` (`zero.py`).
- (b) `E2HypDif szCL 0 (1/2) 0 42 Λ₀ 1 1 0`: `L=2·24⁵`, `W=2^24`, `lam=1`, `lam²=1≤1−u`, `lam²W^d=2^72`, `log W=16.64`; floor `2^{1007.55}≤2^{1008}`; the floor holds at `D=42` for `0≤n≤3000` (exact integers, `limit.py`; the ratio `64m³⁰2^{-6m}` decreases for `m ≥ 8`).
- (c) `LemDecCalEdif_STeeM_le` at (a), `σ=![true,true]`, `a=a'=![0, Pi.single 0 1]`: no hypothesis (identity-type triangle bound).
- (d) `LemDecCalEdif_cut_near` at (a), `σ₀=σ₁=true`: hypothesis = (a); both branches consistent: at `M=0` the loop is `W^{-15}=M_u^{-5}` iff all labels equal (indicator 1).
- (e) `LemDecCalEdif_cut_far` at (b), `σ₀=true,σ₁=false`, `A₁=A₁'=B=B'=0`, `A₂=A₂'=Pi.single 0 300`: `|A₁−A₁'|=|A₂−A₂'|=0≤ℓ*`, `|B−B'|=0≤1`, `4ℓ*=271.4<300<L/2`; right side `>0` (`T(300)=M^{-2}e^{-√300}+W^{-D}>0`, `S,Λ,J,c_e>0`).
- Target 5 premises: `3≤d, |E|<2, 0<lam, lam²≤1, 1≤lam²W^d, 1≤Λ,K₀,J≤W, 4≤log W`, floor `P²≤W^D` (both instances, row 2a) ⇒ `L^dW^{2d}≤W^D`.
- External-hypothesis limit computation (loop clauses ← `STLmaxU`): `Bparam(K=0)=(lam²+1−u)^{-1}+(L^d(1−u))^{-1} ≤ (1+1/27)/(1−u) ≤ 2/(1−u)` (`lam²≥0`, `L^d≥27`) ⇒ `Bctl n u = W^{-d}Bparam ≤ 2M_u^{-1}`, `Bctl^{k-1} ≤ 2^{k-1}M_u^{-(k-1)}`; `Λ` absorbs `2^5N^ε`. The floor is not implied by the pin (below); its limit along `sz0, szCL` is in `limit.py` above.

### Consumer check (§45 O2; right side vs `Step5Pins.lean:178-186` and paper `3_5:2327-2334`)
```
$ python3 cons.py
Step5Pins.lean:178-186 right side (u:=q.1.1.1, a:=q.1.1.2.2, Jst n u D:=J) == check-file shape right side after "loss *": True
pin range conjunct '(zdistInf d (sz.L n) (q.1.2.2 i - q.2 i)) <= log W^(3/2)' present: True | shape has (a i - a' i): True
$ grep -nE "\bhJ\b|hJW|≤ W :=" (RBM2D LemDecCalEdif.lean:1-1031): 0 uses of J ≤ W (only line 358 `1 ≤ W`); part 2 (1032-1691): 1 use (`near_far_small`, line 1167); RBM3D LemDecCalE.lean: `hJW` 7 hits = 5 destructuring patterns (:792,:930,:949,:1084,:1154), the hypothesis :1326, the witness :1332; no term use.
```
Paper `3_5:2327-2334` (`res_deccalE_dif`): `(1−u)^{-1}[1(|a₁−a₂|≤4(log W)^{3/2}) + (W^d|1−u|)^{-1/2}(J*)³]` after dividing by `T²_{u,D}`: same as the pin (`Jst` rpow `3`).
| new premise | `STIngR5` source | status |
|---|---|---|
| four-/six-loop bounds, all `σ,a` | `STLmaxU` (`Step5Pins.lean:91`, def `Step34Pins.lean:176`) at `k=4,6` with `Bctl ≤ 2M_u^{-1}` | ok (`Λ=2⁵N^ε`) |
| floor `(L^dW^{6d})² ≤ W^D` | pin gives only `∀ᶠ n, size n ≤ W^D` (`Step5Pins.lean:163`) | **missing** (needs `W^D ≥ N²W^{10d}`; extends T2164 M1) |
| `E2Hyp` `GijGEX` conjunct | not an `STIngR5` hypothesis (T2164 M2) | **missing** |
| `E2Hyp` `J ≤ W` | `Jst ≥ 1` only (T2164 M3); still a conjunct of `E2HypDif` (inherited), unused by the proofs of parts 1–2 | **missing** |

### Verdicts
- Target 1 (`E2HypDif`, `lossE2dif`, `LemDecCalE_dif`; `κ_dif d = 729^d`, `κ=1` also passes): **PASS**.
- Target 2 (`LemDecCalEdif_STeeM_le`, every `σ`, `a'`): **PASS**.
- Target 3 (`cut_near`, `c_near=32·3^{d+1}`, every `σ₀,σ₁`): **PASS**.
- Target 4 (`cut_far`, `c_e=2·9^d`, `S=e²e^{2Y}`): **PASS** (pin the four-loop factor as `Λ*((W^d(1−u))⁻¹)^(3/2:ℝ)`).
- Target 5 (`LemDecCalEdif_hyp_zero`): **PASS** (`Λ₀=1` exact route).
- Part 2 (S5-07) constant chain closes without `J ≤ W` (row 6). Flags for S5-09 (not blocking stage 1b): floor, `GijGEX`, `J ≤ W` missing as above.

## (b) Script output (stage 1b) — Mon Oct  5 04:55:30 UTC 2026

Commands: `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2171/evidence.sh`
(`evidence.txt`, run at the `date -u` on its first line; scripts `verify.py`, `stmts.py`, `precheck.lean`, `axioms.lean`, `names.lean` in the same directory).
```
$ date -u
Mon Oct  5 04:53:31 UTC 2026
$ git log -1 --format="%h %s" t/T2171; git merge-base main t/T2171; git rev-parse --short main; git diff --stat main...t/T2171
a86773c Jun Yin <321276894+JYin80@users.noreply.github.com> T2171: S5-06 res_deccalE_dif part 1 (Path/LemDecCalEdif)
cc96b69
f8ad4b4
 RBM3D/Path/LemDecCalEdif.lean | 1643 +++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1643 insertions(+)
$ touch RBM3D/Path/LemDecCalEdif.lean; lake build RBM3D.Path.LemDecCalEdif 2>&1 | tail -3; (warnings/errors mentioning the file)
Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (3817 jobs).
lines mentioning LemDecCalEdif.lean:W/E = 0
$ lake build   (whole library; the root import of the new module is added by the hub at merge)
Build completed successfully (3942 jobs).
exit=0
$ lake env lean precheck.lean   # import RBM3D + RBM3D.Path.LemDecCalEdif; #assert_rbm_axioms
exit=0
axiom audit: 5103 theorems, 1762 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
lines naming E2Hyp*, lossE2dif, LemDecCalE_dif in the registry output: 0
$ #print axioms (new public declarations)
'RBM.Path.E2HypDif' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.lossE2dif' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.LemDecCalE_dif' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.LemDecCalEdif_STeeM_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.LemDecCalEdif_cut_near' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.LemDecCalEdif_cut_far' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.LemDecCalEdif_hyp_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.LemDecCalEdif_inst_a' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.LemDecCalEdif_inst_b' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Path/LemDecCalEdif.lean | wc -l
       0
    1643 RBM3D/Path/LemDecCalEdif.lean
$ python3 verify.py   # pinned text vs file
E2HypDif def text (check file section 2 vs RBM3D/Path/LemDecCalEdif.lean) identical modulo whitespace: True
LemDecCalE_dif body == LemDecCalE_difShape body with `loss` replaced by `lossE2dif`: True
lossE2dif := := lossE2 d L W Λ K₀ * ((729 : ℝ) ^ d * (1 + Real.log ((L : ℝ) ^ d * (W : ℝ) ^ (6 * d))) ^ (2 * d))
Step5Pins.lean:178-186 right side (u:=q.1.1.1, a:=q.1.1.2.2, Jst n u D:=J) == right side of LemDecCalE_dif after the loss: True
range hypothesis of the pin present in LemDecCalE_dif: True
$ python3 stmts.py   # statements extracted from the file (whitespace collapsed)
L1155: theorem LemDecCalEdif_STeeM_le (sz : Sizes d) (n : ℕ) (E u : ℝ) (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)) : ‖STeeM sz n E u M σ a a'‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d * ∑ b : Zd d (sz.L n), ∑ b' : Zd d (sz.L n), ‖SB d (sz.L n) (sz.lam n) b b'‖ * (‖STLM sz n E u M ![σ 0, σ 1, σ 0, !σ 0, !σ 1, !σ 0] ![a 0, a 1, b', a' 1, a' 0, b]‖ + ‖STLM sz n E u M ![σ 1, σ 0, σ 1, !σ 1, !σ 0, !σ 1] ![a 1, a 0, b', a' 0, a' 1, b]‖) := by

L688: theorem LemDecCalEdif_cut_near (h : E2HypDif sz n E u D Λ K₀ J M) (σ₀ σ₁ : Bool) (A₁ A₂ A₁' A₂' B B' : Zd d (sz.L n)) : ‖STLM sz n E u M ![σ₀, σ₁, σ₀, !σ₀, !σ₁, !σ₀] ![A₁, A₂, B', A₂', A₁', B]‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 5 * (if (zdistInf d (sz.L n) (A₁ - B) : ℝ) ≤ 4 * Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 then 1 else 0) + 32 * 3 ^ (d + 1) * Λ ^ 6 * J * (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d))⁻¹ := by

L873: theorem LemDecCalEdif_cut_far (h : E2HypDif sz n E u D Λ K₀ J M) (σ₀ σ₁ : Bool) (A₁ A₂ A₁' A₂' B B' : Zd d (sz.L n)) (h1 : (zdistInf d (sz.L n) (A₁ - A₁') : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2)) (h2 : (zdistInf d (sz.L n) (A₂ - A₂') : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2)) (hB : (zdistInf d (sz.L n) (B - B') : ℝ) ≤ 1) (hd : 4 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) < (zdistInf d (sz.L n) (A₁ - A₂) : ℝ)) : ‖STLM sz n E u M ![σ₀, σ₁, σ₀, !σ₀, !σ₁, !σ₀] ![A₁, A₂, B', A₂', A₁', B]‖ ≤ (2 * 9 ^ d * Λ * J) ^ 2 * (Real.exp 2 * Real.exp (2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4))) ^ 3 * tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (A₁ - A₂) : ℝ) ^ 2 * (Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ ((3 : ℝ) / 2)) * ((if (zdistInf d (sz.L n) (A₁ - B) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) + 1 then 1 else 0) + (if (zdistInf d (sz.L n) (A₁' - B) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) + 1 then 1 else 0) + (if (zdistInf d (sz.L n) (A₂ - B) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) + 1 then 1 else 0) + (if (zdistInf d (sz.L n) (A₂' - B) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) + 1 then 1 else 0)) + (2 * 9 ^ d * Λ * J) ^ 3 * (Real.exp 2 * Real.exp (2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4))) ^ 3 * tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (A₁ - A₂) : ℝ) * tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (A₁ - B) : ℝ) * tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (B - A₂) : ℝ) := by

L1354: theorem LemDecCalEdif_hyp_zero (sz : Sizes d) (n : ℕ) {E D Λ K₀ J : ℝ} (hd : 3 ≤ d) (hE : |E| < 2) (hlam : 0 < sz.lam n) (hlam1 : sz.lam n ^ 2 ≤ 1) (hlamW : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) (hΛ : 1 ≤ Λ) (hK : 1 ≤ K₀) (hlog : 4 ≤ Real.log ((sz.W n : ℕ) : ℝ)) (hfloor : (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D) (hJ : 1 ≤ J) (hJW : J ≤ ((sz.W n : ℕ) : ℝ)) : E2HypDif sz n E 0 D Λ K₀ J (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) := by

L1416: theorem LemDecCalEdif_inst_a : E2HypDif sz0 1 (1 / 2) 0 38 1 1 1 (0 : Matrix (Idx 3 (sz0.L 1) (sz0.W 1)) (Idx 3 (sz0.L 1) (sz0.W 1)) ℂ) := by

L1446: theorem LemDecCalEdif_inst_b : E2HypDif szCL 0 (1 / 2) 0 42 1 1 1 (0 : Matrix (Idx 3 (szCL.L 0) (szCL.W 0)) (Idx 3 (szCL.L 0) (szCL.W 0)) ℂ) := by

--- E2HypDif / lossE2dif / LemDecCalE_dif (def text, whitespace collapsed) ---
L61: def E2HypDif {d : ℕ} (sz : Sizes d) (n : ℕ) (E u D Λ K₀ J : ℝ) (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : Prop := E2Hyp sz n E u D Λ K₀ J M ∧ (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D ∧ (∀ (σ : Fin 4 → Bool) (a : Fin 4 → Zd d (sz.L n)), ‖STLM sz n E u M σ a‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 3) ∧ ∀ (σ : Fin 6 → Bool) (a : Fin 6 → Zd d (sz.L n)), ‖STLM sz n E u M σ a‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 5

L72: def lossE2dif (d L W : ℕ) (Λ K₀ : ℝ) : ℝ := lossE2 d L W Λ K₀ * ((729 : ℝ) ^ d * (1 + Real.log ((L : ℝ) ^ d * (W : ℝ) ^ (6 * d))) ^ (2 * d))

L80: def LemDecCalE_dif (d : ℕ) : Prop := ∀ (sz : Sizes d) (n : ℕ) (E u D Λ K₀ J : ℝ) (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), E2HypDif sz n E u D Λ K₀ J M → ∀ (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)), (∀ i : Fin 2, ((zdistInf d (sz.L n) (a i - a' i) : ℕ) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) → ‖STeeM sz n E u M σ a a'‖ ≤ lossE2dif d (sz.L n) (sz.W n) Λ K₀ * ((1 - u)⁻¹ * ((if ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤ 4 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) + (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 : ℝ)) * STtailTD sz n u D a ^ 2)

--- examples (statements) ---
L1470 example#1: example : ‖STeeM sz0 1 (1 / 2) 0 (0 : Matrix (Idx 3 (sz0.L 1) (sz0.W 1)) (Idx 3 (sz0.L 1) (sz0.W 1)) ℂ) ![true, true] ![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1] ![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1]‖ ≤ ((sz0.W 1 : ℕ) : ℝ) ^ 3 * ∑ b : Zd 3 (sz0.L 1), ∑ b' : Zd 3 (sz0.L 1), ‖SB 3 (sz0.L 1) (sz0.lam 1) b b'‖ * (‖STLM sz0 1 (1 / 2) 0 (0 : Matrix (Idx 3 (sz0.L 1) (sz0.W 1)) (Idx 3 (sz0.L 1) (sz0.W 1)) ℂ) ![true, true, true, !true, !true, !true] ![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1, b', Pi.single 0 1, 0, b]‖ + ‖STLM sz0 1 (1 / 2) 0 (0 : Matrix (Idx 3 (sz0.L 1) (sz0.W 1)) (Idx 3 (sz0.L 1) (sz0.W 1)) ℂ) ![true, true, true, !true, !true, !true] ![(Pi.single 0 1 : Zd 3 (sz0.L 1)), 0, b', 0, Pi.single 0 1, b]‖) :=

L1490 example#2: example : let R : ℝ := ((sz0.W 1 : ℕ) : ℝ) ^ 3 * ∑ b : Zd 3 (sz0.L 1), ∑ b' : Zd 3 (sz0.L 1), ‖SB 3 (sz0.L 1) (sz0.lam 1) b b'‖ * (‖STLM sz0 1 (1 / 2) 0 (0 : Matrix (Idx 3 (sz0.L 1) (sz0.W 1)) (Idx 3 (sz0.L 1) (sz0.W 1)) ℂ) ![true, true, true, !true, !true, !true] ![(0 : Zd 3 (sz0.L 1)), 0, b', 0, 0, b]‖ + ‖STLM sz0 1 (1 / 2) 0 (0 : Matrix (Idx 3 (sz0.L 1) (sz0.W 1)) (Idx 3 (sz0.L 1) (sz0.W 1)) ℂ) ![true, true, true, !true, !true, !true] ![(0 : Zd 3 (sz0.L 1)), 0, b', 0, 0, b]‖) 0 < R ∧ ‖STeeM sz0 1 (1 / 2) 0 (0 : Matrix (Idx 3 (sz0.L 1) (sz0.W 1)) (Idx 3 (sz0.L 1) (sz0.W 1)) ℂ) ![true, true] ![(0 : Zd 3 (sz0.L 1)), 0] ![(0 : Zd 3 (sz0.L 1)), 0]‖ ≤ R := by

L1546 example#3: example : ‖STLM sz0 1 (1 / 2) 0 (0 : Matrix (Idx 3 (sz0.L 1) (sz0.W 1)) (Idx 3 (sz0.L 1) (sz0.W 1)) ℂ) ![true, true, true, !true, !true, !true] ![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1, 0, Pi.single 0 1, 0, 0]‖ ≤ 1 * ((((sz0.W 1 : ℕ) : ℝ) ^ 3 * (1 - 0))⁻¹) ^ 5 * (if (zdistInf 3 (sz0.L 1) ((0 : Zd 3 (sz0.L 1)) - 0) : ℝ) ≤ 4 * Real.log (((sz0.L 1 : ℕ) : ℝ) ^ 3 * ((sz0.W 1 : ℕ) : ℝ) ^ (6 * 3)) ^ 2 then 1 else 0) + 32 * 3 ^ (3 + 1) * 1 ^ 6 * 1 * (((sz0.L 1 : ℕ) : ℝ) ^ 3 * ((sz0.W 1 : ℕ) : ℝ) ^ (6 * 3))⁻¹ :=

L1598 example#4: example : let W : ℝ := ((szCL.W 0 : ℕ) : ℝ) let T : ℝ → ℝ := tailTD 3 W 0 42 let S : ℝ := Real.exp 2 * Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4)) let ls : ℝ := Real.log W ^ ((3 : ℝ) / 2) let e : Zd 3 (szCL.L 0) := Pi.single 0 300 let R : ℝ := (2 * 9 ^ 3 * 1 * 1) ^ 2 * S ^ 3 * T (zdistInf 3 (szCL.L 0) ((0 : Zd 3 (szCL.L 0)) - e) : ℝ) ^ 2 * (1 * ((W ^ 3 * (1 - 0))⁻¹) ^ ((3 : ℝ) / 2)) * ((if (zdistInf 3 (szCL.L 0) ((0 : Zd 3 (szCL.L 0)) - 0) : ℝ) ≤ ls + 1 then 1 else 0) + (if (zdistInf 3 (szCL.L 0) ((0 : Zd 3 (szCL.L 0)) - 0) : ℝ) ≤ ls + 1 then 1 else 0) + (if (zdistInf 3 (szCL.L 0) (e - 0) : ℝ) ≤ ls + 1 then 1 else 0) + (if (zdistInf 3 (szCL.L 0) (e - 0) : ℝ) ≤ ls + 1 then 1 else 0)) + (2 * 9 ^ 3 * 1 * 1) ^ 3 * S ^ 3 * T (zdistInf 3 (szCL.L 0) ((0 : Zd 3 (szCL.L 0)) - e) : ℝ) * T (zdistInf 3 (szCL.L 0) ((0 : Zd 3 (szCL.L 0)) - 0) : ℝ) * T (zdistInf 3 (szCL.L 0) (0 - e) : ℝ) 0 < R ∧ ‖STLM szCL 0 (1 / 2) 0 (0 : Matrix (Idx 3 (szCL.L 0) (szCL.W 0)) (Idx 3 (szCL.L 0) (szCL.W 0)) ℂ) ![true, false, true, !true, !false, !true] ![(0 : Zd 3 (szCL.L 0)), e, 0, e, 0, 0]‖ ≤ R := by

$ name-clash grep (Lean tree of main, and of this worktree outside the new file)
E2HypDif: main(f8ad4b4)=       0 other-files-in-worktree=       0
lossE2dif: main(f8ad4b4)=       0 other-files-in-worktree=       0
LemDecCalE_dif: main(f8ad4b4)=       0 other-files-in-worktree=       0
LemDecCalEdif_STeeM_le: main(f8ad4b4)=       0 other-files-in-worktree=       0
LemDecCalEdif_cut_near: main(f8ad4b4)=       0 other-files-in-worktree=       0
LemDecCalEdif_cut_far: main(f8ad4b4)=       0 other-files-in-worktree=       0
LemDecCalEdif_hyp_zero: main(f8ad4b4)=       0 other-files-in-worktree=       0
LemDecCalEdif_inst_a: main(f8ad4b4)=       0 other-files-in-worktree=       0
LemDecCalEdif_inst_b: main(f8ad4b4)=       0 other-files-in-worktree=       0
prefix lemDecCalEdif_ / LemDecCalEdif_ in main:        0 files
$ grep -nE "hJW|J ≤ W|J ≤ \(\(sz" RBM3D/Path/LemDecCalEdif.lean
39:  (`√(Λ M_u⁻³) ≤ Λ M_u^{-3/2}`) in the Cauchy-Schwarz step; the conjunct `J ≤ W` of `E2Hyp` is
58:at `c9a24cf`, with `W^{6d}` so that the near long-edge term needs no `J ≤ W`), and the four- and six-loop bounds
1360:    (hJ : 1 ≤ J) (hJW : J ≤ ((sz.W n : ℕ) : ℝ)) :
1383:  refine ⟨LemDecCalE_e2Hyp_zero sz n hd hE hlam hlam1 hlamW hΛ hK hlog hfloor2 hJ hJW, hfloor,
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h c9a24cf ; ... diff --stat c9a24cf HEAD -- RBM2D/Path/LemDecCalEdif.lean
c9a24cf (RBM2D HEAD: 9e0f275)
 RBM2D/Path/LemDecCalEdif.lean | 68 ++++++++++++-------------------------------
 1 file changed, 18 insertions(+), 50 deletions(-)
```

Narrative.
- All five targets and the pinned vocabulary are in `RBM3D/Path/LemDecCalEdif.lean` (1643 lines, commit `a86773c` on `t/T2171`, the only file in `git diff --stat main...t/T2171`); `lake build RBM3D.Path.LemDecCalEdif` has 0 warnings and 0 errors; `Test/Axioms.lean` is unchanged (the registry pre-check exits 0 and does not name `E2HypDif`: it is concluded by `LemDecCalEdif_hyp_zero`).
- Port sources (RBM2D `Path/LemDecCalEdif.lean` at `c9a24cf`, read with `git show c9a24cf:`): §1 `:65-347` -> `lemDecCalEdif_{wt,path2,loop6,loop4,loop6_rot,mid,glue,loop6_eq_sum,loop4_eq_sum,mid_le,glue_le,loop6_le_glue,wcs,glue_herm,loop4_eq,loop6_le_cs,loop6_le_pt}`; §2 `edge_u`/`shiftS`/`edge_v`/`pair_le` `:427-496` -> `_edge`/`_shift`/`_edge_shift`/`_pair_le` (no `tail_uv`: `v = u`); §3 `:509,515` -> `_STLM6`/`_STLM4`; §4 `logP_ge`/`wD_le`/`tail_Rss`/`cut_near` `:534-615` -> `_logP_ge`/`_wD_le`/`_tail_Rss`/`LemDecCalEdif_cut_near`; §5 `sqrt_loop4_le`/`quad_le`/`cut_far` `:702-746` -> `_sqrt_loop4`/`_quad_le`/`LemDecCalEdif_cut_far`; `EE_le` `:1010` -> `LemDecCalEdif_STeeM_le`. Statements and every constant were re-derived at `d >= 3`, not transcribed: `Z2 -> Zd d L`, `BlockIndex -> Vtx d L W`, `zdist2 -> zdistInf`, `25 -> 9^d`, `50 -> 2*9^d`, `200 -> 3^(d+1)`, `L^2 W^12 -> L^d W^(6d)`, `ellT = 1` (`lemDecCalEdif_ellT_eq_one`).
- General `sigma` (the only structural change): `lemDecCalEdif_loop6 A C A' C'` = `tr(A E1 C E2 A E3 A' E4 C' E5 A' E6)`; `mid = C E2 A E3 A' E4 C'` (pointwise bound only), `glue = A' E6 A` (Hermitian iff `A' = A^H`); rotation by three is `(A,C,A',C') -> (A',C',A,C)`; Cauchy-Schwarz needs only `A' = A^H`; the edge pairs `(C,C')`, `(A,A')`, `(A',A)` use (e7) for both signs (`lemDecCalEdif_edge`, `ST_Gres_false`). The cases (1a)(1b)(2a)(2b) of RBM2D carry over at the `L^inf` distance; `linarith` closes them with `4 <= (log W)^(3/2)`.
- Premise use: `h.1` (entries (e6), (e7), Hermitian); `h.2.1` (floor) only in `_wD_le`; `h.2.2.1` (four-loop) only in `_sqrt_loop4`; `h.2.2.2` (six-loop) only in the near branch of `cut_near`. The `J <= W` conjunct is destructured nowhere in this file; `hJW` occurs only as the premise of `LemDecCalEdif_hyp_zero` (grep above, lines 1360, 1383), passed to `LemDecCalE_e2Hyp_zero`, because `E2Hyp` carries it.
- `LemDecCalEdif_hyp_zero` takes the exact route: `G_0(sigma) = m(sigma) I` (private copies of `lemDecCalE_gres_zero*`), `lemDecCalEdif_prod_diag`, `lemDecCalEdif_norm_trace_diag`: `|L^(k+1)| <= W^(-dk)`, so `1 <= Lambda` suffices (no `(Im m)^(-6) <= Lambda`); `norm_gloop_le_of_le_abs_im` is not used.
- Instances: (a) `LemDecCalEdif_inst_a` (`sz0`, `n = 1`, `D = 38`) and (b) `LemDecCalEdif_inst_b` (`szCL`, `n = 0`, `D = 42`) are `E2HypDif` at `Lambda = K0 = J = 1`, `E = 1/2`, `u = 0`, `M = 0`, so `Lambda0 = 1`. Example 1 is (c) at the ticket's data `a = a' = (0, e1)`: its right side is not shown positive there (the labels `(a0, a1, ...)` are never all equal); example 2 is (c') at `a = a' = (0, 0)` with `R > 0` (`lemDecCalEdif_STLM_zero_const`: the equal-label six-loop at `M = 0` is exactly `W^(-5d)`); example 3 is (d) at (a), `sigma0 = sigma1 = +`; example 4 is (e) at (b), `|A1 - A2| = 300 > 4 (log 2^24)^(3/2)`, with `R > 0` and the bound with the same `R` (`let R`).
- Section (a) is used unchanged (no (a') needed): `c_near = 32*3^(d+1)`, `c_e = 2*9^d`, `kappa_dif = 729^d`, four-loop factor `Lambda * ((W^d (1-u))^-1)^(3/2 : R)`. The part-2 constant chain (row 6) is the preflight's script scan; it is not re-proved here (S5-07 does it). The consumer diff above (`verify.py`) shows the right side of `LemDecCalE_dif` equals `Step5Pins.lean:178-186` after `M := seqHflow n u omega`, `J := Jst n u D`.
- Whole-library `lake build` exit 0 (3942 jobs) in this worktree; the new module is not yet a root import (the hub adds it at merge).

## (c) Verified Mathlib names

`#check` of 37 names (`names.lean`, run in the worktree): 37 `#check` lines, exit 0, 0 lines containing `error` in `names.out`.
- Matrix: `trace_mul_comm`, `mul_apply`, `diagonal_mul_diagonal`, `mul_diagonal`, `diagonal_mul`, `diagonal_conjTranspose`, `conjTranspose_mul`, `IsHermitian.submatrix`, `inv_submatrix_equiv`, `nonsing_inv_eq_ringInverse`, `submatrix_sub`, `submatrix_smul`, `diagonal_smul`, `trace_diagonal`.
- Finset: `prod_le_prod₀` (`h0`, `h1`; `Finset.prod_le_prod` is now the one-hypothesis monoid version), `sum_mul_sq_le_sq_mul_sq`, `sum_pos'`, `prod_mul_distrib`; `Fin.prod_univ_succ`, `norm_prod`, `Equiv.apply_symm_apply`, `List.ofFn_succ`.
- Real/Complex: `Real.le_sqrt_of_sq_le`, `Real.sqrt_le_iff`, `Real.sqrt_lt'`, `Real.rpow_add`, `Real.rpow_le_rpow_of_exponent_le`, `Real.exp_one_lt_d9`, `Real.log_two_lt_d9`, `Real.log_two_gt_d9`, `Complex.conj_mul'`, `Complex.star_def`.
- Order: `pow_le_pow_right₀`, `pow_le_pow_left₀`, `inv_anti₀`, `inv_le_one_of_one_le₀`.
- Verified absent/changed: `Finset.prod_le_prod` with `(h0) (h1)` arguments (now `Finset.prod_le_prod₀`).

## (d) Open issues and paper-delta candidates

For the dispatcher / S5-09 (premises not supplied by `STIngR5`, see the table in (a)):
- Floor `(L^d W^(6d))^2 <= W^D` is **missing** from `STLemDecCalEConcl` (`Step5Pins.lean:163` gives `size <= W^D`); `E2Hyp`'s `GijGEX` conjunct (T2164 M2) and `J <= W` (T2164 M3, a conjunct of `E2Hyp`, hence of `E2HypDif`, unused by parts 1-2) are still open.
- The four- and six-loop clauses come from `STLmaxU` (`Step34Pins.lean:176`) at `k = 4, 6` with `Bctl <= 2 (W^d(1-u))^-1` (preflight (a), Consumer table).
For S5-07: `lemDecCalEdif_*` helpers are `private`; public merged lemmas it can use: `LemDecCalE_e10a`, `LemDecCalE_sum_tail_tail`; the support of `SB` is `lemDecCalE_SB_support` (`Path/LemDecCalE.lean:770`, `private`: copy). Private copies made here (merged versions are private): `lemDecCalEdif_ellT_eq_one` (`Induction/B45.lean:1983`), `_gres_zero_true`, `_gres_zero`, `_blockMat_zero`, `_sum_block_indicator` (`Path/LemDecCalE.lean:1208-1250`), `_Gres_blockMat` (`Evolution/ExpInv.lean:116`).
Paper-delta candidates:
- T2171a: the four- and six-loop bounds are hypotheses of `E2HypDif` (RBM2D `goodSet` clause 2 at `k = 4, 6`, `GoodSet.lean:49`); not in `E2Hyp`.
- T2171b: floor `(L^d W^(6d))^2 <= W^D`, stronger than D374's `L^d W^(2d) <= W^D` and than the paper's `W^D >= N`.
- T2171c: every `sigma in {+,-}^2` in `LemDecCalEdif_STeeM_le`, `_cut_near`, `_cut_far` (RBM2D: `(+,-)` only).
- T2171d: `lossE2dif = lossE2 * 729^d (1 + log(L^d W^(6d)))^(2d)` is the explicit loss in place of the paper's `≺` in `res_deccalE_dif`.
- T2171e: the four-loop factor of `_cut_far` is `Lambda * ((W^d(1-u))^-1)^(3/2 : R)` (inverse before the real power), not `M_u^(-3/2)`; same value.
