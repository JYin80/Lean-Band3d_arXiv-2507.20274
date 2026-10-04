Prover model: claude-sonnet-5-5
## (a) Math preflight — Sun Oct  4 06:11:51 UTC 2026
Notation: `B=Bparam d L g t 0=A⁻¹+(L^d(1-t))⁻¹`, `A=g²+|1-t|`; `K^π=KLKpi`; `P(n):=KLKpiBoundAt d n κ gmax`; `J=(i,j)`, `w=j-i`, `k=w+1` inner, `n''=n-w+1` outer vertices; `SB=S^{(B)}`. Python (numpy, FFT, exact tree sums, Lean conventions `KLleafPar/KLnodePar/KLtreeValW`) in `scratchpad/T2115/` (cwd below); `kk.py` checked against brute force over node labels: `python3 brute.py` -> `treeval vs brute force over node labels: 15 (sigma,F) pairs, n=5, L=3, E=1: max abs err 7.0e-16`.
**The induction (written first).** Measure: `n≥3`, strong induction; step at `n` uses `P(n'')`, `3≤n''<n`, and `KLindStepPin_holds` (no induction) at `k<n`. Cases of `(σ,π,a)` at level `n`:
(S0) `π=∅`: `K^∅=Σ_δ Σ(δ)∏_vΘ_v(a_v,δ_v)` (`KLKpi_eq_sum_SigmaPi`, KLTree:435). (a) `σ` constant: `|Σ(δ)|≤Cm` (`KLmolecule_holds`, KLMolecule:610) and `Σ_b|Θ^{(s,s)}(a_v,b)|≤S` (`KLedge_l1`, probe port) give `|K^∅|≤Cm S^n≤Cm S^n(1+gmax²)^{n-1}B^{n-1}` (`A⁻¹≤B`: `KLlat_inv_le_Bparam`, KLIndStepA:114; `A≤1+gmax²`). (b) `σ_r≠σ_{r+1}`: `K^∅=Σ_bΘ(a_r,b)X_b`, `X_b=Σ_{δ_r=b}Σ∏_{i≠r}Θ_i`; `sup|Θ|≤CdB` (`KLIndStepA_Theta_norm_le`:143; long edge is `Theta (t:ℂ)`, `KLIndStepA_thetaEdge_long`:466) and `Σ_b|X_b|≤C L^τB^{n-2}` (`KLindStepPin_holds d n`, KLIndStepB:847) give `≤CdC L^τB^{n-1}`.
(S1) `KLTSPlong n σ π=∅`: `K^π=0`. (S2) else pick `F₀` with `KLFlong F₀ σ=π`, `π⊆diagonals n`, `J∈π` innermost (`exists_innermost`, KLSumZeroWard:577, private). Cut: `KLsum_cut` (KLCut:1297) with `f G H=1[KLFlong G σ_out=π'']·1[KLFlong H σ_in=∅]·Σ_{u,w}X`, `π''=(π.erase J).image KLshiftOut`; layer condition `Flong_eq_iff_cut` (KLSumZeroWard:165) (this is where "innermost" is used: inner polygon has no long edge). Pointwise cut of `KLtreeValG` (new, RBM2D `treeValW_long_cut` KBoundCut:1550): `KLtreeValW_cut` (KLCut:282) with `P=ξ•1, S=SB, Q=Θ^{(σ_i,σ_j)}` (`Θ-1=ξ•(SB·Θ)` from `mul_Theta_of_three_le`, Props4:90), `KLgval_in_eq` (KLCut:455), `KLgval_out_eq` (KLCut:746); the glue leaf of the outer polygon is the standard leaf `Θ^{(σ_i,σ_j)}`, the inner root leaf is the identity, so
  `K^π(σ,a) = t·Σ_{u,w} A(u) SB_{uw} K^{π''}(σ_out,a_out(w))`, `A(u)=Σ_{δ_r=u}Σ^{(∅)}_{σ_in}(δ)∏_{i≠r}Θ_i(a_in i,δ_i)`, `r=last` (`KLtreeValW_eq_sum_selfW`, KLTree:403): `A(u)` is the summand of the LHS of `KLindStepAt` at `(k,σ_in,r=last)`, and `σ_in(last)=σ_j≠σ_i=σ_in(0)`.
  Bound: `|t|≤1`, `Σ_u|A|≤C_in L^{τ/2}B^{k-2}` (`KLindStepPin_holds d k` at `τ/2`), `sup_w|K''|≤C_out L^{τ/2}B^{n''-1}` (`P(n'')` at `τ/2`), `Σ_w|SB_{uw}|=1` (`sum_norm_SB_row`, Block:118): `|K^π|≤C_inC_out L^τ B^{n-1}`. `C_n(τ)=C_∅+Σ_{k,n''}C_in(k)C_out(n'')` (finite, `choose` over `k<n`).
KLboundPin: `n=1` `KLK_one`; `n=2` `KLK_two`+`KLedge_sup`; `n=3` `KLK_three`+`KLedge_sup`+`KLedge_l1` (target 1); `n≥4`: `KLK_eq_sum_Kpi` (KLTree:392), `norm_sum_le`, `card_powerset`: `|KLK|≤2^{n(n-3)/2}C_Kpi(τ)L^τ((W^d)⁻¹B)^{n-1}`.
**(i) Exponent table**
| # | quantity | value / constraint | slack |
|---|---|---|---|
| 1 | ranges | `3≤d`, pins `n≥3` (`KLKpiBoundPin`), `n≥1` (`KLboundPin`); base `n=3`: `diagonals 3=∅`, `π≠∅` gives `K^π=0`; `n=3` also follows from `KLK_eq_sum_Kpi` (not needed) | `d-2≥1` |
| 2 | cut geometry | `J` diagonal, not `(0,n-1)`: `w∈[2,n-2]`, `k=w+1∈[3,n-1]`, `n''=n-w+1∈[3,n-1]` (so `P(n'')` and `KLindStepPin` at `k≥3` apply); `book.py`: all hold for every diagonal, `n=3..10` | `n-k=n-w-1≥1`, `n-n''=w-1≥1` |
| 3 | `B`-exponent | `(k-2)+(n''-1)=n-1` (e.g. `n=5`: `(k,n'')∈{(3,4),(4,3)}`; `n=6`: `{(3,5),(4,4),(5,3)}`) | exactly 0 |
| 4 | factor of the cut | exactly `t`, `0≤t<1` (ticket text "factor of modulus 1, `∏m`" is corrected: `∏_{in}m·∏_{out}m=∏m·m(σ_i)m(σ_j)` by `prod_leaves_cut`, KLSumZeroWard:372, and `m(σ_i)m(σ_j)=1` for a long `J`, `KLmSigma_mul_not`) | `1-t>0` |
| 5 | `SB`-average | `Σ_w|SB_{uw}|=1` for `3≤L`: `|Σ_wSB_{uw}K''(w)|≤sup_w|K''|` | exactly 0 |
| 6 | `L^τ` split | `π≠∅`: `τ/2` (inner, `KLindStepPin` at `τ/2`) `+τ/2` (outer, `P(n'')` at `τ/2`) `=τ`, `Real.rpow_add`; `π=∅`: `KLindStepPin` at `τ` and `Cd` (no loss), no split; `KLboundPin`: no split (the count `2^{n(n-3)/2}` is a constant): `n=4` 4, `n=5` 32 | `τ` exact |
| 7 | `W^{-d}` count | `KLK_eq_sum_Kpi`: `(W^d)⁻¹` to the `n-1`; `((W^d)⁻¹B)^{n-1}=(W^d)⁻¹^{n-1}B^{n-1}`; `K^π` has no `W` | exactly 0 |
| 8 | `π=∅`, `σ` constant | `B≥A⁻¹≥(1+gmax²)⁻¹` (`1-t≤1`, `g≤gmax`): constant `Cm·S^n·(1+gmax²)^{n-1}`, `S=Cκ(1+gmax²·expC)` (`KLShort`); at the instance `B=2.937≥0.5` | `B(1+gmax²)≥1` |
| 9 | `π=∅`, `σ` not constant | exists `r` with `σ_r≠σ_{r+1}` (cyclic); `KLindStepPin` needs `3≤n`, `σ_r≠σ_{r+1}`: yes | exponent `1+(n-2)=n-1` |
| 10 | constants | `C=C(d,n,κ,gmax,τ)`: `∃C` before `∀p σ π a` in `KLBoundAt/KLKpiBoundAt`; `KLPar` supplies `0≤t<1`, `3≤L`, `1≤W`, `0<g≤gmax`, `|E|≤2-κ`; no `L,W,g,t,E` | — |
| 11 | DECISIONS §29 | (1) `0≤t<1`: `B` finite, `|1-t|=1-t`; (2),(3) no `ilambda`, no `L`–`W` relation (`W` only in the prefactor); (4) pins fix `n`; regimes `1-t≷g²,g²/L²,g²/L^d`: all four visited, table below | — |
| 12 | hypotheses | only `KLPT d κ gmax` (`Test/Axioms.lean` borrowed list) + `KLShort_holds` (KLMolecule:341); no new `Prop`. Registry rule (`Axioms.lean:300-320`): a `Prop` def in a theorem binder counts as assumed unless a theorem concludes it: any step lemma with a `P(n'')` hypothesis needs `KLKpiBoundAt_holds`/`KLBoundAt_one,_two,_three` in the file | — |
| 13 | `KLoopBound` (KBound:74) | implied by `KLboundPin` at `κ:=2-|E|`, `gmax:=g`, for `3≤d,3≤L,1≤W,0<g,|E|<2`, `K=KLK`, given `KLPT d (2-|E|) g` (same bound `C L^τ((W^d)⁻¹B)^{n-1}`; lists `⟨σ,a⟩=KLloopOf`); its `∃C` may depend on `L,W,g` (weaker than `KLBoundAt`); not a ticket target | — |
| 14 | T2106a (`tSΘ` leaf) | settled: the inner polygon has only `Θ^{(σ_i,σ_{i+1})}` leaves (root leaf `=1`); `tSΘ` is the cut edge `P·SB·Q`, `Q` = the standard glue leaf of the outer polygon; `K̃` is not formed because `P(n'')` is uniform in `a`; merged `KLindStepAt` suffices | — |
**(ii) One concrete nondegenerate instance and numerics** (`d=3, κ=gmax=1, L=5, W=2, g=1/2, E=0, t=9/10, τ=1/2, n=4`; probe `KLinst` data):
```
$ python3 inst.py   # hypotheses, B, K^pi, KLK, the cut at J=(0,2) (w=2,k=3,n''=3) for sigma=(+,+,-,-)
hypotheses: 3<=d True | 0<kappa True | 0<gmax True | KLPar: 3<=L True, 1<=W True, 0<g<=gmax True, |E|<=2-kappa True, 0<=t<1 True | n=4: 3<=n True | |m|=1: 1.0, m(+)m(-)=1.0
A=g^2+1-t=0.3500  B_{t,0}=A^-1+(L^d(1-t))^-1=2.9371  B>=(1+gmax^2)^-1=0.500 : True  L^tau0=2.2361  card diagonals(4)=2 diagonals(5)=5
a=[(0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)] sigma=(+,+,-,-):
  K^pi (pi: |K^pi|/B^3): []: 0.0779; [(0, 2)]: 0.0628; [(1, 3)]: 0.0628
  KLK=W^{-d(n-1)} sum_pi K^pi: |KLK|=1.007e-02 ; |KLK|/(L^tau0 (W^-d B)^(n-1)) = 0.0910   [KLBoundAt 4 at this data, tau=1/2]
  cut J=(0,2): K^pi=1.590744e+00+1.540744e-33i, t*sum A S K''=1.590744e+00-1.733337e-33i |diff|=4.4e-16 ; sum_u|A|/B^(k-2)=0.5206 (k=3) ; max_w|K''|/B^(n''-1)=0.2981 (n''=3) ; product bound t*(.)(.)*B^(n-1)=3.5395e+00 >= |K^pi|=1.5907e+00 : True
a=[(0, 0, 0), (1, 0, 0), (0, 1, 2), (2, 2, 2)] sigma=(+,+,-,-):
  K^pi (pi: |K^pi|/B^3): []: 0.0000; [(0, 2)]: 0.0000; [(1, 3)]: 0.0000
  KLK=W^{-d(n-1)} sum_pi K^pi: |KLK|=5.198e-07 ; |KLK|/(L^tau0 (W^-d B)^(n-1)) = 0.0000   [KLBoundAt 4 at this data, tau=1/2]
  cut J=(0,2): K^pi=2.649656e-04-3.669879e-19i, t*sum A S K''=2.649656e-04+1.638100e-19i |diff|=5.3e-19 ; sum_u|A|/B^(k-2)=0.1404 (k=3) ; max_w|K''|/B^(n''-1)=0.0082 (n''=3) ; product bound t*(.)(.)*B^(n-1)=2.6093e-02 >= |K^pi|=2.6497e-04 : True
n=3 sigma=(+,-,+) a=[(0, 0, 0), (0, 0, 0), (0, 0, 0)]: |KLK|/(L^tau0 (W^-d B)^2) = 0.1333   [KLBoundAt_three at this data]
n=3 sigma=(+,-,+) a=[(0, 0, 0), (1, 0, 0), (2, 2, 2)]: |KLK|/(L^tau0 (W^-d B)^2) = 0.0000   [KLBoundAt_three at this data]
$ python3 -W ignore pre2.py inst 0 | sed -n '1p;4,6p'   # external KLPT: L^d(1-t)Theta(0,0)->1, (1-t)rowsum=1, BD1/BD2/KLZero/KLDecay/KLShort bounded as 1-t->0 (md5 145174ee = T2100/pre2.py)
B0=2.9371 A=0.35 m(+)m(-)=1.0; max|Tp(z)-Tp(-z)|=2e-17; signed c0+sum_{y!=0}(Tp+Tn)=0.05263 (T2056 closed form 2/(1+t)-1=1/19=0.05263)
  1-t=1e-01: L^d(1-t)Theta(0,0)=23.2191 (1-t)rowsum=1.000000 BD1 0.809 BD2 2.427 KLZero 0.622 KLDecay 0.632 KLShort 0.0043
  1-t=1e-06: L^d(1-t)Theta(0,0)=1.0003 (1-t)rowsum=1.000000 BD1 0.845 BD2 2.576 KLZero 0.520 KLDecay 1.350 KLShort 0.0042
  1-t=1e-09: L^d(1-t)Theta(0,0)=1.0000 (1-t)rowsum=1.000000 BD1 0.845 BD2 2.576 KLZero 0.577 KLDecay 1.350 KLShort 0.0042
$ python3 -W ignore cut.py 1.0 ; python3 -W ignore cut.py 0.0 | grep -o 'diff|=[0-9.e+-]*' | sort -g | tail -1   # cut identity K^pi = t sum A SB K'' , L=3, E=1 / E=0, n=5,6, pi with 1 or 2 edges
cut1: 10 cases (n=5: pi={(1,3)}; n=6: pi={(1,3),(0,4)}, {(2,5)}), max |diff| 3.2e-19; cut0: 10 cases, max |diff| 3.9e-19; e.g. n=6 sigma=++---+ pi=[(1, 3), (0, 4)] J=(1, 3) w=2 outer=5-gon |pi''|=1: K^pi=-4.580818e-07-2.280388e-06i  t*sum A S K''=-4.580818e-07-2.280388e-06i  |diff|=1.5e-21
$ python3 -W ignore ratios.py | tail -3   # d=3, L in {5,9}, g in {.5,1}, 1-t in {1e-1,1e-3}, E in {0,1}, n in {3,4,5}, all sigma, 20 configs a; ratio = |KLK|/(L^0 (W^-d B)^(n-1)); divide by L^(1/2)=2.236 (L=5), 3 (L=9) for tau=1/2
MAX n=3 over all grid points: |KLK|/(W^-d B)^(n-1) 2.169 | max_pi pi=empty 2.169 | pi!=empty 0.000
MAX n=4 over all grid points: |KLK|/(W^-d B)^(n-1) 4.091 | max_pi pi=empty 4.091 | pi!=empty 0.749
MAX n=5 over all grid points: |KLK|/(W^-d B)^(n-1) 6.897 | max_pi pi=empty 4.292 | pi!=empty 1.302
$ python3 -W ignore ratios2.py | tail -2   # E=0, g in {.05,.5,1}, 1-t in {1,1e-1,1e-3,1e-6}, L in {5,9}, n in {4,5}: all four regimes of DECISIONS 29 (and 1-t>g^2)
regimes visited (count of grid points): {'1-t>g^2': 9, 'g^2/L^2<1-t<=g^2': 13, '1-t<=g^2/L^3': 18, 'g^2/L^3<1-t<=g^2/L^2': 2}
worst ratio per n: {4: 7.934516015294345, 5: 15.015685062680188}
$ python3 -W ignore growth.py   # L-growth (loss L^tau needed only for a log L): n=4, g=1, 1-t=0.1
n=4 g=1 1-t=0.1 L= 5: max |KLK|/(W^-d B)^3 = 3.420 ; /(1+log L) = 1.311  [0s]
n=4 g=1 1-t=0.1 L= 9: max |KLK|/(W^-d B)^3 = 4.091 ; /(1+log L) = 1.279  [0s]
n=4 g=1 1-t=0.1 L=17: max |KLK|/(W^-d B)^3 = 4.248 ; /(1+log L) = 1.108  [0s]
n=4 g=1 1-t=0.1 L=33: max |KLK|/(W^-d B)^3 = 4.273 ; /(1+log L) = 0.950  [1s]
$ python3 pindiff.py   # pin text: probe vs docs/tickets/checks/T2115-check.lean
def KLBoundAt (64b58eb probe line 509, check file line 37): IDENTICAL
def KLboundPin (64b58eb probe line 782, check file line 47): IDENTICAL
def KLKpiBoundAt (64b58eb probe line 800, check file line 53): IDENTICAL
def KLKpiBoundPin (64b58eb probe line 806, check file line 59): IDENTICAL
```
Reading: all ratios are bounded, they grow with `n` (`n=3,4,5`: 2.2, 4.1, 6.9 on the ticket grid; 7.9, 15.0 with `1-t=1` at `g=1`, i.e. `t=0`: there `|K|=1` at equal labels and `B=0.50-0.51`), as `C(n)` allows; the `π≠∅` maxima (0.75 at `n=4`, 1.30 at `n=5`) are below the `π=∅` maxima (4.09, 4.29); no growth in `L` beyond `log L` (`/(1+log L)` falls from 1.31 to 0.95); for `g=.05` the ratios are `≤1.003`. Instance: all hypotheses of `KLKpiBoundAt`, `KLBoundAt` (`n=4`) and `KLBoundAt_three` hold at the same data; `KLPT 3 1 1` stays an instance hypothesis (limit lines above).
**Verdicts.** Target 1 (`n≤3` port; merged twins: `KLIndStepA_Bparam_nonneg`/`_le_zero` for `KLBparam_nonneg`/`KLBparam_le_zero`, `KLIndStepA_Theta_apply_sub` (form `b-a`) for `KLTheta_eq_zero` (form `a-b`); `KLedge_sup` (all `μ`, `‖μ‖=1`), `KLedge_l1`, `KLstar_le`, `KLone_le_rpow` are not merged and are ported): PASS. Target 2 (pins verbatim: the four `def` blocks of `docs/tickets/checks/T2115-check.lean` equal `64b58eb:RBM3D/Probe/T2004Pins.lean` by script, output below): PASS. Target 3 (`Kpi_cut` with exact factor `t`; `KLindStepAt` as merged suffices, no `tSΘ` leaf): PASS; the private `KLSumZeroWard` lemmas can be reached by `open private … from RBM3D.Loop.KLSumZeroWard` (precedent `KLIndStepA.lean:43`), else copy; the pointwise cut `treeValW_long_cut` is not merged and must be written. Target 4 (`KLKpiBoundPin_holds`, `KLboundPin_holds`; hypotheses only `KLPT`, constants `C(d,n,κ,gmax,τ)`): PASS. No exponent is short (slack 0 exactly at rows 3, 5, 7). Overall: **PASS**.

## (a′) Preflight corrections — Sun Oct  4 06:56:01 UTC 2026 (`date -u`)
1. Row 12 and the verdict of target 1 ("hypotheses: only `KLPT` ... no new `Prop`") do not cover the probe's `KLDecay` binders of `KLedge_sup`, `KLBoundAt_two`, `KLBoundAt_three`: ported as they are, `RBM.Loop.KLDecay` becomes an assumed, never concluded, unregistered premise and the registry pre-check fails (fixture in (b), exit 1). Corrected in the file: these three take `KLPT d κ gmax` (registered, borrowed). No verdict changes; target 1 stays PASS.
2. Row 4, refinement: the cut prefactor is `t` for every charges; `m(σ_i) m(σ_j) = 1` is not needed (the product identity is `prod_leaves_cut`, the `hprod` step of `KLKpi_cut`).

## (b) Script output (HEAD `177e4e3` of `t/T2115`, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2115`; scratch scripts in `scratchpad/T2115/`)
```
$ lake build RBM3D.Loop.KLInduct 2>&1 | tail -3      # final_evidence.sh, 06:53:19-06:54:18 UTC
Build completed successfully (3257 jobs).
$ git diff --stat main...t/T2115; wc -l RBM3D/Loop/KLInduct.lean; grep -cE "sorry|admit|native_decide|^axiom|maxHeartbeats" RBM3D/Loop/KLInduct.lean
 RBM3D/Loop/KLInduct.lean | 1397 ++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1397 insertions(+)
    1397 RBM3D/Loop/KLInduct.lean
0
$ lake env lean axscan.lean   # every constant of the module, private included
module RBM3D.Loop.KLInduct: 32 hand-written constants (23 theorems, 9 defs, 7 private, counted among them); constants using an axiom outside [propext, Classical.choice, Quot.sound]: 0 [] 
$ lake env lean axioms_all.lean   # #print axioms of the 24 public declarations, grouped
[propext, Classical.choice, Quot.sound]: 19: KLBoundAt, KLboundPin, KLKpiBoundAt, KLKpiBoundPin, KLTheta_eq_zero, KLedge_sup, KLedge_l1, KLstar_le, KLone_le_rpow, KLBoundAt_one, KLBoundAt_two, KLBoundAt_three, KLKpi_cut, KLInduct_Kpi_empty_bound, KLKpi_step, KLInduct_KpiBoundAt_holds, KLKpiBoundPin_holds, KLInduct_BoundAt_of_Kpi, KLboundPin_holds
[propext, Quot.sound]: 3: KLInduct_aIn, KLInduct_aOut, KLInduct_insta
[propext]: 2: KLInduct_instσ, KLInduct_instJ
$ registry pre-check: printf "import RBM3D\nimport RBM3D.Loop.KLInduct\n#assert_rbm_axioms\n" | lake env lean --stdin; echo exit   (and the same without the second import)
with: exit=0   base: exit=0   # diff base with (the audit text differs in two lines only):
< axiom audit: 3495 theorems, 1233 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
> axiom audit: 3511 theorems, 1242 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
<   RBM.Loop.KLPT: 8 [no certificate]
>   RBM.Loop.KLPT: 15 [no certificate]
premises found by scanning: 83 (borrowed 2, owed 65, structural 16)   # in both; carriers: RBM.Loop.KLoopBound: 0
$ fixture of the probe-style hypothesis (reg_fail.lean: theorem KLInduct_probe_style (hD : KLDecay 3 1) : True; #assert_rbm_axioms)
exit=1  error: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, ...:  [RBM.Loop.KLDecay]
$ full build, temporary `import RBM3D.Loop.KLInduct` after the last import of RBM3D.lean (same run; reverted, not committed)
full build exit=0
608:info: RBM3D.lean:159:0: axiom audit: 3511 theorems, 1242 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
723:premises found by scanning: 83 (borrowed 2, owed 65, structural 16).
790:Build completed successfully (3860 jobs).
$ git status --short   # after the revert: clean
$ pins: docs/tickets/checks/T2115-check.lean (from the docstring of KLBoundAt to the end of KLKpiBoundPin) and 64b58eb:RBM3D/Probe/T2004Pins.lean vs KLInduct.lean §1
section 1 == check file text (docstrings and defs, byte for byte): True
def KLBoundAt: probe == KLInduct.lean: True
def KLboundPin: probe == KLInduct.lean: True
def KLKpiBoundAt: probe == KLInduct.lean: True
def KLKpiBoundPin: probe == KLInduct.lean: True
$ statements extracted from the file by script (scratchpad/T2115/stmts.py; proofs omitted)
L1150 theorem KLKpiBoundPin_holds : KLKpiBoundPin
L1190 theorem KLboundPin_holds : KLboundPin
L609 theorem KLKpi_cut (d L : ℕ) [NeZero L] (g : ℝ) (hL : 3 ≤ L) {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (m : Bool → ℂ) (t : ℝ) (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1)
    (σ : Fin n → Bool) {F₀ : Finset (Fin n × Fin n)} (hF₀ : F₀ ∈ TSP n)
    {π : Finset (Fin n × Fin n)} {J : Fin n × Fin n} (hπ : KLFlong F₀ σ = π) (hJπ : J ∈ π)
    (hinner : ∀ e ∈ π, KLArcLe e J → e = J) (a : Fin n → Zd d L) :
    KLKpi d L g m t σ a π
      = ∑ u : Zd d L, ∑ w : Zd d L,
          (t : ℂ) *
            (∑ δ ∈ Finset.univ.filter (fun δ : Fin (KLwIn J + 1) → Zd d L => δ (Fin.last _) = u),
              KLSigmaPi d L g m t (sigmaIn σ J) ∅ δ *
                ∏ i ∈ Finset.univ.erase (Fin.last (KLwIn J)),
                  thetaEdge d L g m t (sigmaIn σ J i) (sigmaIn σ J (i + 1))
                    (KLInduct_aIn J a i) (δ i))
            * SB d L g u w *
          KLKpi d L g m t (sigmaOut σ J) (KLInduct_aOut J a w) ((π.erase J).image (KLshiftOut J))
L987 theorem KLKpi_step (d n : ℕ) [NeZero n] (κ gmax : ℝ) (hd : 3 ≤ d) (hn : 3 ≤ n) (hκ : 0 < κ)
    (hg : 0 < gmax) (hPT : KLPT d κ gmax)
    (hout : ∀ (n'' : ℕ) [NeZero n''], 3 ≤ n'' → n'' < n → KLKpiBoundAt d n'' κ gmax) :
    KLKpiBoundAt d n κ gmax
L836 theorem KLInduct_Kpi_empty_bound (d n : ℕ) [NeZero n] (κ gmax : ℝ) (hd : 3 ≤ d) (hn : 3 ≤ n)
    (hκ : 0 < κ) (hg : 0 < gmax) (hPT : KLPT d κ gmax) (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool) (a : Fin n → Zd d p.L),
      ‖KLKpi d p.L p.g (mSigma p.E) p.t σ a ∅‖
        ≤ C * (p.L : ℝ) ^ τ * (Bparam d p.L p.g p.t 0) ^ (n - 1)
L1138 theorem KLInduct_KpiBoundAt_holds (d n : ℕ) [NeZero n] (κ gmax : ℝ) (hd : 3 ≤ d) (hn : 3 ≤ n)
    (hκ : 0 < κ) (hg : 0 < gmax) (hPT : KLPT d κ gmax) : KLKpiBoundAt d n κ gmax
L1157 theorem KLInduct_BoundAt_of_Kpi (d n : ℕ) [NeZero n] (κ gmax : ℝ) (hd : 3 ≤ d) (hn : 3 ≤ n)
    (hκ : 0 < κ) (hg : 0 < gmax) (hPT : KLPT d κ gmax) : KLBoundAt d n κ gmax
L226 theorem KLBoundAt_one (d : ℕ) {κ gmax : ℝ} (hκ : 0 < κ) : KLBoundAt d 1 κ gmax
L236 theorem KLBoundAt_two {d : ℕ} {κ gmax : ℝ} (hκ : 0 < κ) (hPT : KLPT d κ gmax) :
    KLBoundAt d 2 κ gmax
L267 theorem KLBoundAt_three {k : ℕ} {κ gmax : ℝ} (hκ : 0 < κ) (hPT : KLPT (k + 2) κ gmax) :
    KLBoundAt (k + 2) 3 κ gmax
L142 theorem KLedge_sup ...   (ported, see the diff against the probe below)
L171 theorem KLedge_l1 ...   (ported, see the diff against the probe below)
L209 theorem KLstar_le ...   (ported, see the diff against the probe below)
L222 theorem KLone_le_rpow ...   (ported, see the diff against the probe below)
L131 theorem KLTheta_eq_zero ...   (ported, see the diff against the probe below)
$ the compiled nonempty instance of the main target (the other 7 examples: 1238-1267, 1271-1291, 1300-1317, 1320-1335, 1340-1361, 1365-1379, 1382-1393)
L1219-1233:
example (hPT : KLPT 3 1 1) :
    ∃ C : ℝ, 0 < C ∧
      (‖KLKpi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLInduct_instσ KLInduct_insta ∅‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (4 - 1)) ∧
      (‖KLKpi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLInduct_instσ KLInduct_insta
          {((0 : Fin 4), (2 : Fin 4))}‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (4 - 1)) ∧
      (‖KLKpi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLInduct_instσ KLInduct_insta
          {((1 : Fin 4), (3 : Fin 4))}‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (4 - 1)) := by
  obtain ⟨C, hC, H⟩ := KLKpiBoundPin_holds 3 4 1 1 (by norm_num) (by norm_num) one_pos one_pos hPT
    1 one_pos
  exact ⟨C, hC, H KLinstPar KLInduct_instσ ∅ KLInduct_insta,
    H KLinstPar KLInduct_instσ {((0 : Fin 4), (2 : Fin 4))} KLInduct_insta,
    H KLinstPar KLInduct_instσ {((1 : Fin 4), (3 : Fin 4))} KLInduct_insta⟩
$ probe diff (scratchpad/T2115/probe_diff.py)
probe 503-750 (248 lines) vs `section Bound` of KLInduct.lean (219 lines): 61 differing lines; headers among them:
-def KLBoundAt (d n : ℕ) (κ gmax : ℝ) : Prop :=
-theorem KLBparam_nonneg (d L : ℕ) (g t : ℝ) (K : ℕ) : 0 ≤ Bparam d L g t K := by
-theorem KLBparam_le_zero {d : ℕ} (L : ℕ) (g t : ℝ) (K : ℕ) :
-theorem KLedge_sup {d : ℕ} {gmax : ℝ} (hD : KLDecay d gmax) :
+theorem KLedge_sup {d : ℕ} {κ gmax : ℝ} (hPT : KLPT d κ gmax) :
-theorem KLBoundAt_two {d : ℕ} {κ gmax : ℝ} (hκ : 0 < κ) (hD : KLDecay d gmax) :
+theorem KLBoundAt_two {d : ℕ} {κ gmax : ℝ} (hκ : 0 < κ) (hPT : KLPT d κ gmax) :
-theorem KLBoundAt_three {k : ℕ} {κ gmax : ℝ} (hκ : 0 < κ) (hD : KLDecay (k + 2) gmax)
-    (hS : KLShort (k + 2) κ gmax) : KLBoundAt (k + 2) 3 κ gmax := by
+theorem KLBoundAt_three {k : ℕ} {κ gmax : ℝ} (hκ : 0 < κ) (hPT : KLPT (k + 2) κ gmax) :
(the rest: `KLBparam_nonneg/_le_zero` calls replaced by the merged `KLIndStepA_Bparam_nonneg/_le_zero`; `hD` by `hPT.decay`; `hS` by `hPT.short`)
$ name-clash: every new declaration (31: 24 public, 7 private) vs declarations in RBM3D/, RBM3D.lean
new declarations: 31 (public 24, private 7); declaration clashes in main: 0 []
RBM3D/Loop/KLUnique.lean:26:  probe section needs `KLBoundAt` (KL11) and is not here.
$ ports (RBM2D, read-only, commit c9a24cf; RBM2D HEAD 9e0f275)
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Loop/KBoundCut.lean RBM2D/Loop/KBound.lean
 RBM2D/Loop/KBound.lean    |  83 ++++++++----------------
 RBM2D/Loop/KBoundCut.lean | 158 +++++++---------------------------------------
 2 files changed, 49 insertions(+), 192 deletions(-)
file:line at c9a24cf of the ported statements (the mapping to the new names is item 4 of the narrative):
KBoundCut.lean:1528  treeValW_leaf_smul
KBoundCut.lean:1550  treeValW_long_cut
KBoundCut.lean:1908  norm_sum_SB_mul_le
KBoundCut.lean:1927  norm_cut_le
KBoundCut.lean:1954  Kpi_cut
KBound.lean:316  Kpi_step
KBound.lean:423  Kpi_bound_prec
KBound.lean:465  Kbound_prec
```

Narrative (each claim is read off the scripts above or the file):
1. One new file `RBM3D/Loop/KLInduct.lean` (1397 lines, branch `t/T2115`, HEAD `177e4e3`); no merged file and not `Test/Axioms.lean` is touched. §1 pins, §2 probe section 6, §3-§5 the cut,
   §6 the layer `π = ∅`, §7 step, induction and pins, §8 eight compiled `example`s.
2. Reused, not copied: `KLsum_cut`, `KLtreeValW_cut`, `KLgval_in_eq/_out_eq`, `KLFIn`, `KLFOut`, `KLwIn`, `KLshiftOut`, the vertex maps (KLCut); `KLKpi_eq_sum_SigmaPi`,
   `KLtreeValW_eq_sum_selfW`, `KLK_eq_sum_Kpi` (KLTree); `KLmolecule_holds` (KLMolecule); `KLindStepPin_holds` (KLIndStepB); `KLIndStepA_{Theta_norm_le, thetaEdge_long, Bparam_nonneg,
   Bparam_le_zero}`, `KLlat_inv_le_Bparam`; `sum_norm_SB_row`, `mul_Theta_of_three_le`; the private `sigmaIn`, `sigmaOut`, `Flong_eq_iff_cut`, `prod_leaves_cut`, `exists_innermost`,
   `Flong_subset_diagonals`, `Flong_subset` of `KLSumZeroWard.lean` through `open private` (precedent `KLIndStepA.lean:40-43`).
3. Target 1: merged twins used are `KLIndStepA_Bparam_nonneg`, `KLIndStepA_Bparam_le_zero` (for the probe's `KLBparam_nonneg`, `KLBparam_le_zero`). `KLTheta_eq_zero` (form `a-b`) is ported;
   its nearest merged lemma `KLIndStepA_Theta_apply_sub` has form `b-a`. `KLedge_sup`, `KLedge_l1`, `KLstar_le`, `KLone_le_rpow`, `KLBoundAt_one/two/three` have no merged twin and are ported
   (probe diff above).
4. Ports (RBM2D, file:line above): `treeValW_leaf_smul`, `treeValW_long_cut` -> `KLInduct_treeValW_leaf_smul`, `KLInduct_treeValG_cut`; `Kpi_cut` -> `KLKpi_cut`; `norm_sum_SB_mul_le`,
   `norm_cut_le` -> `KLInduct_norm_sum_SB_mul_le`, `KLInduct_norm_cut_le`; `Kpi_step` -> `KLKpi_step`; `Kpi_bound_prec` -> `KLInduct_KpiBoundAt_holds`; the `n ≥ 3` branch of `Kbound_prec` ->
   `KLInduct_BoundAt_of_Kpi`. New: `KLInduct_inner_eq` (the inner polygon is a root sum of `KLindStepAt`), `KLInduct_Kpi_empty_slice/_short/_bound` (the layer `π = ∅`; replace RBM2D's
   `KpiEmptyAt`; `InnerSumAt` is replaced by the merged `KLindStepPin_holds`).
5. The induction (module docstring has the details): strong induction on `n ≥ 3` for `KLKpiBoundAt d n κ gmax`. At `n`: `π = ∅` by `KLInduct_Kpi_empty_bound`; `KLTSPlong n σ π = ∅` gives
   `K^{(π)} = 0`; else an innermost `J ∈ π`, `KLKpi_cut`, inner polygon `k = j-i+1` and outer polygon `n'' = n-(j-i)+1`, both in `[3, n-1]` (`hw2`, `hwn` in the proof); inner root sum `≺
   B^{k-2}` (`KLindStepPin_holds` at `τ/2`), outer `≺ B^{n''-1}` (induction hypothesis at `τ/2`), `∑_w|S_{uw}| = 1`, `|t| ≤ 1`, `(k-2)+(n''-1) = n-1`, `L^{τ/2}L^{τ/2} = L^τ`. The constant
   `C₀ + ∑_{w<n} C_in(w+1) C_out(n-w+1)` (by `choose`) depends on `d, n, κ, gmax, τ` only. `KLboundPin_holds`: `n ≤ 3` by `KLBoundAt_one/two/three`, `n ≥ 4` by `KLK_eq_sum_Kpi` and the
   `2^{|diagonals n|}` layers.
6. T2106a (the `tSΘ` leaf) is settled: the merged `KLindStepAt` suffices. The cut edge carries `Θ^{(σ_i,σ_j)} - I = ξ_J S^{(B)} Θ^{(σ_i,σ_j)}` (`mul_Theta_of_three_le`, step `hEJ` of
   `KLInduct_treeValG_cut`); `Q = Θ^{(σ_i,σ_j)}` is the standard leaf at the glue vertex of the outer polygon, the root leaf of the inner polygon is the identity at the glued label, the
   other inner leaves are `Θ^{(σ_k,σ_{k+1})}`; `KLInduct_inner_eq` identifies the inner polygon with the summand of `KLindStepAt` at `r = Fin.last`, and `σ r ≠ σ (r+1)` since `J` is long
   (`hroot`).
7. Ticket text corrected ("factor of modulus 1, `∏ m`"): the cut prefactor is exactly `t`, for every charges (`hprod`, from `prod_leaves_cut`).
8. Registry: the probe's `KLDecay` binders fail the pre-check (fixture above), so `KLedge_sup`, `KLBoundAt_two`, `KLBoundAt_three` take `KLPT`. Then the pre-check exits 0, 83 premises before
   and after, 7 more theorems carry `KLPT` (8 -> 15), no `Test/Axioms.lean` line is needed: `KLBoundAt` is concluded by `KLBoundAt_one/two/three`, `KLKpiBoundAt` by
   `KLInduct_KpiBoundAt_holds`, the two `...Pin`s by the `_holds` theorems.
9. `KLoopBound` (`Loop/KBound.lean:74`) is implied by `KLboundPin` for `K = KLK` at `κ := 2 - |E|`, `gmax := g` (with `3 ≤ d`, `3 ≤ L`, `1 ≤ W`, `0 < g`, `|E| < 2`, `KLPT d (2-|E|) g`): both
   read `‖K‖ ≤ C L^τ ((W^d)⁻¹ B_{t,0})^{n-1}` with `∃ C` after `∀ τ`, and the `C` of `KLBoundAt` is uniform in `L, W, g`. Not written as a theorem: one concluding `KLoopBound` would count as
   proving that owed premise for the registry scan. The registry shows `RBM.Loop.KLoopBound: 0` carriers, so KL14 can delete it.
10. `KLShort` enters as `hPT.short`; `KLShort_holds` is not needed. `KLedge_l1` keeps the probe's hypothesis `KLShort`, which `KLShort_holds` (KLMolecule) concludes.
11. Instances: `KLinstPar` (`d = 3`, `L = 5`, `W = 2`, `g = 1/2`, `E = 0`, `t = 9/10`, `κ = gmax = 1`), `σ = (+,+,-,-)`, spread labels `KLInduct_insta`: `KLKpiBoundPin_holds` at `n = 4` for
   three layers, `KLboundPin_holds` at `n = 1, 2, 3, 4`, `KLBoundAt_one/two/three`, `KLKpi_step`, `KLInduct_Kpi_empty_bound` (`n = 4, 5`), `KLKpi_cut` (`n = 4`, `J = (0,2)`, `F₀ = {J}`,
   hypotheses by `decide`, `TSP_four`, `norm_mul_mSigma_lt_one`), `KLedge_sup`, `KLedge_l1`, `KLstar_le`, `KLone_le_rpow`, `KLTheta_eq_zero`. Only `KLPT 3 1 1` stays a hypothesis. The
   numerics of (a) were not re-run.

## (c) Verified Mathlib names (script chk_names.lean, `import RBM3D.Loop.KLInduct`: `checked 74 names; missing: [not_forall]`; `not_forall` is `Classical.not_forall` exported to the root, it resolves in the file)
Complex.{norm_natCast, norm_real, re_le_norm}; Fin.{ext, last_add_one, le_def, lt_def, sum_univ_two, val_add, val_add_one_of_lt, val_last, val_one', val_zero}; Fintype.{card_fin,
   piFinset_univ}; Function.{update_of_ne, update_self}; List.ofFn_succ; Nat.{cast_nonneg, mod_eq_of_lt, mod_self, strong_induction_on, sub_add_cancel, sub_self}; Real.{exp_le_one_iff,
   norm_of_nonneg, one_le_rpow, rpow_add, rpow_nonneg}
Finset.{card_powerset, card_univ, mem_filter, mem_range, mem_singleton, mem_univ, mul_prod_erase, mul_sum, ne_of_mem_erase, nonempty_iff_ne_empty, prod_congr, prod_const, prod_le_prod₀,
   prod_nonneg, prod_univ_sum, single_le_sum, sum_add_distrib, sum_comm, sum_congr, sum_const, sum_empty, sum_fiberwise, sum_filter, sum_le_sum, sum_mul, sum_nonneg}; Matrix.{one_apply,
   one_mul, smul_apply, smul_mul, transpose_apply, transpose_one, transpose_smul}
root: add_halves, inv_anti₀, mul_inv_cancel₀, nsmul_eq_mul, one_le_pow₀, pow_le_pow_left₀, norm_sum_le, norm_prod, norm_inv, norm_pow, mul_pow, not_forall (= Classical.not_forall)
Signatures (script chk3.lean): `Finset.prod_le_prod₀ : (∀ i ∈ s, 0 ≤ f i) → (∀ i ∈ s, f i ≤ g i) → ∏ f ≤ ∏ g` (used); `Finset.prod_le_prod` takes only the second hypothesis (ordered-monoid
   form, not used); `Finset.sum_fiberwise s g f : ∑ j, ∑ i ∈ s with g i = j, f i = ∑ i ∈ s, f i`; `Finset.prod_univ_sum t f : ∏ i, ∑ j ∈ t i, f i j = ∑ x ∈ Fintype.piFinset t, ∏ i, f i (x
   i)`; `inv_anti₀ : 0 < b → b ≤ a → a⁻¹ ≤ b⁻¹`; `Real.rpow_add : 0 < x → ∀ y z, x ^ (y + z) = x ^ y * x ^ z`; `Finset.single_le_sum : (∀ i ∈ s, 0 ≤ f i) → a ∈ s → f a ≤ ∑ x ∈ s, f x`.
Verified absent: none needed. `import Mathlib` has no olean in this tree (the scripts import `RBM3D.Loop.KLInduct`).

## (d) Open issues and paper-delta candidates
- T2115a (induction scheme; paper `A_deterministic_estimates.tex:678-680, 791-805`): the paper proves `(eq:K-pi-bound)` for the generalized `K̃^{(π)}` (leaves `Θ̃ ∈ {Θ, tSΘ}`, `(eq:wtKpi)`)
   by induction on the number of molecules `r`, cutting off a leaf molecule (`(eq:Kpipi)`: `B^{l-1} B^{n-l}`). Lean: induction on the number `n` of polygon vertices, cutting a tree at an
   innermost long edge (RBM2D `Kpi_cut`), for the standard `K^{(π)}` only (the pin `KLKpiBoundAt` is for `KLKpi`, the case `Θ̃ = Θ` of the paper's `K̃`); `k = l+1` and `n'' - 1 = n - l` give
   the same exponents. The `tSΘ` leaf never appears: the glued edge is `ξ_J S^{(B)}` times a standard leaf (T2106a answered).
- T2115b (ticket text, not the paper): the cut prefactor is `t` (`∏_{in} m ∏_{out} m = (∏ m) m(σ_i) m(σ_j)` with the merged `KLKpi`), not "modulus 1, `∏ m`"; RBM2D's `ξ_J` becomes `t`.
- T2115c (probe vs file, not the paper): `KLedge_sup`, `KLBoundAt_two`, `KLBoundAt_three` take `KLPT d κ gmax` where the probe takes `KLDecay d gmax` (and `KLShort`); reason: fixture in (b).
   To state them with `KLDecay`, a ticket must first register `KLDecay` in `Test/Axioms.lean` (class borrowed/owed is the dispatcher's call).
- The proved pins keep the forms fixed by T2004: loss `L^τ` for every `τ > 0` (the paper's `≺`), `|E| ≤ 2-κ`, `0 < g ≤ gmax`, `0 ≤ t < 1`, constants `C(d, n, κ, gmax, τ)`. DECISIONS §29: (1)
   `t < 1` is in `KLPar`; (3) no `L`-`W` relation is used, `W` occurs only in the prefactor of `(eq_K-Kpi)`; (4) `n` is fixed in the pins; (2) the `ilambda`-boundary of case (ii) does not occur (no `ilambda` in these pins). No further delta.
- For KL12: `KLKpi_cut` mentions the private `sigmaIn`, `sigmaOut` (`KLSumZeroWard.lean:70, 75`); a consumer names them with `open private sigmaIn sigmaOut from RBM3D.Loop.KLSumZeroWard`.
   `KLInduct_Kpi_empty_bound` and `KLKpi_step` are reusable.
- Not done: a Lean bridge `KLoopBound` from `KLboundPin` (item 9, deliberately); `KLPT 3 1 1` remains an instance hypothesis (limit checks for its parts are in (a)).
