Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 20:49:51 UTC 2026 (`date -u`)

Notation: `N = Nsz sz n`, `t* = N^{-1+τs}`, `a = e^{-t*/2}`, `t = 1-e^{-t*}`, `ζ = w+E`, `W` block side, `τ = τs/8`. Scripts (Python only) are in the scratchpad `T2213/`: `ex.py thr.py sc.py gue.py band.py`.

### (i) Exponent table

| quantity | value | constraint | slack |
|---|---|---|---|
| `𝔠d < 1` | `1/2`; `3/10` (`d=3`; `(𝔠,𝔡)=(1/6,1/10),(1/10,1/20)`) | `W ≥ N^𝔠`, `W^d < N` (`L ≥ 3`) | `1/2`; `7/10` |
| `𝔡 ≤ d/2` | `1/10`, `1/20` vs `3/2` | `WO`, `W → ∞` | `1.4`; `1.45` |
| `τs ≤ 𝔠𝔡 < 1/2` | `1/60`; `1/200` | `𝔠𝔡 ≤ 𝔠d/2` | `0.4833`; `0.495` |
| new term `W^{τs/8} t* ≤ N^{-1+9τs/8}` (`W ≤ N`) | exponent `0.98125`; `0.99438` | `> 3τs/8` iff `τs < 2/3` (`τ=τs/8`); `τ→0` limit `8/11` | gap `0.975`; `0.9925` |
| floor `W^{τs/8-2𝔡} ≤ N^{-15τs/16}` | `0.015625`; `0.004687` | `τs ≤ 𝔠𝔡`, `𝔠<1` | vs `3τs/8`: `0.009375`; `0.002812` |
| local term `W^{τs/8}(N Im ζ)⁻¹ ≤ 8c₀⁻¹N^{-7τs/8}` | `0.014583`; `0.004375` | `Im ζ = Im w ≥ c₀t*/8` | vs `3τs/8`: `0.008333`; `0.0025` |
| bridge `t*(K+Lp(|E|+1))`, `t ≤ t*` | exponent `1-τs = 0.98333`; `0.995` | `> 3τs/8` | `0.9771`; `0.9931` |
| target `N^{-3τs/8}` | `0.00625`; `0.001875` | min of the five rates above is larger | min slack `0.008333`; `0.0025` |
| box (`δ=1/4`, `E=0`, `UNDens'.mono` of `un_dens'_msc_zero`) | `c=9/100`, `K=1`, `Lp=62` | fixed before `∀ᶠ n` | n/a |
| target 4 constants | `c₁=1/16`, `c₀=9/99200=9.0726e-5`, `C₀=514.5`, bridge `K+Lp(|E|+1)=63` | `0<c₀≤c₁≤δ/(4(1+A))` | `c₁/c₀=688.9` |
| OU time | `t*/2 ≤ t ≤ t* ≤ min(c₀,1/2)`, `a⁻¹-1 ≤ t*`, `a⁻¹ ≤ 2` | `t* ≤ 1` | `max (a⁻¹-1)/t* = 0.6487` (at `t*=1`) |
| strip heights | `Im ζ ≥ c₀t/4 ≥ c₀t*/8 ≥ N^{-1+τs/8}`; `|Re a⁻¹ζ - E| ≤ 2c₁+t*|E| ≤ δ`; `Im a⁻¹ζ ≤ 1` | `τs/8 < τs` | `ln N ≥ 780.8` |
| `ε_n` (see ticket) `≤ c₀` | `2(N^{-15τs/16}+8c₀⁻¹N^{-7τs/8})+N^{-1+9τs/8}+63N^{-1+τs}` | exact ε is smaller (`a⁻¹` factor absent in the C form, `mV_vOUC` exact) | `ln N ≥ 1466.6` |
| density `C₀(ε_n+t) ≤ N^{-3τs/8}`, `ρ₀=ρ n` | gaps as rows above; `tendsto_nhds_unique` on `𝓝[>]0` | | `ln N ≥ 2198.8` |
| (2.2), `η∈[g,1/2]`, `g=N^{-1+τs/4}` | `Im mV = Im sN(ouInit)(x+E+iη)`; error `N^{-15τs/16}+N^{-τs/8}+N^{-1+9τs/8} ≤ c/2`; `|x| ≤ G=N^{-τs/4} ≤ δ` | `Im ∈ [c/2, K+c/2]` | `ln N ≥ 1488.5`; `≥ 332.7` |
| (2.2), `η∈(1/2,10]` | `η Im mV` nondecreasing, `Im mV ≤ 1/η` | `Im mV ∈ [c/40, 2]` | pin `c=c_box/40`, `C=2K+c_box+2` |
| (2.3) | `ouInit = aH+(1-a)μ`, Weyl by convexity, `|λ_i(H)|,|λ_i(μ)| ≤ N^{CV₀}` (`UNNormBound` event, `UNMeanBound`) → `|v_i| ≤ N^{CV₀}+|E| ≤ N^{CV₀+1}` | `N^{CV₀}(N-1) ≥ |E|` | `N ≥ |E|+2` |
| probability | bad `⊆` `UNTrLocalInit'` bad at `(τs,τs/8,τs/8,D+1)` `∪` `UNNormBound` bad at `D+1`; `UNMeanBound` deterministic | `2N^{-D-1} ≤ N^{-D}` | `N ≥ 2` |
| band `UNTrLocalInit'` (`δ=1/4 → δ'=1/2`, `K=1`, `Lp=10000/81`) | window `(1+t*)/4 ≤ 1/2`; `Im ζ ≤ a⁻¹ ≤ 2`; `Bctl(1-Im ζ) ≤ Bctl(1-Im z)`; const `Cb=K+Lp(|E|+δ'+2)+(1+Lp)=434.1` | `t* ≤ 1`; `W^{τ/2} ≥ 2` (`2W^{τ/2} ≤ W^τ`); `Cb ≤ W^τ`; `W→∞`, `τs<1` so `t*→0` | eventual in `n`, per `τ` (`τ=1/480`: `ln W ≥ 665 / 2915`) |
| refutation, `R_n = 8N^{CV₀+2}` (indep. of `τs`) | `1-a ≥ t*/4` (`t* ≤ 1`), `t* ≥ N^{-1}`, so `(1-a)R_n ≥ 2N^{CV₀+1}` | `2N^{CV₀+1}-N^{CV₀}-|E| > N^{CV₀+1}` | `N ≥ |E|+2` |
| refutation, rank-one transfer | `‖sN(diag γ')-sN(diag γ)‖ ≤ 2/(N Im z) ≤ 2 Bctl(1-Im z)` (`Bctl ≥ (N η)⁻¹`) | `W^{τ/2}+2 ≤ W^τ` iff `W^{τ/2} ≥ 2` | eventual (`W→∞`) |
| two data, one model (`η=N^{-1/2}`) | `|ρ-ρ̃| ≤ (Lp+L̃p)η/π+(2/π)W^τ(Bctl(1-η)+t*)`; exponents `1/2`, `15τs/16`, `1/2-τs/8`, `1-9τs/8` | `> 3τs/8` | min gap `0.00937`; `0.00281` |

Where `d` enters: `W^d < N` (`𝔠d<1`), `lam²W^d ≥ W^{2𝔡}` (floor `W^{-2𝔡}`), `W ≤ N` (`W^τ ≤ N^τ`), `𝔠𝔡 < 1/2` (`τs<2/3`).

Consumer check (target 4 `FreeConvRegular.lean:1234-1250`, token by token): `hbox`,`hlip` = the `UNDens'` box at `n` (`mref=m n`, `E₀=E`, `A=|E|`); `0<t≤c₀`, `s=1-t=e^{-t*}`, `0≤ε≤c₀`; strip closeness `‖mV v w - (√s)⁻¹ m((√s)⁻¹(w+E))‖ ≤ ‖sN(ouInit)(ζ)-m(ζ)‖ + ‖m(ζ)-a⁻¹m(a⁻¹ζ)‖`, with `√s=a`, `mV(vOUC)(w)=sN(ouInit)(w+E)`, second term `≤ (a⁻¹-1)K+Lp(a⁻¹-1)|ζ| ≤ t*(K+Lp(|E|+1))` (both points in the box); conclusions `|ρ'-ρ_0| ≤ C₀(ε+t)`, `ρ₀=ρ n`. `UNCoreC''` against `T2197.md:30` ("BA-C1b targets `UNCoreC″` (with `UNTrLocalInit′`, `UNMeanBound`)"): same hypothesis list. `UNTrLocalInit'` vs supervisor B2 "BA": coupling `λe^{t*/2}`, shift `C t*` absorbed by `W^τ t*`.

Two models, same data (the variant behind T2208a): the conclusion reads (2.3) through `UNNormBound`+`UNMeanBound`+Weyl, and (2.2), `v⊞sc_t` near `0` through `sN(ouInit)` on the strip (`UNTrLocalInit'`), all observed: PASS. The merged `UNStep1GoodC'` fails it because `‖mean‖` is not observed (a change of `R_n` in one eigenvalue of `mean` moves `sN` by `≤ 2/(N Im z)`, below the tolerance). `UNTrLocalInit'`, `UNMeanBound`: one datum each, no conclusion, no test.

### (ii) One concrete nondegenerate instance

Data: `d=3`, `sz0` (`L_n=4(n+1)`, `W_n=(2(n+1))^5`, `lam_n=(2(n+1))^{-6}`), `(𝔠,𝔡)=(1/6,1/10)`, band model `(UNModel.band sz0).toC` (mean `0`), `m=msc`, `E=0`, `ρ=rhoSC 0`, `δ=1/4`, `δ'=1/2`, `κ=1`, `τs=1/60=𝔠𝔡`, `D=1`, `CV₀=1`, `E'=0`, `k=1`, `bump`. Deterministic hypotheses: `3≤3`, `Admissible` (`sz0_adm`), `UNDens'` (box), `UNMeanBound` (mean `0`), `IsTestFun bump`, `|0|<2`, `1≤1`. Kept as hypotheses (other gates' pins, argued below): `UNLocAvgBand`, `UNTrLocalBandRow` (→ `UNTrLocal sz0 band msc 0 (1/2)`), `UNNormBandRow`/`UNNormBound`, `UNL32`, `UNGUELocal`, `UNGreenCorrAllC`, `UNClaimAllC`. The conclusions are eventual in `n`; thresholds below are not witnesses.

`python3 ex.py` (exact `Fraction`; both pairs shown in table (i)); lines used:
```
sz0 n=0: L=4 W=32 lam=0.015625 N=2097152  N^(1/6)=11.31<=W:True  W^(-3/2+1/10)=0.00781<=lam<=10:True  ln(L^3)/ln N=0.286
sz0 n=1: L=8 W=1024 lam=0.000244141 N=549755813888  N^(1/6)=90.51<=W:True  W^(-3/2+1/10)=6.1e-05<=lam<=10:True  ln(L^3)/ln N=0.231
sz0 admissible (1/6,1/10) algebraic check on sampled m<=1e6: True
```
`python3 thr.py` (mpmath, 60 digits; bound forms of the proof, `K=1, Lp=62, c=9/100, δ=1/4, τs=1/60`):
```
delta=1/4 box c=9/100 K=1 Lp=62: c1=0.0625 c0=9.0725806e-5 (9/99200=9.0725806e-5) C0=514.5 bridge K+Lp(|E|+1)=63.0
E2 t*<=min(c0,1/2): ln N >= 9.46543      E3 N^{-1+ts/8}<=c0 t*/8: ln N >= 780.83
E4 eps_n<=c0: ln N >= 1466.6             E5 C0(eps_n+N^{-1+ts})<=N^{-3ts/8}: ln N >= 2198.81
E6 (2.2) N^{-15ts/16}+N^{-ts/8}+N^{-1+9ts/8}<=c/2: ln N >= 1488.52   E7 G<=delta: ln N >= 332.711
(E1, E8, E9: ln N >= 1.0)  max threshold ln N = 2198.81
ln m=130: ln N=2354.5561 ln W=653.46574  W>=N^{1/6}:True  W<=N:True ; all E-conditions at ln m=130: True
true W^{ts/8}(Bctl(1-g)+t*)=0.00021406 <= c/2=0.045 : True
tau=ts/8=0.0020833: W^{tau/2}>=2 iff ln W >= 665.421 ; at ln m=130 ln W=653.466
```
So every eventual condition of `step1GoodC''_det` holds from `ln N ≈ 2.2·10^3` (`ln m ≥ 121.3` on `sz0`), as T2208 `(a)` (`2157.2`); the instances stay eventual (§56). The rank-one and band conditions `W^{τ/2} ≥ 2` are per-`τ` thresholds (`ln W ≥ 2ln2/τ`), not used by the instance of `step1GoodC''` (it calls `UNTrLocalInit'` only at `τ=τs/8` through the eventual `∀ᶠ`).

`python3 sc.py`, `python3 gue.py`, `python3 band.py` (lines used):
```
a=0.99: max |a^-1 msc(z/a)-msc(z)|/(1-a) = 1.018; at z=i: 0.343   (|Re z|<=1/4, 0<Im z<=1)
a=0.999: max |a^-1 msc(z/a)-msc(z)|/(1-a) = 1.009; at z=i: 0.342
msc on |Re|<=1/2,0<Im<=2: min Im = 0.4033 >= 9/100; max |msc| = 0.999950 <= 1
sampled Lipschitz ratio of msc on that box: 0.516 <= 10000/81=123.5
n=0: t*=6.078e-07  1-a=3.039e-07 >= t*/4=1.519e-07: True  (1-a)*R_0 = 2.242e+13 >= 2N^2 = 8.796e+12: True
1-e^{-x/2}>=x/4 on (0,1]: True
t* in (0,1]: a^-1-1<=t*: True | max (a^-1-1)/t* = 0.6487 | a^-1<=2: True
band instance: window (1+t*)/4+0<=1/2 iff t*<=1; constant Cb=K+Lp(|E|+d'+2)+(1+Lp)=434.1
sz0 n=0: W^d=32768 N=2097152: ln(4N^2)=30.5  W^d/4=8192  ln(4N^2)-W^d/4=-8162 <= -D lnN (D=1: -14.6)
sz0 n=1: W^d=1073741824 N=549755813888: ln(4N^2)=55.5  W^d/4=2.684e+08  ln(4N^2)-W^d/4=-2.684e+08 <= -D lnN (D=1: -27.0)
two-data ts=0.01667: target 3ts/8=0.00625; exponents {'eta=N^-1/2': 0.5, 'floor N^-15ts/16': 0.01562, 'W^tau(N eta)^-1<=N^{ts/8-1/2}': 0.49792, 'W^tau t*<=N^{-1+9ts/8}': 0.98125} min gap 0.00937
```
External hypotheses (O3: kept hypotheses hold for the intended model; limit/numbers):
- `UNDens'` at `msc`, limit clause: `Im msc(iη) = (√(η²+4)-η)/2 → 1` as `η↓0`, so `Im msc(iη)/π → 1/π = rhoSC 0` (`un_msc_imag_axis`, `un_dens'_msc_zero`); box numbers above (`min Im msc=0.4033 ≥ 9/100`, `max‖msc‖ ≤ 1`, Lipschitz ratio `0.516 ≤ 62`).
- `UNTrLocal sz0 band msc 0 (1/2)` from `UNLocAvgBand`: the paper's (G_bound_ave) (`1_2_Intro_model_result.tex:391`, Thm `MR:locSC`) in `𝐃_{κ,ε}`, `κ=1`, `|Re z| ≤ 1/2 ≤ 2-κ`, tolerance `W^τ B_{η,0}`, `W^{-d}B_{η,0}=Bctl(1-η) ≥ (Nη)⁻¹` and `≥ W^{-d}(lam²+η)⁻¹`; the tracial value is the average of the `L^d` block averages (no loss). `sz0`: `n=0` `L=4, W=32, lam=1/64, N=2097152`; `n=1` `L=8, W=1024, N=549755813888`; `ln L^d/ln N = 0.286, 0.231`.
- `UNNormBound`, `CV₀=1`: `S_xy=W^{-d}S^{(B)}_{ab} ≤ W^{-d}` (`Gauss/Model.lean:62`; `S^{(B)}` doubly stochastic, `Defs/Block.lean:13-24`), Gaussian tail `P(|h_xy|>1) ≤ 4exp(-W^d/4)`, union over `N²` entries (output lines above: `-8162`, `-2.684e8` against `-14.6`, `-27.0`), `|λ| ≤ N max|h_xy| ≤ N`.
- `UNClaimAllC sz0 (band).toC 0` is the merged `UNClaimAll` for the band model (`UNClaimAllC_toC`, `PinsK.lean:180`; mean `0`); `UNL32`, `UNGUELocal`, `UNGreenCorrAllC` are universally quantified results of other gates (statements over all `sz`/models), not conditions on the band model.
- The merged `UNTrLocalInit` fails along `sz0` for `τs>1/6` (T2208b in numbers, `0.171 t*` against `W^τ Bctl(Im=1)`, `τ=τs/8`): ratio at `m=1,10,100,10³,10⁴`: `0.182, 30.2, 4.9e3, 8.0e5, 1.3e8` for `τs=0.3`; decreasing (`1.1e-2 … 9.8e-8`) for `τs=0.1`; the pin quantifies all `τs<1`, so it is false for the band model along `sz0` (argued, supervisor B1: the ratio grows like a positive power of `m` for `τs>1/6`; not compiled).

Refutation hypotheses satisfiable together (diagonal quantile model, `γ_j=F_sc⁻¹((j-1/2)/N)`, `m=msc`, `CV₀=1`): the quantile (midpoint) rule gives `‖m_γ-msc‖ ≤ (1/N)∫|x-z|⁻²dx ≤ π/(Nη) ≤ W^τ Bctl(1-η)` once `W^τ ≥ π`, uniformly (argued; hence `UNTrLocalInit` holds eventually per `(τs,ε,τ,D)`); `|γ| ≤ 2 ≤ N` gives `UNNormBound`. Numeric check at `N=2000`, window `|Re z| ≤ 1/4`, `Im z ∈ [30/N,1]` (`python3` in-line, output): `max N Im z |m_γ-msc| = 3.42e-04 (≤ π)`, `max|γ|=1.9888`. `UNTrLocalInit'` vs `UNTrLocalInit` on this model and on a GUE sample (`N=2000`; `Bctl` of `(W,L,lam)=(4,3,1/64)`, `d=3`, shape check only):
```
ts=0.3: t*=0.0049 shift at z=i 0.00084 (=0.171 t* -> 0.00084); max dif/tolA(with t*)=0.039 ; max dif/tolB(no t*)=0.049
ts=0.8: t*=0.2187 shift at z=i 0.03708 (=0.171 t* -> 0.03739); max dif/tolA(with t*)=0.273 ; max dif/tolB(no t*)=2.015
GUE ts=0.8: max dif/[W^tau(Bctl+t*)]=0.275; max dif/[W^tau Bctl]=2.018; at z=i: dif=0.03711
```
(`tolA = W^τ(Bctl+t*)`: holds; `tolB = W^τ Bctl`: ratio `2.015 > 1` at `τs=0.8`, so `UNTrLocalInit` fails and `UNTrLocalInit'` holds.)

### Verdicts

- Target 1 pins `UNTrLocalInit'`, `UNMeanBound`, `UNStep1GoodC''`, `UNCoreC''`: PASS (all four are consistent: instances above).
- Target 2 matrix facts and dictionary (`un_eigenvalues_abs_le_convex`, `un_exists_eigenvalues_eq_diagonal`, `stieltjesN_diagonal`, `stieltjesN_vert_le`, `mV_vOUC`, `stieltjesN_ouInit_toC`): PASS (each statement true as written; `stieltjesN_vert_le` termwise `|Im-shift|/(y y')` since `|λ-z| ≥ Im z`; `stieltjesN_ouInit_toC` for any real `t`, `a>0`).
- Target 3 (`UNDens'.mono`, `UNTrLocal.mono`, `unMeanBound_toC`): PASS.
- Target 4 (`unTrLocalInit'_of_unTrLocal`, `unTrLocalInit'_band_zero`): PASS (eventual conditions `t*≤1`, `W^{τ/2}≥2`, `Cb≤W^τ`, `t*→0` as `τs<1`).
- Target 5 `not_UNStep1GoodC'_of_diag`: PASS (argued in full; `R_n` independent of `τs`; `τs=min(𝔠𝔡,1/2)`, `D=1`; the deterministic bad set is empty or everything, `N^{-D}<1`).
- Target 6 `step1GoodC''_det`, `step1GoodC''`: PASS (all rates close, min slack `0.0083`/`0.0025`; `τs<2/3` from `𝔠𝔡<1/2`; constants `c_box/40`, `2K+c_box+2` fixed before `∀ᶠ n`).
- Target 7 instances (`inst_diag_model`, `inst_unTrLocalInit'_band`, `inst_step1GoodC''_band`, `inst_coreC_band''`): PASS (nondegenerate data above; no kept hypothesis is one the band model fails).
- Remark T2213c confirmed: with `τ=τs/8` the new term needs `τs<2/3`; the supervisor's `8/11` is the `τ→0` limit.

Overall verdict: PASS.

## (a′) Preflight corrections — Mon Oct  5 21:25:09 UTC 2026 (`date -u`)
No verdict of (a) changes.  Three numbers/routes of (a) differ from what the proof uses (statements unchanged):
1. Strip bridge constant: (a) row "bridge `K+Lp(|E|+1)=63`" needs `‖ζ‖ ≤ |E|+1`, i.e. `c₁ ≤ 1/8`; the statement of `freeConv_stable_lip`
   (`FreeConvRegular.lean:1234-1250`) exposes only `c₁ ≤ δ/(4(1+A))` (the `1/8` is in its docstring).  The proof uses `Kb = K + Lp(|E|+δ+1)`
   (`= 78.5` at the instance data, `δ = 1/4`); `ε_n` is internal to the proof, so no statement changes.
2. `ε_n = (N^{-15τs/16}+8c₀⁻¹N^{-7τs/8}) + N^{-1+9τs/8} + Kb N^{-1+τs}` (no factor 2: `a⁻¹` is absent in the C form), rate budgets `1/5` each;
   `python3 thr2.py` (mpmath; `τs=1/60, δ=1/4, E=0, c=9/100, K=1, Lp=62`; selected lines of the output):
   c1=0.0625 c0=9.0725806e-5 (9/99200=9.0725806e-5) C0=514.5 Kb=78.5
   e18 N^{-ts/8}<=cb/6                        ln N >= 2015.858
   e9  N^{-9ts/16}<=1/(5C0)                   ln N >= 837.6142
   e12 N^{-ts/2}<=c0/(40C0)                   ln N >= 2308.769
   max threshold ln N = 2308.769
   (a) quoted a maximum `2198.8`; the conditions of `step1GoodC''_det` give `2308.8` (`N^{-τs/2} ≤ c₀/(40 C₀)`); the instances stay eventual (§56).
3. Refutation: `R_n = 4N(N^{CV₀+1} + |E| + |γ_{n,i₀}| + 1)` instead of `8N^{CV₀+2}` (still independent of `τs`; it makes the eigenvalue
   `γ_{i₀} + (1-a)R_n ≥ N^{CV₀+1} + |E| + 1` without deducing `|γ_{i₀}| ≤ N^{CV₀}` from the norm event).  Verdict of Target 5 unchanged.

## (b) Script output — Mon Oct  5 21:25:09 UTC 2026 (`date -u`)
```
$ git log --oneline | head -1 ; git diff --stat main...t/T2213     (worktree RBM3D-wt/T2213, branch t/T2213)
5fae3de T2213: UN-12b C'' re-pin, C-form Step 1, conditional refutation of UNStep1GoodC'
 RBM3D/Test/Axioms.lean         |   11 +-
 RBM3D/Universality/PinsC2.lean | 1711 ++++++++++++++++++++++++++++++++++++++++
 2 files changed, 1718 insertions(+), 4 deletions(-)
$ lake build RBM3D.Universality.PinsC2      (exit 0; 0 lines with "error"; 20 warnings in PinsC2.lean, all linter.style.longLine at lines 13-45 of the module docstring)
Build completed successfully (3343 jobs).
$ lake build   (RBM3D.lean with `import RBM3D.Universality.PinsC2` added after the last import line, temporary, reverted, not committed)  exit 0
info: RBM3D.lean:257:0: axiom audit: 6351 theorems, 2203 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
registry: 2 borrowed + 147 owed + 80 structural + 7 refuted; 108 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
info: RBM3D/Test/AuditNegative.lean:30:0: audit reverse test: an unclassified premise is caught (RBM.Audit.Fixture.FakePremise).
Build completed successfully (4017 jobs).
$ lake build RBM3D   (RBM3D.lean as committed, without the new import)  exit 0 : registry: 2 borrowed + 147 owed + 80 structural + 7 refuted; 110 registered premise(s) carry nothing yet: [RBM

$ lake env lean axioms.lean   (#print axioms of the 31 new public declarations: 5 defs, 26 theorems)
31 of 31 lines end with "depends on axioms: [propext, Classical.choice, Quot.sound]"; 0 others.  First/last:
'RBM.Univ.UNTrLocalInit'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.PinsC2Inst.inst_stieltjesN_ouInit_toC' depends on axioms: [propext, Classical.choice, Quot.sound]

$ registry pre-check: scratch file `import RBM3D` + `import RBM3D.Universality.PinsC2` + `#assert_rbm_axioms`; lake env lean  → exit 0
axiom audit: 6351 theorems, 2203 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 128 (borrowed 1, owed 96, structural 25, refuted 6).
registry: 2 borrowed + 147 owed + 80 structural + 7 refuted; 108 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
RBM.Univ.UNTrLocalInit': 3 [no certificate]    <- "theorems resting on each premise THIS FORMALIZATION owes"
RBM.Univ.UNCoreC'': 1 [no certificate]    <- "theorems resting on each premise THIS FORMALIZATION owes"
RBM.Univ.UNTrLocalInit',    <- "registered premise(s) carry nothing yet" list
RBM.Univ.UNMeanBound,    <- "registered premise(s) carry nothing yet" list
no line "unregistered premise"; counts of the lists in Test/Axioms.lean by script, main vs this branch:
main {'owedProps': 148, 'structuralProps': 79, 'refutedProps': 4} | branch {'owedProps': 147, 'structuralProps': 80, 'refutedProps': 7}
negative test (scratch, restored from a saved copy afterwards; `UNStep1GoodC'` put back into owedProps; lake build RBM3D → exit 1):
2494:error: RBM3D.lean:257:0: axiom audit: 1 refuted premise(s) are also in `borrowedProps`, `owedProps` or `structuralProps`: [RBM.Univ.UNStep1GoodC']

$ pin diff (merged text + the declared substitutions vs the committed file; script pindiff2.py, same substitutions as the ticket)
UNTrLocalInit (PinsK.lean) --1 substitution(s)--> UNTrLocalInit': IDENTICAL
UNStep1GoodC' (PinsDens.lean) --2 substitution(s)--> UNStep1GoodC'': IDENTICAL
UNCoreC' (PinsDens.lean) --2 substitution(s)--> UNCoreC'': IDENTICAL
$ text diff of check section 3 vs the file (stmtdiff.py): 18 identical after whitespace/`Type*` normalisation (the 4 pins and 14 theorem statements), 3 not text-comparable (binders before the colon: UNDens'.mono, UNTrLocal.mono, unMeanBound_toC), 0 different;
$ lake env lean defeqcheck.lean   (check file with the 18 lines `example : T2213_<name> := @RBM.Univ.<name>`, incl. `T2213_step1GoodC''` := `step1GoodC''`) → exit 0, no output

$ name-clash grep (grep -rnF of each new public name and of `PinsC2_`, `PinsC2Inst`, `Universality.PinsC2` in RBM3D/ excl. PinsC2.lean and Test/Axioms.lean, RBM3D.lean, docs/tickets/*.md excl. T2213):
34 patterns; total hits (RBM3D/, RBM3D.lean, docs/tickets): [0, 0, 1] ; patterns with a hit: [('UNMeanBound', 0, 0, 1)]
```

Targets and instances, statements extracted from `RBM3D/Universality/PinsC2.lean` by script (`report_tools.py`: text between the name and `:=`, whitespace collapsed; Mon Oct  5 21:25:48 UTC 2026):
```
def UNTrLocalInit'(sz : Sizes d) (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E δ : ℝ) : Prop := ∀ τs : ℝ, 0 < τs → τs < 1 → ∀ ε τ D : ℝ, 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop, M.μ {ω | ∃ z : ℂ, |z.re - E| ≤ δ ∧ Nsz sz n ^ (-1 + ε) ≤ z.im ∧ z.im ≤ 1 ∧ ((sz.W n : ℕ) : ℝ) ^ τ * (sz.Bctl n (1 - z.im) + ouTStar sz τs n) < ‖stieltjesN (ouInit M n (ouTStar sz τs n) ω) z - m n z‖} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))
def UNMeanBound(sz : Sizes d) (M : UNModelC sz) (CV₀ : ℝ) : Prop := ∀ᶠ n in atTop, ∀ i, |(M.mean_herm n).eigenvalues i| ≤ Nsz sz n ^ CV₀
def UNStep1GoodC'': Prop := ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ), UNDens' m E ρ δ → UNTrLocalInit' sz M m E δ → ∀ CV₀ : ℝ, 0 ≤ CV₀ → UNNormBound sz M.toUNModel CV₀ → UNMeanBound sz M CV₀ → ∀ τs D : ℝ, 0 < τs → τs < 1 → τs ≤ 𝔠 * 𝔡 → 0 < D → ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop, M.μ {ω | ¬ (IsRegular32 (vOUC sz M n τs E ω) (Nsz sz n ^ (-1 + τs / 4)) (Nsz sz n ^ (-(min (τs / 4) ((1 - τs) / 3)))) c C (CV₀ + 1) ∧ ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOUC sz M n τs E ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧ ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧ |ρ' - ρ n| ≤ Nsz sz n ^ (-(3 * τs / 8)))} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))
def UNCoreC'': Prop := UNL32 → UNGUELocal → UNGreenCorrAllC → ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ), UNDens' m E ρ δ → UNTrLocal sz M.toUNModel m E δ → UNTrLocalInit' sz M m E δ → (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz M.toUNModel CV₀ ∧ UNMeanBound sz M CV₀) → UNClaimAllC sz M E → ∀ E' : ℝ, |E'| < 2 → ∀ k : ℕ, 1 ≤ k → ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O → UNUnivDilAt sz M.toUNModel ρ E E' k O
theorem un_eigenvalues_abs_le_convex: ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {A B C : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian) {a R : ℝ}, 0 ≤ a → a ≤ 1 → C = a • A + (1 - a) • B → (∀ i, |hA.eigenvalues i| ≤ R) → (∀ i, |hB.eigenvalues i| ≤ R) → ∀ i, |hC.eigenvalues i| ≤ R
theorem un_exists_eigenvalues_eq_diagonal: ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → ℝ) (hA : (Matrix.diagonal (fun i => (u i : ℂ))).IsHermitian) (j : ι), ∃ i, hA.eigenvalues i = u j
theorem stieltjesN_diagonal: ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → ℝ) {z : ℂ}, 0 < z.im → stieltjesN (Matrix.diagonal (fun i => (u i : ℂ))) z = mV u z
theorem stieltjesN_vert_le: ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}, H.IsHermitian → ∀ (x y y' : ℝ), 0 < y → 0 < y' → ‖stieltjesN H ⟨x, y⟩ - stieltjesN H ⟨x, y'⟩‖ ≤ |y - y'| / (y * y')
theorem mV_vOUC: ∀ {d : ℕ} (sz : Sizes d) (M : UNModelC sz) (n : ℕ) (τs E : ℝ) (ω : Sizes.SeqΩ sz) {w : ℂ}, 0 < w.im → mV (vOUC sz M n τs E ω) w = stieltjesN (ouInit M n (ouTStar sz τs n) ω) (w + E)
theorem stieltjesN_ouInit_toC: ∀ {d : ℕ} (sz : Sizes d) (M : UNModel sz) (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz) {z : ℂ}, 0 < z.im → stieltjesN (ouInit M.toC n t ω) z = ((Real.exp (-t / 2) : ℝ) : ℂ)⁻¹ * stieltjesN (M.H n ω) (((Real.exp (-t / 2) : ℝ) : ℂ)⁻¹ * z)
theorem UNDens'.mono{m : ℕ → ℂ → ℂ} {E : ℝ} {ρ : ℕ → ℝ} {δ δ' : ℝ} (hδ : 0 < δ) (hδδ' : δ ≤ δ') (h : UNDens' m E ρ δ') : UNDens' m E ρ δ
theorem UNTrLocal.mono{d : ℕ} {sz : Sizes d} {M : UNModel sz} {m : ℕ → ℂ → ℂ} {E δ δ' : ℝ} (hδδ' : δ ≤ δ') (h : UNTrLocal sz M m E δ') : UNTrLocal sz M m E δ
theorem unMeanBound_toC{d : ℕ} (sz : Sizes d) (M : UNModel sz) (CV₀ : ℝ) : UNMeanBound sz M.toC CV₀
theorem unTrLocalInit'_of_unTrLocal: ∀ {d : ℕ} (sz : Sizes d) {𝔠 𝔡 : ℝ}, sz.Admissible 𝔠 𝔡 → ∀ (M : UNModel sz) (m : ℂ → ℂ) (E δ δ' K Lp : ℝ), 0 < δ → δ < δ' → (∀ z : ℂ, |z.re - E| ≤ δ' → 0 < z.im → z.im ≤ 2 → ‖m z‖ ≤ K) → (∀ z z' : ℂ, |z.re - E| ≤ δ' → 0 < z.im → z.im ≤ 2 → |z'.re - E| ≤ δ' → 0 < z'.im → z'.im ≤ 2 → ‖m z - m z'‖ ≤ Lp * ‖z - z'‖) → UNTrLocal sz M (fun _ => m) E δ' → UNTrLocalInit' sz M.toC (fun _ => m) E δ
theorem unTrLocalInit'_band_zero: ∀ {d : ℕ} (sz : Sizes d) {𝔠 𝔡 : ℝ}, sz.Admissible 𝔠 𝔡 → UNTrLocal sz (UNModel.band sz) (fun _ => msc) 0 (1 / 2) → UNTrLocalInit' sz (UNModel.band sz).toC (fun _ => msc) 0 (1 / 4)
theorem not_UNStep1GoodC'_of_diag: UNStep1GoodC' → ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ (M : UNModelC sz) (γ : ∀ n : ℕ, Idx d (sz.L n) (sz.W n) → ℝ), (∀ n ω, M.H n ω = Matrix.diagonal (fun i => (γ n i : ℂ))) → (∀ n, M.mean n = Matrix.diagonal (fun i => (γ n i : ℂ))) → ∀ (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ), UNDens' m E ρ δ → UNTrLocalInit sz M m E δ → ∀ CV₀ : ℝ, 0 ≤ CV₀ → UNNormBound sz M.toUNModel CV₀ → False
theorem step1GoodC''_det: ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ), UNDens' m E ρ δ → ∀ CV₀ : ℝ, 0 ≤ CV₀ → UNMeanBound sz M CV₀ → ∀ τs : ℝ, 0 < τs → τs < 1 → τs ≤ 𝔠 * 𝔡 → ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ ω : Sizes.SeqΩ sz, (∀ z : ℂ, |z.re - E| ≤ δ → Nsz sz n ^ (-1 + τs / 8) ≤ z.im → z.im ≤ 1 → ‖stieltjesN (ouInit M n (ouTStar sz τs n) ω) z - m n z‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (τs / 8) * (sz.Bctl n (1 - z.im) + ouTStar sz τs n)) → (∀ i, |(M.herm n ω).eigenvalues i| ≤ Nsz sz n ^ CV₀) → (IsRegular32 (vOUC sz M n τs E ω) (Nsz sz n ^ (-1 + τs / 4)) (Nsz sz n ^ (-(min (τs / 4) ((1 - τs) / 3)))) c C (CV₀ + 1) ∧ ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOUC sz M n τs E ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧ ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧ |ρ' - ρ n| ≤ Nsz sz n ^ (-(3 * τs / 8)))
theorem step1GoodC'': UNStep1GoodC''
def diagModel{d : ℕ} (sz : Sizes d) (γ : ∀ n : ℕ, Idx d (sz.L n) (sz.W n) → ℝ) : UNModelC sz where μ := Sizes.seqP sz prob := inferInstance H := fun n _ => Matrix.diagonal (fun i => (γ n i : ℂ)) herm := fun n _ => PinsC2_diag_herm (γ n) meas := fun n i j => measurable_const mean := fun n => Matrix.diagonal (fun i => (γ n i : ℂ)) mean_herm := fun n => PinsC2_diag_herm (γ n)
theorem inst_diag_model: ∀ {d : ℕ} (sz : Sizes d) (γ : ∀ n : ℕ, Idx d (sz.L n) (sz.W n) → ℝ), ∃ M : UNModelC sz, (∀ n ω, M.H n ω = Matrix.diagonal (fun i => (γ n i : ℂ))) ∧ ∀ n, M.mean n = Matrix.diagonal (fun i => (γ n i : ℂ))
theorem inst_not_UNStep1GoodC'_diag(hS : UNStep1GoodC') (γ : ∀ n : ℕ, Idx 3 (sz0.L n) (sz0.W n) → ℝ) (hTi : UNTrLocalInit sz0 (diagModel sz0 γ) (fun _ => msc) 0 (1 / 4)) (hN : UNNormBound sz0 (diagModel sz0 γ).toUNModel 1) : False
theorem inst_unTrLocalInit'_band: UNLocAvgBand → UNTrLocalBandRow → UNTrLocalInit' sz0 (UNModel.band sz0).toC (fun _ => msc) 0 (1 / 4)
theorem inst_step1GoodC''_band: UNLocAvgBand → UNTrLocalBandRow → UNNormBandRow → ∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop, (UNModel.band sz0).toC.μ {ω | ¬ (IsRegular32 (vOUC sz0 (UNModel.band sz0).toC n (1 / 60) 0 ω) (Nsz sz0 n ^ (-1 + (1 / 60 : ℝ) / 4)) (Nsz sz0 n ^ (-(min ((1 / 60 : ℝ) / 4) ((1 - (1 / 60 : ℝ)) / 3)))) c C (CV₀ + 1) ∧ ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOUC sz0 (UNModel.band sz0).toC n (1 / 60) 0 ω) (1 - Real.exp (-(ouTStar sz0 (1 / 60) n))) mfc ∧ ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧ |ρ' - rhoSC 0| ≤ Nsz sz0 n ^ (-(3 * (1 / 60 : ℝ) / 8)))} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(1 : ℝ)))
theorem inst_step1GoodC''_det_band: ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ ω : Sizes.SeqΩ sz0, (∀ z : ℂ, |z.re - 0| ≤ 1 / 4 → Nsz sz0 n ^ (-1 + (1 / 60 : ℝ) / 8) ≤ z.im → z.im ≤ 1 → ‖stieltjesN (ouInit (UNModel.band sz0).toC n (ouTStar sz0 (1 / 60) n) ω) z - msc z‖ ≤ ((sz0.W n : ℕ) : ℝ) ^ ((1 / 60 : ℝ) / 8) * (sz0.Bctl n (1 - z.im) + ouTStar sz0 (1 / 60) n)) → (∀ i, |((UNModel.band sz0).herm n ω).eigenvalues i| ≤ Nsz sz0 n ^ (1 : ℝ)) → (IsRegular32 (vOUC sz0 (UNModel.band sz0).toC n (1 / 60) 0 ω) (Nsz sz0 n ^ (-1 + (1 / 60 : ℝ) / 4)) (Nsz sz0 n ^ (-(min ((1 / 60 : ℝ) / 4) ((1 - (1 / 60 : ℝ)) / 3)))) c C (1 + 1) ∧ ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOUC sz0 (UNModel.band sz0).toC n (1 / 60) 0 ω) (1 - Real.exp (-(ouTStar sz0 (1 / 60) n))) mfc ∧ ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧ |ρ' - rhoSC 0| ≤ Nsz sz0 n ^ (-(3 * (1 / 60 : ℝ) / 8)))
theorem inst_coreC_band'': UNCoreC'' → UNL32 → UNGUELocal → UNGreenCorrAllC → UNTrLocal sz0 (UNModel.band sz0) (fun _ => msc) 0 (1 / 2) → (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz0 (UNModel.band sz0) CV₀) → UNClaimAllC sz0 (UNModel.band sz0).toC 0 → UNUnivDilAt sz0 (UNModel.band sz0) (fun _ => rhoSC 0) 0 0 1 (bump : (Fin 1 → ℝ) → ℝ)
theorem inst_un_eigenvalues_abs_le_convex: ∀ i, |(PinsC2_diag_herm (fun j : Fin 3 => (1 / 3 : ℝ) * (![2, -1, 1 / 2] : Fin 3 → ℝ) j + (1 - 1 / 3) * (![-1, 1, 0] : Fin 3 → ℝ) j)).eigenvalues i| ≤ 2
theorem inst_un_exists_eigenvalues_eq_diagonal: ∃ i, (PinsC2_diag_herm (![1, 2, 3] : Fin 3 → ℝ)).eigenvalues i = 2
theorem inst_stieltjesN_diagonal: stieltjesN (Matrix.diagonal (fun i => ((![1, 2, 3] : Fin 3 → ℝ) i : ℂ))) (⟨0, 1⟩ : ℂ) = mV (![1, 2, 3] : Fin 3 → ℝ) (⟨0, 1⟩ : ℂ)
theorem inst_stieltjesN_vert_le: ‖stieltjesN (Matrix.diagonal (fun i => ((![1, 2, 3] : Fin 3 → ℝ) i : ℂ))) ⟨0, 1⟩ - stieltjesN (Matrix.diagonal (fun i => ((![1, 2, 3] : Fin 3 → ℝ) i : ℂ))) ⟨0, 2⟩‖ ≤ |1 - 2| / (1 * 2)
theorem inst_mV_vOUC(ω : Sizes.SeqΩ sz0) : mV (vOUC sz0 (UNModel.band sz0).toC 0 (1 / 60) 0 ω) (⟨0, 1⟩ : ℂ) = stieltjesN (ouInit (UNModel.band sz0).toC 0 (ouTStar sz0 (1 / 60) 0) ω) ((⟨0, 1⟩ : ℂ) + (0 : ℝ))
theorem inst_stieltjesN_ouInit_toC(ω : Sizes.SeqΩ sz0) : stieltjesN (ouInit (UNModel.band sz0).toC 0 (ouTStar sz0 (1 / 60) 0) ω) (⟨0, 1⟩ : ℂ) = ((Real.exp (-(ouTStar sz0 (1 / 60) 0) / 2) : ℝ) : ℂ)⁻¹ * stieltjesN ((UNModel.band sz0).H 0 ω) (((Real.exp (-(ouTStar sz0 (1 / 60) 0) / 2) : ℝ) : ℂ)⁻¹ * (⟨0, 1⟩ : ℂ))
```

**Narrative** (facts from the files and the outputs above):
- Delivered: the new file `RBM3D/Universality/PinsC2.lean` (1711 lines, 31 public declarations, 43 private helpers prefixed `PinsC2_`) and the registry edit in
  `RBM3D/Test/Axioms.lean` (+7/-4); `git diff --stat main...t/T2213` lists exactly these two files; no merged file is edited; one commit `5fae3de`.
- Statements: the four pins equal the merged text plus the declared substitutions (pin diff above); every `T2213_<name>` of the check file is
  definitionally the library theorem (18 `example`s elaborate); `step1GoodC''` has type exactly `UNStep1GoodC''`.  No hypothesis added, no statement changed.
- Proof routes are those of the ticket except the three items of (a′): Weyl by `PosSemidef` of `R•1 ∓ A` (`un_eigenvalues_abs_le_convex`), the spectrum of a diagonal
  matrix by `charpoly_eq`/`charpoly_diagonal` (`un_exists_eigenvalues_eq_diagonal`), the scaling `stieltjesN (aH) z = a⁻¹ stieltjesN H (a⁻¹z)` by `Ring.inverse_mul`,
  the rank-one transfer `‖mV u' z - mV u z‖ ≤ 2/(N Im z)` and `(N η)⁻¹ ≤ Bctl (1-η)` for `not_UNStep1GoodC'_of_diag`, and the copies of the T2208 strip/regular/rate/at_n
  with `v = λ(ouInit) - E` (`mV_vOUC`; no `e^{-T/2}` factor), the extra tolerance `N^{-1+9τs/8}`, the bridge `T·Kb`, and (2.3) from `UNNormBound` + `UNMeanBound` + Weyl.
- `unTrLocalInit'_of_unTrLocal` derives `0 ≤ K`, `0 ≤ Lp` from its two bound hypotheses (the box is nonempty); `Im ζ ∈ (1, a⁻¹]` is bridged by `stieltjesN_vert_le`.
- Two declarations (`unTrLocalInit'_of_unTrLocal`, `step1GoodC''_det`) carry `set_option maxHeartbeats 1000000 in` with a reason comment (the module build takes about 15 s).
- Instances (namespace `PinsC2Inst`, data `sz0`, `𝔠=1/6`, `𝔡=1/10`, `E=0`, `δ=1/4`, `δ'=1/2`, `τs=1/60=𝔠𝔡`, `D=1`, `k=1`, `bump`): deterministic hypotheses discharged:
  `Admissible` (`sz0_adm`), `UNDens'` (`UNDens'.mono` of `un_dens'_msc_zero`), `UNMeanBound` (`unMeanBound_toC`), `UNTrLocalInit'` (`unTrLocalInit'_band_zero`),
  `UNTrLocal` at `1/4` (`UNTrLocal.mono`), `0<1/60<1`, `1/60 ≤ 𝔠𝔡`, `|0|<2`, `1≤1`, `IsTestFun bump`.  Kept as hypotheses (other gates' pins, each with its numbers in (a) "External hypotheses"):
  `UNLocAvgBand`, `UNTrLocalBandRow`, `UNNormBandRow`, `UNL32`, `UNGUELocal`, `UNGreenCorrAllC`, `UNClaimAllC sz0 (band).toC 0`, the band local law at `1/2`, the norm bound,
  and the owed pin `UNCoreC''` itself (`inst_coreC_band''`).  `inst_not_UNStep1GoodC'_diag` keeps `UNStep1GoodC'` (the refuted pin) and `UNTrLocalInit`, `UNNormBound` of
  `diagModel sz0 γ`: argued, not compiled, for the semicircle-quantile `γ` of (a) "Refutation hypotheses satisfiable together"; for an arbitrary `γ` they need not hold.  The structural hypotheses are satisfiable (`inst_diag_model`).
  Seven further instances apply the matrix facts, the dictionary and `step1GoodC''_det` at concrete data (`Fin 3` diagonal matrices; `sz0`, band model).  No `N = 0`, empty index, collapsed window.
- Not targets (ticket): a composition `un_coreC_of_rows''`; a compiled refutation of `UNTrLocalInit` at the band model (argued in (a)); the general non-diagonal T2208a refutation;
  the BA rows of `UNTrLocalInit'`, `UNMeanBound` (BA-C1b).  The merged `UNKInst.inst_coreC_band`, `UNDensInst.inst_coreC_band'` are vacuous (their hypothesis `UNTrLocalInit` fails for
  the band model, (a) "External hypotheses"); the module docstring says so; `PinsC2Inst.inst_coreC_band''` replaces them.  No real obstruction was met.
- Registry (§66 (2), §69): as the ticket lists; the full `lake build` and the pre-check pass; the negative test fails with the disjointness error as required.
  Hub merge: root import `import RBM3D.Universality.PinsC2` after the last import line (tested above); on an `Axioms.lean` conflict take the union except that
  `UNTrLocalInit`, `UNStep1GoodC'`, `UNCoreC'` must not be in `owedProps` (the full build fails otherwise: negative test).
- Ports: no RBM1D/RBM2D file was read or copied in this stage (RBM2D has no centred model), so no RBM1D/RBM2D diff-stat applies.  Copies are from merged RBM3D files:
  `Universality/Step1Good.lean` (last commit a42cad0; its module docstring cites RBM2D `Step1RegularityB.lean` at c9a24cf), `PinsDens.lean` (3fc9d03), `Induction/ScaleFacts.lean` (5d1e6b1).

## (c) Verified Mathlib names — Mon Oct  5 21:25:48 UTC 2026 (`date -u`)
All 61 names below elaborate under `#check @name` (script `mathlib_check.lean`, `open MeasureTheory Filter`; exit 0, 0 errors); grouped, not one per line, for the length limit.  Names verified absent: none tried.
- Hermitian/PSD: `Matrix.IsHermitian.{posSemidef_iff_eigenvalues_nonneg, spectrum_real_eq_range_eigenvalues, eigenvalues_mem_spectrum_real, eigenvalues_eq_zero_iff, charpoly_eq, smul, sub, add}`,
  `Matrix.PosSemidef.{add, smul}`, `Matrix.{isHermitian_diagonal_of_self_adjoint, isHermitian_one, charpoly_diagonal}`; spectra: `spectrum.{singleton_sub_eq, singleton_add_eq, mem_iff}`, `Algebra.algebraMap_eq_smul_one`.
- Matrices/inverses: `Matrix.{inv_eq_right_inv, nonsing_inv_eq_ringInverse, trace_diagonal, trace_smul, diagonal_mul_diagonal, diagonal_one, isUnit_diagonal, smul_mul, mul_smul}`, `Ring.inverse_mul`, `Pi.isUnit_iff`,
  `IsUnit.map`, `isUnit_iff_ne_zero`; polynomials/sums: `Polynomial.eval_prod`, `Finset.{prod_eq_zero, prod_eq_zero_iff, sum_eq_single, sum_sub_distrib}`, `Fintype.card_pos_iff`.
- Complex/real: `Complex.{conj_ofReal, norm_le_abs_re_add_abs_im, abs_im_le_norm, re_ofReal_mul, im_ofReal_mul, norm_real, norm_natCast, real_smul}`, `Real.{add_one_le_exp, exp_half,
  rpow_le_one_of_one_le_of_nonpos, rpow_le_rpow_of_exponent_le, one_le_rpow, rpow_neg_one}`, `inv_lt_one_of_one_lt₀`, `le_of_mul_le_mul_left`.
- Limits/measure: `tendsto_rpow_atTop`, `tendsto_rpow_neg_atTop`, `tendsto_nhds_unique`, `Filter.tendsto_atTop_mono'`, `ENNReal.{one_le_ofReal, ofReal_add}`, `MeasureTheory.{measure_univ, measure_union_le, measure_mono}`.
- API facts met: `push_neg` is spelled `push Not`; `Set.mem_setOf_eq` is deprecated for `Set.mem_ofPred_eq`; `if_true` for `ite_true`; the notation `⁻¹ʳ` of `Ring.inverse` needs its scope (write `Ring.inverse`).

## (d) Open issues and paper-delta candidates — Mon Oct  5 21:25:48 UTC 2026 (`date -u`)
- **T2213a** (registry; for the dispatcher): `UNStep1GoodC''` is proved here (`step1GoodC''`), so it is not registered (as `UNCore'` in T2201); the supervisor's B2 list had it owed.
- **T2213b** (registry wording): the docstring of `refutedProps` says "pins shown false"; `UNCoreC'` is only superseded and `UNTrLocalInit` is a predicate argued false for the band model;
  the comment lines of the new entries say so; a "superseded, not needed" class (§68 (9)) would be the exact home.
- **T2213c** (docstring only): with `τ = τs/8` the new term `W^τ t*` needs `τs < 2/3` (the rate lemma `PinsC2_rate`, gap `1 - 3τs/2`); the supervisor's `8/11` is the `τ → 0` limit;
  `step1GoodC''_det` gets `τs < 2/3` from `un_admissible_cd_lt_half` (`τs ≤ 𝔠𝔡 < 1/2`).
- **T2213d**: none.  No new statement differs from its pinned text (pin diff, 18 text-identical checks, 18 definitional `example`s).
- **T2213e** (docstring/ticket table only): the bridge constant of the strip is `K + Lp(|E|+δ+1)`, not `K + Lp(|E|+1)` ((a′) 1); `ε_n` is internal.
- **T2213f** (proof route only): the refutation uses `R_n = 4N(N^{CV₀+1}+|E|+|γ_{n,i₀}|+1)`, not `8N^{CV₀+2}` ((a′) 3); the pin's order of quantifiers is respected (`R_n` is built before `τs`).
- **T2213g** (paper-delta candidate, for the dispatcher): the tolerance `W^τ (Bctl + t*)` of `UNTrLocalInit'` is a formalization-side model of the OU shift `a⁻¹ - 1 ≤ t*` of the initial
  matrix (the paper's (G_bound_ave) concerns `H` itself); `unTrLocalInit'_band_zero` derives it from `UNTrLocal` in the window `1/2` (paper statement `MR:locSC`) and shrinks the window to `1/4`.
- **T2208b** (supervisor O2, no paper statement changes here): the merged `UNTrLocalInit` fails for the band model for `τs > 1/6` (numbers in (a) "External hypotheses" and "Refutation hypotheses satisfiable together"; argued, not compiled).
- Open for later tickets: the BA rows of `UNTrLocalInit'` and `UNMeanBound`, the C-form `UNInfty1Row` analogue (UN-14), the semicircle-quantile diagonal model as a compiled witness of the
  kept hypotheses of `inst_not_UNStep1GoodC'_diag`.
